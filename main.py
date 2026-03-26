"""Standalone CS2 runtime.

Internal layout:
1) Boot / dependencies / offsets
2) ESP + world math helpers
3) Process + memory primitives
4) Overlay + menu rendering
5) Feature workers (aimbot/trigger/esp/misc)
6) Supervisor + lifecycle
7) Entrypoint
"""

import ctypes
import hashlib
import json
import logging
import math
import os
import random
import signal
import struct
import sys
import tempfile
import threading
import time
import traceback
from ctypes import wintypes
from logging.handlers import RotatingFileHandler
from multiprocessing import Lock, Manager, Process, freeze_support

import glfw
import imgui
import numpy as np
import OpenGL.GL as gl
import psutil
import pyautogui
import requests
import win32api
import win32con
import win32gui
from imgui.integrations.glfw import GlfwRenderer
from PIL import ImageGrab
from scipy.signal import convolve2d
from win32gui import FindWindow

_THIS_DIR = os.path.dirname(os.path.abspath(__file__))
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

from runtime.context import RuntimeContext
from runtime.observability import log_event as _runtime_log_event
from runtime.offsets import load_offsets_with_fallback as _runtime_load_offsets_with_fallback
from runtime.parity import build_function_parity_report

# Keep pycache clean for multiprocess launches on Windows.
sys.dont_write_bytecode = True
os.environ.setdefault("PYTHONDONTWRITEBYTECODE", "1")

PROCESS_ALL_ACCESS = 0x1F0FFF
TH32CS_SNAPMODULE = 0x00000008
MAX_MODULE_NAME32 = 255
CS2_PROCESS_NAME = "cs2.exe"
CS2_WINDOW_TITLE = "Counter-Strike 2"
REMOTE_OFFSETS_ENABLED = os.environ.get("GSCRIPT_ALLOW_REMOTE_OFFSETS", "0").strip().lower() in {
    "1", "true", "yes", "on"
}

# ==============================
# SECTION 1: BOOT + OFFSETS
# ==============================


def _read_font_bytes(candidates):
    for path in candidates:
        try:
            if path and os.path.exists(path):
                with open(path, "rb") as f:
                    data = f.read()
                if data:
                    return data
        except OSError:
            continue
    return b""


_PROJECT_ROOT = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.dirname(_PROJECT_ROOT)
_LOCAL_FONT_DIRS = [
    _PROJECT_ROOT,
    os.path.join(_PROJECT_ROOT, "fonts"),
    os.path.join(os.getcwd(), "fonts"),
]
_LOG_BOOTSTRAPPED = False
_LOGGER = logging.getLogger("gscript_runtime")
_SHUTDOWN_REQUESTED = threading.Event()
_SINGLE_INSTANCE_HANDLE = None
_SINGLE_INSTANCE_MUTEX = "Global\\GScriptCS2RuntimeSingleton"
ERROR_ALREADY_EXISTS = 183
_WARN_THROTTLE_STATE = {}


def _bootstrap_logging(level=logging.DEBUG):
    global _LOG_BOOTSTRAPPED, _LOGGER
    if _LOG_BOOTSTRAPPED:
        return _LOGGER

    logger = logging.getLogger("gscript_runtime")
    logger.setLevel(level)
    logger.propagate = False

    # Clear inherited handlers to avoid duplicate logs under multiprocessing spawn.
    logger.handlers.clear()

    fmt = logging.Formatter(
        "[%(asctime)s] [%(levelname)s] [pid=%(process)d] [%(threadName)s] %(message)s"
    )
    console = logging.StreamHandler(sys.stdout)
    console.setFormatter(fmt)
    console.setLevel(level)
    logger.addHandler(console)

    try:
        logs_dir = os.path.join(_REPO_ROOT, "logs")
        os.makedirs(logs_dir, exist_ok=True)
        file_handler = RotatingFileHandler(
            os.path.join(logs_dir, "runtime.log"),
            maxBytes=2 * 1024 * 1024,
            backupCount=5,
            encoding="utf-8",
        )
        file_handler.setFormatter(fmt)
        file_handler.setLevel(level)
        logger.addHandler(file_handler)
    except Exception:
        logger.exception("Failed to initialize file logging handler.")

    _LOGGER = logger
    _LOG_BOOTSTRAPPED = True
    _LOGGER.info("Logging initialized (console + rotating file).")
    return _LOGGER


def _log_exception(message, *args):
    try:
        _LOGGER.exception(message, *args)
    except Exception:
        traceback.print_exc()


def _emit_runtime_event(event_name, level="info", **fields):
    try:
        _runtime_log_event(_LOGGER, event_name, level=level, **fields)
    except Exception:
        pass


def _log_warning_throttled(key, interval_sec, message, *args):
    now = time.monotonic()
    try:
        interval = max(0.1, float(interval_sec))
    except Exception:
        interval = 1.0
    last = float(_WARN_THROTTLE_STATE.get(str(key), 0.0))
    if (now - last) < interval:
        return
    _WARN_THROTTLE_STATE[str(key)] = now
    _LOGGER.warning(message, *args)


def _global_excepthook(exc_type, exc_value, exc_traceback):
    if issubclass(exc_type, KeyboardInterrupt):
        sys.__excepthook__(exc_type, exc_value, exc_traceback)
        return
    try:
        _LOGGER.error(
            "Unhandled top-level exception.",
            exc_info=(exc_type, exc_value, exc_traceback),
        )
    except Exception:
        sys.__excepthook__(exc_type, exc_value, exc_traceback)


def _request_shutdown(reason=""):
    if not _SHUTDOWN_REQUESTED.is_set():
        _SHUTDOWN_REQUESTED.set()
        if reason:
            _LOGGER.info("[shutdown] %s", reason)


def _install_signal_handlers():
    def _handler(signum, _frame):
        _request_shutdown(f"Signal {signum} received.")

    try:
        signal.signal(signal.SIGINT, _handler)
    except Exception:
        pass
    try:
        signal.signal(signal.SIGTERM, _handler)
    except Exception:
        pass


def _sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def _log_runtime_identity():
    runtime_path = os.path.abspath(__file__)
    try:
        runtime_hash = _sha256_file(runtime_path)[:12]
    except Exception:
        runtime_hash = "unknown"
    _LOGGER.info("[startup] Runtime file: %s", runtime_path)
    _LOGGER.info("[startup] Runtime version: %s", runtime_hash)

    # Warn if likely duplicate entry scripts exist with different content.
    candidates = [
        os.path.join(_REPO_ROOT, "main.py"),
        os.path.join(_PROJECT_ROOT, "main.py"),
    ]
    runtime_real = os.path.realpath(runtime_path)
    for candidate in candidates:
        if not os.path.exists(candidate):
            continue
        if os.path.realpath(candidate) == runtime_real:
            continue
        try:
            with open(candidate, "r", encoding="utf-8", errors="ignore") as f:
                preview = f.read(512)
            # Expected thin launchers should not be reported as conflicting runtimes.
            if "runpy.run_path" in preview and "cs2.py" in preview:
                continue
            c_hash = _sha256_file(candidate)[:12]
            if c_hash != runtime_hash:
                _LOGGER.warning(
                    "[startup] Duplicate runtime script differs: %s (hash=%s) vs active hash=%s",
                    os.path.abspath(candidate),
                    c_hash,
                    runtime_hash,
                )
        except Exception:
            _LOGGER.warning("[startup] Could not hash duplicate runtime candidate: %s", candidate)


def _acquire_single_instance_guard():
    global _SINGLE_INSTANCE_HANDLE
    if os.name != "nt":
        return True
    kernel32 = ctypes.windll.kernel32
    handle = kernel32.CreateMutexW(None, False, _SINGLE_INSTANCE_MUTEX)
    if not handle:
        _LOGGER.error("[startup] Failed to create single-instance mutex.")
        return False
    last_error = int(kernel32.GetLastError())
    if last_error == ERROR_ALREADY_EXISTS:
        kernel32.CloseHandle(handle)
        _LOGGER.error("[startup] Another instance is already running. Exiting.")
        return False
    _SINGLE_INSTANCE_HANDLE = handle
    return True


def _release_single_instance_guard():
    global _SINGLE_INSTANCE_HANDLE
    if os.name != "nt":
        return
    handle = _SINGLE_INSTANCE_HANDLE
    _SINGLE_INSTANCE_HANDLE = None
    if handle:
        try:
            ctypes.windll.kernel32.CloseHandle(handle)
        except Exception:
            pass


class AdaptivePerfController:
    def __init__(self):
        self.frame_ema = 0.0
        self.tier = 0
        self.last_change = 0.0

    def update(self, frame_time, enabled=True):
        frame_time = max(1e-6, float(frame_time))
        if self.frame_ema <= 0.0:
            self.frame_ema = frame_time
        else:
            self.frame_ema = self.frame_ema * 0.90 + frame_time * 0.10

        if not enabled:
            self.tier = 0
            return self.tier, self.frame_ema

        now = time.perf_counter()
        ema_ms = self.frame_ema * 1000.0
        target = 0
        if ema_ms > 30.0:
            target = 3
        elif ema_ms > 24.0:
            target = 2
        elif ema_ms > 19.0:
            target = 1

        if target > self.tier and (now - self.last_change) >= 0.20:
            self.tier = target
            self.last_change = now
        elif target < self.tier and (now - self.last_change) >= 1.40:
            self.tier = target
            self.last_change = now
        return self.tier, self.frame_ema


_adaptive_perf_controller = AdaptivePerfController()
_PERF_PROFILE_NAMES = {0: "LOW", 1: "BALANCED", 2: "QUALITY"}
_PROFILE_TIER_BIAS = {0: 1, 1: 0, 2: -1}
_adaptive_perf_state = {"tier": 0, "base_tier": 0, "guard_tier": 0, "profile": 1, "ema_fps": 0.0}
_resource_budget_state = {"cpu": 0.0, "ram_mb": 0.0, "guard_tier": 0, "status": "INIT", "polled": False}


def _clamp_int(value, lo, hi):
    try:
        return max(int(lo), min(int(hi), int(value)))
    except Exception:
        return int(lo)


def _perf_profile_idx(settings_snapshot):
    return _clamp_int(settings_snapshot.get("perf_profile", 0), 0, 2)


def _worker_sleep_scale(settings_snapshot):
    idx = _perf_profile_idx(settings_snapshot)
    if idx == 0:
        return 1.35
    if idx == 2:
        return 0.85
    return 1.0


def _sleep_active(duration=0.0, sleep_scale=1.0):
    base = max(0.0, float(duration)) * max(0.5, float(sleep_scale))
    time.sleep(max(0.006, base))


def _sleep_idle(duration=0.0, sleep_scale=1.0):
    base = max(0.0, float(duration)) * max(0.5, float(sleep_scale))
    time.sleep(max(0.05, base))


def _sleep_master_off(duration=0.15, sleep_scale=1.0):
    base = max(0.0, float(duration)) * max(0.5, float(sleep_scale))
    time.sleep(max(0.12, min(0.25, base)))


class ResourceBudgetGovernor:
    def __init__(self):
        self._proc = psutil.Process(os.getpid())
        try:
            self._proc.cpu_percent(None)
        except Exception:
            pass
        self._last_poll = 0.0
        self._pressure_ema = 0.0
        self._guard_tier = 0
        self._warmup_polls = 2

    def poll(self, settings_snapshot):
        state = dict(_resource_budget_state)
        state["polled"] = False
        now = time.perf_counter()
        interval = max(0.25, float(settings_snapshot.get("resource_poll_interval", 1.25) or 1.25))
        if (now - self._last_poll) < interval:
            return state
        self._last_poll = now

        enabled = bool(settings_snapshot.get("resource_guard_enabled", True))
        cpu = 0.0
        ram_mb = 0.0
        guard_tier = 0
        status = "DISABLED"
        pressure = 0.0
        try:
            cpu = float(self._proc.cpu_percent(None))
            ram_mb = float(self._proc.memory_info().rss / (1024 * 1024))
            if enabled:
                cpu_budget = max(5.0, float(settings_snapshot.get("resource_cpu_budget_pct", 55.0) or 55.0))
                ram_budget = max(128.0, float(settings_snapshot.get("resource_ram_budget_mb", 1536.0) or 1536.0))
                cpu_ratio = cpu / cpu_budget
                ram_ratio = ram_mb / ram_budget
                pressure = max(cpu_ratio, ram_ratio)
                if self._pressure_ema <= 0.0:
                    self._pressure_ema = pressure
                else:
                    self._pressure_ema = self._pressure_ema * 0.78 + pressure * 0.22

                if self._warmup_polls > 0:
                    self._warmup_polls -= 1
                    self._guard_tier = 0
                    status = "WARMUP"
                else:
                    p = self._pressure_ema
                    tier = self._guard_tier
                    if tier <= 0:
                        if p > 1.80:
                            tier = 3
                        elif p > 1.45:
                            tier = 2
                        elif p > 1.20:
                            tier = 1
                        else:
                            tier = 0
                    elif tier == 1:
                        if p > 1.60:
                            tier = 2
                        elif p < 0.95:
                            tier = 0
                    elif tier == 2:
                        if p > 1.90:
                            tier = 3
                        elif p < 1.18:
                            tier = 1
                    else:
                        if p < 1.45:
                            tier = 2
                    self._guard_tier = int(tier)
                    status = "OVER" if self._guard_tier > 0 else "OK"
                guard_tier = int(self._guard_tier)
            else:
                self._guard_tier = 0
                status = "DISABLED"
        except Exception:
            status = "ERROR"

        return {
            "cpu": cpu,
            "ram_mb": ram_mb,
            "guard_tier": int(guard_tier) if enabled else 0,
            "status": status,
            "pressure": float(self._pressure_ema if self._pressure_ema > 0.0 else pressure),
            "polled": True,
        }


_resource_budget_governor = ResourceBudgetGovernor()


def _bootstrap_import_paths():
    candidates = [_PROJECT_ROOT, _REPO_ROOT, os.getcwd()]
    appdata = os.environ.get("APPDATA", "").strip()
    if appdata:
        candidates.append(os.path.join(appdata, "GScript"))
    for path in candidates:
        if path and os.path.isdir(path) and path not in sys.path:
            sys.path.insert(0, path)


_bootstrap_import_paths()
_bootstrap_logging()
sys.excepthook = _global_excepthook

_CSGO_ICON_FONT_CANDIDATES = [
    os.path.join(d, "weapon.ttf") for d in _LOCAL_FONT_DIRS
] + [
    os.path.join(d, "csgo_icons.ttf") for d in _LOCAL_FONT_DIRS
]

_VERDANA_CANDIDATES = [
    os.path.join(d, "verdana.ttf") for d in _LOCAL_FONT_DIRS
] + [
    r"C:\Windows\Fonts\verdana.ttf",
    r"C:\Windows\Fonts\segoeui.ttf",
    r"C:\Windows\Fonts\arial.ttf",
]

_FA_CANDIDATES = [
    os.path.join(d, "fa-solid-900.ttf") for d in _LOCAL_FONT_DIRS
] + [
    os.path.join(d, "Font Awesome 6 Free-Solid-900.otf") for d in _LOCAL_FONT_DIRS
]

verdana_bytes = _read_font_bytes(_VERDANA_CANDIDATES)
font_awesome = _read_font_bytes(_FA_CANDIDATES)
weapon_bytes = _read_font_bytes(_CSGO_ICON_FONT_CANDIDATES)

if not weapon_bytes:
    weapon_bytes = verdana_bytes
if not font_awesome:
    font_awesome = verdana_bytes


def _safe_remove_file(path):
    if path and os.path.exists(path):
        try:
            os.remove(path)
        except OSError:
            pass


def _add_font_from_candidates(io, candidates, size_px, glyph_ranges=None):
    for path in candidates:
        if not path or not os.path.exists(path):
            continue
        try:
            font = io.fonts.add_font_from_file_ttf(path, size_px, glyph_ranges=glyph_ranges)
            if font is not None:
                return font
        except Exception:
            continue
    return None


def _add_font_from_bytes(io, font_bytes, size_px, temp_paths, glyph_ranges=None):
    if not font_bytes:
        return None
    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".ttf") as f:
            f.write(font_bytes)
            tmp_path = f.name
        font = io.fonts.add_font_from_file_ttf(tmp_path, size_px, glyph_ranges=glyph_ranges)
        if font is not None:
            temp_paths.append(tmp_path)
            return font
    except Exception:
        pass
    _safe_remove_file(tmp_path)
    return None


def _ensure_default_font(io):
    try:
        return io.fonts.add_font_default()
    except Exception:
        return None


def _sleep_to_fps(frame_start, fps_limit):
    try:
        limit = float(fps_limit)
    except Exception:
        return
    if limit <= 0:
        return
    frame_budget = 1.0 / max(15.0, min(360.0, limit))
    remaining = frame_budget - (time.perf_counter() - frame_start)
    if remaining > 0:
        time.sleep(remaining)


def _font_push_safe(font):
    if font is None:
        return False
    try:
        imgui.push_font(font)
        return True
    except Exception:
        return False


def _font_pop_safe(pushed):
    if pushed:
        try:
            imgui.pop_font()
        except Exception:
            pass


def _load_offsets_with_fallback():
    def _fetch_json(url, timeout):
        if requests is None:
            raise RuntimeError("requests dependency unavailable.")
        response = requests.get(url, timeout=timeout)
        response.raise_for_status()
        return response.json()

    return _runtime_load_offsets_with_fallback(
        project_root=_PROJECT_ROOT,
        cwd=os.getcwd(),
        allow_remote=REMOTE_OFFSETS_ENABLED,
        fetch_json=_fetch_json if requests is not None else None,
        logger=_LOGGER,
    )


bone_ids = {
    "head": 6,
    "neck": 5,
    "spine": 4,
    "pelvis": 0,
    "left_shoulder": 13,
    "left_elbow": 14,
    "left_wrist": 15,
    "right_shoulder": 9,
    "right_elbow": 10,
    "right_wrist": 11,
    "left_hip": 25,
    "left_knee": 26,
    "left_ankle": 27,
    "right_hip": 22,
    "right_knee": 23,
    "right_ankle": 24,
}

bone_connections = [
    ("head", "neck"),
    ("neck", "spine"),
    ("spine", "pelvis"),
    ("pelvis", "left_hip"),
    ("left_hip", "left_knee"),
    ("left_knee", "left_ankle"),
    ("pelvis", "right_hip"),
    ("right_hip", "right_knee"),
    ("right_knee", "right_ankle"),
    ("neck", "left_shoulder"),
    ("left_shoulder", "left_elbow"),
    ("left_elbow", "left_wrist"),
    ("neck", "right_shoulder"),
    ("right_shoulder", "right_elbow"),
    ("right_elbow", "right_wrist"),
]

offsets, client_dll = _load_offsets_with_fallback()

dwEntityList = offsets['client.dll']['dwEntityList']
dwLocalPlayerPawn = offsets['client.dll']['dwLocalPlayerPawn']
dwLocalPlayerController = offsets['client.dll']['dwLocalPlayerController']
dwViewMatrix = offsets['client.dll']['dwViewMatrix']
dwPlantedC4 = offsets['client.dll']['dwPlantedC4']
dwViewAngles = offsets['client.dll']['dwViewAngles']
dwSensitivity = offsets['client.dll']['dwSensitivity']
dwSensitivity_sensitivity = offsets['client.dll']['dwSensitivity_sensitivity']

m_iTeamNum = client_dll['client.dll']['classes']['C_BaseEntity']['fields']['m_iTeamNum']
m_lifeState = client_dll['client.dll']['classes']['C_BaseEntity']['fields']['m_lifeState']
m_pGameSceneNode = client_dll['client.dll']['classes']['C_BaseEntity']['fields']['m_pGameSceneNode']
m_modelState = client_dll['client.dll']['classes']['CSkeletonInstance']['fields']['m_modelState']
m_hPlayerPawn = client_dll['client.dll']['classes']['CCSPlayerController']['fields']['m_hPlayerPawn']
m_iHealth = client_dll['client.dll']['classes']['C_BaseEntity']['fields']['m_iHealth']
m_iszPlayerName = client_dll['client.dll']['classes']['CBasePlayerController']['fields']['m_iszPlayerName']
m_pClippingWeapon = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_pClippingWeapon']
m_bGunGameImmunity = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_bGunGameImmunity']
m_AttributeManager = client_dll['client.dll']['classes']['C_EconEntity']['fields']['m_AttributeManager']
m_Item = client_dll['client.dll']['classes']['C_AttributeContainer']['fields']['m_Item']
m_iItemDefinitionIndex = client_dll['client.dll']['classes']['C_EconItemView']['fields']['m_iItemDefinitionIndex']
m_ArmorValue = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_ArmorValue']
m_vecAbsOrigin = client_dll['client.dll']['classes']['CGameSceneNode']['fields']['m_vecAbsOrigin']
m_vecOrigin = client_dll['client.dll']['classes']['CGameSceneNode']['fields']['m_vecOrigin']
m_flTimerLength = client_dll['client.dll']['classes']['C_PlantedC4']['fields']['m_flTimerLength']
m_flDefuseLength = client_dll['client.dll']['classes']['C_PlantedC4']['fields']['m_flDefuseLength']
m_bBeingDefused = client_dll['client.dll']['classes']['C_PlantedC4']['fields']['m_bBeingDefused']
m_bSpottedByMask = client_dll['client.dll']['classes']['EntitySpottedState_t']['fields']['m_bSpottedByMask']
m_bSpotted = client_dll['client.dll']['classes']['EntitySpottedState_t']['fields']['m_bSpotted']
m_entitySpottedState = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_entitySpottedState']
m_angEyeAngles = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_angEyeAngles']
m_fFlags = client_dll['client.dll']['classes']['C_BaseEntity']['fields']['m_fFlags']
m_pCameraServices = client_dll['client.dll']['classes']['C_BasePlayerPawn']['fields']['m_pCameraServices']
m_iIDEntIndex = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_iIDEntIndex']
m_vecVelocity = client_dll['client.dll']['classes']['C_BaseEntity']['fields']['m_vecVelocity']
m_aimPunchAngle = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_aimPunchAngle']
m_vOldOrigin = client_dll['client.dll']['classes']['C_BasePlayerPawn']['fields']['m_vOldOrigin']
m_iShotsFired = client_dll['client.dll']['classes']['C_CSPlayerPawn']['fields']['m_iShotsFired']
m_nBombSite = client_dll['client.dll']['classes']['C_PlantedC4']['fields']['m_nBombSite']
m_flFlashDuration = client_dll['client.dll']['classes']['C_CSPlayerPawnBase']['fields']['m_flFlashDuration']
_ccs_controller_fields = client_dll['client.dll']['classes'].get('CCSPlayerController', {}).get('fields', {})
m_hObserverPawn = _ccs_controller_fields.get('m_hObserverPawn', 0)
_observer_services_fields = client_dll['client.dll']['classes'].get('CCSObserver_ObserverServices', {}).get('fields', {})
m_hObserverTarget = _observer_services_fields.get('m_hObserverTarget', 0)
dwGameTypes = offsets.get('matchmaking.dll', {}).get('dwGameTypes', 0)
DW_GAME_TYPES_MAP_NAME = 288

_CURRENT_DYNAMIC_FOV = 0.0


def set_current_dynamic_fov(value):
    global _CURRENT_DYNAMIC_FOV
    try:
        _CURRENT_DYNAMIC_FOV = float(value)
    except Exception:
        _CURRENT_DYNAMIC_FOV = 0.0


def get_current_dynamic_fov(default=0.0):
    try:
        val = float(_CURRENT_DYNAMIC_FOV)
    except Exception:
        return float(default)
    if val <= 0.0:
        return float(default)
    return val

# ==============================
# SECTION 2: GAME STATE + ESP DATA
# ==============================

def make_dpi_aware():
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except (AttributeError, OSError):
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except (AttributeError, OSError):
            pass
make_dpi_aware()
WINDOW_WIDTH, WINDOW_HEIGHT = win32api.GetSystemMetrics(win32con.SM_CXSCREEN), win32api.GetSystemMetrics(win32con.SM_CYSCREEN)

def wait_cs2(timeout=None, poll_interval=1.0):
    started = time.time()
    while True:
        if _SHUTDOWN_REQUESTED.is_set():
            _LOGGER.info("[startup] CS2 wait aborted by shutdown request.")
            return False
        pid = GetProcessIdByName(CS2_PROCESS_NAME)
        if pid:
            client = GetModuleBaseAddress(pid, "client.dll")
            if client:
                return True

        if timeout is not None and (time.time() - started) >= timeout:
            return False
        time.sleep(max(0.05, float(poll_interval)))


def get_descriptor():
    pid = GetProcessIdByName(CS2_PROCESS_NAME)
    if not pid:
        raise RuntimeError("CS2 process not found.")
    client = GetModuleBaseAddress(pid, "client.dll")
    if not client:
        raise RuntimeError("client.dll module not found.")
    pm = Memory(pid)
    if not pm:
        raise RuntimeError("Failed to create memory reader.")
    return client, pm


def get_descriptor_blocking(retry_delay=1.0):
    while True:
        if _SHUTDOWN_REQUESTED.is_set():
            raise RuntimeError("Shutdown requested.")
        try:
            return get_descriptor()
        except Exception:
            time.sleep(max(0.05, float(retry_delay)))

def offsets_mem(pm, client):
    if not pm or not client:
        return [0.0] * 16, 0, 0, 0, 0

    view_matrix = [pm.read_float(client + dwViewMatrix + i * 4) for i in range(16)]
    local_player_pawn_addr = pm.read_longlong(client + dwLocalPlayerPawn)
    if not local_player_pawn_addr:
        return view_matrix, 0, 0, 0, 0

    local_player_team = pm.read_int(local_player_pawn_addr + m_iTeamNum) or 0
    entity_list = pm.read_longlong(client + dwEntityList)
    if not entity_list:
        return view_matrix, local_player_pawn_addr, local_player_team, 0, 0
    entity_ptr = pm.read_longlong(entity_list + 0x10)

    return view_matrix, local_player_pawn_addr, local_player_team, entity_list, entity_ptr

    
def client_mem(pm, i, entity_ptr, entity_list, local_player_pawn_addr, local_player_team):
    if not entity_ptr or not entity_list:
        return

    entity_controller = pm.read_longlong(entity_ptr + 0x70 * (i & 0x1FF))
    if not entity_controller:
        return
    entity_controller_pawn = pm.read_longlong(entity_controller + m_hPlayerPawn)
    if not entity_controller_pawn:
        return
    entity_list_pawn = pm.read_longlong(entity_list + 0x8 * ((entity_controller_pawn & 0x7FFF) >> 0x9) + 0x10)
    if not entity_list_pawn:
        return
    entity_pawn_addr = pm.read_longlong(entity_list_pawn + 0x70 * (entity_controller_pawn & 0x1FF))
    if not entity_pawn_addr or entity_pawn_addr == local_player_pawn_addr:
        return
    entity_team = pm.read_int(entity_pawn_addr + m_iTeamNum)
    if entity_team is None:
        return
    entity_hp = pm.read_int(entity_pawn_addr + m_iHealth)
    if not entity_hp or entity_hp <= 0:
        return
    entity_alive = pm.read_int(entity_pawn_addr + m_lifeState)
    if entity_alive != 256:
        return
    spotted = pm.read_bool(entity_pawn_addr + m_entitySpottedState + m_bSpottedByMask)
    
    return entity_team, local_player_team, entity_pawn_addr, entity_controller, spotted

def esp_dweapon(pm, i, entity_list, view_matrix, width, height):
    itementitylistentry = pm.read_longlong(entity_list + 8 * ((i & 0x7FFF) >> 9) + 16)
    if not itementitylistentry:
        return
    itementity = pm.read_longlong(itementitylistentry + 112 * (i & 0x1FF))
    if not itementity:
        return
    itementitynode = pm.read_longlong(itementity + m_pGameSceneNode)
    itementityorigin = read_vec3(pm, itementitynode + m_vecOrigin)
    weaponowner = pm.read_longlong(itementity + 0x440)
    if not weaponowner:
        return

    weaponsc = w2s(view_matrix, itementityorigin[0], itementityorigin[1], itementityorigin[2], width, height)
    if not weaponsc:
        return
    iteminfo = pm.read_longlong(itementity + 0x10)
    itemtypeptr = pm.read_longlong(iteminfo + 0x20)
    if itementityorigin[0]:
        type = pm.read_string(itemtypeptr, 128)
        weapons = get_weapon_type(type)
        return weaponsc, weapons

def esp_line(pm, entity_pawn_addr, view_matrix, width, height):
    game_scene = pm.read_longlong(entity_pawn_addr + m_pGameSceneNode)
    bone_matrix = pm.read_longlong(game_scene + m_modelState + 0x80)
    data = pm.read_bytes(bone_matrix + 6 * 0x20, 3 * 4)
    headX, headY, headZ = struct.unpack('fff', data)
    headZ += 8
    head_pos = w2s(view_matrix, headX, headY, headZ, width, height)
    legZ = pm.read_float(bone_matrix + 28 * 0x20 + 0x8)
    leg_pos = w2s(view_matrix, headX, headY, legZ, width, height)
    bottom_left_x = head_pos[0] - (head_pos[0] - leg_pos[0]) // 2
    bottom_y = leg_pos[1]

    return bottom_left_x, bottom_y, bone_matrix, headX, headY, headZ, head_pos

def read_vec2(pm, address):
    data = pm.read_bytes(address, 8)
    vec2 = struct.unpack('2f', data)
    return vec2

def read_vec3(pm, address):
    data = pm.read_bytes(address, 12)
    vec3 = struct.unpack('3f', data)
    return vec3

def esp_head_line(pm, entity_pawn_addr, bone_matrix, view_matrix, lenght, width, height):
    data = pm.read_bytes(bone_matrix + 6 * 0x20, 3 * 4)
    headX, headY, headZ = struct.unpack('fff', data)
    head_pos = w2s(view_matrix, headX, headY, headZ, width, height)
    firstX = head_pos[0]
    firstY = head_pos[1]
    vec2eye = read_vec2(pm, entity_pawn_addr + m_angEyeAngles)
    line_length = math.cos(vec2eye[0] * math.pi / 180) * lenght
    temp_x = headX + math.cos(vec2eye[1] * math.pi / 180) * line_length
    temp_y = headY + math.sin(vec2eye[1] * math.pi / 180) * line_length
    temp_z = headZ - math.sin(vec2eye[0] * math.pi / 180 ) * lenght
    end_point = w2s(view_matrix, temp_x, temp_y, temp_z, width, height)
    return firstX, firstY, end_point 

def esp_box(pm, bone_matrix, view_matrix, headX, headY, head_pos, width, height):
    legZ = pm.read_float(bone_matrix + 28 * 0x20 + 0x8)
    leg_pos = w2s(view_matrix, headX, headY, legZ, width, height)
    deltaZ = abs(head_pos[1] - leg_pos[1])
    leftX = head_pos[0] - deltaZ // 4
    rightX = head_pos[0] + deltaZ // 4

    return leftX, leg_pos, rightX, deltaZ

def esp_headbox(pm, bone_matrix, view_matrix, rightX, leftX, window_width, window_height):
    data = pm.read_bytes(bone_matrix + 6 * 0x20, 3 * 4)
    boneX, boneY, boneZ = struct.unpack('fff', data)
    rhead_pos = w2s(view_matrix, boneX, boneY, boneZ, window_width, window_height)
    head_hitbox_size = (rightX - leftX) / 4.5
    head_hitbox_radius = head_hitbox_size * 2 ** 0.5 / 2
    head_hitbox_x = rhead_pos[0] 
    head_hitbox_y = rhead_pos[1]

    return head_hitbox_x, head_hitbox_y, head_hitbox_radius

def esp_bone(pm, bone_matrix, view_matrix, window_width, window_height):
    bone_positions = {}
    for bone_name, bone_id in bone_ids.items():
        data = pm.read_bytes(bone_matrix + bone_id * 0x20, 3 * 4)
        boneX, boneY, boneZ = struct.unpack('fff', data)
        bone_pos = w2s(view_matrix, boneX, boneY, boneZ, window_width, window_height)
        if bone_pos[0] != -999 and bone_pos[1] != -999:
            bone_positions[bone_name] = bone_pos

    return bone_connections, bone_positions

def esp_nickname(pm, entity_controller):
    player_name = pm.read_string(entity_controller + m_iszPlayerName, 32)

    return player_name

def esp_weapon(pm, entity_pawn_addr):
    weapon_pointer = pm.read_longlong(entity_pawn_addr + m_pClippingWeapon)
    weapon_index = pm.read_int(weapon_pointer + m_AttributeManager + m_Item + m_iItemDefinitionIndex)
    weapon_name = get_weapon_name(weapon_index)
    weapon_icon = get_weapon_icon(weapon_name)

    return weapon_icon

def esp_immunity(pm, entity_pawn_addr):
    immunity = pm.read_int(entity_pawn_addr + m_bGunGameImmunity)
    return immunity in (1, 257)

def esp_hp(pm, entity_pawn_addr, deltaZ, head_pos, leftX):
    entity_hp = pm.read_int(entity_pawn_addr + m_iHealth)
    #print(entity_hp)
    max_hp = 100
    hp_percentage = min(1.0, max(0.0, entity_hp / max_hp))
    hp_bar_width = 2
    hp_bar_height = deltaZ
    hp_bar_x_left = leftX - hp_bar_width
    hp_bar_y_top = head_pos[1]
    current_hp_height = hp_bar_height * hp_percentage
    hp_bar_y_bottom = hp_bar_y_top + hp_bar_height - current_hp_height

    return hp_bar_x_left, hp_bar_y_top, hp_bar_y_bottom, current_hp_height

def esp_br(pm, entity_pawn_addr, deltaZ, head_pos, rightX, leftX, leg_pos):
    armor_hp = pm.read_int(entity_pawn_addr + m_ArmorValue)
    max_armor_hp = 100
    armor_hp_percentage = min(1.0, max(0.0, armor_hp / max_armor_hp))
    armor_bar_height = 2  # Height of the armor bar
    armor_bar_width = rightX - leftX  # Width of the armor bar
    armor_bar_x_left = leftX
    armor_bar_y_top = leg_pos[1] + 2  # 2 pixels below the bottom of the enemy box
    current_armor_width = armor_bar_width * armor_hp_percentage
    armor_bar_x_right = rightX

    return armor_bar_x_left, armor_bar_y_top, armor_bar_x_right, current_armor_width

# ==============================
# Gameplay Helpers
# ==============================

class csBomb:
    BombPlantedTime = 0
    BombDefusedTime = 0
    
    @staticmethod
    def getC4BaseClass(pm, client):
        PlantedC4Class = pm.read_longlong(client + dwPlantedC4)
        return pm.read_longlong(PlantedC4Class)
    
    @staticmethod
    def getPositionWTS(pm, client, view_matrix, window_width, window_height):
        base_class = csBomb.getC4BaseClass(pm, client)
        if not base_class:
            return None
            
        C4Node = pm.read_longlong(base_class + m_pGameSceneNode)
        if not C4Node:
            return None
            
        c4_pos = (
            pm.read_float(C4Node + m_vecAbsOrigin),
            pm.read_float(C4Node + m_vecAbsOrigin + 0x4),
            pm.read_float(C4Node + m_vecAbsOrigin + 0x8)
        )
        
        return w2s(view_matrix, *c4_pos, window_width, window_height)
    
    @staticmethod
    def getSite(pm, client):
        base_class = csBomb.getC4BaseClass(pm, client)
        if not base_class:
            return None
            
        Site = pm.read_int(base_class + m_nBombSite)
        return "A" if (Site != 1) else "B"
    
    @staticmethod
    def isPlanted(pm, client):
        BombIsPlanted = pm.read_bool(client + dwPlantedC4 - 0x8)

        if BombIsPlanted:
            if csBomb.BombPlantedTime == 0:
                csBomb.BombPlantedTime = time.time()
        else:
            csBomb.BombPlantedTime = 0

        return BombIsPlanted
    
    @staticmethod
    def isBeingDefused(pm, client):
        base_class = csBomb.getC4BaseClass(pm, client)
        if not base_class:
            return False
            
        BombIsDefused = pm.read_bool(base_class + m_bBeingDefused)

        if BombIsDefused:
            if csBomb.BombDefusedTime == 0:
                csBomb.BombDefusedTime = time.time()
        else:
            csBomb.BombDefusedTime = 0

        return BombIsDefused
    
    @staticmethod
    def getDefuseLength(pm, client):
        base_class = csBomb.getC4BaseClass(pm, client)
        if not base_class:
            return 0.0
        return pm.read_float(base_class + m_flDefuseLength)
    
    @staticmethod
    def getTimerLength(pm, client):
        base_class = csBomb.getC4BaseClass(pm, client)
        if not base_class:
            return 0.0
        return pm.read_float(base_class + m_flTimerLength)
    
    @staticmethod
    def getBombTime(pm, client):
        if csBomb.BombPlantedTime == 0:
            return 0.0
            
        timer_length = csBomb.getTimerLength(pm, client)
        bomb_time = timer_length - (time.time() - csBomb.BombPlantedTime)
        return max(0.0, bomb_time)
    
    @staticmethod
    def getDefuseTime(pm, client):
        if not csBomb.isBeingDefused(pm, client) or csBomb.BombDefusedTime == 0:
            return 0.0
            
        defuse_length = csBomb.getDefuseLength(pm, client)
        defuse_time = defuse_length - (time.time() - csBomb.BombDefusedTime)
        return max(0.0, defuse_time)
    
class RCSState:
    old_punch_x = 0.0
    old_punch_y = 0.0

def no_recoil(pm, client, local_player_addr):
    aim_punch_x = pm.read_float(local_player_addr + m_aimPunchAngle)
    aim_punch_y = pm.read_float(local_player_addr + m_aimPunchAngle + 0x4)
    shots_fired = pm.read_int(local_player_addr + m_iShotsFired)
    mouse_x, mouse_y = 0, 0

    if aim_punch_x is None or aim_punch_y is None or shots_fired is None:
        return mouse_x, mouse_y

    if shots_fired > 1:
        delta_x = (aim_punch_x - RCSState.old_punch_x) * -1.0
        delta_y = (aim_punch_y - RCSState.old_punch_y) * -1.0
        sens_ptr = pm.read_longlong(client + dwSensitivity)
        if not sens_ptr:
            return mouse_x, mouse_y
        sensitivity = pm.read_float(sens_ptr + dwSensitivity_sensitivity)
        if sensitivity and sensitivity > 0:
            mouse_x = int((delta_y * 2.0 / sensitivity) / -0.022)
            mouse_y = int((delta_x * 2.0 / sensitivity) / 0.022)

    RCSState.old_punch_x = aim_punch_x
    RCSState.old_punch_y = aim_punch_y

    return mouse_x, mouse_y

# ==============================
# SECTION 3: PROCESS + MEMORY
# ==============================

class ProcessManager:
    def __init__(self):
        self.process_id = None
        self.process_handle = None
        self.client_module = None
        self.server_module = None
        self.hwnd = None

    @staticmethod
    def get_process_id(process_name):
        expected = str(process_name).lower()
        for proc in psutil.process_iter(['pid', 'name']):
            name = (proc.info.get('name') or "").lower()
            if name == expected:
                return proc.info['pid']
        return None

    def connect(self, process_name, window_title):
        self.process_id = self.get_process_id(process_name)
        if not self.process_id:
            return False
            
        self.hwnd = FindWindow("SDL_app", window_title)
        self.process_handle = ctypes.windll.kernel32.OpenProcess(
            PROCESS_ALL_ACCESS, 
            False, 
            self.process_id
        )
        self.client_module = self.get_module_address("client.dll")
        self.server_module = self.get_module_address("server.dll")
        
        return self.process_handle is not None

    def get_module_address(self, module_name):
        h_snapshot = ctypes.windll.kernel32.CreateToolhelp32Snapshot(
            TH32CS_SNAPMODULE, 
            self.process_id
        )
        
        class ModuleEntry32(ctypes.Structure):
            _fields_ = [
                ('dwSize', wintypes.DWORD),
                ('th32ModuleID', wintypes.DWORD),
                ('th32ProcessID', wintypes.DWORD),
                ('GlblcntUsage', wintypes.DWORD),
                ('ProccntUsage', wintypes.DWORD),
                ('modBaseAddr', ctypes.POINTER(wintypes.BYTE)),
                ('modBaseSize', wintypes.DWORD),
                ('hModule', wintypes.HMODULE),
                ('szModule', ctypes.c_char * (MAX_MODULE_NAME32 + 1)),
                ('szExePath', ctypes.c_char * 260)
            ]
            
        entry = ModuleEntry32()
        entry.dwSize = ctypes.sizeof(ModuleEntry32)
        
        if ctypes.windll.kernel32.Module32First(h_snapshot, ctypes.byref(entry)):
            while True:
                if module_name.encode() == entry.szModule:
                    ctypes.windll.kernel32.CloseHandle(h_snapshot)
                    return entry.hModule
                if not ctypes.windll.kernel32.Module32Next(h_snapshot, ctypes.byref(entry)):
                    break
                    
        ctypes.windll.kernel32.CloseHandle(h_snapshot)
        return 0

class MemoryReader:
    def __init__(self, process_handle):
        self.process_handle = process_handle
        
    def read(self, address, c_type):
        buffer = c_type()
        bytes_read = ctypes.c_size_t()
        
        ctypes.windll.kernel32.ReadProcessMemory(
            self.process_handle,
            ctypes.c_void_p(address),
            ctypes.byref(buffer),
            ctypes.sizeof(buffer),
            ctypes.byref(bytes_read)
        )
        
        return buffer.value if bytes_read.value == ctypes.sizeof(buffer) else None

    def read_bytes(self, address, size):
        buffer = (ctypes.c_byte * size)()
        bytes_read = ctypes.c_size_t()
        
        ctypes.windll.kernel32.ReadProcessMemory(
            self.process_handle,
            ctypes.c_void_p(address),
            buffer,
            size,
            ctypes.byref(bytes_read)
        )
        
        return bytes(buffer) if bytes_read.value == size else None
    
    def read_int(self, address):
        return self.read(address, ctypes.c_int)
        
    def read_float(self, address):
        return self.read(address, ctypes.c_float)
        
    def read_longlong(self, address):
        return self.read(address, ctypes.c_longlong)
        
    def read_bool(self, address):
        return self.read(address, ctypes.c_bool)
        
    def read_short(self, address):
        return self.read(address, ctypes.c_short)
        
    def read_string(self, address, max_length):
        buffer = ctypes.create_string_buffer(max_length)
        bytes_read = ctypes.c_size_t()
        
        ctypes.windll.kernel32.ReadProcessMemory(
            self.process_handle,
            ctypes.c_void_p(address),
            buffer,
            max_length,
            ctypes.byref(bytes_read)
        )
        
        return buffer.value.decode('utf-8', 'ignore') if bytes_read.value > 0 else ""

def GetProcessIdByName(process_name):
    return ProcessManager.get_process_id(process_name)

def GetModuleBaseAddress(pid, module_name):
    temp_manager = ProcessManager()
    temp_manager.process_id = pid
    return temp_manager.get_module_address(module_name)

def Memory(pid):
    handle = ctypes.windll.kernel32.OpenProcess(PROCESS_ALL_ACCESS, False, pid)
    return MemoryReader(handle) if handle else None

weapon_font = None
verdana_font = None
menu_main_font = None
menu_icon_font = None

_overlay_menu_state = {
    "visible": False,
    "last_insert_toggle": 0.0,
    "last_f5_toggle": 0.0,
    "insert_wait_release": False,
    "current_tab": 0,
    "prev_tab": -1,
    "tab_animations": [],
    "content_alpha": 0.0,
    "last_tab_change_time": 0.0,
    "config_filename": "",
    "config_combo": None,
}


def _set_overlay_menu_interaction(window, enabled):
    try:
        hwnd = glfw.get_win32_window(window)
        ex_style = win32gui.GetWindowLong(hwnd, win32con.GWL_EXSTYLE)
        if enabled:
            ex_style &= ~win32con.WS_EX_TRANSPARENT
            win32gui.SetForegroundWindow(hwnd)
        else:
            ex_style |= win32con.WS_EX_TRANSPARENT
        win32gui.SetWindowLong(hwnd, win32con.GWL_EXSTYLE, ex_style)
    except Exception:
        pass
    try:
        glfw.set_window_attrib(
            window,
            glfw.MOUSE_PASSTHROUGH,
            glfw.FALSE if enabled else glfw.TRUE
        )
    except Exception:
        pass
    try:
        glfw.set_input_mode(
            window,
            glfw.CURSOR,
            glfw.CURSOR_NORMAL if enabled else glfw.CURSOR_DISABLED
        )
    except Exception:
        pass


def _toggle_master_enabled(settings_obj):
    current = bool(settings_obj.get("master_enabled", True))
    new_state = not current
    settings_obj.set("master_enabled", new_state)
    state_word = "ENABLED" if new_state else "DISABLED"
    _LOGGER.info("[hotkey] F5 -> master %s", state_word)
    return new_state

# ==============================
# SECTION 4: OVERLAY RENDERING
# ==============================

def create_window():
    global weapon_font, verdana_font, menu_main_font, menu_icon_font
    font_paths = []
    

    if not glfw.init():
        sys.exit(1)

    glfw.window_hint(glfw.TRANSPARENT_FRAMEBUFFER, glfw.TRUE)
    glfw.window_hint(glfw.DECORATED, glfw.FALSE)
    glfw.window_hint(glfw.FLOATING, glfw.TRUE)
    glfw.window_hint(glfw.RESIZABLE, glfw.FALSE)
    glfw.window_hint(glfw.MAXIMIZED, glfw.TRUE)
    glfw.window_hint(glfw.FOCUS_ON_SHOW, glfw.FALSE)
    
    glfw.window_hint(glfw.MOUSE_PASSTHROUGH, glfw.TRUE)

    window = glfw.create_window(WINDOW_WIDTH, WINDOW_HEIGHT, "Overlay", None, None)
    if not window:
        glfw.terminate()
        sys.exit(1)

    glfw.make_context_current(window)
    try:
        glfw.swap_interval(1)
    except Exception:
        pass
    glfw.set_input_mode(window, glfw.CURSOR, glfw.CURSOR_DISABLED)
    
    gl.glEnable(gl.GL_BLEND)
    gl.glBlendFunc(gl.GL_SRC_ALPHA, gl.GL_ONE_MINUS_SRC_ALPHA)

    hwnd = glfw.get_win32_window(window)

    class MARGINS(ctypes.Structure):
        _fields_ = [("cxLeftWidth", ctypes.c_int),
                    ("cxRightWidth", ctypes.c_int),
                    ("cyTopHeight", ctypes.c_int),
                    ("cyBottomHeight", ctypes.c_int)]

    margins = MARGINS(-1, -1, -1, -1)
    ctypes.windll.dwmapi.DwmExtendFrameIntoClientArea(hwnd, ctypes.byref(margins))

    ex_style = win32gui.GetWindowLong(hwnd, win32con.GWL_EXSTYLE)
    win32gui.SetWindowLong(hwnd, win32con.GWL_EXSTYLE, 
                           ex_style | win32con.WS_EX_LAYERED | win32con.WS_EX_TRANSPARENT | win32con.WS_EX_TOOLWINDOW)
    
    win32gui.SetLayeredWindowAttributes(
        hwnd,
        win32api.RGB(0, 0, 0),
        255,
        win32con.LWA_ALPHA | win32con.LWA_COLORKEY
    )

    # Hard reset in case this process previously crashed mid-frame.
    try:
        imgui.destroy_context()
    except Exception:
        pass
    imgui.create_context()
    io = imgui.get_io()
    weapon_font = None
    verdana_font = None
    menu_main_font = None
    menu_icon_font = None

    ranges = imgui.core.GlyphRanges([
        0x0020, 0x00FF, 0x0400, 0x04FF, 0x0370, 0x03FF,
        0x0600, 0x06FF, 0x0900, 0x097F, 0x4E00, 0x9FFF,
        0x3040, 0x309F, 0x30A0, 0x30FF, 0xAC00, 0xD7AF,
        0xE000, 0xEFFF, 0
    ])

    weapon_font = _add_font_from_candidates(io, _CSGO_ICON_FONT_CANDIDATES, 10)
    if weapon_font is None:
        weapon_font = _add_font_from_bytes(io, weapon_bytes, 10, font_paths)

    verdana_font = _add_font_from_candidates(io, _VERDANA_CANDIDATES, 14, glyph_ranges=ranges)
    if verdana_font is None:
        verdana_font = _add_font_from_bytes(io, verdana_bytes, 14, font_paths, glyph_ranges=ranges)

    menu_main_font = _add_font_from_candidates(io, _VERDANA_CANDIDATES, 16)
    if menu_main_font is None:
        menu_main_font = _add_font_from_bytes(io, verdana_bytes, 16, font_paths)

    icon_ranges = imgui.core.GlyphRanges([0xf000, 0xf8ff, 0])
    menu_icon_font = _add_font_from_candidates(io, _FA_CANDIDATES, 30, glyph_ranges=icon_ranges)
    if menu_icon_font is None:
        menu_icon_font = _add_font_from_bytes(io, font_awesome, 30, font_paths, glyph_ranges=icon_ranges)

    fallback_font = verdana_font or menu_main_font or _ensure_default_font(io)
    if verdana_font is None:
        verdana_font = fallback_font
    if menu_main_font is None:
        menu_main_font = fallback_font
    if weapon_font is None:
        weapon_font = fallback_font
    if menu_icon_font is None:
        menu_icon_font = menu_main_font

    impl = GlfwRenderer(window)
    setup_imgui_style()
    
    return window, impl, hwnd, font_paths
def render_loop(draw_func):
    global _adaptive_perf_state, _resource_budget_state
    window, impl, hwnd, font_paths = create_window()
    fps_ema = 0.0
    menu_state = _overlay_menu_state
    menu_state["visible"] = False
    _set_overlay_menu_interaction(window, False)
    last_z_order = None
    last_menu_visible = None
    last_setpos_time = 0.0
    last_capture_excluded = None
    last_perf_tier = 0
    last_guard_tier = 0
    frame_setting_keys = (
        "wallhack_stop",
        "radar_always_on_top",
        "esp_draw_fps",
        "hide_esp_from_capture",
        "overlay_fps_limit",
        "menu_fps_limit",
        "adaptive_perf_enabled",
        "perf_profile",
        "resource_guard_enabled",
        "resource_cpu_budget_pct",
        "resource_ram_budget_mb",
        "resource_poll_interval",
    )

    try:
        while not glfw.window_should_close(window):
            frame_settings = settings.snapshot(frame_setting_keys) if settings is not None else {}
            wallhack_stop = bool(frame_settings.get("wallhack_stop", False))
            if wallhack_stop:
                break

            insert_state = int(win32api.GetAsyncKeyState(win32con.VK_INSERT))
            insert_down = bool(insert_state & 0x8000)
            insert_pressed = bool(insert_state & 1)
            if not insert_down:
                menu_state["insert_wait_release"] = False
            if insert_pressed and not bool(menu_state.get("insert_wait_release", False)):
                now_insert = time.perf_counter()
                if (now_insert - float(menu_state.get("last_insert_toggle", 0.0))) >= 0.20:
                    menu_state["visible"] = not menu_state["visible"]
                    menu_state["last_insert_toggle"] = now_insert
                    _set_overlay_menu_interaction(window, menu_state["visible"])
                    _LOGGER.info(
                        "[hotkey] INSERT -> menu %s",
                        "OPEN" if menu_state["visible"] else "HIDDEN",
                    )
                menu_state["insert_wait_release"] = True

            z_order = win32con.HWND_TOPMOST
            if not bool(frame_settings.get("radar_always_on_top", True)):
                z_order = win32con.HWND_NOTOPMOST
            pos_flags = win32con.SWP_NOMOVE | win32con.SWP_NOSIZE
            if not menu_state["visible"]:
                pos_flags |= win32con.SWP_NOACTIVATE
            now = time.perf_counter()
            if (
                z_order != last_z_order
                or menu_state["visible"] != last_menu_visible
                or (now - last_setpos_time) > 0.5
            ):
                win32gui.SetWindowPos(
                    hwnd,
                    z_order,
                    0, 0, 0, 0,
                    pos_flags
                )
                last_z_order = z_order
                last_menu_visible = menu_state["visible"]
                last_setpos_time = now

            start_time = time.perf_counter()
            glfw.poll_events()
            impl.process_inputs()
            imgui.new_frame()
            imgui.set_next_window_size(WINDOW_WIDTH, WINDOW_HEIGHT)
            imgui.set_next_window_position(0, 0)
            imgui.push_style_var(imgui.STYLE_WINDOW_PADDING, (0.0, 0.0))
            imgui.begin(
                "overlay",
                flags=imgui.WINDOW_NO_TITLE_BAR |
                imgui.WINDOW_NO_RESIZE |
                imgui.WINDOW_NO_SCROLLBAR |
                imgui.WINDOW_NO_COLLAPSE |
                imgui.WINDOW_NO_BACKGROUND |
                imgui.WINDOW_NO_MOVE
            )
            imgui.pop_style_var()
            draw_list = imgui.get_window_draw_list()
            
            draw_func(draw_list)
            
            frame_time = max(1e-6, time.perf_counter() - start_time)
            inst_fps = 1.0 / frame_time
            fps_ema = inst_fps if fps_ema <= 0.0 else (fps_ema * 0.9 + inst_fps * 0.1)

            adaptive_enabled = bool(frame_settings.get("adaptive_perf_enabled", True))
            base_tier, perf_ema = _adaptive_perf_controller.update(frame_time, adaptive_enabled)
            perf_ema_fps = 1.0 / max(1e-6, perf_ema)

            resource_state = _resource_budget_governor.poll(frame_settings)
            if resource_state.get("polled", False):
                _resource_budget_state = resource_state
                if settings is not None:
                    settings.set("runtime_cpu_percent", round(float(resource_state.get("cpu", 0.0)), 2))
                    settings.set("runtime_ram_mb", round(float(resource_state.get("ram_mb", 0.0)), 1))
                    settings.set("resource_guard_tier", int(resource_state.get("guard_tier", 0)))
                    settings.set("resource_status", str(resource_state.get("status", "OK")))

            profile_idx = _perf_profile_idx(frame_settings)
            profile_bias = int(_PROFILE_TIER_BIAS.get(profile_idx, 0))
            guard_tier = int(_resource_budget_state.get("guard_tier", 0)) if bool(frame_settings.get("resource_guard_enabled", True)) else 0
            perf_tier = max(0, min(3, int(base_tier + profile_bias + guard_tier)))
            _adaptive_perf_state = {
                "tier": perf_tier,
                "base_tier": int(base_tier),
                "guard_tier": int(guard_tier),
                "profile": int(profile_idx),
                "ema_fps": perf_ema_fps,
            }

            if guard_tier != last_guard_tier:
                _LOGGER.warning(
                    "[resource] Guard tier %s -> %s | cpu=%.1f%% | ram=%.1fMB | status=%s",
                    last_guard_tier,
                    guard_tier,
                    float(_resource_budget_state.get("cpu", 0.0)),
                    float(_resource_budget_state.get("ram_mb", 0.0)),
                    str(_resource_budget_state.get("status", "OK")),
                )
                last_guard_tier = guard_tier

            if perf_tier != last_perf_tier:
                if settings is not None:
                    settings.set("adaptive_perf_level", int(perf_tier))
                _LOGGER.warning(
                    "[perf] Tier %s -> %s | base=%s guard=%s profile=%s ema_fps=%.1f",
                    last_perf_tier,
                    perf_tier,
                    base_tier,
                    guard_tier,
                    _PERF_PROFILE_NAMES.get(profile_idx, "BALANCED"),
                    perf_ema_fps,
                )
                last_perf_tier = perf_tier

            if bool(frame_settings.get("esp_draw_fps", False)):
                draw_text(draw_list, 10, 10, f"FPS: {int(fps_ema)}", (1.0, 1.0, 1.0, 1.0))

            capture_excluded = bool(frame_settings.get("hide_esp_from_capture", False))
            if capture_excluded != last_capture_excluded:
                set_overlay_capture_excluded(hwnd, capture_excluded)
                last_capture_excluded = capture_excluded
            
            imgui.end()
            if settings is not None and menu_state["visible"]:
                draw_unified_overlay_menu(settings)
            gl.glClearColor(0.0, 0.0, 0.0, 0.0)
            gl.glClear(gl.GL_COLOR_BUFFER_BIT)
            imgui.render()
            impl.render(imgui.get_draw_data())
            glfw.swap_buffers(window)
            if menu_state["visible"]:
                fps_cap = float(frame_settings.get("menu_fps_limit", 60.0))
            else:
                fps_cap = float(frame_settings.get("overlay_fps_limit", 45.0))
            profile_scale = {0: 0.78, 1: 0.92, 2: 1.0}.get(_perf_profile_idx(frame_settings), 0.92)
            guard_scale = {0: 1.00, 1: 0.82, 2: 0.68, 3: 0.56}.get(last_guard_tier, 1.0)
            tier_cap = (60.0, 52.0, 44.0, 38.0)[max(0, min(3, int(perf_tier)))]
            fps_cap = max(30.0, min(240.0, float(fps_cap) * profile_scale * guard_scale))
            fps_cap = min(fps_cap, tier_cap)
            _sleep_to_fps(start_time, fps_cap)
    finally:
        menu_state["visible"] = False
        try:
            impl.shutdown()
        except Exception:
            pass
        try:
            imgui.destroy_context()
        except Exception:
            pass
        try:
            glfw.destroy_window(window)
        except Exception:
            pass
        glfw.terminate()
        for path in font_paths:
            _safe_remove_file(path)

def draw_circle_outline(draw_list, x, y, radius, color, px_size):
    imgui_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_circle(x, y, radius, imgui_color, 0, px_size)

def draw_circle(draw_list, x, y, radius, color):
    imgui_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_circle_filled(x, y, radius, imgui_color)

def draw_line(draw_list, x, y, x1, y1, color, px_size):
    imgui_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_line(x, y, x1, y1, imgui_color, px_size)

def draw_box(draw_list, x, y, x1, y1, color, px_size):
    imgui_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_line(x, y, x1, y, imgui_color, px_size)
    draw_list.add_line(x, y, x, y1, imgui_color, px_size)
    draw_list.add_line(x1, y, x1, y1, imgui_color, px_size)
    draw_list.add_line(x, y1, x1, y1, imgui_color, px_size)

def draw_filled_box(draw_list, x, y, x1, y1, color):
    imgui_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_rect_filled(x, y, x1, y1, imgui_color)

def draw_corners(draw_list, x, y, x1, y1, color, px_size, percentage=0.2):
    imgui_color = imgui.get_color_u32_rgba(*color)
    width = x1 - x
    short_width = width * percentage
    short_height = -(width * percentage)
    draw_list.add_line(x, y, x + short_width, y, imgui_color, px_size)
    draw_list.add_line(x, y, x, y + short_height, imgui_color, px_size)
    draw_list.add_line(x1, y, x1 - short_width, y, imgui_color, px_size)
    draw_list.add_line(x1, y1, x1, y1 - short_height, imgui_color, px_size)
    draw_list.add_line(x, y1, x + short_width, y1, imgui_color, px_size)
    draw_list.add_line(x, y1, x, y1 - short_height, imgui_color, px_size)
    draw_list.add_line(x1, y, x1, y + short_height, imgui_color, px_size)
    draw_list.add_line(x1, y1, x1 - short_width, y1, imgui_color, px_size)

def draw_text(draw_list, x, y, text, color):
    global verdana_font
    if not verdana_font: return
    pushed = _font_push_safe(verdana_font)
    shadow_x, shadow_y = x + 1, y + 1
    imgui_shadow_color = imgui.get_color_u32_rgba(*(0, 0, 0, 1))
    draw_list.add_text(shadow_x, shadow_y, imgui_shadow_color, text)
    imgui_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_text(x, y, imgui_color, text)
    _font_pop_safe(pushed)

def draw_nickname(draw_list, text, head_pos, rightX, leftX, color):
    global verdana_font
    if not verdana_font: return
    pushed = _font_push_safe(verdana_font)
    text_size = imgui.calc_text_size(text)
    text_width = text_size.x
    text_height = text_size.y
    x = (rightX + leftX - text_width) / 2
    y = head_pos[1] - text_height - 5
    shadow_x, shadow_y = x + 1, y + 1
    imgui_shadow_color = imgui.get_color_u32_rgba(*(0, 0, 0, 1))
    draw_list.add_text(shadow_x, shadow_y, imgui_shadow_color, text)
    imgui_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_text(x, y, imgui_color, text)
    _font_pop_safe(pushed)

def draw_weapon(draw_list, weapon_icon, leg_pos, rightX, leftX, color):
    if weapon_icon:
        global weapon_font
        if not weapon_font: return
        pushed = _font_push_safe(weapon_font)
        text_size = imgui.calc_text_size(weapon_icon)
        text_width = text_size.x
        text_height = text_size.y / 2.5
        x = (rightX + leftX - text_width) / 2
        y = leg_pos[1] + text_height
        shadow_x, shadow_y = x + 1, y + 1
        imgui_shadow_color = imgui.get_color_u32_rgba(*(0, 0, 0, 1))
        draw_list.add_text(shadow_x, shadow_y, imgui_shadow_color, weapon_icon)
        imgui_color = imgui.get_color_u32_rgba(*color)
        draw_list.add_text(x, y, imgui_color, weapon_icon)
        _font_pop_safe(pushed)

def w2s(mtx, posx, posy, posz, width, height):
    screenW = (mtx[12] * posx) + (mtx[13] * posy) + (mtx[14] * posz) + mtx[15]
    if screenW > 0.001:
        screenX = (mtx[0] * posx) + (mtx[1] * posy) + (mtx[2] * posz) + mtx[3]
        screenY = (mtx[4] * posx) + (mtx[5] * posy) + (mtx[6] * posz) + mtx[7]
        camX = width / 2
        camY = height / 2
        x = camX + (camX * screenX / screenW)
        y = camY - (camY * screenY / screenW)
        return [int(x), int(y)]
    return [-999, -999]

weapons_type = {
    "weapon_ak47": "AK-47",
    "weapon_m4a1": "M4A1",
    "weapon_awp": "AWP",
    "weapon_elite": "Elite",
    "weapon_famas": "Famas",
    "weapon_flashbang": "Flashbang",
    "weapon_g3sg1": "G3SG1",
    "weapon_galilar": "Galil AR",
    "weapon_healthshot": "Health Shot",
    "weapon_hegrenade": "HE Grenade",
    "weapon_incgrenade": "Incendiary Grenade",
    "weapon_m249": "M249",
    "weapon_m4a1_silencer": "M4A1-S",
    "weapon_mac10": "MAC-10",
    "weapon_mag7": "MAG-7",
    "weapon_molotov": "Molotov",
    "weapon_mp5sd": "MP5-SD",
    "weapon_mp7": "MP7",
    "weapon_mp9": "MP9",
    "weapon_negev": "Negev",
    "weapon_nova": "Nova",
    "weapon_p90": "P90",
    "weapon_sawedoff": "Sawed-Off",
    "weapon_scar20": "SCAR-20",
    "weapon_sg556": "SG 553",
    "weapon_smokegrenade": "Smoke Grenade",
    "weapon_ssg08": "SSG 08",
    "weapon_tagrenade": "TA Grenade",
    "weapon_taser": "Taser",
    "weapon_ump45": "UMP-45",
    "weapon_xm1014": "XM1014",
    "weapon_aug": "AUG",
    "weapon_bizon": "PP-Bizon",
    "weapon_decoy": "Decoy Grenade",
    "weapon_fiveseven": "Five-Seven",
    "weapon_hkp2000": "P2000",
    "weapon_usp_silencer": "USP-S",
    "weapon_p250": "P250",
    "weapon_tec9": "Tec-9",
    "weapon_cz75a": "CZ75-Auto",
    "weapon_deagle": "Desert Eagle",
    "weapon_revolver": "R8 Revolver",
    "weapon_glock": "Glock-18"
}

def get_weapon_type(item_identifier):
    return weapons_type.get(item_identifier, "unknown")

def get_weapon_name(weapon_id):
    if weapon_id > 262100:
        weapon_id = weapon_id - 262144
    weapon_name = {
        1: 'deagle', 2: 'elite', 3: 'fiveseven', 4: 'glock', 7: 'ak47', 8: 'aug', 9: 'awp',
        10: 'famas', 11: 'g3sg1', 13: 'galil', 14: 'm249', 16: 'm4a1', 17: 'mac10', 19: 'p90',
        23: 'ump45', 24: 'ump45', 25: 'xm1014', 26: 'bizon', 27: 'mag7', 28: 'negev', 29: 'sawedoff', 30: 'tec9',
        31: 'taser', 32: 'hkp2000', 33: 'mp7', 34: 'mp9', 35: 'nova', 36: 'p250', 38: 'scar20',
        39: 'sg556', 40: 'ssg08', 42: 'knife_ct', 43: 'flashbang', 44: 'hegrenade', 45: 'smokegrenade',
        46: 'molotov', 47: 'decoy', 48: 'incgrenade', 49: 'c4', 57: 'deagle', 59: 'knife_t', 60: 'm4a1_silencer',
        61: 'usp_silencer', 63: 'cz75a', 64: 'revolver', 500: 'bayonet', 505: 'knife_flip',
        506: 'knife_gut', 507: 'knife_karambit', 508: 'knife_m9_bayonet', 509: 'knife_tactical',
        512: 'knife_falchion', 514: 'knife_survival_bowie', 515: 'knife_butterfly', 516: 'knife_push',
        526: 'knife_kukri'
    }
    return weapon_name.get(weapon_id, None)

def get_weapon_icon(weapon_name):
    if weapon_name:
        weapon_icons_dict = {
            'knife_ct': ']', 'knife_t': '[', 'deagle': 'A', 'elite': 'B', 'fiveseven': 'C',
            'glock': 'D', 'revolver': 'J', 'hkp2000': 'E', 'p250': 'F', 'usp_silencer': 'G',
            'tec9': 'H', 'cz75a': 'I', 'mac10': 'K', 'ump45': 'L', 'bizon': 'M', 'mp7': 'N',
            'mp9': 'P', 'p90': 'O', 'galil': 'Q', 'famas': 'R', 'm4a1_silencer': 'T', 'm4a1': 'S',
            'aug': 'U', 'sg556': 'V', 'ak47': 'W', 'g3sg1': 'X', 'scar20': 'Y', 'awp': 'Z',
            'ssg08': 'a', 'xm1014': 'b', 'sawedoff': 'c', 'mag7': 'd', 'nova': 'e', 'negev': 'f',
            'm249': 'g', 'taser': 'h', 'flashbang': 'i', 'hegrenade': 'j', 'smokegrenade': 'k',
            'molotov': 'l', 'decoy': 'm', 'incgrenade': 'n', 'c4': 'o', 'mp5': 'z',
        }
        return weapon_icons_dict.get(weapon_name, None)
    return None

_window_handle_cache = {"time": 0.0, "hwnd": 0}
_window_active_cache = {"time": 0.0, "value": False}


def get_window_handle(force=False):
    now = time.perf_counter()
    if not force and (now - _window_handle_cache["time"]) < 0.20:
        return _window_handle_cache["hwnd"]
    hwnd = win32gui.FindWindow(None, CS2_WINDOW_TITLE) or 0
    _window_handle_cache["time"] = now
    _window_handle_cache["hwnd"] = hwnd
    return hwnd


def is_cs2_window_active():
    now = time.perf_counter()
    if (now - _window_active_cache["time"]) < 0.035:
        return _window_active_cache["value"]
    hwnd = get_window_handle()
    if not hwnd:
        _window_active_cache["time"] = now
        _window_active_cache["value"] = False
        return False
    foreground_hwnd = win32gui.GetForegroundWindow()
    active = hwnd == foreground_hwnd
    _window_active_cache["time"] = now
    _window_active_cache["value"] = active
    return active


_capture_excluded_state = None


def set_overlay_capture_excluded(hwnd, excluded):
    global _capture_excluded_state
    if not hwnd:
        return
    excluded = bool(excluded)
    if _capture_excluded_state is excluded:
        return
    try:
        ctypes.windll.user32.SetWindowDisplayAffinity(hwnd, 17 if excluded else 0)
        _capture_excluded_state = excluded
    except Exception:
        pass


def get_current_map_name(pm):
    if not pm or not dwGameTypes:
        return "unknown"
    try:
        pid = GetProcessIdByName(CS2_PROCESS_NAME)
        if not pid:
            return "unknown"
        matchmaking_base = GetModuleBaseAddress(pid, "matchmaking.dll")
        if not matchmaking_base:
            return "unknown"
        map_name_ptr = pm.read_longlong(matchmaking_base + dwGameTypes + DW_GAME_TYPES_MAP_NAME)
        if not map_name_ptr:
            return "unknown"
        map_name = (pm.read_string(map_name_ptr, 64) or "").strip()
        if not map_name:
            return "unknown"
        return map_name
    except Exception:
        return "unknown"


_VISCHECK_IMPORT_DONE = False
_VISCHECK_MODULE = None
_vis_checker = None
_vis_loaded_map_name = ""
_vis_last_attempt = 0.0
_vis_module_missing_state_written = False
_vis_module_unavailable_last_event = 0.0
_VISCHECK_UNAVAILABLE_EVENT_INTERVAL = 15.0
_MAP_DIR_CANDIDATES = [
    os.path.join(_PROJECT_ROOT, "maps"),
    os.path.join(_REPO_ROOT, "maps"),
    os.path.join(os.getcwd(), "maps"),
]


def _import_vischeck_module():
    global _VISCHECK_IMPORT_DONE, _VISCHECK_MODULE
    if _VISCHECK_IMPORT_DONE:
        return _VISCHECK_MODULE
    _VISCHECK_IMPORT_DONE = True
    try:
        import vischeck as _vc  # type: ignore
        _VISCHECK_MODULE = _vc
    except Exception:
        _VISCHECK_MODULE = None
    return _VISCHECK_MODULE


def _map_name_candidates(map_name):
    if not map_name:
        return []
    raw = str(map_name).strip().lower().replace("\\", "/")
    if not raw or raw == "unknown":
        return []
    pieces = [
        raw,
        raw.split("/")[-1],
        raw.replace("maps/", ""),
        raw.split("/")[-1].replace(".bsp", ""),
    ]
    out = []
    for part in pieces:
        p = part.strip().strip("/")
        if not p:
            continue
        if p.endswith(".opt.z"):
            out.append(p)
        else:
            out.append(f"{p}.opt.z")
    seen = set()
    unique = []
    for p in out:
        if p not in seen:
            seen.add(p)
            unique.append(p)
    return unique


def _resolve_visibility_map_path(map_name):
    for rel in _map_name_candidates(map_name):
        for base in _MAP_DIR_CANDIDATES:
            path = os.path.join(base, rel)
            if os.path.isfile(path):
                return path
    return ""


def ensure_vischeck_ready(pm, settings):
    global _vis_checker, _vis_loaded_map_name, _vis_last_attempt
    global _vis_module_missing_state_written, _vis_module_unavailable_last_event

    if not pm or settings is None:
        return None

    use_esp = bool(settings.get("visibility_esp_enabled", True))
    use_aim = bool(settings.get("visibility_aim_enabled", True))
    if not (use_esp or use_aim):
        return None

    module = _import_vischeck_module()
    if module is None:
        if not _vis_module_missing_state_written:
            settings.set("visibility_map_loaded", False)
            _vis_module_missing_state_written = True
        now_mono = time.monotonic()
        if (now_mono - _vis_module_unavailable_last_event) >= _VISCHECK_UNAVAILABLE_EVENT_INTERVAL:
            _emit_runtime_event("vischeck.module_unavailable", level="warning")
            _vis_module_unavailable_last_event = now_mono
        return None
    _vis_module_missing_state_written = False

    if _vis_checker is None:
        try:
            _vis_checker = module.VisCheck()
            _emit_runtime_event("vischeck.instance_created")
        except Exception:
            _vis_checker = None
            settings.set("visibility_map_loaded", False)
            _emit_runtime_event("vischeck.instance_failed", level="error")
            return None

    current_map = get_current_map_name(pm)
    if not current_map or current_map == "unknown":
        return _vis_checker

    reload_needed = bool(settings.get("visibility_map_reload_needed", False))
    if current_map != _vis_loaded_map_name:
        reload_needed = True

    if reload_needed and (time.time() - _vis_last_attempt) >= 1.0:
        _vis_last_attempt = time.time()
        map_path = _resolve_visibility_map_path(current_map)
        settings.set("visibility_map_path", map_path)
        loaded = False
        if map_path:
            try:
                if hasattr(_vis_checker, "load_map"):
                    result = _vis_checker.load_map(map_path)
                elif hasattr(_vis_checker, "load"):
                    result = _vis_checker.load(map_path)
                else:
                    result = False
                loaded = bool(result) if result is not None else True
            except Exception:
                loaded = False
        settings.set("visibility_map_loaded", loaded)
        settings.set("visibility_map_reload_needed", False)
        if loaded:
            _vis_loaded_map_name = current_map
        _emit_runtime_event(
            "vischeck.map_reload",
            level="info" if loaded else "warning",
            map=current_map,
            loaded=loaded,
            path=map_path,
        )

    return _vis_checker


def check_player_visibility(local_pos, entity_pos, vis_checker_obj, eye_offset=64.0):
    if vis_checker_obj is None or local_pos is None or entity_pos is None:
        return True
    try:
        lx, ly, lz = float(local_pos[0]), float(local_pos[1]), float(local_pos[2]) + float(eye_offset)
        tx, ty, tz = float(entity_pos[0]), float(entity_pos[1]), float(entity_pos[2]) + float(eye_offset)
    except Exception:
        return True
    try:
        if hasattr(vis_checker_obj, "is_visible"):
            result = vis_checker_obj.is_visible((lx, ly, lz), (tx, ty, tz))
            return bool(result) if result is not None else True
        if hasattr(vis_checker_obj, "trace"):
            dx, dy, dz = (tx - lx), (ty - ly), (tz - lz)
            result = vis_checker_obj.trace(lx, ly, lz, dx, dy, dz)
            return bool(result) if result is not None else True
    except Exception:
        return True
    return True


def collect_team_and_spectator_info(pm, entity_ptr, entity_list):
    t_players = []
    ct_players = []
    spectators = []
    if not pm or not entity_ptr or not entity_list:
        return t_players, ct_players, spectators

    for i in range(1, 65):
        try:
            entity_controller = pm.read_longlong(entity_ptr + 0x70 * (i & 0x1FF))
            if not entity_controller:
                continue
            handle = pm.read_longlong(entity_controller + m_hPlayerPawn)
            if not handle:
                continue
            ent_list_pawn = pm.read_longlong(entity_list + 0x8 * ((handle & 0x7FFF) >> 0x9) + 0x10)
            if not ent_list_pawn:
                continue
            pawn = pm.read_longlong(ent_list_pawn + 0x70 * (handle & 0x1FF))
            if not pawn:
                continue

            name = (pm.read_string(entity_controller + m_iszPlayerName, 32) or "").strip() or f"Player {i}"
            team = pm.read_int(pawn + m_iTeamNum) or 0
            hp = pm.read_int(pawn + m_iHealth) or 0
            life = pm.read_int(pawn + m_lifeState) or 0

            if hp > 0 and life == 256:
                if team == 2:
                    t_players.append(name)
                elif team == 3:
                    ct_players.append(name)
                continue

            if name not in spectators:
                spectators.append(name)
        except Exception:
            continue

    return t_players, ct_players, spectators


def draw_info_box(draw_list, x, y, title, lines, color=(1.0, 1.0, 1.0, 1.0)):
    line_height = 16
    width = 240
    height = 30 + max(1, len(lines)) * line_height
    bg = imgui.get_color_u32_rgba(0.08, 0.08, 0.1, 0.86)
    border = imgui.get_color_u32_rgba(0.35, 0.35, 0.45, 0.9)
    title_col = imgui.get_color_u32_rgba(0.92, 0.92, 0.98, 1.0)
    text_col = imgui.get_color_u32_rgba(*color)
    draw_list.add_rect_filled(x, y, x + width, y + height, bg, 6.0)
    draw_list.add_rect(x, y, x + width, y + height, border, 6.0, thickness=1.0)
    draw_list.add_text(x + 8, y + 7, title_col, title)
    line_y = y + 28
    for line in lines:
        draw_list.add_text(x + 8, line_y, text_col, str(line))
        line_y += line_height


def draw_radar(draw_list, snapshot, settings_proxy):
    if not snapshot:
        return
    local = snapshot.get("local")
    entities = snapshot.get("entities", [])
    if not local or not entities:
        return

    radar_size = int(settings_proxy.get("radar_size", 220))
    radar_x = int(settings_proxy.get("radar_x", 40))
    radar_y = int(settings_proxy.get("radar_y", 140))
    radar_range = max(100.0, float(settings_proxy.get("radar_range_units", 3000.0)))
    fixed_range = bool(settings_proxy.get("radar_fixed_range", False))
    show_team = bool(settings_proxy.get("radar_show_team", True))
    show_me_dir = bool(settings_proxy.get("radar_show_me_dir", True))
    show_enemy_dir = bool(settings_proxy.get("radar_show_enemy_dir", True))
    show_team_dir = bool(settings_proxy.get("radar_show_team_dir", False))
    radar_alpha = max(40, min(255, int(settings_proxy.get("radar_alpha", 235))))
    alpha = radar_alpha / 255.0

    lpx, lpy = float(local.get("x", 0.0)), float(local.get("y", 0.0))
    lyaw = math.radians(float(local.get("yaw", 0.0)))
    sin_y = math.sin(-lyaw)
    cos_y = math.cos(-lyaw)
    center_x = radar_x + radar_size / 2.0
    center_y = radar_y + radar_size / 2.0
    scale = (radar_size / 2.0) / radar_range

    if not fixed_range:
        farthest = 0.0
        for ent in entities:
            try:
                team = int(ent.get("team", 0))
                if team == int(local.get("team", 0)) and not show_team:
                    continue
                dx = float(ent.get("x", 0.0)) - lpx
                dy = float(ent.get("y", 0.0)) - lpy
                farthest = max(farthest, math.hypot(dx, dy))
            except Exception:
                continue
        if farthest > 0.0:
            radar_range = max(600.0, min(12000.0, farthest * 1.2))

    bg = imgui.get_color_u32_rgba(0.08, 0.08, 0.12, 0.86 * alpha)
    border = imgui.get_color_u32_rgba(0.35, 0.35, 0.45, 0.95 * alpha)
    axis = imgui.get_color_u32_rgba(0.25, 0.25, 0.3, 0.65 * alpha)
    draw_list.add_rect_filled(radar_x, radar_y, radar_x + radar_size, radar_y + radar_size, bg, 6.0)
    draw_list.add_rect(radar_x, radar_y, radar_x + radar_size, radar_y + radar_size, border, 6.0, thickness=1.0)
    draw_list.add_line(center_x, radar_y, center_x, radar_y + radar_size, axis, 1.0)
    draw_list.add_line(radar_x, center_y, radar_x + radar_size, center_y, axis, 1.0)
    draw_list.add_text(radar_x + 8, radar_y + 8, imgui.get_color_u32_rgba(0.95, 0.95, 0.98, 1.0 * alpha), "RADAR")

    if show_me_dir:
        dir_len = 15.0
        dx = math.cos(lyaw) * dir_len
        dy = math.sin(lyaw) * dir_len
        draw_list.add_line(center_x, center_y, center_x + dx, center_y + dy, imgui.get_color_u32_rgba(0.95, 0.95, 0.98, 0.95 * alpha), 1.5)

    for ent in entities:
        try:
            team = int(ent.get("team", 0))
            if team == int(local.get("team", 0)) and not show_team:
                continue
            dx = float(ent["x"]) - lpx
            dy = float(ent["y"]) - lpy
            rx = (dx * cos_y - dy * sin_y) * scale
            ry = (dx * sin_y + dy * cos_y) * scale
            rx = max(-radar_size / 2 + 5, min(radar_size / 2 - 5, rx))
            ry = max(-radar_size / 2 + 5, min(radar_size / 2 - 5, ry))
            px = center_x + rx
            py = center_y + ry
            is_team = team == int(local.get("team", 0))
            if is_team:
                col = imgui.get_color_u32_rgba(0.0, 0.85, 0.35, 0.95 * alpha)
            else:
                col = imgui.get_color_u32_rgba(0.95, 0.22, 0.22, 0.95 * alpha)
            draw_list.add_circle_filled(px, py, 3.0, col)

            ent_yaw = ent.get("yaw", None)
            if ent_yaw is not None and ((is_team and show_team_dir) or ((not is_team) and show_enemy_dir)):
                ey = math.radians(float(ent_yaw))
                exdx = math.cos(ey) * 8.0
                exdy = math.sin(ey) * 8.0
                draw_list.add_line(px, py, px + exdx, py + exdy, col, 1.0)
        except Exception:
            continue

# ==============================
# SECTION 5: MENU / UI CONTROLS
# ==============================

win32_key_map = {
    "NONE": 0,
    "MOUSE1": win32con.VK_LBUTTON,
    "MOUSE2": win32con.VK_RBUTTON,
    "MOUSE3": win32con.VK_MBUTTON,
    "MOUSE4": win32con.VK_XBUTTON1,
    "MOUSE5": win32con.VK_XBUTTON2,
    "LSHIFT": win32con.VK_LSHIFT,
    "LEFT_SHIFT": win32con.VK_LSHIFT,
    "RSHIFT": win32con.VK_RSHIFT,
    "RIGHT_SHIFT": win32con.VK_RSHIFT,
    "LCTRL": win32con.VK_LCONTROL,
    "LEFT_CTRL": win32con.VK_LCONTROL,
    "RCTRL": win32con.VK_RCONTROL,
    "RIGHT_CTRL": win32con.VK_RCONTROL,
    "LALT": win32con.VK_LMENU,
    "LEFT_ALT": win32con.VK_LMENU,
    "RALT": win32con.VK_RMENU,
    "RIGHT_ALT": win32con.VK_RMENU,
    "SPACE": win32con.VK_SPACE,
    "ENTER": win32con.VK_RETURN,
    "ESCAPE": win32con.VK_ESCAPE,
    "DELETE": win32con.VK_DELETE,
    "INSERT": win32con.VK_INSERT,
    "TAB": win32con.VK_TAB,
    "UP": win32con.VK_UP,
    "DOWN": win32con.VK_DOWN,
    "LEFT": win32con.VK_LEFT,
    "RIGHT": win32con.VK_RIGHT,
    "F1": win32con.VK_F1, "F2": win32con.VK_F2, "F3": win32con.VK_F3,
    "F4": win32con.VK_F4, "F5": win32con.VK_F5, "F6": win32con.VK_F6,
    "F7": win32con.VK_F7, "F8": win32con.VK_F8, "F9": win32con.VK_F9,
    "F10": win32con.VK_F10, "F11": win32con.VK_F11, "F12": win32con.VK_F12,
    "A": ord('A'), "B": ord('B'), "C": ord('C'), "D": ord('D'), "E": ord('E'),
    "F": ord('F'), "G": ord('G'), "H": ord('H'), "I": ord('I'), "J": ord('J'),
    "K": ord('K'), "L": ord('L'), "M": ord('M'), "N": ord('N'), "O": ord('O'),
    "P": ord('P'), "Q": ord('Q'), "R": ord('R'), "S": ord('S'), "T": ord('T'),
    "U": ord('U'), "V": ord('V'), "W": ord('W'), "X": ord('X'), "Y": ord('Y'),
    "Z": ord('Z'),
    "0": ord('0'), "1": ord('1'), "2": ord('2'), "3": ord('3'), "4": ord('4'),
    "5": ord('5'), "6": ord('6'), "7": ord('7'), "8": ord('8'), "9": ord('9'),
}


color_accent = (0.55, 0.00, 0.55, 1.00)
color_bg_dark = (0.08, 0.08, 0.08, 1.00)
color_item_bg = (0.15, 0.15, 0.15, 1.00)
color_text = (0.90, 0.90, 0.90, 1.00)
color_border = (0.25, 0.25, 0.25, 0.50)

def setup_imgui_style():
    global color_accent, color_bg_dark, color_item_bg, color_text, color_border
    style = imgui.get_style()
    style.window_rounding = 3
    style.frame_rounding = 3
    style.grab_rounding = 3
    style.scrollbar_rounding = 3
    style.window_padding = (8, 8)
    style.frame_padding = (6, 4)
    style.item_spacing = (8, 6)
    style.scrollbar_size = 10

    colors = style.colors
    colors[imgui.COLOR_WINDOW_BACKGROUND] = color_bg_dark
    colors[imgui.COLOR_BORDER] = color_border
    colors[imgui.COLOR_FRAME_BACKGROUND] = color_item_bg
    colors[imgui.COLOR_FRAME_BACKGROUND_HOVERED] = (0.20, 0.20, 0.20, 1.0)
    colors[imgui.COLOR_FRAME_BACKGROUND_ACTIVE] = (0.25, 0.25, 0.25, 1.0)
    colors[imgui.COLOR_CHECK_MARK] = color_accent
    colors[imgui.COLOR_SLIDER_GRAB] = color_accent
    colors[imgui.COLOR_SLIDER_GRAB_ACTIVE] = (0.70, 0.00, 0.55, 1.0)
    colors[imgui.COLOR_HEADER] = color_accent
    colors[imgui.COLOR_HEADER_HOVERED] = (0.65, 0.00, 0.55, 1.0)
    colors[imgui.COLOR_HEADER_ACTIVE] = (0.50, 0.00, 0.55, 1.0)
    colors[imgui.COLOR_SCROLLBAR_BACKGROUND] = (0.10, 0.10, 0.10, 1.0)
    colors[imgui.COLOR_SCROLLBAR_GRAB] = color_item_bg
    colors[imgui.COLOR_TEXT] = color_text
    colors[imgui.COLOR_TEXT_DISABLED] = (0.50, 0.50, 0.50, 1.0)
    colors[imgui.COLOR_BUTTON] = color_accent
    colors[imgui.COLOR_BUTTON_HOVERED] = (0.65, 0.00, 0.55, 1.0)
    colors[imgui.COLOR_BUTTON_ACTIVE] = (0.50, 0.00, 0.55, 1.0)

def custom_tab_bar(tabs, current_tab, width, icon_font, main_font, tab_animations):
    global color_accent
    imgui.begin_child("##tabbar", width, 0, border=False)

    for i, tab in enumerate(tabs):
        button_height = 90
        pos = imgui.get_cursor_pos()
        is_selected = (current_tab == i)
        anim = tab_animations[i]

        if imgui.invisible_button(f"##tab_{i}", width, button_height):
            current_tab = i

        draw_list = imgui.get_window_draw_list()
        if anim > 0.001:
            col = list(color_accent)
            col[3] *= anim
            draw_list.add_rect_filled(
                *imgui.get_item_rect_min(), *imgui.get_item_rect_max(),
                imgui.get_color_u32_rgba(*col)
            )
        if imgui.is_item_hovered() and not is_selected:
            draw_list.add_rect_filled(
                *imgui.get_item_rect_min(), *imgui.get_item_rect_max(),
                imgui.get_color_u32_rgba(0.2, 0.2, 0.2, 0.3)
            )
        pushed_icon = _font_push_safe(icon_font)
        icon_size = imgui.calc_text_size(tab["icon"])
        imgui.set_cursor_pos((
            pos[0] + (width - icon_size.x) * 0.5,
            pos[1] + 20
        ))
        imgui.text(tab["icon"])
        _font_pop_safe(pushed_icon)
        
        pushed_main = _font_push_safe(main_font)
        text_width = imgui.calc_text_size(tab["name"]).x
        imgui.set_cursor_pos((
            pos[0] + (width - text_width) * 0.5,
            pos[1] + button_height - imgui.get_text_line_height() - 20
        ))
        imgui.text(tab["name"])
        _font_pop_safe(pushed_main)

        imgui.set_cursor_pos((pos[0], pos[1] + button_height))

    imgui.end_child()
    return current_tab

def section_header(label, font):
    global color_accent
    pushed = _font_push_safe(font)
    imgui.push_style_color(imgui.COLOR_TEXT, *color_accent)
    imgui.text(label.upper())
    imgui.pop_style_color()
    imgui.separator()
    _font_pop_safe(pushed)

def custom_checkbox(label, state, font):
    pushed = _font_push_safe(font)
    imgui.push_style_var(imgui.STYLE_FRAME_ROUNDING, 3)
    changed, state = imgui.checkbox(f"##{label}", state)
    imgui.same_line()
    imgui.text(label)
    imgui.pop_style_var()
    _font_pop_safe(pushed)
    return changed, state

def custom_slider_float(label, value, v_min, v_max, format="%.2f", font=None):
    global color_accent, color_item_bg
    pushed = _font_push_safe(font)
    imgui.push_style_color(imgui.COLOR_FRAME_BACKGROUND, *color_item_bg)
    imgui.push_style_color(imgui.COLOR_SLIDER_GRAB, *color_accent)
    changed, value = imgui.slider_float(f"##{label}", value, v_min, v_max, format=format)
    imgui.pop_style_color(2)
    imgui.same_line()
    imgui.text(label)
    _font_pop_safe(pushed)
    return changed, value

def custom_combo(label, current_item, items, font):
    global color_accent, color_item_bg
    pushed = _font_push_safe(font)
    imgui.push_style_color(imgui.COLOR_FRAME_BACKGROUND, *color_item_bg)
    imgui.push_style_color(imgui.COLOR_HEADER, *color_accent)
    imgui.push_style_color(imgui.COLOR_BUTTON, *color_item_bg)
    imgui.push_style_color(imgui.COLOR_BUTTON_HOVERED, *color_item_bg)
    imgui.push_style_color(imgui.COLOR_BUTTON_ACTIVE, *color_item_bg)
    
    if isinstance(current_item, str):
        original_is_string = True
        try:
            current_index = items.index(current_item)
        except Exception:
            current_index = 0
    else:
        original_is_string = False
        try:
            current_index = int(current_item)
        except Exception:
            current_index = 0

    current_index = max(0, min(current_index, len(items) - 1)) if items else 0
    preview_value = items[current_index] if items else ""

    new_item = None
    if imgui.begin_combo(f"##{label}", preview_value):
        for i, item in enumerate(items):
            is_selected = (i == current_index)
            if imgui.selectable(item, is_selected)[0]:
                new_item = item if original_is_string else i
            if is_selected:
                imgui.set_item_default_focus()
        imgui.end_combo()
    
    imgui.same_line()
    imgui.text(label)
    imgui.pop_style_color(5)
    _font_pop_safe(pushed)
    return new_item

def color_cube(label, color, font):
    global color_item_bg
    pushed = _font_push_safe(font)
    imgui.push_style_color(imgui.COLOR_FRAME_BACKGROUND, *color_item_bg)
    flags = (
        imgui.COLOR_EDIT_ALPHA_BAR | 
        imgui.COLOR_EDIT_ALPHA_PREVIEW |
        imgui.COLOR_EDIT_NO_INPUTS
    )
    changed, new_color = imgui.color_edit4(f"##{label}", *color, flags=flags)
    
    imgui.same_line()
    imgui.text(label)
    imgui.pop_style_color()
    _font_pop_safe(pushed)
    return changed, new_color

def draw_esp_preview(settings, font):
    draw_list = imgui.get_window_draw_list()
    pos = imgui.get_cursor_screen_pos()
    size = imgui.get_content_region_available()
    
    center_x = pos.x + size.x * 0.5
    center_y = pos.y + size.y * 0.5
    
    box_w = size.x * 0.6
    box_h = box_w * 2.0
    
    x1, y1 = center_x - box_w / 2, center_y - box_h / 2
    x2, y2 = center_x + box_w / 2, center_y + box_h / 2
    
    head = (center_x, y1 + box_h * 0.1)
    neck = (center_x, y1 + box_h * 0.2)
    l_shoulder = (center_x - box_w * 0.3, y1 + box_h * 0.25)
    r_shoulder = (center_x + box_w * 0.3, y1 + box_h * 0.25)
    l_elbow = (center_x - box_w * 0.4, y1 + box_h * 0.4)
    r_elbow = (center_x + box_w * 0.4, y1 + box_h * 0.4)
    spine = (center_x, y1 + box_h * 0.45)
    l_hip = (center_x - box_w * 0.2, y1 + box_h * 0.5)
    r_hip = (center_x + box_w * 0.2, y1 + box_h * 0.5)
    l_knee = (center_x - box_w * 0.22, y1 + box_h * 0.75)
    r_knee = (center_x + box_w * 0.22, y1 + box_h * 0.75)
    l_foot = (center_x - box_w * 0.2, y2)
    r_foot = (center_x + box_w * 0.2, y2)
    connections = [
    (neck, l_shoulder), (neck, r_shoulder), (l_shoulder, l_elbow), (r_shoulder, r_elbow),
    (neck, spine), (spine, l_hip), (spine, r_hip), (l_hip, l_knee), (r_hip, r_knee),
    (l_knee, l_foot), (r_knee, r_foot)
    ]

    if settings.get("esp_filled_box"):
        draw_list.add_rect_filled(x1, y1, x2, y2, imgui.get_color_u32_rgba(*settings.get("esp_box_fill_spotted_color")))
        
    if settings.get("esp_box"):
        draw_list.add_rect(x1, y1, x2, y2, imgui.get_color_u32_rgba(*settings.get("esp_box_border_color")), thickness=1.0)
        
    if settings.get("esp_skeleton"):
        col = imgui.get_color_u32_rgba(*settings.get("esp_skeleton_color"))
        for p1, p2 in connections:
            draw_list.add_line(p1[0], p1[1], p2[0], p2[1], col, 1.0)

    if settings.get("esp_corners"):
        corner_len = box_w * 0.3
        col = imgui.get_color_u32_rgba(*settings.get("esp_enemy_color"))
        draw_list.add_line(x1, y1, x1 + corner_len, y1, col, 1.0); draw_list.add_line(x1, y1, x1, y1 + corner_len, col, 1.0)
        draw_list.add_line(x2, y1, x2 - corner_len, y1, col, 1.0); draw_list.add_line(x2, y1, x2, y1 + corner_len, col, 1.0)
        draw_list.add_line(x1, y2, x1 + corner_len, y2, col, 1.0); draw_list.add_line(x1, y2, x1, y2 - corner_len, col, 1.0)
        draw_list.add_line(x2, y2, x2 - corner_len, y2, col, 1.0); draw_list.add_line(x2, y2, x2, y2 - corner_len, col, 1.0)
        
    if settings.get("esp_health_bar"):
        hb_x = x1 - 6
        draw_list.add_line(hb_x, y1, hb_x, y2, imgui.get_color_u32_rgba(*settings.get("esp_health_bar_bg_color")), 2.0)
        draw_list.add_line(hb_x, y1, hb_x, y2, imgui.get_color_u32_rgba(*settings.get("esp_health_bar_color")), 2.0)
        
    if settings.get("esp_armor_bar"):
        ab_y = y2 + 4
        draw_list.add_line(x1, ab_y, x2, ab_y, imgui.get_color_u32_rgba(*settings.get("esp_health_bar_bg_color")), 2.0)
        draw_list.add_line(x1, ab_y, x2, ab_y, imgui.get_color_u32_rgba(*settings.get("esp_armor_bar_color")), 2.0)
        
    if settings.get("esp_head_dot"):
        draw_list.add_circle_filled(head[0], head[1], 15, imgui.get_color_u32_rgba(*settings.get("esp_head_dot_color")))
    
    pushed = _font_push_safe(font)
    if settings.get("esp_names"):
        name_text = "Player"
        name_w, _ = imgui.calc_text_size(name_text)
        draw_list.add_text(center_x - name_w / 2, y1 - 20, imgui.get_color_u32_rgba(*settings.get("esp_name_color")), name_text)
        
    if settings.get("esp_weapons"):
        wep_text = "Weapon"
        wep_w, _ = imgui.calc_text_size(wep_text)
        draw_list.add_text(center_x - wep_w / 2, y2 + 8, imgui.get_color_u32_rgba(*settings.get("esp_weapon_color")), wep_text)
    _font_pop_safe(pushed)

def custom_button(label, font):
    pushed = _font_push_safe(font)
    clicked = imgui.button(label)
    _font_pop_safe(pushed)
    return clicked

def custom_text_input(label, value, buffer_length, font):
    pushed = _font_push_safe(font)
    imgui.text(label)
    imgui.same_line()
    changed, new_value = imgui.input_text(f"##{label}", value, buffer_length)
    _font_pop_safe(pushed)
    return changed, new_value

key_map = {
    "NONE": 0, "MOUSE1": glfw.MOUSE_BUTTON_1, "MOUSE2": glfw.MOUSE_BUTTON_2, "MOUSE3": glfw.MOUSE_BUTTON_3,
    "MOUSE4": glfw.MOUSE_BUTTON_4, "MOUSE5": glfw.MOUSE_BUTTON_5, "MOUSEWHEEL_UP": -1, "MOUSEWHEEL_DOWN": -2,
    "LSHIFT": glfw.KEY_LEFT_SHIFT, "RSHIFT": glfw.KEY_RIGHT_SHIFT, "LCTRL": glfw.KEY_LEFT_CONTROL,
    "RCTRL": glfw.KEY_RIGHT_CONTROL, "LALT": glfw.KEY_LEFT_ALT, "RALT": glfw.KEY_RIGHT_ALT,
    "SPACE": glfw.KEY_SPACE, "ENTER": glfw.KEY_ENTER, "ESCAPE": glfw.KEY_ESCAPE, "TAB": glfw.KEY_TAB,
    "DELETE": glfw.KEY_DELETE,
    "UP": glfw.KEY_UP, "DOWN": glfw.KEY_DOWN, "LEFT": glfw.KEY_LEFT, "RIGHT": glfw.KEY_RIGHT,
    "F1": glfw.KEY_F1, "F2": glfw.KEY_F2, "F3": glfw.KEY_F3, "F4": glfw.KEY_F4, "F5": glfw.KEY_F5,
    "F6": glfw.KEY_F6, "F7": glfw.KEY_F7, "F8": glfw.KEY_F8, "F9": glfw.KEY_F9, "F10": glfw.KEY_F10,
    "F11": glfw.KEY_F11, "F12": glfw.KEY_F12, "A": glfw.KEY_A, "B": glfw.KEY_B, "C": glfw.KEY_C,
    "D": glfw.KEY_D, "E": glfw.KEY_E, "F": glfw.KEY_F, "G": glfw.KEY_G, "H": glfw.KEY_H, "I": glfw.KEY_I,
    "J": glfw.KEY_J, "K": glfw.KEY_K, "L": glfw.KEY_L, "M": glfw.KEY_M, "N": glfw.KEY_N, "O": glfw.KEY_O,
    "P": glfw.KEY_P, "Q": glfw.KEY_Q, "R": glfw.KEY_R, "S": glfw.KEY_S, "T": glfw.KEY_T, "U": glfw.KEY_U,
    "V": glfw.KEY_V, "W": glfw.KEY_W, "X": glfw.KEY_X, "Y": glfw.KEY_Y, "Z": glfw.KEY_Z, "0": glfw.KEY_0,
    "1": glfw.KEY_1, "2": glfw.KEY_2, "3": glfw.KEY_3, "4": glfw.KEY_4, "5": glfw.KEY_5, "6": glfw.KEY_6,
    "7": glfw.KEY_7, "8": glfw.KEY_8, "9": glfw.KEY_9,
}

code_to_name = {v: k for k, v in key_map.items()}

def key_bind(label, current_key, font):
    global color_accent
    pushed = _font_push_safe(font)
    
    popup_id = f"Set Key##{label}"
    is_binding = imgui.is_popup_open(popup_id)
    new_key_value = None
    
    imgui.push_style_color(imgui.COLOR_BUTTON, *color_accent)
    imgui.push_style_color(imgui.COLOR_BUTTON_HOVERED, *(0.65, 0.00, 0.55, 1.0))
    imgui.push_style_color(imgui.COLOR_BUTTON_ACTIVE, *(0.50, 0.00, 0.55, 1.0))
    
    btn_text = "..." if is_binding else (current_key if current_key != "NONE" else "bind")
    
    if imgui.button(f"{btn_text}##{label}"):
        imgui.open_popup(popup_id)

    if imgui.is_item_hovered() and not is_binding:
        imgui.set_tooltip("Click to bind\nRight-click to clear")
        if imgui.is_mouse_clicked(1):
            new_key_value = "NONE"

    if imgui.begin_popup(popup_id):
        imgui.text("Press any key...")
        imgui.separator()
        imgui.text("[DEL] or [Right-Click] to clear")
        
        io = imgui.get_io()
        
        if imgui.is_key_pressed(glfw.KEY_DELETE):
            new_key_value = "NONE"
            imgui.close_current_popup()
        
        if io.mouse_wheel < 0:
            new_key_value = "MOUSEWHEEL_DOWN"
            imgui.close_current_popup()
        elif io.mouse_wheel > 0:
            new_key_value = "MOUSEWHEEL_UP"
            imgui.close_current_popup()
        
        for i in range(5):
            if imgui.is_mouse_clicked(i):
                new_key_value = f"MOUSE{i+1}"
                imgui.close_current_popup()
                break
        
        if new_key_value is None:
            for code, name in code_to_name.items():
                if code > 0 and imgui.is_key_pressed(code):
                    new_key_value = name
                    imgui.close_current_popup()
                    break
        
        imgui.end_popup()
    
    imgui.same_line()
    imgui.text(label)
    imgui.pop_style_color(3)
    _font_pop_safe(pushed)
    
    return new_key_value


# ==============================
# SECTION 6: FEATURE WORKERS
# ==============================

class Aimbot:
    def __init__(self, settings):
        self.settings = settings
        self.locked_target = 0
        self.prev_target = 0
        self.last_switch_time = 0.0
        self.shots_fired = 0
        self.smooth_ramp = 0.0
        self.last_aim_key_down = False
        self.client, self.pm = get_descriptor_blocking()
        self.sensitivity = 0.022
        self.bone_name_map = {
            "head": "head",
            "neck": "neck",
            "chest": "spine",
            "spine": "spine",
            "pelvis": "pelvis",
            "left_hand": "left_wrist",
            "right_hand": "right_wrist",
            "left_leg": "left_knee",
            "right_leg": "right_knee",
            "left_foot": "left_ankle",
            "right_foot": "right_ankle",
        }
        self._last_sens_read = 0.0
        self._entity_cache = []
        self._entity_cache_time = 0.0

    @staticmethod
    def _clamp(value, mn, mx):
        return mn if value < mn else mx if value > mx else value

    @staticmethod
    def _angle_diff(a, b):
        return (a - b + 180.0) % 360.0 - 180.0

    def _normalize(self, pitch, yaw):
        if math.isnan(pitch) or math.isnan(yaw):
            return 0.0, 0.0
        pitch = self._clamp(pitch, -89.0, 89.0)
        yaw = (yaw + 180.0) % 360.0 - 180.0
        return pitch, yaw

    @staticmethod
    def _ease_in_out_quad(t):
        t = max(0.0, min(1.0, t))
        return 2.0 * t * t if t < 0.5 else -1.0 + (4.0 - 2.0 * t) * t

    def _read_view_angles(self):
        view = self.pm.read_bytes(self.client + dwViewAngles, 8)
        if not view:
            return 0.0, 0.0
        return struct.unpack("ff", view)

    def _calc_angle(self, src, dst):
        dx, dy, dz = (dst[0] - src[0], dst[1] - src[1], dst[2] - src[2])
        hyp = math.hypot(dx, dy)
        pitch = -math.degrees(math.atan2(dz, hyp))
        yaw = math.degrees(math.atan2(dy, dx))
        return self._normalize(pitch, yaw)

    def _read_sensitivity(self):
        now = time.time()
        if now - self._last_sens_read < 0.35:
            return max(0.001, float(self.sensitivity))
        self._last_sens_read = now
        try:
            sens_ptr = self.pm.read_longlong(self.client + dwSensitivity)
            if sens_ptr:
                sens = self.pm.read_float(sens_ptr + dwSensitivity_sensitivity)
                if sens and sens > 0:
                    self.sensitivity = sens
        except Exception:
            pass
        return max(0.001, float(self.sensitivity))

    def _read_bone_world_pos(self, pawn, bone_name):
        mapped = self.bone_name_map.get(str(bone_name).lower().strip(), "head")
        bone_idx = bone_ids.get(mapped, bone_ids["head"])
        scene = self.pm.read_longlong(pawn + m_pGameSceneNode)
        if not scene:
            return None
        bone_matrix = self.pm.read_longlong(scene + m_modelState + 0x80)
        if not bone_matrix:
            return None
        data = self.pm.read_bytes(bone_matrix + bone_idx * 0x20, 12)
        if not data:
            return None
        return list(struct.unpack("fff", data))

    def _target_bones(self, cfg):
        if cfg.get("aimbot_closest_to_crosshair", False):
            raw = cfg.get("aimbot_bone_list", "head,neck,chest,pelvis")
            bones = [b.strip().lower() for b in str(raw).split(",") if b.strip()]
            return bones or ["head"]
        return [str(cfg.get("aimbot_target_bone", "head")).strip().lower()]

    def _effective_fov(self, base_fov, dist_sq, cfg):
        base = max(1.0, float(base_fov))
        if not cfg.get("aim_dynamic_fov_enabled", False) or dist_sq <= 0:
            set_current_dynamic_fov(base)
            return base
        dist = math.sqrt(dist_sq)
        max_dist = max(1.0, float(cfg.get("aim_dynamic_fov_max_distance", 3000.0)))
        min_scale = float(cfg.get("aim_dynamic_fov_min_scale", 0.5))
        max_scale = max(min_scale, float(cfg.get("aim_dynamic_fov_max_scale", 1.5)))
        t = self._clamp(dist / max_dist, 0.0, 1.0)
        eff = base * (min_scale + (max_scale - min_scale) * t)
        set_current_dynamic_fov(eff)
        return eff

    def _select_target(self, my_pos, my_team, pitch, yaw, entity_ptr, entity_list, local_pawn, vis_checker, cfg):
        best = None
        best_metric = float("inf")
        attack_all = bool(cfg.get("aim_attack_all", False)) or bool(cfg.get("aimbot_deathmatch_mode", False))
        vis_check = bool(cfg.get("aimbot_visibility_check", True)) and bool(cfg.get("visibility_aim_enabled", True))
        vel_predict = bool(cfg.get("aimbot_velocity_prediction", True))
        vel_factor = float(cfg.get("aimbot_velocity_factor", 1.0))
        eye_height = float(cfg.get("aimbot_eye_height", 64.0))
        frame_time = 1.0 / max(30.0, float(cfg.get("aimbot_tick_rate", 60.0)))
        base_fov = float(cfg.get("aimbot_fov", 40.0))
        max_entities = max(1, min(64, int(cfg.get("aimbot_max_entities", 64))))
        cache_refresh = max(0.01, float(cfg.get("aimbot_entity_cache_refresh", 0.2)))
        now = time.time()

        if now - self._entity_cache_time >= cache_refresh:
            fresh_entities = []
            for i in range(1, max_entities + 1):
                entity_data = client_mem(self.pm, i, entity_ptr, entity_list, local_pawn, my_team)
                if entity_data:
                    fresh_entities.append(entity_data)
            self._entity_cache = fresh_entities
            self._entity_cache_time = now

        for ent_team, _, pawn, _, spotted in self._entity_cache:
            if ent_team == my_team and not attack_all:
                continue
            if vis_check and vis_checker is None and (not spotted):
                continue
            immunity = esp_immunity(self.pm, pawn)
            if immunity and ent_team == my_team:
                continue

            bone_choice = None
            for bone_name in self._target_bones(cfg):
                pos = self._read_bone_world_pos(pawn, bone_name)
                if not pos:
                    continue
                if vel_predict:
                    vel = read_vec3(self.pm, pawn + m_vecVelocity)
                    if vel:
                        pos[0] += vel[0] * frame_time * vel_factor
                        pos[1] += vel[1] * frame_time * vel_factor
                        pos[2] += vel[2] * frame_time * vel_factor
                pos[2] -= float(cfg.get("aimbot_downward_offset", 0.0))
                if vis_check and vis_checker is not None:
                    if not check_player_visibility(my_pos, pos, vis_checker, eye_offset=eye_height):
                        continue
                tp, ty = self._calc_angle((my_pos[0], my_pos[1], my_pos[2] + eye_height), pos)
                dp = self._angle_diff(tp, pitch)
                dy = self._angle_diff(ty, yaw)
                dist_sq = (pos[0] - my_pos[0]) ** 2 + (pos[1] - my_pos[1]) ** 2 + (pos[2] - my_pos[2]) ** 2
                effective_fov = self._effective_fov(base_fov, dist_sq, cfg)
                if abs(dp) > effective_fov or abs(dy) > effective_fov:
                    continue
                metric = math.hypot(dp, dy)
                if bone_choice is None or metric < bone_choice["metric"]:
                    bone_choice = {"pos": pos, "pitch": tp, "yaw": ty, "metric": metric, "dist_sq": dist_sq}

            if bone_choice and bone_choice["metric"] < best_metric:
                best_metric = bone_choice["metric"]
                best = {"pawn": pawn, **bone_choice}
        return best

    def run(self):
        loop_cfg = {}
        while True:
            try:
                loop_cfg = self.settings.snapshot(
                    (
                        "aim_stop",
                        "master_enabled",
                        "aimbot_enable",
                        "aimbot_always_on",
                        "aimbot_key",
                        "aimbot_closest_to_crosshair",
                        "aimbot_bone_list",
                        "aimbot_target_bone",
                        "aim_attack_all",
                        "aimbot_deathmatch_mode",
                        "aimbot_visibility_check",
                        "visibility_aim_enabled",
                        "aimbot_velocity_prediction",
                        "aimbot_velocity_factor",
                        "aimbot_eye_height",
                        "aimbot_tick_rate",
                        "aimbot_fov",
                        "aimbot_max_entities",
                        "aimbot_entity_cache_refresh",
                        "aimbot_downward_offset",
                        "aim_dynamic_fov_enabled",
                        "aim_dynamic_fov_max_distance",
                        "aim_dynamic_fov_min_scale",
                        "aim_dynamic_fov_max_scale",
                        "aimbot_stickiness_time",
                        "aimbot_rcs_enabled",
                        "aimbot_rcs_scale",
                        "aimbot_deadzone",
                        "aimbot_speed",
                        "aimbot_smooth_ramp_speed",
                        "aimbot_ease_out",
                        "aimbot_overshoot_chance",
                        "aimbot_overshoot_strength",
                        "aimbot_invert_y",
                        "aimbot_max_mouse_move",
                        "debug_worker_crashes",
                    )
                )
                if loop_cfg.get("aim_stop", False):
                    break
                if not loop_cfg.get("master_enabled", True):
                    self.locked_target = 0
                    self.last_aim_key_down = False
                    _sleep_master_off(0.18)
                    continue
                if not is_cs2_window_active() or not loop_cfg.get("aimbot_enable", False):
                    self.locked_target = 0
                    self.last_aim_key_down = False
                    _sleep_idle(0.10)
                    continue

                always_on = bool(loop_cfg.get("aimbot_always_on", False))
                key_code = win32_key_map.get(str(loop_cfg.get("aimbot_key", "MOUSE5")).upper(), 0)
                key_down = always_on or (key_code > 0 and (win32api.GetAsyncKeyState(key_code) & 0x8000))
                if not key_down:
                    if self.last_aim_key_down:
                        self.locked_target = 0
                        self.shots_fired = 0
                        self.smooth_ramp = 0.0
                    self.last_aim_key_down = False
                    _sleep_idle(0.05)
                    continue
                self.last_aim_key_down = True

                view_matrix, local_pawn, local_team, entity_list, entity_ptr = offsets_mem(self.pm, self.client)
                if not local_pawn or not local_team or not entity_ptr:
                    _sleep_active(0.01)
                    continue

                my_pos = read_vec3(self.pm, local_pawn + m_vOldOrigin)
                pitch, yaw = self._read_view_angles()
                use_vis = bool(loop_cfg.get("aimbot_visibility_check", True)) and bool(loop_cfg.get("visibility_aim_enabled", True))
                vis_checker = ensure_vischeck_ready(self.pm, self.settings) if use_vis else None
                target = self._select_target(
                    my_pos,
                    local_team,
                    pitch,
                    yaw,
                    entity_ptr,
                    entity_list,
                    local_pawn,
                    vis_checker,
                    loop_cfg,
                )
                if not target:
                    self.locked_target = 0
                    self.smooth_ramp = 0.0
                    _sleep_active(0.006)
                    continue

                if target["pawn"] != self.locked_target:
                    stickiness = float(loop_cfg.get("aimbot_stickiness_time", 0.18))
                    now = time.time()
                    if self.locked_target and (now - self.last_switch_time) < stickiness:
                        _sleep_active(0.006)
                        continue
                    self.prev_target = self.locked_target
                    self.locked_target = target["pawn"]
                    self.last_switch_time = now
                    self.smooth_ramp = 0.0
                    self.shots_fired = 0

                target_pitch, target_yaw = target["pitch"], target["yaw"]
                if bool(loop_cfg.get("aimbot_rcs_enabled", True)):
                    punch_bytes = self.pm.read_bytes(local_pawn + m_aimPunchAngle, 8)
                    shots = self.pm.read_int(local_pawn + m_iShotsFired) or 0
                    if punch_bytes and shots > 1:
                        pp, py = struct.unpack("ff", punch_bytes)
                        scale = float(loop_cfg.get("aimbot_rcs_scale", 2.0))
                        target_pitch -= pp * scale
                        target_yaw -= py * scale
                        self.shots_fired = shots

                delta_pitch = self._angle_diff(target_pitch, pitch)
                delta_yaw = self._angle_diff(target_yaw, yaw)
                deadzone = float(loop_cfg.get("aimbot_deadzone", 0.25))
                if abs(delta_pitch) < deadzone and abs(delta_yaw) < deadzone:
                    _sleep_active(0.006)
                    continue

                speed = float(loop_cfg.get("aimbot_speed", 1.6))
                ramp_speed = float(loop_cfg.get("aimbot_smooth_ramp_speed", 1.45))
                ease_out_power = max(0.1, float(loop_cfg.get("aimbot_ease_out", 0.85)))
                tick_rate = max(30.0, float(loop_cfg.get("aimbot_tick_rate", 60.0)))
                frame_time = 1.0 / tick_rate
                self.smooth_ramp = min(1.0, self.smooth_ramp + frame_time * ramp_speed)
                ease = self._ease_in_out_quad(self.smooth_ramp)
                distance_mag = math.hypot(delta_pitch, delta_yaw)
                fov_cap = max(1.0, float(loop_cfg.get("aimbot_fov", 40.0)))
                distance_factor = self._clamp(distance_mag / fov_cap, 0.0, 1.0)
                eased_distance = distance_factor ** ease_out_power
                lerp_t = self._clamp((speed / 5.0) * (0.35 + 0.65 * ease) * (0.45 + 0.55 * eased_distance), 0.02, 0.92)
                smooth_pitch = pitch + delta_pitch * lerp_t
                smooth_yaw = yaw + delta_yaw * lerp_t
                overshoot_chance = self._clamp(float(loop_cfg.get("aimbot_overshoot_chance", 0.3)), 0.0, 1.0)
                overshoot_strength = max(0.0, float(loop_cfg.get("aimbot_overshoot_strength", 3.5)))
                if overshoot_strength > 0.0 and random.random() < overshoot_chance:
                    scale = 0.08 * overshoot_strength * random.uniform(0.2, 1.0)
                    smooth_pitch += (1.0 if delta_pitch >= 0 else -1.0) * scale
                    smooth_yaw += (1.0 if delta_yaw >= 0 else -1.0) * scale
                smooth_pitch, smooth_yaw = self._normalize(smooth_pitch, smooth_yaw)

                sens = self._read_sensitivity()
                invert_y = float(loop_cfg.get("aimbot_invert_y", -1.0))
                raw_dx = -(smooth_yaw - yaw) / sens
                raw_dy = -((smooth_pitch - pitch) / sens) * invert_y
                max_move = int(loop_cfg.get("aimbot_max_mouse_move", 35))
                move_x = int(round(self._clamp(raw_dx, -max_move, max_move)))
                move_y = int(round(self._clamp(raw_dy, -max_move, max_move)))
                if move_x or move_y:
                    win32api.mouse_event(win32con.MOUSEEVENTF_MOVE, move_x, move_y, 0, 0)

                _sleep_active(frame_time * 0.70)
            except Exception:
                if loop_cfg.get("debug_worker_crashes", False):
                    _log_exception("[aimbot] worker loop crashed.")
                _sleep_idle(0.12)

def aimbot(s):
    aimbot_instance = Aimbot(s)
    aimbot_instance.run()


def find_button():
    screenshot = ImageGrab.grab()
    img = np.array(screenshot)
    color_match = np.all(img == (54, 183, 82), axis=-1).astype(int)
    kernel = np.ones((10, 10))
    convolution = convolve2d(color_match, kernel, mode='valid')
    y_coords, x_coords = np.where(convolution == 10**2)
    if len(y_coords) > 0:
        x = x_coords[0] + 10 // 2
        y = y_coords[0] + 10 // 2
        return (x, y)
    return None

def auto_accept(settings):
    while True:
        s_cache = settings.snapshot(("autoaccept_stop", "master_enabled", "autoaccept_enable", "perf_profile"))
        sleep_scale = _worker_sleep_scale(s_cache)
        if s_cache.get("autoaccept_stop", False):
            break
        if not s_cache.get("master_enabled", True):
            time.sleep(max(0.5, 0.5 * sleep_scale))
            continue
        if not s_cache.get("autoaccept_enable", False):
            time.sleep(max(1.0, 1.0 * sleep_scale))
            continue
            
        button_pos = find_button()
        if button_pos:
            x, y = button_pos
            pyautogui.moveTo(x, y)
            pyautogui.click()
            
            screen_width, screen_height = pyautogui.size()
            pyautogui.moveTo(screen_width / 2, screen_height / 2)
            
            time.sleep(3)
        else:
            time.sleep(max(0.5, 0.5 * sleep_scale))

def forcejump():
    ctypes.windll.user32.keybd_event(win32con.VK_SPACE, 0, 0, 0)
    _sleep_active(0.006)
    ctypes.windll.user32.keybd_event(win32con.VK_SPACE, 0, 2, 0)

def bunnyhop(settings):
    client, pm = get_descriptor_blocking()
    last_jump = 0.0
    while True:
        sleep_scale = 1.0
        try:
            s_cache = settings.snapshot(("bhop_stop", "master_enabled", "bunnyhop_enable", "bunnyhop_key", "bunnyhop_fast_mode", "perf_profile"))
            sleep_scale = _worker_sleep_scale(s_cache)
            if s_cache.get("bhop_stop", False):
                break
            if not s_cache.get("master_enabled", True):
                last_jump = 0.0
                _sleep_master_off(0.18, sleep_scale)
                continue
            if not s_cache.get("bunnyhop_enable", True) or not is_cs2_window_active():
                last_jump = 0.0
                _sleep_idle(0.06, sleep_scale)
                continue

            key_code = win32_key_map.get(str(s_cache.get("bunnyhop_key", "SPACE")).upper(), 0)
            if key_code <= 0:
                _sleep_idle(0.06, sleep_scale)
                continue
            if win32api.GetAsyncKeyState(key_code) & 0x8000:
                _, local_player_pawn_addr, _, _, _ = offsets_mem(pm, client)
                if not local_player_pawn_addr:
                    _sleep_active(0.006, sleep_scale)
                    continue
                move_flags = pm.read_int(local_player_pawn_addr + m_fFlags) or 0
                on_ground = (move_flags & 1) == 1
                now = time.monotonic()
                min_jump_interval = 0.0 if s_cache.get("bunnyhop_fast_mode", True) else 0.06
                if on_ground and (now - last_jump) >= min_jump_interval:
                    forcejump()
                    last_jump = now
            else:
                _sleep_idle(0.05, sleep_scale)
        except Exception:
            _sleep_idle(0.08, sleep_scale)
        _sleep_active(0.006, sleep_scale)


# ==============================
# Feature Config Schema
# ==============================

icons = {
    "ESP": "\uF06E", "AIMBOT": "\uF05B", "TRIGGER": "\uF0E7",
    "VISUALS": "\uF042", "MISC": "\uF013", "RADAR": "\uF0AC",
    "SYSTEM": "\uF085", "CONFIGS": "\uF07C"
}

config_tabs = [
    {
        "name": "ESP", "icon": icons["ESP"],
        "elements": [
            {"type": "checkbox", "label": "Enable ESP", "name": "esp_enable", "default": True},
            {"type": "checkbox", "label": "ESP Box", "name": "esp_box", "default": True},
            {"type": "checkbox", "label": "Filled Box", "name": "esp_filled_box", "default": True, "dependencies": [("esp_box", True)]},
            {"type": "checkbox", "label": "Corners", "name": "esp_corners", "default": True},
            {"type": "checkbox", "label": "Skeleton", "name": "esp_skeleton", "default": True},
            {"type": "checkbox", "label": "Names", "name": "esp_names", "default": True},
            {"type": "checkbox", "label": "Weapons", "name": "esp_weapons", "default": True},
            {"type": "checkbox", "label": "Health Bar", "name": "esp_health_bar", "default": True},
            {"type": "checkbox", "label": "Armor Bar", "name": "esp_armor_bar", "default": True},
            {"type": "checkbox", "label": "Head Dot", "name": "esp_head_dot", "default": True},
            {"type": "checkbox", "label": "Snap Lines", "name": "esp_snap_lines", "default": False},
            {"type": "checkbox", "label": "Eye Lines", "name": "esp_eye_lines", "default": True},
            {"type": "checkbox", "label": "Bomb Info", "name": "esp_bomb", "default": True},
            {"type": "checkbox", "label": "Dropped Weapons", "name": "esp_dropped_weapons", "default": False},
            {"type": "checkbox", "label": "Visible Only", "name": "esp_visible_only", "default": False},
            {"type": "checkbox", "label": "ESP Visibility Logic", "name": "visibility_esp_enabled", "default": True},
            {"type": "checkbox", "label": "Show Terrorists", "name": "esp_show_t", "default": True},
            {"type": "checkbox", "label": "Show Counter-Terrorists", "name": "esp_show_ct", "default": True},
            {"type": "checkbox", "label": "Show Team List", "name": "esp_show_team_list", "default": True},
            {"type": "checkbox", "label": "Show Spectator List", "name": "esp_show_spectator_list", "default": False},
            {"type": "checkbox", "label": "Show Map Status", "name": "esp_show_map_status", "default": True},
            {"type": "checkbox", "label": "Show FPS", "name": "esp_draw_fps", "default": False},
        ]
    },
    {
        "name": "VISUALS", "icon": icons["VISUALS"],
        "elements": [
            {"type": "color", "label": "Ally Color", "name": "esp_ally_color"},
            {"type": "color", "label": "Enemy Color", "name": "esp_enemy_color"},
            {"type": "color", "label": "Ally Visible", "name": "esp_ally_color_visible"},
            {"type": "color", "label": "Enemy Visible", "name": "esp_enemy_color_visible"},
            {"type": "color", "label": "Ally Invisible", "name": "esp_ally_color_invisible"},
            {"type": "color", "label": "Enemy Invisible", "name": "esp_enemy_color_invisible"},
            {"type": "color", "label": "Ally Snapline", "name": "esp_ally_snapline_color"},
            {"type": "color", "label": "Enemy Snapline", "name": "esp_enemy_snapline_color"},
            {"type": "color", "label": "Box Border", "name": "esp_box_border_color"},
            {"type": "color", "label": "Fill Normal", "name": "esp_box_fill_normal_color"},
            {"type": "color", "label": "Fill Spotted", "name": "esp_box_fill_spotted_color"},
            {"type": "color", "label": "Fill Immune", "name": "esp_box_fill_immune_color"},
            {"type": "color", "label": "Health Bar", "name": "esp_health_bar_color"},
            {"type": "color", "label": "Health Bar BG", "name": "esp_health_bar_bg_color"},
            {"type": "color", "label": "Armor Bar", "name": "esp_armor_bar_color"},
            {"type": "color", "label": "Head Dot", "name": "esp_head_dot_color"},
            {"type": "color", "label": "Skeleton", "name": "esp_skeleton_color"},
            {"type": "color", "label": "Name", "name": "esp_name_color"},
            {"type": "color", "label": "Weapon", "name": "esp_weapon_color"},
            {"type": "color", "label": "Eye Line", "name": "esp_eye_line_color"},
            {"type": "color", "label": "Bomb Timer", "name": "esp_bomb_color"},
            {"type": "color", "label": "Bomb Defusing", "name": "esp_bomb_defusing_color"},
            {"type": "color", "label": "Dropped Weapon", "name": "esp_dropped_weapon_color"},
            {"type": "color", "label": "Spectator Widget", "name": "esp_spectator_color"},
            {"type": "color", "label": "Map Widget", "name": "esp_map_color"},
            {"type": "color", "label": "FOV Circle", "name": "esp_fov_color"},
            {"type": "color", "label": "Crosshair", "name": "esp_crosshair_color"},
        ]
    },
    {
        "name": "AIMBOT", "icon": icons["AIMBOT"],
        "elements": [
            {"type": "checkbox", "label": "Enable Aimbot", "name": "aimbot_enable", "default": False},
            {"type": "bind", "label": "Aimbot Key", "name": "aimbot_key"},
            {"type": "checkbox", "label": "Always On", "name": "aimbot_always_on", "default": False},
            {"type": "checkbox", "label": "Attack All", "name": "aim_attack_all", "default": False},
            {"type": "checkbox", "label": "Draw FOV", "name": "draw_fov", "default": True},
            {"type": "slider", "label": "FOV", "name": "aimbot_fov", "min": 1.0, "max": 100.0, "default": 40.0, "format": "%.1f"},
            {"type": "slider", "label": "Speed", "name": "aimbot_speed", "min": 0.1, "max": 5.0, "default": 1.6, "format": "%.2f"},
            {"type": "checkbox", "label": "Dynamic FOV", "name": "aim_dynamic_fov_enabled", "default": False},
            {"type": "slider", "label": "Dyn Min Scale", "name": "aim_dynamic_fov_min_scale", "min": 0.1, "max": 2.0, "default": 0.5, "format": "%.2f"},
            {"type": "slider", "label": "Dyn Max Scale", "name": "aim_dynamic_fov_max_scale", "min": 0.1, "max": 3.0, "default": 1.5, "format": "%.2f"},
            {"type": "slider", "label": "Dyn Max Dist", "name": "aim_dynamic_fov_max_distance", "min": 500.0, "max": 8000.0, "default": 3000.0, "format": "%.0f"},
            {"type": "checkbox", "label": "Closest Crosshair Bone", "name": "aimbot_closest_to_crosshair", "default": False},
            {"type": "combo", "label": "Bone Pool", "name": "aimbot_bone_list", "items": [
                "head,neck,chest,pelvis,left_hand,right_hand,left_leg,right_leg",
                "head,neck,chest,pelvis",
                "head,neck,chest",
                "head"
            ]},
            {"type": "combo", "label": "Target Bone", "name": "aimbot_target_bone", "items": ["head", "neck", "chest", "pelvis", "left_hand", "right_hand", "left_leg", "right_leg"]},
            {"type": "checkbox", "label": "Velocity Prediction", "name": "aimbot_velocity_prediction", "default": True},
            {"type": "slider", "label": "Velocity Factor", "name": "aimbot_velocity_factor", "min": 0.1, "max": 3.0, "default": 1.0, "format": "%.2f"},
            {"type": "checkbox", "label": "Visibility Check", "name": "aimbot_visibility_check", "default": True},
            {"type": "checkbox", "label": "Use Visibility Engine", "name": "visibility_aim_enabled", "default": True},
            {"type": "checkbox", "label": "Deathmatch Mode", "name": "aimbot_deathmatch_mode", "default": False},
            {"type": "checkbox", "label": "RCS", "name": "aimbot_rcs_enabled", "default": True},
            {"type": "slider", "label": "RCS Scale", "name": "aimbot_rcs_scale", "min": 0.0, "max": 3.5, "default": 2.0, "format": "%.2f"},
            {"type": "slider", "label": "Deadzone", "name": "aimbot_deadzone", "min": 0.0, "max": 2.0, "default": 0.25, "format": "%.2f"},
            {"type": "slider", "label": "Ramp Speed", "name": "aimbot_smooth_ramp_speed", "min": 0.1, "max": 4.0, "default": 1.45, "format": "%.2f"},
            {"type": "slider", "label": "Downward Offset", "name": "aimbot_downward_offset", "min": -40.0, "max": 40.0, "default": 0.0, "format": "%.1f"},
            {"type": "slider", "label": "Eye Height", "name": "aimbot_eye_height", "min": 30.0, "max": 90.0, "default": 64.0, "format": "%.1f"},
            {"type": "slider", "label": "Max Mouse Move", "name": "aimbot_max_mouse_move", "min": 1.0, "max": 120.0, "default": 35.0, "format": "%.0f"},
            {"type": "slider", "label": "Y Axis Mult", "name": "aimbot_invert_y", "min": -1.0, "max": 1.0, "default": -1.0, "format": "%.2f"},
            {"type": "slider", "label": "Entity Scan Limit", "name": "aimbot_max_entities", "min": 1.0, "max": 64.0, "default": 64.0, "format": "%.0f"},
            {"type": "slider", "label": "Entity Cache Refresh", "name": "aimbot_entity_cache_refresh", "min": 0.01, "max": 1.0, "default": 0.2, "format": "%.2f"},
            {"type": "slider", "label": "Stickiness", "name": "aimbot_stickiness_time", "min": 0.0, "max": 1.0, "default": 0.18, "format": "%.2f"},
            {"type": "slider", "label": "Tick Rate", "name": "aimbot_tick_rate", "min": 30.0, "max": 240.0, "default": 60.0, "format": "%.0f"},
            {"type": "slider", "label": "Ease Out Power", "name": "aimbot_ease_out", "min": 0.1, "max": 1.0, "default": 0.85, "format": "%.2f"},
            {"type": "slider", "label": "Overshoot Chance", "name": "aimbot_overshoot_chance", "min": 0.0, "max": 1.0, "default": 0.3, "format": "%.2f"},
            {"type": "slider", "label": "Overshoot Strength", "name": "aimbot_overshoot_strength", "min": 0.0, "max": 10.0, "default": 3.5, "format": "%.1f"},
        ]
    },
    {
        "name": "TRIGGER", "icon": icons["TRIGGER"],
        "elements": [
            {"type": "checkbox", "label": "Enable Trigger", "name": "trigger_enable", "default": False},
            {"type": "bind", "label": "Trigger Key", "name": "trigger_key"},
            {"type": "checkbox", "label": "Always On", "name": "trigger_always_on", "default": False},
            {"type": "checkbox", "label": "Attack All", "name": "trigger_attack_all", "default": False},
            {"type": "checkbox", "label": "Shoot Teammates", "name": "trigger_teammates", "default": False},
            {"type": "checkbox", "label": "Flash Check", "name": "trigger_flash_check", "default": True},
            {"type": "slider", "label": "Delay", "name": "trigger_delay", "min": 0.0, "max": 0.5, "format": "%.3f s"},
            {"type": "slider", "label": "Cooldown", "name": "trigger_cooldown", "min": 0.0, "max": 1.5, "default": 0.08, "format": "%.3f s"},
        ]
    },
    {
        "name": "RADAR", "icon": icons["RADAR"],
        "elements": [
            {"type": "checkbox", "label": "Enable Radar", "name": "radar_enable", "default": False},
            {"type": "checkbox", "label": "Show Teammates", "name": "radar_show_team", "default": True},
            {"type": "checkbox", "label": "Fixed Range", "name": "radar_fixed_range", "default": False},
            {"type": "checkbox", "label": "Show My Dir", "name": "radar_show_me_dir", "default": True},
            {"type": "checkbox", "label": "Show Enemy Dir", "name": "radar_show_enemy_dir", "default": True},
            {"type": "checkbox", "label": "Show Team Dir", "name": "radar_show_team_dir", "default": False},
            {"type": "slider", "label": "Radar Size", "name": "radar_size", "min": 140.0, "max": 420.0, "default": 220.0, "format": "%.0f"},
            {"type": "slider", "label": "Radar X", "name": "radar_x", "min": 0.0, "max": 800.0, "default": 40.0, "format": "%.0f"},
            {"type": "slider", "label": "Radar Y", "name": "radar_y", "min": 0.0, "max": 800.0, "default": 140.0, "format": "%.0f"},
            {"type": "slider", "label": "Radar Alpha", "name": "radar_alpha", "min": 40.0, "max": 255.0, "default": 235.0, "format": "%.0f"},
            {"type": "slider", "label": "Radar Range", "name": "radar_range_units", "min": 500.0, "max": 8000.0, "default": 3000.0, "format": "%.0f"},
            {"type": "slider", "label": "Radar FPS", "name": "radar_reader_fps", "min": 5.0, "max": 120.0, "default": 25.0, "format": "%.0f"},
            {"type": "checkbox", "label": "Overlay Always On Top", "name": "radar_always_on_top", "default": True},
        ]
    },
    {
        "name": "MISC", "icon": icons["MISC"],
        "elements": [
            {"type": "checkbox", "label": "Bunny Hop", "name": "bunnyhop_enable", "default": False},
            {"type": "bind", "label": "BHop Key", "name": "bunnyhop_key"},
            {"type": "checkbox", "label": "Draw Crosshair", "name": "draw_crosshair", "default": True},
            {"type": "checkbox", "label": "Auto Accept Match", "name": "autoaccept_enable", "default": False},
            {"type": "checkbox", "label": "No Recoil", "name": "norecoil_enable", "default": False},
            {"type": "slider", "label": "Recoil X", "name": "norecoil_x", "min": 0.0, "max": 2.0, "default": 1.0, "format": "%.2f"},
            {"type": "slider", "label": "Recoil Y", "name": "norecoil_y", "min": 0.0, "max": 2.0, "default": 1.0, "format": "%.2f"},
            {"type": "checkbox", "label": "Fast BHop Loop", "name": "bunnyhop_fast_mode", "default": True},
        ]
    },
    {
        "name": "SYSTEM", "icon": icons["SYSTEM"],
        "elements": [
            {"type": "checkbox", "label": "Master Enable (F5)", "name": "master_enabled", "default": True},
            {"type": "checkbox", "label": "Hide ESP From Capture", "name": "hide_esp_from_capture", "default": False},
            {"type": "checkbox", "label": "Debug Worker Crashes", "name": "debug_worker_crashes", "default": True},
            {"type": "slider", "label": "Perf Profile (0=Low,1=Balanced,2=Quality)", "name": "perf_profile", "min": 0.0, "max": 2.0, "default": 0.0, "format": "%.0f"},
            {"type": "checkbox", "label": "Adaptive Perf Auto-Scale", "name": "adaptive_perf_enabled", "default": True},
            {"type": "checkbox", "label": "Show Perf Status Overlay", "name": "adaptive_perf_show_status", "default": True},
            {"type": "status", "label": "Adaptive Perf Tier", "name": "adaptive_perf_level"},
            {"type": "checkbox", "label": "Resource Guard", "name": "resource_guard_enabled", "default": True},
            {"type": "slider", "label": "CPU Budget %", "name": "resource_cpu_budget_pct", "min": 5.0, "max": 95.0, "default": 55.0, "format": "%.1f"},
            {"type": "slider", "label": "RAM Budget MB", "name": "resource_ram_budget_mb", "min": 128.0, "max": 16384.0, "default": 1536.0, "format": "%.0f"},
            {"type": "slider", "label": "Budget Poll (s)", "name": "resource_poll_interval", "min": 0.25, "max": 5.0, "default": 1.25, "format": "%.2f"},
            {"type": "status", "label": "Runtime CPU %", "name": "runtime_cpu_percent"},
            {"type": "status", "label": "Runtime RAM MB", "name": "runtime_ram_mb"},
            {"type": "status", "label": "Resource Status", "name": "resource_status"},
            {"type": "slider", "label": "Vischeck Budget / Frame", "name": "vischeck_max_per_frame", "min": 0.0, "max": 64.0, "default": 4.0, "format": "%.0f"},
            {"type": "slider", "label": "Overlay FPS Limit", "name": "overlay_fps_limit", "min": 30.0, "max": 240.0, "default": 45.0, "format": "%.0f"},
            {"type": "slider", "label": "Menu FPS Limit", "name": "menu_fps_limit", "min": 30.0, "max": 240.0, "default": 60.0, "format": "%.0f"},
            {"type": "button", "label": "Reload Visibility Map", "name": "visibility_map_reload"},
            {"type": "status", "label": "Vis Map Loaded", "name": "visibility_map_loaded"},
            {"type": "status", "label": "Vis Map Path", "name": "visibility_map_path"},
            {"type": "checkbox", "label": "Pause Aimbot", "name": "aim_stop", "default": False},
            {"type": "checkbox", "label": "Pause Triggerbot", "name": "triggerbot_stop", "default": False},
            {"type": "checkbox", "label": "Pause BHop", "name": "bhop_stop", "default": False},
            {"type": "checkbox", "label": "Pause ESP Overlay", "name": "wallhack_stop", "default": False},
            {"type": "checkbox", "label": "Pause No-Recoil", "name": "norecoil_stop", "default": False},
            {"type": "checkbox", "label": "Pause Auto-Accept", "name": "autoaccept_stop", "default": False},
            {"type": "checkbox", "label": "Pause Radar Reader", "name": "radar_stop", "default": False},
            {"type": "bind", "label": "Panic Key", "name": "panic_key"},
        ]
    },
    {
        "name": "CONFIGS", "icon": icons["CONFIGS"],
        "elements": [
            {"type": "text_input", "label": "Config Name", "name": "config_filename"},
            {"type": "button", "label": "Save Config", "name": "config_save"},
            {"type": "combo", "label": "Load Config", "name": "config_profile", "items": ["Loading..."]},
            {"type": "button", "label": "Load Selected", "name": "config_load"},
            {"type": "button", "label": "Refresh List", "name": "config_refresh"},
            {"type": "button", "label": "Reset To Defaults", "name": "config_reset"},
        ]
    }
]

class Settings:
    def __init__(self, manager):
        self._lock = Lock()
        self.config_dir = "configs"
        self._defaults = {
            "esp_enable": True, "esp_box": True, "esp_filled_box": True, "esp_corners": True,
            "esp_skeleton": True, "esp_names": True, "esp_weapons": True, "esp_health_bar": True,
            "esp_armor_bar": True, "esp_head_dot": True, "esp_snap_lines": False, "esp_eye_lines": True,
            "esp_bomb": True, "esp_dropped_weapons": False, "esp_visible_only": False,
            "esp_show_team_list": True, "esp_show_spectator_list": False, "esp_show_map_status": True,
            "esp_draw_fps": False, "esp_show_t": True, "esp_show_ct": True,
            "esp_ally_color": (0.0, 1.0, 0.0, 0.8), "esp_enemy_color": (1.0, 0.0, 0.0, 0.8),
            "esp_ally_color_visible": (0.22, 1.0, 0.55, 0.9), "esp_enemy_color_visible": (1.0, 0.45, 0.1, 0.9),
            "esp_ally_color_invisible": (0.0, 0.62, 0.28, 0.8), "esp_enemy_color_invisible": (0.82, 0.15, 0.15, 0.8),
            "esp_ally_snapline_color": (0.0, 1.0, 0.0, 0.5), "esp_enemy_snapline_color": (1.0, 0.0, 0.0, 0.5),
            "esp_box_border_color": (0.1, 0.1, 0.1, 0.8),
            "esp_box_fill_normal_color": (0.23, 0.2, 0.19, 0.4), "esp_box_fill_spotted_color": (0.23, 0.3, 0.19, 0.4),
            "esp_box_fill_immune_color": (0.83, 0.3, 0.19, 0.4),
            "esp_health_bar_color": (1.0, 0.0, 0.0, 0.9), "esp_health_bar_bg_color": (0.0, 0.0, 0.0, 0.7),
            "esp_armor_bar_color": (0.05, 0.27, 0.56, 0.9), "esp_head_dot_color": (1.0, 0.0, 0.0, 0.7),
            "esp_skeleton_color": (1.0, 1.0, 1.0, 1.0), "esp_name_color": (1.0, 1.0, 1.0, 1.0),
            "esp_spectator_color": (0.88, 0.88, 0.92, 1.0), "esp_map_color": (0.82, 0.95, 1.0, 1.0),
            "esp_weapon_color": (1.0, 1.0, 1.0, 1.0), "esp_eye_line_color": (1.0, 1.0, 1.0, 0.7),
            "esp_bomb_color": (1.0, 0.0, 0.0, 1.0), "esp_bomb_defusing_color": (0.0, 1.0, 0.0, 1.0),
            "esp_dropped_weapon_color": (1.0, 1.0, 1.0, 1.0), "esp_fov_color": (1.0, 1.0, 1.0, 0.7),
            "esp_crosshair_color": (0.0, 1.0, 0.0, 1.0),
            "aimbot_enable": False, "aimbot_key": "MOUSE5", "aim_attack_all": False,
            "aimbot_always_on": False, "draw_fov": True, "aimbot_target_bone": "head",
            "aimbot_bone_list": "head,neck,chest,pelvis,left_hand,right_hand,left_leg,right_leg",
            "aimbot_closest_to_crosshair": False, "aimbot_visibility_check": True,
            "aimbot_velocity_prediction": True, "aimbot_velocity_factor": 1.0, "aimbot_downward_offset": 0.0,
            "aimbot_eye_height": 64.0, "aimbot_tick_rate": 60.0, "aimbot_stickiness_time": 0.18,
            "aimbot_smooth_ramp_speed": 1.45, "aimbot_max_mouse_move": 35, "aimbot_invert_y": -1.0,
            "aimbot_rcs_enabled": True, "aimbot_rcs_scale": 2.0, "aimbot_deadzone": 0.25,
            "aim_dynamic_fov_enabled": False, "aim_dynamic_fov_min_scale": 0.5,
            "aim_dynamic_fov_max_scale": 1.5, "aim_dynamic_fov_max_distance": 3000.0,
            "aimbot_max_entities": 64, "aimbot_entity_cache_refresh": 0.2, "aimbot_deathmatch_mode": False,
            "aimbot_fov": 40.0, "aimbot_speed": 1.6, "aimbot_ease_out": 0.85, "aimbot_overshoot_chance": 0.3, "aimbot_overshoot_strength": 3.5,
            "trigger_enable": False, "trigger_attack_all": False, "trigger_key": "MOUSE4",
            "trigger_delay": 0.01, "trigger_flash_check": True, "trigger_always_on": False,
            "trigger_teammates": False, "trigger_cooldown": 0.08,
            "bunnyhop_enable": False, "bunnyhop_key": "SPACE", "bunnyhop_fast_mode": True,
            "radar_enable": False, "radar_show_team": True, "radar_size": 220.0,
            "radar_x": 40.0, "radar_y": 140.0, "radar_range_units": 3000.0,
            "radar_alpha": 235, "radar_always_on_top": True, "radar_reader_fps": 25.0,
            "radar_fixed_range": False, "radar_show_me_dir": True,
            "radar_show_enemy_dir": True, "radar_show_team_dir": False,
            "visibility_esp_enabled": True, "visibility_aim_enabled": True, "vischeck_max_per_frame": 4,
            "visibility_map_path": "", "visibility_map_reload_needed": False, "visibility_map_loaded": False,
            "draw_crosshair": True,
            "norecoil_enable": False, "norecoil_x": 1.0, "norecoil_y": 1.0, "autoaccept_enable": False,
            "aim_stop": False, "triggerbot_stop": False, "bhop_stop": False, "radar_stop": False,
            "wallhack_stop": False, "norecoil_stop": False, "autoaccept_stop": False,
            "master_enabled": True,
            "perf_profile": 0,
            "hide_esp_from_capture": False, "overlay_fps_limit": 45.0, "menu_fps_limit": 60.0,
            "adaptive_perf_enabled": True, "adaptive_perf_level": 0, "adaptive_perf_show_status": True,
            "resource_guard_enabled": True, "resource_cpu_budget_pct": 55.0, "resource_ram_budget_mb": 1536.0,
            "resource_poll_interval": 1.25, "resource_guard_tier": 0, "resource_status": "INIT",
            "runtime_cpu_percent": 0.0, "runtime_ram_mb": 0.0,
            "panic_key": "DELETE", "debug_worker_crashes": True,
            "config_profile": 0,
        }
        self._legacy_map = {
            "aimbot_enabled": "aimbot_enable",
            "aimbot_bone": "aimbot_target_bone",
            "aim_key": "aimbot_key",
            "draw_aimbot_fov": "draw_fov",
            "FOV": "aimbot_fov",
            "dynamic_fov_enabled": "aim_dynamic_fov_enabled",
            "dynamic_fov_min_scale": "aim_dynamic_fov_min_scale",
            "dynamic_fov_max_scale": "aim_dynamic_fov_max_scale",
            "dynamic_fov_max_distance": "aim_dynamic_fov_max_distance",
            "target_bone_name": "aimbot_target_bone",
            "closest_to_crosshair": "aimbot_closest_to_crosshair",
            "visibility_aim_enabled": "aimbot_visibility_check",
            "visibility_esp_enabled": "visibility_esp_enabled",
            "vischeck_max_per_frame": "vischeck_max_per_frame",
            "visibility_map_path": "visibility_map_path",
            "visibility_map_reload_needed": "visibility_map_reload_needed",
            "visibility_map_loaded": "visibility_map_loaded",
            "triggerbot_enabled": "trigger_enable",
            "triggerbot_stop": "triggerbot_stop",
            "triggerbot_always_on": "trigger_always_on",
            "triggerbot_cooldown": "trigger_cooldown",
            "shoot_teammates": "trigger_teammates",
            "bhop_enabled": "bunnyhop_enable",
            "bhop_stop": "bhop_stop",
            "radar_enabled": "radar_enable",
            "radar_stop": "radar_stop",
            "radar_width": "radar_size",
            "radar_height": "radar_size",
            "radar_alpha": "radar_alpha",
            "radar_always_on_top": "radar_always_on_top",
            "radar_reader_fps": "radar_reader_fps",
            "radar_fixed_range": "radar_fixed_range",
            "radar_show_me_dir": "radar_show_me_dir",
            "radar_show_enemy_dir": "radar_show_enemy_dir",
            "radar_show_team_dir": "radar_show_team_dir",
            "spectator_list_enabled": "esp_show_spectator_list",
            "esp_draw_fps": "esp_draw_fps",
            "esp_show_t": "esp_show_t",
            "esp_show_ct": "esp_show_ct",
            "color_t": "esp_enemy_color",
            "color_ct": "esp_ally_color",
            "color_skeleton_t": "esp_skeleton_color",
            "color_skeleton_ct": "esp_skeleton_color",
            "color_skeleton_t_visible": "esp_skeleton_color",
            "color_skeleton_ct_visible": "esp_skeleton_color",
            "color_skeleton_t_invisible": "esp_skeleton_color",
            "color_skeleton_ct_invisible": "esp_skeleton_color",
            "color_name_t": "esp_name_color",
            "color_name_ct": "esp_name_color",
            "color_vis_t_visible": "esp_enemy_color_visible",
            "color_vis_ct_visible": "esp_ally_color_visible",
            "color_vis_t_invisible": "esp_enemy_color_invisible",
            "color_vis_ct_invisible": "esp_ally_color_invisible",
            "color_spectators": "esp_spectator_color",
            "aim_bones": "aimbot_bone_list",
            "max_entities": "aimbot_max_entities",
            "entity_cache_refresh": "aimbot_entity_cache_refresh",
            "DeathMatch": "aimbot_deathmatch_mode",
            "aim_stop": "aim_stop",
        }
        self._numeric_bounds = {
            "aimbot_max_entities": (1, 64),
            "perf_profile": (0, 2),
            "resource_cpu_budget_pct": (5.0, 95.0),
            "resource_poll_interval": (0.25, 5.0),
            "overlay_fps_limit": (30.0, 240.0),
            "menu_fps_limit": (30.0, 240.0),
        }
        self._data = manager.dict(self._defaults)
        self._local_cache = dict(self._defaults)
        self._local_cache_time = 0.0
        self._local_cache_ttl = 0.08

    def _refresh_local_cache(self, force=False):
        now = time.perf_counter()
        if not force and (now - self._local_cache_time) < self._local_cache_ttl:
            return
        try:
            self._local_cache = dict(self._data)
            self._local_cache_time = now
        except Exception:
            pass

    @staticmethod
    def _normalize_color(value, fallback):
        if not isinstance(value, (list, tuple)):
            return fallback
        parts = list(value)
        if len(parts) == 3:
            parts.append(1.0)
        if len(parts) != 4:
            return fallback
        if any(abs(float(x)) > 1.0 for x in parts):
            return tuple(max(0.0, min(1.0, float(x) / 255.0)) for x in parts)
        return tuple(max(0.0, min(1.0, float(x))) for x in parts)

    def _normalize_value(self, key, value):
        default = self._defaults.get(key)
        if default is None:
            return value
        bounds = self._numeric_bounds.get(key)
        if isinstance(default, bool):
            if isinstance(value, str):
                return value.strip().lower() in {"1", "true", "yes", "on"}
            return bool(value)
        if isinstance(default, int) and not isinstance(default, bool):
            try:
                parsed = int(value)
                if bounds:
                    parsed = max(int(bounds[0]), min(int(bounds[1]), parsed))
                return parsed
            except Exception:
                return default
        if isinstance(default, float):
            try:
                parsed = float(value)
                if bounds:
                    parsed = max(float(bounds[0]), min(float(bounds[1]), parsed))
                return parsed
            except Exception:
                return default
        if isinstance(default, str):
            if key == "aimbot_bone_list" and isinstance(value, (list, tuple)):
                return ",".join(str(x).strip().lower() for x in value if str(x).strip())
            return str(value).strip() or default
        if isinstance(default, tuple):
            return self._normalize_color(value, default)
        return value

    def _migrate_payload(self, payload):
        migrated = {}
        if not isinstance(payload, dict):
            return migrated
        for key, value in payload.items():
            mapped = key if key in self._defaults else self._legacy_map.get(key)
            if not mapped:
                continue
            migrated[mapped] = self._normalize_value(mapped, value)

        # If legacy radar width/height exist, prefer the larger edge for square radar size.
        if "radar_width" in payload or "radar_height" in payload:
            try:
                w = float(payload.get("radar_width", 0) or 0)
                h = float(payload.get("radar_height", 0) or 0)
                if max(w, h) > 0:
                    migrated["radar_size"] = self._normalize_value("radar_size", max(w, h))
            except Exception:
                pass
        if "radar_reader_fps" not in payload and "radar_fps" in payload:
            migrated["radar_reader_fps"] = self._normalize_value("radar_reader_fps", payload.get("radar_fps"))

        # Keep legacy vischeck toggles coherent with new fields.
        if "visibility_aim_enabled" in payload and "aimbot_visibility_check" not in migrated:
            migrated["aimbot_visibility_check"] = self._normalize_value("aimbot_visibility_check", payload.get("visibility_aim_enabled"))
        if "visibility_esp_enabled" in payload and "esp_visible_only" not in migrated:
            vis_esp = self._normalize_value("visibility_esp_enabled", payload.get("visibility_esp_enabled"))
            migrated["visibility_esp_enabled"] = vis_esp
            migrated["esp_visible_only"] = bool(vis_esp) and bool(migrated.get("esp_visible_only", False))

        # Legacy numeric bone index -> new bone name.
        if "aimbot_bone" in payload:
            try:
                idx = int(payload.get("aimbot_bone", 0))
            except Exception:
                idx = 0
            bone_order = ["head", "neck", "chest", "pelvis", "left_hand", "right_hand", "left_leg", "right_leg"]
            if 0 <= idx < len(bone_order):
                migrated["aimbot_target_bone"] = bone_order[idx]

        return migrated
    
    def get(self, key, default=None):
        self._refresh_local_cache(force=False)
        return self._local_cache.get(key, default)
    
    def set(self, key, value):
        norm = self._normalize_value(key, value)
        self._data[key] = norm
        self._local_cache[key] = norm
        self._local_cache_time = time.perf_counter()

    def snapshot(self, keys=None, force=False):
        self._refresh_local_cache(force=force)
        if keys is None:
            return dict(self._local_cache)
        return {k: self._local_cache.get(k) for k in keys}
            
    def save(self, filename):
        if not filename.endswith(".json"):
            filename += ".json"
        if not os.path.exists(self.config_dir):
            os.makedirs(self.config_dir)
        filepath = os.path.join(self.config_dir, filename)
        
        with self._lock:
            self._refresh_local_cache(force=True)
            config_data = dict(self._local_cache)
            
        with open(filepath, 'w', encoding="utf-8") as f:
            json.dump(config_data, f, indent=4)
        return True

    @staticmethod
    def _legacy_appdata_path():
        appdata = os.environ.get("APPDATA", "")
        if not appdata:
            return ""
        return os.path.join(appdata, "GScript", "gscript_config.json")

    def load(self, filename):
        if not filename.endswith(".json"):
            filename += ".json"
        filepath = os.path.join(self.config_dir, filename)
        if not os.path.exists(filepath):
            legacy_path = self._legacy_appdata_path()
            if filename.lower() in ("default.json", "gscript_config.json") and legacy_path and os.path.exists(legacy_path):
                filepath = legacy_path
            else:
                return False
        
        with open(filepath, 'r', encoding="utf-8") as f:
            config_data = json.load(f)

        migrated = self._migrate_payload(config_data)
            
        with self._lock:
            for key, value in self._defaults.items():
                self._data[key] = value
            for key, value in migrated.items():
                self._data[key] = value
            self._refresh_local_cache(force=True)
        return True

    def reset(self):
        with self._lock:
            for key, value in self._defaults.items():
                self._data[key] = value
            self._refresh_local_cache(force=True)
        return True
        
    def list_configs(self):
        if not os.path.exists(self.config_dir):
            return ["No configs found"]
        files = sorted(f for f in os.listdir(self.config_dir) if f.endswith(".json"))
        return files if files else ["No configs found"]
    

center_x_circle = WINDOW_WIDTH // 2 + 0.5
center_y_circle = WINDOW_HEIGHT // 2 + 0.5

weapon_draw_list = []
radar_snapshot = {"local": None, "entities": []}
_last_overlay_meta = {"map_name": "unknown", "map_time": 0.0}
_overlay_cached_lists = {"time": 0.0, "t": [], "ct": [], "spec": []}
_overlay_sidecar_state = {
    "weapon_last": 0.0,
    "radar_last": 0.0,
    "last_perf_log": 0.0,
}


def _perf_tier_enabled(settings_snapshot):
    try:
        return max(0, min(3, int(_adaptive_perf_state.get("tier", 0))))
    except Exception:
        return 0


def _update_weapon_draw_cache(settings_snapshot, perf_tier):
    global weapon_draw_list

    if not bool(settings_snapshot.get("master_enabled", True)):
        weapon_draw_list = []
        return
    if not bool(settings_snapshot.get("esp_dropped_weapons", False)):
        weapon_draw_list = []
        return
    if not client or not pm:
        weapon_draw_list = []
        return

    interval_by_tier = (0.14, 0.24, 0.42, 0.70)
    max_index_by_tier = (900, 640, 420, 260)
    now = time.perf_counter()
    if (now - _overlay_sidecar_state["weapon_last"]) < interval_by_tier[perf_tier]:
        return
    _overlay_sidecar_state["weapon_last"] = now

    try:
        view_matrix, _, _, entity_list, _ = offsets_mem(pm, client)
        if not entity_list:
            weapon_draw_list = []
            return

        temp_weapon_list = []
        for i in range(64, max_index_by_tier[perf_tier]):
            weapon_data = esp_dweapon(pm, i, entity_list, view_matrix, WINDOW_WIDTH, WINDOW_HEIGHT)
            if not weapon_data:
                continue
            weapon_screen_pos, weapon_name = weapon_data
            if weapon_name != "unknown" and weapon_screen_pos:
                temp_weapon_list.append({"pos": weapon_screen_pos, "name": weapon_name})
        weapon_draw_list = temp_weapon_list
    except Exception:
        weapon_draw_list = []
        _log_exception("[overlay-sidecar] weapon cache update failed.")


def _update_radar_snapshot_cache(settings_snapshot, perf_tier):
    global radar_snapshot

    if not bool(settings_snapshot.get("master_enabled", True)):
        radar_snapshot = {"local": None, "entities": []}
        return
    if not bool(settings_snapshot.get("radar_enable", False)):
        radar_snapshot = {"local": None, "entities": []}
        return
    if not client or not pm:
        radar_snapshot = {"local": None, "entities": []}
        return

    base_fps = max(5.0, float(settings_snapshot.get("radar_reader_fps", 25.0)))
    perf_scale = (1.2, 1.6, 2.2, 3.1)[perf_tier]
    frame_dt = max(0.01, (1.0 / base_fps) * perf_scale)
    now = time.perf_counter()
    if (now - _overlay_sidecar_state["radar_last"]) < frame_dt:
        return
    _overlay_sidecar_state["radar_last"] = now

    try:
        view_matrix, local_pawn, local_team, entity_list, entity_ptr = offsets_mem(pm, client)
        if not local_pawn or not entity_list or not entity_ptr:
            radar_snapshot = {"local": None, "entities": []}
            return

        local_pos = read_vec3(pm, local_pawn + m_vOldOrigin)
        pitch, yaw = (0.0, 0.0)
        try:
            view = pm.read_bytes(client + dwViewAngles, 8)
            if view:
                pitch, yaw = struct.unpack("ff", view)
        except Exception:
            pass

        max_entities = (48, 36, 26, 18)[perf_tier]
        entities = []
        for i in range(1, max_entities + 1):
            try:
                entity_data = client_mem(pm, i, entity_ptr, entity_list, local_pawn, local_team)
                if not entity_data:
                    continue
                ent_team, _, pawn, _, _ = entity_data
                ent_yaw = None
                try:
                    eye = read_vec2(pm, pawn + m_angEyeAngles)
                    if eye:
                        ent_yaw = float(eye[1])
                except Exception:
                    ent_yaw = None
                pos = read_vec3(pm, pawn + m_vOldOrigin)
                entities.append(
                    {
                        "x": float(pos[0]),
                        "y": float(pos[1]),
                        "team": int(ent_team),
                        "yaw": ent_yaw,
                    }
                )
            except Exception:
                continue

        radar_snapshot = {
            "local": {
                "x": float(local_pos[0]),
                "y": float(local_pos[1]),
                "yaw": float(yaw),
                "team": int(local_team),
            },
            "entities": entities,
        }
    except Exception:
        radar_snapshot = {"local": None, "entities": []}
        _log_exception("[overlay-sidecar] radar cache update failed.")


def _update_overlay_sidecars(settings_snapshot):
    perf_tier = _perf_tier_enabled(settings_snapshot)
    _update_weapon_draw_cache(settings_snapshot, perf_tier)
    _update_radar_snapshot_cache(settings_snapshot, perf_tier)

def weapon_worker(shared_list, settings_proxy):
    worker_client, worker_pm = get_descriptor_blocking()
    if not worker_client or not worker_pm:
        return

    while True:
        try:
            if settings_proxy.get("wallhack_stop", False):
                break
            if not settings_proxy.get("master_enabled", True):
                shared_list[:] = []
                time.sleep(0.25)
                continue
            if not is_cs2_window_active():
                shared_list[:] = []
                time.sleep(1)
                continue

            if not settings_proxy.get("esp_dropped_weapons", False):
                shared_list[:] = []
                time.sleep(1)
                continue

            view_matrix, _, _, entity_list, _ = offsets_mem(worker_pm, worker_client)
            if entity_list == 0:
                time.sleep(1)
                continue

            temp_weapon_list = []
            for i in range(64, 1024):
                weapon_data = esp_dweapon(worker_pm, i, entity_list, view_matrix, WINDOW_WIDTH, WINDOW_HEIGHT)
                if weapon_data:
                    weapon_screen_pos, weapon_name = weapon_data
                    if weapon_name != 'unknown' and weapon_screen_pos:
                        temp_weapon_list.append({
                            'pos': weapon_screen_pos,
                            'name': weapon_name
                        })
            
            shared_list[:] = temp_weapon_list

        except Exception:
            shared_list[:] = []
        
        time.sleep(0.1)


def radar_worker(shared_snapshot, settings_proxy):
    worker_client, worker_pm = get_descriptor_blocking()
    if not worker_client or not worker_pm:
        return

    while True:
        try:
            if settings_proxy.get("radar_stop", False):
                shared_snapshot["local"] = None
                shared_snapshot["entities"] = []
                time.sleep(0.15)
                continue
            if not settings_proxy.get("master_enabled", True):
                shared_snapshot["local"] = None
                shared_snapshot["entities"] = []
                time.sleep(0.15)
                continue
            fps = max(5.0, float(settings_proxy.get("radar_reader_fps", 25.0)))
            frame_dt = 1.0 / fps

            if not settings_proxy.get("radar_enable", False):
                shared_snapshot["local"] = None
                shared_snapshot["entities"] = []
                time.sleep(0.15)
                continue

            view_matrix, local_pawn, local_team, entity_list, entity_ptr = offsets_mem(worker_pm, worker_client)
            if not local_pawn or not entity_list or not entity_ptr:
                shared_snapshot["local"] = None
                shared_snapshot["entities"] = []
                time.sleep(0.05)
                continue

            local_pos = read_vec3(worker_pm, local_pawn + m_vOldOrigin)
            pitch, yaw = (0.0, 0.0)
            try:
                view = worker_pm.read_bytes(worker_client + dwViewAngles, 8)
                if view:
                    pitch, yaw = struct.unpack("ff", view)
            except Exception:
                pass

            entities = []
            for i in range(1, 65):
                try:
                    entity_data = client_mem(worker_pm, i, entity_ptr, entity_list, local_pawn, local_team)
                    if not entity_data:
                        continue
                    ent_team, _, pawn, _, _ = entity_data
                    ent_yaw = None
                    try:
                        eye = read_vec2(worker_pm, pawn + m_angEyeAngles)
                        if eye:
                            ent_yaw = float(eye[1])
                    except Exception:
                        ent_yaw = None
                    pos = read_vec3(worker_pm, pawn + m_vOldOrigin)
                    entities.append({
                        "x": float(pos[0]),
                        "y": float(pos[1]),
                        "team": int(ent_team),
                        "yaw": ent_yaw,
                    })
                except Exception:
                    continue

            shared_snapshot["local"] = {
                "x": float(local_pos[0]),
                "y": float(local_pos[1]),
                "yaw": float(yaw),
                "team": int(local_team),
            }
            shared_snapshot["entities"] = entities
            time.sleep(frame_dt)
        except Exception:
            if settings_proxy.get("debug_worker_crashes", False):
                _log_exception("[radar-worker] crashed.")
            time.sleep(0.15)

def esp(draw_list):
    global center_x_circle, center_y_circle, _last_overlay_meta, _overlay_cached_lists

    if settings is None:
        return

    # Single shared settings snapshot per frame to reduce proxy chatter.
    s = settings.snapshot()
    if not s.get("master_enabled", True):
        return
    if not is_cs2_window_active() or not s.get("esp_enable", True):
        return

    perf_tier = _perf_tier_enabled(s)
    _update_overlay_sidecars(s)

    draw_eye_lines = bool(s.get("esp_eye_lines", True)) and perf_tier < 2
    draw_skeleton = bool(s.get("esp_skeleton", True)) and perf_tier < 3
    draw_names = bool(s.get("esp_names", True)) and perf_tier < 3
    draw_weapons = bool(s.get("esp_weapons", True)) and perf_tier < 3
    draw_team_list = bool(s.get("esp_show_team_list", True)) and perf_tier < 3
    draw_spectator_list = bool(s.get("esp_show_spectator_list", False)) and perf_tier < 3
    draw_map_status = bool(s.get("esp_show_map_status", True))

    center_x = WINDOW_WIDTH / 2
    center_y = WINDOW_HEIGHT * 0.90
    view_matrix, local_player_pawn_addr, local_player_team, entity_list, entity_ptr = offsets_mem(pm, client)
    if local_player_team == 0 or entity_ptr == 0:
        return
    local_pos = read_vec3(pm, local_player_pawn_addr + m_vOldOrigin) if local_player_pawn_addr else None
    vis_checker = ensure_vischeck_ready(pm, settings) if s.get("visibility_esp_enabled", True) else None
    vis_budget = max(0, int(s.get("vischeck_max_per_frame", 4)))
    vis_budget = min(vis_budget, (4, 3, 2, 1)[perf_tier])
    vis_used = 0

    if s.get("draw_fov", True):
        radius = get_current_dynamic_fov(s.get("aimbot_fov", 40.0)) if s.get("aim_dynamic_fov_enabled", False) else s.get("aimbot_fov", 40.0)
        radius = max(1.0, float(radius))
        screen_radius = radius / 100.0 * min(center_x_circle, center_y_circle)
        draw_circle_outline(draw_list, center_x_circle, center_y_circle, screen_radius, s.get("esp_fov_color", (1.0, 1.0, 1.0, 0.7)), 1.0)

    if s.get("draw_crosshair", True):
        draw_circle_outline(draw_list, center_x_circle, center_y_circle, 3, s.get("esp_crosshair_color", (0.0, 1.0, 0.0, 1.0)), 1.0)

    if draw_team_list or draw_spectator_list:
        now_lists = time.time()
        list_refresh = 0.70 * (1.0 + 0.55 * perf_tier)
        if (now_lists - _overlay_cached_lists["time"]) >= list_refresh:
            t_players, ct_players, spectators = collect_team_and_spectator_info(pm, entity_ptr, entity_list)
            _overlay_cached_lists = {"time": now_lists, "t": t_players, "ct": ct_players, "spec": spectators}
        else:
            t_players = _overlay_cached_lists["t"]
            ct_players = _overlay_cached_lists["ct"]
            spectators = _overlay_cached_lists["spec"]
    else:
        t_players, ct_players, spectators = [], [], []

    entity_candidates = []
    entity_scan_cap = (48, 36, 26, 18)[perf_tier]
    for i in range(1, entity_scan_cap + 1):
        try:
            client_m = client_mem(pm, i, entity_ptr, entity_list, local_player_pawn_addr, local_player_team)
            if not client_m:
                continue

            entity_team, _, entity_pawn_addr, entity_controller, spotted = client_m
            is_visible = bool(spotted)
            if s.get("visibility_esp_enabled", True):
                if vis_checker is not None and local_pos is not None and vis_used < vis_budget:
                    entity_pos = read_vec3(pm, entity_pawn_addr + m_vOldOrigin)
                    is_visible = check_player_visibility(local_pos, entity_pos, vis_checker, eye_offset=float(s.get("aimbot_eye_height", 64.0)))
                    vis_used += 1
                elif vis_checker is None:
                    is_visible = bool(spotted)
            else:
                is_visible = True
            if entity_team == 2 and not s.get("esp_show_t", True):
                continue
            if entity_team == 3 and not s.get("esp_show_ct", True):
                continue
            if s.get("esp_visible_only", False) and not is_visible:
                continue
            entity_candidates.append((entity_team, entity_pawn_addr, entity_controller, is_visible))
        except Exception:
            continue

    frame_name_cache = {}
    frame_weapon_cache = {}
    for entity_team, entity_pawn_addr, entity_controller, is_visible in entity_candidates:
        try:
            bottom_left_x, bottom_y, bone_matrix, headX, headY, _, head_pos = esp_line(pm, entity_pawn_addr, view_matrix, WINDOW_WIDTH, WINDOW_HEIGHT)
            if head_pos[1] < 0:
                continue

            immunity = esp_immunity(pm, entity_pawn_addr)
            is_ally = entity_team == local_player_team
            if is_ally:
                espcolor = s.get("esp_ally_color_visible", s.get("esp_ally_color")) if is_visible else s.get("esp_ally_color_invisible", s.get("esp_ally_color"))
                linecolor = s.get("esp_ally_snapline_color", s.get("esp_ally_color"))
            else:
                espcolor = s.get("esp_enemy_color_visible", s.get("esp_enemy_color")) if is_visible else s.get("esp_enemy_color_invisible", s.get("esp_enemy_color"))
                linecolor = s.get("esp_enemy_snapline_color", s.get("esp_enemy_color"))

            filled_box_color = s.get("esp_box_fill_spotted_color") if is_visible else s.get("esp_box_fill_normal_color")
            if immunity:
                filled_box_color = s.get("esp_box_fill_immune_color")

            if s.get("esp_snap_lines", False):
                draw_line(draw_list, bottom_left_x, bottom_y, center_x, center_y, linecolor, 1.0)

            leftX, leg_pos, rightX, deltaZ = esp_box(pm, bone_matrix, view_matrix, headX, headY, head_pos, WINDOW_WIDTH, WINDOW_HEIGHT)
            if s.get("esp_box", True):
                draw_box(draw_list, leftX, leg_pos[1], rightX, head_pos[1], s.get("esp_box_border_color"), 1.0)
            if s.get("esp_filled_box", True):
                draw_filled_box(draw_list, leftX, leg_pos[1], rightX, head_pos[1], filled_box_color)
            if s.get("esp_corners", True):
                draw_corners(draw_list, leftX, leg_pos[1], rightX, head_pos[1], espcolor, 1.0, 0.3)

            if s.get("esp_head_dot", True):
                hx, hy, hr = esp_headbox(pm, bone_matrix, view_matrix, rightX, leftX, WINDOW_WIDTH, WINDOW_HEIGHT)
                draw_circle(draw_list, hx, hy, hr, s.get("esp_head_dot_color"))

            if draw_eye_lines:
                fx, fy, end_point = esp_head_line(pm, entity_pawn_addr, bone_matrix, view_matrix, 100, WINDOW_WIDTH, WINDOW_HEIGHT)
                draw_line(draw_list, fx, fy, end_point[0], end_point[1], s.get("esp_eye_line_color"), 1.0)

            if draw_skeleton:
                conn, bone_positions = esp_bone(pm, bone_matrix, view_matrix, WINDOW_WIDTH, WINDOW_HEIGHT)
                for a, b in conn:
                    if a in bone_positions and b in bone_positions:
                        draw_line(draw_list, bone_positions[a][0], bone_positions[a][1], bone_positions[b][0], bone_positions[b][1], s.get("esp_skeleton_color"), 1.0)

            if draw_names:
                if entity_controller not in frame_name_cache:
                    frame_name_cache[entity_controller] = esp_nickname(pm, entity_controller)
                draw_nickname(draw_list, frame_name_cache[entity_controller], head_pos, rightX, leftX, s.get("esp_name_color"))

            if draw_weapons:
                if entity_pawn_addr not in frame_weapon_cache:
                    frame_weapon_cache[entity_pawn_addr] = esp_weapon(pm, entity_pawn_addr)
                draw_weapon(draw_list, frame_weapon_cache[entity_pawn_addr], leg_pos, rightX, leftX, s.get("esp_weapon_color"))

            if s.get("esp_health_bar", True):
                hp_bar_x_left, hp_bar_y_top, hp_bar_y_bottom, current_hp_height = esp_hp(pm, entity_pawn_addr, deltaZ, head_pos, leftX)
                draw_line(draw_list, hp_bar_x_left, hp_bar_y_top, hp_bar_x_left, hp_bar_y_bottom + current_hp_height, s.get("esp_health_bar_bg_color"), 2.0)
                draw_line(draw_list, hp_bar_x_left, hp_bar_y_bottom, hp_bar_x_left, hp_bar_y_bottom + current_hp_height, s.get("esp_health_bar_color"), 2.0)

            if s.get("esp_armor_bar", True):
                armor_bar_x_left, armor_bar_y_top, armor_bar_x_right, current_armor_width = esp_br(pm, entity_pawn_addr, deltaZ, head_pos, rightX, leftX, leg_pos)
                draw_line(draw_list, armor_bar_x_left, armor_bar_y_top, armor_bar_x_right, armor_bar_y_top, s.get("esp_health_bar_bg_color"), 2.0)
                draw_line(draw_list, armor_bar_x_left, armor_bar_y_top, armor_bar_x_left + current_armor_width, armor_bar_y_top, s.get("esp_armor_bar_color"), 2.0)
        except Exception:
            continue

    try:
        if s.get("esp_bomb", True) and csBomb.isPlanted(pm, client):
            bomb_pos = csBomb.getPositionWTS(pm, client, view_matrix, WINDOW_WIDTH, WINDOW_HEIGHT)
            if bomb_pos and bomb_pos[0] > 0 and bomb_pos[1] > 0:
                time_left = csBomb.getBombTime(pm, client)
                defuse_time = csBomb.getDefuseTime(pm, client)
                text = f"BOMB: {time_left:.1f}s"
                is_defusing = defuse_time > 0
                if is_defusing:
                    text += f" | DEFUSE: {defuse_time:.1f}s"
                draw_text(draw_list, bomb_pos[0], bomb_pos[1], text, s.get("esp_bomb_defusing_color") if is_defusing else s.get("esp_bomb_color"))
    except Exception:
        pass

    if s.get("esp_dropped_weapons", False) and perf_tier < 3 and weapon_draw_list is not None:
        for weapon in weapon_draw_list:
            draw_text(draw_list, weapon["pos"][0], weapon["pos"][1], weapon["name"], s.get("esp_dropped_weapon_color"))

    if draw_team_list:
        team_lines = [
            f"T ({len(t_players)}): {', '.join(t_players[:3]) if t_players else 'none'}",
            f"CT ({len(ct_players)}): {', '.join(ct_players[:3]) if ct_players else 'none'}",
        ]
        draw_info_box(draw_list, 20, 110, "TEAM LIST", team_lines)

    if draw_spectator_list:
        spec_lines = spectators[:7] if spectators else ["None"]
        draw_info_box(draw_list, 20, 190, "SPECTATORS", spec_lines, s.get("esp_spectator_color"))

    if draw_map_status:
        now = time.time()
        if now - _last_overlay_meta["map_time"] > (1.4 + 0.65 * perf_tier):
            _last_overlay_meta["map_name"] = get_current_map_name(pm)
            _last_overlay_meta["map_time"] = now
        map_loaded = bool(s.get("visibility_map_loaded", False))
        map_path = s.get("visibility_map_path", "")
        map_lines = [
            f"Map: {_last_overlay_meta['map_name']}",
            f"VisMap: {'loaded' if map_loaded else 'not loaded'}",
            f"File: {os.path.basename(map_path) if map_path else 'none'}",
            f"Time: {time.strftime('%H:%M:%S')}",
        ]
        draw_info_box(draw_list, 20, 320, "MAP STATUS", map_lines, s.get("esp_map_color"))

    if s.get("radar_enable", False) and radar_snapshot is not None:
        draw_radar(draw_list, radar_snapshot, s)

    if bool(s.get("adaptive_perf_show_status", True)):
        profile_idx = int(_adaptive_perf_state.get("profile", 1))
        profile_name = _PERF_PROFILE_NAMES.get(profile_idx, "BALANCED")
        cpu_now = float(_resource_budget_state.get("cpu", 0.0))
        ram_now = float(_resource_budget_state.get("ram_mb", 0.0))
        perf_text = (
            f"Perf Tier {perf_tier} ({profile_name}) | "
            f"EMA FPS {int(_adaptive_perf_state.get('ema_fps', 0.0))} | "
            f"CPU {cpu_now:.1f}% RAM {ram_now:.0f}MB"
        )
        perf_color = (0.9, 0.9, 0.95, 1.0)
        if perf_tier >= 2:
            perf_color = (1.0, 0.75, 0.25, 1.0)
        if perf_tier >= 3:
            perf_color = (1.0, 0.35, 0.25, 1.0)
        draw_text(draw_list, 20, 75, perf_text, perf_color)

    panic_key = win32_key_map.get(str(s.get("panic_key", "DELETE")).upper(), 0)
    if panic_key and (win32api.GetAsyncKeyState(panic_key) & 0x8000):
        settings.set("master_enabled", False)
        settings.set("aimbot_enable", False)
        settings.set("trigger_enable", False)
        settings.set("bunnyhop_enable", False)
        settings.set("norecoil_enable", False)
        settings.set("radar_enable", False)

settings = None
client = None
pm = None

# ==============================
# Overlay Runtime
# ==============================

def wallhack(s):
    global settings, weapon_draw_list, radar_snapshot, client, pm
    settings = s
    client, pm = get_descriptor_blocking()
    weapon_draw_list = []
    radar_snapshot = {"local": None, "entities": []}

    try:
        _LOGGER.info("[overlay] Unified mode active: INSERT toggles menu, F5 toggles master enable.")
        render_loop(esp)
    finally:
        weapon_draw_list = []
        radar_snapshot = {"local": None, "entities": []}

tabs_config = config_tabs

def begin_disabled(disabled=True):
    if disabled:
        imgui.push_style_var(imgui.STYLE_ALPHA, imgui.get_style().alpha * 0.5)
    return disabled

def end_disabled(disabled):
    if disabled:
        imgui.pop_style_var()

def check_dependencies(element, settings):
    for (key, expected) in element.get("dependencies", []):
        if settings.get(key) != expected:
            return False
    return True


def draw_unified_overlay_menu(settings_obj):
    state = _overlay_menu_state
    if not state["visible"]:
        return
    if menu_main_font is None:
        return

    if len(state["tab_animations"]) != len(config_tabs):
        state["tab_animations"] = [0.0] * len(config_tabs)

    if state["config_combo"] is None:
        config_tab_index = next((i for i, tab in enumerate(tabs_config) if tab["name"] == "CONFIGS"), -1)
        if config_tab_index != -1:
            state["config_combo"] = next(
                (el for el in tabs_config[config_tab_index]["elements"] if el["name"] == "config_profile"),
                None
            )
            if state["config_combo"] is not None:
                state["config_combo"]["items"] = settings_obj.list_configs()

    current_time = time.time()
    io = imgui.get_io()

    if state["prev_tab"] != state["current_tab"]:
        state["last_tab_change_time"] = current_time
        state["content_alpha"] = 0.0
        state["prev_tab"] = state["current_tab"]

    for i in range(len(state["tab_animations"])):
        if i == state["current_tab"]:
            state["tab_animations"][i] = min(state["tab_animations"][i] + io.delta_time * 2, 1.0)
        else:
            state["tab_animations"][i] = 0.0

    fade_duration = 0.5
    state["content_alpha"] = min((current_time - state["last_tab_change_time"]) / fade_duration, 1.0)

    menu_w, menu_h = 800, 600
    menu_x = max(10, int((WINDOW_WIDTH - menu_w) * 0.5))
    menu_y = max(10, int((WINDOW_HEIGHT - menu_h) * 0.5))

    imgui.set_next_window_size(menu_w, menu_h)
    imgui.set_next_window_position(menu_x, menu_y)
    imgui.begin(
        "MainWindow",
        flags=imgui.WINDOW_NO_TITLE_BAR | imgui.WINDOW_NO_RESIZE | imgui.WINDOW_NO_COLLAPSE
    )
    imgui.begin_child("MainContent", 0, 0, border=False)

    imgui.begin_group()
    state["current_tab"] = custom_tab_bar(
        config_tabs,
        state["current_tab"],
        120,
        menu_icon_font,
        menu_main_font,
        state["tab_animations"],
    )
    imgui.end_group()

    imgui.same_line()
    is_visuals_tab = tabs_config[state["current_tab"]]["name"] == "VISUALS"
    content_width = 450 if is_visuals_tab else 0

    imgui.begin_child("TabContent", content_width, 0, border=False)
    if state["content_alpha"] > 0:
        imgui.push_style_var(imgui.STYLE_ALPHA, state["content_alpha"])

        current_tab_config = tabs_config[state["current_tab"]]
        section_header(current_tab_config["name"], menu_main_font)

        if is_visuals_tab:
            imgui.columns(2, "visuals_settings", border=False)

        for element in current_tab_config["elements"]:
            disabled = not check_dependencies(element, settings_obj)
            disable_state = begin_disabled(disabled)

            if element["type"] == "checkbox":
                current_val = settings_obj.get(element["name"], element.get("default", False))
                changed, new_val = custom_checkbox(element["label"], current_val, menu_main_font)
                if changed and not disabled:
                    settings_obj.set(element["name"], new_val)

            elif element["type"] == "slider":
                current_val = settings_obj.get(element["name"], element.get("default", 0.0))
                changed, new_val = custom_slider_float(
                    element["label"], current_val, element["min"], element["max"],
                    element.get("format", "%.2f"), menu_main_font
                )
                if changed and not disabled:
                    settings_obj.set(element["name"], new_val)

            elif element["type"] == "combo":
                current_val = settings_obj.get(element["name"], element.get("default", 0))
                new_val = custom_combo(element["label"], current_val, element["items"], menu_main_font)
                if new_val is not None and new_val != current_val and not disabled:
                    settings_obj.set(element["name"], new_val)

            elif element["type"] == "color":
                current_val = settings_obj.get(element["name"])
                changed, new_val = color_cube(element["label"], current_val, menu_main_font)
                if changed and not disabled:
                    settings_obj.set(element["name"], new_val)
                if is_visuals_tab:
                    imgui.next_column()

            elif element["type"] == "bind":
                current_val = settings_obj.get(element["name"])
                new_val = key_bind(element["label"], current_val, menu_main_font)
                if new_val is not None and not disabled:
                    settings_obj.set(element["name"], new_val)

            elif element["type"] == "button":
                if custom_button(element["label"], menu_main_font) and not disabled:
                    if element["name"] == "config_save":
                        if state["config_filename"]:
                            settings_obj.save(state["config_filename"])
                    elif element["name"] == "config_load":
                        selected_idx = settings_obj.get("config_profile", 0)
                        if state["config_combo"] and selected_idx < len(state["config_combo"]["items"]):
                            selected_file = state["config_combo"]["items"][selected_idx]
                            if selected_file != "No configs found":
                                settings_obj.load(selected_file)
                    elif element["name"] == "config_refresh":
                        if state["config_combo"] is not None:
                            state["config_combo"]["items"] = settings_obj.list_configs()
                            settings_obj.set("config_profile", 0)
                    elif element["name"] == "config_reset":
                        settings_obj.reset()
                    elif element["name"] == "visibility_map_reload":
                        settings_obj.set("visibility_map_reload_needed", True)

            elif element["type"] == "text_input":
                changed, new_text = custom_text_input(element["label"], state["config_filename"], 64, menu_main_font)
                if changed:
                    state["config_filename"] = new_text

            elif element["type"] == "status":
                value = settings_obj.get(element["name"], "")
                if isinstance(value, bool):
                    status_text = "ON" if value else "OFF"
                else:
                    status_text = str(value).strip() or "N/A"
                pushed_status = _font_push_safe(menu_main_font)
                imgui.text(f"{element['label']}: {status_text}")
                _font_pop_safe(pushed_status)

            end_disabled(disable_state)

        if is_visuals_tab:
            imgui.columns(1)

        imgui.pop_style_var()

    imgui.end_child()

    if is_visuals_tab:
        imgui.same_line()
        imgui.begin_child("PreviewPanel", 0, 0, border=True)
        draw_esp_preview(settings_obj, menu_main_font)
        imgui.end_child()

    imgui.end_child()
    imgui.end()

def menu(s):
    global settings
    settings = s
    _LOGGER.info("[menu] Legacy standalone menu disabled. Use INSERT in unified overlay.")
    return

# ==============================
# SECTION 7: WORKER SUPERVISOR
# ==============================

def norecoil(settings):
    client, pm = get_descriptor_blocking()
    while True:
        s_cache = settings.snapshot(
            (
                "norecoil_stop",
                "master_enabled",
                "norecoil_enable",
                "norecoil_x",
                "norecoil_y",
                "debug_worker_crashes",
                "perf_profile",
            )
        )
        sleep_scale = _worker_sleep_scale(s_cache)
        if s_cache.get("norecoil_stop", False):
            break
        if not s_cache.get("master_enabled", True):
            _sleep_master_off(0.18, sleep_scale)
            continue
        if not s_cache.get("norecoil_enable", False) or not is_cs2_window_active():
            _sleep_idle(0.10, sleep_scale)
            continue
        try:
            player = pm.read_longlong(client + dwLocalPlayerPawn)
            x, y = no_recoil(pm, client, player)
            
            move_x = int(x * float(s_cache.get("norecoil_x", 1.0)))
            move_y = int(y * float(s_cache.get("norecoil_y", 1.0)))
            
            win32api.mouse_event(win32con.MOUSEEVENTF_MOVE, move_x, move_y, 0, 0)
        except Exception:
            if s_cache.get("debug_worker_crashes", False):
                _log_exception("[norecoil] worker loop crashed.")
        _sleep_active(0.006, sleep_scale)

def send_mouse_click():
    if win32api.GetAsyncKeyState(win32con.VK_LBUTTON) & 0x8000:
        return False
    win32api.mouse_event(win32con.MOUSEEVENTF_LEFTDOWN, 0, 0, 0, 0)
    time.sleep(0.01)
    win32api.mouse_event(win32con.MOUSEEVENTF_LEFTUP, 0, 0, 0, 0)
    return True

def triggerbot(settings):
    client, pm = get_descriptor_blocking()
    last_shot_time = 0.0
    while True:
        s_cache = settings.snapshot(
            (
                "triggerbot_stop",
                "master_enabled",
                "trigger_enable",
                "trigger_key",
                "trigger_attack_all",
                "trigger_flash_check",
                "trigger_delay",
                "trigger_always_on",
                "trigger_teammates",
                "trigger_cooldown",
                "perf_profile",
            )
        )
        sleep_scale = _worker_sleep_scale(s_cache)
        if s_cache.get("triggerbot_stop", False):
            break
        if not s_cache.get("master_enabled", True):
            _sleep_master_off(0.18, sleep_scale)
            continue
        if not s_cache.get("trigger_enable", False) or not is_cs2_window_active():
            _sleep_idle(0.10, sleep_scale)
            continue
           
        key_code = win32_key_map.get(str(s_cache.get("trigger_key", "MOUSE4")).upper(), 0)
        if key_code <= 0:
            _sleep_idle(0.08, sleep_scale)
            continue
        if s_cache.get("trigger_always_on", False) or (win32api.GetAsyncKeyState(key_code) & 0x8000):
            try:
                player = pm.read_longlong(client + dwLocalPlayerPawn)
                if not player:
                    _sleep_active(0.006, sleep_scale)
                    continue

                if s_cache.get("trigger_flash_check", True):
                    flash_duration = pm.read_float(player + m_flFlashDuration)
                    if flash_duration > 0:
                        _sleep_idle(0.10, sleep_scale)
                        continue

                entityId = pm.read_int(player + m_iIDEntIndex)
                if entityId and entityId > 0:
                    entList = pm.read_longlong(client + dwEntityList)
                    if not entList:
                        continue
                    entEntry = pm.read_longlong(entList + 0x8 * (entityId >> 9) + 0x10)
                    if not entEntry:
                        continue
                    entity = pm.read_longlong(entEntry + 112 * (entityId & 0x1FF))
                    if not entity:
                        continue
                    
                    entityTeam = pm.read_int(entity + m_iTeamNum)
                    playerTeam = pm.read_int(player + m_iTeamNum)
                    if entityTeam is None or playerTeam is None:
                        continue
                    
                    can_attack = (
                        s_cache.get("trigger_attack_all", False)
                        or s_cache.get("trigger_teammates", False)
                        or entityTeam != playerTeam
                    )
                    if can_attack:
                        entityHp = pm.read_int(entity + m_iHealth) or 0
                        immunity = pm.read_int(entity + m_bGunGameImmunity) or 0
                        if entityHp > 0 and immunity == 0:
                            now = time.time()
                            cooldown = max(0.0, float(s_cache.get("trigger_cooldown", 0.0) or 0.0))
                            if (now - last_shot_time) >= cooldown:
                                time.sleep(max(0.0, float(s_cache.get("trigger_delay", 0.0) or 0.0)))
                                if send_mouse_click():
                                    last_shot_time = now
            except Exception:
                _sleep_idle(0.08, sleep_scale)
        else:
            _sleep_idle(0.05, sleep_scale)
            continue

        _sleep_active(0.006, sleep_scale)


WORKER_SPECS = [
    ("triggerbot", triggerbot),
    ("bunnyhop", bunnyhop),
    ("wallhack", wallhack),
    ("aimbot", aimbot),
    ("norecoil", norecoil),
    ("auto_accept", auto_accept),
]

STOP_FLAG_BY_WORKER = {
    "aimbot": "aim_stop",
    "triggerbot": "triggerbot_stop",
    "bunnyhop": "bhop_stop",
    "wallhack": "wallhack_stop",
    "norecoil": "norecoil_stop",
    "auto_accept": "autoaccept_stop",
}
ENABLE_FLAG_BY_WORKER = {
    "aimbot": "aimbot_enable",
    "triggerbot": "trigger_enable",
    "bunnyhop": "bunnyhop_enable",
    "wallhack": "esp_enable",
    "norecoil": "norecoil_enable",
    "auto_accept": "autoaccept_enable",
}

ALL_STOP_FLAGS = tuple(sorted(set(STOP_FLAG_BY_WORKER.values())))
ALL_ENABLE_FLAGS = tuple(sorted(set(ENABLE_FLAG_BY_WORKER.values())))
WORKER_STATE_STOPPED = "STOPPED"
WORKER_STATE_STARTING = "STARTING"
WORKER_STATE_RUNNING = "RUNNING"
WORKER_STATE_STOPPING = "STOPPING"


def _apply_master_state(settings, enabled, announce=True):
    enabled = bool(enabled)
    settings.set("master_enabled", enabled)
    for stop_key in ALL_STOP_FLAGS:
        settings.set(stop_key, not enabled)
    if announce:
        _LOGGER.info("[hotkey] F5 -> %s (all workers)", "ENABLED" if enabled else "DISABLED")


def _worker_desired_state(loop_snapshot, worker_name, master_state):
    stop_key = STOP_FLAG_BY_WORKER.get(worker_name)
    enable_key = ENABLE_FLAG_BY_WORKER.get(worker_name)
    enabled = bool(loop_snapshot.get(enable_key, True)) if enable_key else True
    stopped = bool(loop_snapshot.get(stop_key, False)) if stop_key else False
    desired = bool(master_state and enabled and not stopped)
    if not master_state:
        reason = "master_disabled"
    elif not enabled:
        reason = f"feature_disabled:{enable_key}"
    elif stopped:
        reason = f"stop_flag:{stop_key}"
    else:
        reason = "enabled"
    return desired, reason


def _set_worker_state(meta, worker_name, new_state, reason):
    old = meta.get("state", WORKER_STATE_STOPPED)
    if old != new_state:
        now = time.monotonic()
        sig = (old, new_state, str(reason))
        last_sig = meta.get("last_state_log_sig")
        last_at = float(meta.get("last_state_log_at", 0.0))
        if not (sig == last_sig and (now - last_at) < 1.0):
            _LOGGER.info(
                "[supervisor] state %s: %s -> %s (%s)",
                worker_name,
                old,
                new_state,
                reason,
            )
            meta["last_state_log_sig"] = sig
            meta["last_state_log_at"] = now
        meta["state"] = new_state


def _stop_worker_process(worker_name, workers, restart_meta, reason="requested", join_timeout=1.0):
    proc = workers.get(worker_name)
    meta = restart_meta[worker_name]
    if proc is None:
        _set_worker_state(meta, worker_name, WORKER_STATE_STOPPED, reason)
        return
    _set_worker_state(meta, worker_name, WORKER_STATE_STOPPING, reason)
    try:
        if proc.is_alive():
            proc.terminate()
            proc.join(timeout=max(0.1, float(join_timeout)))
            if proc.is_alive():
                proc.kill()
                proc.join(timeout=0.2)
    except Exception:
        pass
    workers.pop(worker_name, None)
    _set_worker_state(meta, worker_name, WORKER_STATE_STOPPED, reason)


def _run_with_restart(name, target, settings):
    def stopped_intentionally():
        if _SHUTDOWN_REQUESTED.is_set():
            return True
        key = STOP_FLAG_BY_WORKER.get(name)
        if key and settings.get(key, False):
            return True
        enable_key = ENABLE_FLAG_BY_WORKER.get(name)
        if enable_key and not bool(settings.get(enable_key, True)):
            return True
        if not bool(settings.get("master_enabled", True)):
            return True
        return False

    _LOGGER.info("[worker] %s booting (pid=%s)", name, os.getpid())
    _emit_runtime_event("worker.boot", worker=name, pid=os.getpid())
    try:
        target(settings)
        if not stopped_intentionally():
            _LOGGER.warning("[supervisor] %s exited unexpectedly.", name)
            _emit_runtime_event("worker.unexpected_exit", level="warning", worker=name)
    except KeyboardInterrupt:
        pass
    except SystemExit:
        pass
    except Exception as exc:
        if not stopped_intentionally():
            _LOGGER.error("[supervisor] %s crashed: %s", name, exc)
            _emit_runtime_event("worker.crash", level="error", worker=name, error=str(exc))
            _log_exception("[supervisor] crash traceback for %s", name)
    finally:
        _LOGGER.info("[worker] %s stopped (pid=%s)", name, os.getpid())
        _emit_runtime_event("worker.stop", worker=name, pid=os.getpid())


def _stop_workers(workers, restart_meta, join_timeout=1.5):
    for worker_name in list(workers.keys()):
        _stop_worker_process(
            worker_name,
            workers,
            restart_meta,
            reason="global_shutdown",
            join_timeout=join_timeout,
        )
    workers.clear()


def run_supervisor(settings, poll_interval=0.2, runtime_context=None):
    if runtime_context is not None:
        runtime_context.settings = settings
        runtime_context.shutdown_event = _SHUTDOWN_REQUESTED
        runtime_context.metadata.setdefault("supervisor", {})
    workers = {}
    restart_meta = {
        name: {
            "last_start": 0.0,
            "failures": 0,
            "eligible_at": 0.0,
            "last_exit_sig": None,
            "state": WORKER_STATE_STOPPED,
            "desired": False,
            "desired_reason": "init",
            "parked": False,
            "park_log_sent": False,
            "last_state_log_sig": None,
            "last_state_log_at": 0.0,
        }
        for name, _ in WORKER_SPECS
    }
    last_heartbeat = 0.0
    last_heartbeat_sig = None
    last_forced_heartbeat = 0.0
    min_start_interval = 1.2
    flap_threshold = 4
    f5_wait_release = False
    last_f5_toggle = 0.0
    f5_toggle_cooldown = 0.30

    bootstrap_state = settings.snapshot(("master_enabled",))
    master_state = bool(bootstrap_state.get("master_enabled", True))
    _apply_master_state(settings, master_state, announce=False)
    try:
        while not _SHUTDOWN_REQUESTED.is_set():
            now_wall = time.monotonic()
            loop_snapshot = settings.snapshot(("master_enabled",) + ALL_STOP_FLAGS + ALL_ENABLE_FLAGS)
            f5_state = int(win32api.GetAsyncKeyState(win32con.VK_F5))
            f5_down = bool(f5_state & 0x8000)
            f5_pressed = bool(f5_state & 1)
            if not f5_down:
                f5_wait_release = False
            if f5_pressed and not f5_wait_release:
                if (now_wall - last_f5_toggle) >= f5_toggle_cooldown:
                    master_state = not master_state
                    _apply_master_state(settings, master_state, announce=True)
                    loop_snapshot = settings.snapshot(("master_enabled",) + ALL_STOP_FLAGS + ALL_ENABLE_FLAGS)
                    last_f5_toggle = now_wall
                f5_wait_release = True

            desired_master = bool(loop_snapshot.get("master_enabled", master_state))
            if desired_master != master_state:
                master_state = desired_master
                _apply_master_state(settings, master_state, announce=True)
                loop_snapshot = settings.snapshot(("master_enabled",) + ALL_STOP_FLAGS + ALL_ENABLE_FLAGS)

            if not master_state:
                if workers:
                    _LOGGER.info("[supervisor] Master OFF: stopping all workers now.")
                    _emit_runtime_event("supervisor.master_disabled", worker_count=len(workers))
                    _stop_workers(workers, restart_meta)
                _sleep_master_off(max(0.15, float(poll_interval) * 3.0))
                continue

            for name, target in WORKER_SPECS:
                meta = restart_meta[name]
                desired, desired_reason = _worker_desired_state(loop_snapshot, name, master_state)
                enable_key = ENABLE_FLAG_BY_WORKER.get(name)
                enabled_now = bool(loop_snapshot.get(enable_key, True)) if enable_key else True

                # Anti-flap park mode: explicit disable -> enable needed to clear.
                if meta["parked"] and not enabled_now:
                    meta["parked"] = False
                    meta["park_log_sent"] = False
                    meta["failures"] = 0
                    meta["eligible_at"] = time.monotonic() + 0.25
                    _LOGGER.info("[supervisor] %s unparked after explicit disable.", name)
                if meta["parked"] and enabled_now and desired:
                    desired = False
                    desired_reason = "parked_after_flap"
                    if not meta.get("park_log_sent", False):
                        _LOGGER.warning(
                            "[supervisor] %s is parked after repeated failures. Disable+enable feature to retry.",
                            name,
                        )
                        meta["park_log_sent"] = True

                if desired != meta.get("desired", False) or desired_reason != meta.get("desired_reason", ""):
                    _LOGGER.info(
                        "[supervisor] desired %s: %s (%s)",
                        name,
                        "RUN" if desired else "STOP",
                        desired_reason,
                    )
                    _emit_runtime_event(
                        "supervisor.desired_state",
                        worker=name,
                        desired=bool(desired),
                        reason=desired_reason,
                    )
                    meta["desired"] = desired
                    meta["desired_reason"] = desired_reason

                proc = workers.get(name)
                now = time.monotonic()

                if proc is not None and not proc.is_alive():
                    exit_sig = (proc.pid, proc.exitcode)
                    if meta["last_exit_sig"] != exit_sig:
                        runtime = now - meta["last_start"] if meta["last_start"] > 0.0 else 999.0
                        intentional = (not desired) or _SHUTDOWN_REQUESTED.is_set() or (not master_state)
                        if intentional:
                            meta["failures"] = max(0, meta["failures"] - 1)
                            meta["eligible_at"] = now + 0.2
                        else:
                            crashed = (proc.exitcode != 0) or (runtime < 3.0)
                            if crashed:
                                meta["failures"] = min(10, meta["failures"] + 1)
                                delay = min(12.0, 0.75 * (2 ** (meta["failures"] - 1)))
                                meta["eligible_at"] = now + delay
                                _log_warning_throttled(
                                    f"supervisor.crash_backoff.{name}",
                                    3.0,
                                    "[supervisor] %s crashed/quit too fast (exit=%s, runtime=%.2fs). Backoff %.1fs.",
                                    name,
                                    proc.exitcode,
                                    runtime,
                                    delay,
                                )
                                if meta["failures"] >= flap_threshold:
                                    meta["parked"] = True
                                    meta["park_log_sent"] = False
                                    desired = False
                                    meta["desired"] = False
                                    meta["desired_reason"] = "parked_after_flap"
                                    _log_warning_throttled(
                                        f"supervisor.parked.{name}",
                                        5.0,
                                        "[supervisor] %s parked after %s rapid failures.",
                                        name,
                                        meta["failures"],
                                    )
                            else:
                                meta["failures"] = max(0, meta["failures"] - 1)
                                meta["eligible_at"] = now + 0.3
                        meta["last_exit_sig"] = exit_sig
                    workers.pop(name, None)
                    _set_worker_state(meta, name, WORKER_STATE_STOPPED, "exited")
                    proc = None

                if not desired:
                    _stop_worker_process(name, workers, restart_meta, reason=desired_reason, join_timeout=1.0)
                    continue

                proc = workers.get(name)
                if proc is not None and proc.is_alive():
                    _set_worker_state(meta, name, WORKER_STATE_RUNNING, "healthy")
                    continue

                if now < meta["eligible_at"]:
                    _set_worker_state(meta, name, WORKER_STATE_STOPPED, "cooldown")
                    continue
                if (now - meta["last_start"]) < min_start_interval:
                    _set_worker_state(meta, name, WORKER_STATE_STOPPED, "start_debounce")
                    continue

                _set_worker_state(meta, name, WORKER_STATE_STARTING, "spawn")
                new_proc = Process(target=_run_with_restart, args=(name, target, settings), name=name)
                new_proc.start()
                workers[name] = new_proc
                meta["last_start"] = time.monotonic()
                meta["last_exit_sig"] = None
                _set_worker_state(meta, name, WORKER_STATE_RUNNING, "spawned")
                _emit_runtime_event("supervisor.worker_spawned", worker=name, pid=new_proc.pid)
                if runtime_context is not None:
                    runtime_context.metadata["supervisor"][name] = {"pid": new_proc.pid, "state": WORKER_STATE_RUNNING}

            if (now_wall - last_heartbeat) >= 10.0:
                alive = tuple(sorted(name for name, proc in workers.items() if proc is not None and proc.is_alive()))
                desired_count = sum(1 for m in restart_meta.values() if m.get("desired", False))
                parked_count = sum(1 for m in restart_meta.values() if m.get("parked", False))
                hb_sig = (master_state, alive, desired_count, parked_count)
                should_force = (now_wall - last_forced_heartbeat) >= 60.0
                if hb_sig != last_heartbeat_sig or should_force:
                    _LOGGER.info(
                        "[supervisor] heartbeat | master=%s desired=%s parked=%s alive=%s",
                        master_state,
                        desired_count,
                        parked_count,
                        ",".join(alive) if alive else "none",
                    )
                    _emit_runtime_event(
                        "supervisor.heartbeat",
                        master=bool(master_state),
                        desired=int(desired_count),
                        parked=int(parked_count),
                        alive=list(alive),
                    )
                    if runtime_context is not None:
                        runtime_context.metadata["supervisor"]["alive_workers"] = list(alive)
                        runtime_context.metadata["supervisor"]["master_enabled"] = bool(master_state)
                    last_heartbeat_sig = hb_sig
                    if should_force:
                        last_forced_heartbeat = now_wall
                last_heartbeat = now_wall

            time.sleep(max(0.05, float(poll_interval)))
    except KeyboardInterrupt:
        _request_shutdown("Supervisor keyboard interrupt.")
    finally:
        _stop_workers(workers, restart_meta, join_timeout=2.0)


def startup_self_check(settings):
    sentinel = object()
    required_keys = [
        "master_enabled",
        "aimbot_enable",
        "trigger_enable",
        "bunnyhop_enable",
        "esp_enable",
        "radar_enable",
        "autoaccept_enable",
        "norecoil_enable",
        "radar_reader_fps",
        "radar_always_on_top",
        "perf_profile",
        "adaptive_perf_enabled",
        "adaptive_perf_level",
        "adaptive_perf_show_status",
        "resource_guard_enabled",
        "resource_cpu_budget_pct",
        "resource_ram_budget_mb",
        "resource_poll_interval",
        "runtime_cpu_percent",
        "runtime_ram_mb",
        "resource_status",
        "visibility_esp_enabled",
        "visibility_aim_enabled",
        "visibility_map_loaded",
        "visibility_map_path",
    ]
    missing = [key for key in required_keys if settings.get(key, sentinel) is sentinel]
    stop_mismatch = [
        name for name, _ in WORKER_SPECS
        if name not in STOP_FLAG_BY_WORKER
    ]
    _LOGGER.info(
        "[self-check] Settings keys linked: %s/%s",
        len(required_keys) - len(missing),
        len(required_keys),
    )
    if missing:
        _LOGGER.warning("[self-check] Missing keys: %s", ", ".join(missing))
    else:
        _LOGGER.info("[self-check] Required keys: OK")
    if stop_mismatch:
        _LOGGER.warning("[self-check] Worker stop-map mismatch: %s", ", ".join(stop_mismatch))
    else:
        _LOGGER.info("[self-check] Worker stop-map linkage: OK")


def report_ultimate_parity(max_list=120):
    try:
        main_path = os.path.join(_PROJECT_ROOT, "main.py")
        ultimate_path = os.path.join(_PROJECT_ROOT, "ultimate.py")
        if not os.path.exists(ultimate_path):
            _LOGGER.info("[parity] ultimate.py not found; parity check skipped.")
            return

        report = build_function_parity_report(main_path, ultimate_path)
        missing = report["missing"]
        extra = report["extra"]

        _LOGGER.info("[parity] defs in ultimate.py: %s", report["reference_count"])
        _LOGGER.info("[parity] defs in main.py: %s", report["main_count"])
        _LOGGER.info("[parity] missing-in-main: %s", len(missing))
        if missing:
            _LOGGER.info("[parity] missing names: %s", ", ".join(missing[:max_list]))
        _LOGGER.info("[parity] extra-in-main: %s", len(extra))
        if extra:
            _LOGGER.info("[parity] extra names: %s", ", ".join(extra[:max_list]))
        _emit_runtime_event(
            "parity.report",
            missing_count=len(missing),
            extra_count=len(extra),
            missing_preview=missing[: min(len(missing), max_list)],
            extra_preview=extra[: min(len(extra), max_list)],
        )
    except Exception:
        _log_exception("[parity] function parity check failed.")


# ==============================
# Ultimate Compatibility Layer
# ==============================

_compat_memory_readers = {}
_compat_last_press = {}


def _clamp(value, lo, hi):
    return max(lo, min(hi, value))


def _snap(value, step=1.0):
    try:
        step = float(step)
        if step <= 0:
            return float(value)
        return round(float(value) / step) * step
    except Exception:
        return value


def _clamp255(value):
    return int(_clamp(int(round(float(value))), 0, 255))


def _rgb(r, g, b, a=255):
    return (_clamp255(r) / 255.0, _clamp255(g) / 255.0, _clamp255(b) / 255.0, _clamp255(a) / 255.0)


def _colorref(r, g, b):
    return win32api.RGB(_clamp255(r), _clamp255(g), _clamp255(b))


def _draw_shadow(draw_list, x, y, text, color=(0.0, 0.0, 0.0, 1.0)):
    shadow_color = imgui.get_color_u32_rgba(*color)
    draw_list.add_text(x + 1, y + 1, shadow_color, str(text))


def _esp_vis_enabled(settings_obj=None):
    s = settings_obj or settings
    if s is None:
        return False
    return bool(s.get("visibility_esp_enabled", True))


def _get_gscript_maps_dir():
    path = os.path.join(_REPO_ROOT, "maps")
    os.makedirs(path, exist_ok=True)
    return path


def register_memory_reader(handle, reader):
    _compat_memory_readers[int(handle)] = reader
    return reader


def unregister_memory_reader(handle):
    _compat_memory_readers.pop(int(handle), None)


def _get_reader_for_handle(handle):
    return _compat_memory_readers.get(int(handle))


def _get_slider_spec(name, default_min=0.0, default_max=1.0, default_step=0.01):
    for tab in config_tabs:
        for element in tab.get("elements", []):
            if element.get("type") == "slider" and element.get("name") == name:
                return {
                    "min": float(element.get("min", default_min)),
                    "max": float(element.get("max", default_max)),
                    "step": float(default_step),
                    "format": element.get("format", "%.2f"),
                }
    return {"min": float(default_min), "max": float(default_max), "step": float(default_step), "format": "%.2f"}


def _lo_word(value):
    return int(value) & 0xFFFF


def _hi_word(value):
    return (int(value) >> 16) & 0xFFFF


def _sign16(value):
    value = int(value) & 0xFFFF
    return value - 0x10000 if value & 0x8000 else value


def _init_config_path():
    path = os.path.join(_REPO_ROOT, "configs")
    os.makedirs(path, exist_ok=True)
    return path


def _iter_menu_fields():
    for tab in config_tabs:
        for element in tab.get("elements", []):
            yield tab.get("name", ""), element


def _lazy_import_features():
    return {
        "imgui": imgui,
        "glfw": glfw,
        "OpenGL.GL": gl,
    }


def _set_cfg_status(settings_obj, status):
    if settings_obj is not None:
        settings_obj.set("config_status", str(status))


def _set_crash_status(settings_obj, status):
    if settings_obj is not None:
        settings_obj.set("crash_status", str(status))
    _LOGGER.error("[status] crash: %s", status)


def _set_overlay_capture_excluded(hwnd, excluded):
    return set_overlay_capture_excluded(hwnd, excluded)


def _set_radar_capture_excluded(hwnd, excluded):
    return set_overlay_capture_excluded(hwnd, excluded)


def _start_safe_thread(name, target, *args, **kwargs):
    def runner():
        try:
            target(*args, **kwargs)
        except Exception:
            _log_exception("[thread] %s crashed", name)
    t = threading.Thread(target=runner, name=name, daemon=True)
    t.start()
    return t


def _wait_for_cs2_with_overlay(timeout=None):
    return wait_cs2(timeout=timeout)


def angle_to_direction(yaw_deg):
    yaw = math.radians(float(yaw_deg))
    return math.cos(yaw), math.sin(yaw)


def point_along_direction(origin, yaw_deg, distance):
    ox, oy = float(origin[0]), float(origin[1])
    dx, dy = angle_to_direction(yaw_deg)
    return ox + dx * float(distance), oy + dy * float(distance)


def clamp_box_to_screen(x1, y1, x2, y2, width=WINDOW_WIDTH, height=WINDOW_HEIGHT):
    return (
        _clamp(float(x1), 0.0, float(width)),
        _clamp(float(y1), 0.0, float(height)),
        _clamp(float(x2), 0.0, float(width)),
        _clamp(float(y2), 0.0, float(height)),
    )


def descritptor():
    return get_descriptor_blocking()


def draw_crosshair(draw_list, cx=None, cy=None, color=None, size=5.0, thickness=1.0):
    if cx is None:
        cx = center_x_circle
    if cy is None:
        cy = center_y_circle
    if color is None:
        color = settings.get("esp_crosshair_color", (0.0, 1.0, 0.0, 1.0)) if settings else (0.0, 1.0, 0.0, 1.0)
    draw_line(draw_list, cx - size, cy, cx + size, cy, color, thickness)
    draw_line(draw_list, cx, cy - size, cx, cy + size, color, thickness)


def draw_fps_box(draw_list, fps, x=10, y=10):
    draw_info_box(draw_list, x, y, "PERF", [f"FPS: {int(fps)}"])


def draw_map_status(draw_list, lines, x=20, y=320):
    draw_info_box(draw_list, x, y, "MAP STATUS", list(lines), settings.get("esp_map_color", (0.82, 0.95, 1.0, 1.0)) if settings else (0.82, 0.95, 1.0, 1.0))


def draw_spectator_list(draw_list, spectators, x=20, y=190):
    draw_info_box(draw_list, x, y, "SPECTATORS", spectators if spectators else ["None"], settings.get("esp_spectator_color", (0.88, 0.88, 0.92, 1.0)) if settings else (0.88, 0.88, 0.92, 1.0))


def draw_team_list(draw_list, t_players, ct_players, x=20, y=110):
    lines = [
        f"T ({len(t_players)}): {', '.join(t_players[:3]) if t_players else 'none'}",
        f"CT ({len(ct_players)}): {', '.join(ct_players[:3]) if ct_players else 'none'}",
    ]
    draw_info_box(draw_list, x, y, "TEAM LIST", lines)


def draw_menu(settings_obj):
    draw_unified_overlay_menu(settings_obj)


def handle_menu(settings_obj=None):
    draw_unified_overlay_menu(settings_obj or settings)


def begin_hook():
    _LOGGER.info("[compat] begin_hook is a no-op in unified GLFW mode.")
    return True


def end_hook():
    return True


def wnd_proc(hwnd=None, msg=0, wparam=0, lparam=0):
    return 0


def ensure_offsets_loaded():
    return bool(offsets) and bool(client_dll)


def ensure_qapp():
    return None


def esp_aim(draw_list):
    esp(draw_list)


def exit_program(code=0):
    raise SystemExit(code)


def get_entities(pm_obj=None, client_base=None):
    out = []
    pm_ref = pm_obj or pm
    client_ref = client_base or client
    if not pm_ref or not client_ref:
        return out
    view_matrix, local_pawn, local_team, entity_list, entity_ptr = offsets_mem(pm_ref, client_ref)
    if not local_pawn or not entity_ptr:
        return out
    for i in range(1, 65):
        data = client_mem(pm_ref, i, entity_ptr, entity_list, local_pawn, local_team)
        if not data:
            continue
        team, _, pawn, controller, spotted = data
        pos = read_vec3(pm_ref, pawn + m_vOldOrigin)
        out.append({
            "index": i,
            "team": int(team),
            "pawn": int(pawn),
            "controller": int(controller),
            "spotted": bool(spotted),
            "pos": (float(pos[0]), float(pos[1]), float(pos[2])) if pos else None,
        })
    return out


def get_module_base(pid, module_name):
    return GetModuleBaseAddress(pid, module_name)


def get_mouse_pos():
    return win32api.GetCursorPos()


def get_offsets():
    return {"offsets": offsets, "client_dll": client_dll}


def get_process_image_name(pid):
    try:
        return psutil.Process(int(pid)).name()
    except Exception:
        return ""


def get_vk_code(key_name):
    if key_name is None:
        return 0
    return win32_key_map.get(str(key_name).upper(), 0)


def get_weapon_name_from_pawn(pm_obj, pawn_addr):
    try:
        weapon_pointer = pm_obj.read_longlong(pawn_addr + m_pClippingWeapon)
        weapon_index = pm_obj.read_int(weapon_pointer + m_AttributeManager + m_Item + m_iItemDefinitionIndex)
        return get_weapon_name(weapon_index)
    except Exception:
        return None


def get_weapon_name_simple(weapon_id):
    return get_weapon_name(int(weapon_id)) or "unknown"


def initialize():
    ok = wait_cs2()
    if not ok:
        return False
    get_descriptor_blocking()
    return True


def is_cs2_running():
    return GetProcessIdByName(CS2_PROCESS_NAME) != 0


def key_down(vk):
    return bool(win32api.GetAsyncKeyState(int(vk)) & 0x8000)


def pressed(vk):
    return bool(win32api.GetAsyncKeyState(int(vk)) & 1)


def mouse_down(button=0):
    vk = win32con.VK_LBUTTON if button in (0, "left", "L") else win32con.VK_RBUTTON
    return bool(win32api.GetAsyncKeyState(vk) & 0x8000)


def mouse_clicked(button=0):
    vk = win32con.VK_LBUTTON if button in (0, "left", "L") else win32con.VK_RBUTTON
    return bool(win32api.GetAsyncKeyState(vk) & 1)


def mouse_just_pressed(button=0):
    key = f"mouse_{button}"
    now = mouse_down(button)
    before = _compat_last_press.get(key, False)
    _compat_last_press[key] = now
    return now and not before


def mouse_left_click():
    return send_mouse_click()


def move_mouse(dx, dy):
    win32api.mouse_event(win32con.MOUSEEVENTF_MOVE, int(dx), int(dy), 0, 0)


def send_mouse_flags(flags, dx=0, dy=0, data=0, extra=0):
    win32api.mouse_event(int(flags), int(dx), int(dy), int(data), int(extra))


def read_bytes(pm_obj, address, size):
    return pm_obj.read_bytes(int(address), int(size))


def read_int(pm_obj, address):
    return pm_obj.read_int(int(address))


def read_float(pm_obj, address):
    return pm_obj.read_float(int(address))


def read_string(pm_obj, address, max_length=64):
    return pm_obj.read_string(int(address), int(max_length))


def read_u64(pm_obj, address):
    return pm_obj.read_longlong(int(address))


def safe_read_uint64(pm_obj, address, default=0):
    try:
        value = read_u64(pm_obj, address)
        if value is None:
            return default
        return int(value)
    except Exception:
        return default


def read_matrix(pm_obj, base):
    return [pm_obj.read_float(base + i * 4) for i in range(16)]


def render_bone_esp(draw_list, pm_obj, bone_matrix, view_matrix, color=(1.0, 1.0, 1.0, 1.0), thickness=1.0):
    conn, bones = esp_bone(pm_obj, bone_matrix, view_matrix, WINDOW_WIDTH, WINDOW_HEIGHT)
    for a, b in conn:
        if a in bones and b in bones:
            draw_line(draw_list, bones[a][0], bones[a][1], bones[b][0], bones[b][1], color, thickness)


def reset_menu_config(settings_obj=None):
    s = settings_obj or settings
    if s is not None:
        s.reset()
        return True
    return False


def save_menu_config(filename, settings_obj=None):
    s = settings_obj or settings
    if s is None:
        return False
    return s.save(filename)


def load_menu_config(filename, settings_obj=None):
    s = settings_obj or settings
    if s is None:
        return False
    return s.load(filename)


def set_global_offsets(new_offsets, new_client_dll):
    global offsets, client_dll
    offsets = new_offsets
    client_dll = new_client_dll
    _LOGGER.info(
        "[compat] set_global_offsets updated dictionaries; runtime numeric offset globals stay unchanged until restart."
    )
    return True


def start_aim_rcs(settings_obj):
    return aimbot(settings_obj)


def update_fps_drag(x, y):
    return float(x), float(y)


def update_map_status_drag(x, y):
    return float(x), float(y)


def update_spectator_drag(x, y):
    return float(x), float(y)


def update_team_list_drag(x, y):
    return float(x), float(y)


def vk_to_key_name(vk):
    vk = int(vk)
    for name, code in win32_key_map.items():
        if int(code) == vk:
            return name
    return f"VK_{vk}"


def auto_map_loader(settings_obj=None):
    s = settings_obj or settings
    if s is None:
        return False
    s.set("visibility_map_reload_needed", True)
    return True


def main():
    if os.name != "nt":
        raise SystemExit("This script is Windows-only.")

    _SHUTDOWN_REQUESTED.clear()
    _install_signal_handlers()
    _log_runtime_identity()
    _emit_runtime_event("runtime.start", process=CS2_PROCESS_NAME, window=CS2_WINDOW_TITLE)

    if not _acquire_single_instance_guard():
        raise SystemExit(1)

    freeze_support()
    _LOGGER.info("[startup] Waiting for CS2...")
    if not wait_cs2():
        _release_single_instance_guard()
        raise SystemExit("Failed to detect CS2.")

    _LOGGER.info("[startup] CS2 detected. Launching workers...")
    _emit_runtime_event("runtime.cs2_detected")
    runtime_context = RuntimeContext(
        process_name=CS2_PROCESS_NAME,
        window_title=CS2_WINDOW_TITLE,
        project_root=_PROJECT_ROOT,
        repo_root=_REPO_ROOT,
        shutdown_event=_SHUTDOWN_REQUESTED,
    )
    try:
        with Manager() as manager:
            shared_settings = Settings(manager)
            runtime_context.settings = shared_settings
            startup_self_check(shared_settings)
            report_ultimate_parity()
            run_supervisor(shared_settings, runtime_context=runtime_context)
    except KeyboardInterrupt:
        _request_shutdown("KeyboardInterrupt received in main.")
    finally:
        _emit_runtime_event("runtime.stop")
        _release_single_instance_guard()


if __name__ == "__main__":
    main()
