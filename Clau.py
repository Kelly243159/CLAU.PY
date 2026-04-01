import os
import json
import time
import threading
import datetime
import customtkinter as ctk
from pynput import mouse, keyboard
from pynput.mouse import Button, Controller as MouseController
from pynput.keyboard import Key, Controller as KeyboardController
import pyautogui
from tkinter import filedialog, messagebox
import queue
import re
import pyperclip
import subprocess
import sys
import wave
import numpy as np
from PIL import Image, ImageTk
import base64
import io
import speech_recognition as sr
import pyttsx3
import pyaudio
from collections import Counter
import hashlib


# CONFIGURAÇÕES 


ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("dark-blue")

TASKS_FILE = "tasks.json"
CONFIG_FILE = "config.json"
LEARNING_FILE = "learning_data.json"
VOICE_PROFILES_FILE = "voice_profiles.json"

# ESTADO GLOBAL 
 

recording = False
playing = False
actions = []
current_task_name = ""
mouse_listener = None
keyboard_listener = None
task_queue = queue.Queue()
execution_thread = None
stop_execution_flag = False
last_mouse_position = None
mouse_trail = []
last_action_time = time.time()
voice_listening = False
voice_thread = None
clau_activated = False
wake_word = "clau"
last_command_time = 0
paused = False
pause_event = threading.Event()

# Controles
mouse_controller = MouseController()
keyboard_controller = KeyboardController()

# FUNÇÕES BÁSICAS 


def log(msg, level="INFO"):
    """Adiciona mensagem ao log com cores"""
    if 'log_box' in globals() and log_box:
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        colors = {
            "INFO": "#ffffff",
            "SUCCESS": "#10b981",
            "ERROR": "#ef4444",
            "WARNING": "#f59e0b",
            "VOICE": "#3b82f6",
            "SYSTEM": "#8b5cf6"
        }
        color = colors.get(level, "#ffffff")
        log_box.insert("end", f"[{timestamp}] {msg}\n")
        log_box.tag_add(f"color_{level}", "end-2c linestart", "end-1c lineend")
        log_box.tag_config(f"color_{level}", foreground=color)
        log_box.see("end")
        if 'app' in globals() and app:
            app.update()
    else:
        print(f"[{datetime.datetime.now().strftime('%H:%M:%S')}] [{level}] {msg}")

def load_tasks():
    """Carrega tarefas salvas"""
    if not os.path.exists(TASKS_FILE):
        return {}
    try:
        with open(TASKS_FILE, "r", encoding="utf-8") as f:
            tasks = json.load(f)
        log(f"📁 Carregadas {len(tasks)} tarefas", "SUCCESS")
        return tasks
    except Exception as e:
        log(f"❌ Erro ao carregar tarefas: {e}", "ERROR")
        return {}

def save_tasks(tasks):
    """Salva tarefas"""
    try:
        with open(TASKS_FILE, "w", encoding="utf-8") as f:
            json.dump(tasks, f, indent=2, ensure_ascii=False)
        log("✅ Tarefas salvas com sucesso", "SUCCESS")
        return True
    except Exception as e:
        log(f"❌ Erro ao salvar tarefas: {e}", "ERROR")
        return False

def update_task_list():
    """Atualiza lista de tarefas"""
    tasks = load_tasks()
    task_names = list(tasks.keys())
    if 'task_select' in globals() and task_select:
        current_value = task_select.get()
        task_select.configure(values=task_names)
        if task_names:
            if current_value in task_names:
                task_select.set(current_value)
            else:
                task_select.set(task_names[0])
        else:
            task_select.set("")
    if 'task_count_label' in globals():
        task_count_label.configure(text=f"📊 {len(task_names)} tarefas")
    log(f"📊 Lista atualizada: {len(task_names)} tarefas disponíveis", "INFO")

def delete_selected_task():
    """Exclui a tarefa selecionada"""
    task_name = task_select.get()
    if not task_name:
        voice_system.speak("Nenhuma tarefa selecionada para excluir.")
        log("⚠ Nenhuma tarefa selecionada", "WARNING")
        return
    if messagebox.askyesno("Confirmar Exclusão", f"Tem certeza que deseja excluir a tarefa '{task_name}'?\n\nEsta ação não pode ser desfeita."):
        tasks = load_tasks()
        if task_name in tasks:
            backup = {task_name: tasks[task_name]}
            backup_file = f"backup_{int(time.time())}.json"
            with open(backup_file, "w", encoding="utf-8") as f:
                json.dump(backup, f, indent=2)
            del tasks[task_name]
            if save_tasks(tasks):
                update_task_list()
                log(f"🗑️ Tarefa '{task_name}' excluída (backup em {backup_file})", "SUCCESS")
                voice_system.speak(f"Tarefa {task_name} excluída com sucesso.")
            else:
                log(f"❌ Falha ao excluir tarefa '{task_name}'", "ERROR")


# SISTEMA DE APRENDIZADO AVANÇADO 


class LearningSystem:
    def __init__(self):
        self.tasks_data = {}
        self.patterns = {}
        self.mistakes = []
        self.user_profiles = {}
        self.adaptive_delay = 0.3
        self.confidence_scores = {}
        self.intelligence_level = 1
        self.load_data()

    def load_data(self):
        """Carrega dados de aprendizado"""
        try:
            if os.path.exists(LEARNING_FILE):
                with open(LEARNING_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                self.tasks_data = data.get("tasks", {})
                self.patterns = data.get("patterns", {})
                self.mistakes = data.get("mistakes", [])
                self.user_profiles = data.get("user_profiles", {})
                self.adaptive_delay = data.get("adaptive_delay", 0.3)
                self.intelligence_level = data.get("intelligence_level", 1)
                log(f"📚 Dados de aprendizado carregados: {len(self.tasks_data)} tarefas", "SUCCESS")
                self._analyze_intelligence()
        except Exception as e:
            log(f"⚠ Erro ao carregar aprendizado: {e}", "WARNING")
            self._initialize_default_data()

    def _initialize_default_data(self):
        """Inicializa dados padrão"""
        self.tasks_data = {}
        self.patterns = {}
        self.mistakes = []
        self.user_profiles = {"default": {"preferences": {}}}
        self.adaptive_delay = 0.3
        self.intelligence_level = 1

    def save_data(self):
        """Salva dados de aprendizado"""
        try:
            data = {
                "tasks": self.tasks_data,
                "patterns": self.patterns,
                "mistakes": self.mistakes,
                "user_profiles": self.user_profiles,
                "adaptive_delay": self.adaptive_delay,
                "intelligence_level": self.intelligence_level,
                "last_save": datetime.datetime.now().isoformat()
            }
            with open(LEARNING_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            log("💾 Dados de aprendizado salvos", "SUCCESS")
            return True
        except Exception as e:
            log(f"❌ Erro ao salvar aprendizado: {e}", "ERROR")
            return False

    def _analyze_intelligence(self):
        """Analisa e ajusta nível de inteligência"""
        if not self.tasks_data:
            self.intelligence_level = 1
            return
        total_executions = sum(task.get("executions", 0) for task in self.tasks_data.values())
        total_successes = sum(task.get("successes", 0) for task in self.tasks_data.values())
        if total_executions > 0:
            success_rate = total_successes / total_executions
            if success_rate > 0.9 and total_executions > 20:
                self.intelligence_level = min(5, self.intelligence_level + 0.1)
            elif success_rate < 0.6:
                self.intelligence_level = max(1, self.intelligence_level - 0.1)
            self.adaptive_delay = max(0.1, min(1.0, 0.5 / (self.intelligence_level * 0.5)))

    def analyze_task(self, task_name, actions):
        """Analisa uma tarefa para aprendizado avançado"""
        if not actions:
            log(f"⚠ Tarefa '{task_name}' sem ações para análise", "WARNING")
            return
        if task_name not in self.tasks_data:
            self.tasks_data[task_name] = {
                "executions": 0,
                "successes": 0,
                "failures": 0,
                "total_time": 0,
                "average_time": 0,
                "last_executed": "",
                "created": datetime.datetime.now().isoformat(),
                "common_errors": [],
                "optimizations": [],
                "action_types": {},
                "complexity_score": 0,
                "confidence": 0.5
            }
        task_info = self.tasks_data[task_name]
        task_info["executions"] += 1
        task_info["last_executed"] = datetime.datetime.now().isoformat()
        action_counts = {}
        for action in actions:
            action_type = action["type"]
            action_counts[action_type] = action_counts.get(action_type, 0) + 1
        task_info["action_types"] = action_counts
        task_info["complexity_score"] = len(actions) * 0.1 + len(action_counts) * 0.3
        self._analyze_patterns(task_name, actions)
        optimizations = self._find_optimizations(task_name, actions)
        if optimizations:
            for opt in optimizations:
                if opt not in task_info["optimizations"]:
                    task_info["optimizations"].append(opt)
            log(f"💡 Sugestão para '{task_name}': {opt}", "INFO")
        self._calculate_confidence(task_name)
        self._analyze_intelligence()
        log(f"📊 Tarefa '{task_name}' analisada: {len(actions)} ações, complexidade: {task_info['complexity_score']:.2f}", "INFO")
        self.save_data()

    def _analyze_patterns(self, task_name, actions):
        """Analisa padrões na tarefa"""
        click_positions = []
        key_sequences = []
        move_paths = []
        for i, action in enumerate(actions):
            if action["type"] == "click":
                click_positions.append((action["x"], action["y"]))
            elif action["type"] == "key_press":
                key_sequences.append(action["key"])
            elif action["type"] == "move":
                move_paths.append((action["x"], action["y"]))
        if task_name not in self.patterns:
            self.patterns[task_name] = {}
        self.patterns[task_name]["click_clusters"] = self._cluster_positions(click_positions)
        self.patterns[task_name]["key_patterns"] = self._analyze_key_patterns(key_sequences)
        self.patterns[task_name]["move_patterns"] = self._analyze_move_patterns(move_paths)

    def _cluster_positions(self, positions, threshold=15):
        """Agrupa posições próximas do mouse"""
        if not positions:
            return []
        clusters = []
        for pos in positions:
            added = False
            for cluster in clusters:
                if len(cluster["points"]) > 0:
                    center = np.mean(cluster["points"], axis=0)
                    dist = np.sqrt((pos[0] - center[0]) ** 2 + (pos[1] - center[1]) ** 2)
                    if dist < threshold:
                        cluster["points"].append(pos)
                        cluster["count"] += 1
                        cluster["center"] = np.mean(cluster["points"], axis=0).tolist()
                        added = True
                        break
            if not added:
                clusters.append({
                    "points": [pos],
                    "count": 1,
                    "center": list(pos)
                })
        return clusters

    def _analyze_key_patterns(self, keys):
        """Analisa padrões de teclas"""
        if not keys:
            return {}
        patterns = {
            "common_keys": Counter(keys).most_common(5),
            "sequences": [],
            "shortcuts": []
        }
        for i in range(len(keys) - 1):
            seq = f"{keys[i]}+{keys[i + 1]}"
            patterns["sequences"].append(seq)
        for key in keys:
            if any(mod in key.lower() for mod in ["ctrl", "alt", "shift", "cmd"]):
                patterns["shortcuts"].append(key)
        return patterns

    def _analyze_move_patterns(self, positions):
        """Analisa padrões de movimento"""
        if len(positions) < 2:
            return {"total_distance": 0, "segments": []}
        total_distance = 0
        segments = []
        for i in range(len(positions) - 1):
            start = positions[i]
            end = positions[i + 1]
            distance = np.sqrt((end[0] - start[0]) ** 2 + (end[1] - start[1]) ** 2)
            total_distance += distance
            if distance > 10:
                segments.append({
                    "from": start,
                    "to": end,
                    "distance": distance,
                    "direction": self._calculate_direction(start, end)
                })
        return {
            "total_distance": total_distance,
            "average_distance": total_distance / max(1, len(segments)),
            "segments": segments[:10]
        }

    def _calculate_direction(self, start, end):
        """Calcula direção do movimento"""
        dx = end[0] - start[0]
        dy = end[1] - start[1]
        if abs(dx) > abs(dy):
            return "horizontal"
        else:
            return "vertical"

    def _find_optimizations(self, task_name, actions):
        """Encontra otimizações possíveis"""
        optimizations = []
        click_times = []
        for i, action in enumerate(actions):
            if action["type"] == "click":
                click_times.append((i, action["timestamp"]))
        for j in range(len(click_times) - 1):
            i1, t1 = click_times[j]
            i2, t2 = click_times[j + 1]
            if t2 - t1 < 0.1:
                optimizations.append(f"Cliques rápidos em sequência (ações {i1} e {i2})")
        for i in range(len(actions) - 2):
            if (actions[i]["type"] == "move" and actions[i + 1]["type"] == "click" and actions[i + 2]["type"] == "move"):
                optimizations.append(f"Movimento desnecessário após clique (ação {i + 2})")
        key_counts = {}
        for action in actions:
            if action["type"] == "key_press":
                key = action["key"]
                key_counts[key] = key_counts.get(key, 0) + 1
        for key, count in key_counts.items():
            if count > 5 and len(key) == 1:
                optimizations.append(f"Tecla '{key}' pressionada {count} vezes - considere otimizar")
        return list(set(optimizations))[:3]

    def _calculate_confidence(self, task_name):
        """Calcula confiança na tarefa"""
        if task_name not in self.tasks_data:
            return 0.5
        task_info = self.tasks_data[task_name]
        if task_info["executions"] == 0:
            task_info["confidence"] = 0.5
            return
        success_rate = task_info["successes"] / task_info["executions"]
        execution_count = min(task_info["executions"], 10) / 10
        confidence = (success_rate * 0.7 + execution_count * 0.3)
        task_info["confidence"] = min(0.99, max(0.1, confidence))

    def record_success(self, task_name, execution_time=None):
        """Registra execução bem-sucedida"""
        if task_name in self.tasks_data:
            task_info = self.tasks_data[task_name]
            task_info["successes"] += 1
            if execution_time:
                task_info["total_time"] += execution_time
                task_info["average_time"] = task_info["total_time"] / task_info["executions"]
            task_info["confidence"] = min(0.99, task_info["confidence"] + 0.05)
            success_rate = task_info["successes"] / task_info["executions"]
            if success_rate > 0.8:
                self.adaptive_delay = max(0.1, self.adaptive_delay * 0.95)
            self._analyze_intelligence()
            self.save_data()
            log(f"✅ Sucesso registrado para '{task_name}' (taxa: {success_rate:.1%})", "SUCCESS")

    def record_mistake(self, task_name, error, context=None):
        """Registra erro para aprendizado"""
        mistake = {
            "task": task_name,
            "error": error,
            "context": context,
            "timestamp": datetime.datetime.now().isoformat(),
            "resolved": False,
            "occurrences": 1
        }
        for existing in self.mistakes:
            if (existing["task"] == task_name and existing["error"] == error and not existing["resolved"]):
                existing["occurrences"] += 1
                existing["last_occurrence"] = datetime.datetime.now().isoformat()
                log(f"⚠ Erro repetido em '{task_name}': {error} ({existing['occurrences']}x)", "WARNING")
                self.save_data()
                return
        self.mistakes.append(mistake)
        if task_name in self.tasks_data:
            if error not in self.tasks_data[task_name]["common_errors"]:
                self.tasks_data[task_name]["common_errors"].append(error)
        if task_name in self.tasks_data:
            self.tasks_data[task_name]["confidence"] = max(0.1, self.tasks_data[task_name]["confidence"] - 0.1)
        self.adaptive_delay = min(1.0, self.adaptive_delay * 1.1)
        log(f"❌ Erro registrado em '{task_name}': {error}", "ERROR")
        self.save_data()

    def get_task_stats(self, task_name):
        """Retorna estatísticas detalhadas da tarefa"""
        if task_name in self.tasks_data:
            stats = self.tasks_data[task_name].copy()
            if task_name in self.patterns:
                stats["patterns"] = self.patterns[task_name]
            stats["suggestions"] = self.get_suggestions(task_name)
            return stats
        return None

    def get_suggestions(self, task_name):
        """Retorna sugestões inteligentes"""
        suggestions = []
        if task_name not in self.tasks_data:
            return suggestions
        task_info = self.tasks_data[task_name]
        if task_info["confidence"] < 0.4:
            suggestions.append("Esta tarefa tem baixa confiança. Considere regravá-la.")
        if task_info.get("complexity_score", 0) > 5:
            suggestions.append("Tarefa complexa. Pode ser dividida em subtarefas?")
        if len(task_info.get("common_errors", [])) > 2:
            suggestions.append("Múltiplos erros detectados. Verifique os passos.")
        if task_info.get("average_time", 0) > 30:
            suggestions.append("Tarefa demorada. Procure otimizar os passos.")
        return suggestions

    def get_intelligence_report(self):
        """Retorna relatório de inteligência"""
        total_tasks = len(self.tasks_data)
        total_executions = sum(t.get("executions", 0) for t in self.tasks_data.values())
        total_successes = sum(t.get("successes", 0) for t in self.tasks_data.values())
        if total_executions > 0:
            success_rate = total_successes / total_executions
        else:
            success_rate = 0
        return {
            "intelligence_level": round(self.intelligence_level, 1),
            "total_tasks": total_tasks,
            "total_executions": total_executions,
            "success_rate": success_rate,
            "adaptive_delay": round(self.adaptive_delay, 2),
            "unresolved_mistakes": len([m for m in self.mistakes if not m["resolved"]]),
            "learning_progress": min(100, total_executions * 2)
        }


# SISTEMA DE VOZ AVANÇADO


class VoiceSystem:
    def __init__(self):
        self.recognizer = None
        self.engine = None
        self.listening = False
        self.setup_complete = False
        self.wake_word_detected = False
        self.last_command = ""
        self.command_history = []
        self.activation_time = time.time()
        self.command_cooldown = 1.5
        self.sensitivity = 0.8
        self.voice_profile = {}
        self.microphone_device_index = None
        self.load_voice_profile()
        self._setup_fallback()

    def _setup_fallback(self):
        """Configuração inicial segura"""
        try:
            self.engine = pyttsx3.init()
            voices = self.engine.getProperty('voices')
            for voice in voices:
                voice_lower = voice.name.lower()
                if 'portuguese' in voice_lower or 'brazil' in voice_lower:
                    self.engine.setProperty('voice', voice.id)
                    break
            self.engine.setProperty('rate', 170)
            self.engine.setProperty('volume', 0.9)
            self.recognizer = sr.Recognizer()
            self.recognizer.energy_threshold = 4000
            self.recognizer.dynamic_energy_threshold = False
            self.recognizer.pause_threshold = 1.0
            log("✅ Sistema de voz inicializado em modo seguro", "SUCCESS")
            self.setup_complete = True
        except Exception as e:
            log(f"⚠ Configuração inicial básica: {e}", "WARNING")
            self.setup_complete = False

    def load_voice_profile(self):
        """Carrega perfil de voz personalizado"""
        self.voice_profile = {
            "wake_words": ["clau", "cláudio", "claudio", "assistente", "oi clau"],
            "response_style": "friendly",
            "speech_speed": 170,
            "speech_volume": 0.9,
            "energy_threshold": 4000
        }
        try:
            if os.path.exists(VOICE_PROFILES_FILE):
                with open(VOICE_PROFILES_FILE, "r", encoding="utf-8") as f:
                    profiles = json.load(f)
                if "default" in profiles:
                    self.voice_profile.update(profiles["default"])
        except:
            pass

    def save_voice_profile(self):
        """Salva perfil de voz"""
        try:
            profiles = {"default": self.voice_profile}
            with open(VOICE_PROFILES_FILE, "w", encoding="utf-8") as f:
                json.dump(profiles, f, indent=2, ensure_ascii=False)
        except:
            pass

    def find_microphone(self):
        """Encontra o melhor microfone disponível"""
        try:
            mic_list = sr.Microphone.list_microphone_names()
            log(f"🎤 Microfones encontrados: {len(mic_list)}", "INFO")
            preferred_keywords = ['default', 'microfone', 'microphone', 'input', 'entrada', 'realtek', 'logitech', 'usb']
            for idx, name in enumerate(mic_list):
                name_lower = name.lower()
                for keyword in preferred_keywords:
                    if keyword in name_lower:
                        self.microphone_device_index = idx
                        log(f"✅ Microfone selecionado: {name} (índice: {idx})", "SUCCESS")
                        return True
            if mic_list:
                self.microphone_device_index = 0
                log(f"✅ Usando microfone: {mic_list[0]}", "SUCCESS")
                return True
        except Exception as e:
            log(f"⚠ Não foi possível listar microfones: {e}", "WARNING")
            return False

    def setup(self):
        """Configura sistema de voz"""
        try:
            if not self.setup_complete:
                if not self.find_microphone():
                    log("⚠ Usando microfone padrão do sistema", "WARNING")
                if self.recognizer:
                    self.recognizer.energy_threshold = self.voice_profile.get("energy_threshold", 4000)
                    self.recognizer.dynamic_energy_threshold = True
                self.setup_complete = True
                log("✅ Sistema de voz configurado", "SUCCESS")
                return True
            return True
        except Exception as e:
            log(f"❌ Erro na configuração de voz: {e}", "ERROR")
            return False

    def speak(self, text, emotion="neutral"):
        """Faz a Clau falar - versão robusta"""
        if not text or not self.engine:
            return
        def _speak():
            try:
                emotions = {
                    "happy": ["Ótimo! ", "Perfeito! ", "Excelente! "],
                    "sad": ["Poxa... ", "Que pena... ", "Desculpe... "],
                    "excited": ["Incrível! ", "Fantástico! ", "Maravilha! "],
                    "error": ["Ops! ", "Atenção! ", "Cuidado! "],
                    "confirm": ["Certo! ", "Entendido! ", "Confirmado! "],
                    "neutral": [""]
                }
                import random
                prefix = random.choice(emotions.get(emotion, [""]))
                full_text = prefix + text
                log(f"🗣 Clau: {full_text}", "VOICE")
                self.engine.say(full_text)
                self.engine.runAndWait()
            except Exception as e:
                log(f"⚠ Erro na fala: {e}", "WARNING")
                log(f"💬 (Fala): {full_text}", "VOICE")
        threading.Thread(target=_speak, daemon=True).start()

    def listen(self, timeout=3, phrase_time_limit=4):
        """Escuta com tratamento robusto de erros"""
        if not self.recognizer:
            return None
        try:
            if self.microphone_device_index is not None:
                with sr.Microphone(device_index=self.microphone_device_index) as source:
                    return self._listen_from_source(source, timeout, phrase_time_limit)
            else:
                with sr.Microphone() as source:
                    return self._listen_from_source(source, timeout, phrase_time_limit)
        except sr.WaitTimeoutError:
            return None
        except Exception as e:
            log(f"⚠ Erro na escuta: {e}", "WARNING")
            return None

    def _listen_from_source(self, source, timeout, phrase_time_limit):
        """Processa áudio de uma fonte específica"""
        try:
            self.recognizer.adjust_for_ambient_noise(source, duration=0.8)
            log("👂 Ouvindo...", "INFO")
            audio = self.recognizer.listen(source, timeout=timeout, phrase_time_limit=phrase_time_limit)
            text = self.recognizer.recognize_google(audio, language='pt-BR')
            text = text.lower().strip()
            if text:
                log(f"🎤 Reconhecido: '{text}'", "VOICE")
                return text
        except sr.UnknownValueError:
            pass
        except sr.RequestError as e:
            log(f"⚠ Erro no serviço de reconhecimento: {e}", "WARNING")
        except Exception as e:
            log(f"⚠ Erro no processamento de áudio: {e}", "WARNING")
        return None

    def continuous_listen(self):
        """Loop contínuo de escuta"""
        log("🎯 Modo escuta ativado - Diga 'Clau' para ativar", "SYSTEM")
        while self.listening:
            try:
                audio_text = self.listen(timeout=2, phrase_time_limit=3)
                if audio_text:
                    processed = self.process_command(audio_text)
                    if processed:
                        self.last_command = audio_text
                        self.command_history.append({
                            "command": audio_text,
                            "timestamp": datetime.datetime.now().isoformat(),
                            "processed": True
                        })
                    time.sleep(0.3)
            except Exception as e:
                log(f"⚠ Erro no loop de escuta: {e}", "ERROR")
                time.sleep(1)

    def process_command(self, command_text):
        """Processa comandos de voz de forma inteligente"""
        if not command_text:
            return False
        command = command_text.lower().strip()
        current_time = time.time()
        if current_time - self.activation_time < self.command_cooldown:
            return False
        self.activation_time = current_time
        log(f"🔍 Analisando comando: '{command}'", "INFO")
        wake_words = self.voice_profile.get("wake_words", ["clau", "assistente"])
        has_wake_word = any(wake_word in command for wake_word in wake_words)
        if has_wake_word:
            self.wake_word_detected = True
            log("✅ Palavra de ativação detectada", "SUCCESS")
            for wake_word in wake_words:
                command = command.replace(wake_word, "")
            command = command.strip()
            if not command:
                responses = ["Sim? Estou aqui! Como posso ajudar?", "Olá! Pronta para auxiliar.", "Oi! Clau à disposição.", "Estou ouvindo. O que precisa?"]
                import random
                self.speak(random.choice(responses), "happy")
                return True
        if self.wake_word_detected or self._is_direct_command(command):
            return self._execute_command(command)
        return False

    def _is_direct_command(self, command):
        """Verifica se é um comando direto (sem palavra de ativação)"""
        direct_keywords = ['execute', 'faça', 'rode', 'inicia', 'pare', 'pausa', 'continue', 'gravar', 'aprender', 'tarefa', 'parar']
        return any(keyword in command for keyword in direct_keywords)

    def _execute_command(self, command):
        """Executa o comando específico"""
        execution_keywords = ['execute', 'faça', 'rode', 'inicia', 'comece', 'iniciar', 'rodar']
        for keyword in execution_keywords:
            if keyword in command:
                task_name = self._extract_task_name(command, keyword)
                if task_name:
                    self.speak(f"Executando tarefa: {task_name}", "excited")
                    tasks = load_tasks()
                    task_found = None
                    for task in tasks.keys():
                        task_lower = task.lower()
                        name_lower = task_name.lower()
                        if (name_lower in task_lower or task_lower in name_lower or self._similarity(name_lower, task_lower) > 0.6):
                            task_found = task
                            break
                    if task_found:
                        threading.Thread(target=execute_task, args=(task_found, True), daemon=True).start()
                        return True
                    else:
                        self.speak(f"Não encontrei a tarefa '{task_name}'. Ensine-me primeiro.", "sad")
                        return True
        if any(word in command for word in ['pare', 'parar', 'interrompa', 'stop', 'parada']):
            self.speak("Parando a execução atual.", "confirm")
            stop_execution()
            return True
        if any(word in command for word in ['pausa', 'pause', 'pausar', 'espera']):
            self.speak("Pausando a execução.", "confirm")
            toggle_pause()
            return True
        if any(word in command for word in ['continue', 'continuar', 'retome', 'volte', 'retomar']):
            self.speak("Continuando a execução.", "confirm")
            toggle_pause()
            return True
        learn_keywords = ['aprenda', 'grave', 'gravar', 'ensine', 'ensinar', 'crie', 'criar']
        for keyword in learn_keywords:
            if keyword in command:
                task_name = self._extract_task_name(command, keyword)
                if task_name:
                    self.speak(f"Vou aprender a tarefa '{task_name}'. Por favor, digite o nome e clique em 'Ensinar Nova Tarefa'.", "excited")
                    if 'task_name_entry' in globals() and app:
                        app.after(0, lambda name=task_name: task_name_entry.delete(0, "end"))
                        app.after(0, lambda name=task_name: task_name_entry.insert(0, name))
                        app.after(0, lambda: task_name_entry.focus())
                    return True
        if any(word in command for word in ['tarefas', 'lista', 'o que você sabe', 'mostre', 'mostrar']):
            tasks = load_tasks()
            if tasks:
                count = len(tasks)
                if count <= 5:
                    task_list = ", ".join(tasks.keys())
                    self.speak(f"Sei fazer {count} tarefas: {task_list}", "happy")
                else:
                    sample = ", ".join(list(tasks.keys())[:3])
                    self.speak(f"Sei fazer {count} tarefas. Por exemplo: {sample}", "happy")
            else:
                self.speak("Ainda não aprendi nenhuma tarefa. Você pode me ensinar!", "sad")
            return True
        if any(word in command for word in ['ajuda', 'ajude', 'comandos', 'como usar', 'o que você faz']):
            help_text = "Posso executar tarefas salvas, aprender novas tarefas, pausar e continuar execuções. Diga 'Clau, execute' seguido do nome da tarefa para executar. Diga 'Clau, aprenda' seguido do nome para me ensinar uma nova tarefa. Diga 'Clau, pare' para interromper ou 'Clau, pause' para pausar."
            self.speak(help_text, "happy")
            return True
        if self.wake_word_detected and command:
            responses = [f"Desculpe, não entendi '{command}'. Pode repetir?", f"Não reconheci o comando '{command}'. Tente novamente.", f"Comando '{command}' não reconhecido. Diga 'ajuda' para ver opções."]
            import random
            self.speak(random.choice(responses), "sad")
            return False

    def _extract_task_name(self, command, keyword):
        """Extrai nome da tarefa do comando"""
        command = command.replace(keyword, "")
        stop_words = ['a', 'o', 'as', 'os', 'de', 'do', 'da', 'em', 'por', 'para', 'tarefa', 'chamada', 'nome', 'com', 'uma', 'um']
        words = [w for w in command.split() if w.lower() not in stop_words and len(w) > 2]
        if words:
            name = ' '.join(words[:4])
            return name.title()
        return None

    def _similarity(self, s1, s2):
        """Calcula similaridade entre strings"""
        if not s1 or not s2:
            return 0
        set1, set2 = set(s1.split()), set(s2.split())
        intersection = len(set1.intersection(set2))
        union = len(set1.union(set2))
        if union == 0:
            return 0
        return intersection / union

    def start_listening(self):
        """Inicia escuta ativa"""
        if not self.setup_complete:
            if not self.setup():
                self.speak("Não consegui configurar o sistema de voz. Verifique o microfone.", "error")
                return False
        if not self.listening:
            self.listening = True
            self.wake_word_detected = False
            threading.Thread(target=self.continuous_listen, daemon=True).start()
            greetings = ["Olá! Eu sou a Clau. Diga 'Clau' seguido do comando.", "Ativada e pronta! Chame por 'Clau' quando precisar.", "Estou aqui! Para começar, diga 'Clau' e o que deseja."]
            import random
            self.speak(random.choice(greetings), "happy")
            log("✅ Sistema de voz ativado - Aguardando comandos", "SUCCESS")
            return True
        return True

    def stop_listening(self):
        """Para a escuta"""
        if self.listening:
            self.listening = False
            self.speak("Sistema de voz desativado. Ative-me novamente quando precisar.", "confirm")
            log("🔇 Sistema de voz desativado", "INFO")

    def get_audio_devices(self):
        """Lista dispositivos de áudio disponíveis"""
        try:
            p = pyaudio.PyAudio()
            devices = []
            for i in range(p.get_device_count()):
                device_info = p.get_device_info_by_index(i)
                if device_info['maxInputChannels'] > 0:
                    devices.append({
                        'index': i,
                        'name': device_info['name'],
                        'channels': device_info['maxInputChannels'],
                        'sample_rate': device_info['defaultSampleRate']
                    })
            p.terminate()
            return devices
        except:
            return []


# FUNÇÕES DE APRENDIZADO E ENSINO 


def start_teaching():
    """Inicia modo de ensino com feedback visual"""
    global recording, current_task_name
    task_name = task_name_entry.get().strip() if 'task_name_entry' in globals() else ""
    if not task_name:
        voice_system.speak("Por favor, dê um nome para esta tarefa.", "error")
        log("⚠ Nome da tarefa não informado", "WARNING")
        return
    tasks = load_tasks()
    if task_name in tasks:
        response = messagebox.askyesno("Tarefa Existente", f"A tarefa '{task_name}' já existe.\n\nDeseja sobrescrever?\n\nA tarefa atual tem {len(tasks[task_name].get('actions', []))} ações.")
        if not response:
            return
    current_task_name = task_name
    voice_system.speak(f"Iniciando aprendizado da tarefa '{task_name}'. Faça a tarefa normalmente que eu vou aprender.", "excited")
    if 'teaching_button' in globals():
        teaching_button.configure(state="disabled", text="🎥 Gravando...")
    if 'stop_teaching_button' in globals():
        stop_teaching_button.configure(state="normal")
    if 'recording_indicator' in globals():
        recording_indicator.configure(text="🔴 GRAVANDO", text_color="#ef4444")
    start_recording()
    log(f"🎥 Aprendendo tarefa: '{task_name}'", "INFO")

def stop_teaching():
    """Para modo de ensino e salva tarefa"""
    global recording
    if not recording:
        voice_system.speak("Não estou gravando no momento.", "error")
        return
    stop_recording()
    if actions and current_task_name:
        learning_system.analyze_task(current_task_name, actions)
        stats = learning_system.get_task_stats(current_task_name)
        if stats and stats.get("suggestions"):
            suggestions_text = "\n".join(stats["suggestions"])
            log(f"💡 Sugestões para '{current_task_name}':\n{suggestions_text}", "INFO")
        action_count = len(actions)
        voice_system.speak(f"Tarefa '{current_task_name}' aprendida com sucesso! Capturei {action_count} ações.", "happy")
        log(f"✅ Tarefa '{current_task_name}' salva com {action_count} ações", "SUCCESS")
    if 'teaching_button' in globals():
        teaching_button.configure(state="normal", text="▶ Ensinar Nova Tarefa")
    if 'stop_teaching_button' in globals():
        stop_teaching_button.configure(state="disabled")
    if 'recording_indicator' in globals():
        recording_indicator.configure(text="Pronto", text_color="#10b981")
    update_task_list()

def name_learned_activity():
    """Permite nomear atividade aprendida"""
    if not actions:
        voice_system.speak("Primeiro aprenda uma tarefa antes de nomeá-la.", "error")
        return
    dialog = ctk.CTkToplevel(app)
    dialog.title("Nomear Atividade")
    dialog.geometry("400x200")
    dialog.transient(app)
    dialog.grab_set()
    ctk.CTkLabel(dialog, text="Digite um nome para a atividade aprendida:", font=ctk.CTkFont(size=14)).pack(pady=20)
    name_entry = ctk.CTkEntry(dialog, width=300, height=40, font=ctk.CTkFont(size=14))
    name_entry.pack(pady=10)
    name_entry.focus()
    def save_name():
        name = name_entry.get().strip()
        if name:
            if 'task_name_entry' in globals():
                task_name_entry.delete(0, "end")
                task_name_entry.insert(0, name)
            voice_system.speak(f"Atividade nomeada como '{name}'.", "confirm")
            dialog.destroy()
    ctk.CTkButton(dialog, text="Salvar", command=save_name, width=100, height=40).pack(pady=20)
    dialog.bind('<Return>', lambda e: save_name())


# FUNÇÕES DE CONTROLE (PAUSA/CONTINUAR) 


def toggle_pause():
    """Pausa ou continua execução"""
    global paused
    if not playing:
        voice_system.speak("Não há execução em andamento para pausar.", "error")
        return
    paused = not paused
    if paused:
        pause_event.clear()
        voice_system.speak("Execução pausada. Diga 'Clau, continue' para retomar.", "confirm")
        if 'pause_button' in globals():
            pause_button.configure(text="▶ Continuar", fg_color="#059669")
        log("⏸ Execução pausada", "INFO")
    else:
        pause_event.set()
        voice_system.speak("Continuando a execução.", "confirm")
        if 'pause_button' in globals():
            pause_button.configure(text="⏸ Pausar", fg_color="#d97706")
        log("▶ Execução continuada", "INFO")

def wait_if_paused():
    """Espera se a execução estiver pausada"""
    if paused:
        log("⏸ Aguardando continuar...", "INFO")
        pause_event.wait()

# CAPTURA DE AÇÕES 


def on_move(x, y):
    """Captura movimentos do mouse"""
    global last_mouse_position, last_action_time
    if recording:
        current_time = time.time()
        time_since_last = current_time - last_action_time
        if last_mouse_position:
            distance = ((x - last_mouse_position[0]) ** 2 + (y - last_mouse_position[1]) ** 2) ** 0.5
            if time_since_last > 0.3 or distance > 50:
                action = {
                    "type": "move",
                    "x": x,
                    "y": y,
                    "timestamp": current_time,
                    "distance_from_last": distance
                }
                actions.append(action)
                last_action_time = current_time
        last_mouse_position = (x, y)

def on_click(x, y, button, pressed):
    """Captura cliques"""
    global last_action_time
    if recording and pressed:
        last_action_time = time.time()
        action = {
            "type": "click",
            "x": x,
            "y": y,
            "button": str(button).split('.')[-1],
            "pressed": pressed,
            "timestamp": time.time()
        }
        actions.append(action)
        log(f"🖱 Clique {button} em ({x},{y})", "INFO")

def on_scroll(x, y, dx, dy):
    """Captura scroll"""
    global last_action_time
    if recording:
        last_action_time = time.time()
        action = {
            "type": "scroll",
            "x": x,
            "y": y,
            "dx": dx,
            "dy": dy,
            "timestamp": time.time(),
            "intensity": abs(dy)
        }
        actions.append(action)
        direction = "cima" if dy > 0 else "baixo"
        log(f"🖱 Scroll para {direction} em ({x},{y})", "INFO")

def on_press(key):
    """Captura teclas"""
    global last_action_time
    if recording:
        last_action_time = time.time()
        try:
            key_str = key.char
        except AttributeError:
            key_str = str(key).replace("Key.", "")
        action = {
            "type": "key_press",
            "key": key_str,
            "timestamp": time.time()
        }
        actions.append(action)
        log(f"⌨ Tecla: {key_str}", "INFO")

def start_recording():
    """Inicia gravação de ações"""
    global recording, actions, mouse_listener, keyboard_listener
    actions.clear()
    mouse_listener = mouse.Listener(on_move=on_move, on_click=on_click, on_scroll=on_scroll)
    keyboard_listener = keyboard.Listener(on_press=on_press)
    mouse_listener.start()
    keyboard_listener.start()
    recording = True
    log("🎥 Gravação iniciada", "SUCCESS")

def stop_recording():
    """Para gravação e processa ações"""
    global recording, mouse_listener, keyboard_listener
    if not recording:
        return
    recording = False
    if mouse_listener:
        mouse_listener.stop()
    if keyboard_listener:
        keyboard_listener.stop()
    if actions:
        filtered_actions = []
        last_time = 0
        for action in actions:
            current_time = action["timestamp"]
            if current_time - last_time > 0.05:
                filtered_actions.append(action)
                last_time = current_time
        actions[:] = filtered_actions
        if actions and current_task_name:
            tasks = load_tasks()
            tasks[current_task_name] = {
                "actions": actions,
                "created": datetime.datetime.now().isoformat(),
                "updated": datetime.datetime.now().isoformat(),
                "action_count": len(actions),
                "metadata": {
                    "screen_size": pyautogui.size(),
                    "recorded_at": datetime.datetime.now().isoformat()
                }
            }
            if save_tasks(tasks):
                log(f"✅ Tarefa '{current_task_name}' salva com {len(actions)} ações", "SUCCESS")
            else:
                log(f"❌ Falha ao salvar tarefa '{current_task_name}'", "ERROR")
    else:
        log("⚠ Nenhuma ação foi gravada", "WARNING")


# EXECUÇÃO DE TAREFAS 


def execute_task_voice(task_name):
    """Executa tarefa por comando de voz"""
    tasks = load_tasks()
    task_lower = task_name.lower()
    matching_tasks = []
    for task in tasks.keys():
        task_l = task.lower()
        if (task_lower in task_l or task_l in task_lower or voice_system._similarity(task_lower, task_l) > 0.5):
            matching_tasks.append((task, voice_system._similarity(task_lower, task_l)))
    if matching_tasks:
        matching_tasks.sort(key=lambda x: x[1], reverse=True)
        best_match = matching_tasks[0][0]
        voice_system.speak(f"Executando tarefa: {best_match}", "excited")
        threading.Thread(target=execute_task, args=(best_match, True), daemon=True).start()
        return True
    else:
        voice_system.speak(f"Não encontrei a tarefa '{task_name}'.", "sad")
        return False

def execute_task(task_name, show_log=True):
    """Executa uma tarefa com controle e monitoramento"""
    global playing, stop_execution_flag, paused
    if playing:
        voice_system.speak("Já há uma execução em andamento.", "error")
        return
    tasks = load_tasks()
    if task_name not in tasks:
        voice_system.speak(f"Tarefa '{task_name}' não encontrada.", "error")
        return
    playing = True
    stop_execution_flag = False
    paused = False
    pause_event.set()
    task_actions = tasks[task_name].get("actions", [])
    if not task_actions:
        voice_system.speak(f"A tarefa '{task_name}' não tem ações.", "error")
        playing = False
        return
    start_time = time.time()
    voice_system.speak(f"Iniciando execução de '{task_name}'. São {len(task_actions)} passos.", "excited")
    log(f"⚡ Iniciando execução: '{task_name}' ({len(task_actions)} ações)", "INFO")
    try:
        for i, action in enumerate(task_actions):
            if stop_execution_flag:
                log("🛑 Execução interrompida pelo usuário", "WARNING")
                break
            wait_if_paused()
            action_type = action.get("type", "")
            if action_type == "move":
                x, y = action.get("x", 0), action.get("y", 0)
                pyautogui.moveTo(x, y, duration=0.2)
            elif action_type == "click":
                x, y = action.get("x", 0), action.get("y", 0)
                button = action.get("button", "left")
                pyautogui.moveTo(x, y, duration=0.2)
                if button == "left":
                    pyautogui.click()
                elif button == "right":
                    pyautogui.rightClick()
                elif button == "middle":
                    pyautogui.middleClick()
            elif action_type == "scroll":
                dy = action.get("dy", 0)
                pyautogui.scroll(dy * 40)
            elif action_type == "key_press":
                key = action.get("key", "")
                special_keys = {'enter': 'enter', 'tab': 'tab', 'space': 'space', 'esc': 'esc', 'backspace': 'backspace', 'delete': 'delete'}
                if key in special_keys:
                    pyautogui.press(special_keys[key])
                elif '+' in key:
                    keys = key.split('+')
                    pyautogui.hotkey(*keys)
                elif len(key) == 1:
                    pyautogui.press(key)
                else:
                    pyautogui.press(key)
            delay = learning_system.adaptive_delay
            time.sleep(delay)
            if show_log and (i + 1) % max(1, len(task_actions) // 10) == 0:
                progress = (i + 1) / len(task_actions) * 100
                if 'progress_bar' in globals():
                    progress_bar.set(progress / 100)
                if 'progress_label' in globals():
                    progress_label.configure(text=f"{progress:.1f}%")
            if len(task_actions) > 20 and i == len(task_actions) // 2:
                voice_system.speak("Estou na metade da tarefa.", "confirm")
        if not stop_execution_flag:
            execution_time = time.time() - start_time
            learning_system.record_success(task_name, execution_time)
            voice_system.speak(f"Tarefa '{task_name}' concluída com sucesso em {execution_time:.1f} segundos!", "happy")
            log(f"✅ Tarefa '{task_name}' concluída em {execution_time:.1f}s", "SUCCESS")
            stats = learning_system.get_task_stats(task_name)
            if stats:
                confidence = stats.get("confidence", 0.5)
                log(f"📊 Confiança atual: {confidence:.1%}", "INFO")
    except Exception as e:
        learning_system.record_mistake(task_name, str(e), {"action_index": i})
        error_msg = str(e)[:100]
        voice_system.speak(f"Ocorreu um erro durante a execução: {error_msg}", "error")
        log(f"❌ Erro na execução: {e}", "ERROR")
    finally:
        playing = False
        stop_execution_flag = False
        if 'progress_bar' in globals():
            progress_bar.set(0)
        if 'progress_label' in globals():
            progress_label.configure(text="0%")
        if 'pause_button' in globals() and paused:
            pause_button.configure(text="⏸ Pausar", fg_color="#d97706")
        paused = False
        pause_event.set()

def stop_execution():
    """Para execução atual"""
    global stop_execution_flag
    if playing:
        stop_execution_flag = True
        pause_event.set()
        voice_system.speak("Execução interrompida.", "confirm")
        log("🛑 Execução interrompida", "WARNING")
    else:
        voice_system.speak("Não há execução em andamento.", "error")


# FUNÇÕES AUXILIARES E DIAGNÓSTICO 


def toggle_voice_system():
    """Alterna sistema de voz"""
    global voice_listening
    if voice_listening:
        voice_system.stop_listening()
        voice_listening = False
        if 'voice_button' in globals():
            voice_button.configure(text="🎤 Ativar Clau", fg_color="#1e40af")
        if 'status_label' in globals():
            status_label.configure(text="🔴 Clau Desativada", text_color="#6b7280")
        if 'voice_status_indicator' in globals():
            voice_status_indicator.configure(text="🔴", text_color="#ef4444")
        log("🔇 Sistema de voz desativado", "INFO")
    else:
        if voice_system.start_listening():
            voice_listening = True
            if 'voice_button' in globals():
                voice_button.configure(text="🔴 Clau Ativa", fg_color="#dc2626")
            if 'status_label' in globals():
                status_label.configure(text="🟢 Clau Ativa - Diga 'Clau'", text_color="#10b981")
            if 'voice_status_indicator' in globals():
                voice_status_indicator.configure(text="🟢", text_color="#10b981")
        else:
            log("❌ Falha ao ativar sistema de voz", "ERROR")

def test_microphone():
    """Testa o microfone com múltiplas tentativas"""
    def perform_test():
        try:
            if 'test_status_label' in globals():
                app.after(0, lambda: test_status_label.configure(text="🎤 Testando...", text_color="#3b82f6"))
            if not voice_system.setup():
                voice_system.speak("Não consegui configurar o microfone.", "error")
                app.after(0, lambda: test_status_label.configure(text="❌ Falha na configuração", text_color="#dc2626"))
                return
            voice_system.speak("Testando o microfone. Por favor, fale agora.", "confirm")
            command = None
            for attempt in range(3):
                if attempt > 0:
                    voice_system.speak(f"Tentativa {attempt + 1} de 3.", "neutral")
                command = voice_system.listen(timeout=4, phrase_time_limit=3)
                if command:
                    break
            if command:
                voice_system.speak(f"Microfone funcionando! Ouvi: '{command}'", "happy")
                app.after(0, lambda: test_status_label.configure(text="✅ Funcionando", text_color="#059669"))
                log(f"✅ Teste de microfone OK: '{command}'", "SUCCESS")
            else:
                voice_system.speak("Não ouvi nada. Verifique o microfone e as permissões.", "error")
                app.after(0, lambda: test_status_label.configure(text="❌ Não ouvi nada", text_color="#dc2626"))
                log("❌ Teste de microfone falhou", "ERROR")
        except Exception as e:
            log(f"❌ Erro no teste de microfone: {e}", "ERROR")
            voice_system.speak("Erro durante o teste.", "error")
    threading.Thread(target=perform_test, daemon=True).start()

def show_audio_diagnostic():
    """Mostra diagnóstico detalhado de áudio"""
    diagnostic_window = ctk.CTkToplevel(app)
    diagnostic_window.title("Diagnóstico de Áudio")
    diagnostic_window.geometry("600x500")
    diagnostic_window.transient(app)
    ctk.CTkLabel(diagnostic_window, text="🔍 Diagnóstico de Áudio", font=ctk.CTkFont(size=20, weight="bold")).pack(pady=20)
    info_frame = ctk.CTkFrame(diagnostic_window)
    info_frame.pack(fill="both", expand=True, padx=20, pady=10)
    info_text = ctk.CTkTextbox(info_frame, height=300)
    info_text.pack(fill="both", expand=True, padx=10, pady=10)
    info_lines = []
    info_lines.append("=== DIAGNÓSTICO DE ÁUDIO ===\n")
    try:
        devices = voice_system.get_audio_devices()
        info_lines.append(f"🎤 Dispositivos de entrada encontrados: {len(devices)}\n")
        for device in devices:
            info_lines.append(f" • {device['name']} (Canais: {device['channels']})")
    except:
        info_lines.append("❌ Não foi possível listar dispositivos de áudio\n")
    info_lines.append("\n=== STATUS DO SISTEMA ===\n")
    info_lines.append(f"✅ Sistema de voz configurado: {voice_system.setup_complete}")
    info_lines.append(f"✅ Reconhecedor inicializado: {voice_system.recognizer is not None}")
    info_lines.append(f"✅ Sintetizador inicializado: {voice_system.engine is not None}")
    info_lines.append(f"✅ Escuta ativa: {voice_system.listening}")
    info_lines.append("\n=== SOLUÇÕES PARA PROBLEMAS COMUNS ===\n")
    info_lines.append("1. Microfone não detectado:")
    info_lines.append(" • Verifique se o microfone está conectado")
    info_lines.append(" • Verifique as permissões do sistema")
    info_lines.append(" • Tente outro dispositivo de áudio")
    info_lines.append("\n2. Clau não responde:")
    info_lines.append(" • Fale claramente e perto do microfone")
    info_lines.append(" • Diga 'Clau' antes do comando")
    info_lines.append(" • Ajuste a sensibilidade do microfone no sistema")
    info_text.insert("1.0", "\n".join(info_lines))
    info_text.configure(state="disabled")
    button_frame = ctk.CTkFrame(diagnostic_window)
    button_frame.pack(fill="x", padx=20, pady=10)
    ctk.CTkButton(button_frame, text="🔄 Testar Novamente", command=test_microphone).pack(side="left", padx=5)
    ctk.CTkButton(button_frame, text="🔧 Reconfigurar Voz", command=lambda: voice_system.setup()).pack(side="left", padx=5)
    ctk.CTkButton(button_frame, text="✖ Fechar", command=diagnostic_window.destroy).pack(side="right", padx=5)

def show_help_dialog():
    """Mostra diálogo de ajuda completo"""
    help_window = ctk.CTkToplevel(app)
    help_window.title("📚 Ajuda - Comandos da Clau")
    help_window.geometry("700x600")
    help_window.transient(app)
    tabview = ctk.CTkTabview(help_window)
    tabview.pack(fill="both", expand=True, padx=20, pady=20)
    tabview.add("Comandos de Voz")
    tabview.add("Como Ensinar")
    tabview.add("Dicas e Truques")
    voice_tab = tabview.tab("Comandos de Voz")
    voice_text = """ 🎯 COMANDOS PRINCIPAIS: ATIVAÇÃO: • "Clau" ou "Oi, Clau" EXECUTAR TAREFAS: • "Clau, execute [nome da tarefa]" • "Clau, faça [nome da tarefa]" • "Clau, rode [nome da tarefa]" CONTROLE DE EXECUÇÃO: • "Clau, pare" - Para a execução atual • "Clau, pause" - Pausa a execução • "Clau, continue" - Continua a execução APRENDIZADO: • "Clau, aprenda [nome da tarefa]" • "Clau, grave [nome da tarefa]" INFORMAÇÕES: • "Clau, quais tarefas você sabe?" • "Clau, ajuda" EXEMPLOS PRÁTICOS: • "Clau, execute cadastro de cliente" • "Clau, aprenda backup diário" • "Clau, pare a execução" """
    voice_textbox = ctk.CTkTextbox(voice_tab, wrap="word")
    voice_textbox.pack(fill="both", expand=True, padx=10, pady=10)
    voice_textbox.insert("1.0", voice_text)
    voice_textbox.configure(state="disabled")
    teach_tab = tabview.tab("Como Ensinar")
    teach_text = """ 📚 COMO ENSINAR UMA NOVA TAREFA: 1. DIGITE O NOME: • Digite um nome descritivo na caixa "Nome da Tarefa" • Exemplo: "Cadastro de Cliente" 2. CLIQUE EM "ENSINAR": • Clique no botão "Ensinar Nova Tarefa" • A Clau começará a gravar suas ações 3. EXECUTE A TAREFA: • Faça a tarefa normalmente no computador • A Clau irá capturar todos os cliques e teclas 4. FINALIZE O ENSINO: • Clique em "Parar Ensino" quando terminar • A Clau salvará a tarefa automaticamente 💡 DICAS PARA UM BOM ENSINO: • Faça a tarefa de forma consistente • Use nomes claros e descritivos • Evite pausas muito longas durante o ensino • Teste a tarefa após ensinar """
    teach_textbox = ctk.CTkTextbox(teach_tab, wrap="word")
    teach_textbox.pack(fill="both", expand=True, padx=10, pady=10)
    teach_textbox.insert("1.0", teach_text)
    teach_textbox.configure(state="disabled")
    tips_tab = tabview.tab("Dicas e Truques")
    tips_text = """ 💡 DICAS AVANÇADAS: OTIMIZAÇÃO DE TAREFAS: • Tarefas muito longas podem ser divididas • Use atalhos de teclado quando possível • A Clau aprende com cada execução COMANDOS DE VOZ: • Fale claramente e em ritmo normal • Use palavras-chave como "execute", "pare", "pause" • A Clau entende variações dos comandos SISTEMA DE APRENDIZADO: • A Clau melhora com o uso contínuo • Erros são registrados para aprendizado • Confiança aumenta com execuções bem-sucedidas SOLUÇÃO DE PROBLEMAS: • Teste o microfone regularmente • Verifique as permissões do sistema • Reinicie a Clau se necessário ⚡ ATALHOS ÚTEIS: • Ativar/desativar voz: Botão "Ativar Clau" • Testar microfone: Botão "Testar Microfone" • Ver tarefas: Lista suspensa no painel direito """
    tips_textbox = ctk.CTkTextbox(tips_tab, wrap="word")
    tips_textbox.pack(fill="both", expand=True, padx=10, pady=10)
    tips_textbox.insert("1.0", tips_text)
    tips_textbox.configure(state="disabled")

def show_learning_report():
    """Mostra relatório de aprendizado"""
    report = learning_system.get_intelligence_report()
    report_window = ctk.CTkToplevel(app)
    report_window.title("📊 Relatório de Aprendizado")
    report_window.geometry("500x400")
    report_window.transient(app)
    ctk.CTkLabel(report_window, text="📊 Relatório de Inteligência da Clau", font=ctk.CTkFont(size=18, weight="bold")).pack(pady=20)
    stats_frame = ctk.CTkFrame(report_window)
    stats_frame.pack(fill="both", expand=True, padx=20, pady=10)
    intelligence_level = report.get("intelligence_level", 1)
    level_text = f"Nível de Inteligência: {intelligence_level:.1f}/5.0"
    ctk.CTkLabel(stats_frame, text=level_text, font=ctk.CTkFont(size=16)).pack(pady=10)
    level_bar = ctk.CTkProgressBar(stats_frame, width=300, height=20)
    level_bar.pack(pady=5)
    level_bar.set(intelligence_level / 5)
    details = f""" 📈 ESTATÍSTICAS: • Tarefas aprendidas: {report.get('total_tasks', 0)} • Execuções totais: {report.get('total_executions', 0)} • Taxa de sucesso: {report.get('success_rate', 0):.1%} • Atraso adaptativo: {report.get('adaptive_delay', 0.3):.2f}s • Erros não resolvidos: {report.get('unresolved_mistakes', 0)} • Progresso de aprendizado: {report.get('learning_progress', 0)}% """
    details_label = ctk.CTkLabel(stats_frame, text=details, font=ctk.CTkFont(size=14), justify="left")
    details_label.pack(pady=20, padx=20)
    if intelligence_level >= 4:
        message = "🌟 Excelente! A Clau está muito inteligente!"
    elif intelligence_level >= 2.5:
        message = "👍 Bom progresso! Continue usando para melhorar."
    else:
        message = "💪 Vamos lá! Quanto mais você usar, mais inteligente a Clau ficará."
    ctk.CTkLabel(stats_frame, text=message, font=ctk.CTkFont(size=12), text_color="#3b82f6").pack(pady=10)
    ctk.CTkButton(report_window, text="Fechar", command=report_window.destroy).pack(pady=20)


# INICIALIZAR SISTEMAS 


learning_system = LearningSystem()
voice_system = VoiceSystem()


# INTERFACE GRÁFICA AVANÇADA 


app = ctk.CTk()
app.title("🤖 Clau - Assistente RPA Inteligente v9.0")
app.geometry("1200x900")
app.grid_columnconfigure(0, weight=1)
app.grid_rowconfigure(1, weight=1)

header = ctk.CTkFrame(app, height=140, corner_radius=20, fg_color=("#2b2b2b", "#1a1a1a"))
header.grid(row=0, column=0, padx=25, pady=(20, 10), sticky="ew")

title_frame = ctk.CTkFrame(header, fg_color="transparent")
title_frame.pack(fill="x", padx=30, pady=(20, 10))

logo_frame = ctk.CTkFrame(title_frame, fg_color="transparent")
logo_frame.pack(side="left")
ctk.CTkLabel(logo_frame, text="🤖", font=ctk.CTkFont(size=40)).pack(side="left")
title_text = ctk.CTkLabel(logo_frame, text="Clau - Assistente Pessoal de Automação", font=ctk.CTkFont(size=28, weight="bold"))
title_text.pack(side="left", padx=15)

status_frame = ctk.CTkFrame(title_frame, fg_color="transparent")
status_frame.pack(side="right")
voice_status_indicator = ctk.CTkLabel(status_frame, text="🔴", font=ctk.CTkFont(size=20))
voice_status_indicator.pack(side="left", padx=5)
status_label = ctk.CTkLabel(status_frame, text="🔴 Clau Desativada", font=ctk.CTkFont(size=14), text_color="#6b7280")
status_label.pack(side="left")

info_bar = ctk.CTkFrame(header, height=40, corner_radius=10, fg_color=("#3b82f6", "#1e40af"))
info_bar.pack(fill="x", padx=30, pady=(0, 15))
task_count_label = ctk.CTkLabel(info_bar, text="📊 Carregando tarefas...", font=ctk.CTkFont(size=12, weight="bold"), text_color="white")
task_count_label.pack(side="left", padx=20)
recording_indicator = ctk.CTkLabel(info_bar, text="Pronto", font=ctk.CTkFont(size=12), text_color="#10b981")
recording_indicator.pack(side="right", padx=20)

main_container = ctk.CTkFrame(app, corner_radius=20)
main_container.grid(row=1, column=0, padx=25, pady=(0, 20), sticky="nsew")
main_container.grid_columnconfigure(0, weight=1)
main_container.grid_rowconfigure(1, weight=1)

top_panel = ctk.CTkFrame(main_container, corner_radius=15)
top_panel.grid(row=0, column=0, padx=15, pady=15, sticky="ew")

voice_panel = ctk.CTkFrame(top_panel, corner_radius=12, width=250)
voice_panel.pack(side="left", padx=10, pady=10, fill="y")
ctk.CTkLabel(voice_panel, text="🎤 Controle por Voz", font=ctk.CTkFont(size=16, weight="bold")).pack(pady=(15, 10))
voice_button = ctk.CTkButton(voice_panel, text="🎤 Ativar Clau", command=toggle_voice_system, width=200, height=45, font=ctk.CTkFont(size=14), fg_color="#1e40af", hover_color="#1e3a8a")
voice_button.pack(pady=10)
ctk.CTkButton(voice_panel, text="🔊 Testar Microfone", command=test_microphone, width=200, height=38, font=ctk.CTkFont(size=13)).pack(pady=5)
ctk.CTkButton(voice_panel, text="🔍 Diagnóstico de Áudio", command=show_audio_diagnostic, width=200, height=38, font=ctk.CTkFont(size=13), fg_color="#7c3aed").pack(pady=5)
test_status_label = ctk.CTkLabel(voice_panel, text="", font=ctk.CTkFont(size=12))
test_status_label.pack(pady=5)
ctk.CTkButton(voice_panel, text="📋 Comandos de Voz", command=show_help_dialog, width=200, height=38, font=ctk.CTkFont(size=13)).pack(pady=5)

learn_panel = ctk.CTkFrame(top_panel, corner_radius=12)
learn_panel.pack(side="left", padx=10, pady=10, fill="both", expand=True)
ctk.CTkLabel(learn_panel, text="📚 Aprender Novas Tarefas", font=ctk.CTkFont(size=16, weight="bold")).pack(pady=(15, 10))
name_frame = ctk.CTkFrame(learn_panel, fg_color="transparent")
name_frame.pack(fill="x", padx=20, pady=10)
ctk.CTkLabel(name_frame, text="Nome da Tarefa:", font=ctk.CTkFont(size=14)).pack(side="left")
task_name_entry = ctk.CTkEntry(name_frame, placeholder_text="Ex: Cadastro de Cliente", width=300, height=45, font=ctk.CTkFont(size=14))
task_name_entry.pack(side="left", padx=20)
teaching_button = ctk.CTkButton(learn_panel, text="▶ Ensinar Nova Tarefa", command=start_teaching, width=350, height=45, font=ctk.CTkFont(size=14, weight="bold"), fg_color="#059669", hover_color="#047857")
teaching_button.pack(pady=10)
stop_teaching_button = ctk.CTkButton(learn_panel, text="⏹ Parar Ensino", command=stop_teaching, width=350, height=40, font=ctk.CTkFont(size=13), fg_color="#dc2626", hover_color="#b91c1c", state="disabled")
stop_teaching_button.pack(pady=5)
aux_frame = ctk.CTkFrame(learn_panel, fg_color="transparent")
aux_frame.pack(pady=10)
ctk.CTkButton(aux_frame, text="🏷️ Nomear Atividade", command=name_learned_activity, width=170, height=38).pack(side="left", padx=5)
ctk.CTkButton(aux_frame, text="📊 Relatório de Aprendizado", command=show_learning_report, width=170, height=38, fg_color="#8b5cf6").pack(side="left", padx=5)

exec_panel = ctk.CTkFrame(top_panel, corner_radius=12, width=250)
exec_panel.pack(side="left", padx=10, pady=10, fill="y")
ctk.CTkLabel(exec_panel, text="⚡ Executar Tarefas", font=ctk.CTkFont(size=16, weight="bold")).pack(pady=(15, 10))
task_select = ctk.CTkComboBox(exec_panel, values=[], width=220, height=45, font=ctk.CTkFont(size=14), dropdown_font=ctk.CTkFont(size=13))
task_select.pack(pady=10)
ctk.CTkButton(exec_panel, text="🤖 Executar Tarefa", command=lambda: threading.Thread(target=execute_task, args=(task_select.get(), True), daemon=True).start(), width=220, height=45, font=ctk.CTkFont(size=14, weight="bold"), fg_color="#3b82f6", hover_color="#2563eb").pack(pady=10)
pause_button = ctk.CTkButton(exec_panel, text="⏸ Pausar", command=toggle_pause, width=220, height=40, font=ctk.CTkFont(size=13), fg_color="#d97706", hover_color="#b45309")
pause_button.pack(pady=5)
ctk.CTkButton(exec_panel, text="🛑 Parar Execução", command=stop_execution, width=220, height=40, font=ctk.CTkFont(size=13), fg_color="#ef4444", hover_color="#dc2626").pack(pady=5)
ctk.CTkButton(exec_panel, text="🗑️ Excluir Tarefa", command=delete_selected_task, width=220, height=40, font=ctk.CTkFont(size=13), fg_color="#7c3aed", hover_color="#6d28d9").pack(pady=5)

log_panel = ctk.CTkFrame(main_container, corner_radius=15)
log_panel.grid(row=1, column=0, padx=15, pady=(0, 15), sticky="nsew")
log_panel.grid_columnconfigure(0, weight=1)
log_panel.grid_rowconfigure(0, weight=1)

log_header = ctk.CTkFrame(log_panel, fg_color="transparent")
log_header.pack(fill="x", padx=20, pady=(15, 5))
ctk.CTkLabel(log_header, text="📝 Diálogo com a Clau", font=ctk.CTkFont(size=16, weight="bold")).pack(side="left")
log_controls = ctk.CTkFrame(log_header, fg_color="transparent")
log_controls.pack(side="right")
ctk.CTkButton(log_controls, text="🗑️ Limpar", command=lambda: log_box.delete("1.0", "end"), width=80, height=30).pack(side="left", padx=5)
ctk.CTkButton(log_controls, text="💾 Salvar Log", command=lambda: save_log_to_file(), width=80, height=30).pack(side="left", padx=5)

log_box = ctk.CTkTextbox(log_panel, font=ctk.CTkFont(size=13, family="Consolas"), wrap="word", fg_color=("#1a1a1a", "#ffffff"), text_color=("#ffffff", "#000000"))
log_box.pack(fill="both", expand=True, padx=20, pady=(0, 20))

for level, color in [("INFO", "#ffffff"), ("SUCCESS", "#10b981"), ("ERROR", "#ef4444"), ("WARNING", "#f59e0b"), ("VOICE", "#3b82f6"), ("SYSTEM", "#8b5cf6")]:
    log_box.tag_config(f"color_{level}", foreground=color)

progress_panel = ctk.CTkFrame(app, height=80, corner_radius=15)
progress_panel.grid(row=2, column=0, padx=25, pady=(0, 20), sticky="ew")
progress_label = ctk.CTkLabel(progress_panel, text="0%", width=70, font=ctk.CTkFont(size=16, weight="bold"))
progress_label.pack(side="left", padx=25)
progress_bar = ctk.CTkProgressBar(progress_panel, width=800, height=25, corner_radius=12, progress_color="#3b82f6")
progress_bar.pack(side="left", fill="x", expand=True, padx=(0, 25))
progress_bar.set(0)

footer = ctk.CTkFrame(app, height=60, corner_radius=12)
footer.grid(row=3, column=0, padx=25, pady=(0, 20), sticky="ew")
footer_text = "💡 Dica: Diga 'Clau' seguido do comando. Exemplo: 'Clau, execute cadastro de cliente'"
ctk.CTkLabel(footer, text=footer_text, font=ctk.CTkFont(size=13), text_color="#6b7280").pack(pady=20)


# FUNÇÕES ADICIONAIS 


def save_log_to_file():
    """Salva o log em um arquivo"""
    filename = f"clau_log_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.txt"
    try:
        log_content = log_box.get("1.0", "end")
        with open(filename, "w", encoding="utf-8") as f:
            f.write("=== LOG CLAU ===\n")
            f.write(f"Data: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write("=" * 50 + "\n\n")
            f.write(log_content)
        log(f"📄 Log salvo em: {filename}", "SUCCESS")
        voice_system.speak(f"Log salvo com sucesso.", "confirm")
    except Exception as e:
        log(f"❌ Erro ao salvar log: {e}", "ERROR")

def check_system_requirements():
    """Verifica se todos os requisitos estão atendidos"""
    log("🔍 Verificando requisitos do sistema...", "SYSTEM")
    requirements = {
        "customtkinter": "Interface gráfica",
        "pyttsx3": "Síntese de voz",
        "speech_recognition": "Reconhecimento de voz",
        "pyaudio": "Acesso ao microfone",
        "pyautogui": "Automação de interface"
    }
    all_ok = True
    for package, description in requirements.items():
        try:
            __import__(package)
            log(f"✅ {description}: OK", "SUCCESS")
        except ImportError as e:
            log(f"❌ {description}: FALTA - {e}", "ERROR")
            all_ok = False
    if not all_ok:
        log("⚠ Alguns requisitos não estão instalados. Use: pip install -r requirements_fixed.txt", "WARNING")
    return all_ok

def quick_voice_test():
    """Teste rápido inicial do sistema de voz"""
    check_system_requirements()
    log("🔧 Realizando teste rápido de inicialização...", "SYSTEM")
    voice_system.speak("Sistema inicializado. Teste de voz ok.", "confirm")
    app.after(2000, lambda: update_task_list())
    app.after(3000, lambda: log("\n" + "=" * 60 + "\n", "SYSTEM"))
    app.after(3200, lambda: log("🤖 CLAU - ASSISTENTE RPA INTELIGENTE v9.0", "SYSTEM"))
    app.after(3400, lambda: log("=" * 60, "SYSTEM"))
    app.after(3600, lambda: log("", "SYSTEM"))
    app.after(3800, lambda: log("💬 Clau: Olá! Eu sou a Clau, sua assistente pessoal.", "VOICE"))
    app.after(4000, lambda: log("💬 Clau: Para começar, ative o sistema de voz.", "VOICE"))
    app.after(4200, lambda: log("", "SYSTEM"))
    app.after(4400, lambda: log("🎯 COMANDOS DISPONÍVEIS:", "SYSTEM"))
    app.after(4600, lambda: log(" • 'Clau' - Para ativar", "SYSTEM"))
    app.after(4800, lambda: log(" • 'Clau, execute [tarefa]' - Executa uma tarefa", "SYSTEM"))
    app.after(5000, lambda: log(" • 'Clau, pare' - Para a execução", "SYSTEM"))
    app.after(5200, lambda: log(" • 'Clau, pause' - Pausa a execução", "SYSTEM"))
    app.after(5400, lambda: log(" • 'Clau, continue' - Continua a execução", "SYSTEM"))
    app.after(5600, lambda: log(" • 'Clau, aprenda [nome]' - Aprende nova tarefa", "SYSTEM"))
    app.after(5800, lambda: log("=" * 60 + "\n", "SYSTEM"))

# ============================================= 
# INICIALIZAÇÃO E FINALIZAÇÃO 
# ============================================= 

def on_closing():
    """Função executada ao fechar o aplicativo"""
    log("🔧 Encerrando sistema Clau...", "SYSTEM")
    if voice_listening:
        voice_system.stop_listening()
    if recording:
        stop_recording()
    if playing:
        stop_execution()
    learning_system.save_data()
    voice_system.save_voice_profile()
    voice_system.speak("Até logo! Obrigada por usar a Clau.", "happy")
    log("✅ Sistema encerrado com sucesso", "SUCCESS")
    app.destroy()

app.protocol("WM_DELETE_WINDOW", on_closing)
app.after(100, quick_voice_test)
app.mainloop()
