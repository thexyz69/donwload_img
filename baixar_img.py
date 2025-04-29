import os
import requests
from requests.adapters import HTTPAdapter # Importa para usar Retry
from urllib3.util.retry import Retry # Importa Retry
from bs4 import BeautifulSoup
import time
import logging
import tkinter as tk
from tkinter import ttk, messagebox, font
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Thread, Lock, Condition
import re
import json
from datetime import datetime
from urllib.parse import urljoin, urlparse
from queue import Queue
import sys # Para verificar lxml (removido do código original, mas bom ter)


# --- Constantes ---
APP_VERSION = "v 1.0" # Versão atualizada
LOG_FILE = 'image_downloader.log'
CONFIG_FILE = 'config.json'
DOWNLOAD_FOLDER = 'donwload imgs' # <-- Nome da pasta alterado aqui
MAX_WORKERS = 10 # Ajustável - número de threads para download/crawl
REQUEST_TIMEOUT = (10, 30) # (connect_timeout, read_timeout) - Aumentado um pouco

# Configuração aprimorada de logging para o arquivo
# Agora inclui o nome do nível de log
logging.basicConfig(
    filename=LOG_FILE,
    level=logging.DEBUG, # Define o nível mínimo para DEBUG para capturar tudo no arquivo
    format='%(asctime)s - %(levelname)s - %(message)s', # Adicionado levelname
    filemode='w' # 'w' para sobrescrever a cada execução, 'a' para append
)

class ImageDownloader:
    def __init__(self, root):
        """Inicializa o aplicativo com a janela principal"""
        self.root = root
        self.setup_ui()
        self.session = self.create_session() # Usando a versão com retries
        self.stop_flag = False
        self.paused = False
        self.pause_cond = Condition(Lock())
        self.is_running = False
        self.download_count = 0
        self.images_found = 0
        self.pages_processed = 0
        self.url_queue = Queue()
        self.processed_urls = set()
        self.image_urls = set()
        self.base_domain = None # Para armazenar o domínio base do scan
        self.base_domain_name = None # Para armazenar o nome seguro da pasta do domínio

        # Carregar configuração após a UI ser configurada (principalmente entry_url)
        self.load_config()

    def create_session(self):
        """Cria e configura uma sessão HTTP com headers, timeout e retries"""
        session = requests.Session()
        session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8'
        })

        # Configuração de Retries
        retries = Retry(
            total=3,            # Número total de tentativas
            backoff_factor=0.5,  # Fator de espera entre tentativas (0.5, 1, 2 segundos...)
            status_forcelist=[500, 502, 503, 504], # Tentar novamente para estes códigos de status
            allowed_methods=frozenset(['HEAD', 'GET', 'OPTIONS']) # Métodos que permitem retry
        )

        # Monta o adaptador com a política de retry para http e https
        adapter = HTTPAdapter(max_retries=retries)
        session.mount('http://', adapter)
        session.mount('https://', adapter)

        return session

    def _configure_styles(self):
        """Configura estilos ttk e fontes para o tema dark hacking"""
        self.style = ttk.Style()
        self.style.theme_use('clam') # Baseia-se no tema 'clam' para customização

        # Definição de cores (Tema Dark Hacking)
        self.bg_color = "#0a0a0a"       # Fundo muito escuro
        self.text_color = "#00ff00"     # Texto principal em verde neon
        self.accent_color = "#00cc00"   # Cor de destaque em verde mais escuro
        self.error_color = "#ff0000"    # Cor de erro em vermelho vibrante
        self.success_color = "#00ff00"  # Cor de sucesso (igual ao texto principal)
        self.warning_color = "#ffff00"  # Cor de aviso em amarelo
        self.highlight_color = "#00ffff" # Cor de destaque/seleção em ciano
        self.timestamp_color = "#888888" # Cor do timestamp em cinza
        self.widget_bg = "#1a1a1a"      # Fundo de widgets um pouco menos escuro
        self.widget_border = "#008800"  # Borda de widgets em verde escuro

        # Configuração de fontes
        # Fontes monospace ficam bem em temas de hacking, mas Segoe UI ainda é uma boa opção legível
        self.terminal_font = font.Font(family="Consolas", size=10) # Consolas ou Courier New são boas opções monospace
        self.title_font = font.Font(family="Consolas", size=14, weight="bold")

        # Estilo da Progressbar
        self.style.configure('Custom.Horizontal.TProgressbar',
                             thickness=10,
                             background=self.accent_color, # Barra de progresso em verde
                             troughcolor=self.widget_bg,   # Fundo da barra em cinza escuro
                             bordercolor=self.widget_bg,
                             lightcolor=self.accent_color,
                             darkcolor=self.accent_color)

        # Tags para cores no log - APLICA SOMENTE SE log_text EXISTE E ESTÁ VISÍVEL
        if hasattr(self, 'log_text') and self.log_text.winfo_exists():
            self.log_text.tag_config("error", foreground=self.error_color)
            self.log_text.tag_config("success", foreground=self.success_color)
            self.log_text.tag_config("warning", foreground=self.warning_color)
            self.log_text.tag_config("info", foreground=self.text_color) # Texto info em verde neon
            self.log_text.tag_config("debug", foreground=self.highlight_color) # Debug em ciano
            self.log_text.tag_config("timestamp", foreground=self.timestamp_color)


    def setup_ui(self):
        """Configura todos os componentes da interface gráfica"""
        self.root.title(f"by theXYZZZ")
        self.root.geometry("1000x800")

        # Define estilos e cores ANTES de usar as cores para configurar widgets
        self._configure_styles()

        self.root.configure(bg=self.bg_color) # Usa a cor definida em _configure_styles

        # Frame principal
        main_frame = tk.Frame(self.root, bg=self.bg_color, bd=0)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Cabeçalho
        header_frame = tk.Frame(main_frame, bg=self.bg_color)
        header_frame.pack(fill=tk.X, pady=(0, 15))

        title_label = tk.Label(header_frame,
                              text="Image Downloader by theXYZZZ - V 1.0",
                              font=self.title_font,
                              fg=self.highlight_color, # Título em ciano
                              bg=self.bg_color)
        title_label.pack()

        # Seção de entrada de URL
        url_frame = tk.Frame(main_frame, bg=self.bg_color)
        url_frame.pack(fill=tk.X, pady=(0, 10))

        tk.Label(url_frame,
                 text="Target URL:",
                 font=self.terminal_font,
                 fg=self.text_color,
                 bg=self.bg_color).pack(side=tk.LEFT, padx=(0, 10))

        self.entry_url = tk.Entry(url_frame,
                                 width=70,
                                 font=self.terminal_font,
                                 bg=self.widget_bg, # Usa cor definida
                                 fg=self.text_color,
                                 insertbackground=self.text_color,
                                 relief='flat',
                                 bd=2,
                                 highlightbackground=self.widget_border, # Usa cor definida
                                 highlightcolor=self.highlight_color,
                                 highlightthickness=1)
        self.entry_url.pack(side=tk.LEFT, expand=True, fill=tk.X)

        # Seção de configuração
        config_frame = tk.Frame(main_frame, bg=self.bg_color)
        config_frame.pack(fill=tk.X, pady=(0, 15))

        # Configuração de profundidade
        tk.Label(config_frame,
                 text="Scan Depth:",
                 font=self.terminal_font,
                 fg=self.text_color,
                 bg=self.bg_color).pack(side=tk.LEFT, padx=(0, 5))

        self.max_depth = tk.IntVar(value=1)
        depth_spin = tk.Spinbox(config_frame,
                               from_=1, to=5,
                               textvariable=self.max_depth,
                               width=3,
                               font=self.terminal_font,
                               bg=self.widget_bg, # Usa cor definida
                               fg=self.text_color,
                               buttonbackground=self.widget_bg, # Usa cor definida
                               relief='flat',
                               bd=0,
                               highlightbackground=self.widget_border, # Usa cor definida
                               highlightcolor=self.highlight_color,
                               highlightthickness=1)
        depth_spin.pack(side=tk.LEFT)

        # Configuração de tipos de imagem
        tk.Label(config_frame,
                 text="Image Types:",
                 font=self.terminal_font,
                 fg=self.text_color,
                 bg=self.bg_color).pack(side=tk.LEFT, padx=(10, 5))

        self.image_types = {
            'JPG': tk.BooleanVar(value=True),
            'PNG': tk.BooleanVar(value=True),
            'GIF': tk.BooleanVar(value=False),
            'WEBP': tk.BooleanVar(value=True)
        }

        for name, var in self.image_types.items():
            cb = tk.Checkbutton(config_frame,
                               text=name,
                               variable=var,
                               font=self.terminal_font,
                               fg=self.text_color,
                               bg=self.bg_color,
                               selectcolor=self.widget_bg, # Usa cor definida
                               activebackground=self.bg_color,
                               activeforeground=self.text_color)
            cb.pack(side=tk.LEFT, padx=(0, 5))

        # Seção de botões
        button_frame = tk.Frame(main_frame, bg=self.bg_color)
        button_frame.pack(fill=tk.X, pady=(0, 15))

        self.btn_start = tk.Button(button_frame,
                                   text="Start Scan",
                                   command=self.start_download,
                                   font=self.terminal_font,
                                   bg=self.widget_bg, # Usa cor definida
                                   fg=self.text_color, # Texto do botão em verde neon
                                   activebackground=self.widget_border, # Usa cor definida
                                   activeforeground=self.text_color,
                                   relief='flat',
                                   bd=0,
                                   highlightbackground=self.highlight_color,
                                   highlightthickness=1, width=10) # Adicionado highlightthickness para borda
        self.btn_start.pack(side=tk.LEFT, padx=(0, 10))

        self.btn_pause = tk.Button(button_frame,
                                   text="Pause",
                                   command=self.toggle_pause,
                                   state=tk.DISABLED,
                                   font=self.terminal_font,
                                   bg=self.widget_bg, # Usa cor definida
                                   fg=self.text_color, # Texto do botão em verde neon
                                   activebackground=self.widget_border, # Usa cor definida
                                   activeforeground=self.text_color,
                                   relief='flat',
                                   bd=0,
                                   highlightbackground=self.highlight_color,
                                   highlightthickness=1, width=10) # Adicionado highlightthickness para borda
        self.btn_pause.pack(side=tk.LEFT, padx=(0, 10))

        self.btn_stop = tk.Button(button_frame,
                                  text="Stop",
                                  command=self.stop_download,
                                  state=tk.DISABLED,
                                  font=self.terminal_font,
                                  bg=self.widget_bg, # Usa cor definida
                                  fg=self.error_color, # Texto do botão em vermelho
                                  activebackground=self.widget_border, # Usa cor definida
                                  activeforeground=self.error_color,
                                  relief='flat',
                                  bd=0,
                                  highlightbackground=self.error_color,
                                  highlightthickness=1, width=10) # Adicionado highlightthickness para borda
        self.btn_stop.pack(side=tk.LEFT)

        # Barra de progresso
        progress_frame = tk.Frame(main_frame, bg=self.bg_color)
        progress_frame.pack(fill=tk.X, pady=(0, 10))

        tk.Label(progress_frame,
                 text="Progress:",
                 font=self.terminal_font,
                 fg=self.text_color,
                 bg=self.bg_color).pack(anchor='w')

        self.progress_bar = ttk.Progressbar(progress_frame,
                                            mode='determinate',
                                            style='Custom.Horizontal.TProgressbar')
        self.progress_bar.pack(fill=tk.X)

        # Os estilos da Progressbar já foram configurados em _configure_styles

        self.lbl_progress = tk.Label(progress_frame,
                                     text="Ready",
                                     font=self.terminal_font,
                                     fg=self.text_color,
                                     bg=self.bg_color)
        self.lbl_progress.pack(fill=tk.X)

        # Terminal de log
        log_frame = tk.Frame(main_frame, bg=self.bg_color)
        log_frame.pack(fill=tk.BOTH, expand=True)

        tk.Label(log_frame,
                 text="Log:",
                 font=self.terminal_font,
                 fg=self.text_color,
                 bg=self.bg_color).pack(anchor='w')

        self.log_text = tk.Text(log_frame,
                                wrap=tk.WORD,
                                state=tk.DISABLED,
                                bg=self.widget_bg, # Usa cor definida
                                fg=self.text_color, # Texto do log em verde neon
                                insertbackground=self.text_color,
                                font=self.terminal_font,
                                relief='flat',
                                bd=0,
                                highlightbackground=self.widget_border, # Usa cor definida
                                highlightcolor=self.highlight_color,
                                highlightthickness=1)
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True) # Ajustado para side=tk.LEFT

        scrollbar = tk.Scrollbar(log_frame, # Scrollbar deve estar no mesmo frame do Text widget
                                 bg=self.widget_bg, # Usa cor definida
                                 troughcolor=self.bg_color, # Usa cor definida
                                 relief='flat')
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.config(yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.log_text.yview)

        # Reconfigura as tags no log_text AGORA que ele existe e está empacotado
        # Chamamos _configure_styles novamente para aplicar as tags
        self._configure_styles()

        # Barra de status
        self.status_bar = tk.Frame(self.root, bg=self.bg_color, height=25) # Empacotado direto no root
        self.status_bar.pack(fill=tk.X, side=tk.BOTTOM, pady=(5,0)) # Empacotado na parte inferior

        self.status_message = tk.Label(self.status_bar,
                                       text="Status: Ready",
                                       font=self.terminal_font,
                                       fg=self.text_color, # Texto do status em verde neon
                                       bg=self.bg_color)
        self.status_message.pack(side=tk.LEFT)

        self.version_label = tk.Label(self.status_bar,
                                      text=APP_VERSION, # Usa a constante
                                      font=self.terminal_font,
                                      fg=self.timestamp_color, # Texto da versão em cinza
                                      bg=self.bg_color)
        self.version_label.pack(side=tk.RIGHT)


    def log_message(self, message, tag="info", level=logging.INFO):
        """
        Adiciona mensagem ao log da GUI (thread-safe) e ao arquivo de log.
        :param message: A mensagem de texto.
        :param tag: Tag para colorir na GUI ("info", "success", "warning", "error", "debug").
        :param level: Nível de logging para o arquivo (logging.INFO, logging.WARNING, etc.).
                      Se não especificado, é inferido da tag.
        """
        timestamp = datetime.now().strftime("%H:%M:%S")

        # Mapeia tag GUI para nível de logging se o nível não for especificado
        if level is logging.INFO: # Usamos INFO como default, se não for mudado, inferimos da tag
            if tag == "error":
                level = logging.ERROR
            elif tag == "warning":
                level = logging.WARNING
            elif tag == "success":
                level = logging.INFO # Não há nível 'success' no logging padrão, usa INFO
            elif tag == "debug":
                level = logging.DEBUG
            # Se a tag for "info" ou desconhecida, mantém logging.INFO

        # Log para o arquivo
        logging.log(level, message)

        # Atualiza a GUI (thread-safe)
        # A função `update_gui` será executada na thread principal do Tkinter
        def update_gui():
            try:
                # Verifica se os widgets ainda existem antes de tentar atualizá-los
                if hasattr(self, 'log_text') and self.log_text.winfo_exists():
                    self.log_text.config(state=tk.NORMAL) # Habilita para escrever
                    # Insere timestamp com tag 'timestamp'
                    self.log_text.insert(tk.END, f"[{timestamp}] ", "timestamp")
                    # Insere a mensagem com a tag de cor correspondente
                    self.log_text.insert(tk.END, message + "\n", tag)
                    self.log_text.see(tk.END) # Rola para o final
                    self.log_text.config(state=tk.DISABLED) # Desabilita para evitar edição

                if hasattr(self, 'status_message') and self.status_message.winfo_exists():
                    # Atualiza a barra de status com uma parte da mensagem
                    status_text = f"Status: {message[:70]}" + ("..." if len(message) > 70 else "")
                    self.status_message.config(text=status_text)

            except tk.TclError as e:
                # Captura erro comum quando a janela é fechada enquanto uma atualização está pendente
                #print(f"TclError during GUI update: {e}") # Opcional: imprimir no console
                pass # Ignora o erro, pois a janela está fechando

            except Exception as e:
                # Loga qualquer outro erro inesperado na atualização da GUI (vai para o arquivo)
                logging.error(f"Error updating GUI log/status: {e}", exc_info=True)


        # Agenda a função de atualização para ser executada na thread principal do Tkinter
        # using root.after is crucial for thread-safe GUI updates
        if hasattr(self, 'root') and self.root:
            self.root.after(0, update_gui)
        else:
            # Se o root não existe (app fechando), ainda loga para o arquivo
            pass
            # print(f"GUI not available for log: {message}") # Opcional: imprimir no console


    def load_config(self):
        """Carrega configurações do arquivo config.json"""
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r') as f:
                    config = json.load(f)
                    if 'target_url' in config and hasattr(self, 'entry_url'):
                        self.entry_url.insert(0, config.get('target_url', ''))
                    if 'scan_depth' in config and hasattr(self, 'max_depth'):
                        self.max_depth.set(config.get('scan_depth', 1))
                    # Carregar image_types (ajustado para verificar a existência da variável)
                    if 'image_types' in config and hasattr(self, 'image_types'):
                        for type_name, value in config['image_types'].items():
                            if type_name in self.image_types:
                                self.image_types[type_name].set(value)

                self.log_message(f"Config loaded from {CONFIG_FILE}", "success")
            except json.JSONDecodeError:
                self.log_message(f"Error decoding {CONFIG_FILE}. Using defaults.", "error", level=logging.ERROR)
                logging.exception(f"Detailed decoding error for {CONFIG_FILE}") # Loga traceback para o arquivo
            except Exception as e:
                self.log_message(f"Failed to load config from {CONFIG_FILE}: {str(e)}", "error", level=logging.ERROR)
                logging.exception(f"Detailed config loading error for {CONFIG_FILE}") # Loga traceback para o arquivo


    def save_config(self):
        """Salva configurações no arquivo config.json"""
        # Verifica se os widgets existem antes de tentar pegar os valores
        target_url = self.entry_url.get() if hasattr(self, 'entry_url') else ''
        scan_depth = self.max_depth.get() if hasattr(self, 'max_depth') else 1
        image_types_state = {name: var.get() for name, var in self.image_types.items()} if hasattr(self, 'image_types') else {}

        config = {
            'target_url': target_url,
            'scan_depth': scan_depth,
            'image_types': image_types_state
        }
        try:
            with open(CONFIG_FILE, 'w') as f:
                json.dump(config, f, indent=4) # Adicionado indent para legibilidade
            # Não logar para a GUI aqui, pois pode ser chamado ao fechar a janela
            logging.info(f"Config saved to {CONFIG_FILE}") # Loga apenas para o arquivo
        except Exception as e:
            # Usar print ou logging.error aqui pois a GUI pode não estar disponível
            logging.error(f"Failed to save config to {CONFIG_FILE}: {str(e)}", exc_info=True)


    def get_safe_domain_name(self, url):
        """Extrai nome do domínio de forma segura para criar pastas"""
        try:
            parsed = urlparse(url)
            domain = parsed.netloc
            if not domain: # Tenta adicionar http se não houver schema
                parsed = urlparse('http://' + url)
                domain = parsed.netloc

            # Remove porta, www., e caracteres inválidos
            domain = domain.split(':')[0].replace('www.', '')
            safe_domain = re.sub(r'[\\/*?:"<>|]', '_', domain).lower() # Usando '_' para caracteres inválidos
            if not safe_domain:
                self.log_message(f"Could not extract a safe domain name from {url}, using 'unknown_domain'", "warning", level=logging.WARNING)
                return "unknown_domain" # Nome fallback
            return safe_domain
        except Exception as e:
            self.log_message(f"Error extracting domain from {url}: {e}", "error", level=logging.ERROR)
            logging.exception(f"Detailed domain extraction error for {url}")
            return "invalid_domain" # Nome fallback


    def create_domain_folder(self, domain_name):
        """Cria a estrutura de pastas: DOWNLOAD_FOLDER/domain_name"""
        try:
            main_folder = DOWNLOAD_FOLDER
            if not os.path.exists(main_folder):
                os.makedirs(main_folder)
                self.log_message(f"Created main download folder: {main_folder}", "info")

            domain_folder = os.path.join(main_folder, domain_name)
            if not os.path.exists(domain_folder):
                os.makedirs(domain_folder)
                self.log_message(f"Created domain folder: {domain_folder}", "success")

            return domain_folder

        except OSError as e:
            self.log_message(f"Failed to create folder structure {DOWNLOAD_FOLDER}/{domain_name}: {e}", "error", level=logging.ERROR)
            logging.exception("Detailed folder creation error")
            return None # Não pode continuar sem a pasta


    def generate_image_name(self, img_url, response_headers=None):
        """Gera nome de arquivo válido para a imagem, tentando usar Content-Type"""
        try:
            # Tenta obter extensão do Content-Type se disponível
            content_type = response_headers.get('content-type', '') if response_headers else ''
            ext_from_content = ''
            if content_type.startswith('image/'):
                # Mapeamento simples (pode precisar de mais tipos)
                mime_map = {'jpeg': '.jpg', 'png': '.png', 'gif': '.gif', 'webp': '.webp'}
                img_type = content_type.split('/')[1].split(';')[0].lower()
                ext_from_content = mime_map.get(img_type, '')
                if ext_from_content:
                     self.log_message(f"Content-Type detected: {content_type} -> using extension {ext_from_content}", "debug", level=logging.DEBUG)


            # Obtém nome do path da URL
            path = urlparse(img_url).path
            filename = os.path.basename(path)

            # Limpa nome e obtém extensão original
            name_part, ext_original = os.path.splitext(filename)
            name_part = re.sub(r'[\\/*?:"<>|]', '_', name_part) # Substitui inválidos por _
            name_part = name_part[:100].strip() # Limita o tamanho e remove espaços extras

            # Decide a extensão final
            final_ext = ext_original.lower()
            # Usa extensão do Content-Type se a original for vazia/inválida ou se for mais específica
            if ext_from_content and (not final_ext or final_ext not in ['.jpg', '.jpeg', '.png', '.gif', '.webp']):
                final_ext = ext_from_content
            elif not final_ext: # Se ainda não tem extensão, default para .jpg (último recurso)
                final_ext = '.jpg'
                self.log_message(f"No extension found in URL path for {img_url}, defaulting to .jpg", "debug", level=logging.DEBUG)

            # Garante que a extensão detectada está na lista permitida (sem o ponto para comparação)
            enabled_exts = self.get_enabled_extensions() # Lista sem ponto
            final_ext_no_dot = final_ext.lstrip('.')
            if final_ext_no_dot not in enabled_exts:
                # Se a extensão detectada não está habilitada, loga um aviso
                self.log_message(f"Image extension '.{final_ext_no_dot}' detected for {os.path.basename(img_url)} is not enabled in settings. URL: {img_url}", "warning", level=logging.WARNING)
                # Você pode escolher parar aqui ou continuar. Vamos continuar mas com warning.


            # Lida com nomes vazios após limpeza
            if not name_part:
                timestamp_suffix = int(time.time() * 1000)
                safe_filename = f"image_{timestamp_suffix}{final_ext}"
                self.log_message(f"Generated fallback name for {img_url}: {safe_filename}", "debug", level=logging.DEBUG)
            else:
                safe_filename = f"{name_part}{final_ext}"


            return safe_filename

        except Exception as e:
            self.log_message(f"Error generating image name for {img_url}: {e}", "error", level=logging.ERROR)
            logging.exception(f"Detailed image name generation error for {img_url}")
            # Fallback final em caso de erro inesperado
            return f"fallback_error_{int(time.time() * 1000)}.jpg"


    def normalize_url(self, url, base_url=None):
        """Normaliza URL removendo fragmentos, params opcionais e junta com base se relativo"""
        if not url:
            return None
        try:
            url = url.strip()
            if base_url:
                url = urljoin(base_url, url)

            # Remove fragmento
            url = url.split('#', 1)[0]

            # Opcional: remover query params? Pode quebrar alguns sites.
            # Manter query params por padrão, pois podem ser essenciais
            # url = url.split('?', 1)[0]

            # Adiciona scheme se faltar (assumindo http)
            parsed = urlparse(url)
            if not parsed.scheme:
                url = 'http://' + url
                parsed = urlparse(url)
                self.log_message(f"Added http:// scheme to URL: {url}", "debug", level=logging.DEBUG)


            # Remove / no final do path para consistência, exceto se for só o domínio
            path = parsed.path.rstrip('/')
            if not path and parsed.path == '/': # Mantém a barra se for a raiz
                path = '/'

            # Recria a URL normalizada (lowercase no scheme e netloc)
            # Mantém case do path e query se existir, pois alguns servidores são case-sensitive
            normalized = f"{parsed.scheme.lower()}://{parsed.netloc.lower()}{path}"
            if parsed.query:
                normalized += f"?{parsed.query}"

            return normalized

        except Exception as e:
            self.log_message(f"Could not normalize URL '{url}': {e}", "warning", level=logging.WARNING)
            logging.exception(f"Detailed URL normalization error for {url}")
            return url # Retorna original em caso de erro


    def get_enabled_extensions(self):
        """Retorna extensões de imagem habilitadas (sem o ponto)"""
        extensions = set()
        # Adicionado tratamento para garantir que self.image_types existe e tem get()
        if hasattr(self, 'image_types'):
            if 'JPG' in self.image_types and self.image_types['JPG'].get():
                extensions.update(['jpg', 'jpeg'])
            if 'PNG' in self.image_types and self.image_types['PNG'].get():
                extensions.add('png')
            if 'GIF' in self.image_types and self.image_types['GIF'].get():
                extensions.add('gif')
            if 'WEBP' in self.image_types and self.image_types['WEBP'].get():
                extensions.add('webp')
        return list(extensions) # Retorna lista


    def is_image_url(self, url):
        """Verifica se URL parece ser uma imagem com extensão habilitada"""
        if not url:
            return False
        try:
            path = urlparse(url).path
            ext = os.path.splitext(path)[1].lower().strip('.')
            if not ext:
                # URLs sem extensão (.php, etc.) podem servir imagens via Content-Type,
                # mas checar isso com HEAD requests em massa seria lento.
                # Por enquanto, confiamos na extensão no path.
                # self.log_message(f"URL without extension in path: {url}", "debug") # Pode ser muito verboso
                return False # Assume que não é imagem se não tem extensão no path

            enabled_exts = self.get_enabled_extensions() # Lista sem ponto
            is_valid = ext in enabled_exts
            #if not is_valid:
                #self.log_message(f"Extension '{ext}' not in enabled list for {url}", "debug") # Verboso
            return is_valid

        except Exception as e:
            self.log_message(f"Error checking if URL is image {url}: {e}", "error", level=logging.ERROR)
            logging.exception(f"Detailed image URL check error for {url}")
            return False


    def process_page(self, url, depth, base_domain):
        """Processa página para encontrar imagens e links"""
        if self.stop_flag or depth > self.max_depth.get():
            self.log_message(f"Stopping scan for {url}: stop requested or max depth reached ({depth})", "debug", level=logging.DEBUG)
            return

        normalized_url = self.normalize_url(url)
        if not normalized_url:
            self.log_message(f"Skipping invalid URL: {url}", "warning", level=logging.WARNING)
            return

        if normalized_url in self.processed_urls:
            self.log_message(f"Skipping already processed URL: {normalized_url}", "debug", level=logging.DEBUG)
            return

        # Verifica se pertence ao domínio base antes de processar
        try:
            page_domain = urlparse(normalized_url).netloc.lower()
            # Permite subdomínios do base_domain
            if not page_domain.endswith(base_domain):
                self.log_message(f"Skipping external domain: {normalized_url}", "debug", level=logging.DEBUG)
                return
        except Exception as e:
            self.log_message(f"Error checking domain for {normalized_url}: {e}", "error", level=logging.ERROR)
            logging.exception(f"Detailed domain check error for {normalized_url}")
            return # Ignora URLs inválidas ou com erro na checagem

        self.processed_urls.add(normalized_url)
        self.pages_processed += 1

        try:
            self.log_message(f"Scanning page ({self.pages_processed}): {url} (Depth {depth})", "info")
            response = self.session.get(url, timeout=REQUEST_TIMEOUT)
            response.raise_for_status() # Lança exceção para status >= 400

            # Verifica se é HTML antes de tentar parsear
            content_type = response.headers.get('content-type', '').lower()
            if 'html' not in content_type:
                self.log_message(f"Skipping non-HTML content at {url} ({content_type})", "debug", level=logging.DEBUG)
                return

            # --- Usa lxml se disponível (tentativa de usar a versão mais rápida) ---
            parser = 'html.parser' # Default
            try:
                import lxml
                parser = 'lxml'
            except ImportError:
                # Loga a primeira vez que lxml não é encontrado
                if not hasattr(self, '_lxml_warned'):
                    self.log_message("lxml parser not found, using html.parser (slower). Install 'pip install lxml' for better performance.", "warning", level=logging.WARNING)
                    self._lxml_warned = True # Flag para logar apenas uma vez
            except Exception as e:
                self.log_message(f"Error importing lxml, falling back to html.parser: {e}", "warning", level=logging.WARNING)
                if not hasattr(self, '_lxml_warned'):
                    self._lxml_warned = True


            try:
                soup = BeautifulSoup(response.text, parser)
            except Exception as parse_err: # Captura outros erros de parsing
                self.log_message(f"Failed to parse HTML at {url} using {parser}: {parse_err}", "error", level=logging.ERROR)
                logging.exception(f"Detailed HTML parsing error for {url}")
                return
            # --- Fim do Bloco parser ---


            self.find_images_on_page(soup, url) # Chama método separado para imagens

            if depth < self.max_depth.get():
                self.find_links_on_page(soup, url, depth, base_domain) # Chama método separado para links


        except requests.exceptions.Timeout:
            self.log_message(f"Timeout accessing {url}", "warning", level=logging.WARNING)
        except requests.exceptions.TooManyRedirects:
            self.log_message(f"Too many redirects at {url}", "warning", level=logging.WARNING)
        except requests.exceptions.RequestException as e:
            # Loga erros de rede com nível apropriado
            level = logging.ERROR
            tag = "error"
            if hasattr(e, 'response') and e.response is not None:
                if e.response.status_code in [404, 403, 401]: # Considerar 4xx como avisos
                    level = logging.WARNING
                    tag = "warning"
                self.log_message(f"HTTP error scanning {url}: Status {e.response.status_code}", tag, level=level)
            else:
                 self.log_message(f"Network error scanning {url}: {str(e)}", tag, level=level)
            logging.exception(f"Detailed network error scan {url}") # Loga traceback


        except Exception as e:
            self.log_message(f"Unexpected error processing page {url}: {type(e).__name__} - {str(e)}", "error", level=logging.ERROR)
            logging.exception(f"Detailed exception processing page {url}") # Log completo no arquivo


    def find_images_on_page(self, soup, base_url):
        """Encontra URLs de imagem na página e as adiciona ao set"""
        images_found_on_this_page = 0
        for img in soup.find_all(['img', 'source']): # Inclui tag <source> para <picture>
            if self.stop_flag: break
            # Pega src ou srcset, tratando srcset básico (pega a primeira URL)
            img_src = img.get('src') or img.get('srcset')
            if isinstance(img_src, str) and ' ' in img_src: # Check if img_src is a string before splitting
                img_src = img_src.split(',')[0].split(' ')[0]

            if not img_src: continue

            img_url_abs = self.normalize_url(img_src, base_url=base_url)

            if img_url_abs and self.is_image_url(img_url_abs):
                # Usamos um lock para garantir que a atualização do set e contador seja segura entre threads
                # Na verdade, como image_urls só é preenchido na fase de scan antes do download,
                # não precisamos de um lock aqui se a fase de scan for única.
                # Mas como process_page pode ser chamado por múltiplas threads, é mais seguro usar um lock.
                # Ou melhor, usamos um set thread-safe ou mecanismos da Queue,
                # mas para um set simples, um Lock manual é ok.
                # Vamos usar a abordagem de adicionar e depois verificar o tamanho total fora dos workers.
                initial_image_count = len(self.image_urls)
                self.image_urls.add(img_url_abs)
                if len(self.image_urls) > initial_image_count:
                    # Apenas incrementa se for uma nova imagem
                    self.images_found += 1
                    images_found_on_this_page += 1
                    # Atualiza contagem total encontrada (sem barra de progresso ainda, só texto)
                    self.update_progress(self.download_count, self.images_found, is_scanning=True)

        if images_found_on_this_page > 0:
            self.log_message(f"Found {images_found_on_this_page} new image URL(s) on {base_url}", "debug", level=logging.DEBUG)


    def find_links_on_page(self, soup, base_url, depth, base_domain):
        """Encontra links na página e os adiciona à fila para processamento futuro"""
        links_added_count = 0
        for link in soup.find_all('a', href=True):
            if self.stop_flag: break
            href = link['href']
            # Ignora links vazios, âncoras, javascript etc.
            if not href or href.startswith(('#', 'javascript:', 'mailto:')):
                 continue

            new_url_abs = self.normalize_url(href, base_url=base_url)
            if not new_url_abs: continue

            new_normalized = self.normalize_url(new_url_abs) # Normaliza de novo para checar domínio

            if new_normalized and new_normalized not in self.processed_urls:
                try:
                    new_domain = urlparse(new_normalized).netloc.lower()
                    # Permanece no domínio/subdomínio do domínio base original
                    if new_domain.endswith(base_domain):
                        self.url_queue.put((depth + 1, new_url_abs)) # Adiciona à fila para processar
                        links_added_count += 1
                        self.log_message(f"Added link to queue: {new_normalized} (Depth {depth+1})", "debug", level=logging.DEBUG)
                    #else:
                        #self.log_message(f"Skipping external link: {new_normalized}", "debug", level=logging.DEBUG) # Muito verboso


                except Exception as e:
                    self.log_message(f"Error processing link {href} from {base_url}: {e}", "warning", level=logging.WARNING)
                    # Logging exception aqui pode ser muito verboso para cada link inválido
                    # logging.exception(f"Detailed link processing error for {href}")

        #if links_added_count > 0: # Mover log para fora do loop
            #self.log_message(f"Added {links_added_count} links to queue from {base_url}", "debug")


    def download_image(self, img_url): # Removido 'domain' pois base_domain_name agora é self.
        """Baixa imagem para pasta do domínio"""
        # --- Pausa / Stop Check ---
        while self.paused and not self.stop_flag:
            with self.pause_cond:
                # Espera com timeout curto para que a thread não fique presa se stop_flag mudar
                self.pause_cond.wait(timeout=0.1)
        if self.stop_flag:
            self.log_message(f"Download task cancelled for {os.path.basename(img_url)} due to stop request.", "debug", level=logging.DEBUG)
            return False # Download foi parado

        # --- Validação Inicial ---
        if not self.is_image_url(img_url):
            self.log_message(f"Skipping download for invalid/disabled image URL: {img_url}", "warning", level=logging.WARNING)
            return False

        # --- Criação de Pasta ---
        # self.base_domain_name já foi definido em start_download
        if not self.base_domain_name:
             # Isso não deve acontecer se o fluxo normal for seguido
             self.log_message(f"Base domain name not set, cannot download {img_url}", "error", level=logging.ERROR)
             return False

        domain_folder = self.create_domain_folder(self.base_domain_name)
        if not domain_folder:
            # create_domain_folder já logou o erro
            return False # Não pode continuar sem a pasta

        # --- Download ---
        try:
            # Loga o início da tentativa de download para o arquivo/debug
            self.log_message(f"Attempting to download: {os.path.basename(img_url)} from {img_url}", "debug", level=logging.DEBUG)

            # Usa stream=True para potencialmente grandes arquivos e lê em chunks
            response = self.session.get(img_url, stream=True, timeout=REQUEST_TIMEOUT)
            response.raise_for_status() # Lança exceção para status >= 400

            # Gera nome do arquivo usando headers se possível
            img_name = self.generate_image_name(img_url, response.headers)
            img_path = os.path.join(domain_folder, img_name)

            # Verifica se o arquivo já existe ANTES de baixar tudo
            if os.path.exists(img_path):
                # Opcional: verificar tamanho do arquivo para retomar/sobrescrever?
                self.log_message(f"Image already exists, skipping: {self.base_domain_name}/{img_name}", "info", level=logging.INFO)
                return False # Conta como pulado, não falha

            # Escreve o arquivo em chunks
            # downloaded_size = 0 # Remover se não usado para progress bar por arquivo
            # total_size = int(response.headers.get('content-length', 0)) # Remover se não usado

            with open(img_path, 'wb') as f:
                for chunk in response.iter_content(8192): # Chunk size de 8KB
                    if self.stop_flag:
                        raise Exception("Download stopped by user") # Levanta exceção para sair do loop

                    # Pausa check dentro do loop de download
                    while self.paused and not self.stop_flag:
                        with self.pause_cond:
                            self.pause_cond.wait(timeout=0.1) # Short timeout for responsiveness
                    # Verifica stop_flag novamente após sair da pausa
                    if self.stop_flag:
                        raise Exception("Download stopped by user") # Levanta exceção para sair do loop

                    f.write(chunk)
                    # downloaded_size += len(chunk) # Remover se não usado

            # Verifica se o arquivo foi criado corretamente (não vazio)
            if os.path.getsize(img_path) == 0:
                os.remove(img_path)
                raise ValueError("Downloaded file is empty")

            # Download concluído com sucesso
            self.download_count += 1
            self.log_message(f"Successfully downloaded: {self.base_domain_name}/{img_name}", "success", level=logging.INFO)
            self.update_progress(self.download_count, len(self.image_urls)) # Atualiza progresso total
            return True

        except requests.exceptions.Timeout:
            self.log_message(f"Timeout downloading {img_url}", "warning", level=logging.WARNING)
            return False # Falha no download

        except requests.exceptions.TooManyRedirects:
            self.log_message(f"Too many redirects downloading {img_url}", "warning", level=logging.WARNING)
            return False # Falha no download

        except requests.exceptions.RequestException as e:
            # Loga erros de rede com nível apropriado
            level = logging.ERROR
            tag = "error"
            if hasattr(e, 'response') and e.response is not None:
                if e.response.status_code in [404, 403, 401]: # Considerar 4xx como avisos
                    level = logging.WARNING
                    tag = "warning"
                self.log_message(f"HTTP error downloading {img_url}: Status {e.response.status_code}", tag, level=level)
            else:
                 self.log_message(f"Network error downloading {img_url}: {str(e)}", tag, level=level)
            logging.exception(f"Detailed network error download {img_url}") # Loga traceback
            return False # Falha no download


        except IOError as e:
            # Captura erros de escrita no disco
            self.log_message(f"File system error saving {img_url} to {img_path}: {e}", "error", level=logging.ERROR)
            logging.exception(f"Detailed IOError saving image {img_url}")
            # Tenta limpar o arquivo parcial se ele existir
            if 'img_path' in locals() and os.path.exists(img_path):
                try: os.remove(img_path)
                except OSError: pass # Ignora erros na remoção
            return False

        except Exception as e:
            # Captura qualquer outro erro inesperado
            self.log_message(f"Unexpected error downloading {img_url}: {type(e).__name__} - {str(e)}", "error", level=logging.ERROR)
            logging.exception(f"Detailed unexpected exception downloading image {img_url}")
            # Tenta limpar o arquivo parcial se ele existir
            if 'img_path' in locals() and os.path.exists(img_path):
                try: os.remove(img_path)
                except OSError: pass # Ignora erros na remoção
            return False

    def update_progress(self, current, total, is_scanning=False):
        """Atualiza a barra de progresso e o texto (thread-safe)"""
        # Função para atualizar a GUI na thread principal
        def perform_update():
            try:
                # Check if widgets exist before updating
                if not (hasattr(self, 'progress_bar') and self.progress_bar.winfo_exists() and
                        hasattr(self, 'lbl_progress') and self.lbl_progress.winfo_exists()):
                    return # Do nothing if widgets are gone

                if is_scanning:
                    self.lbl_progress.config(text=f"Scanning... Found {total} images on {self.pages_processed} pages")
                    # Não atualiza a barra de progresso no modo scanning determinate
                    self.progress_bar.config(mode='indeterminate') # Modo indeterminado durante o scan
                    if not self.paused and not self.stop_flag:
                        self.progress_bar.start() # Anima a barra
                    else:
                        self.progress_bar.stop() # Para a animação se pausado/parado

                else: # Modo download
                    self.progress_bar.config(mode='determinate') # Modo determinado para download
                    self.progress_bar.stop() # Para a animação indeterminada se estiver rodando
                    total_for_progress = max(total, 1) # Evita divisão por zero
                    progress_percent = (current / total_for_progress) * 100
                    self.progress_bar['value'] = progress_percent
                    self.lbl_progress.config(text=f"Downloading... {current}/{total} images ({progress_percent:.1f}%)")

            except tk.TclError as e:
                # Ignore TclError if GUI is closing
                pass
            except Exception as e:
                logging.error(f"Error updating progress bar: {e}")


        # Schedule update on the main thread
        if hasattr(self, 'root') and self.root:
            self.root.after(0, perform_update)


    def toggle_pause(self):
        """Alterna o estado de pausa/retomar"""
        if self.is_running:
            self.paused = not self.paused
            if self.paused:
                self.log_message("Operation Paused", "warning")
                self.btn_pause.config(text="Resume")
                # Atualiza a barra de progresso para parar a animação se estiver no modo scan
                self.update_progress(self.download_count, self.images_found, is_scanning=self.progress_bar['mode'] == 'indeterminate')

            else:
                self.log_message("Operation Resumed", "info")
                self.btn_pause.config(text="Pause")
                # Notifica threads esperando na condição de pausa
                with self.pause_cond:
                    self.pause_cond.notify_all()
                # Atualiza a barra de progresso para retomar a animação se estiver no modo scan
                self.update_progress(self.download_count, self.images_found, is_scanning=self.progress_bar['mode'] == 'indeterminate')


    def stop_download(self):
        """Sinaliza para parar o processo de download/scan"""
        if not self.is_running:
            self.log_message("No operation is currently running to stop.", "info")
            return

        self.stop_flag = True
        self.log_message("Stop requested. Finishing current tasks...", "warning")
        # Garante que threads pausadas ou esperando na fila sejam notificadas para verificar stop_flag
        with self.pause_cond:
            self.pause_cond.notify_all()

        # A thread principal run_scan_and_download vai detectar o stop_flag e chamar finish_download

    def set_buttons_state(self, start_state, pause_state, stop_state):
        """Define o estado dos botões (thread-safe)"""
        def update_buttons():
            try:
                # Verifica se os widgets existem antes de atualizar
                if (hasattr(self, 'btn_start') and self.btn_start.winfo_exists() and
                    hasattr(self, 'btn_pause') and self.btn_pause.winfo_exists() and
                    hasattr(self, 'btn_stop') and self.btn_stop.winfo_exists()):

                    self.btn_start.config(state=start_state)
                    self.btn_pause.config(state=pause_state)
                    self.btn_stop.config(state=stop_state)
                    # Reseta o texto do botão de pausa se não estiver ativo
                    if pause_state == tk.DISABLED:
                        self.btn_pause.config(text="Pause")
            except tk.TclError:
                pass # Ignora se a janela foi fechada

        if hasattr(self, 'root') and self.root:
            self.root.after(0, update_buttons)


    def start_download(self):
        """Inicia o processo de scan e download em uma nova thread"""
        if self.is_running:
            self.log_message("An operation is already running.", "warning")
            return

        start_url = self.entry_url.get().strip()
        if not start_url:
            messagebox.showwarning("Input Error", "Please enter a target URL.")
            self.log_message("Start URL is empty.", "warning", level=logging.WARNING)
            return

        # Valida e normaliza a URL inicial
        initial_normalized_url = self.normalize_url(start_url)
        if not initial_normalized_url or not urlparse(initial_normalized_url).netloc:
            messagebox.showwarning("Input Error", "Invalid URL format.")
            self.log_message(f"Invalid initial URL format: {start_url}", "error", level=logging.ERROR)
            return

        # Obtém o domínio base para restringir o scan e nome para a pasta
        self.base_domain = urlparse(initial_normalized_url).netloc.lower()
        self.base_domain_name = self.get_safe_domain_name(start_url) # Usa URL original para extração


        # Reset state variables
        self.stop_flag = False
        self.paused = False
        self.download_count = 0
        self.images_found = 0
        self.pages_processed = 0
        # Limpa as filas e sets para uma nova execução
        while not self.url_queue.empty():
            self.url_queue.get()
        self.processed_urls.clear()
        self.image_urls.clear()


        self.progress_bar['value'] = 0
        self.lbl_progress.config(text="Starting...")
        # Limpa o log da GUI no início
        if hasattr(self, 'log_text') and self.log_text.winfo_exists():
            self.log_text.config(state=tk.NORMAL)
            self.log_text.delete(1.0, tk.END)
            self.log_text.config(state=tk.DISABLED)


        # Adiciona a URL inicial na fila
        self.url_queue.put((0, initial_normalized_url)) # Tuple: (depth, url)

        self.log_message(f"Starting scan and download for: {initial_normalized_url}", "info")
        self.log_message(f"Scanning domain: {self.base_domain} up to depth {self.max_depth.get()}", "info")
        self.log_message(f"Images will be saved in: {DOWNLOAD_FOLDER}/{self.base_domain_name}/", "info")


        self.set_buttons_state(tk.DISABLED, tk.NORMAL, tk.NORMAL)


        # Inicia a thread principal de controle/execução
        self.is_running = True
        self.master_thread = Thread(target=self.run_scan_and_download, daemon=True)
        self.master_thread.start()


    def run_scan_and_download(self):
        """Controla o processo de scan e download usando ThreadPoolExecutor"""
        try:
            # --- Fase de Scan ---
            self.log_message("Starting scan phase to discover images and links...", "info")
            self.update_progress(self.download_count, self.images_found, is_scanning=True) # Inicia barra no modo scan

            # Executor para o scan (processar páginas)
            # Usa menos threads para scan, pois é mais CPU bound (parsing) e menos I/O bound (rede, disco)
            with ThreadPoolExecutor(max_workers=MAX_WORKERS // 2 or 1) as scan_executor:
                scan_futures = set()

                while not self.stop_flag and (not self.url_queue.empty() or scan_futures):

                    # Adiciona novas tarefas de scan enquanto houver URLs na fila e espaço no executor
                    while not self.paused and not self.stop_flag and not self.url_queue.empty() and len(scan_futures) < (MAX_WORKERS // 2 or 1) * 2: # Limita o número de tarefas na fila para evitar excesso de memória
                        try:
                            depth, url = self.url_queue.get_nowait() # Tenta pegar sem bloquear
                            # Normalizar e checar novamente para URLs da fila (segurança extra)
                            normalized_url_from_queue = self.normalize_url(url)
                            if not normalized_url_from_queue or normalized_url_from_queue in self.processed_urls:
                                self.log_message(f"Skipping queued URL (processed or invalid): {url}", "debug", level=logging.DEBUG)
                                continue # Pula este item da fila

                            future = scan_executor.submit(self.process_page, normalized_url_from_queue, depth, self.base_domain)
                            scan_futures.add(future)
                        except Queue.Empty:
                            break # Fila vazia no momento

                    # Processa futuros de scan concluídos
                    done_futures = set()
                    for future in scan_futures:
                        if future.done():
                            try:
                                future.result() # Captura e propaga exceções do worker
                            except Exception as exc:
                                # Exceções já devem ser logadas dentro de process_page
                                # logging.error(f"Scan task generated an exception: {exc}") # Evita log duplicado se já logado dentro do worker
                                pass # Ignora exceções que já foram logadas
                            done_futures.add(future)

                    scan_futures -= done_futures

                    # Espera um pouco para evitar busy-waiting
                    if not self.url_queue.empty() or scan_futures:
                        time.sleep(0.05) # Curto sleep
                    elif self.paused:
                        with self.pause_cond:
                            self.pause_cond.wait() # Espera na condição de pausa
                    else:
                        time.sleep(0.1) # Espera um pouco mais se a fila e futuros estão vazios
            # scan_executor.shutdown(wait=True) # feito pelo 'with' statement


            if self.stop_flag:
                self.log_message("Scan phase aborted by user.", "warning")
            else:
                self.log_message(f"Scan phase finished. Found {len(self.image_urls)} unique images across {self.pages_processed} pages.", "info")


            # Check if stopped or no images found before starting download
            if self.stop_flag or not self.image_urls:
                self.finish_download() # Chama finalização mesmo sem download
                return

            # --- Fase de Download ---
            total_images_to_download = len(self.image_urls)
            self.log_message(f"Starting download phase for {total_images_to_download} images...", "info")
            self.update_progress(self.download_count, total_images_to_download, is_scanning=False) # Muda para modo download na barra

            # Executor para download
            # Pode usar mais threads para download, pois é mais I/O bound (rede, disco)
            with ThreadPoolExecutor(max_workers=MAX_WORKERS) as download_executor:
                # Submete todas as imagens para download
                download_futures = {download_executor.submit(self.download_image, img_url): img_url for img_url in self.image_urls}

                # Espera a conclusão das tarefas de download
                for future in as_completed(download_futures):
                    if self.stop_flag:
                        # Ao parar, cancela futures restantes (melhor esforço)
                        for remaining_future in download_futures:
                            remaining_future.cancel()
                        break # Sai do loop de resultados

                    # img_url = download_futures[future] # Não é mais necessário, o log interno já tem a URL
                    try:
                        future.result() # Garante que exceções do worker sejam tratadas (já logadas dentro de download_image)
                    except Exception:
                        # Exceções já são logadas em download_image, apenas ignoramos aqui
                        pass

            # download_executor.shutdown(wait=True) # feito pelo 'with' statement

        except Exception as e:
            self.log_message(f"An unexpected error occurred during scan or download process: {str(e)}", "error", level=logging.CRITICAL)
            logging.exception("Critical exception in run_scan_and_download")

        finally:
            self.finish_download()

    def finish_download(self):
        """Limpa e finaliza o processo"""
        self.is_running = False
        # Reset flags
        was_stopped = self.stop_flag
        self.stop_flag = False
        self.paused = False

        # Garante que a barra de progresso pare e chegue a 100% (ou 0% se nada foi encontrado/parado no início)
        final_download_count = self.download_count
        total_found = len(self.image_urls)
        self.update_progress(final_download_count, total_found, is_scanning=False)
        if total_found == 0: # Se nada foi encontrado, barra fica em 0
            self.progress_bar['value'] = 0
        else: # Caso contrário, barra vai para 100%
             self.progress_bar['value'] = 100


        if was_stopped:
            final_message = f"Operation Stopped by User. Downloaded {final_download_count}/{total_found} images found."
            self.log_message(final_message, "warning", level=logging.WARNING)
        elif total_found == 0:
             final_message = f"Operation Finished. No images found on domain {self.base_domain} up to depth {self.max_depth.get()}."
             self.log_message(final_message, "info")
        else:
            final_message = f"Operation Finished. Downloaded {final_download_count}/{total_found} images to {DOWNLOAD_FOLDER}/{self.base_domain_name}/"
            self.log_message(final_message, "success")

        self.lbl_progress.config(text=final_message) # Atualiza label final

        # Restaura estado dos botões
        self.set_buttons_state(tk.NORMAL, tk.DISABLED, tk.DISABLED)


    # toggle_pause já está ok com as chamadas a log_message

    # stop_download já está ok com a chamada a log_message inicial.
    # A finalização e o log final de stop são feitos em finish_download


    def on_close(self):
        """Manipula fechamento da janela"""
        if self.is_running:
            if messagebox.askokcancel("Exit", "An operation is running. Stop and exit?"):
                self.stop_download()
                # Espera um pouco para que a thread principal finalize
                self.root.after(500, self._finish_and_destroy) # Pequeno delay para garantir que a thread finalize
            else:
                pass # Não fechar
        else:
            self.save_config()
            self.root.destroy()

    def _finish_and_destroy(self):
        """Garanta que a config seja salva e a janela destruída após parar."""
        self.save_config()
        if hasattr(self, 'root') and self.root:
            self.root.destroy()


if __name__ == "__main__":
    # Check for lxml availability outside the class if desired for initial print
    try:
        import lxml
        print("lxml parser found.") # Keep this print as requested
    except ImportError:
        print("lxml parser not found. Install 'pip install lxml' for better performance.")
        # The application will fall back to html.parser and log a warning via log_message


    root = tk.Tk()
    app = ImageDownloader(root)
    root.protocol("WM_DELETE_WINDOW", app.on_close)
    root.mainloop()
