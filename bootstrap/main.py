#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
proofuck 完全準拠系リファレンスインタプリタ (Reference Interpreter for proofuck)
仕様に基づく素数制約、逆転優先順位AST、任意精度小数抽出、ゼロ保存文字列演算、
および30,000セル・8ビット循環テープ型VMの全機能を包括的に実装。
セルフホスト完全耐性最終版（=位置厳密固定＋ブロック内最終スタック検査）。
"""

import sys
import re
from decimal import Decimal, getcontext

# セルフホスト規模の長大式でも桁落ちを完全に防ぐため精度を10000桁に強化
getcontext().prec = 10000

class ProofuckError(Exception):
    """proofuckコンパイルおよび実行時における全ての致命的エラーを捕捉する基底例外クラス"""
    pass

def is_prime(n: int) -> bool:
    """エラトステネスの篩の論理に基づく、効率的な素数判定アルゴリズム"""
    if n <= 1: return False
    if n <= 3: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

class VariableManager:
    """変数の厳密な順序規則（辞書式生成）とプライム値への単射マッピングを管理するクラス"""
    
    def __init__(self):
        self.var_map = {}
        self.used_primes = set()
        self.generator = self._create_generator()

    def _create_generator(self):
        """x-z, α-ω(24文字), a-w の順序で変数を無限生成するジェネレータ"""
        base = ['x', 'y', 'z']
        
        # ギリシア文字 α(U+03B1) から ω(U+03C9) までの24文字（語末形シグマ ς を除く）
        greek = [chr(i) for i in range(ord('α'), ord('ω') + 1) if chr(i) != 'ς']
        
        # ラテン小文字 a から w まで
        latin = [chr(i) for i in range(ord('a'), ord('x'))]
        
        sequence = base + greek + latin
        ticks = ""
        
        while True:
            for var in sequence:
                yield var + ticks
            ticks += "'"  # 2周目以降はプライム記号を付与

    def register_variable(self, name: str, value: int):
        """定義された変数と素数値の妥当性を検証し、マップに登録する"""
        expected_name = next(self.generator)
        if name != expected_name:
            raise ProofuckError(f"変数の定義順序が不正です。期待される変数: {expected_name}, 実際の変数: {name}")
            
        if not is_prime(value):
            raise ProofuckError(f"変数 {name} に代入された値 {value} は素数ではありません。")
            
        if value in self.used_primes:
            raise ProofuckError(f"素数値 {value} は既に他の変数で定義されており、重複が禁止されています。")
            
        self.var_map[name] = Decimal(value)
        self.used_primes.add(value)


class IntraBlockEvaluator:
    """ブロック内部の数式における逆転演算子優先順位と重複使用禁止ルールを適用したAST評価器"""
    
    # proofuck独自仕様: + と - は × と ÷ よりも優先される（優先度値が高いほど優先）
    PRECEDENCE = {'+': 2, '-': 2, '×': 1, '÷': 1}

    @staticmethod
    def evaluate(expression: str, var_map: dict) -> Decimal:
        """Shunting-yardアルゴリズムを用いて数式を逆ポーランド記法に変換し、安全に評価する"""
        used_vars = set()
        used_ops = set()
        tokens = []
        
        i = 0
        while i < len(expression):
            char = expression[i]
            if char in IntraBlockEvaluator.PRECEDENCE:
                if char in used_ops:
                    raise ProofuckError(f"ブロック内で演算子 '{char}' が複数回使用されています（仕様違反）。")
                used_ops.add(char)
                tokens.append(char)
                i += 1
            else:
                var_name = char
                i += 1
                while i < len(expression) and expression[i] == "'":
                    var_name += "'"
                    i += 1
                
                if var_name not in var_map:
                    raise ProofuckError(f"未定義の変数 '{var_name}' が数式ブロック内で使用されました。")
                if var_name in used_vars:
                    raise ProofuckError(f"ブロック内で変数 '{var_name}' が複数回使用されています（仕様違反）。")
                
                used_vars.add(var_name)
                tokens.append(var_map[var_name])

        # Shunting-yardアルゴリズムによるASTの線形化 (RPN生成)
        output_queue = []
        operator_stack = []
        
        for token in tokens:
            if isinstance(token, Decimal):
                output_queue.append(token)
            else:
                while (operator_stack and 
                       IntraBlockEvaluator.PRECEDENCE[operator_stack[-1]] >= IntraBlockEvaluator.PRECEDENCE[token]):
                    output_queue.append(operator_stack.pop())
                operator_stack.append(token)
                
        while operator_stack:
            output_queue.append(operator_stack.pop())
            
        # RPN評価
        eval_stack = []
        for token in output_queue:
            if isinstance(token, Decimal):
                eval_stack.append(token)
            else:
                if len(eval_stack) < 2:
                    raise ProofuckError("数式ブロックの構文が不正です。演算に対するオペランドが不足しています。")
                b = eval_stack.pop()
                a = eval_stack.pop()
                
                if token == '+': eval_stack.append(a + b)
                elif token == '-': eval_stack.append(a - b)
                elif token == '×': eval_stack.append(a * b)
                elif token == '÷':
                    if b == 0:
                        raise ProofuckError("数式ブロック内でゼロ除算が発生しました。")
                    eval_stack.append(a / b)
        
        # 【セルフホスト必須修正】最終スタックがちょうど1つであることを厳密に検証
        if len(eval_stack) != 1:
            raise ProofuckError("数式ブロックの構文が不正です。最終的に評価スタックにちょうど1つの値が残っていません（演算子不足／過剰オペランド／並び違い）。")
                    
        return eval_stack[0]


class DecimalExtractor:
    """算出された任意精度浮動小数点数から、指定された範囲の桁を双方向に抽出するメカニズム"""

    @staticmethod
    def extract(value: Decimal, start: int, end: int) -> str:
        """
        負数対応（符号無視）＋高精度保証（セルフホスト必須）。
        例: (-16!-13) の場合、小数点以下第16位から13位へ遡る方向で文字列を構築する。
        """
        value = abs(value)
        
        # 高精度で全桁を正確に文字列化（prec=10000対応）
        val_str = format(value, '.1000f')
        if '.' not in val_str:
            val_str += '.'
        
        int_part, dec_part = val_str.split('.')
        
        def get_digit_at(pos: int) -> str:
            if pos < 0:
                idx = abs(pos) - 1
                return dec_part[idx] if idx < len(dec_part) else '0'
            elif pos > 0:
                idx = len(int_part) - pos
                return int_part[idx] if idx >= 0 else '0'
            else:
                return '0'

        result = ""
        step = -1 if start > end else 1
        current = start
        
        while True:
            result += get_digit_at(current)
            if current == end:
                break
            current += step
            
        return result


class InterBlockStringMath:
    """通常の演算子優先順位と、ゼロ保存パディング規則を持つ文字列数学の評価器"""

    # ブロック間では通常の数学優先順位を適用（×が+や-より優先）
    PRECEDENCE = {'×': 2, '+': 1, '-': 1}

    @staticmethod
    def _pad_and_calculate(val1: str, val2: str, op: str) -> str:
        i_val1, i_val2 = int(val1), int(val2)
        
        if op == '+':
            res = str(i_val1 + i_val2)
            return res.zfill(max(len(val1), len(val2)))
        elif op == '-':
            res = i_val1 - i_val2
            if res < 0:
                raise ProofuckError(f"ブロック間減算の結果が負になりました: {val1} - {val2} = {res} "
                                    f"（最終VMコードは正の数列（0-9のみ）のみ許可されます）")
            return str(res).zfill(max(len(val1), len(val2)))
        elif op == '×':
            res = str(i_val1 * i_val2)
            # 乗算のパディング規則: 長さA + 長さB - 1
            pad_len = len(val1) + len(val2) - 1
            return res.zfill(pad_len)
        raise ProofuckError(f"未知のブロック間演算子: {op}")

    @staticmethod
    def evaluate(blocks: list, operators: list) -> str:
        if not blocks:
            return ""
        
        # 乗算を先に処理する
        i = 0
        while i < len(operators):
            if operators[i] == '×':
                res = InterBlockStringMath._pad_and_calculate(blocks[i], blocks[i + 1], '×')
                blocks[i] = res
                del blocks[i + 1]
                del operators[i]
            else:
                i += 1
                
        # 加算と減算を左から右へ処理する
        i = 0
        while i < len(operators):
            res = InterBlockStringMath._pad_and_calculate(blocks[i], blocks[i + 1], operators[i])
            blocks[i] = res
            del blocks[i + 1]
            del operators[i]
            
        return blocks[0] if blocks else ""


class ProofuckInterpreter:
    """字句解析からブロック統合、予測結果の照合までを統括するメインコントローラ"""

    def __init__(self, source_code: str):
        self.lines = [line.strip() for line in source_code.strip().split('\n') if line.strip()]
        self.var_manager = VariableManager()
        self.expected_result = None
        self.main_code_line = ""

    def parse_and_compile(self) -> str:
        if not self.lines:
            raise ProofuckError("ソースコードが空です。")
        if self.lines[0] != "∵":
            raise ProofuckError("ソースコードの先頭は必ずスタート宣言 '∵' でなければなりません。")
        if self.lines[-1] != "Q.E.D.":
            raise ProofuckError("ソースコードの末尾は必ず終了宣言 'Q.E.D.' でなければなりません。")

        line_idx = 1
        
        # 1. 変数定義部の解析
        while line_idx < len(self.lines):
            line = self.lines[line_idx]
            match = re.match(r"^([^=]+)=(\d+)$", line)
            
            if '(' in line or line.startswith('='):
                break
                
            if match:
                var_name = match.group(1)
                var_val = int(match.group(2))
                self.var_manager.register_variable(var_name, var_val)
                line_idx += 1
            else:
                break

        # 2. 主論理部および予測結果の取得（仕様厳密対応）
        # Q.E.D.直前の1行だけが予測結果でなければならない
        if line_idx >= len(self.lines) - 1:
            raise ProofuckError("予測結果の行 (=...) が見つかりません。")
        
        main_logic_lines = self.lines[line_idx : -1]  # Q.E.D.直前まで
        
        if not main_logic_lines or not main_logic_lines[-1].startswith('='):
            raise ProofuckError("予測結果の行 (=...) はメイン論理部の直後（Q.E.D.の直前）に1行だけ置かなければなりません。")
        
        self.expected_result = main_logic_lines[-1][1:].strip()
        
        # 予測結果より前の行はすべてロジックフラグメント
        logic_fragments = main_logic_lines[:-1]
        self.main_code_line = "".join(logic_fragments).replace(" ", "")

        # 3. 数式ブロックの抽出と評価
        block_pattern = re.compile(r"\(([^)]+)\)\(([-0-9]+)!([-0-9]+)\)")
        matches = list(block_pattern.finditer(self.main_code_line))
        
        if not matches:
            raise ProofuckError("評価可能な数式ブロックが見つかりません。")

        blocks_results = []
        inter_operators = []
        last_end = 0
        
        for match in matches:
            if last_end > 0:
                op_str = self.main_code_line[last_end:match.start()].strip()
                if op_str not in ['+', '-', '×']:
                    raise ProofuckError(f"ブロック間を接続する不正な演算子を検出しました: {op_str}")
                inter_operators.append(op_str)
                
            expression = match.group(1)
            start_digit = int(match.group(2))
            end_digit = int(match.group(3))
            
            if abs(start_digit) > 30 or abs(end_digit) > 30:
                raise ProofuckError("小数桁の抽出指定は、30桁から-30桁の範囲内である必要があります。")
                
            eval_val = IntraBlockEvaluator.evaluate(expression, self.var_manager.var_map)
            extracted_str = DecimalExtractor.extract(eval_val, start_digit, end_digit)
            blocks_results.append(extracted_str)
            
            last_end = match.end()

        # 厳密構文チェック（先頭ゴミ＋末尾ゴミを完全排除）
        if matches[0].start() != 0:
            prefix = self.main_code_line[:matches[0].start()].strip()
            if prefix:
                raise ProofuckError(f"主論理部の先頭に余分な文字があります（構文エラー）: '{prefix}'")
        
        if last_end != len(self.main_code_line):
            leftover = self.main_code_line[last_end:].strip()
            if leftover:
                raise ProofuckError(f"数式ブロック解析後に余分な文字が残っています（構文エラー）: '{leftover}'")

        # 4. ブロック間のゼロ保存文字列演算の実行
        final_machine_code = InterBlockStringMath.evaluate(blocks_results, inter_operators)

        # 5. 予測結果との厳密照合
        if final_machine_code != self.expected_result:
            raise ProofuckError(f"計算結果の不一致: 予測された数列 [{self.expected_result}] に対して、実際の算出数列は [{final_machine_code}] でした。")

        return final_machine_code


class VirtualMachine:
    """30,000個の循環テープメモリと、抽出された数列を命令として実行するチューリング完全なオートマトン"""
    
    def __init__(self, code: str):
        self.code = code
        self.tape = [0] * 30000
        self.pointer = 0
        self.pc = 0
        
        # opcodeマッピング仕様
        self.cmd_map = {
            '1': '>', '2': '<', '3': '+', '4': '-',
            '5': '.', '6': ',', '7': '[', '8': ']',
            '9': 'NOP', '0': 'NOP'
        }
        self.instructions = [self.cmd_map.get(char, 'NOP') for char in self.code]
        self.bracket_map = self._build_bracket_map()

    def _build_bracket_map(self) -> dict:
        """実行前最適化: ループ命令（[ と ]）の対応関係を静的解析し、O(1)のジャンプテーブルを構築する"""
        bmap = {}
        stack = []
        for i, cmd in enumerate(self.instructions):
            if cmd == '[':
                stack.append(i)
            elif cmd == ']':
                if not stack:
                    raise ProofuckError("仮想マシンの実行前エラー: 閉じ括弧 ']' に対応する開き括弧 '[' が存在しません。")
                start = stack.pop()
                bmap[start] = i
                bmap[i] = start
        if stack:
            raise ProofuckError("仮想マシンの実行前エラー: 開き括弧 '[' が閉じられていません。")
        return bmap

    def run(self):
        """仮想マシンのメイン実行ループ。テープとポインタの完全なモジュロ循環を保証する"""
        length = len(self.instructions)
        while self.pc < length:
            cmd = self.instructions[self.pc]
            
            if cmd == '>':
                self.pointer = (self.pointer + 1) % 30000
            elif cmd == '<':
                self.pointer = (self.pointer - 1) % 30000
            elif cmd == '+':
                self.tape[self.pointer] = (self.tape[self.pointer] + 1) % 256
            elif cmd == '-':
                self.tape[self.pointer] = (self.tape[self.pointer] - 1) % 256
            elif cmd == '.':
                sys.stdout.write(chr(self.tape[self.pointer]))
                sys.stdout.flush()
            elif cmd == ',':
                char = sys.stdin.read(1)
                if not char:  # EOFハンドリング: 仕様に従い0を強制代入
                    self.tape[self.pointer] = 0
                else:
                    self.tape[self.pointer] = ord(char) % 256
            elif cmd == '[':
                if self.tape[self.pointer] == 0:
                    self.pc = self.bracket_map[self.pc]
            elif cmd == ']':
                if self.tape[self.pointer] != 0:
                    self.pc = self.bracket_map[self.pc]
                    
            self.pc += 1

def execute_proofuck_file(source_data: str):
    try:
        interpreter = ProofuckInterpreter(source_data)
        machine_code = interpreter.parse_and_compile()
        vm = VirtualMachine(machine_code)
        vm.run()
    except ProofuckError as e:
        print(f"\n[Proofuck 致命的エラー] {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"\n[システム エラー] 予期せぬ障害が発生しました: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    # スクリプト引数からファイルパスを受け取るか、標準入力から直接ソースコードを読み込む
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r', encoding='utf-8') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
        
    execute_proofuck_file(source)