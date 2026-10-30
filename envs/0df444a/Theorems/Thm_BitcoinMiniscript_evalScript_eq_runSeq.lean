-- Prove2me | Theorems.Thm_BitcoinMiniscript_evalScript_eq_runSeq
-- name    : BitcoinMiniscript.evalScript_eq_runSeq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:23:06.09132+00:00
-- url     : https://prove2.me/theorems/46e0f7d8-304a-4a8c-a23f-c192860b0fa6
-- title:
--   evalScript through runSeq
-- statement:
--   `evalScript f o st sc` is the stack of `runSeq` from the initial state when the condition stack ends empty, `none` otherwise.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.evalScript_eq_runSeq (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle)
    (st : List BitcoinScript.Bytes) (sc : BitcoinScript.Script) :
    BitcoinScript.evalScript f o st sc =
      match BitcoinMiniscript.runSeq f o (BitcoinScript.State.initial st) sc with
      | none => none
      | some s' => if s'.vfExec.isEmpty then some s'.stack else none := by sorry
