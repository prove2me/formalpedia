-- Prove2me | Theorems.Thm_BitcoinMiniscript_run_eq_runSeq
-- name    : BitcoinMiniscript.run_eq_runSeq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:22:55.222153+00:00
-- url     : https://prove2.me/theorems/72f58ce7-3e51-4709-ac42-3a6d7e6b3732
-- title:
--   The interpreter's loop is runSeq followed by the balance check
-- statement:
--   `run f o s sc` is `runSeq f o s sc` followed by the test that the condition stack is empty.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.run_eq_runSeq (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle)
    (s : BitcoinScript.State) (sc : BitcoinScript.Script) :
    BitcoinScript.run f o s sc =
      match BitcoinMiniscript.runSeq f o s sc with
      | none => none
      | some s' => if s'.vfExec.isEmpty then some s' else none := by sorry
