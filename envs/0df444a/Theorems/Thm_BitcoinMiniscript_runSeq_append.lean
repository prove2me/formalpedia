-- Prove2me | Theorems.Thm_BitcoinMiniscript_runSeq_append
-- name    : BitcoinMiniscript.runSeq_append
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:22:41.938351+00:00
-- url     : https://prove2.me/theorems/74da461c-9f4c-404e-ace3-44d731f10412
-- title:
--   Sequential execution composes
-- statement:
--   `runSeq f o s (a ++ b)` runs `a`, then `b` from the result (or fails if `a` fails).
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.runSeq_append (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle)
    (s : BitcoinScript.State) (a b : BitcoinScript.Script) :
    BitcoinMiniscript.runSeq f o s (a ++ b) =
      match BitcoinMiniscript.runSeq f o s a with
      | none => none
      | some s' => BitcoinMiniscript.runSeq f o s' b := by sorry
