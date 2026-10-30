-- Prove2me | Theorems.Thm_BitcoinMiniscript_sat_sound
-- name    : BitcoinMiniscript.sat_sound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:24:52.415009+00:00
-- url     : https://prove2.me/theorems/f67c96b7-4597-4ce2-b536-f134f9e2574d
-- title:
--   A satisfaction makes the compiled script leave a true value
-- statement:
--   For `m : B` and `Sat f o m w`, with bounds: some `v` with `castToBool v = true` and `evalScript f o (w ++ rest) (compile m) = some (v :: rest)`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sat_sound (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .B) (w rest : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.Sat f o m w)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    ∃ v, BitcoinScript.castToBool v = true ∧
      BitcoinScript.evalScript f o (w ++ rest) (BitcoinMiniscript.compile m) = some (v :: rest) := by sorry
