-- Prove2me | Theorems.Thm_BitcoinMiniscript_semW_sound
-- name    : BitcoinMiniscript.semW_sound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:24:42.2677+00:00
-- url     : https://prove2.me/theorems/b3be04ce-64a6-4f78-8fba-bc892a005f2c
-- title:
--   Compiler soundness for W: the output lands next to the top element
-- statement:
--   For `m : W` and `Sem f o m w [v]`: running `compile m` on `x :: (w ++ rest)` leaves `v :: x :: rest` or `x :: v :: rest` (the `a:` and `s:` wrappers' two placements).
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.semW_sound (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .W) (w rest : List BitcoinScript.Bytes) (x v : BitcoinScript.Bytes)
    (hs : BitcoinMiniscript.Sem f o m w [v])
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + 1 + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (x :: (w ++ rest)) (BitcoinMiniscript.compile m) = some (v :: x :: rest) ∨
    BitcoinScript.evalScript f o (x :: (w ++ rest)) (BitcoinMiniscript.compile m) = some (x :: v :: rest) := by sorry
