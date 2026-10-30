-- Prove2me | Theorems.Thm_BitcoinMiniscript_dsat_sound
-- name    : BitcoinMiniscript.dsat_sound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:25:07.613879+00:00
-- url     : https://prove2.me/theorems/53debf12-4f27-43dd-9eb3-3b79a07af0db
-- title:
--   A dissatisfaction makes the compiled script leave the empty element
-- statement:
--   For `m : B` and `Dsat f o m w`, with bounds: `evalScript f o (w ++ rest) (compile m) = some ([] :: rest)`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.dsat_sound (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .B) (w rest : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.Dsat f o m w)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (w ++ rest) (BitcoinMiniscript.compile m) = some ([] :: rest) := by sorry
