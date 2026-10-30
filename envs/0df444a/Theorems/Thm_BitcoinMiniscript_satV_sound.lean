-- Prove2me | Theorems.Thm_BitcoinMiniscript_satV_sound
-- name    : BitcoinMiniscript.satV_sound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:25:21.657049+00:00
-- url     : https://prove2.me/theorems/2272fad2-97ee-45d1-86fa-8dbfdf2538c4
-- title:
--   A V satisfaction leaves the stack below untouched
-- statement:
--   For `m : V` and `SatV f o m w`, with bounds: `evalScript f o (w ++ rest) (compile m) = some rest`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.satV_sound (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .V) (w rest : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.SatV f o m w)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (w ++ rest) (BitcoinMiniscript.compile m) = some rest := by sorry
