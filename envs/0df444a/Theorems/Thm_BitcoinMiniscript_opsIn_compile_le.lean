-- Prove2me | Theorems.Thm_BitcoinMiniscript_opsIn_compile_le
-- name    : BitcoinMiniscript.opsIn_compile_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:25:57.006117+00:00
-- url     : https://prove2.me/theorems/7a727e1f-ab2b-4362-b2a7-0612d0052449
-- title:
--   The counted opcodes are bounded by opsMax
-- statement:
--   `opsIn (compile m) ≤ opsMax m`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.opsIn_compile_le (m : BitcoinMiniscript.Ms) :
    BitcoinScript.opsIn (BitcoinMiniscript.compile m) ≤ BitcoinMiniscript.opsMax m := by sorry
