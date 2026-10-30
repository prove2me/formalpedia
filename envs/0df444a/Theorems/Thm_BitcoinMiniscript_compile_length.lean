-- Prove2me | Theorems.Thm_BitcoinMiniscript_compile_length
-- name    : BitcoinMiniscript.compile_length
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:25:42.773201+00:00
-- url     : https://prove2.me/theorems/9294d725-0de0-405f-9a78-4c160ccc0f9b
-- title:
--   The compiled script has size m instructions
-- statement:
--   `(compile m).length = size m`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.compile_length (m : BitcoinMiniscript.Ms) :
    (BitcoinMiniscript.compile m).length = BitcoinMiniscript.size m := by sorry
