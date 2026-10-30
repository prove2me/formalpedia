-- Prove2me | Theorems.Thm_BitcoinMiniscript_typeOf_sound
-- name    : BitcoinMiniscript.typeOf_sound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:26:11.77198+00:00
-- url     : https://prove2.me/theorems/ddc7bd15-de7a-4342-acd4-7e5c700dd360
-- title:
--   The type checker is sound
-- statement:
--   `typeOf m = some ty` implies `HasType m ty`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.typeOf_sound (m : BitcoinMiniscript.Ms) (ty : BitcoinMiniscript.Ty)
    (h : BitcoinMiniscript.typeOf m = some ty) : BitcoinMiniscript.HasType m ty := by sorry
