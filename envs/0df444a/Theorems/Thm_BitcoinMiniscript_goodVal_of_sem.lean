-- Prove2me | Theorems.Thm_BitcoinMiniscript_goodVal_of_sem
-- name    : BitcoinMiniscript.goodVal_of_sem
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:23:40.899823+00:00
-- url     : https://prove2.me/theorems/e0015ad5-b4e3-42ec-b694-2e8a7d584205
-- title:
--   B fragments leave a valid script number
-- statement:
--   For `m : B`, `Sem f o m w [v]` implies `GoodVal v`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.goodVal_of_sem (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .B) (w : List BitcoinScript.Bytes) (v : BitcoinScript.Bytes)
    (h : BitcoinMiniscript.Sem f o m w [v]) : BitcoinMiniscript.GoodVal v := by sorry
