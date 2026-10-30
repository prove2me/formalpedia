-- Prove2me | Theorems.Thm_BitcoinMiniscript_goodVal_of_semW
-- name    : BitcoinMiniscript.goodVal_of_semW
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:23:55.905636+00:00
-- url     : https://prove2.me/theorems/890b73d4-8c6c-4901-8b1c-7a9eaa55ff4b
-- title:
--   W fragments leave a valid script number
-- statement:
--   As `goodVal_of_sem` for `m : W`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.goodVal_of_semW (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .W) (w : List BitcoinScript.Bytes) (v : BitcoinScript.Bytes)
    (h : BitcoinMiniscript.Sem f o m w [v]) : BitcoinMiniscript.GoodVal v := by sorry
