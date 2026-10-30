-- Prove2me | Theorems.Thm_BitcoinMiniscript_sem_K_shape
-- name    : BitcoinMiniscript.sem_K_shape
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:24:19.888716+00:00
-- url     : https://prove2.me/theorems/8d819477-8878-497d-8935-5c3598549b09
-- title:
--   K fragments leave a key and a signature
-- statement:
--   For `m : K`, `Sem f o m w out` implies `out = [key, sig]` for some `key`, `sig`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sem_K_shape (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .K) (w out : List BitcoinScript.Bytes)
    (h : BitcoinMiniscript.Sem f o m w out) : ∃ key sig, out = [key, sig] := by sorry
