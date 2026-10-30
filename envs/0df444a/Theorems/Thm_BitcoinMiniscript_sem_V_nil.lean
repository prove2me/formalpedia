-- Prove2me | Theorems.Thm_BitcoinMiniscript_sem_V_nil
-- name    : BitcoinMiniscript.sem_V_nil
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:24:10.100568+00:00
-- url     : https://prove2.me/theorems/6cac152a-17de-4d15-a8f4-30af0ec78b52
-- title:
--   V fragments leave nothing
-- statement:
--   For `m : V`, `Sem f o m w out` implies `out = []`.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sem_V_nil (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .V) (w out : List BitcoinScript.Bytes)
    (h : BitcoinMiniscript.Sem f o m w out) : out = [] := by sorry
