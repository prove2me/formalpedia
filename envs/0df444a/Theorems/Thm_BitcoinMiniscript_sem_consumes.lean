-- Prove2me | Theorems.Thm_BitcoinMiniscript_sem_consumes
-- name    : BitcoinMiniscript.sem_consumes
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:23:18.331978+00:00
-- url     : https://prove2.me/theorems/1dd2b74f-e335-4be4-a70d-760c1cf8bc91
-- title:
--   The z and o modifiers are respected
-- statement:
--   If `Sem f o m w out` then `props m`'s `z` forces `w = []` and its `o` forces `w` to have one element.
-- source:
--   Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp (https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)

import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sem_consumes (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (w out : List BitcoinScript.Bytes) (h : BitcoinMiniscript.Sem f o m w out) :
    ((BitcoinMiniscript.props m).z = true → w = []) ∧ ((BitcoinMiniscript.props m).o = true → w.length = 1) := by sorry
