-- Prove2me | Theorems.Thm_DeletedPrimes_muSFun_apply
-- name    : DeletedPrimes.muSFun_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:44.608975+00:00
-- url     : https://prove2.me/theorems/7a617b51-3c36-4b5c-abb5-f23c8f8f3f79
-- title:
--   Deleted Primes: mu SFun apply
-- statement:
--   The Deleted Primes construction uses the mu SFun apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L83-L83
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L83-L83

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muSFun_apply (n : ℕ) : muSFun S n = muS S n := by sorry
