-- Prove2me | Theorems.Thm_DeletedPrimes_muS_ne_zero_iff
-- name    : DeletedPrimes.muS_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:03.17265+00:00
-- url     : https://prove2.me/theorems/7bdde12f-6cba-4491-b291-54019e158bcc
-- title:
--   Deleted Primes: mu S ne zero iff
-- statement:
--   The Deleted Primes construction uses the mu S ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L49-L54
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L49-L54

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muS_ne_zero_iff {d : ℕ} :
    muS S d ≠ 0 ↔ Squarefree d ∧ ∀ p ∈ d.primeFactors, p ∈ S := by sorry
