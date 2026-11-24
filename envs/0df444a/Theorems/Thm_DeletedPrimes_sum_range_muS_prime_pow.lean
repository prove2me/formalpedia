-- Prove2me | Theorems.Thm_DeletedPrimes_sum_range_muS_prime_pow
-- name    : DeletedPrimes.sum_range_muS_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:31.259661+00:00
-- url     : https://prove2.me/theorems/e3135d63-4752-47ff-bc18-c7887af3b182
-- title:
--   Deleted Primes: sum range mu S prime pow
-- statement:
--   The Deleted Primes construction uses the sum range mu S prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L116-L120
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L116-L120

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.sum_range_muS_prime_pow {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, ∑ j ∈ Finset.range (k + 2), muS S (p ^ j) = 1 + muS S p
  := by sorry
