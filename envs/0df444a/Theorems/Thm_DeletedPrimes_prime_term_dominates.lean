-- Prove2me | Theorems.Thm_DeletedPrimes_prime_term_dominates
-- name    : DeletedPrimes.prime_term_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:12:12.912817+00:00
-- url     : https://prove2.me/theorems/7cb773c3-5804-4d73-88ab-aabd72072afa
-- title:
--   Deleted Primes: prime term dominates
-- statement:
--   The prime term: for `β < 1/2 < α` and `x ≥ 1`, `x^β ≤ x^α` and `x^{1/2} ≤ x^α`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L246-L248
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L246-L248

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.prime_term_dominates {α β x : ℝ} (hβ : β < 1 / 2) (hα : 1 / 2 < α) (hx : 1 ≤ x) :
    x ^ β ≤ x ^ α ∧ x ^ (1 / 2 : ℝ) ≤ x ^ α := by sorry
