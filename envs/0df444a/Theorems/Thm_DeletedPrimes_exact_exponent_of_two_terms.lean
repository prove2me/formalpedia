-- Prove2me | Theorems.Thm_DeletedPrimes_exact_exponent_of_two_terms
-- name    : DeletedPrimes.exact_exponent_of_two_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:12:42.877288+00:00
-- url     : https://prove2.me/theorems/aea2b52c-2130-44ac-ab0a-2c36a36720ba
-- title:
--   Deleted Primes: exact exponent of two terms
-- statement:
--   A two-term asymptotic `f(x) = a x + c x^β + O(x^{β'})` with `c ≠ 0` and `β' < β` has exponent exactly `β`:
--   `f(x) − a x = O(x^β)`, and `f(x) − a x` is not `O(x^θ)` for any `θ < β`. This is the "for every `ε > 0` and for no
--   `ε < 0`" step for the integers of `P_β`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L266-L308
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L266-L308

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.exact_exponent_of_two_terms {f : ℝ → ℝ} {a c β β' C : ℝ} (hc : c ≠ 0) (hβ' : β' < β)
    (h : ∀ x : ℝ, 1 ≤ x → |f x - a * x - c * x ^ β| ≤ C * x ^ β') :
    (∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → |f x - a * x| ≤ C' * x ^ β) ∧
    ∀ θ : ℝ, θ < β → ¬ ∃ C' : ℝ, ∀ x : ℝ, 1 ≤ x → |f x - a * x| ≤ C' * x ^ θ := by sorry
