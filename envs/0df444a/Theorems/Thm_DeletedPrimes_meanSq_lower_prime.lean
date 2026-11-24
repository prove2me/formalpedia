-- Prove2me | Theorems.Thm_DeletedPrimes_meanSq_lower_prime
-- name    : DeletedPrimes.meanSq_lower_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:57.886814+00:00
-- url     : https://prove2.me/theorems/30e0454e-bc9e-44d2-8c19-35a7f0a41ab9
-- title:
--   Deleted Primes: mean Sq lower prime
-- statement:
--   **Theorem 6(1).** For every `κ < κ_1(α)` and `ε > 0` there are arbitrarily large `X` with
--   `X⁻¹∫_X^{2X} E² ≥ c X^{ακ−ε}`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L107-L165
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L107-L165

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.meanSq_lower_prime {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) {κ ε : ℝ} (hκ0 : 0 < κ) (hκ : κ < kappaOne (dim S)) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ X : ℝ in atTop, c * X ^ (dim S * κ - ε) ≤ meanSq S X := by sorry
