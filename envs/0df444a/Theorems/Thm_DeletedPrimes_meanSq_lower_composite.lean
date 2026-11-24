-- Prove2me | Theorems.Thm_DeletedPrimes_meanSq_lower_composite
-- name    : DeletedPrimes.meanSq_lower_composite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:58:02.307625+00:00
-- url     : https://prove2.me/theorems/d8d7adb2-875d-46b9-a9a2-f7d5873f3edb
-- title:
--   Deleted Primes: mean Sq lower composite
-- statement:
--   The scales for `k` product blocks: for every `η` below the frame's range, the mean square is
--   `≥ c X^{κ(α−η)}` along arbitrarily large `X`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L213-L326
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L213-L326

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.meanSq_lower_composite {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) {m : ℝ} (hm : 0 < m) (hM : MertensLaw S (dim S) m) {k : ℕ} (hk : 1 ≤ k) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ : κ < kappaK k (dim S)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ c : ℝ, 0 < c ∧ ∃ᶠ X : ℝ in atTop, c * X ^ (κ * (dim S - η)) ≤ meanSq S X := by sorry
