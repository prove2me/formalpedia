-- Prove2me | Theorems.Thm_DeletedPrimes_smooth_half_le
-- name    : DeletedPrimes.smooth_half_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:13:13.485606+00:00
-- url     : https://prove2.me/theorems/6a0cb806-f5bb-4322-9a45-2020a1b0b01c
-- title:
--   Deleted Primes: smooth half le
-- statement:
--   **Theorem 5**, last step. `hcount` is the count bound (1.3) proved in §3 for every admissible `θ`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L151-L194
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L151-L194

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.smooth_half_le {S : Set ℕ} {α δ : ℝ} (hδα : δ < α / 2)
    (hcount : ∀ θ σ : ℝ, 0 ≤ θ → IsRegular S θ → max θ δ < σ →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → (intervalCount S X : ℝ) ≤ C * X ^ (2 * σ) * Real.log X ^ 2)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, c * X ^ α / Real.log X ≤ intervalCount S X) :
    α / 2 ≤ theta S := by sorry
