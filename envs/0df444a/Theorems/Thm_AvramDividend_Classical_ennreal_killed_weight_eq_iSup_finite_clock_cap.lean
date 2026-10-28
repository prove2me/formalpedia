-- Prove2me | Theorems.Thm_AvramDividend_Classical_ennreal_killed_weight_eq_iSup_finite_clock_cap
-- name    : AvramDividend.Classical.ennreal_killed_weight_eq_iSup_finite_clock_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:56:32.77431+00:00
-- url     : https://prove2.me/theorems/c8d5e403-d258-4b9f-ba81-5354ec5fbea2
-- title:
--   Killed ENNReal reward equals supremum of its finite clock truncations
-- statement:
--   When a nonnegative reward vanishes on paths where its associated extended stopping clock is infinite, the reward is exactly the pointwise supremum of its restrictions to the events T≤n for natural-number horizons n. This is the finite-horizon-to-global identity used to finish the killed first-record expected renewal estimate.
-- source:
--   Pinned Mathlib ENNReal.exists_nat_gt, bounded complete-lattice iSup, and if-case order.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Basic

open scoped ENNReal

theorem AvramDividend.Classical.ennreal_killed_weight_eq_iSup_finite_clock_cap
    {Ω : Type*} (T : Ω → ℝ≥0∞) (weight : Ω → ℝ≥0∞)
    (hzero : ∀ ω, T ω = ⊤ → weight ω = 0) (ω : Ω) :
    (⨆ n : ℕ, if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) = weight ω := by sorry
