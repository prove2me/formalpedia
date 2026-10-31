-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_ennreal_drift_budget_strict_horizon_to_closed
-- name    : AvramDividend.Classical.avram_wave3_03_ennreal_drift_budget_strict_horizon_to_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:30:06.293028+00:00
-- url     : https://prove2.me/theorems/191ddd35-2f16-44d4-9ae0-5ba639951d4b
-- title:
--   Sharp extended-nonnegative drift budget at a closed endpoint from all strict later horizons
-- statement:
--   A nonnegative possibly infinite reward u bounded by capital a plus drift d times every horizon H strictly later than finite T is already bounded by the exact endpoint allowance a+T d, without a horizon slack. The theorem works in extended nonnegative reals and is tailored to the full Stieltjes dividend localisation limit.
-- source:
--   Order continuity from above of NNReal coercions into ENNReal; applies the pinned Mathlib ENNReal.le_of_forall_pos_le_add theorem with a positive dividend allowance epsilon divided by drift plus one.

import Mathlib
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_ennreal_drift_budget_strict_horizon_to_closed
    (a d T : ℝ≥0) (u : ℝ≥0∞)
    (h : ∀ H : ℝ≥0, T < H →
      u ≤ ((a + H * d : ℝ≥0) : ℝ≥0∞)) :
    u ≤ ((a + T * d : ℝ≥0) : ℝ≥0∞) := by sorry
