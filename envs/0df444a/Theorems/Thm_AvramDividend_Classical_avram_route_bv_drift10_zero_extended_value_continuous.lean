-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_zero_extended_value_continuous
-- name    : AvramDividend.Classical.avram_route_bv_drift10_zero_extended_value_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:50:13.94119+00:00
-- url     : https://prove2.me/theorems/55ad1cee-efae-4915-87d0-0481b532efe1
-- title:
--   Original zero-extended reserve candidate is globally continuous
-- statement:
--   The candidate is continuous on nonnegative reserves and equals zero to the left of the origin, with value zero at the origin. It is the composite of its nonnegative-domain restriction with the continuous projection x ↦ max(0,x), so is continuous on all real reserves. This supplies joint Borel measurability of the real Lévy jump-loss kernel used in the original BV Tonelli proof.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift10_zero_extended_value_continuous
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ x : ℝ, x < 0 → w x = 0) (hwzero : w 0 = 0) :
    Continuous w := by sorry
