-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
-- name    : AvramDividend.Classical.avram_limit2_bv_C1_closed_cap_payoff_above_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:10:31.718369+00:00
-- url     : https://prove2.me/theorems/781581e9-7063-4874-bb71-b161b86e9510
-- title:
--   Original BV C1 closed-cap candidate payoff dominates nonnegative reserves
-- statement:
--   For every original nonnegative capped reserve y, the bounded-variation C1 interior slope lower bound and w(0)>=0 force the quantitative inequality y<=w(y), including y=C, y=0 and C=top. The result follows from the previously proved physical closed-cap C1 secant estimate.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_bv_C1_closed_cap_payoff_above_reserve
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → y ≤ w y := by sorry
