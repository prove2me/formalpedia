-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_nonnegative
-- name    : AvramDividend.Classical.avram_limit2_bv_C1_closed_cap_payoff_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:05:26.489207+00:00
-- url     : https://prove2.me/theorems/c803e24d-66bb-4df6-8ed4-11d881bec094
-- title:
--   C1 closed-cap candidate nonnegativity from the original two-point secant
-- statement:
--   The original C1 slope condition with nonnegative value at zero forces nonnegative candidate payoff at every nonnegative reserve up to and including the cap, even for the infinite cap, by the proved original-process closed-endpoint two-point secant inequality.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_bv_C1_closed_cap_payoff_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y := by sorry
