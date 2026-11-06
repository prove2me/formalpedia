-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
-- name    : AvramDividend.Classical.avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:15:41.028061+00:00
-- url     : https://prove2.me/theorems/91f24b4f-e37b-454e-b202-683e1194b926
-- title:
--   Original UBV C2 closed-cap payoff quantitatively dominates reserve
-- statement:
--   The original UBV C2 secant inequality applied between zero and any capped nonnegative reserve y, together with w(0)>=0, yields y<=w(y), valid at C=top and the closed cap boundary. It is deterministic and independent of the stopped Itô source.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → y ≤ w y := by sorry
