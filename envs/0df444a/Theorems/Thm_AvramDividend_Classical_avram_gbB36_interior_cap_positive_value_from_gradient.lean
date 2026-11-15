-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB36_interior_cap_positive_value_from_gradient
-- name    : AvramDividend.Classical.avram_gbB36_interior_cap_positive_value_from_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:25:13.002201+00:00
-- url     : https://prove2.me/theorems/ab36821d-342f-4733-a5dc-29a6e3ea43d1
-- title:
--   Interior finite-cap value is nonnegative from HJB gradient and nonnegative initial value
-- statement:
--   A continuous interior-C2 value function with first derivative at least one on the positive reserve band and nonnegative value at the origin is nonnegative at each b inside the cap. This supplies the upper affine-generator drift estimate for a caplinear test payoff without assuming extra positivity.
-- source:
--   Apply the proved closed-cap gradient secant from zero to b; w(b)>=w(0)+b>=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB36_interior_cap_positive_value_from_gradient
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    0 ≤ w b := by sorry
