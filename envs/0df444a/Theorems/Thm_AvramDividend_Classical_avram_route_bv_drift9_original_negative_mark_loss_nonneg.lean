-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_negative_mark_loss_nonneg
-- name    : AvramDividend.Classical.avram_route_bv_drift9_original_negative_mark_loss_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:14:02.498967+00:00
-- url     : https://prove2.me/theorems/2a39ed19-d3f4-4743-9e66-095325dee660
-- title:
--   Negative-jump spatial reserve loss is pointwise nonnegative
-- statement:
--   The original cap-local derivative at least one makes the reserve value candidate monotone on [0,epsilon]. A negative jump reduces the reserve. If it crosses zero, the zero-extension and nonnegativity at the origin yield nonnegative loss; otherwise monotonicity compares values at the before-and-after reserves. This nonnegative real kernel is needed to apply Tonelli to the original Levy measure without finite jump activity.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift9_original_negative_mark_loss_nonneg
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C)
    (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) ε) (z : ℝ) (hz : z < 0) :
    0 ≤ w y - w (y + z) := by sorry
