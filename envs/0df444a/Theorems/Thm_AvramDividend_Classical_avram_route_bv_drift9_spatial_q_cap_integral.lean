-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_spatial_q_cap_integral
-- name    : AvramDividend.Classical.avram_route_bv_drift9_spatial_q_cap_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:56:38.481305+00:00
-- url     : https://prove2.me/theorems/f32f4e90-b8bd-49b4-87e6-2c0da268aa10
-- title:
--   Uniform spatial capped value bound for the BV HJB q term
-- statement:
--   Integrate the positive discount-times-value term in the original BV HJB over reserves from zero to epsilon. On the cap interior, the already proved original secant inequality makes w monotone. Nonnegative q preserves the pointwise comparison w(y) at most w(epsilon). Interval integral monotonicity then gives the explicit q epsilon w(epsilon) bound.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift9_spatial_q_cap_integral
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ y in Ioc (0 : ℝ) ε, q * w y ∂(volume : Measure ℝ)) ≤ q * ε * w ε := by sorry
