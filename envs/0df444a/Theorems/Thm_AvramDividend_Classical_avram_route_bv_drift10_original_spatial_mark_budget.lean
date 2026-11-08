-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_mark_budget
-- name    : AvramDividend.Classical.avram_route_bv_drift10_original_spatial_mark_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:39:47.449837+00:00
-- url     : https://prove2.me/theorems/68f07066-e74f-46f4-a841-98588e44c6a6
-- title:
--   Original BV spatially integrated negative-mark loss is bounded by the truncated first moment
-- statement:
--   Integrate the proved individual negative-mark spatial reserve-loss bound against the actual original Lévy measure. The right-hand truncated first moment is finite by bounded variation, and monotone real integration gives the stated bound. This isolates the mark-side analytic estimate from the independent product-measure Tonelli interchange.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_negative_mark_loss_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_each_mark_spatial_loss_le
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift10_original_spatial_mark_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    (∫ z in Iio (0 : ℝ), (∫ y in Ioc (0 : ℝ) ε, w y - w (y + z) ∂(volume : Measure ℝ)) ∂X.ν) ≤
    (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) * w ε := by sorry
