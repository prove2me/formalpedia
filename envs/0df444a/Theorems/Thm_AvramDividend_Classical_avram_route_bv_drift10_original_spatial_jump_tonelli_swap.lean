-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_jump_tonelli_swap
-- name    : AvramDividend.Classical.avram_route_bv_drift10_original_spatial_jump_tonelli_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:39:45.753862+00:00
-- url     : https://prove2.me/theorems/9819a04e-5833-452d-af63-c7c36caff5b9
-- title:
--   Original BV Lévy jump-loss kernel satisfies the spatial Tonelli swap
-- statement:
--   For the actual original bounded-variation Lévy measure, the spatial jump loss is jointly measurable, nonnegative on positive reserves and negative marks, and has finite product integral. The per-mark reserve integral is bounded by min(epsilon,-z) times the terminal value, and the truncated first moment is Lévy-integrable. These facts justify exchanging the original spatial and negative-mark real integrals without assuming finite jump activity.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_negative_mark_loss_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_each_mark_spatial_loss_le
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift10_original_spatial_jump_tonelli_swap
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
    (∫ y in Ioc (0 : ℝ) ε, (∫ z in Iio (0 : ℝ), w y - w (y + z) ∂X.ν) ∂(volume : Measure ℝ)) =
    (∫ z in Iio (0 : ℝ), (∫ y in Ioc (0 : ℝ) ε, w y - w (y + z) ∂(volume : Measure ℝ)) ∂X.ν) := by sorry
