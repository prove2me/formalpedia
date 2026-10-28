-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_volterra_rhs_continuous
-- name    : AvramDividend.Classical.bv_finite_activity_volterra_rhs_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:45:40.399507+00:00
-- url     : https://prove2.me/theorems/e82a6597-27d2-4530-8d36-3e3d674d7c62
-- title:
--   Continuity of both finite-activity scale renewal expressions
-- statement:
--   Under standing BV and finite negative-jump activity, the drift times scale function and its integrated Volterra renewal expression are both continuous on positive reserves. Apply the existing positive-time C1 theorem to scale and finite-jump-convolution primitives, using their proved continuity and local integrability.
-- source:
--   Proved causal_positive_kernel_primitive_contDiff_one, scaleFunction_intervalIntegrable_nonnegative and finite-activity jump-convolution continuity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_volterra_rhs_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ContinuousOn (fun x : ℝ => X.drift * W x) (Ioi (0 : ℝ)) ∧
    ContinuousOn (fun x : ℝ =>
      1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ z in (0 : ℝ)..x, W z) -
      ∫ z in (0 : ℝ)..x,
        (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)) (Ioi (0 : ℝ)) := by sorry
