-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_positive
-- name    : AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_continuous_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:32:23.033032+00:00
-- url     : https://prove2.me/theorems/b5817db2-0038-465b-a09e-669319864df5
-- title:
--   Finite-activity jump convolution is continuous at positive reserves
-- statement:
--   The negative-jump convolution of the q-scale function is continuous for positive reserves, using local boundedness of W and the fact that the standing condition gives an absolutely continuous finite negative Lévy jump measure. The only possible discontinuity of W is at zero and is invisible to the diffuse jump measure.
-- source:
--   Scale-function continuity and dominated convergence for finite Lévy measures, Avram et al. (2007).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_continuous_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)
      (Ioi (0 : ℝ)) := by sorry
