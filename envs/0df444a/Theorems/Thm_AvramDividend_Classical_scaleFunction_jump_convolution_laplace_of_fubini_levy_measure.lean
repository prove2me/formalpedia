-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_laplace_of_fubini_levy_measure
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_laplace_of_fubini_levy_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:36:43.330179+00:00
-- url     : https://prove2.me/theorems/d984c41d-def4-43a5-a23a-765ff3b185e2
-- title:
--   Lévy-measure jump convolution Laplace factor from Fubini
-- statement:
--   Given the weighted integral interchange with the Lévy measure in both the inner and outer negative-jump integrals, the Laplace transform of the scale jump convolution factors into the Lévy negative-jump exponential moment and the q-scale resolvent. This is the corrected measure-specific statement needed for the finite-activity Volterra identity.
-- source:
--   The proved shifted scale-function Laplace transform; Bochner integral congruence and scalar extraction.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_laplace_of_fubini_levy_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hfubini :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) ∂X.ν) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) *
      (X.ψ θ - q)⁻¹ := by sorry
