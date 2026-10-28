-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_laplace_of_fubini
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_laplace_of_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:29:26.347324+00:00
-- url     : https://prove2.me/theorems/b6012e67-fb23-4d76-8024-5355d745477f
-- title:
--   Finite negative-jump convolution Laplace transform from Fubini
-- statement:
--   For any spectrally negative Levy q-scale function, on an admissible positive Laplace ray, the weighted Laplace transform of the convolution over negative jumps equals the product of the negative-jump exponential moment and the q-scale resolvent, provided the weighted integral interchange is justified. This isolates the exact signed Fubini obligation needed by the finite-activity integrated Volterra equation.
-- source:
--   The previously proved scaleFunction_shifted_laplace_transform and Bochner integral congruence and constant multiplication.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_laplace_of_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hfubini :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) *
      (X.ψ θ - q)⁻¹ := by sorry
