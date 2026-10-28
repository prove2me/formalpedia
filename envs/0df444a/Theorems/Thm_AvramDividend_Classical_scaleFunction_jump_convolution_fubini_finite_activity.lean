-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_fubini_finite_activity
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_fubini_finite_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:48:11.136331+00:00
-- url     : https://prove2.me/theorems/7a0d83fa-1df2-4d81-8588-5bed4a85b093
-- title:
--   Finite-activity Lévy jump Fubini under weighted product integrability
-- statement:
--   For finite negative-jump Lévy activity, the restricted jump measure is finite. Together with weighted product integrability this proves the valid Fubini exchange of the reserve and Lévy-jump integrals; every negative-jump integral has respect to the Lévy measure.
-- source:
--   Mathlib.MeasureTheory.Integral.Prod.integral_integral_swap; finite restricted-measure typeclass.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_fubini_finite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hint : Integrable (Function.uncurry
      (fun x y : ℝ => Real.exp (-(θ * x)) * W (x + y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) ∂X.ν := by sorry
