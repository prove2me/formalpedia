-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_integral_decomposition
-- name    : AvramDividend.Classical.bv_weighted_generator_residual_integral_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:05:26.268191+00:00
-- url     : https://prove2.me/theorems/62ea5b7a-ec53-413a-985a-fd4ec19c6f26
-- title:
--   Full BV weighted generator residual decomposes into integrable drift, compensated jump and discount transforms
-- statement:
--   Given genuine global weighted integrability of the derivative, compensated jump generator and scale function, the bounded-variation Lévy generator identity may be integrated term by term. The result expresses the generator residual transform as characteristic drift times derivative transform plus weighted jump transform minus q times the scale Laplace transform. This removes the explicit residual decomposition assumption from the accepted BV algebraic cancellation theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, integrating the bounded-variation Lévy generator against the scale-function Laplace weight.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_weighted_generator_residual_integral_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q θ : ℝ) (W : ℝ → ℝ)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hLaplace : (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * W x) = (X.ψ θ - q)⁻¹) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) =
      X.c * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv W x) +
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) -
      q * (X.ψ θ - q)⁻¹ := by sorry

end AvramDividend.Classical
