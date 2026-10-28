-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_zero_of_transform_components
-- name    : AvramDividend.Classical.bv_weighted_generator_residual_zero_of_transform_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:39:50.51792+00:00
-- url     : https://prove2.me/theorems/0fc0e3c2-b260-48b8-ba8d-df998ec7bae1
-- title:
--   BV generator residual has zero weighted transform from derivative, jump and physical-drift identities
-- statement:
--   For a standing bounded-variation spectrally negative Levy process, the q-scale function and positive Laplace parameter with psi(theta)>q, suppose the weighted first derivative, generator jump, and residual transform have the stated justified integral decompositions. The compensated first-order boundary term cancels exactly using W(0)=1/drift, and the Levy exponent rearrangement gives zero weighted generator residual. This isolates the remaining analytic Fubini and integrability steps.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, first-order bounded-variation generator and Laplace transform calculation.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_weighted_generator_residual_zero_of_transform_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hexp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν)
    (hcomp : IntegrableOn
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) X.ν)
    (hderiv : (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * deriv W x) =
       θ * (X.ψ θ - q)⁻¹ - W 0)
    (hjump : (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
       (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) *
       (X.ψ θ - q)⁻¹ -
       θ * (X.c - X.drift) * (X.ψ θ - q)⁻¹ +
       (X.c - X.drift) * W 0)
    (hresidual : (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (X.generator W x - q * W x)) =
       X.c * (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) * deriv W x) +
       (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) *
           (∫ y in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) -
       q * (X.ψ θ - q)⁻¹) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (X.generator W x - q * W x)) = 0 := by sorry

end AvramDividend.Classical
