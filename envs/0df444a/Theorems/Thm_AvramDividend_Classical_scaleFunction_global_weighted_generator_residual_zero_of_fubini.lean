-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_generator_residual_zero_of_fubini
-- name    : AvramDividend.Classical.scaleFunction_global_weighted_generator_residual_zero_of_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:37:23.605981+00:00
-- url     : https://prove2.me/theorems/dbb38661-c8b5-4a79-82be-a63d705af695
-- title:
--   The full weighted Lévy-generator residual has zero transform under justified Fubini and origin normalisation
-- statement:
--   Under explicitly stated global weighted integrability of W,W',W'' and the compensated jump generator, right continuity at 0, W(0)=0, Gaussian origin derivative normalisation (σ²/2)W'(0)=1, correct Lévy–Khintchine exponent identity and a valid global Fubini interchange, the weighted Laplace transform of the full Gaussian-drift-plus-compensated-jump generator residual vanishes. The proof combines three previously remotely verified theorems: Gaussian/diffusion derivative-transform with exact origin terms, integrated compensated jump transform, and the exponent/boundary algebraic cancellation. This is conditional on global regularity and Fubini; it does not infer them from C2 on a finite interval, and does not assert pointwise q-harmonicity from a single transform.
-- source:
--   Avram, Palmowski and Pistorius q-scale generator analysis; pinned accepted weighted Gaussian/drift and compensated Lévy transform identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_global_weighted_generator_residual_zero_of_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ σ c : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hzero : W 0 = 0)
    (horigin : (σ ^ 2 / 2) * deriv W 0 = 1)
    (hkernel : IntegrableOn (fun y : ℝ =>
      Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
      (Iio 0) X.ν)
    (hfubini :
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν)
    (hpsi : X.ψ θ =
      (σ ^ 2 / 2) * θ ^ 2 + c * θ +
        (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 -
            θ * (y * (Ioo (-1 : ℝ) 1).indicator
              (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν)) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x +
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
          - q * W x)) = 0 := by sorry

end AvramDividend.Classical
