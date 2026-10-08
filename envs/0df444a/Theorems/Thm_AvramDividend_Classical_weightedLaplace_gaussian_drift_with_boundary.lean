-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_gaussian_drift_with_boundary
-- name    : AvramDividend.Classical.weightedLaplace_gaussian_drift_with_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:38:03.289054+00:00
-- url     : https://prove2.me/theorems/4b7b73e7-8049-4187-b8fe-da1cb95d6427
-- title:
--   Laplace transform of Gaussian and drift generator terms including both boundary corrections
-- statement:
--   For a function W with sufficient right-continuity, twice differentiability and exponentially weighted integrability, the transform of (σ²/2)W''+cW' equals ((σ²/2)θ²+cθ)L(W) minus ((σ²/2)θ+c)W(0) minus (σ²/2)W'(0). It follows by linearity and the previously proved first- and second-derivative Laplace integration-by-parts formulas. The result identifies exactly the boundary terms from the local Gaussian and drift components of a spectrally negative Lévy generator, preparing the full ψ(θ)-q cancellation calculation.
-- source:
--   Standard Lévy generator Fourier–Laplace calculation with origin boundary terms; required by Avram–Palmowski–Pistorius Lemma 4.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem weightedLaplace_gaussian_drift_with_boundary
    (W : ℝ → ℝ) (θ σ c : ℝ)
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
       Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x)) =
      ((σ ^ 2 / 2) * θ ^ 2 + c * θ) *
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
       ((σ ^ 2 / 2) * θ + c) * W 0 -
       (σ ^ 2 / 2) * deriv W 0 := by sorry

end AvramDividend.Classical
