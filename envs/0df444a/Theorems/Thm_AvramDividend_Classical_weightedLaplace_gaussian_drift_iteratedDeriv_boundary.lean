-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_gaussian_drift_iteratedDeriv_boundary
-- name    : AvramDividend.Classical.weightedLaplace_gaussian_drift_iteratedDeriv_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:12:21.613234+00:00
-- url     : https://prove2.me/theorems/e238bec7-ae4e-48f1-85ba-f174e426b092
-- title:
--   Exact iterated-second-derivative Gaussian generator Laplace transform with origin boundary terms
-- statement:
--   The Laplace transform of the exact Gaussian and drift terms appearing in the Lévy generator, with its `iteratedDeriv 2 W` convention, has boundary corrections `-((σ²/2)θ+c)W(0) -(σ²/2)W'(0)`. It follows from the proved twice-integrated Laplace transform and the proved identification `iteratedDeriv 2 W x = deriv (deriv W) x`. This removes a formal-definition mismatch from the eventual q-harmonic generator transform.
-- source:
--   The accepted weightedLaplace_gaussian_drift_with_boundary and the second iterated derivative convention in pinned Mathlib.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem weightedLaplace_gaussian_drift_iteratedDeriv_boundary
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
         ((σ ^ 2 / 2) * iteratedDeriv 2 W x + c * deriv W x)) =
      ((σ ^ 2 / 2) * θ ^ 2 + c * θ) *
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
       ((σ ^ 2 / 2) * θ + c) * W 0 -
       (σ ^ 2 / 2) * deriv W 0 := by sorry

end AvramDividend.Classical
