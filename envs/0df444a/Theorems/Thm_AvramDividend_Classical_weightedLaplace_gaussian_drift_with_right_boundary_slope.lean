-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_gaussian_drift_with_right_boundary_slope
-- name    : AvramDividend.Classical.weightedLaplace_gaussian_drift_with_right_boundary_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:43:57.153913+00:00
-- url     : https://prove2.me/theorems/49a02435-8052-4a25-b2be-819beaf7c515
-- title:
--   Gaussian and drift generator transform with the correct one-sided derivative boundary
-- statement:
--   For W with suitable global weighted integrability, differentiability on (0,∞), continuity at zero from the right, and right-hand derivative limit η, the weighted Laplace transform of (σ²/2)W''+cW' equals ((σ²/2)θ²+cθ)L(W)−((σ²/2)θ+c)W(0)−(σ²/2)η. This uses the accepted first derivative boundary transform and newly proved one-sided second derivative transform. Unlike the earlier formula, the boundary term does not assume ordinary deriv W 0 equals η, an invalid assumption for a positive-slope q-scale function extended as zero to negative arguments.
-- source:
--   Proper Gaussian generator integration by parts with one-sided origin slope.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem weightedLaplace_gaussian_drift_with_right_boundary_slope
    (W : ℝ → ℝ) (θ σ c η : ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDlim : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η))
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
       (σ ^ 2 / 2) * η := by sorry

end AvramDividend.Classical
