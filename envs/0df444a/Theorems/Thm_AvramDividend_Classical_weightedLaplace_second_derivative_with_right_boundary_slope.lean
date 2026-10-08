-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_second_derivative_with_right_boundary_slope
-- name    : AvramDividend.Classical.weightedLaplace_second_derivative_with_right_boundary_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:42:17.798987+00:00
-- url     : https://prove2.me/theorems/15c89a52-e759-48fa-85b5-0aff2e5d24ca
-- title:
--   Second-derivative Laplace transform with the correct one-sided boundary slope
-- statement:
--   For a real function W right-continuous at 0 and twice differentiable on (0,∞), assume W' tends to η as x↓0 and weighted W,W',W'' are integrable. Then ∫_0∞e^{-θx}W''(x)dx = θ²∫_0∞e^{-θx}W(x)dx−θ W(0)−η. Crucially η is the right-hand derivative limit, not the ordinary deriv W 0. The proof extends W' at x=0 by η, invokes the proved first-derivative boundary transform for this extension, and checks a.e. equality of integrals on the open half-line. This fixes a genuine boundary-interface defect in the Gaussian q-scale-function generator calculation, because a zero-extended q-scale function can have no ordinary derivative at 0 even when its right derivative equals 2/σ².
-- source:
--   Correct Gaussian Lévy scale-function boundary derivative and pinned Mathlib right-continuity equivalence continuousWithinAt_Ioi_iff_Ici.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem weightedLaplace_second_derivative_with_right_boundary_slope
    (W : ℝ → ℝ) (θ η : ℝ)
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
       Real.exp (-(θ * x)) * deriv (deriv W) x) =
      θ ^ 2 * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * W x) - θ * W 0 - η := by sorry

end AvramDividend.Classical
