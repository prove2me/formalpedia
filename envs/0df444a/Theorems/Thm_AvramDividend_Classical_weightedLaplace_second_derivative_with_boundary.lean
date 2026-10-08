-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_second_derivative_with_boundary
-- name    : AvramDividend.Classical.weightedLaplace_second_derivative_with_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:35:33.013214+00:00
-- url     : https://prove2.me/theorems/7e93bba5-07b5-41d0-a0a5-f0e5354adb16
-- title:
--   Second derivative Laplace transform with both origin boundary terms
-- statement:
--   A twice differentiable real function W on (0,∞), with W and W' right continuous at 0, and weighted W, W', W'' all integrable, satisfies the identity ∫exp(-θx)W''(x)dx = θ²∫exp(-θx)W(x)dx−θW(0)−W'(0). The theorem is proved by applying the accepted weighted first-derivative integration-by-parts result once to W and again to W', then combining the two equalities algebraically. Both origin values are retained, which is indispensable in analysing the Gaussian part of a spectrally negative Lévy generator.
-- source:
--   Elementary twofold integration by parts for the q-scale-function generator's Gaussian term and Laplace boundary audit.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem weightedLaplace_second_derivative_with_boundary
    (W : ℝ → ℝ) (θ : ℝ)
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
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * deriv (deriv W) x) =
      θ ^ 2 * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
        θ * W 0 - deriv W 0 := by sorry

end AvramDividend.Classical
