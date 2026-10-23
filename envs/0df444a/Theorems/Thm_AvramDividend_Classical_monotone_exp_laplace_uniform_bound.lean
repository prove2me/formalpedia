-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_exp_laplace_uniform_bound
-- name    : AvramDividend.Classical.monotone_exp_laplace_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T20:29:00.119778+00:00
-- url     : https://prove2.me/theorems/bf05cef5-445f-48f7-9d47-c45dae41c0fd
-- title:
--   Uniform bound for a monotone nonnegative function from its Laplace envelope
-- statement:
--   Let V be nonnegative and nondecreasing on positive reals, and let A be nonnegative. Assume that for each theta>0 the weighted function exp(-theta*y)*V(y) is integrable over positive reals, and its Laplace integral is at most A/theta. Then V(x) is at most exp(2)*A for all x>0. For x>0 set theta=1/x. On the interval [x,2*x], monotonicity gives V(y)>=V(x), and exp(-theta*y)>=exp(-2). The integral over this interval is at least x*exp(-2)*V(x), while the global Laplace envelope is at most A*x. Cancel the positive x to obtain the uniform bound. This analytic step is useful for the unbounded Esscher-tilted scale bound once monotonicity and the shifted scale Laplace estimate are supplied.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.monotone_exp_laplace_uniform_bound
    (V : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hVnonneg : ∀ x : ℝ, 0 < x → 0 ≤ V x)
    (hmono : MonotoneOn V (Ioi (0 : ℝ)))
    (hLap : ∀ θ : ℝ, 0 < θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * V y) (Ioi 0) volume ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) ≤ A / θ) :
    ∀ x : ℝ, 0 < x → V x ≤ Real.exp 2 * A := by sorry
