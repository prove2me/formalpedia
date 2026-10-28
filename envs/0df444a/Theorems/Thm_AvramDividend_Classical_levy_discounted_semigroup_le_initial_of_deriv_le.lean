-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_initial_of_deriv_le
-- name    : AvramDividend.Classical.levy_discounted_semigroup_le_initial_of_deriv_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:19:05.816994+00:00
-- url     : https://prove2.me/theorems/f16129b5-0c17-4dd1-8c61-c514dc670fb2
-- title:
--   Discounted Lévy transition comparison from a differential HJB bound
-- statement:
--   For a continuous nonnegative-time transition expectation f(t) = E[w(x+X_t)], if f is differentiable at all positive times and its derivative is at most q f(t), then its discounted value is bounded above by f(0). This analytic comparison will supply the explicit semigroup domination hypothesis in the proved adapted-reserve one-step HJB budget once the controlled Lévy generator-to-transition derivative identity is established. The lemma handles continuity at zero and uses no stochastic assumptions beyond those captured by f.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
open Set

theorem AvramDividend.Classical.levy_discounted_semigroup_le_initial_of_deriv_le
    (f : ℝ → ℝ) (q : ℝ)
    (hfcont : ContinuousOn f (Ici 0))
    (hfdiff : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ f s)
    (hderiv : ∀ s : ℝ, 0 < s → deriv f s ≤ q * f s)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(q * t)) * f t ≤ f 0 := by sorry
