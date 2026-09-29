-- Prove2me | Theorems.Thm_EthierKurtz_second_deriv_nonneg_of_isLocalMin
-- name    : EthierKurtz.second_deriv_nonneg_of_isLocalMin
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T18:56:52.303431+00:00
-- url     : https://prove2.me/theorems/18c60265-9e17-4726-ad55-05850b45706b
-- title:
--   Second-order necessary condition for a one-variable local minimum
-- statement:
--   This is the one-variable second-order necessary condition for a local minimum.
--
--   Let $g : \mathbb{R} \to \mathbb{R}$ be everywhere differentiable, suppose its derivative $g'$ is differentiable at the origin, and suppose $g$ attains a local minimum at $0$. Then
--
--   $$
--   g''(0) \ge 0.
--   $$
--
--   In words, the second derivative at a interior local minimizer cannot be strictly negative: otherwise the function would lie strictly below its value at the minimizer on one side. This is the converse direction of the usual second-derivative test, and it is the analytic core used to deduce Hessian positive-semidefiniteness at minimizers of several-variable functions by restriction to lines.
--
--   **Formalization Note** Lean's `deriv` is defined to be $0$ where the function is not differentiable, so the hypothesis that `deriv g` is differentiable at $0$ carries real content: it forces $g$ to be differentiable near $0$.
-- source:
--   Second-derivative test, necessary direction: a critical point with negative second derivative is a strict local maximizer, so a local minimizer has nonnegative second derivative. https://en.wikipedia.org/wiki/Derivative_test, Second-derivative test section.

import Mathlib
open scoped Topology

namespace EthierKurtz

theorem second_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ}
    (hdiff : Differentiable ℝ g)
    (hg2 : DifferentiableAt ℝ (deriv g) 0)
    (hmin : IsLocalMin g 0) :
    0 ≤ deriv (deriv g) 0 := by sorry

end EthierKurtz
