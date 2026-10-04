-- Prove2me | Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
-- name    : AvramDividend.Classical.normalized_derivative_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T12:12:56.528653+00:00
-- url     : https://prove2.me/theorems/e6abedf7-c2d3-45de-b9da-d5e57165e3fe
-- title:
--   Monotonicity of the tilted scale function forces $\phi W(x) \le W'(x)$
-- statement:
--   Suppose the tilted function $g(t) = e^{-\phi t} W(t)$ is monotone on $(0,\infty)$ and $W$ is differentiable at $x>0$. Then $\phi W(x) \le W'(x)$.
--
--   Since $g$ is monotone on the open set $(0,\infty)$, its derivative within that set at $x$ is non-negative, and because the set is open at $x$ that derivative equals the ordinary derivative. Expanding by the product rule gives
--
--   $$g'(x) = e^{-\phi x}\bigl(-\phi W(x) + W'(x)\bigr) \ge 0.$$
--
--   Because $e^{-\phi x} > 0$, the bracket is non-negative, which is exactly the claim. Positivity of the exponential factor is what lets the sign of the derivative be read off the bracket.
--
--   This is the entire analytic content of the bridge `scaleFunction_tilted_positive_monotone`: once a $\phi$ with the stated monotonicity is known, the differential inequality $\phi W \le W'$ follows from elementary calculus alone. The existence of such a $\phi$ for a scale function is the separate stochastic content and is not proved here.
-- source:
--   Kuznetsov, Kyprianou and Rivero, scale-function tilted monotonicity: the measure $dW - \phi W\,dx$ is non-negative for $\phi = \Phi(q)$, which makes $e^{-\phi x}W(x)$ non-decreasing. The differential inequality is then a one-line product-rule consequence, isolated here so that it can be proved independently of the stochastic positivity theorem.

import Mathlib

open Set

namespace AvramDividend.Classical

/-- Normalized monotonicity of the tilted scale function gives a lower bound on
the derivative of the scale function itself. -/
theorem normalized_derivative_lower_bound {W : ℝ → ℝ} (φ x : ℝ)
    (hg : MonotoneOn (fun t : ℝ => Real.exp (-φ * t) * W t) (Ioi 0))
    (hx : 0 < x) (hW : DifferentiableAt ℝ W x) :
    φ * W x ≤ deriv W x := by
  sorry

end AvramDividend.Classical
