-- Prove2me | Theorems.Thm_FiniteEnergyPlane_le_div_mul_exp_of_deriv_ge
-- name    : FiniteEnergyPlane.le_div_mul_exp_of_deriv_ge
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T22:00:08.541118+00:00
-- url     : https://prove2.me/theorems/2af81236-7fdd-46f0-b94f-07181bdf0773
-- title:
--   One-sided exponential bound for a function tending to zero with exponentially small negative derivative
-- statement:
--   Let $a:\mathbb{R}\to\mathbb{R}$ be differentiable on $(s_0,\infty)$ with derivative $a'$, let $a(s)\to0$ as $s\to+\infty$, and let $K\in\mathbb{R}$, $\beta>0$. If $a'(s)\ge -Ke^{-\beta s}$ for all $s>s_0$, then
--   $$a(s)\le \frac{K}{\beta}\,e^{-\beta s}\qquad\text{for all } s>s_0 .$$
--
--   A basic comparison estimate on a half-line, used to turn exponential bounds on derivatives of quantities that vanish at infinity into exponential bounds on the quantities themselves (for example, $t$-averages of functions on a half-cylinder).
--
--   **Formalization Note** Differentiability is given as `HasDerivAt a (a' s) s` for every `s > s₀`, and the limit as `Tendsto a atTop (𝓝 0)`.
-- source:
--   Elementary real analysis; used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Mathlib

namespace FiniteEnergyPlane

open Set Filter Topology

/-- If `a → 0` at `+∞` and `a' ≥ -K e^{-βs}` on `(s₀, ∞)` with `β > 0`, then
`a s ≤ (K/β) e^{-βs}` for all `s > s₀`. -/
theorem le_div_mul_exp_of_deriv_ge (a a' : ℝ → ℝ) (s₀ K β : ℝ) (hβ : 0 < β)
    (hd : ∀ s > s₀, HasDerivAt a (a' s) s) (ha : Tendsto a atTop (𝓝 0))
    (hineq : ∀ s > s₀, -(K * Real.exp (-(β * s))) ≤ a' s) :
    ∀ s > s₀, a s ≤ K / β * Real.exp (-(β * s)) := by
  sorry

end FiniteEnergyPlane
