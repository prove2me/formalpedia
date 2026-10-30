-- Prove2me | Theorems.Thm_FiniteEnergyPlane_le_exp_of_deriv_ge_of_lipschitz
-- name    : FiniteEnergyPlane.le_exp_of_deriv_ge_of_lipschitz
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T22:08:48.143487+00:00
-- url     : https://prove2.me/theorems/5115d02f-33e9-4874-96e1-12fbc68d69a3
-- title:
--   Pointwise exponential bound for a Lipschitz function dominated by the derivative of an exponentially small function
-- statement:
--   Let $a,E:\mathbb{R}\to\mathbb{R}$, let $a$ be differentiable on $(s_0,\infty)$ with derivative $a'$, and let $A,M,K\in\mathbb{R}$, $\kappa,\beta>0$. Assume, for all $s,x,y>s_0$,
--   $$|a(s)|\le Ae^{-\kappa s},\qquad |E(x)-E(y)|\le M|x-y|,\qquad E(s)-Ke^{-\beta s}\le a'(s).$$
--   Then there are $\kappa'>0$, $C$ and $s_1$ with $E(s)\le Ce^{-\kappa' s}$ for all $s\ge s_1$.
--
--   It upgrades exponential decay of a quantity $a$ to a pointwise exponential bound on a regular quantity $E$ that $a'$ controls from below, for instance an energy density along a half-cylinder.
--
--   **Formalization Note** No sign condition on $E$ is assumed; the conclusion is an upper bound only.
-- source:
--   Elementary real analysis; used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Mathlib

namespace FiniteEnergyPlane

open Set Filter Topology

/-- If `|a| ≤ A e^{-κs}`, `E` is `M`-Lipschitz and `a' ≥ E - K e^{-βs}` on `(s₀, ∞)` with
`κ, β > 0`, then `E` is bounded above by a decaying exponential for large `s`. -/
theorem le_exp_of_deriv_ge_of_lipschitz (a a' E : ℝ → ℝ) (s₀ A κ M K β : ℝ) (hκ : 0 < κ)
    (hβ : 0 < β) (hd : ∀ s > s₀, HasDerivAt a (a' s) s)
    (ha : ∀ s > s₀, |a s| ≤ A * Real.exp (-(κ * s)))
    (hE : ∀ x > s₀, ∀ y > s₀, |E x - E y| ≤ M * |x - y|)
    (hineq : ∀ s > s₀, E s - K * Real.exp (-(β * s)) ≤ a' s) :
    ∃ κ' > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, E s ≤ C * Real.exp (-(κ' * s)) := by
  sorry

end FiniteEnergyPlane
