-- Prove2me | Theorems.Thm_FiniteEnergyPlane_abs_le_exp_of_deriv_ge_abs_sub
-- name    : FiniteEnergyPlane.abs_le_exp_of_deriv_ge_abs_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T22:04:38.967793+00:00
-- url     : https://prove2.me/theorems/b584eed3-3bb5-4dae-a631-1d05f7697069
-- title:
--   Exponential decay for a function tending to zero whose derivative dominates its absolute value up to an exponential error
-- statement:
--   Let $a:\mathbb{R}\to\mathbb{R}$ be differentiable on $(s_0,\infty)$ with derivative $a'$, with $a(s)\to0$ as $s\to+\infty$. Let $K\in\mathbb{R}$ and $\beta>0$, and assume
--   $$a'(s)\ \ge\ |a(s)|-Ke^{-\beta s}\qquad (s>s_0).$$
--   Then there are $\kappa>0$, $C$ and $s_1$ such that $|a(s)|\le Ce^{-\kappa s}$ for all $s\ge s_1$.
--
--   Such differential inequalities arise for action-type functionals of maps on a half-cylinder that are close to holomorphic; the lemma converts them into exponential decay.
--
--   **Formalization Note** Differentiability is `HasDerivAt a (a' s) s` for every `s > s₀`; the limit is `Tendsto a atTop (𝓝 0)`.
-- source:
--   Elementary real analysis; used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Mathlib

namespace FiniteEnergyPlane

open Set Filter Topology

/-- If `a → 0` at `+∞` and `a' ≥ |a| - K e^{-βs}` on `(s₀, ∞)` with `β > 0`, then `|a|` is
bounded by a decaying exponential for large `s`. -/
theorem abs_le_exp_of_deriv_ge_abs_sub (a a' : ℝ → ℝ) (s₀ K β : ℝ) (hβ : 0 < β)
    (hd : ∀ s > s₀, HasDerivAt a (a' s) s) (ha : Tendsto a atTop (𝓝 0))
    (hineq : ∀ s > s₀, |a s| - K * Real.exp (-(β * s)) ≤ a' s) :
    ∃ κ > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, |a s| ≤ C * Real.exp (-(κ * s)) := by
  sorry

end FiniteEnergyPlane
