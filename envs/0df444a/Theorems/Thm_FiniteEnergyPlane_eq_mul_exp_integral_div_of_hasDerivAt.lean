-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_mul_exp_integral_div_of_hasDerivAt
-- name    : FiniteEnergyPlane.eq_mul_exp_integral_div_of_hasDerivAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T22:25:41.768818+00:00
-- url     : https://prove2.me/theorems/204bec92-e58d-4c1d-8639-268ae5395288
-- title:
--   A nowhere-vanishing complex path is its initial value times the exponential of the integrated logarithmic derivative
-- statement:
--   Let $X:\mathbb{R}\to\mathbb{C}$ be differentiable with continuous derivative $X'$, and suppose $X(t)\neq0$ for all $t$. Then for every $t\in\mathbb{R}$,
--   $$X(t)=X(0)\,\exp\Big(\int_0^t\frac{X'(s)}{X(s)}\,ds\Big).$$
--
--   A representation of nowhere-vanishing $C^1$ paths in $\mathbb{C}^*$ by an explicit logarithm; its imaginary part is a continuous argument of $X$ with known derivative $\operatorname{Im}(X'/X)$, which is used to compute winding numbers and angle displacements of solutions of linear ODEs.
--
--   **Formalization Note** Differentiability is `∀ t, HasDerivAt X (X' t) t` with `Continuous X'`; the integral is the interval integral `∫ s in (0 : ℝ)..t, X' s / X s`.
-- source:
--   Standard complex analysis on the line; used in C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7.

import Mathlib

namespace FiniteEnergyPlane

/-- A nowhere-vanishing path `X : ℝ → ℂ` with continuous derivative `X'` satisfies
`X t = X 0 · exp (∫₀ᵗ X'/X)` for every `t`. -/
theorem eq_mul_exp_integral_div_of_hasDerivAt {X X' : ℝ → ℂ}
    (hX : ∀ t, HasDerivAt X (X' t) t) (hX' : Continuous X') (h0 : ∀ t, X t ≠ 0) (t : ℝ) :
    X t = X 0 * Complex.exp (∫ s in (0 : ℝ)..t, X' s / X s) := by
  sorry

end FiniteEnergyPlane
