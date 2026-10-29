-- Prove2me | Theorems.Thm_FiniteEnergyPlane_le_exp_mul_of_abs_deriv_le
-- name    : FiniteEnergyPlane.le_exp_mul_of_abs_deriv_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T22:40:21.314984+00:00
-- url     : https://prove2.me/theorems/e379ca78-0e68-4cbe-b9d4-51dd78aa739a
-- title:
--   Comparability on unit windows for a nonnegative function with bounded logarithmic derivative
-- statement:
--   Let $F,D:\mathbb{R}\to\mathbb{R}$, $s_0\in\mathbb{R}$ and $\Lambda\ge0$. Suppose that for every $x\ge s_0$, $F$ is differentiable at $x$ with $F'(x)=2D(x)$, $F(x)\ge0$ and $|D(x)|\le\Lambda F(x)$. Then $F(\sigma)\le e^{2\Lambda}F(s)$ for all $s,\sigma\ge s_0$ with $|\sigma-s|\le1$.
--
--   The values of $F$ on any window of length $2$ in $[s_0,\infty)$ are comparable to its value at the centre, with a constant depending only on $\Lambda$.
--
--   **Formalization Note** The derivative is given by `HasDerivAt F (2 * D x) x` for every `x ≥ s₀`.
-- source:
--   Standard; used for C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Lemma 4.8.8

import Mathlib

namespace FiniteEnergyPlane

open Set

/-- If `F' = 2D` and `|D| ≤ Λ F` with `F ≥ 0` on `[s₀, ∞)`, then `F(σ) ≤ e^{2Λ} F(s)` for all
`s, σ ≥ s₀` with `|σ - s| ≤ 1`. -/
theorem le_exp_mul_of_abs_deriv_le (F D : ℝ → ℝ) (s₀ Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hd : ∀ x ≥ s₀, HasDerivAt F (2 * D x) x) (hD : ∀ x ≥ s₀, |D x| ≤ Λ * F x)
    (hF0' : ∀ x ≥ s₀, 0 ≤ F x)
    {s σ : ℝ} (hs : s₀ ≤ s) (hσ : s₀ ≤ σ) (h1 : |σ - s| ≤ 1) :
    F σ ≤ Real.exp (2 * Λ) * F s := by
  sorry

end FiniteEnergyPlane
