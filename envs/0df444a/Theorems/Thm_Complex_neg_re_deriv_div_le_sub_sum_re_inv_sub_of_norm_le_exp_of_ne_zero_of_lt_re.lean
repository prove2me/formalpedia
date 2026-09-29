-- Prove2me | Theorems.Thm_Complex_neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re
-- name    : Complex.neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/c351a155-64b4-56c9-b810-795e2fdc021b
-- title:
--   Landau's lemma on the logarithmic derivative
-- statement:
--   Let $f\colon\mathbb{C}\to\mathbb{C}$, let $s_0\in\mathbb{C}$, and let $r,M\in\mathbb{R}$ with $r>0$. Assume $f$ is analytic on a neighbourhood of each point of the closed disc $\{s:|s-s_0|\le r\}$, that $f(s_0)\ne 0$, and that $\|f(s)\|\le e^{M}\|f(s_0)\|$ for every $s$ in that closed disc. Assume further that $f$ has no zero in the open right half of the concentric disc of half the radius: $f(s)\ne 0$ whenever $|s-s_0|\le r/2$ and $\operatorname{Re}s_0<\operatorname{Re}s$. Finally, let $Z$ be a finite set of complex numbers each of which lies in the closed disc $\{ \rho : |\rho-s_0|\le r/2\}$ and satisfies $f(\rho)=0$. Then
--   $$-\operatorname{Re}\frac{f'(s_0)}{f(s_0)}\;\le\;\frac{8(M+1)}{r}-\sum_{\rho\in Z}\operatorname{Re}\frac{1}{s_0-\rho},$$
--   where $f'$ denotes the derivative of $f$. Note that $Z$ is an arbitrary finite set of such zeros, not the full zero set, and that no multiplicities appear: each $\rho\in Z$ contributes a single term.
--
--   This is Landau's local lemma on the logarithmic derivative, the device by which a purely local growth bound $|f|\le e^{M}|f(s_0)|$ yields an upper bound for $-\operatorname{Re}(f'/f)(s_0)$ with the contribution of nearby zeros subtracted, with no appeal to Hadamard factorisation. It is used here in the derivation of a de la Vallée Poussin type zero-free region, being cited by [`Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg`](thm.html#Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg), where the resulting inequalities at several points are combined with the positivity $3+4\cos\theta+\cos 2\theta\ge 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re
    (f : ℂ → ℂ) (s₀ : ℂ) (r M : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall s₀ r)) (h₀ : f s₀ ≠ 0)
    (hM : ∀ s ∈ Metric.closedBall s₀ r, ‖f s‖ ≤ Real.exp M * ‖f s₀‖)
    (hne : ∀ s ∈ Metric.closedBall s₀ (r / 2), s₀.re < s.re → f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall s₀ (r / 2) ∧ f ρ = 0) :
    -(deriv f s₀ / f s₀).re ≤ 8 * (M + 1) / r - ∑ ρ ∈ Z, ((s₀ - ρ)⁻¹).re := by sorry
