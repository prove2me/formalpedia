-- Prove2me | Theorems.Thm_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
-- name    : Complex.norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/4175b3a4-1243-506e-a664-a2dee786cf29
-- title:
--   Landau's lemma on F'/F on a zero-free disc
-- statement:
--   Let $F:\mathbb{C}\to\mathbb{C}$ be a function, $s_0\in\mathbb{C}$ a centre, and $R,M$ real numbers with $R>0$ and $M>0$. Assume: $F$ is complex differentiable on the open ball $\{z:|z-s_0|<R\}$; $F(z)\neq 0$ for every $z$ in that ball; $\|F(z)\|\le e^{M}$ for every $z$ in that ball; and $e^{-M}\le\|F(s_0)\|$. The conclusion is that for every $s$ in the closed ball of radius $R/2$ about $s_0$ both inequalities
--   $$\|F'(s)\|\le \frac{48M}{R}\,\|F(s)\|,\qquad e^{-5M}\le\|F(s)\|$$
--   hold, where $F'$ is the Mathlib derivative `deriv F` and the first bound is stated in the cleared form $\|\operatorname{deriv} F(s)\|\le (48M/R)\cdot\|F(s)\|$ rather than as a bound on the logarithmic derivative. Note that differentiability and the hypotheses on $F$ are assumed only on the open ball of radius $R$, while the conclusion is asserted on the closed ball of radius $R/2$.
--
--   This is Landau's local lemma on the logarithmic derivative in the zero-free case, in the form used to pass from a zero-free region with upper and lower bounds for an $L$-function to a bound on $L'/L$. It is used in the analytic part of the project, in [`NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq`](thm.html#NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
    (F : ℂ → ℂ) (s₀ : ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hd : DifferentiableOn ℂ F (Metric.ball s₀ R))
    (hnz : ∀ z ∈ Metric.ball s₀ R, F z ≠ 0)
    (hup : ∀ z ∈ Metric.ball s₀ R, ‖F z‖ ≤ Real.exp M)
    (hlo : Real.exp (-M) ≤ ‖F s₀‖) :
    ∀ s ∈ Metric.closedBall s₀ (R / 2),
      ‖deriv F s‖ ≤ 48 * M / R * ‖F s‖ ∧ Real.exp (-(5 * M)) ≤ ‖F s‖ := by sorry
