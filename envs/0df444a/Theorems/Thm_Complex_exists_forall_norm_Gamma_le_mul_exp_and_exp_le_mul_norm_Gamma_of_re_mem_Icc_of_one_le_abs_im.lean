-- Prove2me | Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
-- name    : Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/e820e6f6-16ac-5143-abd3-035156eea834
-- title:
--   Two-sided exponential bounds for Γ on vertical strips
-- statement:
--   Let $\sigma_1,\sigma_2$ be real numbers. Then there exist a real number $A$ and a natural number $N$ such that for every complex number $w$ with $\sigma_1 \le \operatorname{Re} w$, $\operatorname{Re} w \le \sigma_2$ and $1 \le |\operatorname{Im} w|$, both of the following hold for Mathlib's Gamma function `Complex.Gamma`: first, $\|\Gamma(w)\| \le A\,(1+|\operatorname{Im} w|)^N \exp\bigl(-(\pi/2)|\operatorname{Im} w|\bigr)$, and second, $\exp\bigl(-(\pi/2)|\operatorname{Im} w|\bigr) \le A\,(1+|\operatorname{Im} w|)^N \|\Gamma(w)\|$. Thus on the part of the vertical strip $\sigma_1 \le \operatorname{Re} w \le \sigma_2$ at distance at least $1$ from the real axis, $\|\Gamma(w)\|$ is bounded above and below by $\exp(-(\pi/2)|\operatorname{Im} w|)$ up to a factor polynomial in $|\operatorname{Im} w|$, with the constant $A$ and the exponent $N$ depending only on $\sigma_1,\sigma_2$. The lower bound is stated in multiplicative form, with $\|\Gamma(w)\|$ on the right-hand side, so that no division or non-vanishing assertion is needed; the constraint $|\operatorname{Im} w| \ge 1$ keeps $w$ away from the poles of $\Gamma$. If $\sigma_2 < \sigma_1$ the hypotheses are vacuous.
--
--   This is the standard consequence of Stirling's asymptotic formula for $\Gamma$ in a vertical strip: away from the real axis the modulus of $\Gamma$ decays like $e^{-\pi|t|/2}$ up to polynomial factors, and no faster. It is used in the analytic estimates for intertwining operators and their normalisations, where vertical growth bounds for completed $L$-factors and Gamma factors are needed to continue and estimate Weyl intertwining integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
    (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → 1 ≤ |w.im| →
      ‖Complex.Gamma w‖ ≤ A * (1 + |w.im|) ^ N * Real.exp (-(Real.pi / 2) * |w.im|) ∧
        Real.exp (-(Real.pi / 2) * |w.im|) ≤ A * (1 + |w.im|) ^ N * ‖Complex.Gamma w‖ := by sorry
