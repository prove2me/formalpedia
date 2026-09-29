-- Prove2me | Theorems.Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
-- name    : Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/650b1238-1f1e-51b2-9645-e3b2b4bae7e1
-- title:
--   Boundedness of a continuous logarithm near a non-zero boundary limit
-- statement:
--   Let $a$ be a real number, let $\Lambda, \ell \colon \mathbb{R} \to \mathbb{C}$ be functions and let $c$ be a complex number. Assume that $\Lambda$ is continuous on the open half-line $(a,\infty)$; that $\exp(\Lambda(s)) = \ell(s)$ for every real $s > a$, so that $\Lambda$ is a pointwise logarithm of $\ell$ to the right of $a$; that $\ell(s) \to c$ as $s \to a$ within $(a,\infty)$, i.e. $\ell$ tends to $c$ along the filter of neighbourhoods of $a$ restricted to $(a,\infty)$; and that $c \neq 0$. The conclusion is the existence of real numbers $C$ and $\delta$ with $\delta > 0$ such that $\|\Lambda(s)\| \le C$ for every real $s$ with $a < s < a + \delta$. No continuity or measurability is assumed of $\ell$ beyond what follows from the exponential identity, and no lower bound on $C$ is asserted: the statement is purely the existence of a bound for $\Lambda$ on some right-hand neighbourhood of $a$.
--
--   This is the elementary fact that a continuous branch of the logarithm of a function with a non-zero one-sided limit remains bounded near the endpoint; the real part $\log|\ell|$ is bounded for trivial reasons, and the content lies in controlling the imaginary part, i.e. the choice of branch. It is used in the analytic estimates for Dedekind zeta functions of cyclotomic fields, being cited by [`NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension`](thm.html#NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension) and [`NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension`](thm.html#NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
    {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by sorry
