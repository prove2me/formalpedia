-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div
-- name    : AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/e8a01f4d-c18f-522b-92b3-95166cd55658
-- title:
--   Euler's beta integral int_ℝ(1+x²)^{-(s+1/2)}=Γ_ℝ(2s)/Γ_ℝ(2s+1)
-- statement:
--   Let $s$ be a complex number with $\operatorname{Re} s > 0$. Then the integral over $\mathbb{R}$, with respect to Lebesgue measure, of the function sending a real number $x$ to the complex power $((1+x^2))^{-(s+1/2)}$ — the base being the positive real number $1+x^2$ viewed in $\mathbb{C}$, and the power taken in the sense of `Complex.cpow`, so on the principal branch — equals the quotient $\Gamma_{\mathbb{R}}(2s)/\Gamma_{\mathbb{R}}(2s+1)$, where $\Gamma_{\mathbb{R}}(z) = \pi^{-z/2}\,\Gamma(z/2)$ is Mathlib's real archimedean Gamma factor `Complex.Gammaℝ`. Unwinding the right-hand side, the asserted value is $\pi^{-s}\Gamma(s)\big/\big(\pi^{-(2s+1)/2}\Gamma(s+\tfrac12)\big) = \sqrt{\pi}\,\Gamma(s)/\Gamma(s+\tfrac12)$, that is the beta value $B(s,\tfrac12)$. The integral is the Bochner integral of a $\mathbb{C}$-valued function; integrability of the integrand, which holds precisely because $\operatorname{Re}(s+\tfrac12) > \tfrac12$, is not stated separately but is part of what the identity encodes (for a non-integrable function the Bochner integral would be $0$, whereas the right-hand side is in general non-zero). No continuation of the identity beyond the half-plane $\operatorname{Re} s > 0$ is claimed.
--
--   This is Euler's beta integral $\int_{\mathbb{R}}(1+x^2)^{-a}\,dx = \sqrt{\pi}\,\Gamma(a-\tfrac12)/\Gamma(a)$ with $a = s+\tfrac12$, written in terms of the archimedean Gamma factor so that the answer appears as the ratio $\Gamma_{\mathbb{R}}(2s)/\Gamma_{\mathbb{R}}(2s+1)$ familiar from the spherical local intertwining (Gindikin–Karpelevich) computation for $\mathrm{GL}_2$ at a real place. It is used in the evaluation of the corresponding intertwining integral over the unipotent radical in [`AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal`](thm.html#AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div
    (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) := by sorry
