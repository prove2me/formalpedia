-- Prove2me | Theorems.Thm_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
-- name    : Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/a801c927-4818-52ba-8f74-e989814f7003
-- title:
--   Logarithmic growth of ψ and archimedean Γ-factors on a half-plane
-- statement:
--   Let $\delta$ be a real number with $\delta > 0$. The assertion is the existence of a real constant $C > 0$ such that for every $s \in \mathbb{C}$ with $\delta \le \operatorname{Re} s$ the three bounds $\|\psi(s)\| \le C \log(2 + \|s\|)$, $\|(\log \Gamma_{\mathbb{R}})'(s)\| \le C \log(2 + \|s\|)$ and $\|(\log \Gamma_{\mathbb{C}})'(s)\| \le C \log(2 + \|s\|)$ hold simultaneously, where $\psi = \Gamma'/\Gamma$ is the digamma function `Complex.digamma`, the second and third expressions are the logarithmic derivatives `logDeriv` of the archimedean Gamma-factors $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ and $\Gamma_{\mathbb{C}}(s) = 2(2\pi)^{-s}\Gamma(s)$, and $\|s\|$ is the complex modulus of $s$. Thus the constant is uniform over the whole closed half-plane $\operatorname{Re} s \ge \delta$, and the majorant involves $\log(2 + \|s\|)$ rather than $\log(2 + |\operatorname{Im} s|)$, so the bound is genuinely unbounded in the real direction as well.
--
--   This is the standard logarithmic growth estimate for the digamma function and for the archimedean local factors at a real and at a complex place, valid uniformly on a closed right half-plane. It is the half-plane form of the corresponding estimate on the vertical strip $\delta \le \operatorname{Re} s \le 2$, and it is used in bounding the derivative along a vertical axis of the analytically continued Weyl intertwining integral, where the archimedean factor at a complex place is evaluated at an argument whose real part grows with the weight.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + ‖s‖) := by sorry
