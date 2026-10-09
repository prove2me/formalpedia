-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_proof_thm21_second_moment
-- name    : DurmusULA.StrongLC.proof_thm21_second_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:54.137981+00:00
-- url     : https://prove2.me/theorems/8a4ee497-6109-4196-81d3-81765205c2a8
-- title:
--   §5.1, p. 34 — under L1 and H3(M_s), ∫‖y − x⋆‖²dπ(y) ≤ d/m + M_s²
-- statement:
--   Let $U:\mathbb R^d\to\mathbb R$ satisfy **L1** and **H3($M_s$)** with constants $L$, $m>0$, $M_s\ge0$, let $x^\star$ be a minimiser of $U$, and let $\pi(dx)\propto e^{-U(x)}dx$. With $W_s(x)=\|x-x^\star\|^2$,
--   $$\int_{\mathbb R^d}W_s(y)\,d\pi(y)\le \frac dm+M_s^2 .$$
--
--   By Cauchy–Schwarz this gives $\int\|y-x^\star\|d\pi(y)\le(d/m+M_s^2)^{1/2}$, the term $2(d/m+M_s^2)^{1/2}$ in the constant $C(\delta_xQ^n_\gamma)$ of Theorem 21. For $U(x)=\frac m2\|x\|^2$ the bound is an equality.
--
--   **Formalization Note** The integral is a lower Lebesgue integral of a nonnegative function, so it cannot take a junk value; $x^\star$ is a bound variable with the hypothesis that it minimises $U$.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 34, §5.1, proof of Theorem 21 (definition of W_s and the bound 'By [32, Theorem 4.3-(ii)] …')

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem proof_thm21_second_moment (d : ℕ) (U : EthierKurtz.SDEState d → ℝ) (L m Ms : ℝ)
    (xstar : EthierKurtz.SDEState d)
    (hL1 : L1 U L) (hH3 : H3 U m Ms) (hxstar : ∀ y, U xstar ≤ U y) :
    ∫⁻ y, ENNReal.ofReal (‖y - xstar‖ ^ 2) ∂(gibbs U) ≤
      ENNReal.ofReal ((d : ℝ) / m + Ms ^ 2) := by sorry

end DurmusULA.StrongLC
