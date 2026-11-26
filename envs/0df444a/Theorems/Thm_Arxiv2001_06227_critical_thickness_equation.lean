-- Prove2me | Theorems.Thm_Arxiv2001_06227_critical_thickness_equation
-- name    : Arxiv2001_06227.critical_thickness_equation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T08:33:56.706784+00:00
-- url     : https://prove2.me/theorems/42653768-a520-51ca-bc22-1ac1a2943ed2
-- title:
--   Eqs. (D4)-(D5): equation for the critical absorption optical thickness $b_{a,c}$
-- statement:
--   Let $p$ be as in (D3), $P_0,\mu_a,L>0$, and let
--
--   $$\langle P_a\rangle(\mu_s)=P_0\,[1-(R+T)(\mu_s)]$$
--
--   with $R+T$ given by the closed form (D3), as a function of $\mu_s$ at fixed $\mu_a$ and $L$. Then $\langle P_a\rangle$ is differentiable at $\mu_s=0$, and the condition (D4), $\partial\langle P_a\rangle/\partial\mu_s|_{\mu_s=0}=0$, holds if and only if $b=\mu_aL=L/\ell_a$ solves (D5):
--
--   $$\int_0^1\Big[\frac{\mu p(-\mu,1)}{1+\mu}\Big\{1-e^{-\frac{b(1+\mu)}{\mu}}\Big\}+\frac{\mu p(\mu,1)}{1-\mu}\Big\{e^{-b}-e^{-b/\mu}\Big\}\Big]d\mu-be^{-b}=0.$$
--
--   **Formalization Note** The derivative is the two-sided derivative of the closed form (D3), taken as a function of $\mu_s$ on a neighbourhood of $0$; this closed form agrees with the paper's $R+T$ wherever $\mu_a+\mu_s>0$, which holds near $\mu_s=0$ because $\mu_a>0$.
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), claim c024; Appendix D, eqs. (D4)-(D5), PDF pp. 12-13

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology

namespace Arxiv2001_06227

theorem critical_thickness_equation (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p)
    (P0 muA L : ℝ) (hP0 : 0 < P0) (hmuA : 0 < muA) (hL : 0 < L) :
    DifferentiableAt ℝ (fun muS => slabAbsorbed p P0 muS muA L) 0 ∧
    (deriv (fun muS => slabAbsorbed p P0 muS muA L) 0 = 0 ↔ criticalLHS p (muA * L) = 0) := by sorry

end Arxiv2001_06227
