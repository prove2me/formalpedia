-- Prove2me | Theorems.Thm_BoundedNV_ExpFam_fact13_dA_deta1
-- name    : BoundedNV.ExpFam.fact13_dA_deta1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:31.511439+00:00
-- url     : https://prove2.me/theorems/42d5c195-24ac-46d8-87c4-44f18eb69e77
-- title:
--   Fact (13), p. 575, i = 1 — ∂A/∂η₁ at (p/β, c/β) equals E min(D, X♭)
-- statement:
--   Let $D$ have density $f$, decision domain $S$, and let $0<c<p$, $\beta>0$. Let $X^\flat$ be the behavioral solution, with density $\psi_{p,c}$ of (11), and let $A$ be the log-partition function (12). Then $\eta_1\mapsto A(\eta_1, c/\beta)$ is differentiable at $\eta_1=p/\beta$ and
--   $$\frac{\partial A}{\partial \eta_1}\Big(\frac p\beta,\frac c\beta\Big) = E\,T_1(X^\flat) = \int_{\mathbb R} E\min(D,x)\,\psi_{p,c}(x)\,dx .$$
--
--   This is the case $i=1$ of the exponential-family identity (13), $E\,T_i(X)=\partial A/\partial\eta_i$, for the newsvendor family, with sufficient statistic $T_1(x)=E\min(D,x)$, the expected sales at order $x$.
--
--   **Formalization Note** The derivative is asserted with `HasDerivAt`, which includes differentiability, so the identity cannot hold through Lean's convention that an undefined derivative is $0$. Standing readings $\beta>0$, $c>0$ as in the Observation; no finite mean of $D$ is assumed. The Fact is stated for this family only, not for abstract exponential families.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 575 (PDF p. 10), Fact, eq. (13), i = 1

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
import Definitions.Def_BoundedNV_ExpFam_LogPartition

namespace BoundedNV.ExpFam

theorem fact13_dA_deta1 (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (p c β : ℝ) (hβ : 0 < β) (hc : 0 < c) (hcp : c < p) :
    HasDerivAt (fun t => logPartition f t (c / β))
      (BoundedNV.Uniform.logitExp (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β (BoundedNV.Uniform.expMin f)) (p / β) := by sorry

end BoundedNV.ExpFam
