-- Prove2me | Theorems.Thm_BoundedNV_ExpFam_eq14_expected_order
-- name    : BoundedNV.ExpFam.eq14_expected_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:42.537954+00:00
-- url     : https://prove2.me/theorems/895daf40-989d-4236-8d51-c050365ab41c
-- title:
--   Proposition 2, eq. (14), p. 575 — the expected behavioral order is −∂A/∂η₂(p/β, c/β)
-- statement:
--   Let $D$ have density $f$, decision domain $S$, and let $0<c<p$, $\beta>0$. Let $X^\flat$ be the behavioral solution, with density $\psi_{p,c}$ of (11), and $A$ the log-partition function (12). Then $\eta_2\mapsto A(p/\beta,\eta_2)$ is differentiable at $\eta_2=c/\beta$ and
--   $$\frac{\partial A}{\partial \eta_2}\Big(\frac p\beta,\frac c\beta\Big) = -E X^\flat = -\int_{\mathbb R} x\,\psi_{p,c}(x)\,dx ,$$
--   that is, $EX^\flat = -\partial A/\partial\eta_2(\eta_1,\eta_2)$, eq. (14).
--
--   This is the case $i=2$ of identity (13), with $T_2(x) = -x$, and gives the expected order quantity of the boundedly rational newsvendor as a derivative of $A$.
--
--   **Formalization Note** Asserted with `HasDerivAt`, so differentiability is part of the claim. Standing readings $\beta>0$, $c>0$; no finite mean of $D$ is assumed, and $S$ may be unbounded.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 575 (PDF p. 10), Fact (13) with i = 2 and Proposition 2, eq. (14)

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
import Definitions.Def_BoundedNV_ExpFam_LogPartition

namespace BoundedNV.ExpFam

theorem eq14_expected_order (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (p c β : ℝ) (hβ : 0 < β) (hc : 0 < c) (hcp : c < p) :
    HasDerivAt (fun t => logPartition f (p / β) t)
      (-(BoundedNV.Uniform.logitExp (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β id)) (c / β) := by sorry

end BoundedNV.ExpFam
