-- Prove2me | Theorems.Thm_BoundedNV_Stakes_cor2_newsvendor_share
-- name    : BoundedNV.Stakes.cor2_newsvendor_share
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:04:38.252342+00:00
-- url     : https://prove2.me/theorems/988b557c-a1f9-413d-9b5e-a127d4a09ef0
-- title:
--   Corollary 2, p. 580 — a newsvendor with the larger profit share λ₁ > λ₂ earns the higher expected total profit
-- statement:
--   Let demand $D$ have density $f$ ($f\ge0$, $f=0$ on $(-\infty,0)$, $\int f=1$), let $0<c<p$, and let
--   $$\pi(x)=p\,E\min(D,x)-c\,x$$
--   be the supply chain's newsvendor profit on the decision domain $S$, the smallest interval containing the support of $f$. A decision maker with bounded-rationality parameter $\beta>0$ who enjoys the share $\lambda$ of total profits chooses the order $X^\flat$ with logit density proportional to $e^{\lambda\pi(x)/\beta}$ on $S$. If $0<\lambda_2<\lambda_1$ and $X^\flat_i$ is the behavioral solution for share $\lambda_i$, then
--   $$E\pi(X^\flat_1)>E\pi(X^\flat_2).$$
--
--   In particular a retailer who receives only a fraction $\lambda<1$ of the chain's profits, with the same $\beta$, lowers the chain's expected profit relative to a centralised boundedly rational newsvendor: aligning incentives proportionally does not coordinate the chain.
--
--   **Formalization Note** "$\lambda_i$ share of the total profits" is read as $\lambda_i>0$; $\lambda_i>1$ is allowed. $\beta>0$ and $c>0$ are standing readings ($c>0$ is needed for $x^*$ to exist and, on an unbounded $S$, for the logit law to exist). No finite mean of $D$ is assumed and no integrability or non-constancy is assumed: the existence of both logit laws and expected profits, and the non-constancy of $\pi$ on $S$, are part of what is to be proved.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 580 (PDF p. 15), Corollary 2

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit

namespace BoundedNV.Stakes

/-- Corollary 2, p. 580: for the newsvendor profit `π(x) = p E min(D, x) − c x` on the decision
domain `S`, a logit decision maker who receives the share `λ₁` of total profits has strictly higher
expected total profit than one who receives `λ₂ < λ₁` (same `β`). Integrability of the logit laws
and non-constancy of `π` on `S` are part of the claim, not hypotheses. -/
theorem cor2_newsvendor_share (f : ℝ → ℝ) (hf : BoundedNV.ExpFam.IsDemandDensity f)
    (p c β lam₁ lam₂ : ℝ) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β)
    (hlam₂ : 0 < lam₂) (hlam : lam₂ < lam₁) :
    BoundedNV.Uniform.logitExp (BoundedNV.ExpFam.decisionDomain f) (fun x => lam₂ * BoundedNV.Uniform.nvProfit f p c x) β (BoundedNV.Uniform.nvProfit f p c) <
      BoundedNV.Uniform.logitExp (BoundedNV.ExpFam.decisionDomain f) (fun x => lam₁ * BoundedNV.Uniform.nvProfit f p c x) β (BoundedNV.Uniform.nvProfit f p c) := by sorry

end BoundedNV.Stakes
