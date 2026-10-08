-- Prove2me | Theorems.Thm_BoundedNV_ExpFam_prop2_moments_from_logPartition
-- name    : BoundedNV.ExpFam.prop2_moments_from_logPartition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:39.491854+00:00
-- url     : https://prove2.me/theorems/1c6473c9-5327-42bb-9073-1245403d3668
-- title:
--   Proposition 2, p. 575 — EX♭ = −∂A/∂η₂ and Eπ(X♭) = p ∂A/∂η₁ + c ∂A/∂η₂ at (p/β, c/β)
-- statement:
--   Let the demand $D$ have density $f$ (nonnegative, zero on $(-\infty,0)$, total mass $1$) and let $S$ be the smallest interval containing its support. Let the price $p$ and the cost $c$ satisfy $0<c<p$ and let $\beta>0$. Let $X^\flat$ be the behavioral solution to the newsvendor problem, the random order with density
--   $$\psi_{p,c}(x)=\frac{e^{(pE\min(D,x)-cx)/\beta}}{\int_S e^{(pE\min(D,v)-cv)/\beta}\,dv}\qquad(x\in S),$$
--   so that the natural parameters of the choice distribution are $\eta_1=p/\beta$ and $\eta_2=c/\beta$, and let $A(\eta_1,\eta_2)=\ln\int_S e^{\eta_1E\min(D,v)-\eta_2 v}dv$. Then both partial derivatives of $A$ exist at $(\eta_1,\eta_2)$ and, with $\pi(x)=pE\min(D,x)-cx$,
--   $$EX^\flat = -\frac{\partial A}{\partial\eta_2}(\eta_1,\eta_2),\qquad E\pi(X^\flat) = p\,\frac{\partial A}{\partial\eta_1}(\eta_1,\eta_2) + c\,\frac{\partial A}{\partial\eta_2}(\eta_1,\eta_2).$$
--
--   The function $A$ thus generates the moments of interest of the boundedly rational newsvendor, the expected order and the expected profit, by differentiation instead of integration against the density (11).
--
--   **Formalization Note** The partial derivatives are derivatives of the sections $t\mapsto A(t,\eta_2)$ and $t\mapsto A(\eta_1,t)$; the statement asserts reals $d_1,d_2$ that are these derivatives (`HasDerivAt`, which includes differentiability) and satisfy (14) and (15). Standing readings: $\beta>0$ and $c>0$ are added to the paper's $p>c$; no finite mean of $D$ is assumed and $S$ may be unbounded.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 575 (PDF p. 10), Proposition 2, eqs. (14)–(15)

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
import Definitions.Def_BoundedNV_ExpFam_LogPartition

namespace BoundedNV.ExpFam

theorem prop2_moments_from_logPartition (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (p c β : ℝ) (hβ : 0 < β) (hc : 0 < c) (hcp : c < p) :
    ∃ d₁ d₂ : ℝ,
      HasDerivAt (fun t => logPartition f t (c / β)) d₁ (p / β) ∧
      HasDerivAt (fun t => logPartition f (p / β) t) d₂ (c / β) ∧
      BoundedNV.Uniform.logitExp (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β id = -d₂ ∧
      BoundedNV.Uniform.logitExp (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β (BoundedNV.Uniform.nvProfit f p c) = p * d₁ + c * d₂ := by sorry

end BoundedNV.ExpFam
