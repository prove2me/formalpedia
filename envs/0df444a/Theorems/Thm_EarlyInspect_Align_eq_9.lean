-- Prove2me | Theorems.Thm_EarlyInspect_Align_eq_9
-- name    : EarlyInspect.Align.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:17.734741+00:00
-- url     : https://prove2.me/theorems/9f2cea11-81d5-4c8a-aa5b-46c15a39640d
-- title:
--   Eq. (9), p. 63 — the derivative of the agent's score (4) at S = μ + zσ is ω(z) = Φ(z) − M/(√tσ) φ((a + z)/√t)
-- statement:
--   Let $D\sim N(\mu,\sigma^2)$ with $\sigma>0$ be the period demand, let $t\in(0,1)$ be the inspection time and $Y_t\sim N(t\mu,t\sigma^2)$ the demand up to time $t$, and let $M\in\mathbb R$. Consider the agent's expected score under scheme $[M,t]$ with $\hat c_o=1$,
--   $$\mathrm{ETPM}_{[Mt]}(S)=\mathbb E\big[(S-D)^+\big]+M\,\mathbb P\{Y_t\ge S\}.$$
--   Write $k=\mu/\sigma$ and $a=k(1-t)$. Then $\mathrm{ETPM}_{[Mt]}$ is differentiable at every $S\in\mathbb R$, and with $z=(S-\mu)/\sigma$,
--   $$\mathrm{ETPM}'_{[Mt]}(S)=\omega(z)=\Phi(z)-\frac{M}{\sqrt t\,\sigma}\,\varphi\!\left(\frac{a+z}{\sqrt t}\right).$$
--
--   This first-order expression is the basis of the agent's analysis: Lemma 1 and Theorem 3 study the shape and the roots of $\omega$, and Proposition 2 chooses $M$ so that $\omega(\hat z)=0$.
--
--   **Formalization Note** The derivative is with respect to the order-up-to level $S$ (not $z$), stated as `HasDerivAt` at every real $S$. The weight $\hat c_o$ is $1$, as in the paper's derivation of (9).
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), pp. 62–63 (PDF 9–10), §4.2.1, eq. (9)

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align

theorem eq_9 (μ σ M t : ℝ) (hσ : 0 < σ) (ht : 0 < t) (ht1 : t < 1) (S : ℝ) :
    HasDerivAt (agentCost μ σ M t) (omega μ σ M t ((S - μ) / σ)) S := by sorry

end EarlyInspect.Align
