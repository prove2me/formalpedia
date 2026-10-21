-- Prove2me | Theorems.Thm_EarlyInspect_Align_newsvendor_optimum
-- name    : EarlyInspect.Align.newsvendor_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:24.128728+00:00
-- url     : https://prove2.me/theorems/0a414c51-1ad9-45fc-b84a-77826b3d24f3
-- title:
--   §4.1.2, pp. 60–61 — the principal's newsvendor cost is minimized exactly at μ + ẑσ, and over S ≥ I exactly at max(I, μ + ẑσ)
-- statement:
--   Let the period demand be $D\sim N(\mu,\sigma^2)$ with $\sigma>0$, let $c_o>0$ be the cost per unit of leftover stock and $c_u>0$ the cost per unit of lost demand, and let the principal's expected cost of the order-up-to level $S$ be
--   $$\mathrm{ETC}(S)=c_o\,\mathbb E\big[(S-D)^+\big]+c_u\,\mathbb E\big[(D-S)^+\big].$$
--   Let $\hat z$ be the critical fractile, $\Phi(\hat z)=\dfrac{c_u}{c_o+c_u}$. Then:
--
--   1. $\mu+\hat z\sigma$ is the unique global minimizer of $\mathrm{ETC}$ on $\mathbb R$;
--   2. for every starting inventory level $I$, the unique minimizer of $\mathrm{ETC}$ over $S\ge I$ is $\max(I,\mu+\hat z\sigma)$:
--   $$\operatorname*{argmin}_{S\ge I}\mathrm{ETC}(S)=\{\max(I,\ \mu+\hat z\sigma)\}.$$
--
--   This is the complete-information benchmark of the paper, the newsvendor solution $S^{p*}=F^{-1}(\alpha)$ with $\alpha=c_u/(c_u+c_o)$, written for normal demand as $\mu+\hat z\sigma$ (§4.2.2). It is the target that the incentive scheme of Proposition 2 makes the agent hit.
--
--   **Formalization Note** The cost is the published `InventoryControl.newsboyCost co cu μ σ`, i.e. eq. (1) with the coefficients of the text (eq. (1) prints $c_u$ and $c_o$ swapped). $\hat z$ is a real number characterized by $\Phi(\hat z)=c_u/(c_o+c_u)$; $\Phi$ is strictly increasing, so it is unique.
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), pp. 60–61 (PDF 7–8), §4.1.2; p. 63 (PDF 10), §4.2.2 (S_j = μ_j + ẑσ_j)

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align

open InventoryControl

theorem newsvendor_optimum (co cu μ σ zhat : ℝ) (hco : 0 < co) (hcu : 0 < cu) (hσ : 0 < σ)
    (hzhat : Φ zhat = cu / (co + cu)) :
    {S : ℝ | ∀ S' : ℝ, newsboyCost co cu μ σ S ≤ newsboyCost co cu μ σ S'} = {μ + zhat * σ} ∧
      ∀ I : ℝ, argminFrom (newsboyCost co cu μ σ) I = {max I (μ + zhat * σ)} := by sorry

end EarlyInspect.Align
