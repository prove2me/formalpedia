-- Prove2me | Theorems.Thm_EarlyInspect_Align_proposition_2_tau
-- name    : EarlyInspect.Align.proposition_2_tau
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:26.911479+00:00
-- url     : https://prove2.me/theorems/3320b60f-0a6c-4da3-a12d-864929b28b64
-- title:
--   Proposition 2, p. 63, first part (with the added hypothesis 0 ≤ μ₁ + ẑσ₁) — an inspection time τ ∈ (0,1) solving the inspection equation exists, and there the two expressions for M agree
-- statement:
--   Consider two states of demand, $D_j\sim N(\mu_j,\sigma_j^2)$, $j=1,2$, with $0<\sigma_2<\sigma_1$ and $k_j=\mu_j/\sigma_j$ satisfying $k_2>k_1$. Let $c_o,c_u>0$ and let $\hat z$ satisfy $\Phi(\hat z)=c_u/(c_o+c_u)$, and assume $\mu_1+\hat z\sigma_1\ge0$. Then:
--
--   1. there is a $\tau$ with $0<\tau<1$ such that
--   $$e^{-\frac12\left[\frac{(k_2(1-\tau)+\hat z)^2-(k_1(1-\tau)+\hat z)^2}{\tau}\right]}=\frac{\sigma_2}{\sigma_1};$$
--   2. for every $\tau\in(0,1)$ satisfying this equation,
--   $$\frac{\Phi(\hat z)}{\varphi\!\left(\frac{k_1(1-\tau)+\hat z}{\sqrt\tau}\right)}\sqrt\tau\,\sigma_1=\frac{\Phi(\hat z)}{\varphi\!\left(\frac{k_2(1-\tau)+\hat z}{\sqrt\tau}\right)}\sqrt\tau\,\sigma_2.$$
--
--   This is the first part of Proposition 2: it produces the inspection time and the single penalty $M$ that the principal posts in both states.
--
--   **Formalization Note** The hypothesis $\mu_1+\hat z\sigma_1\ge0$ is added to the page, which states only $\sigma_2<\sigma_1$ and $k_2>k_1$. Without it the statement is false, including in the paper's own case $\mu_1=\mu_2$, $\sigma_1>\sigma_2$: with $\mu_1=\mu_2=0.2$, $\sigma_1=2$, $\sigma_2=1$ and $\hat z=-2$ the bracket equals $(1-\tau)(k_2-k_1)\big((k_1+k_2)(1-\tau)+2\hat z\big)/\tau<0$ on $(0,1)$, so the left side exceeds $1>\sigma_2/\sigma_1$. The hypothesis says that the principal's state-1 target $\mu_1+\hat z\sigma_1$ is a feasible stock level.
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 63 (PDF 10), Proposition 2 (first sentence and the display of M)

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align

theorem proposition_2_tau (co cu μ₁ σ₁ μ₂ σ₂ zhat : ℝ) (hco : 0 < co) (hcu : 0 < cu)
    (hσ₂ : 0 < σ₂) (hσ : σ₂ < σ₁) (hk : μ₁ / σ₁ < μ₂ / σ₂)
    (hzhat : Φ zhat = cu / (co + cu)) (hS : 0 ≤ μ₁ + zhat * σ₁) :
    (∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ inspectionLHS (μ₁ / σ₁) (μ₂ / σ₂) zhat τ = σ₂ / σ₁) ∧
      ∀ τ : ℝ, 0 < τ → τ < 1 → inspectionLHS (μ₁ / σ₁) (μ₂ / σ₂) zhat τ = σ₂ / σ₁ →
        incentiveM μ₁ σ₁ zhat τ = incentiveM μ₂ σ₂ zhat τ := by sorry

end EarlyInspect.Align
