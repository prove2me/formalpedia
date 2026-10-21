-- Prove2me | Theorems.Thm_EarlyInspect_Align_proposition_2
-- name    : EarlyInspect.Align.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:23.64082+00:00
-- url     : https://prove2.me/theorems/7c4a5626-3d21-4286-878a-78e39ff34f84
-- title:
--   Proposition 2, p. 63 — J = 2, σ₂ < σ₁, k₂ > k₁ (and 0 ≤ μ₁ + ẑσ₁): an inspection time τ ∈ (0,1) and one penalty M make both states' agents order exactly the principal's newsvendor level
-- statement:
--   A principal delegates the stocking decision to an agent who knows the state $j\in\{1,2\}$ of demand, $D_j\sim N(\mu_j,\sigma_j^2)$; the demand up to time $t$ is $Y_{t,j}\sim N(t\mu_j,t\sigma_j^2)$. The principal's cost of the order-up-to level $S$ in state $j$ is the newsvendor cost
--   $$\mathrm{ETC}_j(S)=c_o\,\mathbb E[(S-D_j)^+]+c_u\,\mathbb E[(D_j-S)^+],$$
--   and under the scheme $[M,t]$ with $\hat c_o=1$ the agent's expected score is
--   $$\mathrm{ETPM}_j(S)=\mathbb E[(S-D_j)^+]+M\,\mathbb P\{Y_{t,j}\ge S\}.$$
--   Both minimize over $S\ge I$, where $I\ge0$ is the starting inventory.
--
--   Assume $c_o,c_u>0$, $0<\sigma_2<\sigma_1$, $k_2>k_1$ where $k_j=\mu_j/\sigma_j$, let $\hat z$ satisfy $\Phi(\hat z)=c_u/(c_o+c_u)$, and assume $\mu_1+\hat z\sigma_1\ge0$. Then there is a $\tau\in(0,1)$ such that
--
--   1. $e^{-\frac12\left[\frac{(k_2(1-\tau)+\hat z)^2-(k_1(1-\tau)+\hat z)^2}{\tau}\right]}=\dfrac{\sigma_2}{\sigma_1}$;
--   2. $M:=\dfrac{\Phi(\hat z)}{\varphi\left(\frac{k_1(1-\tau)+\hat z}{\sqrt\tau}\right)}\sqrt\tau\,\sigma_1=\dfrac{\Phi(\hat z)}{\varphi\left(\frac{k_2(1-\tau)+\hat z}{\sqrt\tau}\right)}\sqrt\tau\,\sigma_2$;
--   3. under the scheme $[M,t]$ with $\hat c_o=1$, $t=\tau$ and this $M$, for every starting inventory $I\ge0$ and both states $j=1,2$,
--   $$\operatorname*{argmin}_{S\ge I}\mathrm{ETPM}_j(S)=\{\max(I,\ \mu_j+\hat z\sigma_j)\}=\operatorname*{argmin}_{S\ge I}\mathrm{ETC}_j(S).$$
--
--   So a single posted pair $(\tau,M)$ makes the agent choose, in each state, exactly the principal's optimal order-up-to level $\mu_j+\hat z\sigma_j$ (perfect alignment), and when that level is below the starting inventory both choose not to order. Under end-of-period inspection (scheme $[M]$) this is possible only when all $\sigma_j$ are equal (Corollary 1).
--
--   **Formalization Note** The hypothesis $\mu_1+\hat z\sigma_1\ge0$ is added to the page: without it no $\tau$ need exist (e.g. $\mu_1=\mu_2=0.2$, $\sigma_1=2$, $\sigma_2=1$, $\hat z=-2$), and the agent's choice can differ from the principal's when the target level is negative. The agent's and the principal's choices are the sets of minimizers of the two expected costs over $[I,\infty)$, not roots of a first-order condition; the same $M$ (the state-1 expression) is used in both states. The existence of $\tau$ is stated as on the page ("there exists a $\tau$"). §4.2.2's standing assumption $M>\frac{\Phi(-k_j)}{\varphi(-k_j\sqrt t)}\sqrt t\,\sigma_j$ constrains the $(\tau,M)$ that the conclusion constructs and is not assumed; numerically it holds at Proposition 2's $(\tau,M)$.
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 63 (PDF 10), Proposition 2

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

namespace EarlyInspect.Align

open InventoryControl

theorem proposition_2 (co cu μ₁ σ₁ μ₂ σ₂ zhat : ℝ) (hco : 0 < co) (hcu : 0 < cu)
    (hσ₂ : 0 < σ₂) (hσ : σ₂ < σ₁) (hk : μ₁ / σ₁ < μ₂ / σ₂)
    (hzhat : Φ zhat = cu / (co + cu)) (hS : 0 ≤ μ₁ + zhat * σ₁) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
      inspectionLHS (μ₁ / σ₁) (μ₂ / σ₂) zhat τ = σ₂ / σ₁ ∧
      incentiveM μ₁ σ₁ zhat τ = incentiveM μ₂ σ₂ zhat τ ∧
      ∀ I : ℝ, 0 ≤ I →
        argminFrom (agentCost μ₁ σ₁ (incentiveM μ₁ σ₁ zhat τ) τ) I = {max I (μ₁ + zhat * σ₁)} ∧
        argminFrom (agentCost μ₂ σ₂ (incentiveM μ₁ σ₁ zhat τ) τ) I = {max I (μ₂ + zhat * σ₂)} ∧
        argminFrom (newsboyCost co cu μ₁ σ₁) I = {max I (μ₁ + zhat * σ₁)} ∧
        argminFrom (newsboyCost co cu μ₂ σ₂) I = {max I (μ₂ + zhat * σ₂)} := by sorry

end EarlyInspect.Align
