-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_cor_C_2
-- name    : FoodDeliv.Decentral.cor_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:09.215141+00:00
-- url     : https://prove2.me/theorems/6f63c191-ea1d-456b-b679-1446d23d9096
-- title:
--   Corollary C.2 (OA p. 18) — the restaurant's profit Π(p) under the platform's best response
-- statement:
--   Consider the model with the standing assumptions and $\phi>0$, a customers' equilibrium response $\sigma$ to every $p\ge0,\theta\ge0$, and a best-response fee rule $\theta(\cdot)$. The restaurant's profit $\Pi(p)=p\,(\lambda_D+\lambda_W)$ at a price $p\ge0$ is:
--
--   1. if $\Lambda_1\le\frac{c-\phi}{c}\mu$:
--   $$\Pi(p)=\begin{cases} p\big(\mu-\frac{c}{R-p}\big) & p\le R-\frac{c}{\mu-\Lambda_1},\\ p\Lambda_1 & R-\frac{c}{\mu-\Lambda_1}<p\le R-\frac{\mu\phi}{(\mu-\Lambda_1)^2},\\ p\Big(\mu-\sqrt{\frac{\mu\phi}{R-p}}\Big) & R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}<p\le R-\frac{\phi}{\mu};\end{cases}$$
--   2. if $\Lambda_1>\frac{c-\phi}{c}\mu$:
--   $$\Pi(p)=\begin{cases} p\big(\mu-\frac{c}{R-p}\big) & p\le R-\frac{c^2}{\mu\phi},\\ p\Big(\mu-\sqrt{\frac{\mu\phi}{R-p}}\Big) & R-\frac{c^2}{\mu\phi}<p\le R-\frac{\phi}{\mu}.\end{cases}$$
--
--   This is the objective of the restaurant, the Stackelberg leader.
--
--   **Formalization Note** The paper's last rows carry no upper bound on $p$; above $R-\phi/\mu$ the formula is negative or undefined while the true profit is $0$ (finding F6), so they are stated for $p\le R-\phi/\mu$, the range of Proposition C.3. $\phi>0$ is added (findings F5, F7). The profit is that of the game, $p$ times the equilibrium throughput under the platform's best response, not a formula.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix p. 18, Corollary C.2

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

namespace FoodDeliv.Decentral

/-- Corollary C.2, Online Appendix p. 18: the restaurant's profit `Π(p) = p (λ_D + λ_W)` at food
price `p ≥ 0` when the platform plays a best-response fee and customers an equilibrium. The
last row of each case is stated for `p ≤ R - ϕ/μ`, the range of Proposition C.3's table. -/
theorem cor_C_2 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ)
    (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ)
    (hσ : ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq P p θ (σ p θ))
    (hfee : ∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) :
    (P.Λ1 ≤ (P.c - P.ϕ) / P.c * P.μ → ∀ p : ℝ, 0 ≤ p →
      (p ≤ P.R - P.c / (P.μ - P.Λ1) →
        restProfit σ fee p = p * (P.μ - P.c / (P.R - p))) ∧
      (P.R - P.c / (P.μ - P.Λ1) < p ∧ p ≤ P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 →
        restProfit σ fee p = p * P.Λ1) ∧
      (P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 < p ∧ p ≤ P.R - P.ϕ / P.μ →
        restProfit σ fee p = p * (P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p))))) ∧
    ((P.c - P.ϕ) / P.c * P.μ < P.Λ1 → ∀ p : ℝ, 0 ≤ p →
      (p ≤ P.R - P.c ^ 2 / (P.μ * P.ϕ) →
        restProfit σ fee p = p * (P.μ - P.c / (P.R - p))) ∧
      (P.R - P.c ^ 2 / (P.μ * P.ϕ) < p ∧ p ≤ P.R - P.ϕ / P.μ →
        restProfit σ fee p = p * (P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p))))) := by sorry

end FoodDeliv.Decentral
