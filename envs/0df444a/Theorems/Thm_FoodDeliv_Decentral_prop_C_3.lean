-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_prop_C_3
-- name    : FoodDeliv.Decentral.prop_C_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:13.19254+00:00
-- url     : https://prove2.me/theorems/635db9a9-46f1-42f6-ab1f-bb7776c013f3
-- title:
--   Proposition C.3 (OA p. 14) — the platform's best-response delivery fee θ*(p) and the resulting joining rates
-- statement:
--   Consider the model with the standing assumptions and $\phi>0$. Let $\sigma$ be a customers' equilibrium response to every $p\ge0$, $\theta\ge0$, and $\theta(\cdot)$ a best-response fee rule for every $p\ge0$. For a price $0\le p$:
--
--   1. If $\Lambda_1\le\frac{c-\phi}{c}\mu$, the fee $\theta^*(p)$ below is a best response, and the joining rates under it are:
--
--   | range of $p$ | $\theta^*(p)$ | $\lambda_D(p,\theta^*(p))$ | $\lambda_W(p,\theta^*(p))$ |
--   |---|---|---|---|
--   | $p\le R-\frac{c}{\mu-\Lambda_1}$ | $\frac{(c-\phi)(R-p)}{c}$ | $\Lambda_1$ | $\mu-\frac{c}{R-p}-\Lambda_1$ |
--   | $R-\frac{c}{\mu-\Lambda_1}<p\le R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}$ | $R-p-\frac{\phi}{\mu-\Lambda_1}$ | $\Lambda_1$ | $0$ |
--   | $R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}<p\le R-\frac{\phi}{\mu}$ | $R-p-\frac{\sqrt{\mu\phi(R-p)}}{\mu}$ | $\mu-\sqrt{\frac{\mu\phi}{R-p}}$ | $0$ |
--
--   2. If $\Lambda_1>\frac{c-\phi}{c}\mu$, likewise with:
--
--   | range of $p$ | $\theta^*(p)$ | $\lambda_D(p,\theta^*(p))$ | $\lambda_W(p,\theta^*(p))$ |
--   |---|---|---|---|
--   | $p\le R-\frac{c}{\mu-\Lambda_1}$ | $\frac{(c-\phi)(R-p)}{c}$ | $\Lambda_1$ | $\mu-\frac{c}{R-p}-\Lambda_1$ |
--   | $R-\frac{c}{\mu-\Lambda_1}<p\le R-\frac{c^2}{\mu\phi}$ | $\frac{(c-\phi)(R-p)}{c}$ | $\mu-\frac{c}{R-p}$ | $0$ |
--   | $R-\frac{c^2}{\mu\phi}<p\le R-\frac{\phi}{\mu}$ | $R-p-\frac{\sqrt{\mu\phi(R-p)}}{\mu}$ | $\mu-\sqrt{\frac{\mu\phi}{R-p}}$ | $0$ |
--
--   Moreover, the platform's profit under its best response, $\pi^*(p)=\theta(p)\,\lambda_D(p,\theta(p))$, is strictly decreasing in $p$ on $[0,R-\phi/\mu]$.
--
--   This is the second stage of the game: the platform's reaction to the restaurant's price.
--
--   **Formalization Note** "The best-response fee $\theta^*(p)$" is read as "the table's fee is a best response": at $p=R-\phi/\mu$ every fee earns $0$, so best responses are not unique there. $\phi>0$ is added (findings F5, F7). Prices are $p\ge0$, as in the game; "decreasing" is read as strictly decreasing on the range of the tables, $[0,R-\phi/\mu]$.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix p. 14, Proposition C.3

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

namespace FoodDeliv.Decentral

/-- Proposition C.3 (Food Delivery Platform Strategy), Online Appendix p. 14: for every food
price `0 ≤ p ≤ R - ϕ/μ` the table's fee `θ*(p)` is a best-response delivery fee, the customers'
equilibrium under it has the table's joining rates, and the platform's optimal profit
`π*(p)` is a decreasing function of `p`. -/
theorem prop_C_3 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ)
    (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ)
    (hσ : ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq P p θ (σ p θ))
    (hfee : ∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) :
    (P.Λ1 ≤ (P.c - P.ϕ) / P.c * P.μ → ∀ p : ℝ, 0 ≤ p →
      (p ≤ P.R - P.c / (P.μ - P.Λ1) →
        IsFeeBR σ p ((P.c - P.ϕ) * (P.R - p) / P.c) ∧
        (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamD = P.Λ1 ∧
        (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamW = P.μ - P.c / (P.R - p) - P.Λ1) ∧
      (P.R - P.c / (P.μ - P.Λ1) < p ∧ p ≤ P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 →
        IsFeeBR σ p (P.R - p - P.ϕ / (P.μ - P.Λ1)) ∧
        (σ p (P.R - p - P.ϕ / (P.μ - P.Λ1))).lamD = P.Λ1 ∧
        (σ p (P.R - p - P.ϕ / (P.μ - P.Λ1))).lamW = 0) ∧
      (P.R - P.μ * P.ϕ / (P.μ - P.Λ1) ^ 2 < p ∧ p ≤ P.R - P.ϕ / P.μ →
        IsFeeBR σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ) ∧
        (σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ)).lamD =
          P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p)) ∧
        (σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ)).lamW = 0)) ∧
    ((P.c - P.ϕ) / P.c * P.μ < P.Λ1 → ∀ p : ℝ, 0 ≤ p →
      (p ≤ P.R - P.c / (P.μ - P.Λ1) →
        IsFeeBR σ p ((P.c - P.ϕ) * (P.R - p) / P.c) ∧
        (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamD = P.Λ1 ∧
        (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamW = P.μ - P.c / (P.R - p) - P.Λ1) ∧
      (P.R - P.c / (P.μ - P.Λ1) < p ∧ p ≤ P.R - P.c ^ 2 / (P.μ * P.ϕ) →
        IsFeeBR σ p ((P.c - P.ϕ) * (P.R - p) / P.c) ∧
        (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamD = P.μ - P.c / (P.R - p) ∧
        (σ p ((P.c - P.ϕ) * (P.R - p) / P.c)).lamW = 0) ∧
      (P.R - P.c ^ 2 / (P.μ * P.ϕ) < p ∧ p ≤ P.R - P.ϕ / P.μ →
        IsFeeBR σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ) ∧
        (σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ)).lamD =
          P.μ - Real.sqrt (P.μ * P.ϕ / (P.R - p)) ∧
        (σ p (P.R - p - Real.sqrt (P.μ * P.ϕ * (P.R - p)) / P.μ)).lamW = 0)) ∧
    StrictAntiOn (fun p => platProfit σ p (fee p)) (Set.Icc 0 (P.R - P.ϕ / P.μ)) := by sorry

end FoodDeliv.Decentral
