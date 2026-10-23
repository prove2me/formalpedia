-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_cor_C_3
-- name    : FoodDeliv.Decentral.cor_C_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:21.737732+00:00
-- url     : https://prove2.me/theorems/988d0fcf-0d55-44ee-8d82-d0dbb1a809e4
-- title:
--   Corollary C.3 (OA p. 26) — the platform's equilibrium fee θ*, profit π* and joining rates λ*_D, λ*_W
-- statement:
--   Fix $R,\mu,c,\phi,\Lambda_0$ with $\mu>0$, $c>0$, $c<R\mu$, $0<\phi<c$, $\Lambda_0\ge\mu$, the thresholds $\phi_1,\lambda_1,\lambda_2=\mu-\chi$ of the model, and $p^*(\Lambda_1)$ the price of Proposition C.4's table. Define
--
--   | | $\theta^*(p^*(\Lambda_1))$ | $\pi^*(p^*(\Lambda_1))$ | $\lambda^*_D$ | $\lambda^*_W$ |
--   |---|---|---|---|---|
--   | $\phi\le\phi_1$, $0<\Lambda_1\le\lambda_1$ | $(c-\phi)\sqrt{\frac{R}{\mu c}}$ | $\Lambda_1(c-\phi)\sqrt{\frac{R}{c\mu}}$ | $\Lambda_1$ | $\mu-\sqrt{\frac{c\mu}{R}}-\Lambda_1$ |
--   | $\phi\le\phi_1$, $\lambda_1<\Lambda_1\le\lambda_2$ | $\frac{\phi\Lambda_1}{(\mu-\Lambda_1)^2}$ | $\frac{\phi\Lambda_1^2}{(\mu-\Lambda_1)^2}$ | $\Lambda_1$ | $0$ |
--   | $\phi\le\phi_1$, $\Lambda_1>\lambda_2$ | $\frac{R\chi(\mu-\chi)}{\mu(2\mu-\chi)}$ | $\frac{R\chi(\mu-\chi)^2}{\mu(2\mu-\chi)}$ | $\mu-\chi$ | $0$ |
--   | $\phi>\phi_1$, $0<\Lambda_1\le\mu-\sqrt{\frac{c\mu}{R}}$ | $(c-\phi)\sqrt{\frac{R}{c\mu}}$ | $\Lambda_1(c-\phi)\sqrt{\frac{R}{c\mu}}$ | $\Lambda_1$ | $\mu-\sqrt{\frac{c\mu}{R}}-\Lambda_1$ |
--   | $\phi>\phi_1$, $\Lambda_1>\mu-\sqrt{\frac{c\mu}{R}}$ | $(c-\phi)\sqrt{\frac{R}{c\mu}}$ | $(c-\phi)\Big(\sqrt{\frac{R\mu}{c}}-1\Big)$ | $\mu-\sqrt{\frac{c\mu}{R}}$ | $0$ |
--
--   Then:
--
--   1. For every $\Lambda_1\in(0,\mu)$, every customers' equilibrium response $\sigma$ and every best-response fee rule $\theta(\cdot)$ of the game with tech-savvy rate $\Lambda_1$, the fee at $p^*(\Lambda_1)$ is $\theta^*(p^*(\Lambda_1))$, and the platform's profit and the joining rates there are the table's.
--   2. (i) If $\phi\le\phi_1$, the right limit $L=\lim_{\Lambda_1\searrow\lambda_1}\pi^*(p^*(\Lambda_1))$ exists and $L<\pi^*(p^*(\lambda_1))$.
--   3. (ii) If $\phi>\phi_1$, $\pi^*(p^*(\Lambda_1))$ is weakly increasing in $\Lambda_1$ on $(0,\mu)$.
--
--   It translates the restaurant's choice into the platform's profit, and gives the drop of the platform's profit at the critical mass $\lambda_1$.
--
--   **Formalization Note** The thresholds are those of Proposition C.4 (explicit, Online Appendix pp. 22–23). "$\pi^*|_{\Lambda_1\le\lambda_1}>\pi^*|_{\Lambda_1\searrow\lambda_1}$" compares the value at $\lambda_1$ with the right limit, as the proof does (Online Appendix p. 27), and the limit is asserted to exist. $c<R\mu$ (F4) and $\phi>0$ (F5, F7) are added.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix p. 26, Corollary C.3

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

open Filter Topology

namespace FoodDeliv.Decentral

/-- Corollary C.3 (Food Delivery Platform's Profit), Online Appendix p. 26, with the thresholds
`ϕ1 = phi1 R μ c`, `λ1 = lam1 R μ c ϕ`, `λ2 = lam2 R μ ϕ = μ - χ`: under the restaurant's price
`p*(Λ1)` of Proposition C.4's table, every best-response fee is the table's `θ*`, and the
platform's profit and the joining rates are the table's; moreover (i) the platform's profit at
`Λ1 = λ1` exceeds its right limit at `λ1` when `ϕ ≤ ϕ1`, and (ii) it is weakly increasing in
`Λ1` when `ϕ > ϕ1`. -/
theorem cor_C_3 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    let ϕ1 := phi1 R μ c
    let l1 := lam1 R μ c ϕ
    let l2 := lam2 R μ ϕ
    let χ := chi R μ ϕ
    -- Proposition C.4's equilibrium price `p*(Λ1)`
    let pT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then R - Real.sqrt (c / μ * R)
          else if Λ1 ≤ l2 then R - μ * ϕ / (μ - Λ1) ^ 2
          else 2 * R * (μ - χ) / (2 * μ - χ))
      else R - Real.sqrt (c / μ * R)
    -- the table: `θ*(p*(Λ1))`, `π*(p*(Λ1))`, `λ*_D`, `λ*_W`
    let θT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then (c - ϕ) * Real.sqrt (R / (μ * c))
          else if Λ1 ≤ l2 then ϕ * Λ1 / (μ - Λ1) ^ 2
          else R * χ * (μ - χ) / (μ * (2 * μ - χ)))
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then (c - ϕ) * Real.sqrt (R / (c * μ))
          else (c - ϕ) * Real.sqrt (R / (c * μ)))
    let πT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else if Λ1 ≤ l2 then ϕ * Λ1 ^ 2 / (μ - Λ1) ^ 2
          else R * χ * (μ - χ) ^ 2 / (μ * (2 * μ - χ)))
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else (c - ϕ) * (Real.sqrt (R * μ / c) - 1))
    let DT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then Λ1 else if Λ1 ≤ l2 then Λ1 else μ - χ)
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then Λ1 else μ - Real.sqrt (c * μ / R))
    let WT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then μ - Real.sqrt (c * μ / R) - Λ1 else if Λ1 ≤ l2 then 0 else 0)
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then μ - Real.sqrt (c * μ / R) - Λ1 else 0)
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      fee (pT Λ1) = θT Λ1 ∧ platProfit σ (pT Λ1) (fee (pT Λ1)) = πT Λ1 ∧
        (σ (pT Λ1) (fee (pT Λ1))).lamD = DT Λ1 ∧ (σ (pT Λ1) (fee (pT Λ1))).lamW = WT Λ1) ∧
    -- (i)
    (ϕ ≤ ϕ1 → ∃ L : ℝ, Tendsto πT (𝓝[>] l1) (𝓝 L) ∧ L < πT l1) ∧
    -- (ii)
    (ϕ1 < ϕ → MonotoneOn πT (Set.Ioo 0 μ)) := by sorry

end FoodDeliv.Decentral
