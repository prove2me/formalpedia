-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_prop_C_4
-- name    : FoodDeliv.Decentral.prop_C_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:10.716174+00:00
-- url     : https://prove2.me/theorems/50903e9a-53ee-4197-bedb-fc6f3a99b447
-- title:
--   Proposition C.4 (OA pp. 18–19) — the restaurant's optimal price p*, profit Π* and throughput λ*_D + λ*_W
-- statement:
--   Fix $R,\mu,c,\phi,\Lambda_0$ with $\mu>0$, $c>0$, $c<R\mu$, $0<\phi<c$, $\Lambda_0\ge\mu$, and let $\phi_1$, $\lambda_1$, $\lambda_2=\mu-\chi$ and $\chi$ be the thresholds of the model. For $\Lambda_1\in(0,\mu)$ define
--
--   | | $p^*(\Lambda_1)$ | $\Pi^*(\Lambda_1)$ | $\lambda^*_D+\lambda^*_W$ |
--   |---|---|---|---|
--   | $\phi\le\phi_1$, $0<\Lambda_1\le\lambda_1$ | $R-\sqrt{\frac c\mu R}$ | $(\sqrt{R\mu}-\sqrt c)^2$ | $\mu-\sqrt{\frac{c\mu}{R}}$ |
--   | $\phi\le\phi_1$, $\lambda_1<\Lambda_1\le\lambda_2$ | $R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}$ | $\Lambda_1\Big(R-\frac{\mu\phi}{(\mu-\Lambda_1)^2}\Big)$ | $\Lambda_1$ |
--   | $\phi\le\phi_1$, $\Lambda_1>\lambda_2$ | $\frac{2R(\mu-\chi)}{2\mu-\chi}$ | $\frac{2R(\mu-\chi)^2}{2\mu-\chi}$ | $\mu-\chi$ |
--   | $\phi>\phi_1$ | $R-\sqrt{\frac c\mu R}$ | $(\sqrt{R\mu}-\sqrt c)^2$ | $\mu-\sqrt{\frac{c\mu}{R}}$ |
--
--   Then:
--
--   1. For every $\Lambda_1\in(0,\mu)$, every customers' equilibrium response $\sigma$ (for all $p,\theta\ge0$) and every best-response fee rule $\theta(\cdot)$ of the game with tech-savvy rate $\Lambda_1$, the price $p^*(\Lambda_1)$ is an optimal price of the restaurant, its profit there is $\Pi^*(\Lambda_1)$, and the equilibrium throughput there is the table's.
--   2. (i) If $\phi\le\phi_1$: $p^*(a)<p^*(b)$ for all $a\in(0,\lambda_1]$, $b\in(\lambda_1,\mu)$.
--   3. (ii) $\Pi^*$ is weakly increasing in $\Lambda_1$ on $(0,\mu)$.
--   4. (iii) If $\phi<c/(2\sqrt{R\mu/c}-1)$, then $c/(2\sqrt{R\mu/c}-1)\le\phi_1$ and $\mu-\sqrt{c\mu/R}<\lambda_2$.
--
--   This is the first stage of the game, the restaurant's choice as Stackelberg leader, and the source of the jump at $\lambda_1$ in Proposition 1.
--
--   **Formalization Note** The paper's "there exist threshold values $\phi_1,\lambda_1,\lambda_2$" is made explicit with the thresholds the proof constructs (Online Appendix pp. 22–23), shared by Corollaries C.3 and C.4. "The restaurant's optimal price $p^*$" is read as "the table's price is optimal": at $\Lambda_1=\lambda_1$, and when $\phi=\phi_1$ on $(\lambda_1,\mu-\sqrt{c\mu/R}]$, two prices are optimal (findings F1, F2). In (iii) the paper's "$\phi<c/(2\sqrt{R\mu/c}-1)\le\phi_1$" is read with "$\le\phi_1$" as a conclusion. $c<R\mu$ (F4) and $\phi>0$ (F5, F7: at $\phi=0$ the restaurant's profit at $p=R$ depends on the platform's tie-break) are added.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix pp. 18–19, Proposition C.4; thresholds OA pp. 22–23

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

namespace FoodDeliv.Decentral

/-- Proposition C.4 (Restaurant Strategy), Online Appendix pp. 18–19, with the thresholds
`ϕ1 = phi1 R μ c`, `λ1 = lam1 R μ c ϕ`, `λ2 = lam2 R μ ϕ = μ - χ` of Online Appendix pp. 22–23:
for every `Λ1 ∈ (0, μ)` and every customers' equilibrium selection `σ` and best-response fee
rule `fee`, the table's price `p*(Λ1)` is an optimal price of the restaurant, with profit
`Π*(Λ1)` and throughput `λ*_D + λ*_W` as in the table; moreover (i)–(iii). -/
theorem prop_C_4 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) (hΛ0 : μ ≤ Λ0) :
    let ϕ1 := phi1 R μ c
    let l1 := lam1 R μ c ϕ
    let l2 := lam2 R μ ϕ
    let χ := chi R μ ϕ
    -- the table: `p*(Λ1)`, `Π*(Λ1)` and `λ*_D + λ*_W`
    let pT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then R - Real.sqrt (c / μ * R)
          else if Λ1 ≤ l2 then R - μ * ϕ / (μ - Λ1) ^ 2
          else 2 * R * (μ - χ) / (2 * μ - χ))
      else R - Real.sqrt (c / μ * R)
    let VT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2
          else if Λ1 ≤ l2 then Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2)
          else 2 * R * (μ - χ) ^ 2 / (2 * μ - χ))
      else (Real.sqrt (R * μ) - Real.sqrt c) ^ 2
    let TT : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then μ - Real.sqrt (c * μ / R)
          else if Λ1 ≤ l2 then Λ1
          else μ - χ)
      else μ - Real.sqrt (c * μ / R)
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      IsOptPrice σ fee (pT Λ1) ∧ restProfit σ fee (pT Λ1) = VT Λ1 ∧
        (σ (pT Λ1) (fee (pT Λ1))).total = TT Λ1) ∧
    -- (i)
    (ϕ ≤ ϕ1 → ∀ a ∈ Set.Ioc 0 l1, ∀ b ∈ Set.Ioo l1 μ, pT a < pT b) ∧
    -- (ii)
    MonotoneOn VT (Set.Ioo 0 μ) ∧
    -- (iii)
    (ϕ < c / (2 * Real.sqrt (R * μ / c) - 1) →
      c / (2 * Real.sqrt (R * μ / c) - 1) ≤ ϕ1 ∧ μ - Real.sqrt (c * μ / R) < l2) := by sorry

end FoodDeliv.Decentral
