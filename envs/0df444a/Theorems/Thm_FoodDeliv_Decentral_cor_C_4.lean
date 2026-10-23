-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_cor_C_4
-- name    : FoodDeliv.Decentral.cor_C_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:09.797813+00:00
-- url     : https://prove2.me/theorems/b3f16108-4047-4e56-a031-dd5cc007c569
-- title:
--   Corollary C.4 (OA p. 28) — social welfare S*(Λ1) in the decentralized equilibrium
-- statement:
--   Fix $R,\mu,c,\phi,\Lambda_0$ with $\mu>0$, $c>0$, $c<R\mu$, $0<\phi<c$, $\Lambda_0\ge\mu$, the thresholds $\phi_1,\lambda_1,\lambda_2=\mu-\chi$ of the model, and $p^*(\Lambda_1)$ the price of Proposition C.4's table. Define
--
--   | | $S^*(\Lambda_1)$ |
--   |---|---|
--   | $\phi\le\phi_1$, $0<\Lambda_1\le\lambda_1$ | $(\sqrt{R\mu}-\sqrt c)^2+\Lambda_1(c-\phi)\sqrt{\frac{R}{c\mu}}$ |
--   | $\phi\le\phi_1$, $\lambda_1<\Lambda_1\le\lambda_2$ | $R\Lambda_1-\frac{\phi\Lambda_1}{\mu-\Lambda_1}$ |
--   | $\phi\le\phi_1$, $\Lambda_1>\lambda_2$ | $\frac{R(2\mu+\chi)(\mu-\chi)^2}{\mu(2\mu-\chi)}$ |
--   | $\phi>\phi_1$, $0<\Lambda_1\le\mu-\sqrt{\frac{c\mu}{R}}$ | $(\sqrt{R\mu}-\sqrt c)^2+\Lambda_1(c-\phi)\sqrt{\frac{R}{c\mu}}$ |
--   | $\phi>\phi_1$, $\Lambda_1>\mu-\sqrt{\frac{c\mu}{R}}$ | $\phi+R\mu-(c+\phi)\sqrt{\frac{R\mu}{c}}$ |
--
--   Then:
--
--   1. For every $\Lambda_1\in(0,\mu)$, every customers' equilibrium response $\sigma$ and every best-response fee rule $\theta(\cdot)$ of the game with tech-savvy rate $\Lambda_1$, social welfare at the price $p^*(\Lambda_1)$ — restaurant profit plus platform profit plus customers' surplus $\lambda_DU_D(\lambda)+\lambda_WU_W(\lambda)$ — equals $S^*(\Lambda_1)$.
--   2. (i) If $\phi\le\phi_1$, the right limit $L=\lim_{\Lambda_1\searrow\lambda_1}S^*(\Lambda_1)$ exists and $L<S^*(\lambda_1)$.
--   3. (ii) If $\phi>\phi_1$, $S^*$ is weakly increasing in $\Lambda_1$ on $(0,\mu)$.
--
--   It shows that social welfare drops when the restaurant switches to the delivery-only regime.
--
--   **Formalization Note** The paper defines welfare here as restaurant plus platform profit and notes that "customers have zero utility in equilibrium" (Online Appendix p. 28); the statement uses the model's welfare, which includes the customers' surplus, so that zero-surplus fact is part of what is asserted. The thresholds are those of Proposition C.4. The jump compares the value at $\lambda_1$ with the right limit, which is asserted to exist. $c<R\mu$ (F4) and $\phi>0$ (F5, F7) are added.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix p. 28, Corollary C.4

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

open Filter Topology

namespace FoodDeliv.Decentral

/-- Corollary C.4 (Social Welfare), Online Appendix p. 28, with the thresholds
`ϕ1 = phi1 R μ c`, `λ1 = lam1 R μ c ϕ`, `λ2 = lam2 R μ ϕ = μ - χ`: under the restaurant's price
`p*(Λ1)` of Proposition C.4's table and the platform's best-response fee, social welfare
(restaurant profit + platform profit + customers' surplus) is the table's `S*(Λ1)`; moreover
(i) `S*` at `Λ1 = λ1` exceeds its right limit at `λ1` when `ϕ ≤ ϕ1`, and (ii) `S*` is weakly
increasing in `Λ1` when `ϕ > ϕ1`. -/
theorem cor_C_4 (R μ c ϕ Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
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
    -- the table: `S*(Λ1)`
    let ST : ℝ → ℝ := fun Λ1 =>
      if ϕ ≤ ϕ1 then
        (if Λ1 ≤ l1 then (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else if Λ1 ≤ l2 then R * Λ1 - ϕ * Λ1 / (μ - Λ1)
          else R * (2 * μ + χ) * (μ - χ) ^ 2 / (μ * (2 * μ - χ)))
      else
        (if Λ1 ≤ μ - Real.sqrt (c * μ / R) then
            (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 + Λ1 * (c - ϕ) * Real.sqrt (R / (c * μ))
          else ϕ + R * μ - (c + ϕ) * Real.sqrt (R * μ / c))
    (∀ Λ1 ∈ Set.Ioo 0 μ, ∀ (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ),
      (∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq ⟨R, μ, c, ϕ, Λ0, Λ1⟩ p θ (σ p θ)) →
      (∀ p : ℝ, 0 ≤ p → IsFeeBR σ p (fee p)) →
      welfare ⟨R, μ, c, ϕ, Λ0, Λ1⟩ σ fee (pT Λ1) = ST Λ1) ∧
    -- (i)
    (ϕ ≤ ϕ1 → ∃ L : ℝ, Tendsto ST (𝓝[>] l1) (𝓝 L) ∧ L < ST l1) ∧
    -- (ii)
    (ϕ1 < ϕ → MonotoneOn ST (Set.Ioo 0 μ)) := by sorry

end FoodDeliv.Decentral
