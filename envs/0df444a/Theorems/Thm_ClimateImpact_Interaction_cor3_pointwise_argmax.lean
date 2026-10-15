-- Prove2me | Theorems.Thm_ClimateImpact_Interaction_cor3_pointwise_argmax
-- name    : ClimateImpact.Interaction.cor3_pointwise_argmax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:19.582028+00:00
-- url     : https://prove2.me/theorems/95525318-e80c-4fcf-b7e5-47a7db72eda8
-- title:
--   Corollary 3, p. 20 — with θ(x) = κ₀ − (κ/2)x², ψ^{*,i}_t = c^i_t/(β^c_tκ^c_t + αβ_tκ_t) is the unique maximizer of (12) over x ≥ 0
-- statement:
--   Let $\rho,T>0$, $0<\alpha<1$, let $\kappa_t,\kappa^c_t>0$ and $c^i_t\ge0$ for $t\in[0,T]$, and let $\kappa_{0,t},\kappa^c_{0,t}$ be arbitrary. For every $t\in[0,T]$ and every company $i$, the rate (13)
--   $$\psi^{*,i}_t=\frac{c^i_t}{\beta^c_t\kappa^c_t+\alpha\beta_t\kappa_t}$$
--   is nonnegative, its denominator is positive, and it is the unique maximizer over $x\ge0$ of the date-$t$ payoff (12): for every $x\ge0$ with $x\ne\psi^{*,i}_t$
--   $$\beta^c_t\Big(\kappa^c_{0,t}-\frac{\kappa^c_t}{2}x^2\Big)+\alpha\beta_t\Big(\kappa_{0,t}-\frac{\kappa_t}{2}x^2\Big)+c^i_tx<\beta^c_t\Big(\kappa^c_{0,t}-\frac{\kappa^c_t}{2}(\psi^{*,i}_t)^2\Big)+\alpha\beta_t\Big(\kappa_{0,t}-\frac{\kappa_t}{2}(\psi^{*,i}_t)^2\Big)+c^i_t\psi^{*,i}_t .$$
--
--   With externalities that depend on a company's own emissions only, (12) is a function of $\psi^i_t$ alone, and this is the date-$t$ content of Corollary 3.
--
--   **Formalization Note** $c^i_t\ge0$ is implicit on the page (emissions are nonnegative). Positivity of $\kappa_{0,t},\kappa^c_{0,t}$ (Corollary 3) is not used and is dropped, which makes the statement stronger.
-- source:
--   SSRN 3562534 (25 Jun 2021), Corollary 3, (13), p. 20

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Interaction_Game

namespace ClimateImpact.Interaction

theorem cor3_pointwise_argmax {n : ℕ} (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (κ κc κ₀ κc₀ : ℝ → ℝ) (hκ : ∀ t ∈ Set.Icc 0 T, 0 < κ t)
    (hκc : ∀ t ∈ Set.Icc 0 T, 0 < κc t)
    (c : Fin n → ℝ → ℝ) (hc : ∀ i, ∀ t ∈ Set.Icc 0 T, 0 ≤ c i t)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (i : Fin n) :
    0 ≤ noInt ρ T α κ κc c t i ∧
      0 < betaC ρ T t * κc t + α * beta ρ T t * κ t ∧
      ∀ x : ℝ, 0 ≤ x → x ≠ noInt ρ T α κ κc c t i →
        betaC ρ T t * quadExt (κc₀ t) (κc t) x + α * beta ρ T t * quadExt (κ₀ t) (κ t) x
            + c i t * x
          < betaC ρ T t * quadExt (κc₀ t) (κc t) (noInt ρ T α κ κc c t i)
            + α * beta ρ T t * quadExt (κ₀ t) (κ t) (noInt ρ T α κ κc c t i)
            + c i t * noInt ρ T α κ κc c t i := by sorry

end ClimateImpact.Interaction
