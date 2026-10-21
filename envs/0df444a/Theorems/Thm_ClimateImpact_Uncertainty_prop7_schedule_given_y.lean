-- Prove2me | Theorems.Thm_ClimateImpact_Uncertainty_prop7_schedule_given_y
-- name    : ClimateImpact.Uncertainty.prop7_schedule_given_y
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:41.494684+00:00
-- url     : https://prove2.me/theorems/836d3909-f581-4bf6-9f98-d42a5c983f21
-- title:
--   Proposition 7, p. 37 — for fixed y > 0 the maximizer of (21) is ψ^i_t(y) = c^i_t/(αβ_tκ_t y + β^c_tκ^c_t)
-- statement:
--   Fix a date $t\in[0,T]$ and a value $y>0$ of the uncertainty factor $y_\lambda$. Company $i$ chooses its emission rate $x\ge 0$ to maximize the pointwise objective (21),
--
--   $$
--   F_i(x)=\beta^c_t\,\theta^{c}(x)+\alpha\beta_t\,y\,\theta(x)+c^i_t\,x,
--   $$
--
--   where $\theta^c(x)=\kappa^c_0-\frac{\kappa^c}{2}x^2$ is the companies' externality and $\theta(x)=\kappa_0-\frac{\kappa}{2}x^2$ the green investors' one (Corollary 3). Then:
--
--   1. the denominator $\alpha\beta_t\kappa_t y+\beta^c_t\kappa^c_t$ is positive;
--   2. the rate (22), $\psi^i_t(y)=c^i_t/(\alpha\beta_t\kappa_t y+\beta^c_t\kappa^c_t)$, is nonnegative;
--   3. for every $x\ge 0$ with $x\ne\psi^i_t(y)$,
--   $$
--   F_i(x)<F_i\big(\psi^i_t(y)\big).
--   $$
--
--   So $\psi^i_t(y)$ is the unique optimal emission rate when the company takes $y_\lambda$ as given. This is the decoupling that Proposition 7 obtains from the large-market assumption.
--
--   **Formalization Note** The large-market assumption of Proposition 7 is, by footnote 25, the statement that each company solves (21) for a fixed value of $y_\lambda$. That is what is formalized here, for every $y>0$, at a fixed date $t$. That $y^*_\lambda$ solves (23) is the content of the definition `IsYStar` and of Proposition 8. The standing assumptions $\rho,T>0$, $t\in[0,T]$, $0<\alpha<1$, $\kappa,\kappa^c,\kappa_0,\kappa^c_0>0$ and $c^i\ge0$ are binders.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 7, (21)–(22), p. 37; §6.5, proof of Proposition 7, p. 71

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint
open Matrix

namespace ClimateImpact.Uncertainty

/-- Proposition 7 (SSRN 3562534, p. 37): for a fixed value `y > 0` of `y_λ`, the emission rate
(22) is the unique nonnegative maximizer of the company's pointwise objective (21). -/
theorem prop7_schedule_given_y {n : ℕ} (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ κc₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀) (hκc₀ : 0 < κc₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (y : ℝ) (hy : 0 < y) (i : Fin n) :
    0 < α * ClimateImpact.Interaction.beta ρ T t * κ * y + ClimateImpact.Interaction.betaC ρ T t * κc ∧
    0 ≤ schedule ρ T t α κ κc c y i ∧
    ∀ x : ℝ, 0 ≤ x → x ≠ schedule ρ T t α κ κc c y i →
      ClimateImpact.Interaction.betaC ρ T t * ClimateImpact.Interaction.quadExt κc₀ κc x + α * ClimateImpact.Interaction.beta ρ T t * y * ClimateImpact.Interaction.quadExt κ₀ κ x + c i * x <
        ClimateImpact.Interaction.betaC ρ T t * ClimateImpact.Interaction.quadExt κc₀ κc (schedule ρ T t α κ κc c y i)
          + α * ClimateImpact.Interaction.beta ρ T t * y * ClimateImpact.Interaction.quadExt κ₀ κ (schedule ρ T t α κ κc c y i)
          + c i * schedule ρ T t α κ κc c y i := by sorry

end ClimateImpact.Uncertainty
