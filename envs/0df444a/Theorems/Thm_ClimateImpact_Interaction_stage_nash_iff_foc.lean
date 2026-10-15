-- Prove2me | Theorems.Thm_ClimateImpact_Interaction_stage_nash_iff_foc
-- name    : ClimateImpact.Interaction.stage_nash_iff_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:17.930225+00:00
-- url     : https://prove2.me/theorems/ab5fac94-9daa-4297-ab2d-2114f273b495
-- title:
--   (40), §6.3, proof of Proposition 4, p. 65 — x is a stage Nash equilibrium iff x^i = ψ^{*,i}_t − (ε/2n)(Σ_j x^j + x^i) for all i
-- statement:
--   Let $n\ge1$, $\rho,T>0$, $0<\alpha<1$, let $\kappa_t,\kappa^c_t>0$ and $c^i_t\ge0$ on $[0,T]$, let $\varepsilon\ge0$ and $t\in[0,T]$. A profile $x\in\mathbb R^n$ is a Nash equilibrium of the date-$t$ stage game with the externalities of Proposition 4 if and only if, for every company $i$,
--   $$x^i=\psi^{*,i}_t-\frac{\varepsilon}{2n}\Big(\sum_{j=1}^n x^j+x^i\Big),$$
--   where $\psi^{*,i}_t$ is the schedule (13) without interaction effect.
--
--   Each company's stage payoff is a strictly concave quadratic in its own emission (the average $\bar x$ contains $x^i$), so equilibria are exactly the solutions of the first-order system (40).
--
--   **Formalization Note** The stage game is played on $\mathbb R^n$ (deviations to any real $z$), as the page's first-order argument requires; see the goal theorem for the domain discussion. Positivity of $\kappa_t,\kappa^c_t$ is Corollary 3's standing assumption, which Proposition 4 inherits through $\psi^{*,i}_t$.
-- source:
--   SSRN 3562534 (25 Jun 2021), §6.3, proof of Proposition 4, (40), p. 65

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Interaction_Game

namespace ClimateImpact.Interaction

theorem stage_nash_iff_foc (n : ℕ) (hn : 0 < n) (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (κ κc κ₀ κc₀ : ℝ → ℝ) (hκ : ∀ t ∈ Set.Icc 0 T, 0 < κ t)
    (hκc : ∀ t ∈ Set.Icc 0 T, 0 < κc t)
    (c : Fin n → ℝ → ℝ) (hc : ∀ i, ∀ t ∈ Set.Icc 0 T, 0 ≤ c i t)
    (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ∀ x : Fin n → ℝ, IsStageNash ρ T α κ κc κ₀ κc₀ c ε t x ↔
      ∀ i, x i = noInt ρ T α κ κc c t i - ε / (2 * n) * (∑ j, x j + x i) := by sorry

end ClimateImpact.Interaction
