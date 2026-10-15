-- Prove2me | Theorems.Thm_ClimateImpact_Interaction_prop4_interaction_equilibrium
-- name    : ClimateImpact.Interaction.prop4_interaction_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:14.342562+00:00
-- url     : https://prove2.me/theorems/47646471-cebc-415a-8b2c-7aecd702c22a
-- title:
--   Proposition 4(i), pp. 29–30 — the stage game with interaction effect has the unique equilibrium (15), and (15) ≤ ψ^{*,i}_t
-- statement:
--   Let $n\ge1$ companies, rate of time preference $\rho>0$, final date $T>0$, green investors' wealth share $0<\alpha<1$, sensitivities $\kappa_t,\kappa^c_t>0$ on $[0,T]$, arbitrary levels $\kappa_{0,t},\kappa^c_{0,t}$, marginal abatement costs $c^i_t\ge0$ on $[0,T]$, and an elasticity parameter $\varepsilon\ge0$. The externalities are
--   $$\theta^i_t(\psi)=\kappa_{0,t}-\frac{\kappa_t}{2}\big[(\psi^i_t)^2+\varepsilon\psi^i_t\bar\psi_t\big],\qquad\theta^{c,i}_t(\psi)=\kappa^c_{0,t}-\frac{\kappa^c_t}{2}\big[(\psi^i_t)^2+\varepsilon\psi^i_t\bar\psi_t\big],$$
--   with $\bar\psi_t=\frac1n\sum_j\psi^j_t$, and each company maximizes the date-$t$ payoff (12) $F_i=\beta^c_t\theta^{c,i}_t+\alpha\beta_t\theta^i_t+c^i_t\psi^i_t$.
--
--   Then for every $t\in[0,T]$:
--
--   1. a profile $x\in\mathbb R^n$ is a Nash equilibrium of the date-$t$ stage game if and only if $x=\psi^{*,\varepsilon}_t$, where
--   $$\psi^{*,\varepsilon,i}_t=\psi^{*,i}_t-\frac{\varepsilon}{2n+\varepsilon}\Big(\psi^{*,i}_t+\frac{2n^2}{2n+(n+1)\varepsilon}\bar\psi^*_t\Big),\tag{15}$$
--   $\psi^{*,i}_t=c^i_t(\beta^c_t\kappa^c_t+\alpha\beta_t\kappa_t)^{-1}$ is Corollary 3's schedule without interaction effect, and $\bar\psi^*_t$ its average;
--   2. companies lower their emissions compared with the case without interaction effect: $\psi^{*,\varepsilon,i}_t\le\psi^{*,i}_t$ for every $i$.
--
--   By Proposition 2, the stage game at each date is the companies' problem; the result says that internalizing the economy's average emissions makes every company emit less.
--
--   **Formalization Note** The stage game is played on $\mathbb R^n$. Schedules are $\mathbb R_+$-valued on the page (footnote 7), but its proof imposes first-order conditions, which characterize equilibria of the unconstrained game, and (15) can be negative (e.g. $c^i_t=0$, $\varepsilon>0$). The companion `prop4_schedule_nash` gives the $\mathbb R_+$ version for a nonnegative (15). Positivity of $\kappa_t,\kappa^c_t$ is Corollary 3's standing assumption (Proposition 4 recalls $\psi^{*,i}_t$ from it); $c^i_t\ge0$ is implicit (the page calls the bracket of (15) positive). The comparison is weak: at $\varepsilon=0$ or $c\equiv0$ it is an equality.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 4(i), (15), pp. 29–30; proof §6.3, pp. 64–65

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Interaction_Game

namespace ClimateImpact.Interaction

theorem prop4_interaction_equilibrium (n : ℕ) (hn : 0 < n) (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (κ κc κ₀ κc₀ : ℝ → ℝ) (hκ : ∀ t ∈ Set.Icc 0 T, 0 < κ t)
    (hκc : ∀ t ∈ Set.Icc 0 T, 0 < κc t)
    (c : Fin n → ℝ → ℝ) (hc : ∀ i, ∀ t ∈ Set.Icc 0 T, 0 ≤ c i t)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ t ∈ Set.Icc 0 T,
      (∀ x : Fin n → ℝ, IsStageNash ρ T α κ κc κ₀ κc₀ c ε t x ↔
          x = interactionRate ρ T α κ κc c ε t) ∧
        ∀ i, interactionRate ρ T α κ κc c ε t i ≤ noInt ρ T α κ κc c t i := by sorry

end ClimateImpact.Interaction
