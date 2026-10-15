-- Prove2me | Theorems.Thm_ClimateImpact_Interaction_prop2_pointwise_optimal
-- name    : ClimateImpact.Interaction.prop2_pointwise_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:02.095978+00:00
-- url     : https://prove2.me/theorems/97b3bc97-09e5-4f30-82e9-7f33bffcf3b1
-- title:
--   Proposition 2, p. 19 — a schedule maximizing the date-t payoff (12) for every t ∈ [0, T] is optimal for J^i
-- statement:
--   Let $\rho>0$, $T>0$, let $c^i$ and $s\mapsto[\Sigma_s\mathbf 1]_i$ be integrable on $[0,T]$, and let $\psi$ be an admissible schedule for company $i$. Suppose that for every $t\in[0,T]$, company $i$'s emission $\psi^i_t$ maximizes the date-$t$ payoff (12)
--   $$\beta^c_t\,\theta^{c,i}_t(\psi_t)+\alpha\beta_t\,\theta^i_t(\psi_t)+c^i_t\psi^i_t$$
--   over all nonnegative values of its own emission, the other companies' emissions $\psi^{-i}_t$ held fixed. Then for every schedule $\chi$ of company $i$ such that the deviated profile $(\chi,\psi^{-i})$ is admissible,
--   $$\mathcal J^i(\chi,\psi^{-i})\le\mathcal J^i(\psi^i,\psi^{-i}).$$
--
--   This is the sufficiency direction of Proposition 2: a company's best response to the others' schedules is obtained date by date from (12).
--
--   **Formalization Note** The page's "is the one that maximizes" also contains a necessity direction (an optimal schedule maximizes (12) for almost every $t$), which is not stated here. $\rho>0$, integrability of the data and admissibility are disclosed standing hypotheses; $\alpha$ is unrestricted.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 2, p. 19; proof §6.2, p. 64

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Interaction_Objective

open MeasureTheory

namespace ClimateImpact.Interaction

theorem prop2_pointwise_optimal {n : ℕ} (ρ T α γstar : ℝ) (hρ : 0 < ρ) (hT : 0 < T)
    (θ θc : ℝ → (Fin n → ℝ) → Fin n → ℝ) (c : Fin n → ℝ → ℝ) (d ψb : Fin n → ℝ)
    (Sig : ℝ → Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (hc_int : IntegrableOn (c i) (Set.Icc 0 T))
    (hSig_int : IntegrableOn (fun s => Matrix.mulVec (Sig s) (fun _ => 1) i) (Set.Icc 0 T))
    (ψ : ℝ → Fin n → ℝ) (hψ : IsAdmissible T θ θc c i ψ)
    (hmax : ∀ t ∈ Set.Icc 0 T, ∀ z : ℝ, 0 ≤ z →
      stage12 ρ T α θ θc c i t (Function.update (ψ t) i z) ≤ stage12 ρ T α θ θc c i t (ψ t)) :
    ∀ χ : ℝ → ℝ, IsAdmissible T θ θc c i (fun s => Function.update (ψ s) i (χ s)) →
      objective ρ T α γstar θ θc c d ψb Sig i (fun s => Function.update (ψ s) i (χ s))
        ≤ objective ρ T α γstar θ θc c d ψb Sig i ψ := by sorry

end ClimateImpact.Interaction
