-- Prove2me | Theorems.Thm_BellmanIneq_Regret_theorem_5_compensated_step
-- name    : BellmanIneq.Regret.theorem_5_compensated_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:38.917372+00:00
-- url     : https://prove2.me/theorems/f8c13feb-a973-4c28-abb1-1ff2814b48a1
-- title:
--   Proof of Theorem 5 — compensated one-step inequality
-- statement:
--   For a feasible non-anticipative policy, let $Q(t,S^t)$ mark the periods when its action is not satisfying. If $r$ bounds maximum loss, then the relaxed value at the visited state obeys
--
--   $$\phi(t,S^t)\le\mathbb E\!\left[R(S^t,\xi^t,\widehat U^t)+\phi(t-1,S^{t-1})+r\mathbf1_{Q(t,S^t)}+\mathbf1_{Q(t,S^t)^c}L_B(t,S^t)\mid\mathcal G_t\right]\quad\text{a.s.}$$
--
--   The inequality assigns maximum-loss compensation to a disagreement and Bellman loss to a satisfying action.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, p. 14, Proof of Theorem 5, compensated one-step display

import Definitions.Def_BellmanIneq_Regret_Policy

set_option autoImplicit false

namespace BellmanIneq.Regret

open MeasureTheory

variable {Ω S Ξ U : Type*}
variable [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
variable [mΞ : MeasurableSpace Ξ] [mU : MeasurableSpace U]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]
variable [Countable S] [Fintype U] [Nonempty U]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ)
variable (Gextra : MeasurableSpace Ω) (K : ℝ)
variable (ϕ LB : ℕ → S → Ω → ℝ) (s₀ : S)

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman
Inequalities*, arXiv:1906.06361v2, Proof of Theorem 5, compensated one-step display, p. 14.
The online action can be followed with compensation `r` on disagreement and
Bellman loss on its complement.
Formalization Note: the policy is observed-information adapted; `Q` uses
Definition 5 with the same `LB` as Definition 2. -/
theorem theorem_5_compensated_step
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (r : ℝ) (hr : @MaxLossBound Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ r)
    (π : Policy Ω S U)
    (hπF : NonAnticipative ξ T π)
    (hπ : Feasible P ξ T π) :
    ∀ t ∈ Finset.Icc 1 T,
      (fun ω => ϕ t (traj P ξ T π s₀ t ω) ω) ≤ᵐ[μ]
        μ[fun ω => P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω) + ϕ (t - 1) (traj P ξ T π s₀ (t - 1) ω) ω + (r * (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t).indicator (fun _ => (1 : ℝ)) ω + (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)ᶜ.indicator (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω) |
          augmented ξ T Gextra t] := by sorry

end BellmanIneq.Regret
