-- Prove2me | Theorems.Thm_BellmanIneq_Regret_theorem_5_iterated
-- name    : BellmanIneq.Regret.theorem_5_iterated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:34.785102+00:00
-- url     : https://prove2.me/theorems/d3843b65-bfb2-4fac-a3a4-dd17e49a8f14
-- title:
--   Proof of Theorem 5 — iterated compensation inequality
-- statement:
--   Let a feasible non-anticipative policy have trajectory $S^t$, action $\widehat U^t$, and disagreement event $Q(t,S^t)$. Iterating the compensated one-step inequality gives
--
--   $$\mathbb E[\phi(T,S^T)]\le\mathbb E\!\left[\sum_{t=1}^{T}R(S^t,\xi^t,\widehat U^t)+\sum_{t=1}^{T}\bigl(r\mathbf1_{Q(t,S^t)}+\mathbf1_{Q(t,S^t)^c}L_B(t,S^t)\bigr)\right].$$
--
--   This is the last intermediate estimate before initial ordering replaces $\phi(T,S^T)$ by Offline's value.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, p. 14, Proof of Theorem 5, iterated display

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
Inequalities*, arXiv:1906.06361v2, Proof of Theorem 5, iterated display, p. 14. Iterating the
compensated one-step inequality bounds the initial relaxation by online
rewards plus compensation.
Formalization Note: `S^T = s₀`, and `t` runs from 1 through T. -/
theorem theorem_5_iterated
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (r : ℝ) (hr : @MaxLossBound Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ r)
    (π : Policy Ω S U)
    (hπF : NonAnticipative ξ T π)
    (hπ : Feasible P ξ T π) :
    (∫ ω, ϕ T s₀ ω ∂μ) ≤
      ∫ ω, (∑ t ∈ Finset.Icc 1 T,
          P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω)) +
        (∑ t ∈ Finset.Icc 1 T, (r * (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t).indicator (fun _ => (1 : ℝ)) ω + (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)ᶜ.indicator (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω)) ∂μ := by sorry

end BellmanIneq.Regret
