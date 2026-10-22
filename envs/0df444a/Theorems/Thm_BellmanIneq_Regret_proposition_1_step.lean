-- Prove2me | Theorems.Thm_BellmanIneq_Regret_proposition_1_step
-- name    : BellmanIneq.Regret.proposition_1_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:36.702632+00:00
-- url     : https://prove2.me/theorems/ac6cbad2-cc0b-40d6-9dea-470d6e2d0c2e
-- title:
--   Proof of Proposition 1 — satisfying-action one-step inequality
-- statement:
--   Let a feasible policy be adapted to Offline's augmented information and choose a satisfying action at each visited state, almost surely. If $S^t$ and $U^t$ are its state and action, then in every decision period,
--
--   $$\phi(t,S^t)\le\mathbb E\left[R(S^t,\xi^t,U^t)+\phi(t-1,S^{t-1})+L_B(t,S^t)\mid\mathcal G_t\right]\quad\text{a.s.}$$
--
--   This is the one-step inequality used to accumulate the Bellman loss in Proposition 1. It identifies the fixed-state continuation in Definition 5 with the continuation of the actual random trajectory.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, p. 12, Proof of Proposition 1, one-step display

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
Inequalities*, arXiv:1906.06361v2, Proof of Proposition 1, one-step display, p. 12. The trajectory action is
satisfying for an augmented-filtration adapted feasible policy.
Formalization Note: `t` is time-to-go in `[1,T]`; the random-state substitution
and identification with the trajectory continuation are the theorem's content. -/
theorem proposition_1_step
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (π : Policy Ω S U)
    (hπG : AugmentedAdapted ξ T Gextra π)
    (hπ : Feasible P ξ T π)
    (hSat : ∀ t ∈ Finset.Icc 1 T,
      ∀ᵐ ω ∂μ, @Satisfying Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB t
        (traj P ξ T π s₀ t ω) (act P ξ T π s₀ t ω) ω) :
    ∀ t ∈ Finset.Icc 1 T,
      (fun ω => ϕ t (traj P ξ T π s₀ t ω) ω) ≤ᵐ[μ]
        μ[fun ω => P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω) + ϕ (t - 1) (traj P ξ T π s₀ (t - 1) ω) ω + LB t (traj P ξ T π s₀ t ω) ω |
          augmented ξ T Gextra t] := by sorry

end BellmanIneq.Regret
