-- Prove2me | Theorems.Thm_BellmanIneq_Regret_proposition_1
-- name    : BellmanIneq.Regret.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:34.941435+00:00
-- url     : https://prove2.me/theorems/685876f8-627c-4dab-ab3a-f3e660a7f012
-- title:
--   Proposition 1 — loss of a satisfying augmented policy
-- statement:
--   Let $\phi$ and $L_B$ satisfy the Bellman inequalities. An augmented-information adapted feasible policy whose action is satisfying along its trajectory in every period has expected total reward within the accumulated Bellman loss of Offline's value:
--
--   $$\mathbb E[V(T,S^T)]-\mathbb E\!\left[\sum_{t=1}^{T}R(S^t,\xi^t,U^t)\right]\le\mathbb E\!\left[\sum_{t=1}^{T}L_B(t,S^t)\right].$$
--
--   This bounds the performance gap of a policy that can see Offline's augmented information. It is the benchmark step for the online compensated-coupling argument.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, p. 12, Proposition 1

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
Inequalities*, arXiv:1906.06361v2, Proposition 1, p. 12. Any augmented-information policy that always takes
a satisfying action loses at most the accumulated Bellman loss.
Formalization Note: this policy is `G_t`-adapted, as on the source page; the
horizon sum is `[1,T]`. -/
theorem proposition_1
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (π : Policy Ω S U)
    (hπG : AugmentedAdapted ξ T Gextra π)
    (hπ : Feasible P ξ T π)
    (hSat : ∀ t ∈ Finset.Icc 1 T,
      ∀ᵐ ω ∂μ, @Satisfying Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB t
        (traj P ξ T π s₀ t ω) (act P ξ T π s₀ t ω) ω) :
    (∫ ω, @offlineValue Ω S Ξ U mΩ mΞ μ P ξ T Gextra T s₀ ω ∂μ) -
      @onlineValue Ω S Ξ U mΩ μ P ξ T π s₀ ≤
      ∫ ω, ∑ t ∈ Finset.Icc 1 T, LB t (traj P ξ T π s₀ t ω) ω ∂μ := by sorry

end BellmanIneq.Regret
