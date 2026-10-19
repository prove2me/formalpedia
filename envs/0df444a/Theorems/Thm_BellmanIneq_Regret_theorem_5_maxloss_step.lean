-- Prove2me | Theorems.Thm_BellmanIneq_Regret_theorem_5_maxloss_step
-- name    : BellmanIneq.Regret.theorem_5_maxloss_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:35.051874+00:00
-- url     : https://prove2.me/theorems/d5bfb469-1657-412f-b81a-2cf9b51c5e40
-- title:
--   Proof of Theorem 5 — maximum-loss step
-- statement:
--   Let a feasible non-anticipative policy take action $\widehat U^t$ at state $S^t$. On the event $Q(t,S^t)$ where that action is not satisfying, the maximum-loss bound $r$ controls its Bellman shortfall:
--
--   $$\phi(t,S^t)-\left(R(S^t,\xi^t,\widehat U^t)+\mathbb E[\phi(t-1,S^{t-1})\mid\mathcal G_t]\right)\le r\quad\text{a.s. on }Q(t,S^t).$$
--
--   This is the compensation available when Online and Offline would otherwise choose different actions.
--
--   **Formalization Note** The printed p. 14 display has an unbalanced parenthesis and a plus sign before the conditional expectation. Definition 4 on p. 11 fixes the sign and parentheses used here.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, p. 14, Proof of Theorem 5, maximum-loss display (corrected using Definition 4, p. 11)

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
Inequalities*, arXiv:1906.06361v2, Proof of Theorem 5, maximum-loss display, p. 14. On disagreement paths,
the Online action's Bellman shortfall is bounded by `r`.
Formalization Note: the page has an unbalanced parenthesis and a plus before
the expectation; the subtraction here follows Definition 4 on p. 11. `r` is
an almost-sure upper bound, rather than a potentially undefined maximum. -/
theorem theorem_5_maxloss_step
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (r : ℝ) (hr : @MaxLossBound Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ r)
    (π : Policy Ω S U)
    (hπF : NonAnticipative ξ T π)
    (hπ : Feasible P ξ T π) :
    ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ,
      ω ∈ @disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t →
      ϕ t (traj P ξ T π s₀ t ω) ω -
        (P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω) +
          μ[fun ω => ϕ (t - 1) (traj P ξ T π s₀ (t - 1) ω) ω | augmented ξ T Gextra t] ω) ≤ r := by sorry

end BellmanIneq.Regret
