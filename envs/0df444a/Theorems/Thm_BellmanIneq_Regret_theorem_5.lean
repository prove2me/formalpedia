-- Prove2me | Theorems.Thm_BellmanIneq_Regret_theorem_5
-- name    : BellmanIneq.Regret.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:40.782643+00:00
-- url     : https://prove2.me/theorems/ab7d0e97-5179-4e36-8529-1ea645904988
-- title:
--   Theorem 5 — regret bounded by information and Bellman losses
-- statement:
--   Let Offline use the canonical augmented filtration $\mathcal G$, let $\phi$ and $L_B$ satisfy the Bellman inequalities, and let $r$ bound the maximum loss. For any feasible non-anticipative state-feedback policy, write $S^t$ and $\widehat U^t$ for its trajectory and actions, and $Q_t$ for the event that $\widehat U^t$ is not satisfying. Its expected regret against Offline satisfies
--
--   $$\mathbb E[\mathrm{Regret}]\le\mathbb E\!\left[\sum_{t=1}^{T}\bigl(r\mathbf1_{Q_t}+\mathbf1_{Q_t^c}L_B(t,S^t)\bigr)\right].$$
--
--   If $L_B(t,s)\ge0$ throughout the decision horizon, then the same bound is at most
--
--   $$\sum_{t=1}^{T}\left(r\,\mathbb P(Q_t)+\mathbb E[L_B(t,S^t)]\right).$$
--
--   This separates the information loss from violations of the Bellman equation. RABBI is included among the stated policies.
--
--   **Formalization Note** The second inequality needs nonnegative $L_B$, absent from the printed theorem. Both bounds use a real, almost-sure maximum-loss upper bound and the feasible-action Offline value computed by equation (2). The model assumes bounded, measurable data on countable states and finite actions.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, p. 13, Theorem 5

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
Inequalities*, arXiv:1906.06361v2, Theorem 5, p. 13. Expected regret against Offline is at most the
information-loss compensation plus Bellman loss.
Formalization Note: the first inequality holds for signed `LB`; the page's
second inequality needs the disclosed hypothesis `LB ≥ 0`. The result is
stated for any observed-information adapted feasible state-feedback policy,
which includes RABBI. `r` is an almost-sure upper bound from Definition 4.
The benchmark value is computed by equation (2), and all sums run over
`[1,T]` with time-to-go indexing. -/
theorem theorem_5
    (hG : Gextra ≤ mΩ) (hξ : ∀ t ∈ Finset.Icc 1 T, Measurable[mΩ] (ξ t))
    (hP : P.Standing K)
    (hBI : @BellmanInequalities Ω S Ξ U mΩ mΞ μ P ξ T Gextra K ϕ LB s₀)
    (r : ℝ) (hr : @MaxLossBound Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ r)
    (π : Policy Ω S U)
    (hπF : NonAnticipative ξ T π)
    (hπ : Feasible P ξ T π) :
    @regret Ω S Ξ U mΩ mΞ μ P ξ T Gextra π s₀ ≤
        ∫ ω, ∑ t ∈ Finset.Icc 1 T, (r * (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t).indicator (fun _ => (1 : ℝ)) ω + (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)ᶜ.indicator (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω) ∂μ ∧
      ((∀ t ∈ Finset.Icc 1 T, ∀ s ω, 0 ≤ LB t s ω) →
        (∫ ω, ∑ t ∈ Finset.Icc 1 T, (r * (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t).indicator (fun _ => (1 : ℝ)) ω + (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)ᶜ.indicator (fun ω => LB t (traj P ξ T π s₀ t ω) ω) ω) ∂μ) ≤
          ∑ t ∈ Finset.Icc 1 T,
            (r * (μ (@disagreement Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB π s₀ t)).toReal +
              ∫ ω, LB t (traj P ξ T π s₀ t ω) ω ∂μ)) := by sorry

end BellmanIneq.Regret
