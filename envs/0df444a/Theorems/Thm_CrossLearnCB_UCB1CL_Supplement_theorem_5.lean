-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_5
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:56:38.448805+00:00
-- url     : https://prove2.me/theorems/6dad089a-c067-4316-a8b8-85f438845795
-- title:
--   Theorem 5, p. 27 — stochastic rewards and contexts force Ω(√(ν₂(G)KT)) regret
-- statement:
--   There is an absolute $a>0$ such that for each $K\ge2$, $C\ge1$, and self-looped directed graph $G$ on $[C]$, there is $T_0\ge1$ such that every $T\ge T_0$ and every randomized measurable policy admit a stochastic reward/context instance with graph $G$ for every arm and
--   $$\mathbb E[\mathrm{Reg}(A)]\ge a\sqrt{\nu_2(G)KT}.$$
--   The benchmark chooses the highest-mean arm in each context. This is the lower bound of §4.1. The context distribution is chosen before the policy, which may know it; the reward instance may depend on the policy and horizon.
--
--   **Formalization Note** The threshold may depend on $K,C,G$. The hard instance has independent reward coordinates with time-independent laws on $[0,1]$ and i.i.d. contexts; `IsCoordinateIndependent` explicitly retains this source class even though the general stochastic model also allows footnote 3 correlations. No restriction to special graphs or context distributions is imposed.
--
--   Differences from the source:
--   - encoding: an Ω lower bound → one absolute positive real constant, then every fixed dimension/graph has a positive horizon threshold, and every larger horizon satisfies the bound; reason: the meaning of the asymptotic rate; constants never depend on the horizon, instance, dimensions or policy
--   - reading: multi-armed bandits with a nonzero asymptotic lower bound → K ≥ 2, C > 0 and a positive horizon threshold; reason: one arm has identically zero regret and no positive context law exists on an empty set; thresholds exclude only the small-horizon regime, where an uncapped square-root lower bound can exceed T
--   - encoding: any randomized algorithm and its expected regret → valid measurable behavioural policies with the masked feedback record, finite arm/context sums, and integrals over bounded reward tables; reason: the protocol has perfect recall; behavioural policies describe the same observable strategies and measurability makes the source expectations defined
--   - generalization: any learning algorithm has a hard stochastic instance → for each horizon there is one context law D, then every policy admits a hard reward instance with S.D = D; reason: the proof on pp. 51–53 first fixes f using G, independently of the algorithm; algorithms may know that context law
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 27, Theorem 5

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_GraphLowerQuantities
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

namespace CrossLearnCB.UCB1CL.Supplement

/-- Theorem 5, p. 27. An absolute positive lower-bound constant, with sufficiently large
horizon for each fixed graph and arm count. All arms have graph G. -/
theorem theorem_5 : ∃ c : ℝ, 0 < c ∧
    ∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∀ G : Fin C → Fin C → Prop,
    (∀ d, G d d) → ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
    ∃ D : Fin C → ℝ, IsDistribution D ∧ ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
      ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧ S.D = D ∧
        c * Real.sqrt (nuTwo G * K * T) ≤ stochRegret T (fun _ => G) S A := by sorry

end CrossLearnCB.UCB1CL.Supplement
