-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_6
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:57:31.508794+00:00
-- url     : https://prove2.me/theorems/c4dce730-2da1-42f6-825b-a760ff1ca6bb
-- title:
--   Theorem 6, p. 28 — stochastic rewards and adversarial contexts force Ω(√(λ(G)KT)) regret
-- statement:
--   There is an absolute $a>0$ such that for each $K\ge2$, $C\ge1$, and self-looped directed graph $G$ on $[C]$, for every sufficiently large horizon and every randomized measurable policy, there exist an oblivious context sequence and stochastic reward laws in $[0,1]$, with all arm graphs equal to $G$, such that
--   $$\mathbb E[\mathrm{Reg}(A)]\ge a\sqrt{\lambda(G)KT}.$$
--   The expectation is over rewards and the policy; the benchmark chooses the highest-mean arm in each context. This is the lower bound of §4.2.
--
--   **Formalization Note** The horizon threshold may depend on $K,C,G$, and there is no divisibility assumption. The context sequence is fixed in advance. The hard reward laws have independent coordinates, expressed by `S.IsCoordinateIndependent`, as in Appendix C.8. The auxiliary context law inside `StochInstance` is unused in `fixedStochRegret` and places no restriction on the selected sequence.
--
--   Differences from the source:
--   - encoding: an Ω lower bound → one absolute positive real constant, then every fixed dimension/graph has a positive horizon threshold, and every larger horizon satisfies the bound; reason: the meaning of the asymptotic rate; constants never depend on the horizon, instance, dimensions or policy
--   - reading: multi-armed bandits with a nonzero asymptotic lower bound → K ≥ 2, C > 0 and a positive horizon threshold; reason: one arm has identically zero regret and no positive context law exists on an empty set; thresholds exclude only the small-horizon regime, where an uncapped square-root lower bound can exceed T
--   - encoding: any randomized algorithm and its expected regret → valid measurable behavioural policies with the masked feedback record, finite arm/context sums, and integrals over bounded reward tables; reason: the protocol has perfect recall; behavioural policies describe the same observable strategies and measurability makes the source expectations defined
--   - generalization: any learning algorithm has a hard stochastic instance and adversarial contexts → one oblivious context sequence is chosen before every policy, and the stochastic reward laws may then depend on the policy; reason: Appendix C.8 fixes the epoch schedule from G alone; forgetting the uniformity recovers the source assertion
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 28, Theorem 6

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_AcyclicNumber
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_FixedContextProtocol

namespace CrossLearnCB.UCB1CL.Supplement

/-- Theorem 6, p. 28. Stochastic rewards with an oblivious context sequence.
The asymptotic constant precedes all problem parameters. -/
theorem theorem_6 : ∃ c : ℝ, 0 < c ∧
    ∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∀ G : Fin C → Fin C → Prop,
    (∀ d, G d d) → ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
    ∃ ctx : Fin T → Fin C, ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
      ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧
        c * Real.sqrt ((maxAcyclicNumber G : ℝ) * K * T) ≤
          fixedStochRegret (fun _ => G) ctx S A := by sorry

end CrossLearnCB.UCB1CL.Supplement
