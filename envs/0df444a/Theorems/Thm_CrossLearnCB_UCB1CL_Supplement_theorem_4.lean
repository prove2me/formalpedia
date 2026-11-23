-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_4
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:53:41.054496+00:00
-- url     : https://prove2.me/theorems/0919c5bd-19e9-4596-8718-df6b9c23d670
-- title:
--   Theorem 4, p. 25 — adversarial rewards and contexts force Ω(√(CKT)) regret even with complete cross-learning
-- statement:
--   There is an absolute $a>0$ such that for every $K\ge2$ and $C\ge1$, for all sufficiently large horizons $T$, there are an oblivious context sequence and a probability law on reward tables in $[0,1]$ for which every randomized measurable policy, even with complete cross-learning, has expected regret
--   $$\mathbb E[\mathrm{Reg}(A)]\ge a\sqrt{CKT}.$$
--   The same distribution defeats every policy; the benchmark is the best stationary policy in hindsight for the realized table and fixed contexts. This states the worst-case lower bound of §3.3.
--
--   **Formalization Note** The threshold may depend on $K,C$, and the table law and context sequence may depend on $T$. Complete cross-learning is the relation `True` on all context pairs. Rounds are 0-based. The source proof divides the horizon into epochs; the statement imposes no divisibility restriction and expresses its full asymptotic rate for every sufficiently large horizon.
--
--   Differences from the source:
--   - encoding: an Ω lower bound → one absolute positive real constant, then every fixed dimension/graph has a positive horizon threshold, and every larger horizon satisfies the bound; reason: the meaning of the asymptotic rate; constants never depend on the horizon, instance, dimensions or policy
--   - reading: multi-armed bandits with a nonzero asymptotic lower bound → K ≥ 2, C > 0 and a positive horizon threshold; reason: one arm has identically zero regret and no positive context law exists on an empty set; thresholds exclude only the small-horizon regime, where an uncapped square-root lower bound can exceed T
--   - encoding: any randomized algorithm and its expected regret → valid measurable behavioural policies with the masked feedback record, finite arm/context sums, and integrals over bounded reward tables; reason: the protocol has perfect recall; behavioural policies describe the same observable strategies and measurability makes the source expectations defined
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 25, Theorem 4

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_FixedContextProtocol

namespace CrossLearnCB.UCB1CL.Supplement

open MeasureTheory

/-- Theorem 4, pp. 25–26. The asymptotic constant is absolute; the threshold may depend
on K,C. A single oblivious distribution over tables defeats every measurable policy.
The context sequence and law are chosen before the algorithm. -/
theorem theorem_4 : ∃ c : ℝ, 0 < c ∧
    ∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∃ T₀ : ℕ, 0 < T₀ ∧
    ∀ T : ℕ, T₀ ≤ T → ∃ ctx : Fin T → Fin C,
    ∃ L : Measure (Fin T → Fin K → Fin C → ℝ),
      IsProbabilityMeasure L ∧
      (∀ᵐ r ∂L, ∀ t i d, r t i d ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
        c * Real.sqrt ((C : ℝ) * K * T) ≤
          ∫ r, fixedAdvRegret (fun _ _ _ => True) ctx A r ∂L := by sorry

end CrossLearnCB.UCB1CL.Supplement
