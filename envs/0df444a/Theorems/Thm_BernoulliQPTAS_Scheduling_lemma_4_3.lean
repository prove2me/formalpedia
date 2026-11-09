-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_4_3
-- name    : BernoulliQPTAS.Scheduling.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:40.815406+00:00
-- url     : https://prove2.me/theorems/013c69bf-4471-45f2-abc1-399e3cf2c7a4
-- title:
--   Lemma 4.3 — exact Bellman recursion
-- statement:
--   For an instance with ordered equal-size classes and integer $K\ge1$, let $V$ be the specified rational Bellman recursion. If $N_c$ is the number of jobs of class $c$, then $V((0,\ldots,0),(N_1,\ldots,N_n))$ is the minimum cost of a grid-non-idling reuse-rule policy respecting the class orders. A policy attains it whenever it chooses, in each state, a class attaining the minimum, starts that class's first remaining job and uses a machine of minimum release: every such policy, with ties broken in any way, is a grid-non-idling reuse-rule policy respecting the class orders with cost $V$, and the defined recursive policy is one of them.
--
--   This identifies the mathematical optimization target. The cost of computing it is the subject of Theorem 4.6.
--
--   Differences from the source:
--   - encoding: remaining counts νc representing the last νc jobs in each fixed class order → reachable labeled remaining-job sets obtained only by removing class heads; reason: these sets encode exactly the same suffix tuples; a sorted release list omits physical labels while execution separately maintains them
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 4.3, p. 12; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_4_3 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N)
    (K : ℕ) (hK : 1 ≤ K) :
    let root : PhysicalDPState N m := ⟨fun _ => 0, Finset.univ⟩
    let V := bellman I K N (dpInitial N m Finset.univ)
    ENNReal.ofReal V = reuseOptimum I K ∧
      ChoosesMinimum I K N root (dpPolicy I K) ∧
      ∀ t : PolicyTree N m, ChoosesMinimum I K N root t →
        ReuseAdmissible I K (initialState Finset.univ) t ∧
        GridNonIdling I K (initialState Finset.univ) t ∧
        RespectsClasses I (initialState Finset.univ) t ∧
        treeCost I t = ENNReal.ofReal V := by sorry

end BernoulliQPTAS.Scheduling
