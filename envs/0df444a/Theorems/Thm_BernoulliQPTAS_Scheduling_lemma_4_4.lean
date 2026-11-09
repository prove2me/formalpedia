-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_4_4
-- name    : BernoulliQPTAS.Scheduling.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:30.11972+00:00
-- url     : https://prove2.me/theorems/4e424a60-bc6b-445e-bdb0-b4d6aef7caab
-- title:
--   Lemma 4.4 — release-time counting
-- statement:
--   Let $n$ be the number of nonempty distinct-size classes and $K\ge1$. Generate every state reachable from zero releases and the full job set under every eligible class action and either outcome of the specified Bellman dynamic program. Let $\mathcal T$ be the union of the entries of all its release vectors, including zero. Then
--
--   $$|\mathcal T|\le\binom{(K+1)N+n-1}{n}.$$
--
--   The set is generated from the transitions. Its cardinality bound is a conclusion, not a field or supplied invariant of the state type.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 4.4, p. 12; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_4_4 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N)
    (K : ℕ) (hK : 1 ≤ K) :
    (releaseTimes I K).card ≤ Nat.choose ((K + 1) * N + (sizeClasses I).card - 1)
      (sizeClasses I).card := by sorry

end BernoulliQPTAS.Scheduling
