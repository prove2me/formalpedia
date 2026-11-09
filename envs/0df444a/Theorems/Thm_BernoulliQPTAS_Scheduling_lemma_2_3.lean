-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_2_3
-- name    : BernoulliQPTAS.Scheduling.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:53.788111+00:00
-- url     : https://prove2.me/theorems/0fb670f6-4c3d-4aee-a8c0-00dddaea1e34
-- title:
--   Lemma 2.3 — free times and residual volume
-- statement:
--   Start all machines free at zero and fix any complete feasible realized schedule in which each job starts at the earliest time a machine is free. Let $S_k$ be the first $k$ started jobs and $F_k$ the next start time. Let $W_{m-1}(S_k)$ be their processing volume after removing the $m-1$ largest realized processing times. For every $0\le k<N$,
--
--   $$F_k\le W_{m-1}(S_k)\le mF_k.$$
--
--   This statement concerns the particular realization. It does not require that the policy be non-idling on different realizations.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 2.3, p. 8; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Objective

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_2_3 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N)
    (actions : List (Action N m)) (ω : Outcome N)
    (hvalid : RealizedAdmissible I actions ω)
    (hearliest : EarliestTrace I (initialState Finset.univ) actions ω) :
    ∀ k < N,
      let F : ℝ≥0∞ := ((((actions[k]?).map Action.time).getD 0 : ℝ≥0) : ℝ≥0∞)
      let W := residualVolume I ω (m - 1) ((actions.take k).map Action.job)
      F ≤ W ∧ W ≤ m * F := by sorry

end BernoulliQPTAS.Scheduling
