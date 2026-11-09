-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_2_1
-- name    : BernoulliQPTAS.Scheduling.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:41.98195+00:00
-- url     : https://prove2.me/theorems/93e3152d-ac79-4509-ae0a-1df8e5a61744
-- title:
--   Lemma 2.1 — optimal deterministic non-idling policies
-- statement:
--   Let $s$ be any residual state of the Bernoulli scheduling instance. Among all causal randomized policies from $s$, including policies that idle, a deterministic non-idling policy attains the optimum. More precisely, the recursively enumerated finite family $\mathcal F_s$ is nonempty, consists of admissible non-idling trees, and satisfies
--
--   $$\operatorname{OPT}(s)=\min_{T\in\mathcal F_s}\operatorname{cost}(T).$$
--
--   The result establishes attainment over a finite family without restricting the original benchmark to that family.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 2.1, p. 7; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Objective

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_2_1 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N)
    (s : State N m) :
    let F := nonIdleTrees I s.remaining.card s
    F.Nonempty ∧
      (∀ t ∈ F, Admissible I s t ∧ NonIdling I s t) ∧
      (∃ t ∈ F, treeCost I t = optimum I s) := by sorry

end BernoulliQPTAS.Scheduling
