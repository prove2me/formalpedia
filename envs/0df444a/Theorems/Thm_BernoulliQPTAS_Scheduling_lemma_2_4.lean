-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_2_4
-- name    : BernoulliQPTAS.Scheduling.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:50.480328+00:00
-- url     : https://prove2.me/theorems/b24cf2e6-c48e-4f99-bcf2-b0e908599630
-- title:
--   Lemma 2.4 — optimal class-ordered policies
-- statement:
--   Order each equal-size class by nondecreasing probability, breaking ties by job label. From every residual state $s$, there is an admissible deterministic non-idling policy $T$ respecting all these orders such that
--
--   $$\operatorname{cost}(T)=\operatorname{OPT}(s).$$
--
--   The optimum is still taken over all randomized causal policies, including deliberate idling. The assertion is existential; it does not claim that sorting an arbitrary given policy tree improves it.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 2.4, p. 8; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Objective

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_2_4 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N)
    (s : State N m) :
    ∃ t : PolicyTree N m, Admissible I s t ∧ NonIdling I s t ∧
      RespectsClasses I s t ∧ treeCost I t = optimum I s := by sorry

end BernoulliQPTAS.Scheduling
