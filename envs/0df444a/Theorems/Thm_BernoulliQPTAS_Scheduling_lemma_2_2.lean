-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_2_2
-- name    : BernoulliQPTAS.Scheduling.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:47.232453+00:00
-- url     : https://prove2.me/theorems/95bb1856-d202-46c2-85e4-07545a84072c
-- title:
--   Lemma 2.2 — processing-volume and subset lower bounds
-- statement:
--   Let $J$ be the full job set, let $P(U)=\sum_{j\in U}q_jp_j$, and let $\operatorname{OPT}(U)$ be the unrestricted adaptive optimum when only jobs in $U$ are present on the original $m$ machines. Then
--
--   $$P(J)\le\operatorname{OPT}(J),\qquad \operatorname{OPT}(U)+P(J\setminus U)\le\operatorname{OPT}(J)\quad\text{for every }U\subseteq J.$$
--
--   These are simultaneous conclusions, including the empty and full subsets. They compare the wrapper with the original unrestricted optimum.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 2.2, p. 7; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Objective

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_2_2 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N) :
    totalMean I Finset.univ ≤ optimum I (initialState Finset.univ) ∧
      ∀ U : Finset (Fin N), optimum I (initialState U) +
        totalMean I (Finset.univ \ U) ≤ optimum I (initialState Finset.univ) := by sorry

end BernoulliQPTAS.Scheduling
