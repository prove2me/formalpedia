-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_4_5
-- name    : BernoulliQPTAS.Scheduling.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:42.842556+00:00
-- url     : https://prove2.me/theorems/b22b41a2-1796-4cc7-9f37-dbe01714abd0
-- title:
--   Lemma 4.5 — release-vector counting
-- statement:
--   Let $n$ be the number of distinct size classes, let $K\ge1$, and put $d=n(K+1)$. For every decision time $t$, let $\mathcal R_t$ be the distinct sorted release vectors reached by the full specified dynamic program whose minimum release is $t$. Then
--
--   $$|\mathcal R_t|\le\binom{m+d-1}{d-1}.$$
--
--   Only sorted vectors are counted, so identical machines do not create distinct permutations. All possible decision times are rational because sizes and the reuse map are rational.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 4.5, p. 13; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_4_5 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N)
    (K : ℕ) (hK : 1 ≤ K) (t : ℚ) :
    let d := (sizeClasses I).card * (K + 1)
    (releaseVectorsAt I K t).card ≤ Nat.choose (m + d - 1) (d - 1) := by sorry

end BernoulliQPTAS.Scheduling
