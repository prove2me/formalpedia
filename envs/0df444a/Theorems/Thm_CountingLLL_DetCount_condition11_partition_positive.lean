-- Prove2me | Theorems.Thm_CountingLLL_DetCount_condition11_partition_positive
-- name    : CountingLLL.DetCount.condition11_partition_positive
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T03:57:04.224833+00:00
-- url     : https://prove2.me/theorems/49713544-5316-4b59-b742-c2da8795ce95
-- title:
--   Condition 1.1 implies positivity for every subfamily
-- statement:
--   Let $\Phi$ be a finite constraint satisfaction problem with independent uniform variables, nonempty finite domains and nonempty constraint scopes. Let $p$ be its maximum violation probability and $D$ its maximum dependency degree. If
--
--   $$4\mathrm e\,p(D+1)^2\le1,$$
--
--   then every subfamily $E$ of its constraints has at least one satisfying assignment: $Z_\Phi(E)>0$.
--
--   This includes the empty family and supplies the positive denominators used in the marginal and 2-tree expansions. It is a corollary of Condition 1.1 and the Lovász local lemma; the additional standing assumptions on maximum width and degree are not required.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442, Condition 1.1 and the discussion preceding Lemma 3.1, printed pp. 2 and 7; derived corollary. https://arxiv.org/abs/2608.08616

import Definitions.Def_CountingLLL_DetCount_CSP

namespace CountingLLL.DetCount

/-- Every subfamily of a CSP satisfying Condition 1.1 has a satisfying assignment. -/
theorem condition11_partition_positive (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) : 0 < Φ.Z E := by sorry

end CountingLLL.DetCount
