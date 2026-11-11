-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_short_scalar_separation
-- name    : CyclotomicRankTwoSVP.Main.short_scalar_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:02.558574+00:00
-- url     : https://prove2.me/theorems/0acab5f9-9695-4e62-8c1f-36a0fffe2e76
-- title:
--   Theorem 3.7 — short scalar coset separation
-- statement:
--   There are sufficiently large absolute positive integers $C_0,k_0$ such that for every $k\ge k_0$ and odd prime $q\ge(2k)^{C_0}$, set $h=\lfloor21k/20\rfloor$, $c=h+(1-\zeta)^{\lfloor k/2\rfloor}$ and $L=2kq$. Every nonzero $w\in O_K$ with $N(w)\le3q$ satisfies
--
--   $$\operatorname{dist}(wc,\mathfrak a_{q,k})^2>L/10.$$
--
--   The strict gap holds for every such scalar, including roots of unity, using this explicit center. The center is not supplied as an arbitrary point assumed to satisfy separation. The theorem controls short multiples of the coset in the rank-two reduction.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: one sufficiently large absolute pair C_0,k_0 → existential positive integer thresholds before every k,q and every instance; reason: taking maxima of the finitely many threshold witnesses supplies one common pair; increasing either threshold preserves each domain-restricted conclusion
--   - encoding: squared attained distance to the ideal → infimum of N(wc-y) for y in the actual principal ideal; reason: the ideal is nonempty and discrete, so this is exactly the squared source distance
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 13 / PDF p. 14, Theorem 3.7

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Counting

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem short_scalar_separation :
    ∃ C₀ k₀ : ℕ, 1 ≤ C₀ ∧ 1 ≤ k₀ ∧
      ∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ k₀ k q →
        ∀ w : K q, w ∈ OK q → w ≠ 0 → N w ≤ 3 * q →
          distanceSquared (w * center q k) (idealSet q k) > L q k / 10 := by sorry

end CyclotomicRankTwoSVP.Main
