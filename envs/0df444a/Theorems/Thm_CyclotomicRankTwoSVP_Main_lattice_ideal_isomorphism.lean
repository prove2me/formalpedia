-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_lattice_ideal_isomorphism
-- name    : CyclotomicRankTwoSVP.Main.lattice_ideal_isomorphism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:07.328736+00:00
-- url     : https://prove2.me/theorems/37a98f7f-abb4-4398-970a-77544143aec4
-- title:
--   Theorem 3.2 — lattice-to-ideal isomorphism and minimum
-- statement:
--   Let $q$ be an odd prime and $1\le k\le q/2$. Evaluation at the primitive root restricts to an additive-group isomorphism
--
--   $$L_{q,k}\cap1_q^\perp\ \xrightarrow{\ z\mapsto[z]\ }\ \mathfrak a_{q,k},\qquad\mathfrak a_{q,k}=(1-\zeta)^kO_K.$$
--
--   The zero-sum condition is an integer equality. In addition, for the unnormalized canonical norm,
--
--   $$\lambda_1(\mathfrak a_{q,k})^2\ge2kq.$$
--
--   The formal isomorphism is required to agree pointwise with the actual coefficient evaluation; existence of an unrelated abstract isomorphism would not suffice. This result gives both the structural map and its metric consequence.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - encoding: the squared attained first minimum of the indicated lattice → the real infimum of its nonzero squared norm values; reason: these nonzero discrete lattices have a shortest vector; the set of values is nonempty and bounded below by zero
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 9 / PDF p. 10, Theorem 3.2

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem lattice_ideal_isomorphism (q k : ℕ) [Fact q.Prime]
    (hq : Odd q) (hk : 1 ≤ k) (hkq : 2 * k ≤ q) :
    (∃ e : zeroSumRS q k ≃+ idealGroup q k,
      ∀ z : zeroSumRS q k, (e z : K q) = evalZ (z : ZMod q → ℤ)) ∧
    firstSquared N (idealSet q k) ≥ 2 * k * q := by sorry

end CyclotomicRankTwoSVP.Main
