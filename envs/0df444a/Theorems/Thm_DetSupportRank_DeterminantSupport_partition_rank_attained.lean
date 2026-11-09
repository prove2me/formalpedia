-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_partition_rank_attained
-- name    : DetSupportRank.DeterminantSupport.partition_rank_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:54.495028+00:00
-- url     : https://prove2.me/theorems/1fa21aff-9597-4a87-9bef-8f3211d9a91f
-- title:
--   Partition rank has an attained finite minimum
-- statement:
--   Let $F$ be any field, let $d\ge2$ and $m>0$, and let $f\in F[x_{i,j}]$ be set-multilinear in its $d$ row parts. Then
--   $$\exists r\le m:\quad f\text{ has a partition decomposition of length }r,\qquad\operatorname{PR}(f)=r.$$
--   This records finite attainment of the actual minimum, including the empty decomposition when $f=0$. The source's expansion along one row supplies the finite upper bound.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: minimum finite decomposition length and hyperplane-covering size → infimum of actual witness lengths in ℕ∞, with empty infimum ∞; reason: on the source domain partition rank is finite and attained by a row expansion; the separate attainment target records this, and Theorem 3.9 also implies finite covering rank
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §1, row-expansion upper bound, p. 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank

noncomputable section

namespace DetSupportRank.DeterminantSupport

/-- §1, p.1, row-expansion bound and the actual finite minimum defining partition rank. -/
theorem partition_rank_attained {K : Type*} [Field K] {d m : ℕ}
    (hd : 2 ≤ d) (hm : 0 < m) (f : MvPolynomial (Fin d × Fin m) K)
    (hml : SetMultCost.IsSetMultilinearOn Prod.fst Finset.univ f) :
    ∃ r : ℕ, r ≤ m ∧ HasPartitionDecomposition f r ∧ partitionRank f = (r : ℕ∞) := by sorry

end DetSupportRank.DeterminantSupport
