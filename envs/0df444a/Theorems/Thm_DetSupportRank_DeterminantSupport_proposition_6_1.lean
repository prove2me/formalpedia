-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_proposition_6_1
-- name    : DetSupportRank.DeterminantSupport.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:25.729194+00:00
-- url     : https://prove2.me/theorems/9e365133-10b4-4327-a827-df002eef54ae
-- title:
--   Proposition 6.1 — A full permutation orbit gives the rank bound
-- statement:
--   Let $f$ be a nonzero set-multilinear polynomial over any field, with $n\ge3$ row parts and any positive number of variables per row. Suppose there is a point $y\in\mathbb C^n$ with pairwise distinct coordinates such that every $y^\sigma$ lies in $X_{n-1}(f)$. Then
--   $$\operatorname{PR}(f)\ge\begin{cases}n,&n\text{ odd},\\n-1,&n\text{ even}.\end{cases}$$
--   The hypothesis concerns one entire orbit. It does not require determinant support, symmetry of the entire variety, or nonzero coordinate sum.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: minimum finite decomposition length and hyperplane-covering size → infimum of actual witness lengths in ℕ∞, with empty infimum ∞; reason: on the source domain partition rank is finite and attained by a row expansion; the separate attainment target records this, and Theorem 3.9 also implies finite covering rank
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 6.1, p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Permutations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Proposition 6.1, p.27. -/
theorem proposition_6_1 {K : Type*} [Field K] {n m : ℕ}
    (hn : 3 ≤ n) (hm : 0 < m) (f : MvPolynomial (Fin n × Fin m) K)
    (hf : f ≠ 0) (hml : SetMultCost.IsSetMultilinearOn Prod.fst Finset.univ f)
    (y : Fin n → ℂ) (hy : Function.Injective y)
    (horbit : ∀ σ : Equiv.Perm (Fin n), (fun i => y (σ i)) ∈ degreeVariety f (n - 1)) :
    (if Odd n then (n : ℕ∞) else ((n - 1 : ℕ) : ℕ∞)) ≤ partitionRank f := by sorry

end DetSupportRank.DeterminantSupport
