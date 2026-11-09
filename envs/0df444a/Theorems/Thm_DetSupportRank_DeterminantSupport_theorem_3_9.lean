-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_theorem_3_9
-- name    : DetSupportRank.DeterminantSupport.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:45.133178+00:00
-- url     : https://prove2.me/theorems/519b4d05-4a5c-4b4b-a94f-d288dd4a4e30
-- title:
--   Theorem 3.9 — Partition rank lower bound method
-- statement:
--   Let $f$ be a nonzero set-multilinear polynomial over an arbitrary field, with $d\ge2$ row parts and any positive number of variables per row. Then
--   $$\rho(f)\le\operatorname{PR}(f).$$
--   Here $\rho$ is the actual hyperplane-covering minimum of the equation-defined degree varieties. This is the lower-bound framework, rather than a hypothesis of the final target.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: minimum finite decomposition length and hyperplane-covering size → infimum of actual witness lengths in ℕ∞, with empty infimum ∞; reason: on the source domain partition rank is finite and attained by a row expansion; the separate attainment target records this, and Theorem 3.9 also implies finite covering rank
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 3.9, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeVarieties

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Theorem 3.9, p.7. -/
theorem theorem_3_9 {K : Type*} [Field K] {d m : ℕ}
    (hd : 2 ≤ d) (hm : 0 < m) (f : MvPolynomial (Fin d × Fin m) K)
    (hf : f ≠ 0) (hml : SetMultCost.IsSetMultilinearOn Prod.fst Finset.univ f) :
    coveringRank f ≤ partitionRank f := by sorry

end DetSupportRank.DeterminantSupport
