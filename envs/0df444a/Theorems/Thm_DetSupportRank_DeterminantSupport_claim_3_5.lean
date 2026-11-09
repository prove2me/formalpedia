-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_claim_3_5
-- name    : DetSupportRank.DeterminantSupport.claim_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:26.617301+00:00
-- url     : https://prove2.me/theorems/03cd3838-978b-424d-a8f9-2ed76bf4d45c
-- title:
--   Claim 3.5 — Nested degree varieties
-- statement:
--   Let $f$ be a nonzero set-multilinear polynomial over any field, with positive row and column counts. For every $r\ge2$,
--   $$X_r(f)\subseteq X_{r-1}(f),\qquad X_1(f)\subseteq\{y:\textstyle\sum_i y_i=0\}.$$
--   Together these assertions give the full descending chain of degree varieties and its common ambient hyperplane.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Claim 3.5, p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeVarieties

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Claim 3.5, p.6. -/
theorem claim_3_5 {K : Type*} [Field K] {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (f : MvPolynomial (Fin d × Fin m) K) (hf : f ≠ 0)
    (hml : SetMultCost.IsSetMultilinearOn Prod.fst Finset.univ f) :
    (∀ r : ℕ, 2 ≤ r → degreeVariety f r ⊆ degreeVariety f (r - 1)) ∧
    degreeVariety f 1 ⊆ subsetHyperplane Finset.univ := by sorry

end DetSupportRank.DeterminantSupport
