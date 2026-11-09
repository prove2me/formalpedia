-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_3
-- name    : DetSupportRank.DeterminantSupport.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:20.169248+00:00
-- url     : https://prove2.me/theorems/6933f7e6-368a-42cd-9a8f-249f001c0077
-- title:
--   Lemma 5.3 — Elementary symmetric zeroes pass every J-test
-- statement:
--   For $1\le r\le n$, let $q(z)=\sum_v c_vz^v\in\mathbb Z[z_1,\ldots,z_n]$ have a common lift to $J$. For every $y\in E_r$,
--   $$\sum_v c_v(v\cdot y)^r=0\quad\text{in }\mathbb C.$$
--   The coefficient sum has finite support and ranges over every integer polynomial with the lift property, not just polynomials from one selected degree relation.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.3, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_TestIdeal

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 5.3, p.17. -/
theorem lemma_5_3 {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n)
    (q : MvPolynomial (Fin n) ℤ) (hq : HasTestLift q)
    (y : Fin n → ℂ) (hy : y ∈ elementaryZeroSet n r) : powerTest q r y = 0 := by sorry

end DetSupportRank.DeterminantSupport
