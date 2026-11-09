-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_theorem_5_1
-- name    : DetSupportRank.DeterminantSupport.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:59.155058+00:00
-- url     : https://prove2.me/theorems/5e18ff9b-654e-4f1c-b092-8cbf7e07a353
-- title:
--   Theorem 5.1 — Elementary symmetric variety inclusion
-- statement:
--   For every field $F$, every polynomial $D$ with determinant support, and every integer $1\le r\le n$,
--   $$E_r\subseteq X_r(D).$$
--   The assertion includes $r=n$ and all independent nonzero permutation coefficients. It is the source's inclusion, without assuming an equality special to the determinant.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: independent nonzero field coefficients cσ → a function from permutations to field units; reason: every nonzero field element determines a unique unit, so this parametrizes exactly the source family
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 5.1, p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DeterminantFamily
import Definitions.Def_DetSupportRank_DeterminantSupport_TestIdeal

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Theorem 5.1, p.16. -/
theorem theorem_5_1 {K : Type*} [Field K] {n r : ℕ}
    (c : Equiv.Perm (Fin n) → Kˣ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    elementaryZeroSet n r ⊆ degreeVariety (determinantSupportPolynomial c) r := by sorry

end DetSupportRank.DeterminantSupport
