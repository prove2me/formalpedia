-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_5_2
-- name    : DetSupportRank.DeterminantSupport.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:13.959822+00:00
-- url     : https://prove2.me/theorems/6c05813c-8951-40d2-829f-c74274abde32
-- title:
--   Lemma 5.2 — Degree-relation tests have a common lift to J
-- statement:
--   For every field $F$, every positive $n$, every polynomial $D$ with determinant support, every finite tuple size $N\ge0$, and every degree relation $a\sim_D b$,
--   $$q_{a,b}\le J.$$
--   Thus one integer polynomial $Q$ lies in every permutation ideal and specializes to the integer polynomial $\sum_i(z^{b_i}-z^{a_i})$ when all $\alpha_j$ become one. No map from $F$ to $\mathbb C$ or to $\mathbb Z$ is needed.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: independent nonzero field coefficients cσ → a function from permutations to field units; reason: every nonzero field element determines a unique unit, so this parametrizes exactly the source family
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 5.2, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DeterminantFamily
import Definitions.Def_DetSupportRank_DeterminantSupport_TestIdeal

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 5.2, p.17. -/
theorem lemma_5_2 {K : Type*} [Field K] {n N : ℕ}
    (hn : 0 < n) (c : Equiv.Perm (Fin n) → Kˣ) (a b : Fin N → Fin n → ℕ)
    (hrel : DegreeRelation (determinantSupportPolynomial c) a b) :
    HasTestLift (relationTest a b) := by sorry

end DetSupportRank.DeterminantSupport
