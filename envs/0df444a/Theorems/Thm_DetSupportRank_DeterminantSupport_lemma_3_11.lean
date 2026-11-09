-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_lemma_3_11
-- name    : DetSupportRank.DeterminantSupport.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:53.233979+00:00
-- url     : https://prove2.me/theorems/388c5954-ce49-4cce-9cde-dae235d0a8cc
-- title:
--   Lemma 3.11 — Power polarization identity
-- statement:
--   For any commutative ring $R$, every $r\ge0$, and $t_1,\ldots,t_r\in R$,
--   $$\sum_{I\subseteq[r]}(-1)^{|I|}\left(\sum_{i\in I}t_i\right)^r=(-1)^r r!\prod_{i=1}^r t_i.$$
--   At $r=0$ both sides are one. This is the full polynomial identity, before any cancellation of a factorial in the later complex application.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - generalization: an integer polynomial identity in formal variables → the identity after substitution into every commutative ring; reason: every substitution follows from the integer identity; taking the universal polynomial ring recovers it
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Lemma 3.11, p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeRelations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Lemma 3.11, p.8. -/
theorem lemma_3_11 {R : Type*} [CommRing R] (r : ℕ) (t : Fin r → R) :
    (∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
      (-1 : R) ^ I.card * (∑ i ∈ I, t i) ^ r) =
    (-1 : R) ^ r * (Nat.factorial r : R) * ∏ i, t i := by sorry

end DetSupportRank.DeterminantSupport
