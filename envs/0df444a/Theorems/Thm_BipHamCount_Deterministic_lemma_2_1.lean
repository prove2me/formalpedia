-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_lemma_2_1
-- name    : BipHamCount.Deterministic.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:52.297132+00:00
-- url     : https://prove2.me/theorems/2d62ba3e-c226-4035-bc89-89e21935711c
-- title:
--   Lemma 2.1 — Ryser’s formula with independent row and column sets
-- statement:
--   Let $R$ be a commutative ring, and let $I,J$ be finite ordered sets with $|I|=|J|$. For a matrix $M:I\times J\to R$, its permanent is the sum of $\prod_{i\in I}M_{i,f(i)}$ over all bijections $f:I\to J$. Then
--   $$\operatorname{per}M=\sum_{X\subseteq J}(-1)^{|J|-|X|}\prod_{i\in I}\sum_{j\in X}M_{ij}.$$
--   This includes two empty carriers, giving one on both sides. In particular, the independent row and column sets can be subsets of different sides, as in the paper's applications. This form of inclusion–exclusion supplies the permanent expansion needed by the small-term identity.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - generalization: the matrix identities in the paper scalar setting (also used over ℤ[x] on p.9) → the identity over every commutative ring; reason: the identity is polynomial in the matrix entries and specializes to both ℤ and ℤ[x]
--   - encoding: permanent of a matrix with independent row and column sets → sum over all bijections between the two finite carriers; reason: this is the same permanent; when both carriers are empty there is one bijection and its product is one
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 2.1, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Lemma 2.1 (Ryser), p.5. Independent finite row/column carriers of equal
cardinality, including empty carriers; the bijection sum is the permanent. -/
theorem lemma_2_1 {R I J : Type*} [CommRing R] [Fintype I] [Fintype J]
    [LinearOrder I] [LinearOrder J] (hcard : Fintype.card I = Fintype.card J)
    (M : Matrix I J R) :
    rectPermanent M = ∑ X ∈ (Finset.univ : Finset J).powerset,
      (-1 : R) ^ (Fintype.card J - X.card) * ∏ i, ∑ j ∈ X, M i j := by sorry

end BipHamCount.Deterministic
