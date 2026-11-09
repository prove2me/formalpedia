-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_lemma_2_3
-- name    : BipHamCount.Deterministic.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:57.019542+00:00
-- url     : https://prove2.me/theorems/07f86448-1365-491b-8eb8-c0932557dfc7
-- title:
--   Lemma 2.3 — determinant of a diagonal matrix plus a matrix
-- statement:
--   Let $R$ be a commutative ring and $K$ any finite ordered set. Let $C$ be a square matrix on $K$, and let $D$ be diagonal with entries $d_i$. Then
--   $$\det(D+C)=\sum_{I\subseteq K}\det C[I,I]\prod_{i\in K\setminus I}d_i.$$
--   All empty determinants and products are one. In particular the identity applies over $\mathbb Z[x]$, the coefficient ring required by the paper's determinant polynomial. This is the principal-minor expansion used to identify its coefficients.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - generalization: the matrix identities in the paper scalar setting (also used over ℤ[x] on p.9) → the identity over every commutative ring; reason: the identity is polynomial in the matrix entries and specializes to both ℤ and ℤ[x]
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 2.3, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Lemma 2.3 p.5. The coefficient ring includes ℤ[x], used on p.9.
The empty minor and empty product both equal one. -/
theorem lemma_2_3 {R K : Type*} [CommRing R] [Fintype K] [LinearOrder K]
    (C : Matrix K K R) (d : K → R) :
    (Matrix.diagonal d + C).det = ∑ I ∈ (Finset.univ : Finset K).powerset,
      minor C I I * ∏ i ∈ Iᶜ, d i := by sorry

end BipHamCount.Deterministic
