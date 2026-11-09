-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_lemma_2_2
-- name    : BipHamCount.Deterministic.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:46.742208+00:00
-- url     : https://prove2.me/theorems/7d3b82b5-ae58-40fe-93fa-23f9fa16ebee
-- title:
--   Lemma 2.2 — full Cauchy–Binet, including a smaller middle dimension
-- statement:
--   Let $R$ be a commutative ring, let $I$ have $r$ elements, and let $K$ be any finite ordered set. For $M:I\times K\to R$ and $N:K\times I\to R$,
--   $$\det(MN)=\sum_{J\subseteq K,\ |J|=r}\det M[I,J]\det N[J,I].$$
--   There is no assumption $|K|\ge r$. If $|K|<r$, the sum is empty and the determinant is zero. Both minor factors use the same increasing order on $J$, and empty square determinants equal one. The Open MatroidSensOracle.lemma_2_4 states the restricted case with $r\le|K|$; the present target includes the missing case needed by Lemma 4.4, rather than reposing that restricted goal.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - generalization: the matrix identities in the paper scalar setting (also used over ℤ[x] on p.9) → the identity over every commutative ring; reason: the identity is polynomial in the matrix entries and specializes to both ℤ and ℤ[x]
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 2.2, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Lemma 2.2 (Cauchy–Binet), p.5, with no dimension restriction.
This includes |K|<|I|, when the right side is empty and det(MN)=0.
The two minor factors use the same increasing order on J. -/
theorem lemma_2_2 {R : Type*} [CommRing R] (r : ℕ) {K : Type*}
    [Fintype K] [LinearOrder K] (M : Matrix (Fin r) K R) (N : Matrix K (Fin r) R) :
    (M * N).det = ∑ J ∈ (Finset.univ : Finset K).powerset.filter (fun J => J.card = r),
      minor M Finset.univ J * minor N J Finset.univ := by sorry

end BipHamCount.Deterministic
