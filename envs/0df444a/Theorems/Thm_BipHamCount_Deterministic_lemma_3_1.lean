-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_lemma_3_1
-- name    : BipHamCount.Deterministic.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:47.582612+00:00
-- url     : https://prove2.me/theorems/9ac6d2bd-9472-45db-a2bc-3c17994fcc04
-- title:
--   Lemma 3.1 — Hamiltonian-cycle permanent/determinant identity
-- statement:
--   Let $G$ be any loopless digraph on a finite ordered vertex set $V$, with Boolean adjacency and integer adjacency matrix $M$, and let $v\in V$. If $h(G)$ is its number of directed Hamiltonian cycles, then
--   $$h(G)=\sum_{U\subseteq V\setminus\{v\}}(-1)^{|V\setminus U|+1}\operatorname{per}M[U,U]\det M[V\setminus U,V\setminus U].$$
--   No bipartiteness assumption is made. The determinant and permanent of the empty matrix equal one. This identity connects the cycle count with principal minors and is the input to the bipartite factorization.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - encoding: directed Hamiltonian cycles, with the permutation-successor bijection on p.6 → single-cycle permutations with support equal to the full vertex set; counts zero for n≤1 and counts a directed digon once; reason: this is exactly the stated successor bijection on loopless nondegenerate inputs; the paper does not discuss n≤1
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 3.1, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Lemma 3.1, p.5 (proof p.6): the full identity for every loopless digraph.
The vertex v makes the carrier nonempty; bipartiteness is not assumed. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [LinearOrder V]
    (adj : V → V → Bool) (hloop : ∀ u, adj u u = false) (v : V) :
    (hamCount adj : ℤ) =
      ∑ U ∈ (Finset.univ.erase v).powerset,
        (-1 : ℤ) ^ (Uᶜ.card + 1) * permMinor (adjMatrix adj) U U *
          minor (adjMatrix adj) Uᶜ Uᶜ := by sorry

end BipHamCount.Deterministic
