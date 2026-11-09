-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_lemma_3_2
-- name    : BipHamCount.Deterministic.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:49.558877+00:00
-- url     : https://prove2.me/theorems/64050318-47dc-4afe-9a39-48a363d69322
-- title:
--   Lemma 3.2 — the bipartite signed sum is the exact count
-- statement:
--   Let $m$ be any natural number, $A,B$ zero–one integer matrices indexed by two ordered copies of $\mathrm{Fin}(m)$, and $v$ a vertex in the left side. Form the bipartite digraph $D$ whose left-to-right adjacency is $A$ and whose right-to-left adjacency is $B$. Then
--   $$\sigma(A,B,v)=h(D).$$
--   Here $\sigma$ is the signed product-of-minors sum from §3, and the equality is in the integers. Both arc directions are independent. This identifies the algebraic quantity computed by the program with the exact combinatorial count.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - encoding: directed Hamiltonian cycles, with the permutation-successor bijection on p.6 → single-cycle permutations with support equal to the full vertex set; counts zero for n≤1 and counts a directed digon once; reason: this is exactly the stated successor bijection on loopless nondegenerate inputs; the paper does not discuss n≤1
--   - encoding: A and B are the zero–one adjacency matrices from §2 p.4 → integer matrices with explicit ZeroOne hypotheses; reason: these hypotheses specify exactly the source matrices and prevent entry bit lengths from being unconstrained
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 3.2, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Lemma 3.2 p.6: σ equals the directed Hamiltonian-cycle count. -/
theorem lemma_3_2 (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (v : Fin m) :
    sigma A B v = (hamCount (bipDigraph A B) : ℤ) := by sorry

end BipHamCount.Deterministic
