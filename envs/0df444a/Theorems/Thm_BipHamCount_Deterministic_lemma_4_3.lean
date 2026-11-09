-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_lemma_4_3
-- name    : BipHamCount.Deterministic.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:46.7412+00:00
-- url     : https://prove2.me/theorems/f3304dd7-ffca-4f20-b32a-62a918113d36
-- title:
--   Lemma 4.3 — the small-term Ryser rewrite
-- statement:
--   For any natural side size $m$, integer matrices $A,B$, vertex $v$ on the left, and natural threshold $k$, let $F$ and $\sigma_{\le k}$ be the finite sums of §4.2. Then
--   $$\sigma_{\le k}=\sum_{X,Y\subseteq R,\ |X\cup Y|\le k}(-1)^{|X|+|Y|}F(X,Y).$$
--   Both the union restriction and the sign are retained. This identity replaces the small-term summation by a family of the polynomial-time evaluations from Lemma 4.4.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - generalization: zero–one adjacency matrices A,B → arbitrary integer matrices A,B; reason: the Ryser rewrite is an integer polynomial identity and specializes to all adjacency matrices
--   - generalization: the fixed threshold k=αm → every natural threshold k (restricted to k≤m in the polynomial-cost statement); reason: the full source threshold kOf m is among these choices; no source instance is removed
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.3, p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Lemma 4.3 p.7 (proof p.8). The identity is over arbitrary integer matrices
and any threshold, specializing to the source's zero–one matrices and kOf m. -/
theorem lemma_4_3 (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) :
    sigmaSmall A B v k =
      ∑ X ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∑ Y ∈ Finset.univ.powerset.filter (fun Y : Finset (Fin m) => (X ∪ Y).card ≤ k),
          (-1 : ℤ) ^ (X.card+Y.card) * Fval A B v k X Y := by sorry

end BipHamCount.Deterministic
