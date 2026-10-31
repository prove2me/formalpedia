-- Prove2me | Theorems.Thm_BimatrixStableSet_lemma_8
-- name    : BimatrixStableSet.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:31.507355+00:00
-- url     : https://prove2.me/theorems/b2e0f62f-6c36-4b83-8638-cd11d0c58a80
-- title:
--   Lemma 8 — a semi-cube among two disjoint facets of $P$
-- statement:
--   Let $(A,B)$ be a non-degenerate $5\times5$ game with best-response polytopes $P$ and $Q$. Let $P$ and $Q$ be non-neighborly, let $P_i$ and $P_j$ be disjoint facets of $P$, and let $P_i$ be a semi-cube. Then the game has at most $32$ equilibria, counting the artificial equilibrium $(0,0)$.
--
--   This closes the semi-cube case in the proof of Theorem 5.
--
--   Differences from the source:
--   - encoding: the standing assumptions of the section, stated once → explicit hypotheses `HasBestResponsePolytopes A B` and `IsNondegenerate A B`; reason: same instances
--   - encoding: "at most $c$ equilibria" → `Set.encard` $\le c$ in $\mathbb N_\infty$; reason: finiteness is part of the claim, so no count of an infinite set collapses
--   - encoding: labels in $[m+n]$ → the type `Fin m ⊕ Fin n`, with label $i\le m$ as `Sum.inl` and label $m+j$ as `Sum.inr`; reason: same labels, zero-based
--   - encoding: the facets $P_1$, $P_2$ → facets $P_i$, $P_j$ with arbitrary labels $i\ne j$; reason: p.15 fixes the labels $1,2$ without loss of generality ("this is irrelevant")
--   - reading: "a semi-cube" → `IsSemiCube`, a polytope in $\mathcal P^4_8$ with $(V,b)=(17,14)$; reason: p.16 and row 23 of (8)
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Lemma 8, p.18

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

/-- Lemma 8, p.18 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): let `P` and `Q` be
non-neighborly, with disjoint facets `P₁` and `P₂` of `P`, and let `P₁` be a semi-cube. Then the game
has at most 32 equilibria.

**Formalization Note.** The standing assumptions of §6 are hypotheses. The paper's labels `1` and `2`
are a relabeling made without loss of generality on p.15, so the two labels `i ≠ j` are arbitrary. -/
theorem lemma_8 (A B : Matrix (Fin 5) (Fin 5) ℝ) (hPQ : HasBestResponsePolytopes A B)
    (hAB : IsNondegenerate A B)
    (hP : ¬ (bestResponseP B).IsDualNeighborly (bestResponseP B).carrier)
    (hQ : ¬ (bestResponseQ A).IsDualNeighborly (bestResponseQ A).carrier)
    (i j : Fin 5 ⊕ Fin 5) (hij : i ≠ j)
    (hi : (bestResponseP B).IsFacetOf ((bestResponseP B).face {i}) (bestResponseP B).carrier)
    (hj : (bestResponseP B).IsFacetOf ((bestResponseP B).face {j}) (bestResponseP B).carrier)
    (hdisj : Disjoint ((bestResponseP B).face {i}) ((bestResponseP B).face {j}))
    (hsemi : IsSemiCube ((bestResponseP B).realize ((bestResponseP B).face {i}))) :
    (equilibria A B).encard ≤ 32 := by sorry

end BimatrixStableSet
