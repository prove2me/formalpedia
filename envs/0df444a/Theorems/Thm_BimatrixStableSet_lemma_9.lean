-- Prove2me | Theorems.Thm_BimatrixStableSet_lemma_9
-- name    : BimatrixStableSet.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:51.519999+00:00
-- url     : https://prove2.me/theorems/be2270bd-0936-4bf8-969d-5f0479b7268a
-- title:
--   Lemma 9 — a 4-cube among two disjoint facets of $P$, and a 4-cube facet of $Q$
-- statement:
--   Let $(A,B)$ be a non-degenerate $5\times5$ game with best-response polytopes $P$ and $Q$. Let $P$ and $Q$ be non-neighborly, let $P_i$ and $P_j$ be disjoint facets of $P$, assume that one of them is a 4-cube, and assume that one facet of $Q$ is a 4-cube. Then the game has at most $32$ equilibria, counting the artificial equilibrium $(0,0)$.
--
--   This closes the last case in the proof of Theorem 5.
--
--   Differences from the source:
--   - encoding: the standing assumptions of the section, stated once → explicit hypotheses `HasBestResponsePolytopes A B` and `IsNondegenerate A B`; reason: same instances
--   - encoding: "at most $c$ equilibria" → `Set.encard` $\le c$ in $\mathbb N_\infty$; reason: finiteness is part of the claim, so no count of an infinite set collapses
--   - encoding: labels in $[m+n]$ → the type `Fin m ⊕ Fin n`, with label $i\le m$ as `Sum.inl` and label $m+j$ as `Sum.inr`; reason: same labels, zero-based
--   - encoding: the facets $P_1$, $P_2$ → facets $P_i$, $P_j$ with arbitrary labels $i\ne j$; reason: p.15 fixes the labels $1,2$ without loss of generality
--   - encoding: a facet of $Q$ → the facet $Q_k$ with some label $k$; reason: p.8: every facet of a non-degenerate game has a label
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Lemma 9, pp.18–19

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

/-- Lemma 9, pp.18–19 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3): let `P` and `Q` be
non-neighborly and assume that one of the disjoint facets `P₁`, `P₂` is a 4-cube, and that one facet
of `Q` is a 4-cube. Then the game has at most 32 equilibria.

**Formalization Note.** The standing assumptions of §6 are hypotheses, and the labels `i ≠ j` are
arbitrary, as for Lemma 8. "Is a 4-cube" means that the face lattice is that of `[0,1]⁴`, p.19. Every
facet of `Q` is the set `Q_k` of points with some label `k`, p.8. -/
theorem lemma_9 (A B : Matrix (Fin 5) (Fin 5) ℝ) (hPQ : HasBestResponsePolytopes A B)
    (hAB : IsNondegenerate A B)
    (hP : ¬ (bestResponseP B).IsDualNeighborly (bestResponseP B).carrier)
    (hQ : ¬ (bestResponseQ A).IsDualNeighborly (bestResponseQ A).carrier)
    (i j : Fin 5 ⊕ Fin 5) (hij : i ≠ j)
    (hi : (bestResponseP B).IsFacetOf ((bestResponseP B).face {i}) (bestResponseP B).carrier)
    (hj : (bestResponseP B).IsFacetOf ((bestResponseP B).face {j}) (bestResponseP B).carrier)
    (hdisj : Disjoint ((bestResponseP B).face {i}) ((bestResponseP B).face {j}))
    (hcubeP : (bestResponseP B).IsCubeType ((bestResponseP B).face {i}) 4 ∨
      (bestResponseP B).IsCubeType ((bestResponseP B).face {j}) 4)
    (k : Fin 5 ⊕ Fin 5)
    (hk : (bestResponseQ A).IsFacetOf ((bestResponseQ A).face {k}) (bestResponseQ A).carrier)
    (hcubeQ : (bestResponseQ A).IsCubeType ((bestResponseQ A).face {k}) 4) :
    (equilibria A B).encard ≤ 32 := by sorry

end BimatrixStableSet
