-- Prove2me | Theorems.Thm_FiniteGraph_exists_maximal_supergraph_with_property
-- name    : FiniteGraph.exists_maximal_supergraph_with_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:15:31.961632+00:00
-- url     : https://prove2.me/theorems/fc50763b-b07a-4448-8a68-23cfb193bb44
-- title:
--   A maximal finite property-preserving supergraph
-- statement:
--   Among property-preserving supergraphs of a given graph on a finite vertex type, there is one whose edge set cannot be enlarged while preserving the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem FiniteGraph.exists_maximal_supergraph_with_property
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ F : SimpleGraph V,
      G.edgeSet ⊆ F.edgeSet ∧ P F ∧
        ∀ H : SimpleGraph V, F.edgeSet ⊆ H.edgeSet → P H → H.edgeSet = F.edgeSet := by sorry
