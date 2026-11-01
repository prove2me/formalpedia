-- Prove2me | Theorems.Thm_FiniteSimpleGraph_exists_edge_maximal_extension__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
-- name    : FiniteSimpleGraph.exists_edge_maximal_extension__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:22:14.182747+00:00
-- url     : https://prove2.me/theorems/04530e67-a406-43c9-a9b5-30db75f9b07d
-- title:
--   Finite edge-maximal extension for a downward-closed predicate
-- statement:
--   For a finite ordered vertex type, any downward-closed graph property satisfied by K has a supergraph of K satisfying the property that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem FiniteSimpleGraph.exists_edge_maximal_extension__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ G H : SimpleGraph V, H.edgeSet ⊆ G.edgeSet → P G → P H)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ P L ∧
      (∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet → P M →
        M.edgeSet = L.edgeSet) := by
  sorry
