-- Prove2me | solution 1 for maximal_drawable_graph_has_edge_extension_triangulation__p2m_869ffda5_b864_4783_a885_44fd746ff24a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:58:47.875832+00:00
-- url     : https://prove2.me/submissions/d88a28c7-1e5d-4385-9227-ca9d53a237d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_exists_maximal_drawable_supergraph__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
import Theorems.Thm_maximal_drawable_graph_has_triangulation_edge_count__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
import Theorems.Thm_strict_supergraph_of_planar_edge_count_gap__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := dK
    K.edgeFinset.card < 3 * Fintype.card V - 6 →
      ∃ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧ ¬ L ≤ K ∧
          (letI : DecidableRel L.Adj := Classical.decRel L.Adj
           L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := dK
  intro hsmall
  obtain ⟨L, hL, hKL, hmax⟩ :=
    exists_maximal_drawable_supergraph__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1 K hK
  have hcount :=
    maximal_drawable_graph_has_triangulation_edge_count__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
      L hL hmax hn
  exact ⟨L, hL, hKL,
    strict_supergraph_of_planar_edge_count_gap__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
      K L dK hKL hsmall hcount,
    hcount⟩