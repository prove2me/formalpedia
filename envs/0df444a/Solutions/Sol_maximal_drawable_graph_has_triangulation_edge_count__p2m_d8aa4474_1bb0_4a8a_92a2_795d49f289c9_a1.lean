-- Prove2me | solution 1 for maximal_drawable_graph_has_triangulation_edge_count__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:14:47.853273+00:00
-- url     : https://prove2.me/submissions/050215cb-b641-4245-84db-e9f7d7c29273
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_drawable_graph_edge_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
import Theorems.Thm_maximal_drawable_graph_edge_lower_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J → M ≤ J → J ≤ M)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hlow := maximal_drawable_graph_edge_lower_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
    M hM hmax hn
  have hupp := drawable_graph_edge_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
    M hM hn
  omega