-- Prove2me | solution 1 for maximal_drawable_graph_has_triangulated_edge_count__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:07:33.529178+00:00
-- url     : https://prove2.me/submissions/71d42405-ecbb-42a2-8e76-8e05049cdba4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_planar_drawable_edge_upper_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
import Theorems.Thm_maximal_drawable_graph_edge_lower_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    ∃ dK : DecidableRel K.Adj,
      letI : DecidableRel K.Adj := dK
      3 * Fintype.card V - 6 = K.edgeFinset.card := by
  classical
  refine ⟨inferInstance, ?_⟩
  letI : DecidableRel K.Adj := inferInstance
  have hupper := planar_drawable_edge_upper_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2 K inferInstance hK hn
  have hlower := maximal_drawable_graph_edge_lower_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2 K inferInstance hK hn hmax
  omega