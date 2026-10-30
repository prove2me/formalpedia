-- Prove2me | solution 1 for maximal_planar_drawing_edge_bound__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:41:12.861643+00:00
-- url     : https://prove2.me/submissions/9f059076-59be-4cad-82c6-4e45b311ec23

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_simple_graph_edge_bound__p2m_1b2f5fb4_d124_4d13_b4e3_793d27613e6f_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  exact planar_drawing_simple_graph_edge_bound__p2m_1b2f5fb4_d124_4d13_b4e3_793d27613e6f_a1
    G hDraw hCard