-- Prove2me | solution 1 for planar_drawing_edgeSet_ncard_le_three_mul_card_sub_six
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:26:39.577346+00:00
-- url     : https://prove2.me/submissions/97fad655-9170-4e13-abc4-f5c3981a8b74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_has_maximal_planar_extension__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
import Theorems.Thm_maximal_planar_drawing_edge_bound__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
import Theorems.Thm_simpleGraph_edgeSet_ncard_le_of_le__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  rcases planar_drawing_has_maximal_planar_extension__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
      G hDraw with
    ⟨H, hEdge, hDrawH, hMax⟩
  have hBound :
      H.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
    maximal_planar_drawing_edge_bound__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
      H hDrawH hMax hCard
  exact simpleGraph_edgeSet_ncard_le_of_le__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
    G H hEdge (3 * Fintype.card V - 6) hBound