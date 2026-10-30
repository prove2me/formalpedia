-- Prove2me | solution 1 for maximal_planar_drawing_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:12:29.236214+00:00
-- url     : https://prove2.me/submissions/e9e5a6f4-0897-4be4-9587-81043ca4935b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_maximal_planar_drawing_edge_bound__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3

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
  first
  | exact _root_.maximal_planar_drawing_edge_bound__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
  | (apply _root_.maximal_planar_drawing_edge_bound__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3 <;> assumption)
  | (intros; apply _root_.maximal_planar_drawing_edge_bound__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3 <;> assumption)
