-- Prove2me | solution 1 for planar_drawing_simple_graph_edge_bound__p2m_1b2f5fb4_d124_4d13_b4e3_793d27613e6f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:09:48.947814+00:00
-- url     : https://prove2.me/submissions/70081765-040b-4c7e-a07c-d633b07366e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_exact_edge_count__p2m_ee2f00f2_33d3_4fa6_ae59_6744e739db8c_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, _, hle, hExact, _⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count__p2m_ee2f00f2_33d3_4fa6_ae59_6744e739db8c_a2
      G hDraw hCard
  rw [hExact] at hle
  exact hle