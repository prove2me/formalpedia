-- Prove2me | solution 1 for drawable_graph_edge_bound__p2m_d1879139_c8f2_40b8_b730_a1c2d5f0f3db_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:37:05.817904+00:00
-- url     : https://prove2.me/submissions/5af65826-b063-414a-89b7-e160f15b747e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  exact WilliamsonShmoys.drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1 M hM hn
