-- Prove2me | solution 1 for planar_supergraph_edge_lower_bound__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:52.66112+00:00
-- url     : https://prove2.me/submissions/96c16749-3abd-436d-bbae-fa8f6bc4a63a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_maximal_supergraph_exists__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
import Theorems.Thm_planar_edge_count_of_maximal__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ M : SimpleGraph V,
      LE.le L M ∧ HasPlanarDrawingOn M ∧
      LE.le (3 * Fintype.card V) (M.edgeSet.ncard + 6) := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    planar_maximal_supergraph_exists__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1 L hL hV
  exact ⟨M, hLM, hM,
    planar_edge_count_of_maximal__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1 M hM hmax hV⟩