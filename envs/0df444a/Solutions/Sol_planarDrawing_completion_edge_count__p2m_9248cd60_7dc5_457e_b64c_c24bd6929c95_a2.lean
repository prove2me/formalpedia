-- Prove2me | solution 1 for planarDrawing_completion_edge_count__p2m_9248cd60_7dc5_457e_b64c_c24bd6929c95_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:16.764358+00:00
-- url     : https://prove2.me/submissions/a842f234-726b-49b6-a79f-18afec0a64fa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_extension__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
import Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawing_edge_count__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ M : SimpleGraph V,
      LE.le L M ∧ HasPlanarDrawingOn M ∧
        3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planarDrawing_maximal_extension__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
      L hL
  obtain hcount :=
    WilliamsonShmoys.maximalPlanarDrawing_edge_count__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
      M hM hV hmax
  exact ⟨M, hLM, hM, hcount⟩
