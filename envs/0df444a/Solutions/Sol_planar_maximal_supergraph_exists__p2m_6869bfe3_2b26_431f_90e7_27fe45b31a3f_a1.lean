-- Prove2me | solution 1 for planar_maximal_supergraph_exists__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:17:23.391302+00:00
-- url     : https://prove2.me/submissions/559cb02c-ae24-46b8-b9a5-3f05219f1493

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_simpleGraph_extension__p2m_7fd45cf3_e203_47de_9dbd_2f0909dacdf1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ M : SimpleGraph V,
      LE.le L M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, HasPlanarDrawingOn N → LE.le M N → LE.le N M := by
  obtain ⟨M, hLM, hPM, hmax⟩ :=
    finite_maximal_simpleGraph_extension__p2m_7fd45cf3_e203_47de_9dbd_2f0909dacdf1_a1
      (fun G => LE.le L G ∧ HasPlanarDrawingOn G) L ⟨le_rfl, hL⟩
  exact ⟨M, hLM, hPM.2, fun N hN hMN =>
    hmax N ⟨LE.le.trans hLM hMN, hN⟩ hMN⟩