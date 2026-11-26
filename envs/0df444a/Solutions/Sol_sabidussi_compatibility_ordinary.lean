-- Prove2me | solution 1 for sabidussi_compatibility_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:23:36.982177+00:00
-- url     : https://prove2.me/submissions/e98a4da5-d11f-4ce8-976c-3c4768cbf7ed

import Definitions.Def_Sabidussi
import Definitions.Def_Sabidussi_Solution
import Theorems.Thm_Sabidussi_LoopMultigraph_loop_sabidussi_compatibility_ordinary


set_option autoImplicit true

theorem _root_.solution
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Sabidussi.LoopMultigraph V E} (T : G.EulerTour)
    (hmin : ∀ v : V, 4 ≤ G.degree v) :
    ∃ S : G.OrdinaryCircuitDecomposition, S.Compatible T := by
  exact Sabidussi.LoopMultigraph.loop_sabidussi_compatibility_ordinary T hmin
