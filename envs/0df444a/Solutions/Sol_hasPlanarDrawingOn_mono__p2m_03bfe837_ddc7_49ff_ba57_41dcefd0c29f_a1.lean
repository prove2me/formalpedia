-- Prove2me | solution 1 for hasPlanarDrawingOn_mono__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:01.088809+00:00
-- url     : https://prove2.me/submissions/db2c3276-ac64-4fb6-9d05-df7ee5d84bb9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hHG : H ≤ G)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp_inj, h_edges, h_crossings⟩
  refine ⟨p, arc, hp_inj, ?_, ?_⟩
  · intro u v huv hHuv
    exact h_edges u v huv (hHG hHuv)
  · intro u v x y huv hxy hHuv hHxy hne t ht s hs heq
    exact h_crossings u v x y huv hxy (hHG hHuv) (hHG hHxy) hne t ht s hs heq