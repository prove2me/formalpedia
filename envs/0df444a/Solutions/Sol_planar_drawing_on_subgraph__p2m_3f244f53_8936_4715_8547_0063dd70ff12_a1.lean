-- Prove2me | solution 1 for planar_drawing_on_subgraph__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:20.846634+00:00
-- url     : https://prove2.me/submissions/b4ef4f17-16e2-40e2-a740-4e03948b1e30

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, h_edges, h_crossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact h_edges u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact h_crossings u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs heq