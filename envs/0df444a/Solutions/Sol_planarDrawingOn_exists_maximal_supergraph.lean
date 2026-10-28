-- Prove2me | solution 1 for planarDrawingOn_exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:31:07.550427+00:00
-- url     : https://prove2.me/submissions/15b6a896-9922-4f79-8588-f4fc849884ee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_downward_closed

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ L := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (by
      intro A B hAB hB
      rcases hB with ⟨p, arc, hp, hedge, hcross⟩
      refine ⟨p, arc, hp, ?_, ?_⟩
      · intro u v huv huvB
        exact hedge u v huv (hAB huvB)
      · intro u v x y huv hxy huvB hxyB hne t ht s hs heq
        exact hcross u v x y huv hxy (hAB huvB) (hAB hxyB) hne t ht s hs heq)
    G hDraw