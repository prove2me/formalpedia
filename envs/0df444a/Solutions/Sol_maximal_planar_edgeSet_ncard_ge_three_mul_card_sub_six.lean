-- Prove2me | solution 1 for maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:13:37.061271+00:00
-- url     : https://prove2.me/submissions/903d0218-9a79-42a1-9d12-e55b07d49158

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawingOn_has_supergraph_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : forall L : SimpleGraph V, G <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = G)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  obtain ⟨L, hSub, hPlanar, hBound⟩ :=
    planar_drawingOn_has_supergraph_edge_bound G hDraw hCard
  have hEq : L = G := hMax L hSub hPlanar
  simpa [hEq] using hBound