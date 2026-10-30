-- Prove2me | solution 1 for planar_drawingOn_has_supergraph_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:45:26.369473+00:00
-- url     : https://prove2.me/submissions/ba434126-3a94-4826-899d-b69b1d6eb83d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planarDrawingOn_exists_maximal_supergraph
import Theorems.Thm_planarDrawingOn_maximal_supergraph_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V, G <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨L, hGL, hDrawL, hMax⟩ :=
    planarDrawingOn_exists_maximal_supergraph G hDraw
  exact ⟨L, hGL, hDrawL,
    planarDrawingOn_maximal_supergraph_edge_bound L hDrawL hCard hMax⟩