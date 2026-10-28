-- Prove2me | solution 1 for planarDrawingOn_maximal_supergraph_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:33:08.74147+00:00
-- url     : https://prove2.me/submissions/de8fc305-64e4-4504-bdf9-e74927f0345e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_augmentation_to_triangulation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall K : SimpleGraph V, L <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K <= L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨K, hLK, hKDraw, hKcard⟩ :=
    WilliamsonShmoys.planarDrawingOn_augmentation_to_triangulation L hDraw hCard
  have hKL : K <= L := hMax K hLK hKDraw
  have hEq : L = K := le_antisymm hLK hKL
  rw [hEq]
  exact le_of_eq hKcard.symm