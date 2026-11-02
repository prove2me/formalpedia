-- Prove2me | solution 1 for maximal_planar_drawing_edge_count__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:32:19.080955+00:00
-- url     : https://prove2.me/submissions/b3765da1-0062-4cbe-987c-2ed21b4e4c57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph__p2m_3aaeb753_8214_46cb_ae23_34cf4eb39be4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    letI : DecidableRel K.Adj := dK
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel K.Adj := dK
  obtain ⟨H, dH, hKH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_3aaeb753_8214_46cb_ae23_34cf4eb39be4_a1
      K dK hK hn
  have hHK : H ≤ K := hmax H dH hKH hH
  have hEq : H = K := le_antisymm hHK hKH
  subst H
  have hd : dH = dK := Subsingleton.elim _ _
  cases hd
  exact hcount