-- Prove2me | solution 1 for planar_drawing_triangulates_to_maximal_planar__p2m_89c022f5_9981_432e_a40e_914f486e5a7e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:02.616393+00:00
-- url     : https://prove2.me/submissions/e04d7f57-bf8c-4c7b-8a05-6a36083c364d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_planar_drawing_has_maximal_planar_extension__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
import Theorems.Thm_maximal_planar_drawing_edge_count__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    ∃ (K' : SimpleGraph V) (dK' : DecidableRel K'.Adj),
      K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧
        (letI : DecidableRel K'.Adj := dK';
          K'.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨K', dK', hsub, hdraw, hmax⟩ :=
    planar_drawing_has_maximal_planar_extension__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
      K dK hK
  refine ⟨K', dK', hsub, hdraw, ?_⟩
  exact maximal_planar_drawing_edge_count__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
    K' dK' hdraw hn hmax