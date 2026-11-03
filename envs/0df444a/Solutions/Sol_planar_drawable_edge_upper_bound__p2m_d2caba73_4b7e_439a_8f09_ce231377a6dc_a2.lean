-- Prove2me | solution 1 for planar_drawable_edge_upper_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:27:31.474098+00:00
-- url     : https://prove2.me/submissions/8ce2a021-a049-4d97-a5b1-08983fd24b2f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_triangulates_to_maximal_planar__p2m_89c022f5_9981_432e_a40e_914f486e5a7e_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := dK
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : DecidableRel K.Adj := dK
  obtain ⟨K', dK', hsub, hK', hcard⟩ :=
    planar_drawing_triangulates_to_maximal_planar__p2m_89c022f5_9981_432e_a40e_914f486e5a7e_a1
      K dK hK hn
  letI : DecidableRel K'.Adj := dK'
  calc
    K.edgeFinset.card <= K'.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)
    _ = 3 * Fintype.card V - 6 := hcard