-- Prove2me | solution 1 for planar_drawing_augmentation_edge_bound__p2m_c7182b6b_7db6_44e9_8732_a23951984627_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:01.377293+00:00
-- url     : https://prove2.me/submissions/1a1ccc03-11ee-4023-ac09-b37dea9b35de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_maximal_extension__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
import Theorems.Thm_maximal_planar_edge_bound__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hV : LE.le 3 (Fintype.card V)) :
    Exists fun L : SimpleGraph V => And (LE.le K L) (And (HasPlanarDrawingOn L)
      (LE.le (3 * Fintype.card V) (L.edgeSet.ncard + 6))) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    planar_drawing_maximal_extension__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1 K hK hV
  exact ⟨L, hKL, hL,
    maximal_planar_edge_bound__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1 L hL hV hmax⟩