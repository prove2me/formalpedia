-- Prove2me | solution 1 for planar_simple_face_degree_bound__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:25.27599+00:00
-- url     : https://prove2.me/submissions/482314ac-0f3f-49c1-9b36-45ea89c9388f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_simple_edge_bound_from_drawing__p2m_5ec8fcdd_ba42_4764_bfb5_c1bd9285046d_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H)
    (f : ℕ) (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    3 * f ≤ 2 * H.edgeSet.ncard := by
  have hbound := planar_simple_edge_bound_from_drawing__p2m_5ec8fcdd_ba42_4764_bfb5_c1bd9285046d_a1
    H hV hHconn hHplanar
  omega