-- Prove2me | solution 1 for planar_simple_edge_bound_from_drawing__p2m_5ec8fcdd_ba42_4764_bfb5_c1bd9285046d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:33.634976+00:00
-- url     : https://prove2.me/submissions/abcafe4c-4c90-4083-9b2d-2a39cc5b89df

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_e3b94d84_a772_4bbe_8d1c_d23630bc7e79_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.planar_drawing_face_data__p2m_e3b94d84_a772_4bbe_8d1c_d23630bc7e79_a2
      H hV hHconn hHplanar
  omega