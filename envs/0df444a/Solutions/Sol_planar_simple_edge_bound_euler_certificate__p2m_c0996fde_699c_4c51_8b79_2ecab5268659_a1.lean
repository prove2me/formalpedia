-- Prove2me | solution 1 for planar_simple_edge_bound_euler_certificate__p2m_c0996fde_699c_4c51_8b79_2ecab5268659_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:51.053685+00:00
-- url     : https://prove2.me/submissions/6e5d5b9d-fa7f-48cf-8481-6a2f10fb7678
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_connected_euler_face_count__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
import Theorems.Thm_planar_simple_face_degree_bound__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    planar_connected_euler_face_count__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
      H hV hHconn hHplanar
  exact ⟨f, hEuler,
    planar_simple_face_degree_bound__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
      H hV hHconn hHplanar f hEuler⟩