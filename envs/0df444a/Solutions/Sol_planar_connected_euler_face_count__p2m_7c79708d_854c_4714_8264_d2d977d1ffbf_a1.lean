-- Prove2me | solution 1 for planar_connected_euler_face_count__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:11.742067+00:00
-- url     : https://prove2.me/submissions/5fb2917d-3763-4156-91c7-0d9276f9cc64

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_edgeSet_card_ge_card_add_one__p2m_422010ac_e404_45c7_bd98_f3385e323913_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have hE : Fintype.card V ≤ H.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_edgeSet_card_ge_card_add_one__p2m_422010ac_e404_45c7_bd98_f3385e323913_a1 H hHconn
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega