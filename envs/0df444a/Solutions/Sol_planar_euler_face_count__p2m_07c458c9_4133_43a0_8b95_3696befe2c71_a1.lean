-- Prove2me | solution 1 for planar_euler_face_count__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:44:35.264875+00:00
-- url     : https://prove2.me/submissions/372f5b46-875e-4524-bf84-be4c4ca98b22

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_ac816c5dcb924d25
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 :=
  WilliamsonShmoys.planar_drawing_euler_face_count_ac816c5dcb924d25 H hV hHconn hHplanar
