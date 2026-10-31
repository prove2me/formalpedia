-- Prove2me | solution 1 for planar_simple_edge_bound__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:10.763505+00:00
-- url     : https://prove2.me/submissions/e87996a2-c69c-4c01-8c57-b5c2e4375157

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_simple_edge_bound_euler_certificate__p2m_c0996fde_699c_4c51_8b79_2ecab5268659_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, heuler, hfaceDegree⟩ :=
    planar_simple_edge_bound_euler_certificate__p2m_c0996fde_699c_4c51_8b79_2ecab5268659_a1
      H hV hHconn hHplanar
  omega
