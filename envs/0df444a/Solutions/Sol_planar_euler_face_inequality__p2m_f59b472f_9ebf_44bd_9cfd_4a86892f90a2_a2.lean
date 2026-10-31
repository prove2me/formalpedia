-- Prove2me | solution 1 for planar_euler_face_inequality__p2m_f59b472f_9ebf_44bd_9cfd_4a86892f90a2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:30.580508+00:00
-- url     : https://prove2.me/submissions/b7b44d25-bd54-4cb2-b5e7-6affe8dfeac2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_euler_face_count__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
import Theorems.Thm_planar_simple_edge_bound__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ := planar_euler_face_count__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
    H hV hHconn hHplanar
  have hEdge := planar_simple_edge_bound__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
    H hV hHconn hHplanar
  refine ⟨f, hEuler, ?_⟩
  omega
