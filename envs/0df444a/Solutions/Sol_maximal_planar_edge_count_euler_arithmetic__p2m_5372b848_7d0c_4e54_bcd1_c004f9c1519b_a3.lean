-- Prove2me | solution 1 for maximal_planar_edge_count_euler_arithmetic__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:57.634598+00:00
-- url     : https://prove2.me/submissions/fe20c37c-569b-4462-933a-a67c5a09e02f

import Mathlib
set_option autoImplicit false

theorem solution (n e f : ℕ) (hEuler : n + f = e + 2) (hFaces : 3 * f = 2 * e) : 3 * n ≤ e + 6 := by
  omega