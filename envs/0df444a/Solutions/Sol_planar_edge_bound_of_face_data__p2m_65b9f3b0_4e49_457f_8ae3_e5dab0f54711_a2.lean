-- Prove2me | solution 1 for planar_edge_bound_of_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:19.871403+00:00
-- url     : https://prove2.me/submissions/34f0fe26-8233-4a36-afa2-534345f7f03b

import Mathlib

set_option autoImplicit false

theorem solution (n f m : Nat) (hn : 3 ≤ n)
    (heuler : n + f = m + 2)
    (hfaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by
  omega