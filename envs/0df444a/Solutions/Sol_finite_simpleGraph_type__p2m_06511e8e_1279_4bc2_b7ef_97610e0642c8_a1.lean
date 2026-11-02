-- Prove2me | solution 1 for finite_simpleGraph_type__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:45.970726+00:00
-- url     : https://prove2.me/submissions/3381889a-0d60-432a-a6c1-0e01614ae0c8

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance