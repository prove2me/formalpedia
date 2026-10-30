-- Prove2me | solution 1 for finite_simpleGraph_of_fintype__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:01.870774+00:00
-- url     : https://prove2.me/submissions/83cb853f-c89c-4914-b05f-da1674c65100

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance