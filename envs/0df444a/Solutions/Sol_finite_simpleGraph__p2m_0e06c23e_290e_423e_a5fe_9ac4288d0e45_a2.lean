-- Prove2me | solution 1 for finite_simpleGraph__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:48:56.509954+00:00
-- url     : https://prove2.me/submissions/6a179e92-b406-446c-9ba6-22b740b44f47

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance