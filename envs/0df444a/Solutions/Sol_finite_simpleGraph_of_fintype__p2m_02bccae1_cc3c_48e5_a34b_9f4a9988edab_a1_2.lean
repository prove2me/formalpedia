-- Prove2me | solution 2 for finite_simpleGraph_of_fintype__p2m_02bccae1_cc3c_48e5_a34b_9f4a9988edab_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:09:36.231572+00:00
-- url     : https://prove2.me/submissions/eb1501bc-1f39-4898-a807-ba576afe244d

import Mathlib

theorem solution (V : Type) [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance
