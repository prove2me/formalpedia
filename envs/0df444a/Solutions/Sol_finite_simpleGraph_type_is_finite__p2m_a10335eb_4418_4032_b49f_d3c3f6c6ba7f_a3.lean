-- Prove2me | solution 1 for finite_simpleGraph_type_is_finite__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:17.726207+00:00
-- url     : https://prove2.me/submissions/3c2214ec-bc72-4470-b606-80cf89b3c85a

import Mathlib

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance