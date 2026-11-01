-- Prove2me | solution 1 for finite_simpleGraph_of_fintype__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:48.193194+00:00
-- url     : https://prove2.me/submissions/546e86c9-40ed-4eb6-bbb0-645713fb4762

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance