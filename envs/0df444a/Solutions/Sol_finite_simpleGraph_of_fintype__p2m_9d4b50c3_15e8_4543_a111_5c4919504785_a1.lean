-- Prove2me | solution 1 for finite_simpleGraph_of_fintype__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:52.682749+00:00
-- url     : https://prove2.me/submissions/7317457f-0e04-4bc3-bb0f-5aa65d8c0ec5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance