-- Prove2me | solution 1 for edgeSet_ncard_mono_of_le__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:20.165337+00:00
-- url     : https://prove2.me/submissions/d6be1182-f3a1-4e20-9769-ff652dd4f7eb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (h : LE.le G H) :
    LE.le G.edgeSet.ncard H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h)