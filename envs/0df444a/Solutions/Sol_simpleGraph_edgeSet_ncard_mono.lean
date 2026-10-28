-- Prove2me | solution 1 for simpleGraph_edgeSet_ncard_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:02:20.94983+00:00
-- url     : https://prove2.me/submissions/00275e10-1cab-465e-9515-ede256974c2c

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono h)