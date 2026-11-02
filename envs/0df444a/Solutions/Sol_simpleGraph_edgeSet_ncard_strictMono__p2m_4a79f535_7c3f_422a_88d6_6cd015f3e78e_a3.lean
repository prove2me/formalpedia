-- Prove2me | solution 1 for simpleGraph_edgeSet_ncard_strictMono__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:15.212273+00:00
-- url     : https://prove2.me/submissions/845694f3-8bc2-427c-9e03-628a4cbda6a6

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G K : SimpleGraph V) (hGK : G ≤ K) (hne : G ≠ K) : G.edgeSet.ncard < K.edgeSet.ncard := by
  classical
  exact Set.ncard_lt_ncard
    (SimpleGraph.edgeSet_ssubset_edgeSet.mpr (lt_of_le_of_ne hGK hne))
    (Set.toFinite K.edgeSet)