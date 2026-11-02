-- Prove2me | solution 1 for simpleGraph_edgeFinset_card_lt_of_le_of_ne__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:53:43.575919+00:00
-- url     : https://prove2.me/submissions/b1f04b89-7475-4fcd-a208-e9ffa140cac0

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (hne : G ≠ H) :
    G.edgeFinset.card < H.edgeFinset.card := by
  exact Finset.card_lt_card <|
    (SimpleGraph.edgeFinset_ssubset_edgeFinset).2 (lt_of_le_of_ne hle hne)