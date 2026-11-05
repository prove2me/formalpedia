-- Prove2me | solution 1 for crossing_adjacency_makes_strict_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:41:04.751444+00:00
-- url     : https://prove2.me/submissions/966d3b72-66b3-43a7-bc65-f3bc61c395b3

import Mathlib

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (u v : V) (hG : ¬ G.Adj u v) (hH : H.Adj u v) : G < H := by
  refine lt_of_le_of_ne hGH ?_
  intro hEq
  exact hG (by simpa [hEq] using hH)
