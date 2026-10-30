-- Prove2me | solution 1 for finite_simplegraph__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:39:16.767799+00:00
-- url     : https://prove2.me/submissions/f4fad2ea-9fc7-4424-b356-15ee2db5ce42

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  classical
  let encode : SimpleGraph V → (V → V → Bool) := fun G v w => decide (G.Adj v w)
  apply Finite.of_injective encode
  intro G H h
  apply SimpleGraph.ext
  funext v w
  apply propext
  constructor
  · intro hG
    have hEq := congrFun (congrFun h v) w
    change decide (G.Adj v w) = decide (H.Adj v w) at hEq
    exact of_decide_eq_true (by simpa [hG] using hEq.symm)
  · intro hH
    have hEq := congrFun (congrFun h v) w
    change decide (G.Adj v w) = decide (H.Adj v w) at hEq
    exact of_decide_eq_true (by simpa [hH] using hEq)