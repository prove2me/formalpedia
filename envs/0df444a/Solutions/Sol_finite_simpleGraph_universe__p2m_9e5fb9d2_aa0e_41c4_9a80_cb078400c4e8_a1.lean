-- Prove2me | solution 1 for finite_simpleGraph_universe__p2m_9e5fb9d2_aa0e_41c4_9a80_cb078400c4e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:11.143447+00:00
-- url     : https://prove2.me/submissions/5e67d730-c043-47cb-a84f-1d18a900d33c

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  classical
  let encode : SimpleGraph V → (V → V → Bool) := fun G u v => decide (G.Adj u v)
  apply Finite.of_injective encode
  intro G H h
  apply SimpleGraph.ext
  funext u v
  apply propext
  have h' : decide (G.Adj u v) = decide (H.Adj u v) := by
    exact congrFun (congrFun h u) v
  constructor
  · intro hG
    have hb : decide (G.Adj u v) = true := by
      simpa only [decide_eq_true_eq] using hG
    rw [h'] at hb
    simpa only [decide_eq_true_eq] using hb
  · intro hH
    have hb : decide (H.Adj u v) = true := by
      simpa only [decide_eq_true_eq] using hH
    rw [← h'] at hb
    simpa only [decide_eq_true_eq] using hb