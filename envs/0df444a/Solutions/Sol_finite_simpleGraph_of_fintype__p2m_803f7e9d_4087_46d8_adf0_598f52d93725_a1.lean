-- Prove2me | solution 1 for finite_simpleGraph_of_fintype__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:31.334384+00:00
-- url     : https://prove2.me/submissions/898d6ec2-f471-41e2-a75b-dd7981f35204

import Mathlib

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  classical
  apply Finite.of_injective (fun G : SimpleGraph V => fun v w => decide (G.Adj v w))
  intro G H h
  ext v w
  have hAdj : decide (G.Adj v w) = decide (H.Adj v w) := by
    exact congrFun (congrFun h v) w
  by_cases hG : G.Adj v w
  all_goals by_cases hH : H.Adj v w
  all_goals simp [hG, hH] at hAdj
  all_goals simp [hG, hH]