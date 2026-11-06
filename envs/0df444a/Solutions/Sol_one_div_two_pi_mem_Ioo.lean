-- Prove2me | solution 1 for one_div_two_pi_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:23:37.17994+00:00
-- url     : https://prove2.me/submissions/2e8c46f4-4294-4849-a02f-f7d513b1ebfd

import Mathlib.Analysis.SumIntegralComparisons

open Real Set

theorem solution : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  have hπ : 0 < π := Real.pi_pos
  have hpos : 0 < 1 / (2 * π) := by positivity
  constructor
  · linarith
  · rw [div_lt_one (by positivity : 0 < 2 * π)]
    nlinarith [Real.two_le_pi]
