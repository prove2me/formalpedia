-- Prove2me | solution 1 for one_add_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:50:30.890787+00:00
-- url     : https://prove2.me/submissions/5c43aa05-bb46-40d6-a01c-527076edf78c

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

theorem solution (u : ℝ) : 0 < 1 + u ^ 2 := by
  nlinarith [sq_nonneg u]
