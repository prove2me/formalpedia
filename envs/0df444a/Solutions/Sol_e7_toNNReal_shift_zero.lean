-- Prove2me | solution 1 for e7_toNNReal_shift_zero
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T06:45:08.054361+00:00
-- url     : https://prove2.me/submissions/3ad3dc6c-eb60-4027-aed2-2919195e6f48

import Mathlib

open scoped NNReal

theorem solution (u : ℝ≥0) : (((u : ℝ) + 0).toNNReal) = u := by
  simp
