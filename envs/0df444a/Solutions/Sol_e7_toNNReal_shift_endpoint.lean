-- Prove2me | solution 1 for e7_toNNReal_shift_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T06:54:35.855597+00:00
-- url     : https://prove2.me/submissions/c15d2c67-ca63-47e1-9883-ef20776d9cf3

import Mathlib

open scoped NNReal

theorem solution {u v : ℝ≥0} (huv : u ≤ v) :
    (((u : ℝ) + ((v : ℝ) - (u : ℝ))).toNNReal) = v := by
  simp
