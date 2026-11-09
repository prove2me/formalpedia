-- Prove2me | solution 1 for e7_real_toNNReal_measurable
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T06:45:13.989734+00:00
-- url     : https://prove2.me/submissions/de307e71-a86f-46a8-b8cf-10ba4edfce6e

import Mathlib

open scoped NNReal

theorem solution : Measurable (fun w : ℝ => w.toNNReal) := by
  simp only [Real.toNNReal]
  exact Measurable.subtype_mk (measurable_id.max measurable_const)
