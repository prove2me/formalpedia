-- Prove2me | solution 1 for cyclotomic5_mod5
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:19.277939+00:00
-- url     : https://prove2.me/submissions/0a4e92f1-c99f-4296-abe6-d255e11ada73

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution : ¬ (∀ a b : ℤ, (5 : ℤ) ∣ (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) - (a - b) ^ 4) := by
  intro h
  have h11 := h 1 1
  norm_num at h11
  omega
