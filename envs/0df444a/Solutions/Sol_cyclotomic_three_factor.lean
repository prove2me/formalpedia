-- Prove2me | solution 1 for cyclotomic_three_factor
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T05:41:07.876027+00:00
-- url     : https://prove2.me/submissions/3f69b1a1-4437-4f46-9e7a-0789bf4221bc

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by
  ring
