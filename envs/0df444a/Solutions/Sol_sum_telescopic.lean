-- Prove2me | solution 1 for sum_telescopic
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:09.968172+00:00
-- url     : https://prove2.me/submissions/88fd9d6d-f4ed-4e3a-9100-e66efd96c7ca

import Mathlib.Analysis.SumIntegralComparisons

open BigOperators

theorem solution (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  exact Finset.sum_range_sub a n
