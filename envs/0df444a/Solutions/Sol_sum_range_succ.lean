-- Prove2me | solution 1 for sum_range_succ
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:34.356202+00:00
-- url     : https://prove2.me/submissions/96571dfe-d77e-49bb-a944-62e5e222d3e6

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Real BigOperators

theorem solution (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  rw [Finset.sum_range_succ']
  abel
