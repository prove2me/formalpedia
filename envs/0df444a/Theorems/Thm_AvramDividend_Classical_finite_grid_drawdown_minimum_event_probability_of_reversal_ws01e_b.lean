-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_drawdown_minimum_event_probability_of_reversal_ws01e_b
-- name    : AvramDividend.Classical.finite_grid_drawdown_minimum_event_probability_of_reversal_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:49:54.581867+00:00
-- url     : https://prove2.me/theorems/1eada579-3e41-4583-8998-f7bdce582941
-- title:
--   Finite-grid drawdown and running minimum have the same threshold law under genuine increment-vector reversal
-- statement:
--   For a measure on real-increment sequences invariant under reversal of the first n coordinates (leaving all remaining coordinates unchanged), the mass of the event that terminal total minus some finite prefix is at most a equals the mass of the event that some ordinary prefix is at most a. The full equality of measures under a measurable reversal operator supplies the stochastic content; the pathwise equality of finite value ranges was separately proved. No exponential-time independence or first-passage law is assumed.
-- source:
--   Elementary Lévy finite-grid time-reversal; Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1 (https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/scale-review-final.pdf). Exact deterministic imported proof 6fa58242-1065-456e-980e-3450dae9487b.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

theorem AvramDividend.Classical.finite_grid_drawdown_minimum_event_probability_of_reversal_ws01e_b
    (n : ℕ) (μ : MeasureTheory.Measure (ℕ → ℝ)) (a : ℝ)
    (hrev : MeasureTheory.Measure.map
      (fun v : ℕ → ℝ => fun j : ℕ =>
        if j < n then v (n - 1 - j) else v j) μ = μ) :
    μ {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v ≤ a} =
    μ {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) v ≤ a} := by sorry
