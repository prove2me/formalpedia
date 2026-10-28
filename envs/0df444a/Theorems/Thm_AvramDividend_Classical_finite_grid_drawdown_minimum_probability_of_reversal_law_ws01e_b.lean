-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_drawdown_minimum_probability_of_reversal_law_ws01e_b
-- name    : AvramDividend.Classical.finite_grid_drawdown_minimum_probability_of_reversal_law_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:46:28.755489+00:00
-- url     : https://prove2.me/theorems/7b5b78d7-f22e-4874-bf53-e594641064d6
-- title:
--   Finite-grid terminal-drawdown and minimum have identical laws under reversal-invariant increment measures
-- statement:
--   For any measure on finite real-increment vectors whose full vector law is invariant under reversal, the probability that total displacement minus some prefix is at most a equals the probability that some ordinary prefix is at most a, including the empty and full prefixes. The measurable finite-grid distributional identity is a direct corollary of the canonically proved deterministic set-range reversal theorem and applies to genuine equal-mesh Lévy increment laws.
-- source:
--   Elementary deterministic time-reversal of random walks and Lévy finite-dimensional increments; Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1 (https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/scale-review-final.pdf). Builds on accepted 6fa58242-1065-456e-980e-3450dae9487b and b78d5f90-43d4-4229-9f1a-23b5c29a59a7.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

theorem AvramDividend.Classical.finite_grid_drawdown_minimum_probability_of_reversal_law_ws01e_b
    (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) (a : ℝ)
    (hrev : MeasureTheory.Measure.map
      (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ = μ) :
    let w : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) ≤ a} =
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) (w v) ≤ a} := by sorry
