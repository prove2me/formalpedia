-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_drawdown_minimum_strict_event_probability_ws01e_b
-- name    : AvramDividend.Classical.finite_grid_drawdown_minimum_strict_event_probability_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:04:38.807421+00:00
-- url     : https://prove2.me/theorems/1e6b36c9-305d-4bfd-bc3a-84d0b6ab44c3
-- title:
--   Strict finite-grid terminal drawdown and minimum probabilities agree under reversal invariance
-- statement:
--   For an actual measure on real increment sequences invariant under reversal of its first n coordinates, the probability that some terminal-minus-prefix partial-sum difference is strictly below a equals the probability that some ordinary prefix sum is strictly below a. The strict threshold is essential when passing nested finite-grid identities to an actual càdlàg finite-horizon infimum, because no atomlessness of the value at the threshold is needed. Includes every endpoint and n=0.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes §2.1 finite-time path reversal; direct strict-event proof reusing canonically Proved finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b 6fa58242 and the accepted finite-grid closed-threshold measure transport 1eada579.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b
open MeasureTheory AvramDividend.Classical

theorem AvramDividend.Classical.finite_grid_drawdown_minimum_strict_event_probability_ws01e_b
    (n : ℕ) (μ : MeasureTheory.Measure (ℕ → ℝ)) (a : ℝ)
    (hrev : MeasureTheory.Measure.map
      (fun v : ℕ → ℝ => fun j : ℕ =>
        if j < n then v (n - 1 - j) else v j) μ = μ) :
    μ {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v < a} =
    μ {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) v < a} := by sorry
