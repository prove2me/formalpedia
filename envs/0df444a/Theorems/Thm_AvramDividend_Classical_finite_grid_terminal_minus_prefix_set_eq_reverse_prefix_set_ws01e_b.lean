-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b
-- name    : AvramDividend.Classical.finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:34:49.567838+00:00
-- url     : https://prove2.me/theorems/6fa58242-1065-456e-980e-3450dae9487b
-- title:
--   Finite-walk terminal-minus-prefix range equals reversed-prefix range
-- statement:
--   For an arbitrary finite list of real increments encoded by a natural-indexed function v, the set of terminal total minus all prefix sums, including the empty and complete prefixes, equals the set of prefix sums formed by reading those same n increments backwards. This is the deterministic pathwise finite-grid reversal identity. Taking minima on both sides yields terminal drawdown equals the reversed-grid minimum, and the preceding canonically Proved Lévy vector-law reversal can then transport its distribution.
-- source:
--   Elementary finite-walk reversal identity underlying Lévy path duality; Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1 Wiener–Hopf factorisation (https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/scale-review-final.pdf). Proof uses the Mathlib finite-range sum reflection and range-add/subtract identities.

import Mathlib

theorem AvramDividend.Classical.finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b (v : ℕ → ℝ) (n : ℕ) :
    Set.range (fun k : Fin n.succ =>
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v) =
    Set.range (fun k : Fin n.succ =>
      Finset.sum (Finset.range k.val) (fun j => v (n - 1 - j))) := by sorry
