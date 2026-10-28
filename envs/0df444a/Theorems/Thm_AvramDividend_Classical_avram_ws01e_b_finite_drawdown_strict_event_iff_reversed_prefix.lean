-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_drawdown_strict_event_iff_reversed_prefix
-- name    : AvramDividend.Classical.avram_ws01e_b_finite_drawdown_strict_event_iff_reversed_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:33:17.459018+00:00
-- url     : https://prove2.me/theorems/bb8fa832-72b8-49e1-ae61-677b8bb4f065
-- title:
--   Finite-grid terminal drawdown strict-threshold event equals reversed-prefix strict-threshold event
-- statement:
--   For any real increment sequence v, finite grid length n and real threshold a, there exists a prefix k with terminal total minus the k-prefix below a exactly when some prefix of the reversed n increments has sum below a. This is the strict threshold version of the already accepted exact finite-grid set-range reversal identity, and is the event-level combinatorial tool needed to convert Esscher-invariant finite-grid increment law into drawdown/minimum symmetry.
-- source:
--   Canonically Proved finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b (6fa58242), direct membership of equal set ranges.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

open AvramDividend.Classical Finset Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_finite_drawdown_strict_event_iff_reversed_prefix (v : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    (∃ k : Fin n.succ,
      (∑ j ∈ Finset.range n, v j) -
        (∑ j ∈ Finset.range k.val, v j) < a) ↔
    (∃ k : Fin n.succ,
      (∑ j ∈ Finset.range k.val, v (n - 1 - j)) < a) := by sorry
