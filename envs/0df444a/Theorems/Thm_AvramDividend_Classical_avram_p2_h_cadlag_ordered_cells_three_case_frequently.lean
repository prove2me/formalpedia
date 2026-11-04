-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_ordered_cells_three_case_frequently
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_ordered_cells_three_case_frequently
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:43:16.113333+00:00
-- url     : https://prove2.me/theorems/9738f407-2826-4bd0-bbf9-356196f0930b
-- title:
--   Finite pigeonhole for the three sides of a shrinking observation cell
-- statement:
--   For any ordered endpoints a_n≤b_n of nonnegative-time intervals and fixed time t, at least one of three exact positional alternatives occurs arbitrarily far along n: the cell lies strictly to the left, lies weakly to the right, or genuinely straddles t with t included as the right endpoint. This finite-pigeonhole ingredient supports the compactness contradiction for absence of spurious cadlag mesh jumps and assigns equality at the left endpoint to the right-side case.

import Mathlib

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_ordered_cells_three_case_frequently
    (a b : ℕ → ℝ≥0) (t : ℝ≥0)
    (hab : ∀ n, a n ≤ b n) :
    (∃ᶠ n in atTop, b n < t) ∨
    (∃ᶠ n in atTop, t ≤ a n) ∨
    (∃ᶠ n in atTop, a n < t ∧ t ≤ b n) := by sorry
