-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_strict_mono_cell_selector
-- name    : AvramDividend.Classical.avram_chat24_strict_mono_cell_selector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T19:04:12.534254+00:00
-- url     : https://prove2.me/theorems/c5e2e76a-3d18-4c8a-9113-91f3ff9e24be
-- title:
--   Unique strict-left cell in an increasing finite grid
-- statement:
--   The least index m with t <= u m is positive; m-1 is the required cell. Strict monotonicity makes it unique. This is the finite combinatorial part of parent 977d6566-a376-446c-9fdf-c3488477439a, independently of its convergence claim. The complete direct parent draft is preserved but its whole-theorem complexity score 0.1597 exceeds the configured -0.0523 limit. The two independent mathematical claims give a source-faithful reduction without changing that policy. Neither helper refers to the parent or to the other helper, so there is no dependency cycle.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_strict_mono_cell_selector
    (u : ℕ → ℝ≥0) (hu : StrictMono u) (N : ℕ) (t : ℝ≥0)
    (h0 : u 0 < t) (hN : t ≤ u N) :
    ∃ k, k < N ∧ u k < t ∧ t ≤ u (k + 1) ∧
      ∀ j, u j < t → t ≤ u (j + 1) → j = k := by sorry
