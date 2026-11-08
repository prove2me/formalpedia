-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_unique_ruin_contact_cell
-- name    : AvramDividend.Classical.avram_bv_strict12_original_unique_ruin_contact_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:37:16.432636+00:00
-- url     : https://prove2.me/theorems/867869c3-5699-4472-a6d2-5aa39cabfa17
-- title:
--   At most one original monotone physical-grid cell can cross ruin time
-- statement:
--   The original monotone dividend verification grid has a unique possible cell with left endpoint strictly before ruin and right endpoint at or after ruin. This justifies isolating the sole raw residual contact correction.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict12_original_unique_ruin_contact_cell
    (u : ℕ → ℝ≥0) (τ : ℝ≥0) (hmono : Monotone u) :
    ∀ i j : ℕ,
      (u i < τ ∧ τ ≤ u (i + 1)) →
      (u j < τ ∧ τ ≤ u (j + 1)) → i = j := by sorry
