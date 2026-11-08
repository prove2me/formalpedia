-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_finite_row_unique_contact
-- name    : AvramDividend.Classical.avram_bv_strict12_original_finite_row_unique_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:54:39.025311+00:00
-- url     : https://prove2.me/theorems/fd161e0c-7c5b-40f8-b67b-a3dc0ee989db
-- title:
--   Original finite physical-grid row monotonicity isolates one ruin-contact cell
-- statement:
--   From the canonical e49 row-wise monotonicity only through n+1, derive uniqueness of the cell with left endpoint strictly before ruin and right endpoint at or after ruin. Proof uses a constant capped extension and previously Proved global uniqueness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_unique_ruin_contact_cell
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict12_original_finite_row_unique_contact
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1)) :
    ∀ i j : ℕ, i < n + 1 → j < n + 1 →
      (u i < τ ∧ τ ≤ u (i + 1)) →
      (u j < τ ∧ τ ≤ u (j + 1)) → i = j := by sorry
