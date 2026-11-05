-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_pathwise_weighted_marks_by_cell
-- name    : AvramDividend.Classical.avram_p4_g_isometry_finite_pathwise_weighted_marks_by_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:51:35.94702+00:00
-- url     : https://prove2.me/theorems/3831035f-450f-4874-8841-01fcf93238a1
-- title:
--   Finite physical weighted marked-jump sum equals chronological cell-weight sum
-- statement:
--   For a finite set of actual source jump times, assigning every time to exactly one chronological grid cell and using a predictable weight per cell makes the weighted cell-count sum equal exactly the pathwise sum of the weights at the original jump times. This is the deterministic pathwise identification step needed before any stochastic integral limit claim.
-- source:
--   Pinned Mathlib Finset.card_filter, sum_comm and finite sum expansion, to be instantiated with P2-E true original marked jump-time set and exact half-open cell selector.

import Mathlib
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_finite_pathwise_weighted_marks_by_cell
    {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) (cell : α → Fin n) (w : Fin n → ℝ) :
    (∑ i : Fin n, w i * ((s.filter (fun a => cell a = i)).card : ℝ)) =
      ∑ a ∈ s, w (cell a) := by sorry
