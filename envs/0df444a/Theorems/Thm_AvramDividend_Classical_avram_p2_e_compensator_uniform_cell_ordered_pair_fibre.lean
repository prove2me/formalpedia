-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_ordered_pair_fibre
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_ordered_pair_fibre
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:47:36.214346+00:00
-- url     : https://prove2.me/theorems/497f4771-35d5-4407-970d-af91d570785d
-- title:
--   Every ordered original finite jump-time pair crosses its second time's uniform cell
-- statement:
--   Once original finite marked-jump times occupy distinct half-open uniform grid cells, each strictly ordered pair belongs to the physical past/future crossing set of the second time's cell.
-- source:
--   Proved source-independent P2-E strict physical-time cell index order helper and interval endpoint arithmetic; feeds original source chronological-pair fibre union and Fatou limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_idx_strict_order

open Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_ordered_pair_fibre
    (F : Finset ℝ≥0) (δ : ℝ≥0) (idx : ℝ≥0 → ℕ)
    (hcell : ∀ u ∈ F,
      (idx u : ℝ≥0) * δ < u ∧
      u ≤ (((idx u + 1 : ℕ) : ℝ≥0) * δ))
    (hinj : Set.InjOn idx (F : Set ℝ≥0)) :
    ∀ u ∈ F, ∀ v ∈ F, u < v →
      u ≤ (idx v : ℝ≥0) * δ ∧
      (idx v : ℝ≥0) * δ < v ∧
      v ≤ (((idx v + 1 : ℕ) : ℝ≥0) * δ) := by sorry
