-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ceil_grid_pair_count_le_chronological
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_ceil_grid_pair_count_le_chronological
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:52:55.845596+00:00
-- url     : https://prove2.me/theorems/1a973bbe-0807-4401-ae51-5dd3b9c6649a
-- title:
--   Every original uniform-grid chronological pair count is dominated by the physical pair count
-- statement:
--   For any finite set of observed original jump times, a strict ceiling-index pair must be in strict chronological order, because the ceiling function is monotone under positive uniform-grid scaling. Thus each grid pair count is pathwise bounded by the true full chronological pair count, with no mesh nesting assumption.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_ceil_grid_pair_count_le_chronological
    (F : Finset ℝ≥0) (T : ℝ≥0) (hT : 0 < T) (k : ℕ) :
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card ≤
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by sorry
