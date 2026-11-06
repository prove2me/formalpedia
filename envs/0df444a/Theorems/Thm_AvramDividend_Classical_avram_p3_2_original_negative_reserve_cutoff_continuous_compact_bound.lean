-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_negative_reserve_cutoff_continuous_compact_bound
-- name    : AvramDividend.Classical.avram_p3_2_original_negative_reserve_cutoff_continuous_compact_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:32:58.938216+00:00
-- url     : https://prove2.me/theorems/66f5ea06-8d13-46f7-8f4e-585fe6226827
-- title:
--   Source-continuous value with negative-reserve zero extension uniformly bounded below a cap
-- statement:
--   The exact original dividend verification value w, continuous on nonnegative reserves and zero on negative reserves, admits a uniform nonnegative magnitude bound for all real post-jump states y below any finite upper reserve ceiling b. This removes an extra global boundedness hypothesis from the original nonlinear negative-jump kernel envelope, including jumps that cross ruin.
-- source:
--   Original value assumptions hw_cont and hw_neg; compactness of Icc 0 b, IsCompact.exists_bound_of_continuousOn, and zero extension on negative reserves.

import Mathlib

open Set
noncomputable section

/-- Continuity on nonnegative reserves and zero extension below ruin supply
a uniform bound on every state reached after a negative original jump. -/

theorem AvramDividend.Classical.avram_p3_2_original_negative_reserve_cutoff_continuous_compact_bound
    (w : ℝ → ℝ) (b : ℝ)
    (hw_cont : ContinuousOn w (Set.Ici (0 : ℝ)))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ y : ℝ, y ≤ b → |w y| ≤ R := by sorry
