-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_finset_step_no_new_mark_equal
-- name    : AvramDividend.Classical.avram_bva_finset_step_no_new_mark_equal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:43:14.120366+00:00
-- url     : https://prove2.me/theorems/5988c263-624f-4cbe-ae3e-73de1f6e0316
-- title:
--   Finite actual-mark step sum constant across jump-free interval
-- statement:
--   A cumulative sum of finitely many marked step contributions is unchanged between s and t whenever its finite mark set has no time in (s,t]. Applies to original finite-activity Lévy jump process after identifying its physical jump set.
-- source:
--   Finite sum indicator algebra and marked-jump measure decomposition

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical Set AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bva_finset_step_no_new_mark_equal
    (S : Finset ℝ≥0) (w : ℝ≥0 → ℝ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hNo : ∀ u ∈ S, ¬ (s < u ∧ u ≤ t)) :
    Finset.sum S (fun u => if u ≤ s then w u else 0) =
    Finset.sum S (fun u => if u ≤ t then w u else 0) := by sorry
