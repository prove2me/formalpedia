-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB39_original_continuity_away_from_zero
-- name    : AvramDividend.Classical.avram_bva_capHJB39_original_continuity_away_from_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:21:21.548409+00:00
-- url     : https://prove2.me/theorems/4d1ee944-38ce-4560-995c-18b913ffa7af
-- title:
--   Original Avram candidate is continuous at every nonzero reserve
-- statement:
--   A candidate continuous on nonnegative reserves and identically zero on strictly negative reserves is continuous at every nonzero real reserve. At negative values it is locally constant zero, and at positive values continuous within the positive halfline extends to ordinary continuity. This is precisely the candidate regularity needed by source-original Standing BV negative-mark atomlessness at the zero reserve crossing.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB39_original_continuity_away_from_zero
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (r : ℝ) (hr : r ≠ 0) :
    ContinuousAt w r := by sorry
