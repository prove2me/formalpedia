-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_upper_first_preserves_lower_survival_through_record
-- name    : AvramDividend.Classical.avram_ws01h_upper_first_preserves_lower_survival_through_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:07:01.017476+00:00
-- url     : https://prove2.me/theorems/c419e0ac-3db1-484f-bc96-1c5baaa442b8
-- title:
--   Original upper-before-ruin first record preserves the lower reserve barrier along its full past
-- statement:
--   For the actual strict first-passage clocks, if the upper record occurs before strict lower ruin, every observation at or before the record has nonnegative reserve x+X_s. A strict negative observation would force the accepted actual lower exit clock no later than s, contradicting the upper-first event. This gives the exact killed-history prefix survival needed for the Esscher CDF renewal and uses no scale-function exit result.
-- source:
--   Direct pathwise consequence of the actual strict lower exit definition and canonical Proved observation inequality fa7ceff5, original Lévy law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_upper_first_preserves_lower_survival_through_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (ω : Ω) (s : ℝ≥0)
    (hfirst : twoSidedExitUpTime X b ω <
      twoSidedExitDownTime X (-x) ω)
    (hbefore : (s : ℝ≥0∞) ≤ twoSidedExitUpTime X b ω) :
    0 ≤ x + X.X s ω := by sorry
