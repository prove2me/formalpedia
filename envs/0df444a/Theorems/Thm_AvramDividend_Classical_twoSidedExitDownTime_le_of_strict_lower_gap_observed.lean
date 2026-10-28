-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed
-- name    : AvramDividend.Classical.twoSidedExitDownTime_le_of_strict_lower_gap_observed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:07:23.572738+00:00
-- url     : https://prove2.me/theorems/fa7ceff5-37e3-4a61-8ee2-60a7dc1416fc
-- title:
--   Strict lower passage clock is bounded by a downcrossing of the negative initial-reserve gap
-- statement:
--   If the centred Lévy process has fallen below the level -x at observation time s, its canonical strict lower first-passage clock with threshold -x is no later than s. The threshold argument is deliberately -x, matching the process-side inequality exactly. This corrects a prior mis-specified auxiliary clock statement that used threshold x and was mathematically false without an extra order hypothesis.
-- source:
--   Definition of twoSidedExitDownTime as nested infimum over crossing instants; order bounds for nested indexed infima.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_le_of_strict_lower_gap_observed
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (s : ℝ≥0)
    (hs : X.X s ω < -x) :
    twoSidedExitDownTime X (-x) ω ≤ (s : ℝ≥0∞) := by sorry
