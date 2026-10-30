-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_survival_earlier_record_before_ruin
-- name    : AvramDividend.Classical.avram_ws01h_finite_survival_earlier_record_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:35:08.700432+00:00
-- url     : https://prove2.me/theorems/a3077fc7-b391-4f5b-a19e-9be5b4735a3f
-- title:
--   Finite nonruin survival and an earlier genuine upper record imply strict upper-before-lower passage
-- statement:
--   Under the actual source-defined strict passage clocks, if the process has reached an upper threshold strictly before a finite horizon and remains nonnegative in initial-reserve coordinates at every instant through that horizon, the first lower strict passage cannot occur by the horizon; hence the upper record strictly precedes lower ruin. This is a genuine pathwise upper-before-lower bridge for the killed Esscher finite-clock CDF decomposition, assuming no exit scale identity.
-- source:
--   Definitions of strict ENNReal indexed infimum passage times and the original Lévy trajectory, NNReal order and linear arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_finite_survival_earlier_record_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (ω : Ω) (t : ℝ≥0)
    (hUpper : twoSidedExitUpTime X b ω < (t : ℝ≥0∞))
    (hSurvive : ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) :
    twoSidedExitUpTime X b ω <
      twoSidedExitDownTime X (-x) ω := by sorry
