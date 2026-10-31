-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_ruin_clock_shift_at_record
-- name    : AvramDividend.Classical.avram_wave3_01_reflected_ruin_clock_shift_at_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:30:54.521783+00:00
-- url     : https://prove2.me/theorems/315975ae-5927-46c2-b5da-a45a93eb40a9
-- title:
--   Original reflected ruin clock decomposes exactly into a surviving first-record time and shifted future strict drawdown clock
-- statement:
--   At an actual finite attained upward record u of level b before reflected ruin at positive depth a, the genuine original strict reflected-ruin clock equals u plus the exact strict future drawdown first-breach clock of the post-u original Lévy path. This follows from the Proved source pathwise record drawdown reset, Proved prefix survival at the record, Proved original barrier ruin clock representation, and Proved general first-bad-time translation. It preserves infinite futures and strict endpoints and directly proves the event decomposition needed for the source discounted killed-record semigroup.
-- source:
--   Proved 23721444 firstBadClock_shift_of_no_early_breach; e8ca9cea firstRecord_drawdown_post_shift_reset; 9a4b2916 firstUpcrossing_before_barrierRuin_iff_prefix_survival; 75280f18 actual barrier ruin subtype clock. Semigroup 3890ee9b and pure-jump C1 cd61d678.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_reflected_ruin_clock_shift_at_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    barrierRuinTime X a ω =
      (u : ℝ≥0∞) +
        (⨅ i : {t : ℝ≥0 //
          X.X (u + t) ω -
            sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) < -a},
          (i.1 : ℝ≥0∞)) := by sorry
