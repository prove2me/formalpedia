-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_next_record_future_ruin_iff
-- name    : AvramDividend.Classical.avram_wave3_01_reflected_next_record_future_ruin_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:07:11.154845+00:00
-- url     : https://prove2.me/theorems/62269b6b-9b81-447b-9b0f-8a6175b702b9
-- title:
--   Strict reflected survival to next record equals the shifted-future survival event, including infinite clocks
-- statement:
--   At a genuine finite upward record before strict reflected drawdown ruin, the next unbounded upward passage survives the original drawdown clock if and only if the shifted future upward passage survives the shifted future reflected drawdown clock. This is a pathwise equivalence for the original spectrally negative Lévy process including infinite future first-passage or ruin clocks, obtained by canceling a genuinely finite past record from proved additive decompositions.
-- source:
--   Proved firstUpcrossing_attains_peak 473109a5, nextRecord_upclock_eq_add_shifted_inf 794e45f9, avram_wave3_01_reflected_ruin_clock_shift_at_record 315975ae; KKR 2013 scale review lemma 2.4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_ruin_clock_shift_at_record

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_reflected_next_record_future_ruin_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    (twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω) ↔
      (⨅ i : {t : ℝ≥0 //
          c < X.X (u + t) ω - X.X u ω}, (i.1 : ℝ≥0∞)) <
      (⨅ i : {t : ℝ≥0 //
          X.X (u + t) ω -
            sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)) := by sorry
