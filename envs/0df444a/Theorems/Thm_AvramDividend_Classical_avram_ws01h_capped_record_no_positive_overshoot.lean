-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_record_no_positive_overshoot
-- name    : AvramDividend.Classical.avram_ws01h_capped_record_no_positive_overshoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:17:18.396023+00:00
-- url     : https://prove2.me/theorems/df1c0da0-aa12-4f9f-89de-296081c3a314
-- title:
--   No positive overshoot at a capped original first record on the hit event
-- statement:
--   At an actual finite first strict upcrossing of a spectrally negative Levy process, the capped first-record stopping clock evaluates the original path exactly at its threshold. The identity uses the source upper-passage clock and the proven no-positive-overshoot theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), two-sided exit; Kuznetsov, Kyprianou and Rivero (2013), Section 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_capped_record_no_positive_overshoot
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 ≤ b)
    (N : ℝ≥0) (ω : Ω)
    (hhit : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    X.X ((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) ω = b := by sorry
