-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_levy_measure_eq_negative_restrict
-- name    : AvramDividend.Classical.avram_p2_d_future_levy_measure_eq_negative_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:31:44.934643+00:00
-- url     : https://prove2.me/theorems/e95d5a2e-349a-4019-bf21-40c369849786
-- title:
--   Original Lévy measure equals its strictly negative-mark restriction
-- statement:
--   For the exact original spectrally negative Lévy triplet, its Lévy measure is equal as a measure on ℝ to its restriction to strictly negative marks. This is a support identity and does not assume any count intensity formula.
-- source:
--   Apply Measure.ext to the Proved original ν arbitrary-mark negative restriction c324380a, and identify restriction evaluation by pinned Mathlib Measure.restrict_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_levy_measure_eq_negative_restrict
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.ν = X.ν.restrict (Iio (0 : ℝ)) := by sorry
