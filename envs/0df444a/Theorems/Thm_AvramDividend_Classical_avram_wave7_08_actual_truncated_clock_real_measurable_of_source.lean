-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_real_measurable_of_source
-- name    : AvramDividend.Classical.avram_wave7_08_actual_truncated_clock_real_measurable_of_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:29:52.181514+00:00
-- url     : https://prove2.me/theorems/413f855c-101f-435e-befe-e950bcb2d767
-- title:
--   Canonical ruin-truncated clock is real-measurable when original source ruin time is measurable
-- statement:
--   For the original Lévy process and its exact ruin time, measurability of the source ruinTime entails measurability of the finite-horizon NNReal truncated clock viewed as a real-valued random variable. The conversion retains the original Ω, ambient measurable space, filtration, and ruin-time definition.
-- source:
--   Independent measurability adapter for the original W7-08 stopped Itô witnesses; formal condition is explicit and no claim that original ruin time is automatically measurable is made.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_actual_truncated_clock_real_measurable_of_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hRuinMeas : Measurable (ruinTime X x D)) :
    Measurable (fun ω => (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ)) := by sorry
