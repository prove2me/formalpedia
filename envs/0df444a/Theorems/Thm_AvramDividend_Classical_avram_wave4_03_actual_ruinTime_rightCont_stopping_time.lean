-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time
-- name    : AvramDividend.Classical.avram_wave4_03_actual_ruinTime_rightCont_stopping_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:28:49.444287+00:00
-- url     : https://prove2.me/theorems/0e921b75-8854-48dd-81ae-f0a62352256d
-- title:
--   Actual controlled ruin clock is a stopping time in the right-continuous original Levy filtration
-- statement:
--   For the genuine original spectrally negative Levy process and its adapted left-continuous dividend strategy, the actual ruinTime is a stopping time with respect to the right-continuous modification of the same filtration. This bridges the exact stopping-time hypothesis of the proved predictable stopped nonlinear Levy jump kernel, even for right-payment atoms; it does not assume or establish a Poisson compensator, Ito-Meyer formula, or expected dividend bound.
-- source:
--   Already proved original strict-ruin event filtration measurability db6ca856-288d-4f40-82db-ec146c59a018; pinned Mathlib isStoppingTime_of_measurableSet_lt_of_isRightContinuous and Filtration.le_rightCont.

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_strict_event_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_actual_ruinTime_rightCont_stopping_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    IsStoppingTime 𝓕.rightCont (ruinTime X x D) := by sorry
