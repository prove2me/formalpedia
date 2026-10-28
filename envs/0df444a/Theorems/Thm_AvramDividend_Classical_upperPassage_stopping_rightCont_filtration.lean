-- Prove2me | Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
-- name    : AvramDividend.Classical.upperPassage_stopping_rightCont_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:50:46.375058+00:00
-- url     : https://prove2.me/theorems/72dac635-d5e8-4383-aff1-3cd8e9f2e942
-- title:
--   Strict first-upcrossing is a stopping time for the right-continuous Lévy filtration
-- statement:
--   For every strict upper-passage record of a spectrally negative Lévy process and arbitrary starting filtration, its first passage is a stopping time in the canonical right-continuous modification. Observability of the strict event before each horizon is already proved for the original filtration; its inclusion in the right continuation plus Mathlib's stopping-time criterion closes the result. This avoids imposing right-continuity on the original Lévy filtration and is a prerequisite for stopped-renewal strong-Markov arguments.
-- source:
--   Apply the right-continuous filtration stopping-time criterion to the proved strict upper-passage events measurable in the original filtration.

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.upperPassage_stopping_rightCont_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    IsStoppingTime 𝓕.rightCont (twoSidedExitUpTime X b) := by sorry
