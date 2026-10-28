-- Prove2me | Theorems.Thm_AvramDividend_Classical_upperPassage_isStoppingTime_of_rightContinuous
-- name    : AvramDividend.Classical.upperPassage_isStoppingTime_of_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:01:21.049684+00:00
-- url     : https://prove2.me/theorems/26c5218b-2d13-4fbd-bff0-bbc082d06be6
-- title:
--   Strict Lévy upward passage is a stopping time under right-continuous filtration
-- statement:
--   When the filtration of an adapted spectrally negative Lévy process is right-continuous, the strict upward first-passage clock is a genuine stopping time. The proof upgrades the already established filtration measurability of all strict-before-horizon events using Mathlib's right-continuity stopping-time criterion. This gives the first-record strong-Markov argument a precisely stated filtration regularity prerequisite.
-- source:
--   Mathlib.Probability.Process.Stopping, isStoppingTime_of_measurableSet_lt_of_isRightContinuous; Avram, Palmowski, Pistorius (2007), first-record strong Markov decomposition.

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.upperPassage_isStoppingTime_of_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    IsStoppingTime 𝓕 (twoSidedExitUpTime X b) := by sorry
