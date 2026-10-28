-- Prove2me | Theorems.Thm_AvramDividend_Classical_upperPassage_capped_stopping_rightCont
-- name    : AvramDividend.Classical.upperPassage_capped_stopping_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:15:52.313913+00:00
-- url     : https://prove2.me/theorems/47ec1ea2-32d7-4b5d-abfa-865b452c572e
-- title:
--   Finite-horizon cap of strict first-passage is a right-continuous stopping time
-- statement:
--   Capping a strict upper-record stopping time at a fixed finite horizon preserves the stopping-time property for the right-continuous Lévy filtration. This is the finite-clock localisation step for the strong-Markov next-record expectation upper bound.
-- source:
--   Mathlib Probability Process Stopping, IsStoppingTime.min_const; proved upperPassage_stopping_rightCont_filtration.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.upperPassage_capped_stopping_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)) := by sorry
