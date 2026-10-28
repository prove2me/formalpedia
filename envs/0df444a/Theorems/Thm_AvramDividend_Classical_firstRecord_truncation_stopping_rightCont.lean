-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
-- name    : AvramDividend.Classical.firstRecord_truncation_stopping_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:02:51.359066+00:00
-- url     : https://prove2.me/theorems/ac9470f5-bf7c-4d9b-8b69-cade04431f46
-- title:
--   Finite-horizon first-record clock is a finite stopping time in the right-continuous filtration
-- statement:
--   For every strict Lévy first-record time, truncate the extended clock at a finite deterministic horizon M and convert the result to a finite nonnegative time. The resulting clock has measurable before-s events at every right-continuous filtration time. This is the exact finite-clock prerequisite for strong-Markov factorisation of the killed next-record reward, without assuming original-filtration right-continuity.
-- source:
--   Apply the proved generic extended-stopping-time truncation theorem to the proved right-continuous first-upcrossing stopping time.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_extendedStopping_truncate_finite_leEvents

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstRecord_truncation_stopping_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (M : ℝ≥0) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s]
        {ω : Ω | (min (twoSidedExitUpTime X b ω) (M : ℝ≥0∞)).toNNReal ≤ s} := by sorry
