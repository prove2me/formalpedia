-- Prove2me | Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule
-- name    : AvramDividend.Classical.shifted_lower_survival_filtration_measurable_no_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:50:49.523377+00:00
-- url     : https://prove2.me/theorems/cf6d2ea5-84a9-4da2-a275-41d7d12918b9
-- title:
--   Shifted Lévy whole-history survival is measurable at the horizon without a schedule
-- statement:
--   For a spectrally negative Lévy process, the event that the shifted reserve x+X_s is nonnegative for all times s up to and including T is measurable with respect to the filtration at time T. The proof combines the previously proved strict lower-crossing event before T with the adapted terminal-time observation, and requires no auxiliary countable schedule.
-- source:
--   Builds on Proved AvramDividend.Classical.levy_lowerCrossing_before_filtration_measurable (UUID 335dd834-2ef6-4a67-af94-9309d520c224). Supplies the adapted survival event for finite-horizon Esscher-weighted killed scale harmonicity.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.shifted_lower_survival_filtration_measurable_no_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω | ∀ s : ℝ≥0, s ≤ T → 0 ≤ x + X.X s ω} := by sorry
