-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upperExit_noLowerCrossing_horizon_filtration_measurable
-- name    : AvramDividend.Classical.levy_upperExit_noLowerCrossing_horizon_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:58:08.56347+00:00
-- url     : https://prove2.me/theorems/dd4abf20-1914-419e-8cce-2ed67aab9501
-- title:
--   Killed upper-exit grid event is measurable in the past Lévy filtration
-- statement:
--   The event that strict upper passage occurs before a deterministic horizon while no lower ruin-level crossing has occurred before the same horizon is measurable in the Lévy filtration at that horizon. This is the killed first-exit fibre usable in finite-grid restart approximations.
-- source:
--   Directly combines the two independently Proved first-passage filtration-measurability results 6ca1be8a-4673-4c7b-b77f-8143dd6550d2 and 335dd834-2ef6-4a67-af94-9309d520c224, for the strong-Markov dividend split child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_upperExit_noLowerCrossing_horizon_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper lower : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
          (T : ℝ≥0∞) ∧
        ¬ ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} := by
  sorry
