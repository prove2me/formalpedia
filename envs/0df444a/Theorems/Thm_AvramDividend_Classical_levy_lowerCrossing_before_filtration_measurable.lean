-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable
-- name    : AvramDividend.Classical.levy_lowerCrossing_before_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:30:23.751697+00:00
-- url     : https://prove2.me/theorems/335dd834-2ef6-4a67-af94-9309d520c224
-- title:
--   Lower ruin-crossing before a finite horizon is measurable in the Lévy filtration
-- statement:
--   For an adapted right-continuous spectrally negative Lévy process, the occurrence of any strict crossing below a fixed lower threshold before deterministic time T is measurable with respect to the filtration at T. The countable-grid detection theorem reduces the continuous event to a countable union of threshold observations, all made strictly before T and hence measurable in its past filtration. This provides the ruin-side stopped-history event for the killed upper-exit barrier reward.
-- source:
--   Ruin-before-barrier stopped-event prerequisite for child 79978d61-9d1f-4b20-b8a5-114797a8e380 and mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Strengthens ambient chat03_lower_before_horizon_measurable UUID 76ef792f by using Proved countable-grid equivalence UUID 0ec8694a and adaptedness.

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_lowerCrossing_before_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} := by
  sorry
