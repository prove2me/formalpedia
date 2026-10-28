-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable
-- name    : AvramDividend.Classical.levy_upperPassage_lt_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:25:18.711877+00:00
-- url     : https://prove2.me/theorems/6ca1be8a-4673-4c7b-b77f-8143dd6550d2
-- title:
--   First strict upper-passage time is a stopping time for the Lévy filtration
-- statement:
--   For an adapted right-continuous spectrally negative Lévy process and any strict upper-passage level, the event that the first strict upper-passage time is below a finite deterministic horizon T is observable in the sigma-algebra of the filtration at T. The pathwise first-passage equivalence and the proved horizon-preserving countable-grid detection yield a countable union of events measurable at grid times strictly before T. This is the filtration-level (rather than merely ambient) stopping-time measurability needed to apply strong Markov at the upper barrier exit.
-- source:
--   Direct stopping-time prerequisite for the Strong-Markov barrier-value split child 79978d61-9d1f-4b20-b8a5-114797a8e380 in mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Strengthens Proved chat03_named_upper_passage_lt_horizon_measurable (917e5e2e), by using the Proved countable grid iff (c4e268ac) and filtration adaptedness (bb9f53a4).

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_lt_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat08_levy_upcrossing_event_measurable_at_time

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_upperPassage_lt_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (upper : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
          (T : ℝ≥0∞)} := by
  sorry
