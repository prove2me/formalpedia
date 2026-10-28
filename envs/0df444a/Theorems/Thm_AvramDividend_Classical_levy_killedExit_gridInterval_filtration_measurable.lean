-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_killedExit_gridInterval_filtration_measurable
-- name    : AvramDividend.Classical.levy_killedExit_gridInterval_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:03:37.021804+00:00
-- url     : https://prove2.me/theorems/4463b759-7990-43c1-b589-c9d2e709eaed
-- title:
--   Killed upper-exit first-arrival grid interval is measurable by the later grid time
-- statement:
--   If S≤T, the event that first upper passage occurs before T but not before S, while the Lévy path has made no lower threshold crossing before T, belongs to the filtration at T. The event is a measurable finite-grid fibre for approximating the upper exit before ruin.
-- source:
--   Directly applies both Proved up-passage and lower-crossing filtration measurability theorems, with filtration monotonicity for the earlier grid time. Root-connected path to strong-Markov barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_killedExit_gridInterval_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper lower : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (T : ℝ≥0∞) ∧
        ¬ (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (S : ℝ≥0∞) ∧
        ¬ ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} := by
  sorry
