-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_positive_near_zero_germ_measurable
-- name    : AvramDividend.Classical.avram_p4_f12_original_positive_near_zero_germ_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:14:13.865922+00:00
-- url     : https://prove2.me/theorems/f1e93061-4a7a-487a-97db-a8d1b2aa6b41
-- title:
--   Germ measurability of original Lévy arbitrarily early positive excursions
-- statement:
--   The actual right-continuous Lévy path event of reaching strictly positive observations arbitrarily close to time zero is measurable in the germ sigma algebra; formalization may use right continuity and countable rational time witnesses. This is an independent filtration-measurability obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory Set AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f12_original_positive_near_zero_germ_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    MeasurableSet[germSigma X.X] {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by sorry
