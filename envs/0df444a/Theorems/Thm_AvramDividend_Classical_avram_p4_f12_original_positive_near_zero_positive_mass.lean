-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_positive_near_zero_positive_mass
-- name    : AvramDividend.Classical.avram_p4_f12_original_positive_near_zero_positive_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T19:03:50.611331+00:00
-- url     : https://prove2.me/theorems/e07bb5e6-dc38-49f8-b63a-254bb51f221d
-- title:
--   Strictly positive mass of near-zero upward Lévy excursions under unbounded variation
-- statement:
--   Under unbounded variation, the original spectrally negative Lévy process has strictly positive probability of arbitrarily early positive observations. This source probability obligation is separate from germ measurability and the completed zero-one transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f12_original_positive_near_zero_positive_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation) :
    0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by sorry
