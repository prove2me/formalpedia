-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_near_zero_rational_path_equiv
-- name    : AvramDividend.Classical.avram_p4_f14_original_near_zero_rational_path_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:34:54.833037+00:00
-- url     : https://prove2.me/theorems/516bf573-0839-424e-ba30-fd61ed132bb8
-- title:
--   Right-continuous original Lévy positive excursions have rational time witnesses
-- statement:
--   By pathwise right continuity, any strictly positive value observed at a time before a positive horizon remains positive for a short later interval, which contains a nonnegative rational time. Thus arbitrarily early positive excursions are equivalent pointwise to the corresponding countable rational-time event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory Set AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f14_original_near_zero_rational_path_equiv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} = {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω} := by sorry
