-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:34:39.216797+00:00
-- url     : https://prove2.me/theorems/cd060910-1502-4991-8cbe-36eac75b529f
-- title:
--   Original right-continuous predictable localisation is product-measurable
-- statement:
--   For the original time-indexed filtration 𝓕 on the source sample space Ω, every right-continuous predictable set E of time×samples is measurable under the ambient product sigma algebra. Prove it using the actual predictable generating rectangles {0}×A and (i,∞)×A and Filtration.le, without postulating predictability or changing the process.
-- source:
--   Official Mathlib.Probability.Process.Predictable measurableSpace_le_predictable_of_measurableSet, Mathlib.Probability.Process.Filtration.le; genuine rightCont filtration.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
{Ω : Type*} [mΩ : MeasurableSpace Ω]
{𝓕 : Filtration ℝ≥0 mΩ} (E : Set (ℝ≥0 × Ω))
(hE : MeasurableSet[𝓕.rightCont.predictable] E) :
MeasurableSet E := by sorry
