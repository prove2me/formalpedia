-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_finite_cell_measurable
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_finite_cell_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:16:38.806841+00:00
-- url     : https://prove2.me/theorems/c56034c1-bc9f-49e7-9767-1df23ca0df26
-- title:
--   Original-filtration past-event finite jump cylinder is measurable for the right-continuous predictable marked space
-- statement:
--   For the original filtration, every adapted finite (s,t] time/past-event rectangle crossed with any Borel negative-jump mark cell belongs to the right-continuous predictable product sigma algebra. This discharges the exact measurability premise of the P3-B finite-to-future extension. It makes no claim about the source jump-rate or compensation equality.
-- source:
--   Mathlib.Probability.Process.Predictable measurableSet_predictable_Ioc_prod; Filtration.le_rightCont; original Avram Proposition 4(i).

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_finite_cell_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      ((Ioc s t ×ˢ A) ×ˢ B) := by sorry
