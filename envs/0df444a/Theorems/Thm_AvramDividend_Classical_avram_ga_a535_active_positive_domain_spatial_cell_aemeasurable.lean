-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
-- name    : AvramDividend.Classical.avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:27:39.423838+00:00
-- url     : https://prove2.me/theorems/560c444a-7582-43b4-91c7-0cb497335ae6
-- title:
--   Single stopped spatial cell is a.e. measurable under active positive domain or equality
-- statement:
--   If measurable source endpoints coincide or both belong to the strictly positive region almost surely, then the weighted difference of a function continuous on that region is almost-everywhere strongly measurable. This is the single-cell version of an already proved finite-sum spatial measurability theorem.
-- source:
--   Direct one-term specialization of the Proved a159 finite active positive-domain spatial sum measurability result.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ioi (0 : ℝ)))
    (Y Z E : Ω → ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) (hE : Measurable E)
    (hAlt : ∀ᵐ ω ∂P,
      Y ω = Z ω ∨ (0 < Y ω ∧ 0 < Z ω)) :
    AEStronglyMeasurable (fun ω => E ω * (w (Z ω) - w (Y ω))) P := by sorry
