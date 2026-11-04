-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_trimmed_physical_clock_exists
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_trimmed_physical_clock_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:09:18.123191+00:00
-- url     : https://prove2.me/theorems/e73b5fba-e16e-4830-94e5-26641f9d8a65
-- title:
--   Construct original finite predictable physical clock by trimming the time-path product measure
-- statement:
--   Construct a finite predictable measure on the same original time-path space and right-continuous filtration as the controlled spectrally negative Lévy source, exactly equal on all original predictable sets to the mapped real-Lebesgue finite physical clock times the original path probability law. The construction uses Mathlib Measure.trim on the inclusion of predictable into ordinary product measurable space. It introduces no new compensator axiom and no independent marked Poisson process; it supplies both hμfinite and hμclock for the original stopped BV jump-compensation identity.
-- source:
--   Mathlib Measure.trim/trim_measurableSet_eq plus accepted P3-B predictable_le_product and predictable_physical_clock_mass_finite

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_le_product_space
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_physical_clock_mass_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_trimmed_physical_clock_exists {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) : ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable), μ Set.univ < ∞ ∧ ∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A → μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A := by sorry
