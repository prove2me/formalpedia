-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_physical_clock_mass_finite
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_physical_clock_mass_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:14:03.433226+00:00
-- url     : https://prove2.me/theorems/2d492b9b-8f96-413a-a129-654cdbb01153
-- title:
--   Finite mass of the actual original predictable physical clock
-- statement:
--   For the exact original right-continuous predictable clock μ, assume only its physical product-clock equality on predictable sets and the original probability law P. Prove finite total μ mass from the finite real-Lebesgue physical horizon, discharging the source signed nonlinear expectation theorem's hμfinite without an independent Lévy jump or compensator premise.
-- source:
--   Original source predictable clock μ and its exact physical product-clock equality in accepted 4846bbef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_physical_clock_total_mass_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_physical_clock_mass_finite {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} (T : ℝ≥0) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) (hμclock : ∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A → μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) : μ Set.univ < ∞ := by sorry
