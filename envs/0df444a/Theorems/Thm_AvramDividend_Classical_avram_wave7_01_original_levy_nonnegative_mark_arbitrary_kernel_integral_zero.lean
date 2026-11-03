-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_nonnegative_mark_arbitrary_kernel_integral_zero
-- name    : AvramDividend.Classical.avram_wave7_01_original_levy_nonnegative_mark_arbitrary_kernel_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:54:39.25995+00:00
-- url     : https://prove2.me/theorems/e754f267-6be8-4715-90ad-f7fa3fbdc26b
-- title:
--   Every nonnegative-mark Lévy generator kernel integral vanishes for the exact source ν
-- statement:
--   For the original SpectrallyNegativeLevy X and its exact Lévy measure X.ν, the ENNReal integral of any nonnegative possibly unbounded mark kernel over [0,∞) vanishes. This holds for arbitrary predictable sample/time parameterized kernels by specializing K and pairs with the exact source pathwise marked jump-reward support; no BV, finite activity, or ν-rate identification is assumed.
-- source:
--   Structural original-source axiom X.ν_Ici=0; Mathlib Measure.restrict_eq_zero and lintegral_zero_measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_levy_nonnegative_mark_arbitrary_kernel_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (K : ℝ → ℝ≥0∞) :
    (∫⁻ y in Ici (0 : ℝ), K y ∂X.ν) = 0 := by sorry
