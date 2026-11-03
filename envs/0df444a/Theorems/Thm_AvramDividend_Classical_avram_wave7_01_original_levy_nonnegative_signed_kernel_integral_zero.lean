-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_nonnegative_signed_kernel_integral_zero
-- name    : AvramDividend.Classical.avram_wave7_01_original_levy_nonnegative_signed_kernel_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:05:45.930679+00:00
-- url     : https://prove2.me/theorems/e61acdd7-6a75-4e4a-b74d-42a893bd5209
-- title:
--   Signed original Lévy generator kernels contribute zero over nonnegative marks
-- statement:
--   For the exact original X.ν, every real-valued signed mark kernel integrates to zero over nonnegative jump sizes. No L¹ assumption is needed on this null region, and no finite-activity/BV premise is involved. The theorem allows W7-02/W7-04 to eliminate the positive-mark part of signed predictable Lévy generator kernels on the original source.
-- source:
--   Source axiom X.ν_Ici=0, Mathlib Measure.restrict_eq_zero and integral_zero_measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_levy_nonnegative_signed_kernel_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (K : ℝ → ℝ) :
    (∫ y in Ici (0 : ℝ), K y ∂X.ν) = 0 := by sorry
