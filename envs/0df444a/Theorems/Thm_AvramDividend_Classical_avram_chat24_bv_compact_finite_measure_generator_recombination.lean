-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_compact_finite_measure_generator_recombination
-- name    : AvramDividend.Classical.avram_chat24_bv_compact_finite_measure_generator_recombination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:35:49.46019+00:00
-- url     : https://prove2.me/theorems/584a15bf-02b1-4dc4-8e73-e9d279727936
-- title:
--   AvramDividend.Classical.avram_chat24_bv_compact_finite_measure_generator_recombination
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_bv_compact_finite_measure_generator_recombination from oversized parent candidate cc40c24032fbb96f501748668f544ad388ec4748950a70d1b6e1d081b20d1a32.
-- source:
--   candidate-decomposition:269be26a-5616-4a58-ae4e-feb24dcd0568:cc40c24032fbb96f501748668f544ad388ec4748950a70d1b6e1d081b20d1a32

import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_compact_kernel_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical

noncomputable section
theorem AvramDividend.Classical.avram_chat24_bv_compact_finite_measure_generator_recombination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (w : ℝ → ℝ) (hwm : Measurable w)
    (q a b L R A : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hW : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hDeriv : ∀ y ∈ Icc a b, |deriv w y| ≤ A)
    (hGen : ∀ y ∈ Icc a b, X.GeneratorIntegrable w y)
    {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [IsFiniteMeasure μ]
    (Y e : ι → ℝ) (hYm : Measurable Y) (hem : Measurable e)
    (he : ∀ t, |e t| ≤ 1) (E : Set ι) (hEm : MeasurableSet E)
    (hE : ∀ t ∈ E, Y t ∈ Icc a b) :
    (∫ t, if t ∈ E then e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0 ∂μ) =
      -(∫ t, if t ∈ E then e t * (∫ z in Iio (0 : ℝ),
        w (Y t + z) - w (Y t) ∂X.ν) else 0 ∂μ) +
      (∫ t, if t ∈ E then e t * (X.generator w (Y t) - q * w (Y t)) else 0 ∂μ) := by sorry
end
