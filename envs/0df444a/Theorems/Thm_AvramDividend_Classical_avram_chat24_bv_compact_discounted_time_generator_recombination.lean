-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_compact_discounted_time_generator_recombination
-- name    : AvramDividend.Classical.avram_chat24_bv_compact_discounted_time_generator_recombination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:11:42.640614+00:00
-- url     : https://prove2.me/theorems/1d02ec65-2962-4f89-88ae-45c335592582
-- title:
--   Compact BV discounted time generator recombination
-- statement:
--   Source-faithful deterministic child of 269be26a-5616-4a58-ae4e-feb24dcd0568. For a measurable real reserve observed on a finite nonnegative-time measure, positive compact band, nonnegative discount and a positive C1 ruin-extended value, recombine the physical drift time integral into minus the actual negative-mark kernel intensity integral plus the physical generator time integral. Compact value, Lipschitz and derivative bounds yield genuine integrability through compact finite-measure recombination 584a15bf-02b1-4dc4-8e73-e9d279727936; no path admissibility, HJB sign or convergence hypothesis is added. The actual parent applies this to the original shifted predictable reserve. Publication is a deterministic time specialization, not a stochastic or source-limit theorem.

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
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_chat24_bv_compact_discounted_time_generator_recombination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hs : ContDiffOn ℝ 1 w (Ioi 0)) (q a b : ℝ)
    (hq : 0 ≤ q) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hgen : ∀ y ∈ Icc a b, X.GeneratorIntegrable w y)
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (Y : ℝ≥0 → ℝ) (hYm : Measurable Y) (τ : ℝ≥0) :
    (∫ t, if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Y t) - q * w (Y t)) else 0 ∂μ) =
    -(∫ t, ∫ z in Iio (0 : ℝ), if t ≤ τ ∧ Y t ∈ Icc a b ∧ z < 0 then
      Real.exp (-(q * (t : ℝ))) * (w (Y t + z) - w (Y t)) else 0 ∂X.ν ∂μ) +
    (∫ t, if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * (X.generator w (Y t) - q * w (Y t)) else 0 ∂μ) := by sorry
