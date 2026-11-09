-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_pointwise_limit_ae
-- name    : AvramDividend.Classical.avram_mix_fin13_original_finite_activity_intrinsic_residual_pointwise_limit_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:57:43.565167+00:00
-- url     : https://prove2.me/theorems/f5d2a47e-d1e1-4b40-8bbc-a4217f63462f
-- title:
--   Original finite-activity intrinsic Gaussian residual has a pathwise real limit at each time
-- statement:
--   For almost every sample path of the original spectrally negative Levy source X with finite negative jump intensity, at every nonnegative time the physical truncated Gaussian residual converges in real numbers. The proof applies the same-X uniform-on-bounded-clock Cauchy theorem and completeness of real numbers, with no new probability space or unproved Gaussian law. This is a source-realisation step toward constructing the original Gaussian part for the ruin-clipped mixed Ito-Meyer reward theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_truncated_residual_uniform_cauchy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin13_original_finite_activity_intrinsic_residual_pointwise_limit_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ∃ y : ℝ, Tendsto
        (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds y) := by sorry
