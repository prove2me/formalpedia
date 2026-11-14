-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_cutoff_gaussian_plus_all_smallmarks_second_moment_20261113_v2
-- name    : AvramDividend.Classical.avram_a21_original_zero_cutoff_gaussian_plus_all_smallmarks_second_moment_20261113_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T07:59:03.048685+00:00
-- url     : https://prove2.me/theorems/4cd3877e-2d14-498f-89eb-883535cad919
-- title:
--   Original zero cutoff residual exact variance includes Gaussian and every compensated negative small jump
-- statement:
--   On the actual original Lévy process probability space, the cutoff-zero intrinsic residual has an integrable square and exact second moment time times Gaussian coefficient squared plus the entire (-1,0) squared Levy jump intensity.
-- source:
--   Correct Lévy–Itô decomposition. This is an outstanding original-space source identity required by original Gaussian cutoff variance 74450e6a; it requires original joint law/covariance verification and does not follow from Jsmall0=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_zero_cutoff_gaussian_plus_all_smallmarks_second_moment_20261113_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      let R0 : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
      Integrable (fun ω => (R0 ω)^2) P ∧
        (∫ ω, (R0 ω)^2 ∂P) =
          (t : ℝ) * X.σ ^ 2 +
            (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) := by sorry
