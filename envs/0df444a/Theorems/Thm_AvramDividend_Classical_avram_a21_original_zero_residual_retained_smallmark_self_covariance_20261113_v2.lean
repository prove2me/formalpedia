-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_residual_retained_smallmark_self_covariance_20261113_v2
-- name    : AvramDividend.Classical.avram_a21_original_zero_residual_retained_smallmark_self_covariance_20261113_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T07:59:13.54596+00:00
-- url     : https://prove2.me/theorems/d376c1db-cb38-48d5-9f0e-4845527d4d92
-- title:
--   Original zero cutoff residual has true retained physical smallmark self covariance
-- statement:
--   The actual original-space zero-cutoff residual and physically retained compensated strip martingale have integrable squares and cross product, and their cross expectation equals the retained strip second moment, as follows from Gaussian and compensated Poisson orthogonality in the original Lévy–Itô decomposition.
-- source:
--   Original Lévy–Itô joint law or martingale quadratic covariation. Distinguishes the true cross term from a mathematically false independence assumption; required by original cutoff Gaussian variance 74450e6a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_zero_residual_retained_smallmark_self_covariance_20261113_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let R0 : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
      Integrable (fun ω => (J ω)^2) P ∧
      Integrable (fun ω => R0 ω * J ω) P ∧
        (∫ ω, R0 ω * J ω ∂P) =
          (∫ ω, (J ω)^2 ∂P) := by sorry
