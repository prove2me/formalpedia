-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_positive_gaussian_limit_square_moment_20261113
-- name    : AvramDividend.Classical.avram_a21_original_sigma_positive_gaussian_limit_square_moment_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T10:36:56.619558+00:00
-- url     : https://prove2.me/theorems/8caf9ed8-349e-41d8-ad48-fb9a7f9918ea
-- title:
--   Strictly positive sigma: exact original physical intrinsic Gaussian limit second moment
-- statement:
--   The positive Gaussian coefficient branch of the original physical Gaussian residual limit has exact quadratic moment time multiplied by sigma squared on the original probability space. This is the hard original Lévy-Itô characteristic-function / continuous martingale quadratic bracket calculation. The sigma=0 branch is separately source-BV to avoid falsely assuming a Brownian process on another probability space.
-- source:
--   Original Lévy exponent Gaussian coefficient, Lévy-Itô source residual and physical stopped martingale quadratic bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_sigma_positive_gaussian_limit_square_moment_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    0 < X.σ →
      ∀ (t : ℝ≥0), 0 < t →
        Integrable (fun ω => (R t ω)^2) P ∧
        (∫ ω, (R t ω)^2 ∂P) = (t : ℝ) * X.σ^2 := by sorry
