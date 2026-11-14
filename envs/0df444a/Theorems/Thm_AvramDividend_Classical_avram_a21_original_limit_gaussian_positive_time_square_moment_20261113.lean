-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
-- name    : AvramDividend.Classical.avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T09:18:49.077288+00:00
-- url     : https://prove2.me/theorems/205869d5-5dfc-4e91-8175-c18b04a98892
-- title:
--   Original intrinsic Gaussian limit exact sigma-squared moment at strictly positive horizons
-- statement:
--   At a strictly positive source horizon, the almost-sure limit of the physical intrinsic Gaussian residual has integrable square and exact variance t times the Gaussian coefficient squared. It is the genuine stochastic positive-horizon core of theorem 2c95ecd3 and requires an original-source Gaussian/Levy-Itô moment proof.
-- source:
--   Original Levy-Ito small-jump L2 limit and Brownian Gaussian second moment on the original probability space; positive-horizon parent split.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0, 0 < t →
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by sorry
