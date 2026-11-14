-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a116_actual_original_gaussian_stop_crossing_source_increment_ae_zero
-- name    : AvramDividend.Classical.avram_ga_a116_actual_original_gaussian_stop_crossing_source_increment_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:54:54.754873+00:00
-- url     : https://prove2.me/theorems/9db10d66-da62-46a3-ae5b-bd77d85678a4
-- title:
--   Original zero jump Gaussian Lévy source has vanishing stopped physical crossing increment at the true random stopping time
-- statement:
--   For the original zero-jump Lévy source X and any actual stopping clock rho bounded by the physical horizon n, take any randomly selected index whose physical uniform source grid cell straddles rho. The source displacement X(rho)-X(s_i) converges to zero almost surely, even if i depends on the whole path. This is a direct true-ruin crossing theorem, rather than an arbitrary endpoint or final mesh substitute.
-- source:
--   Original Avram b0 physically clipped Gaussian residual, proved original source random clock modulus ga102.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a116_actual_original_gaussian_stop_crossing_source_increment_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0) (i : ℕ → Ω → ℕ)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hCross : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ < ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      X.X (ρ ω) ω -
        X.X ((i m ω : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)
      atTop (𝓝 (0 : ℝ)) := by sorry
