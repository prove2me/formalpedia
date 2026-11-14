-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a94_original_gaussian_clipped_spatial_residual_true_full_cross_partition
-- name    : AvramDividend.Classical.avram_ga_a94_original_gaussian_clipped_spatial_residual_true_full_cross_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:18:54.884531+00:00
-- url     : https://prove2.me/theorems/d7ead43e-b5c6-4d28-aed7-f7afc9ad8b6d
-- title:
--   Original positive Gaussian source spatial HJB residual equals exact physically full pre-stop and true clipped crossing cell sums
-- statement:
--   For the original Gaussian Levy driver and dividend strategy on the exact stopped physical mesh, the source-specific compensated spatial HJB residual splits pathwise into full pre-stop cell terms with original physical source endpoints plus true stopped crossing cell terms with actual clipped source endpoints, with post-stop cells vanishing.
-- source:
--   Direct b0d9951c source-exact parent-level full versus unique stopped crossing decomposition, using ga_a71, ga_a89, ga_a90, ga_a93.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a94_original_gaussian_clipped_spatial_residual_true_full_cross_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun i => min (s i) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let U : ℕ → ℝ := fun i =>
      E (v (i + 1)) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          w (Y (v i))) -
      (if s i < ρ then H i else 0)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    let C : ℕ → ℝ := fun i =>
      E ρ * (w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) -
        w (Y (s i))) - H i
    (∑ i ∈ Finset.range m, U i) =
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by sorry
