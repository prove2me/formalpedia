-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a107_original_gaussian_true_clipped_positive_spatial_two_cell_partition_bound
-- name    : AvramDividend.Classical.avram_ga_a107_original_gaussian_true_clipped_positive_spatial_two_cell_partition_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:33:35.348947+00:00
-- url     : https://prove2.me/theorems/6f7d9364-b34b-4758-a332-dadea13e8972
-- title:
--   Actual Gaussian clipped positive spatial residual bounded by full-cell absolute source error plus one crossing-cell positive remainder
-- statement:
--   The exact original clipped Gaussian finite-mesh positive residual from the b0 parent is bounded pathwise by the absolute sum of physically full pre-stop source-generator residuals plus the positive part of the genuinely clipped single crossing-cell source-generator residual. All poststop cells vanish. This is a one-sided reduction with no false C2 Taylor on the crossing cell.
-- source:
--   Proved exact physical full/cross/post partition ga_a94 and scalar max-subadd bound, for the original b0d9951c positive L1 proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a94_original_gaussian_clipped_spatial_residual_true_full_cross_partition
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a107_original_gaussian_true_clipped_positive_spatial_two_cell_partition_bound
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
    max (∑ i ∈ Finset.range m, U i) 0 ≤
      |∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0| +
      max (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0) 0 := by sorry
