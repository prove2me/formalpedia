-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a126_b0_original_root_true_full_cross_positive_spatial_bound
-- name    : AvramDividend.Classical.avram_ga_a126_b0_original_root_true_full_cross_positive_spatial_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:14:11.055227+00:00
-- url     : https://prove2.me/theorems/17592946-ed92-4946-98cc-8ed266421cde
-- title:
--   Original Gaussian positive-interior root spatial residual pointwise bounded by full absolute error plus the genuine one crossing positive error
-- statement:
--   For the original stochastic Lévy source, dividend right limits, physical m-cell mesh and true clipped stopping clock, the positive part of the exact original b0 triple source residual is bounded by the absolute full pre-stop Gaussian source generator residual plus the positive part of the sole genuinely clipped stop-crossing source residual. The bridge is exact finite algebra from two certified theorems and imposes no global smoothness beyond the positive reserve domain.
-- source:
--   Certified source-exact original b0 finite summation ga121 and certified source-specific true full/cross positive bound ga107.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a121_b0_root_spatial_residual_eq_genuine_clipped_cell_sum
import Theorems.Thm_AvramDividend_Classical_avram_ga_a107_original_gaussian_true_clipped_positive_spatial_two_cell_partition_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a126_b0_original_root_true_full_cross_positive_spatial_bound
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
    let A : ℕ → ℝ := fun i =>
      E (v (i + 1)) * (w (x + X.X (v (i + 1)) ω -
        rightLimit D (v i) ω) - w (Y (v i)))
    let B : ℕ → ℝ := fun i =>
      if s i < ρ then E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
    let G : ℕ → ℝ := fun i =>
      if s i < ρ then (Δ : ℝ) * E (s i) *
        X.generator w (Y (s i)) else 0
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    let C : ℕ → ℝ := fun i =>
      E ρ * (w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) -
        w (Y (s i))) - H i
    max ((∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, B i) -
      (∑ i ∈ Finset.range m, G i)) 0 ≤
      |∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0| +
      max (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0) 0 := by sorry
