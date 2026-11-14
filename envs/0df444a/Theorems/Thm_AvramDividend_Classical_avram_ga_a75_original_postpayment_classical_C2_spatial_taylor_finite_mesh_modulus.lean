-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a75_original_postpayment_classical_C2_spatial_taylor_finite_mesh_modulus
-- name    : AvramDividend.Classical.avram_ga_a75_original_postpayment_classical_C2_spatial_taylor_finite_mesh_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:40:32.906218+00:00
-- url     : https://prove2.me/theorems/07672132-f239-493f-98d0-35c03949855b
-- title:
--   Original postpayment positive compact Gaussian spatial Taylor quadratic modulus holds for the actual classical generator gradient
-- statement:
--   For the original dividend-controlled source X,D and a positive compact C2 spatial reserve band, the finite physical Gaussian spatial Taylor remainder using ordinary value derivatives at the original source start is bounded by an arbitrarily small coefficient times the original raw squared spatial displacement energy.
-- source:
--   Direct positive-only original b0d9951c Gaussian C2 Taylor error bridge from ga_a58 within Taylor to classical generator via ga_a74.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a75_original_postpayment_classical_C2_spatial_taylor_finite_mesh_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (hDiff : ∀ z ∈ Icc a b, DifferentiableAt ℝ w z) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (S : Finset ℕ) (s : ℕ → ℝ≥0) (y : ℕ → ℝ),
        let z : ℕ → ℝ := fun i =>
          x + X.X (s i) ω - rightLimit D (s i) ω
        (∀ i ∈ S, z i ∈ Icc a b ∧ y i ∈ Icc a b ∧
          z i ≠ y i ∧ dist (y i) (z i) < δ) →
        |∑ i ∈ S, (w (y i) - w (z i) -
          deriv w (z i) * (y i - z i) -
          (iteratedDeriv 2 w (z i) * (y i - z i)^2) / 2)| ≤
          ε * ∑ i ∈ S, (y i - z i)^2 := by sorry
