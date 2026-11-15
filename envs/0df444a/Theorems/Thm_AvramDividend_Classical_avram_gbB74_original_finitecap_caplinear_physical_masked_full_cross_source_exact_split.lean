-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB74_original_finitecap_caplinear_physical_masked_full_cross_source_exact_split
-- name    : AvramDividend.Classical.avram_gbB74_original_finitecap_caplinear_physical_masked_full_cross_source_exact_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:25:56.563213+00:00
-- url     : https://prove2.me/theorems/f8e848aa-ef82-4ba8-9481-174cb6470b2c
-- title:
--   Original finite-cap interior caplinear Gaussian physical-grid spatial source residual splits exactly into full and stop-crossing cells
-- statement:
--   The genuine original physical stopped Gaussian source residual for the interior clipped caplinear continuation V_b of w, using original X, D, original rightLimit D and physical stopped mesh v_i=min(s_i,rho), splits exactly into the sum of full stopped cells with s_i+Δ≤rho and the single true stop-straddling crossing-cell residual. The left side contains the actual discounted prepayment spatial source, true centred Gaussian Hermite first/second coefficients and source generator on the physical left grid. This is the exact original source bridge between B73 cash ledger, B71 full-cell positive error, B59 crossing error, and B54 L1 cash witness.
-- source:
--   Instantiate Proved A123 original physical stopped spatial residual full-versus-crossing exact identity at the true interior caplinear V_b. The theorem is independent of smoothness and requires no artificial smaller admissibility cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a123_b0_original_root_exact_genuine_full_cross_residual_identity
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB74_original_finitecap_caplinear_physical_masked_full_cross_source_exact_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (b q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Vb : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun i => min (s i) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv Vb (Y (s i)) * Z i +
        (iteratedDeriv 2 Vb (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator Vb (Y (s i))
    let U : ℕ → ℝ := fun i =>
      E (v (i + 1)) *
        (Vb (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          Vb (Y (v i))) -
      (if s i < ρ then H i else 0)
    let A : ℕ → ℝ := fun i =>
      E (v (i + 1)) * (Vb (x + X.X (v (i + 1)) ω -
        rightLimit D (v i) ω) - Vb (Y (v i)))
    let B : ℕ → ℝ := fun i =>
      if s i < ρ then E (s i) * (deriv Vb (Y (s i)) * Z i +
        (iteratedDeriv 2 Vb (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
    let G : ℕ → ℝ := fun i =>
      if s i < ρ then (Δ : ℝ) * E (s i) *
        X.generator Vb (Y (s i)) else 0
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (Vb (Y (s i) + R i) - Vb (Y (s i))) - H i
    let C : ℕ → ℝ := fun i =>
      E ρ * (Vb (Y (s i) + (X.X ρ ω - X.X (s i) ω)) -
        Vb (Y (s i))) - H i
    (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, B i) -
      (∑ i ∈ Finset.range m, G i) =
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by sorry
