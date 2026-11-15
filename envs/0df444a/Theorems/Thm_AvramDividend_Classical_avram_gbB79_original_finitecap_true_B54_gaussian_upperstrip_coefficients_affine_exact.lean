-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB79_original_finitecap_true_B54_gaussian_upperstrip_coefficients_affine_exact
-- name    : AvramDividend.Classical.avram_gbB79_original_finitecap_true_B54_gaussian_upperstrip_coefficients_affine_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:39:21.344201+00:00
-- url     : https://prove2.me/theorems/78c24939-51ac-4f6c-a636-5f181ad4edff
-- title:
--   Original finite-cap B54 physical Gaussian first and second Hermite coefficients exactly specialise to affine upper strip
-- statement:
--   For the original B54 physical mesh and exact candidate G and H coefficients including true stopping mask s_i<rho, lower compact cutoff δ/2 and upper finitecap rational clipping level b_j, whenever the actual postpayment Y_i=x+X(s_i)-rightLimit D(s_i) exceeds b_j, the first Hermite coefficient is precisely exp(-q s_i), and the second is exactly zero. This is the source-faithful identification needed to combine B68 exact positive drift bound with B54 actual finite Gaussian centred grid, without an artificial global C2 assumption or a different controlled reserve.
-- source:
--   On true stopped physical upper-strip cells s_i<rho and Y_i>b_j, Y_i cannot belong to closed Icc(δ/2,b_j). Thus the exact original clipped G_i selects unit slope and H_i selects zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB79_original_finitecap_true_B54_gaussian_upperstrip_coefficients_affine_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q δ : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0)
    (n m j i : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let G : ℝ :=
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0
    let H : ℝ :=
      if s < ρ ω then (1 / 2 : ℝ) *
        Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then iteratedDeriv 2 w Y else 0)
      else 0
    s < ρ ω → b < Y →
      G = Real.exp (-(q * (s : ℝ))) ∧ H = 0 := by sorry
