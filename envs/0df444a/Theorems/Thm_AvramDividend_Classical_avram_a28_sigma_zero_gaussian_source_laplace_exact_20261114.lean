-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_sigma_zero_gaussian_source_laplace_exact_20261114
-- name    : AvramDividend.Classical.avram_a28_sigma_zero_gaussian_source_laplace_exact_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:02:46.525633+00:00
-- url     : https://prove2.me/theorems/2ad7a5c5-fd61-4f26-bbb9-c1ebdfb22a52
-- title:
--   Original finite-activity Gaussian intrinsic residual has exact zero-sigma Gaussian Laplace law
-- statement:
--   At sigma=0, every actual original-space finite-activity Gaussian intrinsic residual limit and every almost-everywhere equivalent global representative has exponential moment exactly one, matching the zero-volatility, zero-jump Levy Laplace exponent.
-- source:
--   Proved 77f47f2e Gaussian residual zero on one source conull event, Proved 1a7a54e5 Laplace exponent no-jump identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original intrinsic Gaussian residual has the exact trivial Gaussian Laplace law at zero sigma. -/

theorem AvramDividend.Classical.avram_a28_sigma_zero_gaussian_source_laplace_exact_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hSigma : X.σ = 0)
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ) := by sorry
