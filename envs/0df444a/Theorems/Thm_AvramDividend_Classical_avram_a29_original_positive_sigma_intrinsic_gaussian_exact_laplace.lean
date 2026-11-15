-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_intrinsic_gaussian_exact_laplace
-- name    : AvramDividend.Classical.avram_a29_original_positive_sigma_intrinsic_gaussian_exact_laplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:03:05.506232+00:00
-- url     : https://prove2.me/theorems/7b0929c3-0cc4-43b9-a648-a6434c568c5d
-- title:
--   Exact original-space positive-volatility intrinsic Gaussian Laplace exponent from physical finite-activity Lévy source
-- statement:
--   For a finite-activity spectrally negative original Lévy source with strictly positive sigma, prove the exact Gaussian exponential moment and Laplace exponent of the original intrinsic Gaussian cutoff limit, on exactly its original probability measure, independently of any zero-nu companion process.
-- source:
--   Source-faithful Lévy–Khintchine / Poisson-mark cancellation and original Gaussian cutoff L1 limits; this is the remaining nontrivial positive-sigma analytic problem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a29_original_positive_sigma_intrinsic_gaussian_exact_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ) := by sorry
