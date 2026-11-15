-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_intrinsic_gaussian_exact_zero_nu_laplace_exponent
-- name    : AvramDividend.Classical.avram_a28_original_intrinsic_gaussian_exact_zero_nu_laplace_exponent
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T07:54:24.582964+00:00
-- url     : https://prove2.me/theorems/d83430ac-a3d9-4599-ba29-e1e2529cd951
-- title:
--   Original Gaussian intrinsic residual has exact centred zero-nu Lévy Laplace exponent
-- statement:
--   Identify the exact original-probability exponential moment and Laplace exponent of the intrinsic Gaussian residual limit at all deterministic times for every nonnegative tilt, invariant under all-time almost-sure equivalent representatives.
-- source:
--   Original A24/A27 source constructions; remaining genuine finite-activity path or Lévy-Khintchine analytic proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_original_intrinsic_gaussian_exact_zero_nu_laplace_exponent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
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
