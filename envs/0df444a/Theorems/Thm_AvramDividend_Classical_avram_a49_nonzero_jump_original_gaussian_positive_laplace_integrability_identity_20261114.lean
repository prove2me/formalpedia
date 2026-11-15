-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
-- name    : AvramDividend.Classical.avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T10:41:07.452137+00:00
-- url     : https://prove2.me/theorems/1ab4c700-c399-4fc7-b3d3-902dbf3975f0
-- title:
--   Original nonzero finite-jump intrinsic Gaussian residual has positive-ray Laplace integrability and exact sigma-squared Gaussian MGF
-- statement:
--   On the actual finite but nonzero jump Lévy source, prove positive exponential integrability and exact centred Gaussian positive-ray moment-generating function of its intrinsic Gaussian residual at strictly positive deterministic times. This is the remaining source Lévy–Khintchine marked-jump cancellation statement after the Gaussian-law uniqueness bridge has been proved independently.
-- source:
--   Positive-ray Lévy–Khintchine formula for spectrally negative finite-activity source and source-faithful compound Poisson mark cancellation; gaussian MGF bridge A48.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (ht : 0 < t) (θ : ℝ), 0 < θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      mgf (G t) P θ =
        mgf id (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) θ := by sorry
