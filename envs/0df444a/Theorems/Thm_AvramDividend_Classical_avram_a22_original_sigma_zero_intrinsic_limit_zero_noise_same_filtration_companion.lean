-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
-- name    : AvramDividend.Classical.avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:04:48.350238+00:00
-- url     : https://prove2.me/theorems/36dea78b-c796-4d22-9cb0-9db5391df461
-- title:
--   Original finite-activity σ=0 Gaussian-source companion from genuine zero residual and deterministic same-filtration Lévy witness
-- statement:
--   The original finite-activity zero-Gaussian case of c5c7: if X.σ=0, the genuine physical cutoff residual R vanishes almost surely at every time, so the on-the-original-space zero-path zero-triplet Lévy process Y realises R=Y.X-t Y.c, simultaneously for all times on the same Ω,P,filtration. Requires the true original BV source zero-residual lemma, the now-Proved same-space zero-noise Lévy witness and the exact zero-drift consequence of its own Laplace law. This is a genuine reduction of c5c7 with no artificial independent noise.
-- source:
--   Proved 594b2140 original-space deterministic zero-noise witness, Open 77f47f2e original σ=0 physical residual vanishes, new original zero-path zero triplet drift lemma; existing c5c7 parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hSigma : X.σ = 0) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by sorry
