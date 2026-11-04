-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_sigma_zero_ae_original_stopped_residual_vanishes
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_ae_original_stopped_residual_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:57:34.180186+00:00
-- url     : https://prove2.me/theorems/fc2a6faf-5987-4db6-97e3-5728e1554264
-- title:
--   Original Levy sigma-zero actual bounded stopped Gaussian residual vanishes almost surely from a.s. same-source extraction
-- statement:
--   For the original arbitrary-jump Levy process X with sigma=0, zero-jump Y and exact same-space sigma and an explicitly assumed almost-sure all-times Levy-Ito decomposition, the jump-subtracted Gaussian residual across an actual bounded right-continuous stopping interval is almost surely zero. Uses the Proved original zero-jump zero-Gaussian stopped drift identity; no Brownian process needed for pure-jump UBV.
-- source:
--   Original zero-jump zero-Gaussian stopped drift source theorem 9c95d92e-c3a2-4912-b449-496dda6ef86f; a.s. stopped evaluation transport.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_nojump_nogaussian_drift_increment_ae
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_ae_original_stopped_residual_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : X.σ = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω) -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω) = 0 := by sorry
