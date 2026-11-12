-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja20_original_cutoff_gaussian_uncorrelated_components
-- name    : AvramDividend.Classical.avram_ja20_original_cutoff_gaussian_uncorrelated_components
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T13:51:28.525203+00:00
-- url     : https://prove2.me/theorems/ebbab4df-51ba-4ad1-a464-ac68c0fead41
-- title:
--   Original finite-cutoff Gaussian and compensated bounded-jump source components are orthogonal with exact second moments
-- statement:
--   For the original finite-activity spectrally negative Levy process on its existing probability space and filtration, decompose each intrinsic finite-cutoff residual into the original Gaussian component and the compensated bounded negative-jump band, a.e. Prove square integrability of both, vanishing covariance, Gaussian second moment t sigma² and jump-band second moment t integral z² ν. This is the stochastic source-level core of the exact residual variance formula, explicitly separating it from the independently provable square-of-sum algebra.
-- source:
--   J-A20 direct route from cd5dbc12, using Proved original count L² and limit sources; avoid auxiliary unproved Brownian identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja20_original_cutoff_gaussian_uncorrelated_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ∃ (G J : Ω → ℝ),
        (∀ᵐ ω ∂P,
          avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω = G ω + J ω) ∧
        Integrable (fun ω => (G ω) ^ 2) P ∧
        Integrable (fun ω => (J ω) ^ 2) P ∧
        Integrable (fun ω => G ω * J ω) P ∧
        (∫ ω, G ω * J ω ∂P) = 0 ∧
        (∫ ω, (G ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 ∧
        (∫ ω, (J ω) ^ 2 ∂P) =
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by sorry
