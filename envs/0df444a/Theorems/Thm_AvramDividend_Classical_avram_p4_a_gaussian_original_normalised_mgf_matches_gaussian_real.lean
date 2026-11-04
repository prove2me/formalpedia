-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:56:42.418353+00:00
-- url     : https://prove2.me/theorems/5b4b88ef-571b-4f95-942b-b5b231fabd25
-- title:
--   Original zero-jump same-volatility Gaussian positive MGF agrees with Mathlib GaussianReal
-- statement:
--   At each fixed time, the MGF of the actual zero-jump Levy source component, centred and scaled using the original sigma, agrees on all nonnegative arguments with the MGF of the Mathlib Gaussian distribution of mean zero and variance t. This moves from an explicit exponential integral to the existing probability-law API; law uniqueness remains a separate step.
-- source:
--   Original SpectrallyNegativeLevy triplet and the Proved normalised Laplace identity, and Mathlib Probability.Moments.Basic and Gaussian.Real.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_laplace_identity
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ProbabilityTheory.mgf
      (fun ω => (Y.X t ω - (t : ℝ) * Y.c) / X.σ) P θ =
        ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 t) θ := by sorry
