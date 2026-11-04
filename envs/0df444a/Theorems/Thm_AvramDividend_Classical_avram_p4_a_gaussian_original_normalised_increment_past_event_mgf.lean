-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_past_event_mgf
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_past_event_mgf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:24:26.029257+00:00
-- url     : https://prove2.me/theorems/2066f4a2-e975-4a66-ae9d-c939da80b624
-- title:
--   Original normalised Gaussian increment MGF factors on genuine past events
-- statement:
--   The Gaussian MGF of the original same-volatility zero-jump Levy source's normalised increment factors on every event of the actual past filtration, with unrestricted factor equal to the Gaussian real MGF for the interval length.
-- source:
--   Proved P4-A original centred increment independence and normalised increment MGF; Mathlib Indep.setIntegral_eq_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_past_event_mgf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A, Real.exp
      (θ * (((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ)) ∂P) =
      P.real A * ProbabilityTheory.mgf id
        (ProbabilityTheory.gaussianReal 0 (t - s)) θ := by sorry
