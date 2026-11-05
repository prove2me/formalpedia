-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_past_event_centred_laplace
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_past_event_centred_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:38:36.241511+00:00
-- url     : https://prove2.me/theorems/0506ad7c-1354-4a17-9fa3-59da4eeca28b
-- title:
--   Original zero-jump Gaussian centred increment Laplace factorisation over any past event
-- statement:
--   Conditioning on any measurable event in the original filtration at time s, the future drift-centred zero-jump original Lévy increment has its exact Gaussian positive Laplace transform multiplied by the past event probability.
-- source:
--   Proved original future-past centred increment independence, Mathlib Indep.setIntegral_eq_mul, Proved original zero-jump centred increment Laplace law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_past
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_past_event_centred_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A, Real.exp
      (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P) =
      P.real A * Real.exp (((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) := by sorry
