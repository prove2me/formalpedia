-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_sigma_zero_ae_finite_variable_stops_taylor_sum_vanishes
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_ae_finite_variable_stops_taylor_sum_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:17:04.8341+00:00
-- url     : https://prove2.me/theorems/704bb708-52cb-4629-a76d-78e4990f1fd9
-- title:
--   Sigma zero original Levy Gaussian arbitrary finite stopped mesh vanishes a.e. and integrable
-- statement:
--   For original jump-bearing X with sigma zero, assuming one same-source a.s.-all-times Levy-Ito extraction, each finite collection of genuinely stopped Gaussian residual Taylor increments with arbitrary random weights vanishes a.e. even for different stopped clocks, and the total has automatic L1; no Brownian motion or global smoothness needed.
-- source:
--   Already-Proved original X sigma-zero stopped residual fc2a6faf-5987-4db6-97e3-5728e1554264; finite intersection of a.e. events; integrable_zero.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_sigma_zero_ae_original_stopped_residual_vanishes
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_ae_finite_variable_stops_taylor_sum_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : X.σ = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S,
      IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
        Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      (fun ω => ∑ i ∈ S, F i ω) =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
