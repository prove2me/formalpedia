-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_stopped_taylor_finite_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_stopped_taylor_finite_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:07:53.378072+00:00
-- url     : https://prove2.me/theorems/6a5225ac-1b3f-48d0-93a8-e53f3bf13d53
-- title:
--   Actual Levy source finite stopped Gaussian predictable Taylor residual conditional zero with a.s. extractor
-- statement:
--   Under an a.s. all-times same-space original Levy-Ito source decomposition into zero-jump Gaussian Y, finite predictable original-X Gaussian residual Taylor cells at one genuine bounded stopping time have integrable sum and conditional stopped mean zero. Requires explicit source weighted L1, quadratic L1, and stopped-history measurability. Works with sigma zero or positive, no invented Brownian, no global C2 assumption or pathwise bracket.
-- source:
--   Proved original zero-jump stopped Gaussian finite Taylor conditional identity 01f8f1b2-f954-4558-9538-dbc7a383ba00, and a.s.-all-times source transport via integrable congruence and condExp congruence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_stopped_taylor_finite_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hH : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ ω + h i) ω - ((τ ω + h i) : ℝ) * X.c -
        Jsmall (τ ω + h i) ω - Jlarge (τ ω + h i) ω) -
       (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω))) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (((X.X (τ ω + h i) ω - ((τ ω + h i) : ℝ) * X.c -
          Jsmall (τ ω + h i) ω - Jlarge (τ ω + h i) ω) -
         (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
          Jsmall (τ ω) ω - Jlarge (τ ω) ω)) ^ 2)) P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ ω + h i) ω - ((τ ω + h i) : ℝ) * X.c -
        Jsmall (τ ω + h i) ω - Jlarge (τ ω + h i) ω) -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      P[(fun ω => ∑ i ∈ S, F i ω) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
