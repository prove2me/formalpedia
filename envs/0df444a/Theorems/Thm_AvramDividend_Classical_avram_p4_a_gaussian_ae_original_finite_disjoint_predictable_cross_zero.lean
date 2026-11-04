-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_finite_disjoint_predictable_cross_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_finite_disjoint_predictable_cross_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:40:30.412437+00:00
-- url     : https://prove2.me/theorems/85f3e9f1-2ad6-4d08-8aa4-586dadeb3610
-- title:
--   Original Levy finite disjoint Gaussian residual predictable cross-covariance zero under a.s. all-times decomposition
-- statement:
--   Given actual jump-bearing original X and zero-jump Y on the same probability/filtration space with Y.sigma=X.sigma and an almost-sure all-times Levy-Ito decomposition, every distinct pair of disjoint deterministic-grid predictable weighted Gaussian residual cells is integrable and has expectation zero, under explicit L2 hypotheses. Holds also for sigma=0; no independent invented Brownian, pathwise bracket or stochastic integral asserted.
-- source:
--   Proved original zero-jump source finite pairwise theorem 93c3a7cc-3ba0-43ef-b6fc-4eedd0a8de0e; a.s. all-times transport via congr and integral_congr_ae; Avram Eq. (5.11).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_disjoint_predictable_L2_pairwise_cross_zero
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_finite_disjoint_predictable_cross_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hLp : ∀ i ∈ S, MemLp (fun ω => G i ω *
      ((X.X (t i) ω - (t i : ℝ) * X.c - Jsmall (t i) ω - Jlarge (t i) ω) -
       (X.X (s i) ω - (s i : ℝ) * X.c - Jsmall (s i) ω - Jlarge (s i) ω))) 2 P) :
    let F : ι → Ω → ℝ := fun i ω => G i ω *
      ((X.X (t i) ω - (t i : ℝ) * X.c - Jsmall (t i) ω - Jlarge (t i) ω) -
       (X.X (s i) ω - (s i : ℝ) * X.c - Jsmall (s i) ω - Jlarge (s i) ω))
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Integrable (F i * F j) P ∧ (∫ ω, F i ω * F j ω ∂P) = 0 := by sorry
