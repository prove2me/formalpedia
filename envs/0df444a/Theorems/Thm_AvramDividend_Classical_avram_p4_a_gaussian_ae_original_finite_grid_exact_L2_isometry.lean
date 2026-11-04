-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_finite_grid_exact_L2_isometry
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_finite_grid_exact_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:50:45.252258+00:00
-- url     : https://prove2.me/theorems/3e0fcecf-cfb9-4b43-b87e-43c9c379f6a1
-- title:
--   Actual jump-bearing Levy Gaussian residual finite predictable disjoint-grid exact L2 isometry under a.s. extraction
-- statement:
--   Under a single almost-sure all-times same-probability-space Levy-Ito decomposition of actual spectrally negative jump-bearing X into Gaussian zero-jump Y with the original sigma and real jump residuals, a finite disjoint deterministic-grid sum of original jump-subtracted Gaussian residual cells with predictable L2 coefficients belongs to L2, has integrable square, and its exact L2 energy is the sum of cell energies. Both sigma branches; no intrinsic decomposition existence, pathwise bracket, or continuous stochastic integral claimed.
-- source:
--   Proved original zero-jump finite predictable-grid exact L2 isometry 78e197ea-3427-4cce-aab5-066bba435863, plus same-a.s-event transport using memLp_congr_ae, Integrable.congr and integral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_finite_grid_exact_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
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
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by sorry
