-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_predictable_stopped_mesh_L1_limit_mean_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_predictable_stopped_mesh_L1_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:30:19.572195+00:00
-- url     : https://prove2.me/theorems/6de09ea4-797b-443e-8ca7-d9f65836044d
-- title:
--   Original Levy stopped Gaussian predictable C2 mesh L1 limit preserves zero expectation
-- statement:
--   Under an almost-sure same-space decomposition of the genuine spectrally negative Levy source X into its source-centred zero-jump Gaussian component and its jumps, genuine stopped-history predictable mesh weights, the exact finite L1 hypotheses and L1 convergence to f, the original-process Gaussian stochastic Taylor integral and compensated quadratic-variation limit have zero expectation. The half sigma-squared correction is preserved, including sigma zero. No Brownian process is assumed and the source decomposition and convergence are explicit upstream obligations.
-- source:
--   Source-specific corollary of two formally published original stopped variable-mesh finite Taylor identities and the proved L1 limit of zero-mean stochastic sums; Proposition 4(i), equation (5.13), Avram, Palmowski and Pistorius.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_full_taylor_L1_sum_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_predictable_stopped_mesh_L1_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hGstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (G n i))
    (hHstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (H n i))
    (hGglobal : ∀ n, ∀ i ∈ S n, Measurable (G n i))
    (hHglobal : ∀ n, ∀ i ∈ S n, Measurable (H n i))
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : ∀ u ω, Z u ω =
      X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω)
    (hGI : ∀ n, ∀ i ∈ S n, Integrable (fun ω => G n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω)) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n, Integrable (fun ω => H n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2) P)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω = ∑ i ∈ S n,
        (G n i ω * (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) +
        (1 / 2 : ℝ) * H n i ω *
          ((Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2 -
            (h n i : ℝ) * X.σ ^ 2)))
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖F n ω - f ω‖ₑ ∂P)
      atTop (nhds 0)) :
    (∫ ω, f ω ∂P) = 0 := by sorry
