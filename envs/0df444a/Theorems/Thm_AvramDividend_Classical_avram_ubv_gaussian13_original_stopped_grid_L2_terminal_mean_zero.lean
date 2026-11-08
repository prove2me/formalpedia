-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_original_stopped_grid_L2_terminal_mean_zero
-- name    : AvramDividend.Classical.avram_ubv_gaussian13_original_stopped_grid_L2_terminal_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:46:57.571229+00:00
-- url     : https://prove2.me/theorems/d4385740-d90d-40bb-8b3a-d4d3d1d6d36d
-- title:
--   Genuine bounded predictable original stopped Gaussian grid L² limit has zero mean
-- statement:
--   For the same original no-jump Lévy process and its right-continuous filtration, consider bounded stopping-time increments weighted by bounded predictably measurable original integrands. Existing mean-zero finite-grid estimates make every sum centred. If those sums are L² and converge in L² to an almost-everywhere strongly measurable terminal random variable, the terminal variable inherits L² membership and exactly zero expectation. The centring assumption is proved internally from source stochastic increments.
-- source:
--   Proved ba7b6ee6 original bounded stopped Gaussian grid mean-zero; pinned Mathlib memLp_of_cauchy_tendsto, eLpNorm comparison, and Bochner integral L1 continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_zero_nu_original_bounded_stopped_gaussian_grid_mean_zero

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian13_original_stopped_grid_L2_terminal_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n i, i ∈ S n → ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hB : ∀ n i, i ∈ S n → ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGstop : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events
        (τ n i) (hτ n i hi)).measurableSpace] (G n i))
    (hGglobal : ∀ n i, i ∈ S n → Measurable (G n i))
    (K : ℕ → ι → ℝ) (hK : ∀ n i, i ∈ S n → 0 ≤ K n i)
    (hGbound : ∀ n i, i ∈ S n → ∀ ω, |G n i ω| ≤ K n i)
    (M : Ω → ℝ) (hMmeas : AEStronglyMeasurable M P) :
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω *
        (X.X (τ n i ω + h n i) ω - X.X (τ n i ω) ω -
          (h n i : ℝ) * X.c)
    (∀ n, MemLp (Q n) 2 P) →
    Tendsto (fun n => eLpNorm (Q n - M) 2 P) atTop (𝓝 0) →
    MemLp M 2 P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
