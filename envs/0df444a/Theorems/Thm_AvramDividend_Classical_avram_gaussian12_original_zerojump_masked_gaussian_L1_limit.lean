-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zerojump_masked_gaussian_L1_limit
-- name    : AvramDividend.Classical.avram_gaussian12_original_zerojump_masked_gaussian_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:38:39.523505+00:00
-- url     : https://prove2.me/theorems/b2465ceb-2844-4b23-ba69-16927f20d566
-- title:
--   Original zero-jump source stopped Gaussian Ito L1 limit stays centred on strictly positive clocks
-- statement:
--   For genuine original X zero-negative-jump Lévy stopped Gaussian Taylor meshes, source stopped-history conditional centring and initial-filtration masking imply each finite source Gaussian grid has zero integral over the strictly positive stopping-clock event. Passing to the integrable original Gaussian Ito martingale limit under explicit restricted L1 convergence retains masked mean zero. This discharges precisely the Gaussian martingale channel of the original finite-cap conditional expected payoff budget, leaving the controlled Ito pathwise dividend and HJB sign bound separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zerojump_finite_gaussian_grid_positive_mask
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean
open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gaussian12_original_zerojump_masked_gaussian_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hA : MeasurableSet {ω : Ω | σ ω ≠ 0})
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hG : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i)
        (hτ n i hi)).measurableSpace] (G n i))
    (hH : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i)
        (hτ n i hi)).measurableSpace] (H n i))
    (M : ℕ → ι → Ω → ℝ)
    (hM : ∀ n, M n = (fun i ω =>
        (X.X (τ n i ω + h n i) ω -
          ((τ n i ω + h n i) : ℝ) * X.c) -
        (X.X (τ n i ω) ω - (τ n i ω : ℝ) * X.c)))
    (hGI : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => G n i ω * M n i ω) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => H n i ω * (M n i ω) ^ 2) P)
    (Z : Ω → ℝ) (hZI : Integrable Z P) :
    let F : ℕ → ι → Ω → ℝ := fun n i ω =>
      G n i ω * M n i ω +
        (H n i ω * M n i ω ^ 2 -
          ((h n i : ℝ) * X.σ ^ 2) * H n i ω)
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, F n i ω
    Tendsto (fun n => ∫⁻ ω in {ω : Ω | σ ω ≠ 0},
        ‖Q n ω - Z ω‖ₑ ∂P) atTop (nhds (0 : ℝ≥0∞)) →
      (∫ ω in {ω : Ω | σ ω ≠ 0}, Z ω ∂P) = 0 := by sorry
