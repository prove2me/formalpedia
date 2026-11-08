-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_original_gaussian_initial_event_L1_limit
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn11_original_gaussian_initial_event_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T00:47:24.159514+00:00
-- url     : https://prove2.me/theorems/7e72461b-cfa2-4a0c-9801-87797b996672
-- title:
--   Original zero-jump stopped Gaussian Ito L1 limits remain centred on every initial-filtration event
-- statement:
--   Actual zero-jump Lévy Gaussian stopped Taylor-grid sums that converge in restricted L1 to an integrable martingale limit retain zero integral on every event observable initially. This upgrades the previous positive-clock-only Gaussian L1 limit and is a source-backed route to the initial-event martingale centring required by the finite-cap HJB verification budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_original_gaussian_grid_initial_event_zero

open MeasureTheory ProbabilityTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn11_original_gaussian_initial_event_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
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
    let Q : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ S n, F n i ω
    Tendsto (fun n => ∫⁻ ω in A, ‖Q n ω - Z ω‖ₑ ∂P)
      atTop (nhds (0 : ℝ≥0∞)) →
      (∫ ω in A, Z ω ∂P) = 0 := by sorry
