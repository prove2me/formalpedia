-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_original_gaussian_global_L1_all_initial_events
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn11_original_gaussian_global_L1_all_initial_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T00:53:47.383177+00:00
-- url     : https://prove2.me/theorems/7bc909cb-d6a5-4a2b-91b6-76c600b41eb5
-- title:
--   One global L1 Gaussian stopped-Ito mesh limit centres the actual Lévy martingale on every initial event
-- statement:
--   If original pure-Gaussian Lévy stopped Taylor-mesh sums converge globally in L1 to an integrable limit, the limit integrates to zero over every initially measurable event. Finite-grid conditional centring and L1 monotonicity under restriction produce a single uniform initial-event stochastic bridge suitable for finite-cap HJB verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_original_gaussian_initial_event_L1_limit

open MeasureTheory ProbabilityTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn11_original_gaussian_global_L1_all_initial_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
    Tendsto (fun n => ∫⁻ ω, ‖Q n ω - Z ω‖ₑ ∂P)
      atTop (nhds (0 : ℝ≥0∞)) →
      ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, Z ω ∂P) = 0 := by sorry
