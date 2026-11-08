-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zerojump_finite_gaussian_grid_positive_mask
-- name    : AvramDividend.Classical.avram_gaussian12_original_zerojump_finite_gaussian_grid_positive_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:44:42.871479+00:00
-- url     : https://prove2.me/theorems/04fc6555-91c9-4a4d-99a9-67caa3e17763
-- title:
--   Original zero-jump Gaussian stopped Taylor grid martingale vanishes on any positive stopping-clock event
-- statement:
--   For the genuine zero-negative-jump Lévy source X and finite varying stopped clocks with predictable coefficients and integrable Gaussian Taylor cells, the finite-mesh compensated Gaussian martingale is centred after restriction to an arbitrary positive stopping-clock event. Combines the source-specific zero-jump stopped conditional mean theorem with the general masked finite-sum bridge; leaves controlled dividend cash and generator inequalities as independent obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_finite_gaussian_stopped_cells_positive_mask
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussian12_original_zerojump_finite_gaussian_grid_positive_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (G i))
    (hH : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (H i))
    (M : ι → Ω → ℝ)
    (hM : M = (fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c)))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S,
      Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    (∫ ω in {ω : Ω | σ ω ≠ 0}, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
