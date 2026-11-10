-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_cells_F0_centred
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_original_cells_F0_centred
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:28:11.744202+00:00
-- url     : https://prove2.me/theorems/13c649df-bb14-4303-8164-3e045c78cf24
-- title:
--   Finite original stopped Gaussian predictable cells remain conditionally centred at time zero
-- statement:
--   Exact initial-original-filtration centring interface needed by finite-cap stopped C2 physical Gaussian reward a338c453-58c0-411c-aaca-5cec689ed807 and top-cap masked stopped positive-clock source 249c532d-4ec0-498c-81f0-b380dd476344. For finite genuinely stopped cells built from the original X.X Gaussian increments on the same Ω,P and right-continuous filtration, with G,H measurable in their true stopped histories and explicit integrable linear and quadratic products, Proved 4a4b4e27 gives each original compensated C2 cell integrable and conditional expectation zero in its stopped history. Since time zero precedes every nonnegative stop, conditional expectation tower yields zero at F.rightCont 0; finite linearity supplies the complete integrable initially centred finite-grid sum. The relevant parent must still prove its actual controlled left-limit coefficients are measurable at each stopped history, assemble the physical Ito-Stieltjes ledger and handle payment/ruin/final atom boundaries. No detached Brownian source and no floor stopping clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_original_cells_F0_centred
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
      (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      P[(fun ω => ∑ i ∈ S, F i ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
  sorry
