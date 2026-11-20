-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_original_gaussian_physical_L1_limit_initial_condzero
-- name    : AvramDividend.Classical.avram_a19_original_gaussian_physical_L1_limit_initial_condzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:14:34.106436+00:00
-- url     : https://prove2.me/theorems/100a0b89-4842-4d43-bfc1-c237749cbf09
-- title:
--   Original physical Gaussian stopped finite-grid L1 limit retains initial conditional zero
-- statement:
--   For the original zero-jump Lévy Gaussian process, construct the genuine finite stopped Taylor Gaussian linear-plus-quadratic centred sums with original predictable coefficients and original X increments. When those physical sums converge in L1 to an integrable limit L, the limit has conditional expectation zero at the original initial sigma-algebra. This directly combines Proved 13c649df (physical finite-grid conditional martingale) and Proved 64edbbf5 (conditional L1 transfer), without assuming HJB inequality, ruin-contact error or arbitrary source martingales. It is the precise probabilistic centring component needed in source e4624500.
-- source:
--   Original physical stopped Gaussian two-term Ito/Taylor grid with bounded rightCont predictable coefficients, finite aggregation, conditional L1 limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- The true stopped Gaussian physical grid limit inherits initial conditional centring. -/
theorem AvramDividend.Classical.avram_a19_original_gaussian_physical_L1_limit_initial_condzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hF0 : 𝓕.rightCont 0 ≤ mΩ)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hBound : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hG : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events
        (τ n i) (hτ n i hi)).measurableSpace] (G n i))
    (hH : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events
        (τ n i) (hτ n i hi)).measurableSpace] (H n i))
    (M : ℕ → ι → Ω → ℝ)
    (hM : ∀ n, M n = fun i ω =>
      (X.X (τ n i ω + h n i) ω -
        ((τ n i ω + h n i) : ℝ) * X.c) -
      (X.X (τ n i ω) ω - (τ n i ω : ℝ) * X.c))
    (hGI : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => G n i ω * M n i ω) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => H n i ω * (M n i ω) ^ 2) P)
    (L : Ω → ℝ) (hLI : Integrable L P)
    (hL1 : Tendsto
      (fun n => eLpNorm (fun ω =>
        L ω - ∑ i ∈ S n,
          (G n i ω * M n i ω +
            (H n i ω * M n i ω ^ 2 -
              ((h n i : ℝ) * X.σ ^ 2) * H n i ω))) 1 P)
      atTop (nhds 0)) :
    condExp (𝓕.rightCont 0) P L =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
