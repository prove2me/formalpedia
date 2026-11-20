-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_original_grid_smallmark_energy_L2_limit_zero_mean
-- name    : AvramDividend.Classical.avram_jump6_B_actual_original_grid_smallmark_energy_L2_limit_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:03:51.990466+00:00
-- url     : https://prove2.me/theorems/66c39d01-3e35-4e68-bbf9-e6ec28428382
-- title:
--   Original Levy adapted physical-grid martingale L2 limit has zero expectation from small-mark energy bound
-- statement:
--   For the actual spectrally negative Levy path, the finite predictable-grid sums of source Levy increments centred by the true expected increment admit a zero-mean L2 martingale limit when their actual Lp2 representatives satisfy the Levy small-negative-mark energy tail bound. Derives the Cauchy condition using the original physical band estimate; no independent Brownian replacement, finite jump activity, or assumed martingale convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_smallmark_Lp2_limit_from_physical_band_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_original_grid_smallmark_energy_L2_limit_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)] (W k i))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (W k i) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
        (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P)))
    (Cband : ℝ)
    (hBandBound : ∀ i j : ℕ, i ≤ j →
      dist (M i) (M j) ≤
        Cband * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((i : ℝ) + 1))) (0 : ℝ),
          ENNReal.ofReal (z ^ 2) ∂X.ν).toReal)) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
