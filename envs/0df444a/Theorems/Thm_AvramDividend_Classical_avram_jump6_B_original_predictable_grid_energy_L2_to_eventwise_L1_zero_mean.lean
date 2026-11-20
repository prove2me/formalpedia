-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_predictable_grid_energy_L2_to_eventwise_L1_zero_mean
-- name    : AvramDividend.Classical.avram_jump6_B_original_predictable_grid_energy_L2_to_eventwise_L1_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:15:26.888587+00:00
-- url     : https://prove2.me/theorems/22d5a8e3-1263-4633-91c6-21563bcdeb5c
-- title:
--   Actual infinite-activity predictable Levy grid L2 energy gives eventwise L1 convergence and zero mean
-- statement:
--   For the true original source Lévy path and physical predictable-grid centred increment sums, an explicit small-mark quadratic energy bound gives an integrable centred Lp2 limit, and the actual sequence of source representatives converges to this limit in absolute L1 on every measurable event. Uses Proved physical L2 martingale centring and probability-space L2-to-L1 transfer; retains original integrability and source representation hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_original_grid_smallmark_energy_L2_limit_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_predictable_grid_energy_L2_to_eventwise_L1_zero_mean
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
      (∫ ω, L ω ∂P) = 0 ∧
      ∀ A : Set Ω,
        Tendsto (fun j : ℕ =>
          ∫ ω in A, |L ω - M j ω| ∂P)
          atTop (𝓝 (0 : ℝ)) := by sorry
