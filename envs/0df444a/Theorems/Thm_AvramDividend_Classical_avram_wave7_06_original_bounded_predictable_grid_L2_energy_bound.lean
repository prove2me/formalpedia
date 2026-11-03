-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_bounded_predictable_grid_L2_energy_bound
-- name    : AvramDividend.Classical.avram_wave7_06_original_bounded_predictable_grid_L2_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:57:17.882735+00:00
-- url     : https://prove2.me/theorems/a721feaa-1535-43ce-ba36-57a845717487
-- title:
--   Bounded original-filtration predictable finite-grid centred Levy L2 martingale energy estimate
-- statement:
--   For actual original spectrally negative Levy X and bounded squared predictable cell coefficients W_i²≤K², the second moment of the weighted centred finite-grid martingale is at most K² times the sum of the exact source increment variances. The finite-grid original-source L2 variance factorisation and integral monotonicity prove the estimate with explicit source moment and mixed integrability assumptions. This is a quantitative energy bound potentially usable for original small-jump truncation tails once a marked-source representation exists.
-- source:
--   W7-06 original scalar bounded predictable finite-grid variance upper bound for source martingale truncation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_bounded_predictable_grid_L2_energy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ) (K : ℝ)
    (hOrder : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → s i + t i ≤ s j)
    (hWPast : ∀ i ∈ Finset.range n, Measurable[𝓕 (s i)] (W i))
    (hWI2 : ∀ i ∈ Finset.range n, Integrable (fun ω => (W i ω)^2) P)
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hXI2 : ∀ i ∈ Finset.range n,
      Integrable (fun ω => (X.X (t i) ω)^2) P)
    (hEarlier : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → Integrable (fun ω =>
        (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) * W j ω) P)
    (hPairI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) * (W j ω * (X.X (s j + t j) ω - X.X (s j) ω -
          (∫ η, X.X (t j) η ∂P)))) P)
    (hWeightBound : ∀ i ∈ Finset.range n, ∀ ω, (W i ω)^2 ≤ K^2) :
    (∫ ω, (∑ i ∈ Finset.range n, (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))))^2 ∂P) ≤
      K^2 * ∑ i ∈ Finset.range n,
        (∫ ω, (X.X (t i) ω - (∫ η, X.X (t i) η ∂P))^2 ∂P) := by sorry
