-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_finite_grid_variance_factorisation
-- name    : AvramDividend.Classical.avram_wave7_06_original_stopped_finite_grid_variance_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:49:28.668784+00:00
-- url     : https://prove2.me/theorems/43d64323-96b1-4135-b3d4-d6c4d34ab1b6
-- title:
--   Actual stopped original-predictable finite-grid centred Levy L2 variance factorisation
-- statement:
--   The exact second moment of a finite sum of original-process X centred increments multiplied by stopped predictable coefficients 1_{i<τ}H_i equals the sum of E[stopped-weight²] Var(X_ti), on ordered nonoverlapping cells. Each coefficient is required original-source past measurable and all source moments and pair products are integrable. It specialises the genuine original finite-grid isometry and does not assert marked jump isometry without source Poisson law.
-- source:
--   W7-06 explicit stopped finite-grid original scalar source martingale L² energy for W7-07/W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_stopped_finite_grid_variance_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hOrder : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → s i + t i ≤ s j)
    (hWPast : ∀ i ∈ Finset.range n,
      Measurable[𝓕 (s i)] (fun ω => if i < τ ω then H i ω else 0))
    (hWI2 : ∀ i ∈ Finset.range n,
      Integrable (fun ω => (if i < τ ω then H i ω else 0)^2) P)
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hXI2 : ∀ i ∈ Finset.range n,
      Integrable (fun ω => (X.X (t i) ω)^2) P)
    (hEarlier : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → Integrable (fun ω =>
        ((if i < τ ω then H i ω else 0) *
        (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) *
          (if j < τ ω then H j ω else 0)) P)
    (hPairI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => ((if i < τ ω then H i ω else 0) *
        (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) *
        ((if j < τ ω then H j ω else 0) *
        (X.X (s j + t j) ω - X.X (s j) ω -
          (∫ η, X.X (t j) η ∂P)))) P) :
    (∫ ω, (∑ i ∈ Finset.range n, ((if i < τ ω then H i ω else 0) *
        (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))))^2 ∂P) =
      ∑ i ∈ Finset.range n,
        (∫ ω, (if i < τ ω then H i ω else 0)^2 ∂P) *
          (∫ ω, (X.X (t i) ω - (∫ η, X.X (t i) η ∂P))^2 ∂P) := by sorry
