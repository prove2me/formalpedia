-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_centered_X_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_centered_X_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:36:59.155167+00:00
-- url     : https://prove2.me/theorems/c60ee11e-744e-49a9-9a8a-8945a4e15586
-- title:
--   Original predictable finite-grid centred Levy scalar L2 martingale isometry
-- statement:
--   For an arbitrary finite ordered grid of genuine original X increments with original-filtration predictable scalar weights, the expectation of the squared centred weighted sum equals the sum of its individual cell energies. The grid intervals are nonoverlapping, and explicit L1 integrability for earlier-weight products and all L2 pair products validates every expectation. Pairwise covariance zero follows from original adaptedness and independent future increments, and finite double-sum integration yields the isometry. This theorem has the precise original X, P and filtration; it does not claim marked jump Poisson compensation.
-- source:
--   W7-06 source-specific finite-grid scalar compensated martingale L2 isometry; consumer W7-07/W7-08 finite-step energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_centered_X_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hOrder : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → s i + t i ≤ s j)
    (hWPast : ∀ i ∈ Finset.range n, Measurable[𝓕 (s i)] (W i))
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hEarlier : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → Integrable (fun ω =>
        (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))) * W j ω) P)
    (hPairI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))) *
        (W j ω * (X.X (s j + t j) ω - X.X (s j) ω -
        (∫ η, X.X (t j) η ∂P)))) P) :
    (∫ ω, (∑ i ∈ Finset.range n,
      (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))))^2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P)))^2 ∂P := by sorry
