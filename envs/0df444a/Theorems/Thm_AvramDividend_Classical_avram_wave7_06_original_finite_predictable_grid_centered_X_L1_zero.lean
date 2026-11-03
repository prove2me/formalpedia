-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:31:29.42691+00:00
-- url     : https://prove2.me/theorems/fcf6e557-dd63-418a-9742-1a69c5a6fc4e
-- title:
--   Finite-grid original-filtration predictable centred Levy martingale has L1 mean zero
-- statement:
--   For every finite family of genuine original X future increments and their predictable original-filtration weights, their centred scalar sum has expectation zero. Assumptions give exact source past measurability and integrable weight and future X increments at each cell; cell integrability validates finite-sum interchange. This includes stopped predictable weights once their adaptedness/integrability is established. No auxiliary sample space.
-- source:
--   W7-06 original source finite-grid compensation L1 expectation identity; stopped scalar martingale precursor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hWPast : ∀ i ∈ Finset.range n, Measurable[𝓕 (s i)] (W i))
    (hWI : ∀ i ∈ Finset.range n, Integrable (W i) P)
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hCellI : ∀ i ∈ Finset.range n, Integrable (fun ω =>
      W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))) P) :
    (∫ ω, ∑ i ∈ Finset.range n,
      W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P)) ∂P) = 0 := by sorry
