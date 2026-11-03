-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_finite_predictable_grid_X_L1_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_stopped_finite_predictable_grid_X_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:48:35.06329+00:00
-- url     : https://prove2.me/theorems/e191bf58-b677-404c-875a-7a84acb1c6df
-- title:
--   Original stopped predictable finite-grid centred Levy sum has exact zero mean
-- statement:
--   On a monotone time grid, the stopped original-filtration predictable scalar coefficient 1_{i<τ} H_i multiplied by each actual centred X future increment has zero expected finite total sum, provided weights, source increments and weighted cells are integrable. The proof substitutes stopped coefficients in the general original finite-grid L1 martingale theorem and uses grid monotonicity to identify s_i+(s_(i+1)-s_i) with s_(i+1).
-- source:
--   W7-06 explicit original stopped finite-grid scalar martingale expectation zero for W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_stopped_finite_predictable_grid_X_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : Monotone grid)
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : ∀ i ∈ Finset.range n,
      Measurable[𝓕 (grid i)]
        (fun ω => if i < τ ω then H i ω else 0))
    (hWI : ∀ i ∈ Finset.range n,
      Integrable (fun ω => if i < τ ω then H i ω else 0) P)
    (hXI : ∀ i ∈ Finset.range n,
      Integrable (X.X (grid (i + 1) - grid i)) P)
    (hCellI : ∀ i ∈ Finset.range n, Integrable (fun ω =>
      (if i < τ ω then H i ω else 0) *
        (X.X (grid i + (grid (i + 1) - grid i)) ω -
          X.X (grid i) ω -
            (∫ η, X.X (grid (i + 1) - grid i) η ∂P))) P) :
    (∫ ω, ∑ i ∈ Finset.range n,
      (if i < τ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by sorry
