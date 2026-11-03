-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:10:59.149865+00:00
-- url     : https://prove2.me/theorems/00d9de67-d50a-4e9d-95d7-4c63a2180ac3
-- title:
--   Original stopped predictable source gridcell centered X has zero weighted L1 mean
-- statement:
--   For the actual canonical X on the original Ω/P/𝓕 and a nondecreasing time grid, any integrable stopped predictable grid coefficient 1_{i<τ}H_i satisfies E[1_{i<τ}H_i (X_(grid i+1)-X_(grid i)-E[X_(length)])]=0. This is source X compensation, not a marked jump-band identity.
-- source:
--   W7-06 actual stopped predictable finite-grid original-process L1 martingale cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : Measurable[𝓕 (grid i)]
      (fun ω => if i < τ ω then H i ω else 0))
    (hWI : Integrable (fun ω =>
      if i < τ ω then H i ω else 0) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P) :
    (∫ ω, (if i < τ ω then H i ω else 0) *
      (X.X (grid (i + 1)) ω - X.X (grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by sorry
