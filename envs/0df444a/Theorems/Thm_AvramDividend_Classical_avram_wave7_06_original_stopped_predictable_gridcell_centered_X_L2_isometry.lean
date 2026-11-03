-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:00:51.175997+00:00
-- url     : https://prove2.me/theorems/766928a6-645e-4bff-88bf-8f2b8c2314c3
-- title:
--   Actual original stopped predictable grid-cell centred X increment L2 isometry
-- statement:
--   For a nondecreasing original time grid and the stopped source-past measurable coefficient W_i=1_{i<τ}H_i, the exact original-X centred future increment weighted squared integral factorises into the coefficient second moment and source increment variance. It specialises the Proved original predictable-weight L2 isometry, and does not assert an analogous marked compensated jump integral formula without source marked-cell representation.
-- source:
--   W7-06 stopped predictable finite-grid scalar source martingale L2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : Measurable[𝓕 (grid i)]
      (fun ω => if i < τ ω then H i ω else 0))
    (hW2 : Integrable (fun ω =>
      (if i < τ ω then H i ω else 0)^2) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P)
    (hXSq : Integrable (fun ω =>
      (X.X (grid (i + 1) - grid i) ω)^2) P) :
    (∫ ω,
      ((if i < τ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P)))^2 ∂P) =
    (∫ ω, (if i < τ ω then H i ω else 0)^2 ∂P) *
      (∫ ω, (X.X (grid (i + 1) - grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P))^2 ∂P) := by sorry
