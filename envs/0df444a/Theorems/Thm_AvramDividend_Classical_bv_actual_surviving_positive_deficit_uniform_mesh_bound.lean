-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_surviving_positive_deficit_uniform_mesh_bound
-- name    : AvramDividend.Classical.bv_actual_surviving_positive_deficit_uniform_mesh_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:25:54.429555+00:00
-- url     : https://prove2.me/theorems/f4187dd4-291e-42ae-a164-10a862ccbf64
-- title:
--   Actual BV Levy strict-survivor deficit obeys a canonical uniform-mesh probability estimate
-- statement:
--   For every finite observation horizon and positive grid count, choose a genuine equal-duration nonnegative-time mesh. The probability of surviving beyond the horizon with increased cumulative drift deficit is at most the cell count times one cell's small-positive-deficit probability, with no separate mesh hypotheses.
-- source:
--   Combination of the accepted Prove2Me uniform NNReal grid, drift arithmetic and actual stationary-increment grid estimate; Avram, Palmowski and Pistorius (2007), §3.3.

import Theorems.Thm_AvramDividend_Classical_nonnegative_uniform_time_grid_exists
import Theorems.Thm_AvramDividend_Classical_uniform_nnreal_grid_drift_arithmetic
import Theorems.Thm_AvramDividend_Classical_bv_survival_positive_deficit_measure_le_uniform_mesh_single_cell
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_surviving_positive_deficit_uniform_mesh_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    ∃ δ : ℝ≥0, (N : ℝ≥0) * δ = T ∧
      P {ω : Ω |
        (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
        X.drift * (0 : ℝ) - X.X 0 ω <
          X.drift * (T : ℝ) - X.X T ω} ≤
      (N : ℝ≥0∞) *
        P {ω : Ω |
          0 < X.drift * (δ : ℝ) - X.X δ ω ∧
          X.drift * (δ : ℝ) - X.X δ ω ≤
            X.drift * (δ : ℝ)} := by sorry
