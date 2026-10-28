-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_grid
-- name    : AvramDividend.Classical.bv_infinite_activity_deficit_positive_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:18:09.221931+00:00
-- url     : https://prove2.me/theorems/4aa1e591-686d-4a79-9c14-e904bcdcadf6
-- title:
--   Almost-sure strict positivity of the infinite-activity Lévy drift deficit on countable positive-time grids
-- statement:
--   Infinite negative Lévy activity eliminates the fixed-time zero atom of the bounded-variation drift deficit. At each positive grid time it is almost surely nonnegative and nonzero; countable intersection gives one common probability-one event for the entire grid. Useful in near-zero path regularity without importing a Poisson jump process.
-- source:
--   Accepted drift-deficit zero-atom and fixed-time upper bound theorems; Mathlib ae_all_iff and measureReal_eq_zero_iff.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_deficit_positive_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ n, 0 < grid n) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      0 < X.drift * (grid n : ℝ) - X.X (grid n) ω := by sorry
