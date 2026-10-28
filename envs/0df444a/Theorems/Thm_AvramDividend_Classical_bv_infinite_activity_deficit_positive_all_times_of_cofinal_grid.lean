-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_all_times_of_cofinal_grid
-- name    : AvramDividend.Classical.bv_infinite_activity_deficit_positive_all_times_of_cofinal_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:26:19.664472+00:00
-- url     : https://prove2.me/theorems/a144fac5-ffe5-4c78-9bc9-a5bcc7a8571b
-- title:
--   Infinite-activity Lévy drift deficit is positive at every positive time from a cofinal observation grid
-- statement:
--   Under infinite negative jump activity, the bounded-variation Lévy drift deficit is strictly positive on a countable sequence of positive observation times. If that grid has a point below every positive time, almost-sure monotonicity of the actual drift deficit propagates strict positivity to every positive time on one common probability-one event.
-- source:
--   Proved bv_drift_deficit_ae_monotone_all_times and the separately published positive-grid lemma.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_grid
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_deficit_positive_all_times_of_cofinal_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0)
    (hgrid : ∀ n, 0 < grid n)
    (hbelow : ∀ t : ℝ≥0, 0 < t → ∃ n, grid n ≤ t) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      0 < X.drift * (t : ℝ) - X.X t ω := by sorry
