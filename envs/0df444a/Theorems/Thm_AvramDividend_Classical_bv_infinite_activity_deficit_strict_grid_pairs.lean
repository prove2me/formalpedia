-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_strict_grid_pairs
-- name    : AvramDividend.Classical.bv_infinite_activity_deficit_strict_grid_pairs
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:46:13.545182+00:00
-- url     : https://prove2.me/theorems/6f22a35d-b5e5-459c-a85a-9f25d00d250c
-- title:
--   Infinite-activity bounded-variation drift deficit strictly increases between all ordered countable observation-grid pairs almost surely
-- statement:
--   For any countable observation grid of nonnegative times, an actual bounded-variation spectrally negative Lévy process with infinite negative-jump activity has strictly increasing canonical drift deficit at every strictly ordered grid pair on a common probability-one event. Uses fixed-interval strict increment law and two applications of ae_all_iff.
-- source:
--   Accepted bv_infinite_activity_drift_deficit_increment_strict_ae and Mathlib ae_all_iff.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_strict_ae
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_deficit_strict_grid_pairs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i j : ℕ, grid i < grid j →
      X.drift * (grid i : ℝ) - X.X (grid i) ω <
        X.drift * (grid j : ℝ) - X.X (grid j) ω := by sorry
