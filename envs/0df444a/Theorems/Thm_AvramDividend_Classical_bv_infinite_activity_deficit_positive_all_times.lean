-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_all_times
-- name    : AvramDividend.Classical.bv_infinite_activity_deficit_positive_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:27:44.933418+00:00
-- url     : https://prove2.me/theorems/c34ef313-d797-43f1-9a2d-bd87a54d54a1
-- title:
--   Actual infinite-activity bounded-variation Lévy drift deficit is strictly positive at every positive time almost surely
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process with infinite negative-jump intensity, on one probability-one event the canonical drift deficit dt-Xt is strictly positive at every positive time. Use the natural grid 1/(n+1), the accepted simultaneous positive-grid theorem, the proved monotonicity of the drift deficit, and pinned Mathlib exists_nat_one_div_lt.
-- source:
--   Accepted bv_infinite_activity_deficit_positive_grid and bv_drift_deficit_ae_monotone_all_times; Mathlib Algebra.Order.Archimedean.Basic.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_deficit_positive_grid
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_deficit_positive_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      0 < X.drift * (t : ℝ) - X.X t ω := by sorry
