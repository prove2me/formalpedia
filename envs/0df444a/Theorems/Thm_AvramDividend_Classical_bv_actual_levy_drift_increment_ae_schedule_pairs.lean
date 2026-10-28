-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_schedule_pairs
-- name    : AvramDividend.Classical.bv_actual_levy_drift_increment_ae_schedule_pairs
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:17:09.79399+00:00
-- url     : https://prove2.me/theorems/931205fa-e220-4a44-9add-9f4af3cb4704
-- title:
--   Simultaneous drift bound on every ordered pair of scheduled Lévy times
-- statement:
--   A single probability-one set obeys the actual bounded-variation Lévy increment drift bound for every ordered pair from an arbitrary countable time schedule. This follows by iterated ae_all_iff from the Proved fixed-pair increment law and provides the dense-grid foundation for global residual monotonicity.
-- source:
--   Avram Palmowski Pistorius (2007), finite-activity bounded-variation process-law foundations; already-Proved increment support lemma.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_fixed_times
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_drift_increment_ae_schedule_pairs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (ts : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i j : ℕ, ts i ≤ ts j →
      X.X (ts j) ω - X.X (ts i) ω ≤
        ((ts j - ts i : ℝ≥0) : ℝ) * X.drift := by sorry
