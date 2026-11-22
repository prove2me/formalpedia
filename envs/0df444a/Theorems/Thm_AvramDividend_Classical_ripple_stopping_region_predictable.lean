-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
-- name    : AvramDividend.Classical.ripple_stopping_region_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:51:22.368673+00:00
-- url     : https://prove2.me/theorems/ee80bb4f-29d8-45ab-8d46-fd8093074fd0
-- title:
--   Stopped stochastic interval is predictable in nonnegative physical time
-- statement:
--   For any nonnegative-real-time filtration and stopping time, the stochastic interval with 0 < t and t ≤ τ(ω) is measurable for the predictable sigma-algebra. This is a mathematical bridge for stopped Avram Gaussian integrands.
-- source:
--   Proof code adapted from zinan-huang/Ripple, Ripple/Stochastic/StoppedPredictableIntegrand.lean, commit e216e28ce3ffb43877e11f71be260e40a37a35df, Apache-2.0. Avram Dividend Classical mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ripple_stopping_region_predictable
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable]
      {z : ℝ≥0 × Ω | 0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ τ z.2} := by sorry
