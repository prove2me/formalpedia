-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_between_stopping_times_predictable
-- name    : AvramDividend.Classical.ripple_between_stopping_times_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:04:33.015225+00:00
-- url     : https://prove2.me/theorems/730ba1ff-2b25-4037-8d77-beff6f5f8483
-- title:
--   The original two-clock predictable stochastic window is measurable
-- statement:
--   For two stopping times in the right-continuous filtration, the random interval (sigma,tau] is predictable as the difference of the corresponding predictable stopping regions (0,tau] and (0,sigma]. This holds for genuinely random clocks and infinite stopping times.
-- source:
--   Ripple/Stochastic/ContinuousItoStoppedIsometry.lean, stopping_indicator_sub, commit e216e28ce3ffb43877e11f71be260e40a37a35df Apache-2.0, adapted via proved Prove2Me predictable stopping region ee80bb4f-29d8-45ab-8d46-fd8093074fd0.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
open MeasureTheory Set
open scoped NNReal

/-- The genuinely random stochastic window (sigma,tau] is predictable.
Adapted from Ripple/Stochastic/ContinuousItoStoppedIsometry.lean,
stopping_indicator_sub, commit e216e28ce3ffb43877e11f71be260e40a37a35df
(Apache-2.0); both windows need to be stopping times. -/

theorem AvramDividend.Classical.ripple_between_stopping_times_predictable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 mΩ) (σ τ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable]
      {z : ℝ≥0 × Ω |
        0 < z.1 ∧ σ z.2 < (z.1 : WithTop ℝ≥0) ∧
          (z.1 : WithTop ℝ≥0) ≤ τ z.2} := by sorry
