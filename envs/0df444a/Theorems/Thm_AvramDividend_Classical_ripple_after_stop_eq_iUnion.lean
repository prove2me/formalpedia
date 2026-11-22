-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_after_stop_eq_iUnion
-- name    : AvramDividend.Classical.ripple_after_stop_eq_iUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:53:13.691134+00:00
-- url     : https://prove2.me/theorems/15c63330-b293-4301-92a0-f7cb4467db4a
-- title:
--   Rational rectangle decomposition of the strict after-stop stochastic region
-- statement:
--   For a nonnegative-real-time stopping time, the strict post-stop epigraph is the countable union over rational cut times of the post-rational time interval and the event that the stop is before the rational cut.
-- source:
--   Source proof adapted from zinan-huang/Ripple, Ripple/Stochastic/StoppedPredictableIntegrand.lean, commit e216e28ce3ffb43877e11f71be260e40a37a35df, Apache-2.0; intended as a real mathematical child of AvramDividend.Classical.ripple_stopping_region_predictable.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ripple_after_stop_eq_iUnion
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0) :
    {z : ℝ≥0 × Ω | τ z.2 < (z.1 : WithTop ℝ≥0)} =
      ⋃ q : ℚ, Ioi (Real.toNNReal (q : ℝ)) ×ˢ
        {ω | τ ω ≤ (Real.toNNReal (q : ℝ) : WithTop ℝ≥0)} := by sorry
