-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_stopping_time_early_observed_switch
-- name    : AvramDividend.Classical.chat08_stopping_time_early_observed_switch
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:41:49.022292+00:00
-- url     : https://prove2.me/theorems/8901c301-4d7a-4700-9b39-7508d8cece79
-- title:
--   Switching to an earlier observed event preserves the stopping-time property
-- statement:
--   Let s be a deterministic time, A an event observable by s, and τ a stopping time never earlier than s. The clock which stops at s on A and otherwise follows τ is a stopping time. Repeated application constructs finite-grid first-upcrossing stopping clocks.
-- source:
--   Mathlib.Probability.Process.Stopping; filtration monotonicity.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_stopping_time_early_observed_switch
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (hlater : ∀ ω, (s : WithTop ℝ≥0) ≤ τ ω) :
    IsStoppingTime ℱ
      (fun ω => if ω ∈ A then (s : WithTop ℝ≥0) else τ ω) := by sorry
