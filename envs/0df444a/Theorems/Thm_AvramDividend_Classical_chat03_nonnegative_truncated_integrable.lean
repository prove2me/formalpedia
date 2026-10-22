-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncated_integrable
-- name    : AvramDividend.Classical.chat03_nonnegative_truncated_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:55:44.190964+00:00
-- url     : https://prove2.me/theorems/bc8216f4-be78-43e0-b504-52d094ef2d6d
-- title:
--   Integrability of nonnegative bounded truncations
-- statement:
--   The finite nonnegative clipping of an almost-everywhere strongly measurable and almost-everywhere nonnegative real random variable is integrable under a probability measure. Its absolute value is bounded by the clipping threshold.
-- source:
--   Bounded measurable functions are integrable under a finite measure, using MeasureTheory.Integrable.of_bound.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory

theorem AvramDividend.Classical.chat03_nonnegative_truncated_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hYm : AEStronglyMeasurable Y P)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) :
    Integrable (fun ω => min (Y ω) R) P := by sorry
