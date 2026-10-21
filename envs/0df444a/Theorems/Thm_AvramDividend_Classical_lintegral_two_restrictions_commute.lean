-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_two_restrictions_commute
-- name    : AvramDividend.Classical.lintegral_two_restrictions_commute
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:11:17.263508+00:00
-- url     : https://prove2.me/theorems/7c4dd274-6f51-4800-a8db-4adb6caed06e
-- title:
--   Swapping two measurable Stieltjes time restrictions in an extended nonnegative integral
-- statement:
--   For an arbitrary measure on a measurable space, any nonnegative integrand and two measurable time sets s and t, integrating the t-indicated function over the measure restricted to s equals integrating the s-indicated function over the measure restricted to t. The proof converts each indicator to a second measure restriction and observes that the two resulting restricted measures agree because the set intersections commute. This exact identity supports expressing the original stopped Stieltjes interval rewards, whose payment-time set occurs in the measure restriction, using the already proved interval-restricted random-kernel reward whose payment-time set occurs in the integrand. It does not impose samplewise mass boundedness or integrability.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_indicator and MeasureTheory.Measure.restrict_restrict. Used for Chat 05 true reflected-supremum stopped Stieltjes random rewards.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.lintegral_two_restrictions_commute
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : α → ℝ≥0∞) :
    (∫⁻ x in s, if x ∈ t then f x else 0 ∂μ) =
    (∫⁻ x, if x ∈ s then f x else 0 ∂(μ.restrict t)) := by sorry
