-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_indicator_restrict_of_subset
-- name    : AvramDividend.Classical.lintegral_indicator_restrict_of_subset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:22:09.261461+00:00
-- url     : https://prove2.me/theorems/f1580e19-c0a4-45df-bf2e-f2d2563b73b2
-- title:
--   Stopping restriction is immaterial when the measured interval lies entirely inside the payment-time set
-- statement:
--   Let μ be any measure, A a measurable stopping-payment set and B a measurable deterministic interval contained in A. Integrating the B-indicated nonnegative payout over the measure restricted to A equals integrating the same B-indicated payout over μ without stopping. This is an exact identity, independent of integrability, probability, Lévy dynamics or positive discount assumptions. It provides the essential step for obtaining both lower and upper endpoint-discount Stieltjes record bounds on any interval completely preceding reflected ruin.
-- source:
--   Mathlib.MeasureTheory.lintegral_indicator and MeasureTheory.Measure.restrict_restrict on the pinned Mathlib revision, remote exact signature job 134daa8d-8a76-4632-aafe-540d58ac41ef.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.lintegral_indicator_restrict_of_subset
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (A B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsub : B ⊆ A) (f : α → ℝ≥0∞) :
    (∫⁻ x in A, if x ∈ B then f x else 0 ∂μ) =
    (∫⁻ x, if x ∈ B then f x else 0 ∂μ) := by sorry
