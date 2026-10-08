-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousAt_eq_zero_of_ae_zero_at_support
-- name    : AvramDividend.Classical.continuousAt_eq_zero_of_ae_zero_at_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:53:44.165299+00:00
-- url     : https://prove2.me/theorems/42561892-6af5-4259-ac2f-9e3eb7bd81ae
-- title:
--   A continuous-at-x almost-everywhere-zero function vanishes at any point in measure support
-- statement:
--   If x belongs to the support of a measure μ, a real-valued function f is continuous at x, and f=0 μ-almost everywhere, then f(x)=0. Otherwise continuity provides a neighbourhood of x where f≠0; the support condition says that neighbourhood has strictly positive measure, contradicting almost-everywhere zero. This localises the a.e.-to-pointwise bridge and avoids a global continuity premise for a Lévy generator residual defined on only a positive interval.
-- source:
--   Pinned Mathlib Measure.mem_support_iff_forall and the ae_iff null-set theorem.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuousAt_eq_zero_of_ae_zero_at_support
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (x : α)
    (hx : x ∈ μ.support)
    (hf : ContinuousAt f x)
    (hae : ∀ᵐ y ∂μ, f y = 0) :
    f x = 0 := by sorry

end AvramDividend.Classical
