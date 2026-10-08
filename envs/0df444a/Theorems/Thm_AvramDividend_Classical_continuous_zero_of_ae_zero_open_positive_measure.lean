-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_zero_of_ae_zero_open_positive_measure
-- name    : AvramDividend.Classical.continuous_zero_of_ae_zero_open_positive_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:08:38.701194+00:00
-- url     : https://prove2.me/theorems/bc1944c0-45ad-4bf3-a285-e0d3c26f450a
-- title:
--   Continuous function vanishing almost everywhere vanishes everywhere for a full-support measure
-- statement:
--   On a measurable topological space where every nonempty open set has positive measure, a continuous real function that vanishes almost everywhere vanishes identically. The zero set is closed and conull, so it contains the support of the measure, which is the whole space. This is the final generic bridge for upgrading an almost-everywhere vanishing Levy generator residual to a pointwise identity once continuity and an almost-everywhere q-harmonicity statement have been independently proved.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.support_subset_of_isClosed and support_eq_univ; continuity and measure support.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuous_zero_of_ae_zero_open_positive_measure
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [μ.IsOpenPosMeasure]
    (f : α → ℝ) (hf : Continuous f)
    (hzero : ∀ᵐ x ∂μ, f x = 0) :
    ∀ x : α, f x = 0 := by sorry

end AvramDividend.Classical
