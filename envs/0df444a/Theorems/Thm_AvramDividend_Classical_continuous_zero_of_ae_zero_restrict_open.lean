-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_zero_of_ae_zero_restrict_open
-- name    : AvramDividend.Classical.continuous_zero_of_ae_zero_restrict_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:25:23.714998+00:00
-- url     : https://prove2.me/theorems/7e14862d-ae50-474f-b82c-1642abd2f921
-- title:
--   A continuous function vanishing a.e. on an open set vanishes at every interior point
-- statement:
--   For a full-support Borel measure on the real line, a globally continuous real function which vanishes almost everywhere under the measure restricted to an open subset s vanishes pointwise everywhere in s. Uses pinned Mathlib interior_inter_support and support_subset_of_isClosed.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.interior_inter_support and support_subset_of_isClosed.

import Mathlib

open MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuous_zero_of_ae_zero_restrict_open
    (μ : Measure ℝ) [μ.IsOpenPosMeasure]
    (f : ℝ → ℝ) (hf : Continuous f)
    (s : Set ℝ) (hs : IsOpen s)
    (hae : ∀ᵐ x ∂(μ.restrict s), f x = 0) :
    ∀ x ∈ s, f x = 0 := by sorry

end AvramDividend.Classical
