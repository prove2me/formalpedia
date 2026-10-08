-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_zero_of_ae_zero_restrict_open
-- name    : AvramDividend.Classical.continuousOn_zero_of_ae_zero_restrict_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:26:27.441993+00:00
-- url     : https://prove2.me/theorems/690d26cd-85fe-4bf3-b115-d390bb0a0db1
-- title:
--   An a.e.-vanishing continuous function on an open interval vanishes pointwise there
-- statement:
--   Let a full-support real measure μ be restricted to an open set s. If f is continuous on s and f vanishes μ-almost everywhere in s, it vanishes at every point in s. At any interior point where f is hypothetically nonzero, continuity supplies a neighborhood of nonzero values; the support of the restricted measure includes the point and forces positive measure of this neighborhood, contradicting a.e. zero. Crucially only local continuity is assumed, not global continuity; applicable to a Lévy generator residual established continuous on compact interior intervals.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.interior_inter_support and mem_support_iff_forall, and continuity-on-open-set.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuousOn_zero_of_ae_zero_restrict_open
    (μ : Measure ℝ) [μ.IsOpenPosMeasure]
    (s : Set ℝ) (hs : IsOpen s)
    (f : ℝ → ℝ) (hf : ContinuousOn f s)
    (hae : ∀ᵐ x ∂(μ.restrict s), f x = 0) :
    ∀ x ∈ s, f x = 0 := by sorry

end AvramDividend.Classical
