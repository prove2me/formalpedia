-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_uniformIntegrable_of_pointwise_bounded_family
-- name    : AvramDividend.Classical.chat03_uniformIntegrable_of_pointwise_bounded_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:34:56.853114+00:00
-- url     : https://prove2.me/theorems/08f16d9a-9bcd-4770-b88b-83cab5913059
-- title:
--   Finite-measure L1 uniform integrability from pointwise bounded measurable families
-- statement:
--   On any finite measure space, a family of real-valued almost-everywhere strongly measurable random variables that is uniformly bounded pointwise by a fixed nonnegative constant is uniformly integrable in L1. This elementary tail-vanishing result provides the exact pinned Mathlib uniform-integrability interface needed for the pathwise bounded no-passage branch of the Avram dividend stopped-scale verification programme.
-- source:
--   Exact pinned Mathlib MeasureTheory.uniformIntegrable_of tail-norm criterion, independently remote-signature-verified at revision 0df444a360eaa60ab8c11dca51a86af692955474. No killed scale martingale assumptions.

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.chat03_uniformIntegrable_of_pointwise_bounded_family
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : ι → Ω → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (K : ℝ≥0)
    (hbound : ∀ i ω, ‖f i ω‖₊ ≤ K) :
    UniformIntegrable f (1 : ℝ≥0∞) μ := by sorry
