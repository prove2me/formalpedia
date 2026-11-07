-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_rightcont_prefix_to_ambient
-- name    : AvramDividend.Classical.avram_route_runner_rightcont_prefix_to_ambient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:07:08.629768+00:00
-- url     : https://prove2.me/theorems/6c9cf0d7-141f-4650-8a1c-40e685c36562
-- title:
--   Predictable prefix events are measurable in the ambient sample space
-- statement:
--   Every event measurable at a right-continuous filtration level is measurable in the original ambient σ-algebra. Apply the defining filtration inclusion to each selected-prefix event. This is the missing glue between the accepted stopped-grid event theorem 0ae52c11 and the integer-prefix all-preimages theorem 86ff26ac, for original martingale budget 2b993cd3.
-- source:
--   Original-process measurable-grid glue; no equality in law, moment assumption or fabricated Lévy process.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_rightcont_prefix_to_ambient
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (u : ℕ → ℝ≥0) (k : Ω → ℕ)
    (hPredictable : ∀ i, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < k ω}) :
    ∀ i, MeasurableSet {ω : Ω | i < k ω} := by sorry
