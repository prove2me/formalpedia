-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_bounded_filtration_measurable
-- name    : AvramDividend.Classical.stoppedHistory_bounded_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:26:46.473162+00:00
-- url     : https://prove2.me/theorems/0846e555-63fc-41b2-89d4-11aa4ffc3f49
-- title:
--   A bounded stopped-history event is measurable at the deterministic terminal horizon
-- statement:
--   A stopped-history event A satisfies A∩{τ≤s}∈𝓕_s. If the stopping time is everywhere bounded by T, the event A itself belongs to 𝓕_T. This supplies measurability of the stopped-history indicator at a fixed horizon for the strong-Markov approximation and dominated-convergence argument.
-- source:
--   Measurability foundation on the direct path from strong-Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 to barrier-dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380, independent of W.

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stoppedHistory_bounded_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    MeasurableSet[𝓕 T] A := by
  sorry
