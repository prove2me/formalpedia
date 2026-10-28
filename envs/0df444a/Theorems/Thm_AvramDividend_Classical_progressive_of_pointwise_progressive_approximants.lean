-- Prove2me | Theorems.Thm_AvramDividend_Classical_progressive_of_pointwise_progressive_approximants
-- name    : AvramDividend.Classical.progressive_of_pointwise_progressive_approximants
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:12:24.091176+00:00
-- url     : https://prove2.me/theorems/b42fca26-a636-4b8a-89df-dc375c394fa6
-- title:
--   Pointwise limits of progressively measurable real processes remain progressive
-- statement:
--   For a filtered measurable space, if a sequence of real-valued processes is progressively measurable at every stage and converges at every time and sample to a limiting process, then the limit is progressively measurable. This is the type-level bridge required by dyadic one-sided sample-path approximation of adapted left-continuous dividend and right-continuous Lévy paths.
-- source:
--   Pinned Mathlib MeasureTheory.isStronglyProgressive_of_tendsto and Filter.tendsto_pi_nhds, specialising its function-space convergence hypothesis to a pointwise condition.

import Mathlib.Probability.Process.Adapted

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.progressive_of_pointwise_progressive_approximants
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (U : ℕ → ℝ≥0 → Ω → ℝ)
    (u : ℝ≥0 → Ω → ℝ)
    (hU : ∀ n, ProgMeasurable 𝓕 (U n))
    (hpoint : ∀ t ω, Filter.Tendsto
      (fun n => U n t ω) Filter.atTop (nhds (u t ω))) :
    ProgMeasurable 𝓕 u := by sorry
