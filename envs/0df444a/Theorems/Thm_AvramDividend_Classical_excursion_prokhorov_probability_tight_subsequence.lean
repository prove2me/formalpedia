-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_prokhorov_probability_tight_subsequence
-- name    : AvramDividend.Classical.excursion_prokhorov_probability_tight_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:51:49.254359+00:00
-- url     : https://prove2.me/theorems/6ab32bd9-9b53-4c6f-b835-ec74069f35c1
-- title:
--   Prokhorov convergent subsequence for tight real probability measures
-- statement:
--   A sequence of real probability measures whose underlying measures form a tight family has a strictly increasing-index subsequence converging weakly to a probability measure. This is Prokhorov compactness followed by sequential compactness.
-- source:
--   Mathlib pinned Prokhorov compact-closure theorem and compact-subsequence lemma; support for the excursion Laplace weak-limit existence proof.

import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Filter Topology Set

theorem AvramDividend.Classical.excursion_prokhorov_probability_tight_subsequence
    (ν : ℕ → ProbabilityMeasure ℝ)
    (htight : IsTightMeasureSet
      {x : Measure ℝ | ∃ μ ∈ Set.range ν, (μ : Measure ℝ) = x}) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) := by sorry
