-- Prove2me | solution 1 for e7_integrable_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:03:55.134902+00:00
-- url     : https://prove2.me/submissions/9f82d374-f01a-4f20-8437-1daccee9cb73

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (F : α → ℝ) (hF : Measurable F) (M : ℝ)
    (hbound : ∀ x, ‖F x‖ ≤ M) : Integrable F ν :=
  MeasureTheory.Integrable.of_bound hF.aestronglyMeasurable M (Filter.Eventually.of_forall hbound)
