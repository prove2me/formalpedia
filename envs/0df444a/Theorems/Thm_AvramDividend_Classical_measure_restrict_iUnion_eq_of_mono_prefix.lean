-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_restrict_iUnion_eq_of_mono_prefix
-- name    : AvramDividend.Classical.measure_restrict_iUnion_eq_of_mono_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:13:19.880803+00:00
-- url     : https://prove2.me/theorems/da107ff6-d702-44d0-b6a5-e7897d043615
-- title:
--   Agreement of measures on increasing restrictions extends to their union
-- statement:
--   If two Borel measures agree after restriction to every member of an increasing sequence of measurable or arbitrary sets, they agree when restricted to the union. The proof is a direct application of the directed restriction monotone-convergence formula for measures and does not require global finiteness.
-- source:
--   Pinned Mathlib 0df444a, MeasureTheory.Measure.restrict_iUnion_apply_eq_iSup, foundational restriction continuity used for the strict-ruin dividend support.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set

theorem AvramDividend.Classical.measure_restrict_iUnion_eq_of_mono_prefix
    (μ ν : Measure ℝ) (s : ℕ → Set ℝ)
    (hmono : Monotone s)
    (heq : ∀ n, μ.restrict (s n) = ν.restrict (s n)) :
    μ.restrict (⋃ n, s n) = ν.restrict (⋃ n, s n) := by sorry
