-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_time_rectangle_split
-- name    : AvramDividend.Classical.avram_p2_c_borel_time_rectangle_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:48:40.134146+00:00
-- url     : https://prove2.me/theorems/781cf9ae-636e-4e3f-9ed8-73bc5d6c77c8
-- title:
--   Exact finite or infinite measure additivity across adjacent marked time rectangles
-- statement:
--   For every measure on nonnegative time and real marks, its mass on (s,u] × B is the sum of the masses on adjacent disjoint time rectangles (s,t] × B and (t,u] × B. This is an exact pathwise measure identity with no stochastic rate assumption.
-- source:
--   Formal disjoint decomposition of measurable half-open intervals and MeasureTheory.measure_union; supports original intrinsic jump count time additivity and later expectation rate Cauchy arguments.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_time_rectangle_split
    (μ : Measure (ℝ≥0 × ℝ))
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    μ (Ioc s u ×ˢ B) =
      μ (Ioc s t ×ˢ B) + μ (Ioc t u ×ˢ B) := by sorry
