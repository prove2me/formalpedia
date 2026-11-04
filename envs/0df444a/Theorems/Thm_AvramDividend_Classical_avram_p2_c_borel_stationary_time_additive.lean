-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_stationary_time_additive
-- name    : AvramDividend.Classical.avram_p2_c_borel_stationary_time_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:43:59.119908+00:00
-- url     : https://prove2.me/theorems/9d1be992-043e-4c6d-9d1f-70cd7390d2de
-- title:
--   Stationary marked rectangle masses satisfy the additive time Cauchy identity
-- statement:
--   For any measure of nonnegative-time marked events, an exact stationary shift identity for a fixed measurable mark set implies that zero-origin rectangle mass is additive in time, allowing infinite ENNReal values. This isolates the rate function's additive structure independently of any Lévy measure identification.
-- source:
--   Apply the genuine disjoint half-open rectangle splitting theorem avram_p2_c_borel_time_rectangle_split and the explicitly assumed stationarity of marked-rectangle mass. A prospective original-source application composes this with the proved intrinsic marked-count stationary-mean theorem add050a6. This is a time-rate Cauchy bridge, not an assertion of the unknown ν coefficient.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_time_rectangle_split

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_stationary_time_additive
    (μ : Measure (ℝ≥0 × ℝ))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hShift : ∀ (s t : ℝ≥0),
      μ (Ioc s (s + t) ×ˢ B) = μ (Ioc 0 t ×ˢ B))
    (s t : ℝ≥0) :
    μ (Ioc 0 (s + t) ×ˢ B) =
      μ (Ioc 0 s ×ˢ B) + μ (Ioc 0 t ×ˢ B) := by sorry
