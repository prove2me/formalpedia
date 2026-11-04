-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_mesh_quotient
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_real_nnreal_mesh_quotient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:43:36.663078+00:00
-- url     : https://prove2.me/theorems/f64a073e-7e17-4bea-9869-f8bd51dcdef2
-- title:
--   Exact positive uniform real mesh to NNReal quotient bridge
-- statement:
--   For each finite nonnegative horizon T and every uniform natural grid index n, the nonnegative time obtained by Real.toNNReal of the positive real width (T:Real)/(n+1) equals T divided in NNReal by the nonnegative embedding of the real denominator. This is the exact coercion step required to transport the original source O(h) bound from real h to NNReal time.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_real_nnreal_mesh_quotient
    (T : ℝ≥0) (n : ℕ) :
    Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / Real.toNNReal ((n : ℝ) + 1) := by sorry
