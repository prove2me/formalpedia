-- Prove2me | Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
-- name    : AvramDividend.Classical.dense_timeSup_with_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T23:18:09.690052+00:00
-- url     : https://prove2.me/theorems/4cdf4ed6-71c6-4948-849b-8bfefa587f36
-- title:
--   Right continuous running supremum equals dense-sample supremum plus current endpoint
-- statement:
--   For a right-continuous real path over nonnegative time, a dense subset S containing zero and a bounded above path image over [0,t], the inclusive supremum on [0,t] equals the maximum of the supremum sampled at times in S up to t and the current endpoint f(t). For u<t, values are limits of values at sample points strictly between u and t. At u=t, the endpoint term handles its value directly. No assumption on left limits or absence of positive jumps is required.
-- source:
--   General analytic endpoint-inclusive simplification for the Prove2Me Avram Dividend mission. Avoids the no-positive-jump endpoint case in the earlier dense representation plan and feeds the conditional endpoint-adaptedness bridge.

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dense_timeSup_with_endpoint (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (S : Set ℝ≥0) (hS : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0)
    (hb : BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) =
      max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, f s.1) (f t) := by
  sorry
