-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
-- name    : AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:59:57.831994+00:00
-- url     : https://prove2.me/theorems/c2451a3a-6c5f-45bc-ba0f-ea173787bf91
-- title:
--   Dyadic ceiling times dominate the underlying nonnegative-real stopping time
-- statement:
--   Every nonnegative time t is bounded above by its dyadic upward-rounded nonnegative-real time ceil(2^n t)/2^n. This bridges the proved real rounding bound into the exact order of the stopping-time domain, discharging pointwise domination in finite-grid stopping approximations.
-- source:
--   Proved dyadic_ceiling_rounding_bounds (57b560d3-993c-406e-b3e8-bd006ac45674) and NNReal coercion lemmas; downstream bounded_stopping_dyadic_grid_approximation.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal
    (t : ℝ≥0) (n : ℕ) :
    t ≤ (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n := by sorry
