-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
-- name    : AvramDividend.Classical.avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:03:21.816989+00:00
-- url     : https://prove2.me/theorems/da8556b4-347e-47d5-9bbf-9b0b87454251
-- title:
--   Uniform dyadic ceilings scaled to a fixed finite horizon stay inside the horizon and converge from above
-- statement:
--   For every positive finite horizon T and time s in [0,T], define its right-approximating grid point as T times the upward dyadic rounding of s/T to mesh 2⁻ⁿ. At every resolution n the grid point lies between s and T inclusive, so it is one of the finite equal-mesh observations of the same horizon. The sequence converges to s as n tends to infinity. This geometric lemma packages precisely the nonnegative-time boundary and right-approach facts needed to pass finite-mesh Lévy drawdown/minimum laws to genuine fixed-time càdlàg extrema; it assumes no stochastic law.
-- source:
--   Exact elementary dyadic rounding and density on a finite horizon, built from already Proved AvramDividend.Classical.dyadic_ceiling_rounding_bounds, dyadic_ceiling_index_mem_finite_grid, and dyadic_ceiling_nnreal_tendsto, Mathlib 0df444a.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
open Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
    (s T : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) :
    let u : ℕ → ℝ≥0 := fun n =>
      (Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n * T
    (∀ n, s ≤ u n ∧ u n ≤ T) ∧ Filter.Tendsto u Filter.atTop (nhds s) := by sorry
