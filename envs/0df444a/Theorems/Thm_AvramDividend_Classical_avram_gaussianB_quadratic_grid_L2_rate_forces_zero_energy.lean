-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_quadratic_grid_L2_rate_forces_zero_energy
-- name    : AvramDividend.Classical.avram_gaussianB_quadratic_grid_L2_rate_forces_zero_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:39:01.564692+00:00
-- url     : https://prove2.me/theorems/c63b75d3-fa7d-42e6-9d40-a47607b11496
-- title:
--   Original compensated Gaussian quadratic-grid L2 energy O(1/m) converges to zero
-- statement:
--   Any nonnegative original compensated Gaussian quadratic-grid second-moment energy a_m with a uniform upper bound K/(m+1) converges to zero. This converts the exact O(1/m) second-moment bound certified by gb28 into the limiting vanishing quadratic martingale channel required when assembling the original fixed-band G/H Gaussian physical-grid L2-Cauchy theorem.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
open Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_quadratic_grid_L2_rate_forces_zero_energy
    (K : ℝ) (hK : 0 ≤ K)
    (a : ℕ → ℝ)
    (hNonneg : ∀ m, 0 ≤ a m)
    (hRate : ∀ m, a m ≤ K / ((m + 1 : ℕ) : ℝ)) :
    Tendsto a atTop (𝓝 (0 : ℝ)) := by sorry
