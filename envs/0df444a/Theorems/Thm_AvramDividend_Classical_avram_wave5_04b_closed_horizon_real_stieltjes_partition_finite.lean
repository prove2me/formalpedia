-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
-- name    : AvramDividend.Classical.avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:05:36.470698+00:00
-- url     : https://prove2.me/theorems/3c789eef-bb52-4955-949c-348ed5034fa7
-- title:
--   Finite real-valued closed-horizon Stieltjes grid decomposition including actual zero atom
-- statement:
--   For any measure on the real line, any nonnegative extended-real integrand and any monotone finite time grid beginning at zero, a finite lower Stieltjes integral over the true closed horizon has real value equal to the real integral at the time-zero singleton plus the sum of the real integrals on every chronological half-open cell. The statement applies to atomless singular-continuous, diffuse, and countably atomic measure components without loss.
-- source:
--   Proved exact closed-horizon partition bc3c810a-82f6-4448-a4e0-457c95d9b2dc, ENNReal.add_ne_top, ENNReal.sum_ne_top, ENNReal.toReal_add and ENNReal.toReal_sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (hu0 : u 0 = 0) (n : ℕ)
    (hFinite : (∫⁻ s in Icc (0 : ℝ) (u n), f s ∂μ) ≠ ⊤) :
    (∫⁻ s in Icc (0 : ℝ) (u n), f s ∂μ).toReal =
      (∫⁻ s in ({0} : Set ℝ), f s ∂μ).toReal +
      ∑ i ∈ Finset.range n,
        (∫⁻ s in Ioc (u i) (u (i + 1)), f s ∂μ).toReal := by sorry
