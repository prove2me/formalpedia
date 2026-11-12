-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger95_zero_atom_interior_final_cash_partition
-- name    : AvramDividend.Classical.avram_gledger95_zero_atom_interior_final_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:36:34.26153+00:00
-- url     : https://prove2.me/theorems/ee6f0012-c22e-45ab-80b4-da3e2d15f2d2
-- title:
--   A first-crossing grid partitions strict stopped cash into time zero, interior cells, and the last open cell
-- statement:
--   For any measurable nonnegative-time payment set S, a monotone grid starting at zero and having a first crossing cell ending at rho partitions the strict stopped cash integral exactly into the atom at time zero, the non-overlapping preceding half-open cells, and the open final crossing strip. This prevents counting one dividend payment more than once and avoids including the ruin/horizon payment.
-- source:
--   Strictly smaller set and measure identity for gledger81, building on Proved gledger90. Handles the original time-zero dividend atom and final strict cash separately, with no stochastic claim.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger90_masked_monotone_grid_Ioc_cash_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger95_zero_atom_interior_final_cash_partition
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ) =
      (∫⁻ s in S ∩ {0}, f s ∂μ) +
      (∑ i ∈ Finset.range k,
        ∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) +
      (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ) := by sorry
