-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger114_finite_real_grid_mass_le_strict_stop
-- name    : AvramDividend.Classical.avram_gledger114_finite_real_grid_mass_le_strict_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:02:50.404663+00:00
-- url     : https://prove2.me/theorems/c0801955-7b10-4489-8e24-031179e18ee3
-- title:
--   Finite real dividend mass over complete cells is bounded by strict pre-stop mass
-- statement:
--   For a monotone clipped time grid, the finite real-valued dividend measures of complete half-open cells sum to no more than the finite measure of the strict pre-stop interval. The ENNReal-to-real conversion preserves the finite sum, allowing use of the original cash budget gledger106.
-- source:
--   Original gledger81 interior mass budget: converts gledger111 ENNReal partition into finite real dividend masses with strict-stopping-time endpoint, before multiplication by mesh width.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger111_monotone_grid_Ioc_cash_le_strict_stop
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger114_finite_real_grid_mass_le_strict_stop
    (μ : Measure ℝ) (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hfinite : μ (Ioo (0 : ℝ) ρ) ≠ ⊤) :
    (∑ i ∈ Finset.range k, (μ (Ioc (v i) (v (i + 1)))).toReal) ≤
      (μ (Ioo (0 : ℝ) ρ)).toReal := by sorry
