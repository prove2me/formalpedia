-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_horizon_uniform_original_physical_grid_certificate
-- name    : AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_uniform_original_physical_grid_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:58:13.611637+00:00
-- url     : https://prove2.me/theorems/4140ae57-116c-46c4-9d2e-a3addeded799
-- title:
--   Actual tenth-unit original physical grid has exact final strict clock, monotonicity, and uniform step equation
-- statement:
--   The explicit physical grid u(n,i)=(1/10)i/(n+2), coerced into nonnegative time, satisfies all three required original BV physical-mesh hypotheses simultaneously: starts at zero, ends at horizon minus mesh spacing, monotone within each row, and preserves exact real-time uniform equation. This permits fully source-exact application of original finitecap survivor/ruin BV cash and drift-grid theorems.
-- source:
--   Directly apply Proved avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock after showing its two elementary input clock equations, without altering the original physical-grid representation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock
open Classical AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_uniform_original_physical_grid_certificate :
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
    (∀ n, u n 0 = 0 ∧
      (u n (n + 1) : ℝ) =
        (1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)) ∧
    (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
    (∀ n i, (u n i : ℝ) = (1 / 10 : ℝ) *
      (i : ℝ) / ((n : ℝ) + 2)) := by sorry
