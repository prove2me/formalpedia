-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite70_nonnegative_cap_fraction_monotone
-- name    : AvramDividend.Classical.avram_gfinite70_nonnegative_cap_fraction_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:13:45.169505+00:00
-- url     : https://prove2.me/theorems/c830b445-bd0d-4929-9536-b1c4b70b7719
-- title:
--   Finite-cap rational interior cutoffs are monotone
-- statement:
--   For a nonnegative real cap, the finite-cap fractions c(j+1)/(j+2) increase monotonically with j. This supplies the scalar monotonicity required to apply finite-measure strip continuity without requiring differentiability of a reward at the cap.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite70_nonnegative_cap_fraction_monotone
    (c : ℝ) (hc : 0 ≤ c) :
    Monotone (fun j : ℕ => c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))) := by
  sorry
