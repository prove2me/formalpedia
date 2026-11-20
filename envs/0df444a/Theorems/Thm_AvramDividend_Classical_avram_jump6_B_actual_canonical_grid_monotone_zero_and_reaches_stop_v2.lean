-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
-- name    : AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:06:48.782173+00:00
-- url     : https://prove2.me/theorems/b3b7e5c3-1121-4aa7-a81a-6f447922e3df
-- title:
--   Exact original canonical integer grid is monotone and exhausts bounded stopped clock
-- statement:
--   For the exact original Avram physical grid, with m=(n+1)(j+1) and u(i)=min(i/(j+1),t), 0≤t≤n implies u monotone, u(0)=0 and u(m)=t. This is source-specific time-grid coverage required to split the last ruin-contact cell. It is independent of the stochastic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    let u : ℕ → ℝ≥0 :=
      fun i => min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ := (n + 1) * (j + 1)
    Monotone u ∧ u 0 = 0 ∧ u m = t := by sorry
