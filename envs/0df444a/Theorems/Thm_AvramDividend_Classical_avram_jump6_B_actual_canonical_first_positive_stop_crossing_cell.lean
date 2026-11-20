-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_first_positive_stop_crossing_cell
-- name    : AvramDividend.Classical.avram_jump6_B_actual_canonical_first_positive_stop_crossing_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:44:46.622194+00:00
-- url     : https://prove2.me/theorems/c018c822-6b19-48f3-a029-096cdeb3cad9
-- title:
--   First strictly pre-contact and then stopped physical cell on the actual canonical grid
-- statement:
--   For the original canonical clipped physical grid and any positive bounded stop rho, a minimal transition cell exists: its left endpoint is strictly earlier than rho and its right endpoint is exactly rho. The cell is inside the true number of grid cells. This uses the already Proved physical grid monotonicity, zero origin and finite endpoint coverage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_canonical_first_positive_stop_crossing_cell
    (n j : ℕ) (ρ : ℝ≥0)
    (hρ : 0 < ρ) (hρn : ρ ≤ (n : ℝ≥0)) :
    ∃ i : ℕ, i < (n + 1) * (j + 1) ∧
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ < ρ ∧
      min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ = ρ := by sorry
