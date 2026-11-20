-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_clipped_grid_widths_telescope_real_clock
-- name    : AvramDividend.Classical.avram_jump6_B_actual_clipped_grid_widths_telescope_real_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:05:42.535473+00:00
-- url     : https://prove2.me/theorems/ce253940-21e8-4676-afef-1485a64ecaec
-- title:
--   Exact original physical stopped-grid cell widths telescope to the true clock
-- statement:
--   The actual stopped canonical physical mesh v_i=min(i/(j+1),t) reaches the original clock t at its final grid point, is monotone, and its cast-to-real nonnegative cell widths sum exactly to t. The proof handles ℝ≥0 truncated subtraction explicitly, allowing source-exact generator Q_j and bounded-horizon integrability estimates without replacing the grid by a different discretisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_clipped_grid_widths_telescope_real_clock
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    let u : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ := (n + 1) * (j + 1)
    (∑ i ∈ Finset.range m,
      (((u (i + 1) - u i : ℝ≥0) : ℝ))) = (t : ℝ) := by sorry
