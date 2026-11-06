-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_exact_cell_length
-- name    : AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_exact_cell_length
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:54:46.569306+00:00
-- url     : https://prove2.me/theorems/6f6c5b7d-8fa4-4129-81d8-57c30ad8f188
-- title:
--   Exact uniform physical BV grid cell length before final horizon
-- statement:
--   For the deterministic physical mesh u(j)=min(j,m+1)*T/(m+1), the truncated NNReal difference of consecutive times equals T/(m+1) on every actual cell i<m+1. Together with the accepted endpoint/monotonicity geometry this supports stopped source C1 mesh-smallness arguments using the original reserve process, without changing the Lévy source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_exact_cell_length
    (T : ℝ≥0) (m i : ℕ) (hi : i < m + 1) :
    let u : ℕ → ℝ≥0 := fun j =>
      ((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
    u (i + 1) - u i = T / (m + 1) := by sorry
