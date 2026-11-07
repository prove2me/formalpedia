-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
-- name    : AvramDividend.Classical.avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:30:33.354792+00:00
-- url     : https://prove2.me/theorems/0071cc00-bca0-46c3-b374-2a8ad01a4133
-- title:
--   Strict original physical grid approaches the horizon with positive mesh gap
-- statement:
--   For the exact positive horizon and uniform n+2 original BV physical grid, the omitted final gap is strictly positive for every n, so each last grid point is genuinely inside the strict Iio T horizon; the omitted gap vanishes and the last point tends to T. This supplies the temporal cofinality component required for strict cash source convergence without introducing horizon right-payment atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
    (T : ℝ) (hT : 0 < T) :
    (∀ n : ℕ, 0 < T / ((n : ℝ) + 2) ∧
      T - T / ((n : ℝ) + 2) < T) ∧
    Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2))
      atTop (𝓝 T) := by sorry
