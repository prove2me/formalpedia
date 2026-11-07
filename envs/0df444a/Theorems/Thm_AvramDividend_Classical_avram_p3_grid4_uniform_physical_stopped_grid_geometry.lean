-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uniform_physical_stopped_grid_geometry
-- name    : AvramDividend.Classical.avram_p3_grid4_uniform_physical_stopped_grid_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:29:08.820505+00:00
-- url     : https://prove2.me/theorems/3ca54011-8d14-449e-8147-4a04db7a4a13
-- title:
--   Uniform physical stopped-grid geometry for the original BV dividend process
-- statement:
--   For the exact positive physical horizon T and delta_n = T/(n+2), construct nonnegative grid times u(n,i) = T*i/(n+2), starting at time zero, ending at T-delta_n for i=n+1 and increasing along the entire finite row. This discharges precisely the first two conjuncts of the original physical stopped-cell error witness, independently of the original process and its compensated-jump estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_uniform_physical_stopped_grid_geometry (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) := by sorry
