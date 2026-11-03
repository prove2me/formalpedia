-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
-- name    : AvramDividend.Classical.avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:24:35.970036+00:00
-- url     : https://prove2.me/theorems/572b8d66-e344-43ac-97dc-13a1e0fdb4fe
-- title:
--   Clipping a nonnegative source time cell at a stopping horizon preserves mesh width upper bounds
-- statement:
--   On the exact original nonnegative time grid, clipping both endpoints of an increasing cell at any fixed stopping horizon can only reduce its real mesh increment. This supplies the missing deterministic source-grid-to-stopped-grid clock-width transport for Chat06 and is independent of controlled Itô–Meyer or specialist stochastic cores.
-- source:
--   Avram Proposition 4(i) stopped finite-grid localisation, chronological mesh control

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
    (u : ℕ → ℝ≥0) (hu : Monotone u) (i : ℕ) (τ : ℝ≥0)
    (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m) :
    ((min (u (i + 1)) τ : ℝ) - (min (u i) τ : ℝ)) ≤ m := by sorry
