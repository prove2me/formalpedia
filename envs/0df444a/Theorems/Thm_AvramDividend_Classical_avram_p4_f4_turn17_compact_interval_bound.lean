-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_compact_interval_bound
-- name    : AvramDividend.Classical.avram_p4_f4_turn17_compact_interval_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:21:01.195113+00:00
-- url     : https://prove2.me/theorems/b78140e3-a345-4a7f-ae85-bd72db216a99
-- title:
--   A continuous half-ray function is bounded above on [0,1]
-- statement:
--   Continuity on the initial compact interval provides a nonnegative finite upper bound, independently of any ODE.
-- source:
--   Source-exact mathematical reduction of f8c60858; independent positive ray, initial compact interval and global glue.

import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn17_compact_interval_bound
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ M := by sorry
