-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_uniform_nnreal_real_mesh_identification
-- name    : AvramDividend.Classical.avram_p2_j_ui_uniform_nnreal_real_mesh_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:40:53.589282+00:00
-- url     : https://prove2.me/theorems/0ac2aa61-3fa4-4f04-84ec-b6b095baac51
-- title:
--   Exact agreement of real-to-NNReal and NNReal uniform (n+1)-cell mesh widths
-- statement:
--   For every nonnegative horizon T and natural n, converting the real uniform width T/(n+1) to NNReal agrees exactly with the uniform NNReal division T/((n:NNReal)+1). This source-independent arithmetic identity aligns the already-Proved P2-J expectation uniform-grid theorem with P2-H's deterministic NNReal grid-to-jump theorem without assuming the latter is Proved.

import Mathlib.Data.NNReal.Defs
import Mathlib

open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_j_ui_uniform_nnreal_real_mesh_identification
    (T : ℝ≥0) (n : ℕ) :
    Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / ((n : ℝ≥0) + 1) := by sorry
