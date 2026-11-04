-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_positive_plus_one_mesh_horizon
-- name    : AvramDividend.Classical.avram_p2_j_ui_positive_plus_one_mesh_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:48:34.660443+00:00
-- url     : https://prove2.me/theorems/371702c6-3326-4f6f-b55c-1e9659642a1e
-- title:
--   Uniform n+1 interval positive mesh converges to zero and fills the horizon
-- statement:
--   For every positive real horizon T, the explicit uniform mesh width h_n=T/(n+1) tends to zero in the positive one-sided neighbourhood filter and (n+1)h_n=T exactly. This discharges the technical mesh and horizon hypotheses in the original-process conditional P2-J expectation theorem, matching the P2-H pathwise indexing convention.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.NhdsWithin

open Filter Set Topology
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_positive_plus_one_mesh_horizon
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop
      (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
    (∀ n : ℕ, (((n + 1 : ℕ) : ℝ) *
      (T / ((n : ℝ) + 1))) = T) := by sorry
