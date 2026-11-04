-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_index_indicator_liminf
-- name    : AvramDividend.Classical.avram_p2_34dbea70_all_negative_path_jumps_le_index_indicator_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:50:06.998053+00:00
-- url     : https://prove2.me/theorems/7d78562b-167a-4c1a-9428-3040159ff048
-- title:
--   All actual negative path jumps bounded by original ENat indexed-cell indicator liminf
-- statement:
--   For any real path on NNReal time and set S of negative jumps satisfying explicit time/left-limit/right-continuity/jump-size hypotheses, the full extended-natural jump count is at most the liminf of original adjacent indexed uniform-grid ENat indicator sums. This combines two accepted finite/pathwise inequalities and imposes no rate, finite-activity or compensator assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_uniform_grid_image_le_enat_indicator_count

open Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_all_negative_path_jumps_le_index_indicator_liminf
    (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε) :
    S.encard ≤ Filter.liminf (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℕ∞) else 0)) atTop := by sorry
