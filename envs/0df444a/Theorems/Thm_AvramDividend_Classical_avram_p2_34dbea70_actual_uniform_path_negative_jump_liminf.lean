-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:50:22.595117+00:00
-- url     : https://prove2.me/theorems/80a6a455-62e3-4169-bd07-6f968e792c2e
-- title:
--   All actual negative path jumps on a horizon are bounded by uniform mesh negative cells
-- statement:
--   For any cadlag real path and its actual negative jumps on the time interval (0,T], the full extended count of jumps of magnitude at least epsilon is at most the limit inferior of negative uniform-mesh cell counts with threshold epsilon/2. Uses the proved original half-open grid locator, genuinely shrinking sided endpoints and finite-jump-to-all-jump count bridge. The theorem is exact for the supplied path and permits infinite jump activity, without any Lévy-rate identification or compensator assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_jump_mesh_liminf

open Set Filter Topology AvramDividend.Classical
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
    (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε) :
    S.encard ≤ Filter.liminf (fun n : ℕ =>
      ((((Finset.range (n + 1)).image
        (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
        (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℕ∞))
      atTop := by sorry
