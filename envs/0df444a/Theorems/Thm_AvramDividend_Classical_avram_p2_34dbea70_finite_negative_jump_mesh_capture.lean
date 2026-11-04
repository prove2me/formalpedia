-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_negative_jump_mesh_capture
-- name    : AvramDividend.Classical.avram_p2_34dbea70_finite_negative_jump_mesh_capture
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:50:43.418082+00:00
-- url     : https://prove2.me/theorems/fdc7e12d-7369-46a3-b02c-f2b6fc0a2345
-- title:
--   Every finite collection of genuine negative jumps is eventually counted by distinct mesh cells
-- statement:
--   For any right-continuous real-valued source path with genuine strict left limits at a finite selection of negative jumps of size at least epsilon, choose straddling left and right cell endpoints converging from the appropriate sides. Assume the cells come from the actual finite right-endpoint mesh and have its genuine left predecessor. Then for all sufficiently fine meshes the selected jump count is at most the number of cells whose path increments are less than minus epsilon over two. This is a deterministic finite-set counting inequality, with no Lévy rate, compensator, Poisson proxy, or finite-activity assumption. The proof combines the existing source jump-cell detection theorem with finite-label endpoint injectivity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_straddling_cell_detects_negative_jump
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective

open Set Filter Topology AvramDividend.Classical
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_34dbea70_finite_negative_jump_mesh_capture
    (Y : ℝ≥0 → ℝ) (F : Finset ℝ≥0)
    (a b : ℝ≥0 → ℕ → ℝ≥0)
    (E : ℕ → Finset ℝ≥0) (left : ℕ → ℝ≥0 → ℝ≥0)
    (ε : ℝ) (hε : 0 < ε)
    (ha : ∀ u ∈ F, Tendsto (a u) atTop (𝓝[<] u))
    (hb : ∀ u ∈ F, Tendsto (b u) atTop (nhdsWithin u (Ici u)))
    (hL : ∀ u ∈ F, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ F, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ F, Y u - Function.leftLim Y u ≤ -ε)
    (hIn : ∀ u ∈ F, ∀ n, b u n ∈ E n)
    (hLeft : ∀ u ∈ F, ∀ n, left n (b u n) = a u n) :
    ∀ᶠ n : ℕ in atTop,
      F.card ≤ ((E n).filter
        (fun t : ℝ≥0 => Y t - Y (left n t) < -ε / 2)).card := by sorry
