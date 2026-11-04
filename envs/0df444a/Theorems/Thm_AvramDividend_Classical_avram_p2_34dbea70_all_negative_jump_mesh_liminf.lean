-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_jump_mesh_liminf
-- name    : AvramDividend.Classical.avram_p2_34dbea70_all_negative_jump_mesh_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:17:53.566472+00:00
-- url     : https://prove2.me/theorems/7c87cc5c-a3a1-4a1c-b018-48c01b94a98d
-- title:
--   All negative jumps are bounded by the liminf of genuine mesh negative-cell counts
-- statement:
--   The total extended count of actual negative jumps of a cadlag path is bounded by the limit inferior of negative increments on its finite approximating meshes. Every jump has genuinely convergent straddling endpoints and belongs to its own mesh cell. The proof quantifies over arbitrary finite selections, uses already source-verified jump capture and injectivity, then upgrades to full cardinality without a finite-activity assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_negative_jump_mesh_capture
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_subsets_liminf_encard

open Set Filter Topology AvramDividend.Classical
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_34dbea70_all_negative_jump_mesh_liminf
    (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (a b : ℝ≥0 → ℕ → ℝ≥0)
    (E : ℕ → Finset ℝ≥0) (left : ℕ → ℝ≥0 → ℝ≥0)
    (ε : ℝ) (hε : 0 < ε)
    (ha : ∀ u ∈ S, Tendsto (a u) atTop (𝓝[<] u))
    (hb : ∀ u ∈ S, Tendsto (b u) atTop (nhdsWithin u (Ici u)))
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε)
    (hIn : ∀ u ∈ S, ∀ n, b u n ∈ E n)
    (hLeft : ∀ u ∈ S, ∀ n, left n (b u n) = a u n) :
    S.encard ≤ Filter.liminf (fun n : ℕ =>
      (((E n).filter (fun t : ℝ≥0 =>
        Y t - Y (left n t) < -ε / 2)).card : ℕ∞)) atTop := by sorry
