-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_same_side_large_increments_impossible
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_same_side_large_increments_impossible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:20:57.659331+00:00
-- url     : https://prove2.me/theorems/24bc3573-7c24-4f1c-bf83-64c17ae9843e
-- title:
--   A positive persistent increment bound excludes both same-side shrinking cases
-- statement:
--   When shrinking observation endpoints converge to a common time from the same left or right side, their increment tends to zero. Therefore their increment magnitude cannot stay above a fixed positive threshold. This supplies the two non-crossing contradictions for the uniform no-spurious-mesh argument, independently of any stochastic rate.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_same_side_shrinking_increments_zero

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_same_side_large_increments_impossible
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n : ℕ, ρ ≤ |Y (b n) - Y (a n)|)
    (hsides :
      (Tendsto a atTop (𝓝[<] t) ∧ Tendsto b atTop (𝓝[<] t)) ∨
      (Tendsto a atTop (nhdsWithin t (Ici t)) ∧
        Tendsto b atTop (nhdsWithin t (Ici t)))) :
    False := by sorry
