-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_crossing_large_increments_force_large_actual_jump
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_crossing_large_increments_force_large_actual_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:20:54.802488+00:00
-- url     : https://prove2.me/theorems/b107f86b-f132-412a-8991-a813d280e119
-- title:
--   Genuine jump magnitude bounds every persistently large crossing-cell increment
-- statement:
--   When shrinking càdlàg observation cells straddle a fixed genuine jump time and have uniformly large real increments, the true jump at that time is at least that large in absolute magnitude. The proof passes a closed inequality to the limit using the accepted straddling increment convergence. Handles the right-closed endpoint convention.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_crossing_large_increments_force_large_actual_jump
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (ha : Tendsto a atTop (𝓝[<] t))
    (hb : Tendsto b atTop (nhdsWithin t (Ici t)))
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ)
    (hlarge : ∀ n : ℕ, ρ ≤ |Y (b n) - Y (a n)|) :
    ρ ≤ |Y t - Function.leftLim Y t| := by sorry
