-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_compact_large_cells_have_actual_jump_inside_subsequence
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_compact_large_cells_have_actual_jump_inside_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:06:44.814115+00:00
-- url     : https://prove2.me/theorems/2229c075-abf3-4ae6-a3b6-0254fa9b0123
-- title:
--   Compactness produces a jump actually inside a cofinal sequence of large cells
-- statement:
--   Every finite-horizon sequence of ordered cells of vanishing real width with uniformly large path increments contains, along a cofinal subsequence, one common actual large càdlàg jump inside each right-closed cell.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_bounded_endpoint_has_convergent_subsequence
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_left_endpoint_limit_of_vanishing_real_mesh_width
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_large_shrinking_cells_have_crossing_subsequence

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_compact_large_cells_have_actual_jump_inside_subsequence
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (hab : ∀ n, a n ≤ b n)
    (hbound : ∀ n, b n ≤ T)
    (hgap : Tendsto (fun n => (b n : ℝ) - (a n : ℝ))
      atTop (𝓝 (0 : ℝ)))
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|)
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∃ t : ℝ≥0, t ≤ T ∧
      ∃ ψ : ℕ → ℕ,
        Tendsto ψ atTop (atTop : Filter ℕ) ∧
        (∀ n, a (ψ n) < t ∧ t ≤ b (ψ n)) ∧
        ρ ≤ |Y t - Function.leftLim Y t| := by sorry
