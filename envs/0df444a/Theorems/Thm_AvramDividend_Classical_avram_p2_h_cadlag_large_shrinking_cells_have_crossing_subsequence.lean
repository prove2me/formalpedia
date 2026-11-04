-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_large_shrinking_cells_have_crossing_subsequence
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_large_shrinking_cells_have_crossing_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:37:54.857832+00:00
-- url     : https://prove2.me/theorems/54fd66e2-d67d-41d4-8896-d7e44295c24a
-- title:
--   Large shrinking cells admit a cofinal right-closed jump-containing subsequence
-- statement:
--   Given càdlàg path limits at a common time, any ordered shrinking intervals with uniformly large increments admit a cofinal subsequence each satisfying left<t≤right, and the time's actual jump is at least that large. This strengthens numerical jump detection by preserving exact right-closed cell localisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_ordered_cells_three_case_cofinal_subsequence
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_same_side_large_increments_impossible
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_crossing_large_increments_force_large_actual_jump

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_large_shrinking_cells_have_crossing_subsequence
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ n, a n ≤ b n)
    (ha : Tendsto a atTop (𝓝 t))
    (hb : Tendsto b atTop (𝓝 t))
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    ∃ φ : ℕ → ℕ,
      Tendsto φ atTop (atTop : Filter ℕ) ∧
      (∀ n, a (φ n) < t ∧ t ≤ b (φ n)) ∧
      ρ ≤ |Y t - Function.leftLim Y t| := by sorry
