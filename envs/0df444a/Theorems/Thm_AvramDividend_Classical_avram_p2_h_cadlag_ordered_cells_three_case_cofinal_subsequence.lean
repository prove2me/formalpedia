-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_ordered_cells_three_case_cofinal_subsequence
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_ordered_cells_three_case_cofinal_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:24:48.887126+00:00
-- url     : https://prove2.me/theorems/312d1cf5-8201-4f87-81c6-a6c013ebecbc
-- title:
--   Extract a cofinal shrinking-cell subsequence with a fixed positional side
-- statement:
--   If endpoints a_n≤b_n both converge to a time t, a cofinal subsequence exists on which every interval lies left of t, every interval lies right of t, or every interval straddles t according to the exact right-closed convention. Both endpoint convergence statements survive the subsequence. This is the rigorous three-way compactness branch needed to eliminate spurious jump-like mesh increments.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_ordered_cells_three_case_frequently

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_ordered_cells_three_case_cofinal_subsequence
    (a b : ℕ → ℝ≥0) (t : ℝ≥0)
    (hab : ∀ n, a n ≤ b n)
    (ha : Tendsto a atTop (𝓝 t))
    (hb : Tendsto b atTop (𝓝 t)) :
    ∃ φ : ℕ → ℕ,
      Tendsto φ atTop (atTop : Filter ℕ) ∧
      Tendsto (a ∘ φ) atTop (𝓝 t) ∧
      Tendsto (b ∘ φ) atTop (𝓝 t) ∧
      ((∀ n, b (φ n) < t) ∨
       (∀ n, t ≤ a (φ n)) ∨
       (∀ n, a (φ n) < t ∧ t ≤ b (φ n))) := by sorry
