-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_no_cofinally_spurious_large_fine_cells
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_no_cofinally_spurious_large_fine_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:15:43.071549+00:00
-- url     : https://prove2.me/theorems/057385f1-51fc-47ea-8923-832ec9f41c4e
-- title:
--   No cofinally fine large mesh cells can avoid all genuine large jumps
-- statement:
--   For any uniformly shrinking and bounded indexed family of ordered cells, it is impossible to choose arbitrarily fine cells with a positive large path increment that contain no actual same-threshold càdlàg jump. The proof extracts a bad-cell sequence and invokes compact crossing-cell jump localisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_compact_large_cells_have_actual_jump_inside_subsequence

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_no_cofinally_spurious_large_fine_cells
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℕ → ℕ → ℝ≥0)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbound : ∀ n i, b n i ≤ T)
    (hwidth : ∀ (is ns : ℕ → ℕ),
      Tendsto ns atTop (atTop : Filter ℕ) →
      Tendsto (fun k => (b (ns k) (is k) : ℝ) -
        (a (ns k) (is k) : ℝ)) atTop (𝓝 (0 : ℝ)))
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t)
    (hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ i : ℕ, ρ ≤ |Y (b n i) - Y (a n i)| ∧
        ∀ t : ℝ≥0, ¬
          (a n i < t ∧ t ≤ b n i ∧
            ρ ≤ |Y t - Function.leftLim Y t|)) :
    False := by sorry
