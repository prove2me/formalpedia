-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:41:50.384081+00:00
-- url     : https://prove2.me/theorems/580da8bb-a167-4363-b67a-22d9774cac2a
-- title:
--   Persistent large original mesh cells isolate an actual original jump in an infinite subsequence
-- statement:
--   For a genuine original càdlàg path on bounded horizon T, shrinking ordered mesh cell endpoints and positive increment threshold ρ, show any sequence whose increments remain ≥ρ has an original jump of size ≥ρ inside every cell of some cofinal subsequence. Use proved P2-A compactness and P2-H side classification. Assume no Lévy rate or compensator.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b w : ℕ → ℝ≥0)
    (haT : ∀ n, a n ≤ T)
    (hab : ∀ n, a n ≤ b n)
    (hbw : ∀ n, b n ≤ a n + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    ∃ t : ℝ≥0, t ∈ Icc (0 : ℝ≥0) T ∧
      ρ ≤ |Y t - Function.leftLim Y t| ∧
      ∃ φ : ℕ → ℕ, Tendsto φ atTop (atTop : Filter ℕ) ∧
        (∀ n, a (φ n) < t ∧ t ≤ b (φ n)) := by sorry
