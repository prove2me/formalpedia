-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_actual_jumps_exclude_spurious_large_cells
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_finite_actual_jumps_exclude_spurious_large_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:43:49.057136+00:00
-- url     : https://prove2.me/theorems/4548174e-ca85-4ced-834b-651a345171fc
-- title:
--   All sufficiently fine persistent original large cells must meet an actual large jump
-- statement:
--   Assume that a finite set F captures every original càdlàg jump of magnitude ≥ρ in [0,T]. For any shrinking sequence of ordered mesh cells with increments all at least ρ, prove it is impossible that every half-open cell avoids F. The proof uses only the original-path pinpointed crossing-cell subsequence result and no compensator or jump-rate premise.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_finite_actual_jumps_exclude_spurious_large_cells
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
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
       ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (havoid : ∀ n, ∀ t ∈ F, ¬ (a n < t ∧ t ≤ b n))
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    False := by sorry
