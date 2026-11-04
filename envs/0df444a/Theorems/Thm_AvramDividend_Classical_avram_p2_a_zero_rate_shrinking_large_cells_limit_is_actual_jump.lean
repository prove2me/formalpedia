-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_shrinking_large_cells_limit_is_actual_jump
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_shrinking_large_cells_limit_is_actual_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:41:59.289836+00:00
-- url     : https://prove2.me/theorems/577cad4e-026d-4299-846f-85ae781101e5
-- title:
--   Persistent original càdlàg shrinking-cell increments force a genuine jump at the limiting time
-- statement:
--   Suppose original càdlàg path Y has left and right limits at t, a_n≤b_n and both endpoints converge to t. If ρ>0 and every observed cell increment has magnitude at least ρ, prove the actual jump magnitude |Y(t)-Y(t-)| is at least ρ. Use proved original-source deterministic P2-H three-side extraction, same-side contradiction and crossing bound; assume no jump count, rate or compensator.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_shrinking_large_cells_limit_is_actual_jump
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ n, a n ≤ b n)
    (ha : Tendsto a atTop (𝓝 t))
    (hb : Tendsto b atTop (𝓝 t))
    (hL : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    ρ ≤ |Y t - Function.leftLim Y t| := by sorry
