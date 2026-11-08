-- Prove2me | solution 1 for levy_foundations_piecewisePathAtZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:54:51.209092+00:00
-- url     : https://prove2.me/submissions/32ee57b1-76a4-4cad-9f46-a4f1bdfa96ae

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original source's deterministic zero-time jump-count argument. -/
theorem solution
    {x₀ b : ℝ} {T Y : ℕ → ℝ} (hpos : 0 < T 0) :
    LevyFoundations.piecewisePath x₀ b T Y 0 = x₀ := by
  classical
  have hcount : LevyFoundations.jumpCount T 0 = 0 := by
    have hmem : (0 : ℕ) ∈ {n : ℕ | (0 : ℝ) < T n} := hpos
    have hle : LevyFoundations.jumpCount T 0 ≤ 0 := by
      unfold LevyFoundations.jumpCount
      exact Nat.sInf_le hmem
    exact Nat.eq_zero_of_le_zero hle
  simp [LevyFoundations.piecewisePath, hcount]
