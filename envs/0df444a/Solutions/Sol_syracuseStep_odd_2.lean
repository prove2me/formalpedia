-- Prove2me | solution 2 for syracuseStep_odd
-- status  : ACCEPTED   (prove)
-- author  : @curiyu
-- created : 2026-09-08T04:32:37.540722+00:00
-- url     : https://prove2.me/submissions/24dcde33-71b2-4566-a8ef-7633181f5c57

import Mathlib
import Definitions.Def_syracuseStep

theorem solution (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd
