-- Prove2me | solution 1 for syracuseStep_odd
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:29:37.772038+00:00
-- url     : https://prove2.me/submissions/5907565d-3376-45a8-86ae-2bed6201d8a7

import Mathlib
import Definitions.Def_syracuseStep

theorem solution (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd
