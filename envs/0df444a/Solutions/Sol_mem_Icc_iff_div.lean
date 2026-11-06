-- Prove2me | solution 1 for mem_Icc_iff_div
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:23.246244+00:00
-- url     : https://prove2.me/submissions/73fbb3ff-f302-410a-897c-bfb48f602cc2

import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit true

open Real Set

variable {n : ℕ} {a b x : ℝ}

theorem solution (hb : 0 ≤ b) (hx : 0 < x) :
    n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, Set.mem_Icc, Nat.ceil_le,
    Nat.le_floor_iff (mul_nonneg hb hx.le), le_div_iff₀ hx, div_le_iff₀ hx]
