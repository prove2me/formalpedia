-- Prove2me | solution 1 for flt5_pow5_inj
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T18:01:18.391385+00:00
-- url     : https://prove2.me/submissions/e292ea4e-ff10-4a9a-afa1-5d1b51da2469

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

-- flt5_pow5_inj: 5th power is injective on ℤ
-- Strategy: reduce to natAbs level (Nat), use Nat.pow_lt_pow_left for strict monotonicity.
-- Cross-sign cases: (-z)^5 = -(z^5) by ring, then 2*(z^5) = 0 → z = 0 via omega+natAbs.

theorem solution (x y : ℤ) (h : x ^ 5 = y ^ 5) : x = y := by
  -- Step 1: natAbs^5 equal
  have habs : x.natAbs ^ 5 = y.natAbs ^ 5 := by
    have hh : (x ^ 5).natAbs = (y ^ 5).natAbs := congr_arg Int.natAbs h
    simp only [Int.natAbs_pow] at hh
    exact hh
  -- Step 2: natAbs equal (strict monotonicity of ·^5 on ℕ)
  have heq_abs : x.natAbs = y.natAbs := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : x.natAbs ^ 5 < y.natAbs ^ 5 := Nat.pow_lt_pow_left hlt (by decide)
      omega
    · have : y.natAbs ^ 5 < x.natAbs ^ 5 := Nat.pow_lt_pow_left hgt (by decide)
      omega
  -- Step 3: a^5 = 0 → a = 0 for ℤ (via natAbs positivity)
  have pow5_zero : ∀ a : ℤ, a ^ 5 = 0 → a = 0 := by
    intro a hpow
    by_contra hne
    have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr hne
    have h_nat : a.natAbs ^ 5 = 0 := by
      have := congr_arg Int.natAbs hpow
      simp only [Int.natAbs_pow, Int.natAbs_zero] at this
      exact this
    have h_pos : 0 < a.natAbs ^ 5 := Nat.pow_pos hpos
    omega
  -- Step 4: case split on signs via Int.natAbs_eq
  have neg_pow5 : ∀ z : ℤ, (-z) ^ 5 = -(z ^ 5) := fun z => by ring
  rcases Int.natAbs_eq x with hx | hx <;>
    rcases Int.natAbs_eq y with hy | hy
  · -- x = |x|, y = |y|
    have hcast : (x.natAbs : ℤ) = y.natAbs := by exact_mod_cast heq_abs
    omega
  · -- x = |x|, y = -|y|, so y = -x; then x^5 = -x^5 → x = 0
    have hcast : (x.natAbs : ℤ) = y.natAbs := by exact_mod_cast heq_abs
    have hval : y = -x := by omega
    rw [hval, neg_pow5] at h
    have hpow : x ^ 5 = 0 := by omega
    have : x = 0 := pow5_zero x hpow
    omega
  · -- x = -|x|, y = |y|, so x = -y; then y^5 = -y^5 → y = 0
    have hcast : (x.natAbs : ℤ) = y.natAbs := by exact_mod_cast heq_abs
    have hval : x = -y := by omega
    rw [hval, neg_pow5] at h
    have hpow : y ^ 5 = 0 := by omega
    have : y = 0 := pow5_zero y hpow
    omega
  · -- x = -|x|, y = -|y|
    have hcast : (x.natAbs : ℤ) = y.natAbs := by exact_mod_cast heq_abs
    omega
