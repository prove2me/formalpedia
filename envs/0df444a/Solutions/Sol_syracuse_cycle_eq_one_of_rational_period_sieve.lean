-- Prove2me | solution 1 for syracuse_cycle_eq_one_of_rational_period_sieve
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:40:09.757745+00:00
-- url     : https://prove2.me/submissions/37027b5f-eca5-4bdb-ba9b-7b00117a5e31

import Theorems.Thm_syracuse_cycle_eq_one_of_margin_at
import Theorems.Thm_syracuse_no_cycle_below_2887463

/- Compare powers by clearing rational exponents. -/
private theorem transposePowers (a i j : ℕ) : (a ^ i) ^ j = (a ^ j) ^ i := by
  rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm i j]

set_option exponentiation.threshold 150000 in
private theorem exponentLower (p K : ℕ) (hp : 0 < p) (hg : 3 ^ p < 2 ^ K) :
    50508 * p < 31867 * K := by
  have hfixed : (2 : ℕ) ^ 50508 < 3 ^ 31867 := by decide +kernel
  have h : (2 : ℕ) ^ (50508 * p) < 2 ^ (31867 * K) := by
    calc
      (2 : ℕ) ^ (50508 * p) = (2 ^ 50508) ^ p := Nat.pow_mul _ _ _
      _ < (3 ^ 31867) ^ p :=
        Nat.pow_lt_pow_left (n := p) hfixed (Nat.ne_of_gt hp)
      _ = (3 ^ p) ^ 31867 := transposePowers _ _ _
      _ < (2 ^ K) ^ 31867 := Nat.pow_lt_pow_left (n := 31867) hg (by decide)
      _ = 2 ^ (31867 * K) := by rw [← Nat.pow_mul, Nat.mul_comm K]
  exact Nat.lt_of_not_ge fun hbad => Nat.not_le_of_gt h (Nat.pow_le_pow_right (by decide) hbad)

set_option exponentiation.threshold 150000 in
private theorem budgetMargin (p K : ℕ) (hp : 0 < p) (hu : 145834 * p ≤ 92011 * K) :
    8662390 ^ p < 2 ^ K * 2887463 ^ p := by
  apply Nat.lt_of_not_ge
  intro hbad
  have hfixed : (8662390 : ℕ) ^ 92011 < 2 ^ 145834 * 2887463 ^ 92011 := by decide +kernel
  have h : ((8662390 : ℕ) ^ p) ^ 92011 < (2 ^ K * 2887463 ^ p) ^ 92011 := by
    calc
      ((8662390 : ℕ) ^ p) ^ 92011 = (8662390 ^ 92011) ^ p := transposePowers _ _ _
      _ < (2 ^ 145834 * 2887463 ^ 92011) ^ p :=
        Nat.pow_lt_pow_left (n := p) hfixed (Nat.ne_of_gt hp)
      _ ≤ (2 ^ K * 2887463 ^ p) ^ 92011 := by
        rw [Nat.mul_pow, Nat.mul_pow, transposePowers 2887463 92011 p]
        apply Nat.mul_le_mul_right
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm K 92011] using hu)
  exact Nat.not_le_of_gt h (Nat.pow_le_pow_left hbad _)

/-- When the rational interval admits no integer exponent, a positive
    periodic Syracuse orbit consists of the fixed point 1. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hsieve : 145834 * p ≤ 92011 * (50508 * p / 31867 + 1)) : m = 1 := by
  apply syracuse_cycle_eq_one_of_margin_at p m 2887463 hp hm (by decide) hcyc
    syracuse_no_cycle_below_2887463
  intro K hg
  have hl := exponentLower p K hp hg
  have hK : 50508 * p / 31867 + 1 ≤ K := by omega
  exact budgetMargin p K hp (hsieve.trans (Nat.mul_le_mul_left _ hK))
