-- Prove2me | solution 1 for syracuse_power_gap_baseline_budget_period_sparse_6291
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-02T14:23:02.066712+00:00
-- url     : https://prove2.me/submissions/148bed53-8007-4529-90a5-00c1158db5de

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

/-
Task94 source-only submission candidate derived from the reviewed Task93 source.
This assembled packet requires independent review; no elaboration, kernel check,
runtime guarantee, public acceptance, or improved baseline is claimed.
-/

namespace CollatzBudgetPeriodSparse6291Draft01

-- Ordinary kernel-checkable repeated squaring, copied from the fixed5626 source.
def binaryPow : Nat → Nat → Nat → Nat
  | _, _, 0 => 1
  | a, n, fuel + 1 =>
      let r := binaryPow a (n / 2) fuel
      if n % 2 = 0 then r * r else r * r * a

theorem binaryPow_eq (a n fuel : Nat) (h : n < 2 ^ fuel) :
    binaryPow a n fuel = a ^ n := by
  induction fuel generalizing n with
  | zero =>
      have hn : n = 0 := by simpa using h
      subst n
      rfl
  | succ fuel ih =>
      have hn : n / 2 < 2 ^ fuel := by
        rw [pow_succ] at h
        omega
      simp only [binaryPow, ih (n / 2) hn]
      split
      · rename_i heven
        have he : n = n / 2 + n / 2 := by omega
        rw [← pow_add, ← he]
      · rename_i hodd
        have he : n = n / 2 + n / 2 + 1 := by omega
        rw [← pow_add, ← pow_succ, ← he]

private theorem budget_margin_certificate :
    binaryPow 6930001 4961 14 <
      binaryPow 2 7863 14 * binaryPow 2310000 4961 14 := by
  decide +kernel

theorem budget_margin_4961 :
    (6930001 : ℕ) ^ 4961 < 2 ^ 7863 * 2310000 ^ 4961 := by
  simpa only [binaryPow_eq 6930001 4961 14 (by decide),
    binaryPow_eq 2 7863 14 (by decide),
    binaryPow_eq 2310000 4961 14 (by decide)] using budget_margin_certificate

/-- Raising the unchanged budget and the single margin gives a strict mean upper bound. -/
theorem mean_upper_of_budget (p K : ℕ) (hp : 0 < p)
    (hbudget : 2 ^ K * 2310000 ^ p ≤ 6930001 ^ p) :
    4961 * K < 7863 * p := by
  have hbudget4961 :
      (2 : ℕ) ^ (4961 * K) * 2310000 ^ (4961 * p) ≤
        6930001 ^ (4961 * p) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul,
      Nat.mul_comm K 4961, Nat.mul_comm p 4961] using
      Nat.pow_le_pow_left hbudget 4961
  have hmarginp :
      (6930001 : ℕ) ^ (4961 * p) <
        2 ^ (7863 * p) * 2310000 ^ (4961 * p) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using
      Nat.pow_lt_pow_left budget_margin_4961 (ne_of_gt hp)
  have hscaled :
      (2 : ℕ) ^ (4961 * K) * 2310000 ^ (4961 * p) <
        2 ^ (7863 * p) * 2310000 ^ (4961 * p) :=
    hbudget4961.trans_lt hmarginp
  have hpower : (2 : ℕ) ^ (4961 * K) < 2 ^ (7863 * p) :=
    Nat.lt_of_mul_lt_mul_right hscaled
  exact (Nat.pow_lt_pow_iff_right (Nat.lt_succ_self 1)).mp hpower

private theorem block_power_gap_1054_665 :
    (2 : ℕ) ^ 1054 < 3 ^ 665 := by
  decide +kernel

/-- The single lower block gap lifts to an arbitrary positive period. -/
theorem mean_lower_of_power_gap (p K : ℕ) (hp : 0 < p)
    (hgap : 3 ^ p < 2 ^ K) : 1054 * p < 665 * K := by
  have hblockp : ((2 : ℕ) ^ 1054) ^ p < (3 ^ 665) ^ p :=
    Nat.pow_lt_pow_left block_power_gap_1054_665 (ne_of_gt hp)
  have hgap665 : ((3 : ℕ) ^ p) ^ 665 < (2 ^ K) ^ 665 :=
    Nat.pow_lt_pow_left hgap (Nat.succ_ne_zero 664)
  have hpower : (2 : ℕ) ^ (1054 * p) < 2 ^ (665 * K) := by
    calc
      (2 : ℕ) ^ (1054 * p) = ((2 : ℕ) ^ 1054) ^ p :=
        Nat.pow_mul 2 1054 p
      _ < (3 ^ 665) ^ p := hblockp
      _ = ((3 : ℕ) ^ p) ^ 665 := Nat.pow_right_comm 3 665 p
      _ < (2 ^ K) ^ 665 := hgap665
      _ = (2 : ℕ) ^ (665 * K) := (Nat.pow_mul' 2 665 K).symm
  exact (Nat.pow_lt_pow_iff_right (Nat.lt_succ_self 1)).mp hpower

end CollatzBudgetPeriodSparse6291Draft01

/-- The original arithmetic budget leaves only period 6291 below 6956.
This does not eliminate the remaining period or assert any cycle theorem. -/
theorem solution (p K : ℕ) (hlarge : 6291 ≤ p)
    (hgap : 3 ^ p < 2 ^ K)
    (hbudget : 2 ^ K * 2310000 ^ p ≤ 6930001 ^ p) :
    p = 6291 ∨ 6956 ≤ p := by
  have hp : 0 < p := by omega
  have hlower := CollatzBudgetPeriodSparse6291Draft01.mean_lower_of_power_gap p K hp hgap
  have hupper := CollatzBudgetPeriodSparse6291Draft01.mean_upper_of_budget p K hp hbudget
  by_cases hsmall : p < 6956
  · let d : ℕ := 665 * K - 1054 * p
    let t : ℕ := 7863 * p - 4961 * K
    have hd_pos : 1 ≤ d := by dsimp [d]; omega
    have ht_pos : 1 ≤ t := by dsimp [t]; omega
    have hd_exact : 665 * K = 1054 * p + d := by dsimp [d]; omega
    have ht_exact : 7863 * p = 4961 * K + t := by dsimp [t]; omega
    -- 7863*665 - 4961*1054 = 1, so both nonnegative differences reconstruct p.
    have hidentity : p = 665 * t + 4961 * d := by omega
    have hd_one : d = 1 := by omega
    have ht_two : t = 2 := by omega
    left
    omega
  · right
    omega
