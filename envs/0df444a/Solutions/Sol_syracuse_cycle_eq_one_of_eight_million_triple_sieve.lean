-- Prove2me | solution 1 for syracuse_cycle_eq_one_of_eight_million_triple_sieve
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T08:18:33.369117+00:00
-- url     : https://prove2.me/submissions/b62a9120-8872-4bf6-b47e-ee4dfba174d8

import Theorems.Thm_syracuse_cycle_three_consecutive_entries_budget
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three
import Theorems.Thm_syracuse_no_cycle_below_two_pow_twenty_three
import Theorems.Thm_syracuse_periodic_reaches_one

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

set_option exponentiation.threshold 350000 in
private theorem budgetMargin (p K : ℕ) (hp : 0 < p) (hu : 116173 * p ≤ 73297 * K) :
    26895355590655500877825 ^ p < 2 ^ (3 * K) * 996124179980315787264 ^ p := by
  apply Nat.lt_of_not_ge
  intro hbad
  have hfixed : (26895355590655500877825 : ℕ) ^ 73297 < 2 ^ (3 * 116173) * 996124179980315787264 ^ 73297 := by decide +kernel
  have h : ((26895355590655500877825 : ℕ) ^ p) ^ 73297 < (2 ^ (3 * K) * 996124179980315787264 ^ p) ^ 73297 := by
    calc
      ((26895355590655500877825 : ℕ) ^ p) ^ 73297 = (26895355590655500877825 ^ 73297) ^ p := transposePowers _ _ _
      _ < (2 ^ (3 * 116173) * 996124179980315787264 ^ 73297) ^ p :=
        Nat.pow_lt_pow_left (n := p) hfixed (Nat.ne_of_gt hp)
      _ ≤ (2 ^ (3 * K) * 996124179980315787264 ^ p) ^ 73297 := by
        rw [Nat.mul_pow, Nat.mul_pow, transposePowers 996124179980315787264 73297 p]
        apply Nat.mul_le_mul_right
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.not_le_of_gt h (Nat.pow_le_pow_left hbad _)

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hcyc : syracuseStep^[p] m = m)
    (hsieve : 116173 * p ≤ 73297 * (50508 * p / 31867 + 1)) : m = 1 := by
  by_contra hne
  have hbase (i : ℕ) : 8388608 ≤ syracuseStep^[i] m := by
    apply Nat.le_of_not_gt
    intro hsmall
    have hpos : 0 < syracuseStep^[i] m := by
      cases i with
      | zero => exact hm
      | succ j =>
        rw [Function.iterate_succ_apply']
        exact Nat.ordCompl_pos 2 (by omega : 3 * syracuseStep^[j] m + 1 ≠ 0)
    have hreturn : syracuseStep^[p] (syracuseStep^[i] m) = syracuseStep^[i] m := by
      rw [← Function.iterate_add_apply, Nat.add_comm p i, Function.iterate_add_apply, hcyc]
    have hone := syracuse_no_cycle_below_two_pow_twenty_three _ p hpos hp hsmall hreturn
    exact hne (syracuse_periodic_reaches_one m p hp hcyc ⟨i, hone⟩)
  let K := ∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2
  have hg : 3 ^ p < 2 ^ K := syracuse_cycle_pow_two_gt_pow_three m p hm hp hcyc
  have hl := exponentLower p K hp hg
  have hK : 50508 * p / 31867 + 1 ≤ K := by omega
  have upper := budgetMargin p K hp (hsieve.trans (Nat.mul_le_mul_left _ hK))
  have hbase8 (i : ℕ) : 8 * 1048576 ≤ syracuseStep^[i] m :=
    Nat.le_trans (by decide : 8 * 1048576 ≤ 8388608) (hbase i)
  have budget := syracuse_cycle_three_consecutive_entries_budget m p 1048576 (by decide) hcyc hbase8
  exact Nat.not_le_of_gt upper budget
