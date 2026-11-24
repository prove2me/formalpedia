-- Prove2me | solution 1 for syracuse_nontrivial_period_coordinates_at_247463936
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T23:20:37.085782+00:00
-- url     : https://prove2.me/submissions/ecb1b6b9-570e-40ec-aad6-99367e76b02e

import Theorems.Thm_syracuse_no_cycle_below_247463936
import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_cycle_three_consecutive_entries_budget
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three

/-
  The power-comparison scheme (budgetMargin) is adapted from the accepted Prove2me submission
  for syracuse_nontrivial_period_coordinates_at_twenty_million (theorem
  3cab8615-2e85-420a-8a3f-88728e4955e0) by user immiq, Apache-2.0 via the Prove2me terms.
-/

set_option exponentiation.threshold 200000

/- Compare powers by clearing rational exponents. -/
private theorem transposePowers (a i j : ℕ) : (a ^ i) ^ j = (a ^ j) ^ i := by
  rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm i j]

private theorem budgetMargin (p K : ℕ) (hp : 0 < p) (hu : 24727 * p ≤ 15601 * K) :
    690467586742413694710841345 ^ p < 2 ^ (3 * K) * 25572873495022159509061632 ^ p := by
  apply Nat.lt_of_not_ge
  intro hbad
  have hfixed : (690467586742413694710841345 : ℕ) ^ 15601 < 2 ^ (3 * 24727) * 25572873495022159509061632 ^ 15601 := by decide +kernel
  have h : ((690467586742413694710841345 : ℕ) ^ p) ^ 15601 < (2 ^ (3 * K) * 25572873495022159509061632 ^ p) ^ 15601 := by
    calc
      ((690467586742413694710841345 : ℕ) ^ p) ^ 15601 = (690467586742413694710841345 ^ 15601) ^ p := transposePowers _ _ _
      _ < (2 ^ (3 * 24727) * 25572873495022159509061632 ^ 15601) ^ p :=
        Nat.pow_lt_pow_left (n := p) hfixed (Nat.ne_of_gt hp)
      _ ≤ (2 ^ (3 * K) * 25572873495022159509061632 ^ p) ^ 15601 := by
        rw [Nat.mul_pow, Nat.mul_pow, transposePowers 25572873495022159509061632 15601 p]
        apply Nat.mul_le_mul_right
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.not_le_of_gt h (Nat.pow_le_pow_left hbad _)

private theorem meanLower (p K : ℕ) (hp : 0 < p) (hg : 3 ^ p < 2 ^ K) :
    50508 * p < 31867 * K := by
  have hblock : (2 : ℕ) ^ 50508 < 3 ^ 31867 := by decide +kernel
  apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
  calc
    (2 : ℕ) ^ (50508 * p) = (2 ^ 50508) ^ p := Nat.pow_mul 2 50508 p
    _ < (3 ^ 31867) ^ p := Nat.pow_lt_pow_left hblock (Nat.ne_of_gt hp)
    _ = (3 ^ p) ^ 31867 := Nat.pow_right_comm 3 31867 p
    _ < (2 ^ K) ^ 31867 := Nat.pow_lt_pow_left hg (by decide)
    _ = 2 ^ (31867 * K) := (Nat.pow_mul' 2 31867 K).symm

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    47468 ≤ p ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 31867*a + 15601*b ∧ K = 50508*a + 24727*b) := by
  intro K
  have hbase (i : ℕ) : 247463936 ≤ syracuseStep^[i] m := by
    apply Nat.le_of_not_gt
    intro hsmall
    have hpos : 0 < syracuseStep^[i] m := by
      cases i with
      | zero => exact hm
      | succ j =>
        rw [Function.iterate_succ_apply']
        exact Nat.ordCompl_pos 2 (by omega : 3 * syracuseStep^[j] m + 1 ≠ 0)
    have hreturn : syracuseStep^[p] (syracuseStep^[i] m) = syracuseStep^[i] m := by
      rw [← Function.iterate_add_apply, Nat.add_comm p i, Function.iterate_add_apply, hcycle]
    have hone := syracuse_no_cycle_below_247463936 _ p hpos hp hsmall hreturn
    exact hne (syracuse_periodic_reaches_one m p hp hcycle ⟨i, hone⟩)
  have budget := syracuse_cycle_three_consecutive_entries_budget m p 30932992
    (by decide) hcycle hbase
  have hg : 3 ^ p < 2 ^ K := syracuse_cycle_pow_two_gt_pow_three m p hm hp hcycle
  have exphigh : 15601 * K < 24727 * p := by
    apply Nat.lt_of_not_ge
    intro contra
    exact Nat.not_le_of_gt (budgetMargin p K hp contra) budget
  have explow : 50508 * p < 31867 * K := meanLower p K hp hg
  refine ⟨by omega, 24727 * p - 15601 * K, 31867 * K - 50508 * p, by omega, by omega, by omega, by omega⟩
