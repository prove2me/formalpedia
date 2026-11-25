-- Prove2me | solution 1 for syracuse_nontrivial_period_coordinates_at_1241513984
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:42:46.156718+00:00
-- url     : https://prove2.me/submissions/69c974c0-5b5a-4ea1-89b7-79787232527c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_no_cycle_below_1241513984
import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_cycle_three_consecutive_entries_budget
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three

/-
  Adapted from the accepted Prove2me solution of syracuse_nontrivial_period_coordinates_at_247463936
  (theorem 5930e7d5); only the cutoff, the budget base b and the upper Farey generator changed.
  The power-comparison scheme (budgetMargin) is adapted from the accepted Prove2me submission
  for syracuse_nontrivial_period_coordinates_at_twenty_million (theorem
  3cab8615-2e85-420a-8a3f-88728e4955e0) by user immiq, Apache-2.0 via the Prove2me terms.
-/

set_option exponentiation.threshold 200000

/- Compare powers by clearing rational exponents. -/
private theorem transposePowers (a i j : ℕ) : (a ^ i) ^ j = (a ^ j) ^ i := by
  rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm i j]

private theorem budgetMargin (p K : ℕ) (hp : 0 < p) (hu : 75235 * p ≤ 47468 * K) :
    87189139796826110176304037889 ^ p < 2 ^ (3 * K) * 3229227397666747876626137088 ^ p := by
  apply Nat.lt_of_not_ge
  intro hbad
  have hfixed : (87189139796826110176304037889 : ℕ) ^ 47468 < 2 ^ (3 * 75235) * 3229227397666747876626137088 ^ 47468 := by decide +kernel
  have h : ((87189139796826110176304037889 : ℕ) ^ p) ^ 47468 < (2 ^ (3 * K) * 3229227397666747876626137088 ^ p) ^ 47468 := by
    calc
      ((87189139796826110176304037889 : ℕ) ^ p) ^ 47468 = (87189139796826110176304037889 ^ 47468) ^ p := transposePowers _ _ _
      _ < (2 ^ (3 * 75235) * 3229227397666747876626137088 ^ 47468) ^ p :=
        Nat.pow_lt_pow_left (n := p) hfixed (Nat.ne_of_gt hp)
      _ ≤ (2 ^ (3 * K) * 3229227397666747876626137088 ^ p) ^ 47468 := by
        rw [Nat.mul_pow, Nat.mul_pow, transposePowers 3229227397666747876626137088 47468 p]
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
    79335 ≤ p ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 31867*a + 47468*b ∧ K = 50508*a + 75235*b) := by
  intro K
  have hbase (i : ℕ) : 1241513984 ≤ syracuseStep^[i] m := by
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
    have hone := syracuse_no_cycle_below_1241513984 _ p hpos hp hsmall hreturn
    exact hne (syracuse_periodic_reaches_one m p hp hcycle ⟨i, hone⟩)
  have budget := syracuse_cycle_three_consecutive_entries_budget m p 155189248
    (by decide) hcycle hbase
  have hg : 3 ^ p < 2 ^ K := syracuse_cycle_pow_two_gt_pow_three m p hm hp hcycle
  have exphigh : 47468 * K < 75235 * p := by
    apply Nat.lt_of_not_ge
    intro contra
    exact Nat.not_le_of_gt (budgetMargin p K hp contra) budget
  have explow : 50508 * p < 31867 * K := meanLower p K hp hg
  refine ⟨by omega, 75235 * p - 47468 * K, 31867 * K - 50508 * p, by omega, by omega, by omega, by omega⟩
