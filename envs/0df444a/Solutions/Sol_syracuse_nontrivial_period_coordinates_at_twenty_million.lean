-- Prove2me | solution 1 for syracuse_nontrivial_period_coordinates_at_twenty_million
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T10:37:42.865174+00:00
-- url     : https://prove2.me/submissions/a94a4af9-f0cc-49ca-b39c-1bad94719fb6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_no_cycle_below_twenty_million_cutoff
import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_cycle_three_consecutive_entries_budget
import Theorems.Thm_syracuse_nontrivial_period_farey_coordinates

/- Compare powers by clearing rational exponents. -/
private theorem transposePowers (a i j : ℕ) : (a ^ i) ^ j = (a ^ j) ^ i := by
  rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm i j]

set_option exponentiation.threshold 190000 in
private theorem budgetMargin (p K : ℕ) (hp : 0 < p) (hu : 62587 * p ≤ 39488 * K) :
    420239905499113972039681 ^ p < 2 ^ (3 * K) * 15564440312192434176000 ^ p := by
  apply Nat.lt_of_not_ge
  intro hbad
  have hfixed : (420239905499113972039681 : ℕ) ^ 39488 < 2 ^ (3 * 62587) * 15564440312192434176000 ^ 39488 := by decide +kernel
  have h : ((420239905499113972039681 : ℕ) ^ p) ^ 39488 < (2 ^ (3 * K) * 15564440312192434176000 ^ p) ^ 39488 := by
    calc
      ((420239905499113972039681 : ℕ) ^ p) ^ 39488 = (420239905499113972039681 ^ 39488) ^ p := transposePowers _ _ _
      _ < (2 ^ (3 * 62587) * 15564440312192434176000 ^ 39488) ^ p :=
        Nat.pow_lt_pow_left (n := p) hfixed (Nat.ne_of_gt hp)
      _ ≤ (2 ^ (3 * K) * 15564440312192434176000 ^ p) ^ 39488 := by
        rw [Nat.mul_pow, Nat.mul_pow, transposePowers 15564440312192434176000 39488 p]
        apply Nat.mul_le_mul_right
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.not_le_of_gt h (Nat.pow_le_pow_left hbad _)

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    13606 ≤ p ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 665*a + 10946*b ∧ K = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 10*b < 3*a) := by
  dsimp only
  let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
  have hbase (i : ℕ) : 20971520 ≤ syracuseStep^[i] m := by
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
    have hone := syracuse_no_cycle_below_twenty_million_cutoff _ p hpos hp hsmall hreturn
    exact hne (syracuse_periodic_reaches_one m p hp hcycle ⟨i, hone⟩)
  have budget := syracuse_cycle_three_consecutive_entries_budget m p 2621440
    (by decide) hcycle hbase
  have exphigh : 39488*K < 62587*p := by
    apply Nat.lt_of_not_ge
    intro contra
    exact Nat.not_le_of_gt (budgetMargin p K hp contra) budget
  obtain ⟨a,b,ha,hb,hpab,hKab,hlo,_⟩ := syracuse_nontrivial_period_farey_coordinates m p hm hp hcycle hne
  change K = 1054*a + 17349*b at hKab
  have sharpened : 10*b < 3*a := by omega
  have ha4 : 4 ≤ a := by omega
  exact ⟨by omega, a,b,ha,hb,hpab,hKab,hlo,sharpened⟩
