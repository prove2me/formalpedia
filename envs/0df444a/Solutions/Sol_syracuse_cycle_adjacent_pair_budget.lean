-- Prove2me | solution 1 for syracuse_cycle_adjacent_pair_budget
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:49:34.176932+00:00
-- url     : https://prove2.me/submissions/a258de79-8453-4313-ac79-56e5ebae8174

import Definitions.Def_syracuseStep
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Function.Iterate

private theorem adjacentHigh (x y e B H : ℕ) (hstep : 2 ^ e * y = 3 * x + 1)
    (hx : B ≤ x) (hy : B ≤ y) (h1 : 2 * H ≤ 3 * B + 1) (h2 : 3 * H ≤ 4 * B + 1) :
    H ≤ x ∨ H ≤ y := by
  by_cases he : e ≤ 1
  · have hc : 2 ^ e ≤ 2 := Nat.pow_le_pow_right (by decide) he
    have h := Nat.mul_le_mul_right y hc
    omega
  · have hc : 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ e)
    have h := Nat.mul_le_mul_right y hc
    omega

private theorem ratioBound {x b : ℕ} (h : b ≤ x) :
    (3 * x + 1) * b ≤ x * (3 * b + 1) := by
  simpa only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
    Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using Nat.add_le_add_left h (3 * x * b)

private theorem shiftProduct (f : ℕ → ℕ) (p : ℕ) (h : f p = f 0) (hf : 0 < f 0) :
    (∏ i ∈ Finset.range p, f (i + 1)) = ∏ i ∈ Finset.range p, f i := by
  apply Nat.eq_of_mul_eq_mul_right hf
  rw [← Finset.prod_range_succ', ← h, ← Finset.prod_range_succ]

theorem solution (m p B H : ℕ) (hB : 0 < B) (hcycle : syracuseStep^[p] m = m)
    (hbase : ∀ i : ℕ, B ≤ syracuseStep^[i] m)
    (h1 : 2 * H ≤ 3 * B + 1) (h2 : 3 * H ≤ 4 * B + 1) :
    2 ^ (2 * ∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      (B * H) ^ p ≤ ((3 * B + 1) * (3 * H + 1)) ^ p := by
  let x (i : ℕ) := syracuseStep^[i] m
  let f (i : ℕ) := 3 * x i + 1
  let e (i : ℕ) := (f i).factorization 2
  let R := Finset.range p
  have hstep (i : ℕ) : 2 ^ e i * x (i + 1) = f i := by
    change 2 ^ (f i).factorization 2 * syracuseStep^[i + 1] m = f i
    rw [Function.iterate_succ_apply']
    exact Nat.ordProj_mul_ordCompl_eq_self (f i) 2
  have hpair (i : ℕ) : f i * f (i + 1) * (B * H) ≤
      x i * x (i + 1) * ((3 * B + 1) * (3 * H + 1)) := by
    rcases adjacentHigh _ _ _ _ _ (hstep i) (hbase i) (hbase (i + 1)) h1 h2 with hi | hj
    · simpa only [f, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul (ratioBound hi) (ratioBound (hbase (i + 1)))
    · simpa only [f, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul (ratioBound (hbase i)) (ratioBound hj)
  have hx : x p = x 0 := hcycle
  have xpos (i : ℕ) : 0 < x i := lt_of_lt_of_le hB (hbase i)
  have sx := shiftProduct x p hx (xpos 0)
  have sf := shiftProduct f p (congrArg (fun z => 3 * z + 1) hx) (by dsimp [f]; omega)
  have hprod : (∏ i ∈ R, f i) = 2 ^ (∑ i ∈ R, e i) * ∏ i ∈ R, x i := by
    calc
      (∏ i ∈ R, f i) = ∏ i ∈ R, (2 ^ e i * x (i + 1)) :=
        Finset.prod_congr rfl (fun i _ => (hstep i).symm)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sx]
  have hp := Finset.prod_le_prod' (s := Finset.range p) (fun i _ => hpair i)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, sf, sx] at hp
  rw [← Nat.mul_pow, ← Nat.mul_pow (3 * B + 1) (3 * H + 1)] at hp
  change (∏ i ∈ R, f i) * (∏ i ∈ R, f i) * (B * H) ^ p ≤
    (∏ i ∈ R, x i) * (∏ i ∈ R, x i) * ((3 * B + 1) * (3 * H + 1)) ^ p at hp
  rw [hprod] at hp
  have hpos : 0 < ∏ i ∈ R, x i := Finset.prod_pos (fun i _ => xpos i)
  change 2 ^ (2 * ∑ i ∈ R, e i) * (B * H) ^ p ≤ _
  apply Nat.le_of_mul_le_mul_right (c := (∏ i ∈ R, x i) * ∏ i ∈ R, x i) _ (Nat.mul_pos hpos hpos)
  simpa only [two_mul, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hp
