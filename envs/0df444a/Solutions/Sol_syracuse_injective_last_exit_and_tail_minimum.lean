-- Prove2me | solution 1 for syracuse_injective_last_exit_and_tail_minimum
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:11:52.771581+00:00
-- url     : https://prove2.me/submissions/3594cd70-f787-4807-908b-cfb87ff96116

import Mathlib
import Definitions.Def_syracuseStep

open Nat

private theorem image_coprime (t : ℕ) :
    syracuseStep t % 2 = 1 ∧ ¬ 3 ∣ syracuseStep t := by
  have hne : 3*t+1 ≠ 0 := by omega
  have hnot2 : ¬ 2 ∣ syracuseStep t := Nat.not_dvd_ordCompl Nat.prime_two hne
  refine ⟨by omega, ?_⟩
  intro h3
  have hd := dvd_trans h3 (Nat.ordCompl_dvd (3*t+1) 2)
  omega

private theorem one_mod_four_descent (t : ℕ) (ht : 1 < t) (hr : t%4 = 1) :
    syracuseStep t < t := by
  have hl : 2 ∣ 3*t+1 := by omega
  have hr' : 2 ∣ (3*t+1)/2 := by omega
  have hd : syracuseStep t = ordCompl[2] ((3*t+1)/4) := by
    rw [syracuseStep, ← Nat.ordCompl_div_of_dvd Nat.prime_two hl,
      ← Nat.ordCompl_div_of_dvd Nat.prime_two hr',
      show (3*t+1)/2/2=(3*t+1)/4 by omega]
  rw [hd]
  exact (Nat.div_le_self _ _).trans_lt (by omega)

theorem solution (n B : ℕ)
    (hodd : n % 2 = 1) (hB : 1 < B) (hnB : n < B)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    ∃ k j : ℕ, k < j ∧ syracuseStep^[k] n < B ∧
      2 * syracuseStep^[k+1] n = 3 * syracuseStep^[k] n + 1 ∧
      (∀ i > k, B ≤ syracuseStep^[i] n) ∧
      B ≤ syracuseStep^[j] n ∧ 2 * syracuseStep^[j] n + 2 ≤ 3 * B ∧
      (syracuseStep^[j] n % 12 = 7 ∨ syracuseStep^[j] n % 12 = 11) ∧
      (∀ i > k, syracuseStep^[j] n ≤ syracuseStep^[i] n) := by
  classical
  let x (i : ℕ) := syracuseStep^[i] n
  have hxstep (i : ℕ) : x (i+1) = syracuseStep (x i) :=
    Function.iterate_succ_apply' _ _ _
  have hxodd (i : ℕ) : x i % 2 = 1 := by
    cases i with
    | zero => exact hodd
    | succ i => rw [hxstep]; exact (image_coprime _).1
  have hfinite : (x ⁻¹' Set.Iio B).Finite :=
    Set.Finite.preimage hinj.injOn (Set.finite_Iio B)
  have hnonempty : (x ⁻¹' Set.Iio B).Nonempty := ⟨0, hnB⟩
  let k := hfinite.toFinset.max' (by rwa [Set.Finite.toFinset_nonempty])
  have hk_mem : k ∈ hfinite.toFinset := Finset.max'_mem _ _
  have hk : x k < B := hfinite.mem_toFinset.mp hk_mem
  have hstable (i : ℕ) (hi : k < i) : B ≤ x i := by
    by_contra hlt
    have hmem : i ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr (Nat.lt_of_not_ge hlt)
    exact (Nat.not_le_of_gt hi) (Finset.le_max' _ _ hmem)
  let a := (3*x k+1).factorization 2
  have ha : 0 < a := Nat.prime_two.factorization_pos_of_dvd (by omega) (by have := hxodd k; omega)
  have heq : 2^a * x (k+1) = 3*x k+1 := by
    rw [hxstep]
    exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hnext := hstable (k+1) (by omega)
  have ha1 : a = 1 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ a by omega)
    have hle := Nat.mul_le_mul_right (x (k+1)) hp
    rw [heq] at hle
    norm_num at hle
    omega
  rw [ha1, pow_one] at heq
  let V := x '' {i : ℕ | k < i}
  have hV : V.Nonempty := ⟨x (k+1), k+1, by simp, rfl⟩
  have hm : sInf V ∈ V := Nat.sInf_mem hV
  obtain ⟨j, hj, hminval⟩ := hm
  have hj' : k < j := hj
  have hmin (i : ℕ) (hi : k < i) : x j ≤ x i :=
    hminval.trans_le (Nat.sInf_le (show x i ∈ V from ⟨i, hi, rfl⟩))
  have hbelow := hmin (k+1) (by omega)
  have hBmin := hstable j hj'
  have hthree : ¬ 3 ∣ x j := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [hxstep]
    exact (image_coprime _).2
  have hnot1 : x j % 4 ≠ 1 := by
    intro h1
    have hdesc := one_mod_four_descent (x j) (by omega) h1
    rw [← hxstep] at hdesc
    exact (Nat.not_lt_of_ge (hmin (j+1) (by omega))) hdesc
  have hjodd := hxodd j
  have hres : x j % 12 = 7 ∨ x j % 12 = 11 := by omega
  refine ⟨k, j, hj', hk, heq, hstable, hBmin, ?_, hres, hmin⟩
  change 2 * x j + 2 ≤ 3 * B
  omega
