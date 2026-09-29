-- Prove2me | solution 1 for syracuse_seven_cycle_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T01:49:23.463562+00:00
-- url     : https://prove2.me/submissions/e40ed52a-c2ce-48ae-b6e0-4f576db7891a

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_no_small_cycle
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three
import Theorems.Thm_syracuse_cycle_min_upper_bound

open Nat

private lemma syracuseStep_pos {n : ℕ} (hn : 0 < n) : 0 < syracuseStep n := by
  unfold syracuseStep
  apply Nat.ordCompl_pos
  omega

private lemma syracuse_iterate_pos (m i : ℕ) (hm : 0 < m) :
    0 < syracuseStep^[i] m := by
  induction i with
  | zero => simpa using hm
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact syracuseStep_pos ih

theorem solution (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[7] m = m) : m = 1 := by
  classical
  have horbit : ∃ z : ℕ, ∃ i : ℕ, syracuseStep^[i] m = z :=
    ⟨m, 0, by simp⟩
  let z := Nat.find horbit
  have hz_spec : ∃ i : ℕ, syracuseStep^[i] m = z := Nat.find_spec horbit
  obtain ⟨j, hj⟩ := hz_spec
  have hz : 0 < z := by
    rw [← hj]
    exact syracuse_iterate_pos m j hm
  have hzcyc : syracuseStep^[7] z = z := by
    rw [← hj, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hcyc]
  have hzmin : ∀ i : ℕ, z ≤ syracuseStep^[i] z := by
    intro i
    change Nat.find horbit ≤ syracuseStep^[i] z
    rw [← hj, ← Function.iterate_add_apply]
    exact Nat.find_min' (m := syracuseStep^[i + j] m) horbit ⟨i + j, rfl⟩
  let K := ∑ i ∈ Finset.range 7, (3 * syracuseStep^[i] z + 1).factorization 2
  have hpow : 3 ^ 7 < 2 ^ K := by
    simpa [K] using syracuse_cycle_pow_two_gt_pow_three z 7 hz (by norm_num) hzcyc
  have hupper : 2 ^ K * z ^ 7 ≤ (3 * z + 1) ^ 7 := by
    simpa [K] using syracuse_cycle_min_upper_bound z 7 hz (by norm_num) hzcyc hzmin
  have hK : 12 ≤ K := by
    by_contra hK'
    have hKle : K ≤ 11 := by omega
    have hpow_le : 2 ^ K ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) hKle
    norm_num at hpow hpow_le
    omega
  have h4096 : 4096 * z ^ 7 ≤ (3 * z + 1) ^ 7 := by
    have hpowK : 4096 ≤ 2 ^ K := by
      calc
        4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
    exact (Nat.mul_le_mul_right (z ^ 7) hpowK).trans hupper
  have hz_le : z ≤ 33 := by
    by_contra hz_big
    have hz4 : 4 ≤ z := by omega
    have hlin : 4 * (3 * z + 1) ≤ 13 * z := by nlinarith
    have hpowlin : (4 * (3 * z + 1)) ^ 7 ≤ (13 * z) ^ 7 :=
      Nat.pow_le_pow_left hlin 7
    have hscaled : 4 ^ 7 * (3 * z + 1) ^ 7 ≤ 13 ^ 7 * z ^ 7 := by
      simpa [mul_pow] using hpowlin
    have hstrict : 13 ^ 7 * z ^ 7 < 4096 * 4 ^ 7 * z ^ 7 := by
      have hzpow : 0 < z ^ 7 := pow_pos hz 7
      exact (Nat.mul_lt_mul_right hzpow).mpr (by norm_num)
    have hscaled_lower : 4096 * 4 ^ 7 * z ^ 7 ≤ 4 ^ 7 * (3 * z + 1) ^ 7 := by
      calc
        4096 * 4 ^ 7 * z ^ 7 = 4 ^ 7 * (4096 * z ^ 7) := by ring
        _ ≤ 4 ^ 7 * (3 * z + 1) ^ 7 := Nat.mul_le_mul_left _ h4096
    omega
  have hz1 : z = 1 := syracuse_no_small_cycle z 7 hz (by norm_num) hz_le hzcyc
  have hj1 : syracuseStep^[j] m = 1 := hj.trans hz1
  have hone : syracuseStep 1 = 1 := by
    change ordCompl[2] 4 = 1
    rw [show 4 = 2 ^ 2 by norm_num, Nat.ordCompl_self_pow Nat.prime_two]
  have hiter_one : ∀ n : ℕ, syracuseStep^[n] 1 = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hone]
  have hmul0 : ∀ k : ℕ, syracuseStep^[7 * k] m = m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          syracuseStep^[7 * (k + 1)] m = syracuseStep^[7 * k + 7] m := by rw [Nat.mul_succ]
          _ = syracuseStep^[7 * k] (syracuseStep^[7] m) := by rw [Function.iterate_add_apply]
          _ = syracuseStep^[7 * k] m := by rw [hcyc]
          _ = m := ih
  have hmul : syracuseStep^[7 * j] m = m := hmul0 j
  have hjle : j ≤ 7 * j := by omega
  have hreach : syracuseStep^[7 * j] m = 1 := by
    calc
      syracuseStep^[7 * j] m = syracuseStep^[(7 * j - j) + j] m := by rw [Nat.sub_add_cancel hjle]
      _ = syracuseStep^[7 * j - j] (syracuseStep^[j] m) := by rw [Function.iterate_add_apply]
      _ = 1 := by rw [hj1, hiter_one]
  exact hmul.symm.trans hreach
