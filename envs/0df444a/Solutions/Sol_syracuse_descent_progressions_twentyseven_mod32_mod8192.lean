-- Prove2me | solution 1 for syracuse_descent_progressions_twentyseven_mod32_mod8192
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T02:00:31.203971+00:00
-- url     : https://prove2.me/submissions/32fab4da-718a-4ed5-9ce6-032f957dfb84

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import Definitions.Def_syracuseStep

open Nat

/-- Exact Syracuse step from a prescribed complete power of two factor. -/
private theorem step_eq (a : ℕ) {x y : ℕ} (h : 3 * x + 1 = 2 ^ a * y) (hy : Odd y) :
    syracuseStep x = y := by
  have hy0 : y ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hy
  have hfac : (3 * x + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hy0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * x + 1) = y
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

/-- Upper bound when the prescribed power of two need not be complete. -/
private theorem step_le (a : ℕ) {x y : ℕ} (h : 3 * x + 1 = 2 ^ a * y) :
    syracuseStep x ≤ y := by
  have hne : 3 * x + 1 ≠ 0 := by omega
  have hle : a ≤ (3 * x + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 ⟨y, h⟩
  show ordCompl[2] (3 * x + 1) ≤ y
  calc
    (3 * x + 1) / 2 ^ ((3 * x + 1).factorization 2)
        ≤ (3 * x + 1) / 2 ^ a :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hle) (by positivity)
    _ = y := by rw [h, Nat.mul_div_cancel_left _ (by positivity)]

/-- Every listed residue has an eight-step affine descent certificate. -/
theorem solution (n : ℕ)
    (h : n % 8192 = 539 ∨ n % 8192 = 1563 ∨ n % 8192 = 2075 ∨
      n % 8192 = 3483 ∨ n % 8192 = 3835 ∨ n % 8192 = 4507 ∨
      n % 8192 = 4859 ∨ n % 8192 = 5371 ∨ n % 8192 = 5723 ∨
      n % 8192 = 6747 ∨ n % 8192 = 7259) :
    ∃ t : ℕ, t ≤ 8 ∧ syracuseStep^[t] n < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 539 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 539) = 12288 * m + 809 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 809) = 9216 * m + 607 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 607) = 13824 * m + 911 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 911) = 20736 * m + 1367 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 1367) = 31104 * m + 2051 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 2051) = 46656 * m + 3077 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (46656 * m + 3077) = 8748 * m + 577 :=
      step_eq 4 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (8748 * m + 577) ≤ 6561 * m + 433 :=
      step_le 2 (by ring)
    change (syracuseStep^[8]) (8192 * m + 539) < 8192 * m + 539
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 1563 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 1563) = 12288 * m + 2345 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 2345) = 9216 * m + 1759 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 1759) = 13824 * m + 2639 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 2639) = 20736 * m + 3959 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 3959) = 31104 * m + 5939 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 5939) = 46656 * m + 8909 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (46656 * m + 8909) = 17496 * m + 3341 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (17496 * m + 3341) ≤ 6561 * m + 1253 :=
      step_le 3 (by ring)
    change (syracuseStep^[8]) (8192 * m + 1563) < 8192 * m + 1563
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 2075 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 2075) = 12288 * m + 3113 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 3113) = 9216 * m + 2335 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 2335) = 13824 * m + 3503 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 3503) = 20736 * m + 5255 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 5255) = 31104 * m + 7883 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 7883) = 46656 * m + 11825 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (46656 * m + 11825) = 34992 * m + 8869 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (34992 * m + 8869) ≤ 6561 * m + 1663 :=
      step_le 4 (by ring)
    change (syracuseStep^[8]) (8192 * m + 2075) < 8192 * m + 2075
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 3483 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 3483) = 12288 * m + 5225 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 5225) = 9216 * m + 3919 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 3919) = 13824 * m + 5879 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 5879) = 20736 * m + 8819 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 8819) = 31104 * m + 13229 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 13229) = 11664 * m + 4961 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 4961) = 8748 * m + 3721 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (8748 * m + 3721) ≤ 6561 * m + 2791 :=
      step_le 2 (by ring)
    change (syracuseStep^[8]) (8192 * m + 3483) < 8192 * m + 3483
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 3835 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 3835) = 12288 * m + 5753 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 5753) = 9216 * m + 4315 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 4315) = 13824 * m + 6473 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 6473) = 10368 * m + 4855 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 4855) = 15552 * m + 7283 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 7283) = 23328 * m + 10925 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 10925) = 8748 * m + 4097 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (8748 * m + 4097) ≤ 6561 * m + 3073 :=
      step_le 2 (by ring)
    change (syracuseStep^[8]) (8192 * m + 3835) < 8192 * m + 3835
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 4507 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 4507) = 12288 * m + 6761 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 6761) = 9216 * m + 5071 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 5071) = 13824 * m + 7607 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 7607) = 20736 * m + 11411 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 11411) = 31104 * m + 17117 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 17117) = 11664 * m + 6419 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 6419) = 17496 * m + 9629 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (17496 * m + 9629) ≤ 6561 * m + 3611 :=
      step_le 3 (by ring)
    change (syracuseStep^[8]) (8192 * m + 4507) < 8192 * m + 4507
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 4859 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 4859) = 12288 * m + 7289 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 7289) = 9216 * m + 5467 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 5467) = 13824 * m + 8201 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 8201) = 10368 * m + 6151 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 6151) = 15552 * m + 9227 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 9227) = 23328 * m + 13841 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 13841) = 17496 * m + 10381 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (17496 * m + 10381) ≤ 6561 * m + 3893 :=
      step_le 3 (by ring)
    change (syracuseStep^[8]) (8192 * m + 4859) < 8192 * m + 4859
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 5371 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 5371) = 12288 * m + 8057 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 8057) = 9216 * m + 6043 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 6043) = 13824 * m + 9065 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 9065) = 10368 * m + 6799 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 6799) = 15552 * m + 10199 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 10199) = 23328 * m + 15299 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 15299) = 34992 * m + 22949 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (34992 * m + 22949) ≤ 6561 * m + 4303 :=
      step_le 4 (by ring)
    change (syracuseStep^[8]) (8192 * m + 5371) < 8192 * m + 5371
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 5723 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 5723) = 12288 * m + 8585 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 8585) = 9216 * m + 6439 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 6439) = 13824 * m + 9659 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 9659) = 20736 * m + 14489 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 14489) = 15552 * m + 10867 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 10867) = 23328 * m + 16301 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 16301) = 8748 * m + 6113 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (8748 * m + 6113) ≤ 6561 * m + 4585 :=
      step_le 2 (by ring)
    change (syracuseStep^[8]) (8192 * m + 5723) < 8192 * m + 5723
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 6747 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 6747) = 12288 * m + 10121 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 10121) = 9216 * m + 7591 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 7591) = 13824 * m + 11387 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 11387) = 20736 * m + 17081 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 17081) = 15552 * m + 12811 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 12811) = 23328 * m + 19217 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 19217) = 17496 * m + 14413 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (17496 * m + 14413) ≤ 6561 * m + 5405 :=
      step_le 3 (by ring)
    change (syracuseStep^[8]) (8192 * m + 6747) < 8192 * m + 6747
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 7259 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 7259) = 12288 * m + 10889 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 10889) = 9216 * m + 8167 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 8167) = 13824 * m + 12251 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 12251) = 20736 * m + 18377 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 18377) = 15552 * m + 13783 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 13783) = 23328 * m + 20675 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 20675) = 34992 * m + 31013 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (34992 * m + 31013) ≤ 6561 * m + 5815 :=
      step_le 4 (by ring)
    change (syracuseStep^[8]) (8192 * m + 7259) < 8192 * m + 7259
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
