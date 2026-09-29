-- Prove2me | solution 1 for syracuse_descent_eight_more_progressions_twentyseven_mod32_mod8192
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T19:42:46.62465+00:00
-- url     : https://prove2.me/submissions/6005005f-9366-42d3-9549-244b27ea4350

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

/-- Eight further 27-mod-32 progressions with eight-step affine descent. -/
theorem solution (n : ℕ)
    (h : n % 8192 = 2331 ∨ n % 8192 = 3067 ∨ n % 8192 = 4091 ∨ n % 8192 = 4251 ∨ n % 8192 = 4955 ∨ n % 8192 = 5275 ∨ n % 8192 = 5787 ∨ n % 8192 = 5979) :
    ∃ t : ℕ, t ≤ 8 ∧ syracuseStep^[t] n < n := by
  rcases h with h | h | h | h | h | h | h | h
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 2331 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 2331) = 12288 * m + 3497 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 3497) = 9216 * m + 2623 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 2623) = 13824 * m + 3935 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 3935) = 20736 * m + 5903 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 5903) = 31104 * m + 8855 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 8855) = 46656 * m + 13283 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (46656 * m + 13283) = 69984 * m + 19925 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (69984 * m + 19925) ≤ 6561 * m + 1868 :=
      step_le 5 (by ring)
    change (syracuseStep^[8]) (8192 * m + 2331) < 8192 * m + 2331
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 3067 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 3067) = 12288 * m + 4601 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 4601) = 9216 * m + 3451 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 3451) = 13824 * m + 5177 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 5177) = 10368 * m + 3883 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 3883) = 15552 * m + 5825 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 5825) = 11664 * m + 4369 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 4369) = 8748 * m + 3277 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (8748 * m + 3277) ≤ 6561 * m + 2458 :=
      step_le 2 (by ring)
    change (syracuseStep^[8]) (8192 * m + 3067) < 8192 * m + 3067
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 4091 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 4091) = 12288 * m + 6137 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 6137) = 9216 * m + 4603 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 4603) = 13824 * m + 6905 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 6905) = 10368 * m + 5179 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 5179) = 15552 * m + 7769 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 7769) = 11664 * m + 5827 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 5827) = 17496 * m + 8741 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (17496 * m + 8741) ≤ 6561 * m + 3278 :=
      step_le 3 (by ring)
    change (syracuseStep^[8]) (8192 * m + 4091) < 8192 * m + 4091
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 4251 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 4251) = 12288 * m + 6377 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 6377) = 9216 * m + 4783 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 4783) = 13824 * m + 7175 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 7175) = 20736 * m + 10763 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 10763) = 31104 * m + 16145 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 16145) = 23328 * m + 12109 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 12109) = 8748 * m + 4541 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (8748 * m + 4541) ≤ 6561 * m + 3406 :=
      step_le 2 (by ring)
    change (syracuseStep^[8]) (8192 * m + 4251) < 8192 * m + 4251
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 4955 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 4955) = 12288 * m + 7433 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 7433) = 9216 * m + 5575 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 5575) = 13824 * m + 8363 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 8363) = 20736 * m + 12545 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 12545) = 15552 * m + 9409 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 9409) = 11664 * m + 7057 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 7057) = 8748 * m + 5293 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (8748 * m + 5293) ≤ 6561 * m + 3970 :=
      step_le 2 (by ring)
    change (syracuseStep^[8]) (8192 * m + 4955) < 8192 * m + 4955
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 5275 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 5275) = 12288 * m + 7913 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 7913) = 9216 * m + 5935 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 5935) = 13824 * m + 8903 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 8903) = 20736 * m + 13355 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 13355) = 31104 * m + 20033 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 20033) = 23328 * m + 15025 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 15025) = 17496 * m + 11269 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (17496 * m + 11269) ≤ 6561 * m + 4226 :=
      step_le 3 (by ring)
    change (syracuseStep^[8]) (8192 * m + 5275) < 8192 * m + 5275
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 5787 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 5787) = 12288 * m + 8681 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 8681) = 9216 * m + 6511 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 6511) = 13824 * m + 9767 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 9767) = 20736 * m + 14651 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 14651) = 31104 * m + 21977 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 21977) = 23328 * m + 16483 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 16483) = 34992 * m + 24725 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (34992 * m + 24725) ≤ 6561 * m + 4636 :=
      step_le 4 (by ring)
    change (syracuseStep^[8]) (8192 * m + 5787) < 8192 * m + 5787
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 8192 * m + 5979 := ⟨n / 8192, by omega⟩
    subst hm
    refine ⟨8, by norm_num, ?_⟩
    have e1 : syracuseStep (8192 * m + 5979) = 12288 * m + 8969 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (12288 * m + 8969) = 9216 * m + 6727 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 6727) = 13824 * m + 10091 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 10091) = 20736 * m + 15137 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 15137) = 15552 * m + 11353 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 11353) = 11664 * m + 8515 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 8515) = 17496 * m + 12773 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e8 : syracuseStep (17496 * m + 12773) ≤ 6561 * m + 4790 :=
      step_le 3 (by ring)
    change (syracuseStep^[8]) (8192 * m + 5979) < 8192 * m + 5979
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact lt_of_le_of_lt e8 (by omega)
