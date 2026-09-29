-- Prove2me | solution 1 for syracuse_descent_progressions_twentyseven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:14:44.249666+00:00
-- url     : https://prove2.me/submissions/f78cbadb-7386-4f2b-9fa9-35059a194b8c

import Mathlib
import Definitions.Def_syracuseStep

open Nat

/-- If `3 * x + 1 = 2 ^ a * y` with `y` odd, then `y` is exactly the odd part of `3 * x + 1`. -/
theorem step_eq (a : ℕ) {x y : ℕ} (h : 3 * x + 1 = 2 ^ a * y) (hy : Odd y) :
    syracuseStep x = y := by
  have hy0 : y ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hy
  have hfac : (3 * x + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hy0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * x + 1) = y
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

/-- Truncated step: knowing only `2 ^ a ∣ 3 * x + 1` still bounds the odd part from above. -/
theorem step_le (a : ℕ) {x y : ℕ} (h : 3 * x + 1 = 2 ^ a * y) : syracuseStep x ≤ y := by
  have hne : 3 * x + 1 ≠ 0 := by omega
  have hle : a ≤ (3 * x + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 ⟨y, h⟩
  show ordCompl[2] (3 * x + 1) ≤ y
  calc (3 * x + 1) / 2 ^ ((3 * x + 1).factorization 2)
      ≤ (3 * x + 1) / 2 ^ a :=
        Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hle) (by positivity)
    _ = y := by rw [h, Nat.mul_div_cancel_left _ (by positivity)]

theorem solution (n : ℕ)
    (h : n % 128 = 59 ∨
      n % 256 = 123 ∨
      n % 256 = 219 ∨
      n % 1024 = 347 ∨
      n % 1024 = 507 ∨
      n % 1024 = 923 ∨
      n % 4096 = 1019 ∨
      n % 4096 = 1435 ∨
      n % 4096 = 1787 ∨
      n % 4096 = 2203 ∨
      n % 4096 = 2587 ∨
      n % 4096 = 2907 ∨
      n % 4096 = 3675) :
    ∃ t : ℕ, t ≤ 7 ∧ syracuseStep^[t] n < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨m, hm⟩ : ∃ m, n = 128 * m + 59 := ⟨n / 128, by omega⟩
    subst hm
    refine ⟨4, by norm_num, ?_⟩
    have e1 : syracuseStep (128 * m + 59) = 192 * m + 89 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (192 * m + 89) = 144 * m + 67 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (144 * m + 67) = 216 * m + 101 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (216 * m + 101) ≤ 81 * m + 38 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (128 * m + 59)))) < 128 * m + 59
    rw [e1, e2, e3]
    exact lt_of_le_of_lt e4 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 256 * m + 123 := ⟨n / 256, by omega⟩
    subst hm
    refine ⟨5, by norm_num, ?_⟩
    have e1 : syracuseStep (256 * m + 123) = 384 * m + 185 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (384 * m + 185) = 288 * m + 139 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (288 * m + 139) = 432 * m + 209 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (432 * m + 209) = 324 * m + 157 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (324 * m + 157) ≤ 243 * m + 118 := step_le 2 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (256 * m + 123))))) < 256 * m + 123
    rw [e1, e2, e3, e4]
    exact lt_of_le_of_lt e5 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 256 * m + 219 := ⟨n / 256, by omega⟩
    subst hm
    refine ⟨5, by norm_num, ?_⟩
    have e1 : syracuseStep (256 * m + 219) = 384 * m + 329 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (384 * m + 329) = 288 * m + 247 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (288 * m + 247) = 432 * m + 371 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (432 * m + 371) = 648 * m + 557 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (648 * m + 557) ≤ 243 * m + 209 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (256 * m + 219))))) < 256 * m + 219
    rw [e1, e2, e3, e4]
    exact lt_of_le_of_lt e5 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 347 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 347) = 1536 * m + 521 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 521) = 1152 * m + 391 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (1152 * m + 391) = 1728 * m + 587 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (1728 * m + 587) = 2592 * m + 881 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (2592 * m + 881) = 1944 * m + 661 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (1944 * m + 661) ≤ 729 * m + 248 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 347)))))) < 1024 * m + 347
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 507 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 507) = 1536 * m + 761 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 761) = 1152 * m + 571 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (1152 * m + 571) = 1728 * m + 857 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (1728 * m + 857) = 1296 * m + 643 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (1296 * m + 643) = 1944 * m + 965 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (1944 * m + 965) ≤ 729 * m + 362 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 507)))))) < 1024 * m + 507
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 923 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 923) = 1536 * m + 1385 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 1385) = 1152 * m + 1039 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (1152 * m + 1039) = 1728 * m + 1559 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (1728 * m + 1559) = 2592 * m + 2339 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (2592 * m + 2339) = 3888 * m + 3509 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (3888 * m + 3509) ≤ 729 * m + 658 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 923)))))) < 1024 * m + 923
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1019 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1019) = 6144 * m + 1529 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 1529) = 4608 * m + 1147 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (4608 * m + 1147) = 6912 * m + 1721 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (6912 * m + 1721) = 5184 * m + 1291 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (5184 * m + 1291) = 7776 * m + 1937 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 1937) = 5832 * m + 1453 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 1453) ≤ 2187 * m + 545 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1019))))))) < 4096 * m + 1019
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1435 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1435) = 6144 * m + 2153 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 2153) = 4608 * m + 1615 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (4608 * m + 1615) = 6912 * m + 2423 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (6912 * m + 2423) = 10368 * m + 3635 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 3635) = 15552 * m + 5453 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 5453) = 5832 * m + 2045 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 2045) ≤ 2187 * m + 767 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1435))))))) < 4096 * m + 1435
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1787 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1787) = 6144 * m + 2681 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 2681) = 4608 * m + 2011 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (4608 * m + 2011) = 6912 * m + 3017 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (6912 * m + 3017) = 5184 * m + 2263 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (5184 * m + 2263) = 7776 * m + 3395 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 3395) = 11664 * m + 5093 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 5093) ≤ 2187 * m + 955 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1787))))))) < 4096 * m + 1787
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2203 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2203) = 6144 * m + 3305 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 3305) = 4608 * m + 2479 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (4608 * m + 2479) = 6912 * m + 3719 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (6912 * m + 3719) = 10368 * m + 5579 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 5579) = 15552 * m + 8369 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 8369) = 11664 * m + 6277 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 6277) ≤ 2187 * m + 1177 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2203))))))) < 4096 * m + 2203
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2587 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2587) = 6144 * m + 3881 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 3881) = 4608 * m + 2911 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (4608 * m + 2911) = 6912 * m + 4367 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (6912 * m + 4367) = 10368 * m + 6551 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 6551) = 15552 * m + 9827 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 9827) = 23328 * m + 14741 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 14741) ≤ 2187 * m + 1382 := step_le 5 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2587))))))) < 4096 * m + 2587
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2907 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2907) = 6144 * m + 4361 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 4361) = 4608 * m + 3271 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (4608 * m + 3271) = 6912 * m + 4907 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (6912 * m + 4907) = 10368 * m + 7361 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 7361) = 7776 * m + 5521 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 5521) = 5832 * m + 4141 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 4141) ≤ 2187 * m + 1553 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2907))))))) < 4096 * m + 2907
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 3675 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 3675) = 6144 * m + 5513 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 5513) = 4608 * m + 4135 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (4608 * m + 4135) = 6912 * m + 6203 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (6912 * m + 6203) = 10368 * m + 9305 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 9305) = 7776 * m + 6979 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 6979) = 11664 * m + 10469 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 10469) ≤ 2187 * m + 1963 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 3675))))))) < 4096 * m + 3675
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
