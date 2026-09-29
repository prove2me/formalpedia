-- Prove2me | solution 1 for syracuse_descent_progressions_fifteen_mod16
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:14:44.742048+00:00
-- url     : https://prove2.me/submissions/90748013-f66a-4845-bf45-665744846ad5

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
    (h : n % 128 = 15 ∨
      n % 256 = 79 ∨
      n % 256 = 95 ∨
      n % 256 = 175 ∨
      n % 1024 = 287 ∨
      n % 1024 = 367 ∨
      n % 1024 = 575 ∨
      n % 1024 = 735 ∨
      n % 1024 = 815 ∨
      n % 1024 = 975 ∨
      n % 4096 = 383 ∨
      n % 4096 = 463 ∨
      n % 4096 = 879 ∨
      n % 4096 = 1087 ∨
      n % 4096 = 1231 ∨
      n % 4096 = 1647 ∨
      n % 4096 = 1823 ∨
      n % 4096 = 1855 ∨
      n % 4096 = 2031 ∨
      n % 4096 = 2239 ∨
      n % 4096 = 2351 ∨
      n % 4096 = 2591 ∨
      n % 4096 = 2975 ∨
      n % 4096 = 3119 ∨
      n % 4096 = 3295 ∨
      n % 4096 = 4063) :
    ∃ t : ℕ, t ≤ 7 ∧ syracuseStep^[t] n < n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨m, hm⟩ : ∃ m, n = 128 * m + 15 := ⟨n / 128, by omega⟩
    subst hm
    refine ⟨4, by norm_num, ?_⟩
    have e1 : syracuseStep (128 * m + 15) = 192 * m + 23 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (192 * m + 23) = 288 * m + 35 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (288 * m + 35) = 432 * m + 53 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (432 * m + 53) ≤ 81 * m + 10 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (128 * m + 15)))) < 128 * m + 15
    rw [e1, e2, e3]
    exact lt_of_le_of_lt e4 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 256 * m + 79 := ⟨n / 256, by omega⟩
    subst hm
    refine ⟨5, by norm_num, ?_⟩
    have e1 : syracuseStep (256 * m + 79) = 384 * m + 119 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (384 * m + 119) = 576 * m + 179 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (576 * m + 179) = 864 * m + 269 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (864 * m + 269) = 324 * m + 101 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (324 * m + 101) ≤ 243 * m + 76 := step_le 2 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (256 * m + 79))))) < 256 * m + 79
    rw [e1, e2, e3, e4]
    exact lt_of_le_of_lt e5 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 256 * m + 95 := ⟨n / 256, by omega⟩
    subst hm
    refine ⟨5, by norm_num, ?_⟩
    have e1 : syracuseStep (256 * m + 95) = 384 * m + 143 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (384 * m + 143) = 576 * m + 215 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (576 * m + 215) = 864 * m + 323 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (864 * m + 323) = 1296 * m + 485 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (1296 * m + 485) ≤ 243 * m + 91 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (256 * m + 95))))) < 256 * m + 95
    rw [e1, e2, e3, e4]
    exact lt_of_le_of_lt e5 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 256 * m + 175 := ⟨n / 256, by omega⟩
    subst hm
    refine ⟨5, by norm_num, ?_⟩
    have e1 : syracuseStep (256 * m + 175) = 384 * m + 263 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (384 * m + 263) = 576 * m + 395 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (576 * m + 395) = 864 * m + 593 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (864 * m + 593) = 648 * m + 445 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (648 * m + 445) ≤ 243 * m + 167 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (256 * m + 175))))) < 256 * m + 175
    rw [e1, e2, e3, e4]
    exact lt_of_le_of_lt e5 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 287 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 287) = 1536 * m + 431 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 431) = 2304 * m + 647 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (2304 * m + 647) = 3456 * m + 971 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (3456 * m + 971) = 5184 * m + 1457 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (5184 * m + 1457) = 3888 * m + 1093 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (3888 * m + 1093) ≤ 729 * m + 205 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 287)))))) < 1024 * m + 287
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 367 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 367) = 1536 * m + 551 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 551) = 2304 * m + 827 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (2304 * m + 827) = 3456 * m + 1241 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (3456 * m + 1241) = 2592 * m + 931 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (2592 * m + 931) = 3888 * m + 1397 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (3888 * m + 1397) ≤ 729 * m + 262 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 367)))))) < 1024 * m + 367
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 575 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 575) = 1536 * m + 863 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 863) = 2304 * m + 1295 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (2304 * m + 1295) = 3456 * m + 1943 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (3456 * m + 1943) = 5184 * m + 2915 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (5184 * m + 2915) = 7776 * m + 4373 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 4373) ≤ 729 * m + 410 := step_le 5 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 575)))))) < 1024 * m + 575
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 735 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 735) = 1536 * m + 1103 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 1103) = 2304 * m + 1655 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (2304 * m + 1655) = 3456 * m + 2483 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (3456 * m + 2483) = 5184 * m + 3725 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (5184 * m + 3725) = 1944 * m + 1397 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (1944 * m + 1397) ≤ 729 * m + 524 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 735)))))) < 1024 * m + 735
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 815 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 815) = 1536 * m + 1223 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 1223) = 2304 * m + 1835 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (2304 * m + 1835) = 3456 * m + 2753 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (3456 * m + 2753) = 2592 * m + 2065 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (2592 * m + 2065) = 1944 * m + 1549 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (1944 * m + 1549) ≤ 729 * m + 581 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 815)))))) < 1024 * m + 815
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 1024 * m + 975 := ⟨n / 1024, by omega⟩
    subst hm
    refine ⟨6, by norm_num, ?_⟩
    have e1 : syracuseStep (1024 * m + 975) = 1536 * m + 1463 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (1536 * m + 1463) = 2304 * m + 2195 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (2304 * m + 2195) = 3456 * m + 3293 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (3456 * m + 3293) = 1296 * m + 1235 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (1296 * m + 1235) = 1944 * m + 1853 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (1944 * m + 1853) ≤ 729 * m + 695 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (1024 * m + 975)))))) < 1024 * m + 975
    rw [e1, e2, e3, e4, e5]
    exact lt_of_le_of_lt e6 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 383 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 383) = 6144 * m + 575 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 575) = 9216 * m + 863 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 863) = 13824 * m + 1295 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 1295) = 20736 * m + 1943 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 1943) = 31104 * m + 2915 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 2915) = 46656 * m + 4373 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (46656 * m + 4373) ≤ 2187 * m + 205 := step_le 6 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 383))))))) < 4096 * m + 383
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 463 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 463) = 6144 * m + 695 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 695) = 9216 * m + 1043 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 1043) = 13824 * m + 1565 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 1565) = 5184 * m + 587 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (5184 * m + 587) = 7776 * m + 881 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 881) = 5832 * m + 661 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 661) ≤ 2187 * m + 248 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 463))))))) < 4096 * m + 463
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 879 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 879) = 6144 * m + 1319 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 1319) = 9216 * m + 1979 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 1979) = 13824 * m + 2969 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 2969) = 10368 * m + 2227 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 2227) = 15552 * m + 3341 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 3341) = 5832 * m + 1253 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 1253) ≤ 2187 * m + 470 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 879))))))) < 4096 * m + 879
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1087 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1087) = 6144 * m + 1631 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 1631) = 9216 * m + 2447 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 2447) = 13824 * m + 3671 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 3671) = 20736 * m + 5507 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 5507) = 31104 * m + 8261 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 8261) = 5832 * m + 1549 :=
      step_eq 4 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 1549) ≤ 2187 * m + 581 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1087))))))) < 4096 * m + 1087
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1231 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1231) = 6144 * m + 1847 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 1847) = 9216 * m + 2771 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 2771) = 13824 * m + 4157 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 4157) = 5184 * m + 1559 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (5184 * m + 1559) = 7776 * m + 2339 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 2339) = 11664 * m + 3509 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 3509) ≤ 2187 * m + 658 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1231))))))) < 4096 * m + 1231
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1647 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1647) = 6144 * m + 2471 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 2471) = 9216 * m + 3707 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 3707) = 13824 * m + 5561 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 5561) = 10368 * m + 4171 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 4171) = 15552 * m + 6257 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 6257) = 11664 * m + 4693 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 4693) ≤ 2187 * m + 880 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1647))))))) < 4096 * m + 1647
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1823 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1823) = 6144 * m + 2735 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 2735) = 9216 * m + 4103 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 4103) = 13824 * m + 6155 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 6155) = 20736 * m + 9233 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 9233) = 15552 * m + 6925 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 6925) = 5832 * m + 2597 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 2597) ≤ 2187 * m + 974 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1823))))))) < 4096 * m + 1823
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 1855 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 1855) = 6144 * m + 2783 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 2783) = 9216 * m + 4175 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 4175) = 13824 * m + 6263 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 6263) = 20736 * m + 9395 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 9395) = 31104 * m + 14093 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 14093) = 11664 * m + 5285 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 5285) ≤ 2187 * m + 991 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 1855))))))) < 4096 * m + 1855
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2031 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2031) = 6144 * m + 3047 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 3047) = 9216 * m + 4571 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 4571) = 13824 * m + 6857 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 6857) = 10368 * m + 5143 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 5143) = 15552 * m + 7715 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 7715) = 23328 * m + 11573 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 11573) ≤ 2187 * m + 1085 := step_le 5 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2031))))))) < 4096 * m + 2031
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2239 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2239) = 6144 * m + 3359 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 3359) = 9216 * m + 5039 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 5039) = 13824 * m + 7559 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 7559) = 20736 * m + 11339 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 11339) = 31104 * m + 17009 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (31104 * m + 17009) = 23328 * m + 12757 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 12757) ≤ 2187 * m + 1196 := step_le 5 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2239))))))) < 4096 * m + 2239
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2351 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2351) = 6144 * m + 3527 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 3527) = 9216 * m + 5291 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 5291) = 13824 * m + 7937 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 7937) = 10368 * m + 5953 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 5953) = 7776 * m + 4465 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 4465) = 5832 * m + 3349 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 3349) ≤ 2187 * m + 1256 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2351))))))) < 4096 * m + 2351
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2591 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2591) = 6144 * m + 3887 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 3887) = 9216 * m + 5831 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 5831) = 13824 * m + 8747 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 8747) = 20736 * m + 13121 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 13121) = 15552 * m + 9841 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 9841) = 11664 * m + 7381 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 7381) ≤ 2187 * m + 1384 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2591))))))) < 4096 * m + 2591
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 2975 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 2975) = 6144 * m + 4463 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 4463) = 9216 * m + 6695 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 6695) = 13824 * m + 10043 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 10043) = 20736 * m + 15065 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 15065) = 15552 * m + 11299 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (15552 * m + 11299) = 23328 * m + 16949 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (23328 * m + 16949) ≤ 2187 * m + 1589 := step_le 5 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 2975))))))) < 4096 * m + 2975
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 3119 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 3119) = 6144 * m + 4679 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 4679) = 9216 * m + 7019 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 7019) = 13824 * m + 10529 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 10529) = 10368 * m + 7897 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (10368 * m + 7897) = 7776 * m + 5923 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 5923) = 11664 * m + 8885 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 8885) ≤ 2187 * m + 1666 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 3119))))))) < 4096 * m + 3119
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 3295 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 3295) = 6144 * m + 4943 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 4943) = 9216 * m + 7415 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 7415) = 13824 * m + 11123 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 11123) = 20736 * m + 16685 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 16685) = 7776 * m + 6257 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 6257) = 5832 * m + 4693 :=
      step_eq 2 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (5832 * m + 4693) ≤ 2187 * m + 1760 := step_le 3 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 3295))))))) < 4096 * m + 3295
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
  · obtain ⟨m, hm⟩ : ∃ m, n = 4096 * m + 4063 := ⟨n / 4096, by omega⟩
    subst hm
    refine ⟨7, by norm_num, ?_⟩
    have e1 : syracuseStep (4096 * m + 4063) = 6144 * m + 6095 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e2 : syracuseStep (6144 * m + 6095) = 9216 * m + 9143 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e3 : syracuseStep (9216 * m + 9143) = 13824 * m + 13715 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e4 : syracuseStep (13824 * m + 13715) = 20736 * m + 20573 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e5 : syracuseStep (20736 * m + 20573) = 7776 * m + 7715 :=
      step_eq 3 (by ring) (by rw [Nat.odd_iff]; omega)
    have e6 : syracuseStep (7776 * m + 7715) = 11664 * m + 11573 :=
      step_eq 1 (by ring) (by rw [Nat.odd_iff]; omega)
    have e7 : syracuseStep (11664 * m + 11573) ≤ 2187 * m + 2170 := step_le 4 (by ring)
    show syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (4096 * m + 4063))))))) < 4096 * m + 4063
    rw [e1, e2, e3, e4, e5, e6]
    exact lt_of_le_of_lt e7 (by omega)
