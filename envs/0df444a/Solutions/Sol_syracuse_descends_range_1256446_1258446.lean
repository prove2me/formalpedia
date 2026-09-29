-- Prove2me | solution 1 for syracuse_descends_range_1256446_1258446
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:21.079781+00:00
-- url     : https://prove2.me/submissions/d1e73d9b-7331-450e-b4fb-79081891fe20

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B2547757 : Blo 1256446 2547757 := bbase (se 3 (by rfl) ⟨477704, by rfl⟩ : syracuseStep 2547757 = 955409) (by norm_num)
theorem B2121781 : Blo 1256446 2121781 := bbase (se 5 (by rfl) ⟨99458, by rfl⟩ : syracuseStep 2121781 = 198917) (by norm_num)
theorem B2015317 : Blo 1256446 2015317 := bbase (se 8 (by rfl) ⟨11808, by rfl⟩ : syracuseStep 2015317 = 23617) (by norm_num)
theorem B4243589 : Blo 1256446 4243589 := bbase (se 4 (by rfl) ⟨397836, by rfl⟩ : syracuseStep 4243589 = 795673) (by norm_num)
theorem B2121869 : Blo 1256446 2121869 := bbase (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) (by norm_num)
theorem B2015381 : Blo 1256446 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B1532101 : Blo 1256446 1532101 := bbase (se 4 (by rfl) ⟨143634, by rfl⟩ : syracuseStep 1532101 = 287269) (by norm_num)
theorem B1343737 : Blo 1256446 1343737 := bbase (se 2 (by rfl) ⟨503901, by rfl⟩ : syracuseStep 1343737 = 1007803) (by norm_num)
theorem B2121997 : Blo 1256446 2121997 := bbase (se 3 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 2121997 = 795749) (by norm_num)
theorem B8053013 : Blo 1256446 8053013 := bbase (se 6 (by rfl) ⟨188742, by rfl⟩ : syracuseStep 8053013 = 377485) (by norm_num)
theorem B2015509 : Blo 1256446 2015509 := bbase (se 6 (by rfl) ⟨47238, by rfl⟩ : syracuseStep 2015509 = 94477) (by norm_num)
theorem B4301093 : Blo 1256446 4301093 := bbase (se 4 (by rfl) ⟨403227, by rfl⟩ : syracuseStep 4301093 = 806455) (by norm_num)
theorem B2687269 : Blo 1256446 2687269 := bbase (se 4 (by rfl) ⟨251931, by rfl⟩ : syracuseStep 2687269 = 503863) (by norm_num)
theorem B1343809 : Blo 1256446 1343809 := bbase (se 2 (by rfl) ⟨503928, by rfl⟩ : syracuseStep 1343809 = 1007857) (by norm_num)
theorem B2122085 : Blo 1256446 2122085 := bbase (se 4 (by rfl) ⟨198945, by rfl⟩ : syracuseStep 2122085 = 397891) (by norm_num)
theorem B3580325 : Blo 1256446 3580325 := bbase (se 4 (by rfl) ⟨335655, by rfl⟩ : syracuseStep 3580325 = 671311) (by norm_num)
theorem B2687413 : Blo 1256446 2687413 := bbase (se 5 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 2687413 = 251945) (by norm_num)
theorem B2122213 : Blo 1256446 2122213 := bbase (se 4 (by rfl) ⟨198957, by rfl⟩ : syracuseStep 2122213 = 397915) (by norm_num)
theorem B9814517 : Blo 1256446 9814517 := bbase (se 5 (by rfl) ⟨460055, by rfl⟩ : syracuseStep 9814517 = 920111) (by norm_num)
theorem B1884677 : Blo 1256446 1884677 := bbase (se 4 (by rfl) ⟨176688, by rfl⟩ : syracuseStep 1884677 = 353377) (by norm_num)
theorem B1884701 : Blo 1256446 1884701 := bbase (se 3 (by rfl) ⟨353381, by rfl⟩ : syracuseStep 1884701 = 706763) (by norm_num)
theorem B1884725 : Blo 1256446 1884725 := bbase (se 5 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 1884725 = 176693) (by norm_num)
theorem B2548277 : Blo 1256446 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B4244021 : Blo 1256446 4244021 := bbase (se 5 (by rfl) ⟨198938, by rfl⟩ : syracuseStep 4244021 = 397877) (by norm_num)
theorem B2122301 : Blo 1256446 2122301 := bbase (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) (by norm_num)
theorem B1884749 : Blo 1256446 1884749 := bbase (se 3 (by rfl) ⟨353390, by rfl⟩ : syracuseStep 1884749 = 706781) (by norm_num)
theorem B1884773 : Blo 1256446 1884773 := bbase (se 4 (by rfl) ⟨176697, by rfl⟩ : syracuseStep 1884773 = 353395) (by norm_num)
theorem B1884797 : Blo 1256446 1884797 := bbase (se 3 (by rfl) ⟨353399, by rfl⟩ : syracuseStep 1884797 = 706799) (by norm_num)
theorem B1884821 : Blo 1256446 1884821 := bbase (se 6 (by rfl) ⟨44175, by rfl⟩ : syracuseStep 1884821 = 88351) (by norm_num)
theorem B1884845 : Blo 1256446 1884845 := bbase (se 3 (by rfl) ⟨353408, by rfl⟩ : syracuseStep 1884845 = 706817) (by norm_num)
theorem B2122429 : Blo 1256446 2122429 := bbase (se 3 (by rfl) ⟨397955, by rfl⟩ : syracuseStep 2122429 = 795911) (by norm_num)
theorem B1434305 : Blo 1256446 1434305 := bbase (se 2 (by rfl) ⟨537864, by rfl⟩ : syracuseStep 1434305 = 1075729) (by norm_num)
theorem B1884869 : Blo 1256446 1884869 := bbase (se 4 (by rfl) ⟨176706, by rfl⟩ : syracuseStep 1884869 = 353413) (by norm_num)
theorem B1884893 : Blo 1256446 1884893 := bbase (se 3 (by rfl) ⟨353417, by rfl⟩ : syracuseStep 1884893 = 706835) (by norm_num)
theorem B4530917 : Blo 1256446 4530917 := bbase (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) (by norm_num)
theorem B1884917 : Blo 1256446 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B1884941 : Blo 1256446 1884941 := bbase (se 3 (by rfl) ⟨353426, by rfl⟩ : syracuseStep 1884941 = 706853) (by norm_num)
theorem B2122517 : Blo 1256446 2122517 := bbase (se 6 (by rfl) ⟨49746, by rfl⟩ : syracuseStep 2122517 = 99493) (by norm_num)
theorem B1884965 : Blo 1256446 1884965 := bbase (se 4 (by rfl) ⟨176715, by rfl⟩ : syracuseStep 1884965 = 353431) (by norm_num)
theorem B2827061 : Blo 1256446 2827061 := bbase (se 5 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 2827061 = 265037) (by norm_num)
theorem B1884989 : Blo 1256446 1884989 := bbase (se 3 (by rfl) ⟨353435, by rfl⟩ : syracuseStep 1884989 = 706871) (by norm_num)
theorem B1885013 : Blo 1256446 1885013 := bbase (se 9 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 1885013 = 11045) (by norm_num)
theorem B3580757 : Blo 1256446 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B1885037 : Blo 1256446 1885037 := bbase (se 3 (by rfl) ⟨353444, by rfl⟩ : syracuseStep 1885037 = 706889) (by norm_num)
theorem B2827133 : Blo 1256446 2827133 := bbase (se 3 (by rfl) ⟨530087, by rfl⟩ : syracuseStep 2827133 = 1060175) (by norm_num)
theorem B1885061 : Blo 1256446 1885061 := bbase (se 4 (by rfl) ⟨176724, by rfl⟩ : syracuseStep 1885061 = 353449) (by norm_num)
theorem B1434505 : Blo 1256446 1434505 := bbase (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) (by norm_num)
theorem B2122645 : Blo 1256446 2122645 := bbase (se 6 (by rfl) ⟨49749, by rfl⟩ : syracuseStep 2122645 = 99499) (by norm_num)
theorem B1885085 : Blo 1256446 1885085 := bbase (se 3 (by rfl) ⟨353453, by rfl⟩ : syracuseStep 1885085 = 706907) (by norm_num)
theorem B1885109 : Blo 1256446 1885109 := bbase (se 5 (by rfl) ⟨88364, by rfl⟩ : syracuseStep 1885109 = 176729) (by norm_num)
theorem B2827205 : Blo 1256446 2827205 := bbase (se 4 (by rfl) ⟨265050, by rfl⟩ : syracuseStep 2827205 = 530101) (by norm_num)
theorem B1885133 : Blo 1256446 1885133 := bbase (se 3 (by rfl) ⟨353462, by rfl⟩ : syracuseStep 1885133 = 706925) (by norm_num)
theorem B1885157 : Blo 1256446 1885157 := bbase (se 4 (by rfl) ⟨176733, by rfl⟩ : syracuseStep 1885157 = 353467) (by norm_num)
theorem B4244453 : Blo 1256446 4244453 := bbase (se 4 (by rfl) ⟨397917, by rfl⟩ : syracuseStep 4244453 = 795835) (by norm_num)
theorem B2122733 : Blo 1256446 2122733 := bbase (se 3 (by rfl) ⟨398012, by rfl⟩ : syracuseStep 2122733 = 796025) (by norm_num)
theorem B1885181 : Blo 1256446 1885181 := bbase (se 3 (by rfl) ⟨353471, by rfl⟩ : syracuseStep 1885181 = 706943) (by norm_num)
theorem B2827277 : Blo 1256446 2827277 := bbase (se 3 (by rfl) ⟨530114, by rfl⟩ : syracuseStep 2827277 = 1060229) (by norm_num)
theorem B1590293 : Blo 1256446 1590293 := bbase (se 6 (by rfl) ⟨37272, by rfl⟩ : syracuseStep 1590293 = 74545) (by norm_num)
theorem B1885205 : Blo 1256446 1885205 := bbase (se 6 (by rfl) ⟨44184, by rfl⟩ : syracuseStep 1885205 = 88369) (by norm_num)
theorem B1885229 : Blo 1256446 1885229 := bbase (se 3 (by rfl) ⟨353480, by rfl⟩ : syracuseStep 1885229 = 706961) (by norm_num)
theorem B1885253 : Blo 1256446 1885253 := bbase (se 4 (by rfl) ⟨176742, by rfl⟩ : syracuseStep 1885253 = 353485) (by norm_num)
theorem B1590349 : Blo 1256446 1590349 := bbase (se 3 (by rfl) ⟨298190, by rfl⟩ : syracuseStep 1590349 = 596381) (by norm_num)
theorem B2827349 : Blo 1256446 2827349 := bbase (se 8 (by rfl) ⟨16566, by rfl⟩ : syracuseStep 2827349 = 33133) (by norm_num)
theorem B1885277 : Blo 1256446 1885277 := bbase (se 3 (by rfl) ⟨353489, by rfl⟩ : syracuseStep 1885277 = 706979) (by norm_num)
theorem B2122861 : Blo 1256446 2122861 := bbase (se 3 (by rfl) ⟨398036, by rfl⟩ : syracuseStep 2122861 = 796073) (by norm_num)
theorem B1885301 : Blo 1256446 1885301 := bbase (se 5 (by rfl) ⟨88373, by rfl⟩ : syracuseStep 1885301 = 176747) (by norm_num)
theorem B1885325 : Blo 1256446 1885325 := bbase (se 3 (by rfl) ⟨353498, by rfl⟩ : syracuseStep 1885325 = 706997) (by norm_num)
theorem B2827421 : Blo 1256446 2827421 := bbase (se 3 (by rfl) ⟨530141, by rfl⟩ : syracuseStep 2827421 = 1060283) (by norm_num)
theorem B1885349 : Blo 1256446 1885349 := bbase (se 4 (by rfl) ⟨176751, by rfl⟩ : syracuseStep 1885349 = 353503) (by norm_num)
theorem B1590445 : Blo 1256446 1590445 := bbase (se 3 (by rfl) ⟨298208, by rfl⟩ : syracuseStep 1590445 = 596417) (by norm_num)
theorem B1885373 : Blo 1256446 1885373 := bbase (se 3 (by rfl) ⟨353507, by rfl⟩ : syracuseStep 1885373 = 707015) (by norm_num)
theorem B2122949 : Blo 1256446 2122949 := bbase (se 4 (by rfl) ⟨199026, by rfl⟩ : syracuseStep 2122949 = 398053) (by norm_num)
theorem B1885397 : Blo 1256446 1885397 := bbase (se 7 (by rfl) ⟨22094, by rfl⟩ : syracuseStep 1885397 = 44189) (by norm_num)
theorem B2827493 : Blo 1256446 2827493 := bbase (se 4 (by rfl) ⟨265077, by rfl⟩ : syracuseStep 2827493 = 530155) (by norm_num)
theorem B6366437 : Blo 1256446 6366437 := bbase (se 4 (by rfl) ⟨596853, by rfl⟩ : syracuseStep 6366437 = 1193707) (by norm_num)
theorem B1885421 : Blo 1256446 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B2041085 : Blo 1256446 2041085 := bbase (se 3 (by rfl) ⟨382703, by rfl⟩ : syracuseStep 2041085 = 765407) (by norm_num)
theorem B1885445 : Blo 1256446 1885445 := bbase (se 4 (by rfl) ⟨176760, by rfl⟩ : syracuseStep 1885445 = 353521) (by norm_num)
theorem B1885469 : Blo 1256446 1885469 := bbase (se 3 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 1885469 = 707051) (by norm_num)
theorem B2827565 : Blo 1256446 2827565 := bbase (se 3 (by rfl) ⟨530168, by rfl⟩ : syracuseStep 2827565 = 1060337) (by norm_num)
theorem B1885493 : Blo 1256446 1885493 := bbase (se 5 (by rfl) ⟨88382, by rfl⟩ : syracuseStep 1885493 = 176765) (by norm_num)
theorem B2123077 : Blo 1256446 2123077 := bbase (se 4 (by rfl) ⟨199038, by rfl⟩ : syracuseStep 2123077 = 398077) (by norm_num)
theorem B1885517 : Blo 1256446 1885517 := bbase (se 3 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 1885517 = 707069) (by norm_num)
theorem B1590617 : Blo 1256446 1590617 := bbase (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) (by norm_num)
theorem B1885541 : Blo 1256446 1885541 := bbase (se 4 (by rfl) ⟨176769, by rfl⟩ : syracuseStep 1885541 = 353539) (by norm_num)
theorem B2827637 : Blo 1256446 2827637 := bbase (se 5 (by rfl) ⟨132545, by rfl⟩ : syracuseStep 2827637 = 265091) (by norm_num)
theorem B1885565 : Blo 1256446 1885565 := bbase (se 3 (by rfl) ⟨353543, by rfl⟩ : syracuseStep 1885565 = 707087) (by norm_num)
theorem B1590673 : Blo 1256446 1590673 := bbase (se 2 (by rfl) ⟨596502, by rfl⟩ : syracuseStep 1590673 = 1193005) (by norm_num)
theorem B1885589 : Blo 1256446 1885589 := bbase (se 6 (by rfl) ⟨44193, by rfl⟩ : syracuseStep 1885589 = 88387) (by norm_num)
theorem B4244885 : Blo 1256446 4244885 := bbase (se 6 (by rfl) ⟨99489, by rfl⟩ : syracuseStep 4244885 = 198979) (by norm_num)
theorem B9553301 : Blo 1256446 9553301 := bbase (se 6 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 9553301 = 447811) (by norm_num)
theorem B2123165 : Blo 1256446 2123165 := bbase (se 3 (by rfl) ⟨398093, by rfl⟩ : syracuseStep 2123165 = 796187) (by norm_num)
theorem B1885613 : Blo 1256446 1885613 := bbase (se 3 (by rfl) ⟨353552, by rfl⟩ : syracuseStep 1885613 = 707105) (by norm_num)
theorem B2827709 : Blo 1256446 2827709 := bbase (se 3 (by rfl) ⟨530195, by rfl⟩ : syracuseStep 2827709 = 1060391) (by norm_num)
theorem B1885637 : Blo 1256446 1885637 := bbase (se 4 (by rfl) ⟨176778, by rfl⟩ : syracuseStep 1885637 = 353557) (by norm_num)
theorem B5170645 : Blo 1256446 5170645 := bbase (se 7 (by rfl) ⟨60593, by rfl⟩ : syracuseStep 5170645 = 121187) (by norm_num)
theorem B1885661 : Blo 1256446 1885661 := bbase (se 3 (by rfl) ⟨353561, by rfl⟩ : syracuseStep 1885661 = 707123) (by norm_num)
theorem B1590769 : Blo 1256446 1590769 := bbase (se 2 (by rfl) ⟨596538, by rfl⟩ : syracuseStep 1590769 = 1193077) (by norm_num)
theorem B1885685 : Blo 1256446 1885685 := bbase (se 5 (by rfl) ⟨88391, by rfl⟩ : syracuseStep 1885685 = 176783) (by norm_num)
theorem B2827781 : Blo 1256446 2827781 := bbase (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) (by norm_num)
theorem B1885709 : Blo 1256446 1885709 := bbase (se 3 (by rfl) ⟨353570, by rfl⟩ : syracuseStep 1885709 = 707141) (by norm_num)
theorem B2123293 : Blo 1256446 2123293 := bbase (se 3 (by rfl) ⟨398117, by rfl⟩ : syracuseStep 2123293 = 796235) (by norm_num)
theorem B1885733 : Blo 1256446 1885733 := bbase (se 4 (by rfl) ⟨176787, by rfl⟩ : syracuseStep 1885733 = 353575) (by norm_num)
theorem B1885757 : Blo 1256446 1885757 := bbase (se 3 (by rfl) ⟨353579, by rfl⟩ : syracuseStep 1885757 = 707159) (by norm_num)
theorem B4531781 : Blo 1256446 4531781 := bbase (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) (by norm_num)
theorem B3581509 : Blo 1256446 3581509 := bbase (se 4 (by rfl) ⟨335766, by rfl⟩ : syracuseStep 3581509 = 671533) (by norm_num)
theorem B2827853 : Blo 1256446 2827853 := bbase (se 3 (by rfl) ⟨530222, by rfl⟩ : syracuseStep 2827853 = 1060445) (by norm_num)
theorem B1885781 : Blo 1256446 1885781 := bbase (se 8 (by rfl) ⟨11049, by rfl⟩ : syracuseStep 1885781 = 22099) (by norm_num)
theorem B4908629 : Blo 1256446 4908629 := bbase (se 8 (by rfl) ⟨28761, by rfl⟩ : syracuseStep 4908629 = 57523) (by norm_num)
theorem B1885805 : Blo 1256446 1885805 := bbase (se 3 (by rfl) ⟨353588, by rfl⟩ : syracuseStep 1885805 = 707177) (by norm_num)
theorem B2123381 : Blo 1256446 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B1885829 : Blo 1256446 1885829 := bbase (se 4 (by rfl) ⟨176796, by rfl⟩ : syracuseStep 1885829 = 353593) (by norm_num)
theorem B2827925 : Blo 1256446 2827925 := bbase (se 6 (by rfl) ⟨66279, by rfl⟩ : syracuseStep 2827925 = 132559) (by norm_num)
theorem B1590941 : Blo 1256446 1590941 := bbase (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) (by norm_num)
theorem B1885853 : Blo 1256446 1885853 := bbase (se 3 (by rfl) ⟨353597, by rfl⟩ : syracuseStep 1885853 = 707195) (by norm_num)
theorem B1885877 : Blo 1256446 1885877 := bbase (se 5 (by rfl) ⟨88400, by rfl⟩ : syracuseStep 1885877 = 176801) (by norm_num)
theorem B1885901 : Blo 1256446 1885901 := bbase (se 3 (by rfl) ⟨353606, by rfl⟩ : syracuseStep 1885901 = 707213) (by norm_num)
theorem B1590997 : Blo 1256446 1590997 := bbase (se 7 (by rfl) ⟨18644, by rfl⟩ : syracuseStep 1590997 = 37289) (by norm_num)
theorem B2827997 : Blo 1256446 2827997 := bbase (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) (by norm_num)
theorem B1885925 : Blo 1256446 1885925 := bbase (se 4 (by rfl) ⟨176805, by rfl⟩ : syracuseStep 1885925 = 353611) (by norm_num)
theorem B2123509 : Blo 1256446 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B1885949 : Blo 1256446 1885949 := bbase (se 3 (by rfl) ⟨353615, by rfl⟩ : syracuseStep 1885949 = 707231) (by norm_num)
theorem B1885973 : Blo 1256446 1885973 := bbase (se 6 (by rfl) ⟨44202, by rfl⟩ : syracuseStep 1885973 = 88405) (by norm_num)
theorem B1910557 : Blo 1256446 1910557 := bbase (se 3 (by rfl) ⟨358229, by rfl⟩ : syracuseStep 1910557 = 716459) (by norm_num)
theorem B2828069 : Blo 1256446 2828069 := bbase (se 4 (by rfl) ⟨265131, by rfl⟩ : syracuseStep 2828069 = 530263) (by norm_num)
theorem B1885997 : Blo 1256446 1885997 := bbase (se 3 (by rfl) ⟨353624, by rfl⟩ : syracuseStep 1885997 = 707249) (by norm_num)
theorem B9545525 : Blo 1256446 9545525 := bbase (se 5 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 9545525 = 894893) (by norm_num)
theorem B1591093 : Blo 1256446 1591093 := bbase (se 5 (by rfl) ⟨74582, by rfl⟩ : syracuseStep 1591093 = 149165) (by norm_num)
theorem B1886021 : Blo 1256446 1886021 := bbase (se 4 (by rfl) ⟨176814, by rfl⟩ : syracuseStep 1886021 = 353629) (by norm_num)
theorem B4245317 : Blo 1256446 4245317 := bbase (se 4 (by rfl) ⟨397998, by rfl⟩ : syracuseStep 4245317 = 795997) (by norm_num)
theorem B2123597 : Blo 1256446 2123597 := bbase (se 3 (by rfl) ⟨398174, by rfl⟩ : syracuseStep 2123597 = 796349) (by norm_num)
theorem B1886045 : Blo 1256446 1886045 := bbase (se 3 (by rfl) ⟨353633, by rfl⟩ : syracuseStep 1886045 = 707267) (by norm_num)
theorem B1910629 : Blo 1256446 1910629 := bbase (se 4 (by rfl) ⟨179121, by rfl⟩ : syracuseStep 1910629 = 358243) (by norm_num)
theorem B2828141 : Blo 1256446 2828141 := bbase (se 3 (by rfl) ⟨530276, by rfl⟩ : syracuseStep 2828141 = 1060553) (by norm_num)
theorem B1886069 : Blo 1256446 1886069 := bbase (se 5 (by rfl) ⟨88409, by rfl⟩ : syracuseStep 1886069 = 176819) (by norm_num)
theorem B1886093 : Blo 1256446 1886093 := bbase (se 3 (by rfl) ⟨353642, by rfl⟩ : syracuseStep 1886093 = 707285) (by norm_num)
theorem B1886117 : Blo 1256446 1886117 := bbase (se 4 (by rfl) ⟨176823, by rfl⟩ : syracuseStep 1886117 = 353647) (by norm_num)
theorem B2869157 : Blo 1256446 2869157 := bbase (se 4 (by rfl) ⟨268983, by rfl⟩ : syracuseStep 2869157 = 537967) (by norm_num)
theorem B2828213 : Blo 1256446 2828213 := bbase (se 5 (by rfl) ⟨132572, by rfl⟩ : syracuseStep 2828213 = 265145) (by norm_num)
theorem B1886141 : Blo 1256446 1886141 := bbase (se 3 (by rfl) ⟨353651, by rfl⟩ : syracuseStep 1886141 = 707303) (by norm_num)
theorem B3180485 : Blo 1256446 3180485 := bbase (se 4 (by rfl) ⟨298170, by rfl⟩ : syracuseStep 3180485 = 596341) (by norm_num)
theorem B1886165 : Blo 1256446 1886165 := bbase (se 7 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 1886165 = 44207) (by norm_num)
theorem B1591265 : Blo 1256446 1591265 := bbase (se 2 (by rfl) ⟨596724, by rfl⟩ : syracuseStep 1591265 = 1193449) (by norm_num)
theorem B1886189 : Blo 1256446 1886189 := bbase (se 3 (by rfl) ⟨353660, by rfl⟩ : syracuseStep 1886189 = 707321) (by norm_num)
theorem B4777973 : Blo 1256446 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B2828285 : Blo 1256446 2828285 := bbase (se 3 (by rfl) ⟨530303, by rfl⟩ : syracuseStep 2828285 = 1060607) (by norm_num)
theorem B1886213 : Blo 1256446 1886213 := bbase (se 4 (by rfl) ⟨176832, by rfl⟩ : syracuseStep 1886213 = 353665) (by norm_num)
theorem B1591321 : Blo 1256446 1591321 := bbase (se 2 (by rfl) ⟨596745, by rfl⟩ : syracuseStep 1591321 = 1193491) (by norm_num)
theorem B2385949 : Blo 1256446 2385949 := bbase (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) (by norm_num)
theorem B1886237 : Blo 1256446 1886237 := bbase (se 3 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 1886237 = 707339) (by norm_num)
theorem B1361953 : Blo 1256446 1361953 := bbase (se 2 (by rfl) ⟨510732, by rfl⟩ : syracuseStep 1361953 = 1021465) (by norm_num)
theorem B1886261 : Blo 1256446 1886261 := bbase (se 5 (by rfl) ⟨88418, by rfl⟩ : syracuseStep 1886261 = 176837) (by norm_num)
theorem B2828357 : Blo 1256446 2828357 := bbase (se 4 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 2828357 = 530317) (by norm_num)
theorem B1886285 : Blo 1256446 1886285 := bbase (se 3 (by rfl) ⟨353678, by rfl⟩ : syracuseStep 1886285 = 707357) (by norm_num)
theorem B103254101 : Blo 1256446 103254101 := bbase (se 8 (by rfl) ⟨605004, by rfl⟩ : syracuseStep 103254101 = 1210009) (by norm_num)
theorem B2484317 : Blo 1256446 2484317 := bbase (se 3 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 2484317 = 931619) (by norm_num)
theorem B1886309 : Blo 1256446 1886309 := bbase (se 4 (by rfl) ⟨176841, by rfl⟩ : syracuseStep 1886309 = 353683) (by norm_num)
theorem B1591417 : Blo 1256446 1591417 := bbase (se 2 (by rfl) ⟨596781, by rfl⟩ : syracuseStep 1591417 = 1193563) (by norm_num)
theorem B1886333 : Blo 1256446 1886333 := bbase (se 3 (by rfl) ⟨353687, by rfl⟩ : syracuseStep 1886333 = 707375) (by norm_num)
theorem B2721925 : Blo 1256446 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B2828429 : Blo 1256446 2828429 := bbase (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) (by norm_num)
theorem B1910933 : Blo 1256446 1910933 := bbase (se 6 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 1910933 = 89575) (by norm_num)
theorem B1886357 : Blo 1256446 1886357 := bbase (se 6 (by rfl) ⟨44211, by rfl⟩ : syracuseStep 1886357 = 88423) (by norm_num)
theorem B2386093 : Blo 1256446 2386093 := bbase (se 3 (by rfl) ⟨447392, by rfl⟩ : syracuseStep 2386093 = 894785) (by norm_num)
theorem B1886381 : Blo 1256446 1886381 := bbase (se 3 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 1886381 = 707393) (by norm_num)
theorem B1886405 : Blo 1256446 1886405 := bbase (se 4 (by rfl) ⟨176850, by rfl⟩ : syracuseStep 1886405 = 353701) (by norm_num)
theorem B15288533 : Blo 1256446 15288533 := bbase (se 7 (by rfl) ⟨179162, by rfl⟩ : syracuseStep 15288533 = 358325) (by norm_num)
theorem B2828501 : Blo 1256446 2828501 := bbase (se 7 (by rfl) ⟨33146, by rfl⟩ : syracuseStep 2828501 = 66293) (by norm_num)
theorem B1886429 : Blo 1256446 1886429 := bbase (se 3 (by rfl) ⟨353705, by rfl⟩ : syracuseStep 1886429 = 707411) (by norm_num)
theorem B1886453 : Blo 1256446 1886453 := bbase (se 5 (by rfl) ⟨88427, by rfl⟩ : syracuseStep 1886453 = 176855) (by norm_num)
theorem B4245749 : Blo 1256446 4245749 := bbase (se 5 (by rfl) ⟨199019, by rfl⟩ : syracuseStep 4245749 = 398039) (by norm_num)
theorem B1886477 : Blo 1256446 1886477 := bbase (se 3 (by rfl) ⟨353714, by rfl⟩ : syracuseStep 1886477 = 707429) (by norm_num)
theorem B3180829 : Blo 1256446 3180829 := bbase (se 3 (by rfl) ⟨596405, by rfl⟩ : syracuseStep 3180829 = 1192811) (by norm_num)
theorem B2828573 : Blo 1256446 2828573 := bbase (se 3 (by rfl) ⟨530357, by rfl⟩ : syracuseStep 2828573 = 1060715) (by norm_num)
theorem B1591589 : Blo 1256446 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B1886501 : Blo 1256446 1886501 := bbase (se 4 (by rfl) ⟨176859, by rfl⟩ : syracuseStep 1886501 = 353719) (by norm_num)
theorem B1886525 : Blo 1256446 1886525 := bbase (se 3 (by rfl) ⟨353723, by rfl⟩ : syracuseStep 1886525 = 707447) (by norm_num)
theorem B2386253 : Blo 1256446 2386253 := bbase (se 3 (by rfl) ⟨447422, by rfl⟩ : syracuseStep 2386253 = 894845) (by norm_num)
theorem B1886549 : Blo 1256446 1886549 := bbase (se 10 (by rfl) ⟨2763, by rfl⟩ : syracuseStep 1886549 = 5527) (by norm_num)
theorem B1591645 : Blo 1256446 1591645 := bbase (se 3 (by rfl) ⟨298433, by rfl⟩ : syracuseStep 1591645 = 596867) (by norm_num)
theorem B2828645 : Blo 1256446 2828645 := bbase (se 4 (by rfl) ⟨265185, by rfl⟩ : syracuseStep 2828645 = 530371) (by norm_num)
theorem B1886573 : Blo 1256446 1886573 := bbase (se 3 (by rfl) ⟨353732, by rfl⟩ : syracuseStep 1886573 = 707465) (by norm_num)
theorem B2869613 : Blo 1256446 2869613 := bbase (se 3 (by rfl) ⟨538052, by rfl⟩ : syracuseStep 2869613 = 1076105) (by norm_num)
theorem B1886597 : Blo 1256446 1886597 := bbase (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) (by norm_num)
theorem B6457733 : Blo 1256446 6457733 := bbase (se 4 (by rfl) ⟨605412, by rfl⟩ : syracuseStep 6457733 = 1210825) (by norm_num)
theorem B3180941 : Blo 1256446 3180941 := bbase (se 3 (by rfl) ⟨596426, by rfl⟩ : syracuseStep 3180941 = 1192853) (by norm_num)
theorem B1886621 : Blo 1256446 1886621 := bbase (se 3 (by rfl) ⟨353741, by rfl⟩ : syracuseStep 1886621 = 707483) (by norm_num)
theorem B2828717 : Blo 1256446 2828717 := bbase (se 3 (by rfl) ⟨530384, by rfl⟩ : syracuseStep 2828717 = 1060769) (by norm_num)
theorem B9677237 : Blo 1256446 9677237 := bbase (se 5 (by rfl) ⟨453620, by rfl⟩ : syracuseStep 9677237 = 907241) (by norm_num)
theorem B1886645 : Blo 1256446 1886645 := bbase (se 5 (by rfl) ⟨88436, by rfl⟩ : syracuseStep 1886645 = 176873) (by norm_num)
theorem B1591741 : Blo 1256446 1591741 := bbase (se 3 (by rfl) ⟨298451, by rfl⟩ : syracuseStep 1591741 = 596903) (by norm_num)
theorem B1886669 : Blo 1256446 1886669 := bbase (se 3 (by rfl) ⟨353750, by rfl⟩ : syracuseStep 1886669 = 707501) (by norm_num)
theorem B2386397 : Blo 1256446 2386397 := bbase (se 3 (by rfl) ⟨447449, by rfl⟩ : syracuseStep 2386397 = 894899) (by norm_num)
theorem B1886693 : Blo 1256446 1886693 := bbase (se 4 (by rfl) ⟨176877, by rfl⟩ : syracuseStep 1886693 = 353755) (by norm_num)
theorem B2828789 : Blo 1256446 2828789 := bbase (se 5 (by rfl) ⟨132599, by rfl⟩ : syracuseStep 2828789 = 265199) (by norm_num)
theorem B6367733 : Blo 1256446 6367733 := bbase (se 5 (by rfl) ⟨298487, by rfl⟩ : syracuseStep 6367733 = 596975) (by norm_num)
theorem B1886717 : Blo 1256446 1886717 := bbase (se 3 (by rfl) ⟨353759, by rfl⟩ : syracuseStep 1886717 = 707519) (by norm_num)
theorem B3148301 : Blo 1256446 3148301 := bbase (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) (by norm_num)
theorem B1886741 : Blo 1256446 1886741 := bbase (se 6 (by rfl) ⟨44220, by rfl⟩ : syracuseStep 1886741 = 88441) (by norm_num)
theorem B1886765 : Blo 1256446 1886765 := bbase (se 3 (by rfl) ⟨353768, by rfl⟩ : syracuseStep 1886765 = 707537) (by norm_num)
theorem B2828861 : Blo 1256446 2828861 := bbase (se 3 (by rfl) ⟨530411, by rfl⟩ : syracuseStep 2828861 = 1060823) (by norm_num)
theorem B1886789 : Blo 1256446 1886789 := bbase (se 4 (by rfl) ⟨176886, by rfl⟩ : syracuseStep 1886789 = 353773) (by norm_num)
theorem B3181133 : Blo 1256446 3181133 := bbase (se 3 (by rfl) ⟨596462, by rfl⟩ : syracuseStep 3181133 = 1192925) (by norm_num)
theorem B1886813 : Blo 1256446 1886813 := bbase (se 3 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 1886813 = 707555) (by norm_num)
theorem B1591913 : Blo 1256446 1591913 := bbase (se 2 (by rfl) ⟨596967, by rfl⟩ : syracuseStep 1591913 = 1193935) (by norm_num)
theorem B1886837 : Blo 1256446 1886837 := bbase (se 5 (by rfl) ⟨88445, by rfl⟩ : syracuseStep 1886837 = 176891) (by norm_num)
theorem B2828933 : Blo 1256446 2828933 := bbase (se 4 (by rfl) ⟨265212, by rfl⟩ : syracuseStep 2828933 = 530425) (by norm_num)
theorem B1886861 : Blo 1256446 1886861 := bbase (se 3 (by rfl) ⟨353786, by rfl⟩ : syracuseStep 1886861 = 707573) (by norm_num)
theorem B1591969 : Blo 1256446 1591969 := bbase (se 2 (by rfl) ⟨596988, by rfl⟩ : syracuseStep 1591969 = 1193977) (by norm_num)
theorem B1886885 : Blo 1256446 1886885 := bbase (se 4 (by rfl) ⟨176895, by rfl⟩ : syracuseStep 1886885 = 353791) (by norm_num)
theorem B4246181 : Blo 1256446 4246181 := bbase (se 4 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 4246181 = 796159) (by norm_num)
theorem B1886909 : Blo 1256446 1886909 := bbase (se 3 (by rfl) ⟨353795, by rfl⟩ : syracuseStep 1886909 = 707591) (by norm_num)
theorem B2829005 : Blo 1256446 2829005 := bbase (se 3 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 2829005 = 1060877) (by norm_num)
theorem B1886933 : Blo 1256446 1886933 := bbase (se 7 (by rfl) ⟨22112, by rfl⟩ : syracuseStep 1886933 = 44225) (by norm_num)
theorem B1886957 : Blo 1256446 1886957 := bbase (se 3 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 1886957 = 707609) (by norm_num)
theorem B2386685 : Blo 1256446 2386685 := bbase (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) (by norm_num)
theorem B1592065 : Blo 1256446 1592065 := bbase (se 2 (by rfl) ⟨597024, by rfl⟩ : syracuseStep 1592065 = 1194049) (by norm_num)
theorem B1698565 : Blo 1256446 1698565 := bbase (se 4 (by rfl) ⟨159240, by rfl⟩ : syracuseStep 1698565 = 318481) (by norm_num)
theorem B1886981 : Blo 1256446 1886981 := bbase (se 4 (by rfl) ⟨176904, by rfl⟩ : syracuseStep 1886981 = 353809) (by norm_num)
theorem B6540053 : Blo 1256446 6540053 := bbase (se 6 (by rfl) ⟨153282, by rfl⟩ : syracuseStep 6540053 = 306565) (by norm_num)
theorem B2829077 : Blo 1256446 2829077 := bbase (se 6 (by rfl) ⟨66306, by rfl⟩ : syracuseStep 2829077 = 132613) (by norm_num)
theorem B1887005 : Blo 1256446 1887005 := bbase (se 3 (by rfl) ⟨353813, by rfl⟩ : syracuseStep 1887005 = 707627) (by norm_num)
theorem B1887029 : Blo 1256446 1887029 := bbase (se 5 (by rfl) ⟨88454, by rfl⟩ : syracuseStep 1887029 = 176909) (by norm_num)
theorem B1887053 : Blo 1256446 1887053 := bbase (se 3 (by rfl) ⟨353822, by rfl⟩ : syracuseStep 1887053 = 707645) (by norm_num)
theorem B2829149 : Blo 1256446 2829149 := bbase (se 3 (by rfl) ⟨530465, by rfl⟩ : syracuseStep 2829149 = 1060931) (by norm_num)
theorem B1887077 : Blo 1256446 1887077 := bbase (se 4 (by rfl) ⟨176913, by rfl⟩ : syracuseStep 1887077 = 353827) (by norm_num)
theorem B1887101 : Blo 1256446 1887101 := bbase (se 3 (by rfl) ⟨353831, by rfl⟩ : syracuseStep 1887101 = 707663) (by norm_num)
theorem B6040453 : Blo 1256446 6040453 := bbase (se 4 (by rfl) ⟨566292, by rfl⟩ : syracuseStep 6040453 = 1132585) (by norm_num)
theorem B2386837 : Blo 1256446 2386837 := bbase (se 6 (by rfl) ⟨55941, by rfl⟩ : syracuseStep 2386837 = 111883) (by norm_num)
theorem B1887125 : Blo 1256446 1887125 := bbase (se 6 (by rfl) ⟨44229, by rfl⟩ : syracuseStep 1887125 = 88459) (by norm_num)
theorem B3181477 : Blo 1256446 3181477 := bbase (se 4 (by rfl) ⟨298263, by rfl⟩ : syracuseStep 3181477 = 596527) (by norm_num)
theorem B2829221 : Blo 1256446 2829221 := bbase (se 4 (by rfl) ⟨265239, by rfl⟩ : syracuseStep 2829221 = 530479) (by norm_num)
theorem B1592237 : Blo 1256446 1592237 := bbase (se 3 (by rfl) ⟨298544, by rfl⟩ : syracuseStep 1592237 = 597089) (by norm_num)
theorem B1887149 : Blo 1256446 1887149 := bbase (se 3 (by rfl) ⟨353840, by rfl⟩ : syracuseStep 1887149 = 707681) (by norm_num)
theorem B6450101 : Blo 1256446 6450101 := bbase (se 5 (by rfl) ⟨302348, by rfl⟩ : syracuseStep 6450101 = 604697) (by norm_num)
theorem B1887173 : Blo 1256446 1887173 := bbase (se 4 (by rfl) ⟨176922, by rfl⟩ : syracuseStep 1887173 = 353845) (by norm_num)
theorem B1887197 : Blo 1256446 1887197 := bbase (se 3 (by rfl) ⟨353849, by rfl⟩ : syracuseStep 1887197 = 707699) (by norm_num)
theorem B1592293 : Blo 1256446 1592293 := bbase (se 4 (by rfl) ⟨149277, by rfl⟩ : syracuseStep 1592293 = 298555) (by norm_num)
theorem B2829293 : Blo 1256446 2829293 := bbase (se 3 (by rfl) ⟨530492, by rfl⟩ : syracuseStep 2829293 = 1060985) (by norm_num)
theorem B1887221 : Blo 1256446 1887221 := bbase (se 5 (by rfl) ⟨88463, by rfl⟩ : syracuseStep 1887221 = 176927) (by norm_num)
theorem B1887245 : Blo 1256446 1887245 := bbase (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) (by norm_num)
theorem B21761045 : Blo 1256446 21761045 := bbase (se 6 (by rfl) ⟨510024, by rfl⟩ : syracuseStep 21761045 = 1020049) (by norm_num)
theorem B3181589 : Blo 1256446 3181589 := bbase (se 6 (by rfl) ⟨74568, by rfl⟩ : syracuseStep 3181589 = 149137) (by norm_num)
theorem B1887269 : Blo 1256446 1887269 := bbase (se 4 (by rfl) ⟨176931, by rfl⟩ : syracuseStep 1887269 = 353863) (by norm_num)
theorem B2829365 : Blo 1256446 2829365 := bbase (se 5 (by rfl) ⟨132626, by rfl⟩ : syracuseStep 2829365 = 265253) (by norm_num)
theorem B1887293 : Blo 1256446 1887293 := bbase (se 3 (by rfl) ⟨353867, by rfl⟩ : syracuseStep 1887293 = 707735) (by norm_num)
theorem B1592389 : Blo 1256446 1592389 := bbase (se 4 (by rfl) ⟨149286, by rfl⟩ : syracuseStep 1592389 = 298573) (by norm_num)
theorem B1887317 : Blo 1256446 1887317 := bbase (se 8 (by rfl) ⟨11058, by rfl⟩ : syracuseStep 1887317 = 22117) (by norm_num)
theorem B4246613 : Blo 1256446 4246613 := bbase (se 8 (by rfl) ⟨24882, by rfl⟩ : syracuseStep 4246613 = 49765) (by norm_num)
theorem B1887341 : Blo 1256446 1887341 := bbase (se 3 (by rfl) ⟨353876, by rfl⟩ : syracuseStep 1887341 = 707753) (by norm_num)
theorem B5368949 : Blo 1256446 5368949 := bbase (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) (by norm_num)
theorem B2829437 : Blo 1256446 2829437 := bbase (se 3 (by rfl) ⟨530519, by rfl⟩ : syracuseStep 2829437 = 1061039) (by norm_num)
theorem B1887365 : Blo 1256446 1887365 := bbase (se 4 (by rfl) ⟨176940, by rfl⟩ : syracuseStep 1887365 = 353881) (by norm_num)
theorem B1789069 : Blo 1256446 1789069 := bbase (se 3 (by rfl) ⟨335450, by rfl⟩ : syracuseStep 1789069 = 670901) (by norm_num)
theorem B1887389 : Blo 1256446 1887389 := bbase (se 3 (by rfl) ⟨353885, by rfl⟩ : syracuseStep 1887389 = 707771) (by norm_num)
theorem B1887413 : Blo 1256446 1887413 := bbase (se 5 (by rfl) ⟨88472, by rfl⟩ : syracuseStep 1887413 = 176945) (by norm_num)
theorem B2387141 : Blo 1256446 2387141 := bbase (se 4 (by rfl) ⟨223794, by rfl⟩ : syracuseStep 2387141 = 447589) (by norm_num)
theorem B2829509 : Blo 1256446 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B1887437 : Blo 1256446 1887437 := bbase (se 3 (by rfl) ⟨353894, by rfl⟩ : syracuseStep 1887437 = 707789) (by norm_num)
theorem B3181781 : Blo 1256446 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B1887461 : Blo 1256446 1887461 := bbase (se 4 (by rfl) ⟨176949, by rfl⟩ : syracuseStep 1887461 = 353899) (by norm_num)
theorem B1592561 : Blo 1256446 1592561 := bbase (se 2 (by rfl) ⟨597210, by rfl⟩ : syracuseStep 1592561 = 1194421) (by norm_num)
theorem B1887485 : Blo 1256446 1887485 := bbase (se 3 (by rfl) ⟨353903, by rfl⟩ : syracuseStep 1887485 = 707807) (by norm_num)
theorem B2829581 : Blo 1256446 2829581 := bbase (se 3 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 2829581 = 1061093) (by norm_num)
theorem B1887509 : Blo 1256446 1887509 := bbase (se 6 (by rfl) ⟨44238, by rfl⟩ : syracuseStep 1887509 = 88477) (by norm_num)
theorem B1592617 : Blo 1256446 1592617 := bbase (se 2 (by rfl) ⟨597231, by rfl⟩ : syracuseStep 1592617 = 1194463) (by norm_num)
theorem B1887533 : Blo 1256446 1887533 := bbase (se 3 (by rfl) ⟨353912, by rfl⟩ : syracuseStep 1887533 = 707825) (by norm_num)
theorem B1510709 : Blo 1256446 1510709 := bbase (se 5 (by rfl) ⟨70814, by rfl⟩ : syracuseStep 1510709 = 141629) (by norm_num)
theorem B1887557 : Blo 1256446 1887557 := bbase (se 4 (by rfl) ⟨176958, by rfl⟩ : syracuseStep 1887557 = 353917) (by norm_num)
theorem B2829653 : Blo 1256446 2829653 := bbase (se 11 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 2829653 = 4145) (by norm_num)
theorem B1887581 : Blo 1256446 1887581 := bbase (se 3 (by rfl) ⟨353921, by rfl⟩ : syracuseStep 1887581 = 707843) (by norm_num)
theorem B1789285 : Blo 1256446 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B2149733 : Blo 1256446 2149733 := bbase (se 4 (by rfl) ⟨201537, by rfl⟩ : syracuseStep 2149733 = 403075) (by norm_num)
theorem B1887605 : Blo 1256446 1887605 := bbase (se 5 (by rfl) ⟨88481, by rfl⟩ : syracuseStep 1887605 = 176963) (by norm_num)
theorem B3313021 : Blo 1256446 3313021 := bbase (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) (by norm_num)
theorem B1592713 : Blo 1256446 1592713 := bbase (se 2 (by rfl) ⟨597267, by rfl⟩ : syracuseStep 1592713 = 1194535) (by norm_num)
theorem B1887629 : Blo 1256446 1887629 := bbase (se 3 (by rfl) ⟨353930, by rfl⟩ : syracuseStep 1887629 = 707861) (by norm_num)
theorem B2829725 : Blo 1256446 2829725 := bbase (se 3 (by rfl) ⟨530573, by rfl⟩ : syracuseStep 2829725 = 1061147) (by norm_num)
theorem B1887653 : Blo 1256446 1887653 := bbase (se 4 (by rfl) ⟨176967, by rfl⟩ : syracuseStep 1887653 = 353935) (by norm_num)
theorem B2829797 : Blo 1256446 2829797 := bbase (se 4 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 2829797 = 530587) (by norm_num)
theorem B4247045 : Blo 1256446 4247045 := bbase (se 4 (by rfl) ⟨398160, by rfl⟩ : syracuseStep 4247045 = 796321) (by norm_num)
theorem B1510921 : Blo 1256446 1510921 := bbase (se 2 (by rfl) ⟨566595, by rfl⟩ : syracuseStep 1510921 = 1133191) (by norm_num)
theorem B3182125 : Blo 1256446 3182125 := bbase (se 3 (by rfl) ⟨596648, by rfl⟩ : syracuseStep 3182125 = 1193297) (by norm_num)
theorem B2829869 : Blo 1256446 2829869 := bbase (se 3 (by rfl) ⟨530600, by rfl⟩ : syracuseStep 2829869 = 1061201) (by norm_num)
theorem B1912429 : Blo 1256446 1912429 := bbase (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) (by norm_num)
theorem B2829941 : Blo 1256446 2829941 := bbase (se 5 (by rfl) ⟨132653, by rfl⟩ : syracuseStep 2829941 = 265307) (by norm_num)
theorem B1511065 : Blo 1256446 1511065 := bbase (se 2 (by rfl) ⟨566649, by rfl⟩ : syracuseStep 1511065 = 1133299) (by norm_num)
theorem B3182237 : Blo 1256446 3182237 := bbase (se 3 (by rfl) ⟨596669, by rfl⟩ : syracuseStep 3182237 = 1193339) (by norm_num)
theorem B2830013 : Blo 1256446 2830013 := bbase (se 3 (by rfl) ⟨530627, by rfl⟩ : syracuseStep 2830013 = 1061255) (by norm_num)
theorem B32640725 : Blo 1256446 32640725 := bbase (se 7 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 32640725 = 765017) (by norm_num)
theorem B1789661 : Blo 1256446 1789661 := bbase (se 3 (by rfl) ⟨335561, by rfl⟩ : syracuseStep 1789661 = 671123) (by norm_num)
theorem B2830085 : Blo 1256446 2830085 := bbase (se 4 (by rfl) ⟨265320, by rfl⟩ : syracuseStep 2830085 = 530641) (by norm_num)
theorem B6369029 : Blo 1256446 6369029 := bbase (se 4 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 6369029 = 1194193) (by norm_num)
theorem B4026149 : Blo 1256446 4026149 := bbase (se 4 (by rfl) ⟨377451, by rfl⟩ : syracuseStep 4026149 = 754903) (by norm_num)
theorem B2830157 : Blo 1256446 2830157 := bbase (se 3 (by rfl) ⟨530654, by rfl⟩ : syracuseStep 2830157 = 1061309) (by norm_num)
theorem B4771669 : Blo 1256446 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B10743637 : Blo 1256446 10743637 := bbase (se 9 (by rfl) ⟨31475, by rfl⟩ : syracuseStep 10743637 = 62951) (by norm_num)
theorem B3182429 : Blo 1256446 3182429 := bbase (se 3 (by rfl) ⟨596705, by rfl⟩ : syracuseStep 3182429 = 1193411) (by norm_num)
theorem B2723725 : Blo 1256446 2723725 := bbase (se 3 (by rfl) ⟨510698, by rfl⟩ : syracuseStep 2723725 = 1021397) (by norm_num)
theorem B6123413 : Blo 1256446 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B2830229 : Blo 1256446 2830229 := bbase (se 6 (by rfl) ⟨66333, by rfl⟩ : syracuseStep 2830229 = 132667) (by norm_num)
theorem B2387893 : Blo 1256446 2387893 := bbase (se 5 (by rfl) ⟨111932, by rfl⟩ : syracuseStep 2387893 = 223865) (by norm_num)
theorem B2830301 : Blo 1256446 2830301 := bbase (se 3 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 2830301 = 1061363) (by norm_num)
theorem B2830373 : Blo 1256446 2830373 := bbase (se 4 (by rfl) ⟨265347, by rfl⟩ : syracuseStep 2830373 = 530695) (by norm_num)
theorem B2388037 : Blo 1256446 2388037 := bbase (se 4 (by rfl) ⟨223878, by rfl⟩ : syracuseStep 2388037 = 447757) (by norm_num)
theorem B2830445 : Blo 1256446 2830445 := bbase (se 3 (by rfl) ⟨530708, by rfl⟩ : syracuseStep 2830445 = 1061417) (by norm_num)
theorem B4771973 : Blo 1256446 4771973 := bbase (se 4 (by rfl) ⟨447372, by rfl⟩ : syracuseStep 4771973 = 894745) (by norm_num)
theorem B6361253 : Blo 1256446 6361253 := bbase (se 4 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 6361253 = 1192735) (by norm_num)
theorem B3182773 : Blo 1256446 3182773 := bbase (se 5 (by rfl) ⟨149192, by rfl⟩ : syracuseStep 3182773 = 298385) (by norm_num)
theorem B2830517 : Blo 1256446 2830517 := bbase (se 5 (by rfl) ⟨132680, by rfl⟩ : syracuseStep 2830517 = 265361) (by norm_num)
theorem B2388197 : Blo 1256446 2388197 := bbase (se 4 (by rfl) ⟨223893, by rfl⟩ : syracuseStep 2388197 = 447787) (by norm_num)
theorem B7852277 : Blo 1256446 7852277 := bbase (se 5 (by rfl) ⟨368075, by rfl⟩ : syracuseStep 7852277 = 736151) (by norm_num)
theorem B2830589 : Blo 1256446 2830589 := bbase (se 3 (by rfl) ⟨530735, by rfl⟩ : syracuseStep 2830589 = 1061471) (by norm_num)
theorem B2265365 : Blo 1256446 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B3182885 : Blo 1256446 3182885 := bbase (se 4 (by rfl) ⟨298395, by rfl⟩ : syracuseStep 3182885 = 596791) (by norm_num)
theorem B2617661 : Blo 1256446 2617661 := bbase (se 3 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 2617661 = 981623) (by norm_num)
theorem B2830661 : Blo 1256446 2830661 := bbase (se 4 (by rfl) ⟨265374, by rfl⟩ : syracuseStep 2830661 = 530749) (by norm_num)
theorem B4591973 : Blo 1256446 4591973 := bbase (se 4 (by rfl) ⟨430497, by rfl⟩ : syracuseStep 4591973 = 860995) (by norm_num)
theorem B2388341 : Blo 1256446 2388341 := bbase (se 5 (by rfl) ⟨111953, by rfl⟩ : syracuseStep 2388341 = 223907) (by norm_num)
theorem B1913221 : Blo 1256446 1913221 := bbase (se 4 (by rfl) ⟨179364, by rfl⟩ : syracuseStep 1913221 = 358729) (by norm_num)
theorem B1413517 : Blo 1256446 1413517 := bbase (se 3 (by rfl) ⟨265034, by rfl⟩ : syracuseStep 1413517 = 530069) (by norm_num)
theorem B2830733 : Blo 1256446 2830733 := bbase (se 3 (by rfl) ⟨530762, by rfl⟩ : syracuseStep 2830733 = 1061525) (by norm_num)
theorem B1413553 : Blo 1256446 1413553 := bbase (se 2 (by rfl) ⟨530082, by rfl⟩ : syracuseStep 1413553 = 1060165) (by norm_num)
theorem B1913269 : Blo 1256446 1913269 := bbase (se 5 (by rfl) ⟨89684, by rfl⟩ : syracuseStep 1913269 = 179369) (by norm_num)
theorem B1413589 : Blo 1256446 1413589 := bbase (se 7 (by rfl) ⟨16565, by rfl⟩ : syracuseStep 1413589 = 33131) (by norm_num)
theorem B2830805 : Blo 1256446 2830805 := bbase (se 7 (by rfl) ⟨33173, by rfl⟩ : syracuseStep 2830805 = 66347) (by norm_num)
theorem B3183077 : Blo 1256446 3183077 := bbase (se 4 (by rfl) ⟨298413, by rfl⟩ : syracuseStep 3183077 = 596827) (by norm_num)
theorem B1413625 : Blo 1256446 1413625 := bbase (se 2 (by rfl) ⟨530109, by rfl⟩ : syracuseStep 1413625 = 1060219) (by norm_num)
theorem B1839613 : Blo 1256446 1839613 := bbase (se 3 (by rfl) ⟨344927, by rfl⟩ : syracuseStep 1839613 = 689855) (by norm_num)
theorem B3019285 : Blo 1256446 3019285 := bbase (se 6 (by rfl) ⟨70764, by rfl⟩ : syracuseStep 3019285 = 141529) (by norm_num)
theorem B1413661 : Blo 1256446 1413661 := bbase (se 3 (by rfl) ⟨265061, by rfl⟩ : syracuseStep 1413661 = 530123) (by norm_num)
theorem B2830877 : Blo 1256446 2830877 := bbase (se 3 (by rfl) ⟨530789, by rfl⟩ : syracuseStep 2830877 = 1061579) (by norm_num)
theorem B4026917 : Blo 1256446 4026917 := bbase (se 4 (by rfl) ⟨377523, by rfl⟩ : syracuseStep 4026917 = 755047) (by norm_num)
theorem B1413697 : Blo 1256446 1413697 := bbase (se 2 (by rfl) ⟨530136, by rfl⟩ : syracuseStep 1413697 = 1060273) (by norm_num)
theorem B1413733 : Blo 1256446 1413733 := bbase (se 4 (by rfl) ⟨132537, by rfl⟩ : syracuseStep 1413733 = 265075) (by norm_num)
theorem B2830949 : Blo 1256446 2830949 := bbase (se 4 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 2830949 = 530803) (by norm_num)
theorem B1413769 : Blo 1256446 1413769 := bbase (se 2 (by rfl) ⟨530163, by rfl⟩ : syracuseStep 1413769 = 1060327) (by norm_num)
theorem B2388629 : Blo 1256446 2388629 := bbase (se 6 (by rfl) ⟨55983, by rfl⟩ : syracuseStep 2388629 = 111967) (by norm_num)
theorem B1413805 : Blo 1256446 1413805 := bbase (se 3 (by rfl) ⟨265088, by rfl⟩ : syracuseStep 1413805 = 530177) (by norm_num)
theorem B2831021 : Blo 1256446 2831021 := bbase (se 3 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 2831021 = 1061633) (by norm_num)
theorem B1413841 : Blo 1256446 1413841 := bbase (se 2 (by rfl) ⟨530190, by rfl⟩ : syracuseStep 1413841 = 1060381) (by norm_num)
theorem B1700581 : Blo 1256446 1700581 := bbase (se 4 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 1700581 = 318859) (by norm_num)
theorem B1413877 : Blo 1256446 1413877 := bbase (se 5 (by rfl) ⟨66275, by rfl⟩ : syracuseStep 1413877 = 132551) (by norm_num)
theorem B12907253 : Blo 1256446 12907253 := bbase (se 5 (by rfl) ⟨605027, by rfl⟩ : syracuseStep 12907253 = 1210055) (by norm_num)
theorem B2831093 : Blo 1256446 2831093 := bbase (se 5 (by rfl) ⟨132707, by rfl⟩ : syracuseStep 2831093 = 265415) (by norm_num)
theorem B1413913 : Blo 1256446 1413913 := bbase (se 2 (by rfl) ⟨530217, by rfl⟩ : syracuseStep 1413913 = 1060435) (by norm_num)
theorem B2388781 : Blo 1256446 2388781 := bbase (se 3 (by rfl) ⟨447896, by rfl⟩ : syracuseStep 2388781 = 895793) (by norm_num)
theorem B2904893 : Blo 1256446 2904893 := bbase (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) (by norm_num)
theorem B1413949 : Blo 1256446 1413949 := bbase (se 3 (by rfl) ⟨265115, by rfl⟩ : syracuseStep 1413949 = 530231) (by norm_num)
theorem B3183421 : Blo 1256446 3183421 := bbase (se 3 (by rfl) ⟨596891, by rfl⟩ : syracuseStep 3183421 = 1193783) (by norm_num)
theorem B2831165 : Blo 1256446 2831165 := bbase (se 3 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 2831165 = 1061687) (by norm_num)
theorem B1413985 : Blo 1256446 1413985 := bbase (se 2 (by rfl) ⟨530244, by rfl⟩ : syracuseStep 1413985 = 1060489) (by norm_num)
theorem B5370725 : Blo 1256446 5370725 := bbase (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) (by norm_num)
theorem B1414021 : Blo 1256446 1414021 := bbase (se 4 (by rfl) ⟨132564, by rfl⟩ : syracuseStep 1414021 = 265129) (by norm_num)
theorem B2831237 : Blo 1256446 2831237 := bbase (se 4 (by rfl) ⟨265428, by rfl⟩ : syracuseStep 2831237 = 530857) (by norm_num)
theorem B1414057 : Blo 1256446 1414057 := bbase (se 2 (by rfl) ⟨530271, by rfl⟩ : syracuseStep 1414057 = 1060543) (by norm_num)
theorem B3183533 : Blo 1256446 3183533 := bbase (se 3 (by rfl) ⟨596912, by rfl⟩ : syracuseStep 3183533 = 1193825) (by norm_num)
theorem B1414093 : Blo 1256446 1414093 := bbase (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) (by norm_num)
theorem B2831309 : Blo 1256446 2831309 := bbase (se 3 (by rfl) ⟨530870, by rfl⟩ : syracuseStep 2831309 = 1061741) (by norm_num)
theorem B2266093 : Blo 1256446 2266093 := bbase (se 3 (by rfl) ⟨424892, by rfl⟩ : syracuseStep 2266093 = 849785) (by norm_num)
theorem B1414129 : Blo 1256446 1414129 := bbase (se 2 (by rfl) ⟨530298, by rfl⟩ : syracuseStep 1414129 = 1060597) (by norm_num)
theorem B1414165 : Blo 1256446 1414165 := bbase (se 6 (by rfl) ⟨33144, by rfl⟩ : syracuseStep 1414165 = 66289) (by norm_num)
theorem B6370325 : Blo 1256446 6370325 := bbase (se 6 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 6370325 = 298609) (by norm_num)
theorem B2831381 : Blo 1256446 2831381 := bbase (se 6 (by rfl) ⟨66360, by rfl⟩ : syracuseStep 2831381 = 132721) (by norm_num)
theorem B4027429 : Blo 1256446 4027429 := bbase (se 4 (by rfl) ⟨377571, by rfl⟩ : syracuseStep 4027429 = 755143) (by norm_num)
theorem B9679925 : Blo 1256446 9679925 := bbase (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) (by norm_num)
theorem B1414201 : Blo 1256446 1414201 := bbase (se 2 (by rfl) ⟨530325, by rfl⟩ : syracuseStep 1414201 = 1060651) (by norm_num)
theorem B1414237 : Blo 1256446 1414237 := bbase (se 3 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 1414237 = 530339) (by norm_num)
theorem B2831453 : Blo 1256446 2831453 := bbase (se 3 (by rfl) ⟨530897, by rfl⟩ : syracuseStep 2831453 = 1061795) (by norm_num)
theorem B3183725 : Blo 1256446 3183725 := bbase (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) (by norm_num)
theorem B1791085 : Blo 1256446 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B1414273 : Blo 1256446 1414273 := bbase (se 2 (by rfl) ⟨530352, by rfl⟩ : syracuseStep 1414273 = 1060705) (by norm_num)
theorem B1414309 : Blo 1256446 1414309 := bbase (se 4 (by rfl) ⟨132591, by rfl⟩ : syracuseStep 1414309 = 265183) (by norm_num)
theorem B4240565 : Blo 1256446 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B2266309 : Blo 1256446 2266309 := bbase (se 4 (by rfl) ⟨212466, by rfl⟩ : syracuseStep 2266309 = 424933) (by norm_num)
theorem B1414345 : Blo 1256446 1414345 := bbase (se 2 (by rfl) ⟨530379, by rfl⟩ : syracuseStep 1414345 = 1060759) (by norm_num)
theorem B3019997 : Blo 1256446 3019997 := bbase (se 3 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 3019997 = 1132499) (by norm_num)
theorem B1414381 : Blo 1256446 1414381 := bbase (se 3 (by rfl) ⟨265196, by rfl⟩ : syracuseStep 1414381 = 530393) (by norm_num)
theorem B1414417 : Blo 1256446 1414417 := bbase (se 2 (by rfl) ⟨530406, by rfl⟩ : syracuseStep 1414417 = 1060813) (by norm_num)
theorem B7165205 : Blo 1256446 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B1414453 : Blo 1256446 1414453 := bbase (se 5 (by rfl) ⟨66302, by rfl⟩ : syracuseStep 1414453 = 132605) (by norm_num)
theorem B1414489 : Blo 1256446 1414489 := bbase (se 2 (by rfl) ⟨530433, by rfl⟩ : syracuseStep 1414489 = 1060867) (by norm_num)
theorem B2684269 : Blo 1256446 2684269 := bbase (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) (by norm_num)
theorem B3102077 : Blo 1256446 3102077 := bbase (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) (by norm_num)
theorem B1414525 : Blo 1256446 1414525 := bbase (se 3 (by rfl) ⟨265223, by rfl⟩ : syracuseStep 1414525 = 530447) (by norm_num)
theorem B1414561 : Blo 1256446 1414561 := bbase (se 2 (by rfl) ⟨530460, by rfl⟩ : syracuseStep 1414561 = 1060921) (by norm_num)
theorem B5100965 : Blo 1256446 5100965 := bbase (se 4 (by rfl) ⟨478215, by rfl⟩ : syracuseStep 5100965 = 956431) (by norm_num)
theorem B6362549 : Blo 1256446 6362549 := bbase (se 5 (by rfl) ⟨298244, by rfl⟩ : syracuseStep 6362549 = 596489) (by norm_num)
theorem B1414597 : Blo 1256446 1414597 := bbase (se 4 (by rfl) ⟨132618, by rfl⟩ : syracuseStep 1414597 = 265237) (by norm_num)
theorem B3184069 : Blo 1256446 3184069 := bbase (se 4 (by rfl) ⟨298506, by rfl⟩ : syracuseStep 3184069 = 597013) (by norm_num)
theorem B1414633 : Blo 1256446 1414633 := bbase (se 2 (by rfl) ⟨530487, by rfl⟩ : syracuseStep 1414633 = 1060975) (by norm_num)
theorem B1414669 : Blo 1256446 1414669 := bbase (se 3 (by rfl) ⟨265250, by rfl⟩ : syracuseStep 1414669 = 530501) (by norm_num)
theorem B1414705 : Blo 1256446 1414705 := bbase (se 2 (by rfl) ⟨530514, by rfl⟩ : syracuseStep 1414705 = 1061029) (by norm_num)
theorem B3184181 : Blo 1256446 3184181 := bbase (se 5 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 3184181 = 298517) (by norm_num)
theorem B1414741 : Blo 1256446 1414741 := bbase (se 8 (by rfl) ⟨8289, by rfl⟩ : syracuseStep 1414741 = 16579) (by norm_num)
theorem B3020381 : Blo 1256446 3020381 := bbase (se 3 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 3020381 = 1132643) (by norm_num)
theorem B4240997 : Blo 1256446 4240997 := bbase (se 4 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 4240997 = 795187) (by norm_num)
theorem B1414777 : Blo 1256446 1414777 := bbase (se 2 (by rfl) ⟨530541, by rfl⟩ : syracuseStep 1414777 = 1061083) (by norm_num)
theorem B1414813 : Blo 1256446 1414813 := bbase (se 3 (by rfl) ⟨265277, by rfl⟩ : syracuseStep 1414813 = 530555) (by norm_num)
theorem B2266813 : Blo 1256446 2266813 := bbase (se 3 (by rfl) ⟨425027, by rfl⟩ : syracuseStep 2266813 = 850055) (by norm_num)
theorem B1791677 : Blo 1256446 1791677 := bbase (se 3 (by rfl) ⟨335939, by rfl⟩ : syracuseStep 1791677 = 671879) (by norm_num)
theorem B1414849 : Blo 1256446 1414849 := bbase (se 2 (by rfl) ⟨530568, by rfl⟩ : syracuseStep 1414849 = 1061137) (by norm_num)
theorem B1414885 : Blo 1256446 1414885 := bbase (se 4 (by rfl) ⟨132645, by rfl⟩ : syracuseStep 1414885 = 265291) (by norm_num)
theorem B3184373 : Blo 1256446 3184373 := bbase (se 5 (by rfl) ⟨149267, by rfl⟩ : syracuseStep 3184373 = 298535) (by norm_num)
theorem B1414921 : Blo 1256446 1414921 := bbase (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) (by norm_num)
theorem B1791757 : Blo 1256446 1791757 := bbase (se 3 (by rfl) ⟨335954, by rfl⟩ : syracuseStep 1791757 = 671909) (by norm_num)
theorem B10745621 : Blo 1256446 10745621 := bbase (se 6 (by rfl) ⟨251850, by rfl⟩ : syracuseStep 10745621 = 503701) (by norm_num)
theorem B1414957 : Blo 1256446 1414957 := bbase (se 3 (by rfl) ⟨265304, by rfl⟩ : syracuseStep 1414957 = 530609) (by norm_num)
theorem B5371717 : Blo 1256446 5371717 := bbase (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) (by norm_num)
theorem B1414993 : Blo 1256446 1414993 := bbase (se 2 (by rfl) ⟨530622, by rfl⟩ : syracuseStep 1414993 = 1061245) (by norm_num)
theorem B24180565 : Blo 1256446 24180565 := bbase (se 9 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 24180565 = 141683) (by norm_num)
theorem B2684765 : Blo 1256446 2684765 := bbase (se 3 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 2684765 = 1006787) (by norm_num)
theorem B1415029 : Blo 1256446 1415029 := bbase (se 5 (by rfl) ⟨66329, by rfl⟩ : syracuseStep 1415029 = 132659) (by norm_num)
theorem B3020669 : Blo 1256446 3020669 := bbase (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) (by norm_num)
theorem B1415065 : Blo 1256446 1415065 := bbase (se 2 (by rfl) ⟨530649, by rfl⟩ : syracuseStep 1415065 = 1061299) (by norm_num)
theorem B1415101 : Blo 1256446 1415101 := bbase (se 3 (by rfl) ⟨265331, by rfl⟩ : syracuseStep 1415101 = 530663) (by norm_num)
theorem B1415137 : Blo 1256446 1415137 := bbase (se 2 (by rfl) ⟨530676, by rfl⟩ : syracuseStep 1415137 = 1061353) (by norm_num)
theorem B1415173 : Blo 1256446 1415173 := bbase (se 4 (by rfl) ⟨132672, by rfl⟩ : syracuseStep 1415173 = 265345) (by norm_num)
theorem B4241429 : Blo 1256446 4241429 := bbase (se 6 (by rfl) ⟨99408, by rfl⟩ : syracuseStep 4241429 = 198817) (by norm_num)
theorem B2152469 : Blo 1256446 2152469 := bbase (se 6 (by rfl) ⟨50448, by rfl⟩ : syracuseStep 2152469 = 100897) (by norm_num)
theorem B1415209 : Blo 1256446 1415209 := bbase (se 2 (by rfl) ⟨530703, by rfl⟩ : syracuseStep 1415209 = 1061407) (by norm_num)
theorem B1415245 : Blo 1256446 1415245 := bbase (se 3 (by rfl) ⟨265358, by rfl⟩ : syracuseStep 1415245 = 530717) (by norm_num)
theorem B3184717 : Blo 1256446 3184717 := bbase (se 3 (by rfl) ⟨597134, by rfl⟩ : syracuseStep 3184717 = 1194269) (by norm_num)
theorem B1415281 : Blo 1256446 1415281 := bbase (se 2 (by rfl) ⟨530730, by rfl⟩ : syracuseStep 1415281 = 1061461) (by norm_num)
theorem B1702013 : Blo 1256446 1702013 := bbase (se 3 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 1702013 = 638255) (by norm_num)
theorem B3061901 : Blo 1256446 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B13596821 : Blo 1256446 13596821 := bbase (se 6 (by rfl) ⟨318675, by rfl⟩ : syracuseStep 13596821 = 637351) (by norm_num)
theorem B1415317 : Blo 1256446 1415317 := bbase (se 6 (by rfl) ⟨33171, by rfl⟩ : syracuseStep 1415317 = 66343) (by norm_num)
theorem B1415353 : Blo 1256446 1415353 := bbase (se 2 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 1415353 = 1061515) (by norm_num)
theorem B3184829 : Blo 1256446 3184829 := bbase (se 3 (by rfl) ⟨597155, by rfl⟩ : syracuseStep 3184829 = 1194311) (by norm_num)
theorem B4774085 : Blo 1256446 4774085 := bbase (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) (by norm_num)
theorem B3578069 : Blo 1256446 3578069 := bbase (se 7 (by rfl) ⟨41930, by rfl⟩ : syracuseStep 3578069 = 83861) (by norm_num)
theorem B1415389 : Blo 1256446 1415389 := bbase (se 3 (by rfl) ⟨265385, by rfl⟩ : syracuseStep 1415389 = 530771) (by norm_num)
theorem B1415425 : Blo 1256446 1415425 := bbase (se 2 (by rfl) ⟨530784, by rfl⟩ : syracuseStep 1415425 = 1061569) (by norm_num)
theorem B1415461 : Blo 1256446 1415461 := bbase (se 4 (by rfl) ⟨132699, by rfl⟩ : syracuseStep 1415461 = 265399) (by norm_num)
theorem B1415497 : Blo 1256446 1415497 := bbase (se 2 (by rfl) ⟨530811, by rfl⟩ : syracuseStep 1415497 = 1061623) (by norm_num)
theorem B1341793 : Blo 1256446 1341793 := bbase (se 2 (by rfl) ⟨503172, by rfl⟩ : syracuseStep 1341793 = 1006345) (by norm_num)
theorem B3823973 : Blo 1256446 3823973 := bbase (se 4 (by rfl) ⟨358497, by rfl⟩ : syracuseStep 3823973 = 716995) (by norm_num)
theorem B1415533 : Blo 1256446 1415533 := bbase (se 3 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 1415533 = 530825) (by norm_num)
theorem B3185021 : Blo 1256446 3185021 := bbase (se 3 (by rfl) ⟨597191, by rfl⟩ : syracuseStep 3185021 = 1194383) (by norm_num)
theorem B1415569 : Blo 1256446 1415569 := bbase (se 2 (by rfl) ⟨530838, by rfl⟩ : syracuseStep 1415569 = 1061677) (by norm_num)
theorem B1415605 : Blo 1256446 1415605 := bbase (se 5 (by rfl) ⟨66356, by rfl⟩ : syracuseStep 1415605 = 132713) (by norm_num)
theorem B4241861 : Blo 1256446 4241861 := bbase (se 4 (by rfl) ⟨397674, by rfl⟩ : syracuseStep 4241861 = 795349) (by norm_num)
theorem B1415641 : Blo 1256446 1415641 := bbase (se 2 (by rfl) ⟨530865, by rfl⟩ : syracuseStep 1415641 = 1061731) (by norm_num)
theorem B4774373 : Blo 1256446 4774373 := bbase (se 4 (by rfl) ⟨447597, by rfl⟩ : syracuseStep 4774373 = 895195) (by norm_num)
theorem B2013677 : Blo 1256446 2013677 := bbase (se 3 (by rfl) ⟨377564, by rfl⟩ : syracuseStep 2013677 = 755129) (by norm_num)
theorem B1415677 : Blo 1256446 1415677 := bbase (se 3 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 1415677 = 530879) (by norm_num)
theorem B5896709 : Blo 1256446 5896709 := bbase (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) (by norm_num)
theorem B1415713 : Blo 1256446 1415713 := bbase (se 2 (by rfl) ⟨530892, by rfl⟩ : syracuseStep 1415713 = 1061785) (by norm_num)
theorem B5167685 : Blo 1256446 5167685 := bbase (se 4 (by rfl) ⟨484470, by rfl⟩ : syracuseStep 5167685 = 968941) (by norm_num)
theorem B1415749 : Blo 1256446 1415749 := bbase (se 4 (by rfl) ⟨132726, by rfl⟩ : syracuseStep 1415749 = 265453) (by norm_num)
theorem B2120269 : Blo 1256446 2120269 := bbase (se 3 (by rfl) ⟨397550, by rfl⟩ : syracuseStep 2120269 = 795101) (by norm_num)
theorem B2120357 : Blo 1256446 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B2013869 : Blo 1256446 2013869 := bbase (se 3 (by rfl) ⟨377600, by rfl⟩ : syracuseStep 2013869 = 755201) (by norm_num)
theorem B2685629 : Blo 1256446 2685629 := bbase (se 3 (by rfl) ⟨503555, by rfl⟩ : syracuseStep 2685629 = 1007111) (by norm_num)
theorem B6363845 : Blo 1256446 6363845 := bbase (se 4 (by rfl) ⟨596610, by rfl⟩ : syracuseStep 6363845 = 1193221) (by norm_num)
theorem B1342165 : Blo 1256446 1342165 := bbase (se 7 (by rfl) ⟨15728, by rfl⟩ : syracuseStep 1342165 = 31457) (by norm_num)
theorem B3185365 : Blo 1256446 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B4528885 : Blo 1256446 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B4029173 : Blo 1256446 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B2120485 : Blo 1256446 2120485 := bbase (se 4 (by rfl) ⟨198795, by rfl⟩ : syracuseStep 2120485 = 397591) (by norm_num)
theorem B2013997 : Blo 1256446 2013997 := bbase (se 3 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 2013997 = 755249) (by norm_num)
theorem B2685773 : Blo 1256446 2685773 := bbase (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) (by norm_num)
theorem B4242293 : Blo 1256446 4242293 := bbase (se 5 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 4242293 = 397715) (by norm_num)
theorem B2120573 : Blo 1256446 2120573 := bbase (se 3 (by rfl) ⟨397607, by rfl⟩ : syracuseStep 2120573 = 795215) (by norm_num)
theorem B4029365 : Blo 1256446 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B2866109 : Blo 1256446 2866109 := bbase (se 3 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 2866109 = 1074791) (by norm_num)
theorem B5815253 : Blo 1256446 5815253 := bbase (se 7 (by rfl) ⟨68147, by rfl⟩ : syracuseStep 5815253 = 136295) (by norm_num)
theorem B2120701 : Blo 1256446 2120701 := bbase (se 3 (by rfl) ⟨397631, by rfl⟩ : syracuseStep 2120701 = 795263) (by norm_num)
theorem B1342541 : Blo 1256446 1342541 := bbase (se 3 (by rfl) ⟨251726, by rfl⟩ : syracuseStep 1342541 = 503453) (by norm_num)
theorem B2120789 : Blo 1256446 2120789 := bbase (se 8 (by rfl) ⟨12426, by rfl⟩ : syracuseStep 2120789 = 24853) (by norm_num)
theorem B3398773 : Blo 1256446 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B1342613 : Blo 1256446 1342613 := bbase (se 6 (by rfl) ⟨31467, by rfl⟩ : syracuseStep 1342613 = 62935) (by norm_num)
theorem B2120917 : Blo 1256446 2120917 := bbase (se 7 (by rfl) ⟨24854, by rfl⟩ : syracuseStep 2120917 = 49709) (by norm_num)
theorem B11476181 : Blo 1256446 11476181 := bbase (se 7 (by rfl) ⟨134486, by rfl⟩ : syracuseStep 11476181 = 268973) (by norm_num)
theorem B4242725 : Blo 1256446 4242725 := bbase (se 4 (by rfl) ⟨397755, by rfl⟩ : syracuseStep 4242725 = 795511) (by norm_num)
theorem B2121005 : Blo 1256446 2121005 := bbase (se 3 (by rfl) ⟨397688, by rfl⟩ : syracuseStep 2121005 = 795377) (by norm_num)
theorem B1342801 : Blo 1256446 1342801 := bbase (se 2 (by rfl) ⟨503550, by rfl⟩ : syracuseStep 1342801 = 1007101) (by norm_num)
theorem B6045029 : Blo 1256446 6045029 := bbase (se 4 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 6045029 = 1133443) (by norm_num)
theorem B3063149 : Blo 1256446 3063149 := bbase (se 3 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 3063149 = 1148681) (by norm_num)
theorem B2121133 : Blo 1256446 2121133 := bbase (se 3 (by rfl) ⟨397712, by rfl⟩ : syracuseStep 2121133 = 795425) (by norm_num)
theorem B2014637 : Blo 1256446 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B1433009 : Blo 1256446 1433009 := bbase (se 2 (by rfl) ⟨537378, by rfl⟩ : syracuseStep 1433009 = 1074757) (by norm_num)
theorem B2121221 : Blo 1256446 2121221 := bbase (se 4 (by rfl) ⟨198864, by rfl⟩ : syracuseStep 2121221 = 397729) (by norm_num)
theorem B1342985 : Blo 1256446 1342985 := bbase (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) (by norm_num)
theorem B2686517 : Blo 1256446 2686517 := bbase (se 5 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 2686517 = 251861) (by norm_num)
theorem B2121349 : Blo 1256446 2121349 := bbase (se 4 (by rfl) ⟨198876, by rfl⟩ : syracuseStep 2121349 = 397753) (by norm_num)
theorem B4775557 : Blo 1256446 4775557 := bbase (se 4 (by rfl) ⟨447708, by rfl⟩ : syracuseStep 4775557 = 895417) (by norm_num)
theorem B1613449 : Blo 1256446 1613449 := bbase (se 2 (by rfl) ⟨605043, by rfl⟩ : syracuseStep 1613449 = 1210087) (by norm_num)
theorem B4243157 : Blo 1256446 4243157 := bbase (se 7 (by rfl) ⟨49724, by rfl⟩ : syracuseStep 4243157 = 99449) (by norm_num)
theorem B15302357 : Blo 1256446 15302357 := bbase (se 7 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 15302357 = 358649) (by norm_num)
theorem B2121437 : Blo 1256446 2121437 := bbase (se 3 (by rfl) ⟨397769, by rfl⟩ : syracuseStep 2121437 = 795539) (by norm_num)
theorem B3579653 : Blo 1256446 3579653 := bbase (se 4 (by rfl) ⟨335592, by rfl⟩ : syracuseStep 3579653 = 671185) (by norm_num)
theorem B2121565 : Blo 1256446 2121565 := bbase (se 3 (by rfl) ⟨397793, by rfl⟩ : syracuseStep 2121565 = 795587) (by norm_num)
theorem B2015093 : Blo 1256446 2015093 := bbase (se 5 (by rfl) ⟨94457, by rfl⟩ : syracuseStep 2015093 = 188915) (by norm_num)
theorem B2547605 : Blo 1256446 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B2121653 : Blo 1256446 2121653 := bbase (se 5 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 2121653 = 198905) (by norm_num)
theorem B4775861 : Blo 1256446 4775861 := bbase (se 5 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 4775861 = 447737) (by norm_num)
theorem B6365141 : Blo 1256446 6365141 := bbase (se 7 (by rfl) ⟨74591, by rfl⟩ : syracuseStep 6365141 = 149183) (by norm_num)
theorem B14327765 : Blo 1256446 14327765 := bbase (se 7 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 14327765 = 335807) (by norm_num)
theorem B2121761 : Blo 1256446 2121761 := bstep (se 2 (by rfl) ⟨795660, by rfl⟩ : syracuseStep 2121761 = 1591321) B1591321
theorem B2687089 : Blo 1256446 2687089 := bstep (se 2 (by rfl) ⟨1007658, by rfl⟩ : syracuseStep 2687089 = 2015317) B2015317
theorem B2121889 : Blo 1256446 2121889 := bstep (se 2 (by rfl) ⟨795708, by rfl⟩ : syracuseStep 2121889 = 1591417) B1591417
theorem B5234851 : Blo 1256446 5234851 := bstep (se 1 (by rfl) ⟨3926138, by rfl⟩ : syracuseStep 5234851 = 7852277) B7852277
theorem B3629233 : Blo 1256446 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B2867395 : Blo 1256446 2867395 := bstep (se 1 (by rfl) ⟨2150546, by rfl⟩ : syracuseStep 2867395 = 4301093) B4301093
theorem B2121923 : Blo 1256446 2121923 := bstep (se 1 (by rfl) ⟨1591442, by rfl⟩ : syracuseStep 2121923 = 3182885) B3182885
theorem B3580109 : Blo 1256446 3580109 := bstep (se 3 (by rfl) ⟨671270, by rfl⟩ : syracuseStep 3580109 = 1342541) B1342541
theorem B1745107 : Blo 1256446 1745107 := bstep (se 1 (by rfl) ⟨1308830, by rfl⟩ : syracuseStep 1745107 = 2617661) B2617661
theorem B4243697 : Blo 1256446 4243697 := bstep (se 2 (by rfl) ⟨1591386, by rfl⟩ : syracuseStep 4243697 = 3182773) B3182773
theorem B2122051 : Blo 1256446 2122051 := bstep (se 1 (by rfl) ⟨1591538, by rfl⟩ : syracuseStep 2122051 = 3183077) B3183077
theorem B4538701 : Blo 1256446 4538701 := bstep (se 3 (by rfl) ⟨851006, by rfl⟩ : syracuseStep 4538701 = 1702013) B1702013
theorem B2687345 : Blo 1256446 2687345 := bstep (se 2 (by rfl) ⟨1007754, by rfl⟩ : syracuseStep 2687345 = 2015509) B2015509
theorem B3580301 : Blo 1256446 3580301 := bstep (se 3 (by rfl) ⟨671306, by rfl⟩ : syracuseStep 3580301 = 1342613) B1342613
theorem B5374349 : Blo 1256446 5374349 := bstep (se 3 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 5374349 = 2015381) B2015381
theorem B2122193 : Blo 1256446 2122193 := bstep (se 2 (by rfl) ⟨795822, by rfl⟩ : syracuseStep 2122193 = 1591645) B1591645
theorem B1884689 : Blo 1256446 1884689 := bstep (se 2 (by rfl) ⟨706758, by rfl⟩ : syracuseStep 1884689 = 1413517) B1413517
theorem B1884707 : Blo 1256446 1884707 := bstep (se 1 (by rfl) ⟨1413530, by rfl⟩ : syracuseStep 1884707 = 2827061) B2827061
theorem B1884737 : Blo 1256446 1884737 := bstep (se 2 (by rfl) ⟨706776, by rfl⟩ : syracuseStep 1884737 = 1413553) B1413553
theorem B10199621 : Blo 1256446 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B2122321 : Blo 1256446 2122321 := bstep (se 2 (by rfl) ⟨795870, by rfl⟩ : syracuseStep 2122321 = 1591741) B1591741
theorem B1884755 : Blo 1256446 1884755 := bstep (se 1 (by rfl) ⟨1413566, by rfl⟩ : syracuseStep 1884755 = 2827133) B2827133
theorem B1884785 : Blo 1256446 1884785 := bstep (se 2 (by rfl) ⟨706794, by rfl⟩ : syracuseStep 1884785 = 1413589) B1413589
theorem B2122355 : Blo 1256446 2122355 := bstep (se 1 (by rfl) ⟨1591766, by rfl⟩ : syracuseStep 2122355 = 3183533) B3183533
theorem B1884803 : Blo 1256446 1884803 := bstep (se 1 (by rfl) ⟨1413602, by rfl⟩ : syracuseStep 1884803 = 2827205) B2827205
theorem B1884833 : Blo 1256446 1884833 := bstep (se 2 (by rfl) ⟨706812, by rfl⟩ : syracuseStep 1884833 = 1413625) B1413625
theorem B1884851 : Blo 1256446 1884851 := bstep (se 1 (by rfl) ⟨1413638, by rfl⟩ : syracuseStep 1884851 = 2827277) B2827277
theorem B1884881 : Blo 1256446 1884881 := bstep (se 2 (by rfl) ⟨706830, by rfl⟩ : syracuseStep 1884881 = 1413661) B1413661
theorem B1884899 : Blo 1256446 1884899 := bstep (se 1 (by rfl) ⟨1413674, by rfl⟩ : syracuseStep 1884899 = 2827349) B2827349
theorem B2122483 : Blo 1256446 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B1884929 : Blo 1256446 1884929 := bstep (se 2 (by rfl) ⟨706848, by rfl⟩ : syracuseStep 1884929 = 1413697) B1413697
theorem B4244237 : Blo 1256446 4244237 := bstep (se 3 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 4244237 = 1591589) B1591589
theorem B2827025 : Blo 1256446 2827025 := bstep (se 2 (by rfl) ⟨1060134, by rfl⟩ : syracuseStep 2827025 = 2120269) B2120269
theorem B1884947 : Blo 1256446 1884947 := bstep (se 1 (by rfl) ⟨1413710, by rfl⟩ : syracuseStep 1884947 = 2827421) B2827421
theorem B2827043 : Blo 1256446 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B1884977 : Blo 1256446 1884977 := bstep (se 2 (by rfl) ⟨706866, by rfl⟩ : syracuseStep 1884977 = 1413733) B1413733
theorem B1884995 : Blo 1256446 1884995 := bstep (se 1 (by rfl) ⟨1413746, by rfl⟩ : syracuseStep 1884995 = 2827493) B2827493
theorem B4244291 : Blo 1256446 4244291 := bstep (se 1 (by rfl) ⟨3183218, by rfl⟩ : syracuseStep 4244291 = 6366437) B6366437
theorem B1885025 : Blo 1256446 1885025 := bstep (se 2 (by rfl) ⟨706884, by rfl⟩ : syracuseStep 1885025 = 1413769) B1413769
theorem B4776803 : Blo 1256446 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B1885043 : Blo 1256446 1885043 := bstep (se 1 (by rfl) ⟨1413782, by rfl⟩ : syracuseStep 1885043 = 2827565) B2827565
theorem B2122625 : Blo 1256446 2122625 := bstep (se 2 (by rfl) ⟨795984, by rfl⟩ : syracuseStep 2122625 = 1591969) B1591969
theorem B1885073 : Blo 1256446 1885073 := bstep (se 2 (by rfl) ⟨706902, by rfl⟩ : syracuseStep 1885073 = 1413805) B1413805
theorem B1885091 : Blo 1256446 1885091 := bstep (se 1 (by rfl) ⟨1413818, by rfl⟩ : syracuseStep 1885091 = 2827637) B2827637
theorem B1885121 : Blo 1256446 1885121 := bstep (se 2 (by rfl) ⟨706920, by rfl⟩ : syracuseStep 1885121 = 1413841) B1413841
theorem B3400643 : Blo 1256446 3400643 := bstep (se 1 (by rfl) ⟨2550482, by rfl⟩ : syracuseStep 3400643 = 5100965) B5100965
theorem B1885139 : Blo 1256446 1885139 := bstep (se 1 (by rfl) ⟨1413854, by rfl⟩ : syracuseStep 1885139 = 2827709) B2827709
theorem B6038513 : Blo 1256446 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B1885169 : Blo 1256446 1885169 := bstep (se 2 (by rfl) ⟨706938, by rfl⟩ : syracuseStep 1885169 = 1413877) B1413877
theorem B2122753 : Blo 1256446 2122753 := bstep (se 2 (by rfl) ⟨796032, by rfl⟩ : syracuseStep 2122753 = 1592065) B1592065
theorem B1885187 : Blo 1256446 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B1885217 : Blo 1256446 1885217 := bstep (se 2 (by rfl) ⟨706956, by rfl⟩ : syracuseStep 1885217 = 1413913) B1413913
theorem B2122787 : Blo 1256446 2122787 := bstep (se 1 (by rfl) ⟨1592090, by rfl⟩ : syracuseStep 2122787 = 3184181) B3184181
theorem B2827313 : Blo 1256446 2827313 := bstep (se 2 (by rfl) ⟨1060242, by rfl⟩ : syracuseStep 2827313 = 2120485) B2120485
theorem B1885235 : Blo 1256446 1885235 := bstep (se 1 (by rfl) ⟨1413926, by rfl⟩ : syracuseStep 1885235 = 2827853) B2827853
theorem B2827331 : Blo 1256446 2827331 := bstep (se 1 (by rfl) ⟨2120498, by rfl⟩ : syracuseStep 2827331 = 4240997) B4240997
theorem B1885265 : Blo 1256446 1885265 := bstep (se 2 (by rfl) ⟨706974, by rfl⟩ : syracuseStep 1885265 = 1413949) B1413949
theorem B4244561 : Blo 1256446 4244561 := bstep (se 2 (by rfl) ⟨1591710, by rfl⟩ : syracuseStep 4244561 = 3183421) B3183421
theorem B1885283 : Blo 1256446 1885283 := bstep (se 1 (by rfl) ⟨1413962, by rfl⟩ : syracuseStep 1885283 = 2827925) B2827925
theorem B1885313 : Blo 1256446 1885313 := bstep (se 2 (by rfl) ⟨706992, by rfl⟩ : syracuseStep 1885313 = 1413985) B1413985
theorem B25805965 : Blo 1256446 25805965 := bstep (se 3 (by rfl) ⟨4838618, by rfl⟩ : syracuseStep 25805965 = 9677237) B9677237
theorem B1885331 : Blo 1256446 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B2122915 : Blo 1256446 2122915 := bstep (se 1 (by rfl) ⟨1592186, by rfl⟩ : syracuseStep 2122915 = 3184373) B3184373
theorem B1885361 : Blo 1256446 1885361 := bstep (se 2 (by rfl) ⟨707010, by rfl⟩ : syracuseStep 1885361 = 1414021) B1414021
theorem B8053937 : Blo 1256446 8053937 := bstep (se 2 (by rfl) ⟨3020226, by rfl⟩ : syracuseStep 8053937 = 6040453) B6040453
theorem B1885379 : Blo 1256446 1885379 := bstep (se 1 (by rfl) ⟨1414034, by rfl⟩ : syracuseStep 1885379 = 2828069) B2828069
theorem B1885409 : Blo 1256446 1885409 := bstep (se 2 (by rfl) ⟨707028, by rfl⟩ : syracuseStep 1885409 = 1414057) B1414057
theorem B1885427 : Blo 1256446 1885427 := bstep (se 1 (by rfl) ⟨1414070, by rfl⟩ : syracuseStep 1885427 = 2828141) B2828141
theorem B1885457 : Blo 1256446 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B1885475 : Blo 1256446 1885475 := bstep (se 1 (by rfl) ⟨1414106, by rfl⟩ : syracuseStep 1885475 = 2828213) B2828213
theorem B2123057 : Blo 1256446 2123057 := bstep (se 2 (by rfl) ⟨796146, by rfl⟩ : syracuseStep 2123057 = 1592293) B1592293
theorem B1885505 : Blo 1256446 1885505 := bstep (se 2 (by rfl) ⟨707064, by rfl⟩ : syracuseStep 1885505 = 1414129) B1414129
theorem B2827601 : Blo 1256446 2827601 := bstep (se 2 (by rfl) ⟨1060350, by rfl⟩ : syracuseStep 2827601 = 2120701) B2120701
theorem B1885523 : Blo 1256446 1885523 := bstep (se 1 (by rfl) ⟨1414142, by rfl⟩ : syracuseStep 1885523 = 2828285) B2828285
theorem B2827619 : Blo 1256446 2827619 := bstep (se 1 (by rfl) ⟨2120714, by rfl⟩ : syracuseStep 2827619 = 4241429) B4241429
theorem B1434979 : Blo 1256446 1434979 := bstep (se 1 (by rfl) ⟨1076234, by rfl⟩ : syracuseStep 1434979 = 2152469) B2152469
theorem B3581293 : Blo 1256446 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B1885553 : Blo 1256446 1885553 := bstep (se 2 (by rfl) ⟨707082, by rfl⟩ : syracuseStep 1885553 = 1414165) B1414165
theorem B1885571 : Blo 1256446 1885571 := bstep (se 1 (by rfl) ⟨1414178, by rfl⟩ : syracuseStep 1885571 = 2828357) B2828357
theorem B1885601 : Blo 1256446 1885601 := bstep (se 2 (by rfl) ⟨707100, by rfl⟩ : syracuseStep 1885601 = 1414201) B1414201
theorem B2123185 : Blo 1256446 2123185 := bstep (se 2 (by rfl) ⟨796194, by rfl⟩ : syracuseStep 2123185 = 1592389) B1592389
theorem B1885619 : Blo 1256446 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B1885649 : Blo 1256446 1885649 := bstep (se 2 (by rfl) ⟨707118, by rfl⟩ : syracuseStep 1885649 = 1414237) B1414237
theorem B2123219 : Blo 1256446 2123219 := bstep (se 1 (by rfl) ⟨1592414, by rfl⟩ : syracuseStep 2123219 = 3184829) B3184829
theorem B2385379 : Blo 1256446 2385379 := bstep (se 1 (by rfl) ⟨1789034, by rfl⟩ : syracuseStep 2385379 = 3578069) B3578069
theorem B10192355 : Blo 1256446 10192355 := bstep (se 1 (by rfl) ⟨7644266, by rfl⟩ : syracuseStep 10192355 = 15288533) B15288533
theorem B1885667 : Blo 1256446 1885667 := bstep (se 1 (by rfl) ⟨1414250, by rfl⟩ : syracuseStep 1885667 = 2828501) B2828501
theorem B4531697 : Blo 1256446 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B1885697 : Blo 1256446 1885697 := bstep (se 2 (by rfl) ⟨707136, by rfl⟩ : syracuseStep 1885697 = 1414273) B1414273
theorem B13780493 : Blo 1256446 13780493 := bstep (se 3 (by rfl) ⟨2583842, by rfl⟩ : syracuseStep 13780493 = 5167685) B5167685
theorem B2385425 : Blo 1256446 2385425 := bstep (se 2 (by rfl) ⟨894534, by rfl⟩ : syracuseStep 2385425 = 1789069) B1789069
theorem B1885715 : Blo 1256446 1885715 := bstep (se 1 (by rfl) ⟨1414286, by rfl⟩ : syracuseStep 1885715 = 2828573) B2828573
theorem B1885745 : Blo 1256446 1885745 := bstep (se 2 (by rfl) ⟨707154, by rfl⟩ : syracuseStep 1885745 = 1414309) B1414309
theorem B1590835 : Blo 1256446 1590835 := bstep (se 1 (by rfl) ⟨1193126, by rfl⟩ : syracuseStep 1590835 = 2386253) B2386253
theorem B20383285 : Blo 1256446 20383285 := bstep (se 5 (by rfl) ⟨955466, by rfl⟩ : syracuseStep 20383285 = 1910933) B1910933
theorem B1885763 : Blo 1256446 1885763 := bstep (se 1 (by rfl) ⟨1414322, by rfl⟩ : syracuseStep 1885763 = 2828645) B2828645
theorem B2549315 : Blo 1256446 2549315 := bstep (se 1 (by rfl) ⟨1911986, by rfl⟩ : syracuseStep 2549315 = 3823973) B3823973
theorem B2123347 : Blo 1256446 2123347 := bstep (se 1 (by rfl) ⟨1592510, by rfl⟩ : syracuseStep 2123347 = 3185021) B3185021
theorem B1885793 : Blo 1256446 1885793 := bstep (se 2 (by rfl) ⟨707172, by rfl⟩ : syracuseStep 1885793 = 1414345) B1414345
theorem B4245101 : Blo 1256446 4245101 := bstep (se 3 (by rfl) ⟨795956, by rfl⟩ : syracuseStep 4245101 = 1591913) B1591913
theorem B2827889 : Blo 1256446 2827889 := bstep (se 2 (by rfl) ⟨1060458, by rfl⟩ : syracuseStep 2827889 = 2120917) B2120917
theorem B1885811 : Blo 1256446 1885811 := bstep (se 1 (by rfl) ⟨1414358, by rfl⟩ : syracuseStep 1885811 = 2828717) B2828717
theorem B2827907 : Blo 1256446 2827907 := bstep (se 1 (by rfl) ⟨2120930, by rfl⟩ : syracuseStep 2827907 = 4241861) B4241861
theorem B1885841 : Blo 1256446 1885841 := bstep (se 2 (by rfl) ⟨707190, by rfl⟩ : syracuseStep 1885841 = 1414381) B1414381
theorem B1590931 : Blo 1256446 1590931 := bstep (se 1 (by rfl) ⟨1193198, by rfl⟩ : syracuseStep 1590931 = 2386397) B2386397
theorem B1885859 : Blo 1256446 1885859 := bstep (se 1 (by rfl) ⟨1414394, by rfl⟩ : syracuseStep 1885859 = 2828789) B2828789
theorem B4245155 : Blo 1256446 4245155 := bstep (se 1 (by rfl) ⟨3183866, by rfl⟩ : syracuseStep 4245155 = 6367733) B6367733
theorem B2098867 : Blo 1256446 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B1885889 : Blo 1256446 1885889 := bstep (se 2 (by rfl) ⟨707208, by rfl⟩ : syracuseStep 1885889 = 1414417) B1414417
theorem B1885907 : Blo 1256446 1885907 := bstep (se 1 (by rfl) ⟨1414430, by rfl⟩ : syracuseStep 1885907 = 2828861) B2828861
theorem B2123489 : Blo 1256446 2123489 := bstep (se 2 (by rfl) ⟨796308, by rfl⟩ : syracuseStep 2123489 = 1592617) B1592617
theorem B1885937 : Blo 1256446 1885937 := bstep (se 2 (by rfl) ⟨707226, by rfl⟩ : syracuseStep 1885937 = 1414453) B1414453
theorem B1885955 : Blo 1256446 1885955 := bstep (se 1 (by rfl) ⟨1414466, by rfl⟩ : syracuseStep 1885955 = 2828933) B2828933
theorem B7161605 : Blo 1256446 7161605 := bstep (se 4 (by rfl) ⟨671400, by rfl⟩ : syracuseStep 7161605 = 1342801) B1342801
theorem B1885985 : Blo 1256446 1885985 := bstep (se 2 (by rfl) ⟨707244, by rfl⟩ : syracuseStep 1885985 = 1414489) B1414489
theorem B2385713 : Blo 1256446 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B1886003 : Blo 1256446 1886003 := bstep (se 1 (by rfl) ⟨1414502, by rfl⟩ : syracuseStep 1886003 = 2829005) B2829005
theorem B21489461 : Blo 1256446 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B4777805 : Blo 1256446 4777805 := bstep (se 3 (by rfl) ⟨895838, by rfl⟩ : syracuseStep 4777805 = 1791677) B1791677
theorem B4417361 : Blo 1256446 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B1886033 : Blo 1256446 1886033 := bstep (se 2 (by rfl) ⟨707262, by rfl⟩ : syracuseStep 1886033 = 1414525) B1414525
theorem B2123617 : Blo 1256446 2123617 := bstep (se 2 (by rfl) ⟨796356, by rfl⟩ : syracuseStep 2123617 = 1592713) B1592713
theorem B1886051 : Blo 1256446 1886051 := bstep (se 1 (by rfl) ⟨1414538, by rfl⟩ : syracuseStep 1886051 = 2829077) B2829077
theorem B1886081 : Blo 1256446 1886081 := bstep (se 2 (by rfl) ⟨707280, by rfl⟩ : syracuseStep 1886081 = 1414561) B1414561
theorem B2828177 : Blo 1256446 2828177 := bstep (se 2 (by rfl) ⟨1060566, by rfl⟩ : syracuseStep 2828177 = 2121133) B2121133
theorem B1886099 : Blo 1256446 1886099 := bstep (se 1 (by rfl) ⟨1414574, by rfl⟩ : syracuseStep 1886099 = 2829149) B2829149
theorem B2828195 : Blo 1256446 2828195 := bstep (se 1 (by rfl) ⟨2121146, by rfl⟩ : syracuseStep 2828195 = 4242293) B4242293
theorem B1886129 : Blo 1256446 1886129 := bstep (se 2 (by rfl) ⟨707298, by rfl⟩ : syracuseStep 1886129 = 1414597) B1414597
theorem B4245425 : Blo 1256446 4245425 := bstep (se 2 (by rfl) ⟨1592034, by rfl⟩ : syracuseStep 4245425 = 3184069) B3184069
theorem B1886147 : Blo 1256446 1886147 := bstep (se 1 (by rfl) ⟨1414610, by rfl⟩ : syracuseStep 1886147 = 2829221) B2829221
theorem B1886177 : Blo 1256446 1886177 := bstep (se 2 (by rfl) ⟨707316, by rfl⟩ : syracuseStep 1886177 = 1414633) B1414633
theorem B3876835 : Blo 1256446 3876835 := bstep (se 1 (by rfl) ⟨2907626, by rfl⟩ : syracuseStep 3876835 = 5815253) B5815253
theorem B1886195 : Blo 1256446 1886195 := bstep (se 1 (by rfl) ⟨1414646, by rfl⟩ : syracuseStep 1886195 = 2829293) B2829293
theorem B1886225 : Blo 1256446 1886225 := bstep (se 2 (by rfl) ⟨707334, by rfl⟩ : syracuseStep 1886225 = 1414669) B1414669
theorem B1886243 : Blo 1256446 1886243 := bstep (se 1 (by rfl) ⟨1414682, by rfl⟩ : syracuseStep 1886243 = 2829365) B2829365
theorem B1886273 : Blo 1256446 1886273 := bstep (se 2 (by rfl) ⟨707352, by rfl⟩ : syracuseStep 1886273 = 1414705) B1414705
theorem B14526533 : Blo 1256446 14526533 := bstep (se 4 (by rfl) ⟨1361862, by rfl⟩ : syracuseStep 14526533 = 2723725) B2723725
theorem B1886291 : Blo 1256446 1886291 := bstep (se 1 (by rfl) ⟨1414718, by rfl⟩ : syracuseStep 1886291 = 2829437) B2829437
theorem B1886321 : Blo 1256446 1886321 := bstep (se 2 (by rfl) ⟨707370, by rfl⟩ : syracuseStep 1886321 = 1414741) B1414741
theorem B1591427 : Blo 1256446 1591427 := bstep (se 1 (by rfl) ⟨1193570, by rfl⟩ : syracuseStep 1591427 = 2387141) B2387141
theorem B1886339 : Blo 1256446 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B1886369 : Blo 1256446 1886369 := bstep (se 2 (by rfl) ⟨707388, by rfl⟩ : syracuseStep 1886369 = 1414777) B1414777
theorem B2828465 : Blo 1256446 2828465 := bstep (se 2 (by rfl) ⟨1060674, by rfl⟩ : syracuseStep 2828465 = 2121349) B2121349
theorem B6367409 : Blo 1256446 6367409 := bstep (se 2 (by rfl) ⟨2387778, by rfl⟩ : syracuseStep 6367409 = 4775557) B4775557
theorem B1886387 : Blo 1256446 1886387 := bstep (se 1 (by rfl) ⟨1414790, by rfl⟩ : syracuseStep 1886387 = 2829581) B2829581
theorem B2828483 : Blo 1256446 2828483 := bstep (se 1 (by rfl) ⟨2121362, by rfl⟩ : syracuseStep 2828483 = 4242725) B4242725
theorem B1886417 : Blo 1256446 1886417 := bstep (se 2 (by rfl) ⟨707406, by rfl⟩ : syracuseStep 1886417 = 1414813) B1414813
theorem B1886435 : Blo 1256446 1886435 := bstep (se 1 (by rfl) ⟨1414826, by rfl⟩ : syracuseStep 1886435 = 2829653) B2829653
theorem B2042099 : Blo 1256446 2042099 := bstep (se 1 (by rfl) ⟨1531574, by rfl⟩ : syracuseStep 2042099 = 3063149) B3063149
theorem B1886465 : Blo 1256446 1886465 := bstep (se 2 (by rfl) ⟨707424, by rfl⟩ : syracuseStep 1886465 = 1414849) B1414849
theorem B14321933 : Blo 1256446 14321933 := bstep (se 3 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 14321933 = 5370725) B5370725
theorem B1886483 : Blo 1256446 1886483 := bstep (se 1 (by rfl) ⟨1414862, by rfl⟩ : syracuseStep 1886483 = 2829725) B2829725
theorem B1886513 : Blo 1256446 1886513 := bstep (se 2 (by rfl) ⟨707442, by rfl⟩ : syracuseStep 1886513 = 1414885) B1414885
theorem B1886531 : Blo 1256446 1886531 := bstep (se 1 (by rfl) ⟨1414898, by rfl⟩ : syracuseStep 1886531 = 2829797) B2829797
theorem B1886561 : Blo 1256446 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B1886579 : Blo 1256446 1886579 := bstep (se 1 (by rfl) ⟨1414934, by rfl⟩ : syracuseStep 1886579 = 2829869) B2829869
theorem B1886609 : Blo 1256446 1886609 := bstep (se 2 (by rfl) ⟨707478, by rfl⟩ : syracuseStep 1886609 = 1414957) B1414957
theorem B1886627 : Blo 1256446 1886627 := bstep (se 1 (by rfl) ⟨1414970, by rfl⟩ : syracuseStep 1886627 = 2829941) B2829941
theorem B7162289 : Blo 1256446 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B1886657 : Blo 1256446 1886657 := bstep (se 2 (by rfl) ⟨707496, by rfl⟩ : syracuseStep 1886657 = 1414993) B1414993
theorem B27576773 : Blo 1256446 27576773 := bstep (se 4 (by rfl) ⟨2585322, by rfl⟩ : syracuseStep 27576773 = 5170645) B5170645
theorem B4245965 : Blo 1256446 4245965 := bstep (se 3 (by rfl) ⟨796118, by rfl⟩ : syracuseStep 4245965 = 1592237) B1592237
theorem B2828753 : Blo 1256446 2828753 := bstep (se 2 (by rfl) ⟨1060782, by rfl⟩ : syracuseStep 2828753 = 2121565) B2121565
theorem B1886675 : Blo 1256446 1886675 := bstep (se 1 (by rfl) ⟨1415006, by rfl⟩ : syracuseStep 1886675 = 2830013) B2830013
theorem B21760483 : Blo 1256446 21760483 := bstep (se 1 (by rfl) ⟨16320362, by rfl⟩ : syracuseStep 21760483 = 32640725) B32640725
theorem B2828771 : Blo 1256446 2828771 := bstep (se 1 (by rfl) ⟨2121578, by rfl⟩ : syracuseStep 2828771 = 4243157) B4243157
theorem B10201571 : Blo 1256446 10201571 := bstep (se 1 (by rfl) ⟨7651178, by rfl⟩ : syracuseStep 10201571 = 15302357) B15302357
theorem B1886705 : Blo 1256446 1886705 := bstep (se 2 (by rfl) ⟨707514, by rfl⟩ : syracuseStep 1886705 = 1415029) B1415029
theorem B2386435 : Blo 1256446 2386435 := bstep (se 1 (by rfl) ⟨1789826, by rfl⟩ : syracuseStep 2386435 = 3579653) B3579653
theorem B1886723 : Blo 1256446 1886723 := bstep (se 1 (by rfl) ⟨1415042, by rfl⟩ : syracuseStep 1886723 = 2830085) B2830085
theorem B4246019 : Blo 1256446 4246019 := bstep (se 1 (by rfl) ⟨3184514, by rfl⟩ : syracuseStep 4246019 = 6369029) B6369029
theorem B1886753 : Blo 1256446 1886753 := bstep (se 2 (by rfl) ⟨707532, by rfl⟩ : syracuseStep 1886753 = 1415065) B1415065
theorem B1886771 : Blo 1256446 1886771 := bstep (se 1 (by rfl) ⟨1415078, by rfl⟩ : syracuseStep 1886771 = 2830157) B2830157
theorem B1886801 : Blo 1256446 1886801 := bstep (se 2 (by rfl) ⟨707550, by rfl⟩ : syracuseStep 1886801 = 1415101) B1415101
theorem B1698403 : Blo 1256446 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B4082275 : Blo 1256446 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B1886819 : Blo 1256446 1886819 := bstep (se 1 (by rfl) ⟨1415114, by rfl⟩ : syracuseStep 1886819 = 2830229) B2830229
theorem B1886849 : Blo 1256446 1886849 := bstep (se 2 (by rfl) ⟨707568, by rfl⟩ : syracuseStep 1886849 = 1415137) B1415137
theorem B1886867 : Blo 1256446 1886867 := bstep (se 1 (by rfl) ⟨1415150, by rfl⟩ : syracuseStep 1886867 = 2830301) B2830301
theorem B1886897 : Blo 1256446 1886897 := bstep (se 2 (by rfl) ⟨707586, by rfl⟩ : syracuseStep 1886897 = 1415173) B1415173
theorem B1886915 : Blo 1256446 1886915 := bstep (se 1 (by rfl) ⟨1415186, by rfl⟩ : syracuseStep 1886915 = 2830373) B2830373
theorem B3181265 : Blo 1256446 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B1886945 : Blo 1256446 1886945 := bstep (se 2 (by rfl) ⟨707604, by rfl⟩ : syracuseStep 1886945 = 1415209) B1415209
theorem B2829041 : Blo 1256446 2829041 := bstep (se 2 (by rfl) ⟨1060890, by rfl⟩ : syracuseStep 2829041 = 2121781) B2121781
theorem B1886963 : Blo 1256446 1886963 := bstep (se 1 (by rfl) ⟨1415222, by rfl⟩ : syracuseStep 1886963 = 2830445) B2830445
theorem B3181315 : Blo 1256446 3181315 := bstep (se 1 (by rfl) ⟨2385986, by rfl⟩ : syracuseStep 3181315 = 4771973) B4771973
theorem B2829059 : Blo 1256446 2829059 := bstep (se 1 (by rfl) ⟨2121794, by rfl⟩ : syracuseStep 2829059 = 4243589) B4243589
theorem B1886993 : Blo 1256446 1886993 := bstep (se 2 (by rfl) ⟨707622, by rfl⟩ : syracuseStep 1886993 = 1415245) B1415245
theorem B4246289 : Blo 1256446 4246289 := bstep (se 2 (by rfl) ⟨1592358, by rfl⟩ : syracuseStep 4246289 = 3184717) B3184717
theorem B1887011 : Blo 1256446 1887011 := bstep (se 1 (by rfl) ⟨1415258, by rfl⟩ : syracuseStep 1887011 = 2830517) B2830517
theorem B1887041 : Blo 1256446 1887041 := bstep (se 2 (by rfl) ⟨707640, by rfl⟩ : syracuseStep 1887041 = 1415281) B1415281
theorem B1592131 : Blo 1256446 1592131 := bstep (se 1 (by rfl) ⟨1194098, by rfl⟩ : syracuseStep 1592131 = 2388197) B2388197
theorem B1887059 : Blo 1256446 1887059 := bstep (se 1 (by rfl) ⟨1415294, by rfl⟩ : syracuseStep 1887059 = 2830589) B2830589
theorem B5368675 : Blo 1256446 5368675 := bstep (se 1 (by rfl) ⟨4026506, by rfl⟩ : syracuseStep 5368675 = 8053013) B8053013
theorem B1887089 : Blo 1256446 1887089 := bstep (se 2 (by rfl) ⟨707658, by rfl⟩ : syracuseStep 1887089 = 1415317) B1415317
theorem B1887107 : Blo 1256446 1887107 := bstep (se 1 (by rfl) ⟨1415330, by rfl⟩ : syracuseStep 1887107 = 2830661) B2830661
theorem B3181457 : Blo 1256446 3181457 := bstep (se 2 (by rfl) ⟨1193046, by rfl⟩ : syracuseStep 3181457 = 2386093) B2386093
theorem B1887137 : Blo 1256446 1887137 := bstep (se 2 (by rfl) ⟨707676, by rfl⟩ : syracuseStep 1887137 = 1415353) B1415353
theorem B1592227 : Blo 1256446 1592227 := bstep (se 1 (by rfl) ⟨1194170, by rfl⟩ : syracuseStep 1592227 = 2388341) B2388341
theorem B2042801 : Blo 1256446 2042801 := bstep (se 2 (by rfl) ⟨766050, by rfl⟩ : syracuseStep 2042801 = 1532101) B1532101
theorem B1887155 : Blo 1256446 1887155 := bstep (se 1 (by rfl) ⟨1415366, by rfl⟩ : syracuseStep 1887155 = 2830733) B2830733
theorem B2386883 : Blo 1256446 2386883 := bstep (se 1 (by rfl) ⟨1790162, by rfl⟩ : syracuseStep 2386883 = 3580325) B3580325
theorem B1887185 : Blo 1256446 1887185 := bstep (se 2 (by rfl) ⟨707694, by rfl⟩ : syracuseStep 1887185 = 1415389) B1415389
theorem B1887203 : Blo 1256446 1887203 := bstep (se 1 (by rfl) ⟨1415402, by rfl⟩ : syracuseStep 1887203 = 2830805) B2830805
theorem B1256451 : Blo 1256446 1256451 := bstep (se 1 (by rfl) ⟨942338, by rfl⟩ : syracuseStep 1256451 = 1884677) B1884677
theorem B1887233 : Blo 1256446 1887233 := bstep (se 2 (by rfl) ⟨707712, by rfl⟩ : syracuseStep 1887233 = 1415425) B1415425
theorem B2829329 : Blo 1256446 2829329 := bstep (se 2 (by rfl) ⟨1060998, by rfl⟩ : syracuseStep 2829329 = 2121997) B2121997
theorem B1256467 : Blo 1256446 1256467 := bstep (se 1 (by rfl) ⟨942350, by rfl⟩ : syracuseStep 1256467 = 1884701) B1884701
theorem B1887251 : Blo 1256446 1887251 := bstep (se 1 (by rfl) ⟨1415438, by rfl⟩ : syracuseStep 1887251 = 2830877) B2830877
theorem B1256483 : Blo 1256446 1256483 := bstep (se 1 (by rfl) ⟨942362, by rfl⟩ : syracuseStep 1256483 = 1884725) B1884725
theorem B1698851 : Blo 1256446 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B2829347 : Blo 1256446 2829347 := bstep (se 1 (by rfl) ⟨2122010, by rfl⟩ : syracuseStep 2829347 = 4244021) B4244021
theorem B1887281 : Blo 1256446 1887281 := bstep (se 2 (by rfl) ⟨707730, by rfl⟩ : syracuseStep 1887281 = 1415461) B1415461
theorem B3583025 : Blo 1256446 3583025 := bstep (se 2 (by rfl) ⟨1343634, by rfl⟩ : syracuseStep 3583025 = 2687269) B2687269
theorem B1256499 : Blo 1256446 1256499 := bstep (se 1 (by rfl) ⟨942374, by rfl⟩ : syracuseStep 1256499 = 1884749) B1884749
theorem B1256515 : Blo 1256446 1256515 := bstep (se 1 (by rfl) ⟨942386, by rfl⟩ : syracuseStep 1256515 = 1884773) B1884773
theorem B1887299 : Blo 1256446 1887299 := bstep (se 1 (by rfl) ⟨1415474, by rfl⟩ : syracuseStep 1887299 = 2830949) B2830949
theorem B1256531 : Blo 1256446 1256531 := bstep (se 1 (by rfl) ⟨942398, by rfl⟩ : syracuseStep 1256531 = 1884797) B1884797
theorem B1887329 : Blo 1256446 1887329 := bstep (se 2 (by rfl) ⟨707748, by rfl⟩ : syracuseStep 1887329 = 1415497) B1415497
theorem B1256547 : Blo 1256446 1256547 := bstep (se 1 (by rfl) ⟨942410, by rfl⟩ : syracuseStep 1256547 = 1884821) B1884821
theorem B1256563 : Blo 1256446 1256563 := bstep (se 1 (by rfl) ⟨942422, by rfl⟩ : syracuseStep 1256563 = 1884845) B1884845
theorem B1887347 : Blo 1256446 1887347 := bstep (se 1 (by rfl) ⟨1415510, by rfl⟩ : syracuseStep 1887347 = 2831021) B2831021
theorem B1789057 : Blo 1256446 1789057 := bstep (se 2 (by rfl) ⟨670896, by rfl⟩ : syracuseStep 1789057 = 1341793) B1341793
theorem B1256579 : Blo 1256446 1256579 := bstep (se 1 (by rfl) ⟨942434, by rfl⟩ : syracuseStep 1256579 = 1884869) B1884869
theorem B1887377 : Blo 1256446 1887377 := bstep (se 2 (by rfl) ⟨707766, by rfl⟩ : syracuseStep 1887377 = 1415533) B1415533
theorem B1256595 : Blo 1256446 1256595 := bstep (se 1 (by rfl) ⟨942446, by rfl⟩ : syracuseStep 1256595 = 1884893) B1884893
theorem B1256611 : Blo 1256446 1256611 := bstep (se 1 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 1256611 = 1884917) B1884917
theorem B8604835 : Blo 1256446 8604835 := bstep (se 1 (by rfl) ⟨6453626, by rfl⟩ : syracuseStep 8604835 = 12907253) B12907253
theorem B1887395 : Blo 1256446 1887395 := bstep (se 1 (by rfl) ⟨1415546, by rfl⟩ : syracuseStep 1887395 = 2831093) B2831093
theorem B2550961 : Blo 1256446 2550961 := bstep (se 2 (by rfl) ⟨956610, by rfl⟩ : syracuseStep 2550961 = 1913221) B1913221
theorem B1256627 : Blo 1256446 1256627 := bstep (se 1 (by rfl) ⟨942470, by rfl⟩ : syracuseStep 1256627 = 1884941) B1884941
theorem B1887425 : Blo 1256446 1887425 := bstep (se 2 (by rfl) ⟨707784, by rfl⟩ : syracuseStep 1887425 = 1415569) B1415569
theorem B1256643 : Blo 1256446 1256643 := bstep (se 1 (by rfl) ⟨942482, by rfl⟩ : syracuseStep 1256643 = 1884965) B1884965
theorem B1936595 : Blo 1256446 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B1256659 : Blo 1256446 1256659 := bstep (se 1 (by rfl) ⟨942494, by rfl⟩ : syracuseStep 1256659 = 1884989) B1884989
theorem B1887443 : Blo 1256446 1887443 := bstep (se 1 (by rfl) ⟨1415582, by rfl⟩ : syracuseStep 1887443 = 2831165) B2831165
theorem B1256675 : Blo 1256446 1256675 := bstep (se 1 (by rfl) ⟨942506, by rfl⟩ : syracuseStep 1256675 = 1885013) B1885013
theorem B2387171 : Blo 1256446 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B3583217 : Blo 1256446 3583217 := bstep (se 2 (by rfl) ⟨1343706, by rfl⟩ : syracuseStep 3583217 = 2687413) B2687413
theorem B1887473 : Blo 1256446 1887473 := bstep (se 2 (by rfl) ⟨707802, by rfl⟩ : syracuseStep 1887473 = 1415605) B1415605
theorem B1256691 : Blo 1256446 1256691 := bstep (se 1 (by rfl) ⟨942518, by rfl⟩ : syracuseStep 1256691 = 1885037) B1885037
theorem B2551025 : Blo 1256446 2551025 := bstep (se 2 (by rfl) ⟨956634, by rfl⟩ : syracuseStep 2551025 = 1913269) B1913269
theorem B1256707 : Blo 1256446 1256707 := bstep (se 1 (by rfl) ⟨942530, by rfl⟩ : syracuseStep 1256707 = 1885061) B1885061
theorem B1887491 : Blo 1256446 1887491 := bstep (se 1 (by rfl) ⟨1415618, by rfl⟩ : syracuseStep 1887491 = 2831237) B2831237
theorem B1256723 : Blo 1256446 1256723 := bstep (se 1 (by rfl) ⟨942542, by rfl⟩ : syracuseStep 1256723 = 1885085) B1885085
theorem B1887521 : Blo 1256446 1887521 := bstep (se 2 (by rfl) ⟨707820, by rfl⟩ : syracuseStep 1887521 = 1415641) B1415641
theorem B1256739 : Blo 1256446 1256739 := bstep (se 1 (by rfl) ⟨942554, by rfl⟩ : syracuseStep 1256739 = 1885109) B1885109
theorem B4246829 : Blo 1256446 4246829 := bstep (se 3 (by rfl) ⟨796280, by rfl⟩ : syracuseStep 4246829 = 1592561) B1592561
theorem B2829617 : Blo 1256446 2829617 := bstep (se 2 (by rfl) ⟨1061106, by rfl⟩ : syracuseStep 2829617 = 2122213) B2122213
theorem B1256755 : Blo 1256446 1256755 := bstep (se 1 (by rfl) ⟨942566, by rfl⟩ : syracuseStep 1256755 = 1885133) B1885133
theorem B1887539 : Blo 1256446 1887539 := bstep (se 1 (by rfl) ⟨1415654, by rfl⟩ : syracuseStep 1887539 = 2831309) B2831309
theorem B1256771 : Blo 1256446 1256771 := bstep (se 1 (by rfl) ⟨942578, by rfl⟩ : syracuseStep 1256771 = 1885157) B1885157
theorem B2829635 : Blo 1256446 2829635 := bstep (se 1 (by rfl) ⟨2122226, by rfl⟩ : syracuseStep 2829635 = 4244453) B4244453
theorem B5442893 : Blo 1256446 5442893 := bstep (se 3 (by rfl) ⟨1020542, by rfl⟩ : syracuseStep 5442893 = 2041085) B2041085
theorem B2452817 : Blo 1256446 2452817 := bstep (se 2 (by rfl) ⟨919806, by rfl⟩ : syracuseStep 2452817 = 1839613) B1839613
theorem B1256787 : Blo 1256446 1256787 := bstep (se 1 (by rfl) ⟨942590, by rfl⟩ : syracuseStep 1256787 = 1885181) B1885181
theorem B1887569 : Blo 1256446 1887569 := bstep (se 2 (by rfl) ⟨707838, by rfl⟩ : syracuseStep 1887569 = 1415677) B1415677
theorem B1256803 : Blo 1256446 1256803 := bstep (se 1 (by rfl) ⟨942602, by rfl⟩ : syracuseStep 1256803 = 1885205) B1885205
theorem B4246883 : Blo 1256446 4246883 := bstep (se 1 (by rfl) ⟨3185162, by rfl⟩ : syracuseStep 4246883 = 6370325) B6370325
theorem B1887587 : Blo 1256446 1887587 := bstep (se 1 (by rfl) ⟨1415690, by rfl⟩ : syracuseStep 1887587 = 2831381) B2831381
theorem B4025713 : Blo 1256446 4025713 := bstep (se 2 (by rfl) ⟨1509642, by rfl⟩ : syracuseStep 4025713 = 3019285) B3019285
theorem B1256819 : Blo 1256446 1256819 := bstep (se 1 (by rfl) ⟨942614, by rfl⟩ : syracuseStep 1256819 = 1885229) B1885229
theorem B1887617 : Blo 1256446 1887617 := bstep (se 2 (by rfl) ⟨707856, by rfl⟩ : syracuseStep 1887617 = 1415713) B1415713
theorem B1256835 : Blo 1256446 1256835 := bstep (se 1 (by rfl) ⟨942626, by rfl⟩ : syracuseStep 1256835 = 1885253) B1885253
theorem B8605061 : Blo 1256446 8605061 := bstep (se 4 (by rfl) ⟨806724, by rfl⟩ : syracuseStep 8605061 = 1613449) B1613449
theorem B6040973 : Blo 1256446 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B1256851 : Blo 1256446 1256851 := bstep (se 1 (by rfl) ⟨942638, by rfl⟩ : syracuseStep 1256851 = 1885277) B1885277
theorem B1887635 : Blo 1256446 1887635 := bstep (se 1 (by rfl) ⟨1415726, by rfl⟩ : syracuseStep 1887635 = 2831453) B2831453
theorem B1256867 : Blo 1256446 1256867 := bstep (se 1 (by rfl) ⟨942650, by rfl⟩ : syracuseStep 1256867 = 1885301) B1885301
theorem B1887665 : Blo 1256446 1887665 := bstep (se 2 (by rfl) ⟨707874, by rfl⟩ : syracuseStep 1887665 = 1415749) B1415749
theorem B1256883 : Blo 1256446 1256883 := bstep (se 1 (by rfl) ⟨942662, by rfl⟩ : syracuseStep 1256883 = 1885325) B1885325
theorem B1256899 : Blo 1256446 1256899 := bstep (se 1 (by rfl) ⟨942674, by rfl⟩ : syracuseStep 1256899 = 1885349) B1885349
theorem B1256915 : Blo 1256446 1256915 := bstep (se 1 (by rfl) ⟨942686, by rfl⟩ : syracuseStep 1256915 = 1885373) B1885373
theorem B1256931 : Blo 1256446 1256931 := bstep (se 1 (by rfl) ⟨942698, by rfl⟩ : syracuseStep 1256931 = 1885397) B1885397
theorem B1256947 : Blo 1256446 1256947 := bstep (se 1 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 1256947 = 1885421) B1885421
theorem B1256963 : Blo 1256446 1256963 := bstep (se 1 (by rfl) ⟨942722, by rfl⟩ : syracuseStep 1256963 = 1885445) B1885445
theorem B1256979 : Blo 1256446 1256979 := bstep (se 1 (by rfl) ⟨942734, by rfl⟩ : syracuseStep 1256979 = 1885469) B1885469
theorem B1256995 : Blo 1256446 1256995 := bstep (se 1 (by rfl) ⟨942746, by rfl⟩ : syracuseStep 1256995 = 1885493) B1885493
theorem B1257011 : Blo 1256446 1257011 := bstep (se 1 (by rfl) ⟨942758, by rfl⟩ : syracuseStep 1257011 = 1885517) B1885517
theorem B1257027 : Blo 1256446 1257027 := bstep (se 1 (by rfl) ⟨942770, by rfl⟩ : syracuseStep 1257027 = 1885541) B1885541
theorem B2829905 : Blo 1256446 2829905 := bstep (se 2 (by rfl) ⟨1061214, by rfl⟩ : syracuseStep 2829905 = 2122429) B2122429
theorem B1257043 : Blo 1256446 1257043 := bstep (se 1 (by rfl) ⟨942782, by rfl⟩ : syracuseStep 1257043 = 1885565) B1885565
theorem B1257059 : Blo 1256446 1257059 := bstep (se 1 (by rfl) ⟨942794, by rfl⟩ : syracuseStep 1257059 = 1885589) B1885589
theorem B2829923 : Blo 1256446 2829923 := bstep (se 1 (by rfl) ⟨2122442, by rfl⟩ : syracuseStep 2829923 = 4244885) B4244885
theorem B6368867 : Blo 1256446 6368867 := bstep (se 1 (by rfl) ⟨4776650, by rfl⟩ : syracuseStep 6368867 = 9553301) B9553301
theorem B1789553 : Blo 1256446 1789553 := bstep (se 2 (by rfl) ⟨671082, by rfl⟩ : syracuseStep 1789553 = 1342165) B1342165
theorem B4247153 : Blo 1256446 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B1257075 : Blo 1256446 1257075 := bstep (se 1 (by rfl) ⟨942806, by rfl⟩ : syracuseStep 1257075 = 1885613) B1885613
theorem B1257091 : Blo 1256446 1257091 := bstep (se 1 (by rfl) ⟨942818, by rfl⟩ : syracuseStep 1257091 = 1885637) B1885637
theorem B1257107 : Blo 1256446 1257107 := bstep (se 1 (by rfl) ⟨942830, by rfl⟩ : syracuseStep 1257107 = 1885661) B1885661
theorem B1257123 : Blo 1256446 1257123 := bstep (se 1 (by rfl) ⟨942842, by rfl⟩ : syracuseStep 1257123 = 1885685) B1885685
theorem B2264753 : Blo 1256446 2264753 := bstep (se 2 (by rfl) ⟨849282, by rfl⟩ : syracuseStep 2264753 = 1698565) B1698565
theorem B1257139 : Blo 1256446 1257139 := bstep (se 1 (by rfl) ⟨942854, by rfl⟩ : syracuseStep 1257139 = 1885709) B1885709
theorem B1257155 : Blo 1256446 1257155 := bstep (se 1 (by rfl) ⟨942866, by rfl⟩ : syracuseStep 1257155 = 1885733) B1885733
theorem B12086981 : Blo 1256446 12086981 := bstep (se 4 (by rfl) ⟨1133154, by rfl⟩ : syracuseStep 12086981 = 2266309) B2266309
theorem B1257171 : Blo 1256446 1257171 := bstep (se 1 (by rfl) ⟨942878, by rfl⟩ : syracuseStep 1257171 = 1885757) B1885757
theorem B1257187 : Blo 1256446 1257187 := bstep (se 1 (by rfl) ⟨942890, by rfl⟩ : syracuseStep 1257187 = 1885781) B1885781
theorem B3272419 : Blo 1256446 3272419 := bstep (se 1 (by rfl) ⟨2454314, by rfl⟩ : syracuseStep 3272419 = 4908629) B4908629
theorem B1257203 : Blo 1256446 1257203 := bstep (se 1 (by rfl) ⟨942902, by rfl⟩ : syracuseStep 1257203 = 1885805) B1885805
theorem B1257219 : Blo 1256446 1257219 := bstep (se 1 (by rfl) ⟨942914, by rfl⟩ : syracuseStep 1257219 = 1885829) B1885829
theorem B1257235 : Blo 1256446 1257235 := bstep (se 1 (by rfl) ⟨942926, by rfl⟩ : syracuseStep 1257235 = 1885853) B1885853
theorem B1257251 : Blo 1256446 1257251 := bstep (se 1 (by rfl) ⟨942938, by rfl⟩ : syracuseStep 1257251 = 1885877) B1885877
theorem B3821357 : Blo 1256446 3821357 := bstep (se 3 (by rfl) ⟨716504, by rfl⟩ : syracuseStep 3821357 = 1433009) B1433009
theorem B1257267 : Blo 1256446 1257267 := bstep (se 1 (by rfl) ⟨942950, by rfl⟩ : syracuseStep 1257267 = 1885901) B1885901
theorem B1257283 : Blo 1256446 1257283 := bstep (se 1 (by rfl) ⟨942962, by rfl⟩ : syracuseStep 1257283 = 1885925) B1885925
theorem B1257299 : Blo 1256446 1257299 := bstep (se 1 (by rfl) ⟨942974, by rfl⟩ : syracuseStep 1257299 = 1885949) B1885949
theorem B1257315 : Blo 1256446 1257315 := bstep (se 1 (by rfl) ⟨942986, by rfl⟩ : syracuseStep 1257315 = 1885973) B1885973
theorem B7163747 : Blo 1256446 7163747 := bstep (se 1 (by rfl) ⟨5372810, by rfl⟩ : syracuseStep 7163747 = 10745621) B10745621
theorem B1912673 : Blo 1256446 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B3182449 : Blo 1256446 3182449 := bstep (se 2 (by rfl) ⟨1193418, by rfl⟩ : syracuseStep 3182449 = 2386837) B2386837
theorem B2830193 : Blo 1256446 2830193 := bstep (se 2 (by rfl) ⟨1061322, by rfl⟩ : syracuseStep 2830193 = 2122645) B2122645
theorem B1257331 : Blo 1256446 1257331 := bstep (se 1 (by rfl) ⟨942998, by rfl⟩ : syracuseStep 1257331 = 1885997) B1885997
theorem B1257347 : Blo 1256446 1257347 := bstep (se 1 (by rfl) ⟨943010, by rfl⟩ : syracuseStep 1257347 = 1886021) B1886021
theorem B2830211 : Blo 1256446 2830211 := bstep (se 1 (by rfl) ⟨2122658, by rfl⟩ : syracuseStep 2830211 = 4245317) B4245317
theorem B1257363 : Blo 1256446 1257363 := bstep (se 1 (by rfl) ⟨943022, by rfl⟩ : syracuseStep 1257363 = 1886045) B1886045
theorem B1257379 : Blo 1256446 1257379 := bstep (se 1 (by rfl) ⟨943034, by rfl⟩ : syracuseStep 1257379 = 1886069) B1886069
theorem B1257395 : Blo 1256446 1257395 := bstep (se 1 (by rfl) ⟨943046, by rfl⟩ : syracuseStep 1257395 = 1886093) B1886093
theorem B1257411 : Blo 1256446 1257411 := bstep (se 1 (by rfl) ⟨943058, by rfl⟩ : syracuseStep 1257411 = 1886117) B1886117
theorem B1912771 : Blo 1256446 1912771 := bstep (se 1 (by rfl) ⟨1434578, by rfl⟩ : syracuseStep 1912771 = 2869157) B2869157
theorem B1257427 : Blo 1256446 1257427 := bstep (se 1 (by rfl) ⟨943070, by rfl⟩ : syracuseStep 1257427 = 1886141) B1886141
theorem B1257443 : Blo 1256446 1257443 := bstep (se 1 (by rfl) ⟨943082, by rfl⟩ : syracuseStep 1257443 = 1886165) B1886165
theorem B1257459 : Blo 1256446 1257459 := bstep (se 1 (by rfl) ⟨943094, by rfl⟩ : syracuseStep 1257459 = 1886189) B1886189
theorem B1257475 : Blo 1256446 1257475 := bstep (se 1 (by rfl) ⟨943106, by rfl⟩ : syracuseStep 1257475 = 1886213) B1886213
theorem B1257491 : Blo 1256446 1257491 := bstep (se 1 (by rfl) ⟨943118, by rfl⟩ : syracuseStep 1257491 = 1886237) B1886237
theorem B1257507 : Blo 1256446 1257507 := bstep (se 1 (by rfl) ⟨943130, by rfl⟩ : syracuseStep 1257507 = 1886261) B1886261
theorem B5369905 : Blo 1256446 5369905 := bstep (se 2 (by rfl) ⟨2013714, by rfl⟩ : syracuseStep 5369905 = 4027429) B4027429
theorem B1257523 : Blo 1256446 1257523 := bstep (se 1 (by rfl) ⟨943142, by rfl⟩ : syracuseStep 1257523 = 1886285) B1886285
theorem B1257539 : Blo 1256446 1257539 := bstep (se 1 (by rfl) ⟨943154, by rfl⟩ : syracuseStep 1257539 = 1886309) B1886309
theorem B1257555 : Blo 1256446 1257555 := bstep (se 1 (by rfl) ⟨943166, by rfl⟩ : syracuseStep 1257555 = 1886333) B1886333
theorem B9064547 : Blo 1256446 9064547 := bstep (se 1 (by rfl) ⟨6798410, by rfl⟩ : syracuseStep 9064547 = 13596821) B13596821
theorem B1257571 : Blo 1256446 1257571 := bstep (se 1 (by rfl) ⟨943178, by rfl⟩ : syracuseStep 1257571 = 1886357) B1886357
theorem B1257587 : Blo 1256446 1257587 := bstep (se 1 (by rfl) ⟨943190, by rfl⟩ : syracuseStep 1257587 = 1886381) B1886381
theorem B3182723 : Blo 1256446 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B1257603 : Blo 1256446 1257603 := bstep (se 1 (by rfl) ⟨943202, by rfl⟩ : syracuseStep 1257603 = 1886405) B1886405
theorem B2388113 : Blo 1256446 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B2830481 : Blo 1256446 2830481 := bstep (se 2 (by rfl) ⟨1061430, by rfl⟩ : syracuseStep 2830481 = 2122861) B2122861
theorem B1257619 : Blo 1256446 1257619 := bstep (se 1 (by rfl) ⟨943214, by rfl⟩ : syracuseStep 1257619 = 1886429) B1886429
theorem B1257635 : Blo 1256446 1257635 := bstep (se 1 (by rfl) ⟨943226, by rfl⟩ : syracuseStep 1257635 = 1886453) B1886453
theorem B2830499 : Blo 1256446 2830499 := bstep (se 1 (by rfl) ⟨2122874, by rfl⟩ : syracuseStep 2830499 = 4245749) B4245749
theorem B1257651 : Blo 1256446 1257651 := bstep (se 1 (by rfl) ⟨943238, by rfl⟩ : syracuseStep 1257651 = 1886477) B1886477
theorem B1257667 : Blo 1256446 1257667 := bstep (se 1 (by rfl) ⟨943250, by rfl⟩ : syracuseStep 1257667 = 1886501) B1886501
theorem B1257683 : Blo 1256446 1257683 := bstep (se 1 (by rfl) ⟨943262, by rfl⟩ : syracuseStep 1257683 = 1886525) B1886525
theorem B1257699 : Blo 1256446 1257699 := bstep (se 1 (by rfl) ⟨943274, by rfl⟩ : syracuseStep 1257699 = 1886549) B1886549
theorem B1257715 : Blo 1256446 1257715 := bstep (se 1 (by rfl) ⟨943286, by rfl⟩ : syracuseStep 1257715 = 1886573) B1886573
theorem B1913075 : Blo 1256446 1913075 := bstep (se 1 (by rfl) ⟨1434806, by rfl⟩ : syracuseStep 1913075 = 2869613) B2869613
theorem B1257731 : Blo 1256446 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B4305155 : Blo 1256446 4305155 := bstep (se 1 (by rfl) ⟨3228866, by rfl⟩ : syracuseStep 4305155 = 6457733) B6457733
theorem B1257747 : Blo 1256446 1257747 := bstep (se 1 (by rfl) ⟨943310, by rfl⟩ : syracuseStep 1257747 = 1886621) B1886621
theorem B1257763 : Blo 1256446 1257763 := bstep (se 1 (by rfl) ⟨943322, by rfl⟩ : syracuseStep 1257763 = 1886645) B1886645
theorem B1257779 : Blo 1256446 1257779 := bstep (se 1 (by rfl) ⟨943334, by rfl⟩ : syracuseStep 1257779 = 1886669) B1886669
theorem B3182915 : Blo 1256446 3182915 := bstep (se 1 (by rfl) ⟨2387186, by rfl⟩ : syracuseStep 3182915 = 4774373) B4774373
theorem B1257795 : Blo 1256446 1257795 := bstep (se 1 (by rfl) ⟨943346, by rfl⟩ : syracuseStep 1257795 = 1886693) B1886693
theorem B1257811 : Blo 1256446 1257811 := bstep (se 1 (by rfl) ⟨943358, by rfl⟩ : syracuseStep 1257811 = 1886717) B1886717
theorem B1257827 : Blo 1256446 1257827 := bstep (se 1 (by rfl) ⟨943370, by rfl⟩ : syracuseStep 1257827 = 1886741) B1886741
theorem B1257843 : Blo 1256446 1257843 := bstep (se 1 (by rfl) ⟨943382, by rfl⟩ : syracuseStep 1257843 = 1886765) B1886765
theorem B1257859 : Blo 1256446 1257859 := bstep (se 1 (by rfl) ⟨943394, by rfl⟩ : syracuseStep 1257859 = 1886789) B1886789
theorem B6369677 : Blo 1256446 6369677 := bstep (se 3 (by rfl) ⟨1194314, by rfl⟩ : syracuseStep 6369677 = 2388629) B2388629
theorem B1257875 : Blo 1256446 1257875 := bstep (se 1 (by rfl) ⟨943406, by rfl⟩ : syracuseStep 1257875 = 1886813) B1886813
theorem B1257891 : Blo 1256446 1257891 := bstep (se 1 (by rfl) ⟨943418, by rfl⟩ : syracuseStep 1257891 = 1886837) B1886837
theorem B2830769 : Blo 1256446 2830769 := bstep (se 2 (by rfl) ⟨1061538, by rfl⟩ : syracuseStep 2830769 = 2123077) B2123077
theorem B1257907 : Blo 1256446 1257907 := bstep (se 1 (by rfl) ⟨943430, by rfl⟩ : syracuseStep 1257907 = 1886861) B1886861
theorem B1413571 : Blo 1256446 1413571 := bstep (se 1 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 1413571 = 2120357) B2120357
theorem B1257923 : Blo 1256446 1257923 := bstep (se 1 (by rfl) ⟨943442, by rfl⟩ : syracuseStep 1257923 = 1886885) B1886885
theorem B2830787 : Blo 1256446 2830787 := bstep (se 1 (by rfl) ⟨2123090, by rfl⟩ : syracuseStep 2830787 = 4246181) B4246181
theorem B1790419 : Blo 1256446 1790419 := bstep (se 1 (by rfl) ⟨1342814, by rfl⟩ : syracuseStep 1790419 = 2685629) B2685629
theorem B1257939 : Blo 1256446 1257939 := bstep (se 1 (by rfl) ⟨943454, by rfl⟩ : syracuseStep 1257939 = 1886909) B1886909
theorem B1257955 : Blo 1256446 1257955 := bstep (se 1 (by rfl) ⟨943466, by rfl⟩ : syracuseStep 1257955 = 1886933) B1886933
theorem B1257971 : Blo 1256446 1257971 := bstep (se 1 (by rfl) ⟨943478, by rfl⟩ : syracuseStep 1257971 = 1886957) B1886957
theorem B1257987 : Blo 1256446 1257987 := bstep (se 1 (by rfl) ⟨943490, by rfl⟩ : syracuseStep 1257987 = 1886981) B1886981
theorem B1258003 : Blo 1256446 1258003 := bstep (se 1 (by rfl) ⟨943502, by rfl⟩ : syracuseStep 1258003 = 1887005) B1887005
theorem B1258019 : Blo 1256446 1258019 := bstep (se 1 (by rfl) ⟨943514, by rfl⟩ : syracuseStep 1258019 = 1887029) B1887029
theorem B1790515 : Blo 1256446 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B1258035 : Blo 1256446 1258035 := bstep (se 1 (by rfl) ⟨943526, by rfl⟩ : syracuseStep 1258035 = 1887053) B1887053
theorem B1258051 : Blo 1256446 1258051 := bstep (se 1 (by rfl) ⟨943538, by rfl⟩ : syracuseStep 1258051 = 1887077) B1887077
theorem B14316101 : Blo 1256446 14316101 := bstep (se 4 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 14316101 = 2684269) B2684269
theorem B4772429 : Blo 1256446 4772429 := bstep (se 3 (by rfl) ⟨894830, by rfl⟩ : syracuseStep 4772429 = 1789661) B1789661
theorem B1413715 : Blo 1256446 1413715 := bstep (se 1 (by rfl) ⟨1060286, by rfl⟩ : syracuseStep 1413715 = 2120573) B2120573
theorem B1258067 : Blo 1256446 1258067 := bstep (se 1 (by rfl) ⟨943550, by rfl⟩ : syracuseStep 1258067 = 1887101) B1887101
theorem B1258083 : Blo 1256446 1258083 := bstep (se 1 (by rfl) ⟨943562, by rfl⟩ : syracuseStep 1258083 = 1887125) B1887125
theorem B1258099 : Blo 1256446 1258099 := bstep (se 1 (by rfl) ⟨943574, by rfl⟩ : syracuseStep 1258099 = 1887149) B1887149
theorem B1258115 : Blo 1256446 1258115 := bstep (se 1 (by rfl) ⟨943586, by rfl⟩ : syracuseStep 1258115 = 1887173) B1887173
theorem B1258131 : Blo 1256446 1258131 := bstep (se 1 (by rfl) ⟨943598, by rfl⟩ : syracuseStep 1258131 = 1887197) B1887197
theorem B1258147 : Blo 1256446 1258147 := bstep (se 1 (by rfl) ⟨943610, by rfl⟩ : syracuseStep 1258147 = 1887221) B1887221
theorem B1258163 : Blo 1256446 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B1258179 : Blo 1256446 1258179 := bstep (se 1 (by rfl) ⟨943634, by rfl⟩ : syracuseStep 1258179 = 1887269) B1887269
theorem B2831057 : Blo 1256446 2831057 := bstep (se 2 (by rfl) ⟨1061646, by rfl⟩ : syracuseStep 2831057 = 2123293) B2123293
theorem B1258195 : Blo 1256446 1258195 := bstep (se 1 (by rfl) ⟨943646, by rfl⟩ : syracuseStep 1258195 = 1887293) B1887293
theorem B1413859 : Blo 1256446 1413859 := bstep (se 1 (by rfl) ⟨1060394, by rfl⟩ : syracuseStep 1413859 = 2120789) B2120789
theorem B1258211 : Blo 1256446 1258211 := bstep (se 1 (by rfl) ⟨943658, by rfl⟩ : syracuseStep 1258211 = 1887317) B1887317
theorem B2831075 : Blo 1256446 2831075 := bstep (se 1 (by rfl) ⟨2123306, by rfl⟩ : syracuseStep 2831075 = 4246613) B4246613
theorem B1258227 : Blo 1256446 1258227 := bstep (se 1 (by rfl) ⟨943670, by rfl⟩ : syracuseStep 1258227 = 1887341) B1887341
theorem B1258243 : Blo 1256446 1258243 := bstep (se 1 (by rfl) ⟨943682, by rfl⟩ : syracuseStep 1258243 = 1887365) B1887365
theorem B1258259 : Blo 1256446 1258259 := bstep (se 1 (by rfl) ⟨943694, by rfl⟩ : syracuseStep 1258259 = 1887389) B1887389
theorem B1258275 : Blo 1256446 1258275 := bstep (se 1 (by rfl) ⟨943706, by rfl⟩ : syracuseStep 1258275 = 1887413) B1887413
theorem B1258291 : Blo 1256446 1258291 := bstep (se 1 (by rfl) ⟨943718, by rfl⟩ : syracuseStep 1258291 = 1887437) B1887437
theorem B1258307 : Blo 1256446 1258307 := bstep (se 1 (by rfl) ⟨943730, by rfl⟩ : syracuseStep 1258307 = 1887461) B1887461
theorem B1258323 : Blo 1256446 1258323 := bstep (se 1 (by rfl) ⟨943742, by rfl⟩ : syracuseStep 1258323 = 1887485) B1887485
theorem B1258339 : Blo 1256446 1258339 := bstep (se 1 (by rfl) ⟨943754, by rfl⟩ : syracuseStep 1258339 = 1887509) B1887509
theorem B1414003 : Blo 1256446 1414003 := bstep (se 1 (by rfl) ⟨1060502, by rfl⟩ : syracuseStep 1414003 = 2121005) B2121005
theorem B1258355 : Blo 1256446 1258355 := bstep (se 1 (by rfl) ⟨943766, by rfl⟩ : syracuseStep 1258355 = 1887533) B1887533
theorem B1258371 : Blo 1256446 1258371 := bstep (se 1 (by rfl) ⟨943778, by rfl⟩ : syracuseStep 1258371 = 1887557) B1887557
theorem B1258387 : Blo 1256446 1258387 := bstep (se 1 (by rfl) ⟨943790, by rfl⟩ : syracuseStep 1258387 = 1887581) B1887581
theorem B1258403 : Blo 1256446 1258403 := bstep (se 1 (by rfl) ⟨943802, by rfl⟩ : syracuseStep 1258403 = 1887605) B1887605
theorem B1258419 : Blo 1256446 1258419 := bstep (se 1 (by rfl) ⟨943814, by rfl⟩ : syracuseStep 1258419 = 1887629) B1887629
theorem B1258435 : Blo 1256446 1258435 := bstep (se 1 (by rfl) ⟨943826, by rfl⟩ : syracuseStep 1258435 = 1887653) B1887653
theorem B2831345 : Blo 1256446 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B1414147 : Blo 1256446 1414147 := bstep (se 1 (by rfl) ⟨1060610, by rfl⟩ : syracuseStep 1414147 = 2121221) B2121221
theorem B2831363 : Blo 1256446 2831363 := bstep (se 1 (by rfl) ⟨2123522, by rfl⟩ : syracuseStep 2831363 = 4247045) B4247045
theorem B2389009 : Blo 1256446 2389009 := bstep (se 2 (by rfl) ⟨895878, by rfl⟩ : syracuseStep 2389009 = 1791757) B1791757
theorem B1791011 : Blo 1256446 1791011 := bstep (se 1 (by rfl) ⟨1343258, by rfl⟩ : syracuseStep 1791011 = 2686517) B2686517
theorem B6362225 : Blo 1256446 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B14324849 : Blo 1256446 14324849 := bstep (se 2 (by rfl) ⟨5371818, by rfl⟩ : syracuseStep 14324849 = 10743637) B10743637
theorem B32240753 : Blo 1256446 32240753 := bstep (se 2 (by rfl) ⟨12090282, by rfl⟩ : syracuseStep 32240753 = 24180565) B24180565
theorem B10744973 : Blo 1256446 10744973 := bstep (se 3 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 10744973 = 4029365) B4029365
theorem B1414291 : Blo 1256446 1414291 := bstep (se 1 (by rfl) ⟨1060718, by rfl⟩ : syracuseStep 1414291 = 2121437) B2121437
theorem B2684099 : Blo 1256446 2684099 := bstep (se 1 (by rfl) ⟨2013074, by rfl⟩ : syracuseStep 2684099 = 4026149) B4026149
theorem B3183857 : Blo 1256446 3183857 := bstep (se 2 (by rfl) ⟨1193946, by rfl⟩ : syracuseStep 3183857 = 2387893) B2387893
theorem B1414435 : Blo 1256446 1414435 := bstep (se 1 (by rfl) ⟨1060826, by rfl⟩ : syracuseStep 1414435 = 2121653) B2121653
theorem B3183907 : Blo 1256446 3183907 := bstep (se 1 (by rfl) ⟨2387930, by rfl⟩ : syracuseStep 3183907 = 4775861) B4775861
theorem B4240781 : Blo 1256446 4240781 := bstep (se 3 (by rfl) ⟨795146, by rfl⟩ : syracuseStep 4240781 = 1590293) B1590293
theorem B3184049 : Blo 1256446 3184049 := bstep (se 2 (by rfl) ⟨1194018, by rfl⟩ : syracuseStep 3184049 = 2388037) B2388037
theorem B1414579 : Blo 1256446 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B4240835 : Blo 1256446 4240835 := bstep (se 1 (by rfl) ⟨3180626, by rfl⟩ : syracuseStep 4240835 = 6361253) B6361253
theorem B7263749 : Blo 1256446 7263749 := bstep (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) B1361953
theorem B69760565 : Blo 1256446 69760565 := bstep (se 5 (by rfl) ⟨3270026, by rfl⟩ : syracuseStep 69760565 = 6540053) B6540053
theorem B1414723 : Blo 1256446 1414723 := bstep (se 1 (by rfl) ⟨1061042, by rfl⟩ : syracuseStep 1414723 = 2122085) B2122085
theorem B13588037 : Blo 1256446 13588037 := bstep (se 4 (by rfl) ⟨1273878, by rfl⟩ : syracuseStep 13588037 = 2547757) B2547757
theorem B6624845 : Blo 1256446 6624845 := bstep (se 3 (by rfl) ⟨1242158, by rfl⟩ : syracuseStep 6624845 = 2484317) B2484317
theorem B1791649 : Blo 1256446 1791649 := bstep (se 2 (by rfl) ⟨671868, by rfl⟩ : syracuseStep 1791649 = 1343737) B1343737
theorem B6543011 : Blo 1256446 6543011 := bstep (se 1 (by rfl) ⟨4907258, by rfl⟩ : syracuseStep 6543011 = 9814517) B9814517
theorem B2684611 : Blo 1256446 2684611 := bstep (se 1 (by rfl) ⟨2013458, by rfl⟩ : syracuseStep 2684611 = 4026917) B4026917
theorem B8165069 : Blo 1256446 8165069 := bstep (se 3 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 8165069 = 3061901) B3061901
theorem B4241105 : Blo 1256446 4241105 := bstep (se 2 (by rfl) ⟨1590414, by rfl⟩ : syracuseStep 4241105 = 3180829) B3180829
theorem B1414867 : Blo 1256446 1414867 := bstep (se 1 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 1414867 = 2122301) B2122301
theorem B1415011 : Blo 1256446 1415011 := bstep (se 1 (by rfl) ⟨1061258, by rfl⟩ : syracuseStep 1415011 = 2122517) B2122517
theorem B1415155 : Blo 1256446 1415155 := bstep (se 1 (by rfl) ⟨1061366, by rfl⟩ : syracuseStep 1415155 = 2122733) B2122733
theorem B6453283 : Blo 1256446 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B1415299 : Blo 1256446 1415299 := bstep (se 1 (by rfl) ⟨1061474, by rfl⟩ : syracuseStep 1415299 = 2122949) B2122949
theorem B8059013 : Blo 1256446 8059013 := bstep (se 4 (by rfl) ⟨755532, by rfl⟩ : syracuseStep 8059013 = 1511065) B1511065
theorem B4028557 : Blo 1256446 4028557 := bstep (se 3 (by rfl) ⟨755354, by rfl⟩ : syracuseStep 4028557 = 1510709) B1510709
theorem B2013331 : Blo 1256446 2013331 := bstep (se 1 (by rfl) ⟨1509998, by rfl⟩ : syracuseStep 2013331 = 3019997) B3019997
theorem B4241645 : Blo 1256446 4241645 := bstep (se 3 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 4241645 = 1590617) B1590617
theorem B12245261 : Blo 1256446 12245261 := bstep (se 3 (by rfl) ⟨2295986, by rfl⟩ : syracuseStep 12245261 = 4591973) B4591973
theorem B1415443 : Blo 1256446 1415443 := bstep (se 1 (by rfl) ⟨1061582, by rfl⟩ : syracuseStep 1415443 = 2123165) B2123165
theorem B4241699 : Blo 1256446 4241699 := bstep (se 1 (by rfl) ⟨3181274, by rfl⟩ : syracuseStep 4241699 = 6362549) B6362549
theorem B2267441 : Blo 1256446 2267441 := bstep (se 2 (by rfl) ⟨850290, by rfl⟩ : syracuseStep 2267441 = 1700581) B1700581
theorem B8272205 : Blo 1256446 8272205 := bstep (se 3 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 8272205 = 3102077) B3102077
theorem B3021187 : Blo 1256446 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B2685329 : Blo 1256446 2685329 := bstep (se 2 (by rfl) ⟨1006998, by rfl⟩ : syracuseStep 2685329 = 2013997) B2013997
theorem B2013587 : Blo 1256446 2013587 := bstep (se 1 (by rfl) ⟨1510190, by rfl⟩ : syracuseStep 2013587 = 3020381) B3020381
theorem B3185041 : Blo 1256446 3185041 := bstep (se 2 (by rfl) ⟨1194390, by rfl⟩ : syracuseStep 3185041 = 2388781) B2388781
theorem B1415587 : Blo 1256446 1415587 := bstep (se 1 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 1415587 = 2123381) B2123381
theorem B6363683 : Blo 1256446 6363683 := bstep (se 1 (by rfl) ⟨4772762, by rfl⟩ : syracuseStep 6363683 = 9545525) B9545525
theorem B4241969 : Blo 1256446 4241969 := bstep (se 2 (by rfl) ⟨1590738, by rfl⟩ : syracuseStep 4241969 = 3181477) B3181477
theorem B1415731 : Blo 1256446 1415731 := bstep (se 1 (by rfl) ⟨1061798, by rfl⟩ : syracuseStep 1415731 = 2123597) B2123597
theorem B2013779 : Blo 1256446 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B2120323 : Blo 1256446 2120323 := bstep (se 1 (by rfl) ⟨1590242, by rfl⟩ : syracuseStep 2120323 = 3180485) B3180485
theorem B3021457 : Blo 1256446 3021457 := bstep (se 2 (by rfl) ⟨1133046, by rfl⟩ : syracuseStep 3021457 = 2266093) B2266093
theorem B3185315 : Blo 1256446 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B68836067 : Blo 1256446 68836067 := bstep (se 1 (by rfl) ⟨51627050, by rfl⟩ : syracuseStep 68836067 = 103254101) B103254101
theorem B2120465 : Blo 1256446 2120465 := bstep (se 2 (by rfl) ⟨795174, by rfl⟩ : syracuseStep 2120465 = 1590349) B1590349
theorem B2120593 : Blo 1256446 2120593 := bstep (se 2 (by rfl) ⟨795222, by rfl⟩ : syracuseStep 2120593 = 1590445) B1590445
theorem B2120627 : Blo 1256446 2120627 := bstep (se 1 (by rfl) ⟨1590470, by rfl⟩ : syracuseStep 2120627 = 3180941) B3180941
theorem B1342451 : Blo 1256446 1342451 := bstep (se 1 (by rfl) ⟨1006838, by rfl⟩ : syracuseStep 1342451 = 2013677) B2013677
theorem B3931139 : Blo 1256446 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B7166981 : Blo 1256446 7166981 := bstep (se 4 (by rfl) ⟨671904, by rfl⟩ : syracuseStep 7166981 = 1343809) B1343809
theorem B2120755 : Blo 1256446 2120755 := bstep (se 1 (by rfl) ⟨1590566, by rfl⟩ : syracuseStep 2120755 = 3181133) B3181133
theorem B4242509 : Blo 1256446 4242509 := bstep (se 3 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 4242509 = 1590941) B1590941
theorem B1342579 : Blo 1256446 1342579 := bstep (se 1 (by rfl) ⟨1006934, by rfl⟩ : syracuseStep 1342579 = 2013869) B2013869
theorem B4242563 : Blo 1256446 4242563 := bstep (se 1 (by rfl) ⟨3181922, by rfl⟩ : syracuseStep 4242563 = 6363845) B6363845
theorem B2686115 : Blo 1256446 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B3824813 : Blo 1256446 3824813 := bstep (se 3 (by rfl) ⟨717152, by rfl⟩ : syracuseStep 3824813 = 1434305) B1434305
theorem B2120897 : Blo 1256446 2120897 := bstep (se 2 (by rfl) ⟨795336, by rfl⟩ : syracuseStep 2120897 = 1590673) B1590673
theorem B12082445 : Blo 1256446 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B4300067 : Blo 1256446 4300067 := bstep (se 1 (by rfl) ⟨3225050, by rfl⟩ : syracuseStep 4300067 = 6450101) B6450101
theorem B2121025 : Blo 1256446 2121025 := bstep (se 2 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 2121025 = 1590769) B1590769
theorem B6364493 : Blo 1256446 6364493 := bstep (se 3 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 6364493 = 2386685) B2386685
theorem B2014561 : Blo 1256446 2014561 := bstep (se 2 (by rfl) ⟨755460, by rfl⟩ : syracuseStep 2014561 = 1510921) B1510921
theorem B14507363 : Blo 1256446 14507363 := bstep (se 1 (by rfl) ⟨10880522, by rfl⟩ : syracuseStep 14507363 = 21761045) B21761045
theorem B2121059 : Blo 1256446 2121059 := bstep (se 1 (by rfl) ⟨1590794, by rfl⟩ : syracuseStep 2121059 = 3181589) B3181589
theorem B4242833 : Blo 1256446 4242833 := bstep (se 2 (by rfl) ⟨1591062, by rfl⟩ : syracuseStep 4242833 = 3182125) B3182125
theorem B3579299 : Blo 1256446 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B4775345 : Blo 1256446 4775345 := bstep (se 2 (by rfl) ⟨1790754, by rfl⟩ : syracuseStep 4775345 = 3581509) B3581509
theorem B2121187 : Blo 1256446 2121187 := bstep (se 1 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 2121187 = 3181781) B3181781
theorem B7650787 : Blo 1256446 7650787 := bstep (se 1 (by rfl) ⟨5738090, by rfl⟩ : syracuseStep 7650787 = 11476181) B11476181
theorem B1433155 : Blo 1256446 1433155 := bstep (se 1 (by rfl) ⟨1074866, by rfl⟩ : syracuseStep 1433155 = 2149733) B2149733
theorem B4030019 : Blo 1256446 4030019 := bstep (se 1 (by rfl) ⟨3022514, by rfl⟩ : syracuseStep 4030019 = 6045029) B6045029
theorem B7159373 : Blo 1256446 7159373 := bstep (se 3 (by rfl) ⟨1342382, by rfl⟩ : syracuseStep 7159373 = 2684765) B2684765
theorem B3022417 : Blo 1256446 3022417 := bstep (se 2 (by rfl) ⟨1133406, by rfl⟩ : syracuseStep 3022417 = 2266813) B2266813
theorem B2121329 : Blo 1256446 2121329 := bstep (se 2 (by rfl) ⟨795498, by rfl⟩ : syracuseStep 2121329 = 1590997) B1590997
theorem B2547409 : Blo 1256446 2547409 := bstep (se 2 (by rfl) ⟨955278, by rfl⟩ : syracuseStep 2547409 = 1910557) B1910557
theorem B2121457 : Blo 1256446 2121457 := bstep (se 2 (by rfl) ⟨795546, by rfl⟩ : syracuseStep 2121457 = 1591093) B1591093
theorem B2121491 : Blo 1256446 2121491 := bstep (se 1 (by rfl) ⟨1591118, by rfl⟩ : syracuseStep 2121491 = 3182237) B3182237
theorem B2547505 : Blo 1256446 2547505 := bstep (se 2 (by rfl) ⟨955314, by rfl⟩ : syracuseStep 2547505 = 1910629) B1910629
theorem B7642957 : Blo 1256446 7642957 := bstep (se 3 (by rfl) ⟨1433054, by rfl⟩ : syracuseStep 7642957 = 2866109) B2866109
theorem B2121619 : Blo 1256446 2121619 := bstep (se 1 (by rfl) ⟨1591214, by rfl⟩ : syracuseStep 2121619 = 3182429) B3182429
theorem B1343395 : Blo 1256446 1343395 := bstep (se 1 (by rfl) ⟨1007546, by rfl⟩ : syracuseStep 1343395 = 2015093) B2015093
theorem B4243373 : Blo 1256446 4243373 := bstep (se 3 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 4243373 = 1591265) B1591265
theorem B4243427 : Blo 1256446 4243427 := bstep (se 1 (by rfl) ⟨3182570, by rfl⟩ : syracuseStep 4243427 = 6365141) B6365141
theorem B9551843 : Blo 1256446 9551843 := bstep (se 1 (by rfl) ⟨7163882, by rfl⟩ : syracuseStep 9551843 = 14327765) B14327765
theorem B7159873 : Blo 1256446 7159873 := bstep (se 2 (by rfl) ⟨2684952, by rfl⟩ : syracuseStep 7159873 = 5369905) B5369905
theorem B2121815 : Blo 1256446 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B4530269 : Blo 1256446 4530269 := bstep (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) B1698851
theorem B4776029 : Blo 1256446 4776029 := bstep (se 3 (by rfl) ⟨895505, by rfl⟩ : syracuseStep 4776029 = 1791011) B1791011
theorem B2121943 : Blo 1256446 2121943 := bstep (se 1 (by rfl) ⟨1591457, by rfl⟩ : syracuseStep 2121943 = 3182915) B3182915
theorem B4243805 : Blo 1256446 4243805 := bstep (se 3 (by rfl) ⟨795713, by rfl⟩ : syracuseStep 4243805 = 1591427) B1591427
theorem B9544067 : Blo 1256446 9544067 := bstep (se 1 (by rfl) ⟨7158050, by rfl⟩ : syracuseStep 9544067 = 14316101) B14316101
theorem B1884683 : Blo 1256446 1884683 := bstep (se 1 (by rfl) ⟨1413512, by rfl⟩ : syracuseStep 1884683 = 2827025) B2827025
theorem B1884695 : Blo 1256446 1884695 := bstep (se 1 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 1884695 = 2827043) B2827043
theorem B1884761 : Blo 1256446 1884761 := bstep (se 2 (by rfl) ⟨706785, by rfl⟩ : syracuseStep 1884761 = 1413571) B1413571
theorem B6365789 : Blo 1256446 6365789 := bstep (se 3 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 6365789 = 2387171) B2387171
theorem B1884875 : Blo 1256446 1884875 := bstep (se 1 (by rfl) ⟨1413656, by rfl⟩ : syracuseStep 1884875 = 2827313) B2827313
theorem B32654029 : Blo 1256446 32654029 := bstep (se 3 (by rfl) ⟨6122630, by rfl⟩ : syracuseStep 32654029 = 12245261) B12245261
theorem B1884887 : Blo 1256446 1884887 := bstep (se 1 (by rfl) ⟨1413665, by rfl⟩ : syracuseStep 1884887 = 2827331) B2827331
theorem B1884953 : Blo 1256446 1884953 := bstep (se 2 (by rfl) ⟨706857, by rfl⟩ : syracuseStep 1884953 = 1413715) B1413715
theorem B2122571 : Blo 1256446 2122571 := bstep (se 1 (by rfl) ⟨1591928, by rfl⟩ : syracuseStep 2122571 = 3183857) B3183857
theorem B2827097 : Blo 1256446 2827097 := bstep (se 2 (by rfl) ⟨1060161, by rfl⟩ : syracuseStep 2827097 = 2120323) B2120323
theorem B27919205 : Blo 1256446 27919205 := bstep (se 4 (by rfl) ⟨2617425, by rfl⟩ : syracuseStep 27919205 = 5234851) B5234851
theorem B45892453 : Blo 1256446 45892453 := bstep (se 4 (by rfl) ⟨4302417, by rfl⟩ : syracuseStep 45892453 = 8604835) B8604835
theorem B1885067 : Blo 1256446 1885067 := bstep (se 1 (by rfl) ⟨1413800, by rfl⟩ : syracuseStep 1885067 = 2827601) B2827601
theorem B1885079 : Blo 1256446 1885079 := bstep (se 1 (by rfl) ⟨1413809, by rfl⟩ : syracuseStep 1885079 = 2827619) B2827619
theorem B2827187 : Blo 1256446 2827187 := bstep (se 1 (by rfl) ⟨2120390, by rfl⟩ : syracuseStep 2827187 = 4240781) B4240781
theorem B2122699 : Blo 1256446 2122699 := bstep (se 1 (by rfl) ⟨1592024, by rfl⟩ : syracuseStep 2122699 = 3184049) B3184049
theorem B2827223 : Blo 1256446 2827223 := bstep (se 1 (by rfl) ⟨2120417, by rfl⟩ : syracuseStep 2827223 = 4240835) B4240835
theorem B1885145 : Blo 1256446 1885145 := bstep (se 2 (by rfl) ⟨706929, by rfl⟩ : syracuseStep 1885145 = 1413859) B1413859
theorem B4842499 : Blo 1256446 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B1590283 : Blo 1256446 1590283 := bstep (se 1 (by rfl) ⟨1192712, by rfl⟩ : syracuseStep 1590283 = 2385425) B2385425
theorem B46507043 : Blo 1256446 46507043 := bstep (se 1 (by rfl) ⟨34880282, by rfl⟩ : syracuseStep 46507043 = 69760565) B69760565
theorem B4416563 : Blo 1256446 4416563 := bstep (se 1 (by rfl) ⟨3312422, by rfl⟩ : syracuseStep 4416563 = 6624845) B6624845
theorem B1885259 : Blo 1256446 1885259 := bstep (se 1 (by rfl) ⟨1413944, by rfl⟩ : syracuseStep 1885259 = 2827889) B2827889
theorem B1885271 : Blo 1256446 1885271 := bstep (se 1 (by rfl) ⟨1413953, by rfl⟩ : syracuseStep 1885271 = 2827907) B2827907
theorem B2122841 : Blo 1256446 2122841 := bstep (se 2 (by rfl) ⟨796065, by rfl⟩ : syracuseStep 2122841 = 1592131) B1592131
theorem B9307237 : Blo 1256446 9307237 := bstep (se 4 (by rfl) ⟨872553, by rfl⟩ : syracuseStep 9307237 = 1745107) B1745107
theorem B2827403 : Blo 1256446 2827403 := bstep (se 1 (by rfl) ⟨2120552, by rfl⟩ : syracuseStep 2827403 = 4241105) B4241105
theorem B1885337 : Blo 1256446 1885337 := bstep (se 2 (by rfl) ⟨707001, by rfl⟩ : syracuseStep 1885337 = 1414003) B1414003
theorem B2827457 : Blo 1256446 2827457 := bstep (se 2 (by rfl) ⟨1060296, by rfl⟩ : syracuseStep 2827457 = 2120593) B2120593
theorem B2122969 : Blo 1256446 2122969 := bstep (se 2 (by rfl) ⟨796113, by rfl⟩ : syracuseStep 2122969 = 1592227) B1592227
theorem B1885451 : Blo 1256446 1885451 := bstep (se 1 (by rfl) ⟨1414088, by rfl⟩ : syracuseStep 1885451 = 2828177) B2828177
theorem B1885463 : Blo 1256446 1885463 := bstep (se 1 (by rfl) ⟨1414097, by rfl⟩ : syracuseStep 1885463 = 2828195) B2828195
theorem B1885529 : Blo 1256446 1885529 := bstep (se 2 (by rfl) ⟨707073, by rfl⟩ : syracuseStep 1885529 = 1414147) B1414147
theorem B9684355 : Blo 1256446 9684355 := bstep (se 1 (by rfl) ⟨7263266, by rfl⟩ : syracuseStep 9684355 = 14526533) B14526533
theorem B2827673 : Blo 1256446 2827673 := bstep (se 2 (by rfl) ⟨1060377, by rfl⟩ : syracuseStep 2827673 = 2120755) B2120755
theorem B1885643 : Blo 1256446 1885643 := bstep (se 1 (by rfl) ⟨1414232, by rfl⟩ : syracuseStep 1885643 = 2828465) B2828465
theorem B4244939 : Blo 1256446 4244939 := bstep (se 1 (by rfl) ⟨3183704, by rfl⟩ : syracuseStep 4244939 = 6367409) B6367409
theorem B1885655 : Blo 1256446 1885655 := bstep (se 1 (by rfl) ⟨1414241, by rfl⟩ : syracuseStep 1885655 = 2828483) B2828483
theorem B2827763 : Blo 1256446 2827763 := bstep (se 1 (by rfl) ⟨2120822, by rfl⟩ : syracuseStep 2827763 = 4241645) B4241645
theorem B1361399 : Blo 1256446 1361399 := bstep (se 1 (by rfl) ⟨1021049, by rfl⟩ : syracuseStep 1361399 = 2042099) B2042099
theorem B27198989 : Blo 1256446 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B34407953 : Blo 1256446 34407953 := bstep (se 2 (by rfl) ⟨12902982, by rfl⟩ : syracuseStep 34407953 = 25805965) B25805965
theorem B2827799 : Blo 1256446 2827799 := bstep (se 1 (by rfl) ⟨2120849, by rfl⟩ : syracuseStep 2827799 = 4241699) B4241699
theorem B1885721 : Blo 1256446 1885721 := bstep (se 2 (by rfl) ⟨707145, by rfl⟩ : syracuseStep 1885721 = 1414291) B1414291
theorem B5514803 : Blo 1256446 5514803 := bstep (se 1 (by rfl) ⟨4136102, by rfl⟩ : syracuseStep 5514803 = 8272205) B8272205
theorem B3401281 : Blo 1256446 3401281 := bstep (se 2 (by rfl) ⟨1275480, by rfl⟩ : syracuseStep 3401281 = 2550961) B2550961
theorem B18384515 : Blo 1256446 18384515 := bstep (se 1 (by rfl) ⟨13788386, by rfl⟩ : syracuseStep 18384515 = 27576773) B27576773
theorem B1885835 : Blo 1256446 1885835 := bstep (se 1 (by rfl) ⟨1414376, by rfl⟩ : syracuseStep 1885835 = 2828753) B2828753
theorem B1885847 : Blo 1256446 1885847 := bstep (se 1 (by rfl) ⟨1414385, by rfl⟩ : syracuseStep 1885847 = 2828771) B2828771
theorem B6801047 : Blo 1256446 6801047 := bstep (se 1 (by rfl) ⟨5100785, by rfl⟩ : syracuseStep 6801047 = 10201571) B10201571
theorem B2827979 : Blo 1256446 2827979 := bstep (se 1 (by rfl) ⟨2120984, by rfl⟩ : syracuseStep 2827979 = 4241969) B4241969
theorem B1885913 : Blo 1256446 1885913 := bstep (se 2 (by rfl) ⟨707217, by rfl⟩ : syracuseStep 1885913 = 1414435) B1414435
theorem B4245209 : Blo 1256446 4245209 := bstep (se 2 (by rfl) ⟨1591953, by rfl⟩ : syracuseStep 4245209 = 3183907) B3183907
theorem B2828033 : Blo 1256446 2828033 := bstep (se 2 (by rfl) ⟨1060512, by rfl⟩ : syracuseStep 2828033 = 2121025) B2121025
theorem B2123543 : Blo 1256446 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B5367617 : Blo 1256446 5367617 := bstep (se 2 (by rfl) ⟨2012856, by rfl⟩ : syracuseStep 5367617 = 4025713) B4025713
theorem B1886027 : Blo 1256446 1886027 := bstep (se 1 (by rfl) ⟨1414520, by rfl⟩ : syracuseStep 1886027 = 2829041) B2829041
theorem B1886039 : Blo 1256446 1886039 := bstep (se 1 (by rfl) ⟨1414529, by rfl⟩ : syracuseStep 1886039 = 2829059) B2829059
theorem B1886105 : Blo 1256446 1886105 := bstep (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) B1414579
theorem B1361867 : Blo 1256446 1361867 := bstep (se 1 (by rfl) ⟨1021400, by rfl⟩ : syracuseStep 1361867 = 2042801) B2042801
theorem B1591255 : Blo 1256446 1591255 := bstep (se 1 (by rfl) ⟨1193441, by rfl⟩ : syracuseStep 1591255 = 2386883) B2386883
theorem B3180505 : Blo 1256446 3180505 := bstep (se 2 (by rfl) ⟨1192689, by rfl⟩ : syracuseStep 3180505 = 2385379) B2385379
theorem B2828249 : Blo 1256446 2828249 := bstep (se 2 (by rfl) ⟨1060593, by rfl⟩ : syracuseStep 2828249 = 2121187) B2121187
theorem B10201049 : Blo 1256446 10201049 := bstep (se 2 (by rfl) ⟨3825393, by rfl⟩ : syracuseStep 10201049 = 7650787) B7650787
theorem B4777987 : Blo 1256446 4777987 := bstep (se 1 (by rfl) ⟨3583490, by rfl⟩ : syracuseStep 4777987 = 7166981) B7166981
theorem B1886219 : Blo 1256446 1886219 := bstep (se 1 (by rfl) ⟨1414664, by rfl⟩ : syracuseStep 1886219 = 2829329) B2829329
theorem B1886231 : Blo 1256446 1886231 := bstep (se 1 (by rfl) ⟨1414673, by rfl⟩ : syracuseStep 1886231 = 2829347) B2829347
theorem B2828339 : Blo 1256446 2828339 := bstep (se 1 (by rfl) ⟨2121254, by rfl⟩ : syracuseStep 2828339 = 4242509) B4242509
theorem B2828375 : Blo 1256446 2828375 := bstep (se 1 (by rfl) ⟨2121281, by rfl⟩ : syracuseStep 2828375 = 4242563) B4242563
theorem B1910873 : Blo 1256446 1910873 := bstep (se 2 (by rfl) ⟨716577, by rfl⟩ : syracuseStep 1910873 = 1433155) B1433155
theorem B1886297 : Blo 1256446 1886297 := bstep (se 2 (by rfl) ⟨707361, by rfl⟩ : syracuseStep 1886297 = 1414723) B1414723
theorem B2549875 : Blo 1256446 2549875 := bstep (se 1 (by rfl) ⟨1912406, by rfl⟩ : syracuseStep 2549875 = 3824813) B3824813
theorem B8054963 : Blo 1256446 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B1886411 : Blo 1256446 1886411 := bstep (se 1 (by rfl) ⟨1414808, by rfl⟩ : syracuseStep 1886411 = 2829617) B2829617
theorem B1886423 : Blo 1256446 1886423 := bstep (se 1 (by rfl) ⟨1414817, by rfl⟩ : syracuseStep 1886423 = 2829635) B2829635
theorem B5736707 : Blo 1256446 5736707 := bstep (se 1 (by rfl) ⟨4302530, by rfl⟩ : syracuseStep 5736707 = 8605061) B8605061
theorem B2828555 : Blo 1256446 2828555 := bstep (se 1 (by rfl) ⟨2121416, by rfl⟩ : syracuseStep 2828555 = 4242833) B4242833
theorem B2386199 : Blo 1256446 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B1886489 : Blo 1256446 1886489 := bstep (se 2 (by rfl) ⟨707433, by rfl⟩ : syracuseStep 1886489 = 1414867) B1414867
theorem B2828609 : Blo 1256446 2828609 := bstep (se 2 (by rfl) ⟨1060728, by rfl⟩ : syracuseStep 2828609 = 2121457) B2121457
theorem B1886603 : Blo 1256446 1886603 := bstep (se 1 (by rfl) ⟨1414952, by rfl⟩ : syracuseStep 1886603 = 2829905) B2829905
theorem B1886615 : Blo 1256446 1886615 := bstep (se 1 (by rfl) ⟨1414961, by rfl⟩ : syracuseStep 1886615 = 2829923) B2829923
theorem B4245911 : Blo 1256446 4245911 := bstep (se 1 (by rfl) ⟨3184433, by rfl⟩ : syracuseStep 4245911 = 6368867) B6368867
theorem B1509835 : Blo 1256446 1509835 := bstep (se 1 (by rfl) ⟨1132376, by rfl⟩ : syracuseStep 1509835 = 2264753) B2264753
theorem B1886681 : Blo 1256446 1886681 := bstep (se 2 (by rfl) ⟨707505, by rfl⟩ : syracuseStep 1886681 = 1415011) B1415011
theorem B2828825 : Blo 1256446 2828825 := bstep (se 2 (by rfl) ⟨1060809, by rfl⟩ : syracuseStep 2828825 = 2121619) B2121619
theorem B1886795 : Blo 1256446 1886795 := bstep (se 1 (by rfl) ⟨1415096, by rfl⟩ : syracuseStep 1886795 = 2830193) B2830193
theorem B1886807 : Blo 1256446 1886807 := bstep (se 1 (by rfl) ⟨1415105, by rfl⟩ : syracuseStep 1886807 = 2830211) B2830211
theorem B2550361 : Blo 1256446 2550361 := bstep (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) B1912771
theorem B2828915 : Blo 1256446 2828915 := bstep (se 1 (by rfl) ⟨2121686, by rfl⟩ : syracuseStep 2828915 = 4243373) B4243373
theorem B2828951 : Blo 1256446 2828951 := bstep (se 1 (by rfl) ⟨2121713, by rfl⟩ : syracuseStep 2828951 = 4243427) B4243427
theorem B6367895 : Blo 1256446 6367895 := bstep (se 1 (by rfl) ⟨4775921, by rfl⟩ : syracuseStep 6367895 = 9551843) B9551843
theorem B1886873 : Blo 1256446 1886873 := bstep (se 2 (by rfl) ⟨707577, by rfl⟩ : syracuseStep 1886873 = 1415155) B1415155
theorem B8604377 : Blo 1256446 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B1592075 : Blo 1256446 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1886987 : Blo 1256446 1886987 := bstep (se 1 (by rfl) ⟨1415240, by rfl⟩ : syracuseStep 1886987 = 2830481) B2830481
theorem B1886999 : Blo 1256446 1886999 := bstep (se 1 (by rfl) ⟨1415249, by rfl⟩ : syracuseStep 1886999 = 2830499) B2830499
theorem B2386739 : Blo 1256446 2386739 := bstep (se 1 (by rfl) ⟨1790054, by rfl⟩ : syracuseStep 2386739 = 3580109) B3580109
theorem B3582785 : Blo 1256446 3582785 := bstep (se 2 (by rfl) ⟨1343544, by rfl⟩ : syracuseStep 3582785 = 2687089) B2687089
theorem B2829131 : Blo 1256446 2829131 := bstep (se 1 (by rfl) ⟨2121848, by rfl⟩ : syracuseStep 2829131 = 4243697) B4243697
theorem B1887065 : Blo 1256446 1887065 := bstep (se 2 (by rfl) ⟨707649, by rfl⟩ : syracuseStep 1887065 = 1415299) B1415299
theorem B2829185 : Blo 1256446 2829185 := bstep (se 2 (by rfl) ⟨1060944, by rfl⟩ : syracuseStep 2829185 = 2121889) B2121889
theorem B3582899 : Blo 1256446 3582899 := bstep (se 1 (by rfl) ⟨2687174, by rfl⟩ : syracuseStep 3582899 = 5374349) B5374349
theorem B4246451 : Blo 1256446 4246451 := bstep (se 1 (by rfl) ⟨3184838, by rfl⟩ : syracuseStep 4246451 = 6369677) B6369677
theorem B1887179 : Blo 1256446 1887179 := bstep (se 1 (by rfl) ⟨1415384, by rfl⟩ : syracuseStep 1887179 = 2830769) B2830769
theorem B1887191 : Blo 1256446 1887191 := bstep (se 1 (by rfl) ⟨1415393, by rfl⟩ : syracuseStep 1887191 = 2830787) B2830787
theorem B1256459 : Blo 1256446 1256459 := bstep (se 1 (by rfl) ⟨942344, by rfl⟩ : syracuseStep 1256459 = 1884689) B1884689
theorem B1256471 : Blo 1256446 1256471 := bstep (se 1 (by rfl) ⟨942353, by rfl⟩ : syracuseStep 1256471 = 1884707) B1884707
theorem B1887257 : Blo 1256446 1887257 := bstep (se 2 (by rfl) ⟨707721, by rfl⟩ : syracuseStep 1887257 = 1415443) B1415443
theorem B1256491 : Blo 1256446 1256491 := bstep (se 1 (by rfl) ⟨942368, by rfl⟩ : syracuseStep 1256491 = 1884737) B1884737
theorem B3181619 : Blo 1256446 3181619 := bstep (se 1 (by rfl) ⟨2386214, by rfl⟩ : syracuseStep 3181619 = 4772429) B4772429
theorem B1256503 : Blo 1256446 1256503 := bstep (se 1 (by rfl) ⟨942377, by rfl⟩ : syracuseStep 1256503 = 1884755) B1884755
theorem B1256523 : Blo 1256446 1256523 := bstep (se 1 (by rfl) ⟨942392, by rfl⟩ : syracuseStep 1256523 = 1884785) B1884785
theorem B1256535 : Blo 1256446 1256535 := bstep (se 1 (by rfl) ⟨942401, by rfl⟩ : syracuseStep 1256535 = 1884803) B1884803
theorem B2829401 : Blo 1256446 2829401 := bstep (se 2 (by rfl) ⟨1061025, by rfl⟩ : syracuseStep 2829401 = 2122051) B2122051
theorem B1256555 : Blo 1256446 1256555 := bstep (se 1 (by rfl) ⟨942416, by rfl⟩ : syracuseStep 1256555 = 1884833) B1884833
theorem B1256567 : Blo 1256446 1256567 := bstep (se 1 (by rfl) ⟨942425, by rfl⟩ : syracuseStep 1256567 = 1884851) B1884851
theorem B1256587 : Blo 1256446 1256587 := bstep (se 1 (by rfl) ⟨942440, by rfl⟩ : syracuseStep 1256587 = 1884881) B1884881
theorem B1887371 : Blo 1256446 1887371 := bstep (se 1 (by rfl) ⟨1415528, by rfl⟩ : syracuseStep 1887371 = 2831057) B2831057
theorem B1256599 : Blo 1256446 1256599 := bstep (se 1 (by rfl) ⟨942449, by rfl⟩ : syracuseStep 1256599 = 1884899) B1884899
theorem B1887383 : Blo 1256446 1887383 := bstep (se 1 (by rfl) ⟨1415537, by rfl⟩ : syracuseStep 1887383 = 2831075) B2831075
theorem B1256619 : Blo 1256446 1256619 := bstep (se 1 (by rfl) ⟨942464, by rfl⟩ : syracuseStep 1256619 = 1884929) B1884929
theorem B2829491 : Blo 1256446 2829491 := bstep (se 1 (by rfl) ⟨2122118, by rfl⟩ : syracuseStep 2829491 = 4244237) B4244237
theorem B1256631 : Blo 1256446 1256631 := bstep (se 1 (by rfl) ⟨942473, by rfl⟩ : syracuseStep 1256631 = 1884947) B1884947
theorem B4246721 : Blo 1256446 4246721 := bstep (se 2 (by rfl) ⟨1592520, by rfl⟩ : syracuseStep 4246721 = 3185041) B3185041
theorem B1256651 : Blo 1256446 1256651 := bstep (se 1 (by rfl) ⟨942488, by rfl⟩ : syracuseStep 1256651 = 1884977) B1884977
theorem B1256663 : Blo 1256446 1256663 := bstep (se 1 (by rfl) ⟨942497, by rfl⟩ : syracuseStep 1256663 = 1884995) B1884995
theorem B2829527 : Blo 1256446 2829527 := bstep (se 1 (by rfl) ⟨2122145, by rfl⟩ : syracuseStep 2829527 = 4244291) B4244291
theorem B1887449 : Blo 1256446 1887449 := bstep (se 2 (by rfl) ⟨707793, by rfl⟩ : syracuseStep 1887449 = 1415587) B1415587
theorem B1256683 : Blo 1256446 1256683 := bstep (se 1 (by rfl) ⟨942512, by rfl⟩ : syracuseStep 1256683 = 1885025) B1885025
theorem B1256695 : Blo 1256446 1256695 := bstep (se 1 (by rfl) ⟨942521, by rfl⟩ : syracuseStep 1256695 = 1885043) B1885043
theorem B1256715 : Blo 1256446 1256715 := bstep (se 1 (by rfl) ⟨942536, by rfl⟩ : syracuseStep 1256715 = 1885073) B1885073
theorem B1256727 : Blo 1256446 1256727 := bstep (se 1 (by rfl) ⟨942545, by rfl⟩ : syracuseStep 1256727 = 1885091) B1885091
theorem B2387225 : Blo 1256446 2387225 := bstep (se 2 (by rfl) ⟨895209, by rfl⟩ : syracuseStep 2387225 = 1790419) B1790419
theorem B1256747 : Blo 1256446 1256747 := bstep (se 1 (by rfl) ⟨942560, by rfl⟩ : syracuseStep 1256747 = 1885121) B1885121
theorem B9555245 : Blo 1256446 9555245 := bstep (se 3 (by rfl) ⟨1791608, by rfl⟩ : syracuseStep 9555245 = 3583217) B3583217
theorem B1256759 : Blo 1256446 1256759 := bstep (se 1 (by rfl) ⟨942569, by rfl⟩ : syracuseStep 1256759 = 1885139) B1885139
theorem B4025675 : Blo 1256446 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B1256779 : Blo 1256446 1256779 := bstep (se 1 (by rfl) ⟨942584, by rfl⟩ : syracuseStep 1256779 = 1885169) B1885169
theorem B1887563 : Blo 1256446 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B1256791 : Blo 1256446 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B1887575 : Blo 1256446 1887575 := bstep (se 1 (by rfl) ⟨1415681, by rfl⟩ : syracuseStep 1887575 = 2831363) B2831363
theorem B3181913 : Blo 1256446 3181913 := bstep (se 2 (by rfl) ⟨1193217, by rfl⟩ : syracuseStep 3181913 = 2386435) B2386435
theorem B11480413 : Blo 1256446 11480413 := bstep (se 3 (by rfl) ⟨2152577, by rfl⟩ : syracuseStep 11480413 = 4305155) B4305155
theorem B1256811 : Blo 1256446 1256811 := bstep (se 1 (by rfl) ⟨942608, by rfl⟩ : syracuseStep 1256811 = 1885217) B1885217
theorem B1256823 : Blo 1256446 1256823 := bstep (se 1 (by rfl) ⟨942617, by rfl⟩ : syracuseStep 1256823 = 1885235) B1885235
theorem B1256843 : Blo 1256446 1256843 := bstep (se 1 (by rfl) ⟨942632, by rfl⟩ : syracuseStep 1256843 = 1885265) B1885265
theorem B2829707 : Blo 1256446 2829707 := bstep (se 1 (by rfl) ⟨2122280, by rfl⟩ : syracuseStep 2829707 = 4244561) B4244561
theorem B1256855 : Blo 1256446 1256855 := bstep (se 1 (by rfl) ⟨942641, by rfl⟩ : syracuseStep 1256855 = 1885283) B1885283
theorem B1887641 : Blo 1256446 1887641 := bstep (se 2 (by rfl) ⟨707865, by rfl⟩ : syracuseStep 1887641 = 1415731) B1415731
theorem B1256875 : Blo 1256446 1256875 := bstep (se 1 (by rfl) ⟨942656, by rfl⟩ : syracuseStep 1256875 = 1885313) B1885313
theorem B7163315 : Blo 1256446 7163315 := bstep (se 1 (by rfl) ⟨5372486, by rfl⟩ : syracuseStep 7163315 = 10744973) B10744973
theorem B1256887 : Blo 1256446 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B2829761 : Blo 1256446 2829761 := bstep (se 2 (by rfl) ⟨1061160, by rfl⟩ : syracuseStep 2829761 = 2122321) B2122321
theorem B1256907 : Blo 1256446 1256907 := bstep (se 1 (by rfl) ⟨942680, by rfl⟩ : syracuseStep 1256907 = 1885361) B1885361
theorem B5369291 : Blo 1256446 5369291 := bstep (se 1 (by rfl) ⟨4026968, by rfl⟩ : syracuseStep 5369291 = 8053937) B8053937
theorem B1789399 : Blo 1256446 1789399 := bstep (se 1 (by rfl) ⟨1342049, by rfl⟩ : syracuseStep 1789399 = 2684099) B2684099
theorem B5443033 : Blo 1256446 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B2264537 : Blo 1256446 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B1256919 : Blo 1256446 1256919 := bstep (se 1 (by rfl) ⟨942689, by rfl⟩ : syracuseStep 1256919 = 1885379) B1885379
theorem B1256939 : Blo 1256446 1256939 := bstep (se 1 (by rfl) ⟨942704, by rfl⟩ : syracuseStep 1256939 = 1885409) B1885409
theorem B1256951 : Blo 1256446 1256951 := bstep (se 1 (by rfl) ⟨942713, by rfl⟩ : syracuseStep 1256951 = 1885427) B1885427
theorem B1256971 : Blo 1256446 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B1256983 : Blo 1256446 1256983 := bstep (se 1 (by rfl) ⟨942737, by rfl⟩ : syracuseStep 1256983 = 1885475) B1885475
theorem B1257003 : Blo 1256446 1257003 := bstep (se 1 (by rfl) ⟨942752, by rfl⟩ : syracuseStep 1257003 = 1885505) B1885505
theorem B1257015 : Blo 1256446 1257015 := bstep (se 1 (by rfl) ⟨942761, by rfl⟩ : syracuseStep 1257015 = 1885523) B1885523
theorem B1257035 : Blo 1256446 1257035 := bstep (se 1 (by rfl) ⟨942776, by rfl⟩ : syracuseStep 1257035 = 1885553) B1885553
theorem B1257047 : Blo 1256446 1257047 := bstep (se 1 (by rfl) ⟨942785, by rfl⟩ : syracuseStep 1257047 = 1885571) B1885571
theorem B1257067 : Blo 1256446 1257067 := bstep (se 1 (by rfl) ⟨942800, by rfl⟩ : syracuseStep 1257067 = 1885601) B1885601
theorem B1257079 : Blo 1256446 1257079 := bstep (se 1 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 1257079 = 1885619) B1885619
theorem B1257099 : Blo 1256446 1257099 := bstep (se 1 (by rfl) ⟨942824, by rfl⟩ : syracuseStep 1257099 = 1885649) B1885649
theorem B6794903 : Blo 1256446 6794903 := bstep (se 1 (by rfl) ⟨5096177, by rfl⟩ : syracuseStep 6794903 = 10192355) B10192355
theorem B1257111 : Blo 1256446 1257111 := bstep (se 1 (by rfl) ⟨942833, by rfl⟩ : syracuseStep 1257111 = 1885667) B1885667
theorem B2829977 : Blo 1256446 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B1257131 : Blo 1256446 1257131 := bstep (se 1 (by rfl) ⟨942848, by rfl⟩ : syracuseStep 1257131 = 1885697) B1885697
theorem B9186995 : Blo 1256446 9186995 := bstep (se 1 (by rfl) ⟨6890246, by rfl⟩ : syracuseStep 9186995 = 13780493) B13780493
theorem B1257143 : Blo 1256446 1257143 := bstep (se 1 (by rfl) ⟨942857, by rfl⟩ : syracuseStep 1257143 = 1885715) B1885715
theorem B1257163 : Blo 1256446 1257163 := bstep (se 1 (by rfl) ⟨942872, by rfl⟩ : syracuseStep 1257163 = 1885745) B1885745
theorem B9547469 : Blo 1256446 9547469 := bstep (se 3 (by rfl) ⟨1790150, by rfl⟩ : syracuseStep 9547469 = 3580301) B3580301
theorem B1257175 : Blo 1256446 1257175 := bstep (se 1 (by rfl) ⟨942881, by rfl⟩ : syracuseStep 1257175 = 1885763) B1885763
theorem B1699543 : Blo 1256446 1699543 := bstep (se 1 (by rfl) ⟨1274657, by rfl⟩ : syracuseStep 1699543 = 2549315) B2549315
theorem B1257195 : Blo 1256446 1257195 := bstep (se 1 (by rfl) ⟨942896, by rfl⟩ : syracuseStep 1257195 = 1885793) B1885793
theorem B2830067 : Blo 1256446 2830067 := bstep (se 1 (by rfl) ⟨2122550, by rfl⟩ : syracuseStep 2830067 = 4245101) B4245101
theorem B1257207 : Blo 1256446 1257207 := bstep (se 1 (by rfl) ⟨942905, by rfl⟩ : syracuseStep 1257207 = 1885811) B1885811
theorem B1257227 : Blo 1256446 1257227 := bstep (se 1 (by rfl) ⟨942920, by rfl⟩ : syracuseStep 1257227 = 1885841) B1885841
theorem B1257239 : Blo 1256446 1257239 := bstep (se 1 (by rfl) ⟨942929, by rfl⟩ : syracuseStep 1257239 = 1885859) B1885859
theorem B2830103 : Blo 1256446 2830103 := bstep (se 1 (by rfl) ⟨2122577, by rfl⟩ : syracuseStep 2830103 = 4245155) B4245155
theorem B1257259 : Blo 1256446 1257259 := bstep (se 1 (by rfl) ⟨942944, by rfl⟩ : syracuseStep 1257259 = 1885889) B1885889
theorem B5443379 : Blo 1256446 5443379 := bstep (se 1 (by rfl) ⟨4082534, by rfl⟩ : syracuseStep 5443379 = 8165069) B8165069
theorem B1257271 : Blo 1256446 1257271 := bstep (se 1 (by rfl) ⟨942953, by rfl⟩ : syracuseStep 1257271 = 1885907) B1885907
theorem B1257291 : Blo 1256446 1257291 := bstep (se 1 (by rfl) ⟨942968, by rfl⟩ : syracuseStep 1257291 = 1885937) B1885937
theorem B1257303 : Blo 1256446 1257303 := bstep (se 1 (by rfl) ⟨942977, by rfl⟩ : syracuseStep 1257303 = 1885955) B1885955
theorem B17452901 : Blo 1256446 17452901 := bstep (se 4 (by rfl) ⟨1636209, by rfl⟩ : syracuseStep 17452901 = 3272419) B3272419
theorem B1257323 : Blo 1256446 1257323 := bstep (se 1 (by rfl) ⟨942992, by rfl⟩ : syracuseStep 1257323 = 1885985) B1885985
theorem B1257335 : Blo 1256446 1257335 := bstep (se 1 (by rfl) ⟨943001, by rfl⟩ : syracuseStep 1257335 = 1886003) B1886003
theorem B2944907 : Blo 1256446 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B1257355 : Blo 1256446 1257355 := bstep (se 1 (by rfl) ⟨943016, by rfl⟩ : syracuseStep 1257355 = 1886033) B1886033
theorem B1257367 : Blo 1256446 1257367 := bstep (se 1 (by rfl) ⟨943025, by rfl⟩ : syracuseStep 1257367 = 1886051) B1886051
theorem B1257387 : Blo 1256446 1257387 := bstep (se 1 (by rfl) ⟨943040, by rfl⟩ : syracuseStep 1257387 = 1886081) B1886081
theorem B1257399 : Blo 1256446 1257399 := bstep (se 1 (by rfl) ⟨943049, by rfl⟩ : syracuseStep 1257399 = 1886099) B1886099
theorem B1257419 : Blo 1256446 1257419 := bstep (se 1 (by rfl) ⟨943064, by rfl⟩ : syracuseStep 1257419 = 1886129) B1886129
theorem B2830283 : Blo 1256446 2830283 := bstep (se 1 (by rfl) ⟨2122712, by rfl⟩ : syracuseStep 2830283 = 4245425) B4245425
theorem B1257431 : Blo 1256446 1257431 := bstep (se 1 (by rfl) ⟨943073, by rfl⟩ : syracuseStep 1257431 = 1886147) B1886147
theorem B1257451 : Blo 1256446 1257451 := bstep (se 1 (by rfl) ⟨943088, by rfl⟩ : syracuseStep 1257451 = 1886177) B1886177
theorem B1257463 : Blo 1256446 1257463 := bstep (se 1 (by rfl) ⟨943097, by rfl⟩ : syracuseStep 1257463 = 1886195) B1886195
theorem B2830337 : Blo 1256446 2830337 := bstep (se 2 (by rfl) ⟨1061376, by rfl⟩ : syracuseStep 2830337 = 2122753) B2122753
theorem B1257483 : Blo 1256446 1257483 := bstep (se 1 (by rfl) ⟨943112, by rfl⟩ : syracuseStep 1257483 = 1886225) B1886225
theorem B1257495 : Blo 1256446 1257495 := bstep (se 1 (by rfl) ⟨943121, by rfl⟩ : syracuseStep 1257495 = 1886243) B1886243
theorem B1257515 : Blo 1256446 1257515 := bstep (se 1 (by rfl) ⟨943136, by rfl⟩ : syracuseStep 1257515 = 1886273) B1886273
theorem B1257527 : Blo 1256446 1257527 := bstep (se 1 (by rfl) ⟨943145, by rfl⟩ : syracuseStep 1257527 = 1886291) B1886291
theorem B1257547 : Blo 1256446 1257547 := bstep (se 1 (by rfl) ⟨943160, by rfl⟩ : syracuseStep 1257547 = 1886321) B1886321
theorem B1257559 : Blo 1256446 1257559 := bstep (se 1 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 1257559 = 1886339) B1886339
theorem B1257579 : Blo 1256446 1257579 := bstep (se 1 (by rfl) ⟨943184, by rfl⟩ : syracuseStep 1257579 = 1886369) B1886369
theorem B1257591 : Blo 1256446 1257591 := bstep (se 1 (by rfl) ⟨943193, by rfl⟩ : syracuseStep 1257591 = 1886387) B1886387
theorem B1257611 : Blo 1256446 1257611 := bstep (se 1 (by rfl) ⟨943208, by rfl⟩ : syracuseStep 1257611 = 1886417) B1886417
theorem B1257623 : Blo 1256446 1257623 := bstep (se 1 (by rfl) ⟨943217, by rfl⟩ : syracuseStep 1257623 = 1886435) B1886435
theorem B1790105 : Blo 1256446 1790105 := bstep (se 2 (by rfl) ⟨671289, by rfl⟩ : syracuseStep 1790105 = 1342579) B1342579
theorem B1257643 : Blo 1256446 1257643 := bstep (se 1 (by rfl) ⟨943232, by rfl⟩ : syracuseStep 1257643 = 1886465) B1886465
theorem B9547955 : Blo 1256446 9547955 := bstep (se 1 (by rfl) ⟨7160966, by rfl⟩ : syracuseStep 9547955 = 14321933) B14321933
theorem B1257655 : Blo 1256446 1257655 := bstep (se 1 (by rfl) ⟨943241, by rfl⟩ : syracuseStep 1257655 = 1886483) B1886483
theorem B1257675 : Blo 1256446 1257675 := bstep (se 1 (by rfl) ⟨943256, by rfl⟩ : syracuseStep 1257675 = 1886513) B1886513
theorem B1511627 : Blo 1256446 1511627 := bstep (se 1 (by rfl) ⟨1133720, by rfl⟩ : syracuseStep 1511627 = 2267441) B2267441
theorem B1257687 : Blo 1256446 1257687 := bstep (se 1 (by rfl) ⟨943265, by rfl⟩ : syracuseStep 1257687 = 1886531) B1886531
theorem B2830553 : Blo 1256446 2830553 := bstep (se 2 (by rfl) ⟨1061457, by rfl⟩ : syracuseStep 2830553 = 2122915) B2122915
theorem B5370077 : Blo 1256446 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B1257707 : Blo 1256446 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B1257719 : Blo 1256446 1257719 := bstep (se 1 (by rfl) ⟨943289, by rfl⟩ : syracuseStep 1257719 = 1886579) B1886579
theorem B1790219 : Blo 1256446 1790219 := bstep (se 1 (by rfl) ⟨1342664, by rfl⟩ : syracuseStep 1790219 = 2685329) B2685329
theorem B1257739 : Blo 1256446 1257739 := bstep (se 1 (by rfl) ⟨943304, by rfl⟩ : syracuseStep 1257739 = 1886609) B1886609
theorem B1257751 : Blo 1256446 1257751 := bstep (se 1 (by rfl) ⟨943313, by rfl⟩ : syracuseStep 1257751 = 1886627) B1886627
theorem B1257771 : Blo 1256446 1257771 := bstep (se 1 (by rfl) ⟨943328, by rfl⟩ : syracuseStep 1257771 = 1886657) B1886657
theorem B4772141 : Blo 1256446 4772141 := bstep (se 3 (by rfl) ⟨894776, by rfl⟩ : syracuseStep 4772141 = 1789553) B1789553
theorem B2830643 : Blo 1256446 2830643 := bstep (se 1 (by rfl) ⟨2122982, by rfl⟩ : syracuseStep 2830643 = 4245965) B4245965
theorem B1257783 : Blo 1256446 1257783 := bstep (se 1 (by rfl) ⟨943337, by rfl⟩ : syracuseStep 1257783 = 1886675) B1886675
theorem B1257803 : Blo 1256446 1257803 := bstep (se 1 (by rfl) ⟨943352, by rfl⟩ : syracuseStep 1257803 = 1886705) B1886705
theorem B1257815 : Blo 1256446 1257815 := bstep (se 1 (by rfl) ⟨943361, by rfl⟩ : syracuseStep 1257815 = 1886723) B1886723
theorem B2830679 : Blo 1256446 2830679 := bstep (se 1 (by rfl) ⟨2123009, by rfl⟩ : syracuseStep 2830679 = 4246019) B4246019
theorem B1257835 : Blo 1256446 1257835 := bstep (se 1 (by rfl) ⟨943376, by rfl⟩ : syracuseStep 1257835 = 1886753) B1886753
theorem B1257847 : Blo 1256446 1257847 := bstep (se 1 (by rfl) ⟨943385, by rfl⟩ : syracuseStep 1257847 = 1886771) B1886771
theorem B1257867 : Blo 1256446 1257867 := bstep (se 1 (by rfl) ⟨943400, by rfl⟩ : syracuseStep 1257867 = 1886801) B1886801
theorem B1257879 : Blo 1256446 1257879 := bstep (se 1 (by rfl) ⟨943409, by rfl⟩ : syracuseStep 1257879 = 1886819) B1886819
theorem B1257899 : Blo 1256446 1257899 := bstep (se 1 (by rfl) ⟨943424, by rfl⟩ : syracuseStep 1257899 = 1886849) B1886849
theorem B1257911 : Blo 1256446 1257911 := bstep (se 1 (by rfl) ⟨943433, by rfl⟩ : syracuseStep 1257911 = 1886867) B1886867
theorem B1257931 : Blo 1256446 1257931 := bstep (se 1 (by rfl) ⟨943448, by rfl⟩ : syracuseStep 1257931 = 1886897) B1886897
theorem B1257943 : Blo 1256446 1257943 := bstep (se 1 (by rfl) ⟨943457, by rfl⟩ : syracuseStep 1257943 = 1886915) B1886915
theorem B1913305 : Blo 1256446 1913305 := bstep (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) B1434979
theorem B1257963 : Blo 1256446 1257963 := bstep (se 1 (by rfl) ⟨943472, by rfl⟩ : syracuseStep 1257963 = 1886945) B1886945
theorem B1257975 : Blo 1256446 1257975 := bstep (se 1 (by rfl) ⟨943481, by rfl⟩ : syracuseStep 1257975 = 1886963) B1886963
theorem B1413643 : Blo 1256446 1413643 := bstep (se 1 (by rfl) ⟨1060232, by rfl⟩ : syracuseStep 1413643 = 2120465) B2120465
theorem B1257995 : Blo 1256446 1257995 := bstep (se 1 (by rfl) ⟨943496, by rfl⟩ : syracuseStep 1257995 = 1886993) B1886993
theorem B2830859 : Blo 1256446 2830859 := bstep (se 1 (by rfl) ⟨2123144, by rfl⟩ : syracuseStep 2830859 = 4246289) B4246289
theorem B1258007 : Blo 1256446 1258007 := bstep (se 1 (by rfl) ⟨943505, by rfl⟩ : syracuseStep 1258007 = 1887011) B1887011
theorem B1258027 : Blo 1256446 1258027 := bstep (se 1 (by rfl) ⟨943520, by rfl⟩ : syracuseStep 1258027 = 1887041) B1887041
theorem B1258039 : Blo 1256446 1258039 := bstep (se 1 (by rfl) ⟨943529, by rfl⟩ : syracuseStep 1258039 = 1887059) B1887059
theorem B2830913 : Blo 1256446 2830913 := bstep (se 2 (by rfl) ⟨1061592, by rfl⟩ : syracuseStep 2830913 = 2123185) B2123185
theorem B1258059 : Blo 1256446 1258059 := bstep (se 1 (by rfl) ⟨943544, by rfl⟩ : syracuseStep 1258059 = 1887089) B1887089
theorem B1258071 : Blo 1256446 1258071 := bstep (se 1 (by rfl) ⟨943553, by rfl⟩ : syracuseStep 1258071 = 1887107) B1887107
theorem B1258091 : Blo 1256446 1258091 := bstep (se 1 (by rfl) ⟨943568, by rfl⟩ : syracuseStep 1258091 = 1887137) B1887137
theorem B1413751 : Blo 1256446 1413751 := bstep (se 1 (by rfl) ⟨1060313, by rfl⟩ : syracuseStep 1413751 = 2120627) B2120627
theorem B1258103 : Blo 1256446 1258103 := bstep (se 1 (by rfl) ⟨943577, by rfl⟩ : syracuseStep 1258103 = 1887155) B1887155
theorem B1258123 : Blo 1256446 1258123 := bstep (se 1 (by rfl) ⟨943592, by rfl⟩ : syracuseStep 1258123 = 1887185) B1887185
theorem B1258135 : Blo 1256446 1258135 := bstep (se 1 (by rfl) ⟨943601, by rfl⟩ : syracuseStep 1258135 = 1887203) B1887203
theorem B1258155 : Blo 1256446 1258155 := bstep (se 1 (by rfl) ⟨943616, by rfl⟩ : syracuseStep 1258155 = 1887233) B1887233
theorem B1258167 : Blo 1256446 1258167 := bstep (se 1 (by rfl) ⟨943625, by rfl⟩ : syracuseStep 1258167 = 1887251) B1887251
theorem B1258187 : Blo 1256446 1258187 := bstep (se 1 (by rfl) ⟨943640, by rfl⟩ : syracuseStep 1258187 = 1887281) B1887281
theorem B2388683 : Blo 1256446 2388683 := bstep (se 1 (by rfl) ⟨1791512, by rfl⟩ : syracuseStep 2388683 = 3583025) B3583025
theorem B1258199 : Blo 1256446 1258199 := bstep (se 1 (by rfl) ⟨943649, by rfl⟩ : syracuseStep 1258199 = 1887299) B1887299
theorem B1258219 : Blo 1256446 1258219 := bstep (se 1 (by rfl) ⟨943664, by rfl⟩ : syracuseStep 1258219 = 1887329) B1887329
theorem B27177713 : Blo 1256446 27177713 := bstep (se 2 (by rfl) ⟨10191642, by rfl⟩ : syracuseStep 27177713 = 20383285) B20383285
theorem B1258231 : Blo 1256446 1258231 := bstep (se 1 (by rfl) ⟨943673, by rfl⟩ : syracuseStep 1258231 = 1887347) B1887347
theorem B1258251 : Blo 1256446 1258251 := bstep (se 1 (by rfl) ⟨943688, by rfl⟩ : syracuseStep 1258251 = 1887377) B1887377
theorem B1790743 : Blo 1256446 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B1258263 : Blo 1256446 1258263 := bstep (se 1 (by rfl) ⟨943697, by rfl⟩ : syracuseStep 1258263 = 1887395) B1887395
theorem B2831129 : Blo 1256446 2831129 := bstep (se 2 (by rfl) ⟨1061673, by rfl⟩ : syracuseStep 2831129 = 2123347) B2123347
theorem B1413931 : Blo 1256446 1413931 := bstep (se 1 (by rfl) ⟨1060448, by rfl⟩ : syracuseStep 1413931 = 2120897) B2120897
theorem B1258283 : Blo 1256446 1258283 := bstep (se 1 (by rfl) ⟨943712, by rfl⟩ : syracuseStep 1258283 = 1887425) B1887425
theorem B6361901 : Blo 1256446 6361901 := bstep (se 3 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 6361901 = 2385713) B2385713
theorem B1291063 : Blo 1256446 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B1258295 : Blo 1256446 1258295 := bstep (se 1 (by rfl) ⟨943721, by rfl⟩ : syracuseStep 1258295 = 1887443) B1887443
theorem B1258315 : Blo 1256446 1258315 := bstep (se 1 (by rfl) ⟨943736, by rfl⟩ : syracuseStep 1258315 = 1887473) B1887473
theorem B1700683 : Blo 1256446 1700683 := bstep (se 1 (by rfl) ⟨1275512, by rfl⟩ : syracuseStep 1700683 = 2551025) B2551025
theorem B1258327 : Blo 1256446 1258327 := bstep (se 1 (by rfl) ⟨943745, by rfl⟩ : syracuseStep 1258327 = 1887491) B1887491
theorem B7164773 : Blo 1256446 7164773 := bstep (se 4 (by rfl) ⟨671697, by rfl⟩ : syracuseStep 7164773 = 1343395) B1343395
theorem B1258347 : Blo 1256446 1258347 := bstep (se 1 (by rfl) ⟨943760, by rfl⟩ : syracuseStep 1258347 = 1887521) B1887521
theorem B2831219 : Blo 1256446 2831219 := bstep (se 1 (by rfl) ⟨2123414, by rfl⟩ : syracuseStep 2831219 = 4246829) B4246829
theorem B1258359 : Blo 1256446 1258359 := bstep (se 1 (by rfl) ⟨943769, by rfl⟩ : syracuseStep 1258359 = 1887539) B1887539
theorem B2388865 : Blo 1256446 2388865 := bstep (se 2 (by rfl) ⟨895824, by rfl⟩ : syracuseStep 2388865 = 1791649) B1791649
theorem B1635211 : Blo 1256446 1635211 := bstep (se 1 (by rfl) ⟨1226408, by rfl⟩ : syracuseStep 1635211 = 2452817) B2452817
theorem B1258379 : Blo 1256446 1258379 := bstep (se 1 (by rfl) ⟨943784, by rfl⟩ : syracuseStep 1258379 = 1887569) B1887569
theorem B9671575 : Blo 1256446 9671575 := bstep (se 1 (by rfl) ⟨7253681, by rfl⟩ : syracuseStep 9671575 = 14507363) B14507363
theorem B1414039 : Blo 1256446 1414039 := bstep (se 1 (by rfl) ⟨1060529, by rfl⟩ : syracuseStep 1414039 = 2121059) B2121059
theorem B2831255 : Blo 1256446 2831255 := bstep (se 1 (by rfl) ⟨2123441, by rfl⟩ : syracuseStep 2831255 = 4246883) B4246883
theorem B1258391 : Blo 1256446 1258391 := bstep (se 1 (by rfl) ⟨943793, by rfl⟩ : syracuseStep 1258391 = 1887587) B1887587
theorem B1258411 : Blo 1256446 1258411 := bstep (se 1 (by rfl) ⟨943808, by rfl⟩ : syracuseStep 1258411 = 1887617) B1887617
theorem B5100461 : Blo 1256446 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B4027315 : Blo 1256446 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B1258423 : Blo 1256446 1258423 := bstep (se 1 (by rfl) ⟨943817, by rfl⟩ : syracuseStep 1258423 = 1887635) B1887635
theorem B3396545 : Blo 1256446 3396545 := bstep (se 2 (by rfl) ⟨1273704, by rfl⟩ : syracuseStep 3396545 = 2547409) B2547409
theorem B3183563 : Blo 1256446 3183563 := bstep (se 1 (by rfl) ⟨2387672, by rfl⟩ : syracuseStep 3183563 = 4775345) B4775345
theorem B1258443 : Blo 1256446 1258443 := bstep (se 1 (by rfl) ⟨943832, by rfl⟩ : syracuseStep 1258443 = 1887665) B1887665
theorem B4772915 : Blo 1256446 4772915 := bstep (se 1 (by rfl) ⟨3579686, by rfl⟩ : syracuseStep 4772915 = 7159373) B7159373
theorem B3396673 : Blo 1256446 3396673 := bstep (se 2 (by rfl) ⟨1273752, by rfl⟩ : syracuseStep 3396673 = 2547505) B2547505
theorem B1414219 : Blo 1256446 1414219 := bstep (se 1 (by rfl) ⟨1060664, by rfl⟩ : syracuseStep 1414219 = 2121329) B2121329
theorem B2831435 : Blo 1256446 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B8057987 : Blo 1256446 8057987 := bstep (se 1 (by rfl) ⟨6043490, by rfl⟩ : syracuseStep 8057987 = 12086981) B12086981
theorem B2831489 : Blo 1256446 2831489 := bstep (se 2 (by rfl) ⟨1061808, by rfl⟩ : syracuseStep 2831489 = 2123617) B2123617
theorem B1414327 : Blo 1256446 1414327 := bstep (se 1 (by rfl) ⟨1060745, by rfl⟩ : syracuseStep 1414327 = 2121491) B2121491
theorem B1414507 : Blo 1256446 1414507 := bstep (se 1 (by rfl) ⟨1060880, by rfl⟩ : syracuseStep 1414507 = 2121761) B2121761
theorem B6043031 : Blo 1256446 6043031 := bstep (se 1 (by rfl) ⟨4532273, by rfl⟩ : syracuseStep 6043031 = 9064547) B9064547
theorem B1414615 : Blo 1256446 1414615 := bstep (se 1 (by rfl) ⟨1060961, by rfl⟩ : syracuseStep 1414615 = 2121923) B2121923
theorem B1275383 : Blo 1256446 1275383 := bstep (se 1 (by rfl) ⟨956537, by rfl⟩ : syracuseStep 1275383 = 1913075) B1913075
theorem B5371409 : Blo 1256446 5371409 := bstep (se 2 (by rfl) ⟨2014278, by rfl⟩ : syracuseStep 5371409 = 4028557) B4028557
theorem B2684441 : Blo 1256446 2684441 := bstep (se 2 (by rfl) ⟨1006665, by rfl⟩ : syracuseStep 2684441 = 2013331) B2013331
theorem B4838977 : Blo 1256446 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B1791563 : Blo 1256446 1791563 := bstep (se 1 (by rfl) ⟨1343672, by rfl⟩ : syracuseStep 1791563 = 2687345) B2687345
theorem B3823193 : Blo 1256446 3823193 := bstep (se 2 (by rfl) ⟨1433697, by rfl⟩ : syracuseStep 3823193 = 2867395) B2867395
theorem B9549413 : Blo 1256446 9549413 := bstep (se 4 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 9549413 = 1790515) B1790515
theorem B1414795 : Blo 1256446 1414795 := bstep (se 1 (by rfl) ⟨1061096, by rfl⟩ : syracuseStep 1414795 = 2122193) B2122193
theorem B1414903 : Blo 1256446 1414903 := bstep (se 1 (by rfl) ⟨1061177, by rfl⟩ : syracuseStep 1414903 = 2122355) B2122355
theorem B16119557 : Blo 1256446 16119557 := bstep (se 4 (by rfl) ⟨1511208, by rfl⟩ : syracuseStep 16119557 = 3022417) B3022417
theorem B6051601 : Blo 1256446 6051601 := bstep (se 2 (by rfl) ⟨2269350, by rfl⟩ : syracuseStep 6051601 = 4538701) B4538701
theorem B4028249 : Blo 1256446 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B3184535 : Blo 1256446 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B1415083 : Blo 1256446 1415083 := bstep (se 1 (by rfl) ⟨1061312, by rfl⟩ : syracuseStep 1415083 = 2122625) B2122625
theorem B29013977 : Blo 1256446 29013977 := bstep (se 2 (by rfl) ⟨10880241, by rfl⟩ : syracuseStep 29013977 = 21760483) B21760483
theorem B9541637 : Blo 1256446 9541637 := bstep (se 4 (by rfl) ⟨894528, by rfl⟩ : syracuseStep 9541637 = 1789057) B1789057
theorem B1415191 : Blo 1256446 1415191 := bstep (se 1 (by rfl) ⟨1061393, by rfl⟩ : syracuseStep 1415191 = 2122787) B2122787
theorem B4241483 : Blo 1256446 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B9549899 : Blo 1256446 9549899 := bstep (se 1 (by rfl) ⟨7162424, by rfl⟩ : syracuseStep 9549899 = 14324849) B14324849
theorem B21493835 : Blo 1256446 21493835 := bstep (se 1 (by rfl) ⟨16120376, by rfl⟩ : syracuseStep 21493835 = 32240753) B32240753
theorem B4028609 : Blo 1256446 4028609 := bstep (se 2 (by rfl) ⟨1510728, by rfl⟩ : syracuseStep 4028609 = 3021457) B3021457
theorem B1415371 : Blo 1256446 1415371 := bstep (se 1 (by rfl) ⟨1061528, by rfl⟩ : syracuseStep 1415371 = 2123057) B2123057
theorem B1415479 : Blo 1256446 1415479 := bstep (se 1 (by rfl) ⟨1061609, by rfl⟩ : syracuseStep 1415479 = 2123219) B2123219
theorem B3021131 : Blo 1256446 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B4241753 : Blo 1256446 4241753 := bstep (se 2 (by rfl) ⟨1590657, by rfl⟩ : syracuseStep 4241753 = 3181315) B3181315
theorem B9058691 : Blo 1256446 9058691 := bstep (se 1 (by rfl) ⟨6794018, by rfl⟩ : syracuseStep 9058691 = 13588037) B13588037
theorem B44775829 : Blo 1256446 44775829 := bstep (se 6 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 44775829 = 2098867) B2098867
theorem B7158233 : Blo 1256446 7158233 := bstep (se 2 (by rfl) ⟨2684337, by rfl⟩ : syracuseStep 7158233 = 5368675) B5368675
theorem B1415659 : Blo 1256446 1415659 := bstep (se 1 (by rfl) ⟨1061744, by rfl⟩ : syracuseStep 1415659 = 2123489) B2123489
theorem B4774403 : Blo 1256446 4774403 := bstep (se 1 (by rfl) ⟨3580802, by rfl⟩ : syracuseStep 4774403 = 7161605) B7161605
theorem B14326307 : Blo 1256446 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B3185203 : Blo 1256446 3185203 := bstep (se 1 (by rfl) ⟨2388902, by rfl⟩ : syracuseStep 3185203 = 4777805) B4777805
theorem B3185345 : Blo 1256446 3185345 := bstep (se 2 (by rfl) ⟨1194504, by rfl⟩ : syracuseStep 3185345 = 2389009) B2389009
theorem B5372675 : Blo 1256446 5372675 := bstep (se 1 (by rfl) ⟨4029506, by rfl⟩ : syracuseStep 5372675 = 8059013) B8059013
theorem B1342391 : Blo 1256446 1342391 := bstep (se 1 (by rfl) ⟨1006793, by rfl⟩ : syracuseStep 1342391 = 2013587) B2013587
theorem B4774859 : Blo 1256446 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B4242455 : Blo 1256446 4242455 := bstep (se 1 (by rfl) ⟨3181841, by rfl⟩ : syracuseStep 4242455 = 6363683) B6363683
theorem B17448029 : Blo 1256446 17448029 := bstep (se 3 (by rfl) ⟨3271505, by rfl⟩ : syracuseStep 17448029 = 6543011) B6543011
theorem B2686081 : Blo 1256446 2686081 := bstep (se 2 (by rfl) ⟨1007280, by rfl⟩ : syracuseStep 2686081 = 2014561) B2014561
theorem B2120843 : Blo 1256446 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B4775057 : Blo 1256446 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B45890711 : Blo 1256446 45890711 := bstep (se 1 (by rfl) ⟨34418033, by rfl⟩ : syracuseStep 45890711 = 68836067) B68836067
theorem B2120971 : Blo 1256446 2120971 := bstep (se 1 (by rfl) ⟨1590728, by rfl⟩ : syracuseStep 2120971 = 3181457) B3181457
theorem B2620759 : Blo 1256446 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B2121113 : Blo 1256446 2121113 := bstep (se 2 (by rfl) ⟨795417, by rfl⟩ : syracuseStep 2121113 = 1590835) B1590835
theorem B2866711 : Blo 1256446 2866711 := bstep (se 1 (by rfl) ⟨2150033, by rfl⟩ : syracuseStep 2866711 = 4300067) B4300067
theorem B2121241 : Blo 1256446 2121241 := bstep (se 2 (by rfl) ⟨795465, by rfl⟩ : syracuseStep 2121241 = 1590931) B1590931
theorem B4242995 : Blo 1256446 4242995 := bstep (se 1 (by rfl) ⟨3182246, by rfl⟩ : syracuseStep 4242995 = 6364493) B6364493
theorem B3628595 : Blo 1256446 3628595 := bstep (se 1 (by rfl) ⟨2721446, by rfl⟩ : syracuseStep 3628595 = 5442893) B5442893
theorem B3579481 : Blo 1256446 3579481 := bstep (se 2 (by rfl) ⟨1342305, by rfl⟩ : syracuseStep 3579481 = 2684611) B2684611
theorem B2686679 : Blo 1256446 2686679 := bstep (se 1 (by rfl) ⟨2015009, by rfl⟩ : syracuseStep 2686679 = 4030019) B4030019
theorem B10190609 : Blo 1256446 10190609 := bstep (se 2 (by rfl) ⟨3821478, by rfl⟩ : syracuseStep 10190609 = 7642957) B7642957
theorem B4243265 : Blo 1256446 4243265 := bstep (se 2 (by rfl) ⟨1591224, by rfl⟩ : syracuseStep 4243265 = 3182449) B3182449
theorem B9068381 : Blo 1256446 9068381 := bstep (se 3 (by rfl) ⟨1700321, by rfl⟩ : syracuseStep 9068381 = 3400643) B3400643
theorem B2547571 : Blo 1256446 2547571 := bstep (se 1 (by rfl) ⟨1910678, by rfl⟩ : syracuseStep 2547571 = 3821357) B3821357
theorem B4775831 : Blo 1256446 4775831 := bstep (se 1 (by rfl) ⟨3581873, by rfl⟩ : syracuseStep 4775831 = 7163747) B7163747
theorem B5169113 : Blo 1256446 5169113 := bstep (se 2 (by rfl) ⟨1938417, by rfl⟩ : syracuseStep 5169113 = 3876835) B3876835
theorem B3579869 : Blo 1256446 3579869 := bstep (se 3 (by rfl) ⟨671225, by rfl⟩ : syracuseStep 3579869 = 1342451) B1342451
theorem B6365303 : Blo 1256446 6365303 := bstep (se 1 (by rfl) ⟨4773977, by rfl⟩ : syracuseStep 6365303 = 9547955) B9547955
theorem B3580051 : Blo 1256446 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B3399833 : Blo 1256446 3399833 := bstep (se 2 (by rfl) ⟨1274937, by rfl⟩ : syracuseStep 3399833 = 2549875) B2549875
theorem B4243859 : Blo 1256446 4243859 := bstep (se 1 (by rfl) ⟨3182894, by rfl⟩ : syracuseStep 4243859 = 6365789) B6365789
theorem B1884731 : Blo 1256446 1884731 := bstep (se 1 (by rfl) ⟨1413548, by rfl⟩ : syracuseStep 1884731 = 2827097) B2827097
theorem B18612803 : Blo 1256446 18612803 := bstep (se 1 (by rfl) ⟨13959602, by rfl⟩ : syracuseStep 18612803 = 27919205) B27919205
theorem B4776515 : Blo 1256446 4776515 := bstep (se 1 (by rfl) ⟨3582386, by rfl⟩ : syracuseStep 4776515 = 7164773) B7164773
theorem B3400307 : Blo 1256446 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B1884791 : Blo 1256446 1884791 := bstep (se 1 (by rfl) ⟨1413593, by rfl⟩ : syracuseStep 1884791 = 2827187) B2827187
theorem B2122375 : Blo 1256446 2122375 := bstep (se 1 (by rfl) ⟨1591781, by rfl⟩ : syracuseStep 2122375 = 3183563) B3183563
theorem B1884815 : Blo 1256446 1884815 := bstep (se 1 (by rfl) ⟨1413611, by rfl⟩ : syracuseStep 1884815 = 2827223) B2827223
theorem B1884857 : Blo 1256446 1884857 := bstep (se 2 (by rfl) ⟨706821, by rfl⟩ : syracuseStep 1884857 = 1413643) B1413643
theorem B1884935 : Blo 1256446 1884935 := bstep (se 1 (by rfl) ⟨1413701, by rfl⟩ : syracuseStep 1884935 = 2827403) B2827403
theorem B3400481 : Blo 1256446 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B1884971 : Blo 1256446 1884971 := bstep (se 1 (by rfl) ⟨1413728, by rfl⟩ : syracuseStep 1884971 = 2827457) B2827457
theorem B1885001 : Blo 1256446 1885001 := bstep (se 2 (by rfl) ⟨706875, by rfl⟩ : syracuseStep 1885001 = 1413751) B1413751
theorem B1885115 : Blo 1256446 1885115 := bstep (se 1 (by rfl) ⟨1413836, by rfl⟩ : syracuseStep 1885115 = 2827673) B2827673
theorem B1885175 : Blo 1256446 1885175 := bstep (se 1 (by rfl) ⟨1413881, by rfl⟩ : syracuseStep 1885175 = 2827763) B2827763
theorem B22938635 : Blo 1256446 22938635 := bstep (se 1 (by rfl) ⟨17203976, by rfl⟩ : syracuseStep 22938635 = 34407953) B34407953
theorem B3580939 : Blo 1256446 3580939 := bstep (se 1 (by rfl) ⟨2685704, by rfl⟩ : syracuseStep 3580939 = 5371409) B5371409
theorem B1885199 : Blo 1256446 1885199 := bstep (se 1 (by rfl) ⟨1413899, by rfl⟩ : syracuseStep 1885199 = 2827799) B2827799
theorem B1885241 : Blo 1256446 1885241 := bstep (se 2 (by rfl) ⟨706965, by rfl⟩ : syracuseStep 1885241 = 1413931) B1413931
theorem B2548795 : Blo 1256446 2548795 := bstep (se 1 (by rfl) ⟨1911596, by rfl⟩ : syracuseStep 2548795 = 3823193) B3823193
theorem B6366275 : Blo 1256446 6366275 := bstep (se 1 (by rfl) ⟨4774706, by rfl⟩ : syracuseStep 6366275 = 9549413) B9549413
theorem B1721417 : Blo 1256446 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B12256343 : Blo 1256446 12256343 := bstep (se 1 (by rfl) ⟨9192257, by rfl⟩ : syracuseStep 12256343 = 18384515) B18384515
theorem B1885319 : Blo 1256446 1885319 := bstep (se 1 (by rfl) ⟨1413989, by rfl⟩ : syracuseStep 1885319 = 2827979) B2827979
theorem B1885355 : Blo 1256446 1885355 := bstep (se 1 (by rfl) ⟨1414016, by rfl⟩ : syracuseStep 1885355 = 2828033) B2828033
theorem B12895433 : Blo 1256446 12895433 := bstep (se 2 (by rfl) ⟨4835787, by rfl⟩ : syracuseStep 12895433 = 9671575) B9671575
theorem B1885385 : Blo 1256446 1885385 := bstep (se 2 (by rfl) ⟨707019, by rfl⟩ : syracuseStep 1885385 = 1414039) B1414039
theorem B2123023 : Blo 1256446 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B19342651 : Blo 1256446 19342651 := bstep (se 1 (by rfl) ⟨14506988, by rfl⟩ : syracuseStep 19342651 = 29013977) B29013977
theorem B1885499 : Blo 1256446 1885499 := bstep (se 1 (by rfl) ⟨1414124, by rfl⟩ : syracuseStep 1885499 = 2828249) B2828249
theorem B6800699 : Blo 1256446 6800699 := bstep (se 1 (by rfl) ⟨5100524, by rfl⟩ : syracuseStep 6800699 = 10201049) B10201049
theorem B3401021 : Blo 1256446 3401021 := bstep (se 3 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 3401021 = 1275383) B1275383
theorem B6456665 : Blo 1256446 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B1885559 : Blo 1256446 1885559 := bstep (se 1 (by rfl) ⟨1414169, by rfl⟩ : syracuseStep 1885559 = 2828339) B2828339
theorem B2827655 : Blo 1256446 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B6366599 : Blo 1256446 6366599 := bstep (se 1 (by rfl) ⟨4774949, by rfl⟩ : syracuseStep 6366599 = 9549899) B9549899
theorem B14329223 : Blo 1256446 14329223 := bstep (se 1 (by rfl) ⟨10746917, by rfl⟩ : syracuseStep 14329223 = 21493835) B21493835
theorem B1885583 : Blo 1256446 1885583 := bstep (se 1 (by rfl) ⟨1414187, by rfl⟩ : syracuseStep 1885583 = 2828375) B2828375
theorem B1885625 : Blo 1256446 1885625 := bstep (se 2 (by rfl) ⟨707109, by rfl⟩ : syracuseStep 1885625 = 1414219) B1414219
theorem B9676253 : Blo 1256446 9676253 := bstep (se 3 (by rfl) ⟨1814297, by rfl⟩ : syracuseStep 9676253 = 3628595) B3628595
theorem B3581441 : Blo 1256446 3581441 := bstep (se 2 (by rfl) ⟨1343040, by rfl⟩ : syracuseStep 3581441 = 2686081) B2686081
theorem B1885703 : Blo 1256446 1885703 := bstep (se 1 (by rfl) ⟨1414277, by rfl⟩ : syracuseStep 1885703 = 2828555) B2828555
theorem B4777501 : Blo 1256446 4777501 := bstep (se 3 (by rfl) ⟨895781, by rfl⟩ : syracuseStep 4777501 = 1791563) B1791563
theorem B1885739 : Blo 1256446 1885739 := bstep (se 1 (by rfl) ⟨1414304, by rfl⟩ : syracuseStep 1885739 = 2828609) B2828609
theorem B2827835 : Blo 1256446 2827835 := bstep (se 1 (by rfl) ⟨2120876, by rfl⟩ : syracuseStep 2827835 = 4241753) B4241753
theorem B1885769 : Blo 1256446 1885769 := bstep (se 2 (by rfl) ⟨707163, by rfl⟩ : syracuseStep 1885769 = 1414327) B1414327
theorem B6039127 : Blo 1256446 6039127 := bstep (se 1 (by rfl) ⟨4529345, by rfl⟩ : syracuseStep 6039127 = 9058691) B9058691
theorem B2827961 : Blo 1256446 2827961 := bstep (se 2 (by rfl) ⟨1060485, by rfl⟩ : syracuseStep 2827961 = 2120971) B2120971
theorem B1885883 : Blo 1256446 1885883 := bstep (se 1 (by rfl) ⟨1414412, by rfl⟩ : syracuseStep 1885883 = 2828825) B2828825
theorem B9070309 : Blo 1256446 9070309 := bstep (se 4 (by rfl) ⟨850341, by rfl⟩ : syracuseStep 9070309 = 1700683) B1700683
theorem B1885943 : Blo 1256446 1885943 := bstep (se 1 (by rfl) ⟨1414457, by rfl⟩ : syracuseStep 1885943 = 2828915) B2828915
theorem B1885967 : Blo 1256446 1885967 := bstep (se 1 (by rfl) ⟨1414475, by rfl⟩ : syracuseStep 1885967 = 2828951) B2828951
theorem B4245263 : Blo 1256446 4245263 := bstep (se 1 (by rfl) ⟨3183947, by rfl⟩ : syracuseStep 4245263 = 6367895) B6367895
theorem B2123563 : Blo 1256446 2123563 := bstep (se 1 (by rfl) ⟨1592672, by rfl⟩ : syracuseStep 2123563 = 3185345) B3185345
theorem B1886009 : Blo 1256446 1886009 := bstep (se 2 (by rfl) ⟨707253, by rfl⟩ : syracuseStep 1886009 = 1414507) B1414507
theorem B5736251 : Blo 1256446 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B3581783 : Blo 1256446 3581783 := bstep (se 1 (by rfl) ⟨2686337, by rfl⟩ : syracuseStep 3581783 = 5372675) B5372675
theorem B12912473 : Blo 1256446 12912473 := bstep (se 2 (by rfl) ⟨4842177, by rfl⟩ : syracuseStep 12912473 = 9684355) B9684355
theorem B1591159 : Blo 1256446 1591159 := bstep (se 1 (by rfl) ⟨1193369, by rfl⟩ : syracuseStep 1591159 = 2386739) B2386739
theorem B1886087 : Blo 1256446 1886087 := bstep (se 1 (by rfl) ⟨1414565, by rfl⟩ : syracuseStep 1886087 = 2829131) B2829131
theorem B1886123 : Blo 1256446 1886123 := bstep (se 1 (by rfl) ⟨1414592, by rfl⟩ : syracuseStep 1886123 = 2829185) B2829185
theorem B2385865 : Blo 1256446 2385865 := bstep (se 2 (by rfl) ⟨894699, by rfl⟩ : syracuseStep 2385865 = 1789399) B1789399
theorem B1886153 : Blo 1256446 1886153 := bstep (se 2 (by rfl) ⟨707307, by rfl⟩ : syracuseStep 1886153 = 1414615) B1414615
theorem B2828303 : Blo 1256446 2828303 := bstep (se 1 (by rfl) ⟨2121227, by rfl⟩ : syracuseStep 2828303 = 4242455) B4242455
theorem B4245533 : Blo 1256446 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B2828321 : Blo 1256446 2828321 := bstep (se 2 (by rfl) ⟨1060620, by rfl⟩ : syracuseStep 2828321 = 2121241) B2121241
theorem B1886267 : Blo 1256446 1886267 := bstep (se 1 (by rfl) ⟨1414700, by rfl⟩ : syracuseStep 1886267 = 2829401) B2829401
theorem B16124021 : Blo 1256446 16124021 := bstep (se 5 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 16124021 = 1511627) B1511627
theorem B1886327 : Blo 1256446 1886327 := bstep (se 1 (by rfl) ⟨1414745, by rfl⟩ : syracuseStep 1886327 = 2829491) B2829491
theorem B1886351 : Blo 1256446 1886351 := bstep (se 1 (by rfl) ⟨1414763, by rfl⟩ : syracuseStep 1886351 = 2829527) B2829527
theorem B1886393 : Blo 1256446 1886393 := bstep (se 2 (by rfl) ⟨707397, by rfl⟩ : syracuseStep 1886393 = 1414795) B1414795
theorem B1591483 : Blo 1256446 1591483 := bstep (se 1 (by rfl) ⟨1193612, by rfl⟩ : syracuseStep 1591483 = 2387225) B2387225
theorem B10741997 : Blo 1256446 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B1886471 : Blo 1256446 1886471 := bstep (se 1 (by rfl) ⟨1414853, by rfl⟩ : syracuseStep 1886471 = 2829707) B2829707
theorem B46541069 : Blo 1256446 46541069 := bstep (se 3 (by rfl) ⟨8726450, by rfl⟩ : syracuseStep 46541069 = 17452901) B17452901
theorem B1886507 : Blo 1256446 1886507 := bstep (se 1 (by rfl) ⟨1414880, by rfl⟩ : syracuseStep 1886507 = 2829761) B2829761
theorem B1509691 : Blo 1256446 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B1886537 : Blo 1256446 1886537 := bstep (se 2 (by rfl) ⟨707451, by rfl⟩ : syracuseStep 1886537 = 1414903) B1414903
theorem B2828663 : Blo 1256446 2828663 := bstep (se 1 (by rfl) ⟨2121497, by rfl⟩ : syracuseStep 2828663 = 4242995) B4242995
theorem B1886651 : Blo 1256446 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B1886711 : Blo 1256446 1886711 := bstep (se 1 (by rfl) ⟨1415033, by rfl⟩ : syracuseStep 1886711 = 2830067) B2830067
theorem B6793739 : Blo 1256446 6793739 := bstep (se 1 (by rfl) ⟨5095304, by rfl⟩ : syracuseStep 6793739 = 10190609) B10190609
theorem B1886735 : Blo 1256446 1886735 := bstep (se 1 (by rfl) ⟨1415051, by rfl⟩ : syracuseStep 1886735 = 2830103) B2830103
theorem B3631645 : Blo 1256446 3631645 := bstep (se 3 (by rfl) ⟨680933, by rfl⟩ : syracuseStep 3631645 = 1361867) B1361867
theorem B2828843 : Blo 1256446 2828843 := bstep (se 1 (by rfl) ⟨2121632, by rfl⟩ : syracuseStep 2828843 = 4243265) B4243265
theorem B1886777 : Blo 1256446 1886777 := bstep (se 2 (by rfl) ⟨707541, by rfl⟩ : syracuseStep 1886777 = 1415083) B1415083
theorem B1886855 : Blo 1256446 1886855 := bstep (se 1 (by rfl) ⟨1415141, by rfl⟩ : syracuseStep 1886855 = 2830283) B2830283
theorem B2386579 : Blo 1256446 2386579 := bstep (se 1 (by rfl) ⟨1789934, by rfl⟩ : syracuseStep 2386579 = 3579869) B3579869
theorem B1886891 : Blo 1256446 1886891 := bstep (se 1 (by rfl) ⟨1415168, by rfl⟩ : syracuseStep 1886891 = 2830337) B2830337
theorem B1886921 : Blo 1256446 1886921 := bstep (se 2 (by rfl) ⟨707595, by rfl⟩ : syracuseStep 1886921 = 1415191) B1415191
theorem B9546497 : Blo 1256446 9546497 := bstep (se 2 (by rfl) ⟨3579936, by rfl⟩ : syracuseStep 9546497 = 7159873) B7159873
theorem B1887035 : Blo 1256446 1887035 := bstep (se 1 (by rfl) ⟨1415276, by rfl⟩ : syracuseStep 1887035 = 2830553) B2830553
theorem B3181427 : Blo 1256446 3181427 := bstep (se 1 (by rfl) ⟨2386070, by rfl⟩ : syracuseStep 3181427 = 4772141) B4772141
theorem B1887095 : Blo 1256446 1887095 := bstep (se 1 (by rfl) ⟨1415321, by rfl⟩ : syracuseStep 1887095 = 2830643) B2830643
theorem B1887119 : Blo 1256446 1887119 := bstep (se 1 (by rfl) ⟨1415339, by rfl⟩ : syracuseStep 1887119 = 2830679) B2830679
theorem B2829203 : Blo 1256446 2829203 := bstep (se 1 (by rfl) ⟨2121902, by rfl⟩ : syracuseStep 2829203 = 4243805) B4243805
theorem B1887161 : Blo 1256446 1887161 := bstep (se 2 (by rfl) ⟨707685, by rfl⟩ : syracuseStep 1887161 = 1415371) B1415371
theorem B2829257 : Blo 1256446 2829257 := bstep (se 2 (by rfl) ⟨1060971, by rfl⟩ : syracuseStep 2829257 = 2121943) B2121943
theorem B18115589 : Blo 1256446 18115589 := bstep (se 4 (by rfl) ⟨1698336, by rfl⟩ : syracuseStep 18115589 = 3396673) B3396673
theorem B1256455 : Blo 1256446 1256455 := bstep (se 1 (by rfl) ⟨942341, by rfl⟩ : syracuseStep 1256455 = 1884683) B1884683
theorem B1887239 : Blo 1256446 1887239 := bstep (se 1 (by rfl) ⟨1415429, by rfl⟩ : syracuseStep 1887239 = 2830859) B2830859
theorem B1256463 : Blo 1256446 1256463 := bstep (se 1 (by rfl) ⟨942347, by rfl⟩ : syracuseStep 1256463 = 1884695) B1884695
theorem B1887275 : Blo 1256446 1887275 := bstep (se 1 (by rfl) ⟨1415456, by rfl⟩ : syracuseStep 1887275 = 2830913) B2830913
theorem B1256507 : Blo 1256446 1256507 := bstep (se 1 (by rfl) ⟨942380, by rfl⟩ : syracuseStep 1256507 = 1884761) B1884761
theorem B1887305 : Blo 1256446 1887305 := bstep (se 2 (by rfl) ⟨707739, by rfl⟩ : syracuseStep 1887305 = 1415479) B1415479
theorem B1256583 : Blo 1256446 1256583 := bstep (se 1 (by rfl) ⟨942437, by rfl⟩ : syracuseStep 1256583 = 1884875) B1884875
theorem B1592455 : Blo 1256446 1592455 := bstep (se 1 (by rfl) ⟨1194341, by rfl⟩ : syracuseStep 1592455 = 2388683) B2388683
theorem B1256591 : Blo 1256446 1256591 := bstep (se 1 (by rfl) ⟨942443, by rfl⟩ : syracuseStep 1256591 = 1884887) B1884887
theorem B1256635 : Blo 1256446 1256635 := bstep (se 1 (by rfl) ⟨942476, by rfl⟩ : syracuseStep 1256635 = 1884953) B1884953
theorem B1887419 : Blo 1256446 1887419 := bstep (se 1 (by rfl) ⟨1415564, by rfl⟩ : syracuseStep 1887419 = 2831129) B2831129
theorem B1887479 : Blo 1256446 1887479 := bstep (se 1 (by rfl) ⟨1415609, by rfl⟩ : syracuseStep 1887479 = 2831219) B2831219
theorem B1256711 : Blo 1256446 1256711 := bstep (se 1 (by rfl) ⟨942533, by rfl⟩ : syracuseStep 1256711 = 1885067) B1885067
theorem B1256719 : Blo 1256446 1256719 := bstep (se 1 (by rfl) ⟨942539, by rfl⟩ : syracuseStep 1256719 = 1885079) B1885079
theorem B1887503 : Blo 1256446 1887503 := bstep (se 1 (by rfl) ⟨1415627, by rfl⟩ : syracuseStep 1887503 = 2831255) B2831255
theorem B2551073 : Blo 1256446 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B2264363 : Blo 1256446 2264363 := bstep (se 1 (by rfl) ⟨1698272, by rfl⟩ : syracuseStep 2264363 = 3396545) B3396545
theorem B1887545 : Blo 1256446 1887545 := bstep (se 2 (by rfl) ⟨707829, by rfl⟩ : syracuseStep 1887545 = 1415659) B1415659
theorem B1256763 : Blo 1256446 1256763 := bstep (se 1 (by rfl) ⟨942572, by rfl⟩ : syracuseStep 1256763 = 1885145) B1885145
theorem B3181943 : Blo 1256446 3181943 := bstep (se 1 (by rfl) ⟨2386457, by rfl⟩ : syracuseStep 3181943 = 4772915) B4772915
theorem B1256839 : Blo 1256446 1256839 := bstep (se 1 (by rfl) ⟨942629, by rfl⟩ : syracuseStep 1256839 = 1885259) B1885259
theorem B1887623 : Blo 1256446 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B1256847 : Blo 1256446 1256847 := bstep (se 1 (by rfl) ⟨942635, by rfl⟩ : syracuseStep 1256847 = 1885271) B1885271
theorem B4246937 : Blo 1256446 4246937 := bstep (se 2 (by rfl) ⟨1592601, by rfl⟩ : syracuseStep 4246937 = 3185203) B3185203
theorem B1887659 : Blo 1256446 1887659 := bstep (se 1 (by rfl) ⟨1415744, by rfl⟩ : syracuseStep 1887659 = 2831489) B2831489
theorem B1256891 : Blo 1256446 1256891 := bstep (se 1 (by rfl) ⟨942668, by rfl⟩ : syracuseStep 1256891 = 1885337) B1885337
theorem B1256967 : Blo 1256446 1256967 := bstep (se 1 (by rfl) ⟨942725, by rfl⟩ : syracuseStep 1256967 = 1885451) B1885451
theorem B1256975 : Blo 1256446 1256975 := bstep (se 1 (by rfl) ⟨942731, by rfl⟩ : syracuseStep 1256975 = 1885463) B1885463
theorem B1257019 : Blo 1256446 1257019 := bstep (se 1 (by rfl) ⟨942764, by rfl⟩ : syracuseStep 1257019 = 1885529) B1885529
theorem B1257095 : Blo 1256446 1257095 := bstep (se 1 (by rfl) ⟨942821, by rfl⟩ : syracuseStep 1257095 = 1885643) B1885643
theorem B2829959 : Blo 1256446 2829959 := bstep (se 1 (by rfl) ⟨2122469, by rfl⟩ : syracuseStep 2829959 = 4244939) B4244939
theorem B1257103 : Blo 1256446 1257103 := bstep (se 1 (by rfl) ⟨942827, by rfl⟩ : syracuseStep 1257103 = 1885655) B1885655
theorem B18132659 : Blo 1256446 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B1789627 : Blo 1256446 1789627 := bstep (se 1 (by rfl) ⟨1342220, by rfl⟩ : syracuseStep 1789627 = 2684441) B2684441
theorem B1257147 : Blo 1256446 1257147 := bstep (se 1 (by rfl) ⟨942860, by rfl⟩ : syracuseStep 1257147 = 1885721) B1885721
theorem B2387657 : Blo 1256446 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B1257223 : Blo 1256446 1257223 := bstep (se 1 (by rfl) ⟨942917, by rfl⟩ : syracuseStep 1257223 = 1885835) B1885835
theorem B1257231 : Blo 1256446 1257231 := bstep (se 1 (by rfl) ⟨942923, by rfl⟩ : syracuseStep 1257231 = 1885847) B1885847
theorem B4534031 : Blo 1256446 4534031 := bstep (se 1 (by rfl) ⟨3400523, by rfl⟩ : syracuseStep 4534031 = 6801047) B6801047
theorem B61189937 : Blo 1256446 61189937 := bstep (se 2 (by rfl) ⟨22946226, by rfl⟩ : syracuseStep 61189937 = 45892453) B45892453
theorem B1257275 : Blo 1256446 1257275 := bstep (se 1 (by rfl) ⟨942956, by rfl⟩ : syracuseStep 1257275 = 1885913) B1885913
theorem B2830139 : Blo 1256446 2830139 := bstep (se 1 (by rfl) ⟨2122604, by rfl⟩ : syracuseStep 2830139 = 4245209) B4245209
theorem B1257351 : Blo 1256446 1257351 := bstep (se 1 (by rfl) ⟨943013, by rfl⟩ : syracuseStep 1257351 = 1886027) B1886027
theorem B1257359 : Blo 1256446 1257359 := bstep (se 1 (by rfl) ⟨943019, by rfl⟩ : syracuseStep 1257359 = 1886039) B1886039
theorem B5369753 : Blo 1256446 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B2830265 : Blo 1256446 2830265 := bstep (se 2 (by rfl) ⟨1061349, by rfl⟩ : syracuseStep 2830265 = 2122699) B2122699
theorem B1257403 : Blo 1256446 1257403 := bstep (se 1 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 1257403 = 1886105) B1886105
theorem B6361091 : Blo 1256446 6361091 := bstep (se 1 (by rfl) ⟨4770818, by rfl⟩ : syracuseStep 6361091 = 9541637) B9541637
theorem B1257479 : Blo 1256446 1257479 := bstep (se 1 (by rfl) ⟨943109, by rfl⟩ : syracuseStep 1257479 = 1886219) B1886219
theorem B1257487 : Blo 1256446 1257487 := bstep (se 1 (by rfl) ⟨943115, by rfl⟩ : syracuseStep 1257487 = 1886231) B1886231
theorem B1273915 : Blo 1256446 1273915 := bstep (se 1 (by rfl) ⟨955436, by rfl⟩ : syracuseStep 1273915 = 1910873) B1910873
theorem B1257531 : Blo 1256446 1257531 := bstep (se 1 (by rfl) ⟨943148, by rfl⟩ : syracuseStep 1257531 = 1886297) B1886297
theorem B5369975 : Blo 1256446 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B1257607 : Blo 1256446 1257607 := bstep (se 1 (by rfl) ⟨943205, by rfl⟩ : syracuseStep 1257607 = 1886411) B1886411
theorem B1257615 : Blo 1256446 1257615 := bstep (se 1 (by rfl) ⟨943211, by rfl⟩ : syracuseStep 1257615 = 1886423) B1886423
theorem B1257659 : Blo 1256446 1257659 := bstep (se 1 (by rfl) ⟨943244, by rfl⟩ : syracuseStep 1257659 = 1886489) B1886489
theorem B1257735 : Blo 1256446 1257735 := bstep (se 1 (by rfl) ⟨943301, by rfl⟩ : syracuseStep 1257735 = 1886603) B1886603
theorem B1257743 : Blo 1256446 1257743 := bstep (se 1 (by rfl) ⟨943307, by rfl⟩ : syracuseStep 1257743 = 1886615) B1886615
theorem B2830607 : Blo 1256446 2830607 := bstep (se 1 (by rfl) ⟨2122955, by rfl⟩ : syracuseStep 2830607 = 4245911) B4245911
theorem B2830625 : Blo 1256446 2830625 := bstep (se 2 (by rfl) ⟨1061484, by rfl⟩ : syracuseStep 2830625 = 2122969) B2122969
theorem B4772155 : Blo 1256446 4772155 := bstep (se 1 (by rfl) ⟨3579116, by rfl⟩ : syracuseStep 4772155 = 7158233) B7158233
theorem B1257787 : Blo 1256446 1257787 := bstep (se 1 (by rfl) ⟨943340, by rfl⟩ : syracuseStep 1257787 = 1886681) B1886681
theorem B3182935 : Blo 1256446 3182935 := bstep (se 1 (by rfl) ⟨2387201, by rfl⟩ : syracuseStep 3182935 = 4774403) B4774403
theorem B1257863 : Blo 1256446 1257863 := bstep (se 1 (by rfl) ⟨943397, by rfl⟩ : syracuseStep 1257863 = 1886795) B1886795
theorem B1257871 : Blo 1256446 1257871 := bstep (se 1 (by rfl) ⟨943403, by rfl⟩ : syracuseStep 1257871 = 1886807) B1886807
theorem B1257915 : Blo 1256446 1257915 := bstep (se 1 (by rfl) ⟨943436, by rfl⟩ : syracuseStep 1257915 = 1886873) B1886873
theorem B3494345 : Blo 1256446 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B15307217 : Blo 1256446 15307217 := bstep (se 2 (by rfl) ⟨5740206, by rfl⟩ : syracuseStep 15307217 = 11480413) B11480413
theorem B1257991 : Blo 1256446 1257991 := bstep (se 1 (by rfl) ⟨943493, by rfl⟩ : syracuseStep 1257991 = 1886987) B1886987
theorem B1257999 : Blo 1256446 1257999 := bstep (se 1 (by rfl) ⟨943499, by rfl⟩ : syracuseStep 1257999 = 1886999) B1886999
theorem B2388523 : Blo 1256446 2388523 := bstep (se 1 (by rfl) ⟨1791392, by rfl⟩ : syracuseStep 2388523 = 3582785) B3582785
theorem B1258043 : Blo 1256446 1258043 := bstep (se 1 (by rfl) ⟨943532, by rfl⟩ : syracuseStep 1258043 = 1887065) B1887065
theorem B2388599 : Blo 1256446 2388599 := bstep (se 1 (by rfl) ⟨1791449, by rfl⟩ : syracuseStep 2388599 = 3582899) B3582899
theorem B2830967 : Blo 1256446 2830967 := bstep (se 1 (by rfl) ⟨2123225, by rfl⟩ : syracuseStep 2830967 = 4246451) B4246451
theorem B3183239 : Blo 1256446 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B1258119 : Blo 1256446 1258119 := bstep (se 1 (by rfl) ⟨943589, by rfl⟩ : syracuseStep 1258119 = 1887179) B1887179
theorem B1258127 : Blo 1256446 1258127 := bstep (se 1 (by rfl) ⟨943595, by rfl⟩ : syracuseStep 1258127 = 1887191) B1887191
theorem B1258171 : Blo 1256446 1258171 := bstep (se 1 (by rfl) ⟨943628, by rfl⟩ : syracuseStep 1258171 = 1887257) B1887257
theorem B3822281 : Blo 1256446 3822281 := bstep (se 2 (by rfl) ⟨1433355, by rfl⟩ : syracuseStep 3822281 = 2866711) B2866711
theorem B8721125 : Blo 1256446 8721125 := bstep (se 4 (by rfl) ⟨817605, by rfl⟩ : syracuseStep 8721125 = 1635211) B1635211
theorem B6451969 : Blo 1256446 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B4535041 : Blo 1256446 4535041 := bstep (se 2 (by rfl) ⟨1700640, by rfl⟩ : syracuseStep 4535041 = 3401281) B3401281
theorem B1413895 : Blo 1256446 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B1258247 : Blo 1256446 1258247 := bstep (se 1 (by rfl) ⟨943685, by rfl⟩ : syracuseStep 1258247 = 1887371) B1887371
theorem B3183371 : Blo 1256446 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B30593807 : Blo 1256446 30593807 := bstep (se 1 (by rfl) ⟨22945355, by rfl⟩ : syracuseStep 30593807 = 45890711) B45890711
theorem B1258255 : Blo 1256446 1258255 := bstep (se 1 (by rfl) ⟨943691, by rfl⟩ : syracuseStep 1258255 = 1887383) B1887383
theorem B4772641 : Blo 1256446 4772641 := bstep (se 2 (by rfl) ⟨1789740, by rfl⟩ : syracuseStep 4772641 = 3579481) B3579481
theorem B2831147 : Blo 1256446 2831147 := bstep (se 1 (by rfl) ⟨2123360, by rfl⟩ : syracuseStep 2831147 = 4246721) B4246721
theorem B1258299 : Blo 1256446 1258299 := bstep (se 1 (by rfl) ⟨943724, by rfl⟩ : syracuseStep 1258299 = 1887449) B1887449
theorem B6370163 : Blo 1256446 6370163 := bstep (se 1 (by rfl) ⟨4777622, by rfl⟩ : syracuseStep 6370163 = 9555245) B9555245
theorem B2683783 : Blo 1256446 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B1258375 : Blo 1256446 1258375 := bstep (se 1 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 1258375 = 1887563) B1887563
theorem B1258383 : Blo 1256446 1258383 := bstep (se 1 (by rfl) ⟨943787, by rfl⟩ : syracuseStep 1258383 = 1887575) B1887575
theorem B1414075 : Blo 1256446 1414075 := bstep (se 1 (by rfl) ⟨1060556, by rfl⟩ : syracuseStep 1414075 = 2121113) B2121113
theorem B1258427 : Blo 1256446 1258427 := bstep (se 1 (by rfl) ⟨943820, by rfl⟩ : syracuseStep 1258427 = 1887641) B1887641
theorem B2266057 : Blo 1256446 2266057 := bstep (se 2 (by rfl) ⟨849771, by rfl⟩ : syracuseStep 2266057 = 1699543) B1699543
theorem B6124663 : Blo 1256446 6124663 := bstep (se 1 (by rfl) ⟨4593497, by rfl⟩ : syracuseStep 6124663 = 9186995) B9186995
theorem B1791119 : Blo 1256446 1791119 := bstep (se 1 (by rfl) ⟨1343339, by rfl⟩ : syracuseStep 1791119 = 2686679) B2686679
theorem B3396761 : Blo 1256446 3396761 := bstep (se 2 (by rfl) ⟨1273785, by rfl⟩ : syracuseStep 3396761 = 2547571) B2547571
theorem B14521589 : Blo 1256446 14521589 := bstep (se 5 (by rfl) ⟨680699, by rfl⟩ : syracuseStep 14521589 = 1361399) B1361399
theorem B1963271 : Blo 1256446 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B3183887 : Blo 1256446 3183887 := bstep (se 1 (by rfl) ⟨2387915, by rfl⟩ : syracuseStep 3183887 = 4775831) B4775831
theorem B4240673 : Blo 1256446 4240673 := bstep (se 2 (by rfl) ⟨1590252, by rfl⟩ : syracuseStep 4240673 = 3180505) B3180505
theorem B3446075 : Blo 1256446 3446075 := bstep (se 1 (by rfl) ⟨2584556, by rfl⟩ : syracuseStep 3446075 = 5169113) B5169113
theorem B6370649 : Blo 1256446 6370649 := bstep (se 2 (by rfl) ⟨2388993, by rfl⟩ : syracuseStep 6370649 = 4777987) B4777987
theorem B1414543 : Blo 1256446 1414543 := bstep (se 1 (by rfl) ⟨1060907, by rfl⟩ : syracuseStep 1414543 = 2121815) B2121815
theorem B3020179 : Blo 1256446 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B3184019 : Blo 1256446 3184019 := bstep (se 1 (by rfl) ⟨2388014, by rfl⟩ : syracuseStep 3184019 = 4776029) B4776029
theorem B11777501 : Blo 1256446 11777501 := bstep (se 3 (by rfl) ⟨2208281, by rfl⟩ : syracuseStep 11777501 = 4416563) B4416563
theorem B6362711 : Blo 1256446 6362711 := bstep (se 1 (by rfl) ⟨4772033, by rfl⟩ : syracuseStep 6362711 = 9544067) B9544067
theorem B4773613 : Blo 1256446 4773613 := bstep (se 3 (by rfl) ⟨895052, by rfl⟩ : syracuseStep 4773613 = 1790105) B1790105
theorem B18118475 : Blo 1256446 18118475 := bstep (se 1 (by rfl) ⟨13588856, by rfl⟩ : syracuseStep 18118475 = 27177713) B27177713
theorem B4241267 : Blo 1256446 4241267 := bstep (se 1 (by rfl) ⟨3180950, by rfl⟩ : syracuseStep 4241267 = 6361901) B6361901
theorem B1415047 : Blo 1256446 1415047 := bstep (se 1 (by rfl) ⟨1061285, by rfl⟩ : syracuseStep 1415047 = 2122571) B2122571
theorem B2013113 : Blo 1256446 2013113 := bstep (se 2 (by rfl) ⟨754917, by rfl⟩ : syracuseStep 2013113 = 1509835) B1509835
theorem B31004695 : Blo 1256446 31004695 := bstep (se 1 (by rfl) ⟨23253521, by rfl⟩ : syracuseStep 31004695 = 46507043) B46507043
theorem B4773917 : Blo 1256446 4773917 := bstep (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) B1790219
theorem B1415227 : Blo 1256446 1415227 := bstep (se 1 (by rfl) ⟨1061420, by rfl⟩ : syracuseStep 1415227 = 2122841) B2122841
theorem B6363197 : Blo 1256446 6363197 := bstep (se 3 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 6363197 = 2386199) B2386199
theorem B5371991 : Blo 1256446 5371991 := bstep (se 1 (by rfl) ⟨4028993, by rfl⟩ : syracuseStep 5371991 = 8057987) B8057987
theorem B4028687 : Blo 1256446 4028687 := bstep (se 1 (by rfl) ⟨3021515, by rfl⟩ : syracuseStep 4028687 = 6043031) B6043031
theorem B43538705 : Blo 1256446 43538705 := bstep (se 2 (by rfl) ⟨16327014, by rfl⟩ : syracuseStep 43538705 = 32654029) B32654029
theorem B3676535 : Blo 1256446 3676535 := bstep (se 1 (by rfl) ⟨2757401, by rfl⟩ : syracuseStep 3676535 = 5514803) B5514803
theorem B3185153 : Blo 1256446 3185153 := bstep (se 2 (by rfl) ⟨1194432, by rfl⟩ : syracuseStep 3185153 = 2388865) B2388865
theorem B10746371 : Blo 1256446 10746371 := bstep (se 1 (by rfl) ⟨8059778, by rfl⟩ : syracuseStep 10746371 = 16119557) B16119557
theorem B1415695 : Blo 1256446 1415695 := bstep (se 1 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 1415695 = 2123543) B2123543
theorem B3578411 : Blo 1256446 3578411 := bstep (se 1 (by rfl) ⟨2683808, by rfl⟩ : syracuseStep 3578411 = 5367617) B5367617
theorem B2120377 : Blo 1256446 2120377 := bstep (se 2 (by rfl) ⟨795141, by rfl⟩ : syracuseStep 2120377 = 1590283) B1590283
theorem B32275205 : Blo 1256446 32275205 := bstep (se 4 (by rfl) ⟨3025800, by rfl⟩ : syracuseStep 32275205 = 6051601) B6051601
theorem B2685739 : Blo 1256446 2685739 := bstep (se 1 (by rfl) ⟨2014304, by rfl⟩ : syracuseStep 2685739 = 4028609) B4028609
theorem B12409649 : Blo 1256446 12409649 := bstep (se 2 (by rfl) ⟨4653618, by rfl⟩ : syracuseStep 12409649 = 9307237) B9307237
theorem B3824471 : Blo 1256446 3824471 := bstep (se 1 (by rfl) ⟨2868353, by rfl⟩ : syracuseStep 3824471 = 5736707) B5736707
theorem B2014087 : Blo 1256446 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B9550871 : Blo 1256446 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B7257377 : Blo 1256446 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B2121079 : Blo 1256446 2121079 := bstep (se 1 (by rfl) ⟨1590809, by rfl⟩ : syracuseStep 2121079 = 3181619) B3181619
theorem B11632019 : Blo 1256446 11632019 := bstep (se 1 (by rfl) ⟨8724014, by rfl⟩ : syracuseStep 11632019 = 17448029) B17448029
theorem B238804421 : Blo 1256446 238804421 := bstep (se 4 (by rfl) ⟨22387914, by rfl⟩ : syracuseStep 238804421 = 44775829) B44775829
theorem B2121275 : Blo 1256446 2121275 := bstep (se 1 (by rfl) ⟨1590956, by rfl⟩ : syracuseStep 2121275 = 3181913) B3181913
theorem B4775543 : Blo 1256446 4775543 := bstep (se 1 (by rfl) ⟨3581657, by rfl⟩ : syracuseStep 4775543 = 7163315) B7163315
theorem B3579527 : Blo 1256446 3579527 := bstep (se 1 (by rfl) ⟨2684645, by rfl⟩ : syracuseStep 3579527 = 5369291) B5369291
theorem B4529935 : Blo 1256446 4529935 := bstep (se 1 (by rfl) ⟨3397451, by rfl⟩ : syracuseStep 4529935 = 6794903) B6794903
theorem B6364979 : Blo 1256446 6364979 := bstep (se 1 (by rfl) ⟨4773734, by rfl⟩ : syracuseStep 6364979 = 9547469) B9547469
theorem B3579709 : Blo 1256446 3579709 := bstep (se 3 (by rfl) ⟨671195, by rfl⟩ : syracuseStep 3579709 = 1342391) B1342391
theorem B3628919 : Blo 1256446 3628919 := bstep (se 1 (by rfl) ⟨2721689, by rfl⟩ : syracuseStep 3628919 = 5443379) B5443379
theorem B6045587 : Blo 1256446 6045587 := bstep (se 1 (by rfl) ⟨4534190, by rfl⟩ : syracuseStep 6045587 = 9068381) B9068381
theorem B2121673 : Blo 1256446 2121673 := bstep (se 2 (by rfl) ⟨795627, by rfl⟩ : syracuseStep 2121673 = 1591255) B1591255
theorem B3579983 : Blo 1256446 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B4243535 : Blo 1256446 4243535 := bstep (se 1 (by rfl) ⟨3182651, by rfl⟩ : syracuseStep 4243535 = 6365303) B6365303
theorem B2121977 : Blo 1256446 2121977 := bstep (se 2 (by rfl) ⟨795741, by rfl⟩ : syracuseStep 2121977 = 1591483) B1591483
theorem B4776317 : Blo 1256446 4776317 := bstep (se 3 (by rfl) ⟨895559, by rfl⟩ : syracuseStep 4776317 = 1791119) B1791119
theorem B2122159 : Blo 1256446 2122159 := bstep (se 1 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 2122159 = 3183239) B3183239
theorem B4243913 : Blo 1256446 4243913 := bstep (se 2 (by rfl) ⟨1591467, by rfl⟩ : syracuseStep 4243913 = 3182935) B3182935
theorem B2548187 : Blo 1256446 2548187 := bstep (se 1 (by rfl) ⟨1911140, by rfl⟩ : syracuseStep 2548187 = 3822281) B3822281
theorem B2122247 : Blo 1256446 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B4842193 : Blo 1256446 4842193 := bstep (se 2 (by rfl) ⟨1815822, by rfl⟩ : syracuseStep 4842193 = 3631645) B3631645
theorem B4244183 : Blo 1256446 4244183 := bstep (se 1 (by rfl) ⟨3183137, by rfl⟩ : syracuseStep 4244183 = 6366275) B6366275
theorem B2122591 : Blo 1256446 2122591 := bstep (se 1 (by rfl) ⟨1591943, by rfl⟩ : syracuseStep 2122591 = 3183887) B3183887
theorem B2827115 : Blo 1256446 2827115 := bstep (se 1 (by rfl) ⟨2120336, by rfl⟩ : syracuseStep 2827115 = 4240673) B4240673
theorem B2827169 : Blo 1256446 2827169 := bstep (se 2 (by rfl) ⟨1060188, by rfl⟩ : syracuseStep 2827169 = 2120377) B2120377
theorem B1885103 : Blo 1256446 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B4244399 : Blo 1256446 4244399 := bstep (se 1 (by rfl) ⟨3183299, by rfl⟩ : syracuseStep 4244399 = 6366599) B6366599
theorem B9552815 : Blo 1256446 9552815 := bstep (se 1 (by rfl) ⟨7164611, by rfl⟩ : syracuseStep 9552815 = 14329223) B14329223
theorem B2122679 : Blo 1256446 2122679 := bstep (se 1 (by rfl) ⟨1592009, by rfl⟩ : syracuseStep 2122679 = 3184019) B3184019
theorem B8602625 : Blo 1256446 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B6046721 : Blo 1256446 6046721 := bstep (se 2 (by rfl) ⟨2267520, by rfl⟩ : syracuseStep 6046721 = 4535041) B4535041
theorem B1885193 : Blo 1256446 1885193 := bstep (se 2 (by rfl) ⟨706947, by rfl⟩ : syracuseStep 1885193 = 1413895) B1413895
theorem B1885223 : Blo 1256446 1885223 := bstep (se 1 (by rfl) ⟨1413917, by rfl⟩ : syracuseStep 1885223 = 2827835) B2827835
theorem B3580985 : Blo 1256446 3580985 := bstep (se 2 (by rfl) ⟨1342869, by rfl⟩ : syracuseStep 3580985 = 2685739) B2685739
theorem B1885307 : Blo 1256446 1885307 := bstep (se 1 (by rfl) ⟨1413980, by rfl⟩ : syracuseStep 1885307 = 2827961) B2827961
theorem B2827511 : Blo 1256446 2827511 := bstep (se 1 (by rfl) ⟨2120633, by rfl⟩ : syracuseStep 2827511 = 4241267) B4241267
theorem B1885433 : Blo 1256446 1885433 := bstep (se 2 (by rfl) ⟨707037, by rfl⟩ : syracuseStep 1885433 = 1414075) B1414075
theorem B1885535 : Blo 1256446 1885535 := bstep (se 1 (by rfl) ⟨1414151, by rfl⟩ : syracuseStep 1885535 = 2828303) B2828303
theorem B1885547 : Blo 1256446 1885547 := bstep (se 1 (by rfl) ⟨1414160, by rfl⟩ : syracuseStep 1885547 = 2828321) B2828321
theorem B3581327 : Blo 1256446 3581327 := bstep (se 1 (by rfl) ⟨2685995, by rfl⟩ : syracuseStep 3581327 = 5371991) B5371991
theorem B10749347 : Blo 1256446 10749347 := bstep (se 1 (by rfl) ⟨8062010, by rfl⟩ : syracuseStep 10749347 = 16124021) B16124021
theorem B24159653 : Blo 1256446 24159653 := bstep (se 4 (by rfl) ⟨2264967, by rfl⟩ : syracuseStep 24159653 = 4529935) B4529935
theorem B7161331 : Blo 1256446 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B2123273 : Blo 1256446 2123273 := bstep (se 2 (by rfl) ⟨796227, by rfl⟩ : syracuseStep 2123273 = 1592455) B1592455
theorem B29025803 : Blo 1256446 29025803 := bstep (se 1 (by rfl) ⟨21769352, by rfl⟩ : syracuseStep 29025803 = 43538705) B43538705
theorem B2451023 : Blo 1256446 2451023 := bstep (se 1 (by rfl) ⟨1838267, by rfl⟩ : syracuseStep 2451023 = 3676535) B3676535
theorem B1885775 : Blo 1256446 1885775 := bstep (se 1 (by rfl) ⟨1414331, by rfl⟩ : syracuseStep 1885775 = 2828663) B2828663
theorem B2123435 : Blo 1256446 2123435 := bstep (se 1 (by rfl) ⟨1592576, by rfl⟩ : syracuseStep 2123435 = 3185153) B3185153
theorem B2385607 : Blo 1256446 2385607 := bstep (se 1 (by rfl) ⟨1789205, by rfl⟩ : syracuseStep 2385607 = 3578411) B3578411
theorem B1885895 : Blo 1256446 1885895 := bstep (se 1 (by rfl) ⟨1414421, by rfl⟩ : syracuseStep 1885895 = 2828843) B2828843
theorem B25790201 : Blo 1256446 25790201 := bstep (se 2 (by rfl) ⟨9671325, by rfl⟩ : syracuseStep 25790201 = 19342651) B19342651
theorem B2828105 : Blo 1256446 2828105 := bstep (se 2 (by rfl) ⟨1060539, by rfl⟩ : syracuseStep 2828105 = 2121079) B2121079
theorem B1886057 : Blo 1256446 1886057 := bstep (se 2 (by rfl) ⟨707271, by rfl⟩ : syracuseStep 1886057 = 1414543) B1414543
theorem B6367085 : Blo 1256446 6367085 := bstep (se 3 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 6367085 = 2387657) B2387657
theorem B2549647 : Blo 1256446 2549647 := bstep (se 1 (by rfl) ⟨1912235, by rfl⟩ : syracuseStep 2549647 = 3824471) B3824471
theorem B1886135 : Blo 1256446 1886135 := bstep (se 1 (by rfl) ⟨1414601, by rfl⟩ : syracuseStep 1886135 = 2829203) B2829203
theorem B1886171 : Blo 1256446 1886171 := bstep (se 1 (by rfl) ⟨1414628, by rfl⟩ : syracuseStep 1886171 = 2829257) B2829257
theorem B12077059 : Blo 1256446 12077059 := bstep (se 1 (by rfl) ⟨9057794, by rfl⟩ : syracuseStep 12077059 = 18115589) B18115589
theorem B6367247 : Blo 1256446 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B1509575 : Blo 1256446 1509575 := bstep (se 1 (by rfl) ⟨1132181, by rfl⟩ : syracuseStep 1509575 = 2264363) B2264363
theorem B2386169 : Blo 1256446 2386169 := bstep (se 2 (by rfl) ⟨894813, by rfl⟩ : syracuseStep 2386169 = 1789627) B1789627
theorem B12093745 : Blo 1256446 12093745 := bstep (se 2 (by rfl) ⟨4535154, by rfl⟩ : syracuseStep 12093745 = 9070309) B9070309
theorem B9677117 : Blo 1256446 9677117 := bstep (se 3 (by rfl) ⟨1814459, by rfl⟩ : syracuseStep 9677117 = 3628919) B3628919
theorem B2386351 : Blo 1256446 2386351 := bstep (se 1 (by rfl) ⟨1789763, by rfl⟩ : syracuseStep 2386351 = 3579527) B3579527
theorem B1886639 : Blo 1256446 1886639 := bstep (se 1 (by rfl) ⟨1414979, by rfl⟩ : syracuseStep 1886639 = 2829959) B2829959
theorem B5368301 : Blo 1256446 5368301 := bstep (se 3 (by rfl) ⟨1006556, by rfl⟩ : syracuseStep 5368301 = 2013113) B2013113
theorem B1886729 : Blo 1256446 1886729 := bstep (se 2 (by rfl) ⟨707523, by rfl⟩ : syracuseStep 1886729 = 1415047) B1415047
theorem B1886759 : Blo 1256446 1886759 := bstep (se 1 (by rfl) ⟨1415069, by rfl⟩ : syracuseStep 1886759 = 2830139) B2830139
theorem B3181153 : Blo 1256446 3181153 := bstep (se 2 (by rfl) ⟨1192932, by rfl⟩ : syracuseStep 3181153 = 2385865) B2385865
theorem B2828897 : Blo 1256446 2828897 := bstep (se 2 (by rfl) ⟨1060836, by rfl⟩ : syracuseStep 2828897 = 2121673) B2121673
theorem B1886843 : Blo 1256446 1886843 := bstep (se 1 (by rfl) ⟨1415132, by rfl⟩ : syracuseStep 1886843 = 2830265) B2830265
theorem B41339593 : Blo 1256446 41339593 := bstep (se 2 (by rfl) ⟨15502347, by rfl⟩ : syracuseStep 41339593 = 31004695) B31004695
theorem B1698553 : Blo 1256446 1698553 := bstep (se 2 (by rfl) ⟨636957, by rfl⟩ : syracuseStep 1698553 = 1273915) B1273915
theorem B1886969 : Blo 1256446 1886969 := bstep (se 2 (by rfl) ⟨707613, by rfl⟩ : syracuseStep 1886969 = 1415227) B1415227
theorem B1887071 : Blo 1256446 1887071 := bstep (se 1 (by rfl) ⟨1415303, by rfl⟩ : syracuseStep 1887071 = 2830607) B2830607
theorem B1887083 : Blo 1256446 1887083 := bstep (se 1 (by rfl) ⟨1415312, by rfl⟩ : syracuseStep 1887083 = 2830625) B2830625
theorem B4590445 : Blo 1256446 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B2829239 : Blo 1256446 2829239 := bstep (se 1 (by rfl) ⟨2121929, by rfl⟩ : syracuseStep 2829239 = 4243859) B4243859
theorem B1256487 : Blo 1256446 1256487 := bstep (se 1 (by rfl) ⟨942365, by rfl⟩ : syracuseStep 1256487 = 1884731) B1884731
theorem B1256527 : Blo 1256446 1256527 := bstep (se 1 (by rfl) ⟨942395, by rfl⟩ : syracuseStep 1256527 = 1884791) B1884791
theorem B1592399 : Blo 1256446 1592399 := bstep (se 1 (by rfl) ⟨1194299, by rfl⟩ : syracuseStep 1592399 = 2388599) B2388599
theorem B1887311 : Blo 1256446 1887311 := bstep (se 1 (by rfl) ⟨1415483, by rfl⟩ : syracuseStep 1887311 = 2830967) B2830967
theorem B1256543 : Blo 1256446 1256543 := bstep (se 1 (by rfl) ⟨942407, by rfl⟩ : syracuseStep 1256543 = 1884815) B1884815
theorem B1256571 : Blo 1256446 1256571 := bstep (se 1 (by rfl) ⟨942428, by rfl⟩ : syracuseStep 1256571 = 1884857) B1884857
theorem B1256623 : Blo 1256446 1256623 := bstep (se 1 (by rfl) ⟨942467, by rfl⟩ : syracuseStep 1256623 = 1884935) B1884935
theorem B1256647 : Blo 1256446 1256647 := bstep (se 1 (by rfl) ⟨942485, by rfl⟩ : syracuseStep 1256647 = 1884971) B1884971
theorem B1887431 : Blo 1256446 1887431 := bstep (se 1 (by rfl) ⟨1415573, by rfl⟩ : syracuseStep 1887431 = 2831147) B2831147
theorem B1256667 : Blo 1256446 1256667 := bstep (se 1 (by rfl) ⟨942500, by rfl⟩ : syracuseStep 1256667 = 1885001) B1885001
theorem B4246775 : Blo 1256446 4246775 := bstep (se 1 (by rfl) ⟨3185081, by rfl⟩ : syracuseStep 4246775 = 6370163) B6370163
theorem B1256743 : Blo 1256446 1256743 := bstep (se 1 (by rfl) ⟨942557, by rfl⟩ : syracuseStep 1256743 = 1885115) B1885115
theorem B1256783 : Blo 1256446 1256783 := bstep (se 1 (by rfl) ⟨942587, by rfl⟩ : syracuseStep 1256783 = 1885175) B1885175
theorem B1256799 : Blo 1256446 1256799 := bstep (se 1 (by rfl) ⟨942599, by rfl⟩ : syracuseStep 1256799 = 1885199) B1885199
theorem B1887593 : Blo 1256446 1887593 := bstep (se 2 (by rfl) ⟨707847, by rfl⟩ : syracuseStep 1887593 = 1415695) B1415695
theorem B1256827 : Blo 1256446 1256827 := bstep (se 1 (by rfl) ⟨942620, by rfl⟩ : syracuseStep 1256827 = 1885241) B1885241
theorem B8170895 : Blo 1256446 8170895 := bstep (se 1 (by rfl) ⟨6128171, by rfl⟩ : syracuseStep 8170895 = 12256343) B12256343
theorem B19353005 : Blo 1256446 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B6802861 : Blo 1256446 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B1256879 : Blo 1256446 1256879 := bstep (se 1 (by rfl) ⟨942659, by rfl⟩ : syracuseStep 1256879 = 1885319) B1885319
theorem B2264507 : Blo 1256446 2264507 := bstep (se 1 (by rfl) ⟨1698380, by rfl⟩ : syracuseStep 2264507 = 3396761) B3396761
theorem B1256903 : Blo 1256446 1256903 := bstep (se 1 (by rfl) ⟨942677, by rfl⟩ : syracuseStep 1256903 = 1885355) B1885355
theorem B8596955 : Blo 1256446 8596955 := bstep (se 1 (by rfl) ⟨6447716, by rfl⟩ : syracuseStep 8596955 = 12895433) B12895433
theorem B1256923 : Blo 1256446 1256923 := bstep (se 1 (by rfl) ⟨942692, by rfl⟩ : syracuseStep 1256923 = 1885385) B1885385
theorem B2829833 : Blo 1256446 2829833 := bstep (se 2 (by rfl) ⟨1061187, by rfl⟩ : syracuseStep 2829833 = 2122375) B2122375
theorem B3182105 : Blo 1256446 3182105 := bstep (se 2 (by rfl) ⟨1193289, by rfl⟩ : syracuseStep 3182105 = 2386579) B2386579
theorem B1256999 : Blo 1256446 1256999 := bstep (se 1 (by rfl) ⟨942749, by rfl⟩ : syracuseStep 1256999 = 1885499) B1885499
theorem B2297383 : Blo 1256446 2297383 := bstep (se 1 (by rfl) ⟨1723037, by rfl⟩ : syracuseStep 2297383 = 3446075) B3446075
theorem B4247099 : Blo 1256446 4247099 := bstep (se 1 (by rfl) ⟨3185324, by rfl⟩ : syracuseStep 4247099 = 6370649) B6370649
theorem B1257039 : Blo 1256446 1257039 := bstep (se 1 (by rfl) ⟨942779, by rfl⟩ : syracuseStep 1257039 = 1885559) B1885559
theorem B1257055 : Blo 1256446 1257055 := bstep (se 1 (by rfl) ⟨942791, by rfl⟩ : syracuseStep 1257055 = 1885583) B1885583
theorem B1257083 : Blo 1256446 1257083 := bstep (se 1 (by rfl) ⟨942812, by rfl⟩ : syracuseStep 1257083 = 1885625) B1885625
theorem B7851667 : Blo 1256446 7851667 := bstep (se 1 (by rfl) ⟨5888750, by rfl⟩ : syracuseStep 7851667 = 11777501) B11777501
theorem B6450835 : Blo 1256446 6450835 := bstep (se 1 (by rfl) ⟨4838126, by rfl⟩ : syracuseStep 6450835 = 9676253) B9676253
theorem B2387627 : Blo 1256446 2387627 := bstep (se 1 (by rfl) ⟨1790720, by rfl⟩ : syracuseStep 2387627 = 3581441) B3581441
theorem B1257135 : Blo 1256446 1257135 := bstep (se 1 (by rfl) ⟨942851, by rfl⟩ : syracuseStep 1257135 = 1885703) B1885703
theorem B1257159 : Blo 1256446 1257159 := bstep (se 1 (by rfl) ⟨942869, by rfl⟩ : syracuseStep 1257159 = 1885739) B1885739
theorem B1257179 : Blo 1256446 1257179 := bstep (se 1 (by rfl) ⟨942884, by rfl⟩ : syracuseStep 1257179 = 1885769) B1885769
theorem B31018717 : Blo 1256446 31018717 := bstep (se 3 (by rfl) ⟨5816009, by rfl⟩ : syracuseStep 31018717 = 11632019) B11632019
theorem B1257255 : Blo 1256446 1257255 := bstep (se 1 (by rfl) ⟨942941, by rfl⟩ : syracuseStep 1257255 = 1885883) B1885883
theorem B1257295 : Blo 1256446 1257295 := bstep (se 1 (by rfl) ⟨942971, by rfl⟩ : syracuseStep 1257295 = 1885943) B1885943
theorem B1257311 : Blo 1256446 1257311 := bstep (se 1 (by rfl) ⟨942983, by rfl⟩ : syracuseStep 1257311 = 1885967) B1885967
theorem B2830175 : Blo 1256446 2830175 := bstep (se 1 (by rfl) ⟨2122631, by rfl⟩ : syracuseStep 2830175 = 4245263) B4245263
theorem B9318253 : Blo 1256446 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B1257339 : Blo 1256446 1257339 := bstep (se 1 (by rfl) ⟨943004, by rfl⟩ : syracuseStep 1257339 = 1886009) B1886009
theorem B12078983 : Blo 1256446 12078983 := bstep (se 1 (by rfl) ⟨9059237, by rfl⟩ : syracuseStep 12078983 = 18118475) B18118475
theorem B2387855 : Blo 1256446 2387855 := bstep (se 1 (by rfl) ⟨1790891, by rfl⟩ : syracuseStep 2387855 = 3581783) B3581783
theorem B1257391 : Blo 1256446 1257391 := bstep (se 1 (by rfl) ⟨943043, by rfl⟩ : syracuseStep 1257391 = 1886087) B1886087
theorem B1257415 : Blo 1256446 1257415 := bstep (se 1 (by rfl) ⟨943061, by rfl⟩ : syracuseStep 1257415 = 1886123) B1886123
theorem B1257435 : Blo 1256446 1257435 := bstep (se 1 (by rfl) ⟨943076, by rfl⟩ : syracuseStep 1257435 = 1886153) B1886153
theorem B3182611 : Blo 1256446 3182611 := bstep (se 1 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 3182611 = 4773917) B4773917
theorem B2830355 : Blo 1256446 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B1257511 : Blo 1256446 1257511 := bstep (se 1 (by rfl) ⟨943133, by rfl⟩ : syracuseStep 1257511 = 1886267) B1886267
theorem B1257551 : Blo 1256446 1257551 := bstep (se 1 (by rfl) ⟨943163, by rfl⟩ : syracuseStep 1257551 = 1886327) B1886327
theorem B1257567 : Blo 1256446 1257567 := bstep (se 1 (by rfl) ⟨943175, by rfl⟩ : syracuseStep 1257567 = 1886351) B1886351
theorem B1257595 : Blo 1256446 1257595 := bstep (se 1 (by rfl) ⟨943196, by rfl⟩ : syracuseStep 1257595 = 1886393) B1886393
theorem B1257647 : Blo 1256446 1257647 := bstep (se 1 (by rfl) ⟨943235, by rfl⟩ : syracuseStep 1257647 = 1886471) B1886471
theorem B31027379 : Blo 1256446 31027379 := bstep (se 1 (by rfl) ⟨23270534, by rfl⟩ : syracuseStep 31027379 = 46541069) B46541069
theorem B1257671 : Blo 1256446 1257671 := bstep (se 1 (by rfl) ⟨943253, by rfl⟩ : syracuseStep 1257671 = 1886507) B1886507
theorem B1257691 : Blo 1256446 1257691 := bstep (se 1 (by rfl) ⟨943268, by rfl⟩ : syracuseStep 1257691 = 1886537) B1886537
theorem B1257767 : Blo 1256446 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B1257807 : Blo 1256446 1257807 := bstep (se 1 (by rfl) ⟨943355, by rfl⟩ : syracuseStep 1257807 = 1886711) B1886711
theorem B7164247 : Blo 1256446 7164247 := bstep (se 1 (by rfl) ⟨5373185, by rfl⟩ : syracuseStep 7164247 = 10746371) B10746371
theorem B1257823 : Blo 1256446 1257823 := bstep (se 1 (by rfl) ⟨943367, by rfl⟩ : syracuseStep 1257823 = 1886735) B1886735
theorem B2830697 : Blo 1256446 2830697 := bstep (se 2 (by rfl) ⟨1061511, by rfl⟩ : syracuseStep 2830697 = 2123023) B2123023
theorem B1257851 : Blo 1256446 1257851 := bstep (se 1 (by rfl) ⟨943388, by rfl⟩ : syracuseStep 1257851 = 1886777) B1886777
theorem B1257903 : Blo 1256446 1257903 := bstep (se 1 (by rfl) ⟨943427, by rfl⟩ : syracuseStep 1257903 = 1886855) B1886855
theorem B1257927 : Blo 1256446 1257927 := bstep (se 1 (by rfl) ⟨943445, by rfl⟩ : syracuseStep 1257927 = 1886891) B1886891
theorem B1257947 : Blo 1256446 1257947 := bstep (se 1 (by rfl) ⟨943460, by rfl⟩ : syracuseStep 1257947 = 1886921) B1886921
theorem B21516803 : Blo 1256446 21516803 := bstep (se 1 (by rfl) ⟨16137602, by rfl⟩ : syracuseStep 21516803 = 32275205) B32275205
theorem B4026905 : Blo 1256446 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B1258023 : Blo 1256446 1258023 := bstep (se 1 (by rfl) ⟨943517, by rfl⟩ : syracuseStep 1258023 = 1887035) B1887035
theorem B1258063 : Blo 1256446 1258063 := bstep (se 1 (by rfl) ⟨943547, by rfl⟩ : syracuseStep 1258063 = 1887095) B1887095
theorem B1258079 : Blo 1256446 1258079 := bstep (se 1 (by rfl) ⟨943559, by rfl⟩ : syracuseStep 1258079 = 1887119) B1887119
theorem B1258107 : Blo 1256446 1258107 := bstep (se 1 (by rfl) ⟨943580, by rfl⟩ : syracuseStep 1258107 = 1887161) B1887161
theorem B1258159 : Blo 1256446 1258159 := bstep (se 1 (by rfl) ⟨943619, by rfl⟩ : syracuseStep 1258159 = 1887239) B1887239
theorem B1258183 : Blo 1256446 1258183 := bstep (se 1 (by rfl) ⟨943637, by rfl⟩ : syracuseStep 1258183 = 1887275) B1887275
theorem B6370001 : Blo 1256446 6370001 := bstep (se 2 (by rfl) ⟨2388750, by rfl⟩ : syracuseStep 6370001 = 4777501) B4777501
theorem B1258203 : Blo 1256446 1258203 := bstep (se 1 (by rfl) ⟨943652, by rfl⟩ : syracuseStep 1258203 = 1887305) B1887305
theorem B1258279 : Blo 1256446 1258279 := bstep (se 1 (by rfl) ⟨943709, by rfl⟩ : syracuseStep 1258279 = 1887419) B1887419
theorem B1258319 : Blo 1256446 1258319 := bstep (se 1 (by rfl) ⟨943739, by rfl⟩ : syracuseStep 1258319 = 1887479) B1887479
theorem B1258335 : Blo 1256446 1258335 := bstep (se 1 (by rfl) ⟨943751, by rfl⟩ : syracuseStep 1258335 = 1887503) B1887503
theorem B1258363 : Blo 1256446 1258363 := bstep (se 1 (by rfl) ⟨943772, by rfl⟩ : syracuseStep 1258363 = 1887545) B1887545
theorem B1258415 : Blo 1256446 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B2831291 : Blo 1256446 2831291 := bstep (se 1 (by rfl) ⟨2123468, by rfl⟩ : syracuseStep 2831291 = 4246937) B4246937
theorem B1258439 : Blo 1256446 1258439 := bstep (se 1 (by rfl) ⟨943829, by rfl⟩ : syracuseStep 1258439 = 1887659) B1887659
theorem B1414183 : Blo 1256446 1414183 := bstep (se 1 (by rfl) ⟨1060637, by rfl⟩ : syracuseStep 1414183 = 2121275) B2121275
theorem B2831417 : Blo 1256446 2831417 := bstep (se 2 (by rfl) ⟨1061781, by rfl⟩ : syracuseStep 2831417 = 2123563) B2123563
theorem B3183695 : Blo 1256446 3183695 := bstep (se 1 (by rfl) ⟨2387771, by rfl⟩ : syracuseStep 3183695 = 4775543) B4775543
theorem B4772945 : Blo 1256446 4772945 := bstep (se 2 (by rfl) ⟨1789854, by rfl⟩ : syracuseStep 4772945 = 3579709) B3579709
theorem B12088439 : Blo 1256446 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B40793291 : Blo 1256446 40793291 := bstep (se 1 (by rfl) ⟨30594968, by rfl⟩ : syracuseStep 40793291 = 61189937) B61189937
theorem B4240727 : Blo 1256446 4240727 := bstep (se 1 (by rfl) ⟨3180545, by rfl⟩ : syracuseStep 4240727 = 6361091) B6361091
theorem B2266555 : Blo 1256446 2266555 := bstep (se 1 (by rfl) ⟨1699916, by rfl⟩ : syracuseStep 2266555 = 3399833) B3399833
theorem B4773401 : Blo 1256446 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B10204811 : Blo 1256446 10204811 := bstep (se 1 (by rfl) ⟨7653608, by rfl⟩ : syracuseStep 10204811 = 15307217) B15307217
theorem B12408535 : Blo 1256446 12408535 := bstep (se 1 (by rfl) ⟨9306401, by rfl⟩ : syracuseStep 12408535 = 18612803) B18612803
theorem B3184343 : Blo 1256446 3184343 := bstep (se 1 (by rfl) ⟨2388257, by rfl⟩ : syracuseStep 3184343 = 4776515) B4776515
theorem B2266871 : Blo 1256446 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B2012921 : Blo 1256446 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B6362873 : Blo 1256446 6362873 := bstep (se 2 (by rfl) ⟨2386077, by rfl⟩ : syracuseStep 6362873 = 4772155) B4772155
theorem B5814083 : Blo 1256446 5814083 := bstep (se 1 (by rfl) ⟨4360562, by rfl⟩ : syracuseStep 5814083 = 8721125) B8721125
theorem B20395871 : Blo 1256446 20395871 := bstep (se 1 (by rfl) ⟨15296903, by rfl⟩ : syracuseStep 20395871 = 30593807) B30593807
theorem B2266987 : Blo 1256446 2266987 := bstep (se 1 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 2266987 = 3400481) B3400481
theorem B15292423 : Blo 1256446 15292423 := bstep (se 1 (by rfl) ⟨11469317, by rfl⟩ : syracuseStep 15292423 = 22938635) B22938635
theorem B3184697 : Blo 1256446 3184697 := bstep (se 2 (by rfl) ⟨1194261, by rfl⟩ : syracuseStep 3184697 = 2388523) B2388523
theorem B18135197 : Blo 1256446 18135197 := bstep (se 3 (by rfl) ⟨3400349, by rfl⟩ : syracuseStep 18135197 = 6800699) B6800699
theorem B9681059 : Blo 1256446 9681059 := bstep (se 1 (by rfl) ⟨7260794, by rfl⟩ : syracuseStep 9681059 = 14521589) B14521589
theorem B1308847 : Blo 1256446 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B2267347 : Blo 1256446 2267347 := bstep (se 1 (by rfl) ⟨1700510, by rfl⟩ : syracuseStep 2267347 = 3401021) B3401021
theorem B17217773 : Blo 1256446 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B6363521 : Blo 1256446 6363521 := bstep (se 2 (by rfl) ⟨2386320, by rfl⟩ : syracuseStep 6363521 = 4772641) B4772641
theorem B4241807 : Blo 1256446 4241807 := bstep (se 1 (by rfl) ⟨3181355, by rfl⟩ : syracuseStep 4241807 = 6362711) B6362711
theorem B3578377 : Blo 1256446 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B2685449 : Blo 1256446 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B636811789 : Blo 1256446 636811789 := bstep (se 3 (by rfl) ⟨119402210, by rfl⟩ : syracuseStep 636811789 = 238804421) B238804421
theorem B3824167 : Blo 1256446 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B8608315 : Blo 1256446 8608315 := bstep (se 1 (by rfl) ⟨6456236, by rfl⟩ : syracuseStep 8608315 = 12912473) B12912473
theorem B3021409 : Blo 1256446 3021409 := bstep (se 2 (by rfl) ⟨1133028, by rfl⟩ : syracuseStep 3021409 = 2266057) B2266057
theorem B4774585 : Blo 1256446 4774585 := bstep (se 2 (by rfl) ⟨1790469, by rfl⟩ : syracuseStep 4774585 = 3580939) B3580939
theorem B4242131 : Blo 1256446 4242131 := bstep (se 1 (by rfl) ⟨3181598, by rfl⟩ : syracuseStep 4242131 = 6363197) B6363197
theorem B3398393 : Blo 1256446 3398393 := bstep (se 2 (by rfl) ⟨1274397, by rfl⟩ : syracuseStep 3398393 = 2548795) B2548795
theorem B8166217 : Blo 1256446 8166217 := bstep (se 2 (by rfl) ⟨3062331, by rfl⟩ : syracuseStep 8166217 = 6124663) B6124663
theorem B2685791 : Blo 1256446 2685791 := bstep (se 1 (by rfl) ⟨2014343, by rfl⟩ : syracuseStep 2685791 = 4028687) B4028687
theorem B4529159 : Blo 1256446 4529159 := bstep (se 1 (by rfl) ⟨3396869, by rfl⟩ : syracuseStep 4529159 = 6793739) B6793739
theorem B6364331 : Blo 1256446 6364331 := bstep (se 1 (by rfl) ⟨4773248, by rfl⟩ : syracuseStep 6364331 = 9546497) B9546497
theorem B8273099 : Blo 1256446 8273099 := bstep (se 1 (by rfl) ⟨6204824, by rfl⟩ : syracuseStep 8273099 = 12409649) B12409649
theorem B2120951 : Blo 1256446 2120951 := bstep (se 1 (by rfl) ⟨1590713, by rfl⟩ : syracuseStep 2120951 = 3181427) B3181427
theorem B8052169 : Blo 1256446 8052169 := bstep (se 2 (by rfl) ⟨3019563, by rfl⟩ : syracuseStep 8052169 = 6039127) B6039127
theorem B2121295 : Blo 1256446 2121295 := bstep (se 1 (by rfl) ⟨1590971, by rfl⟩ : syracuseStep 2121295 = 3181943) B3181943
theorem B6364817 : Blo 1256446 6364817 := bstep (se 2 (by rfl) ⟨2386806, by rfl⟩ : syracuseStep 6364817 = 4773613) B4773613
theorem B2121545 : Blo 1256446 2121545 := bstep (se 2 (by rfl) ⟨795579, by rfl⟩ : syracuseStep 2121545 = 1591159) B1591159
theorem B3022687 : Blo 1256446 3022687 := bstep (se 1 (by rfl) ⟨2267015, by rfl⟩ : syracuseStep 3022687 = 4534031) B4534031
theorem B4243319 : Blo 1256446 4243319 := bstep (se 1 (by rfl) ⟨3182489, by rfl⟩ : syracuseStep 4243319 = 6364979) B6364979
theorem B4030391 : Blo 1256446 4030391 := bstep (se 1 (by rfl) ⟨3022793, by rfl⟩ : syracuseStep 4030391 = 6045587) B6045587
theorem B3579835 : Blo 1256446 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B20389897 : Blo 1256446 20389897 := bstep (se 2 (by rfl) ⟨7646211, by rfl⟩ : syracuseStep 20389897 = 15292423) B15292423
theorem B4243481 : Blo 1256446 4243481 := bstep (se 2 (by rfl) ⟨1591305, by rfl⟩ : syracuseStep 4243481 = 3182611) B3182611
theorem B1745129 : Blo 1256446 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B3023129 : Blo 1256446 3023129 := bstep (se 2 (by rfl) ⟨1133673, by rfl⟩ : syracuseStep 3023129 = 2267347) B2267347
theorem B14344535 : Blo 1256446 14344535 := bstep (se 1 (by rfl) ⟨10758401, by rfl⟩ : syracuseStep 14344535 = 21516803) B21516803
theorem B9552329 : Blo 1256446 9552329 := bstep (se 2 (by rfl) ⟨3582123, by rfl⟩ : syracuseStep 9552329 = 7164247) B7164247
theorem B82739677 : Blo 1256446 82739677 := bstep (se 3 (by rfl) ⟨15513689, by rfl⟩ : syracuseStep 82739677 = 31027379) B31027379
theorem B1884743 : Blo 1256446 1884743 := bstep (se 1 (by rfl) ⟨1413557, by rfl⟩ : syracuseStep 1884743 = 2827115) B2827115
theorem B1884779 : Blo 1256446 1884779 := bstep (se 1 (by rfl) ⟨1413584, by rfl⟩ : syracuseStep 1884779 = 2827169) B2827169
theorem B4031147 : Blo 1256446 4031147 := bstep (se 1 (by rfl) ⟨3023360, by rfl⟩ : syracuseStep 4031147 = 6046721) B6046721
theorem B2122463 : Blo 1256446 2122463 := bstep (se 1 (by rfl) ⟨1591847, by rfl⟩ : syracuseStep 2122463 = 3183695) B3183695
theorem B11477753 : Blo 1256446 11477753 := bstep (se 2 (by rfl) ⟨4304157, by rfl⟩ : syracuseStep 11477753 = 8608315) B8608315
theorem B1885007 : Blo 1256446 1885007 := bstep (se 1 (by rfl) ⟨1413755, by rfl⟩ : syracuseStep 1885007 = 2827511) B2827511
theorem B2827151 : Blo 1256446 2827151 := bstep (se 1 (by rfl) ⟨2120363, by rfl⟩ : syracuseStep 2827151 = 4240727) B4240727
theorem B6366113 : Blo 1256446 6366113 := bstep (se 2 (by rfl) ⟨2387292, by rfl⟩ : syracuseStep 6366113 = 4774585) B4774585
theorem B6456257 : Blo 1256446 6456257 := bstep (se 2 (by rfl) ⟨2421096, by rfl⟩ : syracuseStep 6456257 = 4842193) B4842193
theorem B16106435 : Blo 1256446 16106435 := bstep (se 1 (by rfl) ⟨12079826, by rfl⟩ : syracuseStep 16106435 = 24159653) B24159653
theorem B19350535 : Blo 1256446 19350535 := bstep (se 1 (by rfl) ⟨14512901, by rfl⟩ : syracuseStep 19350535 = 29025803) B29025803
theorem B10888289 : Blo 1256446 10888289 := bstep (se 2 (by rfl) ⟨4083108, by rfl⟩ : syracuseStep 10888289 = 8166217) B8166217
theorem B2122895 : Blo 1256446 2122895 := bstep (se 1 (by rfl) ⟨1592171, by rfl⟩ : syracuseStep 2122895 = 3184343) B3184343
theorem B6120593 : Blo 1256446 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B3876055 : Blo 1256446 3876055 := bstep (se 1 (by rfl) ⟨2907041, by rfl⟩ : syracuseStep 3876055 = 5814083) B5814083
theorem B1885403 : Blo 1256446 1885403 := bstep (se 1 (by rfl) ⟨1414052, by rfl⟩ : syracuseStep 1885403 = 2828105) B2828105
theorem B4244723 : Blo 1256446 4244723 := bstep (se 1 (by rfl) ⟨3183542, by rfl⟩ : syracuseStep 4244723 = 6367085) B6367085
theorem B4244831 : Blo 1256446 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B2123131 : Blo 1256446 2123131 := bstep (se 1 (by rfl) ⟨1592348, by rfl⟩ : syracuseStep 2123131 = 3184697) B3184697
theorem B1885577 : Blo 1256446 1885577 := bstep (se 2 (by rfl) ⟨707091, by rfl⟩ : syracuseStep 1885577 = 1414183) B1414183
theorem B11478515 : Blo 1256446 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B1590779 : Blo 1256446 1590779 := bstep (se 1 (by rfl) ⟨1193084, by rfl⟩ : syracuseStep 1590779 = 2386169) B2386169
theorem B2827871 : Blo 1256446 2827871 := bstep (se 1 (by rfl) ⟨2120903, by rfl⟩ : syracuseStep 2827871 = 4241807) B4241807
theorem B1885931 : Blo 1256446 1885931 := bstep (se 1 (by rfl) ⟨1414448, by rfl⟩ : syracuseStep 1885931 = 2828897) B2828897
theorem B2828087 : Blo 1256446 2828087 := bstep (se 1 (by rfl) ⟨2121065, by rfl⟩ : syracuseStep 2828087 = 4242131) B4242131
theorem B9070481 : Blo 1256446 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B1886159 : Blo 1256446 1886159 := bstep (se 1 (by rfl) ⟨1414619, by rfl⟩ : syracuseStep 1886159 = 2829239) B2829239
theorem B9062381 : Blo 1256446 9062381 := bstep (se 3 (by rfl) ⟨1699196, by rfl⟩ : syracuseStep 9062381 = 3398393) B3398393
theorem B2828393 : Blo 1256446 2828393 := bstep (se 2 (by rfl) ⟨1060647, by rfl⟩ : syracuseStep 2828393 = 2121295) B2121295
theorem B5515399 : Blo 1256446 5515399 := bstep (se 1 (by rfl) ⟨4136549, by rfl⟩ : syracuseStep 5515399 = 8273099) B8273099
theorem B3180809 : Blo 1256446 3180809 := bstep (se 2 (by rfl) ⟨1192803, by rfl⟩ : syracuseStep 3180809 = 2385607) B2385607
theorem B1509671 : Blo 1256446 1509671 := bstep (se 1 (by rfl) ⟨1132253, by rfl⟩ : syracuseStep 1509671 = 2264507) B2264507
theorem B1886555 : Blo 1256446 1886555 := bstep (se 1 (by rfl) ⟨1414916, by rfl⟩ : syracuseStep 1886555 = 2829833) B2829833
theorem B1591751 : Blo 1256446 1591751 := bstep (se 1 (by rfl) ⟨1193813, by rfl⟩ : syracuseStep 1591751 = 2387627) B2387627
theorem B1886783 : Blo 1256446 1886783 := bstep (se 1 (by rfl) ⟨1415087, by rfl⟩ : syracuseStep 1886783 = 2830175) B2830175
theorem B2828879 : Blo 1256446 2828879 := bstep (se 1 (by rfl) ⟨2121659, by rfl⟩ : syracuseStep 2828879 = 4243319) B4243319
theorem B1591903 : Blo 1256446 1591903 := bstep (se 1 (by rfl) ⟨1193927, by rfl⟩ : syracuseStep 1591903 = 2387855) B2387855
theorem B22940333 : Blo 1256446 22940333 := bstep (se 3 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 22940333 = 8602625) B8602625
theorem B1886903 : Blo 1256446 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B2386655 : Blo 1256446 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B2829023 : Blo 1256446 2829023 := bstep (se 1 (by rfl) ⟨2121767, by rfl⟩ : syracuseStep 2829023 = 4243535) B4243535
theorem B4246397 : Blo 1256446 4246397 := bstep (se 3 (by rfl) ⟨796199, by rfl⟩ : syracuseStep 4246397 = 1592399) B1592399
theorem B1887131 : Blo 1256446 1887131 := bstep (se 1 (by rfl) ⟨1415348, by rfl⟩ : syracuseStep 1887131 = 2830697) B2830697
theorem B2829275 : Blo 1256446 2829275 := bstep (se 1 (by rfl) ⟨2121956, by rfl⟩ : syracuseStep 2829275 = 4243913) B4243913
theorem B1698791 : Blo 1256446 1698791 := bstep (se 1 (by rfl) ⟨1274093, by rfl⟩ : syracuseStep 1698791 = 2548187) B2548187
theorem B16124993 : Blo 1256446 16124993 := bstep (se 2 (by rfl) ⟨6046872, by rfl⟩ : syracuseStep 16124993 = 12093745) B12093745
theorem B4246667 : Blo 1256446 4246667 := bstep (se 1 (by rfl) ⟨3185000, by rfl⟩ : syracuseStep 4246667 = 6370001) B6370001
theorem B2829455 : Blo 1256446 2829455 := bstep (se 1 (by rfl) ⟨2122091, by rfl⟩ : syracuseStep 2829455 = 4244183) B4244183
theorem B4025533 : Blo 1256446 4025533 := bstep (se 3 (by rfl) ⟨754787, by rfl⟩ : syracuseStep 4025533 = 1509575) B1509575
theorem B3181801 : Blo 1256446 3181801 := bstep (se 2 (by rfl) ⟨1193175, by rfl⟩ : syracuseStep 3181801 = 2386351) B2386351
theorem B2829545 : Blo 1256446 2829545 := bstep (se 2 (by rfl) ⟨1061079, by rfl⟩ : syracuseStep 2829545 = 2122159) B2122159
theorem B1256735 : Blo 1256446 1256735 := bstep (se 1 (by rfl) ⟨942551, by rfl⟩ : syracuseStep 1256735 = 1885103) B1885103
theorem B2829599 : Blo 1256446 2829599 := bstep (se 1 (by rfl) ⟨2122199, by rfl⟩ : syracuseStep 2829599 = 4244399) B4244399
theorem B6368543 : Blo 1256446 6368543 := bstep (se 1 (by rfl) ⟨4776407, by rfl⟩ : syracuseStep 6368543 = 9552815) B9552815
theorem B1887527 : Blo 1256446 1887527 := bstep (se 1 (by rfl) ⟨1415645, by rfl⟩ : syracuseStep 1887527 = 2831291) B2831291
theorem B1256795 : Blo 1256446 1256795 := bstep (se 1 (by rfl) ⟨942596, by rfl⟩ : syracuseStep 1256795 = 1885193) B1885193
theorem B4771169 : Blo 1256446 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B1256815 : Blo 1256446 1256815 := bstep (se 1 (by rfl) ⟨942611, by rfl⟩ : syracuseStep 1256815 = 1885223) B1885223
theorem B2387323 : Blo 1256446 2387323 := bstep (se 1 (by rfl) ⟨1790492, by rfl⟩ : syracuseStep 2387323 = 3580985) B3580985
theorem B1887611 : Blo 1256446 1887611 := bstep (se 1 (by rfl) ⟨1415708, by rfl⟩ : syracuseStep 1887611 = 2831417) B2831417
theorem B5098889 : Blo 1256446 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B3181963 : Blo 1256446 3181963 := bstep (se 1 (by rfl) ⟨2386472, by rfl⟩ : syracuseStep 3181963 = 4772945) B4772945
theorem B1256871 : Blo 1256446 1256871 := bstep (se 1 (by rfl) ⟨942653, by rfl⟩ : syracuseStep 1256871 = 1885307) B1885307
theorem B1256955 : Blo 1256446 1256955 := bstep (se 1 (by rfl) ⟨942716, by rfl⟩ : syracuseStep 1256955 = 1885433) B1885433
theorem B1257023 : Blo 1256446 1257023 := bstep (se 1 (by rfl) ⟨942767, by rfl⟩ : syracuseStep 1257023 = 1885535) B1885535
theorem B1257031 : Blo 1256446 1257031 := bstep (se 1 (by rfl) ⟨942773, by rfl⟩ : syracuseStep 1257031 = 1885547) B1885547
theorem B2387551 : Blo 1256446 2387551 := bstep (se 1 (by rfl) ⟨1790663, by rfl⟩ : syracuseStep 2387551 = 3581327) B3581327
theorem B55119457 : Blo 1256446 55119457 := bstep (se 2 (by rfl) ⟨20669796, by rfl⟩ : syracuseStep 55119457 = 41339593) B41339593
theorem B3182267 : Blo 1256446 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B1634015 : Blo 1256446 1634015 := bstep (se 1 (by rfl) ⟨1225511, by rfl⟩ : syracuseStep 1634015 = 2451023) B2451023
theorem B1257183 : Blo 1256446 1257183 := bstep (se 1 (by rfl) ⟨942887, by rfl⟩ : syracuseStep 1257183 = 1885775) B1885775
theorem B6803207 : Blo 1256446 6803207 := bstep (se 1 (by rfl) ⟨5102405, by rfl⟩ : syracuseStep 6803207 = 10204811) B10204811
theorem B66178853 : Blo 1256446 66178853 := bstep (se 4 (by rfl) ⟨6204267, by rfl⟩ : syracuseStep 66178853 = 12408535) B12408535
theorem B2830121 : Blo 1256446 2830121 := bstep (se 2 (by rfl) ⟨1061295, by rfl⟩ : syracuseStep 2830121 = 2122591) B2122591
theorem B1257263 : Blo 1256446 1257263 := bstep (se 1 (by rfl) ⟨942947, by rfl⟩ : syracuseStep 1257263 = 1885895) B1885895
theorem B1257371 : Blo 1256446 1257371 := bstep (se 1 (by rfl) ⟨943028, by rfl⟩ : syracuseStep 1257371 = 1886057) B1886057
theorem B22925213 : Blo 1256446 22925213 := bstep (se 3 (by rfl) ⟨4298477, by rfl⟩ : syracuseStep 22925213 = 8596955) B8596955
theorem B1257423 : Blo 1256446 1257423 := bstep (se 1 (by rfl) ⟨943067, by rfl⟩ : syracuseStep 1257423 = 1886135) B1886135
theorem B1257447 : Blo 1256446 1257447 := bstep (se 1 (by rfl) ⟨943085, by rfl⟩ : syracuseStep 1257447 = 1886171) B1886171
theorem B6451411 : Blo 1256446 6451411 := bstep (se 1 (by rfl) ⟨4838558, by rfl⟩ : syracuseStep 6451411 = 9677117) B9677117
theorem B1257759 : Blo 1256446 1257759 := bstep (se 1 (by rfl) ⟨943319, by rfl⟩ : syracuseStep 1257759 = 1886639) B1886639
theorem B1790299 : Blo 1256446 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B1257819 : Blo 1256446 1257819 := bstep (se 1 (by rfl) ⟨943364, by rfl⟩ : syracuseStep 1257819 = 1886729) B1886729
theorem B1257839 : Blo 1256446 1257839 := bstep (se 1 (by rfl) ⟨943379, by rfl⟩ : syracuseStep 1257839 = 1886759) B1886759
theorem B1257895 : Blo 1256446 1257895 := bstep (se 1 (by rfl) ⟨943421, by rfl⟩ : syracuseStep 1257895 = 1886843) B1886843
theorem B1257979 : Blo 1256446 1257979 := bstep (se 1 (by rfl) ⟨943484, by rfl⟩ : syracuseStep 1257979 = 1886969) B1886969
theorem B1790527 : Blo 1256446 1790527 := bstep (se 1 (by rfl) ⟨1342895, by rfl⟩ : syracuseStep 1790527 = 2685791) B2685791
theorem B1258047 : Blo 1256446 1258047 := bstep (se 1 (by rfl) ⟨943535, by rfl⟩ : syracuseStep 1258047 = 1887071) B1887071
theorem B1258055 : Blo 1256446 1258055 := bstep (se 1 (by rfl) ⟨943541, by rfl⟩ : syracuseStep 1258055 = 1887083) B1887083
theorem B10736225 : Blo 1256446 10736225 := bstep (se 2 (by rfl) ⟨4026084, by rfl⟩ : syracuseStep 10736225 = 8052169) B8052169
theorem B9548441 : Blo 1256446 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B3019439 : Blo 1256446 3019439 := bstep (se 1 (by rfl) ⟨2264579, by rfl⟩ : syracuseStep 3019439 = 4529159) B4529159
theorem B1258207 : Blo 1256446 1258207 := bstep (se 1 (by rfl) ⟨943655, by rfl⟩ : syracuseStep 1258207 = 1887311) B1887311
theorem B1258287 : Blo 1256446 1258287 := bstep (se 1 (by rfl) ⟨943715, by rfl⟩ : syracuseStep 1258287 = 1887431) B1887431
theorem B1413967 : Blo 1256446 1413967 := bstep (se 1 (by rfl) ⟨1060475, by rfl⟩ : syracuseStep 1413967 = 2120951) B2120951
theorem B2831183 : Blo 1256446 2831183 := bstep (se 1 (by rfl) ⟨2123387, by rfl⟩ : syracuseStep 2831183 = 4246775) B4246775
theorem B1258395 : Blo 1256446 1258395 := bstep (se 1 (by rfl) ⟨943796, by rfl⟩ : syracuseStep 1258395 = 1887593) B1887593
theorem B41358289 : Blo 1256446 41358289 := bstep (se 2 (by rfl) ⟨15509358, by rfl⟩ : syracuseStep 41358289 = 31018717) B31018717
theorem B2831399 : Blo 1256446 2831399 := bstep (se 1 (by rfl) ⟨2123549, by rfl⟩ : syracuseStep 2831399 = 4247099) B4247099
theorem B12424337 : Blo 1256446 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B1414363 : Blo 1256446 1414363 := bstep (se 1 (by rfl) ⟨1060772, by rfl⟩ : syracuseStep 1414363 = 2121545) B2121545
theorem B4773113 : Blo 1256446 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B16102745 : Blo 1256446 16102745 := bstep (se 2 (by rfl) ⟨6038529, by rfl⟩ : syracuseStep 16102745 = 12077059) B12077059
theorem B1414651 : Blo 1256446 1414651 := bstep (se 1 (by rfl) ⟨1060988, by rfl⟩ : syracuseStep 1414651 = 2121977) B2121977
theorem B3184211 : Blo 1256446 3184211 := bstep (se 1 (by rfl) ⟨2388158, by rfl⟩ : syracuseStep 3184211 = 4776317) B4776317
theorem B1414831 : Blo 1256446 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B2684603 : Blo 1256446 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B1415119 : Blo 1256446 1415119 := bstep (se 1 (by rfl) ⟨1061339, by rfl⟩ : syracuseStep 1415119 = 2122679) B2122679
theorem B849082385 : Blo 1256446 849082385 := bstep (se 2 (by rfl) ⟨318405894, by rfl⟩ : syracuseStep 849082385 = 636811789) B636811789
theorem B8058959 : Blo 1256446 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B4241537 : Blo 1256446 4241537 := bstep (se 2 (by rfl) ⟨1590576, by rfl⟩ : syracuseStep 4241537 = 3181153) B3181153
theorem B4028545 : Blo 1256446 4028545 := bstep (se 2 (by rfl) ⟨1510704, by rfl⟩ : syracuseStep 4028545 = 3021409) B3021409
theorem B27195527 : Blo 1256446 27195527 := bstep (se 1 (by rfl) ⟨20396645, by rfl⟩ : syracuseStep 27195527 = 40793291) B40793291
theorem B49010837 : Blo 1256446 49010837 := bstep (se 6 (by rfl) ⟨1148691, by rfl⟩ : syracuseStep 49010837 = 2297383) B2297383
theorem B7166231 : Blo 1256446 7166231 := bstep (se 1 (by rfl) ⟨5374673, by rfl⟩ : syracuseStep 7166231 = 10749347) B10749347
theorem B1415515 : Blo 1256446 1415515 := bstep (se 1 (by rfl) ⟨1061636, by rfl⟩ : syracuseStep 1415515 = 2123273) B2123273
theorem B1415623 : Blo 1256446 1415623 := bstep (se 1 (by rfl) ⟨1061717, by rfl⟩ : syracuseStep 1415623 = 2123435) B2123435
theorem B17193467 : Blo 1256446 17193467 := bstep (se 1 (by rfl) ⟨12895100, by rfl⟩ : syracuseStep 17193467 = 25790201) B25790201
theorem B1341947 : Blo 1256446 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B4241915 : Blo 1256446 4241915 := bstep (se 1 (by rfl) ⟨3181436, by rfl⟩ : syracuseStep 4241915 = 6362873) B6362873
theorem B13597247 : Blo 1256446 13597247 := bstep (se 1 (by rfl) ⟨10197935, by rfl⟩ : syracuseStep 13597247 = 20395871) B20395871
theorem B9058949 : Blo 1256446 9058949 := bstep (se 4 (by rfl) ⟨849276, by rfl⟩ : syracuseStep 9058949 = 1698553) B1698553
theorem B12090131 : Blo 1256446 12090131 := bstep (se 1 (by rfl) ⟨9067598, by rfl⟩ : syracuseStep 12090131 = 18135197) B18135197
theorem B6454039 : Blo 1256446 6454039 := bstep (se 1 (by rfl) ⟨4840529, by rfl⟩ : syracuseStep 6454039 = 9681059) B9681059
theorem B4242347 : Blo 1256446 4242347 := bstep (se 1 (by rfl) ⟨3181760, by rfl⟩ : syracuseStep 4242347 = 6363521) B6363521
theorem B3578867 : Blo 1256446 3578867 := bstep (se 1 (by rfl) ⟨2684150, by rfl⟩ : syracuseStep 3578867 = 5368301) B5368301
theorem B3022073 : Blo 1256446 3022073 := bstep (se 2 (by rfl) ⟨1133277, by rfl⟩ : syracuseStep 3022073 = 2266555) B2266555
theorem B6044989 : Blo 1256446 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B4242887 : Blo 1256446 4242887 := bstep (se 1 (by rfl) ⟨3182165, by rfl⟩ : syracuseStep 4242887 = 6364331) B6364331
theorem B10468889 : Blo 1256446 10468889 := bstep (se 2 (by rfl) ⟨3925833, by rfl⟩ : syracuseStep 10468889 = 7851667) B7851667
theorem B8601113 : Blo 1256446 8601113 := bstep (se 2 (by rfl) ⟨3225417, by rfl⟩ : syracuseStep 8601113 = 6450835) B6450835
theorem B5447263 : Blo 1256446 5447263 := bstep (se 1 (by rfl) ⟨4085447, by rfl⟩ : syracuseStep 5447263 = 8170895) B8170895
theorem B12902003 : Blo 1256446 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B2121403 : Blo 1256446 2121403 := bstep (se 1 (by rfl) ⟨1591052, by rfl⟩ : syracuseStep 2121403 = 3182105) B3182105
theorem B4243211 : Blo 1256446 4243211 := bstep (se 1 (by rfl) ⟨3182408, by rfl⟩ : syracuseStep 4243211 = 6364817) B6364817
theorem B4030249 : Blo 1256446 4030249 := bstep (se 2 (by rfl) ⟨1511343, by rfl⟩ : syracuseStep 4030249 = 3022687) B3022687
theorem B3022649 : Blo 1256446 3022649 := bstep (se 2 (by rfl) ⟨1133493, by rfl⟩ : syracuseStep 3022649 = 2266987) B2266987
theorem B3399529 : Blo 1256446 3399529 := bstep (se 2 (by rfl) ⟨1274823, by rfl⟩ : syracuseStep 3399529 = 2549647) B2549647
theorem B8052655 : Blo 1256446 8052655 := bstep (se 1 (by rfl) ⟨6039491, by rfl⟩ : syracuseStep 8052655 = 12078983) B12078983
theorem B2686927 : Blo 1256446 2686927 := bstep (se 1 (by rfl) ⟨2015195, by rfl⟩ : syracuseStep 2686927 = 4030391) B4030391
theorem B2264219693 : Blo 1256446 2264219693 := bstep (se 3 (by rfl) ⟨424541192, by rfl⟩ : syracuseStep 2264219693 = 849082385) B849082385
theorem B8601881 : Blo 1256446 8601881 := bstep (se 2 (by rfl) ⟨3225705, by rfl⟩ : syracuseStep 8601881 = 6451411) B6451411
theorem B130695565 : Blo 1256446 130695565 := bstep (se 3 (by rfl) ⟨24505418, by rfl⟩ : syracuseStep 130695565 = 49010837) B49010837
theorem B6365627 : Blo 1256446 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B2687431 : Blo 1256446 2687431 := bstep (se 1 (by rfl) ⟨2015573, by rfl⟩ : syracuseStep 2687431 = 4031147) B4031147
theorem B7651835 : Blo 1256446 7651835 := bstep (se 1 (by rfl) ⟨5738876, by rfl⟩ : syracuseStep 7651835 = 11477753) B11477753
theorem B1884767 : Blo 1256446 1884767 := bstep (se 1 (by rfl) ⟨1413575, by rfl⟩ : syracuseStep 1884767 = 2827151) B2827151
theorem B4244075 : Blo 1256446 4244075 := bstep (se 1 (by rfl) ⟨3183056, by rfl⟩ : syracuseStep 4244075 = 6366113) B6366113
theorem B4653677 : Blo 1256446 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B7258859 : Blo 1256446 7258859 := bstep (se 1 (by rfl) ⟨5444144, by rfl⟩ : syracuseStep 7258859 = 10888289) B10888289
theorem B8061677 : Blo 1256446 8061677 := bstep (se 3 (by rfl) ⟨1511564, by rfl⟩ : syracuseStep 8061677 = 3023129) B3023129
theorem B4080395 : Blo 1256446 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B8282891 : Blo 1256446 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B2122537 : Blo 1256446 2122537 := bstep (se 2 (by rfl) ⟨795951, by rfl⟩ : syracuseStep 2122537 = 1591903) B1591903
theorem B2122807 : Blo 1256446 2122807 := bstep (se 1 (by rfl) ⟨1592105, by rfl⟩ : syracuseStep 2122807 = 3184211) B3184211
theorem B1885247 : Blo 1256446 1885247 := bstep (se 1 (by rfl) ⟨1413935, by rfl⟩ : syracuseStep 1885247 = 2827871) B2827871
theorem B1885289 : Blo 1256446 1885289 := bstep (se 2 (by rfl) ⟨706983, by rfl⟩ : syracuseStep 1885289 = 1413967) B1413967
theorem B4244669 : Blo 1256446 4244669 := bstep (se 3 (by rfl) ⟨795875, by rfl⟩ : syracuseStep 4244669 = 1591751) B1591751
theorem B1885391 : Blo 1256446 1885391 := bstep (se 1 (by rfl) ⟨1414043, by rfl⟩ : syracuseStep 1885391 = 2828087) B2828087
theorem B6046987 : Blo 1256446 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B1885595 : Blo 1256446 1885595 := bstep (se 1 (by rfl) ⟨1414196, by rfl⟩ : syracuseStep 1885595 = 2828393) B2828393
theorem B2827691 : Blo 1256446 2827691 := bstep (se 1 (by rfl) ⟨2120768, by rfl⟩ : syracuseStep 2827691 = 4241537) B4241537
theorem B18130351 : Blo 1256446 18130351 := bstep (se 1 (by rfl) ⟨13597763, by rfl⟩ : syracuseStep 18130351 = 27195527) B27195527
theorem B4777487 : Blo 1256446 4777487 := bstep (se 1 (by rfl) ⟨3583115, by rfl⟩ : syracuseStep 4777487 = 7166231) B7166231
theorem B5367377 : Blo 1256446 5367377 := bstep (se 2 (by rfl) ⟨2012766, by rfl⟩ : syracuseStep 5367377 = 4025533) B4025533
theorem B1885817 : Blo 1256446 1885817 := bstep (se 2 (by rfl) ⟨707181, by rfl⟩ : syracuseStep 1885817 = 1414363) B1414363
theorem B11462311 : Blo 1256446 11462311 := bstep (se 1 (by rfl) ⟨8596733, by rfl⟩ : syracuseStep 11462311 = 17193467) B17193467
theorem B2827943 : Blo 1256446 2827943 := bstep (se 1 (by rfl) ⟨2120957, by rfl⟩ : syracuseStep 2827943 = 4241915) B4241915
theorem B1885919 : Blo 1256446 1885919 := bstep (se 1 (by rfl) ⟨1414439, by rfl⟩ : syracuseStep 1885919 = 2828879) B2828879
theorem B6039299 : Blo 1256446 6039299 := bstep (se 1 (by rfl) ⟨4529474, by rfl⟩ : syracuseStep 6039299 = 9058949) B9058949
theorem B1591103 : Blo 1256446 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B1886015 : Blo 1256446 1886015 := bstep (se 1 (by rfl) ⟨1414511, by rfl⟩ : syracuseStep 1886015 = 2829023) B2829023
theorem B2828231 : Blo 1256446 2828231 := bstep (se 1 (by rfl) ⟨2121173, by rfl⟩ : syracuseStep 2828231 = 4242347) B4242347
theorem B1886183 : Blo 1256446 1886183 := bstep (se 1 (by rfl) ⟨1414637, by rfl⟩ : syracuseStep 1886183 = 2829275) B2829275
theorem B2385911 : Blo 1256446 2385911 := bstep (se 1 (by rfl) ⟨1789433, by rfl⟩ : syracuseStep 2385911 = 3578867) B3578867
theorem B1886201 : Blo 1256446 1886201 := bstep (se 2 (by rfl) ⟨707325, by rfl⟩ : syracuseStep 1886201 = 1414651) B1414651
theorem B10749995 : Blo 1256446 10749995 := bstep (se 1 (by rfl) ⟨8062496, by rfl⟩ : syracuseStep 10749995 = 16124993) B16124993
theorem B1886303 : Blo 1256446 1886303 := bstep (se 1 (by rfl) ⟨1414727, by rfl⟩ : syracuseStep 1886303 = 2829455) B2829455
theorem B73492609 : Blo 1256446 73492609 := bstep (se 2 (by rfl) ⟨27559728, by rfl⟩ : syracuseStep 73492609 = 55119457) B55119457
theorem B1886363 : Blo 1256446 1886363 := bstep (se 1 (by rfl) ⟨1414772, by rfl⟩ : syracuseStep 1886363 = 2829545) B2829545
theorem B1886399 : Blo 1256446 1886399 := bstep (se 1 (by rfl) ⟨1414799, by rfl⟩ : syracuseStep 1886399 = 2829599) B2829599
theorem B4245695 : Blo 1256446 4245695 := bstep (se 1 (by rfl) ⟨3184271, by rfl⟩ : syracuseStep 4245695 = 6368543) B6368543
theorem B1886441 : Blo 1256446 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B3180779 : Blo 1256446 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B2828537 : Blo 1256446 2828537 := bstep (se 2 (by rfl) ⟨1060701, by rfl⟩ : syracuseStep 2828537 = 2121403) B2121403
theorem B2828591 : Blo 1256446 2828591 := bstep (se 1 (by rfl) ⟨2121443, by rfl⟩ : syracuseStep 2828591 = 4242887) B4242887
theorem B4532705 : Blo 1256446 4532705 := bstep (se 2 (by rfl) ⟨1699764, by rfl⟩ : syracuseStep 4532705 = 3399529) B3399529
theorem B2828807 : Blo 1256446 2828807 := bstep (se 1 (by rfl) ⟨2121605, by rfl⟩ : syracuseStep 2828807 = 4243211) B4243211
theorem B1886747 : Blo 1256446 1886747 := bstep (se 1 (by rfl) ⟨1415060, by rfl⟩ : syracuseStep 1886747 = 2830121) B2830121
theorem B1886825 : Blo 1256446 1886825 := bstep (se 2 (by rfl) ⟨707559, by rfl⟩ : syracuseStep 1886825 = 1415119) B1415119
theorem B3582569 : Blo 1256446 3582569 := bstep (se 2 (by rfl) ⟨1343463, by rfl⟩ : syracuseStep 3582569 = 2686927) B2686927
theorem B2828987 : Blo 1256446 2828987 := bstep (se 1 (by rfl) ⟨2121740, by rfl⟩ : syracuseStep 2828987 = 4243481) B4243481
theorem B9563023 : Blo 1256446 9563023 := bstep (se 1 (by rfl) ⟨7172267, by rfl⟩ : syracuseStep 9563023 = 14344535) B14344535
theorem B6368219 : Blo 1256446 6368219 := bstep (se 1 (by rfl) ⟨4776164, by rfl⟩ : syracuseStep 6368219 = 9552329) B9552329
theorem B1256495 : Blo 1256446 1256495 := bstep (se 1 (by rfl) ⟨942371, by rfl⟩ : syracuseStep 1256495 = 1884743) B1884743
theorem B1256519 : Blo 1256446 1256519 := bstep (se 1 (by rfl) ⟨942389, by rfl⟩ : syracuseStep 1256519 = 1884779) B1884779
theorem B2387065 : Blo 1256446 2387065 := bstep (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) B1790299
theorem B1887353 : Blo 1256446 1887353 := bstep (se 2 (by rfl) ⟨707757, by rfl⟩ : syracuseStep 1887353 = 1415515) B1415515
theorem B1256671 : Blo 1256446 1256671 := bstep (se 1 (by rfl) ⟨942503, by rfl⟩ : syracuseStep 1256671 = 1885007) B1885007
theorem B1887455 : Blo 1256446 1887455 := bstep (se 1 (by rfl) ⟨1415591, by rfl⟩ : syracuseStep 1887455 = 2831183) B2831183
theorem B1887497 : Blo 1256446 1887497 := bstep (se 2 (by rfl) ⟨707811, by rfl⟩ : syracuseStep 1887497 = 1415623) B1415623
theorem B4304171 : Blo 1256446 4304171 := bstep (se 1 (by rfl) ⟨3228128, by rfl⟩ : syracuseStep 4304171 = 6456257) B6456257
theorem B1887599 : Blo 1256446 1887599 := bstep (se 1 (by rfl) ⟨1415699, by rfl⟩ : syracuseStep 1887599 = 2831399) B2831399
theorem B2387369 : Blo 1256446 2387369 := bstep (se 2 (by rfl) ⟨895263, by rfl⟩ : syracuseStep 2387369 = 1790527) B1790527
theorem B4025789 : Blo 1256446 4025789 := bstep (se 3 (by rfl) ⟨754835, by rfl⟩ : syracuseStep 4025789 = 1509671) B1509671
theorem B1256935 : Blo 1256446 1256935 := bstep (se 1 (by rfl) ⟨942701, by rfl⟩ : syracuseStep 1256935 = 1885403) B1885403
theorem B2829815 : Blo 1256446 2829815 := bstep (se 1 (by rfl) ⟨2122361, by rfl⟩ : syracuseStep 2829815 = 4244723) B4244723
theorem B3182075 : Blo 1256446 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B10735163 : Blo 1256446 10735163 := bstep (se 1 (by rfl) ⟨8051372, by rfl⟩ : syracuseStep 10735163 = 16102745) B16102745
theorem B2829887 : Blo 1256446 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B1257051 : Blo 1256446 1257051 := bstep (se 1 (by rfl) ⟨942788, by rfl⟩ : syracuseStep 1257051 = 1885577) B1885577
theorem B8605385 : Blo 1256446 8605385 := bstep (se 2 (by rfl) ⟨3227019, by rfl⟩ : syracuseStep 8605385 = 6454039) B6454039
theorem B1257287 : Blo 1256446 1257287 := bstep (se 1 (by rfl) ⟨942965, by rfl⟩ : syracuseStep 1257287 = 1885931) B1885931
theorem B55144385 : Blo 1256446 55144385 := bstep (se 2 (by rfl) ⟨20679144, by rfl⟩ : syracuseStep 55144385 = 41358289) B41358289
theorem B30609373 : Blo 1256446 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B1257439 : Blo 1256446 1257439 := bstep (se 1 (by rfl) ⟨943079, by rfl⟩ : syracuseStep 1257439 = 1886159) B1886159
theorem B25800713 : Blo 1256446 25800713 := bstep (se 2 (by rfl) ⟨9675267, by rfl⟩ : syracuseStep 25800713 = 19350535) B19350535
theorem B1257703 : Blo 1256446 1257703 := bstep (se 1 (by rfl) ⟨943277, by rfl⟩ : syracuseStep 1257703 = 1886555) B1886555
theorem B9064831 : Blo 1256446 9064831 := bstep (se 1 (by rfl) ⟨6798623, by rfl⟩ : syracuseStep 9064831 = 13597247) B13597247
theorem B1257855 : Blo 1256446 1257855 := bstep (se 1 (by rfl) ⟨943391, by rfl⟩ : syracuseStep 1257855 = 1886783) B1886783
theorem B1257935 : Blo 1256446 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B3183097 : Blo 1256446 3183097 := bstep (se 2 (by rfl) ⟨1193661, by rfl⟩ : syracuseStep 3183097 = 2387323) B2387323
theorem B2830841 : Blo 1256446 2830841 := bstep (se 2 (by rfl) ⟨1061565, by rfl⟩ : syracuseStep 2830841 = 2123131) B2123131
theorem B2830931 : Blo 1256446 2830931 := bstep (se 1 (by rfl) ⟨2123198, by rfl⟩ : syracuseStep 2830931 = 4246397) B4246397
theorem B1258087 : Blo 1256446 1258087 := bstep (se 1 (by rfl) ⟨943565, by rfl⟩ : syracuseStep 1258087 = 1887131) B1887131
theorem B2831111 : Blo 1256446 2831111 := bstep (se 1 (by rfl) ⟨2123333, by rfl⟩ : syracuseStep 2831111 = 4246667) B4246667
theorem B3183401 : Blo 1256446 3183401 := bstep (se 2 (by rfl) ⟨1193775, by rfl⟩ : syracuseStep 3183401 = 2387551) B2387551
theorem B7263017 : Blo 1256446 7263017 := bstep (se 2 (by rfl) ⟨2723631, by rfl⟩ : syracuseStep 7263017 = 5447263) B5447263
theorem B1258351 : Blo 1256446 1258351 := bstep (se 1 (by rfl) ⟨943763, by rfl⟩ : syracuseStep 1258351 = 1887527) B1887527
theorem B1258407 : Blo 1256446 1258407 := bstep (se 1 (by rfl) ⟨943805, by rfl⟩ : syracuseStep 1258407 = 1887611) B1887611
theorem B4535471 : Blo 1256446 4535471 := bstep (se 1 (by rfl) ⟨3401603, by rfl⟩ : syracuseStep 4535471 = 6803207) B6803207
theorem B44119235 : Blo 1256446 44119235 := bstep (se 1 (by rfl) ⟨33089426, by rfl⟩ : syracuseStep 44119235 = 66178853) B66178853
theorem B10736873 : Blo 1256446 10736873 := bstep (se 2 (by rfl) ⟨4026327, by rfl⟩ : syracuseStep 10736873 = 8052655) B8052655
theorem B15283475 : Blo 1256446 15283475 := bstep (se 1 (by rfl) ⟨11462606, by rfl⟩ : syracuseStep 15283475 = 22925213) B22925213
theorem B27186529 : Blo 1256446 27186529 := bstep (se 2 (by rfl) ⟨10194948, by rfl⟩ : syracuseStep 27186529 = 20389897) B20389897
theorem B5371393 : Blo 1256446 5371393 := bstep (se 2 (by rfl) ⟨2014272, by rfl⟩ : syracuseStep 5371393 = 4028545) B4028545
theorem B7353865 : Blo 1256446 7353865 := bstep (se 2 (by rfl) ⟨2757699, by rfl⟩ : syracuseStep 7353865 = 5515399) B5515399
theorem B7157483 : Blo 1256446 7157483 := bstep (se 1 (by rfl) ⟨5368112, by rfl⟩ : syracuseStep 7157483 = 10736225) B10736225
theorem B2012959 : Blo 1256446 2012959 := bstep (se 1 (by rfl) ⟨1509719, by rfl⟩ : syracuseStep 2012959 = 3019439) B3019439
theorem B1414975 : Blo 1256446 1414975 := bstep (se 1 (by rfl) ⟨1061231, by rfl⟩ : syracuseStep 1414975 = 2122463) B2122463
theorem B110319569 : Blo 1256446 110319569 := bstep (se 2 (by rfl) ⟨41369838, by rfl⟩ : syracuseStep 110319569 = 82739677) B82739677
theorem B10737623 : Blo 1256446 10737623 := bstep (se 1 (by rfl) ⟨8053217, by rfl⟩ : syracuseStep 10737623 = 16106435) B16106435
theorem B1415263 : Blo 1256446 1415263 := bstep (se 1 (by rfl) ⟨1061447, by rfl⟩ : syracuseStep 1415263 = 2122895) B2122895
theorem B3578525 : Blo 1256446 3578525 := bstep (se 3 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 3578525 = 1341947) B1341947
theorem B4242077 : Blo 1256446 4242077 := bstep (se 3 (by rfl) ⟨795389, by rfl⟩ : syracuseStep 4242077 = 1590779) B1590779
theorem B5372639 : Blo 1256446 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B2120539 : Blo 1256446 2120539 := bstep (se 1 (by rfl) ⟨1590404, by rfl⟩ : syracuseStep 2120539 = 3180809) B3180809
theorem B4242401 : Blo 1256446 4242401 := bstep (se 2 (by rfl) ⟨1590900, by rfl⟩ : syracuseStep 4242401 = 3181801) B3181801
theorem B8059985 : Blo 1256446 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B15293555 : Blo 1256446 15293555 := bstep (se 1 (by rfl) ⟨11470166, by rfl⟩ : syracuseStep 15293555 = 22940333) B22940333
theorem B82689173 : Blo 1256446 82689173 := bstep (se 6 (by rfl) ⟨1938027, by rfl⟩ : syracuseStep 82689173 = 3876055) B3876055
theorem B7158941 : Blo 1256446 7158941 := bstep (se 3 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 7158941 = 2684603) B2684603
theorem B8060087 : Blo 1256446 8060087 := bstep (se 1 (by rfl) ⟨6045065, by rfl⟩ : syracuseStep 8060087 = 12090131) B12090131
theorem B4242617 : Blo 1256446 4242617 := bstep (se 2 (by rfl) ⟨1590981, by rfl⟩ : syracuseStep 4242617 = 3181963) B3181963
theorem B4357373 : Blo 1256446 4357373 := bstep (se 3 (by rfl) ⟨817007, by rfl⟩ : syracuseStep 4357373 = 1634015) B1634015
theorem B2014715 : Blo 1256446 2014715 := bstep (se 1 (by rfl) ⟨1511036, by rfl⟩ : syracuseStep 2014715 = 3022073) B3022073
theorem B3399259 : Blo 1256446 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B6979259 : Blo 1256446 6979259 := bstep (se 1 (by rfl) ⟨5234444, by rfl⟩ : syracuseStep 6979259 = 10468889) B10468889
theorem B5734075 : Blo 1256446 5734075 := bstep (se 1 (by rfl) ⟨4300556, by rfl⟩ : syracuseStep 5734075 = 8601113) B8601113
theorem B5373665 : Blo 1256446 5373665 := bstep (se 2 (by rfl) ⟨2015124, by rfl⟩ : syracuseStep 5373665 = 4030249) B4030249
theorem B8601335 : Blo 1256446 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B2121511 : Blo 1256446 2121511 := bstep (se 1 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 2121511 = 3182267) B3182267
theorem B2015099 : Blo 1256446 2015099 := bstep (se 1 (by rfl) ⟨1511324, by rfl⟩ : syracuseStep 2015099 = 3022649) B3022649
theorem B4530109 : Blo 1256446 4530109 := bstep (se 3 (by rfl) ⟨849395, by rfl⟩ : syracuseStep 4530109 = 1698791) B1698791
theorem B24166349 : Blo 1256446 24166349 := bstep (se 3 (by rfl) ⟨4531190, by rfl⟩ : syracuseStep 24166349 = 9062381) B9062381
theorem B4243751 : Blo 1256446 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B5374451 : Blo 1256446 5374451 := bstep (se 1 (by rfl) ⟨4030838, by rfl⟩ : syracuseStep 5374451 = 8061677) B8061677
theorem B174260753 : Blo 1256446 174260753 := bstep (se 2 (by rfl) ⟨65347782, by rfl⟩ : syracuseStep 174260753 = 130695565) B130695565
theorem B2122267 : Blo 1256446 2122267 := bstep (se 1 (by rfl) ⟨1591700, by rfl⟩ : syracuseStep 2122267 = 3183401) B3183401
theorem B4842011 : Blo 1256446 4842011 := bstep (se 1 (by rfl) ⟨3631508, by rfl⟩ : syracuseStep 4842011 = 7263017) B7263017
theorem B4244129 : Blo 1256446 4244129 := bstep (se 2 (by rfl) ⟨1591548, by rfl⟩ : syracuseStep 4244129 = 3183097) B3183097
theorem B22938349 : Blo 1256446 22938349 := bstep (se 3 (by rfl) ⟨4300940, by rfl⟩ : syracuseStep 22938349 = 8601881) B8601881
theorem B1885127 : Blo 1256446 1885127 := bstep (se 1 (by rfl) ⟨1413845, by rfl⟩ : syracuseStep 1885127 = 2827691) B2827691
theorem B1885295 : Blo 1256446 1885295 := bstep (se 1 (by rfl) ⟨1413971, by rfl⟩ : syracuseStep 1885295 = 2827943) B2827943
theorem B2827385 : Blo 1256446 2827385 := bstep (se 2 (by rfl) ⟨1060269, by rfl⟩ : syracuseStep 2827385 = 2120539) B2120539
theorem B1885487 : Blo 1256446 1885487 := bstep (se 1 (by rfl) ⟨1414115, by rfl⟩ : syracuseStep 1885487 = 2828231) B2828231
theorem B1590607 : Blo 1256446 1590607 := bstep (se 1 (by rfl) ⟨1192955, by rfl⟩ : syracuseStep 1590607 = 2385911) B2385911
theorem B1885691 : Blo 1256446 1885691 := bstep (se 1 (by rfl) ⟨1414268, by rfl⟩ : syracuseStep 1885691 = 2828537) B2828537
theorem B1885727 : Blo 1256446 1885727 := bstep (se 1 (by rfl) ⟨1414295, by rfl⟩ : syracuseStep 1885727 = 2828591) B2828591
theorem B1885871 : Blo 1256446 1885871 := bstep (se 1 (by rfl) ⟨1414403, by rfl⟩ : syracuseStep 1885871 = 2828807) B2828807
theorem B8062649 : Blo 1256446 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B2385683 : Blo 1256446 2385683 := bstep (se 1 (by rfl) ⟨1789262, by rfl⟩ : syracuseStep 2385683 = 3578525) B3578525
theorem B2828051 : Blo 1256446 2828051 := bstep (se 1 (by rfl) ⟨2121038, by rfl⟩ : syracuseStep 2828051 = 4242077) B4242077
theorem B1885991 : Blo 1256446 1885991 := bstep (se 1 (by rfl) ⟨1414493, by rfl⟩ : syracuseStep 1885991 = 2828987) B2828987
theorem B3581759 : Blo 1256446 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B4245479 : Blo 1256446 4245479 := bstep (se 1 (by rfl) ⟨3184109, by rfl⟩ : syracuseStep 4245479 = 6368219) B6368219
theorem B2828267 : Blo 1256446 2828267 := bstep (se 1 (by rfl) ⟨2121200, by rfl⟩ : syracuseStep 2828267 = 4242401) B4242401
theorem B7161857 : Blo 1256446 7161857 := bstep (se 2 (by rfl) ⟨2685696, by rfl⟩ : syracuseStep 7161857 = 5371393) B5371393
theorem B10881053 : Blo 1256446 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B22087709 : Blo 1256446 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B55126115 : Blo 1256446 55126115 := bstep (se 1 (by rfl) ⟨41344586, by rfl⟩ : syracuseStep 55126115 = 82689173) B82689173
theorem B4532345 : Blo 1256446 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B2828411 : Blo 1256446 2828411 := bstep (se 1 (by rfl) ⟨2121308, by rfl⟩ : syracuseStep 2828411 = 4242617) B4242617
theorem B2869447 : Blo 1256446 2869447 := bstep (se 1 (by rfl) ⟨2152085, by rfl⟩ : syracuseStep 2869447 = 4304171) B4304171
theorem B7645433 : Blo 1256446 7645433 := bstep (se 2 (by rfl) ⟨2867037, by rfl⟩ : syracuseStep 7645433 = 5734075) B5734075
theorem B1591579 : Blo 1256446 1591579 := bstep (se 1 (by rfl) ⟨1193684, by rfl⟩ : syracuseStep 1591579 = 2387369) B2387369
theorem B1886543 : Blo 1256446 1886543 := bstep (se 1 (by rfl) ⟨1414907, by rfl⟩ : syracuseStep 1886543 = 2829815) B2829815
theorem B1886591 : Blo 1256446 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B2828681 : Blo 1256446 2828681 := bstep (se 2 (by rfl) ⟨1060755, by rfl⟩ : syracuseStep 2828681 = 2121511) B2121511
theorem B1886633 : Blo 1256446 1886633 := bstep (se 2 (by rfl) ⟨707487, by rfl⟩ : syracuseStep 1886633 = 1414975) B1414975
theorem B5736923 : Blo 1256446 5736923 := bstep (se 1 (by rfl) ⟨4302692, by rfl⟩ : syracuseStep 5736923 = 8605385) B8605385
theorem B3582443 : Blo 1256446 3582443 := bstep (se 1 (by rfl) ⟨2686832, by rfl⟩ : syracuseStep 3582443 = 5373665) B5373665
theorem B6040145 : Blo 1256446 6040145 := bstep (se 2 (by rfl) ⟨2265054, by rfl⟩ : syracuseStep 6040145 = 4530109) B4530109
theorem B1887017 : Blo 1256446 1887017 := bstep (se 2 (by rfl) ⟨707631, by rfl⟩ : syracuseStep 1887017 = 1415263) B1415263
theorem B1887227 : Blo 1256446 1887227 := bstep (se 1 (by rfl) ⟨1415420, by rfl⟩ : syracuseStep 1887227 = 2830841) B2830841
theorem B1887287 : Blo 1256446 1887287 := bstep (se 1 (by rfl) ⟨1415465, by rfl⟩ : syracuseStep 1887287 = 2830931) B2830931
theorem B1256511 : Blo 1256446 1256511 := bstep (se 1 (by rfl) ⟨942383, by rfl⟩ : syracuseStep 1256511 = 1884767) B1884767
theorem B2829383 : Blo 1256446 2829383 := bstep (se 1 (by rfl) ⟨2122037, by rfl⟩ : syracuseStep 2829383 = 4244075) B4244075
theorem B12094589 : Blo 1256446 12094589 := bstep (se 3 (by rfl) ⟨2267735, by rfl⟩ : syracuseStep 12094589 = 4535471) B4535471
theorem B12086441 : Blo 1256446 12086441 := bstep (se 2 (by rfl) ⟨4532415, by rfl⟩ : syracuseStep 12086441 = 9064831) B9064831
theorem B1887407 : Blo 1256446 1887407 := bstep (se 1 (by rfl) ⟨1415555, by rfl⟩ : syracuseStep 1887407 = 2831111) B2831111
theorem B3583241 : Blo 1256446 3583241 := bstep (se 2 (by rfl) ⟨1343715, by rfl⟩ : syracuseStep 3583241 = 2687431) B2687431
theorem B11619661 : Blo 1256446 11619661 := bstep (se 3 (by rfl) ⟨2178686, by rfl⟩ : syracuseStep 11619661 = 4357373) B4357373
theorem B1256831 : Blo 1256446 1256831 := bstep (se 1 (by rfl) ⟨942623, by rfl⟩ : syracuseStep 1256831 = 1885247) B1885247
theorem B1256859 : Blo 1256446 1256859 := bstep (se 1 (by rfl) ⟨942644, by rfl⟩ : syracuseStep 1256859 = 1885289) B1885289
theorem B2829779 : Blo 1256446 2829779 := bstep (se 1 (by rfl) ⟨2122334, by rfl⟩ : syracuseStep 2829779 = 4244669) B4244669
theorem B29412823 : Blo 1256446 29412823 := bstep (se 1 (by rfl) ⟨22059617, by rfl⟩ : syracuseStep 29412823 = 44119235) B44119235
theorem B1256927 : Blo 1256446 1256927 := bstep (se 1 (by rfl) ⟨942695, by rfl⟩ : syracuseStep 1256927 = 1885391) B1885391
theorem B1257063 : Blo 1256446 1257063 := bstep (se 1 (by rfl) ⟨942797, by rfl⟩ : syracuseStep 1257063 = 1885595) B1885595
theorem B2830049 : Blo 1256446 2830049 := bstep (se 2 (by rfl) ⟨1061268, by rfl⟩ : syracuseStep 2830049 = 2122537) B2122537
theorem B1257211 : Blo 1256446 1257211 := bstep (se 1 (by rfl) ⟨942908, by rfl⟩ : syracuseStep 1257211 = 1885817) B1885817
theorem B1257279 : Blo 1256446 1257279 := bstep (se 1 (by rfl) ⟨942959, by rfl⟩ : syracuseStep 1257279 = 1885919) B1885919
theorem B4771655 : Blo 1256446 4771655 := bstep (se 1 (by rfl) ⟨3578741, by rfl⟩ : syracuseStep 4771655 = 7157483) B7157483
theorem B4026199 : Blo 1256446 4026199 := bstep (se 1 (by rfl) ⟨3019649, by rfl⟩ : syracuseStep 4026199 = 6039299) B6039299
theorem B12750697 : Blo 1256446 12750697 := bstep (se 2 (by rfl) ⟨4781511, by rfl⟩ : syracuseStep 12750697 = 9563023) B9563023
theorem B1257343 : Blo 1256446 1257343 := bstep (se 1 (by rfl) ⟨943007, by rfl⟩ : syracuseStep 1257343 = 1886015) B1886015
theorem B1257455 : Blo 1256446 1257455 := bstep (se 1 (by rfl) ⟨943091, by rfl⟩ : syracuseStep 1257455 = 1886183) B1886183
theorem B1257467 : Blo 1256446 1257467 := bstep (se 1 (by rfl) ⟨943100, by rfl⟩ : syracuseStep 1257467 = 1886201) B1886201
theorem B1257535 : Blo 1256446 1257535 := bstep (se 1 (by rfl) ⟨943151, by rfl⟩ : syracuseStep 1257535 = 1886303) B1886303
theorem B2830409 : Blo 1256446 2830409 := bstep (se 2 (by rfl) ⟨1061403, by rfl⟩ : syracuseStep 2830409 = 2122807) B2122807
theorem B1257575 : Blo 1256446 1257575 := bstep (se 1 (by rfl) ⟨943181, by rfl⟩ : syracuseStep 1257575 = 1886363) B1886363
theorem B1257599 : Blo 1256446 1257599 := bstep (se 1 (by rfl) ⟨943199, by rfl⟩ : syracuseStep 1257599 = 1886399) B1886399
theorem B2830463 : Blo 1256446 2830463 := bstep (se 1 (by rfl) ⟨2122847, by rfl⟩ : syracuseStep 2830463 = 4245695) B4245695
theorem B1257627 : Blo 1256446 1257627 := bstep (se 1 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 1257627 = 1886441) B1886441
theorem B3182753 : Blo 1256446 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B1257831 : Blo 1256446 1257831 := bstep (se 1 (by rfl) ⟨943373, by rfl⟩ : syracuseStep 1257831 = 1886747) B1886747
theorem B1257883 : Blo 1256446 1257883 := bstep (se 1 (by rfl) ⟨943412, by rfl⟩ : syracuseStep 1257883 = 1886825) B1886825
theorem B2388379 : Blo 1256446 2388379 := bstep (se 1 (by rfl) ⟨1791284, by rfl⟩ : syracuseStep 2388379 = 3582569) B3582569
theorem B10195703 : Blo 1256446 10195703 := bstep (se 1 (by rfl) ⟨7646777, by rfl⟩ : syracuseStep 10195703 = 15293555) B15293555
theorem B1258235 : Blo 1256446 1258235 := bstep (se 1 (by rfl) ⟨943676, by rfl⟩ : syracuseStep 1258235 = 1887353) B1887353
theorem B4772627 : Blo 1256446 4772627 := bstep (se 1 (by rfl) ⟨3579470, by rfl⟩ : syracuseStep 4772627 = 7158941) B7158941
theorem B1258303 : Blo 1256446 1258303 := bstep (se 1 (by rfl) ⟨943727, by rfl⟩ : syracuseStep 1258303 = 1887455) B1887455
theorem B1258331 : Blo 1256446 1258331 := bstep (se 1 (by rfl) ⟨943748, by rfl⟩ : syracuseStep 1258331 = 1887497) B1887497
theorem B15283081 : Blo 1256446 15283081 := bstep (se 2 (by rfl) ⟨5731155, by rfl⟩ : syracuseStep 15283081 = 11462311) B11462311
theorem B1258399 : Blo 1256446 1258399 := bstep (se 1 (by rfl) ⟨943799, by rfl⟩ : syracuseStep 1258399 = 1887599) B1887599
theorem B2683859 : Blo 1256446 2683859 := bstep (se 1 (by rfl) ⟨2012894, by rfl⟩ : syracuseStep 2683859 = 4025789) B4025789
theorem B7156775 : Blo 1256446 7156775 := bstep (se 1 (by rfl) ⟨5367581, by rfl⟩ : syracuseStep 7156775 = 10735163) B10735163
theorem B2683945 : Blo 1256446 2683945 := bstep (se 2 (by rfl) ⟨1006479, by rfl⟩ : syracuseStep 2683945 = 2012959) B2012959
theorem B36762923 : Blo 1256446 36762923 := bstep (se 1 (by rfl) ⟨27572192, by rfl⟩ : syracuseStep 36762923 = 55144385) B55144385
theorem B16110899 : Blo 1256446 16110899 := bstep (se 1 (by rfl) ⟨12083174, by rfl⟩ : syracuseStep 16110899 = 24166349) B24166349
theorem B17200475 : Blo 1256446 17200475 := bstep (se 1 (by rfl) ⟨12900356, by rfl⟩ : syracuseStep 17200475 = 25800713) B25800713
theorem B1509479795 : Blo 1256446 1509479795 := bstep (se 1 (by rfl) ⟨1132109846, by rfl⟩ : syracuseStep 1509479795 = 2264219693) B2264219693
theorem B97990145 : Blo 1256446 97990145 := bstep (se 2 (by rfl) ⟨36746304, by rfl⟩ : syracuseStep 97990145 = 73492609) B73492609
theorem B5101223 : Blo 1256446 5101223 := bstep (se 1 (by rfl) ⟨3825917, by rfl⟩ : syracuseStep 5101223 = 7651835) B7651835
theorem B4839239 : Blo 1256446 4839239 := bstep (se 1 (by rfl) ⟨3629429, by rfl⟩ : syracuseStep 4839239 = 7258859) B7258859
theorem B7157915 : Blo 1256446 7157915 := bstep (se 1 (by rfl) ⟨5368436, by rfl⟩ : syracuseStep 7157915 = 10736873) B10736873
theorem B10188983 : Blo 1256446 10188983 := bstep (se 1 (by rfl) ⟨7641737, by rfl⟩ : syracuseStep 10188983 = 15283475) B15283475
theorem B3184991 : Blo 1256446 3184991 := bstep (se 1 (by rfl) ⟨2388743, by rfl⟩ : syracuseStep 3184991 = 4777487) B4777487
theorem B3578251 : Blo 1256446 3578251 := bstep (se 1 (by rfl) ⟨2683688, by rfl⟩ : syracuseStep 3578251 = 5367377) B5367377
theorem B73546379 : Blo 1256446 73546379 := bstep (se 1 (by rfl) ⟨55159784, by rfl⟩ : syracuseStep 73546379 = 110319569) B110319569
theorem B7158415 : Blo 1256446 7158415 := bstep (se 1 (by rfl) ⟨5368811, by rfl⟩ : syracuseStep 7158415 = 10737623) B10737623
theorem B7166663 : Blo 1256446 7166663 := bstep (se 1 (by rfl) ⟨5374997, by rfl⟩ : syracuseStep 7166663 = 10749995) B10749995
theorem B2120519 : Blo 1256446 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B12409805 : Blo 1256446 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B3021803 : Blo 1256446 3021803 := bstep (se 1 (by rfl) ⟨2266352, by rfl⟩ : syracuseStep 3021803 = 4532705) B4532705
theorem B36248705 : Blo 1256446 36248705 := bstep (se 2 (by rfl) ⟨13593264, by rfl⟩ : syracuseStep 36248705 = 27186529) B27186529
theorem B24173801 : Blo 1256446 24173801 := bstep (se 2 (by rfl) ⟨9065175, by rfl⟩ : syracuseStep 24173801 = 18130351) B18130351
theorem B9805153 : Blo 1256446 9805153 := bstep (se 2 (by rfl) ⟨3676932, by rfl⟩ : syracuseStep 9805153 = 7353865) B7353865
theorem B5373323 : Blo 1256446 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B5373391 : Blo 1256446 5373391 := bstep (se 1 (by rfl) ⟨4030043, by rfl⟩ : syracuseStep 5373391 = 8060087) B8060087
theorem B4242941 : Blo 1256446 4242941 := bstep (se 3 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 4242941 = 1591103) B1591103
theorem B2121383 : Blo 1256446 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B1343143 : Blo 1256446 1343143 := bstep (se 1 (by rfl) ⟨1007357, by rfl⟩ : syracuseStep 1343143 = 2014715) B2014715
theorem B4652839 : Blo 1256446 4652839 := bstep (se 1 (by rfl) ⟨3489629, by rfl⟩ : syracuseStep 4652839 = 6979259) B6979259
theorem B5734223 : Blo 1256446 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B1343399 : Blo 1256446 1343399 := bstep (se 1 (by rfl) ⟨1007549, by rfl⟩ : syracuseStep 1343399 = 2015099) B2015099
theorem B40812497 : Blo 1256446 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B2121835 : Blo 1256446 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B3825929 : Blo 1256446 3825929 := bstep (se 2 (by rfl) ⟨1434723, by rfl⟩ : syracuseStep 3825929 = 2869447) B2869447
theorem B235602229 : Blo 1256446 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B3228007 : Blo 1256446 3228007 := bstep (se 1 (by rfl) ⟨2421005, by rfl⟩ : syracuseStep 3228007 = 4842011) B4842011
theorem B2122105 : Blo 1256446 2122105 := bstep (se 2 (by rfl) ⟨795789, by rfl⟩ : syracuseStep 2122105 = 1591579) B1591579
theorem B1884923 : Blo 1256446 1884923 := bstep (se 1 (by rfl) ⟨1413692, by rfl⟩ : syracuseStep 1884923 = 2827385) B2827385
theorem B9544553 : Blo 1256446 9544553 := bstep (se 2 (by rfl) ⟨3579207, by rfl⟩ : syracuseStep 9544553 = 7158415) B7158415
theorem B10740599 : Blo 1256446 10740599 := bstep (se 1 (by rfl) ⟨8055449, by rfl⟩ : syracuseStep 10740599 = 16110899) B16110899
theorem B5375099 : Blo 1256446 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B1590455 : Blo 1256446 1590455 := bstep (se 1 (by rfl) ⟨1192841, by rfl⟩ : syracuseStep 1590455 = 2385683) B2385683
theorem B1885367 : Blo 1256446 1885367 := bstep (se 1 (by rfl) ⟨1414025, by rfl⟩ : syracuseStep 1885367 = 2828051) B2828051
theorem B1885511 : Blo 1256446 1885511 := bstep (se 1 (by rfl) ⟨1414133, by rfl⟩ : syracuseStep 1885511 = 2828267) B2828267
theorem B36750743 : Blo 1256446 36750743 := bstep (se 1 (by rfl) ⟨27563057, by rfl⟩ : syracuseStep 36750743 = 55126115) B55126115
theorem B1885607 : Blo 1256446 1885607 := bstep (se 1 (by rfl) ⟨1414205, by rfl⟩ : syracuseStep 1885607 = 2828411) B2828411
theorem B6792655 : Blo 1256446 6792655 := bstep (se 1 (by rfl) ⟨5094491, by rfl⟩ : syracuseStep 6792655 = 10188983) B10188983
theorem B2123327 : Blo 1256446 2123327 := bstep (se 1 (by rfl) ⟨1592495, by rfl⟩ : syracuseStep 2123327 = 3184991) B3184991
theorem B1885787 : Blo 1256446 1885787 := bstep (se 1 (by rfl) ⟨1414340, by rfl⟩ : syracuseStep 1885787 = 2828681) B2828681
theorem B49030919 : Blo 1256446 49030919 := bstep (se 1 (by rfl) ⟨36773189, by rfl⟩ : syracuseStep 49030919 = 73546379) B73546379
theorem B15492881 : Blo 1256446 15492881 := bstep (se 2 (by rfl) ⟨5809830, by rfl⟩ : syracuseStep 15492881 = 11619661) B11619661
theorem B4777775 : Blo 1256446 4777775 := bstep (se 1 (by rfl) ⟨3583331, by rfl⟩ : syracuseStep 4777775 = 7166663) B7166663
theorem B68003717 : Blo 1256446 68003717 := bstep (se 4 (by rfl) ⟨6375348, by rfl⟩ : syracuseStep 68003717 = 12750697) B12750697
theorem B39217097 : Blo 1256446 39217097 := bstep (se 2 (by rfl) ⟨14706411, by rfl⟩ : syracuseStep 39217097 = 29412823) B29412823
theorem B1886255 : Blo 1256446 1886255 := bstep (se 1 (by rfl) ⟨1414691, by rfl⟩ : syracuseStep 1886255 = 2829383) B2829383
theorem B8063059 : Blo 1256446 8063059 := bstep (se 1 (by rfl) ⟨6047294, by rfl⟩ : syracuseStep 8063059 = 12094589) B12094589
theorem B16115867 : Blo 1256446 16115867 := bstep (se 1 (by rfl) ⟨12086900, by rfl⟩ : syracuseStep 16115867 = 24173801) B24173801
theorem B3582215 : Blo 1256446 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B1886519 : Blo 1256446 1886519 := bstep (se 1 (by rfl) ⟨1414889, by rfl⟩ : syracuseStep 1886519 = 2829779) B2829779
theorem B2828627 : Blo 1256446 2828627 := bstep (se 1 (by rfl) ⟨2121470, by rfl⟩ : syracuseStep 2828627 = 4242941) B4242941
theorem B6203785 : Blo 1256446 6203785 := bstep (se 2 (by rfl) ⟨2326419, by rfl⟩ : syracuseStep 6203785 = 4652839) B4652839
theorem B3582397 : Blo 1256446 3582397 := bstep (se 3 (by rfl) ⟨671699, by rfl⟩ : syracuseStep 3582397 = 1343399) B1343399
theorem B5368265 : Blo 1256446 5368265 := bstep (se 2 (by rfl) ⟨2013099, by rfl⟩ : syracuseStep 5368265 = 4026199) B4026199
theorem B1886699 : Blo 1256446 1886699 := bstep (se 1 (by rfl) ⟨1415024, by rfl⟩ : syracuseStep 1886699 = 2830049) B2830049
theorem B3181103 : Blo 1256446 3181103 := bstep (se 1 (by rfl) ⟨2385827, by rfl⟩ : syracuseStep 3181103 = 4771655) B4771655
theorem B27208331 : Blo 1256446 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B1886939 : Blo 1256446 1886939 := bstep (se 1 (by rfl) ⟨1415204, by rfl⟩ : syracuseStep 1886939 = 2830409) B2830409
theorem B1886975 : Blo 1256446 1886975 := bstep (se 1 (by rfl) ⟨1415231, by rfl⟩ : syracuseStep 1886975 = 2830463) B2830463
theorem B2829167 : Blo 1256446 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B3582967 : Blo 1256446 3582967 := bstep (se 1 (by rfl) ⟨2687225, by rfl⟩ : syracuseStep 3582967 = 5374451) B5374451
theorem B116173835 : Blo 1256446 116173835 := bstep (se 1 (by rfl) ⟨87130376, by rfl⟩ : syracuseStep 116173835 = 174260753) B174260753
theorem B2829419 : Blo 1256446 2829419 := bstep (se 1 (by rfl) ⟨2122064, by rfl⟩ : syracuseStep 2829419 = 4244129) B4244129
theorem B3181751 : Blo 1256446 3181751 := bstep (se 1 (by rfl) ⟨2386313, by rfl⟩ : syracuseStep 3181751 = 4772627) B4772627
theorem B4771001 : Blo 1256446 4771001 := bstep (se 2 (by rfl) ⟨1789125, by rfl⟩ : syracuseStep 4771001 = 3578251) B3578251
theorem B1256751 : Blo 1256446 1256751 := bstep (se 1 (by rfl) ⟨942563, by rfl⟩ : syracuseStep 1256751 = 1885127) B1885127
theorem B4771183 : Blo 1256446 4771183 := bstep (se 1 (by rfl) ⟨3578387, by rfl⟩ : syracuseStep 4771183 = 7156775) B7156775
theorem B2829689 : Blo 1256446 2829689 := bstep (se 2 (by rfl) ⟨1061133, by rfl⟩ : syracuseStep 2829689 = 2122267) B2122267
theorem B1256863 : Blo 1256446 1256863 := bstep (se 1 (by rfl) ⟨942647, by rfl⟩ : syracuseStep 1256863 = 1885295) B1885295
theorem B1256991 : Blo 1256446 1256991 := bstep (se 1 (by rfl) ⟨942743, by rfl⟩ : syracuseStep 1256991 = 1885487) B1885487
theorem B30584465 : Blo 1256446 30584465 := bstep (se 2 (by rfl) ⟨11469174, by rfl⟩ : syracuseStep 30584465 = 22938349) B22938349
theorem B1257127 : Blo 1256446 1257127 := bstep (se 1 (by rfl) ⟨942845, by rfl⟩ : syracuseStep 1257127 = 1885691) B1885691
theorem B65326763 : Blo 1256446 65326763 := bstep (se 1 (by rfl) ⟨48995072, by rfl⟩ : syracuseStep 65326763 = 97990145) B97990145
theorem B1257151 : Blo 1256446 1257151 := bstep (se 1 (by rfl) ⟨942863, by rfl⟩ : syracuseStep 1257151 = 1885727) B1885727
theorem B1257247 : Blo 1256446 1257247 := bstep (se 1 (by rfl) ⟨942935, by rfl⟩ : syracuseStep 1257247 = 1885871) B1885871
theorem B20377441 : Blo 1256446 20377441 := bstep (se 2 (by rfl) ⟨7641540, by rfl⟩ : syracuseStep 20377441 = 15283081) B15283081
theorem B1257327 : Blo 1256446 1257327 := bstep (se 1 (by rfl) ⟨942995, by rfl⟩ : syracuseStep 1257327 = 1885991) B1885991
theorem B2830319 : Blo 1256446 2830319 := bstep (se 1 (by rfl) ⟨2122739, by rfl⟩ : syracuseStep 2830319 = 4245479) B4245479
theorem B7254035 : Blo 1256446 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B4771943 : Blo 1256446 4771943 := bstep (se 1 (by rfl) ⟨3578957, by rfl⟩ : syracuseStep 4771943 = 7157915) B7157915
theorem B1257695 : Blo 1256446 1257695 := bstep (se 1 (by rfl) ⟨943271, by rfl⟩ : syracuseStep 1257695 = 1886543) B1886543
theorem B1257727 : Blo 1256446 1257727 := bstep (se 1 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 1257727 = 1886591) B1886591
theorem B1257755 : Blo 1256446 1257755 := bstep (se 1 (by rfl) ⟨943316, by rfl⟩ : syracuseStep 1257755 = 1886633) B1886633
theorem B2388295 : Blo 1256446 2388295 := bstep (se 1 (by rfl) ⟨1791221, by rfl⟩ : syracuseStep 2388295 = 3582443) B3582443
theorem B4026763 : Blo 1256446 4026763 := bstep (se 1 (by rfl) ⟨3020072, by rfl⟩ : syracuseStep 4026763 = 6040145) B6040145
theorem B13603261 : Blo 1256446 13603261 := bstep (se 3 (by rfl) ⟨2550611, by rfl⟩ : syracuseStep 13603261 = 5101223) B5101223
theorem B1258011 : Blo 1256446 1258011 := bstep (se 1 (by rfl) ⟨943508, by rfl⟩ : syracuseStep 1258011 = 1887017) B1887017
theorem B1413679 : Blo 1256446 1413679 := bstep (se 1 (by rfl) ⟨1060259, by rfl⟩ : syracuseStep 1413679 = 2120519) B2120519
theorem B7164521 : Blo 1256446 7164521 := bstep (se 2 (by rfl) ⟨2686695, by rfl⟩ : syracuseStep 7164521 = 5373391) B5373391
theorem B1258151 : Blo 1256446 1258151 := bstep (se 1 (by rfl) ⟨943613, by rfl⟩ : syracuseStep 1258151 = 1887227) B1887227
theorem B1258191 : Blo 1256446 1258191 := bstep (se 1 (by rfl) ⟨943643, by rfl⟩ : syracuseStep 1258191 = 1887287) B1887287
theorem B8057627 : Blo 1256446 8057627 := bstep (se 1 (by rfl) ⟨6043220, by rfl⟩ : syracuseStep 8057627 = 12086441) B12086441
theorem B1258271 : Blo 1256446 1258271 := bstep (se 1 (by rfl) ⟨943703, by rfl⟩ : syracuseStep 1258271 = 1887407) B1887407
theorem B2388827 : Blo 1256446 2388827 := bstep (se 1 (by rfl) ⟨1791620, by rfl⟩ : syracuseStep 2388827 = 3583241) B3583241
theorem B1790857 : Blo 1256446 1790857 := bstep (se 2 (by rfl) ⟨671571, by rfl⟩ : syracuseStep 1790857 = 1343143) B1343143
theorem B1414255 : Blo 1256446 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B33092813 : Blo 1256446 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B7156957 : Blo 1256446 7156957 := bstep (se 3 (by rfl) ⟨1341929, by rfl⟩ : syracuseStep 7156957 = 2683859) B2683859
theorem B3822815 : Blo 1256446 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B6797135 : Blo 1256446 6797135 := bstep (se 1 (by rfl) ⟨5097851, by rfl⟩ : syracuseStep 6797135 = 10195703) B10195703
theorem B3184505 : Blo 1256446 3184505 := bstep (se 2 (by rfl) ⟨1194189, by rfl⟩ : syracuseStep 3184505 = 2388379) B2388379
theorem B24508615 : Blo 1256446 24508615 := bstep (se 1 (by rfl) ⟨18381461, by rfl⟩ : syracuseStep 24508615 = 36762923) B36762923
theorem B11466983 : Blo 1256446 11466983 := bstep (se 1 (by rfl) ⟨8600237, by rfl⟩ : syracuseStep 11466983 = 17200475) B17200475
theorem B1006319863 : Blo 1256446 1006319863 := bstep (se 1 (by rfl) ⟨754739897, by rfl⟩ : syracuseStep 1006319863 = 1509479795) B1509479795
theorem B3226159 : Blo 1256446 3226159 := bstep (se 1 (by rfl) ⟨2419619, by rfl⟩ : syracuseStep 3226159 = 4839239) B4839239
theorem B4774571 : Blo 1256446 4774571 := bstep (se 1 (by rfl) ⟨3580928, by rfl⟩ : syracuseStep 4774571 = 7161857) B7161857
theorem B3578593 : Blo 1256446 3578593 := bstep (se 2 (by rfl) ⟨1341972, by rfl⟩ : syracuseStep 3578593 = 2683945) B2683945
theorem B3021563 : Blo 1256446 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B3824615 : Blo 1256446 3824615 := bstep (se 1 (by rfl) ⟨2868461, by rfl⟩ : syracuseStep 3824615 = 5736923) B5736923
theorem B2120809 : Blo 1256446 2120809 := bstep (se 2 (by rfl) ⟨795303, by rfl⟩ : syracuseStep 2120809 = 1590607) B1590607
theorem B13073537 : Blo 1256446 13073537 := bstep (se 2 (by rfl) ⟨4902576, by rfl⟩ : syracuseStep 13073537 = 9805153) B9805153
theorem B2014535 : Blo 1256446 2014535 := bstep (se 1 (by rfl) ⟨1510901, by rfl⟩ : syracuseStep 2014535 = 3021803) B3021803
theorem B24165803 : Blo 1256446 24165803 := bstep (se 1 (by rfl) ⟨18124352, by rfl⟩ : syracuseStep 24165803 = 36248705) B36248705
theorem B9551357 : Blo 1256446 9551357 := bstep (se 3 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 9551357 = 3581759) B3581759
theorem B81551285 : Blo 1256446 81551285 := bstep (se 5 (by rfl) ⟨3822716, by rfl⟩ : syracuseStep 81551285 = 7645433) B7645433
theorem B32678153 : Blo 1256446 32678153 := bstep (se 2 (by rfl) ⟨12254307, by rfl⟩ : syracuseStep 32678153 = 24508615) B24508615
theorem B1341759817 : Blo 1256446 1341759817 := bstep (se 2 (by rfl) ⟨503159931, by rfl⟩ : syracuseStep 1341759817 = 1006319863) B1006319863
theorem B4776347 : Blo 1256446 4776347 := bstep (se 1 (by rfl) ⟨3582260, by rfl⟩ : syracuseStep 4776347 = 7164521) B7164521
theorem B7160399 : Blo 1256446 7160399 := bstep (se 1 (by rfl) ⟨5370299, by rfl⟩ : syracuseStep 7160399 = 10740599) B10740599
theorem B4776529 : Blo 1256446 4776529 := bstep (se 2 (by rfl) ⟨1791198, by rfl⟩ : syracuseStep 4776529 = 3582397) B3582397
theorem B18137681 : Blo 1256446 18137681 := bstep (se 2 (by rfl) ⟨6801630, by rfl⟩ : syracuseStep 18137681 = 13603261) B13603261
theorem B1884905 : Blo 1256446 1884905 := bstep (se 2 (by rfl) ⟨706839, by rfl⟩ : syracuseStep 1884905 = 1413679) B1413679
theorem B4301545 : Blo 1256446 4301545 := bstep (se 2 (by rfl) ⟨1613079, by rfl⟩ : syracuseStep 4301545 = 3226159) B3226159
theorem B32687279 : Blo 1256446 32687279 := bstep (se 1 (by rfl) ⟨24515459, by rfl⟩ : syracuseStep 32687279 = 49030919) B49030919
theorem B4531423 : Blo 1256446 4531423 := bstep (se 1 (by rfl) ⟨3398567, by rfl⟩ : syracuseStep 4531423 = 6797135) B6797135
theorem B2123003 : Blo 1256446 2123003 := bstep (se 1 (by rfl) ⟨1592252, by rfl⟩ : syracuseStep 2123003 = 3184505) B3184505
theorem B4777289 : Blo 1256446 4777289 := bstep (se 2 (by rfl) ⟨1791483, by rfl⟩ : syracuseStep 4777289 = 3582967) B3582967
theorem B2827745 : Blo 1256446 2827745 := bstep (se 2 (by rfl) ⟨1060404, by rfl⟩ : syracuseStep 2827745 = 2120809) B2120809
theorem B1885673 : Blo 1256446 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B7644655 : Blo 1256446 7644655 := bstep (se 1 (by rfl) ⟨5733491, by rfl⟩ : syracuseStep 7644655 = 11466983) B11466983
theorem B1885751 : Blo 1256446 1885751 := bstep (se 1 (by rfl) ⟨1414313, by rfl⟩ : syracuseStep 1885751 = 2828627) B2828627
theorem B18138887 : Blo 1256446 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B174204701 : Blo 1256446 174204701 := bstep (se 3 (by rfl) ⟨32663381, by rfl⟩ : syracuseStep 174204701 = 65326763) B65326763
theorem B1886111 : Blo 1256446 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B77449223 : Blo 1256446 77449223 := bstep (se 1 (by rfl) ⟨58086917, by rfl⟩ : syracuseStep 77449223 = 116173835) B116173835
theorem B41314349 : Blo 1256446 41314349 := bstep (se 3 (by rfl) ⟨7746440, by rfl⟩ : syracuseStep 41314349 = 15492881) B15492881
theorem B1886279 : Blo 1256446 1886279 := bstep (se 1 (by rfl) ⟨1414709, by rfl⟩ : syracuseStep 1886279 = 2829419) B2829419
theorem B3180667 : Blo 1256446 3180667 := bstep (se 1 (by rfl) ⟨2385500, by rfl⟩ : syracuseStep 3180667 = 4771001) B4771001
theorem B1886459 : Blo 1256446 1886459 := bstep (se 1 (by rfl) ⟨1414844, by rfl⟩ : syracuseStep 1886459 = 2829689) B2829689
theorem B6367571 : Blo 1256446 6367571 := bstep (se 1 (by rfl) ⟨4775678, by rfl⟩ : syracuseStep 6367571 = 9551357) B9551357
theorem B1886879 : Blo 1256446 1886879 := bstep (se 1 (by rfl) ⟨1415159, by rfl⟩ : syracuseStep 1886879 = 2830319) B2830319
theorem B4836023 : Blo 1256446 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B3181295 : Blo 1256446 3181295 := bstep (se 1 (by rfl) ⟨2385971, by rfl⟩ : syracuseStep 3181295 = 4771943) B4771943
theorem B10750745 : Blo 1256446 10750745 := bstep (se 2 (by rfl) ⟨4031529, by rfl⟩ : syracuseStep 10750745 = 8063059) B8063059
theorem B2829113 : Blo 1256446 2829113 := bstep (se 2 (by rfl) ⟨1060917, by rfl⟩ : syracuseStep 2829113 = 2121835) B2121835
theorem B2550619 : Blo 1256446 2550619 := bstep (se 1 (by rfl) ⟨1912964, by rfl⟩ : syracuseStep 2550619 = 3825929) B3825929
theorem B4304009 : Blo 1256446 4304009 := bstep (se 2 (by rfl) ⟨1614003, by rfl⟩ : syracuseStep 4304009 = 3228007) B3228007
theorem B2829473 : Blo 1256446 2829473 := bstep (se 2 (by rfl) ⟨1061052, by rfl⟩ : syracuseStep 2829473 = 2122105) B2122105
theorem B1256615 : Blo 1256446 1256615 := bstep (se 1 (by rfl) ⟨942461, by rfl⟩ : syracuseStep 1256615 = 1884923) B1884923
theorem B5369017 : Blo 1256446 5369017 := bstep (se 2 (by rfl) ⟨2013381, by rfl⟩ : syracuseStep 5369017 = 4026763) B4026763
theorem B88247501 : Blo 1256446 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B1592551 : Blo 1256446 1592551 := bstep (se 1 (by rfl) ⟨1194413, by rfl⟩ : syracuseStep 1592551 = 2388827) B2388827
theorem B10194173 : Blo 1256446 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B1256911 : Blo 1256446 1256911 := bstep (se 1 (by rfl) ⟨942683, by rfl⟩ : syracuseStep 1256911 = 1885367) B1885367
theorem B1257007 : Blo 1256446 1257007 := bstep (se 1 (by rfl) ⟨942755, by rfl⟩ : syracuseStep 1257007 = 1885511) B1885511
theorem B1257071 : Blo 1256446 1257071 := bstep (se 1 (by rfl) ⟨942803, by rfl⟩ : syracuseStep 1257071 = 1885607) B1885607
theorem B4771457 : Blo 1256446 4771457 := bstep (se 2 (by rfl) ⟨1789296, by rfl⟩ : syracuseStep 4771457 = 3578593) B3578593
theorem B1257191 : Blo 1256446 1257191 := bstep (se 1 (by rfl) ⟨942893, by rfl⟩ : syracuseStep 1257191 = 1885787) B1885787
theorem B2387809 : Blo 1256446 2387809 := bstep (se 2 (by rfl) ⟨895428, by rfl⟩ : syracuseStep 2387809 = 1790857) B1790857
theorem B26144731 : Blo 1256446 26144731 := bstep (se 1 (by rfl) ⟨19608548, by rfl⟩ : syracuseStep 26144731 = 39217097) B39217097
theorem B1257503 : Blo 1256446 1257503 := bstep (se 1 (by rfl) ⟨943127, by rfl⟩ : syracuseStep 1257503 = 1886255) B1886255
theorem B10743911 : Blo 1256446 10743911 := bstep (se 1 (by rfl) ⟨8057933, by rfl⟩ : syracuseStep 10743911 = 16115867) B16115867
theorem B2388143 : Blo 1256446 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B1257679 : Blo 1256446 1257679 := bstep (se 1 (by rfl) ⟨943259, by rfl⟩ : syracuseStep 1257679 = 1886519) B1886519
theorem B1257799 : Blo 1256446 1257799 := bstep (se 1 (by rfl) ⟨943349, by rfl⟩ : syracuseStep 1257799 = 1886699) B1886699
theorem B3183047 : Blo 1256446 3183047 := bstep (se 1 (by rfl) ⟨2387285, by rfl⟩ : syracuseStep 3183047 = 4774571) B4774571
theorem B1257959 : Blo 1256446 1257959 := bstep (se 1 (by rfl) ⟨943469, by rfl⟩ : syracuseStep 1257959 = 1886939) B1886939
theorem B6361577 : Blo 1256446 6361577 := bstep (se 2 (by rfl) ⟨2385591, by rfl⟩ : syracuseStep 6361577 = 4771183) B4771183
theorem B1257983 : Blo 1256446 1257983 := bstep (se 1 (by rfl) ⟨943487, by rfl⟩ : syracuseStep 1257983 = 1886975) B1886975
theorem B9056873 : Blo 1256446 9056873 := bstep (se 2 (by rfl) ⟨3396327, by rfl⟩ : syracuseStep 9056873 = 6792655) B6792655
theorem B8057501 : Blo 1256446 8057501 := bstep (se 3 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 8057501 = 3021563) B3021563
theorem B16110535 : Blo 1256446 16110535 := bstep (se 1 (by rfl) ⟨12082901, by rfl⟩ : syracuseStep 16110535 = 24165803) B24165803
theorem B181343245 : Blo 1256446 181343245 := bstep (se 3 (by rfl) ⟨34001858, by rfl⟩ : syracuseStep 181343245 = 68003717) B68003717
theorem B27169921 : Blo 1256446 27169921 := bstep (se 2 (by rfl) ⟨10188720, by rfl⟩ : syracuseStep 27169921 = 20377441) B20377441
theorem B54367523 : Blo 1256446 54367523 := bstep (se 1 (by rfl) ⟨40775642, by rfl⟩ : syracuseStep 54367523 = 81551285) B81551285
theorem B14333597 : Blo 1256446 14333597 := bstep (se 3 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 14333597 = 5375099) B5375099
theorem B314136305 : Blo 1256446 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B3184393 : Blo 1256446 3184393 := bstep (se 2 (by rfl) ⟨1194147, by rfl⟩ : syracuseStep 3184393 = 2388295) B2388295
theorem B4241213 : Blo 1256446 4241213 := bstep (se 3 (by rfl) ⟨795227, by rfl⟩ : syracuseStep 4241213 = 1590455) B1590455
theorem B8271713 : Blo 1256446 8271713 := bstep (se 2 (by rfl) ⟨3101892, by rfl⟩ : syracuseStep 8271713 = 6203785) B6203785
theorem B5371751 : Blo 1256446 5371751 := bstep (se 1 (by rfl) ⟨4028813, by rfl⟩ : syracuseStep 5371751 = 8057627) B8057627
theorem B6363035 : Blo 1256446 6363035 := bstep (se 1 (by rfl) ⟨4772276, by rfl⟩ : syracuseStep 6363035 = 9544553) B9544553
theorem B24500495 : Blo 1256446 24500495 := bstep (se 1 (by rfl) ⟨18375371, by rfl⟩ : syracuseStep 24500495 = 36750743) B36750743
theorem B1415551 : Blo 1256446 1415551 := bstep (se 1 (by rfl) ⟨1061663, by rfl⟩ : syracuseStep 1415551 = 2123327) B2123327
theorem B3185183 : Blo 1256446 3185183 := bstep (se 1 (by rfl) ⟨2388887, by rfl⟩ : syracuseStep 3185183 = 4777775) B4777775
theorem B9542609 : Blo 1256446 9542609 := bstep (se 2 (by rfl) ⟨3578478, by rfl⟩ : syracuseStep 9542609 = 7156957) B7156957
theorem B3578843 : Blo 1256446 3578843 := bstep (se 1 (by rfl) ⟨2684132, by rfl⟩ : syracuseStep 3578843 = 5368265) B5368265
theorem B2120735 : Blo 1256446 2120735 := bstep (se 1 (by rfl) ⟨1590551, by rfl⟩ : syracuseStep 2120735 = 3181103) B3181103
theorem B8715691 : Blo 1256446 8715691 := bstep (se 1 (by rfl) ⟨6536768, by rfl⟩ : syracuseStep 8715691 = 13073537) B13073537
theorem B2121167 : Blo 1256446 2121167 := bstep (se 1 (by rfl) ⟨1590875, by rfl⟩ : syracuseStep 2121167 = 3181751) B3181751
theorem B1343023 : Blo 1256446 1343023 := bstep (se 1 (by rfl) ⟨1007267, by rfl⟩ : syracuseStep 1343023 = 2014535) B2014535
theorem B20389643 : Blo 1256446 20389643 := bstep (se 1 (by rfl) ⟨15292232, by rfl⟩ : syracuseStep 20389643 = 30584465) B30584465
theorem B10198973 : Blo 1256446 10198973 := bstep (se 3 (by rfl) ⟨1912307, by rfl⟩ : syracuseStep 10198973 = 3824615) B3824615
theorem B2122031 : Blo 1256446 2122031 := bstep (se 1 (by rfl) ⟨1591523, by rfl⟩ : syracuseStep 2122031 = 3183047) B3183047
theorem B12091787 : Blo 1256446 12091787 := bstep (se 1 (by rfl) ⟨9068840, by rfl⟩ : syracuseStep 12091787 = 18137681) B18137681
theorem B6037915 : Blo 1256446 6037915 := bstep (se 1 (by rfl) ⟨4528436, by rfl⟩ : syracuseStep 6037915 = 9056873) B9056873
theorem B21791519 : Blo 1256446 21791519 := bstep (se 1 (by rfl) ⟨16343639, by rfl⟩ : syracuseStep 21791519 = 32687279) B32687279
theorem B5735393 : Blo 1256446 5735393 := bstep (se 2 (by rfl) ⟨2150772, by rfl⟩ : syracuseStep 5735393 = 4301545) B4301545
theorem B1885163 : Blo 1256446 1885163 := bstep (se 1 (by rfl) ⟨1413872, by rfl⟩ : syracuseStep 1885163 = 2827745) B2827745
theorem B12092591 : Blo 1256446 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B2827475 : Blo 1256446 2827475 := bstep (se 1 (by rfl) ⟨2120606, by rfl⟩ : syracuseStep 2827475 = 4241213) B4241213
theorem B5514475 : Blo 1256446 5514475 := bstep (se 1 (by rfl) ⟨4135856, by rfl⟩ : syracuseStep 5514475 = 8271713) B8271713
theorem B3581167 : Blo 1256446 3581167 := bstep (se 1 (by rfl) ⟨2685875, by rfl⟩ : syracuseStep 3581167 = 5371751) B5371751
theorem B21480713 : Blo 1256446 21480713 := bstep (se 2 (by rfl) ⟨8055267, by rfl⟩ : syracuseStep 21480713 = 16110535) B16110535
theorem B27542899 : Blo 1256446 27542899 := bstep (se 1 (by rfl) ⟨20657174, by rfl⟩ : syracuseStep 27542899 = 41314349) B41314349
theorem B36226561 : Blo 1256446 36226561 := bstep (se 2 (by rfl) ⟨13584960, by rfl⟩ : syracuseStep 36226561 = 27169921) B27169921
theorem B4245047 : Blo 1256446 4245047 := bstep (se 1 (by rfl) ⟨3183785, by rfl⟩ : syracuseStep 4245047 = 6367571) B6367571
theorem B2123401 : Blo 1256446 2123401 := bstep (se 2 (by rfl) ⟨796275, by rfl⟩ : syracuseStep 2123401 = 1592551) B1592551
theorem B2123455 : Blo 1256446 2123455 := bstep (se 1 (by rfl) ⟨1592591, by rfl⟩ : syracuseStep 2123455 = 3185183) B3185183
theorem B1886075 : Blo 1256446 1886075 := bstep (se 1 (by rfl) ⟨1414556, by rfl⟩ : syracuseStep 1886075 = 2829113) B2829113
theorem B10192873 : Blo 1256446 10192873 := bstep (se 2 (by rfl) ⟨3822327, by rfl⟩ : syracuseStep 10192873 = 7644655) B7644655
theorem B2869339 : Blo 1256446 2869339 := bstep (se 1 (by rfl) ⟨2152004, by rfl⟩ : syracuseStep 2869339 = 4304009) B4304009
theorem B1886315 : Blo 1256446 1886315 := bstep (se 1 (by rfl) ⟨1414736, by rfl⟩ : syracuseStep 1886315 = 2829473) B2829473
theorem B4245857 : Blo 1256446 4245857 := bstep (se 2 (by rfl) ⟨1592196, by rfl⟩ : syracuseStep 4245857 = 3184393) B3184393
theorem B3180971 : Blo 1256446 3180971 := bstep (se 1 (by rfl) ⟨2385728, by rfl⟩ : syracuseStep 3180971 = 4771457) B4771457
theorem B13593095 : Blo 1256446 13593095 := bstep (se 1 (by rfl) ⟨10194821, by rfl⟩ : syracuseStep 13593095 = 20389643) B20389643
theorem B34859641 : Blo 1256446 34859641 := bstep (se 2 (by rfl) ⟨13072365, by rfl⟩ : syracuseStep 34859641 = 26144731) B26144731
theorem B7162607 : Blo 1256446 7162607 := bstep (se 1 (by rfl) ⟨5371955, by rfl⟩ : syracuseStep 7162607 = 10743911) B10743911
theorem B21785435 : Blo 1256446 21785435 := bstep (se 1 (by rfl) ⟨16339076, by rfl⟩ : syracuseStep 21785435 = 32678153) B32678153
theorem B7162789 : Blo 1256446 7162789 := bstep (se 4 (by rfl) ⟨671511, by rfl⟩ : syracuseStep 7162789 = 1343023) B1343023
theorem B1789013089 : Blo 1256446 1789013089 := bstep (se 2 (by rfl) ⟨670879908, by rfl⟩ : syracuseStep 1789013089 = 1341759817) B1341759817
theorem B6368381 : Blo 1256446 6368381 := bstep (se 3 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 6368381 = 2388143) B2388143
theorem B1256603 : Blo 1256446 1256603 := bstep (se 1 (by rfl) ⟨942452, by rfl⟩ : syracuseStep 1256603 = 1884905) B1884905
theorem B1887401 : Blo 1256446 1887401 := bstep (se 2 (by rfl) ⟨707775, by rfl⟩ : syracuseStep 1887401 = 1415551) B1415551
theorem B6368705 : Blo 1256446 6368705 := bstep (se 2 (by rfl) ⟨2388264, by rfl⟩ : syracuseStep 6368705 = 4776529) B4776529
theorem B36245015 : Blo 1256446 36245015 := bstep (se 1 (by rfl) ⟨27183761, by rfl⟩ : syracuseStep 36245015 = 54367523) B54367523
theorem B1257115 : Blo 1256446 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B1257167 : Blo 1256446 1257167 := bstep (se 1 (by rfl) ⟨942875, by rfl⟩ : syracuseStep 1257167 = 1885751) B1885751
theorem B9555731 : Blo 1256446 9555731 := bstep (se 1 (by rfl) ⟨7166798, by rfl⟩ : syracuseStep 9555731 = 14333597) B14333597
theorem B209424203 : Blo 1256446 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B1257407 : Blo 1256446 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B241790993 : Blo 1256446 241790993 := bstep (se 2 (by rfl) ⟨90671622, by rfl⟩ : syracuseStep 241790993 = 181343245) B181343245
theorem B1257519 : Blo 1256446 1257519 := bstep (se 1 (by rfl) ⟨943139, by rfl⟩ : syracuseStep 1257519 = 1886279) B1886279
theorem B1257639 : Blo 1256446 1257639 := bstep (se 1 (by rfl) ⟨943229, by rfl⟩ : syracuseStep 1257639 = 1886459) B1886459
theorem B6041897 : Blo 1256446 6041897 := bstep (se 2 (by rfl) ⟨2265711, by rfl⟩ : syracuseStep 6041897 = 4531423) B4531423
theorem B1257919 : Blo 1256446 1257919 := bstep (se 1 (by rfl) ⟨943439, by rfl⟩ : syracuseStep 1257919 = 1886879) B1886879
theorem B3224015 : Blo 1256446 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B13603301 : Blo 1256446 13603301 := bstep (se 4 (by rfl) ⟨1275309, by rfl⟩ : syracuseStep 13603301 = 2550619) B2550619
theorem B11620921 : Blo 1256446 11620921 := bstep (se 2 (by rfl) ⟨4357845, by rfl⟩ : syracuseStep 11620921 = 8715691) B8715691
theorem B6361739 : Blo 1256446 6361739 := bstep (se 1 (by rfl) ⟨4771304, by rfl⟩ : syracuseStep 6361739 = 9542609) B9542609
theorem B1413823 : Blo 1256446 1413823 := bstep (se 1 (by rfl) ⟨1060367, by rfl⟩ : syracuseStep 1413823 = 2120735) B2120735
theorem B58831667 : Blo 1256446 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B6796115 : Blo 1256446 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B1414111 : Blo 1256446 1414111 := bstep (se 1 (by rfl) ⟨1060583, by rfl⟩ : syracuseStep 1414111 = 2121167) B2121167
theorem B3183745 : Blo 1256446 3183745 := bstep (se 2 (by rfl) ⟨1193904, by rfl⟩ : syracuseStep 3183745 = 2387809) B2387809
theorem B4240889 : Blo 1256446 4240889 := bstep (se 2 (by rfl) ⟨1590333, by rfl⟩ : syracuseStep 4240889 = 3180667) B3180667
theorem B3184231 : Blo 1256446 3184231 := bstep (se 1 (by rfl) ⟨2388173, by rfl⟩ : syracuseStep 3184231 = 4776347) B4776347
theorem B4241051 : Blo 1256446 4241051 := bstep (se 1 (by rfl) ⟨3180788, by rfl⟩ : syracuseStep 4241051 = 6361577) B6361577
theorem B4773599 : Blo 1256446 4773599 := bstep (se 1 (by rfl) ⟨3580199, by rfl⟩ : syracuseStep 4773599 = 7160399) B7160399
theorem B5371667 : Blo 1256446 5371667 := bstep (se 1 (by rfl) ⟨4028750, by rfl⟩ : syracuseStep 5371667 = 8057501) B8057501
theorem B1415335 : Blo 1256446 1415335 := bstep (se 1 (by rfl) ⟨1061501, by rfl⟩ : syracuseStep 1415335 = 2123003) B2123003
theorem B3184859 : Blo 1256446 3184859 := bstep (se 1 (by rfl) ⟨2388644, by rfl⟩ : syracuseStep 3184859 = 4777289) B4777289
theorem B116136467 : Blo 1256446 116136467 := bstep (se 1 (by rfl) ⟨87102350, by rfl⟩ : syracuseStep 116136467 = 174204701) B174204701
theorem B4242023 : Blo 1256446 4242023 := bstep (se 1 (by rfl) ⟨3181517, by rfl⟩ : syracuseStep 4242023 = 6363035) B6363035
theorem B51632815 : Blo 1256446 51632815 := bstep (se 1 (by rfl) ⟨38724611, by rfl⟩ : syracuseStep 51632815 = 77449223) B77449223
theorem B16333663 : Blo 1256446 16333663 := bstep (se 1 (by rfl) ⟨12250247, by rfl⟩ : syracuseStep 16333663 = 24500495) B24500495
theorem B7158689 : Blo 1256446 7158689 := bstep (se 2 (by rfl) ⟨2684508, by rfl⟩ : syracuseStep 7158689 = 5369017) B5369017
theorem B2120863 : Blo 1256446 2120863 := bstep (se 1 (by rfl) ⟨1590647, by rfl⟩ : syracuseStep 2120863 = 3181295) B3181295
theorem B7167163 : Blo 1256446 7167163 := bstep (se 1 (by rfl) ⟨5375372, by rfl⟩ : syracuseStep 7167163 = 10750745) B10750745
theorem B9543581 : Blo 1256446 9543581 := bstep (se 3 (by rfl) ⟨1789421, by rfl⟩ : syracuseStep 9543581 = 3578843) B3578843
theorem B6799315 : Blo 1256446 6799315 := bstep (se 1 (by rfl) ⟨5099486, by rfl⟩ : syracuseStep 6799315 = 10198973) B10198973
theorem B161193995 : Blo 1256446 161193995 := bstep (se 1 (by rfl) ⟨120895496, by rfl⟩ : syracuseStep 161193995 = 241790993) B241790993
theorem B3825785 : Blo 1256446 3825785 := bstep (se 2 (by rfl) ⟨1434669, by rfl⟩ : syracuseStep 3825785 = 2869339) B2869339
theorem B8061191 : Blo 1256446 8061191 := bstep (se 1 (by rfl) ⟨6045893, by rfl⟩ : syracuseStep 8061191 = 12091787) B12091787
theorem B9068867 : Blo 1256446 9068867 := bstep (se 1 (by rfl) ⟨6801650, by rfl⟩ : syracuseStep 9068867 = 13603301) B13603301
theorem B4530743 : Blo 1256446 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B8061727 : Blo 1256446 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B1884983 : Blo 1256446 1884983 := bstep (se 1 (by rfl) ⟨1413737, by rfl⟩ : syracuseStep 1884983 = 2827475) B2827475
theorem B14320475 : Blo 1256446 14320475 := bstep (se 1 (by rfl) ⟨10740356, by rfl⟩ : syracuseStep 14320475 = 21480713) B21480713
theorem B1885097 : Blo 1256446 1885097 := bstep (se 2 (by rfl) ⟨706911, by rfl⟩ : syracuseStep 1885097 = 1413823) B1413823
theorem B2827259 : Blo 1256446 2827259 := bstep (se 1 (by rfl) ⟨2120444, by rfl⟩ : syracuseStep 2827259 = 4240889) B4240889
theorem B2827367 : Blo 1256446 2827367 := bstep (se 1 (by rfl) ⟨2120525, by rfl⟩ : syracuseStep 2827367 = 4241051) B4241051
theorem B3581111 : Blo 1256446 3581111 := bstep (se 1 (by rfl) ⟨2685833, by rfl⟩ : syracuseStep 3581111 = 5371667) B5371667
theorem B1885481 : Blo 1256446 1885481 := bstep (se 2 (by rfl) ⟨707055, by rfl⟩ : syracuseStep 1885481 = 1414111) B1414111
theorem B2123239 : Blo 1256446 2123239 := bstep (se 1 (by rfl) ⟨1592429, by rfl⟩ : syracuseStep 2123239 = 3184859) B3184859
theorem B4244993 : Blo 1256446 4244993 := bstep (se 2 (by rfl) ⟨1591872, by rfl⟩ : syracuseStep 4244993 = 3183745) B3183745
theorem B2827817 : Blo 1256446 2827817 := bstep (se 2 (by rfl) ⟨1060431, by rfl⟩ : syracuseStep 2827817 = 2120863) B2120863
theorem B9062063 : Blo 1256446 9062063 := bstep (se 1 (by rfl) ⟨6796547, by rfl⟩ : syracuseStep 9062063 = 13593095) B13593095
theorem B77424311 : Blo 1256446 77424311 := bstep (se 1 (by rfl) ⟨58068233, by rfl⟩ : syracuseStep 77424311 = 116136467) B116136467
theorem B2828015 : Blo 1256446 2828015 := bstep (se 1 (by rfl) ⟨2121011, by rfl⟩ : syracuseStep 2828015 = 4242023) B4242023
theorem B48302081 : Blo 1256446 48302081 := bstep (se 2 (by rfl) ⟨18113280, by rfl⟩ : syracuseStep 48302081 = 36226561) B36226561
theorem B4245587 : Blo 1256446 4245587 := bstep (se 1 (by rfl) ⟨3184190, by rfl⟩ : syracuseStep 4245587 = 6368381) B6368381
theorem B4245641 : Blo 1256446 4245641 := bstep (se 2 (by rfl) ⟨1592115, by rfl⟩ : syracuseStep 4245641 = 3184231) B3184231
theorem B4245803 : Blo 1256446 4245803 := bstep (se 1 (by rfl) ⟨3184352, by rfl⟩ : syracuseStep 4245803 = 6368705) B6368705
theorem B1887113 : Blo 1256446 1887113 := bstep (se 2 (by rfl) ⟨707667, by rfl⟩ : syracuseStep 1887113 = 1415335) B1415335
theorem B2149343 : Blo 1256446 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B14527679 : Blo 1256446 14527679 := bstep (se 1 (by rfl) ⟨10895759, by rfl⟩ : syracuseStep 14527679 = 21791519) B21791519
theorem B1256775 : Blo 1256446 1256775 := bstep (se 1 (by rfl) ⟨942581, by rfl⟩ : syracuseStep 1256775 = 1885163) B1885163
theorem B15494561 : Blo 1256446 15494561 := bstep (se 2 (by rfl) ⟨5810460, by rfl⟩ : syracuseStep 15494561 = 11620921) B11620921
theorem B2830031 : Blo 1256446 2830031 := bstep (se 1 (by rfl) ⟨2122523, by rfl⟩ : syracuseStep 2830031 = 4245047) B4245047
theorem B21778217 : Blo 1256446 21778217 := bstep (se 2 (by rfl) ⟨8166831, by rfl⟩ : syracuseStep 21778217 = 16333663) B16333663
theorem B3182399 : Blo 1256446 3182399 := bstep (se 1 (by rfl) ⟨2386799, by rfl⟩ : syracuseStep 3182399 = 4773599) B4773599
theorem B1257383 : Blo 1256446 1257383 := bstep (se 1 (by rfl) ⟨943037, by rfl⟩ : syracuseStep 1257383 = 1886075) B1886075
theorem B1257543 : Blo 1256446 1257543 := bstep (se 1 (by rfl) ⟨943157, by rfl⟩ : syracuseStep 1257543 = 1886315) B1886315
theorem B2385350785 : Blo 1256446 2385350785 := bstep (se 2 (by rfl) ⟨894506544, by rfl⟩ : syracuseStep 2385350785 = 1789013089) B1789013089
theorem B2830571 : Blo 1256446 2830571 := bstep (se 1 (by rfl) ⟨2122928, by rfl⟩ : syracuseStep 2830571 = 4245857) B4245857
theorem B9556217 : Blo 1256446 9556217 := bstep (se 2 (by rfl) ⟨3583581, by rfl⟩ : syracuseStep 9556217 = 7167163) B7167163
theorem B7352633 : Blo 1256446 7352633 := bstep (se 2 (by rfl) ⟨2757237, by rfl⟩ : syracuseStep 7352633 = 5514475) B5514475
theorem B4772459 : Blo 1256446 4772459 := bstep (se 1 (by rfl) ⟨3579344, by rfl⟩ : syracuseStep 4772459 = 7158689) B7158689
theorem B1258267 : Blo 1256446 1258267 := bstep (se 1 (by rfl) ⟨943700, by rfl⟩ : syracuseStep 1258267 = 1887401) B1887401
theorem B2831201 : Blo 1256446 2831201 := bstep (se 2 (by rfl) ⟨1061700, by rfl⟩ : syracuseStep 2831201 = 2123401) B2123401
theorem B2831273 : Blo 1256446 2831273 := bstep (se 2 (by rfl) ⟨1061727, by rfl⟩ : syracuseStep 2831273 = 2123455) B2123455
theorem B24163343 : Blo 1256446 24163343 := bstep (se 1 (by rfl) ⟨18122507, by rfl⟩ : syracuseStep 24163343 = 36245015) B36245015
theorem B6370487 : Blo 1256446 6370487 := bstep (se 1 (by rfl) ⟨4777865, by rfl⟩ : syracuseStep 6370487 = 9555731) B9555731
theorem B6362387 : Blo 1256446 6362387 := bstep (se 1 (by rfl) ⟨4771790, by rfl⟩ : syracuseStep 6362387 = 9543581) B9543581
theorem B9065753 : Blo 1256446 9065753 := bstep (se 2 (by rfl) ⟨3399657, by rfl⟩ : syracuseStep 9065753 = 6799315) B6799315
theorem B4027931 : Blo 1256446 4027931 := bstep (se 1 (by rfl) ⟨3020948, by rfl⟩ : syracuseStep 4027931 = 6041897) B6041897
theorem B1414687 : Blo 1256446 1414687 := bstep (se 1 (by rfl) ⟨1061015, by rfl⟩ : syracuseStep 1414687 = 2122031) B2122031
theorem B4241159 : Blo 1256446 4241159 := bstep (se 1 (by rfl) ⟨3180869, by rfl⟩ : syracuseStep 4241159 = 6361739) B6361739
theorem B39221111 : Blo 1256446 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B8050553 : Blo 1256446 8050553 := bstep (se 2 (by rfl) ⟨3018957, by rfl⟩ : syracuseStep 8050553 = 6037915) B6037915
theorem B3823595 : Blo 1256446 3823595 := bstep (se 1 (by rfl) ⟨2867696, by rfl⟩ : syracuseStep 3823595 = 5735393) B5735393
theorem B46479521 : Blo 1256446 46479521 := bstep (se 2 (by rfl) ⟨17429820, by rfl⟩ : syracuseStep 46479521 = 34859641) B34859641
theorem B68843753 : Blo 1256446 68843753 := bstep (se 2 (by rfl) ⟨25816407, by rfl⟩ : syracuseStep 68843753 = 51632815) B51632815
theorem B9550385 : Blo 1256446 9550385 := bstep (se 2 (by rfl) ⟨3581394, by rfl⟩ : syracuseStep 9550385 = 7162789) B7162789
theorem B2120647 : Blo 1256446 2120647 := bstep (se 1 (by rfl) ⟨1590485, by rfl⟩ : syracuseStep 2120647 = 3180971) B3180971
theorem B4774889 : Blo 1256446 4774889 := bstep (se 2 (by rfl) ⟨1790583, by rfl⟩ : syracuseStep 4774889 = 3581167) B3581167
theorem B36723865 : Blo 1256446 36723865 := bstep (se 2 (by rfl) ⟨13771449, by rfl⟩ : syracuseStep 36723865 = 27542899) B27542899
theorem B4775071 : Blo 1256446 4775071 := bstep (se 1 (by rfl) ⟨3581303, by rfl⟩ : syracuseStep 4775071 = 7162607) B7162607
theorem B14523623 : Blo 1256446 14523623 := bstep (se 1 (by rfl) ⟨10892717, by rfl⟩ : syracuseStep 14523623 = 21785435) B21785435
theorem B139616135 : Blo 1256446 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B13590497 : Blo 1256446 13590497 := bstep (se 2 (by rfl) ⟨5096436, by rfl⟩ : syracuseStep 13590497 = 10192873) B10192873
theorem B107462663 : Blo 1256446 107462663 := bstep (se 1 (by rfl) ⟨80596997, by rfl⟩ : syracuseStep 107462663 = 161193995) B161193995
theorem B5374127 : Blo 1256446 5374127 := bstep (se 1 (by rfl) ⟨4030595, by rfl⟩ : syracuseStep 5374127 = 8061191) B8061191
theorem B6045911 : Blo 1256446 6045911 := bstep (se 1 (by rfl) ⟨4534433, by rfl⟩ : syracuseStep 6045911 = 9068867) B9068867
theorem B38740477 : Blo 1256446 38740477 := bstep (se 3 (by rfl) ⟨7263839, by rfl⟩ : syracuseStep 38740477 = 14527679) B14527679
theorem B1884839 : Blo 1256446 1884839 := bstep (se 1 (by rfl) ⟨1413629, by rfl⟩ : syracuseStep 1884839 = 2827259) B2827259
theorem B1884911 : Blo 1256446 1884911 := bstep (se 1 (by rfl) ⟨1413683, by rfl⟩ : syracuseStep 1884911 = 2827367) B2827367
theorem B1885211 : Blo 1256446 1885211 := bstep (se 1 (by rfl) ⟨1413908, by rfl⟩ : syracuseStep 1885211 = 2827817) B2827817
theorem B10748969 : Blo 1256446 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B1885343 : Blo 1256446 1885343 := bstep (se 1 (by rfl) ⟨1414007, by rfl⟩ : syracuseStep 1885343 = 2828015) B2828015
theorem B2827439 : Blo 1256446 2827439 := bstep (se 1 (by rfl) ⟨2120579, by rfl⟩ : syracuseStep 2827439 = 4241159) B4241159
theorem B5367035 : Blo 1256446 5367035 := bstep (se 1 (by rfl) ⟨4025276, by rfl⟩ : syracuseStep 5367035 = 8050553) B8050553
theorem B2827529 : Blo 1256446 2827529 := bstep (se 2 (by rfl) ⟨1060323, by rfl⟩ : syracuseStep 2827529 = 2120647) B2120647
theorem B2549063 : Blo 1256446 2549063 := bstep (se 1 (by rfl) ⟨1911797, by rfl⟩ : syracuseStep 2549063 = 3823595) B3823595
theorem B48965153 : Blo 1256446 48965153 := bstep (se 2 (by rfl) ⟨18361932, by rfl⟩ : syracuseStep 48965153 = 36723865) B36723865
theorem B6366761 : Blo 1256446 6366761 := bstep (se 2 (by rfl) ⟨2387535, by rfl⟩ : syracuseStep 6366761 = 4775071) B4775071
theorem B6366923 : Blo 1256446 6366923 := bstep (se 1 (by rfl) ⟨4775192, by rfl⟩ : syracuseStep 6366923 = 9550385) B9550385
theorem B1886249 : Blo 1256446 1886249 := bstep (se 2 (by rfl) ⟨707343, by rfl⟩ : syracuseStep 1886249 = 1414687) B1414687
theorem B1886687 : Blo 1256446 1886687 := bstep (se 1 (by rfl) ⟨1415015, by rfl⟩ : syracuseStep 1886687 = 2830031) B2830031
theorem B14518811 : Blo 1256446 14518811 := bstep (se 1 (by rfl) ⟨10889108, by rfl⟩ : syracuseStep 14518811 = 21778217) B21778217
theorem B2550523 : Blo 1256446 2550523 := bstep (se 1 (by rfl) ⟨1912892, by rfl⟩ : syracuseStep 2550523 = 3825785) B3825785
theorem B1887047 : Blo 1256446 1887047 := bstep (se 1 (by rfl) ⟨1415285, by rfl⟩ : syracuseStep 1887047 = 2830571) B2830571
theorem B4901755 : Blo 1256446 4901755 := bstep (se 1 (by rfl) ⟨3676316, by rfl⟩ : syracuseStep 4901755 = 7352633) B7352633
theorem B3181639 : Blo 1256446 3181639 := bstep (se 1 (by rfl) ⟨2386229, by rfl⟩ : syracuseStep 3181639 = 4772459) B4772459
theorem B1256655 : Blo 1256446 1256655 := bstep (se 1 (by rfl) ⟨942491, by rfl⟩ : syracuseStep 1256655 = 1884983) B1884983
theorem B9546983 : Blo 1256446 9546983 := bstep (se 1 (by rfl) ⟨7160237, by rfl⟩ : syracuseStep 9546983 = 14320475) B14320475
theorem B1887467 : Blo 1256446 1887467 := bstep (se 1 (by rfl) ⟨1415600, by rfl⟩ : syracuseStep 1887467 = 2831201) B2831201
theorem B1256731 : Blo 1256446 1256731 := bstep (se 1 (by rfl) ⟨942548, by rfl⟩ : syracuseStep 1256731 = 1885097) B1885097
theorem B1887515 : Blo 1256446 1887515 := bstep (se 1 (by rfl) ⟨1415636, by rfl⟩ : syracuseStep 1887515 = 2831273) B2831273
theorem B16108895 : Blo 1256446 16108895 := bstep (se 1 (by rfl) ⟨12081671, by rfl⟩ : syracuseStep 16108895 = 24163343) B24163343
theorem B2387407 : Blo 1256446 2387407 := bstep (se 1 (by rfl) ⟨1790555, by rfl⟩ : syracuseStep 2387407 = 3581111) B3581111
theorem B4246991 : Blo 1256446 4246991 := bstep (se 1 (by rfl) ⟨3185243, by rfl⟩ : syracuseStep 4246991 = 6370487) B6370487
theorem B1256987 : Blo 1256446 1256987 := bstep (se 1 (by rfl) ⟨942740, by rfl⟩ : syracuseStep 1256987 = 1885481) B1885481
theorem B2829995 : Blo 1256446 2829995 := bstep (se 1 (by rfl) ⟨2122496, by rfl⟩ : syracuseStep 2829995 = 4244993) B4244993
theorem B6041375 : Blo 1256446 6041375 := bstep (se 1 (by rfl) ⟨4531031, by rfl⟩ : syracuseStep 6041375 = 9062063) B9062063
theorem B2830391 : Blo 1256446 2830391 := bstep (se 1 (by rfl) ⟨2122793, by rfl⟩ : syracuseStep 2830391 = 4245587) B4245587
theorem B2830427 : Blo 1256446 2830427 := bstep (se 1 (by rfl) ⟨2122820, by rfl⟩ : syracuseStep 2830427 = 4245641) B4245641
theorem B30986347 : Blo 1256446 30986347 := bstep (se 1 (by rfl) ⟨23239760, by rfl⟩ : syracuseStep 30986347 = 46479521) B46479521
theorem B45895835 : Blo 1256446 45895835 := bstep (se 1 (by rfl) ⟨34421876, by rfl⟩ : syracuseStep 45895835 = 68843753) B68843753
theorem B2830535 : Blo 1256446 2830535 := bstep (se 1 (by rfl) ⟨2122901, by rfl⟩ : syracuseStep 2830535 = 4245803) B4245803
theorem B1258075 : Blo 1256446 1258075 := bstep (se 1 (by rfl) ⟨943556, by rfl⟩ : syracuseStep 1258075 = 1887113) B1887113
theorem B2830985 : Blo 1256446 2830985 := bstep (se 2 (by rfl) ⟨1061619, by rfl⟩ : syracuseStep 2830985 = 2123239) B2123239
theorem B3183259 : Blo 1256446 3183259 := bstep (se 1 (by rfl) ⟨2387444, by rfl⟩ : syracuseStep 3183259 = 4774889) B4774889
theorem B6370811 : Blo 1256446 6370811 := bstep (se 1 (by rfl) ⟨4778108, by rfl⟩ : syracuseStep 6370811 = 9556217) B9556217
theorem B3180467713 : Blo 1256446 3180467713 := bstep (se 2 (by rfl) ⟨1192675392, by rfl⟩ : syracuseStep 3180467713 = 2385350785) B2385350785
theorem B3020495 : Blo 1256446 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B4241591 : Blo 1256446 4241591 := bstep (se 1 (by rfl) ⟨3181193, by rfl⟩ : syracuseStep 4241591 = 6362387) B6362387
theorem B6043835 : Blo 1256446 6043835 := bstep (se 1 (by rfl) ⟨4532876, by rfl⟩ : syracuseStep 6043835 = 9065753) B9065753
theorem B2685287 : Blo 1256446 2685287 := bstep (se 1 (by rfl) ⟨2013965, by rfl⟩ : syracuseStep 2685287 = 4027931) B4027931
theorem B51616207 : Blo 1256446 51616207 := bstep (se 1 (by rfl) ⟨38712155, by rfl⟩ : syracuseStep 51616207 = 77424311) B77424311
theorem B26147407 : Blo 1256446 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B32201387 : Blo 1256446 32201387 := bstep (se 1 (by rfl) ⟨24151040, by rfl⟩ : syracuseStep 32201387 = 48302081) B48302081
theorem B1432895 : Blo 1256446 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B9682415 : Blo 1256446 9682415 := bstep (se 1 (by rfl) ⟨7261811, by rfl⟩ : syracuseStep 9682415 = 14523623) B14523623
theorem B10329707 : Blo 1256446 10329707 := bstep (se 1 (by rfl) ⟨7747280, by rfl⟩ : syracuseStep 10329707 = 15494561) B15494561
theorem B2121599 : Blo 1256446 2121599 := bstep (se 1 (by rfl) ⟨1591199, by rfl⟩ : syracuseStep 2121599 = 3182399) B3182399
theorem B93077423 : Blo 1256446 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B9060331 : Blo 1256446 9060331 := bstep (se 1 (by rfl) ⟨6795248, by rfl⟩ : syracuseStep 9060331 = 13590497) B13590497
theorem B30597223 : Blo 1256446 30597223 := bstep (se 1 (by rfl) ⟨22947917, by rfl⟩ : syracuseStep 30597223 = 45895835) B45895835
theorem B4030607 : Blo 1256446 4030607 := bstep (se 1 (by rfl) ⟨3022955, by rfl⟩ : syracuseStep 4030607 = 6045911) B6045911
theorem B1884959 : Blo 1256446 1884959 := bstep (se 1 (by rfl) ⟨1413719, by rfl⟩ : syracuseStep 1884959 = 2827439) B2827439
theorem B1885019 : Blo 1256446 1885019 := bstep (se 1 (by rfl) ⟨1413764, by rfl⟩ : syracuseStep 1885019 = 2827529) B2827529
theorem B4244345 : Blo 1256446 4244345 := bstep (se 2 (by rfl) ⟨1591629, by rfl⟩ : syracuseStep 4244345 = 3183259) B3183259
theorem B3400697 : Blo 1256446 3400697 := bstep (se 2 (by rfl) ⟨1275261, by rfl⟩ : syracuseStep 3400697 = 2550523) B2550523
theorem B4244507 : Blo 1256446 4244507 := bstep (se 1 (by rfl) ⟨3183380, by rfl⟩ : syracuseStep 4244507 = 6366761) B6366761
theorem B4244615 : Blo 1256446 4244615 := bstep (se 1 (by rfl) ⟨3183461, by rfl⟩ : syracuseStep 4244615 = 6366923) B6366923
theorem B130573741 : Blo 1256446 130573741 := bstep (se 3 (by rfl) ⟨24482576, by rfl⟩ : syracuseStep 130573741 = 48965153) B48965153
theorem B2827727 : Blo 1256446 2827727 := bstep (se 1 (by rfl) ⟨2120795, by rfl⟩ : syracuseStep 2827727 = 4241591) B4241591
theorem B8054653 : Blo 1256446 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B4240623617 : Blo 1256446 4240623617 := bstep (se 2 (by rfl) ⟨1590233856, by rfl⟩ : syracuseStep 4240623617 = 3180467713) B3180467713
theorem B275286437 : Blo 1256446 275286437 := bstep (se 4 (by rfl) ⟨25808103, by rfl⟩ : syracuseStep 275286437 = 51616207) B51616207
theorem B1886663 : Blo 1256446 1886663 := bstep (se 1 (by rfl) ⟨1414997, by rfl⟩ : syracuseStep 1886663 = 2829995) B2829995
theorem B71641775 : Blo 1256446 71641775 := bstep (se 1 (by rfl) ⟨53731331, by rfl⟩ : syracuseStep 71641775 = 107462663) B107462663
theorem B1886927 : Blo 1256446 1886927 := bstep (se 1 (by rfl) ⟨1415195, by rfl⟩ : syracuseStep 1886927 = 2830391) B2830391
theorem B1886951 : Blo 1256446 1886951 := bstep (se 1 (by rfl) ⟨1415213, by rfl⟩ : syracuseStep 1886951 = 2830427) B2830427
theorem B3582751 : Blo 1256446 3582751 := bstep (se 1 (by rfl) ⟨2687063, by rfl⟩ : syracuseStep 3582751 = 5374127) B5374127
theorem B1887023 : Blo 1256446 1887023 := bstep (se 1 (by rfl) ⟨1415267, by rfl⟩ : syracuseStep 1887023 = 2830535) B2830535
theorem B41315129 : Blo 1256446 41315129 := bstep (se 2 (by rfl) ⟨15493173, by rfl⟩ : syracuseStep 41315129 = 30986347) B30986347
theorem B1887323 : Blo 1256446 1887323 := bstep (se 1 (by rfl) ⟨1415492, by rfl⟩ : syracuseStep 1887323 = 2830985) B2830985
theorem B1256559 : Blo 1256446 1256559 := bstep (se 1 (by rfl) ⟨942419, by rfl⟩ : syracuseStep 1256559 = 1884839) B1884839
theorem B16116893 : Blo 1256446 16116893 := bstep (se 3 (by rfl) ⟨3021917, by rfl⟩ : syracuseStep 16116893 = 6043835) B6043835
theorem B1256607 : Blo 1256446 1256607 := bstep (se 1 (by rfl) ⟨942455, by rfl⟩ : syracuseStep 1256607 = 1884911) B1884911
theorem B51653969 : Blo 1256446 51653969 := bstep (se 2 (by rfl) ⟨19370238, by rfl⟩ : syracuseStep 51653969 = 38740477) B38740477
theorem B1256807 : Blo 1256446 1256807 := bstep (se 1 (by rfl) ⟨942605, by rfl⟩ : syracuseStep 1256807 = 1885211) B1885211
theorem B1256895 : Blo 1256446 1256895 := bstep (se 1 (by rfl) ⟨942671, by rfl⟩ : syracuseStep 1256895 = 1885343) B1885343
theorem B1699375 : Blo 1256446 1699375 := bstep (se 1 (by rfl) ⟨1274531, by rfl⟩ : syracuseStep 1699375 = 2549063) B2549063
theorem B4247207 : Blo 1256446 4247207 := bstep (se 1 (by rfl) ⟨3185405, by rfl⟩ : syracuseStep 4247207 = 6370811) B6370811
theorem B1257499 : Blo 1256446 1257499 := bstep (se 1 (by rfl) ⟨943124, by rfl⟩ : syracuseStep 1257499 = 1886249) B1886249
theorem B1790191 : Blo 1256446 1790191 := bstep (se 1 (by rfl) ⟨1342643, by rfl⟩ : syracuseStep 1790191 = 2685287) B2685287
theorem B1257791 : Blo 1256446 1257791 := bstep (se 1 (by rfl) ⟨943343, by rfl⟩ : syracuseStep 1257791 = 1886687) B1886687
theorem B9679207 : Blo 1256446 9679207 := bstep (se 1 (by rfl) ⟨7259405, by rfl⟩ : syracuseStep 9679207 = 14518811) B14518811
theorem B21467591 : Blo 1256446 21467591 := bstep (se 1 (by rfl) ⟨16100693, by rfl⟩ : syracuseStep 21467591 = 32201387) B32201387
theorem B1258031 : Blo 1256446 1258031 := bstep (se 1 (by rfl) ⟨943523, by rfl⟩ : syracuseStep 1258031 = 1887047) B1887047
theorem B3183209 : Blo 1256446 3183209 := bstep (se 2 (by rfl) ⟨1193703, by rfl⟩ : syracuseStep 3183209 = 2387407) B2387407
theorem B1258311 : Blo 1256446 1258311 := bstep (se 1 (by rfl) ⟨943733, by rfl⟩ : syracuseStep 1258311 = 1887467) B1887467
theorem B1258343 : Blo 1256446 1258343 := bstep (se 1 (by rfl) ⟨943757, by rfl⟩ : syracuseStep 1258343 = 1887515) B1887515
theorem B2831327 : Blo 1256446 2831327 := bstep (se 1 (by rfl) ⟨2123495, by rfl⟩ : syracuseStep 2831327 = 4246991) B4246991
theorem B6886471 : Blo 1256446 6886471 := bstep (se 1 (by rfl) ⟨5164853, by rfl⟩ : syracuseStep 6886471 = 10329707) B10329707
theorem B4027583 : Blo 1256446 4027583 := bstep (se 1 (by rfl) ⟨3020687, by rfl⟩ : syracuseStep 4027583 = 6041375) B6041375
theorem B1414399 : Blo 1256446 1414399 := bstep (se 1 (by rfl) ⟨1060799, by rfl⟩ : syracuseStep 1414399 = 2121599) B2121599
theorem B62051615 : Blo 1256446 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B12080441 : Blo 1256446 12080441 := bstep (se 2 (by rfl) ⟨4530165, by rfl⟩ : syracuseStep 12080441 = 9060331) B9060331
theorem B15284213 : Blo 1256446 15284213 := bstep (se 5 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 15284213 = 1432895) B1432895
theorem B7165979 : Blo 1256446 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B34863209 : Blo 1256446 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B3578023 : Blo 1256446 3578023 := bstep (se 1 (by rfl) ⟨2683517, by rfl⟩ : syracuseStep 3578023 = 5367035) B5367035
theorem B6535673 : Blo 1256446 6535673 := bstep (se 2 (by rfl) ⟨2450877, by rfl⟩ : syracuseStep 6535673 = 4901755) B4901755
theorem B4242185 : Blo 1256446 4242185 := bstep (se 2 (by rfl) ⟨1590819, by rfl⟩ : syracuseStep 4242185 = 3181639) B3181639
theorem B6364655 : Blo 1256446 6364655 := bstep (se 1 (by rfl) ⟨4773491, by rfl⟩ : syracuseStep 6364655 = 9546983) B9546983
theorem B10739263 : Blo 1256446 10739263 := bstep (se 1 (by rfl) ⟨8054447, by rfl⟩ : syracuseStep 10739263 = 16108895) B16108895
theorem B6454943 : Blo 1256446 6454943 := bstep (se 1 (by rfl) ⟨4841207, by rfl⟩ : syracuseStep 6454943 = 9682415) B9682415
theorem B40796297 : Blo 1256446 40796297 := bstep (se 2 (by rfl) ⟨15298611, by rfl⟩ : syracuseStep 40796297 = 30597223) B30597223
theorem B14311727 : Blo 1256446 14311727 := bstep (se 1 (by rfl) ⟨10733795, by rfl⟩ : syracuseStep 14311727 = 21467591) B21467591
theorem B10748285 : Blo 1256446 10748285 := bstep (se 3 (by rfl) ⟨2015303, by rfl⟩ : syracuseStep 10748285 = 4030607) B4030607
theorem B2122139 : Blo 1256446 2122139 := bstep (se 1 (by rfl) ⟨1591604, by rfl⟩ : syracuseStep 2122139 = 3183209) B3183209
theorem B10740221 : Blo 1256446 10740221 := bstep (se 3 (by rfl) ⟨2013791, by rfl⟩ : syracuseStep 10740221 = 4027583) B4027583
theorem B1885151 : Blo 1256446 1885151 := bstep (se 1 (by rfl) ⟨1413863, by rfl⟩ : syracuseStep 1885151 = 2827727) B2827727
theorem B4777001 : Blo 1256446 4777001 := bstep (se 2 (by rfl) ⟨1791375, by rfl⟩ : syracuseStep 4777001 = 3582751) B3582751
theorem B4777319 : Blo 1256446 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B23242139 : Blo 1256446 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B1885865 : Blo 1256446 1885865 := bstep (se 2 (by rfl) ⟨707199, by rfl⟩ : syracuseStep 1885865 = 1414399) B1414399
theorem B47761183 : Blo 1256446 47761183 := bstep (se 1 (by rfl) ⟨35820887, by rfl⟩ : syracuseStep 47761183 = 71641775) B71641775
theorem B2828123 : Blo 1256446 2828123 := bstep (se 1 (by rfl) ⟨2121092, by rfl⟩ : syracuseStep 2828123 = 4242185) B4242185
theorem B27543419 : Blo 1256446 27543419 := bstep (se 1 (by rfl) ⟨20657564, by rfl⟩ : syracuseStep 27543419 = 41315129) B41315129
theorem B174098321 : Blo 1256446 174098321 := bstep (se 2 (by rfl) ⟨65286870, by rfl⟩ : syracuseStep 174098321 = 130573741) B130573741
theorem B4303295 : Blo 1256446 4303295 := bstep (se 1 (by rfl) ⟨3227471, by rfl⟩ : syracuseStep 4303295 = 6454943) B6454943
theorem B4770697 : Blo 1256446 4770697 := bstep (se 2 (by rfl) ⟨1789011, by rfl⟩ : syracuseStep 4770697 = 3578023) B3578023
theorem B2386921 : Blo 1256446 2386921 := bstep (se 2 (by rfl) ⟨895095, by rfl⟩ : syracuseStep 2386921 = 1790191) B1790191
theorem B12905609 : Blo 1256446 12905609 := bstep (se 2 (by rfl) ⟨4839603, by rfl⟩ : syracuseStep 12905609 = 9679207) B9679207
theorem B1256639 : Blo 1256446 1256639 := bstep (se 1 (by rfl) ⟨942479, by rfl⟩ : syracuseStep 1256639 = 1884959) B1884959
theorem B1256679 : Blo 1256446 1256679 := bstep (se 1 (by rfl) ⟨942509, by rfl⟩ : syracuseStep 1256679 = 1885019) B1885019
theorem B2829563 : Blo 1256446 2829563 := bstep (se 1 (by rfl) ⟨2122172, by rfl⟩ : syracuseStep 2829563 = 4244345) B4244345
theorem B1887551 : Blo 1256446 1887551 := bstep (se 1 (by rfl) ⟨1415663, by rfl⟩ : syracuseStep 1887551 = 2831327) B2831327
theorem B2829671 : Blo 1256446 2829671 := bstep (se 1 (by rfl) ⟨2122253, by rfl⟩ : syracuseStep 2829671 = 4244507) B4244507
theorem B2829743 : Blo 1256446 2829743 := bstep (se 1 (by rfl) ⟨2122307, by rfl⟩ : syracuseStep 2829743 = 4244615) B4244615
theorem B32214509 : Blo 1256446 32214509 := bstep (se 3 (by rfl) ⟨6040220, by rfl⟩ : syracuseStep 32214509 = 12080441) B12080441
theorem B1257775 : Blo 1256446 1257775 := bstep (se 1 (by rfl) ⟨943331, by rfl⟩ : syracuseStep 1257775 = 1886663) B1886663
theorem B1257951 : Blo 1256446 1257951 := bstep (se 1 (by rfl) ⟨943463, by rfl⟩ : syracuseStep 1257951 = 1886927) B1886927
theorem B1257967 : Blo 1256446 1257967 := bstep (se 1 (by rfl) ⟨943475, by rfl⟩ : syracuseStep 1257967 = 1886951) B1886951
theorem B1258015 : Blo 1256446 1258015 := bstep (se 1 (by rfl) ⟨943511, by rfl⟩ : syracuseStep 1258015 = 1887023) B1887023
theorem B1258215 : Blo 1256446 1258215 := bstep (se 1 (by rfl) ⟨943661, by rfl⟩ : syracuseStep 1258215 = 1887323) B1887323
theorem B2265833 : Blo 1256446 2265833 := bstep (se 2 (by rfl) ⟨849687, by rfl⟩ : syracuseStep 2265833 = 1699375) B1699375
theorem B10744595 : Blo 1256446 10744595 := bstep (se 1 (by rfl) ⟨8058446, by rfl⟩ : syracuseStep 10744595 = 16116893) B16116893
theorem B34435979 : Blo 1256446 34435979 := bstep (se 1 (by rfl) ⟨25826984, by rfl⟩ : syracuseStep 34435979 = 51653969) B51653969
theorem B2831471 : Blo 1256446 2831471 := bstep (se 1 (by rfl) ⟨2123603, by rfl⟩ : syracuseStep 2831471 = 4247207) B4247207
theorem B2267131 : Blo 1256446 2267131 := bstep (se 1 (by rfl) ⟨1700348, by rfl⟩ : syracuseStep 2267131 = 3400697) B3400697
theorem B41367743 : Blo 1256446 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B10189475 : Blo 1256446 10189475 := bstep (se 1 (by rfl) ⟨7642106, by rfl⟩ : syracuseStep 10189475 = 15284213) B15284213
theorem B2827082411 : Blo 1256446 2827082411 := bstep (se 1 (by rfl) ⟨2120311808, by rfl⟩ : syracuseStep 2827082411 = 4240623617) B4240623617
theorem B9181961 : Blo 1256446 9181961 := bstep (se 2 (by rfl) ⟨3443235, by rfl⟩ : syracuseStep 9181961 = 6886471) B6886471
theorem B183524291 : Blo 1256446 183524291 := bstep (se 1 (by rfl) ⟨137643218, by rfl⟩ : syracuseStep 183524291 = 275286437) B275286437
theorem B4357115 : Blo 1256446 4357115 := bstep (se 1 (by rfl) ⟨3267836, by rfl⟩ : syracuseStep 4357115 = 6535673) B6535673
theorem B14319017 : Blo 1256446 14319017 := bstep (se 2 (by rfl) ⟨5369631, by rfl⟩ : syracuseStep 14319017 = 10739263) B10739263
theorem B4243103 : Blo 1256446 4243103 := bstep (se 1 (by rfl) ⟨3182327, by rfl⟩ : syracuseStep 4243103 = 6364655) B6364655
theorem B10739537 : Blo 1256446 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B27197531 : Blo 1256446 27197531 := bstep (se 1 (by rfl) ⟨20398148, by rfl⟩ : syracuseStep 27197531 = 40796297) B40796297
theorem B7160147 : Blo 1256446 7160147 := bstep (se 1 (by rfl) ⟨5370110, by rfl⟩ : syracuseStep 7160147 = 10740221) B10740221
theorem B34414957 : Blo 1256446 34414957 := bstep (se 3 (by rfl) ⟨6452804, by rfl⟩ : syracuseStep 34414957 = 12905609) B12905609
theorem B1885415 : Blo 1256446 1885415 := bstep (se 1 (by rfl) ⟨1414061, by rfl⟩ : syracuseStep 1885415 = 2828123) B2828123
theorem B116065547 : Blo 1256446 116065547 := bstep (se 1 (by rfl) ⟨87049160, by rfl⟩ : syracuseStep 116065547 = 174098321) B174098321
theorem B2868863 : Blo 1256446 2868863 := bstep (se 1 (by rfl) ⟨2151647, by rfl⟩ : syracuseStep 2868863 = 4303295) B4303295
theorem B6792983 : Blo 1256446 6792983 := bstep (se 1 (by rfl) ⟨5094737, by rfl⟩ : syracuseStep 6792983 = 10189475) B10189475
theorem B6121307 : Blo 1256446 6121307 := bstep (se 1 (by rfl) ⟨4590980, by rfl⟩ : syracuseStep 6121307 = 9181961) B9181961
theorem B122349527 : Blo 1256446 122349527 := bstep (se 1 (by rfl) ⟨91762145, by rfl⟩ : syracuseStep 122349527 = 183524291) B183524291
theorem B1886375 : Blo 1256446 1886375 := bstep (se 1 (by rfl) ⟨1414781, by rfl⟩ : syracuseStep 1886375 = 2829563) B2829563
theorem B1886447 : Blo 1256446 1886447 := bstep (se 1 (by rfl) ⟨1414835, by rfl⟩ : syracuseStep 1886447 = 2829671) B2829671
theorem B9546011 : Blo 1256446 9546011 := bstep (se 1 (by rfl) ⟨7159508, by rfl⟩ : syracuseStep 9546011 = 14319017) B14319017
theorem B1886495 : Blo 1256446 1886495 := bstep (se 1 (by rfl) ⟨1414871, by rfl⟩ : syracuseStep 1886495 = 2829743) B2829743
theorem B2828735 : Blo 1256446 2828735 := bstep (se 1 (by rfl) ⟨2121551, by rfl⟩ : syracuseStep 2828735 = 4243103) B4243103
theorem B7163063 : Blo 1256446 7163063 := bstep (se 1 (by rfl) ⟨5372297, by rfl⟩ : syracuseStep 7163063 = 10744595) B10744595
theorem B22957319 : Blo 1256446 22957319 := bstep (se 1 (by rfl) ⟨17217989, by rfl⟩ : syracuseStep 22957319 = 34435979) B34435979
theorem B1256767 : Blo 1256446 1256767 := bstep (se 1 (by rfl) ⟨942575, by rfl⟩ : syracuseStep 1256767 = 1885151) B1885151
theorem B1887647 : Blo 1256446 1887647 := bstep (se 1 (by rfl) ⟨1415735, by rfl⟩ : syracuseStep 1887647 = 2831471) B2831471
theorem B15494759 : Blo 1256446 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B1257243 : Blo 1256446 1257243 := bstep (se 1 (by rfl) ⟨942932, by rfl⟩ : syracuseStep 1257243 = 1885865) B1885865
theorem B6360929 : Blo 1256446 6360929 := bstep (se 2 (by rfl) ⟨2385348, by rfl⟩ : syracuseStep 6360929 = 4770697) B4770697
theorem B18362279 : Blo 1256446 18362279 := bstep (se 1 (by rfl) ⟨13771709, by rfl⟩ : syracuseStep 18362279 = 27543419) B27543419
theorem B3182561 : Blo 1256446 3182561 := bstep (se 2 (by rfl) ⟨1193460, by rfl⟩ : syracuseStep 3182561 = 2386921) B2386921
theorem B27578495 : Blo 1256446 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B254726309 : Blo 1256446 254726309 := bstep (se 4 (by rfl) ⟨23880591, by rfl⟩ : syracuseStep 254726309 = 47761183) B47761183
theorem B3022841 : Blo 1256446 3022841 := bstep (se 2 (by rfl) ⟨1133565, by rfl⟩ : syracuseStep 3022841 = 2267131) B2267131
theorem B1884721607 : Blo 1256446 1884721607 := bstep (se 1 (by rfl) ⟨1413541205, by rfl⟩ : syracuseStep 1884721607 = 2827082411) B2827082411
theorem B6042221 : Blo 1256446 6042221 := bstep (se 3 (by rfl) ⟨1132916, by rfl⟩ : syracuseStep 6042221 = 2265833) B2265833
theorem B2904743 : Blo 1256446 2904743 := bstep (se 1 (by rfl) ⟨2178557, by rfl⟩ : syracuseStep 2904743 = 4357115) B4357115
theorem B1258367 : Blo 1256446 1258367 := bstep (se 1 (by rfl) ⟨943775, by rfl⟩ : syracuseStep 1258367 = 1887551) B1887551
theorem B21476339 : Blo 1256446 21476339 := bstep (se 1 (by rfl) ⟨16107254, by rfl⟩ : syracuseStep 21476339 = 32214509) B32214509
theorem B9541151 : Blo 1256446 9541151 := bstep (se 1 (by rfl) ⟨7155863, by rfl⟩ : syracuseStep 9541151 = 14311727) B14311727
theorem B7165523 : Blo 1256446 7165523 := bstep (se 1 (by rfl) ⟨5374142, by rfl⟩ : syracuseStep 7165523 = 10748285) B10748285
theorem B1414759 : Blo 1256446 1414759 := bstep (se 1 (by rfl) ⟨1061069, by rfl⟩ : syracuseStep 1414759 = 2122139) B2122139
theorem B3184667 : Blo 1256446 3184667 := bstep (se 1 (by rfl) ⟨2388500, by rfl⟩ : syracuseStep 3184667 = 4777001) B4777001
theorem B3184879 : Blo 1256446 3184879 := bstep (se 1 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 3184879 = 4777319) B4777319
theorem B7159691 : Blo 1256446 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B1256481071 : Blo 1256446 1256481071 := bstep (se 1 (by rfl) ⟨942360803, by rfl⟩ : syracuseStep 1256481071 = 1884721607) B1884721607
theorem B4777015 : Blo 1256446 4777015 := bstep (se 1 (by rfl) ⟨3582761, by rfl⟩ : syracuseStep 4777015 = 7165523) B7165523
theorem B4080871 : Blo 1256446 4080871 := bstep (se 1 (by rfl) ⟨3060653, by rfl⟩ : syracuseStep 4080871 = 6121307) B6121307
theorem B2123111 : Blo 1256446 2123111 := bstep (se 1 (by rfl) ⟨1592333, by rfl⟩ : syracuseStep 2123111 = 3184667) B3184667
theorem B1885823 : Blo 1256446 1885823 := bstep (se 1 (by rfl) ⟨1414367, by rfl⟩ : syracuseStep 1885823 = 2828735) B2828735
theorem B1886345 : Blo 1256446 1886345 := bstep (se 2 (by rfl) ⟨707379, by rfl⟩ : syracuseStep 1886345 = 1414759) B1414759
theorem B15304879 : Blo 1256446 15304879 := bstep (se 1 (by rfl) ⟨11478659, by rfl⟩ : syracuseStep 15304879 = 22957319) B22957319
theorem B12241519 : Blo 1256446 12241519 := bstep (se 1 (by rfl) ⟨9181139, by rfl⟩ : syracuseStep 12241519 = 18362279) B18362279
theorem B18131687 : Blo 1256446 18131687 := bstep (se 1 (by rfl) ⟨13598765, by rfl⟩ : syracuseStep 18131687 = 27197531) B27197531
theorem B18385663 : Blo 1256446 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B4246505 : Blo 1256446 4246505 := bstep (se 2 (by rfl) ⟨1592439, by rfl⟩ : syracuseStep 4246505 = 3184879) B3184879
theorem B1936495 : Blo 1256446 1936495 := bstep (se 1 (by rfl) ⟨1452371, by rfl⟩ : syracuseStep 1936495 = 2904743) B2904743
theorem B45886609 : Blo 1256446 45886609 := bstep (se 2 (by rfl) ⟨17207478, by rfl⟩ : syracuseStep 45886609 = 34414957) B34414957
theorem B1256943 : Blo 1256446 1256943 := bstep (se 1 (by rfl) ⟨942707, by rfl⟩ : syracuseStep 1256943 = 1885415) B1885415
theorem B77377031 : Blo 1256446 77377031 := bstep (se 1 (by rfl) ⟨58032773, by rfl⟩ : syracuseStep 77377031 = 116065547) B116065547
theorem B6360767 : Blo 1256446 6360767 := bstep (se 1 (by rfl) ⟨4770575, by rfl⟩ : syracuseStep 6360767 = 9541151) B9541151
theorem B1257583 : Blo 1256446 1257583 := bstep (se 1 (by rfl) ⟨943187, by rfl⟩ : syracuseStep 1257583 = 1886375) B1886375
theorem B1257631 : Blo 1256446 1257631 := bstep (se 1 (by rfl) ⟨943223, by rfl⟩ : syracuseStep 1257631 = 1886447) B1886447
theorem B1257663 : Blo 1256446 1257663 := bstep (se 1 (by rfl) ⟨943247, by rfl⟩ : syracuseStep 1257663 = 1886495) B1886495
theorem B1258431 : Blo 1256446 1258431 := bstep (se 1 (by rfl) ⟨943823, by rfl⟩ : syracuseStep 1258431 = 1887647) B1887647
theorem B4240619 : Blo 1256446 4240619 := bstep (se 1 (by rfl) ⟨3180464, by rfl⟩ : syracuseStep 4240619 = 6360929) B6360929
theorem B4773127 : Blo 1256446 4773127 := bstep (se 1 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 4773127 = 7159691) B7159691
theorem B2015227 : Blo 1256446 2015227 := bstep (se 1 (by rfl) ⟨1511420, by rfl⟩ : syracuseStep 2015227 = 3022841) B3022841
theorem B4773431 : Blo 1256446 4773431 := bstep (se 1 (by rfl) ⟨3580073, by rfl⟩ : syracuseStep 4773431 = 7160147) B7160147
theorem B4028147 : Blo 1256446 4028147 := bstep (se 1 (by rfl) ⟨3021110, by rfl⟩ : syracuseStep 4028147 = 6042221) B6042221
theorem B679270157 : Blo 1256446 679270157 := bstep (se 3 (by rfl) ⟨127363154, by rfl⟩ : syracuseStep 679270157 = 254726309) B254726309
theorem B14317559 : Blo 1256446 14317559 := bstep (se 1 (by rfl) ⟨10738169, by rfl⟩ : syracuseStep 14317559 = 21476339) B21476339
theorem B4528655 : Blo 1256446 4528655 := bstep (se 1 (by rfl) ⟨3396491, by rfl⟩ : syracuseStep 4528655 = 6792983) B6792983
theorem B81566351 : Blo 1256446 81566351 := bstep (se 1 (by rfl) ⟨61174763, by rfl⟩ : syracuseStep 81566351 = 122349527) B122349527
theorem B6364007 : Blo 1256446 6364007 := bstep (se 1 (by rfl) ⟨4773005, by rfl⟩ : syracuseStep 6364007 = 9546011) B9546011
theorem B7650301 : Blo 1256446 7650301 := bstep (se 3 (by rfl) ⟨1434431, by rfl⟩ : syracuseStep 7650301 = 2868863) B2868863
theorem B4775375 : Blo 1256446 4775375 := bstep (se 1 (by rfl) ⟨3581531, by rfl⟩ : syracuseStep 4775375 = 7163063) B7163063
theorem B10329839 : Blo 1256446 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B2121707 : Blo 1256446 2121707 := bstep (se 1 (by rfl) ⟨1591280, by rfl⟩ : syracuseStep 2121707 = 3182561) B3182561
theorem B20406505 : Blo 1256446 20406505 := bstep (se 2 (by rfl) ⟨7652439, by rfl⟩ : syracuseStep 20406505 = 15304879) B15304879
theorem B2827079 : Blo 1256446 2827079 := bstep (se 1 (by rfl) ⟨2120309, by rfl⟩ : syracuseStep 2827079 = 4240619) B4240619
theorem B452846771 : Blo 1256446 452846771 := bstep (se 1 (by rfl) ⟨339635078, by rfl⟩ : syracuseStep 452846771 = 679270157) B679270157
theorem B9545039 : Blo 1256446 9545039 := bstep (se 1 (by rfl) ⟨7158779, by rfl⟩ : syracuseStep 9545039 = 14317559) B14317559
theorem B10200401 : Blo 1256446 10200401 := bstep (se 2 (by rfl) ⟨3825150, by rfl⟩ : syracuseStep 10200401 = 7650301) B7650301
theorem B2581993 : Blo 1256446 2581993 := bstep (se 2 (by rfl) ⟨968247, by rfl⟩ : syracuseStep 2581993 = 1936495) B1936495
theorem B2686969 : Blo 1256446 2686969 := bstep (se 2 (by rfl) ⟨1007613, by rfl⟩ : syracuseStep 2686969 = 2015227) B2015227
theorem B24514217 : Blo 1256446 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B3182287 : Blo 1256446 3182287 := bstep (se 1 (by rfl) ⟨2386715, by rfl⟩ : syracuseStep 3182287 = 4773431) B4773431
theorem B1257215 : Blo 1256446 1257215 := bstep (se 1 (by rfl) ⟨942911, by rfl⟩ : syracuseStep 1257215 = 1885823) B1885823
theorem B6369353 : Blo 1256446 6369353 := bstep (se 2 (by rfl) ⟨2388507, by rfl⟩ : syracuseStep 6369353 = 4777015) B4777015
theorem B1257563 : Blo 1256446 1257563 := bstep (se 1 (by rfl) ⟨943172, by rfl⟩ : syracuseStep 1257563 = 1886345) B1886345
theorem B61182145 : Blo 1256446 61182145 := bstep (se 2 (by rfl) ⟨22943304, by rfl⟩ : syracuseStep 61182145 = 45886609) B45886609
theorem B3019103 : Blo 1256446 3019103 := bstep (se 1 (by rfl) ⟨2264327, by rfl⟩ : syracuseStep 3019103 = 4528655) B4528655
theorem B12087791 : Blo 1256446 12087791 := bstep (se 1 (by rfl) ⟨9065843, by rfl⟩ : syracuseStep 12087791 = 18131687) B18131687
theorem B2831003 : Blo 1256446 2831003 := bstep (se 1 (by rfl) ⟨2123252, by rfl⟩ : syracuseStep 2831003 = 4246505) B4246505
theorem B3183583 : Blo 1256446 3183583 := bstep (se 1 (by rfl) ⟨2387687, by rfl⟩ : syracuseStep 3183583 = 4775375) B4775375
theorem B4240511 : Blo 1256446 4240511 := bstep (se 1 (by rfl) ⟨3180383, by rfl⟩ : syracuseStep 4240511 = 6360767) B6360767
theorem B6886559 : Blo 1256446 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B1414471 : Blo 1256446 1414471 := bstep (se 1 (by rfl) ⟨1060853, by rfl⟩ : syracuseStep 1414471 = 2121707) B2121707
theorem B837654047 : Blo 1256446 837654047 := bstep (se 1 (by rfl) ⟨628240535, by rfl⟩ : syracuseStep 837654047 = 1256481071) B1256481071
theorem B65288101 : Blo 1256446 65288101 := bstep (se 4 (by rfl) ⟨6120759, by rfl⟩ : syracuseStep 65288101 = 12241519) B12241519
theorem B1415407 : Blo 1256446 1415407 := bstep (se 1 (by rfl) ⟨1061555, by rfl⟩ : syracuseStep 1415407 = 2123111) B2123111
theorem B2685431 : Blo 1256446 2685431 := bstep (se 1 (by rfl) ⟨2014073, by rfl⟩ : syracuseStep 2685431 = 4028147) B4028147
theorem B21764645 : Blo 1256446 21764645 := bstep (se 4 (by rfl) ⟨2040435, by rfl⟩ : syracuseStep 21764645 = 4080871) B4080871
theorem B6364169 : Blo 1256446 6364169 := bstep (se 2 (by rfl) ⟨2386563, by rfl⟩ : syracuseStep 6364169 = 4773127) B4773127
theorem B54377567 : Blo 1256446 54377567 := bstep (se 1 (by rfl) ⟨40783175, by rfl⟩ : syracuseStep 54377567 = 81566351) B81566351
theorem B4242671 : Blo 1256446 4242671 := bstep (se 1 (by rfl) ⟨3182003, by rfl⟩ : syracuseStep 4242671 = 6364007) B6364007
theorem B51584687 : Blo 1256446 51584687 := bstep (se 1 (by rfl) ⟨38688515, by rfl⟩ : syracuseStep 51584687 = 77377031) B77377031
theorem B81576193 : Blo 1256446 81576193 := bstep (se 2 (by rfl) ⟨30591072, by rfl⟩ : syracuseStep 81576193 = 61182145) B61182145
theorem B1884719 : Blo 1256446 1884719 := bstep (se 1 (by rfl) ⟨1413539, by rfl⟩ : syracuseStep 1884719 = 2827079) B2827079
theorem B2827007 : Blo 1256446 2827007 := bstep (se 1 (by rfl) ⟨2120255, by rfl⟩ : syracuseStep 2827007 = 4240511) B4240511
theorem B6800267 : Blo 1256446 6800267 := bstep (se 1 (by rfl) ⟨5100200, by rfl⟩ : syracuseStep 6800267 = 10200401) B10200401
theorem B4244777 : Blo 1256446 4244777 := bstep (se 2 (by rfl) ⟨1591791, by rfl⟩ : syracuseStep 4244777 = 3183583) B3183583
theorem B7161149 : Blo 1256446 7161149 := bstep (se 3 (by rfl) ⟨1342715, by rfl⟩ : syracuseStep 7161149 = 2685431) B2685431
theorem B14509763 : Blo 1256446 14509763 := bstep (se 1 (by rfl) ⟨10882322, by rfl⟩ : syracuseStep 14509763 = 21764645) B21764645
theorem B1885961 : Blo 1256446 1885961 := bstep (se 2 (by rfl) ⟨707235, by rfl⟩ : syracuseStep 1885961 = 1414471) B1414471
theorem B3442657 : Blo 1256446 3442657 := bstep (se 2 (by rfl) ⟨1290996, by rfl⟩ : syracuseStep 3442657 = 2581993) B2581993
theorem B36251711 : Blo 1256446 36251711 := bstep (se 1 (by rfl) ⟨27188783, by rfl⟩ : syracuseStep 36251711 = 54377567) B54377567
theorem B2828447 : Blo 1256446 2828447 := bstep (se 1 (by rfl) ⟨2121335, by rfl⟩ : syracuseStep 2828447 = 4242671) B4242671
theorem B87050801 : Blo 1256446 87050801 := bstep (se 2 (by rfl) ⟨32644050, by rfl⟩ : syracuseStep 87050801 = 65288101) B65288101
theorem B3582625 : Blo 1256446 3582625 := bstep (se 2 (by rfl) ⟨1343484, by rfl⟩ : syracuseStep 3582625 = 2686969) B2686969
theorem B4246235 : Blo 1256446 4246235 := bstep (se 1 (by rfl) ⟨3184676, by rfl⟩ : syracuseStep 4246235 = 6369353) B6369353
theorem B27208673 : Blo 1256446 27208673 := bstep (se 2 (by rfl) ⟨10203252, by rfl⟩ : syracuseStep 27208673 = 20406505) B20406505
theorem B1887209 : Blo 1256446 1887209 := bstep (se 2 (by rfl) ⟨707703, by rfl⟩ : syracuseStep 1887209 = 1415407) B1415407
theorem B1887335 : Blo 1256446 1887335 := bstep (se 1 (by rfl) ⟨1415501, by rfl⟩ : syracuseStep 1887335 = 2831003) B2831003
theorem B558436031 : Blo 1256446 558436031 := bstep (se 1 (by rfl) ⟨418827023, by rfl⟩ : syracuseStep 558436031 = 837654047) B837654047
theorem B2012735 : Blo 1256446 2012735 := bstep (se 1 (by rfl) ⟨1509551, by rfl⟩ : syracuseStep 2012735 = 3019103) B3019103
theorem B8058527 : Blo 1256446 8058527 := bstep (se 1 (by rfl) ⟨6043895, by rfl⟩ : syracuseStep 8058527 = 12087791) B12087791
theorem B18364157 : Blo 1256446 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B301897847 : Blo 1256446 301897847 := bstep (se 1 (by rfl) ⟨226423385, by rfl⟩ : syracuseStep 301897847 = 452846771) B452846771
theorem B6363359 : Blo 1256446 6363359 := bstep (se 1 (by rfl) ⟨4772519, by rfl⟩ : syracuseStep 6363359 = 9545039) B9545039
theorem B4242779 : Blo 1256446 4242779 := bstep (se 1 (by rfl) ⟨3182084, by rfl⟩ : syracuseStep 4242779 = 6364169) B6364169
theorem B4243049 : Blo 1256446 4243049 := bstep (se 2 (by rfl) ⟨1591143, by rfl⟩ : syracuseStep 4243049 = 3182287) B3182287
theorem B16342811 : Blo 1256446 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B34389791 : Blo 1256446 34389791 := bstep (se 1 (by rfl) ⟨25792343, by rfl⟩ : syracuseStep 34389791 = 51584687) B51584687
theorem B1884671 : Blo 1256446 1884671 := bstep (se 1 (by rfl) ⟨1413503, by rfl⟩ : syracuseStep 1884671 = 2827007) B2827007
theorem B4776833 : Blo 1256446 4776833 := bstep (se 2 (by rfl) ⟨1791312, by rfl⟩ : syracuseStep 4776833 = 3582625) B3582625
theorem B24167807 : Blo 1256446 24167807 := bstep (se 1 (by rfl) ⟨18125855, by rfl⟩ : syracuseStep 24167807 = 36251711) B36251711
theorem B1885631 : Blo 1256446 1885631 := bstep (se 1 (by rfl) ⟨1414223, by rfl⟩ : syracuseStep 1885631 = 2828447) B2828447
theorem B5367293 : Blo 1256446 5367293 := bstep (se 3 (by rfl) ⟨1006367, by rfl⟩ : syracuseStep 5367293 = 2012735) B2012735
theorem B58033867 : Blo 1256446 58033867 := bstep (se 1 (by rfl) ⟨43525400, by rfl⟩ : syracuseStep 58033867 = 87050801) B87050801
theorem B18139115 : Blo 1256446 18139115 := bstep (se 1 (by rfl) ⟨13604336, by rfl⟩ : syracuseStep 18139115 = 27208673) B27208673
theorem B2828519 : Blo 1256446 2828519 := bstep (se 1 (by rfl) ⟨2121389, by rfl⟩ : syracuseStep 2828519 = 4242779) B4242779
theorem B2828699 : Blo 1256446 2828699 := bstep (se 1 (by rfl) ⟨2121524, by rfl⟩ : syracuseStep 2828699 = 4243049) B4243049
theorem B4590209 : Blo 1256446 4590209 := bstep (se 2 (by rfl) ⟨1721328, by rfl⟩ : syracuseStep 4590209 = 3442657) B3442657
theorem B108768257 : Blo 1256446 108768257 := bstep (se 2 (by rfl) ⟨40788096, by rfl⟩ : syracuseStep 108768257 = 81576193) B81576193
theorem B1256479 : Blo 1256446 1256479 := bstep (se 1 (by rfl) ⟨942359, by rfl⟩ : syracuseStep 1256479 = 1884719) B1884719
theorem B4533511 : Blo 1256446 4533511 := bstep (se 1 (by rfl) ⟨3400133, by rfl⟩ : syracuseStep 4533511 = 6800267) B6800267
theorem B2829851 : Blo 1256446 2829851 := bstep (se 1 (by rfl) ⟨2122388, by rfl⟩ : syracuseStep 2829851 = 4244777) B4244777
theorem B12242771 : Blo 1256446 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B1257307 : Blo 1256446 1257307 := bstep (se 1 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 1257307 = 1885961) B1885961
theorem B201265231 : Blo 1256446 201265231 := bstep (se 1 (by rfl) ⟨150948923, by rfl⟩ : syracuseStep 201265231 = 301897847) B301897847
theorem B2830823 : Blo 1256446 2830823 := bstep (se 1 (by rfl) ⟨2123117, by rfl⟩ : syracuseStep 2830823 = 4246235) B4246235
theorem B1258139 : Blo 1256446 1258139 := bstep (se 1 (by rfl) ⟨943604, by rfl⟩ : syracuseStep 1258139 = 1887209) B1887209
theorem B1258223 : Blo 1256446 1258223 := bstep (se 1 (by rfl) ⟨943667, by rfl⟩ : syracuseStep 1258223 = 1887335) B1887335
theorem B372290687 : Blo 1256446 372290687 := bstep (se 1 (by rfl) ⟨279218015, by rfl⟩ : syracuseStep 372290687 = 558436031) B558436031
theorem B22926527 : Blo 1256446 22926527 := bstep (se 1 (by rfl) ⟨17194895, by rfl⟩ : syracuseStep 22926527 = 34389791) B34389791
theorem B4774099 : Blo 1256446 4774099 := bstep (se 1 (by rfl) ⟨3580574, by rfl⟩ : syracuseStep 4774099 = 7161149) B7161149
theorem B5372351 : Blo 1256446 5372351 := bstep (se 1 (by rfl) ⟨4029263, by rfl⟩ : syracuseStep 5372351 = 8058527) B8058527
theorem B9673175 : Blo 1256446 9673175 := bstep (se 1 (by rfl) ⟨7254881, by rfl⟩ : syracuseStep 9673175 = 14509763) B14509763
theorem B4242239 : Blo 1256446 4242239 := bstep (se 1 (by rfl) ⟨3181679, by rfl⟩ : syracuseStep 4242239 = 6363359) B6363359
theorem B10895207 : Blo 1256446 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B268353641 : Blo 1256446 268353641 := bstep (se 2 (by rfl) ⟨100632615, by rfl⟩ : syracuseStep 268353641 = 201265231) B201265231
theorem B6365465 : Blo 1256446 6365465 := bstep (se 2 (by rfl) ⟨2387049, by rfl⟩ : syracuseStep 6365465 = 4774099) B4774099
theorem B248193791 : Blo 1256446 248193791 := bstep (se 1 (by rfl) ⟨186145343, by rfl⟩ : syracuseStep 248193791 = 372290687) B372290687
theorem B12092743 : Blo 1256446 12092743 := bstep (se 1 (by rfl) ⟨9069557, by rfl⟩ : syracuseStep 12092743 = 18139115) B18139115
theorem B1885679 : Blo 1256446 1885679 := bstep (se 1 (by rfl) ⟨1414259, by rfl⟩ : syracuseStep 1885679 = 2828519) B2828519
theorem B1885799 : Blo 1256446 1885799 := bstep (se 1 (by rfl) ⟨1414349, by rfl⟩ : syracuseStep 1885799 = 2828699) B2828699
theorem B3581567 : Blo 1256446 3581567 := bstep (se 1 (by rfl) ⟨2686175, by rfl⟩ : syracuseStep 3581567 = 5372351) B5372351
theorem B6448783 : Blo 1256446 6448783 := bstep (se 1 (by rfl) ⟨4836587, by rfl⟩ : syracuseStep 6448783 = 9673175) B9673175
theorem B12240557 : Blo 1256446 12240557 := bstep (se 3 (by rfl) ⟨2295104, by rfl⟩ : syracuseStep 12240557 = 4590209) B4590209
theorem B2828159 : Blo 1256446 2828159 := bstep (se 1 (by rfl) ⟨2121119, by rfl⟩ : syracuseStep 2828159 = 4242239) B4242239
theorem B1886567 : Blo 1256446 1886567 := bstep (se 1 (by rfl) ⟨1414925, by rfl⟩ : syracuseStep 1886567 = 2829851) B2829851
theorem B8161847 : Blo 1256446 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B1887215 : Blo 1256446 1887215 := bstep (se 1 (by rfl) ⟨1415411, by rfl⟩ : syracuseStep 1887215 = 2830823) B2830823
theorem B1256447 : Blo 1256446 1256447 := bstep (se 1 (by rfl) ⟨942335, by rfl⟩ : syracuseStep 1256447 = 1884671) B1884671
theorem B1257087 : Blo 1256446 1257087 := bstep (se 1 (by rfl) ⟨942815, by rfl⟩ : syracuseStep 1257087 = 1885631) B1885631
theorem B72512171 : Blo 1256446 72512171 := bstep (se 1 (by rfl) ⟨54384128, by rfl⟩ : syracuseStep 72512171 = 108768257) B108768257
theorem B77378489 : Blo 1256446 77378489 := bstep (se 2 (by rfl) ⟨29016933, by rfl⟩ : syracuseStep 77378489 = 58033867) B58033867
theorem B29053885 : Blo 1256446 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B3184555 : Blo 1256446 3184555 := bstep (se 1 (by rfl) ⟨2388416, by rfl⟩ : syracuseStep 3184555 = 4776833) B4776833
theorem B15284351 : Blo 1256446 15284351 := bstep (se 1 (by rfl) ⟨11463263, by rfl⟩ : syracuseStep 15284351 = 22926527) B22926527
theorem B16111871 : Blo 1256446 16111871 := bstep (se 1 (by rfl) ⟨12083903, by rfl⟩ : syracuseStep 16111871 = 24167807) B24167807
theorem B3578195 : Blo 1256446 3578195 := bstep (se 1 (by rfl) ⟨2683646, by rfl⟩ : syracuseStep 3578195 = 5367293) B5367293
theorem B6044681 : Blo 1256446 6044681 := bstep (se 2 (by rfl) ⟨2266755, by rfl⟩ : syracuseStep 6044681 = 4533511) B4533511
theorem B4243643 : Blo 1256446 4243643 := bstep (se 1 (by rfl) ⟨3182732, by rfl⟩ : syracuseStep 4243643 = 6365465) B6365465
theorem B48341447 : Blo 1256446 48341447 := bstep (se 1 (by rfl) ⟨36256085, by rfl⟩ : syracuseStep 48341447 = 72512171) B72512171
theorem B165462527 : Blo 1256446 165462527 := bstep (se 1 (by rfl) ⟨124096895, by rfl⟩ : syracuseStep 165462527 = 248193791) B248193791
theorem B51585659 : Blo 1256446 51585659 := bstep (se 1 (by rfl) ⟨38689244, by rfl⟩ : syracuseStep 51585659 = 77378489) B77378489
theorem B8160371 : Blo 1256446 8160371 := bstep (se 1 (by rfl) ⟨6120278, by rfl⟩ : syracuseStep 8160371 = 12240557) B12240557
theorem B1885439 : Blo 1256446 1885439 := bstep (se 1 (by rfl) ⟨1414079, by rfl⟩ : syracuseStep 1885439 = 2828159) B2828159
theorem B10741247 : Blo 1256446 10741247 := bstep (se 1 (by rfl) ⟨8055935, by rfl⟩ : syracuseStep 10741247 = 16111871) B16111871
theorem B2385463 : Blo 1256446 2385463 := bstep (se 1 (by rfl) ⟨1789097, by rfl⟩ : syracuseStep 2385463 = 3578195) B3578195
theorem B5441231 : Blo 1256446 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B16123657 : Blo 1256446 16123657 := bstep (se 2 (by rfl) ⟨6046371, by rfl⟩ : syracuseStep 16123657 = 12092743) B12092743
theorem B4246073 : Blo 1256446 4246073 := bstep (se 2 (by rfl) ⟨1592277, by rfl⟩ : syracuseStep 4246073 = 3184555) B3184555
theorem B1257119 : Blo 1256446 1257119 := bstep (se 1 (by rfl) ⟨942839, by rfl⟩ : syracuseStep 1257119 = 1885679) B1885679
theorem B1257199 : Blo 1256446 1257199 := bstep (se 1 (by rfl) ⟨942899, by rfl⟩ : syracuseStep 1257199 = 1885799) B1885799
theorem B2387711 : Blo 1256446 2387711 := bstep (se 1 (by rfl) ⟨1790783, by rfl⟩ : syracuseStep 2387711 = 3581567) B3581567
theorem B1257711 : Blo 1256446 1257711 := bstep (se 1 (by rfl) ⟨943283, by rfl⟩ : syracuseStep 1257711 = 1886567) B1886567
theorem B1258143 : Blo 1256446 1258143 := bstep (se 1 (by rfl) ⟨943607, by rfl⟩ : syracuseStep 1258143 = 1887215) B1887215
theorem B8598377 : Blo 1256446 8598377 := bstep (se 2 (by rfl) ⟨3224391, by rfl⟩ : syracuseStep 8598377 = 6448783) B6448783
theorem B178902427 : Blo 1256446 178902427 := bstep (se 1 (by rfl) ⟨134176820, by rfl⟩ : syracuseStep 178902427 = 268353641) B268353641
theorem B38738513 : Blo 1256446 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B10189567 : Blo 1256446 10189567 := bstep (se 1 (by rfl) ⟨7642175, by rfl⟩ : syracuseStep 10189567 = 15284351) B15284351
theorem B4029787 : Blo 1256446 4029787 := bstep (se 1 (by rfl) ⟨3022340, by rfl⟩ : syracuseStep 4029787 = 6044681) B6044681
theorem B32227631 : Blo 1256446 32227631 := bstep (se 1 (by rfl) ⟨24170723, by rfl⟩ : syracuseStep 32227631 = 48341447) B48341447
theorem B34390439 : Blo 1256446 34390439 := bstep (se 1 (by rfl) ⟨25792829, by rfl⟩ : syracuseStep 34390439 = 51585659) B51585659
theorem B5440247 : Blo 1256446 5440247 := bstep (se 1 (by rfl) ⟨4080185, by rfl⟩ : syracuseStep 5440247 = 8160371) B8160371
theorem B7160831 : Blo 1256446 7160831 := bstep (se 1 (by rfl) ⟨5370623, by rfl⟩ : syracuseStep 7160831 = 10741247) B10741247
theorem B238536569 : Blo 1256446 238536569 := bstep (se 2 (by rfl) ⟨89451213, by rfl⟩ : syracuseStep 238536569 = 178902427) B178902427
theorem B3180617 : Blo 1256446 3180617 := bstep (se 2 (by rfl) ⟨1192731, by rfl⟩ : syracuseStep 3180617 = 2385463) B2385463
theorem B21498209 : Blo 1256446 21498209 := bstep (se 2 (by rfl) ⟨8061828, by rfl⟩ : syracuseStep 21498209 = 16123657) B16123657
theorem B1591807 : Blo 1256446 1591807 := bstep (se 1 (by rfl) ⟨1193855, by rfl⟩ : syracuseStep 1591807 = 2387711) B2387711
theorem B2829095 : Blo 1256446 2829095 := bstep (se 1 (by rfl) ⟨2121821, by rfl⟩ : syracuseStep 2829095 = 4243643) B4243643
theorem B110308351 : Blo 1256446 110308351 := bstep (se 1 (by rfl) ⟨82731263, by rfl⟩ : syracuseStep 110308351 = 165462527) B165462527
theorem B1256959 : Blo 1256446 1256959 := bstep (se 1 (by rfl) ⟨942719, by rfl⟩ : syracuseStep 1256959 = 1885439) B1885439
theorem B13586089 : Blo 1256446 13586089 := bstep (se 2 (by rfl) ⟨5094783, by rfl⟩ : syracuseStep 13586089 = 10189567) B10189567
theorem B2830715 : Blo 1256446 2830715 := bstep (se 1 (by rfl) ⟨2123036, by rfl⟩ : syracuseStep 2830715 = 4246073) B4246073
theorem B25825675 : Blo 1256446 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B5732251 : Blo 1256446 5732251 := bstep (se 1 (by rfl) ⟨4299188, by rfl⟩ : syracuseStep 5732251 = 8598377) B8598377
theorem B3627487 : Blo 1256446 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B5373049 : Blo 1256446 5373049 := bstep (se 2 (by rfl) ⟨2014893, by rfl⟩ : syracuseStep 5373049 = 4029787) B4029787
theorem B2122409 : Blo 1256446 2122409 := bstep (se 2 (by rfl) ⟨795903, by rfl⟩ : syracuseStep 2122409 = 1591807) B1591807
theorem B159024379 : Blo 1256446 159024379 := bstep (se 1 (by rfl) ⟨119268284, by rfl⟩ : syracuseStep 159024379 = 238536569) B238536569
theorem B1886063 : Blo 1256446 1886063 := bstep (se 1 (by rfl) ⟨1414547, by rfl⟩ : syracuseStep 1886063 = 2829095) B2829095
theorem B18114785 : Blo 1256446 18114785 := bstep (se 2 (by rfl) ⟨6793044, by rfl⟩ : syracuseStep 18114785 = 13586089) B13586089
theorem B1887143 : Blo 1256446 1887143 := bstep (se 1 (by rfl) ⟨1415357, by rfl⟩ : syracuseStep 1887143 = 2830715) B2830715
theorem B34434233 : Blo 1256446 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B7164065 : Blo 1256446 7164065 := bstep (se 2 (by rfl) ⟨2686524, by rfl⟩ : syracuseStep 7164065 = 5373049) B5373049
theorem B14332139 : Blo 1256446 14332139 := bstep (se 1 (by rfl) ⟨10749104, by rfl⟩ : syracuseStep 14332139 = 21498209) B21498209
theorem B19346597 : Blo 1256446 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B21485087 : Blo 1256446 21485087 := bstep (se 1 (by rfl) ⟨16113815, by rfl⟩ : syracuseStep 21485087 = 32227631) B32227631
theorem B22926959 : Blo 1256446 22926959 := bstep (se 1 (by rfl) ⟨17195219, by rfl⟩ : syracuseStep 22926959 = 34390439) B34390439
theorem B3626831 : Blo 1256446 3626831 := bstep (se 1 (by rfl) ⟨2720123, by rfl⟩ : syracuseStep 3626831 = 5440247) B5440247
theorem B4773887 : Blo 1256446 4773887 := bstep (se 1 (by rfl) ⟨3580415, by rfl⟩ : syracuseStep 4773887 = 7160831) B7160831
theorem B147077801 : Blo 1256446 147077801 := bstep (se 2 (by rfl) ⟨55154175, by rfl⟩ : syracuseStep 147077801 = 110308351) B110308351
theorem B2120411 : Blo 1256446 2120411 := bstep (se 1 (by rfl) ⟨1590308, by rfl⟩ : syracuseStep 2120411 = 3180617) B3180617
theorem B30572005 : Blo 1256446 30572005 := bstep (se 4 (by rfl) ⟨2866125, by rfl⟩ : syracuseStep 30572005 = 5732251) B5732251
theorem B4776043 : Blo 1256446 4776043 := bstep (se 1 (by rfl) ⟨3582032, by rfl⟩ : syracuseStep 4776043 = 7164065) B7164065
theorem B2417887 : Blo 1256446 2417887 := bstep (se 1 (by rfl) ⟨1813415, by rfl⟩ : syracuseStep 2417887 = 3626831) B3626831
theorem B12076523 : Blo 1256446 12076523 := bstep (se 1 (by rfl) ⟨9057392, by rfl⟩ : syracuseStep 12076523 = 18114785) B18114785
theorem B98051867 : Blo 1256446 98051867 := bstep (se 1 (by rfl) ⟨73538900, by rfl⟩ : syracuseStep 98051867 = 147077801) B147077801
theorem B22956155 : Blo 1256446 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B9554759 : Blo 1256446 9554759 := bstep (se 1 (by rfl) ⟨7166069, by rfl⟩ : syracuseStep 9554759 = 14332139) B14332139
theorem B12897731 : Blo 1256446 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B14323391 : Blo 1256446 14323391 := bstep (se 1 (by rfl) ⟨10742543, by rfl⟩ : syracuseStep 14323391 = 21485087) B21485087
theorem B1257375 : Blo 1256446 1257375 := bstep (se 1 (by rfl) ⟨943031, by rfl⟩ : syracuseStep 1257375 = 1886063) B1886063
theorem B3182591 : Blo 1256446 3182591 := bstep (se 1 (by rfl) ⟨2386943, by rfl⟩ : syracuseStep 3182591 = 4773887) B4773887
theorem B1413607 : Blo 1256446 1413607 := bstep (se 1 (by rfl) ⟨1060205, by rfl⟩ : syracuseStep 1413607 = 2120411) B2120411
theorem B1258095 : Blo 1256446 1258095 := bstep (se 1 (by rfl) ⟨943571, by rfl⟩ : syracuseStep 1258095 = 1887143) B1887143
theorem B1414939 : Blo 1256446 1414939 := bstep (se 1 (by rfl) ⟨1061204, by rfl⟩ : syracuseStep 1414939 = 2122409) B2122409
theorem B15284639 : Blo 1256446 15284639 := bstep (se 1 (by rfl) ⟨11463479, by rfl⟩ : syracuseStep 15284639 = 22926959) B22926959
theorem B212032505 : Blo 1256446 212032505 := bstep (se 2 (by rfl) ⟨79512189, by rfl⟩ : syracuseStep 212032505 = 159024379) B159024379
theorem B40762673 : Blo 1256446 40762673 := bstep (se 2 (by rfl) ⟨15286002, by rfl⟩ : syracuseStep 40762673 = 30572005) B30572005
theorem B1884809 : Blo 1256446 1884809 := bstep (se 2 (by rfl) ⟨706803, by rfl⟩ : syracuseStep 1884809 = 1413607) B1413607
theorem B15304103 : Blo 1256446 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B141355003 : Blo 1256446 141355003 := bstep (se 1 (by rfl) ⟨106016252, by rfl⟩ : syracuseStep 141355003 = 212032505) B212032505
theorem B27175115 : Blo 1256446 27175115 := bstep (se 1 (by rfl) ⟨20381336, by rfl⟩ : syracuseStep 27175115 = 40762673) B40762673
theorem B1886585 : Blo 1256446 1886585 := bstep (se 2 (by rfl) ⟨707469, by rfl⟩ : syracuseStep 1886585 = 1414939) B1414939
theorem B6368057 : Blo 1256446 6368057 := bstep (se 2 (by rfl) ⟨2388021, by rfl⟩ : syracuseStep 6368057 = 4776043) B4776043
theorem B40759037 : Blo 1256446 40759037 := bstep (se 3 (by rfl) ⟨7642319, by rfl⟩ : syracuseStep 40759037 = 15284639) B15284639
theorem B65367911 : Blo 1256446 65367911 := bstep (se 1 (by rfl) ⟨49025933, by rfl⟩ : syracuseStep 65367911 = 98051867) B98051867
theorem B3223849 : Blo 1256446 3223849 := bstep (se 2 (by rfl) ⟨1208943, by rfl⟩ : syracuseStep 3223849 = 2417887) B2417887
theorem B6369839 : Blo 1256446 6369839 := bstep (se 1 (by rfl) ⟨4777379, by rfl⟩ : syracuseStep 6369839 = 9554759) B9554759
theorem B8598487 : Blo 1256446 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B9548927 : Blo 1256446 9548927 := bstep (se 1 (by rfl) ⟨7161695, by rfl⟩ : syracuseStep 9548927 = 14323391) B14323391
theorem B8051015 : Blo 1256446 8051015 := bstep (se 1 (by rfl) ⟨6038261, by rfl⟩ : syracuseStep 8051015 = 12076523) B12076523
theorem B2121727 : Blo 1256446 2121727 := bstep (se 1 (by rfl) ⟨1591295, by rfl⟩ : syracuseStep 2121727 = 3182591) B3182591
theorem B6365951 : Blo 1256446 6365951 := bstep (se 1 (by rfl) ⟨4774463, by rfl⟩ : syracuseStep 6365951 = 9548927) B9548927
theorem B5367343 : Blo 1256446 5367343 := bstep (se 1 (by rfl) ⟨4025507, by rfl⟩ : syracuseStep 5367343 = 8051015) B8051015
theorem B4245371 : Blo 1256446 4245371 := bstep (se 1 (by rfl) ⟨3184028, by rfl⟩ : syracuseStep 4245371 = 6368057) B6368057
theorem B2828969 : Blo 1256446 2828969 := bstep (se 2 (by rfl) ⟨1060863, by rfl⟩ : syracuseStep 2828969 = 2121727) B2121727
theorem B4246559 : Blo 1256446 4246559 := bstep (se 1 (by rfl) ⟨3184919, by rfl⟩ : syracuseStep 4246559 = 6369839) B6369839
theorem B1256539 : Blo 1256446 1256539 := bstep (se 1 (by rfl) ⟨942404, by rfl⟩ : syracuseStep 1256539 = 1884809) B1884809
theorem B10202735 : Blo 1256446 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B11464649 : Blo 1256446 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B18116743 : Blo 1256446 18116743 := bstep (se 1 (by rfl) ⟨13587557, by rfl⟩ : syracuseStep 18116743 = 27175115) B27175115
theorem B1257723 : Blo 1256446 1257723 := bstep (se 1 (by rfl) ⟨943292, by rfl⟩ : syracuseStep 1257723 = 1886585) B1886585
theorem B43578607 : Blo 1256446 43578607 := bstep (se 1 (by rfl) ⟨32683955, by rfl⟩ : syracuseStep 43578607 = 65367911) B65367911
theorem B4298465 : Blo 1256446 4298465 := bstep (se 2 (by rfl) ⟨1611924, by rfl⟩ : syracuseStep 4298465 = 3223849) B3223849
theorem B27172691 : Blo 1256446 27172691 := bstep (se 1 (by rfl) ⟨20379518, by rfl⟩ : syracuseStep 27172691 = 40759037) B40759037
theorem B188473337 : Blo 1256446 188473337 := bstep (se 2 (by rfl) ⟨70677501, by rfl⟩ : syracuseStep 188473337 = 141355003) B141355003
theorem B4243967 : Blo 1256446 4243967 := bstep (se 1 (by rfl) ⟨3182975, by rfl⟩ : syracuseStep 4243967 = 6365951) B6365951
theorem B1885979 : Blo 1256446 1885979 := bstep (se 1 (by rfl) ⟨1414484, by rfl⟩ : syracuseStep 1885979 = 2828969) B2828969
theorem B11462573 : Blo 1256446 11462573 := bstep (se 3 (by rfl) ⟨2149232, by rfl⟩ : syracuseStep 11462573 = 4298465) B4298465
theorem B6801823 : Blo 1256446 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B18115127 : Blo 1256446 18115127 := bstep (se 1 (by rfl) ⟨13586345, by rfl⟩ : syracuseStep 18115127 = 27172691) B27172691
theorem B2830247 : Blo 1256446 2830247 := bstep (se 1 (by rfl) ⟨2122685, by rfl⟩ : syracuseStep 2830247 = 4245371) B4245371
theorem B2831039 : Blo 1256446 2831039 := bstep (se 1 (by rfl) ⟨2123279, by rfl⟩ : syracuseStep 2831039 = 4246559) B4246559
theorem B7156457 : Blo 1256446 7156457 := bstep (se 2 (by rfl) ⟨2683671, by rfl⟩ : syracuseStep 7156457 = 5367343) B5367343
theorem B24155657 : Blo 1256446 24155657 := bstep (se 2 (by rfl) ⟨9058371, by rfl⟩ : syracuseStep 24155657 = 18116743) B18116743
theorem B58104809 : Blo 1256446 58104809 := bstep (se 2 (by rfl) ⟨21789303, by rfl⟩ : syracuseStep 58104809 = 43578607) B43578607
theorem B7643099 : Blo 1256446 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B125648891 : Blo 1256446 125648891 := bstep (se 1 (by rfl) ⟨94236668, by rfl⟩ : syracuseStep 125648891 = 188473337) B188473337
theorem B9069097 : Blo 1256446 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B12076751 : Blo 1256446 12076751 := bstep (se 1 (by rfl) ⟨9057563, by rfl⟩ : syracuseStep 12076751 = 18115127) B18115127
theorem B1886831 : Blo 1256446 1886831 := bstep (se 1 (by rfl) ⟨1415123, by rfl⟩ : syracuseStep 1886831 = 2830247) B2830247
theorem B83765927 : Blo 1256446 83765927 := bstep (se 1 (by rfl) ⟨62824445, by rfl⟩ : syracuseStep 83765927 = 125648891) B125648891
theorem B2829311 : Blo 1256446 2829311 := bstep (se 1 (by rfl) ⟨2121983, by rfl⟩ : syracuseStep 2829311 = 4243967) B4243967
theorem B1887359 : Blo 1256446 1887359 := bstep (se 1 (by rfl) ⟨1415519, by rfl⟩ : syracuseStep 1887359 = 2831039) B2831039
theorem B4770971 : Blo 1256446 4770971 := bstep (se 1 (by rfl) ⟨3578228, by rfl⟩ : syracuseStep 4770971 = 7156457) B7156457
theorem B1257319 : Blo 1256446 1257319 := bstep (se 1 (by rfl) ⟨942989, by rfl⟩ : syracuseStep 1257319 = 1885979) B1885979
theorem B38736539 : Blo 1256446 38736539 := bstep (se 1 (by rfl) ⟨29052404, by rfl⟩ : syracuseStep 38736539 = 58104809) B58104809
theorem B16103771 : Blo 1256446 16103771 := bstep (se 1 (by rfl) ⟨12077828, by rfl⟩ : syracuseStep 16103771 = 24155657) B24155657
theorem B7641715 : Blo 1256446 7641715 := bstep (se 1 (by rfl) ⟨5731286, by rfl⟩ : syracuseStep 7641715 = 11462573) B11462573
theorem B5095399 : Blo 1256446 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B12092129 : Blo 1256446 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B1886207 : Blo 1256446 1886207 := bstep (se 1 (by rfl) ⟨1414655, by rfl⟩ : syracuseStep 1886207 = 2829311) B2829311
theorem B3180647 : Blo 1256446 3180647 := bstep (se 1 (by rfl) ⟨2385485, by rfl⟩ : syracuseStep 3180647 = 4770971) B4770971
theorem B6793865 : Blo 1256446 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B25824359 : Blo 1256446 25824359 := bstep (se 1 (by rfl) ⟨19368269, by rfl⟩ : syracuseStep 25824359 = 38736539) B38736539
theorem B10735847 : Blo 1256446 10735847 := bstep (se 1 (by rfl) ⟨8051885, by rfl⟩ : syracuseStep 10735847 = 16103771) B16103771
theorem B1257887 : Blo 1256446 1257887 := bstep (se 1 (by rfl) ⟨943415, by rfl⟩ : syracuseStep 1257887 = 1886831) B1886831
theorem B223375805 : Blo 1256446 223375805 := bstep (se 3 (by rfl) ⟨41882963, by rfl⟩ : syracuseStep 223375805 = 83765927) B83765927
theorem B1258239 : Blo 1256446 1258239 := bstep (se 1 (by rfl) ⟨943679, by rfl⟩ : syracuseStep 1258239 = 1887359) B1887359
theorem B10188953 : Blo 1256446 10188953 := bstep (se 2 (by rfl) ⟨3820857, by rfl⟩ : syracuseStep 10188953 = 7641715) B7641715
theorem B8051167 : Blo 1256446 8051167 := bstep (se 1 (by rfl) ⟨6038375, by rfl⟩ : syracuseStep 8051167 = 12076751) B12076751
theorem B8061419 : Blo 1256446 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B6792635 : Blo 1256446 6792635 := bstep (se 1 (by rfl) ⟨5094476, by rfl⟩ : syracuseStep 6792635 = 10188953) B10188953
theorem B148917203 : Blo 1256446 148917203 := bstep (se 1 (by rfl) ⟨111687902, by rfl⟩ : syracuseStep 148917203 = 223375805) B223375805
theorem B10734889 : Blo 1256446 10734889 := bstep (se 2 (by rfl) ⟨4025583, by rfl⟩ : syracuseStep 10734889 = 8051167) B8051167
theorem B1257471 : Blo 1256446 1257471 := bstep (se 1 (by rfl) ⟨943103, by rfl⟩ : syracuseStep 1257471 = 1886207) B1886207
theorem B17216239 : Blo 1256446 17216239 := bstep (se 1 (by rfl) ⟨12912179, by rfl⟩ : syracuseStep 17216239 = 25824359) B25824359
theorem B7157231 : Blo 1256446 7157231 := bstep (se 1 (by rfl) ⟨5367923, by rfl⟩ : syracuseStep 7157231 = 10735847) B10735847
theorem B2120431 : Blo 1256446 2120431 := bstep (se 1 (by rfl) ⟨1590323, by rfl⟩ : syracuseStep 2120431 = 3180647) B3180647
theorem B4529243 : Blo 1256446 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B5374279 : Blo 1256446 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B2827241 : Blo 1256446 2827241 := bstep (se 2 (by rfl) ⟨1060215, by rfl⟩ : syracuseStep 2827241 = 2120431) B2120431
theorem B22954985 : Blo 1256446 22954985 := bstep (se 2 (by rfl) ⟨8608119, by rfl⟩ : syracuseStep 22954985 = 17216239) B17216239
theorem B14313185 : Blo 1256446 14313185 := bstep (se 2 (by rfl) ⟨5367444, by rfl⟩ : syracuseStep 14313185 = 10734889) B10734889
theorem B12077981 : Blo 1256446 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B4771487 : Blo 1256446 4771487 := bstep (se 1 (by rfl) ⟨3578615, by rfl⟩ : syracuseStep 4771487 = 7157231) B7157231
theorem B4528423 : Blo 1256446 4528423 := bstep (se 1 (by rfl) ⟨3396317, by rfl⟩ : syracuseStep 4528423 = 6792635) B6792635
theorem B99278135 : Blo 1256446 99278135 := bstep (se 1 (by rfl) ⟨74458601, by rfl⟩ : syracuseStep 99278135 = 148917203) B148917203
theorem B6037897 : Blo 1256446 6037897 := bstep (se 2 (by rfl) ⟨2264211, by rfl⟩ : syracuseStep 6037897 = 4528423) B4528423
theorem B1884827 : Blo 1256446 1884827 := bstep (se 1 (by rfl) ⟨1413620, by rfl⟩ : syracuseStep 1884827 = 2827241) B2827241
theorem B15303323 : Blo 1256446 15303323 := bstep (se 1 (by rfl) ⟨11477492, by rfl⟩ : syracuseStep 15303323 = 22954985) B22954985
theorem B66185423 : Blo 1256446 66185423 := bstep (se 1 (by rfl) ⟨49639067, by rfl⟩ : syracuseStep 66185423 = 99278135) B99278135
theorem B3180991 : Blo 1256446 3180991 := bstep (se 1 (by rfl) ⟨2385743, by rfl⟩ : syracuseStep 3180991 = 4771487) B4771487
theorem B7165705 : Blo 1256446 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B9542123 : Blo 1256446 9542123 := bstep (se 1 (by rfl) ⟨7156592, by rfl⟩ : syracuseStep 9542123 = 14313185) B14313185
theorem B8051987 : Blo 1256446 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B21471965 : Blo 1256446 21471965 := bstep (se 3 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 21471965 = 8051987) B8051987
theorem B44123615 : Blo 1256446 44123615 := bstep (se 1 (by rfl) ⟨33092711, by rfl⟩ : syracuseStep 44123615 = 66185423) B66185423
theorem B9554273 : Blo 1256446 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B1256551 : Blo 1256446 1256551 := bstep (se 1 (by rfl) ⟨942413, by rfl⟩ : syracuseStep 1256551 = 1884827) B1884827
theorem B10202215 : Blo 1256446 10202215 := bstep (se 1 (by rfl) ⟨7651661, by rfl⟩ : syracuseStep 10202215 = 15303323) B15303323
theorem B6361415 : Blo 1256446 6361415 := bstep (se 1 (by rfl) ⟨4771061, by rfl⟩ : syracuseStep 6361415 = 9542123) B9542123
theorem B8050529 : Blo 1256446 8050529 := bstep (se 2 (by rfl) ⟨3018948, by rfl⟩ : syracuseStep 8050529 = 6037897) B6037897
theorem B4241321 : Blo 1256446 4241321 := bstep (se 2 (by rfl) ⟨1590495, by rfl⟩ : syracuseStep 4241321 = 3180991) B3180991
theorem B5367019 : Blo 1256446 5367019 := bstep (se 1 (by rfl) ⟨4025264, by rfl⟩ : syracuseStep 5367019 = 8050529) B8050529
theorem B2827547 : Blo 1256446 2827547 := bstep (se 1 (by rfl) ⟨2120660, by rfl⟩ : syracuseStep 2827547 = 4241321) B4241321
theorem B14314643 : Blo 1256446 14314643 := bstep (se 1 (by rfl) ⟨10735982, by rfl⟩ : syracuseStep 14314643 = 21471965) B21471965
theorem B13602953 : Blo 1256446 13602953 := bstep (se 2 (by rfl) ⟨5101107, by rfl⟩ : syracuseStep 13602953 = 10202215) B10202215
theorem B6369515 : Blo 1256446 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B4240943 : Blo 1256446 4240943 := bstep (se 1 (by rfl) ⟨3180707, by rfl⟩ : syracuseStep 4240943 = 6361415) B6361415
theorem B29415743 : Blo 1256446 29415743 := bstep (se 1 (by rfl) ⟨22061807, by rfl⟩ : syracuseStep 29415743 = 44123615) B44123615
theorem B9068635 : Blo 1256446 9068635 := bstep (se 1 (by rfl) ⟨6801476, by rfl⟩ : syracuseStep 9068635 = 13602953) B13602953
theorem B1885031 : Blo 1256446 1885031 := bstep (se 1 (by rfl) ⟨1413773, by rfl⟩ : syracuseStep 1885031 = 2827547) B2827547
theorem B2827295 : Blo 1256446 2827295 := bstep (se 1 (by rfl) ⟨2120471, by rfl⟩ : syracuseStep 2827295 = 4240943) B4240943
theorem B4246343 : Blo 1256446 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B7156025 : Blo 1256446 7156025 := bstep (se 2 (by rfl) ⟨2683509, by rfl⟩ : syracuseStep 7156025 = 5367019) B5367019
theorem B19610495 : Blo 1256446 19610495 := bstep (se 1 (by rfl) ⟨14707871, by rfl⟩ : syracuseStep 19610495 = 29415743) B29415743
theorem B9543095 : Blo 1256446 9543095 := bstep (se 1 (by rfl) ⟨7157321, by rfl⟩ : syracuseStep 9543095 = 14314643) B14314643
theorem B12091513 : Blo 1256446 12091513 := bstep (se 2 (by rfl) ⟨4534317, by rfl⟩ : syracuseStep 12091513 = 9068635) B9068635
theorem B1884863 : Blo 1256446 1884863 := bstep (se 1 (by rfl) ⟨1413647, by rfl⟩ : syracuseStep 1884863 = 2827295) B2827295
theorem B4770683 : Blo 1256446 4770683 := bstep (se 1 (by rfl) ⟨3578012, by rfl⟩ : syracuseStep 4770683 = 7156025) B7156025
theorem B1256687 : Blo 1256446 1256687 := bstep (se 1 (by rfl) ⟨942515, by rfl⟩ : syracuseStep 1256687 = 1885031) B1885031
theorem B2830895 : Blo 1256446 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B6362063 : Blo 1256446 6362063 := bstep (se 1 (by rfl) ⟨4771547, by rfl⟩ : syracuseStep 6362063 = 9543095) B9543095
theorem B13073663 : Blo 1256446 13073663 := bstep (se 1 (by rfl) ⟨9805247, by rfl⟩ : syracuseStep 13073663 = 19610495) B19610495
theorem B16122017 : Blo 1256446 16122017 := bstep (se 2 (by rfl) ⟨6045756, by rfl⟩ : syracuseStep 16122017 = 12091513) B12091513
theorem B3180455 : Blo 1256446 3180455 := bstep (se 1 (by rfl) ⟨2385341, by rfl⟩ : syracuseStep 3180455 = 4770683) B4770683
theorem B1887263 : Blo 1256446 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B1256575 : Blo 1256446 1256575 := bstep (se 1 (by rfl) ⟨942431, by rfl⟩ : syracuseStep 1256575 = 1884863) B1884863
theorem B4241375 : Blo 1256446 4241375 := bstep (se 1 (by rfl) ⟨3181031, by rfl⟩ : syracuseStep 4241375 = 6362063) B6362063
theorem B34863101 : Blo 1256446 34863101 := bstep (se 3 (by rfl) ⟨6536831, by rfl⟩ : syracuseStep 34863101 = 13073663) B13073663
theorem B10748011 : Blo 1256446 10748011 := bstep (se 1 (by rfl) ⟨8061008, by rfl⟩ : syracuseStep 10748011 = 16122017) B16122017
theorem B2827583 : Blo 1256446 2827583 := bstep (se 1 (by rfl) ⟨2120687, by rfl⟩ : syracuseStep 2827583 = 4241375) B4241375
theorem B23242067 : Blo 1256446 23242067 := bstep (se 1 (by rfl) ⟨17431550, by rfl⟩ : syracuseStep 23242067 = 34863101) B34863101
theorem B1258175 : Blo 1256446 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B2120303 : Blo 1256446 2120303 := bstep (se 1 (by rfl) ⟨1590227, by rfl⟩ : syracuseStep 2120303 = 3180455) B3180455
theorem B1885055 : Blo 1256446 1885055 := bstep (se 1 (by rfl) ⟨1413791, by rfl⟩ : syracuseStep 1885055 = 2827583) B2827583
theorem B14330681 : Blo 1256446 14330681 := bstep (se 2 (by rfl) ⟨5374005, by rfl⟩ : syracuseStep 14330681 = 10748011) B10748011
theorem B991661525 : Blo 1256446 991661525 := bstep (se 7 (by rfl) ⟨11621033, by rfl⟩ : syracuseStep 991661525 = 23242067) B23242067
theorem B1413535 : Blo 1256446 1413535 := bstep (se 1 (by rfl) ⟨1060151, by rfl⟩ : syracuseStep 1413535 = 2120303) B2120303
theorem B1884713 : Blo 1256446 1884713 := bstep (se 2 (by rfl) ⟨706767, by rfl⟩ : syracuseStep 1884713 = 1413535) B1413535
theorem B9553787 : Blo 1256446 9553787 := bstep (se 1 (by rfl) ⟨7165340, by rfl⟩ : syracuseStep 9553787 = 14330681) B14330681
theorem B1256703 : Blo 1256446 1256703 := bstep (se 1 (by rfl) ⟨942527, by rfl⟩ : syracuseStep 1256703 = 1885055) B1885055
theorem B661107683 : Blo 1256446 661107683 := bstep (se 1 (by rfl) ⟨495830762, by rfl⟩ : syracuseStep 661107683 = 991661525) B991661525
theorem B440738455 : Blo 1256446 440738455 := bstep (se 1 (by rfl) ⟨330553841, by rfl⟩ : syracuseStep 440738455 = 661107683) B661107683
theorem B1256475 : Blo 1256446 1256475 := bstep (se 1 (by rfl) ⟨942356, by rfl⟩ : syracuseStep 1256475 = 1884713) B1884713
theorem B6369191 : Blo 1256446 6369191 := bstep (se 1 (by rfl) ⟨4776893, by rfl⟩ : syracuseStep 6369191 = 9553787) B9553787
theorem B4246127 : Blo 1256446 4246127 := bstep (se 1 (by rfl) ⟨3184595, by rfl⟩ : syracuseStep 4246127 = 6369191) B6369191
theorem B587651273 : Blo 1256446 587651273 := bstep (se 2 (by rfl) ⟨220369227, by rfl⟩ : syracuseStep 587651273 = 440738455) B440738455
theorem B391767515 : Blo 1256446 391767515 := bstep (se 1 (by rfl) ⟨293825636, by rfl⟩ : syracuseStep 391767515 = 587651273) B587651273
theorem B2830751 : Blo 1256446 2830751 := bstep (se 1 (by rfl) ⟨2123063, by rfl⟩ : syracuseStep 2830751 = 4246127) B4246127
theorem B261178343 : Blo 1256446 261178343 := bstep (se 1 (by rfl) ⟨195883757, by rfl⟩ : syracuseStep 261178343 = 391767515) B391767515
theorem B1887167 : Blo 1256446 1887167 := bstep (se 1 (by rfl) ⟨1415375, by rfl⟩ : syracuseStep 1887167 = 2830751) B2830751
theorem B1258111 : Blo 1256446 1258111 := bstep (se 1 (by rfl) ⟨943583, by rfl⟩ : syracuseStep 1258111 = 1887167) B1887167
theorem B174118895 : Blo 1256446 174118895 := bstep (se 1 (by rfl) ⟨130589171, by rfl⟩ : syracuseStep 174118895 = 261178343) B261178343
theorem B116079263 : Blo 1256446 116079263 := bstep (se 1 (by rfl) ⟨87059447, by rfl⟩ : syracuseStep 116079263 = 174118895) B174118895
theorem B77386175 : Blo 1256446 77386175 := bstep (se 1 (by rfl) ⟨58039631, by rfl⟩ : syracuseStep 77386175 = 116079263) B116079263
theorem B51590783 : Blo 1256446 51590783 := bstep (se 1 (by rfl) ⟨38693087, by rfl⟩ : syracuseStep 51590783 = 77386175) B77386175
theorem B34393855 : Blo 1256446 34393855 := bstep (se 1 (by rfl) ⟨25795391, by rfl⟩ : syracuseStep 34393855 = 51590783) B51590783
theorem B45858473 : Blo 1256446 45858473 := bstep (se 2 (by rfl) ⟨17196927, by rfl⟩ : syracuseStep 45858473 = 34393855) B34393855
theorem B30572315 : Blo 1256446 30572315 := bstep (se 1 (by rfl) ⟨22929236, by rfl⟩ : syracuseStep 30572315 = 45858473) B45858473
theorem B20381543 : Blo 1256446 20381543 := bstep (se 1 (by rfl) ⟨15286157, by rfl⟩ : syracuseStep 20381543 = 30572315) B30572315
theorem B13587695 : Blo 1256446 13587695 := bstep (se 1 (by rfl) ⟨10190771, by rfl⟩ : syracuseStep 13587695 = 20381543) B20381543
theorem B9058463 : Blo 1256446 9058463 := bstep (se 1 (by rfl) ⟨6793847, by rfl⟩ : syracuseStep 9058463 = 13587695) B13587695
theorem B6038975 : Blo 1256446 6038975 := bstep (se 1 (by rfl) ⟨4529231, by rfl⟩ : syracuseStep 6038975 = 9058463) B9058463
theorem B4025983 : Blo 1256446 4025983 := bstep (se 1 (by rfl) ⟨3019487, by rfl⟩ : syracuseStep 4025983 = 6038975) B6038975
theorem B5367977 : Blo 1256446 5367977 := bstep (se 2 (by rfl) ⟨2012991, by rfl⟩ : syracuseStep 5367977 = 4025983) B4025983
theorem B3578651 : Blo 1256446 3578651 := bstep (se 1 (by rfl) ⟨2683988, by rfl⟩ : syracuseStep 3578651 = 5367977) B5367977
theorem B2385767 : Blo 1256446 2385767 := bstep (se 1 (by rfl) ⟨1789325, by rfl⟩ : syracuseStep 2385767 = 3578651) B3578651
theorem B1590511 : Blo 1256446 1590511 := bstep (se 1 (by rfl) ⟨1192883, by rfl⟩ : syracuseStep 1590511 = 2385767) B2385767
theorem B2120681 : Blo 1256446 2120681 := bstep (se 2 (by rfl) ⟨795255, by rfl⟩ : syracuseStep 2120681 = 1590511) B1590511
theorem B1413787 : Blo 1256446 1413787 := bstep (se 1 (by rfl) ⟨1060340, by rfl⟩ : syracuseStep 1413787 = 2120681) B2120681
theorem B1885049 : Blo 1256446 1885049 := bstep (se 2 (by rfl) ⟨706893, by rfl⟩ : syracuseStep 1885049 = 1413787) B1413787
theorem B1256699 : Blo 1256446 1256699 := bstep (se 1 (by rfl) ⟨942524, by rfl⟩ : syracuseStep 1256699 = 1885049) B1885049

theorem C0 (j : ℕ) (h1 : 314111 ≤ j) (h2 : j ≤ 314610) : Blo 1256446 (4 * j + 3) := by
  interval_cases j
  · exact B1256447
  · exact B1256451
  · exact B1256455
  · exact B1256459
  · exact B1256463
  · exact B1256467
  · exact B1256471
  · exact B1256475
  · exact B1256479
  · exact B1256483
  · exact B1256487
  · exact B1256491
  · exact B1256495
  · exact B1256499
  · exact B1256503
  · exact B1256507
  · exact B1256511
  · exact B1256515
  · exact B1256519
  · exact B1256523
  · exact B1256527
  · exact B1256531
  · exact B1256535
  · exact B1256539
  · exact B1256543
  · exact B1256547
  · exact B1256551
  · exact B1256555
  · exact B1256559
  · exact B1256563
  · exact B1256567
  · exact B1256571
  · exact B1256575
  · exact B1256579
  · exact B1256583
  · exact B1256587
  · exact B1256591
  · exact B1256595
  · exact B1256599
  · exact B1256603
  · exact B1256607
  · exact B1256611
  · exact B1256615
  · exact B1256619
  · exact B1256623
  · exact B1256627
  · exact B1256631
  · exact B1256635
  · exact B1256639
  · exact B1256643
  · exact B1256647
  · exact B1256651
  · exact B1256655
  · exact B1256659
  · exact B1256663
  · exact B1256667
  · exact B1256671
  · exact B1256675
  · exact B1256679
  · exact B1256683
  · exact B1256687
  · exact B1256691
  · exact B1256695
  · exact B1256699
  · exact B1256703
  · exact B1256707
  · exact B1256711
  · exact B1256715
  · exact B1256719
  · exact B1256723
  · exact B1256727
  · exact B1256731
  · exact B1256735
  · exact B1256739
  · exact B1256743
  · exact B1256747
  · exact B1256751
  · exact B1256755
  · exact B1256759
  · exact B1256763
  · exact B1256767
  · exact B1256771
  · exact B1256775
  · exact B1256779
  · exact B1256783
  · exact B1256787
  · exact B1256791
  · exact B1256795
  · exact B1256799
  · exact B1256803
  · exact B1256807
  · exact B1256811
  · exact B1256815
  · exact B1256819
  · exact B1256823
  · exact B1256827
  · exact B1256831
  · exact B1256835
  · exact B1256839
  · exact B1256843
  · exact B1256847
  · exact B1256851
  · exact B1256855
  · exact B1256859
  · exact B1256863
  · exact B1256867
  · exact B1256871
  · exact B1256875
  · exact B1256879
  · exact B1256883
  · exact B1256887
  · exact B1256891
  · exact B1256895
  · exact B1256899
  · exact B1256903
  · exact B1256907
  · exact B1256911
  · exact B1256915
  · exact B1256919
  · exact B1256923
  · exact B1256927
  · exact B1256931
  · exact B1256935
  · exact B1256939
  · exact B1256943
  · exact B1256947
  · exact B1256951
  · exact B1256955
  · exact B1256959
  · exact B1256963
  · exact B1256967
  · exact B1256971
  · exact B1256975
  · exact B1256979
  · exact B1256983
  · exact B1256987
  · exact B1256991
  · exact B1256995
  · exact B1256999
  · exact B1257003
  · exact B1257007
  · exact B1257011
  · exact B1257015
  · exact B1257019
  · exact B1257023
  · exact B1257027
  · exact B1257031
  · exact B1257035
  · exact B1257039
  · exact B1257043
  · exact B1257047
  · exact B1257051
  · exact B1257055
  · exact B1257059
  · exact B1257063
  · exact B1257067
  · exact B1257071
  · exact B1257075
  · exact B1257079
  · exact B1257083
  · exact B1257087
  · exact B1257091
  · exact B1257095
  · exact B1257099
  · exact B1257103
  · exact B1257107
  · exact B1257111
  · exact B1257115
  · exact B1257119
  · exact B1257123
  · exact B1257127
  · exact B1257131
  · exact B1257135
  · exact B1257139
  · exact B1257143
  · exact B1257147
  · exact B1257151
  · exact B1257155
  · exact B1257159
  · exact B1257163
  · exact B1257167
  · exact B1257171
  · exact B1257175
  · exact B1257179
  · exact B1257183
  · exact B1257187
  · exact B1257191
  · exact B1257195
  · exact B1257199
  · exact B1257203
  · exact B1257207
  · exact B1257211
  · exact B1257215
  · exact B1257219
  · exact B1257223
  · exact B1257227
  · exact B1257231
  · exact B1257235
  · exact B1257239
  · exact B1257243
  · exact B1257247
  · exact B1257251
  · exact B1257255
  · exact B1257259
  · exact B1257263
  · exact B1257267
  · exact B1257271
  · exact B1257275
  · exact B1257279
  · exact B1257283
  · exact B1257287
  · exact B1257291
  · exact B1257295
  · exact B1257299
  · exact B1257303
  · exact B1257307
  · exact B1257311
  · exact B1257315
  · exact B1257319
  · exact B1257323
  · exact B1257327
  · exact B1257331
  · exact B1257335
  · exact B1257339
  · exact B1257343
  · exact B1257347
  · exact B1257351
  · exact B1257355
  · exact B1257359
  · exact B1257363
  · exact B1257367
  · exact B1257371
  · exact B1257375
  · exact B1257379
  · exact B1257383
  · exact B1257387
  · exact B1257391
  · exact B1257395
  · exact B1257399
  · exact B1257403
  · exact B1257407
  · exact B1257411
  · exact B1257415
  · exact B1257419
  · exact B1257423
  · exact B1257427
  · exact B1257431
  · exact B1257435
  · exact B1257439
  · exact B1257443
  · exact B1257447
  · exact B1257451
  · exact B1257455
  · exact B1257459
  · exact B1257463
  · exact B1257467
  · exact B1257471
  · exact B1257475
  · exact B1257479
  · exact B1257483
  · exact B1257487
  · exact B1257491
  · exact B1257495
  · exact B1257499
  · exact B1257503
  · exact B1257507
  · exact B1257511
  · exact B1257515
  · exact B1257519
  · exact B1257523
  · exact B1257527
  · exact B1257531
  · exact B1257535
  · exact B1257539
  · exact B1257543
  · exact B1257547
  · exact B1257551
  · exact B1257555
  · exact B1257559
  · exact B1257563
  · exact B1257567
  · exact B1257571
  · exact B1257575
  · exact B1257579
  · exact B1257583
  · exact B1257587
  · exact B1257591
  · exact B1257595
  · exact B1257599
  · exact B1257603
  · exact B1257607
  · exact B1257611
  · exact B1257615
  · exact B1257619
  · exact B1257623
  · exact B1257627
  · exact B1257631
  · exact B1257635
  · exact B1257639
  · exact B1257643
  · exact B1257647
  · exact B1257651
  · exact B1257655
  · exact B1257659
  · exact B1257663
  · exact B1257667
  · exact B1257671
  · exact B1257675
  · exact B1257679
  · exact B1257683
  · exact B1257687
  · exact B1257691
  · exact B1257695
  · exact B1257699
  · exact B1257703
  · exact B1257707
  · exact B1257711
  · exact B1257715
  · exact B1257719
  · exact B1257723
  · exact B1257727
  · exact B1257731
  · exact B1257735
  · exact B1257739
  · exact B1257743
  · exact B1257747
  · exact B1257751
  · exact B1257755
  · exact B1257759
  · exact B1257763
  · exact B1257767
  · exact B1257771
  · exact B1257775
  · exact B1257779
  · exact B1257783
  · exact B1257787
  · exact B1257791
  · exact B1257795
  · exact B1257799
  · exact B1257803
  · exact B1257807
  · exact B1257811
  · exact B1257815
  · exact B1257819
  · exact B1257823
  · exact B1257827
  · exact B1257831
  · exact B1257835
  · exact B1257839
  · exact B1257843
  · exact B1257847
  · exact B1257851
  · exact B1257855
  · exact B1257859
  · exact B1257863
  · exact B1257867
  · exact B1257871
  · exact B1257875
  · exact B1257879
  · exact B1257883
  · exact B1257887
  · exact B1257891
  · exact B1257895
  · exact B1257899
  · exact B1257903
  · exact B1257907
  · exact B1257911
  · exact B1257915
  · exact B1257919
  · exact B1257923
  · exact B1257927
  · exact B1257931
  · exact B1257935
  · exact B1257939
  · exact B1257943
  · exact B1257947
  · exact B1257951
  · exact B1257955
  · exact B1257959
  · exact B1257963
  · exact B1257967
  · exact B1257971
  · exact B1257975
  · exact B1257979
  · exact B1257983
  · exact B1257987
  · exact B1257991
  · exact B1257995
  · exact B1257999
  · exact B1258003
  · exact B1258007
  · exact B1258011
  · exact B1258015
  · exact B1258019
  · exact B1258023
  · exact B1258027
  · exact B1258031
  · exact B1258035
  · exact B1258039
  · exact B1258043
  · exact B1258047
  · exact B1258051
  · exact B1258055
  · exact B1258059
  · exact B1258063
  · exact B1258067
  · exact B1258071
  · exact B1258075
  · exact B1258079
  · exact B1258083
  · exact B1258087
  · exact B1258091
  · exact B1258095
  · exact B1258099
  · exact B1258103
  · exact B1258107
  · exact B1258111
  · exact B1258115
  · exact B1258119
  · exact B1258123
  · exact B1258127
  · exact B1258131
  · exact B1258135
  · exact B1258139
  · exact B1258143
  · exact B1258147
  · exact B1258151
  · exact B1258155
  · exact B1258159
  · exact B1258163
  · exact B1258167
  · exact B1258171
  · exact B1258175
  · exact B1258179
  · exact B1258183
  · exact B1258187
  · exact B1258191
  · exact B1258195
  · exact B1258199
  · exact B1258203
  · exact B1258207
  · exact B1258211
  · exact B1258215
  · exact B1258219
  · exact B1258223
  · exact B1258227
  · exact B1258231
  · exact B1258235
  · exact B1258239
  · exact B1258243
  · exact B1258247
  · exact B1258251
  · exact B1258255
  · exact B1258259
  · exact B1258263
  · exact B1258267
  · exact B1258271
  · exact B1258275
  · exact B1258279
  · exact B1258283
  · exact B1258287
  · exact B1258291
  · exact B1258295
  · exact B1258299
  · exact B1258303
  · exact B1258307
  · exact B1258311
  · exact B1258315
  · exact B1258319
  · exact B1258323
  · exact B1258327
  · exact B1258331
  · exact B1258335
  · exact B1258339
  · exact B1258343
  · exact B1258347
  · exact B1258351
  · exact B1258355
  · exact B1258359
  · exact B1258363
  · exact B1258367
  · exact B1258371
  · exact B1258375
  · exact B1258379
  · exact B1258383
  · exact B1258387
  · exact B1258391
  · exact B1258395
  · exact B1258399
  · exact B1258403
  · exact B1258407
  · exact B1258411
  · exact B1258415
  · exact B1258419
  · exact B1258423
  · exact B1258427
  · exact B1258431
  · exact B1258435
  · exact B1258439
  · exact B1258443

theorem solution (m : ℕ) (hlo : 1256446 ≤ m) (hhi : m ≤ 1258446) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 314111 ≤ j := by omega
    have hj2 : j ≤ 314610 := by omega
    have hb : Blo 1256446 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
