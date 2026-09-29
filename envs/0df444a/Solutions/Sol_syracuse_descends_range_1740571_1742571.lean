-- Prove2me | solution 1 for syracuse_descends_range_1740571_1742571
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:34:07.861923+00:00
-- url     : https://prove2.me/submissions/b8f2a096-1bf5-4213-a7c8-2a15ad45db51

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


theorem B2613269 : Blo 1740571 2613269 := bbase (se 6 (by rfl) ⟨61248, by rfl⟩ : syracuseStep 2613269 = 122497) (by norm_num)
theorem B2203681 : Blo 1740571 2203681 := bbase (se 2 (by rfl) ⟨826380, by rfl⟩ : syracuseStep 2203681 = 1652761) (by norm_num)
theorem B2613293 : Blo 1740571 2613293 := bbase (se 3 (by rfl) ⟨489992, by rfl⟩ : syracuseStep 2613293 = 979985) (by norm_num)
theorem B6610997 : Blo 1740571 6610997 := bbase (se 5 (by rfl) ⟨309890, by rfl⟩ : syracuseStep 6610997 = 619781) (by norm_num)
theorem B6275141 : Blo 1740571 6275141 := bbase (se 4 (by rfl) ⟨588294, by rfl⟩ : syracuseStep 6275141 = 1176589) (by norm_num)
theorem B2613317 : Blo 1740571 2613317 := bbase (se 4 (by rfl) ⟨244998, by rfl⟩ : syracuseStep 2613317 = 489997) (by norm_num)
theorem B2613341 : Blo 1740571 2613341 := bbase (se 3 (by rfl) ⟨490001, by rfl⟩ : syracuseStep 2613341 = 980003) (by norm_num)
theorem B2613365 : Blo 1740571 2613365 := bbase (se 5 (by rfl) ⟨122501, by rfl⟩ : syracuseStep 2613365 = 245003) (by norm_num)
theorem B2203777 : Blo 1740571 2203777 := bbase (se 2 (by rfl) ⟨826416, by rfl⟩ : syracuseStep 2203777 = 1652833) (by norm_num)
theorem B2613389 : Blo 1740571 2613389 := bbase (se 3 (by rfl) ⟨490010, by rfl⟩ : syracuseStep 2613389 = 980021) (by norm_num)
theorem B1884313 : Blo 1740571 1884313 := bbase (se 2 (by rfl) ⟨706617, by rfl⟩ : syracuseStep 1884313 = 1413235) (by norm_num)
theorem B2613413 : Blo 1740571 2613413 := bbase (se 4 (by rfl) ⟨245007, by rfl⟩ : syracuseStep 2613413 = 490015) (by norm_num)
theorem B2613437 : Blo 1740571 2613437 := bbase (se 3 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 2613437 = 980039) (by norm_num)
theorem B4407493 : Blo 1740571 4407493 := bbase (se 4 (by rfl) ⟨413202, by rfl⟩ : syracuseStep 4407493 = 826405) (by norm_num)
theorem B2613461 : Blo 1740571 2613461 := bbase (se 7 (by rfl) ⟨30626, by rfl⟩ : syracuseStep 2613461 = 61253) (by norm_num)
theorem B2613485 : Blo 1740571 2613485 := bbase (se 3 (by rfl) ⟨490028, by rfl⟩ : syracuseStep 2613485 = 980057) (by norm_num)
theorem B2613509 : Blo 1740571 2613509 := bbase (se 4 (by rfl) ⟨245016, by rfl⟩ : syracuseStep 2613509 = 490033) (by norm_num)
theorem B1958161 : Blo 1740571 1958161 := bbase (se 2 (by rfl) ⟨734310, by rfl⟩ : syracuseStep 1958161 = 1468621) (by norm_num)
theorem B3350813 : Blo 1740571 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B1859869 : Blo 1740571 1859869 := bbase (se 3 (by rfl) ⟨348725, by rfl⟩ : syracuseStep 1859869 = 697451) (by norm_num)
theorem B2613533 : Blo 1740571 2613533 := bbase (se 3 (by rfl) ⟨490037, by rfl⟩ : syracuseStep 2613533 = 980075) (by norm_num)
theorem B4186397 : Blo 1740571 4186397 := bbase (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) (by norm_num)
theorem B2203949 : Blo 1740571 2203949 := bbase (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) (by norm_num)
theorem B1958197 : Blo 1740571 1958197 := bbase (se 5 (by rfl) ⟨91790, by rfl⟩ : syracuseStep 1958197 = 183581) (by norm_num)
theorem B4407605 : Blo 1740571 4407605 := bbase (se 5 (by rfl) ⟨206606, by rfl⟩ : syracuseStep 4407605 = 413213) (by norm_num)
theorem B2613557 : Blo 1740571 2613557 := bbase (se 5 (by rfl) ⟨122510, by rfl⟩ : syracuseStep 2613557 = 245021) (by norm_num)
theorem B2613581 : Blo 1740571 2613581 := bbase (se 3 (by rfl) ⟨490046, by rfl⟩ : syracuseStep 2613581 = 980093) (by norm_num)
theorem B19833173 : Blo 1740571 19833173 := bbase (se 10 (by rfl) ⟨29052, by rfl⟩ : syracuseStep 19833173 = 58105) (by norm_num)
theorem B1958233 : Blo 1740571 1958233 := bbase (se 2 (by rfl) ⟨734337, by rfl⟩ : syracuseStep 1958233 = 1468675) (by norm_num)
theorem B2204005 : Blo 1740571 2204005 := bbase (se 4 (by rfl) ⟨206625, by rfl⟩ : syracuseStep 2204005 = 413251) (by norm_num)
theorem B1859941 : Blo 1740571 1859941 := bbase (se 4 (by rfl) ⟨174369, by rfl⟩ : syracuseStep 1859941 = 348739) (by norm_num)
theorem B2613605 : Blo 1740571 2613605 := bbase (se 4 (by rfl) ⟨245025, by rfl⟩ : syracuseStep 2613605 = 490051) (by norm_num)
theorem B3719533 : Blo 1740571 3719533 := bbase (se 3 (by rfl) ⟨697412, by rfl⟩ : syracuseStep 3719533 = 1394825) (by norm_num)
theorem B1958269 : Blo 1740571 1958269 := bbase (se 3 (by rfl) ⟨367175, by rfl⟩ : syracuseStep 1958269 = 734351) (by norm_num)
theorem B2613629 : Blo 1740571 2613629 := bbase (se 3 (by rfl) ⟨490055, by rfl⟩ : syracuseStep 2613629 = 980111) (by norm_num)
theorem B2613653 : Blo 1740571 2613653 := bbase (se 6 (by rfl) ⟨61257, by rfl⟩ : syracuseStep 2613653 = 122515) (by norm_num)
theorem B1958305 : Blo 1740571 1958305 := bbase (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) (by norm_num)
theorem B2613677 : Blo 1740571 2613677 := bbase (se 3 (by rfl) ⟨490064, by rfl⟩ : syracuseStep 2613677 = 980129) (by norm_num)
theorem B1958341 : Blo 1740571 1958341 := bbase (se 4 (by rfl) ⟨183594, by rfl⟩ : syracuseStep 1958341 = 367189) (by norm_num)
theorem B2204101 : Blo 1740571 2204101 := bbase (se 4 (by rfl) ⟨206634, by rfl⟩ : syracuseStep 2204101 = 413269) (by norm_num)
theorem B2613701 : Blo 1740571 2613701 := bbase (se 4 (by rfl) ⟨245034, by rfl⟩ : syracuseStep 2613701 = 490069) (by norm_num)
theorem B2613725 : Blo 1740571 2613725 := bbase (se 3 (by rfl) ⟨490073, by rfl⟩ : syracuseStep 2613725 = 980147) (by norm_num)
theorem B1958377 : Blo 1740571 1958377 := bbase (se 2 (by rfl) ⟨734391, by rfl⟩ : syracuseStep 1958377 = 1468783) (by norm_num)
theorem B4407797 : Blo 1740571 4407797 := bbase (se 5 (by rfl) ⟨206615, by rfl⟩ : syracuseStep 4407797 = 413231) (by norm_num)
theorem B2613749 : Blo 1740571 2613749 := bbase (se 5 (by rfl) ⟨122519, by rfl⟩ : syracuseStep 2613749 = 245039) (by norm_num)
theorem B3719677 : Blo 1740571 3719677 := bbase (se 3 (by rfl) ⟨697439, by rfl⟩ : syracuseStep 3719677 = 1394879) (by norm_num)
theorem B4956677 : Blo 1740571 4956677 := bbase (se 4 (by rfl) ⟨464688, by rfl⟩ : syracuseStep 4956677 = 929377) (by norm_num)
theorem B1958413 : Blo 1740571 1958413 := bbase (se 3 (by rfl) ⟨367202, by rfl⟩ : syracuseStep 1958413 = 734405) (by norm_num)
theorem B2613773 : Blo 1740571 2613773 := bbase (se 3 (by rfl) ⟨490082, by rfl⟩ : syracuseStep 2613773 = 980165) (by norm_num)
theorem B1860121 : Blo 1740571 1860121 := bbase (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) (by norm_num)
theorem B2613797 : Blo 1740571 2613797 := bbase (se 4 (by rfl) ⟨245043, by rfl⟩ : syracuseStep 2613797 = 490087) (by norm_num)
theorem B1958449 : Blo 1740571 1958449 := bbase (se 2 (by rfl) ⟨734418, by rfl⟩ : syracuseStep 1958449 = 1468837) (by norm_num)
theorem B3916349 : Blo 1740571 3916349 := bbase (se 3 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 3916349 = 1468631) (by norm_num)
theorem B2613821 : Blo 1740571 2613821 := bbase (se 3 (by rfl) ⟨490091, by rfl⟩ : syracuseStep 2613821 = 980183) (by norm_num)
theorem B33456725 : Blo 1740571 33456725 := bbase (se 8 (by rfl) ⟨196035, by rfl⟩ : syracuseStep 33456725 = 392071) (by norm_num)
theorem B1958485 : Blo 1740571 1958485 := bbase (se 8 (by rfl) ⟨11475, by rfl⟩ : syracuseStep 1958485 = 22951) (by norm_num)
theorem B2613845 : Blo 1740571 2613845 := bbase (se 8 (by rfl) ⟨15315, by rfl⟩ : syracuseStep 2613845 = 30631) (by norm_num)
theorem B3531365 : Blo 1740571 3531365 := bbase (se 4 (by rfl) ⟨331065, by rfl⟩ : syracuseStep 3531365 = 662131) (by norm_num)
theorem B2204273 : Blo 1740571 2204273 := bbase (se 2 (by rfl) ⟨826602, by rfl⟩ : syracuseStep 2204273 = 1653205) (by norm_num)
theorem B1958521 : Blo 1740571 1958521 := bbase (se 2 (by rfl) ⟨734445, by rfl⟩ : syracuseStep 1958521 = 1468891) (by norm_num)
theorem B3916421 : Blo 1740571 3916421 := bbase (se 4 (by rfl) ⟨367164, by rfl⟩ : syracuseStep 3916421 = 734329) (by norm_num)
theorem B8938133 : Blo 1740571 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B1958557 : Blo 1740571 1958557 := bbase (se 3 (by rfl) ⟨367229, by rfl⟩ : syracuseStep 1958557 = 734459) (by norm_num)
theorem B3138205 : Blo 1740571 3138205 := bbase (se 3 (by rfl) ⟨588413, by rfl⟩ : syracuseStep 3138205 = 1176827) (by norm_num)
theorem B2204329 : Blo 1740571 2204329 := bbase (se 2 (by rfl) ⟨826623, by rfl⟩ : syracuseStep 2204329 = 1653247) (by norm_num)
theorem B1958593 : Blo 1740571 1958593 := bbase (se 2 (by rfl) ⟨734472, by rfl⟩ : syracuseStep 1958593 = 1468945) (by norm_num)
theorem B3916493 : Blo 1740571 3916493 := bbase (se 3 (by rfl) ⟨734342, by rfl⟩ : syracuseStep 3916493 = 1468685) (by norm_num)
theorem B4186829 : Blo 1740571 4186829 := bbase (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) (by norm_num)
theorem B3973853 : Blo 1740571 3973853 := bbase (se 3 (by rfl) ⟨745097, by rfl⟩ : syracuseStep 3973853 = 1490195) (by norm_num)
theorem B1958629 : Blo 1740571 1958629 := bbase (se 4 (by rfl) ⟨183621, by rfl⟩ : syracuseStep 1958629 = 367243) (by norm_num)
theorem B3138277 : Blo 1740571 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B1958665 : Blo 1740571 1958665 := bbase (se 2 (by rfl) ⟨734499, by rfl⟩ : syracuseStep 1958665 = 1468999) (by norm_num)
theorem B2204425 : Blo 1740571 2204425 := bbase (se 2 (by rfl) ⟨826659, by rfl⟩ : syracuseStep 2204425 = 1653319) (by norm_num)
theorem B3916565 : Blo 1740571 3916565 := bbase (se 6 (by rfl) ⟨91794, by rfl⟩ : syracuseStep 3916565 = 183589) (by norm_num)
theorem B1958701 : Blo 1740571 1958701 := bbase (se 3 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 1958701 = 734513) (by norm_num)
theorem B4408141 : Blo 1740571 4408141 := bbase (se 3 (by rfl) ⟨826526, by rfl⟩ : syracuseStep 4408141 = 1653053) (by norm_num)
theorem B1958737 : Blo 1740571 1958737 := bbase (se 2 (by rfl) ⟨734526, by rfl⟩ : syracuseStep 1958737 = 1469053) (by norm_num)
theorem B3916637 : Blo 1740571 3916637 := bbase (se 3 (by rfl) ⟨734369, by rfl⟩ : syracuseStep 3916637 = 1468739) (by norm_num)
theorem B3973981 : Blo 1740571 3973981 := bbase (se 3 (by rfl) ⟨745121, by rfl⟩ : syracuseStep 3973981 = 1490243) (by norm_num)
theorem B5808997 : Blo 1740571 5808997 := bbase (se 4 (by rfl) ⟨544593, by rfl⟩ : syracuseStep 5808997 = 1089187) (by norm_num)
theorem B5956453 : Blo 1740571 5956453 := bbase (se 4 (by rfl) ⟨558417, by rfl⟩ : syracuseStep 5956453 = 1116835) (by norm_num)
theorem B1958773 : Blo 1740571 1958773 := bbase (se 5 (by rfl) ⟨91817, by rfl⟩ : syracuseStep 1958773 = 183635) (by norm_num)
theorem B3138421 : Blo 1740571 3138421 := bbase (se 5 (by rfl) ⟨147113, by rfl⟩ : syracuseStep 3138421 = 294227) (by norm_num)
theorem B3720053 : Blo 1740571 3720053 := bbase (se 5 (by rfl) ⟨174377, by rfl⟩ : syracuseStep 3720053 = 348755) (by norm_num)
theorem B1958809 : Blo 1740571 1958809 := bbase (se 2 (by rfl) ⟨734553, by rfl⟩ : syracuseStep 1958809 = 1469107) (by norm_num)
theorem B3916709 : Blo 1740571 3916709 := bbase (se 4 (by rfl) ⟨367191, by rfl⟩ : syracuseStep 3916709 = 734383) (by norm_num)
theorem B4957109 : Blo 1740571 4957109 := bbase (se 5 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 4957109 = 464729) (by norm_num)
theorem B2204597 : Blo 1740571 2204597 := bbase (se 5 (by rfl) ⟨103340, by rfl⟩ : syracuseStep 2204597 = 206681) (by norm_num)
theorem B1958845 : Blo 1740571 1958845 := bbase (se 3 (by rfl) ⟨367283, by rfl⟩ : syracuseStep 1958845 = 734567) (by norm_num)
theorem B4408253 : Blo 1740571 4408253 := bbase (se 3 (by rfl) ⟨826547, by rfl⟩ : syracuseStep 4408253 = 1653095) (by norm_num)
theorem B1860565 : Blo 1740571 1860565 := bbase (se 7 (by rfl) ⟨21803, by rfl⟩ : syracuseStep 1860565 = 43607) (by norm_num)
theorem B1958881 : Blo 1740571 1958881 := bbase (se 2 (by rfl) ⟨734580, by rfl⟩ : syracuseStep 1958881 = 1469161) (by norm_num)
theorem B3916781 : Blo 1740571 3916781 := bbase (se 3 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 3916781 = 1468793) (by norm_num)
theorem B2204653 : Blo 1740571 2204653 := bbase (se 3 (by rfl) ⟨413372, by rfl⟩ : syracuseStep 2204653 = 826745) (by norm_num)
theorem B1958917 : Blo 1740571 1958917 := bbase (se 4 (by rfl) ⟨183648, by rfl⟩ : syracuseStep 1958917 = 367297) (by norm_num)
theorem B1958953 : Blo 1740571 1958953 := bbase (se 2 (by rfl) ⟨734607, by rfl⟩ : syracuseStep 1958953 = 1469215) (by norm_num)
theorem B3916853 : Blo 1740571 3916853 := bbase (se 5 (by rfl) ⟨183602, by rfl⟩ : syracuseStep 3916853 = 367205) (by norm_num)
theorem B1958989 : Blo 1740571 1958989 := bbase (se 3 (by rfl) ⟨367310, by rfl⟩ : syracuseStep 1958989 = 734621) (by norm_num)
theorem B2204749 : Blo 1740571 2204749 := bbase (se 3 (by rfl) ⟨413390, by rfl⟩ : syracuseStep 2204749 = 826781) (by norm_num)
theorem B1860689 : Blo 1740571 1860689 := bbase (se 2 (by rfl) ⟨697758, by rfl⟩ : syracuseStep 1860689 = 1395517) (by norm_num)
theorem B1959025 : Blo 1740571 1959025 := bbase (se 2 (by rfl) ⟨734634, by rfl⟩ : syracuseStep 1959025 = 1469269) (by norm_num)
theorem B3916925 : Blo 1740571 3916925 := bbase (se 3 (by rfl) ⟨734423, by rfl⟩ : syracuseStep 3916925 = 1468847) (by norm_num)
theorem B4408445 : Blo 1740571 4408445 := bbase (se 3 (by rfl) ⟨826583, by rfl⟩ : syracuseStep 4408445 = 1653167) (by norm_num)
theorem B5874821 : Blo 1740571 5874821 := bbase (se 4 (by rfl) ⟨550764, by rfl⟩ : syracuseStep 5874821 = 1101529) (by norm_num)
theorem B1959061 : Blo 1740571 1959061 := bbase (se 6 (by rfl) ⟨45915, by rfl⟩ : syracuseStep 1959061 = 91831) (by norm_num)
theorem B1959097 : Blo 1740571 1959097 := bbase (se 2 (by rfl) ⟨734661, by rfl⟩ : syracuseStep 1959097 = 1469323) (by norm_num)
theorem B3916997 : Blo 1740571 3916997 := bbase (se 4 (by rfl) ⟨367218, by rfl⟩ : syracuseStep 3916997 = 734437) (by norm_num)
theorem B1959133 : Blo 1740571 1959133 := bbase (se 3 (by rfl) ⟨367337, by rfl⟩ : syracuseStep 1959133 = 734675) (by norm_num)
theorem B3720421 : Blo 1740571 3720421 := bbase (se 4 (by rfl) ⟨348789, by rfl⟩ : syracuseStep 3720421 = 697579) (by norm_num)
theorem B1885421 : Blo 1740571 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B13231349 : Blo 1740571 13231349 := bbase (se 5 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 13231349 = 1240439) (by norm_num)
theorem B2204921 : Blo 1740571 2204921 := bbase (se 2 (by rfl) ⟨826845, by rfl⟩ : syracuseStep 2204921 = 1653691) (by norm_num)
theorem B1959169 : Blo 1740571 1959169 := bbase (se 2 (by rfl) ⟨734688, by rfl⟩ : syracuseStep 1959169 = 1469377) (by norm_num)
theorem B8815877 : Blo 1740571 8815877 := bbase (se 4 (by rfl) ⟨826488, by rfl⟩ : syracuseStep 8815877 = 1652977) (by norm_num)
theorem B3917069 : Blo 1740571 3917069 := bbase (se 3 (by rfl) ⟨734450, by rfl⟩ : syracuseStep 3917069 = 1468901) (by norm_num)
theorem B1959205 : Blo 1740571 1959205 := bbase (se 4 (by rfl) ⟨183675, by rfl⟩ : syracuseStep 1959205 = 367351) (by norm_num)
theorem B2204977 : Blo 1740571 2204977 := bbase (se 2 (by rfl) ⟨826866, by rfl⟩ : syracuseStep 2204977 = 1653733) (by norm_num)
theorem B1959241 : Blo 1740571 1959241 := bbase (se 2 (by rfl) ⟨734715, by rfl⟩ : syracuseStep 1959241 = 1469431) (by norm_num)
theorem B3917141 : Blo 1740571 3917141 := bbase (se 12 (by rfl) ⟨1434, by rfl⟩ : syracuseStep 3917141 = 2869) (by norm_num)
theorem B1959277 : Blo 1740571 1959277 := bbase (se 3 (by rfl) ⟨367364, by rfl⟩ : syracuseStep 1959277 = 734729) (by norm_num)
theorem B1959313 : Blo 1740571 1959313 := bbase (se 2 (by rfl) ⟨734742, by rfl⟩ : syracuseStep 1959313 = 1469485) (by norm_num)
theorem B2205073 : Blo 1740571 2205073 := bbase (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) (by norm_num)
theorem B3917213 : Blo 1740571 3917213 := bbase (se 3 (by rfl) ⟨734477, by rfl⟩ : syracuseStep 3917213 = 1468955) (by norm_num)
theorem B1959349 : Blo 1740571 1959349 := bbase (se 5 (by rfl) ⟨91844, by rfl⟩ : syracuseStep 1959349 = 183689) (by norm_num)
theorem B4408789 : Blo 1740571 4408789 := bbase (se 7 (by rfl) ⟨51665, by rfl⟩ : syracuseStep 4408789 = 103331) (by norm_num)
theorem B1959385 : Blo 1740571 1959385 := bbase (se 2 (by rfl) ⟨734769, by rfl⟩ : syracuseStep 1959385 = 1469539) (by norm_num)
theorem B3917285 : Blo 1740571 3917285 := bbase (se 4 (by rfl) ⟨367245, by rfl⟩ : syracuseStep 3917285 = 734491) (by norm_num)
theorem B1959421 : Blo 1740571 1959421 := bbase (se 3 (by rfl) ⟨367391, by rfl⟩ : syracuseStep 1959421 = 734783) (by norm_num)
theorem B1959457 : Blo 1740571 1959457 := bbase (se 2 (by rfl) ⟨734796, by rfl⟩ : syracuseStep 1959457 = 1469593) (by norm_num)
theorem B3917357 : Blo 1740571 3917357 := bbase (se 3 (by rfl) ⟨734504, by rfl⟩ : syracuseStep 3917357 = 1469009) (by norm_num)
theorem B5875253 : Blo 1740571 5875253 := bbase (se 5 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 5875253 = 550805) (by norm_num)
theorem B2205245 : Blo 1740571 2205245 := bbase (se 3 (by rfl) ⟨413483, by rfl⟩ : syracuseStep 2205245 = 826967) (by norm_num)
theorem B1959493 : Blo 1740571 1959493 := bbase (se 4 (by rfl) ⟨183702, by rfl⟩ : syracuseStep 1959493 = 367405) (by norm_num)
theorem B4408901 : Blo 1740571 4408901 := bbase (se 4 (by rfl) ⟨413334, by rfl⟩ : syracuseStep 4408901 = 826669) (by norm_num)
theorem B28231253 : Blo 1740571 28231253 := bbase (se 8 (by rfl) ⟨165417, by rfl⟩ : syracuseStep 28231253 = 330835) (by norm_num)
theorem B1959529 : Blo 1740571 1959529 := bbase (se 2 (by rfl) ⟨734823, by rfl⟩ : syracuseStep 1959529 = 1469647) (by norm_num)
theorem B3917429 : Blo 1740571 3917429 := bbase (se 5 (by rfl) ⟨183629, by rfl⟩ : syracuseStep 3917429 = 367259) (by norm_num)
theorem B2205301 : Blo 1740571 2205301 := bbase (se 5 (by rfl) ⟨103373, by rfl⟩ : syracuseStep 2205301 = 206747) (by norm_num)
theorem B1959565 : Blo 1740571 1959565 := bbase (se 3 (by rfl) ⟨367418, by rfl⟩ : syracuseStep 1959565 = 734837) (by norm_num)
theorem B13223573 : Blo 1740571 13223573 := bbase (se 6 (by rfl) ⟨309927, by rfl⟩ : syracuseStep 13223573 = 619855) (by norm_num)
theorem B3139229 : Blo 1740571 3139229 := bbase (se 3 (by rfl) ⟨588605, by rfl⟩ : syracuseStep 3139229 = 1177211) (by norm_num)
theorem B4957861 : Blo 1740571 4957861 := bbase (se 4 (by rfl) ⟨464799, by rfl⟩ : syracuseStep 4957861 = 929599) (by norm_num)
theorem B1959601 : Blo 1740571 1959601 := bbase (se 2 (by rfl) ⟨734850, by rfl⟩ : syracuseStep 1959601 = 1469701) (by norm_num)
theorem B3917501 : Blo 1740571 3917501 := bbase (se 3 (by rfl) ⟨734531, by rfl⟩ : syracuseStep 3917501 = 1469063) (by norm_num)
theorem B1959637 : Blo 1740571 1959637 := bbase (se 7 (by rfl) ⟨22964, by rfl⟩ : syracuseStep 1959637 = 45929) (by norm_num)
theorem B3139285 : Blo 1740571 3139285 := bbase (se 7 (by rfl) ⟨36788, by rfl⟩ : syracuseStep 3139285 = 73577) (by norm_num)
theorem B2205397 : Blo 1740571 2205397 := bbase (se 7 (by rfl) ⟨25844, by rfl⟩ : syracuseStep 2205397 = 51689) (by norm_num)
theorem B1959673 : Blo 1740571 1959673 := bbase (se 2 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 1959673 = 1469755) (by norm_num)
theorem B2828029 : Blo 1740571 2828029 := bbase (se 3 (by rfl) ⟨530255, by rfl⟩ : syracuseStep 2828029 = 1060511) (by norm_num)
theorem B3917573 : Blo 1740571 3917573 := bbase (se 4 (by rfl) ⟨367272, by rfl⟩ : syracuseStep 3917573 = 734545) (by norm_num)
theorem B4409093 : Blo 1740571 4409093 := bbase (se 4 (by rfl) ⟨413352, by rfl⟩ : syracuseStep 4409093 = 826705) (by norm_num)
theorem B1959709 : Blo 1740571 1959709 := bbase (se 3 (by rfl) ⟨367445, by rfl⟩ : syracuseStep 1959709 = 734891) (by norm_num)
theorem B3139373 : Blo 1740571 3139373 := bbase (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) (by norm_num)
theorem B1959745 : Blo 1740571 1959745 := bbase (se 2 (by rfl) ⟨734904, by rfl⟩ : syracuseStep 1959745 = 1469809) (by norm_num)
theorem B3917645 : Blo 1740571 3917645 := bbase (se 3 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 3917645 = 1469117) (by norm_num)
theorem B1959781 : Blo 1740571 1959781 := bbase (se 4 (by rfl) ⟨183729, by rfl⟩ : syracuseStep 1959781 = 367459) (by norm_num)
theorem B10594165 : Blo 1740571 10594165 := bbase (se 5 (by rfl) ⟨496601, by rfl⟩ : syracuseStep 10594165 = 993203) (by norm_num)
theorem B1959817 : Blo 1740571 1959817 := bbase (se 2 (by rfl) ⟨734931, by rfl⟩ : syracuseStep 1959817 = 1469863) (by norm_num)
theorem B3917717 : Blo 1740571 3917717 := bbase (se 6 (by rfl) ⟨91821, by rfl⟩ : syracuseStep 3917717 = 183643) (by norm_num)
theorem B1959853 : Blo 1740571 1959853 := bbase (se 3 (by rfl) ⟨367472, by rfl⟩ : syracuseStep 1959853 = 734945) (by norm_num)
theorem B1959889 : Blo 1740571 1959889 := bbase (se 2 (by rfl) ⟨734958, by rfl⟩ : syracuseStep 1959889 = 1469917) (by norm_num)
theorem B3917789 : Blo 1740571 3917789 := bbase (se 3 (by rfl) ⟨734585, by rfl⟩ : syracuseStep 3917789 = 1469171) (by norm_num)
theorem B5875685 : Blo 1740571 5875685 := bbase (se 4 (by rfl) ⟨550845, by rfl⟩ : syracuseStep 5875685 = 1101691) (by norm_num)
theorem B1959925 : Blo 1740571 1959925 := bbase (se 5 (by rfl) ⟨91871, by rfl⟩ : syracuseStep 1959925 = 183743) (by norm_num)
theorem B1959961 : Blo 1740571 1959961 := bbase (se 2 (by rfl) ⟨734985, by rfl⟩ : syracuseStep 1959961 = 1469971) (by norm_num)
theorem B3917861 : Blo 1740571 3917861 := bbase (se 4 (by rfl) ⟨367299, by rfl⟩ : syracuseStep 3917861 = 734599) (by norm_num)
theorem B1959997 : Blo 1740571 1959997 := bbase (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) (by norm_num)
theorem B3139661 : Blo 1740571 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B4409437 : Blo 1740571 4409437 := bbase (se 3 (by rfl) ⟨826769, by rfl⟩ : syracuseStep 4409437 = 1653539) (by norm_num)
theorem B1960033 : Blo 1740571 1960033 := bbase (se 2 (by rfl) ⟨735012, by rfl⟩ : syracuseStep 1960033 = 1470025) (by norm_num)
theorem B3917933 : Blo 1740571 3917933 := bbase (se 3 (by rfl) ⟨734612, by rfl⟩ : syracuseStep 3917933 = 1469225) (by norm_num)
theorem B6613109 : Blo 1740571 6613109 := bbase (se 5 (by rfl) ⟨309989, by rfl⟩ : syracuseStep 6613109 = 619979) (by norm_num)
theorem B2648189 : Blo 1740571 2648189 := bbase (se 3 (by rfl) ⟨496535, by rfl⟩ : syracuseStep 2648189 = 993071) (by norm_num)
theorem B1960069 : Blo 1740571 1960069 := bbase (se 4 (by rfl) ⟨183756, by rfl⟩ : syracuseStep 1960069 = 367513) (by norm_num)
theorem B1960105 : Blo 1740571 1960105 := bbase (se 2 (by rfl) ⟨735039, by rfl⟩ : syracuseStep 1960105 = 1470079) (by norm_num)
theorem B3918005 : Blo 1740571 3918005 := bbase (se 5 (by rfl) ⟨183656, by rfl⟩ : syracuseStep 3918005 = 367313) (by norm_num)
theorem B4409549 : Blo 1740571 4409549 := bbase (se 3 (by rfl) ⟨826790, by rfl⟩ : syracuseStep 4409549 = 1653581) (by norm_num)
theorem B1960141 : Blo 1740571 1960141 := bbase (se 3 (by rfl) ⟨367526, by rfl⟩ : syracuseStep 1960141 = 735053) (by norm_num)
theorem B3139805 : Blo 1740571 3139805 := bbase (se 3 (by rfl) ⟨588713, by rfl⟩ : syracuseStep 3139805 = 1177427) (by norm_num)
theorem B1960177 : Blo 1740571 1960177 := bbase (se 2 (by rfl) ⟨735066, by rfl⟩ : syracuseStep 1960177 = 1470133) (by norm_num)
theorem B3918077 : Blo 1740571 3918077 := bbase (se 3 (by rfl) ⟨734639, by rfl⟩ : syracuseStep 3918077 = 1469279) (by norm_num)
theorem B1960213 : Blo 1740571 1960213 := bbase (se 6 (by rfl) ⟨45942, by rfl⟩ : syracuseStep 1960213 = 91885) (by norm_num)
theorem B1960249 : Blo 1740571 1960249 := bbase (se 2 (by rfl) ⟨735093, by rfl⟩ : syracuseStep 1960249 = 1470187) (by norm_num)
theorem B3918149 : Blo 1740571 3918149 := bbase (se 4 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 3918149 = 734653) (by norm_num)
theorem B2091353 : Blo 1740571 2091353 := bbase (se 2 (by rfl) ⟨784257, by rfl⟩ : syracuseStep 2091353 = 1568515) (by norm_num)
theorem B1960285 : Blo 1740571 1960285 := bbase (se 3 (by rfl) ⟨367553, by rfl⟩ : syracuseStep 1960285 = 735107) (by norm_num)
theorem B2091377 : Blo 1740571 2091377 := bbase (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) (by norm_num)
theorem B1960321 : Blo 1740571 1960321 := bbase (se 2 (by rfl) ⟨735120, by rfl⟩ : syracuseStep 1960321 = 1470241) (by norm_num)
theorem B3918221 : Blo 1740571 3918221 := bbase (se 3 (by rfl) ⟨734666, by rfl⟩ : syracuseStep 3918221 = 1469333) (by norm_num)
theorem B4409741 : Blo 1740571 4409741 := bbase (se 3 (by rfl) ⟨826826, by rfl⟩ : syracuseStep 4409741 = 1653653) (by norm_num)
theorem B5876117 : Blo 1740571 5876117 := bbase (se 6 (by rfl) ⟨137721, by rfl⟩ : syracuseStep 5876117 = 275443) (by norm_num)
theorem B6613397 : Blo 1740571 6613397 := bbase (se 6 (by rfl) ⟨155001, by rfl⟩ : syracuseStep 6613397 = 310003) (by norm_num)
theorem B1960357 : Blo 1740571 1960357 := bbase (se 4 (by rfl) ⟨183783, by rfl⟩ : syracuseStep 1960357 = 367567) (by norm_num)
theorem B1960393 : Blo 1740571 1960393 := bbase (se 2 (by rfl) ⟨735147, by rfl⟩ : syracuseStep 1960393 = 1470295) (by norm_num)
theorem B3918293 : Blo 1740571 3918293 := bbase (se 7 (by rfl) ⟨45917, by rfl⟩ : syracuseStep 3918293 = 91835) (by norm_num)
theorem B3140093 : Blo 1740571 3140093 := bbase (se 3 (by rfl) ⟨588767, by rfl⟩ : syracuseStep 3140093 = 1177535) (by norm_num)
theorem B8817173 : Blo 1740571 8817173 := bbase (se 6 (by rfl) ⟨206652, by rfl⟩ : syracuseStep 8817173 = 413305) (by norm_num)
theorem B3918365 : Blo 1740571 3918365 := bbase (se 3 (by rfl) ⟨734693, by rfl⟩ : syracuseStep 3918365 = 1469387) (by norm_num)
theorem B5655109 : Blo 1740571 5655109 := bbase (se 4 (by rfl) ⟨530166, by rfl⟩ : syracuseStep 5655109 = 1060333) (by norm_num)
theorem B3140165 : Blo 1740571 3140165 := bbase (se 4 (by rfl) ⟨294390, by rfl⟩ : syracuseStep 3140165 = 588781) (by norm_num)
theorem B3820117 : Blo 1740571 3820117 := bbase (se 8 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 3820117 = 44767) (by norm_num)
theorem B3918437 : Blo 1740571 3918437 := bbase (se 4 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 3918437 = 734707) (by norm_num)
theorem B16738933 : Blo 1740571 16738933 := bbase (se 5 (by rfl) ⟨784637, by rfl⟩ : syracuseStep 16738933 = 1569275) (by norm_num)
theorem B2091685 : Blo 1740571 2091685 := bbase (se 4 (by rfl) ⟨196095, by rfl⟩ : syracuseStep 2091685 = 392191) (by norm_num)
theorem B3918509 : Blo 1740571 3918509 := bbase (se 3 (by rfl) ⟨734720, by rfl⟩ : syracuseStep 3918509 = 1469441) (by norm_num)
theorem B32197333 : Blo 1740571 32197333 := bbase (se 7 (by rfl) ⟨377312, by rfl⟩ : syracuseStep 32197333 = 754625) (by norm_num)
theorem B4410085 : Blo 1740571 4410085 := bbase (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) (by norm_num)
theorem B3918581 : Blo 1740571 3918581 := bbase (se 5 (by rfl) ⟨183683, by rfl⟩ : syracuseStep 3918581 = 367367) (by norm_num)
theorem B3918653 : Blo 1740571 3918653 := bbase (se 3 (by rfl) ⟨734747, by rfl⟩ : syracuseStep 3918653 = 1469495) (by norm_num)
theorem B5876549 : Blo 1740571 5876549 := bbase (se 4 (by rfl) ⟨550926, by rfl⟩ : syracuseStep 5876549 = 1101853) (by norm_num)
theorem B5294917 : Blo 1740571 5294917 := bbase (se 4 (by rfl) ⟨496398, by rfl⟩ : syracuseStep 5294917 = 992797) (by norm_num)
theorem B2091857 : Blo 1740571 2091857 := bbase (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) (by norm_num)
theorem B4410197 : Blo 1740571 4410197 := bbase (se 9 (by rfl) ⟨12920, by rfl⟩ : syracuseStep 4410197 = 25841) (by norm_num)
theorem B7441253 : Blo 1740571 7441253 := bbase (se 4 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 7441253 = 1395235) (by norm_num)
theorem B5581669 : Blo 1740571 5581669 := bbase (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) (by norm_num)
theorem B3918725 : Blo 1740571 3918725 := bbase (se 4 (by rfl) ⟨367380, by rfl⟩ : syracuseStep 3918725 = 734761) (by norm_num)
theorem B2788285 : Blo 1740571 2788285 := bbase (se 3 (by rfl) ⟨522803, by rfl⟩ : syracuseStep 2788285 = 1045607) (by norm_num)
theorem B2091973 : Blo 1740571 2091973 := bbase (se 4 (by rfl) ⟨196122, by rfl⟩ : syracuseStep 2091973 = 392245) (by norm_num)
theorem B3918797 : Blo 1740571 3918797 := bbase (se 3 (by rfl) ⟨734774, by rfl⟩ : syracuseStep 3918797 = 1469549) (by norm_num)
theorem B3304405 : Blo 1740571 3304405 := bbase (se 7 (by rfl) ⟨38723, by rfl⟩ : syracuseStep 3304405 = 77447) (by norm_num)
theorem B3918869 : Blo 1740571 3918869 := bbase (se 6 (by rfl) ⟨91848, by rfl⟩ : syracuseStep 3918869 = 183697) (by norm_num)
theorem B4410389 : Blo 1740571 4410389 := bbase (se 6 (by rfl) ⟨103368, by rfl⟩ : syracuseStep 4410389 = 206737) (by norm_num)
theorem B1764385 : Blo 1740571 1764385 := bbase (se 2 (by rfl) ⟨661644, by rfl⟩ : syracuseStep 1764385 = 1323289) (by norm_num)
theorem B2092069 : Blo 1740571 2092069 := bbase (se 4 (by rfl) ⟨196131, by rfl⟩ : syracuseStep 2092069 = 392263) (by norm_num)
theorem B4467773 : Blo 1740571 4467773 := bbase (se 3 (by rfl) ⟨837707, by rfl⟩ : syracuseStep 4467773 = 1675415) (by norm_num)
theorem B3918941 : Blo 1740571 3918941 := bbase (se 3 (by rfl) ⟨734801, by rfl⟩ : syracuseStep 3918941 = 1469603) (by norm_num)
theorem B7441541 : Blo 1740571 7441541 := bbase (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) (by norm_num)
theorem B3919013 : Blo 1740571 3919013 := bbase (se 4 (by rfl) ⟨367407, by rfl⟩ : syracuseStep 3919013 = 734815) (by norm_num)
theorem B2092213 : Blo 1740571 2092213 := bbase (se 5 (by rfl) ⟨98072, by rfl⟩ : syracuseStep 2092213 = 196145) (by norm_num)
theorem B1985737 : Blo 1740571 1985737 := bbase (se 2 (by rfl) ⟨744651, by rfl⟩ : syracuseStep 1985737 = 1489303) (by norm_num)
theorem B3919085 : Blo 1740571 3919085 := bbase (se 3 (by rfl) ⟨734828, by rfl⟩ : syracuseStep 3919085 = 1469657) (by norm_num)
theorem B5876981 : Blo 1740571 5876981 := bbase (se 5 (by rfl) ⟨275483, by rfl⟩ : syracuseStep 5876981 = 550967) (by norm_num)
theorem B3304709 : Blo 1740571 3304709 := bbase (se 4 (by rfl) ⟨309816, by rfl⟩ : syracuseStep 3304709 = 619633) (by norm_num)
theorem B3919157 : Blo 1740571 3919157 := bbase (se 5 (by rfl) ⟨183710, by rfl⟩ : syracuseStep 3919157 = 367421) (by norm_num)
theorem B6278485 : Blo 1740571 6278485 := bbase (se 11 (by rfl) ⟨4598, by rfl⟩ : syracuseStep 6278485 = 9197) (by norm_num)
theorem B4410733 : Blo 1740571 4410733 := bbase (se 3 (by rfl) ⟨827012, by rfl⟩ : syracuseStep 4410733 = 1654025) (by norm_num)
theorem B2788733 : Blo 1740571 2788733 := bbase (se 3 (by rfl) ⟨522887, by rfl⟩ : syracuseStep 2788733 = 1045775) (by norm_num)
theorem B3919229 : Blo 1740571 3919229 := bbase (se 3 (by rfl) ⟨734855, by rfl⟩ : syracuseStep 3919229 = 1469711) (by norm_num)
theorem B1985977 : Blo 1740571 1985977 := bbase (se 2 (by rfl) ⟨744741, by rfl⟩ : syracuseStep 1985977 = 1489483) (by norm_num)
theorem B3919301 : Blo 1740571 3919301 := bbase (se 4 (by rfl) ⟨367434, by rfl⟩ : syracuseStep 3919301 = 734869) (by norm_num)
theorem B4410845 : Blo 1740571 4410845 := bbase (se 3 (by rfl) ⟨827033, by rfl⟩ : syracuseStep 4410845 = 1654067) (by norm_num)
theorem B3919373 : Blo 1740571 3919373 := bbase (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) (by norm_num)
theorem B25120277 : Blo 1740571 25120277 := bbase (se 6 (by rfl) ⟨588756, by rfl⟩ : syracuseStep 25120277 = 1177513) (by norm_num)
theorem B6614581 : Blo 1740571 6614581 := bbase (se 5 (by rfl) ⟨310058, by rfl⟩ : syracuseStep 6614581 = 620117) (by norm_num)
theorem B3919445 : Blo 1740571 3919445 := bbase (se 8 (by rfl) ⟨22965, by rfl⟩ : syracuseStep 3919445 = 45931) (by norm_num)
theorem B3919517 : Blo 1740571 3919517 := bbase (se 3 (by rfl) ⟨734909, by rfl⟩ : syracuseStep 3919517 = 1469819) (by norm_num)
theorem B5877413 : Blo 1740571 5877413 := bbase (se 4 (by rfl) ⟨551007, by rfl⟩ : syracuseStep 5877413 = 1102015) (by norm_num)
theorem B3919589 : Blo 1740571 3919589 := bbase (se 4 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 3919589 = 734923) (by norm_num)
theorem B12553973 : Blo 1740571 12553973 := bbase (se 5 (by rfl) ⟨588467, by rfl⟩ : syracuseStep 12553973 = 1176935) (by norm_num)
theorem B8818469 : Blo 1740571 8818469 := bbase (se 4 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 8818469 = 1653463) (by norm_num)
theorem B3919661 : Blo 1740571 3919661 := bbase (se 3 (by rfl) ⟨734936, by rfl⟩ : syracuseStep 3919661 = 1469873) (by norm_num)
theorem B4706117 : Blo 1740571 4706117 := bbase (se 4 (by rfl) ⟨441198, by rfl⟩ : syracuseStep 4706117 = 882397) (by norm_num)
theorem B6614885 : Blo 1740571 6614885 := bbase (se 4 (by rfl) ⟨620145, by rfl⟩ : syracuseStep 6614885 = 1240291) (by norm_num)
theorem B3919733 : Blo 1740571 3919733 := bbase (se 5 (by rfl) ⟨183737, by rfl⟩ : syracuseStep 3919733 = 367475) (by norm_num)
theorem B7442293 : Blo 1740571 7442293 := bbase (se 5 (by rfl) ⟨348857, by rfl⟩ : syracuseStep 7442293 = 697715) (by norm_num)
theorem B1986433 : Blo 1740571 1986433 := bbase (se 2 (by rfl) ⟨744912, by rfl⟩ : syracuseStep 1986433 = 1489825) (by norm_num)
theorem B3919805 : Blo 1740571 3919805 := bbase (se 3 (by rfl) ⟨734963, by rfl⟩ : syracuseStep 3919805 = 1469927) (by norm_num)
theorem B3305461 : Blo 1740571 3305461 := bbase (se 5 (by rfl) ⟨154943, by rfl⟩ : syracuseStep 3305461 = 309887) (by norm_num)
theorem B3919877 : Blo 1740571 3919877 := bbase (se 4 (by rfl) ⟨367488, by rfl⟩ : syracuseStep 3919877 = 734977) (by norm_num)
theorem B8368181 : Blo 1740571 8368181 := bbase (se 5 (by rfl) ⟨392258, by rfl⟩ : syracuseStep 8368181 = 784517) (by norm_num)
theorem B3919949 : Blo 1740571 3919949 := bbase (se 3 (by rfl) ⟨734990, by rfl⟩ : syracuseStep 3919949 = 1469981) (by norm_num)
theorem B4182101 : Blo 1740571 4182101 := bbase (se 8 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 4182101 = 49009) (by norm_num)
theorem B5877845 : Blo 1740571 5877845 := bbase (se 8 (by rfl) ⟨34440, by rfl⟩ : syracuseStep 5877845 = 68881) (by norm_num)
theorem B20385877 : Blo 1740571 20385877 := bbase (se 8 (by rfl) ⟨119448, by rfl⟩ : syracuseStep 20385877 = 238897) (by norm_num)
theorem B14872693 : Blo 1740571 14872693 := bbase (se 5 (by rfl) ⟨697157, by rfl⟩ : syracuseStep 14872693 = 1394315) (by norm_num)
theorem B3305605 : Blo 1740571 3305605 := bbase (se 4 (by rfl) ⟨309900, by rfl⟩ : syracuseStep 3305605 = 619801) (by norm_num)
theorem B3920021 : Blo 1740571 3920021 := bbase (se 6 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 3920021 = 183751) (by norm_num)
theorem B18116821 : Blo 1740571 18116821 := bbase (se 7 (by rfl) ⟨212306, by rfl⟩ : syracuseStep 18116821 = 424613) (by norm_num)
theorem B3920093 : Blo 1740571 3920093 := bbase (se 3 (by rfl) ⟨735017, by rfl⟩ : syracuseStep 3920093 = 1470035) (by norm_num)
theorem B1765621 : Blo 1740571 1765621 := bbase (se 5 (by rfl) ⟨82763, by rfl⟩ : syracuseStep 1765621 = 165527) (by norm_num)
theorem B4182293 : Blo 1740571 4182293 := bbase (se 6 (by rfl) ⟨98022, by rfl⟩ : syracuseStep 4182293 = 196045) (by norm_num)
theorem B3305765 : Blo 1740571 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B3920165 : Blo 1740571 3920165 := bbase (se 4 (by rfl) ⟨367515, by rfl⟩ : syracuseStep 3920165 = 735031) (by norm_num)
theorem B3920237 : Blo 1740571 3920237 := bbase (se 3 (by rfl) ⟨735044, by rfl⟩ : syracuseStep 3920237 = 1470089) (by norm_num)
theorem B2937269 : Blo 1740571 2937269 := bbase (se 5 (by rfl) ⟨137684, by rfl⟩ : syracuseStep 2937269 = 275369) (by norm_num)
theorem B3305909 : Blo 1740571 3305909 := bbase (se 5 (by rfl) ⟨154964, by rfl⟩ : syracuseStep 3305909 = 309929) (by norm_num)
theorem B3920309 : Blo 1740571 3920309 := bbase (se 5 (by rfl) ⟨183764, by rfl⟩ : syracuseStep 3920309 = 367529) (by norm_num)
theorem B4960709 : Blo 1740571 4960709 := bbase (se 4 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 4960709 = 930133) (by norm_num)
theorem B3920381 : Blo 1740571 3920381 := bbase (se 3 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 3920381 = 1470143) (by norm_num)
theorem B5878277 : Blo 1740571 5878277 := bbase (se 4 (by rfl) ⟨551088, by rfl⟩ : syracuseStep 5878277 = 1102177) (by norm_num)
theorem B21172757 : Blo 1740571 21172757 := bbase (se 6 (by rfl) ⟨496236, by rfl⟩ : syracuseStep 21172757 = 992473) (by norm_num)
theorem B2937397 : Blo 1740571 2937397 := bbase (se 5 (by rfl) ⟨137690, by rfl⟩ : syracuseStep 2937397 = 275381) (by norm_num)
theorem B3920453 : Blo 1740571 3920453 := bbase (se 4 (by rfl) ⟨367542, by rfl⟩ : syracuseStep 3920453 = 735085) (by norm_num)
theorem B7443029 : Blo 1740571 7443029 := bbase (se 8 (by rfl) ⟨43611, by rfl⟩ : syracuseStep 7443029 = 87223) (by norm_num)
theorem B2937485 : Blo 1740571 2937485 := bbase (se 3 (by rfl) ⟨550778, by rfl⟩ : syracuseStep 2937485 = 1101557) (by norm_num)
theorem B3920525 : Blo 1740571 3920525 := bbase (se 3 (by rfl) ⟨735098, by rfl⟩ : syracuseStep 3920525 = 1470197) (by norm_num)
theorem B3306197 : Blo 1740571 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B3920597 : Blo 1740571 3920597 := bbase (se 7 (by rfl) ⟨45944, by rfl⟩ : syracuseStep 3920597 = 91889) (by norm_num)
theorem B2937613 : Blo 1740571 2937613 := bbase (se 3 (by rfl) ⟨550802, by rfl⟩ : syracuseStep 2937613 = 1101605) (by norm_num)
theorem B3920669 : Blo 1740571 3920669 := bbase (se 3 (by rfl) ⟨735125, by rfl⟩ : syracuseStep 3920669 = 1470251) (by norm_num)
theorem B1766237 : Blo 1740571 1766237 := bbase (se 3 (by rfl) ⟨331169, by rfl⟩ : syracuseStep 1766237 = 662339) (by norm_num)
theorem B2937701 : Blo 1740571 2937701 := bbase (se 4 (by rfl) ⟨275409, by rfl⟩ : syracuseStep 2937701 = 550819) (by norm_num)
theorem B2790245 : Blo 1740571 2790245 := bbase (se 4 (by rfl) ⟨261585, by rfl⟩ : syracuseStep 2790245 = 523171) (by norm_num)
theorem B3920741 : Blo 1740571 3920741 := bbase (se 4 (by rfl) ⟨367569, by rfl⟩ : syracuseStep 3920741 = 735139) (by norm_num)
theorem B3306349 : Blo 1740571 3306349 := bbase (se 3 (by rfl) ⟨619940, by rfl⟩ : syracuseStep 3306349 = 1239881) (by norm_num)
theorem B11154293 : Blo 1740571 11154293 := bbase (se 5 (by rfl) ⟨522857, by rfl⟩ : syracuseStep 11154293 = 1045715) (by norm_num)
theorem B5878709 : Blo 1740571 5878709 := bbase (se 5 (by rfl) ⟨275564, by rfl⟩ : syracuseStep 5878709 = 551129) (by norm_num)
theorem B2937829 : Blo 1740571 2937829 := bbase (se 4 (by rfl) ⟨275421, by rfl⟩ : syracuseStep 2937829 = 550843) (by norm_num)
theorem B2790373 : Blo 1740571 2790373 := bbase (se 4 (by rfl) ⟨261597, by rfl⟩ : syracuseStep 2790373 = 523195) (by norm_num)
theorem B7435253 : Blo 1740571 7435253 := bbase (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) (by norm_num)
theorem B8819765 : Blo 1740571 8819765 := bbase (se 5 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 8819765 = 826853) (by norm_num)
theorem B2937917 : Blo 1740571 2937917 := bbase (se 3 (by rfl) ⟨550859, by rfl⟩ : syracuseStep 2937917 = 1101719) (by norm_num)
theorem B3822661 : Blo 1740571 3822661 := bbase (se 4 (by rfl) ⟨358374, by rfl⟩ : syracuseStep 3822661 = 716749) (by norm_num)
theorem B2479261 : Blo 1740571 2479261 := bbase (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) (by norm_num)
theorem B3306653 : Blo 1740571 3306653 := bbase (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) (by norm_num)
theorem B2938045 : Blo 1740571 2938045 := bbase (se 3 (by rfl) ⟨550883, by rfl⟩ : syracuseStep 2938045 = 1101767) (by norm_num)
theorem B4183253 : Blo 1740571 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B4469989 : Blo 1740571 4469989 := bbase (se 4 (by rfl) ⟨419061, by rfl⟩ : syracuseStep 4469989 = 838123) (by norm_num)
theorem B2938133 : Blo 1740571 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B3970405 : Blo 1740571 3970405 := bbase (se 4 (by rfl) ⟨372225, by rfl⟩ : syracuseStep 3970405 = 744451) (by norm_num)
theorem B5879141 : Blo 1740571 5879141 := bbase (se 4 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 5879141 = 1102339) (by norm_num)
theorem B2938261 : Blo 1740571 2938261 := bbase (se 6 (by rfl) ⟨68865, by rfl⟩ : syracuseStep 2938261 = 137731) (by norm_num)
theorem B8811989 : Blo 1740571 8811989 := bbase (se 7 (by rfl) ⟨103265, by rfl⟩ : syracuseStep 8811989 = 206531) (by norm_num)
theorem B9917909 : Blo 1740571 9917909 := bbase (se 7 (by rfl) ⟨116225, by rfl⟩ : syracuseStep 9917909 = 232451) (by norm_num)
theorem B2938349 : Blo 1740571 2938349 := bbase (se 3 (by rfl) ⟨550940, by rfl⟩ : syracuseStep 2938349 = 1101881) (by norm_num)
theorem B4961893 : Blo 1740571 4961893 := bbase (se 4 (by rfl) ⟨465177, by rfl⟩ : syracuseStep 4961893 = 930355) (by norm_num)
theorem B2938477 : Blo 1740571 2938477 := bbase (se 3 (by rfl) ⟨550964, by rfl⟩ : syracuseStep 2938477 = 1101929) (by norm_num)
theorem B3061373 : Blo 1740571 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B2610869 : Blo 1740571 2610869 := bbase (se 5 (by rfl) ⟨122384, by rfl⟩ : syracuseStep 2610869 = 244769) (by norm_num)
theorem B2938565 : Blo 1740571 2938565 := bbase (se 4 (by rfl) ⟨275490, by rfl⟩ : syracuseStep 2938565 = 550981) (by norm_num)
theorem B5297861 : Blo 1740571 5297861 := bbase (se 4 (by rfl) ⟨496674, by rfl⟩ : syracuseStep 5297861 = 993349) (by norm_num)
theorem B2610893 : Blo 1740571 2610893 := bbase (se 3 (by rfl) ⟨489542, by rfl⟩ : syracuseStep 2610893 = 979085) (by norm_num)
theorem B2610917 : Blo 1740571 2610917 := bbase (se 4 (by rfl) ⟨244773, by rfl⟩ : syracuseStep 2610917 = 489547) (by norm_num)
theorem B2479853 : Blo 1740571 2479853 := bbase (se 3 (by rfl) ⟨464972, by rfl⟩ : syracuseStep 2479853 = 929945) (by norm_num)
theorem B2610941 : Blo 1740571 2610941 := bbase (se 3 (by rfl) ⟨489551, by rfl⟩ : syracuseStep 2610941 = 979103) (by norm_num)
theorem B4962053 : Blo 1740571 4962053 := bbase (se 4 (by rfl) ⟨465192, by rfl⟩ : syracuseStep 4962053 = 930385) (by norm_num)
theorem B2610965 : Blo 1740571 2610965 := bbase (se 6 (by rfl) ⟨61194, by rfl⟩ : syracuseStep 2610965 = 122389) (by norm_num)
theorem B5879573 : Blo 1740571 5879573 := bbase (se 6 (by rfl) ⟨137802, by rfl⟩ : syracuseStep 5879573 = 275605) (by norm_num)
theorem B17880853 : Blo 1740571 17880853 := bbase (se 6 (by rfl) ⟨419082, by rfl⟩ : syracuseStep 17880853 = 838165) (by norm_num)
theorem B2610989 : Blo 1740571 2610989 := bbase (se 3 (by rfl) ⟨489560, by rfl⟩ : syracuseStep 2610989 = 979121) (by norm_num)
theorem B2479933 : Blo 1740571 2479933 := bbase (se 3 (by rfl) ⟨464987, by rfl⟩ : syracuseStep 2479933 = 929975) (by norm_num)
theorem B2611013 : Blo 1740571 2611013 := bbase (se 4 (by rfl) ⟨244782, by rfl⟩ : syracuseStep 2611013 = 489565) (by norm_num)
theorem B2938693 : Blo 1740571 2938693 := bbase (se 4 (by rfl) ⟨275502, by rfl⟩ : syracuseStep 2938693 = 551005) (by norm_num)
theorem B2611037 : Blo 1740571 2611037 := bbase (se 3 (by rfl) ⟨489569, by rfl⟩ : syracuseStep 2611037 = 979139) (by norm_num)
theorem B2611061 : Blo 1740571 2611061 := bbase (se 5 (by rfl) ⟨122393, by rfl⟩ : syracuseStep 2611061 = 244787) (by norm_num)
theorem B2234245 : Blo 1740571 2234245 := bbase (se 4 (by rfl) ⟨209460, by rfl⟩ : syracuseStep 2234245 = 418921) (by norm_num)
theorem B2611085 : Blo 1740571 2611085 := bbase (se 3 (by rfl) ⟨489578, by rfl⟩ : syracuseStep 2611085 = 979157) (by norm_num)
theorem B3307405 : Blo 1740571 3307405 := bbase (se 3 (by rfl) ⟨620138, by rfl⟩ : syracuseStep 3307405 = 1240277) (by norm_num)
theorem B25098133 : Blo 1740571 25098133 := bbase (se 6 (by rfl) ⟨588237, by rfl⟩ : syracuseStep 25098133 = 1176475) (by norm_num)
theorem B2938781 : Blo 1740571 2938781 := bbase (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) (by norm_num)
theorem B2611109 : Blo 1740571 2611109 := bbase (se 4 (by rfl) ⟨244791, by rfl⟩ : syracuseStep 2611109 = 489583) (by norm_num)
theorem B2480053 : Blo 1740571 2480053 := bbase (se 5 (by rfl) ⟨116252, by rfl⟩ : syracuseStep 2480053 = 232505) (by norm_num)
theorem B2611133 : Blo 1740571 2611133 := bbase (se 3 (by rfl) ⟨489587, by rfl⟩ : syracuseStep 2611133 = 979175) (by norm_num)
theorem B2512829 : Blo 1740571 2512829 := bbase (se 3 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 2512829 = 942311) (by norm_num)
theorem B5576645 : Blo 1740571 5576645 := bbase (se 4 (by rfl) ⟨522810, by rfl⟩ : syracuseStep 5576645 = 1045621) (by norm_num)
theorem B2611157 : Blo 1740571 2611157 := bbase (se 7 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 2611157 = 61199) (by norm_num)
theorem B7436245 : Blo 1740571 7436245 := bbase (se 7 (by rfl) ⟨87143, by rfl⟩ : syracuseStep 7436245 = 174287) (by norm_num)
theorem B2611181 : Blo 1740571 2611181 := bbase (se 3 (by rfl) ⟨489596, by rfl⟩ : syracuseStep 2611181 = 979193) (by norm_num)
theorem B2611205 : Blo 1740571 2611205 := bbase (se 4 (by rfl) ⟨244800, by rfl⟩ : syracuseStep 2611205 = 489601) (by norm_num)
theorem B2480149 : Blo 1740571 2480149 := bbase (se 6 (by rfl) ⟨58128, by rfl⟩ : syracuseStep 2480149 = 116257) (by norm_num)
theorem B2611229 : Blo 1740571 2611229 := bbase (se 3 (by rfl) ⟨489605, by rfl⟩ : syracuseStep 2611229 = 979211) (by norm_num)
theorem B2938909 : Blo 1740571 2938909 := bbase (se 3 (by rfl) ⟨551045, by rfl⟩ : syracuseStep 2938909 = 1102091) (by norm_num)
theorem B3307549 : Blo 1740571 3307549 := bbase (se 3 (by rfl) ⟨620165, by rfl⟩ : syracuseStep 3307549 = 1240331) (by norm_num)
theorem B2611253 : Blo 1740571 2611253 := bbase (se 5 (by rfl) ⟨122402, by rfl⟩ : syracuseStep 2611253 = 244805) (by norm_num)
theorem B14874677 : Blo 1740571 14874677 := bbase (se 5 (by rfl) ⟨697250, by rfl⟩ : syracuseStep 14874677 = 1394501) (by norm_num)
theorem B2611277 : Blo 1740571 2611277 := bbase (se 3 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 2611277 = 979229) (by norm_num)
theorem B2611301 : Blo 1740571 2611301 := bbase (se 4 (by rfl) ⟨244809, by rfl⟩ : syracuseStep 2611301 = 489619) (by norm_num)
theorem B2938997 : Blo 1740571 2938997 := bbase (se 5 (by rfl) ⟨137765, by rfl⟩ : syracuseStep 2938997 = 275531) (by norm_num)
theorem B2611325 : Blo 1740571 2611325 := bbase (se 3 (by rfl) ⟨489623, by rfl⟩ : syracuseStep 2611325 = 979247) (by norm_num)
theorem B2611349 : Blo 1740571 2611349 := bbase (se 6 (by rfl) ⟨61203, by rfl⟩ : syracuseStep 2611349 = 122407) (by norm_num)
theorem B2611373 : Blo 1740571 2611373 := bbase (se 3 (by rfl) ⟨489632, by rfl⟩ : syracuseStep 2611373 = 979265) (by norm_num)
theorem B3307709 : Blo 1740571 3307709 := bbase (se 3 (by rfl) ⟨620195, by rfl⟩ : syracuseStep 3307709 = 1240391) (by norm_num)
theorem B2611397 : Blo 1740571 2611397 := bbase (se 4 (by rfl) ⟨244818, by rfl⟩ : syracuseStep 2611397 = 489637) (by norm_num)
theorem B5880005 : Blo 1740571 5880005 := bbase (se 4 (by rfl) ⟨551250, by rfl⟩ : syracuseStep 5880005 = 1102501) (by norm_num)
theorem B2611421 : Blo 1740571 2611421 := bbase (se 3 (by rfl) ⟨489641, by rfl⟩ : syracuseStep 2611421 = 979283) (by norm_num)
theorem B2611445 : Blo 1740571 2611445 := bbase (se 5 (by rfl) ⟨122411, by rfl⟩ : syracuseStep 2611445 = 244823) (by norm_num)
theorem B2939125 : Blo 1740571 2939125 := bbase (se 5 (by rfl) ⟨137771, by rfl⟩ : syracuseStep 2939125 = 275543) (by norm_num)
theorem B2611469 : Blo 1740571 2611469 := bbase (se 3 (by rfl) ⟨489650, by rfl⟩ : syracuseStep 2611469 = 979301) (by norm_num)
theorem B2611493 : Blo 1740571 2611493 := bbase (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) (by norm_num)
theorem B2611517 : Blo 1740571 2611517 := bbase (se 3 (by rfl) ⟨489659, by rfl⟩ : syracuseStep 2611517 = 979319) (by norm_num)
theorem B6609221 : Blo 1740571 6609221 := bbase (se 4 (by rfl) ⟨619614, by rfl⟩ : syracuseStep 6609221 = 1239229) (by norm_num)
theorem B8821061 : Blo 1740571 8821061 := bbase (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) (by norm_num)
theorem B2939213 : Blo 1740571 2939213 := bbase (se 3 (by rfl) ⟨551102, by rfl⟩ : syracuseStep 2939213 = 1102205) (by norm_num)
theorem B3307853 : Blo 1740571 3307853 := bbase (se 3 (by rfl) ⟨620222, by rfl⟩ : syracuseStep 3307853 = 1240445) (by norm_num)
theorem B2611541 : Blo 1740571 2611541 := bbase (se 10 (by rfl) ⟨3825, by rfl⟩ : syracuseStep 2611541 = 7651) (by norm_num)
theorem B2611565 : Blo 1740571 2611565 := bbase (se 3 (by rfl) ⟨489668, by rfl⟩ : syracuseStep 2611565 = 979337) (by norm_num)
theorem B2611589 : Blo 1740571 2611589 := bbase (se 4 (by rfl) ⟨244836, by rfl⟩ : syracuseStep 2611589 = 489673) (by norm_num)
theorem B2611613 : Blo 1740571 2611613 := bbase (se 3 (by rfl) ⟨489677, by rfl⟩ : syracuseStep 2611613 = 979355) (by norm_num)
theorem B2611637 : Blo 1740571 2611637 := bbase (se 5 (by rfl) ⟨122420, by rfl⟩ : syracuseStep 2611637 = 244841) (by norm_num)
theorem B10058165 : Blo 1740571 10058165 := bbase (se 5 (by rfl) ⟨471476, by rfl⟩ : syracuseStep 10058165 = 942953) (by norm_num)
theorem B4135373 : Blo 1740571 4135373 := bbase (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) (by norm_num)
theorem B2611661 : Blo 1740571 2611661 := bbase (se 3 (by rfl) ⟨489686, by rfl⟩ : syracuseStep 2611661 = 979373) (by norm_num)
theorem B2939341 : Blo 1740571 2939341 := bbase (se 3 (by rfl) ⟨551126, by rfl⟩ : syracuseStep 2939341 = 1102253) (by norm_num)
theorem B2611685 : Blo 1740571 2611685 := bbase (se 4 (by rfl) ⟨244845, by rfl⟩ : syracuseStep 2611685 = 489691) (by norm_num)
theorem B2611709 : Blo 1740571 2611709 := bbase (se 3 (by rfl) ⟨489695, by rfl⟩ : syracuseStep 2611709 = 979391) (by norm_num)
theorem B2234881 : Blo 1740571 2234881 := bbase (se 2 (by rfl) ⟨838080, by rfl⟩ : syracuseStep 2234881 = 1676161) (by norm_num)
theorem B2480645 : Blo 1740571 2480645 := bbase (se 4 (by rfl) ⟨232560, by rfl⟩ : syracuseStep 2480645 = 465121) (by norm_num)
theorem B2611733 : Blo 1740571 2611733 := bbase (se 6 (by rfl) ⟨61212, by rfl⟩ : syracuseStep 2611733 = 122425) (by norm_num)
theorem B2939429 : Blo 1740571 2939429 := bbase (se 4 (by rfl) ⟨275571, by rfl⟩ : syracuseStep 2939429 = 551143) (by norm_num)
theorem B2611757 : Blo 1740571 2611757 := bbase (se 3 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 2611757 = 979409) (by norm_num)
theorem B2611781 : Blo 1740571 2611781 := bbase (se 4 (by rfl) ⟨244854, by rfl⟩ : syracuseStep 2611781 = 489709) (by norm_num)
theorem B4405853 : Blo 1740571 4405853 := bbase (se 3 (by rfl) ⟨826097, by rfl⟩ : syracuseStep 4405853 = 1652195) (by norm_num)
theorem B2611805 : Blo 1740571 2611805 := bbase (se 3 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 2611805 = 979427) (by norm_num)
theorem B6609509 : Blo 1740571 6609509 := bbase (se 4 (by rfl) ⟨619641, by rfl⟩ : syracuseStep 6609509 = 1239283) (by norm_num)
theorem B3308141 : Blo 1740571 3308141 := bbase (se 3 (by rfl) ⟨620276, by rfl⟩ : syracuseStep 3308141 = 1240553) (by norm_num)
theorem B2611829 : Blo 1740571 2611829 := bbase (se 5 (by rfl) ⟨122429, by rfl⟩ : syracuseStep 2611829 = 244859) (by norm_num)
theorem B5880437 : Blo 1740571 5880437 := bbase (se 5 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 5880437 = 551291) (by norm_num)
theorem B2611853 : Blo 1740571 2611853 := bbase (se 3 (by rfl) ⟨489722, by rfl⟩ : syracuseStep 2611853 = 979445) (by norm_num)
theorem B2611877 : Blo 1740571 2611877 := bbase (se 4 (by rfl) ⟨244863, by rfl⟩ : syracuseStep 2611877 = 489727) (by norm_num)
theorem B2939557 : Blo 1740571 2939557 := bbase (se 4 (by rfl) ⟨275583, by rfl⟩ : syracuseStep 2939557 = 551167) (by norm_num)
theorem B2611901 : Blo 1740571 2611901 := bbase (se 3 (by rfl) ⟨489731, by rfl⟩ : syracuseStep 2611901 = 979463) (by norm_num)
theorem B2611925 : Blo 1740571 2611925 := bbase (se 7 (by rfl) ⟨30608, by rfl⟩ : syracuseStep 2611925 = 61217) (by norm_num)
theorem B16743125 : Blo 1740571 16743125 := bbase (se 7 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 16743125 = 392417) (by norm_num)
theorem B8813285 : Blo 1740571 8813285 := bbase (se 4 (by rfl) ⟨826245, by rfl⟩ : syracuseStep 8813285 = 1652491) (by norm_num)
theorem B2611949 : Blo 1740571 2611949 := bbase (se 3 (by rfl) ⟨489740, by rfl⟩ : syracuseStep 2611949 = 979481) (by norm_num)
theorem B7060213 : Blo 1740571 7060213 := bbase (se 5 (by rfl) ⟨330947, by rfl⟩ : syracuseStep 7060213 = 661895) (by norm_num)
theorem B2939645 : Blo 1740571 2939645 := bbase (se 3 (by rfl) ⟨551183, by rfl⟩ : syracuseStep 2939645 = 1102367) (by norm_num)
theorem B3717893 : Blo 1740571 3717893 := bbase (se 4 (by rfl) ⟨348552, by rfl⟩ : syracuseStep 3717893 = 697105) (by norm_num)
theorem B2611973 : Blo 1740571 2611973 := bbase (se 4 (by rfl) ⟨244872, by rfl⟩ : syracuseStep 2611973 = 489745) (by norm_num)
theorem B3971845 : Blo 1740571 3971845 := bbase (se 4 (by rfl) ⟨372360, by rfl⟩ : syracuseStep 3971845 = 744721) (by norm_num)
theorem B8370965 : Blo 1740571 8370965 := bbase (se 6 (by rfl) ⟨196194, by rfl⟩ : syracuseStep 8370965 = 392389) (by norm_num)
theorem B2611997 : Blo 1740571 2611997 := bbase (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) (by norm_num)
theorem B7060277 : Blo 1740571 7060277 := bbase (se 5 (by rfl) ⟨330950, by rfl⟩ : syracuseStep 7060277 = 661901) (by norm_num)
theorem B2612021 : Blo 1740571 2612021 := bbase (se 5 (by rfl) ⟨122438, by rfl⟩ : syracuseStep 2612021 = 244877) (by norm_num)
theorem B2612045 : Blo 1740571 2612045 := bbase (se 3 (by rfl) ⟨489758, by rfl⟩ : syracuseStep 2612045 = 979517) (by norm_num)
theorem B2612069 : Blo 1740571 2612069 := bbase (se 4 (by rfl) ⟨244881, by rfl⟩ : syracuseStep 2612069 = 489763) (by norm_num)
theorem B2612093 : Blo 1740571 2612093 := bbase (se 3 (by rfl) ⟨489767, by rfl⟩ : syracuseStep 2612093 = 979535) (by norm_num)
theorem B2939773 : Blo 1740571 2939773 := bbase (se 3 (by rfl) ⟨551207, by rfl⟩ : syracuseStep 2939773 = 1102415) (by norm_num)
theorem B3529613 : Blo 1740571 3529613 := bbase (se 3 (by rfl) ⟨661802, by rfl⟩ : syracuseStep 3529613 = 1323605) (by norm_num)
theorem B3718037 : Blo 1740571 3718037 := bbase (se 6 (by rfl) ⟨87141, by rfl⟩ : syracuseStep 3718037 = 174283) (by norm_num)
theorem B2612117 : Blo 1740571 2612117 := bbase (se 6 (by rfl) ⟨61221, by rfl⟩ : syracuseStep 2612117 = 122443) (by norm_num)
theorem B2612141 : Blo 1740571 2612141 := bbase (se 3 (by rfl) ⟨489776, by rfl⟩ : syracuseStep 2612141 = 979553) (by norm_num)
theorem B4406197 : Blo 1740571 4406197 := bbase (se 5 (by rfl) ⟨206540, by rfl⟩ : syracuseStep 4406197 = 413081) (by norm_num)
theorem B2612165 : Blo 1740571 2612165 := bbase (se 4 (by rfl) ⟨244890, by rfl⟩ : syracuseStep 2612165 = 489781) (by norm_num)
theorem B2939861 : Blo 1740571 2939861 := bbase (se 7 (by rfl) ⟨34451, by rfl⟩ : syracuseStep 2939861 = 68903) (by norm_num)
theorem B2612189 : Blo 1740571 2612189 := bbase (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) (by norm_num)
theorem B2612213 : Blo 1740571 2612213 := bbase (se 5 (by rfl) ⟨122447, by rfl⟩ : syracuseStep 2612213 = 244895) (by norm_num)
theorem B2612237 : Blo 1740571 2612237 := bbase (se 3 (by rfl) ⟨489794, by rfl⟩ : syracuseStep 2612237 = 979589) (by norm_num)
theorem B4406309 : Blo 1740571 4406309 := bbase (se 4 (by rfl) ⟨413091, by rfl⟩ : syracuseStep 4406309 = 826183) (by norm_num)
theorem B2612261 : Blo 1740571 2612261 := bbase (se 4 (by rfl) ⟨244899, by rfl⟩ : syracuseStep 2612261 = 489799) (by norm_num)
theorem B5880869 : Blo 1740571 5880869 := bbase (se 4 (by rfl) ⟨551331, by rfl⟩ : syracuseStep 5880869 = 1102663) (by norm_num)
theorem B2612285 : Blo 1740571 2612285 := bbase (se 3 (by rfl) ⟨489803, by rfl⟩ : syracuseStep 2612285 = 979607) (by norm_num)
theorem B2612309 : Blo 1740571 2612309 := bbase (se 8 (by rfl) ⟨15306, by rfl⟩ : syracuseStep 2612309 = 30613) (by norm_num)
theorem B2939989 : Blo 1740571 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B2612333 : Blo 1740571 2612333 := bbase (se 3 (by rfl) ⟨489812, by rfl⟩ : syracuseStep 2612333 = 979625) (by norm_num)
theorem B2612357 : Blo 1740571 2612357 := bbase (se 4 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 2612357 = 489817) (by norm_num)
theorem B2612381 : Blo 1740571 2612381 := bbase (se 3 (by rfl) ⟨489821, by rfl⟩ : syracuseStep 2612381 = 979643) (by norm_num)
theorem B2940077 : Blo 1740571 2940077 := bbase (se 3 (by rfl) ⟨551264, by rfl⟩ : syracuseStep 2940077 = 1102529) (by norm_num)
theorem B2612405 : Blo 1740571 2612405 := bbase (se 5 (by rfl) ⟨122456, by rfl⟩ : syracuseStep 2612405 = 244913) (by norm_num)
theorem B1858745 : Blo 1740571 1858745 := bbase (se 2 (by rfl) ⟨697029, by rfl⟩ : syracuseStep 1858745 = 1394059) (by norm_num)
theorem B2612429 : Blo 1740571 2612429 := bbase (se 3 (by rfl) ⟨489830, by rfl⟩ : syracuseStep 2612429 = 979661) (by norm_num)
theorem B4406501 : Blo 1740571 4406501 := bbase (se 4 (by rfl) ⟨413109, by rfl⟩ : syracuseStep 4406501 = 826219) (by norm_num)
theorem B2612453 : Blo 1740571 2612453 := bbase (se 4 (by rfl) ⟨244917, by rfl⟩ : syracuseStep 2612453 = 489835) (by norm_num)
theorem B2612477 : Blo 1740571 2612477 := bbase (se 3 (by rfl) ⟨489839, by rfl⟩ : syracuseStep 2612477 = 979679) (by norm_num)
theorem B2612501 : Blo 1740571 2612501 := bbase (se 6 (by rfl) ⟨61230, by rfl⟩ : syracuseStep 2612501 = 122461) (by norm_num)
theorem B2612525 : Blo 1740571 2612525 := bbase (se 3 (by rfl) ⟨489848, by rfl⟩ : syracuseStep 2612525 = 979697) (by norm_num)
theorem B2940205 : Blo 1740571 2940205 := bbase (se 3 (by rfl) ⟨551288, by rfl⟩ : syracuseStep 2940205 = 1102577) (by norm_num)
theorem B2612549 : Blo 1740571 2612549 := bbase (se 4 (by rfl) ⟨244926, by rfl⟩ : syracuseStep 2612549 = 489853) (by norm_num)
theorem B2612573 : Blo 1740571 2612573 := bbase (se 3 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 2612573 = 979715) (by norm_num)
theorem B2202977 : Blo 1740571 2202977 := bbase (se 2 (by rfl) ⟨826116, by rfl⟩ : syracuseStep 2202977 = 1652233) (by norm_num)
theorem B1858933 : Blo 1740571 1858933 := bbase (se 5 (by rfl) ⟨87137, by rfl⟩ : syracuseStep 1858933 = 174275) (by norm_num)
theorem B2612597 : Blo 1740571 2612597 := bbase (se 5 (by rfl) ⟨122465, by rfl⟩ : syracuseStep 2612597 = 244931) (by norm_num)
theorem B2940293 : Blo 1740571 2940293 := bbase (se 4 (by rfl) ⟨275652, by rfl⟩ : syracuseStep 2940293 = 551305) (by norm_num)
theorem B2612621 : Blo 1740571 2612621 := bbase (se 3 (by rfl) ⟨489866, by rfl⟩ : syracuseStep 2612621 = 979733) (by norm_num)
theorem B2203033 : Blo 1740571 2203033 := bbase (se 2 (by rfl) ⟨826137, by rfl⟩ : syracuseStep 2203033 = 1652275) (by norm_num)
theorem B2612645 : Blo 1740571 2612645 := bbase (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) (by norm_num)
theorem B2612669 : Blo 1740571 2612669 := bbase (se 3 (by rfl) ⟨489875, by rfl⟩ : syracuseStep 2612669 = 979751) (by norm_num)
theorem B2612693 : Blo 1740571 2612693 := bbase (se 7 (by rfl) ⟨30617, by rfl⟩ : syracuseStep 2612693 = 61235) (by norm_num)
theorem B2612717 : Blo 1740571 2612717 := bbase (se 3 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 2612717 = 979769) (by norm_num)
theorem B2203129 : Blo 1740571 2203129 := bbase (se 2 (by rfl) ⟨826173, by rfl⟩ : syracuseStep 2203129 = 1652347) (by norm_num)
theorem B2612741 : Blo 1740571 2612741 := bbase (se 4 (by rfl) ⟨244944, by rfl⟩ : syracuseStep 2612741 = 489889) (by norm_num)
theorem B2940421 : Blo 1740571 2940421 := bbase (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) (by norm_num)
theorem B2612765 : Blo 1740571 2612765 := bbase (se 3 (by rfl) ⟨489893, by rfl⟩ : syracuseStep 2612765 = 979787) (by norm_num)
theorem B1859117 : Blo 1740571 1859117 := bbase (se 3 (by rfl) ⟨348584, by rfl⟩ : syracuseStep 1859117 = 697169) (by norm_num)
theorem B2612789 : Blo 1740571 2612789 := bbase (se 5 (by rfl) ⟨122474, by rfl⟩ : syracuseStep 2612789 = 244949) (by norm_num)
theorem B4406845 : Blo 1740571 4406845 := bbase (se 3 (by rfl) ⟨826283, by rfl⟩ : syracuseStep 4406845 = 1652567) (by norm_num)
theorem B2612813 : Blo 1740571 2612813 := bbase (se 3 (by rfl) ⟨489902, by rfl⟩ : syracuseStep 2612813 = 979805) (by norm_num)
theorem B44654165 : Blo 1740571 44654165 := bbase (se 8 (by rfl) ⟨261645, by rfl⟩ : syracuseStep 44654165 = 523291) (by norm_num)
theorem B2940509 : Blo 1740571 2940509 := bbase (se 3 (by rfl) ⟨551345, by rfl⟩ : syracuseStep 2940509 = 1102691) (by norm_num)
theorem B2612837 : Blo 1740571 2612837 := bbase (se 4 (by rfl) ⟨244953, by rfl⟩ : syracuseStep 2612837 = 489907) (by norm_num)
theorem B3718781 : Blo 1740571 3718781 := bbase (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) (by norm_num)
theorem B2612861 : Blo 1740571 2612861 := bbase (se 3 (by rfl) ⟨489911, by rfl⟩ : syracuseStep 2612861 = 979823) (by norm_num)
theorem B6274709 : Blo 1740571 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B2612885 : Blo 1740571 2612885 := bbase (se 6 (by rfl) ⟨61239, by rfl⟩ : syracuseStep 2612885 = 122479) (by norm_num)
theorem B2203301 : Blo 1740571 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B8937125 : Blo 1740571 8937125 := bbase (se 4 (by rfl) ⟨837855, by rfl⟩ : syracuseStep 8937125 = 1675711) (by norm_num)
theorem B4406957 : Blo 1740571 4406957 := bbase (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) (by norm_num)
theorem B2612909 : Blo 1740571 2612909 := bbase (se 3 (by rfl) ⟨489920, by rfl⟩ : syracuseStep 2612909 = 979841) (by norm_num)
theorem B2612933 : Blo 1740571 2612933 := bbase (se 4 (by rfl) ⟨244962, by rfl⟩ : syracuseStep 2612933 = 489925) (by norm_num)
theorem B2203357 : Blo 1740571 2203357 := bbase (se 3 (by rfl) ⟨413129, by rfl⟩ : syracuseStep 2203357 = 826259) (by norm_num)
theorem B2612957 : Blo 1740571 2612957 := bbase (se 3 (by rfl) ⟨489929, by rfl⟩ : syracuseStep 2612957 = 979859) (by norm_num)
theorem B2612981 : Blo 1740571 2612981 := bbase (se 5 (by rfl) ⟨122483, by rfl⟩ : syracuseStep 2612981 = 244967) (by norm_num)
theorem B6610693 : Blo 1740571 6610693 := bbase (se 4 (by rfl) ⟨619752, by rfl⟩ : syracuseStep 6610693 = 1239505) (by norm_num)
theorem B2613005 : Blo 1740571 2613005 := bbase (se 3 (by rfl) ⟨489938, by rfl⟩ : syracuseStep 2613005 = 979877) (by norm_num)
theorem B2613029 : Blo 1740571 2613029 := bbase (se 4 (by rfl) ⟨244971, by rfl⟩ : syracuseStep 2613029 = 489943) (by norm_num)
theorem B2203453 : Blo 1740571 2203453 := bbase (se 3 (by rfl) ⟨413147, by rfl⟩ : syracuseStep 2203453 = 826295) (by norm_num)
theorem B2613053 : Blo 1740571 2613053 := bbase (se 3 (by rfl) ⟨489947, by rfl⟩ : syracuseStep 2613053 = 979895) (by norm_num)
theorem B2178893 : Blo 1740571 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B2613077 : Blo 1740571 2613077 := bbase (se 9 (by rfl) ⟨7655, by rfl⟩ : syracuseStep 2613077 = 15311) (by norm_num)
theorem B4407149 : Blo 1740571 4407149 := bbase (se 3 (by rfl) ⟨826340, by rfl⟩ : syracuseStep 4407149 = 1652681) (by norm_num)
theorem B2613101 : Blo 1740571 2613101 := bbase (se 3 (by rfl) ⟨489956, by rfl⟩ : syracuseStep 2613101 = 979913) (by norm_num)
theorem B2613125 : Blo 1740571 2613125 := bbase (se 4 (by rfl) ⟨244980, by rfl⟩ : syracuseStep 2613125 = 489961) (by norm_num)
theorem B5578645 : Blo 1740571 5578645 := bbase (se 6 (by rfl) ⟨130749, by rfl⟩ : syracuseStep 5578645 = 261499) (by norm_num)
theorem B2613149 : Blo 1740571 2613149 := bbase (se 3 (by rfl) ⟨489965, by rfl⟩ : syracuseStep 2613149 = 979931) (by norm_num)
theorem B4186021 : Blo 1740571 4186021 := bbase (se 4 (by rfl) ⟨392439, by rfl⟩ : syracuseStep 4186021 = 784879) (by norm_num)
theorem B2613173 : Blo 1740571 2613173 := bbase (se 5 (by rfl) ⟨122492, by rfl⟩ : syracuseStep 2613173 = 244985) (by norm_num)
theorem B2613197 : Blo 1740571 2613197 := bbase (se 3 (by rfl) ⟨489974, by rfl⟩ : syracuseStep 2613197 = 979949) (by norm_num)
theorem B2613221 : Blo 1740571 2613221 := bbase (se 4 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 2613221 = 489979) (by norm_num)
theorem B2203625 : Blo 1740571 2203625 := bbase (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) (by norm_num)
theorem B8814581 : Blo 1740571 8814581 := bbase (se 5 (by rfl) ⟨413183, by rfl⟩ : syracuseStep 8814581 = 826367) (by norm_num)
theorem B2613245 : Blo 1740571 2613245 := bbase (se 3 (by rfl) ⟨489983, by rfl⟩ : syracuseStep 2613245 = 979967) (by norm_num)
theorem B2613251 : Blo 1740571 2613251 := bstep (se 1 (by rfl) ⟨1959938, by rfl⟩ : syracuseStep 2613251 = 3919877) B3919877
theorem B11919365 : Blo 1740571 11919365 := bstep (se 4 (by rfl) ⟨1117440, by rfl⟩ : syracuseStep 11919365 = 2234881) B2234881
theorem B2613281 : Blo 1740571 2613281 := bstep (se 2 (by rfl) ⟨979980, by rfl⟩ : syracuseStep 2613281 = 1959961) B1959961
theorem B4407331 : Blo 1740571 4407331 := bstep (se 1 (by rfl) ⟨3305498, by rfl⟩ : syracuseStep 4407331 = 6610997) B6610997
theorem B5578787 : Blo 1740571 5578787 := bstep (se 1 (by rfl) ⟨4184090, by rfl⟩ : syracuseStep 5578787 = 8368181) B8368181
theorem B2613299 : Blo 1740571 2613299 := bstep (se 1 (by rfl) ⟨1959974, by rfl⟩ : syracuseStep 2613299 = 3919949) B3919949
theorem B2613329 : Blo 1740571 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B2613347 : Blo 1740571 2613347 := bstep (se 1 (by rfl) ⟨1960010, by rfl⟩ : syracuseStep 2613347 = 3920021) B3920021
theorem B27181169 : Blo 1740571 27181169 := bstep (se 2 (by rfl) ⟨10192938, by rfl⟩ : syracuseStep 27181169 = 20385877) B20385877
theorem B2613377 : Blo 1740571 2613377 := bstep (se 2 (by rfl) ⟨980016, by rfl⟩ : syracuseStep 2613377 = 1960033) B1960033
theorem B2613395 : Blo 1740571 2613395 := bstep (se 1 (by rfl) ⟨1960046, by rfl⟩ : syracuseStep 2613395 = 3920093) B3920093
theorem B4407473 : Blo 1740571 4407473 := bstep (se 2 (by rfl) ⟨1652802, by rfl⟩ : syracuseStep 4407473 = 3305605) B3305605
theorem B2613425 : Blo 1740571 2613425 := bstep (se 2 (by rfl) ⟨980034, by rfl⟩ : syracuseStep 2613425 = 1960069) B1960069
theorem B2203843 : Blo 1740571 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B2613443 : Blo 1740571 2613443 := bstep (se 1 (by rfl) ⟨1960082, by rfl⟩ : syracuseStep 2613443 = 3920165) B3920165
theorem B8372429 : Blo 1740571 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B2613473 : Blo 1740571 2613473 := bstep (se 2 (by rfl) ⟨980052, by rfl⟩ : syracuseStep 2613473 = 1960105) B1960105
theorem B13222115 : Blo 1740571 13222115 := bstep (se 1 (by rfl) ⟨9916586, by rfl⟩ : syracuseStep 13222115 = 19833173) B19833173
theorem B2613491 : Blo 1740571 2613491 := bstep (se 1 (by rfl) ⟨1960118, by rfl⟩ : syracuseStep 2613491 = 3920237) B3920237
theorem B2613521 : Blo 1740571 2613521 := bstep (se 2 (by rfl) ⟨980070, by rfl⟩ : syracuseStep 2613521 = 1960141) B1960141
theorem B1958179 : Blo 1740571 1958179 := bstep (se 1 (by rfl) ⟨1468634, by rfl⟩ : syracuseStep 1958179 = 2937269) B2937269
theorem B2203939 : Blo 1740571 2203939 := bstep (se 1 (by rfl) ⟨1652954, by rfl⟩ : syracuseStep 2203939 = 3305909) B3305909
theorem B2613539 : Blo 1740571 2613539 := bstep (se 1 (by rfl) ⟨1960154, by rfl⟩ : syracuseStep 2613539 = 3920309) B3920309
theorem B35742005 : Blo 1740571 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B2613569 : Blo 1740571 2613569 := bstep (se 2 (by rfl) ⟨980088, by rfl⟩ : syracuseStep 2613569 = 1960177) B1960177
theorem B2613587 : Blo 1740571 2613587 := bstep (se 1 (by rfl) ⟨1960190, by rfl⟩ : syracuseStep 2613587 = 3920381) B3920381
theorem B2613617 : Blo 1740571 2613617 := bstep (se 2 (by rfl) ⟨980106, by rfl⟩ : syracuseStep 2613617 = 1960213) B1960213
theorem B2613635 : Blo 1740571 2613635 := bstep (se 1 (by rfl) ⟨1960226, by rfl⟩ : syracuseStep 2613635 = 3920453) B3920453
theorem B2613665 : Blo 1740571 2613665 := bstep (se 2 (by rfl) ⟨980124, by rfl⟩ : syracuseStep 2613665 = 1960249) B1960249
theorem B1958323 : Blo 1740571 1958323 := bstep (se 1 (by rfl) ⟨1468742, by rfl⟩ : syracuseStep 1958323 = 2937485) B2937485
theorem B2613683 : Blo 1740571 2613683 := bstep (se 1 (by rfl) ⟨1960262, by rfl⟩ : syracuseStep 2613683 = 3920525) B3920525
theorem B2613713 : Blo 1740571 2613713 := bstep (se 2 (by rfl) ⟨980142, by rfl⟩ : syracuseStep 2613713 = 1960285) B1960285
theorem B2613731 : Blo 1740571 2613731 := bstep (se 1 (by rfl) ⟨1960298, by rfl⟩ : syracuseStep 2613731 = 3920597) B3920597
theorem B4956653 : Blo 1740571 4956653 := bstep (se 3 (by rfl) ⟨929372, by rfl⟩ : syracuseStep 4956653 = 1858745) B1858745
theorem B2613761 : Blo 1740571 2613761 := bstep (se 2 (by rfl) ⟨980160, by rfl⟩ : syracuseStep 2613761 = 1960321) B1960321
theorem B2613779 : Blo 1740571 2613779 := bstep (se 1 (by rfl) ⟨1960334, by rfl⟩ : syracuseStep 2613779 = 3920669) B3920669
theorem B2613809 : Blo 1740571 2613809 := bstep (se 2 (by rfl) ⟨980178, by rfl⟩ : syracuseStep 2613809 = 1960357) B1960357
theorem B1958467 : Blo 1740571 1958467 := bstep (se 1 (by rfl) ⟨1468850, by rfl⟩ : syracuseStep 1958467 = 2937701) B2937701
theorem B2613827 : Blo 1740571 2613827 := bstep (se 1 (by rfl) ⟨1960370, by rfl⟩ : syracuseStep 2613827 = 3920741) B3920741
theorem B2613857 : Blo 1740571 2613857 := bstep (se 2 (by rfl) ⟨980196, by rfl⟩ : syracuseStep 2613857 = 1960393) B1960393
theorem B1958611 : Blo 1740571 1958611 := bstep (se 1 (by rfl) ⟨1468958, by rfl⟩ : syracuseStep 1958611 = 2937917) B2937917
theorem B3916529 : Blo 1740571 3916529 := bstep (se 2 (by rfl) ⟨1468698, by rfl⟩ : syracuseStep 3916529 = 2937397) B2937397
theorem B3916547 : Blo 1740571 3916547 := bstep (se 1 (by rfl) ⟨2937410, by rfl⟩ : syracuseStep 3916547 = 5874821) B5874821
theorem B2204435 : Blo 1740571 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B1958755 : Blo 1740571 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B5874605 : Blo 1740571 5874605 := bstep (se 3 (by rfl) ⟨1101488, by rfl⟩ : syracuseStep 5874605 = 2202977) B2202977
theorem B11158469 : Blo 1740571 11158469 := bstep (se 4 (by rfl) ⟨1046106, by rfl⟩ : syracuseStep 11158469 = 2092213) B2092213
theorem B5874659 : Blo 1740571 5874659 := bstep (se 1 (by rfl) ⟨4405994, by rfl⟩ : syracuseStep 5874659 = 8811989) B8811989
theorem B6611939 : Blo 1740571 6611939 := bstep (se 1 (by rfl) ⟨4958954, by rfl⟩ : syracuseStep 6611939 = 9917909) B9917909
theorem B1958899 : Blo 1740571 1958899 := bstep (se 1 (by rfl) ⟨1469174, by rfl⟩ : syracuseStep 1958899 = 2938349) B2938349
theorem B3916817 : Blo 1740571 3916817 := bstep (se 2 (by rfl) ⟨1468806, by rfl⟩ : syracuseStep 3916817 = 2937613) B2937613
theorem B3916835 : Blo 1740571 3916835 := bstep (se 1 (by rfl) ⟨2937626, by rfl⟩ : syracuseStep 3916835 = 5875253) B5875253
theorem B8815715 : Blo 1740571 8815715 := bstep (se 1 (by rfl) ⟨6611786, by rfl⟩ : syracuseStep 8815715 = 13223573) B13223573
theorem B1959043 : Blo 1740571 1959043 := bstep (se 1 (by rfl) ⟨1469282, by rfl⟩ : syracuseStep 1959043 = 2938565) B2938565
theorem B3531907 : Blo 1740571 3531907 := bstep (se 1 (by rfl) ⟨2648930, by rfl⟩ : syracuseStep 3531907 = 5297861) B5297861
theorem B4408465 : Blo 1740571 4408465 := bstep (se 2 (by rfl) ⟨1653174, by rfl⟩ : syracuseStep 4408465 = 3306349) B3306349
theorem B5874929 : Blo 1740571 5874929 := bstep (se 2 (by rfl) ⟨2203098, by rfl⟩ : syracuseStep 5874929 = 4406197) B4406197
theorem B1959187 : Blo 1740571 1959187 := bstep (se 1 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 1959187 = 2938781) B2938781
theorem B3917105 : Blo 1740571 3917105 := bstep (se 2 (by rfl) ⟨1468914, by rfl⟩ : syracuseStep 3917105 = 2937829) B2937829
theorem B3720497 : Blo 1740571 3720497 := bstep (se 2 (by rfl) ⟨1395186, by rfl⟩ : syracuseStep 3720497 = 2790373) B2790373
theorem B3917123 : Blo 1740571 3917123 := bstep (se 1 (by rfl) ⟨2937842, by rfl⟩ : syracuseStep 3917123 = 5875685) B5875685
theorem B56460685 : Blo 1740571 56460685 := bstep (se 3 (by rfl) ⟨10586378, by rfl⟩ : syracuseStep 56460685 = 21172757) B21172757
theorem B1959331 : Blo 1740571 1959331 := bstep (se 1 (by rfl) ⟨1469498, by rfl⟩ : syracuseStep 1959331 = 2938997) B2938997
theorem B4408739 : Blo 1740571 4408739 := bstep (se 1 (by rfl) ⟨3306554, by rfl⟩ : syracuseStep 4408739 = 6613109) B6613109
theorem B5096881 : Blo 1740571 5096881 := bstep (se 2 (by rfl) ⟨1911330, by rfl⟩ : syracuseStep 5096881 = 3822661) B3822661
theorem B4957645 : Blo 1740571 4957645 := bstep (se 3 (by rfl) ⟨929558, by rfl⟩ : syracuseStep 4957645 = 1859117) B1859117
theorem B2205139 : Blo 1740571 2205139 := bstep (se 1 (by rfl) ⟨1653854, by rfl⟩ : syracuseStep 2205139 = 3307709) B3307709
theorem B8373773 : Blo 1740571 8373773 := bstep (se 3 (by rfl) ⟨1570082, by rfl⟩ : syracuseStep 8373773 = 3140165) B3140165
theorem B1959475 : Blo 1740571 1959475 := bstep (se 1 (by rfl) ⟨1469606, by rfl⟩ : syracuseStep 1959475 = 2939213) B2939213
theorem B2205235 : Blo 1740571 2205235 := bstep (se 1 (by rfl) ⟨1653926, by rfl⟩ : syracuseStep 2205235 = 3307853) B3307853
theorem B3917393 : Blo 1740571 3917393 := bstep (se 2 (by rfl) ⟨1469022, by rfl⟩ : syracuseStep 3917393 = 2938045) B2938045
theorem B2647649 : Blo 1740571 2647649 := bstep (se 2 (by rfl) ⟨992868, by rfl⟩ : syracuseStep 2647649 = 1985737) B1985737
theorem B3917411 : Blo 1740571 3917411 := bstep (se 1 (by rfl) ⟨2938058, by rfl⟩ : syracuseStep 3917411 = 5876117) B5876117
theorem B4408931 : Blo 1740571 4408931 := bstep (se 1 (by rfl) ⟨3306698, by rfl⟩ : syracuseStep 4408931 = 6613397) B6613397
theorem B1959619 : Blo 1740571 1959619 := bstep (se 1 (by rfl) ⟨1469714, by rfl⟩ : syracuseStep 1959619 = 2939429) B2939429
theorem B5875469 : Blo 1740571 5875469 := bstep (se 3 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 5875469 = 2203301) B2203301
theorem B5293873 : Blo 1740571 5293873 := bstep (se 2 (by rfl) ⟨1985202, by rfl⟩ : syracuseStep 5293873 = 3970405) B3970405
theorem B5875523 : Blo 1740571 5875523 := bstep (se 1 (by rfl) ⟨4406642, by rfl⟩ : syracuseStep 5875523 = 8813285) B8813285
theorem B1959763 : Blo 1740571 1959763 := bstep (se 1 (by rfl) ⟨1469822, by rfl⟩ : syracuseStep 1959763 = 2939645) B2939645
theorem B3917681 : Blo 1740571 3917681 := bstep (se 2 (by rfl) ⟨1469130, by rfl⟩ : syracuseStep 3917681 = 2938261) B2938261
theorem B3917699 : Blo 1740571 3917699 := bstep (se 1 (by rfl) ⟨2938274, by rfl⟩ : syracuseStep 3917699 = 5876549) B5876549
theorem B8816525 : Blo 1740571 8816525 := bstep (se 3 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 8816525 = 3306197) B3306197
theorem B9914309 : Blo 1740571 9914309 := bstep (se 4 (by rfl) ⟨929466, by rfl⟩ : syracuseStep 9914309 = 1858933) B1858933
theorem B6612941 : Blo 1740571 6612941 := bstep (se 3 (by rfl) ⟨1239926, by rfl⟩ : syracuseStep 6612941 = 2479853) B2479853
theorem B1959907 : Blo 1740571 1959907 := bstep (se 1 (by rfl) ⟨1469930, by rfl⟩ : syracuseStep 1959907 = 2939861) B2939861
theorem B10594309 : Blo 1740571 10594309 := bstep (se 4 (by rfl) ⟨993216, by rfl⟩ : syracuseStep 10594309 = 1986433) B1986433
theorem B5875793 : Blo 1740571 5875793 := bstep (se 2 (by rfl) ⟨2203422, by rfl⟩ : syracuseStep 5875793 = 4406845) B4406845
theorem B1960051 : Blo 1740571 1960051 := bstep (se 1 (by rfl) ⟨1470038, by rfl⟩ : syracuseStep 1960051 = 2940077) B2940077
theorem B18827405 : Blo 1740571 18827405 := bstep (se 3 (by rfl) ⟨3530138, by rfl⟩ : syracuseStep 18827405 = 7060277) B7060277
theorem B3917969 : Blo 1740571 3917969 := bstep (se 2 (by rfl) ⟨1469238, by rfl⟩ : syracuseStep 3917969 = 2938477) B2938477
theorem B3917987 : Blo 1740571 3917987 := bstep (se 1 (by rfl) ⟨2938490, by rfl⟩ : syracuseStep 3917987 = 5876981) B5876981
theorem B5810381 : Blo 1740571 5810381 := bstep (se 3 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 5810381 = 2178893) B2178893
theorem B1960195 : Blo 1740571 1960195 := bstep (se 1 (by rfl) ⟨1470146, by rfl⟩ : syracuseStep 1960195 = 2940293) B2940293
theorem B7440653 : Blo 1740571 7440653 := bstep (se 3 (by rfl) ⟨1395122, by rfl⟩ : syracuseStep 7440653 = 2790245) B2790245
theorem B3770705 : Blo 1740571 3770705 := bstep (se 2 (by rfl) ⟨1414014, by rfl⟩ : syracuseStep 3770705 = 2828029) B2828029
theorem B16746851 : Blo 1740571 16746851 := bstep (se 1 (by rfl) ⟨12560138, by rfl⟩ : syracuseStep 16746851 = 25120277) B25120277
theorem B23841137 : Blo 1740571 23841137 := bstep (se 2 (by rfl) ⟨8940426, by rfl⟩ : syracuseStep 23841137 = 17880853) B17880853
theorem B1960339 : Blo 1740571 1960339 := bstep (se 1 (by rfl) ⟨1470254, by rfl⟩ : syracuseStep 1960339 = 2940509) B2940509
theorem B3918257 : Blo 1740571 3918257 := bstep (se 2 (by rfl) ⟨1469346, by rfl⟩ : syracuseStep 3918257 = 2938693) B2938693
theorem B3918275 : Blo 1740571 3918275 := bstep (se 1 (by rfl) ⟨2938706, by rfl⟩ : syracuseStep 3918275 = 5877413) B5877413
theorem B5958083 : Blo 1740571 5958083 := bstep (se 1 (by rfl) ⟨4468562, by rfl⟩ : syracuseStep 5958083 = 8937125) B8937125
theorem B14125553 : Blo 1740571 14125553 := bstep (se 2 (by rfl) ⟨5297082, by rfl⟩ : syracuseStep 14125553 = 10594165) B10594165
theorem B9923057 : Blo 1740571 9923057 := bstep (se 2 (by rfl) ⟨3721146, by rfl⟩ : syracuseStep 9923057 = 7442293) B7442293
theorem B14871053 : Blo 1740571 14871053 := bstep (se 3 (by rfl) ⟨2788322, by rfl⟩ : syracuseStep 14871053 = 5576645) B5576645
theorem B4409873 : Blo 1740571 4409873 := bstep (se 2 (by rfl) ⟨1653702, by rfl⟩ : syracuseStep 4409873 = 3307405) B3307405
theorem B5581361 : Blo 1740571 5581361 := bstep (se 2 (by rfl) ⟨2093010, by rfl⟩ : syracuseStep 5581361 = 4186021) B4186021
theorem B4409923 : Blo 1740571 4409923 := bstep (se 1 (by rfl) ⟨3307442, by rfl⟩ : syracuseStep 4409923 = 6614885) B6614885
theorem B5876333 : Blo 1740571 5876333 := bstep (se 3 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 5876333 = 2203625) B2203625
theorem B9914993 : Blo 1740571 9914993 := bstep (se 2 (by rfl) ⟨3718122, by rfl⟩ : syracuseStep 9914993 = 7436245) B7436245
theorem B19827341 : Blo 1740571 19827341 := bstep (se 3 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 19827341 = 7435253) B7435253
theorem B5876387 : Blo 1740571 5876387 := bstep (se 1 (by rfl) ⟨4407290, by rfl⟩ : syracuseStep 5876387 = 8814581) B8814581
theorem B3918545 : Blo 1740571 3918545 := bstep (se 2 (by rfl) ⟨1469454, by rfl⟩ : syracuseStep 3918545 = 2938909) B2938909
theorem B4410065 : Blo 1740571 4410065 := bstep (se 2 (by rfl) ⟨1653774, by rfl⟩ : syracuseStep 4410065 = 3307549) B3307549
theorem B2788067 : Blo 1740571 2788067 := bstep (se 1 (by rfl) ⟨2091050, by rfl⟩ : syracuseStep 2788067 = 4182101) B4182101
theorem B3918563 : Blo 1740571 3918563 := bstep (se 1 (by rfl) ⟨2938922, by rfl⟩ : syracuseStep 3918563 = 5877845) B5877845
theorem B2788195 : Blo 1740571 2788195 := bstep (se 1 (by rfl) ⟨2091146, by rfl⟩ : syracuseStep 2788195 = 4182293) B4182293
theorem B5876657 : Blo 1740571 5876657 := bstep (se 2 (by rfl) ⟨2203746, by rfl⟩ : syracuseStep 5876657 = 4407493) B4407493
theorem B3918833 : Blo 1740571 3918833 := bstep (se 2 (by rfl) ⟨1469562, by rfl⟩ : syracuseStep 3918833 = 2939125) B2939125
theorem B3304451 : Blo 1740571 3304451 := bstep (se 1 (by rfl) ⟨2478338, by rfl⟩ : syracuseStep 3304451 = 4956677) B4956677
theorem B3918851 : Blo 1740571 3918851 := bstep (se 1 (by rfl) ⟨2939138, by rfl⟩ : syracuseStep 3918851 = 5878277) B5878277
theorem B2354243 : Blo 1740571 2354243 := bstep (se 1 (by rfl) ⟨1765682, by rfl⟩ : syracuseStep 2354243 = 3531365) B3531365
theorem B5958755 : Blo 1740571 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B4959377 : Blo 1740571 4959377 := bstep (se 2 (by rfl) ⟨1859766, by rfl⟩ : syracuseStep 4959377 = 3719533) B3719533
theorem B2649235 : Blo 1740571 2649235 := bstep (se 1 (by rfl) ⟨1986926, by rfl⟩ : syracuseStep 2649235 = 3973853) B3973853
theorem B3919121 : Blo 1740571 3919121 := bstep (se 2 (by rfl) ⟨1469670, by rfl⟩ : syracuseStep 3919121 = 2939341) B2939341
theorem B3304739 : Blo 1740571 3304739 := bstep (se 1 (by rfl) ⟨2478554, by rfl⟩ : syracuseStep 3304739 = 4957109) B4957109
theorem B3919139 : Blo 1740571 3919139 := bstep (se 1 (by rfl) ⟨2939354, by rfl⟩ : syracuseStep 3919139 = 5878709) B5878709
theorem B4959569 : Blo 1740571 4959569 := bstep (se 2 (by rfl) ⟨1859838, by rfl⟩ : syracuseStep 4959569 = 3719677) B3719677
theorem B7540145 : Blo 1740571 7540145 := bstep (se 2 (by rfl) ⟨2827554, by rfl⟩ : syracuseStep 7540145 = 5655109) B5655109
theorem B5877197 : Blo 1740571 5877197 := bstep (se 3 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 5877197 = 2203949) B2203949
theorem B2788835 : Blo 1740571 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B22318577 : Blo 1740571 22318577 := bstep (se 2 (by rfl) ⟨8369466, by rfl⟩ : syracuseStep 22318577 = 16738933) B16738933
theorem B5877251 : Blo 1740571 5877251 := bstep (se 1 (by rfl) ⟨4407938, by rfl⟩ : syracuseStep 5877251 = 8815877) B8815877
theorem B2788913 : Blo 1740571 2788913 := bstep (se 2 (by rfl) ⟨1045842, by rfl⟩ : syracuseStep 2788913 = 2091685) B2091685
theorem B3919409 : Blo 1740571 3919409 := bstep (se 2 (by rfl) ⟨1469778, by rfl⟩ : syracuseStep 3919409 = 2939557) B2939557
theorem B3919427 : Blo 1740571 3919427 := bstep (se 1 (by rfl) ⟨2939570, by rfl⟩ : syracuseStep 3919427 = 5879141) B5879141
theorem B42929777 : Blo 1740571 42929777 := bstep (se 2 (by rfl) ⟨16098666, by rfl⟩ : syracuseStep 42929777 = 32197333) B32197333
theorem B5295793 : Blo 1740571 5295793 := bstep (se 2 (by rfl) ⟨1985922, by rfl⟩ : syracuseStep 5295793 = 3971845) B3971845
theorem B18820835 : Blo 1740571 18820835 := bstep (se 1 (by rfl) ⟨14115626, by rfl⟩ : syracuseStep 18820835 = 28231253) B28231253
theorem B5877521 : Blo 1740571 5877521 := bstep (se 2 (by rfl) ⟨2204070, by rfl⟩ : syracuseStep 5877521 = 4408141) B4408141
theorem B2092819 : Blo 1740571 2092819 := bstep (se 1 (by rfl) ⟨1569614, by rfl⟩ : syracuseStep 2092819 = 3139229) B3139229
theorem B1740579 : Blo 1740571 1740579 := bstep (se 1 (by rfl) ⟨1305434, by rfl⟩ : syracuseStep 1740579 = 2610869) B2610869
theorem B7745329 : Blo 1740571 7745329 := bstep (se 2 (by rfl) ⟨2904498, by rfl⟩ : syracuseStep 7745329 = 5808997) B5808997
theorem B7941937 : Blo 1740571 7941937 := bstep (se 2 (by rfl) ⟨2978226, by rfl⟩ : syracuseStep 7941937 = 5956453) B5956453
theorem B1740595 : Blo 1740571 1740595 := bstep (se 1 (by rfl) ⟨1305446, by rfl⟩ : syracuseStep 1740595 = 2610893) B2610893
theorem B7442225 : Blo 1740571 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B1740611 : Blo 1740571 1740611 := bstep (se 1 (by rfl) ⟨1305458, by rfl⟩ : syracuseStep 1740611 = 2610917) B2610917
theorem B3919697 : Blo 1740571 3919697 := bstep (se 2 (by rfl) ⟨1469886, by rfl⟩ : syracuseStep 3919697 = 2939773) B2939773
theorem B1740627 : Blo 1740571 1740627 := bstep (se 1 (by rfl) ⟨1305470, by rfl⟩ : syracuseStep 1740627 = 2610941) B2610941
theorem B1740643 : Blo 1740571 1740643 := bstep (se 1 (by rfl) ⟨1305482, by rfl⟩ : syracuseStep 1740643 = 2610965) B2610965
theorem B3919715 : Blo 1740571 3919715 := bstep (se 1 (by rfl) ⟨2939786, by rfl⟩ : syracuseStep 3919715 = 5879573) B5879573
theorem B1740659 : Blo 1740571 1740659 := bstep (se 1 (by rfl) ⟨1305494, by rfl⟩ : syracuseStep 1740659 = 2610989) B2610989
theorem B2092915 : Blo 1740571 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B1740675 : Blo 1740571 1740675 := bstep (se 1 (by rfl) ⟨1305506, by rfl⟩ : syracuseStep 1740675 = 2611013) B2611013
theorem B1740691 : Blo 1740571 1740691 := bstep (se 1 (by rfl) ⟨1305518, by rfl⟩ : syracuseStep 1740691 = 2611037) B2611037
theorem B1740707 : Blo 1740571 1740707 := bstep (se 1 (by rfl) ⟨1305530, by rfl⟩ : syracuseStep 1740707 = 2611061) B2611061
theorem B2789297 : Blo 1740571 2789297 := bstep (se 2 (by rfl) ⟨1045986, by rfl⟩ : syracuseStep 2789297 = 2091973) B2091973
theorem B1740723 : Blo 1740571 1740723 := bstep (se 1 (by rfl) ⟨1305542, by rfl⟩ : syracuseStep 1740723 = 2611085) B2611085
theorem B1740739 : Blo 1740571 1740739 := bstep (se 1 (by rfl) ⟨1305554, by rfl⟩ : syracuseStep 1740739 = 2611109) B2611109
theorem B37654469 : Blo 1740571 37654469 := bstep (se 4 (by rfl) ⟨3530106, by rfl⟩ : syracuseStep 37654469 = 7060213) B7060213
theorem B9416645 : Blo 1740571 9416645 := bstep (se 4 (by rfl) ⟨882810, by rfl⟩ : syracuseStep 9416645 = 1765621) B1765621
theorem B1740755 : Blo 1740571 1740755 := bstep (se 1 (by rfl) ⟨1305566, by rfl⟩ : syracuseStep 1740755 = 2611133) B2611133
theorem B1740771 : Blo 1740571 1740771 := bstep (se 1 (by rfl) ⟨1305578, by rfl⟩ : syracuseStep 1740771 = 2611157) B2611157
theorem B1740787 : Blo 1740571 1740787 := bstep (se 1 (by rfl) ⟨1305590, by rfl⟩ : syracuseStep 1740787 = 2611181) B2611181
theorem B1740803 : Blo 1740571 1740803 := bstep (se 1 (by rfl) ⟨1305602, by rfl⟩ : syracuseStep 1740803 = 2611205) B2611205
theorem B6615053 : Blo 1740571 6615053 := bstep (se 3 (by rfl) ⟨1240322, by rfl⟩ : syracuseStep 6615053 = 2480645) B2480645
theorem B1740819 : Blo 1740571 1740819 := bstep (se 1 (by rfl) ⟨1305614, by rfl⟩ : syracuseStep 1740819 = 2611229) B2611229
theorem B1740835 : Blo 1740571 1740835 := bstep (se 1 (by rfl) ⟨1305626, by rfl⟩ : syracuseStep 1740835 = 2611253) B2611253
theorem B9916451 : Blo 1740571 9916451 := bstep (se 1 (by rfl) ⟨7437338, by rfl⟩ : syracuseStep 9916451 = 14874677) B14874677
theorem B2789425 : Blo 1740571 2789425 := bstep (se 2 (by rfl) ⟨1046034, by rfl⟩ : syracuseStep 2789425 = 2092069) B2092069
theorem B1740851 : Blo 1740571 1740851 := bstep (se 1 (by rfl) ⟨1305638, by rfl⟩ : syracuseStep 1740851 = 2611277) B2611277
theorem B1740867 : Blo 1740571 1740867 := bstep (se 1 (by rfl) ⟨1305650, by rfl⟩ : syracuseStep 1740867 = 2611301) B2611301
theorem B1740883 : Blo 1740571 1740883 := bstep (se 1 (by rfl) ⟨1305662, by rfl⟩ : syracuseStep 1740883 = 2611325) B2611325
theorem B1765459 : Blo 1740571 1765459 := bstep (se 1 (by rfl) ⟨1324094, by rfl⟩ : syracuseStep 1765459 = 2648189) B2648189
theorem B1740899 : Blo 1740571 1740899 := bstep (se 1 (by rfl) ⟨1305674, by rfl⟩ : syracuseStep 1740899 = 2611349) B2611349
theorem B3919985 : Blo 1740571 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B1740915 : Blo 1740571 1740915 := bstep (se 1 (by rfl) ⟨1305686, by rfl⟩ : syracuseStep 1740915 = 2611373) B2611373
theorem B1740931 : Blo 1740571 1740931 := bstep (se 1 (by rfl) ⟨1305698, by rfl⟩ : syracuseStep 1740931 = 2611397) B2611397
theorem B3920003 : Blo 1740571 3920003 := bstep (se 1 (by rfl) ⟨2940002, by rfl⟩ : syracuseStep 3920003 = 5880005) B5880005
theorem B1740947 : Blo 1740571 1740947 := bstep (se 1 (by rfl) ⟨1305710, by rfl⟩ : syracuseStep 1740947 = 2611421) B2611421
theorem B2093203 : Blo 1740571 2093203 := bstep (se 1 (by rfl) ⟨1569902, by rfl⟩ : syracuseStep 2093203 = 3139805) B3139805
theorem B1740963 : Blo 1740571 1740963 := bstep (se 1 (by rfl) ⟨1305722, by rfl⟩ : syracuseStep 1740963 = 2611445) B2611445
theorem B1740979 : Blo 1740571 1740979 := bstep (se 1 (by rfl) ⟨1305734, by rfl⟩ : syracuseStep 1740979 = 2611469) B2611469
theorem B1740995 : Blo 1740571 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B3305681 : Blo 1740571 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B1741011 : Blo 1740571 1741011 := bstep (se 1 (by rfl) ⟨1305758, by rfl⟩ : syracuseStep 1741011 = 2611517) B2611517
theorem B1741027 : Blo 1740571 1741027 := bstep (se 1 (by rfl) ⟨1305770, by rfl⟩ : syracuseStep 1741027 = 2611541) B2611541
theorem B1741043 : Blo 1740571 1741043 := bstep (se 1 (by rfl) ⟨1305782, by rfl⟩ : syracuseStep 1741043 = 2611565) B2611565
theorem B1741059 : Blo 1740571 1741059 := bstep (se 1 (by rfl) ⟨1305794, by rfl⟩ : syracuseStep 1741059 = 2611589) B2611589
theorem B1741075 : Blo 1740571 1741075 := bstep (se 1 (by rfl) ⟨1305806, by rfl⟩ : syracuseStep 1741075 = 2611613) B2611613
theorem B1741091 : Blo 1740571 1741091 := bstep (se 1 (by rfl) ⟨1305818, by rfl⟩ : syracuseStep 1741091 = 2611637) B2611637
theorem B6705443 : Blo 1740571 6705443 := bstep (se 1 (by rfl) ⟨5029082, by rfl⟩ : syracuseStep 6705443 = 10058165) B10058165
theorem B5878061 : Blo 1740571 5878061 := bstep (se 3 (by rfl) ⟨1102136, by rfl⟩ : syracuseStep 5878061 = 2204273) B2204273
theorem B4960561 : Blo 1740571 4960561 := bstep (se 2 (by rfl) ⟨1860210, by rfl⟩ : syracuseStep 4960561 = 3720421) B3720421
theorem B5959985 : Blo 1740571 5959985 := bstep (se 2 (by rfl) ⟨2234994, by rfl⟩ : syracuseStep 5959985 = 4469989) B4469989
theorem B2756915 : Blo 1740571 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B1741107 : Blo 1740571 1741107 := bstep (se 1 (by rfl) ⟨1305830, by rfl⟩ : syracuseStep 1741107 = 2611661) B2611661
theorem B1741123 : Blo 1740571 1741123 := bstep (se 1 (by rfl) ⟨1305842, by rfl⟩ : syracuseStep 1741123 = 2611685) B2611685
theorem B8163661 : Blo 1740571 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B1741139 : Blo 1740571 1741139 := bstep (se 1 (by rfl) ⟨1305854, by rfl⟩ : syracuseStep 1741139 = 2611709) B2611709
theorem B2093395 : Blo 1740571 2093395 := bstep (se 1 (by rfl) ⟨1570046, by rfl⟩ : syracuseStep 2093395 = 3140093) B3140093
theorem B1741155 : Blo 1740571 1741155 := bstep (se 1 (by rfl) ⟨1305866, by rfl⟩ : syracuseStep 1741155 = 2611733) B2611733
theorem B5878115 : Blo 1740571 5878115 := bstep (se 1 (by rfl) ⟨4408586, by rfl⟩ : syracuseStep 5878115 = 8817173) B8817173
theorem B1741171 : Blo 1740571 1741171 := bstep (se 1 (by rfl) ⟨1305878, by rfl⟩ : syracuseStep 1741171 = 2611757) B2611757
theorem B1741187 : Blo 1740571 1741187 := bstep (se 1 (by rfl) ⟨1305890, by rfl⟩ : syracuseStep 1741187 = 2611781) B2611781
theorem B3920273 : Blo 1740571 3920273 := bstep (se 2 (by rfl) ⟨1470102, by rfl⟩ : syracuseStep 3920273 = 2940205) B2940205
theorem B2937235 : Blo 1740571 2937235 := bstep (se 1 (by rfl) ⟨2202926, by rfl⟩ : syracuseStep 2937235 = 4405853) B4405853
theorem B1741203 : Blo 1740571 1741203 := bstep (se 1 (by rfl) ⟨1305902, by rfl⟩ : syracuseStep 1741203 = 2611805) B2611805
theorem B1741219 : Blo 1740571 1741219 := bstep (se 1 (by rfl) ⟨1305914, by rfl⟩ : syracuseStep 1741219 = 2611829) B2611829
theorem B3920291 : Blo 1740571 3920291 := bstep (se 1 (by rfl) ⟨2940218, by rfl⟩ : syracuseStep 3920291 = 5880437) B5880437
theorem B1741235 : Blo 1740571 1741235 := bstep (se 1 (by rfl) ⟨1305926, by rfl⟩ : syracuseStep 1741235 = 2611853) B2611853
theorem B1741251 : Blo 1740571 1741251 := bstep (se 1 (by rfl) ⟨1305938, by rfl⟩ : syracuseStep 1741251 = 2611877) B2611877
theorem B1741267 : Blo 1740571 1741267 := bstep (se 1 (by rfl) ⟨1305950, by rfl⟩ : syracuseStep 1741267 = 2611901) B2611901
theorem B1741283 : Blo 1740571 1741283 := bstep (se 1 (by rfl) ⟨1305962, by rfl⟩ : syracuseStep 1741283 = 2611925) B2611925
theorem B11162083 : Blo 1740571 11162083 := bstep (se 1 (by rfl) ⟨8371562, by rfl⟩ : syracuseStep 11162083 = 16743125) B16743125
theorem B1741299 : Blo 1740571 1741299 := bstep (se 1 (by rfl) ⟨1305974, by rfl⟩ : syracuseStep 1741299 = 2611949) B2611949
theorem B2478595 : Blo 1740571 2478595 := bstep (se 1 (by rfl) ⟨1858946, by rfl⟩ : syracuseStep 2478595 = 3717893) B3717893
theorem B1741315 : Blo 1740571 1741315 := bstep (se 1 (by rfl) ⟨1305986, by rfl⟩ : syracuseStep 1741315 = 2611973) B2611973
theorem B1741331 : Blo 1740571 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B2937377 : Blo 1740571 2937377 := bstep (se 2 (by rfl) ⟨1101516, by rfl⟩ : syracuseStep 2937377 = 2203033) B2203033
theorem B1741347 : Blo 1740571 1741347 := bstep (se 1 (by rfl) ⟨1306010, by rfl⟩ : syracuseStep 1741347 = 2612021) B2612021
theorem B1741363 : Blo 1740571 1741363 := bstep (se 1 (by rfl) ⟨1306022, by rfl⟩ : syracuseStep 1741363 = 2612045) B2612045
theorem B1741379 : Blo 1740571 1741379 := bstep (se 1 (by rfl) ⟨1306034, by rfl⟩ : syracuseStep 1741379 = 2612069) B2612069
theorem B4960835 : Blo 1740571 4960835 := bstep (se 1 (by rfl) ⟨3720626, by rfl⟩ : syracuseStep 4960835 = 7441253) B7441253
theorem B1741395 : Blo 1740571 1741395 := bstep (se 1 (by rfl) ⟨1306046, by rfl⟩ : syracuseStep 1741395 = 2612093) B2612093
theorem B2478691 : Blo 1740571 2478691 := bstep (se 1 (by rfl) ⟨1859018, by rfl⟩ : syracuseStep 2478691 = 3718037) B3718037
theorem B1741411 : Blo 1740571 1741411 := bstep (se 1 (by rfl) ⟨1306058, by rfl⟩ : syracuseStep 1741411 = 2612117) B2612117
theorem B5878385 : Blo 1740571 5878385 := bstep (se 2 (by rfl) ⟨2204394, by rfl⟩ : syracuseStep 5878385 = 4408789) B4408789
theorem B1741427 : Blo 1740571 1741427 := bstep (se 1 (by rfl) ⟨1306070, by rfl⟩ : syracuseStep 1741427 = 2612141) B2612141
theorem B1741443 : Blo 1740571 1741443 := bstep (se 1 (by rfl) ⟨1306082, by rfl⟩ : syracuseStep 1741443 = 2612165) B2612165
theorem B1741459 : Blo 1740571 1741459 := bstep (se 1 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 1741459 = 2612189) B2612189
theorem B2937505 : Blo 1740571 2937505 := bstep (se 2 (by rfl) ⟨1101564, by rfl⟩ : syracuseStep 2937505 = 2203129) B2203129
theorem B1741475 : Blo 1740571 1741475 := bstep (se 1 (by rfl) ⟨1306106, by rfl⟩ : syracuseStep 1741475 = 2612213) B2612213
theorem B3920561 : Blo 1740571 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B1741491 : Blo 1740571 1741491 := bstep (se 1 (by rfl) ⟨1306118, by rfl⟩ : syracuseStep 1741491 = 2612237) B2612237
theorem B2937539 : Blo 1740571 2937539 := bstep (se 1 (by rfl) ⟨2203154, by rfl⟩ : syracuseStep 2937539 = 4406309) B4406309
theorem B1741507 : Blo 1740571 1741507 := bstep (se 1 (by rfl) ⟨1306130, by rfl⟩ : syracuseStep 1741507 = 2612261) B2612261
theorem B3920579 : Blo 1740571 3920579 := bstep (se 1 (by rfl) ⟨2940434, by rfl⟩ : syracuseStep 3920579 = 5880869) B5880869
theorem B2978515 : Blo 1740571 2978515 := bstep (se 1 (by rfl) ⟨2233886, by rfl⟩ : syracuseStep 2978515 = 4467773) B4467773
theorem B1741523 : Blo 1740571 1741523 := bstep (se 1 (by rfl) ⟨1306142, by rfl⟩ : syracuseStep 1741523 = 2612285) B2612285
theorem B1741539 : Blo 1740571 1741539 := bstep (se 1 (by rfl) ⟨1306154, by rfl⟩ : syracuseStep 1741539 = 2612309) B2612309
theorem B8819441 : Blo 1740571 8819441 := bstep (se 2 (by rfl) ⟨3307290, by rfl⟩ : syracuseStep 8819441 = 6614581) B6614581
theorem B1741555 : Blo 1740571 1741555 := bstep (se 1 (by rfl) ⟨1306166, by rfl⟩ : syracuseStep 1741555 = 2612333) B2612333
theorem B1741571 : Blo 1740571 1741571 := bstep (se 1 (by rfl) ⟨1306178, by rfl⟩ : syracuseStep 1741571 = 2612357) B2612357
theorem B4961027 : Blo 1740571 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B1741587 : Blo 1740571 1741587 := bstep (se 1 (by rfl) ⟨1306190, by rfl⟩ : syracuseStep 1741587 = 2612381) B2612381
theorem B1741603 : Blo 1740571 1741603 := bstep (se 1 (by rfl) ⟨1306202, by rfl⟩ : syracuseStep 1741603 = 2612405) B2612405
theorem B6615857 : Blo 1740571 6615857 := bstep (se 2 (by rfl) ⟨2480946, by rfl⟩ : syracuseStep 6615857 = 4961893) B4961893
theorem B1741619 : Blo 1740571 1741619 := bstep (se 1 (by rfl) ⟨1306214, by rfl⟩ : syracuseStep 1741619 = 2612429) B2612429
theorem B2937667 : Blo 1740571 2937667 := bstep (se 1 (by rfl) ⟨2203250, by rfl⟩ : syracuseStep 2937667 = 4406501) B4406501
theorem B1741635 : Blo 1740571 1741635 := bstep (se 1 (by rfl) ⟨1306226, by rfl⟩ : syracuseStep 1741635 = 2612453) B2612453
theorem B1741651 : Blo 1740571 1741651 := bstep (se 1 (by rfl) ⟨1306238, by rfl⟩ : syracuseStep 1741651 = 2612477) B2612477
theorem B1741667 : Blo 1740571 1741667 := bstep (se 1 (by rfl) ⟨1306250, by rfl⟩ : syracuseStep 1741667 = 2612501) B2612501
theorem B1741683 : Blo 1740571 1741683 := bstep (se 1 (by rfl) ⟨1306262, by rfl⟩ : syracuseStep 1741683 = 2612525) B2612525
theorem B1741699 : Blo 1740571 1741699 := bstep (se 1 (by rfl) ⟨1306274, by rfl⟩ : syracuseStep 1741699 = 2612549) B2612549
theorem B1741715 : Blo 1740571 1741715 := bstep (se 1 (by rfl) ⟨1306286, by rfl⟩ : syracuseStep 1741715 = 2612573) B2612573
theorem B1741731 : Blo 1740571 1741731 := bstep (se 1 (by rfl) ⟨1306298, by rfl⟩ : syracuseStep 1741731 = 2612597) B2612597
theorem B1741747 : Blo 1740571 1741747 := bstep (se 1 (by rfl) ⟨1306310, by rfl⟩ : syracuseStep 1741747 = 2612621) B2612621
theorem B1741763 : Blo 1740571 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B2937809 : Blo 1740571 2937809 := bstep (se 2 (by rfl) ⟨1101678, by rfl⟩ : syracuseStep 2937809 = 2203357) B2203357
theorem B1741779 : Blo 1740571 1741779 := bstep (se 1 (by rfl) ⟨1306334, by rfl⟩ : syracuseStep 1741779 = 2612669) B2612669
theorem B1741795 : Blo 1740571 1741795 := bstep (se 1 (by rfl) ⟨1306346, by rfl⟩ : syracuseStep 1741795 = 2612693) B2612693
theorem B1741811 : Blo 1740571 1741811 := bstep (se 1 (by rfl) ⟨1306358, by rfl⟩ : syracuseStep 1741811 = 2612717) B2612717
theorem B1741827 : Blo 1740571 1741827 := bstep (se 1 (by rfl) ⟨1306370, by rfl⟩ : syracuseStep 1741827 = 2612741) B2612741
theorem B1741843 : Blo 1740571 1741843 := bstep (se 1 (by rfl) ⟨1306382, by rfl⟩ : syracuseStep 1741843 = 2612765) B2612765
theorem B1741859 : Blo 1740571 1741859 := bstep (se 1 (by rfl) ⟨1306394, by rfl⟩ : syracuseStep 1741859 = 2612789) B2612789
theorem B1741875 : Blo 1740571 1741875 := bstep (se 1 (by rfl) ⟨1306406, by rfl⟩ : syracuseStep 1741875 = 2612813) B2612813
theorem B1741891 : Blo 1740571 1741891 := bstep (se 1 (by rfl) ⟨1306418, by rfl⟩ : syracuseStep 1741891 = 2612837) B2612837
theorem B2937937 : Blo 1740571 2937937 := bstep (se 2 (by rfl) ⟨1101726, by rfl⟩ : syracuseStep 2937937 = 2203453) B2203453
theorem B3306577 : Blo 1740571 3306577 := bstep (se 2 (by rfl) ⟨1239966, by rfl⟩ : syracuseStep 3306577 = 2479933) B2479933
theorem B2479187 : Blo 1740571 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B1741907 : Blo 1740571 1741907 := bstep (se 1 (by rfl) ⟨1306430, by rfl⟩ : syracuseStep 1741907 = 2612861) B2612861
theorem B4183139 : Blo 1740571 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B1741923 : Blo 1740571 1741923 := bstep (se 1 (by rfl) ⟨1306442, by rfl⟩ : syracuseStep 1741923 = 2612885) B2612885
theorem B2937971 : Blo 1740571 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B1741939 : Blo 1740571 1741939 := bstep (se 1 (by rfl) ⟨1306454, by rfl⟩ : syracuseStep 1741939 = 2612909) B2612909
theorem B1741955 : Blo 1740571 1741955 := bstep (se 1 (by rfl) ⟨1306466, by rfl⟩ : syracuseStep 1741955 = 2612933) B2612933
theorem B5878925 : Blo 1740571 5878925 := bstep (se 3 (by rfl) ⟨1102298, by rfl⟩ : syracuseStep 5878925 = 2204597) B2204597
theorem B1741971 : Blo 1740571 1741971 := bstep (se 1 (by rfl) ⟨1306478, by rfl⟩ : syracuseStep 1741971 = 2612957) B2612957
theorem B8369315 : Blo 1740571 8369315 := bstep (se 1 (by rfl) ⟨6276986, by rfl⟩ : syracuseStep 8369315 = 12553973) B12553973
theorem B1741987 : Blo 1740571 1741987 := bstep (se 1 (by rfl) ⟨1306490, by rfl⟩ : syracuseStep 1741987 = 2612981) B2612981
theorem B2978993 : Blo 1740571 2978993 := bstep (se 2 (by rfl) ⟨1117122, by rfl⟩ : syracuseStep 2978993 = 2234245) B2234245
theorem B1742003 : Blo 1740571 1742003 := bstep (se 1 (by rfl) ⟨1306502, by rfl⟩ : syracuseStep 1742003 = 2613005) B2613005
theorem B5878979 : Blo 1740571 5878979 := bstep (se 1 (by rfl) ⟨4409234, by rfl⟩ : syracuseStep 5878979 = 8818469) B8818469
theorem B1742019 : Blo 1740571 1742019 := bstep (se 1 (by rfl) ⟨1306514, by rfl⟩ : syracuseStep 1742019 = 2613029) B2613029
theorem B1742035 : Blo 1740571 1742035 := bstep (se 1 (by rfl) ⟨1306526, by rfl⟩ : syracuseStep 1742035 = 2613053) B2613053
theorem B1742051 : Blo 1740571 1742051 := bstep (se 1 (by rfl) ⟨1306538, by rfl⟩ : syracuseStep 1742051 = 2613077) B2613077
theorem B3306737 : Blo 1740571 3306737 := bstep (se 2 (by rfl) ⟨1240026, by rfl⟩ : syracuseStep 3306737 = 2480053) B2480053
theorem B2938099 : Blo 1740571 2938099 := bstep (se 1 (by rfl) ⟨2203574, by rfl⟩ : syracuseStep 2938099 = 4407149) B4407149
theorem B1742067 : Blo 1740571 1742067 := bstep (se 1 (by rfl) ⟨1306550, by rfl⟩ : syracuseStep 1742067 = 2613101) B2613101
theorem B1742083 : Blo 1740571 1742083 := bstep (se 1 (by rfl) ⟨1306562, by rfl⟩ : syracuseStep 1742083 = 2613125) B2613125
theorem B1742099 : Blo 1740571 1742099 := bstep (se 1 (by rfl) ⟨1306574, by rfl⟩ : syracuseStep 1742099 = 2613149) B2613149
theorem B1742115 : Blo 1740571 1742115 := bstep (se 1 (by rfl) ⟨1306586, by rfl⟩ : syracuseStep 1742115 = 2613173) B2613173
theorem B1742131 : Blo 1740571 1742131 := bstep (se 1 (by rfl) ⟨1306598, by rfl⟩ : syracuseStep 1742131 = 2613197) B2613197
theorem B1742147 : Blo 1740571 1742147 := bstep (se 1 (by rfl) ⟨1306610, by rfl⟩ : syracuseStep 1742147 = 2613221) B2613221
theorem B1742163 : Blo 1740571 1742163 := bstep (se 1 (by rfl) ⟨1306622, by rfl⟩ : syracuseStep 1742163 = 2613245) B2613245
theorem B1742179 : Blo 1740571 1742179 := bstep (se 1 (by rfl) ⟨1306634, by rfl⟩ : syracuseStep 1742179 = 2613269) B2613269
theorem B1742195 : Blo 1740571 1742195 := bstep (se 1 (by rfl) ⟨1306646, by rfl⟩ : syracuseStep 1742195 = 2613293) B2613293
theorem B2938241 : Blo 1740571 2938241 := bstep (se 2 (by rfl) ⟨1101840, by rfl⟩ : syracuseStep 2938241 = 2203681) B2203681
theorem B4183427 : Blo 1740571 4183427 := bstep (se 1 (by rfl) ⟨3137570, by rfl⟩ : syracuseStep 4183427 = 6275141) B6275141
theorem B1742211 : Blo 1740571 1742211 := bstep (se 1 (by rfl) ⟨1306658, by rfl⟩ : syracuseStep 1742211 = 2613317) B2613317
theorem B1742227 : Blo 1740571 1742227 := bstep (se 1 (by rfl) ⟨1306670, by rfl⟩ : syracuseStep 1742227 = 2613341) B2613341
theorem B1742243 : Blo 1740571 1742243 := bstep (se 1 (by rfl) ⟨1306682, by rfl⟩ : syracuseStep 1742243 = 2613365) B2613365
theorem B1742259 : Blo 1740571 1742259 := bstep (se 1 (by rfl) ⟨1306694, by rfl⟩ : syracuseStep 1742259 = 2613389) B2613389
theorem B1742275 : Blo 1740571 1742275 := bstep (se 1 (by rfl) ⟨1306706, by rfl⟩ : syracuseStep 1742275 = 2613413) B2613413
theorem B13227461 : Blo 1740571 13227461 := bstep (se 4 (by rfl) ⟨1240074, by rfl⟩ : syracuseStep 13227461 = 2480149) B2480149
theorem B5879249 : Blo 1740571 5879249 := bstep (se 2 (by rfl) ⟨2204718, by rfl⟩ : syracuseStep 5879249 = 4409437) B4409437
theorem B1742291 : Blo 1740571 1742291 := bstep (se 1 (by rfl) ⟨1306718, by rfl⟩ : syracuseStep 1742291 = 2613437) B2613437
theorem B1742307 : Blo 1740571 1742307 := bstep (se 1 (by rfl) ⟨1306730, by rfl⟩ : syracuseStep 1742307 = 2613461) B2613461
theorem B19830257 : Blo 1740571 19830257 := bstep (se 2 (by rfl) ⟨7436346, by rfl⟩ : syracuseStep 19830257 = 14872693) B14872693
theorem B1742323 : Blo 1740571 1742323 := bstep (se 1 (by rfl) ⟨1306742, by rfl⟩ : syracuseStep 1742323 = 2613485) B2613485
theorem B2938369 : Blo 1740571 2938369 := bstep (se 2 (by rfl) ⟨1101888, by rfl⟩ : syracuseStep 2938369 = 2203777) B2203777
theorem B1742339 : Blo 1740571 1742339 := bstep (se 1 (by rfl) ⟨1306754, by rfl⟩ : syracuseStep 1742339 = 2613509) B2613509
theorem B9410053 : Blo 1740571 9410053 := bstep (se 4 (by rfl) ⟨882192, by rfl⟩ : syracuseStep 9410053 = 1764385) B1764385
theorem B1742355 : Blo 1740571 1742355 := bstep (se 1 (by rfl) ⟨1306766, by rfl⟩ : syracuseStep 1742355 = 2613533) B2613533
theorem B2790931 : Blo 1740571 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B2938403 : Blo 1740571 2938403 := bstep (se 1 (by rfl) ⟨2203802, by rfl⟩ : syracuseStep 2938403 = 4407605) B4407605
theorem B1742371 : Blo 1740571 1742371 := bstep (se 1 (by rfl) ⟨1306778, by rfl⟩ : syracuseStep 1742371 = 2613557) B2613557
theorem B4961837 : Blo 1740571 4961837 := bstep (se 3 (by rfl) ⟨930344, by rfl⟩ : syracuseStep 4961837 = 1860689) B1860689
theorem B1742387 : Blo 1740571 1742387 := bstep (se 1 (by rfl) ⟨1306790, by rfl⟩ : syracuseStep 1742387 = 2613581) B2613581
theorem B1742403 : Blo 1740571 1742403 := bstep (se 1 (by rfl) ⟨1306802, by rfl⟩ : syracuseStep 1742403 = 2613605) B2613605
theorem B1742419 : Blo 1740571 1742419 := bstep (se 1 (by rfl) ⟨1306814, by rfl⟩ : syracuseStep 1742419 = 2613629) B2613629
theorem B1742435 : Blo 1740571 1742435 := bstep (se 1 (by rfl) ⟨1306826, by rfl⟩ : syracuseStep 1742435 = 2613653) B2613653
theorem B24155761 : Blo 1740571 24155761 := bstep (se 2 (by rfl) ⟨9058410, by rfl⟩ : syracuseStep 24155761 = 18116821) B18116821
theorem B1742451 : Blo 1740571 1742451 := bstep (se 1 (by rfl) ⟨1306838, by rfl⟩ : syracuseStep 1742451 = 2613677) B2613677
theorem B3307139 : Blo 1740571 3307139 := bstep (se 1 (by rfl) ⟨2480354, by rfl⟩ : syracuseStep 3307139 = 4960709) B4960709
theorem B1742467 : Blo 1740571 1742467 := bstep (se 1 (by rfl) ⟨1306850, by rfl⟩ : syracuseStep 1742467 = 2613701) B2613701
theorem B1742483 : Blo 1740571 1742483 := bstep (se 1 (by rfl) ⟨1306862, by rfl⟩ : syracuseStep 1742483 = 2613725) B2613725
theorem B2938531 : Blo 1740571 2938531 := bstep (se 1 (by rfl) ⟨2203898, by rfl⟩ : syracuseStep 2938531 = 4407797) B4407797
theorem B1742499 : Blo 1740571 1742499 := bstep (se 1 (by rfl) ⟨1306874, by rfl⟩ : syracuseStep 1742499 = 2613749) B2613749
theorem B1742515 : Blo 1740571 1742515 := bstep (se 1 (by rfl) ⟨1306886, by rfl⟩ : syracuseStep 1742515 = 2613773) B2613773
theorem B2610881 : Blo 1740571 2610881 := bstep (se 2 (by rfl) ⟨979080, by rfl⟩ : syracuseStep 2610881 = 1958161) B1958161
theorem B1742531 : Blo 1740571 1742531 := bstep (se 1 (by rfl) ⟨1306898, by rfl⟩ : syracuseStep 1742531 = 2613797) B2613797
theorem B2479825 : Blo 1740571 2479825 := bstep (se 2 (by rfl) ⟨929934, by rfl⟩ : syracuseStep 2479825 = 1859869) B1859869
theorem B2610899 : Blo 1740571 2610899 := bstep (se 1 (by rfl) ⟨1958174, by rfl⟩ : syracuseStep 2610899 = 3916349) B3916349
theorem B1742547 : Blo 1740571 1742547 := bstep (se 1 (by rfl) ⟨1306910, by rfl⟩ : syracuseStep 1742547 = 2613821) B2613821
theorem B22304483 : Blo 1740571 22304483 := bstep (se 1 (by rfl) ⟨16728362, by rfl⟩ : syracuseStep 22304483 = 33456725) B33456725
theorem B4962019 : Blo 1740571 4962019 := bstep (se 1 (by rfl) ⟨3721514, by rfl⟩ : syracuseStep 4962019 = 7443029) B7443029
theorem B1742563 : Blo 1740571 1742563 := bstep (se 1 (by rfl) ⟨1306922, by rfl⟩ : syracuseStep 1742563 = 2613845) B2613845
theorem B2610929 : Blo 1740571 2610929 := bstep (se 2 (by rfl) ⟨979098, by rfl⟩ : syracuseStep 2610929 = 1958197) B1958197
theorem B2610947 : Blo 1740571 2610947 := bstep (se 1 (by rfl) ⟨1958210, by rfl⟩ : syracuseStep 2610947 = 3916421) B3916421
theorem B2610977 : Blo 1740571 2610977 := bstep (se 2 (by rfl) ⟨979116, by rfl⟩ : syracuseStep 2610977 = 1958233) B1958233
theorem B2938673 : Blo 1740571 2938673 := bstep (se 2 (by rfl) ⟨1102002, by rfl⟩ : syracuseStep 2938673 = 2204005) B2204005
theorem B2610995 : Blo 1740571 2610995 := bstep (se 1 (by rfl) ⟨1958246, by rfl⟩ : syracuseStep 2610995 = 3916493) B3916493
theorem B2611025 : Blo 1740571 2611025 := bstep (se 2 (by rfl) ⟨979134, by rfl⟩ : syracuseStep 2611025 = 1958269) B1958269
theorem B2611043 : Blo 1740571 2611043 := bstep (se 1 (by rfl) ⟨1958282, by rfl⟩ : syracuseStep 2611043 = 3916565) B3916565
theorem B2611073 : Blo 1740571 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B2611091 : Blo 1740571 2611091 := bstep (se 1 (by rfl) ⟨1958318, by rfl⟩ : syracuseStep 2611091 = 3916637) B3916637
theorem B7436195 : Blo 1740571 7436195 := bstep (se 1 (by rfl) ⟨5577146, by rfl⟩ : syracuseStep 7436195 = 11154293) B11154293
theorem B2611121 : Blo 1740571 2611121 := bstep (se 2 (by rfl) ⟨979170, by rfl⟩ : syracuseStep 2611121 = 1958341) B1958341
theorem B2938801 : Blo 1740571 2938801 := bstep (se 2 (by rfl) ⟨1102050, by rfl⟩ : syracuseStep 2938801 = 2204101) B2204101
theorem B2611139 : Blo 1740571 2611139 := bstep (se 1 (by rfl) ⟨1958354, by rfl⟩ : syracuseStep 2611139 = 3916709) B3916709
theorem B5027789 : Blo 1740571 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B2938835 : Blo 1740571 2938835 := bstep (se 1 (by rfl) ⟨2204126, by rfl⟩ : syracuseStep 2938835 = 4408253) B4408253
theorem B2611169 : Blo 1740571 2611169 := bstep (se 2 (by rfl) ⟨979188, by rfl⟩ : syracuseStep 2611169 = 1958377) B1958377
theorem B5879789 : Blo 1740571 5879789 := bstep (se 3 (by rfl) ⟨1102460, by rfl⟩ : syracuseStep 5879789 = 2204921) B2204921
theorem B2611187 : Blo 1740571 2611187 := bstep (se 1 (by rfl) ⟨1958390, by rfl⟩ : syracuseStep 2611187 = 3916781) B3916781
theorem B2611217 : Blo 1740571 2611217 := bstep (se 2 (by rfl) ⟨979206, by rfl⟩ : syracuseStep 2611217 = 1958413) B1958413
theorem B2480161 : Blo 1740571 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B2611235 : Blo 1740571 2611235 := bstep (se 1 (by rfl) ⟨1958426, by rfl⟩ : syracuseStep 2611235 = 3916853) B3916853
theorem B5879843 : Blo 1740571 5879843 := bstep (se 1 (by rfl) ⟨4409882, by rfl⟩ : syracuseStep 5879843 = 8819765) B8819765
theorem B2611265 : Blo 1740571 2611265 := bstep (se 2 (by rfl) ⟨979224, by rfl⟩ : syracuseStep 2611265 = 1958449) B1958449
theorem B2611283 : Blo 1740571 2611283 := bstep (se 1 (by rfl) ⟨1958462, by rfl⟩ : syracuseStep 2611283 = 3916925) B3916925
theorem B2938963 : Blo 1740571 2938963 := bstep (se 1 (by rfl) ⟨2204222, by rfl⟩ : syracuseStep 2938963 = 4408445) B4408445
theorem B5093489 : Blo 1740571 5093489 := bstep (se 2 (by rfl) ⟨1910058, by rfl⟩ : syracuseStep 5093489 = 3820117) B3820117
theorem B2611313 : Blo 1740571 2611313 := bstep (se 2 (by rfl) ⟨979242, by rfl⟩ : syracuseStep 2611313 = 1958485) B1958485
theorem B2611331 : Blo 1740571 2611331 := bstep (se 1 (by rfl) ⟨1958498, by rfl⟩ : syracuseStep 2611331 = 3916997) B3916997
theorem B10049669 : Blo 1740571 10049669 := bstep (se 4 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 10049669 = 1884313) B1884313
theorem B2611361 : Blo 1740571 2611361 := bstep (se 2 (by rfl) ⟨979260, by rfl⟩ : syracuseStep 2611361 = 1958521) B1958521
theorem B8820899 : Blo 1740571 8820899 := bstep (se 1 (by rfl) ⟨6615674, by rfl⟩ : syracuseStep 8820899 = 13231349) B13231349
theorem B2611379 : Blo 1740571 2611379 := bstep (se 1 (by rfl) ⟨1958534, by rfl⟩ : syracuseStep 2611379 = 3917069) B3917069
theorem B22313141 : Blo 1740571 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B2611409 : Blo 1740571 2611409 := bstep (se 2 (by rfl) ⟨979278, by rfl⟩ : syracuseStep 2611409 = 1958557) B1958557
theorem B4184273 : Blo 1740571 4184273 := bstep (se 2 (by rfl) ⟨1569102, by rfl⟩ : syracuseStep 4184273 = 3138205) B3138205
theorem B2939105 : Blo 1740571 2939105 := bstep (se 2 (by rfl) ⟨1102164, by rfl⟩ : syracuseStep 2939105 = 2204329) B2204329
theorem B2611427 : Blo 1740571 2611427 := bstep (se 1 (by rfl) ⟨1958570, by rfl⟩ : syracuseStep 2611427 = 3917141) B3917141
theorem B5576941 : Blo 1740571 5576941 := bstep (se 3 (by rfl) ⟨1045676, by rfl⟩ : syracuseStep 5576941 = 2091353) B2091353
theorem B2611457 : Blo 1740571 2611457 := bstep (se 2 (by rfl) ⟨979296, by rfl⟩ : syracuseStep 2611457 = 1958593) B1958593
theorem B2611475 : Blo 1740571 2611475 := bstep (se 1 (by rfl) ⟨1958606, by rfl⟩ : syracuseStep 2611475 = 3917213) B3917213
theorem B5577005 : Blo 1740571 5577005 := bstep (se 3 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 5577005 = 2091377) B2091377
theorem B2611505 : Blo 1740571 2611505 := bstep (se 2 (by rfl) ⟨979314, by rfl⟩ : syracuseStep 2611505 = 1958629) B1958629
theorem B4184369 : Blo 1740571 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B5880113 : Blo 1740571 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B18839861 : Blo 1740571 18839861 := bstep (se 5 (by rfl) ⟨883118, by rfl⟩ : syracuseStep 18839861 = 1766237) B1766237
theorem B2611523 : Blo 1740571 2611523 := bstep (se 1 (by rfl) ⟨1958642, by rfl⟩ : syracuseStep 2611523 = 3917285) B3917285
theorem B2611553 : Blo 1740571 2611553 := bstep (se 2 (by rfl) ⟨979332, by rfl⟩ : syracuseStep 2611553 = 1958665) B1958665
theorem B2939233 : Blo 1740571 2939233 := bstep (se 2 (by rfl) ⟨1102212, by rfl⟩ : syracuseStep 2939233 = 2204425) B2204425
theorem B2611571 : Blo 1740571 2611571 := bstep (se 1 (by rfl) ⟨1958678, by rfl⟩ : syracuseStep 2611571 = 3917357) B3917357
theorem B2939267 : Blo 1740571 2939267 := bstep (se 1 (by rfl) ⟨2204450, by rfl⟩ : syracuseStep 2939267 = 4408901) B4408901
theorem B2611601 : Blo 1740571 2611601 := bstep (se 2 (by rfl) ⟨979350, by rfl⟩ : syracuseStep 2611601 = 1958701) B1958701
theorem B2611619 : Blo 1740571 2611619 := bstep (se 1 (by rfl) ⟨1958714, by rfl⟩ : syracuseStep 2611619 = 3917429) B3917429
theorem B7059889 : Blo 1740571 7059889 := bstep (se 2 (by rfl) ⟨2647458, by rfl⟩ : syracuseStep 7059889 = 5294917) B5294917
theorem B2611649 : Blo 1740571 2611649 := bstep (se 2 (by rfl) ⟨979368, by rfl⟩ : syracuseStep 2611649 = 1958737) B1958737
theorem B2611667 : Blo 1740571 2611667 := bstep (se 1 (by rfl) ⟨1958750, by rfl⟩ : syracuseStep 2611667 = 3917501) B3917501
theorem B5298641 : Blo 1740571 5298641 := bstep (se 2 (by rfl) ⟨1986990, by rfl⟩ : syracuseStep 5298641 = 3973981) B3973981
theorem B2611697 : Blo 1740571 2611697 := bstep (se 2 (by rfl) ⟨979386, by rfl⟩ : syracuseStep 2611697 = 1958773) B1958773
theorem B4184561 : Blo 1740571 4184561 := bstep (se 2 (by rfl) ⟨1569210, by rfl⟩ : syracuseStep 4184561 = 3138421) B3138421
theorem B2611715 : Blo 1740571 2611715 := bstep (se 1 (by rfl) ⟨1958786, by rfl⟩ : syracuseStep 2611715 = 3917573) B3917573
theorem B2939395 : Blo 1740571 2939395 := bstep (se 1 (by rfl) ⟨2204546, by rfl⟩ : syracuseStep 2939395 = 4409093) B4409093
theorem B3308035 : Blo 1740571 3308035 := bstep (se 1 (by rfl) ⟨2481026, by rfl⟩ : syracuseStep 3308035 = 4962053) B4962053
theorem B2611745 : Blo 1740571 2611745 := bstep (se 2 (by rfl) ⟨979404, by rfl⟩ : syracuseStep 2611745 = 1958809) B1958809
theorem B2611763 : Blo 1740571 2611763 := bstep (se 1 (by rfl) ⟨1958822, by rfl⟩ : syracuseStep 2611763 = 3917645) B3917645
theorem B3717713 : Blo 1740571 3717713 := bstep (se 2 (by rfl) ⟨1394142, by rfl⟩ : syracuseStep 3717713 = 2788285) B2788285
theorem B2611793 : Blo 1740571 2611793 := bstep (se 2 (by rfl) ⟨979422, by rfl⟩ : syracuseStep 2611793 = 1958845) B1958845
theorem B2611811 : Blo 1740571 2611811 := bstep (se 1 (by rfl) ⟨1958858, by rfl⟩ : syracuseStep 2611811 = 3917717) B3917717
theorem B4405873 : Blo 1740571 4405873 := bstep (se 2 (by rfl) ⟨1652202, by rfl⟩ : syracuseStep 4405873 = 3304405) B3304405
theorem B2480753 : Blo 1740571 2480753 := bstep (se 2 (by rfl) ⟨930282, by rfl⟩ : syracuseStep 2480753 = 1860565) B1860565
theorem B2611841 : Blo 1740571 2611841 := bstep (se 2 (by rfl) ⟨979440, by rfl⟩ : syracuseStep 2611841 = 1958881) B1958881
theorem B2939537 : Blo 1740571 2939537 := bstep (se 2 (by rfl) ⟨1102326, by rfl⟩ : syracuseStep 2939537 = 2204653) B2204653
theorem B2611859 : Blo 1740571 2611859 := bstep (se 1 (by rfl) ⟨1958894, by rfl⟩ : syracuseStep 2611859 = 3917789) B3917789
theorem B2611889 : Blo 1740571 2611889 := bstep (se 2 (by rfl) ⟨979458, by rfl⟩ : syracuseStep 2611889 = 1958917) B1958917
theorem B2611907 : Blo 1740571 2611907 := bstep (se 1 (by rfl) ⟨1958930, by rfl⟩ : syracuseStep 2611907 = 3917861) B3917861
theorem B2611937 : Blo 1740571 2611937 := bstep (se 2 (by rfl) ⟨979476, by rfl⟩ : syracuseStep 2611937 = 1958953) B1958953
theorem B2611955 : Blo 1740571 2611955 := bstep (se 1 (by rfl) ⟨1958966, by rfl⟩ : syracuseStep 2611955 = 3917933) B3917933
theorem B2611985 : Blo 1740571 2611985 := bstep (se 2 (by rfl) ⟨979494, by rfl⟩ : syracuseStep 2611985 = 1958989) B1958989
theorem B2939665 : Blo 1740571 2939665 := bstep (se 2 (by rfl) ⟨1102374, by rfl⟩ : syracuseStep 2939665 = 2204749) B2204749
theorem B2612003 : Blo 1740571 2612003 := bstep (se 1 (by rfl) ⟨1959002, by rfl⟩ : syracuseStep 2612003 = 3918005) B3918005
theorem B2939699 : Blo 1740571 2939699 := bstep (se 1 (by rfl) ⟨2204774, by rfl⟩ : syracuseStep 2939699 = 4409549) B4409549
theorem B2612033 : Blo 1740571 2612033 := bstep (se 2 (by rfl) ⟨979512, by rfl⟩ : syracuseStep 2612033 = 1959025) B1959025
theorem B5880653 : Blo 1740571 5880653 := bstep (se 3 (by rfl) ⟨1102622, by rfl⟩ : syracuseStep 5880653 = 2205245) B2205245
theorem B2612051 : Blo 1740571 2612051 := bstep (se 1 (by rfl) ⟨1959038, by rfl⟩ : syracuseStep 2612051 = 3918077) B3918077
theorem B2612081 : Blo 1740571 2612081 := bstep (se 2 (by rfl) ⟨979530, by rfl⟩ : syracuseStep 2612081 = 1959061) B1959061
theorem B4406147 : Blo 1740571 4406147 := bstep (se 1 (by rfl) ⟨3304610, by rfl⟩ : syracuseStep 4406147 = 6609221) B6609221
theorem B2612099 : Blo 1740571 2612099 := bstep (se 1 (by rfl) ⟨1959074, by rfl⟩ : syracuseStep 2612099 = 3918149) B3918149
theorem B5880707 : Blo 1740571 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B2612129 : Blo 1740571 2612129 := bstep (se 2 (by rfl) ⟨979548, by rfl⟩ : syracuseStep 2612129 = 1959097) B1959097
theorem B2612147 : Blo 1740571 2612147 := bstep (se 1 (by rfl) ⟨1959110, by rfl⟩ : syracuseStep 2612147 = 3918221) B3918221
theorem B2939827 : Blo 1740571 2939827 := bstep (se 1 (by rfl) ⟨2204870, by rfl⟩ : syracuseStep 2939827 = 4409741) B4409741
theorem B8821709 : Blo 1740571 8821709 := bstep (se 3 (by rfl) ⟨1654070, by rfl⟩ : syracuseStep 8821709 = 3308141) B3308141
theorem B2612177 : Blo 1740571 2612177 := bstep (se 2 (by rfl) ⟨979566, by rfl⟩ : syracuseStep 2612177 = 1959133) B1959133
theorem B2612195 : Blo 1740571 2612195 := bstep (se 1 (by rfl) ⟨1959146, by rfl⟩ : syracuseStep 2612195 = 3918293) B3918293
theorem B2612225 : Blo 1740571 2612225 := bstep (se 2 (by rfl) ⟨979584, by rfl⟩ : syracuseStep 2612225 = 1959169) B1959169
theorem B2612243 : Blo 1740571 2612243 := bstep (se 1 (by rfl) ⟨1959182, by rfl⟩ : syracuseStep 2612243 = 3918365) B3918365
theorem B2612273 : Blo 1740571 2612273 := bstep (se 2 (by rfl) ⟨979602, by rfl⟩ : syracuseStep 2612273 = 1959205) B1959205
theorem B2939969 : Blo 1740571 2939969 := bstep (se 2 (by rfl) ⟨1102488, by rfl⟩ : syracuseStep 2939969 = 2204977) B2204977
theorem B4406339 : Blo 1740571 4406339 := bstep (se 1 (by rfl) ⟨3304754, by rfl⟩ : syracuseStep 4406339 = 6609509) B6609509
theorem B2612291 : Blo 1740571 2612291 := bstep (se 1 (by rfl) ⟨1959218, by rfl⟩ : syracuseStep 2612291 = 3918437) B3918437
theorem B2612321 : Blo 1740571 2612321 := bstep (se 2 (by rfl) ⟨979620, by rfl⟩ : syracuseStep 2612321 = 1959241) B1959241
theorem B8371313 : Blo 1740571 8371313 := bstep (se 2 (by rfl) ⟨3139242, by rfl⟩ : syracuseStep 8371313 = 6278485) B6278485
theorem B2612339 : Blo 1740571 2612339 := bstep (se 1 (by rfl) ⟨1959254, by rfl⟩ : syracuseStep 2612339 = 3918509) B3918509
theorem B2612369 : Blo 1740571 2612369 := bstep (se 2 (by rfl) ⟨979638, by rfl⟩ : syracuseStep 2612369 = 1959277) B1959277
theorem B5880977 : Blo 1740571 5880977 := bstep (se 2 (by rfl) ⟨2205366, by rfl⟩ : syracuseStep 5880977 = 4410733) B4410733
theorem B2612387 : Blo 1740571 2612387 := bstep (se 1 (by rfl) ⟨1959290, by rfl⟩ : syracuseStep 2612387 = 3918581) B3918581
theorem B2612417 : Blo 1740571 2612417 := bstep (se 2 (by rfl) ⟨979656, by rfl⟩ : syracuseStep 2612417 = 1959313) B1959313
theorem B2940097 : Blo 1740571 2940097 := bstep (se 2 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 2940097 = 2205073) B2205073
theorem B9919685 : Blo 1740571 9919685 := bstep (se 4 (by rfl) ⟨929970, by rfl⟩ : syracuseStep 9919685 = 1859941) B1859941
theorem B11164877 : Blo 1740571 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B2612435 : Blo 1740571 2612435 := bstep (se 1 (by rfl) ⟨1959326, by rfl⟩ : syracuseStep 2612435 = 3918653) B3918653
theorem B2940131 : Blo 1740571 2940131 := bstep (se 1 (by rfl) ⟨2205098, by rfl⟩ : syracuseStep 2940131 = 4410197) B4410197
theorem B2612465 : Blo 1740571 2612465 := bstep (se 2 (by rfl) ⟨979674, by rfl⟩ : syracuseStep 2612465 = 1959349) B1959349
theorem B2612483 : Blo 1740571 2612483 := bstep (se 1 (by rfl) ⟨1959362, by rfl⟩ : syracuseStep 2612483 = 3918725) B3918725
theorem B2612513 : Blo 1740571 2612513 := bstep (se 2 (by rfl) ⟨979692, by rfl⟩ : syracuseStep 2612513 = 1959385) B1959385
theorem B2612531 : Blo 1740571 2612531 := bstep (se 1 (by rfl) ⟨1959398, by rfl⟩ : syracuseStep 2612531 = 3918797) B3918797
theorem B2612561 : Blo 1740571 2612561 := bstep (se 2 (by rfl) ⟨979710, by rfl⟩ : syracuseStep 2612561 = 1959421) B1959421
theorem B2612579 : Blo 1740571 2612579 := bstep (se 1 (by rfl) ⟨1959434, by rfl⟩ : syracuseStep 2612579 = 3918869) B3918869
theorem B2940259 : Blo 1740571 2940259 := bstep (se 1 (by rfl) ⟨2205194, by rfl⟩ : syracuseStep 2940259 = 4410389) B4410389
theorem B2612609 : Blo 1740571 2612609 := bstep (se 2 (by rfl) ⟨979728, by rfl⟩ : syracuseStep 2612609 = 1959457) B1959457
theorem B22322573 : Blo 1740571 22322573 := bstep (se 3 (by rfl) ⟨4185482, by rfl⟩ : syracuseStep 22322573 = 8370965) B8370965
theorem B2612627 : Blo 1740571 2612627 := bstep (se 1 (by rfl) ⟨1959470, by rfl⟩ : syracuseStep 2612627 = 3918941) B3918941
theorem B2612657 : Blo 1740571 2612657 := bstep (se 2 (by rfl) ⟨979746, by rfl⟩ : syracuseStep 2612657 = 1959493) B1959493
theorem B2612675 : Blo 1740571 2612675 := bstep (se 1 (by rfl) ⟨1959506, by rfl⟩ : syracuseStep 2612675 = 3919013) B3919013
theorem B2612705 : Blo 1740571 2612705 := bstep (se 2 (by rfl) ⟨979764, by rfl⟩ : syracuseStep 2612705 = 1959529) B1959529
theorem B2940401 : Blo 1740571 2940401 := bstep (se 2 (by rfl) ⟨1102650, by rfl⟩ : syracuseStep 2940401 = 2205301) B2205301
theorem B2612723 : Blo 1740571 2612723 := bstep (se 1 (by rfl) ⟨1959542, by rfl⟩ : syracuseStep 2612723 = 3919085) B3919085
theorem B2203139 : Blo 1740571 2203139 := bstep (se 1 (by rfl) ⟨1652354, by rfl⟩ : syracuseStep 2203139 = 3304709) B3304709
theorem B2612753 : Blo 1740571 2612753 := bstep (se 2 (by rfl) ⟨979782, by rfl⟩ : syracuseStep 2612753 = 1959565) B1959565
theorem B2612771 : Blo 1740571 2612771 := bstep (se 1 (by rfl) ⟨1959578, by rfl⟩ : syracuseStep 2612771 = 3919157) B3919157
theorem B6610481 : Blo 1740571 6610481 := bstep (se 2 (by rfl) ⟨2478930, by rfl⟩ : syracuseStep 6610481 = 4957861) B4957861
theorem B2612801 : Blo 1740571 2612801 := bstep (se 2 (by rfl) ⟨979800, by rfl⟩ : syracuseStep 2612801 = 1959601) B1959601
theorem B1859155 : Blo 1740571 1859155 := bstep (se 1 (by rfl) ⟨1394366, by rfl⟩ : syracuseStep 1859155 = 2788733) B2788733
theorem B2612819 : Blo 1740571 2612819 := bstep (se 1 (by rfl) ⟨1959614, by rfl⟩ : syracuseStep 2612819 = 3919229) B3919229
theorem B2612849 : Blo 1740571 2612849 := bstep (se 2 (by rfl) ⟨979818, by rfl⟩ : syracuseStep 2612849 = 1959637) B1959637
theorem B4185713 : Blo 1740571 4185713 := bstep (se 2 (by rfl) ⟨1569642, by rfl⟩ : syracuseStep 4185713 = 3139285) B3139285
theorem B2940529 : Blo 1740571 2940529 := bstep (se 2 (by rfl) ⟨1102698, by rfl⟩ : syracuseStep 2940529 = 2205397) B2205397
theorem B2612867 : Blo 1740571 2612867 := bstep (se 1 (by rfl) ⟨1959650, by rfl⟩ : syracuseStep 2612867 = 3919301) B3919301
theorem B10591877 : Blo 1740571 10591877 := bstep (se 4 (by rfl) ⟨992988, by rfl⟩ : syracuseStep 10591877 = 1985977) B1985977
theorem B9920141 : Blo 1740571 9920141 := bstep (se 3 (by rfl) ⟨1860026, by rfl⟩ : syracuseStep 9920141 = 3720053) B3720053
theorem B2940563 : Blo 1740571 2940563 := bstep (se 1 (by rfl) ⟨2205422, by rfl⟩ : syracuseStep 2940563 = 4410845) B4410845
theorem B2612897 : Blo 1740571 2612897 := bstep (se 2 (by rfl) ⟨979836, by rfl⟩ : syracuseStep 2612897 = 1959673) B1959673
theorem B8814257 : Blo 1740571 8814257 := bstep (se 2 (by rfl) ⟨3305346, by rfl⟩ : syracuseStep 8814257 = 6610693) B6610693
theorem B2612915 : Blo 1740571 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B9412301 : Blo 1740571 9412301 := bstep (se 3 (by rfl) ⟨1764806, by rfl⟩ : syracuseStep 9412301 = 3529613) B3529613
theorem B2612945 : Blo 1740571 2612945 := bstep (se 2 (by rfl) ⟨979854, by rfl⟩ : syracuseStep 2612945 = 1959709) B1959709
theorem B2612963 : Blo 1740571 2612963 := bstep (se 1 (by rfl) ⟨1959722, by rfl⟩ : syracuseStep 2612963 = 3919445) B3919445
theorem B29769443 : Blo 1740571 29769443 := bstep (se 1 (by rfl) ⟨22327082, by rfl⟩ : syracuseStep 29769443 = 44654165) B44654165
theorem B2612993 : Blo 1740571 2612993 := bstep (se 2 (by rfl) ⟨979872, by rfl⟩ : syracuseStep 2612993 = 1959745) B1959745
theorem B2613011 : Blo 1740571 2613011 := bstep (se 1 (by rfl) ⟨1959758, by rfl⟩ : syracuseStep 2613011 = 3919517) B3919517
theorem B2613041 : Blo 1740571 2613041 := bstep (se 2 (by rfl) ⟨979890, by rfl⟩ : syracuseStep 2613041 = 1959781) B1959781
theorem B2613059 : Blo 1740571 2613059 := bstep (se 1 (by rfl) ⟨1959794, by rfl⟩ : syracuseStep 2613059 = 3919589) B3919589
theorem B6700877 : Blo 1740571 6700877 := bstep (se 3 (by rfl) ⟨1256414, by rfl⟩ : syracuseStep 6700877 = 2512829) B2512829
theorem B2613089 : Blo 1740571 2613089 := bstep (se 2 (by rfl) ⟨979908, by rfl⟩ : syracuseStep 2613089 = 1959817) B1959817
theorem B33464177 : Blo 1740571 33464177 := bstep (se 2 (by rfl) ⟨12549066, by rfl⟩ : syracuseStep 33464177 = 25098133) B25098133
theorem B7438193 : Blo 1740571 7438193 := bstep (se 2 (by rfl) ⟨2789322, by rfl⟩ : syracuseStep 7438193 = 5578645) B5578645
theorem B2613107 : Blo 1740571 2613107 := bstep (se 1 (by rfl) ⟨1959830, by rfl⟩ : syracuseStep 2613107 = 3919661) B3919661
theorem B3137411 : Blo 1740571 3137411 := bstep (se 1 (by rfl) ⟨2353058, by rfl⟩ : syracuseStep 3137411 = 4706117) B4706117
theorem B2613137 : Blo 1740571 2613137 := bstep (se 2 (by rfl) ⟨979926, by rfl⟩ : syracuseStep 2613137 = 1959853) B1959853
theorem B2613155 : Blo 1740571 2613155 := bstep (se 1 (by rfl) ⟨1959866, by rfl⟩ : syracuseStep 2613155 = 3919733) B3919733
theorem B2613185 : Blo 1740571 2613185 := bstep (se 2 (by rfl) ⟨979944, by rfl⟩ : syracuseStep 2613185 = 1959889) B1959889
theorem B2613203 : Blo 1740571 2613203 := bstep (se 1 (by rfl) ⟨1959902, by rfl⟩ : syracuseStep 2613203 = 3919805) B3919805
theorem B4407281 : Blo 1740571 4407281 := bstep (se 2 (by rfl) ⟨1652730, by rfl⟩ : syracuseStep 4407281 = 3305461) B3305461
theorem B2613233 : Blo 1740571 2613233 := bstep (se 2 (by rfl) ⟨979962, by rfl⟩ : syracuseStep 2613233 = 1959925) B1959925
theorem B7946243 : Blo 1740571 7946243 := bstep (se 1 (by rfl) ⟨5959682, by rfl⟩ : syracuseStep 7946243 = 11919365) B11919365
theorem B6610967 : Blo 1740571 6610967 := bstep (se 1 (by rfl) ⟨4958225, by rfl⟩ : syracuseStep 6610967 = 9916451) B9916451
theorem B3719191 : Blo 1740571 3719191 := bstep (se 1 (by rfl) ⟨2789393, by rfl⟩ : syracuseStep 3719191 = 5578787) B5578787
theorem B3719233 : Blo 1740571 3719233 := bstep (se 2 (by rfl) ⟨1394712, by rfl⟩ : syracuseStep 3719233 = 2789425) B2789425
theorem B18120779 : Blo 1740571 18120779 := bstep (se 1 (by rfl) ⟨13590584, by rfl⟩ : syracuseStep 18120779 = 27181169) B27181169
theorem B2613323 : Blo 1740571 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B2613335 : Blo 1740571 2613335 := bstep (se 1 (by rfl) ⟨1960001, by rfl⟩ : syracuseStep 2613335 = 3920003) B3920003
theorem B2203787 : Blo 1740571 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B8814743 : Blo 1740571 8814743 := bstep (se 1 (by rfl) ⟨6611057, by rfl⟩ : syracuseStep 8814743 = 13222115) B13222115
theorem B2613401 : Blo 1740571 2613401 := bstep (se 2 (by rfl) ⟨980025, by rfl⟩ : syracuseStep 2613401 = 1960051) B1960051
theorem B6611165 : Blo 1740571 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B2613515 : Blo 1740571 2613515 := bstep (se 1 (by rfl) ⟨1960136, by rfl⟩ : syracuseStep 2613515 = 3920273) B3920273
theorem B2613527 : Blo 1740571 2613527 := bstep (se 1 (by rfl) ⟨1960145, by rfl⟩ : syracuseStep 2613527 = 3920291) B3920291
theorem B13582637 : Blo 1740571 13582637 := bstep (se 3 (by rfl) ⟨2546744, by rfl⟩ : syracuseStep 13582637 = 5093489) B5093489
theorem B2613593 : Blo 1740571 2613593 := bstep (se 2 (by rfl) ⟨980097, by rfl⟩ : syracuseStep 2613593 = 1960195) B1960195
theorem B1958251 : Blo 1740571 1958251 := bstep (se 1 (by rfl) ⟨1468688, by rfl⟩ : syracuseStep 1958251 = 2937377) B2937377
theorem B2613707 : Blo 1740571 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B1958359 : Blo 1740571 1958359 := bstep (se 1 (by rfl) ⟨1468769, by rfl⟩ : syracuseStep 1958359 = 2937539) B2937539
theorem B2613719 : Blo 1740571 2613719 := bstep (se 1 (by rfl) ⟨1960289, by rfl⟩ : syracuseStep 2613719 = 3920579) B3920579
theorem B3916313 : Blo 1740571 3916313 := bstep (se 2 (by rfl) ⟨1468617, by rfl⟩ : syracuseStep 3916313 = 2937235) B2937235
theorem B2613785 : Blo 1740571 2613785 := bstep (se 2 (by rfl) ⟨980169, by rfl⟩ : syracuseStep 2613785 = 1960339) B1960339
theorem B9413185 : Blo 1740571 9413185 := bstep (se 2 (by rfl) ⟨3529944, by rfl⟩ : syracuseStep 9413185 = 7059889) B7059889
theorem B3916403 : Blo 1740571 3916403 := bstep (se 1 (by rfl) ⟨2937302, by rfl⟩ : syracuseStep 3916403 = 5874605) B5874605
theorem B7438979 : Blo 1740571 7438979 := bstep (se 1 (by rfl) ⟨5579234, by rfl⟩ : syracuseStep 7438979 = 11158469) B11158469
theorem B1958539 : Blo 1740571 1958539 := bstep (se 1 (by rfl) ⟨1468904, by rfl⟩ : syracuseStep 1958539 = 2937809) B2937809
theorem B3916439 : Blo 1740571 3916439 := bstep (se 1 (by rfl) ⟨2937329, by rfl⟩ : syracuseStep 3916439 = 5874659) B5874659
theorem B4407959 : Blo 1740571 4407959 := bstep (se 1 (by rfl) ⟨3305969, by rfl⟩ : syracuseStep 4407959 = 6611939) B6611939
theorem B1958647 : Blo 1740571 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B5579543 : Blo 1740571 5579543 := bstep (se 1 (by rfl) ⟨4184657, by rfl⟩ : syracuseStep 5579543 = 8369315) B8369315
theorem B9921325 : Blo 1740571 9921325 := bstep (se 3 (by rfl) ⟨1860248, by rfl⟩ : syracuseStep 9921325 = 3720497) B3720497
theorem B5874497 : Blo 1740571 5874497 := bstep (se 2 (by rfl) ⟨2202936, by rfl⟩ : syracuseStep 5874497 = 4405873) B4405873
theorem B3916619 : Blo 1740571 3916619 := bstep (se 1 (by rfl) ⟨2937464, by rfl⟩ : syracuseStep 3916619 = 5874929) B5874929
theorem B2204491 : Blo 1740571 2204491 := bstep (se 1 (by rfl) ⟨1653368, by rfl⟩ : syracuseStep 2204491 = 3306737) B3306737
theorem B3916673 : Blo 1740571 3916673 := bstep (se 2 (by rfl) ⟨1468752, by rfl⟩ : syracuseStep 3916673 = 2937505) B2937505
theorem B1958827 : Blo 1740571 1958827 := bstep (se 1 (by rfl) ⟨1469120, by rfl⟩ : syracuseStep 1958827 = 2938241) B2938241
theorem B1958935 : Blo 1740571 1958935 := bstep (se 1 (by rfl) ⟨1469201, by rfl⟩ : syracuseStep 1958935 = 2938403) B2938403
theorem B2204759 : Blo 1740571 2204759 := bstep (se 1 (by rfl) ⟨1653569, by rfl⟩ : syracuseStep 2204759 = 3307139) B3307139
theorem B3916889 : Blo 1740571 3916889 := bstep (se 2 (by rfl) ⟨1468833, by rfl⟩ : syracuseStep 3916889 = 2937667) B2937667
theorem B14869655 : Blo 1740571 14869655 := bstep (se 1 (by rfl) ⟨11152241, by rfl⟩ : syracuseStep 14869655 = 22304483) B22304483
theorem B3916979 : Blo 1740571 3916979 := bstep (se 1 (by rfl) ⟨2937734, by rfl⟩ : syracuseStep 3916979 = 5875469) B5875469
theorem B1959115 : Blo 1740571 1959115 := bstep (se 1 (by rfl) ⟨1469336, by rfl⟩ : syracuseStep 1959115 = 2938673) B2938673
theorem B3917015 : Blo 1740571 3917015 := bstep (se 1 (by rfl) ⟨2937761, by rfl⟩ : syracuseStep 3917015 = 5875523) B5875523
theorem B4957463 : Blo 1740571 4957463 := bstep (se 1 (by rfl) ⟨3718097, by rfl⟩ : syracuseStep 4957463 = 7436195) B7436195
theorem B4408627 : Blo 1740571 4408627 := bstep (se 1 (by rfl) ⟨3306470, by rfl⟩ : syracuseStep 4408627 = 6612941) B6612941
theorem B1959223 : Blo 1740571 1959223 := bstep (se 1 (by rfl) ⟨1469417, by rfl⟩ : syracuseStep 1959223 = 2938835) B2938835
theorem B5875037 : Blo 1740571 5875037 := bstep (se 3 (by rfl) ⟨1101569, by rfl⟩ : syracuseStep 5875037 = 2203139) B2203139
theorem B3917195 : Blo 1740571 3917195 := bstep (se 1 (by rfl) ⟨2937896, by rfl⟩ : syracuseStep 3917195 = 5875793) B5875793
theorem B12551603 : Blo 1740571 12551603 := bstep (se 1 (by rfl) ⟨9413702, by rfl⟩ : syracuseStep 12551603 = 18827405) B18827405
theorem B3917249 : Blo 1740571 3917249 := bstep (se 2 (by rfl) ⟨1468968, by rfl⟩ : syracuseStep 3917249 = 2937937) B2937937
theorem B4408769 : Blo 1740571 4408769 := bstep (se 2 (by rfl) ⟨1653288, by rfl⟩ : syracuseStep 4408769 = 3306577) B3306577
theorem B1959403 : Blo 1740571 1959403 := bstep (se 1 (by rfl) ⟨1469552, by rfl⟩ : syracuseStep 1959403 = 2939105) B2939105
theorem B3532313 : Blo 1740571 3532313 := bstep (se 2 (by rfl) ⟨1324617, by rfl⟩ : syracuseStep 3532313 = 2649235) B2649235
theorem B12559907 : Blo 1740571 12559907 := bstep (se 1 (by rfl) ⟨9419930, by rfl⟩ : syracuseStep 12559907 = 18839861) B18839861
theorem B15894091 : Blo 1740571 15894091 := bstep (se 1 (by rfl) ⟨11920568, by rfl⟩ : syracuseStep 15894091 = 23841137) B23841137
theorem B1959511 : Blo 1740571 1959511 := bstep (se 1 (by rfl) ⟨1469633, by rfl⟩ : syracuseStep 1959511 = 2939267) B2939267
theorem B3532427 : Blo 1740571 3532427 := bstep (se 1 (by rfl) ⟨2649320, by rfl⟩ : syracuseStep 3532427 = 5298641) B5298641
theorem B3917465 : Blo 1740571 3917465 := bstep (se 2 (by rfl) ⟨1469049, by rfl⟩ : syracuseStep 3917465 = 2938099) B2938099
theorem B9914035 : Blo 1740571 9914035 := bstep (se 1 (by rfl) ⟨7435526, by rfl⟩ : syracuseStep 9914035 = 14871053) B14871053
theorem B3720907 : Blo 1740571 3720907 := bstep (se 1 (by rfl) ⟨2790680, by rfl⟩ : syracuseStep 3720907 = 5581361) B5581361
theorem B3917555 : Blo 1740571 3917555 := bstep (se 1 (by rfl) ⟨2938166, by rfl⟩ : syracuseStep 3917555 = 5876333) B5876333
theorem B1959691 : Blo 1740571 1959691 := bstep (se 1 (by rfl) ⟨1469768, by rfl⟩ : syracuseStep 1959691 = 2939537) B2939537
theorem B3917591 : Blo 1740571 3917591 := bstep (se 1 (by rfl) ⟨2938193, by rfl⟩ : syracuseStep 3917591 = 5876387) B5876387
theorem B1959799 : Blo 1740571 1959799 := bstep (se 1 (by rfl) ⟨1469849, by rfl⟩ : syracuseStep 1959799 = 2939699) B2939699
theorem B3917771 : Blo 1740571 3917771 := bstep (se 1 (by rfl) ⟨2938328, by rfl⟩ : syracuseStep 3917771 = 5876657) B5876657
theorem B3917825 : Blo 1740571 3917825 := bstep (se 2 (by rfl) ⟨1469184, by rfl⟩ : syracuseStep 3917825 = 2938369) B2938369
theorem B3721241 : Blo 1740571 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B1959979 : Blo 1740571 1959979 := bstep (se 1 (by rfl) ⟨1469984, by rfl⟩ : syracuseStep 1959979 = 2939969) B2939969
theorem B5580875 : Blo 1740571 5580875 := bstep (se 1 (by rfl) ⟨4185656, by rfl⟩ : syracuseStep 5580875 = 8371313) B8371313
theorem B6613123 : Blo 1740571 6613123 := bstep (se 1 (by rfl) ⟨4959842, by rfl⟩ : syracuseStep 6613123 = 9919685) B9919685
theorem B1960087 : Blo 1740571 1960087 := bstep (se 1 (by rfl) ⟨1470065, by rfl⟩ : syracuseStep 1960087 = 2940131) B2940131
theorem B3918041 : Blo 1740571 3918041 := bstep (se 2 (by rfl) ⟨1469265, by rfl⟩ : syracuseStep 3918041 = 2938531) B2938531
theorem B3918131 : Blo 1740571 3918131 := bstep (se 1 (by rfl) ⟨2938598, by rfl⟩ : syracuseStep 3918131 = 5877197) B5877197
theorem B14879051 : Blo 1740571 14879051 := bstep (se 1 (by rfl) ⟨11159288, by rfl⟩ : syracuseStep 14879051 = 22318577) B22318577
theorem B1960267 : Blo 1740571 1960267 := bstep (se 1 (by rfl) ⟨1470200, by rfl⟩ : syracuseStep 1960267 = 2940401) B2940401
theorem B3918167 : Blo 1740571 3918167 := bstep (se 1 (by rfl) ⟨2938625, by rfl⟩ : syracuseStep 3918167 = 5877251) B5877251
theorem B8366429 : Blo 1740571 8366429 := bstep (se 3 (by rfl) ⟨1568705, by rfl⟩ : syracuseStep 8366429 = 3137411) B3137411
theorem B29747573 : Blo 1740571 29747573 := bstep (se 5 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 29747573 = 2788835) B2788835
theorem B6613427 : Blo 1740571 6613427 := bstep (se 1 (by rfl) ⟨4960070, by rfl⟩ : syracuseStep 6613427 = 9920141) B9920141
theorem B1960375 : Blo 1740571 1960375 := bstep (se 1 (by rfl) ⟨1470281, by rfl⟩ : syracuseStep 1960375 = 2940563) B2940563
theorem B5876171 : Blo 1740571 5876171 := bstep (se 1 (by rfl) ⟨4407128, by rfl⟩ : syracuseStep 5876171 = 8814257) B8814257
theorem B3918347 : Blo 1740571 3918347 := bstep (se 1 (by rfl) ⟨2938760, by rfl⟩ : syracuseStep 3918347 = 5877521) B5877521
theorem B4467251 : Blo 1740571 4467251 := bstep (se 1 (by rfl) ⟨3350438, by rfl⟩ : syracuseStep 4467251 = 6700877) B6700877
theorem B3918401 : Blo 1740571 3918401 := bstep (se 2 (by rfl) ⟨1469400, by rfl⟩ : syracuseStep 3918401 = 2938801) B2938801
theorem B22309451 : Blo 1740571 22309451 := bstep (se 1 (by rfl) ⟨16732088, by rfl⟩ : syracuseStep 22309451 = 33464177) B33464177
theorem B4958795 : Blo 1740571 4958795 := bstep (se 1 (by rfl) ⟨3719096, by rfl⟩ : syracuseStep 4958795 = 7438193) B7438193
theorem B25102979 : Blo 1740571 25102979 := bstep (se 1 (by rfl) ⟨18827234, by rfl⟩ : syracuseStep 25102979 = 37654469) B37654469
theorem B6277763 : Blo 1740571 6277763 := bstep (se 1 (by rfl) ⟨4708322, by rfl⟩ : syracuseStep 6277763 = 9416645) B9416645
theorem B14125745 : Blo 1740571 14125745 := bstep (se 2 (by rfl) ⟨5297154, by rfl⟩ : syracuseStep 14125745 = 10594309) B10594309
theorem B4410035 : Blo 1740571 4410035 := bstep (se 1 (by rfl) ⟨3307526, by rfl⟩ : syracuseStep 4410035 = 6615053) B6615053
theorem B5876441 : Blo 1740571 5876441 := bstep (se 2 (by rfl) ⟨2203665, by rfl⟩ : syracuseStep 5876441 = 4407331) B4407331
theorem B3918617 : Blo 1740571 3918617 := bstep (se 2 (by rfl) ⟨1469481, by rfl⟩ : syracuseStep 3918617 = 2938963) B2938963
theorem B2353945 : Blo 1740571 2353945 := bstep (se 2 (by rfl) ⟨882729, by rfl⟩ : syracuseStep 2353945 = 1765459) B1765459
theorem B5581619 : Blo 1740571 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B6277981 : Blo 1740571 6277981 := bstep (se 3 (by rfl) ⟨1177121, by rfl⟩ : syracuseStep 6277981 = 2354243) B2354243
theorem B3918707 : Blo 1740571 3918707 := bstep (se 1 (by rfl) ⟨2939030, by rfl⟩ : syracuseStep 3918707 = 5878061) B5878061
theorem B3918743 : Blo 1740571 3918743 := bstep (se 1 (by rfl) ⟨2939057, by rfl⟩ : syracuseStep 3918743 = 5878115) B5878115
theorem B6614081 : Blo 1740571 6614081 := bstep (se 2 (by rfl) ⟨2480280, by rfl⟩ : syracuseStep 6614081 = 4960561) B4960561
theorem B3918923 : Blo 1740571 3918923 := bstep (se 1 (by rfl) ⟨2939192, by rfl⟩ : syracuseStep 3918923 = 5878385) B5878385
theorem B9915493 : Blo 1740571 9915493 := bstep (se 4 (by rfl) ⟨929577, by rfl⟩ : syracuseStep 9915493 = 1859155) B1859155
theorem B3918977 : Blo 1740571 3918977 := bstep (se 2 (by rfl) ⟨1469616, by rfl⟩ : syracuseStep 3918977 = 2939233) B2939233
theorem B63573173 : Blo 1740571 63573173 := bstep (se 5 (by rfl) ⟨2979992, by rfl⟩ : syracuseStep 63573173 = 5959985) B5959985
theorem B4410571 : Blo 1740571 4410571 := bstep (se 1 (by rfl) ⟨3307928, by rfl⟩ : syracuseStep 4410571 = 6615857) B6615857
theorem B3304793 : Blo 1740571 3304793 := bstep (se 2 (by rfl) ⟨1239297, by rfl⟩ : syracuseStep 3304793 = 2478595) B2478595
theorem B3919193 : Blo 1740571 3919193 := bstep (se 2 (by rfl) ⟨1469697, by rfl⟩ : syracuseStep 3919193 = 2939395) B2939395
theorem B4410713 : Blo 1740571 4410713 := bstep (se 2 (by rfl) ⟨1654017, by rfl⟩ : syracuseStep 4410713 = 3308035) B3308035
theorem B18836837 : Blo 1740571 18836837 := bstep (se 4 (by rfl) ⟨1765953, by rfl⟩ : syracuseStep 18836837 = 3531907) B3531907
theorem B2788759 : Blo 1740571 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B5877143 : Blo 1740571 5877143 := bstep (se 1 (by rfl) ⟨4407857, by rfl⟩ : syracuseStep 5877143 = 8815715) B8815715
theorem B3919283 : Blo 1740571 3919283 := bstep (se 1 (by rfl) ⟨2939462, by rfl⟩ : syracuseStep 3919283 = 5878925) B5878925
theorem B1985995 : Blo 1740571 1985995 := bstep (se 1 (by rfl) ⟨1489496, by rfl⟩ : syracuseStep 1985995 = 2978993) B2978993
theorem B3919319 : Blo 1740571 3919319 := bstep (se 1 (by rfl) ⟨2939489, by rfl⟩ : syracuseStep 3919319 = 5878979) B5878979
theorem B13225517 : Blo 1740571 13225517 := bstep (se 3 (by rfl) ⟨2479784, by rfl⟩ : syracuseStep 13225517 = 4959569) B4959569
theorem B8818307 : Blo 1740571 8818307 := bstep (se 1 (by rfl) ⟨6613730, by rfl⟩ : syracuseStep 8818307 = 13227461) B13227461
theorem B3919499 : Blo 1740571 3919499 := bstep (se 1 (by rfl) ⟨2939624, by rfl⟩ : syracuseStep 3919499 = 5879249) B5879249
theorem B5582515 : Blo 1740571 5582515 := bstep (se 1 (by rfl) ⟨4186886, by rfl⟩ : syracuseStep 5582515 = 8373773) B8373773
theorem B3919553 : Blo 1740571 3919553 := bstep (se 2 (by rfl) ⟨1469832, by rfl⟩ : syracuseStep 3919553 = 2939665) B2939665
theorem B1765099 : Blo 1740571 1765099 := bstep (se 1 (by rfl) ⟨1323824, by rfl⟩ : syracuseStep 1765099 = 2647649) B2647649
theorem B1740587 : Blo 1740571 1740587 := bstep (se 1 (by rfl) ⟨1305440, by rfl⟩ : syracuseStep 1740587 = 2610881) B2610881
theorem B1740599 : Blo 1740571 1740599 := bstep (se 1 (by rfl) ⟨1305449, by rfl⟩ : syracuseStep 1740599 = 2610899) B2610899
theorem B1740619 : Blo 1740571 1740619 := bstep (se 1 (by rfl) ⟨1305464, by rfl⟩ : syracuseStep 1740619 = 2610929) B2610929
theorem B1740631 : Blo 1740571 1740631 := bstep (se 1 (by rfl) ⟨1305473, by rfl⟩ : syracuseStep 1740631 = 2610947) B2610947
theorem B15888221 : Blo 1740571 15888221 := bstep (se 3 (by rfl) ⟨2979041, by rfl⟩ : syracuseStep 15888221 = 5958083) B5958083
theorem B1740651 : Blo 1740571 1740651 := bstep (se 1 (by rfl) ⟨1305488, by rfl⟩ : syracuseStep 1740651 = 2610977) B2610977
theorem B1740663 : Blo 1740571 1740663 := bstep (se 1 (by rfl) ⟨1305497, by rfl⟩ : syracuseStep 1740663 = 2610995) B2610995
theorem B1740683 : Blo 1740571 1740683 := bstep (se 1 (by rfl) ⟨1305512, by rfl⟩ : syracuseStep 1740683 = 2611025) B2611025
theorem B1740695 : Blo 1740571 1740695 := bstep (se 1 (by rfl) ⟨1305521, by rfl⟩ : syracuseStep 1740695 = 2611043) B2611043
theorem B3919769 : Blo 1740571 3919769 := bstep (se 2 (by rfl) ⟨1469913, by rfl⟩ : syracuseStep 3919769 = 2939827) B2939827
theorem B1740715 : Blo 1740571 1740715 := bstep (se 1 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 1740715 = 2611073) B2611073
theorem B5877683 : Blo 1740571 5877683 := bstep (se 1 (by rfl) ⟨4408262, by rfl⟩ : syracuseStep 5877683 = 8816525) B8816525
theorem B1740727 : Blo 1740571 1740727 := bstep (se 1 (by rfl) ⟨1305545, by rfl⟩ : syracuseStep 1740727 = 2611091) B2611091
theorem B1740747 : Blo 1740571 1740747 := bstep (se 1 (by rfl) ⟨1305560, by rfl⟩ : syracuseStep 1740747 = 2611121) B2611121
theorem B13217741 : Blo 1740571 13217741 := bstep (se 3 (by rfl) ⟨2478326, by rfl⟩ : syracuseStep 13217741 = 4956653) B4956653
theorem B1740759 : Blo 1740571 1740759 := bstep (se 1 (by rfl) ⟨1305569, by rfl⟩ : syracuseStep 1740759 = 2611139) B2611139
theorem B1740779 : Blo 1740571 1740779 := bstep (se 1 (by rfl) ⟨1305584, by rfl⟩ : syracuseStep 1740779 = 2611169) B2611169
theorem B3919859 : Blo 1740571 3919859 := bstep (se 1 (by rfl) ⟨2939894, by rfl⟩ : syracuseStep 3919859 = 5879789) B5879789
theorem B1740791 : Blo 1740571 1740791 := bstep (se 1 (by rfl) ⟨1305593, by rfl⟩ : syracuseStep 1740791 = 2611187) B2611187
theorem B1740811 : Blo 1740571 1740811 := bstep (se 1 (by rfl) ⟨1305608, by rfl⟩ : syracuseStep 1740811 = 2611217) B2611217
theorem B1740823 : Blo 1740571 1740823 := bstep (se 1 (by rfl) ⟨1305617, by rfl⟩ : syracuseStep 1740823 = 2611235) B2611235
theorem B3919895 : Blo 1740571 3919895 := bstep (se 1 (by rfl) ⟨2939921, by rfl⟩ : syracuseStep 3919895 = 5879843) B5879843
theorem B1740843 : Blo 1740571 1740843 := bstep (se 1 (by rfl) ⟨1305632, by rfl⟩ : syracuseStep 1740843 = 2611265) B2611265
theorem B1740855 : Blo 1740571 1740855 := bstep (se 1 (by rfl) ⟨1305641, by rfl⟩ : syracuseStep 1740855 = 2611283) B2611283
theorem B1740875 : Blo 1740571 1740875 := bstep (se 1 (by rfl) ⟨1305656, by rfl⟩ : syracuseStep 1740875 = 2611313) B2611313
theorem B1740887 : Blo 1740571 1740887 := bstep (se 1 (by rfl) ⟨1305665, by rfl⟩ : syracuseStep 1740887 = 2611331) B2611331
theorem B1740907 : Blo 1740571 1740907 := bstep (se 1 (by rfl) ⟨1305680, by rfl⟩ : syracuseStep 1740907 = 2611361) B2611361
theorem B1740919 : Blo 1740571 1740919 := bstep (se 1 (by rfl) ⟨1305689, by rfl⟩ : syracuseStep 1740919 = 2611379) B2611379
theorem B1740939 : Blo 1740571 1740939 := bstep (se 1 (by rfl) ⟨1305704, by rfl⟩ : syracuseStep 1740939 = 2611409) B2611409
theorem B2789515 : Blo 1740571 2789515 := bstep (se 1 (by rfl) ⟨2092136, by rfl⟩ : syracuseStep 2789515 = 4184273) B4184273
theorem B1740951 : Blo 1740571 1740951 := bstep (se 1 (by rfl) ⟨1305713, by rfl⟩ : syracuseStep 1740951 = 2611427) B2611427
theorem B1740971 : Blo 1740571 1740971 := bstep (se 1 (by rfl) ⟨1305728, by rfl⟩ : syracuseStep 1740971 = 2611457) B2611457
theorem B4960435 : Blo 1740571 4960435 := bstep (se 1 (by rfl) ⟨3720326, by rfl⟩ : syracuseStep 4960435 = 7440653) B7440653
theorem B1740983 : Blo 1740571 1740983 := bstep (se 1 (by rfl) ⟨1305737, by rfl⟩ : syracuseStep 1740983 = 2611475) B2611475
theorem B5877953 : Blo 1740571 5877953 := bstep (se 2 (by rfl) ⟨2204232, by rfl⟩ : syracuseStep 5877953 = 4408465) B4408465
theorem B1741003 : Blo 1740571 1741003 := bstep (se 1 (by rfl) ⟨1305752, by rfl⟩ : syracuseStep 1741003 = 2611505) B2611505
theorem B2789579 : Blo 1740571 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B3920075 : Blo 1740571 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B1741015 : Blo 1740571 1741015 := bstep (se 1 (by rfl) ⟨1305761, by rfl⟩ : syracuseStep 1741015 = 2611523) B2611523
theorem B1741035 : Blo 1740571 1741035 := bstep (se 1 (by rfl) ⟨1305776, by rfl⟩ : syracuseStep 1741035 = 2611553) B2611553
theorem B1741047 : Blo 1740571 1741047 := bstep (se 1 (by rfl) ⟨1305785, by rfl⟩ : syracuseStep 1741047 = 2611571) B2611571
theorem B3920129 : Blo 1740571 3920129 := bstep (se 2 (by rfl) ⟨1470048, by rfl⟩ : syracuseStep 3920129 = 2940097) B2940097
theorem B1741067 : Blo 1740571 1741067 := bstep (se 1 (by rfl) ⟨1305800, by rfl⟩ : syracuseStep 1741067 = 2611601) B2611601
theorem B1741079 : Blo 1740571 1741079 := bstep (se 1 (by rfl) ⟨1305809, by rfl⟩ : syracuseStep 1741079 = 2611619) B2611619
theorem B1741099 : Blo 1740571 1741099 := bstep (se 1 (by rfl) ⟨1305824, by rfl⟩ : syracuseStep 1741099 = 2611649) B2611649
theorem B114479405 : Blo 1740571 114479405 := bstep (se 3 (by rfl) ⟨21464888, by rfl⟩ : syracuseStep 114479405 = 42929777) B42929777
theorem B11161901 : Blo 1740571 11161901 := bstep (se 3 (by rfl) ⟨2092856, by rfl⟩ : syracuseStep 11161901 = 4185713) B4185713
theorem B6615341 : Blo 1740571 6615341 := bstep (se 3 (by rfl) ⟨1240376, by rfl⟩ : syracuseStep 6615341 = 2480753) B2480753
theorem B1741111 : Blo 1740571 1741111 := bstep (se 1 (by rfl) ⟨1305833, by rfl⟩ : syracuseStep 1741111 = 2611667) B2611667
theorem B1741131 : Blo 1740571 1741131 := bstep (se 1 (by rfl) ⟨1305848, by rfl⟩ : syracuseStep 1741131 = 2611697) B2611697
theorem B2789707 : Blo 1740571 2789707 := bstep (se 1 (by rfl) ⟨2092280, by rfl⟩ : syracuseStep 2789707 = 4184561) B4184561
theorem B9417035 : Blo 1740571 9417035 := bstep (se 1 (by rfl) ⟨7062776, by rfl⟩ : syracuseStep 9417035 = 14125553) B14125553
theorem B6615371 : Blo 1740571 6615371 := bstep (se 1 (by rfl) ⟨4961528, by rfl⟩ : syracuseStep 6615371 = 9923057) B9923057
theorem B1741143 : Blo 1740571 1741143 := bstep (se 1 (by rfl) ⟨1305857, by rfl⟩ : syracuseStep 1741143 = 2611715) B2611715
theorem B1741163 : Blo 1740571 1741163 := bstep (se 1 (by rfl) ⟨1305872, by rfl⟩ : syracuseStep 1741163 = 2611745) B2611745
theorem B1741175 : Blo 1740571 1741175 := bstep (se 1 (by rfl) ⟨1305881, by rfl⟩ : syracuseStep 1741175 = 2611763) B2611763
theorem B2478475 : Blo 1740571 2478475 := bstep (se 1 (by rfl) ⟨1858856, by rfl⟩ : syracuseStep 2478475 = 3717713) B3717713
theorem B1741195 : Blo 1740571 1741195 := bstep (se 1 (by rfl) ⟨1305896, by rfl⟩ : syracuseStep 1741195 = 2611793) B2611793
theorem B1741207 : Blo 1740571 1741207 := bstep (se 1 (by rfl) ⟨1305905, by rfl⟩ : syracuseStep 1741207 = 2611811) B2611811
theorem B1741227 : Blo 1740571 1741227 := bstep (se 1 (by rfl) ⟨1305920, by rfl⟩ : syracuseStep 1741227 = 2611841) B2611841
theorem B13218227 : Blo 1740571 13218227 := bstep (se 1 (by rfl) ⟨9913670, by rfl⟩ : syracuseStep 13218227 = 19827341) B19827341
theorem B1741239 : Blo 1740571 1741239 := bstep (se 1 (by rfl) ⟨1305929, by rfl⟩ : syracuseStep 1741239 = 2611859) B2611859
theorem B1741259 : Blo 1740571 1741259 := bstep (se 1 (by rfl) ⟨1305944, by rfl⟩ : syracuseStep 1741259 = 2611889) B2611889
theorem B1741271 : Blo 1740571 1741271 := bstep (se 1 (by rfl) ⟨1305953, by rfl⟩ : syracuseStep 1741271 = 2611907) B2611907
theorem B3920345 : Blo 1740571 3920345 := bstep (se 2 (by rfl) ⟨1470129, by rfl⟩ : syracuseStep 3920345 = 2940259) B2940259
theorem B1741291 : Blo 1740571 1741291 := bstep (se 1 (by rfl) ⟨1305968, by rfl⟩ : syracuseStep 1741291 = 2611937) B2611937
theorem B1741303 : Blo 1740571 1741303 := bstep (se 1 (by rfl) ⟨1305977, by rfl⟩ : syracuseStep 1741303 = 2611955) B2611955
theorem B1741323 : Blo 1740571 1741323 := bstep (se 1 (by rfl) ⟨1305992, by rfl⟩ : syracuseStep 1741323 = 2611985) B2611985
theorem B75280913 : Blo 1740571 75280913 := bstep (se 2 (by rfl) ⟨28230342, by rfl⟩ : syracuseStep 75280913 = 56460685) B56460685
theorem B1741335 : Blo 1740571 1741335 := bstep (se 1 (by rfl) ⟨1306001, by rfl⟩ : syracuseStep 1741335 = 2612003) B2612003
theorem B1741355 : Blo 1740571 1741355 := bstep (se 1 (by rfl) ⟨1306016, by rfl⟩ : syracuseStep 1741355 = 2612033) B2612033
theorem B3920435 : Blo 1740571 3920435 := bstep (se 1 (by rfl) ⟨2940326, by rfl⟩ : syracuseStep 3920435 = 5880653) B5880653
theorem B1741367 : Blo 1740571 1741367 := bstep (se 1 (by rfl) ⟨1306025, by rfl⟩ : syracuseStep 1741367 = 2612051) B2612051
theorem B6795841 : Blo 1740571 6795841 := bstep (se 2 (by rfl) ⟨2548440, by rfl⟩ : syracuseStep 6795841 = 5096881) B5096881
theorem B1741387 : Blo 1740571 1741387 := bstep (se 1 (by rfl) ⟨1306040, by rfl⟩ : syracuseStep 1741387 = 2612081) B2612081
theorem B2937431 : Blo 1740571 2937431 := bstep (se 1 (by rfl) ⟨2203073, by rfl⟩ : syracuseStep 2937431 = 4406147) B4406147
theorem B1741399 : Blo 1740571 1741399 := bstep (se 1 (by rfl) ⟨1306049, by rfl⟩ : syracuseStep 1741399 = 2612099) B2612099
theorem B3920471 : Blo 1740571 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B1741419 : Blo 1740571 1741419 := bstep (se 1 (by rfl) ⟨1306064, by rfl⟩ : syracuseStep 1741419 = 2612129) B2612129
theorem B1741431 : Blo 1740571 1741431 := bstep (se 1 (by rfl) ⟨1306073, by rfl⟩ : syracuseStep 1741431 = 2612147) B2612147
theorem B1741451 : Blo 1740571 1741451 := bstep (se 1 (by rfl) ⟨1306088, by rfl⟩ : syracuseStep 1741451 = 2612177) B2612177
theorem B1741463 : Blo 1740571 1741463 := bstep (se 1 (by rfl) ⟨1306097, by rfl⟩ : syracuseStep 1741463 = 2612195) B2612195
theorem B1741483 : Blo 1740571 1741483 := bstep (se 1 (by rfl) ⟨1306112, by rfl⟩ : syracuseStep 1741483 = 2612225) B2612225
theorem B12546737 : Blo 1740571 12546737 := bstep (se 2 (by rfl) ⟨4705026, by rfl⟩ : syracuseStep 12546737 = 9410053) B9410053
theorem B1741495 : Blo 1740571 1741495 := bstep (se 1 (by rfl) ⟨1306121, by rfl⟩ : syracuseStep 1741495 = 2612243) B2612243
theorem B1741515 : Blo 1740571 1741515 := bstep (se 1 (by rfl) ⟨1306136, by rfl⟩ : syracuseStep 1741515 = 2612273) B2612273
theorem B2937559 : Blo 1740571 2937559 := bstep (se 1 (by rfl) ⟨2203169, by rfl⟩ : syracuseStep 2937559 = 4406339) B4406339
theorem B1741527 : Blo 1740571 1741527 := bstep (se 1 (by rfl) ⟨1306145, by rfl⟩ : syracuseStep 1741527 = 2612291) B2612291
theorem B5878493 : Blo 1740571 5878493 := bstep (se 3 (by rfl) ⟨1102217, by rfl⟩ : syracuseStep 5878493 = 2204435) B2204435
theorem B1741547 : Blo 1740571 1741547 := bstep (se 1 (by rfl) ⟨1306160, by rfl⟩ : syracuseStep 1741547 = 2612321) B2612321
theorem B1741559 : Blo 1740571 1741559 := bstep (se 1 (by rfl) ⟨1306169, by rfl⟩ : syracuseStep 1741559 = 2612339) B2612339
theorem B3306251 : Blo 1740571 3306251 := bstep (se 1 (by rfl) ⟨2479688, by rfl⟩ : syracuseStep 3306251 = 4959377) B4959377
theorem B1741579 : Blo 1740571 1741579 := bstep (se 1 (by rfl) ⟨1306184, by rfl⟩ : syracuseStep 1741579 = 2612369) B2612369
theorem B3920651 : Blo 1740571 3920651 := bstep (se 1 (by rfl) ⟨2940488, by rfl⟩ : syracuseStep 3920651 = 5880977) B5880977
theorem B1741591 : Blo 1740571 1741591 := bstep (se 1 (by rfl) ⟨1306193, by rfl⟩ : syracuseStep 1741591 = 2612387) B2612387
theorem B1741611 : Blo 1740571 1741611 := bstep (se 1 (by rfl) ⟨1306208, by rfl⟩ : syracuseStep 1741611 = 2612417) B2612417
theorem B7443251 : Blo 1740571 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B1741623 : Blo 1740571 1741623 := bstep (se 1 (by rfl) ⟨1306217, by rfl⟩ : syracuseStep 1741623 = 2612435) B2612435
theorem B32207681 : Blo 1740571 32207681 := bstep (se 2 (by rfl) ⟨12077880, by rfl⟩ : syracuseStep 32207681 = 24155761) B24155761
theorem B3920705 : Blo 1740571 3920705 := bstep (se 2 (by rfl) ⟨1470264, by rfl⟩ : syracuseStep 3920705 = 2940529) B2940529
theorem B1741643 : Blo 1740571 1741643 := bstep (se 1 (by rfl) ⟨1306232, by rfl⟩ : syracuseStep 1741643 = 2612465) B2612465
theorem B1741655 : Blo 1740571 1741655 := bstep (se 1 (by rfl) ⟨1306241, by rfl⟩ : syracuseStep 1741655 = 2612483) B2612483
theorem B1741675 : Blo 1740571 1741675 := bstep (se 1 (by rfl) ⟨1306256, by rfl⟩ : syracuseStep 1741675 = 2612513) B2612513
theorem B1741687 : Blo 1740571 1741687 := bstep (se 1 (by rfl) ⟨1306265, by rfl⟩ : syracuseStep 1741687 = 2612531) B2612531
theorem B1741707 : Blo 1740571 1741707 := bstep (se 1 (by rfl) ⟨1306280, by rfl⟩ : syracuseStep 1741707 = 2612561) B2612561
theorem B1741719 : Blo 1740571 1741719 := bstep (se 1 (by rfl) ⟨1306289, by rfl⟩ : syracuseStep 1741719 = 2612579) B2612579
theorem B1741739 : Blo 1740571 1741739 := bstep (se 1 (by rfl) ⟨1306304, by rfl⟩ : syracuseStep 1741739 = 2612609) B2612609
theorem B14881715 : Blo 1740571 14881715 := bstep (se 1 (by rfl) ⟨11161286, by rfl⟩ : syracuseStep 14881715 = 22322573) B22322573
theorem B1741751 : Blo 1740571 1741751 := bstep (se 1 (by rfl) ⟨1306313, by rfl⟩ : syracuseStep 1741751 = 2612627) B2612627
theorem B3306433 : Blo 1740571 3306433 := bstep (se 2 (by rfl) ⟨1239912, by rfl⟩ : syracuseStep 3306433 = 2479825) B2479825
theorem B5026763 : Blo 1740571 5026763 := bstep (se 1 (by rfl) ⟨3770072, by rfl⟩ : syracuseStep 5026763 = 7540145) B7540145
theorem B1741771 : Blo 1740571 1741771 := bstep (se 1 (by rfl) ⟨1306328, by rfl⟩ : syracuseStep 1741771 = 2612657) B2612657
theorem B1741783 : Blo 1740571 1741783 := bstep (se 1 (by rfl) ⟨1306337, by rfl⟩ : syracuseStep 1741783 = 2612675) B2612675
theorem B6616025 : Blo 1740571 6616025 := bstep (se 2 (by rfl) ⟨2481009, by rfl⟩ : syracuseStep 6616025 = 4962019) B4962019
theorem B1741803 : Blo 1740571 1741803 := bstep (se 1 (by rfl) ⟨1306352, by rfl⟩ : syracuseStep 1741803 = 2612705) B2612705
theorem B1741815 : Blo 1740571 1741815 := bstep (se 1 (by rfl) ⟨1306361, by rfl⟩ : syracuseStep 1741815 = 2612723) B2612723
theorem B1741835 : Blo 1740571 1741835 := bstep (se 1 (by rfl) ⟨1306376, by rfl⟩ : syracuseStep 1741835 = 2612753) B2612753
theorem B1741847 : Blo 1740571 1741847 := bstep (se 1 (by rfl) ⟨1306385, by rfl⟩ : syracuseStep 1741847 = 2612771) B2612771
theorem B2790425 : Blo 1740571 2790425 := bstep (se 2 (by rfl) ⟨1046409, by rfl⟩ : syracuseStep 2790425 = 2092819) B2092819
theorem B1741867 : Blo 1740571 1741867 := bstep (se 1 (by rfl) ⟨1306400, by rfl⟩ : syracuseStep 1741867 = 2612801) B2612801
theorem B1741879 : Blo 1740571 1741879 := bstep (se 1 (by rfl) ⟨1306409, by rfl⟩ : syracuseStep 1741879 = 2612819) B2612819
theorem B7058497 : Blo 1740571 7058497 := bstep (se 2 (by rfl) ⟨2646936, by rfl⟩ : syracuseStep 7058497 = 5293873) B5293873
theorem B10327105 : Blo 1740571 10327105 := bstep (se 2 (by rfl) ⟨3872664, by rfl⟩ : syracuseStep 10327105 = 7745329) B7745329
theorem B10589249 : Blo 1740571 10589249 := bstep (se 2 (by rfl) ⟨3970968, by rfl⟩ : syracuseStep 10589249 = 7941937) B7941937
theorem B1741899 : Blo 1740571 1741899 := bstep (se 1 (by rfl) ⟨1306424, by rfl⟩ : syracuseStep 1741899 = 2612849) B2612849
theorem B1741911 : Blo 1740571 1741911 := bstep (se 1 (by rfl) ⟨1306433, by rfl⟩ : syracuseStep 1741911 = 2612867) B2612867
theorem B1741931 : Blo 1740571 1741931 := bstep (se 1 (by rfl) ⟨1306448, by rfl⟩ : syracuseStep 1741931 = 2612897) B2612897
theorem B1741943 : Blo 1740571 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B1741963 : Blo 1740571 1741963 := bstep (se 1 (by rfl) ⟨1306472, by rfl⟩ : syracuseStep 1741963 = 2612945) B2612945
theorem B12547223 : Blo 1740571 12547223 := bstep (se 1 (by rfl) ⟨9410417, by rfl⟩ : syracuseStep 12547223 = 18820835) B18820835
theorem B1741975 : Blo 1740571 1741975 := bstep (se 1 (by rfl) ⟨1306481, by rfl⟩ : syracuseStep 1741975 = 2612963) B2612963
theorem B2790553 : Blo 1740571 2790553 := bstep (se 2 (by rfl) ⟨1046457, by rfl⟩ : syracuseStep 2790553 = 2092915) B2092915
theorem B19846295 : Blo 1740571 19846295 := bstep (se 1 (by rfl) ⟨14884721, by rfl⟩ : syracuseStep 19846295 = 29769443) B29769443
theorem B1741995 : Blo 1740571 1741995 := bstep (se 1 (by rfl) ⟨1306496, by rfl⟩ : syracuseStep 1741995 = 2612993) B2612993
theorem B1742007 : Blo 1740571 1742007 := bstep (se 1 (by rfl) ⟨1306505, by rfl⟩ : syracuseStep 1742007 = 2613011) B2613011
theorem B1742027 : Blo 1740571 1742027 := bstep (se 1 (by rfl) ⟨1306520, by rfl⟩ : syracuseStep 1742027 = 2613041) B2613041
theorem B4961483 : Blo 1740571 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B13407437 : Blo 1740571 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1742039 : Blo 1740571 1742039 := bstep (se 1 (by rfl) ⟨1306529, by rfl⟩ : syracuseStep 1742039 = 2613059) B2613059
theorem B1742059 : Blo 1740571 1742059 := bstep (se 1 (by rfl) ⟨1306544, by rfl⟩ : syracuseStep 1742059 = 2613089) B2613089
theorem B1742071 : Blo 1740571 1742071 := bstep (se 1 (by rfl) ⟨1306553, by rfl⟩ : syracuseStep 1742071 = 2613107) B2613107
theorem B1742091 : Blo 1740571 1742091 := bstep (se 1 (by rfl) ⟨1306568, by rfl⟩ : syracuseStep 1742091 = 2613137) B2613137
theorem B1742103 : Blo 1740571 1742103 := bstep (se 1 (by rfl) ⟨1306577, by rfl⟩ : syracuseStep 1742103 = 2613155) B2613155
theorem B1742123 : Blo 1740571 1742123 := bstep (se 1 (by rfl) ⟨1306592, by rfl⟩ : syracuseStep 1742123 = 2613185) B2613185
theorem B1742135 : Blo 1740571 1742135 := bstep (se 1 (by rfl) ⟨1306601, by rfl⟩ : syracuseStep 1742135 = 2613203) B2613203
theorem B2938187 : Blo 1740571 2938187 := bstep (se 1 (by rfl) ⟨2203640, by rfl⟩ : syracuseStep 2938187 = 4407281) B4407281
theorem B1742155 : Blo 1740571 1742155 := bstep (se 1 (by rfl) ⟨1306616, by rfl⟩ : syracuseStep 1742155 = 2613233) B2613233
theorem B1742167 : Blo 1740571 1742167 := bstep (se 1 (by rfl) ⟨1306625, by rfl⟩ : syracuseStep 1742167 = 2613251) B2613251
theorem B1742187 : Blo 1740571 1742187 := bstep (se 1 (by rfl) ⟨1306640, by rfl⟩ : syracuseStep 1742187 = 2613281) B2613281
theorem B1742199 : Blo 1740571 1742199 := bstep (se 1 (by rfl) ⟨1306649, by rfl⟩ : syracuseStep 1742199 = 2613299) B2613299
theorem B3306881 : Blo 1740571 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B1742219 : Blo 1740571 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B1742231 : Blo 1740571 1742231 := bstep (se 1 (by rfl) ⟨1306673, by rfl⟩ : syracuseStep 1742231 = 2613347) B2613347
theorem B1742251 : Blo 1740571 1742251 := bstep (se 1 (by rfl) ⟨1306688, by rfl⟩ : syracuseStep 1742251 = 2613377) B2613377
theorem B1742263 : Blo 1740571 1742263 := bstep (se 1 (by rfl) ⟨1306697, by rfl⟩ : syracuseStep 1742263 = 2613395) B2613395
theorem B2938315 : Blo 1740571 2938315 := bstep (se 1 (by rfl) ⟨2203736, by rfl⟩ : syracuseStep 2938315 = 4407473) B4407473
theorem B1742283 : Blo 1740571 1742283 := bstep (se 1 (by rfl) ⟨1306712, by rfl⟩ : syracuseStep 1742283 = 2613425) B2613425
theorem B1742295 : Blo 1740571 1742295 := bstep (se 1 (by rfl) ⟨1306721, by rfl⟩ : syracuseStep 1742295 = 2613443) B2613443
theorem B1742315 : Blo 1740571 1742315 := bstep (se 1 (by rfl) ⟨1306736, by rfl⟩ : syracuseStep 1742315 = 2613473) B2613473
theorem B1742327 : Blo 1740571 1742327 := bstep (se 1 (by rfl) ⟨1306745, by rfl⟩ : syracuseStep 1742327 = 2613491) B2613491
theorem B1742347 : Blo 1740571 1742347 := bstep (se 1 (by rfl) ⟨1306760, by rfl⟩ : syracuseStep 1742347 = 2613521) B2613521
theorem B1742359 : Blo 1740571 1742359 := bstep (se 1 (by rfl) ⟨1306769, by rfl⟩ : syracuseStep 1742359 = 2613539) B2613539
theorem B2790937 : Blo 1740571 2790937 := bstep (se 2 (by rfl) ⟨1046601, by rfl⟩ : syracuseStep 2790937 = 2093203) B2093203
theorem B23828003 : Blo 1740571 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B1742379 : Blo 1740571 1742379 := bstep (se 1 (by rfl) ⟨1306784, by rfl⟩ : syracuseStep 1742379 = 2613569) B2613569
theorem B1742391 : Blo 1740571 1742391 := bstep (se 1 (by rfl) ⟨1306793, by rfl⟩ : syracuseStep 1742391 = 2613587) B2613587
theorem B1742411 : Blo 1740571 1742411 := bstep (se 1 (by rfl) ⟨1306808, by rfl⟩ : syracuseStep 1742411 = 2613617) B2613617
theorem B1742423 : Blo 1740571 1742423 := bstep (se 1 (by rfl) ⟨1306817, by rfl⟩ : syracuseStep 1742423 = 2613635) B2613635
theorem B2938457 : Blo 1740571 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B1742443 : Blo 1740571 1742443 := bstep (se 1 (by rfl) ⟨1306832, by rfl⟩ : syracuseStep 1742443 = 2613665) B2613665
theorem B1742455 : Blo 1740571 1742455 := bstep (se 1 (by rfl) ⟨1306841, by rfl⟩ : syracuseStep 1742455 = 2613683) B2613683
theorem B1742475 : Blo 1740571 1742475 := bstep (se 1 (by rfl) ⟨1306856, by rfl⟩ : syracuseStep 1742475 = 2613713) B2613713
theorem B7435921 : Blo 1740571 7435921 := bstep (se 2 (by rfl) ⟨2788470, by rfl⟩ : syracuseStep 7435921 = 5576941) B5576941
theorem B1742487 : Blo 1740571 1742487 := bstep (se 1 (by rfl) ⟨1306865, by rfl⟩ : syracuseStep 1742487 = 2613731) B2613731
theorem B1742507 : Blo 1740571 1742507 := bstep (se 1 (by rfl) ⟨1306880, by rfl⟩ : syracuseStep 1742507 = 2613761) B2613761
theorem B1742519 : Blo 1740571 1742519 := bstep (se 1 (by rfl) ⟨1306889, by rfl⟩ : syracuseStep 1742519 = 2613779) B2613779
theorem B1742539 : Blo 1740571 1742539 := bstep (se 1 (by rfl) ⟨1306904, by rfl⟩ : syracuseStep 1742539 = 2613809) B2613809
theorem B3307223 : Blo 1740571 3307223 := bstep (se 1 (by rfl) ⟨2480417, by rfl⟩ : syracuseStep 3307223 = 4960835) B4960835
theorem B1742551 : Blo 1740571 1742551 := bstep (se 1 (by rfl) ⟨1306913, by rfl⟩ : syracuseStep 1742551 = 2613827) B2613827
theorem B2610905 : Blo 1740571 2610905 := bstep (se 2 (by rfl) ⟨979089, by rfl⟩ : syracuseStep 2610905 = 1958179) B1958179
theorem B2938585 : Blo 1740571 2938585 := bstep (se 2 (by rfl) ⟨1101969, by rfl⟩ : syracuseStep 2938585 = 2203939) B2203939
theorem B1742571 : Blo 1740571 1742571 := bstep (se 1 (by rfl) ⟨1306928, by rfl⟩ : syracuseStep 1742571 = 2613857) B2613857
theorem B10884881 : Blo 1740571 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B2791193 : Blo 1740571 2791193 := bstep (se 2 (by rfl) ⟨1046697, by rfl⟩ : syracuseStep 2791193 = 2093395) B2093395
theorem B2611019 : Blo 1740571 2611019 := bstep (se 1 (by rfl) ⟨1958264, by rfl⟩ : syracuseStep 2611019 = 3916529) B3916529
theorem B5879627 : Blo 1740571 5879627 := bstep (se 1 (by rfl) ⟨4409720, by rfl⟩ : syracuseStep 5879627 = 8819441) B8819441
theorem B2611031 : Blo 1740571 2611031 := bstep (se 1 (by rfl) ⟨1958273, by rfl⟩ : syracuseStep 2611031 = 3916547) B3916547
theorem B13219685 : Blo 1740571 13219685 := bstep (se 4 (by rfl) ⟨1239345, by rfl⟩ : syracuseStep 13219685 = 2478691) B2478691
theorem B29407093 : Blo 1740571 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B2611097 : Blo 1740571 2611097 := bstep (se 2 (by rfl) ⟨979161, by rfl⟩ : syracuseStep 2611097 = 1958323) B1958323
theorem B14882777 : Blo 1740571 14882777 := bstep (se 2 (by rfl) ⟨5581041, by rfl⟩ : syracuseStep 14882777 = 11162083) B11162083
theorem B2611211 : Blo 1740571 2611211 := bstep (se 1 (by rfl) ⟨1958408, by rfl⟩ : syracuseStep 2611211 = 3916817) B3916817
theorem B2611223 : Blo 1740571 2611223 := bstep (se 1 (by rfl) ⟨1958417, by rfl⟩ : syracuseStep 2611223 = 3916835) B3916835
theorem B2611289 : Blo 1740571 2611289 := bstep (se 2 (by rfl) ⟨979233, by rfl⟩ : syracuseStep 2611289 = 1958467) B1958467
theorem B5879897 : Blo 1740571 5879897 := bstep (se 2 (by rfl) ⟨2204961, by rfl⟩ : syracuseStep 5879897 = 4409923) B4409923
theorem B8812637 : Blo 1740571 8812637 := bstep (se 3 (by rfl) ⟨1652369, by rfl⟩ : syracuseStep 8812637 = 3304739) B3304739
theorem B17881181 : Blo 1740571 17881181 := bstep (se 3 (by rfl) ⟨3352721, by rfl⟩ : syracuseStep 17881181 = 6705443) B6705443
theorem B2611403 : Blo 1740571 2611403 := bstep (se 1 (by rfl) ⟨1958552, by rfl⟩ : syracuseStep 2611403 = 3917105) B3917105
theorem B2611415 : Blo 1740571 2611415 := bstep (se 1 (by rfl) ⟨1958561, by rfl⟩ : syracuseStep 2611415 = 3917123) B3917123
theorem B2939159 : Blo 1740571 2939159 := bstep (se 1 (by rfl) ⟨2204369, by rfl⟩ : syracuseStep 2939159 = 4408739) B4408739
theorem B2611481 : Blo 1740571 2611481 := bstep (se 2 (by rfl) ⟨979305, by rfl⟩ : syracuseStep 2611481 = 1958611) B1958611
theorem B3971353 : Blo 1740571 3971353 := bstep (se 2 (by rfl) ⟨1489257, by rfl⟩ : syracuseStep 3971353 = 2978515) B2978515
theorem B13220171 : Blo 1740571 13220171 := bstep (se 1 (by rfl) ⟨9915128, by rfl⟩ : syracuseStep 13220171 = 19830257) B19830257
theorem B11155805 : Blo 1740571 11155805 := bstep (se 3 (by rfl) ⟨2091713, by rfl⟩ : syracuseStep 11155805 = 4183427) B4183427
theorem B3307891 : Blo 1740571 3307891 := bstep (se 1 (by rfl) ⟨2480918, by rfl⟩ : syracuseStep 3307891 = 4961837) B4961837
theorem B2611595 : Blo 1740571 2611595 := bstep (se 1 (by rfl) ⟨1958696, by rfl⟩ : syracuseStep 2611595 = 3917393) B3917393
theorem B2611607 : Blo 1740571 2611607 := bstep (se 1 (by rfl) ⟨1958705, by rfl⟩ : syracuseStep 2611607 = 3917411) B3917411
theorem B2939287 : Blo 1740571 2939287 := bstep (se 1 (by rfl) ⟨2204465, by rfl⟩ : syracuseStep 2939287 = 4408931) B4408931
theorem B3717593 : Blo 1740571 3717593 := bstep (se 2 (by rfl) ⟨1394097, by rfl⟩ : syracuseStep 3717593 = 2788195) B2788195
theorem B2611673 : Blo 1740571 2611673 := bstep (se 2 (by rfl) ⟨979377, by rfl⟩ : syracuseStep 2611673 = 1958755) B1958755
theorem B2611787 : Blo 1740571 2611787 := bstep (se 1 (by rfl) ⟨1958840, by rfl⟩ : syracuseStep 2611787 = 3917681) B3917681
theorem B2611799 : Blo 1740571 2611799 := bstep (se 1 (by rfl) ⟨1958849, by rfl⟩ : syracuseStep 2611799 = 3917699) B3917699
theorem B6609539 : Blo 1740571 6609539 := bstep (se 1 (by rfl) ⟨4957154, by rfl⟩ : syracuseStep 6609539 = 9914309) B9914309
theorem B2611865 : Blo 1740571 2611865 := bstep (se 2 (by rfl) ⟨979449, by rfl⟩ : syracuseStep 2611865 = 1958899) B1958899
theorem B6699779 : Blo 1740571 6699779 := bstep (se 1 (by rfl) ⟨5024834, by rfl⟩ : syracuseStep 6699779 = 10049669) B10049669
theorem B2611979 : Blo 1740571 2611979 := bstep (se 1 (by rfl) ⟨1958984, by rfl⟩ : syracuseStep 2611979 = 3917969) B3917969
theorem B2611991 : Blo 1740571 2611991 := bstep (se 1 (by rfl) ⟨1958993, by rfl⟩ : syracuseStep 2611991 = 3917987) B3917987
theorem B5880599 : Blo 1740571 5880599 := bstep (se 1 (by rfl) ⟨4410449, by rfl⟩ : syracuseStep 5880599 = 8820899) B8820899
theorem B14875427 : Blo 1740571 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B3873587 : Blo 1740571 3873587 := bstep (se 1 (by rfl) ⟨2905190, by rfl⟩ : syracuseStep 3873587 = 5810381) B5810381
theorem B2612057 : Blo 1740571 2612057 := bstep (se 2 (by rfl) ⟨979521, by rfl⟩ : syracuseStep 2612057 = 1959043) B1959043
theorem B3718003 : Blo 1740571 3718003 := bstep (se 1 (by rfl) ⟨2788502, by rfl⟩ : syracuseStep 3718003 = 5577005) B5577005
theorem B2513803 : Blo 1740571 2513803 := bstep (se 1 (by rfl) ⟨1885352, by rfl⟩ : syracuseStep 2513803 = 3770705) B3770705
theorem B11164567 : Blo 1740571 11164567 := bstep (se 1 (by rfl) ⟨8373425, by rfl⟩ : syracuseStep 11164567 = 16746851) B16746851
theorem B2612171 : Blo 1740571 2612171 := bstep (se 1 (by rfl) ⟨1959128, by rfl⟩ : syracuseStep 2612171 = 3918257) B3918257
theorem B2612183 : Blo 1740571 2612183 := bstep (se 1 (by rfl) ⟨1959137, by rfl⟩ : syracuseStep 2612183 = 3918275) B3918275
theorem B2939915 : Blo 1740571 2939915 := bstep (se 1 (by rfl) ⟨2204936, by rfl⟩ : syracuseStep 2939915 = 4409873) B4409873
theorem B2612249 : Blo 1740571 2612249 := bstep (se 2 (by rfl) ⟨979593, by rfl⟩ : syracuseStep 2612249 = 1959187) B1959187
theorem B6609995 : Blo 1740571 6609995 := bstep (se 1 (by rfl) ⟨4957496, by rfl⟩ : syracuseStep 6609995 = 9914993) B9914993
theorem B2612363 : Blo 1740571 2612363 := bstep (se 1 (by rfl) ⟨1959272, by rfl⟩ : syracuseStep 2612363 = 3918545) B3918545
theorem B2940043 : Blo 1740571 2940043 := bstep (se 1 (by rfl) ⟨2205032, by rfl⟩ : syracuseStep 2940043 = 4410065) B4410065
theorem B1858711 : Blo 1740571 1858711 := bstep (se 1 (by rfl) ⟨1394033, by rfl⟩ : syracuseStep 1858711 = 2788067) B2788067
theorem B2612375 : Blo 1740571 2612375 := bstep (se 1 (by rfl) ⟨1959281, by rfl⟩ : syracuseStep 2612375 = 3918563) B3918563
theorem B25099469 : Blo 1740571 25099469 := bstep (se 3 (by rfl) ⟨4706150, by rfl⟩ : syracuseStep 25099469 = 9412301) B9412301
theorem B2612441 : Blo 1740571 2612441 := bstep (se 2 (by rfl) ⟨979665, by rfl⟩ : syracuseStep 2612441 = 1959331) B1959331
theorem B6610193 : Blo 1740571 6610193 := bstep (se 2 (by rfl) ⟨2478822, by rfl⟩ : syracuseStep 6610193 = 4957645) B4957645
theorem B2940185 : Blo 1740571 2940185 := bstep (se 2 (by rfl) ⟨1102569, by rfl⟩ : syracuseStep 2940185 = 2205139) B2205139
theorem B5881139 : Blo 1740571 5881139 := bstep (se 1 (by rfl) ⟨4410854, by rfl⟩ : syracuseStep 5881139 = 8821709) B8821709
theorem B2612555 : Blo 1740571 2612555 := bstep (se 1 (by rfl) ⟨1959416, by rfl⟩ : syracuseStep 2612555 = 3918833) B3918833
theorem B2202967 : Blo 1740571 2202967 := bstep (se 1 (by rfl) ⟨1652225, by rfl⟩ : syracuseStep 2202967 = 3304451) B3304451
theorem B2612567 : Blo 1740571 2612567 := bstep (se 1 (by rfl) ⟨1959425, by rfl⟩ : syracuseStep 2612567 = 3918851) B3918851
theorem B13229405 : Blo 1740571 13229405 := bstep (se 3 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 13229405 = 4961027) B4961027
theorem B3972503 : Blo 1740571 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B2612633 : Blo 1740571 2612633 := bstep (se 2 (by rfl) ⟨979737, by rfl⟩ : syracuseStep 2612633 = 1959475) B1959475
theorem B2940313 : Blo 1740571 2940313 := bstep (se 2 (by rfl) ⟨1102617, by rfl⟩ : syracuseStep 2940313 = 2205235) B2205235
theorem B2612747 : Blo 1740571 2612747 := bstep (se 1 (by rfl) ⟨1959560, by rfl⟩ : syracuseStep 2612747 = 3919121) B3919121
theorem B2612759 : Blo 1740571 2612759 := bstep (se 1 (by rfl) ⟨1959569, by rfl⟩ : syracuseStep 2612759 = 3919139) B3919139
theorem B7061057 : Blo 1740571 7061057 := bstep (se 2 (by rfl) ⟨2647896, by rfl⟩ : syracuseStep 7061057 = 5295793) B5295793
theorem B2612825 : Blo 1740571 2612825 := bstep (se 2 (by rfl) ⟨979809, by rfl⟩ : syracuseStep 2612825 = 1959619) B1959619
theorem B4406987 : Blo 1740571 4406987 := bstep (se 1 (by rfl) ⟨3305240, by rfl⟩ : syracuseStep 4406987 = 6610481) B6610481
theorem B1859275 : Blo 1740571 1859275 := bstep (se 1 (by rfl) ⟨1394456, by rfl⟩ : syracuseStep 1859275 = 2788913) B2788913
theorem B2612939 : Blo 1740571 2612939 := bstep (se 1 (by rfl) ⟨1959704, by rfl⟩ : syracuseStep 2612939 = 3919409) B3919409
theorem B2612951 : Blo 1740571 2612951 := bstep (se 1 (by rfl) ⟨1959713, by rfl⟩ : syracuseStep 2612951 = 3919427) B3919427
theorem B7061251 : Blo 1740571 7061251 := bstep (se 1 (by rfl) ⟨5295938, by rfl⟩ : syracuseStep 7061251 = 10591877) B10591877
theorem B2613017 : Blo 1740571 2613017 := bstep (se 2 (by rfl) ⟨979881, by rfl⟩ : syracuseStep 2613017 = 1959763) B1959763
theorem B2613131 : Blo 1740571 2613131 := bstep (se 1 (by rfl) ⟨1959848, by rfl⟩ : syracuseStep 2613131 = 3919697) B3919697
theorem B2613143 : Blo 1740571 2613143 := bstep (se 1 (by rfl) ⟨1959857, by rfl⟩ : syracuseStep 2613143 = 3919715) B3919715
theorem B1859531 : Blo 1740571 1859531 := bstep (se 1 (by rfl) ⟨1394648, by rfl⟩ : syracuseStep 1859531 = 2789297) B2789297
theorem B2613209 : Blo 1740571 2613209 := bstep (se 2 (by rfl) ⟨979953, by rfl⟩ : syracuseStep 2613209 = 1959907) B1959907
theorem B4407311 : Blo 1740571 4407311 := bstep (se 1 (by rfl) ⟨3305483, by rfl⟩ : syracuseStep 4407311 = 6610967) B6610967
theorem B2613263 : Blo 1740571 2613263 := bstep (se 1 (by rfl) ⟨1959947, by rfl⟩ : syracuseStep 2613263 = 3919895) B3919895
theorem B2613305 : Blo 1740571 2613305 := bstep (se 2 (by rfl) ⟨979989, by rfl⟩ : syracuseStep 2613305 = 1959979) B1959979
theorem B2613383 : Blo 1740571 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B4407443 : Blo 1740571 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B2613419 : Blo 1740571 2613419 := bstep (se 1 (by rfl) ⟨1960064, by rfl⟩ : syracuseStep 2613419 = 3920129) B3920129
theorem B28237997 : Blo 1740571 28237997 := bstep (se 3 (by rfl) ⟨5294624, by rfl⟩ : syracuseStep 28237997 = 10589249) B10589249
theorem B3719353 : Blo 1740571 3719353 := bstep (se 2 (by rfl) ⟨1394757, by rfl⟩ : syracuseStep 3719353 = 2789515) B2789515
theorem B2613449 : Blo 1740571 2613449 := bstep (se 2 (by rfl) ⟨980043, by rfl⟩ : syracuseStep 2613449 = 1960087) B1960087
theorem B2613563 : Blo 1740571 2613563 := bstep (se 1 (by rfl) ⟨1960172, by rfl⟩ : syracuseStep 2613563 = 3920345) B3920345
theorem B2613623 : Blo 1740571 2613623 := bstep (se 1 (by rfl) ⟨1960217, by rfl⟩ : syracuseStep 2613623 = 3920435) B3920435
theorem B1958287 : Blo 1740571 1958287 := bstep (se 1 (by rfl) ⟨1468715, by rfl⟩ : syracuseStep 1958287 = 2937431) B2937431
theorem B2613647 : Blo 1740571 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B3719609 : Blo 1740571 3719609 := bstep (se 2 (by rfl) ⟨1394853, by rfl⟩ : syracuseStep 3719609 = 2789707) B2789707
theorem B2613689 : Blo 1740571 2613689 := bstep (se 2 (by rfl) ⟨980133, by rfl⟩ : syracuseStep 2613689 = 1960267) B1960267
theorem B8364491 : Blo 1740571 8364491 := bstep (se 1 (by rfl) ⟨6273368, by rfl⟩ : syracuseStep 8364491 = 12546737) B12546737
theorem B2204167 : Blo 1740571 2204167 := bstep (se 1 (by rfl) ⟨1653125, by rfl⟩ : syracuseStep 2204167 = 3306251) B3306251
theorem B2613767 : Blo 1740571 2613767 := bstep (se 1 (by rfl) ⟨1960325, by rfl⟩ : syracuseStep 2613767 = 3920651) B3920651
theorem B3719695 : Blo 1740571 3719695 := bstep (se 1 (by rfl) ⟨2789771, by rfl⟩ : syracuseStep 3719695 = 5579543) B5579543
theorem B7438877 : Blo 1740571 7438877 := bstep (se 3 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 7438877 = 2789579) B2789579
theorem B3916331 : Blo 1740571 3916331 := bstep (se 1 (by rfl) ⟨2937248, by rfl⟩ : syracuseStep 3916331 = 5874497) B5874497
theorem B21471787 : Blo 1740571 21471787 := bstep (se 1 (by rfl) ⟨16103840, by rfl⟩ : syracuseStep 21471787 = 32207681) B32207681
theorem B2613803 : Blo 1740571 2613803 := bstep (se 1 (by rfl) ⟨1960352, by rfl⟩ : syracuseStep 2613803 = 3920705) B3920705
theorem B2613833 : Blo 1740571 2613833 := bstep (se 2 (by rfl) ⟨980187, by rfl⟩ : syracuseStep 2613833 = 1960375) B1960375
theorem B9921143 : Blo 1740571 9921143 := bstep (se 1 (by rfl) ⟨7440857, by rfl⟩ : syracuseStep 9921143 = 14881715) B14881715
theorem B3351175 : Blo 1740571 3351175 := bstep (se 1 (by rfl) ⟨2513381, by rfl⟩ : syracuseStep 3351175 = 5026763) B5026763
theorem B1860283 : Blo 1740571 1860283 := bstep (se 1 (by rfl) ⟨1395212, by rfl⟩ : syracuseStep 1860283 = 2790425) B2790425
theorem B12550913 : Blo 1740571 12550913 := bstep (se 2 (by rfl) ⟨4706592, by rfl⟩ : syracuseStep 12550913 = 9413185) B9413185
theorem B9061121 : Blo 1740571 9061121 := bstep (se 2 (by rfl) ⟨3397920, by rfl⟩ : syracuseStep 9061121 = 6795841) B6795841
theorem B9913103 : Blo 1740571 9913103 := bstep (se 1 (by rfl) ⟨7434827, by rfl⟩ : syracuseStep 9913103 = 14869655) B14869655
theorem B8364815 : Blo 1740571 8364815 := bstep (se 1 (by rfl) ⟨6273611, by rfl⟩ : syracuseStep 8364815 = 12547223) B12547223
theorem B13230863 : Blo 1740571 13230863 := bstep (se 1 (by rfl) ⟨9923147, by rfl⟩ : syracuseStep 13230863 = 19846295) B19846295
theorem B8938291 : Blo 1740571 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1958791 : Blo 1740571 1958791 := bstep (se 1 (by rfl) ⟨1469093, by rfl⟩ : syracuseStep 1958791 = 2938187) B2938187
theorem B3916691 : Blo 1740571 3916691 := bstep (se 1 (by rfl) ⟨2937518, by rfl⟩ : syracuseStep 3916691 = 5875037) B5875037
theorem B2204587 : Blo 1740571 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B3916745 : Blo 1740571 3916745 := bstep (se 2 (by rfl) ⟨1468779, by rfl⟩ : syracuseStep 3916745 = 2937559) B2937559
theorem B15885335 : Blo 1740571 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B3138593 : Blo 1740571 3138593 := bstep (se 2 (by rfl) ⟨1176972, by rfl⟩ : syracuseStep 3138593 = 2353945) B2353945
theorem B1958971 : Blo 1740571 1958971 := bstep (se 1 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 1958971 = 2938457) B2938457
theorem B10593341 : Blo 1740571 10593341 := bstep (se 3 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 10593341 = 3972503) B3972503
theorem B2204815 : Blo 1740571 2204815 := bstep (se 1 (by rfl) ⟨1653611, by rfl⟩ : syracuseStep 2204815 = 3307223) B3307223
theorem B4957337 : Blo 1740571 4957337 := bstep (se 2 (by rfl) ⟨1859001, by rfl⟩ : syracuseStep 4957337 = 3718003) B3718003
theorem B3351737 : Blo 1740571 3351737 := bstep (se 2 (by rfl) ⟨1256901, by rfl⟩ : syracuseStep 3351737 = 2513803) B2513803
theorem B14886089 : Blo 1740571 14886089 := bstep (se 2 (by rfl) ⟨5582283, by rfl⟩ : syracuseStep 14886089 = 11164567) B11164567
theorem B4408577 : Blo 1740571 4408577 := bstep (se 2 (by rfl) ⟨1653216, by rfl⟩ : syracuseStep 4408577 = 3306433) B3306433
theorem B9921851 : Blo 1740571 9921851 := bstep (se 1 (by rfl) ⟨7441388, by rfl⟩ : syracuseStep 9921851 = 14882777) B14882777
theorem B3720583 : Blo 1740571 3720583 := bstep (se 1 (by rfl) ⟨2790437, by rfl⟩ : syracuseStep 3720583 = 5580875) B5580875
theorem B5875091 : Blo 1740571 5875091 := bstep (se 1 (by rfl) ⟨4406318, by rfl⟩ : syracuseStep 5875091 = 8812637) B8812637
theorem B11920787 : Blo 1740571 11920787 := bstep (se 1 (by rfl) ⟨8940590, by rfl⟩ : syracuseStep 11920787 = 17881181) B17881181
theorem B1959439 : Blo 1740571 1959439 := bstep (se 1 (by rfl) ⟨1469579, by rfl⟩ : syracuseStep 1959439 = 2939159) B2939159
theorem B3720737 : Blo 1740571 3720737 := bstep (se 2 (by rfl) ⟨1395276, by rfl⟩ : syracuseStep 3720737 = 2790553) B2790553
theorem B4408951 : Blo 1740571 4408951 := bstep (se 1 (by rfl) ⟨3306713, by rfl⟩ : syracuseStep 4408951 = 6613427) B6613427
theorem B3917447 : Blo 1740571 3917447 := bstep (se 1 (by rfl) ⟨2938085, by rfl⟩ : syracuseStep 3917447 = 5876171) B5876171
theorem B3917627 : Blo 1740571 3917627 := bstep (se 1 (by rfl) ⟨2938220, by rfl⟩ : syracuseStep 3917627 = 5876441) B5876441
theorem B4466519 : Blo 1740571 4466519 := bstep (se 1 (by rfl) ⟨3349889, by rfl⟩ : syracuseStep 4466519 = 6699779) B6699779
theorem B3721079 : Blo 1740571 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B3917753 : Blo 1740571 3917753 := bstep (se 2 (by rfl) ⟨1469157, by rfl⟩ : syracuseStep 3917753 = 2938315) B2938315
theorem B1959943 : Blo 1740571 1959943 := bstep (se 1 (by rfl) ⟨1469957, by rfl⟩ : syracuseStep 1959943 = 2939915) B2939915
theorem B3721249 : Blo 1740571 3721249 := bstep (se 2 (by rfl) ⟨1395468, by rfl⟩ : syracuseStep 3721249 = 2790937) B2790937
theorem B4409387 : Blo 1740571 4409387 := bstep (se 1 (by rfl) ⟨3307040, by rfl⟩ : syracuseStep 4409387 = 6614081) B6614081
theorem B1960123 : Blo 1740571 1960123 := bstep (se 1 (by rfl) ⟨1470092, by rfl⟩ : syracuseStep 1960123 = 2940185) B2940185
theorem B9914561 : Blo 1740571 9914561 := bstep (se 2 (by rfl) ⟨3717960, by rfl⟩ : syracuseStep 9914561 = 7435921) B7435921
theorem B3918095 : Blo 1740571 3918095 := bstep (se 1 (by rfl) ⟨2938571, by rfl⟩ : syracuseStep 3918095 = 5877143) B5877143
theorem B3918113 : Blo 1740571 3918113 := bstep (se 2 (by rfl) ⟨1469292, by rfl⟩ : syracuseStep 3918113 = 2938585) B2938585
theorem B2353465 : Blo 1740571 2353465 := bstep (se 2 (by rfl) ⟨882549, by rfl⟩ : syracuseStep 2353465 = 1765099) B1765099
theorem B9415001 : Blo 1740571 9415001 := bstep (se 2 (by rfl) ⟨3530625, by rfl⟩ : syracuseStep 9415001 = 7061251) B7061251
theorem B8817011 : Blo 1740571 8817011 := bstep (se 1 (by rfl) ⟨6612758, by rfl⟩ : syracuseStep 8817011 = 13225517) B13225517
theorem B4958749 : Blo 1740571 4958749 := bstep (se 3 (by rfl) ⟨929765, by rfl⟩ : syracuseStep 4958749 = 1859531) B1859531
theorem B3918455 : Blo 1740571 3918455 := bstep (se 1 (by rfl) ⟨2938841, by rfl⟩ : syracuseStep 3918455 = 5877683) B5877683
theorem B4958921 : Blo 1740571 4958921 := bstep (se 2 (by rfl) ⟨1859595, by rfl⟩ : syracuseStep 4958921 = 3719191) B3719191
theorem B9923309 : Blo 1740571 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B4958977 : Blo 1740571 4958977 := bstep (se 2 (by rfl) ⟨1859616, by rfl⟩ : syracuseStep 4958977 = 3719233) B3719233
theorem B5876495 : Blo 1740571 5876495 := bstep (se 1 (by rfl) ⟨4407371, by rfl⟩ : syracuseStep 5876495 = 8814743) B8814743
theorem B3918635 : Blo 1740571 3918635 := bstep (se 1 (by rfl) ⟨2938976, by rfl⟩ : syracuseStep 3918635 = 5877953) B5877953
theorem B8817497 : Blo 1740571 8817497 := bstep (se 2 (by rfl) ⟨3306561, by rfl⟩ : syracuseStep 8817497 = 6613123) B6613123
theorem B9055091 : Blo 1740571 9055091 := bstep (se 1 (by rfl) ⟨6791318, by rfl⟩ : syracuseStep 9055091 = 13582637) B13582637
theorem B76319603 : Blo 1740571 76319603 := bstep (se 1 (by rfl) ⟨57239702, by rfl⟩ : syracuseStep 76319603 = 114479405) B114479405
theorem B4410227 : Blo 1740571 4410227 := bstep (se 1 (by rfl) ⟨3307670, by rfl⟩ : syracuseStep 4410227 = 6615341) B6615341
theorem B6278023 : Blo 1740571 6278023 := bstep (se 1 (by rfl) ⟨4708517, by rfl⟩ : syracuseStep 6278023 = 9417035) B9417035
theorem B4410247 : Blo 1740571 4410247 := bstep (se 1 (by rfl) ⟨3307685, by rfl⟩ : syracuseStep 4410247 = 6615371) B6615371
theorem B6613913 : Blo 1740571 6613913 := bstep (se 2 (by rfl) ⟨2480217, by rfl⟩ : syracuseStep 6613913 = 4960435) B4960435
theorem B50187275 : Blo 1740571 50187275 := bstep (se 1 (by rfl) ⟨37640456, by rfl⟩ : syracuseStep 50187275 = 75280913) B75280913
theorem B5876765 : Blo 1740571 5876765 := bstep (se 3 (by rfl) ⟨1101893, by rfl⟩ : syracuseStep 5876765 = 2203787) B2203787
theorem B5295137 : Blo 1740571 5295137 := bstep (se 2 (by rfl) ⟨1985676, by rfl⟩ : syracuseStep 5295137 = 3971353) B3971353
theorem B4959319 : Blo 1740571 4959319 := bstep (se 1 (by rfl) ⟨3719489, by rfl⟩ : syracuseStep 4959319 = 7438979) B7438979
theorem B3918995 : Blo 1740571 3918995 := bstep (se 1 (by rfl) ⟨2939246, by rfl⟩ : syracuseStep 3918995 = 5878493) B5878493
theorem B4410521 : Blo 1740571 4410521 := bstep (se 2 (by rfl) ⟨1653945, by rfl⟩ : syracuseStep 4410521 = 3307891) B3307891
theorem B3304633 : Blo 1740571 3304633 := bstep (se 2 (by rfl) ⟨1239237, by rfl⟩ : syracuseStep 3304633 = 2478475) B2478475
theorem B3919049 : Blo 1740571 3919049 := bstep (se 2 (by rfl) ⟨1469643, by rfl⟩ : syracuseStep 3919049 = 2939287) B2939287
theorem B4410683 : Blo 1740571 4410683 := bstep (se 1 (by rfl) ⟨3308012, by rfl⟩ : syracuseStep 4410683 = 6616025) B6616025
theorem B29765069 : Blo 1740571 29765069 := bstep (se 3 (by rfl) ⟨5580950, by rfl⟩ : syracuseStep 29765069 = 11161901) B11161901
theorem B3304975 : Blo 1740571 3304975 := bstep (se 1 (by rfl) ⟨2478731, by rfl⟩ : syracuseStep 3304975 = 4957463) B4957463
theorem B22310477 : Blo 1740571 22310477 := bstep (se 3 (by rfl) ⟨4183214, by rfl⟩ : syracuseStep 22310477 = 8366429) B8366429
theorem B2354875 : Blo 1740571 2354875 := bstep (se 1 (by rfl) ⟨1766156, by rfl⟩ : syracuseStep 2354875 = 3532313) B3532313
theorem B19844837 : Blo 1740571 19844837 := bstep (se 4 (by rfl) ⟨1860453, by rfl⟩ : syracuseStep 19844837 = 3720907) B3720907
theorem B2354951 : Blo 1740571 2354951 := bstep (se 1 (by rfl) ⟨1766213, by rfl⟩ : syracuseStep 2354951 = 3532427) B3532427
theorem B1740603 : Blo 1740571 1740603 := bstep (se 1 (by rfl) ⟨1305452, by rfl⟩ : syracuseStep 1740603 = 2610905) B2610905
theorem B1740679 : Blo 1740571 1740679 := bstep (se 1 (by rfl) ⟨1305509, by rfl⟩ : syracuseStep 1740679 = 2611019) B2611019
theorem B3919751 : Blo 1740571 3919751 := bstep (se 1 (by rfl) ⟨2939813, by rfl⟩ : syracuseStep 3919751 = 5879627) B5879627
theorem B1740687 : Blo 1740571 1740687 := bstep (se 1 (by rfl) ⟨1305515, by rfl⟩ : syracuseStep 1740687 = 2611031) B2611031
theorem B1740731 : Blo 1740571 1740731 := bstep (se 1 (by rfl) ⟨1305548, by rfl⟩ : syracuseStep 1740731 = 2611097) B2611097
theorem B1740807 : Blo 1740571 1740807 := bstep (se 1 (by rfl) ⟨1305605, by rfl⟩ : syracuseStep 1740807 = 2611211) B2611211
theorem B1740815 : Blo 1740571 1740815 := bstep (se 1 (by rfl) ⟨1305611, by rfl⟩ : syracuseStep 1740815 = 2611223) B2611223
theorem B1740859 : Blo 1740571 1740859 := bstep (se 1 (by rfl) ⟨1305644, by rfl⟩ : syracuseStep 1740859 = 2611289) B2611289
theorem B3919931 : Blo 1740571 3919931 := bstep (se 1 (by rfl) ⟨2939948, by rfl⟩ : syracuseStep 3919931 = 5879897) B5879897
theorem B33493085 : Blo 1740571 33493085 := bstep (se 3 (by rfl) ⟨6279953, by rfl⟩ : syracuseStep 33493085 = 12559907) B12559907
theorem B1740935 : Blo 1740571 1740935 := bstep (se 1 (by rfl) ⟨1305701, by rfl⟩ : syracuseStep 1740935 = 2611403) B2611403
theorem B1740943 : Blo 1740571 1740943 := bstep (se 1 (by rfl) ⟨1305707, by rfl⟩ : syracuseStep 1740943 = 2611415) B2611415
theorem B3920057 : Blo 1740571 3920057 := bstep (se 2 (by rfl) ⟨1470021, by rfl⟩ : syracuseStep 3920057 = 2940043) B2940043
theorem B1740987 : Blo 1740571 1740987 := bstep (se 1 (by rfl) ⟨1305740, by rfl⟩ : syracuseStep 1740987 = 2611481) B2611481
theorem B2478281 : Blo 1740571 2478281 := bstep (se 2 (by rfl) ⟨929355, by rfl⟩ : syracuseStep 2478281 = 1858711) B1858711
theorem B1741063 : Blo 1740571 1741063 := bstep (se 1 (by rfl) ⟨1305797, by rfl⟩ : syracuseStep 1741063 = 2611595) B2611595
theorem B1741071 : Blo 1740571 1741071 := bstep (se 1 (by rfl) ⟨1305803, by rfl⟩ : syracuseStep 1741071 = 2611607) B2611607
theorem B2478395 : Blo 1740571 2478395 := bstep (se 1 (by rfl) ⟨1858796, by rfl⟩ : syracuseStep 2478395 = 3717593) B3717593
theorem B1741115 : Blo 1740571 1741115 := bstep (se 1 (by rfl) ⟨1305836, by rfl⟩ : syracuseStep 1741115 = 2611673) B2611673
theorem B16740701 : Blo 1740571 16740701 := bstep (se 3 (by rfl) ⟨3138881, by rfl⟩ : syracuseStep 16740701 = 6277763) B6277763
theorem B2978167 : Blo 1740571 2978167 := bstep (se 1 (by rfl) ⟨2233625, by rfl⟩ : syracuseStep 2978167 = 4467251) B4467251
theorem B14872967 : Blo 1740571 14872967 := bstep (se 1 (by rfl) ⟨11154725, by rfl⟩ : syracuseStep 14872967 = 22309451) B22309451
theorem B1741191 : Blo 1740571 1741191 := bstep (se 1 (by rfl) ⟨1305893, by rfl⟩ : syracuseStep 1741191 = 2611787) B2611787
theorem B3305863 : Blo 1740571 3305863 := bstep (se 1 (by rfl) ⟨2479397, by rfl⟩ : syracuseStep 3305863 = 4958795) B4958795
theorem B1741199 : Blo 1740571 1741199 := bstep (se 1 (by rfl) ⟨1305899, by rfl⟩ : syracuseStep 1741199 = 2611799) B2611799
theorem B5878169 : Blo 1740571 5878169 := bstep (se 2 (by rfl) ⟨2204313, by rfl⟩ : syracuseStep 5878169 = 4408627) B4408627
theorem B1741243 : Blo 1740571 1741243 := bstep (se 1 (by rfl) ⟨1305932, by rfl⟩ : syracuseStep 1741243 = 2611865) B2611865
theorem B2937289 : Blo 1740571 2937289 := bstep (se 2 (by rfl) ⟨1101483, by rfl⟩ : syracuseStep 2937289 = 2202967) B2202967
theorem B9417163 : Blo 1740571 9417163 := bstep (se 1 (by rfl) ⟨7062872, by rfl⟩ : syracuseStep 9417163 = 14125745) B14125745
theorem B1741319 : Blo 1740571 1741319 := bstep (se 1 (by rfl) ⟨1305989, by rfl⟩ : syracuseStep 1741319 = 2611979) B2611979
theorem B1741327 : Blo 1740571 1741327 := bstep (se 1 (by rfl) ⟨1305995, by rfl⟩ : syracuseStep 1741327 = 2611991) B2611991
theorem B3920399 : Blo 1740571 3920399 := bstep (se 1 (by rfl) ⟨2940299, by rfl⟩ : syracuseStep 3920399 = 5880599) B5880599
theorem B9916951 : Blo 1740571 9916951 := bstep (se 1 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 9916951 = 14875427) B14875427
theorem B3920417 : Blo 1740571 3920417 := bstep (se 2 (by rfl) ⟨1470156, by rfl⟩ : syracuseStep 3920417 = 2940313) B2940313
theorem B1741371 : Blo 1740571 1741371 := bstep (se 1 (by rfl) ⟨1306028, by rfl⟩ : syracuseStep 1741371 = 2612057) B2612057
theorem B1741447 : Blo 1740571 1741447 := bstep (se 1 (by rfl) ⟨1306085, by rfl⟩ : syracuseStep 1741447 = 2612171) B2612171
theorem B1741455 : Blo 1740571 1741455 := bstep (se 1 (by rfl) ⟨1306091, by rfl⟩ : syracuseStep 1741455 = 2612183) B2612183
theorem B1741499 : Blo 1740571 1741499 := bstep (se 1 (by rfl) ⟨1306124, by rfl⟩ : syracuseStep 1741499 = 2612249) B2612249
theorem B7443181 : Blo 1740571 7443181 := bstep (se 3 (by rfl) ⟨1395596, by rfl⟩ : syracuseStep 7443181 = 2791193) B2791193
theorem B1741575 : Blo 1740571 1741575 := bstep (se 1 (by rfl) ⟨1306181, by rfl⟩ : syracuseStep 1741575 = 2612363) B2612363
theorem B1741583 : Blo 1740571 1741583 := bstep (se 1 (by rfl) ⟨1306187, by rfl⟩ : syracuseStep 1741583 = 2612375) B2612375
theorem B42382115 : Blo 1740571 42382115 := bstep (se 1 (by rfl) ⟨31786586, by rfl⟩ : syracuseStep 42382115 = 63573173) B63573173
theorem B16732979 : Blo 1740571 16732979 := bstep (se 1 (by rfl) ⟨12549734, by rfl⟩ : syracuseStep 16732979 = 25099469) B25099469
theorem B1741627 : Blo 1740571 1741627 := bstep (se 1 (by rfl) ⟨1306220, by rfl⟩ : syracuseStep 1741627 = 2612441) B2612441
theorem B3920759 : Blo 1740571 3920759 := bstep (se 1 (by rfl) ⟨2940569, by rfl⟩ : syracuseStep 3920759 = 5881139) B5881139
theorem B1741703 : Blo 1740571 1741703 := bstep (se 1 (by rfl) ⟨1306277, by rfl⟩ : syracuseStep 1741703 = 2612555) B2612555
theorem B1741711 : Blo 1740571 1741711 := bstep (se 1 (by rfl) ⟨1306283, by rfl⟩ : syracuseStep 1741711 = 2612567) B2612567
theorem B8819603 : Blo 1740571 8819603 := bstep (se 1 (by rfl) ⟨6614702, by rfl⟩ : syracuseStep 8819603 = 13229405) B13229405
theorem B13218713 : Blo 1740571 13218713 := bstep (se 2 (by rfl) ⟨4957017, by rfl⟩ : syracuseStep 13218713 = 9914035) B9914035
theorem B7443353 : Blo 1740571 7443353 := bstep (se 2 (by rfl) ⟨2791257, by rfl⟩ : syracuseStep 7443353 = 5582515) B5582515
theorem B2479033 : Blo 1740571 2479033 := bstep (se 2 (by rfl) ⟨929637, by rfl⟩ : syracuseStep 2479033 = 1859275) B1859275
theorem B1741755 : Blo 1740571 1741755 := bstep (se 1 (by rfl) ⟨1306316, by rfl⟩ : syracuseStep 1741755 = 2612633) B2612633
theorem B1741831 : Blo 1740571 1741831 := bstep (se 1 (by rfl) ⟨1306373, by rfl⟩ : syracuseStep 1741831 = 2612747) B2612747
theorem B1741839 : Blo 1740571 1741839 := bstep (se 1 (by rfl) ⟨1306379, by rfl⟩ : syracuseStep 1741839 = 2612759) B2612759
theorem B4707371 : Blo 1740571 4707371 := bstep (se 1 (by rfl) ⟨3530528, by rfl⟩ : syracuseStep 4707371 = 7061057) B7061057
theorem B1741883 : Blo 1740571 1741883 := bstep (se 1 (by rfl) ⟨1306412, by rfl⟩ : syracuseStep 1741883 = 2612825) B2612825
theorem B5878871 : Blo 1740571 5878871 := bstep (se 1 (by rfl) ⟨4409153, by rfl⟩ : syracuseStep 5878871 = 8818307) B8818307
theorem B2937991 : Blo 1740571 2937991 := bstep (se 1 (by rfl) ⟨2203493, by rfl⟩ : syracuseStep 2937991 = 4406987) B4406987
theorem B1741959 : Blo 1740571 1741959 := bstep (se 1 (by rfl) ⟨1306469, by rfl⟩ : syracuseStep 1741959 = 2612939) B2612939
theorem B1741967 : Blo 1740571 1741967 := bstep (se 1 (by rfl) ⟨1306475, by rfl⟩ : syracuseStep 1741967 = 2612951) B2612951
theorem B1742011 : Blo 1740571 1742011 := bstep (se 1 (by rfl) ⟨1306508, by rfl⟩ : syracuseStep 1742011 = 2613017) B2613017
theorem B1742087 : Blo 1740571 1742087 := bstep (se 1 (by rfl) ⟨1306565, by rfl⟩ : syracuseStep 1742087 = 2613131) B2613131
theorem B1742095 : Blo 1740571 1742095 := bstep (se 1 (by rfl) ⟨1306571, by rfl⟩ : syracuseStep 1742095 = 2613143) B2613143
theorem B8811827 : Blo 1740571 8811827 := bstep (se 1 (by rfl) ⟨6608870, by rfl⟩ : syracuseStep 8811827 = 13217741) B13217741
theorem B1742139 : Blo 1740571 1742139 := bstep (se 1 (by rfl) ⟨1306604, by rfl⟩ : syracuseStep 1742139 = 2613209) B2613209
theorem B5297495 : Blo 1740571 5297495 := bstep (se 1 (by rfl) ⟨3973121, by rfl⟩ : syracuseStep 5297495 = 7946243) B7946243
theorem B12080519 : Blo 1740571 12080519 := bstep (se 1 (by rfl) ⟨9060389, by rfl⟩ : syracuseStep 12080519 = 18120779) B18120779
theorem B1742215 : Blo 1740571 1742215 := bstep (se 1 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 1742215 = 2613323) B2613323
theorem B1742223 : Blo 1740571 1742223 := bstep (se 1 (by rfl) ⟨1306667, by rfl⟩ : syracuseStep 1742223 = 2613335) B2613335
theorem B1742267 : Blo 1740571 1742267 := bstep (se 1 (by rfl) ⟨1306700, by rfl⟩ : syracuseStep 1742267 = 2613401) B2613401
theorem B1742343 : Blo 1740571 1742343 := bstep (se 1 (by rfl) ⟨1306757, by rfl⟩ : syracuseStep 1742343 = 2613515) B2613515
theorem B1742351 : Blo 1740571 1742351 := bstep (se 1 (by rfl) ⟨1306763, by rfl⟩ : syracuseStep 1742351 = 2613527) B2613527
theorem B1742395 : Blo 1740571 1742395 := bstep (se 1 (by rfl) ⟨1306796, by rfl⟩ : syracuseStep 1742395 = 2613593) B2613593
theorem B5879357 : Blo 1740571 5879357 := bstep (se 3 (by rfl) ⟨1102379, by rfl⟩ : syracuseStep 5879357 = 2204759) B2204759
theorem B8812151 : Blo 1740571 8812151 := bstep (se 1 (by rfl) ⟨6609113, by rfl⟩ : syracuseStep 8812151 = 13218227) B13218227
theorem B1742471 : Blo 1740571 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B1742479 : Blo 1740571 1742479 := bstep (se 1 (by rfl) ⟨1306859, by rfl⟩ : syracuseStep 1742479 = 2613719) B2613719
theorem B2610875 : Blo 1740571 2610875 := bstep (se 1 (by rfl) ⟨1958156, by rfl⟩ : syracuseStep 2610875 = 3916313) B3916313
theorem B1742523 : Blo 1740571 1742523 := bstep (se 1 (by rfl) ⟨1306892, by rfl⟩ : syracuseStep 1742523 = 2613785) B2613785
theorem B2610935 : Blo 1740571 2610935 := bstep (se 1 (by rfl) ⟨1958201, by rfl⟩ : syracuseStep 2610935 = 3916403) B3916403
theorem B2610959 : Blo 1740571 2610959 := bstep (se 1 (by rfl) ⟨1958219, by rfl⟩ : syracuseStep 2610959 = 3916439) B3916439
theorem B2938639 : Blo 1740571 2938639 := bstep (se 1 (by rfl) ⟨2203979, by rfl⟩ : syracuseStep 2938639 = 4407959) B4407959
theorem B2611001 : Blo 1740571 2611001 := bstep (se 2 (by rfl) ⟨979125, by rfl⟩ : syracuseStep 2611001 = 1958251) B1958251
theorem B41318261 : Blo 1740571 41318261 := bstep (se 5 (by rfl) ⟨1936793, by rfl⟩ : syracuseStep 41318261 = 3873587) B3873587
theorem B4962167 : Blo 1740571 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B2611079 : Blo 1740571 2611079 := bstep (se 1 (by rfl) ⟨1958309, by rfl⟩ : syracuseStep 2611079 = 3916619) B3916619
theorem B2611115 : Blo 1740571 2611115 := bstep (se 1 (by rfl) ⟨1958336, by rfl⟩ : syracuseStep 2611115 = 3916673) B3916673
theorem B2611145 : Blo 1740571 2611145 := bstep (se 2 (by rfl) ⟨979179, by rfl⟩ : syracuseStep 2611145 = 1958359) B1958359
theorem B2611259 : Blo 1740571 2611259 := bstep (se 1 (by rfl) ⟨1958444, by rfl⟩ : syracuseStep 2611259 = 3916889) B3916889
theorem B2611319 : Blo 1740571 2611319 := bstep (se 1 (by rfl) ⟨1958489, by rfl⟩ : syracuseStep 2611319 = 3916979) B3916979
theorem B3307655 : Blo 1740571 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B2611343 : Blo 1740571 2611343 := bstep (se 1 (by rfl) ⟨1958507, by rfl⟩ : syracuseStep 2611343 = 3917015) B3917015
theorem B2611385 : Blo 1740571 2611385 := bstep (se 2 (by rfl) ⟨979269, by rfl⟩ : syracuseStep 2611385 = 1958539) B1958539
theorem B2611463 : Blo 1740571 2611463 := bstep (se 1 (by rfl) ⟨1958597, by rfl⟩ : syracuseStep 2611463 = 3917195) B3917195
theorem B2611499 : Blo 1740571 2611499 := bstep (se 1 (by rfl) ⟨1958624, by rfl⟩ : syracuseStep 2611499 = 3917249) B3917249
theorem B2939179 : Blo 1740571 2939179 := bstep (se 1 (by rfl) ⟨2204384, by rfl⟩ : syracuseStep 2939179 = 4408769) B4408769
theorem B2611529 : Blo 1740571 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B13228433 : Blo 1740571 13228433 := bstep (se 2 (by rfl) ⟨4960662, by rfl⟩ : syracuseStep 13228433 = 9921325) B9921325
theorem B2939321 : Blo 1740571 2939321 := bstep (se 2 (by rfl) ⟨1102245, by rfl⟩ : syracuseStep 2939321 = 2204491) B2204491
theorem B2611643 : Blo 1740571 2611643 := bstep (se 1 (by rfl) ⟨1958732, by rfl⟩ : syracuseStep 2611643 = 3917465) B3917465
theorem B8370641 : Blo 1740571 8370641 := bstep (se 2 (by rfl) ⟨3138990, by rfl⟩ : syracuseStep 8370641 = 6277981) B6277981
theorem B33470941 : Blo 1740571 33470941 := bstep (se 3 (by rfl) ⟨6275801, by rfl⟩ : syracuseStep 33470941 = 12551603) B12551603
theorem B2611703 : Blo 1740571 2611703 := bstep (se 1 (by rfl) ⟨1958777, by rfl⟩ : syracuseStep 2611703 = 3917555) B3917555
theorem B7256587 : Blo 1740571 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B2611727 : Blo 1740571 2611727 := bstep (se 1 (by rfl) ⟨1958795, by rfl⟩ : syracuseStep 2611727 = 3917591) B3917591
theorem B2611769 : Blo 1740571 2611769 := bstep (se 2 (by rfl) ⟨979413, by rfl⟩ : syracuseStep 2611769 = 1958827) B1958827
theorem B8813123 : Blo 1740571 8813123 := bstep (se 1 (by rfl) ⟨6609842, by rfl⟩ : syracuseStep 8813123 = 13219685) B13219685
theorem B2611847 : Blo 1740571 2611847 := bstep (se 1 (by rfl) ⟨1958885, by rfl⟩ : syracuseStep 2611847 = 3917771) B3917771
theorem B2611883 : Blo 1740571 2611883 := bstep (se 1 (by rfl) ⟨1958912, by rfl⟩ : syracuseStep 2611883 = 3917825) B3917825
theorem B2611913 : Blo 1740571 2611913 := bstep (se 2 (by rfl) ⟨979467, by rfl⟩ : syracuseStep 2611913 = 1958935) B1958935
theorem B9411329 : Blo 1740571 9411329 := bstep (se 2 (by rfl) ⟨3529248, by rfl⟩ : syracuseStep 9411329 = 7058497) B7058497
theorem B13769473 : Blo 1740571 13769473 := bstep (se 2 (by rfl) ⟨5163552, by rfl⟩ : syracuseStep 13769473 = 10327105) B10327105
theorem B13220657 : Blo 1740571 13220657 := bstep (se 2 (by rfl) ⟨4957746, by rfl⟩ : syracuseStep 13220657 = 9915493) B9915493
theorem B2612027 : Blo 1740571 2612027 := bstep (se 1 (by rfl) ⟨1959020, by rfl⟩ : syracuseStep 2612027 = 3918041) B3918041
theorem B2612087 : Blo 1740571 2612087 := bstep (se 1 (by rfl) ⟨1959065, by rfl⟩ : syracuseStep 2612087 = 3918131) B3918131
theorem B8813447 : Blo 1740571 8813447 := bstep (se 1 (by rfl) ⟨6610085, by rfl⟩ : syracuseStep 8813447 = 13220171) B13220171
theorem B9919367 : Blo 1740571 9919367 := bstep (se 1 (by rfl) ⟨7439525, by rfl⟩ : syracuseStep 9919367 = 14879051) B14879051
theorem B2612111 : Blo 1740571 2612111 := bstep (se 1 (by rfl) ⟨1959083, by rfl⟩ : syracuseStep 2612111 = 3918167) B3918167
theorem B7437203 : Blo 1740571 7437203 := bstep (se 1 (by rfl) ⟨5577902, by rfl⟩ : syracuseStep 7437203 = 11155805) B11155805
theorem B19831715 : Blo 1740571 19831715 := bstep (se 1 (by rfl) ⟨14873786, by rfl⟩ : syracuseStep 19831715 = 29747573) B29747573
theorem B2612153 : Blo 1740571 2612153 := bstep (se 2 (by rfl) ⟨979557, by rfl⟩ : syracuseStep 2612153 = 1959115) B1959115
theorem B5880761 : Blo 1740571 5880761 := bstep (se 2 (by rfl) ⟨2205285, by rfl⟩ : syracuseStep 5880761 = 4410571) B4410571
theorem B2612231 : Blo 1740571 2612231 := bstep (se 1 (by rfl) ⟨1959173, by rfl⟩ : syracuseStep 2612231 = 3918347) B3918347
theorem B2612267 : Blo 1740571 2612267 := bstep (se 1 (by rfl) ⟨1959200, by rfl⟩ : syracuseStep 2612267 = 3918401) B3918401
theorem B2612297 : Blo 1740571 2612297 := bstep (se 2 (by rfl) ⟨979611, by rfl⟩ : syracuseStep 2612297 = 1959223) B1959223
theorem B4406359 : Blo 1740571 4406359 := bstep (se 1 (by rfl) ⟨3304769, by rfl⟩ : syracuseStep 4406359 = 6609539) B6609539
theorem B16735319 : Blo 1740571 16735319 := bstep (se 1 (by rfl) ⟨12551489, by rfl⟩ : syracuseStep 16735319 = 25102979) B25102979
theorem B2940023 : Blo 1740571 2940023 := bstep (se 1 (by rfl) ⟨2205017, by rfl⟩ : syracuseStep 2940023 = 4410035) B4410035
theorem B2612411 : Blo 1740571 2612411 := bstep (se 1 (by rfl) ⟨1959308, by rfl⟩ : syracuseStep 2612411 = 3918617) B3918617
theorem B3718345 : Blo 1740571 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B2612471 : Blo 1740571 2612471 := bstep (se 1 (by rfl) ⟨1959353, by rfl⟩ : syracuseStep 2612471 = 3918707) B3918707
theorem B2612495 : Blo 1740571 2612495 := bstep (se 1 (by rfl) ⟨1959371, by rfl⟩ : syracuseStep 2612495 = 3918743) B3918743
theorem B2612537 : Blo 1740571 2612537 := bstep (se 2 (by rfl) ⟨979701, by rfl⟩ : syracuseStep 2612537 = 1959403) B1959403
theorem B4406663 : Blo 1740571 4406663 := bstep (se 1 (by rfl) ⟨3304997, by rfl⟩ : syracuseStep 4406663 = 6609995) B6609995
theorem B2612615 : Blo 1740571 2612615 := bstep (se 1 (by rfl) ⟨1959461, by rfl⟩ : syracuseStep 2612615 = 3918923) B3918923
theorem B2612651 : Blo 1740571 2612651 := bstep (se 1 (by rfl) ⟨1959488, by rfl⟩ : syracuseStep 2612651 = 3918977) B3918977
theorem B21192121 : Blo 1740571 21192121 := bstep (se 2 (by rfl) ⟨7947045, by rfl⟩ : syracuseStep 21192121 = 15894091) B15894091
theorem B2612681 : Blo 1740571 2612681 := bstep (se 2 (by rfl) ⟨979755, by rfl⟩ : syracuseStep 2612681 = 1959511) B1959511
theorem B4406795 : Blo 1740571 4406795 := bstep (se 1 (by rfl) ⟨3305096, by rfl⟩ : syracuseStep 4406795 = 6610193) B6610193
theorem B2203195 : Blo 1740571 2203195 := bstep (se 1 (by rfl) ⟨1652396, by rfl⟩ : syracuseStep 2203195 = 3304793) B3304793
theorem B2612795 : Blo 1740571 2612795 := bstep (se 1 (by rfl) ⟨1959596, by rfl⟩ : syracuseStep 2612795 = 3919193) B3919193
theorem B2940475 : Blo 1740571 2940475 := bstep (se 1 (by rfl) ⟨2205356, by rfl⟩ : syracuseStep 2940475 = 4410713) B4410713
theorem B12557891 : Blo 1740571 12557891 := bstep (se 1 (by rfl) ⟨9418418, by rfl⟩ : syracuseStep 12557891 = 18836837) B18836837
theorem B2612855 : Blo 1740571 2612855 := bstep (se 1 (by rfl) ⟨1959641, by rfl⟩ : syracuseStep 2612855 = 3919283) B3919283
theorem B2612879 : Blo 1740571 2612879 := bstep (se 1 (by rfl) ⟨1959659, by rfl⟩ : syracuseStep 2612879 = 3919319) B3919319
theorem B2612921 : Blo 1740571 2612921 := bstep (se 2 (by rfl) ⟨979845, by rfl⟩ : syracuseStep 2612921 = 1959691) B1959691
theorem B10591973 : Blo 1740571 10591973 := bstep (se 4 (by rfl) ⟨992997, by rfl⟩ : syracuseStep 10591973 = 1985995) B1985995
theorem B2612999 : Blo 1740571 2612999 := bstep (se 1 (by rfl) ⟨1959749, by rfl⟩ : syracuseStep 2612999 = 3919499) B3919499
theorem B627351317 : Blo 1740571 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B2613035 : Blo 1740571 2613035 := bstep (se 1 (by rfl) ⟨1959776, by rfl⟩ : syracuseStep 2613035 = 3919553) B3919553
theorem B2613065 : Blo 1740571 2613065 := bstep (se 2 (by rfl) ⟨979899, by rfl⟩ : syracuseStep 2613065 = 1959799) B1959799
theorem B10592147 : Blo 1740571 10592147 := bstep (se 1 (by rfl) ⟨7944110, by rfl⟩ : syracuseStep 10592147 = 15888221) B15888221
theorem B2613179 : Blo 1740571 2613179 := bstep (se 1 (by rfl) ⟨1959884, by rfl⟩ : syracuseStep 2613179 = 3919769) B3919769
theorem B2613239 : Blo 1740571 2613239 := bstep (se 1 (by rfl) ⟨1959929, by rfl⟩ : syracuseStep 2613239 = 3919859) B3919859
theorem B2613257 : Blo 1740571 2613257 := bstep (se 2 (by rfl) ⟨979971, by rfl⟩ : syracuseStep 2613257 = 1959943) B1959943
theorem B2613287 : Blo 1740571 2613287 := bstep (se 1 (by rfl) ⟨1959965, by rfl⟩ : syracuseStep 2613287 = 3919931) B3919931
theorem B42360893 : Blo 1740571 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B18825331 : Blo 1740571 18825331 := bstep (se 1 (by rfl) ⟨14118998, by rfl⟩ : syracuseStep 18825331 = 28237997) B28237997
theorem B2613371 : Blo 1740571 2613371 := bstep (se 1 (by rfl) ⟨1960028, by rfl⟩ : syracuseStep 2613371 = 3920057) B3920057
theorem B71491733 : Blo 1740571 71491733 := bstep (se 6 (by rfl) ⟨1675587, by rfl⟩ : syracuseStep 71491733 = 3351175) B3351175
theorem B2613497 : Blo 1740571 2613497 := bstep (se 2 (by rfl) ⟨980061, by rfl⟩ : syracuseStep 2613497 = 1960123) B1960123
theorem B2613599 : Blo 1740571 2613599 := bstep (se 1 (by rfl) ⟨1960199, by rfl⟩ : syracuseStep 2613599 = 3920399) B3920399
theorem B2613611 : Blo 1740571 2613611 := bstep (se 1 (by rfl) ⟨1960208, by rfl⟩ : syracuseStep 2613611 = 3920417) B3920417
theorem B3137953 : Blo 1740571 3137953 := bstep (se 2 (by rfl) ⟨1176732, by rfl⟩ : syracuseStep 3137953 = 2353465) B2353465
theorem B8937965 : Blo 1740571 8937965 := bstep (se 3 (by rfl) ⟨1675868, by rfl⟩ : syracuseStep 8937965 = 3351737) B3351737
theorem B4407817 : Blo 1740571 4407817 := bstep (se 2 (by rfl) ⟨1652931, by rfl⟩ : syracuseStep 4407817 = 3305863) B3305863
theorem B28254743 : Blo 1740571 28254743 := bstep (se 1 (by rfl) ⟨21191057, by rfl⟩ : syracuseStep 28254743 = 42382115) B42382115
theorem B2613839 : Blo 1740571 2613839 := bstep (se 1 (by rfl) ⟨1960379, by rfl⟩ : syracuseStep 2613839 = 3920759) B3920759
theorem B3916385 : Blo 1740571 3916385 := bstep (se 2 (by rfl) ⟨1468644, by rfl⟩ : syracuseStep 3916385 = 2937289) B2937289
theorem B9675449 : Blo 1740571 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B3138247 : Blo 1740571 3138247 := bstep (se 1 (by rfl) ⟨2353685, by rfl⟩ : syracuseStep 3138247 = 4707371) B4707371
theorem B13222601 : Blo 1740571 13222601 := bstep (se 2 (by rfl) ⟨4958475, by rfl⟩ : syracuseStep 13222601 = 9916951) B9916951
theorem B6611665 : Blo 1740571 6611665 := bstep (se 2 (by rfl) ⟨2479374, by rfl⟩ : syracuseStep 6611665 = 4958749) B4958749
theorem B7062227 : Blo 1740571 7062227 := bstep (se 1 (by rfl) ⟨5296670, by rfl⟩ : syracuseStep 7062227 = 10593341) B10593341
theorem B5874551 : Blo 1740571 5874551 := bstep (se 1 (by rfl) ⟨4405913, by rfl⟩ : syracuseStep 5874551 = 8811827) B8811827
theorem B8053679 : Blo 1740571 8053679 := bstep (se 1 (by rfl) ⟨6040259, by rfl⟩ : syracuseStep 8053679 = 12080519) B12080519
theorem B3916727 : Blo 1740571 3916727 := bstep (se 1 (by rfl) ⟨2937545, by rfl⟩ : syracuseStep 3916727 = 5875091) B5875091
theorem B7947191 : Blo 1740571 7947191 := bstep (se 1 (by rfl) ⟨5960393, by rfl⟩ : syracuseStep 7947191 = 11920787) B11920787
theorem B12559333 : Blo 1740571 12559333 := bstep (se 4 (by rfl) ⟨1177437, by rfl⟩ : syracuseStep 12559333 = 2354875) B2354875
theorem B18359297 : Blo 1740571 18359297 := bstep (se 2 (by rfl) ⟨6884736, by rfl⟩ : syracuseStep 18359297 = 13769473) B13769473
theorem B6611969 : Blo 1740571 6611969 := bstep (se 2 (by rfl) ⟨2479488, by rfl⟩ : syracuseStep 6611969 = 4958977) B4958977
theorem B5874767 : Blo 1740571 5874767 := bstep (se 1 (by rfl) ⟨4406075, by rfl⟩ : syracuseStep 5874767 = 8812151) B8812151
theorem B5875145 : Blo 1740571 5875145 := bstep (se 2 (by rfl) ⟨2203179, by rfl⟩ : syracuseStep 5875145 = 4406359) B4406359
theorem B6612425 : Blo 1740571 6612425 := bstep (se 2 (by rfl) ⟨2479659, by rfl⟩ : syracuseStep 6612425 = 4959319) B4959319
theorem B3917321 : Blo 1740571 3917321 := bstep (se 2 (by rfl) ⟨1468995, by rfl⟩ : syracuseStep 3917321 = 2937991) B2937991
theorem B4957793 : Blo 1740571 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B1959547 : Blo 1740571 1959547 := bstep (se 1 (by rfl) ⟨1469660, by rfl⟩ : syracuseStep 1959547 = 2939321) B2939321
theorem B5580427 : Blo 1740571 5580427 := bstep (se 1 (by rfl) ⟨4185320, by rfl⟩ : syracuseStep 5580427 = 8370641) B8370641
theorem B5875415 : Blo 1740571 5875415 := bstep (se 1 (by rfl) ⟨4406561, by rfl⟩ : syracuseStep 5875415 = 8813123) B8813123
theorem B3917663 : Blo 1740571 3917663 := bstep (se 1 (by rfl) ⟨2938247, by rfl⟩ : syracuseStep 3917663 = 5876495) B5876495
theorem B28256161 : Blo 1740571 28256161 := bstep (se 2 (by rfl) ⟨10596060, by rfl⟩ : syracuseStep 28256161 = 21192121) B21192121
theorem B5875631 : Blo 1740571 5875631 := bstep (se 1 (by rfl) ⟨4406723, by rfl⟩ : syracuseStep 5875631 = 8813447) B8813447
theorem B6612911 : Blo 1740571 6612911 := bstep (se 1 (by rfl) ⟨4959683, by rfl⟩ : syracuseStep 6612911 = 9919367) B9919367
theorem B4958135 : Blo 1740571 4958135 := bstep (se 1 (by rfl) ⟨3718601, by rfl⟩ : syracuseStep 4958135 = 7437203) B7437203
theorem B4409275 : Blo 1740571 4409275 := bstep (se 1 (by rfl) ⟨3306956, by rfl⟩ : syracuseStep 4409275 = 6613913) B6613913
theorem B33458183 : Blo 1740571 33458183 := bstep (se 1 (by rfl) ⟨25093637, by rfl⟩ : syracuseStep 33458183 = 50187275) B50187275
theorem B3917843 : Blo 1740571 3917843 := bstep (se 1 (by rfl) ⟨2938382, by rfl⟩ : syracuseStep 3917843 = 5876765) B5876765
theorem B1960015 : Blo 1740571 1960015 := bstep (se 1 (by rfl) ⟨1470011, by rfl⟩ : syracuseStep 1960015 = 2940023) B2940023
theorem B19843379 : Blo 1740571 19843379 := bstep (se 1 (by rfl) ⟨14882534, by rfl⟩ : syracuseStep 19843379 = 29765069) B29765069
theorem B3918185 : Blo 1740571 3918185 := bstep (se 2 (by rfl) ⟨1469319, by rfl⟩ : syracuseStep 3918185 = 2938639) B2938639
theorem B11160467 : Blo 1740571 11160467 := bstep (se 1 (by rfl) ⟨8370350, by rfl⟩ : syracuseStep 11160467 = 16740701) B16740701
theorem B4959137 : Blo 1740571 4959137 := bstep (se 2 (by rfl) ⟨1859676, by rfl⟩ : syracuseStep 4959137 = 3719353) B3719353
theorem B9915311 : Blo 1740571 9915311 := bstep (se 1 (by rfl) ⟨7436483, by rfl⟩ : syracuseStep 9915311 = 14872967) B14872967
theorem B3918779 : Blo 1740571 3918779 := bstep (se 1 (by rfl) ⟨2939084, by rfl⟩ : syracuseStep 3918779 = 5878169) B5878169
theorem B4959251 : Blo 1740571 4959251 := bstep (se 1 (by rfl) ⟨3719438, by rfl⟩ : syracuseStep 4959251 = 7438877) B7438877
theorem B3918905 : Blo 1740571 3918905 := bstep (se 2 (by rfl) ⟨1469589, by rfl⟩ : syracuseStep 3918905 = 2939179) B2939179
theorem B6614095 : Blo 1740571 6614095 := bstep (se 1 (by rfl) ⟨4960571, by rfl⟩ : syracuseStep 6614095 = 9921143) B9921143
theorem B8367275 : Blo 1740571 8367275 := bstep (se 1 (by rfl) ⟨6275456, by rfl⟩ : syracuseStep 8367275 = 12550913) B12550913
theorem B6040747 : Blo 1740571 6040747 := bstep (se 1 (by rfl) ⟨4530560, by rfl⟩ : syracuseStep 6040747 = 9061121) B9061121
theorem B4959593 : Blo 1740571 4959593 := bstep (se 2 (by rfl) ⟨1859847, by rfl⟩ : syracuseStep 4959593 = 3719695) B3719695
theorem B3919247 : Blo 1740571 3919247 := bstep (se 1 (by rfl) ⟨2939435, by rfl⟩ : syracuseStep 3919247 = 5878871) B5878871
theorem B3304891 : Blo 1740571 3304891 := bstep (se 1 (by rfl) ⟨2478668, by rfl⟩ : syracuseStep 3304891 = 4957337) B4957337
theorem B9924059 : Blo 1740571 9924059 := bstep (se 1 (by rfl) ⟨7443044, by rfl⟩ : syracuseStep 9924059 = 14886089) B14886089
theorem B6614567 : Blo 1740571 6614567 := bstep (se 1 (by rfl) ⟨4960925, by rfl⟩ : syracuseStep 6614567 = 9921851) B9921851
theorem B14126653 : Blo 1740571 14126653 := bstep (se 3 (by rfl) ⟨2648747, by rfl⟩ : syracuseStep 14126653 = 5297495) B5297495
theorem B9924241 : Blo 1740571 9924241 := bstep (se 2 (by rfl) ⟨3721590, by rfl⟩ : syracuseStep 9924241 = 7443181) B7443181
theorem B3919571 : Blo 1740571 3919571 := bstep (se 1 (by rfl) ⟨2939678, by rfl⟩ : syracuseStep 3919571 = 5879357) B5879357
theorem B1740583 : Blo 1740571 1740583 := bstep (se 1 (by rfl) ⟨1305437, by rfl⟩ : syracuseStep 1740583 = 2610875) B2610875
theorem B1740623 : Blo 1740571 1740623 := bstep (se 1 (by rfl) ⟨1305467, by rfl⟩ : syracuseStep 1740623 = 2610935) B2610935
theorem B1740639 : Blo 1740571 1740639 := bstep (se 1 (by rfl) ⟨1305479, by rfl⟩ : syracuseStep 1740639 = 2610959) B2610959
theorem B1740667 : Blo 1740571 1740667 := bstep (se 1 (by rfl) ⟨1305500, by rfl⟩ : syracuseStep 1740667 = 2611001) B2611001
theorem B2977679 : Blo 1740571 2977679 := bstep (se 1 (by rfl) ⟨2233259, by rfl⟩ : syracuseStep 2977679 = 4466519) B4466519
theorem B3305377 : Blo 1740571 3305377 := bstep (se 2 (by rfl) ⟨1239516, by rfl⟩ : syracuseStep 3305377 = 2479033) B2479033
theorem B27545507 : Blo 1740571 27545507 := bstep (se 1 (by rfl) ⟨20659130, by rfl⟩ : syracuseStep 27545507 = 41318261) B41318261
theorem B1740719 : Blo 1740571 1740719 := bstep (se 1 (by rfl) ⟨1305539, by rfl⟩ : syracuseStep 1740719 = 2611079) B2611079
theorem B1740743 : Blo 1740571 1740743 := bstep (se 1 (by rfl) ⟨1305557, by rfl⟩ : syracuseStep 1740743 = 2611115) B2611115
theorem B1740763 : Blo 1740571 1740763 := bstep (se 1 (by rfl) ⟨1305572, by rfl⟩ : syracuseStep 1740763 = 2611145) B2611145
theorem B1740839 : Blo 1740571 1740839 := bstep (se 1 (by rfl) ⟨1305629, by rfl⟩ : syracuseStep 1740839 = 2611259) B2611259
theorem B1740879 : Blo 1740571 1740879 := bstep (se 1 (by rfl) ⟨1305659, by rfl⟩ : syracuseStep 1740879 = 2611319) B2611319
theorem B1740895 : Blo 1740571 1740895 := bstep (se 1 (by rfl) ⟨1305671, by rfl⟩ : syracuseStep 1740895 = 2611343) B2611343
theorem B1740923 : Blo 1740571 1740923 := bstep (se 1 (by rfl) ⟨1305692, by rfl⟩ : syracuseStep 1740923 = 2611385) B2611385
theorem B1740975 : Blo 1740571 1740975 := bstep (se 1 (by rfl) ⟨1305731, by rfl⟩ : syracuseStep 1740975 = 2611463) B2611463
theorem B1740999 : Blo 1740571 1740999 := bstep (se 1 (by rfl) ⟨1305749, by rfl⟩ : syracuseStep 1740999 = 2611499) B2611499
theorem B1741019 : Blo 1740571 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B5878007 : Blo 1740571 5878007 := bstep (se 1 (by rfl) ⟨4408505, by rfl⟩ : syracuseStep 5878007 = 8817011) B8817011
theorem B8818955 : Blo 1740571 8818955 := bstep (se 1 (by rfl) ⟨6614216, by rfl⟩ : syracuseStep 8818955 = 13228433) B13228433
theorem B1741095 : Blo 1740571 1741095 := bstep (se 1 (by rfl) ⟨1305821, by rfl⟩ : syracuseStep 1741095 = 2611643) B2611643
theorem B1741135 : Blo 1740571 1741135 := bstep (se 1 (by rfl) ⟨1305851, by rfl⟩ : syracuseStep 1741135 = 2611703) B2611703
theorem B1741151 : Blo 1740571 1741151 := bstep (se 1 (by rfl) ⟨1305863, by rfl⟩ : syracuseStep 1741151 = 2611727) B2611727
theorem B1741179 : Blo 1740571 1741179 := bstep (se 1 (by rfl) ⟨1305884, by rfl⟩ : syracuseStep 1741179 = 2611769) B2611769
theorem B1741231 : Blo 1740571 1741231 := bstep (se 1 (by rfl) ⟨1305923, by rfl⟩ : syracuseStep 1741231 = 2611847) B2611847
theorem B1741255 : Blo 1740571 1741255 := bstep (se 1 (by rfl) ⟨1305941, by rfl⟩ : syracuseStep 1741255 = 2611883) B2611883
theorem B1741275 : Blo 1740571 1741275 := bstep (se 1 (by rfl) ⟨1305956, by rfl⟩ : syracuseStep 1741275 = 2611913) B2611913
theorem B3305947 : Blo 1740571 3305947 := bstep (se 1 (by rfl) ⟨2479460, by rfl⟩ : syracuseStep 3305947 = 4958921) B4958921
theorem B6615539 : Blo 1740571 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B4960777 : Blo 1740571 4960777 := bstep (se 2 (by rfl) ⟨1860291, by rfl⟩ : syracuseStep 4960777 = 3720583) B3720583
theorem B1741351 : Blo 1740571 1741351 := bstep (se 1 (by rfl) ⟨1306013, by rfl⟩ : syracuseStep 1741351 = 2612027) B2612027
theorem B5878331 : Blo 1740571 5878331 := bstep (se 1 (by rfl) ⟨4408748, by rfl⟩ : syracuseStep 5878331 = 8817497) B8817497
theorem B1741391 : Blo 1740571 1741391 := bstep (se 1 (by rfl) ⟨1306043, by rfl⟩ : syracuseStep 1741391 = 2612087) B2612087
theorem B1741407 : Blo 1740571 1741407 := bstep (se 1 (by rfl) ⟨1306055, by rfl⟩ : syracuseStep 1741407 = 2612111) B2612111
theorem B1741435 : Blo 1740571 1741435 := bstep (se 1 (by rfl) ⟨1306076, by rfl⟩ : syracuseStep 1741435 = 2612153) B2612153
theorem B3920507 : Blo 1740571 3920507 := bstep (se 1 (by rfl) ⟨2940380, by rfl⟩ : syracuseStep 3920507 = 5880761) B5880761
theorem B1741487 : Blo 1740571 1741487 := bstep (se 1 (by rfl) ⟨1306115, by rfl⟩ : syracuseStep 1741487 = 2612231) B2612231
theorem B6279869 : Blo 1740571 6279869 := bstep (se 3 (by rfl) ⟨1177475, by rfl⟩ : syracuseStep 6279869 = 2354951) B2354951
theorem B1741511 : Blo 1740571 1741511 := bstep (se 1 (by rfl) ⟨1306133, by rfl⟩ : syracuseStep 1741511 = 2612267) B2612267
theorem B1741531 : Blo 1740571 1741531 := bstep (se 1 (by rfl) ⟨1306148, by rfl⟩ : syracuseStep 1741531 = 2612297) B2612297
theorem B2937593 : Blo 1740571 2937593 := bstep (se 2 (by rfl) ⟨1101597, by rfl⟩ : syracuseStep 2937593 = 2203195) B2203195
theorem B3920633 : Blo 1740571 3920633 := bstep (se 2 (by rfl) ⟨1470237, by rfl⟩ : syracuseStep 3920633 = 2940475) B2940475
theorem B1741607 : Blo 1740571 1741607 := bstep (se 1 (by rfl) ⟨1306205, by rfl⟩ : syracuseStep 1741607 = 2612411) B2612411
theorem B5878601 : Blo 1740571 5878601 := bstep (se 2 (by rfl) ⟨2204475, by rfl⟩ : syracuseStep 5878601 = 4408951) B4408951
theorem B1741647 : Blo 1740571 1741647 := bstep (se 1 (by rfl) ⟨1306235, by rfl⟩ : syracuseStep 1741647 = 2612471) B2612471
theorem B1741663 : Blo 1740571 1741663 := bstep (se 1 (by rfl) ⟨1306247, by rfl⟩ : syracuseStep 1741663 = 2612495) B2612495
theorem B1741691 : Blo 1740571 1741691 := bstep (se 1 (by rfl) ⟨1306268, by rfl⟩ : syracuseStep 1741691 = 2612537) B2612537
theorem B2937775 : Blo 1740571 2937775 := bstep (se 1 (by rfl) ⟨2203331, by rfl⟩ : syracuseStep 2937775 = 4406663) B4406663
theorem B1741743 : Blo 1740571 1741743 := bstep (se 1 (by rfl) ⟨1306307, by rfl⟩ : syracuseStep 1741743 = 2612615) B2612615
theorem B1741767 : Blo 1740571 1741767 := bstep (se 1 (by rfl) ⟨1306325, by rfl⟩ : syracuseStep 1741767 = 2612651) B2612651
theorem B1741787 : Blo 1740571 1741787 := bstep (se 1 (by rfl) ⟨1306340, by rfl⟩ : syracuseStep 1741787 = 2612681) B2612681
theorem B24146909 : Blo 1740571 24146909 := bstep (se 3 (by rfl) ⟨4527545, by rfl⟩ : syracuseStep 24146909 = 9055091) B9055091
theorem B2937863 : Blo 1740571 2937863 := bstep (se 1 (by rfl) ⟨2203397, by rfl⟩ : syracuseStep 2937863 = 4406795) B4406795
theorem B1741863 : Blo 1740571 1741863 := bstep (se 1 (by rfl) ⟨1306397, by rfl⟩ : syracuseStep 1741863 = 2612795) B2612795
theorem B14873651 : Blo 1740571 14873651 := bstep (se 1 (by rfl) ⟨11155238, by rfl⟩ : syracuseStep 14873651 = 22310477) B22310477
theorem B1741903 : Blo 1740571 1741903 := bstep (se 1 (by rfl) ⟨1306427, by rfl⟩ : syracuseStep 1741903 = 2612855) B2612855
theorem B1741919 : Blo 1740571 1741919 := bstep (se 1 (by rfl) ⟨1306439, by rfl⟩ : syracuseStep 1741919 = 2612879) B2612879
theorem B1741947 : Blo 1740571 1741947 := bstep (se 1 (by rfl) ⟨1306460, by rfl⟩ : syracuseStep 1741947 = 2612921) B2612921
theorem B1741999 : Blo 1740571 1741999 := bstep (se 1 (by rfl) ⟨1306499, by rfl⟩ : syracuseStep 1741999 = 2612999) B2612999
theorem B1742023 : Blo 1740571 1742023 := bstep (se 1 (by rfl) ⟨1306517, by rfl⟩ : syracuseStep 1742023 = 2613035) B2613035
theorem B1742043 : Blo 1740571 1742043 := bstep (se 1 (by rfl) ⟨1306532, by rfl⟩ : syracuseStep 1742043 = 2613065) B2613065
theorem B1742119 : Blo 1740571 1742119 := bstep (se 1 (by rfl) ⟨1306589, by rfl⟩ : syracuseStep 1742119 = 2613179) B2613179
theorem B1742159 : Blo 1740571 1742159 := bstep (se 1 (by rfl) ⟨1306619, by rfl⟩ : syracuseStep 1742159 = 2613239) B2613239
theorem B2938207 : Blo 1740571 2938207 := bstep (se 1 (by rfl) ⟨2203655, by rfl⟩ : syracuseStep 2938207 = 4407311) B4407311
theorem B1742175 : Blo 1740571 1742175 := bstep (se 1 (by rfl) ⟨1306631, by rfl⟩ : syracuseStep 1742175 = 2613263) B2613263
theorem B1742203 : Blo 1740571 1742203 := bstep (se 1 (by rfl) ⟨1306652, by rfl⟩ : syracuseStep 1742203 = 2613305) B2613305
theorem B4961665 : Blo 1740571 4961665 := bstep (se 2 (by rfl) ⟨1860624, by rfl⟩ : syracuseStep 4961665 = 3721249) B3721249
theorem B22328723 : Blo 1740571 22328723 := bstep (se 1 (by rfl) ⟨16746542, by rfl⟩ : syracuseStep 22328723 = 33493085) B33493085
theorem B14120365 : Blo 1740571 14120365 := bstep (se 3 (by rfl) ⟨2647568, by rfl⟩ : syracuseStep 14120365 = 5295137) B5295137
theorem B8369581 : Blo 1740571 8369581 := bstep (se 3 (by rfl) ⟨1569296, by rfl⟩ : syracuseStep 8369581 = 3138593) B3138593
theorem B1742255 : Blo 1740571 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B2938295 : Blo 1740571 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B1742279 : Blo 1740571 1742279 := bstep (se 1 (by rfl) ⟨1306709, by rfl⟩ : syracuseStep 1742279 = 2613419) B2613419
theorem B1742299 : Blo 1740571 1742299 := bstep (se 1 (by rfl) ⟨1306724, by rfl⟩ : syracuseStep 1742299 = 2613449) B2613449
theorem B1742375 : Blo 1740571 1742375 := bstep (se 1 (by rfl) ⟨1306781, by rfl⟩ : syracuseStep 1742375 = 2613563) B2613563
theorem B1742415 : Blo 1740571 1742415 := bstep (se 1 (by rfl) ⟨1306811, by rfl⟩ : syracuseStep 1742415 = 2613623) B2613623
theorem B1742431 : Blo 1740571 1742431 := bstep (se 1 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 1742431 = 2613647) B2613647
theorem B2479739 : Blo 1740571 2479739 := bstep (se 1 (by rfl) ⟨1859804, by rfl⟩ : syracuseStep 2479739 = 3719609) B3719609
theorem B1742459 : Blo 1740571 1742459 := bstep (se 1 (by rfl) ⟨1306844, by rfl⟩ : syracuseStep 1742459 = 2613689) B2613689
theorem B5576327 : Blo 1740571 5576327 := bstep (se 1 (by rfl) ⟨4182245, by rfl⟩ : syracuseStep 5576327 = 8364491) B8364491
theorem B1742511 : Blo 1740571 1742511 := bstep (se 1 (by rfl) ⟨1306883, by rfl⟩ : syracuseStep 1742511 = 2613767) B2613767
theorem B8820413 : Blo 1740571 8820413 := bstep (se 3 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 8820413 = 3307655) B3307655
theorem B2610887 : Blo 1740571 2610887 := bstep (se 1 (by rfl) ⟨1958165, by rfl⟩ : syracuseStep 2610887 = 3916331) B3916331
theorem B1742535 : Blo 1740571 1742535 := bstep (se 1 (by rfl) ⟨1306901, by rfl⟩ : syracuseStep 1742535 = 2613803) B2613803
theorem B1742555 : Blo 1740571 1742555 := bstep (se 1 (by rfl) ⟨1306916, by rfl⟩ : syracuseStep 1742555 = 2613833) B2613833
theorem B3970889 : Blo 1740571 3970889 := bstep (se 2 (by rfl) ⟨1489083, by rfl⟩ : syracuseStep 3970889 = 2978167) B2978167
theorem B6608735 : Blo 1740571 6608735 := bstep (se 1 (by rfl) ⟨4956551, by rfl⟩ : syracuseStep 6608735 = 9913103) B9913103
theorem B5576543 : Blo 1740571 5576543 := bstep (se 1 (by rfl) ⟨4182407, by rfl⟩ : syracuseStep 5576543 = 8364815) B8364815
theorem B8820575 : Blo 1740571 8820575 := bstep (se 1 (by rfl) ⟨6615431, by rfl⟩ : syracuseStep 8820575 = 13230863) B13230863
theorem B2611049 : Blo 1740571 2611049 := bstep (se 2 (by rfl) ⟨979143, by rfl⟩ : syracuseStep 2611049 = 1958287) B1958287
theorem B6608749 : Blo 1740571 6608749 := bstep (se 3 (by rfl) ⟨1239140, by rfl⟩ : syracuseStep 6608749 = 2478281) B2478281
theorem B11155319 : Blo 1740571 11155319 := bstep (se 1 (by rfl) ⟨8366489, by rfl⟩ : syracuseStep 11155319 = 16732979) B16732979
theorem B2611127 : Blo 1740571 2611127 := bstep (se 1 (by rfl) ⟨1958345, by rfl⟩ : syracuseStep 2611127 = 3916691) B3916691
theorem B5879735 : Blo 1740571 5879735 := bstep (se 1 (by rfl) ⟨4409801, by rfl⟩ : syracuseStep 5879735 = 8819603) B8819603
theorem B12556217 : Blo 1740571 12556217 := bstep (se 2 (by rfl) ⟨4708581, by rfl⟩ : syracuseStep 12556217 = 9417163) B9417163
theorem B8812475 : Blo 1740571 8812475 := bstep (se 1 (by rfl) ⟨6609356, by rfl⟩ : syracuseStep 8812475 = 13218713) B13218713
theorem B4962235 : Blo 1740571 4962235 := bstep (se 1 (by rfl) ⟨3721676, by rfl⟩ : syracuseStep 4962235 = 7443353) B7443353
theorem B44627921 : Blo 1740571 44627921 := bstep (se 2 (by rfl) ⟨16735470, by rfl⟩ : syracuseStep 44627921 = 33470941) B33470941
theorem B2611163 : Blo 1740571 2611163 := bstep (se 1 (by rfl) ⟨1958372, by rfl⟩ : syracuseStep 2611163 = 3916745) B3916745
theorem B2938889 : Blo 1740571 2938889 := bstep (se 2 (by rfl) ⟨1102083, by rfl⟩ : syracuseStep 2938889 = 2204167) B2204167
theorem B28629049 : Blo 1740571 28629049 := bstep (se 2 (by rfl) ⟨10735893, by rfl⟩ : syracuseStep 28629049 = 21471787) B21471787
theorem B6609053 : Blo 1740571 6609053 := bstep (se 3 (by rfl) ⟨1239197, by rfl⟩ : syracuseStep 6609053 = 2478395) B2478395
theorem B2939051 : Blo 1740571 2939051 := bstep (se 1 (by rfl) ⟨2204288, by rfl⟩ : syracuseStep 2939051 = 4408577) B4408577
theorem B25106669 : Blo 1740571 25106669 := bstep (se 3 (by rfl) ⟨4707500, by rfl⟩ : syracuseStep 25106669 = 9415001) B9415001
theorem B2480377 : Blo 1740571 2480377 := bstep (se 2 (by rfl) ⟨930141, by rfl⟩ : syracuseStep 2480377 = 1860283) B1860283
theorem B2480491 : Blo 1740571 2480491 := bstep (se 1 (by rfl) ⟨1860368, by rfl⟩ : syracuseStep 2480491 = 3720737) B3720737
theorem B11917721 : Blo 1740571 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B2611631 : Blo 1740571 2611631 := bstep (se 1 (by rfl) ⟨1958723, by rfl⟩ : syracuseStep 2611631 = 3917447) B3917447
theorem B2611721 : Blo 1740571 2611721 := bstep (se 2 (by rfl) ⟨979395, by rfl⟩ : syracuseStep 2611721 = 1958791) B1958791
theorem B8370697 : Blo 1740571 8370697 := bstep (se 2 (by rfl) ⟨3139011, by rfl⟩ : syracuseStep 8370697 = 6278023) B6278023
theorem B5880329 : Blo 1740571 5880329 := bstep (se 2 (by rfl) ⟨2205123, by rfl⟩ : syracuseStep 5880329 = 4410247) B4410247
theorem B2611751 : Blo 1740571 2611751 := bstep (se 1 (by rfl) ⟨1958813, by rfl⟩ : syracuseStep 2611751 = 3917627) B3917627
theorem B2939449 : Blo 1740571 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B2480719 : Blo 1740571 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B3308111 : Blo 1740571 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B2611835 : Blo 1740571 2611835 := bstep (se 1 (by rfl) ⟨1958876, by rfl⟩ : syracuseStep 2611835 = 3917753) B3917753
theorem B2939591 : Blo 1740571 2939591 := bstep (se 1 (by rfl) ⟨2204693, by rfl⟩ : syracuseStep 2939591 = 4409387) B4409387
theorem B2611961 : Blo 1740571 2611961 := bstep (se 2 (by rfl) ⟨979485, by rfl⟩ : syracuseStep 2611961 = 1958971) B1958971
theorem B6609707 : Blo 1740571 6609707 := bstep (se 1 (by rfl) ⟨4957280, by rfl⟩ : syracuseStep 6609707 = 9914561) B9914561
theorem B2612063 : Blo 1740571 2612063 := bstep (se 1 (by rfl) ⟨1959047, by rfl⟩ : syracuseStep 2612063 = 3918095) B3918095
theorem B2939753 : Blo 1740571 2939753 := bstep (se 2 (by rfl) ⟨1102407, by rfl⟩ : syracuseStep 2939753 = 2204815) B2204815
theorem B2612075 : Blo 1740571 2612075 := bstep (se 1 (by rfl) ⟨1959056, by rfl⟩ : syracuseStep 2612075 = 3918113) B3918113
theorem B4406177 : Blo 1740571 4406177 := bstep (se 2 (by rfl) ⟨1652316, by rfl⟩ : syracuseStep 4406177 = 3304633) B3304633
theorem B2612303 : Blo 1740571 2612303 := bstep (se 1 (by rfl) ⟨1959227, by rfl⟩ : syracuseStep 2612303 = 3918455) B3918455
theorem B6274219 : Blo 1740571 6274219 := bstep (se 1 (by rfl) ⟨4705664, by rfl⟩ : syracuseStep 6274219 = 9411329) B9411329
theorem B2612423 : Blo 1740571 2612423 := bstep (se 1 (by rfl) ⟨1959317, by rfl⟩ : syracuseStep 2612423 = 3918635) B3918635
theorem B8813771 : Blo 1740571 8813771 := bstep (se 1 (by rfl) ⟨6610328, by rfl⟩ : syracuseStep 8813771 = 13220657) B13220657
theorem B50879735 : Blo 1740571 50879735 := bstep (se 1 (by rfl) ⟨38159801, by rfl⟩ : syracuseStep 50879735 = 76319603) B76319603
theorem B2940151 : Blo 1740571 2940151 := bstep (se 1 (by rfl) ⟨2205113, by rfl⟩ : syracuseStep 2940151 = 4410227) B4410227
theorem B13221143 : Blo 1740571 13221143 := bstep (se 1 (by rfl) ⟨9915857, by rfl⟩ : syracuseStep 13221143 = 19831715) B19831715
theorem B4406633 : Blo 1740571 4406633 := bstep (se 2 (by rfl) ⟨1652487, by rfl⟩ : syracuseStep 4406633 = 3304975) B3304975
theorem B2612585 : Blo 1740571 2612585 := bstep (se 2 (by rfl) ⟨979719, by rfl⟩ : syracuseStep 2612585 = 1959439) B1959439
theorem B11156879 : Blo 1740571 11156879 := bstep (se 1 (by rfl) ⟨8367659, by rfl⟩ : syracuseStep 11156879 = 16735319) B16735319
theorem B2612663 : Blo 1740571 2612663 := bstep (se 1 (by rfl) ⟨1959497, by rfl⟩ : syracuseStep 2612663 = 3918995) B3918995
theorem B2940347 : Blo 1740571 2940347 := bstep (se 1 (by rfl) ⟨2205260, by rfl⟩ : syracuseStep 2940347 = 4410521) B4410521
theorem B2612699 : Blo 1740571 2612699 := bstep (se 1 (by rfl) ⟨1959524, by rfl⟩ : syracuseStep 2612699 = 3919049) B3919049
theorem B2940455 : Blo 1740571 2940455 := bstep (se 1 (by rfl) ⟨2205341, by rfl⟩ : syracuseStep 2940455 = 4410683) B4410683
theorem B8371927 : Blo 1740571 8371927 := bstep (se 1 (by rfl) ⟨6278945, by rfl⟩ : syracuseStep 8371927 = 12557891) B12557891
theorem B7061315 : Blo 1740571 7061315 := bstep (se 1 (by rfl) ⟨5295986, by rfl⟩ : syracuseStep 7061315 = 10591973) B10591973
theorem B13229891 : Blo 1740571 13229891 := bstep (se 1 (by rfl) ⟨9922418, by rfl⟩ : syracuseStep 13229891 = 19844837) B19844837
theorem B418234211 : Blo 1740571 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B2613167 : Blo 1740571 2613167 := bstep (se 1 (by rfl) ⟨1959875, by rfl⟩ : syracuseStep 2613167 = 3919751) B3919751
theorem B7061431 : Blo 1740571 7061431 := bstep (se 1 (by rfl) ⟨5296073, by rfl⟩ : syracuseStep 7061431 = 10592147) B10592147
theorem B47661155 : Blo 1740571 47661155 := bstep (se 1 (by rfl) ⟨35745866, by rfl⟩ : syracuseStep 47661155 = 71491733) B71491733
theorem B2613353 : Blo 1740571 2613353 := bstep (se 2 (by rfl) ⟨980007, by rfl⟩ : syracuseStep 2613353 = 1960015) B1960015
theorem B25100441 : Blo 1740571 25100441 := bstep (se 2 (by rfl) ⟨9412665, by rfl⟩ : syracuseStep 25100441 = 18825331) B18825331
theorem B75342149 : Blo 1740571 75342149 := bstep (se 4 (by rfl) ⟨7063326, by rfl⟩ : syracuseStep 75342149 = 14126653) B14126653
theorem B2613671 : Blo 1740571 2613671 := bstep (se 1 (by rfl) ⟨1960253, by rfl⟩ : syracuseStep 2613671 = 3920507) B3920507
theorem B4186579 : Blo 1740571 4186579 := bstep (se 1 (by rfl) ⟨3139934, by rfl⟩ : syracuseStep 4186579 = 6279869) B6279869
theorem B8815067 : Blo 1740571 8815067 := bstep (se 1 (by rfl) ⟨6611300, by rfl⟩ : syracuseStep 8815067 = 13222601) B13222601
theorem B1958395 : Blo 1740571 1958395 := bstep (se 1 (by rfl) ⟨1468796, by rfl⟩ : syracuseStep 1958395 = 2937593) B2937593
theorem B2613755 : Blo 1740571 2613755 := bstep (se 1 (by rfl) ⟨1960316, by rfl⟩ : syracuseStep 2613755 = 3920633) B3920633
theorem B3916367 : Blo 1740571 3916367 := bstep (se 1 (by rfl) ⟨2937275, by rfl⟩ : syracuseStep 3916367 = 5874551) B5874551
theorem B4407929 : Blo 1740571 4407929 := bstep (se 2 (by rfl) ⟨1652973, by rfl⟩ : syracuseStep 4407929 = 3305947) B3305947
theorem B16097939 : Blo 1740571 16097939 := bstep (se 1 (by rfl) ⟨12073454, by rfl⟩ : syracuseStep 16097939 = 24146909) B24146909
theorem B12239531 : Blo 1740571 12239531 := bstep (se 1 (by rfl) ⟨9179648, by rfl⟩ : syracuseStep 12239531 = 18359297) B18359297
theorem B4407979 : Blo 1740571 4407979 := bstep (se 1 (by rfl) ⟨3305984, by rfl⟩ : syracuseStep 4407979 = 6611969) B6611969
theorem B1958575 : Blo 1740571 1958575 := bstep (se 1 (by rfl) ⟨1468931, by rfl⟩ : syracuseStep 1958575 = 2937863) B2937863
theorem B3916511 : Blo 1740571 3916511 := bstep (se 1 (by rfl) ⟨2937383, by rfl⟩ : syracuseStep 3916511 = 5874767) B5874767
theorem B14885815 : Blo 1740571 14885815 := bstep (se 1 (by rfl) ⟨11164361, by rfl⟩ : syracuseStep 14885815 = 22328723) B22328723
theorem B8815553 : Blo 1740571 8815553 := bstep (se 2 (by rfl) ⟨3305832, by rfl⟩ : syracuseStep 8815553 = 6611665) B6611665
theorem B1958863 : Blo 1740571 1958863 := bstep (se 1 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 1958863 = 2938295) B2938295
theorem B3916763 : Blo 1740571 3916763 := bstep (se 1 (by rfl) ⟨2937572, by rfl⟩ : syracuseStep 3916763 = 5875145) B5875145
theorem B4408283 : Blo 1740571 4408283 := bstep (se 1 (by rfl) ⟨3306212, by rfl⟩ : syracuseStep 4408283 = 6612425) B6612425
theorem B16737317 : Blo 1740571 16737317 := bstep (se 4 (by rfl) ⟨1569123, by rfl⟩ : syracuseStep 16737317 = 3138247) B3138247
theorem B3916943 : Blo 1740571 3916943 := bstep (se 1 (by rfl) ⟨2937707, by rfl⟩ : syracuseStep 3916943 = 5875415) B5875415
theorem B2647259 : Blo 1740571 2647259 := bstep (se 1 (by rfl) ⟨1985444, by rfl⟩ : syracuseStep 2647259 = 3970889) B3970889
theorem B3917033 : Blo 1740571 3917033 := bstep (se 2 (by rfl) ⟨1468887, by rfl⟩ : syracuseStep 3917033 = 2937775) B2937775
theorem B3917087 : Blo 1740571 3917087 := bstep (se 1 (by rfl) ⟨2937815, by rfl⟩ : syracuseStep 3917087 = 5875631) B5875631
theorem B4408607 : Blo 1740571 4408607 := bstep (se 1 (by rfl) ⟨3306455, by rfl⟩ : syracuseStep 4408607 = 6612911) B6612911
theorem B5874983 : Blo 1740571 5874983 := bstep (se 1 (by rfl) ⟨4406237, by rfl⟩ : syracuseStep 5874983 = 8812475) B8812475
theorem B16745777 : Blo 1740571 16745777 := bstep (se 2 (by rfl) ⟨6279666, by rfl⟩ : syracuseStep 16745777 = 12559333) B12559333
theorem B1959259 : Blo 1740571 1959259 := bstep (se 1 (by rfl) ⟨1469444, by rfl⟩ : syracuseStep 1959259 = 2938889) B2938889
theorem B1959367 : Blo 1740571 1959367 := bstep (se 1 (by rfl) ⟨1469525, by rfl⟩ : syracuseStep 1959367 = 2939051) B2939051
theorem B16737779 : Blo 1740571 16737779 := bstep (se 1 (by rfl) ⟨12553334, by rfl⟩ : syracuseStep 16737779 = 25106669) B25106669
theorem B8365625 : Blo 1740571 8365625 := bstep (se 2 (by rfl) ⟨3137109, by rfl⟩ : syracuseStep 8365625 = 6274219) B6274219
theorem B8054329 : Blo 1740571 8054329 := bstep (se 2 (by rfl) ⟨3020373, by rfl⟩ : syracuseStep 8054329 = 6040747) B6040747
theorem B6612637 : Blo 1740571 6612637 := bstep (se 3 (by rfl) ⟨1239869, by rfl⟩ : syracuseStep 6612637 = 2479739) B2479739
theorem B2205407 : Blo 1740571 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B3917609 : Blo 1740571 3917609 := bstep (se 2 (by rfl) ⟨1469103, by rfl⟩ : syracuseStep 3917609 = 2938207) B2938207
theorem B1959727 : Blo 1740571 1959727 := bstep (se 1 (by rfl) ⟨1469795, by rfl⟩ : syracuseStep 1959727 = 2939591) B2939591
theorem B18827153 : Blo 1740571 18827153 := bstep (se 2 (by rfl) ⟨7060182, by rfl⟩ : syracuseStep 18827153 = 14120365) B14120365
theorem B11159441 : Blo 1740571 11159441 := bstep (se 2 (by rfl) ⟨4184790, by rfl⟩ : syracuseStep 11159441 = 8369581) B8369581
theorem B1959835 : Blo 1740571 1959835 := bstep (se 1 (by rfl) ⟨1469876, by rfl⟩ : syracuseStep 1959835 = 2939753) B2939753
theorem B7440311 : Blo 1740571 7440311 := bstep (se 1 (by rfl) ⟨5580233, by rfl⟩ : syracuseStep 7440311 = 11160467) B11160467
theorem B5875847 : Blo 1740571 5875847 := bstep (se 1 (by rfl) ⟨4406885, by rfl⟩ : syracuseStep 5875847 = 8813771) B8813771
theorem B7440569 : Blo 1740571 7440569 := bstep (se 2 (by rfl) ⟨2790213, by rfl⟩ : syracuseStep 7440569 = 5580427) B5580427
theorem B13232321 : Blo 1740571 13232321 := bstep (se 2 (by rfl) ⟨4962120, by rfl⟩ : syracuseStep 13232321 = 9924241) B9924241
theorem B1960231 : Blo 1740571 1960231 := bstep (se 1 (by rfl) ⟨1470173, by rfl⟩ : syracuseStep 1960231 = 2940347) B2940347
theorem B4409711 : Blo 1740571 4409711 := bstep (se 1 (by rfl) ⟨3307283, by rfl⟩ : syracuseStep 4409711 = 6614567) B6614567
theorem B1960303 : Blo 1740571 1960303 := bstep (se 1 (by rfl) ⟨1470227, by rfl⟩ : syracuseStep 1960303 = 2940455) B2940455
theorem B9415241 : Blo 1740571 9415241 := bstep (se 2 (by rfl) ⟨3530715, by rfl⟩ : syracuseStep 9415241 = 7061431) B7061431
theorem B1985119 : Blo 1740571 1985119 := bstep (se 1 (by rfl) ⟨1488839, by rfl⟩ : syracuseStep 1985119 = 2977679) B2977679
theorem B28240595 : Blo 1740571 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B3918671 : Blo 1740571 3918671 := bstep (se 1 (by rfl) ⟨2939003, by rfl⟩ : syracuseStep 3918671 = 5878007) B5878007
theorem B5958643 : Blo 1740571 5958643 := bstep (se 1 (by rfl) ⟨4468982, by rfl⟩ : syracuseStep 5958643 = 8937965) B8937965
theorem B4410359 : Blo 1740571 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B18836495 : Blo 1740571 18836495 := bstep (se 1 (by rfl) ⟨14127371, by rfl⟩ : syracuseStep 18836495 = 28254743) B28254743
theorem B3918887 : Blo 1740571 3918887 := bstep (se 1 (by rfl) ⟨2939165, by rfl⟩ : syracuseStep 3918887 = 5878331) B5878331
theorem B6450299 : Blo 1740571 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B3919067 : Blo 1740571 3919067 := bstep (se 1 (by rfl) ⟨2939300, by rfl⟩ : syracuseStep 3919067 = 5878601) B5878601
theorem B5877089 : Blo 1740571 5877089 := bstep (se 2 (by rfl) ⟨2203908, by rfl⟩ : syracuseStep 5877089 = 4407817) B4407817
theorem B11160929 : Blo 1740571 11160929 := bstep (se 2 (by rfl) ⟨4185348, by rfl⟩ : syracuseStep 11160929 = 8370697) B8370697
theorem B6614369 : Blo 1740571 6614369 := bstep (se 2 (by rfl) ⟨2480388, by rfl⟩ : syracuseStep 6614369 = 4960777) B4960777
theorem B9915767 : Blo 1740571 9915767 := bstep (se 1 (by rfl) ⟨7436825, by rfl⟩ : syracuseStep 9915767 = 14873651) B14873651
theorem B3919265 : Blo 1740571 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B3305195 : Blo 1740571 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B1740591 : Blo 1740571 1740591 := bstep (se 1 (by rfl) ⟨1305443, by rfl⟩ : syracuseStep 1740591 = 2610887) B2610887
theorem B1740699 : Blo 1740571 1740699 := bstep (se 1 (by rfl) ⟨1305524, by rfl⟩ : syracuseStep 1740699 = 2611049) B2611049
theorem B1740751 : Blo 1740571 1740751 := bstep (se 1 (by rfl) ⟨1305563, by rfl⟩ : syracuseStep 1740751 = 2611127) B2611127
theorem B3305423 : Blo 1740571 3305423 := bstep (se 1 (by rfl) ⟨2479067, by rfl⟩ : syracuseStep 3305423 = 4958135) B4958135
theorem B3919823 : Blo 1740571 3919823 := bstep (se 1 (by rfl) ⟨2939867, by rfl⟩ : syracuseStep 3919823 = 5879735) B5879735
theorem B1740775 : Blo 1740571 1740775 := bstep (se 1 (by rfl) ⟨1305581, by rfl⟩ : syracuseStep 1740775 = 2611163) B2611163
theorem B8818793 : Blo 1740571 8818793 := bstep (se 2 (by rfl) ⟨3307047, by rfl⟩ : syracuseStep 8818793 = 6614095) B6614095
theorem B1741087 : Blo 1740571 1741087 := bstep (se 1 (by rfl) ⟨1305815, by rfl⟩ : syracuseStep 1741087 = 2611631) B2611631
theorem B3920201 : Blo 1740571 3920201 := bstep (se 2 (by rfl) ⟨1470075, by rfl⟩ : syracuseStep 3920201 = 2940151) B2940151
theorem B1741147 : Blo 1740571 1741147 := bstep (se 1 (by rfl) ⟨1305860, by rfl⟩ : syracuseStep 1741147 = 2611721) B2611721
theorem B3920219 : Blo 1740571 3920219 := bstep (se 1 (by rfl) ⟨2940164, by rfl⟩ : syracuseStep 3920219 = 5880329) B5880329
theorem B1741167 : Blo 1740571 1741167 := bstep (se 1 (by rfl) ⟨1305875, by rfl⟩ : syracuseStep 1741167 = 2611751) B2611751
theorem B1741223 : Blo 1740571 1741223 := bstep (se 1 (by rfl) ⟨1305917, by rfl⟩ : syracuseStep 1741223 = 2611835) B2611835
theorem B1741307 : Blo 1740571 1741307 := bstep (se 1 (by rfl) ⟨1305980, by rfl⟩ : syracuseStep 1741307 = 2611961) B2611961
theorem B6615553 : Blo 1740571 6615553 := bstep (se 2 (by rfl) ⟨2480832, by rfl⟩ : syracuseStep 6615553 = 4961665) B4961665
theorem B1741375 : Blo 1740571 1741375 := bstep (se 1 (by rfl) ⟨1306031, by rfl⟩ : syracuseStep 1741375 = 2612063) B2612063
theorem B1741383 : Blo 1740571 1741383 := bstep (se 1 (by rfl) ⟨1306037, by rfl⟩ : syracuseStep 1741383 = 2612075) B2612075
theorem B2937451 : Blo 1740571 2937451 := bstep (se 1 (by rfl) ⟨2203088, by rfl⟩ : syracuseStep 2937451 = 4406177) B4406177
theorem B3306091 : Blo 1740571 3306091 := bstep (se 1 (by rfl) ⟨2479568, by rfl⟩ : syracuseStep 3306091 = 4959137) B4959137
theorem B3306167 : Blo 1740571 3306167 := bstep (se 1 (by rfl) ⟨2479625, by rfl⟩ : syracuseStep 3306167 = 4959251) B4959251
theorem B1741535 : Blo 1740571 1741535 := bstep (se 1 (by rfl) ⟨1306151, by rfl⟩ : syracuseStep 1741535 = 2612303) B2612303
theorem B1741615 : Blo 1740571 1741615 := bstep (se 1 (by rfl) ⟨1306211, by rfl⟩ : syracuseStep 1741615 = 2612423) B2612423
theorem B33919823 : Blo 1740571 33919823 := bstep (se 1 (by rfl) ⟨25439867, by rfl⟩ : syracuseStep 33919823 = 50879735) B50879735
theorem B18830173 : Blo 1740571 18830173 := bstep (se 3 (by rfl) ⟨3530657, by rfl⟩ : syracuseStep 18830173 = 7061315) B7061315
theorem B2937755 : Blo 1740571 2937755 := bstep (se 1 (by rfl) ⟨2203316, by rfl⟩ : syracuseStep 2937755 = 4406633) B4406633
theorem B3306395 : Blo 1740571 3306395 := bstep (se 1 (by rfl) ⟨2479796, by rfl⟩ : syracuseStep 3306395 = 4959593) B4959593
theorem B1741723 : Blo 1740571 1741723 := bstep (se 1 (by rfl) ⟨1306292, by rfl⟩ : syracuseStep 1741723 = 2612585) B2612585
theorem B11162569 : Blo 1740571 11162569 := bstep (se 2 (by rfl) ⟨4185963, by rfl⟩ : syracuseStep 11162569 = 8371927) B8371927
theorem B1741775 : Blo 1740571 1741775 := bstep (se 1 (by rfl) ⟨1306331, by rfl⟩ : syracuseStep 1741775 = 2612663) B2612663
theorem B1741799 : Blo 1740571 1741799 := bstep (se 1 (by rfl) ⟨1306349, by rfl⟩ : syracuseStep 1741799 = 2612699) B2612699
theorem B6616039 : Blo 1740571 6616039 := bstep (se 1 (by rfl) ⟨4962029, by rfl⟩ : syracuseStep 6616039 = 9924059) B9924059
theorem B21476477 : Blo 1740571 21476477 := bstep (se 3 (by rfl) ⟨4026839, by rfl⟩ : syracuseStep 21476477 = 8053679) B8053679
theorem B8811665 : Blo 1740571 8811665 := bstep (se 2 (by rfl) ⟨3304374, by rfl⟩ : syracuseStep 8811665 = 6608749) B6608749
theorem B8819927 : Blo 1740571 8819927 := bstep (se 1 (by rfl) ⟨6614945, by rfl⟩ : syracuseStep 8819927 = 13229891) B13229891
theorem B5879033 : Blo 1740571 5879033 := bstep (se 2 (by rfl) ⟨2204637, by rfl⟩ : syracuseStep 5879033 = 4409275) B4409275
theorem B6616313 : Blo 1740571 6616313 := bstep (se 2 (by rfl) ⟨2481117, by rfl⟩ : syracuseStep 6616313 = 4962235) B4962235
theorem B18363671 : Blo 1740571 18363671 := bstep (se 1 (by rfl) ⟨13772753, by rfl⟩ : syracuseStep 18363671 = 27545507) B27545507
theorem B1742111 : Blo 1740571 1742111 := bstep (se 1 (by rfl) ⟨1306583, by rfl⟩ : syracuseStep 1742111 = 2613167) B2613167
theorem B1742171 : Blo 1740571 1742171 := bstep (se 1 (by rfl) ⟨1306628, by rfl⟩ : syracuseStep 1742171 = 2613257) B2613257
theorem B1742191 : Blo 1740571 1742191 := bstep (se 1 (by rfl) ⟨1306643, by rfl⟩ : syracuseStep 1742191 = 2613287) B2613287
theorem B38172065 : Blo 1740571 38172065 := bstep (se 2 (by rfl) ⟨14314524, by rfl⟩ : syracuseStep 38172065 = 28629049) B28629049
theorem B1742247 : Blo 1740571 1742247 := bstep (se 1 (by rfl) ⟨1306685, by rfl⟩ : syracuseStep 1742247 = 2613371) B2613371
theorem B1742331 : Blo 1740571 1742331 := bstep (se 1 (by rfl) ⟨1306748, by rfl⟩ : syracuseStep 1742331 = 2613497) B2613497
theorem B5879303 : Blo 1740571 5879303 := bstep (se 1 (by rfl) ⟨4409477, by rfl⟩ : syracuseStep 5879303 = 8818955) B8818955
theorem B1742399 : Blo 1740571 1742399 := bstep (se 1 (by rfl) ⟨1306799, by rfl⟩ : syracuseStep 1742399 = 2613599) B2613599
theorem B1742407 : Blo 1740571 1742407 := bstep (se 1 (by rfl) ⟨1306805, by rfl⟩ : syracuseStep 1742407 = 2613611) B2613611
theorem B3307169 : Blo 1740571 3307169 := bstep (se 2 (by rfl) ⟨1240188, by rfl⟩ : syracuseStep 3307169 = 2480377) B2480377
theorem B1742559 : Blo 1740571 1742559 := bstep (se 1 (by rfl) ⟨1306919, by rfl⟩ : syracuseStep 1742559 = 2613839) B2613839
theorem B2610923 : Blo 1740571 2610923 := bstep (se 1 (by rfl) ⟨1958192, by rfl⟩ : syracuseStep 2610923 = 3916385) B3916385
theorem B4708151 : Blo 1740571 4708151 := bstep (se 1 (by rfl) ⟨3531113, by rfl⟩ : syracuseStep 4708151 = 7062227) B7062227
theorem B3307321 : Blo 1740571 3307321 := bstep (se 2 (by rfl) ⟨1240245, by rfl⟩ : syracuseStep 3307321 = 2480491) B2480491
theorem B4183937 : Blo 1740571 4183937 := bstep (se 2 (by rfl) ⟨1568976, by rfl⟩ : syracuseStep 4183937 = 3137953) B3137953
theorem B2611151 : Blo 1740571 2611151 := bstep (se 1 (by rfl) ⟨1958363, by rfl⟩ : syracuseStep 2611151 = 3916727) B3916727
theorem B3307625 : Blo 1740571 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B2611547 : Blo 1740571 2611547 := bstep (se 1 (by rfl) ⟨1958660, by rfl⟩ : syracuseStep 2611547 = 3917321) B3917321
theorem B3717551 : Blo 1740571 3717551 := bstep (se 1 (by rfl) ⟨2788163, by rfl⟩ : syracuseStep 3717551 = 5576327) B5576327
theorem B5880275 : Blo 1740571 5880275 := bstep (se 1 (by rfl) ⟨4410206, by rfl⟩ : syracuseStep 5880275 = 8820413) B8820413
theorem B4405823 : Blo 1740571 4405823 := bstep (se 1 (by rfl) ⟨3304367, by rfl⟩ : syracuseStep 4405823 = 6608735) B6608735
theorem B3717695 : Blo 1740571 3717695 := bstep (se 1 (by rfl) ⟨2788271, by rfl⟩ : syracuseStep 3717695 = 5576543) B5576543
theorem B2611775 : Blo 1740571 2611775 := bstep (se 1 (by rfl) ⟨1958831, by rfl⟩ : syracuseStep 2611775 = 3917663) B3917663
theorem B5880383 : Blo 1740571 5880383 := bstep (se 1 (by rfl) ⟨4410287, by rfl⟩ : syracuseStep 5880383 = 8820575) B8820575
theorem B7436879 : Blo 1740571 7436879 := bstep (se 1 (by rfl) ⟨5577659, by rfl⟩ : syracuseStep 7436879 = 11155319) B11155319
theorem B8370811 : Blo 1740571 8370811 := bstep (se 1 (by rfl) ⟨6278108, by rfl⟩ : syracuseStep 8370811 = 12556217) B12556217
theorem B29751947 : Blo 1740571 29751947 := bstep (se 1 (by rfl) ⟨22313960, by rfl⟩ : syracuseStep 29751947 = 44627921) B44627921
theorem B22305455 : Blo 1740571 22305455 := bstep (se 1 (by rfl) ⟨16729091, by rfl⟩ : syracuseStep 22305455 = 33458183) B33458183
theorem B2611895 : Blo 1740571 2611895 := bstep (se 1 (by rfl) ⟨1958921, by rfl⟩ : syracuseStep 2611895 = 3917843) B3917843
theorem B4406035 : Blo 1740571 4406035 := bstep (se 1 (by rfl) ⟨3304526, by rfl⟩ : syracuseStep 4406035 = 6609053) B6609053
theorem B13228919 : Blo 1740571 13228919 := bstep (se 1 (by rfl) ⟨9921689, by rfl⟩ : syracuseStep 13228919 = 19843379) B19843379
theorem B2612123 : Blo 1740571 2612123 := bstep (se 1 (by rfl) ⟨1959092, by rfl⟩ : syracuseStep 2612123 = 3918185) B3918185
theorem B7945147 : Blo 1740571 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B4406471 : Blo 1740571 4406471 := bstep (se 1 (by rfl) ⟨3304853, by rfl⟩ : syracuseStep 4406471 = 6609707) B6609707
theorem B4406521 : Blo 1740571 4406521 := bstep (se 2 (by rfl) ⟨1652445, by rfl⟩ : syracuseStep 4406521 = 3304891) B3304891
theorem B6610207 : Blo 1740571 6610207 := bstep (se 1 (by rfl) ⟨4957655, by rfl⟩ : syracuseStep 6610207 = 9915311) B9915311
theorem B2612519 : Blo 1740571 2612519 := bstep (se 1 (by rfl) ⟨1959389, by rfl⟩ : syracuseStep 2612519 = 3918779) B3918779
theorem B2612603 : Blo 1740571 2612603 := bstep (se 1 (by rfl) ⟨1959452, by rfl⟩ : syracuseStep 2612603 = 3918905) B3918905
theorem B5578183 : Blo 1740571 5578183 := bstep (se 1 (by rfl) ⟨4183637, by rfl⟩ : syracuseStep 5578183 = 8367275) B8367275
theorem B2612729 : Blo 1740571 2612729 := bstep (se 2 (by rfl) ⟨979773, by rfl⟩ : syracuseStep 2612729 = 1959547) B1959547
theorem B8814095 : Blo 1740571 8814095 := bstep (se 1 (by rfl) ⟨6610571, by rfl⟩ : syracuseStep 8814095 = 13221143) B13221143
theorem B7437919 : Blo 1740571 7437919 := bstep (se 1 (by rfl) ⟨5578439, by rfl⟩ : syracuseStep 7437919 = 11156879) B11156879
theorem B2612831 : Blo 1740571 2612831 := bstep (se 1 (by rfl) ⟨1959623, by rfl⟩ : syracuseStep 2612831 = 3919247) B3919247
theorem B2613047 : Blo 1740571 2613047 := bstep (se 1 (by rfl) ⟨1959785, by rfl⟩ : syracuseStep 2613047 = 3919571) B3919571
theorem B21192509 : Blo 1740571 21192509 := bstep (se 3 (by rfl) ⟨3973595, by rfl⟩ : syracuseStep 21192509 = 7947191) B7947191
theorem B4407169 : Blo 1740571 4407169 := bstep (se 2 (by rfl) ⟨1652688, by rfl⟩ : syracuseStep 4407169 = 3305377) B3305377
theorem B37674881 : Blo 1740571 37674881 := bstep (se 2 (by rfl) ⟨14128080, by rfl⟩ : syracuseStep 37674881 = 28256161) B28256161
theorem B278822807 : Blo 1740571 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B2613467 : Blo 1740571 2613467 := bstep (se 1 (by rfl) ⟨1960100, by rfl⟩ : syracuseStep 2613467 = 3920201) B3920201
theorem B2613479 : Blo 1740571 2613479 := bstep (se 1 (by rfl) ⟨1960109, by rfl⟩ : syracuseStep 2613479 = 3920219) B3920219
theorem B2613641 : Blo 1740571 2613641 := bstep (se 2 (by rfl) ⟨980115, by rfl⟩ : syracuseStep 2613641 = 1960231) B1960231
theorem B10731959 : Blo 1740571 10731959 := bstep (se 1 (by rfl) ⟨8048969, by rfl⟩ : syracuseStep 10731959 = 16097939) B16097939
theorem B8159687 : Blo 1740571 8159687 := bstep (se 1 (by rfl) ⟨6119765, by rfl⟩ : syracuseStep 8159687 = 12239531) B12239531
theorem B2204111 : Blo 1740571 2204111 := bstep (se 1 (by rfl) ⟨1653083, by rfl⟩ : syracuseStep 2204111 = 3306167) B3306167
theorem B2613737 : Blo 1740571 2613737 := bstep (se 2 (by rfl) ⟨980151, by rfl⟩ : syracuseStep 2613737 = 1960303) B1960303
theorem B1958503 : Blo 1740571 1958503 := bstep (se 1 (by rfl) ⟨1468877, by rfl⟩ : syracuseStep 1958503 = 2937755) B2937755
theorem B2204263 : Blo 1740571 2204263 := bstep (se 1 (by rfl) ⟨1653197, by rfl⟩ : syracuseStep 2204263 = 3306395) B3306395
theorem B11158211 : Blo 1740571 11158211 := bstep (se 1 (by rfl) ⟨8368658, by rfl⟩ : syracuseStep 11158211 = 16737317) B16737317
theorem B5874443 : Blo 1740571 5874443 := bstep (se 1 (by rfl) ⟨4405832, by rfl⟩ : syracuseStep 5874443 = 8811665) B8811665
theorem B3916601 : Blo 1740571 3916601 := bstep (se 2 (by rfl) ⟨1468725, by rfl⟩ : syracuseStep 3916601 = 2937451) B2937451
theorem B4408121 : Blo 1740571 4408121 := bstep (se 2 (by rfl) ⟨1653045, by rfl⟩ : syracuseStep 4408121 = 3306091) B3306091
theorem B3916655 : Blo 1740571 3916655 := bstep (se 1 (by rfl) ⟨2937491, by rfl⟩ : syracuseStep 3916655 = 5874983) B5874983
theorem B11158519 : Blo 1740571 11158519 := bstep (se 1 (by rfl) ⟨8368889, by rfl⟩ : syracuseStep 11158519 = 16737779) B16737779
theorem B5874713 : Blo 1740571 5874713 := bstep (se 2 (by rfl) ⟨2203017, by rfl⟩ : syracuseStep 5874713 = 4406035) B4406035
theorem B3138767 : Blo 1740571 3138767 := bstep (se 1 (by rfl) ⟨2354075, by rfl⟩ : syracuseStep 3138767 = 4708151) B4708151
theorem B12551435 : Blo 1740571 12551435 := bstep (se 1 (by rfl) ⟨9413576, by rfl⟩ : syracuseStep 12551435 = 18827153) B18827153
theorem B7439627 : Blo 1740571 7439627 := bstep (se 1 (by rfl) ⟨5579720, by rfl⟩ : syracuseStep 7439627 = 11159441) B11159441
theorem B2205083 : Blo 1740571 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B3917231 : Blo 1740571 3917231 := bstep (se 1 (by rfl) ⟨2937923, by rfl⟩ : syracuseStep 3917231 = 5875847) B5875847
theorem B9913853 : Blo 1740571 9913853 := bstep (se 3 (by rfl) ⟨1858847, by rfl⟩ : syracuseStep 9913853 = 3717695) B3717695
theorem B5875361 : Blo 1740571 5875361 := bstep (se 2 (by rfl) ⟨2203260, by rfl⟩ : syracuseStep 5875361 = 4406521) B4406521
theorem B6276827 : Blo 1740571 6276827 := bstep (se 1 (by rfl) ⟨4707620, by rfl⟩ : syracuseStep 6276827 = 9415241) B9415241
theorem B4957919 : Blo 1740571 4957919 := bstep (se 1 (by rfl) ⟨3718439, by rfl⟩ : syracuseStep 4957919 = 7436879) B7436879
theorem B19834631 : Blo 1740571 19834631 := bstep (se 1 (by rfl) ⟨14875973, by rfl⟩ : syracuseStep 19834631 = 29751947) B29751947
theorem B14870303 : Blo 1740571 14870303 := bstep (se 1 (by rfl) ⟨11152727, by rfl⟩ : syracuseStep 14870303 = 22305455) B22305455
theorem B18827063 : Blo 1740571 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B8816849 : Blo 1740571 8816849 := bstep (se 2 (by rfl) ⟨3306318, by rfl⟩ : syracuseStep 8816849 = 6612637) B6612637
theorem B3918059 : Blo 1740571 3918059 := bstep (se 1 (by rfl) ⟨2938544, by rfl⟩ : syracuseStep 3918059 = 5877089) B5877089
theorem B7440619 : Blo 1740571 7440619 := bstep (se 1 (by rfl) ⟨5580464, by rfl⟩ : syracuseStep 7440619 = 11160929) B11160929
theorem B4409579 : Blo 1740571 4409579 := bstep (se 1 (by rfl) ⟨3307184, by rfl⟩ : syracuseStep 4409579 = 6614369) B6614369
theorem B5876063 : Blo 1740571 5876063 := bstep (se 1 (by rfl) ⟨4407047, by rfl⟩ : syracuseStep 5876063 = 8814095) B8814095
theorem B4409761 : Blo 1740571 4409761 := bstep (se 2 (by rfl) ⟨1653660, by rfl⟩ : syracuseStep 4409761 = 3307321) B3307321
theorem B5876225 : Blo 1740571 5876225 := bstep (se 2 (by rfl) ⟨2203584, by rfl⟩ : syracuseStep 5876225 = 4407169) B4407169
theorem B50228099 : Blo 1740571 50228099 := bstep (se 1 (by rfl) ⟨37671074, by rfl⟩ : syracuseStep 50228099 = 75342149) B75342149
theorem B5876711 : Blo 1740571 5876711 := bstep (se 1 (by rfl) ⟨4407533, by rfl⟩ : syracuseStep 5876711 = 8815067) B8815067
theorem B22613215 : Blo 1740571 22613215 := bstep (se 1 (by rfl) ⟨16959911, by rfl⟩ : syracuseStep 22613215 = 33919823) B33919823
theorem B5582105 : Blo 1740571 5582105 := bstep (se 2 (by rfl) ⟨2093289, by rfl⟩ : syracuseStep 5582105 = 4186579) B4186579
theorem B5877035 : Blo 1740571 5877035 := bstep (se 1 (by rfl) ⟨4407776, by rfl⟩ : syracuseStep 5877035 = 8815553) B8815553
theorem B1764839 : Blo 1740571 1764839 := bstep (se 1 (by rfl) ⟨1323629, by rfl⟩ : syracuseStep 1764839 = 2647259) B2647259
theorem B11161081 : Blo 1740571 11161081 := bstep (se 2 (by rfl) ⟨4185405, by rfl⟩ : syracuseStep 11161081 = 8370811) B8370811
theorem B3919355 : Blo 1740571 3919355 := bstep (se 1 (by rfl) ⟨2939516, by rfl⟩ : syracuseStep 3919355 = 5879033) B5879033
theorem B4410875 : Blo 1740571 4410875 := bstep (se 1 (by rfl) ⟨3308156, by rfl⟩ : syracuseStep 4410875 = 6616313) B6616313
theorem B12242447 : Blo 1740571 12242447 := bstep (se 1 (by rfl) ⟨9181835, by rfl⟩ : syracuseStep 12242447 = 18363671) B18363671
theorem B5877305 : Blo 1740571 5877305 := bstep (se 2 (by rfl) ⟨2203989, by rfl⟩ : syracuseStep 5877305 = 4407979) B4407979
theorem B3919535 : Blo 1740571 3919535 := bstep (se 1 (by rfl) ⟨2939651, by rfl⟩ : syracuseStep 3919535 = 5879303) B5879303
theorem B1740615 : Blo 1740571 1740615 := bstep (se 1 (by rfl) ⟨1305461, by rfl⟩ : syracuseStep 1740615 = 2610923) B2610923
theorem B2789291 : Blo 1740571 2789291 := bstep (se 1 (by rfl) ⟨2091968, by rfl⟩ : syracuseStep 2789291 = 4183937) B4183937
theorem B4960207 : Blo 1740571 4960207 := bstep (se 1 (by rfl) ⟨3720155, by rfl⟩ : syracuseStep 4960207 = 7440311) B7440311
theorem B1740767 : Blo 1740571 1740767 := bstep (se 1 (by rfl) ⟨1305575, by rfl⟩ : syracuseStep 1740767 = 2611151) B2611151
theorem B4960379 : Blo 1740571 4960379 := bstep (se 1 (by rfl) ⟨3720284, by rfl⟩ : syracuseStep 4960379 = 7440569) B7440569
theorem B1741031 : Blo 1740571 1741031 := bstep (se 1 (by rfl) ⟨1305773, by rfl⟩ : syracuseStep 1741031 = 2611547) B2611547
theorem B2478367 : Blo 1740571 2478367 := bstep (se 1 (by rfl) ⟨1858775, by rfl⟩ : syracuseStep 2478367 = 3717551) B3717551
theorem B3920183 : Blo 1740571 3920183 := bstep (se 1 (by rfl) ⟨2940137, by rfl⟩ : syracuseStep 3920183 = 5880275) B5880275
theorem B2937215 : Blo 1740571 2937215 := bstep (se 1 (by rfl) ⟨2202911, by rfl⟩ : syracuseStep 2937215 = 4405823) B4405823
theorem B1741183 : Blo 1740571 1741183 := bstep (se 1 (by rfl) ⟨1305887, by rfl⟩ : syracuseStep 1741183 = 2611775) B2611775
theorem B3920255 : Blo 1740571 3920255 := bstep (se 1 (by rfl) ⟨2940191, by rfl⟩ : syracuseStep 3920255 = 5880383) B5880383
theorem B8819117 : Blo 1740571 8819117 := bstep (se 3 (by rfl) ⟨1653584, by rfl⟩ : syracuseStep 8819117 = 3307169) B3307169
theorem B1741263 : Blo 1740571 1741263 := bstep (se 1 (by rfl) ⟨1305947, by rfl⟩ : syracuseStep 1741263 = 2611895) B2611895
theorem B8819279 : Blo 1740571 8819279 := bstep (se 1 (by rfl) ⟨6614459, by rfl⟩ : syracuseStep 8819279 = 13228919) B13228919
theorem B1741415 : Blo 1740571 1741415 := bstep (se 1 (by rfl) ⟨1306061, by rfl⟩ : syracuseStep 1741415 = 2612123) B2612123
theorem B42349205 : Blo 1740571 42349205 := bstep (se 6 (by rfl) ⟨992559, by rfl⟩ : syracuseStep 42349205 = 1985119) B1985119
theorem B9917225 : Blo 1740571 9917225 := bstep (se 2 (by rfl) ⟨3718959, by rfl⟩ : syracuseStep 9917225 = 7437919) B7437919
theorem B2937647 : Blo 1740571 2937647 := bstep (se 1 (by rfl) ⟨2203235, by rfl⟩ : syracuseStep 2937647 = 4406471) B4406471
theorem B1741679 : Blo 1740571 1741679 := bstep (se 1 (by rfl) ⟨1306259, by rfl⟩ : syracuseStep 1741679 = 2612519) B2612519
theorem B1741735 : Blo 1740571 1741735 := bstep (se 1 (by rfl) ⟨1306301, by rfl⟩ : syracuseStep 1741735 = 2612603) B2612603
theorem B42374117 : Blo 1740571 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B1741819 : Blo 1740571 1741819 := bstep (se 1 (by rfl) ⟨1306364, by rfl⟩ : syracuseStep 1741819 = 2612729) B2612729
theorem B1741887 : Blo 1740571 1741887 := bstep (se 1 (by rfl) ⟨1306415, by rfl⟩ : syracuseStep 1741887 = 2612831) B2612831
theorem B1742031 : Blo 1740571 1742031 := bstep (se 1 (by rfl) ⟨1306523, by rfl⟩ : syracuseStep 1742031 = 2613047) B2613047
theorem B14128339 : Blo 1740571 14128339 := bstep (se 1 (by rfl) ⟨10596254, by rfl⟩ : syracuseStep 14128339 = 21192509) B21192509
theorem B185881871 : Blo 1740571 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B31774103 : Blo 1740571 31774103 := bstep (se 1 (by rfl) ⟨23830577, by rfl⟩ : syracuseStep 31774103 = 47661155) B47661155
theorem B5879195 : Blo 1740571 5879195 := bstep (se 1 (by rfl) ⟨4409396, by rfl⟩ : syracuseStep 5879195 = 8818793) B8818793
theorem B1742235 : Blo 1740571 1742235 := bstep (se 1 (by rfl) ⟨1306676, by rfl⟩ : syracuseStep 1742235 = 2613353) B2613353
theorem B16733627 : Blo 1740571 16733627 := bstep (se 1 (by rfl) ⟨12550220, by rfl⟩ : syracuseStep 16733627 = 25100441) B25100441
theorem B1742447 : Blo 1740571 1742447 := bstep (se 1 (by rfl) ⟨1306835, by rfl⟩ : syracuseStep 1742447 = 2613671) B2613671
theorem B1742503 : Blo 1740571 1742503 := bstep (se 1 (by rfl) ⟨1306877, by rfl⟩ : syracuseStep 1742503 = 2613755) B2613755
theorem B2610911 : Blo 1740571 2610911 := bstep (se 1 (by rfl) ⟨1958183, by rfl⟩ : syracuseStep 2610911 = 3916367) B3916367
theorem B2938619 : Blo 1740571 2938619 := bstep (se 1 (by rfl) ⟨2203964, by rfl⟩ : syracuseStep 2938619 = 4407929) B4407929
theorem B2611007 : Blo 1740571 2611007 := bstep (se 1 (by rfl) ⟨1958255, by rfl⟩ : syracuseStep 2611007 = 3916511) B3916511
theorem B2611175 : Blo 1740571 2611175 := bstep (se 1 (by rfl) ⟨1958381, by rfl⟩ : syracuseStep 2611175 = 3916763) B3916763
theorem B2938855 : Blo 1740571 2938855 := bstep (se 1 (by rfl) ⟨2204141, by rfl⟩ : syracuseStep 2938855 = 4408283) B4408283
theorem B2611193 : Blo 1740571 2611193 := bstep (se 2 (by rfl) ⟨979197, by rfl⟩ : syracuseStep 2611193 = 1958395) B1958395
theorem B8820737 : Blo 1740571 8820737 := bstep (se 2 (by rfl) ⟨3307776, by rfl⟩ : syracuseStep 8820737 = 6615553) B6615553
theorem B14317651 : Blo 1740571 14317651 := bstep (se 1 (by rfl) ⟨10738238, by rfl⟩ : syracuseStep 14317651 = 21476477) B21476477
theorem B2611295 : Blo 1740571 2611295 := bstep (se 1 (by rfl) ⟨1958471, by rfl⟩ : syracuseStep 2611295 = 3916943) B3916943
theorem B5879951 : Blo 1740571 5879951 := bstep (se 1 (by rfl) ⟨4409963, by rfl⟩ : syracuseStep 5879951 = 8819927) B8819927
theorem B2611355 : Blo 1740571 2611355 := bstep (se 1 (by rfl) ⟨1958516, by rfl⟩ : syracuseStep 2611355 = 3917033) B3917033
theorem B2611391 : Blo 1740571 2611391 := bstep (se 1 (by rfl) ⟨1958543, by rfl⟩ : syracuseStep 2611391 = 3917087) B3917087
theorem B2939071 : Blo 1740571 2939071 := bstep (se 1 (by rfl) ⟨2204303, by rfl⟩ : syracuseStep 2939071 = 4408607) B4408607
theorem B11163851 : Blo 1740571 11163851 := bstep (se 1 (by rfl) ⟨8372888, by rfl⟩ : syracuseStep 11163851 = 16745777) B16745777
theorem B2611433 : Blo 1740571 2611433 := bstep (se 2 (by rfl) ⟨979287, by rfl⟩ : syracuseStep 2611433 = 1958575) B1958575
theorem B5577083 : Blo 1740571 5577083 := bstep (se 1 (by rfl) ⟨4182812, by rfl⟩ : syracuseStep 5577083 = 8365625) B8365625
theorem B101792173 : Blo 1740571 101792173 := bstep (se 3 (by rfl) ⟨19086032, by rfl⟩ : syracuseStep 101792173 = 38172065) B38172065
theorem B25106897 : Blo 1740571 25106897 := bstep (se 2 (by rfl) ⟨9415086, by rfl⟩ : syracuseStep 25106897 = 18830173) B18830173
theorem B2611739 : Blo 1740571 2611739 := bstep (se 1 (by rfl) ⟨1958804, by rfl⟩ : syracuseStep 2611739 = 3917609) B3917609
theorem B19847753 : Blo 1740571 19847753 := bstep (se 2 (by rfl) ⟨7442907, by rfl⟩ : syracuseStep 19847753 = 14885815) B14885815
theorem B14883425 : Blo 1740571 14883425 := bstep (se 2 (by rfl) ⟨5581284, by rfl⟩ : syracuseStep 14883425 = 11162569) B11162569
theorem B2611817 : Blo 1740571 2611817 := bstep (se 2 (by rfl) ⟨979431, by rfl⟩ : syracuseStep 2611817 = 1958863) B1958863
theorem B8821385 : Blo 1740571 8821385 := bstep (se 2 (by rfl) ⟨3308019, by rfl⟩ : syracuseStep 8821385 = 6616039) B6616039
theorem B7944857 : Blo 1740571 7944857 := bstep (se 2 (by rfl) ⟨2979321, by rfl⟩ : syracuseStep 7944857 = 5958643) B5958643
theorem B8821547 : Blo 1740571 8821547 := bstep (se 1 (by rfl) ⟨6616160, by rfl⟩ : syracuseStep 8821547 = 13232321) B13232321
theorem B2939807 : Blo 1740571 2939807 := bstep (se 1 (by rfl) ⟨2204855, by rfl⟩ : syracuseStep 2939807 = 4409711) B4409711
theorem B8813609 : Blo 1740571 8813609 := bstep (se 2 (by rfl) ⟨3305103, by rfl⟩ : syracuseStep 8813609 = 6610207) B6610207
theorem B2612345 : Blo 1740571 2612345 := bstep (se 2 (by rfl) ⟨979629, by rfl⟩ : syracuseStep 2612345 = 1959259) B1959259
theorem B2612447 : Blo 1740571 2612447 := bstep (se 1 (by rfl) ⟨1959335, by rfl⟩ : syracuseStep 2612447 = 3918671) B3918671
theorem B5881085 : Blo 1740571 5881085 := bstep (se 3 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 5881085 = 2205407) B2205407
theorem B7437577 : Blo 1740571 7437577 := bstep (se 2 (by rfl) ⟨2789091, by rfl⟩ : syracuseStep 7437577 = 5578183) B5578183
theorem B2612489 : Blo 1740571 2612489 := bstep (se 2 (by rfl) ⟨979683, by rfl⟩ : syracuseStep 2612489 = 1959367) B1959367
theorem B2940239 : Blo 1740571 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B12557663 : Blo 1740571 12557663 := bstep (se 1 (by rfl) ⟨9418247, by rfl⟩ : syracuseStep 12557663 = 18836495) B18836495
theorem B2612591 : Blo 1740571 2612591 := bstep (se 1 (by rfl) ⟨1959443, by rfl⟩ : syracuseStep 2612591 = 3918887) B3918887
theorem B10739105 : Blo 1740571 10739105 := bstep (se 2 (by rfl) ⟨4027164, by rfl⟩ : syracuseStep 10739105 = 8054329) B8054329
theorem B4300199 : Blo 1740571 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B2612711 : Blo 1740571 2612711 := bstep (se 1 (by rfl) ⟨1959533, by rfl⟩ : syracuseStep 2612711 = 3919067) B3919067
theorem B6610511 : Blo 1740571 6610511 := bstep (se 1 (by rfl) ⟨4957883, by rfl⟩ : syracuseStep 6610511 = 9915767) B9915767
theorem B2612843 : Blo 1740571 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B2612969 : Blo 1740571 2612969 := bstep (se 2 (by rfl) ⟨979863, by rfl⟩ : syracuseStep 2612969 = 1959727) B1959727
theorem B2203463 : Blo 1740571 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B2613113 : Blo 1740571 2613113 := bstep (se 2 (by rfl) ⟨979917, by rfl⟩ : syracuseStep 2613113 = 1959835) B1959835
theorem B25116587 : Blo 1740571 25116587 := bstep (se 1 (by rfl) ⟨18837440, by rfl⟩ : syracuseStep 25116587 = 37674881) B37674881
theorem B2203615 : Blo 1740571 2203615 := bstep (se 1 (by rfl) ⟨1652711, by rfl⟩ : syracuseStep 2203615 = 3305423) B3305423
theorem B2613215 : Blo 1740571 2613215 := bstep (se 1 (by rfl) ⟨1959911, by rfl⟩ : syracuseStep 2613215 = 3919823) B3919823
theorem B2613455 : Blo 1740571 2613455 := bstep (se 1 (by rfl) ⟨1960091, by rfl⟩ : syracuseStep 2613455 = 3920183) B3920183
theorem B1958143 : Blo 1740571 1958143 := bstep (se 1 (by rfl) ⟨1468607, by rfl⟩ : syracuseStep 1958143 = 2937215) B2937215
theorem B2613503 : Blo 1740571 2613503 := bstep (se 1 (by rfl) ⟨1960127, by rfl⟩ : syracuseStep 2613503 = 3920255) B3920255
theorem B5439791 : Blo 1740571 5439791 := bstep (se 1 (by rfl) ⟨4079843, by rfl⟩ : syracuseStep 5439791 = 8159687) B8159687
theorem B9920825 : Blo 1740571 9920825 := bstep (se 2 (by rfl) ⟨3720309, by rfl⟩ : syracuseStep 9920825 = 7440619) B7440619
theorem B7438807 : Blo 1740571 7438807 := bstep (se 1 (by rfl) ⟨5579105, by rfl⟩ : syracuseStep 7438807 = 11158211) B11158211
theorem B3916295 : Blo 1740571 3916295 := bstep (se 1 (by rfl) ⟨2937221, by rfl⟩ : syracuseStep 3916295 = 5874443) B5874443
theorem B6611483 : Blo 1740571 6611483 := bstep (se 1 (by rfl) ⟨4958612, by rfl⟩ : syracuseStep 6611483 = 9917225) B9917225
theorem B1958431 : Blo 1740571 1958431 := bstep (se 1 (by rfl) ⟨1468823, by rfl⟩ : syracuseStep 1958431 = 2937647) B2937647
theorem B3916475 : Blo 1740571 3916475 := bstep (se 1 (by rfl) ⟨2937356, by rfl⟩ : syracuseStep 3916475 = 5874713) B5874713
theorem B123921247 : Blo 1740571 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B3916907 : Blo 1740571 3916907 := bstep (se 1 (by rfl) ⟨2937680, by rfl⟩ : syracuseStep 3916907 = 5875361) B5875361
theorem B1959079 : Blo 1740571 1959079 := bstep (se 1 (by rfl) ⟨1469309, by rfl⟩ : syracuseStep 1959079 = 2938619) B2938619
theorem B13223087 : Blo 1740571 13223087 := bstep (se 1 (by rfl) ⟨9917315, by rfl⟩ : syracuseStep 13223087 = 19834631) B19834631
theorem B9913535 : Blo 1740571 9913535 := bstep (se 1 (by rfl) ⟨7435151, by rfl⟩ : syracuseStep 9913535 = 14870303) B14870303
theorem B12551375 : Blo 1740571 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B14878025 : Blo 1740571 14878025 := bstep (se 2 (by rfl) ⟨5579259, by rfl⟩ : syracuseStep 14878025 = 11158519) B11158519
theorem B3917375 : Blo 1740571 3917375 := bstep (se 1 (by rfl) ⟨2938031, by rfl⟩ : syracuseStep 3917375 = 5876063) B5876063
theorem B16737931 : Blo 1740571 16737931 := bstep (se 1 (by rfl) ⟨12553448, by rfl⟩ : syracuseStep 16737931 = 25106897) B25106897
theorem B3917483 : Blo 1740571 3917483 := bstep (se 1 (by rfl) ⟨2938112, by rfl⟩ : syracuseStep 3917483 = 5876225) B5876225
theorem B13231835 : Blo 1740571 13231835 := bstep (se 1 (by rfl) ⟨9923876, by rfl⟩ : syracuseStep 13231835 = 19847753) B19847753
theorem B9922283 : Blo 1740571 9922283 := bstep (se 1 (by rfl) ⟨7441712, by rfl⟩ : syracuseStep 9922283 = 14883425) B14883425
theorem B1959871 : Blo 1740571 1959871 := bstep (se 1 (by rfl) ⟨1469903, by rfl⟩ : syracuseStep 1959871 = 2939807) B2939807
theorem B3917807 : Blo 1740571 3917807 := bstep (se 1 (by rfl) ⟨2938355, by rfl⟩ : syracuseStep 3917807 = 5876711) B5876711
theorem B5875739 : Blo 1740571 5875739 := bstep (se 1 (by rfl) ⟨4406804, by rfl⟩ : syracuseStep 5875739 = 8813609) B8813609
theorem B3721403 : Blo 1740571 3721403 := bstep (se 1 (by rfl) ⟨2791052, by rfl⟩ : syracuseStep 3721403 = 5582105) B5582105
theorem B5875901 : Blo 1740571 5875901 := bstep (se 3 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 5875901 = 2203463) B2203463
theorem B3918023 : Blo 1740571 3918023 := bstep (se 1 (by rfl) ⟨2938517, by rfl⟩ : syracuseStep 3918023 = 5877035) B5877035
theorem B1960159 : Blo 1740571 1960159 := bstep (se 1 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 1960159 = 2940239) B2940239
theorem B8161631 : Blo 1740571 8161631 := bstep (se 1 (by rfl) ⟨6121223, by rfl⟩ : syracuseStep 8161631 = 12242447) B12242447
theorem B3918203 : Blo 1740571 3918203 := bstep (se 1 (by rfl) ⟨2938652, by rfl⟩ : syracuseStep 3918203 = 5877305) B5877305
theorem B6613609 : Blo 1740571 6613609 := bstep (se 2 (by rfl) ⟨2480103, by rfl⟩ : syracuseStep 6613609 = 4960207) B4960207
theorem B3918473 : Blo 1740571 3918473 := bstep (se 2 (by rfl) ⟨1469427, by rfl⟩ : syracuseStep 3918473 = 2938855) B2938855
theorem B19090201 : Blo 1740571 19090201 := bstep (se 2 (by rfl) ⟨7158825, by rfl⟩ : syracuseStep 19090201 = 14317651) B14317651
theorem B3918761 : Blo 1740571 3918761 := bstep (se 2 (by rfl) ⟨1469535, by rfl⟩ : syracuseStep 3918761 = 2939071) B2939071
theorem B7154639 : Blo 1740571 7154639 := bstep (se 1 (by rfl) ⟨5365979, by rfl⟩ : syracuseStep 7154639 = 10731959) B10731959
theorem B3304489 : Blo 1740571 3304489 := bstep (se 2 (by rfl) ⟨1239183, by rfl⟩ : syracuseStep 3304489 = 2478367) B2478367
theorem B28232803 : Blo 1740571 28232803 := bstep (se 1 (by rfl) ⟨21174602, by rfl⟩ : syracuseStep 28232803 = 42349205) B42349205
theorem B28249411 : Blo 1740571 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B2092511 : Blo 1740571 2092511 := bstep (se 1 (by rfl) ⟨1569383, by rfl⟩ : syracuseStep 2092511 = 3138767) B3138767
theorem B8367623 : Blo 1740571 8367623 := bstep (se 1 (by rfl) ⟨6275717, by rfl⟩ : syracuseStep 8367623 = 12551435) B12551435
theorem B3919463 : Blo 1740571 3919463 := bstep (se 1 (by rfl) ⟨2939597, by rfl⟩ : syracuseStep 3919463 = 5879195) B5879195
theorem B1740607 : Blo 1740571 1740607 := bstep (se 1 (by rfl) ⟨1305455, by rfl⟩ : syracuseStep 1740607 = 2610911) B2610911
theorem B3305279 : Blo 1740571 3305279 := bstep (se 1 (by rfl) ⟨2478959, by rfl⟩ : syracuseStep 3305279 = 4957919) B4957919
theorem B5877629 : Blo 1740571 5877629 := bstep (se 3 (by rfl) ⟨1102055, by rfl⟩ : syracuseStep 5877629 = 2204111) B2204111
theorem B1740671 : Blo 1740571 1740671 := bstep (se 1 (by rfl) ⟨1305503, by rfl⟩ : syracuseStep 1740671 = 2611007) B2611007
theorem B4706237 : Blo 1740571 4706237 := bstep (se 3 (by rfl) ⟨882419, by rfl⟩ : syracuseStep 4706237 = 1764839) B1764839
theorem B1740783 : Blo 1740571 1740783 := bstep (se 1 (by rfl) ⟨1305587, by rfl⟩ : syracuseStep 1740783 = 2611175) B2611175
theorem B1740795 : Blo 1740571 1740795 := bstep (se 1 (by rfl) ⟨1305596, by rfl⟩ : syracuseStep 1740795 = 2611193) B2611193
theorem B1740863 : Blo 1740571 1740863 := bstep (se 1 (by rfl) ⟨1305647, by rfl⟩ : syracuseStep 1740863 = 2611295) B2611295
theorem B3919967 : Blo 1740571 3919967 := bstep (se 1 (by rfl) ⟨2939975, by rfl⟩ : syracuseStep 3919967 = 5879951) B5879951
theorem B1740903 : Blo 1740571 1740903 := bstep (se 1 (by rfl) ⟨1305677, by rfl⟩ : syracuseStep 1740903 = 2611355) B2611355
theorem B1740927 : Blo 1740571 1740927 := bstep (se 1 (by rfl) ⟨1305695, by rfl⟩ : syracuseStep 1740927 = 2611391) B2611391
theorem B7442567 : Blo 1740571 7442567 := bstep (se 1 (by rfl) ⟨5581925, by rfl⟩ : syracuseStep 7442567 = 11163851) B11163851
theorem B5877899 : Blo 1740571 5877899 := bstep (se 1 (by rfl) ⟨4408424, by rfl⟩ : syracuseStep 5877899 = 8816849) B8816849
theorem B1740955 : Blo 1740571 1740955 := bstep (se 1 (by rfl) ⟨1305716, by rfl⟩ : syracuseStep 1740955 = 2611433) B2611433
theorem B18837785 : Blo 1740571 18837785 := bstep (se 2 (by rfl) ⟨7064169, by rfl⟩ : syracuseStep 18837785 = 14128339) B14128339
theorem B30150953 : Blo 1740571 30150953 := bstep (se 2 (by rfl) ⟨11306607, by rfl⟩ : syracuseStep 30150953 = 22613215) B22613215
theorem B9916769 : Blo 1740571 9916769 := bstep (se 2 (by rfl) ⟨3718788, by rfl⟩ : syracuseStep 9916769 = 7437577) B7437577
theorem B1741159 : Blo 1740571 1741159 := bstep (se 1 (by rfl) ⟨1305869, by rfl⟩ : syracuseStep 1741159 = 2611739) B2611739
theorem B1741211 : Blo 1740571 1741211 := bstep (se 1 (by rfl) ⟨1305908, by rfl⟩ : syracuseStep 1741211 = 2611817) B2611817
theorem B5296571 : Blo 1740571 5296571 := bstep (se 1 (by rfl) ⟨3972428, by rfl⟩ : syracuseStep 5296571 = 7944857) B7944857
theorem B33485399 : Blo 1740571 33485399 := bstep (se 1 (by rfl) ⟨25114049, by rfl⟩ : syracuseStep 33485399 = 50228099) B50228099
theorem B14881441 : Blo 1740571 14881441 := bstep (se 2 (by rfl) ⟨5580540, by rfl⟩ : syracuseStep 14881441 = 11161081) B11161081
theorem B1741563 : Blo 1740571 1741563 := bstep (se 1 (by rfl) ⟨1306172, by rfl⟩ : syracuseStep 1741563 = 2612345) B2612345
theorem B1741631 : Blo 1740571 1741631 := bstep (se 1 (by rfl) ⟨1306223, by rfl⟩ : syracuseStep 1741631 = 2612447) B2612447
theorem B3920723 : Blo 1740571 3920723 := bstep (se 1 (by rfl) ⟨2940542, by rfl⟩ : syracuseStep 3920723 = 5881085) B5881085
theorem B1741659 : Blo 1740571 1741659 := bstep (se 1 (by rfl) ⟨1306244, by rfl⟩ : syracuseStep 1741659 = 2612489) B2612489
theorem B1741727 : Blo 1740571 1741727 := bstep (se 1 (by rfl) ⟨1306295, by rfl⟩ : syracuseStep 1741727 = 2612591) B2612591
theorem B1741807 : Blo 1740571 1741807 := bstep (se 1 (by rfl) ⟨1306355, by rfl⟩ : syracuseStep 1741807 = 2612711) B2612711
theorem B1741895 : Blo 1740571 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B1741979 : Blo 1740571 1741979 := bstep (se 1 (by rfl) ⟨1306484, by rfl⟩ : syracuseStep 1741979 = 2612969) B2612969
theorem B1742075 : Blo 1740571 1742075 := bstep (se 1 (by rfl) ⟨1306556, by rfl⟩ : syracuseStep 1742075 = 2613113) B2613113
theorem B2938153 : Blo 1740571 2938153 := bstep (se 2 (by rfl) ⟨1101807, by rfl⟩ : syracuseStep 2938153 = 2203615) B2203615
theorem B1742143 : Blo 1740571 1742143 := bstep (se 1 (by rfl) ⟨1306607, by rfl⟩ : syracuseStep 1742143 = 2613215) B2613215
theorem B3306919 : Blo 1740571 3306919 := bstep (se 1 (by rfl) ⟨2480189, by rfl⟩ : syracuseStep 3306919 = 4960379) B4960379
theorem B1742311 : Blo 1740571 1742311 := bstep (se 1 (by rfl) ⟨1306733, by rfl⟩ : syracuseStep 1742311 = 2613467) B2613467
theorem B1742319 : Blo 1740571 1742319 := bstep (se 1 (by rfl) ⟨1306739, by rfl⟩ : syracuseStep 1742319 = 2613479) B2613479
theorem B1742427 : Blo 1740571 1742427 := bstep (se 1 (by rfl) ⟨1306820, by rfl⟩ : syracuseStep 1742427 = 2613641) B2613641
theorem B5879411 : Blo 1740571 5879411 := bstep (se 1 (by rfl) ⟨4409558, by rfl⟩ : syracuseStep 5879411 = 8819117) B8819117
theorem B1742491 : Blo 1740571 1742491 := bstep (se 1 (by rfl) ⟨1306868, by rfl⟩ : syracuseStep 1742491 = 2613737) B2613737
theorem B5879519 : Blo 1740571 5879519 := bstep (se 1 (by rfl) ⟨4409639, by rfl⟩ : syracuseStep 5879519 = 8819279) B8819279
theorem B2611067 : Blo 1740571 2611067 := bstep (se 1 (by rfl) ⟨1958300, by rfl⟩ : syracuseStep 2611067 = 3916601) B3916601
theorem B2938747 : Blo 1740571 2938747 := bstep (se 1 (by rfl) ⟨2204060, by rfl⟩ : syracuseStep 2938747 = 4408121) B4408121
theorem B5879681 : Blo 1740571 5879681 := bstep (se 2 (by rfl) ⟨2204880, by rfl⟩ : syracuseStep 5879681 = 4409761) B4409761
theorem B135722897 : Blo 1740571 135722897 := bstep (se 2 (by rfl) ⟨50896086, by rfl⟩ : syracuseStep 135722897 = 101792173) B101792173
theorem B2611103 : Blo 1740571 2611103 := bstep (se 1 (by rfl) ⟨1958327, by rfl⟩ : syracuseStep 2611103 = 3916655) B3916655
theorem B19839005 : Blo 1740571 19839005 := bstep (se 3 (by rfl) ⟨3719813, by rfl⟩ : syracuseStep 19839005 = 7439627) B7439627
theorem B2611337 : Blo 1740571 2611337 := bstep (se 2 (by rfl) ⟨979251, by rfl⟩ : syracuseStep 2611337 = 1958503) B1958503
theorem B2939017 : Blo 1740571 2939017 := bstep (se 2 (by rfl) ⟨1102131, by rfl⟩ : syracuseStep 2939017 = 2204263) B2204263
theorem B21182735 : Blo 1740571 21182735 := bstep (se 1 (by rfl) ⟨15887051, by rfl⟩ : syracuseStep 21182735 = 31774103) B31774103
theorem B2611487 : Blo 1740571 2611487 := bstep (se 1 (by rfl) ⟨1958615, by rfl⟩ : syracuseStep 2611487 = 3917231) B3917231
theorem B11155751 : Blo 1740571 11155751 := bstep (se 1 (by rfl) ⟨8366813, by rfl⟩ : syracuseStep 11155751 = 16733627) B16733627
theorem B6609235 : Blo 1740571 6609235 := bstep (se 1 (by rfl) ⟨4956926, by rfl⟩ : syracuseStep 6609235 = 9913853) B9913853
theorem B5880221 : Blo 1740571 5880221 := bstep (se 3 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 5880221 = 2205083) B2205083
theorem B4184551 : Blo 1740571 4184551 := bstep (se 1 (by rfl) ⟨3138413, by rfl⟩ : syracuseStep 4184551 = 6276827) B6276827
theorem B5880491 : Blo 1740571 5880491 := bstep (se 1 (by rfl) ⟨4410368, by rfl⟩ : syracuseStep 5880491 = 8820737) B8820737
theorem B2612039 : Blo 1740571 2612039 := bstep (se 1 (by rfl) ⟨1959029, by rfl⟩ : syracuseStep 2612039 = 3918059) B3918059
theorem B2939719 : Blo 1740571 2939719 := bstep (se 1 (by rfl) ⟨2204789, by rfl⟩ : syracuseStep 2939719 = 4409579) B4409579
theorem B3718055 : Blo 1740571 3718055 := bstep (se 1 (by rfl) ⟨2788541, by rfl⟩ : syracuseStep 3718055 = 5577083) B5577083
theorem B5880923 : Blo 1740571 5880923 := bstep (se 1 (by rfl) ⟨4410692, by rfl⟩ : syracuseStep 5880923 = 8821385) B8821385
theorem B5881031 : Blo 1740571 5881031 := bstep (se 1 (by rfl) ⟨4410773, by rfl⟩ : syracuseStep 5881031 = 8821547) B8821547
theorem B8371775 : Blo 1740571 8371775 := bstep (se 1 (by rfl) ⟨6278831, by rfl⟩ : syracuseStep 8371775 = 12557663) B12557663
theorem B7159403 : Blo 1740571 7159403 := bstep (se 1 (by rfl) ⟨5369552, by rfl⟩ : syracuseStep 7159403 = 10739105) B10739105
theorem B2866799 : Blo 1740571 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B2612903 : Blo 1740571 2612903 := bstep (se 1 (by rfl) ⟨1959677, by rfl⟩ : syracuseStep 2612903 = 3919355) B3919355
theorem B2940583 : Blo 1740571 2940583 := bstep (se 1 (by rfl) ⟨2205437, by rfl⟩ : syracuseStep 2940583 = 4410875) B4410875
theorem B4407007 : Blo 1740571 4407007 := bstep (se 1 (by rfl) ⟨3305255, by rfl⟩ : syracuseStep 4407007 = 6610511) B6610511
theorem B2613023 : Blo 1740571 2613023 := bstep (se 1 (by rfl) ⟨1959767, by rfl⟩ : syracuseStep 2613023 = 3919535) B3919535
theorem B1859527 : Blo 1740571 1859527 := bstep (se 1 (by rfl) ⟨1394645, by rfl⟩ : syracuseStep 1859527 = 2789291) B2789291
theorem B16744391 : Blo 1740571 16744391 := bstep (se 1 (by rfl) ⟨12558293, by rfl⟩ : syracuseStep 16744391 = 25116587) B25116587
theorem B2613311 : Blo 1740571 2613311 := bstep (se 1 (by rfl) ⟨1959983, by rfl⟩ : syracuseStep 2613311 = 3919967) B3919967
theorem B6611179 : Blo 1740571 6611179 := bstep (se 1 (by rfl) ⟨4958384, by rfl⟩ : syracuseStep 6611179 = 9916769) B9916769
theorem B3531047 : Blo 1740571 3531047 := bstep (se 1 (by rfl) ⟨2648285, by rfl⟩ : syracuseStep 3531047 = 5296571) B5296571
theorem B2613545 : Blo 1740571 2613545 := bstep (se 2 (by rfl) ⟨980079, by rfl⟩ : syracuseStep 2613545 = 1960159) B1960159
theorem B4407655 : Blo 1740571 4407655 := bstep (se 1 (by rfl) ⟨3305741, by rfl⟩ : syracuseStep 4407655 = 6611483) B6611483
theorem B22323599 : Blo 1740571 22323599 := bstep (se 1 (by rfl) ⟨16742699, by rfl⟩ : syracuseStep 22323599 = 33485399) B33485399
theorem B2613815 : Blo 1740571 2613815 := bstep (se 1 (by rfl) ⟨1960361, by rfl⟩ : syracuseStep 2613815 = 3920723) B3920723
theorem B50234093 : Blo 1740571 50234093 := bstep (se 3 (by rfl) ⟨9418892, by rfl⟩ : syracuseStep 50234093 = 18837785) B18837785
theorem B8815391 : Blo 1740571 8815391 := bstep (se 1 (by rfl) ⟨6611543, by rfl⟩ : syracuseStep 8815391 = 13223087) B13223087
theorem B19841921 : Blo 1740571 19841921 := bstep (se 2 (by rfl) ⟨7440720, by rfl⟩ : syracuseStep 19841921 = 14881441) B14881441
theorem B25453601 : Blo 1740571 25453601 := bstep (se 2 (by rfl) ⟨9545100, by rfl⟩ : syracuseStep 25453601 = 19090201) B19090201
theorem B5580029 : Blo 1740571 5580029 := bstep (se 3 (by rfl) ⟨1046255, by rfl⟩ : syracuseStep 5580029 = 2092511) B2092511
theorem B90481931 : Blo 1740571 90481931 := bstep (se 1 (by rfl) ⟨67861448, by rfl⟩ : syracuseStep 90481931 = 135722897) B135722897
theorem B3917159 : Blo 1740571 3917159 := bstep (se 1 (by rfl) ⟨2937869, by rfl⟩ : syracuseStep 3917159 = 5875739) B5875739
theorem B3917267 : Blo 1740571 3917267 := bstep (se 1 (by rfl) ⟨2937950, by rfl⟩ : syracuseStep 3917267 = 5875901) B5875901
theorem B5441087 : Blo 1740571 5441087 := bstep (se 1 (by rfl) ⟨4080815, by rfl⟩ : syracuseStep 5441087 = 8161631) B8161631
theorem B3917537 : Blo 1740571 3917537 := bstep (se 2 (by rfl) ⟨1469076, by rfl⟩ : syracuseStep 3917537 = 2938153) B2938153
theorem B4409225 : Blo 1740571 4409225 := bstep (se 2 (by rfl) ⟨1653459, by rfl⟩ : syracuseStep 4409225 = 3306919) B3306919
theorem B4769759 : Blo 1740571 4769759 := bstep (se 1 (by rfl) ⟨3577319, by rfl⟩ : syracuseStep 4769759 = 7154639) B7154639
theorem B22317241 : Blo 1740571 22317241 := bstep (se 2 (by rfl) ⟨8368965, by rfl⟩ : syracuseStep 22317241 = 16737931) B16737931
theorem B5876009 : Blo 1740571 5876009 := bstep (se 2 (by rfl) ⟨2203503, by rfl⟩ : syracuseStep 5876009 = 4407007) B4407007
theorem B5581183 : Blo 1740571 5581183 := bstep (se 1 (by rfl) ⟨4185887, by rfl⟩ : syracuseStep 5581183 = 8371775) B8371775
theorem B1911199 : Blo 1740571 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B3918329 : Blo 1740571 3918329 := bstep (se 2 (by rfl) ⟨1469373, by rfl⟩ : syracuseStep 3918329 = 2938747) B2938747
theorem B22317605 : Blo 1740571 22317605 := bstep (se 4 (by rfl) ⟨2092275, by rfl⟩ : syracuseStep 22317605 = 4184551) B4184551
theorem B3918419 : Blo 1740571 3918419 := bstep (se 1 (by rfl) ⟨2938814, by rfl⟩ : syracuseStep 3918419 = 5877629) B5877629
theorem B3918599 : Blo 1740571 3918599 := bstep (se 1 (by rfl) ⟨2938949, by rfl⟩ : syracuseStep 3918599 = 5877899) B5877899
theorem B3918689 : Blo 1740571 3918689 := bstep (se 2 (by rfl) ⟨1469508, by rfl⟩ : syracuseStep 3918689 = 2939017) B2939017
theorem B6613883 : Blo 1740571 6613883 := bstep (se 1 (by rfl) ⟨4960412, by rfl⟩ : syracuseStep 6613883 = 9920825) B9920825
theorem B9923741 : Blo 1740571 9923741 := bstep (se 3 (by rfl) ⟨1860701, by rfl⟩ : syracuseStep 9923741 = 3721403) B3721403
theorem B56487293 : Blo 1740571 56487293 := bstep (se 3 (by rfl) ⟨10591367, by rfl⟩ : syracuseStep 56487293 = 21182735) B21182735
theorem B8367583 : Blo 1740571 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B8818145 : Blo 1740571 8818145 := bstep (se 2 (by rfl) ⟨3306804, by rfl⟩ : syracuseStep 8818145 = 6613609) B6613609
theorem B3919607 : Blo 1740571 3919607 := bstep (se 1 (by rfl) ⟨2939705, by rfl⟩ : syracuseStep 3919607 = 5879411) B5879411
theorem B3919625 : Blo 1740571 3919625 := bstep (se 2 (by rfl) ⟨1469859, by rfl⟩ : syracuseStep 3919625 = 2939719) B2939719
theorem B165228329 : Blo 1740571 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B3919679 : Blo 1740571 3919679 := bstep (se 1 (by rfl) ⟨2939759, by rfl⟩ : syracuseStep 3919679 = 5879519) B5879519
theorem B6614855 : Blo 1740571 6614855 := bstep (se 1 (by rfl) ⟨4961141, by rfl⟩ : syracuseStep 6614855 = 9922283) B9922283
theorem B1740711 : Blo 1740571 1740711 := bstep (se 1 (by rfl) ⟨1305533, by rfl⟩ : syracuseStep 1740711 = 2611067) B2611067
theorem B3919787 : Blo 1740571 3919787 := bstep (se 1 (by rfl) ⟨2939840, by rfl⟩ : syracuseStep 3919787 = 5879681) B5879681
theorem B1740735 : Blo 1740571 1740735 := bstep (se 1 (by rfl) ⟨1305551, by rfl⟩ : syracuseStep 1740735 = 2611103) B2611103
theorem B13226003 : Blo 1740571 13226003 := bstep (se 1 (by rfl) ⟨9919502, by rfl⟩ : syracuseStep 13226003 = 19839005) B19839005
theorem B1740891 : Blo 1740571 1740891 := bstep (se 1 (by rfl) ⟨1305668, by rfl⟩ : syracuseStep 1740891 = 2611337) B2611337
theorem B1740991 : Blo 1740571 1740991 := bstep (se 1 (by rfl) ⟨1305743, by rfl⟩ : syracuseStep 1740991 = 2611487) B2611487
theorem B3920147 : Blo 1740571 3920147 := bstep (se 1 (by rfl) ⟨2940110, by rfl⟩ : syracuseStep 3920147 = 5880221) B5880221
theorem B3920327 : Blo 1740571 3920327 := bstep (se 1 (by rfl) ⟨2940245, by rfl⟩ : syracuseStep 3920327 = 5880491) B5880491
theorem B1741359 : Blo 1740571 1741359 := bstep (se 1 (by rfl) ⟨1306019, by rfl⟩ : syracuseStep 1741359 = 2612039) B2612039
theorem B2478703 : Blo 1740571 2478703 := bstep (se 1 (by rfl) ⟨1859027, by rfl⟩ : syracuseStep 2478703 = 3718055) B3718055
theorem B3920615 : Blo 1740571 3920615 := bstep (se 1 (by rfl) ⟨2940461, by rfl⟩ : syracuseStep 3920615 = 5880923) B5880923
theorem B3920687 : Blo 1740571 3920687 := bstep (se 1 (by rfl) ⟨2940515, by rfl⟩ : syracuseStep 3920687 = 5881031) B5881031
theorem B3920777 : Blo 1740571 3920777 := bstep (se 2 (by rfl) ⟨1470291, by rfl⟩ : syracuseStep 3920777 = 2940583) B2940583
theorem B9917477 : Blo 1740571 9917477 := bstep (se 4 (by rfl) ⟨929763, by rfl⟩ : syracuseStep 9917477 = 1859527) B1859527
theorem B4772935 : Blo 1740571 4772935 := bstep (se 1 (by rfl) ⟨3579701, by rfl⟩ : syracuseStep 4772935 = 7159403) B7159403
theorem B1741935 : Blo 1740571 1741935 := bstep (se 1 (by rfl) ⟨1306451, by rfl⟩ : syracuseStep 1741935 = 2612903) B2612903
theorem B1742015 : Blo 1740571 1742015 := bstep (se 1 (by rfl) ⟨1306511, by rfl⟩ : syracuseStep 1742015 = 2613023) B2613023
theorem B11162927 : Blo 1740571 11162927 := bstep (se 1 (by rfl) ⟨8372195, by rfl⟩ : syracuseStep 11162927 = 16744391) B16744391
theorem B4961711 : Blo 1740571 4961711 := bstep (se 1 (by rfl) ⟨3721283, by rfl⟩ : syracuseStep 4961711 = 7442567) B7442567
theorem B1742303 : Blo 1740571 1742303 := bstep (se 1 (by rfl) ⟨1306727, by rfl⟩ : syracuseStep 1742303 = 2613455) B2613455
theorem B1742335 : Blo 1740571 1742335 := bstep (se 1 (by rfl) ⟨1306751, by rfl⟩ : syracuseStep 1742335 = 2613503) B2613503
theorem B20100635 : Blo 1740571 20100635 := bstep (se 1 (by rfl) ⟨15075476, by rfl⟩ : syracuseStep 20100635 = 30150953) B30150953
theorem B3626527 : Blo 1740571 3626527 := bstep (se 1 (by rfl) ⟨2719895, by rfl⟩ : syracuseStep 3626527 = 5439791) B5439791
theorem B2610857 : Blo 1740571 2610857 := bstep (se 2 (by rfl) ⟨979071, by rfl⟩ : syracuseStep 2610857 = 1958143) B1958143
theorem B2610863 : Blo 1740571 2610863 := bstep (se 1 (by rfl) ⟨1958147, by rfl⟩ : syracuseStep 2610863 = 3916295) B3916295
theorem B8812313 : Blo 1740571 8812313 := bstep (se 2 (by rfl) ⟨3304617, by rfl⟩ : syracuseStep 8812313 = 6609235) B6609235
theorem B2610983 : Blo 1740571 2610983 := bstep (se 1 (by rfl) ⟨1958237, by rfl⟩ : syracuseStep 2610983 = 3916475) B3916475
theorem B150574949 : Blo 1740571 150574949 := bstep (se 4 (by rfl) ⟨14116401, by rfl⟩ : syracuseStep 150574949 = 28232803) B28232803
theorem B9918409 : Blo 1740571 9918409 := bstep (se 2 (by rfl) ⟨3719403, by rfl⟩ : syracuseStep 9918409 = 7438807) B7438807
theorem B2611241 : Blo 1740571 2611241 := bstep (se 2 (by rfl) ⟨979215, by rfl⟩ : syracuseStep 2611241 = 1958431) B1958431
theorem B2611271 : Blo 1740571 2611271 := bstep (se 1 (by rfl) ⟨1958453, by rfl⟩ : syracuseStep 2611271 = 3916907) B3916907
theorem B6609023 : Blo 1740571 6609023 := bstep (se 1 (by rfl) ⟨4956767, by rfl⟩ : syracuseStep 6609023 = 9913535) B9913535
theorem B9918683 : Blo 1740571 9918683 := bstep (se 1 (by rfl) ⟨7439012, by rfl⟩ : syracuseStep 9918683 = 14878025) B14878025
theorem B2611583 : Blo 1740571 2611583 := bstep (se 1 (by rfl) ⟨1958687, by rfl⟩ : syracuseStep 2611583 = 3917375) B3917375
theorem B2611655 : Blo 1740571 2611655 := bstep (se 1 (by rfl) ⟨1958741, by rfl⟩ : syracuseStep 2611655 = 3917483) B3917483
theorem B8821223 : Blo 1740571 8821223 := bstep (se 1 (by rfl) ⟨6615917, by rfl⟩ : syracuseStep 8821223 = 13231835) B13231835
theorem B2611871 : Blo 1740571 2611871 := bstep (se 1 (by rfl) ⟨1958903, by rfl⟩ : syracuseStep 2611871 = 3917807) B3917807
theorem B4405985 : Blo 1740571 4405985 := bstep (se 2 (by rfl) ⟨1652244, by rfl⟩ : syracuseStep 4405985 = 3304489) B3304489
theorem B2612015 : Blo 1740571 2612015 := bstep (se 1 (by rfl) ⟨1959011, by rfl⟩ : syracuseStep 2612015 = 3918023) B3918023
theorem B7437167 : Blo 1740571 7437167 := bstep (se 1 (by rfl) ⟨5577875, by rfl⟩ : syracuseStep 7437167 = 11155751) B11155751
theorem B2612105 : Blo 1740571 2612105 := bstep (se 2 (by rfl) ⟨979539, by rfl⟩ : syracuseStep 2612105 = 1959079) B1959079
theorem B2612135 : Blo 1740571 2612135 := bstep (se 1 (by rfl) ⟨1959101, by rfl⟩ : syracuseStep 2612135 = 3918203) B3918203
theorem B37665881 : Blo 1740571 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B2612315 : Blo 1740571 2612315 := bstep (se 1 (by rfl) ⟨1959236, by rfl⟩ : syracuseStep 2612315 = 3918473) B3918473
theorem B2612507 : Blo 1740571 2612507 := bstep (se 1 (by rfl) ⟨1959380, by rfl⟩ : syracuseStep 2612507 = 3918761) B3918761
theorem B5578415 : Blo 1740571 5578415 := bstep (se 1 (by rfl) ⟨4183811, by rfl⟩ : syracuseStep 5578415 = 8367623) B8367623
theorem B2612975 : Blo 1740571 2612975 := bstep (se 1 (by rfl) ⟨1959731, by rfl⟩ : syracuseStep 2612975 = 3919463) B3919463
theorem B2203519 : Blo 1740571 2203519 := bstep (se 1 (by rfl) ⟨1652639, by rfl⟩ : syracuseStep 2203519 = 3305279) B3305279
theorem B2613161 : Blo 1740571 2613161 := bstep (se 2 (by rfl) ⟨979935, by rfl⟩ : syracuseStep 2613161 = 1959871) B1959871
theorem B3137491 : Blo 1740571 3137491 := bstep (se 1 (by rfl) ⟨2353118, by rfl⟩ : syracuseStep 3137491 = 4706237) B4706237
theorem B2613431 : Blo 1740571 2613431 := bstep (se 1 (by rfl) ⟨1960073, by rfl⟩ : syracuseStep 2613431 = 3920147) B3920147
theorem B2613551 : Blo 1740571 2613551 := bstep (se 1 (by rfl) ⟨1960163, by rfl⟩ : syracuseStep 2613551 = 3920327) B3920327
theorem B8814905 : Blo 1740571 8814905 := bstep (se 2 (by rfl) ⟨3305589, by rfl⟩ : syracuseStep 8814905 = 6611179) B6611179
theorem B2613743 : Blo 1740571 2613743 := bstep (se 1 (by rfl) ⟨1960307, by rfl⟩ : syracuseStep 2613743 = 3920615) B3920615
theorem B33489395 : Blo 1740571 33489395 := bstep (se 1 (by rfl) ⟨25117046, by rfl⟩ : syracuseStep 33489395 = 50234093) B50234093
theorem B2613791 : Blo 1740571 2613791 := bstep (se 1 (by rfl) ⟨1960343, by rfl⟩ : syracuseStep 2613791 = 3920687) B3920687
theorem B2548265 : Blo 1740571 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B2613851 : Blo 1740571 2613851 := bstep (se 1 (by rfl) ⟨1960388, by rfl⟩ : syracuseStep 2613851 = 3920777) B3920777
theorem B6611651 : Blo 1740571 6611651 := bstep (se 1 (by rfl) ⟨4958738, by rfl⟩ : syracuseStep 6611651 = 9917477) B9917477
theorem B3720019 : Blo 1740571 3720019 := bstep (se 1 (by rfl) ⟨2790014, by rfl⟩ : syracuseStep 3720019 = 5580029) B5580029
theorem B5874875 : Blo 1740571 5874875 := bstep (se 1 (by rfl) ⟨4406156, by rfl⟩ : syracuseStep 5874875 = 8812313) B8812313
theorem B3179839 : Blo 1740571 3179839 := bstep (se 1 (by rfl) ⟨2384879, by rfl⟩ : syracuseStep 3179839 = 4769759) B4769759
theorem B6612455 : Blo 1740571 6612455 := bstep (se 1 (by rfl) ⟨4959341, by rfl⟩ : syracuseStep 6612455 = 9918683) B9918683
theorem B3917339 : Blo 1740571 3917339 := bstep (se 1 (by rfl) ⟨2938004, by rfl⟩ : syracuseStep 3917339 = 5876009) B5876009
theorem B14878403 : Blo 1740571 14878403 := bstep (se 1 (by rfl) ⟨11158802, by rfl⟩ : syracuseStep 14878403 = 22317605) B22317605
theorem B4958111 : Blo 1740571 4958111 := bstep (se 1 (by rfl) ⟨3718583, by rfl⟩ : syracuseStep 4958111 = 7437167) B7437167
theorem B4409255 : Blo 1740571 4409255 := bstep (se 1 (by rfl) ⟨3306941, by rfl⟩ : syracuseStep 4409255 = 6613883) B6613883
theorem B4835369 : Blo 1740571 4835369 := bstep (se 2 (by rfl) ⟨1813263, by rfl⟩ : syracuseStep 4835369 = 3626527) B3626527
theorem B25110587 : Blo 1740571 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B110152219 : Blo 1740571 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B4409903 : Blo 1740571 4409903 := bstep (se 1 (by rfl) ⟨3307427, by rfl⟩ : syracuseStep 4409903 = 6614855) B6614855
theorem B13224545 : Blo 1740571 13224545 := bstep (se 2 (by rfl) ⟨4959204, by rfl⟩ : syracuseStep 13224545 = 9918409) B9918409
theorem B8817335 : Blo 1740571 8817335 := bstep (se 1 (by rfl) ⟨6613001, by rfl⟩ : syracuseStep 8817335 = 13226003) B13226003
theorem B29756321 : Blo 1740571 29756321 := bstep (se 2 (by rfl) ⟨11158620, by rfl⟩ : syracuseStep 29756321 = 22317241) B22317241
theorem B5876873 : Blo 1740571 5876873 := bstep (se 2 (by rfl) ⟨2203827, by rfl⟩ : syracuseStep 5876873 = 4407655) B4407655
theorem B7441577 : Blo 1740571 7441577 := bstep (se 2 (by rfl) ⟨2790591, by rfl⟩ : syracuseStep 7441577 = 5581183) B5581183
theorem B5876927 : Blo 1740571 5876927 := bstep (se 1 (by rfl) ⟨4407695, by rfl⟩ : syracuseStep 5876927 = 8815391) B8815391
theorem B16969067 : Blo 1740571 16969067 := bstep (se 1 (by rfl) ⟨12726800, by rfl⟩ : syracuseStep 16969067 = 25453601) B25453601
theorem B9416125 : Blo 1740571 9416125 := bstep (se 3 (by rfl) ⟨1765523, by rfl⟩ : syracuseStep 9416125 = 3531047) B3531047
theorem B3304937 : Blo 1740571 3304937 := bstep (se 2 (by rfl) ⟨1239351, by rfl⟩ : syracuseStep 3304937 = 2478703) B2478703
theorem B60321287 : Blo 1740571 60321287 := bstep (se 1 (by rfl) ⟨45240965, by rfl⟩ : syracuseStep 60321287 = 90481931) B90481931
theorem B7441951 : Blo 1740571 7441951 := bstep (se 1 (by rfl) ⟨5581463, by rfl⟩ : syracuseStep 7441951 = 11162927) B11162927
theorem B1740571 : Blo 1740571 1740571 := bstep (se 1 (by rfl) ⟨1305428, by rfl⟩ : syracuseStep 1740571 = 2610857) B2610857
theorem B1740575 : Blo 1740571 1740575 := bstep (se 1 (by rfl) ⟨1305431, by rfl⟩ : syracuseStep 1740575 = 2610863) B2610863
theorem B1740655 : Blo 1740571 1740655 := bstep (se 1 (by rfl) ⟨1305491, by rfl⟩ : syracuseStep 1740655 = 2610983) B2610983
theorem B1740827 : Blo 1740571 1740827 := bstep (se 1 (by rfl) ⟨1305620, by rfl⟩ : syracuseStep 1740827 = 2611241) B2611241
theorem B1740847 : Blo 1740571 1740847 := bstep (se 1 (by rfl) ⟨1305635, by rfl⟩ : syracuseStep 1740847 = 2611271) B2611271
theorem B1741055 : Blo 1740571 1741055 := bstep (se 1 (by rfl) ⟨1305791, by rfl⟩ : syracuseStep 1741055 = 2611583) B2611583
theorem B1741103 : Blo 1740571 1741103 := bstep (se 1 (by rfl) ⟨1305827, by rfl⟩ : syracuseStep 1741103 = 2611655) B2611655
theorem B1741247 : Blo 1740571 1741247 := bstep (se 1 (by rfl) ⟨1305935, by rfl⟩ : syracuseStep 1741247 = 2611871) B2611871
theorem B2937323 : Blo 1740571 2937323 := bstep (se 1 (by rfl) ⟨2202992, by rfl⟩ : syracuseStep 2937323 = 4405985) B4405985
theorem B1741343 : Blo 1740571 1741343 := bstep (se 1 (by rfl) ⟨1306007, by rfl⟩ : syracuseStep 1741343 = 2612015) B2612015
theorem B1741403 : Blo 1740571 1741403 := bstep (se 1 (by rfl) ⟨1306052, by rfl⟩ : syracuseStep 1741403 = 2612105) B2612105
theorem B1741423 : Blo 1740571 1741423 := bstep (se 1 (by rfl) ⟨1306067, by rfl⟩ : syracuseStep 1741423 = 2612135) B2612135
theorem B1741543 : Blo 1740571 1741543 := bstep (se 1 (by rfl) ⟨1306157, by rfl⟩ : syracuseStep 1741543 = 2612315) B2612315
theorem B6615827 : Blo 1740571 6615827 := bstep (se 1 (by rfl) ⟨4961870, by rfl⟩ : syracuseStep 6615827 = 9923741) B9923741
theorem B1741671 : Blo 1740571 1741671 := bstep (se 1 (by rfl) ⟨1306253, by rfl⟩ : syracuseStep 1741671 = 2612507) B2612507
theorem B5878763 : Blo 1740571 5878763 := bstep (se 1 (by rfl) ⟨4409072, by rfl⟩ : syracuseStep 5878763 = 8818145) B8818145
theorem B1741983 : Blo 1740571 1741983 := bstep (se 1 (by rfl) ⟨1306487, by rfl⟩ : syracuseStep 1741983 = 2612975) B2612975
theorem B2938025 : Blo 1740571 2938025 := bstep (se 2 (by rfl) ⟨1101759, by rfl⟩ : syracuseStep 2938025 = 2203519) B2203519
theorem B4183321 : Blo 1740571 4183321 := bstep (se 2 (by rfl) ⟨1568745, by rfl⟩ : syracuseStep 4183321 = 3137491) B3137491
theorem B1742107 : Blo 1740571 1742107 := bstep (se 1 (by rfl) ⟨1306580, by rfl⟩ : syracuseStep 1742107 = 2613161) B2613161
theorem B1742207 : Blo 1740571 1742207 := bstep (se 1 (by rfl) ⟨1306655, by rfl⟩ : syracuseStep 1742207 = 2613311) B2613311
theorem B1742363 : Blo 1740571 1742363 := bstep (se 1 (by rfl) ⟨1306772, by rfl⟩ : syracuseStep 1742363 = 2613545) B2613545
theorem B14882399 : Blo 1740571 14882399 := bstep (se 1 (by rfl) ⟨11161799, by rfl⟩ : syracuseStep 14882399 = 22323599) B22323599
theorem B1742543 : Blo 1740571 1742543 := bstep (se 1 (by rfl) ⟨1306907, by rfl⟩ : syracuseStep 1742543 = 2613815) B2613815
theorem B13227947 : Blo 1740571 13227947 := bstep (se 1 (by rfl) ⟨9920960, by rfl⟩ : syracuseStep 13227947 = 19841921) B19841921
theorem B2611439 : Blo 1740571 2611439 := bstep (se 1 (by rfl) ⟨1958579, by rfl⟩ : syracuseStep 2611439 = 3917159) B3917159
theorem B3307807 : Blo 1740571 3307807 := bstep (se 1 (by rfl) ⟨2480855, by rfl⟩ : syracuseStep 3307807 = 4961711) B4961711
theorem B2611511 : Blo 1740571 2611511 := bstep (se 1 (by rfl) ⟨1958633, by rfl⟩ : syracuseStep 2611511 = 3917267) B3917267
theorem B13400423 : Blo 1740571 13400423 := bstep (se 1 (by rfl) ⟨10050317, by rfl⟩ : syracuseStep 13400423 = 20100635) B20100635
theorem B3627391 : Blo 1740571 3627391 := bstep (se 1 (by rfl) ⟨2720543, by rfl⟩ : syracuseStep 3627391 = 5441087) B5441087
theorem B2611691 : Blo 1740571 2611691 := bstep (se 1 (by rfl) ⟨1958768, by rfl⟩ : syracuseStep 2611691 = 3917537) B3917537
theorem B100383299 : Blo 1740571 100383299 := bstep (se 1 (by rfl) ⟨75287474, by rfl⟩ : syracuseStep 100383299 = 150574949) B150574949
theorem B2939483 : Blo 1740571 2939483 := bstep (se 1 (by rfl) ⟨2204612, by rfl⟩ : syracuseStep 2939483 = 4409225) B4409225
theorem B4406015 : Blo 1740571 4406015 := bstep (se 1 (by rfl) ⟨3304511, by rfl⟩ : syracuseStep 4406015 = 6609023) B6609023
theorem B6363913 : Blo 1740571 6363913 := bstep (se 2 (by rfl) ⟨2386467, by rfl⟩ : syracuseStep 6363913 = 4772935) B4772935
theorem B5880815 : Blo 1740571 5880815 := bstep (se 1 (by rfl) ⟨4410611, by rfl⟩ : syracuseStep 5880815 = 8821223) B8821223
theorem B2612219 : Blo 1740571 2612219 := bstep (se 1 (by rfl) ⟨1959164, by rfl⟩ : syracuseStep 2612219 = 3918329) B3918329
theorem B2612279 : Blo 1740571 2612279 := bstep (se 1 (by rfl) ⟨1959209, by rfl⟩ : syracuseStep 2612279 = 3918419) B3918419
theorem B2612399 : Blo 1740571 2612399 := bstep (se 1 (by rfl) ⟨1959299, by rfl⟩ : syracuseStep 2612399 = 3918599) B3918599
theorem B2612459 : Blo 1740571 2612459 := bstep (se 1 (by rfl) ⟨1959344, by rfl⟩ : syracuseStep 2612459 = 3918689) B3918689
theorem B11156777 : Blo 1740571 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B37658195 : Blo 1740571 37658195 := bstep (se 1 (by rfl) ⟨28243646, by rfl⟩ : syracuseStep 37658195 = 56487293) B56487293
theorem B3718943 : Blo 1740571 3718943 := bstep (se 1 (by rfl) ⟨2789207, by rfl⟩ : syracuseStep 3718943 = 5578415) B5578415
theorem B2613071 : Blo 1740571 2613071 := bstep (se 1 (by rfl) ⟨1959803, by rfl⟩ : syracuseStep 2613071 = 3919607) B3919607
theorem B2613083 : Blo 1740571 2613083 := bstep (se 1 (by rfl) ⟨1959812, by rfl⟩ : syracuseStep 2613083 = 3919625) B3919625
theorem B2613119 : Blo 1740571 2613119 := bstep (se 1 (by rfl) ⟨1959839, by rfl⟩ : syracuseStep 2613119 = 3919679) B3919679
theorem B2613191 : Blo 1740571 2613191 := bstep (se 1 (by rfl) ⟨1959893, by rfl⟩ : syracuseStep 2613191 = 3919787) B3919787
theorem B66961565 : Blo 1740571 66961565 := bstep (se 3 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 66961565 = 25110587) B25110587
theorem B1958215 : Blo 1740571 1958215 := bstep (se 1 (by rfl) ⟨1468661, by rfl⟩ : syracuseStep 1958215 = 2937323) B2937323
theorem B27181493 : Blo 1740571 27181493 := bstep (se 5 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 27181493 = 2548265) B2548265
theorem B4407767 : Blo 1740571 4407767 := bstep (se 1 (by rfl) ⟨3305825, by rfl⟩ : syracuseStep 4407767 = 6611651) B6611651
theorem B1958683 : Blo 1740571 1958683 := bstep (se 1 (by rfl) ⟨1469012, by rfl⟩ : syracuseStep 1958683 = 2938025) B2938025
theorem B3916583 : Blo 1740571 3916583 := bstep (se 1 (by rfl) ⟨2937437, by rfl⟩ : syracuseStep 3916583 = 5874875) B5874875
theorem B4408303 : Blo 1740571 4408303 := bstep (se 1 (by rfl) ⟨3306227, by rfl⟩ : syracuseStep 4408303 = 6612455) B6612455
theorem B9921599 : Blo 1740571 9921599 := bstep (se 1 (by rfl) ⟨7441199, by rfl⟩ : syracuseStep 9921599 = 14882399) B14882399
theorem B66922199 : Blo 1740571 66922199 := bstep (se 1 (by rfl) ⟨50191649, by rfl⟩ : syracuseStep 66922199 = 100383299) B100383299
theorem B1959655 : Blo 1740571 1959655 := bstep (se 1 (by rfl) ⟨1469741, by rfl⟩ : syracuseStep 1959655 = 2939483) B2939483
theorem B8816363 : Blo 1740571 8816363 := bstep (se 1 (by rfl) ⟨6612272, by rfl⟩ : syracuseStep 8816363 = 13224545) B13224545
theorem B9922601 : Blo 1740571 9922601 := bstep (se 2 (by rfl) ⟨3720975, by rfl⟩ : syracuseStep 9922601 = 7441951) B7441951
theorem B3917915 : Blo 1740571 3917915 := bstep (se 1 (by rfl) ⟨2938436, by rfl⟩ : syracuseStep 3917915 = 5876873) B5876873
theorem B3917951 : Blo 1740571 3917951 := bstep (se 1 (by rfl) ⟨2938463, by rfl⟩ : syracuseStep 3917951 = 5876927) B5876927
theorem B5876603 : Blo 1740571 5876603 := bstep (se 1 (by rfl) ⟨4407452, by rfl⟩ : syracuseStep 5876603 = 8814905) B8814905
theorem B22326263 : Blo 1740571 22326263 := bstep (se 1 (by rfl) ⟨16744697, by rfl⟩ : syracuseStep 22326263 = 33489395) B33489395
theorem B4410409 : Blo 1740571 4410409 := bstep (se 2 (by rfl) ⟨1653903, by rfl⟩ : syracuseStep 4410409 = 3307807) B3307807
theorem B4836521 : Blo 1740571 4836521 := bstep (se 2 (by rfl) ⟨1813695, by rfl⟩ : syracuseStep 4836521 = 3627391) B3627391
theorem B4410551 : Blo 1740571 4410551 := bstep (se 1 (by rfl) ⟨3307913, by rfl⟩ : syracuseStep 4410551 = 6615827) B6615827
theorem B3919175 : Blo 1740571 3919175 := bstep (se 1 (by rfl) ⟨2939381, by rfl⟩ : syracuseStep 3919175 = 5878763) B5878763
theorem B146869625 : Blo 1740571 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B4960025 : Blo 1740571 4960025 := bstep (se 2 (by rfl) ⟨1860009, by rfl⟩ : syracuseStep 4960025 = 3720019) B3720019
theorem B8818631 : Blo 1740571 8818631 := bstep (se 1 (by rfl) ⟨6613973, by rfl⟩ : syracuseStep 8818631 = 13227947) B13227947
theorem B3223579 : Blo 1740571 3223579 := bstep (se 1 (by rfl) ⟨2417684, by rfl⟩ : syracuseStep 3223579 = 4835369) B4835369
theorem B1740959 : Blo 1740571 1740959 := bstep (se 1 (by rfl) ⟨1305719, by rfl⟩ : syracuseStep 1740959 = 2611439) B2611439
theorem B1741007 : Blo 1740571 1741007 := bstep (se 1 (by rfl) ⟨1305755, by rfl⟩ : syracuseStep 1741007 = 2611511) B2611511
theorem B8933615 : Blo 1740571 8933615 := bstep (se 1 (by rfl) ⟨6700211, by rfl⟩ : syracuseStep 8933615 = 13400423) B13400423
theorem B1741127 : Blo 1740571 1741127 := bstep (se 1 (by rfl) ⟨1305845, by rfl⟩ : syracuseStep 1741127 = 2611691) B2611691
theorem B4239785 : Blo 1740571 4239785 := bstep (se 2 (by rfl) ⟨1589919, by rfl⟩ : syracuseStep 4239785 = 3179839) B3179839
theorem B5878223 : Blo 1740571 5878223 := bstep (se 1 (by rfl) ⟨4408667, by rfl⟩ : syracuseStep 5878223 = 8817335) B8817335
theorem B2937343 : Blo 1740571 2937343 := bstep (se 1 (by rfl) ⟨2203007, by rfl⟩ : syracuseStep 2937343 = 4406015) B4406015
theorem B12554833 : Blo 1740571 12554833 := bstep (se 2 (by rfl) ⟨4708062, by rfl⟩ : syracuseStep 12554833 = 9416125) B9416125
theorem B19837547 : Blo 1740571 19837547 := bstep (se 1 (by rfl) ⟨14878160, by rfl⟩ : syracuseStep 19837547 = 29756321) B29756321
theorem B3920543 : Blo 1740571 3920543 := bstep (se 1 (by rfl) ⟨2940407, by rfl⟩ : syracuseStep 3920543 = 5880815) B5880815
theorem B1741479 : Blo 1740571 1741479 := bstep (se 1 (by rfl) ⟨1306109, by rfl⟩ : syracuseStep 1741479 = 2612219) B2612219
theorem B1741519 : Blo 1740571 1741519 := bstep (se 1 (by rfl) ⟨1306139, by rfl⟩ : syracuseStep 1741519 = 2612279) B2612279
theorem B4961051 : Blo 1740571 4961051 := bstep (se 1 (by rfl) ⟨3720788, by rfl⟩ : syracuseStep 4961051 = 7441577) B7441577
theorem B1741599 : Blo 1740571 1741599 := bstep (se 1 (by rfl) ⟨1306199, by rfl⟩ : syracuseStep 1741599 = 2612399) B2612399
theorem B1741639 : Blo 1740571 1741639 := bstep (se 1 (by rfl) ⟨1306229, by rfl⟩ : syracuseStep 1741639 = 2612459) B2612459
theorem B25105463 : Blo 1740571 25105463 := bstep (se 1 (by rfl) ⟨18829097, by rfl⟩ : syracuseStep 25105463 = 37658195) B37658195
theorem B2479295 : Blo 1740571 2479295 := bstep (se 1 (by rfl) ⟨1859471, by rfl⟩ : syracuseStep 2479295 = 3718943) B3718943
theorem B1742047 : Blo 1740571 1742047 := bstep (se 1 (by rfl) ⟨1306535, by rfl⟩ : syracuseStep 1742047 = 2613071) B2613071
theorem B1742055 : Blo 1740571 1742055 := bstep (se 1 (by rfl) ⟨1306541, by rfl⟩ : syracuseStep 1742055 = 2613083) B2613083
theorem B1742079 : Blo 1740571 1742079 := bstep (se 1 (by rfl) ⟨1306559, by rfl⟩ : syracuseStep 1742079 = 2613119) B2613119
theorem B1742127 : Blo 1740571 1742127 := bstep (se 1 (by rfl) ⟨1306595, by rfl⟩ : syracuseStep 1742127 = 2613191) B2613191
theorem B1742287 : Blo 1740571 1742287 := bstep (se 1 (by rfl) ⟨1306715, by rfl⟩ : syracuseStep 1742287 = 2613431) B2613431
theorem B1742367 : Blo 1740571 1742367 := bstep (se 1 (by rfl) ⟨1306775, by rfl⟩ : syracuseStep 1742367 = 2613551) B2613551
theorem B1742495 : Blo 1740571 1742495 := bstep (se 1 (by rfl) ⟨1306871, by rfl⟩ : syracuseStep 1742495 = 2613743) B2613743
theorem B1742527 : Blo 1740571 1742527 := bstep (se 1 (by rfl) ⟨1306895, by rfl⟩ : syracuseStep 1742527 = 2613791) B2613791
theorem B1742567 : Blo 1740571 1742567 := bstep (se 1 (by rfl) ⟨1306925, by rfl⟩ : syracuseStep 1742567 = 2613851) B2613851
theorem B8485217 : Blo 1740571 8485217 := bstep (se 2 (by rfl) ⟨3181956, by rfl⟩ : syracuseStep 8485217 = 6363913) B6363913
theorem B2611559 : Blo 1740571 2611559 := bstep (se 1 (by rfl) ⟨1958669, by rfl⟩ : syracuseStep 2611559 = 3917339) B3917339
theorem B9918935 : Blo 1740571 9918935 := bstep (se 1 (by rfl) ⟨7439201, by rfl⟩ : syracuseStep 9918935 = 14878403) B14878403
theorem B2939503 : Blo 1740571 2939503 := bstep (se 1 (by rfl) ⟨2204627, by rfl⟩ : syracuseStep 2939503 = 4409255) B4409255
theorem B2939935 : Blo 1740571 2939935 := bstep (se 1 (by rfl) ⟨2204951, by rfl⟩ : syracuseStep 2939935 = 4409903) B4409903
theorem B5577761 : Blo 1740571 5577761 := bstep (se 2 (by rfl) ⟨2091660, by rfl⟩ : syracuseStep 5577761 = 4183321) B4183321
theorem B7437851 : Blo 1740571 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B11312711 : Blo 1740571 11312711 := bstep (se 1 (by rfl) ⟨8484533, by rfl⟩ : syracuseStep 11312711 = 16969067) B16969067
theorem B2203291 : Blo 1740571 2203291 := bstep (se 1 (by rfl) ⟨1652468, by rfl⟩ : syracuseStep 2203291 = 3304937) B3304937
theorem B40214191 : Blo 1740571 40214191 := bstep (se 1 (by rfl) ⟨30160643, by rfl⟩ : syracuseStep 40214191 = 60321287) B60321287
theorem B13221629 : Blo 1740571 13221629 := bstep (se 3 (by rfl) ⟨2479055, by rfl⟩ : syracuseStep 13221629 = 4958111) B4958111
theorem B5955743 : Blo 1740571 5955743 := bstep (se 1 (by rfl) ⟨4466807, by rfl⟩ : syracuseStep 5955743 = 8933615) B8933615
theorem B2826523 : Blo 1740571 2826523 := bstep (se 1 (by rfl) ⟨2119892, by rfl⟩ : syracuseStep 2826523 = 4239785) B4239785
theorem B18120995 : Blo 1740571 18120995 := bstep (se 1 (by rfl) ⟨13590746, by rfl⟩ : syracuseStep 18120995 = 27181493) B27181493
theorem B2613695 : Blo 1740571 2613695 := bstep (se 1 (by rfl) ⟨1960271, by rfl⟩ : syracuseStep 2613695 = 3920543) B3920543
theorem B6611453 : Blo 1740571 6611453 := bstep (se 3 (by rfl) ⟨1239647, by rfl⟩ : syracuseStep 6611453 = 2479295) B2479295
theorem B3916457 : Blo 1740571 3916457 := bstep (se 2 (by rfl) ⟨1468671, by rfl⟩ : syracuseStep 3916457 = 2937343) B2937343
theorem B16736975 : Blo 1740571 16736975 := bstep (se 1 (by rfl) ⟨12552731, by rfl⟩ : syracuseStep 16736975 = 25105463) B25105463
theorem B44614799 : Blo 1740571 44614799 := bstep (se 1 (by rfl) ⟨33461099, by rfl⟩ : syracuseStep 44614799 = 66922199) B66922199
theorem B6612623 : Blo 1740571 6612623 := bstep (se 1 (by rfl) ⟨4959467, by rfl⟩ : syracuseStep 6612623 = 9918935) B9918935
theorem B3917735 : Blo 1740571 3917735 := bstep (se 1 (by rfl) ⟨2938301, by rfl⟩ : syracuseStep 3917735 = 5876603) B5876603
theorem B53618921 : Blo 1740571 53618921 := bstep (se 2 (by rfl) ⟨20107095, by rfl⟩ : syracuseStep 53618921 = 40214191) B40214191
theorem B97913083 : Blo 1740571 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B4958567 : Blo 1740571 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B44641043 : Blo 1740571 44641043 := bstep (se 1 (by rfl) ⟨33480782, by rfl⟩ : syracuseStep 44641043 = 66961565) B66961565
theorem B3918815 : Blo 1740571 3918815 := bstep (se 1 (by rfl) ⟨2939111, by rfl⟩ : syracuseStep 3918815 = 5878223) B5878223
theorem B13225031 : Blo 1740571 13225031 := bstep (se 1 (by rfl) ⟨9918773, by rfl⟩ : syracuseStep 13225031 = 19837547) B19837547
theorem B12897389 : Blo 1740571 12897389 := bstep (se 3 (by rfl) ⟨2418260, by rfl⟩ : syracuseStep 12897389 = 4836521) B4836521
theorem B6614399 : Blo 1740571 6614399 := bstep (se 1 (by rfl) ⟨4960799, by rfl⟩ : syracuseStep 6614399 = 9921599) B9921599
theorem B16739777 : Blo 1740571 16739777 := bstep (se 2 (by rfl) ⟨6277416, by rfl⟩ : syracuseStep 16739777 = 12554833) B12554833
theorem B3919337 : Blo 1740571 3919337 := bstep (se 2 (by rfl) ⟨1469751, by rfl⟩ : syracuseStep 3919337 = 2939503) B2939503
theorem B5877575 : Blo 1740571 5877575 := bstep (se 1 (by rfl) ⟨4408181, by rfl⟩ : syracuseStep 5877575 = 8816363) B8816363
theorem B5877737 : Blo 1740571 5877737 := bstep (se 2 (by rfl) ⟨2204151, by rfl⟩ : syracuseStep 5877737 = 4408303) B4408303
theorem B6615067 : Blo 1740571 6615067 := bstep (se 1 (by rfl) ⟨4961300, by rfl⟩ : syracuseStep 6615067 = 9922601) B9922601
theorem B3919913 : Blo 1740571 3919913 := bstep (se 2 (by rfl) ⟨1469967, by rfl⟩ : syracuseStep 3919913 = 2939935) B2939935
theorem B5656811 : Blo 1740571 5656811 := bstep (se 1 (by rfl) ⟨4242608, by rfl⟩ : syracuseStep 5656811 = 8485217) B8485217
theorem B1741039 : Blo 1740571 1741039 := bstep (se 1 (by rfl) ⟨1305779, by rfl⟩ : syracuseStep 1741039 = 2611559) B2611559
theorem B2937721 : Blo 1740571 2937721 := bstep (se 2 (by rfl) ⟨1101645, by rfl⟩ : syracuseStep 2937721 = 2203291) B2203291
theorem B7541807 : Blo 1740571 7541807 := bstep (se 1 (by rfl) ⟨5656355, by rfl⟩ : syracuseStep 7541807 = 11312711) B11312711
theorem B3306683 : Blo 1740571 3306683 := bstep (se 1 (by rfl) ⟨2480012, by rfl⟩ : syracuseStep 3306683 = 4960025) B4960025
theorem B5879087 : Blo 1740571 5879087 := bstep (se 1 (by rfl) ⟨4409315, by rfl⟩ : syracuseStep 5879087 = 8818631) B8818631
theorem B4298105 : Blo 1740571 4298105 := bstep (se 2 (by rfl) ⟨1611789, by rfl⟩ : syracuseStep 4298105 = 3223579) B3223579
theorem B14874029 : Blo 1740571 14874029 := bstep (se 3 (by rfl) ⟨2788880, by rfl⟩ : syracuseStep 14874029 = 5577761) B5577761
theorem B2938511 : Blo 1740571 2938511 := bstep (se 1 (by rfl) ⟨2203883, by rfl⟩ : syracuseStep 2938511 = 4407767) B4407767
theorem B2610953 : Blo 1740571 2610953 := bstep (se 2 (by rfl) ⟨979107, by rfl⟩ : syracuseStep 2610953 = 1958215) B1958215
theorem B3307367 : Blo 1740571 3307367 := bstep (se 1 (by rfl) ⟨2480525, by rfl⟩ : syracuseStep 3307367 = 4961051) B4961051
theorem B2611055 : Blo 1740571 2611055 := bstep (se 1 (by rfl) ⟨1958291, by rfl⟩ : syracuseStep 2611055 = 3916583) B3916583
theorem B2611577 : Blo 1740571 2611577 := bstep (se 2 (by rfl) ⟨979341, by rfl⟩ : syracuseStep 2611577 = 1958683) B1958683
theorem B5880545 : Blo 1740571 5880545 := bstep (se 2 (by rfl) ⟨2205204, by rfl⟩ : syracuseStep 5880545 = 4410409) B4410409
theorem B2611943 : Blo 1740571 2611943 := bstep (se 1 (by rfl) ⟨1958957, by rfl⟩ : syracuseStep 2611943 = 3917915) B3917915
theorem B2611967 : Blo 1740571 2611967 := bstep (se 1 (by rfl) ⟨1958975, by rfl⟩ : syracuseStep 2611967 = 3917951) B3917951
theorem B14884175 : Blo 1740571 14884175 := bstep (se 1 (by rfl) ⟨11163131, by rfl⟩ : syracuseStep 14884175 = 22326263) B22326263
theorem B2940367 : Blo 1740571 2940367 := bstep (se 1 (by rfl) ⟨2205275, by rfl⟩ : syracuseStep 2940367 = 4410551) B4410551
theorem B2612783 : Blo 1740571 2612783 := bstep (se 1 (by rfl) ⟨1959587, by rfl⟩ : syracuseStep 2612783 = 3919175) B3919175
theorem B2612873 : Blo 1740571 2612873 := bstep (se 2 (by rfl) ⟨979827, by rfl⟩ : syracuseStep 2612873 = 1959655) B1959655
theorem B8814419 : Blo 1740571 8814419 := bstep (se 1 (by rfl) ⟨6610814, by rfl⟩ : syracuseStep 8814419 = 13221629) B13221629
theorem B2613275 : Blo 1740571 2613275 := bstep (se 1 (by rfl) ⟨1959956, by rfl⟩ : syracuseStep 2613275 = 3919913) B3919913
theorem B20111485 : Blo 1740571 20111485 := bstep (se 3 (by rfl) ⟨3770903, by rfl⟩ : syracuseStep 20111485 = 7541807) B7541807
theorem B4407635 : Blo 1740571 4407635 := bstep (se 1 (by rfl) ⟨3305726, by rfl⟩ : syracuseStep 4407635 = 6611453) B6611453
theorem B3768697 : Blo 1740571 3768697 := bstep (se 2 (by rfl) ⟨1413261, by rfl⟩ : syracuseStep 3768697 = 2826523) B2826523
theorem B11157983 : Blo 1740571 11157983 := bstep (se 1 (by rfl) ⟨8368487, by rfl⟩ : syracuseStep 11157983 = 16736975) B16736975
theorem B1959007 : Blo 1740571 1959007 := bstep (se 1 (by rfl) ⟨1469255, by rfl⟩ : syracuseStep 1959007 = 2938511) B2938511
theorem B4408415 : Blo 1740571 4408415 := bstep (se 1 (by rfl) ⟨3306311, by rfl⟩ : syracuseStep 4408415 = 6612623) B6612623
theorem B3916961 : Blo 1740571 3916961 := bstep (se 2 (by rfl) ⟨1468860, by rfl⟩ : syracuseStep 3916961 = 2937721) B2937721
theorem B2204911 : Blo 1740571 2204911 := bstep (se 1 (by rfl) ⟨1653683, by rfl⟩ : syracuseStep 2204911 = 3307367) B3307367
theorem B8816687 : Blo 1740571 8816687 := bstep (se 1 (by rfl) ⟨6612515, by rfl⟩ : syracuseStep 8816687 = 13225031) B13225031
theorem B9922783 : Blo 1740571 9922783 := bstep (se 1 (by rfl) ⟨7442087, by rfl⟩ : syracuseStep 9922783 = 14884175) B14884175
theorem B4409599 : Blo 1740571 4409599 := bstep (se 1 (by rfl) ⟨3307199, by rfl⟩ : syracuseStep 4409599 = 6614399) B6614399
theorem B11159851 : Blo 1740571 11159851 := bstep (se 1 (by rfl) ⟨8369888, by rfl⟩ : syracuseStep 11159851 = 16739777) B16739777
theorem B3918383 : Blo 1740571 3918383 := bstep (se 1 (by rfl) ⟨2938787, by rfl⟩ : syracuseStep 3918383 = 5877575) B5877575
theorem B5876279 : Blo 1740571 5876279 := bstep (se 1 (by rfl) ⟨4407209, by rfl⟩ : syracuseStep 5876279 = 8814419) B8814419
theorem B3918491 : Blo 1740571 3918491 := bstep (se 1 (by rfl) ⟨2938868, by rfl⟩ : syracuseStep 3918491 = 5877737) B5877737
theorem B130550777 : Blo 1740571 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B8817821 : Blo 1740571 8817821 := bstep (se 3 (by rfl) ⟨1653341, by rfl⟩ : syracuseStep 8817821 = 3306683) B3306683
theorem B15084829 : Blo 1740571 15084829 := bstep (se 3 (by rfl) ⟨2828405, by rfl⟩ : syracuseStep 15084829 = 5656811) B5656811
theorem B3919391 : Blo 1740571 3919391 := bstep (se 1 (by rfl) ⟨2939543, by rfl⟩ : syracuseStep 3919391 = 5879087) B5879087
theorem B9916019 : Blo 1740571 9916019 := bstep (se 1 (by rfl) ⟨7437014, by rfl⟩ : syracuseStep 9916019 = 14874029) B14874029
theorem B1740635 : Blo 1740571 1740635 := bstep (se 1 (by rfl) ⟨1305476, by rfl⟩ : syracuseStep 1740635 = 2610953) B2610953
theorem B1740703 : Blo 1740571 1740703 := bstep (se 1 (by rfl) ⟨1305527, by rfl⟩ : syracuseStep 1740703 = 2611055) B2611055
theorem B35745947 : Blo 1740571 35745947 := bstep (se 1 (by rfl) ⟨26809460, by rfl⟩ : syracuseStep 35745947 = 53618921) B53618921
theorem B3305711 : Blo 1740571 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B1741051 : Blo 1740571 1741051 := bstep (se 1 (by rfl) ⟨1305788, by rfl⟩ : syracuseStep 1741051 = 2611577) B2611577
theorem B3920363 : Blo 1740571 3920363 := bstep (se 1 (by rfl) ⟨2940272, by rfl⟩ : syracuseStep 3920363 = 5880545) B5880545
theorem B1741295 : Blo 1740571 1741295 := bstep (se 1 (by rfl) ⟨1305971, by rfl⟩ : syracuseStep 1741295 = 2611943) B2611943
theorem B1741311 : Blo 1740571 1741311 := bstep (se 1 (by rfl) ⟨1305983, by rfl⟩ : syracuseStep 1741311 = 2611967) B2611967
theorem B3920489 : Blo 1740571 3920489 := bstep (se 2 (by rfl) ⟨1470183, by rfl⟩ : syracuseStep 3920489 = 2940367) B2940367
theorem B8598259 : Blo 1740571 8598259 := bstep (se 1 (by rfl) ⟨6448694, by rfl⟩ : syracuseStep 8598259 = 12897389) B12897389
theorem B1741855 : Blo 1740571 1741855 := bstep (se 1 (by rfl) ⟨1306391, by rfl⟩ : syracuseStep 1741855 = 2612783) B2612783
theorem B1741915 : Blo 1740571 1741915 := bstep (se 1 (by rfl) ⟨1306436, by rfl⟩ : syracuseStep 1741915 = 2612873) B2612873
theorem B8820089 : Blo 1740571 8820089 := bstep (se 2 (by rfl) ⟨3307533, by rfl⟩ : syracuseStep 8820089 = 6615067) B6615067
theorem B3970495 : Blo 1740571 3970495 := bstep (se 1 (by rfl) ⟨2977871, by rfl⟩ : syracuseStep 3970495 = 5955743) B5955743
theorem B12080663 : Blo 1740571 12080663 := bstep (se 1 (by rfl) ⟨9060497, by rfl⟩ : syracuseStep 12080663 = 18120995) B18120995
theorem B1742463 : Blo 1740571 1742463 := bstep (se 1 (by rfl) ⟨1306847, by rfl⟩ : syracuseStep 1742463 = 2613695) B2613695
theorem B2610971 : Blo 1740571 2610971 := bstep (se 1 (by rfl) ⟨1958228, by rfl⟩ : syracuseStep 2610971 = 3916457) B3916457
theorem B29743199 : Blo 1740571 29743199 := bstep (se 1 (by rfl) ⟨22307399, by rfl⟩ : syracuseStep 29743199 = 44614799) B44614799
theorem B2865403 : Blo 1740571 2865403 := bstep (se 1 (by rfl) ⟨2149052, by rfl⟩ : syracuseStep 2865403 = 4298105) B4298105
theorem B2611823 : Blo 1740571 2611823 := bstep (se 1 (by rfl) ⟨1958867, by rfl⟩ : syracuseStep 2611823 = 3917735) B3917735
theorem B29760695 : Blo 1740571 29760695 := bstep (se 1 (by rfl) ⟨22320521, by rfl⟩ : syracuseStep 29760695 = 44641043) B44641043
theorem B2612543 : Blo 1740571 2612543 := bstep (se 1 (by rfl) ⟨1959407, by rfl⟩ : syracuseStep 2612543 = 3918815) B3918815
theorem B2612891 : Blo 1740571 2612891 := bstep (se 1 (by rfl) ⟨1959668, by rfl⟩ : syracuseStep 2612891 = 3919337) B3919337
theorem B23830631 : Blo 1740571 23830631 := bstep (se 1 (by rfl) ⟨17872973, by rfl⟩ : syracuseStep 23830631 = 35745947) B35745947
theorem B13230377 : Blo 1740571 13230377 := bstep (se 2 (by rfl) ⟨4961391, by rfl⟩ : syracuseStep 13230377 = 9922783) B9922783
theorem B7438655 : Blo 1740571 7438655 := bstep (se 1 (by rfl) ⟨5578991, by rfl⟩ : syracuseStep 7438655 = 11157983) B11157983
theorem B2613575 : Blo 1740571 2613575 := bstep (se 1 (by rfl) ⟨1960181, by rfl⟩ : syracuseStep 2613575 = 3920363) B3920363
theorem B2613659 : Blo 1740571 2613659 := bstep (se 1 (by rfl) ⟨1960244, by rfl⟩ : syracuseStep 2613659 = 3920489) B3920489
theorem B8815229 : Blo 1740571 8815229 := bstep (se 3 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 8815229 = 3305711) B3305711
theorem B8053775 : Blo 1740571 8053775 := bstep (se 1 (by rfl) ⟨6040331, by rfl⟩ : syracuseStep 8053775 = 12080663) B12080663
theorem B3917519 : Blo 1740571 3917519 := bstep (se 1 (by rfl) ⟨2938139, by rfl⟩ : syracuseStep 3917519 = 5876279) B5876279
theorem B20113105 : Blo 1740571 20113105 := bstep (se 2 (by rfl) ⟨7542414, by rfl⟩ : syracuseStep 20113105 = 15084829) B15084829
theorem B5293993 : Blo 1740571 5293993 := bstep (se 2 (by rfl) ⟨1985247, by rfl⟩ : syracuseStep 5293993 = 3970495) B3970495
theorem B87033851 : Blo 1740571 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B26815313 : Blo 1740571 26815313 := bstep (se 2 (by rfl) ⟨10055742, by rfl⟩ : syracuseStep 26815313 = 20111485) B20111485
theorem B3820537 : Blo 1740571 3820537 := bstep (se 2 (by rfl) ⟨1432701, by rfl⟩ : syracuseStep 3820537 = 2865403) B2865403
theorem B14879801 : Blo 1740571 14879801 := bstep (se 2 (by rfl) ⟨5579925, by rfl⟩ : syracuseStep 14879801 = 11159851) B11159851
theorem B5024929 : Blo 1740571 5024929 := bstep (se 2 (by rfl) ⟨1884348, by rfl⟩ : syracuseStep 5024929 = 3768697) B3768697
theorem B11464345 : Blo 1740571 11464345 := bstep (se 2 (by rfl) ⟨4299129, by rfl⟩ : syracuseStep 11464345 = 8598259) B8598259
theorem B1740647 : Blo 1740571 1740647 := bstep (se 1 (by rfl) ⟨1305485, by rfl⟩ : syracuseStep 1740647 = 2610971) B2610971
theorem B5877791 : Blo 1740571 5877791 := bstep (se 1 (by rfl) ⟨4408343, by rfl⟩ : syracuseStep 5877791 = 8816687) B8816687
theorem B19828799 : Blo 1740571 19828799 := bstep (se 1 (by rfl) ⟨14871599, by rfl⟩ : syracuseStep 19828799 = 29743199) B29743199
theorem B1741215 : Blo 1740571 1741215 := bstep (se 1 (by rfl) ⟨1305911, by rfl⟩ : syracuseStep 1741215 = 2611823) B2611823
theorem B5878547 : Blo 1740571 5878547 := bstep (se 1 (by rfl) ⟨4408910, by rfl⟩ : syracuseStep 5878547 = 8817821) B8817821
theorem B1741695 : Blo 1740571 1741695 := bstep (se 1 (by rfl) ⟨1306271, by rfl⟩ : syracuseStep 1741695 = 2612543) B2612543
theorem B1741927 : Blo 1740571 1741927 := bstep (se 1 (by rfl) ⟨1306445, by rfl⟩ : syracuseStep 1741927 = 2612891) B2612891
theorem B1742183 : Blo 1740571 1742183 := bstep (se 1 (by rfl) ⟨1306637, by rfl⟩ : syracuseStep 1742183 = 2613275) B2613275
theorem B2938423 : Blo 1740571 2938423 := bstep (se 1 (by rfl) ⟨2203817, by rfl⟩ : syracuseStep 2938423 = 4407635) B4407635
theorem B5879465 : Blo 1740571 5879465 := bstep (se 2 (by rfl) ⟨2204799, by rfl⟩ : syracuseStep 5879465 = 4409599) B4409599
theorem B2938943 : Blo 1740571 2938943 := bstep (se 1 (by rfl) ⟨2204207, by rfl⟩ : syracuseStep 2938943 = 4408415) B4408415
theorem B2611307 : Blo 1740571 2611307 := bstep (se 1 (by rfl) ⟨1958480, by rfl⟩ : syracuseStep 2611307 = 3916961) B3916961
theorem B5880059 : Blo 1740571 5880059 := bstep (se 1 (by rfl) ⟨4410044, by rfl⟩ : syracuseStep 5880059 = 8820089) B8820089
theorem B2612009 : Blo 1740571 2612009 := bstep (se 2 (by rfl) ⟨979503, by rfl⟩ : syracuseStep 2612009 = 1959007) B1959007
theorem B2939881 : Blo 1740571 2939881 := bstep (se 2 (by rfl) ⟨1102455, by rfl⟩ : syracuseStep 2939881 = 2204911) B2204911
theorem B2612255 : Blo 1740571 2612255 := bstep (se 1 (by rfl) ⟨1959191, by rfl⟩ : syracuseStep 2612255 = 3918383) B3918383
theorem B2612327 : Blo 1740571 2612327 := bstep (se 1 (by rfl) ⟨1959245, by rfl⟩ : syracuseStep 2612327 = 3918491) B3918491
theorem B19840463 : Blo 1740571 19840463 := bstep (se 1 (by rfl) ⟨14880347, by rfl⟩ : syracuseStep 19840463 = 29760695) B29760695
theorem B2612927 : Blo 1740571 2612927 := bstep (se 1 (by rfl) ⟨1959695, by rfl⟩ : syracuseStep 2612927 = 3919391) B3919391
theorem B6610679 : Blo 1740571 6610679 := bstep (se 1 (by rfl) ⟨4958009, by rfl⟩ : syracuseStep 6610679 = 9916019) B9916019
theorem B1959295 : Blo 1740571 1959295 := bstep (se 1 (by rfl) ⟨1469471, by rfl⟩ : syracuseStep 1959295 = 2938943) B2938943
theorem B17876875 : Blo 1740571 17876875 := bstep (se 1 (by rfl) ⟨13407656, by rfl⟩ : syracuseStep 17876875 = 26815313) B26815313
theorem B3917897 : Blo 1740571 3917897 := bstep (se 2 (by rfl) ⟨1469211, by rfl⟩ : syracuseStep 3917897 = 2938423) B2938423
theorem B20376197 : Blo 1740571 20376197 := bstep (se 4 (by rfl) ⟨1910268, by rfl⟩ : syracuseStep 20376197 = 3820537) B3820537
theorem B3918527 : Blo 1740571 3918527 := bstep (se 1 (by rfl) ⟨2938895, by rfl⟩ : syracuseStep 3918527 = 5877791) B5877791
theorem B15887087 : Blo 1740571 15887087 := bstep (se 1 (by rfl) ⟨11915315, by rfl⟩ : syracuseStep 15887087 = 23830631) B23830631
theorem B4959103 : Blo 1740571 4959103 := bstep (se 1 (by rfl) ⟨3719327, by rfl⟩ : syracuseStep 4959103 = 7438655) B7438655
theorem B5876819 : Blo 1740571 5876819 := bstep (se 1 (by rfl) ⟨4407614, by rfl⟩ : syracuseStep 5876819 = 8815229) B8815229
theorem B3919031 : Blo 1740571 3919031 := bstep (se 1 (by rfl) ⟨2939273, by rfl⟩ : syracuseStep 3919031 = 5878547) B5878547
theorem B5369183 : Blo 1740571 5369183 := bstep (se 1 (by rfl) ⟨4026887, by rfl⟩ : syracuseStep 5369183 = 8053775) B8053775
theorem B3919643 : Blo 1740571 3919643 := bstep (se 1 (by rfl) ⟨2939732, by rfl⟩ : syracuseStep 3919643 = 5879465) B5879465
theorem B3919841 : Blo 1740571 3919841 := bstep (se 2 (by rfl) ⟨1469940, by rfl⟩ : syracuseStep 3919841 = 2939881) B2939881
theorem B1740871 : Blo 1740571 1740871 := bstep (se 1 (by rfl) ⟨1305653, by rfl⟩ : syracuseStep 1740871 = 2611307) B2611307
theorem B3920039 : Blo 1740571 3920039 := bstep (se 1 (by rfl) ⟨2940029, by rfl⟩ : syracuseStep 3920039 = 5880059) B5880059
theorem B1741339 : Blo 1740571 1741339 := bstep (se 1 (by rfl) ⟨1306004, by rfl⟩ : syracuseStep 1741339 = 2612009) B2612009
theorem B1741503 : Blo 1740571 1741503 := bstep (se 1 (by rfl) ⟨1306127, by rfl⟩ : syracuseStep 1741503 = 2612255) B2612255
theorem B1741551 : Blo 1740571 1741551 := bstep (se 1 (by rfl) ⟨1306163, by rfl⟩ : syracuseStep 1741551 = 2612327) B2612327
theorem B26817473 : Blo 1740571 26817473 := bstep (se 2 (by rfl) ⟨10056552, by rfl⟩ : syracuseStep 26817473 = 20113105) B20113105
theorem B13226975 : Blo 1740571 13226975 := bstep (se 1 (by rfl) ⟨9920231, by rfl⟩ : syracuseStep 13226975 = 19840463) B19840463
theorem B1741951 : Blo 1740571 1741951 := bstep (se 1 (by rfl) ⟨1306463, by rfl⟩ : syracuseStep 1741951 = 2612927) B2612927
theorem B7058657 : Blo 1740571 7058657 := bstep (se 2 (by rfl) ⟨2646996, by rfl⟩ : syracuseStep 7058657 = 5293993) B5293993
theorem B13219199 : Blo 1740571 13219199 := bstep (se 1 (by rfl) ⟨9914399, by rfl⟩ : syracuseStep 13219199 = 19828799) B19828799
theorem B8820251 : Blo 1740571 8820251 := bstep (se 1 (by rfl) ⟨6615188, by rfl⟩ : syracuseStep 8820251 = 13230377) B13230377
theorem B1742383 : Blo 1740571 1742383 := bstep (se 1 (by rfl) ⟨1306787, by rfl⟩ : syracuseStep 1742383 = 2613575) B2613575
theorem B1742439 : Blo 1740571 1742439 := bstep (se 1 (by rfl) ⟨1306829, by rfl⟩ : syracuseStep 1742439 = 2613659) B2613659
theorem B2611679 : Blo 1740571 2611679 := bstep (se 1 (by rfl) ⟨1958759, by rfl⟩ : syracuseStep 2611679 = 3917519) B3917519
theorem B58022567 : Blo 1740571 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B6699905 : Blo 1740571 6699905 := bstep (se 2 (by rfl) ⟨2512464, by rfl⟩ : syracuseStep 6699905 = 5024929) B5024929
theorem B9919867 : Blo 1740571 9919867 := bstep (se 1 (by rfl) ⟨7439900, by rfl⟩ : syracuseStep 9919867 = 14879801) B14879801
theorem B15285793 : Blo 1740571 15285793 := bstep (se 2 (by rfl) ⟨5732172, by rfl⟩ : syracuseStep 15285793 = 11464345) B11464345
theorem B4407119 : Blo 1740571 4407119 := bstep (se 1 (by rfl) ⟨3305339, by rfl⟩ : syracuseStep 4407119 = 6610679) B6610679
theorem B2613359 : Blo 1740571 2613359 := bstep (se 1 (by rfl) ⟨1960019, by rfl⟩ : syracuseStep 2613359 = 3920039) B3920039
theorem B6612137 : Blo 1740571 6612137 := bstep (se 2 (by rfl) ⟨2479551, by rfl⟩ : syracuseStep 6612137 = 4959103) B4959103
theorem B13584131 : Blo 1740571 13584131 := bstep (se 1 (by rfl) ⟨10188098, by rfl⟩ : syracuseStep 13584131 = 20376197) B20376197
theorem B4466603 : Blo 1740571 4466603 := bstep (se 1 (by rfl) ⟨3349952, by rfl⟩ : syracuseStep 4466603 = 6699905) B6699905
theorem B3917879 : Blo 1740571 3917879 := bstep (se 1 (by rfl) ⟨2938409, by rfl⟩ : syracuseStep 3917879 = 5876819) B5876819
theorem B17878315 : Blo 1740571 17878315 := bstep (se 1 (by rfl) ⟨13408736, by rfl⟩ : syracuseStep 17878315 = 26817473) B26817473
theorem B8817983 : Blo 1740571 8817983 := bstep (se 1 (by rfl) ⟨6613487, by rfl⟩ : syracuseStep 8817983 = 13226975) B13226975
theorem B4705771 : Blo 1740571 4705771 := bstep (se 1 (by rfl) ⟨3529328, by rfl⟩ : syracuseStep 4705771 = 7058657) B7058657
theorem B1741119 : Blo 1740571 1741119 := bstep (se 1 (by rfl) ⟨1305839, by rfl⟩ : syracuseStep 1741119 = 2611679) B2611679
theorem B13226489 : Blo 1740571 13226489 := bstep (se 2 (by rfl) ⟨4959933, by rfl⟩ : syracuseStep 13226489 = 9919867) B9919867
theorem B23835833 : Blo 1740571 23835833 := bstep (se 2 (by rfl) ⟨8938437, by rfl⟩ : syracuseStep 23835833 = 17876875) B17876875
theorem B2938079 : Blo 1740571 2938079 := bstep (se 1 (by rfl) ⟨2203559, by rfl⟩ : syracuseStep 2938079 = 4407119) B4407119
theorem B8812799 : Blo 1740571 8812799 := bstep (se 1 (by rfl) ⟨6609599, by rfl⟩ : syracuseStep 8812799 = 13219199) B13219199
theorem B5880167 : Blo 1740571 5880167 := bstep (se 1 (by rfl) ⟨4410125, by rfl⟩ : syracuseStep 5880167 = 8820251) B8820251
theorem B2611931 : Blo 1740571 2611931 := bstep (se 1 (by rfl) ⟨1958948, by rfl⟩ : syracuseStep 2611931 = 3917897) B3917897
theorem B38681711 : Blo 1740571 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B2612351 : Blo 1740571 2612351 := bstep (se 1 (by rfl) ⟨1959263, by rfl⟩ : syracuseStep 2612351 = 3918527) B3918527
theorem B10591391 : Blo 1740571 10591391 := bstep (se 1 (by rfl) ⟨7943543, by rfl⟩ : syracuseStep 10591391 = 15887087) B15887087
theorem B2612393 : Blo 1740571 2612393 := bstep (se 2 (by rfl) ⟨979647, by rfl⟩ : syracuseStep 2612393 = 1959295) B1959295
theorem B20381057 : Blo 1740571 20381057 := bstep (se 2 (by rfl) ⟨7642896, by rfl⟩ : syracuseStep 20381057 = 15285793) B15285793
theorem B2612687 : Blo 1740571 2612687 := bstep (se 1 (by rfl) ⟨1959515, by rfl⟩ : syracuseStep 2612687 = 3919031) B3919031
theorem B3579455 : Blo 1740571 3579455 := bstep (se 1 (by rfl) ⟨2684591, by rfl⟩ : syracuseStep 3579455 = 5369183) B5369183
theorem B2613095 : Blo 1740571 2613095 := bstep (se 1 (by rfl) ⟨1959821, by rfl⟩ : syracuseStep 2613095 = 3919643) B3919643
theorem B2613227 : Blo 1740571 2613227 := bstep (se 1 (by rfl) ⟨1959920, by rfl⟩ : syracuseStep 2613227 = 3919841) B3919841
theorem B4408091 : Blo 1740571 4408091 := bstep (se 1 (by rfl) ⟨3306068, by rfl⟩ : syracuseStep 4408091 = 6612137) B6612137
theorem B1958719 : Blo 1740571 1958719 := bstep (se 1 (by rfl) ⟨1469039, by rfl⟩ : syracuseStep 1958719 = 2938079) B2938079
theorem B5875199 : Blo 1740571 5875199 := bstep (se 1 (by rfl) ⟨4406399, by rfl⟩ : syracuseStep 5875199 = 8812799) B8812799
theorem B2386303 : Blo 1740571 2386303 := bstep (se 1 (by rfl) ⟨1789727, by rfl⟩ : syracuseStep 2386303 = 3579455) B3579455
theorem B8817659 : Blo 1740571 8817659 := bstep (se 1 (by rfl) ⟨6613244, by rfl⟩ : syracuseStep 8817659 = 13226489) B13226489
theorem B9056087 : Blo 1740571 9056087 := bstep (se 1 (by rfl) ⟨6792065, by rfl⟩ : syracuseStep 9056087 = 13584131) B13584131
theorem B2977735 : Blo 1740571 2977735 := bstep (se 1 (by rfl) ⟨2233301, by rfl⟩ : syracuseStep 2977735 = 4466603) B4466603
theorem B3920111 : Blo 1740571 3920111 := bstep (se 1 (by rfl) ⟨2940083, by rfl⟩ : syracuseStep 3920111 = 5880167) B5880167
theorem B1741287 : Blo 1740571 1741287 := bstep (se 1 (by rfl) ⟨1305965, by rfl⟩ : syracuseStep 1741287 = 2611931) B2611931
theorem B1741567 : Blo 1740571 1741567 := bstep (se 1 (by rfl) ⟨1306175, by rfl⟩ : syracuseStep 1741567 = 2612351) B2612351
theorem B1741595 : Blo 1740571 1741595 := bstep (se 1 (by rfl) ⟨1306196, by rfl⟩ : syracuseStep 1741595 = 2612393) B2612393
theorem B5878655 : Blo 1740571 5878655 := bstep (se 1 (by rfl) ⟨4408991, by rfl⟩ : syracuseStep 5878655 = 8817983) B8817983
theorem B13587371 : Blo 1740571 13587371 := bstep (se 1 (by rfl) ⟨10190528, by rfl⟩ : syracuseStep 13587371 = 20381057) B20381057
theorem B1741791 : Blo 1740571 1741791 := bstep (se 1 (by rfl) ⟨1306343, by rfl⟩ : syracuseStep 1741791 = 2612687) B2612687
theorem B1742063 : Blo 1740571 1742063 := bstep (se 1 (by rfl) ⟨1306547, by rfl⟩ : syracuseStep 1742063 = 2613095) B2613095
theorem B1742151 : Blo 1740571 1742151 := bstep (se 1 (by rfl) ⟨1306613, by rfl⟩ : syracuseStep 1742151 = 2613227) B2613227
theorem B1742239 : Blo 1740571 1742239 := bstep (se 1 (by rfl) ⟨1306679, by rfl⟩ : syracuseStep 1742239 = 2613359) B2613359
theorem B15890555 : Blo 1740571 15890555 := bstep (se 1 (by rfl) ⟨11917916, by rfl⟩ : syracuseStep 15890555 = 23835833) B23835833
theorem B2611919 : Blo 1740571 2611919 := bstep (se 1 (by rfl) ⟨1958939, by rfl⟩ : syracuseStep 2611919 = 3917879) B3917879
theorem B23837753 : Blo 1740571 23837753 := bstep (se 2 (by rfl) ⟨8939157, by rfl⟩ : syracuseStep 23837753 = 17878315) B17878315
theorem B6274361 : Blo 1740571 6274361 := bstep (se 2 (by rfl) ⟨2352885, by rfl⟩ : syracuseStep 6274361 = 4705771) B4705771
theorem B25787807 : Blo 1740571 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B7060927 : Blo 1740571 7060927 := bstep (se 1 (by rfl) ⟨5295695, by rfl⟩ : syracuseStep 7060927 = 10591391) B10591391
theorem B2613407 : Blo 1740571 2613407 := bstep (se 1 (by rfl) ⟨1960055, by rfl⟩ : syracuseStep 2613407 = 3920111) B3920111
theorem B3916799 : Blo 1740571 3916799 := bstep (se 1 (by rfl) ⟨2937599, by rfl⟩ : syracuseStep 3916799 = 5875199) B5875199
theorem B10593703 : Blo 1740571 10593703 := bstep (se 1 (by rfl) ⟨7945277, by rfl⟩ : syracuseStep 10593703 = 15890555) B15890555
theorem B9414569 : Blo 1740571 9414569 := bstep (se 2 (by rfl) ⟨3530463, by rfl⟩ : syracuseStep 9414569 = 7060927) B7060927
theorem B3919103 : Blo 1740571 3919103 := bstep (se 1 (by rfl) ⟨2939327, by rfl⟩ : syracuseStep 3919103 = 5878655) B5878655
theorem B16731629 : Blo 1740571 16731629 := bstep (se 3 (by rfl) ⟨3137180, by rfl⟩ : syracuseStep 16731629 = 6274361) B6274361
theorem B1741279 : Blo 1740571 1741279 := bstep (se 1 (by rfl) ⟨1305959, by rfl⟩ : syracuseStep 1741279 = 2611919) B2611919
theorem B12726949 : Blo 1740571 12726949 := bstep (se 4 (by rfl) ⟨1193151, by rfl⟩ : syracuseStep 12726949 = 2386303) B2386303
theorem B5878439 : Blo 1740571 5878439 := bstep (se 1 (by rfl) ⟨4408829, by rfl⟩ : syracuseStep 5878439 = 8817659) B8817659
theorem B17191871 : Blo 1740571 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B3970313 : Blo 1740571 3970313 := bstep (se 2 (by rfl) ⟨1488867, by rfl⟩ : syracuseStep 3970313 = 2977735) B2977735
theorem B2938727 : Blo 1740571 2938727 := bstep (se 1 (by rfl) ⟨2204045, by rfl⟩ : syracuseStep 2938727 = 4408091) B4408091
theorem B9058247 : Blo 1740571 9058247 := bstep (se 1 (by rfl) ⟨6793685, by rfl⟩ : syracuseStep 9058247 = 13587371) B13587371
theorem B2611625 : Blo 1740571 2611625 := bstep (se 2 (by rfl) ⟨979359, by rfl⟩ : syracuseStep 2611625 = 1958719) B1958719
theorem B15891835 : Blo 1740571 15891835 := bstep (se 1 (by rfl) ⟨11918876, by rfl⟩ : syracuseStep 15891835 = 23837753) B23837753
theorem B6037391 : Blo 1740571 6037391 := bstep (se 1 (by rfl) ⟨4528043, by rfl⟩ : syracuseStep 6037391 = 9056087) B9056087
theorem B11461247 : Blo 1740571 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B2646875 : Blo 1740571 2646875 := bstep (se 1 (by rfl) ⟨1985156, by rfl⟩ : syracuseStep 2646875 = 3970313) B3970313
theorem B1959151 : Blo 1740571 1959151 := bstep (se 1 (by rfl) ⟨1469363, by rfl⟩ : syracuseStep 1959151 = 2938727) B2938727
theorem B6276379 : Blo 1740571 6276379 := bstep (se 1 (by rfl) ⟨4707284, by rfl⟩ : syracuseStep 6276379 = 9414569) B9414569
theorem B6038831 : Blo 1740571 6038831 := bstep (se 1 (by rfl) ⟨4529123, by rfl⟩ : syracuseStep 6038831 = 9058247) B9058247
theorem B14124937 : Blo 1740571 14124937 := bstep (se 2 (by rfl) ⟨5296851, by rfl⟩ : syracuseStep 14124937 = 10593703) B10593703
theorem B4024927 : Blo 1740571 4024927 := bstep (se 1 (by rfl) ⟨3018695, by rfl⟩ : syracuseStep 4024927 = 6037391) B6037391
theorem B3918959 : Blo 1740571 3918959 := bstep (se 1 (by rfl) ⟨2939219, by rfl⟩ : syracuseStep 3918959 = 5878439) B5878439
theorem B16969265 : Blo 1740571 16969265 := bstep (se 2 (by rfl) ⟨6363474, by rfl⟩ : syracuseStep 16969265 = 12726949) B12726949
theorem B1741083 : Blo 1740571 1741083 := bstep (se 1 (by rfl) ⟨1305812, by rfl⟩ : syracuseStep 1741083 = 2611625) B2611625
theorem B21189113 : Blo 1740571 21189113 := bstep (se 2 (by rfl) ⟨7945917, by rfl⟩ : syracuseStep 21189113 = 15891835) B15891835
theorem B11154419 : Blo 1740571 11154419 := bstep (se 1 (by rfl) ⟨8365814, by rfl⟩ : syracuseStep 11154419 = 16731629) B16731629
theorem B1742271 : Blo 1740571 1742271 := bstep (se 1 (by rfl) ⟨1306703, by rfl⟩ : syracuseStep 1742271 = 2613407) B2613407
theorem B2611199 : Blo 1740571 2611199 := bstep (se 1 (by rfl) ⟨1958399, by rfl⟩ : syracuseStep 2611199 = 3916799) B3916799
theorem B2612735 : Blo 1740571 2612735 := bstep (se 1 (by rfl) ⟨1959551, by rfl⟩ : syracuseStep 2612735 = 3919103) B3919103
theorem B5366569 : Blo 1740571 5366569 := bstep (se 2 (by rfl) ⟨2012463, by rfl⟩ : syracuseStep 5366569 = 4024927) B4024927
theorem B14126075 : Blo 1740571 14126075 := bstep (se 1 (by rfl) ⟨10594556, by rfl⟩ : syracuseStep 14126075 = 21189113) B21189113
theorem B1740799 : Blo 1740571 1740799 := bstep (se 1 (by rfl) ⟨1305599, by rfl⟩ : syracuseStep 1740799 = 2611199) B2611199
theorem B8368505 : Blo 1740571 8368505 := bstep (se 2 (by rfl) ⟨3138189, by rfl⟩ : syracuseStep 8368505 = 6276379) B6276379
theorem B7058333 : Blo 1740571 7058333 := bstep (se 3 (by rfl) ⟨1323437, by rfl⟩ : syracuseStep 7058333 = 2646875) B2646875
theorem B1741823 : Blo 1740571 1741823 := bstep (se 1 (by rfl) ⟨1306367, by rfl⟩ : syracuseStep 1741823 = 2612735) B2612735
theorem B7640831 : Blo 1740571 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B7436279 : Blo 1740571 7436279 := bstep (se 1 (by rfl) ⟨5577209, by rfl⟩ : syracuseStep 7436279 = 11154419) B11154419
theorem B16103549 : Blo 1740571 16103549 := bstep (se 3 (by rfl) ⟨3019415, by rfl⟩ : syracuseStep 16103549 = 6038831) B6038831
theorem B2612201 : Blo 1740571 2612201 := bstep (se 2 (by rfl) ⟨979575, by rfl⟩ : syracuseStep 2612201 = 1959151) B1959151
theorem B2612639 : Blo 1740571 2612639 := bstep (se 1 (by rfl) ⟨1959479, by rfl⟩ : syracuseStep 2612639 = 3918959) B3918959
theorem B11312843 : Blo 1740571 11312843 := bstep (se 1 (by rfl) ⟨8484632, by rfl⟩ : syracuseStep 11312843 = 16969265) B16969265
theorem B18833249 : Blo 1740571 18833249 := bstep (se 2 (by rfl) ⟨7062468, by rfl⟩ : syracuseStep 18833249 = 14124937) B14124937
theorem B5579003 : Blo 1740571 5579003 := bstep (se 1 (by rfl) ⟨4184252, by rfl⟩ : syracuseStep 5579003 = 8368505) B8368505
theorem B4957519 : Blo 1740571 4957519 := bstep (se 1 (by rfl) ⟨3718139, by rfl⟩ : syracuseStep 4957519 = 7436279) B7436279
theorem B20375549 : Blo 1740571 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B4705555 : Blo 1740571 4705555 := bstep (se 1 (by rfl) ⟨3529166, by rfl⟩ : syracuseStep 4705555 = 7058333) B7058333
theorem B7155425 : Blo 1740571 7155425 := bstep (se 2 (by rfl) ⟨2683284, by rfl⟩ : syracuseStep 7155425 = 5366569) B5366569
theorem B10735699 : Blo 1740571 10735699 := bstep (se 1 (by rfl) ⟨8051774, by rfl⟩ : syracuseStep 10735699 = 16103549) B16103549
theorem B30167581 : Blo 1740571 30167581 := bstep (se 3 (by rfl) ⟨5656421, by rfl⟩ : syracuseStep 30167581 = 11312843) B11312843
theorem B1741467 : Blo 1740571 1741467 := bstep (se 1 (by rfl) ⟨1306100, by rfl⟩ : syracuseStep 1741467 = 2612201) B2612201
theorem B9417383 : Blo 1740571 9417383 := bstep (se 1 (by rfl) ⟨7063037, by rfl⟩ : syracuseStep 9417383 = 14126075) B14126075
theorem B1741759 : Blo 1740571 1741759 := bstep (se 1 (by rfl) ⟨1306319, by rfl⟩ : syracuseStep 1741759 = 2612639) B2612639
theorem B12555499 : Blo 1740571 12555499 := bstep (se 1 (by rfl) ⟨9416624, by rfl⟩ : syracuseStep 12555499 = 18833249) B18833249
theorem B14877341 : Blo 1740571 14877341 := bstep (se 3 (by rfl) ⟨2789501, by rfl⟩ : syracuseStep 14877341 = 5579003) B5579003
theorem B40223441 : Blo 1740571 40223441 := bstep (se 2 (by rfl) ⟨15083790, by rfl⟩ : syracuseStep 40223441 = 30167581) B30167581
theorem B13583699 : Blo 1740571 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B4770283 : Blo 1740571 4770283 := bstep (se 1 (by rfl) ⟨3577712, by rfl⟩ : syracuseStep 4770283 = 7155425) B7155425
theorem B14314265 : Blo 1740571 14314265 := bstep (se 2 (by rfl) ⟨5367849, by rfl⟩ : syracuseStep 14314265 = 10735699) B10735699
theorem B6278255 : Blo 1740571 6278255 := bstep (se 1 (by rfl) ⟨4708691, by rfl⟩ : syracuseStep 6278255 = 9417383) B9417383
theorem B16740665 : Blo 1740571 16740665 := bstep (se 2 (by rfl) ⟨6277749, by rfl⟩ : syracuseStep 16740665 = 12555499) B12555499
theorem B6274073 : Blo 1740571 6274073 := bstep (se 2 (by rfl) ⟨2352777, by rfl⟩ : syracuseStep 6274073 = 4705555) B4705555
theorem B6610025 : Blo 1740571 6610025 := bstep (se 2 (by rfl) ⟨2478759, by rfl⟩ : syracuseStep 6610025 = 4957519) B4957519
theorem B11160443 : Blo 1740571 11160443 := bstep (se 1 (by rfl) ⟨8370332, by rfl⟩ : syracuseStep 11160443 = 16740665) B16740665
theorem B26815627 : Blo 1740571 26815627 := bstep (se 1 (by rfl) ⟨20111720, by rfl⟩ : syracuseStep 26815627 = 40223441) B40223441
theorem B6360377 : Blo 1740571 6360377 := bstep (se 2 (by rfl) ⟨2385141, by rfl⟩ : syracuseStep 6360377 = 4770283) B4770283
theorem B9055799 : Blo 1740571 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B4182715 : Blo 1740571 4182715 := bstep (se 1 (by rfl) ⟨3137036, by rfl⟩ : syracuseStep 4182715 = 6274073) B6274073
theorem B9918227 : Blo 1740571 9918227 := bstep (se 1 (by rfl) ⟨7438670, by rfl⟩ : syracuseStep 9918227 = 14877341) B14877341
theorem B9542843 : Blo 1740571 9542843 := bstep (se 1 (by rfl) ⟨7157132, by rfl⟩ : syracuseStep 9542843 = 14314265) B14314265
theorem B4406683 : Blo 1740571 4406683 := bstep (se 1 (by rfl) ⟨3305012, by rfl⟩ : syracuseStep 4406683 = 6610025) B6610025
theorem B4185503 : Blo 1740571 4185503 := bstep (se 1 (by rfl) ⟨3139127, by rfl⟩ : syracuseStep 4185503 = 6278255) B6278255
theorem B6612151 : Blo 1740571 6612151 := bstep (se 1 (by rfl) ⟨4959113, by rfl⟩ : syracuseStep 6612151 = 9918227) B9918227
theorem B5875577 : Blo 1740571 5875577 := bstep (se 2 (by rfl) ⟨2203341, by rfl⟩ : syracuseStep 5875577 = 4406683) B4406683
theorem B7440295 : Blo 1740571 7440295 := bstep (se 1 (by rfl) ⟨5580221, by rfl⟩ : syracuseStep 7440295 = 11160443) B11160443
theorem B16961005 : Blo 1740571 16961005 := bstep (se 3 (by rfl) ⟨3180188, by rfl⟩ : syracuseStep 16961005 = 6360377) B6360377
theorem B35754169 : Blo 1740571 35754169 := bstep (se 2 (by rfl) ⟨13407813, by rfl⟩ : syracuseStep 35754169 = 26815627) B26815627
theorem B6361895 : Blo 1740571 6361895 := bstep (se 1 (by rfl) ⟨4771421, by rfl⟩ : syracuseStep 6361895 = 9542843) B9542843
theorem B2790335 : Blo 1740571 2790335 := bstep (se 1 (by rfl) ⟨2092751, by rfl⟩ : syracuseStep 2790335 = 4185503) B4185503
theorem B5576953 : Blo 1740571 5576953 := bstep (se 2 (by rfl) ⟨2091357, by rfl⟩ : syracuseStep 5576953 = 4182715) B4182715
theorem B6037199 : Blo 1740571 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B3917051 : Blo 1740571 3917051 := bstep (se 1 (by rfl) ⟨2937788, by rfl⟩ : syracuseStep 3917051 = 5875577) B5875577
theorem B8816201 : Blo 1740571 8816201 := bstep (se 2 (by rfl) ⟨3306075, by rfl⟩ : syracuseStep 8816201 = 6612151) B6612151
theorem B4024799 : Blo 1740571 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B7440893 : Blo 1740571 7440893 := bstep (se 3 (by rfl) ⟨1395167, by rfl⟩ : syracuseStep 7440893 = 2790335) B2790335
theorem B90458693 : Blo 1740571 90458693 := bstep (se 4 (by rfl) ⟨8480502, by rfl⟩ : syracuseStep 90458693 = 16961005) B16961005
theorem B47672225 : Blo 1740571 47672225 := bstep (se 2 (by rfl) ⟨17877084, by rfl⟩ : syracuseStep 47672225 = 35754169) B35754169
theorem B7435937 : Blo 1740571 7435937 := bstep (se 2 (by rfl) ⟨2788476, by rfl⟩ : syracuseStep 7435937 = 5576953) B5576953
theorem B4241263 : Blo 1740571 4241263 := bstep (se 1 (by rfl) ⟨3180947, by rfl⟩ : syracuseStep 4241263 = 6361895) B6361895
theorem B9920393 : Blo 1740571 9920393 := bstep (se 2 (by rfl) ⟨3720147, by rfl⟩ : syracuseStep 9920393 = 7440295) B7440295
theorem B4957291 : Blo 1740571 4957291 := bstep (se 1 (by rfl) ⟨3717968, by rfl⟩ : syracuseStep 4957291 = 7435937) B7435937
theorem B5655017 : Blo 1740571 5655017 := bstep (se 2 (by rfl) ⟨2120631, by rfl⟩ : syracuseStep 5655017 = 4241263) B4241263
theorem B6613595 : Blo 1740571 6613595 := bstep (se 1 (by rfl) ⟨4960196, by rfl⟩ : syracuseStep 6613595 = 9920393) B9920393
theorem B5877467 : Blo 1740571 5877467 := bstep (se 1 (by rfl) ⟨4408100, by rfl⟩ : syracuseStep 5877467 = 8816201) B8816201
theorem B2683199 : Blo 1740571 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B4960595 : Blo 1740571 4960595 := bstep (se 1 (by rfl) ⟨3720446, by rfl⟩ : syracuseStep 4960595 = 7440893) B7440893
theorem B60305795 : Blo 1740571 60305795 := bstep (se 1 (by rfl) ⟨45229346, by rfl⟩ : syracuseStep 60305795 = 90458693) B90458693
theorem B31781483 : Blo 1740571 31781483 := bstep (se 1 (by rfl) ⟨23836112, by rfl⟩ : syracuseStep 31781483 = 47672225) B47672225
theorem B2611367 : Blo 1740571 2611367 := bstep (se 1 (by rfl) ⟨1958525, by rfl⟩ : syracuseStep 2611367 = 3917051) B3917051
theorem B3770011 : Blo 1740571 3770011 := bstep (se 1 (by rfl) ⟨2827508, by rfl⟩ : syracuseStep 3770011 = 5655017) B5655017
theorem B4409063 : Blo 1740571 4409063 := bstep (se 1 (by rfl) ⟨3306797, by rfl⟩ : syracuseStep 4409063 = 6613595) B6613595
theorem B3918311 : Blo 1740571 3918311 := bstep (se 1 (by rfl) ⟨2938733, by rfl⟩ : syracuseStep 3918311 = 5877467) B5877467
theorem B1788799 : Blo 1740571 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B21187655 : Blo 1740571 21187655 := bstep (se 1 (by rfl) ⟨15890741, by rfl⟩ : syracuseStep 21187655 = 31781483) B31781483
theorem B1740911 : Blo 1740571 1740911 := bstep (se 1 (by rfl) ⟨1305683, by rfl⟩ : syracuseStep 1740911 = 2611367) B2611367
theorem B3307063 : Blo 1740571 3307063 := bstep (se 1 (by rfl) ⟨2480297, by rfl⟩ : syracuseStep 3307063 = 4960595) B4960595
theorem B40203863 : Blo 1740571 40203863 := bstep (se 1 (by rfl) ⟨30152897, by rfl⟩ : syracuseStep 40203863 = 60305795) B60305795
theorem B6609721 : Blo 1740571 6609721 := bstep (se 2 (by rfl) ⟨2478645, by rfl⟩ : syracuseStep 6609721 = 4957291) B4957291
theorem B2385065 : Blo 1740571 2385065 := bstep (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) B1788799
theorem B14125103 : Blo 1740571 14125103 := bstep (se 1 (by rfl) ⟨10593827, by rfl⟩ : syracuseStep 14125103 = 21187655) B21187655
theorem B4409417 : Blo 1740571 4409417 := bstep (se 2 (by rfl) ⟨1653531, by rfl⟩ : syracuseStep 4409417 = 3307063) B3307063
theorem B5026681 : Blo 1740571 5026681 := bstep (se 2 (by rfl) ⟨1885005, by rfl⟩ : syracuseStep 5026681 = 3770011) B3770011
theorem B26802575 : Blo 1740571 26802575 := bstep (se 1 (by rfl) ⟨20101931, by rfl⟩ : syracuseStep 26802575 = 40203863) B40203863
theorem B8812961 : Blo 1740571 8812961 := bstep (se 2 (by rfl) ⟨3304860, by rfl⟩ : syracuseStep 8812961 = 6609721) B6609721
theorem B2939375 : Blo 1740571 2939375 := bstep (se 1 (by rfl) ⟨2204531, by rfl⟩ : syracuseStep 2939375 = 4409063) B4409063
theorem B2612207 : Blo 1740571 2612207 := bstep (se 1 (by rfl) ⟨1959155, by rfl⟩ : syracuseStep 2612207 = 3918311) B3918311
theorem B17868383 : Blo 1740571 17868383 := bstep (se 1 (by rfl) ⟨13401287, by rfl⟩ : syracuseStep 17868383 = 26802575) B26802575
theorem B5875307 : Blo 1740571 5875307 := bstep (se 1 (by rfl) ⟨4406480, by rfl⟩ : syracuseStep 5875307 = 8812961) B8812961
theorem B1959583 : Blo 1740571 1959583 := bstep (se 1 (by rfl) ⟨1469687, by rfl⟩ : syracuseStep 1959583 = 2939375) B2939375
theorem B6360173 : Blo 1740571 6360173 := bstep (se 3 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 6360173 = 2385065) B2385065
theorem B9416735 : Blo 1740571 9416735 := bstep (se 1 (by rfl) ⟨7062551, by rfl⟩ : syracuseStep 9416735 = 14125103) B14125103
theorem B26808965 : Blo 1740571 26808965 := bstep (se 4 (by rfl) ⟨2513340, by rfl⟩ : syracuseStep 26808965 = 5026681) B5026681
theorem B1741471 : Blo 1740571 1741471 := bstep (se 1 (by rfl) ⟨1306103, by rfl⟩ : syracuseStep 1741471 = 2612207) B2612207
theorem B2939611 : Blo 1740571 2939611 := bstep (se 1 (by rfl) ⟨2204708, by rfl⟩ : syracuseStep 2939611 = 4409417) B4409417
theorem B11912255 : Blo 1740571 11912255 := bstep (se 1 (by rfl) ⟨8934191, by rfl⟩ : syracuseStep 11912255 = 17868383) B17868383
theorem B3916871 : Blo 1740571 3916871 := bstep (se 1 (by rfl) ⟨2937653, by rfl⟩ : syracuseStep 3916871 = 5875307) B5875307
theorem B6277823 : Blo 1740571 6277823 := bstep (se 1 (by rfl) ⟨4708367, by rfl⟩ : syracuseStep 6277823 = 9416735) B9416735
theorem B3919481 : Blo 1740571 3919481 := bstep (se 2 (by rfl) ⟨1469805, by rfl⟩ : syracuseStep 3919481 = 2939611) B2939611
theorem B4240115 : Blo 1740571 4240115 := bstep (se 1 (by rfl) ⟨3180086, by rfl⟩ : syracuseStep 4240115 = 6360173) B6360173
theorem B17872643 : Blo 1740571 17872643 := bstep (se 1 (by rfl) ⟨13404482, by rfl⟩ : syracuseStep 17872643 = 26808965) B26808965
theorem B2612777 : Blo 1740571 2612777 := bstep (se 2 (by rfl) ⟨979791, by rfl⟩ : syracuseStep 2612777 = 1959583) B1959583
theorem B2826743 : Blo 1740571 2826743 := bstep (se 1 (by rfl) ⟨2120057, by rfl⟩ : syracuseStep 2826743 = 4240115) B4240115
theorem B7941503 : Blo 1740571 7941503 := bstep (se 1 (by rfl) ⟨5956127, by rfl⟩ : syracuseStep 7941503 = 11912255) B11912255
theorem B11915095 : Blo 1740571 11915095 := bstep (se 1 (by rfl) ⟨8936321, by rfl⟩ : syracuseStep 11915095 = 17872643) B17872643
theorem B1741851 : Blo 1740571 1741851 := bstep (se 1 (by rfl) ⟨1306388, by rfl⟩ : syracuseStep 1741851 = 2612777) B2612777
theorem B2611247 : Blo 1740571 2611247 := bstep (se 1 (by rfl) ⟨1958435, by rfl⟩ : syracuseStep 2611247 = 3916871) B3916871
theorem B4185215 : Blo 1740571 4185215 := bstep (se 1 (by rfl) ⟨3138911, by rfl⟩ : syracuseStep 4185215 = 6277823) B6277823
theorem B2612987 : Blo 1740571 2612987 := bstep (se 1 (by rfl) ⟨1959740, by rfl⟩ : syracuseStep 2612987 = 3919481) B3919481
theorem B7537981 : Blo 1740571 7537981 := bstep (se 3 (by rfl) ⟨1413371, by rfl⟩ : syracuseStep 7537981 = 2826743) B2826743
theorem B5294335 : Blo 1740571 5294335 := bstep (se 1 (by rfl) ⟨3970751, by rfl⟩ : syracuseStep 5294335 = 7941503) B7941503
theorem B15886793 : Blo 1740571 15886793 := bstep (se 2 (by rfl) ⟨5957547, by rfl⟩ : syracuseStep 15886793 = 11915095) B11915095
theorem B1740831 : Blo 1740571 1740831 := bstep (se 1 (by rfl) ⟨1305623, by rfl⟩ : syracuseStep 1740831 = 2611247) B2611247
theorem B2790143 : Blo 1740571 2790143 := bstep (se 1 (by rfl) ⟨2092607, by rfl⟩ : syracuseStep 2790143 = 4185215) B4185215
theorem B1741991 : Blo 1740571 1741991 := bstep (se 1 (by rfl) ⟨1306493, by rfl⟩ : syracuseStep 1741991 = 2612987) B2612987
theorem B1860095 : Blo 1740571 1860095 := bstep (se 1 (by rfl) ⟨1395071, by rfl⟩ : syracuseStep 1860095 = 2790143) B2790143
theorem B7059113 : Blo 1740571 7059113 := bstep (se 2 (by rfl) ⟨2647167, by rfl⟩ : syracuseStep 7059113 = 5294335) B5294335
theorem B10591195 : Blo 1740571 10591195 := bstep (se 1 (by rfl) ⟨7943396, by rfl⟩ : syracuseStep 10591195 = 15886793) B15886793
theorem B10050641 : Blo 1740571 10050641 := bstep (se 2 (by rfl) ⟨3768990, by rfl⟩ : syracuseStep 10050641 = 7537981) B7537981
theorem B4706075 : Blo 1740571 4706075 := bstep (se 1 (by rfl) ⟨3529556, by rfl⟩ : syracuseStep 4706075 = 7059113) B7059113
theorem B4960253 : Blo 1740571 4960253 := bstep (se 3 (by rfl) ⟨930047, by rfl⟩ : syracuseStep 4960253 = 1860095) B1860095
theorem B14121593 : Blo 1740571 14121593 := bstep (se 2 (by rfl) ⟨5295597, by rfl⟩ : syracuseStep 14121593 = 10591195) B10591195
theorem B6700427 : Blo 1740571 6700427 := bstep (se 1 (by rfl) ⟨5025320, by rfl⟩ : syracuseStep 6700427 = 10050641) B10050641
theorem B9414395 : Blo 1740571 9414395 := bstep (se 1 (by rfl) ⟨7060796, by rfl⟩ : syracuseStep 9414395 = 14121593) B14121593
theorem B4466951 : Blo 1740571 4466951 := bstep (se 1 (by rfl) ⟨3350213, by rfl⟩ : syracuseStep 4466951 = 6700427) B6700427
theorem B3306835 : Blo 1740571 3306835 := bstep (se 1 (by rfl) ⟨2480126, by rfl⟩ : syracuseStep 3306835 = 4960253) B4960253
theorem B3137383 : Blo 1740571 3137383 := bstep (se 1 (by rfl) ⟨2353037, by rfl⟩ : syracuseStep 3137383 = 4706075) B4706075
theorem B6276263 : Blo 1740571 6276263 := bstep (se 1 (by rfl) ⟨4707197, by rfl⟩ : syracuseStep 6276263 = 9414395) B9414395
theorem B4409113 : Blo 1740571 4409113 := bstep (se 2 (by rfl) ⟨1653417, by rfl⟩ : syracuseStep 4409113 = 3306835) B3306835
theorem B2977967 : Blo 1740571 2977967 := bstep (se 1 (by rfl) ⟨2233475, by rfl⟩ : syracuseStep 2977967 = 4466951) B4466951
theorem B4183177 : Blo 1740571 4183177 := bstep (se 2 (by rfl) ⟨1568691, by rfl⟩ : syracuseStep 4183177 = 3137383) B3137383
theorem B16736701 : Blo 1740571 16736701 := bstep (se 3 (by rfl) ⟨3138131, by rfl⟩ : syracuseStep 16736701 = 6276263) B6276263
theorem B7941245 : Blo 1740571 7941245 := bstep (se 3 (by rfl) ⟨1488983, by rfl⟩ : syracuseStep 7941245 = 2977967) B2977967
theorem B5878817 : Blo 1740571 5878817 := bstep (se 2 (by rfl) ⟨2204556, by rfl⟩ : syracuseStep 5878817 = 4409113) B4409113
theorem B5577569 : Blo 1740571 5577569 := bstep (se 2 (by rfl) ⟨2091588, by rfl⟩ : syracuseStep 5577569 = 4183177) B4183177
theorem B21176653 : Blo 1740571 21176653 := bstep (se 3 (by rfl) ⟨3970622, by rfl⟩ : syracuseStep 21176653 = 7941245) B7941245
theorem B22315601 : Blo 1740571 22315601 := bstep (se 2 (by rfl) ⟨8368350, by rfl⟩ : syracuseStep 22315601 = 16736701) B16736701
theorem B3919211 : Blo 1740571 3919211 := bstep (se 1 (by rfl) ⟨2939408, by rfl⟩ : syracuseStep 3919211 = 5878817) B5878817
theorem B3718379 : Blo 1740571 3718379 := bstep (se 1 (by rfl) ⟨2788784, by rfl⟩ : syracuseStep 3718379 = 5577569) B5577569
theorem B14877067 : Blo 1740571 14877067 := bstep (se 1 (by rfl) ⟨11157800, by rfl⟩ : syracuseStep 14877067 = 22315601) B22315601
theorem B2478919 : Blo 1740571 2478919 := bstep (se 1 (by rfl) ⟨1859189, by rfl⟩ : syracuseStep 2478919 = 3718379) B3718379
theorem B28235537 : Blo 1740571 28235537 := bstep (se 2 (by rfl) ⟨10588326, by rfl⟩ : syracuseStep 28235537 = 21176653) B21176653
theorem B2612807 : Blo 1740571 2612807 := bstep (se 1 (by rfl) ⟨1959605, by rfl⟩ : syracuseStep 2612807 = 3919211) B3919211
theorem B19836089 : Blo 1740571 19836089 := bstep (se 2 (by rfl) ⟨7438533, by rfl⟩ : syracuseStep 19836089 = 14877067) B14877067
theorem B3305225 : Blo 1740571 3305225 := bstep (se 2 (by rfl) ⟨1239459, by rfl⟩ : syracuseStep 3305225 = 2478919) B2478919
theorem B1741871 : Blo 1740571 1741871 := bstep (se 1 (by rfl) ⟨1306403, by rfl⟩ : syracuseStep 1741871 = 2612807) B2612807
theorem B18823691 : Blo 1740571 18823691 := bstep (se 1 (by rfl) ⟨14117768, by rfl⟩ : syracuseStep 18823691 = 28235537) B28235537
theorem B13224059 : Blo 1740571 13224059 := bstep (se 1 (by rfl) ⟨9918044, by rfl⟩ : syracuseStep 13224059 = 19836089) B19836089
theorem B12549127 : Blo 1740571 12549127 := bstep (se 1 (by rfl) ⟨9411845, by rfl⟩ : syracuseStep 12549127 = 18823691) B18823691
theorem B8813933 : Blo 1740571 8813933 := bstep (se 3 (by rfl) ⟨1652612, by rfl⟩ : syracuseStep 8813933 = 3305225) B3305225
theorem B8816039 : Blo 1740571 8816039 := bstep (se 1 (by rfl) ⟨6612029, by rfl⟩ : syracuseStep 8816039 = 13224059) B13224059
theorem B5875955 : Blo 1740571 5875955 := bstep (se 1 (by rfl) ⟨4406966, by rfl⟩ : syracuseStep 5875955 = 8813933) B8813933
theorem B16732169 : Blo 1740571 16732169 := bstep (se 2 (by rfl) ⟨6274563, by rfl⟩ : syracuseStep 16732169 = 12549127) B12549127
theorem B3917303 : Blo 1740571 3917303 := bstep (se 1 (by rfl) ⟨2937977, by rfl⟩ : syracuseStep 3917303 = 5875955) B5875955
theorem B5877359 : Blo 1740571 5877359 := bstep (se 1 (by rfl) ⟨4408019, by rfl⟩ : syracuseStep 5877359 = 8816039) B8816039
theorem B11154779 : Blo 1740571 11154779 := bstep (se 1 (by rfl) ⟨8366084, by rfl⟩ : syracuseStep 11154779 = 16732169) B16732169
theorem B3918239 : Blo 1740571 3918239 := bstep (se 1 (by rfl) ⟨2938679, by rfl⟩ : syracuseStep 3918239 = 5877359) B5877359
theorem B7436519 : Blo 1740571 7436519 := bstep (se 1 (by rfl) ⟨5577389, by rfl⟩ : syracuseStep 7436519 = 11154779) B11154779
theorem B2611535 : Blo 1740571 2611535 := bstep (se 1 (by rfl) ⟨1958651, by rfl⟩ : syracuseStep 2611535 = 3917303) B3917303
theorem B4957679 : Blo 1740571 4957679 := bstep (se 1 (by rfl) ⟨3718259, by rfl⟩ : syracuseStep 4957679 = 7436519) B7436519
theorem B1741023 : Blo 1740571 1741023 := bstep (se 1 (by rfl) ⟨1305767, by rfl⟩ : syracuseStep 1741023 = 2611535) B2611535
theorem B2612159 : Blo 1740571 2612159 := bstep (se 1 (by rfl) ⟨1959119, by rfl⟩ : syracuseStep 2612159 = 3918239) B3918239
theorem B3305119 : Blo 1740571 3305119 := bstep (se 1 (by rfl) ⟨2478839, by rfl⟩ : syracuseStep 3305119 = 4957679) B4957679
theorem B1741439 : Blo 1740571 1741439 := bstep (se 1 (by rfl) ⟨1306079, by rfl⟩ : syracuseStep 1741439 = 2612159) B2612159
theorem B4406825 : Blo 1740571 4406825 := bstep (se 2 (by rfl) ⟨1652559, by rfl⟩ : syracuseStep 4406825 = 3305119) B3305119
theorem B2937883 : Blo 1740571 2937883 := bstep (se 1 (by rfl) ⟨2203412, by rfl⟩ : syracuseStep 2937883 = 4406825) B4406825
theorem B3917177 : Blo 1740571 3917177 := bstep (se 2 (by rfl) ⟨1468941, by rfl⟩ : syracuseStep 3917177 = 2937883) B2937883
theorem B2611451 : Blo 1740571 2611451 := bstep (se 1 (by rfl) ⟨1958588, by rfl⟩ : syracuseStep 2611451 = 3917177) B3917177
theorem B1740967 : Blo 1740571 1740967 := bstep (se 1 (by rfl) ⟨1305725, by rfl⟩ : syracuseStep 1740967 = 2611451) B2611451

theorem C0 (j : ℕ) (h1 : 435142 ≤ j) (h2 : j ≤ 435642) : Blo 1740571 (4 * j + 3) := by
  interval_cases j
  · exact B1740571
  · exact B1740575
  · exact B1740579
  · exact B1740583
  · exact B1740587
  · exact B1740591
  · exact B1740595
  · exact B1740599
  · exact B1740603
  · exact B1740607
  · exact B1740611
  · exact B1740615
  · exact B1740619
  · exact B1740623
  · exact B1740627
  · exact B1740631
  · exact B1740635
  · exact B1740639
  · exact B1740643
  · exact B1740647
  · exact B1740651
  · exact B1740655
  · exact B1740659
  · exact B1740663
  · exact B1740667
  · exact B1740671
  · exact B1740675
  · exact B1740679
  · exact B1740683
  · exact B1740687
  · exact B1740691
  · exact B1740695
  · exact B1740699
  · exact B1740703
  · exact B1740707
  · exact B1740711
  · exact B1740715
  · exact B1740719
  · exact B1740723
  · exact B1740727
  · exact B1740731
  · exact B1740735
  · exact B1740739
  · exact B1740743
  · exact B1740747
  · exact B1740751
  · exact B1740755
  · exact B1740759
  · exact B1740763
  · exact B1740767
  · exact B1740771
  · exact B1740775
  · exact B1740779
  · exact B1740783
  · exact B1740787
  · exact B1740791
  · exact B1740795
  · exact B1740799
  · exact B1740803
  · exact B1740807
  · exact B1740811
  · exact B1740815
  · exact B1740819
  · exact B1740823
  · exact B1740827
  · exact B1740831
  · exact B1740835
  · exact B1740839
  · exact B1740843
  · exact B1740847
  · exact B1740851
  · exact B1740855
  · exact B1740859
  · exact B1740863
  · exact B1740867
  · exact B1740871
  · exact B1740875
  · exact B1740879
  · exact B1740883
  · exact B1740887
  · exact B1740891
  · exact B1740895
  · exact B1740899
  · exact B1740903
  · exact B1740907
  · exact B1740911
  · exact B1740915
  · exact B1740919
  · exact B1740923
  · exact B1740927
  · exact B1740931
  · exact B1740935
  · exact B1740939
  · exact B1740943
  · exact B1740947
  · exact B1740951
  · exact B1740955
  · exact B1740959
  · exact B1740963
  · exact B1740967
  · exact B1740971
  · exact B1740975
  · exact B1740979
  · exact B1740983
  · exact B1740987
  · exact B1740991
  · exact B1740995
  · exact B1740999
  · exact B1741003
  · exact B1741007
  · exact B1741011
  · exact B1741015
  · exact B1741019
  · exact B1741023
  · exact B1741027
  · exact B1741031
  · exact B1741035
  · exact B1741039
  · exact B1741043
  · exact B1741047
  · exact B1741051
  · exact B1741055
  · exact B1741059
  · exact B1741063
  · exact B1741067
  · exact B1741071
  · exact B1741075
  · exact B1741079
  · exact B1741083
  · exact B1741087
  · exact B1741091
  · exact B1741095
  · exact B1741099
  · exact B1741103
  · exact B1741107
  · exact B1741111
  · exact B1741115
  · exact B1741119
  · exact B1741123
  · exact B1741127
  · exact B1741131
  · exact B1741135
  · exact B1741139
  · exact B1741143
  · exact B1741147
  · exact B1741151
  · exact B1741155
  · exact B1741159
  · exact B1741163
  · exact B1741167
  · exact B1741171
  · exact B1741175
  · exact B1741179
  · exact B1741183
  · exact B1741187
  · exact B1741191
  · exact B1741195
  · exact B1741199
  · exact B1741203
  · exact B1741207
  · exact B1741211
  · exact B1741215
  · exact B1741219
  · exact B1741223
  · exact B1741227
  · exact B1741231
  · exact B1741235
  · exact B1741239
  · exact B1741243
  · exact B1741247
  · exact B1741251
  · exact B1741255
  · exact B1741259
  · exact B1741263
  · exact B1741267
  · exact B1741271
  · exact B1741275
  · exact B1741279
  · exact B1741283
  · exact B1741287
  · exact B1741291
  · exact B1741295
  · exact B1741299
  · exact B1741303
  · exact B1741307
  · exact B1741311
  · exact B1741315
  · exact B1741319
  · exact B1741323
  · exact B1741327
  · exact B1741331
  · exact B1741335
  · exact B1741339
  · exact B1741343
  · exact B1741347
  · exact B1741351
  · exact B1741355
  · exact B1741359
  · exact B1741363
  · exact B1741367
  · exact B1741371
  · exact B1741375
  · exact B1741379
  · exact B1741383
  · exact B1741387
  · exact B1741391
  · exact B1741395
  · exact B1741399
  · exact B1741403
  · exact B1741407
  · exact B1741411
  · exact B1741415
  · exact B1741419
  · exact B1741423
  · exact B1741427
  · exact B1741431
  · exact B1741435
  · exact B1741439
  · exact B1741443
  · exact B1741447
  · exact B1741451
  · exact B1741455
  · exact B1741459
  · exact B1741463
  · exact B1741467
  · exact B1741471
  · exact B1741475
  · exact B1741479
  · exact B1741483
  · exact B1741487
  · exact B1741491
  · exact B1741495
  · exact B1741499
  · exact B1741503
  · exact B1741507
  · exact B1741511
  · exact B1741515
  · exact B1741519
  · exact B1741523
  · exact B1741527
  · exact B1741531
  · exact B1741535
  · exact B1741539
  · exact B1741543
  · exact B1741547
  · exact B1741551
  · exact B1741555
  · exact B1741559
  · exact B1741563
  · exact B1741567
  · exact B1741571
  · exact B1741575
  · exact B1741579
  · exact B1741583
  · exact B1741587
  · exact B1741591
  · exact B1741595
  · exact B1741599
  · exact B1741603
  · exact B1741607
  · exact B1741611
  · exact B1741615
  · exact B1741619
  · exact B1741623
  · exact B1741627
  · exact B1741631
  · exact B1741635
  · exact B1741639
  · exact B1741643
  · exact B1741647
  · exact B1741651
  · exact B1741655
  · exact B1741659
  · exact B1741663
  · exact B1741667
  · exact B1741671
  · exact B1741675
  · exact B1741679
  · exact B1741683
  · exact B1741687
  · exact B1741691
  · exact B1741695
  · exact B1741699
  · exact B1741703
  · exact B1741707
  · exact B1741711
  · exact B1741715
  · exact B1741719
  · exact B1741723
  · exact B1741727
  · exact B1741731
  · exact B1741735
  · exact B1741739
  · exact B1741743
  · exact B1741747
  · exact B1741751
  · exact B1741755
  · exact B1741759
  · exact B1741763
  · exact B1741767
  · exact B1741771
  · exact B1741775
  · exact B1741779
  · exact B1741783
  · exact B1741787
  · exact B1741791
  · exact B1741795
  · exact B1741799
  · exact B1741803
  · exact B1741807
  · exact B1741811
  · exact B1741815
  · exact B1741819
  · exact B1741823
  · exact B1741827
  · exact B1741831
  · exact B1741835
  · exact B1741839
  · exact B1741843
  · exact B1741847
  · exact B1741851
  · exact B1741855
  · exact B1741859
  · exact B1741863
  · exact B1741867
  · exact B1741871
  · exact B1741875
  · exact B1741879
  · exact B1741883
  · exact B1741887
  · exact B1741891
  · exact B1741895
  · exact B1741899
  · exact B1741903
  · exact B1741907
  · exact B1741911
  · exact B1741915
  · exact B1741919
  · exact B1741923
  · exact B1741927
  · exact B1741931
  · exact B1741935
  · exact B1741939
  · exact B1741943
  · exact B1741947
  · exact B1741951
  · exact B1741955
  · exact B1741959
  · exact B1741963
  · exact B1741967
  · exact B1741971
  · exact B1741975
  · exact B1741979
  · exact B1741983
  · exact B1741987
  · exact B1741991
  · exact B1741995
  · exact B1741999
  · exact B1742003
  · exact B1742007
  · exact B1742011
  · exact B1742015
  · exact B1742019
  · exact B1742023
  · exact B1742027
  · exact B1742031
  · exact B1742035
  · exact B1742039
  · exact B1742043
  · exact B1742047
  · exact B1742051
  · exact B1742055
  · exact B1742059
  · exact B1742063
  · exact B1742067
  · exact B1742071
  · exact B1742075
  · exact B1742079
  · exact B1742083
  · exact B1742087
  · exact B1742091
  · exact B1742095
  · exact B1742099
  · exact B1742103
  · exact B1742107
  · exact B1742111
  · exact B1742115
  · exact B1742119
  · exact B1742123
  · exact B1742127
  · exact B1742131
  · exact B1742135
  · exact B1742139
  · exact B1742143
  · exact B1742147
  · exact B1742151
  · exact B1742155
  · exact B1742159
  · exact B1742163
  · exact B1742167
  · exact B1742171
  · exact B1742175
  · exact B1742179
  · exact B1742183
  · exact B1742187
  · exact B1742191
  · exact B1742195
  · exact B1742199
  · exact B1742203
  · exact B1742207
  · exact B1742211
  · exact B1742215
  · exact B1742219
  · exact B1742223
  · exact B1742227
  · exact B1742231
  · exact B1742235
  · exact B1742239
  · exact B1742243
  · exact B1742247
  · exact B1742251
  · exact B1742255
  · exact B1742259
  · exact B1742263
  · exact B1742267
  · exact B1742271
  · exact B1742275
  · exact B1742279
  · exact B1742283
  · exact B1742287
  · exact B1742291
  · exact B1742295
  · exact B1742299
  · exact B1742303
  · exact B1742307
  · exact B1742311
  · exact B1742315
  · exact B1742319
  · exact B1742323
  · exact B1742327
  · exact B1742331
  · exact B1742335
  · exact B1742339
  · exact B1742343
  · exact B1742347
  · exact B1742351
  · exact B1742355
  · exact B1742359
  · exact B1742363
  · exact B1742367
  · exact B1742371
  · exact B1742375
  · exact B1742379
  · exact B1742383
  · exact B1742387
  · exact B1742391
  · exact B1742395
  · exact B1742399
  · exact B1742403
  · exact B1742407
  · exact B1742411
  · exact B1742415
  · exact B1742419
  · exact B1742423
  · exact B1742427
  · exact B1742431
  · exact B1742435
  · exact B1742439
  · exact B1742443
  · exact B1742447
  · exact B1742451
  · exact B1742455
  · exact B1742459
  · exact B1742463
  · exact B1742467
  · exact B1742471
  · exact B1742475
  · exact B1742479
  · exact B1742483
  · exact B1742487
  · exact B1742491
  · exact B1742495
  · exact B1742499
  · exact B1742503
  · exact B1742507
  · exact B1742511
  · exact B1742515
  · exact B1742519
  · exact B1742523
  · exact B1742527
  · exact B1742531
  · exact B1742535
  · exact B1742539
  · exact B1742543
  · exact B1742547
  · exact B1742551
  · exact B1742555
  · exact B1742559
  · exact B1742563
  · exact B1742567
  · exact B1742571

theorem solution (m : ℕ) (hlo : 1740571 ≤ m) (hhi : m ≤ 1742571) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 435142 ≤ j := by omega
    have hj2 : j ≤ 435642 := by omega
    have hb : Blo 1740571 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
