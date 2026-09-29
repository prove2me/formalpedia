-- Prove2me | solution 1 for syracuse_descends_range_123787_127787
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:32.743548+00:00
-- url     : https://prove2.me/submissions/b321428a-9d11-42f8-b5cf-7652a9bebef1

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


theorem B426005 : Blo 123787 426005 := bbase (se 6 (by rfl) ⟨9984, by rfl⟩ : syracuseStep 426005 = 19969) (by norm_num)
theorem B557237 : Blo 123787 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B295093 : Blo 123787 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B229565 : Blo 123787 229565 := bbase (se 3 (by rfl) ⟨43043, by rfl⟩ : syracuseStep 229565 = 86087) (by norm_num)
theorem B164101 : Blo 123787 164101 := bbase (se 4 (by rfl) ⟨15384, by rfl⟩ : syracuseStep 164101 = 30769) (by norm_num)
theorem B426437 : Blo 123787 426437 := bbase (se 4 (by rfl) ⟨39978, by rfl⟩ : syracuseStep 426437 = 79957) (by norm_num)
theorem B361061 : Blo 123787 361061 := bbase (se 4 (by rfl) ⟨33849, by rfl⟩ : syracuseStep 361061 = 67699) (by norm_num)
theorem B164497 : Blo 123787 164497 := bbase (se 2 (by rfl) ⟨61686, by rfl⟩ : syracuseStep 164497 = 123373) (by norm_num)
theorem B426869 : Blo 123787 426869 := bbase (se 5 (by rfl) ⟨20009, by rfl⟩ : syracuseStep 426869 = 40019) (by norm_num)
theorem B361493 : Blo 123787 361493 := bbase (se 6 (by rfl) ⟨8472, by rfl⟩ : syracuseStep 361493 = 16945) (by norm_num)
theorem B132365 : Blo 123787 132365 := bbase (se 3 (by rfl) ⟨24818, by rfl⟩ : syracuseStep 132365 = 49637) (by norm_num)
theorem B427301 : Blo 123787 427301 := bbase (se 4 (by rfl) ⟨40059, by rfl⟩ : syracuseStep 427301 = 80119) (by norm_num)
theorem B132553 : Blo 123787 132553 := bbase (se 2 (by rfl) ⟨49707, by rfl⟩ : syracuseStep 132553 = 99415) (by norm_num)
theorem B165341 : Blo 123787 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B231005 : Blo 123787 231005 := bbase (se 3 (by rfl) ⟨43313, by rfl⟩ : syracuseStep 231005 = 86627) (by norm_num)
theorem B198317 : Blo 123787 198317 := bbase (se 3 (by rfl) ⟨37184, by rfl⟩ : syracuseStep 198317 = 74369) (by norm_num)
theorem B427733 : Blo 123787 427733 := bbase (se 7 (by rfl) ⟨5012, by rfl⟩ : syracuseStep 427733 = 10025) (by norm_num)
theorem B362245 : Blo 123787 362245 := bbase (se 4 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 362245 = 67921) (by norm_num)
theorem B198445 : Blo 123787 198445 := bbase (se 3 (by rfl) ⟨37208, by rfl⟩ : syracuseStep 198445 = 74417) (by norm_num)
theorem B264173 : Blo 123787 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B428165 : Blo 123787 428165 := bbase (se 4 (by rfl) ⟨40140, by rfl⟩ : syracuseStep 428165 = 80281) (by norm_num)
theorem B133373 : Blo 123787 133373 := bbase (se 3 (by rfl) ⟨25007, by rfl⟩ : syracuseStep 133373 = 50015) (by norm_num)
theorem B297317 : Blo 123787 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B428597 : Blo 123787 428597 := bbase (se 5 (by rfl) ⟨20090, by rfl⟩ : syracuseStep 428597 = 40181) (by norm_num)
theorem B199253 : Blo 123787 199253 := bbase (se 8 (by rfl) ⟨1167, by rfl⟩ : syracuseStep 199253 = 2335) (by norm_num)
theorem B133817 : Blo 123787 133817 := bbase (se 2 (by rfl) ⟨50181, by rfl⟩ : syracuseStep 133817 = 100363) (by norm_num)
theorem B953045 : Blo 123787 953045 := bbase (se 7 (by rfl) ⟨11168, by rfl⟩ : syracuseStep 953045 = 22337) (by norm_num)
theorem B265037 : Blo 123787 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B199541 : Blo 123787 199541 := bbase (se 5 (by rfl) ⟨9353, by rfl⟩ : syracuseStep 199541 = 18707) (by norm_num)
theorem B134065 : Blo 123787 134065 := bbase (se 2 (by rfl) ⟨50274, by rfl⟩ : syracuseStep 134065 = 100549) (by norm_num)
theorem B429029 : Blo 123787 429029 := bbase (se 4 (by rfl) ⟨40221, by rfl⟩ : syracuseStep 429029 = 80443) (by norm_num)
theorem B298013 : Blo 123787 298013 := bbase (se 3 (by rfl) ⟨55877, by rfl⟩ : syracuseStep 298013 = 111755) (by norm_num)
theorem B265277 : Blo 123787 265277 := bbase (se 3 (by rfl) ⟨49739, by rfl⟩ : syracuseStep 265277 = 99479) (by norm_num)
theorem B199957 : Blo 123787 199957 := bbase (se 6 (by rfl) ⟨4686, by rfl⟩ : syracuseStep 199957 = 9373) (by norm_num)
theorem B134497 : Blo 123787 134497 := bbase (se 2 (by rfl) ⟨50436, by rfl⟩ : syracuseStep 134497 = 100873) (by norm_num)
theorem B429461 : Blo 123787 429461 := bbase (se 6 (by rfl) ⟨10065, by rfl⟩ : syracuseStep 429461 = 20131) (by norm_num)
theorem B134569 : Blo 123787 134569 := bbase (se 2 (by rfl) ⟨50463, by rfl⟩ : syracuseStep 134569 = 100927) (by norm_num)
theorem B265781 : Blo 123787 265781 := bbase (se 5 (by rfl) ⟨12458, by rfl⟩ : syracuseStep 265781 = 24917) (by norm_num)
theorem B265789 : Blo 123787 265789 := bbase (se 3 (by rfl) ⟨49835, by rfl⟩ : syracuseStep 265789 = 99671) (by norm_num)
theorem B134941 : Blo 123787 134941 := bbase (se 3 (by rfl) ⟨25301, by rfl⟩ : syracuseStep 134941 = 50603) (by norm_num)
theorem B429893 : Blo 123787 429893 := bbase (se 4 (by rfl) ⟨40302, by rfl⟩ : syracuseStep 429893 = 80605) (by norm_num)
theorem B397237 : Blo 123787 397237 := bbase (se 5 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 397237 = 37241) (by norm_num)
theorem B135317 : Blo 123787 135317 := bbase (se 6 (by rfl) ⟨3171, by rfl⟩ : syracuseStep 135317 = 6343) (by norm_num)
theorem B200893 : Blo 123787 200893 := bbase (se 3 (by rfl) ⟨37667, by rfl⟩ : syracuseStep 200893 = 75335) (by norm_num)
theorem B135389 : Blo 123787 135389 := bbase (se 3 (by rfl) ⟨25385, by rfl⟩ : syracuseStep 135389 = 50771) (by norm_num)
theorem B430325 : Blo 123787 430325 := bbase (se 5 (by rfl) ⟨20171, by rfl⟩ : syracuseStep 430325 = 40343) (by norm_num)
theorem B397685 : Blo 123787 397685 := bbase (se 5 (by rfl) ⟨18641, by rfl⟩ : syracuseStep 397685 = 37283) (by norm_num)
theorem B1085845 : Blo 123787 1085845 := bbase (se 6 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 1085845 = 50899) (by norm_num)
theorem B135577 : Blo 123787 135577 := bbase (se 2 (by rfl) ⟨50841, by rfl⟩ : syracuseStep 135577 = 101683) (by norm_num)
theorem B1217045 : Blo 123787 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B135761 : Blo 123787 135761 := bbase (se 2 (by rfl) ⟨50910, by rfl⟩ : syracuseStep 135761 = 101821) (by norm_num)
theorem B266917 : Blo 123787 266917 := bbase (se 4 (by rfl) ⟨25023, by rfl⟩ : syracuseStep 266917 = 50047) (by norm_num)
theorem B430757 : Blo 123787 430757 := bbase (se 4 (by rfl) ⟨40383, by rfl⟩ : syracuseStep 430757 = 80767) (by norm_num)
theorem B2036501 : Blo 123787 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B135965 : Blo 123787 135965 := bbase (se 3 (by rfl) ⟨25493, by rfl⟩ : syracuseStep 135965 = 50987) (by norm_num)
theorem B299821 : Blo 123787 299821 := bbase (se 3 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 299821 = 112433) (by norm_num)
theorem B1217429 : Blo 123787 1217429 := bbase (se 6 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 1217429 = 57067) (by norm_num)
theorem B1151957 : Blo 123787 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B267293 : Blo 123787 267293 := bbase (se 3 (by rfl) ⟨50117, by rfl⟩ : syracuseStep 267293 = 100235) (by norm_num)
theorem B627749 : Blo 123787 627749 := bbase (se 4 (by rfl) ⟨58851, by rfl⟩ : syracuseStep 627749 = 117703) (by norm_num)
theorem B431189 : Blo 123787 431189 := bbase (se 8 (by rfl) ⟨2526, by rfl⟩ : syracuseStep 431189 = 5053) (by norm_num)
theorem B136441 : Blo 123787 136441 := bbase (se 2 (by rfl) ⟨51165, by rfl⟩ : syracuseStep 136441 = 102331) (by norm_num)
theorem B300341 : Blo 123787 300341 := bbase (se 5 (by rfl) ⟨14078, by rfl⟩ : syracuseStep 300341 = 28157) (by norm_num)
theorem B529733 : Blo 123787 529733 := bbase (se 4 (by rfl) ⟨49662, by rfl⟩ : syracuseStep 529733 = 99325) (by norm_num)
theorem B202085 : Blo 123787 202085 := bbase (se 4 (by rfl) ⟨18945, by rfl⟩ : syracuseStep 202085 = 37891) (by norm_num)
theorem B955925 : Blo 123787 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B202277 : Blo 123787 202277 := bbase (se 4 (by rfl) ⟨18963, by rfl⟩ : syracuseStep 202277 = 37927) (by norm_num)
theorem B529973 : Blo 123787 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B235133 : Blo 123787 235133 := bbase (se 3 (by rfl) ⟨44087, by rfl⟩ : syracuseStep 235133 = 88175) (by norm_num)
theorem B726677 : Blo 123787 726677 := bbase (se 6 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 726677 = 34063) (by norm_num)
theorem B300725 : Blo 123787 300725 := bbase (se 5 (by rfl) ⟨14096, by rfl⟩ : syracuseStep 300725 = 28193) (by norm_num)
theorem B169661 : Blo 123787 169661 := bbase (se 3 (by rfl) ⟨31811, by rfl⟩ : syracuseStep 169661 = 63623) (by norm_num)
theorem B300773 : Blo 123787 300773 := bbase (se 4 (by rfl) ⟨28197, by rfl⟩ : syracuseStep 300773 = 56395) (by norm_num)
theorem B300781 : Blo 123787 300781 := bbase (se 3 (by rfl) ⟨56396, by rfl⟩ : syracuseStep 300781 = 112793) (by norm_num)
theorem B170141 : Blo 123787 170141 := bbase (se 3 (by rfl) ⟨31901, by rfl⟩ : syracuseStep 170141 = 63803) (by norm_num)
theorem B629045 : Blo 123787 629045 := bbase (se 5 (by rfl) ⟨29486, by rfl⟩ : syracuseStep 629045 = 58973) (by norm_num)
theorem B1087829 : Blo 123787 1087829 := bbase (se 10 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 1087829 = 3187) (by norm_num)
theorem B235885 : Blo 123787 235885 := bbase (se 3 (by rfl) ⟨44228, by rfl⟩ : syracuseStep 235885 = 88457) (by norm_num)
theorem B236029 : Blo 123787 236029 := bbase (se 3 (by rfl) ⟨44255, by rfl⟩ : syracuseStep 236029 = 88511) (by norm_num)
theorem B662069 : Blo 123787 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B399941 : Blo 123787 399941 := bbase (se 4 (by rfl) ⟨37494, by rfl⟩ : syracuseStep 399941 = 74989) (by norm_num)
theorem B268933 : Blo 123787 268933 := bbase (se 4 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 268933 = 50425) (by norm_num)
theorem B236189 : Blo 123787 236189 := bbase (se 3 (by rfl) ⟨44285, by rfl⟩ : syracuseStep 236189 = 88571) (by norm_num)
theorem B301781 : Blo 123787 301781 := bbase (se 7 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 301781 = 7073) (by norm_num)
theorem B236333 : Blo 123787 236333 := bbase (se 3 (by rfl) ⟨44312, by rfl⟩ : syracuseStep 236333 = 88625) (by norm_num)
theorem B301973 : Blo 123787 301973 := bbase (se 6 (by rfl) ⟨7077, by rfl⟩ : syracuseStep 301973 = 14155) (by norm_num)
theorem B203725 : Blo 123787 203725 := bbase (se 3 (by rfl) ⟨38198, by rfl⟩ : syracuseStep 203725 = 76397) (by norm_num)
theorem B236621 : Blo 123787 236621 := bbase (se 3 (by rfl) ⟨44366, by rfl⟩ : syracuseStep 236621 = 88733) (by norm_num)
theorem B236773 : Blo 123787 236773 := bbase (se 4 (by rfl) ⟨22197, by rfl⟩ : syracuseStep 236773 = 44395) (by norm_num)
theorem B269693 : Blo 123787 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B269821 : Blo 123787 269821 := bbase (se 3 (by rfl) ⟨50591, by rfl⟩ : syracuseStep 269821 = 101183) (by norm_num)
theorem B237077 : Blo 123787 237077 := bbase (se 6 (by rfl) ⟨5556, by rfl⟩ : syracuseStep 237077 = 11113) (by norm_num)
theorem B630341 : Blo 123787 630341 := bbase (se 4 (by rfl) ⟨59094, by rfl⟩ : syracuseStep 630341 = 118189) (by norm_num)
theorem B171677 : Blo 123787 171677 := bbase (se 3 (by rfl) ⟨32189, by rfl⟩ : syracuseStep 171677 = 64379) (by norm_num)
theorem B171805 : Blo 123787 171805 := bbase (se 3 (by rfl) ⟨32213, by rfl⟩ : syracuseStep 171805 = 64427) (by norm_num)
theorem B532261 : Blo 123787 532261 := bbase (se 4 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 532261 = 99799) (by norm_num)
theorem B794549 : Blo 123787 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B270317 : Blo 123787 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B139261 : Blo 123787 139261 := bbase (se 3 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 139261 = 52223) (by norm_num)
theorem B335893 : Blo 123787 335893 := bbase (se 6 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 335893 = 15745) (by norm_num)
theorem B139297 : Blo 123787 139297 := bbase (se 2 (by rfl) ⟨52236, by rfl⟩ : syracuseStep 139297 = 104473) (by norm_num)
theorem B139333 : Blo 123787 139333 := bbase (se 4 (by rfl) ⟨13062, by rfl⟩ : syracuseStep 139333 = 26125) (by norm_num)
theorem B139369 : Blo 123787 139369 := bbase (se 2 (by rfl) ⟨52263, by rfl⟩ : syracuseStep 139369 = 104527) (by norm_num)
theorem B139405 : Blo 123787 139405 := bbase (se 3 (by rfl) ⟨26138, by rfl⟩ : syracuseStep 139405 = 52277) (by norm_num)
theorem B139441 : Blo 123787 139441 := bbase (se 2 (by rfl) ⟨52290, by rfl⟩ : syracuseStep 139441 = 104581) (by norm_num)
theorem B139477 : Blo 123787 139477 := bbase (se 7 (by rfl) ⟨1634, by rfl⟩ : syracuseStep 139477 = 3269) (by norm_num)
theorem B139513 : Blo 123787 139513 := bbase (se 2 (by rfl) ⟨52317, by rfl⟩ : syracuseStep 139513 = 104635) (by norm_num)
theorem B237829 : Blo 123787 237829 := bbase (se 4 (by rfl) ⟨22296, by rfl⟩ : syracuseStep 237829 = 44593) (by norm_num)
theorem B139549 : Blo 123787 139549 := bbase (se 3 (by rfl) ⟨26165, by rfl⟩ : syracuseStep 139549 = 52331) (by norm_num)
theorem B139585 : Blo 123787 139585 := bbase (se 2 (by rfl) ⟨52344, by rfl⟩ : syracuseStep 139585 = 104689) (by norm_num)
theorem B139621 : Blo 123787 139621 := bbase (se 4 (by rfl) ⟨13089, by rfl⟩ : syracuseStep 139621 = 26179) (by norm_num)
theorem B598373 : Blo 123787 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B139657 : Blo 123787 139657 := bbase (se 2 (by rfl) ⟨52371, by rfl⟩ : syracuseStep 139657 = 104743) (by norm_num)
theorem B237973 : Blo 123787 237973 := bbase (se 6 (by rfl) ⟨5577, by rfl⟩ : syracuseStep 237973 = 11155) (by norm_num)
theorem B139693 : Blo 123787 139693 := bbase (se 3 (by rfl) ⟨26192, by rfl⟩ : syracuseStep 139693 = 52385) (by norm_num)
theorem B139729 : Blo 123787 139729 := bbase (se 2 (by rfl) ⟨52398, by rfl⟩ : syracuseStep 139729 = 104797) (by norm_num)
theorem B139765 : Blo 123787 139765 := bbase (se 5 (by rfl) ⟨6551, by rfl⟩ : syracuseStep 139765 = 13103) (by norm_num)
theorem B139801 : Blo 123787 139801 := bbase (se 2 (by rfl) ⟨52425, by rfl⟩ : syracuseStep 139801 = 104851) (by norm_num)
theorem B238133 : Blo 123787 238133 := bbase (se 5 (by rfl) ⟨11162, by rfl⟩ : syracuseStep 238133 = 22325) (by norm_num)
theorem B139837 : Blo 123787 139837 := bbase (se 3 (by rfl) ⟨26219, by rfl⟩ : syracuseStep 139837 = 52439) (by norm_num)
theorem B303709 : Blo 123787 303709 := bbase (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) (by norm_num)
theorem B139873 : Blo 123787 139873 := bbase (se 2 (by rfl) ⟨52452, by rfl⟩ : syracuseStep 139873 = 104905) (by norm_num)
theorem B139909 : Blo 123787 139909 := bbase (se 4 (by rfl) ⟨13116, by rfl⟩ : syracuseStep 139909 = 26233) (by norm_num)
theorem B139945 : Blo 123787 139945 := bbase (se 2 (by rfl) ⟨52479, by rfl⟩ : syracuseStep 139945 = 104959) (by norm_num)
theorem B238277 : Blo 123787 238277 := bbase (se 4 (by rfl) ⟨22338, by rfl⟩ : syracuseStep 238277 = 44677) (by norm_num)
theorem B139981 : Blo 123787 139981 := bbase (se 3 (by rfl) ⟨26246, by rfl⟩ : syracuseStep 139981 = 52493) (by norm_num)
theorem B1450709 : Blo 123787 1450709 := bbase (se 7 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 1450709 = 34001) (by norm_num)
theorem B402149 : Blo 123787 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B140017 : Blo 123787 140017 := bbase (se 2 (by rfl) ⟨52506, by rfl⟩ : syracuseStep 140017 = 105013) (by norm_num)
theorem B1155829 : Blo 123787 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B140053 : Blo 123787 140053 := bbase (se 6 (by rfl) ⟨3282, by rfl⟩ : syracuseStep 140053 = 6565) (by norm_num)
theorem B303925 : Blo 123787 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B140089 : Blo 123787 140089 := bbase (se 2 (by rfl) ⟨52533, by rfl⟩ : syracuseStep 140089 = 105067) (by norm_num)
theorem B271181 : Blo 123787 271181 := bbase (se 3 (by rfl) ⟨50846, by rfl⟩ : syracuseStep 271181 = 101693) (by norm_num)
theorem B631637 : Blo 123787 631637 := bbase (se 9 (by rfl) ⟨1850, by rfl⟩ : syracuseStep 631637 = 3701) (by norm_num)
theorem B140125 : Blo 123787 140125 := bbase (se 3 (by rfl) ⟨26273, by rfl⟩ : syracuseStep 140125 = 52547) (by norm_num)
theorem B140161 : Blo 123787 140161 := bbase (se 2 (by rfl) ⟨52560, by rfl⟩ : syracuseStep 140161 = 105121) (by norm_num)
theorem B140197 : Blo 123787 140197 := bbase (se 4 (by rfl) ⟨13143, by rfl⟩ : syracuseStep 140197 = 26287) (by norm_num)
theorem B140233 : Blo 123787 140233 := bbase (se 2 (by rfl) ⟨52587, by rfl⟩ : syracuseStep 140233 = 105175) (by norm_num)
theorem B271325 : Blo 123787 271325 := bbase (se 3 (by rfl) ⟨50873, by rfl⟩ : syracuseStep 271325 = 101747) (by norm_num)
theorem B238565 : Blo 123787 238565 := bbase (se 4 (by rfl) ⟨22365, by rfl⟩ : syracuseStep 238565 = 44731) (by norm_num)
theorem B140269 : Blo 123787 140269 := bbase (se 3 (by rfl) ⟨26300, by rfl⟩ : syracuseStep 140269 = 52601) (by norm_num)
theorem B140305 : Blo 123787 140305 := bbase (se 2 (by rfl) ⟨52614, by rfl⟩ : syracuseStep 140305 = 105229) (by norm_num)
theorem B140341 : Blo 123787 140341 := bbase (se 5 (by rfl) ⟨6578, by rfl⟩ : syracuseStep 140341 = 13157) (by norm_num)
theorem B140377 : Blo 123787 140377 := bbase (se 2 (by rfl) ⟨52641, by rfl⟩ : syracuseStep 140377 = 105283) (by norm_num)
theorem B140413 : Blo 123787 140413 := bbase (se 3 (by rfl) ⟨26327, by rfl⟩ : syracuseStep 140413 = 52655) (by norm_num)
theorem B238717 : Blo 123787 238717 := bbase (se 3 (by rfl) ⟨44759, by rfl⟩ : syracuseStep 238717 = 89519) (by norm_num)
theorem B140449 : Blo 123787 140449 := bbase (se 2 (by rfl) ⟨52668, by rfl⟩ : syracuseStep 140449 = 105337) (by norm_num)
theorem B140485 : Blo 123787 140485 := bbase (se 4 (by rfl) ⟨13170, by rfl⟩ : syracuseStep 140485 = 26341) (by norm_num)
theorem B140521 : Blo 123787 140521 := bbase (se 2 (by rfl) ⟨52695, by rfl⟩ : syracuseStep 140521 = 105391) (by norm_num)
theorem B533749 : Blo 123787 533749 := bbase (se 5 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 533749 = 50039) (by norm_num)
theorem B533765 : Blo 123787 533765 := bbase (se 4 (by rfl) ⟨50040, by rfl⟩ : syracuseStep 533765 = 100081) (by norm_num)
theorem B140557 : Blo 123787 140557 := bbase (se 3 (by rfl) ⟨26354, by rfl⟩ : syracuseStep 140557 = 52709) (by norm_num)
theorem B140593 : Blo 123787 140593 := bbase (se 2 (by rfl) ⟨52722, by rfl⟩ : syracuseStep 140593 = 105445) (by norm_num)
theorem B140629 : Blo 123787 140629 := bbase (se 12 (by rfl) ⟨51, by rfl⟩ : syracuseStep 140629 = 103) (by norm_num)
theorem B140665 : Blo 123787 140665 := bbase (se 2 (by rfl) ⟨52749, by rfl⟩ : syracuseStep 140665 = 105499) (by norm_num)
theorem B140701 : Blo 123787 140701 := bbase (se 3 (by rfl) ⟨26381, by rfl⟩ : syracuseStep 140701 = 52763) (by norm_num)
theorem B239021 : Blo 123787 239021 := bbase (se 3 (by rfl) ⟨44816, by rfl⟩ : syracuseStep 239021 = 89633) (by norm_num)
theorem B140737 : Blo 123787 140737 := bbase (se 2 (by rfl) ⟨52776, by rfl⟩ : syracuseStep 140737 = 105553) (by norm_num)
theorem B140773 : Blo 123787 140773 := bbase (se 4 (by rfl) ⟨13197, by rfl⟩ : syracuseStep 140773 = 26395) (by norm_num)
theorem B140809 : Blo 123787 140809 := bbase (se 2 (by rfl) ⟨52803, by rfl⟩ : syracuseStep 140809 = 105607) (by norm_num)
theorem B140845 : Blo 123787 140845 := bbase (se 3 (by rfl) ⟨26408, by rfl⟩ : syracuseStep 140845 = 52817) (by norm_num)
theorem B140881 : Blo 123787 140881 := bbase (se 2 (by rfl) ⟨52830, by rfl⟩ : syracuseStep 140881 = 105661) (by norm_num)
theorem B140917 : Blo 123787 140917 := bbase (se 5 (by rfl) ⟨6605, by rfl⟩ : syracuseStep 140917 = 13211) (by norm_num)
theorem B140953 : Blo 123787 140953 := bbase (se 2 (by rfl) ⟨52857, by rfl⟩ : syracuseStep 140953 = 105715) (by norm_num)
theorem B599717 : Blo 123787 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B140989 : Blo 123787 140989 := bbase (se 3 (by rfl) ⟨26435, by rfl⟩ : syracuseStep 140989 = 52871) (by norm_num)
theorem B272069 : Blo 123787 272069 := bbase (se 4 (by rfl) ⟨25506, by rfl⟩ : syracuseStep 272069 = 51013) (by norm_num)
theorem B141025 : Blo 123787 141025 := bbase (se 2 (by rfl) ⟨52884, by rfl⟩ : syracuseStep 141025 = 105769) (by norm_num)
theorem B304877 : Blo 123787 304877 := bbase (se 3 (by rfl) ⟨57164, by rfl⟩ : syracuseStep 304877 = 114329) (by norm_num)
theorem B141061 : Blo 123787 141061 := bbase (se 4 (by rfl) ⟨13224, by rfl⟩ : syracuseStep 141061 = 26449) (by norm_num)
theorem B304933 : Blo 123787 304933 := bbase (se 4 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 304933 = 57175) (by norm_num)
theorem B141097 : Blo 123787 141097 := bbase (se 2 (by rfl) ⟨52911, by rfl⟩ : syracuseStep 141097 = 105823) (by norm_num)
theorem B141133 : Blo 123787 141133 := bbase (se 3 (by rfl) ⟨26462, by rfl⟩ : syracuseStep 141133 = 52925) (by norm_num)
theorem B141169 : Blo 123787 141169 := bbase (se 2 (by rfl) ⟨52938, by rfl⟩ : syracuseStep 141169 = 105877) (by norm_num)
theorem B1025909 : Blo 123787 1025909 := bbase (se 5 (by rfl) ⟨48089, by rfl⟩ : syracuseStep 1025909 = 96179) (by norm_num)
theorem B141205 : Blo 123787 141205 := bbase (se 6 (by rfl) ⟨3309, by rfl⟩ : syracuseStep 141205 = 6619) (by norm_num)
theorem B141241 : Blo 123787 141241 := bbase (se 2 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 141241 = 105931) (by norm_num)
theorem B337861 : Blo 123787 337861 := bbase (se 4 (by rfl) ⟨31674, by rfl⟩ : syracuseStep 337861 = 63349) (by norm_num)
theorem B141277 : Blo 123787 141277 := bbase (se 3 (by rfl) ⟨26489, by rfl⟩ : syracuseStep 141277 = 52979) (by norm_num)
theorem B141313 : Blo 123787 141313 := bbase (se 2 (by rfl) ⟨52992, by rfl⟩ : syracuseStep 141313 = 105985) (by norm_num)
theorem B141349 : Blo 123787 141349 := bbase (se 4 (by rfl) ⟨13251, by rfl⟩ : syracuseStep 141349 = 26503) (by norm_num)
theorem B141385 : Blo 123787 141385 := bbase (se 2 (by rfl) ⟨53019, by rfl⟩ : syracuseStep 141385 = 106039) (by norm_num)
theorem B632933 : Blo 123787 632933 := bbase (se 4 (by rfl) ⟨59337, by rfl⟩ : syracuseStep 632933 = 118675) (by norm_num)
theorem B141421 : Blo 123787 141421 := bbase (se 3 (by rfl) ⟨26516, by rfl⟩ : syracuseStep 141421 = 53033) (by norm_num)
theorem B141457 : Blo 123787 141457 := bbase (se 2 (by rfl) ⟨53046, by rfl⟩ : syracuseStep 141457 = 106093) (by norm_num)
theorem B239773 : Blo 123787 239773 := bbase (se 3 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 239773 = 89915) (by norm_num)
theorem B305309 : Blo 123787 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B141493 : Blo 123787 141493 := bbase (se 5 (by rfl) ⟨6632, by rfl⟩ : syracuseStep 141493 = 13265) (by norm_num)
theorem B141529 : Blo 123787 141529 := bbase (se 2 (by rfl) ⟨53073, by rfl⟩ : syracuseStep 141529 = 106147) (by norm_num)
theorem B141565 : Blo 123787 141565 := bbase (se 3 (by rfl) ⟨26543, by rfl⟩ : syracuseStep 141565 = 53087) (by norm_num)
theorem B141601 : Blo 123787 141601 := bbase (se 2 (by rfl) ⟨53100, by rfl⟩ : syracuseStep 141601 = 106201) (by norm_num)
theorem B239917 : Blo 123787 239917 := bbase (se 3 (by rfl) ⟨44984, by rfl⟩ : syracuseStep 239917 = 89969) (by norm_num)
theorem B960821 : Blo 123787 960821 := bbase (se 5 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 960821 = 90077) (by norm_num)
theorem B141637 : Blo 123787 141637 := bbase (se 4 (by rfl) ⟨13278, by rfl⟩ : syracuseStep 141637 = 26557) (by norm_num)
theorem B141673 : Blo 123787 141673 := bbase (se 2 (by rfl) ⟨53127, by rfl⟩ : syracuseStep 141673 = 106255) (by norm_num)
theorem B141709 : Blo 123787 141709 := bbase (se 3 (by rfl) ⟨26570, by rfl⟩ : syracuseStep 141709 = 53141) (by norm_num)
theorem B305549 : Blo 123787 305549 := bbase (se 3 (by rfl) ⟨57290, by rfl⟩ : syracuseStep 305549 = 114581) (by norm_num)
theorem B403861 : Blo 123787 403861 := bbase (se 6 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 403861 = 18931) (by norm_num)
theorem B141745 : Blo 123787 141745 := bbase (se 2 (by rfl) ⟨53154, by rfl⟩ : syracuseStep 141745 = 106309) (by norm_num)
theorem B272821 : Blo 123787 272821 := bbase (se 5 (by rfl) ⟨12788, by rfl⟩ : syracuseStep 272821 = 25577) (by norm_num)
theorem B240077 : Blo 123787 240077 := bbase (se 3 (by rfl) ⟨45014, by rfl⟩ : syracuseStep 240077 = 90029) (by norm_num)
theorem B141781 : Blo 123787 141781 := bbase (se 7 (by rfl) ⟨1661, by rfl⟩ : syracuseStep 141781 = 3323) (by norm_num)
theorem B141817 : Blo 123787 141817 := bbase (se 2 (by rfl) ⟨53181, by rfl⟩ : syracuseStep 141817 = 106363) (by norm_num)
theorem B141853 : Blo 123787 141853 := bbase (se 3 (by rfl) ⟨26597, by rfl⟩ : syracuseStep 141853 = 53195) (by norm_num)
theorem B404021 : Blo 123787 404021 := bbase (se 5 (by rfl) ⟨18938, by rfl⟩ : syracuseStep 404021 = 37877) (by norm_num)
theorem B141889 : Blo 123787 141889 := bbase (se 2 (by rfl) ⟨53208, by rfl⟩ : syracuseStep 141889 = 106417) (by norm_num)
theorem B240221 : Blo 123787 240221 := bbase (se 3 (by rfl) ⟨45041, by rfl⟩ : syracuseStep 240221 = 90083) (by norm_num)
theorem B141925 : Blo 123787 141925 := bbase (se 4 (by rfl) ⟨13305, by rfl⟩ : syracuseStep 141925 = 26611) (by norm_num)
theorem B141961 : Blo 123787 141961 := bbase (se 2 (by rfl) ⟨53235, by rfl⟩ : syracuseStep 141961 = 106471) (by norm_num)
theorem B404117 : Blo 123787 404117 := bbase (se 6 (by rfl) ⟨9471, by rfl⟩ : syracuseStep 404117 = 18943) (by norm_num)
theorem B141997 : Blo 123787 141997 := bbase (se 3 (by rfl) ⟨26624, by rfl⟩ : syracuseStep 141997 = 53249) (by norm_num)
theorem B142033 : Blo 123787 142033 := bbase (se 2 (by rfl) ⟨53262, by rfl⟩ : syracuseStep 142033 = 106525) (by norm_num)
theorem B142069 : Blo 123787 142069 := bbase (se 5 (by rfl) ⟨6659, by rfl⟩ : syracuseStep 142069 = 13319) (by norm_num)
theorem B142105 : Blo 123787 142105 := bbase (se 2 (by rfl) ⟨53289, by rfl⟩ : syracuseStep 142105 = 106579) (by norm_num)
theorem B273197 : Blo 123787 273197 := bbase (se 3 (by rfl) ⟨51224, by rfl⟩ : syracuseStep 273197 = 102449) (by norm_num)
theorem B142141 : Blo 123787 142141 := bbase (se 3 (by rfl) ⟨26651, by rfl⟩ : syracuseStep 142141 = 53303) (by norm_num)
theorem B142177 : Blo 123787 142177 := bbase (se 2 (by rfl) ⟨53316, by rfl⟩ : syracuseStep 142177 = 106633) (by norm_num)
theorem B240509 : Blo 123787 240509 := bbase (se 3 (by rfl) ⟨45095, by rfl⟩ : syracuseStep 240509 = 90191) (by norm_num)
theorem B142213 : Blo 123787 142213 := bbase (se 4 (by rfl) ⟨13332, by rfl⟩ : syracuseStep 142213 = 26665) (by norm_num)
theorem B142249 : Blo 123787 142249 := bbase (se 2 (by rfl) ⟨53343, by rfl⟩ : syracuseStep 142249 = 106687) (by norm_num)
theorem B306125 : Blo 123787 306125 := bbase (se 3 (by rfl) ⟨57398, by rfl⟩ : syracuseStep 306125 = 114797) (by norm_num)
theorem B142285 : Blo 123787 142285 := bbase (se 3 (by rfl) ⟨26678, by rfl⟩ : syracuseStep 142285 = 53357) (by norm_num)
theorem B142321 : Blo 123787 142321 := bbase (se 2 (by rfl) ⟨53370, by rfl⟩ : syracuseStep 142321 = 106741) (by norm_num)
theorem B142357 : Blo 123787 142357 := bbase (se 6 (by rfl) ⟨3336, by rfl⟩ : syracuseStep 142357 = 6673) (by norm_num)
theorem B240661 : Blo 123787 240661 := bbase (se 6 (by rfl) ⟨5640, by rfl⟩ : syracuseStep 240661 = 11281) (by norm_num)
theorem B470069 : Blo 123787 470069 := bbase (se 5 (by rfl) ⟨22034, by rfl⟩ : syracuseStep 470069 = 44069) (by norm_num)
theorem B601141 : Blo 123787 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B142393 : Blo 123787 142393 := bbase (se 2 (by rfl) ⟨53397, by rfl⟩ : syracuseStep 142393 = 106795) (by norm_num)
theorem B339029 : Blo 123787 339029 := bbase (se 8 (by rfl) ⟨1986, by rfl⟩ : syracuseStep 339029 = 3973) (by norm_num)
theorem B142429 : Blo 123787 142429 := bbase (se 3 (by rfl) ⟨26705, by rfl⟩ : syracuseStep 142429 = 53411) (by norm_num)
theorem B142465 : Blo 123787 142465 := bbase (se 2 (by rfl) ⟨53424, by rfl⟩ : syracuseStep 142465 = 106849) (by norm_num)
theorem B142501 : Blo 123787 142501 := bbase (se 4 (by rfl) ⟨13359, by rfl⟩ : syracuseStep 142501 = 26719) (by norm_num)
theorem B142537 : Blo 123787 142537 := bbase (se 2 (by rfl) ⟨53451, by rfl⟩ : syracuseStep 142537 = 106903) (by norm_num)
theorem B142573 : Blo 123787 142573 := bbase (se 3 (by rfl) ⟨26732, by rfl⟩ : syracuseStep 142573 = 53465) (by norm_num)
theorem B142609 : Blo 123787 142609 := bbase (se 2 (by rfl) ⟨53478, by rfl⟩ : syracuseStep 142609 = 106957) (by norm_num)
theorem B142645 : Blo 123787 142645 := bbase (se 5 (by rfl) ⟨6686, by rfl⟩ : syracuseStep 142645 = 13373) (by norm_num)
theorem B240965 : Blo 123787 240965 := bbase (se 4 (by rfl) ⟨22590, by rfl⟩ : syracuseStep 240965 = 45181) (by norm_num)
theorem B470357 : Blo 123787 470357 := bbase (se 11 (by rfl) ⟨344, by rfl⟩ : syracuseStep 470357 = 689) (by norm_num)
theorem B142681 : Blo 123787 142681 := bbase (se 2 (by rfl) ⟨53505, by rfl⟩ : syracuseStep 142681 = 107011) (by norm_num)
theorem B634229 : Blo 123787 634229 := bbase (se 5 (by rfl) ⟨29729, by rfl⟩ : syracuseStep 634229 = 59459) (by norm_num)
theorem B142717 : Blo 123787 142717 := bbase (se 3 (by rfl) ⟨26759, by rfl⟩ : syracuseStep 142717 = 53519) (by norm_num)
theorem B142753 : Blo 123787 142753 := bbase (se 2 (by rfl) ⟨53532, by rfl⟩ : syracuseStep 142753 = 107065) (by norm_num)
theorem B142789 : Blo 123787 142789 := bbase (se 4 (by rfl) ⟨13386, by rfl⟩ : syracuseStep 142789 = 26773) (by norm_num)
theorem B536021 : Blo 123787 536021 := bbase (se 7 (by rfl) ⟨6281, by rfl⟩ : syracuseStep 536021 = 12563) (by norm_num)
theorem B142825 : Blo 123787 142825 := bbase (se 2 (by rfl) ⟨53559, by rfl⟩ : syracuseStep 142825 = 107119) (by norm_num)
theorem B142861 : Blo 123787 142861 := bbase (se 3 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 142861 = 53573) (by norm_num)
theorem B142897 : Blo 123787 142897 := bbase (se 2 (by rfl) ⟨53586, by rfl⟩ : syracuseStep 142897 = 107173) (by norm_num)
theorem B142933 : Blo 123787 142933 := bbase (se 8 (by rfl) ⟨837, by rfl⟩ : syracuseStep 142933 = 1675) (by norm_num)
theorem B142969 : Blo 123787 142969 := bbase (se 2 (by rfl) ⟨53613, by rfl⟩ : syracuseStep 142969 = 107227) (by norm_num)
theorem B143005 : Blo 123787 143005 := bbase (se 3 (by rfl) ⟨26813, by rfl⟩ : syracuseStep 143005 = 53627) (by norm_num)
theorem B143041 : Blo 123787 143041 := bbase (se 2 (by rfl) ⟨53640, by rfl⟩ : syracuseStep 143041 = 107281) (by norm_num)
theorem B143077 : Blo 123787 143077 := bbase (se 4 (by rfl) ⟨13413, by rfl⟩ : syracuseStep 143077 = 26827) (by norm_num)
theorem B143113 : Blo 123787 143113 := bbase (se 2 (by rfl) ⟨53667, by rfl⟩ : syracuseStep 143113 = 107335) (by norm_num)
theorem B143149 : Blo 123787 143149 := bbase (se 3 (by rfl) ⟨26840, by rfl⟩ : syracuseStep 143149 = 53681) (by norm_num)
theorem B143185 : Blo 123787 143185 := bbase (se 2 (by rfl) ⟨53694, by rfl⟩ : syracuseStep 143185 = 107389) (by norm_num)
theorem B143221 : Blo 123787 143221 := bbase (se 5 (by rfl) ⟨6713, by rfl⟩ : syracuseStep 143221 = 13427) (by norm_num)
theorem B143257 : Blo 123787 143257 := bbase (se 2 (by rfl) ⟨53721, by rfl⟩ : syracuseStep 143257 = 107443) (by norm_num)
theorem B143293 : Blo 123787 143293 := bbase (se 3 (by rfl) ⟨26867, by rfl⟩ : syracuseStep 143293 = 53735) (by norm_num)
theorem B143329 : Blo 123787 143329 := bbase (se 2 (by rfl) ⟨53748, by rfl⟩ : syracuseStep 143329 = 107497) (by norm_num)
theorem B143365 : Blo 123787 143365 := bbase (se 4 (by rfl) ⟨13440, by rfl⟩ : syracuseStep 143365 = 26881) (by norm_num)
theorem B143401 : Blo 123787 143401 := bbase (se 2 (by rfl) ⟨53775, by rfl⟩ : syracuseStep 143401 = 107551) (by norm_num)
theorem B241717 : Blo 123787 241717 := bbase (se 5 (by rfl) ⟨11330, by rfl⟩ : syracuseStep 241717 = 22661) (by norm_num)
theorem B208973 : Blo 123787 208973 := bbase (se 3 (by rfl) ⟨39182, by rfl⟩ : syracuseStep 208973 = 78365) (by norm_num)
theorem B143437 : Blo 123787 143437 := bbase (se 3 (by rfl) ⟨26894, by rfl⟩ : syracuseStep 143437 = 53789) (by norm_num)
theorem B143473 : Blo 123787 143473 := bbase (se 2 (by rfl) ⟨53802, by rfl⟩ : syracuseStep 143473 = 107605) (by norm_num)
theorem B143509 : Blo 123787 143509 := bbase (se 6 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 143509 = 6727) (by norm_num)
theorem B176293 : Blo 123787 176293 := bbase (se 4 (by rfl) ⟨16527, by rfl⟩ : syracuseStep 176293 = 33055) (by norm_num)
theorem B307381 : Blo 123787 307381 := bbase (se 5 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 307381 = 28817) (by norm_num)
theorem B143545 : Blo 123787 143545 := bbase (se 2 (by rfl) ⟨53829, by rfl⟩ : syracuseStep 143545 = 107659) (by norm_num)
theorem B241861 : Blo 123787 241861 := bbase (se 4 (by rfl) ⟨22674, by rfl⟩ : syracuseStep 241861 = 45349) (by norm_num)
theorem B209101 : Blo 123787 209101 := bbase (se 3 (by rfl) ⟨39206, by rfl⟩ : syracuseStep 209101 = 78413) (by norm_num)
theorem B143581 : Blo 123787 143581 := bbase (se 3 (by rfl) ⟨26921, by rfl⟩ : syracuseStep 143581 = 53843) (by norm_num)
theorem B143617 : Blo 123787 143617 := bbase (se 2 (by rfl) ⟨53856, by rfl⟩ : syracuseStep 143617 = 107713) (by norm_num)
theorem B176413 : Blo 123787 176413 := bbase (se 3 (by rfl) ⟨33077, by rfl⟩ : syracuseStep 176413 = 66155) (by norm_num)
theorem B209189 : Blo 123787 209189 := bbase (se 4 (by rfl) ⟨19611, by rfl⟩ : syracuseStep 209189 = 39223) (by norm_num)
theorem B143653 : Blo 123787 143653 := bbase (se 4 (by rfl) ⟨13467, by rfl⟩ : syracuseStep 143653 = 26935) (by norm_num)
theorem B143689 : Blo 123787 143689 := bbase (se 2 (by rfl) ⟨53883, by rfl⟩ : syracuseStep 143689 = 107767) (by norm_num)
theorem B242021 : Blo 123787 242021 := bbase (se 4 (by rfl) ⟨22689, by rfl⟩ : syracuseStep 242021 = 45379) (by norm_num)
theorem B143725 : Blo 123787 143725 := bbase (se 3 (by rfl) ⟨26948, by rfl⟩ : syracuseStep 143725 = 53897) (by norm_num)
theorem B176509 : Blo 123787 176509 := bbase (se 3 (by rfl) ⟨33095, by rfl⟩ : syracuseStep 176509 = 66191) (by norm_num)
theorem B143761 : Blo 123787 143761 := bbase (se 2 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 143761 = 107821) (by norm_num)
theorem B209317 : Blo 123787 209317 := bbase (se 4 (by rfl) ⟨19623, by rfl⟩ : syracuseStep 209317 = 39247) (by norm_num)
theorem B471541 : Blo 123787 471541 := bbase (se 5 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 471541 = 44207) (by norm_num)
theorem B242165 : Blo 123787 242165 := bbase (se 5 (by rfl) ⟨11351, by rfl⟩ : syracuseStep 242165 = 22703) (by norm_num)
theorem B209405 : Blo 123787 209405 := bbase (se 3 (by rfl) ⟨39263, by rfl⟩ : syracuseStep 209405 = 78527) (by norm_num)
theorem B209533 : Blo 123787 209533 := bbase (se 3 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 209533 = 78575) (by norm_num)
theorem B635525 : Blo 123787 635525 := bbase (se 4 (by rfl) ⟨59580, by rfl⟩ : syracuseStep 635525 = 119161) (by norm_num)
theorem B209621 : Blo 123787 209621 := bbase (se 7 (by rfl) ⟨2456, by rfl⟩ : syracuseStep 209621 = 4913) (by norm_num)
theorem B242437 : Blo 123787 242437 := bbase (se 4 (by rfl) ⟨22728, by rfl⟩ : syracuseStep 242437 = 45457) (by norm_num)
theorem B242453 : Blo 123787 242453 := bbase (se 6 (by rfl) ⟨5682, by rfl⟩ : syracuseStep 242453 = 11365) (by norm_num)
theorem B471845 : Blo 123787 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B209749 : Blo 123787 209749 := bbase (se 9 (by rfl) ⟨614, by rfl⟩ : syracuseStep 209749 = 1229) (by norm_num)
theorem B177005 : Blo 123787 177005 := bbase (se 3 (by rfl) ⟨33188, by rfl⟩ : syracuseStep 177005 = 66377) (by norm_num)
theorem B209837 : Blo 123787 209837 := bbase (se 3 (by rfl) ⟨39344, by rfl⟩ : syracuseStep 209837 = 78689) (by norm_num)
theorem B275437 : Blo 123787 275437 := bbase (se 3 (by rfl) ⟨51644, by rfl⟩ : syracuseStep 275437 = 103289) (by norm_num)
theorem B766997 : Blo 123787 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B209965 : Blo 123787 209965 := bbase (se 3 (by rfl) ⟨39368, by rfl⟩ : syracuseStep 209965 = 78737) (by norm_num)
theorem B144433 : Blo 123787 144433 := bbase (se 2 (by rfl) ⟨54162, by rfl⟩ : syracuseStep 144433 = 108325) (by norm_num)
theorem B210053 : Blo 123787 210053 := bbase (se 4 (by rfl) ⟨19692, by rfl⟩ : syracuseStep 210053 = 39385) (by norm_num)
theorem B210181 : Blo 123787 210181 := bbase (se 4 (by rfl) ⟨19704, by rfl⟩ : syracuseStep 210181 = 39409) (by norm_num)
theorem B210269 : Blo 123787 210269 := bbase (se 3 (by rfl) ⟨39425, by rfl⟩ : syracuseStep 210269 = 78851) (by norm_num)
theorem B406885 : Blo 123787 406885 := bbase (se 4 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 406885 = 76291) (by norm_num)
theorem B177557 : Blo 123787 177557 := bbase (se 6 (by rfl) ⟨4161, by rfl⟩ : syracuseStep 177557 = 8323) (by norm_num)
theorem B210397 : Blo 123787 210397 := bbase (se 3 (by rfl) ⟨39449, by rfl⟩ : syracuseStep 210397 = 78899) (by norm_num)
theorem B210485 : Blo 123787 210485 := bbase (se 5 (by rfl) ⟨9866, by rfl⟩ : syracuseStep 210485 = 19733) (by norm_num)
theorem B505493 : Blo 123787 505493 := bbase (se 6 (by rfl) ⟨11847, by rfl⟩ : syracuseStep 505493 = 23695) (by norm_num)
theorem B210613 : Blo 123787 210613 := bbase (se 5 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 210613 = 19745) (by norm_num)
theorem B210701 : Blo 123787 210701 := bbase (se 3 (by rfl) ⟨39506, by rfl⟩ : syracuseStep 210701 = 79013) (by norm_num)
theorem B210829 : Blo 123787 210829 := bbase (se 3 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 210829 = 79061) (by norm_num)
theorem B636821 : Blo 123787 636821 := bbase (se 6 (by rfl) ⟨14925, by rfl⟩ : syracuseStep 636821 = 29851) (by norm_num)
theorem B145309 : Blo 123787 145309 := bbase (se 3 (by rfl) ⟨27245, by rfl⟩ : syracuseStep 145309 = 54491) (by norm_num)
theorem B210917 : Blo 123787 210917 := bbase (se 4 (by rfl) ⟨19773, by rfl⟩ : syracuseStep 210917 = 39547) (by norm_num)
theorem B276517 : Blo 123787 276517 := bbase (se 4 (by rfl) ⟨25923, by rfl⟩ : syracuseStep 276517 = 51847) (by norm_num)
theorem B211045 : Blo 123787 211045 := bbase (se 4 (by rfl) ⟨19785, by rfl⟩ : syracuseStep 211045 = 39571) (by norm_num)
theorem B178309 : Blo 123787 178309 := bbase (se 4 (by rfl) ⟨16716, by rfl⟩ : syracuseStep 178309 = 33433) (by norm_num)
theorem B211133 : Blo 123787 211133 := bbase (se 3 (by rfl) ⟨39587, by rfl⟩ : syracuseStep 211133 = 79175) (by norm_num)
theorem B211261 : Blo 123787 211261 := bbase (se 3 (by rfl) ⟨39611, by rfl⟩ : syracuseStep 211261 = 79223) (by norm_num)
theorem B211349 : Blo 123787 211349 := bbase (se 6 (by rfl) ⟨4953, by rfl⟩ : syracuseStep 211349 = 9907) (by norm_num)
theorem B211477 : Blo 123787 211477 := bbase (se 6 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 211477 = 9913) (by norm_num)
theorem B178733 : Blo 123787 178733 := bbase (se 3 (by rfl) ⟨33512, by rfl⟩ : syracuseStep 178733 = 67025) (by norm_num)
theorem B211565 : Blo 123787 211565 := bbase (se 3 (by rfl) ⟨39668, by rfl⟩ : syracuseStep 211565 = 79337) (by norm_num)
theorem B211693 : Blo 123787 211693 := bbase (se 3 (by rfl) ⟨39692, by rfl⟩ : syracuseStep 211693 = 79385) (by norm_num)
theorem B211781 : Blo 123787 211781 := bbase (se 4 (by rfl) ⟨19854, by rfl⟩ : syracuseStep 211781 = 39709) (by norm_num)
theorem B473957 : Blo 123787 473957 := bbase (se 4 (by rfl) ⟨44433, by rfl⟩ : syracuseStep 473957 = 88867) (by norm_num)
theorem B179101 : Blo 123787 179101 := bbase (se 3 (by rfl) ⟨33581, by rfl⟩ : syracuseStep 179101 = 67163) (by norm_num)
theorem B211909 : Blo 123787 211909 := bbase (se 4 (by rfl) ⟨19866, by rfl⟩ : syracuseStep 211909 = 39733) (by norm_num)
theorem B211997 : Blo 123787 211997 := bbase (se 3 (by rfl) ⟨39749, by rfl⟩ : syracuseStep 211997 = 79499) (by norm_num)
theorem B474245 : Blo 123787 474245 := bbase (se 4 (by rfl) ⟨44460, by rfl⟩ : syracuseStep 474245 = 88921) (by norm_num)
theorem B212125 : Blo 123787 212125 := bbase (se 3 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 212125 = 79547) (by norm_num)
theorem B638117 : Blo 123787 638117 := bbase (se 4 (by rfl) ⟨59823, by rfl⟩ : syracuseStep 638117 = 119647) (by norm_num)
theorem B179437 : Blo 123787 179437 := bbase (se 3 (by rfl) ⟨33644, by rfl⟩ : syracuseStep 179437 = 67289) (by norm_num)
theorem B212213 : Blo 123787 212213 := bbase (se 5 (by rfl) ⟨9947, by rfl⟩ : syracuseStep 212213 = 19895) (by norm_num)
theorem B212341 : Blo 123787 212341 := bbase (se 5 (by rfl) ⟨9953, by rfl⟩ : syracuseStep 212341 = 19907) (by norm_num)
theorem B540053 : Blo 123787 540053 := bbase (se 6 (by rfl) ⟨12657, by rfl⟩ : syracuseStep 540053 = 25315) (by norm_num)
theorem B179653 : Blo 123787 179653 := bbase (se 4 (by rfl) ⟨16842, by rfl⟩ : syracuseStep 179653 = 33685) (by norm_num)
theorem B212429 : Blo 123787 212429 := bbase (se 3 (by rfl) ⟨39830, by rfl⟩ : syracuseStep 212429 = 79661) (by norm_num)
theorem B212557 : Blo 123787 212557 := bbase (se 3 (by rfl) ⟨39854, by rfl⟩ : syracuseStep 212557 = 79709) (by norm_num)
theorem B212645 : Blo 123787 212645 := bbase (se 4 (by rfl) ⟨19935, by rfl⟩ : syracuseStep 212645 = 39871) (by norm_num)
theorem B409349 : Blo 123787 409349 := bbase (se 4 (by rfl) ⟨38376, by rfl⟩ : syracuseStep 409349 = 76753) (by norm_num)
theorem B212773 : Blo 123787 212773 := bbase (se 4 (by rfl) ⟨19947, by rfl⟩ : syracuseStep 212773 = 39895) (by norm_num)
theorem B606005 : Blo 123787 606005 := bbase (se 5 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 606005 = 56813) (by norm_num)
theorem B180029 : Blo 123787 180029 := bbase (se 3 (by rfl) ⟨33755, by rfl⟩ : syracuseStep 180029 = 67511) (by norm_num)
theorem B212861 : Blo 123787 212861 := bbase (se 3 (by rfl) ⟨39911, by rfl⟩ : syracuseStep 212861 = 79823) (by norm_num)
theorem B507829 : Blo 123787 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B212989 : Blo 123787 212989 := bbase (se 3 (by rfl) ⟨39935, by rfl⟩ : syracuseStep 212989 = 79871) (by norm_num)
theorem B278549 : Blo 123787 278549 := bbase (se 6 (by rfl) ⟨6528, by rfl⟩ : syracuseStep 278549 = 13057) (by norm_num)
theorem B213077 : Blo 123787 213077 := bbase (se 8 (by rfl) ⟨1248, by rfl⟩ : syracuseStep 213077 = 2497) (by norm_num)
theorem B278621 : Blo 123787 278621 := bbase (se 3 (by rfl) ⟨52241, by rfl⟩ : syracuseStep 278621 = 104483) (by norm_num)
theorem B1130645 : Blo 123787 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B278693 : Blo 123787 278693 := bbase (se 4 (by rfl) ⟨26127, by rfl⟩ : syracuseStep 278693 = 52255) (by norm_num)
theorem B213205 : Blo 123787 213205 := bbase (se 7 (by rfl) ⟨2498, by rfl⟩ : syracuseStep 213205 = 4997) (by norm_num)
theorem B278765 : Blo 123787 278765 := bbase (se 3 (by rfl) ⟨52268, by rfl⟩ : syracuseStep 278765 = 104537) (by norm_num)
theorem B213229 : Blo 123787 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B475429 : Blo 123787 475429 := bbase (se 4 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 475429 = 89143) (by norm_num)
theorem B213293 : Blo 123787 213293 := bbase (se 3 (by rfl) ⟨39992, by rfl⟩ : syracuseStep 213293 = 79985) (by norm_num)
theorem B278837 : Blo 123787 278837 := bbase (se 5 (by rfl) ⟨13070, by rfl⟩ : syracuseStep 278837 = 26141) (by norm_num)
theorem B278909 : Blo 123787 278909 := bbase (se 3 (by rfl) ⟨52295, by rfl⟩ : syracuseStep 278909 = 104591) (by norm_num)
theorem B213421 : Blo 123787 213421 := bbase (se 3 (by rfl) ⟨40016, by rfl⟩ : syracuseStep 213421 = 80033) (by norm_num)
theorem B639413 : Blo 123787 639413 := bbase (se 5 (by rfl) ⟨29972, by rfl⟩ : syracuseStep 639413 = 59945) (by norm_num)
theorem B278981 : Blo 123787 278981 := bbase (se 4 (by rfl) ⟨26154, by rfl⟩ : syracuseStep 278981 = 52309) (by norm_num)
theorem B4047317 : Blo 123787 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B213509 : Blo 123787 213509 := bbase (se 4 (by rfl) ⟨20016, by rfl⟩ : syracuseStep 213509 = 40033) (by norm_num)
theorem B279053 : Blo 123787 279053 := bbase (se 3 (by rfl) ⟨52322, by rfl⟩ : syracuseStep 279053 = 104645) (by norm_num)
theorem B279125 : Blo 123787 279125 := bbase (se 8 (by rfl) ⟨1635, by rfl⟩ : syracuseStep 279125 = 3271) (by norm_num)
theorem B475733 : Blo 123787 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B213637 : Blo 123787 213637 := bbase (se 4 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 213637 = 40057) (by norm_num)
theorem B279197 : Blo 123787 279197 := bbase (se 3 (by rfl) ⟨52349, by rfl⟩ : syracuseStep 279197 = 104699) (by norm_num)
theorem B541397 : Blo 123787 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B213725 : Blo 123787 213725 := bbase (se 3 (by rfl) ⟨40073, by rfl⟩ : syracuseStep 213725 = 80147) (by norm_num)
theorem B279269 : Blo 123787 279269 := bbase (se 4 (by rfl) ⟨26181, by rfl⟩ : syracuseStep 279269 = 52363) (by norm_num)
theorem B279341 : Blo 123787 279341 := bbase (se 3 (by rfl) ⟨52376, by rfl⟩ : syracuseStep 279341 = 104753) (by norm_num)
theorem B213853 : Blo 123787 213853 := bbase (se 3 (by rfl) ⟨40097, by rfl⟩ : syracuseStep 213853 = 80195) (by norm_num)
theorem B279413 : Blo 123787 279413 := bbase (se 5 (by rfl) ⟨13097, by rfl⟩ : syracuseStep 279413 = 26195) (by norm_num)
theorem B574373 : Blo 123787 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B213941 : Blo 123787 213941 := bbase (se 5 (by rfl) ⟨10028, by rfl⟩ : syracuseStep 213941 = 20057) (by norm_num)
theorem B279485 : Blo 123787 279485 := bbase (se 3 (by rfl) ⟨52403, by rfl⟩ : syracuseStep 279485 = 104807) (by norm_num)
theorem B279557 : Blo 123787 279557 := bbase (se 4 (by rfl) ⟨26208, by rfl⟩ : syracuseStep 279557 = 52417) (by norm_num)
theorem B574517 : Blo 123787 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B214069 : Blo 123787 214069 := bbase (se 5 (by rfl) ⟨10034, by rfl⟩ : syracuseStep 214069 = 20069) (by norm_num)
theorem B279629 : Blo 123787 279629 := bbase (se 3 (by rfl) ⟨52430, by rfl⟩ : syracuseStep 279629 = 104861) (by norm_num)
theorem B541829 : Blo 123787 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B214157 : Blo 123787 214157 := bbase (se 3 (by rfl) ⟨40154, by rfl⟩ : syracuseStep 214157 = 80309) (by norm_num)
theorem B279701 : Blo 123787 279701 := bbase (se 6 (by rfl) ⟨6555, by rfl⟩ : syracuseStep 279701 = 13111) (by norm_num)
theorem B181453 : Blo 123787 181453 := bbase (se 3 (by rfl) ⟨34022, by rfl⟩ : syracuseStep 181453 = 68045) (by norm_num)
theorem B279773 : Blo 123787 279773 := bbase (se 3 (by rfl) ⟨52457, by rfl⟩ : syracuseStep 279773 = 104915) (by norm_num)
theorem B214285 : Blo 123787 214285 := bbase (se 3 (by rfl) ⟨40178, by rfl⟩ : syracuseStep 214285 = 80357) (by norm_num)
theorem B279845 : Blo 123787 279845 := bbase (se 4 (by rfl) ⟨26235, by rfl⟩ : syracuseStep 279845 = 52471) (by norm_num)
theorem B214309 : Blo 123787 214309 := bbase (se 4 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 214309 = 40183) (by norm_num)
theorem B673109 : Blo 123787 673109 := bbase (se 12 (by rfl) ⟨246, by rfl⟩ : syracuseStep 673109 = 493) (by norm_num)
theorem B181597 : Blo 123787 181597 := bbase (se 3 (by rfl) ⟨34049, by rfl⟩ : syracuseStep 181597 = 68099) (by norm_num)
theorem B214373 : Blo 123787 214373 := bbase (se 4 (by rfl) ⟨20097, by rfl⟩ : syracuseStep 214373 = 40195) (by norm_num)
theorem B279917 : Blo 123787 279917 := bbase (se 3 (by rfl) ⟨52484, by rfl⟩ : syracuseStep 279917 = 104969) (by norm_num)
theorem B378245 : Blo 123787 378245 := bbase (se 4 (by rfl) ⟨35460, by rfl⟩ : syracuseStep 378245 = 70921) (by norm_num)
theorem B607637 : Blo 123787 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B279989 : Blo 123787 279989 := bbase (se 5 (by rfl) ⟨13124, by rfl⟩ : syracuseStep 279989 = 26249) (by norm_num)
theorem B1295797 : Blo 123787 1295797 := bbase (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) (by norm_num)
theorem B2803157 : Blo 123787 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B214501 : Blo 123787 214501 := bbase (se 4 (by rfl) ⟨20109, by rfl⟩ : syracuseStep 214501 = 40219) (by norm_num)
theorem B280061 : Blo 123787 280061 := bbase (se 3 (by rfl) ⟨52511, by rfl⟩ : syracuseStep 280061 = 105023) (by norm_num)
theorem B149041 : Blo 123787 149041 := bbase (se 2 (by rfl) ⟨55890, by rfl⟩ : syracuseStep 149041 = 111781) (by norm_num)
theorem B149045 : Blo 123787 149045 := bbase (se 5 (by rfl) ⟨6986, by rfl⟩ : syracuseStep 149045 = 13973) (by norm_num)
theorem B214589 : Blo 123787 214589 := bbase (se 3 (by rfl) ⟨40235, by rfl⟩ : syracuseStep 214589 = 80471) (by norm_num)
theorem B280133 : Blo 123787 280133 := bbase (se 4 (by rfl) ⟨26262, by rfl⟩ : syracuseStep 280133 = 52525) (by norm_num)
theorem B280205 : Blo 123787 280205 := bbase (se 3 (by rfl) ⟨52538, by rfl⟩ : syracuseStep 280205 = 105077) (by norm_num)
theorem B214717 : Blo 123787 214717 := bbase (se 3 (by rfl) ⟨40259, by rfl⟩ : syracuseStep 214717 = 80519) (by norm_num)
theorem B476869 : Blo 123787 476869 := bbase (se 4 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 476869 = 89413) (by norm_num)
theorem B640709 : Blo 123787 640709 := bbase (se 4 (by rfl) ⟨60066, by rfl⟩ : syracuseStep 640709 = 120133) (by norm_num)
theorem B280277 : Blo 123787 280277 := bbase (se 7 (by rfl) ⟨3284, by rfl⟩ : syracuseStep 280277 = 6569) (by norm_num)
theorem B1066709 : Blo 123787 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B214805 : Blo 123787 214805 := bbase (se 6 (by rfl) ⟨5034, by rfl⟩ : syracuseStep 214805 = 10069) (by norm_num)
theorem B280349 : Blo 123787 280349 := bbase (se 3 (by rfl) ⟨52565, by rfl⟩ : syracuseStep 280349 = 105131) (by norm_num)
theorem B149321 : Blo 123787 149321 := bbase (se 2 (by rfl) ⟨55995, by rfl⟩ : syracuseStep 149321 = 111991) (by norm_num)
theorem B280421 : Blo 123787 280421 := bbase (se 4 (by rfl) ⟨26289, by rfl⟩ : syracuseStep 280421 = 52579) (by norm_num)
theorem B804725 : Blo 123787 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B214933 : Blo 123787 214933 := bbase (se 6 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 214933 = 10075) (by norm_num)
theorem B968597 : Blo 123787 968597 := bbase (se 6 (by rfl) ⟨22701, by rfl⟩ : syracuseStep 968597 = 45403) (by norm_num)
theorem B280493 : Blo 123787 280493 := bbase (se 3 (by rfl) ⟨52592, by rfl⟩ : syracuseStep 280493 = 105185) (by norm_num)
theorem B149449 : Blo 123787 149449 := bbase (se 2 (by rfl) ⟨56043, by rfl⟩ : syracuseStep 149449 = 112087) (by norm_num)
theorem B215021 : Blo 123787 215021 := bbase (se 3 (by rfl) ⟨40316, by rfl⟩ : syracuseStep 215021 = 80633) (by norm_num)
theorem B280565 : Blo 123787 280565 := bbase (se 5 (by rfl) ⟨13151, by rfl⟩ : syracuseStep 280565 = 26303) (by norm_num)
theorem B280637 : Blo 123787 280637 := bbase (se 3 (by rfl) ⟨52619, by rfl⟩ : syracuseStep 280637 = 105239) (by norm_num)
theorem B215117 : Blo 123787 215117 := bbase (se 3 (by rfl) ⟨40334, by rfl⟩ : syracuseStep 215117 = 80669) (by norm_num)
theorem B313429 : Blo 123787 313429 := bbase (se 8 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 313429 = 3673) (by norm_num)
theorem B542821 : Blo 123787 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B215149 : Blo 123787 215149 := bbase (se 3 (by rfl) ⟨40340, by rfl⟩ : syracuseStep 215149 = 80681) (by norm_num)
theorem B280709 : Blo 123787 280709 := bbase (se 4 (by rfl) ⟨26316, by rfl⟩ : syracuseStep 280709 = 52633) (by norm_num)
theorem B313541 : Blo 123787 313541 := bbase (se 4 (by rfl) ⟨29394, by rfl⟩ : syracuseStep 313541 = 58789) (by norm_num)
theorem B215237 : Blo 123787 215237 := bbase (se 4 (by rfl) ⟨20178, by rfl⟩ : syracuseStep 215237 = 40357) (by norm_num)
theorem B280781 : Blo 123787 280781 := bbase (se 3 (by rfl) ⟨52646, by rfl⟩ : syracuseStep 280781 = 105293) (by norm_num)
theorem B280853 : Blo 123787 280853 := bbase (se 6 (by rfl) ⟨6582, by rfl⟩ : syracuseStep 280853 = 13165) (by norm_num)
theorem B215365 : Blo 123787 215365 := bbase (se 4 (by rfl) ⟨20190, by rfl⟩ : syracuseStep 215365 = 40381) (by norm_num)
theorem B280925 : Blo 123787 280925 := bbase (se 3 (by rfl) ⟨52673, by rfl⟩ : syracuseStep 280925 = 105347) (by norm_num)
theorem B313733 : Blo 123787 313733 := bbase (se 4 (by rfl) ⟨29412, by rfl⟩ : syracuseStep 313733 = 58825) (by norm_num)
theorem B215453 : Blo 123787 215453 := bbase (se 3 (by rfl) ⟨40397, by rfl⟩ : syracuseStep 215453 = 80795) (by norm_num)
theorem B280997 : Blo 123787 280997 := bbase (se 4 (by rfl) ⟨26343, by rfl⟩ : syracuseStep 280997 = 52687) (by norm_num)
theorem B281069 : Blo 123787 281069 := bbase (se 3 (by rfl) ⟨52700, by rfl⟩ : syracuseStep 281069 = 105401) (by norm_num)
theorem B215581 : Blo 123787 215581 := bbase (se 3 (by rfl) ⟨40421, by rfl⟩ : syracuseStep 215581 = 80843) (by norm_num)
theorem B281141 : Blo 123787 281141 := bbase (se 5 (by rfl) ⟨13178, by rfl⟩ : syracuseStep 281141 = 26357) (by norm_num)
theorem B281213 : Blo 123787 281213 := bbase (se 3 (by rfl) ⟨52727, by rfl⟩ : syracuseStep 281213 = 105455) (by norm_num)
theorem B477845 : Blo 123787 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B281285 : Blo 123787 281285 := bbase (se 4 (by rfl) ⟨26370, by rfl⟩ : syracuseStep 281285 = 52741) (by norm_num)
theorem B314077 : Blo 123787 314077 := bbase (se 3 (by rfl) ⟨58889, by rfl⟩ : syracuseStep 314077 = 117779) (by norm_num)
theorem B281357 : Blo 123787 281357 := bbase (se 3 (by rfl) ⟨52754, by rfl⟩ : syracuseStep 281357 = 105509) (by norm_num)
theorem B314189 : Blo 123787 314189 := bbase (se 3 (by rfl) ⟨58910, by rfl⟩ : syracuseStep 314189 = 117821) (by norm_num)
theorem B281429 : Blo 123787 281429 := bbase (se 9 (by rfl) ⟨824, by rfl⟩ : syracuseStep 281429 = 1649) (by norm_num)
theorem B281501 : Blo 123787 281501 := bbase (se 3 (by rfl) ⟨52781, by rfl⟩ : syracuseStep 281501 = 105563) (by norm_num)
theorem B478133 : Blo 123787 478133 := bbase (se 5 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 478133 = 44825) (by norm_num)
theorem B642005 : Blo 123787 642005 := bbase (se 7 (by rfl) ⟨7523, by rfl⟩ : syracuseStep 642005 = 15047) (by norm_num)
theorem B281573 : Blo 123787 281573 := bbase (se 4 (by rfl) ⟨26397, by rfl⟩ : syracuseStep 281573 = 52795) (by norm_num)
theorem B248845 : Blo 123787 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B314381 : Blo 123787 314381 := bbase (se 3 (by rfl) ⟨58946, by rfl⟩ : syracuseStep 314381 = 117893) (by norm_num)
theorem B281645 : Blo 123787 281645 := bbase (se 3 (by rfl) ⟨52808, by rfl⟩ : syracuseStep 281645 = 105617) (by norm_num)
theorem B281717 : Blo 123787 281717 := bbase (se 5 (by rfl) ⟨13205, by rfl⟩ : syracuseStep 281717 = 26411) (by norm_num)
theorem B281789 : Blo 123787 281789 := bbase (se 3 (by rfl) ⟨52835, by rfl⟩ : syracuseStep 281789 = 105671) (by norm_num)
theorem B281861 : Blo 123787 281861 := bbase (se 4 (by rfl) ⟨26424, by rfl⟩ : syracuseStep 281861 = 52849) (by norm_num)
theorem B150833 : Blo 123787 150833 := bbase (se 2 (by rfl) ⟨56562, by rfl⟩ : syracuseStep 150833 = 113125) (by norm_num)
theorem B281933 : Blo 123787 281933 := bbase (se 3 (by rfl) ⟨52862, by rfl⟩ : syracuseStep 281933 = 105725) (by norm_num)
theorem B314725 : Blo 123787 314725 := bbase (se 4 (by rfl) ⟨29505, by rfl⟩ : syracuseStep 314725 = 59011) (by norm_num)
theorem B282005 : Blo 123787 282005 := bbase (se 6 (by rfl) ⟨6609, by rfl⟩ : syracuseStep 282005 = 13219) (by norm_num)
theorem B314837 : Blo 123787 314837 := bbase (se 7 (by rfl) ⟨3689, by rfl⟩ : syracuseStep 314837 = 7379) (by norm_num)
theorem B282077 : Blo 123787 282077 := bbase (se 3 (by rfl) ⟨52889, by rfl⟩ : syracuseStep 282077 = 105779) (by norm_num)
theorem B216589 : Blo 123787 216589 := bbase (se 3 (by rfl) ⟨40610, by rfl⟩ : syracuseStep 216589 = 81221) (by norm_num)
theorem B282149 : Blo 123787 282149 := bbase (se 4 (by rfl) ⟨26451, by rfl⟩ : syracuseStep 282149 = 52903) (by norm_num)
theorem B151093 : Blo 123787 151093 := bbase (se 5 (by rfl) ⟨7082, by rfl⟩ : syracuseStep 151093 = 14165) (by norm_num)
theorem B151141 : Blo 123787 151141 := bbase (se 4 (by rfl) ⟨14169, by rfl⟩ : syracuseStep 151141 = 28339) (by norm_num)
theorem B282221 : Blo 123787 282221 := bbase (se 3 (by rfl) ⟨52916, by rfl⟩ : syracuseStep 282221 = 105833) (by norm_num)
theorem B380533 : Blo 123787 380533 := bbase (se 5 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 380533 = 35675) (by norm_num)
theorem B315029 : Blo 123787 315029 := bbase (se 6 (by rfl) ⟨7383, by rfl⟩ : syracuseStep 315029 = 14767) (by norm_num)
theorem B282293 : Blo 123787 282293 := bbase (se 5 (by rfl) ⟨13232, by rfl⟩ : syracuseStep 282293 = 26465) (by norm_num)
theorem B282365 : Blo 123787 282365 := bbase (se 3 (by rfl) ⟨52943, by rfl⟩ : syracuseStep 282365 = 105887) (by norm_num)
theorem B282437 : Blo 123787 282437 := bbase (se 4 (by rfl) ⟨26478, by rfl⟩ : syracuseStep 282437 = 52957) (by norm_num)
theorem B184133 : Blo 123787 184133 := bbase (se 4 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 184133 = 34525) (by norm_num)
theorem B282509 : Blo 123787 282509 := bbase (se 3 (by rfl) ⟨52970, by rfl⟩ : syracuseStep 282509 = 105941) (by norm_num)
theorem B282581 : Blo 123787 282581 := bbase (se 7 (by rfl) ⟨3311, by rfl⟩ : syracuseStep 282581 = 6623) (by norm_num)
theorem B315373 : Blo 123787 315373 := bbase (se 3 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 315373 = 118265) (by norm_num)
theorem B282653 : Blo 123787 282653 := bbase (se 3 (by rfl) ⟨52997, by rfl⟩ : syracuseStep 282653 = 105995) (by norm_num)
theorem B479317 : Blo 123787 479317 := bbase (se 8 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 479317 = 5617) (by norm_num)
theorem B315485 : Blo 123787 315485 := bbase (se 3 (by rfl) ⟨59153, by rfl⟩ : syracuseStep 315485 = 118307) (by norm_num)
theorem B282725 : Blo 123787 282725 := bbase (se 4 (by rfl) ⟨26505, by rfl⟩ : syracuseStep 282725 = 53011) (by norm_num)
theorem B282797 : Blo 123787 282797 := bbase (se 3 (by rfl) ⟨53024, by rfl⟩ : syracuseStep 282797 = 106049) (by norm_num)
theorem B643301 : Blo 123787 643301 := bbase (se 4 (by rfl) ⟨60309, by rfl⟩ : syracuseStep 643301 = 120619) (by norm_num)
theorem B282869 : Blo 123787 282869 := bbase (se 5 (by rfl) ⟨13259, by rfl⟩ : syracuseStep 282869 = 26519) (by norm_num)
theorem B151813 : Blo 123787 151813 := bbase (se 4 (by rfl) ⟨14232, by rfl⟩ : syracuseStep 151813 = 28465) (by norm_num)
theorem B315677 : Blo 123787 315677 := bbase (se 3 (by rfl) ⟨59189, by rfl⟩ : syracuseStep 315677 = 118379) (by norm_num)
theorem B282941 : Blo 123787 282941 := bbase (se 3 (by rfl) ⟨53051, by rfl⟩ : syracuseStep 282941 = 106103) (by norm_num)
theorem B283013 : Blo 123787 283013 := bbase (se 4 (by rfl) ⟨26532, by rfl⟩ : syracuseStep 283013 = 53065) (by norm_num)
theorem B479621 : Blo 123787 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B283085 : Blo 123787 283085 := bbase (se 3 (by rfl) ⟨53078, by rfl⟩ : syracuseStep 283085 = 106157) (by norm_num)
theorem B1102325 : Blo 123787 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B283157 : Blo 123787 283157 := bbase (se 6 (by rfl) ⟨6636, by rfl⟩ : syracuseStep 283157 = 13273) (by norm_num)
theorem B283229 : Blo 123787 283229 := bbase (se 3 (by rfl) ⟨53105, by rfl⟩ : syracuseStep 283229 = 106211) (by norm_num)
theorem B316021 : Blo 123787 316021 := bbase (se 5 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 316021 = 29627) (by norm_num)
theorem B1069685 : Blo 123787 1069685 := bbase (se 5 (by rfl) ⟨50141, by rfl⟩ : syracuseStep 1069685 = 100283) (by norm_num)
theorem B283301 : Blo 123787 283301 := bbase (se 4 (by rfl) ⟨26559, by rfl⟩ : syracuseStep 283301 = 53119) (by norm_num)
theorem B316133 : Blo 123787 316133 := bbase (se 4 (by rfl) ⟨29637, by rfl⟩ : syracuseStep 316133 = 59275) (by norm_num)
theorem B283373 : Blo 123787 283373 := bbase (se 3 (by rfl) ⟨53132, by rfl⟩ : syracuseStep 283373 = 106265) (by norm_num)
theorem B283445 : Blo 123787 283445 := bbase (se 5 (by rfl) ⟨13286, by rfl⟩ : syracuseStep 283445 = 26573) (by norm_num)
theorem B283517 : Blo 123787 283517 := bbase (se 3 (by rfl) ⟨53159, by rfl⟩ : syracuseStep 283517 = 106319) (by norm_num)
theorem B316325 : Blo 123787 316325 := bbase (se 4 (by rfl) ⟨29655, by rfl⟩ : syracuseStep 316325 = 59311) (by norm_num)
theorem B283589 : Blo 123787 283589 := bbase (se 4 (by rfl) ⟨26586, by rfl⟩ : syracuseStep 283589 = 53173) (by norm_num)
theorem B1004501 : Blo 123787 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B283661 : Blo 123787 283661 := bbase (se 3 (by rfl) ⟨53186, by rfl⟩ : syracuseStep 283661 = 106373) (by norm_num)
theorem B283733 : Blo 123787 283733 := bbase (se 8 (by rfl) ⟨1662, by rfl⟩ : syracuseStep 283733 = 3325) (by norm_num)
theorem B283805 : Blo 123787 283805 := bbase (se 3 (by rfl) ⟨53213, by rfl⟩ : syracuseStep 283805 = 106427) (by norm_num)
theorem B283877 : Blo 123787 283877 := bbase (se 4 (by rfl) ⟨26613, by rfl⟩ : syracuseStep 283877 = 53227) (by norm_num)
theorem B152813 : Blo 123787 152813 := bbase (se 3 (by rfl) ⟨28652, by rfl⟩ : syracuseStep 152813 = 57305) (by norm_num)
theorem B316669 : Blo 123787 316669 := bbase (se 3 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 316669 = 118751) (by norm_num)
theorem B283949 : Blo 123787 283949 := bbase (se 3 (by rfl) ⟨53240, by rfl⟩ : syracuseStep 283949 = 106481) (by norm_num)
theorem B152885 : Blo 123787 152885 := bbase (se 5 (by rfl) ⟨7166, by rfl⟩ : syracuseStep 152885 = 14333) (by norm_num)
theorem B185693 : Blo 123787 185693 := bbase (se 3 (by rfl) ⟨34817, by rfl⟩ : syracuseStep 185693 = 69635) (by norm_num)
theorem B316781 : Blo 123787 316781 := bbase (se 3 (by rfl) ⟨59396, by rfl⟩ : syracuseStep 316781 = 118793) (by norm_num)
theorem B185717 : Blo 123787 185717 := bbase (se 5 (by rfl) ⟨8705, by rfl⟩ : syracuseStep 185717 = 17411) (by norm_num)
theorem B284021 : Blo 123787 284021 := bbase (se 5 (by rfl) ⟨13313, by rfl⟩ : syracuseStep 284021 = 26627) (by norm_num)
theorem B185741 : Blo 123787 185741 := bbase (se 3 (by rfl) ⟨34826, by rfl⟩ : syracuseStep 185741 = 69653) (by norm_num)
theorem B185765 : Blo 123787 185765 := bbase (se 4 (by rfl) ⟨17415, by rfl⟩ : syracuseStep 185765 = 34831) (by norm_num)
theorem B185789 : Blo 123787 185789 := bbase (se 3 (by rfl) ⟨34835, by rfl⟩ : syracuseStep 185789 = 69671) (by norm_num)
theorem B284093 : Blo 123787 284093 := bbase (se 3 (by rfl) ⟨53267, by rfl⟩ : syracuseStep 284093 = 106535) (by norm_num)
theorem B185813 : Blo 123787 185813 := bbase (se 7 (by rfl) ⟨2177, by rfl⟩ : syracuseStep 185813 = 4355) (by norm_num)
theorem B185837 : Blo 123787 185837 := bbase (se 3 (by rfl) ⟨34844, by rfl⟩ : syracuseStep 185837 = 69689) (by norm_num)
theorem B644597 : Blo 123787 644597 := bbase (se 5 (by rfl) ⟨30215, by rfl⟩ : syracuseStep 644597 = 60431) (by norm_num)
theorem B185861 : Blo 123787 185861 := bbase (se 4 (by rfl) ⟨17424, by rfl⟩ : syracuseStep 185861 = 34849) (by norm_num)
theorem B284165 : Blo 123787 284165 := bbase (se 4 (by rfl) ⟨26640, by rfl⟩ : syracuseStep 284165 = 53281) (by norm_num)
theorem B185885 : Blo 123787 185885 := bbase (se 3 (by rfl) ⟨34853, by rfl⟩ : syracuseStep 185885 = 69707) (by norm_num)
theorem B316973 : Blo 123787 316973 := bbase (se 3 (by rfl) ⟨59432, by rfl⟩ : syracuseStep 316973 = 118865) (by norm_num)
theorem B185909 : Blo 123787 185909 := bbase (se 5 (by rfl) ⟨8714, by rfl⟩ : syracuseStep 185909 = 17429) (by norm_num)
theorem B874037 : Blo 123787 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B185933 : Blo 123787 185933 := bbase (se 3 (by rfl) ⟨34862, by rfl⟩ : syracuseStep 185933 = 69725) (by norm_num)
theorem B284237 : Blo 123787 284237 := bbase (se 3 (by rfl) ⟨53294, by rfl⟩ : syracuseStep 284237 = 106589) (by norm_num)
theorem B185957 : Blo 123787 185957 := bbase (se 4 (by rfl) ⟨17433, by rfl⟩ : syracuseStep 185957 = 34867) (by norm_num)
theorem B153193 : Blo 123787 153193 := bbase (se 2 (by rfl) ⟨57447, by rfl⟩ : syracuseStep 153193 = 114895) (by norm_num)
theorem B185981 : Blo 123787 185981 := bbase (se 3 (by rfl) ⟨34871, by rfl⟩ : syracuseStep 185981 = 69743) (by norm_num)
theorem B186005 : Blo 123787 186005 := bbase (se 6 (by rfl) ⟨4359, by rfl⟩ : syracuseStep 186005 = 8719) (by norm_num)
theorem B284309 : Blo 123787 284309 := bbase (se 6 (by rfl) ⟨6663, by rfl⟩ : syracuseStep 284309 = 13327) (by norm_num)
theorem B186029 : Blo 123787 186029 := bbase (se 3 (by rfl) ⟨34880, by rfl⟩ : syracuseStep 186029 = 69761) (by norm_num)
theorem B186053 : Blo 123787 186053 := bbase (se 4 (by rfl) ⟨17442, by rfl⟩ : syracuseStep 186053 = 34885) (by norm_num)
theorem B186077 : Blo 123787 186077 := bbase (se 3 (by rfl) ⟨34889, by rfl⟩ : syracuseStep 186077 = 69779) (by norm_num)
theorem B284381 : Blo 123787 284381 := bbase (se 3 (by rfl) ⟨53321, by rfl⟩ : syracuseStep 284381 = 106643) (by norm_num)
theorem B186101 : Blo 123787 186101 := bbase (se 5 (by rfl) ⟨8723, by rfl⟩ : syracuseStep 186101 = 17447) (by norm_num)
theorem B186125 : Blo 123787 186125 := bbase (se 3 (by rfl) ⟨34898, by rfl⟩ : syracuseStep 186125 = 69797) (by norm_num)
theorem B153361 : Blo 123787 153361 := bbase (se 2 (by rfl) ⟨57510, by rfl⟩ : syracuseStep 153361 = 115021) (by norm_num)
theorem B186149 : Blo 123787 186149 := bbase (se 4 (by rfl) ⟨17451, by rfl⟩ : syracuseStep 186149 = 34903) (by norm_num)
theorem B284453 : Blo 123787 284453 := bbase (se 4 (by rfl) ⟨26667, by rfl⟩ : syracuseStep 284453 = 53335) (by norm_num)
theorem B186173 : Blo 123787 186173 := bbase (se 3 (by rfl) ⟨34907, by rfl⟩ : syracuseStep 186173 = 69815) (by norm_num)
theorem B153409 : Blo 123787 153409 := bbase (se 2 (by rfl) ⟨57528, by rfl⟩ : syracuseStep 153409 = 115057) (by norm_num)
theorem B186197 : Blo 123787 186197 := bbase (se 9 (by rfl) ⟨545, by rfl⟩ : syracuseStep 186197 = 1091) (by norm_num)
theorem B186221 : Blo 123787 186221 := bbase (se 3 (by rfl) ⟨34916, by rfl⟩ : syracuseStep 186221 = 69833) (by norm_num)
theorem B284525 : Blo 123787 284525 := bbase (se 3 (by rfl) ⟨53348, by rfl⟩ : syracuseStep 284525 = 106697) (by norm_num)
theorem B186245 : Blo 123787 186245 := bbase (se 4 (by rfl) ⟨17460, by rfl⟩ : syracuseStep 186245 = 34921) (by norm_num)
theorem B317317 : Blo 123787 317317 := bbase (se 4 (by rfl) ⟨29748, by rfl⟩ : syracuseStep 317317 = 59497) (by norm_num)
theorem B186269 : Blo 123787 186269 := bbase (se 3 (by rfl) ⟨34925, by rfl⟩ : syracuseStep 186269 = 69851) (by norm_num)
theorem B153505 : Blo 123787 153505 := bbase (se 2 (by rfl) ⟨57564, by rfl⟩ : syracuseStep 153505 = 115129) (by norm_num)
theorem B186293 : Blo 123787 186293 := bbase (se 5 (by rfl) ⟨8732, by rfl⟩ : syracuseStep 186293 = 17465) (by norm_num)
theorem B284597 : Blo 123787 284597 := bbase (se 5 (by rfl) ⟨13340, by rfl⟩ : syracuseStep 284597 = 26681) (by norm_num)
theorem B186317 : Blo 123787 186317 := bbase (se 3 (by rfl) ⟨34934, by rfl⟩ : syracuseStep 186317 = 69869) (by norm_num)
theorem B186341 : Blo 123787 186341 := bbase (se 4 (by rfl) ⟨17469, by rfl⟩ : syracuseStep 186341 = 34939) (by norm_num)
theorem B317429 : Blo 123787 317429 := bbase (se 5 (by rfl) ⟨14879, by rfl⟩ : syracuseStep 317429 = 29759) (by norm_num)
theorem B186365 : Blo 123787 186365 := bbase (se 3 (by rfl) ⟨34943, by rfl⟩ : syracuseStep 186365 = 69887) (by norm_num)
theorem B284669 : Blo 123787 284669 := bbase (se 3 (by rfl) ⟨53375, by rfl⟩ : syracuseStep 284669 = 106751) (by norm_num)
theorem B186389 : Blo 123787 186389 := bbase (se 6 (by rfl) ⟨4368, by rfl⟩ : syracuseStep 186389 = 8737) (by norm_num)
theorem B186413 : Blo 123787 186413 := bbase (se 3 (by rfl) ⟨34952, by rfl⟩ : syracuseStep 186413 = 69905) (by norm_num)
theorem B186437 : Blo 123787 186437 := bbase (se 4 (by rfl) ⟨17478, by rfl⟩ : syracuseStep 186437 = 34957) (by norm_num)
theorem B284741 : Blo 123787 284741 := bbase (se 4 (by rfl) ⟨26694, by rfl⟩ : syracuseStep 284741 = 53389) (by norm_num)
theorem B186461 : Blo 123787 186461 := bbase (se 3 (by rfl) ⟨34961, by rfl⟩ : syracuseStep 186461 = 69923) (by norm_num)
theorem B186485 : Blo 123787 186485 := bbase (se 5 (by rfl) ⟨8741, by rfl⟩ : syracuseStep 186485 = 17483) (by norm_num)
theorem B252029 : Blo 123787 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B186509 : Blo 123787 186509 := bbase (se 3 (by rfl) ⟨34970, by rfl⟩ : syracuseStep 186509 = 69941) (by norm_num)
theorem B284813 : Blo 123787 284813 := bbase (se 3 (by rfl) ⟨53402, by rfl⟩ : syracuseStep 284813 = 106805) (by norm_num)
theorem B186533 : Blo 123787 186533 := bbase (se 4 (by rfl) ⟨17487, by rfl⟩ : syracuseStep 186533 = 34975) (by norm_num)
theorem B317621 : Blo 123787 317621 := bbase (se 5 (by rfl) ⟨14888, by rfl⟩ : syracuseStep 317621 = 29777) (by norm_num)
theorem B186557 : Blo 123787 186557 := bbase (se 3 (by rfl) ⟨34979, by rfl⟩ : syracuseStep 186557 = 69959) (by norm_num)
theorem B186581 : Blo 123787 186581 := bbase (se 7 (by rfl) ⟨2186, by rfl⟩ : syracuseStep 186581 = 4373) (by norm_num)
theorem B284885 : Blo 123787 284885 := bbase (se 7 (by rfl) ⟨3338, by rfl⟩ : syracuseStep 284885 = 6677) (by norm_num)
theorem B186605 : Blo 123787 186605 := bbase (se 3 (by rfl) ⟨34988, by rfl⟩ : syracuseStep 186605 = 69977) (by norm_num)
theorem B186629 : Blo 123787 186629 := bbase (se 4 (by rfl) ⟨17496, by rfl⟩ : syracuseStep 186629 = 34993) (by norm_num)
theorem B186653 : Blo 123787 186653 := bbase (se 3 (by rfl) ⟨34997, by rfl⟩ : syracuseStep 186653 = 69995) (by norm_num)
theorem B284957 : Blo 123787 284957 := bbase (se 3 (by rfl) ⟨53429, by rfl⟩ : syracuseStep 284957 = 106859) (by norm_num)
theorem B186677 : Blo 123787 186677 := bbase (se 5 (by rfl) ⟨8750, by rfl⟩ : syracuseStep 186677 = 17501) (by norm_num)
theorem B186701 : Blo 123787 186701 := bbase (se 3 (by rfl) ⟨35006, by rfl⟩ : syracuseStep 186701 = 70013) (by norm_num)
theorem B186725 : Blo 123787 186725 := bbase (se 4 (by rfl) ⟨17505, by rfl⟩ : syracuseStep 186725 = 35011) (by norm_num)
theorem B285029 : Blo 123787 285029 := bbase (se 4 (by rfl) ⟨26721, by rfl⟩ : syracuseStep 285029 = 53443) (by norm_num)
theorem B186749 : Blo 123787 186749 := bbase (se 3 (by rfl) ⟨35015, by rfl⟩ : syracuseStep 186749 = 70031) (by norm_num)
theorem B186773 : Blo 123787 186773 := bbase (se 6 (by rfl) ⟨4377, by rfl⟩ : syracuseStep 186773 = 8755) (by norm_num)
theorem B186797 : Blo 123787 186797 := bbase (se 3 (by rfl) ⟨35024, by rfl⟩ : syracuseStep 186797 = 70049) (by norm_num)
theorem B285101 : Blo 123787 285101 := bbase (se 3 (by rfl) ⟨53456, by rfl⟩ : syracuseStep 285101 = 106913) (by norm_num)
theorem B186821 : Blo 123787 186821 := bbase (se 4 (by rfl) ⟨17514, by rfl⟩ : syracuseStep 186821 = 35029) (by norm_num)
theorem B481733 : Blo 123787 481733 := bbase (se 4 (by rfl) ⟨45162, by rfl⟩ : syracuseStep 481733 = 90325) (by norm_num)
theorem B186845 : Blo 123787 186845 := bbase (se 3 (by rfl) ⟨35033, by rfl⟩ : syracuseStep 186845 = 70067) (by norm_num)
theorem B186869 : Blo 123787 186869 := bbase (se 5 (by rfl) ⟨8759, by rfl⟩ : syracuseStep 186869 = 17519) (by norm_num)
theorem B285173 : Blo 123787 285173 := bbase (se 5 (by rfl) ⟨13367, by rfl⟩ : syracuseStep 285173 = 26735) (by norm_num)
theorem B186893 : Blo 123787 186893 := bbase (se 3 (by rfl) ⟨35042, by rfl⟩ : syracuseStep 186893 = 70085) (by norm_num)
theorem B317965 : Blo 123787 317965 := bbase (se 3 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 317965 = 119237) (by norm_num)
theorem B186917 : Blo 123787 186917 := bbase (se 4 (by rfl) ⟨17523, by rfl⟩ : syracuseStep 186917 = 35047) (by norm_num)
theorem B383525 : Blo 123787 383525 := bbase (se 4 (by rfl) ⟨35955, by rfl⟩ : syracuseStep 383525 = 71911) (by norm_num)
theorem B186941 : Blo 123787 186941 := bbase (se 3 (by rfl) ⟨35051, by rfl⟩ : syracuseStep 186941 = 70103) (by norm_num)
theorem B285245 : Blo 123787 285245 := bbase (se 3 (by rfl) ⟨53483, by rfl⟩ : syracuseStep 285245 = 106967) (by norm_num)
theorem B186965 : Blo 123787 186965 := bbase (se 8 (by rfl) ⟨1095, by rfl⟩ : syracuseStep 186965 = 2191) (by norm_num)
theorem B186989 : Blo 123787 186989 := bbase (se 3 (by rfl) ⟨35060, by rfl⟩ : syracuseStep 186989 = 70121) (by norm_num)
theorem B318077 : Blo 123787 318077 := bbase (se 3 (by rfl) ⟨59639, by rfl⟩ : syracuseStep 318077 = 119279) (by norm_num)
theorem B187013 : Blo 123787 187013 := bbase (se 4 (by rfl) ⟨17532, by rfl⟩ : syracuseStep 187013 = 35065) (by norm_num)
theorem B285317 : Blo 123787 285317 := bbase (se 4 (by rfl) ⟨26748, by rfl⟩ : syracuseStep 285317 = 53497) (by norm_num)
theorem B187037 : Blo 123787 187037 := bbase (se 3 (by rfl) ⟨35069, by rfl⟩ : syracuseStep 187037 = 70139) (by norm_num)
theorem B187061 : Blo 123787 187061 := bbase (se 5 (by rfl) ⟨8768, by rfl⟩ : syracuseStep 187061 = 17537) (by norm_num)
theorem B187085 : Blo 123787 187085 := bbase (se 3 (by rfl) ⟨35078, by rfl⟩ : syracuseStep 187085 = 70157) (by norm_num)
theorem B285389 : Blo 123787 285389 := bbase (se 3 (by rfl) ⟨53510, by rfl⟩ : syracuseStep 285389 = 107021) (by norm_num)
theorem B187109 : Blo 123787 187109 := bbase (se 4 (by rfl) ⟨17541, by rfl⟩ : syracuseStep 187109 = 35083) (by norm_num)
theorem B482021 : Blo 123787 482021 := bbase (se 4 (by rfl) ⟨45189, by rfl⟩ : syracuseStep 482021 = 90379) (by norm_num)
theorem B711413 : Blo 123787 711413 := bbase (se 5 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 711413 = 66695) (by norm_num)
theorem B187133 : Blo 123787 187133 := bbase (se 3 (by rfl) ⟨35087, by rfl⟩ : syracuseStep 187133 = 70175) (by norm_num)
theorem B645893 : Blo 123787 645893 := bbase (se 4 (by rfl) ⟨60552, by rfl⟩ : syracuseStep 645893 = 121105) (by norm_num)
theorem B187157 : Blo 123787 187157 := bbase (se 6 (by rfl) ⟨4386, by rfl⟩ : syracuseStep 187157 = 8773) (by norm_num)
theorem B285461 : Blo 123787 285461 := bbase (se 6 (by rfl) ⟨6690, by rfl⟩ : syracuseStep 285461 = 13381) (by norm_num)
theorem B187181 : Blo 123787 187181 := bbase (se 3 (by rfl) ⟨35096, by rfl⟩ : syracuseStep 187181 = 70193) (by norm_num)
theorem B318269 : Blo 123787 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B187205 : Blo 123787 187205 := bbase (se 4 (by rfl) ⟨17550, by rfl⟩ : syracuseStep 187205 = 35101) (by norm_num)
theorem B187229 : Blo 123787 187229 := bbase (se 3 (by rfl) ⟨35105, by rfl⟩ : syracuseStep 187229 = 70211) (by norm_num)
theorem B285533 : Blo 123787 285533 := bbase (se 3 (by rfl) ⟨53537, by rfl⟩ : syracuseStep 285533 = 107075) (by norm_num)
theorem B187253 : Blo 123787 187253 := bbase (se 5 (by rfl) ⟨8777, by rfl⟩ : syracuseStep 187253 = 17555) (by norm_num)
theorem B187277 : Blo 123787 187277 := bbase (se 3 (by rfl) ⟨35114, by rfl⟩ : syracuseStep 187277 = 70229) (by norm_num)
theorem B187301 : Blo 123787 187301 := bbase (se 4 (by rfl) ⟨17559, by rfl⟩ : syracuseStep 187301 = 35119) (by norm_num)
theorem B285605 : Blo 123787 285605 := bbase (se 4 (by rfl) ⟨26775, by rfl⟩ : syracuseStep 285605 = 53551) (by norm_num)
theorem B187325 : Blo 123787 187325 := bbase (se 3 (by rfl) ⟨35123, by rfl⟩ : syracuseStep 187325 = 70247) (by norm_num)
theorem B187349 : Blo 123787 187349 := bbase (se 7 (by rfl) ⟨2195, by rfl⟩ : syracuseStep 187349 = 4391) (by norm_num)
theorem B187373 : Blo 123787 187373 := bbase (se 3 (by rfl) ⟨35132, by rfl⟩ : syracuseStep 187373 = 70265) (by norm_num)
theorem B285677 : Blo 123787 285677 := bbase (se 3 (by rfl) ⟨53564, by rfl⟩ : syracuseStep 285677 = 107129) (by norm_num)
theorem B187397 : Blo 123787 187397 := bbase (se 4 (by rfl) ⟨17568, by rfl⟩ : syracuseStep 187397 = 35137) (by norm_num)
theorem B187421 : Blo 123787 187421 := bbase (se 3 (by rfl) ⟨35141, by rfl⟩ : syracuseStep 187421 = 70283) (by norm_num)
theorem B187445 : Blo 123787 187445 := bbase (se 5 (by rfl) ⟨8786, by rfl⟩ : syracuseStep 187445 = 17573) (by norm_num)
theorem B777269 : Blo 123787 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B285749 : Blo 123787 285749 := bbase (se 5 (by rfl) ⟨13394, by rfl⟩ : syracuseStep 285749 = 26789) (by norm_num)
theorem B187469 : Blo 123787 187469 := bbase (se 3 (by rfl) ⟨35150, by rfl⟩ : syracuseStep 187469 = 70301) (by norm_num)
theorem B187493 : Blo 123787 187493 := bbase (se 4 (by rfl) ⟨17577, by rfl⟩ : syracuseStep 187493 = 35155) (by norm_num)
theorem B187517 : Blo 123787 187517 := bbase (se 3 (by rfl) ⟨35159, by rfl⟩ : syracuseStep 187517 = 70319) (by norm_num)
theorem B285821 : Blo 123787 285821 := bbase (se 3 (by rfl) ⟨53591, by rfl⟩ : syracuseStep 285821 = 107183) (by norm_num)
theorem B187541 : Blo 123787 187541 := bbase (se 6 (by rfl) ⟨4395, by rfl⟩ : syracuseStep 187541 = 8791) (by norm_num)
theorem B318613 : Blo 123787 318613 := bbase (se 6 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 318613 = 14935) (by norm_num)
theorem B187565 : Blo 123787 187565 := bbase (se 3 (by rfl) ⟨35168, by rfl⟩ : syracuseStep 187565 = 70337) (by norm_num)
theorem B187589 : Blo 123787 187589 := bbase (se 4 (by rfl) ⟨17586, by rfl⟩ : syracuseStep 187589 = 35173) (by norm_num)
theorem B285893 : Blo 123787 285893 := bbase (se 4 (by rfl) ⟨26802, by rfl⟩ : syracuseStep 285893 = 53605) (by norm_num)
theorem B515285 : Blo 123787 515285 := bbase (se 7 (by rfl) ⟨6038, by rfl⟩ : syracuseStep 515285 = 12077) (by norm_num)
theorem B187613 : Blo 123787 187613 := bbase (se 3 (by rfl) ⟨35177, by rfl⟩ : syracuseStep 187613 = 70355) (by norm_num)
theorem B187637 : Blo 123787 187637 := bbase (se 5 (by rfl) ⟨8795, by rfl⟩ : syracuseStep 187637 = 17591) (by norm_num)
theorem B318725 : Blo 123787 318725 := bbase (se 4 (by rfl) ⟨29880, by rfl⟩ : syracuseStep 318725 = 59761) (by norm_num)
theorem B187661 : Blo 123787 187661 := bbase (se 3 (by rfl) ⟨35186, by rfl⟩ : syracuseStep 187661 = 70373) (by norm_num)
theorem B285965 : Blo 123787 285965 := bbase (se 3 (by rfl) ⟨53618, by rfl⟩ : syracuseStep 285965 = 107237) (by norm_num)
theorem B187685 : Blo 123787 187685 := bbase (se 4 (by rfl) ⟨17595, by rfl⟩ : syracuseStep 187685 = 35191) (by norm_num)
theorem B187709 : Blo 123787 187709 := bbase (se 3 (by rfl) ⟨35195, by rfl⟩ : syracuseStep 187709 = 70391) (by norm_num)
theorem B187733 : Blo 123787 187733 := bbase (se 11 (by rfl) ⟨137, by rfl⟩ : syracuseStep 187733 = 275) (by norm_num)
theorem B286037 : Blo 123787 286037 := bbase (se 11 (by rfl) ⟨209, by rfl⟩ : syracuseStep 286037 = 419) (by norm_num)
theorem B187757 : Blo 123787 187757 := bbase (se 3 (by rfl) ⟨35204, by rfl⟩ : syracuseStep 187757 = 70409) (by norm_num)
theorem B187781 : Blo 123787 187781 := bbase (se 4 (by rfl) ⟨17604, by rfl⟩ : syracuseStep 187781 = 35209) (by norm_num)
theorem B187805 : Blo 123787 187805 := bbase (se 3 (by rfl) ⟨35213, by rfl⟩ : syracuseStep 187805 = 70427) (by norm_num)
theorem B286109 : Blo 123787 286109 := bbase (se 3 (by rfl) ⟨53645, by rfl⟩ : syracuseStep 286109 = 107291) (by norm_num)
theorem B187829 : Blo 123787 187829 := bbase (se 5 (by rfl) ⟨8804, by rfl⟩ : syracuseStep 187829 = 17609) (by norm_num)
theorem B318917 : Blo 123787 318917 := bbase (se 4 (by rfl) ⟨29898, by rfl⟩ : syracuseStep 318917 = 59797) (by norm_num)
theorem B187853 : Blo 123787 187853 := bbase (se 3 (by rfl) ⟨35222, by rfl⟩ : syracuseStep 187853 = 70445) (by norm_num)
theorem B187877 : Blo 123787 187877 := bbase (se 4 (by rfl) ⟨17613, by rfl⟩ : syracuseStep 187877 = 35227) (by norm_num)
theorem B286181 : Blo 123787 286181 := bbase (se 4 (by rfl) ⟨26829, by rfl⟩ : syracuseStep 286181 = 53659) (by norm_num)
theorem B187901 : Blo 123787 187901 := bbase (se 3 (by rfl) ⟨35231, by rfl⟩ : syracuseStep 187901 = 70463) (by norm_num)
theorem B253453 : Blo 123787 253453 := bbase (se 3 (by rfl) ⟨47522, by rfl⟩ : syracuseStep 253453 = 95045) (by norm_num)
theorem B187925 : Blo 123787 187925 := bbase (se 6 (by rfl) ⟨4404, by rfl⟩ : syracuseStep 187925 = 8809) (by norm_num)
theorem B253477 : Blo 123787 253477 := bbase (se 4 (by rfl) ⟨23763, by rfl⟩ : syracuseStep 253477 = 47527) (by norm_num)
theorem B187949 : Blo 123787 187949 := bbase (se 3 (by rfl) ⟨35240, by rfl⟩ : syracuseStep 187949 = 70481) (by norm_num)
theorem B286253 : Blo 123787 286253 := bbase (se 3 (by rfl) ⟨53672, by rfl⟩ : syracuseStep 286253 = 107345) (by norm_num)
theorem B187973 : Blo 123787 187973 := bbase (se 4 (by rfl) ⟨17622, by rfl⟩ : syracuseStep 187973 = 35245) (by norm_num)
theorem B253525 : Blo 123787 253525 := bbase (se 8 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 253525 = 2971) (by norm_num)
theorem B187997 : Blo 123787 187997 := bbase (se 3 (by rfl) ⟨35249, by rfl⟩ : syracuseStep 187997 = 70499) (by norm_num)
theorem B188021 : Blo 123787 188021 := bbase (se 5 (by rfl) ⟨8813, by rfl⟩ : syracuseStep 188021 = 17627) (by norm_num)
theorem B286325 : Blo 123787 286325 := bbase (se 5 (by rfl) ⟨13421, by rfl⟩ : syracuseStep 286325 = 26843) (by norm_num)
theorem B188045 : Blo 123787 188045 := bbase (se 3 (by rfl) ⟨35258, by rfl⟩ : syracuseStep 188045 = 70517) (by norm_num)
theorem B188069 : Blo 123787 188069 := bbase (se 4 (by rfl) ⟨17631, by rfl⟩ : syracuseStep 188069 = 35263) (by norm_num)
theorem B188093 : Blo 123787 188093 := bbase (se 3 (by rfl) ⟨35267, by rfl⟩ : syracuseStep 188093 = 70535) (by norm_num)
theorem B286397 : Blo 123787 286397 := bbase (se 3 (by rfl) ⟨53699, by rfl⟩ : syracuseStep 286397 = 107399) (by norm_num)
theorem B188117 : Blo 123787 188117 := bbase (se 7 (by rfl) ⟨2204, by rfl⟩ : syracuseStep 188117 = 4409) (by norm_num)
theorem B188141 : Blo 123787 188141 := bbase (se 3 (by rfl) ⟨35276, by rfl⟩ : syracuseStep 188141 = 70553) (by norm_num)
theorem B188165 : Blo 123787 188165 := bbase (se 4 (by rfl) ⟨17640, by rfl⟩ : syracuseStep 188165 = 35281) (by norm_num)
theorem B286469 : Blo 123787 286469 := bbase (se 4 (by rfl) ⟨26856, by rfl⟩ : syracuseStep 286469 = 53713) (by norm_num)
theorem B581381 : Blo 123787 581381 := bbase (se 4 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 581381 = 109009) (by norm_num)
theorem B188189 : Blo 123787 188189 := bbase (se 3 (by rfl) ⟨35285, by rfl⟩ : syracuseStep 188189 = 70571) (by norm_num)
theorem B319261 : Blo 123787 319261 := bbase (se 3 (by rfl) ⟨59861, by rfl⟩ : syracuseStep 319261 = 119723) (by norm_num)
theorem B188213 : Blo 123787 188213 := bbase (se 5 (by rfl) ⟨8822, by rfl⟩ : syracuseStep 188213 = 17645) (by norm_num)
theorem B188237 : Blo 123787 188237 := bbase (se 3 (by rfl) ⟨35294, by rfl⟩ : syracuseStep 188237 = 70589) (by norm_num)
theorem B286541 : Blo 123787 286541 := bbase (se 3 (by rfl) ⟨53726, by rfl⟩ : syracuseStep 286541 = 107453) (by norm_num)
theorem B188261 : Blo 123787 188261 := bbase (se 4 (by rfl) ⟨17649, by rfl⟩ : syracuseStep 188261 = 35299) (by norm_num)
theorem B188285 : Blo 123787 188285 := bbase (se 3 (by rfl) ⟨35303, by rfl⟩ : syracuseStep 188285 = 70607) (by norm_num)
theorem B483205 : Blo 123787 483205 := bbase (se 4 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 483205 = 90601) (by norm_num)
theorem B319373 : Blo 123787 319373 := bbase (se 3 (by rfl) ⟨59882, by rfl⟩ : syracuseStep 319373 = 119765) (by norm_num)
theorem B712597 : Blo 123787 712597 := bbase (se 6 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 712597 = 33403) (by norm_num)
theorem B188309 : Blo 123787 188309 := bbase (se 6 (by rfl) ⟨4413, by rfl⟩ : syracuseStep 188309 = 8827) (by norm_num)
theorem B286613 : Blo 123787 286613 := bbase (se 6 (by rfl) ⟨6717, by rfl⟩ : syracuseStep 286613 = 13435) (by norm_num)
theorem B581525 : Blo 123787 581525 := bbase (se 6 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 581525 = 27259) (by norm_num)
theorem B286621 : Blo 123787 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B188333 : Blo 123787 188333 := bbase (se 3 (by rfl) ⟨35312, by rfl⟩ : syracuseStep 188333 = 70625) (by norm_num)
theorem B188357 : Blo 123787 188357 := bbase (se 4 (by rfl) ⟨17658, by rfl⟩ : syracuseStep 188357 = 35317) (by norm_num)
theorem B188381 : Blo 123787 188381 := bbase (se 3 (by rfl) ⟨35321, by rfl⟩ : syracuseStep 188381 = 70643) (by norm_num)
theorem B286685 : Blo 123787 286685 := bbase (se 3 (by rfl) ⟨53753, by rfl⟩ : syracuseStep 286685 = 107507) (by norm_num)
theorem B188405 : Blo 123787 188405 := bbase (se 5 (by rfl) ⟨8831, by rfl⟩ : syracuseStep 188405 = 17663) (by norm_num)
theorem B417797 : Blo 123787 417797 := bbase (se 4 (by rfl) ⟨39168, by rfl⟩ : syracuseStep 417797 = 78337) (by norm_num)
theorem B188429 : Blo 123787 188429 := bbase (se 3 (by rfl) ⟨35330, by rfl⟩ : syracuseStep 188429 = 70661) (by norm_num)
theorem B188453 : Blo 123787 188453 := bbase (se 4 (by rfl) ⟨17667, by rfl⟩ : syracuseStep 188453 = 35335) (by norm_num)
theorem B286757 : Blo 123787 286757 := bbase (se 4 (by rfl) ⟨26883, by rfl⟩ : syracuseStep 286757 = 53767) (by norm_num)
theorem B188477 : Blo 123787 188477 := bbase (se 3 (by rfl) ⟨35339, by rfl⟩ : syracuseStep 188477 = 70679) (by norm_num)
theorem B319565 : Blo 123787 319565 := bbase (se 3 (by rfl) ⟨59918, by rfl⟩ : syracuseStep 319565 = 119837) (by norm_num)
theorem B188501 : Blo 123787 188501 := bbase (se 8 (by rfl) ⟨1104, by rfl⟩ : syracuseStep 188501 = 2209) (by norm_num)
theorem B188525 : Blo 123787 188525 := bbase (se 3 (by rfl) ⟨35348, by rfl⟩ : syracuseStep 188525 = 70697) (by norm_num)
theorem B286829 : Blo 123787 286829 := bbase (se 3 (by rfl) ⟨53780, by rfl⟩ : syracuseStep 286829 = 107561) (by norm_num)
theorem B188549 : Blo 123787 188549 := bbase (se 4 (by rfl) ⟨17676, by rfl⟩ : syracuseStep 188549 = 35353) (by norm_num)
theorem B188573 : Blo 123787 188573 := bbase (se 3 (by rfl) ⟨35357, by rfl⟩ : syracuseStep 188573 = 70715) (by norm_num)
theorem B188597 : Blo 123787 188597 := bbase (se 5 (by rfl) ⟨8840, by rfl⟩ : syracuseStep 188597 = 17681) (by norm_num)
theorem B483509 : Blo 123787 483509 := bbase (se 5 (by rfl) ⟨22664, by rfl⟩ : syracuseStep 483509 = 45329) (by norm_num)
theorem B286901 : Blo 123787 286901 := bbase (se 5 (by rfl) ⟨13448, by rfl⟩ : syracuseStep 286901 = 26897) (by norm_num)
theorem B188621 : Blo 123787 188621 := bbase (se 3 (by rfl) ⟨35366, by rfl⟩ : syracuseStep 188621 = 70733) (by norm_num)
theorem B188645 : Blo 123787 188645 := bbase (se 4 (by rfl) ⟨17685, by rfl⟩ : syracuseStep 188645 = 35371) (by norm_num)
theorem B188669 : Blo 123787 188669 := bbase (se 3 (by rfl) ⟨35375, by rfl⟩ : syracuseStep 188669 = 70751) (by norm_num)
theorem B286973 : Blo 123787 286973 := bbase (se 3 (by rfl) ⟨53807, by rfl⟩ : syracuseStep 286973 = 107615) (by norm_num)
theorem B188693 : Blo 123787 188693 := bbase (se 6 (by rfl) ⟨4422, by rfl⟩ : syracuseStep 188693 = 8845) (by norm_num)
theorem B188717 : Blo 123787 188717 := bbase (se 3 (by rfl) ⟨35384, by rfl⟩ : syracuseStep 188717 = 70769) (by norm_num)
theorem B188741 : Blo 123787 188741 := bbase (se 4 (by rfl) ⟨17694, by rfl⟩ : syracuseStep 188741 = 35389) (by norm_num)
theorem B287045 : Blo 123787 287045 := bbase (se 4 (by rfl) ⟨26910, by rfl⟩ : syracuseStep 287045 = 53821) (by norm_num)
theorem B188765 : Blo 123787 188765 := bbase (se 3 (by rfl) ⟨35393, by rfl⟩ : syracuseStep 188765 = 70787) (by norm_num)
theorem B188789 : Blo 123787 188789 := bbase (se 5 (by rfl) ⟨8849, by rfl⟩ : syracuseStep 188789 = 17699) (by norm_num)
theorem B188813 : Blo 123787 188813 := bbase (se 3 (by rfl) ⟨35402, by rfl⟩ : syracuseStep 188813 = 70805) (by norm_num)
theorem B287117 : Blo 123787 287117 := bbase (se 3 (by rfl) ⟨53834, by rfl⟩ : syracuseStep 287117 = 107669) (by norm_num)
theorem B188837 : Blo 123787 188837 := bbase (se 4 (by rfl) ⟨17703, by rfl⟩ : syracuseStep 188837 = 35407) (by norm_num)
theorem B319909 : Blo 123787 319909 := bbase (se 4 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 319909 = 59983) (by norm_num)
theorem B418229 : Blo 123787 418229 := bbase (se 5 (by rfl) ⟨19604, by rfl⟩ : syracuseStep 418229 = 39209) (by norm_num)
theorem B188861 : Blo 123787 188861 := bbase (se 3 (by rfl) ⟨35411, by rfl⟩ : syracuseStep 188861 = 70823) (by norm_num)
theorem B188885 : Blo 123787 188885 := bbase (se 7 (by rfl) ⟨2213, by rfl⟩ : syracuseStep 188885 = 4427) (by norm_num)
theorem B287189 : Blo 123787 287189 := bbase (se 7 (by rfl) ⟨3365, by rfl⟩ : syracuseStep 287189 = 6731) (by norm_num)
theorem B188909 : Blo 123787 188909 := bbase (se 3 (by rfl) ⟨35420, by rfl⟩ : syracuseStep 188909 = 70841) (by norm_num)
theorem B188933 : Blo 123787 188933 := bbase (se 4 (by rfl) ⟨17712, by rfl⟩ : syracuseStep 188933 = 35425) (by norm_num)
theorem B320021 : Blo 123787 320021 := bbase (se 6 (by rfl) ⟨7500, by rfl⟩ : syracuseStep 320021 = 15001) (by norm_num)
theorem B188957 : Blo 123787 188957 := bbase (se 3 (by rfl) ⟨35429, by rfl⟩ : syracuseStep 188957 = 70859) (by norm_num)
theorem B287261 : Blo 123787 287261 := bbase (se 3 (by rfl) ⟨53861, by rfl⟩ : syracuseStep 287261 = 107723) (by norm_num)
theorem B483893 : Blo 123787 483893 := bbase (se 5 (by rfl) ⟨22682, by rfl⟩ : syracuseStep 483893 = 45365) (by norm_num)
theorem B188981 : Blo 123787 188981 := bbase (se 5 (by rfl) ⟨8858, by rfl⟩ : syracuseStep 188981 = 17717) (by norm_num)
theorem B189005 : Blo 123787 189005 := bbase (se 3 (by rfl) ⟨35438, by rfl⟩ : syracuseStep 189005 = 70877) (by norm_num)
theorem B189029 : Blo 123787 189029 := bbase (se 4 (by rfl) ⟨17721, by rfl⟩ : syracuseStep 189029 = 35443) (by norm_num)
theorem B287333 : Blo 123787 287333 := bbase (se 4 (by rfl) ⟨26937, by rfl⟩ : syracuseStep 287333 = 53875) (by norm_num)
theorem B189053 : Blo 123787 189053 := bbase (se 3 (by rfl) ⟨35447, by rfl⟩ : syracuseStep 189053 = 70895) (by norm_num)
theorem B189077 : Blo 123787 189077 := bbase (se 6 (by rfl) ⟨4431, by rfl⟩ : syracuseStep 189077 = 8863) (by norm_num)
theorem B189101 : Blo 123787 189101 := bbase (se 3 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 189101 = 70913) (by norm_num)
theorem B287405 : Blo 123787 287405 := bbase (se 3 (by rfl) ⟨53888, by rfl⟩ : syracuseStep 287405 = 107777) (by norm_num)
theorem B189125 : Blo 123787 189125 := bbase (se 4 (by rfl) ⟨17730, by rfl⟩ : syracuseStep 189125 = 35461) (by norm_num)
theorem B320213 : Blo 123787 320213 := bbase (se 7 (by rfl) ⟨3752, by rfl⟩ : syracuseStep 320213 = 7505) (by norm_num)
theorem B189149 : Blo 123787 189149 := bbase (se 3 (by rfl) ⟨35465, by rfl⟩ : syracuseStep 189149 = 70931) (by norm_num)
theorem B254693 : Blo 123787 254693 := bbase (se 4 (by rfl) ⟨23877, by rfl⟩ : syracuseStep 254693 = 47755) (by norm_num)
theorem B189173 : Blo 123787 189173 := bbase (se 5 (by rfl) ⟨8867, by rfl⟩ : syracuseStep 189173 = 17735) (by norm_num)
theorem B287477 : Blo 123787 287477 := bbase (se 5 (by rfl) ⟨13475, by rfl⟩ : syracuseStep 287477 = 26951) (by norm_num)
theorem B189197 : Blo 123787 189197 := bbase (se 3 (by rfl) ⟨35474, by rfl⟩ : syracuseStep 189197 = 70949) (by norm_num)
theorem B189221 : Blo 123787 189221 := bbase (se 4 (by rfl) ⟨17739, by rfl⟩ : syracuseStep 189221 = 35479) (by norm_num)
theorem B189245 : Blo 123787 189245 := bbase (se 3 (by rfl) ⟨35483, by rfl⟩ : syracuseStep 189245 = 70967) (by norm_num)
theorem B189269 : Blo 123787 189269 := bbase (se 9 (by rfl) ⟨554, by rfl⟩ : syracuseStep 189269 = 1109) (by norm_num)
theorem B418661 : Blo 123787 418661 := bbase (se 4 (by rfl) ⟨39249, by rfl⟩ : syracuseStep 418661 = 78499) (by norm_num)
theorem B615269 : Blo 123787 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B189293 : Blo 123787 189293 := bbase (se 3 (by rfl) ⟨35492, by rfl⟩ : syracuseStep 189293 = 70985) (by norm_num)
theorem B189317 : Blo 123787 189317 := bbase (se 4 (by rfl) ⟨17748, by rfl⟩ : syracuseStep 189317 = 35497) (by norm_num)
theorem B189341 : Blo 123787 189341 := bbase (se 3 (by rfl) ⟨35501, by rfl⟩ : syracuseStep 189341 = 71003) (by norm_num)
theorem B189365 : Blo 123787 189365 := bbase (se 5 (by rfl) ⟨8876, by rfl⟩ : syracuseStep 189365 = 17753) (by norm_num)
theorem B189389 : Blo 123787 189389 := bbase (se 3 (by rfl) ⟨35510, by rfl⟩ : syracuseStep 189389 = 71021) (by norm_num)
theorem B1139669 : Blo 123787 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B189413 : Blo 123787 189413 := bbase (se 4 (by rfl) ⟨17757, by rfl⟩ : syracuseStep 189413 = 35515) (by norm_num)
theorem B189437 : Blo 123787 189437 := bbase (se 3 (by rfl) ⟨35519, by rfl⟩ : syracuseStep 189437 = 71039) (by norm_num)
theorem B189461 : Blo 123787 189461 := bbase (se 6 (by rfl) ⟨4440, by rfl⟩ : syracuseStep 189461 = 8881) (by norm_num)
theorem B189485 : Blo 123787 189485 := bbase (se 3 (by rfl) ⟨35528, by rfl⟩ : syracuseStep 189485 = 71057) (by norm_num)
theorem B320557 : Blo 123787 320557 := bbase (se 3 (by rfl) ⟨60104, by rfl⟩ : syracuseStep 320557 = 120209) (by norm_num)
theorem B189509 : Blo 123787 189509 := bbase (se 4 (by rfl) ⟨17766, by rfl⟩ : syracuseStep 189509 = 35533) (by norm_num)
theorem B156745 : Blo 123787 156745 := bbase (se 2 (by rfl) ⟨58779, by rfl⟩ : syracuseStep 156745 = 117559) (by norm_num)
theorem B287837 : Blo 123787 287837 := bbase (se 3 (by rfl) ⟨53969, by rfl⟩ : syracuseStep 287837 = 107939) (by norm_num)
theorem B189533 : Blo 123787 189533 := bbase (se 3 (by rfl) ⟨35537, by rfl⟩ : syracuseStep 189533 = 71075) (by norm_num)
theorem B189557 : Blo 123787 189557 := bbase (se 5 (by rfl) ⟨8885, by rfl⟩ : syracuseStep 189557 = 17771) (by norm_num)
theorem B189581 : Blo 123787 189581 := bbase (se 3 (by rfl) ⟨35546, by rfl⟩ : syracuseStep 189581 = 71093) (by norm_num)
theorem B353429 : Blo 123787 353429 := bbase (se 6 (by rfl) ⟨8283, by rfl⟩ : syracuseStep 353429 = 16567) (by norm_num)
theorem B320669 : Blo 123787 320669 := bbase (se 3 (by rfl) ⟨60125, by rfl⟩ : syracuseStep 320669 = 120251) (by norm_num)
theorem B189605 : Blo 123787 189605 := bbase (se 4 (by rfl) ⟨17775, by rfl⟩ : syracuseStep 189605 = 35551) (by norm_num)
theorem B189629 : Blo 123787 189629 := bbase (se 3 (by rfl) ⟨35555, by rfl⟩ : syracuseStep 189629 = 71111) (by norm_num)
theorem B189653 : Blo 123787 189653 := bbase (se 7 (by rfl) ⟨2222, by rfl⟩ : syracuseStep 189653 = 4445) (by norm_num)
theorem B189677 : Blo 123787 189677 := bbase (se 3 (by rfl) ⟨35564, by rfl⟩ : syracuseStep 189677 = 71129) (by norm_num)
theorem B156917 : Blo 123787 156917 := bbase (se 5 (by rfl) ⟨7355, by rfl⟩ : syracuseStep 156917 = 14711) (by norm_num)
theorem B189701 : Blo 123787 189701 := bbase (se 4 (by rfl) ⟨17784, by rfl⟩ : syracuseStep 189701 = 35569) (by norm_num)
theorem B419093 : Blo 123787 419093 := bbase (se 6 (by rfl) ⟨9822, by rfl⟩ : syracuseStep 419093 = 19645) (by norm_num)
theorem B189725 : Blo 123787 189725 := bbase (se 3 (by rfl) ⟨35573, by rfl⟩ : syracuseStep 189725 = 71147) (by norm_num)
theorem B156973 : Blo 123787 156973 := bbase (se 3 (by rfl) ⟨29432, by rfl⟩ : syracuseStep 156973 = 58865) (by norm_num)
theorem B189749 : Blo 123787 189749 := bbase (se 5 (by rfl) ⟨8894, by rfl⟩ : syracuseStep 189749 = 17789) (by norm_num)
theorem B517429 : Blo 123787 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B255293 : Blo 123787 255293 := bbase (se 3 (by rfl) ⟨47867, by rfl⟩ : syracuseStep 255293 = 95735) (by norm_num)
theorem B189773 : Blo 123787 189773 := bbase (se 3 (by rfl) ⟨35582, by rfl⟩ : syracuseStep 189773 = 71165) (by norm_num)
theorem B451925 : Blo 123787 451925 := bbase (se 12 (by rfl) ⟨165, by rfl⟩ : syracuseStep 451925 = 331) (by norm_num)
theorem B3106133 : Blo 123787 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B320861 : Blo 123787 320861 := bbase (se 3 (by rfl) ⟨60161, by rfl⟩ : syracuseStep 320861 = 120323) (by norm_num)
theorem B189797 : Blo 123787 189797 := bbase (se 4 (by rfl) ⟨17793, by rfl⟩ : syracuseStep 189797 = 35587) (by norm_num)
theorem B189821 : Blo 123787 189821 := bbase (se 3 (by rfl) ⟨35591, by rfl⟩ : syracuseStep 189821 = 71183) (by norm_num)
theorem B157069 : Blo 123787 157069 := bbase (se 3 (by rfl) ⟨29450, by rfl⟩ : syracuseStep 157069 = 58901) (by norm_num)
theorem B189845 : Blo 123787 189845 := bbase (se 6 (by rfl) ⟨4449, by rfl⟩ : syracuseStep 189845 = 8899) (by norm_num)
theorem B189869 : Blo 123787 189869 := bbase (se 3 (by rfl) ⟨35600, by rfl⟩ : syracuseStep 189869 = 71201) (by norm_num)
theorem B189893 : Blo 123787 189893 := bbase (se 4 (by rfl) ⟨17802, by rfl⟩ : syracuseStep 189893 = 35605) (by norm_num)
theorem B189917 : Blo 123787 189917 := bbase (se 3 (by rfl) ⟨35609, by rfl⟩ : syracuseStep 189917 = 71219) (by norm_num)
theorem B976373 : Blo 123787 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B189941 : Blo 123787 189941 := bbase (se 5 (by rfl) ⟨8903, by rfl⟩ : syracuseStep 189941 = 17807) (by norm_num)
theorem B189965 : Blo 123787 189965 := bbase (se 3 (by rfl) ⟨35618, by rfl⟩ : syracuseStep 189965 = 71237) (by norm_num)
theorem B189989 : Blo 123787 189989 := bbase (se 4 (by rfl) ⟨17811, by rfl⟩ : syracuseStep 189989 = 35623) (by norm_num)
theorem B157241 : Blo 123787 157241 := bbase (se 2 (by rfl) ⟨58965, by rfl⟩ : syracuseStep 157241 = 117931) (by norm_num)
theorem B190013 : Blo 123787 190013 := bbase (se 3 (by rfl) ⟨35627, by rfl⟩ : syracuseStep 190013 = 71255) (by norm_num)
theorem B190037 : Blo 123787 190037 := bbase (se 8 (by rfl) ⟨1113, by rfl⟩ : syracuseStep 190037 = 2227) (by norm_num)
theorem B190061 : Blo 123787 190061 := bbase (se 3 (by rfl) ⟨35636, by rfl⟩ : syracuseStep 190061 = 71273) (by norm_num)
theorem B157297 : Blo 123787 157297 := bbase (se 2 (by rfl) ⟨58986, by rfl⟩ : syracuseStep 157297 = 117973) (by norm_num)
theorem B190085 : Blo 123787 190085 := bbase (se 4 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 190085 = 35641) (by norm_num)
theorem B190109 : Blo 123787 190109 := bbase (se 3 (by rfl) ⟨35645, by rfl⟩ : syracuseStep 190109 = 71291) (by norm_num)
theorem B190133 : Blo 123787 190133 := bbase (se 5 (by rfl) ⟨8912, by rfl⟩ : syracuseStep 190133 = 17825) (by norm_num)
theorem B321205 : Blo 123787 321205 := bbase (se 5 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 321205 = 30113) (by norm_num)
theorem B419525 : Blo 123787 419525 := bbase (se 4 (by rfl) ⟨39330, by rfl⟩ : syracuseStep 419525 = 78661) (by norm_num)
theorem B190157 : Blo 123787 190157 := bbase (se 3 (by rfl) ⟨35654, by rfl⟩ : syracuseStep 190157 = 71309) (by norm_num)
theorem B157393 : Blo 123787 157393 := bbase (se 2 (by rfl) ⟨59022, by rfl⟩ : syracuseStep 157393 = 118045) (by norm_num)
theorem B190181 : Blo 123787 190181 := bbase (se 4 (by rfl) ⟨17829, by rfl⟩ : syracuseStep 190181 = 35659) (by norm_num)
theorem B190205 : Blo 123787 190205 := bbase (se 3 (by rfl) ⟨35663, by rfl⟩ : syracuseStep 190205 = 71327) (by norm_num)
theorem B190229 : Blo 123787 190229 := bbase (se 6 (by rfl) ⟨4458, by rfl⟩ : syracuseStep 190229 = 8917) (by norm_num)
theorem B321317 : Blo 123787 321317 := bbase (se 4 (by rfl) ⟨30123, by rfl⟩ : syracuseStep 321317 = 60247) (by norm_num)
theorem B190253 : Blo 123787 190253 := bbase (se 3 (by rfl) ⟨35672, by rfl⟩ : syracuseStep 190253 = 71345) (by norm_num)
theorem B190277 : Blo 123787 190277 := bbase (se 4 (by rfl) ⟨17838, by rfl⟩ : syracuseStep 190277 = 35677) (by norm_num)
theorem B714581 : Blo 123787 714581 := bbase (se 9 (by rfl) ⟨2093, by rfl⟩ : syracuseStep 714581 = 4187) (by norm_num)
theorem B190301 : Blo 123787 190301 := bbase (se 3 (by rfl) ⟨35681, by rfl⟩ : syracuseStep 190301 = 71363) (by norm_num)
theorem B190325 : Blo 123787 190325 := bbase (se 5 (by rfl) ⟨8921, by rfl⟩ : syracuseStep 190325 = 17843) (by norm_num)
theorem B157565 : Blo 123787 157565 := bbase (se 3 (by rfl) ⟨29543, by rfl⟩ : syracuseStep 157565 = 59087) (by norm_num)
theorem B157573 : Blo 123787 157573 := bbase (se 4 (by rfl) ⟨14772, by rfl⟩ : syracuseStep 157573 = 29545) (by norm_num)
theorem B190349 : Blo 123787 190349 := bbase (se 3 (by rfl) ⟨35690, by rfl⟩ : syracuseStep 190349 = 71381) (by norm_num)
theorem B190373 : Blo 123787 190373 := bbase (se 4 (by rfl) ⟨17847, by rfl⟩ : syracuseStep 190373 = 35695) (by norm_num)
theorem B157621 : Blo 123787 157621 := bbase (se 5 (by rfl) ⟨7388, by rfl⟩ : syracuseStep 157621 = 14777) (by norm_num)
theorem B190397 : Blo 123787 190397 := bbase (se 3 (by rfl) ⟨35699, by rfl⟩ : syracuseStep 190397 = 71399) (by norm_num)
theorem B190421 : Blo 123787 190421 := bbase (se 7 (by rfl) ⟨2231, by rfl⟩ : syracuseStep 190421 = 4463) (by norm_num)
theorem B321509 : Blo 123787 321509 := bbase (se 4 (by rfl) ⟨30141, by rfl⟩ : syracuseStep 321509 = 60283) (by norm_num)
theorem B190445 : Blo 123787 190445 := bbase (se 3 (by rfl) ⟨35708, by rfl⟩ : syracuseStep 190445 = 71417) (by norm_num)
theorem B190469 : Blo 123787 190469 := bbase (se 4 (by rfl) ⟨17856, by rfl⟩ : syracuseStep 190469 = 35713) (by norm_num)
theorem B157717 : Blo 123787 157717 := bbase (se 6 (by rfl) ⟨3696, by rfl⟩ : syracuseStep 157717 = 7393) (by norm_num)
theorem B190493 : Blo 123787 190493 := bbase (se 3 (by rfl) ⟨35717, by rfl⟩ : syracuseStep 190493 = 71435) (by norm_num)
theorem B190517 : Blo 123787 190517 := bbase (se 5 (by rfl) ⟨8930, by rfl⟩ : syracuseStep 190517 = 17861) (by norm_num)
theorem B190541 : Blo 123787 190541 := bbase (se 3 (by rfl) ⟨35726, by rfl⟩ : syracuseStep 190541 = 71453) (by norm_num)
theorem B190565 : Blo 123787 190565 := bbase (se 4 (by rfl) ⟨17865, by rfl⟩ : syracuseStep 190565 = 35731) (by norm_num)
theorem B419957 : Blo 123787 419957 := bbase (se 5 (by rfl) ⟨19685, by rfl⟩ : syracuseStep 419957 = 39371) (by norm_num)
theorem B190589 : Blo 123787 190589 := bbase (se 3 (by rfl) ⟨35735, by rfl⟩ : syracuseStep 190589 = 71471) (by norm_num)
theorem B190613 : Blo 123787 190613 := bbase (se 6 (by rfl) ⟨4467, by rfl⟩ : syracuseStep 190613 = 8935) (by norm_num)
theorem B190637 : Blo 123787 190637 := bbase (se 3 (by rfl) ⟨35744, by rfl⟩ : syracuseStep 190637 = 71489) (by norm_num)
theorem B157889 : Blo 123787 157889 := bbase (se 2 (by rfl) ⟨59208, by rfl⟩ : syracuseStep 157889 = 118417) (by norm_num)
theorem B190661 : Blo 123787 190661 := bbase (se 4 (by rfl) ⟨17874, by rfl⟩ : syracuseStep 190661 = 35749) (by norm_num)
theorem B190685 : Blo 123787 190685 := bbase (se 3 (by rfl) ⟨35753, by rfl⟩ : syracuseStep 190685 = 71507) (by norm_num)
theorem B190709 : Blo 123787 190709 := bbase (se 5 (by rfl) ⟨8939, by rfl⟩ : syracuseStep 190709 = 17879) (by norm_num)
theorem B157945 : Blo 123787 157945 := bbase (se 2 (by rfl) ⟨59229, by rfl⟩ : syracuseStep 157945 = 118459) (by norm_num)
theorem B190733 : Blo 123787 190733 := bbase (se 3 (by rfl) ⟨35762, by rfl⟩ : syracuseStep 190733 = 71525) (by norm_num)
theorem B190757 : Blo 123787 190757 := bbase (se 4 (by rfl) ⟨17883, by rfl⟩ : syracuseStep 190757 = 35767) (by norm_num)
theorem B354613 : Blo 123787 354613 := bbase (se 5 (by rfl) ⟨16622, by rfl⟩ : syracuseStep 354613 = 33245) (by norm_num)
theorem B321853 : Blo 123787 321853 := bbase (se 3 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 321853 = 120695) (by norm_num)
theorem B190781 : Blo 123787 190781 := bbase (se 3 (by rfl) ⟨35771, by rfl⟩ : syracuseStep 190781 = 71543) (by norm_num)
theorem B190805 : Blo 123787 190805 := bbase (se 10 (by rfl) ⟨279, by rfl⟩ : syracuseStep 190805 = 559) (by norm_num)
theorem B158041 : Blo 123787 158041 := bbase (se 2 (by rfl) ⟨59265, by rfl⟩ : syracuseStep 158041 = 118531) (by norm_num)
theorem B190829 : Blo 123787 190829 := bbase (se 3 (by rfl) ⟨35780, by rfl⟩ : syracuseStep 190829 = 71561) (by norm_num)
theorem B190853 : Blo 123787 190853 := bbase (se 4 (by rfl) ⟨17892, by rfl⟩ : syracuseStep 190853 = 35785) (by norm_num)
theorem B190877 : Blo 123787 190877 := bbase (se 3 (by rfl) ⟨35789, by rfl⟩ : syracuseStep 190877 = 71579) (by norm_num)
theorem B321965 : Blo 123787 321965 := bbase (se 3 (by rfl) ⟨60368, by rfl⟩ : syracuseStep 321965 = 120737) (by norm_num)
theorem B190901 : Blo 123787 190901 := bbase (se 5 (by rfl) ⟨8948, by rfl⟩ : syracuseStep 190901 = 17897) (by norm_num)
theorem B190925 : Blo 123787 190925 := bbase (se 3 (by rfl) ⟨35798, by rfl⟩ : syracuseStep 190925 = 71597) (by norm_num)
theorem B354773 : Blo 123787 354773 := bbase (se 7 (by rfl) ⟨4157, by rfl⟩ : syracuseStep 354773 = 8315) (by norm_num)
theorem B190949 : Blo 123787 190949 := bbase (se 4 (by rfl) ⟨17901, by rfl⟩ : syracuseStep 190949 = 35803) (by norm_num)
theorem B190973 : Blo 123787 190973 := bbase (se 3 (by rfl) ⟨35807, by rfl⟩ : syracuseStep 190973 = 71615) (by norm_num)
theorem B158213 : Blo 123787 158213 := bbase (se 4 (by rfl) ⟨14832, by rfl⟩ : syracuseStep 158213 = 29665) (by norm_num)
theorem B190997 : Blo 123787 190997 := bbase (se 6 (by rfl) ⟨4476, by rfl⟩ : syracuseStep 190997 = 8953) (by norm_num)
theorem B420389 : Blo 123787 420389 := bbase (se 4 (by rfl) ⟨39411, by rfl⟩ : syracuseStep 420389 = 78823) (by norm_num)
theorem B191021 : Blo 123787 191021 := bbase (se 3 (by rfl) ⟨35816, by rfl⟩ : syracuseStep 191021 = 71633) (by norm_num)
theorem B158269 : Blo 123787 158269 := bbase (se 3 (by rfl) ⟨29675, by rfl⟩ : syracuseStep 158269 = 59351) (by norm_num)
theorem B191045 : Blo 123787 191045 := bbase (se 4 (by rfl) ⟨17910, by rfl⟩ : syracuseStep 191045 = 35821) (by norm_num)
theorem B191069 : Blo 123787 191069 := bbase (se 3 (by rfl) ⟨35825, by rfl⟩ : syracuseStep 191069 = 71651) (by norm_num)
theorem B322157 : Blo 123787 322157 := bbase (se 3 (by rfl) ⟨60404, by rfl⟩ : syracuseStep 322157 = 120809) (by norm_num)
theorem B191093 : Blo 123787 191093 := bbase (se 5 (by rfl) ⟨8957, by rfl⟩ : syracuseStep 191093 = 17915) (by norm_num)
theorem B191117 : Blo 123787 191117 := bbase (se 3 (by rfl) ⟨35834, by rfl⟩ : syracuseStep 191117 = 71669) (by norm_num)
theorem B158365 : Blo 123787 158365 := bbase (se 3 (by rfl) ⟨29693, by rfl⟩ : syracuseStep 158365 = 59387) (by norm_num)
theorem B191141 : Blo 123787 191141 := bbase (se 4 (by rfl) ⟨17919, by rfl⟩ : syracuseStep 191141 = 35839) (by norm_num)
theorem B191165 : Blo 123787 191165 := bbase (se 3 (by rfl) ⟨35843, by rfl⟩ : syracuseStep 191165 = 71687) (by norm_num)
theorem B355013 : Blo 123787 355013 := bbase (se 4 (by rfl) ⟨33282, by rfl⟩ : syracuseStep 355013 = 66565) (by norm_num)
theorem B191189 : Blo 123787 191189 := bbase (se 7 (by rfl) ⟨2240, by rfl⟩ : syracuseStep 191189 = 4481) (by norm_num)
theorem B125669 : Blo 123787 125669 := bbase (se 4 (by rfl) ⟨11781, by rfl⟩ : syracuseStep 125669 = 23563) (by norm_num)
theorem B191213 : Blo 123787 191213 := bbase (se 3 (by rfl) ⟨35852, by rfl⟩ : syracuseStep 191213 = 71705) (by norm_num)
theorem B191237 : Blo 123787 191237 := bbase (se 4 (by rfl) ⟨17928, by rfl⟩ : syracuseStep 191237 = 35857) (by norm_num)
theorem B224029 : Blo 123787 224029 := bbase (se 3 (by rfl) ⟨42005, by rfl⟩ : syracuseStep 224029 = 84011) (by norm_num)
theorem B191261 : Blo 123787 191261 := bbase (se 3 (by rfl) ⟨35861, by rfl⟩ : syracuseStep 191261 = 71723) (by norm_num)
theorem B191285 : Blo 123787 191285 := bbase (se 5 (by rfl) ⟨8966, by rfl⟩ : syracuseStep 191285 = 17933) (by norm_num)
theorem B158537 : Blo 123787 158537 := bbase (se 2 (by rfl) ⟨59451, by rfl⟩ : syracuseStep 158537 = 118903) (by norm_num)
theorem B191309 : Blo 123787 191309 := bbase (se 3 (by rfl) ⟨35870, by rfl⟩ : syracuseStep 191309 = 71741) (by norm_num)
theorem B191333 : Blo 123787 191333 := bbase (se 4 (by rfl) ⟨17937, by rfl⟩ : syracuseStep 191333 = 35875) (by norm_num)
theorem B224117 : Blo 123787 224117 := bbase (se 5 (by rfl) ⟨10505, by rfl⟩ : syracuseStep 224117 = 21011) (by norm_num)
theorem B191357 : Blo 123787 191357 := bbase (se 3 (by rfl) ⟨35879, by rfl⟩ : syracuseStep 191357 = 71759) (by norm_num)
theorem B158593 : Blo 123787 158593 := bbase (se 2 (by rfl) ⟨59472, by rfl⟩ : syracuseStep 158593 = 118945) (by norm_num)
theorem B355205 : Blo 123787 355205 := bbase (se 4 (by rfl) ⟨33300, by rfl⟩ : syracuseStep 355205 = 66601) (by norm_num)
theorem B191381 : Blo 123787 191381 := bbase (se 6 (by rfl) ⟨4485, by rfl⟩ : syracuseStep 191381 = 8971) (by norm_num)
theorem B191405 : Blo 123787 191405 := bbase (se 3 (by rfl) ⟨35888, by rfl⟩ : syracuseStep 191405 = 71777) (by norm_num)
theorem B322501 : Blo 123787 322501 := bbase (se 4 (by rfl) ⟨30234, by rfl⟩ : syracuseStep 322501 = 60469) (by norm_num)
theorem B191429 : Blo 123787 191429 := bbase (se 4 (by rfl) ⟨17946, by rfl⟩ : syracuseStep 191429 = 35893) (by norm_num)
theorem B420821 : Blo 123787 420821 := bbase (se 7 (by rfl) ⟨4931, by rfl⟩ : syracuseStep 420821 = 9863) (by norm_num)
theorem B191453 : Blo 123787 191453 := bbase (se 3 (by rfl) ⟨35897, by rfl⟩ : syracuseStep 191453 = 71795) (by norm_num)
theorem B158689 : Blo 123787 158689 := bbase (se 2 (by rfl) ⟨59508, by rfl⟩ : syracuseStep 158689 = 119017) (by norm_num)
theorem B191477 : Blo 123787 191477 := bbase (se 5 (by rfl) ⟨8975, by rfl⟩ : syracuseStep 191477 = 17951) (by norm_num)
theorem B191501 : Blo 123787 191501 := bbase (se 3 (by rfl) ⟨35906, by rfl⟩ : syracuseStep 191501 = 71813) (by norm_num)
theorem B257053 : Blo 123787 257053 := bbase (se 3 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 257053 = 96395) (by norm_num)
theorem B191525 : Blo 123787 191525 := bbase (se 4 (by rfl) ⟨17955, by rfl⟩ : syracuseStep 191525 = 35911) (by norm_num)
theorem B322613 : Blo 123787 322613 := bbase (se 5 (by rfl) ⟨15122, by rfl⟩ : syracuseStep 322613 = 30245) (by norm_num)
theorem B191549 : Blo 123787 191549 := bbase (se 3 (by rfl) ⟨35915, by rfl⟩ : syracuseStep 191549 = 71831) (by norm_num)
theorem B191573 : Blo 123787 191573 := bbase (se 8 (by rfl) ⟨1122, by rfl⟩ : syracuseStep 191573 = 2245) (by norm_num)
theorem B191597 : Blo 123787 191597 := bbase (se 3 (by rfl) ⟨35924, by rfl⟩ : syracuseStep 191597 = 71849) (by norm_num)
theorem B945269 : Blo 123787 945269 := bbase (se 5 (by rfl) ⟨44309, by rfl⟩ : syracuseStep 945269 = 88619) (by norm_num)
theorem B191621 : Blo 123787 191621 := bbase (se 4 (by rfl) ⟨17964, by rfl⟩ : syracuseStep 191621 = 35929) (by norm_num)
theorem B158861 : Blo 123787 158861 := bbase (se 3 (by rfl) ⟨29786, by rfl⟩ : syracuseStep 158861 = 59573) (by norm_num)
theorem B191645 : Blo 123787 191645 := bbase (se 3 (by rfl) ⟨35933, by rfl⟩ : syracuseStep 191645 = 71867) (by norm_num)
theorem B191669 : Blo 123787 191669 := bbase (se 5 (by rfl) ⟨8984, by rfl⟩ : syracuseStep 191669 = 17969) (by norm_num)
theorem B158917 : Blo 123787 158917 := bbase (se 4 (by rfl) ⟨14898, by rfl⟩ : syracuseStep 158917 = 29797) (by norm_num)
theorem B2616533 : Blo 123787 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B322805 : Blo 123787 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B159013 : Blo 123787 159013 := bbase (se 4 (by rfl) ⟨14907, by rfl⟩ : syracuseStep 159013 = 29815) (by norm_num)
theorem B224621 : Blo 123787 224621 := bbase (se 3 (by rfl) ⟨42116, by rfl⟩ : syracuseStep 224621 = 84233) (by norm_num)
theorem B126325 : Blo 123787 126325 := bbase (se 5 (by rfl) ⟨5921, by rfl⟩ : syracuseStep 126325 = 11843) (by norm_num)
theorem B421253 : Blo 123787 421253 := bbase (se 4 (by rfl) ⟨39492, by rfl⟩ : syracuseStep 421253 = 78985) (by norm_num)
theorem B159185 : Blo 123787 159185 := bbase (se 2 (by rfl) ⟨59694, by rfl⟩ : syracuseStep 159185 = 119389) (by norm_num)
theorem B159241 : Blo 123787 159241 := bbase (se 2 (by rfl) ⟨59715, by rfl⟩ : syracuseStep 159241 = 119431) (by norm_num)
theorem B323149 : Blo 123787 323149 := bbase (se 3 (by rfl) ⟨60590, by rfl⟩ : syracuseStep 323149 = 121181) (by norm_num)
theorem B159337 : Blo 123787 159337 := bbase (se 2 (by rfl) ⟨59751, by rfl⟩ : syracuseStep 159337 = 119503) (by norm_num)
theorem B257645 : Blo 123787 257645 := bbase (se 3 (by rfl) ⟨48308, by rfl⟩ : syracuseStep 257645 = 96617) (by norm_num)
theorem B323261 : Blo 123787 323261 := bbase (se 3 (by rfl) ⟨60611, by rfl⟩ : syracuseStep 323261 = 121223) (by norm_num)
theorem B1732309 : Blo 123787 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B159449 : Blo 123787 159449 := bbase (se 2 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 159449 = 119587) (by norm_num)
theorem B257773 : Blo 123787 257773 := bbase (se 3 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 257773 = 96665) (by norm_num)
theorem B159509 : Blo 123787 159509 := bbase (se 6 (by rfl) ⟨3738, by rfl⟩ : syracuseStep 159509 = 7477) (by norm_num)
theorem B421685 : Blo 123787 421685 := bbase (se 5 (by rfl) ⟨19766, by rfl⟩ : syracuseStep 421685 = 39533) (by norm_num)
theorem B159565 : Blo 123787 159565 := bbase (se 3 (by rfl) ⟨29918, by rfl⟩ : syracuseStep 159565 = 59837) (by norm_num)
theorem B356197 : Blo 123787 356197 := bbase (se 4 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 356197 = 66787) (by norm_num)
theorem B323453 : Blo 123787 323453 := bbase (se 3 (by rfl) ⟨60647, by rfl⟩ : syracuseStep 323453 = 121295) (by norm_num)
theorem B913301 : Blo 123787 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B159661 : Blo 123787 159661 := bbase (se 3 (by rfl) ⟨29936, by rfl⟩ : syracuseStep 159661 = 59873) (by norm_num)
theorem B3502037 : Blo 123787 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B716789 : Blo 123787 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B290837 : Blo 123787 290837 := bbase (se 6 (by rfl) ⟨6816, by rfl⟩ : syracuseStep 290837 = 13633) (by norm_num)
theorem B159833 : Blo 123787 159833 := bbase (se 2 (by rfl) ⟨59937, by rfl⟩ : syracuseStep 159833 = 119875) (by norm_num)
theorem B159889 : Blo 123787 159889 := bbase (se 2 (by rfl) ⟨59958, by rfl⟩ : syracuseStep 159889 = 119917) (by norm_num)
theorem B422117 : Blo 123787 422117 := bbase (se 4 (by rfl) ⟨39573, by rfl⟩ : syracuseStep 422117 = 79147) (by norm_num)
theorem B159985 : Blo 123787 159985 := bbase (se 2 (by rfl) ⟨59994, by rfl⟩ : syracuseStep 159985 = 119989) (by norm_num)
theorem B160061 : Blo 123787 160061 := bbase (se 3 (by rfl) ⟨30011, by rfl⟩ : syracuseStep 160061 = 60023) (by norm_num)
theorem B160157 : Blo 123787 160157 := bbase (se 3 (by rfl) ⟨30029, by rfl⟩ : syracuseStep 160157 = 60059) (by norm_num)
theorem B160213 : Blo 123787 160213 := bbase (se 7 (by rfl) ⟨1877, by rfl⟩ : syracuseStep 160213 = 3755) (by norm_num)
theorem B291293 : Blo 123787 291293 := bbase (se 3 (by rfl) ⟨54617, by rfl⟩ : syracuseStep 291293 = 109235) (by norm_num)
theorem B160309 : Blo 123787 160309 := bbase (se 5 (by rfl) ⟨7514, by rfl⟩ : syracuseStep 160309 = 15029) (by norm_num)
theorem B815669 : Blo 123787 815669 := bbase (se 5 (by rfl) ⟨38234, by rfl⟩ : syracuseStep 815669 = 76469) (by norm_num)
theorem B422549 : Blo 123787 422549 := bbase (se 6 (by rfl) ⟨9903, by rfl⟩ : syracuseStep 422549 = 19807) (by norm_num)
theorem B160481 : Blo 123787 160481 := bbase (se 2 (by rfl) ⟨60180, by rfl⟩ : syracuseStep 160481 = 120361) (by norm_num)
theorem B127765 : Blo 123787 127765 := bbase (se 6 (by rfl) ⟨2994, by rfl⟩ : syracuseStep 127765 = 5989) (by norm_num)
theorem B160537 : Blo 123787 160537 := bbase (se 2 (by rfl) ⟨60201, by rfl⟩ : syracuseStep 160537 = 120403) (by norm_num)
theorem B160633 : Blo 123787 160633 := bbase (se 2 (by rfl) ⟨60237, by rfl⟩ : syracuseStep 160633 = 120475) (by norm_num)
theorem B357301 : Blo 123787 357301 := bbase (se 5 (by rfl) ⟨16748, by rfl⟩ : syracuseStep 357301 = 33497) (by norm_num)
theorem B160805 : Blo 123787 160805 := bbase (se 4 (by rfl) ⟨15075, by rfl⟩ : syracuseStep 160805 = 30151) (by norm_num)
theorem B422981 : Blo 123787 422981 := bbase (se 4 (by rfl) ⟨39654, by rfl⟩ : syracuseStep 422981 = 79309) (by norm_num)
theorem B160861 : Blo 123787 160861 := bbase (se 3 (by rfl) ⟨30161, by rfl⟩ : syracuseStep 160861 = 60323) (by norm_num)
theorem B128125 : Blo 123787 128125 := bbase (se 3 (by rfl) ⟨24023, by rfl⟩ : syracuseStep 128125 = 48047) (by norm_num)
theorem B160957 : Blo 123787 160957 := bbase (se 3 (by rfl) ⟨30179, by rfl⟩ : syracuseStep 160957 = 60359) (by norm_num)
theorem B357733 : Blo 123787 357733 := bbase (se 4 (by rfl) ⟨33537, by rfl⟩ : syracuseStep 357733 = 67075) (by norm_num)
theorem B161129 : Blo 123787 161129 := bbase (se 2 (by rfl) ⟨60423, by rfl⟩ : syracuseStep 161129 = 120847) (by norm_num)
theorem B161185 : Blo 123787 161185 := bbase (se 2 (by rfl) ⟨60444, by rfl⟩ : syracuseStep 161185 = 120889) (by norm_num)
theorem B423413 : Blo 123787 423413 := bbase (se 5 (by rfl) ⟨19847, by rfl⟩ : syracuseStep 423413 = 39695) (by norm_num)
theorem B226813 : Blo 123787 226813 := bbase (se 3 (by rfl) ⟨42527, by rfl⟩ : syracuseStep 226813 = 85055) (by norm_num)
theorem B161281 : Blo 123787 161281 := bbase (se 2 (by rfl) ⟨60480, by rfl⟩ : syracuseStep 161281 = 120961) (by norm_num)
theorem B161389 : Blo 123787 161389 := bbase (se 3 (by rfl) ⟨30260, by rfl⟩ : syracuseStep 161389 = 60521) (by norm_num)
theorem B161453 : Blo 123787 161453 := bbase (se 3 (by rfl) ⟨30272, by rfl⟩ : syracuseStep 161453 = 60545) (by norm_num)
theorem B259781 : Blo 123787 259781 := bbase (se 4 (by rfl) ⟨24354, by rfl⟩ : syracuseStep 259781 = 48709) (by norm_num)
theorem B227021 : Blo 123787 227021 := bbase (se 3 (by rfl) ⟨42566, by rfl⟩ : syracuseStep 227021 = 85133) (by norm_num)
theorem B161509 : Blo 123787 161509 := bbase (se 4 (by rfl) ⟨15141, by rfl⟩ : syracuseStep 161509 = 30283) (by norm_num)
theorem B161605 : Blo 123787 161605 := bbase (se 4 (by rfl) ⟨15150, by rfl⟩ : syracuseStep 161605 = 30301) (by norm_num)
theorem B423845 : Blo 123787 423845 := bbase (se 4 (by rfl) ⟨39735, by rfl⟩ : syracuseStep 423845 = 79471) (by norm_num)
theorem B227389 : Blo 123787 227389 := bbase (se 3 (by rfl) ⟨42635, by rfl⟩ : syracuseStep 227389 = 85271) (by norm_num)
theorem B129277 : Blo 123787 129277 := bbase (se 3 (by rfl) ⟨24239, by rfl⟩ : syracuseStep 129277 = 48479) (by norm_num)
theorem B522517 : Blo 123787 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B260405 : Blo 123787 260405 := bbase (se 5 (by rfl) ⟨12206, by rfl⟩ : syracuseStep 260405 = 24413) (by norm_num)
theorem B424277 : Blo 123787 424277 := bbase (se 10 (by rfl) ⟨621, by rfl⟩ : syracuseStep 424277 = 1243) (by norm_num)
theorem B325981 : Blo 123787 325981 := bbase (se 3 (by rfl) ⟨61121, by rfl⟩ : syracuseStep 325981 = 122243) (by norm_num)
theorem B358805 : Blo 123787 358805 := bbase (se 6 (by rfl) ⟨8409, by rfl⟩ : syracuseStep 358805 = 16819) (by norm_num)
theorem B260597 : Blo 123787 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B457285 : Blo 123787 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B424709 : Blo 123787 424709 := bbase (se 4 (by rfl) ⟨39816, by rfl⟩ : syracuseStep 424709 = 79633) (by norm_num)
theorem B162605 : Blo 123787 162605 := bbase (se 3 (by rfl) ⟨30488, by rfl⟩ : syracuseStep 162605 = 60977) (by norm_num)
theorem B228181 : Blo 123787 228181 := bbase (se 9 (by rfl) ⟨668, by rfl⟩ : syracuseStep 228181 = 1337) (by norm_num)
theorem B228197 : Blo 123787 228197 := bbase (se 4 (by rfl) ⟨21393, by rfl⟩ : syracuseStep 228197 = 42787) (by norm_num)
theorem B1637333 : Blo 123787 1637333 := bbase (se 7 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 1637333 = 38375) (by norm_num)
theorem B457733 : Blo 123787 457733 := bbase (se 4 (by rfl) ⟨42912, by rfl⟩ : syracuseStep 457733 = 85825) (by norm_num)
theorem B228413 : Blo 123787 228413 := bbase (se 3 (by rfl) ⟨42827, by rfl⟩ : syracuseStep 228413 = 85655) (by norm_num)
theorem B425141 : Blo 123787 425141 := bbase (se 5 (by rfl) ⟨19928, by rfl⟩ : syracuseStep 425141 = 39857) (by norm_num)
theorem B228557 : Blo 123787 228557 := bbase (se 3 (by rfl) ⟨42854, by rfl⟩ : syracuseStep 228557 = 85709) (by norm_num)
theorem B425573 : Blo 123787 425573 := bbase (se 4 (by rfl) ⟨39897, by rfl⟩ : syracuseStep 425573 = 79795) (by norm_num)
theorem B327397 : Blo 123787 327397 := bbase (se 4 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 327397 = 61387) (by norm_num)
theorem B229277 : Blo 123787 229277 := bbase (se 3 (by rfl) ⟨42989, by rfl⟩ : syracuseStep 229277 = 85979) (by norm_num)
theorem B360389 : Blo 123787 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B1474757 : Blo 123787 1474757 := bstep (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) B276517
theorem B426221 : Blo 123787 426221 := bstep (se 3 (by rfl) ⟨79916, by rfl⟩ : syracuseStep 426221 = 159833) B159833
theorem B426275 : Blo 123787 426275 := bstep (se 1 (by rfl) ⟨319706, by rfl⟩ : syracuseStep 426275 = 639413) B639413
theorem B3015053 : Blo 123787 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B360845 : Blo 123787 360845 := bstep (se 3 (by rfl) ⟨67658, by rfl⟩ : syracuseStep 360845 = 135317) B135317
theorem B360931 : Blo 123787 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B426545 : Blo 123787 426545 := bstep (se 2 (by rfl) ⟨159954, by rfl⟩ : syracuseStep 426545 = 319909) B319909
theorem B361037 : Blo 123787 361037 := bstep (se 3 (by rfl) ⟨67694, by rfl⟩ : syracuseStep 361037 = 135389) B135389
theorem B1573829 : Blo 123787 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B1868771 : Blo 123787 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1541105 : Blo 123787 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B427085 : Blo 123787 427085 := bstep (se 3 (by rfl) ⟨80078, by rfl⟩ : syracuseStep 427085 = 160157) B160157
theorem B132211 : Blo 123787 132211 := bstep (se 1 (by rfl) ⟨99158, by rfl⟩ : syracuseStep 132211 = 198317) B198317
theorem B427139 : Blo 123787 427139 := bstep (se 1 (by rfl) ⟨320354, by rfl⟩ : syracuseStep 427139 = 640709) B640709
theorem B427409 : Blo 123787 427409 := bstep (se 2 (by rfl) ⟨160278, by rfl⟩ : syracuseStep 427409 = 320557) B320557
theorem B362029 : Blo 123787 362029 := bstep (se 3 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 362029 = 135761) B135761
theorem B132835 : Blo 123787 132835 := bstep (se 1 (by rfl) ⟨99626, by rfl⟩ : syracuseStep 132835 = 199253) B199253
theorem B689905 : Blo 123787 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B427949 : Blo 123787 427949 := bstep (se 3 (by rfl) ⟨80240, by rfl⟩ : syracuseStep 427949 = 160481) B160481
theorem B428003 : Blo 123787 428003 := bstep (se 1 (by rfl) ⟨321002, by rfl⟩ : syracuseStep 428003 = 642005) B642005
theorem B198721 : Blo 123787 198721 := bstep (se 2 (by rfl) ⟨74520, by rfl⟩ : syracuseStep 198721 = 149041) B149041
theorem B362573 : Blo 123787 362573 := bstep (se 3 (by rfl) ⟨67982, by rfl⟩ : syracuseStep 362573 = 135965) B135965
theorem B723077 : Blo 123787 723077 := bstep (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) B135577
theorem B428273 : Blo 123787 428273 := bstep (se 2 (by rfl) ⟨160602, by rfl⟩ : syracuseStep 428273 = 321205) B321205
theorem B264593 : Blo 123787 264593 := bstep (se 2 (by rfl) ⟨99222, by rfl⟩ : syracuseStep 264593 = 198445) B198445
theorem B199265 : Blo 123787 199265 := bstep (se 2 (by rfl) ⟨74724, by rfl⟩ : syracuseStep 199265 = 149449) B149449
theorem B428813 : Blo 123787 428813 := bstep (se 3 (by rfl) ⟨80402, by rfl⟩ : syracuseStep 428813 = 160805) B160805
theorem B723761 : Blo 123787 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B428867 : Blo 123787 428867 := bstep (se 1 (by rfl) ⟨321650, by rfl⟩ : syracuseStep 428867 = 643301) B643301
theorem B265123 : Blo 123787 265123 := bstep (se 1 (by rfl) ⟨198842, by rfl⟩ : syracuseStep 265123 = 397685) B397685
theorem B1444877 : Blo 123787 1444877 := bstep (se 3 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 1444877 = 541829) B541829
theorem B429137 : Blo 123787 429137 := bstep (se 2 (by rfl) ⟨160926, by rfl⟩ : syracuseStep 429137 = 321853) B321853
theorem B363761 : Blo 123787 363761 := bstep (se 2 (by rfl) ⟨136410, by rfl⟩ : syracuseStep 363761 = 272821) B272821
theorem B1707317 : Blo 123787 1707317 := bstep (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) B160061
theorem B200227 : Blo 123787 200227 := bstep (se 1 (by rfl) ⟨150170, by rfl⟩ : syracuseStep 200227 = 300341) B300341
theorem B134723 : Blo 123787 134723 := bstep (se 1 (by rfl) ⟨101042, by rfl⟩ : syracuseStep 134723 = 202085) B202085
theorem B429677 : Blo 123787 429677 := bstep (se 3 (by rfl) ⟨80564, by rfl⟩ : syracuseStep 429677 = 161129) B161129
theorem B429731 : Blo 123787 429731 := bstep (se 1 (by rfl) ⟨322298, by rfl⟩ : syracuseStep 429731 = 644597) B644597
theorem B200483 : Blo 123787 200483 := bstep (se 1 (by rfl) ⟨150362, by rfl⟩ : syracuseStep 200483 = 300725) B300725
theorem B430001 : Blo 123787 430001 := bstep (se 2 (by rfl) ⟨161250, by rfl⟩ : syracuseStep 430001 = 322501) B322501
theorem B331793 : Blo 123787 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B2330765 : Blo 123787 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B725219 : Blo 123787 725219 := bstep (se 1 (by rfl) ⟨543914, by rfl⟩ : syracuseStep 725219 = 1087829) B1087829
theorem B266609 : Blo 123787 266609 := bstep (se 2 (by rfl) ⟨99978, by rfl⟩ : syracuseStep 266609 = 199957) B199957
theorem B266627 : Blo 123787 266627 := bstep (se 1 (by rfl) ⟨199970, by rfl⟩ : syracuseStep 266627 = 399941) B399941
theorem B430541 : Blo 123787 430541 := bstep (se 3 (by rfl) ⟨80726, by rfl⟩ : syracuseStep 430541 = 161453) B161453
theorem B201187 : Blo 123787 201187 := bstep (se 1 (by rfl) ⟨150890, by rfl⟩ : syracuseStep 201187 = 301781) B301781
theorem B430595 : Blo 123787 430595 := bstep (se 1 (by rfl) ⟨322946, by rfl⟩ : syracuseStep 430595 = 645893) B645893
theorem B692749 : Blo 123787 692749 := bstep (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) B259781
theorem B201457 : Blo 123787 201457 := bstep (se 2 (by rfl) ⟨75546, by rfl⟩ : syracuseStep 201457 = 151093) B151093
theorem B430865 : Blo 123787 430865 := bstep (se 2 (by rfl) ⟨161574, by rfl⟩ : syracuseStep 430865 = 323149) B323149
theorem B201521 : Blo 123787 201521 := bstep (se 2 (by rfl) ⟨75570, by rfl⟩ : syracuseStep 201521 = 151141) B151141
theorem B398189 : Blo 123787 398189 := bstep (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) B149321
theorem B529649 : Blo 123787 529649 := bstep (se 2 (by rfl) ⟨198618, by rfl⟩ : syracuseStep 529649 = 397237) B397237
theorem B529699 : Blo 123787 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B235057 : Blo 123787 235057 := bstep (se 2 (by rfl) ⟨88146, by rfl⟩ : syracuseStep 235057 = 176293) B176293
theorem B398915 : Blo 123787 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B267857 : Blo 123787 267857 := bstep (se 2 (by rfl) ⟨100446, by rfl⟩ : syracuseStep 267857 = 200893) B200893
theorem B235217 : Blo 123787 235217 := bstep (se 2 (by rfl) ⟨88206, by rfl⟩ : syracuseStep 235217 = 176413) B176413
theorem B169795 : Blo 123787 169795 := bstep (se 1 (by rfl) ⟨127346, by rfl⟩ : syracuseStep 169795 = 254693) B254693
theorem B1447793 : Blo 123787 1447793 := bstep (se 2 (by rfl) ⟨542922, by rfl⟩ : syracuseStep 1447793 = 1085845) B1085845
theorem B759779 : Blo 123787 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B628721 : Blo 123787 628721 := bstep (se 2 (by rfl) ⟨235770, by rfl⟩ : syracuseStep 628721 = 471541) B471541
theorem B235619 : Blo 123787 235619 := bstep (se 1 (by rfl) ⟨176714, by rfl⟩ : syracuseStep 235619 = 353429) B353429
theorem B170195 : Blo 123787 170195 := bstep (se 1 (by rfl) ⟨127646, by rfl⟩ : syracuseStep 170195 = 255293) B255293
theorem B301283 : Blo 123787 301283 := bstep (se 1 (by rfl) ⟨225962, by rfl⟩ : syracuseStep 301283 = 451925) B451925
theorem B2070755 : Blo 123787 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B792845 : Blo 123787 792845 := bstep (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) B297317
theorem B170353 : Blo 123787 170353 := bstep (se 2 (by rfl) ⟨63882, by rfl⟩ : syracuseStep 170353 = 127765) B127765
theorem B399761 : Blo 123787 399761 := bstep (se 2 (by rfl) ⟨149910, by rfl⟩ : syracuseStep 399761 = 299821) B299821
theorem B399811 : Blo 123787 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B203251 : Blo 123787 203251 := bstep (se 1 (by rfl) ⟨152438, by rfl⟩ : syracuseStep 203251 = 304877) B304877
theorem B694925 : Blo 123787 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B367249 : Blo 123787 367249 := bstep (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) B275437
theorem B170833 : Blo 123787 170833 := bstep (se 2 (by rfl) ⟨64062, by rfl⟩ : syracuseStep 170833 = 128125) B128125
theorem B203699 : Blo 123787 203699 := bstep (se 1 (by rfl) ⟨152774, by rfl⟩ : syracuseStep 203699 = 305549) B305549
theorem B236515 : Blo 123787 236515 := bstep (se 1 (by rfl) ⟨177386, by rfl⟩ : syracuseStep 236515 = 354773) B354773
theorem B269347 : Blo 123787 269347 := bstep (se 1 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 269347 = 404021) B404021
theorem B269411 : Blo 123787 269411 := bstep (se 1 (by rfl) ⟨202058, by rfl⟩ : syracuseStep 269411 = 404117) B404117
theorem B236675 : Blo 123787 236675 := bstep (se 1 (by rfl) ⟨177506, by rfl⟩ : syracuseStep 236675 = 355013) B355013
theorem B335117 : Blo 123787 335117 := bstep (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) B125669
theorem B204083 : Blo 123787 204083 := bstep (se 1 (by rfl) ⟨153062, by rfl⟩ : syracuseStep 204083 = 306125) B306125
theorem B302417 : Blo 123787 302417 := bstep (se 2 (by rfl) ⟨113406, by rfl⟩ : syracuseStep 302417 = 226813) B226813
theorem B630179 : Blo 123787 630179 := bstep (se 1 (by rfl) ⟨472634, by rfl⟩ : syracuseStep 630179 = 945269) B945269
theorem B433613 : Blo 123787 433613 := bstep (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) B162605
theorem B204257 : Blo 123787 204257 := bstep (se 2 (by rfl) ⟨76596, by rfl⟩ : syracuseStep 204257 = 153193) B153193
theorem B1744355 : Blo 123787 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B532109 : Blo 123787 532109 := bstep (se 3 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 532109 = 199541) B199541
theorem B401041 : Blo 123787 401041 := bstep (se 2 (by rfl) ⟨150390, by rfl⟩ : syracuseStep 401041 = 300781) B300781
theorem B204481 : Blo 123787 204481 := bstep (se 2 (by rfl) ⟨76680, by rfl⟩ : syracuseStep 204481 = 153361) B153361
theorem B171763 : Blo 123787 171763 := bstep (se 1 (by rfl) ⟨128822, by rfl⟩ : syracuseStep 171763 = 257645) B257645
theorem B204545 : Blo 123787 204545 := bstep (se 2 (by rfl) ⟨76704, by rfl⟩ : syracuseStep 204545 = 153409) B153409
theorem B204673 : Blo 123787 204673 := bstep (se 2 (by rfl) ⟨76752, by rfl⟩ : syracuseStep 204673 = 153505) B153505
theorem B2334691 : Blo 123787 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B139315 : Blo 123787 139315 := bstep (se 1 (by rfl) ⟨104486, by rfl⟩ : syracuseStep 139315 = 208973) B208973
theorem B794701 : Blo 123787 794701 := bstep (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) B298013
theorem B303185 : Blo 123787 303185 := bstep (se 2 (by rfl) ⟨113694, by rfl⟩ : syracuseStep 303185 = 227389) B227389
theorem B237745 : Blo 123787 237745 := bstep (se 2 (by rfl) ⟨89154, by rfl⟩ : syracuseStep 237745 = 178309) B178309
theorem B139459 : Blo 123787 139459 := bstep (se 1 (by rfl) ⟨104594, by rfl⟩ : syracuseStep 139459 = 209189) B209189
theorem B630989 : Blo 123787 630989 := bstep (se 3 (by rfl) ⟨118310, by rfl⟩ : syracuseStep 630989 = 236621) B236621
theorem B172369 : Blo 123787 172369 := bstep (se 2 (by rfl) ⟨64638, by rfl⟩ : syracuseStep 172369 = 129277) B129277
theorem B139603 : Blo 123787 139603 := bstep (se 1 (by rfl) ⟨104702, by rfl⟩ : syracuseStep 139603 = 209405) B209405
theorem B696689 : Blo 123787 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B434641 : Blo 123787 434641 := bstep (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) B325981
theorem B139747 : Blo 123787 139747 := bstep (se 1 (by rfl) ⟨104810, by rfl⟩ : syracuseStep 139747 = 209621) B209621
theorem B139891 : Blo 123787 139891 := bstep (se 1 (by rfl) ⟨104918, by rfl⟩ : syracuseStep 139891 = 209837) B209837
theorem B140035 : Blo 123787 140035 := bstep (se 1 (by rfl) ⟨105026, by rfl⟩ : syracuseStep 140035 = 210053) B210053
theorem B402221 : Blo 123787 402221 := bstep (se 3 (by rfl) ⟨75416, by rfl⟩ : syracuseStep 402221 = 150833) B150833
theorem B140179 : Blo 123787 140179 := bstep (se 1 (by rfl) ⟨105134, by rfl⟩ : syracuseStep 140179 = 210269) B210269
theorem B140323 : Blo 123787 140323 := bstep (se 1 (by rfl) ⟨105242, by rfl⟩ : syracuseStep 140323 = 210485) B210485
theorem B336995 : Blo 123787 336995 := bstep (se 1 (by rfl) ⟨252746, by rfl⟩ : syracuseStep 336995 = 505493) B505493
theorem B304241 : Blo 123787 304241 := bstep (se 2 (by rfl) ⟨114090, by rfl⟩ : syracuseStep 304241 = 228181) B228181
theorem B140467 : Blo 123787 140467 := bstep (se 1 (by rfl) ⟨105350, by rfl⟩ : syracuseStep 140467 = 210701) B210701
theorem B238801 : Blo 123787 238801 := bstep (se 2 (by rfl) ⟨89550, by rfl⟩ : syracuseStep 238801 = 179101) B179101
theorem B271633 : Blo 123787 271633 := bstep (se 2 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 271633 = 203725) B203725
theorem B140611 : Blo 123787 140611 := bstep (se 1 (by rfl) ⟨105458, by rfl⟩ : syracuseStep 140611 = 210917) B210917
theorem B140755 : Blo 123787 140755 := bstep (se 1 (by rfl) ⟨105566, by rfl⟩ : syracuseStep 140755 = 211133) B211133
theorem B173603 : Blo 123787 173603 := bstep (se 1 (by rfl) ⟨130202, by rfl⟩ : syracuseStep 173603 = 260405) B260405
theorem B140899 : Blo 123787 140899 := bstep (se 1 (by rfl) ⟨105674, by rfl⟩ : syracuseStep 140899 = 211349) B211349
theorem B239203 : Blo 123787 239203 := bstep (se 1 (by rfl) ⟨179402, by rfl⟩ : syracuseStep 239203 = 358805) B358805
theorem B239249 : Blo 123787 239249 := bstep (se 2 (by rfl) ⟨89718, by rfl⟩ : syracuseStep 239249 = 179437) B179437
theorem B141043 : Blo 123787 141043 := bstep (se 1 (by rfl) ⟨105782, by rfl⟩ : syracuseStep 141043 = 211565) B211565
theorem B141187 : Blo 123787 141187 := bstep (se 1 (by rfl) ⟨105890, by rfl⟩ : syracuseStep 141187 = 211781) B211781
theorem B239537 : Blo 123787 239537 := bstep (se 2 (by rfl) ⟨89826, by rfl⟩ : syracuseStep 239537 = 179653) B179653
theorem B1091555 : Blo 123787 1091555 := bstep (se 1 (by rfl) ⟨818666, by rfl⟩ : syracuseStep 1091555 = 1637333) B1637333
theorem B305155 : Blo 123787 305155 := bstep (se 1 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 305155 = 457733) B457733
theorem B337937 : Blo 123787 337937 := bstep (se 2 (by rfl) ⟨126726, by rfl⟩ : syracuseStep 337937 = 253453) B253453
theorem B141331 : Blo 123787 141331 := bstep (se 1 (by rfl) ⟨105998, by rfl⟩ : syracuseStep 141331 = 211997) B211997
theorem B337969 : Blo 123787 337969 := bstep (se 2 (by rfl) ⟨126738, by rfl⟩ : syracuseStep 337969 = 253477) B253477
theorem B338033 : Blo 123787 338033 := bstep (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) B253525
theorem B141475 : Blo 123787 141475 := bstep (se 1 (by rfl) ⟨106106, by rfl⟩ : syracuseStep 141475 = 212213) B212213
theorem B436529 : Blo 123787 436529 := bstep (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) B327397
theorem B141619 : Blo 123787 141619 := bstep (se 1 (by rfl) ⟨106214, by rfl⟩ : syracuseStep 141619 = 212429) B212429
theorem B141763 : Blo 123787 141763 := bstep (se 1 (by rfl) ⟨106322, by rfl⟩ : syracuseStep 141763 = 212645) B212645
theorem B272899 : Blo 123787 272899 := bstep (se 1 (by rfl) ⟨204674, by rfl⟩ : syracuseStep 272899 = 409349) B409349
theorem B404003 : Blo 123787 404003 := bstep (se 1 (by rfl) ⟨303002, by rfl⟩ : syracuseStep 404003 = 606005) B606005
theorem B141907 : Blo 123787 141907 := bstep (se 1 (by rfl) ⟨106430, by rfl⟩ : syracuseStep 141907 = 212861) B212861
theorem B240259 : Blo 123787 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B142051 : Blo 123787 142051 := bstep (se 1 (by rfl) ⟨106538, by rfl⟩ : syracuseStep 142051 = 213077) B213077
theorem B371491 : Blo 123787 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B142195 : Blo 123787 142195 := bstep (se 1 (by rfl) ⟨106646, by rfl⟩ : syracuseStep 142195 = 213293) B213293
theorem B2698211 : Blo 123787 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B142339 : Blo 123787 142339 := bstep (se 1 (by rfl) ⟨106754, by rfl⟩ : syracuseStep 142339 = 213509) B213509
theorem B633905 : Blo 123787 633905 := bstep (se 2 (by rfl) ⟨237714, by rfl⟩ : syracuseStep 633905 = 475429) B475429
theorem B240707 : Blo 123787 240707 := bstep (se 1 (by rfl) ⟨180530, by rfl⟩ : syracuseStep 240707 = 361061) B361061
theorem B142483 : Blo 123787 142483 := bstep (se 1 (by rfl) ⟨106862, by rfl⟩ : syracuseStep 142483 = 213725) B213725
theorem B142627 : Blo 123787 142627 := bstep (se 1 (by rfl) ⟨106970, by rfl⟩ : syracuseStep 142627 = 213941) B213941
theorem B240995 : Blo 123787 240995 := bstep (se 1 (by rfl) ⟨180746, by rfl⟩ : syracuseStep 240995 = 361493) B361493
theorem B142771 : Blo 123787 142771 := bstep (se 1 (by rfl) ⟨107078, by rfl⟩ : syracuseStep 142771 = 214157) B214157
theorem B404945 : Blo 123787 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B142915 : Blo 123787 142915 := bstep (se 1 (by rfl) ⟨107186, by rfl⟩ : syracuseStep 142915 = 214373) B214373
theorem B405091 : Blo 123787 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B143059 : Blo 123787 143059 := bstep (se 1 (by rfl) ⟨107294, by rfl⟩ : syracuseStep 143059 = 214589) B214589
theorem B405233 : Blo 123787 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B143203 : Blo 123787 143203 := bstep (se 1 (by rfl) ⟨107402, by rfl⟩ : syracuseStep 143203 = 214805) B214805
theorem B536483 : Blo 123787 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B143347 : Blo 123787 143347 := bstep (se 1 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 143347 = 215021) B215021
theorem B143411 : Blo 123787 143411 := bstep (se 1 (by rfl) ⟨107558, by rfl⟩ : syracuseStep 143411 = 215117) B215117
theorem B208993 : Blo 123787 208993 := bstep (se 2 (by rfl) ⟨78372, by rfl⟩ : syracuseStep 208993 = 156745) B156745
theorem B209027 : Blo 123787 209027 := bstep (se 1 (by rfl) ⟨156770, by rfl⟩ : syracuseStep 209027 = 313541) B313541
theorem B143491 : Blo 123787 143491 := bstep (se 1 (by rfl) ⟨107618, by rfl⟩ : syracuseStep 143491 = 215237) B215237
theorem B209155 : Blo 123787 209155 := bstep (se 1 (by rfl) ⟨156866, by rfl⟩ : syracuseStep 209155 = 313733) B313733
theorem B241937 : Blo 123787 241937 := bstep (se 2 (by rfl) ⟨90726, by rfl⟩ : syracuseStep 241937 = 181453) B181453
theorem B143635 : Blo 123787 143635 := bstep (se 1 (by rfl) ⟨107726, by rfl⟩ : syracuseStep 143635 = 215453) B215453
theorem B209297 : Blo 123787 209297 := bstep (se 2 (by rfl) ⟨78486, by rfl⟩ : syracuseStep 209297 = 156973) B156973
theorem B242129 : Blo 123787 242129 := bstep (se 2 (by rfl) ⟨90798, by rfl⟩ : syracuseStep 242129 = 181597) B181597
theorem B635363 : Blo 123787 635363 := bstep (se 1 (by rfl) ⟨476522, by rfl⟩ : syracuseStep 635363 = 953045) B953045
theorem B209425 : Blo 123787 209425 := bstep (se 2 (by rfl) ⟨78534, by rfl⟩ : syracuseStep 209425 = 157069) B157069
theorem B209459 : Blo 123787 209459 := bstep (se 1 (by rfl) ⟨157094, by rfl⟩ : syracuseStep 209459 = 314189) B314189
theorem B176737 : Blo 123787 176737 := bstep (se 2 (by rfl) ⟨66276, by rfl⟩ : syracuseStep 176737 = 132553) B132553
theorem B209587 : Blo 123787 209587 := bstep (se 1 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 209587 = 314381) B314381
theorem B176851 : Blo 123787 176851 := bstep (se 1 (by rfl) ⟨132638, by rfl⟩ : syracuseStep 176851 = 265277) B265277
theorem B209729 : Blo 123787 209729 := bstep (se 2 (by rfl) ⟨78648, by rfl⟩ : syracuseStep 209729 = 157297) B157297
theorem B635825 : Blo 123787 635825 := bstep (se 2 (by rfl) ⟨238434, by rfl⟩ : syracuseStep 635825 = 476869) B476869
theorem B209857 : Blo 123787 209857 := bstep (se 2 (by rfl) ⟨78696, by rfl⟩ : syracuseStep 209857 = 157393) B157393
theorem B472013 : Blo 123787 472013 := bstep (se 3 (by rfl) ⟨88502, by rfl⟩ : syracuseStep 472013 = 177005) B177005
theorem B209891 : Blo 123787 209891 := bstep (se 1 (by rfl) ⟨157418, by rfl⟩ : syracuseStep 209891 = 314837) B314837
theorem B406577 : Blo 123787 406577 := bstep (se 2 (by rfl) ⟨152466, by rfl⟩ : syracuseStep 406577 = 304933) B304933
theorem B210019 : Blo 123787 210019 := bstep (se 1 (by rfl) ⟨157514, by rfl⟩ : syracuseStep 210019 = 315029) B315029
theorem B504973 : Blo 123787 504973 := bstep (se 3 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 504973 = 189365) B189365
theorem B210161 : Blo 123787 210161 := bstep (se 2 (by rfl) ⟨78810, by rfl⟩ : syracuseStep 210161 = 157621) B157621
theorem B636173 : Blo 123787 636173 := bstep (se 3 (by rfl) ⟨119282, by rfl⟩ : syracuseStep 636173 = 238565) B238565
theorem B210289 : Blo 123787 210289 := bstep (se 2 (by rfl) ⟨78858, by rfl⟩ : syracuseStep 210289 = 157717) B157717
theorem B210323 : Blo 123787 210323 := bstep (se 1 (by rfl) ⟨157742, by rfl⟩ : syracuseStep 210323 = 315485) B315485
theorem B210451 : Blo 123787 210451 := bstep (se 1 (by rfl) ⟨157838, by rfl⟩ : syracuseStep 210451 = 315677) B315677
theorem B210593 : Blo 123787 210593 := bstep (se 2 (by rfl) ⟨78972, by rfl⟩ : syracuseStep 210593 = 157945) B157945
theorem B472817 : Blo 123787 472817 := bstep (se 2 (by rfl) ⟨177306, by rfl⟩ : syracuseStep 472817 = 354613) B354613
theorem B210721 : Blo 123787 210721 := bstep (se 2 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 210721 = 158041) B158041
theorem B210755 : Blo 123787 210755 := bstep (se 1 (by rfl) ⟨158066, by rfl⟩ : syracuseStep 210755 = 316133) B316133
theorem B1357667 : Blo 123787 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B538481 : Blo 123787 538481 := bstep (se 2 (by rfl) ⟨201930, by rfl⟩ : syracuseStep 538481 = 403861) B403861
theorem B210883 : Blo 123787 210883 := bstep (se 1 (by rfl) ⟨158162, by rfl⟩ : syracuseStep 210883 = 316325) B316325
theorem B407501 : Blo 123787 407501 := bstep (se 3 (by rfl) ⟨76406, by rfl⟩ : syracuseStep 407501 = 152813) B152813
theorem B669667 : Blo 123787 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B767971 : Blo 123787 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B178195 : Blo 123787 178195 := bstep (se 1 (by rfl) ⟨133646, by rfl⟩ : syracuseStep 178195 = 267293) B267293
theorem B211025 : Blo 123787 211025 := bstep (se 2 (by rfl) ⟨79134, by rfl⟩ : syracuseStep 211025 = 158269) B158269
theorem B407693 : Blo 123787 407693 := bstep (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) B152885
theorem B211153 : Blo 123787 211153 := bstep (se 2 (by rfl) ⟨79182, by rfl⟩ : syracuseStep 211153 = 158365) B158365
theorem B211187 : Blo 123787 211187 := bstep (se 1 (by rfl) ⟨158390, by rfl⟩ : syracuseStep 211187 = 316781) B316781
theorem B637283 : Blo 123787 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B211315 : Blo 123787 211315 := bstep (se 1 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 211315 = 316973) B316973
theorem B473485 : Blo 123787 473485 := bstep (se 3 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 473485 = 177557) B177557
theorem B211457 : Blo 123787 211457 := bstep (se 2 (by rfl) ⟨79296, by rfl⟩ : syracuseStep 211457 = 158593) B158593
theorem B440909 : Blo 123787 440909 := bstep (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) B165341
theorem B211585 : Blo 123787 211585 := bstep (se 2 (by rfl) ⟨79344, by rfl⟩ : syracuseStep 211585 = 158689) B158689
theorem B211619 : Blo 123787 211619 := bstep (se 1 (by rfl) ⟨158714, by rfl⟩ : syracuseStep 211619 = 317429) B317429
theorem B342737 : Blo 123787 342737 := bstep (se 2 (by rfl) ⟨128526, by rfl⟩ : syracuseStep 342737 = 257053) B257053
theorem B801521 : Blo 123787 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B539405 : Blo 123787 539405 := bstep (se 3 (by rfl) ⟨101138, by rfl⟩ : syracuseStep 539405 = 202277) B202277
theorem B211747 : Blo 123787 211747 := bstep (se 1 (by rfl) ⟨158810, by rfl⟩ : syracuseStep 211747 = 317621) B317621
theorem B1194821 : Blo 123787 1194821 := bstep (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) B224029
theorem B211889 : Blo 123787 211889 := bstep (se 2 (by rfl) ⟨79458, by rfl⟩ : syracuseStep 211889 = 158917) B158917
theorem B441379 : Blo 123787 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B212017 : Blo 123787 212017 := bstep (se 2 (by rfl) ⟨79506, by rfl⟩ : syracuseStep 212017 = 159013) B159013
theorem B212051 : Blo 123787 212051 := bstep (se 1 (by rfl) ⟨159038, by rfl⟩ : syracuseStep 212051 = 318077) B318077
theorem B179329 : Blo 123787 179329 := bstep (se 2 (by rfl) ⟨67248, by rfl⟩ : syracuseStep 179329 = 134497) B134497
theorem B474275 : Blo 123787 474275 := bstep (se 1 (by rfl) ⟨355706, by rfl⟩ : syracuseStep 474275 = 711413) B711413
theorem B605389 : Blo 123787 605389 := bstep (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) B227021
theorem B212179 : Blo 123787 212179 := bstep (se 1 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 212179 = 318269) B318269
theorem B179425 : Blo 123787 179425 := bstep (se 2 (by rfl) ⟨67284, by rfl⟩ : syracuseStep 179425 = 134569) B134569
theorem B802061 : Blo 123787 802061 := bstep (se 3 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 802061 = 300773) B300773
theorem B212321 : Blo 123787 212321 := bstep (se 2 (by rfl) ⟨79620, by rfl⟩ : syracuseStep 212321 = 159241) B159241
theorem B212449 : Blo 123787 212449 := bstep (se 2 (by rfl) ⟨79668, by rfl⟩ : syracuseStep 212449 = 159337) B159337
theorem B343523 : Blo 123787 343523 := bstep (se 1 (by rfl) ⟨257642, by rfl⟩ : syracuseStep 343523 = 515285) B515285
theorem B507377 : Blo 123787 507377 := bstep (se 2 (by rfl) ⟨190266, by rfl⟩ : syracuseStep 507377 = 380533) B380533
theorem B212483 : Blo 123787 212483 := bstep (se 1 (by rfl) ⟨159362, by rfl⟩ : syracuseStep 212483 = 318725) B318725
theorem B212611 : Blo 123787 212611 := bstep (se 1 (by rfl) ⟨159458, by rfl⟩ : syracuseStep 212611 = 318917) B318917
theorem B343697 : Blo 123787 343697 := bstep (se 2 (by rfl) ⟨128886, by rfl⟩ : syracuseStep 343697 = 257773) B257773
theorem B179921 : Blo 123787 179921 := bstep (se 2 (by rfl) ⟨67470, by rfl⟩ : syracuseStep 179921 = 134941) B134941
theorem B212753 : Blo 123787 212753 := bstep (se 2 (by rfl) ⟨79782, by rfl⟩ : syracuseStep 212753 = 159565) B159565
theorem B474929 : Blo 123787 474929 := bstep (se 2 (by rfl) ⟨178098, by rfl⟩ : syracuseStep 474929 = 356197) B356197
theorem B212881 : Blo 123787 212881 := bstep (se 2 (by rfl) ⟨79830, by rfl⟩ : syracuseStep 212881 = 159661) B159661
theorem B212915 : Blo 123787 212915 := bstep (se 1 (by rfl) ⟨159686, by rfl⟩ : syracuseStep 212915 = 319373) B319373
theorem B278531 : Blo 123787 278531 := bstep (se 1 (by rfl) ⟨208898, by rfl⟩ : syracuseStep 278531 = 417797) B417797
theorem B213043 : Blo 123787 213043 := bstep (se 1 (by rfl) ⟨159782, by rfl⟩ : syracuseStep 213043 = 319565) B319565
theorem B639089 : Blo 123787 639089 := bstep (se 2 (by rfl) ⟨239658, by rfl⟩ : syracuseStep 639089 = 479317) B479317
theorem B213185 : Blo 123787 213185 := bstep (se 2 (by rfl) ⟨79944, by rfl⟩ : syracuseStep 213185 = 159889) B159889
theorem B409841 : Blo 123787 409841 := bstep (se 2 (by rfl) ⟨153690, by rfl⟩ : syracuseStep 409841 = 307381) B307381
theorem B770309 : Blo 123787 770309 := bstep (se 4 (by rfl) ⟨72216, by rfl⟩ : syracuseStep 770309 = 144433) B144433
theorem B278801 : Blo 123787 278801 := bstep (se 2 (by rfl) ⟨104550, by rfl⟩ : syracuseStep 278801 = 209101) B209101
theorem B278819 : Blo 123787 278819 := bstep (se 1 (by rfl) ⟨209114, by rfl⟩ : syracuseStep 278819 = 418229) B418229
theorem B213313 : Blo 123787 213313 := bstep (se 2 (by rfl) ⟨79992, by rfl⟩ : syracuseStep 213313 = 159985) B159985
theorem B672077 : Blo 123787 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B213347 : Blo 123787 213347 := bstep (se 1 (by rfl) ⟨160010, by rfl⟩ : syracuseStep 213347 = 320021) B320021
theorem B213475 : Blo 123787 213475 := bstep (se 1 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 213475 = 320213) B320213
theorem B967139 : Blo 123787 967139 := bstep (se 1 (by rfl) ⟨725354, by rfl⟩ : syracuseStep 967139 = 1450709) B1450709
theorem B279089 : Blo 123787 279089 := bstep (se 2 (by rfl) ⟨104658, by rfl⟩ : syracuseStep 279089 = 209317) B209317
theorem B180787 : Blo 123787 180787 := bstep (se 1 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 180787 = 271181) B271181
theorem B1589813 : Blo 123787 1589813 := bstep (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) B149045
theorem B279107 : Blo 123787 279107 := bstep (se 1 (by rfl) ⟨209330, by rfl⟩ : syracuseStep 279107 = 418661) B418661
theorem B410179 : Blo 123787 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B213617 : Blo 123787 213617 := bstep (se 2 (by rfl) ⟨80106, by rfl⟩ : syracuseStep 213617 = 160213) B160213
theorem B180883 : Blo 123787 180883 := bstep (se 1 (by rfl) ⟨135662, by rfl⟩ : syracuseStep 180883 = 271325) B271325
theorem B213745 : Blo 123787 213745 := bstep (se 2 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 213745 = 160309) B160309
theorem B213779 : Blo 123787 213779 := bstep (se 1 (by rfl) ⟨160334, by rfl⟩ : syracuseStep 213779 = 320669) B320669
theorem B279377 : Blo 123787 279377 := bstep (se 2 (by rfl) ⟨104766, by rfl⟩ : syracuseStep 279377 = 209533) B209533
theorem B279395 : Blo 123787 279395 := bstep (se 1 (by rfl) ⟨209546, by rfl⟩ : syracuseStep 279395 = 419093) B419093
theorem B213907 : Blo 123787 213907 := bstep (se 1 (by rfl) ⟨160430, by rfl⟩ : syracuseStep 213907 = 320861) B320861
theorem B214049 : Blo 123787 214049 := bstep (se 2 (by rfl) ⟨80268, by rfl⟩ : syracuseStep 214049 = 160537) B160537
theorem B279665 : Blo 123787 279665 := bstep (se 2 (by rfl) ⟨104874, by rfl⟩ : syracuseStep 279665 = 209749) B209749
theorem B279683 : Blo 123787 279683 := bstep (se 1 (by rfl) ⟨209762, by rfl⟩ : syracuseStep 279683 = 419525) B419525
theorem B181379 : Blo 123787 181379 := bstep (se 1 (by rfl) ⟨136034, by rfl⟩ : syracuseStep 181379 = 272069) B272069
theorem B214177 : Blo 123787 214177 := bstep (se 2 (by rfl) ⟨80316, by rfl⟩ : syracuseStep 214177 = 160633) B160633
theorem B214211 : Blo 123787 214211 := bstep (se 1 (by rfl) ⟨160658, by rfl⟩ : syracuseStep 214211 = 321317) B321317
theorem B476387 : Blo 123787 476387 := bstep (se 1 (by rfl) ⟨357290, by rfl⟩ : syracuseStep 476387 = 714581) B714581
theorem B476401 : Blo 123787 476401 := bstep (se 2 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 476401 = 357301) B357301
theorem B214339 : Blo 123787 214339 := bstep (se 1 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 214339 = 321509) B321509
theorem B279953 : Blo 123787 279953 := bstep (se 2 (by rfl) ⟨104982, by rfl⟩ : syracuseStep 279953 = 209965) B209965
theorem B279971 : Blo 123787 279971 := bstep (se 1 (by rfl) ⟨209978, by rfl⟩ : syracuseStep 279971 = 419957) B419957
theorem B476621 : Blo 123787 476621 := bstep (se 3 (by rfl) ⟨89366, by rfl⟩ : syracuseStep 476621 = 178733) B178733
theorem B214481 : Blo 123787 214481 := bstep (se 2 (by rfl) ⟨80430, by rfl⟩ : syracuseStep 214481 = 160861) B160861
theorem B509453 : Blo 123787 509453 := bstep (se 3 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 509453 = 191045) B191045
theorem B640547 : Blo 123787 640547 := bstep (se 1 (by rfl) ⟨480410, by rfl⟩ : syracuseStep 640547 = 960821) B960821
theorem B214609 : Blo 123787 214609 := bstep (se 2 (by rfl) ⟨80478, by rfl⟩ : syracuseStep 214609 = 160957) B160957
theorem B214643 : Blo 123787 214643 := bstep (se 1 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 214643 = 321965) B321965
theorem B181921 : Blo 123787 181921 := bstep (se 2 (by rfl) ⟨68220, by rfl⟩ : syracuseStep 181921 = 136441) B136441
theorem B280241 : Blo 123787 280241 := bstep (se 2 (by rfl) ⟨105090, by rfl⟩ : syracuseStep 280241 = 210181) B210181
theorem B280259 : Blo 123787 280259 := bstep (se 1 (by rfl) ⟨210194, by rfl⟩ : syracuseStep 280259 = 420389) B420389
theorem B509645 : Blo 123787 509645 := bstep (se 3 (by rfl) ⟨95558, by rfl⟩ : syracuseStep 509645 = 191117) B191117
theorem B214771 : Blo 123787 214771 := bstep (se 1 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 214771 = 322157) B322157
theorem B476977 : Blo 123787 476977 := bstep (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) B357733
theorem B542513 : Blo 123787 542513 := bstep (se 2 (by rfl) ⟨203442, by rfl⟩ : syracuseStep 542513 = 406885) B406885
theorem B182131 : Blo 123787 182131 := bstep (se 1 (by rfl) ⟨136598, by rfl⟩ : syracuseStep 182131 = 273197) B273197
theorem B214913 : Blo 123787 214913 := bstep (se 2 (by rfl) ⟨80592, by rfl⟩ : syracuseStep 214913 = 161185) B161185
theorem B149411 : Blo 123787 149411 := bstep (se 1 (by rfl) ⟨112058, by rfl⟩ : syracuseStep 149411 = 224117) B224117
theorem B1427381 : Blo 123787 1427381 := bstep (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) B133817
theorem B673733 : Blo 123787 673733 := bstep (se 4 (by rfl) ⟨63162, by rfl⟩ : syracuseStep 673733 = 126325) B126325
theorem B280529 : Blo 123787 280529 := bstep (se 2 (by rfl) ⟨105198, by rfl⟩ : syracuseStep 280529 = 210397) B210397
theorem B280547 : Blo 123787 280547 := bstep (se 1 (by rfl) ⟨210410, by rfl⟩ : syracuseStep 280547 = 420821) B420821
theorem B215041 : Blo 123787 215041 := bstep (se 2 (by rfl) ⟨80640, by rfl⟩ : syracuseStep 215041 = 161281) B161281
theorem B313379 : Blo 123787 313379 := bstep (se 1 (by rfl) ⟨235034, by rfl⟩ : syracuseStep 313379 = 470069) B470069
theorem B215075 : Blo 123787 215075 := bstep (se 1 (by rfl) ⟨161306, by rfl⟩ : syracuseStep 215075 = 322613) B322613
theorem B215185 : Blo 123787 215185 := bstep (se 2 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 215185 = 161389) B161389
theorem B215203 : Blo 123787 215203 := bstep (se 1 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 215203 = 322805) B322805
theorem B706765 : Blo 123787 706765 := bstep (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) B265037
theorem B313571 : Blo 123787 313571 := bstep (se 1 (by rfl) ⟨235178, by rfl⟩ : syracuseStep 313571 = 470357) B470357
theorem B280817 : Blo 123787 280817 := bstep (se 2 (by rfl) ⟨105306, by rfl⟩ : syracuseStep 280817 = 210613) B210613
theorem B149747 : Blo 123787 149747 := bstep (se 1 (by rfl) ⟨112310, by rfl⟩ : syracuseStep 149747 = 224621) B224621
theorem B280835 : Blo 123787 280835 := bstep (se 1 (by rfl) ⟨210626, by rfl⟩ : syracuseStep 280835 = 421253) B421253
theorem B215345 : Blo 123787 215345 := bstep (se 2 (by rfl) ⟨80754, by rfl⟩ : syracuseStep 215345 = 161509) B161509
theorem B641357 : Blo 123787 641357 := bstep (se 3 (by rfl) ⟨120254, by rfl⟩ : syracuseStep 641357 = 240509) B240509
theorem B805261 : Blo 123787 805261 := bstep (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) B301973
theorem B215473 : Blo 123787 215473 := bstep (se 2 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 215473 = 161605) B161605
theorem B215507 : Blo 123787 215507 := bstep (se 1 (by rfl) ⟨161630, by rfl⟩ : syracuseStep 215507 = 323261) B323261
theorem B281105 : Blo 123787 281105 := bstep (se 2 (by rfl) ⟨105414, by rfl⟩ : syracuseStep 281105 = 210829) B210829
theorem B281123 : Blo 123787 281123 := bstep (se 1 (by rfl) ⟨210842, by rfl⟩ : syracuseStep 281123 = 421685) B421685
theorem B215635 : Blo 123787 215635 := bstep (se 1 (by rfl) ⟨161726, by rfl⟩ : syracuseStep 215635 = 323453) B323453
theorem B608867 : Blo 123787 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B477859 : Blo 123787 477859 := bstep (se 1 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 477859 = 716789) B716789
theorem B281393 : Blo 123787 281393 := bstep (se 2 (by rfl) ⟨105522, by rfl⟩ : syracuseStep 281393 = 211045) B211045
theorem B281411 : Blo 123787 281411 := bstep (se 1 (by rfl) ⟨211058, by rfl⟩ : syracuseStep 281411 = 422117) B422117
theorem B543779 : Blo 123787 543779 := bstep (se 1 (by rfl) ⟨407834, by rfl⟩ : syracuseStep 543779 = 815669) B815669
theorem B281681 : Blo 123787 281681 := bstep (se 2 (by rfl) ⟨105630, by rfl⟩ : syracuseStep 281681 = 211261) B211261
theorem B281699 : Blo 123787 281699 := bstep (se 1 (by rfl) ⟨211274, by rfl⟩ : syracuseStep 281699 = 422549) B422549
theorem B314513 : Blo 123787 314513 := bstep (se 2 (by rfl) ⟨117942, by rfl⟩ : syracuseStep 314513 = 235885) B235885
theorem B314563 : Blo 123787 314563 := bstep (se 1 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 314563 = 471845) B471845
theorem B314705 : Blo 123787 314705 := bstep (se 2 (by rfl) ⟨118014, by rfl⟩ : syracuseStep 314705 = 236029) B236029
theorem B511331 : Blo 123787 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B281969 : Blo 123787 281969 := bstep (se 2 (by rfl) ⟨105738, by rfl⟩ : syracuseStep 281969 = 211477) B211477
theorem B281987 : Blo 123787 281987 := bstep (se 1 (by rfl) ⟨211490, by rfl⟩ : syracuseStep 281987 = 422981) B422981
theorem B609713 : Blo 123787 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B282257 : Blo 123787 282257 := bstep (se 2 (by rfl) ⟨105846, by rfl⟩ : syracuseStep 282257 = 211693) B211693
theorem B282275 : Blo 123787 282275 := bstep (se 1 (by rfl) ⟨211706, by rfl⟩ : syracuseStep 282275 = 423413) B423413
theorem B282545 : Blo 123787 282545 := bstep (se 2 (by rfl) ⟨105954, by rfl⟩ : syracuseStep 282545 = 211909) B211909
theorem B282563 : Blo 123787 282563 := bstep (se 1 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 282563 = 423845) B423845
theorem B708749 : Blo 123787 708749 := bstep (se 3 (by rfl) ⟨132890, by rfl⟩ : syracuseStep 708749 = 265781) B265781
theorem B282833 : Blo 123787 282833 := bstep (se 2 (by rfl) ⟨106062, by rfl⟩ : syracuseStep 282833 = 212125) B212125
theorem B282851 : Blo 123787 282851 := bstep (se 1 (by rfl) ⟨212138, by rfl⟩ : syracuseStep 282851 = 424277) B424277
theorem B315697 : Blo 123787 315697 := bstep (se 2 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 315697 = 236773) B236773
theorem B283121 : Blo 123787 283121 := bstep (se 2 (by rfl) ⟨106170, by rfl⟩ : syracuseStep 283121 = 212341) B212341
theorem B283139 : Blo 123787 283139 := bstep (se 1 (by rfl) ⟨212354, by rfl⟩ : syracuseStep 283139 = 424709) B424709
theorem B315971 : Blo 123787 315971 := bstep (se 1 (by rfl) ⟨236978, by rfl⟩ : syracuseStep 315971 = 473957) B473957
theorem B152131 : Blo 123787 152131 := bstep (se 1 (by rfl) ⟨114098, by rfl⟩ : syracuseStep 152131 = 228197) B228197
theorem B840389 : Blo 123787 840389 := bstep (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) B157573
theorem B152275 : Blo 123787 152275 := bstep (se 1 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 152275 = 228413) B228413
theorem B316163 : Blo 123787 316163 := bstep (se 1 (by rfl) ⟨237122, by rfl⟩ : syracuseStep 316163 = 474245) B474245
theorem B283409 : Blo 123787 283409 := bstep (se 2 (by rfl) ⟨106278, by rfl⟩ : syracuseStep 283409 = 212557) B212557
theorem B283427 : Blo 123787 283427 := bstep (se 1 (by rfl) ⟨212570, by rfl⟩ : syracuseStep 283427 = 425141) B425141
theorem B152371 : Blo 123787 152371 := bstep (se 1 (by rfl) ⟨114278, by rfl⟩ : syracuseStep 152371 = 228557) B228557
theorem B1528645 : Blo 123787 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B480077 : Blo 123787 480077 := bstep (se 3 (by rfl) ⟨90014, by rfl⟩ : syracuseStep 480077 = 180029) B180029
theorem B709681 : Blo 123787 709681 := bstep (se 2 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 709681 = 532261) B532261
theorem B283697 : Blo 123787 283697 := bstep (se 2 (by rfl) ⟨106386, by rfl⟩ : syracuseStep 283697 = 212773) B212773
theorem B283715 : Blo 123787 283715 := bstep (se 1 (by rfl) ⟨212786, by rfl⟩ : syracuseStep 283715 = 425573) B425573
theorem B644273 : Blo 123787 644273 := bstep (se 2 (by rfl) ⟨241602, by rfl⟩ : syracuseStep 644273 = 483205) B483205
theorem B677105 : Blo 123787 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B152851 : Blo 123787 152851 := bstep (se 1 (by rfl) ⟨114638, by rfl⟩ : syracuseStep 152851 = 229277) B229277
theorem B185681 : Blo 123787 185681 := bstep (se 2 (by rfl) ⟨69630, by rfl⟩ : syracuseStep 185681 = 139261) B139261
theorem B283985 : Blo 123787 283985 := bstep (se 2 (by rfl) ⟨106494, by rfl⟩ : syracuseStep 283985 = 212989) B212989
theorem B185699 : Blo 123787 185699 := bstep (se 1 (by rfl) ⟨139274, by rfl⟩ : syracuseStep 185699 = 278549) B278549
theorem B284003 : Blo 123787 284003 := bstep (se 1 (by rfl) ⟨213002, by rfl⟩ : syracuseStep 284003 = 426005) B426005
theorem B447857 : Blo 123787 447857 := bstep (se 2 (by rfl) ⟨167946, by rfl⟩ : syracuseStep 447857 = 335893) B335893
theorem B185729 : Blo 123787 185729 := bstep (se 2 (by rfl) ⟨69648, by rfl⟩ : syracuseStep 185729 = 139297) B139297
theorem B775565 : Blo 123787 775565 := bstep (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) B290837
theorem B185747 : Blo 123787 185747 := bstep (se 1 (by rfl) ⟨139310, by rfl⟩ : syracuseStep 185747 = 278621) B278621
theorem B185777 : Blo 123787 185777 := bstep (se 2 (by rfl) ⟨69666, by rfl⟩ : syracuseStep 185777 = 139333) B139333
theorem B185795 : Blo 123787 185795 := bstep (se 1 (by rfl) ⟨139346, by rfl⟩ : syracuseStep 185795 = 278693) B278693
theorem B185825 : Blo 123787 185825 := bstep (se 2 (by rfl) ⟨69684, by rfl⟩ : syracuseStep 185825 = 139369) B139369
theorem B185843 : Blo 123787 185843 := bstep (se 1 (by rfl) ⟨139382, by rfl⟩ : syracuseStep 185843 = 278765) B278765
theorem B185873 : Blo 123787 185873 := bstep (se 2 (by rfl) ⟨69702, by rfl⟩ : syracuseStep 185873 = 139405) B139405
theorem B185891 : Blo 123787 185891 := bstep (se 1 (by rfl) ⟨139418, by rfl⟩ : syracuseStep 185891 = 278837) B278837
theorem B185921 : Blo 123787 185921 := bstep (se 2 (by rfl) ⟨69720, by rfl⟩ : syracuseStep 185921 = 139441) B139441
theorem B185939 : Blo 123787 185939 := bstep (se 1 (by rfl) ⟨139454, by rfl⟩ : syracuseStep 185939 = 278909) B278909
theorem B185969 : Blo 123787 185969 := bstep (se 2 (by rfl) ⟨69738, by rfl⟩ : syracuseStep 185969 = 139477) B139477
theorem B284273 : Blo 123787 284273 := bstep (se 2 (by rfl) ⟨106602, by rfl⟩ : syracuseStep 284273 = 213205) B213205
theorem B185987 : Blo 123787 185987 := bstep (se 1 (by rfl) ⟨139490, by rfl⟩ : syracuseStep 185987 = 278981) B278981
theorem B284291 : Blo 123787 284291 := bstep (se 1 (by rfl) ⟨213218, by rfl⟩ : syracuseStep 284291 = 426437) B426437
theorem B284305 : Blo 123787 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B186017 : Blo 123787 186017 := bstep (se 2 (by rfl) ⟨69756, by rfl⟩ : syracuseStep 186017 = 139513) B139513
theorem B317105 : Blo 123787 317105 := bstep (se 2 (by rfl) ⟨118914, by rfl⟩ : syracuseStep 317105 = 237829) B237829
theorem B218801 : Blo 123787 218801 := bstep (se 2 (by rfl) ⟨82050, by rfl⟩ : syracuseStep 218801 = 164101) B164101
theorem B186035 : Blo 123787 186035 := bstep (se 1 (by rfl) ⟨139526, by rfl⟩ : syracuseStep 186035 = 279053) B279053
theorem B186065 : Blo 123787 186065 := bstep (se 2 (by rfl) ⟨69774, by rfl⟩ : syracuseStep 186065 = 139549) B139549
theorem B186083 : Blo 123787 186083 := bstep (se 1 (by rfl) ⟨139562, by rfl⟩ : syracuseStep 186083 = 279125) B279125
theorem B317155 : Blo 123787 317155 := bstep (se 1 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 317155 = 475733) B475733
theorem B186113 : Blo 123787 186113 := bstep (se 2 (by rfl) ⟨69792, by rfl⟩ : syracuseStep 186113 = 139585) B139585
theorem B186131 : Blo 123787 186131 := bstep (se 1 (by rfl) ⟨139598, by rfl⟩ : syracuseStep 186131 = 279197) B279197
theorem B186161 : Blo 123787 186161 := bstep (se 2 (by rfl) ⟨69810, by rfl⟩ : syracuseStep 186161 = 139621) B139621
theorem B186179 : Blo 123787 186179 := bstep (se 1 (by rfl) ⟨139634, by rfl⟩ : syracuseStep 186179 = 279269) B279269
theorem B612173 : Blo 123787 612173 := bstep (se 3 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 612173 = 229565) B229565
theorem B186209 : Blo 123787 186209 := bstep (se 2 (by rfl) ⟨69828, by rfl⟩ : syracuseStep 186209 = 139657) B139657
theorem B317297 : Blo 123787 317297 := bstep (se 2 (by rfl) ⟨118986, by rfl⟩ : syracuseStep 317297 = 237973) B237973
theorem B186227 : Blo 123787 186227 := bstep (se 1 (by rfl) ⟨139670, by rfl⟩ : syracuseStep 186227 = 279341) B279341
theorem B186257 : Blo 123787 186257 := bstep (se 2 (by rfl) ⟨69846, by rfl⟩ : syracuseStep 186257 = 139693) B139693
theorem B284561 : Blo 123787 284561 := bstep (se 2 (by rfl) ⟨106710, by rfl⟩ : syracuseStep 284561 = 213421) B213421
theorem B186275 : Blo 123787 186275 := bstep (se 1 (by rfl) ⟨139706, by rfl⟩ : syracuseStep 186275 = 279413) B279413
theorem B284579 : Blo 123787 284579 := bstep (se 1 (by rfl) ⟨213434, by rfl⟩ : syracuseStep 284579 = 426869) B426869
theorem B186305 : Blo 123787 186305 := bstep (se 2 (by rfl) ⟨69864, by rfl⟩ : syracuseStep 186305 = 139729) B139729
theorem B382915 : Blo 123787 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B186323 : Blo 123787 186323 := bstep (se 1 (by rfl) ⟨139742, by rfl⟩ : syracuseStep 186323 = 279485) B279485
theorem B186353 : Blo 123787 186353 := bstep (se 2 (by rfl) ⟨69882, by rfl⟩ : syracuseStep 186353 = 139765) B139765
theorem B186371 : Blo 123787 186371 := bstep (se 1 (by rfl) ⟨139778, by rfl⟩ : syracuseStep 186371 = 279557) B279557
theorem B186401 : Blo 123787 186401 := bstep (se 2 (by rfl) ⟨69900, by rfl⟩ : syracuseStep 186401 = 139801) B139801
theorem B186419 : Blo 123787 186419 := bstep (se 1 (by rfl) ⟨139814, by rfl⟩ : syracuseStep 186419 = 279629) B279629
theorem B186449 : Blo 123787 186449 := bstep (se 2 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 186449 = 139837) B139837
theorem B186467 : Blo 123787 186467 := bstep (se 1 (by rfl) ⟨139850, by rfl⟩ : syracuseStep 186467 = 279701) B279701
theorem B186497 : Blo 123787 186497 := bstep (se 2 (by rfl) ⟨69936, by rfl⟩ : syracuseStep 186497 = 139873) B139873
theorem B186515 : Blo 123787 186515 := bstep (se 1 (by rfl) ⟨139886, by rfl⟩ : syracuseStep 186515 = 279773) B279773
theorem B186545 : Blo 123787 186545 := bstep (se 2 (by rfl) ⟨69954, by rfl⟩ : syracuseStep 186545 = 139909) B139909
theorem B284849 : Blo 123787 284849 := bstep (se 2 (by rfl) ⟨106818, by rfl⟩ : syracuseStep 284849 = 213637) B213637
theorem B219329 : Blo 123787 219329 := bstep (se 2 (by rfl) ⟨82248, by rfl⟩ : syracuseStep 219329 = 164497) B164497
theorem B186563 : Blo 123787 186563 := bstep (se 1 (by rfl) ⟨139922, by rfl⟩ : syracuseStep 186563 = 279845) B279845
theorem B284867 : Blo 123787 284867 := bstep (se 1 (by rfl) ⟨213650, by rfl⟩ : syracuseStep 284867 = 427301) B427301
theorem B186593 : Blo 123787 186593 := bstep (se 2 (by rfl) ⟨69972, by rfl⟩ : syracuseStep 186593 = 139945) B139945
theorem B448739 : Blo 123787 448739 := bstep (se 1 (by rfl) ⟨336554, by rfl⟩ : syracuseStep 448739 = 673109) B673109
theorem B186611 : Blo 123787 186611 := bstep (se 1 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 186611 = 279917) B279917
theorem B252163 : Blo 123787 252163 := bstep (se 1 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 252163 = 378245) B378245
theorem B186641 : Blo 123787 186641 := bstep (se 2 (by rfl) ⟨69990, by rfl⟩ : syracuseStep 186641 = 139981) B139981
theorem B186659 : Blo 123787 186659 := bstep (se 1 (by rfl) ⟨139994, by rfl⟩ : syracuseStep 186659 = 279989) B279989
theorem B186689 : Blo 123787 186689 := bstep (se 2 (by rfl) ⟨70008, by rfl⟩ : syracuseStep 186689 = 140017) B140017
theorem B186707 : Blo 123787 186707 := bstep (se 1 (by rfl) ⟨140030, by rfl⟩ : syracuseStep 186707 = 280061) B280061
theorem B186737 : Blo 123787 186737 := bstep (se 2 (by rfl) ⟨70026, by rfl⟩ : syracuseStep 186737 = 140053) B140053
theorem B186755 : Blo 123787 186755 := bstep (se 1 (by rfl) ⟨140066, by rfl⟩ : syracuseStep 186755 = 280133) B280133
theorem B154003 : Blo 123787 154003 := bstep (se 1 (by rfl) ⟨115502, by rfl⟩ : syracuseStep 154003 = 231005) B231005
theorem B186785 : Blo 123787 186785 := bstep (se 2 (by rfl) ⟨70044, by rfl⟩ : syracuseStep 186785 = 140089) B140089
theorem B186803 : Blo 123787 186803 := bstep (se 1 (by rfl) ⟨140102, by rfl⟩ : syracuseStep 186803 = 280205) B280205
theorem B186833 : Blo 123787 186833 := bstep (se 2 (by rfl) ⟨70062, by rfl⟩ : syracuseStep 186833 = 140125) B140125
theorem B285137 : Blo 123787 285137 := bstep (se 2 (by rfl) ⟨106926, by rfl⟩ : syracuseStep 285137 = 213853) B213853
theorem B186851 : Blo 123787 186851 := bstep (se 1 (by rfl) ⟨140138, by rfl⟩ : syracuseStep 186851 = 280277) B280277
theorem B711139 : Blo 123787 711139 := bstep (se 1 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 711139 = 1066709) B1066709
theorem B285155 : Blo 123787 285155 := bstep (se 1 (by rfl) ⟨213866, by rfl⟩ : syracuseStep 285155 = 427733) B427733
theorem B186881 : Blo 123787 186881 := bstep (se 2 (by rfl) ⟨70080, by rfl⟩ : syracuseStep 186881 = 140161) B140161
theorem B186899 : Blo 123787 186899 := bstep (se 1 (by rfl) ⟨140174, by rfl⟩ : syracuseStep 186899 = 280349) B280349
theorem B186929 : Blo 123787 186929 := bstep (se 2 (by rfl) ⟨70098, by rfl⟩ : syracuseStep 186929 = 140197) B140197
theorem B186947 : Blo 123787 186947 := bstep (se 1 (by rfl) ⟨140210, by rfl⟩ : syracuseStep 186947 = 280421) B280421
theorem B186977 : Blo 123787 186977 := bstep (se 2 (by rfl) ⟨70116, by rfl⟩ : syracuseStep 186977 = 140233) B140233
theorem B645731 : Blo 123787 645731 := bstep (se 1 (by rfl) ⟨484298, by rfl⟩ : syracuseStep 645731 = 968597) B968597
theorem B186995 : Blo 123787 186995 := bstep (se 1 (by rfl) ⟨140246, by rfl⟩ : syracuseStep 186995 = 280493) B280493
theorem B2939533 : Blo 123787 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B187025 : Blo 123787 187025 := bstep (se 2 (by rfl) ⟨70134, by rfl⟩ : syracuseStep 187025 = 140269) B140269
theorem B187043 : Blo 123787 187043 := bstep (se 1 (by rfl) ⟨140282, by rfl⟩ : syracuseStep 187043 = 280565) B280565
theorem B187073 : Blo 123787 187073 := bstep (se 2 (by rfl) ⟨70152, by rfl⟩ : syracuseStep 187073 = 140305) B140305
theorem B809669 : Blo 123787 809669 := bstep (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) B151813
theorem B187091 : Blo 123787 187091 := bstep (se 1 (by rfl) ⟨140318, by rfl⟩ : syracuseStep 187091 = 280637) B280637
theorem B187121 : Blo 123787 187121 := bstep (se 2 (by rfl) ⟨70170, by rfl⟩ : syracuseStep 187121 = 140341) B140341
theorem B285425 : Blo 123787 285425 := bstep (se 2 (by rfl) ⟨107034, by rfl⟩ : syracuseStep 285425 = 214069) B214069
theorem B187139 : Blo 123787 187139 := bstep (se 1 (by rfl) ⟨140354, by rfl⟩ : syracuseStep 187139 = 280709) B280709
theorem B285443 : Blo 123787 285443 := bstep (se 1 (by rfl) ⟨214082, by rfl⟩ : syracuseStep 285443 = 428165) B428165
theorem B187169 : Blo 123787 187169 := bstep (se 2 (by rfl) ⟨70188, by rfl⟩ : syracuseStep 187169 = 140377) B140377
theorem B187187 : Blo 123787 187187 := bstep (se 1 (by rfl) ⟨140390, by rfl⟩ : syracuseStep 187187 = 280781) B280781
theorem B187217 : Blo 123787 187217 := bstep (se 2 (by rfl) ⟨70206, by rfl⟩ : syracuseStep 187217 = 140413) B140413
theorem B318289 : Blo 123787 318289 := bstep (se 2 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 318289 = 238717) B238717
theorem B187235 : Blo 123787 187235 := bstep (se 1 (by rfl) ⟨140426, by rfl⟩ : syracuseStep 187235 = 280853) B280853
theorem B187265 : Blo 123787 187265 := bstep (se 2 (by rfl) ⟨70224, by rfl⟩ : syracuseStep 187265 = 140449) B140449
theorem B187283 : Blo 123787 187283 := bstep (se 1 (by rfl) ⟨140462, by rfl⟩ : syracuseStep 187283 = 280925) B280925
theorem B187313 : Blo 123787 187313 := bstep (se 2 (by rfl) ⟨70242, by rfl⟩ : syracuseStep 187313 = 140485) B140485
theorem B187331 : Blo 123787 187331 := bstep (se 1 (by rfl) ⟨140498, by rfl⟩ : syracuseStep 187331 = 280997) B280997
theorem B187361 : Blo 123787 187361 := bstep (se 2 (by rfl) ⟨70260, by rfl⟩ : syracuseStep 187361 = 140521) B140521
theorem B711665 : Blo 123787 711665 := bstep (se 2 (by rfl) ⟨266874, by rfl⟩ : syracuseStep 711665 = 533749) B533749
theorem B187379 : Blo 123787 187379 := bstep (se 1 (by rfl) ⟨140534, by rfl⟩ : syracuseStep 187379 = 281069) B281069
theorem B187409 : Blo 123787 187409 := bstep (se 2 (by rfl) ⟨70278, by rfl⟩ : syracuseStep 187409 = 140557) B140557
theorem B285713 : Blo 123787 285713 := bstep (se 2 (by rfl) ⟨107142, by rfl⟩ : syracuseStep 285713 = 214285) B214285
theorem B187427 : Blo 123787 187427 := bstep (se 1 (by rfl) ⟨140570, by rfl⟩ : syracuseStep 187427 = 281141) B281141
theorem B285731 : Blo 123787 285731 := bstep (se 1 (by rfl) ⟨214298, by rfl⟩ : syracuseStep 285731 = 428597) B428597
theorem B187457 : Blo 123787 187457 := bstep (se 2 (by rfl) ⟨70296, by rfl⟩ : syracuseStep 187457 = 140593) B140593
theorem B187475 : Blo 123787 187475 := bstep (se 1 (by rfl) ⟨140606, by rfl⟩ : syracuseStep 187475 = 281213) B281213
theorem B318563 : Blo 123787 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B187505 : Blo 123787 187505 := bstep (se 2 (by rfl) ⟨70314, by rfl⟩ : syracuseStep 187505 = 140629) B140629
theorem B187523 : Blo 123787 187523 := bstep (se 1 (by rfl) ⟨140642, by rfl⟩ : syracuseStep 187523 = 281285) B281285
theorem B187553 : Blo 123787 187553 := bstep (se 2 (by rfl) ⟨70332, by rfl⟩ : syracuseStep 187553 = 140665) B140665
theorem B187571 : Blo 123787 187571 := bstep (se 1 (by rfl) ⟨140678, by rfl⟩ : syracuseStep 187571 = 281357) B281357
theorem B187601 : Blo 123787 187601 := bstep (se 2 (by rfl) ⟨70350, by rfl⟩ : syracuseStep 187601 = 140701) B140701
theorem B187619 : Blo 123787 187619 := bstep (se 1 (by rfl) ⟨140714, by rfl⟩ : syracuseStep 187619 = 281429) B281429
theorem B1727729 : Blo 123787 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B187649 : Blo 123787 187649 := bstep (se 2 (by rfl) ⟨70368, by rfl⟩ : syracuseStep 187649 = 140737) B140737
theorem B1072397 : Blo 123787 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B187667 : Blo 123787 187667 := bstep (se 1 (by rfl) ⟨140750, by rfl⟩ : syracuseStep 187667 = 281501) B281501
theorem B318755 : Blo 123787 318755 := bstep (se 1 (by rfl) ⟨239066, by rfl⟩ : syracuseStep 318755 = 478133) B478133
theorem B187697 : Blo 123787 187697 := bstep (se 2 (by rfl) ⟨70386, by rfl⟩ : syracuseStep 187697 = 140773) B140773
theorem B286001 : Blo 123787 286001 := bstep (se 2 (by rfl) ⟨107250, by rfl⟩ : syracuseStep 286001 = 214501) B214501
theorem B187715 : Blo 123787 187715 := bstep (se 1 (by rfl) ⟨140786, by rfl⟩ : syracuseStep 187715 = 281573) B281573
theorem B286019 : Blo 123787 286019 := bstep (se 1 (by rfl) ⟨214514, by rfl⟩ : syracuseStep 286019 = 429029) B429029
theorem B941381 : Blo 123787 941381 := bstep (se 4 (by rfl) ⟨88254, by rfl⟩ : syracuseStep 941381 = 176509) B176509
theorem B187745 : Blo 123787 187745 := bstep (se 2 (by rfl) ⟨70404, by rfl⟩ : syracuseStep 187745 = 140809) B140809
theorem B187763 : Blo 123787 187763 := bstep (se 1 (by rfl) ⟨140822, by rfl⟩ : syracuseStep 187763 = 281645) B281645
theorem B646541 : Blo 123787 646541 := bstep (se 3 (by rfl) ⟨121226, by rfl⟩ : syracuseStep 646541 = 242453) B242453
theorem B187793 : Blo 123787 187793 := bstep (se 2 (by rfl) ⟨70422, by rfl⟩ : syracuseStep 187793 = 140845) B140845
theorem B187811 : Blo 123787 187811 := bstep (se 1 (by rfl) ⟨140858, by rfl⟩ : syracuseStep 187811 = 281717) B281717
theorem B187841 : Blo 123787 187841 := bstep (se 2 (by rfl) ⟨70440, by rfl⟩ : syracuseStep 187841 = 140881) B140881
theorem B187859 : Blo 123787 187859 := bstep (se 1 (by rfl) ⟨140894, by rfl⟩ : syracuseStep 187859 = 281789) B281789
theorem B187889 : Blo 123787 187889 := bstep (se 2 (by rfl) ⟨70458, by rfl⟩ : syracuseStep 187889 = 140917) B140917
theorem B187907 : Blo 123787 187907 := bstep (se 1 (by rfl) ⟨140930, by rfl⟩ : syracuseStep 187907 = 281861) B281861
theorem B187937 : Blo 123787 187937 := bstep (se 2 (by rfl) ⟨70476, by rfl⟩ : syracuseStep 187937 = 140953) B140953
theorem B187955 : Blo 123787 187955 := bstep (se 1 (by rfl) ⟨140966, by rfl⟩ : syracuseStep 187955 = 281933) B281933
theorem B187985 : Blo 123787 187985 := bstep (se 2 (by rfl) ⟨70494, by rfl⟩ : syracuseStep 187985 = 140989) B140989
theorem B286289 : Blo 123787 286289 := bstep (se 2 (by rfl) ⟨107358, by rfl⟩ : syracuseStep 286289 = 214717) B214717
theorem B188003 : Blo 123787 188003 := bstep (se 1 (by rfl) ⟨141002, by rfl⟩ : syracuseStep 188003 = 282005) B282005
theorem B286307 : Blo 123787 286307 := bstep (se 1 (by rfl) ⟨214730, by rfl⟩ : syracuseStep 286307 = 429461) B429461
theorem B188033 : Blo 123787 188033 := bstep (se 2 (by rfl) ⟨70512, by rfl⟩ : syracuseStep 188033 = 141025) B141025
theorem B188051 : Blo 123787 188051 := bstep (se 1 (by rfl) ⟨141038, by rfl⟩ : syracuseStep 188051 = 282077) B282077
theorem B188081 : Blo 123787 188081 := bstep (se 2 (by rfl) ⟨70530, by rfl⟩ : syracuseStep 188081 = 141061) B141061
theorem B482993 : Blo 123787 482993 := bstep (se 2 (by rfl) ⟨181122, by rfl⟩ : syracuseStep 482993 = 362245) B362245
theorem B188099 : Blo 123787 188099 := bstep (se 1 (by rfl) ⟨141074, by rfl⟩ : syracuseStep 188099 = 282149) B282149
theorem B188129 : Blo 123787 188129 := bstep (se 2 (by rfl) ⟨70548, by rfl⟩ : syracuseStep 188129 = 141097) B141097
theorem B188147 : Blo 123787 188147 := bstep (se 1 (by rfl) ⟨141110, by rfl⟩ : syracuseStep 188147 = 282221) B282221
theorem B188177 : Blo 123787 188177 := bstep (se 2 (by rfl) ⟨70566, by rfl⟩ : syracuseStep 188177 = 141133) B141133
theorem B188195 : Blo 123787 188195 := bstep (se 1 (by rfl) ⟨141146, by rfl⟩ : syracuseStep 188195 = 282293) B282293
theorem B188225 : Blo 123787 188225 := bstep (se 2 (by rfl) ⟨70584, by rfl⟩ : syracuseStep 188225 = 141169) B141169
theorem B188243 : Blo 123787 188243 := bstep (se 1 (by rfl) ⟨141182, by rfl⟩ : syracuseStep 188243 = 282365) B282365
theorem B188273 : Blo 123787 188273 := bstep (se 2 (by rfl) ⟨70602, by rfl⟩ : syracuseStep 188273 = 141205) B141205
theorem B286577 : Blo 123787 286577 := bstep (se 2 (by rfl) ⟨107466, by rfl⟩ : syracuseStep 286577 = 214933) B214933
theorem B188291 : Blo 123787 188291 := bstep (se 1 (by rfl) ⟨141218, by rfl⟩ : syracuseStep 188291 = 282437) B282437
theorem B286595 : Blo 123787 286595 := bstep (se 1 (by rfl) ⟨214946, by rfl⟩ : syracuseStep 286595 = 429893) B429893
theorem B188321 : Blo 123787 188321 := bstep (se 2 (by rfl) ⟨70620, by rfl⟩ : syracuseStep 188321 = 141241) B141241
theorem B450481 : Blo 123787 450481 := bstep (se 2 (by rfl) ⟨168930, by rfl⟩ : syracuseStep 450481 = 337861) B337861
theorem B188339 : Blo 123787 188339 := bstep (se 1 (by rfl) ⟨141254, by rfl⟩ : syracuseStep 188339 = 282509) B282509
theorem B188369 : Blo 123787 188369 := bstep (se 2 (by rfl) ⟨70638, by rfl⟩ : syracuseStep 188369 = 141277) B141277
theorem B188387 : Blo 123787 188387 := bstep (se 1 (by rfl) ⟨141290, by rfl⟩ : syracuseStep 188387 = 282581) B282581
theorem B188417 : Blo 123787 188417 := bstep (se 2 (by rfl) ⟨70656, by rfl⟩ : syracuseStep 188417 = 141313) B141313
theorem B188435 : Blo 123787 188435 := bstep (se 1 (by rfl) ⟨141326, by rfl⟩ : syracuseStep 188435 = 282653) B282653
theorem B188465 : Blo 123787 188465 := bstep (se 2 (by rfl) ⟨70674, by rfl⟩ : syracuseStep 188465 = 141349) B141349
theorem B188483 : Blo 123787 188483 := bstep (se 1 (by rfl) ⟨141362, by rfl⟩ : syracuseStep 188483 = 282725) B282725
theorem B188513 : Blo 123787 188513 := bstep (se 2 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 188513 = 141385) B141385
theorem B417905 : Blo 123787 417905 := bstep (se 2 (by rfl) ⟨156714, by rfl⟩ : syracuseStep 417905 = 313429) B313429
theorem B188531 : Blo 123787 188531 := bstep (se 1 (by rfl) ⟨141398, by rfl⟩ : syracuseStep 188531 = 282797) B282797
theorem B1532045 : Blo 123787 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B188561 : Blo 123787 188561 := bstep (se 2 (by rfl) ⟨70710, by rfl⟩ : syracuseStep 188561 = 141421) B141421
theorem B286865 : Blo 123787 286865 := bstep (se 2 (by rfl) ⟨107574, by rfl⟩ : syracuseStep 286865 = 215149) B215149
theorem B188579 : Blo 123787 188579 := bstep (se 1 (by rfl) ⟨141434, by rfl⟩ : syracuseStep 188579 = 282869) B282869
theorem B286883 : Blo 123787 286883 := bstep (se 1 (by rfl) ⟨215162, by rfl⟩ : syracuseStep 286883 = 430325) B430325
theorem B188609 : Blo 123787 188609 := bstep (se 2 (by rfl) ⟨70728, by rfl⟩ : syracuseStep 188609 = 141457) B141457
theorem B319697 : Blo 123787 319697 := bstep (se 2 (by rfl) ⟨119886, by rfl⟩ : syracuseStep 319697 = 239773) B239773
theorem B188627 : Blo 123787 188627 := bstep (se 1 (by rfl) ⟨141470, by rfl⟩ : syracuseStep 188627 = 282941) B282941
theorem B188657 : Blo 123787 188657 := bstep (se 2 (by rfl) ⟨70746, by rfl⟩ : syracuseStep 188657 = 141493) B141493
theorem B188675 : Blo 123787 188675 := bstep (se 1 (by rfl) ⟨141506, by rfl⟩ : syracuseStep 188675 = 283013) B283013
theorem B319747 : Blo 123787 319747 := bstep (se 1 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 319747 = 479621) B479621
theorem B188705 : Blo 123787 188705 := bstep (se 2 (by rfl) ⟨70764, by rfl⟩ : syracuseStep 188705 = 141529) B141529
theorem B188723 : Blo 123787 188723 := bstep (se 1 (by rfl) ⟨141542, by rfl⟩ : syracuseStep 188723 = 283085) B283085
theorem B188753 : Blo 123787 188753 := bstep (se 2 (by rfl) ⟨70782, by rfl⟩ : syracuseStep 188753 = 141565) B141565
theorem B811363 : Blo 123787 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B188771 : Blo 123787 188771 := bstep (se 1 (by rfl) ⟨141578, by rfl⟩ : syracuseStep 188771 = 283157) B283157
theorem B188801 : Blo 123787 188801 := bstep (se 2 (by rfl) ⟨70800, by rfl⟩ : syracuseStep 188801 = 141601) B141601
theorem B319889 : Blo 123787 319889 := bstep (se 2 (by rfl) ⟨119958, by rfl⟩ : syracuseStep 319889 = 239917) B239917
theorem B188819 : Blo 123787 188819 := bstep (se 1 (by rfl) ⟨141614, by rfl⟩ : syracuseStep 188819 = 283229) B283229
theorem B713123 : Blo 123787 713123 := bstep (se 1 (by rfl) ⟨534842, by rfl⟩ : syracuseStep 713123 = 1069685) B1069685
theorem B188849 : Blo 123787 188849 := bstep (se 2 (by rfl) ⟨70818, by rfl⟩ : syracuseStep 188849 = 141637) B141637
theorem B287153 : Blo 123787 287153 := bstep (se 2 (by rfl) ⟨107682, by rfl⟩ : syracuseStep 287153 = 215365) B215365
theorem B188867 : Blo 123787 188867 := bstep (se 1 (by rfl) ⟨141650, by rfl⟩ : syracuseStep 188867 = 283301) B283301
theorem B287171 : Blo 123787 287171 := bstep (se 1 (by rfl) ⟨215378, by rfl⟩ : syracuseStep 287171 = 430757) B430757
theorem B188897 : Blo 123787 188897 := bstep (se 2 (by rfl) ⟨70836, by rfl⟩ : syracuseStep 188897 = 141673) B141673
theorem B188915 : Blo 123787 188915 := bstep (se 1 (by rfl) ⟨141686, by rfl⟩ : syracuseStep 188915 = 283373) B283373
theorem B188945 : Blo 123787 188945 := bstep (se 2 (by rfl) ⟨70854, by rfl⟩ : syracuseStep 188945 = 141709) B141709
theorem B188963 : Blo 123787 188963 := bstep (se 1 (by rfl) ⟨141722, by rfl⟩ : syracuseStep 188963 = 283445) B283445
theorem B188993 : Blo 123787 188993 := bstep (se 2 (by rfl) ⟨70872, by rfl⟩ : syracuseStep 188993 = 141745) B141745
theorem B189011 : Blo 123787 189011 := bstep (se 1 (by rfl) ⟨141758, by rfl⟩ : syracuseStep 189011 = 283517) B283517
theorem B811619 : Blo 123787 811619 := bstep (se 1 (by rfl) ⟨608714, by rfl⟩ : syracuseStep 811619 = 1217429) B1217429
theorem B189041 : Blo 123787 189041 := bstep (se 2 (by rfl) ⟨70890, by rfl⟩ : syracuseStep 189041 = 141781) B141781
theorem B189059 : Blo 123787 189059 := bstep (se 1 (by rfl) ⟨141794, by rfl⟩ : syracuseStep 189059 = 283589) B283589
theorem B418445 : Blo 123787 418445 := bstep (se 3 (by rfl) ⟨78458, by rfl⟩ : syracuseStep 418445 = 156917) B156917
theorem B189089 : Blo 123787 189089 := bstep (se 2 (by rfl) ⟨70908, by rfl⟩ : syracuseStep 189089 = 141817) B141817
theorem B189107 : Blo 123787 189107 := bstep (se 1 (by rfl) ⟨141830, by rfl⟩ : syracuseStep 189107 = 283661) B283661
theorem B418499 : Blo 123787 418499 := bstep (se 1 (by rfl) ⟨313874, by rfl⟩ : syracuseStep 418499 = 627749) B627749
theorem B352973 : Blo 123787 352973 := bstep (se 3 (by rfl) ⟨66182, by rfl⟩ : syracuseStep 352973 = 132365) B132365
theorem B189137 : Blo 123787 189137 := bstep (se 2 (by rfl) ⟨70926, by rfl⟩ : syracuseStep 189137 = 141853) B141853
theorem B287441 : Blo 123787 287441 := bstep (se 2 (by rfl) ⟨107790, by rfl⟩ : syracuseStep 287441 = 215581) B215581
theorem B189155 : Blo 123787 189155 := bstep (se 1 (by rfl) ⟨141866, by rfl⟩ : syracuseStep 189155 = 283733) B283733
theorem B287459 : Blo 123787 287459 := bstep (se 1 (by rfl) ⟨215594, by rfl⟩ : syracuseStep 287459 = 431189) B431189
theorem B189185 : Blo 123787 189185 := bstep (se 2 (by rfl) ⟨70944, by rfl⟩ : syracuseStep 189185 = 141889) B141889
theorem B189203 : Blo 123787 189203 := bstep (se 1 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 189203 = 283805) B283805
theorem B189233 : Blo 123787 189233 := bstep (se 2 (by rfl) ⟨70962, by rfl⟩ : syracuseStep 189233 = 141925) B141925
theorem B189251 : Blo 123787 189251 := bstep (se 1 (by rfl) ⟨141938, by rfl⟩ : syracuseStep 189251 = 283877) B283877
theorem B189281 : Blo 123787 189281 := bstep (se 2 (by rfl) ⟨70980, by rfl⟩ : syracuseStep 189281 = 141961) B141961
theorem B189299 : Blo 123787 189299 := bstep (se 1 (by rfl) ⟨141974, by rfl⟩ : syracuseStep 189299 = 283949) B283949
theorem B353155 : Blo 123787 353155 := bstep (se 1 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 353155 = 529733) B529733
theorem B189329 : Blo 123787 189329 := bstep (se 2 (by rfl) ⟨70998, by rfl⟩ : syracuseStep 189329 = 141997) B141997
theorem B123795 : Blo 123787 123795 := bstep (se 1 (by rfl) ⟨92846, by rfl⟩ : syracuseStep 123795 = 185693) B185693
theorem B123811 : Blo 123787 123811 := bstep (se 1 (by rfl) ⟨92858, by rfl⟩ : syracuseStep 123811 = 185717) B185717
theorem B189347 : Blo 123787 189347 := bstep (se 1 (by rfl) ⟨142010, by rfl⟩ : syracuseStep 189347 = 284021) B284021
theorem B123827 : Blo 123787 123827 := bstep (se 1 (by rfl) ⟨92870, by rfl⟩ : syracuseStep 123827 = 185741) B185741
theorem B189377 : Blo 123787 189377 := bstep (se 2 (by rfl) ⟨71016, by rfl⟩ : syracuseStep 189377 = 142033) B142033
theorem B123843 : Blo 123787 123843 := bstep (se 1 (by rfl) ⟨92882, by rfl⟩ : syracuseStep 123843 = 185765) B185765
theorem B418769 : Blo 123787 418769 := bstep (se 2 (by rfl) ⟨157038, by rfl⟩ : syracuseStep 418769 = 314077) B314077
theorem B123859 : Blo 123787 123859 := bstep (se 1 (by rfl) ⟨92894, by rfl⟩ : syracuseStep 123859 = 185789) B185789
theorem B189395 : Blo 123787 189395 := bstep (se 1 (by rfl) ⟨142046, by rfl⟩ : syracuseStep 189395 = 284093) B284093
theorem B123875 : Blo 123787 123875 := bstep (se 1 (by rfl) ⟨92906, by rfl⟩ : syracuseStep 123875 = 185813) B185813
theorem B189425 : Blo 123787 189425 := bstep (se 2 (by rfl) ⟨71034, by rfl⟩ : syracuseStep 189425 = 142069) B142069
theorem B123891 : Blo 123787 123891 := bstep (se 1 (by rfl) ⟨92918, by rfl⟩ : syracuseStep 123891 = 185837) B185837
theorem B123907 : Blo 123787 123907 := bstep (se 1 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 123907 = 185861) B185861
theorem B189443 : Blo 123787 189443 := bstep (se 1 (by rfl) ⟨142082, by rfl⟩ : syracuseStep 189443 = 284165) B284165
theorem B123923 : Blo 123787 123923 := bstep (se 1 (by rfl) ⟨92942, by rfl⟩ : syracuseStep 123923 = 185885) B185885
theorem B189473 : Blo 123787 189473 := bstep (se 2 (by rfl) ⟨71052, by rfl⟩ : syracuseStep 189473 = 142105) B142105
theorem B123939 : Blo 123787 123939 := bstep (se 1 (by rfl) ⟨92954, by rfl⟩ : syracuseStep 123939 = 185909) B185909
theorem B353315 : Blo 123787 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B123955 : Blo 123787 123955 := bstep (se 1 (by rfl) ⟨92966, by rfl⟩ : syracuseStep 123955 = 185933) B185933
theorem B189491 : Blo 123787 189491 := bstep (se 1 (by rfl) ⟨142118, by rfl⟩ : syracuseStep 189491 = 284237) B284237
theorem B123971 : Blo 123787 123971 := bstep (se 1 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 123971 = 185957) B185957
theorem B189521 : Blo 123787 189521 := bstep (se 2 (by rfl) ⟨71070, by rfl⟩ : syracuseStep 189521 = 142141) B142141
theorem B156755 : Blo 123787 156755 := bstep (se 1 (by rfl) ⟨117566, by rfl⟩ : syracuseStep 156755 = 235133) B235133
theorem B123987 : Blo 123787 123987 := bstep (se 1 (by rfl) ⟨92990, by rfl⟩ : syracuseStep 123987 = 185981) B185981
theorem B124003 : Blo 123787 124003 := bstep (se 1 (by rfl) ⟨93002, by rfl⟩ : syracuseStep 124003 = 186005) B186005
theorem B189539 : Blo 123787 189539 := bstep (se 1 (by rfl) ⟨142154, by rfl⟩ : syracuseStep 189539 = 284309) B284309
theorem B484451 : Blo 123787 484451 := bstep (se 1 (by rfl) ⟨363338, by rfl⟩ : syracuseStep 484451 = 726677) B726677
theorem B124019 : Blo 123787 124019 := bstep (se 1 (by rfl) ⟨93014, by rfl⟩ : syracuseStep 124019 = 186029) B186029
theorem B189569 : Blo 123787 189569 := bstep (se 2 (by rfl) ⟨71088, by rfl⟩ : syracuseStep 189569 = 142177) B142177
theorem B124035 : Blo 123787 124035 := bstep (se 1 (by rfl) ⟨93026, by rfl⟩ : syracuseStep 124035 = 186053) B186053
theorem B124051 : Blo 123787 124051 := bstep (se 1 (by rfl) ⟨93038, by rfl⟩ : syracuseStep 124051 = 186077) B186077
theorem B189587 : Blo 123787 189587 := bstep (se 1 (by rfl) ⟨142190, by rfl⟩ : syracuseStep 189587 = 284381) B284381
theorem B124067 : Blo 123787 124067 := bstep (se 1 (by rfl) ⟨93050, by rfl⟩ : syracuseStep 124067 = 186101) B186101
theorem B189617 : Blo 123787 189617 := bstep (se 2 (by rfl) ⟨71106, by rfl⟩ : syracuseStep 189617 = 142213) B142213
theorem B124083 : Blo 123787 124083 := bstep (se 1 (by rfl) ⟨93062, by rfl⟩ : syracuseStep 124083 = 186125) B186125
theorem B124099 : Blo 123787 124099 := bstep (se 1 (by rfl) ⟨93074, by rfl⟩ : syracuseStep 124099 = 186149) B186149
theorem B189635 : Blo 123787 189635 := bstep (se 1 (by rfl) ⟨142226, by rfl⟩ : syracuseStep 189635 = 284453) B284453
theorem B124115 : Blo 123787 124115 := bstep (se 1 (by rfl) ⟨93086, by rfl⟩ : syracuseStep 124115 = 186173) B186173
theorem B189665 : Blo 123787 189665 := bstep (se 2 (by rfl) ⟨71124, by rfl⟩ : syracuseStep 189665 = 142249) B142249
theorem B124131 : Blo 123787 124131 := bstep (se 1 (by rfl) ⟨93098, by rfl⟩ : syracuseStep 124131 = 186197) B186197
theorem B124147 : Blo 123787 124147 := bstep (se 1 (by rfl) ⟨93110, by rfl⟩ : syracuseStep 124147 = 186221) B186221
theorem B189683 : Blo 123787 189683 := bstep (se 1 (by rfl) ⟨142262, by rfl⟩ : syracuseStep 189683 = 284525) B284525
theorem B124163 : Blo 123787 124163 := bstep (se 1 (by rfl) ⟨93122, by rfl⟩ : syracuseStep 124163 = 186245) B186245
theorem B189713 : Blo 123787 189713 := bstep (se 2 (by rfl) ⟨71142, by rfl⟩ : syracuseStep 189713 = 142285) B142285
theorem B124179 : Blo 123787 124179 := bstep (se 1 (by rfl) ⟨93134, by rfl⟩ : syracuseStep 124179 = 186269) B186269
theorem B124195 : Blo 123787 124195 := bstep (se 1 (by rfl) ⟨93146, by rfl⟩ : syracuseStep 124195 = 186293) B186293
theorem B189731 : Blo 123787 189731 := bstep (se 1 (by rfl) ⟨142298, by rfl⟩ : syracuseStep 189731 = 284597) B284597
theorem B124211 : Blo 123787 124211 := bstep (se 1 (by rfl) ⟨93158, by rfl⟩ : syracuseStep 124211 = 186317) B186317
theorem B2876725 : Blo 123787 2876725 := bstep (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) B269693
theorem B189761 : Blo 123787 189761 := bstep (se 2 (by rfl) ⟨71160, by rfl⟩ : syracuseStep 189761 = 142321) B142321
theorem B124227 : Blo 123787 124227 := bstep (se 1 (by rfl) ⟨93170, by rfl⟩ : syracuseStep 124227 = 186341) B186341
theorem B124243 : Blo 123787 124243 := bstep (se 1 (by rfl) ⟨93182, by rfl⟩ : syracuseStep 124243 = 186365) B186365
theorem B189779 : Blo 123787 189779 := bstep (se 1 (by rfl) ⟨142334, by rfl⟩ : syracuseStep 189779 = 284669) B284669
theorem B124259 : Blo 123787 124259 := bstep (se 1 (by rfl) ⟨93194, by rfl⟩ : syracuseStep 124259 = 186389) B186389
theorem B189809 : Blo 123787 189809 := bstep (se 2 (by rfl) ⟨71178, by rfl⟩ : syracuseStep 189809 = 142357) B142357
theorem B320881 : Blo 123787 320881 := bstep (se 2 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 320881 = 240661) B240661
theorem B124275 : Blo 123787 124275 := bstep (se 1 (by rfl) ⟨93206, by rfl⟩ : syracuseStep 124275 = 186413) B186413
theorem B124291 : Blo 123787 124291 := bstep (se 1 (by rfl) ⟨93218, by rfl⟩ : syracuseStep 124291 = 186437) B186437
theorem B189827 : Blo 123787 189827 := bstep (se 1 (by rfl) ⟨142370, by rfl⟩ : syracuseStep 189827 = 284741) B284741
theorem B124307 : Blo 123787 124307 := bstep (se 1 (by rfl) ⟨93230, by rfl⟩ : syracuseStep 124307 = 186461) B186461
theorem B189857 : Blo 123787 189857 := bstep (se 2 (by rfl) ⟨71196, by rfl⟩ : syracuseStep 189857 = 142393) B142393
theorem B124323 : Blo 123787 124323 := bstep (se 1 (by rfl) ⟨93242, by rfl⟩ : syracuseStep 124323 = 186485) B186485
theorem B124339 : Blo 123787 124339 := bstep (se 1 (by rfl) ⟨93254, by rfl⟩ : syracuseStep 124339 = 186509) B186509
theorem B189875 : Blo 123787 189875 := bstep (se 1 (by rfl) ⟨142406, by rfl⟩ : syracuseStep 189875 = 284813) B284813
theorem B124355 : Blo 123787 124355 := bstep (se 1 (by rfl) ⟨93266, by rfl⟩ : syracuseStep 124355 = 186533) B186533
theorem B189905 : Blo 123787 189905 := bstep (se 2 (by rfl) ⟨71214, by rfl⟩ : syracuseStep 189905 = 142429) B142429
theorem B124371 : Blo 123787 124371 := bstep (se 1 (by rfl) ⟨93278, by rfl⟩ : syracuseStep 124371 = 186557) B186557
theorem B124387 : Blo 123787 124387 := bstep (se 1 (by rfl) ⟨93290, by rfl⟩ : syracuseStep 124387 = 186581) B186581
theorem B189923 : Blo 123787 189923 := bstep (se 1 (by rfl) ⟨142442, by rfl⟩ : syracuseStep 189923 = 284885) B284885
theorem B419309 : Blo 123787 419309 := bstep (se 3 (by rfl) ⟨78620, by rfl⟩ : syracuseStep 419309 = 157241) B157241
theorem B124403 : Blo 123787 124403 := bstep (se 1 (by rfl) ⟨93302, by rfl⟩ : syracuseStep 124403 = 186605) B186605
theorem B189953 : Blo 123787 189953 := bstep (se 2 (by rfl) ⟨71232, by rfl⟩ : syracuseStep 189953 = 142465) B142465
theorem B124419 : Blo 123787 124419 := bstep (se 1 (by rfl) ⟨93314, by rfl⟩ : syracuseStep 124419 = 186629) B186629
theorem B124435 : Blo 123787 124435 := bstep (se 1 (by rfl) ⟨93326, by rfl⟩ : syracuseStep 124435 = 186653) B186653
theorem B189971 : Blo 123787 189971 := bstep (se 1 (by rfl) ⟨142478, by rfl⟩ : syracuseStep 189971 = 284957) B284957
theorem B419363 : Blo 123787 419363 := bstep (se 1 (by rfl) ⟨314522, by rfl⟩ : syracuseStep 419363 = 629045) B629045
theorem B124451 : Blo 123787 124451 := bstep (se 1 (by rfl) ⟨93338, by rfl⟩ : syracuseStep 124451 = 186677) B186677
theorem B190001 : Blo 123787 190001 := bstep (se 2 (by rfl) ⟨71250, by rfl⟩ : syracuseStep 190001 = 142501) B142501
theorem B124467 : Blo 123787 124467 := bstep (se 1 (by rfl) ⟨93350, by rfl⟩ : syracuseStep 124467 = 186701) B186701
theorem B124483 : Blo 123787 124483 := bstep (se 1 (by rfl) ⟨93362, by rfl⟩ : syracuseStep 124483 = 186725) B186725
theorem B190019 : Blo 123787 190019 := bstep (se 1 (by rfl) ⟨142514, by rfl⟩ : syracuseStep 190019 = 285029) B285029
theorem B124499 : Blo 123787 124499 := bstep (se 1 (by rfl) ⟨93374, by rfl⟩ : syracuseStep 124499 = 186749) B186749
theorem B190049 : Blo 123787 190049 := bstep (se 2 (by rfl) ⟨71268, by rfl⟩ : syracuseStep 190049 = 142537) B142537
theorem B124515 : Blo 123787 124515 := bstep (se 1 (by rfl) ⟨93386, by rfl⟩ : syracuseStep 124515 = 186773) B186773
theorem B124531 : Blo 123787 124531 := bstep (se 1 (by rfl) ⟨93398, by rfl⟩ : syracuseStep 124531 = 186797) B186797
theorem B190067 : Blo 123787 190067 := bstep (se 1 (by rfl) ⟨142550, by rfl⟩ : syracuseStep 190067 = 285101) B285101
theorem B124547 : Blo 123787 124547 := bstep (se 1 (by rfl) ⟨93410, by rfl⟩ : syracuseStep 124547 = 186821) B186821
theorem B321155 : Blo 123787 321155 := bstep (se 1 (by rfl) ⟨240866, by rfl⟩ : syracuseStep 321155 = 481733) B481733
theorem B190097 : Blo 123787 190097 := bstep (se 2 (by rfl) ⟨71286, by rfl⟩ : syracuseStep 190097 = 142573) B142573
theorem B124563 : Blo 123787 124563 := bstep (se 1 (by rfl) ⟨93422, by rfl⟩ : syracuseStep 124563 = 186845) B186845
theorem B124579 : Blo 123787 124579 := bstep (se 1 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 124579 = 186869) B186869
theorem B190115 : Blo 123787 190115 := bstep (se 1 (by rfl) ⟨142586, by rfl⟩ : syracuseStep 190115 = 285173) B285173
theorem B124595 : Blo 123787 124595 := bstep (se 1 (by rfl) ⟨93446, by rfl⟩ : syracuseStep 124595 = 186893) B186893
theorem B190145 : Blo 123787 190145 := bstep (se 2 (by rfl) ⟨71304, by rfl⟩ : syracuseStep 190145 = 142609) B142609
theorem B124611 : Blo 123787 124611 := bstep (se 1 (by rfl) ⟨93458, by rfl⟩ : syracuseStep 124611 = 186917) B186917
theorem B255683 : Blo 123787 255683 := bstep (se 1 (by rfl) ⟨191762, by rfl⟩ : syracuseStep 255683 = 383525) B383525
theorem B124627 : Blo 123787 124627 := bstep (se 1 (by rfl) ⟨93470, by rfl⟩ : syracuseStep 124627 = 186941) B186941
theorem B190163 : Blo 123787 190163 := bstep (se 1 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 190163 = 285245) B285245
theorem B124643 : Blo 123787 124643 := bstep (se 1 (by rfl) ⟨93482, by rfl⟩ : syracuseStep 124643 = 186965) B186965
theorem B190193 : Blo 123787 190193 := bstep (se 2 (by rfl) ⟨71322, by rfl⟩ : syracuseStep 190193 = 142645) B142645
theorem B124659 : Blo 123787 124659 := bstep (se 1 (by rfl) ⟨93494, by rfl⟩ : syracuseStep 124659 = 186989) B186989
theorem B124675 : Blo 123787 124675 := bstep (se 1 (by rfl) ⟨93506, by rfl⟩ : syracuseStep 124675 = 187013) B187013
theorem B190211 : Blo 123787 190211 := bstep (se 1 (by rfl) ⟨142658, by rfl⟩ : syracuseStep 190211 = 285317) B285317
theorem B157459 : Blo 123787 157459 := bstep (se 1 (by rfl) ⟨118094, by rfl⟩ : syracuseStep 157459 = 236189) B236189
theorem B124691 : Blo 123787 124691 := bstep (se 1 (by rfl) ⟨93518, by rfl⟩ : syracuseStep 124691 = 187037) B187037
theorem B190241 : Blo 123787 190241 := bstep (se 2 (by rfl) ⟨71340, by rfl⟩ : syracuseStep 190241 = 142681) B142681
theorem B124707 : Blo 123787 124707 := bstep (se 1 (by rfl) ⟨93530, by rfl⟩ : syracuseStep 124707 = 187061) B187061
theorem B419633 : Blo 123787 419633 := bstep (se 2 (by rfl) ⟨157362, by rfl⟩ : syracuseStep 419633 = 314725) B314725
theorem B124723 : Blo 123787 124723 := bstep (se 1 (by rfl) ⟨93542, by rfl⟩ : syracuseStep 124723 = 187085) B187085
theorem B190259 : Blo 123787 190259 := bstep (se 1 (by rfl) ⟨142694, by rfl⟩ : syracuseStep 190259 = 285389) B285389
theorem B124739 : Blo 123787 124739 := bstep (se 1 (by rfl) ⟨93554, by rfl⟩ : syracuseStep 124739 = 187109) B187109
theorem B321347 : Blo 123787 321347 := bstep (se 1 (by rfl) ⟨241010, by rfl⟩ : syracuseStep 321347 = 482021) B482021
theorem B452429 : Blo 123787 452429 := bstep (se 3 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 452429 = 169661) B169661
theorem B190289 : Blo 123787 190289 := bstep (se 2 (by rfl) ⟨71358, by rfl⟩ : syracuseStep 190289 = 142717) B142717
theorem B124755 : Blo 123787 124755 := bstep (se 1 (by rfl) ⟨93566, by rfl⟩ : syracuseStep 124755 = 187133) B187133
theorem B124771 : Blo 123787 124771 := bstep (se 1 (by rfl) ⟨93578, by rfl⟩ : syracuseStep 124771 = 187157) B187157
theorem B190307 : Blo 123787 190307 := bstep (se 1 (by rfl) ⟨142730, by rfl⟩ : syracuseStep 190307 = 285461) B285461
theorem B157555 : Blo 123787 157555 := bstep (se 1 (by rfl) ⟨118166, by rfl⟩ : syracuseStep 157555 = 236333) B236333
theorem B124787 : Blo 123787 124787 := bstep (se 1 (by rfl) ⟨93590, by rfl⟩ : syracuseStep 124787 = 187181) B187181
theorem B190337 : Blo 123787 190337 := bstep (se 2 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 190337 = 142753) B142753
theorem B124803 : Blo 123787 124803 := bstep (se 1 (by rfl) ⟨93602, by rfl⟩ : syracuseStep 124803 = 187205) B187205
theorem B124819 : Blo 123787 124819 := bstep (se 1 (by rfl) ⟨93614, by rfl⟩ : syracuseStep 124819 = 187229) B187229
theorem B190355 : Blo 123787 190355 := bstep (se 1 (by rfl) ⟨142766, by rfl⟩ : syracuseStep 190355 = 285533) B285533
theorem B124835 : Blo 123787 124835 := bstep (se 1 (by rfl) ⟨93626, by rfl⟩ : syracuseStep 124835 = 187253) B187253
theorem B190385 : Blo 123787 190385 := bstep (se 2 (by rfl) ⟨71394, by rfl⟩ : syracuseStep 190385 = 142789) B142789
theorem B124851 : Blo 123787 124851 := bstep (se 1 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 124851 = 187277) B187277
theorem B124867 : Blo 123787 124867 := bstep (se 1 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 124867 = 187301) B187301
theorem B190403 : Blo 123787 190403 := bstep (se 1 (by rfl) ⟨142802, by rfl⟩ : syracuseStep 190403 = 285605) B285605
theorem B124883 : Blo 123787 124883 := bstep (se 1 (by rfl) ⟨93662, by rfl⟩ : syracuseStep 124883 = 187325) B187325
theorem B190433 : Blo 123787 190433 := bstep (se 2 (by rfl) ⟨71412, by rfl⟩ : syracuseStep 190433 = 142825) B142825
theorem B124899 : Blo 123787 124899 := bstep (se 1 (by rfl) ⟨93674, by rfl⟩ : syracuseStep 124899 = 187349) B187349
theorem B124915 : Blo 123787 124915 := bstep (se 1 (by rfl) ⟨93686, by rfl⟩ : syracuseStep 124915 = 187373) B187373
theorem B190451 : Blo 123787 190451 := bstep (se 1 (by rfl) ⟨142838, by rfl⟩ : syracuseStep 190451 = 285677) B285677
theorem B124931 : Blo 123787 124931 := bstep (se 1 (by rfl) ⟨93698, by rfl⟩ : syracuseStep 124931 = 187397) B187397
theorem B288785 : Blo 123787 288785 := bstep (se 2 (by rfl) ⟨108294, by rfl⟩ : syracuseStep 288785 = 216589) B216589
theorem B190481 : Blo 123787 190481 := bstep (se 2 (by rfl) ⟨71430, by rfl⟩ : syracuseStep 190481 = 142861) B142861
theorem B124947 : Blo 123787 124947 := bstep (se 1 (by rfl) ⟨93710, by rfl⟩ : syracuseStep 124947 = 187421) B187421
theorem B124963 : Blo 123787 124963 := bstep (se 1 (by rfl) ⟨93722, by rfl⟩ : syracuseStep 124963 = 187445) B187445
theorem B518179 : Blo 123787 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B190499 : Blo 123787 190499 := bstep (se 1 (by rfl) ⟨142874, by rfl⟩ : syracuseStep 190499 = 285749) B285749
theorem B124979 : Blo 123787 124979 := bstep (se 1 (by rfl) ⟨93734, by rfl⟩ : syracuseStep 124979 = 187469) B187469
theorem B190529 : Blo 123787 190529 := bstep (se 2 (by rfl) ⟨71448, by rfl⟩ : syracuseStep 190529 = 142897) B142897
theorem B124995 : Blo 123787 124995 := bstep (se 1 (by rfl) ⟨93746, by rfl⟩ : syracuseStep 124995 = 187493) B187493
theorem B354385 : Blo 123787 354385 := bstep (se 2 (by rfl) ⟨132894, by rfl⟩ : syracuseStep 354385 = 265789) B265789
theorem B125011 : Blo 123787 125011 := bstep (se 1 (by rfl) ⟨93758, by rfl⟩ : syracuseStep 125011 = 187517) B187517
theorem B190547 : Blo 123787 190547 := bstep (se 1 (by rfl) ⟨142910, by rfl⟩ : syracuseStep 190547 = 285821) B285821
theorem B125027 : Blo 123787 125027 := bstep (se 1 (by rfl) ⟨93770, by rfl⟩ : syracuseStep 125027 = 187541) B187541
theorem B190577 : Blo 123787 190577 := bstep (se 2 (by rfl) ⟨71466, by rfl⟩ : syracuseStep 190577 = 142933) B142933
theorem B125043 : Blo 123787 125043 := bstep (se 1 (by rfl) ⟨93782, by rfl⟩ : syracuseStep 125043 = 187565) B187565
theorem B125059 : Blo 123787 125059 := bstep (se 1 (by rfl) ⟨93794, by rfl⟩ : syracuseStep 125059 = 187589) B187589
theorem B190595 : Blo 123787 190595 := bstep (se 1 (by rfl) ⟨142946, by rfl⟩ : syracuseStep 190595 = 285893) B285893
theorem B125075 : Blo 123787 125075 := bstep (se 1 (by rfl) ⟨93806, by rfl⟩ : syracuseStep 125075 = 187613) B187613
theorem B190625 : Blo 123787 190625 := bstep (se 2 (by rfl) ⟨71484, by rfl⟩ : syracuseStep 190625 = 142969) B142969
theorem B125091 : Blo 123787 125091 := bstep (se 1 (by rfl) ⟨93818, by rfl⟩ : syracuseStep 125091 = 187637) B187637
theorem B125107 : Blo 123787 125107 := bstep (se 1 (by rfl) ⟨93830, by rfl⟩ : syracuseStep 125107 = 187661) B187661
theorem B190643 : Blo 123787 190643 := bstep (se 1 (by rfl) ⟨142982, by rfl⟩ : syracuseStep 190643 = 285965) B285965
theorem B125123 : Blo 123787 125123 := bstep (se 1 (by rfl) ⟨93842, by rfl⟩ : syracuseStep 125123 = 187685) B187685
theorem B190673 : Blo 123787 190673 := bstep (se 2 (by rfl) ⟨71502, by rfl⟩ : syracuseStep 190673 = 143005) B143005
theorem B125139 : Blo 123787 125139 := bstep (se 1 (by rfl) ⟨93854, by rfl⟩ : syracuseStep 125139 = 187709) B187709
theorem B125155 : Blo 123787 125155 := bstep (se 1 (by rfl) ⟨93866, by rfl⟩ : syracuseStep 125155 = 187733) B187733
theorem B190691 : Blo 123787 190691 := bstep (se 1 (by rfl) ⟨143018, by rfl⟩ : syracuseStep 190691 = 286037) B286037
theorem B125171 : Blo 123787 125171 := bstep (se 1 (by rfl) ⟨93878, by rfl⟩ : syracuseStep 125171 = 187757) B187757
theorem B190721 : Blo 123787 190721 := bstep (se 2 (by rfl) ⟨71520, by rfl⟩ : syracuseStep 190721 = 143041) B143041
theorem B125187 : Blo 123787 125187 := bstep (se 1 (by rfl) ⟨93890, by rfl⟩ : syracuseStep 125187 = 187781) B187781
theorem B715013 : Blo 123787 715013 := bstep (se 4 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 715013 = 134065) B134065
theorem B125203 : Blo 123787 125203 := bstep (se 1 (by rfl) ⟨93902, by rfl⟩ : syracuseStep 125203 = 187805) B187805
theorem B190739 : Blo 123787 190739 := bstep (se 1 (by rfl) ⟨143054, by rfl⟩ : syracuseStep 190739 = 286109) B286109
theorem B125219 : Blo 123787 125219 := bstep (se 1 (by rfl) ⟨93914, by rfl⟩ : syracuseStep 125219 = 187829) B187829
theorem B190769 : Blo 123787 190769 := bstep (se 2 (by rfl) ⟨71538, by rfl⟩ : syracuseStep 190769 = 143077) B143077
theorem B125235 : Blo 123787 125235 := bstep (se 1 (by rfl) ⟨93926, by rfl⟩ : syracuseStep 125235 = 187853) B187853
theorem B125251 : Blo 123787 125251 := bstep (se 1 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 125251 = 187877) B187877
theorem B190787 : Blo 123787 190787 := bstep (se 1 (by rfl) ⟨143090, by rfl⟩ : syracuseStep 190787 = 286181) B286181
theorem B420173 : Blo 123787 420173 := bstep (se 3 (by rfl) ⟨78782, by rfl⟩ : syracuseStep 420173 = 157565) B157565
theorem B125267 : Blo 123787 125267 := bstep (se 1 (by rfl) ⟨93950, by rfl⟩ : syracuseStep 125267 = 187901) B187901
theorem B190817 : Blo 123787 190817 := bstep (se 2 (by rfl) ⟨71556, by rfl⟩ : syracuseStep 190817 = 143113) B143113
theorem B158051 : Blo 123787 158051 := bstep (se 1 (by rfl) ⟨118538, by rfl⟩ : syracuseStep 158051 = 237077) B237077
theorem B125283 : Blo 123787 125283 := bstep (se 1 (by rfl) ⟨93962, by rfl⟩ : syracuseStep 125283 = 187925) B187925
theorem B125299 : Blo 123787 125299 := bstep (se 1 (by rfl) ⟨93974, by rfl⟩ : syracuseStep 125299 = 187949) B187949
theorem B190835 : Blo 123787 190835 := bstep (se 1 (by rfl) ⟨143126, by rfl⟩ : syracuseStep 190835 = 286253) B286253
theorem B420227 : Blo 123787 420227 := bstep (se 1 (by rfl) ⟨315170, by rfl⟩ : syracuseStep 420227 = 630341) B630341
theorem B125315 : Blo 123787 125315 := bstep (se 1 (by rfl) ⟨93986, by rfl⟩ : syracuseStep 125315 = 187973) B187973
theorem B190865 : Blo 123787 190865 := bstep (se 2 (by rfl) ⟨71574, by rfl⟩ : syracuseStep 190865 = 143149) B143149
theorem B125331 : Blo 123787 125331 := bstep (se 1 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 125331 = 187997) B187997
theorem B125347 : Blo 123787 125347 := bstep (se 1 (by rfl) ⟨94010, by rfl⟩ : syracuseStep 125347 = 188021) B188021
theorem B190883 : Blo 123787 190883 := bstep (se 1 (by rfl) ⟨143162, by rfl⟩ : syracuseStep 190883 = 286325) B286325
theorem B125363 : Blo 123787 125363 := bstep (se 1 (by rfl) ⟨94022, by rfl⟩ : syracuseStep 125363 = 188045) B188045
theorem B190913 : Blo 123787 190913 := bstep (se 2 (by rfl) ⟨71592, by rfl⟩ : syracuseStep 190913 = 143185) B143185
theorem B125379 : Blo 123787 125379 := bstep (se 1 (by rfl) ⟨94034, by rfl⟩ : syracuseStep 125379 = 188069) B188069
theorem B125395 : Blo 123787 125395 := bstep (se 1 (by rfl) ⟨94046, by rfl⟩ : syracuseStep 125395 = 188093) B188093
theorem B190931 : Blo 123787 190931 := bstep (se 1 (by rfl) ⟨143198, by rfl⟩ : syracuseStep 190931 = 286397) B286397
theorem B125411 : Blo 123787 125411 := bstep (se 1 (by rfl) ⟨94058, by rfl⟩ : syracuseStep 125411 = 188117) B188117
theorem B190961 : Blo 123787 190961 := bstep (se 2 (by rfl) ⟨71610, by rfl⟩ : syracuseStep 190961 = 143221) B143221
theorem B125427 : Blo 123787 125427 := bstep (se 1 (by rfl) ⟨94070, by rfl⟩ : syracuseStep 125427 = 188141) B188141
theorem B125443 : Blo 123787 125443 := bstep (se 1 (by rfl) ⟨94082, by rfl⟩ : syracuseStep 125443 = 188165) B188165
theorem B190979 : Blo 123787 190979 := bstep (se 1 (by rfl) ⟨143234, by rfl⟩ : syracuseStep 190979 = 286469) B286469
theorem B387587 : Blo 123787 387587 := bstep (se 1 (by rfl) ⟨290690, by rfl⟩ : syracuseStep 387587 = 581381) B581381
theorem B125459 : Blo 123787 125459 := bstep (se 1 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 125459 = 188189) B188189
theorem B191009 : Blo 123787 191009 := bstep (se 2 (by rfl) ⟨71628, by rfl⟩ : syracuseStep 191009 = 143257) B143257
theorem B125475 : Blo 123787 125475 := bstep (se 1 (by rfl) ⟨94106, by rfl⟩ : syracuseStep 125475 = 188213) B188213
theorem B125491 : Blo 123787 125491 := bstep (se 1 (by rfl) ⟨94118, by rfl⟩ : syracuseStep 125491 = 188237) B188237
theorem B191027 : Blo 123787 191027 := bstep (se 1 (by rfl) ⟨143270, by rfl⟩ : syracuseStep 191027 = 286541) B286541
theorem B125507 : Blo 123787 125507 := bstep (se 1 (by rfl) ⟨94130, by rfl⟩ : syracuseStep 125507 = 188261) B188261
theorem B191057 : Blo 123787 191057 := bstep (se 2 (by rfl) ⟨71646, by rfl⟩ : syracuseStep 191057 = 143293) B143293
theorem B125523 : Blo 123787 125523 := bstep (se 1 (by rfl) ⟨94142, by rfl⟩ : syracuseStep 125523 = 188285) B188285
theorem B125539 : Blo 123787 125539 := bstep (se 1 (by rfl) ⟨94154, by rfl⟩ : syracuseStep 125539 = 188309) B188309
theorem B191075 : Blo 123787 191075 := bstep (se 1 (by rfl) ⟨143306, by rfl⟩ : syracuseStep 191075 = 286613) B286613
theorem B387683 : Blo 123787 387683 := bstep (se 1 (by rfl) ⟨290762, by rfl⟩ : syracuseStep 387683 = 581525) B581525
theorem B125555 : Blo 123787 125555 := bstep (se 1 (by rfl) ⟨94166, by rfl⟩ : syracuseStep 125555 = 188333) B188333
theorem B191105 : Blo 123787 191105 := bstep (se 2 (by rfl) ⟨71664, by rfl⟩ : syracuseStep 191105 = 143329) B143329
theorem B125571 : Blo 123787 125571 := bstep (se 1 (by rfl) ⟨94178, by rfl⟩ : syracuseStep 125571 = 188357) B188357
theorem B420497 : Blo 123787 420497 := bstep (se 2 (by rfl) ⟨157686, by rfl⟩ : syracuseStep 420497 = 315373) B315373
theorem B125587 : Blo 123787 125587 := bstep (se 1 (by rfl) ⟨94190, by rfl⟩ : syracuseStep 125587 = 188381) B188381
theorem B191123 : Blo 123787 191123 := bstep (se 1 (by rfl) ⟨143342, by rfl⟩ : syracuseStep 191123 = 286685) B286685
theorem B125603 : Blo 123787 125603 := bstep (se 1 (by rfl) ⟨94202, by rfl⟩ : syracuseStep 125603 = 188405) B188405
theorem B191153 : Blo 123787 191153 := bstep (se 2 (by rfl) ⟨71682, by rfl⟩ : syracuseStep 191153 = 143365) B143365
theorem B125619 : Blo 123787 125619 := bstep (se 1 (by rfl) ⟨94214, by rfl⟩ : syracuseStep 125619 = 188429) B188429
theorem B125635 : Blo 123787 125635 := bstep (se 1 (by rfl) ⟨94226, by rfl⟩ : syracuseStep 125635 = 188453) B188453
theorem B191171 : Blo 123787 191171 := bstep (se 1 (by rfl) ⟨143378, by rfl⟩ : syracuseStep 191171 = 286757) B286757
theorem B125651 : Blo 123787 125651 := bstep (se 1 (by rfl) ⟨94238, by rfl⟩ : syracuseStep 125651 = 188477) B188477
theorem B191201 : Blo 123787 191201 := bstep (se 2 (by rfl) ⟨71700, by rfl⟩ : syracuseStep 191201 = 143401) B143401
theorem B125667 : Blo 123787 125667 := bstep (se 1 (by rfl) ⟨94250, by rfl⟩ : syracuseStep 125667 = 188501) B188501
theorem B322289 : Blo 123787 322289 := bstep (se 2 (by rfl) ⟨120858, by rfl⟩ : syracuseStep 322289 = 241717) B241717
theorem B125683 : Blo 123787 125683 := bstep (se 1 (by rfl) ⟨94262, by rfl⟩ : syracuseStep 125683 = 188525) B188525
theorem B191219 : Blo 123787 191219 := bstep (se 1 (by rfl) ⟨143414, by rfl⟩ : syracuseStep 191219 = 286829) B286829
theorem B125699 : Blo 123787 125699 := bstep (se 1 (by rfl) ⟨94274, by rfl⟩ : syracuseStep 125699 = 188549) B188549
theorem B191249 : Blo 123787 191249 := bstep (se 2 (by rfl) ⟨71718, by rfl⟩ : syracuseStep 191249 = 143437) B143437
theorem B125715 : Blo 123787 125715 := bstep (se 1 (by rfl) ⟨94286, by rfl⟩ : syracuseStep 125715 = 188573) B188573
theorem B125731 : Blo 123787 125731 := bstep (se 1 (by rfl) ⟨94298, by rfl⟩ : syracuseStep 125731 = 188597) B188597
theorem B322339 : Blo 123787 322339 := bstep (se 1 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 322339 = 483509) B483509
theorem B191267 : Blo 123787 191267 := bstep (se 1 (by rfl) ⟨143450, by rfl⟩ : syracuseStep 191267 = 286901) B286901
theorem B125747 : Blo 123787 125747 := bstep (se 1 (by rfl) ⟨94310, by rfl⟩ : syracuseStep 125747 = 188621) B188621
theorem B191297 : Blo 123787 191297 := bstep (se 2 (by rfl) ⟨71736, by rfl⟩ : syracuseStep 191297 = 143473) B143473
theorem B125763 : Blo 123787 125763 := bstep (se 1 (by rfl) ⟨94322, by rfl⟩ : syracuseStep 125763 = 188645) B188645
theorem B125779 : Blo 123787 125779 := bstep (se 1 (by rfl) ⟨94334, by rfl⟩ : syracuseStep 125779 = 188669) B188669
theorem B191315 : Blo 123787 191315 := bstep (se 1 (by rfl) ⟨143486, by rfl⟩ : syracuseStep 191315 = 286973) B286973
theorem B125795 : Blo 123787 125795 := bstep (se 1 (by rfl) ⟨94346, by rfl⟩ : syracuseStep 125795 = 188693) B188693
theorem B191345 : Blo 123787 191345 := bstep (se 2 (by rfl) ⟨71754, by rfl⟩ : syracuseStep 191345 = 143509) B143509
theorem B125811 : Blo 123787 125811 := bstep (se 1 (by rfl) ⟨94358, by rfl⟩ : syracuseStep 125811 = 188717) B188717
theorem B125827 : Blo 123787 125827 := bstep (se 1 (by rfl) ⟨94370, by rfl⟩ : syracuseStep 125827 = 188741) B188741
theorem B191363 : Blo 123787 191363 := bstep (se 1 (by rfl) ⟨143522, by rfl⟩ : syracuseStep 191363 = 287045) B287045
theorem B125843 : Blo 123787 125843 := bstep (se 1 (by rfl) ⟨94382, by rfl⟩ : syracuseStep 125843 = 188765) B188765
theorem B191393 : Blo 123787 191393 := bstep (se 2 (by rfl) ⟨71772, by rfl⟩ : syracuseStep 191393 = 143545) B143545
theorem B125859 : Blo 123787 125859 := bstep (se 1 (by rfl) ⟨94394, by rfl⟩ : syracuseStep 125859 = 188789) B188789
theorem B322481 : Blo 123787 322481 := bstep (se 2 (by rfl) ⟨120930, by rfl⟩ : syracuseStep 322481 = 241861) B241861
theorem B125875 : Blo 123787 125875 := bstep (se 1 (by rfl) ⟨94406, by rfl⟩ : syracuseStep 125875 = 188813) B188813
theorem B191411 : Blo 123787 191411 := bstep (se 1 (by rfl) ⟨143558, by rfl⟩ : syracuseStep 191411 = 287117) B287117
theorem B125891 : Blo 123787 125891 := bstep (se 1 (by rfl) ⟨94418, by rfl⟩ : syracuseStep 125891 = 188837) B188837
theorem B191441 : Blo 123787 191441 := bstep (se 2 (by rfl) ⟨71790, by rfl⟩ : syracuseStep 191441 = 143581) B143581
theorem B125907 : Blo 123787 125907 := bstep (se 1 (by rfl) ⟨94430, by rfl⟩ : syracuseStep 125907 = 188861) B188861
theorem B125923 : Blo 123787 125923 := bstep (se 1 (by rfl) ⟨94442, by rfl⟩ : syracuseStep 125923 = 188885) B188885
theorem B191459 : Blo 123787 191459 := bstep (se 1 (by rfl) ⟨143594, by rfl⟩ : syracuseStep 191459 = 287189) B287189
theorem B125939 : Blo 123787 125939 := bstep (se 1 (by rfl) ⟨94454, by rfl⟩ : syracuseStep 125939 = 188909) B188909
theorem B191489 : Blo 123787 191489 := bstep (se 2 (by rfl) ⟨71808, by rfl⟩ : syracuseStep 191489 = 143617) B143617
theorem B125955 : Blo 123787 125955 := bstep (se 1 (by rfl) ⟨94466, by rfl⟩ : syracuseStep 125955 = 188933) B188933
theorem B125971 : Blo 123787 125971 := bstep (se 1 (by rfl) ⟨94478, by rfl⟩ : syracuseStep 125971 = 188957) B188957
theorem B191507 : Blo 123787 191507 := bstep (se 1 (by rfl) ⟨143630, by rfl⟩ : syracuseStep 191507 = 287261) B287261
theorem B158755 : Blo 123787 158755 := bstep (se 1 (by rfl) ⟨119066, by rfl⟩ : syracuseStep 158755 = 238133) B238133
theorem B322595 : Blo 123787 322595 := bstep (se 1 (by rfl) ⟨241946, by rfl⟩ : syracuseStep 322595 = 483893) B483893
theorem B125987 : Blo 123787 125987 := bstep (se 1 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 125987 = 188981) B188981
theorem B191537 : Blo 123787 191537 := bstep (se 2 (by rfl) ⟨71826, by rfl⟩ : syracuseStep 191537 = 143653) B143653
theorem B126003 : Blo 123787 126003 := bstep (se 1 (by rfl) ⟨94502, by rfl⟩ : syracuseStep 126003 = 189005) B189005
theorem B126019 : Blo 123787 126019 := bstep (se 1 (by rfl) ⟨94514, by rfl⟩ : syracuseStep 126019 = 189029) B189029
theorem B191555 : Blo 123787 191555 := bstep (se 1 (by rfl) ⟨143666, by rfl⟩ : syracuseStep 191555 = 287333) B287333
theorem B453709 : Blo 123787 453709 := bstep (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) B170141
theorem B814157 : Blo 123787 814157 := bstep (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) B305309
theorem B126035 : Blo 123787 126035 := bstep (se 1 (by rfl) ⟨94526, by rfl⟩ : syracuseStep 126035 = 189053) B189053
theorem B191585 : Blo 123787 191585 := bstep (se 2 (by rfl) ⟨71844, by rfl⟩ : syracuseStep 191585 = 143689) B143689
theorem B126051 : Blo 123787 126051 := bstep (se 1 (by rfl) ⟨94538, by rfl⟩ : syracuseStep 126051 = 189077) B189077
theorem B126067 : Blo 123787 126067 := bstep (se 1 (by rfl) ⟨94550, by rfl⟩ : syracuseStep 126067 = 189101) B189101
theorem B191603 : Blo 123787 191603 := bstep (se 1 (by rfl) ⟨143702, by rfl⟩ : syracuseStep 191603 = 287405) B287405
theorem B158851 : Blo 123787 158851 := bstep (se 1 (by rfl) ⟨119138, by rfl⟩ : syracuseStep 158851 = 238277) B238277
theorem B126083 : Blo 123787 126083 := bstep (se 1 (by rfl) ⟨94562, by rfl⟩ : syracuseStep 126083 = 189125) B189125
theorem B191633 : Blo 123787 191633 := bstep (se 2 (by rfl) ⟨71862, by rfl⟩ : syracuseStep 191633 = 143725) B143725
theorem B126099 : Blo 123787 126099 := bstep (se 1 (by rfl) ⟨94574, by rfl⟩ : syracuseStep 126099 = 189149) B189149
theorem B126115 : Blo 123787 126115 := bstep (se 1 (by rfl) ⟨94586, by rfl⟩ : syracuseStep 126115 = 189173) B189173
theorem B191651 : Blo 123787 191651 := bstep (se 1 (by rfl) ⟨143738, by rfl⟩ : syracuseStep 191651 = 287477) B287477
theorem B421037 : Blo 123787 421037 := bstep (se 3 (by rfl) ⟨78944, by rfl⟩ : syracuseStep 421037 = 157889) B157889
theorem B126131 : Blo 123787 126131 := bstep (se 1 (by rfl) ⟨94598, by rfl⟩ : syracuseStep 126131 = 189197) B189197
theorem B191681 : Blo 123787 191681 := bstep (se 2 (by rfl) ⟨71880, by rfl⟩ : syracuseStep 191681 = 143761) B143761
theorem B126147 : Blo 123787 126147 := bstep (se 1 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 126147 = 189221) B189221
theorem B126163 : Blo 123787 126163 := bstep (se 1 (by rfl) ⟨94622, by rfl⟩ : syracuseStep 126163 = 189245) B189245
theorem B421091 : Blo 123787 421091 := bstep (se 1 (by rfl) ⟨315818, by rfl⟩ : syracuseStep 421091 = 631637) B631637
theorem B126179 : Blo 123787 126179 := bstep (se 1 (by rfl) ⟨94634, by rfl⟩ : syracuseStep 126179 = 189269) B189269
theorem B126195 : Blo 123787 126195 := bstep (se 1 (by rfl) ⟨94646, by rfl⟩ : syracuseStep 126195 = 189293) B189293
theorem B126211 : Blo 123787 126211 := bstep (se 1 (by rfl) ⟨94658, by rfl⟩ : syracuseStep 126211 = 189317) B189317
theorem B126227 : Blo 123787 126227 := bstep (se 1 (by rfl) ⟨94670, by rfl⟩ : syracuseStep 126227 = 189341) B189341
theorem B3665173 : Blo 123787 3665173 := bstep (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) B171805
theorem B126243 : Blo 123787 126243 := bstep (se 1 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 126243 = 189365) B189365
theorem B126259 : Blo 123787 126259 := bstep (se 1 (by rfl) ⟨94694, by rfl⟩ : syracuseStep 126259 = 189389) B189389
theorem B126275 : Blo 123787 126275 := bstep (se 1 (by rfl) ⟨94706, by rfl⟩ : syracuseStep 126275 = 189413) B189413
theorem B355661 : Blo 123787 355661 := bstep (se 3 (by rfl) ⟨66686, by rfl⟩ : syracuseStep 355661 = 133373) B133373
theorem B126291 : Blo 123787 126291 := bstep (se 1 (by rfl) ⟨94718, by rfl⟩ : syracuseStep 126291 = 189437) B189437
theorem B126307 : Blo 123787 126307 := bstep (se 1 (by rfl) ⟨94730, by rfl⟩ : syracuseStep 126307 = 189461) B189461
theorem B126323 : Blo 123787 126323 := bstep (se 1 (by rfl) ⟨94742, by rfl⟩ : syracuseStep 126323 = 189485) B189485
theorem B126339 : Blo 123787 126339 := bstep (se 1 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 126339 = 189509) B189509
theorem B191891 : Blo 123787 191891 := bstep (se 1 (by rfl) ⟨143918, by rfl⟩ : syracuseStep 191891 = 287837) B287837
theorem B126355 : Blo 123787 126355 := bstep (se 1 (by rfl) ⟨94766, by rfl⟩ : syracuseStep 126355 = 189533) B189533
theorem B126371 : Blo 123787 126371 := bstep (se 1 (by rfl) ⟨94778, by rfl⟩ : syracuseStep 126371 = 189557) B189557
theorem B126387 : Blo 123787 126387 := bstep (se 1 (by rfl) ⟨94790, by rfl⟩ : syracuseStep 126387 = 189581) B189581
theorem B126403 : Blo 123787 126403 := bstep (se 1 (by rfl) ⟨94802, by rfl⟩ : syracuseStep 126403 = 189605) B189605
theorem B126419 : Blo 123787 126419 := bstep (se 1 (by rfl) ⟨94814, by rfl⟩ : syracuseStep 126419 = 189629) B189629
theorem B126435 : Blo 123787 126435 := bstep (se 1 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 126435 = 189653) B189653
theorem B421361 : Blo 123787 421361 := bstep (se 2 (by rfl) ⟨158010, by rfl⟩ : syracuseStep 421361 = 316021) B316021
theorem B126451 : Blo 123787 126451 := bstep (se 1 (by rfl) ⟨94838, by rfl⟩ : syracuseStep 126451 = 189677) B189677
theorem B355843 : Blo 123787 355843 := bstep (se 1 (by rfl) ⟨266882, by rfl⟩ : syracuseStep 355843 = 533765) B533765
theorem B126467 : Blo 123787 126467 := bstep (se 1 (by rfl) ⟨94850, by rfl⟩ : syracuseStep 126467 = 189701) B189701
theorem B126483 : Blo 123787 126483 := bstep (se 1 (by rfl) ⟨94862, by rfl⟩ : syracuseStep 126483 = 189725) B189725
theorem B126499 : Blo 123787 126499 := bstep (se 1 (by rfl) ⟨94874, by rfl⟩ : syracuseStep 126499 = 189749) B189749
theorem B355889 : Blo 123787 355889 := bstep (se 2 (by rfl) ⟨133458, by rfl⟩ : syracuseStep 355889 = 266917) B266917
theorem B126515 : Blo 123787 126515 := bstep (se 1 (by rfl) ⟨94886, by rfl⟩ : syracuseStep 126515 = 189773) B189773
theorem B126531 : Blo 123787 126531 := bstep (se 1 (by rfl) ⟨94898, by rfl⟩ : syracuseStep 126531 = 189797) B189797
theorem B126547 : Blo 123787 126547 := bstep (se 1 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 126547 = 189821) B189821
theorem B126563 : Blo 123787 126563 := bstep (se 1 (by rfl) ⟨94922, by rfl⟩ : syracuseStep 126563 = 189845) B189845
theorem B159347 : Blo 123787 159347 := bstep (se 1 (by rfl) ⟨119510, by rfl⟩ : syracuseStep 159347 = 239021) B239021
theorem B126579 : Blo 123787 126579 := bstep (se 1 (by rfl) ⟨94934, by rfl⟩ : syracuseStep 126579 = 189869) B189869
theorem B126595 : Blo 123787 126595 := bstep (se 1 (by rfl) ⟨94946, by rfl⟩ : syracuseStep 126595 = 189893) B189893
theorem B126611 : Blo 123787 126611 := bstep (se 1 (by rfl) ⟨94958, by rfl⟩ : syracuseStep 126611 = 189917) B189917
theorem B650915 : Blo 123787 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B126627 : Blo 123787 126627 := bstep (se 1 (by rfl) ⟨94970, by rfl⟩ : syracuseStep 126627 = 189941) B189941
theorem B323249 : Blo 123787 323249 := bstep (se 2 (by rfl) ⟨121218, by rfl⟩ : syracuseStep 323249 = 242437) B242437
theorem B126643 : Blo 123787 126643 := bstep (se 1 (by rfl) ⟨94982, by rfl⟩ : syracuseStep 126643 = 189965) B189965
theorem B126659 : Blo 123787 126659 := bstep (se 1 (by rfl) ⟨94994, by rfl⟩ : syracuseStep 126659 = 189989) B189989
theorem B126675 : Blo 123787 126675 := bstep (se 1 (by rfl) ⟨95006, by rfl⟩ : syracuseStep 126675 = 190013) B190013
theorem B126691 : Blo 123787 126691 := bstep (se 1 (by rfl) ⟨95018, by rfl⟩ : syracuseStep 126691 = 190037) B190037
theorem B126707 : Blo 123787 126707 := bstep (se 1 (by rfl) ⟨95030, by rfl⟩ : syracuseStep 126707 = 190061) B190061
theorem B126723 : Blo 123787 126723 := bstep (se 1 (by rfl) ⟨95042, by rfl⟩ : syracuseStep 126723 = 190085) B190085
theorem B126739 : Blo 123787 126739 := bstep (se 1 (by rfl) ⟨95054, by rfl⟩ : syracuseStep 126739 = 190109) B190109
theorem B126755 : Blo 123787 126755 := bstep (se 1 (by rfl) ⟨95066, by rfl⟩ : syracuseStep 126755 = 190133) B190133
theorem B126771 : Blo 123787 126771 := bstep (se 1 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 126771 = 190157) B190157
theorem B126787 : Blo 123787 126787 := bstep (se 1 (by rfl) ⟨95090, by rfl⟩ : syracuseStep 126787 = 190181) B190181
theorem B126803 : Blo 123787 126803 := bstep (se 1 (by rfl) ⟨95102, by rfl⟩ : syracuseStep 126803 = 190205) B190205
theorem B126819 : Blo 123787 126819 := bstep (se 1 (by rfl) ⟨95114, by rfl⟩ : syracuseStep 126819 = 190229) B190229
theorem B126835 : Blo 123787 126835 := bstep (se 1 (by rfl) ⟨95126, by rfl⟩ : syracuseStep 126835 = 190253) B190253
theorem B126851 : Blo 123787 126851 := bstep (se 1 (by rfl) ⟨95138, by rfl⟩ : syracuseStep 126851 = 190277) B190277
theorem B126867 : Blo 123787 126867 := bstep (se 1 (by rfl) ⟨95150, by rfl⟩ : syracuseStep 126867 = 190301) B190301
theorem B683939 : Blo 123787 683939 := bstep (se 1 (by rfl) ⟨512954, by rfl⟩ : syracuseStep 683939 = 1025909) B1025909
theorem B126883 : Blo 123787 126883 := bstep (se 1 (by rfl) ⟨95162, by rfl⟩ : syracuseStep 126883 = 190325) B190325
theorem B126899 : Blo 123787 126899 := bstep (se 1 (by rfl) ⟨95174, by rfl⟩ : syracuseStep 126899 = 190349) B190349
theorem B126915 : Blo 123787 126915 := bstep (se 1 (by rfl) ⟨95186, by rfl⟩ : syracuseStep 126915 = 190373) B190373
theorem B126931 : Blo 123787 126931 := bstep (se 1 (by rfl) ⟨95198, by rfl⟩ : syracuseStep 126931 = 190397) B190397
theorem B126947 : Blo 123787 126947 := bstep (se 1 (by rfl) ⟨95210, by rfl⟩ : syracuseStep 126947 = 190421) B190421
theorem B126963 : Blo 123787 126963 := bstep (se 1 (by rfl) ⟨95222, by rfl⟩ : syracuseStep 126963 = 190445) B190445
theorem B126979 : Blo 123787 126979 := bstep (se 1 (by rfl) ⟨95234, by rfl⟩ : syracuseStep 126979 = 190469) B190469
theorem B421901 : Blo 123787 421901 := bstep (se 3 (by rfl) ⟨79106, by rfl⟩ : syracuseStep 421901 = 158213) B158213
theorem B126995 : Blo 123787 126995 := bstep (se 1 (by rfl) ⟨95246, by rfl⟩ : syracuseStep 126995 = 190493) B190493
theorem B127011 : Blo 123787 127011 := bstep (se 1 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 127011 = 190517) B190517
theorem B127027 : Blo 123787 127027 := bstep (se 1 (by rfl) ⟨95270, by rfl⟩ : syracuseStep 127027 = 190541) B190541
theorem B421955 : Blo 123787 421955 := bstep (se 1 (by rfl) ⟨316466, by rfl⟩ : syracuseStep 421955 = 632933) B632933
theorem B127043 : Blo 123787 127043 := bstep (se 1 (by rfl) ⟨95282, by rfl⟩ : syracuseStep 127043 = 190565) B190565
theorem B127059 : Blo 123787 127059 := bstep (se 1 (by rfl) ⟨95294, by rfl⟩ : syracuseStep 127059 = 190589) B190589
theorem B127075 : Blo 123787 127075 := bstep (se 1 (by rfl) ⟨95306, by rfl⟩ : syracuseStep 127075 = 190613) B190613
theorem B127091 : Blo 123787 127091 := bstep (se 1 (by rfl) ⟨95318, by rfl⟩ : syracuseStep 127091 = 190637) B190637
theorem B127107 : Blo 123787 127107 := bstep (se 1 (by rfl) ⟨95330, by rfl⟩ : syracuseStep 127107 = 190661) B190661
theorem B127123 : Blo 123787 127123 := bstep (se 1 (by rfl) ⟨95342, by rfl⟩ : syracuseStep 127123 = 190685) B190685
theorem B127139 : Blo 123787 127139 := bstep (se 1 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 127139 = 190709) B190709
theorem B127155 : Blo 123787 127155 := bstep (se 1 (by rfl) ⟨95366, by rfl⟩ : syracuseStep 127155 = 190733) B190733
theorem B127171 : Blo 123787 127171 := bstep (se 1 (by rfl) ⟨95378, by rfl⟩ : syracuseStep 127171 = 190757) B190757
theorem B1142981 : Blo 123787 1142981 := bstep (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) B214309
theorem B127187 : Blo 123787 127187 := bstep (se 1 (by rfl) ⟨95390, by rfl⟩ : syracuseStep 127187 = 190781) B190781
theorem B127203 : Blo 123787 127203 := bstep (se 1 (by rfl) ⟨95402, by rfl⟩ : syracuseStep 127203 = 190805) B190805
theorem B127219 : Blo 123787 127219 := bstep (se 1 (by rfl) ⟨95414, by rfl⟩ : syracuseStep 127219 = 190829) B190829
theorem B127235 : Blo 123787 127235 := bstep (se 1 (by rfl) ⟨95426, by rfl⟩ : syracuseStep 127235 = 190853) B190853
theorem B127251 : Blo 123787 127251 := bstep (se 1 (by rfl) ⟨95438, by rfl⟩ : syracuseStep 127251 = 190877) B190877
theorem B127267 : Blo 123787 127267 := bstep (se 1 (by rfl) ⟨95450, by rfl⟩ : syracuseStep 127267 = 190901) B190901
theorem B160051 : Blo 123787 160051 := bstep (se 1 (by rfl) ⟨120038, by rfl⟩ : syracuseStep 160051 = 240077) B240077
theorem B127283 : Blo 123787 127283 := bstep (se 1 (by rfl) ⟨95462, by rfl⟩ : syracuseStep 127283 = 190925) B190925
theorem B127299 : Blo 123787 127299 := bstep (se 1 (by rfl) ⟨95474, by rfl⟩ : syracuseStep 127299 = 190949) B190949
theorem B422225 : Blo 123787 422225 := bstep (se 2 (by rfl) ⟨158334, by rfl⟩ : syracuseStep 422225 = 316669) B316669
theorem B127315 : Blo 123787 127315 := bstep (se 1 (by rfl) ⟨95486, by rfl⟩ : syracuseStep 127315 = 190973) B190973
theorem B127331 : Blo 123787 127331 := bstep (se 1 (by rfl) ⟨95498, by rfl⟩ : syracuseStep 127331 = 190997) B190997
theorem B127347 : Blo 123787 127347 := bstep (se 1 (by rfl) ⟨95510, by rfl⟩ : syracuseStep 127347 = 191021) B191021
theorem B127363 : Blo 123787 127363 := bstep (se 1 (by rfl) ⟨95522, by rfl⟩ : syracuseStep 127363 = 191045) B191045
theorem B160147 : Blo 123787 160147 := bstep (se 1 (by rfl) ⟨120110, by rfl⟩ : syracuseStep 160147 = 240221) B240221
theorem B127379 : Blo 123787 127379 := bstep (se 1 (by rfl) ⟨95534, by rfl⟩ : syracuseStep 127379 = 191069) B191069
theorem B127395 : Blo 123787 127395 := bstep (se 1 (by rfl) ⟨95546, by rfl⟩ : syracuseStep 127395 = 191093) B191093
theorem B127411 : Blo 123787 127411 := bstep (se 1 (by rfl) ⟨95558, by rfl⟩ : syracuseStep 127411 = 191117) B191117
theorem B127427 : Blo 123787 127427 := bstep (se 1 (by rfl) ⟨95570, by rfl⟩ : syracuseStep 127427 = 191141) B191141
theorem B127443 : Blo 123787 127443 := bstep (se 1 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 127443 = 191165) B191165
theorem B127459 : Blo 123787 127459 := bstep (se 1 (by rfl) ⟨95594, by rfl⟩ : syracuseStep 127459 = 191189) B191189
theorem B127475 : Blo 123787 127475 := bstep (se 1 (by rfl) ⟨95606, by rfl⟩ : syracuseStep 127475 = 191213) B191213
theorem B127491 : Blo 123787 127491 := bstep (se 1 (by rfl) ⟨95618, by rfl⟩ : syracuseStep 127491 = 191237) B191237
theorem B127507 : Blo 123787 127507 := bstep (se 1 (by rfl) ⟨95630, by rfl⟩ : syracuseStep 127507 = 191261) B191261
theorem B127523 : Blo 123787 127523 := bstep (se 1 (by rfl) ⟨95642, by rfl⟩ : syracuseStep 127523 = 191285) B191285
theorem B127539 : Blo 123787 127539 := bstep (se 1 (by rfl) ⟨95654, by rfl⟩ : syracuseStep 127539 = 191309) B191309
theorem B127555 : Blo 123787 127555 := bstep (se 1 (by rfl) ⟨95666, by rfl⟩ : syracuseStep 127555 = 191333) B191333
theorem B127571 : Blo 123787 127571 := bstep (se 1 (by rfl) ⟨95678, by rfl⟩ : syracuseStep 127571 = 191357) B191357
theorem B127587 : Blo 123787 127587 := bstep (se 1 (by rfl) ⟨95690, by rfl⟩ : syracuseStep 127587 = 191381) B191381
theorem B127603 : Blo 123787 127603 := bstep (se 1 (by rfl) ⟨95702, by rfl⟩ : syracuseStep 127603 = 191405) B191405
theorem B127619 : Blo 123787 127619 := bstep (se 1 (by rfl) ⟨95714, by rfl⟩ : syracuseStep 127619 = 191429) B191429
theorem B127635 : Blo 123787 127635 := bstep (se 1 (by rfl) ⟨95726, by rfl⟩ : syracuseStep 127635 = 191453) B191453
theorem B127651 : Blo 123787 127651 := bstep (se 1 (by rfl) ⟨95738, by rfl⟩ : syracuseStep 127651 = 191477) B191477
theorem B127667 : Blo 123787 127667 := bstep (se 1 (by rfl) ⟨95750, by rfl⟩ : syracuseStep 127667 = 191501) B191501
theorem B127683 : Blo 123787 127683 := bstep (se 1 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 127683 = 191525) B191525
theorem B127699 : Blo 123787 127699 := bstep (se 1 (by rfl) ⟨95774, by rfl⟩ : syracuseStep 127699 = 191549) B191549
theorem B226019 : Blo 123787 226019 := bstep (se 1 (by rfl) ⟨169514, by rfl⟩ : syracuseStep 226019 = 339029) B339029
theorem B127715 : Blo 123787 127715 := bstep (se 1 (by rfl) ⟨95786, by rfl⟩ : syracuseStep 127715 = 191573) B191573
theorem B127731 : Blo 123787 127731 := bstep (se 1 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 127731 = 191597) B191597
theorem B127747 : Blo 123787 127747 := bstep (se 1 (by rfl) ⟨95810, by rfl⟩ : syracuseStep 127747 = 191621) B191621
theorem B127763 : Blo 123787 127763 := bstep (se 1 (by rfl) ⟨95822, by rfl⟩ : syracuseStep 127763 = 191645) B191645
theorem B127779 : Blo 123787 127779 := bstep (se 1 (by rfl) ⟨95834, by rfl⟩ : syracuseStep 127779 = 191669) B191669
theorem B422765 : Blo 123787 422765 := bstep (se 3 (by rfl) ⟨79268, by rfl⟩ : syracuseStep 422765 = 158537) B158537
theorem B160643 : Blo 123787 160643 := bstep (se 1 (by rfl) ⟨120482, by rfl⟩ : syracuseStep 160643 = 240965) B240965
theorem B422819 : Blo 123787 422819 := bstep (se 1 (by rfl) ⟨317114, by rfl⟩ : syracuseStep 422819 = 634229) B634229
theorem B357347 : Blo 123787 357347 := bstep (se 1 (by rfl) ⟨268010, by rfl⟩ : syracuseStep 357347 = 536021) B536021
theorem B947213 : Blo 123787 947213 := bstep (se 3 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 947213 = 355205) B355205
theorem B423089 : Blo 123787 423089 := bstep (se 2 (by rfl) ⟨158658, by rfl⟩ : syracuseStep 423089 = 317317) B317317
theorem B193745 : Blo 123787 193745 := bstep (se 2 (by rfl) ⟨72654, by rfl⟩ : syracuseStep 193745 = 145309) B145309
theorem B1439045 : Blo 123787 1439045 := bstep (se 4 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 1439045 = 269821) B269821
theorem B161347 : Blo 123787 161347 := bstep (se 1 (by rfl) ⟨121010, by rfl⟩ : syracuseStep 161347 = 242021) B242021
theorem B194195 : Blo 123787 194195 := bstep (se 1 (by rfl) ⟨145646, by rfl⟩ : syracuseStep 194195 = 291293) B291293
theorem B161443 : Blo 123787 161443 := bstep (se 1 (by rfl) ⟨121082, by rfl⟩ : syracuseStep 161443 = 242165) B242165
theorem B423629 : Blo 123787 423629 := bstep (se 3 (by rfl) ⟨79430, by rfl⟩ : syracuseStep 423629 = 158861) B158861
theorem B423683 : Blo 123787 423683 := bstep (se 1 (by rfl) ⟨317762, by rfl⟩ : syracuseStep 423683 = 635525) B635525
theorem B423953 : Blo 123787 423953 := bstep (se 2 (by rfl) ⟨158982, by rfl⟩ : syracuseStep 423953 = 317965) B317965
theorem B358577 : Blo 123787 358577 := bstep (se 2 (by rfl) ⟨134466, by rfl⟩ : syracuseStep 358577 = 268933) B268933
theorem B9238981 : Blo 123787 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B424493 : Blo 123787 424493 := bstep (se 3 (by rfl) ⟨79592, by rfl⟩ : syracuseStep 424493 = 159185) B159185
theorem B424547 : Blo 123787 424547 := bstep (se 1 (by rfl) ⟨318410, by rfl⟩ : syracuseStep 424547 = 636821) B636821
theorem B424817 : Blo 123787 424817 := bstep (se 2 (by rfl) ⟨159306, by rfl⟩ : syracuseStep 424817 = 318613) B318613
theorem B457805 : Blo 123787 457805 := bstep (se 3 (by rfl) ⟨85838, by rfl⟩ : syracuseStep 457805 = 171677) B171677
theorem B425197 : Blo 123787 425197 := bstep (se 3 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 425197 = 159449) B159449
theorem B425357 : Blo 123787 425357 := bstep (se 3 (by rfl) ⟨79754, by rfl⟩ : syracuseStep 425357 = 159509) B159509
theorem B425411 : Blo 123787 425411 := bstep (se 1 (by rfl) ⟨319058, by rfl⟩ : syracuseStep 425411 = 638117) B638117
theorem B491021 : Blo 123787 491021 := bstep (se 3 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 491021 = 184133) B184133
theorem B360035 : Blo 123787 360035 := bstep (se 1 (by rfl) ⟨270026, by rfl⟩ : syracuseStep 360035 = 540053) B540053
theorem B425681 : Blo 123787 425681 := bstep (se 2 (by rfl) ⟨159630, by rfl⟩ : syracuseStep 425681 = 319261) B319261
theorem B2817845 : Blo 123787 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B950129 : Blo 123787 950129 := bstep (se 2 (by rfl) ⟨356298, by rfl⟩ : syracuseStep 950129 = 712597) B712597
theorem B720845 : Blo 123787 720845 := bstep (se 3 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 720845 = 270317) B270317
theorem B426059 : Blo 123787 426059 := bstep (se 1 (by rfl) ⟨319544, by rfl⟩ : syracuseStep 426059 = 639089) B639089
theorem B983171 : Blo 123787 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B426329 : Blo 123787 426329 := bstep (se 2 (by rfl) ⟨159873, by rfl⟩ : syracuseStep 426329 = 319747) B319747
theorem B229825 : Blo 123787 229825 := bstep (se 2 (by rfl) ⟨86184, by rfl⟩ : syracuseStep 229825 = 172369) B172369
theorem B1081817 : Blo 123787 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B1049219 : Blo 123787 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B427031 : Blo 123787 427031 := bstep (se 1 (by rfl) ⟨320273, by rfl⟩ : syracuseStep 427031 = 640547) B640547
theorem B361675 : Blo 123787 361675 := bstep (se 1 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 361675 = 542513) B542513
theorem B951587 : Blo 123787 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B1344869 : Blo 123787 1344869 := bstep (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) B252163
theorem B427571 : Blo 123787 427571 := bstep (se 1 (by rfl) ⟨320678, by rfl⟩ : syracuseStep 427571 = 641357) B641357
theorem B362177 : Blo 123787 362177 := bstep (se 2 (by rfl) ⟨135816, by rfl⟩ : syracuseStep 362177 = 271633) B271633
theorem B3835633 : Blo 123787 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B427841 : Blo 123787 427841 := bstep (se 2 (by rfl) ⟨160440, by rfl⟩ : syracuseStep 427841 = 320881) B320881
theorem B362519 : Blo 123787 362519 := bstep (se 1 (by rfl) ⟨271889, by rfl⟩ : syracuseStep 362519 = 543779) B543779
theorem B919873 : Blo 123787 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B428381 : Blo 123787 428381 := bstep (se 3 (by rfl) ⟨80321, by rfl⟩ : syracuseStep 428381 = 160643) B160643
theorem B133655 : Blo 123787 133655 := bstep (se 1 (by rfl) ⟨100241, by rfl⟩ : syracuseStep 133655 = 200483) B200483
theorem B4983389 : Blo 123787 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B690905 : Blo 123787 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B264961 : Blo 123787 264961 := bstep (se 2 (by rfl) ⟨99360, by rfl⟩ : syracuseStep 264961 = 198721) B198721
theorem B1084205 : Blo 123787 1084205 := bstep (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) B406577
theorem B134347 : Blo 123787 134347 := bstep (se 1 (by rfl) ⟨100760, by rfl⟩ : syracuseStep 134347 = 201521) B201521
theorem B265459 : Blo 123787 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B363865 : Blo 123787 363865 := bstep (se 2 (by rfl) ⟨136449, by rfl⟩ : syracuseStep 363865 = 272899) B272899
theorem B429515 : Blo 123787 429515 := bstep (se 1 (by rfl) ⟨322136, by rfl⟩ : syracuseStep 429515 = 644273) B644273
theorem B298571 : Blo 123787 298571 := bstep (se 1 (by rfl) ⟨223928, by rfl⟩ : syracuseStep 298571 = 447857) B447857
theorem B265943 : Blo 123787 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B429785 : Blo 123787 429785 := bstep (se 2 (by rfl) ⟨161169, by rfl⟩ : syracuseStep 429785 = 322339) B322339
theorem B462941 : Blo 123787 462941 := bstep (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) B173603
theorem B299159 : Blo 123787 299159 := bstep (se 1 (by rfl) ⟨224369, by rfl⟩ : syracuseStep 299159 = 448739) B448739
theorem B200855 : Blo 123787 200855 := bstep (se 1 (by rfl) ⟨150641, by rfl⟩ : syracuseStep 200855 = 301283) B301283
theorem B1380503 : Blo 123787 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B528563 : Blo 123787 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B266507 : Blo 123787 266507 := bstep (se 1 (by rfl) ⟨199880, by rfl⟩ : syracuseStep 266507 = 399761) B399761
theorem B4886897 : Blo 123787 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B430487 : Blo 123787 430487 := bstep (se 1 (by rfl) ⟨322865, by rfl⟩ : syracuseStep 430487 = 645731) B645731
theorem B463283 : Blo 123787 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B135799 : Blo 123787 135799 := bstep (se 1 (by rfl) ⟨101849, by rfl⟩ : syracuseStep 135799 = 203699) B203699
theorem B266969 : Blo 123787 266969 := bstep (se 2 (by rfl) ⟨100113, by rfl⟩ : syracuseStep 266969 = 200227) B200227
theorem B1151819 : Blo 123787 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B627587 : Blo 123787 627587 := bstep (se 1 (by rfl) ⟨470690, by rfl⟩ : syracuseStep 627587 = 941381) B941381
theorem B201611 : Blo 123787 201611 := bstep (se 1 (by rfl) ⟨151208, by rfl⟩ : syracuseStep 201611 = 302417) B302417
theorem B431027 : Blo 123787 431027 := bstep (se 1 (by rfl) ⟨323270, by rfl⟩ : syracuseStep 431027 = 646541) B646541
theorem B136171 : Blo 123787 136171 := bstep (se 1 (by rfl) ⟨102128, by rfl⟩ : syracuseStep 136171 = 204257) B204257
theorem B398429 : Blo 123787 398429 := bstep (se 3 (by rfl) ⟨74705, by rfl⟩ : syracuseStep 398429 = 149411) B149411
theorem B202123 : Blo 123787 202123 := bstep (se 1 (by rfl) ⟨151592, by rfl⟩ : syracuseStep 202123 = 303185) B303185
theorem B464459 : Blo 123787 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B1087181 : Blo 123787 1087181 := bstep (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) B407693
theorem B235315 : Blo 123787 235315 := bstep (se 1 (by rfl) ⟨176486, by rfl⟩ : syracuseStep 235315 = 352973) B352973
theorem B268147 : Blo 123787 268147 := bstep (se 1 (by rfl) ⟨201110, by rfl⟩ : syracuseStep 268147 = 402221) B402221
theorem B399325 : Blo 123787 399325 := bstep (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) B149747
theorem B923665 : Blo 123787 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B235543 : Blo 123787 235543 := bstep (se 1 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 235543 = 353315) B353315
theorem B2693189 : Blo 123787 2693189 := bstep (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) B504973
theorem B202841 : Blo 123787 202841 := bstep (se 2 (by rfl) ⟨76065, by rfl⟩ : syracuseStep 202841 = 152131) B152131
theorem B235649 : Blo 123787 235649 := bstep (se 2 (by rfl) ⟨88368, by rfl⟩ : syracuseStep 235649 = 176737) B176737
theorem B235801 : Blo 123787 235801 := bstep (se 2 (by rfl) ⟨88425, by rfl⟩ : syracuseStep 235801 = 176851) B176851
theorem B203033 : Blo 123787 203033 := bstep (se 2 (by rfl) ⟨76137, by rfl⟩ : syracuseStep 203033 = 152275) B152275
theorem B268609 : Blo 123787 268609 := bstep (se 2 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 268609 = 201457) B201457
theorem B203161 : Blo 123787 203161 := bstep (se 2 (by rfl) ⟨76185, by rfl⟩ : syracuseStep 203161 = 152371) B152371
theorem B2038193 : Blo 123787 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B956933 : Blo 123787 956933 := bstep (se 4 (by rfl) ⟨89712, by rfl⟩ : syracuseStep 956933 = 179425) B179425
theorem B301619 : Blo 123787 301619 := bstep (se 1 (by rfl) ⟨226214, by rfl⟩ : syracuseStep 301619 = 452429) B452429
theorem B727703 : Blo 123787 727703 := bstep (se 1 (by rfl) ⟨545777, by rfl⟩ : syracuseStep 727703 = 1091555) B1091555
theorem B531373 : Blo 123787 531373 := bstep (se 3 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 531373 = 199265) B199265
theorem B269335 : Blo 123787 269335 := bstep (se 1 (by rfl) ⟨202001, by rfl⟩ : syracuseStep 269335 = 404003) B404003
theorem B203801 : Blo 123787 203801 := bstep (se 2 (by rfl) ⟨76425, by rfl⟩ : syracuseStep 203801 = 152851) B152851
theorem B237107 : Blo 123787 237107 := bstep (se 1 (by rfl) ⟨177830, by rfl⟩ : syracuseStep 237107 = 355661) B355661
theorem B269963 : Blo 123787 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B237259 : Blo 123787 237259 := bstep (se 1 (by rfl) ⟨177944, by rfl⟩ : syracuseStep 237259 = 355889) B355889
theorem B433943 : Blo 123787 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B270155 : Blo 123787 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B892889 : Blo 123787 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B1023961 : Blo 123787 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B237593 : Blo 123787 237593 := bstep (se 2 (by rfl) ⟨89097, by rfl⟩ : syracuseStep 237593 = 178195) B178195
theorem B139351 : Blo 123787 139351 := bstep (se 1 (by rfl) ⟨104513, by rfl⟩ : syracuseStep 139351 = 209027) B209027
theorem B761987 : Blo 123787 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B139531 : Blo 123787 139531 := bstep (se 1 (by rfl) ⟨104648, by rfl⟩ : syracuseStep 139531 = 209297) B209297
theorem B139639 : Blo 123787 139639 := bstep (se 1 (by rfl) ⟨104729, by rfl⟩ : syracuseStep 139639 = 209459) B209459
theorem B631313 : Blo 123787 631313 := bstep (se 2 (by rfl) ⟨236742, by rfl⟩ : syracuseStep 631313 = 473485) B473485
theorem B205337 : Blo 123787 205337 := bstep (se 2 (by rfl) ⟨77001, by rfl⟩ : syracuseStep 205337 = 154003) B154003
theorem B139819 : Blo 123787 139819 := bstep (se 1 (by rfl) ⟨104864, by rfl⟩ : syracuseStep 139819 = 209729) B209729
theorem B533081 : Blo 123787 533081 := bstep (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) B399811
theorem B139927 : Blo 123787 139927 := bstep (se 1 (by rfl) ⟨104945, by rfl⟩ : syracuseStep 139927 = 209891) B209891
theorem B238231 : Blo 123787 238231 := bstep (se 1 (by rfl) ⟨178673, by rfl⟩ : syracuseStep 238231 = 357347) B357347
theorem B271001 : Blo 123787 271001 := bstep (se 2 (by rfl) ⟨101625, by rfl⟩ : syracuseStep 271001 = 203251) B203251
theorem B631475 : Blo 123787 631475 := bstep (se 1 (by rfl) ⟨473606, by rfl⟩ : syracuseStep 631475 = 947213) B947213
theorem B2859725 : Blo 123787 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B2138885 : Blo 123787 2138885 := bstep (se 4 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 2138885 = 401041) B401041
theorem B140107 : Blo 123787 140107 := bstep (se 1 (by rfl) ⟨105080, by rfl⟩ : syracuseStep 140107 = 210161) B210161
theorem B959363 : Blo 123787 959363 := bstep (se 1 (by rfl) ⟨719522, by rfl⟩ : syracuseStep 959363 = 1439045) B1439045
theorem B140215 : Blo 123787 140215 := bstep (se 1 (by rfl) ⟨105161, by rfl⟩ : syracuseStep 140215 = 210323) B210323
theorem B140395 : Blo 123787 140395 := bstep (se 1 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 140395 = 210593) B210593
theorem B1156301 : Blo 123787 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B140503 : Blo 123787 140503 := bstep (se 1 (by rfl) ⟨105377, by rfl⟩ : syracuseStep 140503 = 210755) B210755
theorem B271667 : Blo 123787 271667 := bstep (se 1 (by rfl) ⟨203750, by rfl⟩ : syracuseStep 271667 = 407501) B407501
theorem B140683 : Blo 123787 140683 := bstep (se 1 (by rfl) ⟨105512, by rfl⟩ : syracuseStep 140683 = 211025) B211025
theorem B239051 : Blo 123787 239051 := bstep (se 1 (by rfl) ⟨179288, by rfl⟩ : syracuseStep 239051 = 358577) B358577
theorem B140791 : Blo 123787 140791 := bstep (se 1 (by rfl) ⟨105593, by rfl⟩ : syracuseStep 140791 = 211187) B211187
theorem B239105 : Blo 123787 239105 := bstep (se 2 (by rfl) ⟨89664, by rfl⟩ : syracuseStep 239105 = 179329) B179329
theorem B566929 : Blo 123787 566929 := bstep (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) B425197
theorem B140971 : Blo 123787 140971 := bstep (se 1 (by rfl) ⟨105728, by rfl⟩ : syracuseStep 140971 = 211457) B211457
theorem B141079 : Blo 123787 141079 := bstep (se 1 (by rfl) ⟨105809, by rfl⟩ : syracuseStep 141079 = 211619) B211619
theorem B861997 : Blo 123787 861997 := bstep (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) B323249
theorem B534347 : Blo 123787 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B796547 : Blo 123787 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B141259 : Blo 123787 141259 := bstep (se 1 (by rfl) ⟨105944, by rfl⟩ : syracuseStep 141259 = 211889) B211889
theorem B305203 : Blo 123787 305203 := bstep (se 1 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 305203 = 457805) B457805
theorem B141367 : Blo 123787 141367 := bstep (se 1 (by rfl) ⟨106025, by rfl⟩ : syracuseStep 141367 = 212051) B212051
theorem B534707 : Blo 123787 534707 := bstep (se 1 (by rfl) ⟨401030, by rfl⟩ : syracuseStep 534707 = 802061) B802061
theorem B141547 : Blo 123787 141547 := bstep (se 1 (by rfl) ⟨106160, by rfl⟩ : syracuseStep 141547 = 212321) B212321
theorem B272641 : Blo 123787 272641 := bstep (se 2 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 272641 = 204481) B204481
theorem B338251 : Blo 123787 338251 := bstep (se 1 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 338251 = 507377) B507377
theorem B141655 : Blo 123787 141655 := bstep (se 1 (by rfl) ⟨106241, by rfl⟩ : syracuseStep 141655 = 212483) B212483
theorem B240023 : Blo 123787 240023 := bstep (se 1 (by rfl) ⟨180017, by rfl⟩ : syracuseStep 240023 = 360035) B360035
theorem B272897 : Blo 123787 272897 := bstep (se 2 (by rfl) ⟨102336, by rfl⟩ : syracuseStep 272897 = 204673) B204673
theorem B141835 : Blo 123787 141835 := bstep (se 1 (by rfl) ⟨106376, by rfl⟩ : syracuseStep 141835 = 212753) B212753
theorem B1878563 : Blo 123787 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B600641 : Blo 123787 600641 := bstep (se 2 (by rfl) ⟨225240, by rfl⟩ : syracuseStep 600641 = 450481) B450481
theorem B633419 : Blo 123787 633419 := bstep (se 1 (by rfl) ⟨475064, by rfl⟩ : syracuseStep 633419 = 950129) B950129
theorem B141943 : Blo 123787 141943 := bstep (se 1 (by rfl) ⟨106457, by rfl⟩ : syracuseStep 141943 = 212915) B212915
theorem B1059601 : Blo 123787 1059601 := bstep (se 2 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 1059601 = 794701) B794701
theorem B142123 : Blo 123787 142123 := bstep (se 1 (by rfl) ⟨106592, by rfl⟩ : syracuseStep 142123 = 213185) B213185
theorem B273227 : Blo 123787 273227 := bstep (se 1 (by rfl) ⟨204920, by rfl⟩ : syracuseStep 273227 = 409841) B409841
theorem B142231 : Blo 123787 142231 := bstep (se 1 (by rfl) ⟨106673, by rfl⟩ : syracuseStep 142231 = 213347) B213347
theorem B2010035 : Blo 123787 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B240563 : Blo 123787 240563 := bstep (se 1 (by rfl) ⟨180422, by rfl⟩ : syracuseStep 240563 = 360845) B360845
theorem B1059875 : Blo 123787 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B142411 : Blo 123787 142411 := bstep (se 1 (by rfl) ⟨106808, by rfl⟩ : syracuseStep 142411 = 213617) B213617
theorem B142519 : Blo 123787 142519 := bstep (se 1 (by rfl) ⟨106889, by rfl⟩ : syracuseStep 142519 = 213779) B213779
theorem B1027403 : Blo 123787 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B142699 : Blo 123787 142699 := bstep (se 1 (by rfl) ⟨107024, by rfl⟩ : syracuseStep 142699 = 214049) B214049
theorem B241049 : Blo 123787 241049 := bstep (se 2 (by rfl) ⟨90393, by rfl⟩ : syracuseStep 241049 = 180787) B180787
theorem B142807 : Blo 123787 142807 := bstep (se 1 (by rfl) ⟨107105, by rfl⟩ : syracuseStep 142807 = 214211) B214211
theorem B142987 : Blo 123787 142987 := bstep (se 1 (by rfl) ⟨107240, by rfl⟩ : syracuseStep 142987 = 214481) B214481
theorem B339635 : Blo 123787 339635 := bstep (se 1 (by rfl) ⟨254726, by rfl⟩ : syracuseStep 339635 = 509453) B509453
theorem B143095 : Blo 123787 143095 := bstep (se 1 (by rfl) ⟨107321, by rfl⟩ : syracuseStep 143095 = 214643) B214643
theorem B339763 : Blo 123787 339763 := bstep (se 1 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 339763 = 509645) B509645
theorem B470873 : Blo 123787 470873 := bstep (se 2 (by rfl) ⟨176577, by rfl⟩ : syracuseStep 470873 = 353155) B353155
theorem B143275 : Blo 123787 143275 := bstep (se 1 (by rfl) ⟨107456, by rfl⟩ : syracuseStep 143275 = 214913) B214913
theorem B208919 : Blo 123787 208919 := bstep (se 1 (by rfl) ⟨156689, by rfl⟩ : syracuseStep 208919 = 313379) B313379
theorem B143383 : Blo 123787 143383 := bstep (se 1 (by rfl) ⟨107537, by rfl⟩ : syracuseStep 143383 = 215075) B215075
theorem B241715 : Blo 123787 241715 := bstep (se 1 (by rfl) ⟨181286, by rfl⟩ : syracuseStep 241715 = 362573) B362573
theorem B209047 : Blo 123787 209047 := bstep (se 1 (by rfl) ⟨156785, by rfl⟩ : syracuseStep 209047 = 313571) B313571
theorem B143563 : Blo 123787 143563 := bstep (se 1 (by rfl) ⟨107672, by rfl⟩ : syracuseStep 143563 = 215345) B215345
theorem B962765 : Blo 123787 962765 := bstep (se 3 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 962765 = 361037) B361037
theorem B143671 : Blo 123787 143671 := bstep (se 1 (by rfl) ⟨107753, by rfl⟩ : syracuseStep 143671 = 215507) B215507
theorem B635201 : Blo 123787 635201 := bstep (se 2 (by rfl) ⟨238200, by rfl⟩ : syracuseStep 635201 = 476401) B476401
theorem B405911 : Blo 123787 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B2241037 : Blo 123787 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B963251 : Blo 123787 963251 := bstep (se 1 (by rfl) ⟨722438, by rfl⟩ : syracuseStep 963251 = 1444877) B1444877
theorem B209675 : Blo 123787 209675 := bstep (se 1 (by rfl) ⟨157256, by rfl⟩ : syracuseStep 209675 = 314513) B314513
theorem B242507 : Blo 123787 242507 := bstep (se 1 (by rfl) ⟨181880, by rfl⟩ : syracuseStep 242507 = 363761) B363761
theorem B242561 : Blo 123787 242561 := bstep (se 2 (by rfl) ⟨90960, by rfl⟩ : syracuseStep 242561 = 181921) B181921
theorem B209803 : Blo 123787 209803 := bstep (se 1 (by rfl) ⟨157352, by rfl⟩ : syracuseStep 209803 = 314705) B314705
theorem B406475 : Blo 123787 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B177113 : Blo 123787 177113 := bstep (se 2 (by rfl) ⟨66417, by rfl⟩ : syracuseStep 177113 = 132835) B132835
theorem B209945 : Blo 123787 209945 := bstep (se 2 (by rfl) ⟨78729, by rfl⟩ : syracuseStep 209945 = 157459) B157459
theorem B635969 : Blo 123787 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B210073 : Blo 123787 210073 := bstep (se 2 (by rfl) ⟨78777, by rfl⟩ : syracuseStep 210073 = 157555) B157555
theorem B406873 : Blo 123787 406873 := bstep (se 2 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 406873 = 305155) B305155
theorem B472499 : Blo 123787 472499 := bstep (se 1 (by rfl) ⟨354374, by rfl⟩ : syracuseStep 472499 = 708749) B708749
theorem B1553843 : Blo 123787 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B472513 : Blo 123787 472513 := bstep (se 2 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 472513 = 354385) B354385
theorem B177751 : Blo 123787 177751 := bstep (se 1 (by rfl) ⟨133313, by rfl⟩ : syracuseStep 177751 = 266627) B266627
theorem B210647 : Blo 123787 210647 := bstep (se 1 (by rfl) ⟨157985, by rfl⟩ : syracuseStep 210647 = 315971) B315971
theorem B210775 : Blo 123787 210775 := bstep (se 1 (by rfl) ⟨158081, by rfl⟩ : syracuseStep 210775 = 316163) B316163
theorem B2176885 : Blo 123787 2176885 := bstep (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) B204083
theorem B15677509 : Blo 123787 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B964709 : Blo 123787 964709 := bstep (se 4 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 964709 = 180883) B180883
theorem B637145 : Blo 123787 637145 := bstep (se 2 (by rfl) ⟨238929, by rfl⟩ : syracuseStep 637145 = 477859) B477859
theorem B178571 : Blo 123787 178571 := bstep (se 1 (by rfl) ⟨133928, by rfl⟩ : syracuseStep 178571 = 267857) B267857
theorem B211403 : Blo 123787 211403 := bstep (se 1 (by rfl) ⟨158552, by rfl⟩ : syracuseStep 211403 = 317105) B317105
theorem B408115 : Blo 123787 408115 := bstep (se 1 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 408115 = 612173) B612173
theorem B211531 : Blo 123787 211531 := bstep (se 1 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 211531 = 317297) B317297
theorem B965195 : Blo 123787 965195 := bstep (se 1 (by rfl) ⟨723896, by rfl⟩ : syracuseStep 965195 = 1447793) B1447793
theorem B506519 : Blo 123787 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B211673 : Blo 123787 211673 := bstep (se 2 (by rfl) ⟨79377, by rfl⟩ : syracuseStep 211673 = 158755) B158755
theorem B604945 : Blo 123787 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B211801 : Blo 123787 211801 := bstep (se 2 (by rfl) ⟨79425, by rfl⟩ : syracuseStep 211801 = 158851) B158851
theorem B539779 : Blo 123787 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B474443 : Blo 123787 474443 := bstep (se 1 (by rfl) ⟨355832, by rfl⟩ : syracuseStep 474443 = 711665) B711665
theorem B474457 : Blo 123787 474457 := bstep (se 2 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 474457 = 355843) B355843
theorem B212375 : Blo 123787 212375 := bstep (se 1 (by rfl) ⟨159281, by rfl⟩ : syracuseStep 212375 = 318563) B318563
theorem B540121 : Blo 123787 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B212503 : Blo 123787 212503 := bstep (se 1 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 212503 = 318755) B318755
theorem B638765 : Blo 123787 638765 := bstep (se 3 (by rfl) ⟨119768, by rfl⟩ : syracuseStep 638765 = 239537) B239537
theorem B901165 : Blo 123787 901165 := bstep (se 3 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 901165 = 337937) B337937
theorem B278603 : Blo 123787 278603 := bstep (se 1 (by rfl) ⟨208952, by rfl⟩ : syracuseStep 278603 = 417905) B417905
theorem B278657 : Blo 123787 278657 := bstep (se 2 (by rfl) ⟨104496, by rfl⟩ : syracuseStep 278657 = 208993) B208993
theorem B213131 : Blo 123787 213131 := bstep (se 1 (by rfl) ⟨159848, by rfl⟩ : syracuseStep 213131 = 319697) B319697
theorem B213259 : Blo 123787 213259 := bstep (se 1 (by rfl) ⟨159944, by rfl⟩ : syracuseStep 213259 = 319889) B319889
theorem B475415 : Blo 123787 475415 := bstep (se 1 (by rfl) ⟨356561, by rfl⟩ : syracuseStep 475415 = 713123) B713123
theorem B901421 : Blo 123787 901421 := bstep (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) B338033
theorem B278873 : Blo 123787 278873 := bstep (se 2 (by rfl) ⟨104577, by rfl⟩ : syracuseStep 278873 = 209155) B209155
theorem B541079 : Blo 123787 541079 := bstep (se 1 (by rfl) ⟨405809, by rfl⟩ : syracuseStep 541079 = 811619) B811619
theorem B213401 : Blo 123787 213401 := bstep (se 2 (by rfl) ⟨80025, by rfl⟩ : syracuseStep 213401 = 160051) B160051
theorem B278963 : Blo 123787 278963 := bstep (se 1 (by rfl) ⟨209222, by rfl⟩ : syracuseStep 278963 = 418445) B418445
theorem B278999 : Blo 123787 278999 := bstep (se 1 (by rfl) ⟨209249, by rfl⟩ : syracuseStep 278999 = 418499) B418499
theorem B213529 : Blo 123787 213529 := bstep (se 2 (by rfl) ⟨80073, by rfl⟩ : syracuseStep 213529 = 160147) B160147
theorem B705125 : Blo 123787 705125 := bstep (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) B132211
theorem B279179 : Blo 123787 279179 := bstep (se 1 (by rfl) ⟨209384, by rfl⟩ : syracuseStep 279179 = 418769) B418769
theorem B279233 : Blo 123787 279233 := bstep (se 2 (by rfl) ⟨104712, by rfl⟩ : syracuseStep 279233 = 209425) B209425
theorem B1164077 : Blo 123787 1164077 := bstep (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) B436529
theorem B279449 : Blo 123787 279449 := bstep (se 2 (by rfl) ⟨104793, by rfl⟩ : syracuseStep 279449 = 209587) B209587
theorem B279539 : Blo 123787 279539 := bstep (se 1 (by rfl) ⟨209654, by rfl⟩ : syracuseStep 279539 = 419309) B419309
theorem B279575 : Blo 123787 279575 := bstep (se 1 (by rfl) ⟨209681, by rfl⟩ : syracuseStep 279575 = 419363) B419363
theorem B705581 : Blo 123787 705581 := bstep (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) B264593
theorem B214103 : Blo 123787 214103 := bstep (se 1 (by rfl) ⟨160577, by rfl⟩ : syracuseStep 214103 = 321155) B321155
theorem B279755 : Blo 123787 279755 := bstep (se 1 (by rfl) ⟨209816, by rfl⟩ : syracuseStep 279755 = 419633) B419633
theorem B214231 : Blo 123787 214231 := bstep (se 1 (by rfl) ⟨160673, by rfl⟩ : syracuseStep 214231 = 321347) B321347
theorem B279809 : Blo 123787 279809 := bstep (se 2 (by rfl) ⟨104928, by rfl⟩ : syracuseStep 279809 = 209857) B209857
theorem B280025 : Blo 123787 280025 := bstep (se 2 (by rfl) ⟨105009, by rfl⟩ : syracuseStep 280025 = 210019) B210019
theorem B476675 : Blo 123787 476675 := bstep (se 1 (by rfl) ⟨357506, by rfl⟩ : syracuseStep 476675 = 715013) B715013
theorem B280115 : Blo 123787 280115 := bstep (se 1 (by rfl) ⟨210086, by rfl⟩ : syracuseStep 280115 = 420173) B420173
theorem B280151 : Blo 123787 280151 := bstep (se 1 (by rfl) ⟨210113, by rfl⟩ : syracuseStep 280151 = 420227) B420227
theorem B706265 : Blo 123787 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B280331 : Blo 123787 280331 := bstep (se 1 (by rfl) ⟨210248, by rfl⟩ : syracuseStep 280331 = 420497) B420497
theorem B280385 : Blo 123787 280385 := bstep (se 2 (by rfl) ⟨105144, by rfl⟩ : syracuseStep 280385 = 210289) B210289
theorem B214859 : Blo 123787 214859 := bstep (se 1 (by rfl) ⟨161144, by rfl⟩ : syracuseStep 214859 = 322289) B322289
theorem B214987 : Blo 123787 214987 := bstep (se 1 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 214987 = 322481) B322481
theorem B215063 : Blo 123787 215063 := bstep (se 1 (by rfl) ⟨161297, by rfl⟩ : syracuseStep 215063 = 322595) B322595
theorem B280601 : Blo 123787 280601 := bstep (se 2 (by rfl) ⟨105225, by rfl⟩ : syracuseStep 280601 = 210451) B210451
theorem B542771 : Blo 123787 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B313409 : Blo 123787 313409 := bstep (se 2 (by rfl) ⟨117528, by rfl⟩ : syracuseStep 313409 = 235057) B235057
theorem B215129 : Blo 123787 215129 := bstep (se 2 (by rfl) ⟨80673, by rfl⟩ : syracuseStep 215129 = 161347) B161347
theorem B280691 : Blo 123787 280691 := bstep (se 1 (by rfl) ⟨210518, by rfl⟩ : syracuseStep 280691 = 421037) B421037
theorem B280727 : Blo 123787 280727 := bstep (se 1 (by rfl) ⟨210545, by rfl⟩ : syracuseStep 280727 = 421091) B421091
theorem B379073 : Blo 123787 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B215257 : Blo 123787 215257 := bstep (se 2 (by rfl) ⟨80721, by rfl⟩ : syracuseStep 215257 = 161443) B161443
theorem B280907 : Blo 123787 280907 := bstep (se 1 (by rfl) ⟨210680, by rfl⟩ : syracuseStep 280907 = 421361) B421361
theorem B280961 : Blo 123787 280961 := bstep (se 2 (by rfl) ⟨105360, by rfl⟩ : syracuseStep 280961 = 210721) B210721
theorem B510553 : Blo 123787 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B281177 : Blo 123787 281177 := bstep (se 2 (by rfl) ⟨105441, by rfl⟩ : syracuseStep 281177 = 210883) B210883
theorem B281267 : Blo 123787 281267 := bstep (se 1 (by rfl) ⟨210950, by rfl⟩ : syracuseStep 281267 = 421901) B421901
theorem B9358037 : Blo 123787 9358037 := bstep (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) B219329
theorem B281303 : Blo 123787 281303 := bstep (se 1 (by rfl) ⟨210977, by rfl⟩ : syracuseStep 281303 = 421955) B421955
theorem B281483 : Blo 123787 281483 := bstep (se 1 (by rfl) ⟨211112, by rfl⟩ : syracuseStep 281483 = 422225) B422225
theorem B281537 : Blo 123787 281537 := bstep (se 2 (by rfl) ⟨105576, by rfl⟩ : syracuseStep 281537 = 211153) B211153
theorem B150679 : Blo 123787 150679 := bstep (se 1 (by rfl) ⟨113009, by rfl⟩ : syracuseStep 150679 = 226019) B226019
theorem B281753 : Blo 123787 281753 := bstep (se 2 (by rfl) ⟨105657, by rfl⟩ : syracuseStep 281753 = 211315) B211315
theorem B281843 : Blo 123787 281843 := bstep (se 1 (by rfl) ⟨211382, by rfl⟩ : syracuseStep 281843 = 422765) B422765
theorem B281879 : Blo 123787 281879 := bstep (se 1 (by rfl) ⟨211409, by rfl⟩ : syracuseStep 281879 = 422819) B422819
theorem B314675 : Blo 123787 314675 := bstep (se 1 (by rfl) ⟨236006, by rfl⟩ : syracuseStep 314675 = 472013) B472013
theorem B282059 : Blo 123787 282059 := bstep (se 1 (by rfl) ⟨211544, by rfl⟩ : syracuseStep 282059 = 423089) B423089
theorem B282113 : Blo 123787 282113 := bstep (se 2 (by rfl) ⟨105792, by rfl⟩ : syracuseStep 282113 = 211585) B211585
theorem B1363549 : Blo 123787 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B642653 : Blo 123787 642653 := bstep (se 3 (by rfl) ⟨120497, by rfl⟩ : syracuseStep 642653 = 240995) B240995
theorem B282329 : Blo 123787 282329 := bstep (se 2 (by rfl) ⟨105873, by rfl⟩ : syracuseStep 282329 = 211747) B211747
theorem B282419 : Blo 123787 282419 := bstep (se 1 (by rfl) ⟨211814, by rfl⟩ : syracuseStep 282419 = 423629) B423629
theorem B315211 : Blo 123787 315211 := bstep (se 1 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 315211 = 472817) B472817
theorem B282455 : Blo 123787 282455 := bstep (se 1 (by rfl) ⟨211841, by rfl⟩ : syracuseStep 282455 = 423683) B423683
theorem B905111 : Blo 123787 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B315353 : Blo 123787 315353 := bstep (se 2 (by rfl) ⟨118257, by rfl⟩ : syracuseStep 315353 = 236515) B236515
theorem B282635 : Blo 123787 282635 := bstep (se 1 (by rfl) ⟨211976, by rfl⟩ : syracuseStep 282635 = 423953) B423953
theorem B282689 : Blo 123787 282689 := bstep (se 2 (by rfl) ⟨106008, by rfl⟩ : syracuseStep 282689 = 212017) B212017
theorem B807185 : Blo 123787 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B282905 : Blo 123787 282905 := bstep (se 2 (by rfl) ⟨106089, by rfl⟩ : syracuseStep 282905 = 212179) B212179
theorem B905573 : Blo 123787 905573 := bstep (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) B169795
theorem B282995 : Blo 123787 282995 := bstep (se 1 (by rfl) ⟨212246, by rfl⟩ : syracuseStep 282995 = 424493) B424493
theorem B283031 : Blo 123787 283031 := bstep (se 1 (by rfl) ⟨212273, by rfl⟩ : syracuseStep 283031 = 424547) B424547
theorem B479789 : Blo 123787 479789 := bstep (se 3 (by rfl) ⟨89960, by rfl⟩ : syracuseStep 479789 = 179921) B179921
theorem B283211 : Blo 123787 283211 := bstep (se 1 (by rfl) ⟨212408, by rfl⟩ : syracuseStep 283211 = 424817) B424817
theorem B971365 : Blo 123787 971365 := bstep (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) B182131
theorem B283265 : Blo 123787 283265 := bstep (se 2 (by rfl) ⟨106224, by rfl⟩ : syracuseStep 283265 = 212449) B212449
theorem B545453 : Blo 123787 545453 := bstep (se 3 (by rfl) ⟨102272, by rfl⟩ : syracuseStep 545453 = 204545) B204545
theorem B316183 : Blo 123787 316183 := bstep (se 1 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 316183 = 474275) B474275
theorem B283481 : Blo 123787 283481 := bstep (se 2 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 283481 = 212611) B212611
theorem B283571 : Blo 123787 283571 := bstep (se 1 (by rfl) ⟨212678, by rfl⟩ : syracuseStep 283571 = 425357) B425357
theorem B283607 : Blo 123787 283607 := bstep (se 1 (by rfl) ⟨212705, by rfl⟩ : syracuseStep 283607 = 425411) B425411
theorem B283787 : Blo 123787 283787 := bstep (se 1 (by rfl) ⟨212840, by rfl⟩ : syracuseStep 283787 = 425681) B425681
theorem B283841 : Blo 123787 283841 := bstep (se 2 (by rfl) ⟨106440, by rfl⟩ : syracuseStep 283841 = 212881) B212881
theorem B316619 : Blo 123787 316619 := bstep (se 1 (by rfl) ⟨237464, by rfl⟩ : syracuseStep 316619 = 474929) B474929
theorem B480563 : Blo 123787 480563 := bstep (se 1 (by rfl) ⟨360422, by rfl⟩ : syracuseStep 480563 = 720845) B720845
theorem B185687 : Blo 123787 185687 := bstep (se 1 (by rfl) ⟨139265, by rfl⟩ : syracuseStep 185687 = 278531) B278531
theorem B185753 : Blo 123787 185753 := bstep (se 2 (by rfl) ⟨69657, by rfl⟩ : syracuseStep 185753 = 139315) B139315
theorem B284057 : Blo 123787 284057 := bstep (se 2 (by rfl) ⟨106521, by rfl⟩ : syracuseStep 284057 = 213043) B213043
theorem B382429 : Blo 123787 382429 := bstep (se 3 (by rfl) ⟨71705, by rfl⟩ : syracuseStep 382429 = 143411) B143411
theorem B284147 : Blo 123787 284147 := bstep (se 1 (by rfl) ⟨213110, by rfl⟩ : syracuseStep 284147 = 426221) B426221
theorem B513539 : Blo 123787 513539 := bstep (se 1 (by rfl) ⟨385154, by rfl⟩ : syracuseStep 513539 = 770309) B770309
theorem B185867 : Blo 123787 185867 := bstep (se 1 (by rfl) ⟨139400, by rfl⟩ : syracuseStep 185867 = 278801) B278801
theorem B185879 : Blo 123787 185879 := bstep (se 1 (by rfl) ⟨139409, by rfl⟩ : syracuseStep 185879 = 278819) B278819
theorem B284183 : Blo 123787 284183 := bstep (se 1 (by rfl) ⟨213137, by rfl⟩ : syracuseStep 284183 = 426275) B426275
theorem B448051 : Blo 123787 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B316993 : Blo 123787 316993 := bstep (se 2 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 316993 = 237745) B237745
theorem B185945 : Blo 123787 185945 := bstep (se 2 (by rfl) ⟨69729, by rfl⟩ : syracuseStep 185945 = 139459) B139459
theorem B644759 : Blo 123787 644759 := bstep (se 1 (by rfl) ⟨483569, by rfl⟩ : syracuseStep 644759 = 967139) B967139
theorem B186059 : Blo 123787 186059 := bstep (se 1 (by rfl) ⟨139544, by rfl⟩ : syracuseStep 186059 = 279089) B279089
theorem B284363 : Blo 123787 284363 := bstep (se 1 (by rfl) ⟨213272, by rfl⟩ : syracuseStep 284363 = 426545) B426545
theorem B4085453 : Blo 123787 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B186071 : Blo 123787 186071 := bstep (se 1 (by rfl) ⟨139553, by rfl⟩ : syracuseStep 186071 = 279107) B279107
theorem B284417 : Blo 123787 284417 := bstep (se 2 (by rfl) ⟨106656, by rfl⟩ : syracuseStep 284417 = 213313) B213313
theorem B186137 : Blo 123787 186137 := bstep (se 2 (by rfl) ⟨69801, by rfl⟩ : syracuseStep 186137 = 139603) B139603
theorem B186251 : Blo 123787 186251 := bstep (se 1 (by rfl) ⟨139688, by rfl⟩ : syracuseStep 186251 = 279377) B279377
theorem B186263 : Blo 123787 186263 := bstep (se 1 (by rfl) ⟨139697, by rfl⟩ : syracuseStep 186263 = 279395) B279395
theorem B579521 : Blo 123787 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B186329 : Blo 123787 186329 := bstep (se 2 (by rfl) ⟨69873, by rfl⟩ : syracuseStep 186329 = 139747) B139747
theorem B481241 : Blo 123787 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B284633 : Blo 123787 284633 := bstep (se 2 (by rfl) ⟨106737, by rfl⟩ : syracuseStep 284633 = 213475) B213475
theorem B284723 : Blo 123787 284723 := bstep (se 1 (by rfl) ⟨213542, by rfl⟩ : syracuseStep 284723 = 427085) B427085
theorem B186443 : Blo 123787 186443 := bstep (se 1 (by rfl) ⟨139832, by rfl⟩ : syracuseStep 186443 = 279665) B279665
theorem B186455 : Blo 123787 186455 := bstep (se 1 (by rfl) ⟨139841, by rfl⟩ : syracuseStep 186455 = 279683) B279683
theorem B284759 : Blo 123787 284759 := bstep (se 1 (by rfl) ⟨213569, by rfl⟩ : syracuseStep 284759 = 427139) B427139
theorem B546905 : Blo 123787 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B317591 : Blo 123787 317591 := bstep (se 1 (by rfl) ⟨238193, by rfl⟩ : syracuseStep 317591 = 476387) B476387
theorem B186521 : Blo 123787 186521 := bstep (se 2 (by rfl) ⟨69945, by rfl⟩ : syracuseStep 186521 = 139891) B139891
theorem B186635 : Blo 123787 186635 := bstep (se 1 (by rfl) ⟨139976, by rfl⟩ : syracuseStep 186635 = 279953) B279953
theorem B284939 : Blo 123787 284939 := bstep (se 1 (by rfl) ⟨213704, by rfl⟩ : syracuseStep 284939 = 427409) B427409
theorem B186647 : Blo 123787 186647 := bstep (se 1 (by rfl) ⟨139985, by rfl⟩ : syracuseStep 186647 = 279971) B279971
theorem B710957 : Blo 123787 710957 := bstep (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) B266609
theorem B317747 : Blo 123787 317747 := bstep (se 1 (by rfl) ⟨238310, by rfl⟩ : syracuseStep 317747 = 476621) B476621
theorem B284993 : Blo 123787 284993 := bstep (se 2 (by rfl) ⟨106872, by rfl⟩ : syracuseStep 284993 = 213745) B213745
theorem B186713 : Blo 123787 186713 := bstep (se 2 (by rfl) ⟨70017, by rfl⟩ : syracuseStep 186713 = 140035) B140035
theorem B186827 : Blo 123787 186827 := bstep (se 1 (by rfl) ⟨140120, by rfl⟩ : syracuseStep 186827 = 280241) B280241
theorem B186839 : Blo 123787 186839 := bstep (se 1 (by rfl) ⟨140129, by rfl⟩ : syracuseStep 186839 = 280259) B280259
theorem B186905 : Blo 123787 186905 := bstep (se 2 (by rfl) ⟨70089, by rfl⟩ : syracuseStep 186905 = 140179) B140179
theorem B285209 : Blo 123787 285209 := bstep (se 2 (by rfl) ⟨106953, by rfl⟩ : syracuseStep 285209 = 213907) B213907
theorem B645677 : Blo 123787 645677 := bstep (se 3 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 645677 = 242129) B242129
theorem B285299 : Blo 123787 285299 := bstep (se 1 (by rfl) ⟨213974, by rfl⟩ : syracuseStep 285299 = 427949) B427949
theorem B449155 : Blo 123787 449155 := bstep (se 1 (by rfl) ⟨336866, by rfl⟩ : syracuseStep 449155 = 673733) B673733
theorem B187019 : Blo 123787 187019 := bstep (se 1 (by rfl) ⟨140264, by rfl⟩ : syracuseStep 187019 = 280529) B280529
theorem B187031 : Blo 123787 187031 := bstep (se 1 (by rfl) ⟨140273, by rfl⟩ : syracuseStep 187031 = 280547) B280547
theorem B285335 : Blo 123787 285335 := bstep (se 1 (by rfl) ⟨214001, by rfl⟩ : syracuseStep 285335 = 428003) B428003
theorem B187097 : Blo 123787 187097 := bstep (se 2 (by rfl) ⟨70161, by rfl⟩ : syracuseStep 187097 = 140323) B140323
theorem B482051 : Blo 123787 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B187211 : Blo 123787 187211 := bstep (se 1 (by rfl) ⟨140408, by rfl⟩ : syracuseStep 187211 = 280817) B280817
theorem B285515 : Blo 123787 285515 := bstep (se 1 (by rfl) ⟨214136, by rfl⟩ : syracuseStep 285515 = 428273) B428273
theorem B187223 : Blo 123787 187223 := bstep (se 1 (by rfl) ⟨140417, by rfl⟩ : syracuseStep 187223 = 280835) B280835
theorem B285569 : Blo 123787 285569 := bstep (se 2 (by rfl) ⟨107088, by rfl⟩ : syracuseStep 285569 = 214177) B214177
theorem B187289 : Blo 123787 187289 := bstep (se 2 (by rfl) ⟨70233, by rfl⟩ : syracuseStep 187289 = 140467) B140467
theorem B318401 : Blo 123787 318401 := bstep (se 2 (by rfl) ⟨119400, by rfl⟩ : syracuseStep 318401 = 238801) B238801
theorem B187403 : Blo 123787 187403 := bstep (se 1 (by rfl) ⟨140552, by rfl⟩ : syracuseStep 187403 = 281105) B281105
theorem B187415 : Blo 123787 187415 := bstep (se 1 (by rfl) ⟨140561, by rfl⟩ : syracuseStep 187415 = 281123) B281123
theorem B187481 : Blo 123787 187481 := bstep (se 2 (by rfl) ⟨70305, by rfl⟩ : syracuseStep 187481 = 140611) B140611
theorem B285785 : Blo 123787 285785 := bstep (se 2 (by rfl) ⟨107169, by rfl⟩ : syracuseStep 285785 = 214339) B214339
theorem B285875 : Blo 123787 285875 := bstep (se 1 (by rfl) ⟨214406, by rfl⟩ : syracuseStep 285875 = 428813) B428813
theorem B187595 : Blo 123787 187595 := bstep (se 1 (by rfl) ⟨140696, by rfl⟩ : syracuseStep 187595 = 281393) B281393
theorem B482507 : Blo 123787 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B187607 : Blo 123787 187607 := bstep (se 1 (by rfl) ⟨140705, by rfl⟩ : syracuseStep 187607 = 281411) B281411
theorem B285911 : Blo 123787 285911 := bstep (se 1 (by rfl) ⟨214433, by rfl⟩ : syracuseStep 285911 = 428867) B428867
theorem B187673 : Blo 123787 187673 := bstep (se 2 (by rfl) ⟨70377, by rfl⟩ : syracuseStep 187673 = 140755) B140755
theorem B187787 : Blo 123787 187787 := bstep (se 1 (by rfl) ⟨140840, by rfl⟩ : syracuseStep 187787 = 281681) B281681
theorem B286091 : Blo 123787 286091 := bstep (se 1 (by rfl) ⟨214568, by rfl⟩ : syracuseStep 286091 = 429137) B429137
theorem B482705 : Blo 123787 482705 := bstep (se 2 (by rfl) ⟨181014, by rfl⟩ : syracuseStep 482705 = 362029) B362029
theorem B187799 : Blo 123787 187799 := bstep (se 1 (by rfl) ⟨140849, by rfl⟩ : syracuseStep 187799 = 281699) B281699
theorem B286145 : Blo 123787 286145 := bstep (se 2 (by rfl) ⟨107304, by rfl⟩ : syracuseStep 286145 = 214609) B214609
theorem B187865 : Blo 123787 187865 := bstep (se 2 (by rfl) ⟨70449, by rfl⟩ : syracuseStep 187865 = 140899) B140899
theorem B318937 : Blo 123787 318937 := bstep (se 2 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 318937 = 239203) B239203
theorem B1138211 : Blo 123787 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B187979 : Blo 123787 187979 := bstep (se 1 (by rfl) ⟨140984, by rfl⟩ : syracuseStep 187979 = 281969) B281969
theorem B187991 : Blo 123787 187991 := bstep (se 1 (by rfl) ⟨140993, by rfl⟩ : syracuseStep 187991 = 281987) B281987
theorem B188057 : Blo 123787 188057 := bstep (se 2 (by rfl) ⟨70521, by rfl⟩ : syracuseStep 188057 = 141043) B141043
theorem B286361 : Blo 123787 286361 := bstep (se 2 (by rfl) ⟨107385, by rfl⟩ : syracuseStep 286361 = 214771) B214771
theorem B286451 : Blo 123787 286451 := bstep (se 1 (by rfl) ⟨214838, by rfl⟩ : syracuseStep 286451 = 429677) B429677
theorem B188171 : Blo 123787 188171 := bstep (se 1 (by rfl) ⟨141128, by rfl⟩ : syracuseStep 188171 = 282257) B282257
theorem B188183 : Blo 123787 188183 := bstep (se 1 (by rfl) ⟨141137, by rfl⟩ : syracuseStep 188183 = 282275) B282275
theorem B286487 : Blo 123787 286487 := bstep (se 1 (by rfl) ⟨214865, by rfl⟩ : syracuseStep 286487 = 429731) B429731
theorem B188249 : Blo 123787 188249 := bstep (se 2 (by rfl) ⟨70593, by rfl⟩ : syracuseStep 188249 = 141187) B141187
theorem B1072997 : Blo 123787 1072997 := bstep (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) B201187
theorem B188363 : Blo 123787 188363 := bstep (se 1 (by rfl) ⟨141272, by rfl⟩ : syracuseStep 188363 = 282545) B282545
theorem B286667 : Blo 123787 286667 := bstep (se 1 (by rfl) ⟨215000, by rfl⟩ : syracuseStep 286667 = 430001) B430001
theorem B188375 : Blo 123787 188375 := bstep (se 1 (by rfl) ⟨141281, by rfl⟩ : syracuseStep 188375 = 282563) B282563
theorem B286721 : Blo 123787 286721 := bstep (se 2 (by rfl) ⟨107520, by rfl⟩ : syracuseStep 286721 = 215041) B215041
theorem B221195 : Blo 123787 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B188441 : Blo 123787 188441 := bstep (se 2 (by rfl) ⟨70665, by rfl⟩ : syracuseStep 188441 = 141331) B141331
theorem B450625 : Blo 123787 450625 := bstep (se 2 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 450625 = 337969) B337969
theorem B188555 : Blo 123787 188555 := bstep (se 1 (by rfl) ⟨141416, by rfl⟩ : syracuseStep 188555 = 282833) B282833
theorem B188567 : Blo 123787 188567 := bstep (se 1 (by rfl) ⟨141425, by rfl⟩ : syracuseStep 188567 = 282851) B282851
theorem B483479 : Blo 123787 483479 := bstep (se 1 (by rfl) ⟨362609, by rfl⟩ : syracuseStep 483479 = 725219) B725219
theorem B286913 : Blo 123787 286913 := bstep (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) B215185
theorem B188633 : Blo 123787 188633 := bstep (se 2 (by rfl) ⟨70737, by rfl⟩ : syracuseStep 188633 = 141475) B141475
theorem B286937 : Blo 123787 286937 := bstep (se 2 (by rfl) ⟨107601, by rfl⟩ : syracuseStep 286937 = 215203) B215203
theorem B418013 : Blo 123787 418013 := bstep (se 3 (by rfl) ⟨78377, by rfl⟩ : syracuseStep 418013 = 156755) B156755
theorem B942353 : Blo 123787 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B811309 : Blo 123787 811309 := bstep (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) B304241
theorem B287027 : Blo 123787 287027 := bstep (se 1 (by rfl) ⟨215270, by rfl⟩ : syracuseStep 287027 = 430541) B430541
theorem B188747 : Blo 123787 188747 := bstep (se 1 (by rfl) ⟨141560, by rfl⟩ : syracuseStep 188747 = 283121) B283121
theorem B188759 : Blo 123787 188759 := bstep (se 1 (by rfl) ⟨141569, by rfl⟩ : syracuseStep 188759 = 283139) B283139
theorem B287063 : Blo 123787 287063 := bstep (se 1 (by rfl) ⟨215297, by rfl⟩ : syracuseStep 287063 = 430595) B430595
theorem B483677 : Blo 123787 483677 := bstep (se 3 (by rfl) ⟨90689, by rfl⟩ : syracuseStep 483677 = 181379) B181379
theorem B680293 : Blo 123787 680293 := bstep (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) B127555
theorem B188825 : Blo 123787 188825 := bstep (se 2 (by rfl) ⟨70809, by rfl⟩ : syracuseStep 188825 = 141619) B141619
theorem B188939 : Blo 123787 188939 := bstep (se 1 (by rfl) ⟨141704, by rfl⟩ : syracuseStep 188939 = 283409) B283409
theorem B287243 : Blo 123787 287243 := bstep (se 1 (by rfl) ⟨215432, by rfl⟩ : syracuseStep 287243 = 430865) B430865
theorem B1073681 : Blo 123787 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B188951 : Blo 123787 188951 := bstep (se 1 (by rfl) ⟨141713, by rfl⟩ : syracuseStep 188951 = 283427) B283427
theorem B320051 : Blo 123787 320051 := bstep (se 1 (by rfl) ⟨240038, by rfl⟩ : syracuseStep 320051 = 480077) B480077
theorem B287297 : Blo 123787 287297 := bstep (se 2 (by rfl) ⟨107736, by rfl⟩ : syracuseStep 287297 = 215473) B215473
theorem B189017 : Blo 123787 189017 := bstep (se 2 (by rfl) ⟨70881, by rfl⟩ : syracuseStep 189017 = 141763) B141763
theorem B189131 : Blo 123787 189131 := bstep (se 1 (by rfl) ⟨141848, by rfl⟩ : syracuseStep 189131 = 283697) B283697
theorem B189143 : Blo 123787 189143 := bstep (se 1 (by rfl) ⟨141857, by rfl⟩ : syracuseStep 189143 = 283715) B283715
theorem B189209 : Blo 123787 189209 := bstep (se 2 (by rfl) ⟨70953, by rfl⟩ : syracuseStep 189209 = 141907) B141907
theorem B287513 : Blo 123787 287513 := bstep (se 2 (by rfl) ⟨107817, by rfl⟩ : syracuseStep 287513 = 215635) B215635
theorem B353099 : Blo 123787 353099 := bstep (se 1 (by rfl) ⟨264824, by rfl⟩ : syracuseStep 353099 = 529649) B529649
theorem B451403 : Blo 123787 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B320345 : Blo 123787 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B123787 : Blo 123787 123787 := bstep (se 1 (by rfl) ⟨92840, by rfl⟩ : syracuseStep 123787 = 185681) B185681
theorem B189323 : Blo 123787 189323 := bstep (se 1 (by rfl) ⟨141992, by rfl⟩ : syracuseStep 189323 = 283985) B283985
theorem B123799 : Blo 123787 123799 := bstep (se 1 (by rfl) ⟨92849, by rfl⟩ : syracuseStep 123799 = 185699) B185699
theorem B189335 : Blo 123787 189335 := bstep (se 1 (by rfl) ⟨142001, by rfl⟩ : syracuseStep 189335 = 284003) B284003
theorem B123819 : Blo 123787 123819 := bstep (se 1 (by rfl) ⟨92864, by rfl⟩ : syracuseStep 123819 = 185729) B185729
theorem B517043 : Blo 123787 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B123831 : Blo 123787 123831 := bstep (se 1 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 123831 = 185747) B185747
theorem B123851 : Blo 123787 123851 := bstep (se 1 (by rfl) ⟨92888, by rfl⟩ : syracuseStep 123851 = 185777) B185777
theorem B123863 : Blo 123787 123863 := bstep (se 1 (by rfl) ⟨92897, by rfl⟩ : syracuseStep 123863 = 185795) B185795
theorem B189401 : Blo 123787 189401 := bstep (se 2 (by rfl) ⟨71025, by rfl⟩ : syracuseStep 189401 = 142051) B142051
theorem B123883 : Blo 123787 123883 := bstep (se 1 (by rfl) ⟨92912, by rfl⟩ : syracuseStep 123883 = 185825) B185825
theorem B123895 : Blo 123787 123895 := bstep (se 1 (by rfl) ⟨92921, by rfl⟩ : syracuseStep 123895 = 185843) B185843
theorem B123915 : Blo 123787 123915 := bstep (se 1 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 123915 = 185873) B185873
theorem B123927 : Blo 123787 123927 := bstep (se 1 (by rfl) ⟨92945, by rfl⟩ : syracuseStep 123927 = 185891) B185891
theorem B123947 : Blo 123787 123947 := bstep (se 1 (by rfl) ⟨92960, by rfl⟩ : syracuseStep 123947 = 185921) B185921
theorem B123959 : Blo 123787 123959 := bstep (se 1 (by rfl) ⟨92969, by rfl⟩ : syracuseStep 123959 = 185939) B185939
theorem B123979 : Blo 123787 123979 := bstep (se 1 (by rfl) ⟨92984, by rfl⟩ : syracuseStep 123979 = 185969) B185969
theorem B189515 : Blo 123787 189515 := bstep (se 1 (by rfl) ⟨142136, by rfl⟩ : syracuseStep 189515 = 284273) B284273
theorem B123991 : Blo 123787 123991 := bstep (se 1 (by rfl) ⟨92993, by rfl⟩ : syracuseStep 123991 = 185987) B185987
theorem B189527 : Blo 123787 189527 := bstep (se 1 (by rfl) ⟨142145, by rfl⟩ : syracuseStep 189527 = 284291) B284291
theorem B124011 : Blo 123787 124011 := bstep (se 1 (by rfl) ⟨93008, by rfl⟩ : syracuseStep 124011 = 186017) B186017
theorem B124023 : Blo 123787 124023 := bstep (se 1 (by rfl) ⟨93017, by rfl⟩ : syracuseStep 124023 = 186035) B186035
theorem B156811 : Blo 123787 156811 := bstep (se 1 (by rfl) ⟨117608, by rfl⟩ : syracuseStep 156811 = 235217) B235217
theorem B124043 : Blo 123787 124043 := bstep (se 1 (by rfl) ⟨93032, by rfl⟩ : syracuseStep 124043 = 186065) B186065
theorem B124055 : Blo 123787 124055 := bstep (se 1 (by rfl) ⟨93041, by rfl⟩ : syracuseStep 124055 = 186083) B186083
theorem B189593 : Blo 123787 189593 := bstep (se 2 (by rfl) ⟨71097, by rfl⟩ : syracuseStep 189593 = 142195) B142195
theorem B124075 : Blo 123787 124075 := bstep (se 1 (by rfl) ⟨93056, by rfl⟩ : syracuseStep 124075 = 186113) B186113
theorem B124087 : Blo 123787 124087 := bstep (se 1 (by rfl) ⟨93065, by rfl⟩ : syracuseStep 124087 = 186131) B186131
theorem B124107 : Blo 123787 124107 := bstep (se 1 (by rfl) ⟨93080, by rfl⟩ : syracuseStep 124107 = 186161) B186161
theorem B124119 : Blo 123787 124119 := bstep (se 1 (by rfl) ⟨93089, by rfl⟩ : syracuseStep 124119 = 186179) B186179
theorem B353497 : Blo 123787 353497 := bstep (se 2 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 353497 = 265123) B265123
theorem B124139 : Blo 123787 124139 := bstep (se 1 (by rfl) ⟨93104, by rfl⟩ : syracuseStep 124139 = 186209) B186209
theorem B124151 : Blo 123787 124151 := bstep (se 1 (by rfl) ⟨93113, by rfl⟩ : syracuseStep 124151 = 186227) B186227
theorem B124171 : Blo 123787 124171 := bstep (se 1 (by rfl) ⟨93128, by rfl⟩ : syracuseStep 124171 = 186257) B186257
theorem B189707 : Blo 123787 189707 := bstep (se 1 (by rfl) ⟨142280, by rfl⟩ : syracuseStep 189707 = 284561) B284561
theorem B124183 : Blo 123787 124183 := bstep (se 1 (by rfl) ⟨93137, by rfl⟩ : syracuseStep 124183 = 186275) B186275
theorem B189719 : Blo 123787 189719 := bstep (se 1 (by rfl) ⟨142289, by rfl⟩ : syracuseStep 189719 = 284579) B284579
theorem B124203 : Blo 123787 124203 := bstep (se 1 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 124203 = 186305) B186305
theorem B124215 : Blo 123787 124215 := bstep (se 1 (by rfl) ⟨93161, by rfl⟩ : syracuseStep 124215 = 186323) B186323
theorem B419147 : Blo 123787 419147 := bstep (se 1 (by rfl) ⟨314360, by rfl⟩ : syracuseStep 419147 = 628721) B628721
theorem B124235 : Blo 123787 124235 := bstep (se 1 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 124235 = 186353) B186353
theorem B124247 : Blo 123787 124247 := bstep (se 1 (by rfl) ⟨93185, by rfl⟩ : syracuseStep 124247 = 186371) B186371
theorem B189785 : Blo 123787 189785 := bstep (se 2 (by rfl) ⟨71169, by rfl⟩ : syracuseStep 189785 = 142339) B142339
theorem B124267 : Blo 123787 124267 := bstep (se 1 (by rfl) ⟨93200, by rfl⟩ : syracuseStep 124267 = 186401) B186401
theorem B124279 : Blo 123787 124279 := bstep (se 1 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 124279 = 186419) B186419
theorem B124299 : Blo 123787 124299 := bstep (se 1 (by rfl) ⟨93224, by rfl⟩ : syracuseStep 124299 = 186449) B186449
theorem B157079 : Blo 123787 157079 := bstep (se 1 (by rfl) ⟨117809, by rfl⟩ : syracuseStep 157079 = 235619) B235619
theorem B124311 : Blo 123787 124311 := bstep (se 1 (by rfl) ⟨93233, by rfl⟩ : syracuseStep 124311 = 186467) B186467
theorem B124331 : Blo 123787 124331 := bstep (se 1 (by rfl) ⟨93248, by rfl⟩ : syracuseStep 124331 = 186497) B186497
theorem B124343 : Blo 123787 124343 := bstep (se 1 (by rfl) ⟨93257, by rfl⟩ : syracuseStep 124343 = 186515) B186515
theorem B124363 : Blo 123787 124363 := bstep (se 1 (by rfl) ⟨93272, by rfl⟩ : syracuseStep 124363 = 186545) B186545
theorem B189899 : Blo 123787 189899 := bstep (se 1 (by rfl) ⟨142424, by rfl⟩ : syracuseStep 189899 = 284849) B284849
theorem B124375 : Blo 123787 124375 := bstep (se 1 (by rfl) ⟨93281, by rfl⟩ : syracuseStep 124375 = 186563) B186563
theorem B189911 : Blo 123787 189911 := bstep (se 1 (by rfl) ⟨142433, by rfl⟩ : syracuseStep 189911 = 284867) B284867
theorem B124395 : Blo 123787 124395 := bstep (se 1 (by rfl) ⟨93296, by rfl⟩ : syracuseStep 124395 = 186593) B186593
theorem B124407 : Blo 123787 124407 := bstep (se 1 (by rfl) ⟨93305, by rfl⟩ : syracuseStep 124407 = 186611) B186611
theorem B124427 : Blo 123787 124427 := bstep (se 1 (by rfl) ⟨93320, by rfl⟩ : syracuseStep 124427 = 186641) B186641
theorem B124439 : Blo 123787 124439 := bstep (se 1 (by rfl) ⟨93329, by rfl⟩ : syracuseStep 124439 = 186659) B186659
theorem B189977 : Blo 123787 189977 := bstep (se 2 (by rfl) ⟨71241, by rfl⟩ : syracuseStep 189977 = 142483) B142483
theorem B124459 : Blo 123787 124459 := bstep (se 1 (by rfl) ⟨93344, by rfl⟩ : syracuseStep 124459 = 186689) B186689
theorem B124471 : Blo 123787 124471 := bstep (se 1 (by rfl) ⟨93353, by rfl⟩ : syracuseStep 124471 = 186707) B186707
theorem B124491 : Blo 123787 124491 := bstep (se 1 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 124491 = 186737) B186737
theorem B124503 : Blo 123787 124503 := bstep (se 1 (by rfl) ⟨93377, by rfl⟩ : syracuseStep 124503 = 186755) B186755
theorem B419417 : Blo 123787 419417 := bstep (se 2 (by rfl) ⟨157281, by rfl⟩ : syracuseStep 419417 = 314563) B314563
theorem B124523 : Blo 123787 124523 := bstep (se 1 (by rfl) ⟨93392, by rfl⟩ : syracuseStep 124523 = 186785) B186785
theorem B124535 : Blo 123787 124535 := bstep (se 1 (by rfl) ⟨93401, by rfl⟩ : syracuseStep 124535 = 186803) B186803
theorem B124555 : Blo 123787 124555 := bstep (se 1 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 124555 = 186833) B186833
theorem B190091 : Blo 123787 190091 := bstep (se 1 (by rfl) ⟨142568, by rfl⟩ : syracuseStep 190091 = 285137) B285137
theorem B124567 : Blo 123787 124567 := bstep (se 1 (by rfl) ⟨93425, by rfl⟩ : syracuseStep 124567 = 186851) B186851
theorem B190103 : Blo 123787 190103 := bstep (se 1 (by rfl) ⟨142577, by rfl⟩ : syracuseStep 190103 = 285155) B285155
theorem B124587 : Blo 123787 124587 := bstep (se 1 (by rfl) ⟨93440, by rfl⟩ : syracuseStep 124587 = 186881) B186881
theorem B124599 : Blo 123787 124599 := bstep (se 1 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 124599 = 186899) B186899
theorem B124619 : Blo 123787 124619 := bstep (se 1 (by rfl) ⟨93464, by rfl⟩ : syracuseStep 124619 = 186929) B186929
theorem B124631 : Blo 123787 124631 := bstep (se 1 (by rfl) ⟨93473, by rfl⟩ : syracuseStep 124631 = 186947) B186947
theorem B190169 : Blo 123787 190169 := bstep (se 2 (by rfl) ⟨71313, by rfl⟩ : syracuseStep 190169 = 142627) B142627
theorem B517853 : Blo 123787 517853 := bstep (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) B194195
theorem B124651 : Blo 123787 124651 := bstep (se 1 (by rfl) ⟨93488, by rfl⟩ : syracuseStep 124651 = 186977) B186977
theorem B124663 : Blo 123787 124663 := bstep (se 1 (by rfl) ⟨93497, by rfl⟩ : syracuseStep 124663 = 186995) B186995
theorem B124683 : Blo 123787 124683 := bstep (se 1 (by rfl) ⟨93512, by rfl⟩ : syracuseStep 124683 = 187025) B187025
theorem B124695 : Blo 123787 124695 := bstep (se 1 (by rfl) ⟨93521, by rfl⟩ : syracuseStep 124695 = 187043) B187043
theorem B124715 : Blo 123787 124715 := bstep (se 1 (by rfl) ⟨93536, by rfl⟩ : syracuseStep 124715 = 187073) B187073
theorem B583469 : Blo 123787 583469 := bstep (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) B218801
theorem B124727 : Blo 123787 124727 := bstep (se 1 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 124727 = 187091) B187091
theorem B124747 : Blo 123787 124747 := bstep (se 1 (by rfl) ⟨93560, by rfl⟩ : syracuseStep 124747 = 187121) B187121
theorem B190283 : Blo 123787 190283 := bstep (se 1 (by rfl) ⟨142712, by rfl⟩ : syracuseStep 190283 = 285425) B285425
theorem B124759 : Blo 123787 124759 := bstep (se 1 (by rfl) ⟨93569, by rfl⟩ : syracuseStep 124759 = 187139) B187139
theorem B190295 : Blo 123787 190295 := bstep (se 1 (by rfl) ⟨142721, by rfl⟩ : syracuseStep 190295 = 285443) B285443
theorem B681821 : Blo 123787 681821 := bstep (se 3 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 681821 = 255683) B255683
theorem B124779 : Blo 123787 124779 := bstep (se 1 (by rfl) ⟨93584, by rfl⟩ : syracuseStep 124779 = 187169) B187169
theorem B124791 : Blo 123787 124791 := bstep (se 1 (by rfl) ⟨93593, by rfl⟩ : syracuseStep 124791 = 187187) B187187
theorem B124811 : Blo 123787 124811 := bstep (se 1 (by rfl) ⟨93608, by rfl⟩ : syracuseStep 124811 = 187217) B187217
theorem B124823 : Blo 123787 124823 := bstep (se 1 (by rfl) ⟨93617, by rfl⟩ : syracuseStep 124823 = 187235) B187235
theorem B190361 : Blo 123787 190361 := bstep (se 2 (by rfl) ⟨71385, by rfl⟩ : syracuseStep 190361 = 142771) B142771
theorem B124843 : Blo 123787 124843 := bstep (se 1 (by rfl) ⟨93632, by rfl⟩ : syracuseStep 124843 = 187265) B187265
theorem B124855 : Blo 123787 124855 := bstep (se 1 (by rfl) ⟨93641, by rfl⟩ : syracuseStep 124855 = 187283) B187283
theorem B124875 : Blo 123787 124875 := bstep (se 1 (by rfl) ⟨93656, by rfl⟩ : syracuseStep 124875 = 187313) B187313
theorem B124887 : Blo 123787 124887 := bstep (se 1 (by rfl) ⟨93665, by rfl⟩ : syracuseStep 124887 = 187331) B187331
theorem B124907 : Blo 123787 124907 := bstep (se 1 (by rfl) ⟨93680, by rfl⟩ : syracuseStep 124907 = 187361) B187361
theorem B124919 : Blo 123787 124919 := bstep (se 1 (by rfl) ⟨93689, by rfl⟩ : syracuseStep 124919 = 187379) B187379
theorem B124939 : Blo 123787 124939 := bstep (se 1 (by rfl) ⟨93704, by rfl⟩ : syracuseStep 124939 = 187409) B187409
theorem B190475 : Blo 123787 190475 := bstep (se 1 (by rfl) ⟨142856, by rfl⟩ : syracuseStep 190475 = 285713) B285713
theorem B124951 : Blo 123787 124951 := bstep (se 1 (by rfl) ⟨93713, by rfl⟩ : syracuseStep 124951 = 187427) B187427
theorem B190487 : Blo 123787 190487 := bstep (se 1 (by rfl) ⟨142865, by rfl⟩ : syracuseStep 190487 = 285731) B285731
theorem B124971 : Blo 123787 124971 := bstep (se 1 (by rfl) ⟨93728, by rfl⟩ : syracuseStep 124971 = 187457) B187457
theorem B124983 : Blo 123787 124983 := bstep (se 1 (by rfl) ⟨93737, by rfl⟩ : syracuseStep 124983 = 187475) B187475
theorem B125003 : Blo 123787 125003 := bstep (se 1 (by rfl) ⟨93752, by rfl⟩ : syracuseStep 125003 = 187505) B187505
theorem B157783 : Blo 123787 157783 := bstep (se 1 (by rfl) ⟨118337, by rfl⟩ : syracuseStep 157783 = 236675) B236675
theorem B125015 : Blo 123787 125015 := bstep (se 1 (by rfl) ⟨93761, by rfl⟩ : syracuseStep 125015 = 187523) B187523
theorem B190553 : Blo 123787 190553 := bstep (se 2 (by rfl) ⟨71457, by rfl⟩ : syracuseStep 190553 = 142915) B142915
theorem B125035 : Blo 123787 125035 := bstep (se 1 (by rfl) ⟨93776, by rfl⟩ : syracuseStep 125035 = 187553) B187553
theorem B125047 : Blo 123787 125047 := bstep (se 1 (by rfl) ⟨93785, by rfl⟩ : syracuseStep 125047 = 187571) B187571
theorem B125067 : Blo 123787 125067 := bstep (se 1 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 125067 = 187601) B187601
theorem B125079 : Blo 123787 125079 := bstep (se 1 (by rfl) ⟨93809, by rfl⟩ : syracuseStep 125079 = 187619) B187619
theorem B125099 : Blo 123787 125099 := bstep (se 1 (by rfl) ⟨93824, by rfl⟩ : syracuseStep 125099 = 187649) B187649
theorem B223411 : Blo 123787 223411 := bstep (se 1 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 223411 = 335117) B335117
theorem B125111 : Blo 123787 125111 := bstep (se 1 (by rfl) ⟨93833, by rfl⟩ : syracuseStep 125111 = 187667) B187667
theorem B125131 : Blo 123787 125131 := bstep (se 1 (by rfl) ⟨93848, by rfl⟩ : syracuseStep 125131 = 187697) B187697
theorem B190667 : Blo 123787 190667 := bstep (se 1 (by rfl) ⟨143000, by rfl⟩ : syracuseStep 190667 = 286001) B286001
theorem B125143 : Blo 123787 125143 := bstep (se 1 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 125143 = 187715) B187715
theorem B190679 : Blo 123787 190679 := bstep (se 1 (by rfl) ⟨143009, by rfl⟩ : syracuseStep 190679 = 286019) B286019
theorem B125163 : Blo 123787 125163 := bstep (se 1 (by rfl) ⟨93872, by rfl⟩ : syracuseStep 125163 = 187745) B187745
theorem B125175 : Blo 123787 125175 := bstep (se 1 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 125175 = 187763) B187763
theorem B125195 : Blo 123787 125195 := bstep (se 1 (by rfl) ⟨93896, by rfl⟩ : syracuseStep 125195 = 187793) B187793
theorem B420119 : Blo 123787 420119 := bstep (se 1 (by rfl) ⟨315089, by rfl⟩ : syracuseStep 420119 = 630179) B630179
theorem B125207 : Blo 123787 125207 := bstep (se 1 (by rfl) ⟨93905, by rfl⟩ : syracuseStep 125207 = 187811) B187811
theorem B190745 : Blo 123787 190745 := bstep (se 2 (by rfl) ⟨71529, by rfl⟩ : syracuseStep 190745 = 143059) B143059
theorem B125227 : Blo 123787 125227 := bstep (se 1 (by rfl) ⟨93920, by rfl⟩ : syracuseStep 125227 = 187841) B187841
theorem B125239 : Blo 123787 125239 := bstep (se 1 (by rfl) ⟨93929, by rfl⟩ : syracuseStep 125239 = 187859) B187859
theorem B125259 : Blo 123787 125259 := bstep (se 1 (by rfl) ⟨93944, by rfl⟩ : syracuseStep 125259 = 187889) B187889
theorem B125271 : Blo 123787 125271 := bstep (se 1 (by rfl) ⟨93953, by rfl⟩ : syracuseStep 125271 = 187907) B187907
theorem B125291 : Blo 123787 125291 := bstep (se 1 (by rfl) ⟨93968, by rfl⟩ : syracuseStep 125291 = 187937) B187937
theorem B125303 : Blo 123787 125303 := bstep (se 1 (by rfl) ⟨93977, by rfl⟩ : syracuseStep 125303 = 187955) B187955
theorem B125323 : Blo 123787 125323 := bstep (se 1 (by rfl) ⟨93992, by rfl⟩ : syracuseStep 125323 = 187985) B187985
theorem B190859 : Blo 123787 190859 := bstep (se 1 (by rfl) ⟨143144, by rfl⟩ : syracuseStep 190859 = 286289) B286289
theorem B125335 : Blo 123787 125335 := bstep (se 1 (by rfl) ⟨94001, by rfl⟩ : syracuseStep 125335 = 188003) B188003
theorem B190871 : Blo 123787 190871 := bstep (se 1 (by rfl) ⟨143153, by rfl⟩ : syracuseStep 190871 = 286307) B286307
theorem B125355 : Blo 123787 125355 := bstep (se 1 (by rfl) ⟨94016, by rfl⟩ : syracuseStep 125355 = 188033) B188033
theorem B354739 : Blo 123787 354739 := bstep (se 1 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 354739 = 532109) B532109
theorem B125367 : Blo 123787 125367 := bstep (se 1 (by rfl) ⟨94025, by rfl⟩ : syracuseStep 125367 = 188051) B188051
theorem B125387 : Blo 123787 125387 := bstep (se 1 (by rfl) ⟨94040, by rfl⟩ : syracuseStep 125387 = 188081) B188081
theorem B321995 : Blo 123787 321995 := bstep (se 1 (by rfl) ⟨241496, by rfl⟩ : syracuseStep 321995 = 482993) B482993
theorem B125399 : Blo 123787 125399 := bstep (se 1 (by rfl) ⟨94049, by rfl⟩ : syracuseStep 125399 = 188099) B188099
theorem B190937 : Blo 123787 190937 := bstep (se 2 (by rfl) ⟨71601, by rfl⟩ : syracuseStep 190937 = 143203) B143203
theorem B125419 : Blo 123787 125419 := bstep (se 1 (by rfl) ⟨94064, by rfl⟩ : syracuseStep 125419 = 188129) B188129
theorem B125431 : Blo 123787 125431 := bstep (se 1 (by rfl) ⟨94073, by rfl⟩ : syracuseStep 125431 = 188147) B188147
theorem B125451 : Blo 123787 125451 := bstep (se 1 (by rfl) ⟨94088, by rfl⟩ : syracuseStep 125451 = 188177) B188177
theorem B125463 : Blo 123787 125463 := bstep (se 1 (by rfl) ⟨94097, by rfl⟩ : syracuseStep 125463 = 188195) B188195
theorem B125483 : Blo 123787 125483 := bstep (se 1 (by rfl) ⟨94112, by rfl⟩ : syracuseStep 125483 = 188225) B188225
theorem B125495 : Blo 123787 125495 := bstep (se 1 (by rfl) ⟨94121, by rfl⟩ : syracuseStep 125495 = 188243) B188243
theorem B125515 : Blo 123787 125515 := bstep (se 1 (by rfl) ⟨94136, by rfl⟩ : syracuseStep 125515 = 188273) B188273
theorem B191051 : Blo 123787 191051 := bstep (se 1 (by rfl) ⟨143288, by rfl⟩ : syracuseStep 191051 = 286577) B286577
theorem B125527 : Blo 123787 125527 := bstep (se 1 (by rfl) ⟨94145, by rfl⟩ : syracuseStep 125527 = 188291) B188291
theorem B191063 : Blo 123787 191063 := bstep (se 1 (by rfl) ⟨143297, by rfl⟩ : syracuseStep 191063 = 286595) B286595
theorem B125547 : Blo 123787 125547 := bstep (se 1 (by rfl) ⟨94160, by rfl⟩ : syracuseStep 125547 = 188321) B188321
theorem B125559 : Blo 123787 125559 := bstep (se 1 (by rfl) ⟨94169, by rfl⟩ : syracuseStep 125559 = 188339) B188339
theorem B125579 : Blo 123787 125579 := bstep (se 1 (by rfl) ⟨94184, by rfl⟩ : syracuseStep 125579 = 188369) B188369
theorem B125591 : Blo 123787 125591 := bstep (se 1 (by rfl) ⟨94193, by rfl⟩ : syracuseStep 125591 = 188387) B188387
theorem B191129 : Blo 123787 191129 := bstep (se 2 (by rfl) ⟨71673, by rfl⟩ : syracuseStep 191129 = 143347) B143347
theorem B125611 : Blo 123787 125611 := bstep (se 1 (by rfl) ⟨94208, by rfl⟩ : syracuseStep 125611 = 188417) B188417
theorem B125623 : Blo 123787 125623 := bstep (se 1 (by rfl) ⟨94217, by rfl⟩ : syracuseStep 125623 = 188435) B188435
theorem B125643 : Blo 123787 125643 := bstep (se 1 (by rfl) ⟨94232, by rfl⟩ : syracuseStep 125643 = 188465) B188465
theorem B125655 : Blo 123787 125655 := bstep (se 1 (by rfl) ⟨94241, by rfl⟩ : syracuseStep 125655 = 188483) B188483
theorem B125675 : Blo 123787 125675 := bstep (se 1 (by rfl) ⟨94256, by rfl⟩ : syracuseStep 125675 = 188513) B188513
theorem B125687 : Blo 123787 125687 := bstep (se 1 (by rfl) ⟨94265, by rfl⟩ : syracuseStep 125687 = 188531) B188531
theorem B125707 : Blo 123787 125707 := bstep (se 1 (by rfl) ⟨94280, by rfl⟩ : syracuseStep 125707 = 188561) B188561
theorem B191243 : Blo 123787 191243 := bstep (se 1 (by rfl) ⟨143432, by rfl⟩ : syracuseStep 191243 = 286865) B286865
theorem B125719 : Blo 123787 125719 := bstep (se 1 (by rfl) ⟨94289, by rfl⟩ : syracuseStep 125719 = 188579) B188579
theorem B191255 : Blo 123787 191255 := bstep (se 1 (by rfl) ⟨143441, by rfl⟩ : syracuseStep 191255 = 286883) B286883
theorem B125739 : Blo 123787 125739 := bstep (se 1 (by rfl) ⟨94304, by rfl⟩ : syracuseStep 125739 = 188609) B188609
theorem B420659 : Blo 123787 420659 := bstep (se 1 (by rfl) ⟨315494, by rfl⟩ : syracuseStep 420659 = 630989) B630989
theorem B125751 : Blo 123787 125751 := bstep (se 1 (by rfl) ⟨94313, by rfl⟩ : syracuseStep 125751 = 188627) B188627
theorem B125771 : Blo 123787 125771 := bstep (se 1 (by rfl) ⟨94328, by rfl⟩ : syracuseStep 125771 = 188657) B188657
theorem B125783 : Blo 123787 125783 := bstep (se 1 (by rfl) ⟨94337, by rfl⟩ : syracuseStep 125783 = 188675) B188675
theorem B191321 : Blo 123787 191321 := bstep (se 2 (by rfl) ⟨71745, by rfl⟩ : syracuseStep 191321 = 143491) B143491
theorem B125803 : Blo 123787 125803 := bstep (se 1 (by rfl) ⟨94352, by rfl⟩ : syracuseStep 125803 = 188705) B188705
theorem B125815 : Blo 123787 125815 := bstep (se 1 (by rfl) ⟨94361, by rfl⟩ : syracuseStep 125815 = 188723) B188723
theorem B125835 : Blo 123787 125835 := bstep (se 1 (by rfl) ⟨94376, by rfl⟩ : syracuseStep 125835 = 188753) B188753
theorem B125847 : Blo 123787 125847 := bstep (se 1 (by rfl) ⟨94385, by rfl⟩ : syracuseStep 125847 = 188771) B188771
theorem B125867 : Blo 123787 125867 := bstep (se 1 (by rfl) ⟨94400, by rfl⟩ : syracuseStep 125867 = 188801) B188801
theorem B125879 : Blo 123787 125879 := bstep (se 1 (by rfl) ⟨94409, by rfl⟩ : syracuseStep 125879 = 188819) B188819
theorem B125899 : Blo 123787 125899 := bstep (se 1 (by rfl) ⟨94424, by rfl⟩ : syracuseStep 125899 = 188849) B188849
theorem B191435 : Blo 123787 191435 := bstep (se 1 (by rfl) ⟨143576, by rfl⟩ : syracuseStep 191435 = 287153) B287153
theorem B125911 : Blo 123787 125911 := bstep (se 1 (by rfl) ⟨94433, by rfl⟩ : syracuseStep 125911 = 188867) B188867
theorem B191447 : Blo 123787 191447 := bstep (se 1 (by rfl) ⟨143585, by rfl⟩ : syracuseStep 191447 = 287171) B287171
theorem B125931 : Blo 123787 125931 := bstep (se 1 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 125931 = 188897) B188897
theorem B125943 : Blo 123787 125943 := bstep (se 1 (by rfl) ⟨94457, by rfl⟩ : syracuseStep 125943 = 188915) B188915
theorem B125963 : Blo 123787 125963 := bstep (se 1 (by rfl) ⟨94472, by rfl⟩ : syracuseStep 125963 = 188945) B188945
theorem B125975 : Blo 123787 125975 := bstep (se 1 (by rfl) ⟨94481, by rfl⟩ : syracuseStep 125975 = 188963) B188963
theorem B191513 : Blo 123787 191513 := bstep (se 2 (by rfl) ⟨71817, by rfl⟩ : syracuseStep 191513 = 143635) B143635
theorem B125995 : Blo 123787 125995 := bstep (se 1 (by rfl) ⟨94496, by rfl⟩ : syracuseStep 125995 = 188993) B188993
theorem B126007 : Blo 123787 126007 := bstep (se 1 (by rfl) ⟨94505, by rfl⟩ : syracuseStep 126007 = 189011) B189011
theorem B420929 : Blo 123787 420929 := bstep (se 2 (by rfl) ⟨157848, by rfl⟩ : syracuseStep 420929 = 315697) B315697
theorem B126027 : Blo 123787 126027 := bstep (se 1 (by rfl) ⟨94520, by rfl⟩ : syracuseStep 126027 = 189041) B189041
theorem B126039 : Blo 123787 126039 := bstep (se 1 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 126039 = 189059) B189059
theorem B126059 : Blo 123787 126059 := bstep (se 1 (by rfl) ⟨94544, by rfl⟩ : syracuseStep 126059 = 189089) B189089
theorem B126071 : Blo 123787 126071 := bstep (se 1 (by rfl) ⟨94553, by rfl⟩ : syracuseStep 126071 = 189107) B189107
theorem B126091 : Blo 123787 126091 := bstep (se 1 (by rfl) ⟨94568, by rfl⟩ : syracuseStep 126091 = 189137) B189137
theorem B191627 : Blo 123787 191627 := bstep (se 1 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 191627 = 287441) B287441
theorem B126103 : Blo 123787 126103 := bstep (se 1 (by rfl) ⟨94577, by rfl⟩ : syracuseStep 126103 = 189155) B189155
theorem B191639 : Blo 123787 191639 := bstep (se 1 (by rfl) ⟨143729, by rfl⟩ : syracuseStep 191639 = 287459) B287459
theorem B126123 : Blo 123787 126123 := bstep (se 1 (by rfl) ⟨94592, by rfl⟩ : syracuseStep 126123 = 189185) B189185
theorem B126135 : Blo 123787 126135 := bstep (se 1 (by rfl) ⟨94601, by rfl⟩ : syracuseStep 126135 = 189203) B189203
theorem B126155 : Blo 123787 126155 := bstep (se 1 (by rfl) ⟨94616, by rfl⟩ : syracuseStep 126155 = 189233) B189233
theorem B126167 : Blo 123787 126167 := bstep (se 1 (by rfl) ⟨94625, by rfl⟩ : syracuseStep 126167 = 189251) B189251
theorem B453853 : Blo 123787 453853 := bstep (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) B170195
theorem B126187 : Blo 123787 126187 := bstep (se 1 (by rfl) ⟨94640, by rfl⟩ : syracuseStep 126187 = 189281) B189281
theorem B126199 : Blo 123787 126199 := bstep (se 1 (by rfl) ⟨94649, by rfl⟩ : syracuseStep 126199 = 189299) B189299
theorem B126219 : Blo 123787 126219 := bstep (se 1 (by rfl) ⟨94664, by rfl⟩ : syracuseStep 126219 = 189329) B189329
theorem B126231 : Blo 123787 126231 := bstep (se 1 (by rfl) ⟨94673, by rfl⟩ : syracuseStep 126231 = 189347) B189347
theorem B126251 : Blo 123787 126251 := bstep (se 1 (by rfl) ⟨94688, by rfl⟩ : syracuseStep 126251 = 189377) B189377
theorem B126263 : Blo 123787 126263 := bstep (se 1 (by rfl) ⟨94697, by rfl⟩ : syracuseStep 126263 = 189395) B189395
theorem B126283 : Blo 123787 126283 := bstep (se 1 (by rfl) ⟨94712, by rfl⟩ : syracuseStep 126283 = 189425) B189425
theorem B126295 : Blo 123787 126295 := bstep (se 1 (by rfl) ⟨94721, by rfl⟩ : syracuseStep 126295 = 189443) B189443
theorem B126315 : Blo 123787 126315 := bstep (se 1 (by rfl) ⟨94736, by rfl⟩ : syracuseStep 126315 = 189473) B189473
theorem B126327 : Blo 123787 126327 := bstep (se 1 (by rfl) ⟨94745, by rfl⟩ : syracuseStep 126327 = 189491) B189491
theorem B126347 : Blo 123787 126347 := bstep (se 1 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 126347 = 189521) B189521
theorem B7925141 : Blo 123787 7925141 := bstep (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) B371491
theorem B224663 : Blo 123787 224663 := bstep (se 1 (by rfl) ⟨168497, by rfl⟩ : syracuseStep 224663 = 336995) B336995
theorem B126359 : Blo 123787 126359 := bstep (se 1 (by rfl) ⟨94769, by rfl⟩ : syracuseStep 126359 = 189539) B189539
theorem B322967 : Blo 123787 322967 := bstep (se 1 (by rfl) ⟨242225, by rfl⟩ : syracuseStep 322967 = 484451) B484451
theorem B126379 : Blo 123787 126379 := bstep (se 1 (by rfl) ⟨94784, by rfl⟩ : syracuseStep 126379 = 189569) B189569
theorem B126391 : Blo 123787 126391 := bstep (se 1 (by rfl) ⟨94793, by rfl⟩ : syracuseStep 126391 = 189587) B189587
theorem B126411 : Blo 123787 126411 := bstep (se 1 (by rfl) ⟨94808, by rfl⟩ : syracuseStep 126411 = 189617) B189617
theorem B126423 : Blo 123787 126423 := bstep (se 1 (by rfl) ⟨94817, by rfl⟩ : syracuseStep 126423 = 189635) B189635
theorem B126443 : Blo 123787 126443 := bstep (se 1 (by rfl) ⟨94832, by rfl⟩ : syracuseStep 126443 = 189665) B189665
theorem B126455 : Blo 123787 126455 := bstep (se 1 (by rfl) ⟨94841, by rfl⟩ : syracuseStep 126455 = 189683) B189683
theorem B126475 : Blo 123787 126475 := bstep (se 1 (by rfl) ⟨94856, by rfl⟩ : syracuseStep 126475 = 189713) B189713
theorem B126487 : Blo 123787 126487 := bstep (se 1 (by rfl) ⟨94865, by rfl⟩ : syracuseStep 126487 = 189731) B189731
theorem B126507 : Blo 123787 126507 := bstep (se 1 (by rfl) ⟨94880, by rfl⟩ : syracuseStep 126507 = 189761) B189761
theorem B126519 : Blo 123787 126519 := bstep (se 1 (by rfl) ⟨94889, by rfl⟩ : syracuseStep 126519 = 189779) B189779
theorem B126539 : Blo 123787 126539 := bstep (se 1 (by rfl) ⟨94904, by rfl⟩ : syracuseStep 126539 = 189809) B189809
theorem B126551 : Blo 123787 126551 := bstep (se 1 (by rfl) ⟨94913, by rfl⟩ : syracuseStep 126551 = 189827) B189827
theorem B421469 : Blo 123787 421469 := bstep (se 3 (by rfl) ⟨79025, by rfl⟩ : syracuseStep 421469 = 158051) B158051
theorem B126571 : Blo 123787 126571 := bstep (se 1 (by rfl) ⟨94928, by rfl⟩ : syracuseStep 126571 = 189857) B189857
theorem B126583 : Blo 123787 126583 := bstep (se 1 (by rfl) ⟨94937, by rfl⟩ : syracuseStep 126583 = 189875) B189875
theorem B126603 : Blo 123787 126603 := bstep (se 1 (by rfl) ⟨94952, by rfl⟩ : syracuseStep 126603 = 189905) B189905
theorem B126615 : Blo 123787 126615 := bstep (se 1 (by rfl) ⟨94961, by rfl⟩ : syracuseStep 126615 = 189923) B189923
theorem B126635 : Blo 123787 126635 := bstep (se 1 (by rfl) ⟨94976, by rfl⟩ : syracuseStep 126635 = 189953) B189953
theorem B126647 : Blo 123787 126647 := bstep (se 1 (by rfl) ⟨94985, by rfl⟩ : syracuseStep 126647 = 189971) B189971
theorem B126667 : Blo 123787 126667 := bstep (se 1 (by rfl) ⟨95000, by rfl⟩ : syracuseStep 126667 = 190001) B190001
theorem B126679 : Blo 123787 126679 := bstep (se 1 (by rfl) ⟨95009, by rfl⟩ : syracuseStep 126679 = 190019) B190019
theorem B126699 : Blo 123787 126699 := bstep (se 1 (by rfl) ⟨95024, by rfl⟩ : syracuseStep 126699 = 190049) B190049
theorem B126711 : Blo 123787 126711 := bstep (se 1 (by rfl) ⟨95033, by rfl⟩ : syracuseStep 126711 = 190067) B190067
theorem B159499 : Blo 123787 159499 := bstep (se 1 (by rfl) ⟨119624, by rfl⟩ : syracuseStep 159499 = 239249) B239249
theorem B126731 : Blo 123787 126731 := bstep (se 1 (by rfl) ⟨95048, by rfl⟩ : syracuseStep 126731 = 190097) B190097
theorem B126743 : Blo 123787 126743 := bstep (se 1 (by rfl) ⟨95057, by rfl⟩ : syracuseStep 126743 = 190115) B190115
theorem B126763 : Blo 123787 126763 := bstep (se 1 (by rfl) ⟨95072, by rfl⟩ : syracuseStep 126763 = 190145) B190145
theorem B126775 : Blo 123787 126775 := bstep (se 1 (by rfl) ⟨95081, by rfl⟩ : syracuseStep 126775 = 190163) B190163
theorem B126795 : Blo 123787 126795 := bstep (se 1 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 126795 = 190193) B190193
theorem B126807 : Blo 123787 126807 := bstep (se 1 (by rfl) ⟨95105, by rfl⟩ : syracuseStep 126807 = 190211) B190211
theorem B126827 : Blo 123787 126827 := bstep (se 1 (by rfl) ⟨95120, by rfl⟩ : syracuseStep 126827 = 190241) B190241
theorem B126839 : Blo 123787 126839 := bstep (se 1 (by rfl) ⟨95129, by rfl⟩ : syracuseStep 126839 = 190259) B190259
theorem B126859 : Blo 123787 126859 := bstep (se 1 (by rfl) ⟨95144, by rfl⟩ : syracuseStep 126859 = 190289) B190289
theorem B126871 : Blo 123787 126871 := bstep (se 1 (by rfl) ⟨95153, by rfl⟩ : syracuseStep 126871 = 190307) B190307
theorem B126891 : Blo 123787 126891 := bstep (se 1 (by rfl) ⟨95168, by rfl⟩ : syracuseStep 126891 = 190337) B190337
theorem B126903 : Blo 123787 126903 := bstep (se 1 (by rfl) ⟨95177, by rfl⟩ : syracuseStep 126903 = 190355) B190355
theorem B126923 : Blo 123787 126923 := bstep (se 1 (by rfl) ⟨95192, by rfl⟩ : syracuseStep 126923 = 190385) B190385
theorem B126935 : Blo 123787 126935 := bstep (se 1 (by rfl) ⟨95201, by rfl⟩ : syracuseStep 126935 = 190403) B190403
theorem B126955 : Blo 123787 126955 := bstep (se 1 (by rfl) ⟨95216, by rfl⟩ : syracuseStep 126955 = 190433) B190433
theorem B126967 : Blo 123787 126967 := bstep (se 1 (by rfl) ⟨95225, by rfl⟩ : syracuseStep 126967 = 190451) B190451
theorem B192523 : Blo 123787 192523 := bstep (se 1 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 192523 = 288785) B288785
theorem B126987 : Blo 123787 126987 := bstep (se 1 (by rfl) ⟨95240, by rfl⟩ : syracuseStep 126987 = 190481) B190481
theorem B126999 : Blo 123787 126999 := bstep (se 1 (by rfl) ⟨95249, by rfl⟩ : syracuseStep 126999 = 190499) B190499
theorem B127019 : Blo 123787 127019 := bstep (se 1 (by rfl) ⟨95264, by rfl⟩ : syracuseStep 127019 = 190529) B190529
theorem B127031 : Blo 123787 127031 := bstep (se 1 (by rfl) ⟨95273, by rfl⟩ : syracuseStep 127031 = 190547) B190547
theorem B946241 : Blo 123787 946241 := bstep (se 2 (by rfl) ⟨354840, by rfl⟩ : syracuseStep 946241 = 709681) B709681
theorem B127051 : Blo 123787 127051 := bstep (se 1 (by rfl) ⟨95288, by rfl⟩ : syracuseStep 127051 = 190577) B190577
theorem B127063 : Blo 123787 127063 := bstep (se 1 (by rfl) ⟨95297, by rfl⟩ : syracuseStep 127063 = 190595) B190595
theorem B127083 : Blo 123787 127083 := bstep (se 1 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 127083 = 190625) B190625
theorem B127095 : Blo 123787 127095 := bstep (se 1 (by rfl) ⟨95321, by rfl⟩ : syracuseStep 127095 = 190643) B190643
theorem B127115 : Blo 123787 127115 := bstep (se 1 (by rfl) ⟨95336, by rfl⟩ : syracuseStep 127115 = 190673) B190673
theorem B127127 : Blo 123787 127127 := bstep (se 1 (by rfl) ⟨95345, by rfl⟩ : syracuseStep 127127 = 190691) B190691
theorem B127147 : Blo 123787 127147 := bstep (se 1 (by rfl) ⟨95360, by rfl⟩ : syracuseStep 127147 = 190721) B190721
theorem B127159 : Blo 123787 127159 := bstep (se 1 (by rfl) ⟨95369, by rfl⟩ : syracuseStep 127159 = 190739) B190739
theorem B127179 : Blo 123787 127179 := bstep (se 1 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 127179 = 190769) B190769
theorem B127191 : Blo 123787 127191 := bstep (se 1 (by rfl) ⟨95393, by rfl⟩ : syracuseStep 127191 = 190787) B190787
theorem B127211 : Blo 123787 127211 := bstep (se 1 (by rfl) ⟨95408, by rfl⟩ : syracuseStep 127211 = 190817) B190817
theorem B127223 : Blo 123787 127223 := bstep (se 1 (by rfl) ⟨95417, by rfl⟩ : syracuseStep 127223 = 190835) B190835
theorem B127243 : Blo 123787 127243 := bstep (se 1 (by rfl) ⟨95432, by rfl⟩ : syracuseStep 127243 = 190865) B190865
theorem B127255 : Blo 123787 127255 := bstep (se 1 (by rfl) ⟨95441, by rfl⟩ : syracuseStep 127255 = 190883) B190883
theorem B127275 : Blo 123787 127275 := bstep (se 1 (by rfl) ⟨95456, by rfl⟩ : syracuseStep 127275 = 190913) B190913
theorem B127287 : Blo 123787 127287 := bstep (se 1 (by rfl) ⟨95465, by rfl⟩ : syracuseStep 127287 = 190931) B190931
theorem B127307 : Blo 123787 127307 := bstep (se 1 (by rfl) ⟨95480, by rfl⟩ : syracuseStep 127307 = 190961) B190961
theorem B127319 : Blo 123787 127319 := bstep (se 1 (by rfl) ⟨95489, by rfl⟩ : syracuseStep 127319 = 190979) B190979
theorem B258391 : Blo 123787 258391 := bstep (se 1 (by rfl) ⟨193793, by rfl⟩ : syracuseStep 258391 = 387587) B387587
theorem B127339 : Blo 123787 127339 := bstep (se 1 (by rfl) ⟨95504, by rfl⟩ : syracuseStep 127339 = 191009) B191009
theorem B127351 : Blo 123787 127351 := bstep (se 1 (by rfl) ⟨95513, by rfl⟩ : syracuseStep 127351 = 191027) B191027
theorem B127371 : Blo 123787 127371 := bstep (se 1 (by rfl) ⟨95528, by rfl⟩ : syracuseStep 127371 = 191057) B191057
theorem B127383 : Blo 123787 127383 := bstep (se 1 (by rfl) ⟨95537, by rfl⟩ : syracuseStep 127383 = 191075) B191075
theorem B258455 : Blo 123787 258455 := bstep (se 1 (by rfl) ⟨193841, by rfl⟩ : syracuseStep 258455 = 387683) B387683
theorem B127403 : Blo 123787 127403 := bstep (se 1 (by rfl) ⟨95552, by rfl⟩ : syracuseStep 127403 = 191105) B191105
theorem B127415 : Blo 123787 127415 := bstep (se 1 (by rfl) ⟨95561, by rfl⟩ : syracuseStep 127415 = 191123) B191123
theorem B127435 : Blo 123787 127435 := bstep (se 1 (by rfl) ⟨95576, by rfl⟩ : syracuseStep 127435 = 191153) B191153
theorem B127447 : Blo 123787 127447 := bstep (se 1 (by rfl) ⟨95585, by rfl⟩ : syracuseStep 127447 = 191171) B191171
theorem B127467 : Blo 123787 127467 := bstep (se 1 (by rfl) ⟨95600, by rfl⟩ : syracuseStep 127467 = 191201) B191201
theorem B127479 : Blo 123787 127479 := bstep (se 1 (by rfl) ⟨95609, by rfl⟩ : syracuseStep 127479 = 191219) B191219
theorem B127499 : Blo 123787 127499 := bstep (se 1 (by rfl) ⟨95624, by rfl⟩ : syracuseStep 127499 = 191249) B191249
theorem B127511 : Blo 123787 127511 := bstep (se 1 (by rfl) ⟨95633, by rfl⟩ : syracuseStep 127511 = 191267) B191267
theorem B127531 : Blo 123787 127531 := bstep (se 1 (by rfl) ⟨95648, by rfl⟩ : syracuseStep 127531 = 191297) B191297
theorem B127543 : Blo 123787 127543 := bstep (se 1 (by rfl) ⟨95657, by rfl⟩ : syracuseStep 127543 = 191315) B191315
theorem B127563 : Blo 123787 127563 := bstep (se 1 (by rfl) ⟨95672, by rfl⟩ : syracuseStep 127563 = 191345) B191345
theorem B127575 : Blo 123787 127575 := bstep (se 1 (by rfl) ⟨95681, by rfl⟩ : syracuseStep 127575 = 191363) B191363
theorem B127595 : Blo 123787 127595 := bstep (se 1 (by rfl) ⟨95696, by rfl⟩ : syracuseStep 127595 = 191393) B191393
theorem B127607 : Blo 123787 127607 := bstep (se 1 (by rfl) ⟨95705, by rfl⟩ : syracuseStep 127607 = 191411) B191411
theorem B127627 : Blo 123787 127627 := bstep (se 1 (by rfl) ⟨95720, by rfl⟩ : syracuseStep 127627 = 191441) B191441
theorem B1798807 : Blo 123787 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B127639 : Blo 123787 127639 := bstep (se 1 (by rfl) ⟨95729, by rfl⟩ : syracuseStep 127639 = 191459) B191459
theorem B127659 : Blo 123787 127659 := bstep (se 1 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 127659 = 191489) B191489
theorem B127671 : Blo 123787 127671 := bstep (se 1 (by rfl) ⟨95753, by rfl⟩ : syracuseStep 127671 = 191507) B191507
theorem B422603 : Blo 123787 422603 := bstep (se 1 (by rfl) ⟨316952, by rfl⟩ : syracuseStep 422603 = 633905) B633905
theorem B127691 : Blo 123787 127691 := bstep (se 1 (by rfl) ⟨95768, by rfl⟩ : syracuseStep 127691 = 191537) B191537
theorem B160471 : Blo 123787 160471 := bstep (se 1 (by rfl) ⟨120353, by rfl⟩ : syracuseStep 160471 = 240707) B240707
theorem B127703 : Blo 123787 127703 := bstep (se 1 (by rfl) ⟨95777, by rfl⟩ : syracuseStep 127703 = 191555) B191555
theorem B127723 : Blo 123787 127723 := bstep (se 1 (by rfl) ⟨95792, by rfl⟩ : syracuseStep 127723 = 191585) B191585
theorem B127735 : Blo 123787 127735 := bstep (se 1 (by rfl) ⟨95801, by rfl⟩ : syracuseStep 127735 = 191603) B191603
theorem B127755 : Blo 123787 127755 := bstep (se 1 (by rfl) ⟨95816, by rfl⟩ : syracuseStep 127755 = 191633) B191633
theorem B127767 : Blo 123787 127767 := bstep (se 1 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 127767 = 191651) B191651
theorem B127787 : Blo 123787 127787 := bstep (se 1 (by rfl) ⟨95840, by rfl⟩ : syracuseStep 127787 = 191681) B191681
theorem B127927 : Blo 123787 127927 := bstep (se 1 (by rfl) ⟨95945, by rfl⟩ : syracuseStep 127927 = 191891) B191891
theorem B422873 : Blo 123787 422873 := bstep (se 2 (by rfl) ⟨158577, by rfl⟩ : syracuseStep 422873 = 317155) B317155
theorem B357655 : Blo 123787 357655 := bstep (se 1 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 357655 = 536483) B536483
theorem B455959 : Blo 123787 455959 := bstep (se 1 (by rfl) ⟨341969, by rfl⟩ : syracuseStep 455959 = 683939) B683939
theorem B161291 : Blo 123787 161291 := bstep (se 1 (by rfl) ⟨120968, by rfl⟩ : syracuseStep 161291 = 241937) B241937
theorem B718429 : Blo 123787 718429 := bstep (se 3 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 718429 = 269411) B269411
theorem B423575 : Blo 123787 423575 := bstep (se 1 (by rfl) ⟨317681, by rfl⟩ : syracuseStep 423575 = 635363) B635363
theorem B227137 : Blo 123787 227137 := bstep (se 2 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 227137 = 170353) B170353
theorem B12318641 : Blo 123787 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B423883 : Blo 123787 423883 := bstep (se 1 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 423883 = 635825) B635825
theorem B948185 : Blo 123787 948185 := bstep (se 2 (by rfl) ⟨355569, by rfl⟩ : syracuseStep 948185 = 711139) B711139
theorem B129163 : Blo 123787 129163 := bstep (se 1 (by rfl) ⟨96872, by rfl⟩ : syracuseStep 129163 = 193745) B193745
theorem B424115 : Blo 123787 424115 := bstep (se 1 (by rfl) ⟨318086, by rfl⟩ : syracuseStep 424115 = 636173) B636173
theorem B489665 : Blo 123787 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B424385 : Blo 123787 424385 := bstep (se 2 (by rfl) ⟨159144, by rfl⟩ : syracuseStep 424385 = 318289) B318289
theorem B227777 : Blo 123787 227777 := bstep (se 2 (by rfl) ⟨85416, by rfl⟩ : syracuseStep 227777 = 170833) B170833
theorem B358987 : Blo 123787 358987 := bstep (se 1 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 358987 = 538481) B538481
theorem B4651613 : Blo 123787 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B916069 : Blo 123787 916069 := bstep (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) B171763
theorem B359129 : Blo 123787 359129 := bstep (se 2 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 359129 = 269347) B269347
theorem B588505 : Blo 123787 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B359261 : Blo 123787 359261 := bstep (se 3 (by rfl) ⟨67361, by rfl⟩ : syracuseStep 359261 = 134723) B134723
theorem B424855 : Blo 123787 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B424925 : Blo 123787 424925 := bstep (se 3 (by rfl) ⟨79673, by rfl⟩ : syracuseStep 424925 = 159347) B159347
theorem B916525 : Blo 123787 916525 := bstep (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) B343697
theorem B293939 : Blo 123787 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B228491 : Blo 123787 228491 := bstep (se 1 (by rfl) ⟨171368, by rfl⟩ : syracuseStep 228491 = 342737) B342737
theorem B359603 : Blo 123787 359603 := bstep (se 1 (by rfl) ⟨269702, by rfl⟩ : syracuseStep 359603 = 539405) B539405
theorem B229015 : Blo 123787 229015 := bstep (se 1 (by rfl) ⟨171761, by rfl⟩ : syracuseStep 229015 = 343523) B343523
theorem B327347 : Blo 123787 327347 := bstep (se 1 (by rfl) ⟨245510, by rfl⟩ : syracuseStep 327347 = 491021) B491021
theorem B3112921 : Blo 123787 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B589853 : Blo 123787 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B655447 : Blo 123787 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B360719 : Blo 123787 360719 := bstep (se 1 (by rfl) ⟨270539, by rfl⟩ : syracuseStep 360719 = 541079) B541079
theorem B2031965 : Blo 123787 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B1081745 : Blo 123787 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B1409501 : Blo 123787 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B1082429 : Blo 123787 1082429 := bstep (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) B405911
theorem B689213 : Blo 123787 689213 := bstep (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) B258455
theorem B361847 : Blo 123787 361847 := bstep (se 1 (by rfl) ⟨271385, by rfl⟩ : syracuseStep 361847 = 542771) B542771
theorem B460603 : Blo 123787 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B722803 : Blo 123787 722803 := bstep (se 1 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 722803 = 1084205) B1084205
theorem B755905 : Blo 123787 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B5114177 : Blo 123787 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B1149329 : Blo 123787 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B428435 : Blo 123787 428435 := bstep (se 1 (by rfl) ⟨321326, by rfl⟩ : syracuseStep 428435 = 642653) B642653
theorem B199439 : Blo 123787 199439 := bstep (se 1 (by rfl) ⟨149579, by rfl⟩ : syracuseStep 199439 = 299159) B299159
theorem B133903 : Blo 123787 133903 := bstep (se 1 (by rfl) ⟨100427, by rfl⟩ : syracuseStep 133903 = 200855) B200855
theorem B920335 : Blo 123787 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B297881 : Blo 123787 297881 := bstep (se 2 (by rfl) ⟨111705, by rfl⟩ : syracuseStep 297881 = 223411) B223411
theorem B363521 : Blo 123787 363521 := bstep (se 2 (by rfl) ⟨136320, by rfl⟩ : syracuseStep 363521 = 272641) B272641
theorem B363635 : Blo 123787 363635 := bstep (se 1 (by rfl) ⟨272726, by rfl⟩ : syracuseStep 363635 = 545453) B545453
theorem B134407 : Blo 123787 134407 := bstep (se 1 (by rfl) ⟨100805, by rfl⟩ : syracuseStep 134407 = 201611) B201611
theorem B724261 : Blo 123787 724261 := bstep (se 4 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 724261 = 135799) B135799
theorem B265619 : Blo 123787 265619 := bstep (se 1 (by rfl) ⟨199214, by rfl⟩ : syracuseStep 265619 = 398429) B398429
theorem B1412801 : Blo 123787 1412801 := bstep (se 2 (by rfl) ⟨529800, by rfl⟩ : syracuseStep 1412801 = 1059601) B1059601
theorem B429839 : Blo 123787 429839 := bstep (se 1 (by rfl) ⟨322379, by rfl⟩ : syracuseStep 429839 = 644759) B644759
theorem B2723635 : Blo 123787 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B724787 : Blo 123787 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B430109 : Blo 123787 430109 := bstep (se 3 (by rfl) ⟨80645, by rfl⟩ : syracuseStep 430109 = 161291) B161291
theorem B364603 : Blo 123787 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B135227 : Blo 123787 135227 := bstep (se 1 (by rfl) ⟨101420, by rfl⟩ : syracuseStep 135227 = 202841) B202841
theorem B135355 : Blo 123787 135355 := bstep (se 1 (by rfl) ⟨101516, by rfl⟩ : syracuseStep 135355 = 203033) B203033
theorem B2396405 : Blo 123787 2396405 := bstep (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) B224663
theorem B430451 : Blo 123787 430451 := bstep (se 1 (by rfl) ⟨322838, by rfl⟩ : syracuseStep 430451 = 645677) B645677
theorem B201079 : Blo 123787 201079 := bstep (se 1 (by rfl) ⟨150809, by rfl⟩ : syracuseStep 201079 = 301619) B301619
theorem B2429621 : Blo 123787 2429621 := bstep (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) B227777
theorem B2265893 : Blo 123787 2265893 := bstep (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) B424855
theorem B758807 : Blo 123787 758807 := bstep (se 1 (by rfl) ⟨569105, by rfl⟩ : syracuseStep 758807 = 1138211) B1138211
theorem B1545389 : Blo 123787 1545389 := bstep (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) B579521
theorem B726245 : Blo 123787 726245 := bstep (se 4 (by rfl) ⟨68085, by rfl⟩ : syracuseStep 726245 = 136171) B136171
theorem B1283309 : Blo 123787 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B595259 : Blo 123787 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B628235 : Blo 123787 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B628397 : Blo 123787 628397 := bstep (se 3 (by rfl) ⟨117824, by rfl⟩ : syracuseStep 628397 = 235649) B235649
theorem B136891 : Blo 123787 136891 := bstep (se 1 (by rfl) ⟨102668, by rfl⟩ : syracuseStep 136891 = 205337) B205337
theorem B235399 : Blo 123787 235399 := bstep (se 1 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 235399 = 353099) B353099
theorem B300935 : Blo 123787 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B4954229 : Blo 123787 4954229 := bstep (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) B464459
theorem B2398409 : Blo 123787 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B170569 : Blo 123787 170569 := bstep (se 2 (by rfl) ⟨63963, by rfl⟩ : syracuseStep 170569 = 127927) B127927
theorem B531031 : Blo 123787 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B400427 : Blo 123787 400427 := bstep (se 1 (by rfl) ⟨300320, by rfl⟩ : syracuseStep 400427 = 600641) B600641
theorem B269497 : Blo 123787 269497 := bstep (se 2 (by rfl) ⟨101061, by rfl⟩ : syracuseStep 269497 = 202123) B202123
theorem B630017 : Blo 123787 630017 := bstep (se 2 (by rfl) ⟨236256, by rfl⟩ : syracuseStep 630017 = 472513) B472513
theorem B597401 : Blo 123787 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B237001 : Blo 123787 237001 := bstep (se 2 (by rfl) ⟨88875, by rfl⟩ : syracuseStep 237001 = 177751) B177751
theorem B957905 : Blo 123787 957905 := bstep (se 2 (by rfl) ⟨359214, by rfl⟩ : syracuseStep 957905 = 718429) B718429
theorem B728605 : Blo 123787 728605 := bstep (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) B273227
theorem B5283427 : Blo 123787 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B302849 : Blo 123787 302849 := bstep (se 2 (by rfl) ⟨113568, by rfl⟩ : syracuseStep 302849 = 227137) B227137
theorem B565177 : Blo 123787 565177 := bstep (se 2 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 565177 = 423883) B423883
theorem B532433 : Blo 123787 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B139279 : Blo 123787 139279 := bstep (se 1 (by rfl) ⟨104459, by rfl⟩ : syracuseStep 139279 = 208919) B208919
theorem B630827 : Blo 123787 630827 := bstep (se 1 (by rfl) ⟨473120, by rfl⟩ : syracuseStep 630827 = 946241) B946241
theorem B172217 : Blo 123787 172217 := bstep (se 2 (by rfl) ⟨64581, by rfl⟩ : syracuseStep 172217 = 129163) B129163
theorem B139783 : Blo 123787 139783 := bstep (se 1 (by rfl) ⟨104837, by rfl⟩ : syracuseStep 139783 = 209675) B209675
theorem B270881 : Blo 123787 270881 := bstep (se 2 (by rfl) ⟨101580, by rfl⟩ : syracuseStep 270881 = 203161) B203161
theorem B270983 : Blo 123787 270983 := bstep (se 1 (by rfl) ⟨203237, by rfl⟩ : syracuseStep 270983 = 406475) B406475
theorem B139963 : Blo 123787 139963 := bstep (se 1 (by rfl) ⟨104972, by rfl⟩ : syracuseStep 139963 = 209945) B209945
theorem B1221425 : Blo 123787 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B598873 : Blo 123787 598873 := bstep (se 2 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 598873 = 449155) B449155
theorem B140431 : Blo 123787 140431 := bstep (se 1 (by rfl) ⟨105323, by rfl⟩ : syracuseStep 140431 = 210647) B210647
theorem B632123 : Blo 123787 632123 := bstep (se 1 (by rfl) ⟨474092, by rfl⟩ : syracuseStep 632123 = 948185) B948185
theorem B1222033 : Blo 123787 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B632285 : Blo 123787 632285 := bstep (se 3 (by rfl) ⟨118553, by rfl⟩ : syracuseStep 632285 = 237107) B237107
theorem B796189 : Blo 123787 796189 := bstep (se 3 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 796189 = 298571) B298571
theorem B140935 : Blo 123787 140935 := bstep (se 1 (by rfl) ⟨105701, by rfl⟩ : syracuseStep 140935 = 211403) B211403
theorem B337679 : Blo 123787 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B632609 : Blo 123787 632609 := bstep (se 2 (by rfl) ⟨237228, by rfl⟩ : syracuseStep 632609 = 474457) B474457
theorem B239419 : Blo 123787 239419 := bstep (se 1 (by rfl) ⟨179564, by rfl⟩ : syracuseStep 239419 = 359129) B359129
theorem B141115 : Blo 123787 141115 := bstep (se 1 (by rfl) ⟨105836, by rfl⟩ : syracuseStep 141115 = 211673) B211673
theorem B239507 : Blo 123787 239507 := bstep (se 1 (by rfl) ⟨179630, by rfl⟩ : syracuseStep 239507 = 359261) B359261
theorem B11610053 : Blo 123787 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B239735 : Blo 123787 239735 := bstep (se 1 (by rfl) ⟨179801, by rfl⟩ : syracuseStep 239735 = 359603) B359603
theorem B305353 : Blo 123787 305353 := bstep (se 2 (by rfl) ⟨114507, by rfl⟩ : syracuseStep 305353 = 229015) B229015
theorem B141583 : Blo 123787 141583 := bstep (se 1 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 141583 = 212375) B212375
theorem B633581 : Blo 123787 633581 := bstep (se 3 (by rfl) ⟨118796, by rfl⟩ : syracuseStep 633581 = 237593) B237593
theorem B600833 : Blo 123787 600833 := bstep (se 2 (by rfl) ⟨225312, by rfl⟩ : syracuseStep 600833 = 450625) B450625
theorem B142087 : Blo 123787 142087 := bstep (se 1 (by rfl) ⟨106565, by rfl⟩ : syracuseStep 142087 = 213131) B213131
theorem B600947 : Blo 123787 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B2173877 : Blo 123787 2173877 := bstep (se 5 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 2173877 = 203801) B203801
theorem B142267 : Blo 123787 142267 := bstep (se 1 (by rfl) ⟨106700, by rfl⟩ : syracuseStep 142267 = 213401) B213401
theorem B470083 : Blo 123787 470083 := bstep (se 1 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 470083 = 705125) B705125
theorem B699479 : Blo 123787 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B765101 : Blo 123787 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B306433 : Blo 123787 306433 := bstep (se 2 (by rfl) ⟨114912, by rfl⟩ : syracuseStep 306433 = 229825) B229825
theorem B470387 : Blo 123787 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B142735 : Blo 123787 142735 := bstep (se 1 (by rfl) ⟨107051, by rfl⟩ : syracuseStep 142735 = 214103) B214103
theorem B634391 : Blo 123787 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B896579 : Blo 123787 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B241451 : Blo 123787 241451 := bstep (se 1 (by rfl) ⟨181088, by rfl⟩ : syracuseStep 241451 = 362177) B362177
theorem B470843 : Blo 123787 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B143239 : Blo 123787 143239 := bstep (se 1 (by rfl) ⟨107429, by rfl⟩ : syracuseStep 143239 = 214859) B214859
theorem B143375 : Blo 123787 143375 := bstep (se 1 (by rfl) ⟨107531, by rfl⟩ : syracuseStep 143375 = 215063) B215063
theorem B241679 : Blo 123787 241679 := bstep (se 1 (by rfl) ⟨181259, by rfl⟩ : syracuseStep 241679 = 362519) B362519
theorem B208939 : Blo 123787 208939 := bstep (se 1 (by rfl) ⟨156704, by rfl⟩ : syracuseStep 208939 = 313409) B313409
theorem B143419 : Blo 123787 143419 := bstep (se 1 (by rfl) ⟨107564, by rfl⟩ : syracuseStep 143419 = 215129) B215129
theorem B209081 : Blo 123787 209081 := bstep (se 2 (by rfl) ⟨78405, by rfl⟩ : syracuseStep 209081 = 156811) B156811
theorem B1421549 : Blo 123787 1421549 := bstep (se 3 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 1421549 = 533081) B533081
theorem B471329 : Blo 123787 471329 := bstep (se 2 (by rfl) ⟨176748, by rfl⟩ : syracuseStep 471329 = 353497) B353497
theorem B3322259 : Blo 123787 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B6238691 : Blo 123787 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B209783 : Blo 123787 209783 := bstep (se 1 (by rfl) ⟨157337, by rfl⟩ : syracuseStep 209783 = 314675) B314675
theorem B472301 : Blo 123787 472301 := bstep (se 3 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 472301 = 177113) B177113
theorem B603407 : Blo 123787 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B210235 : Blo 123787 210235 := bstep (se 1 (by rfl) ⟨157676, by rfl⟩ : syracuseStep 210235 = 315353) B315353
theorem B308627 : Blo 123787 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B406937 : Blo 123787 406937 := bstep (se 2 (by rfl) ⟨152601, by rfl⟩ : syracuseStep 406937 = 305203) B305203
theorem B210377 : Blo 123787 210377 := bstep (se 2 (by rfl) ⟨78891, by rfl⟩ : syracuseStep 210377 = 157783) B157783
theorem B177671 : Blo 123787 177671 := bstep (se 1 (by rfl) ⟨133253, by rfl⟩ : syracuseStep 177671 = 266507) B266507
theorem B538123 : Blo 123787 538123 := bstep (se 1 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 538123 = 807185) B807185
theorem B603715 : Blo 123787 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B308855 : Blo 123787 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B1226497 : Blo 123787 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B177979 : Blo 123787 177979 := bstep (se 1 (by rfl) ⟨133484, by rfl⟩ : syracuseStep 177979 = 266969) B266969
theorem B767879 : Blo 123787 767879 := bstep (se 1 (by rfl) ⟨575909, by rfl⟩ : syracuseStep 767879 = 1151819) B1151819
theorem B472985 : Blo 123787 472985 := bstep (se 2 (by rfl) ⟨177369, by rfl⟩ : syracuseStep 472985 = 354739) B354739
theorem B211079 : Blo 123787 211079 := bstep (se 1 (by rfl) ⟨158309, by rfl⟩ : syracuseStep 211079 = 316619) B316619
theorem B342359 : Blo 123787 342359 := bstep (se 1 (by rfl) ⟨256769, by rfl⟩ : syracuseStep 342359 = 513539) B513539
theorem B4143581 : Blo 123787 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B637469 : Blo 123787 637469 := bstep (se 3 (by rfl) ⟨119525, by rfl⟩ : syracuseStep 637469 = 239051) B239051
theorem B211727 : Blo 123787 211727 := bstep (se 1 (by rfl) ⟨158795, by rfl⟩ : syracuseStep 211727 = 317591) B317591
theorem B473971 : Blo 123787 473971 := bstep (se 1 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 473971 = 710957) B710957
theorem B179129 : Blo 123787 179129 := bstep (se 2 (by rfl) ⟨67173, by rfl⟩ : syracuseStep 179129 = 134347) B134347
theorem B1358795 : Blo 123787 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B637955 : Blo 123787 637955 := bstep (se 1 (by rfl) ⟨478466, by rfl⟩ : syracuseStep 637955 = 956933) B956933
theorem B212267 : Blo 123787 212267 := bstep (se 1 (by rfl) ⟨159200, by rfl⟩ : syracuseStep 212267 = 318401) B318401
theorem B1818065 : Blo 123787 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B212665 : Blo 123787 212665 := bstep (se 2 (by rfl) ⟨79749, by rfl⟩ : syracuseStep 212665 = 159499) B159499
theorem B179975 : Blo 123787 179975 := bstep (se 1 (by rfl) ⟨134981, by rfl⟩ : syracuseStep 179975 = 269963) B269963
theorem B278675 : Blo 123787 278675 := bstep (se 1 (by rfl) ⟨209006, by rfl⟩ : syracuseStep 278675 = 418013) B418013
theorem B278729 : Blo 123787 278729 := bstep (se 2 (by rfl) ⟨104523, by rfl⟩ : syracuseStep 278729 = 209047) B209047
theorem B213367 : Blo 123787 213367 := bstep (se 1 (by rfl) ⟨160025, by rfl⟩ : syracuseStep 213367 = 320051) B320051
theorem B180667 : Blo 123787 180667 := bstep (se 1 (by rfl) ⟨135500, by rfl⟩ : syracuseStep 180667 = 271001) B271001
theorem B344521 : Blo 123787 344521 := bstep (se 2 (by rfl) ⟨129195, by rfl⟩ : syracuseStep 344521 = 258391) B258391
theorem B1425923 : Blo 123787 1425923 := bstep (se 1 (by rfl) ⟨1069442, by rfl⟩ : syracuseStep 1425923 = 2138885) B2138885
theorem B213563 : Blo 123787 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B639575 : Blo 123787 639575 := bstep (se 1 (by rfl) ⟨479681, by rfl⟩ : syracuseStep 639575 = 959363) B959363
theorem B344695 : Blo 123787 344695 := bstep (se 1 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 344695 = 517043) B517043
theorem B803621 : Blo 123787 803621 := bstep (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) B150679
theorem B1295153 : Blo 123787 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B770867 : Blo 123787 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B181111 : Blo 123787 181111 := bstep (se 1 (by rfl) ⟨135833, by rfl⟩ : syracuseStep 181111 = 271667) B271667
theorem B279431 : Blo 123787 279431 := bstep (se 1 (by rfl) ⟨209573, by rfl⟩ : syracuseStep 279431 = 419147) B419147
theorem B213961 : Blo 123787 213961 := bstep (se 2 (by rfl) ⟨80235, by rfl⟩ : syracuseStep 213961 = 160471) B160471
theorem B476189 : Blo 123787 476189 := bstep (se 3 (by rfl) ⟨89285, by rfl⟩ : syracuseStep 476189 = 178571) B178571
theorem B279611 : Blo 123787 279611 := bstep (se 1 (by rfl) ⟨209708, by rfl⟩ : syracuseStep 279611 = 419417) B419417
theorem B640061 : Blo 123787 640061 := bstep (se 3 (by rfl) ⟨120011, by rfl⟩ : syracuseStep 640061 = 240023) B240023
theorem B345235 : Blo 123787 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B279737 : Blo 123787 279737 := bstep (se 2 (by rfl) ⟨104901, by rfl⟩ : syracuseStep 279737 = 209803) B209803
theorem B280079 : Blo 123787 280079 := bstep (se 1 (by rfl) ⟨210059, by rfl⟩ : syracuseStep 280079 = 420119) B420119
theorem B280097 : Blo 123787 280097 := bstep (se 2 (by rfl) ⟨105036, by rfl⟩ : syracuseStep 280097 = 210073) B210073
theorem B214663 : Blo 123787 214663 := bstep (se 1 (by rfl) ⟨160997, by rfl⟩ : syracuseStep 214663 = 321995) B321995
theorem B181931 : Blo 123787 181931 := bstep (se 1 (by rfl) ⟨136448, by rfl⟩ : syracuseStep 181931 = 272897) B272897
theorem B476873 : Blo 123787 476873 := bstep (se 2 (by rfl) ⟨178827, by rfl⟩ : syracuseStep 476873 = 357655) B357655
theorem B607945 : Blo 123787 607945 := bstep (se 2 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 607945 = 455959) B455959
theorem B542497 : Blo 123787 542497 := bstep (se 2 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 542497 = 406873) B406873
theorem B280439 : Blo 123787 280439 := bstep (se 1 (by rfl) ⟨210329, by rfl⟩ : syracuseStep 280439 = 420659) B420659
theorem B509905 : Blo 123787 509905 := bstep (se 2 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 509905 = 382429) B382429
theorem B706583 : Blo 123787 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B280619 : Blo 123787 280619 := bstep (se 1 (by rfl) ⟨210464, by rfl⟩ : syracuseStep 280619 = 420929) B420929
theorem B215311 : Blo 123787 215311 := bstep (se 1 (by rfl) ⟨161483, by rfl⟩ : syracuseStep 215311 = 322967) B322967
theorem B280979 : Blo 123787 280979 := bstep (se 1 (by rfl) ⟨210734, by rfl⟩ : syracuseStep 280979 = 421469) B421469
theorem B313753 : Blo 123787 313753 := bstep (se 2 (by rfl) ⟨117657, by rfl⟩ : syracuseStep 313753 = 235315) B235315
theorem B281033 : Blo 123787 281033 := bstep (se 2 (by rfl) ⟨105387, by rfl⟩ : syracuseStep 281033 = 210775) B210775
theorem B313915 : Blo 123787 313915 := bstep (se 1 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 313915 = 470873) B470873
theorem B1231553 : Blo 123787 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B314057 : Blo 123787 314057 := bstep (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) B235543
theorem B641843 : Blo 123787 641843 := bstep (se 1 (by rfl) ⟨481382, by rfl⟩ : syracuseStep 641843 = 962765) B962765
theorem B314401 : Blo 123787 314401 := bstep (se 2 (by rfl) ⟨117900, by rfl⟩ : syracuseStep 314401 = 235801) B235801
theorem B642167 : Blo 123787 642167 := bstep (se 1 (by rfl) ⟨481625, by rfl⟩ : syracuseStep 642167 = 963251) B963251
theorem B281735 : Blo 123787 281735 := bstep (se 1 (by rfl) ⟨211301, by rfl⟩ : syracuseStep 281735 = 422603) B422603
theorem B281915 : Blo 123787 281915 := bstep (se 1 (by rfl) ⟨211436, by rfl⟩ : syracuseStep 281915 = 422873) B422873
theorem B544153 : Blo 123787 544153 := bstep (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) B408115
theorem B282041 : Blo 123787 282041 := bstep (se 2 (by rfl) ⟨105765, by rfl⟩ : syracuseStep 282041 = 211531) B211531
theorem B478649 : Blo 123787 478649 := bstep (se 2 (by rfl) ⟨179493, by rfl⟩ : syracuseStep 478649 = 358987) B358987
theorem B314999 : Blo 123787 314999 := bstep (se 1 (by rfl) ⟨236249, by rfl⟩ : syracuseStep 314999 = 472499) B472499
theorem B806593 : Blo 123787 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B46157525 : Blo 123787 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B282383 : Blo 123787 282383 := bstep (se 1 (by rfl) ⟨211787, by rfl⟩ : syracuseStep 282383 = 423575) B423575
theorem B282401 : Blo 123787 282401 := bstep (se 2 (by rfl) ⟨105900, by rfl⟩ : syracuseStep 282401 = 211801) B211801
theorem B708497 : Blo 123787 708497 := bstep (se 2 (by rfl) ⟨265686, by rfl⟩ : syracuseStep 708497 = 531373) B531373
theorem B8212427 : Blo 123787 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B643139 : Blo 123787 643139 := bstep (se 1 (by rfl) ⟨482354, by rfl⟩ : syracuseStep 643139 = 964709) B964709
theorem B282743 : Blo 123787 282743 := bstep (se 1 (by rfl) ⟨212057, by rfl⟩ : syracuseStep 282743 = 424115) B424115
theorem B282923 : Blo 123787 282923 := bstep (se 1 (by rfl) ⟨212192, by rfl⟩ : syracuseStep 282923 = 424385) B424385
theorem B643463 : Blo 123787 643463 := bstep (se 1 (by rfl) ⟨482597, by rfl⟩ : syracuseStep 643463 = 965195) B965195
theorem B3101075 : Blo 123787 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B709181 : Blo 123787 709181 := bstep (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) B265943
theorem B283283 : Blo 123787 283283 := bstep (se 1 (by rfl) ⟨212462, by rfl⟩ : syracuseStep 283283 = 424925) B424925
theorem B283337 : Blo 123787 283337 := bstep (se 2 (by rfl) ⟨106251, by rfl⟩ : syracuseStep 283337 = 212503) B212503
theorem B152327 : Blo 123787 152327 := bstep (se 1 (by rfl) ⟨114245, by rfl⟩ : syracuseStep 152327 = 228491) B228491
theorem B316295 : Blo 123787 316295 := bstep (se 1 (by rfl) ⟨237221, by rfl⟩ : syracuseStep 316295 = 474443) B474443
theorem B316345 : Blo 123787 316345 := bstep (se 2 (by rfl) ⟨118629, by rfl⟩ : syracuseStep 316345 = 237259) B237259
theorem B218231 : Blo 123787 218231 := bstep (se 1 (by rfl) ⟨163673, by rfl⟩ : syracuseStep 218231 = 327347) B327347
theorem B4150561 : Blo 123787 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B1365281 : Blo 123787 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B185735 : Blo 123787 185735 := bstep (se 1 (by rfl) ⟨139301, by rfl⟩ : syracuseStep 185735 = 278603) B278603
theorem B284039 : Blo 123787 284039 := bstep (se 1 (by rfl) ⟨213029, by rfl⟩ : syracuseStep 284039 = 426059) B426059
theorem B1201553 : Blo 123787 1201553 := bstep (se 2 (by rfl) ⟨450582, by rfl⟩ : syracuseStep 1201553 = 901165) B901165
theorem B185771 : Blo 123787 185771 := bstep (se 1 (by rfl) ⟨139328, by rfl⟩ : syracuseStep 185771 = 278657) B278657
theorem B185801 : Blo 123787 185801 := bstep (se 2 (by rfl) ⟨69675, by rfl⟩ : syracuseStep 185801 = 139351) B139351
theorem B644573 : Blo 123787 644573 := bstep (se 3 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 644573 = 241715) B241715
theorem B316943 : Blo 123787 316943 := bstep (se 1 (by rfl) ⟨237707, by rfl⟩ : syracuseStep 316943 = 475415) B475415
theorem B185915 : Blo 123787 185915 := bstep (se 1 (by rfl) ⟨139436, by rfl⟩ : syracuseStep 185915 = 278873) B278873
theorem B284219 : Blo 123787 284219 := bstep (se 1 (by rfl) ⟨213164, by rfl⟩ : syracuseStep 284219 = 426329) B426329
theorem B185975 : Blo 123787 185975 := bstep (se 1 (by rfl) ⟨139481, by rfl⟩ : syracuseStep 185975 = 278963) B278963
theorem B185999 : Blo 123787 185999 := bstep (se 1 (by rfl) ⟨139499, by rfl⟩ : syracuseStep 185999 = 278999) B278999
theorem B186041 : Blo 123787 186041 := bstep (se 2 (by rfl) ⟨69765, by rfl⟩ : syracuseStep 186041 = 139531) B139531
theorem B284345 : Blo 123787 284345 := bstep (se 2 (by rfl) ⟨106629, by rfl⟩ : syracuseStep 284345 = 213259) B213259
theorem B677605 : Blo 123787 677605 := bstep (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) B127051
theorem B186119 : Blo 123787 186119 := bstep (se 1 (by rfl) ⟨139589, by rfl⟩ : syracuseStep 186119 = 279179) B279179
theorem B186155 : Blo 123787 186155 := bstep (se 1 (by rfl) ⟨139616, by rfl⟩ : syracuseStep 186155 = 279233) B279233
theorem B907057 : Blo 123787 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B186185 : Blo 123787 186185 := bstep (se 2 (by rfl) ⟨69819, by rfl⟩ : syracuseStep 186185 = 139639) B139639
theorem B776051 : Blo 123787 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B186299 : Blo 123787 186299 := bstep (se 1 (by rfl) ⟨139724, by rfl⟩ : syracuseStep 186299 = 279449) B279449
theorem B186359 : Blo 123787 186359 := bstep (se 1 (by rfl) ⟨139769, by rfl⟩ : syracuseStep 186359 = 279539) B279539
theorem B186383 : Blo 123787 186383 := bstep (se 1 (by rfl) ⟨139787, by rfl⟩ : syracuseStep 186383 = 279575) B279575
theorem B284687 : Blo 123787 284687 := bstep (se 1 (by rfl) ⟨213515, by rfl⟩ : syracuseStep 284687 = 427031) B427031
theorem B284705 : Blo 123787 284705 := bstep (se 2 (by rfl) ⟨106764, by rfl⟩ : syracuseStep 284705 = 213529) B213529
theorem B186425 : Blo 123787 186425 := bstep (se 2 (by rfl) ⟨69909, by rfl⟩ : syracuseStep 186425 = 139819) B139819
theorem B186503 : Blo 123787 186503 := bstep (se 1 (by rfl) ⟨139877, by rfl⟩ : syracuseStep 186503 = 279755) B279755
theorem B186539 : Blo 123787 186539 := bstep (se 1 (by rfl) ⟨139904, by rfl⟩ : syracuseStep 186539 = 279809) B279809
theorem B186569 : Blo 123787 186569 := bstep (se 2 (by rfl) ⟨69963, by rfl⟩ : syracuseStep 186569 = 139927) B139927
theorem B317641 : Blo 123787 317641 := bstep (se 2 (by rfl) ⟨119115, by rfl⟩ : syracuseStep 317641 = 238231) B238231
theorem B13031725 : Blo 123787 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B186683 : Blo 123787 186683 := bstep (se 1 (by rfl) ⟨140012, by rfl⟩ : syracuseStep 186683 = 280025) B280025
theorem B317783 : Blo 123787 317783 := bstep (se 1 (by rfl) ⟨238337, by rfl⟩ : syracuseStep 317783 = 476675) B476675
theorem B186743 : Blo 123787 186743 := bstep (se 1 (by rfl) ⟨140057, by rfl⟩ : syracuseStep 186743 = 280115) B280115
theorem B285047 : Blo 123787 285047 := bstep (se 1 (by rfl) ⟨213785, by rfl⟩ : syracuseStep 285047 = 427571) B427571
theorem B186767 : Blo 123787 186767 := bstep (se 1 (by rfl) ⟨140075, by rfl⟩ : syracuseStep 186767 = 280151) B280151
theorem B186809 : Blo 123787 186809 := bstep (se 2 (by rfl) ⟨70053, by rfl⟩ : syracuseStep 186809 = 140107) B140107
theorem B186887 : Blo 123787 186887 := bstep (se 1 (by rfl) ⟨140165, by rfl⟩ : syracuseStep 186887 = 280331) B280331
theorem B186923 : Blo 123787 186923 := bstep (se 1 (by rfl) ⟨140192, by rfl⟩ : syracuseStep 186923 = 280385) B280385
theorem B285227 : Blo 123787 285227 := bstep (se 1 (by rfl) ⟨213920, by rfl⟩ : syracuseStep 285227 = 427841) B427841
theorem B186953 : Blo 123787 186953 := bstep (se 2 (by rfl) ⟨70107, by rfl⟩ : syracuseStep 186953 = 140215) B140215
theorem B187067 : Blo 123787 187067 := bstep (se 1 (by rfl) ⟨140300, by rfl⟩ : syracuseStep 187067 = 280601) B280601
theorem B187127 : Blo 123787 187127 := bstep (se 1 (by rfl) ⟨140345, by rfl⟩ : syracuseStep 187127 = 280691) B280691
theorem B187151 : Blo 123787 187151 := bstep (se 1 (by rfl) ⟨140363, by rfl⟩ : syracuseStep 187151 = 280727) B280727
theorem B252715 : Blo 123787 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B187193 : Blo 123787 187193 := bstep (se 2 (by rfl) ⟨70197, by rfl⟩ : syracuseStep 187193 = 140395) B140395
theorem B187271 : Blo 123787 187271 := bstep (se 1 (by rfl) ⟨140453, by rfl⟩ : syracuseStep 187271 = 280907) B280907
theorem B285587 : Blo 123787 285587 := bstep (se 1 (by rfl) ⟨214190, by rfl⟩ : syracuseStep 285587 = 428381) B428381
theorem B187307 : Blo 123787 187307 := bstep (se 1 (by rfl) ⟨140480, by rfl⟩ : syracuseStep 187307 = 280961) B280961
theorem B482233 : Blo 123787 482233 := bstep (se 2 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 482233 = 361675) B361675
theorem B187337 : Blo 123787 187337 := bstep (se 2 (by rfl) ⟨70251, by rfl⟩ : syracuseStep 187337 = 140503) B140503
theorem B285641 : Blo 123787 285641 := bstep (se 2 (by rfl) ⟨107115, by rfl⟩ : syracuseStep 285641 = 214231) B214231
theorem B187451 : Blo 123787 187451 := bstep (se 1 (by rfl) ⟨140588, by rfl⟩ : syracuseStep 187451 = 281177) B281177
theorem B187511 : Blo 123787 187511 := bstep (se 1 (by rfl) ⟨140633, by rfl⟩ : syracuseStep 187511 = 281267) B281267
theorem B187535 : Blo 123787 187535 := bstep (se 1 (by rfl) ⟨140651, by rfl⟩ : syracuseStep 187535 = 281303) B281303
theorem B187577 : Blo 123787 187577 := bstep (se 2 (by rfl) ⟨70341, by rfl⟩ : syracuseStep 187577 = 140683) B140683
theorem B7625933 : Blo 123787 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B187655 : Blo 123787 187655 := bstep (se 1 (by rfl) ⟨140741, by rfl⟩ : syracuseStep 187655 = 281483) B281483
theorem B187691 : Blo 123787 187691 := bstep (se 1 (by rfl) ⟨140768, by rfl⟩ : syracuseStep 187691 = 281537) B281537
theorem B187721 : Blo 123787 187721 := bstep (se 2 (by rfl) ⟨70395, by rfl⟩ : syracuseStep 187721 = 140791) B140791
theorem B187835 : Blo 123787 187835 := bstep (se 1 (by rfl) ⟨140876, by rfl⟩ : syracuseStep 187835 = 281753) B281753
theorem B187895 : Blo 123787 187895 := bstep (se 1 (by rfl) ⟨140921, by rfl⟩ : syracuseStep 187895 = 281843) B281843
theorem B187919 : Blo 123787 187919 := bstep (se 1 (by rfl) ⟨140939, by rfl⟩ : syracuseStep 187919 = 281879) B281879
theorem B187961 : Blo 123787 187961 := bstep (se 2 (by rfl) ⟨70485, by rfl⟩ : syracuseStep 187961 = 140971) B140971
theorem B188039 : Blo 123787 188039 := bstep (se 1 (by rfl) ⟨141029, by rfl⟩ : syracuseStep 188039 = 282059) B282059
theorem B286343 : Blo 123787 286343 := bstep (se 1 (by rfl) ⟨214757, by rfl⟩ : syracuseStep 286343 = 429515) B429515
theorem B188075 : Blo 123787 188075 := bstep (se 1 (by rfl) ⟨141056, by rfl⟩ : syracuseStep 188075 = 282113) B282113
theorem B188105 : Blo 123787 188105 := bstep (se 2 (by rfl) ⟨70539, by rfl⟩ : syracuseStep 188105 = 141079) B141079
theorem B188219 : Blo 123787 188219 := bstep (se 1 (by rfl) ⟨141164, by rfl⟩ : syracuseStep 188219 = 282329) B282329
theorem B286523 : Blo 123787 286523 := bstep (se 1 (by rfl) ⟨214892, by rfl⟩ : syracuseStep 286523 = 429785) B429785
theorem B188279 : Blo 123787 188279 := bstep (se 1 (by rfl) ⟨141209, by rfl⟩ : syracuseStep 188279 = 282419) B282419
theorem B188303 : Blo 123787 188303 := bstep (se 1 (by rfl) ⟨141227, by rfl⟩ : syracuseStep 188303 = 282455) B282455
theorem B188345 : Blo 123787 188345 := bstep (se 2 (by rfl) ⟨70629, by rfl⟩ : syracuseStep 188345 = 141259) B141259
theorem B286649 : Blo 123787 286649 := bstep (se 2 (by rfl) ⟨107493, by rfl⟩ : syracuseStep 286649 = 214987) B214987
theorem B188423 : Blo 123787 188423 := bstep (se 1 (by rfl) ⟨141317, by rfl⟩ : syracuseStep 188423 = 282635) B282635
theorem B188459 : Blo 123787 188459 := bstep (se 1 (by rfl) ⟨141344, by rfl⟩ : syracuseStep 188459 = 282689) B282689
theorem B11952197 : Blo 123787 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B188489 : Blo 123787 188489 := bstep (se 2 (by rfl) ⟨70683, by rfl⟩ : syracuseStep 188489 = 141367) B141367
theorem B1695917 : Blo 123787 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B188603 : Blo 123787 188603 := bstep (se 1 (by rfl) ⟨141452, by rfl⟩ : syracuseStep 188603 = 282905) B282905
theorem B188663 : Blo 123787 188663 := bstep (se 1 (by rfl) ⟨141497, by rfl⟩ : syracuseStep 188663 = 282995) B282995
theorem B188687 : Blo 123787 188687 := bstep (se 1 (by rfl) ⟨141515, by rfl⟩ : syracuseStep 188687 = 283031) B283031
theorem B286991 : Blo 123787 286991 := bstep (se 1 (by rfl) ⟨215243, by rfl⟩ : syracuseStep 286991 = 430487) B430487
theorem B287009 : Blo 123787 287009 := bstep (se 2 (by rfl) ⟨107628, by rfl⟩ : syracuseStep 287009 = 215257) B215257
theorem B188729 : Blo 123787 188729 := bstep (se 2 (by rfl) ⟨70773, by rfl⟩ : syracuseStep 188729 = 141547) B141547
theorem B319859 : Blo 123787 319859 := bstep (se 1 (by rfl) ⟨239894, by rfl⟩ : syracuseStep 319859 = 479789) B479789
theorem B188807 : Blo 123787 188807 := bstep (se 1 (by rfl) ⟨141605, by rfl⟩ : syracuseStep 188807 = 283211) B283211
theorem B188843 : Blo 123787 188843 := bstep (se 1 (by rfl) ⟨141632, by rfl⟩ : syracuseStep 188843 = 283265) B283265
theorem B451001 : Blo 123787 451001 := bstep (se 2 (by rfl) ⟨169125, by rfl⟩ : syracuseStep 451001 = 338251) B338251
theorem B188873 : Blo 123787 188873 := bstep (se 2 (by rfl) ⟨70827, by rfl⟩ : syracuseStep 188873 = 141655) B141655
theorem B188987 : Blo 123787 188987 := bstep (se 1 (by rfl) ⟨141740, by rfl⟩ : syracuseStep 188987 = 283481) B283481
theorem B418391 : Blo 123787 418391 := bstep (se 1 (by rfl) ⟨313793, by rfl⟩ : syracuseStep 418391 = 627587) B627587
theorem B189047 : Blo 123787 189047 := bstep (se 1 (by rfl) ⟨141785, by rfl⟩ : syracuseStep 189047 = 283571) B283571
theorem B287351 : Blo 123787 287351 := bstep (se 1 (by rfl) ⟨215513, by rfl⟩ : syracuseStep 287351 = 431027) B431027
theorem B189071 : Blo 123787 189071 := bstep (se 1 (by rfl) ⟨141803, by rfl⟩ : syracuseStep 189071 = 283607) B283607
theorem B189113 : Blo 123787 189113 := bstep (se 2 (by rfl) ⟨70917, by rfl⟩ : syracuseStep 189113 = 141835) B141835
theorem B189191 : Blo 123787 189191 := bstep (se 1 (by rfl) ⟨141893, by rfl⟩ : syracuseStep 189191 = 283787) B283787
theorem B680737 : Blo 123787 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B189227 : Blo 123787 189227 := bstep (se 1 (by rfl) ⟨141920, by rfl⟩ : syracuseStep 189227 = 283841) B283841
theorem B189257 : Blo 123787 189257 := bstep (se 2 (by rfl) ⟨70971, by rfl⟩ : syracuseStep 189257 = 141943) B141943
theorem B320375 : Blo 123787 320375 := bstep (se 1 (by rfl) ⟨240281, by rfl⟩ : syracuseStep 320375 = 480563) B480563
theorem B123791 : Blo 123787 123791 := bstep (se 1 (by rfl) ⟨92843, by rfl⟩ : syracuseStep 123791 = 185687) B185687
theorem B123835 : Blo 123787 123835 := bstep (se 1 (by rfl) ⟨92876, by rfl⟩ : syracuseStep 123835 = 185753) B185753
theorem B189371 : Blo 123787 189371 := bstep (se 1 (by rfl) ⟨142028, by rfl⟩ : syracuseStep 189371 = 284057) B284057
theorem B189431 : Blo 123787 189431 := bstep (se 1 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 189431 = 284147) B284147
theorem B353281 : Blo 123787 353281 := bstep (se 2 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 353281 = 264961) B264961
theorem B123911 : Blo 123787 123911 := bstep (se 1 (by rfl) ⟨92933, by rfl⟩ : syracuseStep 123911 = 185867) B185867
theorem B123919 : Blo 123787 123919 := bstep (se 1 (by rfl) ⟨92939, by rfl⟩ : syracuseStep 123919 = 185879) B185879
theorem B189455 : Blo 123787 189455 := bstep (se 1 (by rfl) ⟨142091, by rfl⟩ : syracuseStep 189455 = 284183) B284183
theorem B189497 : Blo 123787 189497 := bstep (se 2 (by rfl) ⟨71061, by rfl⟩ : syracuseStep 189497 = 142123) B142123
theorem B123963 : Blo 123787 123963 := bstep (se 1 (by rfl) ⟨92972, by rfl⟩ : syracuseStep 123963 = 185945) B185945
theorem B418877 : Blo 123787 418877 := bstep (se 3 (by rfl) ⟨78539, by rfl⟩ : syracuseStep 418877 = 157079) B157079
theorem B124039 : Blo 123787 124039 := bstep (se 1 (by rfl) ⟨93029, by rfl⟩ : syracuseStep 124039 = 186059) B186059
theorem B189575 : Blo 123787 189575 := bstep (se 1 (by rfl) ⟨142181, by rfl⟩ : syracuseStep 189575 = 284363) B284363
theorem B124047 : Blo 123787 124047 := bstep (se 1 (by rfl) ⟨93035, by rfl⟩ : syracuseStep 124047 = 186071) B186071
theorem B189611 : Blo 123787 189611 := bstep (se 1 (by rfl) ⟨142208, by rfl⟩ : syracuseStep 189611 = 284417) B284417
theorem B124091 : Blo 123787 124091 := bstep (se 1 (by rfl) ⟨93068, by rfl⟩ : syracuseStep 124091 = 186137) B186137
theorem B189641 : Blo 123787 189641 := bstep (se 2 (by rfl) ⟨71115, by rfl⟩ : syracuseStep 189641 = 142231) B142231
theorem B124167 : Blo 123787 124167 := bstep (se 1 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 124167 = 186251) B186251
theorem B124175 : Blo 123787 124175 := bstep (se 1 (by rfl) ⟨93131, by rfl⟩ : syracuseStep 124175 = 186263) B186263
theorem B124219 : Blo 123787 124219 := bstep (se 1 (by rfl) ⟨93164, by rfl⟩ : syracuseStep 124219 = 186329) B186329
theorem B189755 : Blo 123787 189755 := bstep (se 1 (by rfl) ⟨142316, by rfl⟩ : syracuseStep 189755 = 284633) B284633
theorem B189815 : Blo 123787 189815 := bstep (se 1 (by rfl) ⟨142361, by rfl⟩ : syracuseStep 189815 = 284723) B284723
theorem B1795459 : Blo 123787 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B124295 : Blo 123787 124295 := bstep (se 1 (by rfl) ⟨93221, by rfl⟩ : syracuseStep 124295 = 186443) B186443
theorem B124303 : Blo 123787 124303 := bstep (se 1 (by rfl) ⟨93227, by rfl⟩ : syracuseStep 124303 = 186455) B186455
theorem B189839 : Blo 123787 189839 := bstep (se 1 (by rfl) ⟨142379, by rfl⟩ : syracuseStep 189839 = 284759) B284759
theorem B189881 : Blo 123787 189881 := bstep (se 2 (by rfl) ⟨71205, by rfl⟩ : syracuseStep 189881 = 142411) B142411
theorem B124347 : Blo 123787 124347 := bstep (se 1 (by rfl) ⟨93260, by rfl⟩ : syracuseStep 124347 = 186521) B186521
theorem B124423 : Blo 123787 124423 := bstep (se 1 (by rfl) ⟨93317, by rfl⟩ : syracuseStep 124423 = 186635) B186635
theorem B189959 : Blo 123787 189959 := bstep (se 1 (by rfl) ⟨142469, by rfl⟩ : syracuseStep 189959 = 284939) B284939
theorem B124431 : Blo 123787 124431 := bstep (se 1 (by rfl) ⟨93323, by rfl⟩ : syracuseStep 124431 = 186647) B186647
theorem B189995 : Blo 123787 189995 := bstep (se 1 (by rfl) ⟨142496, by rfl⟩ : syracuseStep 189995 = 284993) B284993
theorem B124475 : Blo 123787 124475 := bstep (se 1 (by rfl) ⟨93356, by rfl⟩ : syracuseStep 124475 = 186713) B186713
theorem B190025 : Blo 123787 190025 := bstep (se 2 (by rfl) ⟨71259, by rfl⟩ : syracuseStep 190025 = 142519) B142519
theorem B124551 : Blo 123787 124551 := bstep (se 1 (by rfl) ⟨93413, by rfl⟩ : syracuseStep 124551 = 186827) B186827
theorem B124559 : Blo 123787 124559 := bstep (se 1 (by rfl) ⟨93419, by rfl⟩ : syracuseStep 124559 = 186839) B186839
theorem B353945 : Blo 123787 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B124603 : Blo 123787 124603 := bstep (se 1 (by rfl) ⟨93452, by rfl⟩ : syracuseStep 124603 = 186905) B186905
theorem B190139 : Blo 123787 190139 := bstep (se 1 (by rfl) ⟨142604, by rfl⟩ : syracuseStep 190139 = 285209) B285209
theorem B190199 : Blo 123787 190199 := bstep (se 1 (by rfl) ⟨142649, by rfl⟩ : syracuseStep 190199 = 285299) B285299
theorem B124679 : Blo 123787 124679 := bstep (se 1 (by rfl) ⟨93509, by rfl⟩ : syracuseStep 124679 = 187019) B187019
theorem B124687 : Blo 123787 124687 := bstep (se 1 (by rfl) ⟨93515, by rfl⟩ : syracuseStep 124687 = 187031) B187031
theorem B190223 : Blo 123787 190223 := bstep (se 1 (by rfl) ⟨142667, by rfl⟩ : syracuseStep 190223 = 285335) B285335
theorem B485135 : Blo 123787 485135 := bstep (se 1 (by rfl) ⟨363851, by rfl⟩ : syracuseStep 485135 = 727703) B727703
theorem B485153 : Blo 123787 485153 := bstep (se 2 (by rfl) ⟨181932, by rfl⟩ : syracuseStep 485153 = 363865) B363865
theorem B190265 : Blo 123787 190265 := bstep (se 2 (by rfl) ⟨71349, by rfl⟩ : syracuseStep 190265 = 142699) B142699
theorem B124731 : Blo 123787 124731 := bstep (se 1 (by rfl) ⟨93548, by rfl⟩ : syracuseStep 124731 = 187097) B187097
theorem B321367 : Blo 123787 321367 := bstep (se 1 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 321367 = 482051) B482051
theorem B124807 : Blo 123787 124807 := bstep (se 1 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 124807 = 187211) B187211
theorem B190343 : Blo 123787 190343 := bstep (se 1 (by rfl) ⟨142757, by rfl⟩ : syracuseStep 190343 = 285515) B285515
theorem B124815 : Blo 123787 124815 := bstep (se 1 (by rfl) ⟨93611, by rfl⟩ : syracuseStep 124815 = 187223) B187223
theorem B190379 : Blo 123787 190379 := bstep (se 1 (by rfl) ⟨142784, by rfl⟩ : syracuseStep 190379 = 285569) B285569
theorem B124859 : Blo 123787 124859 := bstep (se 1 (by rfl) ⟨93644, by rfl⟩ : syracuseStep 124859 = 187289) B187289
theorem B190409 : Blo 123787 190409 := bstep (se 2 (by rfl) ⟨71403, by rfl⟩ : syracuseStep 190409 = 142807) B142807
theorem B124935 : Blo 123787 124935 := bstep (se 1 (by rfl) ⟨93701, by rfl⟩ : syracuseStep 124935 = 187403) B187403
theorem B124943 : Blo 123787 124943 := bstep (se 1 (by rfl) ⟨93707, by rfl⟩ : syracuseStep 124943 = 187415) B187415
theorem B124987 : Blo 123787 124987 := bstep (se 1 (by rfl) ⟨93740, by rfl⟩ : syracuseStep 124987 = 187481) B187481
theorem B190523 : Blo 123787 190523 := bstep (se 1 (by rfl) ⟨142892, by rfl⟩ : syracuseStep 190523 = 285785) B285785
theorem B190583 : Blo 123787 190583 := bstep (se 1 (by rfl) ⟨142937, by rfl⟩ : syracuseStep 190583 = 285875) B285875
theorem B125063 : Blo 123787 125063 := bstep (se 1 (by rfl) ⟨93797, by rfl⟩ : syracuseStep 125063 = 187595) B187595
theorem B321671 : Blo 123787 321671 := bstep (se 1 (by rfl) ⟨241253, by rfl⟩ : syracuseStep 321671 = 482507) B482507
theorem B125071 : Blo 123787 125071 := bstep (se 1 (by rfl) ⟨93803, by rfl⟩ : syracuseStep 125071 = 187607) B187607
theorem B190607 : Blo 123787 190607 := bstep (se 1 (by rfl) ⟨142955, by rfl⟩ : syracuseStep 190607 = 285911) B285911
theorem B190649 : Blo 123787 190649 := bstep (se 2 (by rfl) ⟨71493, by rfl⟩ : syracuseStep 190649 = 142987) B142987
theorem B125115 : Blo 123787 125115 := bstep (se 1 (by rfl) ⟨93836, by rfl⟩ : syracuseStep 125115 = 187673) B187673
theorem B125191 : Blo 123787 125191 := bstep (se 1 (by rfl) ⟨93893, by rfl⟩ : syracuseStep 125191 = 187787) B187787
theorem B190727 : Blo 123787 190727 := bstep (se 1 (by rfl) ⟨143045, by rfl⟩ : syracuseStep 190727 = 286091) B286091
theorem B321803 : Blo 123787 321803 := bstep (se 1 (by rfl) ⟨241352, by rfl⟩ : syracuseStep 321803 = 482705) B482705
theorem B125199 : Blo 123787 125199 := bstep (se 1 (by rfl) ⟨93899, by rfl⟩ : syracuseStep 125199 = 187799) B187799
theorem B190763 : Blo 123787 190763 := bstep (se 1 (by rfl) ⟨143072, by rfl⟩ : syracuseStep 190763 = 286145) B286145
theorem B125243 : Blo 123787 125243 := bstep (se 1 (by rfl) ⟨93932, by rfl⟩ : syracuseStep 125243 = 187865) B187865
theorem B190793 : Blo 123787 190793 := bstep (se 2 (by rfl) ⟨71547, by rfl⟩ : syracuseStep 190793 = 143095) B143095
theorem B125319 : Blo 123787 125319 := bstep (se 1 (by rfl) ⟨93989, by rfl⟩ : syracuseStep 125319 = 187979) B187979
theorem B125327 : Blo 123787 125327 := bstep (se 1 (by rfl) ⟨93995, by rfl⟩ : syracuseStep 125327 = 187991) B187991
theorem B453017 : Blo 123787 453017 := bstep (se 2 (by rfl) ⟨169881, by rfl⟩ : syracuseStep 453017 = 339763) B339763
theorem B420281 : Blo 123787 420281 := bstep (se 2 (by rfl) ⟨157605, by rfl⟩ : syracuseStep 420281 = 315211) B315211
theorem B125371 : Blo 123787 125371 := bstep (se 1 (by rfl) ⟨94028, by rfl⟩ : syracuseStep 125371 = 188057) B188057
theorem B190907 : Blo 123787 190907 := bstep (se 1 (by rfl) ⟨143180, by rfl⟩ : syracuseStep 190907 = 286361) B286361
theorem B190967 : Blo 123787 190967 := bstep (se 1 (by rfl) ⟨143225, by rfl⟩ : syracuseStep 190967 = 286451) B286451
theorem B125447 : Blo 123787 125447 := bstep (se 1 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 125447 = 188171) B188171
theorem B125455 : Blo 123787 125455 := bstep (se 1 (by rfl) ⟨94091, by rfl⟩ : syracuseStep 125455 = 188183) B188183
theorem B289295 : Blo 123787 289295 := bstep (se 1 (by rfl) ⟨216971, by rfl⟩ : syracuseStep 289295 = 433943) B433943
theorem B190991 : Blo 123787 190991 := bstep (se 1 (by rfl) ⟨143243, by rfl⟩ : syracuseStep 190991 = 286487) B286487
theorem B191033 : Blo 123787 191033 := bstep (se 2 (by rfl) ⟨71637, by rfl⟩ : syracuseStep 191033 = 143275) B143275
theorem B125499 : Blo 123787 125499 := bstep (se 1 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 125499 = 188249) B188249
theorem B715331 : Blo 123787 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B125575 : Blo 123787 125575 := bstep (se 1 (by rfl) ⟨94181, by rfl⟩ : syracuseStep 125575 = 188363) B188363
theorem B191111 : Blo 123787 191111 := bstep (se 1 (by rfl) ⟨143333, by rfl⟩ : syracuseStep 191111 = 286667) B286667
theorem B125583 : Blo 123787 125583 := bstep (se 1 (by rfl) ⟨94187, by rfl⟩ : syracuseStep 125583 = 188375) B188375
theorem B191147 : Blo 123787 191147 := bstep (se 1 (by rfl) ⟨143360, by rfl⟩ : syracuseStep 191147 = 286721) B286721
theorem B256697 : Blo 123787 256697 := bstep (se 2 (by rfl) ⟨96261, by rfl⟩ : syracuseStep 256697 = 192523) B192523
theorem B125627 : Blo 123787 125627 := bstep (se 1 (by rfl) ⟨94220, by rfl⟩ : syracuseStep 125627 = 188441) B188441
theorem B191177 : Blo 123787 191177 := bstep (se 2 (by rfl) ⟨71691, by rfl⟩ : syracuseStep 191177 = 143383) B143383
theorem B125703 : Blo 123787 125703 := bstep (se 1 (by rfl) ⟨94277, by rfl⟩ : syracuseStep 125703 = 188555) B188555
theorem B125711 : Blo 123787 125711 := bstep (se 1 (by rfl) ⟨94283, by rfl⟩ : syracuseStep 125711 = 188567) B188567
theorem B322319 : Blo 123787 322319 := bstep (se 1 (by rfl) ⟨241739, by rfl⟩ : syracuseStep 322319 = 483479) B483479
theorem B125755 : Blo 123787 125755 := bstep (se 1 (by rfl) ⟨94316, by rfl⟩ : syracuseStep 125755 = 188633) B188633
theorem B191291 : Blo 123787 191291 := bstep (se 1 (by rfl) ⟨143468, by rfl⟩ : syracuseStep 191291 = 286937) B286937
theorem B191351 : Blo 123787 191351 := bstep (se 1 (by rfl) ⟨143513, by rfl⟩ : syracuseStep 191351 = 287027) B287027
theorem B125831 : Blo 123787 125831 := bstep (se 1 (by rfl) ⟨94373, by rfl⟩ : syracuseStep 125831 = 188747) B188747
theorem B125839 : Blo 123787 125839 := bstep (se 1 (by rfl) ⟨94379, by rfl⟩ : syracuseStep 125839 = 188759) B188759
theorem B191375 : Blo 123787 191375 := bstep (se 1 (by rfl) ⟨143531, by rfl⟩ : syracuseStep 191375 = 287063) B287063
theorem B322451 : Blo 123787 322451 := bstep (se 1 (by rfl) ⟨241838, by rfl⟩ : syracuseStep 322451 = 483677) B483677
theorem B191417 : Blo 123787 191417 := bstep (se 2 (by rfl) ⟨71781, by rfl⟩ : syracuseStep 191417 = 143563) B143563
theorem B125883 : Blo 123787 125883 := bstep (se 1 (by rfl) ⟨94412, by rfl⟩ : syracuseStep 125883 = 188825) B188825
theorem B125959 : Blo 123787 125959 := bstep (se 1 (by rfl) ⟨94469, by rfl⟩ : syracuseStep 125959 = 188939) B188939
theorem B191495 : Blo 123787 191495 := bstep (se 1 (by rfl) ⟨143621, by rfl⟩ : syracuseStep 191495 = 287243) B287243
theorem B420875 : Blo 123787 420875 := bstep (se 1 (by rfl) ⟨315656, by rfl⟩ : syracuseStep 420875 = 631313) B631313
theorem B715787 : Blo 123787 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B125967 : Blo 123787 125967 := bstep (se 1 (by rfl) ⟨94475, by rfl⟩ : syracuseStep 125967 = 188951) B188951
theorem B191531 : Blo 123787 191531 := bstep (se 1 (by rfl) ⟨143648, by rfl⟩ : syracuseStep 191531 = 287297) B287297
theorem B126011 : Blo 123787 126011 := bstep (se 1 (by rfl) ⟨94508, by rfl⟩ : syracuseStep 126011 = 189017) B189017
theorem B191561 : Blo 123787 191561 := bstep (se 2 (by rfl) ⟨71835, by rfl⟩ : syracuseStep 191561 = 143671) B143671
theorem B420983 : Blo 123787 420983 := bstep (se 1 (by rfl) ⟨315737, by rfl⟩ : syracuseStep 420983 = 631475) B631475
theorem B126087 : Blo 123787 126087 := bstep (se 1 (by rfl) ⟨94565, by rfl⟩ : syracuseStep 126087 = 189131) B189131
theorem B126095 : Blo 123787 126095 := bstep (se 1 (by rfl) ⟨94571, by rfl⟩ : syracuseStep 126095 = 189143) B189143
theorem B126139 : Blo 123787 126139 := bstep (se 1 (by rfl) ⟨94604, by rfl⟩ : syracuseStep 126139 = 189209) B189209
theorem B191675 : Blo 123787 191675 := bstep (se 1 (by rfl) ⟨143756, by rfl⟩ : syracuseStep 191675 = 287513) B287513
theorem B126215 : Blo 123787 126215 := bstep (se 1 (by rfl) ⟨94661, by rfl⟩ : syracuseStep 126215 = 189323) B189323
theorem B126223 : Blo 123787 126223 := bstep (se 1 (by rfl) ⟨94667, by rfl⟩ : syracuseStep 126223 = 189335) B189335
theorem B126267 : Blo 123787 126267 := bstep (se 1 (by rfl) ⟨94700, by rfl⟩ : syracuseStep 126267 = 189401) B189401
theorem B126343 : Blo 123787 126343 := bstep (se 1 (by rfl) ⟨94757, by rfl⟩ : syracuseStep 126343 = 189515) B189515
theorem B126351 : Blo 123787 126351 := bstep (se 1 (by rfl) ⟨94763, by rfl⟩ : syracuseStep 126351 = 189527) B189527
theorem B126395 : Blo 123787 126395 := bstep (se 1 (by rfl) ⟨94796, by rfl⟩ : syracuseStep 126395 = 189593) B189593
theorem B847325 : Blo 123787 847325 := bstep (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) B317747
theorem B126471 : Blo 123787 126471 := bstep (se 1 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 126471 = 189707) B189707
theorem B126479 : Blo 123787 126479 := bstep (se 1 (by rfl) ⟨94859, by rfl⟩ : syracuseStep 126479 = 189719) B189719
theorem B126523 : Blo 123787 126523 := bstep (se 1 (by rfl) ⟨94892, by rfl⟩ : syracuseStep 126523 = 189785) B189785
theorem B126599 : Blo 123787 126599 := bstep (se 1 (by rfl) ⟨94949, by rfl⟩ : syracuseStep 126599 = 189899) B189899
theorem B126607 : Blo 123787 126607 := bstep (se 1 (by rfl) ⟨94955, by rfl⟩ : syracuseStep 126607 = 189911) B189911
theorem B159403 : Blo 123787 159403 := bstep (se 1 (by rfl) ⟨119552, by rfl⟩ : syracuseStep 159403 = 239105) B239105
theorem B126651 : Blo 123787 126651 := bstep (se 1 (by rfl) ⟨94988, by rfl⟩ : syracuseStep 126651 = 189977) B189977
theorem B421577 : Blo 123787 421577 := bstep (se 2 (by rfl) ⟨158091, by rfl⟩ : syracuseStep 421577 = 316183) B316183
theorem B126727 : Blo 123787 126727 := bstep (se 1 (by rfl) ⟨95045, by rfl⟩ : syracuseStep 126727 = 190091) B190091
theorem B126735 : Blo 123787 126735 := bstep (se 1 (by rfl) ⟨95051, by rfl⟩ : syracuseStep 126735 = 190103) B190103
theorem B126779 : Blo 123787 126779 := bstep (se 1 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 126779 = 190169) B190169
theorem B2420549 : Blo 123787 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B388979 : Blo 123787 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B356231 : Blo 123787 356231 := bstep (se 1 (by rfl) ⟨267173, by rfl⟩ : syracuseStep 356231 = 534347) B534347
theorem B126855 : Blo 123787 126855 := bstep (se 1 (by rfl) ⟨95141, by rfl⟩ : syracuseStep 126855 = 190283) B190283
theorem B126863 : Blo 123787 126863 := bstep (se 1 (by rfl) ⟨95147, by rfl⟩ : syracuseStep 126863 = 190295) B190295
theorem B454547 : Blo 123787 454547 := bstep (se 1 (by rfl) ⟨340910, by rfl⟩ : syracuseStep 454547 = 681821) B681821
theorem B126907 : Blo 123787 126907 := bstep (se 1 (by rfl) ⟨95180, by rfl⟩ : syracuseStep 126907 = 190361) B190361
theorem B126983 : Blo 123787 126983 := bstep (se 1 (by rfl) ⟨95237, by rfl⟩ : syracuseStep 126983 = 190475) B190475
theorem B126991 : Blo 123787 126991 := bstep (se 1 (by rfl) ⟨95243, by rfl⟩ : syracuseStep 126991 = 190487) B190487
theorem B127035 : Blo 123787 127035 := bstep (se 1 (by rfl) ⟨95276, by rfl⟩ : syracuseStep 127035 = 190553) B190553
theorem B356413 : Blo 123787 356413 := bstep (se 3 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 356413 = 133655) B133655
theorem B5009501 : Blo 123787 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B356471 : Blo 123787 356471 := bstep (se 1 (by rfl) ⟨267353, by rfl⟩ : syracuseStep 356471 = 534707) B534707
theorem B127111 : Blo 123787 127111 := bstep (se 1 (by rfl) ⟨95333, by rfl⟩ : syracuseStep 127111 = 190667) B190667
theorem B127119 : Blo 123787 127119 := bstep (se 1 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 127119 = 190679) B190679
theorem B127163 : Blo 123787 127163 := bstep (se 1 (by rfl) ⟨95372, by rfl⟩ : syracuseStep 127163 = 190745) B190745
theorem B127239 : Blo 123787 127239 := bstep (se 1 (by rfl) ⟨95429, by rfl⟩ : syracuseStep 127239 = 190859) B190859
theorem B127247 : Blo 123787 127247 := bstep (se 1 (by rfl) ⟨95435, by rfl⟩ : syracuseStep 127247 = 190871) B190871
theorem B127291 : Blo 123787 127291 := bstep (se 1 (by rfl) ⟨95468, by rfl⟩ : syracuseStep 127291 = 190937) B190937
theorem B422279 : Blo 123787 422279 := bstep (se 1 (by rfl) ⟨316709, by rfl⟩ : syracuseStep 422279 = 633419) B633419
theorem B127367 : Blo 123787 127367 := bstep (se 1 (by rfl) ⟨95525, by rfl⟩ : syracuseStep 127367 = 191051) B191051
theorem B127375 : Blo 123787 127375 := bstep (se 1 (by rfl) ⟨95531, by rfl⟩ : syracuseStep 127375 = 191063) B191063
theorem B127419 : Blo 123787 127419 := bstep (se 1 (by rfl) ⟨95564, by rfl⟩ : syracuseStep 127419 = 191129) B191129
theorem B127495 : Blo 123787 127495 := bstep (se 1 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 127495 = 191243) B191243
theorem B127503 : Blo 123787 127503 := bstep (se 1 (by rfl) ⟨95627, by rfl⟩ : syracuseStep 127503 = 191255) B191255
theorem B127547 : Blo 123787 127547 := bstep (se 1 (by rfl) ⟨95660, by rfl⟩ : syracuseStep 127547 = 191321) B191321
theorem B1340023 : Blo 123787 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B160375 : Blo 123787 160375 := bstep (se 1 (by rfl) ⟨120281, by rfl⟩ : syracuseStep 160375 = 240563) B240563
theorem B127623 : Blo 123787 127623 := bstep (se 1 (by rfl) ⟨95717, by rfl⟩ : syracuseStep 127623 = 191435) B191435
theorem B127631 : Blo 123787 127631 := bstep (se 1 (by rfl) ⟨95723, by rfl⟩ : syracuseStep 127631 = 191447) B191447
theorem B127675 : Blo 123787 127675 := bstep (se 1 (by rfl) ⟨95756, by rfl⟩ : syracuseStep 127675 = 191513) B191513
theorem B422657 : Blo 123787 422657 := bstep (se 2 (by rfl) ⟨158496, by rfl⟩ : syracuseStep 422657 = 316993) B316993
theorem B127751 : Blo 123787 127751 := bstep (se 1 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 127751 = 191627) B191627
theorem B127759 : Blo 123787 127759 := bstep (se 1 (by rfl) ⟨95819, by rfl⟩ : syracuseStep 127759 = 191639) B191639
theorem B684935 : Blo 123787 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B160699 : Blo 123787 160699 := bstep (se 1 (by rfl) ⟨120524, by rfl⟩ : syracuseStep 160699 = 241049) B241049
theorem B226423 : Blo 123787 226423 := bstep (se 1 (by rfl) ⟨169817, by rfl⟩ : syracuseStep 226423 = 339635) B339635
theorem B357529 : Blo 123787 357529 := bstep (se 2 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 357529 = 268147) B268147
theorem B20903345 : Blo 123787 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B423467 : Blo 123787 423467 := bstep (se 1 (by rfl) ⟨317600, by rfl⟩ : syracuseStep 423467 = 635201) B635201
theorem B358145 : Blo 123787 358145 := bstep (se 2 (by rfl) ⟨134304, by rfl⟩ : syracuseStep 358145 = 268609) B268609
theorem B161671 : Blo 123787 161671 := bstep (se 1 (by rfl) ⟨121253, by rfl⟩ : syracuseStep 161671 = 242507) B242507
theorem B161707 : Blo 123787 161707 := bstep (se 1 (by rfl) ⟨121280, by rfl⟩ : syracuseStep 161707 = 242561) B242561
theorem B784673 : Blo 123787 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B359113 : Blo 123787 359113 := bstep (se 2 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 359113 = 269335) B269335
theorem B326443 : Blo 123787 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B424763 : Blo 123787 424763 := bstep (se 1 (by rfl) ⟨318572, by rfl⟩ : syracuseStep 424763 = 637145) B637145
theorem B719705 : Blo 123787 719705 := bstep (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) B539779
theorem B720161 : Blo 123787 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B425249 : Blo 123787 425249 := bstep (se 2 (by rfl) ⟨159468, by rfl⟩ : syracuseStep 425249 = 318937) B318937
theorem B195959 : Blo 123787 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B720413 : Blo 123787 720413 := bstep (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) B270155
theorem B425843 : Blo 123787 425843 := bstep (se 1 (by rfl) ⟨319382, by rfl⟩ : syracuseStep 425843 = 638765) B638765
theorem B1572941 : Blo 123787 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B360605 : Blo 123787 360605 := bstep (se 3 (by rfl) ⟨67613, by rfl⟩ : syracuseStep 360605 = 135227) B135227
theorem B721163 : Blo 123787 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B950615 : Blo 123787 950615 := bstep (se 1 (by rfl) ⟨712961, by rfl⟩ : syracuseStep 950615 = 1425923) B1425923
theorem B426383 : Blo 123787 426383 := bstep (se 1 (by rfl) ⟨319787, by rfl⟩ : syracuseStep 426383 = 639575) B639575
theorem B459245 : Blo 123787 459245 := bstep (se 3 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 459245 = 172217) B172217
theorem B459361 : Blo 123787 459361 := bstep (se 2 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 459361 = 344521) B344521
theorem B426707 : Blo 123787 426707 := bstep (se 1 (by rfl) ⟨320030, by rfl⟩ : syracuseStep 426707 = 640061) B640061
theorem B721619 : Blo 123787 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B459475 : Blo 123787 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B459593 : Blo 123787 459593 := bstep (se 2 (by rfl) ⟨172347, by rfl⟩ : syracuseStep 459593 = 344695) B344695
theorem B460313 : Blo 123787 460313 := bstep (se 2 (by rfl) ⟨172617, by rfl⟩ : syracuseStep 460313 = 345235) B345235
theorem B3409451 : Blo 123787 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B722621 : Blo 123787 722621 := bstep (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) B270983
theorem B821035 : Blo 123787 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B2393945 : Blo 123787 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B132959 : Blo 123787 132959 := bstep (se 1 (by rfl) ⟨99719, by rfl⟩ : syracuseStep 132959 = 199439) B199439
theorem B427895 : Blo 123787 427895 := bstep (se 1 (by rfl) ⟨320921, by rfl⟩ : syracuseStep 427895 = 641843) B641843
theorem B198587 : Blo 123787 198587 := bstep (se 1 (by rfl) ⟨148940, by rfl⟩ : syracuseStep 198587 = 297881) B297881
theorem B428111 : Blo 123787 428111 := bstep (se 1 (by rfl) ⟨321083, by rfl⟩ : syracuseStep 428111 = 642167) B642167
theorem B723329 : Blo 123787 723329 := bstep (se 2 (by rfl) ⟨271248, by rfl⟩ : syracuseStep 723329 = 542497) B542497
theorem B428489 : Blo 123787 428489 := bstep (se 2 (by rfl) ⟨160683, by rfl⟩ : syracuseStep 428489 = 321367) B321367
theorem B30771683 : Blo 123787 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B5474951 : Blo 123787 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B428759 : Blo 123787 428759 := bstep (se 1 (by rfl) ⟨321569, by rfl⟩ : syracuseStep 428759 = 643139) B643139
theorem B428975 : Blo 123787 428975 := bstep (se 1 (by rfl) ⟨321731, by rfl⟩ : syracuseStep 428975 = 643463) B643463
theorem B2067383 : Blo 123787 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B1510595 : Blo 123787 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B1609085 : Blo 123787 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B855539 : Blo 123787 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B396839 : Blo 123787 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B429715 : Blo 123787 429715 := bstep (se 1 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 429715 = 644573) B644573
theorem B626777 : Blo 123787 626777 := bstep (se 2 (by rfl) ⟨235041, by rfl⟩ : syracuseStep 626777 = 470083) B470083
theorem B725537 : Blo 123787 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B266951 : Blo 123787 266951 := bstep (se 1 (by rfl) ⟨200213, by rfl⟩ : syracuseStep 266951 = 400427) B400427
theorem B5083955 : Blo 123787 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B398267 : Blo 123787 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B201899 : Blo 123787 201899 := bstep (se 1 (by rfl) ⟨151424, by rfl⟩ : syracuseStep 201899 = 302849) B302849
theorem B7968131 : Blo 123787 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B300667 : Blo 123787 300667 := bstep (se 1 (by rfl) ⟨225500, by rfl⟩ : syracuseStep 300667 = 451001) B451001
theorem B268105 : Blo 123787 268105 := bstep (se 2 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 268105 = 201079) B201079
theorem B235963 : Blo 123787 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B7740035 : Blo 123787 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B301897 : Blo 123787 301897 := bstep (se 2 (by rfl) ⟨113211, by rfl⟩ : syracuseStep 301897 = 226423) B226423
theorem B302011 : Blo 123787 302011 := bstep (se 1 (by rfl) ⟨226508, by rfl⟩ : syracuseStep 302011 = 453017) B453017
theorem B171131 : Blo 123787 171131 := bstep (se 1 (by rfl) ⟨128348, by rfl⟩ : syracuseStep 171131 = 256697) B256697
theorem B400555 : Blo 123787 400555 := bstep (se 1 (by rfl) ⟨300416, by rfl⟩ : syracuseStep 400555 = 600833) B600833
theorem B400631 : Blo 123787 400631 := bstep (se 1 (by rfl) ⟨300473, by rfl⟩ : syracuseStep 400631 = 600947) B600947
theorem B1449251 : Blo 123787 1449251 := bstep (se 1 (by rfl) ⟨1086938, by rfl⟩ : syracuseStep 1449251 = 2173877) B2173877
theorem B466319 : Blo 123787 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B597719 : Blo 123787 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B237305 : Blo 123787 237305 := bstep (se 2 (by rfl) ⟨88989, by rfl⟩ : syracuseStep 237305 = 177979) B177979
theorem B1613699 : Blo 123787 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B237487 : Blo 123787 237487 := bstep (se 1 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 237487 = 356231) B356231
theorem B303031 : Blo 123787 303031 := bstep (se 1 (by rfl) ⟨227273, by rfl⟩ : syracuseStep 303031 = 454547) B454547
theorem B237647 : Blo 123787 237647 := bstep (se 1 (by rfl) ⟨178235, by rfl⟩ : syracuseStep 237647 = 356471) B356471
theorem B139387 : Blo 123787 139387 := bstep (se 1 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 139387 = 209081) B209081
theorem B17375633 : Blo 123787 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B139855 : Blo 123787 139855 := bstep (se 1 (by rfl) ⟨104891, by rfl⟩ : syracuseStep 139855 = 209783) B209783
theorem B3449749 : Blo 123787 3449749 := bstep (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) B161707
theorem B205751 : Blo 123787 205751 := bstep (se 1 (by rfl) ⟨154313, by rfl⟩ : syracuseStep 205751 = 308627) B308627
theorem B271291 : Blo 123787 271291 := bstep (se 1 (by rfl) ⟨203468, by rfl⟩ : syracuseStep 271291 = 406937) B406937
theorem B13935563 : Blo 123787 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B140251 : Blo 123787 140251 := bstep (se 1 (by rfl) ⟨105188, by rfl⟩ : syracuseStep 140251 = 210377) B210377
theorem B336953 : Blo 123787 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B435257 : Blo 123787 435257 := bstep (se 2 (by rfl) ⟨163221, by rfl⟩ : syracuseStep 435257 = 326443) B326443
theorem B205903 : Blo 123787 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B631961 : Blo 123787 631961 := bstep (se 2 (by rfl) ⟨236985, by rfl⟩ : syracuseStep 631961 = 473971) B473971
theorem B238763 : Blo 123787 238763 := bstep (se 1 (by rfl) ⟨179072, by rfl⟩ : syracuseStep 238763 = 358145) B358145
theorem B140719 : Blo 123787 140719 := bstep (se 1 (by rfl) ⟨105539, by rfl⟩ : syracuseStep 140719 = 211079) B211079
theorem B2762387 : Blo 123787 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B141151 : Blo 123787 141151 := bstep (se 1 (by rfl) ⟨105863, by rfl⟩ : syracuseStep 141151 = 211727) B211727
theorem B141511 : Blo 123787 141511 := bstep (se 1 (by rfl) ⟨106133, by rfl⟩ : syracuseStep 141511 = 212267) B212267
theorem B240479 : Blo 123787 240479 := bstep (se 1 (by rfl) ⟨180359, by rfl⟩ : syracuseStep 240479 = 360719) B360719
theorem B1354643 : Blo 123787 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B142375 : Blo 123787 142375 := bstep (se 1 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 142375 = 213563) B213563
theorem B535747 : Blo 123787 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B863435 : Blo 123787 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B240889 : Blo 123787 240889 := bstep (se 2 (by rfl) ⟨90333, by rfl⟩ : syracuseStep 240889 = 180667) B180667
theorem B241231 : Blo 123787 241231 := bstep (se 1 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 241231 = 361847) B361847
theorem B798497 : Blo 123787 798497 := bstep (se 2 (by rfl) ⟨299436, by rfl⟩ : syracuseStep 798497 = 598873) B598873
theorem B241481 : Blo 123787 241481 := bstep (se 2 (by rfl) ⟨90555, by rfl⟩ : syracuseStep 241481 = 181111) B181111
theorem B471041 : Blo 123787 471041 := bstep (se 2 (by rfl) ⟨176640, by rfl⟩ : syracuseStep 471041 = 353281) B353281
theorem B471055 : Blo 123787 471055 := bstep (se 1 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 471055 = 706583) B706583
theorem B209371 : Blo 123787 209371 := bstep (se 1 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 209371 = 314057) B314057
theorem B242347 : Blo 123787 242347 := bstep (se 1 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 242347 = 363521) B363521
theorem B406205 : Blo 123787 406205 := bstep (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) B152327
theorem B1061585 : Blo 123787 1061585 := bstep (se 2 (by rfl) ⟨398094, by rfl⟩ : syracuseStep 1061585 = 796189) B796189
theorem B242423 : Blo 123787 242423 := bstep (se 1 (by rfl) ⟨181817, by rfl⟩ : syracuseStep 242423 = 363635) B363635
theorem B177079 : Blo 123787 177079 := bstep (se 1 (by rfl) ⟨132809, by rfl⟩ : syracuseStep 177079 = 265619) B265619
theorem B209999 : Blo 123787 209999 := bstep (se 1 (by rfl) ⟨157499, by rfl⟩ : syracuseStep 209999 = 314999) B314999
theorem B963737 : Blo 123787 963737 := bstep (se 2 (by rfl) ⟨361401, by rfl⟩ : syracuseStep 963737 = 722803) B722803
theorem B472331 : Blo 123787 472331 := bstep (se 1 (by rfl) ⟨354248, by rfl⟩ : syracuseStep 472331 = 708497) B708497
theorem B472787 : Blo 123787 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B1619747 : Blo 123787 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B210863 : Blo 123787 210863 := bstep (se 1 (by rfl) ⟨158147, by rfl⟩ : syracuseStep 210863 = 316295) B316295
theorem B505871 : Blo 123787 505871 := bstep (se 1 (by rfl) ⟨379403, by rfl⟩ : syracuseStep 505871 = 758807) B758807
theorem B145487 : Blo 123787 145487 := bstep (se 1 (by rfl) ⟨109115, by rfl⟩ : syracuseStep 145487 = 218231) B218231
theorem B1030259 : Blo 123787 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B801035 : Blo 123787 801035 := bstep (se 1 (by rfl) ⟨600776, by rfl⟩ : syracuseStep 801035 = 1201553) B1201553
theorem B211295 : Blo 123787 211295 := bstep (se 1 (by rfl) ⟨158471, by rfl⟩ : syracuseStep 211295 = 316943) B316943
theorem B178537 : Blo 123787 178537 := bstep (se 2 (by rfl) ⟨66951, by rfl⟩ : syracuseStep 178537 = 133903) B133903
theorem B1227113 : Blo 123787 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B473789 : Blo 123787 473789 := bstep (se 3 (by rfl) ⟨88835, by rfl⟩ : syracuseStep 473789 = 177671) B177671
theorem B211855 : Blo 123787 211855 := bstep (se 1 (by rfl) ⟨158891, by rfl⟩ : syracuseStep 211855 = 317783) B317783
theorem B408577 : Blo 123787 408577 := bstep (se 2 (by rfl) ⟨153216, by rfl⟩ : syracuseStep 408577 = 306433) B306433
theorem B179209 : Blo 123787 179209 := bstep (se 2 (by rfl) ⟨67203, by rfl⟩ : syracuseStep 179209 = 134407) B134407
theorem B965681 : Blo 123787 965681 := bstep (se 2 (by rfl) ⟨362130, by rfl⟩ : syracuseStep 965681 = 724261) B724261
theorem B212537 : Blo 123787 212537 := bstep (se 2 (by rfl) ⟨79701, by rfl⟩ : syracuseStep 212537 = 159403) B159403
theorem B638603 : Blo 123787 638603 := bstep (se 1 (by rfl) ⟨478952, by rfl⟩ : syracuseStep 638603 = 957905) B957905
theorem B802493 : Blo 123787 802493 := bstep (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) B300935
theorem B278585 : Blo 123787 278585 := bstep (se 2 (by rfl) ⟨104469, by rfl⟩ : syracuseStep 278585 = 208939) B208939
theorem B475217 : Blo 123787 475217 := bstep (se 2 (by rfl) ⟨178206, by rfl⟩ : syracuseStep 475217 = 356413) B356413
theorem B1130611 : Blo 123787 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B213239 : Blo 123787 213239 := bstep (se 1 (by rfl) ⟨159929, by rfl⟩ : syracuseStep 213239 = 319859) B319859
theorem B180473 : Blo 123787 180473 := bstep (se 2 (by rfl) ⟨67677, by rfl⟩ : syracuseStep 180473 = 135355) B135355
theorem B180587 : Blo 123787 180587 := bstep (se 1 (by rfl) ⟨135440, by rfl⟩ : syracuseStep 180587 = 270881) B270881
theorem B278927 : Blo 123787 278927 := bstep (se 1 (by rfl) ⟨209195, by rfl⟩ : syracuseStep 278927 = 418391) B418391
theorem B213583 : Blo 123787 213583 := bstep (se 1 (by rfl) ⟨160187, by rfl⟩ : syracuseStep 213583 = 320375) B320375
theorem B279251 : Blo 123787 279251 := bstep (se 1 (by rfl) ⟨209438, by rfl⟩ : syracuseStep 279251 = 418877) B418877
theorem B1786697 : Blo 123787 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B213833 : Blo 123787 213833 := bstep (se 2 (by rfl) ⟨80187, by rfl⟩ : syracuseStep 213833 = 160375) B160375
theorem B3064877 : Blo 123787 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B214265 : Blo 123787 214265 := bstep (se 2 (by rfl) ⟨80349, by rfl⟩ : syracuseStep 214265 = 160699) B160699
theorem B214447 : Blo 123787 214447 := bstep (se 1 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 214447 = 321671) B321671
theorem B214535 : Blo 123787 214535 := bstep (se 1 (by rfl) ⟨160901, by rfl⟩ : syracuseStep 214535 = 321803) B321803
theorem B476705 : Blo 123787 476705 := bstep (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) B357529
theorem B280187 : Blo 123787 280187 := bstep (se 1 (by rfl) ⟨210140, by rfl⟩ : syracuseStep 280187 = 420281) B420281
theorem B476887 : Blo 123787 476887 := bstep (se 1 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 476887 = 715331) B715331
theorem B280313 : Blo 123787 280313 := bstep (se 2 (by rfl) ⟨105117, by rfl⟩ : syracuseStep 280313 = 210235) B210235
theorem B214879 : Blo 123787 214879 := bstep (se 1 (by rfl) ⟨161159, by rfl⟩ : syracuseStep 214879 = 322319) B322319
theorem B214967 : Blo 123787 214967 := bstep (se 1 (by rfl) ⟨161225, by rfl⟩ : syracuseStep 214967 = 322451) B322451
theorem B280583 : Blo 123787 280583 := bstep (se 1 (by rfl) ⟨210437, by rfl⟩ : syracuseStep 280583 = 420875) B420875
theorem B477191 : Blo 123787 477191 := bstep (se 1 (by rfl) ⟨357893, by rfl⟩ : syracuseStep 477191 = 715787) B715787
theorem B280655 : Blo 123787 280655 := bstep (se 1 (by rfl) ⟨210491, by rfl⟩ : syracuseStep 280655 = 420983) B420983
theorem B804953 : Blo 123787 804953 := bstep (se 2 (by rfl) ⟨301857, by rfl⟩ : syracuseStep 804953 = 603715) B603715
theorem B510067 : Blo 123787 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B313591 : Blo 123787 313591 := bstep (se 1 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 313591 = 470387) B470387
theorem B182521 : Blo 123787 182521 := bstep (se 2 (by rfl) ⟨68445, by rfl⟩ : syracuseStep 182521 = 136891) B136891
theorem B903473 : Blo 123787 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B281051 : Blo 123787 281051 := bstep (se 1 (by rfl) ⟨210788, by rfl⟩ : syracuseStep 281051 = 421577) B421577
theorem B477677 : Blo 123787 477677 := bstep (se 3 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 477677 = 179129) B179129
theorem B313865 : Blo 123787 313865 := bstep (se 2 (by rfl) ⟨117699, by rfl⟩ : syracuseStep 313865 = 235399) B235399
theorem B215561 : Blo 123787 215561 := bstep (se 2 (by rfl) ⟨80835, by rfl⟩ : syracuseStep 215561 = 161671) B161671
theorem B313895 : Blo 123787 313895 := bstep (se 1 (by rfl) ⟨235421, by rfl⟩ : syracuseStep 313895 = 470843) B470843
theorem B314219 : Blo 123787 314219 := bstep (se 1 (by rfl) ⟨235664, by rfl⟩ : syracuseStep 314219 = 471329) B471329
theorem B281519 : Blo 123787 281519 := bstep (se 1 (by rfl) ⟨211139, by rfl⟩ : syracuseStep 281519 = 422279) B422279
theorem B2214839 : Blo 123787 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B281771 : Blo 123787 281771 := bstep (se 1 (by rfl) ⟨211328, by rfl⟩ : syracuseStep 281771 = 422657) B422657
theorem B708041 : Blo 123787 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B314867 : Blo 123787 314867 := bstep (se 1 (by rfl) ⟨236150, by rfl⟩ : syracuseStep 314867 = 472301) B472301
theorem B478817 : Blo 123787 478817 := bstep (se 2 (by rfl) ⟨179556, by rfl⟩ : syracuseStep 478817 = 359113) B359113
theorem B282311 : Blo 123787 282311 := bstep (se 1 (by rfl) ⟨211733, by rfl⟩ : syracuseStep 282311 = 423467) B423467
theorem B642977 : Blo 123787 642977 := bstep (se 2 (by rfl) ⟨241116, by rfl⟩ : syracuseStep 642977 = 482233) B482233
theorem B511919 : Blo 123787 511919 := bstep (se 1 (by rfl) ⟨383939, by rfl⟩ : syracuseStep 511919 = 767879) B767879
theorem B315323 : Blo 123787 315323 := bstep (se 1 (by rfl) ⟨236492, by rfl⟩ : syracuseStep 315323 = 472985) B472985
theorem B4837637 : Blo 123787 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B283175 : Blo 123787 283175 := bstep (se 1 (by rfl) ⟨212381, by rfl⟩ : syracuseStep 283175 = 424763) B424763
theorem B479803 : Blo 123787 479803 := bstep (se 1 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 479803 = 719705) B719705
theorem B316001 : Blo 123787 316001 := bstep (se 2 (by rfl) ⟨118500, by rfl⟩ : syracuseStep 316001 = 237001) B237001
theorem B905863 : Blo 123787 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B479933 : Blo 123787 479933 := bstep (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) B179975
theorem B971473 : Blo 123787 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B480107 : Blo 123787 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B283499 : Blo 123787 283499 := bstep (se 1 (by rfl) ⟨212624, by rfl⟩ : syracuseStep 283499 = 425249) B425249
theorem B283553 : Blo 123787 283553 := bstep (se 2 (by rfl) ⟨106332, by rfl⟩ : syracuseStep 283553 = 212665) B212665
theorem B480275 : Blo 123787 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B283895 : Blo 123787 283895 := bstep (se 1 (by rfl) ⟨212921, by rfl⟩ : syracuseStep 283895 = 425843) B425843
theorem B185705 : Blo 123787 185705 := bstep (se 2 (by rfl) ⟨69639, by rfl⟩ : syracuseStep 185705 = 139279) B139279
theorem B382333 : Blo 123787 382333 := bstep (se 3 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 382333 = 143375) B143375
theorem B185783 : Blo 123787 185783 := bstep (se 1 (by rfl) ⟨139337, by rfl⟩ : syracuseStep 185783 = 278675) B278675
theorem B873929 : Blo 123787 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B185819 : Blo 123787 185819 := bstep (se 1 (by rfl) ⟨139364, by rfl⟩ : syracuseStep 185819 = 278729) B278729
theorem B284489 : Blo 123787 284489 := bstep (se 2 (by rfl) ⟨106683, by rfl⟩ : syracuseStep 284489 = 213367) B213367
theorem B513911 : Blo 123787 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B186287 : Blo 123787 186287 := bstep (se 1 (by rfl) ⟨139715, by rfl⟩ : syracuseStep 186287 = 279431) B279431
theorem B186377 : Blo 123787 186377 := bstep (se 2 (by rfl) ⟨69891, by rfl⟩ : syracuseStep 186377 = 139783) B139783
theorem B317459 : Blo 123787 317459 := bstep (se 1 (by rfl) ⟨238094, by rfl⟩ : syracuseStep 317459 = 476189) B476189
theorem B186407 : Blo 123787 186407 := bstep (se 1 (by rfl) ⟨139805, by rfl⟩ : syracuseStep 186407 = 279611) B279611
theorem B186491 : Blo 123787 186491 := bstep (se 1 (by rfl) ⟨139868, by rfl⟩ : syracuseStep 186491 = 279737) B279737
theorem B186617 : Blo 123787 186617 := bstep (se 2 (by rfl) ⟨69981, by rfl⟩ : syracuseStep 186617 = 139963) B139963
theorem B186719 : Blo 123787 186719 := bstep (se 1 (by rfl) ⟨140039, by rfl⟩ : syracuseStep 186719 = 280079) B280079
theorem B186731 : Blo 123787 186731 := bstep (se 1 (by rfl) ⟨140048, by rfl⟩ : syracuseStep 186731 = 280097) B280097
theorem B907649 : Blo 123787 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B1628549 : Blo 123787 1628549 := bstep (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) B305353
theorem B317915 : Blo 123787 317915 := bstep (se 1 (by rfl) ⟨238436, by rfl⟩ : syracuseStep 317915 = 476873) B476873
theorem B3758669 : Blo 123787 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B186959 : Blo 123787 186959 := bstep (se 1 (by rfl) ⟨140219, by rfl⟩ : syracuseStep 186959 = 280439) B280439
theorem B285281 : Blo 123787 285281 := bstep (se 2 (by rfl) ⟨106980, by rfl⟩ : syracuseStep 285281 = 213961) B213961
theorem B187079 : Blo 123787 187079 := bstep (se 1 (by rfl) ⟨140309, by rfl⟩ : syracuseStep 187079 = 280619) B280619
theorem B187241 : Blo 123787 187241 := bstep (se 2 (by rfl) ⟨70215, by rfl⟩ : syracuseStep 187241 = 140431) B140431
theorem B187319 : Blo 123787 187319 := bstep (se 1 (by rfl) ⟨140489, by rfl⟩ : syracuseStep 187319 = 280979) B280979
theorem B285623 : Blo 123787 285623 := bstep (se 1 (by rfl) ⟨214217, by rfl⟩ : syracuseStep 285623 = 428435) B428435
theorem B187355 : Blo 123787 187355 := bstep (se 1 (by rfl) ⟨140516, by rfl⟩ : syracuseStep 187355 = 281033) B281033
theorem B1629377 : Blo 123787 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B187823 : Blo 123787 187823 := bstep (se 1 (by rfl) ⟨140867, by rfl⟩ : syracuseStep 187823 = 281735) B281735
theorem B187913 : Blo 123787 187913 := bstep (se 2 (by rfl) ⟨70467, by rfl⟩ : syracuseStep 187913 = 140935) B140935
theorem B286217 : Blo 123787 286217 := bstep (se 2 (by rfl) ⟨107331, by rfl⟩ : syracuseStep 286217 = 214663) B214663
theorem B187943 : Blo 123787 187943 := bstep (se 1 (by rfl) ⟨140957, by rfl⟩ : syracuseStep 187943 = 281915) B281915
theorem B810593 : Blo 123787 810593 := bstep (se 2 (by rfl) ⟨303972, by rfl⟩ : syracuseStep 810593 = 607945) B607945
theorem B188027 : Blo 123787 188027 := bstep (se 1 (by rfl) ⟨141020, by rfl⟩ : syracuseStep 188027 = 282041) B282041
theorem B319099 : Blo 123787 319099 := bstep (se 1 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 319099 = 478649) B478649
theorem B188153 : Blo 123787 188153 := bstep (se 2 (by rfl) ⟨70557, by rfl⟩ : syracuseStep 188153 = 141115) B141115
theorem B614137 : Blo 123787 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B941867 : Blo 123787 941867 := bstep (se 1 (by rfl) ⟨706400, by rfl⟩ : syracuseStep 941867 = 1412801) B1412801
theorem B188255 : Blo 123787 188255 := bstep (se 1 (by rfl) ⟨141191, by rfl⟩ : syracuseStep 188255 = 282383) B282383
theorem B286559 : Blo 123787 286559 := bstep (se 1 (by rfl) ⟨214919, by rfl⟩ : syracuseStep 286559 = 429839) B429839
theorem B188267 : Blo 123787 188267 := bstep (se 1 (by rfl) ⟨141200, by rfl⟩ : syracuseStep 188267 = 282401) B282401
theorem B483191 : Blo 123787 483191 := bstep (se 1 (by rfl) ⟨362393, by rfl⟩ : syracuseStep 483191 = 724787) B724787
theorem B679873 : Blo 123787 679873 := bstep (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) B509905
theorem B286739 : Blo 123787 286739 := bstep (se 1 (by rfl) ⟨215054, by rfl⟩ : syracuseStep 286739 = 430109) B430109
theorem B188495 : Blo 123787 188495 := bstep (se 1 (by rfl) ⟨141371, by rfl⟩ : syracuseStep 188495 = 282743) B282743
theorem B1597603 : Blo 123787 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B188615 : Blo 123787 188615 := bstep (se 1 (by rfl) ⟨141461, by rfl⟩ : syracuseStep 188615 = 282923) B282923
theorem B286967 : Blo 123787 286967 := bstep (se 1 (by rfl) ⟨215225, by rfl⟩ : syracuseStep 286967 = 430451) B430451
theorem B1007873 : Blo 123787 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B188777 : Blo 123787 188777 := bstep (se 2 (by rfl) ⟨70791, by rfl⟩ : syracuseStep 188777 = 141583) B141583
theorem B287081 : Blo 123787 287081 := bstep (se 2 (by rfl) ⟨107655, by rfl⟩ : syracuseStep 287081 = 215311) B215311
theorem B909701 : Blo 123787 909701 := bstep (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) B170569
theorem B188855 : Blo 123787 188855 := bstep (se 1 (by rfl) ⟨141641, by rfl⟩ : syracuseStep 188855 = 283283) B283283
theorem B188891 : Blo 123787 188891 := bstep (se 1 (by rfl) ⟨141668, by rfl⟩ : syracuseStep 188891 = 283337) B283337
theorem B418337 : Blo 123787 418337 := bstep (se 2 (by rfl) ⟨156876, by rfl⟩ : syracuseStep 418337 = 313753) B313753
theorem B418553 : Blo 123787 418553 := bstep (se 2 (by rfl) ⟨156957, by rfl⟩ : syracuseStep 418553 = 313915) B313915
theorem B484163 : Blo 123787 484163 := bstep (se 1 (by rfl) ⟨363122, by rfl⟩ : syracuseStep 484163 = 726245) B726245
theorem B910187 : Blo 123787 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B123823 : Blo 123787 123823 := bstep (se 1 (by rfl) ⟨92867, by rfl⟩ : syracuseStep 123823 = 185735) B185735
theorem B189359 : Blo 123787 189359 := bstep (se 1 (by rfl) ⟨142019, by rfl⟩ : syracuseStep 189359 = 284039) B284039
theorem B123847 : Blo 123787 123847 := bstep (se 1 (by rfl) ⟨92885, by rfl⟩ : syracuseStep 123847 = 185771) B185771
theorem B123867 : Blo 123787 123867 := bstep (se 1 (by rfl) ⟨92900, by rfl⟩ : syracuseStep 123867 = 185801) B185801
theorem B418823 : Blo 123787 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B189449 : Blo 123787 189449 := bstep (se 2 (by rfl) ⟨71043, by rfl⟩ : syracuseStep 189449 = 142087) B142087
theorem B123943 : Blo 123787 123943 := bstep (se 1 (by rfl) ⟨92957, by rfl⟩ : syracuseStep 123943 = 185915) B185915
theorem B189479 : Blo 123787 189479 := bstep (se 1 (by rfl) ⟨142109, by rfl⟩ : syracuseStep 189479 = 284219) B284219
theorem B123983 : Blo 123787 123983 := bstep (se 1 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 123983 = 185975) B185975
theorem B123999 : Blo 123787 123999 := bstep (se 1 (by rfl) ⟨92999, by rfl⟩ : syracuseStep 123999 = 185999) B185999
theorem B418931 : Blo 123787 418931 := bstep (se 1 (by rfl) ⟨314198, by rfl⟩ : syracuseStep 418931 = 628397) B628397
theorem B124027 : Blo 123787 124027 := bstep (se 1 (by rfl) ⟨93020, by rfl⟩ : syracuseStep 124027 = 186041) B186041
theorem B189563 : Blo 123787 189563 := bstep (se 1 (by rfl) ⟨142172, by rfl⟩ : syracuseStep 189563 = 284345) B284345
theorem B124079 : Blo 123787 124079 := bstep (se 1 (by rfl) ⟨93059, by rfl⟩ : syracuseStep 124079 = 186119) B186119
theorem B124103 : Blo 123787 124103 := bstep (se 1 (by rfl) ⟨93077, by rfl⟩ : syracuseStep 124103 = 186155) B186155
theorem B124123 : Blo 123787 124123 := bstep (se 1 (by rfl) ⟨93092, by rfl⟩ : syracuseStep 124123 = 186185) B186185
theorem B517367 : Blo 123787 517367 := bstep (se 1 (by rfl) ⟨388025, by rfl⟩ : syracuseStep 517367 = 776051) B776051
theorem B189689 : Blo 123787 189689 := bstep (se 2 (by rfl) ⟨71133, by rfl⟩ : syracuseStep 189689 = 142267) B142267
theorem B124199 : Blo 123787 124199 := bstep (se 1 (by rfl) ⟨93149, by rfl⟩ : syracuseStep 124199 = 186299) B186299
theorem B124239 : Blo 123787 124239 := bstep (se 1 (by rfl) ⟨93179, by rfl⟩ : syracuseStep 124239 = 186359) B186359
theorem B124255 : Blo 123787 124255 := bstep (se 1 (by rfl) ⟨93191, by rfl⟩ : syracuseStep 124255 = 186383) B186383
theorem B189791 : Blo 123787 189791 := bstep (se 1 (by rfl) ⟨142343, by rfl⟩ : syracuseStep 189791 = 284687) B284687
theorem B189803 : Blo 123787 189803 := bstep (se 1 (by rfl) ⟨142352, by rfl⟩ : syracuseStep 189803 = 284705) B284705
theorem B124283 : Blo 123787 124283 := bstep (se 1 (by rfl) ⟨93212, by rfl⟩ : syracuseStep 124283 = 186425) B186425
theorem B419201 : Blo 123787 419201 := bstep (se 2 (by rfl) ⟨157200, by rfl⟩ : syracuseStep 419201 = 314401) B314401
theorem B3302819 : Blo 123787 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B124335 : Blo 123787 124335 := bstep (se 1 (by rfl) ⟨93251, by rfl⟩ : syracuseStep 124335 = 186503) B186503
theorem B124359 : Blo 123787 124359 := bstep (se 1 (by rfl) ⟨93269, by rfl⟩ : syracuseStep 124359 = 186539) B186539
theorem B124379 : Blo 123787 124379 := bstep (se 1 (by rfl) ⟨93284, by rfl⟩ : syracuseStep 124379 = 186569) B186569
theorem B1598939 : Blo 123787 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B124455 : Blo 123787 124455 := bstep (se 1 (by rfl) ⟨93341, by rfl⟩ : syracuseStep 124455 = 186683) B186683
theorem B124495 : Blo 123787 124495 := bstep (se 1 (by rfl) ⟨93371, by rfl⟩ : syracuseStep 124495 = 186743) B186743
theorem B190031 : Blo 123787 190031 := bstep (se 1 (by rfl) ⟨142523, by rfl⟩ : syracuseStep 190031 = 285047) B285047
theorem B124511 : Blo 123787 124511 := bstep (se 1 (by rfl) ⟨93383, by rfl⟩ : syracuseStep 124511 = 186767) B186767
theorem B124539 : Blo 123787 124539 := bstep (se 1 (by rfl) ⟨93404, by rfl⟩ : syracuseStep 124539 = 186809) B186809
theorem B124591 : Blo 123787 124591 := bstep (se 1 (by rfl) ⟨93443, by rfl⟩ : syracuseStep 124591 = 186887) B186887
theorem B124615 : Blo 123787 124615 := bstep (se 1 (by rfl) ⟨93461, by rfl⟩ : syracuseStep 124615 = 186923) B186923
theorem B190151 : Blo 123787 190151 := bstep (se 1 (by rfl) ⟨142613, by rfl⟩ : syracuseStep 190151 = 285227) B285227
theorem B124635 : Blo 123787 124635 := bstep (se 1 (by rfl) ⟨93476, by rfl⟩ : syracuseStep 124635 = 186953) B186953
theorem B485149 : Blo 123787 485149 := bstep (se 3 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 485149 = 181931) B181931
theorem B124711 : Blo 123787 124711 := bstep (se 1 (by rfl) ⟨93533, by rfl⟩ : syracuseStep 124711 = 187067) B187067
theorem B124751 : Blo 123787 124751 := bstep (se 1 (by rfl) ⟨93563, by rfl⟩ : syracuseStep 124751 = 187127) B187127
theorem B124767 : Blo 123787 124767 := bstep (se 1 (by rfl) ⟨93575, by rfl⟩ : syracuseStep 124767 = 187151) B187151
theorem B190313 : Blo 123787 190313 := bstep (se 2 (by rfl) ⟨71367, by rfl⟩ : syracuseStep 190313 = 142735) B142735
theorem B124795 : Blo 123787 124795 := bstep (se 1 (by rfl) ⟨93596, by rfl⟩ : syracuseStep 124795 = 187193) B187193
theorem B124847 : Blo 123787 124847 := bstep (se 1 (by rfl) ⟨93635, by rfl⟩ : syracuseStep 124847 = 187271) B187271
theorem B190391 : Blo 123787 190391 := bstep (se 1 (by rfl) ⟨142793, by rfl⟩ : syracuseStep 190391 = 285587) B285587
theorem B124871 : Blo 123787 124871 := bstep (se 1 (by rfl) ⟨93653, by rfl⟩ : syracuseStep 124871 = 187307) B187307
theorem B124891 : Blo 123787 124891 := bstep (se 1 (by rfl) ⟨93668, by rfl⟩ : syracuseStep 124891 = 187337) B187337
theorem B190427 : Blo 123787 190427 := bstep (se 1 (by rfl) ⟨142820, by rfl⟩ : syracuseStep 190427 = 285641) B285641
theorem B124967 : Blo 123787 124967 := bstep (se 1 (by rfl) ⟨93725, by rfl⟩ : syracuseStep 124967 = 187451) B187451
theorem B125007 : Blo 123787 125007 := bstep (se 1 (by rfl) ⟨93755, by rfl⟩ : syracuseStep 125007 = 187511) B187511
theorem B125023 : Blo 123787 125023 := bstep (se 1 (by rfl) ⟨93767, by rfl⟩ : syracuseStep 125023 = 187535) B187535
theorem B125051 : Blo 123787 125051 := bstep (se 1 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 125051 = 187577) B187577
theorem B420011 : Blo 123787 420011 := bstep (se 1 (by rfl) ⟨315008, by rfl⟩ : syracuseStep 420011 = 630017) B630017
theorem B125103 : Blo 123787 125103 := bstep (se 1 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 125103 = 187655) B187655
theorem B125127 : Blo 123787 125127 := bstep (se 1 (by rfl) ⟨93845, by rfl⟩ : syracuseStep 125127 = 187691) B187691
theorem B125147 : Blo 123787 125147 := bstep (se 1 (by rfl) ⟨93860, by rfl⟩ : syracuseStep 125147 = 187721) B187721
theorem B1075457 : Blo 123787 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B125223 : Blo 123787 125223 := bstep (se 1 (by rfl) ⟨93917, by rfl⟩ : syracuseStep 125223 = 187835) B187835
theorem B125263 : Blo 123787 125263 := bstep (se 1 (by rfl) ⟨93947, by rfl⟩ : syracuseStep 125263 = 187895) B187895
theorem B125279 : Blo 123787 125279 := bstep (se 1 (by rfl) ⟨93959, by rfl⟩ : syracuseStep 125279 = 187919) B187919
theorem B125307 : Blo 123787 125307 := bstep (se 1 (by rfl) ⟨93980, by rfl⟩ : syracuseStep 125307 = 187961) B187961
theorem B3631513 : Blo 123787 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B125359 : Blo 123787 125359 := bstep (se 1 (by rfl) ⟨94019, by rfl⟩ : syracuseStep 125359 = 188039) B188039
theorem B190895 : Blo 123787 190895 := bstep (se 1 (by rfl) ⟨143171, by rfl⟩ : syracuseStep 190895 = 286343) B286343
theorem B125383 : Blo 123787 125383 := bstep (se 1 (by rfl) ⟨94037, by rfl⟩ : syracuseStep 125383 = 188075) B188075
theorem B125403 : Blo 123787 125403 := bstep (se 1 (by rfl) ⟨94052, by rfl⟩ : syracuseStep 125403 = 188105) B188105
theorem B190985 : Blo 123787 190985 := bstep (se 2 (by rfl) ⟨71619, by rfl⟩ : syracuseStep 190985 = 143239) B143239
theorem B125479 : Blo 123787 125479 := bstep (se 1 (by rfl) ⟨94109, by rfl⟩ : syracuseStep 125479 = 188219) B188219
theorem B191015 : Blo 123787 191015 := bstep (se 1 (by rfl) ⟨143261, by rfl⟩ : syracuseStep 191015 = 286523) B286523
theorem B125519 : Blo 123787 125519 := bstep (se 1 (by rfl) ⟨94139, by rfl⟩ : syracuseStep 125519 = 188279) B188279
theorem B125535 : Blo 123787 125535 := bstep (se 1 (by rfl) ⟨94151, by rfl⟩ : syracuseStep 125535 = 188303) B188303
theorem B125563 : Blo 123787 125563 := bstep (se 1 (by rfl) ⟨94172, by rfl⟩ : syracuseStep 125563 = 188345) B188345
theorem B191099 : Blo 123787 191099 := bstep (se 1 (by rfl) ⟨143324, by rfl⟩ : syracuseStep 191099 = 286649) B286649
theorem B354955 : Blo 123787 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B125615 : Blo 123787 125615 := bstep (se 1 (by rfl) ⟨94211, by rfl⟩ : syracuseStep 125615 = 188423) B188423
theorem B420551 : Blo 123787 420551 := bstep (se 1 (by rfl) ⟨315413, by rfl⟩ : syracuseStep 420551 = 630827) B630827
theorem B125639 : Blo 123787 125639 := bstep (se 1 (by rfl) ⟨94229, by rfl⟩ : syracuseStep 125639 = 188459) B188459
theorem B125659 : Blo 123787 125659 := bstep (se 1 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 125659 = 188489) B188489
theorem B486137 : Blo 123787 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B191225 : Blo 123787 191225 := bstep (se 2 (by rfl) ⟨71709, by rfl⟩ : syracuseStep 191225 = 143419) B143419
theorem B125735 : Blo 123787 125735 := bstep (se 1 (by rfl) ⟨94301, by rfl⟩ : syracuseStep 125735 = 188603) B188603
theorem B125775 : Blo 123787 125775 := bstep (se 1 (by rfl) ⟨94331, by rfl⟩ : syracuseStep 125775 = 188663) B188663
theorem B125791 : Blo 123787 125791 := bstep (se 1 (by rfl) ⟨94343, by rfl⟩ : syracuseStep 125791 = 188687) B188687
theorem B191327 : Blo 123787 191327 := bstep (se 1 (by rfl) ⟨143495, by rfl⟩ : syracuseStep 191327 = 286991) B286991
theorem B191339 : Blo 123787 191339 := bstep (se 1 (by rfl) ⟨143504, by rfl⟩ : syracuseStep 191339 = 287009) B287009
theorem B125819 : Blo 123787 125819 := bstep (se 1 (by rfl) ⟨94364, by rfl⟩ : syracuseStep 125819 = 188729) B188729
theorem B125871 : Blo 123787 125871 := bstep (se 1 (by rfl) ⟨94403, by rfl⟩ : syracuseStep 125871 = 188807) B188807
theorem B125895 : Blo 123787 125895 := bstep (se 1 (by rfl) ⟨94421, by rfl⟩ : syracuseStep 125895 = 188843) B188843
theorem B125915 : Blo 123787 125915 := bstep (se 1 (by rfl) ⟨94436, by rfl⟩ : syracuseStep 125915 = 188873) B188873
theorem B125991 : Blo 123787 125991 := bstep (se 1 (by rfl) ⟨94493, by rfl⟩ : syracuseStep 125991 = 188987) B188987
theorem B126031 : Blo 123787 126031 := bstep (se 1 (by rfl) ⟨94523, by rfl⟩ : syracuseStep 126031 = 189047) B189047
theorem B191567 : Blo 123787 191567 := bstep (se 1 (by rfl) ⟨143675, by rfl⟩ : syracuseStep 191567 = 287351) B287351
theorem B126047 : Blo 123787 126047 := bstep (se 1 (by rfl) ⟨94535, by rfl⟩ : syracuseStep 126047 = 189071) B189071
theorem B126075 : Blo 123787 126075 := bstep (se 1 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 126075 = 189113) B189113
theorem B126127 : Blo 123787 126127 := bstep (se 1 (by rfl) ⟨94595, by rfl⟩ : syracuseStep 126127 = 189191) B189191
theorem B126151 : Blo 123787 126151 := bstep (se 1 (by rfl) ⟨94613, by rfl⟩ : syracuseStep 126151 = 189227) B189227
theorem B814283 : Blo 123787 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B126171 : Blo 123787 126171 := bstep (se 1 (by rfl) ⟨94628, by rfl⟩ : syracuseStep 126171 = 189257) B189257
theorem B126247 : Blo 123787 126247 := bstep (se 1 (by rfl) ⟨94685, by rfl⟩ : syracuseStep 126247 = 189371) B189371
theorem B126287 : Blo 123787 126287 := bstep (se 1 (by rfl) ⟨94715, by rfl⟩ : syracuseStep 126287 = 189431) B189431
theorem B126303 : Blo 123787 126303 := bstep (se 1 (by rfl) ⟨94727, by rfl⟩ : syracuseStep 126303 = 189455) B189455
theorem B126331 : Blo 123787 126331 := bstep (se 1 (by rfl) ⟨94748, by rfl⟩ : syracuseStep 126331 = 189497) B189497
theorem B126383 : Blo 123787 126383 := bstep (se 1 (by rfl) ⟨94787, by rfl⟩ : syracuseStep 126383 = 189575) B189575
theorem B126407 : Blo 123787 126407 := bstep (se 1 (by rfl) ⟨94805, by rfl⟩ : syracuseStep 126407 = 189611) B189611
theorem B126427 : Blo 123787 126427 := bstep (se 1 (by rfl) ⟨94820, by rfl⟩ : syracuseStep 126427 = 189641) B189641
theorem B421415 : Blo 123787 421415 := bstep (se 1 (by rfl) ⟨316061, by rfl⟩ : syracuseStep 421415 = 632123) B632123
theorem B126503 : Blo 123787 126503 := bstep (se 1 (by rfl) ⟨94877, by rfl⟩ : syracuseStep 126503 = 189755) B189755
theorem B126543 : Blo 123787 126543 := bstep (se 1 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 126543 = 189815) B189815
theorem B126559 : Blo 123787 126559 := bstep (se 1 (by rfl) ⟨94919, by rfl⟩ : syracuseStep 126559 = 189839) B189839
theorem B126587 : Blo 123787 126587 := bstep (se 1 (by rfl) ⟨94940, by rfl⟩ : syracuseStep 126587 = 189881) B189881
theorem B421523 : Blo 123787 421523 := bstep (se 1 (by rfl) ⟨316142, by rfl⟩ : syracuseStep 421523 = 632285) B632285
theorem B126639 : Blo 123787 126639 := bstep (se 1 (by rfl) ⟨94979, by rfl⟩ : syracuseStep 126639 = 189959) B189959
theorem B126663 : Blo 123787 126663 := bstep (se 1 (by rfl) ⟨94997, by rfl⟩ : syracuseStep 126663 = 189995) B189995
theorem B126683 : Blo 123787 126683 := bstep (se 1 (by rfl) ⟨95012, by rfl⟩ : syracuseStep 126683 = 190025) B190025
theorem B126759 : Blo 123787 126759 := bstep (se 1 (by rfl) ⟨95069, by rfl⟩ : syracuseStep 126759 = 190139) B190139
theorem B126799 : Blo 123787 126799 := bstep (se 1 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 126799 = 190199) B190199
theorem B225119 : Blo 123787 225119 := bstep (se 1 (by rfl) ⟨168839, by rfl⟩ : syracuseStep 225119 = 337679) B337679
theorem B126815 : Blo 123787 126815 := bstep (se 1 (by rfl) ⟨95111, by rfl⟩ : syracuseStep 126815 = 190223) B190223
theorem B323423 : Blo 123787 323423 := bstep (se 1 (by rfl) ⟨242567, by rfl⟩ : syracuseStep 323423 = 485135) B485135
theorem B421739 : Blo 123787 421739 := bstep (se 1 (by rfl) ⟨316304, by rfl⟩ : syracuseStep 421739 = 632609) B632609
theorem B323435 : Blo 123787 323435 := bstep (se 1 (by rfl) ⟨242576, by rfl⟩ : syracuseStep 323435 = 485153) B485153
theorem B126843 : Blo 123787 126843 := bstep (se 1 (by rfl) ⟨95132, by rfl⟩ : syracuseStep 126843 = 190265) B190265
theorem B421793 : Blo 123787 421793 := bstep (se 2 (by rfl) ⟨158172, by rfl⟩ : syracuseStep 421793 = 316345) B316345
theorem B126895 : Blo 123787 126895 := bstep (se 1 (by rfl) ⟨95171, by rfl⟩ : syracuseStep 126895 = 190343) B190343
theorem B159671 : Blo 123787 159671 := bstep (se 1 (by rfl) ⟨119753, by rfl⟩ : syracuseStep 159671 = 239507) B239507
theorem B126919 : Blo 123787 126919 := bstep (se 1 (by rfl) ⟨95189, by rfl⟩ : syracuseStep 126919 = 190379) B190379
theorem B126939 : Blo 123787 126939 := bstep (se 1 (by rfl) ⟨95204, by rfl⟩ : syracuseStep 126939 = 190409) B190409
theorem B127015 : Blo 123787 127015 := bstep (se 1 (by rfl) ⟨95261, by rfl⟩ : syracuseStep 127015 = 190523) B190523
theorem B127055 : Blo 123787 127055 := bstep (se 1 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 127055 = 190583) B190583
theorem B159823 : Blo 123787 159823 := bstep (se 1 (by rfl) ⟨119867, by rfl⟩ : syracuseStep 159823 = 239735) B239735
theorem B127071 : Blo 123787 127071 := bstep (se 1 (by rfl) ⟨95303, by rfl⟩ : syracuseStep 127071 = 190607) B190607
theorem B127099 : Blo 123787 127099 := bstep (se 1 (by rfl) ⟨95324, by rfl⟩ : syracuseStep 127099 = 190649) B190649
theorem B127151 : Blo 123787 127151 := bstep (se 1 (by rfl) ⟨95363, by rfl⟩ : syracuseStep 127151 = 190727) B190727
theorem B127175 : Blo 123787 127175 := bstep (se 1 (by rfl) ⟨95381, by rfl⟩ : syracuseStep 127175 = 190763) B190763
theorem B127195 : Blo 123787 127195 := bstep (se 1 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 127195 = 190793) B190793
theorem B127271 : Blo 123787 127271 := bstep (se 1 (by rfl) ⟨95453, by rfl⟩ : syracuseStep 127271 = 190907) B190907
theorem B127311 : Blo 123787 127311 := bstep (se 1 (by rfl) ⟨95483, by rfl⟩ : syracuseStep 127311 = 190967) B190967
theorem B192863 : Blo 123787 192863 := bstep (se 1 (by rfl) ⟨144647, by rfl⟩ : syracuseStep 192863 = 289295) B289295
theorem B127327 : Blo 123787 127327 := bstep (se 1 (by rfl) ⟨95495, by rfl⟩ : syracuseStep 127327 = 190991) B190991
theorem B127355 : Blo 123787 127355 := bstep (se 1 (by rfl) ⟨95516, by rfl⟩ : syracuseStep 127355 = 191033) B191033
theorem B5534081 : Blo 123787 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B127407 : Blo 123787 127407 := bstep (se 1 (by rfl) ⟨95555, by rfl⟩ : syracuseStep 127407 = 191111) B191111
theorem B127431 : Blo 123787 127431 := bstep (se 1 (by rfl) ⟨95573, by rfl⟩ : syracuseStep 127431 = 191147) B191147
theorem B127451 : Blo 123787 127451 := bstep (se 1 (by rfl) ⟨95588, by rfl⟩ : syracuseStep 127451 = 191177) B191177
theorem B422387 : Blo 123787 422387 := bstep (se 1 (by rfl) ⟨316790, by rfl⟩ : syracuseStep 422387 = 633581) B633581
theorem B127527 : Blo 123787 127527 := bstep (se 1 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 127527 = 191291) B191291
theorem B127567 : Blo 123787 127567 := bstep (se 1 (by rfl) ⟨95675, by rfl⟩ : syracuseStep 127567 = 191351) B191351
theorem B127583 : Blo 123787 127583 := bstep (se 1 (by rfl) ⟨95687, by rfl⟩ : syracuseStep 127583 = 191375) B191375
theorem B127611 : Blo 123787 127611 := bstep (se 1 (by rfl) ⟨95708, by rfl⟩ : syracuseStep 127611 = 191417) B191417
theorem B127663 : Blo 123787 127663 := bstep (se 1 (by rfl) ⟨95747, by rfl⟩ : syracuseStep 127663 = 191495) B191495
theorem B717497 : Blo 123787 717497 := bstep (se 2 (by rfl) ⟨269061, by rfl⟩ : syracuseStep 717497 = 538123) B538123
theorem B127687 : Blo 123787 127687 := bstep (se 1 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 127687 = 191531) B191531
theorem B127707 : Blo 123787 127707 := bstep (se 1 (by rfl) ⟨95780, by rfl⟩ : syracuseStep 127707 = 191561) B191561
theorem B127783 : Blo 123787 127783 := bstep (se 1 (by rfl) ⟨95837, by rfl⟩ : syracuseStep 127783 = 191675) B191675
theorem B1635329 : Blo 123787 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B422927 : Blo 123787 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B160967 : Blo 123787 160967 := bstep (se 1 (by rfl) ⟨120725, by rfl⟩ : syracuseStep 160967 = 241451) B241451
theorem B259319 : Blo 123787 259319 := bstep (se 1 (by rfl) ⟨194489, by rfl⟩ : syracuseStep 259319 = 388979) B388979
theorem B161119 : Blo 123787 161119 := bstep (se 1 (by rfl) ⟨120839, by rfl⟩ : syracuseStep 161119 = 241679) B241679
theorem B3339667 : Blo 123787 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B947699 : Blo 123787 947699 := bstep (se 1 (by rfl) ⟨710774, by rfl⟩ : syracuseStep 947699 = 1421549) B1421549
theorem B423521 : Blo 123787 423521 := bstep (se 2 (by rfl) ⟨158820, by rfl⟩ : syracuseStep 423521 = 317641) B317641
theorem B4159127 : Blo 123787 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B456623 : Blo 123787 456623 := bstep (se 1 (by rfl) ⟨342467, by rfl⟩ : syracuseStep 456623 = 684935) B684935
theorem B522557 : Blo 123787 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B2259533 : Blo 123787 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B523115 : Blo 123787 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B228239 : Blo 123787 228239 := bstep (se 1 (by rfl) ⟨171179, by rfl⟩ : syracuseStep 228239 = 342359) B342359
theorem B359329 : Blo 123787 359329 := bstep (se 2 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 359329 = 269497) B269497
theorem B1276901 : Blo 123787 1276901 := bstep (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) B239419
theorem B424979 : Blo 123787 424979 := bstep (se 1 (by rfl) ⟨318734, by rfl⟩ : syracuseStep 424979 = 637469) B637469
theorem B425303 : Blo 123787 425303 := bstep (se 1 (by rfl) ⟨318977, by rfl⟩ : syracuseStep 425303 = 637955) B637955
theorem B7044569 : Blo 123787 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B1212043 : Blo 123787 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B753569 : Blo 123787 753569 := bstep (se 2 (by rfl) ⟨282588, by rfl⟩ : syracuseStep 753569 = 565177) B565177
theorem B1048627 : Blo 123787 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B1507481 : Blo 123787 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B2130137 : Blo 123787 2130137 := bstep (se 2 (by rfl) ⟨798801, by rfl⟩ : syracuseStep 2130137 = 1597603) B1597603
theorem B361721 : Blo 123787 361721 := bstep (se 2 (by rfl) ⟨135645, by rfl⟩ : syracuseStep 361721 = 271291) B271291
theorem B132391 : Blo 123787 132391 := bstep (se 1 (by rfl) ⟨99293, by rfl⟩ : syracuseStep 132391 = 198587) B198587
theorem B20514455 : Blo 123787 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B1476559 : Blo 123787 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B1378255 : Blo 123787 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B1280285 : Blo 123787 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B264559 : Blo 123787 264559 := bstep (se 1 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 264559 = 396839) B396839
theorem B428651 : Blo 123787 428651 := bstep (se 1 (by rfl) ⟨321488, by rfl⟩ : syracuseStep 428651 = 642977) B642977
theorem B429245 : Blo 123787 429245 := bstep (se 3 (by rfl) ⟨80483, by rfl⟩ : syracuseStep 429245 = 160967) B160967
theorem B265511 : Blo 123787 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B691517 : Blo 123787 691517 := bstep (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) B259319
theorem B5312087 : Blo 123787 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B2330477 : Blo 123787 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B1085699 : Blo 123787 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B1086251 : Blo 123787 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B1610725 : Blo 123787 1610725 := bstep (se 4 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 1610725 = 302011) B302011
theorem B398479 : Blo 123787 398479 := bstep (se 1 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 398479 = 597719) B597719
theorem B627911 : Blo 123787 627911 := bstep (se 1 (by rfl) ⟨470933, by rfl⟩ : syracuseStep 627911 = 941867) B941867
theorem B628073 : Blo 123787 628073 := bstep (se 2 (by rfl) ⟨235527, by rfl⟩ : syracuseStep 628073 = 471055) B471055
theorem B2201879 : Blo 123787 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1841591 : Blo 123787 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B236105 : Blo 123787 236105 := bstep (se 2 (by rfl) ⟨88539, by rfl⟩ : syracuseStep 236105 = 177079) B177079
theorem B400889 : Blo 123787 400889 := bstep (se 2 (by rfl) ⟨150333, by rfl⟩ : syracuseStep 400889 = 300667) B300667
theorem B532331 : Blo 123787 532331 := bstep (se 1 (by rfl) ⟨399248, by rfl⟩ : syracuseStep 532331 = 798497) B798497
theorem B270803 : Blo 123787 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B238049 : Blo 123787 238049 := bstep (se 2 (by rfl) ⟨89268, by rfl⟩ : syracuseStep 238049 = 178537) B178537
theorem B1090219 : Blo 123787 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B139999 : Blo 123787 139999 := bstep (se 1 (by rfl) ⟨104999, by rfl⟩ : syracuseStep 139999 = 209999) B209999
theorem B631799 : Blo 123787 631799 := bstep (se 1 (by rfl) ⟨473849, by rfl⟩ : syracuseStep 631799 = 947699) B947699
theorem B402529 : Blo 123787 402529 := bstep (se 2 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 402529 = 301897) B301897
theorem B140575 : Blo 123787 140575 := bstep (se 1 (by rfl) ⟨105431, by rfl⟩ : syracuseStep 140575 = 210863) B210863
theorem B304415 : Blo 123787 304415 := bstep (se 1 (by rfl) ⟨228311, by rfl⟩ : syracuseStep 304415 = 456623) B456623
theorem B337247 : Blo 123787 337247 := bstep (se 1 (by rfl) ⟨252935, by rfl⟩ : syracuseStep 337247 = 505871) B505871
theorem B238945 : Blo 123787 238945 := bstep (se 2 (by rfl) ⟨89604, by rfl⟩ : syracuseStep 238945 = 179209) B179209
theorem B534023 : Blo 123787 534023 := bstep (se 1 (by rfl) ⟨400517, by rfl⟩ : syracuseStep 534023 = 801035) B801035
theorem B534073 : Blo 123787 534073 := bstep (se 2 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 534073 = 400555) B400555
theorem B140863 : Blo 123787 140863 := bstep (se 1 (by rfl) ⟨105647, by rfl⟩ : syracuseStep 140863 = 211295) B211295
theorem B1616057 : Blo 123787 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B600317 : Blo 123787 600317 := bstep (se 3 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 600317 = 225119) B225119
theorem B4696379 : Blo 123787 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B141691 : Blo 123787 141691 := bstep (se 1 (by rfl) ⟨106268, by rfl⟩ : syracuseStep 141691 = 212537) B212537
theorem B534995 : Blo 123787 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B404041 : Blo 123787 404041 := bstep (se 2 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 404041 = 303031) B303031
theorem B502379 : Blo 123787 502379 := bstep (se 1 (by rfl) ⟨376784, by rfl⟩ : syracuseStep 502379 = 753569) B753569
theorem B240403 : Blo 123787 240403 := bstep (se 1 (by rfl) ⟨180302, by rfl⟩ : syracuseStep 240403 = 360605) B360605
theorem B142159 : Blo 123787 142159 := bstep (se 1 (by rfl) ⟨106619, by rfl⟩ : syracuseStep 142159 = 213239) B213239
theorem B338813 : Blo 123787 338813 := bstep (se 3 (by rfl) ⟨63527, by rfl⟩ : syracuseStep 338813 = 127055) B127055
theorem B633743 : Blo 123787 633743 := bstep (se 1 (by rfl) ⟨475307, by rfl⟩ : syracuseStep 633743 = 950615) B950615
theorem B306163 : Blo 123787 306163 := bstep (se 1 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 306163 = 459245) B459245
theorem B1191131 : Blo 123787 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B142555 : Blo 123787 142555 := bstep (se 1 (by rfl) ⟨106916, by rfl⟩ : syracuseStep 142555 = 213833) B213833
theorem B306395 : Blo 123787 306395 := bstep (se 1 (by rfl) ⟨229796, by rfl⟩ : syracuseStep 306395 = 459593) B459593
theorem B765245 : Blo 123787 765245 := bstep (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) B286967
theorem B2043251 : Blo 123787 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B142843 : Blo 123787 142843 := bstep (se 1 (by rfl) ⟨107132, by rfl⟩ : syracuseStep 142843 = 214265) B214265
theorem B503405 : Blo 123787 503405 := bstep (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) B188777
theorem B143023 : Blo 123787 143023 := bstep (se 1 (by rfl) ⟨107267, by rfl⟩ : syracuseStep 143023 = 214535) B214535
theorem B306875 : Blo 123787 306875 := bstep (se 1 (by rfl) ⟨230156, by rfl⟩ : syracuseStep 306875 = 460313) B460313
theorem B2272967 : Blo 123787 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B4599665 : Blo 123787 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B143311 : Blo 123787 143311 := bstep (se 1 (by rfl) ⟨107483, by rfl⟩ : syracuseStep 143311 = 214967) B214967
theorem B536635 : Blo 123787 536635 := bstep (se 1 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 536635 = 804953) B804953
theorem B274537 : Blo 123787 274537 := bstep (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) B205903
theorem B602315 : Blo 123787 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B209243 : Blo 123787 209243 := bstep (se 1 (by rfl) ⟨156932, by rfl⟩ : syracuseStep 209243 = 313865) B313865
theorem B143707 : Blo 123787 143707 := bstep (se 1 (by rfl) ⟨107780, by rfl⟩ : syracuseStep 143707 = 215561) B215561
theorem B209263 : Blo 123787 209263 := bstep (se 1 (by rfl) ⟨156947, by rfl⟩ : syracuseStep 209263 = 313895) B313895
theorem B3649967 : Blo 123787 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B209479 : Blo 123787 209479 := bstep (se 1 (by rfl) ⟨157109, by rfl⟩ : syracuseStep 209479 = 314219) B314219
theorem B635849 : Blo 123787 635849 := bstep (se 2 (by rfl) ⟨238443, by rfl⟩ : syracuseStep 635849 = 476887) B476887
theorem B472027 : Blo 123787 472027 := bstep (se 1 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 472027 = 708041) B708041
theorem B209911 : Blo 123787 209911 := bstep (se 1 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 209911 = 314867) B314867
theorem B570359 : Blo 123787 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B341279 : Blo 123787 341279 := bstep (se 1 (by rfl) ⟨255959, by rfl⟩ : syracuseStep 341279 = 511919) B511919
theorem B210215 : Blo 123787 210215 := bstep (se 1 (by rfl) ⟨157661, by rfl⟩ : syracuseStep 210215 = 315323) B315323
theorem B3225091 : Blo 123787 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B243361 : Blo 123787 243361 := bstep (se 2 (by rfl) ⟨91260, by rfl⟩ : syracuseStep 243361 = 182521) B182521
theorem B210667 : Blo 123787 210667 := bstep (se 1 (by rfl) ⟨158000, by rfl⟩ : syracuseStep 210667 = 316001) B316001
theorem B538397 : Blo 123787 538397 := bstep (se 3 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 538397 = 201899) B201899
theorem B177967 : Blo 123787 177967 := bstep (se 1 (by rfl) ⟨133475, by rfl⟩ : syracuseStep 177967 = 266951) B266951
theorem B3389303 : Blo 123787 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B473273 : Blo 123787 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B211639 : Blo 123787 211639 := bstep (se 1 (by rfl) ⟨158729, by rfl⟩ : syracuseStep 211639 = 317459) B317459
theorem B605099 : Blo 123787 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B211943 : Blo 123787 211943 := bstep (se 1 (by rfl) ⟨158957, by rfl⟩ : syracuseStep 211943 = 317915) B317915
theorem B2505779 : Blo 123787 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B5160023 : Blo 123787 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B966167 : Blo 123787 966167 := bstep (se 1 (by rfl) ⟨724625, by rfl⟩ : syracuseStep 966167 = 1449251) B1449251
theorem B572953 : Blo 123787 572953 := bstep (se 2 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 572953 = 429715) B429715
theorem B310879 : Blo 123787 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B540395 : Blo 123787 540395 := bstep (se 1 (by rfl) ⟨405296, by rfl⟩ : syracuseStep 540395 = 810593) B810593
theorem B213097 : Blo 123787 213097 := bstep (se 2 (by rfl) ⟨79911, by rfl⟩ : syracuseStep 213097 = 159823) B159823
theorem B671915 : Blo 123787 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B606467 : Blo 123787 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B11583755 : Blo 123787 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B278891 : Blo 123787 278891 := bstep (se 1 (by rfl) ⟨209168, by rfl⟩ : syracuseStep 278891 = 418337) B418337
theorem B279035 : Blo 123787 279035 := bstep (se 1 (by rfl) ⟨209276, by rfl⟩ : syracuseStep 279035 = 418553) B418553
theorem B606791 : Blo 123787 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B279161 : Blo 123787 279161 := bstep (se 2 (by rfl) ⟨104685, by rfl⟩ : syracuseStep 279161 = 209371) B209371
theorem B9290375 : Blo 123787 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B279215 : Blo 123787 279215 := bstep (se 1 (by rfl) ⟨209411, by rfl⟩ : syracuseStep 279215 = 418823) B418823
theorem B279287 : Blo 123787 279287 := bstep (se 1 (by rfl) ⟨209465, by rfl⟩ : syracuseStep 279287 = 418931) B418931
theorem B639737 : Blo 123787 639737 := bstep (se 2 (by rfl) ⟨239901, by rfl⟩ : syracuseStep 639737 = 479803) B479803
theorem B344911 : Blo 123787 344911 := bstep (se 1 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 344911 = 517367) B517367
theorem B279467 : Blo 123787 279467 := bstep (se 1 (by rfl) ⟨209600, by rfl⟩ : syracuseStep 279467 = 419201) B419201
theorem B1295297 : Blo 123787 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B1065959 : Blo 123787 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B280007 : Blo 123787 280007 := bstep (se 1 (by rfl) ⟨210005, by rfl⟩ : syracuseStep 280007 = 420011) B420011
theorem B214825 : Blo 123787 214825 := bstep (se 2 (by rfl) ⟨80559, by rfl⟩ : syracuseStep 214825 = 161119) B161119
theorem B280367 : Blo 123787 280367 := bstep (se 1 (by rfl) ⟨210275, by rfl⟩ : syracuseStep 280367 = 420551) B420551
theorem B509777 : Blo 123787 509777 := bstep (se 2 (by rfl) ⟨191166, by rfl⟩ : syracuseStep 509777 = 382333) B382333
theorem B903095 : Blo 123787 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B542855 : Blo 123787 542855 := bstep (se 1 (by rfl) ⟨407141, by rfl⟩ : syracuseStep 542855 = 814283) B814283
theorem B575623 : Blo 123787 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B280943 : Blo 123787 280943 := bstep (se 1 (by rfl) ⟨210707, by rfl⟩ : syracuseStep 280943 = 421415) B421415
theorem B281015 : Blo 123787 281015 := bstep (se 1 (by rfl) ⟨210761, by rfl⟩ : syracuseStep 281015 = 421523) B421523
theorem B215615 : Blo 123787 215615 := bstep (se 1 (by rfl) ⟨161711, by rfl⟩ : syracuseStep 215615 = 323423) B323423
theorem B281159 : Blo 123787 281159 := bstep (se 1 (by rfl) ⟨210869, by rfl⟩ : syracuseStep 281159 = 421739) B421739
theorem B215623 : Blo 123787 215623 := bstep (se 1 (by rfl) ⟨161717, by rfl⟩ : syracuseStep 215623 = 323435) B323435
theorem B281195 : Blo 123787 281195 := bstep (se 1 (by rfl) ⟨210896, by rfl⟩ : syracuseStep 281195 = 421793) B421793
theorem B314027 : Blo 123787 314027 := bstep (se 1 (by rfl) ⟨235520, by rfl⟩ : syracuseStep 314027 = 471041) B471041
theorem B3689387 : Blo 123787 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B281591 : Blo 123787 281591 := bstep (se 1 (by rfl) ⟨211193, by rfl⟩ : syracuseStep 281591 = 422387) B422387
theorem B478331 : Blo 123787 478331 := bstep (se 1 (by rfl) ⟨358748, by rfl⟩ : syracuseStep 478331 = 717497) B717497
theorem B707723 : Blo 123787 707723 := bstep (se 1 (by rfl) ⟨530792, by rfl⟩ : syracuseStep 707723 = 1061585) B1061585
theorem B314617 : Blo 123787 314617 := bstep (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) B235963
theorem B1068349 : Blo 123787 1068349 := bstep (se 3 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 1068349 = 400631) B400631
theorem B281951 : Blo 123787 281951 := bstep (se 1 (by rfl) ⟨211463, by rfl⟩ : syracuseStep 281951 = 422927) B422927
theorem B642491 : Blo 123787 642491 := bstep (se 1 (by rfl) ⟨481868, by rfl⟩ : syracuseStep 642491 = 963737) B963737
theorem B314887 : Blo 123787 314887 := bstep (se 1 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 314887 = 472331) B472331
theorem B282347 : Blo 123787 282347 := bstep (se 1 (by rfl) ⟨211760, by rfl⟩ : syracuseStep 282347 = 423521) B423521
theorem B2772751 : Blo 123787 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B315191 : Blo 123787 315191 := bstep (se 1 (by rfl) ⟨236393, by rfl⟩ : syracuseStep 315191 = 472787) B472787
theorem B282473 : Blo 123787 282473 := bstep (se 2 (by rfl) ⟨105927, by rfl⟩ : syracuseStep 282473 = 211855) B211855
theorem B479105 : Blo 123787 479105 := bstep (se 2 (by rfl) ⟨179664, by rfl⟩ : syracuseStep 479105 = 359329) B359329
theorem B544769 : Blo 123787 544769 := bstep (se 2 (by rfl) ⟨204288, by rfl⟩ : syracuseStep 544769 = 408577) B408577
theorem B348371 : Blo 123787 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B4378853 : Blo 123787 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B315859 : Blo 123787 315859 := bstep (se 1 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 315859 = 473789) B473789
theorem B348743 : Blo 123787 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B152159 : Blo 123787 152159 := bstep (se 1 (by rfl) ⟨114119, by rfl⟩ : syracuseStep 152159 = 228239) B228239
theorem B283319 : Blo 123787 283319 := bstep (se 1 (by rfl) ⟨212489, by rfl⟩ : syracuseStep 283319 = 424979) B424979
theorem B643787 : Blo 123787 643787 := bstep (se 1 (by rfl) ⟨482840, by rfl⟩ : syracuseStep 643787 = 965681) B965681
theorem B643949 : Blo 123787 643949 := bstep (se 3 (by rfl) ⟨120740, by rfl⟩ : syracuseStep 643949 = 241481) B241481
theorem B283535 : Blo 123787 283535 := bstep (se 1 (by rfl) ⟨212651, by rfl⟩ : syracuseStep 283535 = 425303) B425303
theorem B316649 : Blo 123787 316649 := bstep (se 2 (by rfl) ⟨118743, by rfl⟩ : syracuseStep 316649 = 237487) B237487
theorem B906497 : Blo 123787 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B185723 : Blo 123787 185723 := bstep (se 1 (by rfl) ⟨139292, by rfl⟩ : syracuseStep 185723 = 278585) B278585
theorem B316811 : Blo 123787 316811 := bstep (se 1 (by rfl) ⟨237608, by rfl⟩ : syracuseStep 316811 = 475217) B475217
theorem B185849 : Blo 123787 185849 := bstep (se 2 (by rfl) ⟨69693, by rfl⟩ : syracuseStep 185849 = 139387) B139387
theorem B480775 : Blo 123787 480775 := bstep (se 1 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 480775 = 721163) B721163
theorem B185951 : Blo 123787 185951 := bstep (se 1 (by rfl) ⟨139463, by rfl⟩ : syracuseStep 185951 = 278927) B278927
theorem B284255 : Blo 123787 284255 := bstep (se 1 (by rfl) ⟨213191, by rfl⟩ : syracuseStep 284255 = 426383) B426383
theorem B186167 : Blo 123787 186167 := bstep (se 1 (by rfl) ⟨139625, by rfl⟩ : syracuseStep 186167 = 279251) B279251
theorem B284471 : Blo 123787 284471 := bstep (se 1 (by rfl) ⟨213353, by rfl⟩ : syracuseStep 284471 = 426707) B426707
theorem B481079 : Blo 123787 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B481261 : Blo 123787 481261 := bstep (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) B180473
theorem B186473 : Blo 123787 186473 := bstep (se 2 (by rfl) ⟨69927, by rfl⟩ : syracuseStep 186473 = 139855) B139855
theorem B284777 : Blo 123787 284777 := bstep (se 2 (by rfl) ⟨106791, by rfl⟩ : syracuseStep 284777 = 213583) B213583
theorem B612481 : Blo 123787 612481 := bstep (se 2 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 612481 = 459361) B459361
theorem B481565 : Blo 123787 481565 := bstep (se 3 (by rfl) ⟨90293, by rfl⟩ : syracuseStep 481565 = 180587) B180587
theorem B317803 : Blo 123787 317803 := bstep (se 1 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 317803 = 476705) B476705
theorem B186791 : Blo 123787 186791 := bstep (se 1 (by rfl) ⟨140093, by rfl⟩ : syracuseStep 186791 = 280187) B280187
theorem B481747 : Blo 123787 481747 := bstep (se 1 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 481747 = 722621) B722621
theorem B186875 : Blo 123787 186875 := bstep (se 1 (by rfl) ⟨140156, by rfl⟩ : syracuseStep 186875 = 280313) B280313
theorem B1595963 : Blo 123787 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B285263 : Blo 123787 285263 := bstep (se 1 (by rfl) ⟨213947, by rfl⟩ : syracuseStep 285263 = 427895) B427895
theorem B187001 : Blo 123787 187001 := bstep (se 2 (by rfl) ⟨70125, by rfl⟩ : syracuseStep 187001 = 140251) B140251
theorem B187055 : Blo 123787 187055 := bstep (se 1 (by rfl) ⟨140291, by rfl⟩ : syracuseStep 187055 = 280583) B280583
theorem B318127 : Blo 123787 318127 := bstep (se 1 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 318127 = 477191) B477191
theorem B187103 : Blo 123787 187103 := bstep (se 1 (by rfl) ⟨140327, by rfl⟩ : syracuseStep 187103 = 280655) B280655
theorem B285407 : Blo 123787 285407 := bstep (se 1 (by rfl) ⟨214055, by rfl⟩ : syracuseStep 285407 = 428111) B428111
theorem B482219 : Blo 123787 482219 := bstep (se 1 (by rfl) ⟨361664, by rfl⟩ : syracuseStep 482219 = 723329) B723329
theorem B285659 : Blo 123787 285659 := bstep (se 1 (by rfl) ⟨214244, by rfl⟩ : syracuseStep 285659 = 428489) B428489
theorem B187367 : Blo 123787 187367 := bstep (se 1 (by rfl) ⟨140525, by rfl⟩ : syracuseStep 187367 = 281051) B281051
theorem B318451 : Blo 123787 318451 := bstep (se 1 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 318451 = 477677) B477677
theorem B285839 : Blo 123787 285839 := bstep (se 1 (by rfl) ⟨214379, by rfl⟩ : syracuseStep 285839 = 428759) B428759
theorem B187625 : Blo 123787 187625 := bstep (se 2 (by rfl) ⟨70359, by rfl⟩ : syracuseStep 187625 = 140719) B140719
theorem B285929 : Blo 123787 285929 := bstep (se 2 (by rfl) ⟨107223, by rfl⟩ : syracuseStep 285929 = 214447) B214447
theorem B187679 : Blo 123787 187679 := bstep (se 1 (by rfl) ⟨140759, by rfl⟩ : syracuseStep 187679 = 281519) B281519
theorem B285983 : Blo 123787 285983 := bstep (se 1 (by rfl) ⟨214487, by rfl⟩ : syracuseStep 285983 = 428975) B428975
theorem B187847 : Blo 123787 187847 := bstep (se 1 (by rfl) ⟨140885, by rfl⟩ : syracuseStep 187847 = 281771) B281771
theorem B1007063 : Blo 123787 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B1072723 : Blo 123787 1072723 := bstep (se 1 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 1072723 = 1609085) B1609085
theorem B646865 : Blo 123787 646865 := bstep (se 2 (by rfl) ⟨242574, by rfl⟩ : syracuseStep 646865 = 485149) B485149
theorem B319211 : Blo 123787 319211 := bstep (se 1 (by rfl) ⟨239408, by rfl⟩ : syracuseStep 319211 = 478817) B478817
theorem B188201 : Blo 123787 188201 := bstep (se 2 (by rfl) ⟨70575, by rfl⟩ : syracuseStep 188201 = 141151) B141151
theorem B286505 : Blo 123787 286505 := bstep (se 2 (by rfl) ⟨107439, by rfl⟩ : syracuseStep 286505 = 214879) B214879
theorem B188207 : Blo 123787 188207 := bstep (se 1 (by rfl) ⟨141155, by rfl⟩ : syracuseStep 188207 = 282311) B282311
theorem B548669 : Blo 123787 548669 := bstep (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) B205751
theorem B417851 : Blo 123787 417851 := bstep (se 1 (by rfl) ⟨313388, by rfl⟩ : syracuseStep 417851 = 626777) B626777
theorem B680089 : Blo 123787 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B188681 : Blo 123787 188681 := bstep (se 2 (by rfl) ⟨70755, by rfl⟩ : syracuseStep 188681 = 141511) B141511
theorem B418121 : Blo 123787 418121 := bstep (se 2 (by rfl) ⟨156795, by rfl⟩ : syracuseStep 418121 = 313591) B313591
theorem B483691 : Blo 123787 483691 := bstep (se 1 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 483691 = 725537) B725537
theorem B188783 : Blo 123787 188783 := bstep (se 1 (by rfl) ⟨141587, by rfl⟩ : syracuseStep 188783 = 283175) B283175
theorem B319955 : Blo 123787 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B4842017 : Blo 123787 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B188999 : Blo 123787 188999 := bstep (se 1 (by rfl) ⟨141749, by rfl⟩ : syracuseStep 188999 = 283499) B283499
theorem B320071 : Blo 123787 320071 := bstep (se 1 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 320071 = 480107) B480107
theorem B189035 : Blo 123787 189035 := bstep (se 1 (by rfl) ⟨141776, by rfl⟩ : syracuseStep 189035 = 283553) B283553
theorem B320183 : Blo 123787 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B189263 : Blo 123787 189263 := bstep (se 1 (by rfl) ⟨141947, by rfl⟩ : syracuseStep 189263 = 283895) B283895
theorem B123803 : Blo 123787 123803 := bstep (se 1 (by rfl) ⟨92852, by rfl⟩ : syracuseStep 123803 = 185705) B185705
theorem B123855 : Blo 123787 123855 := bstep (se 1 (by rfl) ⟨92891, by rfl⟩ : syracuseStep 123855 = 185783) B185783
theorem B123879 : Blo 123787 123879 := bstep (se 1 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 123879 = 185819) B185819
theorem B2450533 : Blo 123787 2450533 := bstep (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) B459475
theorem B189659 : Blo 123787 189659 := bstep (se 1 (by rfl) ⟨142244, by rfl⟩ : syracuseStep 189659 = 284489) B284489
theorem B124191 : Blo 123787 124191 := bstep (se 1 (by rfl) ⟨93143, by rfl⟩ : syracuseStep 124191 = 186287) B186287
theorem B124251 : Blo 123787 124251 := bstep (se 1 (by rfl) ⟨93188, by rfl⟩ : syracuseStep 124251 = 186377) B186377
theorem B124271 : Blo 123787 124271 := bstep (se 1 (by rfl) ⟨93203, by rfl⟩ : syracuseStep 124271 = 186407) B186407
theorem B189833 : Blo 123787 189833 := bstep (se 2 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 189833 = 142375) B142375
theorem B124327 : Blo 123787 124327 := bstep (se 1 (by rfl) ⟨93245, by rfl⟩ : syracuseStep 124327 = 186491) B186491
theorem B124411 : Blo 123787 124411 := bstep (se 1 (by rfl) ⟨93308, by rfl⟩ : syracuseStep 124411 = 186617) B186617
theorem B124479 : Blo 123787 124479 := bstep (se 1 (by rfl) ⟨93359, by rfl⟩ : syracuseStep 124479 = 186719) B186719
theorem B124487 : Blo 123787 124487 := bstep (se 1 (by rfl) ⟨93365, by rfl⟩ : syracuseStep 124487 = 186731) B186731
theorem B714329 : Blo 123787 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B321185 : Blo 123787 321185 := bstep (se 2 (by rfl) ⟨120444, by rfl⟩ : syracuseStep 321185 = 240889) B240889
theorem B124639 : Blo 123787 124639 := bstep (se 1 (by rfl) ⟨93479, by rfl⟩ : syracuseStep 124639 = 186959) B186959
theorem B190187 : Blo 123787 190187 := bstep (se 1 (by rfl) ⟨142640, by rfl⟩ : syracuseStep 190187 = 285281) B285281
theorem B124719 : Blo 123787 124719 := bstep (se 1 (by rfl) ⟨93539, by rfl⟩ : syracuseStep 124719 = 187079) B187079
theorem B124827 : Blo 123787 124827 := bstep (se 1 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 124827 = 187241) B187241
theorem B124879 : Blo 123787 124879 := bstep (se 1 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 124879 = 187319) B187319
theorem B190415 : Blo 123787 190415 := bstep (se 1 (by rfl) ⟨142811, by rfl⟩ : syracuseStep 190415 = 285623) B285623
theorem B124903 : Blo 123787 124903 := bstep (se 1 (by rfl) ⟨93677, by rfl⟩ : syracuseStep 124903 = 187355) B187355
theorem B321641 : Blo 123787 321641 := bstep (se 2 (by rfl) ⟨120615, by rfl⟩ : syracuseStep 321641 = 241231) B241231
theorem B354557 : Blo 123787 354557 := bstep (se 3 (by rfl) ⟨66479, by rfl⟩ : syracuseStep 354557 = 132959) B132959
theorem B125215 : Blo 123787 125215 := bstep (se 1 (by rfl) ⟨93911, by rfl⟩ : syracuseStep 125215 = 187823) B187823
theorem B1370429 : Blo 123787 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B125275 : Blo 123787 125275 := bstep (se 1 (by rfl) ⟨93956, by rfl⟩ : syracuseStep 125275 = 187913) B187913
theorem B190811 : Blo 123787 190811 := bstep (se 1 (by rfl) ⟨143108, by rfl⟩ : syracuseStep 190811 = 286217) B286217
theorem B125295 : Blo 123787 125295 := bstep (se 1 (by rfl) ⟨93971, by rfl⟩ : syracuseStep 125295 = 187943) B187943
theorem B125351 : Blo 123787 125351 := bstep (se 1 (by rfl) ⟨94013, by rfl⟩ : syracuseStep 125351 = 188027) B188027
theorem B158203 : Blo 123787 158203 := bstep (se 1 (by rfl) ⟨118652, by rfl⟩ : syracuseStep 158203 = 237305) B237305
theorem B125435 : Blo 123787 125435 := bstep (se 1 (by rfl) ⟨94076, by rfl⟩ : syracuseStep 125435 = 188153) B188153
theorem B125503 : Blo 123787 125503 := bstep (se 1 (by rfl) ⟨94127, by rfl⟩ : syracuseStep 125503 = 188255) B188255
theorem B191039 : Blo 123787 191039 := bstep (se 1 (by rfl) ⟨143279, by rfl⟩ : syracuseStep 191039 = 286559) B286559
theorem B125511 : Blo 123787 125511 := bstep (se 1 (by rfl) ⟨94133, by rfl⟩ : syracuseStep 125511 = 188267) B188267
theorem B322127 : Blo 123787 322127 := bstep (se 1 (by rfl) ⟨241595, by rfl⟩ : syracuseStep 322127 = 483191) B483191
theorem B1075799 : Blo 123787 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B191159 : Blo 123787 191159 := bstep (se 1 (by rfl) ⟨143369, by rfl⟩ : syracuseStep 191159 = 286739) B286739
theorem B158431 : Blo 123787 158431 := bstep (se 1 (by rfl) ⟨118823, by rfl⟩ : syracuseStep 158431 = 237647) B237647
theorem B125663 : Blo 123787 125663 := bstep (se 1 (by rfl) ⟨94247, by rfl⟩ : syracuseStep 125663 = 188495) B188495
theorem B125743 : Blo 123787 125743 := bstep (se 1 (by rfl) ⟨94307, by rfl⟩ : syracuseStep 125743 = 188615) B188615
theorem B387965 : Blo 123787 387965 := bstep (se 3 (by rfl) ⟨72743, by rfl⟩ : syracuseStep 387965 = 145487) B145487
theorem B125851 : Blo 123787 125851 := bstep (se 1 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 125851 = 188777) B188777
theorem B191387 : Blo 123787 191387 := bstep (se 1 (by rfl) ⟨143540, by rfl⟩ : syracuseStep 191387 = 287081) B287081
theorem B125903 : Blo 123787 125903 := bstep (se 1 (by rfl) ⟨94427, by rfl⟩ : syracuseStep 125903 = 188855) B188855
theorem B125927 : Blo 123787 125927 := bstep (se 1 (by rfl) ⟨94445, by rfl⟩ : syracuseStep 125927 = 188891) B188891
theorem B322775 : Blo 123787 322775 := bstep (se 1 (by rfl) ⟨242081, by rfl⟩ : syracuseStep 322775 = 484163) B484163
theorem B126239 : Blo 123787 126239 := bstep (se 1 (by rfl) ⟨94679, by rfl⟩ : syracuseStep 126239 = 189359) B189359
theorem B126299 : Blo 123787 126299 := bstep (se 1 (by rfl) ⟨94724, by rfl⟩ : syracuseStep 126299 = 189449) B189449
theorem B126319 : Blo 123787 126319 := bstep (se 1 (by rfl) ⟨94739, by rfl⟩ : syracuseStep 126319 = 189479) B189479
theorem B224635 : Blo 123787 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B290171 : Blo 123787 290171 := bstep (se 1 (by rfl) ⟨217628, by rfl⟩ : syracuseStep 290171 = 435257) B435257
theorem B126375 : Blo 123787 126375 := bstep (se 1 (by rfl) ⟨94781, by rfl⟩ : syracuseStep 126375 = 189563) B189563
theorem B421307 : Blo 123787 421307 := bstep (se 1 (by rfl) ⟨315980, by rfl⟩ : syracuseStep 421307 = 631961) B631961
theorem B159175 : Blo 123787 159175 := bstep (se 1 (by rfl) ⟨119381, by rfl⟩ : syracuseStep 159175 = 238763) B238763
theorem B126459 : Blo 123787 126459 := bstep (se 1 (by rfl) ⟨94844, by rfl⟩ : syracuseStep 126459 = 189689) B189689
theorem B1207817 : Blo 123787 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B323129 : Blo 123787 323129 := bstep (se 2 (by rfl) ⟨121173, by rfl⟩ : syracuseStep 323129 = 242347) B242347
theorem B126527 : Blo 123787 126527 := bstep (se 1 (by rfl) ⟨94895, by rfl⟩ : syracuseStep 126527 = 189791) B189791
theorem B126535 : Blo 123787 126535 := bstep (se 1 (by rfl) ⟨94901, by rfl⟩ : syracuseStep 126535 = 189803) B189803
theorem B126687 : Blo 123787 126687 := bstep (se 1 (by rfl) ⟨95015, by rfl⟩ : syracuseStep 126687 = 190031) B190031
theorem B126767 : Blo 123787 126767 := bstep (se 1 (by rfl) ⟨95075, by rfl⟩ : syracuseStep 126767 = 190151) B190151
theorem B126875 : Blo 123787 126875 := bstep (se 1 (by rfl) ⟨95156, by rfl⟩ : syracuseStep 126875 = 190313) B190313
theorem B126927 : Blo 123787 126927 := bstep (se 1 (by rfl) ⟨95195, by rfl⟩ : syracuseStep 126927 = 190391) B190391
theorem B126951 : Blo 123787 126951 := bstep (se 1 (by rfl) ⟨95213, by rfl⟩ : syracuseStep 126951 = 190427) B190427
theorem B716971 : Blo 123787 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B6025421 : Blo 123787 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B127263 : Blo 123787 127263 := bstep (se 1 (by rfl) ⟨95447, by rfl⟩ : syracuseStep 127263 = 190895) B190895
theorem B127323 : Blo 123787 127323 := bstep (se 1 (by rfl) ⟨95492, by rfl⟩ : syracuseStep 127323 = 190985) B190985
theorem B127343 : Blo 123787 127343 := bstep (se 1 (by rfl) ⟨95507, by rfl⟩ : syracuseStep 127343 = 191015) B191015
theorem B127399 : Blo 123787 127399 := bstep (se 1 (by rfl) ⟨95549, by rfl⟩ : syracuseStep 127399 = 191099) B191099
theorem B324091 : Blo 123787 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B127483 : Blo 123787 127483 := bstep (se 1 (by rfl) ⟨95612, by rfl⟩ : syracuseStep 127483 = 191225) B191225
theorem B4452889 : Blo 123787 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B160319 : Blo 123787 160319 := bstep (se 1 (by rfl) ⟨120239, by rfl⟩ : syracuseStep 160319 = 240479) B240479
theorem B127551 : Blo 123787 127551 := bstep (se 1 (by rfl) ⟨95663, by rfl⟩ : syracuseStep 127551 = 191327) B191327
theorem B127559 : Blo 123787 127559 := bstep (se 1 (by rfl) ⟨95669, by rfl⟩ : syracuseStep 127559 = 191339) B191339
theorem B127711 : Blo 123787 127711 := bstep (se 1 (by rfl) ⟨95783, by rfl⟩ : syracuseStep 127711 = 191567) B191567
theorem B357473 : Blo 123787 357473 := bstep (se 2 (by rfl) ⟨134052, by rfl⟩ : syracuseStep 357473 = 268105) B268105
theorem B128575 : Blo 123787 128575 := bstep (se 1 (by rfl) ⟨96431, by rfl⟩ : syracuseStep 128575 = 192863) B192863
theorem B456349 : Blo 123787 456349 := bstep (se 3 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 456349 = 171131) B171131
theorem B161615 : Blo 123787 161615 := bstep (se 1 (by rfl) ⟨121211, by rfl⟩ : syracuseStep 161615 = 242423) B242423
theorem B1079831 : Blo 123787 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B686839 : Blo 123787 686839 := bstep (se 1 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 686839 = 1030259) B1030259
theorem B818075 : Blo 123787 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B851267 : Blo 123787 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B425465 : Blo 123787 425465 := bstep (se 2 (by rfl) ⟨159549, by rfl⟩ : syracuseStep 425465 = 319099) B319099
theorem B818849 : Blo 123787 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B425735 : Blo 123787 425735 := bstep (se 1 (by rfl) ⟨319301, by rfl⟩ : syracuseStep 425735 = 638603) B638603
theorem B425789 : Blo 123787 425789 := bstep (se 3 (by rfl) ⟨79835, by rfl⟩ : syracuseStep 425789 = 159671) B159671
theorem B6193583 : Blo 123787 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B426491 : Blo 123787 426491 := bstep (se 1 (by rfl) ⟨319868, by rfl⟩ : syracuseStep 426491 = 639737) B639737
theorem B426761 : Blo 123787 426761 := bstep (se 2 (by rfl) ⟨160035, by rfl⟩ : syracuseStep 426761 = 320071) B320071
theorem B459881 : Blo 123787 459881 := bstep (se 2 (by rfl) ⟨172455, by rfl⟩ : syracuseStep 459881 = 344911) B344911
theorem B853213 : Blo 123787 853213 := bstep (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) B319955
theorem B361903 : Blo 123787 361903 := bstep (se 1 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 361903 = 542855) B542855
theorem B427517 : Blo 123787 427517 := bstep (se 3 (by rfl) ⟨80159, by rfl⟩ : syracuseStep 427517 = 160319) B160319
theorem B853523 : Blo 123787 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B2459591 : Blo 123787 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B428327 : Blo 123787 428327 := bstep (se 1 (by rfl) ⟨321245, by rfl⟩ : syracuseStep 428327 = 642491) B642491
theorem B3541391 : Blo 123787 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B1968745 : Blo 123787 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B1837673 : Blo 123787 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B363179 : Blo 123787 363179 := bstep (se 1 (by rfl) ⟨272384, by rfl⟩ : syracuseStep 363179 = 544769) B544769
theorem B232247 : Blo 123787 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B2919235 : Blo 123787 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B723799 : Blo 123787 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B429191 : Blo 123787 429191 := bstep (se 1 (by rfl) ⟨321893, by rfl⟩ : syracuseStep 429191 = 643787) B643787
theorem B429299 : Blo 123787 429299 := bstep (se 1 (by rfl) ⟨321974, by rfl⟩ : syracuseStep 429299 = 643949) B643949
theorem B299513 : Blo 123787 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B430973 : Blo 123787 430973 := bstep (se 3 (by rfl) ⟨80807, by rfl⟩ : syracuseStep 430973 = 161615) B161615
theorem B267259 : Blo 123787 267259 := bstep (se 1 (by rfl) ⟨200444, by rfl⟩ : syracuseStep 267259 = 400889) B400889
theorem B431243 : Blo 123787 431243 := bstep (se 1 (by rfl) ⟨323432, by rfl⟩ : syracuseStep 431243 = 646865) B646865
theorem B365779 : Blo 123787 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B366049 : Blo 123787 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B955961 : Blo 123787 955961 := bstep (se 2 (by rfl) ⟨358485, by rfl⟩ : syracuseStep 955961 = 716971) B716971
theorem B432121 : Blo 123787 432121 := bstep (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) B324091
theorem B5937185 : Blo 123787 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B202943 : Blo 123787 202943 := bstep (se 1 (by rfl) ⟨152207, by rfl⟩ : syracuseStep 202943 = 304415) B304415
theorem B629369 : Blo 123787 629369 := bstep (se 2 (by rfl) ⟨236013, by rfl⟩ : syracuseStep 629369 = 472027) B472027
theorem B236371 : Blo 123787 236371 := bstep (se 1 (by rfl) ⟨177278, by rfl⟩ : syracuseStep 236371 = 354557) B354557
theorem B400211 : Blo 123787 400211 := bstep (se 1 (by rfl) ⟨300158, by rfl⟩ : syracuseStep 400211 = 600317) B600317
theorem B531305 : Blo 123787 531305 := bstep (se 2 (by rfl) ⟨199239, by rfl⟩ : syracuseStep 531305 = 398479) B398479
theorem B334919 : Blo 123787 334919 := bstep (se 1 (by rfl) ⟨251189, by rfl⟩ : syracuseStep 334919 = 502379) B502379
theorem B4300121 : Blo 123787 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B171433 : Blo 123787 171433 := bstep (se 2 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 171433 = 128575) B128575
theorem B794087 : Blo 123787 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B204263 : Blo 123787 204263 := bstep (se 1 (by rfl) ⟨153197, by rfl⟩ : syracuseStep 204263 = 306395) B306395
theorem B335603 : Blo 123787 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B1515311 : Blo 123787 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B401543 : Blo 123787 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B139495 : Blo 123787 139495 := bstep (se 1 (by rfl) ⟨104621, by rfl⟩ : syracuseStep 139495 = 209243) B209243
theorem B2433311 : Blo 123787 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B238315 : Blo 123787 238315 := bstep (se 1 (by rfl) ⟨178736, by rfl⟩ : syracuseStep 238315 = 357473) B357473
theorem B2040653 : Blo 123787 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B1844045 : Blo 123787 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B2270045 : Blo 123787 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B140143 : Blo 123787 140143 := bstep (se 1 (by rfl) ⟨105107, by rfl⟩ : syracuseStep 140143 = 210215) B210215
theorem B403399 : Blo 123787 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B141295 : Blo 123787 141295 := bstep (se 1 (by rfl) ⟨105971, by rfl⟩ : syracuseStep 141295 = 211943) B211943
theorem B763937 : Blo 123787 763937 := bstep (se 2 (by rfl) ⟨286476, by rfl⟩ : syracuseStep 763937 = 572953) B572953
theorem B1420091 : Blo 123787 1420091 := bstep (se 1 (by rfl) ⟨1065068, by rfl⟩ : syracuseStep 1420091 = 2130137) B2130137
theorem B404311 : Blo 123787 404311 := bstep (se 1 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 404311 = 606467) B606467
theorem B404527 : Blo 123787 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B863531 : Blo 123787 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B241147 : Blo 123787 241147 := bstep (se 1 (by rfl) ⟨180860, by rfl⟩ : syracuseStep 241147 = 361721) B361721
theorem B1453625 : Blo 123787 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B13676303 : Blo 123787 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B339851 : Blo 123787 339851 := bstep (se 1 (by rfl) ⟨254888, by rfl⟩ : syracuseStep 339851 = 509777) B509777
theorem B602063 : Blo 123787 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B536705 : Blo 123787 536705 := bstep (se 2 (by rfl) ⟨201264, by rfl⟩ : syracuseStep 536705 = 402529) B402529
theorem B929981 : Blo 123787 929981 := bstep (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) B348743
theorem B405757 : Blo 123787 405757 := bstep (se 3 (by rfl) ⟨76079, by rfl⟩ : syracuseStep 405757 = 152159) B152159
theorem B143743 : Blo 123787 143743 := bstep (se 1 (by rfl) ⟨107807, by rfl⟩ : syracuseStep 143743 = 215615) B215615
theorem B176521 : Blo 123787 176521 := bstep (se 2 (by rfl) ⟨66195, by rfl⟩ : syracuseStep 176521 = 132391) B132391
theorem B209351 : Blo 123787 209351 := bstep (se 1 (by rfl) ⟨157013, by rfl⟩ : syracuseStep 209351 = 314027) B314027
theorem B471815 : Blo 123787 471815 := bstep (se 1 (by rfl) ⟨353861, by rfl⟩ : syracuseStep 471815 = 707723) B707723
theorem B2896669 : Blo 123787 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B177007 : Blo 123787 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B210127 : Blo 123787 210127 := bstep (se 1 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 210127 = 315191) B315191
theorem B1553651 : Blo 123787 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1520957 : Blo 123787 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B767497 : Blo 123787 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B210937 : Blo 123787 210937 := bstep (se 2 (by rfl) ⟨79101, by rfl⟩ : syracuseStep 210937 = 158203) B158203
theorem B538721 : Blo 123787 538721 := bstep (se 2 (by rfl) ⟨202020, by rfl⟩ : syracuseStep 538721 = 404041) B404041
theorem B211099 : Blo 123787 211099 := bstep (se 1 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 211099 = 316649) B316649
theorem B604331 : Blo 123787 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B211207 : Blo 123787 211207 := bstep (se 1 (by rfl) ⟨158405, by rfl⟩ : syracuseStep 211207 = 316811) B316811
theorem B211241 : Blo 123787 211241 := bstep (se 2 (by rfl) ⟨79215, by rfl⟩ : syracuseStep 211241 = 158431) B158431
theorem B1227727 : Blo 123787 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B1063975 : Blo 123787 1063975 := bstep (se 1 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 1063975 = 1595963) B1595963
theorem B1424465 : Blo 123787 1424465 := bstep (se 2 (by rfl) ⟨534174, by rfl⟩ : syracuseStep 1424465 = 1068349) B1068349
theorem B212233 : Blo 123787 212233 := bstep (se 2 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 212233 = 159175) B159175
theorem B671375 : Blo 123787 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B212807 : Blo 123787 212807 := bstep (se 1 (by rfl) ⟨159605, by rfl⟩ : syracuseStep 212807 = 319211) B319211
theorem B278567 : Blo 123787 278567 := bstep (se 1 (by rfl) ⟨208925, by rfl⟩ : syracuseStep 278567 = 417851) B417851
theorem B278747 : Blo 123787 278747 := bstep (se 1 (by rfl) ⟨209060, by rfl⟩ : syracuseStep 278747 = 418121) B418121
theorem B180535 : Blo 123787 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B3228011 : Blo 123787 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B213455 : Blo 123787 213455 := bstep (se 1 (by rfl) ⟨160091, by rfl⟩ : syracuseStep 213455 = 320183) B320183
theorem B279017 : Blo 123787 279017 := bstep (se 2 (by rfl) ⟨104631, by rfl⟩ : syracuseStep 279017 = 209263) B209263
theorem B279305 : Blo 123787 279305 := bstep (se 2 (by rfl) ⟨104739, by rfl⟩ : syracuseStep 279305 = 209479) B209479
theorem B476219 : Blo 123787 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B214123 : Blo 123787 214123 := bstep (se 1 (by rfl) ⟨160592, by rfl⟩ : syracuseStep 214123 = 321185) B321185
theorem B2147633 : Blo 123787 2147633 := bstep (se 2 (by rfl) ⟨805362, by rfl⟩ : syracuseStep 2147633 = 1610725) B1610725
theorem B279881 : Blo 123787 279881 := bstep (se 2 (by rfl) ⟨104955, by rfl⟩ : syracuseStep 279881 = 209911) B209911
theorem B214427 : Blo 123787 214427 := bstep (se 1 (by rfl) ⟨160820, by rfl⟩ : syracuseStep 214427 = 321641) B321641
theorem B3130919 : Blo 123787 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B2868797 : Blo 123787 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B214751 : Blo 123787 214751 := bstep (se 1 (by rfl) ⟨161063, by rfl⟩ : syracuseStep 214751 = 322127) B322127
theorem B641033 : Blo 123787 641033 := bstep (se 2 (by rfl) ⟨240387, by rfl⟩ : syracuseStep 641033 = 480775) B480775
theorem B215183 : Blo 123787 215183 := bstep (se 1 (by rfl) ⟨161387, by rfl⟩ : syracuseStep 215183 = 322775) B322775
theorem B608465 : Blo 123787 608465 := bstep (se 2 (by rfl) ⟨228174, by rfl⟩ : syracuseStep 608465 = 456349) B456349
theorem B1362167 : Blo 123787 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B280871 : Blo 123787 280871 := bstep (se 1 (by rfl) ⟨210653, by rfl⟩ : syracuseStep 280871 = 421307) B421307
theorem B280889 : Blo 123787 280889 := bstep (se 2 (by rfl) ⟨105333, by rfl⟩ : syracuseStep 280889 = 210667) B210667
theorem B805211 : Blo 123787 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B215419 : Blo 123787 215419 := bstep (se 1 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 215419 = 323129) B323129
theorem B3066443 : Blo 123787 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B641681 : Blo 123787 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B4016947 : Blo 123787 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B642329 : Blo 123787 642329 := bstep (se 2 (by rfl) ⟨240873, by rfl⟩ : syracuseStep 642329 = 481747) B481747
theorem B282185 : Blo 123787 282185 := bstep (se 2 (by rfl) ⟨105819, by rfl⟩ : syracuseStep 282185 = 211639) B211639
theorem B315515 : Blo 123787 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B2183597 : Blo 123787 2183597 := bstep (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) B818849
theorem B545383 : Blo 123787 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B1430297 : Blo 123787 1430297 := bstep (se 2 (by rfl) ⟨536361, by rfl⟩ : syracuseStep 1430297 = 1072723) B1072723
theorem B414505 : Blo 123787 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B283643 : Blo 123787 283643 := bstep (se 1 (by rfl) ⟨212732, by rfl⟩ : syracuseStep 283643 = 425465) B425465
theorem B644111 : Blo 123787 644111 := bstep (se 1 (by rfl) ⟨483083, by rfl⟩ : syracuseStep 644111 = 966167) B966167
theorem B283823 : Blo 123787 283823 := bstep (se 1 (by rfl) ⟨212867, by rfl⟩ : syracuseStep 283823 = 425735) B425735
theorem B283859 : Blo 123787 283859 := bstep (se 1 (by rfl) ⟨212894, by rfl⟩ : syracuseStep 283859 = 425789) B425789
theorem B1398169 : Blo 123787 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B1004987 : Blo 123787 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B447943 : Blo 123787 447943 := bstep (se 1 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 447943 = 671915) B671915
theorem B284129 : Blo 123787 284129 := bstep (se 2 (by rfl) ⟨106548, by rfl⟩ : syracuseStep 284129 = 213097) B213097
theorem B7722503 : Blo 123787 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B906785 : Blo 123787 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B185927 : Blo 123787 185927 := bstep (se 1 (by rfl) ⟨139445, by rfl⟩ : syracuseStep 185927 = 278891) B278891
theorem B186023 : Blo 123787 186023 := bstep (se 1 (by rfl) ⟨139517, by rfl⟩ : syracuseStep 186023 = 279035) B279035
theorem B186107 : Blo 123787 186107 := bstep (se 1 (by rfl) ⟨139580, by rfl⟩ : syracuseStep 186107 = 279161) B279161
theorem B186143 : Blo 123787 186143 := bstep (se 1 (by rfl) ⟨139607, by rfl⟩ : syracuseStep 186143 = 279215) B279215
theorem B644921 : Blo 123787 644921 := bstep (se 2 (by rfl) ⟨241845, by rfl⟩ : syracuseStep 644921 = 483691) B483691
theorem B186191 : Blo 123787 186191 := bstep (se 1 (by rfl) ⟨139643, by rfl⟩ : syracuseStep 186191 = 279287) B279287
theorem B186311 : Blo 123787 186311 := bstep (se 1 (by rfl) ⟨139733, by rfl⟩ : syracuseStep 186311 = 279467) B279467
theorem B710639 : Blo 123787 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B186665 : Blo 123787 186665 := bstep (se 2 (by rfl) ⟨69999, by rfl⟩ : syracuseStep 186665 = 139999) B139999
theorem B186671 : Blo 123787 186671 := bstep (se 1 (by rfl) ⟨140003, by rfl⟩ : syracuseStep 186671 = 280007) B280007
theorem B186911 : Blo 123787 186911 := bstep (se 1 (by rfl) ⟨140183, by rfl⟩ : syracuseStep 186911 = 280367) B280367
theorem B3267377 : Blo 123787 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B187295 : Blo 123787 187295 := bstep (se 1 (by rfl) ⟨140471, by rfl⟩ : syracuseStep 187295 = 280943) B280943
theorem B187343 : Blo 123787 187343 := bstep (se 1 (by rfl) ⟨140507, by rfl⟩ : syracuseStep 187343 = 281015) B281015
theorem B187433 : Blo 123787 187433 := bstep (se 2 (by rfl) ⟨70287, by rfl⟩ : syracuseStep 187433 = 140575) B140575
theorem B187439 : Blo 123787 187439 := bstep (se 1 (by rfl) ⟨140579, by rfl⟩ : syracuseStep 187439 = 281159) B281159
theorem B187463 : Blo 123787 187463 := bstep (se 1 (by rfl) ⟨140597, by rfl⟩ : syracuseStep 187463 = 281195) B281195
theorem B285767 : Blo 123787 285767 := bstep (se 1 (by rfl) ⟨214325, by rfl⟩ : syracuseStep 285767 = 428651) B428651
theorem B318593 : Blo 123787 318593 := bstep (se 2 (by rfl) ⟨119472, by rfl⟩ : syracuseStep 318593 = 238945) B238945
theorem B187727 : Blo 123787 187727 := bstep (se 1 (by rfl) ⟨140795, by rfl⟩ : syracuseStep 187727 = 281591) B281591
theorem B712097 : Blo 123787 712097 := bstep (se 2 (by rfl) ⟨267036, by rfl⟩ : syracuseStep 712097 = 534073) B534073
theorem B318887 : Blo 123787 318887 := bstep (se 1 (by rfl) ⟨239165, by rfl⟩ : syracuseStep 318887 = 478331) B478331
theorem B187817 : Blo 123787 187817 := bstep (se 2 (by rfl) ⟨70431, by rfl⟩ : syracuseStep 187817 = 140863) B140863
theorem B286163 : Blo 123787 286163 := bstep (se 1 (by rfl) ⟨214622, by rfl⟩ : syracuseStep 286163 = 429245) B429245
theorem B187967 : Blo 123787 187967 := bstep (se 1 (by rfl) ⟨140975, by rfl⟩ : syracuseStep 187967 = 281951) B281951
theorem B286433 : Blo 123787 286433 := bstep (se 2 (by rfl) ⟨107412, by rfl⟩ : syracuseStep 286433 = 214825) B214825
theorem B188231 : Blo 123787 188231 := bstep (se 1 (by rfl) ⟨141173, by rfl⟩ : syracuseStep 188231 = 282347) B282347
theorem B188315 : Blo 123787 188315 := bstep (se 1 (by rfl) ⟨141236, by rfl⟩ : syracuseStep 188315 = 282473) B282473
theorem B319403 : Blo 123787 319403 := bstep (se 1 (by rfl) ⟨239552, by rfl⟩ : syracuseStep 319403 = 479105) B479105
theorem B188879 : Blo 123787 188879 := bstep (se 1 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 188879 = 283319) B283319
theorem B352745 : Blo 123787 352745 := bstep (se 2 (by rfl) ⟨132279, by rfl⟩ : syracuseStep 352745 = 264559) B264559
theorem B188921 : Blo 123787 188921 := bstep (se 2 (by rfl) ⟨70845, by rfl⟩ : syracuseStep 188921 = 141691) B141691
theorem B189023 : Blo 123787 189023 := bstep (se 1 (by rfl) ⟨141767, by rfl⟩ : syracuseStep 189023 = 283535) B283535
theorem B287497 : Blo 123787 287497 := bstep (se 2 (by rfl) ⟨107811, by rfl⟩ : syracuseStep 287497 = 215623) B215623
theorem B418607 : Blo 123787 418607 := bstep (se 1 (by rfl) ⟨313955, by rfl⟩ : syracuseStep 418607 = 627911) B627911
theorem B418715 : Blo 123787 418715 := bstep (se 1 (by rfl) ⟨314036, by rfl⟩ : syracuseStep 418715 = 628073) B628073
theorem B123815 : Blo 123787 123815 := bstep (se 1 (by rfl) ⟨92861, by rfl⟩ : syracuseStep 123815 = 185723) B185723
theorem B123899 : Blo 123787 123899 := bstep (se 1 (by rfl) ⟨92924, by rfl⟩ : syracuseStep 123899 = 185849) B185849
theorem B320537 : Blo 123787 320537 := bstep (se 2 (by rfl) ⟨120201, by rfl⟩ : syracuseStep 320537 = 240403) B240403
theorem B123967 : Blo 123787 123967 := bstep (se 1 (by rfl) ⟨92975, by rfl⟩ : syracuseStep 123967 = 185951) B185951
theorem B189503 : Blo 123787 189503 := bstep (se 1 (by rfl) ⟨142127, by rfl⟩ : syracuseStep 189503 = 284255) B284255
theorem B189545 : Blo 123787 189545 := bstep (se 2 (by rfl) ⟨71079, by rfl⟩ : syracuseStep 189545 = 142159) B142159
theorem B124111 : Blo 123787 124111 := bstep (se 1 (by rfl) ⟨93083, by rfl⟩ : syracuseStep 124111 = 186167) B186167
theorem B189647 : Blo 123787 189647 := bstep (se 1 (by rfl) ⟨142235, by rfl⟩ : syracuseStep 189647 = 284471) B284471
theorem B320719 : Blo 123787 320719 := bstep (se 1 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 320719 = 481079) B481079
theorem B124315 : Blo 123787 124315 := bstep (se 1 (by rfl) ⟨93236, by rfl⟩ : syracuseStep 124315 = 186473) B186473
theorem B189851 : Blo 123787 189851 := bstep (se 1 (by rfl) ⟨142388, by rfl⟩ : syracuseStep 189851 = 284777) B284777
theorem B1467919 : Blo 123787 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B321043 : Blo 123787 321043 := bstep (se 1 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 321043 = 481565) B481565
theorem B124527 : Blo 123787 124527 := bstep (se 1 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 124527 = 186791) B186791
theorem B190073 : Blo 123787 190073 := bstep (se 2 (by rfl) ⟨71277, by rfl⟩ : syracuseStep 190073 = 142555) B142555
theorem B419489 : Blo 123787 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B124583 : Blo 123787 124583 := bstep (se 1 (by rfl) ⟨93437, by rfl⟩ : syracuseStep 124583 = 186875) B186875
theorem B157403 : Blo 123787 157403 := bstep (se 1 (by rfl) ⟨118052, by rfl⟩ : syracuseStep 157403 = 236105) B236105
theorem B190175 : Blo 123787 190175 := bstep (se 1 (by rfl) ⟨142631, by rfl⟩ : syracuseStep 190175 = 285263) B285263
theorem B124667 : Blo 123787 124667 := bstep (se 1 (by rfl) ⟨93500, by rfl⟩ : syracuseStep 124667 = 187001) B187001
theorem B124703 : Blo 123787 124703 := bstep (se 1 (by rfl) ⟨93527, by rfl⟩ : syracuseStep 124703 = 187055) B187055
theorem B124735 : Blo 123787 124735 := bstep (se 1 (by rfl) ⟨93551, by rfl⟩ : syracuseStep 124735 = 187103) B187103
theorem B190271 : Blo 123787 190271 := bstep (se 1 (by rfl) ⟨142703, by rfl⟩ : syracuseStep 190271 = 285407) B285407
theorem B321479 : Blo 123787 321479 := bstep (se 1 (by rfl) ⟨241109, by rfl⟩ : syracuseStep 321479 = 482219) B482219
theorem B190439 : Blo 123787 190439 := bstep (se 1 (by rfl) ⟨142829, by rfl⟩ : syracuseStep 190439 = 285659) B285659
theorem B124911 : Blo 123787 124911 := bstep (se 1 (by rfl) ⟨93683, by rfl⟩ : syracuseStep 124911 = 187367) B187367
theorem B190457 : Blo 123787 190457 := bstep (se 2 (by rfl) ⟨71421, by rfl⟩ : syracuseStep 190457 = 142843) B142843
theorem B419849 : Blo 123787 419849 := bstep (se 2 (by rfl) ⟨157443, by rfl⟩ : syracuseStep 419849 = 314887) B314887
theorem B190559 : Blo 123787 190559 := bstep (se 1 (by rfl) ⟨142919, by rfl⟩ : syracuseStep 190559 = 285839) B285839
theorem B125083 : Blo 123787 125083 := bstep (se 1 (by rfl) ⟨93812, by rfl⟩ : syracuseStep 125083 = 187625) B187625
theorem B190619 : Blo 123787 190619 := bstep (se 1 (by rfl) ⟨142964, by rfl⟩ : syracuseStep 190619 = 285929) B285929
theorem B125119 : Blo 123787 125119 := bstep (se 1 (by rfl) ⟨93839, by rfl⟩ : syracuseStep 125119 = 187679) B187679
theorem B190655 : Blo 123787 190655 := bstep (se 1 (by rfl) ⟨142991, by rfl⟩ : syracuseStep 190655 = 285983) B285983
theorem B190697 : Blo 123787 190697 := bstep (se 2 (by rfl) ⟨71511, by rfl⟩ : syracuseStep 190697 = 143023) B143023
theorem B125231 : Blo 123787 125231 := bstep (se 1 (by rfl) ⟨93923, by rfl⟩ : syracuseStep 125231 = 187847) B187847
theorem B9038141 : Blo 123787 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B3697001 : Blo 123787 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B125467 : Blo 123787 125467 := bstep (se 1 (by rfl) ⟨94100, by rfl⟩ : syracuseStep 125467 = 188201) B188201
theorem B191003 : Blo 123787 191003 := bstep (se 1 (by rfl) ⟨143252, by rfl⟩ : syracuseStep 191003 = 286505) B286505
theorem B125471 : Blo 123787 125471 := bstep (se 1 (by rfl) ⟨94103, by rfl⟩ : syracuseStep 125471 = 188207) B188207
theorem B354887 : Blo 123787 354887 := bstep (se 1 (by rfl) ⟨266165, by rfl⟩ : syracuseStep 354887 = 532331) B532331
theorem B1632869 : Blo 123787 1632869 := bstep (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) B306163
theorem B191081 : Blo 123787 191081 := bstep (se 2 (by rfl) ⟨71655, by rfl⟩ : syracuseStep 191081 = 143311) B143311
theorem B715513 : Blo 123787 715513 := bstep (se 2 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 715513 = 536635) B536635
theorem B125787 : Blo 123787 125787 := bstep (se 1 (by rfl) ⟨94340, by rfl⟩ : syracuseStep 125787 = 188681) B188681
theorem B125855 : Blo 123787 125855 := bstep (se 1 (by rfl) ⟨94391, by rfl⟩ : syracuseStep 125855 = 188783) B188783
theorem B158699 : Blo 123787 158699 := bstep (se 1 (by rfl) ⟨119024, by rfl⟩ : syracuseStep 158699 = 238049) B238049
theorem B125999 : Blo 123787 125999 := bstep (se 1 (by rfl) ⟨94499, by rfl⟩ : syracuseStep 125999 = 188999) B188999
theorem B126023 : Blo 123787 126023 := bstep (se 1 (by rfl) ⟨94517, by rfl⟩ : syracuseStep 126023 = 189035) B189035
theorem B191609 : Blo 123787 191609 := bstep (se 2 (by rfl) ⟨71853, by rfl⟩ : syracuseStep 191609 = 143707) B143707
theorem B126175 : Blo 123787 126175 := bstep (se 1 (by rfl) ⟨94631, by rfl⟩ : syracuseStep 126175 = 189263) B189263
theorem B421145 : Blo 123787 421145 := bstep (se 2 (by rfl) ⟨157929, by rfl⟩ : syracuseStep 421145 = 315859) B315859
theorem B421199 : Blo 123787 421199 := bstep (se 1 (by rfl) ⟨315899, by rfl⟩ : syracuseStep 421199 = 631799) B631799
theorem B126439 : Blo 123787 126439 := bstep (se 1 (by rfl) ⟨94829, by rfl⟩ : syracuseStep 126439 = 189659) B189659
theorem B224831 : Blo 123787 224831 := bstep (se 1 (by rfl) ⟨168623, by rfl⟩ : syracuseStep 224831 = 337247) B337247
theorem B126555 : Blo 123787 126555 := bstep (se 1 (by rfl) ⟨94916, by rfl⟩ : syracuseStep 126555 = 189833) B189833
theorem B356015 : Blo 123787 356015 := bstep (se 1 (by rfl) ⟨267011, by rfl⟩ : syracuseStep 356015 = 534023) B534023
theorem B126791 : Blo 123787 126791 := bstep (se 1 (by rfl) ⟨95093, by rfl⟩ : syracuseStep 126791 = 190187) B190187
theorem B126943 : Blo 123787 126943 := bstep (se 1 (by rfl) ⟨95207, by rfl⟩ : syracuseStep 126943 = 190415) B190415
theorem B1077371 : Blo 123787 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B913619 : Blo 123787 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B127207 : Blo 123787 127207 := bstep (se 1 (by rfl) ⟨95405, by rfl⟩ : syracuseStep 127207 = 190811) B190811
theorem B356663 : Blo 123787 356663 := bstep (se 1 (by rfl) ⟨267497, by rfl⟩ : syracuseStep 356663 = 534995) B534995
theorem B127359 : Blo 123787 127359 := bstep (se 1 (by rfl) ⟨95519, by rfl⟩ : syracuseStep 127359 = 191039) B191039
theorem B127439 : Blo 123787 127439 := bstep (se 1 (by rfl) ⟨95579, by rfl⟩ : syracuseStep 127439 = 191159) B191159
theorem B225875 : Blo 123787 225875 := bstep (se 1 (by rfl) ⟨169406, by rfl⟩ : syracuseStep 225875 = 338813) B338813
theorem B258643 : Blo 123787 258643 := bstep (se 1 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 258643 = 387965) B387965
theorem B422495 : Blo 123787 422495 := bstep (se 1 (by rfl) ⟨316871, by rfl⟩ : syracuseStep 422495 = 633743) B633743
theorem B127591 : Blo 123787 127591 := bstep (se 1 (by rfl) ⟨95693, by rfl⟩ : syracuseStep 127591 = 191387) B191387
theorem B324481 : Blo 123787 324481 := bstep (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) B243361
theorem B193447 : Blo 123787 193447 := bstep (se 1 (by rfl) ⟨145085, by rfl⟩ : syracuseStep 193447 = 290171) B290171
theorem B816641 : Blo 123787 816641 := bstep (se 2 (by rfl) ⟨306240, by rfl⟩ : syracuseStep 816641 = 612481) B612481
theorem B423737 : Blo 123787 423737 := bstep (se 2 (by rfl) ⟨158901, by rfl⟩ : syracuseStep 423737 = 317803) B317803
theorem B423899 : Blo 123787 423899 := bstep (se 1 (by rfl) ⟨317924, by rfl⟩ : syracuseStep 423899 = 635849) B635849
theorem B227519 : Blo 123787 227519 := bstep (se 1 (by rfl) ⟨170639, by rfl⟩ : syracuseStep 227519 = 341279) B341279
theorem B424169 : Blo 123787 424169 := bstep (se 2 (by rfl) ⟨159063, by rfl⟩ : syracuseStep 424169 = 318127) B318127
theorem B915785 : Blo 123787 915785 := bstep (se 2 (by rfl) ⟨343419, by rfl⟩ : syracuseStep 915785 = 686839) B686839
theorem B358931 : Blo 123787 358931 := bstep (se 1 (by rfl) ⟨269198, by rfl⟩ : syracuseStep 358931 = 538397) B538397
theorem B424601 : Blo 123787 424601 := bstep (se 2 (by rfl) ⟨159225, by rfl⟩ : syracuseStep 424601 = 318451) B318451
theorem B949157 : Blo 123787 949157 := bstep (se 4 (by rfl) ⟨88983, by rfl⟩ : syracuseStep 949157 = 177967) B177967
theorem B719887 : Blo 123787 719887 := bstep (se 1 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 719887 = 1079831) B1079831
theorem B818333 : Blo 123787 818333 := bstep (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) B306875
theorem B1670519 : Blo 123787 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B3440015 : Blo 123787 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B360263 : Blo 123787 360263 := bstep (se 1 (by rfl) ⟨270197, by rfl⟩ : syracuseStep 360263 = 540395) B540395
theorem B4129055 : Blo 123787 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B951101 : Blo 123787 951101 := bstep (se 3 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 951101 = 356663) B356663
theorem B1639727 : Blo 123787 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B427355 : Blo 123787 427355 := bstep (se 1 (by rfl) ⟨320516, by rfl⟩ : syracuseStep 427355 = 641033) B641033
theorem B2360927 : Blo 123787 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B427625 : Blo 123787 427625 := bstep (se 2 (by rfl) ⟨160359, by rfl⟩ : syracuseStep 427625 = 320719) B320719
theorem B427787 : Blo 123787 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B428057 : Blo 123787 428057 := bstep (se 2 (by rfl) ⟨160521, by rfl⟩ : syracuseStep 428057 = 321043) B321043
theorem B428219 : Blo 123787 428219 := bstep (se 1 (by rfl) ⟨321164, by rfl⟩ : syracuseStep 428219 = 642329) B642329
theorem B199675 : Blo 123787 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B1379429 : Blo 123787 1379429 := bstep (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) B258643
theorem B953531 : Blo 123787 953531 := bstep (se 1 (by rfl) ⟨715148, by rfl⟩ : syracuseStep 953531 = 1430297) B1430297
theorem B429407 : Blo 123787 429407 := bstep (se 1 (by rfl) ⟨322055, by rfl⟩ : syracuseStep 429407 = 644111) B644111
theorem B2624993 : Blo 123787 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B954017 : Blo 123787 954017 := bstep (se 2 (by rfl) ⟨357756, by rfl⟩ : syracuseStep 954017 = 715513) B715513
theorem B5148335 : Blo 123787 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B429947 : Blo 123787 429947 := bstep (se 1 (by rfl) ⟨322460, by rfl⟩ : syracuseStep 429947 = 644921) B644921
theorem B266807 : Blo 123787 266807 := bstep (se 1 (by rfl) ⟨200105, by rfl⟩ : syracuseStep 266807 = 400211) B400211
theorem B529391 : Blo 123787 529391 := bstep (se 1 (by rfl) ⟨397043, by rfl⟩ : syracuseStep 529391 = 794087) B794087
theorem B136175 : Blo 123787 136175 := bstep (se 1 (by rfl) ⟨102131, by rfl⟩ : syracuseStep 136175 = 204263) B204263
theorem B15832493 : Blo 123787 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B267695 : Blo 123787 267695 := bstep (se 1 (by rfl) ⟨200771, by rfl⟩ : syracuseStep 267695 = 401543) B401543
theorem B235163 : Blo 123787 235163 := bstep (se 1 (by rfl) ⟨176372, by rfl⟩ : syracuseStep 235163 = 352745) B352745
theorem B235361 : Blo 123787 235361 := bstep (se 2 (by rfl) ⟨88260, by rfl⟩ : syracuseStep 235361 = 176521) B176521
theorem B1513363 : Blo 123787 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B727177 : Blo 123787 727177 := bstep (se 2 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 727177 = 545383) B545383
theorem B236009 : Blo 123787 236009 := bstep (se 2 (by rfl) ⟨88503, by rfl⟩ : syracuseStep 236009 = 177007) B177007
theorem B432641 : Blo 123787 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B2464667 : Blo 123787 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B236591 : Blo 123787 236591 := bstep (se 1 (by rfl) ⟨177443, by rfl⟩ : syracuseStep 236591 = 354887) B354887
theorem B1088579 : Blo 123787 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B597257 : Blo 123787 597257 := bstep (se 2 (by rfl) ⟨223971, by rfl⟩ : syracuseStep 597257 = 447943) B447943
theorem B1023329 : Blo 123787 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B237343 : Blo 123787 237343 := bstep (se 1 (by rfl) ⟨178007, by rfl⟩ : syracuseStep 237343 = 356015) B356015
theorem B9117535 : Blo 123787 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B401375 : Blo 123787 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B139567 : Blo 123787 139567 := bstep (se 1 (by rfl) ⟨104675, by rfl⟩ : syracuseStep 139567 = 209351) B209351
theorem B959849 : Blo 123787 959849 := bstep (se 2 (by rfl) ⟨359943, by rfl⟩ : syracuseStep 959849 = 719887) B719887
theorem B1418633 : Blo 123787 1418633 := bstep (se 2 (by rfl) ⟨531987, by rfl⟩ : syracuseStep 1418633 = 1063975) B1063975
theorem B402887 : Blo 123787 402887 := bstep (se 1 (by rfl) ⟨302165, by rfl⟩ : syracuseStep 402887 = 604331) B604331
theorem B140827 : Blo 123787 140827 := bstep (se 1 (by rfl) ⟨105620, by rfl⟩ : syracuseStep 140827 = 211241) B211241
theorem B239287 : Blo 123787 239287 := bstep (se 1 (by rfl) ⟨179465, by rfl⟩ : syracuseStep 239287 = 358931) B358931
theorem B632771 : Blo 123787 632771 := bstep (se 1 (by rfl) ⟨474578, by rfl⟩ : syracuseStep 632771 = 949157) B949157
theorem B141871 : Blo 123787 141871 := bstep (se 1 (by rfl) ⟨106403, by rfl⟩ : syracuseStep 141871 = 212807) B212807
theorem B240175 : Blo 123787 240175 := bstep (se 1 (by rfl) ⟨180131, by rfl⟩ : syracuseStep 240175 = 360263) B360263
theorem B142303 : Blo 123787 142303 := bstep (se 1 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 142303 = 213455) B213455
theorem B240713 : Blo 123787 240713 := bstep (se 2 (by rfl) ⟨90267, by rfl⟩ : syracuseStep 240713 = 180535) B180535
theorem B2436317 : Blo 123787 2436317 := bstep (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) B913619
theorem B306587 : Blo 123787 306587 := bstep (se 1 (by rfl) ⟨229940, by rfl⟩ : syracuseStep 306587 = 459881) B459881
theorem B142951 : Blo 123787 142951 := bstep (se 1 (by rfl) ⟨107213, by rfl⟩ : syracuseStep 142951 = 214427) B214427
theorem B569015 : Blo 123787 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B143167 : Blo 123787 143167 := bstep (se 1 (by rfl) ⟨107375, by rfl⟩ : syracuseStep 143167 = 214751) B214751
theorem B143455 : Blo 123787 143455 := bstep (se 1 (by rfl) ⟨107591, by rfl⟩ : syracuseStep 143455 = 215183) B215183
theorem B405643 : Blo 123787 405643 := bstep (se 1 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 405643 = 608465) B608465
theorem B536807 : Blo 123787 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B2044295 : Blo 123787 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B1225115 : Blo 123787 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B242119 : Blo 123787 242119 := bstep (se 1 (by rfl) ⟨181589, by rfl⟩ : syracuseStep 242119 = 363179) B363179
theorem B210343 : Blo 123787 210343 := bstep (se 1 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 210343 = 315515) B315515
theorem B1455731 : Blo 123787 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B604523 : Blo 123787 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B637307 : Blo 123787 637307 := bstep (se 1 (by rfl) ⟨477980, by rfl⟩ : syracuseStep 637307 = 955961) B955961
theorem B5355929 : Blo 123787 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B539081 : Blo 123787 539081 := bstep (se 2 (by rfl) ⟨202155, by rfl⟩ : syracuseStep 539081 = 404311) B404311
theorem B473759 : Blo 123787 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B539369 : Blo 123787 539369 := bstep (se 2 (by rfl) ⟨202263, by rfl⟩ : syracuseStep 539369 = 404527) B404527
theorem B7650125 : Blo 123787 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B2178251 : Blo 123787 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B212395 : Blo 123787 212395 := bstep (se 1 (by rfl) ⟨159296, by rfl⟩ : syracuseStep 212395 = 318593) B318593
theorem B1031717 : Blo 123787 1031717 := bstep (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) B193447
theorem B2866747 : Blo 123787 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B474731 : Blo 123787 474731 := bstep (se 1 (by rfl) ⟨356048, by rfl⟩ : syracuseStep 474731 = 712097) B712097
theorem B212591 : Blo 123787 212591 := bstep (se 1 (by rfl) ⟨159443, by rfl⟩ : syracuseStep 212591 = 318887) B318887
theorem B212935 : Blo 123787 212935 := bstep (se 1 (by rfl) ⟨159701, by rfl⟩ : syracuseStep 212935 = 319403) B319403
theorem B1622207 : Blo 123787 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B541009 : Blo 123787 541009 := bstep (se 2 (by rfl) ⟨202878, by rfl⟩ : syracuseStep 541009 = 405757) B405757
theorem B541181 : Blo 123787 541181 := bstep (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) B202943
theorem B279071 : Blo 123787 279071 := bstep (se 1 (by rfl) ⟨209303, by rfl⟩ : syracuseStep 279071 = 418607) B418607
theorem B1360435 : Blo 123787 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B1229363 : Blo 123787 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B279143 : Blo 123787 279143 := bstep (se 1 (by rfl) ⟨209357, by rfl⟩ : syracuseStep 279143 = 418715) B418715
theorem B213691 : Blo 123787 213691 := bstep (se 1 (by rfl) ⟨160268, by rfl⟩ : syracuseStep 213691 = 320537) B320537
theorem B279659 : Blo 123787 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B214319 : Blo 123787 214319 := bstep (se 1 (by rfl) ⟨160739, by rfl⟩ : syracuseStep 214319 = 321479) B321479
theorem B279899 : Blo 123787 279899 := bstep (se 1 (by rfl) ⟨209924, by rfl⟩ : syracuseStep 279899 = 419849) B419849
theorem B509291 : Blo 123787 509291 := bstep (se 1 (by rfl) ⟨381968, by rfl⟩ : syracuseStep 509291 = 763937) B763937
theorem B280169 : Blo 123787 280169 := bstep (se 2 (by rfl) ⟨105063, by rfl⟩ : syracuseStep 280169 = 210127) B210127
theorem B280763 : Blo 123787 280763 := bstep (se 1 (by rfl) ⟨210572, by rfl⟩ : syracuseStep 280763 = 421145) B421145
theorem B575687 : Blo 123787 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B280799 : Blo 123787 280799 := bstep (se 1 (by rfl) ⟨210599, by rfl⟩ : syracuseStep 280799 = 421199) B421199
theorem B969083 : Blo 123787 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B149887 : Blo 123787 149887 := bstep (se 1 (by rfl) ⟨112415, by rfl⟩ : syracuseStep 149887 = 224831) B224831
theorem B1952261 : Blo 123787 1952261 := bstep (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) B366049
theorem B281249 : Blo 123787 281249 := bstep (se 2 (by rfl) ⟨105468, by rfl⟩ : syracuseStep 281249 = 210937) B210937
theorem B576161 : Blo 123787 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B281465 : Blo 123787 281465 := bstep (se 2 (by rfl) ⟨105549, by rfl⟩ : syracuseStep 281465 = 211099) B211099
theorem B281609 : Blo 123787 281609 := bstep (se 2 (by rfl) ⟨105603, by rfl⟩ : syracuseStep 281609 = 211207) B211207
theorem B150583 : Blo 123787 150583 := bstep (se 1 (by rfl) ⟨112937, by rfl⟩ : syracuseStep 150583 = 225875) B225875
theorem B281663 : Blo 123787 281663 := bstep (se 1 (by rfl) ⟨211247, by rfl⟩ : syracuseStep 281663 = 422495) B422495
theorem B314543 : Blo 123787 314543 := bstep (se 1 (by rfl) ⟨235907, by rfl⟩ : syracuseStep 314543 = 471815) B471815
theorem B1035767 : Blo 123787 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B544427 : Blo 123787 544427 := bstep (se 1 (by rfl) ⟨408320, by rfl⟩ : syracuseStep 544427 = 816641) B816641
theorem B315161 : Blo 123787 315161 := bstep (se 2 (by rfl) ⟨118185, by rfl⟩ : syracuseStep 315161 = 236371) B236371
theorem B282491 : Blo 123787 282491 := bstep (se 1 (by rfl) ⟨211868, by rfl⟩ : syracuseStep 282491 = 423737) B423737
theorem B282599 : Blo 123787 282599 := bstep (se 1 (by rfl) ⟨211949, by rfl⟩ : syracuseStep 282599 = 423899) B423899
theorem B151679 : Blo 123787 151679 := bstep (se 1 (by rfl) ⟨113759, by rfl⟩ : syracuseStep 151679 = 227519) B227519
theorem B282779 : Blo 123787 282779 := bstep (se 1 (by rfl) ⟨212084, by rfl⟩ : syracuseStep 282779 = 424169) B424169
theorem B610523 : Blo 123787 610523 := bstep (se 1 (by rfl) ⟨457892, by rfl⟩ : syracuseStep 610523 = 915785) B915785
theorem B282977 : Blo 123787 282977 := bstep (se 2 (by rfl) ⟨106116, by rfl⟩ : syracuseStep 282977 = 212233) B212233
theorem B1790333 : Blo 123787 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B283067 : Blo 123787 283067 := bstep (se 1 (by rfl) ⟨212300, by rfl⟩ : syracuseStep 283067 = 424601) B424601
theorem B545555 : Blo 123787 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B2151461 : Blo 123787 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B185711 : Blo 123787 185711 := bstep (se 1 (by rfl) ⟨139283, by rfl⟩ : syracuseStep 185711 = 278567) B278567
theorem B185831 : Blo 123787 185831 := bstep (se 1 (by rfl) ⟨139373, by rfl⟩ : syracuseStep 185831 = 278747) B278747
theorem B2152007 : Blo 123787 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B185993 : Blo 123787 185993 := bstep (se 2 (by rfl) ⟨69747, by rfl⟩ : syracuseStep 185993 = 139495) B139495
theorem B186011 : Blo 123787 186011 := bstep (se 1 (by rfl) ⟨139508, by rfl⟩ : syracuseStep 186011 = 279017) B279017
theorem B284327 : Blo 123787 284327 := bstep (se 1 (by rfl) ⟨213245, by rfl⟩ : syracuseStep 284327 = 426491) B426491
theorem B186203 : Blo 123787 186203 := bstep (se 1 (by rfl) ⟨139652, by rfl⟩ : syracuseStep 186203 = 279305) B279305
theorem B284507 : Blo 123787 284507 := bstep (se 1 (by rfl) ⟨213380, by rfl⟩ : syracuseStep 284507 = 426761) B426761
theorem B317479 : Blo 123787 317479 := bstep (se 1 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 317479 = 476219) B476219
theorem B1431755 : Blo 123787 1431755 := bstep (se 1 (by rfl) ⟨1073816, by rfl⟩ : syracuseStep 1431755 = 2147633) B2147633
theorem B186587 : Blo 123787 186587 := bstep (se 1 (by rfl) ⟨139940, by rfl⟩ : syracuseStep 186587 = 279881) B279881
theorem B317753 : Blo 123787 317753 := bstep (se 2 (by rfl) ⟨119157, by rfl⟩ : syracuseStep 317753 = 238315) B238315
theorem B285011 : Blo 123787 285011 := bstep (se 1 (by rfl) ⟨213758, by rfl⟩ : syracuseStep 285011 = 427517) B427517
theorem B383329 : Blo 123787 383329 := bstep (se 2 (by rfl) ⟨143748, by rfl⟩ : syracuseStep 383329 = 287497) B287497
theorem B2087279 : Blo 123787 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B186857 : Blo 123787 186857 := bstep (se 2 (by rfl) ⟨70071, by rfl⟩ : syracuseStep 186857 = 140143) B140143
theorem B285497 : Blo 123787 285497 := bstep (se 2 (by rfl) ⟨107061, by rfl⟩ : syracuseStep 285497 = 214123) B214123
theorem B908111 : Blo 123787 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B187247 : Blo 123787 187247 := bstep (se 1 (by rfl) ⟨140435, by rfl⟩ : syracuseStep 187247 = 280871) B280871
theorem B285551 : Blo 123787 285551 := bstep (se 1 (by rfl) ⟨214163, by rfl⟩ : syracuseStep 285551 = 428327) B428327
theorem B187259 : Blo 123787 187259 := bstep (se 1 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 187259 = 280889) B280889
theorem B1137617 : Blo 123787 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B482537 : Blo 123787 482537 := bstep (se 2 (by rfl) ⟨180951, by rfl⟩ : syracuseStep 482537 = 361903) B361903
theorem B1957225 : Blo 123787 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B286127 : Blo 123787 286127 := bstep (se 1 (by rfl) ⟨214595, by rfl⟩ : syracuseStep 286127 = 429191) B429191
theorem B286199 : Blo 123787 286199 := bstep (se 1 (by rfl) ⟨214649, by rfl⟩ : syracuseStep 286199 = 429299) B429299
theorem B188123 : Blo 123787 188123 := bstep (se 1 (by rfl) ⟨141092, by rfl⟩ : syracuseStep 188123 = 282185) B282185
theorem B188393 : Blo 123787 188393 := bstep (se 2 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 188393 = 141295) B141295
theorem B287225 : Blo 123787 287225 := bstep (se 2 (by rfl) ⟨107709, by rfl⟩ : syracuseStep 287225 = 215419) B215419
theorem B287315 : Blo 123787 287315 := bstep (se 1 (by rfl) ⟨215486, by rfl⟩ : syracuseStep 287315 = 430973) B430973
theorem B189095 : Blo 123787 189095 := bstep (se 1 (by rfl) ⟨141821, by rfl⟩ : syracuseStep 189095 = 283643) B283643
theorem B287495 : Blo 123787 287495 := bstep (se 1 (by rfl) ⟨215621, by rfl⟩ : syracuseStep 287495 = 431243) B431243
theorem B189215 : Blo 123787 189215 := bstep (se 1 (by rfl) ⟨141911, by rfl⟩ : syracuseStep 189215 = 283823) B283823
theorem B189239 : Blo 123787 189239 := bstep (se 1 (by rfl) ⟨141929, by rfl⟩ : syracuseStep 189239 = 283859) B283859
theorem B189419 : Blo 123787 189419 := bstep (se 1 (by rfl) ⟨142064, by rfl⟩ : syracuseStep 189419 = 284129) B284129
theorem B123951 : Blo 123787 123951 := bstep (se 1 (by rfl) ⟨92963, by rfl⟩ : syracuseStep 123951 = 185927) B185927
theorem B3892313 : Blo 123787 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B124015 : Blo 123787 124015 := bstep (se 1 (by rfl) ⟨93011, by rfl⟩ : syracuseStep 124015 = 186023) B186023
theorem B2679965 : Blo 123787 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B124071 : Blo 123787 124071 := bstep (se 1 (by rfl) ⟨93053, by rfl⟩ : syracuseStep 124071 = 186107) B186107
theorem B124095 : Blo 123787 124095 := bstep (se 1 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 124095 = 186143) B186143
theorem B124127 : Blo 123787 124127 := bstep (se 1 (by rfl) ⟨93095, by rfl⟩ : syracuseStep 124127 = 186191) B186191
theorem B124207 : Blo 123787 124207 := bstep (se 1 (by rfl) ⟨93155, by rfl⟩ : syracuseStep 124207 = 186311) B186311
theorem B124443 : Blo 123787 124443 := bstep (se 1 (by rfl) ⟨93332, by rfl⟩ : syracuseStep 124443 = 186665) B186665
theorem B124447 : Blo 123787 124447 := bstep (se 1 (by rfl) ⟨93335, by rfl⟩ : syracuseStep 124447 = 186671) B186671
theorem B124607 : Blo 123787 124607 := bstep (se 1 (by rfl) ⟨93455, by rfl⟩ : syracuseStep 124607 = 186911) B186911
theorem B419579 : Blo 123787 419579 := bstep (se 1 (by rfl) ⟨314684, by rfl⟩ : syracuseStep 419579 = 629369) B629369
theorem B3860261 : Blo 123787 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B354203 : Blo 123787 354203 := bstep (se 1 (by rfl) ⟨265652, by rfl⟩ : syracuseStep 354203 = 531305) B531305
theorem B419741 : Blo 123787 419741 := bstep (se 3 (by rfl) ⟨78701, by rfl⟩ : syracuseStep 419741 = 157403) B157403
theorem B124863 : Blo 123787 124863 := bstep (se 1 (by rfl) ⟨93647, by rfl⟩ : syracuseStep 124863 = 187295) B187295
theorem B124895 : Blo 123787 124895 := bstep (se 1 (by rfl) ⟨93671, by rfl⟩ : syracuseStep 124895 = 187343) B187343
theorem B321529 : Blo 123787 321529 := bstep (se 2 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 321529 = 241147) B241147
theorem B124955 : Blo 123787 124955 := bstep (se 1 (by rfl) ⟨93716, by rfl⟩ : syracuseStep 124955 = 187433) B187433
theorem B124959 : Blo 123787 124959 := bstep (se 1 (by rfl) ⟨93719, by rfl⟩ : syracuseStep 124959 = 187439) B187439
theorem B223279 : Blo 123787 223279 := bstep (se 1 (by rfl) ⟨167459, by rfl⟩ : syracuseStep 223279 = 334919) B334919
theorem B124975 : Blo 123787 124975 := bstep (se 1 (by rfl) ⟨93731, by rfl⟩ : syracuseStep 124975 = 187463) B187463
theorem B190511 : Blo 123787 190511 := bstep (se 1 (by rfl) ⟨142883, by rfl⟩ : syracuseStep 190511 = 285767) B285767
theorem B125151 : Blo 123787 125151 := bstep (se 1 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 125151 = 187727) B187727
theorem B125211 : Blo 123787 125211 := bstep (se 1 (by rfl) ⟨93908, by rfl⟩ : syracuseStep 125211 = 187817) B187817
theorem B190775 : Blo 123787 190775 := bstep (se 1 (by rfl) ⟨143081, by rfl⟩ : syracuseStep 190775 = 286163) B286163
theorem B125311 : Blo 123787 125311 := bstep (se 1 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 125311 = 187967) B187967
theorem B190955 : Blo 123787 190955 := bstep (se 1 (by rfl) ⟨143216, by rfl⟩ : syracuseStep 190955 = 286433) B286433
theorem B223735 : Blo 123787 223735 := bstep (se 1 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 223735 = 335603) B335603
theorem B1010207 : Blo 123787 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B125487 : Blo 123787 125487 := bstep (se 1 (by rfl) ⟨94115, by rfl⟩ : syracuseStep 125487 = 188231) B188231
theorem B125543 : Blo 123787 125543 := bstep (se 1 (by rfl) ⟨94157, by rfl⟩ : syracuseStep 125543 = 188315) B188315
theorem B125919 : Blo 123787 125919 := bstep (se 1 (by rfl) ⟨94439, by rfl⟩ : syracuseStep 125919 = 188879) B188879
theorem B125947 : Blo 123787 125947 := bstep (se 1 (by rfl) ⟨94460, by rfl⟩ : syracuseStep 125947 = 188921) B188921
theorem B126015 : Blo 123787 126015 := bstep (se 1 (by rfl) ⟨94511, by rfl⟩ : syracuseStep 126015 = 189023) B189023
theorem B191657 : Blo 123787 191657 := bstep (se 2 (by rfl) ⟨71871, by rfl⟩ : syracuseStep 191657 = 143743) B143743
theorem B126335 : Blo 123787 126335 := bstep (se 1 (by rfl) ⟨94751, by rfl⟩ : syracuseStep 126335 = 189503) B189503
theorem B126363 : Blo 123787 126363 := bstep (se 1 (by rfl) ⟨94772, by rfl⟩ : syracuseStep 126363 = 189545) B189545
theorem B126431 : Blo 123787 126431 := bstep (se 1 (by rfl) ⟨94823, by rfl⟩ : syracuseStep 126431 = 189647) B189647
theorem B126567 : Blo 123787 126567 := bstep (se 1 (by rfl) ⟨94925, by rfl⟩ : syracuseStep 126567 = 189851) B189851
theorem B3862225 : Blo 123787 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B552673 : Blo 123787 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B126715 : Blo 123787 126715 := bstep (se 1 (by rfl) ⟨95036, by rfl⟩ : syracuseStep 126715 = 190073) B190073
theorem B126783 : Blo 123787 126783 := bstep (se 1 (by rfl) ⟨95087, by rfl⟩ : syracuseStep 126783 = 190175) B190175
theorem B126847 : Blo 123787 126847 := bstep (se 1 (by rfl) ⟨95135, by rfl⟩ : syracuseStep 126847 = 190271) B190271
theorem B126959 : Blo 123787 126959 := bstep (se 1 (by rfl) ⟨95219, by rfl⟩ : syracuseStep 126959 = 190439) B190439
theorem B356345 : Blo 123787 356345 := bstep (se 2 (by rfl) ⟨133629, by rfl⟩ : syracuseStep 356345 = 267259) B267259
theorem B126971 : Blo 123787 126971 := bstep (se 1 (by rfl) ⟨95228, by rfl⟩ : syracuseStep 126971 = 190457) B190457
theorem B127039 : Blo 123787 127039 := bstep (se 1 (by rfl) ⟨95279, by rfl⟩ : syracuseStep 127039 = 190559) B190559
theorem B127079 : Blo 123787 127079 := bstep (se 1 (by rfl) ⟨95309, by rfl⟩ : syracuseStep 127079 = 190619) B190619
theorem B127103 : Blo 123787 127103 := bstep (se 1 (by rfl) ⟨95327, by rfl⟩ : syracuseStep 127103 = 190655) B190655
theorem B127131 : Blo 123787 127131 := bstep (se 1 (by rfl) ⟨95348, by rfl⟩ : syracuseStep 127131 = 190697) B190697
theorem B6025427 : Blo 123787 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B487705 : Blo 123787 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B127335 : Blo 123787 127335 := bstep (se 1 (by rfl) ⟨95501, by rfl⟩ : syracuseStep 127335 = 191003) B191003
theorem B127387 : Blo 123787 127387 := bstep (se 1 (by rfl) ⟨95540, by rfl⟩ : syracuseStep 127387 = 191081) B191081
theorem B1864225 : Blo 123787 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B946727 : Blo 123787 946727 := bstep (se 1 (by rfl) ⟨710045, by rfl⟩ : syracuseStep 946727 = 1420091) B1420091
theorem B127739 : Blo 123787 127739 := bstep (se 1 (by rfl) ⟨95804, by rfl⟩ : syracuseStep 127739 = 191609) B191609
theorem B619325 : Blo 123787 619325 := bstep (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) B232247
theorem B226567 : Blo 123787 226567 := bstep (se 1 (by rfl) ⟨169925, by rfl⟩ : syracuseStep 226567 = 339851) B339851
theorem B423197 : Blo 123787 423197 := bstep (se 3 (by rfl) ⟨79349, by rfl⟩ : syracuseStep 423197 = 158699) B158699
theorem B718247 : Blo 123787 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B357803 : Blo 123787 357803 := bstep (se 1 (by rfl) ⟨268352, by rfl⟩ : syracuseStep 357803 = 536705) B536705
theorem B619987 : Blo 123787 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B1013971 : Blo 123787 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B1636969 : Blo 123787 1636969 := bstep (se 2 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 1636969 = 1227727) B1227727
theorem B359147 : Blo 123787 359147 := bstep (se 1 (by rfl) ⟨269360, by rfl⟩ : syracuseStep 359147 = 538721) B538721
theorem B228577 : Blo 123787 228577 := bstep (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) B171433
theorem B949643 : Blo 123787 949643 := bstep (se 1 (by rfl) ⟨712232, by rfl⟩ : syracuseStep 949643 = 1424465) B1424465
theorem B1113679 : Blo 123787 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B2293343 : Blo 123787 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B1081471 : Blo 123787 1081471 := bstep (se 1 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 1081471 = 1622207) B1622207
theorem B2752703 : Blo 123787 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B360787 : Blo 123787 360787 := bstep (se 1 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 360787 = 541181) B541181
theorem B819575 : Blo 123787 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B721345 : Blo 123787 721345 := bstep (se 2 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 721345 = 541009) B541009
theorem B919619 : Blo 123787 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B362951 : Blo 123787 362951 := bstep (se 1 (by rfl) ⟨272213, by rfl⟩ : syracuseStep 362951 = 544427) B544427
theorem B363133 : Blo 123787 363133 := bstep (se 3 (by rfl) ⟨68087, by rfl⟩ : syracuseStep 363133 = 136175) B136175
theorem B428705 : Blo 123787 428705 := bstep (se 2 (by rfl) ⟨160764, by rfl⟩ : syracuseStep 428705 = 321529) B321529
theorem B199849 : Blo 123787 199849 := bstep (se 2 (by rfl) ⟨74943, by rfl⟩ : syracuseStep 199849 = 149887) B149887
theorem B363703 : Blo 123787 363703 := bstep (se 1 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 363703 = 545555) B545555
theorem B298313 : Blo 123787 298313 := bstep (se 2 (by rfl) ⟨111867, by rfl⟩ : syracuseStep 298313 = 223735) B223735
theorem B10554995 : Blo 123787 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B200777 : Blo 123787 200777 := bstep (se 2 (by rfl) ⟨75291, by rfl⟩ : syracuseStep 200777 = 150583) B150583
theorem B954503 : Blo 123787 954503 := bstep (se 1 (by rfl) ⟨715877, by rfl⟩ : syracuseStep 954503 = 1431755) B1431755
theorem B6295805 : Blo 123787 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B627101 : Blo 123787 627101 := bstep (se 3 (by rfl) ⟨117581, by rfl⟩ : syracuseStep 627101 = 235163) B235163
theorem B1643111 : Blo 123787 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B758411 : Blo 123787 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B725719 : Blo 123787 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B398171 : Blo 123787 398171 := bstep (se 1 (by rfl) ⟨298628, by rfl⟩ : syracuseStep 398171 = 597257) B597257
theorem B2594875 : Blo 123787 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B1612061 : Blo 123787 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B268591 : Blo 123787 268591 := bstep (se 1 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 268591 = 402887) B402887
theorem B236135 : Blo 123787 236135 := bstep (se 1 (by rfl) ⟨177101, by rfl⟩ : syracuseStep 236135 = 354203) B354203
theorem B302089 : Blo 123787 302089 := bstep (se 2 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 302089 = 226567) B226567
theorem B826649 : Blo 123787 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B204391 : Blo 123787 204391 := bstep (se 1 (by rfl) ⟨153293, by rfl⟩ : syracuseStep 204391 = 306587) B306587
theorem B237563 : Blo 123787 237563 := bstep (se 1 (by rfl) ⟨178172, by rfl⟩ : syracuseStep 237563 = 356345) B356345
theorem B1351961 : Blo 123787 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B631151 : Blo 123787 631151 := bstep (se 1 (by rfl) ⟨473363, by rfl⟩ : syracuseStep 631151 = 946727) B946727
theorem B238535 : Blo 123787 238535 := bstep (se 1 (by rfl) ⟨178901, by rfl⟩ : syracuseStep 238535 = 357803) B357803
theorem B2762045 : Blo 123787 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B304769 : Blo 123787 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B239431 : Blo 123787 239431 := bstep (se 1 (by rfl) ⟨179573, by rfl⟩ : syracuseStep 239431 = 359147) B359147
theorem B1484905 : Blo 123787 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B1452167 : Blo 123787 1452167 := bstep (se 1 (by rfl) ⟨1089125, by rfl⟩ : syracuseStep 1452167 = 2178251) B2178251
theorem B633095 : Blo 123787 633095 := bstep (se 1 (by rfl) ⟨474821, by rfl⟩ : syracuseStep 633095 = 949643) B949643
theorem B141727 : Blo 123787 141727 := bstep (se 1 (by rfl) ⟨106295, by rfl⟩ : syracuseStep 141727 = 212591) B212591
theorem B404477 : Blo 123787 404477 := bstep (se 3 (by rfl) ⟨75839, by rfl⟩ : syracuseStep 404477 = 151679) B151679
theorem B634067 : Blo 123787 634067 := bstep (se 1 (by rfl) ⟨475550, by rfl⟩ : syracuseStep 634067 = 951101) B951101
theorem B1813913 : Blo 123787 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B1093151 : Blo 123787 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B142879 : Blo 123787 142879 := bstep (se 1 (by rfl) ⟨107159, by rfl⟩ : syracuseStep 142879 = 214319) B214319
theorem B339527 : Blo 123787 339527 := bstep (se 1 (by rfl) ⟨254645, by rfl⟩ : syracuseStep 339527 = 509291) B509291
theorem B4763285 : Blo 123787 4763285 := bstep (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) B223279
theorem B209695 : Blo 123787 209695 := bstep (se 1 (by rfl) ⟨157271, by rfl⟩ : syracuseStep 209695 = 314543) B314543
theorem B635687 : Blo 123787 635687 := bstep (se 1 (by rfl) ⟨476765, by rfl⟩ : syracuseStep 635687 = 953531) B953531
theorem B1749995 : Blo 123787 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B636011 : Blo 123787 636011 := bstep (se 1 (by rfl) ⟨477008, by rfl⟩ : syracuseStep 636011 = 954017) B954017
theorem B210107 : Blo 123787 210107 := bstep (se 1 (by rfl) ⟨157580, by rfl⟩ : syracuseStep 210107 = 315161) B315161
theorem B407015 : Blo 123787 407015 := bstep (se 1 (by rfl) ⟨305261, by rfl⟩ : syracuseStep 407015 = 610523) B610523
theorem B1193555 : Blo 123787 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B177871 : Blo 123787 177871 := bstep (se 1 (by rfl) ⟨133403, by rfl⟩ : syracuseStep 177871 = 266807) B266807
theorem B178463 : Blo 123787 178463 := bstep (se 1 (by rfl) ⟨133847, by rfl⟩ : syracuseStep 178463 = 267695) B267695
theorem B211835 : Blo 123787 211835 := bstep (se 1 (by rfl) ⟨158876, by rfl⟩ : syracuseStep 211835 = 317753) B317753
theorem B1391519 : Blo 123787 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B605407 : Blo 123787 605407 := bstep (se 1 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 605407 = 908111) B908111
theorem B736897 : Blo 123787 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B1064933 : Blo 123787 1064933 := bstep (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) B199675
theorem B540857 : Blo 123787 540857 := bstep (se 2 (by rfl) ⟨202821, by rfl⟩ : syracuseStep 540857 = 405643) B405643
theorem B1786643 : Blo 123787 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B639899 : Blo 123787 639899 := bstep (se 1 (by rfl) ⟨479924, by rfl⟩ : syracuseStep 639899 = 959849) B959849
theorem B279719 : Blo 123787 279719 := bstep (se 1 (by rfl) ⟨209789, by rfl⟩ : syracuseStep 279719 = 419579) B419579
theorem B2573507 : Blo 123787 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B279827 : Blo 123787 279827 := bstep (se 1 (by rfl) ⟨209870, by rfl⟩ : syracuseStep 279827 = 419741) B419741
theorem B673471 : Blo 123787 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B280457 : Blo 123787 280457 := bstep (se 2 (by rfl) ⟨105171, by rfl⟩ : syracuseStep 280457 = 210343) B210343
theorem B1624211 : Blo 123787 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B379343 : Blo 123787 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B2017817 : Blo 123787 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B4016951 : Blo 123787 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B969569 : Blo 123787 969569 := bstep (se 2 (by rfl) ⟨363588, by rfl⟩ : syracuseStep 969569 = 727177) B727177
theorem B1362863 : Blo 123787 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B511105 : Blo 123787 511105 := bstep (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) B383329
theorem B412883 : Blo 123787 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B2182625 : Blo 123787 2182625 := bstep (se 2 (by rfl) ⟨818484, by rfl⟩ : syracuseStep 2182625 = 1636969) B1636969
theorem B282131 : Blo 123787 282131 := bstep (se 1 (by rfl) ⟨211598, by rfl⟩ : syracuseStep 282131 = 423197) B423197
theorem B478831 : Blo 123787 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B970487 : Blo 123787 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B20598533 : Blo 123787 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B315839 : Blo 123787 315839 := bstep (se 1 (by rfl) ⟨236879, by rfl⟩ : syracuseStep 315839 = 473759) B473759
theorem B2609633 : Blo 123787 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B5100083 : Blo 123787 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B283193 : Blo 123787 283193 := bstep (se 2 (by rfl) ⟨106197, by rfl⟩ : syracuseStep 283193 = 212395) B212395
theorem B3822329 : Blo 123787 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B316457 : Blo 123787 316457 := bstep (se 2 (by rfl) ⟨118671, by rfl⟩ : syracuseStep 316457 = 237343) B237343
theorem B1528895 : Blo 123787 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B316487 : Blo 123787 316487 := bstep (se 1 (by rfl) ⟨237365, by rfl⟩ : syracuseStep 316487 = 474731) B474731
theorem B1070333 : Blo 123787 1070333 := bstep (se 3 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 1070333 = 401375) B401375
theorem B283913 : Blo 123787 283913 := bstep (se 2 (by rfl) ⟨106467, by rfl⟩ : syracuseStep 283913 = 212935) B212935
theorem B186047 : Blo 123787 186047 := bstep (se 1 (by rfl) ⟨139535, by rfl⟩ : syracuseStep 186047 = 279071) B279071
theorem B186089 : Blo 123787 186089 := bstep (se 2 (by rfl) ⟨69783, by rfl⟩ : syracuseStep 186089 = 139567) B139567
theorem B186095 : Blo 123787 186095 := bstep (se 1 (by rfl) ⟨139571, by rfl⟩ : syracuseStep 186095 = 279143) B279143
theorem B186599 : Blo 123787 186599 := bstep (se 1 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 186599 = 279899) B279899
theorem B284903 : Blo 123787 284903 := bstep (se 1 (by rfl) ⟨213677, by rfl⟩ : syracuseStep 284903 = 427355) B427355
theorem B284921 : Blo 123787 284921 := bstep (se 2 (by rfl) ⟨106845, by rfl⟩ : syracuseStep 284921 = 213691) B213691
theorem B186779 : Blo 123787 186779 := bstep (se 1 (by rfl) ⟨140084, by rfl⟩ : syracuseStep 186779 = 280169) B280169
theorem B285083 : Blo 123787 285083 := bstep (se 1 (by rfl) ⟨213812, by rfl⟩ : syracuseStep 285083 = 427625) B427625
theorem B285191 : Blo 123787 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B285371 : Blo 123787 285371 := bstep (se 1 (by rfl) ⟨214028, by rfl⟩ : syracuseStep 285371 = 428057) B428057
theorem B187175 : Blo 123787 187175 := bstep (se 1 (by rfl) ⟨140381, by rfl⟩ : syracuseStep 187175 = 280763) B280763
theorem B285479 : Blo 123787 285479 := bstep (se 1 (by rfl) ⟨214109, by rfl⟩ : syracuseStep 285479 = 428219) B428219
theorem B383791 : Blo 123787 383791 := bstep (se 1 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 383791 = 575687) B575687
theorem B187199 : Blo 123787 187199 := bstep (se 1 (by rfl) ⟨140399, by rfl⟩ : syracuseStep 187199 = 280799) B280799
theorem B646055 : Blo 123787 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B1301507 : Blo 123787 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B187499 : Blo 123787 187499 := bstep (se 1 (by rfl) ⟨140624, by rfl⟩ : syracuseStep 187499 = 281249) B281249
theorem B384107 : Blo 123787 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B187643 : Blo 123787 187643 := bstep (se 1 (by rfl) ⟨140732, by rfl⟩ : syracuseStep 187643 = 281465) B281465
theorem B187739 : Blo 123787 187739 := bstep (se 1 (by rfl) ⟨140804, by rfl⟩ : syracuseStep 187739 = 281609) B281609
theorem B187769 : Blo 123787 187769 := bstep (se 2 (by rfl) ⟨70413, by rfl⟩ : syracuseStep 187769 = 140827) B140827
theorem B187775 : Blo 123787 187775 := bstep (se 1 (by rfl) ⟨140831, by rfl⟩ : syracuseStep 187775 = 281663) B281663
theorem B286271 : Blo 123787 286271 := bstep (se 1 (by rfl) ⟨214703, by rfl⟩ : syracuseStep 286271 = 429407) B429407
theorem B319049 : Blo 123787 319049 := bstep (se 2 (by rfl) ⟨119643, by rfl⟩ : syracuseStep 319049 = 239287) B239287
theorem B3432223 : Blo 123787 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B188327 : Blo 123787 188327 := bstep (se 1 (by rfl) ⟨141245, by rfl⟩ : syracuseStep 188327 = 282491) B282491
theorem B286631 : Blo 123787 286631 := bstep (se 1 (by rfl) ⟨214973, by rfl⟩ : syracuseStep 286631 = 429947) B429947
theorem B188399 : Blo 123787 188399 := bstep (se 1 (by rfl) ⟨141299, by rfl⟩ : syracuseStep 188399 = 282599) B282599
theorem B188519 : Blo 123787 188519 := bstep (se 1 (by rfl) ⟨141389, by rfl⟩ : syracuseStep 188519 = 282779) B282779
theorem B188651 : Blo 123787 188651 := bstep (se 1 (by rfl) ⟨141488, by rfl⟩ : syracuseStep 188651 = 282977) B282977
theorem B745757 : Blo 123787 745757 := bstep (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) B279659
theorem B188711 : Blo 123787 188711 := bstep (se 1 (by rfl) ⟨141533, by rfl⟩ : syracuseStep 188711 = 283067) B283067
theorem B352927 : Blo 123787 352927 := bstep (se 1 (by rfl) ⟨264695, by rfl⟩ : syracuseStep 352927 = 529391) B529391
theorem B1434307 : Blo 123787 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B189161 : Blo 123787 189161 := bstep (se 2 (by rfl) ⟨70935, by rfl⟩ : syracuseStep 189161 = 141871) B141871
theorem B320233 : Blo 123787 320233 := bstep (se 2 (by rfl) ⟨120087, by rfl⟩ : syracuseStep 320233 = 240175) B240175
theorem B123807 : Blo 123787 123807 := bstep (se 1 (by rfl) ⟨92855, by rfl⟩ : syracuseStep 123807 = 185711) B185711
theorem B123887 : Blo 123787 123887 := bstep (se 1 (by rfl) ⟨92915, by rfl⟩ : syracuseStep 123887 = 185831) B185831
theorem B1434671 : Blo 123787 1434671 := bstep (se 1 (by rfl) ⟨1076003, by rfl⟩ : syracuseStep 1434671 = 2152007) B2152007
theorem B123995 : Blo 123787 123995 := bstep (se 1 (by rfl) ⟨92996, by rfl⟩ : syracuseStep 123995 = 185993) B185993
theorem B124007 : Blo 123787 124007 := bstep (se 1 (by rfl) ⟨93005, by rfl⟩ : syracuseStep 124007 = 186011) B186011
theorem B189551 : Blo 123787 189551 := bstep (se 1 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 189551 = 284327) B284327
theorem B124135 : Blo 123787 124135 := bstep (se 1 (by rfl) ⟨93101, by rfl⟩ : syracuseStep 124135 = 186203) B186203
theorem B189671 : Blo 123787 189671 := bstep (se 1 (by rfl) ⟨142253, by rfl⟩ : syracuseStep 189671 = 284507) B284507
theorem B156907 : Blo 123787 156907 := bstep (se 1 (by rfl) ⟨117680, by rfl⟩ : syracuseStep 156907 = 235361) B235361
theorem B189737 : Blo 123787 189737 := bstep (se 2 (by rfl) ⟨71151, by rfl⟩ : syracuseStep 189737 = 142303) B142303
theorem B124391 : Blo 123787 124391 := bstep (se 1 (by rfl) ⟨93293, by rfl⟩ : syracuseStep 124391 = 186587) B186587
theorem B190007 : Blo 123787 190007 := bstep (se 1 (by rfl) ⟨142505, by rfl⟩ : syracuseStep 190007 = 285011) B285011
theorem B124571 : Blo 123787 124571 := bstep (se 1 (by rfl) ⟨93428, by rfl⟩ : syracuseStep 124571 = 186857) B186857
theorem B157339 : Blo 123787 157339 := bstep (se 1 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 157339 = 236009) B236009
theorem B288427 : Blo 123787 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B190331 : Blo 123787 190331 := bstep (se 1 (by rfl) ⟨142748, by rfl⟩ : syracuseStep 190331 = 285497) B285497
theorem B124831 : Blo 123787 124831 := bstep (se 1 (by rfl) ⟨93623, by rfl⟩ : syracuseStep 124831 = 187247) B187247
theorem B190367 : Blo 123787 190367 := bstep (se 1 (by rfl) ⟨142775, by rfl⟩ : syracuseStep 190367 = 285551) B285551
theorem B124839 : Blo 123787 124839 := bstep (se 1 (by rfl) ⟨93629, by rfl⟩ : syracuseStep 124839 = 187259) B187259
theorem B157727 : Blo 123787 157727 := bstep (se 1 (by rfl) ⟨118295, by rfl⟩ : syracuseStep 157727 = 236591) B236591
theorem B190601 : Blo 123787 190601 := bstep (se 2 (by rfl) ⟨71475, by rfl⟩ : syracuseStep 190601 = 142951) B142951
theorem B321691 : Blo 123787 321691 := bstep (se 1 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 321691 = 482537) B482537
theorem B682219 : Blo 123787 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B190751 : Blo 123787 190751 := bstep (se 1 (by rfl) ⟨143063, by rfl⟩ : syracuseStep 190751 = 286127) B286127
theorem B190799 : Blo 123787 190799 := bstep (se 1 (by rfl) ⟨143099, by rfl⟩ : syracuseStep 190799 = 286199) B286199
theorem B190889 : Blo 123787 190889 := bstep (se 2 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 190889 = 143167) B143167
theorem B125415 : Blo 123787 125415 := bstep (se 1 (by rfl) ⟨94061, by rfl⟩ : syracuseStep 125415 = 188123) B188123
theorem B125595 : Blo 123787 125595 := bstep (se 1 (by rfl) ⟨94196, by rfl⟩ : syracuseStep 125595 = 188393) B188393
theorem B191273 : Blo 123787 191273 := bstep (se 2 (by rfl) ⟨71727, by rfl⟩ : syracuseStep 191273 = 143455) B143455
theorem B191483 : Blo 123787 191483 := bstep (se 1 (by rfl) ⟨143612, by rfl⟩ : syracuseStep 191483 = 287225) B287225
theorem B650273 : Blo 123787 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B191543 : Blo 123787 191543 := bstep (se 1 (by rfl) ⟨143657, by rfl⟩ : syracuseStep 191543 = 287315) B287315
theorem B126063 : Blo 123787 126063 := bstep (se 1 (by rfl) ⟨94547, by rfl⟩ : syracuseStep 126063 = 189095) B189095
theorem B191663 : Blo 123787 191663 := bstep (se 1 (by rfl) ⟨143747, by rfl⟩ : syracuseStep 191663 = 287495) B287495
theorem B126143 : Blo 123787 126143 := bstep (se 1 (by rfl) ⟨94607, by rfl⟩ : syracuseStep 126143 = 189215) B189215
theorem B126159 : Blo 123787 126159 := bstep (se 1 (by rfl) ⟨94619, by rfl⟩ : syracuseStep 126159 = 189239) B189239
theorem B322825 : Blo 123787 322825 := bstep (se 2 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 322825 = 242119) B242119
theorem B126279 : Blo 123787 126279 := bstep (se 1 (by rfl) ⟨94709, by rfl⟩ : syracuseStep 126279 = 189419) B189419
theorem B2485633 : Blo 123787 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B945755 : Blo 123787 945755 := bstep (se 1 (by rfl) ⟨709316, by rfl⟩ : syracuseStep 945755 = 1418633) B1418633
theorem B14282477 : Blo 123787 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B421847 : Blo 123787 421847 := bstep (se 1 (by rfl) ⟨316385, by rfl⟩ : syracuseStep 421847 = 632771) B632771
theorem B127007 : Blo 123787 127007 := bstep (se 1 (by rfl) ⟨95255, by rfl⟩ : syracuseStep 127007 = 190511) B190511
theorem B127183 : Blo 123787 127183 := bstep (se 1 (by rfl) ⟨95387, by rfl⟩ : syracuseStep 127183 = 190775) B190775
theorem B127303 : Blo 123787 127303 := bstep (se 1 (by rfl) ⟨95477, by rfl⟩ : syracuseStep 127303 = 190955) B190955
theorem B160475 : Blo 123787 160475 := bstep (se 1 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 160475 = 240713) B240713
theorem B127771 : Blo 123787 127771 := bstep (se 1 (by rfl) ⟨95828, by rfl⟩ : syracuseStep 127771 = 191657) B191657
theorem B423305 : Blo 123787 423305 := bstep (se 2 (by rfl) ⟨158739, by rfl⟩ : syracuseStep 423305 = 317479) B317479
theorem B357871 : Blo 123787 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B816743 : Blo 123787 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B2751245 : Blo 123787 2751245 := bstep (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) B1031717
theorem B424871 : Blo 123787 424871 := bstep (se 1 (by rfl) ⟨318653, by rfl⟩ : syracuseStep 424871 = 637307) B637307
theorem B359387 : Blo 123787 359387 := bstep (se 1 (by rfl) ⟨269540, by rfl⟩ : syracuseStep 359387 = 539081) B539081
theorem B359579 : Blo 123787 359579 := bstep (se 1 (by rfl) ⟨269684, by rfl⟩ : syracuseStep 359579 = 539369) B539369
theorem B12156713 : Blo 123787 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B360571 : Blo 123787 360571 := bstep (se 1 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 360571 = 540857) B540857
theorem B1835135 : Blo 123787 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B1441961 : Blo 123787 1441961 := bstep (se 2 (by rfl) ⟨540735, by rfl⟩ : syracuseStep 1441961 = 1081471) B1081471
theorem B426599 : Blo 123787 426599 := bstep (se 1 (by rfl) ⟨319949, by rfl⟩ : syracuseStep 426599 = 639899) B639899
theorem B426977 : Blo 123787 426977 := bstep (se 2 (by rfl) ⟨160116, by rfl⟩ : syracuseStep 426977 = 320233) B320233
theorem B4097141 : Blo 123787 4097141 := bstep (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) B384107
theorem B1082807 : Blo 123787 1082807 := bstep (se 1 (by rfl) ⟨812105, by rfl⟩ : syracuseStep 1082807 = 1624211) B1624211
theorem B1345211 : Blo 123787 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B427933 : Blo 123787 427933 := bstep (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) B160475
theorem B10192877 : Blo 123787 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B198875 : Blo 123787 198875 := bstep (se 1 (by rfl) ⟨149156, by rfl⟩ : syracuseStep 198875 = 298313) B298313
theorem B13732355 : Blo 123787 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B4197203 : Blo 123787 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B428921 : Blo 123787 428921 := bstep (se 2 (by rfl) ⟨160845, by rfl⟩ : syracuseStep 428921 = 321691) B321691
theorem B1739755 : Blo 123787 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B265447 : Blo 123787 265447 := bstep (se 1 (by rfl) ⟨199085, by rfl⟩ : syracuseStep 265447 = 398171) B398171
theorem B1019263 : Blo 123787 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B266465 : Blo 123787 266465 := bstep (se 2 (by rfl) ⟨99924, by rfl⟩ : syracuseStep 266465 = 199849) B199849
theorem B430433 : Blo 123787 430433 := bstep (se 2 (by rfl) ⟨161412, by rfl⟩ : syracuseStep 430433 = 322825) B322825
theorem B3314177 : Blo 123787 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B430703 : Blo 123787 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B497171 : Blo 123787 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B956447 : Blo 123787 956447 := bstep (se 1 (by rfl) ⟨717335, by rfl⟩ : syracuseStep 956447 = 1434671) B1434671
theorem B1841363 : Blo 123787 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B629693 : Blo 123787 629693 := bstep (se 3 (by rfl) ⟨118067, by rfl⟩ : syracuseStep 629693 = 236135) B236135
theorem B269651 : Blo 123787 269651 := bstep (se 1 (by rfl) ⟨202238, by rfl⟩ : syracuseStep 269651 = 404477) B404477
theorem B237161 : Blo 123787 237161 := bstep (se 2 (by rfl) ⟨88935, by rfl⟩ : syracuseStep 237161 = 177871) B177871
theorem B728767 : Blo 123787 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B630503 : Blo 123787 630503 := bstep (se 1 (by rfl) ⟨472877, by rfl⟩ : syracuseStep 630503 = 945755) B945755
theorem B958877 : Blo 123787 958877 := bstep (se 3 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 958877 = 359579) B359579
theorem B140071 : Blo 123787 140071 := bstep (se 1 (by rfl) ⟨105053, by rfl⟩ : syracuseStep 140071 = 210107) B210107
theorem B271343 : Blo 123787 271343 := bstep (se 1 (by rfl) ⟨203507, by rfl⟩ : syracuseStep 271343 = 407015) B407015
theorem B795703 : Blo 123787 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B402785 : Blo 123787 402785 := bstep (se 2 (by rfl) ⟨151044, by rfl⟩ : syracuseStep 402785 = 302089) B302089
theorem B141223 : Blo 123787 141223 := bstep (se 1 (by rfl) ⟨105917, by rfl⟩ : syracuseStep 141223 = 211835) B211835
theorem B927679 : Blo 123787 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B239591 : Blo 123787 239591 := bstep (se 1 (by rfl) ⟨179693, by rfl⟩ : syracuseStep 239591 = 359387) B359387
theorem B272521 : Blo 123787 272521 := bstep (se 2 (by rfl) ⟨102195, by rfl⟩ : syracuseStep 272521 = 204391) B204391
theorem B8104475 : Blo 123787 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B535405 : Blo 123787 535405 := bstep (se 3 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 535405 = 200777) B200777
theorem B1191095 : Blo 123787 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B961793 : Blo 123787 961793 := bstep (se 2 (by rfl) ⟨360672, by rfl⟩ : syracuseStep 961793 = 721345) B721345
theorem B1715671 : Blo 123787 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B470569 : Blo 123787 470569 := bstep (se 2 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 470569 = 352927) B352927
theorem B1912409 : Blo 123787 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B241967 : Blo 123787 241967 := bstep (se 1 (by rfl) ⟨181475, by rfl⟩ : syracuseStep 241967 = 362951) B362951
theorem B209209 : Blo 123787 209209 := bstep (se 2 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 209209 = 156907) B156907
theorem B275255 : Blo 123787 275255 := bstep (se 1 (by rfl) ⟨206441, by rfl⟩ : syracuseStep 275255 = 412883) B412883
theorem B209785 : Blo 123787 209785 := bstep (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) B157339
theorem B897961 : Blo 123787 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B1455083 : Blo 123787 1455083 := bstep (se 1 (by rfl) ⟨1091312, by rfl⟩ : syracuseStep 1455083 = 2182625) B2182625
theorem B636335 : Blo 123787 636335 := bstep (se 1 (by rfl) ⟨477251, by rfl⟩ : syracuseStep 636335 = 954503) B954503
theorem B1979873 : Blo 123787 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B210559 : Blo 123787 210559 := bstep (se 1 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 210559 = 315839) B315839
theorem B1095407 : Blo 123787 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B505607 : Blo 123787 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B210971 : Blo 123787 210971 := bstep (se 1 (by rfl) ⟨158228, by rfl⟩ : syracuseStep 210971 = 316457) B316457
theorem B210991 : Blo 123787 210991 := bstep (se 1 (by rfl) ⟨158243, by rfl⟩ : syracuseStep 210991 = 316487) B316487
theorem B867671 : Blo 123787 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B638441 : Blo 123787 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B212699 : Blo 123787 212699 := bstep (se 1 (by rfl) ⟨159524, by rfl⟩ : syracuseStep 212699 = 319049) B319049
theorem B901307 : Blo 123787 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B475901 : Blo 123787 475901 := bstep (se 3 (by rfl) ⟨89231, by rfl⟩ : syracuseStep 475901 = 178463) B178463
theorem B967625 : Blo 123787 967625 := bstep (se 2 (by rfl) ⟨362859, by rfl⟩ : syracuseStep 967625 = 725719) B725719
theorem B279593 : Blo 123787 279593 := bstep (se 2 (by rfl) ⟨104847, by rfl⟩ : syracuseStep 279593 = 209695) B209695
theorem B968111 : Blo 123787 968111 := bstep (se 1 (by rfl) ⟨726083, by rfl⟩ : syracuseStep 968111 = 1452167) B1452167
theorem B477161 : Blo 123787 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B9521651 : Blo 123787 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B281231 : Blo 123787 281231 := bstep (se 1 (by rfl) ⟨210923, by rfl⟩ : syracuseStep 281231 = 421847) B421847
theorem B3459833 : Blo 123787 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B1166663 : Blo 123787 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B282203 : Blo 123787 282203 := bstep (se 1 (by rfl) ⟨211652, by rfl⟩ : syracuseStep 282203 = 423305) B423305
theorem B511721 : Blo 123787 511721 := bstep (se 2 (by rfl) ⟨191895, by rfl⟩ : syracuseStep 511721 = 383791) B383791
theorem B544495 : Blo 123787 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B807209 : Blo 123787 807209 := bstep (se 2 (by rfl) ⟨302703, by rfl⟩ : syracuseStep 807209 = 605407) B605407
theorem B283247 : Blo 123787 283247 := bstep (se 1 (by rfl) ⟨212435, by rfl⟩ : syracuseStep 283247 = 424871) B424871
theorem B4576297 : Blo 123787 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B709955 : Blo 123787 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B546383 : Blo 123787 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B481049 : Blo 123787 481049 := bstep (se 2 (by rfl) ⟨180393, by rfl⟩ : syracuseStep 481049 = 360787) B360787
theorem B186479 : Blo 123787 186479 := bstep (se 1 (by rfl) ⟨139859, by rfl⟩ : syracuseStep 186479 = 279719) B279719
theorem B186551 : Blo 123787 186551 := bstep (se 1 (by rfl) ⟨139913, by rfl⟩ : syracuseStep 186551 = 279827) B279827
theorem B186971 : Blo 123787 186971 := bstep (se 1 (by rfl) ⟨140228, by rfl⟩ : syracuseStep 186971 = 280457) B280457
theorem B613079 : Blo 123787 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B252895 : Blo 123787 252895 := bstep (se 1 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 252895 = 379343) B379343
theorem B285803 : Blo 123787 285803 := bstep (se 1 (by rfl) ⟨214352, by rfl⟩ : syracuseStep 285803 = 428705) B428705
theorem B2677967 : Blo 123787 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B646379 : Blo 123787 646379 := bstep (se 1 (by rfl) ⟨484784, by rfl⟩ : syracuseStep 646379 = 969569) B969569
theorem B384569 : Blo 123787 384569 := bstep (se 2 (by rfl) ⟨144213, by rfl⟩ : syracuseStep 384569 = 288427) B288427
theorem B188087 : Blo 123787 188087 := bstep (se 1 (by rfl) ⟨141065, by rfl⟩ : syracuseStep 188087 = 282131) B282131
theorem B319241 : Blo 123787 319241 := bstep (se 2 (by rfl) ⟨119715, by rfl⟩ : syracuseStep 319241 = 239431) B239431
theorem B646991 : Blo 123787 646991 := bstep (se 1 (by rfl) ⟨485243, by rfl⟩ : syracuseStep 646991 = 970487) B970487
theorem B418067 : Blo 123787 418067 := bstep (se 1 (by rfl) ⟨313550, by rfl⟩ : syracuseStep 418067 = 627101) B627101
theorem B909625 : Blo 123787 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B3400055 : Blo 123787 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B188795 : Blo 123787 188795 := bstep (se 1 (by rfl) ⟨141596, by rfl⟩ : syracuseStep 188795 = 283193) B283193
theorem B188969 : Blo 123787 188969 := bstep (se 2 (by rfl) ⟨70863, by rfl⟩ : syracuseStep 188969 = 141727) B141727
theorem B484177 : Blo 123787 484177 := bstep (se 2 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 484177 = 363133) B363133
theorem B713555 : Blo 123787 713555 := bstep (se 1 (by rfl) ⟨535166, by rfl⟩ : syracuseStep 713555 = 1070333) B1070333
theorem B189275 : Blo 123787 189275 := bstep (se 1 (by rfl) ⟨141956, by rfl⟩ : syracuseStep 189275 = 283913) B283913
theorem B124031 : Blo 123787 124031 := bstep (se 1 (by rfl) ⟨93023, by rfl⟩ : syracuseStep 124031 = 186047) B186047
theorem B124059 : Blo 123787 124059 := bstep (se 1 (by rfl) ⟨93044, by rfl⟩ : syracuseStep 124059 = 186089) B186089
theorem B124063 : Blo 123787 124063 := bstep (se 1 (by rfl) ⟨93047, by rfl⟩ : syracuseStep 124063 = 186095) B186095
theorem B124399 : Blo 123787 124399 := bstep (se 1 (by rfl) ⟨93299, by rfl⟩ : syracuseStep 124399 = 186599) B186599
theorem B189935 : Blo 123787 189935 := bstep (se 1 (by rfl) ⟨142451, by rfl⟩ : syracuseStep 189935 = 284903) B284903
theorem B189947 : Blo 123787 189947 := bstep (se 1 (by rfl) ⟨142460, by rfl⟩ : syracuseStep 189947 = 284921) B284921
theorem B681473 : Blo 123787 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B1074707 : Blo 123787 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B484937 : Blo 123787 484937 := bstep (se 2 (by rfl) ⟨181851, by rfl⟩ : syracuseStep 484937 = 363703) B363703
theorem B124519 : Blo 123787 124519 := bstep (se 1 (by rfl) ⟨93389, by rfl⟩ : syracuseStep 124519 = 186779) B186779
theorem B190055 : Blo 123787 190055 := bstep (se 1 (by rfl) ⟨142541, by rfl⟩ : syracuseStep 190055 = 285083) B285083
theorem B812717 : Blo 123787 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B190127 : Blo 123787 190127 := bstep (se 1 (by rfl) ⟨142595, by rfl⟩ : syracuseStep 190127 = 285191) B285191
theorem B190247 : Blo 123787 190247 := bstep (se 1 (by rfl) ⟨142685, by rfl⟩ : syracuseStep 190247 = 285371) B285371
theorem B124783 : Blo 123787 124783 := bstep (se 1 (by rfl) ⟨93587, by rfl⟩ : syracuseStep 124783 = 187175) B187175
theorem B190319 : Blo 123787 190319 := bstep (se 1 (by rfl) ⟨142739, by rfl⟩ : syracuseStep 190319 = 285479) B285479
theorem B124799 : Blo 123787 124799 := bstep (se 1 (by rfl) ⟨93599, by rfl⟩ : syracuseStep 124799 = 187199) B187199
theorem B190505 : Blo 123787 190505 := bstep (se 2 (by rfl) ⟨71439, by rfl⟩ : syracuseStep 190505 = 142879) B142879
theorem B124999 : Blo 123787 124999 := bstep (se 1 (by rfl) ⟨93749, by rfl⟩ : syracuseStep 124999 = 187499) B187499
theorem B125095 : Blo 123787 125095 := bstep (se 1 (by rfl) ⟨93821, by rfl⟩ : syracuseStep 125095 = 187643) B187643
theorem B551099 : Blo 123787 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B125159 : Blo 123787 125159 := bstep (se 1 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 125159 = 187739) B187739
theorem B125179 : Blo 123787 125179 := bstep (se 1 (by rfl) ⟨93884, by rfl⟩ : syracuseStep 125179 = 187769) B187769
theorem B125183 : Blo 123787 125183 := bstep (se 1 (by rfl) ⟨93887, by rfl⟩ : syracuseStep 125183 = 187775) B187775
theorem B190847 : Blo 123787 190847 := bstep (se 1 (by rfl) ⟨143135, by rfl⟩ : syracuseStep 190847 = 286271) B286271
theorem B125551 : Blo 123787 125551 := bstep (se 1 (by rfl) ⟨94163, by rfl⟩ : syracuseStep 125551 = 188327) B188327
theorem B191087 : Blo 123787 191087 := bstep (se 1 (by rfl) ⟨143315, by rfl⟩ : syracuseStep 191087 = 286631) B286631
theorem B125599 : Blo 123787 125599 := bstep (se 1 (by rfl) ⟨94199, by rfl⟩ : syracuseStep 125599 = 188399) B188399
theorem B158375 : Blo 123787 158375 := bstep (se 1 (by rfl) ⟨118781, by rfl⟩ : syracuseStep 158375 = 237563) B237563
theorem B125679 : Blo 123787 125679 := bstep (se 1 (by rfl) ⟨94259, by rfl⟩ : syracuseStep 125679 = 188519) B188519
theorem B420605 : Blo 123787 420605 := bstep (se 3 (by rfl) ⟨78863, by rfl⟩ : syracuseStep 420605 = 157727) B157727
theorem B125767 : Blo 123787 125767 := bstep (se 1 (by rfl) ⟨94325, by rfl⟩ : syracuseStep 125767 = 188651) B188651
theorem B125807 : Blo 123787 125807 := bstep (se 1 (by rfl) ⟨94355, by rfl⟩ : syracuseStep 125807 = 188711) B188711
theorem B420767 : Blo 123787 420767 := bstep (se 1 (by rfl) ⟨315575, by rfl⟩ : syracuseStep 420767 = 631151) B631151
theorem B126107 : Blo 123787 126107 := bstep (se 1 (by rfl) ⟨94580, by rfl⟩ : syracuseStep 126107 = 189161) B189161
theorem B159023 : Blo 123787 159023 := bstep (se 1 (by rfl) ⟨119267, by rfl⟩ : syracuseStep 159023 = 238535) B238535
theorem B126367 : Blo 123787 126367 := bstep (se 1 (by rfl) ⟨94775, by rfl⟩ : syracuseStep 126367 = 189551) B189551
theorem B126447 : Blo 123787 126447 := bstep (se 1 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 126447 = 189671) B189671
theorem B126491 : Blo 123787 126491 := bstep (se 1 (by rfl) ⟨94868, by rfl⟩ : syracuseStep 126491 = 189737) B189737
theorem B126671 : Blo 123787 126671 := bstep (se 1 (by rfl) ⟨95003, by rfl⟩ : syracuseStep 126671 = 190007) B190007
theorem B126887 : Blo 123787 126887 := bstep (se 1 (by rfl) ⟨95165, by rfl⟩ : syracuseStep 126887 = 190331) B190331
theorem B126911 : Blo 123787 126911 := bstep (se 1 (by rfl) ⟨95183, by rfl⟩ : syracuseStep 126911 = 190367) B190367
theorem B127067 : Blo 123787 127067 := bstep (se 1 (by rfl) ⟨95300, by rfl⟩ : syracuseStep 127067 = 190601) B190601
theorem B422063 : Blo 123787 422063 := bstep (se 1 (by rfl) ⟨316547, by rfl⟩ : syracuseStep 422063 = 633095) B633095
theorem B127167 : Blo 123787 127167 := bstep (se 1 (by rfl) ⟨95375, by rfl⟩ : syracuseStep 127167 = 190751) B190751
theorem B127199 : Blo 123787 127199 := bstep (se 1 (by rfl) ⟨95399, by rfl⟩ : syracuseStep 127199 = 190799) B190799
theorem B127259 : Blo 123787 127259 := bstep (se 1 (by rfl) ⟨95444, by rfl⟩ : syracuseStep 127259 = 190889) B190889
theorem B127515 : Blo 123787 127515 := bstep (se 1 (by rfl) ⟨95636, by rfl⟩ : syracuseStep 127515 = 191273) B191273
theorem B127655 : Blo 123787 127655 := bstep (se 1 (by rfl) ⟨95741, by rfl⟩ : syracuseStep 127655 = 191483) B191483
theorem B127695 : Blo 123787 127695 := bstep (se 1 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 127695 = 191543) B191543
theorem B127775 : Blo 123787 127775 := bstep (se 1 (by rfl) ⟨95831, by rfl⟩ : syracuseStep 127775 = 191663) B191663
theorem B422711 : Blo 123787 422711 := bstep (se 1 (by rfl) ⟨317033, by rfl⟩ : syracuseStep 422711 = 634067) B634067
theorem B1209275 : Blo 123787 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B226351 : Blo 123787 226351 := bstep (se 1 (by rfl) ⟨169763, by rfl⟩ : syracuseStep 226351 = 339527) B339527
theorem B3175523 : Blo 123787 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B3634301 : Blo 123787 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B1734061 : Blo 123787 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B358121 : Blo 123787 358121 := bstep (se 2 (by rfl) ⟨134295, by rfl⟩ : syracuseStep 358121 = 268591) B268591
theorem B423791 : Blo 123787 423791 := bstep (se 1 (by rfl) ⟨317843, by rfl⟩ : syracuseStep 423791 = 635687) B635687
theorem B424007 : Blo 123787 424007 := bstep (se 1 (by rfl) ⟨318005, by rfl⟩ : syracuseStep 424007 = 636011) B636011
theorem B28146653 : Blo 123787 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B1834163 : Blo 123787 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B982529 : Blo 123787 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B1212833 : Blo 123787 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B721871 : Blo 123787 721871 := bstep (se 1 (by rfl) ⟨541403, by rfl⟩ : syracuseStep 721871 = 1082807) B1082807
theorem B363361 : Blo 123787 363361 := bstep (se 2 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 363361 = 272521) B272521
theorem B331447 : Blo 123787 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B167689 : Blo 123787 167689 := bstep (se 2 (by rfl) ⟨62883, by rfl⟩ : syracuseStep 167689 = 125767) B125767
theorem B954989 : Blo 123787 954989 := bstep (se 3 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 954989 = 358121) B358121
theorem B627425 : Blo 123787 627425 := bstep (se 2 (by rfl) ⟨235284, by rfl⟩ : syracuseStep 627425 = 470569) B470569
theorem B430919 : Blo 123787 430919 := bstep (se 1 (by rfl) ⟨323189, by rfl⟩ : syracuseStep 430919 = 646379) B646379
theorem B725993 : Blo 123787 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B431327 : Blo 123787 431327 := bstep (se 1 (by rfl) ⟨323495, by rfl⟩ : syracuseStep 431327 = 646991) B646991
theorem B2266703 : Blo 123787 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B530333 : Blo 123787 530333 := bstep (se 3 (by rfl) ⟨99437, by rfl⟩ : syracuseStep 530333 = 198875) B198875
theorem B268523 : Blo 123787 268523 := bstep (se 1 (by rfl) ⟨201392, by rfl⟩ : syracuseStep 268523 = 402785) B402785
theorem B1415717 : Blo 123787 1415717 := bstep (se 4 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 1415717 = 265447) B265447
theorem B6101729 : Blo 123787 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B301801 : Blo 123787 301801 := bstep (se 2 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 301801 = 226351) B226351
theorem B367399 : Blo 123787 367399 := bstep (se 1 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 367399 = 551099) B551099
theorem B794063 : Blo 123787 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B1319915 : Blo 123787 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B730271 : Blo 123787 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B337193 : Blo 123787 337193 := bstep (se 2 (by rfl) ⟨126447, by rfl⟩ : syracuseStep 337193 = 252895) B252895
theorem B140647 : Blo 123787 140647 := bstep (se 1 (by rfl) ⟨105485, by rfl⟩ : syracuseStep 140647 = 210971) B210971
theorem B1222775 : Blo 123787 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B141799 : Blo 123787 141799 := bstep (se 1 (by rfl) ⟨106349, by rfl⟩ : syracuseStep 141799 = 212699) B212699
theorem B1223423 : Blo 123787 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B961307 : Blo 123787 961307 := bstep (se 1 (by rfl) ⟨720980, by rfl⟩ : syracuseStep 961307 = 1441961) B1441961
theorem B600871 : Blo 123787 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B2731427 : Blo 123787 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B896807 : Blo 123787 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B6795251 : Blo 123787 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B1060937 : Blo 123787 1060937 := bstep (se 2 (by rfl) ⟨397851, by rfl⟩ : syracuseStep 1060937 = 795703) B795703
theorem B9154903 : Blo 123787 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B2306555 : Blo 123787 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B2798135 : Blo 123787 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B341147 : Blo 123787 341147 := bstep (se 1 (by rfl) ⟨255860, by rfl⟩ : syracuseStep 341147 = 511721) B511721
theorem B570577 : Blo 123787 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B177643 : Blo 123787 177643 := bstep (se 1 (by rfl) ⟨133232, by rfl⟩ : syracuseStep 177643 = 266465) B266465
theorem B538139 : Blo 123787 538139 := bstep (se 1 (by rfl) ⟨403604, by rfl⟩ : syracuseStep 538139 = 807209) B807209
theorem B2209451 : Blo 123787 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B473303 : Blo 123787 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B1817261 : Blo 123787 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B637631 : Blo 123787 637631 := bstep (se 1 (by rfl) ⟨478223, by rfl⟩ : syracuseStep 637631 = 956447) B956447
theorem B1227575 : Blo 123787 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B1457021 : Blo 123787 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B408719 : Blo 123787 408719 := bstep (se 1 (by rfl) ⟨306539, by rfl⟩ : syracuseStep 408719 = 613079) B613079
theorem B1359017 : Blo 123787 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B1785311 : Blo 123787 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B179767 : Blo 123787 179767 := bstep (se 1 (by rfl) ⟨134825, by rfl⟩ : syracuseStep 179767 = 269651) B269651
theorem B212827 : Blo 123787 212827 := bstep (se 1 (by rfl) ⟨159620, by rfl⟩ : syracuseStep 212827 = 319241) B319241
theorem B278711 : Blo 123787 278711 := bstep (se 1 (by rfl) ⟨209033, by rfl⟩ : syracuseStep 278711 = 418067) B418067
theorem B639251 : Blo 123787 639251 := bstep (se 1 (by rfl) ⟨479438, by rfl⟩ : syracuseStep 639251 = 958877) B958877
theorem B278945 : Blo 123787 278945 := bstep (se 2 (by rfl) ⟨104604, by rfl⟩ : syracuseStep 278945 = 209209) B209209
theorem B475703 : Blo 123787 475703 := bstep (se 1 (by rfl) ⟨356777, by rfl⟩ : syracuseStep 475703 = 713555) B713555
theorem B180895 : Blo 123787 180895 := bstep (se 1 (by rfl) ⟨135671, by rfl⟩ : syracuseStep 180895 = 271343) B271343
theorem B541811 : Blo 123787 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B279713 : Blo 123787 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B1197281 : Blo 123787 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B280403 : Blo 123787 280403 := bstep (se 1 (by rfl) ⟨210302, by rfl⟩ : syracuseStep 280403 = 420605) B420605
theorem B2312081 : Blo 123787 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B280511 : Blo 123787 280511 := bstep (se 1 (by rfl) ⟨210383, by rfl⟩ : syracuseStep 280511 = 420767) B420767
theorem B280745 : Blo 123787 280745 := bstep (se 2 (by rfl) ⟨105279, by rfl⟩ : syracuseStep 280745 = 210559) B210559
theorem B641195 : Blo 123787 641195 := bstep (se 1 (by rfl) ⟨480896, by rfl⟩ : syracuseStep 641195 = 961793) B961793
theorem B281321 : Blo 123787 281321 := bstep (se 2 (by rfl) ⟨105495, by rfl⟩ : syracuseStep 281321 = 210991) B210991
theorem B5393141 : Blo 123787 5393141 := bstep (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) B505607
theorem B281375 : Blo 123787 281375 := bstep (se 1 (by rfl) ⟨211031, by rfl⟩ : syracuseStep 281375 = 422063) B422063
theorem B281807 : Blo 123787 281807 := bstep (se 1 (by rfl) ⟨211355, by rfl⟩ : syracuseStep 281807 = 422711) B422711
theorem B183503 : Blo 123787 183503 := bstep (se 1 (by rfl) ⟨137627, by rfl⟩ : syracuseStep 183503 = 275255) B275255
theorem B806183 : Blo 123787 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B970055 : Blo 123787 970055 := bstep (se 1 (by rfl) ⟨727541, by rfl⟩ : syracuseStep 970055 = 1455083) B1455083
theorem B2117015 : Blo 123787 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B282527 : Blo 123787 282527 := bstep (se 1 (by rfl) ⟨211895, by rfl⟩ : syracuseStep 282527 = 423791) B423791
theorem B282671 : Blo 123787 282671 := bstep (se 1 (by rfl) ⟨212003, by rfl⟩ : syracuseStep 282671 = 424007) B424007
theorem B18764435 : Blo 123787 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B578447 : Blo 123787 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B971689 : Blo 123787 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B480761 : Blo 123787 480761 := bstep (se 2 (by rfl) ⟨180285, by rfl⟩ : syracuseStep 480761 = 360571) B360571
theorem B284399 : Blo 123787 284399 := bstep (se 1 (by rfl) ⟨213299, by rfl⟩ : syracuseStep 284399 = 426599) B426599
theorem B317267 : Blo 123787 317267 := bstep (se 1 (by rfl) ⟨237950, by rfl⟩ : syracuseStep 317267 = 475901) B475901
theorem B645083 : Blo 123787 645083 := bstep (se 1 (by rfl) ⟨483812, by rfl⟩ : syracuseStep 645083 = 967625) B967625
theorem B284651 : Blo 123787 284651 := bstep (se 1 (by rfl) ⟨213488, by rfl⟩ : syracuseStep 284651 = 426977) B426977
theorem B186395 : Blo 123787 186395 := bstep (se 1 (by rfl) ⟨139796, by rfl⟩ : syracuseStep 186395 = 279593) B279593
theorem B645245 : Blo 123787 645245 := bstep (se 3 (by rfl) ⟨120983, by rfl⟩ : syracuseStep 645245 = 241967) B241967
theorem B645407 : Blo 123787 645407 := bstep (se 1 (by rfl) ⟨484055, by rfl⟩ : syracuseStep 645407 = 968111) B968111
theorem B186761 : Blo 123787 186761 := bstep (se 2 (by rfl) ⟨70035, by rfl⟩ : syracuseStep 186761 = 140071) B140071
theorem B645569 : Blo 123787 645569 := bstep (se 2 (by rfl) ⟨242088, by rfl⟩ : syracuseStep 645569 = 484177) B484177
theorem B318107 : Blo 123787 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B6347767 : Blo 123787 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B187487 : Blo 123787 187487 := bstep (se 1 (by rfl) ⟨140615, by rfl⟩ : syracuseStep 187487 = 281231) B281231
theorem B285947 : Blo 123787 285947 := bstep (se 1 (by rfl) ⟨214460, by rfl⟩ : syracuseStep 285947 = 428921) B428921
theorem B777775 : Blo 123787 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B188135 : Blo 123787 188135 := bstep (se 1 (by rfl) ⟨141101, by rfl⟩ : syracuseStep 188135 = 282203) B282203
theorem B188297 : Blo 123787 188297 := bstep (se 2 (by rfl) ⟨70611, by rfl⟩ : syracuseStep 188297 = 141223) B141223
theorem B1236905 : Blo 123787 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B286955 : Blo 123787 286955 := bstep (se 1 (by rfl) ⟨215216, by rfl⟩ : syracuseStep 286955 = 430433) B430433
theorem B9691469 : Blo 123787 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B188831 : Blo 123787 188831 := bstep (se 1 (by rfl) ⟨141623, by rfl⟩ : syracuseStep 188831 = 283247) B283247
theorem B287135 : Blo 123787 287135 := bstep (se 1 (by rfl) ⟨215351, by rfl⟩ : syracuseStep 287135 = 430703) B430703
theorem B713873 : Blo 123787 713873 := bstep (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) B535405
theorem B320699 : Blo 123787 320699 := bstep (se 1 (by rfl) ⟨240524, by rfl⟩ : syracuseStep 320699 = 481049) B481049
theorem B2319673 : Blo 123787 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B124319 : Blo 123787 124319 := bstep (se 1 (by rfl) ⟨93239, by rfl⟩ : syracuseStep 124319 = 186479) B186479
theorem B124367 : Blo 123787 124367 := bstep (se 1 (by rfl) ⟨93275, by rfl⟩ : syracuseStep 124367 = 186551) B186551
theorem B124647 : Blo 123787 124647 := bstep (se 1 (by rfl) ⟨93485, by rfl⟩ : syracuseStep 124647 = 186971) B186971
theorem B2287561 : Blo 123787 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B419795 : Blo 123787 419795 := bstep (se 1 (by rfl) ⟨314846, by rfl⟩ : syracuseStep 419795 = 629693) B629693
theorem B190535 : Blo 123787 190535 := bstep (se 1 (by rfl) ⟨142901, by rfl⟩ : syracuseStep 190535 = 285803) B285803
theorem B256379 : Blo 123787 256379 := bstep (se 1 (by rfl) ⟨192284, by rfl⟩ : syracuseStep 256379 = 384569) B384569
theorem B158107 : Blo 123787 158107 := bstep (se 1 (by rfl) ⟨118580, by rfl⟩ : syracuseStep 158107 = 237161) B237161
theorem B125391 : Blo 123787 125391 := bstep (se 1 (by rfl) ⟨94043, by rfl⟩ : syracuseStep 125391 = 188087) B188087
theorem B420335 : Blo 123787 420335 := bstep (se 1 (by rfl) ⟨315251, by rfl⟩ : syracuseStep 420335 = 630503) B630503
theorem B125863 : Blo 123787 125863 := bstep (se 1 (by rfl) ⟨94397, by rfl⟩ : syracuseStep 125863 = 188795) B188795
theorem B125979 : Blo 123787 125979 := bstep (se 1 (by rfl) ⟨94484, by rfl⟩ : syracuseStep 125979 = 188969) B188969
theorem B126183 : Blo 123787 126183 := bstep (se 1 (by rfl) ⟨94637, by rfl⟩ : syracuseStep 126183 = 189275) B189275
theorem B126623 : Blo 123787 126623 := bstep (se 1 (by rfl) ⟨94967, by rfl⟩ : syracuseStep 126623 = 189935) B189935
theorem B126631 : Blo 123787 126631 := bstep (se 1 (by rfl) ⟨94973, by rfl⟩ : syracuseStep 126631 = 189947) B189947
theorem B716471 : Blo 123787 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B323291 : Blo 123787 323291 := bstep (se 1 (by rfl) ⟨242468, by rfl⟩ : syracuseStep 323291 = 484937) B484937
theorem B126703 : Blo 123787 126703 := bstep (se 1 (by rfl) ⟨95027, by rfl⟩ : syracuseStep 126703 = 190055) B190055
theorem B126751 : Blo 123787 126751 := bstep (se 1 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 126751 = 190127) B190127
theorem B126831 : Blo 123787 126831 := bstep (se 1 (by rfl) ⟨95123, by rfl⟩ : syracuseStep 126831 = 190247) B190247
theorem B126879 : Blo 123787 126879 := bstep (se 1 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 126879 = 190319) B190319
theorem B159727 : Blo 123787 159727 := bstep (se 1 (by rfl) ⟨119795, by rfl⟩ : syracuseStep 159727 = 239591) B239591
theorem B127003 : Blo 123787 127003 := bstep (se 1 (by rfl) ⟨95252, by rfl⟩ : syracuseStep 127003 = 190505) B190505
theorem B127231 : Blo 123787 127231 := bstep (se 1 (by rfl) ⟨95423, by rfl⟩ : syracuseStep 127231 = 190847) B190847
theorem B5402983 : Blo 123787 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B127391 : Blo 123787 127391 := bstep (se 1 (by rfl) ⟨95543, by rfl⟩ : syracuseStep 127391 = 191087) B191087
theorem B422333 : Blo 123787 422333 := bstep (se 3 (by rfl) ⟨79187, by rfl⟩ : syracuseStep 422333 = 158375) B158375
theorem B1274939 : Blo 123787 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B424061 : Blo 123787 424061 := bstep (se 3 (by rfl) ⟨79511, by rfl⟩ : syracuseStep 424061 = 159023) B159023
theorem B424223 : Blo 123787 424223 := bstep (se 1 (by rfl) ⟨318167, by rfl⟩ : syracuseStep 424223 = 636335) B636335
theorem B425627 : Blo 123787 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B655019 : Blo 123787 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B426167 : Blo 123787 426167 := bstep (se 1 (by rfl) ⟨319625, by rfl⟩ : syracuseStep 426167 = 639251) B639251
theorem B361207 : Blo 123787 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B1541387 : Blo 123787 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B427463 : Blo 123787 427463 := bstep (se 1 (by rfl) ⟨320597, by rfl⟩ : syracuseStep 427463 = 641195) B641195
theorem B1411343 : Blo 123787 1411343 := bstep (se 1 (by rfl) ⟨1058507, by rfl⟩ : syracuseStep 1411343 = 2117015) B2117015
theorem B3050081 : Blo 123787 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B1511135 : Blo 123787 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B430055 : Blo 123787 430055 := bstep (se 1 (by rfl) ⟨322541, by rfl⟩ : syracuseStep 430055 = 645083) B645083
theorem B430163 : Blo 123787 430163 := bstep (se 1 (by rfl) ⟨322622, by rfl⟩ : syracuseStep 430163 = 645245) B645245
theorem B430271 : Blo 123787 430271 := bstep (se 1 (by rfl) ⟨322703, by rfl⟩ : syracuseStep 430271 = 645407) B645407
theorem B430379 : Blo 123787 430379 := bstep (se 1 (by rfl) ⟨322784, by rfl⟩ : syracuseStep 430379 = 645569) B645569
theorem B4067819 : Blo 123787 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B529375 : Blo 123787 529375 := bstep (se 1 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 529375 = 794063) B794063
theorem B824603 : Blo 123787 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B6460979 : Blo 123787 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B760769 : Blo 123787 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B236857 : Blo 123787 236857 := bstep (se 2 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 236857 = 177643) B177643
theorem B597871 : Blo 123787 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B4530167 : Blo 123787 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B402401 : Blo 123787 402401 := bstep (se 2 (by rfl) ⟨150900, by rfl⟩ : syracuseStep 402401 = 301801) B301801
theorem B8463689 : Blo 123787 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B239689 : Blo 123787 239689 := bstep (se 2 (by rfl) ⟨89883, by rfl⟩ : syracuseStep 239689 = 179767) B179767
theorem B272479 : Blo 123787 272479 := bstep (se 1 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 272479 = 408719) B408719
theorem B1190207 : Blo 123787 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B436679 : Blo 123787 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B798187 : Blo 123787 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B241193 : Blo 123787 241193 := bstep (se 2 (by rfl) ⟨90447, by rfl⟩ : syracuseStep 241193 = 180895) B180895
theorem B3092897 : Blo 123787 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B537455 : Blo 123787 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B3519773 : Blo 123787 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B636659 : Blo 123787 636659 := bstep (se 1 (by rfl) ⟨477494, by rfl⟩ : syracuseStep 636659 = 954989) B954989
theorem B210809 : Blo 123787 210809 := bstep (se 2 (by rfl) ⟨79053, by rfl⟩ : syracuseStep 210809 = 158107) B158107
theorem B801161 : Blo 123787 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B211511 : Blo 123787 211511 := bstep (se 1 (by rfl) ⟨158633, by rfl⟩ : syracuseStep 211511 = 317267) B317267
theorem B179015 : Blo 123787 179015 := bstep (se 1 (by rfl) ⟨134261, by rfl⟩ : syracuseStep 179015 = 268523) B268523
theorem B212071 : Blo 123787 212071 := bstep (se 1 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 212071 = 318107) B318107
theorem B441929 : Blo 123787 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B212969 : Blo 123787 212969 := bstep (se 2 (by rfl) ⟨79863, by rfl⟩ : syracuseStep 212969 = 159727) B159727
theorem B12206537 : Blo 123787 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B475915 : Blo 123787 475915 := bstep (se 1 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 475915 = 713873) B713873
theorem B213799 : Blo 123787 213799 := bstep (se 1 (by rfl) ⟨160349, by rfl⟩ : syracuseStep 213799 = 320699) B320699
theorem B1295585 : Blo 123787 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B279863 : Blo 123787 279863 := bstep (se 1 (by rfl) ⟨209897, by rfl⟩ : syracuseStep 279863 = 419795) B419795
theorem B280223 : Blo 123787 280223 := bstep (se 1 (by rfl) ⟨210167, by rfl⟩ : syracuseStep 280223 = 420335) B420335
theorem B640871 : Blo 123787 640871 := bstep (se 1 (by rfl) ⟨480653, by rfl⟩ : syracuseStep 640871 = 961307) B961307
theorem B1820951 : Blo 123787 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B477647 : Blo 123787 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B215527 : Blo 123787 215527 := bstep (se 1 (by rfl) ⟨161645, by rfl⟩ : syracuseStep 215527 = 323291) B323291
theorem B707291 : Blo 123787 707291 := bstep (se 1 (by rfl) ⟨530468, by rfl⟩ : syracuseStep 707291 = 1060937) B1060937
theorem B281555 : Blo 123787 281555 := bstep (se 1 (by rfl) ⟨211166, by rfl⟩ : syracuseStep 281555 = 422333) B422333
theorem B282707 : Blo 123787 282707 := bstep (se 1 (by rfl) ⟨212030, by rfl⟩ : syracuseStep 282707 = 424061) B424061
theorem B315535 : Blo 123787 315535 := bstep (se 1 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 315535 = 473303) B473303
theorem B282815 : Blo 123787 282815 := bstep (se 1 (by rfl) ⟨212111, by rfl⟩ : syracuseStep 282815 = 424223) B424223
theorem B971347 : Blo 123787 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B1037033 : Blo 123787 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B906011 : Blo 123787 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B283751 : Blo 123787 283751 := bstep (se 1 (by rfl) ⟨212813, by rfl⟩ : syracuseStep 283751 = 425627) B425627
theorem B283769 : Blo 123787 283769 := bstep (se 2 (by rfl) ⟨106413, by rfl⟩ : syracuseStep 283769 = 212827) B212827
theorem B185807 : Blo 123787 185807 := bstep (se 1 (by rfl) ⟨139355, by rfl⟩ : syracuseStep 185807 = 278711) B278711
theorem B185963 : Blo 123787 185963 := bstep (se 1 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 185963 = 278945) B278945
theorem B808555 : Blo 123787 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B317135 : Blo 123787 317135 := bstep (se 1 (by rfl) ⟨237851, by rfl⟩ : syracuseStep 317135 = 475703) B475703
theorem B481247 : Blo 123787 481247 := bstep (se 1 (by rfl) ⟨360935, by rfl⟩ : syracuseStep 481247 = 721871) B721871
theorem B186475 : Blo 123787 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B186935 : Blo 123787 186935 := bstep (se 1 (by rfl) ⟨140201, by rfl⟩ : syracuseStep 186935 = 280403) B280403
theorem B187007 : Blo 123787 187007 := bstep (se 1 (by rfl) ⟨140255, by rfl⟩ : syracuseStep 187007 = 280511) B280511
theorem B187163 : Blo 123787 187163 := bstep (se 1 (by rfl) ⟨140372, by rfl⟩ : syracuseStep 187163 = 280745) B280745
theorem B187529 : Blo 123787 187529 := bstep (se 2 (by rfl) ⟨70323, by rfl⟩ : syracuseStep 187529 = 140647) B140647
theorem B187547 : Blo 123787 187547 := bstep (se 1 (by rfl) ⟨140660, by rfl⟩ : syracuseStep 187547 = 281321) B281321
theorem B3595427 : Blo 123787 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B187583 : Blo 123787 187583 := bstep (se 1 (by rfl) ⟨140687, by rfl⟩ : syracuseStep 187583 = 281375) B281375
theorem B187871 : Blo 123787 187871 := bstep (se 1 (by rfl) ⟨140903, by rfl⟩ : syracuseStep 187871 = 281807) B281807
theorem B646703 : Blo 123787 646703 := bstep (se 1 (by rfl) ⟨485027, by rfl⟩ : syracuseStep 646703 = 970055) B970055
theorem B188351 : Blo 123787 188351 := bstep (se 1 (by rfl) ⟨141263, by rfl⟩ : syracuseStep 188351 = 282527) B282527
theorem B188447 : Blo 123787 188447 := bstep (se 1 (by rfl) ⟨141335, by rfl⟩ : syracuseStep 188447 = 282671) B282671
theorem B12509623 : Blo 123787 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B418283 : Blo 123787 418283 := bstep (se 1 (by rfl) ⟨313712, by rfl⟩ : syracuseStep 418283 = 627425) B627425
theorem B287279 : Blo 123787 287279 := bstep (se 1 (by rfl) ⟨215459, by rfl⟩ : syracuseStep 287279 = 430919) B430919
theorem B385631 : Blo 123787 385631 := bstep (se 1 (by rfl) ⟨289223, by rfl⟩ : syracuseStep 385631 = 578447) B578447
theorem B189065 : Blo 123787 189065 := bstep (se 2 (by rfl) ⟨70899, by rfl⟩ : syracuseStep 189065 = 141799) B141799
theorem B483995 : Blo 123787 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B287551 : Blo 123787 287551 := bstep (se 1 (by rfl) ⟨215663, by rfl⟩ : syracuseStep 287551 = 431327) B431327
theorem B320507 : Blo 123787 320507 := bstep (se 1 (by rfl) ⟨240380, by rfl⟩ : syracuseStep 320507 = 480761) B480761
theorem B484481 : Blo 123787 484481 := bstep (se 2 (by rfl) ⟨181680, by rfl⟩ : syracuseStep 484481 = 363361) B363361
theorem B189599 : Blo 123787 189599 := bstep (se 1 (by rfl) ⟨142199, by rfl⟩ : syracuseStep 189599 = 284399) B284399
theorem B353555 : Blo 123787 353555 := bstep (se 1 (by rfl) ⟨265166, by rfl⟩ : syracuseStep 353555 = 530333) B530333
theorem B189767 : Blo 123787 189767 := bstep (se 1 (by rfl) ⟨142325, by rfl⟩ : syracuseStep 189767 = 284651) B284651
theorem B124263 : Blo 123787 124263 := bstep (se 1 (by rfl) ⟨93197, by rfl⟩ : syracuseStep 124263 = 186395) B186395
theorem B1959461 : Blo 123787 1959461 := bstep (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) B367399
theorem B124507 : Blo 123787 124507 := bstep (se 1 (by rfl) ⟨93380, by rfl⟩ : syracuseStep 124507 = 186761) B186761
theorem B943811 : Blo 123787 943811 := bstep (se 1 (by rfl) ⟨707858, by rfl⟩ : syracuseStep 943811 = 1415717) B1415717
theorem B5891869 : Blo 123787 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B124991 : Blo 123787 124991 := bstep (se 1 (by rfl) ⟨93743, by rfl⟩ : syracuseStep 124991 = 187487) B187487
theorem B190631 : Blo 123787 190631 := bstep (se 1 (by rfl) ⟨142973, by rfl⟩ : syracuseStep 190631 = 285947) B285947
theorem B223585 : Blo 123787 223585 := bstep (se 2 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 223585 = 167689) B167689
theorem B125423 : Blo 123787 125423 := bstep (se 1 (by rfl) ⟨94067, by rfl⟩ : syracuseStep 125423 = 188135) B188135
theorem B125531 : Blo 123787 125531 := bstep (se 1 (by rfl) ⟨94148, by rfl⟩ : syracuseStep 125531 = 188297) B188297
theorem B191303 : Blo 123787 191303 := bstep (se 1 (by rfl) ⟨143477, by rfl⟩ : syracuseStep 191303 = 286955) B286955
theorem B125887 : Blo 123787 125887 := bstep (se 1 (by rfl) ⟨94415, by rfl⟩ : syracuseStep 125887 = 188831) B188831
theorem B191423 : Blo 123787 191423 := bstep (se 1 (by rfl) ⟨143567, by rfl⟩ : syracuseStep 191423 = 287135) B287135
theorem B7203977 : Blo 123787 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B486847 : Blo 123787 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B224795 : Blo 123787 224795 := bstep (se 1 (by rfl) ⟨168596, by rfl⟩ : syracuseStep 224795 = 337193) B337193
theorem B683677 : Blo 123787 683677 := bstep (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) B256379
theorem B127023 : Blo 123787 127023 := bstep (se 1 (by rfl) ⟨95267, by rfl⟩ : syracuseStep 127023 = 190535) B190535
theorem B815183 : Blo 123787 815183 := bstep (se 1 (by rfl) ⟨611387, by rfl⟩ : syracuseStep 815183 = 1222775) B1222775
theorem B815615 : Blo 123787 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B1537703 : Blo 123787 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B1865423 : Blo 123787 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B489341 : Blo 123787 489341 := bstep (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) B183503
theorem B849959 : Blo 123787 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B227431 : Blo 123787 227431 := bstep (se 1 (by rfl) ⟨170573, by rfl⟩ : syracuseStep 227431 = 341147) B341147
theorem B358759 : Blo 123787 358759 := bstep (se 1 (by rfl) ⟨269069, by rfl⟩ : syracuseStep 358759 = 538139) B538139
theorem B1211507 : Blo 123787 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B425087 : Blo 123787 425087 := bstep (se 1 (by rfl) ⟨318815, by rfl⟩ : syracuseStep 425087 = 637631) B637631
theorem B818383 : Blo 123787 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B1212965 : Blo 123787 1212965 := bstep (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) B227431
theorem B427247 : Blo 123787 427247 := bstep (se 1 (by rfl) ⟨320435, by rfl⟩ : syracuseStep 427247 = 640871) B640871
theorem B1213967 : Blo 123787 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B2033387 : Blo 123787 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B66717989 : Blo 123787 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B363305 : Blo 123787 363305 := bstep (se 2 (by rfl) ⟨136239, by rfl⟩ : syracuseStep 363305 = 272479) B272479
theorem B691355 : Blo 123787 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B2396951 : Blo 123787 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B431135 : Blo 123787 431135 := bstep (se 1 (by rfl) ⟨323351, by rfl⟩ : syracuseStep 431135 = 646703) B646703
theorem B3020111 : Blo 123787 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B268267 : Blo 123787 268267 := bstep (se 1 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 268267 = 402401) B402401
theorem B235703 : Blo 123787 235703 := bstep (se 1 (by rfl) ⟨176777, by rfl⟩ : syracuseStep 235703 = 353555) B353555
theorem B5642459 : Blo 123787 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B629207 : Blo 123787 629207 := bstep (se 1 (by rfl) ⟨471905, by rfl⟩ : syracuseStep 629207 = 943811) B943811
theorem B793471 : Blo 123787 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B1025135 : Blo 123787 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B140539 : Blo 123787 140539 := bstep (se 1 (by rfl) ⟨105404, by rfl⟩ : syracuseStep 140539 = 210809) B210809
theorem B566639 : Blo 123787 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B534107 : Blo 123787 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B1091177 : Blo 123787 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B141007 : Blo 123787 141007 := bstep (se 1 (by rfl) ⟨105755, by rfl⟩ : syracuseStep 141007 = 211511) B211511
theorem B3188645 : Blo 123787 3188645 := bstep (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) B597871
theorem B141979 : Blo 123787 141979 := bstep (se 1 (by rfl) ⟨106484, by rfl⟩ : syracuseStep 141979 = 212969) B212969
theorem B8137691 : Blo 123787 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B863723 : Blo 123787 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B634553 : Blo 123787 634553 := bstep (se 2 (by rfl) ⟨237957, by rfl⟩ : syracuseStep 634553 = 475915) B475915
theorem B471527 : Blo 123787 471527 := bstep (se 1 (by rfl) ⟨353645, by rfl⟩ : syracuseStep 471527 = 707291) B707291
theorem B8795765 : Blo 123787 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B604007 : Blo 123787 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B4110365 : Blo 123787 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B211423 : Blo 123787 211423 := bstep (se 1 (by rfl) ⟨158567, by rfl⟩ : syracuseStep 211423 = 317135) B317135
theorem B507179 : Blo 123787 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B1064249 : Blo 123787 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B278855 : Blo 123787 278855 := bstep (se 1 (by rfl) ⟨209141, by rfl⟩ : syracuseStep 278855 = 418283) B418283
theorem B213671 : Blo 123787 213671 := bstep (se 1 (by rfl) ⟨160253, by rfl⟩ : syracuseStep 213671 = 320507) B320507
theorem B1295129 : Blo 123787 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B705833 : Blo 123787 705833 := bstep (se 2 (by rfl) ⟨264687, by rfl⟩ : syracuseStep 705833 = 529375) B529375
theorem B4769813 : Blo 123787 4769813 := bstep (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) B223585
theorem B4802651 : Blo 123787 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B477373 : Blo 123787 477373 := bstep (se 3 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 477373 = 179015) B179015
theorem B149863 : Blo 123787 149863 := bstep (se 1 (by rfl) ⟨112397, by rfl⟩ : syracuseStep 149863 = 224795) B224795
theorem B543455 : Blo 123787 543455 := bstep (se 1 (by rfl) ⟨407591, by rfl⟩ : syracuseStep 543455 = 815183) B815183
theorem B248633 : Blo 123787 248633 := bstep (se 2 (by rfl) ⟨93237, by rfl⟩ : syracuseStep 248633 = 186475) B186475
theorem B543743 : Blo 123787 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B478345 : Blo 123787 478345 := bstep (se 2 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 478345 = 358759) B358759
theorem B2346515 : Blo 123787 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B282761 : Blo 123787 282761 := bstep (se 2 (by rfl) ⟨106035, by rfl⟩ : syracuseStep 282761 = 212071) B212071
theorem B315809 : Blo 123787 315809 := bstep (se 2 (by rfl) ⟨118428, by rfl⟩ : syracuseStep 315809 = 236857) B236857
theorem B807671 : Blo 123787 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B283391 : Blo 123787 283391 := bstep (se 1 (by rfl) ⟨212543, by rfl⟩ : syracuseStep 283391 = 425087) B425087
theorem B284111 : Blo 123787 284111 := bstep (se 1 (by rfl) ⟨213083, by rfl⟩ : syracuseStep 284111 = 426167) B426167
theorem B186575 : Blo 123787 186575 := bstep (se 1 (by rfl) ⟨139931, by rfl⟩ : syracuseStep 186575 = 279863) B279863
theorem B284975 : Blo 123787 284975 := bstep (se 1 (by rfl) ⟨213731, by rfl⟩ : syracuseStep 284975 = 427463) B427463
theorem B481609 : Blo 123787 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B285065 : Blo 123787 285065 := bstep (se 2 (by rfl) ⟨106899, by rfl⟩ : syracuseStep 285065 = 213799) B213799
theorem B383401 : Blo 123787 383401 := bstep (se 2 (by rfl) ⟨143775, by rfl⟩ : syracuseStep 383401 = 287551) B287551
theorem B186815 : Blo 123787 186815 := bstep (se 1 (by rfl) ⟨140111, by rfl⟩ : syracuseStep 186815 = 280223) B280223
theorem B940895 : Blo 123787 940895 := bstep (se 1 (by rfl) ⟨705671, by rfl⟩ : syracuseStep 940895 = 1411343) B1411343
theorem B318431 : Blo 123787 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B187703 : Blo 123787 187703 := bstep (se 1 (by rfl) ⟨140777, by rfl⟩ : syracuseStep 187703 = 281555) B281555
theorem B1433213 : Blo 123787 1433213 := bstep (se 3 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 1433213 = 537455) B537455
theorem B7855825 : Blo 123787 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B1007423 : Blo 123787 1007423 := bstep (se 1 (by rfl) ⟨755567, by rfl⟩ : syracuseStep 1007423 = 1511135) B1511135
theorem B286703 : Blo 123787 286703 := bstep (se 1 (by rfl) ⟨215027, by rfl⟩ : syracuseStep 286703 = 430055) B430055
theorem B188471 : Blo 123787 188471 := bstep (se 1 (by rfl) ⟨141353, by rfl⟩ : syracuseStep 188471 = 282707) B282707
theorem B286775 : Blo 123787 286775 := bstep (se 1 (by rfl) ⟨215081, by rfl⟩ : syracuseStep 286775 = 430163) B430163
theorem B319585 : Blo 123787 319585 := bstep (se 2 (by rfl) ⟨119844, by rfl⟩ : syracuseStep 319585 = 239689) B239689
theorem B188543 : Blo 123787 188543 := bstep (se 1 (by rfl) ⟨141407, by rfl⟩ : syracuseStep 188543 = 282815) B282815
theorem B286847 : Blo 123787 286847 := bstep (se 1 (by rfl) ⟨215135, by rfl⟩ : syracuseStep 286847 = 430271) B430271
theorem B286919 : Blo 123787 286919 := bstep (se 1 (by rfl) ⟨215189, by rfl⟩ : syracuseStep 286919 = 430379) B430379
theorem B2711879 : Blo 123787 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B287369 : Blo 123787 287369 := bstep (se 2 (by rfl) ⟨107763, by rfl⟩ : syracuseStep 287369 = 215527) B215527
theorem B189167 : Blo 123787 189167 := bstep (se 1 (by rfl) ⟨141875, by rfl⟩ : syracuseStep 189167 = 283751) B283751
theorem B189179 : Blo 123787 189179 := bstep (se 1 (by rfl) ⟨141884, by rfl⟩ : syracuseStep 189179 = 283769) B283769
theorem B123871 : Blo 123787 123871 := bstep (se 1 (by rfl) ⟨92903, by rfl⟩ : syracuseStep 123871 = 185807) B185807
theorem B123975 : Blo 123787 123975 := bstep (se 1 (by rfl) ⟨92981, by rfl⟩ : syracuseStep 123975 = 185963) B185963
theorem B320831 : Blo 123787 320831 := bstep (se 1 (by rfl) ⟨240623, by rfl⟩ : syracuseStep 320831 = 481247) B481247
theorem B17229277 : Blo 123787 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B124623 : Blo 123787 124623 := bstep (se 1 (by rfl) ⟨93467, by rfl⟩ : syracuseStep 124623 = 186935) B186935
theorem B124671 : Blo 123787 124671 := bstep (se 1 (by rfl) ⟨93503, by rfl⟩ : syracuseStep 124671 = 187007) B187007
theorem B124775 : Blo 123787 124775 := bstep (se 1 (by rfl) ⟨93581, by rfl⟩ : syracuseStep 124775 = 187163) B187163
theorem B649129 : Blo 123787 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B125019 : Blo 123787 125019 := bstep (se 1 (by rfl) ⟨93764, by rfl⟩ : syracuseStep 125019 = 187529) B187529
theorem B125031 : Blo 123787 125031 := bstep (se 1 (by rfl) ⟨93773, by rfl⟩ : syracuseStep 125031 = 187547) B187547
theorem B125055 : Blo 123787 125055 := bstep (se 1 (by rfl) ⟨93791, by rfl⟩ : syracuseStep 125055 = 187583) B187583
theorem B911569 : Blo 123787 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B125247 : Blo 123787 125247 := bstep (se 1 (by rfl) ⟨93935, by rfl⟩ : syracuseStep 125247 = 187871) B187871
theorem B1304909 : Blo 123787 1304909 := bstep (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) B489341
theorem B125567 : Blo 123787 125567 := bstep (se 1 (by rfl) ⟨94175, by rfl⟩ : syracuseStep 125567 = 188351) B188351
theorem B125631 : Blo 123787 125631 := bstep (se 1 (by rfl) ⟨94223, by rfl⟩ : syracuseStep 125631 = 188447) B188447
theorem B420713 : Blo 123787 420713 := bstep (se 2 (by rfl) ⟨157767, by rfl⟩ : syracuseStep 420713 = 315535) B315535
theorem B191519 : Blo 123787 191519 := bstep (se 1 (by rfl) ⟨143639, by rfl⟩ : syracuseStep 191519 = 287279) B287279
theorem B257087 : Blo 123787 257087 := bstep (se 1 (by rfl) ⟨192815, by rfl⟩ : syracuseStep 257087 = 385631) B385631
theorem B126043 : Blo 123787 126043 := bstep (se 1 (by rfl) ⟨94532, by rfl⟩ : syracuseStep 126043 = 189065) B189065
theorem B322663 : Blo 123787 322663 := bstep (se 1 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 322663 = 483995) B483995
theorem B322987 : Blo 123787 322987 := bstep (se 1 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 322987 = 484481) B484481
theorem B126399 : Blo 123787 126399 := bstep (se 1 (by rfl) ⟨94799, by rfl⟩ : syracuseStep 126399 = 189599) B189599
theorem B126511 : Blo 123787 126511 := bstep (se 1 (by rfl) ⟨94883, by rfl⟩ : syracuseStep 126511 = 189767) B189767
theorem B1306307 : Blo 123787 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B127087 : Blo 123787 127087 := bstep (se 1 (by rfl) ⟨95315, by rfl⟩ : syracuseStep 127087 = 190631) B190631
theorem B291119 : Blo 123787 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B127535 : Blo 123787 127535 := bstep (se 1 (by rfl) ⟨95651, by rfl⟩ : syracuseStep 127535 = 191303) B191303
theorem B127615 : Blo 123787 127615 := bstep (se 1 (by rfl) ⟨95711, by rfl⟩ : syracuseStep 127615 = 191423) B191423
theorem B1078073 : Blo 123787 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B160795 : Blo 123787 160795 := bstep (se 1 (by rfl) ⟨120596, by rfl⟩ : syracuseStep 160795 = 241193) B241193
theorem B2061931 : Blo 123787 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B1243615 : Blo 123787 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B424439 : Blo 123787 424439 := bstep (se 1 (by rfl) ⟨318329, by rfl⟩ : syracuseStep 424439 = 636659) B636659
theorem B294619 : Blo 123787 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B426113 : Blo 123787 426113 := bstep (se 2 (by rfl) ⟨159792, by rfl⟩ : syracuseStep 426113 = 319585) B319585
theorem B362303 : Blo 123787 362303 := bstep (se 1 (by rfl) ⟨271727, by rfl⟩ : syracuseStep 362303 = 543455) B543455
theorem B165755 : Blo 123787 165755 := bstep (se 1 (by rfl) ⟨124316, by rfl⟩ : syracuseStep 165755 = 248633) B248633
theorem B22972369 : Blo 123787 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B362495 : Blo 123787 362495 := bstep (se 1 (by rfl) ⟨271871, by rfl⟩ : syracuseStep 362495 = 543743) B543743
theorem B460903 : Blo 123787 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B1215425 : Blo 123787 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B199817 : Blo 123787 199817 := bstep (se 2 (by rfl) ⟨74931, by rfl⟩ : syracuseStep 199817 = 149863) B149863
theorem B430217 : Blo 123787 430217 := bstep (se 2 (by rfl) ⟨161331, by rfl⟩ : syracuseStep 430217 = 322663) B322663
theorem B430649 : Blo 123787 430649 := bstep (se 2 (by rfl) ⟨161493, by rfl⟩ : syracuseStep 430649 = 322987) B322987
theorem B627263 : Blo 123787 627263 := bstep (se 1 (by rfl) ⟨470447, by rfl⟩ : syracuseStep 627263 = 940895) B940895
theorem B955475 : Blo 123787 955475 := bstep (se 1 (by rfl) ⟨716606, by rfl⟩ : syracuseStep 955475 = 1433213) B1433213
theorem B12719501 : Blo 123787 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1807919 : Blo 123787 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B727451 : Blo 123787 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B171391 : Blo 123787 171391 := bstep (se 1 (by rfl) ⟨128543, by rfl⟩ : syracuseStep 171391 = 257087) B257087
theorem B1352477 : Blo 123787 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B1057961 : Blo 123787 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B402671 : Blo 123787 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B2303261 : Blo 123787 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B142447 : Blo 123787 142447 := bstep (se 1 (by rfl) ⟨106835, by rfl⟩ : syracuseStep 142447 = 213671) B213671
theorem B470555 : Blo 123787 470555 := bstep (se 1 (by rfl) ⟨352916, by rfl⟩ : syracuseStep 470555 = 705833) B705833
theorem B1355591 : Blo 123787 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B44478659 : Blo 123787 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B2568581 : Blo 123787 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B242203 : Blo 123787 242203 := bstep (se 1 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 242203 = 363305) B363305
theorem B3453677 : Blo 123787 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B865505 : Blo 123787 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B636497 : Blo 123787 636497 := bstep (se 2 (by rfl) ⟨238686, by rfl⟩ : syracuseStep 636497 = 477373) B477373
theorem B210539 : Blo 123787 210539 := bstep (se 1 (by rfl) ⟨157904, by rfl⟩ : syracuseStep 210539 = 315809) B315809
theorem B538447 : Blo 123787 538447 := bstep (se 1 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 538447 = 807671) B807671
theorem B2013407 : Blo 123787 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B637793 : Blo 123787 637793 := bstep (se 2 (by rfl) ⟨239172, by rfl⟩ : syracuseStep 637793 = 478345) B478345
theorem B212287 : Blo 123787 212287 := bstep (se 1 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 212287 = 318431) B318431
theorem B671615 : Blo 123787 671615 := bstep (se 1 (by rfl) ⟨503711, by rfl⟩ : syracuseStep 671615 = 1007423) B1007423
theorem B213887 : Blo 123787 213887 := bstep (se 1 (by rfl) ⟨160415, by rfl⟩ : syracuseStep 213887 = 320831) B320831
theorem B377759 : Blo 123787 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B214393 : Blo 123787 214393 := bstep (se 2 (by rfl) ⟨80397, by rfl⟩ : syracuseStep 214393 = 160795) B160795
theorem B869939 : Blo 123787 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B280475 : Blo 123787 280475 := bstep (se 1 (by rfl) ⟨210356, by rfl⟩ : syracuseStep 280475 = 420713) B420713
theorem B5425127 : Blo 123787 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B870871 : Blo 123787 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B314351 : Blo 123787 314351 := bstep (se 1 (by rfl) ⟨235763, by rfl⟩ : syracuseStep 314351 = 471527) B471527
theorem B511201 : Blo 123787 511201 := bstep (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) B383401
theorem B281897 : Blo 123787 281897 := bstep (se 2 (by rfl) ⟨105711, by rfl⟩ : syracuseStep 281897 = 211423) B211423
theorem B1658153 : Blo 123787 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B2740243 : Blo 123787 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B282959 : Blo 123787 282959 := bstep (se 1 (by rfl) ⟨212219, by rfl⟩ : syracuseStep 282959 = 424439) B424439
theorem B709499 : Blo 123787 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B10474433 : Blo 123787 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B185903 : Blo 123787 185903 := bstep (se 1 (by rfl) ⟨139427, by rfl⟩ : syracuseStep 185903 = 278855) B278855
theorem B808643 : Blo 123787 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B776317 : Blo 123787 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B284831 : Blo 123787 284831 := bstep (se 1 (by rfl) ⟨213623, by rfl⟩ : syracuseStep 284831 = 427247) B427247
theorem B809311 : Blo 123787 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B3201767 : Blo 123787 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B187385 : Blo 123787 187385 := bstep (se 2 (by rfl) ⟨70269, by rfl⟩ : syracuseStep 187385 = 140539) B140539
theorem B188009 : Blo 123787 188009 := bstep (se 2 (by rfl) ⟨70503, by rfl⟩ : syracuseStep 188009 = 141007) B141007
theorem B1564343 : Blo 123787 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B188507 : Blo 123787 188507 := bstep (se 1 (by rfl) ⟨141380, by rfl⟩ : syracuseStep 188507 = 282761) B282761
theorem B188927 : Blo 123787 188927 := bstep (se 1 (by rfl) ⟨141695, by rfl⟩ : syracuseStep 188927 = 283391) B283391
theorem B1597967 : Blo 123787 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B287423 : Blo 123787 287423 := bstep (se 1 (by rfl) ⟨215567, by rfl⟩ : syracuseStep 287423 = 431135) B431135
theorem B189305 : Blo 123787 189305 := bstep (se 2 (by rfl) ⟨70989, by rfl⟩ : syracuseStep 189305 = 141979) B141979
theorem B189407 : Blo 123787 189407 := bstep (se 1 (by rfl) ⟨142055, by rfl⟩ : syracuseStep 189407 = 284111) B284111
theorem B157135 : Blo 123787 157135 := bstep (se 1 (by rfl) ⟨117851, by rfl⟩ : syracuseStep 157135 = 235703) B235703
theorem B124383 : Blo 123787 124383 := bstep (se 1 (by rfl) ⟨93287, by rfl⟩ : syracuseStep 124383 = 186575) B186575
theorem B3761639 : Blo 123787 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B189983 : Blo 123787 189983 := bstep (se 1 (by rfl) ⟨142487, by rfl⟩ : syracuseStep 189983 = 284975) B284975
theorem B190043 : Blo 123787 190043 := bstep (se 1 (by rfl) ⟨142532, by rfl⟩ : syracuseStep 190043 = 285065) B285065
theorem B124543 : Blo 123787 124543 := bstep (se 1 (by rfl) ⟨93407, by rfl⟩ : syracuseStep 124543 = 186815) B186815
theorem B419471 : Blo 123787 419471 := bstep (se 1 (by rfl) ⟨314603, by rfl⟩ : syracuseStep 419471 = 629207) B629207
theorem B125135 : Blo 123787 125135 := bstep (se 1 (by rfl) ⟨93851, by rfl⟩ : syracuseStep 125135 = 187703) B187703
theorem B191135 : Blo 123787 191135 := bstep (se 1 (by rfl) ⟨143351, by rfl⟩ : syracuseStep 191135 = 286703) B286703
theorem B125647 : Blo 123787 125647 := bstep (se 1 (by rfl) ⟨94235, by rfl⟩ : syracuseStep 125647 = 188471) B188471
theorem B191183 : Blo 123787 191183 := bstep (se 1 (by rfl) ⟨143387, by rfl⟩ : syracuseStep 191183 = 286775) B286775
theorem B125695 : Blo 123787 125695 := bstep (se 1 (by rfl) ⟨94271, by rfl⟩ : syracuseStep 125695 = 188543) B188543
theorem B191231 : Blo 123787 191231 := bstep (se 1 (by rfl) ⟨143423, by rfl⟩ : syracuseStep 191231 = 286847) B286847
theorem B191279 : Blo 123787 191279 := bstep (se 1 (by rfl) ⟨143459, by rfl⟩ : syracuseStep 191279 = 286919) B286919
theorem B191579 : Blo 123787 191579 := bstep (se 1 (by rfl) ⟨143684, by rfl⟩ : syracuseStep 191579 = 287369) B287369
theorem B126111 : Blo 123787 126111 := bstep (se 1 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 126111 = 189167) B189167
theorem B126119 : Blo 123787 126119 := bstep (se 1 (by rfl) ⟨94589, by rfl⟩ : syracuseStep 126119 = 189179) B189179
theorem B683423 : Blo 123787 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B356071 : Blo 123787 356071 := bstep (se 1 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 356071 = 534107) B534107
theorem B2125763 : Blo 123787 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B127679 : Blo 123787 127679 := bstep (se 1 (by rfl) ⟨95759, by rfl⟩ : syracuseStep 127679 = 191519) B191519
theorem B2749241 : Blo 123787 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B423035 : Blo 123787 423035 := bstep (se 1 (by rfl) ⟨317276, by rfl⟩ : syracuseStep 423035 = 634553) B634553
theorem B357689 : Blo 123787 357689 := bstep (se 2 (by rfl) ⟨134133, by rfl⟩ : syracuseStep 357689 = 268267) B268267
theorem B718715 : Blo 123787 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B5863843 : Blo 123787 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B392825 : Blo 123787 392825 := bstep (se 2 (by rfl) ⟨147309, by rfl⟩ : syracuseStep 392825 = 294619) B294619
theorem B3606605 : Blo 123787 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B133211 : Blo 123787 133211 := bstep (se 1 (by rfl) ⟨99908, by rfl⟩ : syracuseStep 133211 = 199817) B199817
theorem B6982955 : Blo 123787 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B2134511 : Blo 123787 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B268447 : Blo 123787 268447 := bstep (se 1 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 268447 = 402671) B402671
theorem B2726405 : Blo 123787 2726405 := bstep (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) B511201
theorem B1417175 : Blo 123787 1417175 := bstep (se 1 (by rfl) ⟨1062881, by rfl⟩ : syracuseStep 1417175 = 2125763) B2125763
theorem B1712387 : Blo 123787 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B2302451 : Blo 123787 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B238459 : Blo 123787 238459 := bstep (se 1 (by rfl) ⟨178844, by rfl⟩ : syracuseStep 238459 = 357689) B357689
theorem B140359 : Blo 123787 140359 := bstep (se 1 (by rfl) ⟨105269, by rfl⟩ : syracuseStep 140359 = 210539) B210539
theorem B142591 : Blo 123787 142591 := bstep (se 1 (by rfl) ⟨106943, by rfl⟩ : syracuseStep 142591 = 213887) B213887
theorem B241535 : Blo 123787 241535 := bstep (se 1 (by rfl) ⟨181151, by rfl⟩ : syracuseStep 241535 = 362303) B362303
theorem B3616751 : Blo 123787 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B209513 : Blo 123787 209513 := bstep (se 2 (by rfl) ⟨78567, by rfl⟩ : syracuseStep 209513 = 157135) B157135
theorem B209567 : Blo 123787 209567 := bstep (se 1 (by rfl) ⟨157175, by rfl⟩ : syracuseStep 209567 = 314351) B314351
theorem B472999 : Blo 123787 472999 := bstep (se 1 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 472999 = 709499) B709499
theorem B1161161 : Blo 123787 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B636983 : Blo 123787 636983 := bstep (se 1 (by rfl) ⟨477737, by rfl⟩ : syracuseStep 636983 = 955475) B955475
theorem B474761 : Blo 123787 474761 := bstep (se 2 (by rfl) ⟨178035, by rfl⟩ : syracuseStep 474761 = 356071) B356071
theorem B442013 : Blo 123787 442013 := bstep (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) B165755
theorem B966653 : Blo 123787 966653 := bstep (se 3 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 966653 = 362495) B362495
theorem B3653657 : Blo 123787 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B1065311 : Blo 123787 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B705307 : Blo 123787 705307 := bstep (se 1 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 705307 = 1057961) B1057961
theorem B2507759 : Blo 123787 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B279647 : Blo 123787 279647 := bstep (se 1 (by rfl) ⟨209735, by rfl⟩ : syracuseStep 279647 = 419471) B419471
theorem B313703 : Blo 123787 313703 := bstep (se 1 (by rfl) ⟨235277, by rfl⟩ : syracuseStep 313703 = 470555) B470555
theorem B903727 : Blo 123787 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B1035089 : Blo 123787 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B7818457 : Blo 123787 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B282023 : Blo 123787 282023 := bstep (se 1 (by rfl) ⟨211517, by rfl⟩ : syracuseStep 282023 = 423035) B423035
theorem B577003 : Blo 123787 577003 := bstep (se 1 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 577003 = 865505) B865505
theorem B479143 : Blo 123787 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B283049 : Blo 123787 283049 := bstep (se 2 (by rfl) ⟨106143, by rfl⟩ : syracuseStep 283049 = 212287) B212287
theorem B447743 : Blo 123787 447743 := bstep (se 1 (by rfl) ⟨335807, by rfl⟩ : syracuseStep 447743 = 671615) B671615
theorem B284075 : Blo 123787 284075 := bstep (se 1 (by rfl) ⟨213056, by rfl⟩ : syracuseStep 284075 = 426113) B426113
theorem B251839 : Blo 123787 251839 := bstep (se 1 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 251839 = 377759) B377759
theorem B579959 : Blo 123787 579959 := bstep (se 1 (by rfl) ⟨434969, by rfl⟩ : syracuseStep 579959 = 869939) B869939
theorem B186983 : Blo 123787 186983 := bstep (se 1 (by rfl) ⟨140237, by rfl⟩ : syracuseStep 186983 = 280475) B280475
theorem B285857 : Blo 123787 285857 := bstep (se 2 (by rfl) ⟨107196, by rfl⟩ : syracuseStep 285857 = 214393) B214393
theorem B187931 : Blo 123787 187931 := bstep (se 1 (by rfl) ⟨140948, by rfl⟩ : syracuseStep 187931 = 281897) B281897
theorem B1105435 : Blo 123787 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B30629825 : Blo 123787 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B286811 : Blo 123787 286811 := bstep (se 1 (by rfl) ⟨215108, by rfl⟩ : syracuseStep 286811 = 430217) B430217
theorem B614537 : Blo 123787 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B188639 : Blo 123787 188639 := bstep (se 1 (by rfl) ⟨141479, by rfl⟩ : syracuseStep 188639 = 282959) B282959
theorem B287099 : Blo 123787 287099 := bstep (se 1 (by rfl) ⟨215324, by rfl⟩ : syracuseStep 287099 = 430649) B430649
theorem B418175 : Blo 123787 418175 := bstep (se 1 (by rfl) ⟨313631, by rfl⟩ : syracuseStep 418175 = 627263) B627263
theorem B8479667 : Blo 123787 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B123935 : Blo 123787 123935 := bstep (se 1 (by rfl) ⟨92951, by rfl⟩ : syracuseStep 123935 = 185903) B185903
theorem B1205279 : Blo 123787 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B189887 : Blo 123787 189887 := bstep (se 1 (by rfl) ⟨142415, by rfl⟩ : syracuseStep 189887 = 284831) B284831
theorem B189929 : Blo 123787 189929 := bstep (se 2 (by rfl) ⟨71223, by rfl⟩ : syracuseStep 189929 = 142447) B142447
theorem B484967 : Blo 123787 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B2156381 : Blo 123787 2156381 := bstep (se 3 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 2156381 = 808643) B808643
theorem B124923 : Blo 123787 124923 := bstep (se 1 (by rfl) ⟨93692, by rfl⟩ : syracuseStep 124923 = 187385) B187385
theorem B125339 : Blo 123787 125339 := bstep (se 1 (by rfl) ⟨94004, by rfl⟩ : syracuseStep 125339 = 188009) B188009
theorem B1042895 : Blo 123787 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B125671 : Blo 123787 125671 := bstep (se 1 (by rfl) ⟨94253, by rfl⟩ : syracuseStep 125671 = 188507) B188507
theorem B125951 : Blo 123787 125951 := bstep (se 1 (by rfl) ⟨94463, by rfl⟩ : syracuseStep 125951 = 188927) B188927
theorem B191615 : Blo 123787 191615 := bstep (se 1 (by rfl) ⟨143711, by rfl⟩ : syracuseStep 191615 = 287423) B287423
theorem B126203 : Blo 123787 126203 := bstep (se 1 (by rfl) ⟨94652, by rfl⟩ : syracuseStep 126203 = 189305) B189305
theorem B126271 : Blo 123787 126271 := bstep (se 1 (by rfl) ⟨94703, by rfl⟩ : syracuseStep 126271 = 189407) B189407
theorem B322937 : Blo 123787 322937 := bstep (se 2 (by rfl) ⟨121101, by rfl⟩ : syracuseStep 322937 = 242203) B242203
theorem B1535507 : Blo 123787 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B126655 : Blo 123787 126655 := bstep (se 1 (by rfl) ⟨94991, by rfl⟩ : syracuseStep 126655 = 189983) B189983
theorem B126695 : Blo 123787 126695 := bstep (se 1 (by rfl) ⟨95021, by rfl⟩ : syracuseStep 126695 = 190043) B190043
theorem B127423 : Blo 123787 127423 := bstep (se 1 (by rfl) ⟨95567, by rfl⟩ : syracuseStep 127423 = 191135) B191135
theorem B127455 : Blo 123787 127455 := bstep (se 1 (by rfl) ⟨95591, by rfl⟩ : syracuseStep 127455 = 191183) B191183
theorem B127487 : Blo 123787 127487 := bstep (se 1 (by rfl) ⟨95615, by rfl⟩ : syracuseStep 127487 = 191231) B191231
theorem B127519 : Blo 123787 127519 := bstep (se 1 (by rfl) ⟨95639, by rfl⟩ : syracuseStep 127519 = 191279) B191279
theorem B127719 : Blo 123787 127719 := bstep (se 1 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 127719 = 191579) B191579
theorem B455615 : Blo 123787 455615 := bstep (se 1 (by rfl) ⟨341711, by rfl⟩ : syracuseStep 455615 = 683423) B683423
theorem B717929 : Blo 123787 717929 := bstep (se 2 (by rfl) ⟨269223, by rfl⟩ : syracuseStep 717929 = 538447) B538447
theorem B3241133 : Blo 123787 3241133 := bstep (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) B1215425
theorem B29652439 : Blo 123787 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B1079081 : Blo 123787 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B1832827 : Blo 123787 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B424331 : Blo 123787 424331 := bstep (se 1 (by rfl) ⟨318248, by rfl⟩ : syracuseStep 424331 = 636497) B636497
theorem B1342271 : Blo 123787 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B228521 : Blo 123787 228521 := bstep (se 2 (by rfl) ⟨85695, by rfl⟩ : syracuseStep 228521 = 171391) B171391
theorem B425195 : Blo 123787 425195 := bstep (se 1 (by rfl) ⟨318896, by rfl⟩ : syracuseStep 425195 = 637793) B637793
theorem B261883 : Blo 123787 261883 := bstep (se 1 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 261883 = 392825) B392825
theorem B1671839 : Blo 123787 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B690059 : Blo 123787 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B4655303 : Blo 123787 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B298495 : Blo 123787 298495 := bstep (se 1 (by rfl) ⟨223871, by rfl⟩ : syracuseStep 298495 = 447743) B447743
theorem B10424609 : Blo 123787 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B20419883 : Blo 123787 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B3579389 : Blo 123787 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B1023671 : Blo 123787 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B630665 : Blo 123787 630665 := bstep (se 2 (by rfl) ⟨236499, by rfl⟩ : syracuseStep 630665 = 472999) B472999
theorem B335785 : Blo 123787 335785 := bstep (se 2 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 335785 = 251839) B251839
theorem B139675 : Blo 123787 139675 := bstep (se 1 (by rfl) ⟨104756, by rfl⟩ : syracuseStep 139675 = 209513) B209513
theorem B139711 : Blo 123787 139711 := bstep (se 1 (by rfl) ⟨104783, by rfl⟩ : syracuseStep 139711 = 209567) B209567
theorem B303743 : Blo 123787 303743 := bstep (se 1 (by rfl) ⟨227807, by rfl⟩ : syracuseStep 303743 = 455615) B455615
theorem B2435771 : Blo 123787 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B4566365 : Blo 123787 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B2404403 : Blo 123787 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B209135 : Blo 123787 209135 := bstep (se 1 (by rfl) ⟨156851, by rfl⟩ : syracuseStep 209135 = 313703) B313703
theorem B1423007 : Blo 123787 1423007 := bstep (se 1 (by rfl) ⟨1067255, by rfl⟩ : syracuseStep 1423007 = 2134511) B2134511
theorem B1817603 : Blo 123787 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B769337 : Blo 123787 769337 := bstep (se 2 (by rfl) ⟨288501, by rfl⟩ : syracuseStep 769337 = 577003) B577003
theorem B638857 : Blo 123787 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B409691 : Blo 123787 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B278783 : Blo 123787 278783 := bstep (se 1 (by rfl) ⟨209087, by rfl⟩ : syracuseStep 278783 = 418175) B418175
theorem B5653111 : Blo 123787 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B803519 : Blo 123787 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B39536585 : Blo 123787 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B215291 : Blo 123787 215291 := bstep (se 1 (by rfl) ⟨161468, by rfl⟩ : syracuseStep 215291 = 322937) B322937
theorem B2443769 : Blo 123787 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B2411167 : Blo 123787 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B609389 : Blo 123787 609389 := bstep (se 3 (by rfl) ⟨114260, by rfl⟩ : syracuseStep 609389 = 228521) B228521
theorem B478619 : Blo 123787 478619 := bstep (se 1 (by rfl) ⟨358964, by rfl⟩ : syracuseStep 478619 = 717929) B717929
theorem B774107 : Blo 123787 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B282887 : Blo 123787 282887 := bstep (se 1 (by rfl) ⟨212165, by rfl⟩ : syracuseStep 282887 = 424331) B424331
theorem B283463 : Blo 123787 283463 := bstep (se 1 (by rfl) ⟨212597, by rfl⟩ : syracuseStep 283463 = 425195) B425195
theorem B349177 : Blo 123787 349177 := bstep (se 2 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 349177 = 261883) B261883
theorem B316507 : Blo 123787 316507 := bstep (se 1 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 316507 = 474761) B474761
theorem B644435 : Blo 123787 644435 := bstep (se 1 (by rfl) ⟨483326, by rfl⟩ : syracuseStep 644435 = 966653) B966653
theorem B710207 : Blo 123787 710207 := bstep (se 1 (by rfl) ⟨532655, by rfl⟩ : syracuseStep 710207 = 1065311) B1065311
theorem B186431 : Blo 123787 186431 := bstep (se 1 (by rfl) ⟨139823, by rfl⟩ : syracuseStep 186431 = 279647) B279647
theorem B940409 : Blo 123787 940409 := bstep (se 2 (by rfl) ⟨352653, by rfl⟩ : syracuseStep 940409 = 705307) B705307
theorem B317945 : Blo 123787 317945 := bstep (se 2 (by rfl) ⟨119229, by rfl⟩ : syracuseStep 317945 = 238459) B238459
theorem B187145 : Blo 123787 187145 := bstep (se 2 (by rfl) ⟨70179, by rfl⟩ : syracuseStep 187145 = 140359) B140359
theorem B188015 : Blo 123787 188015 := bstep (se 1 (by rfl) ⟨141011, by rfl⟩ : syracuseStep 188015 = 282023) B282023
theorem B188699 : Blo 123787 188699 := bstep (se 1 (by rfl) ⟨141524, by rfl⟩ : syracuseStep 188699 = 283049) B283049
theorem B1204969 : Blo 123787 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B189383 : Blo 123787 189383 := bstep (se 1 (by rfl) ⟨142037, by rfl⟩ : syracuseStep 189383 = 284075) B284075
theorem B386639 : Blo 123787 386639 := bstep (se 1 (by rfl) ⟨289979, by rfl⟩ : syracuseStep 386639 = 579959) B579959
theorem B190121 : Blo 123787 190121 := bstep (se 2 (by rfl) ⟨71295, by rfl⟩ : syracuseStep 190121 = 142591) B142591
theorem B124655 : Blo 123787 124655 := bstep (se 1 (by rfl) ⟨93491, by rfl⟩ : syracuseStep 124655 = 186983) B186983
theorem B190571 : Blo 123787 190571 := bstep (se 1 (by rfl) ⟨142928, by rfl⟩ : syracuseStep 190571 = 285857) B285857
theorem B125287 : Blo 123787 125287 := bstep (se 1 (by rfl) ⟨93965, by rfl⟩ : syracuseStep 125287 = 187931) B187931
theorem B944783 : Blo 123787 944783 := bstep (se 1 (by rfl) ⟨708587, by rfl⟩ : syracuseStep 944783 = 1417175) B1417175
theorem B191207 : Blo 123787 191207 := bstep (se 1 (by rfl) ⟨143405, by rfl⟩ : syracuseStep 191207 = 286811) B286811
theorem B125759 : Blo 123787 125759 := bstep (se 1 (by rfl) ⟨94319, by rfl⟩ : syracuseStep 125759 = 188639) B188639
theorem B355229 : Blo 123787 355229 := bstep (se 3 (by rfl) ⟨66605, by rfl⟩ : syracuseStep 355229 = 133211) B133211
theorem B191399 : Blo 123787 191399 := bstep (se 1 (by rfl) ⟨143549, by rfl⟩ : syracuseStep 191399 = 287099) B287099
theorem B1534967 : Blo 123787 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B126591 : Blo 123787 126591 := bstep (se 1 (by rfl) ⟨94943, by rfl⟩ : syracuseStep 126591 = 189887) B189887
theorem B126619 : Blo 123787 126619 := bstep (se 1 (by rfl) ⟨94964, by rfl⟩ : syracuseStep 126619 = 189929) B189929
theorem B323311 : Blo 123787 323311 := bstep (se 1 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 323311 = 484967) B484967
theorem B2781053 : Blo 123787 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B1437587 : Blo 123787 1437587 := bstep (se 1 (by rfl) ⟨1078190, by rfl⟩ : syracuseStep 1437587 = 2156381) B2156381
theorem B4714805 : Blo 123787 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B127743 : Blo 123787 127743 := bstep (se 1 (by rfl) ⟨95807, by rfl⟩ : syracuseStep 127743 = 191615) B191615
theorem B161023 : Blo 123787 161023 := bstep (se 1 (by rfl) ⟨120767, by rfl⟩ : syracuseStep 161023 = 241535) B241535
theorem B357929 : Blo 123787 357929 := bstep (se 2 (by rfl) ⟨134223, by rfl⟩ : syracuseStep 357929 = 268447) B268447
theorem B2160755 : Blo 123787 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B719387 : Blo 123787 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B424655 : Blo 123787 424655 := bstep (se 1 (by rfl) ⟨318491, by rfl⟩ : syracuseStep 424655 = 636983) B636983
theorem B1473913 : Blo 123787 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B1114559 : Blo 123787 1114559 := bstep (se 1 (by rfl) ⟨835919, by rfl⟩ : syracuseStep 1114559 = 1671839) B1671839
theorem B7537481 : Blo 123787 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B1606625 : Blo 123787 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B6949739 : Blo 123787 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B3214889 : Blo 123787 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B429623 : Blo 123787 429623 := bstep (se 1 (by rfl) ⟨322217, by rfl⟩ : syracuseStep 429623 = 644435) B644435
theorem B626939 : Blo 123787 626939 := bstep (se 1 (by rfl) ⟨470204, by rfl⟩ : syracuseStep 626939 = 940409) B940409
theorem B397993 : Blo 123787 397993 := bstep (se 2 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 397993 = 298495) B298495
theorem B431081 : Blo 123787 431081 := bstep (se 2 (by rfl) ⟨161655, by rfl⟩ : syracuseStep 431081 = 323311) B323311
theorem B1840157 : Blo 123787 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B202495 : Blo 123787 202495 := bstep (se 1 (by rfl) ⟨151871, by rfl⟩ : syracuseStep 202495 = 303743) B303743
theorem B465569 : Blo 123787 465569 := bstep (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) B349177
theorem B629855 : Blo 123787 629855 := bstep (se 1 (by rfl) ⟨472391, by rfl⟩ : syracuseStep 629855 = 944783) B944783
theorem B236819 : Blo 123787 236819 := bstep (se 1 (by rfl) ⟨177614, by rfl⟩ : syracuseStep 236819 = 355229) B355229
theorem B1023311 : Blo 123787 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B958391 : Blo 123787 958391 := bstep (se 1 (by rfl) ⟨718793, by rfl⟩ : syracuseStep 958391 = 1437587) B1437587
theorem B139423 : Blo 123787 139423 := bstep (se 1 (by rfl) ⟨104567, by rfl⟩ : syracuseStep 139423 = 209135) B209135
theorem B238619 : Blo 123787 238619 := bstep (se 1 (by rfl) ⟨178964, by rfl⟩ : syracuseStep 238619 = 357929) B357929
theorem B1092509 : Blo 123787 1092509 := bstep (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) B409691
theorem B535679 : Blo 123787 535679 := bstep (se 1 (by rfl) ⟨401759, by rfl⟩ : syracuseStep 535679 = 803519) B803519
theorem B26357723 : Blo 123787 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B143527 : Blo 123787 143527 := bstep (se 1 (by rfl) ⟨107645, by rfl⟩ : syracuseStep 143527 = 215291) B215291
theorem B406259 : Blo 123787 406259 := bstep (se 1 (by rfl) ⟨304694, by rfl⟩ : syracuseStep 406259 = 609389) B609389
theorem B13613255 : Blo 123787 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B473471 : Blo 123787 473471 := bstep (se 1 (by rfl) ⟨355103, by rfl⟩ : syracuseStep 473471 = 710207) B710207
theorem B211963 : Blo 123787 211963 := bstep (se 1 (by rfl) ⟨158972, by rfl⟩ : syracuseStep 211963 = 317945) B317945
theorem B214697 : Blo 123787 214697 := bstep (se 2 (by rfl) ⟨80511, by rfl⟩ : syracuseStep 214697 = 161023) B161023
theorem B1623847 : Blo 123787 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B1854035 : Blo 123787 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B479591 : Blo 123787 479591 := bstep (se 1 (by rfl) ⟨359693, by rfl⟩ : syracuseStep 479591 = 719387) B719387
theorem B283103 : Blo 123787 283103 := bstep (se 1 (by rfl) ⟨212327, by rfl⟩ : syracuseStep 283103 = 424655) B424655
theorem B512891 : Blo 123787 512891 := bstep (se 1 (by rfl) ⟨384668, by rfl⟩ : syracuseStep 512891 = 769337) B769337
theorem B447713 : Blo 123787 447713 := bstep (se 2 (by rfl) ⟨167892, by rfl⟩ : syracuseStep 447713 = 335785) B335785
theorem B185855 : Blo 123787 185855 := bstep (se 1 (by rfl) ⟨139391, by rfl⟩ : syracuseStep 185855 = 278783) B278783
theorem B186233 : Blo 123787 186233 := bstep (se 2 (by rfl) ⟨69837, by rfl⟩ : syracuseStep 186233 = 139675) B139675
theorem B186281 : Blo 123787 186281 := bstep (se 2 (by rfl) ⟨69855, by rfl⟩ : syracuseStep 186281 = 139711) B139711
theorem B12572813 : Blo 123787 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B3103535 : Blo 123787 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B1629179 : Blo 123787 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B319079 : Blo 123787 319079 := bstep (se 1 (by rfl) ⟨239309, by rfl⟩ : syracuseStep 319079 = 478619) B478619
theorem B516071 : Blo 123787 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B188591 : Blo 123787 188591 := bstep (se 1 (by rfl) ⟨141443, by rfl⟩ : syracuseStep 188591 = 282887) B282887
theorem B188975 : Blo 123787 188975 := bstep (se 1 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 188975 = 283463) B283463
theorem B124287 : Blo 123787 124287 := bstep (se 1 (by rfl) ⟨93215, by rfl⟩ : syracuseStep 124287 = 186431) B186431
theorem B124763 : Blo 123787 124763 := bstep (se 1 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 124763 = 187145) B187145
theorem B2386259 : Blo 123787 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B125343 : Blo 123787 125343 := bstep (se 1 (by rfl) ⟨94007, by rfl⟩ : syracuseStep 125343 = 188015) B188015
theorem B682447 : Blo 123787 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B420443 : Blo 123787 420443 := bstep (se 1 (by rfl) ⟨315332, by rfl⟩ : syracuseStep 420443 = 630665) B630665
theorem B125799 : Blo 123787 125799 := bstep (se 1 (by rfl) ⟨94349, by rfl⟩ : syracuseStep 125799 = 188699) B188699
theorem B126255 : Blo 123787 126255 := bstep (se 1 (by rfl) ⟨94691, by rfl⟩ : syracuseStep 126255 = 189383) B189383
theorem B257759 : Blo 123787 257759 := bstep (se 1 (by rfl) ⟨193319, by rfl⟩ : syracuseStep 257759 = 386639) B386639
theorem B126747 : Blo 123787 126747 := bstep (se 1 (by rfl) ⟨95060, by rfl⟩ : syracuseStep 126747 = 190121) B190121
theorem B127047 : Blo 123787 127047 := bstep (se 1 (by rfl) ⟨95285, by rfl⟩ : syracuseStep 127047 = 190571) B190571
theorem B422009 : Blo 123787 422009 := bstep (se 2 (by rfl) ⟨158253, by rfl⟩ : syracuseStep 422009 = 316507) B316507
theorem B127471 : Blo 123787 127471 := bstep (se 1 (by rfl) ⟨95603, by rfl⟩ : syracuseStep 127471 = 191207) B191207
theorem B127599 : Blo 123787 127599 := bstep (se 1 (by rfl) ⟨95699, by rfl⟩ : syracuseStep 127599 = 191399) B191399
theorem B3044243 : Blo 123787 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B1602935 : Blo 123787 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B948671 : Blo 123787 948671 := bstep (se 1 (by rfl) ⟨711503, by rfl⟩ : syracuseStep 948671 = 1423007) B1423007
theorem B1440503 : Blo 123787 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B1965217 : Blo 123787 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B1211735 : Blo 123787 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B851809 : Blo 123787 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B2165129 : Blo 123787 2165129 := bstep (se 2 (by rfl) ⟨811923, by rfl⟩ : syracuseStep 2165129 = 1623847) B1623847
theorem B298475 : Blo 123787 298475 := bstep (se 1 (by rfl) ⟨223856, by rfl⟩ : syracuseStep 298475 = 447713) B447713
theorem B2069023 : Blo 123787 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B1086119 : Blo 123787 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B530657 : Blo 123787 530657 := bstep (se 2 (by rfl) ⟨198996, by rfl⟩ : syracuseStep 530657 = 397993) B397993
theorem B269993 : Blo 123787 269993 := bstep (se 2 (by rfl) ⟨101247, by rfl⟩ : syracuseStep 269993 = 202495) B202495
theorem B171839 : Blo 123787 171839 := bstep (se 1 (by rfl) ⟨128879, by rfl⟩ : syracuseStep 171839 = 257759) B257759
theorem B17571815 : Blo 123787 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B270839 : Blo 123787 270839 := bstep (se 1 (by rfl) ⟨203129, by rfl⟩ : syracuseStep 270839 = 406259) B406259
theorem B2728829 : Blo 123787 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B632447 : Blo 123787 632447 := bstep (se 1 (by rfl) ⟨474335, by rfl⟩ : syracuseStep 632447 = 948671) B948671
theorem B960335 : Blo 123787 960335 := bstep (se 1 (by rfl) ⟨720251, by rfl⟩ : syracuseStep 960335 = 1440503) B1440503
theorem B5024987 : Blo 123787 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B143131 : Blo 123787 143131 := bstep (se 1 (by rfl) ⟨107348, by rfl⟩ : syracuseStep 143131 = 214697) B214697
theorem B4633159 : Blo 123787 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B2143259 : Blo 123787 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B341927 : Blo 123787 341927 := bstep (se 1 (by rfl) ⟨256445, by rfl⟩ : syracuseStep 341927 = 512891) B512891
theorem B1226771 : Blo 123787 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B212719 : Blo 123787 212719 := bstep (se 1 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 212719 = 319079) B319079
theorem B638927 : Blo 123787 638927 := bstep (se 1 (by rfl) ⟨479195, by rfl⟩ : syracuseStep 638927 = 958391) B958391
theorem B344047 : Blo 123787 344047 := bstep (se 1 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 344047 = 516071) B516071
theorem B46613717 : Blo 123787 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B1590839 : Blo 123787 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B4966069 : Blo 123787 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B280295 : Blo 123787 280295 := bstep (se 1 (by rfl) ⟨210221, by rfl⟩ : syracuseStep 280295 = 420443) B420443
theorem B281339 : Blo 123787 281339 := bstep (se 1 (by rfl) ⟨211004, by rfl⟩ : syracuseStep 281339 = 422009) B422009
theorem B1068623 : Blo 123787 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B282617 : Blo 123787 282617 := bstep (se 2 (by rfl) ⟨105981, by rfl⟩ : syracuseStep 282617 = 211963) B211963
theorem B315647 : Blo 123787 315647 := bstep (se 1 (by rfl) ⟨236735, by rfl⟩ : syracuseStep 315647 = 473471) B473471
theorem B807823 : Blo 123787 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B1135745 : Blo 123787 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B185897 : Blo 123787 185897 := bstep (se 2 (by rfl) ⟨69711, by rfl⟩ : syracuseStep 185897 = 139423) B139423
theorem B743039 : Blo 123787 743039 := bstep (se 1 (by rfl) ⟨557279, by rfl⟩ : syracuseStep 743039 = 1114559) B1114559
theorem B1071083 : Blo 123787 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B1236023 : Blo 123787 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B286415 : Blo 123787 286415 := bstep (se 1 (by rfl) ⟨214811, by rfl⟩ : syracuseStep 286415 = 429623) B429623
theorem B417959 : Blo 123787 417959 := bstep (se 1 (by rfl) ⟨313469, by rfl⟩ : syracuseStep 417959 = 626939) B626939
theorem B319727 : Blo 123787 319727 := bstep (se 1 (by rfl) ⟨239795, by rfl⟩ : syracuseStep 319727 = 479591) B479591
theorem B188735 : Blo 123787 188735 := bstep (se 1 (by rfl) ⟨141551, by rfl⟩ : syracuseStep 188735 = 283103) B283103
theorem B909929 : Blo 123787 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B287387 : Blo 123787 287387 := bstep (se 1 (by rfl) ⟨215540, by rfl⟩ : syracuseStep 287387 = 431081) B431081
theorem B123903 : Blo 123787 123903 := bstep (se 1 (by rfl) ⟨92927, by rfl⟩ : syracuseStep 123903 = 185855) B185855
theorem B124155 : Blo 123787 124155 := bstep (se 1 (by rfl) ⟨93116, by rfl⟩ : syracuseStep 124155 = 186233) B186233
theorem B124187 : Blo 123787 124187 := bstep (se 1 (by rfl) ⟨93140, by rfl⟩ : syracuseStep 124187 = 186281) B186281
theorem B8381875 : Blo 123787 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B419903 : Blo 123787 419903 := bstep (se 1 (by rfl) ⟨314927, by rfl⟩ : syracuseStep 419903 = 629855) B629855
theorem B157879 : Blo 123787 157879 := bstep (se 1 (by rfl) ⟨118409, by rfl⟩ : syracuseStep 157879 = 236819) B236819
theorem B125727 : Blo 123787 125727 := bstep (se 1 (by rfl) ⟨94295, by rfl⟩ : syracuseStep 125727 = 188591) B188591
theorem B191369 : Blo 123787 191369 := bstep (se 2 (by rfl) ⟨71763, by rfl⟩ : syracuseStep 191369 = 143527) B143527
theorem B125983 : Blo 123787 125983 := bstep (se 1 (by rfl) ⟨94487, by rfl⟩ : syracuseStep 125983 = 188975) B188975
theorem B159079 : Blo 123787 159079 := bstep (se 1 (by rfl) ⟨119309, by rfl⟩ : syracuseStep 159079 = 238619) B238619
theorem B357119 : Blo 123787 357119 := bstep (se 1 (by rfl) ⟨267839, by rfl⟩ : syracuseStep 357119 = 535679) B535679
theorem B2029495 : Blo 123787 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B9075503 : Blo 123787 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B2620289 : Blo 123787 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B1443419 : Blo 123787 1443419 := bstep (se 1 (by rfl) ⟨1082564, by rfl⟩ : syracuseStep 1443419 = 2165129) B2165129
theorem B11175833 : Blo 123787 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B6621425 : Blo 123787 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B198983 : Blo 123787 198983 := bstep (se 1 (by rfl) ⟨149237, by rfl⟩ : syracuseStep 198983 = 298475) B298475
theorem B724079 : Blo 123787 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B495359 : Blo 123787 495359 := bstep (se 1 (by rfl) ⟨371519, by rfl⟩ : syracuseStep 495359 = 743039) B743039
theorem B824015 : Blo 123787 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B2758697 : Blo 123787 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B3349991 : Blo 123787 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B238079 : Blo 123787 238079 := bstep (se 1 (by rfl) ⟨178559, by rfl⟩ : syracuseStep 238079 = 357119) B357119
theorem B1746859 : Blo 123787 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B31075811 : Blo 123787 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B1060559 : Blo 123787 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B210431 : Blo 123787 210431 := bstep (se 1 (by rfl) ⟨157823, by rfl⟩ : syracuseStep 210431 = 315647) B315647
theorem B210505 : Blo 123787 210505 := bstep (se 2 (by rfl) ⟨78939, by rfl⟩ : syracuseStep 210505 = 157879) B157879
theorem B212105 : Blo 123787 212105 := bstep (se 2 (by rfl) ⟨79539, by rfl⟩ : syracuseStep 212105 = 159079) B159079
theorem B179995 : Blo 123787 179995 := bstep (se 1 (by rfl) ⟨134996, by rfl⟩ : syracuseStep 179995 = 269993) B269993
theorem B11714543 : Blo 123787 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B278639 : Blo 123787 278639 := bstep (se 1 (by rfl) ⟨208979, by rfl⟩ : syracuseStep 278639 = 417959) B417959
theorem B213151 : Blo 123787 213151 := bstep (se 1 (by rfl) ⟨159863, by rfl⟩ : syracuseStep 213151 = 319727) B319727
theorem B180559 : Blo 123787 180559 := bstep (se 1 (by rfl) ⟨135419, by rfl⟩ : syracuseStep 180559 = 270839) B270839
theorem B606619 : Blo 123787 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B1819219 : Blo 123787 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B6177545 : Blo 123787 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B640223 : Blo 123787 640223 := bstep (se 1 (by rfl) ⟨480167, by rfl⟩ : syracuseStep 640223 = 960335) B960335
theorem B279935 : Blo 123787 279935 := bstep (se 1 (by rfl) ⟨209951, by rfl⟩ : syracuseStep 279935 = 419903) B419903
theorem B2705993 : Blo 123787 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B1428839 : Blo 123787 1428839 := bstep (se 1 (by rfl) ⟨1071629, by rfl⟩ : syracuseStep 1428839 = 2143259) B2143259
theorem B6050335 : Blo 123787 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B283625 : Blo 123787 283625 := bstep (se 2 (by rfl) ⟨106359, by rfl⟩ : syracuseStep 283625 = 212719) B212719
theorem B186863 : Blo 123787 186863 := bstep (se 1 (by rfl) ⟨140147, by rfl⟩ : syracuseStep 186863 = 280295) B280295
theorem B12114613 : Blo 123787 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B187559 : Blo 123787 187559 := bstep (se 1 (by rfl) ⟨140669, by rfl⟩ : syracuseStep 187559 = 281339) B281339
theorem B712415 : Blo 123787 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B188411 : Blo 123787 188411 := bstep (se 1 (by rfl) ⟨141308, by rfl⟩ : syracuseStep 188411 = 282617) B282617
theorem B123931 : Blo 123787 123931 := bstep (se 1 (by rfl) ⟨92948, by rfl⟩ : syracuseStep 123931 = 185897) B185897
theorem B714055 : Blo 123787 714055 := bstep (se 1 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 714055 = 1071083) B1071083
theorem B353771 : Blo 123787 353771 := bstep (se 1 (by rfl) ⟨265328, by rfl⟩ : syracuseStep 353771 = 530657) B530657
theorem B190841 : Blo 123787 190841 := bstep (se 2 (by rfl) ⟨71565, by rfl⟩ : syracuseStep 190841 = 143131) B143131
theorem B190943 : Blo 123787 190943 := bstep (se 1 (by rfl) ⟨143207, by rfl⟩ : syracuseStep 190943 = 286415) B286415
theorem B125823 : Blo 123787 125823 := bstep (se 1 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 125823 = 188735) B188735
theorem B191591 : Blo 123787 191591 := bstep (se 1 (by rfl) ⟨143693, by rfl⟩ : syracuseStep 191591 = 287387) B287387
theorem B421631 : Blo 123787 421631 := bstep (se 1 (by rfl) ⟨316223, by rfl⟩ : syracuseStep 421631 = 632447) B632447
theorem B1077097 : Blo 123787 1077097 := bstep (se 2 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 1077097 = 807823) B807823
theorem B127579 : Blo 123787 127579 := bstep (se 1 (by rfl) ⟨95684, by rfl⟩ : syracuseStep 127579 = 191369) B191369
theorem B227951 : Blo 123787 227951 := bstep (se 1 (by rfl) ⟨170963, by rfl⟩ : syracuseStep 227951 = 341927) B341927
theorem B817847 : Blo 123787 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B458237 : Blo 123787 458237 := bstep (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) B171839
theorem B425951 : Blo 123787 425951 := bstep (se 1 (by rfl) ⟨319463, by rfl⟩ : syracuseStep 425951 = 638927) B638927
theorem B458729 : Blo 123787 458729 := bstep (se 2 (by rfl) ⟨172023, by rfl⟩ : syracuseStep 458729 = 344047) B344047
theorem B2425625 : Blo 123787 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B426815 : Blo 123787 426815 := bstep (se 1 (by rfl) ⟨320111, by rfl⟩ : syracuseStep 426815 = 640223) B640223
theorem B1803995 : Blo 123787 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B952073 : Blo 123787 952073 := bstep (se 2 (by rfl) ⟨357027, by rfl⟩ : syracuseStep 952073 = 714055) B714055
theorem B952559 : Blo 123787 952559 := bstep (se 1 (by rfl) ⟨714419, by rfl⟩ : syracuseStep 952559 = 1428839) B1428839
theorem B330239 : Blo 123787 330239 := bstep (se 1 (by rfl) ⟨247679, by rfl⟩ : syracuseStep 330239 = 495359) B495359
theorem B2329145 : Blo 123787 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B1839131 : Blo 123787 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B2233327 : Blo 123787 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B8067113 : Blo 123787 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B530621 : Blo 123787 530621 := bstep (se 3 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 530621 = 198983) B198983
theorem B235847 : Blo 123787 235847 := bstep (se 1 (by rfl) ⟨176885, by rfl⟩ : syracuseStep 235847 = 353771) B353771
theorem B20717207 : Blo 123787 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B140287 : Blo 123787 140287 := bstep (se 1 (by rfl) ⟨105215, by rfl⟩ : syracuseStep 140287 = 210431) B210431
theorem B1221965 : Blo 123787 1221965 := bstep (se 3 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 1221965 = 458237) B458237
theorem B141403 : Blo 123787 141403 := bstep (se 1 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 141403 = 212105) B212105
theorem B239993 : Blo 123787 239993 := bstep (se 2 (by rfl) ⟨89997, by rfl⟩ : syracuseStep 239993 = 179995) B179995
theorem B305819 : Blo 123787 305819 := bstep (se 1 (by rfl) ⟨229364, by rfl⟩ : syracuseStep 305819 = 458729) B458729
theorem B7809695 : Blo 123787 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B240745 : Blo 123787 240745 := bstep (se 2 (by rfl) ⟨90279, by rfl⟩ : syracuseStep 240745 = 180559) B180559
theorem B962279 : Blo 123787 962279 := bstep (se 1 (by rfl) ⟨721709, by rfl⟩ : syracuseStep 962279 = 1443419) B1443419
theorem B7450555 : Blo 123787 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B634877 : Blo 123787 634877 := bstep (se 3 (by rfl) ⟨119039, by rfl⟩ : syracuseStep 634877 = 238079) B238079
theorem B474943 : Blo 123787 474943 := bstep (se 1 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 474943 = 712415) B712415
theorem B280673 : Blo 123787 280673 := bstep (se 2 (by rfl) ⟨105252, by rfl⟩ : syracuseStep 280673 = 210505) B210505
theorem B707039 : Blo 123787 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B281087 : Blo 123787 281087 := bstep (se 1 (by rfl) ⟨210815, by rfl⟩ : syracuseStep 281087 = 421631) B421631
theorem B151967 : Blo 123787 151967 := bstep (se 1 (by rfl) ⟨113975, by rfl⟩ : syracuseStep 151967 = 227951) B227951
theorem B545231 : Blo 123787 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B283967 : Blo 123787 283967 := bstep (se 1 (by rfl) ⟨212975, by rfl⟩ : syracuseStep 283967 = 425951) B425951
theorem B185759 : Blo 123787 185759 := bstep (se 1 (by rfl) ⟨139319, by rfl⟩ : syracuseStep 185759 = 278639) B278639
theorem B284201 : Blo 123787 284201 := bstep (se 2 (by rfl) ⟨106575, by rfl⟩ : syracuseStep 284201 = 213151) B213151
theorem B4118363 : Blo 123787 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B808825 : Blo 123787 808825 := bstep (se 2 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 808825 = 606619) B606619
theorem B186623 : Blo 123787 186623 := bstep (se 1 (by rfl) ⟨139967, by rfl⟩ : syracuseStep 186623 = 279935) B279935
theorem B4414283 : Blo 123787 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B482719 : Blo 123787 482719 := bstep (se 1 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 482719 = 724079) B724079
theorem B549343 : Blo 123787 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B189083 : Blo 123787 189083 := bstep (se 1 (by rfl) ⟨141812, by rfl⟩ : syracuseStep 189083 = 283625) B283625
theorem B124575 : Blo 123787 124575 := bstep (se 1 (by rfl) ⟨93431, by rfl⟩ : syracuseStep 124575 = 186863) B186863
theorem B125039 : Blo 123787 125039 := bstep (se 1 (by rfl) ⟨93779, by rfl⟩ : syracuseStep 125039 = 187559) B187559
theorem B1436129 : Blo 123787 1436129 := bstep (se 2 (by rfl) ⟨538548, by rfl⟩ : syracuseStep 1436129 = 1077097) B1077097
theorem B125607 : Blo 123787 125607 := bstep (se 1 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 125607 = 188411) B188411
theorem B127227 : Blo 123787 127227 := bstep (se 1 (by rfl) ⟨95420, by rfl⟩ : syracuseStep 127227 = 190841) B190841
theorem B127295 : Blo 123787 127295 := bstep (se 1 (by rfl) ⟨95471, by rfl⟩ : syracuseStep 127295 = 190943) B190943
theorem B127727 : Blo 123787 127727 := bstep (se 1 (by rfl) ⟨95795, by rfl⟩ : syracuseStep 127727 = 191591) B191591
theorem B16152817 : Blo 123787 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B363487 : Blo 123787 363487 := bstep (se 1 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 363487 = 545231) B545231
theorem B5378075 : Blo 123787 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B9934073 : Blo 123787 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B957419 : Blo 123787 957419 := bstep (se 1 (by rfl) ⟨718064, by rfl⟩ : syracuseStep 957419 = 1436129) B1436129
theorem B203879 : Blo 123787 203879 := bstep (se 1 (by rfl) ⟨152909, by rfl⟩ : syracuseStep 203879 = 305819) B305819
theorem B21537089 : Blo 123787 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B633257 : Blo 123787 633257 := bstep (se 2 (by rfl) ⟨237471, by rfl⟩ : syracuseStep 633257 = 474943) B474943
theorem B1617083 : Blo 123787 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B405245 : Blo 123787 405245 := bstep (se 3 (by rfl) ⟨75983, by rfl⟩ : syracuseStep 405245 = 151967) B151967
theorem B634715 : Blo 123787 634715 := bstep (se 1 (by rfl) ⟨476036, by rfl⟩ : syracuseStep 634715 = 952073) B952073
theorem B635039 : Blo 123787 635039 := bstep (se 1 (by rfl) ⟨476279, by rfl⟩ : syracuseStep 635039 = 952559) B952559
theorem B471359 : Blo 123787 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B1552763 : Blo 123787 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B2929829 : Blo 123787 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B1226087 : Blo 123787 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B13811471 : Blo 123787 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B641519 : Blo 123787 641519 := bstep (se 1 (by rfl) ⟨481139, by rfl⟩ : syracuseStep 641519 = 962279) B962279
theorem B643625 : Blo 123787 643625 := bstep (se 2 (by rfl) ⟨241359, by rfl⟩ : syracuseStep 643625 = 482719) B482719
theorem B284543 : Blo 123787 284543 := bstep (se 1 (by rfl) ⟨213407, by rfl⟩ : syracuseStep 284543 = 426815) B426815
theorem B1202663 : Blo 123787 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B187049 : Blo 123787 187049 := bstep (se 2 (by rfl) ⟨70143, by rfl⟩ : syracuseStep 187049 = 140287) B140287
theorem B187115 : Blo 123787 187115 := bstep (se 1 (by rfl) ⟨140336, by rfl⟩ : syracuseStep 187115 = 280673) B280673
theorem B187391 : Blo 123787 187391 := bstep (se 1 (by rfl) ⟨140543, by rfl⟩ : syracuseStep 187391 = 281087) B281087
theorem B220159 : Blo 123787 220159 := bstep (se 1 (by rfl) ⟨165119, by rfl⟩ : syracuseStep 220159 = 330239) B330239
theorem B188537 : Blo 123787 188537 := bstep (se 2 (by rfl) ⟨70701, by rfl⟩ : syracuseStep 188537 = 141403) B141403
theorem B189311 : Blo 123787 189311 := bstep (se 1 (by rfl) ⟨141983, by rfl⟩ : syracuseStep 189311 = 283967) B283967
theorem B123839 : Blo 123787 123839 := bstep (se 1 (by rfl) ⟨92879, by rfl⟩ : syracuseStep 123839 = 185759) B185759
theorem B189467 : Blo 123787 189467 := bstep (se 1 (by rfl) ⟨142100, by rfl⟩ : syracuseStep 189467 = 284201) B284201
theorem B2745575 : Blo 123787 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B353747 : Blo 123787 353747 := bstep (se 1 (by rfl) ⟨265310, by rfl⟩ : syracuseStep 353747 = 530621) B530621
theorem B320993 : Blo 123787 320993 := bstep (se 2 (by rfl) ⟨120372, by rfl⟩ : syracuseStep 320993 = 240745) B240745
theorem B124415 : Blo 123787 124415 := bstep (se 1 (by rfl) ⟨93311, by rfl⟩ : syracuseStep 124415 = 186623) B186623
theorem B157231 : Blo 123787 157231 := bstep (se 1 (by rfl) ⟨117923, by rfl⟩ : syracuseStep 157231 = 235847) B235847
theorem B2942855 : Blo 123787 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B126055 : Blo 123787 126055 := bstep (se 1 (by rfl) ⟨94541, by rfl⟩ : syracuseStep 126055 = 189083) B189083
theorem B814643 : Blo 123787 814643 := bstep (se 1 (by rfl) ⟨610982, by rfl⟩ : syracuseStep 814643 = 1221965) B1221965
theorem B2977769 : Blo 123787 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B159995 : Blo 123787 159995 := bstep (se 1 (by rfl) ⟨119996, by rfl⟩ : syracuseStep 159995 = 239993) B239993
theorem B5206463 : Blo 123787 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B1078433 : Blo 123787 1078433 := bstep (se 2 (by rfl) ⟨404412, by rfl⟩ : syracuseStep 1078433 = 808825) B808825
theorem B423251 : Blo 123787 423251 := bstep (se 1 (by rfl) ⟨317438, by rfl⟩ : syracuseStep 423251 = 634877) B634877
theorem B426653 : Blo 123787 426653 := bstep (se 3 (by rfl) ⟨79997, by rfl⟩ : syracuseStep 426653 = 159995) B159995
theorem B427679 : Blo 123787 427679 := bstep (se 1 (by rfl) ⟨320759, by rfl⟩ : syracuseStep 427679 = 641519) B641519
theorem B429083 : Blo 123787 429083 := bstep (se 1 (by rfl) ⟨321812, by rfl⟩ : syracuseStep 429083 = 643625) B643625
theorem B6622715 : Blo 123787 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B135919 : Blo 123787 135919 := bstep (se 1 (by rfl) ⟨101939, by rfl⟩ : syracuseStep 135919 = 203879) B203879
theorem B14358059 : Blo 123787 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B270163 : Blo 123787 270163 := bstep (se 1 (by rfl) ⟨202622, by rfl⟩ : syracuseStep 270163 = 405245) B405245
theorem B7940717 : Blo 123787 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B209641 : Blo 123787 209641 := bstep (se 2 (by rfl) ⟨78615, by rfl⟩ : syracuseStep 209641 = 157231) B157231
theorem B3585383 : Blo 123787 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B7812877 : Blo 123787 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B801775 : Blo 123787 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B638279 : Blo 123787 638279 := bstep (se 1 (by rfl) ⟨478709, by rfl⟩ : syracuseStep 638279 = 957419) B957419
theorem B213995 : Blo 123787 213995 := bstep (se 1 (by rfl) ⟨160496, by rfl⟩ : syracuseStep 213995 = 320993) B320993
theorem B543095 : Blo 123787 543095 := bstep (se 1 (by rfl) ⟨407321, by rfl⟩ : syracuseStep 543095 = 814643) B814643
theorem B314239 : Blo 123787 314239 := bstep (se 1 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 314239 = 471359) B471359
theorem B1035175 : Blo 123787 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B282167 : Blo 123787 282167 := bstep (se 1 (by rfl) ⟨211625, by rfl⟩ : syracuseStep 282167 = 423251) B423251
theorem B943325 : Blo 123787 943325 := bstep (se 3 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 943325 = 353747) B353747
theorem B189695 : Blo 123787 189695 := bstep (se 1 (by rfl) ⟨142271, by rfl⟩ : syracuseStep 189695 = 284543) B284543
theorem B484649 : Blo 123787 484649 := bstep (se 2 (by rfl) ⟨181743, by rfl⟩ : syracuseStep 484649 = 363487) B363487
theorem B124699 : Blo 123787 124699 := bstep (se 1 (by rfl) ⟨93524, by rfl⟩ : syracuseStep 124699 = 187049) B187049
theorem B124743 : Blo 123787 124743 := bstep (se 1 (by rfl) ⟨93557, by rfl⟩ : syracuseStep 124743 = 187115) B187115
theorem B124927 : Blo 123787 124927 := bstep (se 1 (by rfl) ⟨93695, by rfl⟩ : syracuseStep 124927 = 187391) B187391
theorem B1174181 : Blo 123787 1174181 := bstep (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) B220159
theorem B125691 : Blo 123787 125691 := bstep (se 1 (by rfl) ⟨94268, by rfl⟩ : syracuseStep 125691 = 188537) B188537
theorem B126207 : Blo 123787 126207 := bstep (se 1 (by rfl) ⟨94655, by rfl⟩ : syracuseStep 126207 = 189311) B189311
theorem B126311 : Blo 123787 126311 := bstep (se 1 (by rfl) ⟨94733, by rfl⟩ : syracuseStep 126311 = 189467) B189467
theorem B1830383 : Blo 123787 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B1961903 : Blo 123787 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B422171 : Blo 123787 422171 := bstep (se 1 (by rfl) ⟨316628, by rfl⟩ : syracuseStep 422171 = 633257) B633257
theorem B1078055 : Blo 123787 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B423143 : Blo 123787 423143 := bstep (se 1 (by rfl) ⟨317357, by rfl⟩ : syracuseStep 423143 = 634715) B634715
theorem B423359 : Blo 123787 423359 := bstep (se 1 (by rfl) ⟨317519, by rfl⟩ : syracuseStep 423359 = 635039) B635039
theorem B3470975 : Blo 123787 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B718955 : Blo 123787 718955 := bstep (se 1 (by rfl) ⟨539216, by rfl⟩ : syracuseStep 718955 = 1078433) B1078433
theorem B817391 : Blo 123787 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B9207647 : Blo 123787 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B362063 : Blo 123787 362063 := bstep (se 1 (by rfl) ⟨271547, by rfl⟩ : syracuseStep 362063 = 543095) B543095
theorem B9572039 : Blo 123787 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1380233 : Blo 123787 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B628883 : Blo 123787 628883 := bstep (se 1 (by rfl) ⟨471662, by rfl⟩ : syracuseStep 628883 = 943325) B943325
theorem B1220255 : Blo 123787 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B6138431 : Blo 123787 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B142663 : Blo 123787 142663 := bstep (se 1 (by rfl) ⟨106997, by rfl⟩ : syracuseStep 142663 = 213995) B213995
theorem B2179709 : Blo 123787 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B279521 : Blo 123787 279521 := bstep (se 2 (by rfl) ⟨104820, by rfl⟩ : syracuseStep 279521 = 209641) B209641
theorem B181225 : Blo 123787 181225 := bstep (se 2 (by rfl) ⟨67959, by rfl⟩ : syracuseStep 181225 = 135919) B135919
theorem B5293811 : Blo 123787 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B3131149 : Blo 123787 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B281447 : Blo 123787 281447 := bstep (se 1 (by rfl) ⟨211085, by rfl⟩ : syracuseStep 281447 = 422171) B422171
theorem B282095 : Blo 123787 282095 := bstep (se 1 (by rfl) ⟨211571, by rfl⟩ : syracuseStep 282095 = 423143) B423143
theorem B282239 : Blo 123787 282239 := bstep (se 1 (by rfl) ⟨211679, by rfl⟩ : syracuseStep 282239 = 423359) B423359
theorem B2313983 : Blo 123787 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B1069033 : Blo 123787 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B479303 : Blo 123787 479303 := bstep (se 1 (by rfl) ⟨359477, by rfl⟩ : syracuseStep 479303 = 718955) B718955
theorem B284435 : Blo 123787 284435 := bstep (se 1 (by rfl) ⟨213326, by rfl⟩ : syracuseStep 284435 = 426653) B426653
theorem B285119 : Blo 123787 285119 := bstep (se 1 (by rfl) ⟨213839, by rfl⟩ : syracuseStep 285119 = 427679) B427679
theorem B286055 : Blo 123787 286055 := bstep (se 1 (by rfl) ⟨214541, by rfl⟩ : syracuseStep 286055 = 429083) B429083
theorem B4415143 : Blo 123787 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B188111 : Blo 123787 188111 := bstep (se 1 (by rfl) ⟨141083, by rfl⟩ : syracuseStep 188111 = 282167) B282167
theorem B418985 : Blo 123787 418985 := bstep (se 2 (by rfl) ⟨157119, by rfl⟩ : syracuseStep 418985 = 314239) B314239
theorem B126463 : Blo 123787 126463 := bstep (se 1 (by rfl) ⟨94847, by rfl⟩ : syracuseStep 126463 = 189695) B189695
theorem B323099 : Blo 123787 323099 := bstep (se 1 (by rfl) ⟨242324, by rfl⟩ : syracuseStep 323099 = 484649) B484649
theorem B10417169 : Blo 123787 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B1307935 : Blo 123787 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B718703 : Blo 123787 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B2390255 : Blo 123787 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B425519 : Blo 123787 425519 := bstep (se 1 (by rfl) ⟨319139, by rfl⟩ : syracuseStep 425519 = 638279) B638279
theorem B360217 : Blo 123787 360217 := bstep (se 2 (by rfl) ⟨135081, by rfl⟩ : syracuseStep 360217 = 270163) B270163
theorem B1542655 : Blo 123787 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B920155 : Blo 123787 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B1743913 : Blo 123787 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B1453139 : Blo 123787 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B241375 : Blo 123787 241375 := bstep (se 1 (by rfl) ⟨181031, by rfl⟩ : syracuseStep 241375 = 362063) B362063
theorem B241633 : Blo 123787 241633 := bstep (se 2 (by rfl) ⟨90612, by rfl⟩ : syracuseStep 241633 = 181225) B181225
theorem B4174865 : Blo 123787 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B1425377 : Blo 123787 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B279323 : Blo 123787 279323 := bstep (se 1 (by rfl) ⟨209492, by rfl⟩ : syracuseStep 279323 = 418985) B418985
theorem B215399 : Blo 123787 215399 := bstep (se 1 (by rfl) ⟨161549, by rfl⟩ : syracuseStep 215399 = 323099) B323099
theorem B479135 : Blo 123787 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B1593503 : Blo 123787 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B5886857 : Blo 123787 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B283679 : Blo 123787 283679 := bstep (se 1 (by rfl) ⟨212759, by rfl⟩ : syracuseStep 283679 = 425519) B425519
theorem B480289 : Blo 123787 480289 := bstep (se 2 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 480289 = 360217) B360217
theorem B186347 : Blo 123787 186347 := bstep (se 1 (by rfl) ⟨139760, by rfl⟩ : syracuseStep 186347 = 279521) B279521
theorem B3529207 : Blo 123787 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B187631 : Blo 123787 187631 := bstep (se 1 (by rfl) ⟨140723, by rfl⟩ : syracuseStep 187631 = 281447) B281447
theorem B188063 : Blo 123787 188063 := bstep (se 1 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 188063 = 282095) B282095
theorem B188159 : Blo 123787 188159 := bstep (se 1 (by rfl) ⟨141119, by rfl⟩ : syracuseStep 188159 = 282239) B282239
theorem B6381359 : Blo 123787 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B319535 : Blo 123787 319535 := bstep (se 1 (by rfl) ⟨239651, by rfl⟩ : syracuseStep 319535 = 479303) B479303
theorem B189623 : Blo 123787 189623 := bstep (se 1 (by rfl) ⟨142217, by rfl⟩ : syracuseStep 189623 = 284435) B284435
theorem B419255 : Blo 123787 419255 := bstep (se 1 (by rfl) ⟨314441, by rfl⟩ : syracuseStep 419255 = 628883) B628883
theorem B190079 : Blo 123787 190079 := bstep (se 1 (by rfl) ⟨142559, by rfl⟩ : syracuseStep 190079 = 285119) B285119
theorem B190217 : Blo 123787 190217 := bstep (se 2 (by rfl) ⟨71331, by rfl⟩ : syracuseStep 190217 = 142663) B142663
theorem B190703 : Blo 123787 190703 := bstep (se 1 (by rfl) ⟨143027, by rfl⟩ : syracuseStep 190703 = 286055) B286055
theorem B813503 : Blo 123787 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B125407 : Blo 123787 125407 := bstep (se 1 (by rfl) ⟨94055, by rfl⟩ : syracuseStep 125407 = 188111) B188111
theorem B4092287 : Blo 123787 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B6944779 : Blo 123787 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B10912765 : Blo 123787 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B8227493 : Blo 123787 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B143599 : Blo 123787 143599 := bstep (se 1 (by rfl) ⟨107699, by rfl⟩ : syracuseStep 143599 = 215399) B215399
theorem B1062335 : Blo 123787 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B1226873 : Blo 123787 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B213023 : Blo 123787 213023 := bstep (se 1 (by rfl) ⟨159767, by rfl⟩ : syracuseStep 213023 = 319535) B319535
theorem B279503 : Blo 123787 279503 := bstep (se 1 (by rfl) ⟨209627, by rfl⟩ : syracuseStep 279503 = 419255) B419255
theorem B640385 : Blo 123787 640385 := bstep (se 2 (by rfl) ⟨240144, by rfl⟩ : syracuseStep 640385 = 480289) B480289
theorem B542335 : Blo 123787 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B968759 : Blo 123787 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B9259705 : Blo 123787 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B4705609 : Blo 123787 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B186215 : Blo 123787 186215 := bstep (se 1 (by rfl) ⟨139661, by rfl⟩ : syracuseStep 186215 = 279323) B279323
theorem B319423 : Blo 123787 319423 := bstep (se 1 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 319423 = 479135) B479135
theorem B3924571 : Blo 123787 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B189119 : Blo 123787 189119 := bstep (se 1 (by rfl) ⟨141839, by rfl⟩ : syracuseStep 189119 = 283679) B283679
theorem B124231 : Blo 123787 124231 := bstep (se 1 (by rfl) ⟨93173, by rfl⟩ : syracuseStep 124231 = 186347) B186347
theorem B125087 : Blo 123787 125087 := bstep (se 1 (by rfl) ⟨93815, by rfl⟩ : syracuseStep 125087 = 187631) B187631
theorem B321833 : Blo 123787 321833 := bstep (se 2 (by rfl) ⟨120687, by rfl⟩ : syracuseStep 321833 = 241375) B241375
theorem B125375 : Blo 123787 125375 := bstep (se 1 (by rfl) ⟨94031, by rfl⟩ : syracuseStep 125375 = 188063) B188063
theorem B125439 : Blo 123787 125439 := bstep (se 1 (by rfl) ⟨94079, by rfl⟩ : syracuseStep 125439 = 188159) B188159
theorem B4254239 : Blo 123787 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B322177 : Blo 123787 322177 := bstep (se 2 (by rfl) ⟨120816, by rfl⟩ : syracuseStep 322177 = 241633) B241633
theorem B126415 : Blo 123787 126415 := bstep (se 1 (by rfl) ⟨94811, by rfl⟩ : syracuseStep 126415 = 189623) B189623
theorem B126719 : Blo 123787 126719 := bstep (se 1 (by rfl) ⟨95039, by rfl⟩ : syracuseStep 126719 = 190079) B190079
theorem B126811 : Blo 123787 126811 := bstep (se 1 (by rfl) ⟨95108, by rfl⟩ : syracuseStep 126811 = 190217) B190217
theorem B127135 : Blo 123787 127135 := bstep (se 1 (by rfl) ⟨95351, by rfl⟩ : syracuseStep 127135 = 190703) B190703
theorem B2783243 : Blo 123787 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B2325217 : Blo 123787 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B3801005 : Blo 123787 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B426923 : Blo 123787 426923 := bstep (se 1 (by rfl) ⟨320192, by rfl⟩ : syracuseStep 426923 = 640385) B640385
theorem B14550353 : Blo 123787 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B723113 : Blo 123787 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B429569 : Blo 123787 429569 := bstep (se 2 (by rfl) ⟨161088, by rfl⟩ : syracuseStep 429569 = 322177) B322177
theorem B11344637 : Blo 123787 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2534003 : Blo 123787 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B142015 : Blo 123787 142015 := bstep (se 1 (by rfl) ⟨106511, by rfl⟩ : syracuseStep 142015 = 213023) B213023
theorem B5484995 : Blo 123787 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B6274145 : Blo 123787 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B214555 : Blo 123787 214555 := bstep (se 1 (by rfl) ⟨160916, by rfl⟩ : syracuseStep 214555 = 321833) B321833
theorem B708223 : Blo 123787 708223 := bstep (se 1 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 708223 = 1062335) B1062335
theorem B3100289 : Blo 123787 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B1855495 : Blo 123787 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B186335 : Blo 123787 186335 := bstep (se 1 (by rfl) ⟨139751, by rfl⟩ : syracuseStep 186335 = 279503) B279503
theorem B5232761 : Blo 123787 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B645839 : Blo 123787 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B12346273 : Blo 123787 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B124143 : Blo 123787 124143 := bstep (se 1 (by rfl) ⟨93107, by rfl⟩ : syracuseStep 124143 = 186215) B186215
theorem B191465 : Blo 123787 191465 := bstep (se 2 (by rfl) ⟨71799, by rfl⟩ : syracuseStep 191465 = 143599) B143599
theorem B3271661 : Blo 123787 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B126079 : Blo 123787 126079 := bstep (se 1 (by rfl) ⟨94559, by rfl⟩ : syracuseStep 126079 = 189119) B189119
theorem B425897 : Blo 123787 425897 := bstep (se 2 (by rfl) ⟨159711, by rfl⟩ : syracuseStep 425897 = 319423) B319423
theorem B9700235 : Blo 123787 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B430559 : Blo 123787 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B8267437 : Blo 123787 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B3488507 : Blo 123787 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B65846789 : Blo 123787 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B2473993 : Blo 123787 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B1689335 : Blo 123787 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B2181107 : Blo 123787 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B3656663 : Blo 123787 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B4182763 : Blo 123787 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B283931 : Blo 123787 283931 := bstep (se 1 (by rfl) ⟨212948, by rfl⟩ : syracuseStep 283931 = 425897) B425897
theorem B284615 : Blo 123787 284615 := bstep (se 1 (by rfl) ⟨213461, by rfl⟩ : syracuseStep 284615 = 426923) B426923
theorem B482075 : Blo 123787 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B286073 : Blo 123787 286073 := bstep (se 2 (by rfl) ⟨107277, by rfl⟩ : syracuseStep 286073 = 214555) B214555
theorem B286379 : Blo 123787 286379 := bstep (se 1 (by rfl) ⟨214784, by rfl⟩ : syracuseStep 286379 = 429569) B429569
theorem B189353 : Blo 123787 189353 := bstep (se 2 (by rfl) ⟨71007, by rfl⟩ : syracuseStep 189353 = 142015) B142015
theorem B124223 : Blo 123787 124223 := bstep (se 1 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 124223 = 186335) B186335
theorem B7563091 : Blo 123787 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B944297 : Blo 123787 944297 := bstep (se 2 (by rfl) ⟨354111, by rfl⟩ : syracuseStep 944297 = 708223) B708223
theorem B127643 : Blo 123787 127643 := bstep (se 1 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 127643 = 191465) B191465
theorem B5577017 : Blo 123787 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B629531 : Blo 123787 629531 := bstep (se 1 (by rfl) ⟨472148, by rfl⟩ : syracuseStep 629531 = 944297) B944297
theorem B6466823 : Blo 123787 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B1126223 : Blo 123787 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B1454071 : Blo 123787 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B2437775 : Blo 123787 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B44092997 : Blo 123787 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B43897859 : Blo 123787 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B3298657 : Blo 123787 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B10084121 : Blo 123787 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B287039 : Blo 123787 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B189287 : Blo 123787 189287 := bstep (se 1 (by rfl) ⟨141965, by rfl⟩ : syracuseStep 189287 = 283931) B283931
theorem B189743 : Blo 123787 189743 := bstep (se 1 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 189743 = 284615) B284615
theorem B321383 : Blo 123787 321383 := bstep (se 1 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 321383 = 482075) B482075
theorem B190715 : Blo 123787 190715 := bstep (se 1 (by rfl) ⟨143036, by rfl⟩ : syracuseStep 190715 = 286073) B286073
theorem B190919 : Blo 123787 190919 := bstep (se 1 (by rfl) ⟨143189, by rfl⟩ : syracuseStep 190919 = 286379) B286379
theorem B126235 : Blo 123787 126235 := bstep (se 1 (by rfl) ⟨94676, by rfl⟩ : syracuseStep 126235 = 189353) B189353
theorem B2325671 : Blo 123787 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B29395331 : Blo 123787 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B29265239 : Blo 123787 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B6722747 : Blo 123787 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B1938761 : Blo 123787 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B4398209 : Blo 123787 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B1550447 : Blo 123787 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B214255 : Blo 123787 214255 := bstep (se 1 (by rfl) ⟨160691, by rfl⟩ : syracuseStep 214255 = 321383) B321383
theorem B4311215 : Blo 123787 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1625183 : Blo 123787 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B419687 : Blo 123787 419687 := bstep (se 1 (by rfl) ⟨314765, by rfl⟩ : syracuseStep 419687 = 629531) B629531
theorem B191359 : Blo 123787 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B126191 : Blo 123787 126191 := bstep (se 1 (by rfl) ⟨94643, by rfl⟩ : syracuseStep 126191 = 189287) B189287
theorem B14872045 : Blo 123787 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B126495 : Blo 123787 126495 := bstep (se 1 (by rfl) ⟨94871, by rfl⟩ : syracuseStep 126495 = 189743) B189743
theorem B127143 : Blo 123787 127143 := bstep (se 1 (by rfl) ⟨95357, by rfl⟩ : syracuseStep 127143 = 190715) B190715
theorem B127279 : Blo 123787 127279 := bstep (se 1 (by rfl) ⟨95459, by rfl⟩ : syracuseStep 127279 = 190919) B190919
theorem B750815 : Blo 123787 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B19596887 : Blo 123787 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B1083455 : Blo 123787 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B19829393 : Blo 123787 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B500543 : Blo 123787 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B19510159 : Blo 123787 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B1292507 : Blo 123787 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B2932139 : Blo 123787 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B279791 : Blo 123787 279791 := bstep (se 1 (by rfl) ⟨209843, by rfl⟩ : syracuseStep 279791 = 419687) B419687
theorem B1033631 : Blo 123787 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B2874143 : Blo 123787 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B4481831 : Blo 123787 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B255145 : Blo 123787 255145 := bstep (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) B191359
theorem B1142693 : Blo 123787 1142693 := bstep (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) B214255
theorem B689087 : Blo 123787 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B722303 : Blo 123787 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B2987887 : Blo 123787 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B333695 : Blo 123787 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B761795 : Blo 123787 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B861671 : Blo 123787 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B340193 : Blo 123787 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B13219595 : Blo 123787 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B1916095 : Blo 123787 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B1954759 : Blo 123787 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B186527 : Blo 123787 186527 := bstep (se 1 (by rfl) ⟨139895, by rfl⟩ : syracuseStep 186527 = 279791) B279791
theorem B13064591 : Blo 123787 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B26013545 : Blo 123787 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B459391 : Blo 123787 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B17342363 : Blo 123787 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B507863 : Blo 123787 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B574447 : Blo 123787 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B2606345 : Blo 123787 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B3983849 : Blo 123787 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B481535 : Blo 123787 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B222463 : Blo 123787 222463 := bstep (se 1 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 222463 = 333695) B333695
theorem B124351 : Blo 123787 124351 := bstep (se 1 (by rfl) ⟨93263, by rfl⟩ : syracuseStep 124351 = 186527) B186527
theorem B8709727 : Blo 123787 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B226795 : Blo 123787 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B8813063 : Blo 123787 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B2554793 : Blo 123787 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B1737563 : Blo 123787 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B2655899 : Blo 123787 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B296617 : Blo 123787 296617 := bstep (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) B222463
theorem B23501501 : Blo 123787 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B302393 : Blo 123787 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B338575 : Blo 123787 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B765929 : Blo 123787 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B11612969 : Blo 123787 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B612521 : Blo 123787 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B321023 : Blo 123787 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B11561575 : Blo 123787 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B1703195 : Blo 123787 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B1770599 : Blo 123787 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B395489 : Blo 123787 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B15667667 : Blo 123787 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B7741979 : Blo 123787 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B15415433 : Blo 123787 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B408347 : Blo 123787 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B214015 : Blo 123787 214015 := bstep (se 1 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 214015 = 321023) B321023
theorem B510619 : Blo 123787 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B806381 : Blo 123787 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B18534005 : Blo 123787 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B1135463 : Blo 123787 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B451433 : Blo 123787 451433 := bstep (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) B338575
theorem B12356003 : Blo 123787 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B4721597 : Blo 123787 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B1054637 : Blo 123787 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B272231 : Blo 123787 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B3027901 : Blo 123787 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B537587 : Blo 123787 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B5161319 : Blo 123787 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B10276955 : Blo 123787 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B285353 : Blo 123787 285353 := bstep (se 2 (by rfl) ⟨107007, by rfl⟩ : syracuseStep 285353 = 214015) B214015
theorem B1203821 : Blo 123787 1203821 := bstep (se 3 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 1203821 = 451433) B451433
theorem B10445111 : Blo 123787 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B680825 : Blo 123787 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B3440879 : Blo 123787 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B3147731 : Blo 123787 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B6851303 : Blo 123787 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B4037201 : Blo 123787 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B8237335 : Blo 123787 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B703091 : Blo 123787 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B802547 : Blo 123787 802547 := bstep (se 1 (by rfl) ⟨601910, by rfl⟩ : syracuseStep 802547 = 1203821) B1203821
theorem B6963407 : Blo 123787 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B181487 : Blo 123787 181487 := bstep (se 1 (by rfl) ⟨136115, by rfl⟩ : syracuseStep 181487 = 272231) B272231
theorem B190235 : Blo 123787 190235 := bstep (se 1 (by rfl) ⟨142676, by rfl⟩ : syracuseStep 190235 = 285353) B285353
theorem B453883 : Blo 123787 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B358391 : Blo 123787 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B2293919 : Blo 123787 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B2098487 : Blo 123787 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B2691467 : Blo 123787 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B955709 : Blo 123787 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B10983113 : Blo 123787 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B1874909 : Blo 123787 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B535031 : Blo 123787 535031 := bstep (se 1 (by rfl) ⟨401273, by rfl⟩ : syracuseStep 535031 = 802547) B802547
theorem B4567535 : Blo 123787 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B605177 : Blo 123787 605177 := bstep (se 2 (by rfl) ⟨226941, by rfl⟩ : syracuseStep 605177 = 453883) B453883
theorem B4642271 : Blo 123787 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B483965 : Blo 123787 483965 := bstep (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) B181487
theorem B126823 : Blo 123787 126823 := bstep (se 1 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 126823 = 190235) B190235
theorem B1249939 : Blo 123787 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B403451 : Blo 123787 403451 := bstep (se 1 (by rfl) ⟨302588, by rfl⟩ : syracuseStep 403451 = 605177) B605177
theorem B637139 : Blo 123787 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B3094847 : Blo 123787 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B7322075 : Blo 123787 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B1529279 : Blo 123787 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B1794311 : Blo 123787 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B5595965 : Blo 123787 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B322643 : Blo 123787 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B356687 : Blo 123787 356687 := bstep (se 1 (by rfl) ⟨267515, by rfl⟩ : syracuseStep 356687 = 535031) B535031
theorem B3045023 : Blo 123787 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B1019519 : Blo 123787 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B268967 : Blo 123787 268967 := bstep (se 1 (by rfl) ⟨201725, by rfl⟩ : syracuseStep 268967 = 403451) B403451
theorem B237791 : Blo 123787 237791 := bstep (se 1 (by rfl) ⟨178343, by rfl⟩ : syracuseStep 237791 = 356687) B356687
theorem B1196207 : Blo 123787 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B215095 : Blo 123787 215095 := bstep (se 1 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 215095 = 322643) B322643
theorem B3730643 : Blo 123787 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B1666585 : Blo 123787 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B2030015 : Blo 123787 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B424759 : Blo 123787 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B2063231 : Blo 123787 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B4881383 : Blo 123787 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B566345 : Blo 123787 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B1353343 : Blo 123787 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B3254255 : Blo 123787 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B797471 : Blo 123787 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B679679 : Blo 123787 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B286793 : Blo 123787 286793 := bstep (se 2 (by rfl) ⟨107547, by rfl⟩ : syracuseStep 286793 = 215095) B215095
theorem B2222113 : Blo 123787 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B158527 : Blo 123787 158527 := bstep (se 1 (by rfl) ⟨118895, by rfl⟩ : syracuseStep 158527 = 237791) B237791
theorem B717245 : Blo 123787 717245 := bstep (se 3 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 717245 = 268967) B268967
theorem B2487095 : Blo 123787 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B1375487 : Blo 123787 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B1804457 : Blo 123787 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B2169503 : Blo 123787 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B531647 : Blo 123787 531647 := bstep (se 1 (by rfl) ⟨398735, by rfl⟩ : syracuseStep 531647 = 797471) B797471
theorem B2962817 : Blo 123787 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B211369 : Blo 123787 211369 := bstep (se 2 (by rfl) ⟨79263, by rfl⟩ : syracuseStep 211369 = 158527) B158527
theorem B377563 : Blo 123787 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B478163 : Blo 123787 478163 := bstep (se 1 (by rfl) ⟨358622, by rfl⟩ : syracuseStep 478163 = 717245) B717245
theorem B1658063 : Blo 123787 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B453119 : Blo 123787 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B191195 : Blo 123787 191195 := bstep (se 1 (by rfl) ⟨143396, by rfl⟩ : syracuseStep 191195 = 286793) B286793
theorem B916991 : Blo 123787 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B1446335 : Blo 123787 1446335 := bstep (se 1 (by rfl) ⟨1084751, by rfl⟩ : syracuseStep 1446335 = 2169503) B2169503
theorem B1975211 : Blo 123787 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B503417 : Blo 123787 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B281825 : Blo 123787 281825 := bstep (se 2 (by rfl) ⟨105684, by rfl⟩ : syracuseStep 281825 = 211369) B211369
theorem B611327 : Blo 123787 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B1202971 : Blo 123787 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B318775 : Blo 123787 318775 := bstep (se 1 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 318775 = 478163) B478163
theorem B1105375 : Blo 123787 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B354431 : Blo 123787 354431 := bstep (se 1 (by rfl) ⟨265823, by rfl⟩ : syracuseStep 354431 = 531647) B531647
theorem B1208317 : Blo 123787 1208317 := bstep (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) B453119
theorem B127463 : Blo 123787 127463 := bstep (se 1 (by rfl) ⟨95597, by rfl⟩ : syracuseStep 127463 = 191195) B191195
theorem B1611089 : Blo 123787 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B1316807 : Blo 123787 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B236287 : Blo 123787 236287 := bstep (se 1 (by rfl) ⟨177215, by rfl⟩ : syracuseStep 236287 = 354431) B354431
theorem B335611 : Blo 123787 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B964223 : Blo 123787 964223 := bstep (se 1 (by rfl) ⟨723167, by rfl⟩ : syracuseStep 964223 = 1446335) B1446335
theorem B187883 : Blo 123787 187883 := bstep (se 1 (by rfl) ⟨140912, by rfl⟩ : syracuseStep 187883 = 281825) B281825
theorem B1630205 : Blo 123787 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B1603961 : Blo 123787 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B425033 : Blo 123787 425033 := bstep (se 2 (by rfl) ⟨159387, by rfl⟩ : syracuseStep 425033 = 318775) B318775
theorem B1473833 : Blo 123787 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B1086803 : Blo 123787 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B315049 : Blo 123787 315049 := bstep (se 2 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 315049 = 236287) B236287
theorem B642815 : Blo 123787 642815 := bstep (se 1 (by rfl) ⟨482111, by rfl⟩ : syracuseStep 642815 = 964223) B964223
theorem B1069307 : Blo 123787 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B283355 : Blo 123787 283355 := bstep (se 1 (by rfl) ⟨212516, by rfl⟩ : syracuseStep 283355 = 425033) B425033
theorem B447481 : Blo 123787 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B1074059 : Blo 123787 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B877871 : Blo 123787 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B125255 : Blo 123787 125255 := bstep (se 1 (by rfl) ⟨93941, by rfl⟩ : syracuseStep 125255 = 187883) B187883
theorem B3930221 : Blo 123787 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B428543 : Blo 123787 428543 := bstep (se 1 (by rfl) ⟨321407, by rfl⟩ : syracuseStep 428543 = 642815) B642815
theorem B724535 : Blo 123787 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B596641 : Blo 123787 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B712871 : Blo 123787 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B188903 : Blo 123787 188903 := bstep (se 1 (by rfl) ⟨141677, by rfl⟩ : syracuseStep 188903 = 283355) B283355
theorem B420065 : Blo 123787 420065 := bstep (se 2 (by rfl) ⟨157524, by rfl⟩ : syracuseStep 420065 = 315049) B315049
theorem B716039 : Blo 123787 716039 := bstep (se 1 (by rfl) ⟨537029, by rfl⟩ : syracuseStep 716039 = 1074059) B1074059
theorem B585247 : Blo 123787 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B2620147 : Blo 123787 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B795521 : Blo 123787 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B475247 : Blo 123787 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B280043 : Blo 123787 280043 := bstep (se 1 (by rfl) ⟨210032, by rfl⟩ : syracuseStep 280043 = 420065) B420065
theorem B477359 : Blo 123787 477359 := bstep (se 1 (by rfl) ⟨358019, by rfl⟩ : syracuseStep 477359 = 716039) B716039
theorem B3493529 : Blo 123787 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B285695 : Blo 123787 285695 := bstep (se 1 (by rfl) ⟨214271, by rfl⟩ : syracuseStep 285695 = 428543) B428543
theorem B483023 : Blo 123787 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B780329 : Blo 123787 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B125935 : Blo 123787 125935 := bstep (se 1 (by rfl) ⟨94451, by rfl⟩ : syracuseStep 125935 = 188903) B188903
theorem B2329019 : Blo 123787 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B316831 : Blo 123787 316831 := bstep (se 1 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 316831 = 475247) B475247
theorem B186695 : Blo 123787 186695 := bstep (se 1 (by rfl) ⟨140021, by rfl⟩ : syracuseStep 186695 = 280043) B280043
theorem B318239 : Blo 123787 318239 := bstep (se 1 (by rfl) ⟨238679, by rfl⟩ : syracuseStep 318239 = 477359) B477359
theorem B2121389 : Blo 123787 2121389 := bstep (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) B795521
theorem B190463 : Blo 123787 190463 := bstep (se 1 (by rfl) ⟨142847, by rfl⟩ : syracuseStep 190463 = 285695) B285695
theorem B322015 : Blo 123787 322015 := bstep (se 1 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 322015 = 483023) B483023
theorem B520219 : Blo 123787 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B429353 : Blo 123787 429353 := bstep (se 2 (by rfl) ⟨161007, by rfl⟩ : syracuseStep 429353 = 322015) B322015
theorem B1414259 : Blo 123787 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B693625 : Blo 123787 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B1552679 : Blo 123787 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B212159 : Blo 123787 212159 := bstep (se 1 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 212159 = 318239) B318239
theorem B124463 : Blo 123787 124463 := bstep (se 1 (by rfl) ⟨93347, by rfl⟩ : syracuseStep 124463 = 186695) B186695
theorem B126975 : Blo 123787 126975 := bstep (se 1 (by rfl) ⟨95231, by rfl⟩ : syracuseStep 126975 = 190463) B190463
theorem B422441 : Blo 123787 422441 := bstep (se 2 (by rfl) ⟨158415, by rfl⟩ : syracuseStep 422441 = 316831) B316831
theorem B924833 : Blo 123787 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B141439 : Blo 123787 141439 := bstep (se 1 (by rfl) ⟨106079, by rfl⟩ : syracuseStep 141439 = 212159) B212159
theorem B1035119 : Blo 123787 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B281627 : Blo 123787 281627 := bstep (se 1 (by rfl) ⟨211220, by rfl⟩ : syracuseStep 281627 = 422441) B422441
theorem B286235 : Blo 123787 286235 := bstep (se 1 (by rfl) ⟨214676, by rfl⟩ : syracuseStep 286235 = 429353) B429353
theorem B942839 : Blo 123787 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B690079 : Blo 123787 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B628559 : Blo 123787 628559 := bstep (se 1 (by rfl) ⟨471419, by rfl⟩ : syracuseStep 628559 = 942839) B942839
theorem B187751 : Blo 123787 187751 := bstep (se 1 (by rfl) ⟨140813, by rfl⟩ : syracuseStep 187751 = 281627) B281627
theorem B188585 : Blo 123787 188585 := bstep (se 2 (by rfl) ⟨70719, by rfl⟩ : syracuseStep 188585 = 141439) B141439
theorem B616555 : Blo 123787 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B190823 : Blo 123787 190823 := bstep (se 1 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 190823 = 286235) B286235
theorem B920105 : Blo 123787 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B822073 : Blo 123787 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B419039 : Blo 123787 419039 := bstep (se 1 (by rfl) ⟨314279, by rfl⟩ : syracuseStep 419039 = 628559) B628559
theorem B125167 : Blo 123787 125167 := bstep (se 1 (by rfl) ⟨93875, by rfl⟩ : syracuseStep 125167 = 187751) B187751
theorem B125723 : Blo 123787 125723 := bstep (se 1 (by rfl) ⟨94292, by rfl⟩ : syracuseStep 125723 = 188585) B188585
theorem B127215 : Blo 123787 127215 := bstep (se 1 (by rfl) ⟨95411, by rfl⟩ : syracuseStep 127215 = 190823) B190823
theorem B1096097 : Blo 123787 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B279359 : Blo 123787 279359 := bstep (se 1 (by rfl) ⟨209519, by rfl⟩ : syracuseStep 279359 = 419039) B419039
theorem B613403 : Blo 123787 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B408935 : Blo 123787 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B186239 : Blo 123787 186239 := bstep (se 1 (by rfl) ⟨139679, by rfl⟩ : syracuseStep 186239 = 279359) B279359
theorem B11691701 : Blo 123787 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B1090493 : Blo 123787 1090493 := bstep (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) B408935
theorem B124159 : Blo 123787 124159 := bstep (se 1 (by rfl) ⟨93119, by rfl⟩ : syracuseStep 124159 = 186239) B186239
theorem B7794467 : Blo 123787 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B726995 : Blo 123787 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B5196311 : Blo 123787 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B3464207 : Blo 123787 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B484663 : Blo 123787 484663 := bstep (se 1 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 484663 = 726995) B726995
theorem B2309471 : Blo 123787 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B646217 : Blo 123787 646217 := bstep (se 2 (by rfl) ⟨242331, by rfl⟩ : syracuseStep 646217 = 484663) B484663
theorem B430811 : Blo 123787 430811 := bstep (se 1 (by rfl) ⟨323108, by rfl⟩ : syracuseStep 430811 = 646217) B646217
theorem B1539647 : Blo 123787 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B1026431 : Blo 123787 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B287207 : Blo 123787 287207 := bstep (se 1 (by rfl) ⟨215405, by rfl⟩ : syracuseStep 287207 = 430811) B430811
theorem B191471 : Blo 123787 191471 := bstep (se 1 (by rfl) ⟨143603, by rfl⟩ : syracuseStep 191471 = 287207) B287207
theorem B684287 : Blo 123787 684287 := bstep (se 1 (by rfl) ⟨513215, by rfl⟩ : syracuseStep 684287 = 1026431) B1026431
theorem B127647 : Blo 123787 127647 := bstep (se 1 (by rfl) ⟨95735, by rfl⟩ : syracuseStep 127647 = 191471) B191471
theorem B456191 : Blo 123787 456191 := bstep (se 1 (by rfl) ⟨342143, by rfl⟩ : syracuseStep 456191 = 684287) B684287
theorem B304127 : Blo 123787 304127 := bstep (se 1 (by rfl) ⟨228095, by rfl⟩ : syracuseStep 304127 = 456191) B456191
theorem B202751 : Blo 123787 202751 := bstep (se 1 (by rfl) ⟨152063, by rfl⟩ : syracuseStep 202751 = 304127) B304127
theorem B135167 : Blo 123787 135167 := bstep (se 1 (by rfl) ⟨101375, by rfl⟩ : syracuseStep 135167 = 202751) B202751
theorem B360445 : Blo 123787 360445 := bstep (se 3 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 360445 = 135167) B135167
theorem B480593 : Blo 123787 480593 := bstep (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) B360445
theorem B320395 : Blo 123787 320395 := bstep (se 1 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 320395 = 480593) B480593
theorem B427193 : Blo 123787 427193 := bstep (se 2 (by rfl) ⟨160197, by rfl⟩ : syracuseStep 427193 = 320395) B320395
theorem B284795 : Blo 123787 284795 := bstep (se 1 (by rfl) ⟨213596, by rfl⟩ : syracuseStep 284795 = 427193) B427193
theorem B189863 : Blo 123787 189863 := bstep (se 1 (by rfl) ⟨142397, by rfl⟩ : syracuseStep 189863 = 284795) B284795
theorem B126575 : Blo 123787 126575 := bstep (se 1 (by rfl) ⟨94931, by rfl⟩ : syracuseStep 126575 = 189863) B189863

theorem C0 (j : ℕ) (h1 : 30946 ≤ j) (h2 : j ≤ 31645) : Blo 123787 (4 * j + 3) := by
  interval_cases j
  · exact B123787
  · exact B123791
  · exact B123795
  · exact B123799
  · exact B123803
  · exact B123807
  · exact B123811
  · exact B123815
  · exact B123819
  · exact B123823
  · exact B123827
  · exact B123831
  · exact B123835
  · exact B123839
  · exact B123843
  · exact B123847
  · exact B123851
  · exact B123855
  · exact B123859
  · exact B123863
  · exact B123867
  · exact B123871
  · exact B123875
  · exact B123879
  · exact B123883
  · exact B123887
  · exact B123891
  · exact B123895
  · exact B123899
  · exact B123903
  · exact B123907
  · exact B123911
  · exact B123915
  · exact B123919
  · exact B123923
  · exact B123927
  · exact B123931
  · exact B123935
  · exact B123939
  · exact B123943
  · exact B123947
  · exact B123951
  · exact B123955
  · exact B123959
  · exact B123963
  · exact B123967
  · exact B123971
  · exact B123975
  · exact B123979
  · exact B123983
  · exact B123987
  · exact B123991
  · exact B123995
  · exact B123999
  · exact B124003
  · exact B124007
  · exact B124011
  · exact B124015
  · exact B124019
  · exact B124023
  · exact B124027
  · exact B124031
  · exact B124035
  · exact B124039
  · exact B124043
  · exact B124047
  · exact B124051
  · exact B124055
  · exact B124059
  · exact B124063
  · exact B124067
  · exact B124071
  · exact B124075
  · exact B124079
  · exact B124083
  · exact B124087
  · exact B124091
  · exact B124095
  · exact B124099
  · exact B124103
  · exact B124107
  · exact B124111
  · exact B124115
  · exact B124119
  · exact B124123
  · exact B124127
  · exact B124131
  · exact B124135
  · exact B124139
  · exact B124143
  · exact B124147
  · exact B124151
  · exact B124155
  · exact B124159
  · exact B124163
  · exact B124167
  · exact B124171
  · exact B124175
  · exact B124179
  · exact B124183
  · exact B124187
  · exact B124191
  · exact B124195
  · exact B124199
  · exact B124203
  · exact B124207
  · exact B124211
  · exact B124215
  · exact B124219
  · exact B124223
  · exact B124227
  · exact B124231
  · exact B124235
  · exact B124239
  · exact B124243
  · exact B124247
  · exact B124251
  · exact B124255
  · exact B124259
  · exact B124263
  · exact B124267
  · exact B124271
  · exact B124275
  · exact B124279
  · exact B124283
  · exact B124287
  · exact B124291
  · exact B124295
  · exact B124299
  · exact B124303
  · exact B124307
  · exact B124311
  · exact B124315
  · exact B124319
  · exact B124323
  · exact B124327
  · exact B124331
  · exact B124335
  · exact B124339
  · exact B124343
  · exact B124347
  · exact B124351
  · exact B124355
  · exact B124359
  · exact B124363
  · exact B124367
  · exact B124371
  · exact B124375
  · exact B124379
  · exact B124383
  · exact B124387
  · exact B124391
  · exact B124395
  · exact B124399
  · exact B124403
  · exact B124407
  · exact B124411
  · exact B124415
  · exact B124419
  · exact B124423
  · exact B124427
  · exact B124431
  · exact B124435
  · exact B124439
  · exact B124443
  · exact B124447
  · exact B124451
  · exact B124455
  · exact B124459
  · exact B124463
  · exact B124467
  · exact B124471
  · exact B124475
  · exact B124479
  · exact B124483
  · exact B124487
  · exact B124491
  · exact B124495
  · exact B124499
  · exact B124503
  · exact B124507
  · exact B124511
  · exact B124515
  · exact B124519
  · exact B124523
  · exact B124527
  · exact B124531
  · exact B124535
  · exact B124539
  · exact B124543
  · exact B124547
  · exact B124551
  · exact B124555
  · exact B124559
  · exact B124563
  · exact B124567
  · exact B124571
  · exact B124575
  · exact B124579
  · exact B124583
  · exact B124587
  · exact B124591
  · exact B124595
  · exact B124599
  · exact B124603
  · exact B124607
  · exact B124611
  · exact B124615
  · exact B124619
  · exact B124623
  · exact B124627
  · exact B124631
  · exact B124635
  · exact B124639
  · exact B124643
  · exact B124647
  · exact B124651
  · exact B124655
  · exact B124659
  · exact B124663
  · exact B124667
  · exact B124671
  · exact B124675
  · exact B124679
  · exact B124683
  · exact B124687
  · exact B124691
  · exact B124695
  · exact B124699
  · exact B124703
  · exact B124707
  · exact B124711
  · exact B124715
  · exact B124719
  · exact B124723
  · exact B124727
  · exact B124731
  · exact B124735
  · exact B124739
  · exact B124743
  · exact B124747
  · exact B124751
  · exact B124755
  · exact B124759
  · exact B124763
  · exact B124767
  · exact B124771
  · exact B124775
  · exact B124779
  · exact B124783
  · exact B124787
  · exact B124791
  · exact B124795
  · exact B124799
  · exact B124803
  · exact B124807
  · exact B124811
  · exact B124815
  · exact B124819
  · exact B124823
  · exact B124827
  · exact B124831
  · exact B124835
  · exact B124839
  · exact B124843
  · exact B124847
  · exact B124851
  · exact B124855
  · exact B124859
  · exact B124863
  · exact B124867
  · exact B124871
  · exact B124875
  · exact B124879
  · exact B124883
  · exact B124887
  · exact B124891
  · exact B124895
  · exact B124899
  · exact B124903
  · exact B124907
  · exact B124911
  · exact B124915
  · exact B124919
  · exact B124923
  · exact B124927
  · exact B124931
  · exact B124935
  · exact B124939
  · exact B124943
  · exact B124947
  · exact B124951
  · exact B124955
  · exact B124959
  · exact B124963
  · exact B124967
  · exact B124971
  · exact B124975
  · exact B124979
  · exact B124983
  · exact B124987
  · exact B124991
  · exact B124995
  · exact B124999
  · exact B125003
  · exact B125007
  · exact B125011
  · exact B125015
  · exact B125019
  · exact B125023
  · exact B125027
  · exact B125031
  · exact B125035
  · exact B125039
  · exact B125043
  · exact B125047
  · exact B125051
  · exact B125055
  · exact B125059
  · exact B125063
  · exact B125067
  · exact B125071
  · exact B125075
  · exact B125079
  · exact B125083
  · exact B125087
  · exact B125091
  · exact B125095
  · exact B125099
  · exact B125103
  · exact B125107
  · exact B125111
  · exact B125115
  · exact B125119
  · exact B125123
  · exact B125127
  · exact B125131
  · exact B125135
  · exact B125139
  · exact B125143
  · exact B125147
  · exact B125151
  · exact B125155
  · exact B125159
  · exact B125163
  · exact B125167
  · exact B125171
  · exact B125175
  · exact B125179
  · exact B125183
  · exact B125187
  · exact B125191
  · exact B125195
  · exact B125199
  · exact B125203
  · exact B125207
  · exact B125211
  · exact B125215
  · exact B125219
  · exact B125223
  · exact B125227
  · exact B125231
  · exact B125235
  · exact B125239
  · exact B125243
  · exact B125247
  · exact B125251
  · exact B125255
  · exact B125259
  · exact B125263
  · exact B125267
  · exact B125271
  · exact B125275
  · exact B125279
  · exact B125283
  · exact B125287
  · exact B125291
  · exact B125295
  · exact B125299
  · exact B125303
  · exact B125307
  · exact B125311
  · exact B125315
  · exact B125319
  · exact B125323
  · exact B125327
  · exact B125331
  · exact B125335
  · exact B125339
  · exact B125343
  · exact B125347
  · exact B125351
  · exact B125355
  · exact B125359
  · exact B125363
  · exact B125367
  · exact B125371
  · exact B125375
  · exact B125379
  · exact B125383
  · exact B125387
  · exact B125391
  · exact B125395
  · exact B125399
  · exact B125403
  · exact B125407
  · exact B125411
  · exact B125415
  · exact B125419
  · exact B125423
  · exact B125427
  · exact B125431
  · exact B125435
  · exact B125439
  · exact B125443
  · exact B125447
  · exact B125451
  · exact B125455
  · exact B125459
  · exact B125463
  · exact B125467
  · exact B125471
  · exact B125475
  · exact B125479
  · exact B125483
  · exact B125487
  · exact B125491
  · exact B125495
  · exact B125499
  · exact B125503
  · exact B125507
  · exact B125511
  · exact B125515
  · exact B125519
  · exact B125523
  · exact B125527
  · exact B125531
  · exact B125535
  · exact B125539
  · exact B125543
  · exact B125547
  · exact B125551
  · exact B125555
  · exact B125559
  · exact B125563
  · exact B125567
  · exact B125571
  · exact B125575
  · exact B125579
  · exact B125583
  · exact B125587
  · exact B125591
  · exact B125595
  · exact B125599
  · exact B125603
  · exact B125607
  · exact B125611
  · exact B125615
  · exact B125619
  · exact B125623
  · exact B125627
  · exact B125631
  · exact B125635
  · exact B125639
  · exact B125643
  · exact B125647
  · exact B125651
  · exact B125655
  · exact B125659
  · exact B125663
  · exact B125667
  · exact B125671
  · exact B125675
  · exact B125679
  · exact B125683
  · exact B125687
  · exact B125691
  · exact B125695
  · exact B125699
  · exact B125703
  · exact B125707
  · exact B125711
  · exact B125715
  · exact B125719
  · exact B125723
  · exact B125727
  · exact B125731
  · exact B125735
  · exact B125739
  · exact B125743
  · exact B125747
  · exact B125751
  · exact B125755
  · exact B125759
  · exact B125763
  · exact B125767
  · exact B125771
  · exact B125775
  · exact B125779
  · exact B125783
  · exact B125787
  · exact B125791
  · exact B125795
  · exact B125799
  · exact B125803
  · exact B125807
  · exact B125811
  · exact B125815
  · exact B125819
  · exact B125823
  · exact B125827
  · exact B125831
  · exact B125835
  · exact B125839
  · exact B125843
  · exact B125847
  · exact B125851
  · exact B125855
  · exact B125859
  · exact B125863
  · exact B125867
  · exact B125871
  · exact B125875
  · exact B125879
  · exact B125883
  · exact B125887
  · exact B125891
  · exact B125895
  · exact B125899
  · exact B125903
  · exact B125907
  · exact B125911
  · exact B125915
  · exact B125919
  · exact B125923
  · exact B125927
  · exact B125931
  · exact B125935
  · exact B125939
  · exact B125943
  · exact B125947
  · exact B125951
  · exact B125955
  · exact B125959
  · exact B125963
  · exact B125967
  · exact B125971
  · exact B125975
  · exact B125979
  · exact B125983
  · exact B125987
  · exact B125991
  · exact B125995
  · exact B125999
  · exact B126003
  · exact B126007
  · exact B126011
  · exact B126015
  · exact B126019
  · exact B126023
  · exact B126027
  · exact B126031
  · exact B126035
  · exact B126039
  · exact B126043
  · exact B126047
  · exact B126051
  · exact B126055
  · exact B126059
  · exact B126063
  · exact B126067
  · exact B126071
  · exact B126075
  · exact B126079
  · exact B126083
  · exact B126087
  · exact B126091
  · exact B126095
  · exact B126099
  · exact B126103
  · exact B126107
  · exact B126111
  · exact B126115
  · exact B126119
  · exact B126123
  · exact B126127
  · exact B126131
  · exact B126135
  · exact B126139
  · exact B126143
  · exact B126147
  · exact B126151
  · exact B126155
  · exact B126159
  · exact B126163
  · exact B126167
  · exact B126171
  · exact B126175
  · exact B126179
  · exact B126183
  · exact B126187
  · exact B126191
  · exact B126195
  · exact B126199
  · exact B126203
  · exact B126207
  · exact B126211
  · exact B126215
  · exact B126219
  · exact B126223
  · exact B126227
  · exact B126231
  · exact B126235
  · exact B126239
  · exact B126243
  · exact B126247
  · exact B126251
  · exact B126255
  · exact B126259
  · exact B126263
  · exact B126267
  · exact B126271
  · exact B126275
  · exact B126279
  · exact B126283
  · exact B126287
  · exact B126291
  · exact B126295
  · exact B126299
  · exact B126303
  · exact B126307
  · exact B126311
  · exact B126315
  · exact B126319
  · exact B126323
  · exact B126327
  · exact B126331
  · exact B126335
  · exact B126339
  · exact B126343
  · exact B126347
  · exact B126351
  · exact B126355
  · exact B126359
  · exact B126363
  · exact B126367
  · exact B126371
  · exact B126375
  · exact B126379
  · exact B126383
  · exact B126387
  · exact B126391
  · exact B126395
  · exact B126399
  · exact B126403
  · exact B126407
  · exact B126411
  · exact B126415
  · exact B126419
  · exact B126423
  · exact B126427
  · exact B126431
  · exact B126435
  · exact B126439
  · exact B126443
  · exact B126447
  · exact B126451
  · exact B126455
  · exact B126459
  · exact B126463
  · exact B126467
  · exact B126471
  · exact B126475
  · exact B126479
  · exact B126483
  · exact B126487
  · exact B126491
  · exact B126495
  · exact B126499
  · exact B126503
  · exact B126507
  · exact B126511
  · exact B126515
  · exact B126519
  · exact B126523
  · exact B126527
  · exact B126531
  · exact B126535
  · exact B126539
  · exact B126543
  · exact B126547
  · exact B126551
  · exact B126555
  · exact B126559
  · exact B126563
  · exact B126567
  · exact B126571
  · exact B126575
  · exact B126579
  · exact B126583

theorem C1 (j : ℕ) (h1 : 31646 ≤ j) (h2 : j ≤ 31946) : Blo 123787 (4 * j + 3) := by
  interval_cases j
  · exact B126587
  · exact B126591
  · exact B126595
  · exact B126599
  · exact B126603
  · exact B126607
  · exact B126611
  · exact B126615
  · exact B126619
  · exact B126623
  · exact B126627
  · exact B126631
  · exact B126635
  · exact B126639
  · exact B126643
  · exact B126647
  · exact B126651
  · exact B126655
  · exact B126659
  · exact B126663
  · exact B126667
  · exact B126671
  · exact B126675
  · exact B126679
  · exact B126683
  · exact B126687
  · exact B126691
  · exact B126695
  · exact B126699
  · exact B126703
  · exact B126707
  · exact B126711
  · exact B126715
  · exact B126719
  · exact B126723
  · exact B126727
  · exact B126731
  · exact B126735
  · exact B126739
  · exact B126743
  · exact B126747
  · exact B126751
  · exact B126755
  · exact B126759
  · exact B126763
  · exact B126767
  · exact B126771
  · exact B126775
  · exact B126779
  · exact B126783
  · exact B126787
  · exact B126791
  · exact B126795
  · exact B126799
  · exact B126803
  · exact B126807
  · exact B126811
  · exact B126815
  · exact B126819
  · exact B126823
  · exact B126827
  · exact B126831
  · exact B126835
  · exact B126839
  · exact B126843
  · exact B126847
  · exact B126851
  · exact B126855
  · exact B126859
  · exact B126863
  · exact B126867
  · exact B126871
  · exact B126875
  · exact B126879
  · exact B126883
  · exact B126887
  · exact B126891
  · exact B126895
  · exact B126899
  · exact B126903
  · exact B126907
  · exact B126911
  · exact B126915
  · exact B126919
  · exact B126923
  · exact B126927
  · exact B126931
  · exact B126935
  · exact B126939
  · exact B126943
  · exact B126947
  · exact B126951
  · exact B126955
  · exact B126959
  · exact B126963
  · exact B126967
  · exact B126971
  · exact B126975
  · exact B126979
  · exact B126983
  · exact B126987
  · exact B126991
  · exact B126995
  · exact B126999
  · exact B127003
  · exact B127007
  · exact B127011
  · exact B127015
  · exact B127019
  · exact B127023
  · exact B127027
  · exact B127031
  · exact B127035
  · exact B127039
  · exact B127043
  · exact B127047
  · exact B127051
  · exact B127055
  · exact B127059
  · exact B127063
  · exact B127067
  · exact B127071
  · exact B127075
  · exact B127079
  · exact B127083
  · exact B127087
  · exact B127091
  · exact B127095
  · exact B127099
  · exact B127103
  · exact B127107
  · exact B127111
  · exact B127115
  · exact B127119
  · exact B127123
  · exact B127127
  · exact B127131
  · exact B127135
  · exact B127139
  · exact B127143
  · exact B127147
  · exact B127151
  · exact B127155
  · exact B127159
  · exact B127163
  · exact B127167
  · exact B127171
  · exact B127175
  · exact B127179
  · exact B127183
  · exact B127187
  · exact B127191
  · exact B127195
  · exact B127199
  · exact B127203
  · exact B127207
  · exact B127211
  · exact B127215
  · exact B127219
  · exact B127223
  · exact B127227
  · exact B127231
  · exact B127235
  · exact B127239
  · exact B127243
  · exact B127247
  · exact B127251
  · exact B127255
  · exact B127259
  · exact B127263
  · exact B127267
  · exact B127271
  · exact B127275
  · exact B127279
  · exact B127283
  · exact B127287
  · exact B127291
  · exact B127295
  · exact B127299
  · exact B127303
  · exact B127307
  · exact B127311
  · exact B127315
  · exact B127319
  · exact B127323
  · exact B127327
  · exact B127331
  · exact B127335
  · exact B127339
  · exact B127343
  · exact B127347
  · exact B127351
  · exact B127355
  · exact B127359
  · exact B127363
  · exact B127367
  · exact B127371
  · exact B127375
  · exact B127379
  · exact B127383
  · exact B127387
  · exact B127391
  · exact B127395
  · exact B127399
  · exact B127403
  · exact B127407
  · exact B127411
  · exact B127415
  · exact B127419
  · exact B127423
  · exact B127427
  · exact B127431
  · exact B127435
  · exact B127439
  · exact B127443
  · exact B127447
  · exact B127451
  · exact B127455
  · exact B127459
  · exact B127463
  · exact B127467
  · exact B127471
  · exact B127475
  · exact B127479
  · exact B127483
  · exact B127487
  · exact B127491
  · exact B127495
  · exact B127499
  · exact B127503
  · exact B127507
  · exact B127511
  · exact B127515
  · exact B127519
  · exact B127523
  · exact B127527
  · exact B127531
  · exact B127535
  · exact B127539
  · exact B127543
  · exact B127547
  · exact B127551
  · exact B127555
  · exact B127559
  · exact B127563
  · exact B127567
  · exact B127571
  · exact B127575
  · exact B127579
  · exact B127583
  · exact B127587
  · exact B127591
  · exact B127595
  · exact B127599
  · exact B127603
  · exact B127607
  · exact B127611
  · exact B127615
  · exact B127619
  · exact B127623
  · exact B127627
  · exact B127631
  · exact B127635
  · exact B127639
  · exact B127643
  · exact B127647
  · exact B127651
  · exact B127655
  · exact B127659
  · exact B127663
  · exact B127667
  · exact B127671
  · exact B127675
  · exact B127679
  · exact B127683
  · exact B127687
  · exact B127691
  · exact B127695
  · exact B127699
  · exact B127703
  · exact B127707
  · exact B127711
  · exact B127715
  · exact B127719
  · exact B127723
  · exact B127727
  · exact B127731
  · exact B127735
  · exact B127739
  · exact B127743
  · exact B127747
  · exact B127751
  · exact B127755
  · exact B127759
  · exact B127763
  · exact B127767
  · exact B127771
  · exact B127775
  · exact B127779
  · exact B127783
  · exact B127787

theorem solution (m : ℕ) (hlo : 123787 ≤ m) (hhi : m ≤ 127787) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 30946 ≤ j := by omega
    have hj2 : j ≤ 31946 := by omega
    have hb : Blo 123787 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 31646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
