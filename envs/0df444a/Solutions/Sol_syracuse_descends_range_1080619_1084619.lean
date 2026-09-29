-- Prove2me | solution 1 for syracuse_descends_range_1080619_1084619
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:33.792147+00:00
-- url     : https://prove2.me/submissions/b2c3e911-361c-4008-9197-aaae32497894

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


theorem B3473509 : Blo 1080619 3473509 := bbase (se 4 (by rfl) ⟨325641, by rfl⟩ : syracuseStep 3473509 = 651283) (by norm_num)
theorem B1736885 : Blo 1080619 1736885 := bbase (se 5 (by rfl) ⟨81416, by rfl⟩ : syracuseStep 1736885 = 162833) (by norm_num)
theorem B1540309 : Blo 1080619 1540309 := bbase (se 7 (by rfl) ⟨18050, by rfl⟩ : syracuseStep 1540309 = 36101) (by norm_num)
theorem B1737173 : Blo 1080619 1737173 := bbase (se 7 (by rfl) ⟨20357, by rfl⟩ : syracuseStep 1737173 = 40715) (by norm_num)
theorem B12321557 : Blo 1080619 12321557 := bbase (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) (by norm_num)
theorem B6259477 : Blo 1080619 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B1540901 : Blo 1080619 1540901 := bbase (se 4 (by rfl) ⟨144459, by rfl⟩ : syracuseStep 1540901 = 288919) (by norm_num)
theorem B1540981 : Blo 1080619 1540981 := bbase (se 5 (by rfl) ⟨72233, by rfl⟩ : syracuseStep 1540981 = 144467) (by norm_num)
theorem B1737629 : Blo 1080619 1737629 := bbase (se 3 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 1737629 = 651611) (by norm_num)
theorem B35652565 : Blo 1080619 35652565 := bbase (se 7 (by rfl) ⟨417803, by rfl⟩ : syracuseStep 35652565 = 835607) (by norm_num)
theorem B1541101 : Blo 1080619 1541101 := bbase (se 3 (by rfl) ⟨288956, by rfl⟩ : syracuseStep 1541101 = 577913) (by norm_num)
theorem B1541197 : Blo 1080619 1541197 := bbase (se 3 (by rfl) ⟨288974, by rfl⟩ : syracuseStep 1541197 = 577949) (by norm_num)
theorem B3900581 : Blo 1080619 3900581 := bbase (se 4 (by rfl) ⟨365679, by rfl⟩ : syracuseStep 3900581 = 731359) (by norm_num)
theorem B5473493 : Blo 1080619 5473493 := bbase (se 7 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 5473493 = 128285) (by norm_num)
theorem B3900869 : Blo 1080619 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B1541693 : Blo 1080619 1541693 := bbase (se 3 (by rfl) ⟨289067, by rfl⟩ : syracuseStep 1541693 = 578135) (by norm_num)
theorem B6162101 : Blo 1080619 6162101 := bbase (se 5 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 6162101 = 577697) (by norm_num)
theorem B4622021 : Blo 1080619 4622021 := bbase (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) (by norm_num)
theorem B3901301 : Blo 1080619 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B53413973 : Blo 1080619 53413973 := bbase (se 8 (by rfl) ⟨312972, by rfl⟩ : syracuseStep 53413973 = 625945) (by norm_num)
theorem B1542245 : Blo 1080619 1542245 := bbase (se 4 (by rfl) ⟨144585, by rfl⟩ : syracuseStep 1542245 = 289171) (by norm_num)
theorem B2197613 : Blo 1080619 2197613 := bbase (se 3 (by rfl) ⟨412052, by rfl⟩ : syracuseStep 2197613 = 824105) (by norm_num)
theorem B5474789 : Blo 1080619 5474789 := bbase (se 4 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 5474789 = 1026523) (by norm_num)
theorem B3082805 : Blo 1080619 3082805 := bbase (se 5 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 3082805 = 289013) (by norm_num)
theorem B1542997 : Blo 1080619 1542997 := bbase (se 9 (by rfl) ⟨4520, by rfl⟩ : syracuseStep 1542997 = 9041) (by norm_num)
theorem B11111413 : Blo 1080619 11111413 := bbase (se 5 (by rfl) ⟨520847, by rfl⟩ : syracuseStep 11111413 = 1041695) (by norm_num)
theorem B1215697 : Blo 1080619 1215697 := bbase (se 2 (by rfl) ⟨455886, by rfl⟩ : syracuseStep 1215697 = 911773) (by norm_num)
theorem B2198765 : Blo 1080619 2198765 := bbase (se 3 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 2198765 = 824537) (by norm_num)
theorem B1215733 : Blo 1080619 1215733 := bbase (se 5 (by rfl) ⟨56987, by rfl⟩ : syracuseStep 1215733 = 113975) (by norm_num)
theorem B1215769 : Blo 1080619 1215769 := bbase (se 2 (by rfl) ⟨455913, by rfl⟩ : syracuseStep 1215769 = 911827) (by norm_num)
theorem B1215805 : Blo 1080619 1215805 := bbase (se 3 (by rfl) ⟨227963, by rfl⟩ : syracuseStep 1215805 = 455927) (by norm_num)
theorem B1215841 : Blo 1080619 1215841 := bbase (se 2 (by rfl) ⟨455940, by rfl⟩ : syracuseStep 1215841 = 911881) (by norm_num)
theorem B1215877 : Blo 1080619 1215877 := bbase (se 4 (by rfl) ⟨113988, by rfl⟩ : syracuseStep 1215877 = 227977) (by norm_num)
theorem B1215913 : Blo 1080619 1215913 := bbase (se 2 (by rfl) ⟨455967, by rfl⟩ : syracuseStep 1215913 = 911935) (by norm_num)
theorem B4623797 : Blo 1080619 4623797 := bbase (se 5 (by rfl) ⟨216740, by rfl⟩ : syracuseStep 4623797 = 433481) (by norm_num)
theorem B1215949 : Blo 1080619 1215949 := bbase (se 3 (by rfl) ⟨227990, by rfl⟩ : syracuseStep 1215949 = 455981) (by norm_num)
theorem B3706325 : Blo 1080619 3706325 := bbase (se 7 (by rfl) ⟨43433, by rfl⟩ : syracuseStep 3706325 = 86867) (by norm_num)
theorem B1215985 : Blo 1080619 1215985 := bbase (se 2 (by rfl) ⟨455994, by rfl⟩ : syracuseStep 1215985 = 911989) (by norm_num)
theorem B1216021 : Blo 1080619 1216021 := bbase (se 6 (by rfl) ⟨28500, by rfl⟩ : syracuseStep 1216021 = 57001) (by norm_num)
theorem B1216057 : Blo 1080619 1216057 := bbase (se 2 (by rfl) ⟨456021, by rfl⟩ : syracuseStep 1216057 = 912043) (by norm_num)
theorem B1216093 : Blo 1080619 1216093 := bbase (se 3 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 1216093 = 456035) (by norm_num)
theorem B1543789 : Blo 1080619 1543789 := bbase (se 3 (by rfl) ⟨289460, by rfl⟩ : syracuseStep 1543789 = 578921) (by norm_num)
theorem B1216129 : Blo 1080619 1216129 := bbase (se 2 (by rfl) ⟨456048, by rfl⟩ : syracuseStep 1216129 = 912097) (by norm_num)
theorem B1216165 : Blo 1080619 1216165 := bbase (se 4 (by rfl) ⟨114015, by rfl⟩ : syracuseStep 1216165 = 228031) (by norm_num)
theorem B4624037 : Blo 1080619 4624037 := bbase (se 4 (by rfl) ⟨433503, by rfl⟩ : syracuseStep 4624037 = 867007) (by norm_num)
theorem B1216201 : Blo 1080619 1216201 := bbase (se 2 (by rfl) ⟨456075, by rfl⟩ : syracuseStep 1216201 = 912151) (by norm_num)
theorem B3083989 : Blo 1080619 3083989 := bbase (se 7 (by rfl) ⟨36140, by rfl⟩ : syracuseStep 3083989 = 72281) (by norm_num)
theorem B1216237 : Blo 1080619 1216237 := bbase (se 3 (by rfl) ⟨228044, by rfl⟩ : syracuseStep 1216237 = 456089) (by norm_num)
theorem B5476085 : Blo 1080619 5476085 := bbase (se 5 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 5476085 = 513383) (by norm_num)
theorem B1216273 : Blo 1080619 1216273 := bbase (se 2 (by rfl) ⟨456102, by rfl⟩ : syracuseStep 1216273 = 912205) (by norm_num)
theorem B5279525 : Blo 1080619 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B1216309 : Blo 1080619 1216309 := bbase (se 5 (by rfl) ⟨57014, by rfl⟩ : syracuseStep 1216309 = 114029) (by norm_num)
theorem B1216345 : Blo 1080619 1216345 := bbase (se 2 (by rfl) ⟨456129, by rfl⟩ : syracuseStep 1216345 = 912259) (by norm_num)
theorem B3084149 : Blo 1080619 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B1216381 : Blo 1080619 1216381 := bbase (se 3 (by rfl) ⟨228071, by rfl⟩ : syracuseStep 1216381 = 456143) (by norm_num)
theorem B1216417 : Blo 1080619 1216417 := bbase (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) (by norm_num)
theorem B1544125 : Blo 1080619 1544125 := bbase (se 3 (by rfl) ⟨289523, by rfl⟩ : syracuseStep 1544125 = 579047) (by norm_num)
theorem B1216453 : Blo 1080619 1216453 := bbase (se 4 (by rfl) ⟨114042, by rfl⟩ : syracuseStep 1216453 = 228085) (by norm_num)
theorem B1216489 : Blo 1080619 1216489 := bbase (se 2 (by rfl) ⟨456183, by rfl⟩ : syracuseStep 1216489 = 912367) (by norm_num)
theorem B1216525 : Blo 1080619 1216525 := bbase (se 3 (by rfl) ⟨228098, by rfl⟩ : syracuseStep 1216525 = 456197) (by norm_num)
theorem B1216561 : Blo 1080619 1216561 := bbase (se 2 (by rfl) ⟨456210, by rfl⟩ : syracuseStep 1216561 = 912421) (by norm_num)
theorem B1216597 : Blo 1080619 1216597 := bbase (se 8 (by rfl) ⟨7128, by rfl⟩ : syracuseStep 1216597 = 14257) (by norm_num)
theorem B13176917 : Blo 1080619 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B3084389 : Blo 1080619 3084389 := bbase (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) (by norm_num)
theorem B1216633 : Blo 1080619 1216633 := bbase (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) (by norm_num)
theorem B1216669 : Blo 1080619 1216669 := bbase (se 3 (by rfl) ⟨228125, by rfl⟩ : syracuseStep 1216669 = 456251) (by norm_num)
theorem B1216705 : Blo 1080619 1216705 := bbase (se 2 (by rfl) ⟨456264, by rfl⟩ : syracuseStep 1216705 = 912529) (by norm_num)
theorem B1216741 : Blo 1080619 1216741 := bbase (se 4 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 1216741 = 228139) (by norm_num)
theorem B1216777 : Blo 1080619 1216777 := bbase (se 2 (by rfl) ⟨456291, by rfl⟩ : syracuseStep 1216777 = 912583) (by norm_num)
theorem B3084581 : Blo 1080619 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B1216813 : Blo 1080619 1216813 := bbase (se 3 (by rfl) ⟨228152, by rfl⟩ : syracuseStep 1216813 = 456305) (by norm_num)
theorem B1216849 : Blo 1080619 1216849 := bbase (se 2 (by rfl) ⟨456318, by rfl⟩ : syracuseStep 1216849 = 912637) (by norm_num)
theorem B1216885 : Blo 1080619 1216885 := bbase (se 5 (by rfl) ⟨57041, by rfl⟩ : syracuseStep 1216885 = 114083) (by norm_num)
theorem B1216921 : Blo 1080619 1216921 := bbase (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) (by norm_num)
theorem B1216957 : Blo 1080619 1216957 := bbase (se 3 (by rfl) ⟨228179, by rfl⟩ : syracuseStep 1216957 = 456359) (by norm_num)
theorem B1216993 : Blo 1080619 1216993 := bbase (se 2 (by rfl) ⟨456372, by rfl⟩ : syracuseStep 1216993 = 912745) (by norm_num)
theorem B1217029 : Blo 1080619 1217029 := bbase (se 4 (by rfl) ⟨114096, by rfl⟩ : syracuseStep 1217029 = 228193) (by norm_num)
theorem B1217065 : Blo 1080619 1217065 := bbase (se 2 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 1217065 = 912799) (by norm_num)
theorem B1217101 : Blo 1080619 1217101 := bbase (se 3 (by rfl) ⟨228206, by rfl⟩ : syracuseStep 1217101 = 456413) (by norm_num)
theorem B1217137 : Blo 1080619 1217137 := bbase (se 2 (by rfl) ⟨456426, by rfl⟩ : syracuseStep 1217137 = 912853) (by norm_num)
theorem B1217173 : Blo 1080619 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1217209 : Blo 1080619 1217209 := bbase (se 2 (by rfl) ⟨456453, by rfl⟩ : syracuseStep 1217209 = 912907) (by norm_num)
theorem B1217245 : Blo 1080619 1217245 := bbase (se 3 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 1217245 = 456467) (by norm_num)
theorem B1217281 : Blo 1080619 1217281 := bbase (se 2 (by rfl) ⟨456480, by rfl⟩ : syracuseStep 1217281 = 912961) (by norm_num)
theorem B1217317 : Blo 1080619 1217317 := bbase (se 4 (by rfl) ⟨114123, by rfl⟩ : syracuseStep 1217317 = 228247) (by norm_num)
theorem B1217353 : Blo 1080619 1217353 := bbase (se 2 (by rfl) ⟨456507, by rfl⟩ : syracuseStep 1217353 = 913015) (by norm_num)
theorem B1217389 : Blo 1080619 1217389 := bbase (se 3 (by rfl) ⟨228260, by rfl⟩ : syracuseStep 1217389 = 456521) (by norm_num)
theorem B1217425 : Blo 1080619 1217425 := bbase (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) (by norm_num)
theorem B1217461 : Blo 1080619 1217461 := bbase (se 5 (by rfl) ⟨57068, by rfl⟩ : syracuseStep 1217461 = 114137) (by norm_num)
theorem B1217497 : Blo 1080619 1217497 := bbase (se 2 (by rfl) ⟨456561, by rfl⟩ : syracuseStep 1217497 = 913123) (by norm_num)
theorem B2888677 : Blo 1080619 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B1217533 : Blo 1080619 1217533 := bbase (se 3 (by rfl) ⟨228287, by rfl⟩ : syracuseStep 1217533 = 456575) (by norm_num)
theorem B5477381 : Blo 1080619 5477381 := bbase (se 4 (by rfl) ⟨513504, by rfl⟩ : syracuseStep 5477381 = 1027009) (by norm_num)
theorem B1217569 : Blo 1080619 1217569 := bbase (se 2 (by rfl) ⟨456588, by rfl⟩ : syracuseStep 1217569 = 913177) (by norm_num)
theorem B1217605 : Blo 1080619 1217605 := bbase (se 4 (by rfl) ⟨114150, by rfl⟩ : syracuseStep 1217605 = 228301) (by norm_num)
theorem B1217641 : Blo 1080619 1217641 := bbase (se 2 (by rfl) ⟨456615, by rfl⟩ : syracuseStep 1217641 = 913231) (by norm_num)
theorem B1217677 : Blo 1080619 1217677 := bbase (se 3 (by rfl) ⟨228314, by rfl⟩ : syracuseStep 1217677 = 456629) (by norm_num)
theorem B1217713 : Blo 1080619 1217713 := bbase (se 2 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 1217713 = 913285) (by norm_num)
theorem B1217749 : Blo 1080619 1217749 := bbase (se 7 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 1217749 = 28541) (by norm_num)
theorem B1217785 : Blo 1080619 1217785 := bbase (se 2 (by rfl) ⟨456669, by rfl⟩ : syracuseStep 1217785 = 913339) (by norm_num)
theorem B3085573 : Blo 1080619 3085573 := bbase (se 4 (by rfl) ⟨289272, by rfl⟩ : syracuseStep 3085573 = 578545) (by norm_num)
theorem B1217821 : Blo 1080619 1217821 := bbase (se 3 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 1217821 = 456683) (by norm_num)
theorem B1217857 : Blo 1080619 1217857 := bbase (se 2 (by rfl) ⟨456696, by rfl⟩ : syracuseStep 1217857 = 913393) (by norm_num)
theorem B25335125 : Blo 1080619 25335125 := bbase (se 14 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 25335125 = 4639) (by norm_num)
theorem B1217893 : Blo 1080619 1217893 := bbase (se 4 (by rfl) ⟨114177, by rfl⟩ : syracuseStep 1217893 = 228355) (by norm_num)
theorem B1217929 : Blo 1080619 1217929 := bbase (se 2 (by rfl) ⟨456723, by rfl⟩ : syracuseStep 1217929 = 913447) (by norm_num)
theorem B1217965 : Blo 1080619 1217965 := bbase (se 3 (by rfl) ⟨228368, by rfl⟩ : syracuseStep 1217965 = 456737) (by norm_num)
theorem B3904949 : Blo 1080619 3904949 := bbase (se 5 (by rfl) ⟨183044, by rfl⟩ : syracuseStep 3904949 = 366089) (by norm_num)
theorem B1218001 : Blo 1080619 1218001 := bbase (se 2 (by rfl) ⟨456750, by rfl⟩ : syracuseStep 1218001 = 913501) (by norm_num)
theorem B1218037 : Blo 1080619 1218037 := bbase (se 5 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 1218037 = 114191) (by norm_num)
theorem B1218073 : Blo 1080619 1218073 := bbase (se 2 (by rfl) ⟨456777, by rfl⟩ : syracuseStep 1218073 = 913555) (by norm_num)
theorem B3905077 : Blo 1080619 3905077 := bbase (se 5 (by rfl) ⟨183050, by rfl⟩ : syracuseStep 3905077 = 366101) (by norm_num)
theorem B1218109 : Blo 1080619 1218109 := bbase (se 3 (by rfl) ⟨228395, by rfl⟩ : syracuseStep 1218109 = 456791) (by norm_num)
theorem B1218145 : Blo 1080619 1218145 := bbase (se 2 (by rfl) ⟨456804, by rfl⟩ : syracuseStep 1218145 = 913609) (by norm_num)
theorem B1218181 : Blo 1080619 1218181 := bbase (se 4 (by rfl) ⟨114204, by rfl⟩ : syracuseStep 1218181 = 228409) (by norm_num)
theorem B1218217 : Blo 1080619 1218217 := bbase (se 2 (by rfl) ⟨456831, by rfl⟩ : syracuseStep 1218217 = 913663) (by norm_num)
theorem B1316525 : Blo 1080619 1316525 := bbase (se 3 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 1316525 = 493697) (by norm_num)
theorem B1218253 : Blo 1080619 1218253 := bbase (se 3 (by rfl) ⟨228422, by rfl⟩ : syracuseStep 1218253 = 456845) (by norm_num)
theorem B1218289 : Blo 1080619 1218289 := bbase (se 2 (by rfl) ⟨456858, by rfl⟩ : syracuseStep 1218289 = 913717) (by norm_num)
theorem B1218325 : Blo 1080619 1218325 := bbase (se 6 (by rfl) ⟨28554, by rfl⟩ : syracuseStep 1218325 = 57109) (by norm_num)
theorem B1218361 : Blo 1080619 1218361 := bbase (se 2 (by rfl) ⟨456885, by rfl⟩ : syracuseStep 1218361 = 913771) (by norm_num)
theorem B1218397 : Blo 1080619 1218397 := bbase (se 3 (by rfl) ⟨228449, by rfl⟩ : syracuseStep 1218397 = 456899) (by norm_num)
theorem B1218433 : Blo 1080619 1218433 := bbase (se 2 (by rfl) ⟨456912, by rfl⟩ : syracuseStep 1218433 = 913825) (by norm_num)
theorem B4626325 : Blo 1080619 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B1218469 : Blo 1080619 1218469 := bbase (se 4 (by rfl) ⟨114231, by rfl⟩ : syracuseStep 1218469 = 228463) (by norm_num)
theorem B1218505 : Blo 1080619 1218505 := bbase (se 2 (by rfl) ⟨456939, by rfl⟩ : syracuseStep 1218505 = 913879) (by norm_num)
theorem B1218541 : Blo 1080619 1218541 := bbase (se 3 (by rfl) ⟨228476, by rfl⟩ : syracuseStep 1218541 = 456953) (by norm_num)
theorem B1218577 : Blo 1080619 1218577 := bbase (se 2 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 1218577 = 913933) (by norm_num)
theorem B1218613 : Blo 1080619 1218613 := bbase (se 5 (by rfl) ⟨57122, by rfl⟩ : syracuseStep 1218613 = 114245) (by norm_num)
theorem B2922581 : Blo 1080619 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B1218649 : Blo 1080619 1218649 := bbase (se 2 (by rfl) ⟨456993, by rfl⟩ : syracuseStep 1218649 = 913987) (by norm_num)
theorem B1218685 : Blo 1080619 1218685 := bbase (se 3 (by rfl) ⟨228503, by rfl⟩ : syracuseStep 1218685 = 457007) (by norm_num)
theorem B1218721 : Blo 1080619 1218721 := bbase (se 2 (by rfl) ⟨457020, by rfl⟩ : syracuseStep 1218721 = 914041) (by norm_num)
theorem B1218757 : Blo 1080619 1218757 := bbase (se 4 (by rfl) ⟨114258, by rfl⟩ : syracuseStep 1218757 = 228517) (by norm_num)
theorem B1218793 : Blo 1080619 1218793 := bbase (se 2 (by rfl) ⟨457047, by rfl⟩ : syracuseStep 1218793 = 914095) (by norm_num)
theorem B1218829 : Blo 1080619 1218829 := bbase (se 3 (by rfl) ⟨228530, by rfl⟩ : syracuseStep 1218829 = 457061) (by norm_num)
theorem B5478677 : Blo 1080619 5478677 := bbase (se 6 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 5478677 = 256813) (by norm_num)
theorem B1218865 : Blo 1080619 1218865 := bbase (se 2 (by rfl) ⟨457074, by rfl⟩ : syracuseStep 1218865 = 914149) (by norm_num)
theorem B1644877 : Blo 1080619 1644877 := bbase (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) (by norm_num)
theorem B1218901 : Blo 1080619 1218901 := bbase (se 10 (by rfl) ⟨1785, by rfl⟩ : syracuseStep 1218901 = 3571) (by norm_num)
theorem B3086677 : Blo 1080619 3086677 := bbase (se 10 (by rfl) ⟨4521, by rfl⟩ : syracuseStep 3086677 = 9043) (by norm_num)
theorem B1218937 : Blo 1080619 1218937 := bbase (se 2 (by rfl) ⟨457101, by rfl⟩ : syracuseStep 1218937 = 914203) (by norm_num)
theorem B1218973 : Blo 1080619 1218973 := bbase (se 3 (by rfl) ⟨228557, by rfl⟩ : syracuseStep 1218973 = 457115) (by norm_num)
theorem B2431421 : Blo 1080619 2431421 := bbase (se 3 (by rfl) ⟨455891, by rfl⟩ : syracuseStep 2431421 = 911783) (by norm_num)
theorem B1219009 : Blo 1080619 1219009 := bbase (se 2 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 1219009 = 914257) (by norm_num)
theorem B8231381 : Blo 1080619 8231381 := bbase (se 7 (by rfl) ⟨96461, by rfl⟩ : syracuseStep 8231381 = 192923) (by norm_num)
theorem B1219045 : Blo 1080619 1219045 := bbase (se 4 (by rfl) ⟨114285, by rfl⟩ : syracuseStep 1219045 = 228571) (by norm_num)
theorem B2431493 : Blo 1080619 2431493 := bbase (se 4 (by rfl) ⟨227952, by rfl⟩ : syracuseStep 2431493 = 455905) (by norm_num)
theorem B2923013 : Blo 1080619 2923013 := bbase (se 4 (by rfl) ⟨274032, by rfl⟩ : syracuseStep 2923013 = 548065) (by norm_num)
theorem B1219081 : Blo 1080619 1219081 := bbase (se 2 (by rfl) ⟨457155, by rfl⟩ : syracuseStep 1219081 = 914311) (by norm_num)
theorem B1219117 : Blo 1080619 1219117 := bbase (se 3 (by rfl) ⟨228584, by rfl⟩ : syracuseStep 1219117 = 457169) (by norm_num)
theorem B2431565 : Blo 1080619 2431565 := bbase (se 3 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 2431565 = 911837) (by norm_num)
theorem B1219153 : Blo 1080619 1219153 := bbase (se 2 (by rfl) ⟨457182, by rfl⟩ : syracuseStep 1219153 = 914365) (by norm_num)
theorem B1219189 : Blo 1080619 1219189 := bbase (se 5 (by rfl) ⟨57149, by rfl⟩ : syracuseStep 1219189 = 114299) (by norm_num)
theorem B2431637 : Blo 1080619 2431637 := bbase (se 6 (by rfl) ⟨56991, by rfl⟩ : syracuseStep 2431637 = 113983) (by norm_num)
theorem B1219225 : Blo 1080619 1219225 := bbase (se 2 (by rfl) ⟨457209, by rfl⟩ : syracuseStep 1219225 = 914419) (by norm_num)
theorem B1219261 : Blo 1080619 1219261 := bbase (se 3 (by rfl) ⟨228611, by rfl⟩ : syracuseStep 1219261 = 457223) (by norm_num)
theorem B2431709 : Blo 1080619 2431709 := bbase (se 3 (by rfl) ⟨455945, by rfl⟩ : syracuseStep 2431709 = 911891) (by norm_num)
theorem B1219297 : Blo 1080619 1219297 := bbase (se 2 (by rfl) ⟨457236, by rfl⟩ : syracuseStep 1219297 = 914473) (by norm_num)
theorem B1219333 : Blo 1080619 1219333 := bbase (se 4 (by rfl) ⟨114312, by rfl⟩ : syracuseStep 1219333 = 228625) (by norm_num)
theorem B2431781 : Blo 1080619 2431781 := bbase (se 4 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 2431781 = 455959) (by norm_num)
theorem B1219369 : Blo 1080619 1219369 := bbase (se 2 (by rfl) ⟨457263, by rfl⟩ : syracuseStep 1219369 = 914527) (by norm_num)
theorem B1645357 : Blo 1080619 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B1219405 : Blo 1080619 1219405 := bbase (se 3 (by rfl) ⟨228638, by rfl⟩ : syracuseStep 1219405 = 457277) (by norm_num)
theorem B2431853 : Blo 1080619 2431853 := bbase (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) (by norm_num)
theorem B1219441 : Blo 1080619 1219441 := bbase (se 2 (by rfl) ⟨457290, by rfl⟩ : syracuseStep 1219441 = 914581) (by norm_num)
theorem B2923381 : Blo 1080619 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B1219477 : Blo 1080619 1219477 := bbase (se 6 (by rfl) ⟨28581, by rfl⟩ : syracuseStep 1219477 = 57163) (by norm_num)
theorem B2431925 : Blo 1080619 2431925 := bbase (se 5 (by rfl) ⟨113996, by rfl⟩ : syracuseStep 2431925 = 227993) (by norm_num)
theorem B1219513 : Blo 1080619 1219513 := bbase (se 2 (by rfl) ⟨457317, by rfl⟩ : syracuseStep 1219513 = 914635) (by norm_num)
theorem B1219549 : Blo 1080619 1219549 := bbase (se 3 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 1219549 = 457331) (by norm_num)
theorem B2431997 : Blo 1080619 2431997 := bbase (se 3 (by rfl) ⟨455999, by rfl⟩ : syracuseStep 2431997 = 911999) (by norm_num)
theorem B1219585 : Blo 1080619 1219585 := bbase (se 2 (by rfl) ⟨457344, by rfl⟩ : syracuseStep 1219585 = 914689) (by norm_num)
theorem B1219621 : Blo 1080619 1219621 := bbase (se 4 (by rfl) ⟨114339, by rfl⟩ : syracuseStep 1219621 = 228679) (by norm_num)
theorem B4103237 : Blo 1080619 4103237 := bbase (se 4 (by rfl) ⟨384678, by rfl⟩ : syracuseStep 4103237 = 769357) (by norm_num)
theorem B2432069 : Blo 1080619 2432069 := bbase (se 4 (by rfl) ⟨228006, by rfl⟩ : syracuseStep 2432069 = 456013) (by norm_num)
theorem B1219657 : Blo 1080619 1219657 := bbase (se 2 (by rfl) ⟨457371, by rfl⟩ : syracuseStep 1219657 = 914743) (by norm_num)
theorem B1219693 : Blo 1080619 1219693 := bbase (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) (by norm_num)
theorem B2432141 : Blo 1080619 2432141 := bbase (se 3 (by rfl) ⟨456026, by rfl⟩ : syracuseStep 2432141 = 912053) (by norm_num)
theorem B1219729 : Blo 1080619 1219729 := bbase (se 2 (by rfl) ⟨457398, by rfl⟩ : syracuseStep 1219729 = 914797) (by norm_num)
theorem B1219765 : Blo 1080619 1219765 := bbase (se 5 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 1219765 = 114353) (by norm_num)
theorem B2432213 : Blo 1080619 2432213 := bbase (se 7 (by rfl) ⟨28502, by rfl⟩ : syracuseStep 2432213 = 57005) (by norm_num)
theorem B1219801 : Blo 1080619 1219801 := bbase (se 2 (by rfl) ⟨457425, by rfl⟩ : syracuseStep 1219801 = 914851) (by norm_num)
theorem B1219837 : Blo 1080619 1219837 := bbase (se 3 (by rfl) ⟨228719, by rfl⟩ : syracuseStep 1219837 = 457439) (by norm_num)
theorem B1154309 : Blo 1080619 1154309 := bbase (se 4 (by rfl) ⟨108216, by rfl⟩ : syracuseStep 1154309 = 216433) (by norm_num)
theorem B2432285 : Blo 1080619 2432285 := bbase (se 3 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 2432285 = 912107) (by norm_num)
theorem B1219873 : Blo 1080619 1219873 := bbase (se 2 (by rfl) ⟨457452, by rfl⟩ : syracuseStep 1219873 = 914905) (by norm_num)
theorem B1154369 : Blo 1080619 1154369 := bbase (se 2 (by rfl) ⟨432888, by rfl⟩ : syracuseStep 1154369 = 865777) (by norm_num)
theorem B1219909 : Blo 1080619 1219909 := bbase (se 4 (by rfl) ⟨114366, by rfl⟩ : syracuseStep 1219909 = 228733) (by norm_num)
theorem B7806293 : Blo 1080619 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B2432357 : Blo 1080619 2432357 := bbase (se 4 (by rfl) ⟨228033, by rfl⟩ : syracuseStep 2432357 = 456067) (by norm_num)
theorem B4627813 : Blo 1080619 4627813 := bbase (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) (by norm_num)
theorem B1219945 : Blo 1080619 1219945 := bbase (se 2 (by rfl) ⟨457479, by rfl⟩ : syracuseStep 1219945 = 914959) (by norm_num)
theorem B4627829 : Blo 1080619 4627829 := bbase (se 5 (by rfl) ⟨216929, by rfl⟩ : syracuseStep 4627829 = 433859) (by norm_num)
theorem B1219981 : Blo 1080619 1219981 := bbase (se 3 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 1219981 = 457493) (by norm_num)
theorem B2432429 : Blo 1080619 2432429 := bbase (se 3 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 2432429 = 912161) (by norm_num)
theorem B1220017 : Blo 1080619 1220017 := bbase (se 2 (by rfl) ⟨457506, by rfl⟩ : syracuseStep 1220017 = 915013) (by norm_num)
theorem B3120565 : Blo 1080619 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B1154497 : Blo 1080619 1154497 := bbase (se 2 (by rfl) ⟨432936, by rfl⟩ : syracuseStep 1154497 = 865873) (by norm_num)
theorem B1220053 : Blo 1080619 1220053 := bbase (se 7 (by rfl) ⟨14297, by rfl⟩ : syracuseStep 1220053 = 28595) (by norm_num)
theorem B1318361 : Blo 1080619 1318361 := bbase (se 2 (by rfl) ⟨494385, by rfl⟩ : syracuseStep 1318361 = 988771) (by norm_num)
theorem B2432501 : Blo 1080619 2432501 := bbase (se 5 (by rfl) ⟨114023, by rfl⟩ : syracuseStep 2432501 = 228047) (by norm_num)
theorem B1220089 : Blo 1080619 1220089 := bbase (se 2 (by rfl) ⟨457533, by rfl⟩ : syracuseStep 1220089 = 915067) (by norm_num)
theorem B1220125 : Blo 1080619 1220125 := bbase (se 3 (by rfl) ⟨228773, by rfl⟩ : syracuseStep 1220125 = 457547) (by norm_num)
theorem B5479973 : Blo 1080619 5479973 := bbase (se 4 (by rfl) ⟨513747, by rfl⟩ : syracuseStep 5479973 = 1027495) (by norm_num)
theorem B2432573 : Blo 1080619 2432573 := bbase (se 3 (by rfl) ⟨456107, by rfl⟩ : syracuseStep 2432573 = 912215) (by norm_num)
theorem B1220161 : Blo 1080619 1220161 := bbase (se 2 (by rfl) ⟨457560, by rfl⟩ : syracuseStep 1220161 = 915121) (by norm_num)
theorem B1220197 : Blo 1080619 1220197 := bbase (se 4 (by rfl) ⟨114393, by rfl⟩ : syracuseStep 1220197 = 228787) (by norm_num)
theorem B2432645 : Blo 1080619 2432645 := bbase (se 4 (by rfl) ⟨228060, by rfl⟩ : syracuseStep 2432645 = 456121) (by norm_num)
theorem B2432717 : Blo 1080619 2432717 := bbase (se 3 (by rfl) ⟨456134, by rfl⟩ : syracuseStep 2432717 = 912269) (by norm_num)
theorem B2432789 : Blo 1080619 2432789 := bbase (se 6 (by rfl) ⟨57018, by rfl⟩ : syracuseStep 2432789 = 114037) (by norm_num)
theorem B3088181 : Blo 1080619 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B2432861 : Blo 1080619 2432861 := bbase (se 3 (by rfl) ⟨456161, by rfl⟩ : syracuseStep 2432861 = 912323) (by norm_num)
theorem B1154941 : Blo 1080619 1154941 := bbase (se 3 (by rfl) ⟨216551, by rfl⟩ : syracuseStep 1154941 = 433103) (by norm_num)
theorem B2432933 : Blo 1080619 2432933 := bbase (se 4 (by rfl) ⟨228087, by rfl⟩ : syracuseStep 2432933 = 456175) (by norm_num)
theorem B2433005 : Blo 1080619 2433005 := bbase (se 3 (by rfl) ⟨456188, by rfl⟩ : syracuseStep 2433005 = 912377) (by norm_num)
theorem B1155061 : Blo 1080619 1155061 := bbase (se 5 (by rfl) ⟨54143, by rfl⟩ : syracuseStep 1155061 = 108287) (by norm_num)
theorem B2433077 : Blo 1080619 2433077 := bbase (se 5 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 2433077 = 228101) (by norm_num)
theorem B10395701 : Blo 1080619 10395701 := bbase (se 5 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 10395701 = 974597) (by norm_num)
theorem B1876061 : Blo 1080619 1876061 := bbase (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) (by norm_num)
theorem B2433149 : Blo 1080619 2433149 := bbase (se 3 (by rfl) ⟨456215, by rfl⟩ : syracuseStep 2433149 = 912431) (by norm_num)
theorem B1646725 : Blo 1080619 1646725 := bbase (se 4 (by rfl) ⟨154380, by rfl⟩ : syracuseStep 1646725 = 308761) (by norm_num)
theorem B2433221 : Blo 1080619 2433221 := bbase (se 4 (by rfl) ⟨228114, by rfl⟩ : syracuseStep 2433221 = 456229) (by norm_num)
theorem B6004949 : Blo 1080619 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B1155313 : Blo 1080619 1155313 := bbase (se 2 (by rfl) ⟨433242, by rfl⟩ : syracuseStep 1155313 = 866485) (by norm_num)
theorem B1155317 : Blo 1080619 1155317 := bbase (se 5 (by rfl) ⟨54155, by rfl⟩ : syracuseStep 1155317 = 108311) (by norm_num)
theorem B2433293 : Blo 1080619 2433293 := bbase (se 3 (by rfl) ⟨456242, by rfl⟩ : syracuseStep 2433293 = 912485) (by norm_num)
theorem B2433365 : Blo 1080619 2433365 := bbase (se 10 (by rfl) ⟨3564, by rfl⟩ : syracuseStep 2433365 = 7129) (by norm_num)
theorem B2433437 : Blo 1080619 2433437 := bbase (se 3 (by rfl) ⟨456269, by rfl⟩ : syracuseStep 2433437 = 912539) (by norm_num)
theorem B1647029 : Blo 1080619 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B2433509 : Blo 1080619 2433509 := bbase (se 4 (by rfl) ⟨228141, by rfl⟩ : syracuseStep 2433509 = 456283) (by norm_num)
theorem B2433581 : Blo 1080619 2433581 := bbase (se 3 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 2433581 = 912593) (by norm_num)
theorem B2433653 : Blo 1080619 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B2171525 : Blo 1080619 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B1581725 : Blo 1080619 1581725 := bbase (se 3 (by rfl) ⟨296573, by rfl⟩ : syracuseStep 1581725 = 593147) (by norm_num)
theorem B2433725 : Blo 1080619 2433725 := bbase (se 3 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 2433725 = 912647) (by norm_num)
theorem B2433797 : Blo 1080619 2433797 := bbase (se 4 (by rfl) ⟨228168, by rfl⟩ : syracuseStep 2433797 = 456337) (by norm_num)
theorem B1155881 : Blo 1080619 1155881 := bbase (se 2 (by rfl) ⟨433455, by rfl⟩ : syracuseStep 1155881 = 866911) (by norm_num)
theorem B5481269 : Blo 1080619 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B2433869 : Blo 1080619 2433869 := bbase (se 3 (by rfl) ⟨456350, by rfl⟩ : syracuseStep 2433869 = 912701) (by norm_num)
theorem B2433941 : Blo 1080619 2433941 := bbase (se 6 (by rfl) ⟨57045, by rfl⟩ : syracuseStep 2433941 = 114091) (by norm_num)
theorem B2434013 : Blo 1080619 2434013 := bbase (se 3 (by rfl) ⟨456377, by rfl⟩ : syracuseStep 2434013 = 912755) (by norm_num)
theorem B1156069 : Blo 1080619 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B2434085 : Blo 1080619 2434085 := bbase (se 4 (by rfl) ⟨228195, by rfl⟩ : syracuseStep 2434085 = 456391) (by norm_num)
theorem B2434157 : Blo 1080619 2434157 := bbase (se 3 (by rfl) ⟨456404, by rfl⟩ : syracuseStep 2434157 = 912809) (by norm_num)
theorem B4105349 : Blo 1080619 4105349 := bbase (se 4 (by rfl) ⟨384876, by rfl⟩ : syracuseStep 4105349 = 769753) (by norm_num)
theorem B3515557 : Blo 1080619 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B2434229 : Blo 1080619 2434229 := bbase (se 5 (by rfl) ⟨114104, by rfl⟩ : syracuseStep 2434229 = 228209) (by norm_num)
theorem B2434301 : Blo 1080619 2434301 := bbase (se 3 (by rfl) ⟨456431, by rfl⟩ : syracuseStep 2434301 = 912863) (by norm_num)
theorem B2598149 : Blo 1080619 2598149 := bbase (se 4 (by rfl) ⟨243576, by rfl⟩ : syracuseStep 2598149 = 487153) (by norm_num)
theorem B7808309 : Blo 1080619 7808309 := bbase (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) (by norm_num)
theorem B2434373 : Blo 1080619 2434373 := bbase (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) (by norm_num)
theorem B2434445 : Blo 1080619 2434445 := bbase (se 3 (by rfl) ⟨456458, by rfl⟩ : syracuseStep 2434445 = 912917) (by norm_num)
theorem B4105637 : Blo 1080619 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2434517 : Blo 1080619 2434517 := bbase (se 7 (by rfl) ⟨28529, by rfl⟩ : syracuseStep 2434517 = 57059) (by norm_num)
theorem B2434589 : Blo 1080619 2434589 := bbase (se 3 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 2434589 = 912971) (by norm_num)
theorem B6170165 : Blo 1080619 6170165 := bbase (se 5 (by rfl) ⟨289226, by rfl⟩ : syracuseStep 6170165 = 578453) (by norm_num)
theorem B4630085 : Blo 1080619 4630085 := bbase (se 4 (by rfl) ⟨434070, by rfl⟩ : syracuseStep 4630085 = 868141) (by norm_num)
theorem B2434661 : Blo 1080619 2434661 := bbase (se 4 (by rfl) ⟨228249, by rfl⟩ : syracuseStep 2434661 = 456499) (by norm_num)
theorem B2598533 : Blo 1080619 2598533 := bbase (se 4 (by rfl) ⟨243612, by rfl⟩ : syracuseStep 2598533 = 487225) (by norm_num)
theorem B1648277 : Blo 1080619 1648277 := bbase (se 6 (by rfl) ⟨38631, by rfl⟩ : syracuseStep 1648277 = 77263) (by norm_num)
theorem B2434733 : Blo 1080619 2434733 := bbase (se 3 (by rfl) ⟨456512, by rfl⟩ : syracuseStep 2434733 = 913025) (by norm_num)
theorem B2434805 : Blo 1080619 2434805 := bbase (se 5 (by rfl) ⟨114131, by rfl⟩ : syracuseStep 2434805 = 228263) (by norm_num)
theorem B1189621 : Blo 1080619 1189621 := bbase (se 5 (by rfl) ⟨55763, by rfl⟩ : syracuseStep 1189621 = 111527) (by norm_num)
theorem B1156889 : Blo 1080619 1156889 := bbase (se 2 (by rfl) ⟨433833, by rfl⟩ : syracuseStep 1156889 = 867667) (by norm_num)
theorem B2434877 : Blo 1080619 2434877 := bbase (se 3 (by rfl) ⟨456539, by rfl⟩ : syracuseStep 2434877 = 913079) (by norm_num)
theorem B2598733 : Blo 1080619 2598733 := bbase (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) (by norm_num)
theorem B6596437 : Blo 1080619 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B2434949 : Blo 1080619 2434949 := bbase (se 4 (by rfl) ⟨228276, by rfl⟩ : syracuseStep 2434949 = 456553) (by norm_num)
theorem B3647429 : Blo 1080619 3647429 := bbase (se 4 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 3647429 = 683893) (by norm_num)
theorem B2435021 : Blo 1080619 2435021 := bbase (se 3 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 2435021 = 913133) (by norm_num)
theorem B2435093 : Blo 1080619 2435093 := bbase (se 6 (by rfl) ⟨57072, by rfl⟩ : syracuseStep 2435093 = 114145) (by norm_num)
theorem B5482565 : Blo 1080619 5482565 := bbase (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) (by norm_num)
theorem B2435165 : Blo 1080619 2435165 := bbase (se 3 (by rfl) ⟨456593, by rfl⟩ : syracuseStep 2435165 = 913187) (by norm_num)
theorem B2435237 : Blo 1080619 2435237 := bbase (se 4 (by rfl) ⟨228303, by rfl⟩ : syracuseStep 2435237 = 456607) (by norm_num)
theorem B1157333 : Blo 1080619 1157333 := bbase (se 7 (by rfl) ⟨13562, by rfl⟩ : syracuseStep 1157333 = 27125) (by norm_num)
theorem B2435309 : Blo 1080619 2435309 := bbase (se 3 (by rfl) ⟨456620, by rfl⟩ : syracuseStep 2435309 = 913241) (by norm_num)
theorem B2435381 : Blo 1080619 2435381 := bbase (se 5 (by rfl) ⟨114158, by rfl⟩ : syracuseStep 2435381 = 228317) (by norm_num)
theorem B3647861 : Blo 1080619 3647861 := bbase (se 5 (by rfl) ⟨170993, by rfl⟩ : syracuseStep 3647861 = 341987) (by norm_num)
theorem B2435453 : Blo 1080619 2435453 := bbase (se 3 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 2435453 = 913295) (by norm_num)
theorem B2435525 : Blo 1080619 2435525 := bbase (se 4 (by rfl) ⟨228330, by rfl⟩ : syracuseStep 2435525 = 456661) (by norm_num)
theorem B1157581 : Blo 1080619 1157581 := bbase (se 3 (by rfl) ⟨217046, by rfl⟩ : syracuseStep 1157581 = 434093) (by norm_num)
theorem B2435597 : Blo 1080619 2435597 := bbase (se 3 (by rfl) ⟨456674, by rfl⟩ : syracuseStep 2435597 = 913349) (by norm_num)
theorem B4106821 : Blo 1080619 4106821 := bbase (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) (by norm_num)
theorem B2435669 : Blo 1080619 2435669 := bbase (se 8 (by rfl) ⟨14271, by rfl⟩ : syracuseStep 2435669 = 28543) (by norm_num)
theorem B2435741 : Blo 1080619 2435741 := bbase (se 3 (by rfl) ⟨456701, by rfl⟩ : syracuseStep 2435741 = 913403) (by norm_num)
theorem B3517141 : Blo 1080619 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B6171349 : Blo 1080619 6171349 := bbase (se 7 (by rfl) ⟨72320, by rfl⟩ : syracuseStep 6171349 = 144641) (by norm_num)
theorem B2435813 : Blo 1080619 2435813 := bbase (se 4 (by rfl) ⟨228357, by rfl⟩ : syracuseStep 2435813 = 456715) (by norm_num)
theorem B3648293 : Blo 1080619 3648293 := bbase (se 4 (by rfl) ⟨342027, by rfl⟩ : syracuseStep 3648293 = 684055) (by norm_num)
theorem B2435885 : Blo 1080619 2435885 := bbase (se 3 (by rfl) ⟨456728, by rfl⟩ : syracuseStep 2435885 = 913457) (by norm_num)
theorem B4107125 : Blo 1080619 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B2435957 : Blo 1080619 2435957 := bbase (se 5 (by rfl) ⟨114185, by rfl⟩ : syracuseStep 2435957 = 228371) (by norm_num)
theorem B1158013 : Blo 1080619 1158013 := bbase (se 3 (by rfl) ⟨217127, by rfl⟩ : syracuseStep 1158013 = 434255) (by norm_num)
theorem B2436029 : Blo 1080619 2436029 := bbase (se 3 (by rfl) ⟨456755, by rfl⟩ : syracuseStep 2436029 = 913511) (by norm_num)
theorem B1158085 : Blo 1080619 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B2436101 : Blo 1080619 2436101 := bbase (se 4 (by rfl) ⟨228384, by rfl⟩ : syracuseStep 2436101 = 456769) (by norm_num)
theorem B2436173 : Blo 1080619 2436173 := bbase (se 3 (by rfl) ⟨456782, by rfl⟩ : syracuseStep 2436173 = 913565) (by norm_num)
theorem B5549141 : Blo 1080619 5549141 := bbase (se 8 (by rfl) ⟨32514, by rfl⟩ : syracuseStep 5549141 = 65029) (by norm_num)
theorem B2436245 : Blo 1080619 2436245 := bbase (se 6 (by rfl) ⟨57099, by rfl⟩ : syracuseStep 2436245 = 114199) (by norm_num)
theorem B7613621 : Blo 1080619 7613621 := bbase (se 5 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 7613621 = 713777) (by norm_num)
theorem B3648725 : Blo 1080619 3648725 := bbase (se 7 (by rfl) ⟨42758, by rfl⟩ : syracuseStep 3648725 = 85517) (by norm_num)
theorem B2436317 : Blo 1080619 2436317 := bbase (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) (by norm_num)
theorem B2436389 : Blo 1080619 2436389 := bbase (se 4 (by rfl) ⟨228411, by rfl⟩ : syracuseStep 2436389 = 456823) (by norm_num)
theorem B5483861 : Blo 1080619 5483861 := bbase (se 11 (by rfl) ⟨4016, by rfl⟩ : syracuseStep 5483861 = 8033) (by norm_num)
theorem B2436461 : Blo 1080619 2436461 := bbase (se 3 (by rfl) ⟨456836, by rfl⟩ : syracuseStep 2436461 = 913673) (by norm_num)
theorem B2600309 : Blo 1080619 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B2436533 : Blo 1080619 2436533 := bbase (se 5 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 2436533 = 228425) (by norm_num)
theorem B2436605 : Blo 1080619 2436605 := bbase (se 3 (by rfl) ⟨456863, by rfl⟩ : syracuseStep 2436605 = 913727) (by norm_num)
theorem B2436677 : Blo 1080619 2436677 := bbase (se 4 (by rfl) ⟨228438, by rfl⟩ : syracuseStep 2436677 = 456877) (by norm_num)
theorem B3649157 : Blo 1080619 3649157 := bbase (se 4 (by rfl) ⟨342108, by rfl⟩ : syracuseStep 3649157 = 684217) (by norm_num)
theorem B2436749 : Blo 1080619 2436749 := bbase (se 3 (by rfl) ⟨456890, by rfl⟩ : syracuseStep 2436749 = 913781) (by norm_num)
theorem B2436821 : Blo 1080619 2436821 := bbase (se 7 (by rfl) ⟨28556, by rfl⟩ : syracuseStep 2436821 = 57113) (by norm_num)
theorem B5943061 : Blo 1080619 5943061 := bbase (se 6 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 5943061 = 278581) (by norm_num)
theorem B2436893 : Blo 1080619 2436893 := bbase (se 3 (by rfl) ⟨456917, by rfl⟩ : syracuseStep 2436893 = 913835) (by norm_num)
theorem B2436965 : Blo 1080619 2436965 := bbase (se 4 (by rfl) ⟨228465, by rfl⟩ : syracuseStep 2436965 = 456931) (by norm_num)
theorem B2437037 : Blo 1080619 2437037 := bbase (se 3 (by rfl) ⟨456944, by rfl⟩ : syracuseStep 2437037 = 913889) (by norm_num)
theorem B3289061 : Blo 1080619 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B2437109 : Blo 1080619 2437109 := bbase (se 5 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 2437109 = 228479) (by norm_num)
theorem B3649589 : Blo 1080619 3649589 := bbase (se 5 (by rfl) ⟨171074, by rfl⟩ : syracuseStep 3649589 = 342149) (by norm_num)
theorem B2437181 : Blo 1080619 2437181 := bbase (se 3 (by rfl) ⟨456971, by rfl⟩ : syracuseStep 2437181 = 913943) (by norm_num)
theorem B2437253 : Blo 1080619 2437253 := bbase (se 4 (by rfl) ⟨228492, by rfl⟩ : syracuseStep 2437253 = 456985) (by norm_num)
theorem B2437325 : Blo 1080619 2437325 := bbase (se 3 (by rfl) ⟨456998, by rfl⟩ : syracuseStep 2437325 = 913997) (by norm_num)
theorem B2437397 : Blo 1080619 2437397 := bbase (se 6 (by rfl) ⟨57126, by rfl⟩ : syracuseStep 2437397 = 114253) (by norm_num)
theorem B2928917 : Blo 1080619 2928917 := bbase (se 6 (by rfl) ⟨68646, by rfl⟩ : syracuseStep 2928917 = 137293) (by norm_num)
theorem B2437469 : Blo 1080619 2437469 := bbase (se 3 (by rfl) ⟨457025, by rfl⟩ : syracuseStep 2437469 = 914051) (by norm_num)
theorem B2437541 : Blo 1080619 2437541 := bbase (se 4 (by rfl) ⟨228519, by rfl⟩ : syracuseStep 2437541 = 457039) (by norm_num)
theorem B3650021 : Blo 1080619 3650021 := bbase (se 4 (by rfl) ⟨342189, by rfl⟩ : syracuseStep 3650021 = 684379) (by norm_num)
theorem B2437613 : Blo 1080619 2437613 := bbase (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) (by norm_num)
theorem B12497429 : Blo 1080619 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B2437685 : Blo 1080619 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B5485157 : Blo 1080619 5485157 := bbase (se 4 (by rfl) ⟨514233, by rfl⟩ : syracuseStep 5485157 = 1028467) (by norm_num)
theorem B2437757 : Blo 1080619 2437757 := bbase (se 3 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 2437757 = 914159) (by norm_num)
theorem B6173333 : Blo 1080619 6173333 := bbase (se 6 (by rfl) ⟨144687, by rfl⟩ : syracuseStep 6173333 = 289375) (by norm_num)
theorem B2437829 : Blo 1080619 2437829 := bbase (se 4 (by rfl) ⟨228546, by rfl⟩ : syracuseStep 2437829 = 457093) (by norm_num)
theorem B2601733 : Blo 1080619 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B2437901 : Blo 1080619 2437901 := bbase (se 3 (by rfl) ⟨457106, by rfl⟩ : syracuseStep 2437901 = 914213) (by norm_num)
theorem B2437973 : Blo 1080619 2437973 := bbase (se 9 (by rfl) ⟨7142, by rfl⟩ : syracuseStep 2437973 = 14285) (by norm_num)
theorem B3650453 : Blo 1080619 3650453 := bbase (se 6 (by rfl) ⟨85557, by rfl⟩ : syracuseStep 3650453 = 171115) (by norm_num)
theorem B2438045 : Blo 1080619 2438045 := bbase (se 3 (by rfl) ⟨457133, by rfl⟩ : syracuseStep 2438045 = 914267) (by norm_num)
theorem B4109237 : Blo 1080619 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B2438117 : Blo 1080619 2438117 := bbase (se 4 (by rfl) ⟨228573, by rfl⟩ : syracuseStep 2438117 = 457147) (by norm_num)
theorem B2438189 : Blo 1080619 2438189 := bbase (se 3 (by rfl) ⟨457160, by rfl⟩ : syracuseStep 2438189 = 914321) (by norm_num)
theorem B2438261 : Blo 1080619 2438261 := bbase (se 5 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 2438261 = 228587) (by norm_num)
theorem B2438333 : Blo 1080619 2438333 := bbase (se 3 (by rfl) ⟨457187, by rfl⟩ : syracuseStep 2438333 = 914375) (by norm_num)
theorem B4109525 : Blo 1080619 4109525 := bbase (se 7 (by rfl) ⟨48158, by rfl⟩ : syracuseStep 4109525 = 96317) (by norm_num)
theorem B2438405 : Blo 1080619 2438405 := bbase (se 4 (by rfl) ⟨228600, by rfl⟩ : syracuseStep 2438405 = 457201) (by norm_num)
theorem B9385237 : Blo 1080619 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B3650885 : Blo 1080619 3650885 := bbase (se 4 (by rfl) ⟨342270, by rfl⟩ : syracuseStep 3650885 = 684541) (by norm_num)
theorem B2438477 : Blo 1080619 2438477 := bbase (se 3 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 2438477 = 914429) (by norm_num)
theorem B2438549 : Blo 1080619 2438549 := bbase (se 6 (by rfl) ⟨57153, by rfl⟩ : syracuseStep 2438549 = 114307) (by norm_num)
theorem B2602405 : Blo 1080619 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B5551541 : Blo 1080619 5551541 := bbase (se 5 (by rfl) ⟨260228, by rfl⟩ : syracuseStep 5551541 = 520457) (by norm_num)
theorem B2471381 : Blo 1080619 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B2438621 : Blo 1080619 2438621 := bbase (se 3 (by rfl) ⟨457241, by rfl⟩ : syracuseStep 2438621 = 914483) (by norm_num)
theorem B1848845 : Blo 1080619 1848845 := bbase (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) (by norm_num)
theorem B2438693 : Blo 1080619 2438693 := bbase (se 4 (by rfl) ⟨228627, by rfl⟩ : syracuseStep 2438693 = 457255) (by norm_num)
theorem B2438765 : Blo 1080619 2438765 := bbase (se 3 (by rfl) ⟨457268, by rfl⟩ : syracuseStep 2438765 = 914537) (by norm_num)
theorem B2602637 : Blo 1080619 2602637 := bbase (se 3 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 2602637 = 975989) (by norm_num)
theorem B2438837 : Blo 1080619 2438837 := bbase (se 5 (by rfl) ⟨114320, by rfl⟩ : syracuseStep 2438837 = 228641) (by norm_num)
theorem B2602685 : Blo 1080619 2602685 := bbase (se 3 (by rfl) ⟨488003, by rfl⟩ : syracuseStep 2602685 = 976007) (by norm_num)
theorem B1947349 : Blo 1080619 1947349 := bbase (se 7 (by rfl) ⟨22820, by rfl⟩ : syracuseStep 1947349 = 45641) (by norm_num)
theorem B3651317 : Blo 1080619 3651317 := bbase (se 5 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 3651317 = 342311) (by norm_num)
theorem B2438909 : Blo 1080619 2438909 := bbase (se 3 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 2438909 = 914591) (by norm_num)
theorem B1095449 : Blo 1080619 1095449 := bbase (se 2 (by rfl) ⟨410793, by rfl⟩ : syracuseStep 1095449 = 821587) (by norm_num)
theorem B1947421 : Blo 1080619 1947421 := bbase (se 3 (by rfl) ⟨365141, by rfl⟩ : syracuseStep 1947421 = 730283) (by norm_num)
theorem B2438981 : Blo 1080619 2438981 := bbase (se 4 (by rfl) ⟨228654, by rfl⟩ : syracuseStep 2438981 = 457309) (by norm_num)
theorem B5486453 : Blo 1080619 5486453 := bbase (se 5 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 5486453 = 514355) (by norm_num)
theorem B2439053 : Blo 1080619 2439053 := bbase (se 3 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 2439053 = 914645) (by norm_num)
theorem B9254837 : Blo 1080619 9254837 := bbase (se 5 (by rfl) ⟨433820, by rfl⟩ : syracuseStep 9254837 = 867641) (by norm_num)
theorem B2439125 : Blo 1080619 2439125 := bbase (se 7 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 2439125 = 57167) (by norm_num)
theorem B2439197 : Blo 1080619 2439197 := bbase (se 3 (by rfl) ⟨457349, by rfl⟩ : syracuseStep 2439197 = 914699) (by norm_num)
theorem B2668589 : Blo 1080619 2668589 := bbase (se 3 (by rfl) ⟨500360, by rfl⟩ : syracuseStep 2668589 = 1000721) (by norm_num)
theorem B2472005 : Blo 1080619 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B2340949 : Blo 1080619 2340949 := bbase (se 8 (by rfl) ⟨13716, by rfl⟩ : syracuseStep 2340949 = 27433) (by norm_num)
theorem B1095773 : Blo 1080619 1095773 := bbase (se 3 (by rfl) ⟨205457, by rfl⟩ : syracuseStep 1095773 = 410915) (by norm_num)
theorem B2439269 : Blo 1080619 2439269 := bbase (se 4 (by rfl) ⟨228681, by rfl⟩ : syracuseStep 2439269 = 457363) (by norm_num)
theorem B3651749 : Blo 1080619 3651749 := bbase (se 4 (by rfl) ⟨342351, by rfl⟩ : syracuseStep 3651749 = 684703) (by norm_num)
theorem B2439341 : Blo 1080619 2439341 := bbase (se 3 (by rfl) ⟨457376, by rfl⟩ : syracuseStep 2439341 = 914753) (by norm_num)
theorem B2308277 : Blo 1080619 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B2439413 : Blo 1080619 2439413 := bbase (se 5 (by rfl) ⟨114347, by rfl⟩ : syracuseStep 2439413 = 228695) (by norm_num)
theorem B2439485 : Blo 1080619 2439485 := bbase (se 3 (by rfl) ⟨457403, by rfl⟩ : syracuseStep 2439485 = 914807) (by norm_num)
theorem B4110709 : Blo 1080619 4110709 := bbase (se 5 (by rfl) ⟨192689, by rfl⟩ : syracuseStep 4110709 = 385379) (by norm_num)
theorem B2439557 : Blo 1080619 2439557 := bbase (se 4 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 2439557 = 457417) (by norm_num)
theorem B2439629 : Blo 1080619 2439629 := bbase (se 3 (by rfl) ⟨457430, by rfl⟩ : syracuseStep 2439629 = 914861) (by norm_num)
theorem B2439701 : Blo 1080619 2439701 := bbase (se 6 (by rfl) ⟨57180, by rfl⟩ : syracuseStep 2439701 = 114361) (by norm_num)
theorem B3652181 : Blo 1080619 3652181 := bbase (se 8 (by rfl) ⟨21399, by rfl⟩ : syracuseStep 3652181 = 42799) (by norm_num)
theorem B2341469 : Blo 1080619 2341469 := bbase (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) (by norm_num)
theorem B2439773 : Blo 1080619 2439773 := bbase (se 3 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 2439773 = 914915) (by norm_num)
theorem B2931317 : Blo 1080619 2931317 := bbase (se 5 (by rfl) ⟨137405, by rfl⟩ : syracuseStep 2931317 = 274811) (by norm_num)
theorem B4111013 : Blo 1080619 4111013 := bbase (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) (by norm_num)
theorem B2439845 : Blo 1080619 2439845 := bbase (se 4 (by rfl) ⟨228735, by rfl⟩ : syracuseStep 2439845 = 457471) (by norm_num)
theorem B2439917 : Blo 1080619 2439917 := bbase (se 3 (by rfl) ⟨457484, by rfl⟩ : syracuseStep 2439917 = 914969) (by norm_num)
theorem B1948445 : Blo 1080619 1948445 := bbase (se 3 (by rfl) ⟨365333, by rfl⟩ : syracuseStep 1948445 = 730667) (by norm_num)
theorem B6175541 : Blo 1080619 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B2439989 : Blo 1080619 2439989 := bbase (se 5 (by rfl) ⟨114374, by rfl⟩ : syracuseStep 2439989 = 228749) (by norm_num)
theorem B2440061 : Blo 1080619 2440061 := bbase (se 3 (by rfl) ⟨457511, by rfl⟩ : syracuseStep 2440061 = 915023) (by norm_num)
theorem B2440133 : Blo 1080619 2440133 := bbase (se 4 (by rfl) ⟨228762, by rfl⟩ : syracuseStep 2440133 = 457525) (by norm_num)
theorem B2931653 : Blo 1080619 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B1620941 : Blo 1080619 1620941 := bbase (se 3 (by rfl) ⟨303926, by rfl⟩ : syracuseStep 1620941 = 607853) (by norm_num)
theorem B1620965 : Blo 1080619 1620965 := bbase (se 4 (by rfl) ⟨151965, by rfl⟩ : syracuseStep 1620965 = 303931) (by norm_num)
theorem B1620989 : Blo 1080619 1620989 := bbase (se 3 (by rfl) ⟨303935, by rfl⟩ : syracuseStep 1620989 = 607871) (by norm_num)
theorem B3652613 : Blo 1080619 3652613 := bbase (se 4 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 3652613 = 684865) (by norm_num)
theorem B2440205 : Blo 1080619 2440205 := bbase (se 3 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 2440205 = 915077) (by norm_num)
theorem B1621013 : Blo 1080619 1621013 := bbase (se 6 (by rfl) ⟨37992, by rfl⟩ : syracuseStep 1621013 = 75985) (by norm_num)
theorem B1621037 : Blo 1080619 1621037 := bbase (se 3 (by rfl) ⟨303944, by rfl⟩ : syracuseStep 1621037 = 607889) (by norm_num)
theorem B2309165 : Blo 1080619 2309165 := bbase (se 3 (by rfl) ⟨432968, by rfl⟩ : syracuseStep 2309165 = 865937) (by norm_num)
theorem B2604077 : Blo 1080619 2604077 := bbase (se 3 (by rfl) ⟨488264, by rfl⟩ : syracuseStep 2604077 = 976529) (by norm_num)
theorem B1621061 : Blo 1080619 1621061 := bbase (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) (by norm_num)
theorem B2440277 : Blo 1080619 2440277 := bbase (se 8 (by rfl) ⟨14298, by rfl⟩ : syracuseStep 2440277 = 28597) (by norm_num)
theorem B1621085 : Blo 1080619 1621085 := bbase (se 3 (by rfl) ⟨303953, by rfl⟩ : syracuseStep 1621085 = 607907) (by norm_num)
theorem B1621109 : Blo 1080619 1621109 := bbase (se 5 (by rfl) ⟨75989, by rfl⟩ : syracuseStep 1621109 = 151979) (by norm_num)
theorem B5487749 : Blo 1080619 5487749 := bbase (se 4 (by rfl) ⟨514476, by rfl⟩ : syracuseStep 5487749 = 1028953) (by norm_num)
theorem B1621133 : Blo 1080619 1621133 := bbase (se 3 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 1621133 = 607925) (by norm_num)
theorem B2440349 : Blo 1080619 2440349 := bbase (se 3 (by rfl) ⟨457565, by rfl⟩ : syracuseStep 2440349 = 915131) (by norm_num)
theorem B1621157 : Blo 1080619 1621157 := bbase (se 4 (by rfl) ⟨151983, by rfl⟩ : syracuseStep 1621157 = 303967) (by norm_num)
theorem B2309285 : Blo 1080619 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B1621181 : Blo 1080619 1621181 := bbase (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) (by norm_num)
theorem B1621205 : Blo 1080619 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B1621229 : Blo 1080619 1621229 := bbase (se 3 (by rfl) ⟨303980, by rfl⟩ : syracuseStep 1621229 = 607961) (by norm_num)
theorem B2604269 : Blo 1080619 2604269 := bbase (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) (by norm_num)
theorem B1621253 : Blo 1080619 1621253 := bbase (se 4 (by rfl) ⟨151992, by rfl⟩ : syracuseStep 1621253 = 303985) (by norm_num)
theorem B1621277 : Blo 1080619 1621277 := bbase (se 3 (by rfl) ⟨303989, by rfl⟩ : syracuseStep 1621277 = 607979) (by norm_num)
theorem B1621301 : Blo 1080619 1621301 := bbase (se 5 (by rfl) ⟨75998, by rfl⟩ : syracuseStep 1621301 = 151997) (by norm_num)
theorem B1621325 : Blo 1080619 1621325 := bbase (se 3 (by rfl) ⟨303998, by rfl⟩ : syracuseStep 1621325 = 607997) (by norm_num)
theorem B1621349 : Blo 1080619 1621349 := bbase (se 4 (by rfl) ⟨152001, by rfl⟩ : syracuseStep 1621349 = 304003) (by norm_num)
theorem B1621373 : Blo 1080619 1621373 := bbase (se 3 (by rfl) ⟨304007, by rfl⟩ : syracuseStep 1621373 = 608015) (by norm_num)
theorem B1621397 : Blo 1080619 1621397 := bbase (se 6 (by rfl) ⟨38001, by rfl⟩ : syracuseStep 1621397 = 76003) (by norm_num)
theorem B1621421 : Blo 1080619 1621421 := bbase (se 3 (by rfl) ⟨304016, by rfl⟩ : syracuseStep 1621421 = 608033) (by norm_num)
theorem B3653045 : Blo 1080619 3653045 := bbase (se 5 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 3653045 = 342473) (by norm_num)
theorem B1621445 : Blo 1080619 1621445 := bbase (se 4 (by rfl) ⟨152010, by rfl⟩ : syracuseStep 1621445 = 304021) (by norm_num)
theorem B1621469 : Blo 1080619 1621469 := bbase (se 3 (by rfl) ⟨304025, by rfl⟩ : syracuseStep 1621469 = 608051) (by norm_num)
theorem B1621493 : Blo 1080619 1621493 := bbase (se 5 (by rfl) ⟨76007, by rfl⟩ : syracuseStep 1621493 = 152015) (by norm_num)
theorem B1621517 : Blo 1080619 1621517 := bbase (se 3 (by rfl) ⟨304034, by rfl⟩ : syracuseStep 1621517 = 608069) (by norm_num)
theorem B2735653 : Blo 1080619 2735653 := bbase (se 4 (by rfl) ⟨256467, by rfl⟩ : syracuseStep 2735653 = 512935) (by norm_num)
theorem B1621541 : Blo 1080619 1621541 := bbase (se 4 (by rfl) ⟨152019, by rfl⟩ : syracuseStep 1621541 = 304039) (by norm_num)
theorem B1621565 : Blo 1080619 1621565 := bbase (se 3 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 1621565 = 608087) (by norm_num)
theorem B1621589 : Blo 1080619 1621589 := bbase (se 8 (by rfl) ⟨9501, by rfl⟩ : syracuseStep 1621589 = 19003) (by norm_num)
theorem B1621613 : Blo 1080619 1621613 := bbase (se 3 (by rfl) ⟨304052, by rfl⟩ : syracuseStep 1621613 = 608105) (by norm_num)
theorem B1621637 : Blo 1080619 1621637 := bbase (se 4 (by rfl) ⟨152028, by rfl⟩ : syracuseStep 1621637 = 304057) (by norm_num)
theorem B2735765 : Blo 1080619 2735765 := bbase (se 6 (by rfl) ⟨64119, by rfl⟩ : syracuseStep 2735765 = 128239) (by norm_num)
theorem B1621661 : Blo 1080619 1621661 := bbase (se 3 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 1621661 = 608123) (by norm_num)
theorem B8208053 : Blo 1080619 8208053 := bbase (se 5 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 8208053 = 769505) (by norm_num)
theorem B1621685 : Blo 1080619 1621685 := bbase (se 5 (by rfl) ⟨76016, by rfl⟩ : syracuseStep 1621685 = 152033) (by norm_num)
theorem B1621709 : Blo 1080619 1621709 := bbase (se 3 (by rfl) ⟨304070, by rfl⟩ : syracuseStep 1621709 = 608141) (by norm_num)
theorem B1621733 : Blo 1080619 1621733 := bbase (se 4 (by rfl) ⟨152037, by rfl⟩ : syracuseStep 1621733 = 304075) (by norm_num)
theorem B1621757 : Blo 1080619 1621757 := bbase (se 3 (by rfl) ⟨304079, by rfl⟩ : syracuseStep 1621757 = 608159) (by norm_num)
theorem B1621781 : Blo 1080619 1621781 := bbase (se 6 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 1621781 = 76021) (by norm_num)
theorem B2309917 : Blo 1080619 2309917 := bbase (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) (by norm_num)
theorem B1621805 : Blo 1080619 1621805 := bbase (se 3 (by rfl) ⟨304088, by rfl⟩ : syracuseStep 1621805 = 608177) (by norm_num)
theorem B1621829 : Blo 1080619 1621829 := bbase (se 4 (by rfl) ⟨152046, by rfl⟩ : syracuseStep 1621829 = 304093) (by norm_num)
theorem B1097557 : Blo 1080619 1097557 := bbase (se 9 (by rfl) ⟨3215, by rfl⟩ : syracuseStep 1097557 = 6431) (by norm_num)
theorem B2735957 : Blo 1080619 2735957 := bbase (se 9 (by rfl) ⟨8015, by rfl⟩ : syracuseStep 2735957 = 16031) (by norm_num)
theorem B1621853 : Blo 1080619 1621853 := bbase (se 3 (by rfl) ⟨304097, by rfl⟩ : syracuseStep 1621853 = 608195) (by norm_num)
theorem B3653477 : Blo 1080619 3653477 := bbase (se 4 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 3653477 = 685027) (by norm_num)
theorem B1621877 : Blo 1080619 1621877 := bbase (se 5 (by rfl) ⟨76025, by rfl⟩ : syracuseStep 1621877 = 152051) (by norm_num)
theorem B1621901 : Blo 1080619 1621901 := bbase (se 3 (by rfl) ⟨304106, by rfl⟩ : syracuseStep 1621901 = 608213) (by norm_num)
theorem B1621925 : Blo 1080619 1621925 := bbase (se 4 (by rfl) ⟨152055, by rfl⟩ : syracuseStep 1621925 = 304111) (by norm_num)
theorem B1621949 : Blo 1080619 1621949 := bbase (se 3 (by rfl) ⟨304115, by rfl⟩ : syracuseStep 1621949 = 608231) (by norm_num)
theorem B1621973 : Blo 1080619 1621973 := bbase (se 7 (by rfl) ⟨19007, by rfl⟩ : syracuseStep 1621973 = 38015) (by norm_num)
theorem B1621997 : Blo 1080619 1621997 := bbase (se 3 (by rfl) ⟨304124, by rfl⟩ : syracuseStep 1621997 = 608249) (by norm_num)
theorem B1622021 : Blo 1080619 1622021 := bbase (se 4 (by rfl) ⟨152064, by rfl⟩ : syracuseStep 1622021 = 304129) (by norm_num)
theorem B1097749 : Blo 1080619 1097749 := bbase (se 6 (by rfl) ⟨25728, by rfl⟩ : syracuseStep 1097749 = 51457) (by norm_num)
theorem B1622045 : Blo 1080619 1622045 := bbase (se 3 (by rfl) ⟨304133, by rfl⟩ : syracuseStep 1622045 = 608267) (by norm_num)
theorem B1622069 : Blo 1080619 1622069 := bbase (se 5 (by rfl) ⟨76034, by rfl⟩ : syracuseStep 1622069 = 152069) (by norm_num)
theorem B1622093 : Blo 1080619 1622093 := bbase (se 3 (by rfl) ⟨304142, by rfl⟩ : syracuseStep 1622093 = 608285) (by norm_num)
theorem B1622117 : Blo 1080619 1622117 := bbase (se 4 (by rfl) ⟨152073, by rfl⟩ : syracuseStep 1622117 = 304147) (by norm_num)
theorem B1622141 : Blo 1080619 1622141 := bbase (se 3 (by rfl) ⟨304151, by rfl⟩ : syracuseStep 1622141 = 608303) (by norm_num)
theorem B1622165 : Blo 1080619 1622165 := bbase (se 6 (by rfl) ⟨38019, by rfl⟩ : syracuseStep 1622165 = 76039) (by norm_num)
theorem B2736301 : Blo 1080619 2736301 := bbase (se 3 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 2736301 = 1026113) (by norm_num)
theorem B1622189 : Blo 1080619 1622189 := bbase (se 3 (by rfl) ⟨304160, by rfl⟩ : syracuseStep 1622189 = 608321) (by norm_num)
theorem B1622213 : Blo 1080619 1622213 := bbase (se 4 (by rfl) ⟨152082, by rfl⟩ : syracuseStep 1622213 = 304165) (by norm_num)
theorem B1622237 : Blo 1080619 1622237 := bbase (se 3 (by rfl) ⟨304169, by rfl⟩ : syracuseStep 1622237 = 608339) (by norm_num)
theorem B1622261 : Blo 1080619 1622261 := bbase (se 5 (by rfl) ⟨76043, by rfl⟩ : syracuseStep 1622261 = 152087) (by norm_num)
theorem B5193989 : Blo 1080619 5193989 := bbase (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) (by norm_num)
theorem B1622285 : Blo 1080619 1622285 := bbase (se 3 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 1622285 = 608357) (by norm_num)
theorem B3653909 : Blo 1080619 3653909 := bbase (se 6 (by rfl) ⟨85638, by rfl⟩ : syracuseStep 3653909 = 171277) (by norm_num)
theorem B2736413 : Blo 1080619 2736413 := bbase (se 3 (by rfl) ⟨513077, by rfl⟩ : syracuseStep 2736413 = 1026155) (by norm_num)
theorem B1622309 : Blo 1080619 1622309 := bbase (se 4 (by rfl) ⟨152091, by rfl⟩ : syracuseStep 1622309 = 304183) (by norm_num)
theorem B1622333 : Blo 1080619 1622333 := bbase (se 3 (by rfl) ⟨304187, by rfl⟩ : syracuseStep 1622333 = 608375) (by norm_num)
theorem B1622357 : Blo 1080619 1622357 := bbase (se 10 (by rfl) ⟨2376, by rfl⟩ : syracuseStep 1622357 = 4753) (by norm_num)
theorem B1098085 : Blo 1080619 1098085 := bbase (se 4 (by rfl) ⟨102945, by rfl⟩ : syracuseStep 1098085 = 205891) (by norm_num)
theorem B1622381 : Blo 1080619 1622381 := bbase (se 3 (by rfl) ⟨304196, by rfl⟩ : syracuseStep 1622381 = 608393) (by norm_num)
theorem B1622405 : Blo 1080619 1622405 := bbase (se 4 (by rfl) ⟨152100, by rfl⟩ : syracuseStep 1622405 = 304201) (by norm_num)
theorem B5489045 : Blo 1080619 5489045 := bbase (se 6 (by rfl) ⟨128649, by rfl⟩ : syracuseStep 5489045 = 257299) (by norm_num)
theorem B1622429 : Blo 1080619 1622429 := bbase (se 3 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 1622429 = 608411) (by norm_num)
theorem B1622453 : Blo 1080619 1622453 := bbase (se 5 (by rfl) ⟨76052, by rfl⟩ : syracuseStep 1622453 = 152105) (by norm_num)
theorem B1098173 : Blo 1080619 1098173 := bbase (se 3 (by rfl) ⟨205907, by rfl⟩ : syracuseStep 1098173 = 411815) (by norm_num)
theorem B1622477 : Blo 1080619 1622477 := bbase (se 3 (by rfl) ⟨304214, by rfl⟩ : syracuseStep 1622477 = 608429) (by norm_num)
theorem B2736605 : Blo 1080619 2736605 := bbase (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) (by norm_num)
theorem B1622501 : Blo 1080619 1622501 := bbase (se 4 (by rfl) ⟨152109, by rfl⟩ : syracuseStep 1622501 = 304219) (by norm_num)
theorem B1622525 : Blo 1080619 1622525 := bbase (se 3 (by rfl) ⟨304223, by rfl⟩ : syracuseStep 1622525 = 608447) (by norm_num)
theorem B1622549 : Blo 1080619 1622549 := bbase (se 6 (by rfl) ⟨38028, by rfl⟩ : syracuseStep 1622549 = 76057) (by norm_num)
theorem B1622573 : Blo 1080619 1622573 := bbase (se 3 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 1622573 = 608465) (by norm_num)
theorem B1622597 : Blo 1080619 1622597 := bbase (se 4 (by rfl) ⟨152118, by rfl⟩ : syracuseStep 1622597 = 304237) (by norm_num)
theorem B10535509 : Blo 1080619 10535509 := bbase (se 8 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 10535509 = 123463) (by norm_num)
theorem B1622621 : Blo 1080619 1622621 := bbase (se 3 (by rfl) ⟨304241, by rfl⟩ : syracuseStep 1622621 = 608483) (by norm_num)
theorem B1622645 : Blo 1080619 1622645 := bbase (se 5 (by rfl) ⟨76061, by rfl⟩ : syracuseStep 1622645 = 152123) (by norm_num)
theorem B1622669 : Blo 1080619 1622669 := bbase (se 3 (by rfl) ⟨304250, by rfl⟩ : syracuseStep 1622669 = 608501) (by norm_num)
theorem B2310805 : Blo 1080619 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B1622693 : Blo 1080619 1622693 := bbase (se 4 (by rfl) ⟨152127, by rfl⟩ : syracuseStep 1622693 = 304255) (by norm_num)
theorem B1622717 : Blo 1080619 1622717 := bbase (se 3 (by rfl) ⟨304259, by rfl⟩ : syracuseStep 1622717 = 608519) (by norm_num)
theorem B3654341 : Blo 1080619 3654341 := bbase (se 4 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 3654341 = 685189) (by norm_num)
theorem B1622741 : Blo 1080619 1622741 := bbase (se 7 (by rfl) ⟨19016, by rfl⟩ : syracuseStep 1622741 = 38033) (by norm_num)
theorem B4113125 : Blo 1080619 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B1622765 : Blo 1080619 1622765 := bbase (se 3 (by rfl) ⟨304268, by rfl⟩ : syracuseStep 1622765 = 608537) (by norm_num)
theorem B1622789 : Blo 1080619 1622789 := bbase (se 4 (by rfl) ⟨152136, by rfl⟩ : syracuseStep 1622789 = 304273) (by norm_num)
theorem B2310925 : Blo 1080619 2310925 := bbase (se 3 (by rfl) ⟨433298, by rfl⟩ : syracuseStep 2310925 = 866597) (by norm_num)
theorem B1622813 : Blo 1080619 1622813 := bbase (se 3 (by rfl) ⟨304277, by rfl⟩ : syracuseStep 1622813 = 608555) (by norm_num)
theorem B2736949 : Blo 1080619 2736949 := bbase (se 5 (by rfl) ⟨128294, by rfl⟩ : syracuseStep 2736949 = 256589) (by norm_num)
theorem B1622837 : Blo 1080619 1622837 := bbase (se 5 (by rfl) ⟨76070, by rfl⟩ : syracuseStep 1622837 = 152141) (by norm_num)
theorem B1622861 : Blo 1080619 1622861 := bbase (se 3 (by rfl) ⟨304286, by rfl⟩ : syracuseStep 1622861 = 608573) (by norm_num)
theorem B9257813 : Blo 1080619 9257813 := bbase (se 9 (by rfl) ⟨27122, by rfl⟩ : syracuseStep 9257813 = 54245) (by norm_num)
theorem B1622885 : Blo 1080619 1622885 := bbase (se 4 (by rfl) ⟨152145, by rfl⟩ : syracuseStep 1622885 = 304291) (by norm_num)
theorem B1622909 : Blo 1080619 1622909 := bbase (se 3 (by rfl) ⟨304295, by rfl⟩ : syracuseStep 1622909 = 608591) (by norm_num)
theorem B1622933 : Blo 1080619 1622933 := bbase (se 6 (by rfl) ⟨38037, by rfl⟩ : syracuseStep 1622933 = 76075) (by norm_num)
theorem B2737061 : Blo 1080619 2737061 := bbase (se 4 (by rfl) ⟨256599, by rfl⟩ : syracuseStep 2737061 = 513199) (by norm_num)
theorem B1622957 : Blo 1080619 1622957 := bbase (se 3 (by rfl) ⟨304304, by rfl⟩ : syracuseStep 1622957 = 608609) (by norm_num)
theorem B1622981 : Blo 1080619 1622981 := bbase (se 4 (by rfl) ⟨152154, by rfl⟩ : syracuseStep 1622981 = 304309) (by norm_num)
theorem B1623005 : Blo 1080619 1623005 := bbase (se 3 (by rfl) ⟨304313, by rfl⟩ : syracuseStep 1623005 = 608627) (by norm_num)
theorem B1623029 : Blo 1080619 1623029 := bbase (se 5 (by rfl) ⟨76079, by rfl⟩ : syracuseStep 1623029 = 152159) (by norm_num)
theorem B4113413 : Blo 1080619 4113413 := bbase (se 4 (by rfl) ⟨385632, by rfl⟩ : syracuseStep 4113413 = 771265) (by norm_num)
theorem B1623053 : Blo 1080619 1623053 := bbase (se 3 (by rfl) ⟨304322, by rfl⟩ : syracuseStep 1623053 = 608645) (by norm_num)
theorem B2311181 : Blo 1080619 2311181 := bbase (se 3 (by rfl) ⟨433346, by rfl⟩ : syracuseStep 2311181 = 866693) (by norm_num)
theorem B1623077 : Blo 1080619 1623077 := bbase (se 4 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 1623077 = 304327) (by norm_num)
theorem B1623101 : Blo 1080619 1623101 := bbase (se 3 (by rfl) ⟨304331, by rfl⟩ : syracuseStep 1623101 = 608663) (by norm_num)
theorem B1623125 : Blo 1080619 1623125 := bbase (se 8 (by rfl) ⟨9510, by rfl⟩ : syracuseStep 1623125 = 19021) (by norm_num)
theorem B2737253 : Blo 1080619 2737253 := bbase (se 4 (by rfl) ⟨256617, by rfl⟩ : syracuseStep 2737253 = 513235) (by norm_num)
theorem B1623149 : Blo 1080619 1623149 := bbase (se 3 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 1623149 = 608681) (by norm_num)
theorem B3654773 : Blo 1080619 3654773 := bbase (se 5 (by rfl) ⟨171317, by rfl⟩ : syracuseStep 3654773 = 342635) (by norm_num)
theorem B1623173 : Blo 1080619 1623173 := bbase (se 4 (by rfl) ⟨152172, by rfl⟩ : syracuseStep 1623173 = 304345) (by norm_num)
theorem B1623197 : Blo 1080619 1623197 := bbase (se 3 (by rfl) ⟨304349, by rfl⟩ : syracuseStep 1623197 = 608699) (by norm_num)
theorem B1623221 : Blo 1080619 1623221 := bbase (se 5 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 1623221 = 152177) (by norm_num)
theorem B1623245 : Blo 1080619 1623245 := bbase (se 3 (by rfl) ⟨304358, by rfl⟩ : syracuseStep 1623245 = 608717) (by norm_num)
theorem B1623269 : Blo 1080619 1623269 := bbase (se 4 (by rfl) ⟨152181, by rfl⟩ : syracuseStep 1623269 = 304363) (by norm_num)
theorem B1623293 : Blo 1080619 1623293 := bbase (se 3 (by rfl) ⟨304367, by rfl⟩ : syracuseStep 1623293 = 608735) (by norm_num)
theorem B1623317 : Blo 1080619 1623317 := bbase (se 6 (by rfl) ⟨38046, by rfl⟩ : syracuseStep 1623317 = 76093) (by norm_num)
theorem B1623341 : Blo 1080619 1623341 := bbase (se 3 (by rfl) ⟨304376, by rfl⟩ : syracuseStep 1623341 = 608753) (by norm_num)
theorem B1623365 : Blo 1080619 1623365 := bbase (se 4 (by rfl) ⟨152190, by rfl⟩ : syracuseStep 1623365 = 304381) (by norm_num)
theorem B1623389 : Blo 1080619 1623389 := bbase (se 3 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 1623389 = 608771) (by norm_num)
theorem B1623413 : Blo 1080619 1623413 := bbase (se 5 (by rfl) ⟨76097, by rfl⟩ : syracuseStep 1623413 = 152195) (by norm_num)
theorem B1623437 : Blo 1080619 1623437 := bbase (se 3 (by rfl) ⟨304394, by rfl⟩ : syracuseStep 1623437 = 608789) (by norm_num)
theorem B1623461 : Blo 1080619 1623461 := bbase (se 4 (by rfl) ⟨152199, by rfl⟩ : syracuseStep 1623461 = 304399) (by norm_num)
theorem B2737597 : Blo 1080619 2737597 := bbase (se 3 (by rfl) ⟨513299, by rfl⟩ : syracuseStep 2737597 = 1026599) (by norm_num)
theorem B1623485 : Blo 1080619 1623485 := bbase (se 3 (by rfl) ⟨304403, by rfl⟩ : syracuseStep 1623485 = 608807) (by norm_num)
theorem B1623509 : Blo 1080619 1623509 := bbase (se 7 (by rfl) ⟨19025, by rfl⟩ : syracuseStep 1623509 = 38051) (by norm_num)
theorem B1623533 : Blo 1080619 1623533 := bbase (se 3 (by rfl) ⟨304412, by rfl⟩ : syracuseStep 1623533 = 608825) (by norm_num)
theorem B1623557 : Blo 1080619 1623557 := bbase (se 4 (by rfl) ⟨152208, by rfl⟩ : syracuseStep 1623557 = 304417) (by norm_num)
theorem B1623581 : Blo 1080619 1623581 := bbase (se 3 (by rfl) ⟨304421, by rfl⟩ : syracuseStep 1623581 = 608843) (by norm_num)
theorem B3655205 : Blo 1080619 3655205 := bbase (se 4 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 3655205 = 685351) (by norm_num)
theorem B2737709 : Blo 1080619 2737709 := bbase (se 3 (by rfl) ⟨513320, by rfl⟩ : syracuseStep 2737709 = 1026641) (by norm_num)
theorem B1623605 : Blo 1080619 1623605 := bbase (se 5 (by rfl) ⟨76106, by rfl⟩ : syracuseStep 1623605 = 152213) (by norm_num)
theorem B1623629 : Blo 1080619 1623629 := bbase (se 3 (by rfl) ⟨304430, by rfl⟩ : syracuseStep 1623629 = 608861) (by norm_num)
theorem B1623653 : Blo 1080619 1623653 := bbase (se 4 (by rfl) ⟨152217, by rfl⟩ : syracuseStep 1623653 = 304435) (by norm_num)
theorem B1623677 : Blo 1080619 1623677 := bbase (se 3 (by rfl) ⟨304439, by rfl⟩ : syracuseStep 1623677 = 608879) (by norm_num)
theorem B1951357 : Blo 1080619 1951357 := bbase (se 3 (by rfl) ⟨365879, by rfl⟩ : syracuseStep 1951357 = 731759) (by norm_num)
theorem B1623701 : Blo 1080619 1623701 := bbase (se 6 (by rfl) ⟨38055, by rfl⟩ : syracuseStep 1623701 = 76111) (by norm_num)
theorem B5490341 : Blo 1080619 5490341 := bbase (se 4 (by rfl) ⟨514719, by rfl⟩ : syracuseStep 5490341 = 1029439) (by norm_num)
theorem B1623725 : Blo 1080619 1623725 := bbase (se 3 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 1623725 = 608897) (by norm_num)
theorem B1623749 : Blo 1080619 1623749 := bbase (se 4 (by rfl) ⟨152226, by rfl⟩ : syracuseStep 1623749 = 304453) (by norm_num)
theorem B1623773 : Blo 1080619 1623773 := bbase (se 3 (by rfl) ⟨304457, by rfl⟩ : syracuseStep 1623773 = 608915) (by norm_num)
theorem B2737901 : Blo 1080619 2737901 := bbase (se 3 (by rfl) ⟨513356, by rfl⟩ : syracuseStep 2737901 = 1026713) (by norm_num)
theorem B1623797 : Blo 1080619 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B1623821 : Blo 1080619 1623821 := bbase (se 3 (by rfl) ⟨304466, by rfl⟩ : syracuseStep 1623821 = 608933) (by norm_num)
theorem B1623845 : Blo 1080619 1623845 := bbase (se 4 (by rfl) ⟨152235, by rfl⟩ : syracuseStep 1623845 = 304471) (by norm_num)
theorem B1623869 : Blo 1080619 1623869 := bbase (se 3 (by rfl) ⟨304475, by rfl⟩ : syracuseStep 1623869 = 608951) (by norm_num)
theorem B1623893 : Blo 1080619 1623893 := bbase (se 9 (by rfl) ⟨4757, by rfl⟩ : syracuseStep 1623893 = 9515) (by norm_num)
theorem B1623917 : Blo 1080619 1623917 := bbase (se 3 (by rfl) ⟨304484, by rfl⟩ : syracuseStep 1623917 = 608969) (by norm_num)
theorem B2312069 : Blo 1080619 2312069 := bbase (se 4 (by rfl) ⟨216756, by rfl⟩ : syracuseStep 2312069 = 433513) (by norm_num)
theorem B1623941 : Blo 1080619 1623941 := bbase (se 4 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 1623941 = 304489) (by norm_num)
theorem B1623965 : Blo 1080619 1623965 := bbase (se 3 (by rfl) ⟨304493, by rfl⟩ : syracuseStep 1623965 = 608987) (by norm_num)
theorem B1623989 : Blo 1080619 1623989 := bbase (se 5 (by rfl) ⟨76124, by rfl⟩ : syracuseStep 1623989 = 152249) (by norm_num)
theorem B1624013 : Blo 1080619 1624013 := bbase (se 3 (by rfl) ⟨304502, by rfl⟩ : syracuseStep 1624013 = 609005) (by norm_num)
theorem B3655637 : Blo 1080619 3655637 := bbase (se 7 (by rfl) ⟨42839, by rfl⟩ : syracuseStep 3655637 = 85679) (by norm_num)
theorem B1624037 : Blo 1080619 1624037 := bbase (se 4 (by rfl) ⟨152253, by rfl⟩ : syracuseStep 1624037 = 304507) (by norm_num)
theorem B1624061 : Blo 1080619 1624061 := bbase (se 3 (by rfl) ⟨304511, by rfl⟩ : syracuseStep 1624061 = 609023) (by norm_num)
theorem B1624085 : Blo 1080619 1624085 := bbase (se 6 (by rfl) ⟨38064, by rfl⟩ : syracuseStep 1624085 = 76129) (by norm_num)
theorem B1624109 : Blo 1080619 1624109 := bbase (se 3 (by rfl) ⟨304520, by rfl⟩ : syracuseStep 1624109 = 609041) (by norm_num)
theorem B2738245 : Blo 1080619 2738245 := bbase (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) (by norm_num)
theorem B1624133 : Blo 1080619 1624133 := bbase (se 4 (by rfl) ⟨152262, by rfl⟩ : syracuseStep 1624133 = 304525) (by norm_num)
theorem B11683925 : Blo 1080619 11683925 := bbase (se 8 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 11683925 = 136921) (by norm_num)
theorem B1624157 : Blo 1080619 1624157 := bbase (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) (by norm_num)
theorem B1755245 : Blo 1080619 1755245 := bbase (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) (by norm_num)
theorem B2312309 : Blo 1080619 2312309 := bbase (se 5 (by rfl) ⟨108389, by rfl⟩ : syracuseStep 2312309 = 216779) (by norm_num)
theorem B1624181 : Blo 1080619 1624181 := bbase (se 5 (by rfl) ⟨76133, by rfl⟩ : syracuseStep 1624181 = 152267) (by norm_num)
theorem B1624205 : Blo 1080619 1624205 := bbase (se 3 (by rfl) ⟨304538, by rfl⟩ : syracuseStep 1624205 = 609077) (by norm_num)
theorem B1624229 : Blo 1080619 1624229 := bbase (se 4 (by rfl) ⟨152271, by rfl⟩ : syracuseStep 1624229 = 304543) (by norm_num)
theorem B4114597 : Blo 1080619 4114597 := bbase (se 4 (by rfl) ⟨385743, by rfl⟩ : syracuseStep 4114597 = 771487) (by norm_num)
theorem B2738357 : Blo 1080619 2738357 := bbase (se 5 (by rfl) ⟨128360, by rfl⟩ : syracuseStep 2738357 = 256721) (by norm_num)
theorem B1624253 : Blo 1080619 1624253 := bbase (se 3 (by rfl) ⟨304547, by rfl⟩ : syracuseStep 1624253 = 609095) (by norm_num)
theorem B1624277 : Blo 1080619 1624277 := bbase (se 7 (by rfl) ⟨19034, by rfl⟩ : syracuseStep 1624277 = 38069) (by norm_num)
theorem B5196005 : Blo 1080619 5196005 := bbase (se 4 (by rfl) ⟨487125, by rfl⟩ : syracuseStep 5196005 = 974251) (by norm_num)
theorem B1624301 : Blo 1080619 1624301 := bbase (se 3 (by rfl) ⟨304556, by rfl⟩ : syracuseStep 1624301 = 609113) (by norm_num)
theorem B1624325 : Blo 1080619 1624325 := bbase (se 4 (by rfl) ⟨152280, by rfl⟩ : syracuseStep 1624325 = 304561) (by norm_num)
theorem B1624349 : Blo 1080619 1624349 := bbase (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) (by norm_num)
theorem B1624373 : Blo 1080619 1624373 := bbase (se 5 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 1624373 = 152285) (by norm_num)
theorem B1624397 : Blo 1080619 1624397 := bbase (se 3 (by rfl) ⟨304574, by rfl⟩ : syracuseStep 1624397 = 609149) (by norm_num)
theorem B1624421 : Blo 1080619 1624421 := bbase (se 4 (by rfl) ⟨152289, by rfl⟩ : syracuseStep 1624421 = 304579) (by norm_num)
theorem B2738549 : Blo 1080619 2738549 := bbase (se 5 (by rfl) ⟨128369, by rfl⟩ : syracuseStep 2738549 = 256739) (by norm_num)
theorem B1624445 : Blo 1080619 1624445 := bbase (se 3 (by rfl) ⟨304583, by rfl⟩ : syracuseStep 1624445 = 609167) (by norm_num)
theorem B3656069 : Blo 1080619 3656069 := bbase (se 4 (by rfl) ⟨342756, by rfl⟩ : syracuseStep 3656069 = 685513) (by norm_num)
theorem B5851541 : Blo 1080619 5851541 := bbase (se 6 (by rfl) ⟨137145, by rfl⟩ : syracuseStep 5851541 = 274291) (by norm_num)
theorem B1624469 : Blo 1080619 1624469 := bbase (se 6 (by rfl) ⟨38073, by rfl⟩ : syracuseStep 1624469 = 76147) (by norm_num)
theorem B1624493 : Blo 1080619 1624493 := bbase (se 3 (by rfl) ⟨304592, by rfl⟩ : syracuseStep 1624493 = 609185) (by norm_num)
theorem B1624517 : Blo 1080619 1624517 := bbase (se 4 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 1624517 = 304597) (by norm_num)
theorem B4114901 : Blo 1080619 4114901 := bbase (se 7 (by rfl) ⟨48221, by rfl⟩ : syracuseStep 4114901 = 96443) (by norm_num)
theorem B1624541 : Blo 1080619 1624541 := bbase (se 3 (by rfl) ⟨304601, by rfl⟩ : syracuseStep 1624541 = 609203) (by norm_num)
theorem B1624565 : Blo 1080619 1624565 := bbase (se 5 (by rfl) ⟨76151, by rfl⟩ : syracuseStep 1624565 = 152303) (by norm_num)
theorem B1624589 : Blo 1080619 1624589 := bbase (se 3 (by rfl) ⟨304610, by rfl⟩ : syracuseStep 1624589 = 609221) (by norm_num)
theorem B5556757 : Blo 1080619 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B1624613 : Blo 1080619 1624613 := bbase (se 4 (by rfl) ⟨152307, by rfl⟩ : syracuseStep 1624613 = 304615) (by norm_num)
theorem B1624637 : Blo 1080619 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B1624661 : Blo 1080619 1624661 := bbase (se 8 (by rfl) ⟨9519, by rfl⟩ : syracuseStep 1624661 = 19039) (by norm_num)
theorem B2312813 : Blo 1080619 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B1624685 : Blo 1080619 1624685 := bbase (se 3 (by rfl) ⟨304628, by rfl⟩ : syracuseStep 1624685 = 609257) (by norm_num)
theorem B2312821 : Blo 1080619 2312821 := bbase (se 5 (by rfl) ⟨108413, by rfl⟩ : syracuseStep 2312821 = 216827) (by norm_num)
theorem B1624709 : Blo 1080619 1624709 := bbase (se 4 (by rfl) ⟨152316, by rfl⟩ : syracuseStep 1624709 = 304633) (by norm_num)
theorem B2083477 : Blo 1080619 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B1624733 : Blo 1080619 1624733 := bbase (se 3 (by rfl) ⟨304637, by rfl⟩ : syracuseStep 1624733 = 609275) (by norm_num)
theorem B1624757 : Blo 1080619 1624757 := bbase (se 5 (by rfl) ⟨76160, by rfl⟩ : syracuseStep 1624757 = 152321) (by norm_num)
theorem B2738893 : Blo 1080619 2738893 := bbase (se 3 (by rfl) ⟨513542, by rfl⟩ : syracuseStep 2738893 = 1027085) (by norm_num)
theorem B1624781 : Blo 1080619 1624781 := bbase (se 3 (by rfl) ⟨304646, by rfl⟩ : syracuseStep 1624781 = 609293) (by norm_num)
theorem B1624805 : Blo 1080619 1624805 := bbase (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) (by norm_num)
theorem B1624829 : Blo 1080619 1624829 := bbase (se 3 (by rfl) ⟨304655, by rfl⟩ : syracuseStep 1624829 = 609311) (by norm_num)
theorem B1624853 : Blo 1080619 1624853 := bbase (se 6 (by rfl) ⟨38082, by rfl⟩ : syracuseStep 1624853 = 76165) (by norm_num)
theorem B1624877 : Blo 1080619 1624877 := bbase (se 3 (by rfl) ⟨304664, by rfl⟩ : syracuseStep 1624877 = 609329) (by norm_num)
theorem B3656501 : Blo 1080619 3656501 := bbase (se 5 (by rfl) ⟨171398, by rfl⟩ : syracuseStep 3656501 = 342797) (by norm_num)
theorem B2739005 : Blo 1080619 2739005 := bbase (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) (by norm_num)
theorem B1624901 : Blo 1080619 1624901 := bbase (se 4 (by rfl) ⟨152334, by rfl⟩ : syracuseStep 1624901 = 304669) (by norm_num)
theorem B46877525 : Blo 1080619 46877525 := bbase (se 9 (by rfl) ⟨137336, by rfl⟩ : syracuseStep 46877525 = 274673) (by norm_num)
theorem B1624925 : Blo 1080619 1624925 := bbase (se 3 (by rfl) ⟨304673, by rfl⟩ : syracuseStep 1624925 = 609347) (by norm_num)
theorem B1624949 : Blo 1080619 1624949 := bbase (se 5 (by rfl) ⟨76169, by rfl⟩ : syracuseStep 1624949 = 152339) (by norm_num)
theorem B1624973 : Blo 1080619 1624973 := bbase (se 3 (by rfl) ⟨304682, by rfl⟩ : syracuseStep 1624973 = 609365) (by norm_num)
theorem B1624997 : Blo 1080619 1624997 := bbase (se 4 (by rfl) ⟨152343, by rfl⟩ : syracuseStep 1624997 = 304687) (by norm_num)
theorem B1854373 : Blo 1080619 1854373 := bbase (se 4 (by rfl) ⟨173847, by rfl⟩ : syracuseStep 1854373 = 347695) (by norm_num)
theorem B1625021 : Blo 1080619 1625021 := bbase (se 3 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 1625021 = 609383) (by norm_num)
theorem B5196757 : Blo 1080619 5196757 := bbase (se 7 (by rfl) ⟨60899, by rfl⟩ : syracuseStep 5196757 = 121799) (by norm_num)
theorem B1625045 : Blo 1080619 1625045 := bbase (se 7 (by rfl) ⟨19043, by rfl⟩ : syracuseStep 1625045 = 38087) (by norm_num)
theorem B1625069 : Blo 1080619 1625069 := bbase (se 3 (by rfl) ⟨304700, by rfl⟩ : syracuseStep 1625069 = 609401) (by norm_num)
theorem B2739197 : Blo 1080619 2739197 := bbase (se 3 (by rfl) ⟨513599, by rfl⟩ : syracuseStep 2739197 = 1027199) (by norm_num)
theorem B1625093 : Blo 1080619 1625093 := bbase (se 4 (by rfl) ⟨152352, by rfl⟩ : syracuseStep 1625093 = 304705) (by norm_num)
theorem B1625117 : Blo 1080619 1625117 := bbase (se 3 (by rfl) ⟨304709, by rfl⟩ : syracuseStep 1625117 = 609419) (by norm_num)
theorem B1625141 : Blo 1080619 1625141 := bbase (se 5 (by rfl) ⟨76178, by rfl⟩ : syracuseStep 1625141 = 152357) (by norm_num)
theorem B1625165 : Blo 1080619 1625165 := bbase (se 3 (by rfl) ⟨304718, by rfl⟩ : syracuseStep 1625165 = 609437) (by norm_num)
theorem B1625189 : Blo 1080619 1625189 := bbase (se 4 (by rfl) ⟨152361, by rfl⟩ : syracuseStep 1625189 = 304723) (by norm_num)
theorem B4934773 : Blo 1080619 4934773 := bbase (se 5 (by rfl) ⟨231317, by rfl⟩ : syracuseStep 4934773 = 462635) (by norm_num)
theorem B1952885 : Blo 1080619 1952885 := bbase (se 5 (by rfl) ⟨91541, by rfl⟩ : syracuseStep 1952885 = 183083) (by norm_num)
theorem B1625213 : Blo 1080619 1625213 := bbase (se 3 (by rfl) ⟨304727, by rfl⟩ : syracuseStep 1625213 = 609455) (by norm_num)
theorem B1625237 : Blo 1080619 1625237 := bbase (se 6 (by rfl) ⟨38091, by rfl⟩ : syracuseStep 1625237 = 76183) (by norm_num)
theorem B1625261 : Blo 1080619 1625261 := bbase (se 3 (by rfl) ⟨304736, by rfl⟩ : syracuseStep 1625261 = 609473) (by norm_num)
theorem B1952957 : Blo 1080619 1952957 := bbase (se 3 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 1952957 = 732359) (by norm_num)
theorem B1625285 : Blo 1080619 1625285 := bbase (se 4 (by rfl) ⟨152370, by rfl⟩ : syracuseStep 1625285 = 304741) (by norm_num)
theorem B1625309 : Blo 1080619 1625309 := bbase (se 3 (by rfl) ⟨304745, by rfl⟩ : syracuseStep 1625309 = 609491) (by norm_num)
theorem B3656933 : Blo 1080619 3656933 := bbase (se 4 (by rfl) ⟨342837, by rfl⟩ : syracuseStep 3656933 = 685675) (by norm_num)
theorem B1625333 : Blo 1080619 1625333 := bbase (se 5 (by rfl) ⟨76187, by rfl⟩ : syracuseStep 1625333 = 152375) (by norm_num)
theorem B1625357 : Blo 1080619 1625357 := bbase (se 3 (by rfl) ⟨304754, by rfl⟩ : syracuseStep 1625357 = 609509) (by norm_num)
theorem B1625381 : Blo 1080619 1625381 := bbase (se 4 (by rfl) ⟨152379, by rfl⟩ : syracuseStep 1625381 = 304759) (by norm_num)
theorem B1625405 : Blo 1080619 1625405 := bbase (se 3 (by rfl) ⟨304763, by rfl⟩ : syracuseStep 1625405 = 609527) (by norm_num)
theorem B2739541 : Blo 1080619 2739541 := bbase (se 11 (by rfl) ⟨2006, by rfl⟩ : syracuseStep 2739541 = 4013) (by norm_num)
theorem B1625429 : Blo 1080619 1625429 := bbase (se 11 (by rfl) ⟨1190, by rfl⟩ : syracuseStep 1625429 = 2381) (by norm_num)
theorem B1625453 : Blo 1080619 1625453 := bbase (se 3 (by rfl) ⟨304772, by rfl⟩ : syracuseStep 1625453 = 609545) (by norm_num)
theorem B1625477 : Blo 1080619 1625477 := bbase (se 4 (by rfl) ⟨152388, by rfl⟩ : syracuseStep 1625477 = 304777) (by norm_num)
theorem B1625501 : Blo 1080619 1625501 := bbase (se 3 (by rfl) ⟨304781, by rfl⟩ : syracuseStep 1625501 = 609563) (by norm_num)
theorem B1854893 : Blo 1080619 1854893 := bbase (se 3 (by rfl) ⟨347792, by rfl⟩ : syracuseStep 1854893 = 695585) (by norm_num)
theorem B1625525 : Blo 1080619 1625525 := bbase (se 5 (by rfl) ⟨76196, by rfl⟩ : syracuseStep 1625525 = 152393) (by norm_num)
theorem B2739653 : Blo 1080619 2739653 := bbase (se 4 (by rfl) ⟨256842, by rfl⟩ : syracuseStep 2739653 = 513685) (by norm_num)
theorem B1625549 : Blo 1080619 1625549 := bbase (se 3 (by rfl) ⟨304790, by rfl⟩ : syracuseStep 1625549 = 609581) (by norm_num)
theorem B1625573 : Blo 1080619 1625573 := bbase (se 4 (by rfl) ⟨152397, by rfl⟩ : syracuseStep 1625573 = 304795) (by norm_num)
theorem B2051581 : Blo 1080619 2051581 := bbase (se 3 (by rfl) ⟨384671, by rfl⟩ : syracuseStep 2051581 = 769343) (by norm_num)
theorem B1625597 : Blo 1080619 1625597 := bbase (se 3 (by rfl) ⟨304799, by rfl⟩ : syracuseStep 1625597 = 609599) (by norm_num)
theorem B1625621 : Blo 1080619 1625621 := bbase (se 6 (by rfl) ⟨38100, by rfl⟩ : syracuseStep 1625621 = 76201) (by norm_num)
theorem B1625645 : Blo 1080619 1625645 := bbase (se 3 (by rfl) ⟨304808, by rfl⟩ : syracuseStep 1625645 = 609617) (by norm_num)
theorem B1625669 : Blo 1080619 1625669 := bbase (se 4 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 1625669 = 304813) (by norm_num)
theorem B1625693 : Blo 1080619 1625693 := bbase (se 3 (by rfl) ⟨304817, by rfl⟩ : syracuseStep 1625693 = 609635) (by norm_num)
theorem B1625717 : Blo 1080619 1625717 := bbase (se 5 (by rfl) ⟨76205, by rfl⟩ : syracuseStep 1625717 = 152411) (by norm_num)
theorem B2739845 : Blo 1080619 2739845 := bbase (se 4 (by rfl) ⟨256860, by rfl⟩ : syracuseStep 2739845 = 513721) (by norm_num)
theorem B2051725 : Blo 1080619 2051725 := bbase (se 3 (by rfl) ⟨384698, by rfl⟩ : syracuseStep 2051725 = 769397) (by norm_num)
theorem B1625741 : Blo 1080619 1625741 := bbase (se 3 (by rfl) ⟨304826, by rfl⟩ : syracuseStep 1625741 = 609653) (by norm_num)
theorem B3657365 : Blo 1080619 3657365 := bbase (se 6 (by rfl) ⟨85719, by rfl⟩ : syracuseStep 3657365 = 171439) (by norm_num)
theorem B1756829 : Blo 1080619 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B1625765 : Blo 1080619 1625765 := bbase (se 4 (by rfl) ⟨152415, by rfl⟩ : syracuseStep 1625765 = 304831) (by norm_num)
theorem B1953461 : Blo 1080619 1953461 := bbase (se 5 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 1953461 = 183137) (by norm_num)
theorem B1625789 : Blo 1080619 1625789 := bbase (se 3 (by rfl) ⟨304835, by rfl⟩ : syracuseStep 1625789 = 609671) (by norm_num)
theorem B1625813 : Blo 1080619 1625813 := bbase (se 7 (by rfl) ⟨19052, by rfl⟩ : syracuseStep 1625813 = 38105) (by norm_num)
theorem B2313949 : Blo 1080619 2313949 := bbase (se 3 (by rfl) ⟨433865, by rfl⟩ : syracuseStep 2313949 = 867731) (by norm_num)
theorem B1625837 : Blo 1080619 1625837 := bbase (se 3 (by rfl) ⟨304844, by rfl⟩ : syracuseStep 1625837 = 609689) (by norm_num)
theorem B1625861 : Blo 1080619 1625861 := bbase (se 4 (by rfl) ⟨152424, by rfl⟩ : syracuseStep 1625861 = 304849) (by norm_num)
theorem B1625885 : Blo 1080619 1625885 := bbase (se 3 (by rfl) ⟨304853, by rfl⟩ : syracuseStep 1625885 = 609707) (by norm_num)
theorem B2051885 : Blo 1080619 2051885 := bbase (se 3 (by rfl) ⟨384728, by rfl⟩ : syracuseStep 2051885 = 769457) (by norm_num)
theorem B1625909 : Blo 1080619 1625909 := bbase (se 5 (by rfl) ⟨76214, by rfl⟩ : syracuseStep 1625909 = 152429) (by norm_num)
theorem B1232705 : Blo 1080619 1232705 := bbase (se 2 (by rfl) ⟨462264, by rfl⟩ : syracuseStep 1232705 = 924529) (by norm_num)
theorem B1625933 : Blo 1080619 1625933 := bbase (se 3 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 1625933 = 609725) (by norm_num)
theorem B1625957 : Blo 1080619 1625957 := bbase (se 4 (by rfl) ⟨152433, by rfl⟩ : syracuseStep 1625957 = 304867) (by norm_num)
theorem B1625981 : Blo 1080619 1625981 := bbase (se 3 (by rfl) ⟨304871, by rfl⟩ : syracuseStep 1625981 = 609743) (by norm_num)
theorem B1626005 : Blo 1080619 1626005 := bbase (se 6 (by rfl) ⟨38109, by rfl⟩ : syracuseStep 1626005 = 76219) (by norm_num)
theorem B1626029 : Blo 1080619 1626029 := bbase (se 3 (by rfl) ⟨304880, by rfl⟩ : syracuseStep 1626029 = 609761) (by norm_num)
theorem B2052029 : Blo 1080619 2052029 := bbase (se 3 (by rfl) ⟨384755, by rfl⟩ : syracuseStep 2052029 = 769511) (by norm_num)
theorem B1626053 : Blo 1080619 1626053 := bbase (se 4 (by rfl) ⟨152442, by rfl⟩ : syracuseStep 1626053 = 304885) (by norm_num)
theorem B2740189 : Blo 1080619 2740189 := bbase (se 3 (by rfl) ⟨513785, by rfl⟩ : syracuseStep 2740189 = 1027571) (by norm_num)
theorem B1626077 : Blo 1080619 1626077 := bbase (se 3 (by rfl) ⟨304889, by rfl⟩ : syracuseStep 1626077 = 609779) (by norm_num)
theorem B1626101 : Blo 1080619 1626101 := bbase (se 5 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 1626101 = 152447) (by norm_num)
theorem B1298425 : Blo 1080619 1298425 := bbase (se 2 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 1298425 = 973819) (by norm_num)
theorem B1626125 : Blo 1080619 1626125 := bbase (se 3 (by rfl) ⟨304898, by rfl⟩ : syracuseStep 1626125 = 609797) (by norm_num)
theorem B1626149 : Blo 1080619 1626149 := bbase (se 4 (by rfl) ⟨152451, by rfl⟩ : syracuseStep 1626149 = 304903) (by norm_num)
theorem B1626173 : Blo 1080619 1626173 := bbase (se 3 (by rfl) ⟨304907, by rfl⟩ : syracuseStep 1626173 = 609815) (by norm_num)
theorem B3657797 : Blo 1080619 3657797 := bbase (se 4 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 3657797 = 685837) (by norm_num)
theorem B2740301 : Blo 1080619 2740301 := bbase (se 3 (by rfl) ⟨513806, by rfl⟩ : syracuseStep 2740301 = 1027613) (by norm_num)
theorem B2314325 : Blo 1080619 2314325 := bbase (se 8 (by rfl) ⟨13560, by rfl⟩ : syracuseStep 2314325 = 27121) (by norm_num)
theorem B1626197 : Blo 1080619 1626197 := bbase (se 8 (by rfl) ⟨9528, by rfl⟩ : syracuseStep 1626197 = 19057) (by norm_num)
theorem B1298521 : Blo 1080619 1298521 := bbase (se 2 (by rfl) ⟨486945, by rfl⟩ : syracuseStep 1298521 = 973891) (by norm_num)
theorem B1626221 : Blo 1080619 1626221 := bbase (se 3 (by rfl) ⟨304916, by rfl⟩ : syracuseStep 1626221 = 609833) (by norm_num)
theorem B1626245 : Blo 1080619 1626245 := bbase (se 4 (by rfl) ⟨152460, by rfl⟩ : syracuseStep 1626245 = 304921) (by norm_num)
theorem B1626269 : Blo 1080619 1626269 := bbase (se 3 (by rfl) ⟨304925, by rfl⟩ : syracuseStep 1626269 = 609851) (by norm_num)
theorem B1626293 : Blo 1080619 1626293 := bbase (se 5 (by rfl) ⟨76232, by rfl⟩ : syracuseStep 1626293 = 152465) (by norm_num)
theorem B1462469 : Blo 1080619 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B1626317 : Blo 1080619 1626317 := bbase (se 3 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 1626317 = 609869) (by norm_num)
theorem B2052317 : Blo 1080619 2052317 := bbase (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) (by norm_num)
theorem B1462501 : Blo 1080619 1462501 := bbase (se 4 (by rfl) ⟨137109, by rfl⟩ : syracuseStep 1462501 = 274219) (by norm_num)
theorem B1626341 : Blo 1080619 1626341 := bbase (se 4 (by rfl) ⟨152469, by rfl⟩ : syracuseStep 1626341 = 304939) (by norm_num)
theorem B1626365 : Blo 1080619 1626365 := bbase (se 3 (by rfl) ⟨304943, by rfl⟩ : syracuseStep 1626365 = 609887) (by norm_num)
theorem B2740493 : Blo 1080619 2740493 := bbase (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) (by norm_num)
theorem B1626389 : Blo 1080619 1626389 := bbase (se 6 (by rfl) ⟨38118, by rfl⟩ : syracuseStep 1626389 = 76237) (by norm_num)
theorem B1233193 : Blo 1080619 1233193 := bbase (se 2 (by rfl) ⟨462447, by rfl⟩ : syracuseStep 1233193 = 924895) (by norm_num)
theorem B1626413 : Blo 1080619 1626413 := bbase (se 3 (by rfl) ⟨304952, by rfl⟩ : syracuseStep 1626413 = 609905) (by norm_num)
theorem B1626437 : Blo 1080619 1626437 := bbase (se 4 (by rfl) ⟨152478, by rfl⟩ : syracuseStep 1626437 = 304957) (by norm_num)
theorem B1233229 : Blo 1080619 1233229 := bbase (se 3 (by rfl) ⟨231230, by rfl⟩ : syracuseStep 1233229 = 462461) (by norm_num)
theorem B1626461 : Blo 1080619 1626461 := bbase (se 3 (by rfl) ⟨304961, by rfl⟩ : syracuseStep 1626461 = 609923) (by norm_num)
theorem B2052469 : Blo 1080619 2052469 := bbase (se 5 (by rfl) ⟨96209, by rfl⟩ : syracuseStep 2052469 = 192419) (by norm_num)
theorem B1626485 : Blo 1080619 1626485 := bbase (se 5 (by rfl) ⟨76241, by rfl⟩ : syracuseStep 1626485 = 152483) (by norm_num)
theorem B1626509 : Blo 1080619 1626509 := bbase (se 3 (by rfl) ⟨304970, by rfl⟩ : syracuseStep 1626509 = 609941) (by norm_num)
theorem B2085277 : Blo 1080619 2085277 := bbase (se 3 (by rfl) ⟨390989, by rfl⟩ : syracuseStep 2085277 = 781979) (by norm_num)
theorem B1626533 : Blo 1080619 1626533 := bbase (se 4 (by rfl) ⟨152487, by rfl⟩ : syracuseStep 1626533 = 304975) (by norm_num)
theorem B1626557 : Blo 1080619 1626557 := bbase (se 3 (by rfl) ⟨304979, by rfl⟩ : syracuseStep 1626557 = 609959) (by norm_num)
theorem B2773453 : Blo 1080619 2773453 := bbase (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) (by norm_num)
theorem B1626581 : Blo 1080619 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B1626605 : Blo 1080619 1626605 := bbase (se 3 (by rfl) ⟨304988, by rfl⟩ : syracuseStep 1626605 = 609977) (by norm_num)
theorem B3658229 : Blo 1080619 3658229 := bbase (se 5 (by rfl) ⟨171479, by rfl⟩ : syracuseStep 3658229 = 342959) (by norm_num)
theorem B1626629 : Blo 1080619 1626629 := bbase (se 4 (by rfl) ⟨152496, by rfl⟩ : syracuseStep 1626629 = 304993) (by norm_num)
theorem B4117013 : Blo 1080619 4117013 := bbase (se 6 (by rfl) ⟨96492, by rfl⟩ : syracuseStep 4117013 = 192985) (by norm_num)
theorem B1626653 : Blo 1080619 1626653 := bbase (se 3 (by rfl) ⟨304997, by rfl⟩ : syracuseStep 1626653 = 609995) (by norm_num)
theorem B1626677 : Blo 1080619 1626677 := bbase (se 5 (by rfl) ⟨76250, by rfl⟩ : syracuseStep 1626677 = 152501) (by norm_num)
theorem B1626701 : Blo 1080619 1626701 := bbase (se 3 (by rfl) ⟨305006, by rfl⟩ : syracuseStep 1626701 = 610013) (by norm_num)
theorem B2740837 : Blo 1080619 2740837 := bbase (se 4 (by rfl) ⟨256953, by rfl⟩ : syracuseStep 2740837 = 513907) (by norm_num)
theorem B1626725 : Blo 1080619 1626725 := bbase (se 4 (by rfl) ⟨152505, by rfl⟩ : syracuseStep 1626725 = 305011) (by norm_num)
theorem B1626749 : Blo 1080619 1626749 := bbase (se 3 (by rfl) ⟨305015, by rfl⟩ : syracuseStep 1626749 = 610031) (by norm_num)
theorem B1626773 : Blo 1080619 1626773 := bbase (se 6 (by rfl) ⟨38127, by rfl⟩ : syracuseStep 1626773 = 76255) (by norm_num)
theorem B2052773 : Blo 1080619 2052773 := bbase (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) (by norm_num)
theorem B1626797 : Blo 1080619 1626797 := bbase (se 3 (by rfl) ⟨305024, by rfl⟩ : syracuseStep 1626797 = 610049) (by norm_num)
theorem B1626821 : Blo 1080619 1626821 := bbase (se 4 (by rfl) ⟨152514, by rfl⟩ : syracuseStep 1626821 = 305029) (by norm_num)
theorem B2740949 : Blo 1080619 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B1626845 : Blo 1080619 1626845 := bbase (se 3 (by rfl) ⟨305033, by rfl⟩ : syracuseStep 1626845 = 610067) (by norm_num)
theorem B1626869 : Blo 1080619 1626869 := bbase (se 5 (by rfl) ⟨76259, by rfl⟩ : syracuseStep 1626869 = 152519) (by norm_num)
theorem B1626893 : Blo 1080619 1626893 := bbase (se 3 (by rfl) ⟨305042, by rfl⟩ : syracuseStep 1626893 = 610085) (by norm_num)
theorem B1626917 : Blo 1080619 1626917 := bbase (se 4 (by rfl) ⟨152523, by rfl⟩ : syracuseStep 1626917 = 305047) (by norm_num)
theorem B2085677 : Blo 1080619 2085677 := bbase (se 3 (by rfl) ⟨391064, by rfl⟩ : syracuseStep 2085677 = 782129) (by norm_num)
theorem B4117301 : Blo 1080619 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B1823573 : Blo 1080619 1823573 := bbase (se 9 (by rfl) ⟨5342, by rfl⟩ : syracuseStep 1823573 = 10685) (by norm_num)
theorem B1233749 : Blo 1080619 1233749 := bbase (se 9 (by rfl) ⟨3614, by rfl⟩ : syracuseStep 1233749 = 7229) (by norm_num)
theorem B47469397 : Blo 1080619 47469397 := bbase (se 9 (by rfl) ⟨139070, by rfl⟩ : syracuseStep 47469397 = 278141) (by norm_num)
theorem B2347909 : Blo 1080619 2347909 := bbase (se 4 (by rfl) ⟨220116, by rfl⟩ : syracuseStep 2347909 = 440233) (by norm_num)
theorem B2741141 : Blo 1080619 2741141 := bbase (se 6 (by rfl) ⟨64245, by rfl⟩ : syracuseStep 2741141 = 128491) (by norm_num)
theorem B3658661 : Blo 1080619 3658661 := bbase (se 4 (by rfl) ⟨342999, by rfl⟩ : syracuseStep 3658661 = 685999) (by norm_num)
theorem B1823701 : Blo 1080619 1823701 := bbase (se 7 (by rfl) ⟨21371, by rfl⟩ : syracuseStep 1823701 = 42743) (by norm_num)
theorem B1823789 : Blo 1080619 1823789 := bbase (se 3 (by rfl) ⟨341960, by rfl⟩ : syracuseStep 1823789 = 683921) (by norm_num)
theorem B1823917 : Blo 1080619 1823917 := bbase (se 3 (by rfl) ⟨341984, by rfl⟩ : syracuseStep 1823917 = 683969) (by norm_num)
theorem B1299665 : Blo 1080619 1299665 := bbase (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) (by norm_num)
theorem B2741485 : Blo 1080619 2741485 := bbase (se 3 (by rfl) ⟨514028, by rfl⟩ : syracuseStep 2741485 = 1028057) (by norm_num)
theorem B6935797 : Blo 1080619 6935797 := bbase (se 5 (by rfl) ⟨325115, by rfl⟩ : syracuseStep 6935797 = 650231) (by norm_num)
theorem B1824005 : Blo 1080619 1824005 := bbase (se 4 (by rfl) ⟨171000, by rfl⟩ : syracuseStep 1824005 = 342001) (by norm_num)
theorem B3659093 : Blo 1080619 3659093 := bbase (se 15 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3659093 = 335) (by norm_num)
theorem B2741597 : Blo 1080619 2741597 := bbase (se 3 (by rfl) ⟨514049, by rfl⟩ : syracuseStep 2741597 = 1028099) (by norm_num)
theorem B3462517 : Blo 1080619 3462517 := bbase (se 5 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 3462517 = 324611) (by norm_num)
theorem B1824133 : Blo 1080619 1824133 := bbase (se 4 (by rfl) ⟨171012, by rfl⟩ : syracuseStep 1824133 = 342025) (by norm_num)
theorem B2053525 : Blo 1080619 2053525 := bbase (se 6 (by rfl) ⟨48129, by rfl⟩ : syracuseStep 2053525 = 96259) (by norm_num)
theorem B1824221 : Blo 1080619 1824221 := bbase (se 3 (by rfl) ⟨342041, by rfl⟩ : syracuseStep 1824221 = 684083) (by norm_num)
theorem B1299997 : Blo 1080619 1299997 := bbase (se 3 (by rfl) ⟨243749, by rfl⟩ : syracuseStep 1299997 = 487499) (by norm_num)
theorem B2741789 : Blo 1080619 2741789 := bbase (se 3 (by rfl) ⟨514085, by rfl⟩ : syracuseStep 2741789 = 1028171) (by norm_num)
theorem B2053669 : Blo 1080619 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B1824349 : Blo 1080619 1824349 := bbase (se 3 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 1824349 = 684131) (by norm_num)
theorem B1824437 : Blo 1080619 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B2315965 : Blo 1080619 2315965 := bbase (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) (by norm_num)
theorem B2053829 : Blo 1080619 2053829 := bbase (se 4 (by rfl) ⟨192546, by rfl⟩ : syracuseStep 2053829 = 385093) (by norm_num)
theorem B3659525 : Blo 1080619 3659525 := bbase (se 4 (by rfl) ⟨343080, by rfl⟩ : syracuseStep 3659525 = 686161) (by norm_num)
theorem B1824565 : Blo 1080619 1824565 := bbase (se 5 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 1824565 = 171053) (by norm_num)
theorem B2053973 : Blo 1080619 2053973 := bbase (se 9 (by rfl) ⟨6017, by rfl⟩ : syracuseStep 2053973 = 12035) (by norm_num)
theorem B4446053 : Blo 1080619 4446053 := bbase (se 4 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 4446053 = 833635) (by norm_num)
theorem B2742133 : Blo 1080619 2742133 := bbase (se 5 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 2742133 = 257075) (by norm_num)
theorem B1824653 : Blo 1080619 1824653 := bbase (se 3 (by rfl) ⟨342122, by rfl⟩ : syracuseStep 1824653 = 684245) (by norm_num)
theorem B2742245 : Blo 1080619 2742245 := bbase (se 4 (by rfl) ⟨257085, by rfl⟩ : syracuseStep 2742245 = 514171) (by norm_num)
theorem B5560325 : Blo 1080619 5560325 := bbase (se 4 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 5560325 = 1042561) (by norm_num)
theorem B1824781 : Blo 1080619 1824781 := bbase (se 3 (by rfl) ⟨342146, by rfl⟩ : syracuseStep 1824781 = 684293) (by norm_num)
theorem B1824869 : Blo 1080619 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B1267813 : Blo 1080619 1267813 := bbase (se 4 (by rfl) ⟨118857, by rfl⟩ : syracuseStep 1267813 = 237715) (by norm_num)
theorem B2054261 : Blo 1080619 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B2742437 : Blo 1080619 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B3659957 : Blo 1080619 3659957 := bbase (se 5 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 3659957 = 343121) (by norm_num)
theorem B1235153 : Blo 1080619 1235153 := bbase (se 2 (by rfl) ⟨463182, by rfl⟩ : syracuseStep 1235153 = 926365) (by norm_num)
theorem B1300693 : Blo 1080619 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B1824997 : Blo 1080619 1824997 := bbase (se 4 (by rfl) ⟨171093, by rfl⟩ : syracuseStep 1824997 = 342187) (by norm_num)
theorem B1300741 : Blo 1080619 1300741 := bbase (se 4 (by rfl) ⟨121944, by rfl⟩ : syracuseStep 1300741 = 243889) (by norm_num)
theorem B2054413 : Blo 1080619 2054413 := bbase (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) (by norm_num)
theorem B1825085 : Blo 1080619 1825085 := bbase (se 3 (by rfl) ⟨342203, by rfl⟩ : syracuseStep 1825085 = 684407) (by norm_num)
theorem B1562941 : Blo 1080619 1562941 := bbase (se 3 (by rfl) ⟨293051, by rfl⟩ : syracuseStep 1562941 = 586103) (by norm_num)
theorem B5626181 : Blo 1080619 5626181 := bbase (se 4 (by rfl) ⟨527454, by rfl⟩ : syracuseStep 5626181 = 1054909) (by norm_num)
theorem B8346037 : Blo 1080619 8346037 := bbase (se 5 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 8346037 = 782441) (by norm_num)
theorem B1825213 : Blo 1080619 1825213 := bbase (se 3 (by rfl) ⟨342227, by rfl⟩ : syracuseStep 1825213 = 684455) (by norm_num)
theorem B2742781 : Blo 1080619 2742781 := bbase (se 3 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 2742781 = 1028543) (by norm_num)
theorem B3463685 : Blo 1080619 3463685 := bbase (se 4 (by rfl) ⟨324720, by rfl⟩ : syracuseStep 3463685 = 649441) (by norm_num)
theorem B1825301 : Blo 1080619 1825301 := bbase (se 6 (by rfl) ⟨42780, by rfl⟩ : syracuseStep 1825301 = 85561) (by norm_num)
theorem B2054717 : Blo 1080619 2054717 := bbase (se 3 (by rfl) ⟨385259, by rfl⟩ : syracuseStep 2054717 = 770519) (by norm_num)
theorem B3660389 : Blo 1080619 3660389 := bbase (se 4 (by rfl) ⟨343161, by rfl⟩ : syracuseStep 3660389 = 686323) (by norm_num)
theorem B2742893 : Blo 1080619 2742893 := bbase (se 3 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 2742893 = 1028585) (by norm_num)
theorem B1825429 : Blo 1080619 1825429 := bbase (se 6 (by rfl) ⟨42783, by rfl⟩ : syracuseStep 1825429 = 85567) (by norm_num)
theorem B1825517 : Blo 1080619 1825517 := bbase (se 3 (by rfl) ⟨342284, by rfl⟩ : syracuseStep 1825517 = 684569) (by norm_num)
theorem B2743085 : Blo 1080619 2743085 := bbase (se 3 (by rfl) ⟨514328, by rfl⟩ : syracuseStep 2743085 = 1028657) (by norm_num)
theorem B5561189 : Blo 1080619 5561189 := bbase (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) (by norm_num)
theorem B1825645 : Blo 1080619 1825645 := bbase (se 3 (by rfl) ⟨342308, by rfl⟩ : syracuseStep 1825645 = 684617) (by norm_num)
theorem B1465237 : Blo 1080619 1465237 := bbase (se 6 (by rfl) ⟨34341, by rfl⟩ : syracuseStep 1465237 = 68683) (by norm_num)
theorem B1825733 : Blo 1080619 1825733 := bbase (se 4 (by rfl) ⟨171162, by rfl⟩ : syracuseStep 1825733 = 342325) (by norm_num)
theorem B1825861 : Blo 1080619 1825861 := bbase (se 4 (by rfl) ⟨171174, by rfl⟩ : syracuseStep 1825861 = 342349) (by norm_num)
theorem B2743429 : Blo 1080619 2743429 := bbase (se 4 (by rfl) ⟨257196, by rfl⟩ : syracuseStep 2743429 = 514393) (by norm_num)
theorem B1825949 : Blo 1080619 1825949 := bbase (se 3 (by rfl) ⟨342365, by rfl⟩ : syracuseStep 1825949 = 684731) (by norm_num)
theorem B2743541 : Blo 1080619 2743541 := bbase (se 5 (by rfl) ⟨128603, by rfl⟩ : syracuseStep 2743541 = 257207) (by norm_num)
theorem B8215829 : Blo 1080619 8215829 := bbase (se 6 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 8215829 = 385117) (by norm_num)
theorem B1826077 : Blo 1080619 1826077 := bbase (se 3 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 1826077 = 684779) (by norm_num)
theorem B1301789 : Blo 1080619 1301789 := bbase (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) (by norm_num)
theorem B2055469 : Blo 1080619 2055469 := bbase (se 3 (by rfl) ⟨385400, by rfl⟩ : syracuseStep 2055469 = 770801) (by norm_num)
theorem B1826165 : Blo 1080619 1826165 := bbase (se 5 (by rfl) ⟨85601, by rfl⟩ : syracuseStep 1826165 = 171203) (by norm_num)
theorem B1236353 : Blo 1080619 1236353 := bbase (se 2 (by rfl) ⟨463632, by rfl⟩ : syracuseStep 1236353 = 927265) (by norm_num)
theorem B2743733 : Blo 1080619 2743733 := bbase (se 5 (by rfl) ⟨128612, by rfl⟩ : syracuseStep 2743733 = 257225) (by norm_num)
theorem B2055613 : Blo 1080619 2055613 := bbase (se 3 (by rfl) ⟨385427, by rfl⟩ : syracuseStep 2055613 = 770855) (by norm_num)
theorem B1826293 : Blo 1080619 1826293 := bbase (se 5 (by rfl) ⟨85607, by rfl⟩ : syracuseStep 1826293 = 171215) (by norm_num)
theorem B1826381 : Blo 1080619 1826381 := bbase (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) (by norm_num)
theorem B1302097 : Blo 1080619 1302097 := bbase (se 2 (by rfl) ⟨488286, by rfl⟩ : syracuseStep 1302097 = 976573) (by norm_num)
theorem B2055773 : Blo 1080619 2055773 := bbase (se 3 (by rfl) ⟨385457, by rfl⟩ : syracuseStep 2055773 = 770915) (by norm_num)
theorem B1236613 : Blo 1080619 1236613 := bbase (se 4 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 1236613 = 231865) (by norm_num)
theorem B1367705 : Blo 1080619 1367705 := bbase (se 2 (by rfl) ⟨512889, by rfl⟩ : syracuseStep 1367705 = 1025779) (by norm_num)
theorem B1826509 : Blo 1080619 1826509 := bbase (se 3 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 1826509 = 684941) (by norm_num)
theorem B1367761 : Blo 1080619 1367761 := bbase (se 2 (by rfl) ⟨512910, by rfl⟩ : syracuseStep 1367761 = 1025821) (by norm_num)
theorem B2055917 : Blo 1080619 2055917 := bbase (se 3 (by rfl) ⟨385484, by rfl⟩ : syracuseStep 2055917 = 770969) (by norm_num)
theorem B1302265 : Blo 1080619 1302265 := bbase (se 2 (by rfl) ⟨488349, by rfl⟩ : syracuseStep 1302265 = 976699) (by norm_num)
theorem B2744077 : Blo 1080619 2744077 := bbase (se 3 (by rfl) ⟨514514, by rfl⟩ : syracuseStep 2744077 = 1029029) (by norm_num)
theorem B1826597 : Blo 1080619 1826597 := bbase (se 4 (by rfl) ⟨171243, by rfl⟩ : syracuseStep 1826597 = 342487) (by norm_num)
theorem B1367857 : Blo 1080619 1367857 := bbase (se 2 (by rfl) ⟨512946, by rfl⟩ : syracuseStep 1367857 = 1025893) (by norm_num)
theorem B2744189 : Blo 1080619 2744189 := bbase (se 3 (by rfl) ⟨514535, by rfl⟩ : syracuseStep 2744189 = 1029071) (by norm_num)
theorem B1826725 : Blo 1080619 1826725 := bbase (se 4 (by rfl) ⟨171255, by rfl⟩ : syracuseStep 1826725 = 342511) (by norm_num)
theorem B1302461 : Blo 1080619 1302461 := bbase (se 3 (by rfl) ⟨244211, by rfl⟩ : syracuseStep 1302461 = 488423) (by norm_num)
theorem B1368029 : Blo 1080619 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B1826813 : Blo 1080619 1826813 := bbase (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) (by norm_num)
theorem B2056205 : Blo 1080619 2056205 := bbase (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) (by norm_num)
theorem B1368085 : Blo 1080619 1368085 := bbase (se 6 (by rfl) ⟨32064, by rfl⟩ : syracuseStep 1368085 = 64129) (by norm_num)
theorem B2744381 : Blo 1080619 2744381 := bbase (se 3 (by rfl) ⟨514571, by rfl⟩ : syracuseStep 2744381 = 1029143) (by norm_num)
theorem B1368181 : Blo 1080619 1368181 := bbase (se 5 (by rfl) ⟨64133, by rfl⟩ : syracuseStep 1368181 = 128267) (by norm_num)
theorem B1826941 : Blo 1080619 1826941 := bbase (se 3 (by rfl) ⟨342551, by rfl⟩ : syracuseStep 1826941 = 685103) (by norm_num)
theorem B2056357 : Blo 1080619 2056357 := bbase (se 4 (by rfl) ⟨192783, by rfl⟩ : syracuseStep 2056357 = 385567) (by norm_num)
theorem B1827029 : Blo 1080619 1827029 := bbase (se 7 (by rfl) ⟨21410, by rfl⟩ : syracuseStep 1827029 = 42821) (by norm_num)
theorem B1368353 : Blo 1080619 1368353 := bbase (se 2 (by rfl) ⟨513132, by rfl⟩ : syracuseStep 1368353 = 1026265) (by norm_num)
theorem B3465541 : Blo 1080619 3465541 := bbase (se 4 (by rfl) ⟨324894, by rfl⟩ : syracuseStep 3465541 = 649789) (by norm_num)
theorem B1827157 : Blo 1080619 1827157 := bbase (se 10 (by rfl) ⟨2676, by rfl⟩ : syracuseStep 1827157 = 5353) (by norm_num)
theorem B1368409 : Blo 1080619 1368409 := bbase (se 2 (by rfl) ⟨513153, by rfl⟩ : syracuseStep 1368409 = 1026307) (by norm_num)
theorem B2744725 : Blo 1080619 2744725 := bbase (se 6 (by rfl) ⟨64329, by rfl⟩ : syracuseStep 2744725 = 128659) (by norm_num)
theorem B1827245 : Blo 1080619 1827245 := bbase (se 3 (by rfl) ⟨342608, by rfl⟩ : syracuseStep 1827245 = 685217) (by norm_num)
theorem B1368505 : Blo 1080619 1368505 := bbase (se 2 (by rfl) ⟨513189, by rfl⟩ : syracuseStep 1368505 = 1026379) (by norm_num)
theorem B2056661 : Blo 1080619 2056661 := bbase (se 7 (by rfl) ⟨24101, by rfl⟩ : syracuseStep 2056661 = 48203) (by norm_num)
theorem B2744837 : Blo 1080619 2744837 := bbase (se 4 (by rfl) ⟨257328, by rfl⟩ : syracuseStep 2744837 = 514657) (by norm_num)
theorem B1827373 : Blo 1080619 1827373 := bbase (se 3 (by rfl) ⟨342632, by rfl⟩ : syracuseStep 1827373 = 685265) (by norm_num)
theorem B1368677 : Blo 1080619 1368677 := bbase (se 4 (by rfl) ⟨128313, by rfl⟩ : syracuseStep 1368677 = 256627) (by norm_num)
theorem B1827461 : Blo 1080619 1827461 := bbase (se 4 (by rfl) ⟨171324, by rfl⟩ : syracuseStep 1827461 = 342649) (by norm_num)
theorem B1368733 : Blo 1080619 1368733 := bbase (se 3 (by rfl) ⟨256637, by rfl⟩ : syracuseStep 1368733 = 513275) (by norm_num)
theorem B2745029 : Blo 1080619 2745029 := bbase (se 4 (by rfl) ⟨257346, by rfl⟩ : syracuseStep 2745029 = 514693) (by norm_num)
theorem B1368829 : Blo 1080619 1368829 := bbase (se 3 (by rfl) ⟨256655, by rfl⟩ : syracuseStep 1368829 = 513311) (by norm_num)
theorem B1827589 : Blo 1080619 1827589 := bbase (se 4 (by rfl) ⟨171336, by rfl⟩ : syracuseStep 1827589 = 342673) (by norm_num)
theorem B1827677 : Blo 1080619 1827677 := bbase (se 3 (by rfl) ⟨342689, by rfl⟩ : syracuseStep 1827677 = 685379) (by norm_num)
theorem B1369001 : Blo 1080619 1369001 := bbase (se 2 (by rfl) ⟨513375, by rfl⟩ : syracuseStep 1369001 = 1026751) (by norm_num)
theorem B4940741 : Blo 1080619 4940741 := bbase (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) (by norm_num)
theorem B1827805 : Blo 1080619 1827805 := bbase (se 3 (by rfl) ⟨342713, by rfl⟩ : syracuseStep 1827805 = 685427) (by norm_num)
theorem B1369057 : Blo 1080619 1369057 := bbase (se 2 (by rfl) ⟨513396, by rfl⟩ : syracuseStep 1369057 = 1026793) (by norm_num)
theorem B2745373 : Blo 1080619 2745373 := bbase (se 3 (by rfl) ⟨514757, by rfl⟩ : syracuseStep 2745373 = 1029515) (by norm_num)
theorem B1827893 : Blo 1080619 1827893 := bbase (se 5 (by rfl) ⟨85682, by rfl⟩ : syracuseStep 1827893 = 171365) (by norm_num)
theorem B1369153 : Blo 1080619 1369153 := bbase (se 2 (by rfl) ⟨513432, by rfl⟩ : syracuseStep 1369153 = 1026865) (by norm_num)
theorem B1828021 : Blo 1080619 1828021 := bbase (se 5 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 1828021 = 171377) (by norm_num)
theorem B2057413 : Blo 1080619 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B1369325 : Blo 1080619 1369325 := bbase (se 3 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 1369325 = 513497) (by norm_num)
theorem B1828109 : Blo 1080619 1828109 := bbase (se 3 (by rfl) ⟨342770, by rfl⟩ : syracuseStep 1828109 = 685541) (by norm_num)
theorem B1369381 : Blo 1080619 1369381 := bbase (se 4 (by rfl) ⟨128379, by rfl⟩ : syracuseStep 1369381 = 256759) (by norm_num)
theorem B2057557 : Blo 1080619 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B1369477 : Blo 1080619 1369477 := bbase (se 4 (by rfl) ⟨128388, by rfl⟩ : syracuseStep 1369477 = 256777) (by norm_num)
theorem B1828237 : Blo 1080619 1828237 := bbase (se 3 (by rfl) ⟨342794, by rfl⟩ : syracuseStep 1828237 = 685589) (by norm_num)
theorem B1828325 : Blo 1080619 1828325 := bbase (se 4 (by rfl) ⟨171405, by rfl⟩ : syracuseStep 1828325 = 342811) (by norm_num)
theorem B2057717 : Blo 1080619 2057717 := bbase (se 5 (by rfl) ⟨96455, by rfl⟩ : syracuseStep 2057717 = 192911) (by norm_num)
theorem B1369649 : Blo 1080619 1369649 := bbase (se 2 (by rfl) ⟨513618, by rfl⟩ : syracuseStep 1369649 = 1027237) (by norm_num)
theorem B5203541 : Blo 1080619 5203541 := bbase (se 8 (by rfl) ⟨30489, by rfl⟩ : syracuseStep 5203541 = 60979) (by norm_num)
theorem B1828453 : Blo 1080619 1828453 := bbase (se 4 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 1828453 = 342835) (by norm_num)
theorem B1369705 : Blo 1080619 1369705 := bbase (se 2 (by rfl) ⟨513639, by rfl⟩ : syracuseStep 1369705 = 1027279) (by norm_num)
theorem B2057861 : Blo 1080619 2057861 := bbase (se 4 (by rfl) ⟨192924, by rfl⟩ : syracuseStep 2057861 = 385849) (by norm_num)
theorem B3466901 : Blo 1080619 3466901 := bbase (se 6 (by rfl) ⟨81255, by rfl⟩ : syracuseStep 3466901 = 162511) (by norm_num)
theorem B4679333 : Blo 1080619 4679333 := bbase (se 4 (by rfl) ⟨438687, by rfl⟩ : syracuseStep 4679333 = 877375) (by norm_num)
theorem B1828541 : Blo 1080619 1828541 := bbase (se 3 (by rfl) ⟨342851, by rfl⟩ : syracuseStep 1828541 = 685703) (by norm_num)
theorem B1369801 : Blo 1080619 1369801 := bbase (se 2 (by rfl) ⟨513675, by rfl⟩ : syracuseStep 1369801 = 1027351) (by norm_num)
theorem B17589973 : Blo 1080619 17589973 := bbase (se 7 (by rfl) ⟨206132, by rfl⟩ : syracuseStep 17589973 = 412265) (by norm_num)
theorem B1828669 : Blo 1080619 1828669 := bbase (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) (by norm_num)
theorem B1369973 : Blo 1080619 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B1828757 : Blo 1080619 1828757 := bbase (se 6 (by rfl) ⟨42861, by rfl⟩ : syracuseStep 1828757 = 85723) (by norm_num)
theorem B2058149 : Blo 1080619 2058149 := bbase (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) (by norm_num)
theorem B1370029 : Blo 1080619 1370029 := bbase (se 3 (by rfl) ⟨256880, by rfl⟩ : syracuseStep 1370029 = 513761) (by norm_num)
theorem B1370125 : Blo 1080619 1370125 := bbase (se 3 (by rfl) ⟨256898, by rfl⟩ : syracuseStep 1370125 = 513797) (by norm_num)
theorem B1828885 : Blo 1080619 1828885 := bbase (se 6 (by rfl) ⟨42864, by rfl⟩ : syracuseStep 1828885 = 85729) (by norm_num)
theorem B2058301 : Blo 1080619 2058301 := bbase (se 3 (by rfl) ⟨385931, by rfl⟩ : syracuseStep 2058301 = 771863) (by norm_num)
theorem B1828973 : Blo 1080619 1828973 := bbase (se 3 (by rfl) ⟨342932, by rfl⟩ : syracuseStep 1828973 = 685865) (by norm_num)
theorem B1370297 : Blo 1080619 1370297 := bbase (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) (by norm_num)
theorem B26699989 : Blo 1080619 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B1829101 : Blo 1080619 1829101 := bbase (se 3 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 1829101 = 685913) (by norm_num)
theorem B1370353 : Blo 1080619 1370353 := bbase (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) (by norm_num)
theorem B1829189 : Blo 1080619 1829189 := bbase (se 4 (by rfl) ⟨171486, by rfl⟩ : syracuseStep 1829189 = 342973) (by norm_num)
theorem B1370449 : Blo 1080619 1370449 := bbase (se 2 (by rfl) ⟨513918, by rfl⟩ : syracuseStep 1370449 = 1027837) (by norm_num)
theorem B2058605 : Blo 1080619 2058605 := bbase (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) (by norm_num)
theorem B1829317 : Blo 1080619 1829317 := bbase (se 4 (by rfl) ⟨171498, by rfl⟩ : syracuseStep 1829317 = 342997) (by norm_num)
theorem B1370621 : Blo 1080619 1370621 := bbase (se 3 (by rfl) ⟨256991, by rfl⟩ : syracuseStep 1370621 = 513983) (by norm_num)
theorem B1829405 : Blo 1080619 1829405 := bbase (se 3 (by rfl) ⟨343013, by rfl⟩ : syracuseStep 1829405 = 686027) (by norm_num)
theorem B1731125 : Blo 1080619 1731125 := bbase (se 5 (by rfl) ⟨81146, by rfl⟩ : syracuseStep 1731125 = 162293) (by norm_num)
theorem B1370677 : Blo 1080619 1370677 := bbase (se 5 (by rfl) ⟨64250, by rfl⟩ : syracuseStep 1370677 = 128501) (by norm_num)
theorem B1370773 : Blo 1080619 1370773 := bbase (se 6 (by rfl) ⟨32127, by rfl⟩ : syracuseStep 1370773 = 64255) (by norm_num)
theorem B1829533 : Blo 1080619 1829533 := bbase (se 3 (by rfl) ⟨343037, by rfl⟩ : syracuseStep 1829533 = 686075) (by norm_num)
theorem B1829621 : Blo 1080619 1829621 := bbase (se 5 (by rfl) ⟨85763, by rfl⟩ : syracuseStep 1829621 = 171527) (by norm_num)
theorem B1370945 : Blo 1080619 1370945 := bbase (se 2 (by rfl) ⟨514104, by rfl⟩ : syracuseStep 1370945 = 1028209) (by norm_num)
theorem B1829749 : Blo 1080619 1829749 := bbase (se 5 (by rfl) ⟨85769, by rfl⟩ : syracuseStep 1829749 = 171539) (by norm_num)
theorem B1371001 : Blo 1080619 1371001 := bbase (se 2 (by rfl) ⟨514125, by rfl⟩ : syracuseStep 1371001 = 1028251) (by norm_num)
theorem B1829837 : Blo 1080619 1829837 := bbase (se 3 (by rfl) ⟨343094, by rfl⟩ : syracuseStep 1829837 = 686189) (by norm_num)
theorem B1371097 : Blo 1080619 1371097 := bbase (se 2 (by rfl) ⟨514161, by rfl⟩ : syracuseStep 1371097 = 1028323) (by norm_num)
theorem B1829965 : Blo 1080619 1829965 := bbase (se 3 (by rfl) ⟨343118, by rfl⟩ : syracuseStep 1829965 = 686237) (by norm_num)
theorem B1371269 : Blo 1080619 1371269 := bbase (se 4 (by rfl) ⟨128556, by rfl⟩ : syracuseStep 1371269 = 257113) (by norm_num)
theorem B1830053 : Blo 1080619 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B1371325 : Blo 1080619 1371325 := bbase (se 3 (by rfl) ⟨257123, by rfl⟩ : syracuseStep 1371325 = 514247) (by norm_num)
theorem B1731797 : Blo 1080619 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B1338637 : Blo 1080619 1338637 := bbase (se 3 (by rfl) ⟨250994, by rfl⟩ : syracuseStep 1338637 = 501989) (by norm_num)
theorem B1371421 : Blo 1080619 1371421 := bbase (se 3 (by rfl) ⟨257141, by rfl⟩ : syracuseStep 1371421 = 514283) (by norm_num)
theorem B1830181 : Blo 1080619 1830181 := bbase (se 4 (by rfl) ⟨171579, by rfl⟩ : syracuseStep 1830181 = 343159) (by norm_num)
theorem B1830269 : Blo 1080619 1830269 := bbase (se 3 (by rfl) ⟨343175, by rfl⟩ : syracuseStep 1830269 = 686351) (by norm_num)
theorem B1371593 : Blo 1080619 1371593 := bbase (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) (by norm_num)
theorem B5336549 : Blo 1080619 5336549 := bbase (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) (by norm_num)
theorem B1371649 : Blo 1080619 1371649 := bbase (se 2 (by rfl) ⟨514368, by rfl⟩ : syracuseStep 1371649 = 1028737) (by norm_num)
theorem B1371745 : Blo 1080619 1371745 := bbase (se 2 (by rfl) ⟨514404, by rfl⟩ : syracuseStep 1371745 = 1028809) (by norm_num)
theorem B1732309 : Blo 1080619 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B1371917 : Blo 1080619 1371917 := bbase (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) (by norm_num)
theorem B4615973 : Blo 1080619 4615973 := bbase (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) (by norm_num)
theorem B1371973 : Blo 1080619 1371973 := bbase (se 4 (by rfl) ⟨128622, by rfl⟩ : syracuseStep 1371973 = 257245) (by norm_num)
theorem B9891733 : Blo 1080619 9891733 := bbase (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) (by norm_num)
theorem B1372069 : Blo 1080619 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B1372241 : Blo 1080619 1372241 := bbase (se 2 (by rfl) ⟨514590, by rfl⟩ : syracuseStep 1372241 = 1029181) (by norm_num)
theorem B1372297 : Blo 1080619 1372297 := bbase (se 2 (by rfl) ⟨514611, by rfl⟩ : syracuseStep 1372297 = 1029223) (by norm_num)
theorem B1732765 : Blo 1080619 1732765 := bbase (se 3 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 1732765 = 649787) (by norm_num)
theorem B1372393 : Blo 1080619 1372393 := bbase (se 2 (by rfl) ⟨514647, by rfl⟩ : syracuseStep 1372393 = 1029295) (by norm_num)
theorem B1372565 : Blo 1080619 1372565 := bbase (se 6 (by rfl) ⟨32169, by rfl⟩ : syracuseStep 1372565 = 64339) (by norm_num)
theorem B6943157 : Blo 1080619 6943157 := bbase (se 5 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 6943157 = 650921) (by norm_num)
theorem B1372621 : Blo 1080619 1372621 := bbase (se 3 (by rfl) ⟨257366, by rfl⟩ : syracuseStep 1372621 = 514733) (by norm_num)
theorem B4682245 : Blo 1080619 4682245 := bbase (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) (by norm_num)
theorem B1372717 : Blo 1080619 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B5206693 : Blo 1080619 5206693 := bbase (se 4 (by rfl) ⟨488127, by rfl⟩ : syracuseStep 5206693 = 976255) (by norm_num)
theorem B1733437 : Blo 1080619 1733437 := bbase (se 3 (by rfl) ⟨325019, by rfl⟩ : syracuseStep 1733437 = 650039) (by norm_num)
theorem B2192293 : Blo 1080619 2192293 := bbase (se 4 (by rfl) ⟨205527, by rfl⟩ : syracuseStep 2192293 = 411055) (by norm_num)
theorem B3470309 : Blo 1080619 3470309 := bbase (se 4 (by rfl) ⟨325341, by rfl⟩ : syracuseStep 3470309 = 650683) (by norm_num)
theorem B3699877 : Blo 1080619 3699877 := bbase (se 4 (by rfl) ⟨346863, by rfl⟩ : syracuseStep 3699877 = 693727) (by norm_num)
theorem B5862613 : Blo 1080619 5862613 := bbase (se 7 (by rfl) ⟨68702, by rfl⟩ : syracuseStep 5862613 = 137405) (by norm_num)
theorem B1733861 : Blo 1080619 1733861 := bbase (se 4 (by rfl) ⟨162549, by rfl⟩ : syracuseStep 1733861 = 325099) (by norm_num)
theorem B17528213 : Blo 1080619 17528213 := bbase (se 6 (by rfl) ⟨410817, by rfl⟩ : syracuseStep 17528213 = 821635) (by norm_num)
theorem B2192861 : Blo 1080619 2192861 := bbase (se 3 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 2192861 = 822323) (by norm_num)
theorem B1734149 : Blo 1080619 1734149 := bbase (se 4 (by rfl) ⟨162576, by rfl⟩ : syracuseStep 1734149 = 325153) (by norm_num)
theorem B4617749 : Blo 1080619 4617749 := bbase (se 6 (by rfl) ⟨108228, by rfl⟩ : syracuseStep 4617749 = 216457) (by norm_num)
theorem B1111825 : Blo 1080619 1111825 := bbase (se 2 (by rfl) ⟨416934, by rfl⟩ : syracuseStep 1111825 = 833869) (by norm_num)
theorem B3700565 : Blo 1080619 3700565 := bbase (se 9 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 3700565 = 21683) (by norm_num)
theorem B3078101 : Blo 1080619 3078101 := bbase (se 7 (by rfl) ⟨36071, by rfl⟩ : syracuseStep 3078101 = 72143) (by norm_num)
theorem B2193421 : Blo 1080619 2193421 := bbase (se 3 (by rfl) ⟨411266, by rfl⟩ : syracuseStep 2193421 = 822533) (by norm_num)
theorem B4388917 : Blo 1080619 4388917 := bbase (se 5 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 4388917 = 411461) (by norm_num)
theorem B3471589 : Blo 1080619 3471589 := bbase (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) (by norm_num)
theorem B1734949 : Blo 1080619 1734949 := bbase (se 4 (by rfl) ⟨162651, by rfl⟩ : syracuseStep 1734949 = 325303) (by norm_num)
theorem B7043573 : Blo 1080619 7043573 := bbase (se 5 (by rfl) ⟨330167, by rfl⟩ : syracuseStep 7043573 = 660335) (by norm_num)
theorem B2193941 : Blo 1080619 2193941 := bbase (se 6 (by rfl) ⟨51420, by rfl⟩ : syracuseStep 2193941 = 102841) (by norm_num)
theorem B3078773 : Blo 1080619 3078773 := bbase (se 5 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 3078773 = 288635) (by norm_num)
theorem B5470901 : Blo 1080619 5470901 := bbase (se 5 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 5470901 = 512897) (by norm_num)
theorem B19725077 : Blo 1080619 19725077 := bbase (se 6 (by rfl) ⟨462306, by rfl⟩ : syracuseStep 19725077 = 924613) (by norm_num)
theorem B1538885 : Blo 1080619 1538885 := bbase (se 4 (by rfl) ⟨144270, by rfl⟩ : syracuseStep 1538885 = 288541) (by norm_num)
theorem B1735501 : Blo 1080619 1735501 := bbase (se 3 (by rfl) ⟨325406, by rfl⟩ : syracuseStep 1735501 = 650813) (by norm_num)
theorem B8223605 : Blo 1080619 8223605 := bbase (se 5 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 8223605 = 770963) (by norm_num)
theorem B18480149 : Blo 1080619 18480149 := bbase (se 6 (by rfl) ⟨433128, by rfl⟩ : syracuseStep 18480149 = 866257) (by norm_num)
theorem B3079205 : Blo 1080619 3079205 := bbase (se 4 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 3079205 = 577351) (by norm_num)
theorem B1735757 : Blo 1080619 1735757 := bbase (se 3 (by rfl) ⟨325454, by rfl⟩ : syracuseStep 1735757 = 650909) (by norm_num)
theorem B2194589 : Blo 1080619 2194589 := bbase (se 3 (by rfl) ⟨411485, by rfl⟩ : syracuseStep 2194589 = 822971) (by norm_num)
theorem B2194757 : Blo 1080619 2194757 := bbase (se 4 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 2194757 = 411517) (by norm_num)
theorem B3472949 : Blo 1080619 3472949 := bbase (se 5 (by rfl) ⟨162794, by rfl⟩ : syracuseStep 3472949 = 325589) (by norm_num)
theorem B6946357 : Blo 1080619 6946357 := bbase (se 5 (by rfl) ⟨325610, by rfl⟩ : syracuseStep 6946357 = 651221) (by norm_num)
theorem B3473077 : Blo 1080619 3473077 := bbase (se 5 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 3473077 = 325601) (by norm_num)
theorem B5209829 : Blo 1080619 5209829 := bbase (se 4 (by rfl) ⟨488421, by rfl⟩ : syracuseStep 5209829 = 976843) (by norm_num)
theorem B1736461 : Blo 1080619 1736461 := bbase (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) (by norm_num)
theorem B3079957 : Blo 1080619 3079957 := bbase (se 6 (by rfl) ⟨72186, by rfl⟩ : syracuseStep 3079957 = 144373) (by norm_num)
theorem B2817845 : Blo 1080619 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B3702613 : Blo 1080619 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B2195309 : Blo 1080619 2195309 := bbase (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) (by norm_num)
theorem B1114021 : Blo 1080619 1114021 := bbase (se 4 (by rfl) ⟨104439, by rfl⟩ : syracuseStep 1114021 = 208879) (by norm_num)
theorem B3473333 : Blo 1080619 3473333 := bbase (se 5 (by rfl) ⟨162812, by rfl⟩ : syracuseStep 3473333 = 325625) (by norm_num)
theorem B5472197 : Blo 1080619 5472197 := bbase (se 4 (by rfl) ⟨513018, by rfl⟩ : syracuseStep 5472197 = 1026037) (by norm_num)
theorem B3702725 : Blo 1080619 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B1081347 : Blo 1080619 1081347 := bstep (se 1 (by rfl) ⟨811010, by rfl⟩ : syracuseStep 1081347 = 1622021) B1622021
theorem B1081363 : Blo 1080619 1081363 := bstep (se 1 (by rfl) ⟨811022, by rfl⟩ : syracuseStep 1081363 = 1622045) B1622045
theorem B1081379 : Blo 1080619 1081379 := bstep (se 1 (by rfl) ⟨811034, by rfl⟩ : syracuseStep 1081379 = 1622069) B1622069
theorem B1081395 : Blo 1080619 1081395 := bstep (se 1 (by rfl) ⟨811046, by rfl⟩ : syracuseStep 1081395 = 1622093) B1622093
theorem B1081411 : Blo 1080619 1081411 := bstep (se 1 (by rfl) ⟨811058, by rfl⟩ : syracuseStep 1081411 = 1622117) B1622117
theorem B1081427 : Blo 1080619 1081427 := bstep (se 1 (by rfl) ⟨811070, by rfl⟩ : syracuseStep 1081427 = 1622141) B1622141
theorem B1081443 : Blo 1080619 1081443 := bstep (se 1 (by rfl) ⟨811082, by rfl⟩ : syracuseStep 1081443 = 1622165) B1622165
theorem B1081459 : Blo 1080619 1081459 := bstep (se 1 (by rfl) ⟨811094, by rfl⟩ : syracuseStep 1081459 = 1622189) B1622189
theorem B1081475 : Blo 1080619 1081475 := bstep (se 1 (by rfl) ⟨811106, by rfl⟩ : syracuseStep 1081475 = 1622213) B1622213
theorem B1081491 : Blo 1080619 1081491 := bstep (se 1 (by rfl) ⟨811118, by rfl⟩ : syracuseStep 1081491 = 1622237) B1622237
theorem B1081507 : Blo 1080619 1081507 := bstep (se 1 (by rfl) ⟨811130, by rfl⟩ : syracuseStep 1081507 = 1622261) B1622261
theorem B2195633 : Blo 1080619 2195633 := bstep (se 2 (by rfl) ⟨823362, by rfl⟩ : syracuseStep 2195633 = 1646725) B1646725
theorem B1081523 : Blo 1080619 1081523 := bstep (se 1 (by rfl) ⟨811142, by rfl⟩ : syracuseStep 1081523 = 1622285) B1622285
theorem B1081539 : Blo 1080619 1081539 := bstep (se 1 (by rfl) ⟨811154, by rfl⟩ : syracuseStep 1081539 = 1622309) B1622309
theorem B1081555 : Blo 1080619 1081555 := bstep (se 1 (by rfl) ⟨811166, by rfl⟩ : syracuseStep 1081555 = 1622333) B1622333
theorem B1081571 : Blo 1080619 1081571 := bstep (se 1 (by rfl) ⟨811178, by rfl⟩ : syracuseStep 1081571 = 1622357) B1622357
theorem B1081587 : Blo 1080619 1081587 := bstep (se 1 (by rfl) ⟨811190, by rfl⟩ : syracuseStep 1081587 = 1622381) B1622381
theorem B1081603 : Blo 1080619 1081603 := bstep (se 1 (by rfl) ⟨811202, by rfl⟩ : syracuseStep 1081603 = 1622405) B1622405
theorem B1081619 : Blo 1080619 1081619 := bstep (se 1 (by rfl) ⟨811214, by rfl⟩ : syracuseStep 1081619 = 1622429) B1622429
theorem B1081635 : Blo 1080619 1081635 := bstep (se 1 (by rfl) ⟨811226, by rfl⟩ : syracuseStep 1081635 = 1622453) B1622453
theorem B1081651 : Blo 1080619 1081651 := bstep (se 1 (by rfl) ⟨811238, by rfl⟩ : syracuseStep 1081651 = 1622477) B1622477
theorem B1081667 : Blo 1080619 1081667 := bstep (se 1 (by rfl) ⟨811250, by rfl⟩ : syracuseStep 1081667 = 1622501) B1622501
theorem B1081683 : Blo 1080619 1081683 := bstep (se 1 (by rfl) ⟨811262, by rfl⟩ : syracuseStep 1081683 = 1622525) B1622525
theorem B1081699 : Blo 1080619 1081699 := bstep (se 1 (by rfl) ⟨811274, by rfl⟩ : syracuseStep 1081699 = 1622549) B1622549
theorem B1081715 : Blo 1080619 1081715 := bstep (se 1 (by rfl) ⟨811286, by rfl⟩ : syracuseStep 1081715 = 1622573) B1622573
theorem B1081731 : Blo 1080619 1081731 := bstep (se 1 (by rfl) ⟨811298, by rfl⟩ : syracuseStep 1081731 = 1622597) B1622597
theorem B1081747 : Blo 1080619 1081747 := bstep (se 1 (by rfl) ⟨811310, by rfl⟩ : syracuseStep 1081747 = 1622621) B1622621
theorem B1081763 : Blo 1080619 1081763 := bstep (se 1 (by rfl) ⟨811322, by rfl⟩ : syracuseStep 1081763 = 1622645) B1622645
theorem B4620721 : Blo 1080619 4620721 := bstep (se 2 (by rfl) ⟨1732770, by rfl⟩ : syracuseStep 4620721 = 3465541) B3465541
theorem B1081779 : Blo 1080619 1081779 := bstep (se 1 (by rfl) ⟨811334, by rfl⟩ : syracuseStep 1081779 = 1622669) B1622669
theorem B1081795 : Blo 1080619 1081795 := bstep (se 1 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 1081795 = 1622693) B1622693
theorem B1081811 : Blo 1080619 1081811 := bstep (se 1 (by rfl) ⟨811358, by rfl⟩ : syracuseStep 1081811 = 1622717) B1622717
theorem B1081827 : Blo 1080619 1081827 := bstep (se 1 (by rfl) ⟨811370, by rfl⟩ : syracuseStep 1081827 = 1622741) B1622741
theorem B1081843 : Blo 1080619 1081843 := bstep (se 1 (by rfl) ⟨811382, by rfl⟩ : syracuseStep 1081843 = 1622765) B1622765
theorem B1081859 : Blo 1080619 1081859 := bstep (se 1 (by rfl) ⟨811394, by rfl⟩ : syracuseStep 1081859 = 1622789) B1622789
theorem B3899917 : Blo 1080619 3899917 := bstep (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) B1462469
theorem B1081875 : Blo 1080619 1081875 := bstep (se 1 (by rfl) ⟨811406, by rfl⟩ : syracuseStep 1081875 = 1622813) B1622813
theorem B1081891 : Blo 1080619 1081891 := bstep (se 1 (by rfl) ⟨811418, by rfl⟩ : syracuseStep 1081891 = 1622837) B1622837
theorem B1081907 : Blo 1080619 1081907 := bstep (se 1 (by rfl) ⟨811430, by rfl⟩ : syracuseStep 1081907 = 1622861) B1622861
theorem B1081923 : Blo 1080619 1081923 := bstep (se 1 (by rfl) ⟨811442, by rfl⟩ : syracuseStep 1081923 = 1622885) B1622885
theorem B5472845 : Blo 1080619 5472845 := bstep (se 3 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 5472845 = 2052317) B2052317
theorem B1081939 : Blo 1080619 1081939 := bstep (se 1 (by rfl) ⟨811454, by rfl⟩ : syracuseStep 1081939 = 1622909) B1622909
theorem B1081955 : Blo 1080619 1081955 := bstep (se 1 (by rfl) ⟨811466, by rfl⟩ : syracuseStep 1081955 = 1622933) B1622933
theorem B1081971 : Blo 1080619 1081971 := bstep (se 1 (by rfl) ⟨811478, by rfl⟩ : syracuseStep 1081971 = 1622957) B1622957
theorem B1081987 : Blo 1080619 1081987 := bstep (se 1 (by rfl) ⟨811490, by rfl⟩ : syracuseStep 1081987 = 1622981) B1622981
theorem B3080845 : Blo 1080619 3080845 := bstep (se 3 (by rfl) ⟨577658, by rfl⟩ : syracuseStep 3080845 = 1155317) B1155317
theorem B1082003 : Blo 1080619 1082003 := bstep (se 1 (by rfl) ⟨811502, by rfl⟩ : syracuseStep 1082003 = 1623005) B1623005
theorem B1082019 : Blo 1080619 1082019 := bstep (se 1 (by rfl) ⟨811514, by rfl⟩ : syracuseStep 1082019 = 1623029) B1623029
theorem B1082035 : Blo 1080619 1082035 := bstep (se 1 (by rfl) ⟨811526, by rfl⟩ : syracuseStep 1082035 = 1623053) B1623053
theorem B1540787 : Blo 1080619 1540787 := bstep (se 1 (by rfl) ⟨1155590, by rfl⟩ : syracuseStep 1540787 = 2311181) B2311181
theorem B1082051 : Blo 1080619 1082051 := bstep (se 1 (by rfl) ⟨811538, by rfl⟩ : syracuseStep 1082051 = 1623077) B1623077
theorem B1082067 : Blo 1080619 1082067 := bstep (se 1 (by rfl) ⟨811550, by rfl⟩ : syracuseStep 1082067 = 1623101) B1623101
theorem B1082083 : Blo 1080619 1082083 := bstep (se 1 (by rfl) ⟨811562, by rfl⟩ : syracuseStep 1082083 = 1623125) B1623125
theorem B1082099 : Blo 1080619 1082099 := bstep (se 1 (by rfl) ⟨811574, by rfl⟩ : syracuseStep 1082099 = 1623149) B1623149
theorem B1082115 : Blo 1080619 1082115 := bstep (se 1 (by rfl) ⟨811586, by rfl⟩ : syracuseStep 1082115 = 1623173) B1623173
theorem B8225549 : Blo 1080619 8225549 := bstep (se 3 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 8225549 = 3084581) B3084581
theorem B1082131 : Blo 1080619 1082131 := bstep (se 1 (by rfl) ⟨811598, by rfl⟩ : syracuseStep 1082131 = 1623197) B1623197
theorem B1082147 : Blo 1080619 1082147 := bstep (se 1 (by rfl) ⟨811610, by rfl⟩ : syracuseStep 1082147 = 1623221) B1623221
theorem B1082163 : Blo 1080619 1082163 := bstep (se 1 (by rfl) ⟨811622, by rfl⟩ : syracuseStep 1082163 = 1623245) B1623245
theorem B1082179 : Blo 1080619 1082179 := bstep (se 1 (by rfl) ⟨811634, by rfl⟩ : syracuseStep 1082179 = 1623269) B1623269
theorem B1082195 : Blo 1080619 1082195 := bstep (se 1 (by rfl) ⟨811646, by rfl⟩ : syracuseStep 1082195 = 1623293) B1623293
theorem B1082211 : Blo 1080619 1082211 := bstep (se 1 (by rfl) ⟨811658, by rfl⟩ : syracuseStep 1082211 = 1623317) B1623317
theorem B3081073 : Blo 1080619 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B1082227 : Blo 1080619 1082227 := bstep (se 1 (by rfl) ⟨811670, by rfl⟩ : syracuseStep 1082227 = 1623341) B1623341
theorem B1082243 : Blo 1080619 1082243 := bstep (se 1 (by rfl) ⟨811682, by rfl⟩ : syracuseStep 1082243 = 1623365) B1623365
theorem B1082259 : Blo 1080619 1082259 := bstep (se 1 (by rfl) ⟨811694, by rfl⟩ : syracuseStep 1082259 = 1623389) B1623389
theorem B1082275 : Blo 1080619 1082275 := bstep (se 1 (by rfl) ⟨811706, by rfl⟩ : syracuseStep 1082275 = 1623413) B1623413
theorem B1082291 : Blo 1080619 1082291 := bstep (se 1 (by rfl) ⟨811718, by rfl⟩ : syracuseStep 1082291 = 1623437) B1623437
theorem B1082307 : Blo 1080619 1082307 := bstep (se 1 (by rfl) ⟨811730, by rfl⟩ : syracuseStep 1082307 = 1623461) B1623461
theorem B1082323 : Blo 1080619 1082323 := bstep (se 1 (by rfl) ⟨811742, by rfl⟩ : syracuseStep 1082323 = 1623485) B1623485
theorem B1082339 : Blo 1080619 1082339 := bstep (se 1 (by rfl) ⟨811754, by rfl⟩ : syracuseStep 1082339 = 1623509) B1623509
theorem B1082355 : Blo 1080619 1082355 := bstep (se 1 (by rfl) ⟨811766, by rfl⟩ : syracuseStep 1082355 = 1623533) B1623533
theorem B1082371 : Blo 1080619 1082371 := bstep (se 1 (by rfl) ⟨811778, by rfl⟩ : syracuseStep 1082371 = 1623557) B1623557
theorem B3081233 : Blo 1080619 3081233 := bstep (se 2 (by rfl) ⟨1155462, by rfl⟩ : syracuseStep 3081233 = 2310925) B2310925
theorem B1082387 : Blo 1080619 1082387 := bstep (se 1 (by rfl) ⟨811790, by rfl⟩ : syracuseStep 1082387 = 1623581) B1623581
theorem B1082403 : Blo 1080619 1082403 := bstep (se 1 (by rfl) ⟨811802, by rfl⟩ : syracuseStep 1082403 = 1623605) B1623605
theorem B1082419 : Blo 1080619 1082419 := bstep (se 1 (by rfl) ⟨811814, by rfl⟩ : syracuseStep 1082419 = 1623629) B1623629
theorem B1082435 : Blo 1080619 1082435 := bstep (se 1 (by rfl) ⟨811826, by rfl⟩ : syracuseStep 1082435 = 1623653) B1623653
theorem B1082451 : Blo 1080619 1082451 := bstep (se 1 (by rfl) ⟨811838, by rfl⟩ : syracuseStep 1082451 = 1623677) B1623677
theorem B1082467 : Blo 1080619 1082467 := bstep (se 1 (by rfl) ⟨811850, by rfl⟩ : syracuseStep 1082467 = 1623701) B1623701
theorem B1082483 : Blo 1080619 1082483 := bstep (se 1 (by rfl) ⟨811862, by rfl⟩ : syracuseStep 1082483 = 1623725) B1623725
theorem B3081347 : Blo 1080619 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B1082499 : Blo 1080619 1082499 := bstep (se 1 (by rfl) ⟨811874, by rfl⟩ : syracuseStep 1082499 = 1623749) B1623749
theorem B4392077 : Blo 1080619 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B1082515 : Blo 1080619 1082515 := bstep (se 1 (by rfl) ⟨811886, by rfl⟩ : syracuseStep 1082515 = 1623773) B1623773
theorem B1082531 : Blo 1080619 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B1082547 : Blo 1080619 1082547 := bstep (se 1 (by rfl) ⟨811910, by rfl⟩ : syracuseStep 1082547 = 1623821) B1623821
theorem B1082563 : Blo 1080619 1082563 := bstep (se 1 (by rfl) ⟨811922, by rfl⟩ : syracuseStep 1082563 = 1623845) B1623845
theorem B18515141 : Blo 1080619 18515141 := bstep (se 4 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 18515141 = 3471589) B3471589
theorem B1082579 : Blo 1080619 1082579 := bstep (se 1 (by rfl) ⟨811934, by rfl⟩ : syracuseStep 1082579 = 1623869) B1623869
theorem B1082595 : Blo 1080619 1082595 := bstep (se 1 (by rfl) ⟨811946, by rfl⟩ : syracuseStep 1082595 = 1623893) B1623893
theorem B1082611 : Blo 1080619 1082611 := bstep (se 1 (by rfl) ⟨811958, by rfl⟩ : syracuseStep 1082611 = 1623917) B1623917
theorem B1082627 : Blo 1080619 1082627 := bstep (se 1 (by rfl) ⟨811970, by rfl⟩ : syracuseStep 1082627 = 1623941) B1623941
theorem B6161669 : Blo 1080619 6161669 := bstep (se 4 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 6161669 = 1155313) B1155313
theorem B1082643 : Blo 1080619 1082643 := bstep (se 1 (by rfl) ⟨811982, by rfl⟩ : syracuseStep 1082643 = 1623965) B1623965
theorem B1082659 : Blo 1080619 1082659 := bstep (se 1 (by rfl) ⟨811994, by rfl⟩ : syracuseStep 1082659 = 1623989) B1623989
theorem B1541425 : Blo 1080619 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B1082675 : Blo 1080619 1082675 := bstep (se 1 (by rfl) ⟨812006, by rfl⟩ : syracuseStep 1082675 = 1624013) B1624013
theorem B1082691 : Blo 1080619 1082691 := bstep (se 1 (by rfl) ⟨812018, by rfl⟩ : syracuseStep 1082691 = 1624037) B1624037
theorem B1082707 : Blo 1080619 1082707 := bstep (se 1 (by rfl) ⟨812030, by rfl⟩ : syracuseStep 1082707 = 1624061) B1624061
theorem B1082723 : Blo 1080619 1082723 := bstep (se 1 (by rfl) ⟨812042, by rfl⟩ : syracuseStep 1082723 = 1624085) B1624085
theorem B1082739 : Blo 1080619 1082739 := bstep (se 1 (by rfl) ⟨812054, by rfl⟩ : syracuseStep 1082739 = 1624109) B1624109
theorem B1082755 : Blo 1080619 1082755 := bstep (se 1 (by rfl) ⟨812066, by rfl⟩ : syracuseStep 1082755 = 1624133) B1624133
theorem B33326477 : Blo 1080619 33326477 := bstep (se 3 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 33326477 = 12497429) B12497429
theorem B1082771 : Blo 1080619 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B1541539 : Blo 1080619 1541539 := bstep (se 1 (by rfl) ⟨1156154, by rfl⟩ : syracuseStep 1541539 = 2312309) B2312309
theorem B1082787 : Blo 1080619 1082787 := bstep (se 1 (by rfl) ⟨812090, by rfl⟩ : syracuseStep 1082787 = 1624181) B1624181
theorem B1082803 : Blo 1080619 1082803 := bstep (se 1 (by rfl) ⟨812102, by rfl⟩ : syracuseStep 1082803 = 1624205) B1624205
theorem B1082819 : Blo 1080619 1082819 := bstep (se 1 (by rfl) ⟨812114, by rfl⟩ : syracuseStep 1082819 = 1624229) B1624229
theorem B1082835 : Blo 1080619 1082835 := bstep (se 1 (by rfl) ⟨812126, by rfl⟩ : syracuseStep 1082835 = 1624253) B1624253
theorem B1082851 : Blo 1080619 1082851 := bstep (se 1 (by rfl) ⟨812138, by rfl⟩ : syracuseStep 1082851 = 1624277) B1624277
theorem B1082867 : Blo 1080619 1082867 := bstep (se 1 (by rfl) ⟨812150, by rfl⟩ : syracuseStep 1082867 = 1624301) B1624301
theorem B1082883 : Blo 1080619 1082883 := bstep (se 1 (by rfl) ⟨812162, by rfl⟩ : syracuseStep 1082883 = 1624325) B1624325
theorem B1082899 : Blo 1080619 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B1082915 : Blo 1080619 1082915 := bstep (se 1 (by rfl) ⟨812186, by rfl⟩ : syracuseStep 1082915 = 1624373) B1624373
theorem B4687409 : Blo 1080619 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B1082931 : Blo 1080619 1082931 := bstep (se 1 (by rfl) ⟨812198, by rfl⟩ : syracuseStep 1082931 = 1624397) B1624397
theorem B1082947 : Blo 1080619 1082947 := bstep (se 1 (by rfl) ⟨812210, by rfl⟩ : syracuseStep 1082947 = 1624421) B1624421
theorem B1082963 : Blo 1080619 1082963 := bstep (se 1 (by rfl) ⟨812222, by rfl⟩ : syracuseStep 1082963 = 1624445) B1624445
theorem B1082979 : Blo 1080619 1082979 := bstep (se 1 (by rfl) ⟨812234, by rfl⟩ : syracuseStep 1082979 = 1624469) B1624469
theorem B1082995 : Blo 1080619 1082995 := bstep (se 1 (by rfl) ⟨812246, by rfl⟩ : syracuseStep 1082995 = 1624493) B1624493
theorem B1083011 : Blo 1080619 1083011 := bstep (se 1 (by rfl) ⟨812258, by rfl⟩ : syracuseStep 1083011 = 1624517) B1624517
theorem B1083027 : Blo 1080619 1083027 := bstep (se 1 (by rfl) ⟨812270, by rfl⟩ : syracuseStep 1083027 = 1624541) B1624541
theorem B1083043 : Blo 1080619 1083043 := bstep (se 1 (by rfl) ⟨812282, by rfl⟩ : syracuseStep 1083043 = 1624565) B1624565
theorem B1083059 : Blo 1080619 1083059 := bstep (se 1 (by rfl) ⟨812294, by rfl⟩ : syracuseStep 1083059 = 1624589) B1624589
theorem B1083075 : Blo 1080619 1083075 := bstep (se 1 (by rfl) ⟨812306, by rfl⟩ : syracuseStep 1083075 = 1624613) B1624613
theorem B1083091 : Blo 1080619 1083091 := bstep (se 1 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 1083091 = 1624637) B1624637
theorem B1083107 : Blo 1080619 1083107 := bstep (se 1 (by rfl) ⟨812330, by rfl⟩ : syracuseStep 1083107 = 1624661) B1624661
theorem B1083123 : Blo 1080619 1083123 := bstep (se 1 (by rfl) ⟨812342, by rfl⟩ : syracuseStep 1083123 = 1624685) B1624685
theorem B1083139 : Blo 1080619 1083139 := bstep (se 1 (by rfl) ⟨812354, by rfl⟩ : syracuseStep 1083139 = 1624709) B1624709
theorem B1083155 : Blo 1080619 1083155 := bstep (se 1 (by rfl) ⟨812366, by rfl⟩ : syracuseStep 1083155 = 1624733) B1624733
theorem B1083171 : Blo 1080619 1083171 := bstep (se 1 (by rfl) ⟨812378, by rfl⟩ : syracuseStep 1083171 = 1624757) B1624757
theorem B1083187 : Blo 1080619 1083187 := bstep (se 1 (by rfl) ⟨812390, by rfl⟩ : syracuseStep 1083187 = 1624781) B1624781
theorem B1083203 : Blo 1080619 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B1083219 : Blo 1080619 1083219 := bstep (se 1 (by rfl) ⟨812414, by rfl⟩ : syracuseStep 1083219 = 1624829) B1624829
theorem B1083235 : Blo 1080619 1083235 := bstep (se 1 (by rfl) ⟨812426, by rfl⟩ : syracuseStep 1083235 = 1624853) B1624853
theorem B1083251 : Blo 1080619 1083251 := bstep (se 1 (by rfl) ⟨812438, by rfl⟩ : syracuseStep 1083251 = 1624877) B1624877
theorem B1083267 : Blo 1080619 1083267 := bstep (se 1 (by rfl) ⟨812450, by rfl⟩ : syracuseStep 1083267 = 1624901) B1624901
theorem B1083283 : Blo 1080619 1083283 := bstep (se 1 (by rfl) ⟨812462, by rfl⟩ : syracuseStep 1083283 = 1624925) B1624925
theorem B1083299 : Blo 1080619 1083299 := bstep (se 1 (by rfl) ⟨812474, by rfl⟩ : syracuseStep 1083299 = 1624949) B1624949
theorem B1083315 : Blo 1080619 1083315 := bstep (se 1 (by rfl) ⟨812486, by rfl⟩ : syracuseStep 1083315 = 1624973) B1624973
theorem B1083331 : Blo 1080619 1083331 := bstep (se 1 (by rfl) ⟨812498, by rfl⟩ : syracuseStep 1083331 = 1624997) B1624997
theorem B1083347 : Blo 1080619 1083347 := bstep (se 1 (by rfl) ⟨812510, by rfl⟩ : syracuseStep 1083347 = 1625021) B1625021
theorem B1083363 : Blo 1080619 1083363 := bstep (se 1 (by rfl) ⟨812522, by rfl⟩ : syracuseStep 1083363 = 1625045) B1625045
theorem B1083379 : Blo 1080619 1083379 := bstep (se 1 (by rfl) ⟨812534, by rfl⟩ : syracuseStep 1083379 = 1625069) B1625069
theorem B1083395 : Blo 1080619 1083395 := bstep (se 1 (by rfl) ⟨812546, by rfl⟩ : syracuseStep 1083395 = 1625093) B1625093
theorem B1083411 : Blo 1080619 1083411 := bstep (se 1 (by rfl) ⟨812558, by rfl⟩ : syracuseStep 1083411 = 1625117) B1625117
theorem B1083427 : Blo 1080619 1083427 := bstep (se 1 (by rfl) ⟨812570, by rfl⟩ : syracuseStep 1083427 = 1625141) B1625141
theorem B1083443 : Blo 1080619 1083443 := bstep (se 1 (by rfl) ⟨812582, by rfl⟩ : syracuseStep 1083443 = 1625165) B1625165
theorem B1083459 : Blo 1080619 1083459 := bstep (se 1 (by rfl) ⟨812594, by rfl⟩ : syracuseStep 1083459 = 1625189) B1625189
theorem B1083475 : Blo 1080619 1083475 := bstep (se 1 (by rfl) ⟨812606, by rfl⟩ : syracuseStep 1083475 = 1625213) B1625213
theorem B1083491 : Blo 1080619 1083491 := bstep (se 1 (by rfl) ⟨812618, by rfl⟩ : syracuseStep 1083491 = 1625237) B1625237
theorem B3082349 : Blo 1080619 3082349 := bstep (se 3 (by rfl) ⟨577940, by rfl⟩ : syracuseStep 3082349 = 1155881) B1155881
theorem B1083507 : Blo 1080619 1083507 := bstep (se 1 (by rfl) ⟨812630, by rfl⟩ : syracuseStep 1083507 = 1625261) B1625261
theorem B1083523 : Blo 1080619 1083523 := bstep (se 1 (by rfl) ⟨812642, by rfl⟩ : syracuseStep 1083523 = 1625285) B1625285
theorem B1083539 : Blo 1080619 1083539 := bstep (se 1 (by rfl) ⟨812654, by rfl⟩ : syracuseStep 1083539 = 1625309) B1625309
theorem B1083555 : Blo 1080619 1083555 := bstep (se 1 (by rfl) ⟨812666, by rfl⟩ : syracuseStep 1083555 = 1625333) B1625333
theorem B1083571 : Blo 1080619 1083571 := bstep (se 1 (by rfl) ⟨812678, by rfl⟩ : syracuseStep 1083571 = 1625357) B1625357
theorem B1083587 : Blo 1080619 1083587 := bstep (se 1 (by rfl) ⟨812690, by rfl⟩ : syracuseStep 1083587 = 1625381) B1625381
theorem B1083603 : Blo 1080619 1083603 := bstep (se 1 (by rfl) ⟨812702, by rfl⟩ : syracuseStep 1083603 = 1625405) B1625405
theorem B1083619 : Blo 1080619 1083619 := bstep (se 1 (by rfl) ⟨812714, by rfl⟩ : syracuseStep 1083619 = 1625429) B1625429
theorem B1083635 : Blo 1080619 1083635 := bstep (se 1 (by rfl) ⟨812726, by rfl⟩ : syracuseStep 1083635 = 1625453) B1625453
theorem B1083651 : Blo 1080619 1083651 := bstep (se 1 (by rfl) ⟨812738, by rfl⟩ : syracuseStep 1083651 = 1625477) B1625477
theorem B1083667 : Blo 1080619 1083667 := bstep (se 1 (by rfl) ⟨812750, by rfl⟩ : syracuseStep 1083667 = 1625501) B1625501
theorem B3082531 : Blo 1080619 3082531 := bstep (se 1 (by rfl) ⟨2311898, by rfl⟩ : syracuseStep 3082531 = 4623797) B4623797
theorem B1083683 : Blo 1080619 1083683 := bstep (se 1 (by rfl) ⟨812762, by rfl⟩ : syracuseStep 1083683 = 1625525) B1625525
theorem B1083699 : Blo 1080619 1083699 := bstep (se 1 (by rfl) ⟨812774, by rfl⟩ : syracuseStep 1083699 = 1625549) B1625549
theorem B1083715 : Blo 1080619 1083715 := bstep (se 1 (by rfl) ⟨812786, by rfl⟩ : syracuseStep 1083715 = 1625573) B1625573
theorem B1083731 : Blo 1080619 1083731 := bstep (se 1 (by rfl) ⟨812798, by rfl⟩ : syracuseStep 1083731 = 1625597) B1625597
theorem B1083747 : Blo 1080619 1083747 := bstep (se 1 (by rfl) ⟨812810, by rfl⟩ : syracuseStep 1083747 = 1625621) B1625621
theorem B1083763 : Blo 1080619 1083763 := bstep (se 1 (by rfl) ⟨812822, by rfl⟩ : syracuseStep 1083763 = 1625645) B1625645
theorem B1083779 : Blo 1080619 1083779 := bstep (se 1 (by rfl) ⟨812834, by rfl⟩ : syracuseStep 1083779 = 1625669) B1625669
theorem B1083795 : Blo 1080619 1083795 := bstep (se 1 (by rfl) ⟨812846, by rfl⟩ : syracuseStep 1083795 = 1625693) B1625693
theorem B1083811 : Blo 1080619 1083811 := bstep (se 1 (by rfl) ⟨812858, by rfl⟩ : syracuseStep 1083811 = 1625717) B1625717
theorem B1083827 : Blo 1080619 1083827 := bstep (se 1 (by rfl) ⟨812870, by rfl⟩ : syracuseStep 1083827 = 1625741) B1625741
theorem B3082691 : Blo 1080619 3082691 := bstep (se 1 (by rfl) ⟨2312018, by rfl⟩ : syracuseStep 3082691 = 4624037) B4624037
theorem B1083843 : Blo 1080619 1083843 := bstep (se 1 (by rfl) ⟨812882, by rfl⟩ : syracuseStep 1083843 = 1625765) B1625765
theorem B1083859 : Blo 1080619 1083859 := bstep (se 1 (by rfl) ⟨812894, by rfl⟩ : syracuseStep 1083859 = 1625789) B1625789
theorem B1083875 : Blo 1080619 1083875 := bstep (se 1 (by rfl) ⟨812906, by rfl⟩ : syracuseStep 1083875 = 1625813) B1625813
theorem B1083891 : Blo 1080619 1083891 := bstep (se 1 (by rfl) ⟨812918, by rfl⟩ : syracuseStep 1083891 = 1625837) B1625837
theorem B1083907 : Blo 1080619 1083907 := bstep (se 1 (by rfl) ⟨812930, by rfl⟩ : syracuseStep 1083907 = 1625861) B1625861
theorem B1083923 : Blo 1080619 1083923 := bstep (se 1 (by rfl) ⟨812942, by rfl⟩ : syracuseStep 1083923 = 1625885) B1625885
theorem B1083939 : Blo 1080619 1083939 := bstep (se 1 (by rfl) ⟨812954, by rfl⟩ : syracuseStep 1083939 = 1625909) B1625909
theorem B1083955 : Blo 1080619 1083955 := bstep (se 1 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 1083955 = 1625933) B1625933
theorem B1083971 : Blo 1080619 1083971 := bstep (se 1 (by rfl) ⟨812978, by rfl⟩ : syracuseStep 1083971 = 1625957) B1625957
theorem B1083987 : Blo 1080619 1083987 := bstep (se 1 (by rfl) ⟨812990, by rfl⟩ : syracuseStep 1083987 = 1625981) B1625981
theorem B1084003 : Blo 1080619 1084003 := bstep (se 1 (by rfl) ⟨813002, by rfl⟩ : syracuseStep 1084003 = 1626005) B1626005
theorem B1084019 : Blo 1080619 1084019 := bstep (se 1 (by rfl) ⟨813014, by rfl⟩ : syracuseStep 1084019 = 1626029) B1626029
theorem B1084035 : Blo 1080619 1084035 := bstep (se 1 (by rfl) ⟨813026, by rfl⟩ : syracuseStep 1084035 = 1626053) B1626053
theorem B1084051 : Blo 1080619 1084051 := bstep (se 1 (by rfl) ⟨813038, by rfl⟩ : syracuseStep 1084051 = 1626077) B1626077
theorem B1084067 : Blo 1080619 1084067 := bstep (se 1 (by rfl) ⟨813050, by rfl⟩ : syracuseStep 1084067 = 1626101) B1626101
theorem B1084083 : Blo 1080619 1084083 := bstep (se 1 (by rfl) ⟨813062, by rfl⟩ : syracuseStep 1084083 = 1626125) B1626125
theorem B1084099 : Blo 1080619 1084099 := bstep (se 1 (by rfl) ⟨813074, by rfl⟩ : syracuseStep 1084099 = 1626149) B1626149
theorem B1084115 : Blo 1080619 1084115 := bstep (se 1 (by rfl) ⟨813086, by rfl⟩ : syracuseStep 1084115 = 1626173) B1626173
theorem B8784611 : Blo 1080619 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B1542883 : Blo 1080619 1542883 := bstep (se 1 (by rfl) ⟨1157162, by rfl⟩ : syracuseStep 1542883 = 2314325) B2314325
theorem B1084131 : Blo 1080619 1084131 := bstep (se 1 (by rfl) ⟨813098, by rfl⟩ : syracuseStep 1084131 = 1626197) B1626197
theorem B1084147 : Blo 1080619 1084147 := bstep (se 1 (by rfl) ⟨813110, by rfl⟩ : syracuseStep 1084147 = 1626221) B1626221
theorem B1084163 : Blo 1080619 1084163 := bstep (se 1 (by rfl) ⟨813122, by rfl⟩ : syracuseStep 1084163 = 1626245) B1626245
theorem B1084179 : Blo 1080619 1084179 := bstep (se 1 (by rfl) ⟨813134, by rfl⟩ : syracuseStep 1084179 = 1626269) B1626269
theorem B1084195 : Blo 1080619 1084195 := bstep (se 1 (by rfl) ⟨813146, by rfl⟩ : syracuseStep 1084195 = 1626293) B1626293
theorem B1084211 : Blo 1080619 1084211 := bstep (se 1 (by rfl) ⟨813158, by rfl⟩ : syracuseStep 1084211 = 1626317) B1626317
theorem B1084227 : Blo 1080619 1084227 := bstep (se 1 (by rfl) ⟨813170, by rfl⟩ : syracuseStep 1084227 = 1626341) B1626341
theorem B1084243 : Blo 1080619 1084243 := bstep (se 1 (by rfl) ⟨813182, by rfl⟩ : syracuseStep 1084243 = 1626365) B1626365
theorem B1084259 : Blo 1080619 1084259 := bstep (se 1 (by rfl) ⟨813194, by rfl⟩ : syracuseStep 1084259 = 1626389) B1626389
theorem B1084275 : Blo 1080619 1084275 := bstep (se 1 (by rfl) ⟨813206, by rfl⟩ : syracuseStep 1084275 = 1626413) B1626413
theorem B1084291 : Blo 1080619 1084291 := bstep (se 1 (by rfl) ⟨813218, by rfl⟩ : syracuseStep 1084291 = 1626437) B1626437
theorem B1084307 : Blo 1080619 1084307 := bstep (se 1 (by rfl) ⟨813230, by rfl⟩ : syracuseStep 1084307 = 1626461) B1626461
theorem B1084323 : Blo 1080619 1084323 := bstep (se 1 (by rfl) ⟨813242, by rfl⟩ : syracuseStep 1084323 = 1626485) B1626485
theorem B1084339 : Blo 1080619 1084339 := bstep (se 1 (by rfl) ⟨813254, by rfl⟩ : syracuseStep 1084339 = 1626509) B1626509
theorem B1084355 : Blo 1080619 1084355 := bstep (se 1 (by rfl) ⟨813266, by rfl⟩ : syracuseStep 1084355 = 1626533) B1626533
theorem B1084371 : Blo 1080619 1084371 := bstep (se 1 (by rfl) ⟨813278, by rfl⟩ : syracuseStep 1084371 = 1626557) B1626557
theorem B1084387 : Blo 1080619 1084387 := bstep (se 1 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 1084387 = 1626581) B1626581
theorem B1084403 : Blo 1080619 1084403 := bstep (se 1 (by rfl) ⟨813302, by rfl⟩ : syracuseStep 1084403 = 1626605) B1626605
theorem B1084419 : Blo 1080619 1084419 := bstep (se 1 (by rfl) ⟨813314, by rfl⟩ : syracuseStep 1084419 = 1626629) B1626629
theorem B1084435 : Blo 1080619 1084435 := bstep (se 1 (by rfl) ⟨813326, by rfl⟩ : syracuseStep 1084435 = 1626653) B1626653
theorem B1084451 : Blo 1080619 1084451 := bstep (se 1 (by rfl) ⟨813338, by rfl⟩ : syracuseStep 1084451 = 1626677) B1626677
theorem B1084467 : Blo 1080619 1084467 := bstep (se 1 (by rfl) ⟨813350, by rfl⟩ : syracuseStep 1084467 = 1626701) B1626701
theorem B1084483 : Blo 1080619 1084483 := bstep (se 1 (by rfl) ⟨813362, by rfl⟩ : syracuseStep 1084483 = 1626725) B1626725
theorem B1084499 : Blo 1080619 1084499 := bstep (se 1 (by rfl) ⟨813374, by rfl⟩ : syracuseStep 1084499 = 1626749) B1626749
theorem B1084515 : Blo 1080619 1084515 := bstep (se 1 (by rfl) ⟨813386, by rfl⟩ : syracuseStep 1084515 = 1626773) B1626773
theorem B1084531 : Blo 1080619 1084531 := bstep (se 1 (by rfl) ⟨813398, by rfl⟩ : syracuseStep 1084531 = 1626797) B1626797
theorem B1084547 : Blo 1080619 1084547 := bstep (se 1 (by rfl) ⟨813410, by rfl⟩ : syracuseStep 1084547 = 1626821) B1626821
theorem B1084563 : Blo 1080619 1084563 := bstep (se 1 (by rfl) ⟨813422, by rfl⟩ : syracuseStep 1084563 = 1626845) B1626845
theorem B1084579 : Blo 1080619 1084579 := bstep (se 1 (by rfl) ⟨813434, by rfl⟩ : syracuseStep 1084579 = 1626869) B1626869
theorem B1084595 : Blo 1080619 1084595 := bstep (se 1 (by rfl) ⟨813446, by rfl⟩ : syracuseStep 1084595 = 1626893) B1626893
theorem B1084611 : Blo 1080619 1084611 := bstep (se 1 (by rfl) ⟨813458, by rfl⟩ : syracuseStep 1084611 = 1626917) B1626917
theorem B1215715 : Blo 1080619 1215715 := bstep (se 1 (by rfl) ⟨911786, by rfl⟩ : syracuseStep 1215715 = 1823573) B1823573
theorem B7409009 : Blo 1080619 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B1215859 : Blo 1080619 1215859 := bstep (se 1 (by rfl) ⟨911894, by rfl⟩ : syracuseStep 1215859 = 1823789) B1823789
theorem B5475761 : Blo 1080619 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B3083761 : Blo 1080619 3083761 := bstep (se 2 (by rfl) ⟨1156410, by rfl⟩ : syracuseStep 3083761 = 2312821) B2312821
theorem B1216003 : Blo 1080619 1216003 := bstep (se 1 (by rfl) ⟨912002, by rfl⟩ : syracuseStep 1216003 = 1824005) B1824005
theorem B4689521 : Blo 1080619 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B8228465 : Blo 1080619 8228465 := bstep (se 2 (by rfl) ⟨3085674, by rfl⟩ : syracuseStep 8228465 = 6171349) B6171349
theorem B1216147 : Blo 1080619 1216147 := bstep (se 1 (by rfl) ⟨912110, by rfl⟩ : syracuseStep 1216147 = 1824221) B1824221
theorem B1216291 : Blo 1080619 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B1544017 : Blo 1080619 1544017 := bstep (se 2 (by rfl) ⟨579006, by rfl⟩ : syracuseStep 1544017 = 1158013) B1158013
theorem B1544113 : Blo 1080619 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B1216435 : Blo 1080619 1216435 := bstep (se 1 (by rfl) ⟨912326, by rfl⟩ : syracuseStep 1216435 = 1824653) B1824653
theorem B14815217 : Blo 1080619 14815217 := bstep (se 2 (by rfl) ⟨5555706, by rfl⟩ : syracuseStep 14815217 = 11111413) B11111413
theorem B3706883 : Blo 1080619 3706883 := bstep (se 1 (by rfl) ⟨2780162, by rfl⟩ : syracuseStep 3706883 = 5560325) B5560325
theorem B4624397 : Blo 1080619 4624397 := bstep (se 3 (by rfl) ⟨867074, by rfl⟩ : syracuseStep 4624397 = 1734149) B1734149
theorem B1216579 : Blo 1080619 1216579 := bstep (se 1 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 1216579 = 1824869) B1824869
theorem B1216723 : Blo 1080619 1216723 := bstep (se 1 (by rfl) ⟨912542, by rfl⟩ : syracuseStep 1216723 = 1825085) B1825085
theorem B1216867 : Blo 1080619 1216867 := bstep (se 1 (by rfl) ⟨912650, by rfl⟩ : syracuseStep 1216867 = 1825301) B1825301
theorem B1217011 : Blo 1080619 1217011 := bstep (se 1 (by rfl) ⟨912758, by rfl⟩ : syracuseStep 1217011 = 1825517) B1825517
theorem B3707459 : Blo 1080619 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B1217155 : Blo 1080619 1217155 := bstep (se 1 (by rfl) ⟨912866, by rfl⟩ : syracuseStep 1217155 = 1825733) B1825733
theorem B2921197 : Blo 1080619 2921197 := bstep (se 3 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 2921197 = 1095449) B1095449
theorem B3085037 : Blo 1080619 3085037 := bstep (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) B1156889
theorem B1217299 : Blo 1080619 1217299 := bstep (se 1 (by rfl) ⟨912974, by rfl⟩ : syracuseStep 1217299 = 1825949) B1825949
theorem B5477219 : Blo 1080619 5477219 := bstep (se 1 (by rfl) ⟨4107914, by rfl⟩ : syracuseStep 5477219 = 8215829) B8215829
theorem B1217443 : Blo 1080619 1217443 := bstep (se 1 (by rfl) ⟨913082, by rfl⟩ : syracuseStep 1217443 = 1826165) B1826165
theorem B3085219 : Blo 1080619 3085219 := bstep (se 1 (by rfl) ⟨2313914, by rfl⟩ : syracuseStep 3085219 = 4627829) B4627829
theorem B14062517 : Blo 1080619 14062517 := bstep (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) B1318361
theorem B3085265 : Blo 1080619 3085265 := bstep (se 2 (by rfl) ⟨1156974, by rfl⟩ : syracuseStep 3085265 = 2313949) B2313949
theorem B6165517 : Blo 1080619 6165517 := bstep (se 3 (by rfl) ⟨1156034, by rfl⟩ : syracuseStep 6165517 = 2312069) B2312069
theorem B1217587 : Blo 1080619 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B1217731 : Blo 1080619 1217731 := bstep (se 1 (by rfl) ⟨913298, by rfl⟩ : syracuseStep 1217731 = 1826597) B1826597
theorem B1217875 : Blo 1080619 1217875 := bstep (se 1 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 1217875 = 1826813) B1826813
theorem B1250707 : Blo 1080619 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B1218019 : Blo 1080619 1218019 := bstep (se 1 (by rfl) ⟨913514, by rfl⟩ : syracuseStep 1218019 = 1827029) B1827029
theorem B6592013 : Blo 1080619 6592013 := bstep (se 3 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 6592013 = 2472005) B2472005
theorem B1218163 : Blo 1080619 1218163 := bstep (se 1 (by rfl) ⟨913622, by rfl⟩ : syracuseStep 1218163 = 1827245) B1827245
theorem B5478029 : Blo 1080619 5478029 := bstep (se 3 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 5478029 = 2054261) B2054261
theorem B1644257 : Blo 1080619 1644257 := bstep (se 2 (by rfl) ⟨616596, by rfl⟩ : syracuseStep 1644257 = 1233193) B1233193
theorem B1218307 : Blo 1080619 1218307 := bstep (se 1 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 1218307 = 1827461) B1827461
theorem B1644305 : Blo 1080619 1644305 := bstep (se 2 (by rfl) ⟨616614, by rfl⟩ : syracuseStep 1644305 = 1233229) B1233229
theorem B1218451 : Blo 1080619 1218451 := bstep (se 1 (by rfl) ⟨913838, by rfl⟩ : syracuseStep 1218451 = 1827677) B1827677
theorem B1218595 : Blo 1080619 1218595 := bstep (se 1 (by rfl) ⟨913946, by rfl⟩ : syracuseStep 1218595 = 1827893) B1827893
theorem B1218739 : Blo 1080619 1218739 := bstep (se 1 (by rfl) ⟨914054, by rfl⟩ : syracuseStep 1218739 = 1828109) B1828109
theorem B1218883 : Blo 1080619 1218883 := bstep (se 1 (by rfl) ⟨914162, by rfl⟩ : syracuseStep 1218883 = 1828325) B1828325
theorem B3086723 : Blo 1080619 3086723 := bstep (se 1 (by rfl) ⟨2315042, by rfl⟩ : syracuseStep 3086723 = 4630085) B4630085
theorem B15604109 : Blo 1080619 15604109 := bstep (se 3 (by rfl) ⟨2925770, by rfl⟩ : syracuseStep 15604109 = 5851541) B5851541
theorem B3119555 : Blo 1080619 3119555 := bstep (se 1 (by rfl) ⟨2339666, by rfl⟩ : syracuseStep 3119555 = 4679333) B4679333
theorem B1219027 : Blo 1080619 1219027 := bstep (se 1 (by rfl) ⟨914270, by rfl⟩ : syracuseStep 1219027 = 1828541) B1828541
theorem B2923057 : Blo 1080619 2923057 := bstep (se 2 (by rfl) ⟨1096146, by rfl⟩ : syracuseStep 2923057 = 2192293) B2192293
theorem B1219171 : Blo 1080619 1219171 := bstep (se 1 (by rfl) ⟨914378, by rfl⟩ : syracuseStep 1219171 = 1828757) B1828757
theorem B2431601 : Blo 1080619 2431601 := bstep (se 2 (by rfl) ⟨911850, by rfl⟩ : syracuseStep 2431601 = 1823701) B1823701
theorem B2431619 : Blo 1080619 2431619 := bstep (se 1 (by rfl) ⟨1823714, by rfl⟩ : syracuseStep 2431619 = 3647429) B3647429
theorem B1219315 : Blo 1080619 1219315 := bstep (se 1 (by rfl) ⟨914486, by rfl⟩ : syracuseStep 1219315 = 1828973) B1828973
theorem B1219459 : Blo 1080619 1219459 := bstep (se 1 (by rfl) ⟨914594, by rfl⟩ : syracuseStep 1219459 = 1829189) B1829189
theorem B2431889 : Blo 1080619 2431889 := bstep (se 2 (by rfl) ⟨911958, by rfl⟩ : syracuseStep 2431889 = 1823917) B1823917
theorem B2431907 : Blo 1080619 2431907 := bstep (se 1 (by rfl) ⟨1823930, by rfl⟩ : syracuseStep 2431907 = 3647861) B3647861
theorem B6167501 : Blo 1080619 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B9247729 : Blo 1080619 9247729 := bstep (se 2 (by rfl) ⟨3467898, by rfl⟩ : syracuseStep 9247729 = 6935797) B6935797
theorem B1219603 : Blo 1080619 1219603 := bstep (se 1 (by rfl) ⟨914702, by rfl⟩ : syracuseStep 1219603 = 1829405) B1829405
theorem B1154083 : Blo 1080619 1154083 := bstep (se 1 (by rfl) ⟨865562, by rfl⟩ : syracuseStep 1154083 = 1731125) B1731125
theorem B1219747 : Blo 1080619 1219747 := bstep (se 1 (by rfl) ⟨914810, by rfl⟩ : syracuseStep 1219747 = 1829621) B1829621
theorem B2432177 : Blo 1080619 2432177 := bstep (se 2 (by rfl) ⟨912066, by rfl⟩ : syracuseStep 2432177 = 1824133) B1824133
theorem B2432195 : Blo 1080619 2432195 := bstep (se 1 (by rfl) ⟨1824146, by rfl⟩ : syracuseStep 2432195 = 3648293) B3648293
theorem B1219891 : Blo 1080619 1219891 := bstep (se 1 (by rfl) ⟨914918, by rfl⟩ : syracuseStep 1219891 = 1829837) B1829837
theorem B52600205 : Blo 1080619 52600205 := bstep (se 3 (by rfl) ⟨9862538, by rfl⟩ : syracuseStep 52600205 = 19725077) B19725077
theorem B1220035 : Blo 1080619 1220035 := bstep (se 1 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 1220035 = 1830053) B1830053
theorem B2432465 : Blo 1080619 2432465 := bstep (se 2 (by rfl) ⟨912174, by rfl⟩ : syracuseStep 2432465 = 1824349) B1824349
theorem B2432483 : Blo 1080619 2432483 := bstep (se 1 (by rfl) ⟨1824362, by rfl⟩ : syracuseStep 2432483 = 3648725) B3648725
theorem B1154531 : Blo 1080619 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B4103693 : Blo 1080619 4103693 := bstep (se 3 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 4103693 = 1538885) B1538885
theorem B3087953 : Blo 1080619 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B1220179 : Blo 1080619 1220179 := bstep (se 1 (by rfl) ⟨915134, by rfl⟩ : syracuseStep 1220179 = 1830269) B1830269
theorem B2596465 : Blo 1080619 2596465 := bstep (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) B1947349
theorem B2432753 : Blo 1080619 2432753 := bstep (se 2 (by rfl) ⟨912282, by rfl⟩ : syracuseStep 2432753 = 1824565) B1824565
theorem B2432771 : Blo 1080619 2432771 := bstep (se 1 (by rfl) ⟨1824578, by rfl⟩ : syracuseStep 2432771 = 3649157) B3649157
theorem B6168433 : Blo 1080619 6168433 := bstep (se 2 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 6168433 = 4626325) B4626325
theorem B2433041 : Blo 1080619 2433041 := bstep (se 2 (by rfl) ⟨912390, by rfl⟩ : syracuseStep 2433041 = 1824781) B1824781
theorem B2924561 : Blo 1080619 2924561 := bstep (se 2 (by rfl) ⟨1096710, by rfl⟩ : syracuseStep 2924561 = 2193421) B2193421
theorem B2433059 : Blo 1080619 2433059 := bstep (se 1 (by rfl) ⟨1824794, by rfl⟩ : syracuseStep 2433059 = 3649589) B3649589
theorem B3121265 : Blo 1080619 3121265 := bstep (se 2 (by rfl) ⟨1170474, by rfl⟩ : syracuseStep 3121265 = 2340949) B2340949
theorem B4628771 : Blo 1080619 4628771 := bstep (se 1 (by rfl) ⟨3471578, by rfl⟩ : syracuseStep 4628771 = 6943157) B6943157
theorem B2433329 : Blo 1080619 2433329 := bstep (se 2 (by rfl) ⟨912498, by rfl⟩ : syracuseStep 2433329 = 1824997) B1824997
theorem B2433347 : Blo 1080619 2433347 := bstep (se 1 (by rfl) ⟨1825010, by rfl⟩ : syracuseStep 2433347 = 3650021) B3650021
theorem B5480945 : Blo 1080619 5480945 := bstep (se 2 (by rfl) ⟨2055354, by rfl⟩ : syracuseStep 5480945 = 4110709) B4110709
theorem B2433617 : Blo 1080619 2433617 := bstep (se 2 (by rfl) ⟨912606, by rfl⟩ : syracuseStep 2433617 = 1825213) B1825213
theorem B2433635 : Blo 1080619 2433635 := bstep (se 1 (by rfl) ⟨1825226, by rfl⟩ : syracuseStep 2433635 = 3650453) B3650453
theorem B1155907 : Blo 1080619 1155907 := bstep (se 1 (by rfl) ⟨866930, by rfl⟩ : syracuseStep 1155907 = 1733861) B1733861
theorem B2433905 : Blo 1080619 2433905 := bstep (se 2 (by rfl) ⟨912714, by rfl⟩ : syracuseStep 2433905 = 1825429) B1825429
theorem B2433923 : Blo 1080619 2433923 := bstep (se 1 (by rfl) ⟨1825442, by rfl⟩ : syracuseStep 2433923 = 3650885) B3650885
theorem B1647587 : Blo 1080619 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B2434193 : Blo 1080619 2434193 := bstep (se 2 (by rfl) ⟨912822, by rfl⟩ : syracuseStep 2434193 = 1825645) B1825645
theorem B2434211 : Blo 1080619 2434211 := bstep (se 1 (by rfl) ⟨1825658, by rfl⟩ : syracuseStep 2434211 = 3651317) B3651317
theorem B2467043 : Blo 1080619 2467043 := bstep (se 1 (by rfl) ⟨1850282, by rfl⟩ : syracuseStep 2467043 = 3700565) B3700565
theorem B6169891 : Blo 1080619 6169891 := bstep (se 1 (by rfl) ⟨4627418, by rfl⟩ : syracuseStep 6169891 = 9254837) B9254837
theorem B1779059 : Blo 1080619 1779059 := bstep (se 1 (by rfl) ⟨1334294, by rfl⟩ : syracuseStep 1779059 = 2668589) B2668589
theorem B2434481 : Blo 1080619 2434481 := bstep (se 2 (by rfl) ⟨912930, by rfl⟩ : syracuseStep 2434481 = 1825861) B1825861
theorem B2434499 : Blo 1080619 2434499 := bstep (se 1 (by rfl) ⟨1825874, by rfl⟩ : syracuseStep 2434499 = 3651749) B3651749
theorem B4695715 : Blo 1080619 4695715 := bstep (se 1 (by rfl) ⟨3521786, by rfl⟩ : syracuseStep 4695715 = 7043573) B7043573
theorem B2434769 : Blo 1080619 2434769 := bstep (se 2 (by rfl) ⟨913038, by rfl⟩ : syracuseStep 2434769 = 1826077) B1826077
theorem B2434787 : Blo 1080619 2434787 := bstep (se 1 (by rfl) ⟨1826090, by rfl⟩ : syracuseStep 2434787 = 3652181) B3652181
theorem B3647213 : Blo 1080619 3647213 := bstep (se 3 (by rfl) ⟨683852, by rfl⟩ : syracuseStep 3647213 = 1367705) B1367705
theorem B3647267 : Blo 1080619 3647267 := bstep (se 1 (by rfl) ⟨2735450, by rfl⟩ : syracuseStep 3647267 = 5470901) B5470901
theorem B6170417 : Blo 1080619 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B5482403 : Blo 1080619 5482403 := bstep (se 1 (by rfl) ⟨4111802, by rfl⟩ : syracuseStep 5482403 = 8223605) B8223605
theorem B2435057 : Blo 1080619 2435057 := bstep (se 2 (by rfl) ⟨913146, by rfl⟩ : syracuseStep 2435057 = 1826293) B1826293
theorem B2435075 : Blo 1080619 2435075 := bstep (se 1 (by rfl) ⟨1826306, by rfl⟩ : syracuseStep 2435075 = 3652613) B3652613
theorem B3647537 : Blo 1080619 3647537 := bstep (se 2 (by rfl) ⟨1367826, by rfl⟩ : syracuseStep 3647537 = 2735653) B2735653
theorem B1157171 : Blo 1080619 1157171 := bstep (se 1 (by rfl) ⟨867878, by rfl⟩ : syracuseStep 1157171 = 1735757) B1735757
theorem B3287213 : Blo 1080619 3287213 := bstep (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) B1232705
theorem B1648817 : Blo 1080619 1648817 := bstep (se 2 (by rfl) ⟨618306, by rfl⟩ : syracuseStep 1648817 = 1236613) B1236613
theorem B4630769 : Blo 1080619 4630769 := bstep (se 2 (by rfl) ⟨1736538, by rfl⟩ : syracuseStep 4630769 = 3473077) B3473077
theorem B2435345 : Blo 1080619 2435345 := bstep (se 2 (by rfl) ⟨913254, by rfl⟩ : syracuseStep 2435345 = 1826509) B1826509
theorem B2435363 : Blo 1080619 2435363 := bstep (se 1 (by rfl) ⟨1826522, by rfl⟩ : syracuseStep 2435363 = 3653045) B3653045
theorem B4106609 : Blo 1080619 4106609 := bstep (se 2 (by rfl) ⟨1539978, by rfl⟩ : syracuseStep 4106609 = 3079957) B3079957
theorem B1878563 : Blo 1080619 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B2435633 : Blo 1080619 2435633 := bstep (se 2 (by rfl) ⟨913362, by rfl⟩ : syracuseStep 2435633 = 1826725) B1826725
theorem B1485361 : Blo 1080619 1485361 := bstep (se 2 (by rfl) ⟨557010, by rfl⟩ : syracuseStep 1485361 = 1114021) B1114021
theorem B2435651 : Blo 1080619 2435651 := bstep (se 1 (by rfl) ⟨1826738, by rfl⟩ : syracuseStep 2435651 = 3653477) B3653477
theorem B3648077 : Blo 1080619 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B3648131 : Blo 1080619 3648131 := bstep (se 1 (by rfl) ⟨2736098, by rfl⟩ : syracuseStep 3648131 = 5472197) B5472197
theorem B2468483 : Blo 1080619 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B5483213 : Blo 1080619 5483213 := bstep (se 3 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 5483213 = 2056205) B2056205
theorem B1157923 : Blo 1080619 1157923 := bstep (se 1 (by rfl) ⟨868442, by rfl⟩ : syracuseStep 1157923 = 1736885) B1736885
theorem B4631345 : Blo 1080619 4631345 := bstep (se 2 (by rfl) ⟨1736754, by rfl⟩ : syracuseStep 4631345 = 3473509) B3473509
theorem B2435921 : Blo 1080619 2435921 := bstep (se 2 (by rfl) ⟨913470, by rfl⟩ : syracuseStep 2435921 = 1826941) B1826941
theorem B2435939 : Blo 1080619 2435939 := bstep (se 1 (by rfl) ⟨1826954, by rfl⟩ : syracuseStep 2435939 = 3653909) B3653909
theorem B3648401 : Blo 1080619 3648401 := bstep (se 2 (by rfl) ⟨1368150, by rfl⟩ : syracuseStep 3648401 = 2736301) B2736301
theorem B2436209 : Blo 1080619 2436209 := bstep (se 2 (by rfl) ⟨913578, by rfl⟩ : syracuseStep 2436209 = 1827157) B1827157
theorem B2436227 : Blo 1080619 2436227 := bstep (se 1 (by rfl) ⟨1827170, by rfl⟩ : syracuseStep 2436227 = 3654341) B3654341
theorem B6925445 : Blo 1080619 6925445 := bstep (se 4 (by rfl) ⟨649260, by rfl⟩ : syracuseStep 6925445 = 1298521) B1298521
theorem B6171875 : Blo 1080619 6171875 := bstep (se 1 (by rfl) ⟨4628906, by rfl⟩ : syracuseStep 6171875 = 9257813) B9257813
theorem B1158419 : Blo 1080619 1158419 := bstep (se 1 (by rfl) ⟨868814, by rfl⟩ : syracuseStep 1158419 = 1737629) B1737629
theorem B7810445 : Blo 1080619 7810445 := bstep (se 3 (by rfl) ⟨1464458, by rfl⟩ : syracuseStep 7810445 = 2928917) B2928917
theorem B2436497 : Blo 1080619 2436497 := bstep (se 2 (by rfl) ⟨913686, by rfl⟩ : syracuseStep 2436497 = 1827373) B1827373
theorem B2436515 : Blo 1080619 2436515 := bstep (se 1 (by rfl) ⟨1827386, by rfl⟩ : syracuseStep 2436515 = 3654773) B3654773
theorem B3648941 : Blo 1080619 3648941 := bstep (se 3 (by rfl) ⟨684176, by rfl⟩ : syracuseStep 3648941 = 1368353) B1368353
theorem B2600387 : Blo 1080619 2600387 := bstep (se 1 (by rfl) ⟨1950290, by rfl⟩ : syracuseStep 2600387 = 3900581) B3900581
theorem B3648995 : Blo 1080619 3648995 := bstep (se 1 (by rfl) ⟨2736746, by rfl⟩ : syracuseStep 3648995 = 5473493) B5473493
theorem B2600579 : Blo 1080619 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B2436785 : Blo 1080619 2436785 := bstep (se 2 (by rfl) ⟨913794, by rfl⟩ : syracuseStep 2436785 = 1827589) B1827589
theorem B2436803 : Blo 1080619 2436803 := bstep (se 1 (by rfl) ⟨1827602, by rfl⟩ : syracuseStep 2436803 = 3655205) B3655205
theorem B3649265 : Blo 1080619 3649265 := bstep (se 2 (by rfl) ⟨1368474, by rfl⟩ : syracuseStep 3649265 = 2736949) B2736949
theorem B4108067 : Blo 1080619 4108067 := bstep (se 1 (by rfl) ⟨3081050, by rfl⟩ : syracuseStep 4108067 = 6162101) B6162101
theorem B4632461 : Blo 1080619 4632461 := bstep (se 3 (by rfl) ⟨868586, by rfl⟩ : syracuseStep 4632461 = 1737173) B1737173
theorem B2600867 : Blo 1080619 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B2437073 : Blo 1080619 2437073 := bstep (se 2 (by rfl) ⟨913902, by rfl⟩ : syracuseStep 2437073 = 1827805) B1827805
theorem B2437091 : Blo 1080619 2437091 := bstep (se 1 (by rfl) ⟨1827818, by rfl⟩ : syracuseStep 2437091 = 3655637) B3655637
theorem B9253061 : Blo 1080619 9253061 := bstep (se 4 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 9253061 = 1734949) B1734949
theorem B2437361 : Blo 1080619 2437361 := bstep (se 2 (by rfl) ⟨914010, by rfl⟩ : syracuseStep 2437361 = 1828021) B1828021
theorem B2437379 : Blo 1080619 2437379 := bstep (se 1 (by rfl) ⟨1828034, by rfl⟩ : syracuseStep 2437379 = 3656069) B3656069
theorem B3649805 : Blo 1080619 3649805 := bstep (se 3 (by rfl) ⟨684338, by rfl⟩ : syracuseStep 3649805 = 1368677) B1368677
theorem B3649859 : Blo 1080619 3649859 := bstep (se 1 (by rfl) ⟨2737394, by rfl⟩ : syracuseStep 3649859 = 5474789) B5474789
theorem B8335685 : Blo 1080619 8335685 := bstep (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) B1562941
theorem B2437649 : Blo 1080619 2437649 := bstep (se 2 (by rfl) ⟨914118, by rfl⟩ : syracuseStep 2437649 = 1828237) B1828237
theorem B2437667 : Blo 1080619 2437667 := bstep (se 1 (by rfl) ⟨1828250, by rfl⟩ : syracuseStep 2437667 = 3656501) B3656501
theorem B3650129 : Blo 1080619 3650129 := bstep (se 2 (by rfl) ⟨1368798, by rfl⟩ : syracuseStep 3650129 = 2737597) B2737597
theorem B4109069 : Blo 1080619 4109069 := bstep (se 3 (by rfl) ⟨770450, by rfl⟩ : syracuseStep 4109069 = 1540901) B1540901
theorem B2437937 : Blo 1080619 2437937 := bstep (se 2 (by rfl) ⟨914226, by rfl⟩ : syracuseStep 2437937 = 1828453) B1828453
theorem B2437955 : Blo 1080619 2437955 := bstep (se 1 (by rfl) ⟨1828466, by rfl⟩ : syracuseStep 2437955 = 3656933) B3656933
theorem B2601809 : Blo 1080619 2601809 := bstep (se 2 (by rfl) ⟨975678, by rfl⟩ : syracuseStep 2601809 = 1951357) B1951357
theorem B3289997 : Blo 1080619 3289997 := bstep (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) B1233749
theorem B2470883 : Blo 1080619 2470883 := bstep (se 1 (by rfl) ⟨1853162, by rfl⟩ : syracuseStep 2470883 = 3706325) B3706325
theorem B1586161 : Blo 1080619 1586161 := bstep (se 2 (by rfl) ⟨594810, by rfl⟩ : syracuseStep 1586161 = 1189621) B1189621
theorem B6173765 : Blo 1080619 6173765 := bstep (se 4 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 6173765 = 1157581) B1157581
theorem B2438225 : Blo 1080619 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B2438243 : Blo 1080619 2438243 := bstep (se 1 (by rfl) ⟨1828682, by rfl⟩ : syracuseStep 2438243 = 3657365) B3657365
theorem B3650669 : Blo 1080619 3650669 := bstep (se 3 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 3650669 = 1369001) B1369001
theorem B8795249 : Blo 1080619 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B3650723 : Blo 1080619 3650723 := bstep (se 1 (by rfl) ⟨2738042, by rfl⟩ : syracuseStep 3650723 = 5476085) B5476085
theorem B3519683 : Blo 1080619 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B2438513 : Blo 1080619 2438513 := bstep (se 2 (by rfl) ⟨914442, by rfl⟩ : syracuseStep 2438513 = 1828885) B1828885
theorem B2438531 : Blo 1080619 2438531 := bstep (se 1 (by rfl) ⟨1828898, by rfl⟩ : syracuseStep 2438531 = 3657797) B3657797
theorem B3650993 : Blo 1080619 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B5486129 : Blo 1080619 5486129 := bstep (se 2 (by rfl) ⟨2057298, by rfl⟩ : syracuseStep 5486129 = 4114597) B4114597
theorem B35599985 : Blo 1080619 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B2438801 : Blo 1080619 2438801 := bstep (se 2 (by rfl) ⟨914550, by rfl⟩ : syracuseStep 2438801 = 1829101) B1829101
theorem B2438819 : Blo 1080619 2438819 := bstep (se 1 (by rfl) ⟨1829114, by rfl⟩ : syracuseStep 2438819 = 3658229) B3658229
theorem B1390451 : Blo 1080619 1390451 := bstep (se 1 (by rfl) ⟨1042838, by rfl⟩ : syracuseStep 1390451 = 2085677) B2085677
theorem B2439089 : Blo 1080619 2439089 := bstep (se 2 (by rfl) ⟨914658, by rfl⟩ : syracuseStep 2439089 = 1829317) B1829317
theorem B2439107 : Blo 1080619 2439107 := bstep (se 1 (by rfl) ⟨1829330, by rfl⟩ : syracuseStep 2439107 = 3658661) B3658661
theorem B3651533 : Blo 1080619 3651533 := bstep (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) B1369325
theorem B3651587 : Blo 1080619 3651587 := bstep (se 1 (by rfl) ⟨2738690, by rfl⟩ : syracuseStep 3651587 = 5477381) B5477381
theorem B23410741 : Blo 1080619 23410741 := bstep (se 5 (by rfl) ⟨1097378, by rfl⟩ : syracuseStep 23410741 = 2194757) B2194757
theorem B2439377 : Blo 1080619 2439377 := bstep (se 2 (by rfl) ⟨914766, by rfl⟩ : syracuseStep 2439377 = 1829533) B1829533
theorem B16890083 : Blo 1080619 16890083 := bstep (se 1 (by rfl) ⟨12667562, by rfl⟩ : syracuseStep 16890083 = 25335125) B25335125
theorem B2439395 : Blo 1080619 2439395 := bstep (se 1 (by rfl) ⟨1829546, by rfl⟩ : syracuseStep 2439395 = 3659093) B3659093
theorem B3651857 : Blo 1080619 3651857 := bstep (se 2 (by rfl) ⟨1369446, by rfl⟩ : syracuseStep 3651857 = 2738893) B2738893
theorem B2439665 : Blo 1080619 2439665 := bstep (se 2 (by rfl) ⟨914874, by rfl⟩ : syracuseStep 2439665 = 1829749) B1829749
theorem B2439683 : Blo 1080619 2439683 := bstep (se 1 (by rfl) ⟨1829762, by rfl⟩ : syracuseStep 2439683 = 3659525) B3659525
theorem B2472497 : Blo 1080619 2472497 := bstep (se 2 (by rfl) ⟨927186, by rfl⟩ : syracuseStep 2472497 = 1854373) B1854373
theorem B2964035 : Blo 1080619 2964035 := bstep (se 1 (by rfl) ⟨2223026, by rfl⟩ : syracuseStep 2964035 = 4446053) B4446053
theorem B6929009 : Blo 1080619 6929009 := bstep (se 2 (by rfl) ⟨2598378, by rfl⟩ : syracuseStep 6929009 = 5196757) B5196757
theorem B13187765 : Blo 1080619 13187765 := bstep (se 5 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 13187765 = 1236353) B1236353
theorem B1948387 : Blo 1080619 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B2439953 : Blo 1080619 2439953 := bstep (se 2 (by rfl) ⟨914982, by rfl⟩ : syracuseStep 2439953 = 1829965) B1829965
theorem B2439971 : Blo 1080619 2439971 := bstep (se 1 (by rfl) ⟨1829978, by rfl⟩ : syracuseStep 2439971 = 3659957) B3659957
theorem B3652397 : Blo 1080619 3652397 := bstep (se 3 (by rfl) ⟨684824, by rfl⟩ : syracuseStep 3652397 = 1369649) B1369649
theorem B4111181 : Blo 1080619 4111181 := bstep (se 3 (by rfl) ⟨770846, by rfl⟩ : syracuseStep 4111181 = 1541693) B1541693
theorem B3652451 : Blo 1080619 3652451 := bstep (se 1 (by rfl) ⟨2739338, by rfl⟩ : syracuseStep 3652451 = 5478677) B5478677
theorem B3750787 : Blo 1080619 3750787 := bstep (se 1 (by rfl) ⟨2813090, by rfl⟩ : syracuseStep 3750787 = 5626181) B5626181
theorem B1620929 : Blo 1080619 1620929 := bstep (se 2 (by rfl) ⟨607848, by rfl⟩ : syracuseStep 1620929 = 1215697) B1215697
theorem B1620947 : Blo 1080619 1620947 := bstep (se 1 (by rfl) ⟨1215710, by rfl⟩ : syracuseStep 1620947 = 2431421) B2431421
theorem B5487587 : Blo 1080619 5487587 := bstep (se 1 (by rfl) ⟨4115690, by rfl⟩ : syracuseStep 5487587 = 8231381) B8231381
theorem B1620977 : Blo 1080619 1620977 := bstep (se 2 (by rfl) ⟨607866, by rfl⟩ : syracuseStep 1620977 = 1215733) B1215733
theorem B1620995 : Blo 1080619 1620995 := bstep (se 1 (by rfl) ⟨1215746, by rfl⟩ : syracuseStep 1620995 = 2431493) B2431493
theorem B2309123 : Blo 1080619 2309123 := bstep (se 1 (by rfl) ⟨1731842, by rfl⟩ : syracuseStep 2309123 = 3463685) B3463685
theorem B1784849 : Blo 1080619 1784849 := bstep (se 2 (by rfl) ⟨669318, by rfl⟩ : syracuseStep 1784849 = 1338637) B1338637
theorem B1621025 : Blo 1080619 1621025 := bstep (se 2 (by rfl) ⟨607884, by rfl⟩ : syracuseStep 1621025 = 1215769) B1215769
theorem B2440241 : Blo 1080619 2440241 := bstep (se 2 (by rfl) ⟨915090, by rfl⟩ : syracuseStep 2440241 = 1830181) B1830181
theorem B1621043 : Blo 1080619 1621043 := bstep (se 1 (by rfl) ⟨1215782, by rfl⟩ : syracuseStep 1621043 = 2431565) B2431565
theorem B2440259 : Blo 1080619 2440259 := bstep (se 1 (by rfl) ⟨1830194, by rfl⟩ : syracuseStep 2440259 = 3660389) B3660389
theorem B1621073 : Blo 1080619 1621073 := bstep (se 2 (by rfl) ⟨607902, by rfl⟩ : syracuseStep 1621073 = 1215805) B1215805
theorem B1621091 : Blo 1080619 1621091 := bstep (se 1 (by rfl) ⟨1215818, by rfl⟩ : syracuseStep 1621091 = 2431637) B2431637
theorem B3652721 : Blo 1080619 3652721 := bstep (se 2 (by rfl) ⟨1369770, by rfl⟩ : syracuseStep 3652721 = 2739541) B2739541
theorem B1621121 : Blo 1080619 1621121 := bstep (se 2 (by rfl) ⟨607920, by rfl⟩ : syracuseStep 1621121 = 1215841) B1215841
theorem B1621139 : Blo 1080619 1621139 := bstep (se 1 (by rfl) ⟨1215854, by rfl⟩ : syracuseStep 1621139 = 2431709) B2431709
theorem B1621169 : Blo 1080619 1621169 := bstep (se 2 (by rfl) ⟨607938, by rfl⟩ : syracuseStep 1621169 = 1215877) B1215877
theorem B1621187 : Blo 1080619 1621187 := bstep (se 1 (by rfl) ⟨1215890, by rfl⟩ : syracuseStep 1621187 = 2431781) B2431781
theorem B1621217 : Blo 1080619 1621217 := bstep (se 2 (by rfl) ⟨607956, by rfl⟩ : syracuseStep 1621217 = 1215913) B1215913
theorem B1621235 : Blo 1080619 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B1621265 : Blo 1080619 1621265 := bstep (se 2 (by rfl) ⟨607974, by rfl⟩ : syracuseStep 1621265 = 1215949) B1215949
theorem B1621283 : Blo 1080619 1621283 := bstep (se 1 (by rfl) ⟨1215962, by rfl⟩ : syracuseStep 1621283 = 2431925) B2431925
theorem B1621313 : Blo 1080619 1621313 := bstep (se 2 (by rfl) ⟨607992, by rfl⟩ : syracuseStep 1621313 = 1215985) B1215985
theorem B2735441 : Blo 1080619 2735441 := bstep (se 2 (by rfl) ⟨1025790, by rfl⟩ : syracuseStep 2735441 = 2051581) B2051581
theorem B1621331 : Blo 1080619 1621331 := bstep (se 1 (by rfl) ⟨1215998, by rfl⟩ : syracuseStep 1621331 = 2431997) B2431997
theorem B1621361 : Blo 1080619 1621361 := bstep (se 2 (by rfl) ⟨608010, by rfl⟩ : syracuseStep 1621361 = 1216021) B1216021
theorem B2735491 : Blo 1080619 2735491 := bstep (se 1 (by rfl) ⟨2051618, by rfl⟩ : syracuseStep 2735491 = 4103237) B4103237
theorem B1621379 : Blo 1080619 1621379 := bstep (se 1 (by rfl) ⟨1216034, by rfl⟩ : syracuseStep 1621379 = 2432069) B2432069
theorem B1621409 : Blo 1080619 1621409 := bstep (se 2 (by rfl) ⟨608028, by rfl⟩ : syracuseStep 1621409 = 1216057) B1216057
theorem B1621427 : Blo 1080619 1621427 := bstep (se 1 (by rfl) ⟨1216070, by rfl⟩ : syracuseStep 1621427 = 2432141) B2432141
theorem B1621457 : Blo 1080619 1621457 := bstep (se 2 (by rfl) ⟨608046, by rfl⟩ : syracuseStep 1621457 = 1216093) B1216093
theorem B1621475 : Blo 1080619 1621475 := bstep (se 1 (by rfl) ⟨1216106, by rfl⟩ : syracuseStep 1621475 = 2432213) B2432213
theorem B1621505 : Blo 1080619 1621505 := bstep (se 2 (by rfl) ⟨608064, by rfl⟩ : syracuseStep 1621505 = 1216129) B1216129
theorem B2735633 : Blo 1080619 2735633 := bstep (se 2 (by rfl) ⟨1025862, by rfl⟩ : syracuseStep 2735633 = 2051725) B2051725
theorem B1621523 : Blo 1080619 1621523 := bstep (se 1 (by rfl) ⟨1216142, by rfl⟩ : syracuseStep 1621523 = 2432285) B2432285
theorem B1621553 : Blo 1080619 1621553 := bstep (se 2 (by rfl) ⟨608082, by rfl⟩ : syracuseStep 1621553 = 1216165) B1216165
theorem B1621571 : Blo 1080619 1621571 := bstep (se 1 (by rfl) ⟨1216178, by rfl⟩ : syracuseStep 1621571 = 2432357) B2432357
theorem B1621601 : Blo 1080619 1621601 := bstep (se 2 (by rfl) ⟨608100, by rfl⟩ : syracuseStep 1621601 = 1216201) B1216201
theorem B4111985 : Blo 1080619 4111985 := bstep (se 2 (by rfl) ⟨1541994, by rfl⟩ : syracuseStep 4111985 = 3083989) B3083989
theorem B1621619 : Blo 1080619 1621619 := bstep (se 1 (by rfl) ⟨1216214, by rfl⟩ : syracuseStep 1621619 = 2432429) B2432429
theorem B3653261 : Blo 1080619 3653261 := bstep (se 3 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 3653261 = 1369973) B1369973
theorem B1621649 : Blo 1080619 1621649 := bstep (se 2 (by rfl) ⟨608118, by rfl⟩ : syracuseStep 1621649 = 1216237) B1216237
theorem B1621667 : Blo 1080619 1621667 := bstep (se 1 (by rfl) ⟨1216250, by rfl⟩ : syracuseStep 1621667 = 2432501) B2432501
theorem B1621697 : Blo 1080619 1621697 := bstep (se 2 (by rfl) ⟨608136, by rfl⟩ : syracuseStep 1621697 = 1216273) B1216273
theorem B3653315 : Blo 1080619 3653315 := bstep (se 1 (by rfl) ⟨2739986, by rfl⟩ : syracuseStep 3653315 = 5479973) B5479973
theorem B1621715 : Blo 1080619 1621715 := bstep (se 1 (by rfl) ⟨1216286, by rfl⟩ : syracuseStep 1621715 = 2432573) B2432573
theorem B1621745 : Blo 1080619 1621745 := bstep (se 2 (by rfl) ⟨608154, by rfl⟩ : syracuseStep 1621745 = 1216309) B1216309
theorem B1621763 : Blo 1080619 1621763 := bstep (se 1 (by rfl) ⟨1216322, by rfl⟩ : syracuseStep 1621763 = 2432645) B2432645
theorem B5488397 : Blo 1080619 5488397 := bstep (se 3 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 5488397 = 2058149) B2058149
theorem B1621793 : Blo 1080619 1621793 := bstep (se 2 (by rfl) ⟨608172, by rfl⟩ : syracuseStep 1621793 = 1216345) B1216345
theorem B1621811 : Blo 1080619 1621811 := bstep (se 1 (by rfl) ⟨1216358, by rfl⟩ : syracuseStep 1621811 = 2432717) B2432717
theorem B1621841 : Blo 1080619 1621841 := bstep (se 2 (by rfl) ⟨608190, by rfl⟩ : syracuseStep 1621841 = 1216381) B1216381
theorem B1621859 : Blo 1080619 1621859 := bstep (se 1 (by rfl) ⟨1216394, by rfl⟩ : syracuseStep 1621859 = 2432789) B2432789
theorem B13188977 : Blo 1080619 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B1621889 : Blo 1080619 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B1621907 : Blo 1080619 1621907 := bstep (se 1 (by rfl) ⟨1216430, by rfl⟩ : syracuseStep 1621907 = 2432861) B2432861
theorem B1621937 : Blo 1080619 1621937 := bstep (se 2 (by rfl) ⟨608226, by rfl⟩ : syracuseStep 1621937 = 1216453) B1216453
theorem B1621955 : Blo 1080619 1621955 := bstep (se 1 (by rfl) ⟨1216466, by rfl⟩ : syracuseStep 1621955 = 2432933) B2432933
theorem B3653585 : Blo 1080619 3653585 := bstep (se 2 (by rfl) ⟨1370094, by rfl⟩ : syracuseStep 3653585 = 2740189) B2740189
theorem B1621985 : Blo 1080619 1621985 := bstep (se 2 (by rfl) ⟨608244, by rfl⟩ : syracuseStep 1621985 = 1216489) B1216489
theorem B1622003 : Blo 1080619 1622003 := bstep (se 1 (by rfl) ⟨1216502, by rfl⟩ : syracuseStep 1622003 = 2433005) B2433005
theorem B1622033 : Blo 1080619 1622033 := bstep (se 2 (by rfl) ⟨608262, by rfl⟩ : syracuseStep 1622033 = 1216525) B1216525
theorem B1622051 : Blo 1080619 1622051 := bstep (se 1 (by rfl) ⟨1216538, by rfl⟩ : syracuseStep 1622051 = 2433077) B2433077
theorem B6930467 : Blo 1080619 6930467 := bstep (se 1 (by rfl) ⟨5197850, by rfl⟩ : syracuseStep 6930467 = 10395701) B10395701
theorem B1622081 : Blo 1080619 1622081 := bstep (se 2 (by rfl) ⟨608280, by rfl⟩ : syracuseStep 1622081 = 1216561) B1216561
theorem B1622099 : Blo 1080619 1622099 := bstep (se 1 (by rfl) ⟨1216574, by rfl⟩ : syracuseStep 1622099 = 2433149) B2433149
theorem B1622129 : Blo 1080619 1622129 := bstep (se 2 (by rfl) ⟨608298, by rfl⟩ : syracuseStep 1622129 = 1216597) B1216597
theorem B1622147 : Blo 1080619 1622147 := bstep (se 1 (by rfl) ⟨1216610, by rfl⟩ : syracuseStep 1622147 = 2433221) B2433221
theorem B1622177 : Blo 1080619 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B1622195 : Blo 1080619 1622195 := bstep (se 1 (by rfl) ⟨1216646, by rfl⟩ : syracuseStep 1622195 = 2433293) B2433293
theorem B1622225 : Blo 1080619 1622225 := bstep (se 2 (by rfl) ⟨608334, by rfl⟩ : syracuseStep 1622225 = 1216669) B1216669
theorem B2310353 : Blo 1080619 2310353 := bstep (se 2 (by rfl) ⟨866382, by rfl⟩ : syracuseStep 2310353 = 1732765) B1732765
theorem B1622243 : Blo 1080619 1622243 := bstep (se 1 (by rfl) ⟨1216682, by rfl⟩ : syracuseStep 1622243 = 2433365) B2433365
theorem B1622273 : Blo 1080619 1622273 := bstep (se 2 (by rfl) ⟨608352, by rfl⟩ : syracuseStep 1622273 = 1216705) B1216705
theorem B4112653 : Blo 1080619 4112653 := bstep (se 3 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 4112653 = 1542245) B1542245
theorem B1622291 : Blo 1080619 1622291 := bstep (se 1 (by rfl) ⟨1216718, by rfl⟩ : syracuseStep 1622291 = 2433437) B2433437
theorem B1622321 : Blo 1080619 1622321 := bstep (se 2 (by rfl) ⟨608370, by rfl⟩ : syracuseStep 1622321 = 1216741) B1216741
theorem B1950001 : Blo 1080619 1950001 := bstep (se 2 (by rfl) ⟨731250, by rfl⟩ : syracuseStep 1950001 = 1462501) B1462501
theorem B1622339 : Blo 1080619 1622339 := bstep (se 1 (by rfl) ⟨1216754, by rfl⟩ : syracuseStep 1622339 = 2433509) B2433509
theorem B1622369 : Blo 1080619 1622369 := bstep (se 2 (by rfl) ⟨608388, by rfl⟩ : syracuseStep 1622369 = 1216777) B1216777
theorem B1622387 : Blo 1080619 1622387 := bstep (se 1 (by rfl) ⟨1216790, by rfl⟩ : syracuseStep 1622387 = 2433581) B2433581
theorem B1622417 : Blo 1080619 1622417 := bstep (se 2 (by rfl) ⟨608406, by rfl⟩ : syracuseStep 1622417 = 1216813) B1216813
theorem B1622435 : Blo 1080619 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B1622465 : Blo 1080619 1622465 := bstep (se 2 (by rfl) ⟨608424, by rfl⟩ : syracuseStep 1622465 = 1216849) B1216849
theorem B1622483 : Blo 1080619 1622483 := bstep (se 1 (by rfl) ⟨1216862, by rfl⟩ : syracuseStep 1622483 = 2433725) B2433725
theorem B3654125 : Blo 1080619 3654125 := bstep (se 3 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 3654125 = 1370297) B1370297
theorem B2736625 : Blo 1080619 2736625 := bstep (se 2 (by rfl) ⟨1026234, by rfl⟩ : syracuseStep 2736625 = 2052469) B2052469
theorem B1622513 : Blo 1080619 1622513 := bstep (se 2 (by rfl) ⟨608442, by rfl⟩ : syracuseStep 1622513 = 1216885) B1216885
theorem B1622531 : Blo 1080619 1622531 := bstep (se 1 (by rfl) ⟨1216898, by rfl⟩ : syracuseStep 1622531 = 2433797) B2433797
theorem B1622561 : Blo 1080619 1622561 := bstep (se 2 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 1622561 = 1216921) B1216921
theorem B3654179 : Blo 1080619 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B3293741 : Blo 1080619 3293741 := bstep (se 3 (by rfl) ⟨617576, by rfl⟩ : syracuseStep 3293741 = 1235153) B1235153
theorem B1622579 : Blo 1080619 1622579 := bstep (se 1 (by rfl) ⟨1216934, by rfl⟩ : syracuseStep 1622579 = 2433869) B2433869
theorem B1622609 : Blo 1080619 1622609 := bstep (se 2 (by rfl) ⟨608478, by rfl⟩ : syracuseStep 1622609 = 1216957) B1216957
theorem B1622627 : Blo 1080619 1622627 := bstep (se 1 (by rfl) ⟨1216970, by rfl⟩ : syracuseStep 1622627 = 2433941) B2433941
theorem B1622657 : Blo 1080619 1622657 := bstep (se 2 (by rfl) ⟨608496, by rfl⟩ : syracuseStep 1622657 = 1216993) B1216993
theorem B3293827 : Blo 1080619 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B1622675 : Blo 1080619 1622675 := bstep (se 1 (by rfl) ⟨1217006, by rfl⟩ : syracuseStep 1622675 = 2434013) B2434013
theorem B6242993 : Blo 1080619 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B1622705 : Blo 1080619 1622705 := bstep (se 2 (by rfl) ⟨608514, by rfl⟩ : syracuseStep 1622705 = 1217029) B1217029
theorem B1622723 : Blo 1080619 1622723 := bstep (se 1 (by rfl) ⟨1217042, by rfl⟩ : syracuseStep 1622723 = 2434085) B2434085
theorem B1622753 : Blo 1080619 1622753 := bstep (se 2 (by rfl) ⟨608532, by rfl⟩ : syracuseStep 1622753 = 1217065) B1217065
theorem B1622771 : Blo 1080619 1622771 := bstep (se 1 (by rfl) ⟨1217078, by rfl⟩ : syracuseStep 1622771 = 2434157) B2434157
theorem B2736899 : Blo 1080619 2736899 := bstep (se 1 (by rfl) ⟨2052674, by rfl⟩ : syracuseStep 2736899 = 4105349) B4105349
theorem B1622801 : Blo 1080619 1622801 := bstep (se 2 (by rfl) ⟨608550, by rfl⟩ : syracuseStep 1622801 = 1217101) B1217101
theorem B1622819 : Blo 1080619 1622819 := bstep (se 1 (by rfl) ⟨1217114, by rfl⟩ : syracuseStep 1622819 = 2434229) B2434229
theorem B3654449 : Blo 1080619 3654449 := bstep (se 2 (by rfl) ⟨1370418, by rfl⟩ : syracuseStep 3654449 = 2740837) B2740837
theorem B1622849 : Blo 1080619 1622849 := bstep (se 2 (by rfl) ⟨608568, by rfl⟩ : syracuseStep 1622849 = 1217137) B1217137
theorem B1622867 : Blo 1080619 1622867 := bstep (se 1 (by rfl) ⟨1217150, by rfl⟩ : syracuseStep 1622867 = 2434301) B2434301
theorem B1622897 : Blo 1080619 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B1622915 : Blo 1080619 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B1622945 : Blo 1080619 1622945 := bstep (se 2 (by rfl) ⟨608604, by rfl⟩ : syracuseStep 1622945 = 1217209) B1217209
theorem B1622963 : Blo 1080619 1622963 := bstep (se 1 (by rfl) ⟨1217222, by rfl⟩ : syracuseStep 1622963 = 2434445) B2434445
theorem B2737091 : Blo 1080619 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B1622993 : Blo 1080619 1622993 := bstep (se 2 (by rfl) ⟨608622, by rfl⟩ : syracuseStep 1622993 = 1217245) B1217245
theorem B1623011 : Blo 1080619 1623011 := bstep (se 1 (by rfl) ⟨1217258, by rfl⟩ : syracuseStep 1623011 = 2434517) B2434517
theorem B1623041 : Blo 1080619 1623041 := bstep (se 2 (by rfl) ⟨608640, by rfl⟩ : syracuseStep 1623041 = 1217281) B1217281
theorem B1623059 : Blo 1080619 1623059 := bstep (se 1 (by rfl) ⟨1217294, by rfl⟩ : syracuseStep 1623059 = 2434589) B2434589
theorem B4113443 : Blo 1080619 4113443 := bstep (se 1 (by rfl) ⟨3085082, by rfl⟩ : syracuseStep 4113443 = 6170165) B6170165
theorem B1623089 : Blo 1080619 1623089 := bstep (se 2 (by rfl) ⟨608658, by rfl⟩ : syracuseStep 1623089 = 1217317) B1217317
theorem B1623107 : Blo 1080619 1623107 := bstep (se 1 (by rfl) ⟨1217330, by rfl⟩ : syracuseStep 1623107 = 2434661) B2434661
theorem B2311249 : Blo 1080619 2311249 := bstep (se 2 (by rfl) ⟨866718, by rfl⟩ : syracuseStep 2311249 = 1733437) B1733437
theorem B1623137 : Blo 1080619 1623137 := bstep (se 2 (by rfl) ⟨608676, by rfl⟩ : syracuseStep 1623137 = 1217353) B1217353
theorem B2311267 : Blo 1080619 2311267 := bstep (se 1 (by rfl) ⟨1733450, by rfl⟩ : syracuseStep 2311267 = 3466901) B3466901
theorem B1098851 : Blo 1080619 1098851 := bstep (se 1 (by rfl) ⟨824138, by rfl⟩ : syracuseStep 1098851 = 1648277) B1648277
theorem B63292529 : Blo 1080619 63292529 := bstep (se 2 (by rfl) ⟨23734698, by rfl⟩ : syracuseStep 63292529 = 47469397) B47469397
theorem B1623155 : Blo 1080619 1623155 := bstep (se 1 (by rfl) ⟨1217366, by rfl⟩ : syracuseStep 1623155 = 2434733) B2434733
theorem B1623185 : Blo 1080619 1623185 := bstep (se 2 (by rfl) ⟨608694, by rfl⟩ : syracuseStep 1623185 = 1217389) B1217389
theorem B1623203 : Blo 1080619 1623203 := bstep (se 1 (by rfl) ⟨1217402, by rfl⟩ : syracuseStep 1623203 = 2434805) B2434805
theorem B1623233 : Blo 1080619 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B1623251 : Blo 1080619 1623251 := bstep (se 1 (by rfl) ⟨1217438, by rfl⟩ : syracuseStep 1623251 = 2434877) B2434877
theorem B1623281 : Blo 1080619 1623281 := bstep (se 2 (by rfl) ⟨608730, by rfl⟩ : syracuseStep 1623281 = 1217461) B1217461
theorem B1623299 : Blo 1080619 1623299 := bstep (se 1 (by rfl) ⟨1217474, by rfl⟩ : syracuseStep 1623299 = 2434949) B2434949
theorem B1623329 : Blo 1080619 1623329 := bstep (se 2 (by rfl) ⟨608748, by rfl⟩ : syracuseStep 1623329 = 1217497) B1217497
theorem B3851569 : Blo 1080619 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B1623347 : Blo 1080619 1623347 := bstep (se 1 (by rfl) ⟨1217510, by rfl⟩ : syracuseStep 1623347 = 2435021) B2435021
theorem B3654989 : Blo 1080619 3654989 := bstep (se 3 (by rfl) ⟨685310, by rfl⟩ : syracuseStep 3654989 = 1370621) B1370621
theorem B1623377 : Blo 1080619 1623377 := bstep (se 2 (by rfl) ⟨608766, by rfl⟩ : syracuseStep 1623377 = 1217533) B1217533
theorem B1623395 : Blo 1080619 1623395 := bstep (se 1 (by rfl) ⟨1217546, by rfl⟩ : syracuseStep 1623395 = 2435093) B2435093
theorem B1623425 : Blo 1080619 1623425 := bstep (se 2 (by rfl) ⟨608784, by rfl⟩ : syracuseStep 1623425 = 1217569) B1217569
theorem B3655043 : Blo 1080619 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B1623443 : Blo 1080619 1623443 := bstep (se 1 (by rfl) ⟨1217582, by rfl⟩ : syracuseStep 1623443 = 2435165) B2435165
theorem B1623473 : Blo 1080619 1623473 := bstep (se 2 (by rfl) ⟨608802, by rfl⟩ : syracuseStep 1623473 = 1217605) B1217605
theorem B1623491 : Blo 1080619 1623491 := bstep (se 1 (by rfl) ⟨1217618, by rfl⟩ : syracuseStep 1623491 = 2435237) B2435237
theorem B1623521 : Blo 1080619 1623521 := bstep (se 2 (by rfl) ⟨608820, by rfl⟩ : syracuseStep 1623521 = 1217641) B1217641
theorem B1623539 : Blo 1080619 1623539 := bstep (se 1 (by rfl) ⟨1217654, by rfl⟩ : syracuseStep 1623539 = 2435309) B2435309
theorem B1623569 : Blo 1080619 1623569 := bstep (se 2 (by rfl) ⟨608838, by rfl⟩ : syracuseStep 1623569 = 1217677) B1217677
theorem B1623587 : Blo 1080619 1623587 := bstep (se 1 (by rfl) ⟨1217690, by rfl⟩ : syracuseStep 1623587 = 2435381) B2435381
theorem B4933169 : Blo 1080619 4933169 := bstep (se 2 (by rfl) ⟨1849938, by rfl⟩ : syracuseStep 4933169 = 3699877) B3699877
theorem B1623617 : Blo 1080619 1623617 := bstep (se 2 (by rfl) ⟨608856, by rfl⟩ : syracuseStep 1623617 = 1217713) B1217713
theorem B1623635 : Blo 1080619 1623635 := bstep (se 1 (by rfl) ⟨1217726, by rfl⟩ : syracuseStep 1623635 = 2435453) B2435453
theorem B1623665 : Blo 1080619 1623665 := bstep (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) B1217749
theorem B7816817 : Blo 1080619 7816817 := bstep (se 2 (by rfl) ⟨2931306, by rfl⟩ : syracuseStep 7816817 = 5862613) B5862613
theorem B1623683 : Blo 1080619 1623683 := bstep (se 1 (by rfl) ⟨1217762, by rfl⟩ : syracuseStep 1623683 = 2435525) B2435525
theorem B3655313 : Blo 1080619 3655313 := bstep (se 2 (by rfl) ⟨1370742, by rfl⟩ : syracuseStep 3655313 = 2741485) B2741485
theorem B1623713 : Blo 1080619 1623713 := bstep (se 2 (by rfl) ⟨608892, by rfl⟩ : syracuseStep 1623713 = 1217785) B1217785
theorem B4114097 : Blo 1080619 4114097 := bstep (se 2 (by rfl) ⟨1542786, by rfl⟩ : syracuseStep 4114097 = 3085573) B3085573
theorem B1623731 : Blo 1080619 1623731 := bstep (se 1 (by rfl) ⟨1217798, by rfl⟩ : syracuseStep 1623731 = 2435597) B2435597
theorem B1623761 : Blo 1080619 1623761 := bstep (se 2 (by rfl) ⟨608910, by rfl⟩ : syracuseStep 1623761 = 1217821) B1217821
theorem B1623779 : Blo 1080619 1623779 := bstep (se 1 (by rfl) ⟨1217834, by rfl⟩ : syracuseStep 1623779 = 2435669) B2435669
theorem B1623809 : Blo 1080619 1623809 := bstep (se 2 (by rfl) ⟨608928, by rfl⟩ : syracuseStep 1623809 = 1217857) B1217857
theorem B1623827 : Blo 1080619 1623827 := bstep (se 1 (by rfl) ⟨1217870, by rfl⟩ : syracuseStep 1623827 = 2435741) B2435741
theorem B1623857 : Blo 1080619 1623857 := bstep (se 2 (by rfl) ⟨608946, by rfl⟩ : syracuseStep 1623857 = 1217893) B1217893
theorem B14042933 : Blo 1080619 14042933 := bstep (se 5 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 14042933 = 1316525) B1316525
theorem B1623875 : Blo 1080619 1623875 := bstep (se 1 (by rfl) ⟨1217906, by rfl⟩ : syracuseStep 1623875 = 2435813) B2435813
theorem B1623905 : Blo 1080619 1623905 := bstep (se 2 (by rfl) ⟨608964, by rfl⟩ : syracuseStep 1623905 = 1217929) B1217929
theorem B2738033 : Blo 1080619 2738033 := bstep (se 2 (by rfl) ⟨1026762, by rfl⟩ : syracuseStep 2738033 = 2053525) B2053525
theorem B1623923 : Blo 1080619 1623923 := bstep (se 1 (by rfl) ⟨1217942, by rfl⟩ : syracuseStep 1623923 = 2435885) B2435885
theorem B1623953 : Blo 1080619 1623953 := bstep (se 2 (by rfl) ⟨608982, by rfl⟩ : syracuseStep 1623953 = 1217965) B1217965
theorem B2738083 : Blo 1080619 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B1623971 : Blo 1080619 1623971 := bstep (se 1 (by rfl) ⟨1217978, by rfl⟩ : syracuseStep 1623971 = 2435957) B2435957
theorem B1624001 : Blo 1080619 1624001 := bstep (se 2 (by rfl) ⟨609000, by rfl⟩ : syracuseStep 1624001 = 1218001) B1218001
theorem B1624019 : Blo 1080619 1624019 := bstep (se 1 (by rfl) ⟨1218014, by rfl⟩ : syracuseStep 1624019 = 2436029) B2436029
theorem B1624049 : Blo 1080619 1624049 := bstep (se 2 (by rfl) ⟨609018, by rfl⟩ : syracuseStep 1624049 = 1218037) B1218037
theorem B1624067 : Blo 1080619 1624067 := bstep (se 1 (by rfl) ⟨1218050, by rfl⟩ : syracuseStep 1624067 = 2436101) B2436101
theorem B1624097 : Blo 1080619 1624097 := bstep (se 2 (by rfl) ⟨609036, by rfl⟩ : syracuseStep 1624097 = 1218073) B1218073
theorem B2738225 : Blo 1080619 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B1624115 : Blo 1080619 1624115 := bstep (se 1 (by rfl) ⟨1218086, by rfl⟩ : syracuseStep 1624115 = 2436173) B2436173
theorem B1624145 : Blo 1080619 1624145 := bstep (se 2 (by rfl) ⟨609054, by rfl⟩ : syracuseStep 1624145 = 1218109) B1218109
theorem B1624163 : Blo 1080619 1624163 := bstep (se 1 (by rfl) ⟨1218122, by rfl⟩ : syracuseStep 1624163 = 2436245) B2436245
theorem B1624193 : Blo 1080619 1624193 := bstep (se 2 (by rfl) ⟨609072, by rfl⟩ : syracuseStep 1624193 = 1218145) B1218145
theorem B1624211 : Blo 1080619 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B3655853 : Blo 1080619 3655853 := bstep (se 3 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 3655853 = 1370945) B1370945
theorem B1624241 : Blo 1080619 1624241 := bstep (se 2 (by rfl) ⟨609090, by rfl⟩ : syracuseStep 1624241 = 1218181) B1218181
theorem B1624259 : Blo 1080619 1624259 := bstep (se 1 (by rfl) ⟨1218194, by rfl⟩ : syracuseStep 1624259 = 2436389) B2436389
theorem B1624289 : Blo 1080619 1624289 := bstep (se 2 (by rfl) ⟨609108, by rfl⟩ : syracuseStep 1624289 = 1218217) B1218217
theorem B3655907 : Blo 1080619 3655907 := bstep (se 1 (by rfl) ⟨2741930, by rfl⟩ : syracuseStep 3655907 = 5483861) B5483861
theorem B1624307 : Blo 1080619 1624307 := bstep (se 1 (by rfl) ⟨1218230, by rfl⟩ : syracuseStep 1624307 = 2436461) B2436461
theorem B1624337 : Blo 1080619 1624337 := bstep (se 2 (by rfl) ⟨609126, by rfl⟩ : syracuseStep 1624337 = 1218253) B1218253
theorem B1624355 : Blo 1080619 1624355 := bstep (se 1 (by rfl) ⟨1218266, by rfl⟩ : syracuseStep 1624355 = 2436533) B2436533
theorem B1624385 : Blo 1080619 1624385 := bstep (se 2 (by rfl) ⟨609144, by rfl⟩ : syracuseStep 1624385 = 1218289) B1218289
theorem B3557699 : Blo 1080619 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B1624403 : Blo 1080619 1624403 := bstep (se 1 (by rfl) ⟨1218302, by rfl⟩ : syracuseStep 1624403 = 2436605) B2436605
theorem B1624433 : Blo 1080619 1624433 := bstep (se 2 (by rfl) ⟨609162, by rfl⟩ : syracuseStep 1624433 = 1218325) B1218325
theorem B1624451 : Blo 1080619 1624451 := bstep (se 1 (by rfl) ⟨1218338, by rfl⟩ : syracuseStep 1624451 = 2436677) B2436677
theorem B1624481 : Blo 1080619 1624481 := bstep (se 2 (by rfl) ⟨609180, by rfl⟩ : syracuseStep 1624481 = 1218361) B1218361
theorem B1624499 : Blo 1080619 1624499 := bstep (se 1 (by rfl) ⟨1218374, by rfl⟩ : syracuseStep 1624499 = 2436749) B2436749
theorem B1624529 : Blo 1080619 1624529 := bstep (se 2 (by rfl) ⟨609198, by rfl⟩ : syracuseStep 1624529 = 1218397) B1218397
theorem B1624547 : Blo 1080619 1624547 := bstep (se 1 (by rfl) ⟨1218410, by rfl⟩ : syracuseStep 1624547 = 2436821) B2436821
theorem B3656177 : Blo 1080619 3656177 := bstep (se 2 (by rfl) ⟨1371066, by rfl⟩ : syracuseStep 3656177 = 2742133) B2742133
theorem B1624577 : Blo 1080619 1624577 := bstep (se 2 (by rfl) ⟨609216, by rfl⟩ : syracuseStep 1624577 = 1218433) B1218433
theorem B7817741 : Blo 1080619 7817741 := bstep (se 3 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 7817741 = 2931653) B2931653
theorem B1624595 : Blo 1080619 1624595 := bstep (se 1 (by rfl) ⟨1218446, by rfl⟩ : syracuseStep 1624595 = 2436893) B2436893
theorem B1624625 : Blo 1080619 1624625 := bstep (se 2 (by rfl) ⟨609234, by rfl⟩ : syracuseStep 1624625 = 1218469) B1218469
theorem B1624643 : Blo 1080619 1624643 := bstep (se 1 (by rfl) ⟨1218482, by rfl⟩ : syracuseStep 1624643 = 2436965) B2436965
theorem B1624673 : Blo 1080619 1624673 := bstep (se 2 (by rfl) ⟨609252, by rfl⟩ : syracuseStep 1624673 = 1218505) B1218505
theorem B1624691 : Blo 1080619 1624691 := bstep (se 1 (by rfl) ⟨1218518, by rfl⟩ : syracuseStep 1624691 = 2437037) B2437037
theorem B1624721 : Blo 1080619 1624721 := bstep (se 2 (by rfl) ⟨609270, by rfl⟩ : syracuseStep 1624721 = 1218541) B1218541
theorem B1624739 : Blo 1080619 1624739 := bstep (se 1 (by rfl) ⟨1218554, by rfl⟩ : syracuseStep 1624739 = 2437109) B2437109
theorem B1624769 : Blo 1080619 1624769 := bstep (se 2 (by rfl) ⟨609288, by rfl⟩ : syracuseStep 1624769 = 1218577) B1218577
theorem B1624787 : Blo 1080619 1624787 := bstep (se 1 (by rfl) ⟨1218590, by rfl⟩ : syracuseStep 1624787 = 2437181) B2437181
theorem B5851889 : Blo 1080619 5851889 := bstep (se 2 (by rfl) ⟨2194458, by rfl⟩ : syracuseStep 5851889 = 4388917) B4388917
theorem B1624817 : Blo 1080619 1624817 := bstep (se 2 (by rfl) ⟨609306, by rfl⟩ : syracuseStep 1624817 = 1218613) B1218613
theorem B1624835 : Blo 1080619 1624835 := bstep (se 1 (by rfl) ⟨1218626, by rfl⟩ : syracuseStep 1624835 = 2437253) B2437253
theorem B50088725 : Blo 1080619 50088725 := bstep (se 6 (by rfl) ⟨1173954, by rfl⟩ : syracuseStep 50088725 = 2347909) B2347909
theorem B1624865 : Blo 1080619 1624865 := bstep (se 2 (by rfl) ⟨609324, by rfl⟩ : syracuseStep 1624865 = 1218649) B1218649
theorem B1690417 : Blo 1080619 1690417 := bstep (se 2 (by rfl) ⟨633906, by rfl⟩ : syracuseStep 1690417 = 1267813) B1267813
theorem B1624883 : Blo 1080619 1624883 := bstep (se 1 (by rfl) ⟨1218662, by rfl⟩ : syracuseStep 1624883 = 2437325) B2437325
theorem B1624913 : Blo 1080619 1624913 := bstep (se 2 (by rfl) ⟨609342, by rfl⟩ : syracuseStep 1624913 = 1218685) B1218685
theorem B1624931 : Blo 1080619 1624931 := bstep (se 1 (by rfl) ⟨1218698, by rfl⟩ : syracuseStep 1624931 = 2437397) B2437397
theorem B1624961 : Blo 1080619 1624961 := bstep (se 2 (by rfl) ⟨609360, by rfl⟩ : syracuseStep 1624961 = 1218721) B1218721
theorem B1624979 : Blo 1080619 1624979 := bstep (se 1 (by rfl) ⟨1218734, by rfl⟩ : syracuseStep 1624979 = 2437469) B2437469
theorem B1625009 : Blo 1080619 1625009 := bstep (se 2 (by rfl) ⟨609378, by rfl⟩ : syracuseStep 1625009 = 1218757) B1218757
theorem B1625027 : Blo 1080619 1625027 := bstep (se 1 (by rfl) ⟨1218770, by rfl⟩ : syracuseStep 1625027 = 2437541) B2437541
theorem B1625057 : Blo 1080619 1625057 := bstep (se 2 (by rfl) ⟨609396, by rfl⟩ : syracuseStep 1625057 = 1218793) B1218793
theorem B1625075 : Blo 1080619 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B3656717 : Blo 1080619 3656717 := bstep (se 3 (by rfl) ⟨685634, by rfl⟩ : syracuseStep 3656717 = 1371269) B1371269
theorem B2739217 : Blo 1080619 2739217 := bstep (se 2 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 2739217 = 2054413) B2054413
theorem B1625105 : Blo 1080619 1625105 := bstep (se 2 (by rfl) ⟨609414, by rfl⟩ : syracuseStep 1625105 = 1218829) B1218829
theorem B1625123 : Blo 1080619 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B1625153 : Blo 1080619 1625153 := bstep (se 2 (by rfl) ⟨609432, by rfl⟩ : syracuseStep 1625153 = 1218865) B1218865
theorem B3656771 : Blo 1080619 3656771 := bstep (se 1 (by rfl) ⟨2742578, by rfl⟩ : syracuseStep 3656771 = 5485157) B5485157
theorem B1625171 : Blo 1080619 1625171 := bstep (se 1 (by rfl) ⟨1218878, by rfl⟩ : syracuseStep 1625171 = 2437757) B2437757
theorem B4115555 : Blo 1080619 4115555 := bstep (se 1 (by rfl) ⟨3086666, by rfl⟩ : syracuseStep 4115555 = 6173333) B6173333
theorem B1625201 : Blo 1080619 1625201 := bstep (se 2 (by rfl) ⟨609450, by rfl⟩ : syracuseStep 1625201 = 1218901) B1218901
theorem B4115569 : Blo 1080619 4115569 := bstep (se 2 (by rfl) ⟨1543338, by rfl⟩ : syracuseStep 4115569 = 3086677) B3086677
theorem B1625219 : Blo 1080619 1625219 := bstep (se 1 (by rfl) ⟨1218914, by rfl⟩ : syracuseStep 1625219 = 2437829) B2437829
theorem B1625249 : Blo 1080619 1625249 := bstep (se 2 (by rfl) ⟨609468, by rfl⟩ : syracuseStep 1625249 = 1218937) B1218937
theorem B1625267 : Blo 1080619 1625267 := bstep (se 1 (by rfl) ⟨1218950, by rfl⟩ : syracuseStep 1625267 = 2437901) B2437901
theorem B1625297 : Blo 1080619 1625297 := bstep (se 2 (by rfl) ⟨609486, by rfl⟩ : syracuseStep 1625297 = 1218973) B1218973
theorem B1625315 : Blo 1080619 1625315 := bstep (se 1 (by rfl) ⟨1218986, by rfl⟩ : syracuseStep 1625315 = 2437973) B2437973
theorem B11128049 : Blo 1080619 11128049 := bstep (se 2 (by rfl) ⟨4173018, by rfl⟩ : syracuseStep 11128049 = 8346037) B8346037
theorem B1625345 : Blo 1080619 1625345 := bstep (se 2 (by rfl) ⟨609504, by rfl⟩ : syracuseStep 1625345 = 1219009) B1219009
theorem B1625363 : Blo 1080619 1625363 := bstep (se 1 (by rfl) ⟨1219022, by rfl⟩ : syracuseStep 1625363 = 2438045) B2438045
theorem B2739491 : Blo 1080619 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B1625393 : Blo 1080619 1625393 := bstep (se 2 (by rfl) ⟨609522, by rfl⟩ : syracuseStep 1625393 = 1219045) B1219045
theorem B2313539 : Blo 1080619 2313539 := bstep (se 1 (by rfl) ⟨1735154, by rfl⟩ : syracuseStep 2313539 = 3470309) B3470309
theorem B1625411 : Blo 1080619 1625411 := bstep (se 1 (by rfl) ⟨1219058, by rfl⟩ : syracuseStep 1625411 = 2438117) B2438117
theorem B3657041 : Blo 1080619 3657041 := bstep (se 2 (by rfl) ⟨1371390, by rfl⟩ : syracuseStep 3657041 = 2742781) B2742781
theorem B1625441 : Blo 1080619 1625441 := bstep (se 2 (by rfl) ⟨609540, by rfl⟩ : syracuseStep 1625441 = 1219081) B1219081
theorem B1625459 : Blo 1080619 1625459 := bstep (se 1 (by rfl) ⟨1219094, by rfl⟩ : syracuseStep 1625459 = 2438189) B2438189
theorem B1625489 : Blo 1080619 1625489 := bstep (se 2 (by rfl) ⟨609558, by rfl⟩ : syracuseStep 1625489 = 1219117) B1219117
theorem B1625507 : Blo 1080619 1625507 := bstep (se 1 (by rfl) ⟨1219130, by rfl⟩ : syracuseStep 1625507 = 2438261) B2438261
theorem B1625537 : Blo 1080619 1625537 := bstep (se 2 (by rfl) ⟨609576, by rfl⟩ : syracuseStep 1625537 = 1219153) B1219153
theorem B1625555 : Blo 1080619 1625555 := bstep (se 1 (by rfl) ⟨1219166, by rfl⟩ : syracuseStep 1625555 = 2438333) B2438333
theorem B2739683 : Blo 1080619 2739683 := bstep (se 1 (by rfl) ⟨2054762, by rfl⟩ : syracuseStep 2739683 = 4109525) B4109525
theorem B1625585 : Blo 1080619 1625585 := bstep (se 2 (by rfl) ⟨609594, by rfl⟩ : syracuseStep 1625585 = 1219189) B1219189
theorem B1625603 : Blo 1080619 1625603 := bstep (se 1 (by rfl) ⟨1219202, by rfl⟩ : syracuseStep 1625603 = 2438405) B2438405
theorem B1625633 : Blo 1080619 1625633 := bstep (se 2 (by rfl) ⟨609612, by rfl⟩ : syracuseStep 1625633 = 1219225) B1219225
theorem B1625651 : Blo 1080619 1625651 := bstep (se 1 (by rfl) ⟨1219238, by rfl⟩ : syracuseStep 1625651 = 2438477) B2438477
theorem B1625681 : Blo 1080619 1625681 := bstep (se 2 (by rfl) ⟨609630, by rfl⟩ : syracuseStep 1625681 = 1219261) B1219261
theorem B11685475 : Blo 1080619 11685475 := bstep (se 1 (by rfl) ⟨8764106, by rfl⟩ : syracuseStep 11685475 = 17528213) B17528213
theorem B1625699 : Blo 1080619 1625699 := bstep (se 1 (by rfl) ⟨1219274, by rfl⟩ : syracuseStep 1625699 = 2438549) B2438549
theorem B1625729 : Blo 1080619 1625729 := bstep (se 2 (by rfl) ⟨609648, by rfl⟩ : syracuseStep 1625729 = 1219297) B1219297
theorem B6934157 : Blo 1080619 6934157 := bstep (se 3 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 6934157 = 2600309) B2600309
theorem B1461907 : Blo 1080619 1461907 := bstep (se 1 (by rfl) ⟨1096430, by rfl⟩ : syracuseStep 1461907 = 2192861) B2192861
theorem B1625747 : Blo 1080619 1625747 := bstep (se 1 (by rfl) ⟨1219310, by rfl⟩ : syracuseStep 1625747 = 2438621) B2438621
theorem B1625777 : Blo 1080619 1625777 := bstep (se 2 (by rfl) ⟨609666, by rfl⟩ : syracuseStep 1625777 = 1219333) B1219333
theorem B1232563 : Blo 1080619 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B1625795 : Blo 1080619 1625795 := bstep (se 1 (by rfl) ⟨1219346, by rfl⟩ : syracuseStep 1625795 = 2438693) B2438693
theorem B1625825 : Blo 1080619 1625825 := bstep (se 2 (by rfl) ⟨609684, by rfl⟩ : syracuseStep 1625825 = 1219369) B1219369
theorem B1625843 : Blo 1080619 1625843 := bstep (se 1 (by rfl) ⟨1219382, by rfl⟩ : syracuseStep 1625843 = 2438765) B2438765
theorem B2314001 : Blo 1080619 2314001 := bstep (se 2 (by rfl) ⟨867750, by rfl⟩ : syracuseStep 2314001 = 1735501) B1735501
theorem B1625873 : Blo 1080619 1625873 := bstep (se 2 (by rfl) ⟨609702, by rfl⟩ : syracuseStep 1625873 = 1219405) B1219405
theorem B1625891 : Blo 1080619 1625891 := bstep (se 1 (by rfl) ⟨1219418, by rfl⟩ : syracuseStep 1625891 = 2438837) B2438837
theorem B1625921 : Blo 1080619 1625921 := bstep (se 2 (by rfl) ⟨609720, by rfl⟩ : syracuseStep 1625921 = 1219441) B1219441
theorem B1625939 : Blo 1080619 1625939 := bstep (se 1 (by rfl) ⟨1219454, by rfl⟩ : syracuseStep 1625939 = 2438909) B2438909
theorem B3657581 : Blo 1080619 3657581 := bstep (se 3 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 3657581 = 1371593) B1371593
theorem B1625969 : Blo 1080619 1625969 := bstep (se 2 (by rfl) ⟨609738, by rfl⟩ : syracuseStep 1625969 = 1219477) B1219477
theorem B1953649 : Blo 1080619 1953649 := bstep (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) B1465237
theorem B1625987 : Blo 1080619 1625987 := bstep (se 1 (by rfl) ⟨1219490, by rfl⟩ : syracuseStep 1625987 = 2438981) B2438981
theorem B1626017 : Blo 1080619 1626017 := bstep (se 2 (by rfl) ⟨609756, by rfl⟩ : syracuseStep 1626017 = 1219513) B1219513
theorem B3657635 : Blo 1080619 3657635 := bstep (se 1 (by rfl) ⟨2743226, by rfl⟩ : syracuseStep 3657635 = 5486453) B5486453
theorem B1626035 : Blo 1080619 1626035 := bstep (se 1 (by rfl) ⟨1219526, by rfl⟩ : syracuseStep 1626035 = 2439053) B2439053
theorem B1626065 : Blo 1080619 1626065 := bstep (se 2 (by rfl) ⟨609774, by rfl⟩ : syracuseStep 1626065 = 1219549) B1219549
theorem B2052067 : Blo 1080619 2052067 := bstep (se 1 (by rfl) ⟨1539050, by rfl⟩ : syracuseStep 2052067 = 3078101) B3078101
theorem B1626083 : Blo 1080619 1626083 := bstep (se 1 (by rfl) ⟨1219562, by rfl⟩ : syracuseStep 1626083 = 2439125) B2439125
theorem B1626113 : Blo 1080619 1626113 := bstep (se 2 (by rfl) ⟨609792, by rfl⟩ : syracuseStep 1626113 = 1219585) B1219585
theorem B1626131 : Blo 1080619 1626131 := bstep (se 1 (by rfl) ⟨1219598, by rfl⟩ : syracuseStep 1626131 = 2439197) B2439197
theorem B1626161 : Blo 1080619 1626161 := bstep (se 2 (by rfl) ⟨609810, by rfl⟩ : syracuseStep 1626161 = 1219621) B1219621
theorem B1626179 : Blo 1080619 1626179 := bstep (se 1 (by rfl) ⟨1219634, by rfl⟩ : syracuseStep 1626179 = 2439269) B2439269
theorem B9261125 : Blo 1080619 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B1626209 : Blo 1080619 1626209 := bstep (se 2 (by rfl) ⟨609828, by rfl⟩ : syracuseStep 1626209 = 1219657) B1219657
theorem B1626227 : Blo 1080619 1626227 := bstep (se 1 (by rfl) ⟨1219670, by rfl⟩ : syracuseStep 1626227 = 2439341) B2439341
theorem B1626257 : Blo 1080619 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B1626275 : Blo 1080619 1626275 := bstep (se 1 (by rfl) ⟨1219706, by rfl⟩ : syracuseStep 1626275 = 2439413) B2439413
theorem B3657905 : Blo 1080619 3657905 := bstep (se 2 (by rfl) ⟨1371714, by rfl⟩ : syracuseStep 3657905 = 2743429) B2743429
theorem B1626305 : Blo 1080619 1626305 := bstep (se 2 (by rfl) ⟨609864, by rfl⟩ : syracuseStep 1626305 = 1219729) B1219729
theorem B1626323 : Blo 1080619 1626323 := bstep (se 1 (by rfl) ⟨1219742, by rfl⟩ : syracuseStep 1626323 = 2439485) B2439485
theorem B1626353 : Blo 1080619 1626353 := bstep (se 2 (by rfl) ⟨609882, by rfl⟩ : syracuseStep 1626353 = 1219765) B1219765
theorem B1626371 : Blo 1080619 1626371 := bstep (se 1 (by rfl) ⟨1219778, by rfl⟩ : syracuseStep 1626371 = 2439557) B2439557
theorem B1626401 : Blo 1080619 1626401 := bstep (se 2 (by rfl) ⟨609900, by rfl⟩ : syracuseStep 1626401 = 1219801) B1219801
theorem B1626419 : Blo 1080619 1626419 := bstep (se 1 (by rfl) ⟨1219814, by rfl⟩ : syracuseStep 1626419 = 2439629) B2439629
theorem B1626449 : Blo 1080619 1626449 := bstep (se 2 (by rfl) ⟨609918, by rfl⟩ : syracuseStep 1626449 = 1219837) B1219837
theorem B1462627 : Blo 1080619 1462627 := bstep (se 1 (by rfl) ⟨1096970, by rfl⟩ : syracuseStep 1462627 = 2193941) B2193941
theorem B1626467 : Blo 1080619 1626467 := bstep (se 1 (by rfl) ⟨1219850, by rfl⟩ : syracuseStep 1626467 = 2439701) B2439701
theorem B1626497 : Blo 1080619 1626497 := bstep (se 2 (by rfl) ⟨609936, by rfl⟩ : syracuseStep 1626497 = 1219873) B1219873
theorem B2740625 : Blo 1080619 2740625 := bstep (se 2 (by rfl) ⟨1027734, by rfl⟩ : syracuseStep 2740625 = 2055469) B2055469
theorem B1560979 : Blo 1080619 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B1626515 : Blo 1080619 1626515 := bstep (se 1 (by rfl) ⟨1219886, by rfl⟩ : syracuseStep 1626515 = 2439773) B2439773
theorem B2052515 : Blo 1080619 2052515 := bstep (se 1 (by rfl) ⟨1539386, by rfl⟩ : syracuseStep 2052515 = 3078773) B3078773
theorem B1954211 : Blo 1080619 1954211 := bstep (se 1 (by rfl) ⟨1465658, by rfl⟩ : syracuseStep 1954211 = 2931317) B2931317
theorem B1626545 : Blo 1080619 1626545 := bstep (se 2 (by rfl) ⟨609954, by rfl⟩ : syracuseStep 1626545 = 1219909) B1219909
theorem B2740675 : Blo 1080619 2740675 := bstep (se 1 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 2740675 = 4111013) B4111013
theorem B1626563 : Blo 1080619 1626563 := bstep (se 1 (by rfl) ⟨1219922, by rfl⟩ : syracuseStep 1626563 = 2439845) B2439845
theorem B5853637 : Blo 1080619 5853637 := bstep (se 4 (by rfl) ⟨548778, by rfl⟩ : syracuseStep 5853637 = 1097557) B1097557
theorem B1626593 : Blo 1080619 1626593 := bstep (se 2 (by rfl) ⟨609972, by rfl⟩ : syracuseStep 1626593 = 1219945) B1219945
theorem B1626611 : Blo 1080619 1626611 := bstep (se 1 (by rfl) ⟨1219958, by rfl⟩ : syracuseStep 1626611 = 2439917) B2439917
theorem B1626641 : Blo 1080619 1626641 := bstep (se 2 (by rfl) ⟨609990, by rfl⟩ : syracuseStep 1626641 = 1219981) B1219981
theorem B1298963 : Blo 1080619 1298963 := bstep (se 1 (by rfl) ⟨974222, by rfl⟩ : syracuseStep 1298963 = 1948445) B1948445
theorem B4117027 : Blo 1080619 4117027 := bstep (se 1 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 4117027 = 6175541) B6175541
theorem B1626659 : Blo 1080619 1626659 := bstep (se 1 (by rfl) ⟨1219994, by rfl⟩ : syracuseStep 1626659 = 2439989) B2439989
theorem B1626689 : Blo 1080619 1626689 := bstep (se 2 (by rfl) ⟨610008, by rfl⟩ : syracuseStep 1626689 = 1220017) B1220017
theorem B2740817 : Blo 1080619 2740817 := bstep (se 2 (by rfl) ⟨1027806, by rfl⟩ : syracuseStep 2740817 = 2055613) B2055613
theorem B1626707 : Blo 1080619 1626707 := bstep (se 1 (by rfl) ⟨1220030, by rfl⟩ : syracuseStep 1626707 = 2440061) B2440061
theorem B1626737 : Blo 1080619 1626737 := bstep (se 2 (by rfl) ⟨610026, by rfl⟩ : syracuseStep 1626737 = 1220053) B1220053
theorem B1626755 : Blo 1080619 1626755 := bstep (se 1 (by rfl) ⟨1220066, by rfl⟩ : syracuseStep 1626755 = 2440133) B2440133
theorem B1626785 : Blo 1080619 1626785 := bstep (se 2 (by rfl) ⟨610044, by rfl⟩ : syracuseStep 1626785 = 1220089) B1220089
theorem B1626803 : Blo 1080619 1626803 := bstep (se 1 (by rfl) ⟨1220102, by rfl⟩ : syracuseStep 1626803 = 2440205) B2440205
theorem B2052803 : Blo 1080619 2052803 := bstep (se 1 (by rfl) ⟨1539602, by rfl⟩ : syracuseStep 2052803 = 3079205) B3079205
theorem B3658445 : Blo 1080619 3658445 := bstep (se 3 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 3658445 = 1371917) B1371917
theorem B1626833 : Blo 1080619 1626833 := bstep (se 2 (by rfl) ⟨610062, by rfl⟩ : syracuseStep 1626833 = 1220125) B1220125
theorem B1626851 : Blo 1080619 1626851 := bstep (se 1 (by rfl) ⟨1220138, by rfl⟩ : syracuseStep 1626851 = 2440277) B2440277
theorem B9261809 : Blo 1080619 9261809 := bstep (se 2 (by rfl) ⟨3473178, by rfl⟩ : syracuseStep 9261809 = 6946357) B6946357
theorem B1626881 : Blo 1080619 1626881 := bstep (se 2 (by rfl) ⟨610080, by rfl⟩ : syracuseStep 1626881 = 1220161) B1220161
theorem B3658499 : Blo 1080619 3658499 := bstep (se 1 (by rfl) ⟨2743874, by rfl⟩ : syracuseStep 3658499 = 5487749) B5487749
theorem B1463059 : Blo 1080619 1463059 := bstep (se 1 (by rfl) ⟨1097294, by rfl⟩ : syracuseStep 1463059 = 2194589) B2194589
theorem B1626899 : Blo 1080619 1626899 := bstep (se 1 (by rfl) ⟨1220174, by rfl⟩ : syracuseStep 1626899 = 2440349) B2440349
theorem B1626929 : Blo 1080619 1626929 := bstep (se 2 (by rfl) ⟨610098, by rfl⟩ : syracuseStep 1626929 = 1220197) B1220197
theorem B1823681 : Blo 1080619 1823681 := bstep (se 2 (by rfl) ⟨683880, by rfl⟩ : syracuseStep 1823681 = 1367761) B1367761
theorem B3658769 : Blo 1080619 3658769 := bstep (se 2 (by rfl) ⟨1372038, by rfl⟩ : syracuseStep 3658769 = 2744077) B2744077
theorem B2315299 : Blo 1080619 2315299 := bstep (se 1 (by rfl) ⟨1736474, by rfl⟩ : syracuseStep 2315299 = 3472949) B3472949
theorem B1823809 : Blo 1080619 1823809 := bstep (se 2 (by rfl) ⟨683928, by rfl⟩ : syracuseStep 1823809 = 1367857) B1367857
theorem B1823843 : Blo 1080619 1823843 := bstep (se 1 (by rfl) ⟨1367882, by rfl⟩ : syracuseStep 1823843 = 2735765) B2735765
theorem B4936817 : Blo 1080619 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B1823971 : Blo 1080619 1823971 := bstep (se 1 (by rfl) ⟨1367978, by rfl⟩ : syracuseStep 1823971 = 2735957) B2735957
theorem B1463539 : Blo 1080619 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B2315555 : Blo 1080619 2315555 := bstep (se 1 (by rfl) ⟨1736666, by rfl⟩ : syracuseStep 2315555 = 3473333) B3473333
theorem B1824113 : Blo 1080619 1824113 := bstep (se 2 (by rfl) ⟨684042, by rfl⟩ : syracuseStep 1824113 = 1368085) B1368085
theorem B1463665 : Blo 1080619 1463665 := bstep (se 2 (by rfl) ⟨548874, by rfl⟩ : syracuseStep 1463665 = 1097749) B1097749
theorem B1824241 : Blo 1080619 1824241 := bstep (se 2 (by rfl) ⟨684090, by rfl⟩ : syracuseStep 1824241 = 1368181) B1368181
theorem B3462659 : Blo 1080619 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B1824275 : Blo 1080619 1824275 := bstep (se 1 (by rfl) ⟨1368206, by rfl⟩ : syracuseStep 1824275 = 2736413) B2736413
theorem B3659309 : Blo 1080619 3659309 := bstep (se 3 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 3659309 = 1372241) B1372241
theorem B2741809 : Blo 1080619 2741809 := bstep (se 2 (by rfl) ⟨1028178, by rfl⟩ : syracuseStep 2741809 = 2056357) B2056357
theorem B3659363 : Blo 1080619 3659363 := bstep (se 1 (by rfl) ⟨2744522, by rfl⟩ : syracuseStep 3659363 = 5489045) B5489045
theorem B2053745 : Blo 1080619 2053745 := bstep (se 2 (by rfl) ⟨770154, by rfl⟩ : syracuseStep 2053745 = 1540309) B1540309
theorem B1824403 : Blo 1080619 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B1824545 : Blo 1080619 1824545 := bstep (se 2 (by rfl) ⟨684204, by rfl⟩ : syracuseStep 1824545 = 1368409) B1368409
theorem B1464113 : Blo 1080619 1464113 := bstep (se 2 (by rfl) ⟨549042, by rfl⟩ : syracuseStep 1464113 = 1098085) B1098085
theorem B2742083 : Blo 1080619 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B8214371 : Blo 1080619 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B3659633 : Blo 1080619 3659633 := bstep (se 2 (by rfl) ⟨1372362, by rfl⟩ : syracuseStep 3659633 = 2744725) B2744725
theorem B16013197 : Blo 1080619 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B1824673 : Blo 1080619 1824673 := bstep (se 2 (by rfl) ⟨684252, by rfl⟩ : syracuseStep 1824673 = 1368505) B1368505
theorem B1824707 : Blo 1080619 1824707 := bstep (se 1 (by rfl) ⟨1368530, by rfl⟩ : syracuseStep 1824707 = 2737061) B2737061
theorem B2742275 : Blo 1080619 2742275 := bstep (se 1 (by rfl) ⟨2056706, by rfl⟩ : syracuseStep 2742275 = 4113413) B4113413
theorem B1824835 : Blo 1080619 1824835 := bstep (se 1 (by rfl) ⟨1368626, by rfl⟩ : syracuseStep 1824835 = 2737253) B2737253
theorem B14047345 : Blo 1080619 14047345 := bstep (se 2 (by rfl) ⟨5267754, by rfl⟩ : syracuseStep 14047345 = 10535509) B10535509
theorem B1824977 : Blo 1080619 1824977 := bstep (se 2 (by rfl) ⟨684366, by rfl⟩ : syracuseStep 1824977 = 1368733) B1368733
theorem B11688245 : Blo 1080619 11688245 := bstep (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) B1095773
theorem B1825105 : Blo 1080619 1825105 := bstep (se 2 (by rfl) ⟨684414, by rfl⟩ : syracuseStep 1825105 = 1368829) B1368829
theorem B8345969 : Blo 1080619 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B1825139 : Blo 1080619 1825139 := bstep (se 1 (by rfl) ⟨1368854, by rfl⟩ : syracuseStep 1825139 = 2737709) B2737709
theorem B3660173 : Blo 1080619 3660173 := bstep (se 3 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 3660173 = 1372565) B1372565
theorem B3660227 : Blo 1080619 3660227 := bstep (se 1 (by rfl) ⟨2745170, by rfl⟩ : syracuseStep 3660227 = 5490341) B5490341
theorem B2054641 : Blo 1080619 2054641 := bstep (se 2 (by rfl) ⟨770490, by rfl⟩ : syracuseStep 2054641 = 1540981) B1540981
theorem B1825267 : Blo 1080619 1825267 := bstep (se 1 (by rfl) ⟨1368950, by rfl⟩ : syracuseStep 1825267 = 2737901) B2737901
theorem B47536753 : Blo 1080619 47536753 := bstep (se 2 (by rfl) ⟨17826282, by rfl⟩ : syracuseStep 47536753 = 35652565) B35652565
theorem B1825409 : Blo 1080619 1825409 := bstep (se 2 (by rfl) ⟨684528, by rfl⟩ : syracuseStep 1825409 = 1369057) B1369057
theorem B2054801 : Blo 1080619 2054801 := bstep (se 2 (by rfl) ⟨770550, by rfl⟩ : syracuseStep 2054801 = 1541101) B1541101
theorem B6937285 : Blo 1080619 6937285 := bstep (se 4 (by rfl) ⟨650370, by rfl⟩ : syracuseStep 6937285 = 1300741) B1300741
theorem B3660497 : Blo 1080619 3660497 := bstep (se 2 (by rfl) ⟨1372686, by rfl⟩ : syracuseStep 3660497 = 2745373) B2745373
theorem B7789283 : Blo 1080619 7789283 := bstep (se 1 (by rfl) ⟨5841962, by rfl⟩ : syracuseStep 7789283 = 11683925) B11683925
theorem B35609315 : Blo 1080619 35609315 := bstep (se 1 (by rfl) ⟨26706986, by rfl⟩ : syracuseStep 35609315 = 53413973) B53413973
theorem B1170163 : Blo 1080619 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B1465075 : Blo 1080619 1465075 := bstep (se 1 (by rfl) ⟨1098806, by rfl⟩ : syracuseStep 1465075 = 2197613) B2197613
theorem B1825537 : Blo 1080619 1825537 := bstep (se 2 (by rfl) ⟨684576, by rfl⟩ : syracuseStep 1825537 = 1369153) B1369153
theorem B1825571 : Blo 1080619 1825571 := bstep (se 1 (by rfl) ⟨1369178, by rfl⟩ : syracuseStep 1825571 = 2738357) B2738357
theorem B3464003 : Blo 1080619 3464003 := bstep (se 1 (by rfl) ⟨2598002, by rfl⟩ : syracuseStep 3464003 = 5196005) B5196005
theorem B1825699 : Blo 1080619 1825699 := bstep (se 1 (by rfl) ⟨1369274, by rfl⟩ : syracuseStep 1825699 = 2738549) B2738549
theorem B2743217 : Blo 1080619 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B2743267 : Blo 1080619 2743267 := bstep (se 1 (by rfl) ⟨2057450, by rfl⟩ : syracuseStep 2743267 = 4114901) B4114901
theorem B5790733 : Blo 1080619 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B2055203 : Blo 1080619 2055203 := bstep (se 1 (by rfl) ⟨1541402, by rfl⟩ : syracuseStep 2055203 = 3082805) B3082805
theorem B1825841 : Blo 1080619 1825841 := bstep (se 2 (by rfl) ⟨684690, by rfl⟩ : syracuseStep 1825841 = 1369381) B1369381
theorem B4217933 : Blo 1080619 4217933 := bstep (se 3 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 4217933 = 1581725) B1581725
theorem B2743409 : Blo 1080619 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B1825969 : Blo 1080619 1825969 := bstep (se 2 (by rfl) ⟨684738, by rfl⟩ : syracuseStep 1825969 = 1369477) B1369477
theorem B1826003 : Blo 1080619 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B31251683 : Blo 1080619 31251683 := bstep (se 1 (by rfl) ⟨23438762, by rfl⟩ : syracuseStep 31251683 = 46877525) B46877525
theorem B1826131 : Blo 1080619 1826131 := bstep (se 1 (by rfl) ⟨1369598, by rfl⟩ : syracuseStep 1826131 = 2739197) B2739197
theorem B1301923 : Blo 1080619 1301923 := bstep (se 1 (by rfl) ⟨976442, by rfl⟩ : syracuseStep 1301923 = 1952885) B1952885
theorem B1826273 : Blo 1080619 1826273 := bstep (se 2 (by rfl) ⟨684852, by rfl⟩ : syracuseStep 1826273 = 1369705) B1369705
theorem B1465843 : Blo 1080619 1465843 := bstep (se 1 (by rfl) ⟨1099382, by rfl⟩ : syracuseStep 1465843 = 2198765) B2198765
theorem B12344885 : Blo 1080619 12344885 := bstep (se 5 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 12344885 = 1157333) B1157333
theorem B1826401 : Blo 1080619 1826401 := bstep (se 2 (by rfl) ⟨684900, by rfl⟩ : syracuseStep 1826401 = 1369801) B1369801
theorem B23453297 : Blo 1080619 23453297 := bstep (se 2 (by rfl) ⟨8794986, by rfl⟩ : syracuseStep 23453297 = 17589973) B17589973
theorem B1236595 : Blo 1080619 1236595 := bstep (se 1 (by rfl) ⟨927446, by rfl⟩ : syracuseStep 1236595 = 1854893) B1854893
theorem B1826435 : Blo 1080619 1826435 := bstep (se 1 (by rfl) ⟨1369826, by rfl⟩ : syracuseStep 1826435 = 2739653) B2739653
theorem B1826563 : Blo 1080619 1826563 := bstep (se 1 (by rfl) ⟨1369922, by rfl⟩ : syracuseStep 1826563 = 2739845) B2739845
theorem B1367923 : Blo 1080619 1367923 := bstep (se 1 (by rfl) ⟨1025942, by rfl⟩ : syracuseStep 1367923 = 2051885) B2051885
theorem B1826705 : Blo 1080619 1826705 := bstep (se 2 (by rfl) ⟨685014, by rfl⟩ : syracuseStep 1826705 = 1370029) B1370029
theorem B2056099 : Blo 1080619 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B1368019 : Blo 1080619 1368019 := bstep (se 1 (by rfl) ⟨1026014, by rfl⟩ : syracuseStep 1368019 = 2052029) B2052029
theorem B1826833 : Blo 1080619 1826833 := bstep (se 2 (by rfl) ⟨685062, by rfl⟩ : syracuseStep 1826833 = 1370125) B1370125
theorem B1826867 : Blo 1080619 1826867 := bstep (se 1 (by rfl) ⟨1370150, by rfl⟩ : syracuseStep 1826867 = 2740301) B2740301
theorem B2056259 : Blo 1080619 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B2744401 : Blo 1080619 2744401 := bstep (se 2 (by rfl) ⟨1029150, by rfl⟩ : syracuseStep 2744401 = 2058301) B2058301
theorem B1826995 : Blo 1080619 1826995 := bstep (se 1 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 1826995 = 2740493) B2740493
theorem B1827137 : Blo 1080619 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B2744675 : Blo 1080619 2744675 := bstep (se 1 (by rfl) ⟨2058506, by rfl⟩ : syracuseStep 2744675 = 4117013) B4117013
theorem B1827265 : Blo 1080619 1827265 := bstep (se 2 (by rfl) ⟨685224, by rfl⟩ : syracuseStep 1827265 = 1370449) B1370449
theorem B1368515 : Blo 1080619 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B1827299 : Blo 1080619 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B2744867 : Blo 1080619 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B3465773 : Blo 1080619 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B1827427 : Blo 1080619 1827427 := bstep (se 1 (by rfl) ⟨1370570, by rfl⟩ : syracuseStep 1827427 = 2741141) B2741141
theorem B1827569 : Blo 1080619 1827569 := bstep (se 2 (by rfl) ⟨685338, by rfl⟩ : syracuseStep 1827569 = 1370677) B1370677
theorem B2777969 : Blo 1080619 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B1827697 : Blo 1080619 1827697 := bstep (se 2 (by rfl) ⟨685386, by rfl⟩ : syracuseStep 1827697 = 1370773) B1370773
theorem B1827731 : Blo 1080619 1827731 := bstep (se 1 (by rfl) ⟨1370798, by rfl⟩ : syracuseStep 1827731 = 2741597) B2741597
theorem B1827859 : Blo 1080619 1827859 := bstep (se 1 (by rfl) ⟨1370894, by rfl⟩ : syracuseStep 1827859 = 2741789) B2741789
theorem B2057329 : Blo 1080619 2057329 := bstep (se 2 (by rfl) ⟨771498, by rfl⟩ : syracuseStep 2057329 = 1542997) B1542997
theorem B1369219 : Blo 1080619 1369219 := bstep (se 1 (by rfl) ⟨1026914, by rfl⟩ : syracuseStep 1369219 = 2053829) B2053829
theorem B10413197 : Blo 1080619 10413197 := bstep (se 3 (by rfl) ⟨1952474, by rfl⟩ : syracuseStep 10413197 = 3904949) B3904949
theorem B1828001 : Blo 1080619 1828001 := bstep (se 2 (by rfl) ⟨685500, by rfl⟩ : syracuseStep 1828001 = 1371001) B1371001
theorem B1369315 : Blo 1080619 1369315 := bstep (se 1 (by rfl) ⟨1026986, by rfl⟩ : syracuseStep 1369315 = 2053973) B2053973
theorem B1828129 : Blo 1080619 1828129 := bstep (se 2 (by rfl) ⟨685548, by rfl⟩ : syracuseStep 1828129 = 1371097) B1371097
theorem B1828163 : Blo 1080619 1828163 := bstep (se 1 (by rfl) ⟨1371122, by rfl⟩ : syracuseStep 1828163 = 2742245) B2742245
theorem B1828291 : Blo 1080619 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B6579697 : Blo 1080619 6579697 := bstep (se 2 (by rfl) ⟨2467386, by rfl⟩ : syracuseStep 6579697 = 4934773) B4934773
theorem B1828433 : Blo 1080619 1828433 := bstep (se 2 (by rfl) ⟨685662, by rfl⟩ : syracuseStep 1828433 = 1371325) B1371325
theorem B1828561 : Blo 1080619 1828561 := bstep (se 2 (by rfl) ⟨685710, by rfl⟩ : syracuseStep 1828561 = 1371421) B1371421
theorem B1369811 : Blo 1080619 1369811 := bstep (se 1 (by rfl) ⟨1027358, by rfl⟩ : syracuseStep 1369811 = 2054717) B2054717
theorem B1828595 : Blo 1080619 1828595 := bstep (se 1 (by rfl) ⟨1371446, by rfl⟩ : syracuseStep 1828595 = 2742893) B2742893
theorem B1828723 : Blo 1080619 1828723 := bstep (se 1 (by rfl) ⟨1371542, by rfl⟩ : syracuseStep 1828723 = 2743085) B2743085
theorem B15591365 : Blo 1080619 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B1828865 : Blo 1080619 1828865 := bstep (se 2 (by rfl) ⟨685824, by rfl⟩ : syracuseStep 1828865 = 1371649) B1371649
theorem B1828993 : Blo 1080619 1828993 := bstep (se 2 (by rfl) ⟨685872, by rfl⟩ : syracuseStep 1828993 = 1371745) B1371745
theorem B2058385 : Blo 1080619 2058385 := bstep (se 2 (by rfl) ⟨771894, by rfl⟩ : syracuseStep 2058385 = 1543789) B1543789
theorem B1829027 : Blo 1080619 1829027 := bstep (se 1 (by rfl) ⟨1371770, by rfl⟩ : syracuseStep 1829027 = 2743541) B2743541
theorem B5204195 : Blo 1080619 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B1829155 : Blo 1080619 1829155 := bstep (se 1 (by rfl) ⟨1371866, by rfl⟩ : syracuseStep 1829155 = 2743733) B2743733
theorem B7924081 : Blo 1080619 7924081 := bstep (se 2 (by rfl) ⟨2971530, by rfl⟩ : syracuseStep 7924081 = 5943061) B5943061
theorem B1370515 : Blo 1080619 1370515 := bstep (se 1 (by rfl) ⟨1027886, by rfl⟩ : syracuseStep 1370515 = 2055773) B2055773
theorem B1829297 : Blo 1080619 1829297 := bstep (se 2 (by rfl) ⟨685986, by rfl⟩ : syracuseStep 1829297 = 1371973) B1371973
theorem B1370611 : Blo 1080619 1370611 := bstep (se 1 (by rfl) ⟨1027958, by rfl⟩ : syracuseStep 1370611 = 2055917) B2055917
theorem B2058787 : Blo 1080619 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B1829425 : Blo 1080619 1829425 := bstep (se 2 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 1829425 = 1372069) B1372069
theorem B2058833 : Blo 1080619 2058833 := bstep (se 2 (by rfl) ⟨772062, by rfl⟩ : syracuseStep 2058833 = 1544125) B1544125
theorem B1829459 : Blo 1080619 1829459 := bstep (se 1 (by rfl) ⟨1372094, by rfl⟩ : syracuseStep 1829459 = 2744189) B2744189
theorem B1731233 : Blo 1080619 1731233 := bstep (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) B1298425
theorem B1829587 : Blo 1080619 1829587 := bstep (se 1 (by rfl) ⟨1372190, by rfl⟩ : syracuseStep 1829587 = 2744381) B2744381
theorem B1829729 : Blo 1080619 1829729 := bstep (se 2 (by rfl) ⟨686148, by rfl⟩ : syracuseStep 1829729 = 1372297) B1372297
theorem B1829857 : Blo 1080619 1829857 := bstep (se 2 (by rfl) ⟨686196, by rfl⟩ : syracuseStep 1829857 = 1372393) B1372393
theorem B1371107 : Blo 1080619 1371107 := bstep (se 1 (by rfl) ⟨1028330, by rfl⟩ : syracuseStep 1371107 = 2056661) B2056661
theorem B1829891 : Blo 1080619 1829891 := bstep (se 1 (by rfl) ⟨1372418, by rfl⟩ : syracuseStep 1829891 = 2744837) B2744837
theorem B8219717 : Blo 1080619 8219717 := bstep (se 4 (by rfl) ⟨770598, by rfl⟩ : syracuseStep 8219717 = 1541197) B1541197
theorem B1830019 : Blo 1080619 1830019 := bstep (se 1 (by rfl) ⟨1372514, by rfl⟩ : syracuseStep 1830019 = 2745029) B2745029
theorem B2780369 : Blo 1080619 2780369 := bstep (se 2 (by rfl) ⟨1042638, by rfl⟩ : syracuseStep 2780369 = 2085277) B2085277
theorem B3697937 : Blo 1080619 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B1830161 : Blo 1080619 1830161 := bstep (se 2 (by rfl) ⟨686310, by rfl⟩ : syracuseStep 1830161 = 1372621) B1372621
theorem B1830289 : Blo 1080619 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1732099 : Blo 1080619 1732099 := bstep (se 1 (by rfl) ⟨1299074, by rfl⟩ : syracuseStep 1732099 = 2598149) B2598149
theorem B5205539 : Blo 1080619 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B6942257 : Blo 1080619 6942257 := bstep (se 2 (by rfl) ⟨2603346, by rfl⟩ : syracuseStep 6942257 = 5206693) B5206693
theorem B1371811 : Blo 1080619 1371811 := bstep (se 1 (by rfl) ⟨1028858, by rfl⟩ : syracuseStep 1371811 = 2057717) B2057717
theorem B3468977 : Blo 1080619 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B3469027 : Blo 1080619 3469027 := bstep (se 1 (by rfl) ⟨2601770, by rfl⟩ : syracuseStep 3469027 = 5203541) B5203541
theorem B1732355 : Blo 1080619 1732355 := bstep (se 1 (by rfl) ⟨1299266, by rfl⟩ : syracuseStep 1732355 = 2598533) B2598533
theorem B1371907 : Blo 1080619 1371907 := bstep (se 1 (by rfl) ⟨1028930, by rfl⟩ : syracuseStep 1371907 = 2057861) B2057861
theorem B7794701 : Blo 1080619 7794701 := bstep (se 3 (by rfl) ⟨1461506, by rfl⟩ : syracuseStep 7794701 = 2923013) B2923013
theorem B1372403 : Blo 1080619 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B12513649 : Blo 1080619 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B4616689 : Blo 1080619 4616689 := bstep (se 2 (by rfl) ⟨1731258, by rfl⟩ : syracuseStep 4616689 = 3462517) B3462517
theorem B3469873 : Blo 1080619 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B1733329 : Blo 1080619 1733329 := bstep (se 2 (by rfl) ⟨649998, by rfl⟩ : syracuseStep 1733329 = 1299997) B1299997
theorem B3699427 : Blo 1080619 3699427 := bstep (se 1 (by rfl) ⟨2774570, by rfl⟩ : syracuseStep 3699427 = 5549141) B5549141
theorem B5206769 : Blo 1080619 5206769 := bstep (se 2 (by rfl) ⟨1952538, by rfl⟩ : syracuseStep 5206769 = 3905077) B3905077
theorem B5075747 : Blo 1080619 5075747 := bstep (se 1 (by rfl) ⟨3806810, by rfl⟩ : syracuseStep 5075747 = 7613621) B7613621
theorem B3077315 : Blo 1080619 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B46855381 : Blo 1080619 46855381 := bstep (se 7 (by rfl) ⟨549086, by rfl⟩ : syracuseStep 46855381 = 1098173) B1098173
theorem B2192707 : Blo 1080619 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B1734257 : Blo 1080619 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B2193169 : Blo 1080619 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B5207885 : Blo 1080619 5207885 := bstep (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) B1952957
theorem B6944717 : Blo 1080619 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B3078157 : Blo 1080619 3078157 := bstep (se 3 (by rfl) ⟨577154, by rfl⟩ : syracuseStep 3078157 = 1154309) B1154309
theorem B3471437 : Blo 1080619 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B3078317 : Blo 1080619 3078317 := bstep (se 3 (by rfl) ⟨577184, by rfl⟩ : syracuseStep 3078317 = 1154369) B1154369
theorem B3701027 : Blo 1080619 3701027 := bstep (se 1 (by rfl) ⟨2775770, by rfl⟩ : syracuseStep 3701027 = 5551541) B5551541
theorem B3078499 : Blo 1080619 3078499 := bstep (se 1 (by rfl) ⟨2308874, by rfl⟩ : syracuseStep 3078499 = 4617749) B4617749
theorem B2193809 : Blo 1080619 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B1735091 : Blo 1080619 1735091 := bstep (se 1 (by rfl) ⟨1301318, by rfl⟩ : syracuseStep 1735091 = 2602637) B2602637
theorem B9238981 : Blo 1080619 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B1735123 : Blo 1080619 1735123 := bstep (se 1 (by rfl) ⟨1301342, by rfl⟩ : syracuseStep 1735123 = 2602685) B2602685
theorem B5929733 : Blo 1080619 5929733 := bstep (se 4 (by rfl) ⟨555912, by rfl⟩ : syracuseStep 5929733 = 1111825) B1111825
theorem B1538851 : Blo 1080619 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B10386245 : Blo 1080619 10386245 := bstep (se 4 (by rfl) ⟨973710, by rfl⟩ : syracuseStep 10386245 = 1947421) B1947421
theorem B13859909 : Blo 1080619 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B4684877 : Blo 1080619 4684877 := bstep (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) B1756829
theorem B5209229 : Blo 1080619 5209229 := bstep (se 3 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 5209229 = 1953461) B1953461
theorem B4160753 : Blo 1080619 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B1539329 : Blo 1080619 1539329 := bstep (se 2 (by rfl) ⟨577248, by rfl⟩ : syracuseStep 1539329 = 1154497) B1154497
theorem B1080627 : Blo 1080619 1080627 := bstep (se 1 (by rfl) ⟨810470, by rfl⟩ : syracuseStep 1080627 = 1620941) B1620941
theorem B13892917 : Blo 1080619 13892917 := bstep (se 5 (by rfl) ⟨651230, by rfl⟩ : syracuseStep 13892917 = 1302461) B1302461
theorem B1080643 : Blo 1080619 1080643 := bstep (se 1 (by rfl) ⟨810482, by rfl⟩ : syracuseStep 1080643 = 1620965) B1620965
theorem B6159685 : Blo 1080619 6159685 := bstep (se 4 (by rfl) ⟨577470, by rfl⟩ : syracuseStep 6159685 = 1154941) B1154941
theorem B1080659 : Blo 1080619 1080659 := bstep (se 1 (by rfl) ⟨810494, by rfl⟩ : syracuseStep 1080659 = 1620989) B1620989
theorem B1080675 : Blo 1080619 1080675 := bstep (se 1 (by rfl) ⟨810506, by rfl⟩ : syracuseStep 1080675 = 1621013) B1621013
theorem B12320099 : Blo 1080619 12320099 := bstep (se 1 (by rfl) ⟨9240074, by rfl⟩ : syracuseStep 12320099 = 18480149) B18480149
theorem B1736051 : Blo 1080619 1736051 := bstep (se 1 (by rfl) ⟨1302038, by rfl⟩ : syracuseStep 1736051 = 2604077) B2604077
theorem B1080691 : Blo 1080619 1080691 := bstep (se 1 (by rfl) ⟨810518, by rfl⟩ : syracuseStep 1080691 = 1621037) B1621037
theorem B1539443 : Blo 1080619 1539443 := bstep (se 1 (by rfl) ⟨1154582, by rfl⟩ : syracuseStep 1539443 = 2309165) B2309165
theorem B1080707 : Blo 1080619 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B1080723 : Blo 1080619 1080723 := bstep (se 1 (by rfl) ⟨810542, by rfl⟩ : syracuseStep 1080723 = 1621085) B1621085
theorem B1080739 : Blo 1080619 1080739 := bstep (se 1 (by rfl) ⟨810554, by rfl⟩ : syracuseStep 1080739 = 1621109) B1621109
theorem B1080755 : Blo 1080619 1080755 := bstep (se 1 (by rfl) ⟨810566, by rfl⟩ : syracuseStep 1080755 = 1621133) B1621133
theorem B1736129 : Blo 1080619 1736129 := bstep (se 2 (by rfl) ⟨651048, by rfl⟩ : syracuseStep 1736129 = 1302097) B1302097
theorem B1080771 : Blo 1080619 1080771 := bstep (se 1 (by rfl) ⟨810578, by rfl⟩ : syracuseStep 1080771 = 1621157) B1621157
theorem B1539523 : Blo 1080619 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B1080787 : Blo 1080619 1080787 := bstep (se 1 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 1080787 = 1621181) B1621181
theorem B1080803 : Blo 1080619 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B1080819 : Blo 1080619 1080819 := bstep (se 1 (by rfl) ⟨810614, by rfl⟩ : syracuseStep 1080819 = 1621229) B1621229
theorem B1080835 : Blo 1080619 1080835 := bstep (se 1 (by rfl) ⟨810626, by rfl⟩ : syracuseStep 1080835 = 1621253) B1621253
theorem B1080851 : Blo 1080619 1080851 := bstep (se 1 (by rfl) ⟨810638, by rfl⟩ : syracuseStep 1080851 = 1621277) B1621277
theorem B1080867 : Blo 1080619 1080867 := bstep (se 1 (by rfl) ⟨810650, by rfl⟩ : syracuseStep 1080867 = 1621301) B1621301
theorem B1080883 : Blo 1080619 1080883 := bstep (se 1 (by rfl) ⟨810662, by rfl⟩ : syracuseStep 1080883 = 1621325) B1621325
theorem B1080899 : Blo 1080619 1080899 := bstep (se 1 (by rfl) ⟨810674, by rfl⟩ : syracuseStep 1080899 = 1621349) B1621349
theorem B1080915 : Blo 1080619 1080915 := bstep (se 1 (by rfl) ⟨810686, by rfl⟩ : syracuseStep 1080915 = 1621373) B1621373
theorem B1080931 : Blo 1080619 1080931 := bstep (se 1 (by rfl) ⟨810698, by rfl⟩ : syracuseStep 1080931 = 1621397) B1621397
theorem B1080947 : Blo 1080619 1080947 := bstep (se 1 (by rfl) ⟨810710, by rfl⟩ : syracuseStep 1080947 = 1621421) B1621421
theorem B1080963 : Blo 1080619 1080963 := bstep (se 1 (by rfl) ⟨810722, by rfl⟩ : syracuseStep 1080963 = 1621445) B1621445
theorem B1080979 : Blo 1080619 1080979 := bstep (se 1 (by rfl) ⟨810734, by rfl⟩ : syracuseStep 1080979 = 1621469) B1621469
theorem B1736353 : Blo 1080619 1736353 := bstep (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) B1302265
theorem B1080995 : Blo 1080619 1080995 := bstep (se 1 (by rfl) ⟨810746, by rfl⟩ : syracuseStep 1080995 = 1621493) B1621493
theorem B1081011 : Blo 1080619 1081011 := bstep (se 1 (by rfl) ⟨810758, by rfl⟩ : syracuseStep 1081011 = 1621517) B1621517
theorem B1081027 : Blo 1080619 1081027 := bstep (se 1 (by rfl) ⟨810770, by rfl⟩ : syracuseStep 1081027 = 1621541) B1621541
theorem B3079889 : Blo 1080619 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B1081043 : Blo 1080619 1081043 := bstep (se 1 (by rfl) ⟨810782, by rfl⟩ : syracuseStep 1081043 = 1621565) B1621565
theorem B1081059 : Blo 1080619 1081059 := bstep (se 1 (by rfl) ⟨810794, by rfl⟩ : syracuseStep 1081059 = 1621589) B1621589
theorem B1081075 : Blo 1080619 1081075 := bstep (se 1 (by rfl) ⟨810806, by rfl⟩ : syracuseStep 1081075 = 1621613) B1621613
theorem B1081091 : Blo 1080619 1081091 := bstep (se 1 (by rfl) ⟨810818, by rfl⟩ : syracuseStep 1081091 = 1621637) B1621637
theorem B1081107 : Blo 1080619 1081107 := bstep (se 1 (by rfl) ⟨810830, by rfl⟩ : syracuseStep 1081107 = 1621661) B1621661
theorem B5472035 : Blo 1080619 5472035 := bstep (se 1 (by rfl) ⟨4104026, by rfl⟩ : syracuseStep 5472035 = 8208053) B8208053
theorem B1081123 : Blo 1080619 1081123 := bstep (se 1 (by rfl) ⟨810842, by rfl⟩ : syracuseStep 1081123 = 1621685) B1621685
theorem B1081139 : Blo 1080619 1081139 := bstep (se 1 (by rfl) ⟨810854, by rfl⟩ : syracuseStep 1081139 = 1621709) B1621709
theorem B1081155 : Blo 1080619 1081155 := bstep (se 1 (by rfl) ⟨810866, by rfl⟩ : syracuseStep 1081155 = 1621733) B1621733
theorem B3473219 : Blo 1080619 3473219 := bstep (se 1 (by rfl) ⟨2604914, by rfl⟩ : syracuseStep 3473219 = 5209829) B5209829
theorem B1081171 : Blo 1080619 1081171 := bstep (se 1 (by rfl) ⟨810878, by rfl⟩ : syracuseStep 1081171 = 1621757) B1621757
theorem B1081187 : Blo 1080619 1081187 := bstep (se 1 (by rfl) ⟨810890, by rfl⟩ : syracuseStep 1081187 = 1621781) B1621781
theorem B1081203 : Blo 1080619 1081203 := bstep (se 1 (by rfl) ⟨810902, by rfl⟩ : syracuseStep 1081203 = 1621805) B1621805
theorem B1081219 : Blo 1080619 1081219 := bstep (se 1 (by rfl) ⟨810914, by rfl⟩ : syracuseStep 1081219 = 1621829) B1621829
theorem B1081235 : Blo 1080619 1081235 := bstep (se 1 (by rfl) ⟨810926, by rfl⟩ : syracuseStep 1081235 = 1621853) B1621853
theorem B1081251 : Blo 1080619 1081251 := bstep (se 1 (by rfl) ⟨810938, by rfl⟩ : syracuseStep 1081251 = 1621877) B1621877
theorem B1081267 : Blo 1080619 1081267 := bstep (se 1 (by rfl) ⟨810950, by rfl⟩ : syracuseStep 1081267 = 1621901) B1621901
theorem B1081283 : Blo 1080619 1081283 := bstep (se 1 (by rfl) ⟨810962, by rfl⟩ : syracuseStep 1081283 = 1621925) B1621925
theorem B1081299 : Blo 1080619 1081299 := bstep (se 1 (by rfl) ⟨810974, by rfl⟩ : syracuseStep 1081299 = 1621949) B1621949
theorem B1081315 : Blo 1080619 1081315 := bstep (se 1 (by rfl) ⟨810986, by rfl⟩ : syracuseStep 1081315 = 1621973) B1621973
theorem B1540081 : Blo 1080619 1540081 := bstep (se 2 (by rfl) ⟨577530, by rfl⟩ : syracuseStep 1540081 = 1155061) B1155061
theorem B1081331 : Blo 1080619 1081331 := bstep (se 1 (by rfl) ⟨810998, by rfl⟩ : syracuseStep 1081331 = 1621997) B1621997
theorem B1081355 : Blo 1080619 1081355 := bstep (se 1 (by rfl) ⟨811016, by rfl⟩ : syracuseStep 1081355 = 1622033) B1622033
theorem B1081367 : Blo 1080619 1081367 := bstep (se 1 (by rfl) ⟨811025, by rfl⟩ : syracuseStep 1081367 = 1622051) B1622051
theorem B4620311 : Blo 1080619 4620311 := bstep (se 1 (by rfl) ⟨3465233, by rfl⟩ : syracuseStep 4620311 = 6930467) B6930467
theorem B1081387 : Blo 1080619 1081387 := bstep (se 1 (by rfl) ⟨811040, by rfl⟩ : syracuseStep 1081387 = 1622081) B1622081
theorem B1081399 : Blo 1080619 1081399 := bstep (se 1 (by rfl) ⟨811049, by rfl⟩ : syracuseStep 1081399 = 1622099) B1622099
theorem B1081419 : Blo 1080619 1081419 := bstep (se 1 (by rfl) ⟨811064, by rfl⟩ : syracuseStep 1081419 = 1622129) B1622129
theorem B1081431 : Blo 1080619 1081431 := bstep (se 1 (by rfl) ⟨811073, by rfl⟩ : syracuseStep 1081431 = 1622147) B1622147
theorem B1081451 : Blo 1080619 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B1081463 : Blo 1080619 1081463 := bstep (se 1 (by rfl) ⟨811097, by rfl⟩ : syracuseStep 1081463 = 1622195) B1622195
theorem B1081483 : Blo 1080619 1081483 := bstep (se 1 (by rfl) ⟨811112, by rfl⟩ : syracuseStep 1081483 = 1622225) B1622225
theorem B1540235 : Blo 1080619 1540235 := bstep (se 1 (by rfl) ⟨1155176, by rfl⟩ : syracuseStep 1540235 = 2310353) B2310353
theorem B1081495 : Blo 1080619 1081495 := bstep (se 1 (by rfl) ⟨811121, by rfl⟩ : syracuseStep 1081495 = 1622243) B1622243
theorem B1081515 : Blo 1080619 1081515 := bstep (se 1 (by rfl) ⟨811136, by rfl⟩ : syracuseStep 1081515 = 1622273) B1622273
theorem B1081527 : Blo 1080619 1081527 := bstep (se 1 (by rfl) ⟨811145, by rfl⟩ : syracuseStep 1081527 = 1622291) B1622291
theorem B1081547 : Blo 1080619 1081547 := bstep (se 1 (by rfl) ⟨811160, by rfl⟩ : syracuseStep 1081547 = 1622321) B1622321
theorem B1081559 : Blo 1080619 1081559 := bstep (se 1 (by rfl) ⟨811169, by rfl⟩ : syracuseStep 1081559 = 1622339) B1622339
theorem B1081579 : Blo 1080619 1081579 := bstep (se 1 (by rfl) ⟨811184, by rfl⟩ : syracuseStep 1081579 = 1622369) B1622369
theorem B1081591 : Blo 1080619 1081591 := bstep (se 1 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 1081591 = 1622387) B1622387
theorem B1081611 : Blo 1080619 1081611 := bstep (se 1 (by rfl) ⟨811208, by rfl⟩ : syracuseStep 1081611 = 1622417) B1622417
theorem B1081623 : Blo 1080619 1081623 := bstep (se 1 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 1081623 = 1622435) B1622435
theorem B1081643 : Blo 1080619 1081643 := bstep (se 1 (by rfl) ⟨811232, by rfl⟩ : syracuseStep 1081643 = 1622465) B1622465
theorem B8323373 : Blo 1080619 8323373 := bstep (se 3 (by rfl) ⟨1560632, by rfl⟩ : syracuseStep 8323373 = 3121265) B3121265
theorem B1081655 : Blo 1080619 1081655 := bstep (se 1 (by rfl) ⟨811241, by rfl⟩ : syracuseStep 1081655 = 1622483) B1622483
theorem B1081675 : Blo 1080619 1081675 := bstep (se 1 (by rfl) ⟨811256, by rfl⟩ : syracuseStep 1081675 = 1622513) B1622513
theorem B1081687 : Blo 1080619 1081687 := bstep (se 1 (by rfl) ⟨811265, by rfl⟩ : syracuseStep 1081687 = 1622531) B1622531
theorem B1081707 : Blo 1080619 1081707 := bstep (se 1 (by rfl) ⟨811280, by rfl⟩ : syracuseStep 1081707 = 1622561) B1622561
theorem B1081719 : Blo 1080619 1081719 := bstep (se 1 (by rfl) ⟨811289, by rfl⟩ : syracuseStep 1081719 = 1622579) B1622579
theorem B1081739 : Blo 1080619 1081739 := bstep (se 1 (by rfl) ⟨811304, by rfl⟩ : syracuseStep 1081739 = 1622609) B1622609
theorem B1081751 : Blo 1080619 1081751 := bstep (se 1 (by rfl) ⟨811313, by rfl⟩ : syracuseStep 1081751 = 1622627) B1622627
theorem B1081771 : Blo 1080619 1081771 := bstep (se 1 (by rfl) ⟨811328, by rfl⟩ : syracuseStep 1081771 = 1622657) B1622657
theorem B1081783 : Blo 1080619 1081783 := bstep (se 1 (by rfl) ⟨811337, by rfl⟩ : syracuseStep 1081783 = 1622675) B1622675
theorem B4161995 : Blo 1080619 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B1081803 : Blo 1080619 1081803 := bstep (se 1 (by rfl) ⟨811352, by rfl⟩ : syracuseStep 1081803 = 1622705) B1622705
theorem B1081815 : Blo 1080619 1081815 := bstep (se 1 (by rfl) ⟨811361, by rfl⟩ : syracuseStep 1081815 = 1622723) B1622723
theorem B1081835 : Blo 1080619 1081835 := bstep (se 1 (by rfl) ⟨811376, by rfl⟩ : syracuseStep 1081835 = 1622753) B1622753
theorem B1081847 : Blo 1080619 1081847 := bstep (se 1 (by rfl) ⟨811385, by rfl⟩ : syracuseStep 1081847 = 1622771) B1622771
theorem B1081867 : Blo 1080619 1081867 := bstep (se 1 (by rfl) ⟨811400, by rfl⟩ : syracuseStep 1081867 = 1622801) B1622801
theorem B1081879 : Blo 1080619 1081879 := bstep (se 1 (by rfl) ⟨811409, by rfl⟩ : syracuseStep 1081879 = 1622819) B1622819
theorem B1081899 : Blo 1080619 1081899 := bstep (se 1 (by rfl) ⟨811424, by rfl⟩ : syracuseStep 1081899 = 1622849) B1622849
theorem B1081911 : Blo 1080619 1081911 := bstep (se 1 (by rfl) ⟨811433, by rfl⟩ : syracuseStep 1081911 = 1622867) B1622867
theorem B6160961 : Blo 1080619 6160961 := bstep (se 2 (by rfl) ⟨2310360, by rfl⟩ : syracuseStep 6160961 = 4620721) B4620721
theorem B1081931 : Blo 1080619 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B1081943 : Blo 1080619 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B1081963 : Blo 1080619 1081963 := bstep (se 1 (by rfl) ⟨811472, by rfl⟩ : syracuseStep 1081963 = 1622945) B1622945
theorem B1081975 : Blo 1080619 1081975 := bstep (se 1 (by rfl) ⟨811481, by rfl⟩ : syracuseStep 1081975 = 1622963) B1622963
theorem B1081995 : Blo 1080619 1081995 := bstep (se 1 (by rfl) ⟨811496, by rfl⟩ : syracuseStep 1081995 = 1622993) B1622993
theorem B1082007 : Blo 1080619 1082007 := bstep (se 1 (by rfl) ⟨811505, by rfl⟩ : syracuseStep 1082007 = 1623011) B1623011
theorem B1082027 : Blo 1080619 1082027 := bstep (se 1 (by rfl) ⟨811520, by rfl⟩ : syracuseStep 1082027 = 1623041) B1623041
theorem B1082039 : Blo 1080619 1082039 := bstep (se 1 (by rfl) ⟨811529, by rfl⟩ : syracuseStep 1082039 = 1623059) B1623059
theorem B1082059 : Blo 1080619 1082059 := bstep (se 1 (by rfl) ⟨811544, by rfl⟩ : syracuseStep 1082059 = 1623089) B1623089
theorem B1082071 : Blo 1080619 1082071 := bstep (se 1 (by rfl) ⟨811553, by rfl⟩ : syracuseStep 1082071 = 1623107) B1623107
theorem B1082091 : Blo 1080619 1082091 := bstep (se 1 (by rfl) ⟨811568, by rfl⟩ : syracuseStep 1082091 = 1623137) B1623137
theorem B1082103 : Blo 1080619 1082103 := bstep (se 1 (by rfl) ⟨811577, by rfl⟩ : syracuseStep 1082103 = 1623155) B1623155
theorem B1082123 : Blo 1080619 1082123 := bstep (se 1 (by rfl) ⟨811592, by rfl⟩ : syracuseStep 1082123 = 1623185) B1623185
theorem B1082135 : Blo 1080619 1082135 := bstep (se 1 (by rfl) ⟨811601, by rfl⟩ : syracuseStep 1082135 = 1623203) B1623203
theorem B1082155 : Blo 1080619 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B1082167 : Blo 1080619 1082167 := bstep (se 1 (by rfl) ⟨811625, by rfl⟩ : syracuseStep 1082167 = 1623251) B1623251
theorem B1082187 : Blo 1080619 1082187 := bstep (se 1 (by rfl) ⟨811640, by rfl⟩ : syracuseStep 1082187 = 1623281) B1623281
theorem B1082199 : Blo 1080619 1082199 := bstep (se 1 (by rfl) ⟨811649, by rfl⟩ : syracuseStep 1082199 = 1623299) B1623299
theorem B1082219 : Blo 1080619 1082219 := bstep (se 1 (by rfl) ⟨811664, by rfl⟩ : syracuseStep 1082219 = 1623329) B1623329
theorem B1082231 : Blo 1080619 1082231 := bstep (se 1 (by rfl) ⟨811673, by rfl⟩ : syracuseStep 1082231 = 1623347) B1623347
theorem B1082251 : Blo 1080619 1082251 := bstep (se 1 (by rfl) ⟨811688, by rfl⟩ : syracuseStep 1082251 = 1623377) B1623377
theorem B1082263 : Blo 1080619 1082263 := bstep (se 1 (by rfl) ⟨811697, by rfl⟩ : syracuseStep 1082263 = 1623395) B1623395
theorem B1082283 : Blo 1080619 1082283 := bstep (se 1 (by rfl) ⟨811712, by rfl⟩ : syracuseStep 1082283 = 1623425) B1623425
theorem B22217651 : Blo 1080619 22217651 := bstep (se 1 (by rfl) ⟨16663238, by rfl⟩ : syracuseStep 22217651 = 33326477) B33326477
theorem B1082295 : Blo 1080619 1082295 := bstep (se 1 (by rfl) ⟨811721, by rfl⟩ : syracuseStep 1082295 = 1623443) B1623443
theorem B1082315 : Blo 1080619 1082315 := bstep (se 1 (by rfl) ⟨811736, by rfl⟩ : syracuseStep 1082315 = 1623473) B1623473
theorem B1082327 : Blo 1080619 1082327 := bstep (se 1 (by rfl) ⟨811745, by rfl⟩ : syracuseStep 1082327 = 1623491) B1623491
theorem B1082347 : Blo 1080619 1082347 := bstep (se 1 (by rfl) ⟨811760, by rfl⟩ : syracuseStep 1082347 = 1623521) B1623521
theorem B1082359 : Blo 1080619 1082359 := bstep (se 1 (by rfl) ⟨811769, by rfl⟩ : syracuseStep 1082359 = 1623539) B1623539
theorem B1082379 : Blo 1080619 1082379 := bstep (se 1 (by rfl) ⟨811784, by rfl⟩ : syracuseStep 1082379 = 1623569) B1623569
theorem B1082391 : Blo 1080619 1082391 := bstep (se 1 (by rfl) ⟨811793, by rfl⟩ : syracuseStep 1082391 = 1623587) B1623587
theorem B1082411 : Blo 1080619 1082411 := bstep (se 1 (by rfl) ⟨811808, by rfl⟩ : syracuseStep 1082411 = 1623617) B1623617
theorem B1082423 : Blo 1080619 1082423 := bstep (se 1 (by rfl) ⟨811817, by rfl⟩ : syracuseStep 1082423 = 1623635) B1623635
theorem B1082443 : Blo 1080619 1082443 := bstep (se 1 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 1082443 = 1623665) B1623665
theorem B5211211 : Blo 1080619 5211211 := bstep (se 1 (by rfl) ⟨3908408, by rfl⟩ : syracuseStep 5211211 = 7816817) B7816817
theorem B1082455 : Blo 1080619 1082455 := bstep (se 1 (by rfl) ⟨811841, by rfl⟩ : syracuseStep 1082455 = 1623683) B1623683
theorem B1541209 : Blo 1080619 1541209 := bstep (se 2 (by rfl) ⟨577953, by rfl⟩ : syracuseStep 1541209 = 1155907) B1155907
theorem B5211229 : Blo 1080619 5211229 := bstep (se 3 (by rfl) ⟨977105, by rfl⟩ : syracuseStep 5211229 = 1954211) B1954211
theorem B1082475 : Blo 1080619 1082475 := bstep (se 1 (by rfl) ⟨811856, by rfl⟩ : syracuseStep 1082475 = 1623713) B1623713
theorem B1082487 : Blo 1080619 1082487 := bstep (se 1 (by rfl) ⟨811865, by rfl⟩ : syracuseStep 1082487 = 1623731) B1623731
theorem B1082507 : Blo 1080619 1082507 := bstep (se 1 (by rfl) ⟨811880, by rfl⟩ : syracuseStep 1082507 = 1623761) B1623761
theorem B1082519 : Blo 1080619 1082519 := bstep (se 1 (by rfl) ⟨811889, by rfl⟩ : syracuseStep 1082519 = 1623779) B1623779
theorem B1082539 : Blo 1080619 1082539 := bstep (se 1 (by rfl) ⟨811904, by rfl⟩ : syracuseStep 1082539 = 1623809) B1623809
theorem B1082551 : Blo 1080619 1082551 := bstep (se 1 (by rfl) ⟨811913, by rfl⟩ : syracuseStep 1082551 = 1623827) B1623827
theorem B1082571 : Blo 1080619 1082571 := bstep (se 1 (by rfl) ⟨811928, by rfl⟩ : syracuseStep 1082571 = 1623857) B1623857
theorem B1082583 : Blo 1080619 1082583 := bstep (se 1 (by rfl) ⟨811937, by rfl⟩ : syracuseStep 1082583 = 1623875) B1623875
theorem B1082603 : Blo 1080619 1082603 := bstep (se 1 (by rfl) ⟨811952, by rfl⟩ : syracuseStep 1082603 = 1623905) B1623905
theorem B1082615 : Blo 1080619 1082615 := bstep (se 1 (by rfl) ⟨811961, by rfl⟩ : syracuseStep 1082615 = 1623923) B1623923
theorem B1082635 : Blo 1080619 1082635 := bstep (se 1 (by rfl) ⟨811976, by rfl⟩ : syracuseStep 1082635 = 1623953) B1623953
theorem B1082647 : Blo 1080619 1082647 := bstep (se 1 (by rfl) ⟨811985, by rfl⟩ : syracuseStep 1082647 = 1623971) B1623971
theorem B1082667 : Blo 1080619 1082667 := bstep (se 1 (by rfl) ⟨812000, by rfl⟩ : syracuseStep 1082667 = 1624001) B1624001
theorem B1082679 : Blo 1080619 1082679 := bstep (se 1 (by rfl) ⟨812009, by rfl⟩ : syracuseStep 1082679 = 1624019) B1624019
theorem B1082699 : Blo 1080619 1082699 := bstep (se 1 (by rfl) ⟨812024, by rfl⟩ : syracuseStep 1082699 = 1624049) B1624049
theorem B1082711 : Blo 1080619 1082711 := bstep (se 1 (by rfl) ⟨812033, by rfl⟩ : syracuseStep 1082711 = 1624067) B1624067
theorem B1082731 : Blo 1080619 1082731 := bstep (se 1 (by rfl) ⟨812048, by rfl⟩ : syracuseStep 1082731 = 1624097) B1624097
theorem B1082743 : Blo 1080619 1082743 := bstep (se 1 (by rfl) ⟨812057, by rfl⟩ : syracuseStep 1082743 = 1624115) B1624115
theorem B1082763 : Blo 1080619 1082763 := bstep (se 1 (by rfl) ⟨812072, by rfl⟩ : syracuseStep 1082763 = 1624145) B1624145
theorem B1082775 : Blo 1080619 1082775 := bstep (se 1 (by rfl) ⟨812081, by rfl⟩ : syracuseStep 1082775 = 1624163) B1624163
theorem B1082795 : Blo 1080619 1082795 := bstep (se 1 (by rfl) ⟨812096, by rfl⟩ : syracuseStep 1082795 = 1624193) B1624193
theorem B1082807 : Blo 1080619 1082807 := bstep (se 1 (by rfl) ⟨812105, by rfl⟩ : syracuseStep 1082807 = 1624211) B1624211
theorem B3081665 : Blo 1080619 3081665 := bstep (se 2 (by rfl) ⟨1155624, by rfl⟩ : syracuseStep 3081665 = 2311249) B2311249
theorem B1082827 : Blo 1080619 1082827 := bstep (se 1 (by rfl) ⟨812120, by rfl⟩ : syracuseStep 1082827 = 1624241) B1624241
theorem B8783309 : Blo 1080619 8783309 := bstep (se 3 (by rfl) ⟨1646870, by rfl⟩ : syracuseStep 8783309 = 3293741) B3293741
theorem B1082839 : Blo 1080619 1082839 := bstep (se 1 (by rfl) ⟨812129, by rfl⟩ : syracuseStep 1082839 = 1624259) B1624259
theorem B3081689 : Blo 1080619 3081689 := bstep (se 2 (by rfl) ⟨1155633, by rfl⟩ : syracuseStep 3081689 = 2311267) B2311267
theorem B1082859 : Blo 1080619 1082859 := bstep (se 1 (by rfl) ⟨812144, by rfl⟩ : syracuseStep 1082859 = 1624289) B1624289
theorem B1082871 : Blo 1080619 1082871 := bstep (se 1 (by rfl) ⟨812153, by rfl⟩ : syracuseStep 1082871 = 1624307) B1624307
theorem B1082891 : Blo 1080619 1082891 := bstep (se 1 (by rfl) ⟨812168, by rfl⟩ : syracuseStep 1082891 = 1624337) B1624337
theorem B1082903 : Blo 1080619 1082903 := bstep (se 1 (by rfl) ⟨812177, by rfl⟩ : syracuseStep 1082903 = 1624355) B1624355
theorem B1082923 : Blo 1080619 1082923 := bstep (se 1 (by rfl) ⟨812192, by rfl⟩ : syracuseStep 1082923 = 1624385) B1624385
theorem B1082935 : Blo 1080619 1082935 := bstep (se 1 (by rfl) ⟨812201, by rfl⟩ : syracuseStep 1082935 = 1624403) B1624403
theorem B1082955 : Blo 1080619 1082955 := bstep (se 1 (by rfl) ⟨812216, by rfl⟩ : syracuseStep 1082955 = 1624433) B1624433
theorem B1082967 : Blo 1080619 1082967 := bstep (se 1 (by rfl) ⟨812225, by rfl⟩ : syracuseStep 1082967 = 1624451) B1624451
theorem B1082987 : Blo 1080619 1082987 := bstep (se 1 (by rfl) ⟨812240, by rfl⟩ : syracuseStep 1082987 = 1624481) B1624481
theorem B1082999 : Blo 1080619 1082999 := bstep (se 1 (by rfl) ⟨812249, by rfl⟩ : syracuseStep 1082999 = 1624499) B1624499
theorem B1083019 : Blo 1080619 1083019 := bstep (se 1 (by rfl) ⟨812264, by rfl⟩ : syracuseStep 1083019 = 1624529) B1624529
theorem B1083031 : Blo 1080619 1083031 := bstep (se 1 (by rfl) ⟨812273, by rfl⟩ : syracuseStep 1083031 = 1624547) B1624547
theorem B1083051 : Blo 1080619 1083051 := bstep (se 1 (by rfl) ⟨812288, by rfl⟩ : syracuseStep 1083051 = 1624577) B1624577
theorem B5211827 : Blo 1080619 5211827 := bstep (se 1 (by rfl) ⟨3908870, by rfl⟩ : syracuseStep 5211827 = 7817741) B7817741
theorem B1083063 : Blo 1080619 1083063 := bstep (se 1 (by rfl) ⟨812297, by rfl⟩ : syracuseStep 1083063 = 1624595) B1624595
theorem B1083083 : Blo 1080619 1083083 := bstep (se 1 (by rfl) ⟨812312, by rfl⟩ : syracuseStep 1083083 = 1624625) B1624625
theorem B1083095 : Blo 1080619 1083095 := bstep (se 1 (by rfl) ⟨812321, by rfl⟩ : syracuseStep 1083095 = 1624643) B1624643
theorem B8226521 : Blo 1080619 8226521 := bstep (se 2 (by rfl) ⟨3084945, by rfl⟩ : syracuseStep 8226521 = 6169891) B6169891
theorem B1083115 : Blo 1080619 1083115 := bstep (se 1 (by rfl) ⟨812336, by rfl⟩ : syracuseStep 1083115 = 1624673) B1624673
theorem B1083127 : Blo 1080619 1083127 := bstep (se 1 (by rfl) ⟨812345, by rfl⟩ : syracuseStep 1083127 = 1624691) B1624691
theorem B1083147 : Blo 1080619 1083147 := bstep (se 1 (by rfl) ⟨812360, by rfl⟩ : syracuseStep 1083147 = 1624721) B1624721
theorem B1083159 : Blo 1080619 1083159 := bstep (se 1 (by rfl) ⟨812369, by rfl⟩ : syracuseStep 1083159 = 1624739) B1624739
theorem B1083179 : Blo 1080619 1083179 := bstep (se 1 (by rfl) ⟨812384, by rfl⟩ : syracuseStep 1083179 = 1624769) B1624769
theorem B1083191 : Blo 1080619 1083191 := bstep (se 1 (by rfl) ⟨812393, by rfl⟩ : syracuseStep 1083191 = 1624787) B1624787
theorem B3901259 : Blo 1080619 3901259 := bstep (se 1 (by rfl) ⟨2925944, by rfl⟩ : syracuseStep 3901259 = 5851889) B5851889
theorem B1083211 : Blo 1080619 1083211 := bstep (se 1 (by rfl) ⟨812408, by rfl⟩ : syracuseStep 1083211 = 1624817) B1624817
theorem B1083223 : Blo 1080619 1083223 := bstep (se 1 (by rfl) ⟨812417, by rfl⟩ : syracuseStep 1083223 = 1624835) B1624835
theorem B5474141 : Blo 1080619 5474141 := bstep (se 3 (by rfl) ⟨1026401, by rfl⟩ : syracuseStep 5474141 = 2052803) B2052803
theorem B33392483 : Blo 1080619 33392483 := bstep (se 1 (by rfl) ⟨25044362, by rfl⟩ : syracuseStep 33392483 = 50088725) B50088725
theorem B1083243 : Blo 1080619 1083243 := bstep (se 1 (by rfl) ⟨812432, by rfl⟩ : syracuseStep 1083243 = 1624865) B1624865
theorem B1083255 : Blo 1080619 1083255 := bstep (se 1 (by rfl) ⟨812441, by rfl⟩ : syracuseStep 1083255 = 1624883) B1624883
theorem B1083275 : Blo 1080619 1083275 := bstep (se 1 (by rfl) ⟨812456, by rfl⟩ : syracuseStep 1083275 = 1624913) B1624913
theorem B1083287 : Blo 1080619 1083287 := bstep (se 1 (by rfl) ⟨812465, by rfl⟩ : syracuseStep 1083287 = 1624931) B1624931
theorem B1083307 : Blo 1080619 1083307 := bstep (se 1 (by rfl) ⟨812480, by rfl⟩ : syracuseStep 1083307 = 1624961) B1624961
theorem B1083319 : Blo 1080619 1083319 := bstep (se 1 (by rfl) ⟨812489, by rfl⟩ : syracuseStep 1083319 = 1624979) B1624979
theorem B1083339 : Blo 1080619 1083339 := bstep (se 1 (by rfl) ⟨812504, by rfl⟩ : syracuseStep 1083339 = 1625009) B1625009
theorem B1083351 : Blo 1080619 1083351 := bstep (se 1 (by rfl) ⟨812513, by rfl⟩ : syracuseStep 1083351 = 1625027) B1625027
theorem B1083371 : Blo 1080619 1083371 := bstep (se 1 (by rfl) ⟨812528, by rfl⟩ : syracuseStep 1083371 = 1625057) B1625057
theorem B1083383 : Blo 1080619 1083383 := bstep (se 1 (by rfl) ⟨812537, by rfl⟩ : syracuseStep 1083383 = 1625075) B1625075
theorem B1083403 : Blo 1080619 1083403 := bstep (se 1 (by rfl) ⟨812552, by rfl⟩ : syracuseStep 1083403 = 1625105) B1625105
theorem B1083415 : Blo 1080619 1083415 := bstep (se 1 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 1083415 = 1625123) B1625123
theorem B1083435 : Blo 1080619 1083435 := bstep (se 1 (by rfl) ⟨812576, by rfl⟩ : syracuseStep 1083435 = 1625153) B1625153
theorem B1083447 : Blo 1080619 1083447 := bstep (se 1 (by rfl) ⟨812585, by rfl⟩ : syracuseStep 1083447 = 1625171) B1625171
theorem B1083467 : Blo 1080619 1083467 := bstep (se 1 (by rfl) ⟨812600, by rfl⟩ : syracuseStep 1083467 = 1625201) B1625201
theorem B1083479 : Blo 1080619 1083479 := bstep (se 1 (by rfl) ⟨812609, by rfl⟩ : syracuseStep 1083479 = 1625219) B1625219
theorem B1083499 : Blo 1080619 1083499 := bstep (se 1 (by rfl) ⟨812624, by rfl⟩ : syracuseStep 1083499 = 1625249) B1625249
theorem B1083511 : Blo 1080619 1083511 := bstep (se 1 (by rfl) ⟨812633, by rfl⟩ : syracuseStep 1083511 = 1625267) B1625267
theorem B1083531 : Blo 1080619 1083531 := bstep (se 1 (by rfl) ⟨812648, by rfl⟩ : syracuseStep 1083531 = 1625297) B1625297
theorem B1083543 : Blo 1080619 1083543 := bstep (se 1 (by rfl) ⟨812657, by rfl⟩ : syracuseStep 1083543 = 1625315) B1625315
theorem B1083563 : Blo 1080619 1083563 := bstep (se 1 (by rfl) ⟨812672, by rfl⟩ : syracuseStep 1083563 = 1625345) B1625345
theorem B1083575 : Blo 1080619 1083575 := bstep (se 1 (by rfl) ⟨812681, by rfl⟩ : syracuseStep 1083575 = 1625363) B1625363
theorem B1083595 : Blo 1080619 1083595 := bstep (se 1 (by rfl) ⟨812696, by rfl⟩ : syracuseStep 1083595 = 1625393) B1625393
theorem B1542359 : Blo 1080619 1542359 := bstep (se 1 (by rfl) ⟨1156769, by rfl⟩ : syracuseStep 1542359 = 2313539) B2313539
theorem B1083607 : Blo 1080619 1083607 := bstep (se 1 (by rfl) ⟨812705, by rfl⟩ : syracuseStep 1083607 = 1625411) B1625411
theorem B1083627 : Blo 1080619 1083627 := bstep (se 1 (by rfl) ⟨812720, by rfl⟩ : syracuseStep 1083627 = 1625441) B1625441
theorem B1083639 : Blo 1080619 1083639 := bstep (se 1 (by rfl) ⟨812729, by rfl⟩ : syracuseStep 1083639 = 1625459) B1625459
theorem B1083659 : Blo 1080619 1083659 := bstep (se 1 (by rfl) ⟨812744, by rfl⟩ : syracuseStep 1083659 = 1625489) B1625489
theorem B1083671 : Blo 1080619 1083671 := bstep (se 1 (by rfl) ⟨812753, by rfl⟩ : syracuseStep 1083671 = 1625507) B1625507
theorem B1083691 : Blo 1080619 1083691 := bstep (se 1 (by rfl) ⟨812768, by rfl⟩ : syracuseStep 1083691 = 1625537) B1625537
theorem B1083703 : Blo 1080619 1083703 := bstep (se 1 (by rfl) ⟨812777, by rfl⟩ : syracuseStep 1083703 = 1625555) B1625555
theorem B1083723 : Blo 1080619 1083723 := bstep (se 1 (by rfl) ⟨812792, by rfl⟩ : syracuseStep 1083723 = 1625585) B1625585
theorem B1083735 : Blo 1080619 1083735 := bstep (se 1 (by rfl) ⟨812801, by rfl⟩ : syracuseStep 1083735 = 1625603) B1625603
theorem B1083755 : Blo 1080619 1083755 := bstep (se 1 (by rfl) ⟨812816, by rfl⟩ : syracuseStep 1083755 = 1625633) B1625633
theorem B1083767 : Blo 1080619 1083767 := bstep (se 1 (by rfl) ⟨812825, by rfl⟩ : syracuseStep 1083767 = 1625651) B1625651
theorem B1083787 : Blo 1080619 1083787 := bstep (se 1 (by rfl) ⟨812840, by rfl⟩ : syracuseStep 1083787 = 1625681) B1625681
theorem B1083799 : Blo 1080619 1083799 := bstep (se 1 (by rfl) ⟨812849, by rfl⟩ : syracuseStep 1083799 = 1625699) B1625699
theorem B1083819 : Blo 1080619 1083819 := bstep (se 1 (by rfl) ⟨812864, by rfl⟩ : syracuseStep 1083819 = 1625729) B1625729
theorem B4622771 : Blo 1080619 4622771 := bstep (se 1 (by rfl) ⟨3467078, by rfl⟩ : syracuseStep 4622771 = 6934157) B6934157
theorem B1083831 : Blo 1080619 1083831 := bstep (se 1 (by rfl) ⟨812873, by rfl⟩ : syracuseStep 1083831 = 1625747) B1625747
theorem B1083851 : Blo 1080619 1083851 := bstep (se 1 (by rfl) ⟨812888, by rfl⟩ : syracuseStep 1083851 = 1625777) B1625777
theorem B1083863 : Blo 1080619 1083863 := bstep (se 1 (by rfl) ⟨812897, by rfl⟩ : syracuseStep 1083863 = 1625795) B1625795
theorem B1083883 : Blo 1080619 1083883 := bstep (se 1 (by rfl) ⟨812912, by rfl⟩ : syracuseStep 1083883 = 1625825) B1625825
theorem B1083895 : Blo 1080619 1083895 := bstep (se 1 (by rfl) ⟨812921, by rfl⟩ : syracuseStep 1083895 = 1625843) B1625843
theorem B1542667 : Blo 1080619 1542667 := bstep (se 1 (by rfl) ⟨1157000, by rfl⟩ : syracuseStep 1542667 = 2314001) B2314001
theorem B1083915 : Blo 1080619 1083915 := bstep (se 1 (by rfl) ⟨812936, by rfl⟩ : syracuseStep 1083915 = 1625873) B1625873
theorem B1083927 : Blo 1080619 1083927 := bstep (se 1 (by rfl) ⟨812945, by rfl⟩ : syracuseStep 1083927 = 1625891) B1625891
theorem B1083947 : Blo 1080619 1083947 := bstep (se 1 (by rfl) ⟨812960, by rfl⟩ : syracuseStep 1083947 = 1625921) B1625921
theorem B1083959 : Blo 1080619 1083959 := bstep (se 1 (by rfl) ⟨812969, by rfl⟩ : syracuseStep 1083959 = 1625939) B1625939
theorem B1083979 : Blo 1080619 1083979 := bstep (se 1 (by rfl) ⟨812984, by rfl⟩ : syracuseStep 1083979 = 1625969) B1625969
theorem B1083991 : Blo 1080619 1083991 := bstep (se 1 (by rfl) ⟨812993, by rfl⟩ : syracuseStep 1083991 = 1625987) B1625987
theorem B4393565 : Blo 1080619 4393565 := bstep (se 3 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 4393565 = 1647587) B1647587
theorem B6589021 : Blo 1080619 6589021 := bstep (se 3 (by rfl) ⟨1235441, by rfl⟩ : syracuseStep 6589021 = 2470883) B2470883
theorem B1084011 : Blo 1080619 1084011 := bstep (se 1 (by rfl) ⟨813008, by rfl⟩ : syracuseStep 1084011 = 1626017) B1626017
theorem B1084023 : Blo 1080619 1084023 := bstep (se 1 (by rfl) ⟨813017, by rfl⟩ : syracuseStep 1084023 = 1626035) B1626035
theorem B1084043 : Blo 1080619 1084043 := bstep (se 1 (by rfl) ⟨813032, by rfl⟩ : syracuseStep 1084043 = 1626065) B1626065
theorem B1084055 : Blo 1080619 1084055 := bstep (se 1 (by rfl) ⟨813041, by rfl⟩ : syracuseStep 1084055 = 1626083) B1626083
theorem B1084075 : Blo 1080619 1084075 := bstep (se 1 (by rfl) ⟨813056, by rfl⟩ : syracuseStep 1084075 = 1626113) B1626113
theorem B3082931 : Blo 1080619 3082931 := bstep (se 1 (by rfl) ⟨2312198, by rfl⟩ : syracuseStep 3082931 = 4624397) B4624397
theorem B1084087 : Blo 1080619 1084087 := bstep (se 1 (by rfl) ⟨813065, by rfl⟩ : syracuseStep 1084087 = 1626131) B1626131
theorem B1084107 : Blo 1080619 1084107 := bstep (se 1 (by rfl) ⟨813080, by rfl⟩ : syracuseStep 1084107 = 1626161) B1626161
theorem B1084119 : Blo 1080619 1084119 := bstep (se 1 (by rfl) ⟨813089, by rfl⟩ : syracuseStep 1084119 = 1626179) B1626179
theorem B1084139 : Blo 1080619 1084139 := bstep (se 1 (by rfl) ⟨813104, by rfl⟩ : syracuseStep 1084139 = 1626209) B1626209
theorem B1084151 : Blo 1080619 1084151 := bstep (se 1 (by rfl) ⟨813113, by rfl⟩ : syracuseStep 1084151 = 1626227) B1626227
theorem B1084171 : Blo 1080619 1084171 := bstep (se 1 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 1084171 = 1626257) B1626257
theorem B1084183 : Blo 1080619 1084183 := bstep (se 1 (by rfl) ⟨813137, by rfl⟩ : syracuseStep 1084183 = 1626275) B1626275
theorem B1084203 : Blo 1080619 1084203 := bstep (se 1 (by rfl) ⟨813152, by rfl⟩ : syracuseStep 1084203 = 1626305) B1626305
theorem B1084215 : Blo 1080619 1084215 := bstep (se 1 (by rfl) ⟨813161, by rfl⟩ : syracuseStep 1084215 = 1626323) B1626323
theorem B1084235 : Blo 1080619 1084235 := bstep (se 1 (by rfl) ⟨813176, by rfl⟩ : syracuseStep 1084235 = 1626353) B1626353
theorem B1084247 : Blo 1080619 1084247 := bstep (se 1 (by rfl) ⟨813185, by rfl⟩ : syracuseStep 1084247 = 1626371) B1626371
theorem B1084267 : Blo 1080619 1084267 := bstep (se 1 (by rfl) ⟨813200, by rfl⟩ : syracuseStep 1084267 = 1626401) B1626401
theorem B1084279 : Blo 1080619 1084279 := bstep (se 1 (by rfl) ⟨813209, by rfl⟩ : syracuseStep 1084279 = 1626419) B1626419
theorem B1084299 : Blo 1080619 1084299 := bstep (se 1 (by rfl) ⟨813224, by rfl⟩ : syracuseStep 1084299 = 1626449) B1626449
theorem B1084311 : Blo 1080619 1084311 := bstep (se 1 (by rfl) ⟨813233, by rfl⟩ : syracuseStep 1084311 = 1626467) B1626467
theorem B1084331 : Blo 1080619 1084331 := bstep (se 1 (by rfl) ⟨813248, by rfl⟩ : syracuseStep 1084331 = 1626497) B1626497
theorem B1084343 : Blo 1080619 1084343 := bstep (se 1 (by rfl) ⟨813257, by rfl⟩ : syracuseStep 1084343 = 1626515) B1626515
theorem B1084363 : Blo 1080619 1084363 := bstep (se 1 (by rfl) ⟨813272, by rfl⟩ : syracuseStep 1084363 = 1626545) B1626545
theorem B1084375 : Blo 1080619 1084375 := bstep (se 1 (by rfl) ⟨813281, by rfl⟩ : syracuseStep 1084375 = 1626563) B1626563
theorem B1084395 : Blo 1080619 1084395 := bstep (se 1 (by rfl) ⟨813296, by rfl⟩ : syracuseStep 1084395 = 1626593) B1626593
theorem B1084407 : Blo 1080619 1084407 := bstep (se 1 (by rfl) ⟨813305, by rfl⟩ : syracuseStep 1084407 = 1626611) B1626611
theorem B1084427 : Blo 1080619 1084427 := bstep (se 1 (by rfl) ⟨813320, by rfl⟩ : syracuseStep 1084427 = 1626641) B1626641
theorem B1084439 : Blo 1080619 1084439 := bstep (se 1 (by rfl) ⟨813329, by rfl⟩ : syracuseStep 1084439 = 1626659) B1626659
theorem B1084459 : Blo 1080619 1084459 := bstep (se 1 (by rfl) ⟨813344, by rfl⟩ : syracuseStep 1084459 = 1626689) B1626689
theorem B1084471 : Blo 1080619 1084471 := bstep (se 1 (by rfl) ⟨813353, by rfl⟩ : syracuseStep 1084471 = 1626707) B1626707
theorem B1084491 : Blo 1080619 1084491 := bstep (se 1 (by rfl) ⟨813368, by rfl⟩ : syracuseStep 1084491 = 1626737) B1626737
theorem B1084503 : Blo 1080619 1084503 := bstep (se 1 (by rfl) ⟨813377, by rfl⟩ : syracuseStep 1084503 = 1626755) B1626755
theorem B1084523 : Blo 1080619 1084523 := bstep (se 1 (by rfl) ⟨813392, by rfl⟩ : syracuseStep 1084523 = 1626785) B1626785
theorem B1084535 : Blo 1080619 1084535 := bstep (se 1 (by rfl) ⟨813401, by rfl⟩ : syracuseStep 1084535 = 1626803) B1626803
theorem B1084555 : Blo 1080619 1084555 := bstep (se 1 (by rfl) ⟨813416, by rfl⟩ : syracuseStep 1084555 = 1626833) B1626833
theorem B1084567 : Blo 1080619 1084567 := bstep (se 1 (by rfl) ⟨813425, by rfl⟩ : syracuseStep 1084567 = 1626851) B1626851
theorem B1084587 : Blo 1080619 1084587 := bstep (se 1 (by rfl) ⟨813440, by rfl⟩ : syracuseStep 1084587 = 1626881) B1626881
theorem B1084599 : Blo 1080619 1084599 := bstep (se 1 (by rfl) ⟨813449, by rfl⟩ : syracuseStep 1084599 = 1626899) B1626899
theorem B1084619 : Blo 1080619 1084619 := bstep (se 1 (by rfl) ⟨813464, by rfl⟩ : syracuseStep 1084619 = 1626929) B1626929
theorem B9375011 : Blo 1080619 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B1215787 : Blo 1080619 1215787 := bstep (se 1 (by rfl) ⟨911840, by rfl⟩ : syracuseStep 1215787 = 1823681) B1823681
theorem B1215895 : Blo 1080619 1215895 := bstep (se 1 (by rfl) ⟨911921, by rfl⟩ : syracuseStep 1215895 = 1823843) B1823843
theorem B1543703 : Blo 1080619 1543703 := bstep (se 1 (by rfl) ⟨1157777, by rfl⟩ : syracuseStep 1543703 = 2315555) B2315555
theorem B1216075 : Blo 1080619 1216075 := bstep (se 1 (by rfl) ⟨912056, by rfl⟩ : syracuseStep 1216075 = 1824113) B1824113
theorem B4394675 : Blo 1080619 4394675 := bstep (se 1 (by rfl) ⟨3296006, by rfl⟩ : syracuseStep 4394675 = 6592013) B6592013
theorem B1216183 : Blo 1080619 1216183 := bstep (se 1 (by rfl) ⟨912137, by rfl⟩ : syracuseStep 1216183 = 1824275) B1824275
theorem B1543897 : Blo 1080619 1543897 := bstep (se 2 (by rfl) ⟨578961, by rfl⟩ : syracuseStep 1543897 = 1157923) B1157923
theorem B1216363 : Blo 1080619 1216363 := bstep (se 1 (by rfl) ⟨912272, by rfl⟩ : syracuseStep 1216363 = 1824545) B1824545
theorem B5476247 : Blo 1080619 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B1216471 : Blo 1080619 1216471 := bstep (se 1 (by rfl) ⟨912353, by rfl⟩ : syracuseStep 1216471 = 1824707) B1824707
theorem B1216651 : Blo 1080619 1216651 := bstep (se 1 (by rfl) ⟨912488, by rfl⟩ : syracuseStep 1216651 = 1824977) B1824977
theorem B1216759 : Blo 1080619 1216759 := bstep (se 1 (by rfl) ⟨912569, by rfl⟩ : syracuseStep 1216759 = 1825139) B1825139
theorem B4624685 : Blo 1080619 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B1216939 : Blo 1080619 1216939 := bstep (se 1 (by rfl) ⟨912704, by rfl⟩ : syracuseStep 1216939 = 1825409) B1825409
theorem B1217047 : Blo 1080619 1217047 := bstep (se 1 (by rfl) ⟨912785, by rfl⟩ : syracuseStep 1217047 = 1825571) B1825571
theorem B1217227 : Blo 1080619 1217227 := bstep (se 1 (by rfl) ⟨912920, by rfl⟩ : syracuseStep 1217227 = 1825841) B1825841
theorem B3904301 : Blo 1080619 3904301 := bstep (se 3 (by rfl) ⟨732056, by rfl⟩ : syracuseStep 3904301 = 1464113) B1464113
theorem B1217335 : Blo 1080619 1217335 := bstep (se 1 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 1217335 = 1826003) B1826003
theorem B1643417 : Blo 1080619 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B35066803 : Blo 1080619 35066803 := bstep (se 1 (by rfl) ⟨26300102, by rfl⟩ : syracuseStep 35066803 = 52600205) B52600205
theorem B4625369 : Blo 1080619 4625369 := bstep (se 2 (by rfl) ⟨1734513, by rfl⟩ : syracuseStep 4625369 = 3469027) B3469027
theorem B3707869 : Blo 1080619 3707869 := bstep (se 3 (by rfl) ⟨695225, by rfl⟩ : syracuseStep 3707869 = 1390451) B1390451
theorem B1217515 : Blo 1080619 1217515 := bstep (se 1 (by rfl) ⟨913136, by rfl⟩ : syracuseStep 1217515 = 1826273) B1826273
theorem B8229923 : Blo 1080619 8229923 := bstep (se 1 (by rfl) ⟨6172442, by rfl⟩ : syracuseStep 8229923 = 12344885) B12344885
theorem B15635531 : Blo 1080619 15635531 := bstep (se 1 (by rfl) ⟨11726648, by rfl⟩ : syracuseStep 15635531 = 23453297) B23453297
theorem B1217623 : Blo 1080619 1217623 := bstep (se 1 (by rfl) ⟨913217, by rfl⟩ : syracuseStep 1217623 = 1826435) B1826435
theorem B1217803 : Blo 1080619 1217803 := bstep (se 1 (by rfl) ⟨913352, by rfl⟩ : syracuseStep 1217803 = 1826705) B1826705
theorem B1217911 : Blo 1080619 1217911 := bstep (se 1 (by rfl) ⟨913433, by rfl⟩ : syracuseStep 1217911 = 1826867) B1826867
theorem B3085789 : Blo 1080619 3085789 := bstep (se 3 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 3085789 = 1157171) B1157171
theorem B3085847 : Blo 1080619 3085847 := bstep (se 1 (by rfl) ⟨2314385, by rfl⟩ : syracuseStep 3085847 = 4628771) B4628771
theorem B1218091 : Blo 1080619 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B1218199 : Blo 1080619 1218199 := bstep (se 1 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 1218199 = 1827299) B1827299
theorem B16684865 : Blo 1080619 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B1218379 : Blo 1080619 1218379 := bstep (se 1 (by rfl) ⟨913784, by rfl⟩ : syracuseStep 1218379 = 1827569) B1827569
theorem B7804849 : Blo 1080619 7804849 := bstep (se 2 (by rfl) ⟨2926818, by rfl⟩ : syracuseStep 7804849 = 5853637) B5853637
theorem B1218487 : Blo 1080619 1218487 := bstep (se 1 (by rfl) ⟨913865, by rfl⟩ : syracuseStep 1218487 = 1827731) B1827731
theorem B4626497 : Blo 1080619 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B1218667 : Blo 1080619 1218667 := bstep (se 1 (by rfl) ⟨914000, by rfl⟩ : syracuseStep 1218667 = 1828001) B1828001
theorem B1644695 : Blo 1080619 1644695 := bstep (se 1 (by rfl) ⟨1233521, by rfl⟩ : syracuseStep 1644695 = 2467043) B2467043
theorem B1218775 : Blo 1080619 1218775 := bstep (se 1 (by rfl) ⟨914081, by rfl⟩ : syracuseStep 1218775 = 1828163) B1828163
theorem B1186039 : Blo 1080619 1186039 := bstep (se 1 (by rfl) ⟨889529, by rfl⟩ : syracuseStep 1186039 = 1779059) B1779059
theorem B1218955 : Blo 1080619 1218955 := bstep (se 1 (by rfl) ⟨914216, by rfl⟩ : syracuseStep 1218955 = 1828433) B1828433
theorem B2431475 : Blo 1080619 2431475 := bstep (se 1 (by rfl) ⟨1823606, by rfl⟩ : syracuseStep 2431475 = 3647213) B3647213
theorem B1219063 : Blo 1080619 1219063 := bstep (se 1 (by rfl) ⟨914297, by rfl⟩ : syracuseStep 1219063 = 1828595) B1828595
theorem B2431511 : Blo 1080619 2431511 := bstep (se 1 (by rfl) ⟨1823633, by rfl⟩ : syracuseStep 2431511 = 3647267) B3647267
theorem B10394243 : Blo 1080619 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B1219243 : Blo 1080619 1219243 := bstep (se 1 (by rfl) ⟨914432, by rfl⟩ : syracuseStep 1219243 = 1828865) B1828865
theorem B2431691 : Blo 1080619 2431691 := bstep (se 1 (by rfl) ⟨1823768, by rfl⟩ : syracuseStep 2431691 = 3647537) B3647537
theorem B3087065 : Blo 1080619 3087065 := bstep (se 2 (by rfl) ⟨1157649, by rfl⟩ : syracuseStep 3087065 = 2315299) B2315299
theorem B2431745 : Blo 1080619 2431745 := bstep (se 2 (by rfl) ⟨911904, by rfl⟩ : syracuseStep 2431745 = 1823809) B1823809
theorem B1219351 : Blo 1080619 1219351 := bstep (se 1 (by rfl) ⟨914513, by rfl⟩ : syracuseStep 1219351 = 1829027) B1829027
theorem B3087179 : Blo 1080619 3087179 := bstep (se 1 (by rfl) ⟨2315384, by rfl⟩ : syracuseStep 3087179 = 4630769) B4630769
theorem B1219531 : Blo 1080619 1219531 := bstep (se 1 (by rfl) ⟨914648, by rfl⟩ : syracuseStep 1219531 = 1829297) B1829297
theorem B2431961 : Blo 1080619 2431961 := bstep (se 2 (by rfl) ⟨911985, by rfl⟩ : syracuseStep 2431961 = 1823971) B1823971
theorem B2432051 : Blo 1080619 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B1219639 : Blo 1080619 1219639 := bstep (se 1 (by rfl) ⟨914729, by rfl⟩ : syracuseStep 1219639 = 1829459) B1829459
theorem B2432087 : Blo 1080619 2432087 := bstep (se 1 (by rfl) ⟨1824065, by rfl⟩ : syracuseStep 2432087 = 3648131) B3648131
theorem B1645655 : Blo 1080619 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B2923609 : Blo 1080619 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B3087563 : Blo 1080619 3087563 := bstep (se 1 (by rfl) ⟨2315672, by rfl⟩ : syracuseStep 3087563 = 4631345) B4631345
theorem B1219819 : Blo 1080619 1219819 := bstep (se 1 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 1219819 = 1829729) B1829729
theorem B2432267 : Blo 1080619 2432267 := bstep (se 1 (by rfl) ⟨1824200, by rfl⟩ : syracuseStep 2432267 = 3648401) B3648401
theorem B2432321 : Blo 1080619 2432321 := bstep (se 2 (by rfl) ⟨912120, by rfl⟩ : syracuseStep 2432321 = 1824241) B1824241
theorem B1219927 : Blo 1080619 1219927 := bstep (se 1 (by rfl) ⟨914945, by rfl⟩ : syracuseStep 1219927 = 1829891) B1829891
theorem B5479811 : Blo 1080619 5479811 := bstep (se 1 (by rfl) ⟨4109858, by rfl⟩ : syracuseStep 5479811 = 8219717) B8219717
theorem B2465291 : Blo 1080619 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B1220107 : Blo 1080619 1220107 := bstep (se 1 (by rfl) ⟨915080, by rfl⟩ : syracuseStep 1220107 = 1830161) B1830161
theorem B2432537 : Blo 1080619 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B2432627 : Blo 1080619 2432627 := bstep (se 1 (by rfl) ⟨1824470, by rfl⟩ : syracuseStep 2432627 = 3648941) B3648941
theorem B2432663 : Blo 1080619 2432663 := bstep (se 1 (by rfl) ⟨1824497, by rfl⟩ : syracuseStep 2432663 = 3648995) B3648995
theorem B2924225 : Blo 1080619 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B4628171 : Blo 1080619 4628171 := bstep (se 1 (by rfl) ⟨3471128, by rfl⟩ : syracuseStep 4628171 = 6942257) B6942257
theorem B2432843 : Blo 1080619 2432843 := bstep (se 1 (by rfl) ⟨1824632, by rfl⟩ : syracuseStep 2432843 = 3649265) B3649265
theorem B1154903 : Blo 1080619 1154903 := bstep (se 1 (by rfl) ⟨866177, by rfl⟩ : syracuseStep 1154903 = 1732355) B1732355
theorem B2432897 : Blo 1080619 2432897 := bstep (se 2 (by rfl) ⟨912336, by rfl⟩ : syracuseStep 2432897 = 1824673) B1824673
theorem B3088307 : Blo 1080619 3088307 := bstep (se 1 (by rfl) ⟨2316230, by rfl⟩ : syracuseStep 3088307 = 4632461) B4632461
theorem B4104209 : Blo 1080619 4104209 := bstep (se 2 (by rfl) ⟨1539078, by rfl⟩ : syracuseStep 4104209 = 3078157) B3078157
theorem B4759597 : Blo 1080619 4759597 := bstep (se 3 (by rfl) ⟨892424, by rfl⟩ : syracuseStep 4759597 = 1784849) B1784849
theorem B2433113 : Blo 1080619 2433113 := bstep (se 2 (by rfl) ⟨912417, by rfl⟩ : syracuseStep 2433113 = 1824835) B1824835
theorem B6168707 : Blo 1080619 6168707 := bstep (se 1 (by rfl) ⟨4626530, by rfl⟩ : syracuseStep 6168707 = 9253061) B9253061
theorem B2433203 : Blo 1080619 2433203 := bstep (se 1 (by rfl) ⟨1824902, by rfl⟩ : syracuseStep 2433203 = 3649805) B3649805
theorem B11247821 : Blo 1080619 11247821 := bstep (se 3 (by rfl) ⟨2108966, by rfl⟩ : syracuseStep 11247821 = 4217933) B4217933
theorem B2433239 : Blo 1080619 2433239 := bstep (se 1 (by rfl) ⟨1824929, by rfl⟩ : syracuseStep 2433239 = 3649859) B3649859
theorem B2433419 : Blo 1080619 2433419 := bstep (se 1 (by rfl) ⟨1825064, by rfl⟩ : syracuseStep 2433419 = 3650129) B3650129
theorem B2433473 : Blo 1080619 2433473 := bstep (se 2 (by rfl) ⟨912552, by rfl⟩ : syracuseStep 2433473 = 1825105) B1825105
theorem B4104665 : Blo 1080619 4104665 := bstep (se 2 (by rfl) ⟨1539249, by rfl⟩ : syracuseStep 4104665 = 3078499) B3078499
theorem B3383831 : Blo 1080619 3383831 := bstep (se 1 (by rfl) ⟨2537873, by rfl⟩ : syracuseStep 3383831 = 5075747) B5075747
theorem B2433689 : Blo 1080619 2433689 := bstep (se 2 (by rfl) ⟨912633, by rfl⟩ : syracuseStep 2433689 = 1825267) B1825267
theorem B4104877 : Blo 1080619 4104877 := bstep (se 3 (by rfl) ⟨769664, by rfl⟩ : syracuseStep 4104877 = 1539329) B1539329
theorem B3089117 : Blo 1080619 3089117 := bstep (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) B1158419
theorem B2433779 : Blo 1080619 2433779 := bstep (se 1 (by rfl) ⟨1825334, by rfl⟩ : syracuseStep 2433779 = 3650669) B3650669
theorem B2433815 : Blo 1080619 2433815 := bstep (se 1 (by rfl) ⟨1825361, by rfl⟩ : syracuseStep 2433815 = 3650723) B3650723
theorem B63382337 : Blo 1080619 63382337 := bstep (se 2 (by rfl) ⟨23768376, by rfl⟩ : syracuseStep 63382337 = 47536753) B47536753
theorem B25043813 : Blo 1080619 25043813 := bstep (se 4 (by rfl) ⟨2347857, by rfl⟩ : syracuseStep 25043813 = 4695715) B4695715
theorem B9249713 : Blo 1080619 9249713 := bstep (se 2 (by rfl) ⟨3468642, by rfl⟩ : syracuseStep 9249713 = 6937285) B6937285
theorem B2433995 : Blo 1080619 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B2597849 : Blo 1080619 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B4105181 : Blo 1080619 4105181 := bstep (se 3 (by rfl) ⟨769721, by rfl⟩ : syracuseStep 4105181 = 1539443) B1539443
theorem B4629469 : Blo 1080619 4629469 := bstep (se 3 (by rfl) ⟨868025, by rfl⟩ : syracuseStep 4629469 = 1736051) B1736051
theorem B2434049 : Blo 1080619 2434049 := bstep (se 2 (by rfl) ⟨912768, by rfl⟩ : syracuseStep 2434049 = 1825537) B1825537
theorem B23733323 : Blo 1080619 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B2434265 : Blo 1080619 2434265 := bstep (se 2 (by rfl) ⟨912849, by rfl⟩ : syracuseStep 2434265 = 1825699) B1825699
theorem B2434355 : Blo 1080619 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B4629811 : Blo 1080619 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B12330305 : Blo 1080619 12330305 := bstep (se 2 (by rfl) ⟨4623864, by rfl⟩ : syracuseStep 12330305 = 9247729) B9247729
theorem B2434391 : Blo 1080619 2434391 := bstep (se 1 (by rfl) ⟨1825793, by rfl⟩ : syracuseStep 2434391 = 3651587) B3651587
theorem B2434571 : Blo 1080619 2434571 := bstep (se 1 (by rfl) ⟨1825928, by rfl⟩ : syracuseStep 2434571 = 3651857) B3651857
theorem B2467351 : Blo 1080619 2467351 := bstep (se 1 (by rfl) ⟨1850513, by rfl⟩ : syracuseStep 2467351 = 3701027) B3701027
theorem B2434625 : Blo 1080619 2434625 := bstep (se 2 (by rfl) ⟨912984, by rfl⟩ : syracuseStep 2434625 = 1825969) B1825969
theorem B1156727 : Blo 1080619 1156727 := bstep (se 1 (by rfl) ⟨867545, by rfl⟩ : syracuseStep 1156727 = 1735091) B1735091
theorem B1648331 : Blo 1080619 1648331 := bstep (se 1 (by rfl) ⟨1236248, by rfl⟩ : syracuseStep 1648331 = 2472497) B2472497
theorem B1976023 : Blo 1080619 1976023 := bstep (se 1 (by rfl) ⟨1482017, by rfl⟩ : syracuseStep 1976023 = 2964035) B2964035
theorem B18523889 : Blo 1080619 18523889 := bstep (se 2 (by rfl) ⟨6946458, by rfl⟩ : syracuseStep 18523889 = 13892917) B13892917
theorem B2434841 : Blo 1080619 2434841 := bstep (se 2 (by rfl) ⟨913065, by rfl⟩ : syracuseStep 2434841 = 1826131) B1826131
theorem B8791843 : Blo 1080619 8791843 := bstep (se 1 (by rfl) ⟨6593882, by rfl⟩ : syracuseStep 8791843 = 13187765) B13187765
theorem B3647321 : Blo 1080619 3647321 := bstep (se 2 (by rfl) ⟨1367745, by rfl⟩ : syracuseStep 3647321 = 2735491) B2735491
theorem B2434931 : Blo 1080619 2434931 := bstep (se 1 (by rfl) ⟨1826198, by rfl⟩ : syracuseStep 2434931 = 3652397) B3652397
theorem B6924163 : Blo 1080619 6924163 := bstep (se 1 (by rfl) ⟨5193122, by rfl⟩ : syracuseStep 6924163 = 10386245) B10386245
theorem B2434967 : Blo 1080619 2434967 := bstep (se 1 (by rfl) ⟨1826225, by rfl⟩ : syracuseStep 2434967 = 3652451) B3652451
theorem B3123251 : Blo 1080619 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B85403717 : Blo 1080619 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B2435147 : Blo 1080619 2435147 := bstep (se 1 (by rfl) ⟨1826360, by rfl⟩ : syracuseStep 2435147 = 3652721) B3652721
theorem B2435201 : Blo 1080619 2435201 := bstep (se 2 (by rfl) ⟨913200, by rfl⟩ : syracuseStep 2435201 = 1826401) B1826401
theorem B1648793 : Blo 1080619 1648793 := bstep (se 2 (by rfl) ⟨618297, by rfl⟩ : syracuseStep 1648793 = 1236595) B1236595
theorem B8235269 : Blo 1080619 8235269 := bstep (se 4 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 8235269 = 1544113) B1544113
theorem B1157419 : Blo 1080619 1157419 := bstep (se 1 (by rfl) ⟨868064, by rfl⟩ : syracuseStep 1157419 = 1736129) B1736129
theorem B2435417 : Blo 1080619 2435417 := bstep (se 2 (by rfl) ⟨913281, by rfl⟩ : syracuseStep 2435417 = 1826563) B1826563
theorem B2435507 : Blo 1080619 2435507 := bstep (se 1 (by rfl) ⟨1826630, by rfl⟩ : syracuseStep 2435507 = 3653261) B3653261
theorem B2435543 : Blo 1080619 2435543 := bstep (se 1 (by rfl) ⟨1826657, by rfl⟩ : syracuseStep 2435543 = 3653315) B3653315
theorem B3648023 : Blo 1080619 3648023 := bstep (se 1 (by rfl) ⟨2736017, by rfl⟩ : syracuseStep 3648023 = 5472035) B5472035
theorem B8792651 : Blo 1080619 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B2435723 : Blo 1080619 2435723 := bstep (se 1 (by rfl) ⟨1826792, by rfl⟩ : syracuseStep 2435723 = 3653585) B3653585
theorem B2435777 : Blo 1080619 2435777 := bstep (se 2 (by rfl) ⟨913416, by rfl⟩ : syracuseStep 2435777 = 1826833) B1826833
theorem B2435993 : Blo 1080619 2435993 := bstep (se 2 (by rfl) ⟨913497, by rfl⟩ : syracuseStep 2435993 = 1826995) B1826995
theorem B2436083 : Blo 1080619 2436083 := bstep (se 1 (by rfl) ⟨1827062, by rfl⟩ : syracuseStep 2436083 = 3654125) B3654125
theorem B5483537 : Blo 1080619 5483537 := bstep (se 2 (by rfl) ⟨2056326, by rfl⟩ : syracuseStep 5483537 = 4112653) B4112653
theorem B2436119 : Blo 1080619 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B3648563 : Blo 1080619 3648563 := bstep (se 1 (by rfl) ⟨2736422, by rfl⟩ : syracuseStep 3648563 = 5472845) B5472845
theorem B5483699 : Blo 1080619 5483699 := bstep (se 1 (by rfl) ⟨4112774, by rfl⟩ : syracuseStep 5483699 = 8225549) B8225549
theorem B2436299 : Blo 1080619 2436299 := bstep (se 1 (by rfl) ⟨1827224, by rfl⟩ : syracuseStep 2436299 = 3654449) B3654449
theorem B2436353 : Blo 1080619 2436353 := bstep (se 2 (by rfl) ⟨913632, by rfl⟩ : syracuseStep 2436353 = 1827265) B1827265
theorem B3648833 : Blo 1080619 3648833 := bstep (se 2 (by rfl) ⟨1368312, by rfl⟩ : syracuseStep 3648833 = 2736625) B2736625
theorem B2436569 : Blo 1080619 2436569 := bstep (se 2 (by rfl) ⟨913713, by rfl⟩ : syracuseStep 2436569 = 1827427) B1827427
theorem B4107779 : Blo 1080619 4107779 := bstep (se 1 (by rfl) ⟨3080834, by rfl⟩ : syracuseStep 4107779 = 6161669) B6161669
theorem B4107793 : Blo 1080619 4107793 := bstep (se 2 (by rfl) ⟨1540422, by rfl⟩ : syracuseStep 4107793 = 3080845) B3080845
theorem B2436659 : Blo 1080619 2436659 := bstep (se 1 (by rfl) ⟨1827494, by rfl⟩ : syracuseStep 2436659 = 3654989) B3654989
theorem B2436695 : Blo 1080619 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B3288779 : Blo 1080619 3288779 := bstep (se 1 (by rfl) ⟨2466584, by rfl⟩ : syracuseStep 3288779 = 4933169) B4933169
theorem B3124939 : Blo 1080619 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B2436875 : Blo 1080619 2436875 := bstep (se 1 (by rfl) ⟨1827656, by rfl⟩ : syracuseStep 2436875 = 3655313) B3655313
theorem B4108097 : Blo 1080619 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B2436929 : Blo 1080619 2436929 := bstep (se 2 (by rfl) ⟨913848, by rfl⟩ : syracuseStep 2436929 = 1827697) B1827697
theorem B3649373 : Blo 1080619 3649373 := bstep (se 3 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 3649373 = 1368515) B1368515
theorem B2437145 : Blo 1080619 2437145 := bstep (se 2 (by rfl) ⟨913929, by rfl⟩ : syracuseStep 2437145 = 1827859) B1827859
theorem B2437235 : Blo 1080619 2437235 := bstep (se 1 (by rfl) ⟨1827926, by rfl⟩ : syracuseStep 2437235 = 3655853) B3655853
theorem B2437271 : Blo 1080619 2437271 := bstep (se 1 (by rfl) ⟨1827953, by rfl⟩ : syracuseStep 2437271 = 3655907) B3655907
theorem B2371799 : Blo 1080619 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B10400005 : Blo 1080619 10400005 := bstep (se 4 (by rfl) ⟨975000, by rfl⟩ : syracuseStep 10400005 = 1950001) B1950001
theorem B2437451 : Blo 1080619 2437451 := bstep (se 1 (by rfl) ⟨1828088, by rfl⟩ : syracuseStep 2437451 = 3656177) B3656177
theorem B2437505 : Blo 1080619 2437505 := bstep (se 2 (by rfl) ⟨914064, by rfl⟩ : syracuseStep 2437505 = 1828129) B1828129
theorem B4108765 : Blo 1080619 4108765 := bstep (se 3 (by rfl) ⟨770393, by rfl⟩ : syracuseStep 4108765 = 1540787) B1540787
theorem B2437721 : Blo 1080619 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B2437811 : Blo 1080619 2437811 := bstep (se 1 (by rfl) ⟨1828358, by rfl⟩ : syracuseStep 2437811 = 3656717) B3656717
theorem B2437847 : Blo 1080619 2437847 := bstep (se 1 (by rfl) ⟨1828385, by rfl⟩ : syracuseStep 2437847 = 3656771) B3656771
theorem B7418699 : Blo 1080619 7418699 := bstep (se 1 (by rfl) ⟨5564024, by rfl⟩ : syracuseStep 7418699 = 11128049) B11128049
theorem B2438027 : Blo 1080619 2438027 := bstep (se 1 (by rfl) ⟨1828520, by rfl⟩ : syracuseStep 2438027 = 3657041) B3657041
theorem B2438081 : Blo 1080619 2438081 := bstep (se 2 (by rfl) ⟨914280, by rfl⟩ : syracuseStep 2438081 = 1828561) B1828561
theorem B3650507 : Blo 1080619 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B3126347 : Blo 1080619 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B5485643 : Blo 1080619 5485643 := bstep (se 1 (by rfl) ⟨4114232, by rfl⟩ : syracuseStep 5485643 = 8228465) B8228465
theorem B2438297 : Blo 1080619 2438297 := bstep (se 2 (by rfl) ⟨914361, by rfl⟩ : syracuseStep 2438297 = 1828723) B1828723
theorem B3650777 : Blo 1080619 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B2438387 : Blo 1080619 2438387 := bstep (se 1 (by rfl) ⟨1828790, by rfl⟩ : syracuseStep 2438387 = 3657581) B3657581
theorem B2438423 : Blo 1080619 2438423 := bstep (se 1 (by rfl) ⟨1828817, by rfl⟩ : syracuseStep 2438423 = 3657635) B3657635
theorem B9876811 : Blo 1080619 9876811 := bstep (se 1 (by rfl) ⟨7407608, by rfl⟩ : syracuseStep 9876811 = 14815217) B14815217
theorem B2471255 : Blo 1080619 2471255 := bstep (se 1 (by rfl) ⟨1853441, by rfl⟩ : syracuseStep 2471255 = 3706883) B3706883
theorem B6174083 : Blo 1080619 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B70268309 : Blo 1080619 70268309 := bstep (se 6 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 70268309 = 3293827) B3293827
theorem B2438603 : Blo 1080619 2438603 := bstep (se 1 (by rfl) ⟨1828952, by rfl⟩ : syracuseStep 2438603 = 3657905) B3657905
theorem B2438657 : Blo 1080619 2438657 := bstep (se 2 (by rfl) ⟨914496, by rfl⟩ : syracuseStep 2438657 = 1828993) B1828993
theorem B2930269 : Blo 1080619 2930269 := bstep (se 3 (by rfl) ⟨549425, by rfl⟩ : syracuseStep 2930269 = 1098851) B1098851
theorem B11712205 : Blo 1080619 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B2471639 : Blo 1080619 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B4110041 : Blo 1080619 4110041 := bstep (se 2 (by rfl) ⟨1541265, by rfl⟩ : syracuseStep 4110041 = 3082531) B3082531
theorem B2438873 : Blo 1080619 2438873 := bstep (se 2 (by rfl) ⟨914577, by rfl⟩ : syracuseStep 2438873 = 1829155) B1829155
theorem B2438963 : Blo 1080619 2438963 := bstep (se 1 (by rfl) ⟨1829222, by rfl⟩ : syracuseStep 2438963 = 3658445) B3658445
theorem B10565441 : Blo 1080619 10565441 := bstep (se 2 (by rfl) ⟨3962040, by rfl⟩ : syracuseStep 10565441 = 7924081) B7924081
theorem B6174539 : Blo 1080619 6174539 := bstep (se 1 (by rfl) ⟨4630904, by rfl⟩ : syracuseStep 6174539 = 9261809) B9261809
theorem B2438999 : Blo 1080619 2438999 := bstep (se 1 (by rfl) ⟨1829249, by rfl⟩ : syracuseStep 2438999 = 3658499) B3658499
theorem B3651479 : Blo 1080619 3651479 := bstep (se 1 (by rfl) ⟨2738609, by rfl⟩ : syracuseStep 3651479 = 5477219) B5477219
theorem B2439179 : Blo 1080619 2439179 := bstep (se 1 (by rfl) ⟨1829384, by rfl⟩ : syracuseStep 2439179 = 3658769) B3658769
theorem B2439233 : Blo 1080619 2439233 := bstep (se 2 (by rfl) ⟨914712, by rfl⟩ : syracuseStep 2439233 = 1829425) B1829425
theorem B3291211 : Blo 1080619 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B2439449 : Blo 1080619 2439449 := bstep (se 2 (by rfl) ⟨914793, by rfl⟩ : syracuseStep 2439449 = 1829587) B1829587
theorem B2308439 : Blo 1080619 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B2439539 : Blo 1080619 2439539 := bstep (se 1 (by rfl) ⟨1829654, by rfl⟩ : syracuseStep 2439539 = 3659309) B3659309
theorem B2439575 : Blo 1080619 2439575 := bstep (se 1 (by rfl) ⟨1829681, by rfl⟩ : syracuseStep 2439575 = 3659363) B3659363
theorem B3652019 : Blo 1080619 3652019 := bstep (se 1 (by rfl) ⟨2739014, by rfl⟩ : syracuseStep 3652019 = 5478029) B5478029
theorem B2439755 : Blo 1080619 2439755 := bstep (se 1 (by rfl) ⟨1829816, by rfl⟩ : syracuseStep 2439755 = 3659633) B3659633
theorem B2439809 : Blo 1080619 2439809 := bstep (se 2 (by rfl) ⟨914928, by rfl⟩ : syracuseStep 2439809 = 1829857) B1829857
theorem B3652289 : Blo 1080619 3652289 := bstep (se 2 (by rfl) ⟨1369608, by rfl⟩ : syracuseStep 3652289 = 2739217) B2739217
theorem B5487425 : Blo 1080619 5487425 := bstep (se 2 (by rfl) ⟨2057784, by rfl⟩ : syracuseStep 5487425 = 4115569) B4115569
theorem B2440025 : Blo 1080619 2440025 := bstep (se 2 (by rfl) ⟨915009, by rfl⟩ : syracuseStep 2440025 = 1830019) B1830019
theorem B10402739 : Blo 1080619 10402739 := bstep (se 1 (by rfl) ⟨7802054, by rfl⟩ : syracuseStep 10402739 = 15604109) B15604109
theorem B2440115 : Blo 1080619 2440115 := bstep (se 1 (by rfl) ⟨1830086, by rfl⟩ : syracuseStep 2440115 = 3660173) B3660173
theorem B2079703 : Blo 1080619 2079703 := bstep (se 1 (by rfl) ⟨1559777, by rfl⟩ : syracuseStep 2079703 = 3119555) B3119555
theorem B1620953 : Blo 1080619 1620953 := bstep (se 2 (by rfl) ⟨607857, by rfl⟩ : syracuseStep 1620953 = 1215715) B1215715
theorem B2440151 : Blo 1080619 2440151 := bstep (se 1 (by rfl) ⟨1830113, by rfl⟩ : syracuseStep 2440151 = 3660227) B3660227
theorem B1621067 : Blo 1080619 1621067 := bstep (se 1 (by rfl) ⟨1215800, by rfl⟩ : syracuseStep 1621067 = 2431601) B2431601
theorem B1621079 : Blo 1080619 1621079 := bstep (se 1 (by rfl) ⟨1215809, by rfl⟩ : syracuseStep 1621079 = 2431619) B2431619
theorem B2440331 : Blo 1080619 2440331 := bstep (se 1 (by rfl) ⟨1830248, by rfl⟩ : syracuseStep 2440331 = 3660497) B3660497
theorem B5192855 : Blo 1080619 5192855 := bstep (se 1 (by rfl) ⟨3894641, by rfl⟩ : syracuseStep 5192855 = 7789283) B7789283
theorem B1621145 : Blo 1080619 1621145 := bstep (se 2 (by rfl) ⟨607929, by rfl⟩ : syracuseStep 1621145 = 1215859) B1215859
theorem B2440385 : Blo 1080619 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B3652829 : Blo 1080619 3652829 := bstep (se 3 (by rfl) ⟨684905, by rfl⟩ : syracuseStep 3652829 = 1369811) B1369811
theorem B1621259 : Blo 1080619 1621259 := bstep (se 1 (by rfl) ⟨1215944, by rfl⟩ : syracuseStep 1621259 = 2431889) B2431889
theorem B1621271 : Blo 1080619 1621271 := bstep (se 1 (by rfl) ⟨1215953, by rfl⟩ : syracuseStep 1621271 = 2431907) B2431907
theorem B4111667 : Blo 1080619 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B4111681 : Blo 1080619 4111681 := bstep (se 2 (by rfl) ⟨1541880, by rfl⟩ : syracuseStep 4111681 = 3083761) B3083761
theorem B1621337 : Blo 1080619 1621337 := bstep (se 2 (by rfl) ⟨608001, by rfl⟩ : syracuseStep 1621337 = 1216003) B1216003
theorem B2309465 : Blo 1080619 2309465 := bstep (se 2 (by rfl) ⟨866049, by rfl⟩ : syracuseStep 2309465 = 1732099) B1732099
theorem B1621451 : Blo 1080619 1621451 := bstep (se 1 (by rfl) ⟨1216088, by rfl⟩ : syracuseStep 1621451 = 2432177) B2432177
theorem B1621463 : Blo 1080619 1621463 := bstep (se 1 (by rfl) ⟨1216097, by rfl⟩ : syracuseStep 1621463 = 2432195) B2432195
theorem B15580633 : Blo 1080619 15580633 := bstep (se 2 (by rfl) ⟨5842737, by rfl⟩ : syracuseStep 15580633 = 11685475) B11685475
theorem B1621529 : Blo 1080619 1621529 := bstep (se 2 (by rfl) ⟨608073, by rfl⟩ : syracuseStep 1621529 = 1216147) B1216147
theorem B1621643 : Blo 1080619 1621643 := bstep (se 1 (by rfl) ⟨1216232, by rfl⟩ : syracuseStep 1621643 = 2432465) B2432465
theorem B1621655 : Blo 1080619 1621655 := bstep (se 1 (by rfl) ⟨1216241, by rfl⟩ : syracuseStep 1621655 = 2432483) B2432483
theorem B2735795 : Blo 1080619 2735795 := bstep (se 1 (by rfl) ⟨2051846, by rfl⟩ : syracuseStep 2735795 = 4103693) B4103693
theorem B1621721 : Blo 1080619 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B1621835 : Blo 1080619 1621835 := bstep (se 1 (by rfl) ⟨1216376, by rfl⟩ : syracuseStep 1621835 = 2432753) B2432753
theorem B1621847 : Blo 1080619 1621847 := bstep (se 1 (by rfl) ⟨1216385, by rfl⟩ : syracuseStep 1621847 = 2432771) B2432771
theorem B1621913 : Blo 1080619 1621913 := bstep (se 2 (by rfl) ⟨608217, by rfl⟩ : syracuseStep 1621913 = 1216435) B1216435
theorem B2736089 : Blo 1080619 2736089 := bstep (se 2 (by rfl) ⟨1026033, by rfl⟩ : syracuseStep 2736089 = 2052067) B2052067
theorem B1622027 : Blo 1080619 1622027 := bstep (se 1 (by rfl) ⟨1216520, by rfl⟩ : syracuseStep 1622027 = 2433041) B2433041
theorem B1949707 : Blo 1080619 1949707 := bstep (se 1 (by rfl) ⟨1462280, by rfl⟩ : syracuseStep 1949707 = 2924561) B2924561
theorem B1622039 : Blo 1080619 1622039 := bstep (se 1 (by rfl) ⟨1216529, by rfl⟩ : syracuseStep 1622039 = 2433059) B2433059
theorem B30883909 : Blo 1080619 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B1622105 : Blo 1080619 1622105 := bstep (se 2 (by rfl) ⟨608289, by rfl⟩ : syracuseStep 1622105 = 1216579) B1216579
theorem B1622219 : Blo 1080619 1622219 := bstep (se 1 (by rfl) ⟨1216664, by rfl⟩ : syracuseStep 1622219 = 2433329) B2433329
theorem B1622231 : Blo 1080619 1622231 := bstep (se 1 (by rfl) ⟨1216673, by rfl⟩ : syracuseStep 1622231 = 2433347) B2433347
theorem B1622297 : Blo 1080619 1622297 := bstep (se 2 (by rfl) ⟨608361, by rfl⟩ : syracuseStep 1622297 = 1216723) B1216723
theorem B3653963 : Blo 1080619 3653963 := bstep (se 1 (by rfl) ⟨2740472, by rfl⟩ : syracuseStep 3653963 = 5480945) B5480945
theorem B2310515 : Blo 1080619 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B1622411 : Blo 1080619 1622411 := bstep (se 1 (by rfl) ⟨1216808, by rfl⟩ : syracuseStep 1622411 = 2433617) B2433617
theorem B1622423 : Blo 1080619 1622423 := bstep (se 1 (by rfl) ⟨1216817, by rfl⟩ : syracuseStep 1622423 = 2433635) B2433635
theorem B1622489 : Blo 1080619 1622489 := bstep (se 2 (by rfl) ⟨608433, by rfl⟩ : syracuseStep 1622489 = 1216867) B1216867
theorem B1950169 : Blo 1080619 1950169 := bstep (se 2 (by rfl) ⟨731313, by rfl⟩ : syracuseStep 1950169 = 1462627) B1462627
theorem B2081305 : Blo 1080619 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B1622603 : Blo 1080619 1622603 := bstep (se 1 (by rfl) ⟨1216952, by rfl⟩ : syracuseStep 1622603 = 2433905) B2433905
theorem B1851979 : Blo 1080619 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B1622615 : Blo 1080619 1622615 := bstep (se 1 (by rfl) ⟨1216961, by rfl⟩ : syracuseStep 1622615 = 2433923) B2433923
theorem B3654233 : Blo 1080619 3654233 := bstep (se 2 (by rfl) ⟨1370337, by rfl⟩ : syracuseStep 3654233 = 2740675) B2740675
theorem B1622681 : Blo 1080619 1622681 := bstep (se 2 (by rfl) ⟨608505, by rfl⟩ : syracuseStep 1622681 = 1217011) B1217011
theorem B5489369 : Blo 1080619 5489369 := bstep (se 2 (by rfl) ⟨2058513, by rfl⟩ : syracuseStep 5489369 = 4117027) B4117027
theorem B1622795 : Blo 1080619 1622795 := bstep (se 1 (by rfl) ⟨1217096, by rfl⟩ : syracuseStep 1622795 = 2434193) B2434193
theorem B1622807 : Blo 1080619 1622807 := bstep (se 1 (by rfl) ⟨1217105, by rfl⟩ : syracuseStep 1622807 = 2434211) B2434211
theorem B1622873 : Blo 1080619 1622873 := bstep (se 2 (by rfl) ⟨608577, by rfl⟩ : syracuseStep 1622873 = 1217155) B1217155
theorem B2311105 : Blo 1080619 2311105 := bstep (se 2 (by rfl) ⟨866664, by rfl⟩ : syracuseStep 2311105 = 1733329) B1733329
theorem B1622987 : Blo 1080619 1622987 := bstep (se 1 (by rfl) ⟨1217240, by rfl⟩ : syracuseStep 1622987 = 2434481) B2434481
theorem B1622999 : Blo 1080619 1622999 := bstep (se 1 (by rfl) ⟨1217249, by rfl⟩ : syracuseStep 1622999 = 2434499) B2434499
theorem B4932569 : Blo 1080619 4932569 := bstep (se 2 (by rfl) ⟨1849713, by rfl⟩ : syracuseStep 4932569 = 3699427) B3699427
theorem B1623065 : Blo 1080619 1623065 := bstep (se 2 (by rfl) ⟨608649, by rfl⟩ : syracuseStep 1623065 = 1217299) B1217299
theorem B1950745 : Blo 1080619 1950745 := bstep (se 2 (by rfl) ⟨731529, by rfl⟩ : syracuseStep 1950745 = 1463059) B1463059
theorem B5850157 : Blo 1080619 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B1623179 : Blo 1080619 1623179 := bstep (se 1 (by rfl) ⟨1217384, by rfl⟩ : syracuseStep 1623179 = 2434769) B2434769
theorem B1623191 : Blo 1080619 1623191 := bstep (se 1 (by rfl) ⟨1217393, by rfl⟩ : syracuseStep 1623191 = 2434787) B2434787
theorem B4113611 : Blo 1080619 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B1623257 : Blo 1080619 1623257 := bstep (se 2 (by rfl) ⟨608721, by rfl⟩ : syracuseStep 1623257 = 1217443) B1217443
theorem B4113625 : Blo 1080619 4113625 := bstep (se 2 (by rfl) ⟨1542609, by rfl⟩ : syracuseStep 4113625 = 3085219) B3085219
theorem B3654935 : Blo 1080619 3654935 := bstep (se 1 (by rfl) ⟨2741201, by rfl⟩ : syracuseStep 3654935 = 5482403) B5482403
theorem B2114881 : Blo 1080619 2114881 := bstep (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) B1586161
theorem B1623371 : Blo 1080619 1623371 := bstep (se 1 (by rfl) ⟨1217528, by rfl⟩ : syracuseStep 1623371 = 2435057) B2435057
theorem B1623383 : Blo 1080619 1623383 := bstep (se 1 (by rfl) ⟨1217537, by rfl⟩ : syracuseStep 1623383 = 2435075) B2435075
theorem B1623449 : Blo 1080619 1623449 := bstep (se 2 (by rfl) ⟨608793, by rfl⟩ : syracuseStep 1623449 = 1217587) B1217587
theorem B1099211 : Blo 1080619 1099211 := bstep (se 1 (by rfl) ⟨824408, by rfl⟩ : syracuseStep 1099211 = 1648817) B1648817
theorem B1623563 : Blo 1080619 1623563 := bstep (se 1 (by rfl) ⟨1217672, by rfl⟩ : syracuseStep 1623563 = 2435345) B2435345
theorem B1623575 : Blo 1080619 1623575 := bstep (se 1 (by rfl) ⟨1217681, by rfl⟩ : syracuseStep 1623575 = 2435363) B2435363
theorem B2737739 : Blo 1080619 2737739 := bstep (se 1 (by rfl) ⟨2053304, by rfl⟩ : syracuseStep 2737739 = 4106609) B4106609
theorem B1623641 : Blo 1080619 1623641 := bstep (se 2 (by rfl) ⟨608865, by rfl⟩ : syracuseStep 1623641 = 1217731) B1217731
theorem B62473841 : Blo 1080619 62473841 := bstep (se 2 (by rfl) ⟨23427690, by rfl⟩ : syracuseStep 62473841 = 46855381) B46855381
theorem B1951385 : Blo 1080619 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B1623755 : Blo 1080619 1623755 := bstep (se 1 (by rfl) ⟨1217816, by rfl⟩ : syracuseStep 1623755 = 2435633) B2435633
theorem B1623767 : Blo 1080619 1623767 := bstep (se 1 (by rfl) ⟨1217825, by rfl⟩ : syracuseStep 1623767 = 2435651) B2435651
theorem B1623833 : Blo 1080619 1623833 := bstep (se 2 (by rfl) ⟨608937, by rfl⟩ : syracuseStep 1623833 = 1217875) B1217875
theorem B3655475 : Blo 1080619 3655475 := bstep (se 1 (by rfl) ⟨2741606, by rfl⟩ : syracuseStep 3655475 = 5483213) B5483213
theorem B1951553 : Blo 1080619 1951553 := bstep (se 2 (by rfl) ⟨731832, by rfl⟩ : syracuseStep 1951553 = 1463665) B1463665
theorem B1623947 : Blo 1080619 1623947 := bstep (se 1 (by rfl) ⟨1217960, by rfl⟩ : syracuseStep 1623947 = 2435921) B2435921
theorem B1623959 : Blo 1080619 1623959 := bstep (se 1 (by rfl) ⟨1217969, by rfl⟩ : syracuseStep 1623959 = 2435939) B2435939
theorem B1624025 : Blo 1080619 1624025 := bstep (se 2 (by rfl) ⟨609009, by rfl⟩ : syracuseStep 1624025 = 1218019) B1218019
theorem B15812621 : Blo 1080619 15812621 := bstep (se 3 (by rfl) ⟨2964866, by rfl⟩ : syracuseStep 15812621 = 5929733) B5929733
theorem B3655745 : Blo 1080619 3655745 := bstep (se 2 (by rfl) ⟨1370904, by rfl⟩ : syracuseStep 3655745 = 2741809) B2741809
theorem B1624139 : Blo 1080619 1624139 := bstep (se 1 (by rfl) ⟨1218104, by rfl⟩ : syracuseStep 1624139 = 2436209) B2436209
theorem B1624151 : Blo 1080619 1624151 := bstep (se 1 (by rfl) ⟨1218113, by rfl⟩ : syracuseStep 1624151 = 2436227) B2436227
theorem B1853579 : Blo 1080619 1853579 := bstep (se 1 (by rfl) ⟨1390184, by rfl⟩ : syracuseStep 1853579 = 2780369) B2780369
theorem B4114583 : Blo 1080619 4114583 := bstep (se 1 (by rfl) ⟨3085937, by rfl⟩ : syracuseStep 4114583 = 6171875) B6171875
theorem B1624217 : Blo 1080619 1624217 := bstep (se 2 (by rfl) ⟨609081, by rfl⟩ : syracuseStep 1624217 = 1218163) B1218163
theorem B1624331 : Blo 1080619 1624331 := bstep (se 1 (by rfl) ⟨1218248, by rfl⟩ : syracuseStep 1624331 = 2436497) B2436497
theorem B1624343 : Blo 1080619 1624343 := bstep (se 1 (by rfl) ⟨1218257, by rfl⟩ : syracuseStep 1624343 = 2436515) B2436515
theorem B1624409 : Blo 1080619 1624409 := bstep (se 2 (by rfl) ⟨609153, by rfl⟩ : syracuseStep 1624409 = 1218307) B1218307
theorem B2312651 : Blo 1080619 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B1624523 : Blo 1080619 1624523 := bstep (se 1 (by rfl) ⟨1218392, by rfl⟩ : syracuseStep 1624523 = 2436785) B2436785
theorem B1624535 : Blo 1080619 1624535 := bstep (se 1 (by rfl) ⟨1218401, by rfl⟩ : syracuseStep 1624535 = 2436803) B2436803
theorem B2738711 : Blo 1080619 2738711 := bstep (se 1 (by rfl) ⟨2054033, by rfl⟩ : syracuseStep 2738711 = 4108067) B4108067
theorem B1624601 : Blo 1080619 1624601 := bstep (se 2 (by rfl) ⟨609225, by rfl⟩ : syracuseStep 1624601 = 1218451) B1218451
theorem B3656285 : Blo 1080619 3656285 := bstep (se 3 (by rfl) ⟨685553, by rfl⟩ : syracuseStep 3656285 = 1371107) B1371107
theorem B1624715 : Blo 1080619 1624715 := bstep (se 1 (by rfl) ⟨1218536, by rfl⟩ : syracuseStep 1624715 = 2437073) B2437073
theorem B1624727 : Blo 1080619 1624727 := bstep (se 1 (by rfl) ⟨1218545, by rfl⟩ : syracuseStep 1624727 = 2437091) B2437091
theorem B5196467 : Blo 1080619 5196467 := bstep (se 1 (by rfl) ⟨3897350, by rfl⟩ : syracuseStep 5196467 = 7794701) B7794701
theorem B1624793 : Blo 1080619 1624793 := bstep (se 2 (by rfl) ⟨609297, by rfl⟩ : syracuseStep 1624793 = 1218595) B1218595
theorem B31214321 : Blo 1080619 31214321 := bstep (se 2 (by rfl) ⟨11705370, by rfl⟩ : syracuseStep 31214321 = 23410741) B23410741
theorem B18729793 : Blo 1080619 18729793 := bstep (se 2 (by rfl) ⟨7023672, by rfl⟩ : syracuseStep 18729793 = 14047345) B14047345
theorem B1624907 : Blo 1080619 1624907 := bstep (se 1 (by rfl) ⟨1218680, by rfl⟩ : syracuseStep 1624907 = 2437361) B2437361
theorem B1624919 : Blo 1080619 1624919 := bstep (se 1 (by rfl) ⟨1218689, by rfl⟩ : syracuseStep 1624919 = 2437379) B2437379
theorem B5557123 : Blo 1080619 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B1624985 : Blo 1080619 1624985 := bstep (se 2 (by rfl) ⟨609369, by rfl⟩ : syracuseStep 1624985 = 1218739) B1218739
theorem B1625099 : Blo 1080619 1625099 := bstep (se 1 (by rfl) ⟨1218824, by rfl⟩ : syracuseStep 1625099 = 2437649) B2437649
theorem B1625111 : Blo 1080619 1625111 := bstep (se 1 (by rfl) ⟨1218833, by rfl⟩ : syracuseStep 1625111 = 2437667) B2437667
theorem B1625177 : Blo 1080619 1625177 := bstep (se 2 (by rfl) ⟨609441, by rfl⟩ : syracuseStep 1625177 = 1218883) B1218883
theorem B2739379 : Blo 1080619 2739379 := bstep (se 1 (by rfl) ⟨2054534, by rfl⟩ : syracuseStep 2739379 = 4109069) B4109069
theorem B1625291 : Blo 1080619 1625291 := bstep (se 1 (by rfl) ⟨1218968, by rfl⟩ : syracuseStep 1625291 = 2437937) B2437937
theorem B1625303 : Blo 1080619 1625303 := bstep (se 1 (by rfl) ⟨1218977, by rfl⟩ : syracuseStep 1625303 = 2437955) B2437955
theorem B2313497 : Blo 1080619 2313497 := bstep (se 2 (by rfl) ⟨867561, by rfl⟩ : syracuseStep 2313497 = 1735123) B1735123
theorem B1625369 : Blo 1080619 1625369 := bstep (se 2 (by rfl) ⟨609513, by rfl⟩ : syracuseStep 1625369 = 1219027) B1219027
theorem B2739521 : Blo 1080619 2739521 := bstep (se 2 (by rfl) ⟨1027320, by rfl⟩ : syracuseStep 2739521 = 2054641) B2054641
theorem B4115843 : Blo 1080619 4115843 := bstep (se 1 (by rfl) ⟨3086882, by rfl⟩ : syracuseStep 4115843 = 6173765) B6173765
theorem B1625483 : Blo 1080619 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B1625495 : Blo 1080619 1625495 := bstep (se 1 (by rfl) ⟨1219121, by rfl⟩ : syracuseStep 1625495 = 2438243) B2438243
theorem B2051543 : Blo 1080619 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B2346455 : Blo 1080619 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B1625561 : Blo 1080619 1625561 := bstep (se 2 (by rfl) ⟨609585, by rfl⟩ : syracuseStep 1625561 = 1219171) B1219171
theorem B1625675 : Blo 1080619 1625675 := bstep (se 1 (by rfl) ⟨1219256, by rfl⟩ : syracuseStep 1625675 = 2438513) B2438513
theorem B1625687 : Blo 1080619 1625687 := bstep (se 1 (by rfl) ⟨1219265, by rfl⟩ : syracuseStep 1625687 = 2438531) B2438531
theorem B1560217 : Blo 1080619 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B1625753 : Blo 1080619 1625753 := bstep (se 2 (by rfl) ⟨609657, by rfl⟩ : syracuseStep 1625753 = 1219315) B1219315
theorem B1953433 : Blo 1080619 1953433 := bstep (se 2 (by rfl) ⟨732537, by rfl⟩ : syracuseStep 1953433 = 1465075) B1465075
theorem B3657419 : Blo 1080619 3657419 := bstep (se 1 (by rfl) ⟨2743064, by rfl⟩ : syracuseStep 3657419 = 5486129) B5486129
theorem B2051801 : Blo 1080619 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B1625867 : Blo 1080619 1625867 := bstep (se 1 (by rfl) ⟨1219400, by rfl⟩ : syracuseStep 1625867 = 2438801) B2438801
theorem B1625879 : Blo 1080619 1625879 := bstep (se 1 (by rfl) ⟨1219409, by rfl⟩ : syracuseStep 1625879 = 2438819) B2438819
theorem B5001049 : Blo 1080619 5001049 := bstep (se 2 (by rfl) ⟨1875393, by rfl⟩ : syracuseStep 5001049 = 3750787) B3750787
theorem B1625945 : Blo 1080619 1625945 := bstep (se 2 (by rfl) ⟨609729, by rfl⟩ : syracuseStep 1625945 = 1219459) B1219459
theorem B1626059 : Blo 1080619 1626059 := bstep (se 1 (by rfl) ⟨1219544, by rfl⟩ : syracuseStep 1626059 = 2439089) B2439089
theorem B1626071 : Blo 1080619 1626071 := bstep (se 1 (by rfl) ⟨1219553, by rfl⟩ : syracuseStep 1626071 = 2439107) B2439107
theorem B3657689 : Blo 1080619 3657689 := bstep (se 2 (by rfl) ⟨1371633, by rfl⟩ : syracuseStep 3657689 = 2743267) B2743267
theorem B1626137 : Blo 1080619 1626137 := bstep (se 2 (by rfl) ⟨609801, by rfl⟩ : syracuseStep 1626137 = 1219603) B1219603
theorem B2314291 : Blo 1080619 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B2052211 : Blo 1080619 2052211 := bstep (se 1 (by rfl) ⟨1539158, by rfl⟩ : syracuseStep 2052211 = 3078317) B3078317
theorem B1626251 : Blo 1080619 1626251 := bstep (se 1 (by rfl) ⟨1219688, by rfl⟩ : syracuseStep 1626251 = 2439377) B2439377
theorem B11260055 : Blo 1080619 11260055 := bstep (se 1 (by rfl) ⟨8445041, by rfl⟩ : syracuseStep 11260055 = 16890083) B16890083
theorem B1626263 : Blo 1080619 1626263 := bstep (se 1 (by rfl) ⟨1219697, by rfl⟩ : syracuseStep 1626263 = 2439395) B2439395
theorem B1626329 : Blo 1080619 1626329 := bstep (se 2 (by rfl) ⟨609873, by rfl⟩ : syracuseStep 1626329 = 1219747) B1219747
theorem B1626443 : Blo 1080619 1626443 := bstep (se 1 (by rfl) ⟨1219832, by rfl⟩ : syracuseStep 1626443 = 2439665) B2439665
theorem B1626455 : Blo 1080619 1626455 := bstep (se 1 (by rfl) ⟨1219841, by rfl⟩ : syracuseStep 1626455 = 2439683) B2439683
theorem B1626521 : Blo 1080619 1626521 := bstep (se 2 (by rfl) ⟨609945, by rfl⟩ : syracuseStep 1626521 = 1219891) B1219891
theorem B8212913 : Blo 1080619 8212913 := bstep (se 2 (by rfl) ⟨3079842, by rfl⟩ : syracuseStep 8212913 = 6159685) B6159685
theorem B1626635 : Blo 1080619 1626635 := bstep (se 1 (by rfl) ⟨1219976, by rfl⟩ : syracuseStep 1626635 = 2439953) B2439953
theorem B1626647 : Blo 1080619 1626647 := bstep (se 1 (by rfl) ⟨1219985, by rfl⟩ : syracuseStep 1626647 = 2439971) B2439971
theorem B2740787 : Blo 1080619 2740787 := bstep (se 1 (by rfl) ⟨2055590, by rfl⟩ : syracuseStep 2740787 = 4111181) B4111181
theorem B2052697 : Blo 1080619 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B1626713 : Blo 1080619 1626713 := bstep (se 2 (by rfl) ⟨610017, by rfl⟩ : syracuseStep 1626713 = 1220035) B1220035
theorem B3658391 : Blo 1080619 3658391 := bstep (se 1 (by rfl) ⟨2743793, by rfl⟩ : syracuseStep 3658391 = 5487587) B5487587
theorem B1954457 : Blo 1080619 1954457 := bstep (se 2 (by rfl) ⟨732921, by rfl⟩ : syracuseStep 1954457 = 1465843) B1465843
theorem B1626827 : Blo 1080619 1626827 := bstep (se 1 (by rfl) ⟨1220120, by rfl⟩ : syracuseStep 1626827 = 2440241) B2440241
theorem B1626839 : Blo 1080619 1626839 := bstep (se 1 (by rfl) ⟨1220129, by rfl⟩ : syracuseStep 1626839 = 2440259) B2440259
theorem B1626905 : Blo 1080619 1626905 := bstep (se 2 (by rfl) ⟨610089, by rfl⟩ : syracuseStep 1626905 = 1220179) B1220179
theorem B3461953 : Blo 1080619 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B2773835 : Blo 1080619 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B2315137 : Blo 1080619 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B1823627 : Blo 1080619 1823627 := bstep (se 1 (by rfl) ⟨1367720, by rfl⟩ : syracuseStep 1823627 = 2735441) B2735441
theorem B8213399 : Blo 1080619 8213399 := bstep (se 1 (by rfl) ⟨6160049, by rfl⟩ : syracuseStep 8213399 = 12320099) B12320099
theorem B1823755 : Blo 1080619 1823755 := bstep (se 1 (by rfl) ⟨1367816, by rfl⟩ : syracuseStep 1823755 = 2735633) B2735633
theorem B2741323 : Blo 1080619 2741323 := bstep (se 1 (by rfl) ⟨2055992, by rfl⟩ : syracuseStep 2741323 = 4111985) B4111985
theorem B6935645 : Blo 1080619 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B2053259 : Blo 1080619 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B1823897 : Blo 1080619 1823897 := bstep (se 2 (by rfl) ⟨683961, by rfl⟩ : syracuseStep 1823897 = 1367923) B1367923
theorem B3658931 : Blo 1080619 3658931 := bstep (se 1 (by rfl) ⟨2744198, by rfl⟩ : syracuseStep 3658931 = 5488397) B5488397
theorem B2315479 : Blo 1080619 2315479 := bstep (se 1 (by rfl) ⟨1736609, by rfl⟩ : syracuseStep 2315479 = 3473219) B3473219
theorem B2741465 : Blo 1080619 2741465 := bstep (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) B2056099
theorem B1824025 : Blo 1080619 1824025 := bstep (se 2 (by rfl) ⟨684009, by rfl⟩ : syracuseStep 1824025 = 1368019) B1368019
theorem B2053441 : Blo 1080619 2053441 := bstep (se 2 (by rfl) ⟨770040, by rfl⟩ : syracuseStep 2053441 = 1540081) B1540081
theorem B3659201 : Blo 1080619 3659201 := bstep (se 2 (by rfl) ⟨1372200, by rfl⟩ : syracuseStep 3659201 = 2744401) B2744401
theorem B5855021 : Blo 1080619 5855021 := bstep (se 3 (by rfl) ⟨1097816, by rfl⟩ : syracuseStep 5855021 = 2195633) B2195633
theorem B1824599 : Blo 1080619 1824599 := bstep (se 1 (by rfl) ⟨1368449, by rfl⟩ : syracuseStep 1824599 = 2736899) B2736899
theorem B1824727 : Blo 1080619 1824727 := bstep (se 1 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 1824727 = 2737091) B2737091
theorem B3659741 : Blo 1080619 3659741 := bstep (se 3 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 3659741 = 1372403) B1372403
theorem B2054155 : Blo 1080619 2054155 := bstep (se 1 (by rfl) ⟨1540616, by rfl⟩ : syracuseStep 2054155 = 3081233) B3081233
theorem B5199889 : Blo 1080619 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B2742295 : Blo 1080619 2742295 := bstep (se 1 (by rfl) ⟨2056721, by rfl⟩ : syracuseStep 2742295 = 4113443) B4113443
theorem B42195019 : Blo 1080619 42195019 := bstep (se 1 (by rfl) ⟨31646264, by rfl⟩ : syracuseStep 42195019 = 63292529) B63292529
theorem B2054231 : Blo 1080619 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B12343427 : Blo 1080619 12343427 := bstep (se 1 (by rfl) ⟨9257570, by rfl⟩ : syracuseStep 12343427 = 18515141) B18515141
theorem B2742731 : Blo 1080619 2742731 := bstep (se 1 (by rfl) ⟨2057048, by rfl⟩ : syracuseStep 2742731 = 4114097) B4114097
theorem B9361955 : Blo 1080619 9361955 := bstep (se 1 (by rfl) ⟨7021466, by rfl⟩ : syracuseStep 9361955 = 14042933) B14042933
theorem B1825355 : Blo 1080619 1825355 := bstep (se 1 (by rfl) ⟨1369016, by rfl⟩ : syracuseStep 1825355 = 2738033) B2738033
theorem B1825483 : Blo 1080619 1825483 := bstep (se 1 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 1825483 = 2738225) B2738225
theorem B3463901 : Blo 1080619 3463901 := bstep (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) B1298963
theorem B2054899 : Blo 1080619 2054899 := bstep (se 1 (by rfl) ⟨1541174, by rfl⟩ : syracuseStep 2054899 = 3082349) B3082349
theorem B2743105 : Blo 1080619 2743105 := bstep (se 2 (by rfl) ⟨1028664, by rfl⟩ : syracuseStep 2743105 = 2057329) B2057329
theorem B1825625 : Blo 1080619 1825625 := bstep (se 2 (by rfl) ⟨684609, by rfl⟩ : syracuseStep 1825625 = 1369219) B1369219
theorem B2055127 : Blo 1080619 2055127 := bstep (se 1 (by rfl) ⟨1541345, by rfl⟩ : syracuseStep 2055127 = 3082691) B3082691
theorem B1825753 : Blo 1080619 1825753 := bstep (se 2 (by rfl) ⟨684657, by rfl⟩ : syracuseStep 1825753 = 1369315) B1369315
theorem B5135425 : Blo 1080619 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B2055233 : Blo 1080619 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B5856407 : Blo 1080619 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B2055385 : Blo 1080619 2055385 := bstep (se 2 (by rfl) ⟨770769, by rfl⟩ : syracuseStep 2055385 = 1541539) B1541539
theorem B8772929 : Blo 1080619 8772929 := bstep (se 2 (by rfl) ⟨3289848, by rfl⟩ : syracuseStep 8772929 = 6579697) B6579697
theorem B2743703 : Blo 1080619 2743703 := bstep (se 1 (by rfl) ⟨2057777, by rfl⟩ : syracuseStep 2743703 = 4115555) B4115555
theorem B1826327 : Blo 1080619 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B1826455 : Blo 1080619 1826455 := bstep (se 1 (by rfl) ⟨1369841, by rfl⟩ : syracuseStep 1826455 = 2739683) B2739683
theorem B2744513 : Blo 1080619 2744513 := bstep (se 2 (by rfl) ⟨1029192, by rfl⟩ : syracuseStep 2744513 = 2058385) B2058385
theorem B7921925 : Blo 1080619 7921925 := bstep (se 4 (by rfl) ⟨742680, by rfl⟩ : syracuseStep 7921925 = 1485361) B1485361
theorem B1827083 : Blo 1080619 1827083 := bstep (se 1 (by rfl) ⟨1370312, by rfl⟩ : syracuseStep 1827083 = 2740625) B2740625
theorem B1368343 : Blo 1080619 1368343 := bstep (se 1 (by rfl) ⟨1026257, by rfl⟩ : syracuseStep 1368343 = 2052515) B2052515
theorem B1827211 : Blo 1080619 1827211 := bstep (se 1 (by rfl) ⟨1370408, by rfl⟩ : syracuseStep 1827211 = 2740817) B2740817
theorem B2056691 : Blo 1080619 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B1827353 : Blo 1080619 1827353 := bstep (se 2 (by rfl) ⟨685257, by rfl⟩ : syracuseStep 1827353 = 1370515) B1370515
theorem B2056843 : Blo 1080619 2056843 := bstep (se 1 (by rfl) ⟨1542632, by rfl⟩ : syracuseStep 2056843 = 3085265) B3085265
theorem B1827481 : Blo 1080619 1827481 := bstep (se 2 (by rfl) ⟨685305, by rfl⟩ : syracuseStep 1827481 = 1370611) B1370611
theorem B2745049 : Blo 1080619 2745049 := bstep (se 2 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 2745049 = 2058787) B2058787
theorem B2057177 : Blo 1080619 2057177 := bstep (se 2 (by rfl) ⟨771441, by rfl⟩ : syracuseStep 2057177 = 1542883) B1542883
theorem B2253889 : Blo 1080619 2253889 := bstep (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) B1690417
theorem B1369163 : Blo 1080619 1369163 := bstep (se 1 (by rfl) ⟨1026872, by rfl⟩ : syracuseStep 1369163 = 2053745) B2053745
theorem B1828055 : Blo 1080619 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B1828183 : Blo 1080619 1828183 := bstep (se 1 (by rfl) ⟨1371137, by rfl⟩ : syracuseStep 1828183 = 2742275) B2742275
theorem B7792163 : Blo 1080619 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B5563979 : Blo 1080619 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B2057815 : Blo 1080619 2057815 := bstep (se 1 (by rfl) ⟨1543361, by rfl⟩ : syracuseStep 2057815 = 3086723) B3086723
theorem B1369867 : Blo 1080619 1369867 := bstep (se 1 (by rfl) ⟨1027400, by rfl⟩ : syracuseStep 1369867 = 2054801) B2054801
theorem B4384685 : Blo 1080619 4384685 := bstep (se 3 (by rfl) ⟨822128, by rfl⟩ : syracuseStep 4384685 = 1644257) B1644257
theorem B1828811 : Blo 1080619 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B1370135 : Blo 1080619 1370135 := bstep (se 1 (by rfl) ⟨1027601, by rfl⟩ : syracuseStep 1370135 = 2055203) B2055203
theorem B4384813 : Blo 1080619 4384813 := bstep (se 3 (by rfl) ⟨822152, by rfl⟩ : syracuseStep 4384813 = 1644305) B1644305
theorem B1828939 : Blo 1080619 1828939 := bstep (se 1 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 1828939 = 2743409) B2743409
theorem B20834455 : Blo 1080619 20834455 := bstep (se 1 (by rfl) ⟨15625841, by rfl⟩ : syracuseStep 20834455 = 31251683) B31251683
theorem B1829081 : Blo 1080619 1829081 := bstep (se 2 (by rfl) ⟨685905, by rfl⟩ : syracuseStep 1829081 = 1371811) B1371811
theorem B1829209 : Blo 1080619 1829209 := bstep (se 2 (by rfl) ⟨685953, by rfl⟩ : syracuseStep 1829209 = 1371907) B1371907
theorem B2058635 : Blo 1080619 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B2058689 : Blo 1080619 2058689 := bstep (se 2 (by rfl) ⟨772008, by rfl⟩ : syracuseStep 2058689 = 1544017) B1544017
theorem B1370839 : Blo 1080619 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B1829783 : Blo 1080619 1829783 := bstep (se 1 (by rfl) ⟨1372337, by rfl⟩ : syracuseStep 1829783 = 2744675) B2744675
theorem B1829911 : Blo 1080619 1829911 := bstep (se 1 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 1829911 = 2744867) B2744867
theorem B6155585 : Blo 1080619 6155585 := bstep (se 2 (by rfl) ⟨2308344, by rfl⟩ : syracuseStep 6155585 = 4616689) B4616689
theorem B6942131 : Blo 1080619 6942131 := bstep (se 1 (by rfl) ⟨5206598, by rfl⟩ : syracuseStep 6942131 = 10413197) B10413197
theorem B3894929 : Blo 1080619 3894929 := bstep (se 2 (by rfl) ⟨1460598, by rfl⟩ : syracuseStep 3894929 = 2921197) B2921197
theorem B8220689 : Blo 1080619 8220689 := bstep (se 2 (by rfl) ⟨3082758, by rfl⟩ : syracuseStep 8220689 = 6165517) B6165517
theorem B5009501 : Blo 1080619 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B2191475 : Blo 1080619 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B3469463 : Blo 1080619 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B1372555 : Blo 1080619 1372555 := bstep (se 1 (by rfl) ⟨1029416, by rfl⟩ : syracuseStep 1372555 = 2058833) B2058833
theorem B4616621 : Blo 1080619 4616621 := bstep (se 3 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 4616621 = 1731233) B1731233
theorem B1667609 : Blo 1080619 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B94958173 : Blo 1080619 94958173 := bstep (se 3 (by rfl) ⟨17804657, by rfl⟩ : syracuseStep 94958173 = 35609315) B35609315
theorem B4616963 : Blo 1080619 4616963 := bstep (se 1 (by rfl) ⟨3462722, by rfl⟩ : syracuseStep 4616963 = 6925445) B6925445
theorem B9237341 : Blo 1080619 9237341 := bstep (se 3 (by rfl) ⟨1732001, by rfl⟩ : syracuseStep 9237341 = 3464003) B3464003
theorem B6943589 : Blo 1080619 6943589 := bstep (se 4 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 6943589 = 1301923) B1301923
theorem B5206963 : Blo 1080619 5206963 := bstep (se 1 (by rfl) ⟨3905222, by rfl⟩ : syracuseStep 5206963 = 7810445) B7810445
theorem B1733591 : Blo 1080619 1733591 := bstep (se 1 (by rfl) ⟨1300193, by rfl⟩ : syracuseStep 1733591 = 2600387) B2600387
theorem B3470359 : Blo 1080619 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B1733719 : Blo 1080619 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B13891277 : Blo 1080619 13891277 := bstep (se 3 (by rfl) ⟨2604614, by rfl⟩ : syracuseStep 13891277 = 5209229) B5209229
theorem B3471179 : Blo 1080619 3471179 := bstep (se 1 (by rfl) ⟨2603384, by rfl⟩ : syracuseStep 3471179 = 5206769) B5206769
theorem B1734539 : Blo 1080619 1734539 := bstep (se 1 (by rfl) ⟨1300904, by rfl⟩ : syracuseStep 1734539 = 2601809) B2601809
theorem B12318641 : Blo 1080619 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B2193331 : Blo 1080619 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B3897409 : Blo 1080619 3897409 := bstep (se 2 (by rfl) ⟨1461528, by rfl⟩ : syracuseStep 3897409 = 2923057) B2923057
theorem B5863499 : Blo 1080619 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B7796837 : Blo 1080619 7796837 := bstep (se 4 (by rfl) ⟨730953, by rfl⟩ : syracuseStep 7796837 = 1461907) B1461907
theorem B19757357 : Blo 1080619 19757357 := bstep (se 3 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 19757357 = 7409009) B7409009
theorem B3471923 : Blo 1080619 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B3078749 : Blo 1080619 3078749 := bstep (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) B1154531
theorem B1538777 : Blo 1080619 1538777 := bstep (se 2 (by rfl) ⟨577041, by rfl⟩ : syracuseStep 1538777 = 1154083) B1154083
theorem B4619339 : Blo 1080619 4619339 := bstep (se 1 (by rfl) ⟨3464504, by rfl⟩ : syracuseStep 4619339 = 6929009) B6929009
theorem B10419461 : Blo 1080619 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B1080619 : Blo 1080619 1080619 := bstep (se 1 (by rfl) ⟨810464, by rfl⟩ : syracuseStep 1080619 = 1620929) B1620929
theorem B1080631 : Blo 1080619 1080631 := bstep (se 1 (by rfl) ⟨810473, by rfl⟩ : syracuseStep 1080631 = 1620947) B1620947
theorem B1080651 : Blo 1080619 1080651 := bstep (se 1 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 1080651 = 1620977) B1620977
theorem B1080663 : Blo 1080619 1080663 := bstep (se 1 (by rfl) ⟨810497, by rfl⟩ : syracuseStep 1080663 = 1620995) B1620995
theorem B1539415 : Blo 1080619 1539415 := bstep (se 1 (by rfl) ⟨1154561, by rfl⟩ : syracuseStep 1539415 = 2309123) B2309123
theorem B1080683 : Blo 1080619 1080683 := bstep (se 1 (by rfl) ⟨810512, by rfl⟩ : syracuseStep 1080683 = 1621025) B1621025
theorem B1080695 : Blo 1080619 1080695 := bstep (se 1 (by rfl) ⟨810521, by rfl⟩ : syracuseStep 1080695 = 1621043) B1621043
theorem B9239939 : Blo 1080619 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B1080715 : Blo 1080619 1080715 := bstep (se 1 (by rfl) ⟨810536, by rfl⟩ : syracuseStep 1080715 = 1621073) B1621073
theorem B1080727 : Blo 1080619 1080727 := bstep (se 1 (by rfl) ⟨810545, by rfl⟩ : syracuseStep 1080727 = 1621091) B1621091
theorem B1080747 : Blo 1080619 1080747 := bstep (se 1 (by rfl) ⟨810560, by rfl⟩ : syracuseStep 1080747 = 1621121) B1621121
theorem B1080759 : Blo 1080619 1080759 := bstep (se 1 (by rfl) ⟨810569, by rfl⟩ : syracuseStep 1080759 = 1621139) B1621139
theorem B1080779 : Blo 1080619 1080779 := bstep (se 1 (by rfl) ⟨810584, by rfl⟩ : syracuseStep 1080779 = 1621169) B1621169
theorem B1080791 : Blo 1080619 1080791 := bstep (se 1 (by rfl) ⟨810593, by rfl⟩ : syracuseStep 1080791 = 1621187) B1621187
theorem B1080811 : Blo 1080619 1080811 := bstep (se 1 (by rfl) ⟨810608, by rfl⟩ : syracuseStep 1080811 = 1621217) B1621217
theorem B1080823 : Blo 1080619 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B1080843 : Blo 1080619 1080843 := bstep (se 1 (by rfl) ⟨810632, by rfl⟩ : syracuseStep 1080843 = 1621265) B1621265
theorem B1080855 : Blo 1080619 1080855 := bstep (se 1 (by rfl) ⟨810641, by rfl⟩ : syracuseStep 1080855 = 1621283) B1621283
theorem B1080875 : Blo 1080619 1080875 := bstep (se 1 (by rfl) ⟨810656, by rfl⟩ : syracuseStep 1080875 = 1621313) B1621313
theorem B1080887 : Blo 1080619 1080887 := bstep (se 1 (by rfl) ⟨810665, by rfl⟩ : syracuseStep 1080887 = 1621331) B1621331
theorem B1080907 : Blo 1080619 1080907 := bstep (se 1 (by rfl) ⟨810680, by rfl⟩ : syracuseStep 1080907 = 1621361) B1621361
theorem B1080919 : Blo 1080619 1080919 := bstep (se 1 (by rfl) ⟨810689, by rfl⟩ : syracuseStep 1080919 = 1621379) B1621379
theorem B1080939 : Blo 1080619 1080939 := bstep (se 1 (by rfl) ⟨810704, by rfl⟩ : syracuseStep 1080939 = 1621409) B1621409
theorem B1080951 : Blo 1080619 1080951 := bstep (se 1 (by rfl) ⟨810713, by rfl⟩ : syracuseStep 1080951 = 1621427) B1621427
theorem B1080971 : Blo 1080619 1080971 := bstep (se 1 (by rfl) ⟨810728, by rfl⟩ : syracuseStep 1080971 = 1621457) B1621457
theorem B1080983 : Blo 1080619 1080983 := bstep (se 1 (by rfl) ⟨810737, by rfl⟩ : syracuseStep 1080983 = 1621475) B1621475
theorem B1081003 : Blo 1080619 1081003 := bstep (se 1 (by rfl) ⟨810752, by rfl⟩ : syracuseStep 1081003 = 1621505) B1621505
theorem B1081015 : Blo 1080619 1081015 := bstep (se 1 (by rfl) ⟨810761, by rfl⟩ : syracuseStep 1081015 = 1621523) B1621523
theorem B1081035 : Blo 1080619 1081035 := bstep (se 1 (by rfl) ⟨810776, by rfl⟩ : syracuseStep 1081035 = 1621553) B1621553
theorem B1081047 : Blo 1080619 1081047 := bstep (se 1 (by rfl) ⟨810785, by rfl⟩ : syracuseStep 1081047 = 1621571) B1621571
theorem B1081067 : Blo 1080619 1081067 := bstep (se 1 (by rfl) ⟨810800, by rfl⟩ : syracuseStep 1081067 = 1621601) B1621601
theorem B1081079 : Blo 1080619 1081079 := bstep (se 1 (by rfl) ⟨810809, by rfl⟩ : syracuseStep 1081079 = 1621619) B1621619
theorem B1081099 : Blo 1080619 1081099 := bstep (se 1 (by rfl) ⟨810824, by rfl⟩ : syracuseStep 1081099 = 1621649) B1621649
theorem B1081111 : Blo 1080619 1081111 := bstep (se 1 (by rfl) ⟨810833, by rfl⟩ : syracuseStep 1081111 = 1621667) B1621667
theorem B1081131 : Blo 1080619 1081131 := bstep (se 1 (by rfl) ⟨810848, by rfl⟩ : syracuseStep 1081131 = 1621697) B1621697
theorem B1081143 : Blo 1080619 1081143 := bstep (se 1 (by rfl) ⟨810857, by rfl⟩ : syracuseStep 1081143 = 1621715) B1621715
theorem B8224577 : Blo 1080619 8224577 := bstep (se 2 (by rfl) ⟨3084216, by rfl⟩ : syracuseStep 8224577 = 6168433) B6168433
theorem B1081163 : Blo 1080619 1081163 := bstep (se 1 (by rfl) ⟨810872, by rfl⟩ : syracuseStep 1081163 = 1621745) B1621745
theorem B1081175 : Blo 1080619 1081175 := bstep (se 1 (by rfl) ⟨810881, by rfl⟩ : syracuseStep 1081175 = 1621763) B1621763
theorem B1081195 : Blo 1080619 1081195 := bstep (se 1 (by rfl) ⟨810896, by rfl⟩ : syracuseStep 1081195 = 1621793) B1621793
theorem B1081207 : Blo 1080619 1081207 := bstep (se 1 (by rfl) ⟨810905, by rfl⟩ : syracuseStep 1081207 = 1621811) B1621811
theorem B1081227 : Blo 1080619 1081227 := bstep (se 1 (by rfl) ⟨810920, by rfl⟩ : syracuseStep 1081227 = 1621841) B1621841
theorem B1081239 : Blo 1080619 1081239 := bstep (se 1 (by rfl) ⟨810929, by rfl⟩ : syracuseStep 1081239 = 1621859) B1621859
theorem B1081259 : Blo 1080619 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B1081271 : Blo 1080619 1081271 := bstep (se 1 (by rfl) ⟨810953, by rfl⟩ : syracuseStep 1081271 = 1621907) B1621907
theorem B1081291 : Blo 1080619 1081291 := bstep (se 1 (by rfl) ⟨810968, by rfl⟩ : syracuseStep 1081291 = 1621937) B1621937
theorem B1081303 : Blo 1080619 1081303 := bstep (se 1 (by rfl) ⟨810977, by rfl⟩ : syracuseStep 1081303 = 1621955) B1621955
theorem B1081323 : Blo 1080619 1081323 := bstep (se 1 (by rfl) ⟨810992, by rfl⟩ : syracuseStep 1081323 = 1621985) B1621985
theorem B1081335 : Blo 1080619 1081335 := bstep (se 1 (by rfl) ⟨811001, by rfl⟩ : syracuseStep 1081335 = 1622003) B1622003
theorem B1081351 : Blo 1080619 1081351 := bstep (se 1 (by rfl) ⟨811013, by rfl⟩ : syracuseStep 1081351 = 1622027) B1622027
theorem B1081359 : Blo 1080619 1081359 := bstep (se 1 (by rfl) ⟨811019, by rfl⟩ : syracuseStep 1081359 = 1622039) B1622039
theorem B3080207 : Blo 1080619 3080207 := bstep (se 1 (by rfl) ⟨2310155, by rfl⟩ : syracuseStep 3080207 = 4620311) B4620311
theorem B1081403 : Blo 1080619 1081403 := bstep (se 1 (by rfl) ⟨811052, by rfl⟩ : syracuseStep 1081403 = 1622105) B1622105
theorem B1081479 : Blo 1080619 1081479 := bstep (se 1 (by rfl) ⟨811109, by rfl⟩ : syracuseStep 1081479 = 1622219) B1622219
theorem B1081487 : Blo 1080619 1081487 := bstep (se 1 (by rfl) ⟨811115, by rfl⟩ : syracuseStep 1081487 = 1622231) B1622231
theorem B1081531 : Blo 1080619 1081531 := bstep (se 1 (by rfl) ⟨811148, by rfl⟩ : syracuseStep 1081531 = 1622297) B1622297
theorem B1540343 : Blo 1080619 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B1081607 : Blo 1080619 1081607 := bstep (se 1 (by rfl) ⟨811205, by rfl⟩ : syracuseStep 1081607 = 1622411) B1622411
theorem B1081615 : Blo 1080619 1081615 := bstep (se 1 (by rfl) ⟨811211, by rfl⟩ : syracuseStep 1081615 = 1622423) B1622423
theorem B1081659 : Blo 1080619 1081659 := bstep (se 1 (by rfl) ⟨811244, by rfl⟩ : syracuseStep 1081659 = 1622489) B1622489
theorem B1081735 : Blo 1080619 1081735 := bstep (se 1 (by rfl) ⟨811301, by rfl⟩ : syracuseStep 1081735 = 1622603) B1622603
theorem B1081743 : Blo 1080619 1081743 := bstep (se 1 (by rfl) ⟨811307, by rfl⟩ : syracuseStep 1081743 = 1622615) B1622615
theorem B1081787 : Blo 1080619 1081787 := bstep (se 1 (by rfl) ⟨811340, by rfl⟩ : syracuseStep 1081787 = 1622681) B1622681
theorem B1081863 : Blo 1080619 1081863 := bstep (se 1 (by rfl) ⟨811397, by rfl⟩ : syracuseStep 1081863 = 1622795) B1622795
theorem B1081871 : Blo 1080619 1081871 := bstep (se 1 (by rfl) ⟨811403, by rfl⟩ : syracuseStep 1081871 = 1622807) B1622807
theorem B1081915 : Blo 1080619 1081915 := bstep (se 1 (by rfl) ⟨811436, by rfl⟩ : syracuseStep 1081915 = 1622873) B1622873
theorem B6324797 : Blo 1080619 6324797 := bstep (se 3 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 6324797 = 2371799) B2371799
theorem B14811767 : Blo 1080619 14811767 := bstep (se 1 (by rfl) ⟨11108825, by rfl⟩ : syracuseStep 14811767 = 22217651) B22217651
theorem B1081991 : Blo 1080619 1081991 := bstep (se 1 (by rfl) ⟨811493, by rfl⟩ : syracuseStep 1081991 = 1622987) B1622987
theorem B1081999 : Blo 1080619 1081999 := bstep (se 1 (by rfl) ⟨811499, by rfl⟩ : syracuseStep 1081999 = 1622999) B1622999
theorem B1082043 : Blo 1080619 1082043 := bstep (se 1 (by rfl) ⟨811532, by rfl⟩ : syracuseStep 1082043 = 1623065) B1623065
theorem B1082119 : Blo 1080619 1082119 := bstep (se 1 (by rfl) ⟨811589, by rfl⟩ : syracuseStep 1082119 = 1623179) B1623179
theorem B1082127 : Blo 1080619 1082127 := bstep (se 1 (by rfl) ⟨811595, by rfl⟩ : syracuseStep 1082127 = 1623191) B1623191
theorem B1082171 : Blo 1080619 1082171 := bstep (se 1 (by rfl) ⟨811628, by rfl⟩ : syracuseStep 1082171 = 1623257) B1623257
theorem B1082247 : Blo 1080619 1082247 := bstep (se 1 (by rfl) ⟨811685, by rfl⟩ : syracuseStep 1082247 = 1623371) B1623371
theorem B1082255 : Blo 1080619 1082255 := bstep (se 1 (by rfl) ⟨811691, by rfl⟩ : syracuseStep 1082255 = 1623383) B1623383
theorem B5473169 : Blo 1080619 5473169 := bstep (se 2 (by rfl) ⟨2052438, by rfl⟩ : syracuseStep 5473169 = 4104877) B4104877
theorem B1082299 : Blo 1080619 1082299 := bstep (se 1 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 1082299 = 1623449) B1623449
theorem B1082375 : Blo 1080619 1082375 := bstep (se 1 (by rfl) ⟨811781, by rfl⟩ : syracuseStep 1082375 = 1623563) B1623563
theorem B1082383 : Blo 1080619 1082383 := bstep (se 1 (by rfl) ⟨811787, by rfl⟩ : syracuseStep 1082383 = 1623575) B1623575
theorem B1082427 : Blo 1080619 1082427 := bstep (se 1 (by rfl) ⟨811820, by rfl⟩ : syracuseStep 1082427 = 1623641) B1623641
theorem B41649227 : Blo 1080619 41649227 := bstep (se 1 (by rfl) ⟨31236920, by rfl⟩ : syracuseStep 41649227 = 62473841) B62473841
theorem B3474551 : Blo 1080619 3474551 := bstep (se 1 (by rfl) ⟨2605913, by rfl⟩ : syracuseStep 3474551 = 5211827) B5211827
theorem B1082503 : Blo 1080619 1082503 := bstep (se 1 (by rfl) ⟨811877, by rfl⟩ : syracuseStep 1082503 = 1623755) B1623755
theorem B1082511 : Blo 1080619 1082511 := bstep (se 1 (by rfl) ⟨811883, by rfl⟩ : syracuseStep 1082511 = 1623767) B1623767
theorem B1082555 : Blo 1080619 1082555 := bstep (se 1 (by rfl) ⟨811916, by rfl⟩ : syracuseStep 1082555 = 1623833) B1623833
theorem B3081473 : Blo 1080619 3081473 := bstep (se 2 (by rfl) ⟨1155552, by rfl⟩ : syracuseStep 3081473 = 2311105) B2311105
theorem B1082631 : Blo 1080619 1082631 := bstep (se 1 (by rfl) ⟨811973, by rfl⟩ : syracuseStep 1082631 = 1623947) B1623947
theorem B1082639 : Blo 1080619 1082639 := bstep (se 1 (by rfl) ⟨811979, by rfl⟩ : syracuseStep 1082639 = 1623959) B1623959
theorem B6325541 : Blo 1080619 6325541 := bstep (se 4 (by rfl) ⟨593019, by rfl⟩ : syracuseStep 6325541 = 1186039) B1186039
theorem B1082683 : Blo 1080619 1082683 := bstep (se 1 (by rfl) ⟨812012, by rfl⟩ : syracuseStep 1082683 = 1624025) B1624025
theorem B1082759 : Blo 1080619 1082759 := bstep (se 1 (by rfl) ⟨812069, by rfl⟩ : syracuseStep 1082759 = 1624139) B1624139
theorem B1082767 : Blo 1080619 1082767 := bstep (se 1 (by rfl) ⟨812075, by rfl⟩ : syracuseStep 1082767 = 1624151) B1624151
theorem B7800209 : Blo 1080619 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B6948281 : Blo 1080619 6948281 := bstep (se 2 (by rfl) ⟨2605605, by rfl⟩ : syracuseStep 6948281 = 5211211) B5211211
theorem B1082811 : Blo 1080619 1082811 := bstep (se 1 (by rfl) ⟨812108, by rfl⟩ : syracuseStep 1082811 = 1624217) B1624217
theorem B6948305 : Blo 1080619 6948305 := bstep (se 2 (by rfl) ⟨2605614, by rfl⟩ : syracuseStep 6948305 = 5211229) B5211229
theorem B1082887 : Blo 1080619 1082887 := bstep (se 1 (by rfl) ⟨812165, by rfl⟩ : syracuseStep 1082887 = 1624331) B1624331
theorem B1082895 : Blo 1080619 1082895 := bstep (se 1 (by rfl) ⟨812171, by rfl⟩ : syracuseStep 1082895 = 1624343) B1624343
theorem B1082939 : Blo 1080619 1082939 := bstep (se 1 (by rfl) ⟨812204, by rfl⟩ : syracuseStep 1082939 = 1624409) B1624409
theorem B1541767 : Blo 1080619 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B1083015 : Blo 1080619 1083015 := bstep (se 1 (by rfl) ⟨812261, by rfl⟩ : syracuseStep 1083015 = 1624523) B1624523
theorem B1083023 : Blo 1080619 1083023 := bstep (se 1 (by rfl) ⟨812267, by rfl⟩ : syracuseStep 1083023 = 1624535) B1624535
theorem B1083067 : Blo 1080619 1083067 := bstep (se 1 (by rfl) ⟨812300, by rfl⟩ : syracuseStep 1083067 = 1624601) B1624601
theorem B1083143 : Blo 1080619 1083143 := bstep (se 1 (by rfl) ⟨812357, by rfl⟩ : syracuseStep 1083143 = 1624715) B1624715
theorem B1083151 : Blo 1080619 1083151 := bstep (se 1 (by rfl) ⟨812363, by rfl⟩ : syracuseStep 1083151 = 1624727) B1624727
theorem B1083195 : Blo 1080619 1083195 := bstep (se 1 (by rfl) ⟨812396, by rfl⟩ : syracuseStep 1083195 = 1624793) B1624793
theorem B20809547 : Blo 1080619 20809547 := bstep (se 1 (by rfl) ⟨15607160, by rfl⟩ : syracuseStep 20809547 = 31214321) B31214321
theorem B1083271 : Blo 1080619 1083271 := bstep (se 1 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 1083271 = 1624907) B1624907
theorem B1083279 : Blo 1080619 1083279 := bstep (se 1 (by rfl) ⟨812459, by rfl⟩ : syracuseStep 1083279 = 1624919) B1624919
theorem B1083323 : Blo 1080619 1083323 := bstep (se 1 (by rfl) ⟨812492, by rfl⟩ : syracuseStep 1083323 = 1624985) B1624985
theorem B1083399 : Blo 1080619 1083399 := bstep (se 1 (by rfl) ⟨812549, by rfl⟩ : syracuseStep 1083399 = 1625099) B1625099
theorem B1083407 : Blo 1080619 1083407 := bstep (se 1 (by rfl) ⟨812555, by rfl⟩ : syracuseStep 1083407 = 1625111) B1625111
theorem B1083451 : Blo 1080619 1083451 := bstep (se 1 (by rfl) ⟨812588, by rfl⟩ : syracuseStep 1083451 = 1625177) B1625177
theorem B1083527 : Blo 1080619 1083527 := bstep (se 1 (by rfl) ⟨812645, by rfl⟩ : syracuseStep 1083527 = 1625291) B1625291
theorem B1083535 : Blo 1080619 1083535 := bstep (se 1 (by rfl) ⟨812651, by rfl⟩ : syracuseStep 1083535 = 1625303) B1625303
theorem B1542331 : Blo 1080619 1542331 := bstep (se 1 (by rfl) ⟨1156748, by rfl⟩ : syracuseStep 1542331 = 2313497) B2313497
theorem B1083579 : Blo 1080619 1083579 := bstep (se 1 (by rfl) ⟨812684, by rfl⟩ : syracuseStep 1083579 = 1625369) B1625369
theorem B1083655 : Blo 1080619 1083655 := bstep (se 1 (by rfl) ⟨812741, by rfl⟩ : syracuseStep 1083655 = 1625483) B1625483
theorem B1083663 : Blo 1080619 1083663 := bstep (se 1 (by rfl) ⟨812747, by rfl⟩ : syracuseStep 1083663 = 1625495) B1625495
theorem B1083707 : Blo 1080619 1083707 := bstep (se 1 (by rfl) ⟨812780, by rfl⟩ : syracuseStep 1083707 = 1625561) B1625561
theorem B1083783 : Blo 1080619 1083783 := bstep (se 1 (by rfl) ⟨812837, by rfl⟩ : syracuseStep 1083783 = 1625675) B1625675
theorem B1083791 : Blo 1080619 1083791 := bstep (se 1 (by rfl) ⟨812843, by rfl⟩ : syracuseStep 1083791 = 1625687) B1625687
theorem B1083835 : Blo 1080619 1083835 := bstep (se 1 (by rfl) ⟨812876, by rfl⟩ : syracuseStep 1083835 = 1625753) B1625753
theorem B1083911 : Blo 1080619 1083911 := bstep (se 1 (by rfl) ⟨812933, by rfl⟩ : syracuseStep 1083911 = 1625867) B1625867
theorem B1083919 : Blo 1080619 1083919 := bstep (se 1 (by rfl) ⟨812939, by rfl⟩ : syracuseStep 1083919 = 1625879) B1625879
theorem B1083963 : Blo 1080619 1083963 := bstep (se 1 (by rfl) ⟨812972, by rfl⟩ : syracuseStep 1083963 = 1625945) B1625945
theorem B1084039 : Blo 1080619 1084039 := bstep (se 1 (by rfl) ⟨813029, by rfl⟩ : syracuseStep 1084039 = 1626059) B1626059
theorem B1084047 : Blo 1080619 1084047 := bstep (se 1 (by rfl) ⟨813035, by rfl⟩ : syracuseStep 1084047 = 1626071) B1626071
theorem B1084091 : Blo 1080619 1084091 := bstep (se 1 (by rfl) ⟨813068, by rfl⟩ : syracuseStep 1084091 = 1626137) B1626137
theorem B1084167 : Blo 1080619 1084167 := bstep (se 1 (by rfl) ⟨813125, by rfl⟩ : syracuseStep 1084167 = 1626251) B1626251
theorem B7506703 : Blo 1080619 7506703 := bstep (se 1 (by rfl) ⟨5630027, by rfl⟩ : syracuseStep 7506703 = 11260055) B11260055
theorem B1084175 : Blo 1080619 1084175 := bstep (se 1 (by rfl) ⟨813131, by rfl⟩ : syracuseStep 1084175 = 1626263) B1626263
theorem B1084219 : Blo 1080619 1084219 := bstep (se 1 (by rfl) ⟨813164, by rfl⟩ : syracuseStep 1084219 = 1626329) B1626329
theorem B3083123 : Blo 1080619 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B1084295 : Blo 1080619 1084295 := bstep (se 1 (by rfl) ⟨813221, by rfl⟩ : syracuseStep 1084295 = 1626443) B1626443
theorem B1084303 : Blo 1080619 1084303 := bstep (se 1 (by rfl) ⟨813227, by rfl⟩ : syracuseStep 1084303 = 1626455) B1626455
theorem B1084347 : Blo 1080619 1084347 := bstep (se 1 (by rfl) ⟨813260, by rfl⟩ : syracuseStep 1084347 = 1626521) B1626521
theorem B5475275 : Blo 1080619 5475275 := bstep (se 1 (by rfl) ⟨4106456, by rfl⟩ : syracuseStep 5475275 = 8212913) B8212913
theorem B1084423 : Blo 1080619 1084423 := bstep (se 1 (by rfl) ⟨813317, by rfl⟩ : syracuseStep 1084423 = 1626635) B1626635
theorem B1084431 : Blo 1080619 1084431 := bstep (se 1 (by rfl) ⟨813323, by rfl⟩ : syracuseStep 1084431 = 1626647) B1626647
theorem B1543225 : Blo 1080619 1543225 := bstep (se 2 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 1543225 = 1157419) B1157419
theorem B1084475 : Blo 1080619 1084475 := bstep (se 1 (by rfl) ⟨813356, by rfl⟩ : syracuseStep 1084475 = 1626713) B1626713
theorem B1084551 : Blo 1080619 1084551 := bstep (se 1 (by rfl) ⟨813413, by rfl⟩ : syracuseStep 1084551 = 1626827) B1626827
theorem B1084559 : Blo 1080619 1084559 := bstep (se 1 (by rfl) ⟨813419, by rfl⟩ : syracuseStep 1084559 = 1626839) B1626839
theorem B1084603 : Blo 1080619 1084603 := bstep (se 1 (by rfl) ⟨813452, by rfl⟩ : syracuseStep 1084603 = 1626905) B1626905
theorem B1215751 : Blo 1080619 1215751 := bstep (se 1 (by rfl) ⟨911813, by rfl⟩ : syracuseStep 1215751 = 1823627) B1823627
theorem B5475599 : Blo 1080619 5475599 := bstep (se 1 (by rfl) ⟨4106699, by rfl⟩ : syracuseStep 5475599 = 8213399) B8213399
theorem B3083579 : Blo 1080619 3083579 := bstep (se 1 (by rfl) ⟨2312684, by rfl⟩ : syracuseStep 3083579 = 4625369) B4625369
theorem B10423687 : Blo 1080619 10423687 := bstep (se 1 (by rfl) ⟨7817765, by rfl⟩ : syracuseStep 10423687 = 15635531) B15635531
theorem B4623763 : Blo 1080619 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B1215931 : Blo 1080619 1215931 := bstep (se 1 (by rfl) ⟨911948, by rfl⟩ : syracuseStep 1215931 = 1823897) B1823897
theorem B8785361 : Blo 1080619 8785361 := bstep (se 2 (by rfl) ⟨3294510, by rfl⟩ : syracuseStep 8785361 = 6589021) B6589021
theorem B24973057 : Blo 1080619 24973057 := bstep (se 2 (by rfl) ⟨9364896, by rfl⟩ : syracuseStep 24973057 = 18729793) B18729793
theorem B7409497 : Blo 1080619 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B3903347 : Blo 1080619 3903347 := bstep (se 1 (by rfl) ⟨2927510, by rfl⟩ : syracuseStep 3903347 = 5855021) B5855021
theorem B1216399 : Blo 1080619 1216399 := bstep (se 1 (by rfl) ⟨912299, by rfl⟩ : syracuseStep 1216399 = 1824599) B1824599
theorem B3084331 : Blo 1080619 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B8228951 : Blo 1080619 8228951 := bstep (se 1 (by rfl) ⟨6171713, by rfl⟩ : syracuseStep 8228951 = 12343427) B12343427
theorem B3084605 : Blo 1080619 3084605 := bstep (se 3 (by rfl) ⟨578363, by rfl⟩ : syracuseStep 3084605 = 1156727) B1156727
theorem B1216903 : Blo 1080619 1216903 := bstep (se 1 (by rfl) ⟨912677, by rfl⟩ : syracuseStep 1216903 = 1825355) B1825355
theorem B1217083 : Blo 1080619 1217083 := bstep (se 1 (by rfl) ⟨912812, by rfl⟩ : syracuseStep 1217083 = 1825625) B1825625
theorem B5477057 : Blo 1080619 5477057 := bstep (se 2 (by rfl) ⟨2053896, by rfl⟩ : syracuseStep 5477057 = 4107793) B4107793
theorem B3904271 : Blo 1080619 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B4166585 : Blo 1080619 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B1643527 : Blo 1080619 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B1217551 : Blo 1080619 1217551 := bstep (se 1 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 1217551 = 1826327) B1826327
theorem B4625437 : Blo 1080619 4625437 := bstep (se 3 (by rfl) ⟨867269, by rfl⟩ : syracuseStep 4625437 = 1734539) B1734539
theorem B3085447 : Blo 1080619 3085447 := bstep (se 1 (by rfl) ⟨2314085, by rfl⟩ : syracuseStep 3085447 = 4628171) B4628171
theorem B3085721 : Blo 1080619 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B5281283 : Blo 1080619 5281283 := bstep (se 1 (by rfl) ⟨3960962, by rfl⟩ : syracuseStep 5281283 = 7921925) B7921925
theorem B1218055 : Blo 1080619 1218055 := bstep (se 1 (by rfl) ⟨913541, by rfl⟩ : syracuseStep 1218055 = 1827083) B1827083
theorem B13866673 : Blo 1080619 13866673 := bstep (se 2 (by rfl) ⟨5200002, by rfl⟩ : syracuseStep 13866673 = 10400005) B10400005
theorem B1218235 : Blo 1080619 1218235 := bstep (se 1 (by rfl) ⟨913676, by rfl⟩ : syracuseStep 1218235 = 1827353) B1827353
theorem B4396781 : Blo 1080619 4396781 := bstep (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) B1648793
theorem B6166475 : Blo 1080619 6166475 := bstep (se 1 (by rfl) ⟨4624856, by rfl⟩ : syracuseStep 6166475 = 9249713) B9249713
theorem B5478353 : Blo 1080619 5478353 := bstep (se 2 (by rfl) ⟨2054382, by rfl⟩ : syracuseStep 5478353 = 4108765) B4108765
theorem B1218703 : Blo 1080619 1218703 := bstep (se 1 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 1218703 = 1828055) B1828055
theorem B3709319 : Blo 1080619 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B12327389 : Blo 1080619 12327389 := bstep (se 3 (by rfl) ⟨2311385, by rfl⟩ : syracuseStep 12327389 = 4622771) B4622771
theorem B3086849 : Blo 1080619 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B2431547 : Blo 1080619 2431547 := bstep (se 1 (by rfl) ⟨1823660, by rfl⟩ : syracuseStep 2431547 = 3647321) B3647321
theorem B2923123 : Blo 1080619 2923123 := bstep (se 1 (by rfl) ⟨2192342, by rfl⟩ : syracuseStep 2923123 = 4384685) B4384685
theorem B1219207 : Blo 1080619 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B2431673 : Blo 1080619 2431673 := bstep (se 2 (by rfl) ⟨911877, by rfl⟩ : syracuseStep 2431673 = 1823755) B1823755
theorem B4627145 : Blo 1080619 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B1219387 : Blo 1080619 1219387 := bstep (se 1 (by rfl) ⟨914540, by rfl⟩ : syracuseStep 1219387 = 1829081) B1829081
theorem B3087305 : Blo 1080619 3087305 := bstep (se 2 (by rfl) ⟨1157739, by rfl⟩ : syracuseStep 3087305 = 2315479) B2315479
theorem B2432015 : Blo 1080619 2432015 := bstep (se 1 (by rfl) ⟨1824011, by rfl⟩ : syracuseStep 2432015 = 3648023) B3648023
theorem B2432033 : Blo 1080619 2432033 := bstep (se 2 (by rfl) ⟨912012, by rfl⟩ : syracuseStep 2432033 = 1824025) B1824025
theorem B4103405 : Blo 1080619 4103405 := bstep (se 3 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 4103405 = 1538777) B1538777
theorem B1219855 : Blo 1080619 1219855 := bstep (se 1 (by rfl) ⟨914891, by rfl⟩ : syracuseStep 1219855 = 1829783) B1829783
theorem B2432375 : Blo 1080619 2432375 := bstep (se 1 (by rfl) ⟨1824281, by rfl⟩ : syracuseStep 2432375 = 3648563) B3648563
theorem B3907025 : Blo 1080619 3907025 := bstep (se 2 (by rfl) ⟨1465134, by rfl⟩ : syracuseStep 3907025 = 2930269) B2930269
theorem B4103723 : Blo 1080619 4103723 := bstep (se 1 (by rfl) ⟨3077792, by rfl⟩ : syracuseStep 4103723 = 6155585) B6155585
theorem B2432555 : Blo 1080619 2432555 := bstep (se 1 (by rfl) ⟨1824416, by rfl⟩ : syracuseStep 2432555 = 3648833) B3648833
theorem B4628087 : Blo 1080619 4628087 := bstep (se 1 (by rfl) ⟨3471065, by rfl⟩ : syracuseStep 4628087 = 6942131) B6942131
theorem B2596619 : Blo 1080619 2596619 := bstep (se 1 (by rfl) ⟨1947464, by rfl⟩ : syracuseStep 2596619 = 3894929) B3894929
theorem B2432915 : Blo 1080619 2432915 := bstep (se 1 (by rfl) ⟨1824686, by rfl⟩ : syracuseStep 2432915 = 3649373) B3649373
theorem B2924441 : Blo 1080619 2924441 := bstep (se 2 (by rfl) ⟨1096665, by rfl⟩ : syracuseStep 2924441 = 2193331) B2193331
theorem B2432969 : Blo 1080619 2432969 := bstep (se 2 (by rfl) ⟨912363, by rfl⟩ : syracuseStep 2432969 = 1824727) B1824727
theorem B5480459 : Blo 1080619 5480459 := bstep (se 1 (by rfl) ⟨4110344, by rfl⟩ : syracuseStep 5480459 = 8220689) B8220689
theorem B5480621 : Blo 1080619 5480621 := bstep (se 3 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 5480621 = 2055233) B2055233
theorem B8233501 : Blo 1080619 8233501 := bstep (se 3 (by rfl) ⟨1543781, by rfl⟩ : syracuseStep 8233501 = 3087563) B3087563
theorem B4629059 : Blo 1080619 4629059 := bstep (se 1 (by rfl) ⟨3471794, by rfl⟩ : syracuseStep 4629059 = 6943589) B6943589
theorem B2433671 : Blo 1080619 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B1155727 : Blo 1080619 1155727 := bstep (se 1 (by rfl) ⟨866795, by rfl⟩ : syracuseStep 1155727 = 1733591) B1733591
theorem B2433851 : Blo 1080619 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B1647503 : Blo 1080619 1647503 := bstep (se 1 (by rfl) ⟨1235627, by rfl⟩ : syracuseStep 1647503 = 2471255) B2471255
theorem B2433977 : Blo 1080619 2433977 := bstep (se 2 (by rfl) ⟨912741, by rfl⟩ : syracuseStep 2433977 = 1825483) B1825483
theorem B2434319 : Blo 1080619 2434319 := bstep (se 1 (by rfl) ⟨1825739, by rfl⟩ : syracuseStep 2434319 = 3651479) B3651479
theorem B2434337 : Blo 1080619 2434337 := bstep (se 2 (by rfl) ⟨912876, by rfl⟩ : syracuseStep 2434337 = 1825753) B1825753
theorem B3908999 : Blo 1080619 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B2434679 : Blo 1080619 2434679 := bstep (se 1 (by rfl) ⟨1826009, by rfl⟩ : syracuseStep 2434679 = 3652019) B3652019
theorem B5482241 : Blo 1080619 5482241 := bstep (se 2 (by rfl) ⟨2055840, by rfl⟩ : syracuseStep 5482241 = 4111681) B4111681
theorem B2434859 : Blo 1080619 2434859 := bstep (se 1 (by rfl) ⟨1826144, by rfl⟩ : syracuseStep 2434859 = 3652289) B3652289
theorem B2435219 : Blo 1080619 2435219 := bstep (se 1 (by rfl) ⟨1826414, by rfl⟩ : syracuseStep 2435219 = 3652829) B3652829
theorem B2435273 : Blo 1080619 2435273 := bstep (se 2 (by rfl) ⟨913227, by rfl⟩ : syracuseStep 2435273 = 1826455) B1826455
theorem B5483051 : Blo 1080619 5483051 := bstep (se 1 (by rfl) ⟨4112288, by rfl⟩ : syracuseStep 5483051 = 8224577) B8224577
theorem B2599609 : Blo 1080619 2599609 := bstep (se 2 (by rfl) ⟨974853, by rfl⟩ : syracuseStep 2599609 = 1949707) B1949707
theorem B5548915 : Blo 1080619 5548915 := bstep (se 1 (by rfl) ⟨4161686, by rfl⟩ : syracuseStep 5548915 = 8323373) B8323373
theorem B2435975 : Blo 1080619 2435975 := bstep (se 1 (by rfl) ⟨1826981, by rfl⟩ : syracuseStep 2435975 = 3653963) B3653963
theorem B4107293 : Blo 1080619 4107293 := bstep (se 3 (by rfl) ⟨770117, by rfl⟩ : syracuseStep 4107293 = 1540235) B1540235
theorem B4107307 : Blo 1080619 4107307 := bstep (se 1 (by rfl) ⟨3080480, by rfl⟩ : syracuseStep 4107307 = 6160961) B6160961
theorem B2436155 : Blo 1080619 2436155 := bstep (se 1 (by rfl) ⟨1827116, by rfl⟩ : syracuseStep 2436155 = 3654233) B3654233
theorem B2436281 : Blo 1080619 2436281 := bstep (se 2 (by rfl) ⟨913605, by rfl⟩ : syracuseStep 2436281 = 1827211) B1827211
theorem B2600225 : Blo 1080619 2600225 := bstep (se 2 (by rfl) ⟨975084, by rfl⟩ : syracuseStep 2600225 = 1950169) B1950169
theorem B3288379 : Blo 1080619 3288379 := bstep (se 1 (by rfl) ⟨2466284, by rfl⟩ : syracuseStep 3288379 = 4932569) B4932569
theorem B2469305 : Blo 1080619 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B2436623 : Blo 1080619 2436623 := bstep (se 1 (by rfl) ⟨1827467, by rfl⟩ : syracuseStep 2436623 = 3654935) B3654935
theorem B2436641 : Blo 1080619 2436641 := bstep (se 2 (by rfl) ⟨913740, by rfl⟩ : syracuseStep 2436641 = 1827481) B1827481
theorem B5484347 : Blo 1080619 5484347 := bstep (se 1 (by rfl) ⟨4113260, by rfl⟩ : syracuseStep 5484347 = 8226521) B8226521
theorem B2436983 : Blo 1080619 2436983 := bstep (se 1 (by rfl) ⟨1827737, by rfl⟩ : syracuseStep 2436983 = 3655475) B3655475
theorem B2600839 : Blo 1080619 2600839 := bstep (se 1 (by rfl) ⟨1950629, by rfl⟩ : syracuseStep 2600839 = 3901259) B3901259
theorem B3649427 : Blo 1080619 3649427 := bstep (se 1 (by rfl) ⟨2737070, by rfl⟩ : syracuseStep 3649427 = 5474141) B5474141
theorem B22261655 : Blo 1080619 22261655 := bstep (se 1 (by rfl) ⟨16696241, by rfl⟩ : syracuseStep 22261655 = 33392483) B33392483
theorem B6172625 : Blo 1080619 6172625 := bstep (se 2 (by rfl) ⟨2314734, by rfl⟩ : syracuseStep 6172625 = 4629469) B4629469
theorem B5484509 : Blo 1080619 5484509 := bstep (se 3 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 5484509 = 2056691) B2056691
theorem B109555733 : Blo 1080619 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B2600993 : Blo 1080619 2600993 := bstep (se 2 (by rfl) ⟨975372, by rfl⟩ : syracuseStep 2600993 = 1950745) B1950745
theorem B2437163 : Blo 1080619 2437163 := bstep (se 1 (by rfl) ⟨1827872, by rfl⟩ : syracuseStep 2437163 = 3655745) B3655745
theorem B5484833 : Blo 1080619 5484833 := bstep (se 2 (by rfl) ⟨2056812, by rfl⟩ : syracuseStep 5484833 = 4113625) B4113625
theorem B2929043 : Blo 1080619 2929043 := bstep (se 1 (by rfl) ⟨2196782, by rfl⟩ : syracuseStep 2929043 = 4393565) B4393565
theorem B2437523 : Blo 1080619 2437523 := bstep (se 1 (by rfl) ⟨1828142, by rfl⟩ : syracuseStep 2437523 = 3656285) B3656285
theorem B6173081 : Blo 1080619 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B2437577 : Blo 1080619 2437577 := bstep (se 2 (by rfl) ⟨914091, by rfl⟩ : syracuseStep 2437577 = 1828183) B1828183
theorem B8237645 : Blo 1080619 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B3289801 : Blo 1080619 3289801 := bstep (se 2 (by rfl) ⟨1233675, by rfl⟩ : syracuseStep 3289801 = 2467351) B2467351
theorem B2634697 : Blo 1080619 2634697 := bstep (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) B1976023
theorem B2929783 : Blo 1080619 2929783 := bstep (se 1 (by rfl) ⟨2197337, by rfl⟩ : syracuseStep 2929783 = 4394675) B4394675
theorem B2438279 : Blo 1080619 2438279 := bstep (se 1 (by rfl) ⟨1828709, by rfl⟩ : syracuseStep 2438279 = 3657419) B3657419
theorem B5485805 : Blo 1080619 5485805 := bstep (se 3 (by rfl) ⟨1028588, by rfl⟩ : syracuseStep 5485805 = 2057177) B2057177
theorem B3650831 : Blo 1080619 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B2438459 : Blo 1080619 2438459 := bstep (se 1 (by rfl) ⟨1828844, by rfl⟩ : syracuseStep 2438459 = 3657689) B3657689
theorem B5846417 : Blo 1080619 5846417 := bstep (se 2 (by rfl) ⟨2192406, by rfl⟩ : syracuseStep 5846417 = 4384813) B4384813
theorem B2438585 : Blo 1080619 2438585 := bstep (se 2 (by rfl) ⟨914469, by rfl⟩ : syracuseStep 2438585 = 1828939) B1828939
theorem B3651101 : Blo 1080619 3651101 := bstep (se 3 (by rfl) ⟨684581, by rfl⟩ : syracuseStep 3651101 = 1369163) B1369163
theorem B2438927 : Blo 1080619 2438927 := bstep (se 1 (by rfl) ⟨1829195, by rfl⟩ : syracuseStep 2438927 = 3658391) B3658391
theorem B2438945 : Blo 1080619 2438945 := bstep (se 2 (by rfl) ⟨914604, by rfl⟩ : syracuseStep 2438945 = 1829209) B1829209
theorem B2602867 : Blo 1080619 2602867 := bstep (se 1 (by rfl) ⟨1952150, by rfl⟩ : syracuseStep 2602867 = 3904301) B3904301
theorem B1849223 : Blo 1080619 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B1095611 : Blo 1080619 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B5486615 : Blo 1080619 5486615 := bstep (se 1 (by rfl) ⟨4114961, by rfl⟩ : syracuseStep 5486615 = 8229923) B8229923
theorem B2439287 : Blo 1080619 2439287 := bstep (se 1 (by rfl) ⟨1829465, by rfl⟩ : syracuseStep 2439287 = 3658931) B3658931
theorem B2439467 : Blo 1080619 2439467 := bstep (se 1 (by rfl) ⟨1829600, by rfl⟩ : syracuseStep 2439467 = 3659201) B3659201
theorem B11123243 : Blo 1080619 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B2439827 : Blo 1080619 2439827 := bstep (se 1 (by rfl) ⟨1829870, by rfl⟩ : syracuseStep 2439827 = 3659741) B3659741
theorem B2439881 : Blo 1080619 2439881 := bstep (se 2 (by rfl) ⟨914955, by rfl⟩ : syracuseStep 2439881 = 1829911) B1829911
theorem B1096463 : Blo 1080619 1096463 := bstep (se 1 (by rfl) ⟨822347, by rfl⟩ : syracuseStep 1096463 = 1644695) B1644695
theorem B3652505 : Blo 1080619 3652505 := bstep (se 2 (by rfl) ⟨1369689, by rfl⟩ : syracuseStep 3652505 = 2739379) B2739379
theorem B1620983 : Blo 1080619 1620983 := bstep (se 1 (by rfl) ⟨1215737, by rfl⟩ : syracuseStep 1620983 = 2431475) B2431475
theorem B1621007 : Blo 1080619 1621007 := bstep (se 1 (by rfl) ⟨1215755, by rfl⟩ : syracuseStep 1621007 = 2431511) B2431511
theorem B6241303 : Blo 1080619 6241303 := bstep (se 1 (by rfl) ⟨4680977, by rfl⟩ : syracuseStep 6241303 = 9361955) B9361955
theorem B1621049 : Blo 1080619 1621049 := bstep (se 2 (by rfl) ⟨607893, by rfl⟩ : syracuseStep 1621049 = 1215787) B1215787
theorem B6929495 : Blo 1080619 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B1621127 : Blo 1080619 1621127 := bstep (se 1 (by rfl) ⟨1215845, by rfl⟩ : syracuseStep 1621127 = 2431691) B2431691
theorem B2309267 : Blo 1080619 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B1621163 : Blo 1080619 1621163 := bstep (se 1 (by rfl) ⟨1215872, by rfl⟩ : syracuseStep 1621163 = 2431745) B2431745
theorem B1621193 : Blo 1080619 1621193 := bstep (se 2 (by rfl) ⟨607947, by rfl⟩ : syracuseStep 1621193 = 1215895) B1215895
theorem B1621307 : Blo 1080619 1621307 := bstep (se 1 (by rfl) ⟨1215980, by rfl⟩ : syracuseStep 1621307 = 2431961) B2431961
theorem B1621367 : Blo 1080619 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B1621391 : Blo 1080619 1621391 := bstep (se 1 (by rfl) ⟨1216043, by rfl⟩ : syracuseStep 1621391 = 2432087) B2432087
theorem B1621433 : Blo 1080619 1621433 := bstep (se 2 (by rfl) ⟨608037, by rfl⟩ : syracuseStep 1621433 = 1216075) B1216075
theorem B1621511 : Blo 1080619 1621511 := bstep (se 1 (by rfl) ⟨1216133, by rfl⟩ : syracuseStep 1621511 = 2432267) B2432267
theorem B9256477 : Blo 1080619 9256477 := bstep (se 3 (by rfl) ⟨1735589, by rfl⟩ : syracuseStep 9256477 = 3471179) B3471179
theorem B2080289 : Blo 1080619 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B2604577 : Blo 1080619 2604577 := bstep (se 2 (by rfl) ⟨976716, by rfl⟩ : syracuseStep 2604577 = 1953433) B1953433
theorem B1621547 : Blo 1080619 1621547 := bstep (se 1 (by rfl) ⟨1216160, by rfl⟩ : syracuseStep 1621547 = 2432321) B2432321
theorem B5848619 : Blo 1080619 5848619 := bstep (se 1 (by rfl) ⟨4386464, by rfl⟩ : syracuseStep 5848619 = 8772929) B8772929
theorem B1621577 : Blo 1080619 1621577 := bstep (se 2 (by rfl) ⟨608091, by rfl⟩ : syracuseStep 1621577 = 1216183) B1216183
theorem B3653207 : Blo 1080619 3653207 := bstep (se 1 (by rfl) ⟨2739905, by rfl⟩ : syracuseStep 3653207 = 5479811) B5479811
theorem B1621691 : Blo 1080619 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B1621751 : Blo 1080619 1621751 := bstep (se 1 (by rfl) ⟨1216313, by rfl⟩ : syracuseStep 1621751 = 2432627) B2432627
theorem B1621775 : Blo 1080619 1621775 := bstep (se 1 (by rfl) ⟨1216331, by rfl⟩ : syracuseStep 1621775 = 2432663) B2432663
theorem B6668065 : Blo 1080619 6668065 := bstep (se 2 (by rfl) ⟨2500524, by rfl⟩ : syracuseStep 6668065 = 5001049) B5001049
theorem B1949483 : Blo 1080619 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B1621817 : Blo 1080619 1621817 := bstep (se 2 (by rfl) ⟨608181, by rfl⟩ : syracuseStep 1621817 = 1216363) B1216363
theorem B1621895 : Blo 1080619 1621895 := bstep (se 1 (by rfl) ⟨1216421, by rfl⟩ : syracuseStep 1621895 = 2432843) B2432843
theorem B1621931 : Blo 1080619 1621931 := bstep (se 1 (by rfl) ⟨1216448, by rfl⟩ : syracuseStep 1621931 = 2432897) B2432897
theorem B1621961 : Blo 1080619 1621961 := bstep (se 2 (by rfl) ⟨608235, by rfl⟩ : syracuseStep 1621961 = 1216471) B1216471
theorem B2736139 : Blo 1080619 2736139 := bstep (se 1 (by rfl) ⟨2052104, by rfl⟩ : syracuseStep 2736139 = 4104209) B4104209
theorem B1622075 : Blo 1080619 1622075 := bstep (se 1 (by rfl) ⟨1216556, by rfl⟩ : syracuseStep 1622075 = 2433113) B2433113
theorem B3653693 : Blo 1080619 3653693 := bstep (se 3 (by rfl) ⟨685067, by rfl⟩ : syracuseStep 3653693 = 1370135) B1370135
theorem B4112471 : Blo 1080619 4112471 := bstep (se 1 (by rfl) ⟨3084353, by rfl⟩ : syracuseStep 4112471 = 6168707) B6168707
theorem B1622135 : Blo 1080619 1622135 := bstep (se 1 (by rfl) ⟨1216601, by rfl⟩ : syracuseStep 1622135 = 2433203) B2433203
theorem B1622159 : Blo 1080619 1622159 := bstep (se 1 (by rfl) ⟨1216619, by rfl⟩ : syracuseStep 1622159 = 2433239) B2433239
theorem B2736281 : Blo 1080619 2736281 := bstep (se 2 (by rfl) ⟨1026105, by rfl⟩ : syracuseStep 2736281 = 2052211) B2052211
theorem B1622201 : Blo 1080619 1622201 := bstep (se 2 (by rfl) ⟨608325, by rfl⟩ : syracuseStep 1622201 = 1216651) B1216651
theorem B1622279 : Blo 1080619 1622279 := bstep (se 1 (by rfl) ⟨1216709, by rfl⟩ : syracuseStep 1622279 = 2433419) B2433419
theorem B1622315 : Blo 1080619 1622315 := bstep (se 1 (by rfl) ⟨1216736, by rfl⟩ : syracuseStep 1622315 = 2433473) B2433473
theorem B2736443 : Blo 1080619 2736443 := bstep (se 1 (by rfl) ⟨2052332, by rfl⟩ : syracuseStep 2736443 = 4104665) B4104665
theorem B1622345 : Blo 1080619 1622345 := bstep (se 2 (by rfl) ⟨608379, by rfl⟩ : syracuseStep 1622345 = 1216759) B1216759
theorem B1622459 : Blo 1080619 1622459 := bstep (se 1 (by rfl) ⟨1216844, by rfl⟩ : syracuseStep 1622459 = 2433689) B2433689
theorem B1622519 : Blo 1080619 1622519 := bstep (se 1 (by rfl) ⟨1216889, by rfl⟩ : syracuseStep 1622519 = 2433779) B2433779
theorem B1622543 : Blo 1080619 1622543 := bstep (se 1 (by rfl) ⟨1216907, by rfl⟩ : syracuseStep 1622543 = 2433815) B2433815
theorem B42254891 : Blo 1080619 42254891 := bstep (se 1 (by rfl) ⟨31691168, by rfl⟩ : syracuseStep 42254891 = 63382337) B63382337
theorem B1622585 : Blo 1080619 1622585 := bstep (se 2 (by rfl) ⟨608469, by rfl⟩ : syracuseStep 1622585 = 1216939) B1216939
theorem B4112957 : Blo 1080619 4112957 := bstep (se 3 (by rfl) ⟨771179, by rfl⟩ : syracuseStep 4112957 = 1542359) B1542359
theorem B16695875 : Blo 1080619 16695875 := bstep (se 1 (by rfl) ⟨12521906, by rfl⟩ : syracuseStep 16695875 = 25043813) B25043813
theorem B1622663 : Blo 1080619 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B2736787 : Blo 1080619 2736787 := bstep (se 1 (by rfl) ⟨2052590, by rfl⟩ : syracuseStep 2736787 = 4105181) B4105181
theorem B1622699 : Blo 1080619 1622699 := bstep (se 1 (by rfl) ⟨1217024, by rfl⟩ : syracuseStep 1622699 = 2434049) B2434049
theorem B1622729 : Blo 1080619 1622729 := bstep (se 2 (by rfl) ⟨608523, by rfl⟩ : syracuseStep 1622729 = 1217047) B1217047
theorem B2736929 : Blo 1080619 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B1622843 : Blo 1080619 1622843 := bstep (se 1 (by rfl) ⟨1217132, by rfl⟩ : syracuseStep 1622843 = 2434265) B2434265
theorem B1622903 : Blo 1080619 1622903 := bstep (se 1 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 1622903 = 2434355) B2434355
theorem B1622927 : Blo 1080619 1622927 := bstep (se 1 (by rfl) ⟨1217195, by rfl⟩ : syracuseStep 1622927 = 2434391) B2434391
theorem B1622969 : Blo 1080619 1622969 := bstep (se 2 (by rfl) ⟨608613, by rfl⟩ : syracuseStep 1622969 = 1217227) B1217227
theorem B1623047 : Blo 1080619 1623047 := bstep (se 1 (by rfl) ⟨1217285, by rfl⟩ : syracuseStep 1623047 = 2434571) B2434571
theorem B5194775 : Blo 1080619 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B5489693 : Blo 1080619 5489693 := bstep (se 3 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 5489693 = 2058635) B2058635
theorem B1623083 : Blo 1080619 1623083 := bstep (se 1 (by rfl) ⟨1217312, by rfl⟩ : syracuseStep 1623083 = 2434625) B2434625
theorem B1623113 : Blo 1080619 1623113 := bstep (se 2 (by rfl) ⟨608667, by rfl⟩ : syracuseStep 1623113 = 1217335) B1217335
theorem B1098887 : Blo 1080619 1098887 := bstep (se 1 (by rfl) ⟨824165, by rfl⟩ : syracuseStep 1098887 = 1648331) B1648331
theorem B1623227 : Blo 1080619 1623227 := bstep (se 1 (by rfl) ⟨1217420, by rfl⟩ : syracuseStep 1623227 = 2434841) B2434841
theorem B1623287 : Blo 1080619 1623287 := bstep (se 1 (by rfl) ⟨1217465, by rfl⟩ : syracuseStep 1623287 = 2434931) B2434931
theorem B1623311 : Blo 1080619 1623311 := bstep (se 1 (by rfl) ⟨1217483, by rfl⟩ : syracuseStep 1623311 = 2434967) B2434967
theorem B1623353 : Blo 1080619 1623353 := bstep (se 2 (by rfl) ⟨608757, by rfl⟩ : syracuseStep 1623353 = 1217515) B1217515
theorem B2082167 : Blo 1080619 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B56935811 : Blo 1080619 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B1623431 : Blo 1080619 1623431 := bstep (se 1 (by rfl) ⟨1217573, by rfl⟩ : syracuseStep 1623431 = 2435147) B2435147
theorem B1623467 : Blo 1080619 1623467 := bstep (se 1 (by rfl) ⟨1217600, by rfl⟩ : syracuseStep 1623467 = 2435201) B2435201
theorem B3655097 : Blo 1080619 3655097 := bstep (se 2 (by rfl) ⟨1370661, by rfl⟩ : syracuseStep 3655097 = 2741323) B2741323
theorem B1623497 : Blo 1080619 1623497 := bstep (se 2 (by rfl) ⟨608811, by rfl⟩ : syracuseStep 1623497 = 1217623) B1217623
theorem B2311625 : Blo 1080619 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B9258461 : Blo 1080619 9258461 := bstep (se 3 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 9258461 = 3471923) B3471923
theorem B5490179 : Blo 1080619 5490179 := bstep (se 1 (by rfl) ⟨4117634, by rfl⟩ : syracuseStep 5490179 = 8235269) B8235269
theorem B23447069 : Blo 1080619 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B1623611 : Blo 1080619 1623611 := bstep (se 1 (by rfl) ⟨1217708, by rfl⟩ : syracuseStep 1623611 = 2435417) B2435417
theorem B8209997 : Blo 1080619 8209997 := bstep (se 3 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 8209997 = 3078749) B3078749
theorem B1623671 : Blo 1080619 1623671 := bstep (se 1 (by rfl) ⟨1217753, by rfl⟩ : syracuseStep 1623671 = 2435507) B2435507
theorem B1623695 : Blo 1080619 1623695 := bstep (se 1 (by rfl) ⟨1217771, by rfl⟩ : syracuseStep 1623695 = 2435543) B2435543
theorem B1623737 : Blo 1080619 1623737 := bstep (se 2 (by rfl) ⟨608901, by rfl⟩ : syracuseStep 1623737 = 1217803) B1217803
theorem B2737921 : Blo 1080619 2737921 := bstep (se 2 (by rfl) ⟨1026720, by rfl⟩ : syracuseStep 2737921 = 2053441) B2053441
theorem B1623815 : Blo 1080619 1623815 := bstep (se 1 (by rfl) ⟨1217861, by rfl⟩ : syracuseStep 1623815 = 2435723) B2435723
theorem B1623851 : Blo 1080619 1623851 := bstep (se 1 (by rfl) ⟨1217888, by rfl⟩ : syracuseStep 1623851 = 2435777) B2435777
theorem B1623881 : Blo 1080619 1623881 := bstep (se 2 (by rfl) ⟨608955, by rfl⟩ : syracuseStep 1623881 = 1217911) B1217911
theorem B1623995 : Blo 1080619 1623995 := bstep (se 1 (by rfl) ⟨1217996, by rfl⟩ : syracuseStep 1623995 = 2435993) B2435993
theorem B4114385 : Blo 1080619 4114385 := bstep (se 2 (by rfl) ⟨1542894, by rfl⟩ : syracuseStep 4114385 = 3085789) B3085789
theorem B1624055 : Blo 1080619 1624055 := bstep (se 1 (by rfl) ⟨1218041, by rfl⟩ : syracuseStep 1624055 = 2436083) B2436083
theorem B3655691 : Blo 1080619 3655691 := bstep (se 1 (by rfl) ⟨2741768, by rfl⟩ : syracuseStep 3655691 = 5483537) B5483537
theorem B1624079 : Blo 1080619 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B1624121 : Blo 1080619 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B3655799 : Blo 1080619 3655799 := bstep (se 1 (by rfl) ⟨2741849, by rfl⟩ : syracuseStep 3655799 = 5483699) B5483699
theorem B1624199 : Blo 1080619 1624199 := bstep (se 1 (by rfl) ⟨1218149, by rfl⟩ : syracuseStep 1624199 = 2436299) B2436299
theorem B1624235 : Blo 1080619 1624235 := bstep (se 1 (by rfl) ⟨1218176, by rfl⟩ : syracuseStep 1624235 = 2436353) B2436353
theorem B1624265 : Blo 1080619 1624265 := bstep (se 2 (by rfl) ⟨609099, by rfl⟩ : syracuseStep 1624265 = 1218199) B1218199
theorem B26364149 : Blo 1080619 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B15616273 : Blo 1080619 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B1624379 : Blo 1080619 1624379 := bstep (se 1 (by rfl) ⟨1218284, by rfl⟩ : syracuseStep 1624379 = 2436569) B2436569
theorem B2738519 : Blo 1080619 2738519 := bstep (se 1 (by rfl) ⟨2053889, by rfl⟩ : syracuseStep 2738519 = 4107779) B4107779
theorem B1624439 : Blo 1080619 1624439 := bstep (se 1 (by rfl) ⟨1218329, by rfl⟩ : syracuseStep 1624439 = 2436659) B2436659
theorem B1624463 : Blo 1080619 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B1624505 : Blo 1080619 1624505 := bstep (se 2 (by rfl) ⟨609189, by rfl⟩ : syracuseStep 1624505 = 1218379) B1218379
theorem B1624583 : Blo 1080619 1624583 := bstep (se 1 (by rfl) ⟨1218437, by rfl⟩ : syracuseStep 1624583 = 2436875) B2436875
theorem B2738731 : Blo 1080619 2738731 := bstep (se 1 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 2738731 = 4108097) B4108097
theorem B1624619 : Blo 1080619 1624619 := bstep (se 1 (by rfl) ⟨1218464, by rfl⟩ : syracuseStep 1624619 = 2436929) B2436929
theorem B10406465 : Blo 1080619 10406465 := bstep (se 2 (by rfl) ⟨3902424, by rfl⟩ : syracuseStep 10406465 = 7804849) B7804849
theorem B1624649 : Blo 1080619 1624649 := bstep (se 2 (by rfl) ⟨609243, by rfl⟩ : syracuseStep 1624649 = 1218487) B1218487
theorem B2738873 : Blo 1080619 2738873 := bstep (se 2 (by rfl) ⟨1027077, by rfl⟩ : syracuseStep 2738873 = 2054155) B2054155
theorem B1624763 : Blo 1080619 1624763 := bstep (se 1 (by rfl) ⟨1218572, by rfl⟩ : syracuseStep 1624763 = 2437145) B2437145
theorem B6933185 : Blo 1080619 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B3656393 : Blo 1080619 3656393 := bstep (se 2 (by rfl) ⟨1371147, by rfl⟩ : syracuseStep 3656393 = 2742295) B2742295
theorem B1460983 : Blo 1080619 1460983 := bstep (se 1 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 1460983 = 2191475) B2191475
theorem B1624823 : Blo 1080619 1624823 := bstep (se 1 (by rfl) ⟨1218617, by rfl⟩ : syracuseStep 1624823 = 2437235) B2437235
theorem B5196545 : Blo 1080619 5196545 := bstep (se 2 (by rfl) ⟨1948704, by rfl⟩ : syracuseStep 5196545 = 3897409) B3897409
theorem B2312975 : Blo 1080619 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B1624847 : Blo 1080619 1624847 := bstep (se 1 (by rfl) ⟨1218635, by rfl⟩ : syracuseStep 1624847 = 2437271) B2437271
theorem B1624889 : Blo 1080619 1624889 := bstep (se 2 (by rfl) ⟨609333, by rfl⟩ : syracuseStep 1624889 = 1218667) B1218667
theorem B1624967 : Blo 1080619 1624967 := bstep (se 1 (by rfl) ⟨1218725, by rfl⟩ : syracuseStep 1624967 = 2437451) B2437451
theorem B1625003 : Blo 1080619 1625003 := bstep (se 1 (by rfl) ⟨1218752, by rfl⟩ : syracuseStep 1625003 = 2437505) B2437505
theorem B1625033 : Blo 1080619 1625033 := bstep (se 2 (by rfl) ⟨609387, by rfl⟩ : syracuseStep 1625033 = 1218775) B1218775
theorem B1625147 : Blo 1080619 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B1625207 : Blo 1080619 1625207 := bstep (se 1 (by rfl) ⟨1218905, by rfl⟩ : syracuseStep 1625207 = 2437811) B2437811
theorem B1625231 : Blo 1080619 1625231 := bstep (se 1 (by rfl) ⟨1218923, by rfl⟩ : syracuseStep 1625231 = 2437847) B2437847
theorem B1625273 : Blo 1080619 1625273 := bstep (se 2 (by rfl) ⟨609477, by rfl⟩ : syracuseStep 1625273 = 1218955) B1218955
theorem B1625351 : Blo 1080619 1625351 := bstep (se 1 (by rfl) ⟨1219013, by rfl⟩ : syracuseStep 1625351 = 2438027) B2438027
theorem B1625387 : Blo 1080619 1625387 := bstep (se 1 (by rfl) ⟨1219040, by rfl⟩ : syracuseStep 1625387 = 2438081) B2438081
theorem B1625417 : Blo 1080619 1625417 := bstep (se 2 (by rfl) ⟨609531, by rfl⟩ : syracuseStep 1625417 = 1219063) B1219063
theorem B2084231 : Blo 1080619 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B3657095 : Blo 1080619 3657095 := bstep (se 1 (by rfl) ⟨2742821, by rfl⟩ : syracuseStep 3657095 = 5485643) B5485643
theorem B1625531 : Blo 1080619 1625531 := bstep (se 1 (by rfl) ⟨1219148, by rfl⟩ : syracuseStep 1625531 = 2438297) B2438297
theorem B1625591 : Blo 1080619 1625591 := bstep (se 1 (by rfl) ⟨1219193, by rfl⟩ : syracuseStep 1625591 = 2438387) B2438387
theorem B1625615 : Blo 1080619 1625615 := bstep (se 1 (by rfl) ⟨1219211, by rfl⟩ : syracuseStep 1625615 = 2438423) B2438423
theorem B1625657 : Blo 1080619 1625657 := bstep (se 2 (by rfl) ⟨609621, by rfl⟩ : syracuseStep 1625657 = 1219243) B1219243
theorem B4116055 : Blo 1080619 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B46845539 : Blo 1080619 46845539 := bstep (se 1 (by rfl) ⟨35134154, by rfl⟩ : syracuseStep 46845539 = 70268309) B70268309
theorem B1625735 : Blo 1080619 1625735 := bstep (se 1 (by rfl) ⟨1219301, by rfl⟩ : syracuseStep 1625735 = 2438603) B2438603
theorem B2739865 : Blo 1080619 2739865 := bstep (se 2 (by rfl) ⟨1027449, by rfl⟩ : syracuseStep 2739865 = 2054899) B2054899
theorem B1625771 : Blo 1080619 1625771 := bstep (se 1 (by rfl) ⟨1219328, by rfl⟩ : syracuseStep 1625771 = 2438657) B2438657
theorem B1625801 : Blo 1080619 1625801 := bstep (se 2 (by rfl) ⟨609675, by rfl⟩ : syracuseStep 1625801 = 1219351) B1219351
theorem B3657473 : Blo 1080619 3657473 := bstep (se 2 (by rfl) ⟨1371552, by rfl⟩ : syracuseStep 3657473 = 2743105) B2743105
theorem B9260851 : Blo 1080619 9260851 := bstep (se 1 (by rfl) ⟨6945638, by rfl⟩ : syracuseStep 9260851 = 13891277) B13891277
theorem B2740027 : Blo 1080619 2740027 := bstep (se 1 (by rfl) ⟨2055020, by rfl⟩ : syracuseStep 2740027 = 4110041) B4110041
theorem B1625915 : Blo 1080619 1625915 := bstep (se 1 (by rfl) ⟨1219436, by rfl⟩ : syracuseStep 1625915 = 2438873) B2438873
theorem B1625975 : Blo 1080619 1625975 := bstep (se 1 (by rfl) ⟨1219481, by rfl⟩ : syracuseStep 1625975 = 2438963) B2438963
theorem B4116359 : Blo 1080619 4116359 := bstep (se 1 (by rfl) ⟨3087269, by rfl⟩ : syracuseStep 4116359 = 6174539) B6174539
theorem B1625999 : Blo 1080619 1625999 := bstep (se 1 (by rfl) ⟨1219499, by rfl⟩ : syracuseStep 1625999 = 2438999) B2438999
theorem B1626041 : Blo 1080619 1626041 := bstep (se 2 (by rfl) ⟨609765, by rfl⟩ : syracuseStep 1626041 = 1219531) B1219531
theorem B2772937 : Blo 1080619 2772937 := bstep (se 2 (by rfl) ⟨1039851, by rfl⟩ : syracuseStep 2772937 = 2079703) B2079703
theorem B2740169 : Blo 1080619 2740169 := bstep (se 2 (by rfl) ⟨1027563, by rfl⟩ : syracuseStep 2740169 = 2055127) B2055127
theorem B8212427 : Blo 1080619 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B1626119 : Blo 1080619 1626119 := bstep (se 1 (by rfl) ⟨1219589, by rfl⟩ : syracuseStep 1626119 = 2439179) B2439179
theorem B1626155 : Blo 1080619 1626155 := bstep (se 1 (by rfl) ⟨1219616, by rfl⟩ : syracuseStep 1626155 = 2439233) B2439233
theorem B4116541 : Blo 1080619 4116541 := bstep (se 3 (by rfl) ⟨771851, by rfl⟩ : syracuseStep 4116541 = 1543703) B1543703
theorem B5197891 : Blo 1080619 5197891 := bstep (se 1 (by rfl) ⟨3898418, by rfl⟩ : syracuseStep 5197891 = 7796837) B7796837
theorem B1626185 : Blo 1080619 1626185 := bstep (se 2 (by rfl) ⟨609819, by rfl⟩ : syracuseStep 1626185 = 1219639) B1219639
theorem B1626299 : Blo 1080619 1626299 := bstep (se 1 (by rfl) ⟨1219724, by rfl⟩ : syracuseStep 1626299 = 2439449) B2439449
theorem B1626359 : Blo 1080619 1626359 := bstep (se 1 (by rfl) ⟨1219769, by rfl⟩ : syracuseStep 1626359 = 2439539) B2439539
theorem B1626383 : Blo 1080619 1626383 := bstep (se 1 (by rfl) ⟨1219787, by rfl⟩ : syracuseStep 1626383 = 2439575) B2439575
theorem B2740513 : Blo 1080619 2740513 := bstep (se 2 (by rfl) ⟨1027692, by rfl⟩ : syracuseStep 2740513 = 2055385) B2055385
theorem B1626425 : Blo 1080619 1626425 := bstep (se 2 (by rfl) ⟨609909, by rfl⟩ : syracuseStep 1626425 = 1219819) B1219819
theorem B1626503 : Blo 1080619 1626503 := bstep (se 1 (by rfl) ⟨1219877, by rfl⟩ : syracuseStep 1626503 = 2439755) B2439755
theorem B1626539 : Blo 1080619 1626539 := bstep (se 1 (by rfl) ⟨1219904, by rfl⟩ : syracuseStep 1626539 = 2439809) B2439809
theorem B2052553 : Blo 1080619 2052553 := bstep (se 2 (by rfl) ⟨769707, by rfl⟩ : syracuseStep 2052553 = 1539415) B1539415
theorem B1626569 : Blo 1080619 1626569 := bstep (se 2 (by rfl) ⟨609963, by rfl⟩ : syracuseStep 1626569 = 1219927) B1219927
theorem B3658283 : Blo 1080619 3658283 := bstep (se 1 (by rfl) ⟨2743712, by rfl⟩ : syracuseStep 3658283 = 5487425) B5487425
theorem B1626683 : Blo 1080619 1626683 := bstep (se 1 (by rfl) ⟨1220012, by rfl⟩ : syracuseStep 1626683 = 2440025) B2440025
theorem B6935159 : Blo 1080619 6935159 := bstep (se 1 (by rfl) ⟨5201369, by rfl⟩ : syracuseStep 6935159 = 10402739) B10402739
theorem B1626743 : Blo 1080619 1626743 := bstep (se 1 (by rfl) ⟨1220057, by rfl⟩ : syracuseStep 1626743 = 2440115) B2440115
theorem B1626767 : Blo 1080619 1626767 := bstep (se 1 (by rfl) ⟨1220075, by rfl⟩ : syracuseStep 1626767 = 2440151) B2440151
theorem B1626809 : Blo 1080619 1626809 := bstep (se 2 (by rfl) ⟨610053, by rfl⟩ : syracuseStep 1626809 = 1220107) B1220107
theorem B1626887 : Blo 1080619 1626887 := bstep (se 1 (by rfl) ⟨1220165, by rfl⟩ : syracuseStep 1626887 = 2440331) B2440331
theorem B3461903 : Blo 1080619 3461903 := bstep (se 1 (by rfl) ⟨2596427, by rfl⟩ : syracuseStep 3461903 = 5192855) B5192855
theorem B1626923 : Blo 1080619 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B2741111 : Blo 1080619 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B1823863 : Blo 1080619 1823863 := bstep (se 1 (by rfl) ⟨1367897, by rfl⟩ : syracuseStep 1823863 = 2735795) B2735795
theorem B1824059 : Blo 1080619 1824059 := bstep (se 1 (by rfl) ⟨1368044, by rfl⟩ : syracuseStep 1824059 = 2736089) B2736089
theorem B6346129 : Blo 1080619 6346129 := bstep (se 2 (by rfl) ⟨2379798, by rfl⟩ : syracuseStep 6346129 = 4759597) B4759597
theorem B41178545 : Blo 1080619 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B2774663 : Blo 1080619 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B1824457 : Blo 1080619 1824457 := bstep (se 2 (by rfl) ⟨684171, by rfl⟩ : syracuseStep 1824457 = 1368343) B1368343
theorem B17553125 : Blo 1080619 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B3659579 : Blo 1080619 3659579 := bstep (se 1 (by rfl) ⟨2744684, by rfl⟩ : syracuseStep 3659579 = 5489369) B5489369
theorem B2775073 : Blo 1080619 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B2742407 : Blo 1080619 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B2742457 : Blo 1080619 2742457 := bstep (se 2 (by rfl) ⟨1028421, by rfl⟩ : syracuseStep 2742457 = 2056843) B2056843
theorem B3660065 : Blo 1080619 3660065 := bstep (se 2 (by rfl) ⟨1372524, by rfl⟩ : syracuseStep 3660065 = 2745049) B2745049
theorem B5855539 : Blo 1080619 5855539 := bstep (se 1 (by rfl) ⟨4391654, by rfl⟩ : syracuseStep 5855539 = 8783309) B8783309
theorem B2054459 : Blo 1080619 2054459 := bstep (se 1 (by rfl) ⟨1540844, by rfl⟩ : syracuseStep 2054459 = 3081689) B3081689
theorem B1825159 : Blo 1080619 1825159 := bstep (se 1 (by rfl) ⟨1368869, by rfl⟩ : syracuseStep 1825159 = 2737739) B2737739
theorem B1301035 : Blo 1080619 1301035 := bstep (se 1 (by rfl) ⟨975776, by rfl⟩ : syracuseStep 1301035 = 1951553) B1951553
theorem B10541747 : Blo 1080619 10541747 := bstep (se 1 (by rfl) ⟨7906310, by rfl⟩ : syracuseStep 10541747 = 15812621) B15812621
theorem B3005185 : Blo 1080619 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B1235719 : Blo 1080619 1235719 := bstep (se 1 (by rfl) ⟨926789, by rfl⟩ : syracuseStep 1235719 = 1853579) B1853579
theorem B2743055 : Blo 1080619 2743055 := bstep (se 1 (by rfl) ⟨2057291, by rfl⟩ : syracuseStep 2743055 = 4114583) B4114583
theorem B2054945 : Blo 1080619 2054945 := bstep (se 2 (by rfl) ⟨770604, by rfl⟩ : syracuseStep 2054945 = 1541209) B1541209
theorem B1825807 : Blo 1080619 1825807 := bstep (se 1 (by rfl) ⟨1369355, by rfl⟩ : syracuseStep 1825807 = 2738711) B2738711
theorem B3464311 : Blo 1080619 3464311 := bstep (se 1 (by rfl) ⟨2598233, by rfl⟩ : syracuseStep 3464311 = 5196467) B5196467
theorem B2055287 : Blo 1080619 2055287 := bstep (se 1 (by rfl) ⟨1541465, by rfl⟩ : syracuseStep 2055287 = 3082931) B3082931
theorem B2743753 : Blo 1080619 2743753 := bstep (se 2 (by rfl) ⟨1028907, by rfl⟩ : syracuseStep 2743753 = 2057815) B2057815
theorem B6250007 : Blo 1080619 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B1826347 : Blo 1080619 1826347 := bstep (se 1 (by rfl) ⟨1369760, by rfl⟩ : syracuseStep 1826347 = 2739521) B2739521
theorem B2743895 : Blo 1080619 2743895 := bstep (se 1 (by rfl) ⟨2057921, by rfl⟩ : syracuseStep 2743895 = 4115843) B4115843
theorem B1367695 : Blo 1080619 1367695 := bstep (se 1 (by rfl) ⟨1025771, by rfl⟩ : syracuseStep 1367695 = 2051543) B2051543
theorem B1564303 : Blo 1080619 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B1826489 : Blo 1080619 1826489 := bstep (se 2 (by rfl) ⟨684933, by rfl⟩ : syracuseStep 1826489 = 1369867) B1369867
theorem B11722457 : Blo 1080619 11722457 := bstep (se 2 (by rfl) ⟨4395921, by rfl⟩ : syracuseStep 11722457 = 8791843) B8791843
theorem B1367867 : Blo 1080619 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B9232217 : Blo 1080619 9232217 := bstep (se 2 (by rfl) ⟨3462081, by rfl⟩ : syracuseStep 9232217 = 6924163) B6924163
theorem B27779273 : Blo 1080619 27779273 := bstep (se 2 (by rfl) ⟨10417227, by rfl⟩ : syracuseStep 27779273 = 20834455) B20834455
theorem B1827191 : Blo 1080619 1827191 := bstep (se 1 (by rfl) ⟨1370393, by rfl⟩ : syracuseStep 1827191 = 2740787) B2740787
theorem B1302971 : Blo 1080619 1302971 := bstep (se 1 (by rfl) ⟨977228, by rfl⟩ : syracuseStep 1302971 = 1954457) B1954457
theorem B2056889 : Blo 1080619 2056889 := bstep (se 2 (by rfl) ⟨771333, by rfl⟩ : syracuseStep 2056889 = 1542667) B1542667
theorem B1368839 : Blo 1080619 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B1827643 : Blo 1080619 1827643 := bstep (se 1 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 1827643 = 2741465) B2741465
theorem B1827785 : Blo 1080619 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B2057231 : Blo 1080619 2057231 := bstep (se 1 (by rfl) ⟨1542923, by rfl⟩ : syracuseStep 2057231 = 3085847) B3085847
theorem B8217773 : Blo 1080619 8217773 := bstep (se 3 (by rfl) ⟨1540832, by rfl⟩ : syracuseStep 8217773 = 3081665) B3081665
theorem B1369487 : Blo 1080619 1369487 := bstep (se 1 (by rfl) ⟨1027115, by rfl⟩ : syracuseStep 1369487 = 2054231) B2054231
theorem B1828487 : Blo 1080619 1828487 := bstep (se 1 (by rfl) ⟨1371365, by rfl⟩ : syracuseStep 1828487 = 2742731) B2742731
theorem B5203693 : Blo 1080619 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B2058043 : Blo 1080619 2058043 := bstep (se 1 (by rfl) ⟨1543532, by rfl⟩ : syracuseStep 2058043 = 3087065) B3087065
theorem B2058119 : Blo 1080619 2058119 := bstep (se 1 (by rfl) ⟨1543589, by rfl⟩ : syracuseStep 2058119 = 3087179) B3087179
theorem B11724917 : Blo 1080619 11724917 := bstep (se 5 (by rfl) ⟨549605, by rfl⟩ : syracuseStep 11724917 = 1099211) B1099211
theorem B1829135 : Blo 1080619 1829135 := bstep (se 1 (by rfl) ⟨1371851, by rfl⟩ : syracuseStep 1829135 = 2743703) B2743703
theorem B2058529 : Blo 1080619 2058529 := bstep (se 2 (by rfl) ⟨771948, by rfl⟩ : syracuseStep 2058529 = 1543897) B1543897
theorem B2058871 : Blo 1080619 2058871 := bstep (se 1 (by rfl) ⟨1544153, by rfl⟩ : syracuseStep 2058871 = 3088307) B3088307
theorem B1829675 : Blo 1080619 1829675 := bstep (se 1 (by rfl) ⟨1372256, by rfl⟩ : syracuseStep 1829675 = 2744513) B2744513
theorem B7498547 : Blo 1080619 7498547 := bstep (se 1 (by rfl) ⟨5623910, by rfl⟩ : syracuseStep 7498547 = 11247821) B11247821
theorem B2255887 : Blo 1080619 2255887 := bstep (se 1 (by rfl) ⟨1691915, by rfl⟩ : syracuseStep 2255887 = 3383831) B3383831
theorem B1830073 : Blo 1080619 1830073 := bstep (se 2 (by rfl) ⟨686277, by rfl⟩ : syracuseStep 1830073 = 1372555) B1372555
theorem B1731899 : Blo 1080619 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B15822215 : Blo 1080619 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B126610897 : Blo 1080619 126610897 := bstep (se 2 (by rfl) ⟨47479086, by rfl⟩ : syracuseStep 126610897 = 94958173) B94958173
theorem B8220203 : Blo 1080619 8220203 := bstep (se 1 (by rfl) ⟨6165152, by rfl⟩ : syracuseStep 8220203 = 12330305) B12330305
theorem B6155837 : Blo 1080619 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B4615937 : Blo 1080619 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B12349259 : Blo 1080619 12349259 := bstep (se 1 (by rfl) ⟨9261944, by rfl⟩ : syracuseStep 12349259 = 18523889) B18523889
theorem B46755737 : Blo 1080619 46755737 := bstep (se 2 (by rfl) ⟨17533401, by rfl⟩ : syracuseStep 46755737 = 35066803) B35066803
theorem B6942617 : Blo 1080619 6942617 := bstep (se 2 (by rfl) ⟨2603481, by rfl⟩ : syracuseStep 6942617 = 5206963) B5206963
theorem B4943825 : Blo 1080619 4943825 := bstep (se 2 (by rfl) ⟨1853934, by rfl⟩ : syracuseStep 4943825 = 3707869) B3707869
theorem B45117461 : Blo 1080619 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B1372459 : Blo 1080619 1372459 := bstep (se 1 (by rfl) ⟨1029344, by rfl⟩ : syracuseStep 1372459 = 2058689) B2058689
theorem B13169081 : Blo 1080619 13169081 := bstep (se 2 (by rfl) ⟨4938405, by rfl⟩ : syracuseStep 13169081 = 9876811) B9876811
theorem B2192519 : Blo 1080619 2192519 := bstep (se 1 (by rfl) ⟨1644389, by rfl⟩ : syracuseStep 2192519 = 3288779) B3288779
theorem B3339667 : Blo 1080619 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B56260025 : Blo 1080619 56260025 := bstep (se 2 (by rfl) ⟨21097509, by rfl⟩ : syracuseStep 56260025 = 42195019) B42195019
theorem B4388413 : Blo 1080619 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B3077747 : Blo 1080619 3077747 := bstep (se 1 (by rfl) ⟨2308310, by rfl⟩ : syracuseStep 3077747 = 4616621) B4616621
theorem B1111739 : Blo 1080619 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B3077975 : Blo 1080619 3077975 := bstep (se 1 (by rfl) ⟨2308481, by rfl⟩ : syracuseStep 3077975 = 4616963) B4616963
theorem B4945799 : Blo 1080619 4945799 := bstep (se 1 (by rfl) ⟨3709349, by rfl⟩ : syracuseStep 4945799 = 7418699) B7418699
theorem B6158227 : Blo 1080619 6158227 := bstep (se 1 (by rfl) ⟨4618670, by rfl⟩ : syracuseStep 6158227 = 9237341) B9237341
theorem B7043627 : Blo 1080619 7043627 := bstep (se 1 (by rfl) ⟨5282720, by rfl⟩ : syracuseStep 7043627 = 10565441) B10565441
theorem B3898145 : Blo 1080619 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B13171571 : Blo 1080619 13171571 := bstep (se 1 (by rfl) ⟨9878678, by rfl⟩ : syracuseStep 13171571 = 19757357) B19757357
theorem B20774177 : Blo 1080619 20774177 := bstep (se 2 (by rfl) ⟨7790316, by rfl⟩ : syracuseStep 20774177 = 15580633) B15580633
theorem B1080635 : Blo 1080619 1080635 := bstep (se 1 (by rfl) ⟨810476, by rfl⟩ : syracuseStep 1080635 = 1620953) B1620953
theorem B1080711 : Blo 1080619 1080711 := bstep (se 1 (by rfl) ⟨810533, by rfl⟩ : syracuseStep 1080711 = 1621067) B1621067
theorem B3079559 : Blo 1080619 3079559 := bstep (se 1 (by rfl) ⟨2309669, by rfl⟩ : syracuseStep 3079559 = 4619339) B4619339
theorem B1080719 : Blo 1080619 1080719 := bstep (se 1 (by rfl) ⟨810539, by rfl⟩ : syracuseStep 1080719 = 1621079) B1621079
theorem B1080763 : Blo 1080619 1080763 := bstep (se 1 (by rfl) ⟨810572, by rfl⟩ : syracuseStep 1080763 = 1621145) B1621145
theorem B6946307 : Blo 1080619 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B1080839 : Blo 1080619 1080839 := bstep (se 1 (by rfl) ⟨810629, by rfl⟩ : syracuseStep 1080839 = 1621259) B1621259
theorem B1080847 : Blo 1080619 1080847 := bstep (se 1 (by rfl) ⟨810635, by rfl⟩ : syracuseStep 1080847 = 1621271) B1621271
theorem B1080891 : Blo 1080619 1080891 := bstep (se 1 (by rfl) ⟨810668, by rfl⟩ : syracuseStep 1080891 = 1621337) B1621337
theorem B1539643 : Blo 1080619 1539643 := bstep (se 1 (by rfl) ⟨1154732, by rfl⟩ : syracuseStep 1539643 = 2309465) B2309465
theorem B3079741 : Blo 1080619 3079741 := bstep (se 3 (by rfl) ⟨577451, by rfl⟩ : syracuseStep 3079741 = 1154903) B1154903
theorem B6159959 : Blo 1080619 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B1080967 : Blo 1080619 1080967 := bstep (se 1 (by rfl) ⟨810725, by rfl⟩ : syracuseStep 1080967 = 1621451) B1621451
theorem B1080975 : Blo 1080619 1080975 := bstep (se 1 (by rfl) ⟨810731, by rfl⟩ : syracuseStep 1080975 = 1621463) B1621463
theorem B1081019 : Blo 1080619 1081019 := bstep (se 1 (by rfl) ⟨810764, by rfl⟩ : syracuseStep 1081019 = 1621529) B1621529
theorem B1081095 : Blo 1080619 1081095 := bstep (se 1 (by rfl) ⟨810821, by rfl⟩ : syracuseStep 1081095 = 1621643) B1621643
theorem B1081103 : Blo 1080619 1081103 := bstep (se 1 (by rfl) ⟨810827, by rfl⟩ : syracuseStep 1081103 = 1621655) B1621655
theorem B1081147 : Blo 1080619 1081147 := bstep (se 1 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 1081147 = 1621721) B1621721
theorem B1081223 : Blo 1080619 1081223 := bstep (se 1 (by rfl) ⟨810917, by rfl⟩ : syracuseStep 1081223 = 1621835) B1621835
theorem B1081231 : Blo 1080619 1081231 := bstep (se 1 (by rfl) ⟨810923, by rfl⟩ : syracuseStep 1081231 = 1621847) B1621847
theorem B1081275 : Blo 1080619 1081275 := bstep (se 1 (by rfl) ⟨810956, by rfl⟩ : syracuseStep 1081275 = 1621913) B1621913
theorem B1081383 : Blo 1080619 1081383 := bstep (se 1 (by rfl) ⟨811037, by rfl⟩ : syracuseStep 1081383 = 1622075) B1622075
theorem B1081423 : Blo 1080619 1081423 := bstep (se 1 (by rfl) ⟨811067, by rfl⟩ : syracuseStep 1081423 = 1622135) B1622135
theorem B1081439 : Blo 1080619 1081439 := bstep (se 1 (by rfl) ⟨811079, by rfl⟩ : syracuseStep 1081439 = 1622159) B1622159
theorem B1081467 : Blo 1080619 1081467 := bstep (se 1 (by rfl) ⟨811100, by rfl⟩ : syracuseStep 1081467 = 1622201) B1622201
theorem B1081519 : Blo 1080619 1081519 := bstep (se 1 (by rfl) ⟨811139, by rfl⟩ : syracuseStep 1081519 = 1622279) B1622279
theorem B1081543 : Blo 1080619 1081543 := bstep (se 1 (by rfl) ⟨811157, by rfl⟩ : syracuseStep 1081543 = 1622315) B1622315
theorem B1081563 : Blo 1080619 1081563 := bstep (se 1 (by rfl) ⟨811172, by rfl⟩ : syracuseStep 1081563 = 1622345) B1622345
theorem B1081639 : Blo 1080619 1081639 := bstep (se 1 (by rfl) ⟨811229, by rfl⟩ : syracuseStep 1081639 = 1622459) B1622459
theorem B1081679 : Blo 1080619 1081679 := bstep (se 1 (by rfl) ⟨811259, by rfl⟩ : syracuseStep 1081679 = 1622519) B1622519
theorem B1081695 : Blo 1080619 1081695 := bstep (se 1 (by rfl) ⟨811271, by rfl⟩ : syracuseStep 1081695 = 1622543) B1622543
theorem B1081723 : Blo 1080619 1081723 := bstep (se 1 (by rfl) ⟨811292, by rfl⟩ : syracuseStep 1081723 = 1622585) B1622585
theorem B1081775 : Blo 1080619 1081775 := bstep (se 1 (by rfl) ⟨811331, by rfl⟩ : syracuseStep 1081775 = 1622663) B1622663
theorem B1081799 : Blo 1080619 1081799 := bstep (se 1 (by rfl) ⟨811349, by rfl⟩ : syracuseStep 1081799 = 1622699) B1622699
theorem B1081819 : Blo 1080619 1081819 := bstep (se 1 (by rfl) ⟨811364, by rfl⟩ : syracuseStep 1081819 = 1622729) B1622729
theorem B1081895 : Blo 1080619 1081895 := bstep (se 1 (by rfl) ⟨811421, by rfl⟩ : syracuseStep 1081895 = 1622843) B1622843
theorem B1081935 : Blo 1080619 1081935 := bstep (se 1 (by rfl) ⟨811451, by rfl⟩ : syracuseStep 1081935 = 1622903) B1622903
theorem B1081951 : Blo 1080619 1081951 := bstep (se 1 (by rfl) ⟨811463, by rfl⟩ : syracuseStep 1081951 = 1622927) B1622927
theorem B1081979 : Blo 1080619 1081979 := bstep (se 1 (by rfl) ⟨811484, by rfl⟩ : syracuseStep 1081979 = 1622969) B1622969
theorem B1082031 : Blo 1080619 1082031 := bstep (se 1 (by rfl) ⟨811523, by rfl⟩ : syracuseStep 1082031 = 1623047) B1623047
theorem B1082055 : Blo 1080619 1082055 := bstep (se 1 (by rfl) ⟨811541, by rfl⟩ : syracuseStep 1082055 = 1623083) B1623083
theorem B10978001 : Blo 1080619 10978001 := bstep (se 2 (by rfl) ⟨4116750, by rfl⟩ : syracuseStep 10978001 = 8233501) B8233501
theorem B1082075 : Blo 1080619 1082075 := bstep (se 1 (by rfl) ⟨811556, by rfl⟩ : syracuseStep 1082075 = 1623113) B1623113
theorem B1082151 : Blo 1080619 1082151 := bstep (se 1 (by rfl) ⟨811613, by rfl⟩ : syracuseStep 1082151 = 1623227) B1623227
theorem B1082191 : Blo 1080619 1082191 := bstep (se 1 (by rfl) ⟨811643, by rfl⟩ : syracuseStep 1082191 = 1623287) B1623287
theorem B1082207 : Blo 1080619 1082207 := bstep (se 1 (by rfl) ⟨811655, by rfl⟩ : syracuseStep 1082207 = 1623311) B1623311
theorem B1082235 : Blo 1080619 1082235 := bstep (se 1 (by rfl) ⟨811676, by rfl⟩ : syracuseStep 1082235 = 1623353) B1623353
theorem B1082287 : Blo 1080619 1082287 := bstep (se 1 (by rfl) ⟨811715, by rfl⟩ : syracuseStep 1082287 = 1623431) B1623431
theorem B1082311 : Blo 1080619 1082311 := bstep (se 1 (by rfl) ⟨811733, by rfl⟩ : syracuseStep 1082311 = 1623467) B1623467
theorem B1082331 : Blo 1080619 1082331 := bstep (se 1 (by rfl) ⟨811748, by rfl⟩ : syracuseStep 1082331 = 1623497) B1623497
theorem B15631379 : Blo 1080619 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B1082407 : Blo 1080619 1082407 := bstep (se 1 (by rfl) ⟨811805, by rfl⟩ : syracuseStep 1082407 = 1623611) B1623611
theorem B5473331 : Blo 1080619 5473331 := bstep (se 1 (by rfl) ⟨4104998, by rfl⟩ : syracuseStep 5473331 = 8209997) B8209997
theorem B1082447 : Blo 1080619 1082447 := bstep (se 1 (by rfl) ⟨811835, by rfl⟩ : syracuseStep 1082447 = 1623671) B1623671
theorem B1082463 : Blo 1080619 1082463 := bstep (se 1 (by rfl) ⟨811847, by rfl⟩ : syracuseStep 1082463 = 1623695) B1623695
theorem B1082491 : Blo 1080619 1082491 := bstep (se 1 (by rfl) ⟨811868, by rfl⟩ : syracuseStep 1082491 = 1623737) B1623737
theorem B3474589 : Blo 1080619 3474589 := bstep (se 3 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 3474589 = 1302971) B1302971
theorem B1082543 : Blo 1080619 1082543 := bstep (se 1 (by rfl) ⟨811907, by rfl⟩ : syracuseStep 1082543 = 1623815) B1623815
theorem B1082567 : Blo 1080619 1082567 := bstep (se 1 (by rfl) ⟨811925, by rfl⟩ : syracuseStep 1082567 = 1623851) B1623851
theorem B1082587 : Blo 1080619 1082587 := bstep (se 1 (by rfl) ⟨811940, by rfl⟩ : syracuseStep 1082587 = 1623881) B1623881
theorem B1082663 : Blo 1080619 1082663 := bstep (se 1 (by rfl) ⟨811997, by rfl⟩ : syracuseStep 1082663 = 1623995) B1623995
theorem B1082703 : Blo 1080619 1082703 := bstep (se 1 (by rfl) ⟨812027, by rfl⟩ : syracuseStep 1082703 = 1624055) B1624055
theorem B1082719 : Blo 1080619 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B1082747 : Blo 1080619 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B1082799 : Blo 1080619 1082799 := bstep (se 1 (by rfl) ⟨812099, by rfl⟩ : syracuseStep 1082799 = 1624199) B1624199
theorem B1082823 : Blo 1080619 1082823 := bstep (se 1 (by rfl) ⟨812117, by rfl⟩ : syracuseStep 1082823 = 1624235) B1624235
theorem B1082843 : Blo 1080619 1082843 := bstep (se 1 (by rfl) ⟨812132, by rfl⟩ : syracuseStep 1082843 = 1624265) B1624265
theorem B1082919 : Blo 1080619 1082919 := bstep (se 1 (by rfl) ⟨812189, by rfl⟩ : syracuseStep 1082919 = 1624379) B1624379
theorem B1082959 : Blo 1080619 1082959 := bstep (se 1 (by rfl) ⟨812219, by rfl⟩ : syracuseStep 1082959 = 1624439) B1624439
theorem B1082975 : Blo 1080619 1082975 := bstep (se 1 (by rfl) ⟨812231, by rfl⟩ : syracuseStep 1082975 = 1624463) B1624463
theorem B1083003 : Blo 1080619 1083003 := bstep (se 1 (by rfl) ⟨812252, by rfl⟩ : syracuseStep 1083003 = 1624505) B1624505
theorem B1083055 : Blo 1080619 1083055 := bstep (se 1 (by rfl) ⟨812291, by rfl⟩ : syracuseStep 1083055 = 1624583) B1624583
theorem B1083079 : Blo 1080619 1083079 := bstep (se 1 (by rfl) ⟨812309, by rfl⟩ : syracuseStep 1083079 = 1624619) B1624619
theorem B1083099 : Blo 1080619 1083099 := bstep (se 1 (by rfl) ⟨812324, by rfl⟩ : syracuseStep 1083099 = 1624649) B1624649
theorem B1083175 : Blo 1080619 1083175 := bstep (se 1 (by rfl) ⟨812381, by rfl⟩ : syracuseStep 1083175 = 1624763) B1624763
theorem B4622123 : Blo 1080619 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B1083215 : Blo 1080619 1083215 := bstep (se 1 (by rfl) ⟨812411, by rfl⟩ : syracuseStep 1083215 = 1624823) B1624823
theorem B1083231 : Blo 1080619 1083231 := bstep (se 1 (by rfl) ⟨812423, by rfl⟩ : syracuseStep 1083231 = 1624847) B1624847
theorem B1083259 : Blo 1080619 1083259 := bstep (se 1 (by rfl) ⟨812444, by rfl⟩ : syracuseStep 1083259 = 1624889) B1624889
theorem B1083311 : Blo 1080619 1083311 := bstep (se 1 (by rfl) ⟨812483, by rfl⟩ : syracuseStep 1083311 = 1624967) B1624967
theorem B1083335 : Blo 1080619 1083335 := bstep (se 1 (by rfl) ⟨812501, by rfl⟩ : syracuseStep 1083335 = 1625003) B1625003
theorem B1083355 : Blo 1080619 1083355 := bstep (se 1 (by rfl) ⟨812516, by rfl⟩ : syracuseStep 1083355 = 1625033) B1625033
theorem B1083431 : Blo 1080619 1083431 := bstep (se 1 (by rfl) ⟨812573, by rfl⟩ : syracuseStep 1083431 = 1625147) B1625147
theorem B1083471 : Blo 1080619 1083471 := bstep (se 1 (by rfl) ⟨812603, by rfl⟩ : syracuseStep 1083471 = 1625207) B1625207
theorem B1083487 : Blo 1080619 1083487 := bstep (se 1 (by rfl) ⟨812615, by rfl⟩ : syracuseStep 1083487 = 1625231) B1625231
theorem B1083515 : Blo 1080619 1083515 := bstep (se 1 (by rfl) ⟨812636, by rfl⟩ : syracuseStep 1083515 = 1625273) B1625273
theorem B1083567 : Blo 1080619 1083567 := bstep (se 1 (by rfl) ⟨812675, by rfl⟩ : syracuseStep 1083567 = 1625351) B1625351
theorem B1083591 : Blo 1080619 1083591 := bstep (se 1 (by rfl) ⟨812693, by rfl⟩ : syracuseStep 1083591 = 1625387) B1625387
theorem B1083611 : Blo 1080619 1083611 := bstep (se 1 (by rfl) ⟨812708, by rfl⟩ : syracuseStep 1083611 = 1625417) B1625417
theorem B1083687 : Blo 1080619 1083687 := bstep (se 1 (by rfl) ⟨812765, by rfl⟩ : syracuseStep 1083687 = 1625531) B1625531
theorem B1083727 : Blo 1080619 1083727 := bstep (se 1 (by rfl) ⟨812795, by rfl⟩ : syracuseStep 1083727 = 1625591) B1625591
theorem B1083743 : Blo 1080619 1083743 := bstep (se 1 (by rfl) ⟨812807, by rfl⟩ : syracuseStep 1083743 = 1625615) B1625615
theorem B1083771 : Blo 1080619 1083771 := bstep (se 1 (by rfl) ⟨812828, by rfl⟩ : syracuseStep 1083771 = 1625657) B1625657
theorem B31230359 : Blo 1080619 31230359 := bstep (se 1 (by rfl) ⟨23422769, by rfl⟩ : syracuseStep 31230359 = 46845539) B46845539
theorem B1083823 : Blo 1080619 1083823 := bstep (se 1 (by rfl) ⟨812867, by rfl⟩ : syracuseStep 1083823 = 1625735) B1625735
theorem B1083847 : Blo 1080619 1083847 := bstep (se 1 (by rfl) ⟨812885, by rfl⟩ : syracuseStep 1083847 = 1625771) B1625771
theorem B1083867 : Blo 1080619 1083867 := bstep (se 1 (by rfl) ⟨812900, by rfl⟩ : syracuseStep 1083867 = 1625801) B1625801
theorem B1083943 : Blo 1080619 1083943 := bstep (se 1 (by rfl) ⟨812957, by rfl⟩ : syracuseStep 1083943 = 1625915) B1625915
theorem B1083983 : Blo 1080619 1083983 := bstep (se 1 (by rfl) ⟨812987, by rfl⟩ : syracuseStep 1083983 = 1625975) B1625975
theorem B1083999 : Blo 1080619 1083999 := bstep (se 1 (by rfl) ⟨812999, by rfl⟩ : syracuseStep 1083999 = 1625999) B1625999
theorem B1084027 : Blo 1080619 1084027 := bstep (se 1 (by rfl) ⟨813020, by rfl⟩ : syracuseStep 1084027 = 1626041) B1626041
theorem B5474951 : Blo 1080619 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B1084079 : Blo 1080619 1084079 := bstep (se 1 (by rfl) ⟨813059, by rfl⟩ : syracuseStep 1084079 = 1626119) B1626119
theorem B1084103 : Blo 1080619 1084103 := bstep (se 1 (by rfl) ⟨813077, by rfl⟩ : syracuseStep 1084103 = 1626155) B1626155
theorem B1084123 : Blo 1080619 1084123 := bstep (se 1 (by rfl) ⟨813092, by rfl⟩ : syracuseStep 1084123 = 1626185) B1626185
theorem B1084199 : Blo 1080619 1084199 := bstep (se 1 (by rfl) ⟨813149, by rfl⟩ : syracuseStep 1084199 = 1626299) B1626299
theorem B1084239 : Blo 1080619 1084239 := bstep (se 1 (by rfl) ⟨813179, by rfl⟩ : syracuseStep 1084239 = 1626359) B1626359
theorem B1084255 : Blo 1080619 1084255 := bstep (se 1 (by rfl) ⟨813191, by rfl⟩ : syracuseStep 1084255 = 1626383) B1626383
theorem B1084283 : Blo 1080619 1084283 := bstep (se 1 (by rfl) ⟨813212, by rfl⟩ : syracuseStep 1084283 = 1626425) B1626425
theorem B1084335 : Blo 1080619 1084335 := bstep (se 1 (by rfl) ⟨813251, by rfl⟩ : syracuseStep 1084335 = 1626503) B1626503
theorem B1084359 : Blo 1080619 1084359 := bstep (se 1 (by rfl) ⟨813269, by rfl⟩ : syracuseStep 1084359 = 1626539) B1626539
theorem B1084379 : Blo 1080619 1084379 := bstep (se 1 (by rfl) ⟨813284, by rfl⟩ : syracuseStep 1084379 = 1626569) B1626569
theorem B1084455 : Blo 1080619 1084455 := bstep (se 1 (by rfl) ⟨813341, by rfl⟩ : syracuseStep 1084455 = 1626683) B1626683
theorem B4623439 : Blo 1080619 4623439 := bstep (se 1 (by rfl) ⟨3467579, by rfl⟩ : syracuseStep 4623439 = 6935159) B6935159
theorem B1084495 : Blo 1080619 1084495 := bstep (se 1 (by rfl) ⟨813371, by rfl⟩ : syracuseStep 1084495 = 1626743) B1626743
theorem B1084511 : Blo 1080619 1084511 := bstep (se 1 (by rfl) ⟨813383, by rfl⟩ : syracuseStep 1084511 = 1626767) B1626767
theorem B1084539 : Blo 1080619 1084539 := bstep (se 1 (by rfl) ⟨813404, by rfl⟩ : syracuseStep 1084539 = 1626809) B1626809
theorem B1084591 : Blo 1080619 1084591 := bstep (se 1 (by rfl) ⟨813443, by rfl⟩ : syracuseStep 1084591 = 1626887) B1626887
theorem B1084615 : Blo 1080619 1084615 := bstep (se 1 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 1084615 = 1626923) B1626923
theorem B6163877 : Blo 1080619 6163877 := bstep (se 4 (by rfl) ⟨577863, by rfl⟩ : syracuseStep 6163877 = 1155727) B1155727
theorem B1216039 : Blo 1080619 1216039 := bstep (se 1 (by rfl) ⟨912029, by rfl⟩ : syracuseStep 1216039 = 1824059) B1824059
theorem B11702083 : Blo 1080619 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B6164333 : Blo 1080619 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B5476409 : Blo 1080619 5476409 := bstep (se 2 (by rfl) ⟨2053653, by rfl⟩ : syracuseStep 5476409 = 4107307) B4107307
theorem B13898249 : Blo 1080619 13898249 := bstep (se 2 (by rfl) ⟨5211843, by rfl⟩ : syracuseStep 13898249 = 10423687) B10423687
theorem B6165017 : Blo 1080619 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B33297409 : Blo 1080619 33297409 := bstep (se 2 (by rfl) ⟨12486528, by rfl⟩ : syracuseStep 33297409 = 24973057) B24973057
theorem B4166671 : Blo 1080619 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B3085391 : Blo 1080619 3085391 := bstep (se 1 (by rfl) ⟨2314043, by rfl⟩ : syracuseStep 3085391 = 4628087) B4628087
theorem B1217659 : Blo 1080619 1217659 := bstep (se 1 (by rfl) ⟨913244, by rfl⟩ : syracuseStep 1217659 = 1826489) B1826489
theorem B18519515 : Blo 1080619 18519515 := bstep (se 1 (by rfl) ⟨13889636, by rfl⟩ : syracuseStep 18519515 = 27779273) B27779273
theorem B1218127 : Blo 1080619 1218127 := bstep (se 1 (by rfl) ⟨913595, by rfl⟩ : syracuseStep 1218127 = 1827191) B1827191
theorem B31266445 : Blo 1080619 31266445 := bstep (se 3 (by rfl) ⟨5862458, by rfl⟩ : syracuseStep 31266445 = 11724917) B11724917
theorem B3086039 : Blo 1080619 3086039 := bstep (se 1 (by rfl) ⟨2314529, by rfl⟩ : syracuseStep 3086039 = 4629059) B4629059
theorem B1218523 : Blo 1080619 1218523 := bstep (se 1 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 1218523 = 1827785) B1827785
theorem B5478515 : Blo 1080619 5478515 := bstep (se 1 (by rfl) ⟨4108886, by rfl⟩ : syracuseStep 5478515 = 8217773) B8217773
theorem B1218991 : Blo 1080619 1218991 := bstep (se 1 (by rfl) ⟨914243, by rfl⟩ : syracuseStep 1218991 = 1828487) B1828487
theorem B6167249 : Blo 1080619 6167249 := bstep (se 2 (by rfl) ⟨2312718, by rfl⟩ : syracuseStep 6167249 = 4625437) B4625437
theorem B2431817 : Blo 1080619 2431817 := bstep (se 2 (by rfl) ⟨911931, by rfl⟩ : syracuseStep 2431817 = 1823863) B1823863
theorem B3906377 : Blo 1080619 3906377 := bstep (se 2 (by rfl) ⟨1464891, by rfl⟩ : syracuseStep 3906377 = 2929783) B2929783
theorem B1219423 : Blo 1080619 1219423 := bstep (se 1 (by rfl) ⟨914567, by rfl⟩ : syracuseStep 1219423 = 1829135) B1829135
theorem B8461505 : Blo 1080619 8461505 := bstep (se 2 (by rfl) ⟨3173064, by rfl⟩ : syracuseStep 8461505 = 6346129) B6346129
theorem B1219783 : Blo 1080619 1219783 := bstep (se 1 (by rfl) ⟨914837, by rfl⟩ : syracuseStep 1219783 = 1829675) B1829675
theorem B2923901 : Blo 1080619 2923901 := bstep (se 3 (by rfl) ⟨548231, by rfl⟩ : syracuseStep 2923901 = 1096463) B1096463
theorem B6167933 : Blo 1080619 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B10395053 : Blo 1080619 10395053 := bstep (se 3 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 10395053 = 3898145) B3898145
theorem B18488897 : Blo 1080619 18488897 := bstep (se 2 (by rfl) ⟨6933336, by rfl⟩ : syracuseStep 18488897 = 13866673) B13866673
theorem B2432609 : Blo 1080619 2432609 := bstep (se 2 (by rfl) ⟨912228, by rfl⟩ : syracuseStep 2432609 = 1824457) B1824457
theorem B5480135 : Blo 1080619 5480135 := bstep (se 1 (by rfl) ⟨4110101, by rfl⟩ : syracuseStep 5480135 = 8220203) B8220203
theorem B4103891 : Blo 1080619 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B8232839 : Blo 1080619 8232839 := bstep (se 1 (by rfl) ⟨6174629, by rfl⟩ : syracuseStep 8232839 = 12349259) B12349259
theorem B2432951 : Blo 1080619 2432951 := bstep (se 1 (by rfl) ⟨1824713, by rfl⟩ : syracuseStep 2432951 = 3649427) B3649427
theorem B31170491 : Blo 1080619 31170491 := bstep (se 1 (by rfl) ⟨23377868, by rfl⟩ : syracuseStep 31170491 = 46755737) B46755737
theorem B4628411 : Blo 1080619 4628411 := bstep (se 1 (by rfl) ⟨3471308, by rfl⟩ : syracuseStep 4628411 = 6942617) B6942617
theorem B7807385 : Blo 1080619 7807385 := bstep (se 2 (by rfl) ⟨2927769, by rfl⟩ : syracuseStep 7807385 = 5855539) B5855539
theorem B2433545 : Blo 1080619 2433545 := bstep (se 2 (by rfl) ⟨912579, by rfl⟩ : syracuseStep 2433545 = 1825159) B1825159
theorem B2433887 : Blo 1080619 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B4006913 : Blo 1080619 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B1647625 : Blo 1080619 1647625 := bstep (se 2 (by rfl) ⟨617859, by rfl⟩ : syracuseStep 1647625 = 1235719) B1235719
theorem B2434067 : Blo 1080619 2434067 := bstep (se 1 (by rfl) ⟨1825550, by rfl⟩ : syracuseStep 2434067 = 3651101) B3651101
theorem B2434409 : Blo 1080619 2434409 := bstep (se 2 (by rfl) ⟨912903, by rfl⟩ : syracuseStep 2434409 = 1825807) B1825807
theorem B5547437 : Blo 1080619 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B17573365 : Blo 1080619 17573365 := bstep (se 5 (by rfl) ⟨823751, by rfl⟩ : syracuseStep 17573365 = 1647503) B1647503
theorem B35563013 : Blo 1080619 35563013 := bstep (se 4 (by rfl) ⟨3334032, by rfl⟩ : syracuseStep 35563013 = 6668065) B6668065
theorem B7415495 : Blo 1080619 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B4695751 : Blo 1080619 4695751 := bstep (se 1 (by rfl) ⟨3521813, by rfl⟩ : syracuseStep 4695751 = 7043627) B7043627
theorem B2435003 : Blo 1080619 2435003 := bstep (se 1 (by rfl) ⟨1826252, by rfl⟩ : syracuseStep 2435003 = 3652505) B3652505
theorem B2435129 : Blo 1080619 2435129 := bstep (se 2 (by rfl) ⟨913173, by rfl⟩ : syracuseStep 2435129 = 1826347) B1826347
theorem B4106321 : Blo 1080619 4106321 := bstep (se 2 (by rfl) ⟨1539870, by rfl⟩ : syracuseStep 4106321 = 3079741) B3079741
theorem B3647645 : Blo 1080619 3647645 := bstep (se 3 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 3647645 = 1367867) B1367867
theorem B4630871 : Blo 1080619 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B4106639 : Blo 1080619 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B2435471 : Blo 1080619 2435471 := bstep (se 1 (by rfl) ⟨1826603, by rfl⟩ : syracuseStep 2435471 = 3653207) B3653207
theorem B3648185 : Blo 1080619 3648185 := bstep (se 2 (by rfl) ⟨1368069, by rfl⟩ : syracuseStep 3648185 = 2736139) B2736139
theorem B2435795 : Blo 1080619 2435795 := bstep (se 1 (by rfl) ⟨1826846, by rfl⟩ : syracuseStep 2435795 = 3653693) B3653693
theorem B9874511 : Blo 1080619 9874511 := bstep (se 1 (by rfl) ⟨7405883, by rfl⟩ : syracuseStep 9874511 = 14811767) B14811767
theorem B3648779 : Blo 1080619 3648779 := bstep (se 1 (by rfl) ⟨2736584, by rfl⟩ : syracuseStep 3648779 = 5473169) B5473169
theorem B4107581 : Blo 1080619 4107581 := bstep (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) B1540343
theorem B27766151 : Blo 1080619 27766151 := bstep (se 1 (by rfl) ⟨20824613, by rfl⟩ : syracuseStep 27766151 = 41649227) B41649227
theorem B3649049 : Blo 1080619 3649049 := bstep (se 2 (by rfl) ⟨1368393, by rfl⟩ : syracuseStep 3649049 = 2736787) B2736787
theorem B1388111 : Blo 1080619 1388111 := bstep (se 1 (by rfl) ⟨1041083, by rfl⟩ : syracuseStep 1388111 = 2082167) B2082167
theorem B37957207 : Blo 1080619 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B2436731 : Blo 1080619 2436731 := bstep (se 1 (by rfl) ⟨1827548, by rfl⟩ : syracuseStep 2436731 = 3655097) B3655097
theorem B4632187 : Blo 1080619 4632187 := bstep (se 1 (by rfl) ⟨3474140, by rfl⟩ : syracuseStep 4632187 = 6948281) B6948281
theorem B4632203 : Blo 1080619 4632203 := bstep (se 1 (by rfl) ⟨3474152, by rfl⟩ : syracuseStep 4632203 = 6948305) B6948305
theorem B6172307 : Blo 1080619 6172307 := bstep (se 1 (by rfl) ⟨4629230, by rfl⟩ : syracuseStep 6172307 = 9258461) B9258461
theorem B2436857 : Blo 1080619 2436857 := bstep (se 2 (by rfl) ⟨913821, by rfl⟩ : syracuseStep 2436857 = 1827643) B1827643
theorem B13873031 : Blo 1080619 13873031 := bstep (se 1 (by rfl) ⟨10404773, by rfl⟩ : syracuseStep 13873031 = 20809547) B20809547
theorem B2437127 : Blo 1080619 2437127 := bstep (se 1 (by rfl) ⟨1827845, by rfl⟩ : syracuseStep 2437127 = 3655691) B3655691
theorem B2437199 : Blo 1080619 2437199 := bstep (se 1 (by rfl) ⟨1827899, by rfl⟩ : syracuseStep 2437199 = 3655799) B3655799
theorem B17576099 : Blo 1080619 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B2437595 : Blo 1080619 2437595 := bstep (se 1 (by rfl) ⟨1828196, by rfl⟩ : syracuseStep 2437595 = 3656393) B3656393
theorem B3650183 : Blo 1080619 3650183 := bstep (se 1 (by rfl) ⟨2737637, by rfl⟩ : syracuseStep 3650183 = 5475275) B5475275
theorem B3650237 : Blo 1080619 3650237 := bstep (se 3 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 3650237 = 1368839) B1368839
theorem B3650399 : Blo 1080619 3650399 := bstep (se 1 (by rfl) ⟨2737799, by rfl⟩ : syracuseStep 3650399 = 5475599) B5475599
theorem B1389487 : Blo 1080619 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B2438063 : Blo 1080619 2438063 := bstep (se 1 (by rfl) ⟨1828547, by rfl⟩ : syracuseStep 2438063 = 3657095) B3657095
theorem B3650561 : Blo 1080619 3650561 := bstep (se 2 (by rfl) ⟨1368960, by rfl⟩ : syracuseStep 3650561 = 2737921) B2737921
theorem B2438315 : Blo 1080619 2438315 := bstep (se 1 (by rfl) ⟨1828736, by rfl⟩ : syracuseStep 2438315 = 3657473) B3657473
theorem B5485967 : Blo 1080619 5485967 := bstep (se 1 (by rfl) ⟨4114475, by rfl⟩ : syracuseStep 5485967 = 8228951) B8228951
theorem B5846717 : Blo 1080619 5846717 := bstep (se 3 (by rfl) ⟨1096259, by rfl⟩ : syracuseStep 5846717 = 2192519) B2192519
theorem B20821697 : Blo 1080619 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B2930365 : Blo 1080619 2930365 := bstep (se 3 (by rfl) ⟨549443, by rfl⟩ : syracuseStep 2930365 = 1098887) B1098887
theorem B2438855 : Blo 1080619 2438855 := bstep (se 1 (by rfl) ⟨1829141, by rfl⟩ : syracuseStep 2438855 = 3658283) B3658283
theorem B3651371 : Blo 1080619 3651371 := bstep (se 1 (by rfl) ⟨2738528, by rfl⟩ : syracuseStep 3651371 = 5477057) B5477057
theorem B2307935 : Blo 1080619 2307935 := bstep (se 1 (by rfl) ⟨1730951, by rfl⟩ : syracuseStep 2307935 = 3461903) B3461903
theorem B2602847 : Blo 1080619 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B3651641 : Blo 1080619 3651641 := bstep (se 2 (by rfl) ⟨1369365, by rfl⟩ : syracuseStep 3651641 = 2738731) B2738731
theorem B1947977 : Blo 1080619 1947977 := bstep (se 2 (by rfl) ⟨730491, by rfl⟩ : syracuseStep 1947977 = 1460983) B1460983
theorem B3520855 : Blo 1080619 3520855 := bstep (se 1 (by rfl) ⟨2640641, by rfl⟩ : syracuseStep 3520855 = 5281283) B5281283
theorem B10008937 : Blo 1080619 10008937 := bstep (se 2 (by rfl) ⟨3753351, by rfl⟩ : syracuseStep 10008937 = 7506703) B7506703
theorem B3651965 : Blo 1080619 3651965 := bstep (se 3 (by rfl) ⟨684743, by rfl⟩ : syracuseStep 3651965 = 1369487) B1369487
theorem B1849775 : Blo 1080619 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B2439719 : Blo 1080619 2439719 := bstep (se 1 (by rfl) ⟨1829789, by rfl⟩ : syracuseStep 2439719 = 3659579) B3659579
theorem B4110983 : Blo 1080619 4110983 := bstep (se 1 (by rfl) ⟨3083237, by rfl⟩ : syracuseStep 4110983 = 6166475) B6166475
theorem B3652235 : Blo 1080619 3652235 := bstep (se 1 (by rfl) ⟨2739176, by rfl⟩ : syracuseStep 3652235 = 5478353) B5478353
theorem B2440043 : Blo 1080619 2440043 := bstep (se 1 (by rfl) ⟨1830032, by rfl⟩ : syracuseStep 2440043 = 3660065) B3660065
theorem B2440097 : Blo 1080619 2440097 := bstep (se 2 (by rfl) ⟨915036, by rfl⟩ : syracuseStep 2440097 = 1830073) B1830073
theorem B1621001 : Blo 1080619 1621001 := bstep (se 2 (by rfl) ⟨607875, by rfl⟩ : syracuseStep 1621001 = 1215751) B1215751
theorem B1621031 : Blo 1080619 1621031 := bstep (se 1 (by rfl) ⟨1215773, by rfl⟩ : syracuseStep 1621031 = 2431547) B2431547
theorem B7027831 : Blo 1080619 7027831 := bstep (se 1 (by rfl) ⟨5270873, by rfl⟩ : syracuseStep 7027831 = 10541747) B10541747
theorem B1621115 : Blo 1080619 1621115 := bstep (se 1 (by rfl) ⟨1215836, by rfl⟩ : syracuseStep 1621115 = 2431673) B2431673
theorem B2964637 : Blo 1080619 2964637 := bstep (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) B1111739
theorem B1621241 : Blo 1080619 1621241 := bstep (se 2 (by rfl) ⟨607965, by rfl⟩ : syracuseStep 1621241 = 1215931) B1215931
theorem B1621343 : Blo 1080619 1621343 := bstep (se 1 (by rfl) ⟨1216007, by rfl⟩ : syracuseStep 1621343 = 2432015) B2432015
theorem B1621355 : Blo 1080619 1621355 := bstep (se 1 (by rfl) ⟨1216016, by rfl⟩ : syracuseStep 1621355 = 2432033) B2432033
theorem B5488073 : Blo 1080619 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B2735603 : Blo 1080619 2735603 := bstep (se 1 (by rfl) ⟨2051702, by rfl⟩ : syracuseStep 2735603 = 4103405) B4103405
theorem B3653153 : Blo 1080619 3653153 := bstep (se 2 (by rfl) ⟨1369932, by rfl⟩ : syracuseStep 3653153 = 2739865) B2739865
theorem B1621583 : Blo 1080619 1621583 := bstep (se 1 (by rfl) ⟨1216187, by rfl⟩ : syracuseStep 1621583 = 2432375) B2432375
theorem B2604683 : Blo 1080619 2604683 := bstep (se 1 (by rfl) ⟨1953512, by rfl⟩ : syracuseStep 2604683 = 3907025) B3907025
theorem B2735815 : Blo 1080619 2735815 := bstep (se 1 (by rfl) ⟨2051861, by rfl⟩ : syracuseStep 2735815 = 4103723) B4103723
theorem B1621703 : Blo 1080619 1621703 := bstep (se 1 (by rfl) ⟨1216277, by rfl⟩ : syracuseStep 1621703 = 2432555) B2432555
theorem B3653369 : Blo 1080619 3653369 := bstep (se 2 (by rfl) ⟨1370013, by rfl⟩ : syracuseStep 3653369 = 2740027) B2740027
theorem B9879329 : Blo 1080619 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B7814971 : Blo 1080619 7814971 := bstep (se 1 (by rfl) ⟨5861228, by rfl⟩ : syracuseStep 7814971 = 11722457) B11722457
theorem B1621865 : Blo 1080619 1621865 := bstep (se 2 (by rfl) ⟨608199, by rfl⟩ : syracuseStep 1621865 = 1216399) B1216399
theorem B1621943 : Blo 1080619 1621943 := bstep (se 1 (by rfl) ⟨1216457, by rfl⟩ : syracuseStep 1621943 = 2432915) B2432915
theorem B1949627 : Blo 1080619 1949627 := bstep (se 1 (by rfl) ⟨1462220, by rfl⟩ : syracuseStep 1949627 = 2924441) B2924441
theorem B1621979 : Blo 1080619 1621979 := bstep (se 1 (by rfl) ⟨1216484, by rfl⟩ : syracuseStep 1621979 = 2432969) B2432969
theorem B3653639 : Blo 1080619 3653639 := bstep (se 1 (by rfl) ⟨2740229, by rfl⟩ : syracuseStep 3653639 = 5480459) B5480459
theorem B4112441 : Blo 1080619 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B5488721 : Blo 1080619 5488721 := bstep (se 2 (by rfl) ⟨2058270, by rfl⟩ : syracuseStep 5488721 = 4116541) B4116541
theorem B6930521 : Blo 1080619 6930521 := bstep (se 2 (by rfl) ⟨2598945, by rfl⟩ : syracuseStep 6930521 = 5197891) B5197891
theorem B3653747 : Blo 1080619 3653747 := bstep (se 1 (by rfl) ⟨2740310, by rfl⟩ : syracuseStep 3653747 = 5480621) B5480621
theorem B3654017 : Blo 1080619 3654017 := bstep (se 2 (by rfl) ⟨1370256, by rfl⟩ : syracuseStep 3654017 = 2740513) B2740513
theorem B1622447 : Blo 1080619 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B1622537 : Blo 1080619 1622537 := bstep (se 2 (by rfl) ⟨608451, by rfl⟩ : syracuseStep 1622537 = 1216903) B1216903
theorem B1622567 : Blo 1080619 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B2736737 : Blo 1080619 2736737 := bstep (se 2 (by rfl) ⟨1026276, by rfl⟩ : syracuseStep 2736737 = 2052553) B2052553
theorem B1622651 : Blo 1080619 1622651 := bstep (se 1 (by rfl) ⟨1216988, by rfl⟩ : syracuseStep 1622651 = 2433977) B2433977
theorem B1622777 : Blo 1080619 1622777 := bstep (se 2 (by rfl) ⟨608541, by rfl⟩ : syracuseStep 1622777 = 1217083) B1217083
theorem B1622879 : Blo 1080619 1622879 := bstep (se 1 (by rfl) ⟨1217159, by rfl⟩ : syracuseStep 1622879 = 2434319) B2434319
theorem B1622891 : Blo 1080619 1622891 := bstep (se 1 (by rfl) ⟨1217168, by rfl⟩ : syracuseStep 1622891 = 2434337) B2434337
theorem B2605999 : Blo 1080619 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B1623119 : Blo 1080619 1623119 := bstep (se 1 (by rfl) ⟨1217339, by rfl⟩ : syracuseStep 1623119 = 2434679) B2434679
theorem B3654827 : Blo 1080619 3654827 := bstep (se 1 (by rfl) ⟨2741120, by rfl⟩ : syracuseStep 3654827 = 5482241) B5482241
theorem B1623239 : Blo 1080619 1623239 := bstep (se 1 (by rfl) ⟨1217429, by rfl⟩ : syracuseStep 1623239 = 2434859) B2434859
theorem B1623401 : Blo 1080619 1623401 := bstep (se 2 (by rfl) ⟨608775, by rfl⟩ : syracuseStep 1623401 = 1217551) B1217551
theorem B1623479 : Blo 1080619 1623479 := bstep (se 1 (by rfl) ⟨1217609, by rfl⟩ : syracuseStep 1623479 = 2435219) B2435219
theorem B1623515 : Blo 1080619 1623515 := bstep (se 1 (by rfl) ⟨1217636, by rfl⟩ : syracuseStep 1623515 = 2435273) B2435273
theorem B4113929 : Blo 1080619 4113929 := bstep (se 2 (by rfl) ⟨1542723, by rfl⟩ : syracuseStep 4113929 = 3085447) B3085447
theorem B3655367 : Blo 1080619 3655367 := bstep (se 1 (by rfl) ⟨2741525, by rfl⟩ : syracuseStep 3655367 = 5483051) B5483051
theorem B12339053 : Blo 1080619 12339053 := bstep (se 3 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 12339053 = 4627145) B4627145
theorem B4999031 : Blo 1080619 4999031 := bstep (se 1 (by rfl) ⟨3749273, by rfl⟩ : syracuseStep 4999031 = 7498547) B7498547
theorem B1623983 : Blo 1080619 1623983 := bstep (se 1 (by rfl) ⟨1217987, by rfl⟩ : syracuseStep 1623983 = 2435975) B2435975
theorem B1624073 : Blo 1080619 1624073 := bstep (se 2 (by rfl) ⟨609027, by rfl⟩ : syracuseStep 1624073 = 1218055) B1218055
theorem B2738195 : Blo 1080619 2738195 := bstep (se 1 (by rfl) ⟨2053646, by rfl⟩ : syracuseStep 2738195 = 4107293) B4107293
theorem B1624103 : Blo 1080619 1624103 := bstep (se 1 (by rfl) ⟨1218077, by rfl⟩ : syracuseStep 1624103 = 2436155) B2436155
theorem B5851217 : Blo 1080619 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B1624187 : Blo 1080619 1624187 := bstep (se 1 (by rfl) ⟨1218140, by rfl⟩ : syracuseStep 1624187 = 2436281) B2436281
theorem B1624313 : Blo 1080619 1624313 := bstep (se 2 (by rfl) ⟨609117, by rfl⟩ : syracuseStep 1624313 = 1218235) B1218235
theorem B1624415 : Blo 1080619 1624415 := bstep (se 1 (by rfl) ⟨1218311, by rfl⟩ : syracuseStep 1624415 = 2436623) B2436623
theorem B1624427 : Blo 1080619 1624427 := bstep (se 1 (by rfl) ⟨1218320, by rfl⟩ : syracuseStep 1624427 = 2436641) B2436641
theorem B8210969 : Blo 1080619 8210969 := bstep (se 2 (by rfl) ⟨3079113, by rfl⟩ : syracuseStep 8210969 = 6158227) B6158227
theorem B3656231 : Blo 1080619 3656231 := bstep (se 1 (by rfl) ⟨2742173, by rfl⟩ : syracuseStep 3656231 = 5484347) B5484347
theorem B1624655 : Blo 1080619 1624655 := bstep (se 1 (by rfl) ⟨1218491, by rfl⟩ : syracuseStep 1624655 = 2436983) B2436983
theorem B4115083 : Blo 1080619 4115083 := bstep (se 1 (by rfl) ⟨3086312, by rfl⟩ : syracuseStep 4115083 = 6172625) B6172625
theorem B3295883 : Blo 1080619 3295883 := bstep (se 1 (by rfl) ⟨2471912, by rfl⟩ : syracuseStep 3295883 = 4943825) B4943825
theorem B3656339 : Blo 1080619 3656339 := bstep (se 1 (by rfl) ⟨2742254, by rfl⟩ : syracuseStep 3656339 = 5484509) B5484509
theorem B1624775 : Blo 1080619 1624775 := bstep (se 1 (by rfl) ⟨1218581, by rfl⟩ : syracuseStep 1624775 = 2437163) B2437163
theorem B1624937 : Blo 1080619 1624937 := bstep (se 2 (by rfl) ⟨609351, by rfl⟩ : syracuseStep 1624937 = 1218703) B1218703
theorem B3656555 : Blo 1080619 3656555 := bstep (se 1 (by rfl) ⟨2742416, by rfl⟩ : syracuseStep 3656555 = 5484833) B5484833
theorem B3656609 : Blo 1080619 3656609 := bstep (se 2 (by rfl) ⟨1371228, by rfl⟩ : syracuseStep 3656609 = 2742457) B2742457
theorem B1952695 : Blo 1080619 1952695 := bstep (se 1 (by rfl) ⟨1464521, by rfl⟩ : syracuseStep 1952695 = 2929043) B2929043
theorem B1625015 : Blo 1080619 1625015 := bstep (se 1 (by rfl) ⟨1218761, by rfl⟩ : syracuseStep 1625015 = 2437523) B2437523
theorem B4115387 : Blo 1080619 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B1625051 : Blo 1080619 1625051 := bstep (se 1 (by rfl) ⟨1218788, by rfl⟩ : syracuseStep 1625051 = 2437577) B2437577
theorem B5491763 : Blo 1080619 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B1625519 : Blo 1080619 1625519 := bstep (se 1 (by rfl) ⟨1219139, by rfl⟩ : syracuseStep 1625519 = 2438279) B2438279
theorem B3657203 : Blo 1080619 3657203 := bstep (se 1 (by rfl) ⟨2742902, by rfl⟩ : syracuseStep 3657203 = 5485805) B5485805
theorem B1625609 : Blo 1080619 1625609 := bstep (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) B1219207
theorem B1625639 : Blo 1080619 1625639 := bstep (se 1 (by rfl) ⟨1219229, by rfl⟩ : syracuseStep 1625639 = 2438459) B2438459
theorem B37506683 : Blo 1080619 37506683 := bstep (se 1 (by rfl) ⟨28130012, by rfl⟩ : syracuseStep 37506683 = 56260025) B56260025
theorem B1625723 : Blo 1080619 1625723 := bstep (se 1 (by rfl) ⟨1219292, by rfl⟩ : syracuseStep 1625723 = 2438585) B2438585
theorem B2051831 : Blo 1080619 2051831 := bstep (se 1 (by rfl) ⟨1538873, by rfl⟩ : syracuseStep 2051831 = 3077747) B3077747
theorem B1625849 : Blo 1080619 1625849 := bstep (se 2 (by rfl) ⟨609693, by rfl⟩ : syracuseStep 1625849 = 1219387) B1219387
theorem B1625951 : Blo 1080619 1625951 := bstep (se 1 (by rfl) ⟨1219463, by rfl⟩ : syracuseStep 1625951 = 2438927) B2438927
theorem B1625963 : Blo 1080619 1625963 := bstep (se 1 (by rfl) ⟨1219472, by rfl⟩ : syracuseStep 1625963 = 2438945) B2438945
theorem B2051983 : Blo 1080619 2051983 := bstep (se 1 (by rfl) ⟨1538987, by rfl⟩ : syracuseStep 2051983 = 3077975) B3077975
theorem B1232815 : Blo 1080619 1232815 := bstep (se 1 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 1232815 = 1849223) B1849223
theorem B3297199 : Blo 1080619 3297199 := bstep (se 1 (by rfl) ⟨2472899, by rfl⟩ : syracuseStep 3297199 = 4945799) B4945799
theorem B3657743 : Blo 1080619 3657743 := bstep (se 1 (by rfl) ⟨2743307, by rfl⟩ : syracuseStep 3657743 = 5486615) B5486615
theorem B1626191 : Blo 1080619 1626191 := bstep (se 1 (by rfl) ⟨1219643, by rfl⟩ : syracuseStep 1626191 = 2439287) B2439287
theorem B1626311 : Blo 1080619 1626311 := bstep (se 1 (by rfl) ⟨1219733, by rfl⟩ : syracuseStep 1626311 = 2439467) B2439467
theorem B1626473 : Blo 1080619 1626473 := bstep (se 2 (by rfl) ⟨609927, by rfl⟩ : syracuseStep 1626473 = 1219855) B1219855
theorem B1626551 : Blo 1080619 1626551 := bstep (se 1 (by rfl) ⟨1219913, by rfl⟩ : syracuseStep 1626551 = 2439827) B2439827
theorem B1626587 : Blo 1080619 1626587 := bstep (se 1 (by rfl) ⟨1219940, by rfl⟩ : syracuseStep 1626587 = 2439881) B2439881
theorem B3658337 : Blo 1080619 3658337 := bstep (se 2 (by rfl) ⟨1371876, by rfl⟩ : syracuseStep 3658337 = 2743753) B2743753
theorem B11686517 : Blo 1080619 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B12341969 : Blo 1080619 12341969 := bstep (se 2 (by rfl) ⟨4628238, by rfl⟩ : syracuseStep 12341969 = 9256477) B9256477
theorem B2052857 : Blo 1080619 2052857 := bstep (se 2 (by rfl) ⟨769821, by rfl⟩ : syracuseStep 2052857 = 1539643) B1539643
theorem B1823593 : Blo 1080619 1823593 := bstep (se 2 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 1823593 = 1367695) B1367695
theorem B13849451 : Blo 1080619 13849451 := bstep (se 1 (by rfl) ⟨10387088, by rfl⟩ : syracuseStep 13849451 = 20774177) B20774177
theorem B2053039 : Blo 1080619 2053039 := bstep (se 1 (by rfl) ⟨1539779, by rfl⟩ : syracuseStep 2053039 = 3079559) B3079559
theorem B10408925 : Blo 1080619 10408925 := bstep (se 3 (by rfl) ⟨1951673, by rfl⟩ : syracuseStep 10408925 = 3903347) B3903347
theorem B1299655 : Blo 1080619 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B8213885 : Blo 1080619 8213885 := bstep (se 3 (by rfl) ⟨1540103, by rfl⟩ : syracuseStep 8213885 = 3080207) B3080207
theorem B2741647 : Blo 1080619 2741647 := bstep (se 1 (by rfl) ⟨2056235, by rfl⟩ : syracuseStep 2741647 = 4112471) B4112471
theorem B1824187 : Blo 1080619 1824187 := bstep (se 1 (by rfl) ⟨1368140, by rfl⟩ : syracuseStep 1824187 = 2736281) B2736281
theorem B1824295 : Blo 1080619 1824295 := bstep (se 1 (by rfl) ⟨1368221, by rfl⟩ : syracuseStep 1824295 = 2736443) B2736443
theorem B28169927 : Blo 1080619 28169927 := bstep (se 1 (by rfl) ⟨21127445, by rfl⟩ : syracuseStep 28169927 = 42254891) B42254891
theorem B4216531 : Blo 1080619 4216531 := bstep (se 1 (by rfl) ⟨3162398, by rfl⟩ : syracuseStep 4216531 = 6324797) B6324797
theorem B2741971 : Blo 1080619 2741971 := bstep (se 1 (by rfl) ⟨2056478, by rfl⟩ : syracuseStep 2741971 = 4112957) B4112957
theorem B11130583 : Blo 1080619 11130583 := bstep (se 1 (by rfl) ⟨8347937, by rfl⟩ : syracuseStep 11130583 = 16695875) B16695875
theorem B1824619 : Blo 1080619 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B3463183 : Blo 1080619 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B3659795 : Blo 1080619 3659795 := bstep (se 1 (by rfl) ⟨2744846, by rfl⟩ : syracuseStep 3659795 = 5489693) B5489693
theorem B2316367 : Blo 1080619 2316367 := bstep (se 1 (by rfl) ⟨1737275, by rfl⟩ : syracuseStep 2316367 = 3474551) B3474551
theorem B2054315 : Blo 1080619 2054315 := bstep (se 1 (by rfl) ⟨1540736, by rfl⟩ : syracuseStep 2054315 = 3081473) B3081473
theorem B4217027 : Blo 1080619 4217027 := bstep (se 1 (by rfl) ⟨3162770, by rfl⟩ : syracuseStep 4217027 = 6325541) B6325541
theorem B5200139 : Blo 1080619 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B3660119 : Blo 1080619 3660119 := bstep (se 1 (by rfl) ⟨2745089, by rfl⟩ : syracuseStep 3660119 = 5490179) B5490179
theorem B35117549 : Blo 1080619 35117549 := bstep (se 3 (by rfl) ⟨6584540, by rfl⟩ : syracuseStep 35117549 = 13169081) B13169081
theorem B133487189 : Blo 1080619 133487189 := bstep (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) B1564303
theorem B2742923 : Blo 1080619 2742923 := bstep (se 1 (by rfl) ⟨2057192, by rfl⟩ : syracuseStep 2742923 = 4114385) B4114385
theorem B1825679 : Blo 1080619 1825679 := bstep (se 1 (by rfl) ⟨1369259, by rfl⟩ : syracuseStep 1825679 = 2738519) B2738519
theorem B6937643 : Blo 1080619 6937643 := bstep (se 1 (by rfl) ⟨5203232, by rfl⟩ : syracuseStep 6937643 = 10406465) B10406465
theorem B1825915 : Blo 1080619 1825915 := bstep (se 1 (by rfl) ⟨1369436, by rfl⟩ : syracuseStep 1825915 = 2738873) B2738873
theorem B3464363 : Blo 1080619 3464363 := bstep (se 1 (by rfl) ⟨2598272, by rfl⟩ : syracuseStep 3464363 = 5196545) B5196545
theorem B2055689 : Blo 1080619 2055689 := bstep (se 2 (by rfl) ⟨770883, by rfl⟩ : syracuseStep 2055689 = 1541767) B1541767
theorem B2055719 : Blo 1080619 2055719 := bstep (se 1 (by rfl) ⟨1541789, by rfl⟩ : syracuseStep 2055719 = 3083579) B3083579
theorem B5856907 : Blo 1080619 5856907 := bstep (se 1 (by rfl) ⟨4392680, by rfl⟩ : syracuseStep 5856907 = 8785361) B8785361
theorem B2744057 : Blo 1080619 2744057 := bstep (se 2 (by rfl) ⟨1029021, by rfl⟩ : syracuseStep 2744057 = 2058043) B2058043
theorem B2744239 : Blo 1080619 2744239 := bstep (se 1 (by rfl) ⟨2058179, by rfl⟩ : syracuseStep 2744239 = 4116359) B4116359
theorem B1826779 : Blo 1080619 1826779 := bstep (se 1 (by rfl) ⟨1370084, by rfl⟩ : syracuseStep 1826779 = 2740169) B2740169
theorem B2056403 : Blo 1080619 2056403 := bstep (se 1 (by rfl) ⟨1542302, by rfl⟩ : syracuseStep 2056403 = 3084605) B3084605
theorem B2056441 : Blo 1080619 2056441 := bstep (se 2 (by rfl) ⟨771165, by rfl⟩ : syracuseStep 2056441 = 1542331) B1542331
theorem B2744705 : Blo 1080619 2744705 := bstep (se 2 (by rfl) ⟨1029264, by rfl⟩ : syracuseStep 2744705 = 2058529) B2058529
theorem B1827407 : Blo 1080619 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B2777723 : Blo 1080619 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B2745161 : Blo 1080619 2745161 := bstep (se 2 (by rfl) ⟨1029435, by rfl⟩ : syracuseStep 2745161 = 2058871) B2058871
theorem B3466145 : Blo 1080619 3466145 := bstep (se 2 (by rfl) ⟨1299804, by rfl⟩ : syracuseStep 3466145 = 2599609) B2599609
theorem B2057147 : Blo 1080619 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B27452363 : Blo 1080619 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B7398553 : Blo 1080619 7398553 := bstep (se 2 (by rfl) ⟨2774457, by rfl⟩ : syracuseStep 7398553 = 5548915) B5548915
theorem B3007849 : Blo 1080619 3007849 := bstep (se 2 (by rfl) ⟨1127943, by rfl⟩ : syracuseStep 3007849 = 2255887) B2255887
theorem B2057633 : Blo 1080619 2057633 := bstep (se 2 (by rfl) ⟨771612, by rfl⟩ : syracuseStep 2057633 = 1543225) B1543225
theorem B1828271 : Blo 1080619 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B1369639 : Blo 1080619 1369639 := bstep (se 1 (by rfl) ⟨1027229, by rfl⟩ : syracuseStep 1369639 = 2054459) B2054459
theorem B8218259 : Blo 1080619 8218259 := bstep (se 1 (by rfl) ⟨6163694, by rfl⟩ : syracuseStep 8218259 = 12327389) B12327389
theorem B2057899 : Blo 1080619 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B4384505 : Blo 1080619 4384505 := bstep (se 2 (by rfl) ⟨1644189, by rfl⟩ : syracuseStep 4384505 = 3288379) B3288379
theorem B1828703 : Blo 1080619 1828703 := bstep (se 1 (by rfl) ⟨1371527, by rfl⟩ : syracuseStep 1828703 = 2743055) B2743055
theorem B1369963 : Blo 1080619 1369963 := bstep (se 1 (by rfl) ⟨1027472, by rfl⟩ : syracuseStep 1369963 = 2054945) B2054945
theorem B168814529 : Blo 1080619 168814529 := bstep (se 2 (by rfl) ⟨63305448, by rfl⟩ : syracuseStep 168814529 = 126610897) B126610897
theorem B11724749 : Blo 1080619 11724749 := bstep (se 3 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 11724749 = 4396781) B4396781
theorem B2058203 : Blo 1080619 2058203 := bstep (se 1 (by rfl) ⟨1543652, by rfl⟩ : syracuseStep 2058203 = 3087305) B3087305
theorem B1370191 : Blo 1080619 1370191 := bstep (se 1 (by rfl) ⟨1027643, by rfl⟩ : syracuseStep 1370191 = 2055287) B2055287
theorem B14051717 : Blo 1080619 14051717 := bstep (se 4 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 14051717 = 2634697) B2634697
theorem B1829263 : Blo 1080619 1829263 := bstep (se 1 (by rfl) ⟨1371947, by rfl⟩ : syracuseStep 1829263 = 2743895) B2743895
theorem B12347801 : Blo 1080619 12347801 := bstep (se 2 (by rfl) ⟨4630425, by rfl⟩ : syracuseStep 12347801 = 9260851) B9260851
theorem B1731079 : Blo 1080619 1731079 := bstep (se 1 (by rfl) ⟨1298309, by rfl⟩ : syracuseStep 1731079 = 2596619) B2596619
theorem B3467785 : Blo 1080619 3467785 := bstep (se 2 (by rfl) ⟨1300419, by rfl⟩ : syracuseStep 3467785 = 2600839) B2600839
theorem B6154811 : Blo 1080619 6154811 := bstep (se 1 (by rfl) ⟨4616108, by rfl⟩ : syracuseStep 6154811 = 9232217) B9232217
theorem B3697249 : Blo 1080619 3697249 := bstep (se 2 (by rfl) ⟨1386468, by rfl⟩ : syracuseStep 3697249 = 2772937) B2772937
theorem B1829945 : Blo 1080619 1829945 := bstep (se 2 (by rfl) ⟨686229, by rfl⟩ : syracuseStep 1829945 = 1372459) B1372459
theorem B1371259 : Blo 1080619 1371259 := bstep (se 1 (by rfl) ⟨1028444, by rfl⟩ : syracuseStep 1371259 = 2056889) B2056889
theorem B1371487 : Blo 1080619 1371487 := bstep (se 1 (by rfl) ⟨1028615, by rfl⟩ : syracuseStep 1371487 = 2057231) B2057231
theorem B4386401 : Blo 1080619 4386401 := bstep (se 2 (by rfl) ⟨1644900, by rfl⟩ : syracuseStep 4386401 = 3289801) B3289801
theorem B9891517 : Blo 1080619 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B1372079 : Blo 1080619 1372079 := bstep (se 1 (by rfl) ⟨1029059, by rfl⟩ : syracuseStep 1372079 = 2058119) B2058119
theorem B2191369 : Blo 1080619 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B4452889 : Blo 1080619 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B1733483 : Blo 1080619 1733483 := bstep (se 1 (by rfl) ⟨1300112, by rfl⟩ : syracuseStep 1733483 = 2600225) B2600225
theorem B10548143 : Blo 1080619 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B8221661 : Blo 1080619 8221661 := bstep (se 3 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 8221661 = 3083123) B3083123
theorem B3470489 : Blo 1080619 3470489 := bstep (se 2 (by rfl) ⟨1301433, by rfl⟩ : syracuseStep 3470489 = 2602867) B2602867
theorem B3077291 : Blo 1080619 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B14841103 : Blo 1080619 14841103 := bstep (se 1 (by rfl) ⟨11130827, by rfl⟩ : syracuseStep 14841103 = 22261655) B22261655
theorem B73037155 : Blo 1080619 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B30078307 : Blo 1080619 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B1733995 : Blo 1080619 1733995 := bstep (se 1 (by rfl) ⟨1300496, by rfl⟩ : syracuseStep 1733995 = 2600993) B2600993
theorem B3700097 : Blo 1080619 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B6158045 : Blo 1080619 6158045 := bstep (se 3 (by rfl) ⟨1154633, by rfl⟩ : syracuseStep 6158045 = 2309267) B2309267
theorem B1734713 : Blo 1080619 1734713 := bstep (se 2 (by rfl) ⟨650517, by rfl⟩ : syracuseStep 1734713 = 1301035) B1301035
theorem B3897497 : Blo 1080619 3897497 := bstep (se 2 (by rfl) ⟨1461561, by rfl⟩ : syracuseStep 3897497 = 2923123) B2923123
theorem B4618397 : Blo 1080619 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B3897611 : Blo 1080619 3897611 := bstep (se 1 (by rfl) ⟨2923208, by rfl⟩ : syracuseStep 3897611 = 5846417) B5846417
theorem B6584813 : Blo 1080619 6584813 := bstep (se 3 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 6584813 = 2469305) B2469305
theorem B27753029 : Blo 1080619 27753029 := bstep (se 4 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 27753029 = 5203693) B5203693
theorem B8321737 : Blo 1080619 8321737 := bstep (se 2 (by rfl) ⟨3120651, by rfl⟩ : syracuseStep 8321737 = 6241303) B6241303
theorem B15596317 : Blo 1080619 15596317 := bstep (se 3 (by rfl) ⟨2924309, by rfl⟩ : syracuseStep 15596317 = 5848619) B5848619
theorem B4619081 : Blo 1080619 4619081 := bstep (se 2 (by rfl) ⟨1732155, by rfl⟩ : syracuseStep 4619081 = 3464311) B3464311
theorem B8781047 : Blo 1080619 8781047 := bstep (se 1 (by rfl) ⟨6585785, by rfl⟩ : syracuseStep 8781047 = 13171571) B13171571
theorem B1080655 : Blo 1080619 1080655 := bstep (se 1 (by rfl) ⟨810491, by rfl⟩ : syracuseStep 1080655 = 1620983) B1620983
theorem B1080671 : Blo 1080619 1080671 := bstep (se 1 (by rfl) ⟨810503, by rfl⟩ : syracuseStep 1080671 = 1621007) B1621007
theorem B1080699 : Blo 1080619 1080699 := bstep (se 1 (by rfl) ⟨810524, by rfl⟩ : syracuseStep 1080699 = 1621049) B1621049
theorem B3472769 : Blo 1080619 3472769 := bstep (se 2 (by rfl) ⟨1302288, by rfl⟩ : syracuseStep 3472769 = 2604577) B2604577
theorem B4619663 : Blo 1080619 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B1080751 : Blo 1080619 1080751 := bstep (se 1 (by rfl) ⟨810563, by rfl⟩ : syracuseStep 1080751 = 1621127) B1621127
theorem B1080775 : Blo 1080619 1080775 := bstep (se 1 (by rfl) ⟨810581, by rfl⟩ : syracuseStep 1080775 = 1621163) B1621163
theorem B1080795 : Blo 1080619 1080795 := bstep (se 1 (by rfl) ⟨810596, by rfl⟩ : syracuseStep 1080795 = 1621193) B1621193
theorem B1080871 : Blo 1080619 1080871 := bstep (se 1 (by rfl) ⟨810653, by rfl⟩ : syracuseStep 1080871 = 1621307) B1621307
theorem B1080911 : Blo 1080619 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B1080927 : Blo 1080619 1080927 := bstep (se 1 (by rfl) ⟨810695, by rfl⟩ : syracuseStep 1080927 = 1621391) B1621391
theorem B1080955 : Blo 1080619 1080955 := bstep (se 1 (by rfl) ⟨810716, by rfl⟩ : syracuseStep 1080955 = 1621433) B1621433
theorem B1081007 : Blo 1080619 1081007 := bstep (se 1 (by rfl) ⟨810755, by rfl⟩ : syracuseStep 1081007 = 1621511) B1621511
theorem B1081031 : Blo 1080619 1081031 := bstep (se 1 (by rfl) ⟨810773, by rfl⟩ : syracuseStep 1081031 = 1621547) B1621547
theorem B1081051 : Blo 1080619 1081051 := bstep (se 1 (by rfl) ⟨810788, by rfl⟩ : syracuseStep 1081051 = 1621577) B1621577
theorem B1081127 : Blo 1080619 1081127 := bstep (se 1 (by rfl) ⟨810845, by rfl⟩ : syracuseStep 1081127 = 1621691) B1621691
theorem B1081167 : Blo 1080619 1081167 := bstep (se 1 (by rfl) ⟨810875, by rfl⟩ : syracuseStep 1081167 = 1621751) B1621751
theorem B1081183 : Blo 1080619 1081183 := bstep (se 1 (by rfl) ⟨810887, by rfl⟩ : syracuseStep 1081183 = 1621775) B1621775
theorem B1081211 : Blo 1080619 1081211 := bstep (se 1 (by rfl) ⟨810908, by rfl⟩ : syracuseStep 1081211 = 1621817) B1621817
theorem B1081263 : Blo 1080619 1081263 := bstep (se 1 (by rfl) ⟨810947, by rfl⟩ : syracuseStep 1081263 = 1621895) B1621895
theorem B1081287 : Blo 1080619 1081287 := bstep (se 1 (by rfl) ⟨810965, by rfl⟩ : syracuseStep 1081287 = 1621931) B1621931
theorem B1081307 : Blo 1080619 1081307 := bstep (se 1 (by rfl) ⟨810980, by rfl⟩ : syracuseStep 1081307 = 1621961) B1621961
theorem B4620347 : Blo 1080619 4620347 := bstep (se 1 (by rfl) ⟨3465260, by rfl⟩ : syracuseStep 4620347 = 6930521) B6930521
theorem B1081631 : Blo 1080619 1081631 := bstep (se 1 (by rfl) ⟨811223, by rfl⟩ : syracuseStep 1081631 = 1622447) B1622447
theorem B1081691 : Blo 1080619 1081691 := bstep (se 1 (by rfl) ⟨811268, by rfl⟩ : syracuseStep 1081691 = 1622537) B1622537
theorem B1081711 : Blo 1080619 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B1081767 : Blo 1080619 1081767 := bstep (se 1 (by rfl) ⟨811325, by rfl⟩ : syracuseStep 1081767 = 1622651) B1622651
theorem B1081851 : Blo 1080619 1081851 := bstep (se 1 (by rfl) ⟨811388, by rfl⟩ : syracuseStep 1081851 = 1622777) B1622777
theorem B1081919 : Blo 1080619 1081919 := bstep (se 1 (by rfl) ⟨811439, by rfl⟩ : syracuseStep 1081919 = 1622879) B1622879
theorem B1081927 : Blo 1080619 1081927 := bstep (se 1 (by rfl) ⟨811445, by rfl⟩ : syracuseStep 1081927 = 1622891) B1622891
theorem B10420919 : Blo 1080619 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B1082079 : Blo 1080619 1082079 := bstep (se 1 (by rfl) ⟨811559, by rfl⟩ : syracuseStep 1082079 = 1623119) B1623119
theorem B1082159 : Blo 1080619 1082159 := bstep (se 1 (by rfl) ⟨811619, by rfl⟩ : syracuseStep 1082159 = 1623239) B1623239
theorem B1082267 : Blo 1080619 1082267 := bstep (se 1 (by rfl) ⟨811700, by rfl⟩ : syracuseStep 1082267 = 1623401) B1623401
theorem B1082319 : Blo 1080619 1082319 := bstep (se 1 (by rfl) ⟨811739, by rfl⟩ : syracuseStep 1082319 = 1623479) B1623479
theorem B1082343 : Blo 1080619 1082343 := bstep (se 1 (by rfl) ⟨811757, by rfl⟩ : syracuseStep 1082343 = 1623515) B1623515
theorem B3081415 : Blo 1080619 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B3474665 : Blo 1080619 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B8226035 : Blo 1080619 8226035 := bstep (se 1 (by rfl) ⟨6169526, by rfl⟩ : syracuseStep 8226035 = 12339053) B12339053
theorem B1082655 : Blo 1080619 1082655 := bstep (se 1 (by rfl) ⟨811991, by rfl⟩ : syracuseStep 1082655 = 1623983) B1623983
theorem B1082715 : Blo 1080619 1082715 := bstep (se 1 (by rfl) ⟨812036, by rfl⟩ : syracuseStep 1082715 = 1624073) B1624073
theorem B2196833 : Blo 1080619 2196833 := bstep (se 2 (by rfl) ⟨823812, by rfl⟩ : syracuseStep 2196833 = 1647625) B1647625
theorem B1082735 : Blo 1080619 1082735 := bstep (se 1 (by rfl) ⟨812051, by rfl⟩ : syracuseStep 1082735 = 1624103) B1624103
theorem B3900811 : Blo 1080619 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1082791 : Blo 1080619 1082791 := bstep (se 1 (by rfl) ⟨812093, by rfl⟩ : syracuseStep 1082791 = 1624187) B1624187
theorem B1082875 : Blo 1080619 1082875 := bstep (se 1 (by rfl) ⟨812156, by rfl⟩ : syracuseStep 1082875 = 1624313) B1624313
theorem B9864737 : Blo 1080619 9864737 := bstep (se 2 (by rfl) ⟨3699276, by rfl⟩ : syracuseStep 9864737 = 7398553) B7398553
theorem B1082943 : Blo 1080619 1082943 := bstep (se 1 (by rfl) ⟨812207, by rfl⟩ : syracuseStep 1082943 = 1624415) B1624415
theorem B1082951 : Blo 1080619 1082951 := bstep (se 1 (by rfl) ⟨812213, by rfl⟩ : syracuseStep 1082951 = 1624427) B1624427
theorem B5473979 : Blo 1080619 5473979 := bstep (se 1 (by rfl) ⟨4105484, by rfl⟩ : syracuseStep 5473979 = 8210969) B8210969
theorem B1083103 : Blo 1080619 1083103 := bstep (se 1 (by rfl) ⟨812327, by rfl⟩ : syracuseStep 1083103 = 1624655) B1624655
theorem B2197255 : Blo 1080619 2197255 := bstep (se 1 (by rfl) ⟨1647941, by rfl⟩ : syracuseStep 2197255 = 3295883) B3295883
theorem B1083183 : Blo 1080619 1083183 := bstep (se 1 (by rfl) ⟨812387, by rfl⟩ : syracuseStep 1083183 = 1624775) B1624775
theorem B1083291 : Blo 1080619 1083291 := bstep (se 1 (by rfl) ⟨812468, by rfl⟩ : syracuseStep 1083291 = 1624937) B1624937
theorem B1083343 : Blo 1080619 1083343 := bstep (se 1 (by rfl) ⟨812507, by rfl⟩ : syracuseStep 1083343 = 1625015) B1625015
theorem B1083367 : Blo 1080619 1083367 := bstep (se 1 (by rfl) ⟨812525, by rfl⟩ : syracuseStep 1083367 = 1625051) B1625051
theorem B23431153 : Blo 1080619 23431153 := bstep (se 2 (by rfl) ⟨8786682, by rfl⟩ : syracuseStep 23431153 = 17573365) B17573365
theorem B1083679 : Blo 1080619 1083679 := bstep (se 1 (by rfl) ⟨812759, by rfl⟩ : syracuseStep 1083679 = 1625519) B1625519
theorem B1083739 : Blo 1080619 1083739 := bstep (se 1 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 1083739 = 1625609) B1625609
theorem B1083759 : Blo 1080619 1083759 := bstep (se 1 (by rfl) ⟨812819, by rfl⟩ : syracuseStep 1083759 = 1625639) B1625639
theorem B1083815 : Blo 1080619 1083815 := bstep (se 1 (by rfl) ⟨812861, by rfl⟩ : syracuseStep 1083815 = 1625723) B1625723
theorem B1083899 : Blo 1080619 1083899 := bstep (se 1 (by rfl) ⟨812924, by rfl⟩ : syracuseStep 1083899 = 1625849) B1625849
theorem B73206301 : Blo 1080619 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B1083967 : Blo 1080619 1083967 := bstep (se 1 (by rfl) ⟨812975, by rfl⟩ : syracuseStep 1083967 = 1625951) B1625951
theorem B1083975 : Blo 1080619 1083975 := bstep (se 1 (by rfl) ⟨812981, by rfl⟩ : syracuseStep 1083975 = 1625963) B1625963
theorem B1084127 : Blo 1080619 1084127 := bstep (se 1 (by rfl) ⟨813095, by rfl⟩ : syracuseStep 1084127 = 1626191) B1626191
theorem B1084207 : Blo 1080619 1084207 := bstep (se 1 (by rfl) ⟨813155, by rfl⟩ : syracuseStep 1084207 = 1626311) B1626311
theorem B1084315 : Blo 1080619 1084315 := bstep (se 1 (by rfl) ⟨813236, by rfl⟩ : syracuseStep 1084315 = 1626473) B1626473
theorem B1084367 : Blo 1080619 1084367 := bstep (se 1 (by rfl) ⟨813275, by rfl⟩ : syracuseStep 1084367 = 1626551) B1626551
theorem B1084391 : Blo 1080619 1084391 := bstep (se 1 (by rfl) ⟨813293, by rfl⟩ : syracuseStep 1084391 = 1626587) B1626587
theorem B8227979 : Blo 1080619 8227979 := bstep (se 1 (by rfl) ⟨6170984, by rfl⟩ : syracuseStep 8227979 = 12341969) B12341969
theorem B4623713 : Blo 1080619 4623713 := bstep (se 2 (by rfl) ⟨1733892, by rfl⟩ : syracuseStep 4623713 = 3467785) B3467785
theorem B5475923 : Blo 1080619 5475923 := bstep (se 1 (by rfl) ⟨4106942, by rfl⟩ : syracuseStep 5475923 = 8213885) B8213885
theorem B18779951 : Blo 1080619 18779951 := bstep (se 1 (by rfl) ⟨14084963, by rfl⟩ : syracuseStep 18779951 = 28169927) B28169927
theorem B6164585 : Blo 1080619 6164585 := bstep (se 2 (by rfl) ⟨2311719, by rfl⟩ : syracuseStep 6164585 = 4623439) B4623439
theorem B8229437 : Blo 1080619 8229437 := bstep (se 3 (by rfl) ⟨1543019, by rfl⟩ : syracuseStep 8229437 = 3086039) B3086039
theorem B1217119 : Blo 1080619 1217119 := bstep (se 1 (by rfl) ⟨912839, by rfl⟩ : syracuseStep 1217119 = 1825679) B1825679
theorem B4625095 : Blo 1080619 4625095 := bstep (se 1 (by rfl) ⟨3468821, by rfl⟩ : syracuseStep 4625095 = 6937643) B6937643
theorem B12325931 : Blo 1080619 12325931 := bstep (se 1 (by rfl) ⟨9244448, by rfl⟩ : syracuseStep 12325931 = 18488897) B18488897
theorem B15602777 : Blo 1080619 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B1643753 : Blo 1080619 1643753 := bstep (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) B1232815
theorem B4396265 : Blo 1080619 4396265 := bstep (se 2 (by rfl) ⟨1648599, by rfl⟩ : syracuseStep 4396265 = 3297199) B3297199
theorem B20780327 : Blo 1080619 20780327 := bstep (se 1 (by rfl) ⟨15585245, by rfl⟩ : syracuseStep 20780327 = 31170491) B31170491
theorem B3085607 : Blo 1080619 3085607 := bstep (se 1 (by rfl) ⟨2314205, by rfl⟩ : syracuseStep 3085607 = 4628411) B4628411
theorem B2921825 : Blo 1080619 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B1218271 : Blo 1080619 1218271 := bstep (se 1 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 1218271 = 1827407) B1827407
theorem B11245405 : Blo 1080619 11245405 := bstep (se 3 (by rfl) ⟨2108513, by rfl⟩ : syracuseStep 11245405 = 4217027) B4217027
theorem B13867037 : Blo 1080619 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B5937185 : Blo 1080619 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B1218847 : Blo 1080619 1218847 := bstep (se 1 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 1218847 = 1828271) B1828271
theorem B5478839 : Blo 1080619 5478839 := bstep (se 1 (by rfl) ⟨4109129, by rfl⟩ : syracuseStep 5478839 = 8218259) B8218259
theorem B2431457 : Blo 1080619 2431457 := bstep (se 2 (by rfl) ⟨911796, by rfl⟩ : syracuseStep 2431457 = 1823593) B1823593
theorem B2923003 : Blo 1080619 2923003 := bstep (se 1 (by rfl) ⟨2192252, by rfl⟩ : syracuseStep 2923003 = 4384505) B4384505
theorem B1219135 : Blo 1080619 1219135 := bstep (se 1 (by rfl) ⟨914351, by rfl⟩ : syracuseStep 1219135 = 1828703) B1828703
theorem B2431763 : Blo 1080619 2431763 := bstep (se 1 (by rfl) ⟨1823822, by rfl⟩ : syracuseStep 2431763 = 3647645) B3647645
theorem B3087247 : Blo 1080619 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B8231867 : Blo 1080619 8231867 := bstep (se 1 (by rfl) ⟨6173900, by rfl⟩ : syracuseStep 8231867 = 12347801) B12347801
theorem B4103207 : Blo 1080619 4103207 := bstep (se 1 (by rfl) ⟨3077405, by rfl⟩ : syracuseStep 4103207 = 6154811) B6154811
theorem B2432123 : Blo 1080619 2432123 := bstep (se 1 (by rfl) ⟨1824092, by rfl⟩ : syracuseStep 2432123 = 3648185) B3648185
theorem B2432249 : Blo 1080619 2432249 := bstep (se 2 (by rfl) ⟨912093, by rfl⟩ : syracuseStep 2432249 = 1824187) B1824187
theorem B1219963 : Blo 1080619 1219963 := bstep (se 1 (by rfl) ⟨914972, by rfl⟩ : syracuseStep 1219963 = 1829945) B1829945
theorem B2432393 : Blo 1080619 2432393 := bstep (se 2 (by rfl) ⟨912147, by rfl⟩ : syracuseStep 2432393 = 1824295) B1824295
theorem B2432519 : Blo 1080619 2432519 := bstep (se 1 (by rfl) ⟨1824389, by rfl⟩ : syracuseStep 2432519 = 3648779) B3648779
theorem B41688593 : Blo 1080619 41688593 := bstep (se 2 (by rfl) ⟨15633222, by rfl⟩ : syracuseStep 41688593 = 31266445) B31266445
theorem B3907153 : Blo 1080619 3907153 := bstep (se 2 (by rfl) ⟨1465182, by rfl⟩ : syracuseStep 3907153 = 2930365) B2930365
theorem B2432699 : Blo 1080619 2432699 := bstep (se 1 (by rfl) ⟨1824524, by rfl⟩ : syracuseStep 2432699 = 3649049) B3649049
theorem B2924267 : Blo 1080619 2924267 := bstep (se 1 (by rfl) ⟨2193200, by rfl⟩ : syracuseStep 2924267 = 4386401) B4386401
theorem B3088135 : Blo 1080619 3088135 := bstep (se 1 (by rfl) ⟨2316101, by rfl⟩ : syracuseStep 3088135 = 4632203) B4632203
theorem B2432825 : Blo 1080619 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B9248687 : Blo 1080619 9248687 := bstep (se 1 (by rfl) ⟨6936515, by rfl⟩ : syracuseStep 9248687 = 13873031) B13873031
theorem B3088489 : Blo 1080619 3088489 := bstep (se 2 (by rfl) ⟨1158183, by rfl⟩ : syracuseStep 3088489 = 2316367) B2316367
theorem B2433455 : Blo 1080619 2433455 := bstep (se 1 (by rfl) ⟨1825091, by rfl⟩ : syracuseStep 2433455 = 3650183) B3650183
theorem B4694473 : Blo 1080619 4694473 := bstep (se 2 (by rfl) ⟨1760427, by rfl⟩ : syracuseStep 4694473 = 3520855) B3520855
theorem B2433491 : Blo 1080619 2433491 := bstep (se 1 (by rfl) ⟨1825118, by rfl⟩ : syracuseStep 2433491 = 3650237) B3650237
theorem B13345249 : Blo 1080619 13345249 := bstep (se 2 (by rfl) ⟨5004468, by rfl⟩ : syracuseStep 13345249 = 10008937) B10008937
theorem B2433599 : Blo 1080619 2433599 := bstep (se 1 (by rfl) ⟨1825199, by rfl⟩ : syracuseStep 2433599 = 3650399) B3650399
theorem B1155655 : Blo 1080619 1155655 := bstep (se 1 (by rfl) ⟨866741, by rfl⟩ : syracuseStep 1155655 = 1733483) B1733483
theorem B5481107 : Blo 1080619 5481107 := bstep (se 1 (by rfl) ⟨4110830, by rfl⟩ : syracuseStep 5481107 = 8221661) B8221661
theorem B2433707 : Blo 1080619 2433707 := bstep (se 1 (by rfl) ⟨1825280, by rfl⟩ : syracuseStep 2433707 = 3650561) B3650561
theorem B2466731 : Blo 1080619 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B25044005 : Blo 1080619 25044005 := bstep (se 4 (by rfl) ⟨2347875, by rfl⟩ : syracuseStep 25044005 = 4695751) B4695751
theorem B4105363 : Blo 1080619 4105363 := bstep (se 1 (by rfl) ⟨3079022, by rfl⟩ : syracuseStep 4105363 = 6158045) B6158045
theorem B2434247 : Blo 1080619 2434247 := bstep (se 1 (by rfl) ⟨1825685, by rfl⟩ : syracuseStep 2434247 = 3651371) B3651371
theorem B2434427 : Blo 1080619 2434427 := bstep (se 1 (by rfl) ⟨1825820, by rfl⟩ : syracuseStep 2434427 = 3651641) B3651641
theorem B1156475 : Blo 1080619 1156475 := bstep (se 1 (by rfl) ⟨867356, by rfl⟩ : syracuseStep 1156475 = 1734713) B1734713
theorem B2598331 : Blo 1080619 2598331 := bstep (se 1 (by rfl) ⟨1948748, by rfl⟩ : syracuseStep 2598331 = 3897497) B3897497
theorem B5481917 : Blo 1080619 5481917 := bstep (se 3 (by rfl) ⟨1027859, by rfl⟩ : syracuseStep 5481917 = 2055719) B2055719
theorem B2434553 : Blo 1080619 2434553 := bstep (se 2 (by rfl) ⟨912957, by rfl⟩ : syracuseStep 2434553 = 1825915) B1825915
theorem B2598407 : Blo 1080619 2598407 := bstep (se 1 (by rfl) ⟨1948805, by rfl⟩ : syracuseStep 2598407 = 3897611) B3897611
theorem B2434643 : Blo 1080619 2434643 := bstep (se 1 (by rfl) ⟨1825982, by rfl⟩ : syracuseStep 2434643 = 3651965) B3651965
theorem B100017821 : Blo 1080619 100017821 := bstep (se 3 (by rfl) ⟨18753341, by rfl⟩ : syracuseStep 100017821 = 37506683) B37506683
theorem B2434823 : Blo 1080619 2434823 := bstep (se 1 (by rfl) ⟨1826117, by rfl⟩ : syracuseStep 2434823 = 3652235) B3652235
theorem B7809209 : Blo 1080619 7809209 := bstep (se 2 (by rfl) ⟨2928453, by rfl⟩ : syracuseStep 7809209 = 5856907) B5856907
theorem B3647753 : Blo 1080619 3647753 := bstep (se 2 (by rfl) ⟨1367907, by rfl⟩ : syracuseStep 3647753 = 2735815) B2735815
theorem B2435435 : Blo 1080619 2435435 := bstep (se 1 (by rfl) ⟨1826576, by rfl⟩ : syracuseStep 2435435 = 3653153) B3653153
theorem B2435579 : Blo 1080619 2435579 := bstep (se 1 (by rfl) ⟨1826684, by rfl⟩ : syracuseStep 2435579 = 3653369) B3653369
theorem B2435705 : Blo 1080619 2435705 := bstep (se 2 (by rfl) ⟨913389, by rfl⟩ : syracuseStep 2435705 = 1826779) B1826779
theorem B2435759 : Blo 1080619 2435759 := bstep (se 1 (by rfl) ⟨1826819, by rfl⟩ : syracuseStep 2435759 = 3653639) B3653639
theorem B42740405 : Blo 1080619 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B2435831 : Blo 1080619 2435831 := bstep (se 1 (by rfl) ⟨1826873, by rfl⟩ : syracuseStep 2435831 = 3653747) B3653747
theorem B2436011 : Blo 1080619 2436011 := bstep (se 1 (by rfl) ⟨1827008, by rfl⟩ : syracuseStep 2436011 = 3654017) B3654017
theorem B7318667 : Blo 1080619 7318667 := bstep (se 1 (by rfl) ⟨5489000, by rfl⟩ : syracuseStep 7318667 = 10978001) B10978001
theorem B3648887 : Blo 1080619 3648887 := bstep (se 1 (by rfl) ⟨2736665, by rfl⟩ : syracuseStep 3648887 = 5473331) B5473331
theorem B2436551 : Blo 1080619 2436551 := bstep (se 1 (by rfl) ⟨1827413, by rfl⟩ : syracuseStep 2436551 = 3654827) B3654827
theorem B20819693 : Blo 1080619 20819693 := bstep (se 3 (by rfl) ⟨3903692, by rfl⟩ : syracuseStep 20819693 = 7807385) B7807385
theorem B2436911 : Blo 1080619 2436911 := bstep (se 1 (by rfl) ⟨1827683, by rfl⟩ : syracuseStep 2436911 = 3655367) B3655367
theorem B4632785 : Blo 1080619 4632785 := bstep (se 2 (by rfl) ⟨1737294, by rfl⟩ : syracuseStep 4632785 = 3474589) B3474589
theorem B20820239 : Blo 1080619 20820239 := bstep (se 1 (by rfl) ⟨15615179, by rfl⟩ : syracuseStep 20820239 = 31230359) B31230359
theorem B2437487 : Blo 1080619 2437487 := bstep (se 1 (by rfl) ⟨1828115, by rfl⟩ : syracuseStep 2437487 = 3656231) B3656231
theorem B3649967 : Blo 1080619 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B2437559 : Blo 1080619 2437559 := bstep (se 1 (by rfl) ⟨1828169, by rfl⟩ : syracuseStep 2437559 = 3656339) B3656339
theorem B4010465 : Blo 1080619 4010465 := bstep (se 2 (by rfl) ⟨1503924, by rfl⟩ : syracuseStep 4010465 = 3007849) B3007849
theorem B2437703 : Blo 1080619 2437703 := bstep (se 1 (by rfl) ⟨1828277, by rfl⟩ : syracuseStep 2437703 = 3656555) B3656555
theorem B2437739 : Blo 1080619 2437739 := bstep (se 1 (by rfl) ⟨1828304, by rfl⟩ : syracuseStep 2437739 = 3656609) B3656609
theorem B4109251 : Blo 1080619 4109251 := bstep (se 1 (by rfl) ⟨3081938, by rfl⟩ : syracuseStep 4109251 = 6163877) B6163877
theorem B2438135 : Blo 1080619 2438135 := bstep (se 1 (by rfl) ⟨1828601, by rfl⟩ : syracuseStep 2438135 = 3657203) B3657203
theorem B4109555 : Blo 1080619 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B2438495 : Blo 1080619 2438495 := bstep (se 1 (by rfl) ⟨1828871, by rfl⟩ : syracuseStep 2438495 = 3657743) B3657743
theorem B3650939 : Blo 1080619 3650939 := bstep (se 1 (by rfl) ⟨2738204, by rfl⟩ : syracuseStep 3650939 = 5476409) B5476409
theorem B4110011 : Blo 1080619 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B2438891 : Blo 1080619 2438891 := bstep (se 1 (by rfl) ⟨1829168, by rfl⟩ : syracuseStep 2438891 = 3658337) B3658337
theorem B8206109 : Blo 1080619 8206109 := bstep (se 3 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 8206109 = 3077291) B3077291
theorem B2439017 : Blo 1080619 2439017 := bstep (se 2 (by rfl) ⟨914631, by rfl⟩ : syracuseStep 2439017 = 1829263) B1829263
theorem B2308105 : Blo 1080619 2308105 := bstep (se 2 (by rfl) ⟨865539, by rfl⟩ : syracuseStep 2308105 = 1731079) B1731079
theorem B4929665 : Blo 1080619 4929665 := bstep (se 2 (by rfl) ⟨1848624, by rfl⟩ : syracuseStep 4929665 = 3697249) B3697249
theorem B5486777 : Blo 1080619 5486777 := bstep (se 2 (by rfl) ⟨2057541, by rfl⟩ : syracuseStep 5486777 = 4115083) B4115083
theorem B2603593 : Blo 1080619 2603593 := bstep (se 2 (by rfl) ⟨976347, by rfl⟩ : syracuseStep 2603593 = 1952695) B1952695
theorem B2439863 : Blo 1080619 2439863 := bstep (se 1 (by rfl) ⟨1829897, by rfl⟩ : syracuseStep 2439863 = 3659795) B3659795
theorem B3652343 : Blo 1080619 3652343 := bstep (se 1 (by rfl) ⟨2739257, by rfl⟩ : syracuseStep 3652343 = 5478515) B5478515
theorem B2440079 : Blo 1080619 2440079 := bstep (se 1 (by rfl) ⟨1830059, by rfl⟩ : syracuseStep 2440079 = 3660119) B3660119
theorem B23411699 : Blo 1080619 23411699 := bstep (se 1 (by rfl) ⟨17558774, by rfl⟩ : syracuseStep 23411699 = 35117549) B35117549
theorem B4111499 : Blo 1080619 4111499 := bstep (se 1 (by rfl) ⟨3083624, by rfl⟩ : syracuseStep 4111499 = 6167249) B6167249
theorem B1621211 : Blo 1080619 1621211 := bstep (se 1 (by rfl) ⟨1215908, by rfl⟩ : syracuseStep 1621211 = 2431817) B2431817
theorem B2604251 : Blo 1080619 2604251 := bstep (se 1 (by rfl) ⟨1953188, by rfl⟩ : syracuseStep 2604251 = 3906377) B3906377
theorem B1621385 : Blo 1080619 1621385 := bstep (se 2 (by rfl) ⟨608019, by rfl⟩ : syracuseStep 1621385 = 1216039) B1216039
theorem B2309575 : Blo 1080619 2309575 := bstep (se 1 (by rfl) ⟨1732181, by rfl⟩ : syracuseStep 2309575 = 3464363) B3464363
theorem B50609609 : Blo 1080619 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B6176249 : Blo 1080619 6176249 := bstep (se 2 (by rfl) ⟨2316093, by rfl⟩ : syracuseStep 6176249 = 4632187) B4632187
theorem B13188689 : Blo 1080619 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B1949267 : Blo 1080619 1949267 := bstep (se 1 (by rfl) ⟨1461950, by rfl⟩ : syracuseStep 1949267 = 2923901) B2923901
theorem B4111955 : Blo 1080619 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B6930035 : Blo 1080619 6930035 := bstep (se 1 (by rfl) ⟨5197526, by rfl⟩ : syracuseStep 6930035 = 10395053) B10395053
theorem B1621739 : Blo 1080619 1621739 := bstep (se 1 (by rfl) ⟨1216304, by rfl⟩ : syracuseStep 1621739 = 2432609) B2432609
theorem B3653423 : Blo 1080619 3653423 := bstep (se 1 (by rfl) ⟨2740067, by rfl⟩ : syracuseStep 3653423 = 5480135) B5480135
theorem B2735927 : Blo 1080619 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B2735977 : Blo 1080619 2735977 := bstep (se 2 (by rfl) ⟨1025991, by rfl⟩ : syracuseStep 2735977 = 2051983) B2051983
theorem B5488559 : Blo 1080619 5488559 := bstep (se 1 (by rfl) ⟨4116419, by rfl⟩ : syracuseStep 5488559 = 8232839) B8232839
theorem B1621967 : Blo 1080619 1621967 := bstep (se 1 (by rfl) ⟨1216475, by rfl⟩ : syracuseStep 1621967 = 2432951) B2432951
theorem B1622363 : Blo 1080619 1622363 := bstep (se 1 (by rfl) ⟨1216772, by rfl⟩ : syracuseStep 1622363 = 2433545) B2433545
theorem B1851815 : Blo 1080619 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B1622591 : Blo 1080619 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B2310763 : Blo 1080619 2310763 := bstep (se 1 (by rfl) ⟨1733072, by rfl⟩ : syracuseStep 2310763 = 3466145) B3466145
theorem B1622711 : Blo 1080619 1622711 := bstep (se 1 (by rfl) ⟨1217033, by rfl⟩ : syracuseStep 1622711 = 2434067) B2434067
theorem B1622939 : Blo 1080619 1622939 := bstep (se 1 (by rfl) ⟨1217204, by rfl⟩ : syracuseStep 1622939 = 2434409) B2434409
theorem B23708675 : Blo 1080619 23708675 := bstep (se 1 (by rfl) ⟨17781506, by rfl⟩ : syracuseStep 23708675 = 35563013) B35563013
theorem B6931493 : Blo 1080619 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B4932733 : Blo 1080619 4932733 := bstep (se 3 (by rfl) ⟨924887, by rfl⟩ : syracuseStep 4932733 = 1849775) B1849775
theorem B2737385 : Blo 1080619 2737385 := bstep (se 2 (by rfl) ⟨1026519, by rfl⟩ : syracuseStep 2737385 = 2053039) B2053039
theorem B1852649 : Blo 1080619 1852649 := bstep (se 2 (by rfl) ⟨694743, by rfl⟩ : syracuseStep 1852649 = 1389487) B1389487
theorem B1623335 : Blo 1080619 1623335 := bstep (se 1 (by rfl) ⟨1217501, by rfl⟩ : syracuseStep 1623335 = 2435003) B2435003
theorem B112543019 : Blo 1080619 112543019 := bstep (se 1 (by rfl) ⟨84407264, by rfl⟩ : syracuseStep 112543019 = 168814529) B168814529
theorem B7816499 : Blo 1080619 7816499 := bstep (se 1 (by rfl) ⟨5862374, by rfl⟩ : syracuseStep 7816499 = 11724749) B11724749
theorem B5555561 : Blo 1080619 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B1623419 : Blo 1080619 1623419 := bstep (se 1 (by rfl) ⟨1217564, by rfl⟩ : syracuseStep 1623419 = 2435129) B2435129
theorem B2737547 : Blo 1080619 2737547 := bstep (se 1 (by rfl) ⟨2053160, by rfl⟩ : syracuseStep 2737547 = 4106321) B4106321
theorem B1623545 : Blo 1080619 1623545 := bstep (se 2 (by rfl) ⟨608829, by rfl⟩ : syracuseStep 1623545 = 1217659) B1217659
theorem B2737759 : Blo 1080619 2737759 := bstep (se 1 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 2737759 = 4106639) B4106639
theorem B1623647 : Blo 1080619 1623647 := bstep (se 1 (by rfl) ⟨1217735, by rfl⟩ : syracuseStep 1623647 = 2435471) B2435471
theorem B1623863 : Blo 1080619 1623863 := bstep (se 1 (by rfl) ⟨1217897, by rfl⟩ : syracuseStep 1623863 = 2435795) B2435795
theorem B2311993 : Blo 1080619 2311993 := bstep (se 2 (by rfl) ⟨866997, by rfl⟩ : syracuseStep 2311993 = 1733995) B1733995
theorem B3655529 : Blo 1080619 3655529 := bstep (se 2 (by rfl) ⟨1370823, by rfl⟩ : syracuseStep 3655529 = 2741647) B2741647
theorem B1624169 : Blo 1080619 1624169 := bstep (se 2 (by rfl) ⟨609063, by rfl⟩ : syracuseStep 1624169 = 1218127) B1218127
theorem B2738387 : Blo 1080619 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B5622041 : Blo 1080619 5622041 := bstep (se 2 (by rfl) ⟨2108265, by rfl⟩ : syracuseStep 5622041 = 4216531) B4216531
theorem B3655961 : Blo 1080619 3655961 := bstep (se 2 (by rfl) ⟨1370985, by rfl⟩ : syracuseStep 3655961 = 2741971) B2741971
theorem B1624487 : Blo 1080619 1624487 := bstep (se 1 (by rfl) ⟨1218365, by rfl⟩ : syracuseStep 1624487 = 2436731) B2436731
theorem B4114871 : Blo 1080619 4114871 := bstep (se 1 (by rfl) ⟨3086153, by rfl⟩ : syracuseStep 4114871 = 6172307) B6172307
theorem B1624571 : Blo 1080619 1624571 := bstep (se 1 (by rfl) ⟨1218428, by rfl⟩ : syracuseStep 1624571 = 2436857) B2436857
theorem B1624697 : Blo 1080619 1624697 := bstep (se 2 (by rfl) ⟨609261, by rfl⟩ : syracuseStep 1624697 = 1218523) B1218523
theorem B1624751 : Blo 1080619 1624751 := bstep (se 1 (by rfl) ⟨1218563, by rfl⟩ : syracuseStep 1624751 = 2437127) B2437127
theorem B1624799 : Blo 1080619 1624799 := bstep (se 1 (by rfl) ⟨1218599, by rfl⟩ : syracuseStep 1624799 = 2437199) B2437199
theorem B11717399 : Blo 1080619 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B1625063 : Blo 1080619 1625063 := bstep (se 1 (by rfl) ⟨1218797, by rfl⟩ : syracuseStep 1625063 = 2437595) B2437595
theorem B22564013 : Blo 1080619 22564013 := bstep (se 3 (by rfl) ⟨4230752, by rfl⟩ : syracuseStep 22564013 = 8461505) B8461505
theorem B1625321 : Blo 1080619 1625321 := bstep (se 2 (by rfl) ⟨609495, by rfl⟩ : syracuseStep 1625321 = 1218991) B1218991
theorem B7032095 : Blo 1080619 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B1625375 : Blo 1080619 1625375 := bstep (se 1 (by rfl) ⟨1219031, by rfl⟩ : syracuseStep 1625375 = 2438063) B2438063
theorem B2313659 : Blo 1080619 2313659 := bstep (se 1 (by rfl) ⟨1735244, by rfl⟩ : syracuseStep 2313659 = 3470489) B3470489
theorem B1625543 : Blo 1080619 1625543 := bstep (se 1 (by rfl) ⟨1219157, by rfl⟩ : syracuseStep 1625543 = 2438315) B2438315
theorem B3657311 : Blo 1080619 3657311 := bstep (se 1 (by rfl) ⟨2742983, by rfl⟩ : syracuseStep 3657311 = 5485967) B5485967
theorem B11095649 : Blo 1080619 11095649 := bstep (se 2 (by rfl) ⟨4160868, by rfl⟩ : syracuseStep 11095649 = 8321737) B8321737
theorem B20795089 : Blo 1080619 20795089 := bstep (se 2 (by rfl) ⟨7798158, by rfl⟩ : syracuseStep 20795089 = 15596317) B15596317
theorem B1625897 : Blo 1080619 1625897 := bstep (se 2 (by rfl) ⟨609711, by rfl⟩ : syracuseStep 1625897 = 1219423) B1219423
theorem B13881131 : Blo 1080619 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B1625903 : Blo 1080619 1625903 := bstep (se 1 (by rfl) ⟨1219427, by rfl⟩ : syracuseStep 1625903 = 2438855) B2438855
theorem B3952849 : Blo 1080619 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B1298651 : Blo 1080619 1298651 := bstep (se 1 (by rfl) ⟨973988, by rfl⟩ : syracuseStep 1298651 = 1947977) B1947977
theorem B1626377 : Blo 1080619 1626377 := bstep (se 2 (by rfl) ⟨609891, by rfl⟩ : syracuseStep 1626377 = 1219783) B1219783
theorem B1626479 : Blo 1080619 1626479 := bstep (se 1 (by rfl) ⟨1219859, by rfl⟩ : syracuseStep 1626479 = 2439719) B2439719
theorem B18502019 : Blo 1080619 18502019 := bstep (se 1 (by rfl) ⟨13876514, by rfl⟩ : syracuseStep 18502019 = 27753029) B27753029
theorem B2740655 : Blo 1080619 2740655 := bstep (se 1 (by rfl) ⟨2055491, by rfl⟩ : syracuseStep 2740655 = 4110983) B4110983
theorem B1626695 : Blo 1080619 1626695 := bstep (se 1 (by rfl) ⟨1220021, by rfl⟩ : syracuseStep 1626695 = 2440043) B2440043
theorem B1626731 : Blo 1080619 1626731 := bstep (se 1 (by rfl) ⟨1220048, by rfl⟩ : syracuseStep 1626731 = 2440097) B2440097
theorem B5854031 : Blo 1080619 5854031 := bstep (se 1 (by rfl) ⟨4390523, by rfl⟩ : syracuseStep 5854031 = 8781047) B8781047
theorem B2315179 : Blo 1080619 2315179 := bstep (se 1 (by rfl) ⟨1736384, by rfl⟩ : syracuseStep 2315179 = 3472769) B3472769
theorem B3658715 : Blo 1080619 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B1823735 : Blo 1080619 1823735 := bstep (se 1 (by rfl) ⟨1367801, by rfl⟩ : syracuseStep 1823735 = 2735603) B2735603
theorem B3658877 : Blo 1080619 3658877 := bstep (se 3 (by rfl) ⟨686039, by rfl⟩ : syracuseStep 3658877 = 1372079) B1372079
theorem B5199005 : Blo 1080619 5199005 := bstep (se 3 (by rfl) ⟨974813, by rfl⟩ : syracuseStep 5199005 = 1949627) B1949627
theorem B3658985 : Blo 1080619 3658985 := bstep (se 2 (by rfl) ⟨1372119, by rfl⟩ : syracuseStep 3658985 = 2744239) B2744239
theorem B2741627 : Blo 1080619 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B3659147 : Blo 1080619 3659147 := bstep (se 1 (by rfl) ⟨2744360, by rfl⟩ : syracuseStep 3659147 = 5488721) B5488721
theorem B2741921 : Blo 1080619 2741921 := bstep (se 2 (by rfl) ⟨1028220, by rfl⟩ : syracuseStep 2741921 = 2056441) B2056441
theorem B1824491 : Blo 1080619 1824491 := bstep (se 1 (by rfl) ⟨1368368, by rfl⟩ : syracuseStep 1824491 = 2736737) B2736737
theorem B2742619 : Blo 1080619 2742619 := bstep (se 1 (by rfl) ⟨2056964, by rfl⟩ : syracuseStep 2742619 = 4113929) B4113929
theorem B3332687 : Blo 1080619 3332687 := bstep (se 1 (by rfl) ⟨2499515, by rfl⟩ : syracuseStep 3332687 = 4999031) B4999031
theorem B1825463 : Blo 1080619 1825463 := bstep (se 1 (by rfl) ⟨1369097, by rfl⟩ : syracuseStep 1825463 = 2738195) B2738195
theorem B2743591 : Blo 1080619 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B3661175 : Blo 1080619 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B1826185 : Blo 1080619 1826185 := bstep (se 2 (by rfl) ⟨684819, by rfl⟩ : syracuseStep 1826185 = 1369639) B1369639
theorem B2743865 : Blo 1080619 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B1826617 : Blo 1080619 1826617 := bstep (se 2 (by rfl) ⟨684981, by rfl⟩ : syracuseStep 1826617 = 1369963) B1369963
theorem B1826921 : Blo 1080619 1826921 := bstep (se 2 (by rfl) ⟨685095, by rfl⟩ : syracuseStep 1826921 = 1370191) B1370191
theorem B9265499 : Blo 1080619 9265499 := bstep (se 1 (by rfl) ⟨6949124, by rfl⟩ : syracuseStep 9265499 = 13898249) B13898249
theorem B7791011 : Blo 1080619 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B1368571 : Blo 1080619 1368571 := bstep (se 1 (by rfl) ⟨1026428, by rfl⟩ : syracuseStep 1368571 = 2052857) B2052857
theorem B9232967 : Blo 1080619 9232967 := bstep (se 1 (by rfl) ⟨6924725, by rfl⟩ : syracuseStep 9232967 = 13849451) B13849451
theorem B6939283 : Blo 1080619 6939283 := bstep (se 1 (by rfl) ⟨5204462, by rfl⟩ : syracuseStep 6939283 = 10408925) B10408925
theorem B2056927 : Blo 1080619 2056927 := bstep (se 1 (by rfl) ⟨1542695, by rfl⟩ : syracuseStep 2056927 = 3085391) B3085391
theorem B12346343 : Blo 1080619 12346343 := bstep (se 1 (by rfl) ⟨9259757, by rfl⟩ : syracuseStep 12346343 = 18519515) B18519515
theorem B1369543 : Blo 1080619 1369543 := bstep (se 1 (by rfl) ⟨1027157, by rfl⟩ : syracuseStep 1369543 = 2054315) B2054315
theorem B1828345 : Blo 1080619 1828345 := bstep (se 2 (by rfl) ⟨685629, by rfl⟩ : syracuseStep 1828345 = 1371259) B1371259
theorem B88991459 : Blo 1080619 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B1828615 : Blo 1080619 1828615 := bstep (se 1 (by rfl) ⟨1371461, by rfl⟩ : syracuseStep 1828615 = 2742923) B2742923
theorem B1828649 : Blo 1080619 1828649 := bstep (se 2 (by rfl) ⟨685743, by rfl⟩ : syracuseStep 1828649 = 1371487) B1371487
theorem B1370459 : Blo 1080619 1370459 := bstep (se 1 (by rfl) ⟨1027844, by rfl⟩ : syracuseStep 1370459 = 2055689) B2055689
theorem B1829371 : Blo 1080619 1829371 := bstep (se 1 (by rfl) ⟨1372028, by rfl⟩ : syracuseStep 1829371 = 2744057) B2744057
theorem B1370935 : Blo 1080619 1370935 := bstep (se 1 (by rfl) ⟨1028201, by rfl⟩ : syracuseStep 1370935 = 2056403) B2056403
theorem B1829803 : Blo 1080619 1829803 := bstep (se 1 (by rfl) ⟨1372352, by rfl⟩ : syracuseStep 1829803 = 2744705) B2744705
theorem B12315725 : Blo 1080619 12315725 := bstep (se 3 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 12315725 = 4618397) B4618397
theorem B1830107 : Blo 1080619 1830107 := bstep (se 1 (by rfl) ⟨1372580, by rfl⟩ : syracuseStep 1830107 = 2745161) B2745161
theorem B1371431 : Blo 1080619 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B1371755 : Blo 1080619 1371755 := bstep (se 1 (by rfl) ⟨1028816, by rfl⟩ : syracuseStep 1371755 = 2057633) B2057633
theorem B3698291 : Blo 1080619 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B4943663 : Blo 1080619 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B1372135 : Blo 1080619 1372135 := bstep (se 1 (by rfl) ⟨1029101, by rfl⟩ : syracuseStep 1372135 = 2058203) B2058203
theorem B44396545 : Blo 1080619 44396545 := bstep (se 2 (by rfl) ⟨16648704, by rfl⟩ : syracuseStep 44396545 = 33297409) B33297409
theorem B9367811 : Blo 1080619 9367811 := bstep (se 1 (by rfl) ⟨7025858, by rfl⟩ : syracuseStep 9367811 = 14051717) B14051717
theorem B19788137 : Blo 1080619 19788137 := bstep (se 2 (by rfl) ⟨7420551, by rfl⟩ : syracuseStep 19788137 = 14841103) B14841103
theorem B97382873 : Blo 1080619 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B40104409 : Blo 1080619 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B6583007 : Blo 1080619 6583007 := bstep (se 1 (by rfl) ⟨4937255, by rfl⟩ : syracuseStep 6583007 = 9874511) B9874511
theorem B18510767 : Blo 1080619 18510767 := bstep (se 1 (by rfl) ⟨13883075, by rfl⟩ : syracuseStep 18510767 = 27766151) B27766151
theorem B14840777 : Blo 1080619 14840777 := bstep (se 2 (by rfl) ⟨5565291, by rfl⟩ : syracuseStep 14840777 = 11130583) B11130583
theorem B4617577 : Blo 1080619 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B3897811 : Blo 1080619 3897811 := bstep (se 1 (by rfl) ⟨2923358, by rfl⟩ : syracuseStep 3897811 = 5846717) B5846717
theorem B1538623 : Blo 1080619 1538623 := bstep (se 1 (by rfl) ⟨1153967, by rfl⟩ : syracuseStep 1538623 = 2307935) B2307935
theorem B1735231 : Blo 1080619 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B9370441 : Blo 1080619 9370441 := bstep (se 2 (by rfl) ⟨3513915, by rfl⟩ : syracuseStep 9370441 = 7027831) B7027831
theorem B3701629 : Blo 1080619 3701629 := bstep (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) B1388111
theorem B4389875 : Blo 1080619 4389875 := bstep (se 1 (by rfl) ⟨3292406, by rfl⟩ : syracuseStep 4389875 = 6584813) B6584813
theorem B6945821 : Blo 1080619 6945821 := bstep (se 3 (by rfl) ⟨1302341, by rfl⟩ : syracuseStep 6945821 = 2604683) B2604683
theorem B3079387 : Blo 1080619 3079387 := bstep (se 1 (by rfl) ⟨2309540, by rfl⟩ : syracuseStep 3079387 = 4619081) B4619081
theorem B5471549 : Blo 1080619 5471549 := bstep (se 3 (by rfl) ⟨1025915, by rfl⟩ : syracuseStep 5471549 = 2051831) B2051831
theorem B1080667 : Blo 1080619 1080667 := bstep (se 1 (by rfl) ⟨810500, by rfl⟩ : syracuseStep 1080667 = 1621001) B1621001
theorem B1080687 : Blo 1080619 1080687 := bstep (se 1 (by rfl) ⟨810515, by rfl⟩ : syracuseStep 1080687 = 1621031) B1621031
theorem B1080743 : Blo 1080619 1080743 := bstep (se 1 (by rfl) ⟨810557, by rfl⟩ : syracuseStep 1080743 = 1621115) B1621115
theorem B1080827 : Blo 1080619 1080827 := bstep (se 1 (by rfl) ⟨810620, by rfl⟩ : syracuseStep 1080827 = 1621241) B1621241
theorem B1080895 : Blo 1080619 1080895 := bstep (se 1 (by rfl) ⟨810671, by rfl⟩ : syracuseStep 1080895 = 1621343) B1621343
theorem B1080903 : Blo 1080619 1080903 := bstep (se 1 (by rfl) ⟨810677, by rfl⟩ : syracuseStep 1080903 = 1621355) B1621355
theorem B3079775 : Blo 1080619 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B1081055 : Blo 1080619 1081055 := bstep (se 1 (by rfl) ⟨810791, by rfl⟩ : syracuseStep 1081055 = 1621583) B1621583
theorem B10419961 : Blo 1080619 10419961 := bstep (se 2 (by rfl) ⟨3907485, by rfl⟩ : syracuseStep 10419961 = 7814971) B7814971
theorem B1081135 : Blo 1080619 1081135 := bstep (se 1 (by rfl) ⟨810851, by rfl⟩ : syracuseStep 1081135 = 1621703) B1621703
theorem B6586219 : Blo 1080619 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B1081243 : Blo 1080619 1081243 := bstep (se 1 (by rfl) ⟨810932, by rfl⟩ : syracuseStep 1081243 = 1621865) B1621865
theorem B1081295 : Blo 1080619 1081295 := bstep (se 1 (by rfl) ⟨810971, by rfl⟩ : syracuseStep 1081295 = 1621943) B1621943
theorem B1081319 : Blo 1080619 1081319 := bstep (se 1 (by rfl) ⟨810989, by rfl⟩ : syracuseStep 1081319 = 1621979) B1621979
theorem B3080231 : Blo 1080619 3080231 := bstep (se 1 (by rfl) ⟨2310173, by rfl⟩ : syracuseStep 3080231 = 4620347) B4620347
theorem B1081575 : Blo 1080619 1081575 := bstep (se 1 (by rfl) ⟨811181, by rfl⟩ : syracuseStep 1081575 = 1622363) B1622363
theorem B1081727 : Blo 1080619 1081727 := bstep (se 1 (by rfl) ⟨811295, by rfl⟩ : syracuseStep 1081727 = 1622591) B1622591
theorem B1081807 : Blo 1080619 1081807 := bstep (se 1 (by rfl) ⟨811355, by rfl⟩ : syracuseStep 1081807 = 1622711) B1622711
theorem B6947279 : Blo 1080619 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B6259297 : Blo 1080619 6259297 := bstep (se 2 (by rfl) ⟨2347236, by rfl⟩ : syracuseStep 6259297 = 4694473) B4694473
theorem B1081959 : Blo 1080619 1081959 := bstep (se 1 (by rfl) ⟨811469, by rfl⟩ : syracuseStep 1081959 = 1622939) B1622939
theorem B17793665 : Blo 1080619 17793665 := bstep (se 2 (by rfl) ⟨6672624, by rfl⟩ : syracuseStep 17793665 = 13345249) B13345249
theorem B4620995 : Blo 1080619 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B1540873 : Blo 1080619 1540873 := bstep (se 2 (by rfl) ⟨577827, by rfl⟩ : syracuseStep 1540873 = 1155655) B1155655
theorem B3081017 : Blo 1080619 3081017 := bstep (se 2 (by rfl) ⟨1155381, by rfl⟩ : syracuseStep 3081017 = 2310763) B2310763
theorem B1082223 : Blo 1080619 1082223 := bstep (se 1 (by rfl) ⟨811667, by rfl⟩ : syracuseStep 1082223 = 1623335) B1623335
theorem B5210999 : Blo 1080619 5210999 := bstep (se 1 (by rfl) ⟨3908249, by rfl⟩ : syracuseStep 5210999 = 7816499) B7816499
theorem B1082279 : Blo 1080619 1082279 := bstep (se 1 (by rfl) ⟨811709, by rfl⟩ : syracuseStep 1082279 = 1623419) B1623419
theorem B1082363 : Blo 1080619 1082363 := bstep (se 1 (by rfl) ⟨811772, by rfl⟩ : syracuseStep 1082363 = 1623545) B1623545
theorem B1082431 : Blo 1080619 1082431 := bstep (se 1 (by rfl) ⟨811823, by rfl⟩ : syracuseStep 1082431 = 1623647) B1623647
theorem B1082575 : Blo 1080619 1082575 := bstep (se 1 (by rfl) ⟨811931, by rfl⟩ : syracuseStep 1082575 = 1623863) B1623863
theorem B1082779 : Blo 1080619 1082779 := bstep (se 1 (by rfl) ⟨812084, by rfl⟩ : syracuseStep 1082779 = 1624169) B1624169
theorem B5473817 : Blo 1080619 5473817 := bstep (se 2 (by rfl) ⟨2052681, by rfl⟩ : syracuseStep 5473817 = 4105363) B4105363
theorem B1082991 : Blo 1080619 1082991 := bstep (se 1 (by rfl) ⟨812243, by rfl⟩ : syracuseStep 1082991 = 1624487) B1624487
theorem B1083047 : Blo 1080619 1083047 := bstep (se 1 (by rfl) ⟨812285, by rfl⟩ : syracuseStep 1083047 = 1624571) B1624571
theorem B1083131 : Blo 1080619 1083131 := bstep (se 1 (by rfl) ⟨812348, by rfl⟩ : syracuseStep 1083131 = 1624697) B1624697
theorem B1083167 : Blo 1080619 1083167 := bstep (se 1 (by rfl) ⟨812375, by rfl⟩ : syracuseStep 1083167 = 1624751) B1624751
theorem B1083199 : Blo 1080619 1083199 := bstep (se 1 (by rfl) ⟨812399, by rfl⟩ : syracuseStep 1083199 = 1624799) B1624799
theorem B1083375 : Blo 1080619 1083375 := bstep (se 1 (by rfl) ⟨812531, by rfl⟩ : syracuseStep 1083375 = 1625063) B1625063
theorem B1083547 : Blo 1080619 1083547 := bstep (se 1 (by rfl) ⟨812660, by rfl⟩ : syracuseStep 1083547 = 1625321) B1625321
theorem B4688063 : Blo 1080619 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B1083583 : Blo 1080619 1083583 := bstep (se 1 (by rfl) ⟨812687, by rfl⟩ : syracuseStep 1083583 = 1625375) B1625375
theorem B3082475 : Blo 1080619 3082475 := bstep (se 1 (by rfl) ⟨2311856, by rfl⟩ : syracuseStep 3082475 = 4623713) B4623713
theorem B1542439 : Blo 1080619 1542439 := bstep (se 1 (by rfl) ⟨1156829, by rfl⟩ : syracuseStep 1542439 = 2313659) B2313659
theorem B1083695 : Blo 1080619 1083695 := bstep (se 1 (by rfl) ⟨812771, by rfl⟩ : syracuseStep 1083695 = 1625543) B1625543
theorem B3082657 : Blo 1080619 3082657 := bstep (se 2 (by rfl) ⟨1155996, by rfl⟩ : syracuseStep 3082657 = 2311993) B2311993
theorem B1083931 : Blo 1080619 1083931 := bstep (se 1 (by rfl) ⟨812948, by rfl⟩ : syracuseStep 1083931 = 1625897) B1625897
theorem B1083935 : Blo 1080619 1083935 := bstep (se 1 (by rfl) ⟨812951, by rfl⟩ : syracuseStep 1083935 = 1625903) B1625903
theorem B12519967 : Blo 1080619 12519967 := bstep (se 1 (by rfl) ⟨9389975, by rfl⟩ : syracuseStep 12519967 = 18779951) B18779951
theorem B1084251 : Blo 1080619 1084251 := bstep (se 1 (by rfl) ⟨813188, by rfl⟩ : syracuseStep 1084251 = 1626377) B1626377
theorem B1084319 : Blo 1080619 1084319 := bstep (se 1 (by rfl) ⟨813239, by rfl⟩ : syracuseStep 1084319 = 1626479) B1626479
theorem B1084463 : Blo 1080619 1084463 := bstep (se 1 (by rfl) ⟨813347, by rfl⟩ : syracuseStep 1084463 = 1626695) B1626695
theorem B1084487 : Blo 1080619 1084487 := bstep (se 1 (by rfl) ⟨813365, by rfl⟩ : syracuseStep 1084487 = 1626731) B1626731
theorem B3902687 : Blo 1080619 3902687 := bstep (se 1 (by rfl) ⟨2927015, by rfl⟩ : syracuseStep 3902687 = 5854031) B5854031
theorem B1215823 : Blo 1080619 1215823 := bstep (se 1 (by rfl) ⟨911867, by rfl⟩ : syracuseStep 1215823 = 1823735) B1823735
theorem B14814829 : Blo 1080619 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B3083933 : Blo 1080619 3083933 := bstep (se 3 (by rfl) ⟨578237, by rfl⟩ : syracuseStep 3083933 = 1156475) B1156475
theorem B23432885 : Blo 1080619 23432885 := bstep (se 5 (by rfl) ⟨1098416, by rfl⟩ : syracuseStep 23432885 = 2196833) B2196833
theorem B1216327 : Blo 1080619 1216327 := bstep (se 1 (by rfl) ⟨912245, by rfl⟩ : syracuseStep 1216327 = 1824491) B1824491
theorem B9244691 : Blo 1080619 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B1216975 : Blo 1080619 1216975 := bstep (se 1 (by rfl) ⟨912731, by rfl⟩ : syracuseStep 1216975 = 1825463) B1825463
theorem B27726785 : Blo 1080619 27726785 := bstep (se 2 (by rfl) ⟨10397544, by rfl⟩ : syracuseStep 27726785 = 20795089) B20795089
theorem B27792395 : Blo 1080619 27792395 := bstep (se 1 (by rfl) ⟨20844296, by rfl⟩ : syracuseStep 27792395 = 41688593) B41688593
theorem B6165791 : Blo 1080619 6165791 := bstep (se 1 (by rfl) ⟨4624343, by rfl⟩ : syracuseStep 6165791 = 9248687) B9248687
theorem B1217947 : Blo 1080619 1217947 := bstep (se 1 (by rfl) ⟨913460, by rfl⟩ : syracuseStep 1217947 = 1826921) B1826921
theorem B15832493 : Blo 1080619 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B13145773 : Blo 1080619 13145773 := bstep (se 3 (by rfl) ⟨2464832, by rfl⟩ : syracuseStep 13145773 = 4929665) B4929665
theorem B8230895 : Blo 1080619 8230895 := bstep (se 1 (by rfl) ⟨6173171, by rfl⟩ : syracuseStep 8230895 = 12346343) B12346343
theorem B6166793 : Blo 1080619 6166793 := bstep (se 2 (by rfl) ⟨2312547, by rfl⟩ : syracuseStep 6166793 = 4625095) B4625095
theorem B1219099 : Blo 1080619 1219099 := bstep (se 1 (by rfl) ⟨914324, by rfl⟩ : syracuseStep 1219099 = 1828649) B1828649
theorem B3086905 : Blo 1080619 3086905 := bstep (se 2 (by rfl) ⟨1157589, by rfl⟩ : syracuseStep 3086905 = 2315179) B2315179
theorem B5479001 : Blo 1080619 5479001 := bstep (se 2 (by rfl) ⟨2054625, by rfl⟩ : syracuseStep 5479001 = 4109251) B4109251
theorem B2431835 : Blo 1080619 2431835 := bstep (se 1 (by rfl) ⟨1823876, by rfl⟩ : syracuseStep 2431835 = 3647753) B3647753
theorem B8887165 : Blo 1080619 8887165 := bstep (se 3 (by rfl) ⟨1666343, by rfl⟩ : syracuseStep 8887165 = 3332687) B3332687
theorem B1220071 : Blo 1080619 1220071 := bstep (se 1 (by rfl) ⟨915053, by rfl⟩ : syracuseStep 1220071 = 1830107) B1830107
theorem B2432591 : Blo 1080619 2432591 := bstep (se 1 (by rfl) ⟨1824443, by rfl⟩ : syracuseStep 2432591 = 3648887) B3648887
theorem B2465527 : Blo 1080619 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B3088523 : Blo 1080619 3088523 := bstep (se 1 (by rfl) ⟨2316392, by rfl⟩ : syracuseStep 3088523 = 4632785) B4632785
theorem B2433311 : Blo 1080619 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B64921915 : Blo 1080619 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B60170701 : Blo 1080619 60170701 := bstep (se 3 (by rfl) ⟨11282006, by rfl⟩ : syracuseStep 60170701 = 22564013) B22564013
theorem B2433959 : Blo 1080619 2433959 := bstep (se 1 (by rfl) ⟨1825469, by rfl⟩ : syracuseStep 2433959 = 3650939) B3650939
theorem B12493921 : Blo 1080619 12493921 := bstep (se 2 (by rfl) ⟨4685220, by rfl⟩ : syracuseStep 12493921 = 9370441) B9370441
theorem B4105849 : Blo 1080619 4105849 := bstep (se 2 (by rfl) ⟨1539693, by rfl⟩ : syracuseStep 4105849 = 3079387) B3079387
theorem B2434895 : Blo 1080619 2434895 := bstep (se 1 (by rfl) ⟨1826171, by rfl⟩ : syracuseStep 2434895 = 3652343) B3652343
theorem B2434913 : Blo 1080619 2434913 := bstep (se 2 (by rfl) ⟨913092, by rfl⟩ : syracuseStep 2434913 = 1826185) B1826185
theorem B15607799 : Blo 1080619 15607799 := bstep (se 1 (by rfl) ⟨11705849, by rfl⟩ : syracuseStep 15607799 = 23411699) B23411699
theorem B2926583 : Blo 1080619 2926583 := bstep (se 1 (by rfl) ⟨2194937, by rfl⟩ : syracuseStep 2926583 = 4389875) B4389875
theorem B4630547 : Blo 1080619 4630547 := bstep (se 1 (by rfl) ⟨3472910, by rfl⟩ : syracuseStep 4630547 = 6945821) B6945821
theorem B3647699 : Blo 1080619 3647699 := bstep (se 1 (by rfl) ⟨2735774, by rfl⟩ : syracuseStep 3647699 = 5471549) B5471549
theorem B8792459 : Blo 1080619 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B2435489 : Blo 1080619 2435489 := bstep (se 2 (by rfl) ⟨913308, by rfl⟩ : syracuseStep 2435489 = 1826617) B1826617
theorem B3647969 : Blo 1080619 3647969 := bstep (se 2 (by rfl) ⟨1367988, by rfl⟩ : syracuseStep 3647969 = 2735977) B2735977
theorem B2435615 : Blo 1080619 2435615 := bstep (se 1 (by rfl) ⟨1826711, by rfl⟩ : syracuseStep 2435615 = 3653423) B3653423
theorem B15805783 : Blo 1080619 15805783 := bstep (se 1 (by rfl) ⟨11854337, by rfl⟩ : syracuseStep 15805783 = 23708675) B23708675
theorem B5484023 : Blo 1080619 5484023 := bstep (se 1 (by rfl) ⟨4113017, by rfl⟩ : syracuseStep 5484023 = 8226035) B8226035
theorem B9252377 : Blo 1080619 9252377 := bstep (se 2 (by rfl) ⟨3469641, by rfl⟩ : syracuseStep 9252377 = 6939283) B6939283
theorem B3649319 : Blo 1080619 3649319 := bstep (se 1 (by rfl) ⟨2736989, by rfl⟩ : syracuseStep 3649319 = 5473979) B5473979
theorem B2437019 : Blo 1080619 2437019 := bstep (se 1 (by rfl) ⟨1827764, by rfl⟩ : syracuseStep 2437019 = 3655529) B3655529
theorem B10694573 : Blo 1080619 10694573 := bstep (se 3 (by rfl) ⟨2005232, by rfl⟩ : syracuseStep 10694573 = 4010465) B4010465
theorem B3748027 : Blo 1080619 3748027 := bstep (se 1 (by rfl) ⟨2811020, by rfl⟩ : syracuseStep 3748027 = 5622041) B5622041
theorem B2437307 : Blo 1080619 2437307 := bstep (se 1 (by rfl) ⟨1827980, by rfl⟩ : syracuseStep 2437307 = 3655961) B3655961
theorem B4108553 : Blo 1080619 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B7811599 : Blo 1080619 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B2437793 : Blo 1080619 2437793 := bstep (se 2 (by rfl) ⟨914172, by rfl⟩ : syracuseStep 2437793 = 1828345) B1828345
theorem B5485319 : Blo 1080619 5485319 := bstep (se 1 (by rfl) ⟨4113989, by rfl⟩ : syracuseStep 5485319 = 8227979) B8227979
theorem B3650345 : Blo 1080619 3650345 := bstep (se 2 (by rfl) ⟨1368879, by rfl⟩ : syracuseStep 3650345 = 2737759) B2737759
theorem B2438153 : Blo 1080619 2438153 := bstep (se 2 (by rfl) ⟨914307, by rfl⟩ : syracuseStep 2438153 = 1828615) B1828615
theorem B2929673 : Blo 1080619 2929673 := bstep (se 2 (by rfl) ⟨1098627, by rfl⟩ : syracuseStep 2929673 = 2197255) B2197255
theorem B3650615 : Blo 1080619 3650615 := bstep (se 1 (by rfl) ⟨2737961, by rfl⟩ : syracuseStep 3650615 = 5475923) B5475923
theorem B2438207 : Blo 1080619 2438207 := bstep (se 1 (by rfl) ⟨1828655, by rfl⟩ : syracuseStep 2438207 = 3657311) B3657311
theorem B20788325 : Blo 1080619 20788325 := bstep (se 4 (by rfl) ⟨1948905, by rfl⟩ : syracuseStep 20788325 = 3897811) B3897811
theorem B9254087 : Blo 1080619 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B31241537 : Blo 1080619 31241537 := bstep (se 2 (by rfl) ⟨11715576, by rfl⟩ : syracuseStep 31241537 = 23431153) B23431153
theorem B4109723 : Blo 1080619 4109723 := bstep (se 1 (by rfl) ⟨3082292, by rfl⟩ : syracuseStep 4109723 = 6164585) B6164585
theorem B12334679 : Blo 1080619 12334679 := bstep (se 1 (by rfl) ⟨9251009, by rfl⟩ : syracuseStep 12334679 = 18502019) B18502019
theorem B5486291 : Blo 1080619 5486291 := bstep (se 1 (by rfl) ⟨4114718, by rfl⟩ : syracuseStep 5486291 = 8229437) B8229437
theorem B2439143 : Blo 1080619 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B2439161 : Blo 1080619 2439161 := bstep (se 2 (by rfl) ⟨914685, by rfl⟩ : syracuseStep 2439161 = 1829371) B1829371
theorem B10401851 : Blo 1080619 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B2439251 : Blo 1080619 2439251 := bstep (se 1 (by rfl) ⟨1829438, by rfl⟩ : syracuseStep 2439251 = 3658877) B3658877
theorem B2439323 : Blo 1080619 2439323 := bstep (se 1 (by rfl) ⟨1829492, by rfl⟩ : syracuseStep 2439323 = 3658985) B3658985
theorem B2930843 : Blo 1080619 2930843 := bstep (se 1 (by rfl) ⟨2198132, by rfl⟩ : syracuseStep 2930843 = 4396265) B4396265
theorem B1947883 : Blo 1080619 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B2439431 : Blo 1080619 2439431 := bstep (se 1 (by rfl) ⟨1829573, by rfl⟩ : syracuseStep 2439431 = 3659147) B3659147
theorem B2439737 : Blo 1080619 2439737 := bstep (se 2 (by rfl) ⟨914901, by rfl⟩ : syracuseStep 2439737 = 1829803) B1829803
theorem B3652559 : Blo 1080619 3652559 := bstep (se 1 (by rfl) ⟨2739419, by rfl⟩ : syracuseStep 3652559 = 5478839) B5478839
theorem B1620971 : Blo 1080619 1620971 := bstep (se 1 (by rfl) ⟨1215728, by rfl⟩ : syracuseStep 1620971 = 2431457) B2431457
theorem B1621175 : Blo 1080619 1621175 := bstep (se 1 (by rfl) ⟨1215881, by rfl⟩ : syracuseStep 1621175 = 2431763) B2431763
theorem B5487911 : Blo 1080619 5487911 := bstep (se 1 (by rfl) ⟨4115933, by rfl⟩ : syracuseStep 5487911 = 8231867) B8231867
theorem B2735471 : Blo 1080619 2735471 := bstep (se 1 (by rfl) ⟨2051603, by rfl⟩ : syracuseStep 2735471 = 4103207) B4103207
theorem B1621415 : Blo 1080619 1621415 := bstep (se 1 (by rfl) ⟨1216061, by rfl⟩ : syracuseStep 1621415 = 2432123) B2432123
theorem B1621499 : Blo 1080619 1621499 := bstep (se 1 (by rfl) ⟨1216124, by rfl⟩ : syracuseStep 1621499 = 2432249) B2432249
theorem B2440783 : Blo 1080619 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B1621595 : Blo 1080619 1621595 := bstep (se 1 (by rfl) ⟨1216196, by rfl⟩ : syracuseStep 1621595 = 2432393) B2432393
theorem B1621679 : Blo 1080619 1621679 := bstep (se 1 (by rfl) ⟨1216259, by rfl⟩ : syracuseStep 1621679 = 2432519) B2432519
theorem B1621799 : Blo 1080619 1621799 := bstep (se 1 (by rfl) ⟨1216349, by rfl⟩ : syracuseStep 1621799 = 2432699) B2432699
theorem B1621883 : Blo 1080619 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B59195393 : Blo 1080619 59195393 := bstep (se 2 (by rfl) ⟨22198272, by rfl⟩ : syracuseStep 59195393 = 44396545) B44396545
theorem B6176999 : Blo 1080619 6176999 := bstep (se 1 (by rfl) ⟨4632749, by rfl⟩ : syracuseStep 6176999 = 9265499) B9265499
theorem B5194007 : Blo 1080619 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B1622303 : Blo 1080619 1622303 := bstep (se 1 (by rfl) ⟨1216727, by rfl⟩ : syracuseStep 1622303 = 2433455) B2433455
theorem B1622327 : Blo 1080619 1622327 := bstep (se 1 (by rfl) ⟨1216745, by rfl⟩ : syracuseStep 1622327 = 2433491) B2433491
theorem B1622399 : Blo 1080619 1622399 := bstep (se 1 (by rfl) ⟨1216799, by rfl⟩ : syracuseStep 1622399 = 2433599) B2433599
theorem B3654071 : Blo 1080619 3654071 := bstep (se 1 (by rfl) ⟨2740553, by rfl⟩ : syracuseStep 3654071 = 5481107) B5481107
theorem B1622471 : Blo 1080619 1622471 := bstep (se 1 (by rfl) ⟨1216853, by rfl⟩ : syracuseStep 1622471 = 2433707) B2433707
theorem B16696003 : Blo 1080619 16696003 := bstep (se 1 (by rfl) ⟨12522002, by rfl⟩ : syracuseStep 16696003 = 25044005) B25044005
theorem B1622825 : Blo 1080619 1622825 := bstep (se 2 (by rfl) ⟨608559, by rfl⟩ : syracuseStep 1622825 = 1217119) B1217119
theorem B1622831 : Blo 1080619 1622831 := bstep (se 1 (by rfl) ⟨1217123, by rfl⟩ : syracuseStep 1622831 = 2434247) B2434247
theorem B3654557 : Blo 1080619 3654557 := bstep (se 3 (by rfl) ⟨685229, by rfl⟩ : syracuseStep 3654557 = 1370459) B1370459
theorem B1622951 : Blo 1080619 1622951 := bstep (se 1 (by rfl) ⟨1217213, by rfl⟩ : syracuseStep 1622951 = 2434427) B2434427
theorem B3654611 : Blo 1080619 3654611 := bstep (se 1 (by rfl) ⟨2740958, by rfl⟩ : syracuseStep 3654611 = 5481917) B5481917
theorem B1623035 : Blo 1080619 1623035 := bstep (se 1 (by rfl) ⟨1217276, by rfl⟩ : syracuseStep 1623035 = 2434553) B2434553
theorem B1623095 : Blo 1080619 1623095 := bstep (se 1 (by rfl) ⟨1217321, by rfl⟩ : syracuseStep 1623095 = 2434643) B2434643
theorem B59327639 : Blo 1080619 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B1623215 : Blo 1080619 1623215 := bstep (se 1 (by rfl) ⟨1217411, by rfl⟩ : syracuseStep 1623215 = 2434823) B2434823
theorem B1623623 : Blo 1080619 1623623 := bstep (se 1 (by rfl) ⟨1217717, by rfl⟩ : syracuseStep 1623623 = 2435435) B2435435
theorem B1623719 : Blo 1080619 1623719 := bstep (se 1 (by rfl) ⟨1217789, by rfl⟩ : syracuseStep 1623719 = 2435579) B2435579
theorem B1623803 : Blo 1080619 1623803 := bstep (se 1 (by rfl) ⟨1217852, by rfl⟩ : syracuseStep 1623803 = 2435705) B2435705
theorem B1623839 : Blo 1080619 1623839 := bstep (se 1 (by rfl) ⟨1217879, by rfl⟩ : syracuseStep 1623839 = 2435759) B2435759
theorem B28493603 : Blo 1080619 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B1623887 : Blo 1080619 1623887 := bstep (se 1 (by rfl) ⟨1217915, by rfl⟩ : syracuseStep 1623887 = 2435831) B2435831
theorem B1624007 : Blo 1080619 1624007 := bstep (se 1 (by rfl) ⟨1218005, by rfl⟩ : syracuseStep 1624007 = 2436011) B2436011
theorem B8210483 : Blo 1080619 8210483 := bstep (se 1 (by rfl) ⟨6157862, by rfl⟩ : syracuseStep 8210483 = 12315725) B12315725
theorem B1624361 : Blo 1080619 1624361 := bstep (se 2 (by rfl) ⟨609135, by rfl⟩ : syracuseStep 1624361 = 1218271) B1218271
theorem B1624367 : Blo 1080619 1624367 := bstep (se 1 (by rfl) ⟨1218275, by rfl⟩ : syracuseStep 1624367 = 2436551) B2436551
theorem B14993873 : Blo 1080619 14993873 := bstep (se 2 (by rfl) ⟨5622702, by rfl⟩ : syracuseStep 14993873 = 11245405) B11245405
theorem B13879795 : Blo 1080619 13879795 := bstep (se 1 (by rfl) ⟨10409846, by rfl⟩ : syracuseStep 13879795 = 20819693) B20819693
theorem B1624607 : Blo 1080619 1624607 := bstep (se 1 (by rfl) ⟨1218455, by rfl⟩ : syracuseStep 1624607 = 2436911) B2436911
theorem B3295775 : Blo 1080619 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B6245207 : Blo 1080619 6245207 := bstep (se 1 (by rfl) ⟨4683905, by rfl⟩ : syracuseStep 6245207 = 9367811) B9367811
theorem B13880159 : Blo 1080619 13880159 := bstep (se 1 (by rfl) ⟨10410119, by rfl⟩ : syracuseStep 13880159 = 20820239) B20820239
theorem B13192091 : Blo 1080619 13192091 := bstep (se 1 (by rfl) ⟨9894068, by rfl⟩ : syracuseStep 13192091 = 19788137) B19788137
theorem B1624991 : Blo 1080619 1624991 := bstep (se 1 (by rfl) ⟨1218743, by rfl⟩ : syracuseStep 1624991 = 2437487) B2437487
theorem B1625039 : Blo 1080619 1625039 := bstep (se 1 (by rfl) ⟨1218779, by rfl⟩ : syracuseStep 1625039 = 2437559) B2437559
theorem B1625129 : Blo 1080619 1625129 := bstep (se 2 (by rfl) ⟨609423, by rfl⟩ : syracuseStep 1625129 = 1218847) B1218847
theorem B1625135 : Blo 1080619 1625135 := bstep (se 1 (by rfl) ⟨1218851, by rfl⟩ : syracuseStep 1625135 = 2437703) B2437703
theorem B1625159 : Blo 1080619 1625159 := bstep (se 1 (by rfl) ⟨1218869, by rfl⟩ : syracuseStep 1625159 = 2437739) B2437739
theorem B3656825 : Blo 1080619 3656825 := bstep (se 2 (by rfl) ⟨1371309, by rfl⟩ : syracuseStep 3656825 = 2742619) B2742619
theorem B12340511 : Blo 1080619 12340511 := bstep (se 1 (by rfl) ⟨9255383, by rfl⟩ : syracuseStep 12340511 = 18510767) B18510767
theorem B1625423 : Blo 1080619 1625423 := bstep (se 1 (by rfl) ⟨1219067, by rfl⟩ : syracuseStep 1625423 = 2438135) B2438135
theorem B2051497 : Blo 1080619 2051497 := bstep (se 2 (by rfl) ⟨769311, by rfl⟩ : syracuseStep 2051497 = 1538623) B1538623
theorem B2313641 : Blo 1080619 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B1625513 : Blo 1080619 1625513 := bstep (se 2 (by rfl) ⟨609567, by rfl⟩ : syracuseStep 1625513 = 1219135) B1219135
theorem B3657149 : Blo 1080619 3657149 := bstep (se 3 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 3657149 = 1371431) B1371431
theorem B2739703 : Blo 1080619 2739703 := bstep (se 1 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 2739703 = 4109555) B4109555
theorem B1625663 : Blo 1080619 1625663 := bstep (se 1 (by rfl) ⟨1219247, by rfl⟩ : syracuseStep 1625663 = 2438495) B2438495
theorem B2740007 : Blo 1080619 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B1625927 : Blo 1080619 1625927 := bstep (se 1 (by rfl) ⟨1219445, by rfl⟩ : syracuseStep 1625927 = 2438891) B2438891
theorem B4935505 : Blo 1080619 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B4116329 : Blo 1080619 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B1626011 : Blo 1080619 1626011 := bstep (se 1 (by rfl) ⟨1219508, by rfl⟩ : syracuseStep 1626011 = 2439017) B2439017
theorem B3657851 : Blo 1080619 3657851 := bstep (se 1 (by rfl) ⟨2743388, by rfl⟩ : syracuseStep 3657851 = 5486777) B5486777
theorem B3658013 : Blo 1080619 3658013 := bstep (se 3 (by rfl) ⟨685877, by rfl⟩ : syracuseStep 3658013 = 1371755) B1371755
theorem B3658121 : Blo 1080619 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B1626575 : Blo 1080619 1626575 := bstep (se 1 (by rfl) ⟨1219931, by rfl⟩ : syracuseStep 1626575 = 2439863) B2439863
theorem B1626617 : Blo 1080619 1626617 := bstep (se 2 (by rfl) ⟨609981, by rfl⟩ : syracuseStep 1626617 = 1219963) B1219963
theorem B1626719 : Blo 1080619 1626719 := bstep (se 1 (by rfl) ⟨1220039, by rfl⟩ : syracuseStep 1626719 = 2440079) B2440079
theorem B2740999 : Blo 1080619 2740999 := bstep (se 1 (by rfl) ⟨2055749, by rfl⟩ : syracuseStep 2740999 = 4111499) B4111499
theorem B33739739 : Blo 1080619 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B4117499 : Blo 1080619 4117499 := bstep (se 1 (by rfl) ⟨3088124, by rfl⟩ : syracuseStep 4117499 = 6176249) B6176249
theorem B4117513 : Blo 1080619 4117513 := bstep (se 2 (by rfl) ⟨1544067, by rfl⟩ : syracuseStep 4117513 = 3088135) B3088135
theorem B1299511 : Blo 1080619 1299511 := bstep (se 1 (by rfl) ⟨974633, by rfl⟩ : syracuseStep 1299511 = 1949267) B1949267
theorem B2741303 : Blo 1080619 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B2053183 : Blo 1080619 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B1823951 : Blo 1080619 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B3659039 : Blo 1080619 3659039 := bstep (se 1 (by rfl) ⟨2744279, by rfl⟩ : syracuseStep 3659039 = 5488559) B5488559
theorem B12309893 : Blo 1080619 12309893 := bstep (se 4 (by rfl) ⟨1154052, by rfl⟩ : syracuseStep 12309893 = 2308105) B2308105
theorem B4117985 : Blo 1080619 4117985 := bstep (se 2 (by rfl) ⟨1544244, by rfl⟩ : syracuseStep 4117985 = 3088489) B3088489
theorem B1234543 : Blo 1080619 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B3463069 : Blo 1080619 3463069 := bstep (se 3 (by rfl) ⟨649325, by rfl⟩ : syracuseStep 3463069 = 1298651) B1298651
theorem B1824761 : Blo 1080619 1824761 := bstep (se 2 (by rfl) ⟨684285, by rfl⟩ : syracuseStep 1824761 = 1368571) B1368571
theorem B1824923 : Blo 1080619 1824923 := bstep (se 1 (by rfl) ⟨1368692, by rfl⟩ : syracuseStep 1824923 = 2737385) B2737385
theorem B1235099 : Blo 1080619 1235099 := bstep (se 1 (by rfl) ⟨926324, by rfl⟩ : syracuseStep 1235099 = 1852649) B1852649
theorem B2316443 : Blo 1080619 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B75028679 : Blo 1080619 75028679 := bstep (se 1 (by rfl) ⟨56271509, by rfl⟩ : syracuseStep 75028679 = 112543019) B112543019
theorem B1825031 : Blo 1080619 1825031 := bstep (se 1 (by rfl) ⟨1368773, by rfl⟩ : syracuseStep 1825031 = 2737547) B2737547
theorem B2742569 : Blo 1080619 2742569 := bstep (se 2 (by rfl) ⟨1028463, by rfl⟩ : syracuseStep 2742569 = 2056927) B2056927
theorem B6576491 : Blo 1080619 6576491 := bstep (se 1 (by rfl) ⟨4932368, by rfl⟩ : syracuseStep 6576491 = 9864737) B9864737
theorem B1825591 : Blo 1080619 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B6576977 : Blo 1080619 6576977 := bstep (se 2 (by rfl) ⟨2466366, by rfl⟩ : syracuseStep 6576977 = 4932733) B4932733
theorem B2743247 : Blo 1080619 2743247 := bstep (se 1 (by rfl) ⟨2057435, by rfl⟩ : syracuseStep 2743247 = 4114871) B4114871
theorem B5201081 : Blo 1080619 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B3464441 : Blo 1080619 3464441 := bstep (se 2 (by rfl) ⟨1299165, by rfl⟩ : syracuseStep 3464441 = 2598331) B2598331
theorem B1826057 : Blo 1080619 1826057 := bstep (se 2 (by rfl) ⟨684771, by rfl⟩ : syracuseStep 1826057 = 1369543) B1369543
theorem B7397099 : Blo 1080619 7397099 := bstep (se 1 (by rfl) ⟨5547824, by rfl⟩ : syracuseStep 7397099 = 11095649) B11095649
theorem B6577949 : Blo 1080619 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B39575405 : Blo 1080619 39575405 := bstep (se 3 (by rfl) ⟨7420388, by rfl⟩ : syracuseStep 39575405 = 14840777) B14840777
theorem B1827103 : Blo 1080619 1827103 := bstep (se 1 (by rfl) ⟨1370327, by rfl⟩ : syracuseStep 1827103 = 2740655) B2740655
theorem B4383341 : Blo 1080619 4383341 := bstep (se 3 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 4383341 = 1643753) B1643753
theorem B8217287 : Blo 1080619 8217287 := bstep (se 1 (by rfl) ⟨6162965, by rfl⟩ : syracuseStep 8217287 = 12325931) B12325931
theorem B97608401 : Blo 1080619 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B3466003 : Blo 1080619 3466003 := bstep (se 1 (by rfl) ⟨2599502, by rfl⟩ : syracuseStep 3466003 = 5199005) B5199005
theorem B13853551 : Blo 1080619 13853551 := bstep (se 1 (by rfl) ⟨10390163, by rfl⟩ : syracuseStep 13853551 = 20780327) B20780327
theorem B2057071 : Blo 1080619 2057071 := bstep (se 1 (by rfl) ⟨1542803, by rfl⟩ : syracuseStep 2057071 = 3085607) B3085607
theorem B1827751 : Blo 1080619 1827751 := bstep (se 1 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 1827751 = 2741627) B2741627
theorem B1827913 : Blo 1080619 1827913 := bstep (se 2 (by rfl) ⟨685467, by rfl⟩ : syracuseStep 1827913 = 1370935) B1370935
theorem B1827947 : Blo 1080619 1827947 := bstep (se 1 (by rfl) ⟨1370960, by rfl⟩ : syracuseStep 1827947 = 2741921) B2741921
theorem B1829243 : Blo 1080619 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B1829513 : Blo 1080619 1829513 := bstep (se 2 (by rfl) ⟨686067, by rfl⟩ : syracuseStep 1829513 = 1372135) B1372135
theorem B5270465 : Blo 1080619 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B6155311 : Blo 1080619 6155311 := bstep (se 1 (by rfl) ⟨4616483, by rfl⟩ : syracuseStep 6155311 = 9232967) B9232967
theorem B53472545 : Blo 1080619 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B1732271 : Blo 1080619 1732271 := bstep (se 1 (by rfl) ⟨1299203, by rfl⟩ : syracuseStep 1732271 = 2598407) B2598407
theorem B66678547 : Blo 1080619 66678547 := bstep (se 1 (by rfl) ⟨50008910, by rfl⟩ : syracuseStep 66678547 = 100017821) B100017821
theorem B5206139 : Blo 1080619 5206139 := bstep (se 1 (by rfl) ⟨3904604, by rfl⟩ : syracuseStep 5206139 = 7809209) B7809209
theorem B6156769 : Blo 1080619 6156769 := bstep (se 2 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 6156769 = 4617577) B4617577
theorem B4879111 : Blo 1080619 4879111 := bstep (se 1 (by rfl) ⟨3659333, by rfl⟩ : syracuseStep 4879111 = 7318667) B7318667
theorem B4388671 : Blo 1080619 4388671 := bstep (se 1 (by rfl) ⟨3291503, by rfl⟩ : syracuseStep 4388671 = 6583007) B6583007
theorem B3897337 : Blo 1080619 3897337 := bstep (se 2 (by rfl) ⟨1461501, by rfl⟩ : syracuseStep 3897337 = 2923003) B2923003
theorem B3471457 : Blo 1080619 3471457 := bstep (se 2 (by rfl) ⟨1301796, by rfl⟩ : syracuseStep 3471457 = 2603593) B2603593
theorem B5470739 : Blo 1080619 5470739 := bstep (se 1 (by rfl) ⟨4103054, by rfl⟩ : syracuseStep 5470739 = 8206109) B8206109
theorem B3079433 : Blo 1080619 3079433 := bstep (se 2 (by rfl) ⟨1154787, by rfl⟩ : syracuseStep 3079433 = 2309575) B2309575
theorem B7798045 : Blo 1080619 7798045 := bstep (se 3 (by rfl) ⟨1462133, by rfl⟩ : syracuseStep 7798045 = 2924267) B2924267
theorem B5209537 : Blo 1080619 5209537 := bstep (se 2 (by rfl) ⟨1953576, by rfl⟩ : syracuseStep 5209537 = 3907153) B3907153
theorem B1080807 : Blo 1080619 1080807 := bstep (se 1 (by rfl) ⟨810605, by rfl⟩ : syracuseStep 1080807 = 1621211) B1621211
theorem B1736167 : Blo 1080619 1736167 := bstep (se 1 (by rfl) ⟨1302125, by rfl⟩ : syracuseStep 1736167 = 2604251) B2604251
theorem B1080923 : Blo 1080619 1080923 := bstep (se 1 (by rfl) ⟨810692, by rfl⟩ : syracuseStep 1080923 = 1621385) B1621385
theorem B13893281 : Blo 1080619 13893281 := bstep (se 2 (by rfl) ⟨5209980, by rfl⟩ : syracuseStep 13893281 = 10419961) B10419961
theorem B4620023 : Blo 1080619 4620023 := bstep (se 1 (by rfl) ⟨3465017, by rfl⟩ : syracuseStep 4620023 = 6930035) B6930035
theorem B8781625 : Blo 1080619 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B1081159 : Blo 1080619 1081159 := bstep (se 1 (by rfl) ⟨810869, by rfl⟩ : syracuseStep 1081159 = 1621739) B1621739
theorem B1081311 : Blo 1080619 1081311 := bstep (se 1 (by rfl) ⟨810983, by rfl⟩ : syracuseStep 1081311 = 1621967) B1621967
theorem B1081535 : Blo 1080619 1081535 := bstep (se 1 (by rfl) ⟨811151, by rfl⟩ : syracuseStep 1081535 = 1622303) B1622303
theorem B1081551 : Blo 1080619 1081551 := bstep (se 1 (by rfl) ⟨811163, by rfl⟩ : syracuseStep 1081551 = 1622327) B1622327
theorem B1081599 : Blo 1080619 1081599 := bstep (se 1 (by rfl) ⟨811199, by rfl⟩ : syracuseStep 1081599 = 1622399) B1622399
theorem B1081647 : Blo 1080619 1081647 := bstep (se 1 (by rfl) ⟨811235, by rfl⟩ : syracuseStep 1081647 = 1622471) B1622471
theorem B11862443 : Blo 1080619 11862443 := bstep (se 1 (by rfl) ⟨8896832, by rfl⟩ : syracuseStep 11862443 = 17793665) B17793665
theorem B3080663 : Blo 1080619 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B1081883 : Blo 1080619 1081883 := bstep (se 1 (by rfl) ⟨811412, by rfl⟩ : syracuseStep 1081883 = 1622825) B1622825
theorem B1081887 : Blo 1080619 1081887 := bstep (se 1 (by rfl) ⟨811415, by rfl⟩ : syracuseStep 1081887 = 1622831) B1622831
theorem B3473999 : Blo 1080619 3473999 := bstep (se 1 (by rfl) ⟨2605499, by rfl⟩ : syracuseStep 3473999 = 5210999) B5210999
theorem B1081967 : Blo 1080619 1081967 := bstep (se 1 (by rfl) ⟨811475, by rfl⟩ : syracuseStep 1081967 = 1622951) B1622951
theorem B1082023 : Blo 1080619 1082023 := bstep (se 1 (by rfl) ⟨811517, by rfl⟩ : syracuseStep 1082023 = 1623035) B1623035
theorem B1082063 : Blo 1080619 1082063 := bstep (se 1 (by rfl) ⟨811547, by rfl⟩ : syracuseStep 1082063 = 1623095) B1623095
theorem B39551759 : Blo 1080619 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B1082143 : Blo 1080619 1082143 := bstep (se 1 (by rfl) ⟨811607, by rfl⟩ : syracuseStep 1082143 = 1623215) B1623215
theorem B4621337 : Blo 1080619 4621337 := bstep (se 2 (by rfl) ⟨1733001, by rfl⟩ : syracuseStep 4621337 = 3466003) B3466003
theorem B1082415 : Blo 1080619 1082415 := bstep (se 1 (by rfl) ⟨811811, by rfl⟩ : syracuseStep 1082415 = 1623623) B1623623
theorem B1082479 : Blo 1080619 1082479 := bstep (se 1 (by rfl) ⟨811859, by rfl⟩ : syracuseStep 1082479 = 1623719) B1623719
theorem B1082535 : Blo 1080619 1082535 := bstep (se 1 (by rfl) ⟨811901, by rfl⟩ : syracuseStep 1082535 = 1623803) B1623803
theorem B1082559 : Blo 1080619 1082559 := bstep (se 1 (by rfl) ⟨811919, by rfl⟩ : syracuseStep 1082559 = 1623839) B1623839
theorem B1082591 : Blo 1080619 1082591 := bstep (se 1 (by rfl) ⟨811943, by rfl⟩ : syracuseStep 1082591 = 1623887) B1623887
theorem B1082671 : Blo 1080619 1082671 := bstep (se 1 (by rfl) ⟨812003, by rfl⟩ : syracuseStep 1082671 = 1624007) B1624007
theorem B5473655 : Blo 1080619 5473655 := bstep (se 1 (by rfl) ⟨4105241, by rfl⟩ : syracuseStep 5473655 = 8210483) B8210483
theorem B1082907 : Blo 1080619 1082907 := bstep (se 1 (by rfl) ⟨812180, by rfl⟩ : syracuseStep 1082907 = 1624361) B1624361
theorem B1082911 : Blo 1080619 1082911 := bstep (se 1 (by rfl) ⟨812183, by rfl⟩ : syracuseStep 1082911 = 1624367) B1624367
theorem B9995915 : Blo 1080619 9995915 := bstep (se 1 (by rfl) ⟨7496936, by rfl⟩ : syracuseStep 9995915 = 14993873) B14993873
theorem B1083071 : Blo 1080619 1083071 := bstep (se 1 (by rfl) ⟨812303, by rfl⟩ : syracuseStep 1083071 = 1624607) B1624607
theorem B4163471 : Blo 1080619 4163471 := bstep (se 1 (by rfl) ⟨3122603, by rfl⟩ : syracuseStep 4163471 = 6245207) B6245207
theorem B1083327 : Blo 1080619 1083327 := bstep (se 1 (by rfl) ⟨812495, by rfl⟩ : syracuseStep 1083327 = 1624991) B1624991
theorem B1083359 : Blo 1080619 1083359 := bstep (se 1 (by rfl) ⟨812519, by rfl⟩ : syracuseStep 1083359 = 1625039) B1625039
theorem B1083419 : Blo 1080619 1083419 := bstep (se 1 (by rfl) ⟨812564, by rfl⟩ : syracuseStep 1083419 = 1625129) B1625129
theorem B1083423 : Blo 1080619 1083423 := bstep (se 1 (by rfl) ⟨812567, by rfl⟩ : syracuseStep 1083423 = 1625135) B1625135
theorem B1083439 : Blo 1080619 1083439 := bstep (se 1 (by rfl) ⟨812579, by rfl⟩ : syracuseStep 1083439 = 1625159) B1625159
theorem B5474465 : Blo 1080619 5474465 := bstep (se 2 (by rfl) ⟨2052924, by rfl⟩ : syracuseStep 5474465 = 4105849) B4105849
theorem B8227007 : Blo 1080619 8227007 := bstep (se 1 (by rfl) ⟨6170255, by rfl⟩ : syracuseStep 8227007 = 12340511) B12340511
theorem B1083615 : Blo 1080619 1083615 := bstep (se 1 (by rfl) ⟨812711, by rfl⟩ : syracuseStep 1083615 = 1625423) B1625423
theorem B1083675 : Blo 1080619 1083675 := bstep (se 1 (by rfl) ⟨812756, by rfl⟩ : syracuseStep 1083675 = 1625513) B1625513
theorem B1083775 : Blo 1080619 1083775 := bstep (se 1 (by rfl) ⟨812831, by rfl⟩ : syracuseStep 1083775 = 1625663) B1625663
theorem B1083951 : Blo 1080619 1083951 := bstep (se 1 (by rfl) ⟨812963, by rfl⟩ : syracuseStep 1083951 = 1625927) B1625927
theorem B1084007 : Blo 1080619 1084007 := bstep (se 1 (by rfl) ⟨813005, by rfl⟩ : syracuseStep 1084007 = 1626011) B1626011
theorem B6163127 : Blo 1080619 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B1084383 : Blo 1080619 1084383 := bstep (se 1 (by rfl) ⟨813287, by rfl⟩ : syracuseStep 1084383 = 1626575) B1626575
theorem B1084411 : Blo 1080619 1084411 := bstep (se 1 (by rfl) ⟨813308, by rfl⟩ : syracuseStep 1084411 = 1626617) B1626617
theorem B1084479 : Blo 1080619 1084479 := bstep (se 1 (by rfl) ⟨813359, by rfl⟩ : syracuseStep 1084479 = 1626719) B1626719
theorem B18484523 : Blo 1080619 18484523 := bstep (se 1 (by rfl) ⟨13863392, by rfl⟩ : syracuseStep 18484523 = 27726785) B27726785
theorem B1215967 : Blo 1080619 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B10554995 : Blo 1080619 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B1216507 : Blo 1080619 1216507 := bstep (se 1 (by rfl) ⟨912380, by rfl⟩ : syracuseStep 1216507 = 1824761) B1824761
theorem B1216615 : Blo 1080619 1216615 := bstep (se 1 (by rfl) ⟨912461, by rfl⟩ : syracuseStep 1216615 = 1824923) B1824923
theorem B1216687 : Blo 1080619 1216687 := bstep (se 1 (by rfl) ⟨912515, by rfl⟩ : syracuseStep 1216687 = 1825031) B1825031
theorem B21074377 : Blo 1080619 21074377 := bstep (se 2 (by rfl) ⟨7902891, by rfl⟩ : syracuseStep 21074377 = 15805783) B15805783
theorem B1217371 : Blo 1080619 1217371 := bstep (se 1 (by rfl) ⟨913028, by rfl⟩ : syracuseStep 1217371 = 1826057) B1826057
theorem B88904729 : Blo 1080619 88904729 := bstep (se 2 (by rfl) ⟨33339273, by rfl⟩ : syracuseStep 88904729 = 66678547) B66678547
theorem B26383603 : Blo 1080619 26383603 := bstep (se 1 (by rfl) ⟨19787702, by rfl⟩ : syracuseStep 26383603 = 39575405) B39575405
theorem B2922227 : Blo 1080619 2922227 := bstep (se 1 (by rfl) ⟨2191670, by rfl⟩ : syracuseStep 2922227 = 4383341) B4383341
theorem B5478191 : Blo 1080619 5478191 := bstep (se 1 (by rfl) ⟨4108643, by rfl⟩ : syracuseStep 5478191 = 8217287) B8217287
theorem B1218631 : Blo 1080619 1218631 := bstep (se 1 (by rfl) ⟨913973, by rfl⟩ : syracuseStep 1218631 = 1827947) B1827947
theorem B3087031 : Blo 1080619 3087031 := bstep (se 1 (by rfl) ⟨2315273, by rfl⟩ : syracuseStep 3087031 = 4630547) B4630547
theorem B8788733 : Blo 1080619 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B2431799 : Blo 1080619 2431799 := bstep (se 1 (by rfl) ⟨1823849, by rfl⟩ : syracuseStep 2431799 = 3647699) B3647699
theorem B1219495 : Blo 1080619 1219495 := bstep (se 1 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 1219495 = 1829243) B1829243
theorem B2431979 : Blo 1080619 2431979 := bstep (se 1 (by rfl) ⟨1823984, by rfl⟩ : syracuseStep 2431979 = 3647969) B3647969
theorem B1219675 : Blo 1080619 1219675 := bstep (se 1 (by rfl) ⟨914756, by rfl⟩ : syracuseStep 1219675 = 1829513) B1829513
theorem B1646057 : Blo 1080619 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B6168251 : Blo 1080619 6168251 := bstep (se 1 (by rfl) ⟨4626188, by rfl⟩ : syracuseStep 6168251 = 9252377) B9252377
theorem B2432879 : Blo 1080619 2432879 := bstep (se 1 (by rfl) ⟨1824659, by rfl⟩ : syracuseStep 2432879 = 3649319) B3649319
theorem B4628609 : Blo 1080619 4628609 := bstep (se 2 (by rfl) ⟨1735728, by rfl⟩ : syracuseStep 4628609 = 3471457) B3471457
theorem B2597177 : Blo 1080619 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B13017509 : Blo 1080619 13017509 := bstep (se 4 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 13017509 = 2440783) B2440783
theorem B2433563 : Blo 1080619 2433563 := bstep (se 1 (by rfl) ⟨1825172, by rfl⟩ : syracuseStep 2433563 = 3650345) B3650345
theorem B2433743 : Blo 1080619 2433743 := bstep (se 1 (by rfl) ⟨1825307, by rfl⟩ : syracuseStep 2433743 = 3650615) B3650615
theorem B6169391 : Blo 1080619 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B2434121 : Blo 1080619 2434121 := bstep (se 2 (by rfl) ⟨912795, by rfl⟩ : syracuseStep 2434121 = 1825591) B1825591
theorem B6169709 : Blo 1080619 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B23406245 : Blo 1080619 23406245 := bstep (se 4 (by rfl) ⟨2194335, by rfl⟩ : syracuseStep 23406245 = 4388671) B4388671
theorem B3647159 : Blo 1080619 3647159 := bstep (se 1 (by rfl) ⟨2735369, by rfl⟩ : syracuseStep 3647159 = 5470739) B5470739
theorem B10397393 : Blo 1080619 10397393 := bstep (se 2 (by rfl) ⟨3899022, by rfl⟩ : syracuseStep 10397393 = 7798045) B7798045
theorem B2435039 : Blo 1080619 2435039 := bstep (se 1 (by rfl) ⟨1826279, by rfl⟩ : syracuseStep 2435039 = 3652559) B3652559
theorem B17541197 : Blo 1080619 17541197 := bstep (se 3 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 17541197 = 6577949) B6577949
theorem B3287369 : Blo 1080619 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B11708833 : Blo 1080619 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B39463595 : Blo 1080619 39463595 := bstep (se 1 (by rfl) ⟨29597696, by rfl⟩ : syracuseStep 39463595 = 59195393) B59195393
theorem B2436047 : Blo 1080619 2436047 := bstep (se 1 (by rfl) ⟨1827035, by rfl⟩ : syracuseStep 2436047 = 3654071) B3654071
theorem B4631519 : Blo 1080619 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B2436137 : Blo 1080619 2436137 := bstep (se 2 (by rfl) ⟨913551, by rfl⟩ : syracuseStep 2436137 = 1827103) B1827103
theorem B80227601 : Blo 1080619 80227601 := bstep (se 2 (by rfl) ⟨30085350, by rfl⟩ : syracuseStep 80227601 = 60170701) B60170701
theorem B2436371 : Blo 1080619 2436371 := bstep (se 1 (by rfl) ⟨1827278, by rfl⟩ : syracuseStep 2436371 = 3654557) B3654557
theorem B2436407 : Blo 1080619 2436407 := bstep (se 1 (by rfl) ⟨1827305, by rfl⟩ : syracuseStep 2436407 = 3654611) B3654611
theorem B22261337 : Blo 1080619 22261337 := bstep (se 2 (by rfl) ⟨8348001, by rfl⟩ : syracuseStep 22261337 = 16696003) B16696003
theorem B3649211 : Blo 1080619 3649211 := bstep (se 1 (by rfl) ⟨2736908, by rfl⟩ : syracuseStep 3649211 = 5473817) B5473817
theorem B2437001 : Blo 1080619 2437001 := bstep (se 2 (by rfl) ⟨913875, by rfl⟩ : syracuseStep 2437001 = 1827751) B1827751
theorem B2437217 : Blo 1080619 2437217 := bstep (se 2 (by rfl) ⟨913956, by rfl⟩ : syracuseStep 2437217 = 1827913) B1827913
theorem B3125375 : Blo 1080619 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B16658561 : Blo 1080619 16658561 := bstep (se 2 (by rfl) ⟨6246960, by rfl⟩ : syracuseStep 16658561 = 12493921) B12493921
theorem B9253439 : Blo 1080619 9253439 := bstep (se 1 (by rfl) ⟨6940079, by rfl⟩ : syracuseStep 9253439 = 13880159) B13880159
theorem B8794727 : Blo 1080619 8794727 := bstep (se 1 (by rfl) ⟨6596045, by rfl⟩ : syracuseStep 8794727 = 13192091) B13192091
theorem B2437883 : Blo 1080619 2437883 := bstep (se 1 (by rfl) ⟨1828412, by rfl⟩ : syracuseStep 2437883 = 3656825) B3656825
theorem B2601791 : Blo 1080619 2601791 := bstep (se 1 (by rfl) ⟨1951343, by rfl⟩ : syracuseStep 2601791 = 3902687) B3902687
theorem B2438099 : Blo 1080619 2438099 := bstep (se 1 (by rfl) ⟨1828574, by rfl⟩ : syracuseStep 2438099 = 3657149) B3657149
theorem B2438567 : Blo 1080619 2438567 := bstep (se 1 (by rfl) ⟨1828925, by rfl⟩ : syracuseStep 2438567 = 3657851) B3657851
theorem B2438675 : Blo 1080619 2438675 := bstep (se 1 (by rfl) ⟨1829006, by rfl⟩ : syracuseStep 2438675 = 3658013) B3658013
theorem B2438747 : Blo 1080619 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B4110209 : Blo 1080619 4110209 := bstep (se 2 (by rfl) ⟨1541328, by rfl⟩ : syracuseStep 4110209 = 3082657) B3082657
theorem B22493159 : Blo 1080619 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B18528263 : Blo 1080619 18528263 := bstep (se 1 (by rfl) ⟨13896197, by rfl⟩ : syracuseStep 18528263 = 27792395) B27792395
theorem B16693289 : Blo 1080619 16693289 := bstep (se 2 (by rfl) ⟨6259983, by rfl⟩ : syracuseStep 16693289 = 12519967) B12519967
theorem B4110527 : Blo 1080619 4110527 := bstep (se 1 (by rfl) ⟨3082895, by rfl⟩ : syracuseStep 4110527 = 6165791) B6165791
theorem B2439359 : Blo 1080619 2439359 := bstep (se 1 (by rfl) ⟨1829519, by rfl⟩ : syracuseStep 2439359 = 3659039) B3659039
theorem B8206595 : Blo 1080619 8206595 := bstep (se 1 (by rfl) ⟨6154946, by rfl⟩ : syracuseStep 8206595 = 12309893) B12309893
theorem B5487263 : Blo 1080619 5487263 := bstep (se 1 (by rfl) ⟨4115447, by rfl⟩ : syracuseStep 5487263 = 8230895) B8230895
theorem B8207081 : Blo 1080619 8207081 := bstep (se 2 (by rfl) ⟨3077655, by rfl⟩ : syracuseStep 8207081 = 6155311) B6155311
theorem B50019119 : Blo 1080619 50019119 := bstep (se 1 (by rfl) ⟨37514339, by rfl⟩ : syracuseStep 50019119 = 75028679) B75028679
theorem B4111195 : Blo 1080619 4111195 := bstep (se 1 (by rfl) ⟨3083396, by rfl⟩ : syracuseStep 4111195 = 6166793) B6166793
theorem B3652667 : Blo 1080619 3652667 := bstep (se 1 (by rfl) ⟨2739500, by rfl⟩ : syracuseStep 3652667 = 5479001) B5479001
theorem B1621097 : Blo 1080619 1621097 := bstep (se 2 (by rfl) ⟨607911, by rfl⟩ : syracuseStep 1621097 = 1215823) B1215823
theorem B2735329 : Blo 1080619 2735329 := bstep (se 2 (by rfl) ⟨1025748, by rfl⟩ : syracuseStep 2735329 = 2051497) B2051497
theorem B1621223 : Blo 1080619 1621223 := bstep (se 1 (by rfl) ⟨1215917, by rfl⟩ : syracuseStep 1621223 = 2431835) B2431835
theorem B47398213 : Blo 1080619 47398213 := bstep (se 4 (by rfl) ⟨4443582, by rfl⟩ : syracuseStep 47398213 = 8887165) B8887165
theorem B3652937 : Blo 1080619 3652937 := bstep (se 2 (by rfl) ⟨1369851, by rfl⟩ : syracuseStep 3652937 = 2739703) B2739703
theorem B2309627 : Blo 1080619 2309627 := bstep (se 1 (by rfl) ⟨1732220, by rfl⟩ : syracuseStep 2309627 = 3464441) B3464441
theorem B1621727 : Blo 1080619 1621727 := bstep (se 1 (by rfl) ⟨1216295, by rfl⟩ : syracuseStep 1621727 = 2432591) B2432591
theorem B1621769 : Blo 1080619 1621769 := bstep (se 2 (by rfl) ⟨608163, by rfl⟩ : syracuseStep 1621769 = 1216327) B1216327
theorem B4931399 : Blo 1080619 4931399 := bstep (se 1 (by rfl) ⟨3698549, by rfl⟩ : syracuseStep 4931399 = 7397099) B7397099
theorem B1622207 : Blo 1080619 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B4997369 : Blo 1080619 4997369 := bstep (se 2 (by rfl) ⟨1874013, by rfl⟩ : syracuseStep 4997369 = 3748027) B3748027
theorem B3293597 : Blo 1080619 3293597 := bstep (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) B1235099
theorem B6177181 : Blo 1080619 6177181 := bstep (se 3 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 6177181 = 2316443) B2316443
theorem B1622633 : Blo 1080619 1622633 := bstep (se 2 (by rfl) ⟨608487, by rfl⟩ : syracuseStep 1622633 = 1216975) B1216975
theorem B1622639 : Blo 1080619 1622639 := bstep (se 1 (by rfl) ⟨1216979, by rfl⟩ : syracuseStep 1622639 = 2433959) B2433959
theorem B8209025 : Blo 1080619 8209025 := bstep (se 2 (by rfl) ⟨3078384, by rfl⟩ : syracuseStep 8209025 = 6156769) B6156769
theorem B6505481 : Blo 1080619 6505481 := bstep (se 2 (by rfl) ⟨2439555, by rfl⟩ : syracuseStep 6505481 = 4879111) B4879111
theorem B3654665 : Blo 1080619 3654665 := bstep (se 2 (by rfl) ⟨1370499, by rfl⟩ : syracuseStep 3654665 = 2740999) B2740999
theorem B1623263 : Blo 1080619 1623263 := bstep (se 1 (by rfl) ⟨1217447, by rfl⟩ : syracuseStep 1623263 = 2434895) B2434895
theorem B1623275 : Blo 1080619 1623275 := bstep (se 1 (by rfl) ⟨1217456, by rfl⟩ : syracuseStep 1623275 = 2434913) B2434913
theorem B10405199 : Blo 1080619 10405199 := bstep (se 1 (by rfl) ⟨7803899, by rfl⟩ : syracuseStep 10405199 = 15607799) B15607799
theorem B1951055 : Blo 1080619 1951055 := bstep (se 1 (by rfl) ⟨1463291, by rfl⟩ : syracuseStep 1951055 = 2926583) B2926583
theorem B5490017 : Blo 1080619 5490017 := bstep (se 2 (by rfl) ⟨2058756, by rfl⟩ : syracuseStep 5490017 = 4117513) B4117513
theorem B2737577 : Blo 1080619 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B1623659 : Blo 1080619 1623659 := bstep (se 1 (by rfl) ⟨1217744, by rfl⟩ : syracuseStep 1623659 = 2435489) B2435489
theorem B1623743 : Blo 1080619 1623743 := bstep (se 1 (by rfl) ⟨1217807, by rfl⟩ : syracuseStep 1623743 = 2435615) B2435615
theorem B1623929 : Blo 1080619 1623929 := bstep (se 2 (by rfl) ⟨608973, by rfl⟩ : syracuseStep 1623929 = 1217947) B1217947
theorem B3656015 : Blo 1080619 3656015 := bstep (se 1 (by rfl) ⟨2742011, by rfl⟩ : syracuseStep 3656015 = 5484023) B5484023
theorem B1624679 : Blo 1080619 1624679 := bstep (se 1 (by rfl) ⟨1218509, by rfl⟩ : syracuseStep 1624679 = 2437019) B2437019
theorem B7129715 : Blo 1080619 7129715 := bstep (se 1 (by rfl) ⟨5347286, by rfl⟩ : syracuseStep 7129715 = 10694573) B10694573
theorem B5196449 : Blo 1080619 5196449 := bstep (se 2 (by rfl) ⟨1948668, by rfl⟩ : syracuseStep 5196449 = 3897337) B3897337
theorem B1624871 : Blo 1080619 1624871 := bstep (se 1 (by rfl) ⟨1218653, by rfl⟩ : syracuseStep 1624871 = 2437307) B2437307
theorem B2739035 : Blo 1080619 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B1625195 : Blo 1080619 1625195 := bstep (se 1 (by rfl) ⟨1218896, by rfl⟩ : syracuseStep 1625195 = 2437793) B2437793
theorem B3656879 : Blo 1080619 3656879 := bstep (se 1 (by rfl) ⟨2742659, by rfl⟩ : syracuseStep 3656879 = 5485319) B5485319
theorem B1625435 : Blo 1080619 1625435 := bstep (se 1 (by rfl) ⟨1219076, by rfl⟩ : syracuseStep 1625435 = 2438153) B2438153
theorem B1953115 : Blo 1080619 1953115 := bstep (se 1 (by rfl) ⟨1464836, by rfl⟩ : syracuseStep 1953115 = 2929673) B2929673
theorem B1625465 : Blo 1080619 1625465 := bstep (se 2 (by rfl) ⟨609549, by rfl⟩ : syracuseStep 1625465 = 1219099) B1219099
theorem B1625471 : Blo 1080619 1625471 := bstep (se 1 (by rfl) ⟨1219103, by rfl⟩ : syracuseStep 1625471 = 2438207) B2438207
theorem B4115873 : Blo 1080619 4115873 := bstep (se 2 (by rfl) ⟨1543452, by rfl⟩ : syracuseStep 4115873 = 3086905) B3086905
theorem B20827691 : Blo 1080619 20827691 := bstep (se 1 (by rfl) ⟨15620768, by rfl⟩ : syracuseStep 20827691 = 31241537) B31241537
theorem B2739815 : Blo 1080619 2739815 := bstep (se 1 (by rfl) ⟨2054861, by rfl⟩ : syracuseStep 2739815 = 4109723) B4109723
theorem B3657527 : Blo 1080619 3657527 := bstep (se 1 (by rfl) ⟨2743145, by rfl⟩ : syracuseStep 3657527 = 5486291) B5486291
theorem B1626095 : Blo 1080619 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B1626107 : Blo 1080619 1626107 := bstep (se 1 (by rfl) ⟨1219580, by rfl⟩ : syracuseStep 1626107 = 2439161) B2439161
theorem B6934567 : Blo 1080619 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B1626167 : Blo 1080619 1626167 := bstep (se 1 (by rfl) ⟨1219625, by rfl⟩ : syracuseStep 1626167 = 2439251) B2439251
theorem B1626215 : Blo 1080619 1626215 := bstep (se 1 (by rfl) ⟨1219661, by rfl⟩ : syracuseStep 1626215 = 2439323) B2439323
theorem B1953895 : Blo 1080619 1953895 := bstep (se 1 (by rfl) ⟨1465421, by rfl⟩ : syracuseStep 1953895 = 2930843) B2930843
theorem B1626287 : Blo 1080619 1626287 := bstep (se 1 (by rfl) ⟨1219715, by rfl⟩ : syracuseStep 1626287 = 2439431) B2439431
theorem B1626491 : Blo 1080619 1626491 := bstep (se 1 (by rfl) ⟨1219868, by rfl⟩ : syracuseStep 1626491 = 2439737) B2439737
theorem B2314889 : Blo 1080619 2314889 := bstep (se 2 (by rfl) ⟨868083, by rfl⟩ : syracuseStep 2314889 = 1736167) B1736167
theorem B1626761 : Blo 1080619 1626761 := bstep (se 2 (by rfl) ⟨610035, by rfl⟩ : syracuseStep 1626761 = 1220071) B1220071
theorem B2052955 : Blo 1080619 2052955 := bstep (se 1 (by rfl) ⟨1539716, by rfl⟩ : syracuseStep 2052955 = 3079433) B3079433
theorem B3658607 : Blo 1080619 3658607 := bstep (se 1 (by rfl) ⟨2743955, by rfl⟩ : syracuseStep 3658607 = 5487911) B5487911
theorem B1823647 : Blo 1080619 1823647 := bstep (se 1 (by rfl) ⟨1367735, by rfl⟩ : syracuseStep 1823647 = 2735471) B2735471
theorem B9262187 : Blo 1080619 9262187 := bstep (se 1 (by rfl) ⟨6946640, by rfl⟩ : syracuseStep 9262187 = 13893281) B13893281
theorem B2053487 : Blo 1080619 2053487 := bstep (se 1 (by rfl) ⟨1540115, by rfl⟩ : syracuseStep 2053487 = 3080231) B3080231
theorem B4117999 : Blo 1080619 4117999 := bstep (se 1 (by rfl) ⟨3088499, by rfl⟩ : syracuseStep 4117999 = 6176999) B6176999
theorem B3462671 : Blo 1080619 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B86562553 : Blo 1080619 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B2054011 : Blo 1080619 2054011 := bstep (se 1 (by rfl) ⟨1540508, by rfl⟩ : syracuseStep 2054011 = 3081017) B3081017
theorem B8345729 : Blo 1080619 8345729 := bstep (se 2 (by rfl) ⟨3129648, by rfl⟩ : syracuseStep 8345729 = 6259297) B6259297
theorem B2054497 : Blo 1080619 2054497 := bstep (se 2 (by rfl) ⟨770436, by rfl⟩ : syracuseStep 2054497 = 1540873) B1540873
theorem B18471401 : Blo 1080619 18471401 := bstep (se 2 (by rfl) ⟨6926775, by rfl⟩ : syracuseStep 18471401 = 13853551) B13853551
theorem B2742761 : Blo 1080619 2742761 := bstep (se 2 (by rfl) ⟨1028535, by rfl⟩ : syracuseStep 2742761 = 2057071) B2057071
theorem B18995735 : Blo 1080619 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B2054983 : Blo 1080619 2054983 := bstep (se 1 (by rfl) ⟨1541237, by rfl⟩ : syracuseStep 2054983 = 3082475) B3082475
theorem B2055955 : Blo 1080619 2055955 := bstep (se 1 (by rfl) ⟨1541966, by rfl⟩ : syracuseStep 2055955 = 3083933) B3083933
theorem B15621923 : Blo 1080619 15621923 := bstep (se 1 (by rfl) ⟨11716442, by rfl⟩ : syracuseStep 15621923 = 23432885) B23432885
theorem B1826671 : Blo 1080619 1826671 := bstep (se 1 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 1826671 = 2740007) B2740007
theorem B2744219 : Blo 1080619 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B2056585 : Blo 1080619 2056585 := bstep (se 2 (by rfl) ⟨771219, by rfl⟩ : syracuseStep 2056585 = 1542439) B1542439
theorem B18506393 : Blo 1080619 18506393 := bstep (se 2 (by rfl) ⟨6939897, by rfl⟩ : syracuseStep 18506393 = 13879795) B13879795
theorem B2744999 : Blo 1080619 2744999 := bstep (se 1 (by rfl) ⟨2058749, by rfl⟩ : syracuseStep 2744999 = 4117499) B4117499
theorem B1827535 : Blo 1080619 1827535 := bstep (se 1 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 1827535 = 2741303) B2741303
theorem B2745323 : Blo 1080619 2745323 := bstep (se 1 (by rfl) ⟨2058992, by rfl⟩ : syracuseStep 2745323 = 4117985) B4117985
theorem B1828379 : Blo 1080619 1828379 := bstep (se 1 (by rfl) ⟨1371284, by rfl⟩ : syracuseStep 1828379 = 2742569) B2742569
theorem B4384327 : Blo 1080619 4384327 := bstep (se 1 (by rfl) ⟨3288245, by rfl⟩ : syracuseStep 4384327 = 6576491) B6576491
theorem B4384651 : Blo 1080619 4384651 := bstep (se 1 (by rfl) ⟨3288488, by rfl⟩ : syracuseStep 4384651 = 6576977) B6576977
theorem B1828831 : Blo 1080619 1828831 := bstep (se 1 (by rfl) ⟨1371623, by rfl⟩ : syracuseStep 1828831 = 2743247) B2743247
theorem B3467387 : Blo 1080619 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B19753105 : Blo 1080619 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B6580673 : Blo 1080619 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B2059015 : Blo 1080619 2059015 := bstep (se 1 (by rfl) ⟨1544261, by rfl⟩ : syracuseStep 2059015 = 3088523) B3088523
theorem B65072267 : Blo 1080619 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B10415465 : Blo 1080619 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B1732681 : Blo 1080619 1732681 := bstep (se 2 (by rfl) ⟨649755, by rfl⟩ : syracuseStep 1732681 = 1299511) B1299511
theorem B5861639 : Blo 1080619 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B35648363 : Blo 1080619 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B17527697 : Blo 1080619 17527697 := bstep (se 2 (by rfl) ⟨6572886, by rfl⟩ : syracuseStep 17527697 = 13145773) B13145773
theorem B14054573 : Blo 1080619 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B4617425 : Blo 1080619 4617425 := bstep (se 2 (by rfl) ⟨1731534, by rfl⟩ : syracuseStep 4617425 = 3463069) B3463069
theorem B3470759 : Blo 1080619 3470759 := bstep (se 1 (by rfl) ⟨2603069, by rfl⟩ : syracuseStep 3470759 = 5206139) B5206139
theorem B13858883 : Blo 1080619 13858883 := bstep (se 1 (by rfl) ⟨10394162, by rfl⟩ : syracuseStep 13858883 = 20788325) B20788325
theorem B8223119 : Blo 1080619 8223119 := bstep (se 1 (by rfl) ⟨6167339, by rfl⟩ : syracuseStep 8223119 = 12334679) B12334679
theorem B4619389 : Blo 1080619 4619389 := bstep (se 3 (by rfl) ⟨866135, by rfl⟩ : syracuseStep 4619389 = 1732271) B1732271
theorem B6946049 : Blo 1080619 6946049 := bstep (se 2 (by rfl) ⟨2604768, by rfl⟩ : syracuseStep 6946049 = 5209537) B5209537
theorem B1080647 : Blo 1080619 1080647 := bstep (se 1 (by rfl) ⟨810485, by rfl⟩ : syracuseStep 1080647 = 1620971) B1620971
theorem B1080783 : Blo 1080619 1080783 := bstep (se 1 (by rfl) ⟨810587, by rfl⟩ : syracuseStep 1080783 = 1621175) B1621175
theorem B1080943 : Blo 1080619 1080943 := bstep (se 1 (by rfl) ⟨810707, by rfl⟩ : syracuseStep 1080943 = 1621415) B1621415
theorem B1080999 : Blo 1080619 1080999 := bstep (se 1 (by rfl) ⟨810749, by rfl⟩ : syracuseStep 1080999 = 1621499) B1621499
theorem B1081063 : Blo 1080619 1081063 := bstep (se 1 (by rfl) ⟨810797, by rfl⟩ : syracuseStep 1081063 = 1621595) B1621595
theorem B1081119 : Blo 1080619 1081119 := bstep (se 1 (by rfl) ⟨810839, by rfl⟩ : syracuseStep 1081119 = 1621679) B1621679
theorem B3080015 : Blo 1080619 3080015 := bstep (se 1 (by rfl) ⟨2310011, by rfl⟩ : syracuseStep 3080015 = 4620023) B4620023
theorem B1081199 : Blo 1080619 1081199 := bstep (se 1 (by rfl) ⟨810899, by rfl⟩ : syracuseStep 1081199 = 1621799) B1621799
theorem B1081255 : Blo 1080619 1081255 := bstep (se 1 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 1081255 = 1621883) B1621883
theorem B1081471 : Blo 1080619 1081471 := bstep (se 1 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 1081471 = 1622207) B1622207
theorem B2195731 : Blo 1080619 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B9240965 : Blo 1080619 9240965 := bstep (se 4 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 9240965 = 1732681) B1732681
theorem B1081755 : Blo 1080619 1081755 := bstep (se 1 (by rfl) ⟨811316, by rfl⟩ : syracuseStep 1081755 = 1622633) B1622633
theorem B1081759 : Blo 1080619 1081759 := bstep (se 1 (by rfl) ⟨811319, by rfl⟩ : syracuseStep 1081759 = 1622639) B1622639
theorem B5472683 : Blo 1080619 5472683 := bstep (se 1 (by rfl) ⟨4104512, by rfl⟩ : syracuseStep 5472683 = 8209025) B8209025
theorem B3080891 : Blo 1080619 3080891 := bstep (se 1 (by rfl) ⟨2310668, by rfl⟩ : syracuseStep 3080891 = 4621337) B4621337
theorem B1082175 : Blo 1080619 1082175 := bstep (se 1 (by rfl) ⟨811631, by rfl⟩ : syracuseStep 1082175 = 1623263) B1623263
theorem B1082183 : Blo 1080619 1082183 := bstep (se 1 (by rfl) ⟨811637, by rfl⟩ : syracuseStep 1082183 = 1623275) B1623275
theorem B1082439 : Blo 1080619 1082439 := bstep (se 1 (by rfl) ⟨811829, by rfl⟩ : syracuseStep 1082439 = 1623659) B1623659
theorem B1082495 : Blo 1080619 1082495 := bstep (se 1 (by rfl) ⟨811871, by rfl⟩ : syracuseStep 1082495 = 1623743) B1623743
theorem B1082619 : Blo 1080619 1082619 := bstep (se 1 (by rfl) ⟨811964, by rfl⟩ : syracuseStep 1082619 = 1623929) B1623929
theorem B1083119 : Blo 1080619 1083119 := bstep (se 1 (by rfl) ⟨812339, by rfl⟩ : syracuseStep 1083119 = 1624679) B1624679
theorem B1083247 : Blo 1080619 1083247 := bstep (se 1 (by rfl) ⟨812435, by rfl⟩ : syracuseStep 1083247 = 1624871) B1624871
theorem B1083463 : Blo 1080619 1083463 := bstep (se 1 (by rfl) ⟨812597, by rfl⟩ : syracuseStep 1083463 = 1625195) B1625195
theorem B12323015 : Blo 1080619 12323015 := bstep (se 1 (by rfl) ⟨9242261, by rfl⟩ : syracuseStep 12323015 = 18484523) B18484523
theorem B1083623 : Blo 1080619 1083623 := bstep (se 1 (by rfl) ⟨812717, by rfl⟩ : syracuseStep 1083623 = 1625435) B1625435
theorem B1083643 : Blo 1080619 1083643 := bstep (se 1 (by rfl) ⟨812732, by rfl⟩ : syracuseStep 1083643 = 1625465) B1625465
theorem B1083647 : Blo 1080619 1083647 := bstep (se 1 (by rfl) ⟨812735, by rfl⟩ : syracuseStep 1083647 = 1625471) B1625471
theorem B1084063 : Blo 1080619 1084063 := bstep (se 1 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 1084063 = 1626095) B1626095
theorem B1084071 : Blo 1080619 1084071 := bstep (se 1 (by rfl) ⟨813053, by rfl⟩ : syracuseStep 1084071 = 1626107) B1626107
theorem B1084111 : Blo 1080619 1084111 := bstep (se 1 (by rfl) ⟨813083, by rfl⟩ : syracuseStep 1084111 = 1626167) B1626167
theorem B1084143 : Blo 1080619 1084143 := bstep (se 1 (by rfl) ⟨813107, by rfl⟩ : syracuseStep 1084143 = 1626215) B1626215
theorem B1084191 : Blo 1080619 1084191 := bstep (se 1 (by rfl) ⟨813143, by rfl⟩ : syracuseStep 1084191 = 1626287) B1626287
theorem B1084327 : Blo 1080619 1084327 := bstep (se 1 (by rfl) ⟨813245, by rfl⟩ : syracuseStep 1084327 = 1626491) B1626491
theorem B1543259 : Blo 1080619 1543259 := bstep (se 1 (by rfl) ⟨1157444, by rfl⟩ : syracuseStep 1543259 = 2314889) B2314889
theorem B1084507 : Blo 1080619 1084507 := bstep (se 1 (by rfl) ⟨813380, by rfl⟩ : syracuseStep 1084507 = 1626761) B1626761
theorem B9246089 : Blo 1080619 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B3085739 : Blo 1080619 3085739 := bstep (se 1 (by rfl) ⟨2314304, by rfl⟩ : syracuseStep 3085739 = 4628609) B4628609
theorem B1218919 : Blo 1080619 1218919 := bstep (se 1 (by rfl) ⟨914189, by rfl⟩ : syracuseStep 1218919 = 1828379) B1828379
theorem B15604163 : Blo 1080619 15604163 := bstep (se 1 (by rfl) ⟨11703122, by rfl⟩ : syracuseStep 15604163 = 23406245) B23406245
theorem B2431439 : Blo 1080619 2431439 := bstep (se 1 (by rfl) ⟨1823579, by rfl⟩ : syracuseStep 2431439 = 3647159) B3647159
theorem B2431529 : Blo 1080619 2431529 := bstep (se 2 (by rfl) ⟨911823, by rfl⟩ : syracuseStep 2431529 = 1823647) B1823647
theorem B19012573 : Blo 1080619 19012573 := bstep (se 3 (by rfl) ⟨3564857, by rfl⟩ : syracuseStep 19012573 = 7129715) B7129715
theorem B53485067 : Blo 1080619 53485067 := bstep (se 1 (by rfl) ⟨40113800, by rfl⟩ : syracuseStep 53485067 = 80227601) B80227601
theorem B115416737 : Blo 1080619 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B2432807 : Blo 1080619 2432807 := bstep (se 1 (by rfl) ⟨1824605, by rfl⟩ : syracuseStep 2432807 = 3649211) B3649211
theorem B3907759 : Blo 1080619 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B6168959 : Blo 1080619 6168959 := bstep (se 1 (by rfl) ⟨4626719, by rfl⟩ : syracuseStep 6168959 = 9253439) B9253439
theorem B23765575 : Blo 1080619 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B5481593 : Blo 1080619 5481593 := bstep (se 2 (by rfl) ⟨2055597, by rfl⟩ : syracuseStep 5481593 = 4111195) B4111195
theorem B5482079 : Blo 1080619 5482079 := bstep (se 1 (by rfl) ⟨4111559, by rfl⟩ : syracuseStep 5482079 = 8223119) B8223119
theorem B3647105 : Blo 1080619 3647105 := bstep (se 2 (by rfl) ⟨1367664, by rfl⟩ : syracuseStep 3647105 = 2735329) B2735329
theorem B2435111 : Blo 1080619 2435111 := bstep (se 1 (by rfl) ⟨1826333, by rfl⟩ : syracuseStep 2435111 = 3652667) B3652667
theorem B4630699 : Blo 1080619 4630699 := bstep (se 1 (by rfl) ⟨3473024, by rfl⟩ : syracuseStep 4630699 = 6946049) B6946049
theorem B13150397 : Blo 1080619 13150397 := bstep (se 3 (by rfl) ⟨2465699, by rfl⟩ : syracuseStep 13150397 = 4931399) B4931399
theorem B2435291 : Blo 1080619 2435291 := bstep (se 1 (by rfl) ⟨1826468, by rfl⟩ : syracuseStep 2435291 = 3652937) B3652937
theorem B2435561 : Blo 1080619 2435561 := bstep (se 2 (by rfl) ⟨913335, by rfl⟩ : syracuseStep 2435561 = 1826671) B1826671
theorem B7908295 : Blo 1080619 7908295 := bstep (se 1 (by rfl) ⟨5931221, by rfl⟩ : syracuseStep 7908295 = 11862443) B11862443
theorem B8236241 : Blo 1080619 8236241 := bstep (se 2 (by rfl) ⟨3088590, by rfl⟩ : syracuseStep 8236241 = 6177181) B6177181
theorem B4336987 : Blo 1080619 4336987 := bstep (se 1 (by rfl) ⟨3252740, by rfl⟩ : syracuseStep 4336987 = 6505481) B6505481
theorem B2436443 : Blo 1080619 2436443 := bstep (se 1 (by rfl) ⟨1827332, by rfl⟩ : syracuseStep 2436443 = 3654665) B3654665
theorem B3649103 : Blo 1080619 3649103 := bstep (se 1 (by rfl) ⟨2736827, by rfl⟩ : syracuseStep 3649103 = 5473655) B5473655
theorem B2436713 : Blo 1080619 2436713 := bstep (se 2 (by rfl) ⟨913767, by rfl⟩ : syracuseStep 2436713 = 1827535) B1827535
theorem B6663943 : Blo 1080619 6663943 := bstep (se 1 (by rfl) ⟨4997957, by rfl⟩ : syracuseStep 6663943 = 9995915) B9995915
theorem B3649643 : Blo 1080619 3649643 := bstep (se 1 (by rfl) ⟨2737232, by rfl⟩ : syracuseStep 3649643 = 5474465) B5474465
theorem B5484671 : Blo 1080619 5484671 := bstep (se 1 (by rfl) ⟨4113503, by rfl⟩ : syracuseStep 5484671 = 8227007) B8227007
theorem B2437343 : Blo 1080619 2437343 := bstep (se 1 (by rfl) ⟨1828007, by rfl⟩ : syracuseStep 2437343 = 3656015) B3656015
theorem B4108751 : Blo 1080619 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B5845769 : Blo 1080619 5845769 := bstep (se 2 (by rfl) ⟨2192163, by rfl⟩ : syracuseStep 5845769 = 4384327) B4384327
theorem B2437919 : Blo 1080619 2437919 := bstep (se 1 (by rfl) ⟨1828439, by rfl⟩ : syracuseStep 2437919 = 3656879) B3656879
theorem B5846201 : Blo 1080619 5846201 := bstep (se 2 (by rfl) ⟨2192325, by rfl⟩ : syracuseStep 5846201 = 4384651) B4384651
theorem B2438351 : Blo 1080619 2438351 := bstep (se 1 (by rfl) ⟨1828763, by rfl⟩ : syracuseStep 2438351 = 3657527) B3657527
theorem B2438441 : Blo 1080619 2438441 := bstep (se 2 (by rfl) ⟨914415, by rfl⟩ : syracuseStep 2438441 = 1828831) B1828831
theorem B15611777 : Blo 1080619 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B2439071 : Blo 1080619 2439071 := bstep (se 1 (by rfl) ⟨1829303, by rfl⟩ : syracuseStep 2439071 = 3658607) B3658607
theorem B6174791 : Blo 1080619 6174791 := bstep (se 1 (by rfl) ⟨4631093, by rfl⟩ : syracuseStep 6174791 = 9262187) B9262187
theorem B2308447 : Blo 1080619 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B1948151 : Blo 1080619 1948151 := bstep (se 1 (by rfl) ⟨1461113, by rfl⟩ : syracuseStep 1948151 = 2922227) B2922227
theorem B3652127 : Blo 1080619 3652127 := bstep (se 1 (by rfl) ⟨2739095, by rfl⟩ : syracuseStep 3652127 = 5478191) B5478191
theorem B12663823 : Blo 1080619 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B1621199 : Blo 1080619 1621199 := bstep (se 1 (by rfl) ⟨1215899, by rfl⟩ : syracuseStep 1621199 = 2431799) B2431799
theorem B1621289 : Blo 1080619 1621289 := bstep (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) B1215967
theorem B1621319 : Blo 1080619 1621319 := bstep (se 1 (by rfl) ⟨1215989, by rfl⟩ : syracuseStep 1621319 = 2431979) B2431979
theorem B1097371 : Blo 1080619 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B4112167 : Blo 1080619 4112167 := bstep (se 1 (by rfl) ⟨3084125, by rfl⟩ : syracuseStep 4112167 = 6168251) B6168251
theorem B1621919 : Blo 1080619 1621919 := bstep (se 1 (by rfl) ⟨1216439, by rfl⟩ : syracuseStep 1621919 = 2432879) B2432879
theorem B1622009 : Blo 1080619 1622009 := bstep (se 2 (by rfl) ⟨608253, by rfl⟩ : syracuseStep 1622009 = 1216507) B1216507
theorem B1622153 : Blo 1080619 1622153 := bstep (se 2 (by rfl) ⟨608307, by rfl⟩ : syracuseStep 1622153 = 1216615) B1216615
theorem B2605193 : Blo 1080619 2605193 := bstep (se 2 (by rfl) ⟨976947, by rfl⟩ : syracuseStep 2605193 = 1953895) B1953895
theorem B1622249 : Blo 1080619 1622249 := bstep (se 2 (by rfl) ⟨608343, by rfl⟩ : syracuseStep 1622249 = 1216687) B1216687
theorem B1622375 : Blo 1080619 1622375 := bstep (se 1 (by rfl) ⟨1216781, by rfl⟩ : syracuseStep 1622375 = 2433563) B2433563
theorem B12337595 : Blo 1080619 12337595 := bstep (se 1 (by rfl) ⟨9253196, by rfl⟩ : syracuseStep 12337595 = 18506393) B18506393
theorem B1622495 : Blo 1080619 1622495 := bstep (se 1 (by rfl) ⟨1216871, by rfl⟩ : syracuseStep 1622495 = 2433743) B2433743
theorem B4112927 : Blo 1080619 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B28099169 : Blo 1080619 28099169 := bstep (se 2 (by rfl) ⟨10537188, by rfl⟩ : syracuseStep 28099169 = 21074377) B21074377
theorem B1622747 : Blo 1080619 1622747 := bstep (se 1 (by rfl) ⟨1217060, by rfl⟩ : syracuseStep 1622747 = 2434121) B2434121
theorem B4113139 : Blo 1080619 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B2737273 : Blo 1080619 2737273 := bstep (se 2 (by rfl) ⟨1026477, by rfl⟩ : syracuseStep 2737273 = 2052955) B2052955
theorem B1623161 : Blo 1080619 1623161 := bstep (se 2 (by rfl) ⟨608685, by rfl⟩ : syracuseStep 1623161 = 1217371) B1217371
theorem B6931595 : Blo 1080619 6931595 := bstep (se 1 (by rfl) ⟨5198696, by rfl⟩ : syracuseStep 6931595 = 10397393) B10397393
theorem B1623359 : Blo 1080619 1623359 := bstep (se 1 (by rfl) ⟨1217519, by rfl⟩ : syracuseStep 1623359 = 2435039) B2435039
theorem B2311591 : Blo 1080619 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B35178137 : Blo 1080619 35178137 := bstep (se 2 (by rfl) ⟨13191801, by rfl⟩ : syracuseStep 35178137 = 26383603) B26383603
theorem B1624031 : Blo 1080619 1624031 := bstep (se 1 (by rfl) ⟨1218023, by rfl⟩ : syracuseStep 1624031 = 2436047) B2436047
theorem B5490665 : Blo 1080619 5490665 := bstep (se 2 (by rfl) ⟨2058999, by rfl⟩ : syracuseStep 5490665 = 4117999) B4117999
theorem B1624091 : Blo 1080619 1624091 := bstep (se 1 (by rfl) ⟨1218068, by rfl⟩ : syracuseStep 1624091 = 2436137) B2436137
theorem B1624247 : Blo 1080619 1624247 := bstep (se 1 (by rfl) ⟨1218185, by rfl⟩ : syracuseStep 1624247 = 2436371) B2436371
theorem B1624271 : Blo 1080619 1624271 := bstep (se 1 (by rfl) ⟨1218203, by rfl⟩ : syracuseStep 1624271 = 2436407) B2436407
theorem B2738681 : Blo 1080619 2738681 := bstep (se 2 (by rfl) ⟨1027005, by rfl⟩ : syracuseStep 2738681 = 2054011) B2054011
theorem B1624667 : Blo 1080619 1624667 := bstep (se 1 (by rfl) ⟨1218500, by rfl⟩ : syracuseStep 1624667 = 2437001) B2437001
theorem B1624811 : Blo 1080619 1624811 := bstep (se 1 (by rfl) ⟨1218608, by rfl⟩ : syracuseStep 1624811 = 2437217) B2437217
theorem B2083583 : Blo 1080619 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B1624841 : Blo 1080619 1624841 := bstep (se 2 (by rfl) ⟨609315, by rfl⟩ : syracuseStep 1624841 = 1218631) B1218631
theorem B2739329 : Blo 1080619 2739329 := bstep (se 2 (by rfl) ⟨1027248, by rfl⟩ : syracuseStep 2739329 = 2054497) B2054497
theorem B1625255 : Blo 1080619 1625255 := bstep (se 1 (by rfl) ⟨1218941, by rfl⟩ : syracuseStep 1625255 = 2437883) B2437883
theorem B11685131 : Blo 1080619 11685131 := bstep (se 1 (by rfl) ⟨8763848, by rfl⟩ : syracuseStep 11685131 = 17527697) B17527697
theorem B1625399 : Blo 1080619 1625399 := bstep (se 1 (by rfl) ⟨1219049, by rfl⟩ : syracuseStep 1625399 = 2438099) B2438099
theorem B4116041 : Blo 1080619 4116041 := bstep (se 2 (by rfl) ⟨1543515, by rfl⟩ : syracuseStep 4116041 = 3087031) B3087031
theorem B2313839 : Blo 1080619 2313839 := bstep (se 1 (by rfl) ⟨1735379, by rfl⟩ : syracuseStep 2313839 = 3470759) B3470759
theorem B1625711 : Blo 1080619 1625711 := bstep (se 1 (by rfl) ⟨1219283, by rfl⟩ : syracuseStep 1625711 = 2438567) B2438567
theorem B1625783 : Blo 1080619 1625783 := bstep (se 1 (by rfl) ⟨1219337, by rfl⟩ : syracuseStep 1625783 = 2438675) B2438675
theorem B1625831 : Blo 1080619 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B2739977 : Blo 1080619 2739977 := bstep (se 2 (by rfl) ⟨1027491, by rfl⟩ : syracuseStep 2739977 = 2054983) B2054983
theorem B1625993 : Blo 1080619 1625993 := bstep (se 2 (by rfl) ⟨609747, by rfl⟩ : syracuseStep 1625993 = 1219495) B1219495
theorem B2740139 : Blo 1080619 2740139 := bstep (se 1 (by rfl) ⟨2055104, by rfl⟩ : syracuseStep 2740139 = 4110209) B4110209
theorem B14995439 : Blo 1080619 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B11128859 : Blo 1080619 11128859 := bstep (se 1 (by rfl) ⟨8346644, by rfl⟩ : syracuseStep 11128859 = 16693289) B16693289
theorem B1626233 : Blo 1080619 1626233 := bstep (se 2 (by rfl) ⟨609837, by rfl⟩ : syracuseStep 1626233 = 1219675) B1219675
theorem B2740351 : Blo 1080619 2740351 := bstep (se 1 (by rfl) ⟨2055263, by rfl⟩ : syracuseStep 2740351 = 4110527) B4110527
theorem B1626239 : Blo 1080619 1626239 := bstep (se 1 (by rfl) ⟨1219679, by rfl⟩ : syracuseStep 1626239 = 2439359) B2439359
theorem B63197617 : Blo 1080619 63197617 := bstep (se 2 (by rfl) ⟨23699106, by rfl⟩ : syracuseStep 63197617 = 47398213) B47398213
theorem B3658175 : Blo 1080619 3658175 := bstep (se 1 (by rfl) ⟨2743631, by rfl⟩ : syracuseStep 3658175 = 5487263) B5487263
theorem B33346079 : Blo 1080619 33346079 := bstep (se 1 (by rfl) ⟨25009559, by rfl⟩ : syracuseStep 33346079 = 50019119) B50019119
theorem B2741273 : Blo 1080619 2741273 := bstep (se 2 (by rfl) ⟨1027977, by rfl⟩ : syracuseStep 2741273 = 2055955) B2055955
theorem B2053343 : Blo 1080619 2053343 := bstep (se 1 (by rfl) ⟨1540007, by rfl⟩ : syracuseStep 2053343 = 3080015) B3080015
theorem B3331579 : Blo 1080619 3331579 := bstep (se 1 (by rfl) ⟨2498684, by rfl⟩ : syracuseStep 3331579 = 4997369) B4997369
theorem B2053775 : Blo 1080619 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B2315999 : Blo 1080619 2315999 := bstep (se 1 (by rfl) ⟨1736999, by rfl⟩ : syracuseStep 2315999 = 3473999) B3473999
theorem B26367839 : Blo 1080619 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B2742113 : Blo 1080619 2742113 := bstep (se 2 (by rfl) ⟨1028292, by rfl⟩ : syracuseStep 2742113 = 2056585) B2056585
theorem B6936799 : Blo 1080619 6936799 := bstep (se 1 (by rfl) ⟨5202599, by rfl⟩ : syracuseStep 6936799 = 10405199) B10405199
theorem B1300703 : Blo 1080619 1300703 := bstep (se 1 (by rfl) ⟨975527, by rfl⟩ : syracuseStep 1300703 = 1951055) B1951055
theorem B3660011 : Blo 1080619 3660011 := bstep (se 1 (by rfl) ⟨2745008, by rfl⟩ : syracuseStep 3660011 = 5490017) B5490017
theorem B1825051 : Blo 1080619 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B2775647 : Blo 1080619 2775647 := bstep (se 1 (by rfl) ⟨2081735, by rfl⟩ : syracuseStep 2775647 = 4163471) B4163471
theorem B3464299 : Blo 1080619 3464299 := bstep (se 1 (by rfl) ⟨2598224, by rfl⟩ : syracuseStep 3464299 = 5196449) B5196449
theorem B1826023 : Blo 1080619 1826023 := bstep (se 1 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 1826023 = 2739035) B2739035
theorem B2743915 : Blo 1080619 2743915 := bstep (se 1 (by rfl) ⟨2057936, by rfl⟩ : syracuseStep 2743915 = 4115873) B4115873
theorem B13885127 : Blo 1080619 13885127 := bstep (se 1 (by rfl) ⟨10413845, by rfl⟩ : syracuseStep 13885127 = 20827691) B20827691
theorem B1826543 : Blo 1080619 1826543 := bstep (se 1 (by rfl) ⟨1369907, by rfl⟩ : syracuseStep 1826543 = 2739815) B2739815
theorem B26337473 : Blo 1080619 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B37478861 : Blo 1080619 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B59269819 : Blo 1080619 59269819 := bstep (se 1 (by rfl) ⟨44452364, by rfl⟩ : syracuseStep 59269819 = 88904729) B88904729
theorem B1368991 : Blo 1080619 1368991 := bstep (se 1 (by rfl) ⟨1026743, by rfl⟩ : syracuseStep 1368991 = 2053487) B2053487
theorem B2745353 : Blo 1080619 2745353 := bstep (se 2 (by rfl) ⟨1029507, by rfl⟩ : syracuseStep 2745353 = 2059015) B2059015
theorem B5563819 : Blo 1080619 5563819 := bstep (se 1 (by rfl) ⟨4172864, by rfl⟩ : syracuseStep 5563819 = 8345729) B8345729
theorem B12314267 : Blo 1080619 12314267 := bstep (se 1 (by rfl) ⟨9235700, by rfl⟩ : syracuseStep 12314267 = 18471401) B18471401
theorem B1828507 : Blo 1080619 1828507 := bstep (se 1 (by rfl) ⟨1371380, by rfl⟩ : syracuseStep 1828507 = 2742761) B2742761
theorem B5859155 : Blo 1080619 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B10414615 : Blo 1080619 10414615 := bstep (se 1 (by rfl) ⟨7810961, by rfl⟩ : syracuseStep 10414615 = 15621923) B15621923
theorem B1829479 : Blo 1080619 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B1731451 : Blo 1080619 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B8678339 : Blo 1080619 8678339 := bstep (se 1 (by rfl) ⟨6508754, by rfl⟩ : syracuseStep 8678339 = 13017509) B13017509
theorem B1829999 : Blo 1080619 1829999 := bstep (se 1 (by rfl) ⟨1372499, by rfl⟩ : syracuseStep 1829999 = 2744999) B2744999
theorem B1830215 : Blo 1080619 1830215 := bstep (se 1 (by rfl) ⟨1372661, by rfl⟩ : syracuseStep 1830215 = 2745323) B2745323
theorem B11694131 : Blo 1080619 11694131 := bstep (se 1 (by rfl) ⟨8770598, by rfl⟩ : syracuseStep 11694131 = 17541197) B17541197
theorem B2191579 : Blo 1080619 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B4387115 : Blo 1080619 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B26309063 : Blo 1080619 26309063 := bstep (se 1 (by rfl) ⟨19731797, by rfl⟩ : syracuseStep 26309063 = 39463595) B39463595
theorem B10416613 : Blo 1080619 10416613 := bstep (se 4 (by rfl) ⟨976557, by rfl⟩ : syracuseStep 10416613 = 1953115) B1953115
theorem B43381511 : Blo 1080619 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B6943643 : Blo 1080619 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B14840891 : Blo 1080619 14840891 := bstep (se 1 (by rfl) ⟨11130668, by rfl⟩ : syracuseStep 14840891 = 22261337) B22261337
theorem B12350717 : Blo 1080619 12350717 := bstep (se 3 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 12350717 = 4631519) B4631519
theorem B11105707 : Blo 1080619 11105707 := bstep (se 1 (by rfl) ⟨8329280, by rfl⟩ : syracuseStep 11105707 = 16658561) B16658561
theorem B5863151 : Blo 1080619 5863151 := bstep (se 1 (by rfl) ⟨4397363, by rfl⟩ : syracuseStep 5863151 = 8794727) B8794727
theorem B1734527 : Blo 1080619 1734527 := bstep (se 1 (by rfl) ⟨1300895, by rfl⟩ : syracuseStep 1734527 = 2601791) B2601791
theorem B3078283 : Blo 1080619 3078283 := bstep (se 1 (by rfl) ⟨2308712, by rfl⟩ : syracuseStep 3078283 = 4617425) B4617425
theorem B12352175 : Blo 1080619 12352175 := bstep (se 1 (by rfl) ⟨9264131, by rfl⟩ : syracuseStep 12352175 = 18528263) B18528263
theorem B9239255 : Blo 1080619 9239255 := bstep (se 1 (by rfl) ⟨6929441, by rfl⟩ : syracuseStep 9239255 = 13858883) B13858883
theorem B6159185 : Blo 1080619 6159185 := bstep (se 2 (by rfl) ⟨2309694, by rfl⟩ : syracuseStep 6159185 = 4619389) B4619389
theorem B5471063 : Blo 1080619 5471063 := bstep (se 1 (by rfl) ⟨4103297, by rfl⟩ : syracuseStep 5471063 = 8206595) B8206595
theorem B28146653 : Blo 1080619 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B5471387 : Blo 1080619 5471387 := bstep (se 1 (by rfl) ⟨4103540, by rfl⟩ : syracuseStep 5471387 = 8207081) B8207081
theorem B1080731 : Blo 1080619 1080731 := bstep (se 1 (by rfl) ⟨810548, by rfl⟩ : syracuseStep 1080731 = 1621097) B1621097
theorem B1080815 : Blo 1080619 1080815 := bstep (se 1 (by rfl) ⟨810611, by rfl⟩ : syracuseStep 1080815 = 1621223) B1621223
theorem B1539751 : Blo 1080619 1539751 := bstep (se 1 (by rfl) ⟨1154813, by rfl⟩ : syracuseStep 1539751 = 2309627) B2309627
theorem B1081151 : Blo 1080619 1081151 := bstep (se 1 (by rfl) ⟨810863, by rfl⟩ : syracuseStep 1081151 = 1621727) B1621727
theorem B1081179 : Blo 1080619 1081179 := bstep (se 1 (by rfl) ⟨810884, by rfl⟩ : syracuseStep 1081179 = 1621769) B1621769
theorem B1081435 : Blo 1080619 1081435 := bstep (se 1 (by rfl) ⟨811076, by rfl⟩ : syracuseStep 1081435 = 1622153) B1622153
theorem B1736795 : Blo 1080619 1736795 := bstep (se 1 (by rfl) ⟨1302596, by rfl⟩ : syracuseStep 1736795 = 2605193) B2605193
theorem B1081499 : Blo 1080619 1081499 := bstep (se 1 (by rfl) ⟨811124, by rfl⟩ : syracuseStep 1081499 = 1622249) B1622249
theorem B5210345 : Blo 1080619 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B1081583 : Blo 1080619 1081583 := bstep (se 1 (by rfl) ⟨811187, by rfl⟩ : syracuseStep 1081583 = 1622375) B1622375
theorem B6160643 : Blo 1080619 6160643 := bstep (se 1 (by rfl) ⟨4620482, by rfl⟩ : syracuseStep 6160643 = 9240965) B9240965
theorem B8225063 : Blo 1080619 8225063 := bstep (se 1 (by rfl) ⟨6168797, by rfl⟩ : syracuseStep 8225063 = 12337595) B12337595
theorem B1081663 : Blo 1080619 1081663 := bstep (se 1 (by rfl) ⟨811247, by rfl⟩ : syracuseStep 1081663 = 1622495) B1622495
theorem B1081831 : Blo 1080619 1081831 := bstep (se 1 (by rfl) ⟨811373, by rfl⟩ : syracuseStep 1081831 = 1622747) B1622747
theorem B1082107 : Blo 1080619 1082107 := bstep (se 1 (by rfl) ⟨811580, by rfl⟩ : syracuseStep 1082107 = 1623161) B1623161
theorem B4621063 : Blo 1080619 4621063 := bstep (se 1 (by rfl) ⟨3465797, by rfl⟩ : syracuseStep 4621063 = 6931595) B6931595
theorem B31687433 : Blo 1080619 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B1082239 : Blo 1080619 1082239 := bstep (se 1 (by rfl) ⟨811679, by rfl⟩ : syracuseStep 1082239 = 1623359) B1623359
theorem B1082687 : Blo 1080619 1082687 := bstep (se 1 (by rfl) ⟨812015, by rfl⟩ : syracuseStep 1082687 = 1624031) B1624031
theorem B1082727 : Blo 1080619 1082727 := bstep (se 1 (by rfl) ⟨812045, by rfl⟩ : syracuseStep 1082727 = 1624091) B1624091
theorem B1082831 : Blo 1080619 1082831 := bstep (se 1 (by rfl) ⟨812123, by rfl⟩ : syracuseStep 1082831 = 1624247) B1624247
theorem B1082847 : Blo 1080619 1082847 := bstep (se 1 (by rfl) ⟨812135, by rfl⟩ : syracuseStep 1082847 = 1624271) B1624271
theorem B1083111 : Blo 1080619 1083111 := bstep (se 1 (by rfl) ⟨812333, by rfl⟩ : syracuseStep 1083111 = 1624667) B1624667
theorem B1083207 : Blo 1080619 1083207 := bstep (se 1 (by rfl) ⟨812405, by rfl⟩ : syracuseStep 1083207 = 1624811) B1624811
theorem B1083227 : Blo 1080619 1083227 := bstep (se 1 (by rfl) ⟨812420, by rfl⟩ : syracuseStep 1083227 = 1624841) B1624841
theorem B3082121 : Blo 1080619 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B1083503 : Blo 1080619 1083503 := bstep (se 1 (by rfl) ⟨812627, by rfl⟩ : syracuseStep 1083503 = 1625255) B1625255
theorem B1083599 : Blo 1080619 1083599 := bstep (se 1 (by rfl) ⟨812699, by rfl⟩ : syracuseStep 1083599 = 1625399) B1625399
theorem B1542559 : Blo 1080619 1542559 := bstep (se 1 (by rfl) ⟨1156919, by rfl⟩ : syracuseStep 1542559 = 2313839) B2313839
theorem B1083807 : Blo 1080619 1083807 := bstep (se 1 (by rfl) ⟨812855, by rfl⟩ : syracuseStep 1083807 = 1625711) B1625711
theorem B1083855 : Blo 1080619 1083855 := bstep (se 1 (by rfl) ⟨812891, by rfl⟩ : syracuseStep 1083855 = 1625783) B1625783
theorem B1083887 : Blo 1080619 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B1083995 : Blo 1080619 1083995 := bstep (se 1 (by rfl) ⟨812996, by rfl⟩ : syracuseStep 1083995 = 1625993) B1625993
theorem B9996959 : Blo 1080619 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B1084155 : Blo 1080619 1084155 := bstep (se 1 (by rfl) ⟨813116, by rfl⟩ : syracuseStep 1084155 = 1626233) B1626233
theorem B1084159 : Blo 1080619 1084159 := bstep (se 1 (by rfl) ⟨813119, by rfl⟩ : syracuseStep 1084159 = 1626239) B1626239
theorem B6164059 : Blo 1080619 6164059 := bstep (se 1 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 6164059 = 9246089) B9246089
theorem B5476733 : Blo 1080619 5476733 := bstep (se 3 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 5476733 = 2053775) B2053775
theorem B15635069 : Blo 1080619 15635069 := bstep (se 3 (by rfl) ⟨2931575, by rfl⟩ : syracuseStep 15635069 = 5863151) B5863151
theorem B8885257 : Blo 1080619 8885257 := bstep (se 2 (by rfl) ⟨3331971, by rfl⟩ : syracuseStep 8885257 = 6663943) B6663943
theorem B76944491 : Blo 1080619 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B1217695 : Blo 1080619 1217695 := bstep (se 1 (by rfl) ⟨913271, by rfl⟩ : syracuseStep 1217695 = 1826543) B1826543
theorem B35067725 : Blo 1080619 35067725 := bstep (se 3 (by rfl) ⟨6575198, by rfl⟩ : syracuseStep 35067725 = 13150397) B13150397
theorem B2431403 : Blo 1080619 2431403 := bstep (se 1 (by rfl) ⟨1823552, by rfl⟩ : syracuseStep 2431403 = 3647105) B3647105
theorem B3906103 : Blo 1080619 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B1219999 : Blo 1080619 1219999 := bstep (se 1 (by rfl) ⟨914999, by rfl⟩ : syracuseStep 1219999 = 1829999) B1829999
theorem B1220143 : Blo 1080619 1220143 := bstep (se 1 (by rfl) ⟨915107, by rfl⟩ : syracuseStep 1220143 = 1830215) B1830215
theorem B2432735 : Blo 1080619 2432735 := bstep (se 1 (by rfl) ⟨1824551, by rfl⟩ : syracuseStep 2432735 = 3649103) B3649103
theorem B2433095 : Blo 1080619 2433095 := bstep (se 1 (by rfl) ⟨1824821, by rfl⟩ : syracuseStep 2433095 = 3649643) B3649643
theorem B4104377 : Blo 1080619 4104377 := bstep (se 2 (by rfl) ⟨1539141, by rfl⟩ : syracuseStep 4104377 = 3078283) B3078283
theorem B2924743 : Blo 1080619 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B9249065 : Blo 1080619 9249065 := bstep (se 2 (by rfl) ⟨3468399, by rfl⟩ : syracuseStep 9249065 = 6936799) B6936799
theorem B17539375 : Blo 1080619 17539375 := bstep (se 1 (by rfl) ⟨13154531, by rfl⟩ : syracuseStep 17539375 = 26309063) B26309063
theorem B2433401 : Blo 1080619 2433401 := bstep (se 2 (by rfl) ⟨912525, by rfl⟩ : syracuseStep 2433401 = 1825051) B1825051
theorem B4629095 : Blo 1080619 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B8233811 : Blo 1080619 8233811 := bstep (se 1 (by rfl) ⟨6175358, by rfl⟩ : syracuseStep 8233811 = 12350717) B12350717
theorem B1156351 : Blo 1080619 1156351 := bstep (se 1 (by rfl) ⟨867263, by rfl⟩ : syracuseStep 1156351 = 1734527) B1734527
theorem B16885097 : Blo 1080619 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B2434697 : Blo 1080619 2434697 := bstep (se 2 (by rfl) ⟨913011, by rfl⟩ : syracuseStep 2434697 = 1826023) B1826023
theorem B2434751 : Blo 1080619 2434751 := bstep (se 1 (by rfl) ⟨1826063, by rfl⟩ : syracuseStep 2434751 = 3652127) B3652127
theorem B8234783 : Blo 1080619 8234783 := bstep (se 1 (by rfl) ⟨6176087, by rfl⟩ : syracuseStep 8234783 = 12352175) B12352175
theorem B4106123 : Blo 1080619 4106123 := bstep (se 1 (by rfl) ⟨3079592, by rfl⟩ : syracuseStep 4106123 = 6159185) B6159185
theorem B3647375 : Blo 1080619 3647375 := bstep (se 1 (by rfl) ⟨2735531, by rfl⟩ : syracuseStep 3647375 = 5471063) B5471063
theorem B3647591 : Blo 1080619 3647591 := bstep (se 1 (by rfl) ⟨2735693, by rfl⟩ : syracuseStep 3647591 = 5471387) B5471387
theorem B5482889 : Blo 1080619 5482889 := bstep (se 2 (by rfl) ⟨2056083, by rfl⟩ : syracuseStep 5482889 = 4112167) B4112167
theorem B3648455 : Blo 1080619 3648455 := bstep (se 1 (by rfl) ⟨2736341, by rfl⟩ : syracuseStep 3648455 = 5472683) B5472683
theorem B5484185 : Blo 1080619 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B11710565 : Blo 1080619 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B3649697 : Blo 1080619 3649697 := bstep (se 2 (by rfl) ⟨1368636, by rfl⟩ : syracuseStep 3649697 = 2737273) B2737273
theorem B7418425 : Blo 1080619 7418425 := bstep (se 2 (by rfl) ⟨2781909, by rfl⟩ : syracuseStep 7418425 = 5563819) B5563819
theorem B2438009 : Blo 1080619 2438009 := bstep (se 2 (by rfl) ⟨914253, by rfl⟩ : syracuseStep 2438009 = 1828507) B1828507
theorem B7419239 : Blo 1080619 7419239 := bstep (se 1 (by rfl) ⟨5564429, by rfl⟩ : syracuseStep 7419239 = 11128859) B11128859
theorem B6174265 : Blo 1080619 6174265 := bstep (se 2 (by rfl) ⟨2315349, by rfl⟩ : syracuseStep 6174265 = 4630699) B4630699
theorem B2438783 : Blo 1080619 2438783 := bstep (se 1 (by rfl) ⟨1829087, by rfl⟩ : syracuseStep 2438783 = 3658175) B3658175
theorem B22230719 : Blo 1080619 22230719 := bstep (se 1 (by rfl) ⟨16673039, by rfl⟩ : syracuseStep 22230719 = 33346079) B33346079
theorem B2439305 : Blo 1080619 2439305 := bstep (se 2 (by rfl) ⟨914739, by rfl⟩ : syracuseStep 2439305 = 1829479) B1829479
theorem B2308601 : Blo 1080619 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B17578559 : Blo 1080619 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B2440007 : Blo 1080619 2440007 := bstep (se 1 (by rfl) ⟨1830005, by rfl⟩ : syracuseStep 2440007 = 3660011) B3660011
theorem B10402775 : Blo 1080619 10402775 := bstep (se 1 (by rfl) ⟨7802081, by rfl⟩ : syracuseStep 10402775 = 15604163) B15604163
theorem B1620959 : Blo 1080619 1620959 := bstep (se 1 (by rfl) ⟨1215719, by rfl⟩ : syracuseStep 1620959 = 2431439) B2431439
theorem B1621019 : Blo 1080619 1621019 := bstep (se 1 (by rfl) ⟨1215764, by rfl⟩ : syracuseStep 1621019 = 2431529) B2431529
theorem B5782649 : Blo 1080619 5782649 := bstep (se 2 (by rfl) ⟨2168493, by rfl⟩ : syracuseStep 5782649 = 4336987) B4336987
theorem B6175997 : Blo 1080619 6175997 := bstep (se 3 (by rfl) ⟨1157999, by rfl⟩ : syracuseStep 6175997 = 2315999) B2315999
theorem B9256751 : Blo 1080619 9256751 := bstep (se 1 (by rfl) ⟨6942563, by rfl⟩ : syracuseStep 9256751 = 13885127) B13885127
theorem B1621871 : Blo 1080619 1621871 := bstep (se 1 (by rfl) ⟨1216403, by rfl⟩ : syracuseStep 1621871 = 2432807) B2432807
theorem B3653801 : Blo 1080619 3653801 := bstep (se 2 (by rfl) ⟨1370175, by rfl⟩ : syracuseStep 3653801 = 2740351) B2740351
theorem B4112639 : Blo 1080619 4112639 := bstep (se 1 (by rfl) ⟨3084479, by rfl⟩ : syracuseStep 4112639 = 6168959) B6168959
theorem B24985907 : Blo 1080619 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B84263489 : Blo 1080619 84263489 := bstep (se 2 (by rfl) ⟨31598808, by rfl⟩ : syracuseStep 84263489 = 63197617) B63197617
theorem B3654395 : Blo 1080619 3654395 := bstep (se 1 (by rfl) ⟨2740796, by rfl⟩ : syracuseStep 3654395 = 5481593) B5481593
theorem B3654719 : Blo 1080619 3654719 := bstep (se 1 (by rfl) ⟨2741039, by rfl⟩ : syracuseStep 3654719 = 5482079) B5482079
theorem B8209511 : Blo 1080619 8209511 := bstep (se 1 (by rfl) ⟨6157133, by rfl⟩ : syracuseStep 8209511 = 12314267) B12314267
theorem B1623407 : Blo 1080619 1623407 := bstep (se 1 (by rfl) ⟨1217555, by rfl⟩ : syracuseStep 1623407 = 2435111) B2435111
theorem B1623527 : Blo 1080619 1623527 := bstep (se 1 (by rfl) ⟨1217645, by rfl⟩ : syracuseStep 1623527 = 2435291) B2435291
theorem B1623707 : Blo 1080619 1623707 := bstep (se 1 (by rfl) ⟨1217780, by rfl⟩ : syracuseStep 1623707 = 2435561) B2435561
theorem B5785559 : Blo 1080619 5785559 := bstep (se 1 (by rfl) ⟨4339169, by rfl⟩ : syracuseStep 5785559 = 8678339) B8678339
theorem B4442105 : Blo 1080619 4442105 := bstep (se 2 (by rfl) ⟨1665789, by rfl⟩ : syracuseStep 4442105 = 3331579) B3331579
theorem B5556221 : Blo 1080619 5556221 := bstep (se 3 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 5556221 = 2083583) B2083583
theorem B5490827 : Blo 1080619 5490827 := bstep (se 1 (by rfl) ⟨4118120, by rfl⟩ : syracuseStep 5490827 = 8236241) B8236241
theorem B1624295 : Blo 1080619 1624295 := bstep (se 1 (by rfl) ⟨1218221, by rfl⟩ : syracuseStep 1624295 = 2436443) B2436443
theorem B1624475 : Blo 1080619 1624475 := bstep (se 1 (by rfl) ⟨1218356, by rfl⟩ : syracuseStep 1624475 = 2436713) B2436713
theorem B3656447 : Blo 1080619 3656447 := bstep (se 1 (by rfl) ⟨2742335, by rfl⟩ : syracuseStep 3656447 = 5484671) B5484671
theorem B1624895 : Blo 1080619 1624895 := bstep (se 1 (by rfl) ⟨1218671, by rfl⟩ : syracuseStep 1624895 = 2437343) B2437343
theorem B4115357 : Blo 1080619 4115357 := bstep (se 3 (by rfl) ⟨771629, by rfl⟩ : syracuseStep 4115357 = 1543259) B1543259
theorem B2739167 : Blo 1080619 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B1625225 : Blo 1080619 1625225 := bstep (se 2 (by rfl) ⟨609459, by rfl⟩ : syracuseStep 1625225 = 1218919) B1218919
theorem B28921007 : Blo 1080619 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B1625279 : Blo 1080619 1625279 := bstep (se 1 (by rfl) ⟨1218959, by rfl⟩ : syracuseStep 1625279 = 2437919) B2437919
theorem B1625567 : Blo 1080619 1625567 := bstep (se 1 (by rfl) ⟨1219175, by rfl⟩ : syracuseStep 1625567 = 2438351) B2438351
theorem B5852645 : Blo 1080619 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B1625627 : Blo 1080619 1625627 := bstep (se 1 (by rfl) ⟨1219220, by rfl⟩ : syracuseStep 1625627 = 2438441) B2438441
theorem B10407851 : Blo 1080619 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B1626047 : Blo 1080619 1626047 := bstep (se 1 (by rfl) ⟨1219535, by rfl⟩ : syracuseStep 1626047 = 2439071) B2439071
theorem B25350097 : Blo 1080619 25350097 := bstep (se 2 (by rfl) ⟨9506286, by rfl⟩ : syracuseStep 25350097 = 19012573) B19012573
theorem B142626845 : Blo 1080619 142626845 := bstep (se 3 (by rfl) ⟨26742533, by rfl⟩ : syracuseStep 142626845 = 53485067) B53485067
theorem B4116527 : Blo 1080619 4116527 := bstep (se 1 (by rfl) ⟨3087395, by rfl⟩ : syracuseStep 4116527 = 6174791) B6174791
theorem B1298767 : Blo 1080619 1298767 := bstep (se 1 (by rfl) ⟨974075, by rfl⟩ : syracuseStep 1298767 = 1948151) B1948151
theorem B18764435 : Blo 1080619 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B3658553 : Blo 1080619 3658553 := bstep (se 2 (by rfl) ⟨1371957, by rfl⟩ : syracuseStep 3658553 = 2743915) B2743915
theorem B2053001 : Blo 1080619 2053001 := bstep (se 2 (by rfl) ⟨769875, by rfl⟩ : syracuseStep 2053001 = 1539751) B1539751
theorem B2741951 : Blo 1080619 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B18732779 : Blo 1080619 18732779 := bstep (se 1 (by rfl) ⟨14049584, by rfl⟩ : syracuseStep 18732779 = 28099169) B28099169
theorem B2053927 : Blo 1080619 2053927 := bstep (se 1 (by rfl) ⟨1540445, by rfl⟩ : syracuseStep 2053927 = 3080891) B3080891
theorem B79026425 : Blo 1080619 79026425 := bstep (se 2 (by rfl) ⟨29634909, by rfl⟩ : syracuseStep 79026425 = 59269819) B59269819
theorem B23452091 : Blo 1080619 23452091 := bstep (se 1 (by rfl) ⟨17589068, by rfl⟩ : syracuseStep 23452091 = 35178137) B35178137
theorem B11688421 : Blo 1080619 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B1825321 : Blo 1080619 1825321 := bstep (se 2 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 1825321 = 1368991) B1368991
theorem B3660443 : Blo 1080619 3660443 := bstep (se 1 (by rfl) ⟨2745332, by rfl⟩ : syracuseStep 3660443 = 5490665) B5490665
theorem B8215343 : Blo 1080619 8215343 := bstep (se 1 (by rfl) ⟨6161507, by rfl⟩ : syracuseStep 8215343 = 12323015) B12323015
theorem B1825787 : Blo 1080619 1825787 := bstep (se 1 (by rfl) ⟨1369340, by rfl⟩ : syracuseStep 1825787 = 2738681) B2738681
theorem B1826219 : Blo 1080619 1826219 := bstep (se 1 (by rfl) ⟨1369664, by rfl⟩ : syracuseStep 1826219 = 2739329) B2739329
theorem B7790087 : Blo 1080619 7790087 := bstep (se 1 (by rfl) ⟨5842565, by rfl⟩ : syracuseStep 7790087 = 11685131) B11685131
theorem B2744027 : Blo 1080619 2744027 := bstep (se 1 (by rfl) ⟨2058020, by rfl⟩ : syracuseStep 2744027 = 4116041) B4116041
theorem B1826651 : Blo 1080619 1826651 := bstep (se 1 (by rfl) ⟨1369988, by rfl⟩ : syracuseStep 1826651 = 2739977) B2739977
theorem B1826759 : Blo 1080619 1826759 := bstep (se 1 (by rfl) ⟨1370069, by rfl⟩ : syracuseStep 1826759 = 2740139) B2740139
theorem B1827515 : Blo 1080619 1827515 := bstep (se 1 (by rfl) ⟨1370636, by rfl⟩ : syracuseStep 1827515 = 2741273) B2741273
theorem B13886153 : Blo 1080619 13886153 := bstep (se 2 (by rfl) ⟨5207307, by rfl⟩ : syracuseStep 13886153 = 10414615) B10414615
theorem B1368895 : Blo 1080619 1368895 := bstep (se 1 (by rfl) ⟨1026671, by rfl⟩ : syracuseStep 1368895 = 2053343) B2053343
theorem B2057159 : Blo 1080619 2057159 := bstep (se 1 (by rfl) ⟨1542869, by rfl⟩ : syracuseStep 2057159 = 3085739) B3085739
theorem B1828075 : Blo 1080619 1828075 := bstep (se 1 (by rfl) ⟨1371056, by rfl⟩ : syracuseStep 1828075 = 2742113) B2742113
theorem B10544393 : Blo 1080619 10544393 := bstep (se 2 (by rfl) ⟨3954147, by rfl⟩ : syracuseStep 10544393 = 7908295) B7908295
theorem B17558315 : Blo 1080619 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B3468541 : Blo 1080619 3468541 := bstep (se 3 (by rfl) ⟨650351, by rfl⟩ : syracuseStep 3468541 = 1300703) B1300703
theorem B13888817 : Blo 1080619 13888817 := bstep (se 2 (by rfl) ⟨5208306, by rfl⟩ : syracuseStep 13888817 = 10416613) B10416613
theorem B1830235 : Blo 1080619 1830235 := bstep (se 1 (by rfl) ⟨1372676, by rfl⟩ : syracuseStep 1830235 = 2745353) B2745353
theorem B7401725 : Blo 1080619 7401725 := bstep (se 3 (by rfl) ⟨1387823, by rfl⟩ : syracuseStep 7401725 = 2775647) B2775647
theorem B14807609 : Blo 1080619 14807609 := bstep (se 2 (by rfl) ⟨5552853, by rfl⟩ : syracuseStep 14807609 = 11105707) B11105707
theorem B7796087 : Blo 1080619 7796087 := bstep (se 1 (by rfl) ⟨5847065, by rfl⟩ : syracuseStep 7796087 = 11694131) B11694131
theorem B3077929 : Blo 1080619 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B3897179 : Blo 1080619 3897179 := bstep (se 1 (by rfl) ⟨2922884, by rfl⟩ : syracuseStep 3897179 = 5845769) B5845769
theorem B9893927 : Blo 1080619 9893927 := bstep (se 1 (by rfl) ⟨7420445, by rfl⟩ : syracuseStep 9893927 = 14840891) B14840891
theorem B3897467 : Blo 1080619 3897467 := bstep (se 1 (by rfl) ⟨2923100, by rfl⟩ : syracuseStep 3897467 = 5846201) B5846201
theorem B4619065 : Blo 1080619 4619065 := bstep (se 2 (by rfl) ⟨1732149, by rfl⟩ : syracuseStep 4619065 = 3464299) B3464299
theorem B6159503 : Blo 1080619 6159503 := bstep (se 1 (by rfl) ⟨4619627, by rfl⟩ : syracuseStep 6159503 = 9239255) B9239255
theorem B1080799 : Blo 1080619 1080799 := bstep (se 1 (by rfl) ⟨810599, by rfl⟩ : syracuseStep 1080799 = 1621199) B1621199
theorem B1080859 : Blo 1080619 1080859 := bstep (se 1 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 1080859 = 1621289) B1621289
theorem B1080879 : Blo 1080619 1080879 := bstep (se 1 (by rfl) ⟨810659, by rfl⟩ : syracuseStep 1080879 = 1621319) B1621319
theorem B1081279 : Blo 1080619 1081279 := bstep (se 1 (by rfl) ⟨810959, by rfl⟩ : syracuseStep 1081279 = 1621919) B1621919
theorem B1081339 : Blo 1080619 1081339 := bstep (se 1 (by rfl) ⟨811004, by rfl⟩ : syracuseStep 1081339 = 1622009) B1622009
theorem B380338253 : Blo 1080619 380338253 := bstep (se 3 (by rfl) ⟨71313422, by rfl⟩ : syracuseStep 380338253 = 142626845) B142626845
theorem B3899657 : Blo 1080619 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B13894253 : Blo 1080619 13894253 := bstep (se 3 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 13894253 = 5210345) B5210345
theorem B5473007 : Blo 1080619 5473007 := bstep (se 1 (by rfl) ⟨4104755, by rfl⟩ : syracuseStep 5473007 = 8209511) B8209511
theorem B1082271 : Blo 1080619 1082271 := bstep (se 1 (by rfl) ⟨811703, by rfl⟩ : syracuseStep 1082271 = 1623407) B1623407
theorem B1082351 : Blo 1080619 1082351 := bstep (se 1 (by rfl) ⟨811763, by rfl⟩ : syracuseStep 1082351 = 1623527) B1623527
theorem B6161417 : Blo 1080619 6161417 := bstep (se 2 (by rfl) ⟨2310531, by rfl⟩ : syracuseStep 6161417 = 4621063) B4621063
theorem B1082471 : Blo 1080619 1082471 := bstep (se 1 (by rfl) ⟨811853, by rfl⟩ : syracuseStep 1082471 = 1623707) B1623707
theorem B3704147 : Blo 1080619 3704147 := bstep (se 1 (by rfl) ⟨2778110, by rfl⟩ : syracuseStep 3704147 = 5556221) B5556221
theorem B1082863 : Blo 1080619 1082863 := bstep (se 1 (by rfl) ⟨812147, by rfl⟩ : syracuseStep 1082863 = 1624295) B1624295
theorem B1082983 : Blo 1080619 1082983 := bstep (se 1 (by rfl) ⟨812237, by rfl⟩ : syracuseStep 1082983 = 1624475) B1624475
theorem B1541801 : Blo 1080619 1541801 := bstep (se 2 (by rfl) ⟨578175, by rfl⟩ : syracuseStep 1541801 = 1156351) B1156351
theorem B1083263 : Blo 1080619 1083263 := bstep (se 1 (by rfl) ⟨812447, by rfl⟩ : syracuseStep 1083263 = 1624895) B1624895
theorem B1083483 : Blo 1080619 1083483 := bstep (se 1 (by rfl) ⟨812612, by rfl⟩ : syracuseStep 1083483 = 1625225) B1625225
theorem B1083519 : Blo 1080619 1083519 := bstep (se 1 (by rfl) ⟨812639, by rfl⟩ : syracuseStep 1083519 = 1625279) B1625279
theorem B1083711 : Blo 1080619 1083711 := bstep (se 1 (by rfl) ⟨812783, by rfl⟩ : syracuseStep 1083711 = 1625567) B1625567
theorem B3901763 : Blo 1080619 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B1083751 : Blo 1080619 1083751 := bstep (se 1 (by rfl) ⟨812813, by rfl⟩ : syracuseStep 1083751 = 1625627) B1625627
theorem B1084031 : Blo 1080619 1084031 := bstep (se 1 (by rfl) ⟨813023, by rfl⟩ : syracuseStep 1084031 = 1626047) B1626047
theorem B10423379 : Blo 1080619 10423379 := bstep (se 1 (by rfl) ⟨7817534, by rfl⟩ : syracuseStep 10423379 = 15635069) B15635069
theorem B12488519 : Blo 1080619 12488519 := bstep (se 1 (by rfl) ⟨9366389, by rfl⟩ : syracuseStep 12488519 = 18732779) B18732779
theorem B15634727 : Blo 1080619 15634727 := bstep (se 1 (by rfl) ⟨11726045, by rfl⟩ : syracuseStep 15634727 = 23452091) B23452091
theorem B4624721 : Blo 1080619 4624721 := bstep (se 2 (by rfl) ⟨1734270, by rfl⟩ : syracuseStep 4624721 = 3468541) B3468541
theorem B5476895 : Blo 1080619 5476895 := bstep (se 1 (by rfl) ⟨4107671, by rfl⟩ : syracuseStep 5476895 = 8215343) B8215343
theorem B1217191 : Blo 1080619 1217191 := bstep (se 1 (by rfl) ⟨912893, by rfl⟩ : syracuseStep 1217191 = 1825787) B1825787
theorem B1217479 : Blo 1080619 1217479 := bstep (se 1 (by rfl) ⟨913109, by rfl⟩ : syracuseStep 1217479 = 1826219) B1826219
theorem B1217767 : Blo 1080619 1217767 := bstep (se 1 (by rfl) ⟨913325, by rfl⟩ : syracuseStep 1217767 = 1826651) B1826651
theorem B1217839 : Blo 1080619 1217839 := bstep (se 1 (by rfl) ⟨913379, by rfl⟩ : syracuseStep 1217839 = 1826759) B1826759
theorem B47388037 : Blo 1080619 47388037 := bstep (se 4 (by rfl) ⟨4442628, by rfl⟩ : syracuseStep 47388037 = 8885257) B8885257
theorem B6166043 : Blo 1080619 6166043 := bstep (se 1 (by rfl) ⟨4624532, by rfl⟩ : syracuseStep 6166043 = 9249065) B9249065
theorem B3086063 : Blo 1080619 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B1218343 : Blo 1080619 1218343 := bstep (se 1 (by rfl) ⟨913757, by rfl⟩ : syracuseStep 1218343 = 1827515) B1827515
theorem B2431583 : Blo 1080619 2431583 := bstep (se 1 (by rfl) ⟨1823687, by rfl⟩ : syracuseStep 2431583 = 3647375) B3647375
theorem B2431727 : Blo 1080619 2431727 := bstep (se 1 (by rfl) ⟨1823795, by rfl⟩ : syracuseStep 2431727 = 3647591) B3647591
theorem B11705543 : Blo 1080619 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B2432303 : Blo 1080619 2432303 := bstep (se 1 (by rfl) ⟨1824227, by rfl⟩ : syracuseStep 2432303 = 3648455) B3648455
theorem B8232353 : Blo 1080619 8232353 := bstep (se 2 (by rfl) ⟨3087132, by rfl⟩ : syracuseStep 8232353 = 6174265) B6174265
theorem B4103905 : Blo 1080619 4103905 := bstep (se 2 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 4103905 = 3077929) B3077929
theorem B7807043 : Blo 1080619 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B2433131 : Blo 1080619 2433131 := bstep (se 1 (by rfl) ⟨1824848, by rfl⟩ : syracuseStep 2433131 = 3649697) B3649697
theorem B9871739 : Blo 1080619 9871739 := bstep (se 1 (by rfl) ⟨7403804, by rfl⟩ : syracuseStep 9871739 = 14807609) B14807609
theorem B2433761 : Blo 1080619 2433761 := bstep (se 2 (by rfl) ⟨912660, by rfl⟩ : syracuseStep 2433761 = 1825321) B1825321
theorem B14820479 : Blo 1080619 14820479 := bstep (se 1 (by rfl) ⟨11115359, by rfl⟩ : syracuseStep 14820479 = 22230719) B22230719
theorem B2598119 : Blo 1080619 2598119 := bstep (se 1 (by rfl) ⟨1948589, by rfl⟩ : syracuseStep 2598119 = 3897179) B3897179
theorem B6595951 : Blo 1080619 6595951 := bstep (se 1 (by rfl) ⟨4946963, by rfl⟩ : syracuseStep 6595951 = 9893927) B9893927
theorem B2598311 : Blo 1080619 2598311 := bstep (se 1 (by rfl) ⟨1948733, by rfl⟩ : syracuseStep 2598311 = 3897467) B3897467
theorem B4106335 : Blo 1080619 4106335 := bstep (se 1 (by rfl) ⟨3079751, by rfl⟩ : syracuseStep 4106335 = 6159503) B6159503
theorem B6171167 : Blo 1080619 6171167 := bstep (se 1 (by rfl) ⟨4628375, by rfl⟩ : syracuseStep 6171167 = 9256751) B9256751
theorem B1157863 : Blo 1080619 1157863 := bstep (se 1 (by rfl) ⟨868397, by rfl⟩ : syracuseStep 1157863 = 1736795) B1736795
theorem B2435867 : Blo 1080619 2435867 := bstep (se 1 (by rfl) ⟨1826900, by rfl⟩ : syracuseStep 2435867 = 3653801) B3653801
theorem B4107095 : Blo 1080619 4107095 := bstep (se 1 (by rfl) ⟨3080321, by rfl⟩ : syracuseStep 4107095 = 6160643) B6160643
theorem B5483375 : Blo 1080619 5483375 := bstep (se 1 (by rfl) ⟨4112531, by rfl⟩ : syracuseStep 5483375 = 8225063) B8225063
theorem B16657271 : Blo 1080619 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B56175659 : Blo 1080619 56175659 := bstep (se 1 (by rfl) ⟨42131744, by rfl⟩ : syracuseStep 56175659 = 84263489) B84263489
theorem B2436263 : Blo 1080619 2436263 := bstep (se 1 (by rfl) ⟨1827197, by rfl⟩ : syracuseStep 2436263 = 3654395) B3654395
theorem B2436479 : Blo 1080619 2436479 := bstep (se 1 (by rfl) ⟨1827359, by rfl⟩ : syracuseStep 2436479 = 3654719) B3654719
theorem B2961403 : Blo 1080619 2961403 := bstep (se 1 (by rfl) ⟨2221052, by rfl⟩ : syracuseStep 2961403 = 4442105) B4442105
theorem B2437433 : Blo 1080619 2437433 := bstep (se 2 (by rfl) ⟨914037, by rfl⟩ : syracuseStep 2437433 = 1828075) B1828075
theorem B6664639 : Blo 1080619 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B2437631 : Blo 1080619 2437631 := bstep (se 1 (by rfl) ⟨1828223, by rfl⟩ : syracuseStep 2437631 = 3656447) B3656447
theorem B3651155 : Blo 1080619 3651155 := bstep (se 1 (by rfl) ⟨2738366, by rfl⟩ : syracuseStep 3651155 = 5476733) B5476733
theorem B2439035 : Blo 1080619 2439035 := bstep (se 1 (by rfl) ⟨1829276, by rfl⟩ : syracuseStep 2439035 = 3658553) B3658553
theorem B51296327 : Blo 1080619 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B23378483 : Blo 1080619 23378483 := bstep (se 1 (by rfl) ⟨17533862, by rfl⟩ : syracuseStep 23378483 = 35067725) B35067725
theorem B1620935 : Blo 1080619 1620935 := bstep (se 1 (by rfl) ⟨1215701, by rfl⟩ : syracuseStep 1620935 = 2431403) B2431403
theorem B2440295 : Blo 1080619 2440295 := bstep (se 1 (by rfl) ⟨1830221, by rfl⟩ : syracuseStep 2440295 = 3660443) B3660443
theorem B2440313 : Blo 1080619 2440313 := bstep (se 2 (by rfl) ⟨915117, by rfl⟩ : syracuseStep 2440313 = 1830235) B1830235
theorem B5193391 : Blo 1080619 5193391 := bstep (se 1 (by rfl) ⟨3895043, by rfl⟩ : syracuseStep 5193391 = 7790087) B7790087
theorem B1621823 : Blo 1080619 1621823 := bstep (se 1 (by rfl) ⟨1216367, by rfl⟩ : syracuseStep 1621823 = 2432735) B2432735
theorem B33800129 : Blo 1080619 33800129 := bstep (se 2 (by rfl) ⟨12675048, by rfl⟩ : syracuseStep 33800129 = 25350097) B25350097
theorem B1622063 : Blo 1080619 1622063 := bstep (se 1 (by rfl) ⟨1216547, by rfl⟩ : syracuseStep 1622063 = 2433095) B2433095
theorem B2736251 : Blo 1080619 2736251 := bstep (se 1 (by rfl) ⟨2052188, by rfl⟩ : syracuseStep 2736251 = 4104377) B4104377
theorem B1622267 : Blo 1080619 1622267 := bstep (se 1 (by rfl) ⟨1216700, by rfl⟩ : syracuseStep 1622267 = 2433401) B2433401
theorem B9257435 : Blo 1080619 9257435 := bstep (se 1 (by rfl) ⟨6943076, by rfl⟩ : syracuseStep 9257435 = 13886153) B13886153
theorem B5489207 : Blo 1080619 5489207 := bstep (se 1 (by rfl) ⟨4116905, by rfl⟩ : syracuseStep 5489207 = 8233811) B8233811
theorem B7029595 : Blo 1080619 7029595 := bstep (se 1 (by rfl) ⟨5272196, by rfl⟩ : syracuseStep 7029595 = 10544393) B10544393
theorem B11256731 : Blo 1080619 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B1623131 : Blo 1080619 1623131 := bstep (se 1 (by rfl) ⟨1217348, by rfl⟩ : syracuseStep 1623131 = 2434697) B2434697
theorem B1623167 : Blo 1080619 1623167 := bstep (se 1 (by rfl) ⟨1217375, by rfl⟩ : syracuseStep 1623167 = 2434751) B2434751
theorem B5489855 : Blo 1080619 5489855 := bstep (se 1 (by rfl) ⟨4117391, by rfl⟩ : syracuseStep 5489855 = 8234783) B8234783
theorem B2737415 : Blo 1080619 2737415 := bstep (se 1 (by rfl) ⟨2053061, by rfl⟩ : syracuseStep 2737415 = 4106123) B4106123
theorem B1623593 : Blo 1080619 1623593 := bstep (se 2 (by rfl) ⟨608847, by rfl⟩ : syracuseStep 1623593 = 1217695) B1217695
theorem B3655259 : Blo 1080619 3655259 := bstep (se 1 (by rfl) ⟨2741444, by rfl⟩ : syracuseStep 3655259 = 5482889) B5482889
theorem B9259211 : Blo 1080619 9259211 := bstep (se 1 (by rfl) ⟨6944408, by rfl⟩ : syracuseStep 9259211 = 13888817) B13888817
theorem B2738569 : Blo 1080619 2738569 := bstep (se 2 (by rfl) ⟨1026963, by rfl⟩ : syracuseStep 2738569 = 2053927) B2053927
theorem B3656123 : Blo 1080619 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B4934483 : Blo 1080619 4934483 := bstep (se 1 (by rfl) ⟨3700862, by rfl⟩ : syracuseStep 4934483 = 7401725) B7401725
theorem B15420397 : Blo 1080619 15420397 := bstep (se 3 (by rfl) ⟨2891324, by rfl⟩ : syracuseStep 15420397 = 5782649) B5782649
theorem B77122685 : Blo 1080619 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B1625339 : Blo 1080619 1625339 := bstep (se 1 (by rfl) ⟨1219004, by rfl⟩ : syracuseStep 1625339 = 2438009) B2438009
theorem B15584561 : Blo 1080619 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B5197391 : Blo 1080619 5197391 := bstep (se 1 (by rfl) ⟨3898043, by rfl⟩ : syracuseStep 5197391 = 7796087) B7796087
theorem B1625855 : Blo 1080619 1625855 := bstep (se 1 (by rfl) ⟨1219391, by rfl⟩ : syracuseStep 1625855 = 2438783) B2438783
theorem B1626203 : Blo 1080619 1626203 := bstep (se 1 (by rfl) ⟨1219652, by rfl⟩ : syracuseStep 1626203 = 2439305) B2439305
theorem B11719039 : Blo 1080619 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B1626665 : Blo 1080619 1626665 := bstep (se 2 (by rfl) ⟨609999, by rfl⟩ : syracuseStep 1626665 = 1219999) B1219999
theorem B1626671 : Blo 1080619 1626671 := bstep (se 1 (by rfl) ⟨1220003, by rfl⟩ : syracuseStep 1626671 = 2440007) B2440007
theorem B6935183 : Blo 1080619 6935183 := bstep (se 1 (by rfl) ⟨5201387, by rfl⟩ : syracuseStep 6935183 = 10402775) B10402775
theorem B1626857 : Blo 1080619 1626857 := bstep (se 2 (by rfl) ⟨610071, by rfl⟩ : syracuseStep 1626857 = 1220143) B1220143
theorem B4117331 : Blo 1080619 4117331 := bstep (se 1 (by rfl) ⟨3087998, by rfl⟩ : syracuseStep 4117331 = 6175997) B6175997
theorem B2741759 : Blo 1080619 2741759 := bstep (se 1 (by rfl) ⟨2056319, by rfl⟩ : syracuseStep 2741759 = 4112639) B4112639
theorem B23385833 : Blo 1080619 23385833 := bstep (se 2 (by rfl) ⟨8769687, by rfl⟩ : syracuseStep 23385833 = 17539375) B17539375
theorem B21124955 : Blo 1080619 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B1825193 : Blo 1080619 1825193 := bstep (se 2 (by rfl) ⟨684447, by rfl⟩ : syracuseStep 1825193 = 1368895) B1368895
theorem B2054747 : Blo 1080619 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B3857039 : Blo 1080619 3857039 := bstep (se 1 (by rfl) ⟨2892779, by rfl⟩ : syracuseStep 3857039 = 5785559) B5785559
theorem B3660551 : Blo 1080619 3660551 := bstep (se 1 (by rfl) ⟨2745413, by rfl⟩ : syracuseStep 3660551 = 5490827) B5490827
theorem B2743571 : Blo 1080619 2743571 := bstep (se 1 (by rfl) ⟨2057678, by rfl⟩ : syracuseStep 2743571 = 4115357) B4115357
theorem B1826111 : Blo 1080619 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B6938567 : Blo 1080619 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B2744351 : Blo 1080619 2744351 := bstep (se 1 (by rfl) ⟨2058263, by rfl⟩ : syracuseStep 2744351 = 4116527) B4116527
theorem B12509623 : Blo 1080619 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B2056745 : Blo 1080619 2056745 := bstep (se 2 (by rfl) ⟨771279, by rfl⟩ : syracuseStep 2056745 = 1542559) B1542559
theorem B1368667 : Blo 1080619 1368667 := bstep (se 1 (by rfl) ⟨1026500, by rfl⟩ : syracuseStep 1368667 = 2053001) B2053001
theorem B1827967 : Blo 1080619 1827967 := bstep (se 1 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 1827967 = 2741951) B2741951
theorem B52684283 : Blo 1080619 52684283 := bstep (se 1 (by rfl) ⟨39513212, by rfl⟩ : syracuseStep 52684283 = 79026425) B79026425
theorem B8218745 : Blo 1080619 8218745 := bstep (se 2 (by rfl) ⟨3082029, by rfl⟩ : syracuseStep 8218745 = 6164059) B6164059
theorem B1829351 : Blo 1080619 1829351 := bstep (se 1 (by rfl) ⟨1372013, by rfl⟩ : syracuseStep 1829351 = 2744027) B2744027
theorem B1731689 : Blo 1080619 1731689 := bstep (se 2 (by rfl) ⟨649383, by rfl⟩ : syracuseStep 1731689 = 1298767) B1298767
theorem B1371439 : Blo 1080619 1371439 := bstep (se 1 (by rfl) ⟨1028579, by rfl⟩ : syracuseStep 1371439 = 2057159) B2057159
theorem B9891233 : Blo 1080619 9891233 := bstep (se 2 (by rfl) ⟨3709212, by rfl⟩ : syracuseStep 9891233 = 7418425) B7418425
theorem B6156269 : Blo 1080619 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B5208137 : Blo 1080619 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B4946159 : Blo 1080619 4946159 := bstep (se 1 (by rfl) ⟨3709619, by rfl⟩ : syracuseStep 4946159 = 7419239) B7419239
theorem B6158753 : Blo 1080619 6158753 := bstep (se 2 (by rfl) ⟨2309532, by rfl⟩ : syracuseStep 6158753 = 4619065) B4619065
theorem B1080639 : Blo 1080619 1080639 := bstep (se 1 (by rfl) ⟨810479, by rfl⟩ : syracuseStep 1080639 = 1620959) B1620959
theorem B1080679 : Blo 1080619 1080679 := bstep (se 1 (by rfl) ⟨810509, by rfl⟩ : syracuseStep 1080679 = 1621019) B1621019
theorem B1081247 : Blo 1080619 1081247 := bstep (se 1 (by rfl) ⟨810935, by rfl⟩ : syracuseStep 1081247 = 1621871) B1621871
theorem B1081375 : Blo 1080619 1081375 := bstep (se 1 (by rfl) ⟨811031, by rfl⟩ : syracuseStep 1081375 = 1622063) B1622063
theorem B253558835 : Blo 1080619 253558835 := bstep (se 1 (by rfl) ⟨190169126, by rfl⟩ : syracuseStep 253558835 = 380338253) B380338253
theorem B1081511 : Blo 1080619 1081511 := bstep (se 1 (by rfl) ⟨811133, by rfl⟩ : syracuseStep 1081511 = 1622267) B1622267
theorem B7504487 : Blo 1080619 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B1082087 : Blo 1080619 1082087 := bstep (se 1 (by rfl) ⟨811565, by rfl⟩ : syracuseStep 1082087 = 1623131) B1623131
theorem B1082111 : Blo 1080619 1082111 := bstep (se 1 (by rfl) ⟨811583, by rfl⟩ : syracuseStep 1082111 = 1623167) B1623167
theorem B1082395 : Blo 1080619 1082395 := bstep (se 1 (by rfl) ⟨811796, by rfl⟩ : syracuseStep 1082395 = 1623593) B1623593
theorem B6948919 : Blo 1080619 6948919 := bstep (se 1 (by rfl) ⟨5211689, by rfl⟩ : syracuseStep 6948919 = 10423379) B10423379
theorem B51415123 : Blo 1080619 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B1083559 : Blo 1080619 1083559 := bstep (se 1 (by rfl) ⟨812669, by rfl⟩ : syracuseStep 1083559 = 1625339) B1625339
theorem B10389707 : Blo 1080619 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B66717989 : Blo 1080619 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B1083903 : Blo 1080619 1083903 := bstep (se 1 (by rfl) ⟨812927, by rfl⟩ : syracuseStep 1083903 = 1625855) B1625855
theorem B8325679 : Blo 1080619 8325679 := bstep (se 1 (by rfl) ⟨6244259, by rfl⟩ : syracuseStep 8325679 = 12488519) B12488519
theorem B1084135 : Blo 1080619 1084135 := bstep (se 1 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 1084135 = 1626203) B1626203
theorem B5475113 : Blo 1080619 5475113 := bstep (se 2 (by rfl) ⟨2053167, by rfl⟩ : syracuseStep 5475113 = 4106335) B4106335
theorem B10423151 : Blo 1080619 10423151 := bstep (se 1 (by rfl) ⟨7817363, by rfl⟩ : syracuseStep 10423151 = 15634727) B15634727
theorem B3083147 : Blo 1080619 3083147 := bstep (se 1 (by rfl) ⟨2312360, by rfl⟩ : syracuseStep 3083147 = 4624721) B4624721
theorem B1084443 : Blo 1080619 1084443 := bstep (se 1 (by rfl) ⟨813332, by rfl⟩ : syracuseStep 1084443 = 1626665) B1626665
theorem B1084447 : Blo 1080619 1084447 := bstep (se 1 (by rfl) ⟨813335, by rfl⟩ : syracuseStep 1084447 = 1626671) B1626671
theorem B4623455 : Blo 1080619 4623455 := bstep (se 1 (by rfl) ⟨3467591, by rfl⟩ : syracuseStep 4623455 = 6935183) B6935183
theorem B1084571 : Blo 1080619 1084571 := bstep (se 1 (by rfl) ⟨813428, by rfl⟩ : syracuseStep 1084571 = 1626857) B1626857
theorem B1543817 : Blo 1080619 1543817 := bstep (se 2 (by rfl) ⟨578931, by rfl⟩ : syracuseStep 1543817 = 1157863) B1157863
theorem B1216795 : Blo 1080619 1216795 := bstep (se 1 (by rfl) ⟨912596, by rfl⟩ : syracuseStep 1216795 = 1825193) B1825193
theorem B37491173 : Blo 1080619 37491173 := bstep (se 4 (by rfl) ⟨3514797, by rfl⟩ : syracuseStep 37491173 = 7029595) B7029595
theorem B7803695 : Blo 1080619 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B1217407 : Blo 1080619 1217407 := bstep (se 1 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 1217407 = 1826111) B1826111
theorem B4625711 : Blo 1080619 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B8886185 : Blo 1080619 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B5479163 : Blo 1080619 5479163 := bstep (se 1 (by rfl) ⟨4109372, by rfl⟩ : syracuseStep 5479163 = 8218745) B8218745
theorem B5479325 : Blo 1080619 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B1219567 : Blo 1080619 1219567 := bstep (se 1 (by rfl) ⟨914675, by rfl⟩ : syracuseStep 1219567 = 1829351) B1829351
theorem B63184049 : Blo 1080619 63184049 := bstep (se 2 (by rfl) ⟨23694018, by rfl⟩ : syracuseStep 63184049 = 47388037) B47388037
theorem B1154459 : Blo 1080619 1154459 := bstep (se 1 (by rfl) ⟨865844, by rfl⟩ : syracuseStep 1154459 = 1731689) B1731689
theorem B6594155 : Blo 1080619 6594155 := bstep (se 1 (by rfl) ⟨4945616, by rfl⟩ : syracuseStep 6594155 = 9891233) B9891233
theorem B4104179 : Blo 1080619 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B2434103 : Blo 1080619 2434103 := bstep (se 1 (by rfl) ⟨1825577, by rfl⟩ : syracuseStep 2434103 = 3651155) B3651155
theorem B4105835 : Blo 1080619 4105835 := bstep (se 1 (by rfl) ⟨3079376, by rfl⟩ : syracuseStep 4105835 = 6158753) B6158753
theorem B6924521 : Blo 1080619 6924521 := bstep (se 2 (by rfl) ⟨2596695, by rfl⟩ : syracuseStep 6924521 = 5193391) B5193391
theorem B2599771 : Blo 1080619 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B6171623 : Blo 1080619 6171623 := bstep (se 1 (by rfl) ⟨4628717, by rfl⟩ : syracuseStep 6171623 = 9257435) B9257435
theorem B3648671 : Blo 1080619 3648671 := bstep (se 1 (by rfl) ⟨2736503, by rfl⟩ : syracuseStep 3648671 = 5473007) B5473007
theorem B4107611 : Blo 1080619 4107611 := bstep (se 1 (by rfl) ⟨3080708, by rfl⟩ : syracuseStep 4107611 = 6161417) B6161417
theorem B2469431 : Blo 1080619 2469431 := bstep (se 1 (by rfl) ⟨1852073, by rfl⟩ : syracuseStep 2469431 = 3704147) B3704147
theorem B2436839 : Blo 1080619 2436839 := bstep (se 1 (by rfl) ⟨1827629, by rfl⟩ : syracuseStep 2436839 = 3655259) B3655259
theorem B6172807 : Blo 1080619 6172807 := bstep (se 1 (by rfl) ⟨4629605, by rfl⟩ : syracuseStep 6172807 = 9259211) B9259211
theorem B2437289 : Blo 1080619 2437289 := bstep (se 2 (by rfl) ⟨913983, by rfl⟩ : syracuseStep 2437289 = 1827967) B1827967
theorem B2601175 : Blo 1080619 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B2437415 : Blo 1080619 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B8794601 : Blo 1080619 8794601 := bstep (se 2 (by rfl) ⟨3297975, by rfl⟩ : syracuseStep 8794601 = 6595951) B6595951
theorem B3289655 : Blo 1080619 3289655 := bstep (se 1 (by rfl) ⟨2467241, by rfl⟩ : syracuseStep 3289655 = 4934483) B4934483
theorem B3651263 : Blo 1080619 3651263 := bstep (se 1 (by rfl) ⟨2738447, by rfl⟩ : syracuseStep 3651263 = 5476895) B5476895
theorem B3651425 : Blo 1080619 3651425 := bstep (se 2 (by rfl) ⟨1369284, by rfl⟩ : syracuseStep 3651425 = 2738569) B2738569
theorem B4110695 : Blo 1080619 4110695 := bstep (se 1 (by rfl) ⟨3083021, by rfl⟩ : syracuseStep 4110695 = 6166043) B6166043
theorem B20560529 : Blo 1080619 20560529 := bstep (se 2 (by rfl) ⟨7710198, by rfl⟩ : syracuseStep 20560529 = 15420397) B15420397
theorem B1621055 : Blo 1080619 1621055 := bstep (se 1 (by rfl) ⟨1215791, by rfl⟩ : syracuseStep 1621055 = 2431583) B2431583
theorem B2571359 : Blo 1080619 2571359 := bstep (se 1 (by rfl) ⟨1928519, by rfl⟩ : syracuseStep 2571359 = 3857039) B3857039
theorem B4111469 : Blo 1080619 4111469 := bstep (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) B1541801
theorem B1621151 : Blo 1080619 1621151 := bstep (se 1 (by rfl) ⟨1215863, by rfl⟩ : syracuseStep 1621151 = 2431727) B2431727
theorem B2440367 : Blo 1080619 2440367 := bstep (se 1 (by rfl) ⟨1830275, by rfl⟩ : syracuseStep 2440367 = 3660551) B3660551
theorem B1621535 : Blo 1080619 1621535 := bstep (se 1 (by rfl) ⟨1216151, by rfl⟩ : syracuseStep 1621535 = 2432303) B2432303
theorem B5488235 : Blo 1080619 5488235 := bstep (se 1 (by rfl) ⟨4116176, by rfl⟩ : syracuseStep 5488235 = 8232353) B8232353
theorem B1622087 : Blo 1080619 1622087 := bstep (se 1 (by rfl) ⟨1216565, by rfl⟩ : syracuseStep 1622087 = 2433131) B2433131
theorem B1622507 : Blo 1080619 1622507 := bstep (se 1 (by rfl) ⟨1216880, by rfl⟩ : syracuseStep 1622507 = 2433761) B2433761
theorem B9880319 : Blo 1080619 9880319 := bstep (se 1 (by rfl) ⟨7410239, by rfl⟩ : syracuseStep 9880319 = 14820479) B14820479
theorem B1622921 : Blo 1080619 1622921 := bstep (se 2 (by rfl) ⟨608595, by rfl⟩ : syracuseStep 1622921 = 1217191) B1217191
theorem B1623305 : Blo 1080619 1623305 := bstep (se 2 (by rfl) ⟨608739, by rfl⟩ : syracuseStep 1623305 = 1217479) B1217479
theorem B1623689 : Blo 1080619 1623689 := bstep (se 2 (by rfl) ⟨608883, by rfl⟩ : syracuseStep 1623689 = 1217767) B1217767
theorem B4114111 : Blo 1080619 4114111 := bstep (se 1 (by rfl) ⟨3085583, by rfl⟩ : syracuseStep 4114111 = 6171167) B6171167
theorem B1623785 : Blo 1080619 1623785 := bstep (se 2 (by rfl) ⟨608919, by rfl⟩ : syracuseStep 1623785 = 1217839) B1217839
theorem B1623911 : Blo 1080619 1623911 := bstep (se 1 (by rfl) ⟨1217933, by rfl⟩ : syracuseStep 1623911 = 2435867) B2435867
theorem B2738063 : Blo 1080619 2738063 := bstep (se 1 (by rfl) ⟨2053547, by rfl⟩ : syracuseStep 2738063 = 4107095) B4107095
theorem B3655583 : Blo 1080619 3655583 := bstep (se 1 (by rfl) ⟨2741687, by rfl⟩ : syracuseStep 3655583 = 5483375) B5483375
theorem B1624175 : Blo 1080619 1624175 := bstep (se 1 (by rfl) ⟨1218131, by rfl⟩ : syracuseStep 1624175 = 2436263) B2436263
theorem B1624319 : Blo 1080619 1624319 := bstep (se 1 (by rfl) ⟨1218239, by rfl⟩ : syracuseStep 1624319 = 2436479) B2436479
theorem B1624457 : Blo 1080619 1624457 := bstep (se 2 (by rfl) ⟨609171, by rfl⟩ : syracuseStep 1624457 = 1218343) B1218343
theorem B1624955 : Blo 1080619 1624955 := bstep (se 1 (by rfl) ⟨1218716, by rfl⟩ : syracuseStep 1624955 = 2437433) B2437433
theorem B1625087 : Blo 1080619 1625087 := bstep (se 1 (by rfl) ⟨1218815, by rfl⟩ : syracuseStep 1625087 = 2437631) B2437631
theorem B1626023 : Blo 1080619 1626023 := bstep (se 1 (by rfl) ⟨1219517, by rfl⟩ : syracuseStep 1626023 = 2439035) B2439035
theorem B34197551 : Blo 1080619 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B3297439 : Blo 1080619 3297439 := bstep (se 1 (by rfl) ⟨2473079, by rfl⟩ : syracuseStep 3297439 = 4946159) B4946159
theorem B15585655 : Blo 1080619 15585655 := bstep (se 1 (by rfl) ⟨11689241, by rfl⟩ : syracuseStep 15585655 = 23378483) B23378483
theorem B1626863 : Blo 1080619 1626863 := bstep (se 1 (by rfl) ⟨1220147, by rfl⟩ : syracuseStep 1626863 = 2440295) B2440295
theorem B1626875 : Blo 1080619 1626875 := bstep (se 1 (by rfl) ⟨1220156, by rfl⟩ : syracuseStep 1626875 = 2440313) B2440313
theorem B22533419 : Blo 1080619 22533419 := bstep (se 1 (by rfl) ⟨16900064, by rfl⟩ : syracuseStep 22533419 = 33800129) B33800129
theorem B1824167 : Blo 1080619 1824167 := bstep (se 1 (by rfl) ⟨1368125, by rfl⟩ : syracuseStep 1824167 = 2736251) B2736251
theorem B3659471 : Blo 1080619 3659471 := bstep (se 1 (by rfl) ⟨2744603, by rfl⟩ : syracuseStep 3659471 = 5489207) B5489207
theorem B9262835 : Blo 1080619 9262835 := bstep (se 1 (by rfl) ⟨6947126, by rfl⟩ : syracuseStep 9262835 = 13894253) B13894253
theorem B1824889 : Blo 1080619 1824889 := bstep (se 2 (by rfl) ⟨684333, by rfl⟩ : syracuseStep 1824889 = 1368667) B1368667
theorem B3659903 : Blo 1080619 3659903 := bstep (se 1 (by rfl) ⟨2744927, by rfl⟩ : syracuseStep 3659903 = 5489855) B5489855
theorem B1824943 : Blo 1080619 1824943 := bstep (se 1 (by rfl) ⟨1368707, by rfl⟩ : syracuseStep 1824943 = 2737415) B2737415
theorem B3464927 : Blo 1080619 3464927 := bstep (se 1 (by rfl) ⟨2598695, by rfl⟩ : syracuseStep 3464927 = 5197391) B5197391
theorem B2744887 : Blo 1080619 2744887 := bstep (se 1 (by rfl) ⟨2058665, by rfl⟩ : syracuseStep 2744887 = 4117331) B4117331
theorem B1827839 : Blo 1080619 1827839 := bstep (se 1 (by rfl) ⟨1370879, by rfl⟩ : syracuseStep 1827839 = 2741759) B2741759
theorem B15590555 : Blo 1080619 15590555 := bstep (se 1 (by rfl) ⟨11692916, by rfl⟩ : syracuseStep 15590555 = 23385833) B23385833
theorem B2057375 : Blo 1080619 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B14083303 : Blo 1080619 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B1828585 : Blo 1080619 1828585 := bstep (se 2 (by rfl) ⟨685719, by rfl⟩ : syracuseStep 1828585 = 1371439) B1371439
theorem B1829047 : Blo 1080619 1829047 := bstep (se 1 (by rfl) ⟨1371785, by rfl⟩ : syracuseStep 1829047 = 2743571) B2743571
theorem B1829567 : Blo 1080619 1829567 := bstep (se 1 (by rfl) ⟨1372175, by rfl⟩ : syracuseStep 1829567 = 2744351) B2744351
theorem B5204695 : Blo 1080619 5204695 := bstep (se 1 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 5204695 = 7807043) B7807043
theorem B6581159 : Blo 1080619 6581159 := bstep (se 1 (by rfl) ⟨4935869, by rfl⟩ : syracuseStep 6581159 = 9871739) B9871739
theorem B1371163 : Blo 1080619 1371163 := bstep (se 1 (by rfl) ⟨1028372, by rfl⟩ : syracuseStep 1371163 = 2056745) B2056745
theorem B15625385 : Blo 1080619 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B1732079 : Blo 1080619 1732079 := bstep (se 1 (by rfl) ⟨1299059, by rfl⟩ : syracuseStep 1732079 = 2598119) B2598119
theorem B1732207 : Blo 1080619 1732207 := bstep (se 1 (by rfl) ⟨1299155, by rfl⟩ : syracuseStep 1732207 = 2598311) B2598311
theorem B35122855 : Blo 1080619 35122855 := bstep (se 1 (by rfl) ⟨26342141, by rfl⟩ : syracuseStep 35122855 = 52684283) B52684283
theorem B11104847 : Blo 1080619 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B37450439 : Blo 1080619 37450439 := bstep (se 1 (by rfl) ⟨28087829, by rfl⟩ : syracuseStep 37450439 = 56175659) B56175659
theorem B3472091 : Blo 1080619 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B1080623 : Blo 1080619 1080623 := bstep (se 1 (by rfl) ⟨810467, by rfl⟩ : syracuseStep 1080623 = 1620935) B1620935
theorem B5471873 : Blo 1080619 5471873 := bstep (se 2 (by rfl) ⟨2051952, by rfl⟩ : syracuseStep 5471873 = 4103905) B4103905
theorem B1081215 : Blo 1080619 1081215 := bstep (se 1 (by rfl) ⟨810911, by rfl⟩ : syracuseStep 1081215 = 1621823) B1621823
theorem B15794149 : Blo 1080619 15794149 := bstep (se 4 (by rfl) ⟨1480701, by rfl⟩ : syracuseStep 15794149 = 2961403) B2961403
theorem B1081391 : Blo 1080619 1081391 := bstep (se 1 (by rfl) ⟨811043, by rfl⟩ : syracuseStep 1081391 = 1622087) B1622087
theorem B1081671 : Blo 1080619 1081671 := bstep (se 1 (by rfl) ⟨811253, by rfl⟩ : syracuseStep 1081671 = 1622507) B1622507
theorem B6586879 : Blo 1080619 6586879 := bstep (se 1 (by rfl) ⟨4940159, by rfl⟩ : syracuseStep 6586879 = 9880319) B9880319
theorem B1081947 : Blo 1080619 1081947 := bstep (se 1 (by rfl) ⟨811460, by rfl⟩ : syracuseStep 1081947 = 1622921) B1622921
theorem B1082203 : Blo 1080619 1082203 := bstep (se 1 (by rfl) ⟨811652, by rfl⟩ : syracuseStep 1082203 = 1623305) B1623305
theorem B1082459 : Blo 1080619 1082459 := bstep (se 1 (by rfl) ⟨811844, by rfl⟩ : syracuseStep 1082459 = 1623689) B1623689
theorem B1082523 : Blo 1080619 1082523 := bstep (se 1 (by rfl) ⟨811892, by rfl⟩ : syracuseStep 1082523 = 1623785) B1623785
theorem B1082607 : Blo 1080619 1082607 := bstep (se 1 (by rfl) ⟨811955, by rfl⟩ : syracuseStep 1082607 = 1623911) B1623911
theorem B1082783 : Blo 1080619 1082783 := bstep (se 1 (by rfl) ⟨812087, by rfl⟩ : syracuseStep 1082783 = 1624175) B1624175
theorem B1082879 : Blo 1080619 1082879 := bstep (se 1 (by rfl) ⟨812159, by rfl⟩ : syracuseStep 1082879 = 1624319) B1624319
theorem B1082971 : Blo 1080619 1082971 := bstep (se 1 (by rfl) ⟨812228, by rfl⟩ : syracuseStep 1082971 = 1624457) B1624457
theorem B18777737 : Blo 1080619 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B6948767 : Blo 1080619 6948767 := bstep (se 1 (by rfl) ⟨5211575, by rfl⟩ : syracuseStep 6948767 = 10423151) B10423151
theorem B1083303 : Blo 1080619 1083303 := bstep (se 1 (by rfl) ⟨812477, by rfl⟩ : syracuseStep 1083303 = 1624955) B1624955
theorem B1083391 : Blo 1080619 1083391 := bstep (se 1 (by rfl) ⟨812543, by rfl⟩ : syracuseStep 1083391 = 1625087) B1625087
theorem B3082303 : Blo 1080619 3082303 := bstep (se 1 (by rfl) ⟨2311727, by rfl⟩ : syracuseStep 3082303 = 4623455) B4623455
theorem B1084015 : Blo 1080619 1084015 := bstep (se 1 (by rfl) ⟨813011, by rfl⟩ : syracuseStep 1084015 = 1626023) B1626023
theorem B68553497 : Blo 1080619 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B1084575 : Blo 1080619 1084575 := bstep (se 1 (by rfl) ⟨813431, by rfl⟩ : syracuseStep 1084575 = 1626863) B1626863
theorem B1084583 : Blo 1080619 1084583 := bstep (se 1 (by rfl) ⟨813437, by rfl⟩ : syracuseStep 1084583 = 1626875) B1626875
theorem B3083807 : Blo 1080619 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B1216111 : Blo 1080619 1216111 := bstep (se 1 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 1216111 = 1824167) B1824167
theorem B46830473 : Blo 1080619 46830473 := bstep (se 2 (by rfl) ⟨17561427, by rfl⟩ : syracuseStep 46830473 = 35122855) B35122855
theorem B4396103 : Blo 1080619 4396103 := bstep (se 1 (by rfl) ⟨3297077, by rfl⟩ : syracuseStep 4396103 = 6594155) B6594155
theorem B8230409 : Blo 1080619 8230409 := bstep (se 2 (by rfl) ⟨3086403, by rfl⟩ : syracuseStep 8230409 = 6172807) B6172807
theorem B20780873 : Blo 1080619 20780873 := bstep (se 2 (by rfl) ⟨7792827, by rfl⟩ : syracuseStep 20780873 = 15585655) B15585655
theorem B1218559 : Blo 1080619 1218559 := bstep (se 1 (by rfl) ⟨913919, by rfl⟩ : syracuseStep 1218559 = 1827839) B1827839
theorem B10393703 : Blo 1080619 10393703 := bstep (se 1 (by rfl) ⟨7795277, by rfl⟩ : syracuseStep 10393703 = 15590555) B15590555
theorem B1219711 : Blo 1080619 1219711 := bstep (se 1 (by rfl) ⟨914783, by rfl⟩ : syracuseStep 1219711 = 1829567) B1829567
theorem B2432447 : Blo 1080619 2432447 := bstep (se 1 (by rfl) ⟨1824335, by rfl⟩ : syracuseStep 2432447 = 3648671) B3648671
theorem B1154719 : Blo 1080619 1154719 := bstep (se 1 (by rfl) ⟨866039, by rfl⟩ : syracuseStep 1154719 = 1732079) B1732079
theorem B1646287 : Blo 1080619 1646287 := bstep (se 1 (by rfl) ⟨1234715, by rfl⟩ : syracuseStep 1646287 = 2469431) B2469431
theorem B2433185 : Blo 1080619 2433185 := bstep (se 2 (by rfl) ⟨912444, by rfl⟩ : syracuseStep 2433185 = 1824889) B1824889
theorem B2433257 : Blo 1080619 2433257 := bstep (se 2 (by rfl) ⟨912471, by rfl⟩ : syracuseStep 2433257 = 1824943) B1824943
theorem B6856957 : Blo 1080619 6856957 := bstep (se 3 (by rfl) ⟨1285679, by rfl⟩ : syracuseStep 6856957 = 2571359) B2571359
theorem B2434175 : Blo 1080619 2434175 := bstep (se 1 (by rfl) ⟨1825631, by rfl⟩ : syracuseStep 2434175 = 3651263) B3651263
theorem B2434283 : Blo 1080619 2434283 := bstep (se 1 (by rfl) ⟨1825712, by rfl⟩ : syracuseStep 2434283 = 3651425) B3651425
theorem B13707019 : Blo 1080619 13707019 := bstep (se 1 (by rfl) ⟨10280264, by rfl⟩ : syracuseStep 13707019 = 20560529) B20560529
theorem B3647915 : Blo 1080619 3647915 := bstep (se 1 (by rfl) ⟨2735936, by rfl⟩ : syracuseStep 3647915 = 5471873) B5471873
theorem B2437055 : Blo 1080619 2437055 := bstep (se 1 (by rfl) ⟨1827791, by rfl⟩ : syracuseStep 2437055 = 3655583) B3655583
theorem B6926471 : Blo 1080619 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B44478659 : Blo 1080619 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B3650075 : Blo 1080619 3650075 := bstep (se 1 (by rfl) ⟨2737556, by rfl⟩ : syracuseStep 3650075 = 5475113) B5475113
theorem B5485481 : Blo 1080619 5485481 := bstep (se 2 (by rfl) ⟨2057055, by rfl⟩ : syracuseStep 5485481 = 4114111) B4114111
theorem B2438113 : Blo 1080619 2438113 := bstep (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) B1828585
theorem B2438729 : Blo 1080619 2438729 := bstep (se 2 (by rfl) ⟨914523, by rfl⟩ : syracuseStep 2438729 = 1829047) B1829047
theorem B15022279 : Blo 1080619 15022279 := bstep (se 1 (by rfl) ⟨11266709, by rfl⟩ : syracuseStep 15022279 = 22533419) B22533419
theorem B2439647 : Blo 1080619 2439647 := bstep (se 1 (by rfl) ⟨1829735, by rfl⟩ : syracuseStep 2439647 = 3659471) B3659471
theorem B6175223 : Blo 1080619 6175223 := bstep (se 1 (by rfl) ⟨4631417, by rfl⟩ : syracuseStep 6175223 = 9262835) B9262835
theorem B2439935 : Blo 1080619 2439935 := bstep (se 1 (by rfl) ⟨1829951, by rfl⟩ : syracuseStep 2439935 = 3659903) B3659903
theorem B3652775 : Blo 1080619 3652775 := bstep (se 1 (by rfl) ⟨2739581, by rfl⟩ : syracuseStep 3652775 = 5479163) B5479163
theorem B3652883 : Blo 1080619 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B42122699 : Blo 1080619 42122699 := bstep (se 1 (by rfl) ⟨31592024, by rfl⟩ : syracuseStep 42122699 = 63184049) B63184049
theorem B2309609 : Blo 1080619 2309609 := bstep (se 2 (by rfl) ⟨866103, by rfl⟩ : syracuseStep 2309609 = 1732207) B1732207
theorem B2309951 : Blo 1080619 2309951 := bstep (se 1 (by rfl) ⟨1732463, by rfl⟩ : syracuseStep 2309951 = 3464927) B3464927
theorem B2736119 : Blo 1080619 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B1622393 : Blo 1080619 1622393 := bstep (se 2 (by rfl) ⟨608397, by rfl⟩ : syracuseStep 1622393 = 1216795) B1216795
theorem B1622735 : Blo 1080619 1622735 := bstep (se 1 (by rfl) ⟨1217051, by rfl⟩ : syracuseStep 1622735 = 2434103) B2434103
theorem B2737223 : Blo 1080619 2737223 := bstep (se 1 (by rfl) ⟨2052917, by rfl⟩ : syracuseStep 2737223 = 4105835) B4105835
theorem B1623209 : Blo 1080619 1623209 := bstep (se 2 (by rfl) ⟨608703, by rfl⟩ : syracuseStep 1623209 = 1217407) B1217407
theorem B4114415 : Blo 1080619 4114415 := bstep (se 1 (by rfl) ⟨3085811, by rfl⟩ : syracuseStep 4114415 = 6171623) B6171623
theorem B2738407 : Blo 1080619 2738407 := bstep (se 1 (by rfl) ⟨2053805, by rfl⟩ : syracuseStep 2738407 = 4107611) B4107611
theorem B1624559 : Blo 1080619 1624559 := bstep (se 1 (by rfl) ⟨1218419, by rfl⟩ : syracuseStep 1624559 = 2436839) B2436839
theorem B1624859 : Blo 1080619 1624859 := bstep (se 1 (by rfl) ⟨1218644, by rfl⟩ : syracuseStep 1624859 = 2437289) B2437289
theorem B1624943 : Blo 1080619 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B1626089 : Blo 1080619 1626089 := bstep (se 2 (by rfl) ⟨609783, by rfl⟩ : syracuseStep 1626089 = 1219567) B1219567
theorem B2740463 : Blo 1080619 2740463 := bstep (se 1 (by rfl) ⟨2055347, by rfl⟩ : syracuseStep 2740463 = 4110695) B4110695
theorem B4116845 : Blo 1080619 4116845 := bstep (se 3 (by rfl) ⟨771908, by rfl⟩ : syracuseStep 4116845 = 1543817) B1543817
theorem B2314727 : Blo 1080619 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B2740979 : Blo 1080619 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B1626911 : Blo 1080619 1626911 := bstep (se 1 (by rfl) ⟨1220183, by rfl⟩ : syracuseStep 1626911 = 2440367) B2440367
theorem B3658823 : Blo 1080619 3658823 := bstep (se 1 (by rfl) ⟨2744117, by rfl⟩ : syracuseStep 3658823 = 5488235) B5488235
theorem B21058865 : Blo 1080619 21058865 := bstep (se 2 (by rfl) ⟨7897074, by rfl⟩ : syracuseStep 21058865 = 15794149) B15794149
theorem B169039223 : Blo 1080619 169039223 := bstep (se 1 (by rfl) ⟨126779417, by rfl⟩ : syracuseStep 169039223 = 253558835) B253558835
theorem B5002991 : Blo 1080619 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B3659849 : Blo 1080619 3659849 := bstep (se 2 (by rfl) ⟨1372443, by rfl⟩ : syracuseStep 3659849 = 2744887) B2744887
theorem B17586341 : Blo 1080619 17586341 := bstep (se 4 (by rfl) ⟨1648719, by rfl⟩ : syracuseStep 17586341 = 3297439) B3297439
theorem B1825375 : Blo 1080619 1825375 := bstep (se 1 (by rfl) ⟨1369031, by rfl⟩ : syracuseStep 1825375 = 2738063) B2738063
theorem B2055431 : Blo 1080619 2055431 := bstep (se 1 (by rfl) ⟨1541573, by rfl⟩ : syracuseStep 2055431 = 3083147) B3083147
theorem B22798367 : Blo 1080619 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B9265225 : Blo 1080619 9265225 := bstep (se 2 (by rfl) ⟨3474459, by rfl⟩ : syracuseStep 9265225 = 6948919) B6948919
theorem B24994115 : Blo 1080619 24994115 := bstep (se 1 (by rfl) ⟨18745586, by rfl⟩ : syracuseStep 24994115 = 37491173) B37491173
theorem B5202463 : Blo 1080619 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B11100905 : Blo 1080619 11100905 := bstep (se 2 (by rfl) ⟨4162839, by rfl⟩ : syracuseStep 11100905 = 8325679) B8325679
theorem B6939593 : Blo 1080619 6939593 := bstep (se 2 (by rfl) ⟨2602347, by rfl⟩ : syracuseStep 6939593 = 5204695) B5204695
theorem B3466361 : Blo 1080619 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B5924123 : Blo 1080619 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B1828217 : Blo 1080619 1828217 := bstep (se 2 (by rfl) ⟨685581, by rfl⟩ : syracuseStep 1828217 = 1371163) B1371163
theorem B3468233 : Blo 1080619 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B1371583 : Blo 1080619 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B4616347 : Blo 1080619 4616347 := bstep (se 1 (by rfl) ⟨3462260, by rfl⟩ : syracuseStep 4616347 = 6924521) B6924521
theorem B4387439 : Blo 1080619 4387439 := bstep (se 1 (by rfl) ⟨3290579, by rfl⟩ : syracuseStep 4387439 = 6581159) B6581159
theorem B10416923 : Blo 1080619 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B5863067 : Blo 1080619 5863067 := bstep (se 1 (by rfl) ⟨4397300, by rfl⟩ : syracuseStep 5863067 = 8794601) B8794601
theorem B2193103 : Blo 1080619 2193103 := bstep (se 1 (by rfl) ⟨1644827, by rfl⟩ : syracuseStep 2193103 = 3289655) B3289655
theorem B7403231 : Blo 1080619 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B24966959 : Blo 1080619 24966959 := bstep (se 1 (by rfl) ⟨18725219, by rfl⟩ : syracuseStep 24966959 = 37450439) B37450439
theorem B3078557 : Blo 1080619 3078557 := bstep (se 3 (by rfl) ⟨577229, by rfl⟩ : syracuseStep 3078557 = 1154459) B1154459
theorem B1080703 : Blo 1080619 1080703 := bstep (se 1 (by rfl) ⟨810527, by rfl⟩ : syracuseStep 1080703 = 1621055) B1621055
theorem B1080767 : Blo 1080619 1080767 := bstep (se 1 (by rfl) ⟨810575, by rfl⟩ : syracuseStep 1080767 = 1621151) B1621151
theorem B1081023 : Blo 1080619 1081023 := bstep (se 1 (by rfl) ⟨810767, by rfl⟩ : syracuseStep 1081023 = 1621535) B1621535
theorem B12353633 : Blo 1080619 12353633 := bstep (se 2 (by rfl) ⟨4632612, by rfl⟩ : syracuseStep 12353633 = 9265225) B9265225
theorem B1081595 : Blo 1080619 1081595 := bstep (se 1 (by rfl) ⟨811196, by rfl⟩ : syracuseStep 1081595 = 1622393) B1622393
theorem B1081823 : Blo 1080619 1081823 := bstep (se 1 (by rfl) ⟨811367, by rfl⟩ : syracuseStep 1081823 = 1622735) B1622735
theorem B8782505 : Blo 1080619 8782505 := bstep (se 2 (by rfl) ⟨3293439, by rfl⟩ : syracuseStep 8782505 = 6586879) B6586879
theorem B1082139 : Blo 1080619 1082139 := bstep (se 1 (by rfl) ⟨811604, by rfl⟩ : syracuseStep 1082139 = 1623209) B1623209
theorem B80118821 : Blo 1080619 80118821 := bstep (se 4 (by rfl) ⟨7511139, by rfl⟩ : syracuseStep 80118821 = 15022279) B15022279
theorem B12518491 : Blo 1080619 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B36570437 : Blo 1080619 36570437 := bstep (se 4 (by rfl) ⟨3428478, by rfl⟩ : syracuseStep 36570437 = 6856957) B6856957
theorem B1083039 : Blo 1080619 1083039 := bstep (se 1 (by rfl) ⟨812279, by rfl⟩ : syracuseStep 1083039 = 1624559) B1624559
theorem B1083239 : Blo 1080619 1083239 := bstep (se 1 (by rfl) ⟨812429, by rfl⟩ : syracuseStep 1083239 = 1624859) B1624859
theorem B1083295 : Blo 1080619 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B1084059 : Blo 1080619 1084059 := bstep (se 1 (by rfl) ⟨813044, by rfl⟩ : syracuseStep 1084059 = 1626089) B1626089
theorem B9243629 : Blo 1080619 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B1543151 : Blo 1080619 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B1084607 : Blo 1080619 1084607 := bstep (se 1 (by rfl) ⟨813455, by rfl⟩ : syracuseStep 1084607 = 1626911) B1626911
theorem B112692815 : Blo 1080619 112692815 := bstep (se 1 (by rfl) ⟨84519611, by rfl⟩ : syracuseStep 112692815 = 169039223) B169039223
theorem B4626395 : Blo 1080619 4626395 := bstep (se 1 (by rfl) ⟨3469796, by rfl⟩ : syracuseStep 4626395 = 6939593) B6939593
theorem B1218811 : Blo 1080619 1218811 := bstep (se 1 (by rfl) ⟨914108, by rfl⟩ : syracuseStep 1218811 = 1828217) B1828217
theorem B3250817 : Blo 1080619 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B2431943 : Blo 1080619 2431943 := bstep (se 1 (by rfl) ⟨1823957, by rfl⟩ : syracuseStep 2431943 = 3647915) B3647915
theorem B2924137 : Blo 1080619 2924137 := bstep (se 2 (by rfl) ⟨1096551, by rfl⟩ : syracuseStep 2924137 = 2193103) B2193103
theorem B2433383 : Blo 1080619 2433383 := bstep (se 1 (by rfl) ⟨1825037, by rfl⟩ : syracuseStep 2433383 = 3650075) B3650075
theorem B2924959 : Blo 1080619 2924959 := bstep (se 1 (by rfl) ⟨2193719, by rfl⟩ : syracuseStep 2924959 = 4387439) B4387439
theorem B2433833 : Blo 1080619 2433833 := bstep (se 2 (by rfl) ⟨912687, by rfl⟩ : syracuseStep 2433833 = 1825375) B1825375
theorem B3908711 : Blo 1080619 3908711 := bstep (se 1 (by rfl) ⟨2931533, by rfl⟩ : syracuseStep 3908711 = 5863067) B5863067
theorem B2435183 : Blo 1080619 2435183 := bstep (se 1 (by rfl) ⟨1826387, by rfl⟩ : syracuseStep 2435183 = 3652775) B3652775
theorem B2435255 : Blo 1080619 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B4632511 : Blo 1080619 4632511 := bstep (se 1 (by rfl) ⟨3474383, by rfl⟩ : syracuseStep 4632511 = 6948767) B6948767
theorem B4109737 : Blo 1080619 4109737 := bstep (se 2 (by rfl) ⟨1541151, by rfl⟩ : syracuseStep 4109737 = 3082303) B3082303
theorem B3651209 : Blo 1080619 3651209 := bstep (se 2 (by rfl) ⟨1369203, by rfl⟩ : syracuseStep 3651209 = 2738407) B2738407
theorem B2439215 : Blo 1080619 2439215 := bstep (se 1 (by rfl) ⟨1829411, by rfl⟩ : syracuseStep 2439215 = 3658823) B3658823
theorem B2930735 : Blo 1080619 2930735 := bstep (se 1 (by rfl) ⟨2198051, by rfl⟩ : syracuseStep 2930735 = 4396103) B4396103
theorem B14039243 : Blo 1080619 14039243 := bstep (se 1 (by rfl) ⟨10529432, by rfl⟩ : syracuseStep 14039243 = 21058865) B21058865
theorem B5486939 : Blo 1080619 5486939 := bstep (se 1 (by rfl) ⟨4115204, by rfl⟩ : syracuseStep 5486939 = 8230409) B8230409
theorem B2439899 : Blo 1080619 2439899 := bstep (se 1 (by rfl) ⟨1829924, by rfl⟩ : syracuseStep 2439899 = 3659849) B3659849
theorem B6929135 : Blo 1080619 6929135 := bstep (se 1 (by rfl) ⟨5196851, by rfl⟩ : syracuseStep 6929135 = 10393703) B10393703
theorem B1621481 : Blo 1080619 1621481 := bstep (se 2 (by rfl) ⟨608055, by rfl⟩ : syracuseStep 1621481 = 1216111) B1216111
theorem B1621631 : Blo 1080619 1621631 := bstep (se 1 (by rfl) ⟨1216223, by rfl⟩ : syracuseStep 1621631 = 2432447) B2432447
theorem B1622123 : Blo 1080619 1622123 := bstep (se 1 (by rfl) ⟨1216592, by rfl⟩ : syracuseStep 1622123 = 2433185) B2433185
theorem B1622171 : Blo 1080619 1622171 := bstep (se 1 (by rfl) ⟨1216628, by rfl⟩ : syracuseStep 1622171 = 2433257) B2433257
theorem B16662743 : Blo 1080619 16662743 := bstep (se 1 (by rfl) ⟨12497057, by rfl⟩ : syracuseStep 16662743 = 24994115) B24994115
theorem B1622783 : Blo 1080619 1622783 := bstep (se 1 (by rfl) ⟨1217087, by rfl⟩ : syracuseStep 1622783 = 2434175) B2434175
theorem B1622855 : Blo 1080619 1622855 := bstep (se 1 (by rfl) ⟨1217141, by rfl⟩ : syracuseStep 1622855 = 2434283) B2434283
theorem B3949415 : Blo 1080619 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B2312155 : Blo 1080619 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B1624703 : Blo 1080619 1624703 := bstep (se 1 (by rfl) ⟨1218527, by rfl⟩ : syracuseStep 1624703 = 2437055) B2437055
theorem B1624745 : Blo 1080619 1624745 := bstep (se 2 (by rfl) ⟨609279, by rfl⟩ : syracuseStep 1624745 = 1218559) B1218559
theorem B3656987 : Blo 1080619 3656987 := bstep (se 1 (by rfl) ⟨2742740, by rfl⟩ : syracuseStep 3656987 = 5485481) B5485481
theorem B1625819 : Blo 1080619 1625819 := bstep (se 1 (by rfl) ⟨1219364, by rfl⟩ : syracuseStep 1625819 = 2438729) B2438729
theorem B4935487 : Blo 1080619 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B1626281 : Blo 1080619 1626281 := bstep (se 2 (by rfl) ⟨609855, by rfl⟩ : syracuseStep 1626281 = 1219711) B1219711
theorem B2052371 : Blo 1080619 2052371 := bstep (se 1 (by rfl) ⟨1539278, by rfl⟩ : syracuseStep 2052371 = 3078557) B3078557
theorem B1626431 : Blo 1080619 1626431 := bstep (se 1 (by rfl) ⟨1219823, by rfl⟩ : syracuseStep 1626431 = 2439647) B2439647
theorem B4116815 : Blo 1080619 4116815 := bstep (se 1 (by rfl) ⟨3087611, by rfl⟩ : syracuseStep 4116815 = 6175223) B6175223
theorem B1626623 : Blo 1080619 1626623 := bstep (se 1 (by rfl) ⟨1219967, by rfl⟩ : syracuseStep 1626623 = 2439935) B2439935
theorem B1824079 : Blo 1080619 1824079 := bstep (se 1 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 1824079 = 2736119) B2736119
theorem B6936617 : Blo 1080619 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B1824815 : Blo 1080619 1824815 := bstep (se 1 (by rfl) ⟨1368611, by rfl⟩ : syracuseStep 1824815 = 2737223) B2737223
theorem B2742943 : Blo 1080619 2742943 := bstep (se 1 (by rfl) ⟨2057207, by rfl⟩ : syracuseStep 2742943 = 4114415) B4114415
theorem B18276025 : Blo 1080619 18276025 := bstep (se 2 (by rfl) ⟨6853509, by rfl⟩ : syracuseStep 18276025 = 13707019) B13707019
theorem B2055871 : Blo 1080619 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B1826975 : Blo 1080619 1826975 := bstep (se 1 (by rfl) ⟨1370231, by rfl⟩ : syracuseStep 1826975 = 2740463) B2740463
theorem B2744563 : Blo 1080619 2744563 := bstep (se 1 (by rfl) ⟨2058422, by rfl⟩ : syracuseStep 2744563 = 4116845) B4116845
theorem B1827319 : Blo 1080619 1827319 := bstep (se 1 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 1827319 = 2740979) B2740979
theorem B31220315 : Blo 1080619 31220315 := bstep (se 1 (by rfl) ⟨23415236, by rfl⟩ : syracuseStep 31220315 = 46830473) B46830473
theorem B3335327 : Blo 1080619 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B13853915 : Blo 1080619 13853915 := bstep (se 1 (by rfl) ⟨10390436, by rfl⟩ : syracuseStep 13853915 = 20780873) B20780873
theorem B11724227 : Blo 1080619 11724227 := bstep (se 1 (by rfl) ⟨8793170, by rfl⟩ : syracuseStep 11724227 = 17586341) B17586341
theorem B1828777 : Blo 1080619 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B66578557 : Blo 1080619 66578557 := bstep (se 3 (by rfl) ⟨12483479, by rfl⟩ : syracuseStep 66578557 = 24966959) B24966959
theorem B1370287 : Blo 1080619 1370287 := bstep (se 1 (by rfl) ⟨1027715, by rfl⟩ : syracuseStep 1370287 = 2055431) B2055431
theorem B15198911 : Blo 1080619 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B6155129 : Blo 1080619 6155129 := bstep (se 2 (by rfl) ⟨2308173, by rfl⟩ : syracuseStep 6155129 = 4616347) B4616347
theorem B7400603 : Blo 1080619 7400603 := bstep (se 1 (by rfl) ⟨5550452, by rfl⟩ : syracuseStep 7400603 = 11100905) B11100905
theorem B182809325 : Blo 1080619 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B4617647 : Blo 1080619 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B29652439 : Blo 1080619 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B6944615 : Blo 1080619 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B6158501 : Blo 1080619 6158501 := bstep (se 4 (by rfl) ⟨577359, by rfl⟩ : syracuseStep 6158501 = 1154719) B1154719
theorem B8780197 : Blo 1080619 8780197 := bstep (se 4 (by rfl) ⟨823143, by rfl⟩ : syracuseStep 8780197 = 1646287) B1646287
theorem B28081799 : Blo 1080619 28081799 := bstep (se 1 (by rfl) ⟨21061349, by rfl⟩ : syracuseStep 28081799 = 42122699) B42122699
theorem B1539739 : Blo 1080619 1539739 := bstep (se 1 (by rfl) ⟨1154804, by rfl⟩ : syracuseStep 1539739 = 2309609) B2309609
theorem B1539967 : Blo 1080619 1539967 := bstep (se 1 (by rfl) ⟨1154975, by rfl⟩ : syracuseStep 1539967 = 2309951) B2309951
theorem B1081415 : Blo 1080619 1081415 := bstep (se 1 (by rfl) ⟨811061, by rfl⟩ : syracuseStep 1081415 = 1622123) B1622123
theorem B1081447 : Blo 1080619 1081447 := bstep (se 1 (by rfl) ⟨811085, by rfl⟩ : syracuseStep 1081447 = 1622171) B1622171
theorem B11108495 : Blo 1080619 11108495 := bstep (se 1 (by rfl) ⟨8331371, by rfl⟩ : syracuseStep 11108495 = 16662743) B16662743
theorem B1081855 : Blo 1080619 1081855 := bstep (se 1 (by rfl) ⟨811391, by rfl⟩ : syracuseStep 1081855 = 1622783) B1622783
theorem B3899945 : Blo 1080619 3899945 := bstep (se 2 (by rfl) ⟨1462479, by rfl⟩ : syracuseStep 3899945 = 2924959) B2924959
theorem B1081903 : Blo 1080619 1081903 := bstep (se 1 (by rfl) ⟨811427, by rfl⟩ : syracuseStep 1081903 = 1622855) B1622855
theorem B53412547 : Blo 1080619 53412547 := bstep (se 1 (by rfl) ⟨40059410, by rfl⟩ : syracuseStep 53412547 = 80118821) B80118821
theorem B24380291 : Blo 1080619 24380291 := bstep (se 1 (by rfl) ⟨18285218, by rfl⟩ : syracuseStep 24380291 = 36570437) B36570437
theorem B1083135 : Blo 1080619 1083135 := bstep (se 1 (by rfl) ⟨812351, by rfl⟩ : syracuseStep 1083135 = 1624703) B1624703
theorem B1083163 : Blo 1080619 1083163 := bstep (se 1 (by rfl) ⟨812372, by rfl⟩ : syracuseStep 1083163 = 1624745) B1624745
theorem B6162419 : Blo 1080619 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B1083879 : Blo 1080619 1083879 := bstep (se 1 (by rfl) ⟨812909, by rfl⟩ : syracuseStep 1083879 = 1625819) B1625819
theorem B3082873 : Blo 1080619 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B1084187 : Blo 1080619 1084187 := bstep (se 1 (by rfl) ⟨813140, by rfl⟩ : syracuseStep 1084187 = 1626281) B1626281
theorem B88771409 : Blo 1080619 88771409 := bstep (se 2 (by rfl) ⟨33289278, by rfl⟩ : syracuseStep 88771409 = 66578557) B66578557
theorem B1084287 : Blo 1080619 1084287 := bstep (se 1 (by rfl) ⟨813215, by rfl⟩ : syracuseStep 1084287 = 1626431) B1626431
theorem B1084415 : Blo 1080619 1084415 := bstep (se 1 (by rfl) ⟨813311, by rfl⟩ : syracuseStep 1084415 = 1626623) B1626623
theorem B3084263 : Blo 1080619 3084263 := bstep (se 1 (by rfl) ⟨2313197, by rfl⟩ : syracuseStep 3084263 = 4626395) B4626395
theorem B1216543 : Blo 1080619 1216543 := bstep (se 1 (by rfl) ⟨912407, by rfl⟩ : syracuseStep 1216543 = 1824815) B1824815
theorem B2167211 : Blo 1080619 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B1217983 : Blo 1080619 1217983 := bstep (se 1 (by rfl) ⟨913487, by rfl⟩ : syracuseStep 1217983 = 1826975) B1826975
theorem B20813543 : Blo 1080619 20813543 := bstep (se 1 (by rfl) ⟨15610157, by rfl⟩ : syracuseStep 20813543 = 31220315) B31220315
theorem B2432105 : Blo 1080619 2432105 := bstep (se 2 (by rfl) ⟨912039, by rfl⟩ : syracuseStep 2432105 = 1824079) B1824079
theorem B10132607 : Blo 1080619 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B5479649 : Blo 1080619 5479649 := bstep (se 2 (by rfl) ⟨2054868, by rfl⟩ : syracuseStep 5479649 = 4109737) B4109737
theorem B4103419 : Blo 1080619 4103419 := bstep (se 1 (by rfl) ⟨3077564, by rfl⟩ : syracuseStep 4103419 = 6155129) B6155129
theorem B19734941 : Blo 1080619 19734941 := bstep (se 3 (by rfl) ⟨3700301, by rfl⟩ : syracuseStep 19734941 = 7400603) B7400603
theorem B121872883 : Blo 1080619 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B11706929 : Blo 1080619 11706929 := bstep (se 2 (by rfl) ⟨4390098, by rfl⟩ : syracuseStep 11706929 = 8780197) B8780197
theorem B2434139 : Blo 1080619 2434139 := bstep (se 1 (by rfl) ⟨1825604, by rfl⟩ : syracuseStep 2434139 = 3651209) B3651209
theorem B4629743 : Blo 1080619 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B4105667 : Blo 1080619 4105667 := bstep (se 1 (by rfl) ⟨3079250, by rfl⟩ : syracuseStep 4105667 = 6158501) B6158501
theorem B18721199 : Blo 1080619 18721199 := bstep (se 1 (by rfl) ⟨14040899, by rfl⟩ : syracuseStep 18721199 = 28081799) B28081799
theorem B8235755 : Blo 1080619 8235755 := bstep (se 1 (by rfl) ⟨6176816, by rfl⟩ : syracuseStep 8235755 = 12353633) B12353633
theorem B2632943 : Blo 1080619 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B2436425 : Blo 1080619 2436425 := bstep (se 2 (by rfl) ⟨913659, by rfl⟩ : syracuseStep 2436425 = 1827319) B1827319
theorem B16691321 : Blo 1080619 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B2437991 : Blo 1080619 2437991 := bstep (se 1 (by rfl) ⟨1828493, by rfl⟩ : syracuseStep 2437991 = 3656987) B3656987
theorem B2438369 : Blo 1080619 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B1621295 : Blo 1080619 1621295 := bstep (se 1 (by rfl) ⟨1215971, by rfl⟩ : syracuseStep 1621295 = 2431943) B2431943
theorem B6176681 : Blo 1080619 6176681 := bstep (se 2 (by rfl) ⟨2316255, by rfl⟩ : syracuseStep 6176681 = 4632511) B4632511
theorem B18497645 : Blo 1080619 18497645 := bstep (se 3 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 18497645 = 6936617) B6936617
theorem B1622255 : Blo 1080619 1622255 := bstep (se 1 (by rfl) ⟨1216691, by rfl⟩ : syracuseStep 1622255 = 2433383) B2433383
theorem B1622555 : Blo 1080619 1622555 := bstep (se 1 (by rfl) ⟨1216916, by rfl⟩ : syracuseStep 1622555 = 2433833) B2433833
theorem B2605807 : Blo 1080619 2605807 := bstep (se 1 (by rfl) ⟨1954355, by rfl⟩ : syracuseStep 2605807 = 3908711) B3908711
theorem B7816151 : Blo 1080619 7816151 := bstep (se 1 (by rfl) ⟨5862113, by rfl⟩ : syracuseStep 7816151 = 11724227) B11724227
theorem B1623455 : Blo 1080619 1623455 := bstep (se 1 (by rfl) ⟨1217591, by rfl⟩ : syracuseStep 1623455 = 2435183) B2435183
theorem B1623503 : Blo 1080619 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B39536585 : Blo 1080619 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B4115069 : Blo 1080619 4115069 := bstep (se 3 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 4115069 = 1543151) B1543151
theorem B1625081 : Blo 1080619 1625081 := bstep (se 2 (by rfl) ⟨609405, by rfl⟩ : syracuseStep 1625081 = 1218811) B1218811
theorem B8211941 : Blo 1080619 8211941 := bstep (se 4 (by rfl) ⟨769869, by rfl⟩ : syracuseStep 8211941 = 1539739) B1539739
theorem B3657257 : Blo 1080619 3657257 := bstep (se 2 (by rfl) ⟨1371471, by rfl⟩ : syracuseStep 3657257 = 2742943) B2742943
theorem B1626143 : Blo 1080619 1626143 := bstep (se 1 (by rfl) ⟨1219607, by rfl⟩ : syracuseStep 1626143 = 2439215) B2439215
theorem B1953823 : Blo 1080619 1953823 := bstep (se 1 (by rfl) ⟨1465367, by rfl⟩ : syracuseStep 1953823 = 2930735) B2930735
theorem B9359495 : Blo 1080619 9359495 := bstep (se 1 (by rfl) ⟨7019621, by rfl⟩ : syracuseStep 9359495 = 14039243) B14039243
theorem B3657959 : Blo 1080619 3657959 := bstep (se 1 (by rfl) ⟨2743469, by rfl⟩ : syracuseStep 3657959 = 5486939) B5486939
theorem B1626599 : Blo 1080619 1626599 := bstep (se 1 (by rfl) ⟨1219949, by rfl⟩ : syracuseStep 1626599 = 2439899) B2439899
theorem B24368033 : Blo 1080619 24368033 := bstep (se 2 (by rfl) ⟨9138012, by rfl⟩ : syracuseStep 24368033 = 18276025) B18276025
theorem B2741161 : Blo 1080619 2741161 := bstep (se 2 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 2741161 = 2055871) B2055871
theorem B2053289 : Blo 1080619 2053289 := bstep (se 2 (by rfl) ⟨769983, by rfl⟩ : syracuseStep 2053289 = 1539967) B1539967
theorem B3659417 : Blo 1080619 3659417 := bstep (se 2 (by rfl) ⟨1372281, by rfl⟩ : syracuseStep 3659417 = 2744563) B2744563
theorem B5855003 : Blo 1080619 5855003 := bstep (se 1 (by rfl) ⟨4391252, by rfl⟩ : syracuseStep 5855003 = 8782505) B8782505
theorem B75128543 : Blo 1080619 75128543 := bstep (se 1 (by rfl) ⟨56346407, by rfl⟩ : syracuseStep 75128543 = 112692815) B112692815
theorem B1368247 : Blo 1080619 1368247 := bstep (se 1 (by rfl) ⟨1026185, by rfl⟩ : syracuseStep 1368247 = 2052371) B2052371
theorem B2744543 : Blo 1080619 2744543 := bstep (se 1 (by rfl) ⟨2058407, by rfl⟩ : syracuseStep 2744543 = 4116815) B4116815
theorem B1827049 : Blo 1080619 1827049 := bstep (se 2 (by rfl) ⟨685143, by rfl⟩ : syracuseStep 1827049 = 1370287) B1370287
theorem B6580649 : Blo 1080619 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B2223551 : Blo 1080619 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B9235943 : Blo 1080619 9235943 := bstep (se 1 (by rfl) ⟨6926957, by rfl⟩ : syracuseStep 9235943 = 13853915) B13853915
theorem B3078431 : Blo 1080619 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B4619423 : Blo 1080619 4619423 := bstep (se 1 (by rfl) ⟨3464567, by rfl⟩ : syracuseStep 4619423 = 6929135) B6929135
theorem B3898849 : Blo 1080619 3898849 := bstep (se 2 (by rfl) ⟨1462068, by rfl⟩ : syracuseStep 3898849 = 2924137) B2924137
theorem B1080987 : Blo 1080619 1080987 := bstep (se 1 (by rfl) ⟨810740, by rfl⟩ : syracuseStep 1080987 = 1621481) B1621481
theorem B1081087 : Blo 1080619 1081087 := bstep (se 1 (by rfl) ⟨810815, by rfl⟩ : syracuseStep 1081087 = 1621631) B1621631
theorem B7405663 : Blo 1080619 7405663 := bstep (se 1 (by rfl) ⟨5554247, by rfl⟩ : syracuseStep 7405663 = 11108495) B11108495
theorem B1081503 : Blo 1080619 1081503 := bstep (se 1 (by rfl) ⟨811127, by rfl⟩ : syracuseStep 1081503 = 1622255) B1622255
theorem B1081703 : Blo 1080619 1081703 := bstep (se 1 (by rfl) ⟨811277, by rfl⟩ : syracuseStep 1081703 = 1622555) B1622555
theorem B5210767 : Blo 1080619 5210767 := bstep (se 1 (by rfl) ⟨3908075, by rfl⟩ : syracuseStep 5210767 = 7816151) B7816151
theorem B162497177 : Blo 1080619 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B1082303 : Blo 1080619 1082303 := bstep (se 1 (by rfl) ⟨811727, by rfl⟩ : syracuseStep 1082303 = 1623455) B1623455
theorem B1082335 : Blo 1080619 1082335 := bstep (se 1 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 1082335 = 1623503) B1623503
theorem B3474409 : Blo 1080619 3474409 := bstep (se 2 (by rfl) ⟨1302903, by rfl⟩ : syracuseStep 3474409 = 2605807) B2605807
theorem B59180939 : Blo 1080619 59180939 := bstep (se 1 (by rfl) ⟨44385704, by rfl⟩ : syracuseStep 59180939 = 88771409) B88771409
theorem B1083387 : Blo 1080619 1083387 := bstep (se 1 (by rfl) ⟨812540, by rfl⟩ : syracuseStep 1083387 = 1625081) B1625081
theorem B5474627 : Blo 1080619 5474627 := bstep (se 1 (by rfl) ⟨4105970, by rfl⟩ : syracuseStep 5474627 = 8211941) B8211941
theorem B65014109 : Blo 1080619 65014109 := bstep (se 3 (by rfl) ⟨12190145, by rfl⟩ : syracuseStep 65014109 = 24380291) B24380291
theorem B1084095 : Blo 1080619 1084095 := bstep (se 1 (by rfl) ⟨813071, by rfl⟩ : syracuseStep 1084095 = 1626143) B1626143
theorem B1444807 : Blo 1080619 1444807 := bstep (se 1 (by rfl) ⟨1083605, by rfl⟩ : syracuseStep 1444807 = 2167211) B2167211
theorem B1084399 : Blo 1080619 1084399 := bstep (se 1 (by rfl) ⟨813299, by rfl⟩ : syracuseStep 1084399 = 1626599) B1626599
theorem B5475437 : Blo 1080619 5475437 := bstep (se 3 (by rfl) ⟨1026644, by rfl⟩ : syracuseStep 5475437 = 2053289) B2053289
theorem B3903335 : Blo 1080619 3903335 := bstep (se 1 (by rfl) ⟨2927501, by rfl⟩ : syracuseStep 3903335 = 5855003) B5855003
theorem B6755071 : Blo 1080619 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B7804619 : Blo 1080619 7804619 := bstep (se 1 (by rfl) ⟨5853464, by rfl⟩ : syracuseStep 7804619 = 11706929) B11706929
theorem B3086495 : Blo 1080619 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B12331763 : Blo 1080619 12331763 := bstep (se 1 (by rfl) ⟨9248822, by rfl⟩ : syracuseStep 12331763 = 18497645) B18497645
theorem B2436065 : Blo 1080619 2436065 := bstep (se 2 (by rfl) ⟨913524, by rfl⟩ : syracuseStep 2436065 = 1827049) B1827049
theorem B71216729 : Blo 1080619 71216729 := bstep (se 2 (by rfl) ⟨26706273, by rfl⟩ : syracuseStep 71216729 = 53412547) B53412547
theorem B26357723 : Blo 1080619 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B4108279 : Blo 1080619 4108279 := bstep (se 1 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 4108279 = 6162419) B6162419
theorem B10399853 : Blo 1080619 10399853 := bstep (se 3 (by rfl) ⟨1949972, by rfl⟩ : syracuseStep 10399853 = 3899945) B3899945
theorem B2438171 : Blo 1080619 2438171 := bstep (se 1 (by rfl) ⟨1828628, by rfl⟩ : syracuseStep 2438171 = 3657257) B3657257
theorem B6239663 : Blo 1080619 6239663 := bstep (se 1 (by rfl) ⟨4679747, by rfl⟩ : syracuseStep 6239663 = 9359495) B9359495
theorem B2438639 : Blo 1080619 2438639 := bstep (se 1 (by rfl) ⟨1828979, by rfl⟩ : syracuseStep 2438639 = 3657959) B3657959
theorem B4110497 : Blo 1080619 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2439611 : Blo 1080619 2439611 := bstep (se 1 (by rfl) ⟨1829708, by rfl⟩ : syracuseStep 2439611 = 3659417) B3659417
theorem B13875695 : Blo 1080619 13875695 := bstep (se 1 (by rfl) ⟨10406771, by rfl⟩ : syracuseStep 13875695 = 20813543) B20813543
theorem B1621403 : Blo 1080619 1621403 := bstep (se 1 (by rfl) ⟨1216052, by rfl⟩ : syracuseStep 1621403 = 2432105) B2432105
theorem B3653099 : Blo 1080619 3653099 := bstep (se 1 (by rfl) ⟨2739824, by rfl⟩ : syracuseStep 3653099 = 5479649) B5479649
theorem B50085695 : Blo 1080619 50085695 := bstep (se 1 (by rfl) ⟨37564271, by rfl⟩ : syracuseStep 50085695 = 75128543) B75128543
theorem B1622057 : Blo 1080619 1622057 := bstep (se 2 (by rfl) ⟨608271, by rfl⟩ : syracuseStep 1622057 = 1216543) B1216543
theorem B2605097 : Blo 1080619 2605097 := bstep (se 2 (by rfl) ⟨976911, by rfl⟩ : syracuseStep 2605097 = 1953823) B1953823
theorem B13156627 : Blo 1080619 13156627 := bstep (se 1 (by rfl) ⟨9867470, by rfl⟩ : syracuseStep 13156627 = 19734941) B19734941
theorem B1622759 : Blo 1080619 1622759 := bstep (se 1 (by rfl) ⟨1217069, by rfl⟩ : syracuseStep 1622759 = 2434139) B2434139
theorem B2737111 : Blo 1080619 2737111 := bstep (se 1 (by rfl) ⟨2052833, by rfl⟩ : syracuseStep 2737111 = 4105667) B4105667
theorem B17548397 : Blo 1080619 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B3654881 : Blo 1080619 3654881 := bstep (se 2 (by rfl) ⟨1370580, by rfl⟩ : syracuseStep 3654881 = 2741161) B2741161
theorem B5490503 : Blo 1080619 5490503 := bstep (se 1 (by rfl) ⟨4117877, by rfl⟩ : syracuseStep 5490503 = 8235755) B8235755
theorem B1623977 : Blo 1080619 1623977 := bstep (se 2 (by rfl) ⟨608991, by rfl⟩ : syracuseStep 1623977 = 1217983) B1217983
theorem B1755295 : Blo 1080619 1755295 := bstep (se 1 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 1755295 = 2632943) B2632943
theorem B1624283 : Blo 1080619 1624283 := bstep (se 1 (by rfl) ⟨1218212, by rfl⟩ : syracuseStep 1624283 = 2436425) B2436425
theorem B11127547 : Blo 1080619 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B1625327 : Blo 1080619 1625327 := bstep (se 1 (by rfl) ⟨1218995, by rfl⟩ : syracuseStep 1625327 = 2437991) B2437991
theorem B1625579 : Blo 1080619 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B2052287 : Blo 1080619 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B5198465 : Blo 1080619 5198465 := bstep (se 2 (by rfl) ⟨1949424, by rfl⟩ : syracuseStep 5198465 = 3898849) B3898849
theorem B4117787 : Blo 1080619 4117787 := bstep (se 1 (by rfl) ⟨3088340, by rfl⟩ : syracuseStep 4117787 = 6176681) B6176681
theorem B1824329 : Blo 1080619 1824329 := bstep (se 2 (by rfl) ⟨684123, by rfl⟩ : syracuseStep 1824329 = 1368247) B1368247
theorem B2743379 : Blo 1080619 2743379 := bstep (se 1 (by rfl) ⟨2057534, by rfl⟩ : syracuseStep 2743379 = 4115069) B4115069
theorem B2056175 : Blo 1080619 2056175 := bstep (se 1 (by rfl) ⟨1542131, by rfl⟩ : syracuseStep 2056175 = 3084263) B3084263
theorem B16245355 : Blo 1080619 16245355 := bstep (se 1 (by rfl) ⟨12184016, by rfl⟩ : syracuseStep 16245355 = 24368033) B24368033
theorem B1829695 : Blo 1080619 1829695 := bstep (se 1 (by rfl) ⟨1372271, by rfl⟩ : syracuseStep 1829695 = 2744543) B2744543
theorem B12480799 : Blo 1080619 12480799 := bstep (se 1 (by rfl) ⟨9360599, by rfl⟩ : syracuseStep 12480799 = 18721199) B18721199
theorem B6157295 : Blo 1080619 6157295 := bstep (se 1 (by rfl) ⟨4617971, by rfl⟩ : syracuseStep 6157295 = 9235943) B9235943
theorem B5929469 : Blo 1080619 5929469 := bstep (se 3 (by rfl) ⟨1111775, by rfl⟩ : syracuseStep 5929469 = 2223551) B2223551
theorem B5471225 : Blo 1080619 5471225 := bstep (se 2 (by rfl) ⟨2051709, by rfl⟩ : syracuseStep 5471225 = 4103419) B4103419
theorem B3079615 : Blo 1080619 3079615 := bstep (se 1 (by rfl) ⟨2309711, by rfl⟩ : syracuseStep 3079615 = 4619423) B4619423
theorem B1080863 : Blo 1080619 1080863 := bstep (se 1 (by rfl) ⟨810647, by rfl⟩ : syracuseStep 1080863 = 1621295) B1621295
theorem B1081371 : Blo 1080619 1081371 := bstep (se 1 (by rfl) ⟨811028, by rfl⟩ : syracuseStep 1081371 = 1622057) B1622057
theorem B1736731 : Blo 1080619 1736731 := bstep (se 1 (by rfl) ⟨1302548, by rfl⟩ : syracuseStep 1736731 = 2605097) B2605097
theorem B108331451 : Blo 1080619 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B1081839 : Blo 1080619 1081839 := bstep (se 1 (by rfl) ⟨811379, by rfl⟩ : syracuseStep 1081839 = 1622759) B1622759
theorem B11698931 : Blo 1080619 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B21660473 : Blo 1080619 21660473 := bstep (se 2 (by rfl) ⟨8122677, by rfl⟩ : syracuseStep 21660473 = 16245355) B16245355
theorem B6947689 : Blo 1080619 6947689 := bstep (se 2 (by rfl) ⟨2605383, by rfl⟩ : syracuseStep 6947689 = 5210767) B5210767
theorem B39453959 : Blo 1080619 39453959 := bstep (se 1 (by rfl) ⟨29590469, by rfl⟩ : syracuseStep 39453959 = 59180939) B59180939
theorem B1082651 : Blo 1080619 1082651 := bstep (se 1 (by rfl) ⟨811988, by rfl⟩ : syracuseStep 1082651 = 1623977) B1623977
theorem B1082855 : Blo 1080619 1082855 := bstep (se 1 (by rfl) ⟨812141, by rfl⟩ : syracuseStep 1082855 = 1624283) B1624283
theorem B13862573 : Blo 1080619 13862573 := bstep (se 3 (by rfl) ⟨2599232, by rfl⟩ : syracuseStep 13862573 = 5198465) B5198465
theorem B1083551 : Blo 1080619 1083551 := bstep (se 1 (by rfl) ⟨812663, by rfl⟩ : syracuseStep 1083551 = 1625327) B1625327
theorem B1083719 : Blo 1080619 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B1216219 : Blo 1080619 1216219 := bstep (se 1 (by rfl) ⟨912164, by rfl⟩ : syracuseStep 1216219 = 1824329) B1824329
theorem B7705637 : Blo 1080619 7705637 := bstep (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) B1444807
theorem B5477705 : Blo 1080619 5477705 := bstep (se 2 (by rfl) ⟨2054139, by rfl⟩ : syracuseStep 5477705 = 4108279) B4108279
theorem B17571815 : Blo 1080619 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B4104863 : Blo 1080619 4104863 := bstep (se 1 (by rfl) ⟨3078647, by rfl⟩ : syracuseStep 4104863 = 6157295) B6157295
theorem B9250463 : Blo 1080619 9250463 := bstep (se 1 (by rfl) ⟨6937847, by rfl⟩ : syracuseStep 9250463 = 13875695) B13875695
theorem B4106153 : Blo 1080619 4106153 := bstep (se 2 (by rfl) ⟨1539807, by rfl⟩ : syracuseStep 4106153 = 3079615) B3079615
theorem B3647483 : Blo 1080619 3647483 := bstep (se 1 (by rfl) ⟨2735612, by rfl⟩ : syracuseStep 3647483 = 5471225) B5471225
theorem B2435399 : Blo 1080619 2435399 := bstep (se 1 (by rfl) ⟨1826549, by rfl⟩ : syracuseStep 2435399 = 3653099) B3653099
theorem B9874217 : Blo 1080619 9874217 := bstep (se 2 (by rfl) ⟨3702831, by rfl⟩ : syracuseStep 9874217 = 7405663) B7405663
theorem B17542169 : Blo 1080619 17542169 := bstep (se 2 (by rfl) ⟨6578313, by rfl⟩ : syracuseStep 17542169 = 13156627) B13156627
theorem B2436587 : Blo 1080619 2436587 := bstep (se 1 (by rfl) ⟨1827440, by rfl⟩ : syracuseStep 2436587 = 3654881) B3654881
theorem B3649481 : Blo 1080619 3649481 := bstep (se 2 (by rfl) ⟨1368555, by rfl⟩ : syracuseStep 3649481 = 2737111) B2737111
theorem B4632545 : Blo 1080619 4632545 := bstep (se 2 (by rfl) ⟨1737204, by rfl⟩ : syracuseStep 4632545 = 3474409) B3474409
theorem B3649751 : Blo 1080619 3649751 := bstep (se 1 (by rfl) ⟨2737313, by rfl⟩ : syracuseStep 3649751 = 5474627) B5474627
theorem B3650291 : Blo 1080619 3650291 := bstep (se 1 (by rfl) ⟨2737718, by rfl⟩ : syracuseStep 3650291 = 5475437) B5475437
theorem B2602223 : Blo 1080619 2602223 := bstep (se 1 (by rfl) ⟨1951667, by rfl⟩ : syracuseStep 2602223 = 3903335) B3903335
theorem B2439593 : Blo 1080619 2439593 := bstep (se 2 (by rfl) ⟨914847, by rfl⟩ : syracuseStep 2439593 = 1829695) B1829695
theorem B1624043 : Blo 1080619 1624043 := bstep (se 1 (by rfl) ⟨1218032, by rfl⟩ : syracuseStep 1624043 = 2436065) B2436065
theorem B6933235 : Blo 1080619 6933235 := bstep (se 1 (by rfl) ⟨5199926, by rfl⟩ : syracuseStep 6933235 = 10399853) B10399853
theorem B1625447 : Blo 1080619 1625447 := bstep (se 1 (by rfl) ⟨1219085, by rfl⟩ : syracuseStep 1625447 = 2438171) B2438171
theorem B1625759 : Blo 1080619 1625759 := bstep (se 1 (by rfl) ⟨1219319, by rfl⟩ : syracuseStep 1625759 = 2438639) B2438639
theorem B2740331 : Blo 1080619 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B1626407 : Blo 1080619 1626407 := bstep (se 1 (by rfl) ⟨1219805, by rfl⟩ : syracuseStep 1626407 = 2439611) B2439611
theorem B3952979 : Blo 1080619 3952979 := bstep (se 1 (by rfl) ⟨2964734, by rfl⟩ : syracuseStep 3952979 = 5929469) B5929469
theorem B3660335 : Blo 1080619 3660335 := bstep (se 1 (by rfl) ⟨2745251, by rfl⟩ : syracuseStep 3660335 = 5490503) B5490503
theorem B43342739 : Blo 1080619 43342739 := bstep (se 1 (by rfl) ⟨32507054, by rfl⟩ : syracuseStep 43342739 = 65014109) B65014109
theorem B1368191 : Blo 1080619 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B37446293 : Blo 1080619 37446293 := bstep (se 6 (by rfl) ⟨877647, by rfl⟩ : syracuseStep 37446293 = 1755295) B1755295
theorem B2745191 : Blo 1080619 2745191 := bstep (se 1 (by rfl) ⟨2058893, by rfl⟩ : syracuseStep 2745191 = 4117787) B4117787
theorem B14836729 : Blo 1080619 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B5203079 : Blo 1080619 5203079 := bstep (se 1 (by rfl) ⟨3902309, by rfl⟩ : syracuseStep 5203079 = 7804619) B7804619
theorem B2057663 : Blo 1080619 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B1828919 : Blo 1080619 1828919 := bstep (se 1 (by rfl) ⟨1371689, by rfl⟩ : syracuseStep 1828919 = 2743379) B2743379
theorem B1370783 : Blo 1080619 1370783 := bstep (se 1 (by rfl) ⟨1028087, by rfl⟩ : syracuseStep 1370783 = 2056175) B2056175
theorem B16641065 : Blo 1080619 16641065 := bstep (se 2 (by rfl) ⟨6240399, by rfl⟩ : syracuseStep 16641065 = 12480799) B12480799
theorem B9006761 : Blo 1080619 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B8221175 : Blo 1080619 8221175 := bstep (se 1 (by rfl) ⟨6165881, by rfl⟩ : syracuseStep 8221175 = 12331763) B12331763
theorem B47477819 : Blo 1080619 47477819 := bstep (se 1 (by rfl) ⟨35608364, by rfl⟩ : syracuseStep 47477819 = 71216729) B71216729
theorem B4159775 : Blo 1080619 4159775 := bstep (se 1 (by rfl) ⟨3119831, by rfl⟩ : syracuseStep 4159775 = 6239663) B6239663
theorem B1080935 : Blo 1080619 1080935 := bstep (se 1 (by rfl) ⟨810701, by rfl⟩ : syracuseStep 1080935 = 1621403) B1621403
theorem B33390463 : Blo 1080619 33390463 := bstep (se 1 (by rfl) ⟨25042847, by rfl⟩ : syracuseStep 33390463 = 50085695) B50085695
theorem B72220967 : Blo 1080619 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B7799287 : Blo 1080619 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B9241715 : Blo 1080619 9241715 := bstep (se 1 (by rfl) ⟨6931286, by rfl⟩ : syracuseStep 9241715 = 13862573) B13862573
theorem B1082695 : Blo 1080619 1082695 := bstep (se 1 (by rfl) ⟨812021, by rfl⟩ : syracuseStep 1082695 = 1624043) B1624043
theorem B1083631 : Blo 1080619 1083631 := bstep (se 1 (by rfl) ⟨812723, by rfl⟩ : syracuseStep 1083631 = 1625447) B1625447
theorem B1083839 : Blo 1080619 1083839 := bstep (se 1 (by rfl) ⟨812879, by rfl⟩ : syracuseStep 1083839 = 1625759) B1625759
theorem B1084271 : Blo 1080619 1084271 := bstep (se 1 (by rfl) ⟨813203, by rfl⟩ : syracuseStep 1084271 = 1626407) B1626407
theorem B9244313 : Blo 1080619 9244313 := bstep (se 2 (by rfl) ⟨3466617, by rfl⟩ : syracuseStep 9244313 = 6933235) B6933235
theorem B6166975 : Blo 1080619 6166975 := bstep (se 1 (by rfl) ⟨4625231, by rfl⟩ : syracuseStep 6166975 = 9250463) B9250463
theorem B2431655 : Blo 1080619 2431655 := bstep (se 1 (by rfl) ⟨1823741, by rfl⟩ : syracuseStep 2431655 = 3647483) B3647483
theorem B1219279 : Blo 1080619 1219279 := bstep (se 1 (by rfl) ⟨914459, by rfl⟩ : syracuseStep 1219279 = 1828919) B1828919
theorem B6004507 : Blo 1080619 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B2432987 : Blo 1080619 2432987 := bstep (se 1 (by rfl) ⟨1824740, by rfl⟩ : syracuseStep 2432987 = 3649481) B3649481
theorem B3088363 : Blo 1080619 3088363 := bstep (se 1 (by rfl) ⟨2316272, by rfl⟩ : syracuseStep 3088363 = 4632545) B4632545
theorem B44376173 : Blo 1080619 44376173 := bstep (se 3 (by rfl) ⟨8320532, by rfl⟩ : syracuseStep 44376173 = 16641065) B16641065
theorem B2433167 : Blo 1080619 2433167 := bstep (se 1 (by rfl) ⟨1824875, by rfl⟩ : syracuseStep 2433167 = 3649751) B3649751
theorem B5480783 : Blo 1080619 5480783 := bstep (se 1 (by rfl) ⟨4110587, by rfl⟩ : syracuseStep 5480783 = 8221175) B8221175
theorem B2433527 : Blo 1080619 2433527 := bstep (se 1 (by rfl) ⟨1825145, by rfl⟩ : syracuseStep 2433527 = 3650291) B3650291
theorem B3648509 : Blo 1080619 3648509 := bstep (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) B1368191
theorem B2635319 : Blo 1080619 2635319 := bstep (se 1 (by rfl) ⟨1976489, by rfl⟩ : syracuseStep 2635319 = 3952979) B3952979
theorem B3651803 : Blo 1080619 3651803 := bstep (se 1 (by rfl) ⟨2738852, by rfl⟩ : syracuseStep 3651803 = 5477705) B5477705
theorem B5487101 : Blo 1080619 5487101 := bstep (se 3 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 5487101 = 2057663) B2057663
theorem B2440223 : Blo 1080619 2440223 := bstep (se 1 (by rfl) ⟨1830167, by rfl⟩ : syracuseStep 2440223 = 3660335) B3660335
theorem B1621625 : Blo 1080619 1621625 := bstep (se 2 (by rfl) ⟨608109, by rfl⟩ : syracuseStep 1621625 = 1216219) B1216219
theorem B11714543 : Blo 1080619 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B2736575 : Blo 1080619 2736575 := bstep (se 1 (by rfl) ⟨2052431, by rfl⟩ : syracuseStep 2736575 = 4104863) B4104863
theorem B2737435 : Blo 1080619 2737435 := bstep (se 1 (by rfl) ⟨2053076, by rfl⟩ : syracuseStep 2737435 = 4106153) B4106153
theorem B1623599 : Blo 1080619 1623599 := bstep (se 1 (by rfl) ⟨1217699, by rfl⟩ : syracuseStep 1623599 = 2435399) B2435399
theorem B3655421 : Blo 1080619 3655421 := bstep (se 3 (by rfl) ⟨685391, by rfl⟩ : syracuseStep 3655421 = 1370783) B1370783
theorem B1624391 : Blo 1080619 1624391 := bstep (se 1 (by rfl) ⟨1218293, by rfl⟩ : syracuseStep 1624391 = 2436587) B2436587
theorem B2773183 : Blo 1080619 2773183 := bstep (se 1 (by rfl) ⟨2079887, by rfl⟩ : syracuseStep 2773183 = 4159775) B4159775
theorem B1626395 : Blo 1080619 1626395 := bstep (se 1 (by rfl) ⟨1219796, by rfl⟩ : syracuseStep 1626395 = 2439593) B2439593
theorem B44520617 : Blo 1080619 44520617 := bstep (se 2 (by rfl) ⟨16695231, by rfl⟩ : syracuseStep 44520617 = 33390463) B33390463
theorem B2315641 : Blo 1080619 2315641 := bstep (se 2 (by rfl) ⟨868365, by rfl⟩ : syracuseStep 2315641 = 1736731) B1736731
theorem B14440315 : Blo 1080619 14440315 := bstep (se 1 (by rfl) ⟨10830236, by rfl⟩ : syracuseStep 14440315 = 21660473) B21660473
theorem B26302639 : Blo 1080619 26302639 := bstep (se 1 (by rfl) ⟨19726979, by rfl⟩ : syracuseStep 26302639 = 39453959) B39453959
theorem B9263585 : Blo 1080619 9263585 := bstep (se 2 (by rfl) ⟨3473844, by rfl⟩ : syracuseStep 9263585 = 6947689) B6947689
theorem B19782305 : Blo 1080619 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B1826887 : Blo 1080619 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B5137091 : Blo 1080619 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B28895159 : Blo 1080619 28895159 := bstep (se 1 (by rfl) ⟨21671369, by rfl⟩ : syracuseStep 28895159 = 43342739) B43342739
theorem B24964195 : Blo 1080619 24964195 := bstep (se 1 (by rfl) ⟨18723146, by rfl⟩ : syracuseStep 24964195 = 37446293) B37446293
theorem B1830127 : Blo 1080619 1830127 := bstep (se 1 (by rfl) ⟨1372595, by rfl⟩ : syracuseStep 1830127 = 2745191) B2745191
theorem B3468719 : Blo 1080619 3468719 := bstep (se 1 (by rfl) ⟨2601539, by rfl⟩ : syracuseStep 3468719 = 5203079) B5203079
theorem B6582811 : Blo 1080619 6582811 := bstep (se 1 (by rfl) ⟨4937108, by rfl⟩ : syracuseStep 6582811 = 9874217) B9874217
theorem B11694779 : Blo 1080619 11694779 := bstep (se 1 (by rfl) ⟨8771084, by rfl⟩ : syracuseStep 11694779 = 17542169) B17542169
theorem B31651879 : Blo 1080619 31651879 := bstep (se 1 (by rfl) ⟨23738909, by rfl⟩ : syracuseStep 31651879 = 47477819) B47477819
theorem B1734815 : Blo 1080619 1734815 := bstep (se 1 (by rfl) ⟨1301111, by rfl⟩ : syracuseStep 1734815 = 2602223) B2602223
theorem B6161143 : Blo 1080619 6161143 := bstep (se 1 (by rfl) ⟨4620857, by rfl⟩ : syracuseStep 6161143 = 9241715) B9241715
theorem B1082399 : Blo 1080619 1082399 := bstep (se 1 (by rfl) ⟨811799, by rfl⟩ : syracuseStep 1082399 = 1623599) B1623599
theorem B1082927 : Blo 1080619 1082927 := bstep (se 1 (by rfl) ⟨812195, by rfl⟩ : syracuseStep 1082927 = 1624391) B1624391
theorem B6162875 : Blo 1080619 6162875 := bstep (se 1 (by rfl) ⟨4622156, by rfl⟩ : syracuseStep 6162875 = 9244313) B9244313
theorem B1084263 : Blo 1080619 1084263 := bstep (se 1 (by rfl) ⟨813197, by rfl⟩ : syracuseStep 1084263 = 1626395) B1626395
theorem B4626173 : Blo 1080619 4626173 := bstep (se 3 (by rfl) ⟨867407, by rfl⟩ : syracuseStep 4626173 = 1734815) B1734815
theorem B3087521 : Blo 1080619 3087521 := bstep (se 2 (by rfl) ⟨1157820, by rfl⟩ : syracuseStep 3087521 = 2315641) B2315641
theorem B2432339 : Blo 1080619 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B35070185 : Blo 1080619 35070185 := bstep (se 2 (by rfl) ⟨13151319, by rfl⟩ : syracuseStep 35070185 = 26302639) B26302639
theorem B2434535 : Blo 1080619 2434535 := bstep (se 1 (by rfl) ⟨1825901, by rfl⟩ : syracuseStep 2434535 = 3651803) B3651803
theorem B8006009 : Blo 1080619 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B7809695 : Blo 1080619 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B2435849 : Blo 1080619 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B48147311 : Blo 1080619 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B10399049 : Blo 1080619 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B2436947 : Blo 1080619 2436947 := bstep (se 1 (by rfl) ⟨1827710, by rfl⟩ : syracuseStep 2436947 = 3655421) B3655421
theorem B3649913 : Blo 1080619 3649913 := bstep (se 2 (by rfl) ⟨1368717, by rfl⟩ : syracuseStep 3649913 = 2737435) B2737435
theorem B2440169 : Blo 1080619 2440169 := bstep (se 2 (by rfl) ⟨915063, by rfl⟩ : syracuseStep 2440169 = 1830127) B1830127
theorem B6175723 : Blo 1080619 6175723 := bstep (se 1 (by rfl) ⟨4631792, by rfl⟩ : syracuseStep 6175723 = 9263585) B9263585
theorem B13188203 : Blo 1080619 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B1621103 : Blo 1080619 1621103 := bstep (se 1 (by rfl) ⟨1215827, by rfl⟩ : syracuseStep 1621103 = 2431655) B2431655
theorem B1621991 : Blo 1080619 1621991 := bstep (se 1 (by rfl) ⟨1216493, by rfl⟩ : syracuseStep 1621991 = 2432987) B2432987
theorem B1622111 : Blo 1080619 1622111 := bstep (se 1 (by rfl) ⟨1216583, by rfl⟩ : syracuseStep 1622111 = 2433167) B2433167
theorem B3653855 : Blo 1080619 3653855 := bstep (se 1 (by rfl) ⟨2740391, by rfl⟩ : syracuseStep 3653855 = 5480783) B5480783
theorem B1622351 : Blo 1080619 1622351 := bstep (se 1 (by rfl) ⟨1216763, by rfl⟩ : syracuseStep 1622351 = 2433527) B2433527
theorem B3424727 : Blo 1080619 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B2312479 : Blo 1080619 2312479 := bstep (se 1 (by rfl) ⟨1734359, by rfl⟩ : syracuseStep 2312479 = 3468719) B3468719
theorem B19253753 : Blo 1080619 19253753 := bstep (se 2 (by rfl) ⟨7220157, by rfl⟩ : syracuseStep 19253753 = 14440315) B14440315
theorem B1625705 : Blo 1080619 1625705 := bstep (se 2 (by rfl) ⟨609639, by rfl⟩ : syracuseStep 1625705 = 1219279) B1219279
theorem B1756879 : Blo 1080619 1756879 := bstep (se 1 (by rfl) ⟨1317659, by rfl⟩ : syracuseStep 1756879 = 2635319) B2635319
theorem B3658067 : Blo 1080619 3658067 := bstep (se 1 (by rfl) ⟨2743550, by rfl⟩ : syracuseStep 3658067 = 5487101) B5487101
theorem B1626815 : Blo 1080619 1626815 := bstep (se 1 (by rfl) ⟨1220111, by rfl⟩ : syracuseStep 1626815 = 2440223) B2440223
theorem B4117817 : Blo 1080619 4117817 := bstep (se 2 (by rfl) ⟨1544181, by rfl⟩ : syracuseStep 4117817 = 3088363) B3088363
theorem B1824383 : Blo 1080619 1824383 := bstep (se 1 (by rfl) ⟨1368287, by rfl⟩ : syracuseStep 1824383 = 2736575) B2736575
theorem B29680411 : Blo 1080619 29680411 := bstep (se 1 (by rfl) ⟨22260308, by rfl⟩ : syracuseStep 29680411 = 44520617) B44520617
theorem B33285593 : Blo 1080619 33285593 := bstep (se 2 (by rfl) ⟨12482097, by rfl⟩ : syracuseStep 33285593 = 24964195) B24964195
theorem B29584115 : Blo 1080619 29584115 := bstep (se 1 (by rfl) ⟨22188086, by rfl⟩ : syracuseStep 29584115 = 44376173) B44376173
theorem B3697577 : Blo 1080619 3697577 := bstep (se 2 (by rfl) ⟨1386591, by rfl⟩ : syracuseStep 3697577 = 2773183) B2773183
theorem B8777081 : Blo 1080619 8777081 := bstep (se 2 (by rfl) ⟨3291405, by rfl⟩ : syracuseStep 8777081 = 6582811) B6582811
theorem B19263439 : Blo 1080619 19263439 := bstep (se 1 (by rfl) ⟨14447579, by rfl⟩ : syracuseStep 19263439 = 28895159) B28895159
theorem B42202505 : Blo 1080619 42202505 := bstep (se 2 (by rfl) ⟨15825939, by rfl⟩ : syracuseStep 42202505 = 31651879) B31651879
theorem B7796519 : Blo 1080619 7796519 := bstep (se 1 (by rfl) ⟨5847389, by rfl⟩ : syracuseStep 7796519 = 11694779) B11694779
theorem B8222633 : Blo 1080619 8222633 := bstep (se 2 (by rfl) ⟨3083487, by rfl⟩ : syracuseStep 8222633 = 6166975) B6166975
theorem B1081083 : Blo 1080619 1081083 := bstep (se 1 (by rfl) ⟨810812, by rfl⟩ : syracuseStep 1081083 = 1621625) B1621625
theorem B1081407 : Blo 1080619 1081407 := bstep (se 1 (by rfl) ⟨811055, by rfl⟩ : syracuseStep 1081407 = 1622111) B1622111
theorem B1081567 : Blo 1080619 1081567 := bstep (se 1 (by rfl) ⟨811175, by rfl⟩ : syracuseStep 1081567 = 1622351) B1622351
theorem B1083803 : Blo 1080619 1083803 := bstep (se 1 (by rfl) ⟨812852, by rfl⟩ : syracuseStep 1083803 = 1625705) B1625705
theorem B1084543 : Blo 1080619 1084543 := bstep (se 1 (by rfl) ⟨813407, by rfl⟩ : syracuseStep 1084543 = 1626815) B1626815
theorem B1216255 : Blo 1080619 1216255 := bstep (se 1 (by rfl) ⟨912191, by rfl⟩ : syracuseStep 1216255 = 1824383) B1824383
theorem B3084115 : Blo 1080619 3084115 := bstep (se 1 (by rfl) ⟨2313086, by rfl⟩ : syracuseStep 3084115 = 4626173) B4626173
theorem B85397429 : Blo 1080619 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B22190395 : Blo 1080619 22190395 := bstep (se 1 (by rfl) ⟨16642796, by rfl⟩ : syracuseStep 22190395 = 33285593) B33285593
theorem B2465051 : Blo 1080619 2465051 := bstep (se 1 (by rfl) ⟨1848788, by rfl⟩ : syracuseStep 2465051 = 3697577) B3697577
theorem B2433275 : Blo 1080619 2433275 := bstep (se 1 (by rfl) ⟨1824956, by rfl⟩ : syracuseStep 2433275 = 3649913) B3649913
theorem B5481755 : Blo 1080619 5481755 := bstep (se 1 (by rfl) ⟨4111316, by rfl⟩ : syracuseStep 5481755 = 8222633) B8222633
theorem B8234297 : Blo 1080619 8234297 := bstep (se 2 (by rfl) ⟨3087861, by rfl⟩ : syracuseStep 8234297 = 6175723) B6175723
theorem B8792135 : Blo 1080619 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B102738341 : Blo 1080619 102738341 := bstep (se 4 (by rfl) ⟨9631719, by rfl⟩ : syracuseStep 102738341 = 19263439) B19263439
theorem B2435903 : Blo 1080619 2435903 := bstep (se 1 (by rfl) ⟨1826927, by rfl⟩ : syracuseStep 2435903 = 3653855) B3653855
theorem B12333221 : Blo 1080619 12333221 := bstep (se 4 (by rfl) ⟨1156239, by rfl⟩ : syracuseStep 12333221 = 2312479) B2312479
theorem B4108583 : Blo 1080619 4108583 := bstep (se 1 (by rfl) ⟨3081437, by rfl⟩ : syracuseStep 4108583 = 6162875) B6162875
theorem B2438711 : Blo 1080619 2438711 := bstep (se 1 (by rfl) ⟨1829033, by rfl⟩ : syracuseStep 2438711 = 3658067) B3658067
theorem B112540013 : Blo 1080619 112540013 := bstep (se 3 (by rfl) ⟨21101252, by rfl⟩ : syracuseStep 112540013 = 42202505) B42202505
theorem B1621559 : Blo 1080619 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B23380123 : Blo 1080619 23380123 := bstep (se 1 (by rfl) ⟨17535092, by rfl⟩ : syracuseStep 23380123 = 35070185) B35070185
theorem B1623023 : Blo 1080619 1623023 := bstep (se 1 (by rfl) ⟨1217267, by rfl⟩ : syracuseStep 1623023 = 2434535) B2434535
theorem B1623899 : Blo 1080619 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B32098207 : Blo 1080619 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B6932699 : Blo 1080619 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B5851387 : Blo 1080619 5851387 := bstep (se 1 (by rfl) ⟨4388540, by rfl⟩ : syracuseStep 5851387 = 8777081) B8777081
theorem B1624631 : Blo 1080619 1624631 := bstep (se 1 (by rfl) ⟨1218473, by rfl⟩ : syracuseStep 1624631 = 2436947) B2436947
theorem B5197679 : Blo 1080619 5197679 := bstep (se 1 (by rfl) ⟨3898259, by rfl⟩ : syracuseStep 5197679 = 7796519) B7796519
theorem B1626779 : Blo 1080619 1626779 := bstep (se 1 (by rfl) ⟨1220084, by rfl⟩ : syracuseStep 1626779 = 2440169) B2440169
theorem B8214857 : Blo 1080619 8214857 := bstep (se 2 (by rfl) ⟨3080571, by rfl⟩ : syracuseStep 8214857 = 6161143) B6161143
theorem B39573881 : Blo 1080619 39573881 := bstep (se 2 (by rfl) ⟨14840205, by rfl⟩ : syracuseStep 39573881 = 29680411) B29680411
theorem B9132605 : Blo 1080619 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B12835835 : Blo 1080619 12835835 := bstep (se 1 (by rfl) ⟨9626876, by rfl⟩ : syracuseStep 12835835 = 19253753) B19253753
theorem B2745211 : Blo 1080619 2745211 := bstep (se 1 (by rfl) ⟨2058908, by rfl⟩ : syracuseStep 2745211 = 4117817) B4117817
theorem B37480085 : Blo 1080619 37480085 := bstep (se 6 (by rfl) ⟨878439, by rfl⟩ : syracuseStep 37480085 = 1756879) B1756879
theorem B2058347 : Blo 1080619 2058347 := bstep (se 1 (by rfl) ⟨1543760, by rfl⟩ : syracuseStep 2058347 = 3087521) B3087521
theorem B5206463 : Blo 1080619 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B19722743 : Blo 1080619 19722743 := bstep (se 1 (by rfl) ⟨14792057, by rfl⟩ : syracuseStep 19722743 = 29584115) B29584115
theorem B1080735 : Blo 1080619 1080735 := bstep (se 1 (by rfl) ⟨810551, by rfl⟩ : syracuseStep 1080735 = 1621103) B1621103
theorem B1081327 : Blo 1080619 1081327 := bstep (se 1 (by rfl) ⟨810995, by rfl⟩ : syracuseStep 1081327 = 1621991) B1621991
theorem B1082015 : Blo 1080619 1082015 := bstep (se 1 (by rfl) ⟨811511, by rfl⟩ : syracuseStep 1082015 = 1623023) B1623023
theorem B1082599 : Blo 1080619 1082599 := bstep (se 1 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 1082599 = 1623899) B1623899
theorem B4621799 : Blo 1080619 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B1083087 : Blo 1080619 1083087 := bstep (se 1 (by rfl) ⟨812315, by rfl⟩ : syracuseStep 1083087 = 1624631) B1624631
theorem B42797609 : Blo 1080619 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B7801849 : Blo 1080619 7801849 := bstep (se 2 (by rfl) ⟨2925693, by rfl⟩ : syracuseStep 7801849 = 5851387) B5851387
theorem B1084519 : Blo 1080619 1084519 := bstep (se 1 (by rfl) ⟨813389, by rfl⟩ : syracuseStep 1084519 = 1626779) B1626779
theorem B5476571 : Blo 1080619 5476571 := bstep (se 1 (by rfl) ⟨4107428, by rfl⟩ : syracuseStep 5476571 = 8214857) B8214857
theorem B26382587 : Blo 1080619 26382587 := bstep (se 1 (by rfl) ⟨19786940, by rfl⟩ : syracuseStep 26382587 = 39573881) B39573881
theorem B8557223 : Blo 1080619 8557223 := bstep (se 1 (by rfl) ⟨6417917, by rfl⟩ : syracuseStep 8557223 = 12835835) B12835835
theorem B68492227 : Blo 1080619 68492227 := bstep (se 1 (by rfl) ⟨51369170, by rfl⟩ : syracuseStep 68492227 = 102738341) B102738341
theorem B13148495 : Blo 1080619 13148495 := bstep (se 1 (by rfl) ⟨9861371, by rfl⟩ : syracuseStep 13148495 = 19722743) B19722743
theorem B31173497 : Blo 1080619 31173497 := bstep (se 2 (by rfl) ⟨11690061, by rfl⟩ : syracuseStep 31173497 = 23380123) B23380123
theorem B56931619 : Blo 1080619 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B1621673 : Blo 1080619 1621673 := bstep (se 2 (by rfl) ⟨608127, by rfl⟩ : syracuseStep 1621673 = 1216255) B1216255
theorem B4112153 : Blo 1080619 4112153 := bstep (se 2 (by rfl) ⟨1542057, by rfl⟩ : syracuseStep 4112153 = 3084115) B3084115
theorem B1622183 : Blo 1080619 1622183 := bstep (se 1 (by rfl) ⟨1216637, by rfl⟩ : syracuseStep 1622183 = 2433275) B2433275
theorem B3654503 : Blo 1080619 3654503 := bstep (se 1 (by rfl) ⟨2740877, by rfl⟩ : syracuseStep 3654503 = 5481755) B5481755
theorem B5489531 : Blo 1080619 5489531 := bstep (se 1 (by rfl) ⟨4117148, by rfl⟩ : syracuseStep 5489531 = 8234297) B8234297
theorem B24986723 : Blo 1080619 24986723 := bstep (se 1 (by rfl) ⟨18740042, by rfl⟩ : syracuseStep 24986723 = 37480085) B37480085
theorem B1623935 : Blo 1080619 1623935 := bstep (se 1 (by rfl) ⟨1217951, by rfl⟩ : syracuseStep 1623935 = 2435903) B2435903
theorem B2739055 : Blo 1080619 2739055 := bstep (se 1 (by rfl) ⟨2054291, by rfl⟩ : syracuseStep 2739055 = 4108583) B4108583
theorem B6573469 : Blo 1080619 6573469 := bstep (se 3 (by rfl) ⟨1232525, by rfl⟩ : syracuseStep 6573469 = 2465051) B2465051
theorem B1625807 : Blo 1080619 1625807 := bstep (se 1 (by rfl) ⟨1219355, by rfl⟩ : syracuseStep 1625807 = 2438711) B2438711
theorem B75026675 : Blo 1080619 75026675 := bstep (se 1 (by rfl) ⟨56270006, by rfl⟩ : syracuseStep 75026675 = 112540013) B112540013
theorem B3660281 : Blo 1080619 3660281 := bstep (se 2 (by rfl) ⟨1372605, by rfl⟩ : syracuseStep 3660281 = 2745211) B2745211
theorem B3465119 : Blo 1080619 3465119 := bstep (se 1 (by rfl) ⟨2598839, by rfl⟩ : syracuseStep 3465119 = 5197679) B5197679
theorem B6088403 : Blo 1080619 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B5861423 : Blo 1080619 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B1372231 : Blo 1080619 1372231 := bstep (se 1 (by rfl) ⟨1029173, by rfl⟩ : syracuseStep 1372231 = 2058347) B2058347
theorem B8222147 : Blo 1080619 8222147 := bstep (se 1 (by rfl) ⟨6166610, by rfl⟩ : syracuseStep 8222147 = 12333221) B12333221
theorem B3470975 : Blo 1080619 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B29587193 : Blo 1080619 29587193 := bstep (se 2 (by rfl) ⟨11095197, by rfl⟩ : syracuseStep 29587193 = 22190395) B22190395
theorem B1081039 : Blo 1080619 1081039 := bstep (se 1 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 1081039 = 1621559) B1621559
theorem B1081455 : Blo 1080619 1081455 := bstep (se 1 (by rfl) ⟨811091, by rfl⟩ : syracuseStep 1081455 = 1622183) B1622183
theorem B3081199 : Blo 1080619 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B1082623 : Blo 1080619 1082623 := bstep (se 1 (by rfl) ⟨811967, by rfl⟩ : syracuseStep 1082623 = 1623935) B1623935
theorem B1083871 : Blo 1080619 1083871 := bstep (se 1 (by rfl) ⟨812903, by rfl⟩ : syracuseStep 1083871 = 1625807) B1625807
theorem B281414261 : Blo 1080619 281414261 := bstep (se 5 (by rfl) ⟨13191293, by rfl⟩ : syracuseStep 281414261 = 26382587) B26382587
theorem B20782331 : Blo 1080619 20782331 := bstep (se 1 (by rfl) ⟨15586748, by rfl⟩ : syracuseStep 20782331 = 31173497) B31173497
theorem B3907615 : Blo 1080619 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B5481431 : Blo 1080619 5481431 := bstep (se 1 (by rfl) ⟨4111073, by rfl⟩ : syracuseStep 5481431 = 8222147) B8222147
theorem B2436335 : Blo 1080619 2436335 := bstep (se 1 (by rfl) ⟨1827251, by rfl⟩ : syracuseStep 2436335 = 3654503) B3654503
theorem B22819261 : Blo 1080619 22819261 := bstep (se 3 (by rfl) ⟨4278611, by rfl⟩ : syracuseStep 22819261 = 8557223) B8557223
theorem B3651047 : Blo 1080619 3651047 := bstep (se 1 (by rfl) ⟨2738285, by rfl⟩ : syracuseStep 3651047 = 5476571) B5476571
theorem B50017783 : Blo 1080619 50017783 := bstep (se 1 (by rfl) ⟨37513337, by rfl⟩ : syracuseStep 50017783 = 75026675) B75026675
theorem B66631261 : Blo 1080619 66631261 := bstep (se 3 (by rfl) ⟨12493361, by rfl⟩ : syracuseStep 66631261 = 24986723) B24986723
theorem B3652073 : Blo 1080619 3652073 := bstep (se 2 (by rfl) ⟨1369527, by rfl⟩ : syracuseStep 3652073 = 2739055) B2739055
theorem B2440187 : Blo 1080619 2440187 := bstep (se 1 (by rfl) ⟨1830140, by rfl⟩ : syracuseStep 2440187 = 3660281) B3660281
theorem B8764625 : Blo 1080619 8764625 := bstep (se 2 (by rfl) ⟨3286734, by rfl⟩ : syracuseStep 8764625 = 6573469) B6573469
theorem B16235741 : Blo 1080619 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B8765663 : Blo 1080619 8765663 := bstep (se 1 (by rfl) ⟨6574247, by rfl⟩ : syracuseStep 8765663 = 13148495) B13148495
theorem B75908825 : Blo 1080619 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B2313983 : Blo 1080619 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B2741435 : Blo 1080619 2741435 := bstep (se 1 (by rfl) ⟨2056076, by rfl⟩ : syracuseStep 2741435 = 4112153) B4112153
theorem B3659687 : Blo 1080619 3659687 := bstep (se 1 (by rfl) ⟨2744765, by rfl⟩ : syracuseStep 3659687 = 5489531) B5489531
theorem B28531739 : Blo 1080619 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B41609861 : Blo 1080619 41609861 := bstep (se 4 (by rfl) ⟨3900924, by rfl⟩ : syracuseStep 41609861 = 7801849) B7801849
theorem B1829641 : Blo 1080619 1829641 := bstep (se 2 (by rfl) ⟨686115, by rfl⟩ : syracuseStep 1829641 = 1372231) B1372231
theorem B19724795 : Blo 1080619 19724795 := bstep (se 1 (by rfl) ⟨14793596, by rfl⟩ : syracuseStep 19724795 = 29587193) B29587193
theorem B91322969 : Blo 1080619 91322969 := bstep (se 2 (by rfl) ⟨34246113, by rfl⟩ : syracuseStep 91322969 = 68492227) B68492227
theorem B9240317 : Blo 1080619 9240317 := bstep (se 3 (by rfl) ⟨1732559, by rfl⟩ : syracuseStep 9240317 = 3465119) B3465119
theorem B1081115 : Blo 1080619 1081115 := bstep (se 1 (by rfl) ⟨810836, by rfl⟩ : syracuseStep 1081115 = 1621673) B1621673
theorem B5210153 : Blo 1080619 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B1542655 : Blo 1080619 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B66690377 : Blo 1080619 66690377 := bstep (se 2 (by rfl) ⟨25008891, by rfl⟩ : syracuseStep 66690377 = 50017783) B50017783
theorem B88841681 : Blo 1080619 88841681 := bstep (se 2 (by rfl) ⟨33315630, by rfl⟩ : syracuseStep 88841681 = 66631261) B66631261
theorem B23372333 : Blo 1080619 23372333 := bstep (se 3 (by rfl) ⟨4382312, by rfl⟩ : syracuseStep 23372333 = 8764625) B8764625
theorem B43295309 : Blo 1080619 43295309 := bstep (se 3 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 43295309 = 16235741) B16235741
theorem B2434031 : Blo 1080619 2434031 := bstep (se 1 (by rfl) ⟨1825523, by rfl⟩ : syracuseStep 2434031 = 3651047) B3651047
theorem B2434715 : Blo 1080619 2434715 := bstep (se 1 (by rfl) ⟨1826036, by rfl⟩ : syracuseStep 2434715 = 3652073) B3652073
theorem B13149863 : Blo 1080619 13149863 := bstep (se 1 (by rfl) ⟨9862397, by rfl⟩ : syracuseStep 13149863 = 19724795) B19724795
theorem B23375101 : Blo 1080619 23375101 := bstep (se 3 (by rfl) ⟨4382831, by rfl⟩ : syracuseStep 23375101 = 8765663) B8765663
theorem B50605883 : Blo 1080619 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B4108265 : Blo 1080619 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B187609507 : Blo 1080619 187609507 := bstep (se 1 (by rfl) ⟨140707130, by rfl⟩ : syracuseStep 187609507 = 281414261) B281414261
theorem B2439521 : Blo 1080619 2439521 := bstep (se 2 (by rfl) ⟨914820, by rfl⟩ : syracuseStep 2439521 = 1829641) B1829641
theorem B2439791 : Blo 1080619 2439791 := bstep (se 1 (by rfl) ⟨1829843, by rfl⟩ : syracuseStep 2439791 = 3659687) B3659687
theorem B19021159 : Blo 1080619 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B30425681 : Blo 1080619 30425681 := bstep (se 2 (by rfl) ⟨11409630, by rfl⟩ : syracuseStep 30425681 = 22819261) B22819261
theorem B3654287 : Blo 1080619 3654287 := bstep (se 1 (by rfl) ⟨2740715, by rfl⟩ : syracuseStep 3654287 = 5481431) B5481431
theorem B27739907 : Blo 1080619 27739907 := bstep (se 1 (by rfl) ⟨20804930, by rfl⟩ : syracuseStep 27739907 = 41609861) B41609861
theorem B1624223 : Blo 1080619 1624223 := bstep (se 1 (by rfl) ⟨1218167, by rfl⟩ : syracuseStep 1624223 = 2436335) B2436335
theorem B1626791 : Blo 1080619 1626791 := bstep (se 1 (by rfl) ⟨1220093, by rfl⟩ : syracuseStep 1626791 = 2440187) B2440187
theorem B1827623 : Blo 1080619 1827623 := bstep (se 1 (by rfl) ⟨1370717, by rfl⟩ : syracuseStep 1827623 = 2741435) B2741435
theorem B13854887 : Blo 1080619 13854887 := bstep (se 1 (by rfl) ⟨10391165, by rfl⟩ : syracuseStep 13854887 = 20782331) B20782331
theorem B243527917 : Blo 1080619 243527917 := bstep (se 3 (by rfl) ⟨45661484, by rfl⟩ : syracuseStep 243527917 = 91322969) B91322969
theorem B6160211 : Blo 1080619 6160211 := bstep (se 1 (by rfl) ⟨4620158, by rfl⟩ : syracuseStep 6160211 = 9240317) B9240317
theorem B3473435 : Blo 1080619 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B20283787 : Blo 1080619 20283787 := bstep (se 1 (by rfl) ⟨15212840, by rfl⟩ : syracuseStep 20283787 = 30425681) B30425681
theorem B1082815 : Blo 1080619 1082815 := bstep (se 1 (by rfl) ⟨812111, by rfl⟩ : syracuseStep 1082815 = 1624223) B1624223
theorem B8227493 : Blo 1080619 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B1084527 : Blo 1080619 1084527 := bstep (se 1 (by rfl) ⟨813395, by rfl⟩ : syracuseStep 1084527 = 1626791) B1626791
theorem B31166801 : Blo 1080619 31166801 := bstep (se 2 (by rfl) ⟨11687550, by rfl⟩ : syracuseStep 31166801 = 23375101) B23375101
theorem B324703889 : Blo 1080619 324703889 := bstep (se 2 (by rfl) ⟨121763958, by rfl⟩ : syracuseStep 324703889 = 243527917) B243527917
theorem B1218415 : Blo 1080619 1218415 := bstep (se 1 (by rfl) ⟨913811, by rfl⟩ : syracuseStep 1218415 = 1827623) B1827623
theorem B4106807 : Blo 1080619 4106807 := bstep (se 1 (by rfl) ⟨3080105, by rfl⟩ : syracuseStep 4106807 = 6160211) B6160211
theorem B2436191 : Blo 1080619 2436191 := bstep (se 1 (by rfl) ⟨1827143, by rfl⟩ : syracuseStep 2436191 = 3654287) B3654287
theorem B18493271 : Blo 1080619 18493271 := bstep (se 1 (by rfl) ⟨13869953, by rfl⟩ : syracuseStep 18493271 = 27739907) B27739907
theorem B1000584037 : Blo 1080619 1000584037 := bstep (se 4 (by rfl) ⟨93804753, by rfl⟩ : syracuseStep 1000584037 = 187609507) B187609507
theorem B59227787 : Blo 1080619 59227787 := bstep (se 1 (by rfl) ⟨44420840, by rfl⟩ : syracuseStep 59227787 = 88841681) B88841681
theorem B15581555 : Blo 1080619 15581555 := bstep (se 1 (by rfl) ⟨11686166, by rfl⟩ : syracuseStep 15581555 = 23372333) B23372333
theorem B1622687 : Blo 1080619 1622687 := bstep (se 1 (by rfl) ⟨1217015, by rfl⟩ : syracuseStep 1622687 = 2434031) B2434031
theorem B1623143 : Blo 1080619 1623143 := bstep (se 1 (by rfl) ⟨1217357, by rfl⟩ : syracuseStep 1623143 = 2434715) B2434715
theorem B8766575 : Blo 1080619 8766575 := bstep (se 1 (by rfl) ⟨6574931, by rfl⟩ : syracuseStep 8766575 = 13149863) B13149863
theorem B33737255 : Blo 1080619 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B2738843 : Blo 1080619 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B1626347 : Blo 1080619 1626347 := bstep (se 1 (by rfl) ⟨1219760, by rfl⟩ : syracuseStep 1626347 = 2439521) B2439521
theorem B1626527 : Blo 1080619 1626527 := bstep (se 1 (by rfl) ⟨1219895, by rfl⟩ : syracuseStep 1626527 = 2439791) B2439791
theorem B44460251 : Blo 1080619 44460251 := bstep (se 1 (by rfl) ⟨33345188, by rfl⟩ : syracuseStep 44460251 = 66690377) B66690377
theorem B28863539 : Blo 1080619 28863539 := bstep (se 1 (by rfl) ⟨21647654, by rfl⟩ : syracuseStep 28863539 = 43295309) B43295309
theorem B9236591 : Blo 1080619 9236591 := bstep (se 1 (by rfl) ⟨6927443, by rfl⟩ : syracuseStep 9236591 = 13854887) B13854887
theorem B25361545 : Blo 1080619 25361545 := bstep (se 2 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 25361545 = 19021159) B19021159
theorem B10387703 : Blo 1080619 10387703 := bstep (se 1 (by rfl) ⟨7790777, by rfl⟩ : syracuseStep 10387703 = 15581555) B15581555
theorem B1081791 : Blo 1080619 1081791 := bstep (se 1 (by rfl) ⟨811343, by rfl⟩ : syracuseStep 1081791 = 1622687) B1622687
theorem B1082095 : Blo 1080619 1082095 := bstep (se 1 (by rfl) ⟨811571, by rfl⟩ : syracuseStep 1082095 = 1623143) B1623143
theorem B1084231 : Blo 1080619 1084231 := bstep (se 1 (by rfl) ⟨813173, by rfl⟩ : syracuseStep 1084231 = 1626347) B1626347
theorem B20777867 : Blo 1080619 20777867 := bstep (se 1 (by rfl) ⟨15583400, by rfl⟩ : syracuseStep 20777867 = 31166801) B31166801
theorem B1084351 : Blo 1080619 1084351 := bstep (se 1 (by rfl) ⟨813263, by rfl⟩ : syracuseStep 1084351 = 1626527) B1626527
theorem B216469259 : Blo 1080619 216469259 := bstep (se 1 (by rfl) ⟨162351944, by rfl⟩ : syracuseStep 216469259 = 324703889) B324703889
theorem B19242359 : Blo 1080619 19242359 := bstep (se 1 (by rfl) ⟨14431769, by rfl⟩ : syracuseStep 19242359 = 28863539) B28863539
theorem B12328847 : Blo 1080619 12328847 := bstep (se 1 (by rfl) ⟨9246635, by rfl⟩ : syracuseStep 12328847 = 18493271) B18493271
theorem B5844383 : Blo 1080619 5844383 := bstep (se 1 (by rfl) ⟨4383287, by rfl⟩ : syracuseStep 5844383 = 8766575) B8766575
theorem B22491503 : Blo 1080619 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B5484995 : Blo 1080619 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B108180197 : Blo 1080619 108180197 := bstep (se 4 (by rfl) ⟨10141893, by rfl⟩ : syracuseStep 108180197 = 20283787) B20283787
theorem B29640167 : Blo 1080619 29640167 := bstep (se 1 (by rfl) ⟨22230125, by rfl⟩ : syracuseStep 29640167 = 44460251) B44460251
theorem B2737871 : Blo 1080619 2737871 := bstep (se 1 (by rfl) ⟨2053403, by rfl⟩ : syracuseStep 2737871 = 4106807) B4106807
theorem B1624127 : Blo 1080619 1624127 := bstep (se 1 (by rfl) ⟨1218095, by rfl⟩ : syracuseStep 1624127 = 2436191) B2436191
theorem B1624553 : Blo 1080619 1624553 := bstep (se 2 (by rfl) ⟨609207, by rfl⟩ : syracuseStep 1624553 = 1218415) B1218415
theorem B2315623 : Blo 1080619 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B1825895 : Blo 1080619 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B1334112049 : Blo 1080619 1334112049 := bstep (se 2 (by rfl) ⟨500292018, by rfl⟩ : syracuseStep 1334112049 = 1000584037) B1000584037
theorem B6157727 : Blo 1080619 6157727 := bstep (se 1 (by rfl) ⟨4618295, by rfl⟩ : syracuseStep 6157727 = 9236591) B9236591
theorem B33815393 : Blo 1080619 33815393 := bstep (se 2 (by rfl) ⟨12680772, by rfl⟩ : syracuseStep 33815393 = 25361545) B25361545
theorem B39485191 : Blo 1080619 39485191 := bstep (se 1 (by rfl) ⟨29613893, by rfl⟩ : syracuseStep 39485191 = 59227787) B59227787
theorem B19760111 : Blo 1080619 19760111 := bstep (se 1 (by rfl) ⟨14820083, by rfl⟩ : syracuseStep 19760111 = 29640167) B29640167
theorem B1082751 : Blo 1080619 1082751 := bstep (se 1 (by rfl) ⟨812063, by rfl⟩ : syracuseStep 1082751 = 1624127) B1624127
theorem B1083035 : Blo 1080619 1083035 := bstep (se 1 (by rfl) ⟨812276, by rfl⟩ : syracuseStep 1083035 = 1624553) B1624553
theorem B144312839 : Blo 1080619 144312839 := bstep (se 1 (by rfl) ⟨108234629, by rfl⟩ : syracuseStep 144312839 = 216469259) B216469259
theorem B1217263 : Blo 1080619 1217263 := bstep (se 1 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 1217263 = 1825895) B1825895
theorem B1778816065 : Blo 1080619 1778816065 := bstep (se 2 (by rfl) ⟨667056024, by rfl⟩ : syracuseStep 1778816065 = 1334112049) B1334112049
theorem B3087497 : Blo 1080619 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B4105151 : Blo 1080619 4105151 := bstep (se 1 (by rfl) ⟨3078863, by rfl⟩ : syracuseStep 4105151 = 6157727) B6157727
theorem B27700541 : Blo 1080619 27700541 := bstep (se 3 (by rfl) ⟨5193851, by rfl⟩ : syracuseStep 27700541 = 10387703) B10387703
theorem B12828239 : Blo 1080619 12828239 := bstep (se 1 (by rfl) ⟨9621179, by rfl⟩ : syracuseStep 12828239 = 19242359) B19242359
theorem B14994335 : Blo 1080619 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B3656663 : Blo 1080619 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B52646921 : Blo 1080619 52646921 := bstep (se 2 (by rfl) ⟨19742595, by rfl⟩ : syracuseStep 52646921 = 39485191) B39485191
theorem B1825247 : Blo 1080619 1825247 := bstep (se 1 (by rfl) ⟨1368935, by rfl⟩ : syracuseStep 1825247 = 2737871) B2737871
theorem B13851911 : Blo 1080619 13851911 := bstep (se 1 (by rfl) ⟨10388933, by rfl⟩ : syracuseStep 13851911 = 20777867) B20777867
theorem B8219231 : Blo 1080619 8219231 := bstep (se 1 (by rfl) ⟨6164423, by rfl⟩ : syracuseStep 8219231 = 12328847) B12328847
theorem B3896255 : Blo 1080619 3896255 := bstep (se 1 (by rfl) ⟨2922191, by rfl⟩ : syracuseStep 3896255 = 5844383) B5844383
theorem B72120131 : Blo 1080619 72120131 := bstep (se 1 (by rfl) ⟨54090098, by rfl⟩ : syracuseStep 72120131 = 108180197) B108180197
theorem B22543595 : Blo 1080619 22543595 := bstep (se 1 (by rfl) ⟨16907696, by rfl⟩ : syracuseStep 22543595 = 33815393) B33815393
theorem B13173407 : Blo 1080619 13173407 := bstep (se 1 (by rfl) ⟨9880055, by rfl⟩ : syracuseStep 13173407 = 19760111) B19760111
theorem B96208559 : Blo 1080619 96208559 := bstep (se 1 (by rfl) ⟨72156419, by rfl⟩ : syracuseStep 96208559 = 144312839) B144312839
theorem B9996223 : Blo 1080619 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B35097947 : Blo 1080619 35097947 := bstep (se 1 (by rfl) ⟨26323460, by rfl⟩ : syracuseStep 35097947 = 52646921) B52646921
theorem B1216831 : Blo 1080619 1216831 := bstep (se 1 (by rfl) ⟨912623, by rfl⟩ : syracuseStep 1216831 = 1825247) B1825247
theorem B2371754753 : Blo 1080619 2371754753 := bstep (se 2 (by rfl) ⟨889408032, by rfl⟩ : syracuseStep 2371754753 = 1778816065) B1778816065
theorem B5479487 : Blo 1080619 5479487 := bstep (se 1 (by rfl) ⟨4109615, by rfl⟩ : syracuseStep 5479487 = 8219231) B8219231
theorem B8233325 : Blo 1080619 8233325 := bstep (se 3 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 8233325 = 3087497) B3087497
theorem B2597503 : Blo 1080619 2597503 := bstep (se 1 (by rfl) ⟨1948127, by rfl⟩ : syracuseStep 2597503 = 3896255) B3896255
theorem B48080087 : Blo 1080619 48080087 := bstep (se 1 (by rfl) ⟨36060065, by rfl⟩ : syracuseStep 48080087 = 72120131) B72120131
theorem B2437775 : Blo 1080619 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B2736767 : Blo 1080619 2736767 := bstep (se 1 (by rfl) ⟨2052575, by rfl⟩ : syracuseStep 2736767 = 4105151) B4105151
theorem B1623017 : Blo 1080619 1623017 := bstep (se 2 (by rfl) ⟨608631, by rfl⟩ : syracuseStep 1623017 = 1217263) B1217263
theorem B18467027 : Blo 1080619 18467027 := bstep (se 1 (by rfl) ⟨13850270, by rfl⟩ : syracuseStep 18467027 = 27700541) B27700541
theorem B15029063 : Blo 1080619 15029063 := bstep (se 1 (by rfl) ⟨11271797, by rfl⟩ : syracuseStep 15029063 = 22543595) B22543595
theorem B9234607 : Blo 1080619 9234607 := bstep (se 1 (by rfl) ⟨6925955, by rfl⟩ : syracuseStep 9234607 = 13851911) B13851911
theorem B8552159 : Blo 1080619 8552159 := bstep (se 1 (by rfl) ⟨6414119, by rfl⟩ : syracuseStep 8552159 = 12828239) B12828239
theorem B8782271 : Blo 1080619 8782271 := bstep (se 1 (by rfl) ⟨6586703, by rfl⟩ : syracuseStep 8782271 = 13173407) B13173407
theorem B1082011 : Blo 1080619 1082011 := bstep (se 1 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 1082011 = 1623017) B1623017
theorem B23398631 : Blo 1080619 23398631 := bstep (se 1 (by rfl) ⟨17548973, by rfl⟩ : syracuseStep 23398631 = 35097947) B35097947
theorem B32053391 : Blo 1080619 32053391 := bstep (se 1 (by rfl) ⟨24040043, by rfl⟩ : syracuseStep 32053391 = 48080087) B48080087
theorem B64139039 : Blo 1080619 64139039 := bstep (se 1 (by rfl) ⟨48104279, by rfl⟩ : syracuseStep 64139039 = 96208559) B96208559
theorem B1581169835 : Blo 1080619 1581169835 := bstep (se 1 (by rfl) ⟨1185877376, by rfl⟩ : syracuseStep 1581169835 = 2371754753) B2371754753
theorem B3652991 : Blo 1080619 3652991 := bstep (se 1 (by rfl) ⟨2739743, by rfl⟩ : syracuseStep 3652991 = 5479487) B5479487
theorem B5488883 : Blo 1080619 5488883 := bstep (se 1 (by rfl) ⟨4116662, by rfl⟩ : syracuseStep 5488883 = 8233325) B8233325
theorem B1622441 : Blo 1080619 1622441 := bstep (se 2 (by rfl) ⟨608415, by rfl⟩ : syracuseStep 1622441 = 1216831) B1216831
theorem B1625183 : Blo 1080619 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B1824511 : Blo 1080619 1824511 := bstep (se 1 (by rfl) ⟨1368383, by rfl⟩ : syracuseStep 1824511 = 2736767) B2736767
theorem B3463337 : Blo 1080619 3463337 := bstep (se 2 (by rfl) ⟨1298751, by rfl⟩ : syracuseStep 3463337 = 2597503) B2597503
theorem B12311351 : Blo 1080619 12311351 := bstep (se 1 (by rfl) ⟨9233513, by rfl⟩ : syracuseStep 12311351 = 18467027) B18467027
theorem B13328297 : Blo 1080619 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B12312809 : Blo 1080619 12312809 := bstep (se 2 (by rfl) ⟨4617303, by rfl⟩ : syracuseStep 12312809 = 9234607) B9234607
theorem B10019375 : Blo 1080619 10019375 := bstep (se 1 (by rfl) ⟨7514531, by rfl⟩ : syracuseStep 10019375 = 15029063) B15029063
theorem B5701439 : Blo 1080619 5701439 := bstep (se 1 (by rfl) ⟨4276079, by rfl⟩ : syracuseStep 5701439 = 8552159) B8552159
theorem B1081627 : Blo 1080619 1081627 := bstep (se 1 (by rfl) ⟨811220, by rfl⟩ : syracuseStep 1081627 = 1622441) B1622441
theorem B15599087 : Blo 1080619 15599087 := bstep (se 1 (by rfl) ⟨11699315, by rfl⟩ : syracuseStep 15599087 = 23398631) B23398631
theorem B1083455 : Blo 1080619 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B21368927 : Blo 1080619 21368927 := bstep (se 1 (by rfl) ⟨16026695, by rfl⟩ : syracuseStep 21368927 = 32053391) B32053391
theorem B8885531 : Blo 1080619 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B2432681 : Blo 1080619 2432681 := bstep (se 2 (by rfl) ⟨912255, by rfl⟩ : syracuseStep 2432681 = 1824511) B1824511
theorem B2435327 : Blo 1080619 2435327 := bstep (se 1 (by rfl) ⟨1826495, by rfl⟩ : syracuseStep 2435327 = 3652991) B3652991
theorem B8207567 : Blo 1080619 8207567 := bstep (se 1 (by rfl) ⟨6155675, by rfl⟩ : syracuseStep 8207567 = 12311351) B12311351
theorem B8208539 : Blo 1080619 8208539 := bstep (se 1 (by rfl) ⟨6156404, by rfl⟩ : syracuseStep 8208539 = 12312809) B12312809
theorem B3659255 : Blo 1080619 3659255 := bstep (se 1 (by rfl) ⟨2744441, by rfl⟩ : syracuseStep 3659255 = 5488883) B5488883
theorem B5854847 : Blo 1080619 5854847 := bstep (se 1 (by rfl) ⟨4391135, by rfl⟩ : syracuseStep 5854847 = 8782271) B8782271
theorem B6679583 : Blo 1080619 6679583 := bstep (se 1 (by rfl) ⟨5009687, by rfl⟩ : syracuseStep 6679583 = 10019375) B10019375
theorem B9235565 : Blo 1080619 9235565 := bstep (se 3 (by rfl) ⟨1731668, by rfl⟩ : syracuseStep 9235565 = 3463337) B3463337
theorem B42759359 : Blo 1080619 42759359 := bstep (se 1 (by rfl) ⟨32069519, by rfl⟩ : syracuseStep 42759359 = 64139039) B64139039
theorem B4216452893 : Blo 1080619 4216452893 := bstep (se 3 (by rfl) ⟨790584917, by rfl⟩ : syracuseStep 4216452893 = 1581169835) B1581169835
theorem B15203837 : Blo 1080619 15203837 := bstep (se 3 (by rfl) ⟨2850719, by rfl⟩ : syracuseStep 15203837 = 5701439) B5701439
theorem B5472359 : Blo 1080619 5472359 := bstep (se 1 (by rfl) ⟨4104269, by rfl⟩ : syracuseStep 5472359 = 8208539) B8208539
theorem B10135891 : Blo 1080619 10135891 := bstep (se 1 (by rfl) ⟨7601918, by rfl⟩ : syracuseStep 10135891 = 15203837) B15203837
theorem B10399391 : Blo 1080619 10399391 := bstep (se 1 (by rfl) ⟨7799543, by rfl⟩ : syracuseStep 10399391 = 15599087) B15599087
theorem B2439503 : Blo 1080619 2439503 := bstep (se 1 (by rfl) ⟨1829627, by rfl⟩ : syracuseStep 2439503 = 3659255) B3659255
theorem B15612925 : Blo 1080619 15612925 := bstep (se 3 (by rfl) ⟨2927423, by rfl⟩ : syracuseStep 15612925 = 5854847) B5854847
theorem B1621787 : Blo 1080619 1621787 := bstep (se 1 (by rfl) ⟨1216340, by rfl⟩ : syracuseStep 1621787 = 2432681) B2432681
theorem B1623551 : Blo 1080619 1623551 := bstep (se 1 (by rfl) ⟨1217663, by rfl⟩ : syracuseStep 1623551 = 2435327) B2435327
theorem B14245951 : Blo 1080619 14245951 := bstep (se 1 (by rfl) ⟨10684463, by rfl⟩ : syracuseStep 14245951 = 21368927) B21368927
theorem B5923687 : Blo 1080619 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B4453055 : Blo 1080619 4453055 := bstep (se 1 (by rfl) ⟨3339791, by rfl⟩ : syracuseStep 4453055 = 6679583) B6679583
theorem B6157043 : Blo 1080619 6157043 := bstep (se 1 (by rfl) ⟨4617782, by rfl⟩ : syracuseStep 6157043 = 9235565) B9235565
theorem B28506239 : Blo 1080619 28506239 := bstep (se 1 (by rfl) ⟨21379679, by rfl⟩ : syracuseStep 28506239 = 42759359) B42759359
theorem B2810968595 : Blo 1080619 2810968595 := bstep (se 1 (by rfl) ⟨2108226446, by rfl⟩ : syracuseStep 2810968595 = 4216452893) B4216452893
theorem B5471711 : Blo 1080619 5471711 := bstep (se 1 (by rfl) ⟨4103783, by rfl⟩ : syracuseStep 5471711 = 8207567) B8207567
theorem B1082367 : Blo 1080619 1082367 := bstep (se 1 (by rfl) ⟨811775, by rfl⟩ : syracuseStep 1082367 = 1623551) B1623551
theorem B7898249 : Blo 1080619 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B4104695 : Blo 1080619 4104695 := bstep (se 1 (by rfl) ⟨3078521, by rfl⟩ : syracuseStep 4104695 = 6157043) B6157043
theorem B20817233 : Blo 1080619 20817233 := bstep (se 2 (by rfl) ⟨7806462, by rfl⟩ : syracuseStep 20817233 = 15612925) B15612925
theorem B1873979063 : Blo 1080619 1873979063 := bstep (se 1 (by rfl) ⟨1405484297, by rfl⟩ : syracuseStep 1873979063 = 2810968595) B2810968595
theorem B3647807 : Blo 1080619 3647807 := bstep (se 1 (by rfl) ⟨2735855, by rfl⟩ : syracuseStep 3647807 = 5471711) B5471711
theorem B3648239 : Blo 1080619 3648239 := bstep (se 1 (by rfl) ⟨2736179, by rfl⟩ : syracuseStep 3648239 = 5472359) B5472359
theorem B13514521 : Blo 1080619 13514521 := bstep (se 2 (by rfl) ⟨5067945, by rfl⟩ : syracuseStep 13514521 = 10135891) B10135891
theorem B6932927 : Blo 1080619 6932927 := bstep (se 1 (by rfl) ⟨5199695, by rfl⟩ : syracuseStep 6932927 = 10399391) B10399391
theorem B2968703 : Blo 1080619 2968703 := bstep (se 1 (by rfl) ⟨2226527, by rfl⟩ : syracuseStep 2968703 = 4453055) B4453055
theorem B1626335 : Blo 1080619 1626335 := bstep (se 1 (by rfl) ⟨1219751, by rfl⟩ : syracuseStep 1626335 = 2439503) B2439503
theorem B18994601 : Blo 1080619 18994601 := bstep (se 2 (by rfl) ⟨7122975, by rfl⟩ : syracuseStep 18994601 = 14245951) B14245951
theorem B19004159 : Blo 1080619 19004159 := bstep (se 1 (by rfl) ⟨14253119, by rfl⟩ : syracuseStep 19004159 = 28506239) B28506239
theorem B1081191 : Blo 1080619 1081191 := bstep (se 1 (by rfl) ⟨810893, by rfl⟩ : syracuseStep 1081191 = 1621787) B1621787
theorem B4621951 : Blo 1080619 4621951 := bstep (se 1 (by rfl) ⟨3466463, by rfl⟩ : syracuseStep 4621951 = 6932927) B6932927
theorem B1084223 : Blo 1080619 1084223 := bstep (se 1 (by rfl) ⟨813167, by rfl⟩ : syracuseStep 1084223 = 1626335) B1626335
theorem B1249319375 : Blo 1080619 1249319375 := bstep (se 1 (by rfl) ⟨936989531, by rfl⟩ : syracuseStep 1249319375 = 1873979063) B1873979063
theorem B2431871 : Blo 1080619 2431871 := bstep (se 1 (by rfl) ⟨1823903, by rfl⟩ : syracuseStep 2431871 = 3647807) B3647807
theorem B2432159 : Blo 1080619 2432159 := bstep (se 1 (by rfl) ⟨1824119, by rfl⟩ : syracuseStep 2432159 = 3648239) B3648239
theorem B1979135 : Blo 1080619 1979135 := bstep (se 1 (by rfl) ⟨1484351, by rfl⟩ : syracuseStep 1979135 = 2968703) B2968703
theorem B12663067 : Blo 1080619 12663067 := bstep (se 1 (by rfl) ⟨9497300, by rfl⟩ : syracuseStep 12663067 = 18994601) B18994601
theorem B2736463 : Blo 1080619 2736463 := bstep (se 1 (by rfl) ⟨2052347, by rfl⟩ : syracuseStep 2736463 = 4104695) B4104695
theorem B13878155 : Blo 1080619 13878155 := bstep (se 1 (by rfl) ⟨10408616, by rfl⟩ : syracuseStep 13878155 = 20817233) B20817233
theorem B50677757 : Blo 1080619 50677757 := bstep (se 3 (by rfl) ⟨9502079, by rfl⟩ : syracuseStep 50677757 = 19004159) B19004159
theorem B5265499 : Blo 1080619 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B18019361 : Blo 1080619 18019361 := bstep (se 2 (by rfl) ⟨6757260, by rfl⟩ : syracuseStep 18019361 = 13514521) B13514521
theorem B33785171 : Blo 1080619 33785171 := bstep (se 1 (by rfl) ⟨25338878, by rfl⟩ : syracuseStep 33785171 = 50677757) B50677757
theorem B6162601 : Blo 1080619 6162601 := bstep (se 2 (by rfl) ⟨2310975, by rfl⟩ : syracuseStep 6162601 = 4621951) B4621951
theorem B7020665 : Blo 1080619 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B16884089 : Blo 1080619 16884089 := bstep (se 2 (by rfl) ⟨6331533, by rfl⟩ : syracuseStep 16884089 = 12663067) B12663067
theorem B1319423 : Blo 1080619 1319423 := bstep (se 1 (by rfl) ⟨989567, by rfl⟩ : syracuseStep 1319423 = 1979135) B1979135
theorem B3648617 : Blo 1080619 3648617 := bstep (se 2 (by rfl) ⟨1368231, by rfl⟩ : syracuseStep 3648617 = 2736463) B2736463
theorem B9252103 : Blo 1080619 9252103 := bstep (se 1 (by rfl) ⟨6939077, by rfl⟩ : syracuseStep 9252103 = 13878155) B13878155
theorem B832879583 : Blo 1080619 832879583 := bstep (se 1 (by rfl) ⟨624659687, by rfl⟩ : syracuseStep 832879583 = 1249319375) B1249319375
theorem B1621247 : Blo 1080619 1621247 := bstep (se 1 (by rfl) ⟨1215935, by rfl⟩ : syracuseStep 1621247 = 2431871) B2431871
theorem B1621439 : Blo 1080619 1621439 := bstep (se 1 (by rfl) ⟨1216079, by rfl⟩ : syracuseStep 1621439 = 2432159) B2432159
theorem B12012907 : Blo 1080619 12012907 := bstep (se 1 (by rfl) ⟨9009680, by rfl⟩ : syracuseStep 12012907 = 18019361) B18019361
theorem B2432411 : Blo 1080619 2432411 := bstep (se 1 (by rfl) ⟨1824308, by rfl⟩ : syracuseStep 2432411 = 3648617) B3648617
theorem B22523447 : Blo 1080619 22523447 := bstep (se 1 (by rfl) ⟨16892585, by rfl⟩ : syracuseStep 22523447 = 33785171) B33785171
theorem B12336137 : Blo 1080619 12336137 := bstep (se 2 (by rfl) ⟨4626051, by rfl⟩ : syracuseStep 12336137 = 9252103) B9252103
theorem B14073845 : Blo 1080619 14073845 := bstep (se 5 (by rfl) ⟨659711, by rfl⟩ : syracuseStep 14073845 = 1319423) B1319423
theorem B11256059 : Blo 1080619 11256059 := bstep (se 1 (by rfl) ⟨8442044, by rfl⟩ : syracuseStep 11256059 = 16884089) B16884089
theorem B8216801 : Blo 1080619 8216801 := bstep (se 2 (by rfl) ⟨3081300, by rfl⟩ : syracuseStep 8216801 = 6162601) B6162601
theorem B16017209 : Blo 1080619 16017209 := bstep (se 2 (by rfl) ⟨6006453, by rfl⟩ : syracuseStep 16017209 = 12012907) B12012907
theorem B4680443 : Blo 1080619 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B555253055 : Blo 1080619 555253055 := bstep (se 1 (by rfl) ⟨416439791, by rfl⟩ : syracuseStep 555253055 = 832879583) B832879583
theorem B1080831 : Blo 1080619 1080831 := bstep (se 1 (by rfl) ⟨810623, by rfl⟩ : syracuseStep 1080831 = 1621247) B1621247
theorem B1080959 : Blo 1080619 1080959 := bstep (se 1 (by rfl) ⟨810719, by rfl⟩ : syracuseStep 1080959 = 1621439) B1621439
theorem B7504039 : Blo 1080619 7504039 := bstep (se 1 (by rfl) ⟨5628029, by rfl⟩ : syracuseStep 7504039 = 11256059) B11256059
theorem B5477867 : Blo 1080619 5477867 := bstep (se 1 (by rfl) ⟨4108400, by rfl⟩ : syracuseStep 5477867 = 8216801) B8216801
theorem B3120295 : Blo 1080619 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B15015631 : Blo 1080619 15015631 := bstep (se 1 (by rfl) ⟨11261723, by rfl⟩ : syracuseStep 15015631 = 22523447) B22523447
theorem B37530253 : Blo 1080619 37530253 := bstep (se 3 (by rfl) ⟨7036922, by rfl⟩ : syracuseStep 37530253 = 14073845) B14073845
theorem B1621607 : Blo 1080619 1621607 := bstep (se 1 (by rfl) ⟨1216205, by rfl⟩ : syracuseStep 1621607 = 2432411) B2432411
theorem B370168703 : Blo 1080619 370168703 := bstep (se 1 (by rfl) ⟨277626527, by rfl⟩ : syracuseStep 370168703 = 555253055) B555253055
theorem B10678139 : Blo 1080619 10678139 := bstep (se 1 (by rfl) ⟨8008604, by rfl⟩ : syracuseStep 10678139 = 16017209) B16017209
theorem B8224091 : Blo 1080619 8224091 := bstep (se 1 (by rfl) ⟨6168068, by rfl⟩ : syracuseStep 8224091 = 12336137) B12336137
theorem B246779135 : Blo 1080619 246779135 := bstep (se 1 (by rfl) ⟨185084351, by rfl⟩ : syracuseStep 246779135 = 370168703) B370168703
theorem B50040337 : Blo 1080619 50040337 := bstep (se 2 (by rfl) ⟨18765126, by rfl⟩ : syracuseStep 50040337 = 37530253) B37530253
theorem B7118759 : Blo 1080619 7118759 := bstep (se 1 (by rfl) ⟨5339069, by rfl⟩ : syracuseStep 7118759 = 10678139) B10678139
theorem B5482727 : Blo 1080619 5482727 := bstep (se 1 (by rfl) ⟨4112045, by rfl⟩ : syracuseStep 5482727 = 8224091) B8224091
theorem B10005385 : Blo 1080619 10005385 := bstep (se 2 (by rfl) ⟨3752019, by rfl⟩ : syracuseStep 10005385 = 7504039) B7504039
theorem B3651911 : Blo 1080619 3651911 := bstep (se 1 (by rfl) ⟨2738933, by rfl⟩ : syracuseStep 3651911 = 5477867) B5477867
theorem B4160393 : Blo 1080619 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B20020841 : Blo 1080619 20020841 := bstep (se 2 (by rfl) ⟨7507815, by rfl⟩ : syracuseStep 20020841 = 15015631) B15015631
theorem B1081071 : Blo 1080619 1081071 := bstep (se 1 (by rfl) ⟨810803, by rfl⟩ : syracuseStep 1081071 = 1621607) B1621607
theorem B13340513 : Blo 1080619 13340513 := bstep (se 2 (by rfl) ⟨5002692, by rfl⟩ : syracuseStep 13340513 = 10005385) B10005385
theorem B66720449 : Blo 1080619 66720449 := bstep (se 2 (by rfl) ⟨25020168, by rfl⟩ : syracuseStep 66720449 = 50040337) B50040337
theorem B2434607 : Blo 1080619 2434607 := bstep (se 1 (by rfl) ⟨1825955, by rfl⟩ : syracuseStep 2434607 = 3651911) B3651911
theorem B13347227 : Blo 1080619 13347227 := bstep (se 1 (by rfl) ⟨10010420, by rfl⟩ : syracuseStep 13347227 = 20020841) B20020841
theorem B18983357 : Blo 1080619 18983357 := bstep (se 3 (by rfl) ⟨3559379, by rfl⟩ : syracuseStep 18983357 = 7118759) B7118759
theorem B3655151 : Blo 1080619 3655151 := bstep (se 1 (by rfl) ⟨2741363, by rfl⟩ : syracuseStep 3655151 = 5482727) B5482727
theorem B2773595 : Blo 1080619 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B164519423 : Blo 1080619 164519423 := bstep (se 1 (by rfl) ⟨123389567, by rfl⟩ : syracuseStep 164519423 = 246779135) B246779135
theorem B109679615 : Blo 1080619 109679615 := bstep (se 1 (by rfl) ⟨82259711, by rfl⟩ : syracuseStep 109679615 = 164519423) B164519423
theorem B35592605 : Blo 1080619 35592605 := bstep (se 3 (by rfl) ⟨6673613, by rfl⟩ : syracuseStep 35592605 = 13347227) B13347227
theorem B12655571 : Blo 1080619 12655571 := bstep (se 1 (by rfl) ⟨9491678, by rfl⟩ : syracuseStep 12655571 = 18983357) B18983357
theorem B2436767 : Blo 1080619 2436767 := bstep (se 1 (by rfl) ⟨1827575, by rfl⟩ : syracuseStep 2436767 = 3655151) B3655151
theorem B8893675 : Blo 1080619 8893675 := bstep (se 1 (by rfl) ⟨6670256, by rfl⟩ : syracuseStep 8893675 = 13340513) B13340513
theorem B1849063 : Blo 1080619 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B44480299 : Blo 1080619 44480299 := bstep (se 1 (by rfl) ⟨33360224, by rfl⟩ : syracuseStep 44480299 = 66720449) B66720449
theorem B1623071 : Blo 1080619 1623071 := bstep (se 1 (by rfl) ⟨1217303, by rfl⟩ : syracuseStep 1623071 = 2434607) B2434607
theorem B1082047 : Blo 1080619 1082047 := bstep (se 1 (by rfl) ⟨811535, by rfl⟩ : syracuseStep 1082047 = 1623071) B1623071
theorem B23728403 : Blo 1080619 23728403 := bstep (se 1 (by rfl) ⟨17796302, by rfl⟩ : syracuseStep 23728403 = 35592605) B35592605
theorem B2465417 : Blo 1080619 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B73119743 : Blo 1080619 73119743 := bstep (se 1 (by rfl) ⟨54839807, by rfl⟩ : syracuseStep 73119743 = 109679615) B109679615
theorem B1624511 : Blo 1080619 1624511 := bstep (se 1 (by rfl) ⟨1218383, by rfl⟩ : syracuseStep 1624511 = 2436767) B2436767
theorem B134992757 : Blo 1080619 134992757 := bstep (se 5 (by rfl) ⟨6327785, by rfl⟩ : syracuseStep 134992757 = 12655571) B12655571
theorem B11858233 : Blo 1080619 11858233 := bstep (se 2 (by rfl) ⟨4446837, by rfl⟩ : syracuseStep 11858233 = 8893675) B8893675
theorem B59307065 : Blo 1080619 59307065 := bstep (se 2 (by rfl) ⟨22240149, by rfl⟩ : syracuseStep 59307065 = 44480299) B44480299
theorem B63275741 : Blo 1080619 63275741 := bstep (se 3 (by rfl) ⟨11864201, by rfl⟩ : syracuseStep 63275741 = 23728403) B23728403
theorem B1083007 : Blo 1080619 1083007 := bstep (se 1 (by rfl) ⟨812255, by rfl⟩ : syracuseStep 1083007 = 1624511) B1624511
theorem B89995171 : Blo 1080619 89995171 := bstep (se 1 (by rfl) ⟨67496378, by rfl⟩ : syracuseStep 89995171 = 134992757) B134992757
theorem B15810977 : Blo 1080619 15810977 := bstep (se 2 (by rfl) ⟨5929116, by rfl⟩ : syracuseStep 15810977 = 11858233) B11858233
theorem B39538043 : Blo 1080619 39538043 := bstep (se 1 (by rfl) ⟨29653532, by rfl⟩ : syracuseStep 39538043 = 59307065) B59307065
theorem B48746495 : Blo 1080619 48746495 := bstep (se 1 (by rfl) ⟨36559871, by rfl⟩ : syracuseStep 48746495 = 73119743) B73119743
theorem B6574445 : Blo 1080619 6574445 := bstep (se 3 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 6574445 = 2465417) B2465417
theorem B42183827 : Blo 1080619 42183827 := bstep (se 1 (by rfl) ⟨31637870, by rfl⟩ : syracuseStep 42183827 = 63275741) B63275741
theorem B26358695 : Blo 1080619 26358695 := bstep (se 1 (by rfl) ⟨19769021, by rfl⟩ : syracuseStep 26358695 = 39538043) B39538043
theorem B42162605 : Blo 1080619 42162605 := bstep (se 3 (by rfl) ⟨7905488, by rfl⟩ : syracuseStep 42162605 = 15810977) B15810977
theorem B4382963 : Blo 1080619 4382963 := bstep (se 1 (by rfl) ⟨3287222, by rfl⟩ : syracuseStep 4382963 = 6574445) B6574445
theorem B119993561 : Blo 1080619 119993561 := bstep (se 2 (by rfl) ⟨44997585, by rfl⟩ : syracuseStep 119993561 = 89995171) B89995171
theorem B129990653 : Blo 1080619 129990653 := bstep (se 3 (by rfl) ⟨24373247, by rfl⟩ : syracuseStep 129990653 = 48746495) B48746495
theorem B2921975 : Blo 1080619 2921975 := bstep (se 1 (by rfl) ⟨2191481, by rfl⟩ : syracuseStep 2921975 = 4382963) B4382963
theorem B28122551 : Blo 1080619 28122551 := bstep (se 1 (by rfl) ⟨21091913, by rfl⟩ : syracuseStep 28122551 = 42183827) B42183827
theorem B17572463 : Blo 1080619 17572463 := bstep (se 1 (by rfl) ⟨13179347, by rfl⟩ : syracuseStep 17572463 = 26358695) B26358695
theorem B79995707 : Blo 1080619 79995707 := bstep (se 1 (by rfl) ⟨59996780, by rfl⟩ : syracuseStep 79995707 = 119993561) B119993561
theorem B86660435 : Blo 1080619 86660435 := bstep (se 1 (by rfl) ⟨64995326, by rfl⟩ : syracuseStep 86660435 = 129990653) B129990653
theorem B28108403 : Blo 1080619 28108403 := bstep (se 1 (by rfl) ⟨21081302, by rfl⟩ : syracuseStep 28108403 = 42162605) B42162605
theorem B57773623 : Blo 1080619 57773623 := bstep (se 1 (by rfl) ⟨43330217, by rfl⟩ : syracuseStep 57773623 = 86660435) B86660435
theorem B18748367 : Blo 1080619 18748367 := bstep (se 1 (by rfl) ⟨14061275, by rfl⟩ : syracuseStep 18748367 = 28122551) B28122551
theorem B1947983 : Blo 1080619 1947983 := bstep (se 1 (by rfl) ⟨1460987, by rfl⟩ : syracuseStep 1947983 = 2921975) B2921975
theorem B11714975 : Blo 1080619 11714975 := bstep (se 1 (by rfl) ⟨8786231, by rfl⟩ : syracuseStep 11714975 = 17572463) B17572463
theorem B53330471 : Blo 1080619 53330471 := bstep (se 1 (by rfl) ⟨39997853, by rfl⟩ : syracuseStep 53330471 = 79995707) B79995707
theorem B18738935 : Blo 1080619 18738935 := bstep (se 1 (by rfl) ⟨14054201, by rfl⟩ : syracuseStep 18738935 = 28108403) B28108403
theorem B35553647 : Blo 1080619 35553647 := bstep (se 1 (by rfl) ⟨26665235, by rfl⟩ : syracuseStep 35553647 = 53330471) B53330471
theorem B12492623 : Blo 1080619 12492623 := bstep (se 1 (by rfl) ⟨9369467, by rfl⟩ : syracuseStep 12492623 = 18738935) B18738935
theorem B7809983 : Blo 1080619 7809983 := bstep (se 1 (by rfl) ⟨5857487, by rfl⟩ : syracuseStep 7809983 = 11714975) B11714975
theorem B12498911 : Blo 1080619 12498911 := bstep (se 1 (by rfl) ⟨9374183, by rfl⟩ : syracuseStep 12498911 = 18748367) B18748367
theorem B5194621 : Blo 1080619 5194621 := bstep (se 3 (by rfl) ⟨973991, by rfl⟩ : syracuseStep 5194621 = 1947983) B1947983
theorem B77031497 : Blo 1080619 77031497 := bstep (se 2 (by rfl) ⟨28886811, by rfl⟩ : syracuseStep 77031497 = 57773623) B57773623
theorem B8328415 : Blo 1080619 8328415 := bstep (se 1 (by rfl) ⟨6246311, by rfl⟩ : syracuseStep 8328415 = 12492623) B12492623
theorem B51354331 : Blo 1080619 51354331 := bstep (se 1 (by rfl) ⟨38515748, by rfl⟩ : syracuseStep 51354331 = 77031497) B77031497
theorem B8332607 : Blo 1080619 8332607 := bstep (se 1 (by rfl) ⟨6249455, by rfl⟩ : syracuseStep 8332607 = 12498911) B12498911
theorem B23702431 : Blo 1080619 23702431 := bstep (se 1 (by rfl) ⟨17776823, by rfl⟩ : syracuseStep 23702431 = 35553647) B35553647
theorem B6926161 : Blo 1080619 6926161 := bstep (se 2 (by rfl) ⟨2597310, by rfl⟩ : syracuseStep 6926161 = 5194621) B5194621
theorem B5206655 : Blo 1080619 5206655 := bstep (se 1 (by rfl) ⟨3904991, by rfl⟩ : syracuseStep 5206655 = 7809983) B7809983
theorem B273889765 : Blo 1080619 273889765 := bstep (se 4 (by rfl) ⟨25677165, by rfl⟩ : syracuseStep 273889765 = 51354331) B51354331
theorem B31603241 : Blo 1080619 31603241 := bstep (se 2 (by rfl) ⟨11851215, by rfl⟩ : syracuseStep 31603241 = 23702431) B23702431
theorem B5555071 : Blo 1080619 5555071 := bstep (se 1 (by rfl) ⟨4166303, by rfl⟩ : syracuseStep 5555071 = 8332607) B8332607
theorem B9234881 : Blo 1080619 9234881 := bstep (se 2 (by rfl) ⟨3463080, by rfl⟩ : syracuseStep 9234881 = 6926161) B6926161
theorem B11104553 : Blo 1080619 11104553 := bstep (se 2 (by rfl) ⟨4164207, by rfl⟩ : syracuseStep 11104553 = 8328415) B8328415
theorem B3471103 : Blo 1080619 3471103 := bstep (se 1 (by rfl) ⟨2603327, by rfl⟩ : syracuseStep 3471103 = 5206655) B5206655
theorem B7406761 : Blo 1080619 7406761 := bstep (se 2 (by rfl) ⟨2777535, by rfl⟩ : syracuseStep 7406761 = 5555071) B5555071
theorem B4628137 : Blo 1080619 4628137 := bstep (se 2 (by rfl) ⟨1735551, by rfl⟩ : syracuseStep 4628137 = 3471103) B3471103
theorem B365186353 : Blo 1080619 365186353 := bstep (se 2 (by rfl) ⟨136944882, by rfl⟩ : syracuseStep 365186353 = 273889765) B273889765
theorem B29612141 : Blo 1080619 29612141 := bstep (se 3 (by rfl) ⟨5552276, by rfl⟩ : syracuseStep 29612141 = 11104553) B11104553
theorem B84275309 : Blo 1080619 84275309 := bstep (se 3 (by rfl) ⟨15801620, by rfl⟩ : syracuseStep 84275309 = 31603241) B31603241
theorem B6156587 : Blo 1080619 6156587 := bstep (se 1 (by rfl) ⟨4617440, by rfl⟩ : syracuseStep 6156587 = 9234881) B9234881
theorem B4104391 : Blo 1080619 4104391 := bstep (se 1 (by rfl) ⟨3078293, by rfl⟩ : syracuseStep 4104391 = 6156587) B6156587
theorem B6170849 : Blo 1080619 6170849 := bstep (se 2 (by rfl) ⟨2314068, by rfl⟩ : syracuseStep 6170849 = 4628137) B4628137
theorem B9875681 : Blo 1080619 9875681 := bstep (se 2 (by rfl) ⟨3703380, by rfl⟩ : syracuseStep 9875681 = 7406761) B7406761
theorem B19741427 : Blo 1080619 19741427 := bstep (se 1 (by rfl) ⟨14806070, by rfl⟩ : syracuseStep 19741427 = 29612141) B29612141
theorem B486915137 : Blo 1080619 486915137 := bstep (se 2 (by rfl) ⟨182593176, by rfl⟩ : syracuseStep 486915137 = 365186353) B365186353
theorem B56183539 : Blo 1080619 56183539 := bstep (se 1 (by rfl) ⟨42137654, by rfl⟩ : syracuseStep 56183539 = 84275309) B84275309
theorem B5472521 : Blo 1080619 5472521 := bstep (se 2 (by rfl) ⟨2052195, by rfl⟩ : syracuseStep 5472521 = 4104391) B4104391
theorem B74911385 : Blo 1080619 74911385 := bstep (se 2 (by rfl) ⟨28091769, by rfl⟩ : syracuseStep 74911385 = 56183539) B56183539
theorem B324610091 : Blo 1080619 324610091 := bstep (se 1 (by rfl) ⟨243457568, by rfl⟩ : syracuseStep 324610091 = 486915137) B486915137
theorem B4113899 : Blo 1080619 4113899 := bstep (se 1 (by rfl) ⟨3085424, by rfl⟩ : syracuseStep 4113899 = 6170849) B6170849
theorem B13160951 : Blo 1080619 13160951 := bstep (se 1 (by rfl) ⟨9870713, by rfl⟩ : syracuseStep 13160951 = 19741427) B19741427
theorem B6583787 : Blo 1080619 6583787 := bstep (se 1 (by rfl) ⟨4937840, by rfl⟩ : syracuseStep 6583787 = 9875681) B9875681
theorem B49940923 : Blo 1080619 49940923 := bstep (se 1 (by rfl) ⟨37455692, by rfl⟩ : syracuseStep 49940923 = 74911385) B74911385
theorem B216406727 : Blo 1080619 216406727 := bstep (se 1 (by rfl) ⟨162305045, by rfl⟩ : syracuseStep 216406727 = 324610091) B324610091
theorem B3648347 : Blo 1080619 3648347 := bstep (se 1 (by rfl) ⟨2736260, by rfl⟩ : syracuseStep 3648347 = 5472521) B5472521
theorem B2742599 : Blo 1080619 2742599 := bstep (se 1 (by rfl) ⟨2056949, by rfl⟩ : syracuseStep 2742599 = 4113899) B4113899
theorem B8773967 : Blo 1080619 8773967 := bstep (se 1 (by rfl) ⟨6580475, by rfl⟩ : syracuseStep 8773967 = 13160951) B13160951
theorem B4389191 : Blo 1080619 4389191 := bstep (se 1 (by rfl) ⟨3291893, by rfl⟩ : syracuseStep 4389191 = 6583787) B6583787
theorem B23397245 : Blo 1080619 23397245 := bstep (se 3 (by rfl) ⟨4386983, by rfl⟩ : syracuseStep 23397245 = 8773967) B8773967
theorem B66587897 : Blo 1080619 66587897 := bstep (se 2 (by rfl) ⟨24970461, by rfl⟩ : syracuseStep 66587897 = 49940923) B49940923
theorem B2432231 : Blo 1080619 2432231 := bstep (se 1 (by rfl) ⟨1824173, by rfl⟩ : syracuseStep 2432231 = 3648347) B3648347
theorem B2926127 : Blo 1080619 2926127 := bstep (se 1 (by rfl) ⟨2194595, by rfl⟩ : syracuseStep 2926127 = 4389191) B4389191
theorem B1828399 : Blo 1080619 1828399 := bstep (se 1 (by rfl) ⟨1371299, by rfl⟩ : syracuseStep 1828399 = 2742599) B2742599
theorem B144271151 : Blo 1080619 144271151 := bstep (se 1 (by rfl) ⟨108203363, by rfl⟩ : syracuseStep 144271151 = 216406727) B216406727
theorem B15598163 : Blo 1080619 15598163 := bstep (se 1 (by rfl) ⟨11698622, by rfl⟩ : syracuseStep 15598163 = 23397245) B23397245
theorem B96180767 : Blo 1080619 96180767 := bstep (se 1 (by rfl) ⟨72135575, by rfl⟩ : syracuseStep 96180767 = 144271151) B144271151
theorem B2437865 : Blo 1080619 2437865 := bstep (se 2 (by rfl) ⟨914199, by rfl⟩ : syracuseStep 2437865 = 1828399) B1828399
theorem B1621487 : Blo 1080619 1621487 := bstep (se 1 (by rfl) ⟨1216115, by rfl⟩ : syracuseStep 1621487 = 2432231) B2432231
theorem B1950751 : Blo 1080619 1950751 := bstep (se 1 (by rfl) ⟨1463063, by rfl⟩ : syracuseStep 1950751 = 2926127) B2926127
theorem B44391931 : Blo 1080619 44391931 := bstep (se 1 (by rfl) ⟨33293948, by rfl⟩ : syracuseStep 44391931 = 66587897) B66587897
theorem B236756965 : Blo 1080619 236756965 := bstep (se 4 (by rfl) ⟨22195965, by rfl⟩ : syracuseStep 236756965 = 44391931) B44391931
theorem B10398775 : Blo 1080619 10398775 := bstep (se 1 (by rfl) ⟨7799081, by rfl⟩ : syracuseStep 10398775 = 15598163) B15598163
theorem B2601001 : Blo 1080619 2601001 := bstep (se 2 (by rfl) ⟨975375, by rfl⟩ : syracuseStep 2601001 = 1950751) B1950751
theorem B1625243 : Blo 1080619 1625243 := bstep (se 1 (by rfl) ⟨1218932, by rfl⟩ : syracuseStep 1625243 = 2437865) B2437865
theorem B64120511 : Blo 1080619 64120511 := bstep (se 1 (by rfl) ⟨48090383, by rfl⟩ : syracuseStep 64120511 = 96180767) B96180767
theorem B1080991 : Blo 1080619 1080991 := bstep (se 1 (by rfl) ⟨810743, by rfl⟩ : syracuseStep 1080991 = 1621487) B1621487
theorem B1083495 : Blo 1080619 1083495 := bstep (se 1 (by rfl) ⟨812621, by rfl⟩ : syracuseStep 1083495 = 1625243) B1625243
theorem B13865033 : Blo 1080619 13865033 := bstep (se 2 (by rfl) ⟨5199387, by rfl⟩ : syracuseStep 13865033 = 10398775) B10398775
theorem B13872005 : Blo 1080619 13872005 := bstep (se 4 (by rfl) ⟨1300500, by rfl⟩ : syracuseStep 13872005 = 2601001) B2601001
theorem B42747007 : Blo 1080619 42747007 := bstep (se 1 (by rfl) ⟨32060255, by rfl⟩ : syracuseStep 42747007 = 64120511) B64120511
theorem B315675953 : Blo 1080619 315675953 := bstep (se 2 (by rfl) ⟨118378482, by rfl⟩ : syracuseStep 315675953 = 236756965) B236756965
theorem B9243355 : Blo 1080619 9243355 := bstep (se 1 (by rfl) ⟨6932516, by rfl⟩ : syracuseStep 9243355 = 13865033) B13865033
theorem B9248003 : Blo 1080619 9248003 := bstep (se 1 (by rfl) ⟨6936002, by rfl⟩ : syracuseStep 9248003 = 13872005) B13872005
theorem B56996009 : Blo 1080619 56996009 := bstep (se 2 (by rfl) ⟨21373503, by rfl⟩ : syracuseStep 56996009 = 42747007) B42747007
theorem B210450635 : Blo 1080619 210450635 := bstep (se 1 (by rfl) ⟨157837976, by rfl⟩ : syracuseStep 210450635 = 315675953) B315675953
theorem B12324473 : Blo 1080619 12324473 := bstep (se 2 (by rfl) ⟨4621677, by rfl⟩ : syracuseStep 12324473 = 9243355) B9243355
theorem B6165335 : Blo 1080619 6165335 := bstep (se 1 (by rfl) ⟨4624001, by rfl⟩ : syracuseStep 6165335 = 9248003) B9248003
theorem B607957429 : Blo 1080619 607957429 := bstep (se 5 (by rfl) ⟨28498004, by rfl⟩ : syracuseStep 607957429 = 56996009) B56996009
theorem B140300423 : Blo 1080619 140300423 := bstep (se 1 (by rfl) ⟨105225317, by rfl⟩ : syracuseStep 140300423 = 210450635) B210450635
theorem B93533615 : Blo 1080619 93533615 := bstep (se 1 (by rfl) ⟨70150211, by rfl⟩ : syracuseStep 93533615 = 140300423) B140300423
theorem B4110223 : Blo 1080619 4110223 := bstep (se 1 (by rfl) ⟨3082667, by rfl⟩ : syracuseStep 4110223 = 6165335) B6165335
theorem B8216315 : Blo 1080619 8216315 := bstep (se 1 (by rfl) ⟨6162236, by rfl⟩ : syracuseStep 8216315 = 12324473) B12324473
theorem B810609905 : Blo 1080619 810609905 := bstep (se 2 (by rfl) ⟨303978714, by rfl⟩ : syracuseStep 810609905 = 607957429) B607957429
theorem B5477543 : Blo 1080619 5477543 := bstep (se 1 (by rfl) ⟨4108157, by rfl⟩ : syracuseStep 5477543 = 8216315) B8216315
theorem B5480297 : Blo 1080619 5480297 := bstep (se 2 (by rfl) ⟨2055111, by rfl⟩ : syracuseStep 5480297 = 4110223) B4110223
theorem B540406603 : Blo 1080619 540406603 := bstep (se 1 (by rfl) ⟨405304952, by rfl⟩ : syracuseStep 540406603 = 810609905) B810609905
theorem B62355743 : Blo 1080619 62355743 := bstep (se 1 (by rfl) ⟨46766807, by rfl⟩ : syracuseStep 62355743 = 93533615) B93533615
theorem B720542137 : Blo 1080619 720542137 := bstep (se 2 (by rfl) ⟨270203301, by rfl⟩ : syracuseStep 720542137 = 540406603) B540406603
theorem B3651695 : Blo 1080619 3651695 := bstep (se 1 (by rfl) ⟨2738771, by rfl⟩ : syracuseStep 3651695 = 5477543) B5477543
theorem B3653531 : Blo 1080619 3653531 := bstep (se 1 (by rfl) ⟨2740148, by rfl⟩ : syracuseStep 3653531 = 5480297) B5480297
theorem B41570495 : Blo 1080619 41570495 := bstep (se 1 (by rfl) ⟨31177871, by rfl⟩ : syracuseStep 41570495 = 62355743) B62355743
theorem B2434463 : Blo 1080619 2434463 := bstep (se 1 (by rfl) ⟨1825847, by rfl⟩ : syracuseStep 2434463 = 3651695) B3651695
theorem B2435687 : Blo 1080619 2435687 := bstep (se 1 (by rfl) ⟨1826765, by rfl⟩ : syracuseStep 2435687 = 3653531) B3653531
theorem B27713663 : Blo 1080619 27713663 := bstep (se 1 (by rfl) ⟨20785247, by rfl⟩ : syracuseStep 27713663 = 41570495) B41570495
theorem B960722849 : Blo 1080619 960722849 := bstep (se 2 (by rfl) ⟨360271068, by rfl⟩ : syracuseStep 960722849 = 720542137) B720542137
theorem B1622975 : Blo 1080619 1622975 := bstep (se 1 (by rfl) ⟨1217231, by rfl⟩ : syracuseStep 1622975 = 2434463) B2434463
theorem B1623791 : Blo 1080619 1623791 := bstep (se 1 (by rfl) ⟨1217843, by rfl⟩ : syracuseStep 1623791 = 2435687) B2435687
theorem B18475775 : Blo 1080619 18475775 := bstep (se 1 (by rfl) ⟨13856831, by rfl⟩ : syracuseStep 18475775 = 27713663) B27713663
theorem B640481899 : Blo 1080619 640481899 := bstep (se 1 (by rfl) ⟨480361424, by rfl⟩ : syracuseStep 640481899 = 960722849) B960722849
theorem B1081983 : Blo 1080619 1081983 := bstep (se 1 (by rfl) ⟨811487, by rfl⟩ : syracuseStep 1081983 = 1622975) B1622975
theorem B1082527 : Blo 1080619 1082527 := bstep (se 1 (by rfl) ⟨811895, by rfl⟩ : syracuseStep 1082527 = 1623791) B1623791
theorem B853975865 : Blo 1080619 853975865 := bstep (se 2 (by rfl) ⟨320240949, by rfl⟩ : syracuseStep 853975865 = 640481899) B640481899
theorem B12317183 : Blo 1080619 12317183 := bstep (se 1 (by rfl) ⟨9237887, by rfl⟩ : syracuseStep 12317183 = 18475775) B18475775
theorem B569317243 : Blo 1080619 569317243 := bstep (se 1 (by rfl) ⟨426987932, by rfl⟩ : syracuseStep 569317243 = 853975865) B853975865
theorem B8211455 : Blo 1080619 8211455 := bstep (se 1 (by rfl) ⟨6158591, by rfl⟩ : syracuseStep 8211455 = 12317183) B12317183
theorem B5474303 : Blo 1080619 5474303 := bstep (se 1 (by rfl) ⟨4105727, by rfl⟩ : syracuseStep 5474303 = 8211455) B8211455
theorem B759089657 : Blo 1080619 759089657 := bstep (se 2 (by rfl) ⟨284658621, by rfl⟩ : syracuseStep 759089657 = 569317243) B569317243
theorem B3649535 : Blo 1080619 3649535 := bstep (se 1 (by rfl) ⟨2737151, by rfl⟩ : syracuseStep 3649535 = 5474303) B5474303
theorem B506059771 : Blo 1080619 506059771 := bstep (se 1 (by rfl) ⟨379544828, by rfl⟩ : syracuseStep 506059771 = 759089657) B759089657
theorem B2433023 : Blo 1080619 2433023 := bstep (se 1 (by rfl) ⟨1824767, by rfl⟩ : syracuseStep 2433023 = 3649535) B3649535
theorem B674746361 : Blo 1080619 674746361 := bstep (se 2 (by rfl) ⟨253029885, by rfl⟩ : syracuseStep 674746361 = 506059771) B506059771
theorem B1622015 : Blo 1080619 1622015 := bstep (se 1 (by rfl) ⟨1216511, by rfl⟩ : syracuseStep 1622015 = 2433023) B2433023
theorem B449830907 : Blo 1080619 449830907 := bstep (se 1 (by rfl) ⟨337373180, by rfl⟩ : syracuseStep 449830907 = 674746361) B674746361
theorem B299887271 : Blo 1080619 299887271 := bstep (se 1 (by rfl) ⟨224915453, by rfl⟩ : syracuseStep 299887271 = 449830907) B449830907
theorem B1081343 : Blo 1080619 1081343 := bstep (se 1 (by rfl) ⟨811007, by rfl⟩ : syracuseStep 1081343 = 1622015) B1622015
theorem B199924847 : Blo 1080619 199924847 := bstep (se 1 (by rfl) ⟨149943635, by rfl⟩ : syracuseStep 199924847 = 299887271) B299887271
theorem B133283231 : Blo 1080619 133283231 := bstep (se 1 (by rfl) ⟨99962423, by rfl⟩ : syracuseStep 133283231 = 199924847) B199924847
theorem B88855487 : Blo 1080619 88855487 := bstep (se 1 (by rfl) ⟨66641615, by rfl⟩ : syracuseStep 88855487 = 133283231) B133283231
theorem B59236991 : Blo 1080619 59236991 := bstep (se 1 (by rfl) ⟨44427743, by rfl⟩ : syracuseStep 59236991 = 88855487) B88855487
theorem B39491327 : Blo 1080619 39491327 := bstep (se 1 (by rfl) ⟨29618495, by rfl⟩ : syracuseStep 39491327 = 59236991) B59236991
theorem B26327551 : Blo 1080619 26327551 := bstep (se 1 (by rfl) ⟨19745663, by rfl⟩ : syracuseStep 26327551 = 39491327) B39491327
theorem B35103401 : Blo 1080619 35103401 := bstep (se 2 (by rfl) ⟨13163775, by rfl⟩ : syracuseStep 35103401 = 26327551) B26327551
theorem B23402267 : Blo 1080619 23402267 := bstep (se 1 (by rfl) ⟨17551700, by rfl⟩ : syracuseStep 23402267 = 35103401) B35103401
theorem B15601511 : Blo 1080619 15601511 := bstep (se 1 (by rfl) ⟨11701133, by rfl⟩ : syracuseStep 15601511 = 23402267) B23402267
theorem B10401007 : Blo 1080619 10401007 := bstep (se 1 (by rfl) ⟨7800755, by rfl⟩ : syracuseStep 10401007 = 15601511) B15601511
theorem B13868009 : Blo 1080619 13868009 := bstep (se 2 (by rfl) ⟨5200503, by rfl⟩ : syracuseStep 13868009 = 10401007) B10401007
theorem B9245339 : Blo 1080619 9245339 := bstep (se 1 (by rfl) ⟨6934004, by rfl⟩ : syracuseStep 9245339 = 13868009) B13868009
theorem B6163559 : Blo 1080619 6163559 := bstep (se 1 (by rfl) ⟨4622669, by rfl⟩ : syracuseStep 6163559 = 9245339) B9245339
theorem B4109039 : Blo 1080619 4109039 := bstep (se 1 (by rfl) ⟨3081779, by rfl⟩ : syracuseStep 4109039 = 6163559) B6163559
theorem B2739359 : Blo 1080619 2739359 := bstep (se 1 (by rfl) ⟨2054519, by rfl⟩ : syracuseStep 2739359 = 4109039) B4109039
theorem B1826239 : Blo 1080619 1826239 := bstep (se 1 (by rfl) ⟨1369679, by rfl⟩ : syracuseStep 1826239 = 2739359) B2739359
theorem B2434985 : Blo 1080619 2434985 := bstep (se 2 (by rfl) ⟨913119, by rfl⟩ : syracuseStep 2434985 = 1826239) B1826239
theorem B1623323 : Blo 1080619 1623323 := bstep (se 1 (by rfl) ⟨1217492, by rfl⟩ : syracuseStep 1623323 = 2434985) B2434985
theorem B1082215 : Blo 1080619 1082215 := bstep (se 1 (by rfl) ⟨811661, by rfl⟩ : syracuseStep 1082215 = 1623323) B1623323

theorem C0 (j : ℕ) (h1 : 270154 ≤ j) (h2 : j ≤ 270853) : Blo 1080619 (4 * j + 3) := by
  interval_cases j
  · exact B1080619
  · exact B1080623
  · exact B1080627
  · exact B1080631
  · exact B1080635
  · exact B1080639
  · exact B1080643
  · exact B1080647
  · exact B1080651
  · exact B1080655
  · exact B1080659
  · exact B1080663
  · exact B1080667
  · exact B1080671
  · exact B1080675
  · exact B1080679
  · exact B1080683
  · exact B1080687
  · exact B1080691
  · exact B1080695
  · exact B1080699
  · exact B1080703
  · exact B1080707
  · exact B1080711
  · exact B1080715
  · exact B1080719
  · exact B1080723
  · exact B1080727
  · exact B1080731
  · exact B1080735
  · exact B1080739
  · exact B1080743
  · exact B1080747
  · exact B1080751
  · exact B1080755
  · exact B1080759
  · exact B1080763
  · exact B1080767
  · exact B1080771
  · exact B1080775
  · exact B1080779
  · exact B1080783
  · exact B1080787
  · exact B1080791
  · exact B1080795
  · exact B1080799
  · exact B1080803
  · exact B1080807
  · exact B1080811
  · exact B1080815
  · exact B1080819
  · exact B1080823
  · exact B1080827
  · exact B1080831
  · exact B1080835
  · exact B1080839
  · exact B1080843
  · exact B1080847
  · exact B1080851
  · exact B1080855
  · exact B1080859
  · exact B1080863
  · exact B1080867
  · exact B1080871
  · exact B1080875
  · exact B1080879
  · exact B1080883
  · exact B1080887
  · exact B1080891
  · exact B1080895
  · exact B1080899
  · exact B1080903
  · exact B1080907
  · exact B1080911
  · exact B1080915
  · exact B1080919
  · exact B1080923
  · exact B1080927
  · exact B1080931
  · exact B1080935
  · exact B1080939
  · exact B1080943
  · exact B1080947
  · exact B1080951
  · exact B1080955
  · exact B1080959
  · exact B1080963
  · exact B1080967
  · exact B1080971
  · exact B1080975
  · exact B1080979
  · exact B1080983
  · exact B1080987
  · exact B1080991
  · exact B1080995
  · exact B1080999
  · exact B1081003
  · exact B1081007
  · exact B1081011
  · exact B1081015
  · exact B1081019
  · exact B1081023
  · exact B1081027
  · exact B1081031
  · exact B1081035
  · exact B1081039
  · exact B1081043
  · exact B1081047
  · exact B1081051
  · exact B1081055
  · exact B1081059
  · exact B1081063
  · exact B1081067
  · exact B1081071
  · exact B1081075
  · exact B1081079
  · exact B1081083
  · exact B1081087
  · exact B1081091
  · exact B1081095
  · exact B1081099
  · exact B1081103
  · exact B1081107
  · exact B1081111
  · exact B1081115
  · exact B1081119
  · exact B1081123
  · exact B1081127
  · exact B1081131
  · exact B1081135
  · exact B1081139
  · exact B1081143
  · exact B1081147
  · exact B1081151
  · exact B1081155
  · exact B1081159
  · exact B1081163
  · exact B1081167
  · exact B1081171
  · exact B1081175
  · exact B1081179
  · exact B1081183
  · exact B1081187
  · exact B1081191
  · exact B1081195
  · exact B1081199
  · exact B1081203
  · exact B1081207
  · exact B1081211
  · exact B1081215
  · exact B1081219
  · exact B1081223
  · exact B1081227
  · exact B1081231
  · exact B1081235
  · exact B1081239
  · exact B1081243
  · exact B1081247
  · exact B1081251
  · exact B1081255
  · exact B1081259
  · exact B1081263
  · exact B1081267
  · exact B1081271
  · exact B1081275
  · exact B1081279
  · exact B1081283
  · exact B1081287
  · exact B1081291
  · exact B1081295
  · exact B1081299
  · exact B1081303
  · exact B1081307
  · exact B1081311
  · exact B1081315
  · exact B1081319
  · exact B1081323
  · exact B1081327
  · exact B1081331
  · exact B1081335
  · exact B1081339
  · exact B1081343
  · exact B1081347
  · exact B1081351
  · exact B1081355
  · exact B1081359
  · exact B1081363
  · exact B1081367
  · exact B1081371
  · exact B1081375
  · exact B1081379
  · exact B1081383
  · exact B1081387
  · exact B1081391
  · exact B1081395
  · exact B1081399
  · exact B1081403
  · exact B1081407
  · exact B1081411
  · exact B1081415
  · exact B1081419
  · exact B1081423
  · exact B1081427
  · exact B1081431
  · exact B1081435
  · exact B1081439
  · exact B1081443
  · exact B1081447
  · exact B1081451
  · exact B1081455
  · exact B1081459
  · exact B1081463
  · exact B1081467
  · exact B1081471
  · exact B1081475
  · exact B1081479
  · exact B1081483
  · exact B1081487
  · exact B1081491
  · exact B1081495
  · exact B1081499
  · exact B1081503
  · exact B1081507
  · exact B1081511
  · exact B1081515
  · exact B1081519
  · exact B1081523
  · exact B1081527
  · exact B1081531
  · exact B1081535
  · exact B1081539
  · exact B1081543
  · exact B1081547
  · exact B1081551
  · exact B1081555
  · exact B1081559
  · exact B1081563
  · exact B1081567
  · exact B1081571
  · exact B1081575
  · exact B1081579
  · exact B1081583
  · exact B1081587
  · exact B1081591
  · exact B1081595
  · exact B1081599
  · exact B1081603
  · exact B1081607
  · exact B1081611
  · exact B1081615
  · exact B1081619
  · exact B1081623
  · exact B1081627
  · exact B1081631
  · exact B1081635
  · exact B1081639
  · exact B1081643
  · exact B1081647
  · exact B1081651
  · exact B1081655
  · exact B1081659
  · exact B1081663
  · exact B1081667
  · exact B1081671
  · exact B1081675
  · exact B1081679
  · exact B1081683
  · exact B1081687
  · exact B1081691
  · exact B1081695
  · exact B1081699
  · exact B1081703
  · exact B1081707
  · exact B1081711
  · exact B1081715
  · exact B1081719
  · exact B1081723
  · exact B1081727
  · exact B1081731
  · exact B1081735
  · exact B1081739
  · exact B1081743
  · exact B1081747
  · exact B1081751
  · exact B1081755
  · exact B1081759
  · exact B1081763
  · exact B1081767
  · exact B1081771
  · exact B1081775
  · exact B1081779
  · exact B1081783
  · exact B1081787
  · exact B1081791
  · exact B1081795
  · exact B1081799
  · exact B1081803
  · exact B1081807
  · exact B1081811
  · exact B1081815
  · exact B1081819
  · exact B1081823
  · exact B1081827
  · exact B1081831
  · exact B1081835
  · exact B1081839
  · exact B1081843
  · exact B1081847
  · exact B1081851
  · exact B1081855
  · exact B1081859
  · exact B1081863
  · exact B1081867
  · exact B1081871
  · exact B1081875
  · exact B1081879
  · exact B1081883
  · exact B1081887
  · exact B1081891
  · exact B1081895
  · exact B1081899
  · exact B1081903
  · exact B1081907
  · exact B1081911
  · exact B1081915
  · exact B1081919
  · exact B1081923
  · exact B1081927
  · exact B1081931
  · exact B1081935
  · exact B1081939
  · exact B1081943
  · exact B1081947
  · exact B1081951
  · exact B1081955
  · exact B1081959
  · exact B1081963
  · exact B1081967
  · exact B1081971
  · exact B1081975
  · exact B1081979
  · exact B1081983
  · exact B1081987
  · exact B1081991
  · exact B1081995
  · exact B1081999
  · exact B1082003
  · exact B1082007
  · exact B1082011
  · exact B1082015
  · exact B1082019
  · exact B1082023
  · exact B1082027
  · exact B1082031
  · exact B1082035
  · exact B1082039
  · exact B1082043
  · exact B1082047
  · exact B1082051
  · exact B1082055
  · exact B1082059
  · exact B1082063
  · exact B1082067
  · exact B1082071
  · exact B1082075
  · exact B1082079
  · exact B1082083
  · exact B1082087
  · exact B1082091
  · exact B1082095
  · exact B1082099
  · exact B1082103
  · exact B1082107
  · exact B1082111
  · exact B1082115
  · exact B1082119
  · exact B1082123
  · exact B1082127
  · exact B1082131
  · exact B1082135
  · exact B1082139
  · exact B1082143
  · exact B1082147
  · exact B1082151
  · exact B1082155
  · exact B1082159
  · exact B1082163
  · exact B1082167
  · exact B1082171
  · exact B1082175
  · exact B1082179
  · exact B1082183
  · exact B1082187
  · exact B1082191
  · exact B1082195
  · exact B1082199
  · exact B1082203
  · exact B1082207
  · exact B1082211
  · exact B1082215
  · exact B1082219
  · exact B1082223
  · exact B1082227
  · exact B1082231
  · exact B1082235
  · exact B1082239
  · exact B1082243
  · exact B1082247
  · exact B1082251
  · exact B1082255
  · exact B1082259
  · exact B1082263
  · exact B1082267
  · exact B1082271
  · exact B1082275
  · exact B1082279
  · exact B1082283
  · exact B1082287
  · exact B1082291
  · exact B1082295
  · exact B1082299
  · exact B1082303
  · exact B1082307
  · exact B1082311
  · exact B1082315
  · exact B1082319
  · exact B1082323
  · exact B1082327
  · exact B1082331
  · exact B1082335
  · exact B1082339
  · exact B1082343
  · exact B1082347
  · exact B1082351
  · exact B1082355
  · exact B1082359
  · exact B1082363
  · exact B1082367
  · exact B1082371
  · exact B1082375
  · exact B1082379
  · exact B1082383
  · exact B1082387
  · exact B1082391
  · exact B1082395
  · exact B1082399
  · exact B1082403
  · exact B1082407
  · exact B1082411
  · exact B1082415
  · exact B1082419
  · exact B1082423
  · exact B1082427
  · exact B1082431
  · exact B1082435
  · exact B1082439
  · exact B1082443
  · exact B1082447
  · exact B1082451
  · exact B1082455
  · exact B1082459
  · exact B1082463
  · exact B1082467
  · exact B1082471
  · exact B1082475
  · exact B1082479
  · exact B1082483
  · exact B1082487
  · exact B1082491
  · exact B1082495
  · exact B1082499
  · exact B1082503
  · exact B1082507
  · exact B1082511
  · exact B1082515
  · exact B1082519
  · exact B1082523
  · exact B1082527
  · exact B1082531
  · exact B1082535
  · exact B1082539
  · exact B1082543
  · exact B1082547
  · exact B1082551
  · exact B1082555
  · exact B1082559
  · exact B1082563
  · exact B1082567
  · exact B1082571
  · exact B1082575
  · exact B1082579
  · exact B1082583
  · exact B1082587
  · exact B1082591
  · exact B1082595
  · exact B1082599
  · exact B1082603
  · exact B1082607
  · exact B1082611
  · exact B1082615
  · exact B1082619
  · exact B1082623
  · exact B1082627
  · exact B1082631
  · exact B1082635
  · exact B1082639
  · exact B1082643
  · exact B1082647
  · exact B1082651
  · exact B1082655
  · exact B1082659
  · exact B1082663
  · exact B1082667
  · exact B1082671
  · exact B1082675
  · exact B1082679
  · exact B1082683
  · exact B1082687
  · exact B1082691
  · exact B1082695
  · exact B1082699
  · exact B1082703
  · exact B1082707
  · exact B1082711
  · exact B1082715
  · exact B1082719
  · exact B1082723
  · exact B1082727
  · exact B1082731
  · exact B1082735
  · exact B1082739
  · exact B1082743
  · exact B1082747
  · exact B1082751
  · exact B1082755
  · exact B1082759
  · exact B1082763
  · exact B1082767
  · exact B1082771
  · exact B1082775
  · exact B1082779
  · exact B1082783
  · exact B1082787
  · exact B1082791
  · exact B1082795
  · exact B1082799
  · exact B1082803
  · exact B1082807
  · exact B1082811
  · exact B1082815
  · exact B1082819
  · exact B1082823
  · exact B1082827
  · exact B1082831
  · exact B1082835
  · exact B1082839
  · exact B1082843
  · exact B1082847
  · exact B1082851
  · exact B1082855
  · exact B1082859
  · exact B1082863
  · exact B1082867
  · exact B1082871
  · exact B1082875
  · exact B1082879
  · exact B1082883
  · exact B1082887
  · exact B1082891
  · exact B1082895
  · exact B1082899
  · exact B1082903
  · exact B1082907
  · exact B1082911
  · exact B1082915
  · exact B1082919
  · exact B1082923
  · exact B1082927
  · exact B1082931
  · exact B1082935
  · exact B1082939
  · exact B1082943
  · exact B1082947
  · exact B1082951
  · exact B1082955
  · exact B1082959
  · exact B1082963
  · exact B1082967
  · exact B1082971
  · exact B1082975
  · exact B1082979
  · exact B1082983
  · exact B1082987
  · exact B1082991
  · exact B1082995
  · exact B1082999
  · exact B1083003
  · exact B1083007
  · exact B1083011
  · exact B1083015
  · exact B1083019
  · exact B1083023
  · exact B1083027
  · exact B1083031
  · exact B1083035
  · exact B1083039
  · exact B1083043
  · exact B1083047
  · exact B1083051
  · exact B1083055
  · exact B1083059
  · exact B1083063
  · exact B1083067
  · exact B1083071
  · exact B1083075
  · exact B1083079
  · exact B1083083
  · exact B1083087
  · exact B1083091
  · exact B1083095
  · exact B1083099
  · exact B1083103
  · exact B1083107
  · exact B1083111
  · exact B1083115
  · exact B1083119
  · exact B1083123
  · exact B1083127
  · exact B1083131
  · exact B1083135
  · exact B1083139
  · exact B1083143
  · exact B1083147
  · exact B1083151
  · exact B1083155
  · exact B1083159
  · exact B1083163
  · exact B1083167
  · exact B1083171
  · exact B1083175
  · exact B1083179
  · exact B1083183
  · exact B1083187
  · exact B1083191
  · exact B1083195
  · exact B1083199
  · exact B1083203
  · exact B1083207
  · exact B1083211
  · exact B1083215
  · exact B1083219
  · exact B1083223
  · exact B1083227
  · exact B1083231
  · exact B1083235
  · exact B1083239
  · exact B1083243
  · exact B1083247
  · exact B1083251
  · exact B1083255
  · exact B1083259
  · exact B1083263
  · exact B1083267
  · exact B1083271
  · exact B1083275
  · exact B1083279
  · exact B1083283
  · exact B1083287
  · exact B1083291
  · exact B1083295
  · exact B1083299
  · exact B1083303
  · exact B1083307
  · exact B1083311
  · exact B1083315
  · exact B1083319
  · exact B1083323
  · exact B1083327
  · exact B1083331
  · exact B1083335
  · exact B1083339
  · exact B1083343
  · exact B1083347
  · exact B1083351
  · exact B1083355
  · exact B1083359
  · exact B1083363
  · exact B1083367
  · exact B1083371
  · exact B1083375
  · exact B1083379
  · exact B1083383
  · exact B1083387
  · exact B1083391
  · exact B1083395
  · exact B1083399
  · exact B1083403
  · exact B1083407
  · exact B1083411
  · exact B1083415

theorem C1 (j : ℕ) (h1 : 270854 ≤ j) (h2 : j ≤ 271154) : Blo 1080619 (4 * j + 3) := by
  interval_cases j
  · exact B1083419
  · exact B1083423
  · exact B1083427
  · exact B1083431
  · exact B1083435
  · exact B1083439
  · exact B1083443
  · exact B1083447
  · exact B1083451
  · exact B1083455
  · exact B1083459
  · exact B1083463
  · exact B1083467
  · exact B1083471
  · exact B1083475
  · exact B1083479
  · exact B1083483
  · exact B1083487
  · exact B1083491
  · exact B1083495
  · exact B1083499
  · exact B1083503
  · exact B1083507
  · exact B1083511
  · exact B1083515
  · exact B1083519
  · exact B1083523
  · exact B1083527
  · exact B1083531
  · exact B1083535
  · exact B1083539
  · exact B1083543
  · exact B1083547
  · exact B1083551
  · exact B1083555
  · exact B1083559
  · exact B1083563
  · exact B1083567
  · exact B1083571
  · exact B1083575
  · exact B1083579
  · exact B1083583
  · exact B1083587
  · exact B1083591
  · exact B1083595
  · exact B1083599
  · exact B1083603
  · exact B1083607
  · exact B1083611
  · exact B1083615
  · exact B1083619
  · exact B1083623
  · exact B1083627
  · exact B1083631
  · exact B1083635
  · exact B1083639
  · exact B1083643
  · exact B1083647
  · exact B1083651
  · exact B1083655
  · exact B1083659
  · exact B1083663
  · exact B1083667
  · exact B1083671
  · exact B1083675
  · exact B1083679
  · exact B1083683
  · exact B1083687
  · exact B1083691
  · exact B1083695
  · exact B1083699
  · exact B1083703
  · exact B1083707
  · exact B1083711
  · exact B1083715
  · exact B1083719
  · exact B1083723
  · exact B1083727
  · exact B1083731
  · exact B1083735
  · exact B1083739
  · exact B1083743
  · exact B1083747
  · exact B1083751
  · exact B1083755
  · exact B1083759
  · exact B1083763
  · exact B1083767
  · exact B1083771
  · exact B1083775
  · exact B1083779
  · exact B1083783
  · exact B1083787
  · exact B1083791
  · exact B1083795
  · exact B1083799
  · exact B1083803
  · exact B1083807
  · exact B1083811
  · exact B1083815
  · exact B1083819
  · exact B1083823
  · exact B1083827
  · exact B1083831
  · exact B1083835
  · exact B1083839
  · exact B1083843
  · exact B1083847
  · exact B1083851
  · exact B1083855
  · exact B1083859
  · exact B1083863
  · exact B1083867
  · exact B1083871
  · exact B1083875
  · exact B1083879
  · exact B1083883
  · exact B1083887
  · exact B1083891
  · exact B1083895
  · exact B1083899
  · exact B1083903
  · exact B1083907
  · exact B1083911
  · exact B1083915
  · exact B1083919
  · exact B1083923
  · exact B1083927
  · exact B1083931
  · exact B1083935
  · exact B1083939
  · exact B1083943
  · exact B1083947
  · exact B1083951
  · exact B1083955
  · exact B1083959
  · exact B1083963
  · exact B1083967
  · exact B1083971
  · exact B1083975
  · exact B1083979
  · exact B1083983
  · exact B1083987
  · exact B1083991
  · exact B1083995
  · exact B1083999
  · exact B1084003
  · exact B1084007
  · exact B1084011
  · exact B1084015
  · exact B1084019
  · exact B1084023
  · exact B1084027
  · exact B1084031
  · exact B1084035
  · exact B1084039
  · exact B1084043
  · exact B1084047
  · exact B1084051
  · exact B1084055
  · exact B1084059
  · exact B1084063
  · exact B1084067
  · exact B1084071
  · exact B1084075
  · exact B1084079
  · exact B1084083
  · exact B1084087
  · exact B1084091
  · exact B1084095
  · exact B1084099
  · exact B1084103
  · exact B1084107
  · exact B1084111
  · exact B1084115
  · exact B1084119
  · exact B1084123
  · exact B1084127
  · exact B1084131
  · exact B1084135
  · exact B1084139
  · exact B1084143
  · exact B1084147
  · exact B1084151
  · exact B1084155
  · exact B1084159
  · exact B1084163
  · exact B1084167
  · exact B1084171
  · exact B1084175
  · exact B1084179
  · exact B1084183
  · exact B1084187
  · exact B1084191
  · exact B1084195
  · exact B1084199
  · exact B1084203
  · exact B1084207
  · exact B1084211
  · exact B1084215
  · exact B1084219
  · exact B1084223
  · exact B1084227
  · exact B1084231
  · exact B1084235
  · exact B1084239
  · exact B1084243
  · exact B1084247
  · exact B1084251
  · exact B1084255
  · exact B1084259
  · exact B1084263
  · exact B1084267
  · exact B1084271
  · exact B1084275
  · exact B1084279
  · exact B1084283
  · exact B1084287
  · exact B1084291
  · exact B1084295
  · exact B1084299
  · exact B1084303
  · exact B1084307
  · exact B1084311
  · exact B1084315
  · exact B1084319
  · exact B1084323
  · exact B1084327
  · exact B1084331
  · exact B1084335
  · exact B1084339
  · exact B1084343
  · exact B1084347
  · exact B1084351
  · exact B1084355
  · exact B1084359
  · exact B1084363
  · exact B1084367
  · exact B1084371
  · exact B1084375
  · exact B1084379
  · exact B1084383
  · exact B1084387
  · exact B1084391
  · exact B1084395
  · exact B1084399
  · exact B1084403
  · exact B1084407
  · exact B1084411
  · exact B1084415
  · exact B1084419
  · exact B1084423
  · exact B1084427
  · exact B1084431
  · exact B1084435
  · exact B1084439
  · exact B1084443
  · exact B1084447
  · exact B1084451
  · exact B1084455
  · exact B1084459
  · exact B1084463
  · exact B1084467
  · exact B1084471
  · exact B1084475
  · exact B1084479
  · exact B1084483
  · exact B1084487
  · exact B1084491
  · exact B1084495
  · exact B1084499
  · exact B1084503
  · exact B1084507
  · exact B1084511
  · exact B1084515
  · exact B1084519
  · exact B1084523
  · exact B1084527
  · exact B1084531
  · exact B1084535
  · exact B1084539
  · exact B1084543
  · exact B1084547
  · exact B1084551
  · exact B1084555
  · exact B1084559
  · exact B1084563
  · exact B1084567
  · exact B1084571
  · exact B1084575
  · exact B1084579
  · exact B1084583
  · exact B1084587
  · exact B1084591
  · exact B1084595
  · exact B1084599
  · exact B1084603
  · exact B1084607
  · exact B1084611
  · exact B1084615
  · exact B1084619

theorem solution (m : ℕ) (hlo : 1080619 ≤ m) (hhi : m ≤ 1084619) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 270154 ≤ j := by omega
    have hj2 : j ≤ 271154 := by omega
    have hb : Blo 1080619 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 270854 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
