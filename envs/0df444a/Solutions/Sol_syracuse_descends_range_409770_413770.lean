-- Prove2me | solution 1 for syracuse_descends_range_409770_413770
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:50.491899+00:00
-- url     : https://prove2.me/submissions/bb9721fa-2af6-4b30-b381-df9714131360

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


theorem B459109 : Blo 409770 459109 := bbase (se 4 (by rfl) ⟨43041, by rfl⟩ : syracuseStep 459109 = 86083) (by norm_num)
theorem B1671653 : Blo 409770 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B1508005 : Blo 409770 1508005 := bbase (se 4 (by rfl) ⟨141375, by rfl⟩ : syracuseStep 1508005 = 282751) (by norm_num)
theorem B3572437 : Blo 409770 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B1508165 : Blo 409770 1508165 := bbase (se 4 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 1508165 = 282781) (by norm_num)
theorem B558181 : Blo 409770 558181 := bbase (se 4 (by rfl) ⟨52329, by rfl⟩ : syracuseStep 558181 = 104659) (by norm_num)
theorem B656677 : Blo 409770 656677 := bbase (se 4 (by rfl) ⟨61563, by rfl⟩ : syracuseStep 656677 = 123127) (by norm_num)
theorem B1901909 : Blo 409770 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B1246565 : Blo 409770 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B624109 : Blo 409770 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B493085 : Blo 409770 493085 := bbase (se 3 (by rfl) ⟨92453, by rfl⟩ : syracuseStep 493085 = 184907) (by norm_num)
theorem B3114773 : Blo 409770 3114773 := bbase (se 6 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 3114773 = 146005) (by norm_num)
theorem B493393 : Blo 409770 493393 := bbase (se 2 (by rfl) ⟨185022, by rfl⟩ : syracuseStep 493393 = 370045) (by norm_num)
theorem B657325 : Blo 409770 657325 := bbase (se 3 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 657325 = 246497) (by norm_num)
theorem B493609 : Blo 409770 493609 := bbase (se 2 (by rfl) ⟨185103, by rfl⟩ : syracuseStep 493609 = 370207) (by norm_num)
theorem B1411253 : Blo 409770 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B460993 : Blo 409770 460993 := bbase (se 2 (by rfl) ⟨172872, by rfl⟩ : syracuseStep 460993 = 345745) (by norm_num)
theorem B461029 : Blo 409770 461029 := bbase (se 4 (by rfl) ⟨43221, by rfl⟩ : syracuseStep 461029 = 86443) (by norm_num)
theorem B461065 : Blo 409770 461065 := bbase (se 2 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 461065 = 345799) (by norm_num)
theorem B461101 : Blo 409770 461101 := bbase (se 3 (by rfl) ⟨86456, by rfl⟩ : syracuseStep 461101 = 172913) (by norm_num)
theorem B461137 : Blo 409770 461137 := bbase (se 2 (by rfl) ⟨172926, by rfl⟩ : syracuseStep 461137 = 345853) (by norm_num)
theorem B461173 : Blo 409770 461173 := bbase (se 5 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 461173 = 43235) (by norm_num)
theorem B461209 : Blo 409770 461209 := bbase (se 2 (by rfl) ⟨172953, by rfl⟩ : syracuseStep 461209 = 345907) (by norm_num)
theorem B461245 : Blo 409770 461245 := bbase (se 3 (by rfl) ⟨86483, by rfl⟩ : syracuseStep 461245 = 172967) (by norm_num)
theorem B461281 : Blo 409770 461281 := bbase (se 2 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 461281 = 345961) (by norm_num)
theorem B461317 : Blo 409770 461317 := bbase (se 4 (by rfl) ⟨43248, by rfl⟩ : syracuseStep 461317 = 86497) (by norm_num)
theorem B461353 : Blo 409770 461353 := bbase (se 2 (by rfl) ⟨173007, by rfl⟩ : syracuseStep 461353 = 346015) (by norm_num)
theorem B461389 : Blo 409770 461389 := bbase (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) (by norm_num)
theorem B461425 : Blo 409770 461425 := bbase (se 2 (by rfl) ⟨173034, by rfl⟩ : syracuseStep 461425 = 346069) (by norm_num)
theorem B625277 : Blo 409770 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B494209 : Blo 409770 494209 := bbase (se 2 (by rfl) ⟨185328, by rfl⟩ : syracuseStep 494209 = 370657) (by norm_num)
theorem B461461 : Blo 409770 461461 := bbase (se 6 (by rfl) ⟨10815, by rfl⟩ : syracuseStep 461461 = 21631) (by norm_num)
theorem B985765 : Blo 409770 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B461497 : Blo 409770 461497 := bbase (se 2 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 461497 = 346123) (by norm_num)
theorem B625357 : Blo 409770 625357 := bbase (se 3 (by rfl) ⟨117254, by rfl⟩ : syracuseStep 625357 = 234509) (by norm_num)
theorem B461533 : Blo 409770 461533 := bbase (se 3 (by rfl) ⟨86537, by rfl⟩ : syracuseStep 461533 = 173075) (by norm_num)
theorem B461569 : Blo 409770 461569 := bbase (se 2 (by rfl) ⟨173088, by rfl⟩ : syracuseStep 461569 = 346177) (by norm_num)
theorem B461605 : Blo 409770 461605 := bbase (se 4 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 461605 = 86551) (by norm_num)
theorem B4000565 : Blo 409770 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B461641 : Blo 409770 461641 := bbase (se 2 (by rfl) ⟨173115, by rfl⟩ : syracuseStep 461641 = 346231) (by norm_num)
theorem B658253 : Blo 409770 658253 := bbase (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) (by norm_num)
theorem B461677 : Blo 409770 461677 := bbase (se 3 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 461677 = 173129) (by norm_num)
theorem B461713 : Blo 409770 461713 := bbase (se 2 (by rfl) ⟨173142, by rfl⟩ : syracuseStep 461713 = 346285) (by norm_num)
theorem B461749 : Blo 409770 461749 := bbase (se 5 (by rfl) ⟨21644, by rfl⟩ : syracuseStep 461749 = 43289) (by norm_num)
theorem B461785 : Blo 409770 461785 := bbase (se 2 (by rfl) ⟨173169, by rfl⟩ : syracuseStep 461785 = 346339) (by norm_num)
theorem B1313765 : Blo 409770 1313765 := bbase (se 4 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 1313765 = 246331) (by norm_num)
theorem B461821 : Blo 409770 461821 := bbase (se 3 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 461821 = 173183) (by norm_num)
theorem B461857 : Blo 409770 461857 := bbase (se 2 (by rfl) ⟨173196, by rfl⟩ : syracuseStep 461857 = 346393) (by norm_num)
theorem B461893 : Blo 409770 461893 := bbase (se 4 (by rfl) ⟨43302, by rfl⟩ : syracuseStep 461893 = 86605) (by norm_num)
theorem B461929 : Blo 409770 461929 := bbase (se 2 (by rfl) ⟨173223, by rfl⟩ : syracuseStep 461929 = 346447) (by norm_num)
theorem B1510517 : Blo 409770 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B461965 : Blo 409770 461965 := bbase (se 3 (by rfl) ⟨86618, by rfl⟩ : syracuseStep 461965 = 173237) (by norm_num)
theorem B462001 : Blo 409770 462001 := bbase (se 2 (by rfl) ⟨173250, by rfl⟩ : syracuseStep 462001 = 346501) (by norm_num)
theorem B462037 : Blo 409770 462037 := bbase (se 7 (by rfl) ⟨5414, by rfl⟩ : syracuseStep 462037 = 10829) (by norm_num)
theorem B462073 : Blo 409770 462073 := bbase (se 2 (by rfl) ⟨173277, by rfl⟩ : syracuseStep 462073 = 346555) (by norm_num)
theorem B986381 : Blo 409770 986381 := bbase (se 3 (by rfl) ⟨184946, by rfl⟩ : syracuseStep 986381 = 369893) (by norm_num)
theorem B658709 : Blo 409770 658709 := bbase (se 6 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 658709 = 30877) (by norm_num)
theorem B462109 : Blo 409770 462109 := bbase (se 3 (by rfl) ⟨86645, by rfl⟩ : syracuseStep 462109 = 173291) (by norm_num)
theorem B691517 : Blo 409770 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B462145 : Blo 409770 462145 := bbase (se 2 (by rfl) ⟨173304, by rfl⟩ : syracuseStep 462145 = 346609) (by norm_num)
theorem B462181 : Blo 409770 462181 := bbase (se 4 (by rfl) ⟨43329, by rfl⟩ : syracuseStep 462181 = 86659) (by norm_num)
theorem B462217 : Blo 409770 462217 := bbase (se 2 (by rfl) ⟨173331, by rfl⟩ : syracuseStep 462217 = 346663) (by norm_num)
theorem B462253 : Blo 409770 462253 := bbase (se 3 (by rfl) ⟨86672, by rfl⟩ : syracuseStep 462253 = 173345) (by norm_num)
theorem B691645 : Blo 409770 691645 := bbase (se 3 (by rfl) ⟨129683, by rfl⟩ : syracuseStep 691645 = 259367) (by norm_num)
theorem B986573 : Blo 409770 986573 := bbase (se 3 (by rfl) ⟨184982, by rfl⟩ : syracuseStep 986573 = 369965) (by norm_num)
theorem B462289 : Blo 409770 462289 := bbase (se 2 (by rfl) ⟨173358, by rfl⟩ : syracuseStep 462289 = 346717) (by norm_num)
theorem B462325 : Blo 409770 462325 := bbase (se 5 (by rfl) ⟨21671, by rfl⟩ : syracuseStep 462325 = 43343) (by norm_num)
theorem B691733 : Blo 409770 691733 := bbase (se 6 (by rfl) ⟨16212, by rfl⟩ : syracuseStep 691733 = 32425) (by norm_num)
theorem B462361 : Blo 409770 462361 := bbase (se 2 (by rfl) ⟨173385, by rfl⟩ : syracuseStep 462361 = 346771) (by norm_num)
theorem B462397 : Blo 409770 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B462433 : Blo 409770 462433 := bbase (se 2 (by rfl) ⟨173412, by rfl⟩ : syracuseStep 462433 = 346825) (by norm_num)
theorem B1052261 : Blo 409770 1052261 := bbase (se 4 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 1052261 = 197299) (by norm_num)
theorem B1478245 : Blo 409770 1478245 := bbase (se 4 (by rfl) ⟨138585, by rfl⟩ : syracuseStep 1478245 = 277171) (by norm_num)
theorem B462469 : Blo 409770 462469 := bbase (se 4 (by rfl) ⟨43356, by rfl⟩ : syracuseStep 462469 = 86713) (by norm_num)
theorem B691861 : Blo 409770 691861 := bbase (se 6 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 691861 = 32431) (by norm_num)
theorem B462505 : Blo 409770 462505 := bbase (se 2 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 462505 = 346879) (by norm_num)
theorem B462541 : Blo 409770 462541 := bbase (se 3 (by rfl) ⟨86726, by rfl⟩ : syracuseStep 462541 = 173453) (by norm_num)
theorem B691949 : Blo 409770 691949 := bbase (se 3 (by rfl) ⟨129740, by rfl⟩ : syracuseStep 691949 = 259481) (by norm_num)
theorem B986861 : Blo 409770 986861 := bbase (se 3 (by rfl) ⟨185036, by rfl⟩ : syracuseStep 986861 = 370073) (by norm_num)
theorem B462577 : Blo 409770 462577 := bbase (se 2 (by rfl) ⟨173466, by rfl⟩ : syracuseStep 462577 = 346933) (by norm_num)
theorem B495353 : Blo 409770 495353 := bbase (se 2 (by rfl) ⟨185757, by rfl⟩ : syracuseStep 495353 = 371515) (by norm_num)
theorem B1478405 : Blo 409770 1478405 := bbase (se 4 (by rfl) ⟨138600, by rfl⟩ : syracuseStep 1478405 = 277201) (by norm_num)
theorem B462613 : Blo 409770 462613 := bbase (se 6 (by rfl) ⟨10842, by rfl⟩ : syracuseStep 462613 = 21685) (by norm_num)
theorem B495401 : Blo 409770 495401 := bbase (se 2 (by rfl) ⟨185775, by rfl⟩ : syracuseStep 495401 = 371551) (by norm_num)
theorem B462649 : Blo 409770 462649 := bbase (se 2 (by rfl) ⟨173493, by rfl⟩ : syracuseStep 462649 = 346987) (by norm_num)
theorem B462685 : Blo 409770 462685 := bbase (se 3 (by rfl) ⟨86753, by rfl⟩ : syracuseStep 462685 = 173507) (by norm_num)
theorem B626525 : Blo 409770 626525 := bbase (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) (by norm_num)
theorem B692077 : Blo 409770 692077 := bbase (se 3 (by rfl) ⟨129764, by rfl⟩ : syracuseStep 692077 = 259529) (by norm_num)
theorem B1118069 : Blo 409770 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B462721 : Blo 409770 462721 := bbase (se 2 (by rfl) ⟨173520, by rfl⟩ : syracuseStep 462721 = 347041) (by norm_num)
theorem B1249157 : Blo 409770 1249157 := bbase (se 4 (by rfl) ⟨117108, by rfl⟩ : syracuseStep 1249157 = 234217) (by norm_num)
theorem B495497 : Blo 409770 495497 := bbase (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) (by norm_num)
theorem B462757 : Blo 409770 462757 := bbase (se 4 (by rfl) ⟨43383, by rfl⟩ : syracuseStep 462757 = 86767) (by norm_num)
theorem B692165 : Blo 409770 692165 := bbase (se 4 (by rfl) ⟨64890, by rfl⟩ : syracuseStep 692165 = 129781) (by norm_num)
theorem B462793 : Blo 409770 462793 := bbase (se 2 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 462793 = 347095) (by norm_num)
theorem B462829 : Blo 409770 462829 := bbase (se 3 (by rfl) ⟨86780, by rfl⟩ : syracuseStep 462829 = 173561) (by norm_num)
theorem B462865 : Blo 409770 462865 := bbase (se 2 (by rfl) ⟨173574, by rfl⟩ : syracuseStep 462865 = 347149) (by norm_num)
theorem B495661 : Blo 409770 495661 := bbase (se 3 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 495661 = 185873) (by norm_num)
theorem B462901 : Blo 409770 462901 := bbase (se 5 (by rfl) ⟨21698, by rfl⟩ : syracuseStep 462901 = 43397) (by norm_num)
theorem B692293 : Blo 409770 692293 := bbase (se 4 (by rfl) ⟨64902, by rfl⟩ : syracuseStep 692293 = 129805) (by norm_num)
theorem B462937 : Blo 409770 462937 := bbase (se 2 (by rfl) ⟨173601, by rfl⟩ : syracuseStep 462937 = 347203) (by norm_num)
theorem B462973 : Blo 409770 462973 := bbase (se 3 (by rfl) ⟨86807, by rfl⟩ : syracuseStep 462973 = 173615) (by norm_num)
theorem B692381 : Blo 409770 692381 := bbase (se 3 (by rfl) ⟨129821, by rfl⟩ : syracuseStep 692381 = 259643) (by norm_num)
theorem B463009 : Blo 409770 463009 := bbase (se 2 (by rfl) ⟨173628, by rfl⟩ : syracuseStep 463009 = 347257) (by norm_num)
theorem B463045 : Blo 409770 463045 := bbase (se 4 (by rfl) ⟨43410, by rfl⟩ : syracuseStep 463045 = 86821) (by norm_num)
theorem B9539797 : Blo 409770 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B463081 : Blo 409770 463081 := bbase (se 2 (by rfl) ⟨173655, by rfl⟩ : syracuseStep 463081 = 347311) (by norm_num)
theorem B495877 : Blo 409770 495877 := bbase (se 4 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 495877 = 92977) (by norm_num)
theorem B463117 : Blo 409770 463117 := bbase (se 3 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 463117 = 173669) (by norm_num)
theorem B1970453 : Blo 409770 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B692509 : Blo 409770 692509 := bbase (se 3 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 692509 = 259691) (by norm_num)
theorem B463153 : Blo 409770 463153 := bbase (se 2 (by rfl) ⟨173682, by rfl⟩ : syracuseStep 463153 = 347365) (by norm_num)
theorem B463189 : Blo 409770 463189 := bbase (se 10 (by rfl) ⟨678, by rfl⟩ : syracuseStep 463189 = 1357) (by norm_num)
theorem B627029 : Blo 409770 627029 := bbase (se 10 (by rfl) ⟨918, by rfl⟩ : syracuseStep 627029 = 1837) (by norm_num)
theorem B3772757 : Blo 409770 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B692597 : Blo 409770 692597 := bbase (se 5 (by rfl) ⟨32465, by rfl⟩ : syracuseStep 692597 = 64931) (by norm_num)
theorem B463225 : Blo 409770 463225 := bbase (se 2 (by rfl) ⟨173709, by rfl⟩ : syracuseStep 463225 = 347419) (by norm_num)
theorem B922013 : Blo 409770 922013 := bbase (se 3 (by rfl) ⟨172877, by rfl⟩ : syracuseStep 922013 = 345755) (by norm_num)
theorem B463261 : Blo 409770 463261 := bbase (se 3 (by rfl) ⟨86861, by rfl⟩ : syracuseStep 463261 = 173723) (by norm_num)
theorem B496045 : Blo 409770 496045 := bbase (se 3 (by rfl) ⟨93008, by rfl⟩ : syracuseStep 496045 = 186017) (by norm_num)
theorem B463297 : Blo 409770 463297 := bbase (se 2 (by rfl) ⟨173736, by rfl⟩ : syracuseStep 463297 = 347473) (by norm_num)
theorem B922085 : Blo 409770 922085 := bbase (se 4 (by rfl) ⟨86445, by rfl⟩ : syracuseStep 922085 = 172891) (by norm_num)
theorem B1053157 : Blo 409770 1053157 := bbase (se 4 (by rfl) ⟨98733, by rfl⟩ : syracuseStep 1053157 = 197467) (by norm_num)
theorem B463333 : Blo 409770 463333 := bbase (se 4 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 463333 = 86875) (by norm_num)
theorem B692725 : Blo 409770 692725 := bbase (se 5 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 692725 = 64943) (by norm_num)
theorem B463369 : Blo 409770 463369 := bbase (se 2 (by rfl) ⟨173763, by rfl⟩ : syracuseStep 463369 = 347527) (by norm_num)
theorem B922157 : Blo 409770 922157 := bbase (se 3 (by rfl) ⟨172904, by rfl⟩ : syracuseStep 922157 = 345809) (by norm_num)
theorem B561709 : Blo 409770 561709 := bbase (se 3 (by rfl) ⟨105320, by rfl⟩ : syracuseStep 561709 = 210641) (by norm_num)
theorem B463405 : Blo 409770 463405 := bbase (se 3 (by rfl) ⟨86888, by rfl⟩ : syracuseStep 463405 = 173777) (by norm_num)
theorem B692813 : Blo 409770 692813 := bbase (se 3 (by rfl) ⟨129902, by rfl⟩ : syracuseStep 692813 = 259805) (by norm_num)
theorem B463441 : Blo 409770 463441 := bbase (se 2 (by rfl) ⟨173790, by rfl⟩ : syracuseStep 463441 = 347581) (by norm_num)
theorem B922229 : Blo 409770 922229 := bbase (se 5 (by rfl) ⟨43229, by rfl⟩ : syracuseStep 922229 = 86459) (by norm_num)
theorem B463477 : Blo 409770 463477 := bbase (se 5 (by rfl) ⟨21725, by rfl⟩ : syracuseStep 463477 = 43451) (by norm_num)
theorem B463513 : Blo 409770 463513 := bbase (se 2 (by rfl) ⟨173817, by rfl⟩ : syracuseStep 463513 = 347635) (by norm_num)
theorem B660125 : Blo 409770 660125 := bbase (se 3 (by rfl) ⟨123773, by rfl⟩ : syracuseStep 660125 = 247547) (by norm_num)
theorem B922301 : Blo 409770 922301 := bbase (se 3 (by rfl) ⟨172931, by rfl⟩ : syracuseStep 922301 = 345863) (by norm_num)
theorem B463549 : Blo 409770 463549 := bbase (se 3 (by rfl) ⟨86915, by rfl⟩ : syracuseStep 463549 = 173831) (by norm_num)
theorem B692941 : Blo 409770 692941 := bbase (se 3 (by rfl) ⟨129926, by rfl⟩ : syracuseStep 692941 = 259853) (by norm_num)
theorem B463585 : Blo 409770 463585 := bbase (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) (by norm_num)
theorem B922373 : Blo 409770 922373 := bbase (se 4 (by rfl) ⟨86472, by rfl⟩ : syracuseStep 922373 = 172945) (by norm_num)
theorem B463621 : Blo 409770 463621 := bbase (se 4 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 463621 = 86929) (by norm_num)
theorem B693029 : Blo 409770 693029 := bbase (se 4 (by rfl) ⟨64971, by rfl⟩ : syracuseStep 693029 = 129943) (by norm_num)
theorem B463657 : Blo 409770 463657 := bbase (se 2 (by rfl) ⟨173871, by rfl⟩ : syracuseStep 463657 = 347743) (by norm_num)
theorem B922445 : Blo 409770 922445 := bbase (se 3 (by rfl) ⟨172958, by rfl⟩ : syracuseStep 922445 = 345917) (by norm_num)
theorem B463693 : Blo 409770 463693 := bbase (se 3 (by rfl) ⟨86942, by rfl⟩ : syracuseStep 463693 = 173885) (by norm_num)
theorem B2954069 : Blo 409770 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B463729 : Blo 409770 463729 := bbase (se 2 (by rfl) ⟨173898, by rfl⟩ : syracuseStep 463729 = 347797) (by norm_num)
theorem B660349 : Blo 409770 660349 := bbase (se 3 (by rfl) ⟨123815, by rfl⟩ : syracuseStep 660349 = 247631) (by norm_num)
theorem B922517 : Blo 409770 922517 := bbase (se 6 (by rfl) ⟨21621, by rfl⟩ : syracuseStep 922517 = 43243) (by norm_num)
theorem B463765 : Blo 409770 463765 := bbase (se 6 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 463765 = 21739) (by norm_num)
theorem B693157 : Blo 409770 693157 := bbase (se 4 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 693157 = 129967) (by norm_num)
theorem B463801 : Blo 409770 463801 := bbase (se 2 (by rfl) ⟨173925, by rfl⟩ : syracuseStep 463801 = 347851) (by norm_num)
theorem B496573 : Blo 409770 496573 := bbase (se 3 (by rfl) ⟨93107, by rfl⟩ : syracuseStep 496573 = 186215) (by norm_num)
theorem B922589 : Blo 409770 922589 := bbase (se 3 (by rfl) ⟨172985, by rfl⟩ : syracuseStep 922589 = 345971) (by norm_num)
theorem B463837 : Blo 409770 463837 := bbase (se 3 (by rfl) ⟨86969, by rfl⟩ : syracuseStep 463837 = 173939) (by norm_num)
theorem B693245 : Blo 409770 693245 := bbase (se 3 (by rfl) ⟨129983, by rfl⟩ : syracuseStep 693245 = 259967) (by norm_num)
theorem B463873 : Blo 409770 463873 := bbase (se 2 (by rfl) ⟨173952, by rfl⟩ : syracuseStep 463873 = 347905) (by norm_num)
theorem B922661 : Blo 409770 922661 := bbase (se 4 (by rfl) ⟨86499, by rfl⟩ : syracuseStep 922661 = 172999) (by norm_num)
theorem B463909 : Blo 409770 463909 := bbase (se 4 (by rfl) ⟨43491, by rfl⟩ : syracuseStep 463909 = 86983) (by norm_num)
theorem B1414181 : Blo 409770 1414181 := bbase (se 4 (by rfl) ⟨132579, by rfl⟩ : syracuseStep 1414181 = 265159) (by norm_num)
theorem B463945 : Blo 409770 463945 := bbase (se 2 (by rfl) ⟨173979, by rfl⟩ : syracuseStep 463945 = 347959) (by norm_num)
theorem B922733 : Blo 409770 922733 := bbase (se 3 (by rfl) ⟨173012, by rfl⟩ : syracuseStep 922733 = 346025) (by norm_num)
theorem B463981 : Blo 409770 463981 := bbase (se 3 (by rfl) ⟨86996, by rfl⟩ : syracuseStep 463981 = 173993) (by norm_num)
theorem B693373 : Blo 409770 693373 := bbase (se 3 (by rfl) ⟨130007, by rfl⟩ : syracuseStep 693373 = 260015) (by norm_num)
theorem B464017 : Blo 409770 464017 := bbase (se 2 (by rfl) ⟨174006, by rfl⟩ : syracuseStep 464017 = 348013) (by norm_num)
theorem B922805 : Blo 409770 922805 := bbase (se 5 (by rfl) ⟨43256, by rfl⟩ : syracuseStep 922805 = 86513) (by norm_num)
theorem B464053 : Blo 409770 464053 := bbase (se 5 (by rfl) ⟨21752, by rfl⟩ : syracuseStep 464053 = 43505) (by norm_num)
theorem B627917 : Blo 409770 627917 := bbase (se 3 (by rfl) ⟨117734, by rfl⟩ : syracuseStep 627917 = 235469) (by norm_num)
theorem B693461 : Blo 409770 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B464089 : Blo 409770 464089 := bbase (se 2 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 464089 = 348067) (by norm_num)
theorem B627941 : Blo 409770 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B922877 : Blo 409770 922877 := bbase (se 3 (by rfl) ⟨173039, by rfl⟩ : syracuseStep 922877 = 346079) (by norm_num)
theorem B464125 : Blo 409770 464125 := bbase (se 3 (by rfl) ⟨87023, by rfl⟩ : syracuseStep 464125 = 174047) (by norm_num)
theorem B464161 : Blo 409770 464161 := bbase (se 2 (by rfl) ⟨174060, by rfl⟩ : syracuseStep 464161 = 348121) (by norm_num)
theorem B922949 : Blo 409770 922949 := bbase (se 4 (by rfl) ⟨86526, by rfl⟩ : syracuseStep 922949 = 173053) (by norm_num)
theorem B464197 : Blo 409770 464197 := bbase (se 4 (by rfl) ⟨43518, by rfl⟩ : syracuseStep 464197 = 87037) (by norm_num)
theorem B693589 : Blo 409770 693589 := bbase (se 14 (by rfl) ⟨63, by rfl⟩ : syracuseStep 693589 = 127) (by norm_num)
theorem B464233 : Blo 409770 464233 := bbase (se 2 (by rfl) ⟨174087, by rfl⟩ : syracuseStep 464233 = 348175) (by norm_num)
theorem B923021 : Blo 409770 923021 := bbase (se 3 (by rfl) ⟨173066, by rfl⟩ : syracuseStep 923021 = 346133) (by norm_num)
theorem B464269 : Blo 409770 464269 := bbase (se 3 (by rfl) ⟨87050, by rfl⟩ : syracuseStep 464269 = 174101) (by norm_num)
theorem B693677 : Blo 409770 693677 := bbase (se 3 (by rfl) ⟨130064, by rfl⟩ : syracuseStep 693677 = 260129) (by norm_num)
theorem B464305 : Blo 409770 464305 := bbase (se 2 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 464305 = 348229) (by norm_num)
theorem B923093 : Blo 409770 923093 := bbase (se 7 (by rfl) ⟨10817, by rfl⟩ : syracuseStep 923093 = 21635) (by norm_num)
theorem B2004437 : Blo 409770 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B464341 : Blo 409770 464341 := bbase (se 7 (by rfl) ⟨5441, by rfl⟩ : syracuseStep 464341 = 10883) (by norm_num)
theorem B464377 : Blo 409770 464377 := bbase (se 2 (by rfl) ⟨174141, by rfl⟩ : syracuseStep 464377 = 348283) (by norm_num)
theorem B923165 : Blo 409770 923165 := bbase (se 3 (by rfl) ⟨173093, by rfl⟩ : syracuseStep 923165 = 346187) (by norm_num)
theorem B464413 : Blo 409770 464413 := bbase (se 3 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 464413 = 174155) (by norm_num)
theorem B529949 : Blo 409770 529949 := bbase (se 3 (by rfl) ⟨99365, by rfl⟩ : syracuseStep 529949 = 198731) (by norm_num)
theorem B693805 : Blo 409770 693805 := bbase (se 3 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 693805 = 260177) (by norm_num)
theorem B464449 : Blo 409770 464449 := bbase (se 2 (by rfl) ⟨174168, by rfl⟩ : syracuseStep 464449 = 348337) (by norm_num)
theorem B923237 : Blo 409770 923237 := bbase (se 4 (by rfl) ⟨86553, by rfl⟩ : syracuseStep 923237 = 173107) (by norm_num)
theorem B464485 : Blo 409770 464485 := bbase (se 4 (by rfl) ⟨43545, by rfl⟩ : syracuseStep 464485 = 87091) (by norm_num)
theorem B693893 : Blo 409770 693893 := bbase (se 4 (by rfl) ⟨65052, by rfl⟩ : syracuseStep 693893 = 130105) (by norm_num)
theorem B464521 : Blo 409770 464521 := bbase (se 2 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 464521 = 348391) (by norm_num)
theorem B1971877 : Blo 409770 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B923309 : Blo 409770 923309 := bbase (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) (by norm_num)
theorem B464557 : Blo 409770 464557 := bbase (se 3 (by rfl) ⟨87104, by rfl⟩ : syracuseStep 464557 = 174209) (by norm_num)
theorem B1316533 : Blo 409770 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B988861 : Blo 409770 988861 := bbase (se 3 (by rfl) ⟨185411, by rfl⟩ : syracuseStep 988861 = 370823) (by norm_num)
theorem B530113 : Blo 409770 530113 := bbase (se 2 (by rfl) ⟨198792, by rfl⟩ : syracuseStep 530113 = 397585) (by norm_num)
theorem B464593 : Blo 409770 464593 := bbase (se 2 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 464593 = 348445) (by norm_num)
theorem B923381 : Blo 409770 923381 := bbase (se 5 (by rfl) ⟨43283, by rfl⟩ : syracuseStep 923381 = 86567) (by norm_num)
theorem B464629 : Blo 409770 464629 := bbase (se 5 (by rfl) ⟨21779, by rfl⟩ : syracuseStep 464629 = 43559) (by norm_num)
theorem B694021 : Blo 409770 694021 := bbase (se 4 (by rfl) ⟨65064, by rfl⟩ : syracuseStep 694021 = 130129) (by norm_num)
theorem B464665 : Blo 409770 464665 := bbase (se 2 (by rfl) ⟨174249, by rfl⟩ : syracuseStep 464665 = 348499) (by norm_num)
theorem B890677 : Blo 409770 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B923453 : Blo 409770 923453 := bbase (se 3 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 923453 = 346295) (by norm_num)
theorem B464701 : Blo 409770 464701 := bbase (se 3 (by rfl) ⟨87131, by rfl⟩ : syracuseStep 464701 = 174263) (by norm_num)
theorem B628549 : Blo 409770 628549 := bbase (se 4 (by rfl) ⟨58926, by rfl⟩ : syracuseStep 628549 = 117853) (by norm_num)
theorem B694109 : Blo 409770 694109 := bbase (se 3 (by rfl) ⟨130145, by rfl⟩ : syracuseStep 694109 = 260291) (by norm_num)
theorem B464737 : Blo 409770 464737 := bbase (se 2 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 464737 = 348553) (by norm_num)
theorem B923525 : Blo 409770 923525 := bbase (se 4 (by rfl) ⟨86580, by rfl⟩ : syracuseStep 923525 = 173161) (by norm_num)
theorem B464773 : Blo 409770 464773 := bbase (se 4 (by rfl) ⟨43572, by rfl⟩ : syracuseStep 464773 = 87145) (by norm_num)
theorem B2627477 : Blo 409770 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B464809 : Blo 409770 464809 := bbase (se 2 (by rfl) ⟨174303, by rfl⟩ : syracuseStep 464809 = 348607) (by norm_num)
theorem B923597 : Blo 409770 923597 := bbase (se 3 (by rfl) ⟨173174, by rfl⟩ : syracuseStep 923597 = 346349) (by norm_num)
theorem B464845 : Blo 409770 464845 := bbase (se 3 (by rfl) ⟨87158, by rfl⟩ : syracuseStep 464845 = 174317) (by norm_num)
theorem B694237 : Blo 409770 694237 := bbase (se 3 (by rfl) ⟨130169, by rfl⟩ : syracuseStep 694237 = 260339) (by norm_num)
theorem B464881 : Blo 409770 464881 := bbase (se 2 (by rfl) ⟨174330, by rfl⟩ : syracuseStep 464881 = 348661) (by norm_num)
theorem B923669 : Blo 409770 923669 := bbase (se 6 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 923669 = 43297) (by norm_num)
theorem B464917 : Blo 409770 464917 := bbase (se 6 (by rfl) ⟨10896, by rfl⟩ : syracuseStep 464917 = 21793) (by norm_num)
theorem B694325 : Blo 409770 694325 := bbase (se 5 (by rfl) ⟨32546, by rfl⟩ : syracuseStep 694325 = 65093) (by norm_num)
theorem B464953 : Blo 409770 464953 := bbase (se 2 (by rfl) ⟨174357, by rfl⟩ : syracuseStep 464953 = 348715) (by norm_num)
theorem B923741 : Blo 409770 923741 := bbase (se 3 (by rfl) ⟨173201, by rfl⟩ : syracuseStep 923741 = 346403) (by norm_num)
theorem B464989 : Blo 409770 464989 := bbase (se 3 (by rfl) ⟨87185, by rfl⟩ : syracuseStep 464989 = 174371) (by norm_num)
theorem B530533 : Blo 409770 530533 := bbase (se 4 (by rfl) ⟨49737, by rfl⟩ : syracuseStep 530533 = 99475) (by norm_num)
theorem B1054829 : Blo 409770 1054829 := bbase (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) (by norm_num)
theorem B465025 : Blo 409770 465025 := bbase (se 2 (by rfl) ⟨174384, by rfl⟩ : syracuseStep 465025 = 348769) (by norm_num)
theorem B923813 : Blo 409770 923813 := bbase (se 4 (by rfl) ⟨86607, by rfl⟩ : syracuseStep 923813 = 173215) (by norm_num)
theorem B465061 : Blo 409770 465061 := bbase (se 4 (by rfl) ⟨43599, by rfl⟩ : syracuseStep 465061 = 87199) (by norm_num)
theorem B694453 : Blo 409770 694453 := bbase (se 5 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 694453 = 65105) (by norm_num)
theorem B465097 : Blo 409770 465097 := bbase (se 2 (by rfl) ⟨174411, by rfl⟩ : syracuseStep 465097 = 348823) (by norm_num)
theorem B923885 : Blo 409770 923885 := bbase (se 3 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 923885 = 346457) (by norm_num)
theorem B465133 : Blo 409770 465133 := bbase (se 3 (by rfl) ⟨87212, by rfl⟩ : syracuseStep 465133 = 174425) (by norm_num)
theorem B661765 : Blo 409770 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B694541 : Blo 409770 694541 := bbase (se 3 (by rfl) ⟨130226, by rfl⟩ : syracuseStep 694541 = 260453) (by norm_num)
theorem B792845 : Blo 409770 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B465169 : Blo 409770 465169 := bbase (se 2 (by rfl) ⟨174438, by rfl⟩ : syracuseStep 465169 = 348877) (by norm_num)
theorem B923957 : Blo 409770 923957 := bbase (se 5 (by rfl) ⟨43310, by rfl⟩ : syracuseStep 923957 = 86621) (by norm_num)
theorem B465205 : Blo 409770 465205 := bbase (se 5 (by rfl) ⟨21806, by rfl⟩ : syracuseStep 465205 = 43613) (by norm_num)
theorem B465241 : Blo 409770 465241 := bbase (se 2 (by rfl) ⟨174465, by rfl⟩ : syracuseStep 465241 = 348931) (by norm_num)
theorem B924029 : Blo 409770 924029 := bbase (se 3 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 924029 = 346511) (by norm_num)
theorem B465277 : Blo 409770 465277 := bbase (se 3 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 465277 = 174479) (by norm_num)
theorem B694669 : Blo 409770 694669 := bbase (se 3 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 694669 = 260501) (by norm_num)
theorem B465313 : Blo 409770 465313 := bbase (se 2 (by rfl) ⟨174492, by rfl⟩ : syracuseStep 465313 = 348985) (by norm_num)
theorem B924101 : Blo 409770 924101 := bbase (se 4 (by rfl) ⟨86634, by rfl⟩ : syracuseStep 924101 = 173269) (by norm_num)
theorem B465349 : Blo 409770 465349 := bbase (se 4 (by rfl) ⟨43626, by rfl⟩ : syracuseStep 465349 = 87253) (by norm_num)
theorem B694757 : Blo 409770 694757 := bbase (se 4 (by rfl) ⟨65133, by rfl⟩ : syracuseStep 694757 = 130267) (by norm_num)
theorem B465385 : Blo 409770 465385 := bbase (se 2 (by rfl) ⟨174519, by rfl⟩ : syracuseStep 465385 = 349039) (by norm_num)
theorem B662021 : Blo 409770 662021 := bbase (se 4 (by rfl) ⟨62064, by rfl⟩ : syracuseStep 662021 = 124129) (by norm_num)
theorem B924173 : Blo 409770 924173 := bbase (se 3 (by rfl) ⟨173282, by rfl⟩ : syracuseStep 924173 = 346565) (by norm_num)
theorem B465421 : Blo 409770 465421 := bbase (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) (by norm_num)
theorem B465457 : Blo 409770 465457 := bbase (se 2 (by rfl) ⟨174546, by rfl⟩ : syracuseStep 465457 = 349093) (by norm_num)
theorem B924245 : Blo 409770 924245 := bbase (se 8 (by rfl) ⟨5415, by rfl⟩ : syracuseStep 924245 = 10831) (by norm_num)
theorem B694885 : Blo 409770 694885 := bbase (se 4 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 694885 = 130291) (by norm_num)
theorem B924317 : Blo 409770 924317 := bbase (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) (by norm_num)
theorem B694973 : Blo 409770 694973 := bbase (se 3 (by rfl) ⟨130307, by rfl⟩ : syracuseStep 694973 = 260615) (by norm_num)
theorem B662213 : Blo 409770 662213 := bbase (se 4 (by rfl) ⟨62082, by rfl⟩ : syracuseStep 662213 = 124165) (by norm_num)
theorem B3939029 : Blo 409770 3939029 := bbase (se 7 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 3939029 = 92321) (by norm_num)
theorem B924389 : Blo 409770 924389 := bbase (se 4 (by rfl) ⟨86661, by rfl⟩ : syracuseStep 924389 = 173323) (by norm_num)
theorem B924461 : Blo 409770 924461 := bbase (se 3 (by rfl) ⟨173336, by rfl⟩ : syracuseStep 924461 = 346673) (by norm_num)
theorem B695101 : Blo 409770 695101 := bbase (se 3 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 695101 = 260663) (by norm_num)
theorem B924533 : Blo 409770 924533 := bbase (se 5 (by rfl) ⟨43337, by rfl⟩ : syracuseStep 924533 = 86675) (by norm_num)
theorem B1383317 : Blo 409770 1383317 := bbase (se 6 (by rfl) ⟨32421, by rfl⟩ : syracuseStep 1383317 = 64843) (by norm_num)
theorem B695189 : Blo 409770 695189 := bbase (se 6 (by rfl) ⟨16293, by rfl⟩ : syracuseStep 695189 = 32587) (by norm_num)
theorem B924605 : Blo 409770 924605 := bbase (se 3 (by rfl) ⟨173363, by rfl⟩ : syracuseStep 924605 = 346727) (by norm_num)
theorem B1874917 : Blo 409770 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B924677 : Blo 409770 924677 := bbase (se 4 (by rfl) ⟨86688, by rfl⟩ : syracuseStep 924677 = 173377) (by norm_num)
theorem B695317 : Blo 409770 695317 := bbase (se 6 (by rfl) ⟨16296, by rfl⟩ : syracuseStep 695317 = 32593) (by norm_num)
theorem B990245 : Blo 409770 990245 := bbase (se 4 (by rfl) ⟨92835, by rfl⟩ : syracuseStep 990245 = 185671) (by norm_num)
theorem B924749 : Blo 409770 924749 := bbase (se 3 (by rfl) ⟨173390, by rfl⟩ : syracuseStep 924749 = 346781) (by norm_num)
theorem B695405 : Blo 409770 695405 := bbase (se 3 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 695405 = 260777) (by norm_num)
theorem B924821 : Blo 409770 924821 := bbase (se 6 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 924821 = 43351) (by norm_num)
theorem B924893 : Blo 409770 924893 := bbase (se 3 (by rfl) ⟨173417, by rfl⟩ : syracuseStep 924893 = 346835) (by norm_num)
theorem B695533 : Blo 409770 695533 := bbase (se 3 (by rfl) ⟨130412, by rfl⟩ : syracuseStep 695533 = 260825) (by norm_num)
theorem B924965 : Blo 409770 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B1383749 : Blo 409770 1383749 := bbase (se 4 (by rfl) ⟨129726, by rfl⟩ : syracuseStep 1383749 = 259453) (by norm_num)
theorem B695621 : Blo 409770 695621 := bbase (se 4 (by rfl) ⟨65214, by rfl⟩ : syracuseStep 695621 = 130429) (by norm_num)
theorem B925037 : Blo 409770 925037 := bbase (se 3 (by rfl) ⟨173444, by rfl⟩ : syracuseStep 925037 = 346889) (by norm_num)
theorem B925109 : Blo 409770 925109 := bbase (se 5 (by rfl) ⟨43364, by rfl⟩ : syracuseStep 925109 = 86729) (by norm_num)
theorem B695749 : Blo 409770 695749 := bbase (se 4 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 695749 = 130453) (by norm_num)
theorem B990677 : Blo 409770 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B925181 : Blo 409770 925181 := bbase (se 3 (by rfl) ⟨173471, by rfl⟩ : syracuseStep 925181 = 346943) (by norm_num)
theorem B695837 : Blo 409770 695837 := bbase (se 3 (by rfl) ⟨130469, by rfl⟩ : syracuseStep 695837 = 260939) (by norm_num)
theorem B925253 : Blo 409770 925253 := bbase (se 4 (by rfl) ⟨86742, by rfl⟩ : syracuseStep 925253 = 173485) (by norm_num)
theorem B925325 : Blo 409770 925325 := bbase (se 3 (by rfl) ⟨173498, by rfl⟩ : syracuseStep 925325 = 346997) (by norm_num)
theorem B695965 : Blo 409770 695965 := bbase (se 3 (by rfl) ⟨130493, by rfl⟩ : syracuseStep 695965 = 260987) (by norm_num)
theorem B925397 : Blo 409770 925397 := bbase (se 7 (by rfl) ⟨10844, by rfl⟩ : syracuseStep 925397 = 21689) (by norm_num)
theorem B1384181 : Blo 409770 1384181 := bbase (se 5 (by rfl) ⟨64883, by rfl⟩ : syracuseStep 1384181 = 129767) (by norm_num)
theorem B696053 : Blo 409770 696053 := bbase (se 5 (by rfl) ⟨32627, by rfl⟩ : syracuseStep 696053 = 65255) (by norm_num)
theorem B925469 : Blo 409770 925469 := bbase (se 3 (by rfl) ⟨173525, by rfl⟩ : syracuseStep 925469 = 347051) (by norm_num)
theorem B925541 : Blo 409770 925541 := bbase (se 4 (by rfl) ⟨86769, by rfl⟩ : syracuseStep 925541 = 173539) (by norm_num)
theorem B696181 : Blo 409770 696181 := bbase (se 5 (by rfl) ⟨32633, by rfl⟩ : syracuseStep 696181 = 65267) (by norm_num)
theorem B925613 : Blo 409770 925613 := bbase (se 3 (by rfl) ⟨173552, by rfl⟩ : syracuseStep 925613 = 347105) (by norm_num)
theorem B696269 : Blo 409770 696269 := bbase (se 3 (by rfl) ⟨130550, by rfl⟩ : syracuseStep 696269 = 261101) (by norm_num)
theorem B2957269 : Blo 409770 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B925685 : Blo 409770 925685 := bbase (se 5 (by rfl) ⟨43391, by rfl⟩ : syracuseStep 925685 = 86783) (by norm_num)
theorem B925757 : Blo 409770 925757 := bbase (se 3 (by rfl) ⟨173579, by rfl⟩ : syracuseStep 925757 = 347159) (by norm_num)
theorem B696397 : Blo 409770 696397 := bbase (se 3 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 696397 = 261149) (by norm_num)
theorem B925829 : Blo 409770 925829 := bbase (se 4 (by rfl) ⟨86796, by rfl⟩ : syracuseStep 925829 = 173593) (by norm_num)
theorem B1384613 : Blo 409770 1384613 := bbase (se 4 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 1384613 = 259615) (by norm_num)
theorem B696485 : Blo 409770 696485 := bbase (se 4 (by rfl) ⟨65295, by rfl⟩ : syracuseStep 696485 = 130591) (by norm_num)
theorem B925901 : Blo 409770 925901 := bbase (se 3 (by rfl) ⟨173606, by rfl⟩ : syracuseStep 925901 = 347213) (by norm_num)
theorem B925973 : Blo 409770 925973 := bbase (se 6 (by rfl) ⟨21702, by rfl⟩ : syracuseStep 925973 = 43405) (by norm_num)
theorem B1057045 : Blo 409770 1057045 := bbase (se 6 (by rfl) ⟨24774, by rfl⟩ : syracuseStep 1057045 = 49549) (by norm_num)
theorem B696613 : Blo 409770 696613 := bbase (se 4 (by rfl) ⟨65307, by rfl⟩ : syracuseStep 696613 = 130615) (by norm_num)
theorem B926045 : Blo 409770 926045 := bbase (se 3 (by rfl) ⟨173633, by rfl⟩ : syracuseStep 926045 = 347267) (by norm_num)
theorem B696701 : Blo 409770 696701 := bbase (se 3 (by rfl) ⟨130631, by rfl⟩ : syracuseStep 696701 = 261263) (by norm_num)
theorem B926117 : Blo 409770 926117 := bbase (se 4 (by rfl) ⟨86823, by rfl⟩ : syracuseStep 926117 = 173647) (by norm_num)
theorem B926189 : Blo 409770 926189 := bbase (se 3 (by rfl) ⟨173660, by rfl⟩ : syracuseStep 926189 = 347321) (by norm_num)
theorem B696829 : Blo 409770 696829 := bbase (se 3 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 696829 = 261311) (by norm_num)
theorem B1319429 : Blo 409770 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B926261 : Blo 409770 926261 := bbase (se 5 (by rfl) ⟨43418, by rfl⟩ : syracuseStep 926261 = 86837) (by norm_num)
theorem B1385045 : Blo 409770 1385045 := bbase (se 8 (by rfl) ⟨8115, by rfl⟩ : syracuseStep 1385045 = 16231) (by norm_num)
theorem B696917 : Blo 409770 696917 := bbase (se 8 (by rfl) ⟨4083, by rfl⟩ : syracuseStep 696917 = 8167) (by norm_num)
theorem B926333 : Blo 409770 926333 := bbase (se 3 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 926333 = 347375) (by norm_num)
theorem B926405 : Blo 409770 926405 := bbase (se 4 (by rfl) ⟨86850, by rfl⟩ : syracuseStep 926405 = 173701) (by norm_num)
theorem B697045 : Blo 409770 697045 := bbase (se 7 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 697045 = 16337) (by norm_num)
theorem B926477 : Blo 409770 926477 := bbase (se 3 (by rfl) ⟨173714, by rfl⟩ : syracuseStep 926477 = 347429) (by norm_num)
theorem B697133 : Blo 409770 697133 := bbase (se 3 (by rfl) ⟨130712, by rfl⟩ : syracuseStep 697133 = 261425) (by norm_num)
theorem B926549 : Blo 409770 926549 := bbase (se 9 (by rfl) ⟨2714, by rfl⟩ : syracuseStep 926549 = 5429) (by norm_num)
theorem B926621 : Blo 409770 926621 := bbase (se 3 (by rfl) ⟨173741, by rfl⟩ : syracuseStep 926621 = 347483) (by norm_num)
theorem B697261 : Blo 409770 697261 := bbase (se 3 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 697261 = 261473) (by norm_num)
theorem B1254325 : Blo 409770 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B926693 : Blo 409770 926693 := bbase (se 4 (by rfl) ⟨86877, by rfl⟩ : syracuseStep 926693 = 173755) (by norm_num)
theorem B1385477 : Blo 409770 1385477 := bbase (se 4 (by rfl) ⟨129888, by rfl⟩ : syracuseStep 1385477 = 259777) (by norm_num)
theorem B697349 : Blo 409770 697349 := bbase (se 4 (by rfl) ⟨65376, by rfl⟩ : syracuseStep 697349 = 130753) (by norm_num)
theorem B1057805 : Blo 409770 1057805 := bbase (se 3 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 1057805 = 396677) (by norm_num)
theorem B5284885 : Blo 409770 5284885 := bbase (se 6 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 5284885 = 247729) (by norm_num)
theorem B926765 : Blo 409770 926765 := bbase (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) (by norm_num)
theorem B894005 : Blo 409770 894005 := bbase (se 5 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 894005 = 83813) (by norm_num)
theorem B926837 : Blo 409770 926837 := bbase (se 5 (by rfl) ⟨43445, by rfl⟩ : syracuseStep 926837 = 86891) (by norm_num)
theorem B697477 : Blo 409770 697477 := bbase (se 4 (by rfl) ⟨65388, by rfl⟩ : syracuseStep 697477 = 130777) (by norm_num)
theorem B2368693 : Blo 409770 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B926909 : Blo 409770 926909 := bbase (se 3 (by rfl) ⟨173795, by rfl⟩ : syracuseStep 926909 = 347591) (by norm_num)
theorem B697565 : Blo 409770 697565 := bbase (se 3 (by rfl) ⟨130793, by rfl⟩ : syracuseStep 697565 = 261587) (by norm_num)
theorem B926981 : Blo 409770 926981 := bbase (se 4 (by rfl) ⟨86904, by rfl⟩ : syracuseStep 926981 = 173809) (by norm_num)
theorem B927053 : Blo 409770 927053 := bbase (se 3 (by rfl) ⟨173822, by rfl⟩ : syracuseStep 927053 = 347645) (by norm_num)
theorem B697693 : Blo 409770 697693 := bbase (se 3 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 697693 = 261635) (by norm_num)
theorem B3122549 : Blo 409770 3122549 := bbase (se 5 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 3122549 = 292739) (by norm_num)
theorem B927125 : Blo 409770 927125 := bbase (se 6 (by rfl) ⟨21729, by rfl⟩ : syracuseStep 927125 = 43459) (by norm_num)
theorem B1385909 : Blo 409770 1385909 := bbase (se 5 (by rfl) ⟨64964, by rfl⟩ : syracuseStep 1385909 = 129929) (by norm_num)
theorem B1582517 : Blo 409770 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B697781 : Blo 409770 697781 := bbase (se 5 (by rfl) ⟨32708, by rfl⟩ : syracuseStep 697781 = 65417) (by norm_num)
theorem B927197 : Blo 409770 927197 := bbase (se 3 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 927197 = 347699) (by norm_num)
theorem B894461 : Blo 409770 894461 := bbase (se 3 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 894461 = 335423) (by norm_num)
theorem B927269 : Blo 409770 927269 := bbase (se 4 (by rfl) ⟨86931, by rfl⟩ : syracuseStep 927269 = 173863) (by norm_num)
theorem B2336309 : Blo 409770 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B697909 : Blo 409770 697909 := bbase (se 5 (by rfl) ⟨32714, by rfl⟩ : syracuseStep 697909 = 65429) (by norm_num)
theorem B927341 : Blo 409770 927341 := bbase (se 3 (by rfl) ⟨173876, by rfl⟩ : syracuseStep 927341 = 347753) (by norm_num)
theorem B501373 : Blo 409770 501373 := bbase (se 3 (by rfl) ⟨94007, by rfl⟩ : syracuseStep 501373 = 188015) (by norm_num)
theorem B697997 : Blo 409770 697997 := bbase (se 3 (by rfl) ⟨130874, by rfl⟩ : syracuseStep 697997 = 261749) (by norm_num)
theorem B927413 : Blo 409770 927413 := bbase (se 5 (by rfl) ⟨43472, by rfl⟩ : syracuseStep 927413 = 86945) (by norm_num)
theorem B3516149 : Blo 409770 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B927485 : Blo 409770 927485 := bbase (se 3 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 927485 = 347807) (by norm_num)
theorem B698125 : Blo 409770 698125 := bbase (se 3 (by rfl) ⟨130898, by rfl⟩ : syracuseStep 698125 = 261797) (by norm_num)
theorem B468785 : Blo 409770 468785 := bbase (se 2 (by rfl) ⟨175794, by rfl⟩ : syracuseStep 468785 = 351589) (by norm_num)
theorem B927557 : Blo 409770 927557 := bbase (se 4 (by rfl) ⟨86958, by rfl⟩ : syracuseStep 927557 = 173917) (by norm_num)
theorem B1386341 : Blo 409770 1386341 := bbase (se 4 (by rfl) ⟨129969, by rfl⟩ : syracuseStep 1386341 = 259939) (by norm_num)
theorem B698213 : Blo 409770 698213 := bbase (se 4 (by rfl) ⟨65457, by rfl⟩ : syracuseStep 698213 = 130915) (by norm_num)
theorem B927629 : Blo 409770 927629 := bbase (se 3 (by rfl) ⟨173930, by rfl⟩ : syracuseStep 927629 = 347861) (by norm_num)
theorem B927701 : Blo 409770 927701 := bbase (se 7 (by rfl) ⟨10871, by rfl⟩ : syracuseStep 927701 = 21743) (by norm_num)
theorem B927773 : Blo 409770 927773 := bbase (se 3 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 927773 = 347915) (by norm_num)
theorem B1255493 : Blo 409770 1255493 := bbase (se 4 (by rfl) ⟨117702, by rfl⟩ : syracuseStep 1255493 = 235405) (by norm_num)
theorem B927845 : Blo 409770 927845 := bbase (se 4 (by rfl) ⟨86985, by rfl⟩ : syracuseStep 927845 = 173971) (by norm_num)
theorem B927917 : Blo 409770 927917 := bbase (se 3 (by rfl) ⟨173984, by rfl⟩ : syracuseStep 927917 = 347969) (by norm_num)
theorem B469237 : Blo 409770 469237 := bbase (se 5 (by rfl) ⟨21995, by rfl⟩ : syracuseStep 469237 = 43991) (by norm_num)
theorem B927989 : Blo 409770 927989 := bbase (se 5 (by rfl) ⟨43499, by rfl⟩ : syracuseStep 927989 = 86999) (by norm_num)
theorem B1386773 : Blo 409770 1386773 := bbase (se 6 (by rfl) ⟨32502, by rfl⟩ : syracuseStep 1386773 = 65005) (by norm_num)
theorem B928061 : Blo 409770 928061 := bbase (se 3 (by rfl) ⟨174011, by rfl⟩ : syracuseStep 928061 = 348023) (by norm_num)
theorem B928133 : Blo 409770 928133 := bbase (se 4 (by rfl) ⟨87012, by rfl⟩ : syracuseStep 928133 = 174025) (by norm_num)
theorem B1485221 : Blo 409770 1485221 := bbase (se 4 (by rfl) ⟨139239, by rfl⟩ : syracuseStep 1485221 = 278479) (by norm_num)
theorem B928205 : Blo 409770 928205 := bbase (se 3 (by rfl) ⟨174038, by rfl⟩ : syracuseStep 928205 = 348077) (by norm_num)
theorem B928277 : Blo 409770 928277 := bbase (se 6 (by rfl) ⟨21756, by rfl⟩ : syracuseStep 928277 = 43513) (by norm_num)
theorem B502357 : Blo 409770 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B928349 : Blo 409770 928349 := bbase (se 3 (by rfl) ⟨174065, by rfl⟩ : syracuseStep 928349 = 348131) (by norm_num)
theorem B764525 : Blo 409770 764525 := bbase (se 3 (by rfl) ⟨143348, by rfl⟩ : syracuseStep 764525 = 286697) (by norm_num)
theorem B1059485 : Blo 409770 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B928421 : Blo 409770 928421 := bbase (se 4 (by rfl) ⟨87039, by rfl⟩ : syracuseStep 928421 = 174079) (by norm_num)
theorem B666301 : Blo 409770 666301 := bbase (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) (by norm_num)
theorem B1387205 : Blo 409770 1387205 := bbase (se 4 (by rfl) ⟨130050, by rfl⟩ : syracuseStep 1387205 = 260101) (by norm_num)
theorem B928493 : Blo 409770 928493 := bbase (se 3 (by rfl) ⟨174092, by rfl⟩ : syracuseStep 928493 = 348185) (by norm_num)
theorem B2075381 : Blo 409770 2075381 := bbase (se 5 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 2075381 = 194567) (by norm_num)
theorem B994069 : Blo 409770 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B928565 : Blo 409770 928565 := bbase (se 5 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 928565 = 87053) (by norm_num)
theorem B928637 : Blo 409770 928637 := bbase (se 3 (by rfl) ⟨174119, by rfl⟩ : syracuseStep 928637 = 348239) (by norm_num)
theorem B928709 : Blo 409770 928709 := bbase (se 4 (by rfl) ⟨87066, by rfl⟩ : syracuseStep 928709 = 174133) (by norm_num)
theorem B928781 : Blo 409770 928781 := bbase (se 3 (by rfl) ⟨174146, by rfl⟩ : syracuseStep 928781 = 348293) (by norm_num)
theorem B928853 : Blo 409770 928853 := bbase (se 8 (by rfl) ⟨5442, by rfl⟩ : syracuseStep 928853 = 10885) (by norm_num)
theorem B1387637 : Blo 409770 1387637 := bbase (se 5 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 1387637 = 130091) (by norm_num)
theorem B928925 : Blo 409770 928925 := bbase (se 3 (by rfl) ⟨174173, by rfl⟩ : syracuseStep 928925 = 348347) (by norm_num)
theorem B928997 : Blo 409770 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B470281 : Blo 409770 470281 := bbase (se 2 (by rfl) ⟨176355, by rfl⟩ : syracuseStep 470281 = 352711) (by norm_num)
theorem B929069 : Blo 409770 929069 := bbase (se 3 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 929069 = 348401) (by norm_num)
theorem B437605 : Blo 409770 437605 := bbase (se 4 (by rfl) ⟨41025, by rfl⟩ : syracuseStep 437605 = 82051) (by norm_num)
theorem B929141 : Blo 409770 929141 := bbase (se 5 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 929141 = 87107) (by norm_num)
theorem B3943829 : Blo 409770 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B929213 : Blo 409770 929213 := bbase (se 3 (by rfl) ⟨174227, by rfl⟩ : syracuseStep 929213 = 348455) (by norm_num)
theorem B437725 : Blo 409770 437725 := bbase (se 3 (by rfl) ⟨82073, by rfl⟩ : syracuseStep 437725 = 164147) (by norm_num)
theorem B929285 : Blo 409770 929285 := bbase (se 4 (by rfl) ⟨87120, by rfl⟩ : syracuseStep 929285 = 174241) (by norm_num)
theorem B1388069 : Blo 409770 1388069 := bbase (se 4 (by rfl) ⟨130131, by rfl⟩ : syracuseStep 1388069 = 260263) (by norm_num)
theorem B2633269 : Blo 409770 2633269 := bbase (se 5 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 2633269 = 246869) (by norm_num)
theorem B929357 : Blo 409770 929357 := bbase (se 3 (by rfl) ⟨174254, by rfl⟩ : syracuseStep 929357 = 348509) (by norm_num)
theorem B1322581 : Blo 409770 1322581 := bbase (se 8 (by rfl) ⟨7749, by rfl⟩ : syracuseStep 1322581 = 15499) (by norm_num)
theorem B929429 : Blo 409770 929429 := bbase (se 6 (by rfl) ⟨21783, by rfl⟩ : syracuseStep 929429 = 43567) (by norm_num)
theorem B437977 : Blo 409770 437977 := bbase (se 2 (by rfl) ⟨164241, by rfl⟩ : syracuseStep 437977 = 328483) (by norm_num)
theorem B437981 : Blo 409770 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B929501 : Blo 409770 929501 := bbase (se 3 (by rfl) ⟨174281, by rfl⟩ : syracuseStep 929501 = 348563) (by norm_num)
theorem B2010901 : Blo 409770 2010901 := bbase (se 6 (by rfl) ⟨47130, by rfl⟩ : syracuseStep 2010901 = 94261) (by norm_num)
theorem B929573 : Blo 409770 929573 := bbase (se 4 (by rfl) ⟨87147, by rfl⟩ : syracuseStep 929573 = 174295) (by norm_num)
theorem B929645 : Blo 409770 929645 := bbase (se 3 (by rfl) ⟨174308, by rfl⟩ : syracuseStep 929645 = 348617) (by norm_num)
theorem B929717 : Blo 409770 929717 := bbase (se 5 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 929717 = 87161) (by norm_num)
theorem B1388501 : Blo 409770 1388501 := bbase (se 7 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 1388501 = 32543) (by norm_num)
theorem B503777 : Blo 409770 503777 := bbase (se 2 (by rfl) ⟨188916, by rfl⟩ : syracuseStep 503777 = 377833) (by norm_num)
theorem B929789 : Blo 409770 929789 := bbase (se 3 (by rfl) ⟨174335, by rfl⟩ : syracuseStep 929789 = 348671) (by norm_num)
theorem B2076677 : Blo 409770 2076677 := bbase (se 4 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 2076677 = 389377) (by norm_num)
theorem B2109445 : Blo 409770 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B929861 : Blo 409770 929861 := bbase (se 4 (by rfl) ⟨87174, by rfl⟩ : syracuseStep 929861 = 174349) (by norm_num)
theorem B929933 : Blo 409770 929933 := bbase (se 3 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 929933 = 348725) (by norm_num)
theorem B930005 : Blo 409770 930005 := bbase (se 7 (by rfl) ⟨10898, by rfl⟩ : syracuseStep 930005 = 21797) (by norm_num)
theorem B438545 : Blo 409770 438545 := bbase (se 2 (by rfl) ⟨164454, by rfl⟩ : syracuseStep 438545 = 328909) (by norm_num)
theorem B930077 : Blo 409770 930077 := bbase (se 3 (by rfl) ⟨174389, by rfl⟩ : syracuseStep 930077 = 348779) (by norm_num)
theorem B602453 : Blo 409770 602453 := bbase (se 10 (by rfl) ⟨882, by rfl⟩ : syracuseStep 602453 = 1765) (by norm_num)
theorem B930149 : Blo 409770 930149 := bbase (se 4 (by rfl) ⟨87201, by rfl⟩ : syracuseStep 930149 = 174403) (by norm_num)
theorem B1388933 : Blo 409770 1388933 := bbase (se 4 (by rfl) ⟨130212, by rfl⟩ : syracuseStep 1388933 = 260425) (by norm_num)
theorem B1978757 : Blo 409770 1978757 := bbase (se 4 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 1978757 = 371017) (by norm_num)
theorem B930221 : Blo 409770 930221 := bbase (se 3 (by rfl) ⟨174416, by rfl⟩ : syracuseStep 930221 = 348833) (by norm_num)
theorem B438733 : Blo 409770 438733 := bbase (se 3 (by rfl) ⟨82262, by rfl⟩ : syracuseStep 438733 = 164525) (by norm_num)
theorem B930293 : Blo 409770 930293 := bbase (se 5 (by rfl) ⟨43607, by rfl⟩ : syracuseStep 930293 = 87215) (by norm_num)
theorem B1487413 : Blo 409770 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B930365 : Blo 409770 930365 := bbase (se 3 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 930365 = 348887) (by norm_num)
theorem B930437 : Blo 409770 930437 := bbase (se 4 (by rfl) ⟨87228, by rfl⟩ : syracuseStep 930437 = 174457) (by norm_num)
theorem B3519125 : Blo 409770 3519125 := bbase (se 6 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 3519125 = 164959) (by norm_num)
theorem B930509 : Blo 409770 930509 := bbase (se 3 (by rfl) ⟨174470, by rfl⟩ : syracuseStep 930509 = 348941) (by norm_num)
theorem B930581 : Blo 409770 930581 := bbase (se 6 (by rfl) ⟨21810, by rfl⟩ : syracuseStep 930581 = 43621) (by norm_num)
theorem B1389365 : Blo 409770 1389365 := bbase (se 5 (by rfl) ⟨65126, by rfl⟩ : syracuseStep 1389365 = 130253) (by norm_num)
theorem B8926037 : Blo 409770 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B930653 : Blo 409770 930653 := bbase (se 3 (by rfl) ⟨174497, by rfl⟩ : syracuseStep 930653 = 348995) (by norm_num)
theorem B930725 : Blo 409770 930725 := bbase (se 4 (by rfl) ⟨87255, by rfl⟩ : syracuseStep 930725 = 174511) (by norm_num)
theorem B930797 : Blo 409770 930797 := bbase (se 3 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 930797 = 349049) (by norm_num)
theorem B1586213 : Blo 409770 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B930869 : Blo 409770 930869 := bbase (se 5 (by rfl) ⟨43634, by rfl⟩ : syracuseStep 930869 = 87269) (by norm_num)
theorem B930941 : Blo 409770 930941 := bbase (se 3 (by rfl) ⟨174551, by rfl⟩ : syracuseStep 930941 = 349103) (by norm_num)
theorem B1389797 : Blo 409770 1389797 := bbase (se 4 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 1389797 = 260587) (by norm_num)
theorem B439553 : Blo 409770 439553 := bbase (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) (by norm_num)
theorem B2077973 : Blo 409770 2077973 := bbase (se 6 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 2077973 = 97405) (by norm_num)
theorem B832925 : Blo 409770 832925 := bbase (se 3 (by rfl) ⟨156173, by rfl⟩ : syracuseStep 832925 = 312347) (by norm_num)
theorem B1390229 : Blo 409770 1390229 := bbase (se 6 (by rfl) ⟨32583, by rfl⟩ : syracuseStep 1390229 = 65167) (by norm_num)
theorem B439997 : Blo 409770 439997 := bbase (se 3 (by rfl) ⟨82499, by rfl⟩ : syracuseStep 439997 = 164999) (by norm_num)
theorem B1718101 : Blo 409770 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B440245 : Blo 409770 440245 := bbase (se 5 (by rfl) ⟨20636, by rfl⟩ : syracuseStep 440245 = 41273) (by norm_num)
theorem B1390661 : Blo 409770 1390661 := bbase (se 4 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 1390661 = 260749) (by norm_num)
theorem B440677 : Blo 409770 440677 := bbase (se 4 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 440677 = 82627) (by norm_num)
theorem B1325413 : Blo 409770 1325413 := bbase (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) (by norm_num)
theorem B1325477 : Blo 409770 1325477 := bbase (se 4 (by rfl) ⟨124263, by rfl⟩ : syracuseStep 1325477 = 248527) (by norm_num)
theorem B440749 : Blo 409770 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B1391093 : Blo 409770 1391093 := bbase (se 5 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 1391093 = 130415) (by norm_num)
theorem B3750421 : Blo 409770 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B2079269 : Blo 409770 2079269 := bbase (se 4 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 2079269 = 389863) (by norm_num)
theorem B834221 : Blo 409770 834221 := bbase (se 3 (by rfl) ⟨156416, by rfl⟩ : syracuseStep 834221 = 312833) (by norm_num)
theorem B441121 : Blo 409770 441121 := bbase (se 2 (by rfl) ⟨165420, by rfl⟩ : syracuseStep 441121 = 330841) (by norm_num)
theorem B1391525 : Blo 409770 1391525 := bbase (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) (by norm_num)
theorem B703477 : Blo 409770 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B1981525 : Blo 409770 1981525 := bbase (se 8 (by rfl) ⟨11610, by rfl⟩ : syracuseStep 1981525 = 23221) (by norm_num)
theorem B441497 : Blo 409770 441497 := bbase (se 2 (by rfl) ⟨165561, by rfl⟩ : syracuseStep 441497 = 331123) (by norm_num)
theorem B441569 : Blo 409770 441569 := bbase (se 2 (by rfl) ⟨165588, by rfl⟩ : syracuseStep 441569 = 331177) (by norm_num)
theorem B1391957 : Blo 409770 1391957 := bbase (se 11 (by rfl) ⟨1019, by rfl⟩ : syracuseStep 1391957 = 2039) (by norm_num)
theorem B441757 : Blo 409770 441757 := bbase (se 3 (by rfl) ⟨82829, by rfl⟩ : syracuseStep 441757 = 165659) (by norm_num)
theorem B1785253 : Blo 409770 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B769517 : Blo 409770 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B1752677 : Blo 409770 1752677 := bbase (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) (by norm_num)
theorem B1523333 : Blo 409770 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B1392389 : Blo 409770 1392389 := bbase (se 4 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 1392389 = 261073) (by norm_num)
theorem B835373 : Blo 409770 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B2080565 : Blo 409770 2080565 := bbase (se 5 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 2080565 = 195053) (by norm_num)
theorem B1556293 : Blo 409770 1556293 := bbase (se 4 (by rfl) ⟨145902, by rfl⟩ : syracuseStep 1556293 = 291805) (by norm_num)
theorem B1884005 : Blo 409770 1884005 := bbase (se 4 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 1884005 = 353251) (by norm_num)
theorem B2703253 : Blo 409770 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B704533 : Blo 409770 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B1556597 : Blo 409770 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B1392821 : Blo 409770 1392821 := bbase (se 5 (by rfl) ⟨65288, by rfl⟩ : syracuseStep 1392821 = 130577) (by norm_num)
theorem B10961365 : Blo 409770 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B4669973 : Blo 409770 4669973 := bbase (se 6 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 4669973 = 218905) (by norm_num)
theorem B1360469 : Blo 409770 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B803429 : Blo 409770 803429 := bbase (se 4 (by rfl) ⟨75321, by rfl⟩ : syracuseStep 803429 = 150643) (by norm_num)
theorem B1393253 : Blo 409770 1393253 := bbase (se 4 (by rfl) ⟨130617, by rfl⟩ : syracuseStep 1393253 = 261235) (by norm_num)
theorem B1884917 : Blo 409770 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B3130325 : Blo 409770 3130325 := bbase (se 7 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 3130325 = 73367) (by norm_num)
theorem B836573 : Blo 409770 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B1393685 : Blo 409770 1393685 := bbase (se 6 (by rfl) ⟨32664, by rfl⟩ : syracuseStep 1393685 = 65329) (by norm_num)
theorem B2081861 : Blo 409770 2081861 := bbase (se 4 (by rfl) ⟨195174, by rfl⟩ : syracuseStep 2081861 = 390349) (by norm_num)
theorem B4211957 : Blo 409770 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B1754453 : Blo 409770 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B837029 : Blo 409770 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B2344373 : Blo 409770 2344373 := bbase (se 5 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 2344373 = 219785) (by norm_num)
theorem B1394117 : Blo 409770 1394117 := bbase (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) (by norm_num)
theorem B443905 : Blo 409770 443905 := bbase (se 2 (by rfl) ⟨166464, by rfl⟩ : syracuseStep 443905 = 332929) (by norm_num)
theorem B1754693 : Blo 409770 1754693 := bbase (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) (by norm_num)
theorem B2639573 : Blo 409770 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B1984277 : Blo 409770 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B1394549 : Blo 409770 1394549 := bbase (se 5 (by rfl) ⟨65369, by rfl⟩ : syracuseStep 1394549 = 130739) (by norm_num)
theorem B1558709 : Blo 409770 1558709 := bbase (se 5 (by rfl) ⟨73064, by rfl⟩ : syracuseStep 1558709 = 146129) (by norm_num)
theorem B739613 : Blo 409770 739613 := bbase (se 3 (by rfl) ⟨138677, by rfl⟩ : syracuseStep 739613 = 277355) (by norm_num)
theorem B1394981 : Blo 409770 1394981 := bbase (se 4 (by rfl) ⟨130779, by rfl⟩ : syracuseStep 1394981 = 261559) (by norm_num)
theorem B2083157 : Blo 409770 2083157 := bbase (se 10 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 2083157 = 6103) (by norm_num)
theorem B1886597 : Blo 409770 1886597 := bbase (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) (by norm_num)
theorem B1558997 : Blo 409770 1558997 := bbase (se 7 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 1558997 = 36539) (by norm_num)
theorem B510449 : Blo 409770 510449 := bbase (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) (by norm_num)
theorem B739901 : Blo 409770 739901 := bbase (se 3 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 739901 = 277463) (by norm_num)
theorem B2345557 : Blo 409770 2345557 := bbase (se 8 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 2345557 = 27487) (by norm_num)
theorem B1395413 : Blo 409770 1395413 := bbase (se 7 (by rfl) ⟨16352, by rfl⟩ : syracuseStep 1395413 = 32705) (by norm_num)
theorem B740125 : Blo 409770 740125 := bbase (se 3 (by rfl) ⟨138773, by rfl⟩ : syracuseStep 740125 = 277547) (by norm_num)
theorem B740189 : Blo 409770 740189 := bbase (se 3 (by rfl) ⟨138785, by rfl⟩ : syracuseStep 740189 = 277571) (by norm_num)
theorem B1395845 : Blo 409770 1395845 := bbase (se 4 (by rfl) ⟨130860, by rfl⟩ : syracuseStep 1395845 = 261721) (by norm_num)
theorem B838829 : Blo 409770 838829 := bbase (se 3 (by rfl) ⟨157280, by rfl⟩ : syracuseStep 838829 = 314561) (by norm_num)
theorem B1002725 : Blo 409770 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B1396277 : Blo 409770 1396277 := bbase (se 5 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 1396277 = 130901) (by norm_num)
theorem B2084453 : Blo 409770 2084453 := bbase (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) (by norm_num)
theorem B1560181 : Blo 409770 1560181 := bbase (se 5 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 1560181 = 146267) (by norm_num)
theorem B1167061 : Blo 409770 1167061 := bbase (se 7 (by rfl) ⟨13676, by rfl⟩ : syracuseStep 1167061 = 27353) (by norm_num)
theorem B2215637 : Blo 409770 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B1756981 : Blo 409770 1756981 := bbase (se 5 (by rfl) ⟨82358, by rfl⟩ : syracuseStep 1756981 = 164717) (by norm_num)
theorem B1560485 : Blo 409770 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B5918741 : Blo 409770 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B1986677 : Blo 409770 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B938261 : Blo 409770 938261 := bbase (se 6 (by rfl) ⟨21990, by rfl⟩ : syracuseStep 938261 = 43981) (by norm_num)
theorem B938429 : Blo 409770 938429 := bbase (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) (by norm_num)
theorem B2347541 : Blo 409770 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B1430245 : Blo 409770 1430245 := bbase (se 4 (by rfl) ⟨134085, by rfl⟩ : syracuseStep 1430245 = 268171) (by norm_num)
theorem B3756917 : Blo 409770 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B2085749 : Blo 409770 2085749 := bbase (se 5 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 2085749 = 195539) (by norm_num)
theorem B1037245 : Blo 409770 1037245 := bbase (se 3 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 1037245 = 388967) (by norm_num)
theorem B1037357 : Blo 409770 1037357 := bbase (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) (by norm_num)
theorem B2806901 : Blo 409770 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B1037549 : Blo 409770 1037549 := bbase (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) (by norm_num)
theorem B1758469 : Blo 409770 1758469 := bbase (se 4 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 1758469 = 329713) (by norm_num)
theorem B1758485 : Blo 409770 1758485 := bbase (se 6 (by rfl) ⟨41214, by rfl⟩ : syracuseStep 1758485 = 82429) (by norm_num)
theorem B1005061 : Blo 409770 1005061 := bbase (se 4 (by rfl) ⟨94224, by rfl⟩ : syracuseStep 1005061 = 188449) (by norm_num)
theorem B1037893 : Blo 409770 1037893 := bbase (se 4 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 1037893 = 194605) (by norm_num)
theorem B1038005 : Blo 409770 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B415477 : Blo 409770 415477 := bbase (se 5 (by rfl) ⟨19475, by rfl⟩ : syracuseStep 415477 = 38951) (by norm_num)
theorem B415513 : Blo 409770 415513 := bbase (se 2 (by rfl) ⟨155817, by rfl⟩ : syracuseStep 415513 = 311635) (by norm_num)
theorem B1038197 : Blo 409770 1038197 := bbase (se 5 (by rfl) ⟨48665, by rfl⟩ : syracuseStep 1038197 = 97331) (by norm_num)
theorem B939941 : Blo 409770 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B1562597 : Blo 409770 1562597 := bbase (se 4 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 1562597 = 292987) (by norm_num)
theorem B3332117 : Blo 409770 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B2087045 : Blo 409770 2087045 := bbase (se 4 (by rfl) ⟨195660, by rfl⟩ : syracuseStep 2087045 = 391321) (by norm_num)
theorem B1038541 : Blo 409770 1038541 := bbase (se 3 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 1038541 = 389453) (by norm_num)
theorem B1562885 : Blo 409770 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B1038653 : Blo 409770 1038653 := bbase (se 3 (by rfl) ⟨194747, by rfl⟩ : syracuseStep 1038653 = 389495) (by norm_num)
theorem B1169909 : Blo 409770 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B1038845 : Blo 409770 1038845 := bbase (se 3 (by rfl) ⟨194783, by rfl⟩ : syracuseStep 1038845 = 389567) (by norm_num)
theorem B416389 : Blo 409770 416389 := bbase (se 4 (by rfl) ⟨39036, by rfl⟩ : syracuseStep 416389 = 78073) (by norm_num)
theorem B7002773 : Blo 409770 7002773 := bbase (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) (by norm_num)
theorem B2349749 : Blo 409770 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B2251477 : Blo 409770 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B875245 : Blo 409770 875245 := bbase (se 3 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 875245 = 328217) (by norm_num)
theorem B1039189 : Blo 409770 1039189 := bbase (se 9 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 1039189 = 6089) (by norm_num)
theorem B1039301 : Blo 409770 1039301 := bbase (se 4 (by rfl) ⟨97434, by rfl⟩ : syracuseStep 1039301 = 194869) (by norm_num)
theorem B1039493 : Blo 409770 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B57105749 : Blo 409770 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B2088341 : Blo 409770 2088341 := bbase (se 6 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 2088341 = 97891) (by norm_num)
theorem B1564069 : Blo 409770 1564069 := bbase (se 4 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 1564069 = 293263) (by norm_num)
theorem B1039837 : Blo 409770 1039837 := bbase (se 3 (by rfl) ⟨194969, by rfl⟩ : syracuseStep 1039837 = 389939) (by norm_num)
theorem B1760741 : Blo 409770 1760741 := bbase (se 4 (by rfl) ⟨165069, by rfl⟩ : syracuseStep 1760741 = 330139) (by norm_num)
theorem B2514485 : Blo 409770 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B1039949 : Blo 409770 1039949 := bbase (se 3 (by rfl) ⟨194990, by rfl⟩ : syracuseStep 1039949 = 389981) (by norm_num)
theorem B876133 : Blo 409770 876133 := bbase (se 4 (by rfl) ⟨82137, by rfl⟩ : syracuseStep 876133 = 164275) (by norm_num)
theorem B1171093 : Blo 409770 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B6676181 : Blo 409770 6676181 := bbase (se 7 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 6676181 = 156473) (by norm_num)
theorem B1564373 : Blo 409770 1564373 := bbase (se 7 (by rfl) ⟨18332, by rfl⟩ : syracuseStep 1564373 = 36665) (by norm_num)
theorem B876253 : Blo 409770 876253 := bbase (se 3 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 876253 = 328595) (by norm_num)
theorem B417521 : Blo 409770 417521 := bbase (se 2 (by rfl) ⟨156570, by rfl⟩ : syracuseStep 417521 = 313141) (by norm_num)
theorem B1040141 : Blo 409770 1040141 := bbase (se 3 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 1040141 = 390053) (by norm_num)
theorem B1171253 : Blo 409770 1171253 := bbase (se 5 (by rfl) ⟨54902, by rfl⟩ : syracuseStep 1171253 = 109805) (by norm_num)
theorem B876509 : Blo 409770 876509 := bbase (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) (by norm_num)
theorem B778261 : Blo 409770 778261 := bbase (se 6 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 778261 = 36481) (by norm_num)
theorem B1171493 : Blo 409770 1171493 := bbase (se 4 (by rfl) ⟨109827, by rfl⟩ : syracuseStep 1171493 = 219655) (by norm_num)
theorem B1040485 : Blo 409770 1040485 := bbase (se 4 (by rfl) ⟨97545, by rfl⟩ : syracuseStep 1040485 = 195091) (by norm_num)
theorem B778405 : Blo 409770 778405 := bbase (se 4 (by rfl) ⟨72975, by rfl⟩ : syracuseStep 778405 = 145951) (by norm_num)
theorem B1040597 : Blo 409770 1040597 := bbase (se 7 (by rfl) ⟨12194, by rfl⟩ : syracuseStep 1040597 = 24389) (by norm_num)
theorem B1171685 : Blo 409770 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B614669 : Blo 409770 614669 := bbase (se 3 (by rfl) ⟨115250, by rfl⟩ : syracuseStep 614669 = 230501) (by norm_num)
theorem B942349 : Blo 409770 942349 := bbase (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) (by norm_num)
theorem B614693 : Blo 409770 614693 := bbase (se 4 (by rfl) ⟨57627, by rfl⟩ : syracuseStep 614693 = 115255) (by norm_num)
theorem B614717 : Blo 409770 614717 := bbase (se 3 (by rfl) ⟨115259, by rfl⟩ : syracuseStep 614717 = 230519) (by norm_num)
theorem B778565 : Blo 409770 778565 := bbase (se 4 (by rfl) ⟨72990, by rfl⟩ : syracuseStep 778565 = 145981) (by norm_num)
theorem B418117 : Blo 409770 418117 := bbase (se 4 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 418117 = 78397) (by norm_num)
theorem B614741 : Blo 409770 614741 := bbase (se 10 (by rfl) ⟨900, by rfl⟩ : syracuseStep 614741 = 1801) (by norm_num)
theorem B614765 : Blo 409770 614765 := bbase (se 3 (by rfl) ⟨115268, by rfl⟩ : syracuseStep 614765 = 230537) (by norm_num)
theorem B614789 : Blo 409770 614789 := bbase (se 4 (by rfl) ⟨57636, by rfl⟩ : syracuseStep 614789 = 115273) (by norm_num)
theorem B1040789 : Blo 409770 1040789 := bbase (se 6 (by rfl) ⟨24393, by rfl⟩ : syracuseStep 1040789 = 48787) (by norm_num)
theorem B614813 : Blo 409770 614813 := bbase (se 3 (by rfl) ⟨115277, by rfl⟩ : syracuseStep 614813 = 230555) (by norm_num)
theorem B614837 : Blo 409770 614837 := bbase (se 5 (by rfl) ⟨28820, by rfl⟩ : syracuseStep 614837 = 57641) (by norm_num)
theorem B3957173 : Blo 409770 3957173 := bbase (se 5 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 3957173 = 370985) (by norm_num)
theorem B2974133 : Blo 409770 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B614861 : Blo 409770 614861 := bbase (se 3 (by rfl) ⟨115286, by rfl⟩ : syracuseStep 614861 = 230573) (by norm_num)
theorem B778709 : Blo 409770 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B614885 : Blo 409770 614885 := bbase (se 4 (by rfl) ⟨57645, by rfl⟩ : syracuseStep 614885 = 115291) (by norm_num)
theorem B614909 : Blo 409770 614909 := bbase (se 3 (by rfl) ⟨115295, by rfl⟩ : syracuseStep 614909 = 230591) (by norm_num)
theorem B614933 : Blo 409770 614933 := bbase (se 6 (by rfl) ⟨14412, by rfl⟩ : syracuseStep 614933 = 28825) (by norm_num)
theorem B614957 : Blo 409770 614957 := bbase (se 3 (by rfl) ⟨115304, by rfl⟩ : syracuseStep 614957 = 230609) (by norm_num)
theorem B3138101 : Blo 409770 3138101 := bbase (se 5 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 3138101 = 294197) (by norm_num)
theorem B614981 : Blo 409770 614981 := bbase (se 4 (by rfl) ⟨57654, by rfl⟩ : syracuseStep 614981 = 115309) (by norm_num)
theorem B615005 : Blo 409770 615005 := bbase (se 3 (by rfl) ⟨115313, by rfl⟩ : syracuseStep 615005 = 230627) (by norm_num)
theorem B615029 : Blo 409770 615029 := bbase (se 5 (by rfl) ⟨28829, by rfl⟩ : syracuseStep 615029 = 57659) (by norm_num)
theorem B615053 : Blo 409770 615053 := bbase (se 3 (by rfl) ⟨115322, by rfl⟩ : syracuseStep 615053 = 230645) (by norm_num)
theorem B615077 : Blo 409770 615077 := bbase (se 4 (by rfl) ⟨57663, by rfl⟩ : syracuseStep 615077 = 115327) (by norm_num)
theorem B2089637 : Blo 409770 2089637 := bbase (se 4 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 2089637 = 391807) (by norm_num)
theorem B615101 : Blo 409770 615101 := bbase (se 3 (by rfl) ⟨115331, by rfl⟩ : syracuseStep 615101 = 230663) (by norm_num)
theorem B615125 : Blo 409770 615125 := bbase (se 7 (by rfl) ⟨7208, by rfl⟩ : syracuseStep 615125 = 14417) (by norm_num)
theorem B2122469 : Blo 409770 2122469 := bbase (se 4 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 2122469 = 397963) (by norm_num)
theorem B615149 : Blo 409770 615149 := bbase (se 3 (by rfl) ⟨115340, by rfl⟩ : syracuseStep 615149 = 230681) (by norm_num)
theorem B1041133 : Blo 409770 1041133 := bbase (se 3 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 1041133 = 390425) (by norm_num)
theorem B778997 : Blo 409770 778997 := bbase (se 5 (by rfl) ⟨36515, by rfl⟩ : syracuseStep 778997 = 73031) (by norm_num)
theorem B615173 : Blo 409770 615173 := bbase (se 4 (by rfl) ⟨57672, by rfl⟩ : syracuseStep 615173 = 115345) (by norm_num)
theorem B615197 : Blo 409770 615197 := bbase (se 3 (by rfl) ⟨115349, by rfl⟩ : syracuseStep 615197 = 230699) (by norm_num)
theorem B615221 : Blo 409770 615221 := bbase (se 5 (by rfl) ⟨28838, by rfl⟩ : syracuseStep 615221 = 57677) (by norm_num)
theorem B615245 : Blo 409770 615245 := bbase (se 3 (by rfl) ⟨115358, by rfl⟩ : syracuseStep 615245 = 230717) (by norm_num)
theorem B877397 : Blo 409770 877397 := bbase (se 9 (by rfl) ⟨2570, by rfl⟩ : syracuseStep 877397 = 5141) (by norm_num)
theorem B1041245 : Blo 409770 1041245 := bbase (se 3 (by rfl) ⟨195233, by rfl⟩ : syracuseStep 1041245 = 390467) (by norm_num)
theorem B615269 : Blo 409770 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B615293 : Blo 409770 615293 := bbase (se 3 (by rfl) ⟨115367, by rfl⟩ : syracuseStep 615293 = 230735) (by norm_num)
theorem B779149 : Blo 409770 779149 := bbase (se 3 (by rfl) ⟨146090, by rfl⟩ : syracuseStep 779149 = 292181) (by norm_num)
theorem B615317 : Blo 409770 615317 := bbase (se 6 (by rfl) ⟨14421, by rfl⟩ : syracuseStep 615317 = 28843) (by norm_num)
theorem B942997 : Blo 409770 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B615341 : Blo 409770 615341 := bbase (se 3 (by rfl) ⟨115376, by rfl⟩ : syracuseStep 615341 = 230753) (by norm_num)
theorem B615365 : Blo 409770 615365 := bbase (se 4 (by rfl) ⟨57690, by rfl⟩ : syracuseStep 615365 = 115381) (by norm_num)
theorem B615389 : Blo 409770 615389 := bbase (se 3 (by rfl) ⟨115385, by rfl⟩ : syracuseStep 615389 = 230771) (by norm_num)
theorem B615413 : Blo 409770 615413 := bbase (se 5 (by rfl) ⟨28847, by rfl⟩ : syracuseStep 615413 = 57695) (by norm_num)
theorem B615437 : Blo 409770 615437 := bbase (se 3 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 615437 = 230789) (by norm_num)
theorem B1041437 : Blo 409770 1041437 := bbase (se 3 (by rfl) ⟨195269, by rfl⟩ : syracuseStep 1041437 = 390539) (by norm_num)
theorem B615461 : Blo 409770 615461 := bbase (se 4 (by rfl) ⟨57699, by rfl⟩ : syracuseStep 615461 = 115399) (by norm_num)
theorem B615485 : Blo 409770 615485 := bbase (se 3 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 615485 = 230807) (by norm_num)
theorem B877637 : Blo 409770 877637 := bbase (se 4 (by rfl) ⟨82278, by rfl⟩ : syracuseStep 877637 = 164557) (by norm_num)
theorem B615509 : Blo 409770 615509 := bbase (se 8 (by rfl) ⟨3606, by rfl⟩ : syracuseStep 615509 = 7213) (by norm_num)
theorem B615533 : Blo 409770 615533 := bbase (se 3 (by rfl) ⟨115412, by rfl⟩ : syracuseStep 615533 = 230825) (by norm_num)
theorem B615557 : Blo 409770 615557 := bbase (se 4 (by rfl) ⟨57708, by rfl⟩ : syracuseStep 615557 = 115417) (by norm_num)
theorem B615581 : Blo 409770 615581 := bbase (se 3 (by rfl) ⟨115421, by rfl⟩ : syracuseStep 615581 = 230843) (by norm_num)
theorem B615605 : Blo 409770 615605 := bbase (se 5 (by rfl) ⟨28856, by rfl⟩ : syracuseStep 615605 = 57713) (by norm_num)
theorem B779453 : Blo 409770 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B1172677 : Blo 409770 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B615629 : Blo 409770 615629 := bbase (se 3 (by rfl) ⟨115430, by rfl⟩ : syracuseStep 615629 = 230861) (by norm_num)
theorem B615653 : Blo 409770 615653 := bbase (se 4 (by rfl) ⟨57717, by rfl⟩ : syracuseStep 615653 = 115435) (by norm_num)
theorem B615677 : Blo 409770 615677 := bbase (se 3 (by rfl) ⟨115439, by rfl⟩ : syracuseStep 615677 = 230879) (by norm_num)
theorem B615701 : Blo 409770 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B615725 : Blo 409770 615725 := bbase (se 3 (by rfl) ⟨115448, by rfl⟩ : syracuseStep 615725 = 230897) (by norm_num)
theorem B615749 : Blo 409770 615749 := bbase (se 4 (by rfl) ⟨57726, by rfl⟩ : syracuseStep 615749 = 115453) (by norm_num)
theorem B615773 : Blo 409770 615773 := bbase (se 3 (by rfl) ⟨115457, by rfl⟩ : syracuseStep 615773 = 230915) (by norm_num)
theorem B615797 : Blo 409770 615797 := bbase (se 5 (by rfl) ⟨28865, by rfl⟩ : syracuseStep 615797 = 57731) (by norm_num)
theorem B1041781 : Blo 409770 1041781 := bbase (se 5 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 1041781 = 97667) (by norm_num)
theorem B615821 : Blo 409770 615821 := bbase (se 3 (by rfl) ⟨115466, by rfl⟩ : syracuseStep 615821 = 230933) (by norm_num)
theorem B615845 : Blo 409770 615845 := bbase (se 4 (by rfl) ⟨57735, by rfl⟩ : syracuseStep 615845 = 115471) (by norm_num)
theorem B615869 : Blo 409770 615869 := bbase (se 3 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 615869 = 230951) (by norm_num)
theorem B615893 : Blo 409770 615893 := bbase (se 7 (by rfl) ⟨7217, by rfl⟩ : syracuseStep 615893 = 14435) (by norm_num)
theorem B1041893 : Blo 409770 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B615917 : Blo 409770 615917 := bbase (se 3 (by rfl) ⟨115484, by rfl⟩ : syracuseStep 615917 = 230969) (by norm_num)
theorem B615941 : Blo 409770 615941 := bbase (se 4 (by rfl) ⟨57744, by rfl⟩ : syracuseStep 615941 = 115489) (by norm_num)
theorem B615965 : Blo 409770 615965 := bbase (se 3 (by rfl) ⟨115493, by rfl⟩ : syracuseStep 615965 = 230987) (by norm_num)
theorem B615989 : Blo 409770 615989 := bbase (se 5 (by rfl) ⟨28874, by rfl⟩ : syracuseStep 615989 = 57749) (by norm_num)
theorem B878141 : Blo 409770 878141 := bbase (se 3 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 878141 = 329303) (by norm_num)
theorem B878149 : Blo 409770 878149 := bbase (se 4 (by rfl) ⟨82326, by rfl⟩ : syracuseStep 878149 = 164653) (by norm_num)
theorem B616013 : Blo 409770 616013 := bbase (se 3 (by rfl) ⟨115502, by rfl⟩ : syracuseStep 616013 = 231005) (by norm_num)
theorem B616037 : Blo 409770 616037 := bbase (se 4 (by rfl) ⟨57753, by rfl⟩ : syracuseStep 616037 = 115507) (by norm_num)
theorem B616061 : Blo 409770 616061 := bbase (se 3 (by rfl) ⟨115511, by rfl⟩ : syracuseStep 616061 = 231023) (by norm_num)
theorem B616085 : Blo 409770 616085 := bbase (se 6 (by rfl) ⟨14439, by rfl⟩ : syracuseStep 616085 = 28879) (by norm_num)
theorem B1926805 : Blo 409770 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B1042085 : Blo 409770 1042085 := bbase (se 4 (by rfl) ⟨97695, by rfl⟩ : syracuseStep 1042085 = 195391) (by norm_num)
theorem B616109 : Blo 409770 616109 := bbase (se 3 (by rfl) ⟨115520, by rfl⟩ : syracuseStep 616109 = 231041) (by norm_num)
theorem B616133 : Blo 409770 616133 := bbase (se 4 (by rfl) ⟨57762, by rfl⟩ : syracuseStep 616133 = 115525) (by norm_num)
theorem B616157 : Blo 409770 616157 := bbase (se 3 (by rfl) ⟨115529, by rfl⟩ : syracuseStep 616157 = 231059) (by norm_num)
theorem B616181 : Blo 409770 616181 := bbase (se 5 (by rfl) ⟨28883, by rfl⟩ : syracuseStep 616181 = 57767) (by norm_num)
theorem B616205 : Blo 409770 616205 := bbase (se 3 (by rfl) ⟨115538, by rfl⟩ : syracuseStep 616205 = 231077) (by norm_num)
theorem B1566485 : Blo 409770 1566485 := bbase (se 6 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 1566485 = 73429) (by norm_num)
theorem B616229 : Blo 409770 616229 := bbase (se 4 (by rfl) ⟨57771, by rfl⟩ : syracuseStep 616229 = 115543) (by norm_num)
theorem B616253 : Blo 409770 616253 := bbase (se 3 (by rfl) ⟨115547, by rfl⟩ : syracuseStep 616253 = 231095) (by norm_num)
theorem B616277 : Blo 409770 616277 := bbase (se 9 (by rfl) ⟨1805, by rfl⟩ : syracuseStep 616277 = 3611) (by norm_num)
theorem B616301 : Blo 409770 616301 := bbase (se 3 (by rfl) ⟨115556, by rfl⟩ : syracuseStep 616301 = 231113) (by norm_num)
theorem B616325 : Blo 409770 616325 := bbase (se 4 (by rfl) ⟨57780, by rfl⟩ : syracuseStep 616325 = 115561) (by norm_num)
theorem B616349 : Blo 409770 616349 := bbase (se 3 (by rfl) ⟨115565, by rfl⟩ : syracuseStep 616349 = 231131) (by norm_num)
theorem B780205 : Blo 409770 780205 := bbase (se 3 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 780205 = 292577) (by norm_num)
theorem B616373 : Blo 409770 616373 := bbase (se 5 (by rfl) ⟨28892, by rfl⟩ : syracuseStep 616373 = 57785) (by norm_num)
theorem B2090933 : Blo 409770 2090933 := bbase (se 5 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 2090933 = 196025) (by norm_num)
theorem B616397 : Blo 409770 616397 := bbase (se 3 (by rfl) ⟨115574, by rfl⟩ : syracuseStep 616397 = 231149) (by norm_num)
theorem B616421 : Blo 409770 616421 := bbase (se 4 (by rfl) ⟨57789, by rfl⟩ : syracuseStep 616421 = 115579) (by norm_num)
theorem B616445 : Blo 409770 616445 := bbase (se 3 (by rfl) ⟨115583, by rfl⟩ : syracuseStep 616445 = 231167) (by norm_num)
theorem B1042429 : Blo 409770 1042429 := bbase (se 3 (by rfl) ⟨195455, by rfl⟩ : syracuseStep 1042429 = 390911) (by norm_num)
theorem B616469 : Blo 409770 616469 := bbase (se 6 (by rfl) ⟨14448, by rfl⟩ : syracuseStep 616469 = 28897) (by norm_num)
theorem B616493 : Blo 409770 616493 := bbase (se 3 (by rfl) ⟨115592, by rfl⟩ : syracuseStep 616493 = 231185) (by norm_num)
theorem B1566773 : Blo 409770 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B780349 : Blo 409770 780349 := bbase (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) (by norm_num)
theorem B616517 : Blo 409770 616517 := bbase (se 4 (by rfl) ⟨57798, by rfl⟩ : syracuseStep 616517 = 115597) (by norm_num)
theorem B616541 : Blo 409770 616541 := bbase (se 3 (by rfl) ⟨115601, by rfl⟩ : syracuseStep 616541 = 231203) (by norm_num)
theorem B1042541 : Blo 409770 1042541 := bbase (se 3 (by rfl) ⟨195476, by rfl⟩ : syracuseStep 1042541 = 390953) (by norm_num)
theorem B616565 : Blo 409770 616565 := bbase (se 5 (by rfl) ⟨28901, by rfl⟩ : syracuseStep 616565 = 57803) (by norm_num)
theorem B616589 : Blo 409770 616589 := bbase (se 3 (by rfl) ⟨115610, by rfl⟩ : syracuseStep 616589 = 231221) (by norm_num)
theorem B616613 : Blo 409770 616613 := bbase (se 4 (by rfl) ⟨57807, by rfl⟩ : syracuseStep 616613 = 115615) (by norm_num)
theorem B583861 : Blo 409770 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B616637 : Blo 409770 616637 := bbase (se 3 (by rfl) ⟨115619, by rfl⟩ : syracuseStep 616637 = 231239) (by norm_num)
theorem B616661 : Blo 409770 616661 := bbase (se 7 (by rfl) ⟨7226, by rfl⟩ : syracuseStep 616661 = 14453) (by norm_num)
theorem B780509 : Blo 409770 780509 := bbase (se 3 (by rfl) ⟨146345, by rfl⟩ : syracuseStep 780509 = 292691) (by norm_num)
theorem B616685 : Blo 409770 616685 := bbase (se 3 (by rfl) ⟨115628, by rfl⟩ : syracuseStep 616685 = 231257) (by norm_num)
theorem B616709 : Blo 409770 616709 := bbase (se 4 (by rfl) ⟨57816, by rfl⟩ : syracuseStep 616709 = 115633) (by norm_num)
theorem B1173781 : Blo 409770 1173781 := bbase (se 6 (by rfl) ⟨27510, by rfl⟩ : syracuseStep 1173781 = 55021) (by norm_num)
theorem B616733 : Blo 409770 616733 := bbase (se 3 (by rfl) ⟨115637, by rfl⟩ : syracuseStep 616733 = 231275) (by norm_num)
theorem B1042733 : Blo 409770 1042733 := bbase (se 3 (by rfl) ⟨195512, by rfl⟩ : syracuseStep 1042733 = 391025) (by norm_num)
theorem B616757 : Blo 409770 616757 := bbase (se 5 (by rfl) ⟨28910, by rfl⟩ : syracuseStep 616757 = 57821) (by norm_num)
theorem B616781 : Blo 409770 616781 := bbase (se 3 (by rfl) ⟨115646, by rfl⟩ : syracuseStep 616781 = 231293) (by norm_num)
theorem B616805 : Blo 409770 616805 := bbase (se 4 (by rfl) ⟨57825, by rfl⟩ : syracuseStep 616805 = 115651) (by norm_num)
theorem B780653 : Blo 409770 780653 := bbase (se 3 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 780653 = 292745) (by norm_num)
theorem B616829 : Blo 409770 616829 := bbase (se 3 (by rfl) ⟨115655, by rfl⟩ : syracuseStep 616829 = 231311) (by norm_num)
theorem B616853 : Blo 409770 616853 := bbase (se 6 (by rfl) ⟨14457, by rfl⟩ : syracuseStep 616853 = 28915) (by norm_num)
theorem B616877 : Blo 409770 616877 := bbase (se 3 (by rfl) ⟨115664, by rfl⟩ : syracuseStep 616877 = 231329) (by norm_num)
theorem B616901 : Blo 409770 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B616925 : Blo 409770 616925 := bbase (se 3 (by rfl) ⟨115673, by rfl⟩ : syracuseStep 616925 = 231347) (by norm_num)
theorem B616949 : Blo 409770 616949 := bbase (se 5 (by rfl) ⟨28919, by rfl⟩ : syracuseStep 616949 = 57839) (by norm_num)
theorem B518653 : Blo 409770 518653 := bbase (se 3 (by rfl) ⟨97247, by rfl⟩ : syracuseStep 518653 = 194495) (by norm_num)
theorem B616973 : Blo 409770 616973 := bbase (se 3 (by rfl) ⟨115682, by rfl⟩ : syracuseStep 616973 = 231365) (by norm_num)
theorem B616997 : Blo 409770 616997 := bbase (se 4 (by rfl) ⟨57843, by rfl⟩ : syracuseStep 616997 = 115687) (by norm_num)
theorem B617021 : Blo 409770 617021 := bbase (se 3 (by rfl) ⟨115691, by rfl⟩ : syracuseStep 617021 = 231383) (by norm_num)
theorem B617045 : Blo 409770 617045 := bbase (se 8 (by rfl) ⟨3615, by rfl⟩ : syracuseStep 617045 = 7231) (by norm_num)
theorem B617069 : Blo 409770 617069 := bbase (se 3 (by rfl) ⟨115700, by rfl⟩ : syracuseStep 617069 = 231401) (by norm_num)
theorem B846445 : Blo 409770 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B617093 : Blo 409770 617093 := bbase (se 4 (by rfl) ⟨57852, by rfl⟩ : syracuseStep 617093 = 115705) (by norm_num)
theorem B1043077 : Blo 409770 1043077 := bbase (se 4 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 1043077 = 195577) (by norm_num)
theorem B780941 : Blo 409770 780941 := bbase (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) (by norm_num)
theorem B617117 : Blo 409770 617117 := bbase (se 3 (by rfl) ⟨115709, by rfl⟩ : syracuseStep 617117 = 231419) (by norm_num)
theorem B518825 : Blo 409770 518825 := bbase (se 2 (by rfl) ⟨194559, by rfl⟩ : syracuseStep 518825 = 389119) (by norm_num)
theorem B879277 : Blo 409770 879277 := bbase (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) (by norm_num)
theorem B617141 : Blo 409770 617141 := bbase (se 5 (by rfl) ⟨28928, by rfl⟩ : syracuseStep 617141 = 57857) (by norm_num)
theorem B617165 : Blo 409770 617165 := bbase (se 3 (by rfl) ⟨115718, by rfl⟩ : syracuseStep 617165 = 231437) (by norm_num)
theorem B518881 : Blo 409770 518881 := bbase (se 2 (by rfl) ⟨194580, by rfl⟩ : syracuseStep 518881 = 389161) (by norm_num)
theorem B617189 : Blo 409770 617189 := bbase (se 4 (by rfl) ⟨57861, by rfl⟩ : syracuseStep 617189 = 115723) (by norm_num)
theorem B1043189 : Blo 409770 1043189 := bbase (se 5 (by rfl) ⟨48899, by rfl⟩ : syracuseStep 1043189 = 97799) (by norm_num)
theorem B617213 : Blo 409770 617213 := bbase (se 3 (by rfl) ⟨115727, by rfl⟩ : syracuseStep 617213 = 231455) (by norm_num)
theorem B584453 : Blo 409770 584453 := bbase (se 4 (by rfl) ⟨54792, by rfl⟩ : syracuseStep 584453 = 109585) (by norm_num)
theorem B617237 : Blo 409770 617237 := bbase (se 6 (by rfl) ⟨14466, by rfl⟩ : syracuseStep 617237 = 28933) (by norm_num)
theorem B781093 : Blo 409770 781093 := bbase (se 4 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 781093 = 146455) (by norm_num)
theorem B617261 : Blo 409770 617261 := bbase (se 3 (by rfl) ⟨115736, by rfl⟩ : syracuseStep 617261 = 231473) (by norm_num)
theorem B518977 : Blo 409770 518977 := bbase (se 2 (by rfl) ⟨194616, by rfl⟩ : syracuseStep 518977 = 389233) (by norm_num)
theorem B617285 : Blo 409770 617285 := bbase (se 4 (by rfl) ⟨57870, by rfl⟩ : syracuseStep 617285 = 115741) (by norm_num)
theorem B584533 : Blo 409770 584533 := bbase (se 9 (by rfl) ⟨1712, by rfl⟩ : syracuseStep 584533 = 3425) (by norm_num)
theorem B617309 : Blo 409770 617309 := bbase (se 3 (by rfl) ⟨115745, by rfl⟩ : syracuseStep 617309 = 231491) (by norm_num)
theorem B617333 : Blo 409770 617333 := bbase (se 5 (by rfl) ⟨28937, by rfl⟩ : syracuseStep 617333 = 57875) (by norm_num)
theorem B617357 : Blo 409770 617357 := bbase (se 3 (by rfl) ⟨115754, by rfl⟩ : syracuseStep 617357 = 231509) (by norm_num)
theorem B617381 : Blo 409770 617381 := bbase (se 4 (by rfl) ⟨57879, by rfl⟩ : syracuseStep 617381 = 115759) (by norm_num)
theorem B1043381 : Blo 409770 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B617405 : Blo 409770 617405 := bbase (se 3 (by rfl) ⟨115763, by rfl⟩ : syracuseStep 617405 = 231527) (by norm_num)
theorem B584653 : Blo 409770 584653 := bbase (se 3 (by rfl) ⟨109622, by rfl⟩ : syracuseStep 584653 = 219245) (by norm_num)
theorem B617429 : Blo 409770 617429 := bbase (se 7 (by rfl) ⟨7235, by rfl⟩ : syracuseStep 617429 = 14471) (by norm_num)
theorem B519149 : Blo 409770 519149 := bbase (se 3 (by rfl) ⟨97340, by rfl⟩ : syracuseStep 519149 = 194681) (by norm_num)
theorem B617453 : Blo 409770 617453 := bbase (se 3 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 617453 = 231545) (by norm_num)
theorem B617477 : Blo 409770 617477 := bbase (se 4 (by rfl) ⟨57888, by rfl⟩ : syracuseStep 617477 = 115777) (by norm_num)
theorem B617501 : Blo 409770 617501 := bbase (se 3 (by rfl) ⟨115781, by rfl⟩ : syracuseStep 617501 = 231563) (by norm_num)
theorem B519205 : Blo 409770 519205 := bbase (se 4 (by rfl) ⟨48675, by rfl⟩ : syracuseStep 519205 = 97351) (by norm_num)
theorem B879653 : Blo 409770 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B584749 : Blo 409770 584749 := bbase (se 3 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 584749 = 219281) (by norm_num)
theorem B617525 : Blo 409770 617525 := bbase (se 5 (by rfl) ⟨28946, by rfl⟩ : syracuseStep 617525 = 57893) (by norm_num)
theorem B617549 : Blo 409770 617549 := bbase (se 3 (by rfl) ⟨115790, by rfl⟩ : syracuseStep 617549 = 231581) (by norm_num)
theorem B781397 : Blo 409770 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B617573 : Blo 409770 617573 := bbase (se 4 (by rfl) ⟨57897, by rfl⟩ : syracuseStep 617573 = 115795) (by norm_num)
theorem B617597 : Blo 409770 617597 := bbase (se 3 (by rfl) ⟨115799, by rfl⟩ : syracuseStep 617597 = 231599) (by norm_num)
theorem B519301 : Blo 409770 519301 := bbase (se 4 (by rfl) ⟨48684, by rfl⟩ : syracuseStep 519301 = 97369) (by norm_num)
theorem B617621 : Blo 409770 617621 := bbase (se 6 (by rfl) ⟨14475, by rfl⟩ : syracuseStep 617621 = 28951) (by norm_num)
theorem B617645 : Blo 409770 617645 := bbase (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) (by norm_num)
theorem B617669 : Blo 409770 617669 := bbase (se 4 (by rfl) ⟨57906, by rfl⟩ : syracuseStep 617669 = 115813) (by norm_num)
theorem B2092229 : Blo 409770 2092229 := bbase (se 4 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 2092229 = 392293) (by norm_num)
theorem B1567957 : Blo 409770 1567957 := bbase (se 7 (by rfl) ⟨18374, by rfl⟩ : syracuseStep 1567957 = 36749) (by norm_num)
theorem B617693 : Blo 409770 617693 := bbase (se 3 (by rfl) ⟨115817, by rfl⟩ : syracuseStep 617693 = 231635) (by norm_num)
theorem B617717 : Blo 409770 617717 := bbase (se 5 (by rfl) ⟨28955, by rfl⟩ : syracuseStep 617717 = 57911) (by norm_num)
theorem B617741 : Blo 409770 617741 := bbase (se 3 (by rfl) ⟨115826, by rfl⟩ : syracuseStep 617741 = 231653) (by norm_num)
theorem B1043725 : Blo 409770 1043725 := bbase (se 3 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 1043725 = 391397) (by norm_num)
theorem B617765 : Blo 409770 617765 := bbase (se 4 (by rfl) ⟨57915, by rfl⟩ : syracuseStep 617765 = 115831) (by norm_num)
theorem B519473 : Blo 409770 519473 := bbase (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) (by norm_num)
theorem B617789 : Blo 409770 617789 := bbase (se 3 (by rfl) ⟨115835, by rfl⟩ : syracuseStep 617789 = 231671) (by norm_num)
theorem B617813 : Blo 409770 617813 := bbase (se 11 (by rfl) ⟨452, by rfl⟩ : syracuseStep 617813 = 905) (by norm_num)
theorem B519529 : Blo 409770 519529 := bbase (se 2 (by rfl) ⟨194823, by rfl⟩ : syracuseStep 519529 = 389647) (by norm_num)
theorem B617837 : Blo 409770 617837 := bbase (se 3 (by rfl) ⟨115844, by rfl⟩ : syracuseStep 617837 = 231689) (by norm_num)
theorem B1043837 : Blo 409770 1043837 := bbase (se 3 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 1043837 = 391439) (by norm_num)
theorem B617861 : Blo 409770 617861 := bbase (se 4 (by rfl) ⟨57924, by rfl⟩ : syracuseStep 617861 = 115849) (by norm_num)
theorem B617885 : Blo 409770 617885 := bbase (se 3 (by rfl) ⟨115853, by rfl⟩ : syracuseStep 617885 = 231707) (by norm_num)
theorem B1764773 : Blo 409770 1764773 := bbase (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) (by norm_num)
theorem B617909 : Blo 409770 617909 := bbase (se 5 (by rfl) ⟨28964, by rfl⟩ : syracuseStep 617909 = 57929) (by norm_num)
theorem B519625 : Blo 409770 519625 := bbase (se 2 (by rfl) ⟨194859, by rfl⟩ : syracuseStep 519625 = 389719) (by norm_num)
theorem B617933 : Blo 409770 617933 := bbase (se 3 (by rfl) ⟨115862, by rfl⟩ : syracuseStep 617933 = 231725) (by norm_num)
theorem B617957 : Blo 409770 617957 := bbase (se 4 (by rfl) ⟨57933, by rfl⟩ : syracuseStep 617957 = 115867) (by norm_num)
theorem B617981 : Blo 409770 617981 := bbase (se 3 (by rfl) ⟨115871, by rfl⟩ : syracuseStep 617981 = 231743) (by norm_num)
theorem B1568261 : Blo 409770 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B618005 : Blo 409770 618005 := bbase (se 6 (by rfl) ⟨14484, by rfl⟩ : syracuseStep 618005 = 28969) (by norm_num)
theorem B585245 : Blo 409770 585245 := bbase (se 3 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 585245 = 219467) (by norm_num)
theorem B618029 : Blo 409770 618029 := bbase (se 3 (by rfl) ⟨115880, by rfl⟩ : syracuseStep 618029 = 231761) (by norm_num)
theorem B1044029 : Blo 409770 1044029 := bbase (se 3 (by rfl) ⟨195755, by rfl⟩ : syracuseStep 1044029 = 391511) (by norm_num)
theorem B618053 : Blo 409770 618053 := bbase (se 4 (by rfl) ⟨57942, by rfl⟩ : syracuseStep 618053 = 115885) (by norm_num)
theorem B618077 : Blo 409770 618077 := bbase (se 3 (by rfl) ⟨115889, by rfl⟩ : syracuseStep 618077 = 231779) (by norm_num)
theorem B519797 : Blo 409770 519797 := bbase (se 5 (by rfl) ⟨24365, by rfl⟩ : syracuseStep 519797 = 48731) (by norm_num)
theorem B618101 : Blo 409770 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B618125 : Blo 409770 618125 := bbase (se 3 (by rfl) ⟨115898, by rfl⟩ : syracuseStep 618125 = 231797) (by norm_num)
theorem B618149 : Blo 409770 618149 := bbase (se 4 (by rfl) ⟨57951, by rfl⟩ : syracuseStep 618149 = 115903) (by norm_num)
theorem B519853 : Blo 409770 519853 := bbase (se 3 (by rfl) ⟨97472, by rfl⟩ : syracuseStep 519853 = 194945) (by norm_num)
theorem B618173 : Blo 409770 618173 := bbase (se 3 (by rfl) ⟨115907, by rfl⟩ : syracuseStep 618173 = 231815) (by norm_num)
theorem B618197 : Blo 409770 618197 := bbase (se 7 (by rfl) ⟨7244, by rfl⟩ : syracuseStep 618197 = 14489) (by norm_num)
theorem B618221 : Blo 409770 618221 := bbase (se 3 (by rfl) ⟨115916, by rfl⟩ : syracuseStep 618221 = 231833) (by norm_num)
theorem B1175285 : Blo 409770 1175285 := bbase (se 5 (by rfl) ⟨55091, by rfl⟩ : syracuseStep 1175285 = 110183) (by norm_num)
theorem B618245 : Blo 409770 618245 := bbase (se 4 (by rfl) ⟨57960, by rfl⟩ : syracuseStep 618245 = 115921) (by norm_num)
theorem B519949 : Blo 409770 519949 := bbase (se 3 (by rfl) ⟨97490, by rfl⟩ : syracuseStep 519949 = 194981) (by norm_num)
theorem B618269 : Blo 409770 618269 := bbase (se 3 (by rfl) ⟨115925, by rfl⟩ : syracuseStep 618269 = 231851) (by norm_num)
theorem B618293 : Blo 409770 618293 := bbase (se 5 (by rfl) ⟨28982, by rfl⟩ : syracuseStep 618293 = 57965) (by norm_num)
theorem B782149 : Blo 409770 782149 := bbase (se 4 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 782149 = 146653) (by norm_num)
theorem B618317 : Blo 409770 618317 := bbase (se 3 (by rfl) ⟨115934, by rfl⟩ : syracuseStep 618317 = 231869) (by norm_num)
theorem B618341 : Blo 409770 618341 := bbase (se 4 (by rfl) ⟨57969, by rfl⟩ : syracuseStep 618341 = 115939) (by norm_num)
theorem B618365 : Blo 409770 618365 := bbase (se 3 (by rfl) ⟨115943, by rfl⟩ : syracuseStep 618365 = 231887) (by norm_num)
theorem B618389 : Blo 409770 618389 := bbase (se 6 (by rfl) ⟨14493, by rfl⟩ : syracuseStep 618389 = 28987) (by norm_num)
theorem B1044373 : Blo 409770 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B716701 : Blo 409770 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B618413 : Blo 409770 618413 := bbase (se 3 (by rfl) ⟨115952, by rfl⟩ : syracuseStep 618413 = 231905) (by norm_num)
theorem B520121 : Blo 409770 520121 := bbase (se 2 (by rfl) ⟨195045, by rfl⟩ : syracuseStep 520121 = 390091) (by norm_num)
theorem B618437 : Blo 409770 618437 := bbase (se 4 (by rfl) ⟨57978, by rfl⟩ : syracuseStep 618437 = 115957) (by norm_num)
theorem B782293 : Blo 409770 782293 := bbase (se 7 (by rfl) ⟨9167, by rfl⟩ : syracuseStep 782293 = 18335) (by norm_num)
theorem B618461 : Blo 409770 618461 := bbase (se 3 (by rfl) ⟨115961, by rfl⟩ : syracuseStep 618461 = 231923) (by norm_num)
theorem B520177 : Blo 409770 520177 := bbase (se 2 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 520177 = 390133) (by norm_num)
theorem B618485 : Blo 409770 618485 := bbase (se 5 (by rfl) ⟨28991, by rfl⟩ : syracuseStep 618485 = 57983) (by norm_num)
theorem B1044485 : Blo 409770 1044485 := bbase (se 4 (by rfl) ⟨97920, by rfl⟩ : syracuseStep 1044485 = 195841) (by norm_num)
theorem B618509 : Blo 409770 618509 := bbase (se 3 (by rfl) ⟨115970, by rfl⟩ : syracuseStep 618509 = 231941) (by norm_num)
theorem B618533 : Blo 409770 618533 := bbase (se 4 (by rfl) ⟨57987, by rfl⟩ : syracuseStep 618533 = 115975) (by norm_num)
theorem B618557 : Blo 409770 618557 := bbase (se 3 (by rfl) ⟨115979, by rfl⟩ : syracuseStep 618557 = 231959) (by norm_num)
theorem B585797 : Blo 409770 585797 := bbase (se 4 (by rfl) ⟨54918, by rfl⟩ : syracuseStep 585797 = 109837) (by norm_num)
theorem B520273 : Blo 409770 520273 := bbase (se 2 (by rfl) ⟨195102, by rfl⟩ : syracuseStep 520273 = 390205) (by norm_num)
theorem B618581 : Blo 409770 618581 := bbase (se 8 (by rfl) ⟨3624, by rfl⟩ : syracuseStep 618581 = 7249) (by norm_num)
theorem B618605 : Blo 409770 618605 := bbase (se 3 (by rfl) ⟨115988, by rfl⟩ : syracuseStep 618605 = 231977) (by norm_num)
theorem B782453 : Blo 409770 782453 := bbase (se 5 (by rfl) ⟨36677, by rfl⟩ : syracuseStep 782453 = 73355) (by norm_num)
theorem B618629 : Blo 409770 618629 := bbase (se 4 (by rfl) ⟨57996, by rfl⟩ : syracuseStep 618629 = 115993) (by norm_num)
theorem B618653 : Blo 409770 618653 := bbase (se 3 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 618653 = 231995) (by norm_num)
theorem B618677 : Blo 409770 618677 := bbase (se 5 (by rfl) ⟨29000, by rfl⟩ : syracuseStep 618677 = 58001) (by norm_num)
theorem B1044677 : Blo 409770 1044677 := bbase (se 4 (by rfl) ⟨97938, by rfl⟩ : syracuseStep 1044677 = 195877) (by norm_num)
theorem B618701 : Blo 409770 618701 := bbase (se 3 (by rfl) ⟨116006, by rfl⟩ : syracuseStep 618701 = 232013) (by norm_num)
theorem B618725 : Blo 409770 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B749821 : Blo 409770 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B520445 : Blo 409770 520445 := bbase (se 3 (by rfl) ⟨97583, by rfl⟩ : syracuseStep 520445 = 195167) (by norm_num)
theorem B618749 : Blo 409770 618749 := bbase (se 3 (by rfl) ⟨116015, by rfl⟩ : syracuseStep 618749 = 232031) (by norm_num)
theorem B782597 : Blo 409770 782597 := bbase (se 4 (by rfl) ⟨73368, by rfl⟩ : syracuseStep 782597 = 146737) (by norm_num)
theorem B618773 : Blo 409770 618773 := bbase (se 6 (by rfl) ⟨14502, by rfl⟩ : syracuseStep 618773 = 29005) (by norm_num)
theorem B618797 : Blo 409770 618797 := bbase (se 3 (by rfl) ⟨116024, by rfl⟩ : syracuseStep 618797 = 232049) (by norm_num)
theorem B520501 : Blo 409770 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B618821 : Blo 409770 618821 := bbase (se 4 (by rfl) ⟨58014, by rfl⟩ : syracuseStep 618821 = 116029) (by norm_num)
theorem B618845 : Blo 409770 618845 := bbase (se 3 (by rfl) ⟨116033, by rfl⟩ : syracuseStep 618845 = 232067) (by norm_num)
theorem B618869 : Blo 409770 618869 := bbase (se 5 (by rfl) ⟨29009, by rfl⟩ : syracuseStep 618869 = 58019) (by norm_num)
theorem B618893 : Blo 409770 618893 := bbase (se 3 (by rfl) ⟨116042, by rfl⟩ : syracuseStep 618893 = 232085) (by norm_num)
theorem B520597 : Blo 409770 520597 := bbase (se 6 (by rfl) ⟨12201, by rfl⟩ : syracuseStep 520597 = 24403) (by norm_num)
theorem B618917 : Blo 409770 618917 := bbase (se 4 (by rfl) ⟨58023, by rfl⟩ : syracuseStep 618917 = 116047) (by norm_num)
theorem B618941 : Blo 409770 618941 := bbase (se 3 (by rfl) ⟨116051, by rfl⟩ : syracuseStep 618941 = 232103) (by norm_num)
theorem B618965 : Blo 409770 618965 := bbase (se 7 (by rfl) ⟨7253, by rfl⟩ : syracuseStep 618965 = 14507) (by norm_num)
theorem B2093525 : Blo 409770 2093525 := bbase (se 7 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 2093525 = 49067) (by norm_num)
theorem B618989 : Blo 409770 618989 := bbase (se 3 (by rfl) ⟨116060, by rfl⟩ : syracuseStep 618989 = 232121) (by norm_num)
theorem B619013 : Blo 409770 619013 := bbase (se 4 (by rfl) ⟨58032, by rfl⟩ : syracuseStep 619013 = 116065) (by norm_num)
theorem B619037 : Blo 409770 619037 := bbase (se 3 (by rfl) ⟨116069, by rfl⟩ : syracuseStep 619037 = 232139) (by norm_num)
theorem B1045021 : Blo 409770 1045021 := bbase (se 3 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 1045021 = 391883) (by norm_num)
theorem B782885 : Blo 409770 782885 := bbase (se 4 (by rfl) ⟨73395, by rfl⟩ : syracuseStep 782885 = 146791) (by norm_num)
theorem B619061 : Blo 409770 619061 := bbase (se 5 (by rfl) ⟨29018, by rfl⟩ : syracuseStep 619061 = 58037) (by norm_num)
theorem B520769 : Blo 409770 520769 := bbase (se 2 (by rfl) ⟨195288, by rfl⟩ : syracuseStep 520769 = 390577) (by norm_num)
theorem B619085 : Blo 409770 619085 := bbase (se 3 (by rfl) ⟨116078, by rfl⟩ : syracuseStep 619085 = 232157) (by norm_num)
theorem B1110629 : Blo 409770 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B619109 : Blo 409770 619109 := bbase (se 4 (by rfl) ⟨58041, by rfl⟩ : syracuseStep 619109 = 116083) (by norm_num)
theorem B520825 : Blo 409770 520825 := bbase (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) (by norm_num)
theorem B619133 : Blo 409770 619133 := bbase (se 3 (by rfl) ⟨116087, by rfl⟩ : syracuseStep 619133 = 232175) (by norm_num)
theorem B881293 : Blo 409770 881293 := bbase (se 3 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 881293 = 330485) (by norm_num)
theorem B1045133 : Blo 409770 1045133 := bbase (se 3 (by rfl) ⟨195962, by rfl⟩ : syracuseStep 1045133 = 391925) (by norm_num)
theorem B619157 : Blo 409770 619157 := bbase (se 6 (by rfl) ⟨14511, by rfl⟩ : syracuseStep 619157 = 29023) (by norm_num)
theorem B619181 : Blo 409770 619181 := bbase (se 3 (by rfl) ⟨116096, by rfl⟩ : syracuseStep 619181 = 232193) (by norm_num)
theorem B783037 : Blo 409770 783037 := bbase (se 3 (by rfl) ⟨146819, by rfl⟩ : syracuseStep 783037 = 293639) (by norm_num)
theorem B619205 : Blo 409770 619205 := bbase (se 4 (by rfl) ⟨58050, by rfl⟩ : syracuseStep 619205 = 116101) (by norm_num)
theorem B488141 : Blo 409770 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B520921 : Blo 409770 520921 := bbase (se 2 (by rfl) ⟨195345, by rfl⟩ : syracuseStep 520921 = 390691) (by norm_num)
theorem B619229 : Blo 409770 619229 := bbase (se 3 (by rfl) ⟨116105, by rfl⟩ : syracuseStep 619229 = 232211) (by norm_num)
theorem B3764981 : Blo 409770 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B619253 : Blo 409770 619253 := bbase (se 5 (by rfl) ⟨29027, by rfl⟩ : syracuseStep 619253 = 58055) (by norm_num)
theorem B619277 : Blo 409770 619277 := bbase (se 3 (by rfl) ⟨116114, by rfl⟩ : syracuseStep 619277 = 232229) (by norm_num)
theorem B619301 : Blo 409770 619301 := bbase (se 4 (by rfl) ⟨58059, by rfl⟩ : syracuseStep 619301 = 116119) (by norm_num)
theorem B586549 : Blo 409770 586549 := bbase (se 5 (by rfl) ⟨27494, by rfl⟩ : syracuseStep 586549 = 54989) (by norm_num)
theorem B619325 : Blo 409770 619325 := bbase (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) (by norm_num)
theorem B1045325 : Blo 409770 1045325 := bbase (se 3 (by rfl) ⟨195998, by rfl⟩ : syracuseStep 1045325 = 391997) (by norm_num)
theorem B619349 : Blo 409770 619349 := bbase (se 9 (by rfl) ⟨1814, by rfl⟩ : syracuseStep 619349 = 3629) (by norm_num)
theorem B619373 : Blo 409770 619373 := bbase (se 3 (by rfl) ⟨116132, by rfl⟩ : syracuseStep 619373 = 232265) (by norm_num)
theorem B521093 : Blo 409770 521093 := bbase (se 4 (by rfl) ⟨48852, by rfl⟩ : syracuseStep 521093 = 97705) (by norm_num)
theorem B619397 : Blo 409770 619397 := bbase (se 4 (by rfl) ⟨58068, by rfl⟩ : syracuseStep 619397 = 116137) (by norm_num)
theorem B619421 : Blo 409770 619421 := bbase (se 3 (by rfl) ⟨116141, by rfl⟩ : syracuseStep 619421 = 232283) (by norm_num)
theorem B619445 : Blo 409770 619445 := bbase (se 5 (by rfl) ⟨29036, by rfl⟩ : syracuseStep 619445 = 58073) (by norm_num)
theorem B521149 : Blo 409770 521149 := bbase (se 3 (by rfl) ⟨97715, by rfl⟩ : syracuseStep 521149 = 195431) (by norm_num)
theorem B619469 : Blo 409770 619469 := bbase (se 3 (by rfl) ⟨116150, by rfl⟩ : syracuseStep 619469 = 232301) (by norm_num)
theorem B619493 : Blo 409770 619493 := bbase (se 4 (by rfl) ⟨58077, by rfl⟩ : syracuseStep 619493 = 116155) (by norm_num)
theorem B783341 : Blo 409770 783341 := bbase (se 3 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 783341 = 293753) (by norm_num)
theorem B619517 : Blo 409770 619517 := bbase (se 3 (by rfl) ⟨116159, by rfl⟩ : syracuseStep 619517 = 232319) (by norm_num)
theorem B1504261 : Blo 409770 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B619541 : Blo 409770 619541 := bbase (se 6 (by rfl) ⟨14520, by rfl⟩ : syracuseStep 619541 = 29041) (by norm_num)
theorem B521245 : Blo 409770 521245 := bbase (se 3 (by rfl) ⟨97733, by rfl⟩ : syracuseStep 521245 = 195467) (by norm_num)
theorem B619565 : Blo 409770 619565 := bbase (se 3 (by rfl) ⟨116168, by rfl⟩ : syracuseStep 619565 = 232337) (by norm_num)
theorem B619589 : Blo 409770 619589 := bbase (se 4 (by rfl) ⟨58086, by rfl⟩ : syracuseStep 619589 = 116173) (by norm_num)
theorem B619613 : Blo 409770 619613 := bbase (se 3 (by rfl) ⟨116177, by rfl⟩ : syracuseStep 619613 = 232355) (by norm_num)
theorem B619637 : Blo 409770 619637 := bbase (se 5 (by rfl) ⟨29045, by rfl⟩ : syracuseStep 619637 = 58091) (by norm_num)
theorem B619661 : Blo 409770 619661 := bbase (se 3 (by rfl) ⟨116186, by rfl⟩ : syracuseStep 619661 = 232373) (by norm_num)
theorem B1766549 : Blo 409770 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B1045669 : Blo 409770 1045669 := bbase (se 4 (by rfl) ⟨98031, by rfl⟩ : syracuseStep 1045669 = 196063) (by norm_num)
theorem B619685 : Blo 409770 619685 := bbase (se 4 (by rfl) ⟨58095, by rfl⟩ : syracuseStep 619685 = 116191) (by norm_num)
theorem B619709 : Blo 409770 619709 := bbase (se 3 (by rfl) ⟨116195, by rfl⟩ : syracuseStep 619709 = 232391) (by norm_num)
theorem B521417 : Blo 409770 521417 := bbase (se 2 (by rfl) ⟨195531, by rfl⟩ : syracuseStep 521417 = 391063) (by norm_num)
theorem B619733 : Blo 409770 619733 := bbase (se 7 (by rfl) ⟨7262, by rfl⟩ : syracuseStep 619733 = 14525) (by norm_num)
theorem B619757 : Blo 409770 619757 := bbase (se 3 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 619757 = 232409) (by norm_num)
theorem B849133 : Blo 409770 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B521473 : Blo 409770 521473 := bbase (se 2 (by rfl) ⟨195552, by rfl⟩ : syracuseStep 521473 = 391105) (by norm_num)
theorem B619781 : Blo 409770 619781 := bbase (se 4 (by rfl) ⟨58104, by rfl⟩ : syracuseStep 619781 = 116209) (by norm_num)
theorem B1045781 : Blo 409770 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B619805 : Blo 409770 619805 := bbase (se 3 (by rfl) ⟨116213, by rfl⟩ : syracuseStep 619805 = 232427) (by norm_num)
theorem B1176869 : Blo 409770 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B619829 : Blo 409770 619829 := bbase (se 5 (by rfl) ⟨29054, by rfl⟩ : syracuseStep 619829 = 58109) (by norm_num)
theorem B619853 : Blo 409770 619853 := bbase (se 3 (by rfl) ⟨116222, by rfl⟩ : syracuseStep 619853 = 232445) (by norm_num)
theorem B521569 : Blo 409770 521569 := bbase (se 2 (by rfl) ⟨195588, by rfl⟩ : syracuseStep 521569 = 391177) (by norm_num)
theorem B619877 : Blo 409770 619877 := bbase (se 4 (by rfl) ⟨58113, by rfl⟩ : syracuseStep 619877 = 116227) (by norm_num)
theorem B619901 : Blo 409770 619901 := bbase (se 3 (by rfl) ⟨116231, by rfl⟩ : syracuseStep 619901 = 232463) (by norm_num)
theorem B619925 : Blo 409770 619925 := bbase (se 6 (by rfl) ⟨14529, by rfl⟩ : syracuseStep 619925 = 29059) (by norm_num)
theorem B619949 : Blo 409770 619949 := bbase (se 3 (by rfl) ⟨116240, by rfl⟩ : syracuseStep 619949 = 232481) (by norm_num)
theorem B619973 : Blo 409770 619973 := bbase (se 4 (by rfl) ⟨58122, by rfl⟩ : syracuseStep 619973 = 116245) (by norm_num)
theorem B1045973 : Blo 409770 1045973 := bbase (se 7 (by rfl) ⟨12257, by rfl⟩ : syracuseStep 1045973 = 24515) (by norm_num)
theorem B619997 : Blo 409770 619997 := bbase (se 3 (by rfl) ⟨116249, by rfl⟩ : syracuseStep 619997 = 232499) (by norm_num)
theorem B620021 : Blo 409770 620021 := bbase (se 5 (by rfl) ⟨29063, by rfl⟩ : syracuseStep 620021 = 58127) (by norm_num)
theorem B882181 : Blo 409770 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B521741 : Blo 409770 521741 := bbase (se 3 (by rfl) ⟨97826, by rfl⟩ : syracuseStep 521741 = 195653) (by norm_num)
theorem B620045 : Blo 409770 620045 := bbase (se 3 (by rfl) ⟨116258, by rfl⟩ : syracuseStep 620045 = 232517) (by norm_num)
theorem B620069 : Blo 409770 620069 := bbase (se 4 (by rfl) ⟨58131, by rfl⟩ : syracuseStep 620069 = 116263) (by norm_num)
theorem B620093 : Blo 409770 620093 := bbase (se 3 (by rfl) ⟨116267, by rfl⟩ : syracuseStep 620093 = 232535) (by norm_num)
theorem B521797 : Blo 409770 521797 := bbase (se 4 (by rfl) ⟨48918, by rfl⟩ : syracuseStep 521797 = 97837) (by norm_num)
theorem B1570373 : Blo 409770 1570373 := bbase (se 4 (by rfl) ⟨147222, by rfl⟩ : syracuseStep 1570373 = 294445) (by norm_num)
theorem B587341 : Blo 409770 587341 := bbase (se 3 (by rfl) ⟨110126, by rfl⟩ : syracuseStep 587341 = 220253) (by norm_num)
theorem B2979413 : Blo 409770 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B620117 : Blo 409770 620117 := bbase (se 8 (by rfl) ⟨3633, by rfl⟩ : syracuseStep 620117 = 7267) (by norm_num)
theorem B620141 : Blo 409770 620141 := bbase (se 3 (by rfl) ⟨116276, by rfl⟩ : syracuseStep 620141 = 232553) (by norm_num)
theorem B620165 : Blo 409770 620165 := bbase (se 4 (by rfl) ⟨58140, by rfl⟩ : syracuseStep 620165 = 116281) (by norm_num)
theorem B620189 : Blo 409770 620189 := bbase (se 3 (by rfl) ⟨116285, by rfl⟩ : syracuseStep 620189 = 232571) (by norm_num)
theorem B521893 : Blo 409770 521893 := bbase (se 4 (by rfl) ⟨48927, by rfl⟩ : syracuseStep 521893 = 97855) (by norm_num)
theorem B620213 : Blo 409770 620213 := bbase (se 5 (by rfl) ⟨29072, by rfl⟩ : syracuseStep 620213 = 58145) (by norm_num)
theorem B620237 : Blo 409770 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B784093 : Blo 409770 784093 := bbase (se 3 (by rfl) ⟨147017, by rfl⟩ : syracuseStep 784093 = 294035) (by norm_num)
theorem B620261 : Blo 409770 620261 := bbase (se 4 (by rfl) ⟨58149, by rfl⟩ : syracuseStep 620261 = 116299) (by norm_num)
theorem B620285 : Blo 409770 620285 := bbase (se 3 (by rfl) ⟨116303, by rfl⟩ : syracuseStep 620285 = 232607) (by norm_num)
theorem B620309 : Blo 409770 620309 := bbase (se 6 (by rfl) ⟨14538, by rfl⟩ : syracuseStep 620309 = 29077) (by norm_num)
theorem B1046317 : Blo 409770 1046317 := bbase (se 3 (by rfl) ⟨196184, by rfl⟩ : syracuseStep 1046317 = 392369) (by norm_num)
theorem B620333 : Blo 409770 620333 := bbase (se 3 (by rfl) ⟨116312, by rfl⟩ : syracuseStep 620333 = 232625) (by norm_num)
theorem B620357 : Blo 409770 620357 := bbase (se 4 (by rfl) ⟨58158, by rfl⟩ : syracuseStep 620357 = 116317) (by norm_num)
theorem B522065 : Blo 409770 522065 := bbase (se 2 (by rfl) ⟨195774, by rfl⟩ : syracuseStep 522065 = 391549) (by norm_num)
theorem B620381 : Blo 409770 620381 := bbase (se 3 (by rfl) ⟨116321, by rfl⟩ : syracuseStep 620381 = 232643) (by norm_num)
theorem B1570661 : Blo 409770 1570661 := bbase (se 4 (by rfl) ⟨147249, by rfl⟩ : syracuseStep 1570661 = 294499) (by norm_num)
theorem B784237 : Blo 409770 784237 := bbase (se 3 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 784237 = 294089) (by norm_num)
theorem B620405 : Blo 409770 620405 := bbase (se 5 (by rfl) ⟨29081, by rfl⟩ : syracuseStep 620405 = 58163) (by norm_num)
theorem B522121 : Blo 409770 522121 := bbase (se 2 (by rfl) ⟨195795, by rfl⟩ : syracuseStep 522121 = 391591) (by norm_num)
theorem B620429 : Blo 409770 620429 := bbase (se 3 (by rfl) ⟨116330, by rfl⟩ : syracuseStep 620429 = 232661) (by norm_num)
theorem B587677 : Blo 409770 587677 := bbase (se 3 (by rfl) ⟨110189, by rfl⟩ : syracuseStep 587677 = 220379) (by norm_num)
theorem B1046429 : Blo 409770 1046429 := bbase (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) (by norm_num)
theorem B620453 : Blo 409770 620453 := bbase (se 4 (by rfl) ⟨58167, by rfl⟩ : syracuseStep 620453 = 116335) (by norm_num)
theorem B620477 : Blo 409770 620477 := bbase (se 3 (by rfl) ⟨116339, by rfl⟩ : syracuseStep 620477 = 232679) (by norm_num)
theorem B1177541 : Blo 409770 1177541 := bbase (se 4 (by rfl) ⟨110394, by rfl⟩ : syracuseStep 1177541 = 220789) (by norm_num)
theorem B620501 : Blo 409770 620501 := bbase (se 7 (by rfl) ⟨7271, by rfl⟩ : syracuseStep 620501 = 14543) (by norm_num)
theorem B522217 : Blo 409770 522217 := bbase (se 2 (by rfl) ⟨195831, by rfl⟩ : syracuseStep 522217 = 391663) (by norm_num)
theorem B620525 : Blo 409770 620525 := bbase (se 3 (by rfl) ⟨116348, by rfl⟩ : syracuseStep 620525 = 232697) (by norm_num)
theorem B882677 : Blo 409770 882677 := bbase (se 5 (by rfl) ⟨41375, by rfl⟩ : syracuseStep 882677 = 82751) (by norm_num)
theorem B620549 : Blo 409770 620549 := bbase (se 4 (by rfl) ⟨58176, by rfl⟩ : syracuseStep 620549 = 116353) (by norm_num)
theorem B784397 : Blo 409770 784397 := bbase (se 3 (by rfl) ⟨147074, by rfl⟩ : syracuseStep 784397 = 294149) (by norm_num)
theorem B620573 : Blo 409770 620573 := bbase (se 3 (by rfl) ⟨116357, by rfl⟩ : syracuseStep 620573 = 232715) (by norm_num)
theorem B620597 : Blo 409770 620597 := bbase (se 5 (by rfl) ⟨29090, by rfl⟩ : syracuseStep 620597 = 58181) (by norm_num)
theorem B751693 : Blo 409770 751693 := bbase (se 3 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 751693 = 281885) (by norm_num)
theorem B620621 : Blo 409770 620621 := bbase (se 3 (by rfl) ⟨116366, by rfl⟩ : syracuseStep 620621 = 232733) (by norm_num)
theorem B1046621 : Blo 409770 1046621 := bbase (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) (by norm_num)
theorem B620645 : Blo 409770 620645 := bbase (se 4 (by rfl) ⟨58185, by rfl⟩ : syracuseStep 620645 = 116371) (by norm_num)
theorem B587893 : Blo 409770 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B522389 : Blo 409770 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B784541 : Blo 409770 784541 := bbase (se 3 (by rfl) ⟨147101, by rfl⟩ : syracuseStep 784541 = 294203) (by norm_num)
theorem B522445 : Blo 409770 522445 := bbase (se 3 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 522445 = 195917) (by norm_num)
theorem B522541 : Blo 409770 522541 := bbase (se 3 (by rfl) ⟨97976, by rfl⟩ : syracuseStep 522541 = 195953) (by norm_num)
theorem B751925 : Blo 409770 751925 := bbase (se 5 (by rfl) ⟨35246, by rfl⟩ : syracuseStep 751925 = 70493) (by norm_num)
theorem B1603925 : Blo 409770 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B1177973 : Blo 409770 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B1046965 : Blo 409770 1046965 := bbase (se 5 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 1046965 = 98153) (by norm_num)
theorem B784829 : Blo 409770 784829 := bbase (se 3 (by rfl) ⟨147155, by rfl⟩ : syracuseStep 784829 = 294311) (by norm_num)
theorem B522713 : Blo 409770 522713 := bbase (se 2 (by rfl) ⟨196017, by rfl⟩ : syracuseStep 522713 = 392035) (by norm_num)
theorem B588269 : Blo 409770 588269 := bbase (se 3 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 588269 = 220601) (by norm_num)
theorem B522769 : Blo 409770 522769 := bbase (se 2 (by rfl) ⟨196038, by rfl⟩ : syracuseStep 522769 = 392077) (by norm_num)
theorem B1047077 : Blo 409770 1047077 := bbase (se 4 (by rfl) ⟨98163, by rfl⟩ : syracuseStep 1047077 = 196327) (by norm_num)
theorem B784981 : Blo 409770 784981 := bbase (se 8 (by rfl) ⟨4599, by rfl⟩ : syracuseStep 784981 = 9199) (by norm_num)
theorem B522865 : Blo 409770 522865 := bbase (se 2 (by rfl) ⟨196074, by rfl⟩ : syracuseStep 522865 = 392149) (by norm_num)
theorem B1047269 : Blo 409770 1047269 := bbase (se 4 (by rfl) ⟨98181, by rfl⟩ : syracuseStep 1047269 = 196363) (by norm_num)
theorem B523037 : Blo 409770 523037 := bbase (se 3 (by rfl) ⟨98069, by rfl⟩ : syracuseStep 523037 = 196139) (by norm_num)
theorem B4225877 : Blo 409770 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B523093 : Blo 409770 523093 := bbase (se 9 (by rfl) ⟨1532, by rfl⟩ : syracuseStep 523093 = 3065) (by norm_num)
theorem B883541 : Blo 409770 883541 := bbase (se 9 (by rfl) ⟨2588, by rfl⟩ : syracuseStep 883541 = 5177) (by norm_num)
theorem B555877 : Blo 409770 555877 := bbase (se 4 (by rfl) ⟨52113, by rfl⟩ : syracuseStep 555877 = 104227) (by norm_num)
theorem B785285 : Blo 409770 785285 := bbase (se 4 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 785285 = 147241) (by norm_num)
theorem B523189 : Blo 409770 523189 := bbase (se 5 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 523189 = 49049) (by norm_num)
theorem B883685 : Blo 409770 883685 := bbase (se 4 (by rfl) ⟨82845, by rfl⟩ : syracuseStep 883685 = 165691) (by norm_num)
theorem B523361 : Blo 409770 523361 := bbase (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) (by norm_num)
theorem B523417 : Blo 409770 523417 := bbase (se 2 (by rfl) ⟨196281, by rfl⟩ : syracuseStep 523417 = 392563) (by norm_num)
theorem B523513 : Blo 409770 523513 := bbase (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) (by norm_num)
theorem B3211093 : Blo 409770 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B9469973 : Blo 409770 9469973 := bstep (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) B443905
theorem B1114435 : Blo 409770 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B3113315 : Blo 409770 3113315 := bstep (se 1 (by rfl) ⟨2334986, by rfl⟩ : syracuseStep 3113315 = 4669973) B4669973
theorem B1409393 : Blo 409770 1409393 := bstep (se 2 (by rfl) ⟨528522, by rfl⟩ : syracuseStep 1409393 = 1057045) B1057045
theorem B557489 : Blo 409770 557489 := bstep (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) B418117
theorem B14615153 : Blo 409770 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1606541 : Blo 409770 1606541 := bstep (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) B602453
theorem B558019 : Blo 409770 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B1672433 : Blo 409770 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B7046513 : Blo 409770 7046513 := bstep (se 2 (by rfl) ⟨2642442, by rfl⟩ : syracuseStep 7046513 = 5284885) B5284885
theorem B493075 : Blo 409770 493075 := bstep (se 1 (by rfl) ⟨369806, by rfl⟩ : syracuseStep 493075 = 739613) B739613
theorem B493459 : Blo 409770 493459 := bstep (se 1 (by rfl) ⟨370094, by rfl⟩ : syracuseStep 493459 = 740189) B740189
theorem B559219 : Blo 409770 559219 := bstep (se 1 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 559219 = 838829) B838829
theorem B657587 : Blo 409770 657587 := bstep (se 1 (by rfl) ⟨493190, by rfl⟩ : syracuseStep 657587 = 986381) B986381
theorem B461011 : Blo 409770 461011 := bstep (se 1 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 461011 = 691517) B691517
theorem B657715 : Blo 409770 657715 := bstep (se 1 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 657715 = 986573) B986573
theorem B461155 : Blo 409770 461155 := bstep (se 1 (by rfl) ⟨345866, by rfl⟩ : syracuseStep 461155 = 691733) B691733
theorem B657857 : Blo 409770 657857 := bstep (se 2 (by rfl) ⟨246696, by rfl⟩ : syracuseStep 657857 = 493393) B493393
theorem B1477091 : Blo 409770 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B461299 : Blo 409770 461299 := bstep (se 1 (by rfl) ⟨345974, by rfl⟩ : syracuseStep 461299 = 691949) B691949
theorem B985603 : Blo 409770 985603 := bstep (se 1 (by rfl) ⟨739202, by rfl⟩ : syracuseStep 985603 = 1478405) B1478405
theorem B2230861 : Blo 409770 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B461443 : Blo 409770 461443 := bstep (se 1 (by rfl) ⟨346082, by rfl⟩ : syracuseStep 461443 = 692165) B692165
theorem B658145 : Blo 409770 658145 := bstep (se 2 (by rfl) ⟨246804, by rfl⟩ : syracuseStep 658145 = 493609) B493609
theorem B461587 : Blo 409770 461587 := bstep (se 1 (by rfl) ⟨346190, by rfl⟩ : syracuseStep 461587 = 692381) B692381
theorem B461731 : Blo 409770 461731 := bstep (se 1 (by rfl) ⟨346298, by rfl⟩ : syracuseStep 461731 = 692597) B692597
theorem B625619 : Blo 409770 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B625649 : Blo 409770 625649 := bstep (se 2 (by rfl) ⟨234618, by rfl⟩ : syracuseStep 625649 = 469237) B469237
theorem B461875 : Blo 409770 461875 := bstep (se 1 (by rfl) ⟨346406, by rfl⟩ : syracuseStep 461875 = 692813) B692813
theorem B462019 : Blo 409770 462019 := bstep (se 1 (by rfl) ⟨346514, by rfl⟩ : syracuseStep 462019 = 693029) B693029
theorem B1674445 : Blo 409770 1674445 := bstep (se 3 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 1674445 = 627917) B627917
theorem B1969379 : Blo 409770 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B691537 : Blo 409770 691537 := bstep (se 2 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 691537 = 518653) B518653
theorem B462163 : Blo 409770 462163 := bstep (se 1 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 462163 = 693245) B693245
theorem B691571 : Blo 409770 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B1871267 : Blo 409770 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B462307 : Blo 409770 462307 := bstep (se 1 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 462307 = 693461) B693461
theorem B691699 : Blo 409770 691699 := bstep (se 1 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 691699 = 1037549) B1037549
theorem B658945 : Blo 409770 658945 := bstep (se 2 (by rfl) ⟨247104, by rfl⟩ : syracuseStep 658945 = 494209) B494209
theorem B1314353 : Blo 409770 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B888401 : Blo 409770 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B462451 : Blo 409770 462451 := bstep (se 1 (by rfl) ⟨346838, by rfl⟩ : syracuseStep 462451 = 693677) B693677
theorem B691841 : Blo 409770 691841 := bstep (se 2 (by rfl) ⟨259440, by rfl⟩ : syracuseStep 691841 = 518881) B518881
theorem B986833 : Blo 409770 986833 := bstep (se 2 (by rfl) ⟨370062, by rfl⟩ : syracuseStep 986833 = 740125) B740125
theorem B691969 : Blo 409770 691969 := bstep (se 2 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 691969 = 518977) B518977
theorem B462595 : Blo 409770 462595 := bstep (se 1 (by rfl) ⟨346946, by rfl⟩ : syracuseStep 462595 = 693893) B693893
theorem B692003 : Blo 409770 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B5345165 : Blo 409770 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B462739 : Blo 409770 462739 := bstep (se 1 (by rfl) ⟨347054, by rfl⟩ : syracuseStep 462739 = 694109) B694109
theorem B692131 : Blo 409770 692131 := bstep (se 1 (by rfl) ⟨519098, by rfl⟩ : syracuseStep 692131 = 1038197) B1038197
theorem B626627 : Blo 409770 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B462883 : Blo 409770 462883 := bstep (se 1 (by rfl) ⟨347162, by rfl⟩ : syracuseStep 462883 = 694325) B694325
theorem B692273 : Blo 409770 692273 := bstep (se 2 (by rfl) ⟨259602, by rfl⟩ : syracuseStep 692273 = 519205) B519205
theorem B1314893 : Blo 409770 1314893 := bstep (se 3 (by rfl) ⟨246542, by rfl⟩ : syracuseStep 1314893 = 493085) B493085
theorem B1413197 : Blo 409770 1413197 := bstep (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) B529949
theorem B692401 : Blo 409770 692401 := bstep (se 2 (by rfl) ⟨259650, by rfl⟩ : syracuseStep 692401 = 519301) B519301
theorem B463027 : Blo 409770 463027 := bstep (se 1 (by rfl) ⟨347270, by rfl⟩ : syracuseStep 463027 = 694541) B694541
theorem B528563 : Blo 409770 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B692435 : Blo 409770 692435 := bstep (se 1 (by rfl) ⟨519326, by rfl⟩ : syracuseStep 692435 = 1038653) B1038653
theorem B463171 : Blo 409770 463171 := bstep (se 1 (by rfl) ⟨347378, by rfl⟩ : syracuseStep 463171 = 694757) B694757
theorem B692563 : Blo 409770 692563 := bstep (se 1 (by rfl) ⟨519422, by rfl⟩ : syracuseStep 692563 = 1038845) B1038845
theorem B627041 : Blo 409770 627041 := bstep (se 2 (by rfl) ⟨235140, by rfl⟩ : syracuseStep 627041 = 470281) B470281
theorem B463315 : Blo 409770 463315 := bstep (se 1 (by rfl) ⟨347486, by rfl⟩ : syracuseStep 463315 = 694973) B694973
theorem B692705 : Blo 409770 692705 := bstep (se 2 (by rfl) ⟨259764, by rfl⟩ : syracuseStep 692705 = 519529) B519529
theorem B2626019 : Blo 409770 2626019 := bstep (se 1 (by rfl) ⟨1969514, by rfl⟩ : syracuseStep 2626019 = 3939029) B3939029
theorem B922193 : Blo 409770 922193 := bstep (se 2 (by rfl) ⟨345822, by rfl⟩ : syracuseStep 922193 = 691645) B691645
theorem B692833 : Blo 409770 692833 := bstep (se 2 (by rfl) ⟨259812, by rfl⟩ : syracuseStep 692833 = 519625) B519625
theorem B922211 : Blo 409770 922211 := bstep (se 1 (by rfl) ⟨691658, by rfl⟩ : syracuseStep 922211 = 1383317) B1383317
theorem B463459 : Blo 409770 463459 := bstep (se 1 (by rfl) ⟨347594, by rfl⟩ : syracuseStep 463459 = 695189) B695189
theorem B692867 : Blo 409770 692867 := bstep (se 1 (by rfl) ⟨519650, by rfl⟩ : syracuseStep 692867 = 1039301) B1039301
theorem B660163 : Blo 409770 660163 := bstep (se 1 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 660163 = 990245) B990245
theorem B3511025 : Blo 409770 3511025 := bstep (se 2 (by rfl) ⟨1316634, by rfl⟩ : syracuseStep 3511025 = 2633269) B2633269
theorem B463603 : Blo 409770 463603 := bstep (se 1 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 463603 = 695405) B695405
theorem B692995 : Blo 409770 692995 := bstep (se 1 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 692995 = 1039493) B1039493
theorem B1250093 : Blo 409770 1250093 := bstep (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) B468785
theorem B1970993 : Blo 409770 1970993 := bstep (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) B1478245
theorem B922481 : Blo 409770 922481 := bstep (se 2 (by rfl) ⟨345930, by rfl⟩ : syracuseStep 922481 = 691861) B691861
theorem B922499 : Blo 409770 922499 := bstep (se 1 (by rfl) ⟨691874, by rfl⟩ : syracuseStep 922499 = 1383749) B1383749
theorem B463747 : Blo 409770 463747 := bstep (se 1 (by rfl) ⟨347810, by rfl⟩ : syracuseStep 463747 = 695621) B695621
theorem B693137 : Blo 409770 693137 := bstep (se 2 (by rfl) ⟨259926, by rfl⟩ : syracuseStep 693137 = 519853) B519853
theorem B693265 : Blo 409770 693265 := bstep (se 2 (by rfl) ⟨259974, by rfl⟩ : syracuseStep 693265 = 519949) B519949
theorem B463891 : Blo 409770 463891 := bstep (se 1 (by rfl) ⟨347918, by rfl⟩ : syracuseStep 463891 = 695837) B695837
theorem B1676323 : Blo 409770 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B693299 : Blo 409770 693299 := bstep (se 1 (by rfl) ⟨519974, by rfl⟩ : syracuseStep 693299 = 1039949) B1039949
theorem B922769 : Blo 409770 922769 := bstep (se 2 (by rfl) ⟨346038, by rfl⟩ : syracuseStep 922769 = 692077) B692077
theorem B922787 : Blo 409770 922787 := bstep (se 1 (by rfl) ⟨692090, by rfl⟩ : syracuseStep 922787 = 1384181) B1384181
theorem B464035 : Blo 409770 464035 := bstep (se 1 (by rfl) ⟨348026, by rfl⟩ : syracuseStep 464035 = 696053) B696053
theorem B693427 : Blo 409770 693427 := bstep (se 1 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 693427 = 1040141) B1040141
theorem B9999557 : Blo 409770 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B955601 : Blo 409770 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B464179 : Blo 409770 464179 := bstep (se 1 (by rfl) ⟨348134, by rfl⟩ : syracuseStep 464179 = 696269) B696269
theorem B693569 : Blo 409770 693569 := bstep (se 2 (by rfl) ⟨260088, by rfl⟩ : syracuseStep 693569 = 520177) B520177
theorem B8885645 : Blo 409770 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B660881 : Blo 409770 660881 := bstep (se 2 (by rfl) ⟨247830, by rfl⟩ : syracuseStep 660881 = 495661) B495661
theorem B923057 : Blo 409770 923057 := bstep (se 2 (by rfl) ⟨346146, by rfl⟩ : syracuseStep 923057 = 692293) B692293
theorem B693697 : Blo 409770 693697 := bstep (se 2 (by rfl) ⟨260136, by rfl⟩ : syracuseStep 693697 = 520273) B520273
theorem B923075 : Blo 409770 923075 := bstep (se 1 (by rfl) ⟨692306, by rfl⟩ : syracuseStep 923075 = 1384613) B1384613
theorem B464323 : Blo 409770 464323 := bstep (se 1 (by rfl) ⟨348242, by rfl⟩ : syracuseStep 464323 = 696485) B696485
theorem B693731 : Blo 409770 693731 := bstep (se 1 (by rfl) ⟨520298, by rfl⟩ : syracuseStep 693731 = 1040597) B1040597
theorem B3118661 : Blo 409770 3118661 := bstep (se 4 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 3118661 = 584749) B584749
theorem B464467 : Blo 409770 464467 := bstep (se 1 (by rfl) ⟨348350, by rfl⟩ : syracuseStep 464467 = 696701) B696701
theorem B693859 : Blo 409770 693859 := bstep (se 1 (by rfl) ⟨520394, by rfl⟩ : syracuseStep 693859 = 1040789) B1040789
theorem B12719729 : Blo 409770 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B661169 : Blo 409770 661169 := bstep (se 2 (by rfl) ⟨247938, by rfl⟩ : syracuseStep 661169 = 495877) B495877
theorem B923345 : Blo 409770 923345 := bstep (se 2 (by rfl) ⟨346254, by rfl⟩ : syracuseStep 923345 = 692509) B692509
theorem B923363 : Blo 409770 923363 := bstep (se 1 (by rfl) ⟨692522, by rfl⟩ : syracuseStep 923363 = 1385045) B1385045
theorem B464611 : Blo 409770 464611 := bstep (se 1 (by rfl) ⟨348458, by rfl⟩ : syracuseStep 464611 = 696917) B696917
theorem B694001 : Blo 409770 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B1414979 : Blo 409770 1414979 := bstep (se 1 (by rfl) ⟨1061234, by rfl⟩ : syracuseStep 1414979 = 2122469) B2122469
theorem B694129 : Blo 409770 694129 := bstep (se 2 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 694129 = 520597) B520597
theorem B464755 : Blo 409770 464755 := bstep (se 1 (by rfl) ⟨348566, by rfl⟩ : syracuseStep 464755 = 697133) B697133
theorem B661393 : Blo 409770 661393 := bstep (se 2 (by rfl) ⟨248022, by rfl⟩ : syracuseStep 661393 = 496045) B496045
theorem B694163 : Blo 409770 694163 := bstep (se 1 (by rfl) ⟨520622, by rfl⟩ : syracuseStep 694163 = 1041245) B1041245
theorem B923633 : Blo 409770 923633 := bstep (se 2 (by rfl) ⟨346362, by rfl⟩ : syracuseStep 923633 = 692725) B692725
theorem B923651 : Blo 409770 923651 := bstep (se 1 (by rfl) ⟨692738, by rfl⟩ : syracuseStep 923651 = 1385477) B1385477
theorem B464899 : Blo 409770 464899 := bstep (se 1 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 464899 = 697349) B697349
theorem B694291 : Blo 409770 694291 := bstep (se 1 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 694291 = 1041437) B1041437
theorem B596003 : Blo 409770 596003 := bstep (se 1 (by rfl) ⟨447002, by rfl⟩ : syracuseStep 596003 = 894005) B894005
theorem B465043 : Blo 409770 465043 := bstep (se 1 (by rfl) ⟨348782, by rfl⟩ : syracuseStep 465043 = 697565) B697565
theorem B694433 : Blo 409770 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B923921 : Blo 409770 923921 := bstep (se 2 (by rfl) ⟨346470, by rfl⟩ : syracuseStep 923921 = 692941) B692941
theorem B694561 : Blo 409770 694561 := bstep (se 2 (by rfl) ⟨260460, by rfl⟩ : syracuseStep 694561 = 520921) B520921
theorem B923939 : Blo 409770 923939 := bstep (se 1 (by rfl) ⟨692954, by rfl⟩ : syracuseStep 923939 = 1385909) B1385909
theorem B465187 : Blo 409770 465187 := bstep (se 1 (by rfl) ⟨348890, by rfl⟩ : syracuseStep 465187 = 697781) B697781
theorem B1906993 : Blo 409770 1906993 := bstep (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) B1430245
theorem B694595 : Blo 409770 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B465331 : Blo 409770 465331 := bstep (se 1 (by rfl) ⟨348998, by rfl⟩ : syracuseStep 465331 = 697997) B697997
theorem B694723 : Blo 409770 694723 := bstep (se 1 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 694723 = 1042085) B1042085
theorem B924209 : Blo 409770 924209 := bstep (se 2 (by rfl) ⟨346578, by rfl⟩ : syracuseStep 924209 = 693157) B693157
theorem B924227 : Blo 409770 924227 := bstep (se 1 (by rfl) ⟨693170, by rfl⟩ : syracuseStep 924227 = 1386341) B1386341
theorem B465475 : Blo 409770 465475 := bstep (se 1 (by rfl) ⟨349106, by rfl⟩ : syracuseStep 465475 = 698213) B698213
theorem B4528709 : Blo 409770 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B1382993 : Blo 409770 1382993 := bstep (se 2 (by rfl) ⟨518622, by rfl⟩ : syracuseStep 1382993 = 1037245) B1037245
theorem B694865 : Blo 409770 694865 := bstep (se 2 (by rfl) ⟨260574, by rfl⟩ : syracuseStep 694865 = 521149) B521149
theorem B2005681 : Blo 409770 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B694993 : Blo 409770 694993 := bstep (se 2 (by rfl) ⟨260622, by rfl⟩ : syracuseStep 694993 = 521245) B521245
theorem B695027 : Blo 409770 695027 := bstep (se 1 (by rfl) ⟨521270, by rfl⟩ : syracuseStep 695027 = 1042541) B1042541
theorem B1973069 : Blo 409770 1973069 := bstep (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) B739901
theorem B924497 : Blo 409770 924497 := bstep (se 2 (by rfl) ⟨346686, by rfl⟩ : syracuseStep 924497 = 693373) B693373
theorem B924515 : Blo 409770 924515 := bstep (se 1 (by rfl) ⟨693386, by rfl⟩ : syracuseStep 924515 = 1386773) B1386773
theorem B695155 : Blo 409770 695155 := bstep (se 1 (by rfl) ⟨521366, by rfl⟩ : syracuseStep 695155 = 1042733) B1042733
theorem B2038733 : Blo 409770 2038733 := bstep (se 3 (by rfl) ⟨382262, by rfl⟩ : syracuseStep 2038733 = 764525) B764525
theorem B695297 : Blo 409770 695297 := bstep (se 2 (by rfl) ⟨260736, by rfl⟩ : syracuseStep 695297 = 521473) B521473
theorem B2825293 : Blo 409770 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B1383533 : Blo 409770 1383533 := bstep (se 3 (by rfl) ⟨259412, by rfl⟩ : syracuseStep 1383533 = 518825) B518825
theorem B924785 : Blo 409770 924785 := bstep (se 2 (by rfl) ⟨346794, by rfl⟩ : syracuseStep 924785 = 693589) B693589
theorem B695425 : Blo 409770 695425 := bstep (se 2 (by rfl) ⟨260784, by rfl⟩ : syracuseStep 695425 = 521569) B521569
theorem B924803 : Blo 409770 924803 := bstep (se 1 (by rfl) ⟨693602, by rfl⟩ : syracuseStep 924803 = 1387205) B1387205
theorem B1383587 : Blo 409770 1383587 := bstep (se 1 (by rfl) ⟨1037690, by rfl⟩ : syracuseStep 1383587 = 2075381) B2075381
theorem B695459 : Blo 409770 695459 := bstep (se 1 (by rfl) ⟨521594, by rfl⟩ : syracuseStep 695459 = 1043189) B1043189
theorem B2333893 : Blo 409770 2333893 := bstep (se 4 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 2333893 = 437605) B437605
theorem B695587 : Blo 409770 695587 := bstep (se 1 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 695587 = 1043381) B1043381
theorem B4693301 : Blo 409770 4693301 := bstep (se 5 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 4693301 = 439997) B439997
theorem B925073 : Blo 409770 925073 := bstep (se 2 (by rfl) ⟨346902, by rfl⟩ : syracuseStep 925073 = 693805) B693805
theorem B925091 : Blo 409770 925091 := bstep (se 1 (by rfl) ⟨693818, by rfl⟩ : syracuseStep 925091 = 1387637) B1387637
theorem B1383857 : Blo 409770 1383857 := bstep (se 2 (by rfl) ⟨518946, by rfl⟩ : syracuseStep 1383857 = 1037893) B1037893
theorem B695729 : Blo 409770 695729 := bstep (se 2 (by rfl) ⟨260898, by rfl⟩ : syracuseStep 695729 = 521797) B521797
theorem B2629169 : Blo 409770 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B695857 : Blo 409770 695857 := bstep (se 2 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 695857 = 521893) B521893
theorem B1318481 : Blo 409770 1318481 := bstep (se 2 (by rfl) ⟨494430, by rfl⟩ : syracuseStep 1318481 = 988861) B988861
theorem B695891 : Blo 409770 695891 := bstep (se 1 (by rfl) ⟨521918, by rfl⟩ : syracuseStep 695891 = 1043837) B1043837
theorem B2629219 : Blo 409770 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B925361 : Blo 409770 925361 := bstep (se 2 (by rfl) ⟨347010, by rfl⟩ : syracuseStep 925361 = 694021) B694021
theorem B925379 : Blo 409770 925379 := bstep (se 1 (by rfl) ⟨694034, by rfl⟩ : syracuseStep 925379 = 1388069) B1388069
theorem B696019 : Blo 409770 696019 := bstep (se 1 (by rfl) ⟨522014, by rfl⟩ : syracuseStep 696019 = 1044029) B1044029
theorem B1187569 : Blo 409770 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B696161 : Blo 409770 696161 := bstep (se 2 (by rfl) ⟨261060, by rfl⟩ : syracuseStep 696161 = 522121) B522121
theorem B1384397 : Blo 409770 1384397 := bstep (se 3 (by rfl) ⟨259574, by rfl⟩ : syracuseStep 1384397 = 519149) B519149
theorem B925649 : Blo 409770 925649 := bstep (se 2 (by rfl) ⟨347118, by rfl⟩ : syracuseStep 925649 = 694237) B694237
theorem B696289 : Blo 409770 696289 := bstep (se 2 (by rfl) ⟨261108, by rfl⟩ : syracuseStep 696289 = 522217) B522217
theorem B925667 : Blo 409770 925667 := bstep (se 1 (by rfl) ⟨694250, by rfl⟩ : syracuseStep 925667 = 1388501) B1388501
theorem B1384451 : Blo 409770 1384451 := bstep (se 1 (by rfl) ⟨1038338, by rfl⟩ : syracuseStep 1384451 = 2076677) B2076677
theorem B696323 : Blo 409770 696323 := bstep (se 1 (by rfl) ⟨522242, by rfl⟩ : syracuseStep 696323 = 1044485) B1044485
theorem B696451 : Blo 409770 696451 := bstep (se 1 (by rfl) ⟨522338, by rfl⟩ : syracuseStep 696451 = 1044677) B1044677
theorem B925937 : Blo 409770 925937 := bstep (se 2 (by rfl) ⟨347226, by rfl⟩ : syracuseStep 925937 = 694453) B694453
theorem B925955 : Blo 409770 925955 := bstep (se 1 (by rfl) ⟨694466, by rfl⟩ : syracuseStep 925955 = 1388933) B1388933
theorem B1319171 : Blo 409770 1319171 := bstep (se 1 (by rfl) ⟨989378, by rfl⟩ : syracuseStep 1319171 = 1978757) B1978757
theorem B1384721 : Blo 409770 1384721 := bstep (se 2 (by rfl) ⟨519270, by rfl⟩ : syracuseStep 1384721 = 1038541) B1038541
theorem B696593 : Blo 409770 696593 := bstep (se 2 (by rfl) ⟨261222, by rfl⟩ : syracuseStep 696593 = 522445) B522445
theorem B696721 : Blo 409770 696721 := bstep (se 2 (by rfl) ⟨261270, by rfl⟩ : syracuseStep 696721 = 522541) B522541
theorem B696755 : Blo 409770 696755 := bstep (se 1 (by rfl) ⟨522566, by rfl⟩ : syracuseStep 696755 = 1045133) B1045133
theorem B926225 : Blo 409770 926225 := bstep (se 2 (by rfl) ⟨347334, by rfl⟩ : syracuseStep 926225 = 694669) B694669
theorem B926243 : Blo 409770 926243 := bstep (se 1 (by rfl) ⟨694682, by rfl⟩ : syracuseStep 926243 = 1389365) B1389365
theorem B696883 : Blo 409770 696883 := bstep (se 1 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 696883 = 1045325) B1045325
theorem B697025 : Blo 409770 697025 := bstep (se 2 (by rfl) ⟨261384, by rfl⟩ : syracuseStep 697025 = 522769) B522769
theorem B1057475 : Blo 409770 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B1385261 : Blo 409770 1385261 := bstep (se 3 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 1385261 = 519473) B519473
theorem B926513 : Blo 409770 926513 := bstep (se 2 (by rfl) ⟨347442, by rfl⟩ : syracuseStep 926513 = 694885) B694885
theorem B697153 : Blo 409770 697153 := bstep (se 2 (by rfl) ⟨261432, by rfl⟩ : syracuseStep 697153 = 522865) B522865
theorem B926531 : Blo 409770 926531 := bstep (se 1 (by rfl) ⟨694898, by rfl⟩ : syracuseStep 926531 = 1389797) B1389797
theorem B1385315 : Blo 409770 1385315 := bstep (se 1 (by rfl) ⟨1038986, by rfl⟩ : syracuseStep 1385315 = 2077973) B2077973
theorem B697187 : Blo 409770 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B697315 : Blo 409770 697315 := bstep (se 1 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 697315 = 1045973) B1045973
theorem B926801 : Blo 409770 926801 := bstep (se 2 (by rfl) ⟨347550, by rfl⟩ : syracuseStep 926801 = 695101) B695101
theorem B926819 : Blo 409770 926819 := bstep (se 1 (by rfl) ⟨695114, by rfl⟩ : syracuseStep 926819 = 1390229) B1390229
theorem B1385585 : Blo 409770 1385585 := bstep (se 2 (by rfl) ⟨519594, by rfl⟩ : syracuseStep 1385585 = 1039189) B1039189
theorem B697457 : Blo 409770 697457 := bstep (se 2 (by rfl) ⟨261546, by rfl⟩ : syracuseStep 697457 = 523093) B523093
theorem B2335877 : Blo 409770 2335877 := bstep (se 4 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 2335877 = 437977) B437977
theorem B697585 : Blo 409770 697585 := bstep (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) B523189
theorem B697619 : Blo 409770 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B927089 : Blo 409770 927089 := bstep (se 2 (by rfl) ⟨347658, by rfl⟩ : syracuseStep 927089 = 695317) B695317
theorem B927107 : Blo 409770 927107 := bstep (se 1 (by rfl) ⟨695330, by rfl⟩ : syracuseStep 927107 = 1390661) B1390661
theorem B697747 : Blo 409770 697747 := bstep (se 1 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 697747 = 1046621) B1046621
theorem B697889 : Blo 409770 697889 := bstep (se 2 (by rfl) ⟨261708, by rfl⟩ : syracuseStep 697889 = 523417) B523417
theorem B501283 : Blo 409770 501283 := bstep (se 1 (by rfl) ⟨375962, by rfl⟩ : syracuseStep 501283 = 751925) B751925
theorem B1386125 : Blo 409770 1386125 := bstep (se 3 (by rfl) ⟨259898, by rfl⟩ : syracuseStep 1386125 = 519797) B519797
theorem B927377 : Blo 409770 927377 := bstep (se 2 (by rfl) ⟨347766, by rfl⟩ : syracuseStep 927377 = 695533) B695533
theorem B698017 : Blo 409770 698017 := bstep (se 2 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 698017 = 523513) B523513
theorem B927395 : Blo 409770 927395 := bstep (se 1 (by rfl) ⟨695546, by rfl⟩ : syracuseStep 927395 = 1391093) B1391093
theorem B1386179 : Blo 409770 1386179 := bstep (se 1 (by rfl) ⟨1039634, by rfl⟩ : syracuseStep 1386179 = 2079269) B2079269
theorem B698051 : Blo 409770 698051 := bstep (se 1 (by rfl) ⟨523538, by rfl⟩ : syracuseStep 698051 = 1047077) B1047077
theorem B3352261 : Blo 409770 3352261 := bstep (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) B628549
theorem B698179 : Blo 409770 698179 := bstep (se 1 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 698179 = 1047269) B1047269
theorem B927665 : Blo 409770 927665 := bstep (se 2 (by rfl) ⟨347874, by rfl⟩ : syracuseStep 927665 = 695749) B695749
theorem B927683 : Blo 409770 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B2631629 : Blo 409770 2631629 := bstep (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) B986861
theorem B1386449 : Blo 409770 1386449 := bstep (se 2 (by rfl) ⟨519918, by rfl⟩ : syracuseStep 1386449 = 1039837) B1039837
theorem B1320941 : Blo 409770 1320941 := bstep (se 3 (by rfl) ⟨247676, by rfl⟩ : syracuseStep 1320941 = 495353) B495353
theorem B1321069 : Blo 409770 1321069 := bstep (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) B495401
theorem B927953 : Blo 409770 927953 := bstep (se 2 (by rfl) ⟨347982, by rfl⟩ : syracuseStep 927953 = 695965) B695965
theorem B927971 : Blo 409770 927971 := bstep (se 1 (by rfl) ⟨695978, by rfl⟩ : syracuseStep 927971 = 1391957) B1391957
theorem B1321325 : Blo 409770 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B2075057 : Blo 409770 2075057 := bstep (se 2 (by rfl) ⟨778146, by rfl⟩ : syracuseStep 2075057 = 1556293) B1556293
theorem B1386989 : Blo 409770 1386989 := bstep (se 3 (by rfl) ⟨260060, by rfl⟩ : syracuseStep 1386989 = 520121) B520121
theorem B928241 : Blo 409770 928241 := bstep (se 2 (by rfl) ⟨348090, by rfl⟩ : syracuseStep 928241 = 696181) B696181
theorem B928259 : Blo 409770 928259 := bstep (se 1 (by rfl) ⟨696194, by rfl⟩ : syracuseStep 928259 = 1392389) B1392389
theorem B1387043 : Blo 409770 1387043 := bstep (se 1 (by rfl) ⟨1040282, by rfl⟩ : syracuseStep 1387043 = 2080565) B2080565
theorem B1256003 : Blo 409770 1256003 := bstep (se 1 (by rfl) ⟨942002, by rfl⟩ : syracuseStep 1256003 = 1884005) B1884005
theorem B3943025 : Blo 409770 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B11250373 : Blo 409770 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B928529 : Blo 409770 928529 := bstep (se 2 (by rfl) ⟨348198, by rfl⟩ : syracuseStep 928529 = 696397) B696397
theorem B928547 : Blo 409770 928547 := bstep (se 1 (by rfl) ⟨696410, by rfl⟩ : syracuseStep 928547 = 1392821) B1392821
theorem B1387313 : Blo 409770 1387313 := bstep (se 2 (by rfl) ⟨520242, by rfl⟩ : syracuseStep 1387313 = 1040485) B1040485
theorem B1256465 : Blo 409770 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B928817 : Blo 409770 928817 := bstep (se 2 (by rfl) ⟨348306, by rfl⟩ : syracuseStep 928817 = 696613) B696613
theorem B535619 : Blo 409770 535619 := bstep (se 1 (by rfl) ⟨401714, by rfl⟩ : syracuseStep 535619 = 803429) B803429
theorem B928835 : Blo 409770 928835 := bstep (se 1 (by rfl) ⟨696626, by rfl⟩ : syracuseStep 928835 = 1393253) B1393253
theorem B2829509 : Blo 409770 2829509 := bstep (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) B530533
theorem B3124493 : Blo 409770 3124493 := bstep (se 3 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 3124493 = 1171685) B1171685
theorem B1387853 : Blo 409770 1387853 := bstep (se 3 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 1387853 = 520445) B520445
theorem B929105 : Blo 409770 929105 := bstep (se 2 (by rfl) ⟨348414, by rfl⟩ : syracuseStep 929105 = 696829) B696829
theorem B929123 : Blo 409770 929123 := bstep (se 1 (by rfl) ⟨696842, by rfl⟩ : syracuseStep 929123 = 1393685) B1393685
theorem B1387907 : Blo 409770 1387907 := bstep (se 1 (by rfl) ⟨1040930, by rfl⟩ : syracuseStep 1387907 = 2081861) B2081861
theorem B5254541 : Blo 409770 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B2502029 : Blo 409770 2502029 := bstep (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) B938261
theorem B2010673 : Blo 409770 2010673 := bstep (se 2 (by rfl) ⟨754002, by rfl⟩ : syracuseStep 2010673 = 1508005) B1508005
theorem B831043 : Blo 409770 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B4763249 : Blo 409770 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B929393 : Blo 409770 929393 := bstep (se 2 (by rfl) ⟨348522, by rfl⟩ : syracuseStep 929393 = 697045) B697045
theorem B929411 : Blo 409770 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B1388177 : Blo 409770 1388177 := bstep (se 2 (by rfl) ⟨520566, by rfl⟩ : syracuseStep 1388177 = 1041133) B1041133
theorem B2076515 : Blo 409770 2076515 := bstep (se 1 (by rfl) ⟨1557386, by rfl⟩ : syracuseStep 2076515 = 3114773) B3114773
theorem B1322851 : Blo 409770 1322851 := bstep (se 1 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 1322851 = 1984277) B1984277
theorem B1257329 : Blo 409770 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B929681 : Blo 409770 929681 := bstep (se 2 (by rfl) ⟨348630, by rfl⟩ : syracuseStep 929681 = 697261) B697261
theorem B929699 : Blo 409770 929699 := bstep (se 1 (by rfl) ⟨697274, by rfl⟩ : syracuseStep 929699 = 1394549) B1394549
theorem B1388717 : Blo 409770 1388717 := bstep (se 3 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 1388717 = 520769) B520769
theorem B929969 : Blo 409770 929969 := bstep (se 2 (by rfl) ⟨348738, by rfl⟩ : syracuseStep 929969 = 697477) B697477
theorem B929987 : Blo 409770 929987 := bstep (se 1 (by rfl) ⟨697490, by rfl⟩ : syracuseStep 929987 = 1394981) B1394981
theorem B1388771 : Blo 409770 1388771 := bstep (se 1 (by rfl) ⟨1041578, by rfl⟩ : syracuseStep 1388771 = 2083157) B2083157
theorem B1257731 : Blo 409770 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B2961677 : Blo 409770 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B930257 : Blo 409770 930257 := bstep (se 2 (by rfl) ⟨348846, by rfl⟩ : syracuseStep 930257 = 697693) B697693
theorem B930275 : Blo 409770 930275 := bstep (se 1 (by rfl) ⟨697706, by rfl⟩ : syracuseStep 930275 = 1395413) B1395413
theorem B1389041 : Blo 409770 1389041 := bstep (se 2 (by rfl) ⟨520890, by rfl⟩ : syracuseStep 1389041 = 1041781) B1041781
theorem B2667043 : Blo 409770 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B2077325 : Blo 409770 2077325 := bstep (se 3 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 2077325 = 778997) B778997
theorem B10039949 : Blo 409770 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B5026445 : Blo 409770 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B832145 : Blo 409770 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B930545 : Blo 409770 930545 := bstep (se 2 (by rfl) ⟨348954, by rfl⟩ : syracuseStep 930545 = 697909) B697909
theorem B930563 : Blo 409770 930563 := bstep (se 1 (by rfl) ⟨697922, by rfl⟩ : syracuseStep 930563 = 1395845) B1395845
theorem B668483 : Blo 409770 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B668497 : Blo 409770 668497 := bstep (se 2 (by rfl) ⟨250686, by rfl⟩ : syracuseStep 668497 = 501373) B501373
theorem B439139 : Blo 409770 439139 := bstep (se 1 (by rfl) ⟨329354, by rfl⟩ : syracuseStep 439139 = 658709) B658709
theorem B2569073 : Blo 409770 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B2339725 : Blo 409770 2339725 := bstep (se 3 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 2339725 = 877397) B877397
theorem B1389581 : Blo 409770 1389581 := bstep (se 3 (by rfl) ⟨260546, by rfl⟩ : syracuseStep 1389581 = 521093) B521093
theorem B930833 : Blo 409770 930833 := bstep (se 2 (by rfl) ⟨349062, by rfl⟩ : syracuseStep 930833 = 698125) B698125
theorem B930851 : Blo 409770 930851 := bstep (se 1 (by rfl) ⟨698138, by rfl⟩ : syracuseStep 930851 = 1396277) B1396277
theorem B701507 : Blo 409770 701507 := bstep (se 1 (by rfl) ⟨526130, by rfl⟩ : syracuseStep 701507 = 1052261) B1052261
theorem B1389635 : Blo 409770 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B832771 : Blo 409770 832771 := bstep (se 1 (by rfl) ⟨624578, by rfl⟩ : syracuseStep 832771 = 1249157) B1249157
theorem B1389905 : Blo 409770 1389905 := bstep (se 2 (by rfl) ⟨521214, by rfl⟩ : syracuseStep 1389905 = 1042429) B1042429
theorem B3945827 : Blo 409770 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B1324451 : Blo 409770 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B440083 : Blo 409770 440083 := bstep (se 1 (by rfl) ⟨330062, by rfl⟩ : syracuseStep 440083 = 660125) B660125
theorem B1390445 : Blo 409770 1390445 := bstep (se 3 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 1390445 = 521417) B521417
theorem B2504611 : Blo 409770 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B1390499 : Blo 409770 1390499 := bstep (se 1 (by rfl) ⟨1042874, by rfl⟩ : syracuseStep 1390499 = 2085749) B2085749
theorem B3127409 : Blo 409770 3127409 := bstep (se 2 (by rfl) ⟨1172778, by rfl⟩ : syracuseStep 3127409 = 2345557) B2345557
theorem B669809 : Blo 409770 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B1128593 : Blo 409770 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B1390769 : Blo 409770 1390769 := bstep (se 2 (by rfl) ⟨521538, by rfl⟩ : syracuseStep 1390769 = 1043077) B1043077
theorem B833809 : Blo 409770 833809 := bstep (se 2 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 833809 = 625357) B625357
theorem B1325425 : Blo 409770 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B1751651 : Blo 409770 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B1391309 : Blo 409770 1391309 := bstep (se 3 (by rfl) ⟨260870, by rfl⟩ : syracuseStep 1391309 = 521741) B521741
theorem B1391363 : Blo 409770 1391363 := bstep (se 1 (by rfl) ⟨1043522, by rfl⟩ : syracuseStep 1391363 = 2087045) B2087045
theorem B2341709 : Blo 409770 2341709 := bstep (se 3 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 2341709 = 878141) B878141
theorem B441347 : Blo 409770 441347 := bstep (se 1 (by rfl) ⟨331010, by rfl⟩ : syracuseStep 441347 = 662021) B662021
theorem B1391633 : Blo 409770 1391633 := bstep (se 2 (by rfl) ⟨521862, by rfl⟩ : syracuseStep 1391633 = 1043725) B1043725
theorem B4668515 : Blo 409770 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B2080241 : Blo 409770 2080241 := bstep (se 2 (by rfl) ⟨780090, by rfl⟩ : syracuseStep 2080241 = 1560181) B1560181
theorem B1392173 : Blo 409770 1392173 := bstep (se 3 (by rfl) ⟨261032, by rfl⟩ : syracuseStep 1392173 = 522065) B522065
theorem B1392227 : Blo 409770 1392227 := bstep (se 1 (by rfl) ⟨1044170, by rfl⟩ : syracuseStep 1392227 = 2088341) B2088341
theorem B1556081 : Blo 409770 1556081 := bstep (se 2 (by rfl) ⟨583530, by rfl⟩ : syracuseStep 1556081 = 1167061) B1167061
theorem B2342641 : Blo 409770 2342641 := bstep (se 2 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 2342641 = 1756981) B1756981
theorem B1392497 : Blo 409770 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B409779 : Blo 409770 409779 := bstep (se 1 (by rfl) ⟨307334, by rfl⟩ : syracuseStep 409779 = 614669) B614669
theorem B409795 : Blo 409770 409795 := bstep (se 1 (by rfl) ⟨307346, by rfl⟩ : syracuseStep 409795 = 614693) B614693
theorem B409811 : Blo 409770 409811 := bstep (se 1 (by rfl) ⟨307358, by rfl⟩ : syracuseStep 409811 = 614717) B614717
theorem B409827 : Blo 409770 409827 := bstep (se 1 (by rfl) ⟨307370, by rfl⟩ : syracuseStep 409827 = 614741) B614741
theorem B409843 : Blo 409770 409843 := bstep (se 1 (by rfl) ⟨307382, by rfl⟩ : syracuseStep 409843 = 614765) B614765
theorem B409859 : Blo 409770 409859 := bstep (se 1 (by rfl) ⟨307394, by rfl⟩ : syracuseStep 409859 = 614789) B614789
theorem B409875 : Blo 409770 409875 := bstep (se 1 (by rfl) ⟨307406, by rfl⟩ : syracuseStep 409875 = 614813) B614813
theorem B409891 : Blo 409770 409891 := bstep (se 1 (by rfl) ⟨307418, by rfl⟩ : syracuseStep 409891 = 614837) B614837
theorem B2638115 : Blo 409770 2638115 := bstep (se 1 (by rfl) ⟨1978586, by rfl⟩ : syracuseStep 2638115 = 3957173) B3957173
theorem B1982755 : Blo 409770 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B409907 : Blo 409770 409907 := bstep (se 1 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 409907 = 614861) B614861
theorem B409923 : Blo 409770 409923 := bstep (se 1 (by rfl) ⟨307442, by rfl⟩ : syracuseStep 409923 = 614885) B614885
theorem B999761 : Blo 409770 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B409939 : Blo 409770 409939 := bstep (se 1 (by rfl) ⟨307454, by rfl⟩ : syracuseStep 409939 = 614909) B614909
theorem B409955 : Blo 409770 409955 := bstep (se 1 (by rfl) ⟨307466, by rfl⟩ : syracuseStep 409955 = 614933) B614933
theorem B409971 : Blo 409770 409971 := bstep (se 1 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 409971 = 614957) B614957
theorem B409987 : Blo 409770 409987 := bstep (se 1 (by rfl) ⟨307490, by rfl⟩ : syracuseStep 409987 = 614981) B614981
theorem B1393037 : Blo 409770 1393037 := bstep (se 3 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 1393037 = 522389) B522389
theorem B410003 : Blo 409770 410003 := bstep (se 1 (by rfl) ⟨307502, by rfl⟩ : syracuseStep 410003 = 615005) B615005
theorem B410019 : Blo 409770 410019 := bstep (se 1 (by rfl) ⟨307514, by rfl⟩ : syracuseStep 410019 = 615029) B615029
theorem B410035 : Blo 409770 410035 := bstep (se 1 (by rfl) ⟨307526, by rfl⟩ : syracuseStep 410035 = 615053) B615053
theorem B410051 : Blo 409770 410051 := bstep (se 1 (by rfl) ⟨307538, by rfl⟩ : syracuseStep 410051 = 615077) B615077
theorem B1393091 : Blo 409770 1393091 := bstep (se 1 (by rfl) ⟨1044818, by rfl⟩ : syracuseStep 1393091 = 2089637) B2089637
theorem B410067 : Blo 409770 410067 := bstep (se 1 (by rfl) ⟨307550, by rfl⟩ : syracuseStep 410067 = 615101) B615101
theorem B410083 : Blo 409770 410083 := bstep (se 1 (by rfl) ⟨307562, by rfl⟩ : syracuseStep 410083 = 615125) B615125
theorem B410099 : Blo 409770 410099 := bstep (se 1 (by rfl) ⟨307574, by rfl⟩ : syracuseStep 410099 = 615149) B615149
theorem B410115 : Blo 409770 410115 := bstep (se 1 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 410115 = 615173) B615173
theorem B410131 : Blo 409770 410131 := bstep (se 1 (by rfl) ⟨307598, by rfl⟩ : syracuseStep 410131 = 615197) B615197
theorem B410147 : Blo 409770 410147 := bstep (se 1 (by rfl) ⟨307610, by rfl⟩ : syracuseStep 410147 = 615221) B615221
theorem B410163 : Blo 409770 410163 := bstep (se 1 (by rfl) ⟨307622, by rfl⟩ : syracuseStep 410163 = 615245) B615245
theorem B410179 : Blo 409770 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B410195 : Blo 409770 410195 := bstep (se 1 (by rfl) ⟨307646, by rfl⟩ : syracuseStep 410195 = 615293) B615293
theorem B410211 : Blo 409770 410211 := bstep (se 1 (by rfl) ⟨307658, by rfl⟩ : syracuseStep 410211 = 615317) B615317
theorem B410227 : Blo 409770 410227 := bstep (se 1 (by rfl) ⟨307670, by rfl⟩ : syracuseStep 410227 = 615341) B615341
theorem B410243 : Blo 409770 410243 := bstep (se 1 (by rfl) ⟨307682, by rfl⟩ : syracuseStep 410243 = 615365) B615365
theorem B410259 : Blo 409770 410259 := bstep (se 1 (by rfl) ⟨307694, by rfl⟩ : syracuseStep 410259 = 615389) B615389
theorem B410275 : Blo 409770 410275 := bstep (se 1 (by rfl) ⟨307706, by rfl⟩ : syracuseStep 410275 = 615413) B615413
theorem B410291 : Blo 409770 410291 := bstep (se 1 (by rfl) ⟨307718, by rfl⟩ : syracuseStep 410291 = 615437) B615437
theorem B705203 : Blo 409770 705203 := bstep (se 1 (by rfl) ⟨528902, by rfl⟩ : syracuseStep 705203 = 1057805) B1057805
theorem B410307 : Blo 409770 410307 := bstep (se 1 (by rfl) ⟨307730, by rfl⟩ : syracuseStep 410307 = 615461) B615461
theorem B1393361 : Blo 409770 1393361 := bstep (se 2 (by rfl) ⟨522510, by rfl⟩ : syracuseStep 1393361 = 1045021) B1045021
theorem B410323 : Blo 409770 410323 := bstep (se 1 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 410323 = 615485) B615485
theorem B410339 : Blo 409770 410339 := bstep (se 1 (by rfl) ⟨307754, by rfl⟩ : syracuseStep 410339 = 615509) B615509
theorem B1983217 : Blo 409770 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B410355 : Blo 409770 410355 := bstep (se 1 (by rfl) ⟨307766, by rfl⟩ : syracuseStep 410355 = 615533) B615533
theorem B410371 : Blo 409770 410371 := bstep (se 1 (by rfl) ⟨307778, by rfl⟩ : syracuseStep 410371 = 615557) B615557
theorem B410387 : Blo 409770 410387 := bstep (se 1 (by rfl) ⟨307790, by rfl⟩ : syracuseStep 410387 = 615581) B615581
theorem B410403 : Blo 409770 410403 := bstep (se 1 (by rfl) ⟨307802, by rfl⟩ : syracuseStep 410403 = 615605) B615605
theorem B410419 : Blo 409770 410419 := bstep (se 1 (by rfl) ⟨307814, by rfl⟩ : syracuseStep 410419 = 615629) B615629
theorem B410435 : Blo 409770 410435 := bstep (se 1 (by rfl) ⟨307826, by rfl⟩ : syracuseStep 410435 = 615653) B615653
theorem B410451 : Blo 409770 410451 := bstep (se 1 (by rfl) ⟨307838, by rfl⟩ : syracuseStep 410451 = 615677) B615677
theorem B410467 : Blo 409770 410467 := bstep (se 1 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 410467 = 615701) B615701
theorem B410483 : Blo 409770 410483 := bstep (se 1 (by rfl) ⟨307862, by rfl⟩ : syracuseStep 410483 = 615725) B615725
theorem B410499 : Blo 409770 410499 := bstep (se 1 (by rfl) ⟨307874, by rfl⟩ : syracuseStep 410499 = 615749) B615749
theorem B410515 : Blo 409770 410515 := bstep (se 1 (by rfl) ⟨307886, by rfl⟩ : syracuseStep 410515 = 615773) B615773
theorem B410531 : Blo 409770 410531 := bstep (se 1 (by rfl) ⟨307898, by rfl⟩ : syracuseStep 410531 = 615797) B615797
theorem B2081699 : Blo 409770 2081699 := bstep (se 1 (by rfl) ⟨1561274, by rfl⟩ : syracuseStep 2081699 = 3122549) B3122549
theorem B410547 : Blo 409770 410547 := bstep (se 1 (by rfl) ⟨307910, by rfl⟩ : syracuseStep 410547 = 615821) B615821
theorem B410563 : Blo 409770 410563 := bstep (se 1 (by rfl) ⟨307922, by rfl⟩ : syracuseStep 410563 = 615845) B615845
theorem B12633029 : Blo 409770 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B410579 : Blo 409770 410579 := bstep (se 1 (by rfl) ⟨307934, by rfl⟩ : syracuseStep 410579 = 615869) B615869
theorem B410595 : Blo 409770 410595 := bstep (se 1 (by rfl) ⟨307946, by rfl⟩ : syracuseStep 410595 = 615893) B615893
theorem B410611 : Blo 409770 410611 := bstep (se 1 (by rfl) ⟨307958, by rfl⟩ : syracuseStep 410611 = 615917) B615917
theorem B410627 : Blo 409770 410627 := bstep (se 1 (by rfl) ⟨307970, by rfl⟩ : syracuseStep 410627 = 615941) B615941
theorem B410643 : Blo 409770 410643 := bstep (se 1 (by rfl) ⟨307982, by rfl⟩ : syracuseStep 410643 = 615965) B615965
theorem B1557539 : Blo 409770 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B410659 : Blo 409770 410659 := bstep (se 1 (by rfl) ⟨307994, by rfl⟩ : syracuseStep 410659 = 615989) B615989
theorem B410675 : Blo 409770 410675 := bstep (se 1 (by rfl) ⟨308006, by rfl⟩ : syracuseStep 410675 = 616013) B616013
theorem B410691 : Blo 409770 410691 := bstep (se 1 (by rfl) ⟨308018, by rfl⟩ : syracuseStep 410691 = 616037) B616037
theorem B410707 : Blo 409770 410707 := bstep (se 1 (by rfl) ⟨308030, by rfl⟩ : syracuseStep 410707 = 616061) B616061
theorem B410723 : Blo 409770 410723 := bstep (se 1 (by rfl) ⟨308042, by rfl⟩ : syracuseStep 410723 = 616085) B616085
theorem B410739 : Blo 409770 410739 := bstep (se 1 (by rfl) ⟨308054, by rfl⟩ : syracuseStep 410739 = 616109) B616109
theorem B410755 : Blo 409770 410755 := bstep (se 1 (by rfl) ⟨308066, by rfl⟩ : syracuseStep 410755 = 616133) B616133
theorem B410771 : Blo 409770 410771 := bstep (se 1 (by rfl) ⟨308078, by rfl⟩ : syracuseStep 410771 = 616157) B616157
theorem B410787 : Blo 409770 410787 := bstep (se 1 (by rfl) ⟨308090, by rfl⟩ : syracuseStep 410787 = 616181) B616181
theorem B2344099 : Blo 409770 2344099 := bstep (se 1 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 2344099 = 3516149) B3516149
theorem B410803 : Blo 409770 410803 := bstep (se 1 (by rfl) ⟨308102, by rfl⟩ : syracuseStep 410803 = 616205) B616205
theorem B410819 : Blo 409770 410819 := bstep (se 1 (by rfl) ⟨308114, by rfl⟩ : syracuseStep 410819 = 616229) B616229
theorem B410835 : Blo 409770 410835 := bstep (se 1 (by rfl) ⟨308126, by rfl⟩ : syracuseStep 410835 = 616253) B616253
theorem B410851 : Blo 409770 410851 := bstep (se 1 (by rfl) ⟨308138, by rfl⟩ : syracuseStep 410851 = 616277) B616277
theorem B1393901 : Blo 409770 1393901 := bstep (se 3 (by rfl) ⟨261356, by rfl⟩ : syracuseStep 1393901 = 522713) B522713
theorem B410867 : Blo 409770 410867 := bstep (se 1 (by rfl) ⟨308150, by rfl⟩ : syracuseStep 410867 = 616301) B616301
theorem B410883 : Blo 409770 410883 := bstep (se 1 (by rfl) ⟨308162, by rfl⟩ : syracuseStep 410883 = 616325) B616325
theorem B410899 : Blo 409770 410899 := bstep (se 1 (by rfl) ⟨308174, by rfl⟩ : syracuseStep 410899 = 616349) B616349
theorem B410915 : Blo 409770 410915 := bstep (se 1 (by rfl) ⟨308186, by rfl⟩ : syracuseStep 410915 = 616373) B616373
theorem B1393955 : Blo 409770 1393955 := bstep (se 1 (by rfl) ⟨1045466, by rfl⟩ : syracuseStep 1393955 = 2090933) B2090933
theorem B1361197 : Blo 409770 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B410931 : Blo 409770 410931 := bstep (se 1 (by rfl) ⟨308198, by rfl⟩ : syracuseStep 410931 = 616397) B616397
theorem B410947 : Blo 409770 410947 := bstep (se 1 (by rfl) ⟨308210, by rfl⟩ : syracuseStep 410947 = 616421) B616421
theorem B410963 : Blo 409770 410963 := bstep (se 1 (by rfl) ⟨308222, by rfl⟩ : syracuseStep 410963 = 616445) B616445
theorem B410979 : Blo 409770 410979 := bstep (se 1 (by rfl) ⟨308234, by rfl⟩ : syracuseStep 410979 = 616469) B616469
theorem B410995 : Blo 409770 410995 := bstep (se 1 (by rfl) ⟨308246, by rfl⟩ : syracuseStep 410995 = 616493) B616493
theorem B411011 : Blo 409770 411011 := bstep (se 1 (by rfl) ⟨308258, by rfl⟩ : syracuseStep 411011 = 616517) B616517
theorem B836995 : Blo 409770 836995 := bstep (se 1 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 836995 = 1255493) B1255493
theorem B411027 : Blo 409770 411027 := bstep (se 1 (by rfl) ⟨308270, by rfl⟩ : syracuseStep 411027 = 616541) B616541
theorem B411043 : Blo 409770 411043 := bstep (se 1 (by rfl) ⟨308282, by rfl⟩ : syracuseStep 411043 = 616565) B616565
theorem B411059 : Blo 409770 411059 := bstep (se 1 (by rfl) ⟨308294, by rfl⟩ : syracuseStep 411059 = 616589) B616589
theorem B411075 : Blo 409770 411075 := bstep (se 1 (by rfl) ⟨308306, by rfl⟩ : syracuseStep 411075 = 616613) B616613
theorem B411091 : Blo 409770 411091 := bstep (se 1 (by rfl) ⟨308318, by rfl⟩ : syracuseStep 411091 = 616637) B616637
theorem B411107 : Blo 409770 411107 := bstep (se 1 (by rfl) ⟨308330, by rfl⟩ : syracuseStep 411107 = 616661) B616661
theorem B411123 : Blo 409770 411123 := bstep (se 1 (by rfl) ⟨308342, by rfl⟩ : syracuseStep 411123 = 616685) B616685
theorem B411139 : Blo 409770 411139 := bstep (se 1 (by rfl) ⟨308354, by rfl⟩ : syracuseStep 411139 = 616709) B616709
theorem B411155 : Blo 409770 411155 := bstep (se 1 (by rfl) ⟨308366, by rfl⟩ : syracuseStep 411155 = 616733) B616733
theorem B411171 : Blo 409770 411171 := bstep (se 1 (by rfl) ⟨308378, by rfl⟩ : syracuseStep 411171 = 616757) B616757
theorem B1394225 : Blo 409770 1394225 := bstep (se 2 (by rfl) ⟨522834, by rfl⟩ : syracuseStep 1394225 = 1045669) B1045669
theorem B411187 : Blo 409770 411187 := bstep (se 1 (by rfl) ⟨308390, by rfl⟩ : syracuseStep 411187 = 616781) B616781
theorem B411203 : Blo 409770 411203 := bstep (se 1 (by rfl) ⟨308402, by rfl⟩ : syracuseStep 411203 = 616805) B616805
theorem B411219 : Blo 409770 411219 := bstep (se 1 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 411219 = 616829) B616829
theorem B411235 : Blo 409770 411235 := bstep (se 1 (by rfl) ⟨308426, by rfl⟩ : syracuseStep 411235 = 616853) B616853
theorem B411251 : Blo 409770 411251 := bstep (se 1 (by rfl) ⟨308438, by rfl⟩ : syracuseStep 411251 = 616877) B616877
theorem B411267 : Blo 409770 411267 := bstep (se 1 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 411267 = 616901) B616901
theorem B411283 : Blo 409770 411283 := bstep (se 1 (by rfl) ⟨308462, by rfl⟩ : syracuseStep 411283 = 616925) B616925
theorem B411299 : Blo 409770 411299 := bstep (se 1 (by rfl) ⟨308474, by rfl⟩ : syracuseStep 411299 = 616949) B616949
theorem B2344625 : Blo 409770 2344625 := bstep (se 2 (by rfl) ⟨879234, by rfl⟩ : syracuseStep 2344625 = 1758469) B1758469
theorem B411315 : Blo 409770 411315 := bstep (se 1 (by rfl) ⟨308486, by rfl⟩ : syracuseStep 411315 = 616973) B616973
theorem B411331 : Blo 409770 411331 := bstep (se 1 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 411331 = 616997) B616997
theorem B2082509 : Blo 409770 2082509 := bstep (se 3 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 2082509 = 780941) B780941
theorem B411347 : Blo 409770 411347 := bstep (se 1 (by rfl) ⟨308510, by rfl⟩ : syracuseStep 411347 = 617021) B617021
theorem B411363 : Blo 409770 411363 := bstep (se 1 (by rfl) ⟨308522, by rfl⟩ : syracuseStep 411363 = 617045) B617045
theorem B411379 : Blo 409770 411379 := bstep (se 1 (by rfl) ⟨308534, by rfl⟩ : syracuseStep 411379 = 617069) B617069
theorem B411395 : Blo 409770 411395 := bstep (se 1 (by rfl) ⟨308546, by rfl⟩ : syracuseStep 411395 = 617093) B617093
theorem B411411 : Blo 409770 411411 := bstep (se 1 (by rfl) ⟨308558, by rfl⟩ : syracuseStep 411411 = 617117) B617117
theorem B411427 : Blo 409770 411427 := bstep (se 1 (by rfl) ⟨308570, by rfl⟩ : syracuseStep 411427 = 617141) B617141
theorem B411443 : Blo 409770 411443 := bstep (se 1 (by rfl) ⟨308582, by rfl⟩ : syracuseStep 411443 = 617165) B617165
theorem B411459 : Blo 409770 411459 := bstep (se 1 (by rfl) ⟨308594, by rfl⟩ : syracuseStep 411459 = 617189) B617189
theorem B411475 : Blo 409770 411475 := bstep (se 1 (by rfl) ⟨308606, by rfl⟩ : syracuseStep 411475 = 617213) B617213
theorem B411491 : Blo 409770 411491 := bstep (se 1 (by rfl) ⟨308618, by rfl⟩ : syracuseStep 411491 = 617237) B617237
theorem B411507 : Blo 409770 411507 := bstep (se 1 (by rfl) ⟨308630, by rfl⟩ : syracuseStep 411507 = 617261) B617261
theorem B411523 : Blo 409770 411523 := bstep (se 1 (by rfl) ⟨308642, by rfl⟩ : syracuseStep 411523 = 617285) B617285
theorem B411539 : Blo 409770 411539 := bstep (se 1 (by rfl) ⟨308654, by rfl⟩ : syracuseStep 411539 = 617309) B617309
theorem B411555 : Blo 409770 411555 := bstep (se 1 (by rfl) ⟨308666, by rfl⟩ : syracuseStep 411555 = 617333) B617333
theorem B411571 : Blo 409770 411571 := bstep (se 1 (by rfl) ⟨308678, by rfl⟩ : syracuseStep 411571 = 617357) B617357
theorem B411587 : Blo 409770 411587 := bstep (se 1 (by rfl) ⟨308690, by rfl⟩ : syracuseStep 411587 = 617381) B617381
theorem B411603 : Blo 409770 411603 := bstep (se 1 (by rfl) ⟨308702, by rfl⟩ : syracuseStep 411603 = 617405) B617405
theorem B411619 : Blo 409770 411619 := bstep (se 1 (by rfl) ⟨308714, by rfl⟩ : syracuseStep 411619 = 617429) B617429
theorem B411635 : Blo 409770 411635 := bstep (se 1 (by rfl) ⟨308726, by rfl⟩ : syracuseStep 411635 = 617453) B617453
theorem B411651 : Blo 409770 411651 := bstep (se 1 (by rfl) ⟨308738, by rfl⟩ : syracuseStep 411651 = 617477) B617477
theorem B1558541 : Blo 409770 1558541 := bstep (se 3 (by rfl) ⟨292226, by rfl⟩ : syracuseStep 1558541 = 584453) B584453
theorem B411667 : Blo 409770 411667 := bstep (se 1 (by rfl) ⟨308750, by rfl⟩ : syracuseStep 411667 = 617501) B617501
theorem B411683 : Blo 409770 411683 := bstep (se 1 (by rfl) ⟨308762, by rfl⟩ : syracuseStep 411683 = 617525) B617525
theorem B411699 : Blo 409770 411699 := bstep (se 1 (by rfl) ⟨308774, by rfl⟩ : syracuseStep 411699 = 617549) B617549
theorem B411715 : Blo 409770 411715 := bstep (se 1 (by rfl) ⟨308786, by rfl⟩ : syracuseStep 411715 = 617573) B617573
theorem B1394765 : Blo 409770 1394765 := bstep (se 3 (by rfl) ⟨261518, by rfl⟩ : syracuseStep 1394765 = 523037) B523037
theorem B411731 : Blo 409770 411731 := bstep (se 1 (by rfl) ⟨308798, by rfl⟩ : syracuseStep 411731 = 617597) B617597
theorem B411747 : Blo 409770 411747 := bstep (se 1 (by rfl) ⟨308810, by rfl⟩ : syracuseStep 411747 = 617621) B617621
theorem B411763 : Blo 409770 411763 := bstep (se 1 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 411763 = 617645) B617645
theorem B411779 : Blo 409770 411779 := bstep (se 1 (by rfl) ⟨308834, by rfl⟩ : syracuseStep 411779 = 617669) B617669
theorem B1394819 : Blo 409770 1394819 := bstep (se 1 (by rfl) ⟨1046114, by rfl⟩ : syracuseStep 1394819 = 2092229) B2092229
theorem B411795 : Blo 409770 411795 := bstep (se 1 (by rfl) ⟨308846, by rfl⟩ : syracuseStep 411795 = 617693) B617693
theorem B411811 : Blo 409770 411811 := bstep (se 1 (by rfl) ⟨308858, by rfl⟩ : syracuseStep 411811 = 617717) B617717
theorem B411827 : Blo 409770 411827 := bstep (se 1 (by rfl) ⟨308870, by rfl⟩ : syracuseStep 411827 = 617741) B617741
theorem B411843 : Blo 409770 411843 := bstep (se 1 (by rfl) ⟨308882, by rfl⟩ : syracuseStep 411843 = 617765) B617765
theorem B1755341 : Blo 409770 1755341 := bstep (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) B658253
theorem B411859 : Blo 409770 411859 := bstep (se 1 (by rfl) ⟨308894, by rfl⟩ : syracuseStep 411859 = 617789) B617789
theorem B411875 : Blo 409770 411875 := bstep (se 1 (by rfl) ⟨308906, by rfl⟩ : syracuseStep 411875 = 617813) B617813
theorem B1755377 : Blo 409770 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B411891 : Blo 409770 411891 := bstep (se 1 (by rfl) ⟨308918, by rfl⟩ : syracuseStep 411891 = 617837) B617837
theorem B706817 : Blo 409770 706817 := bstep (se 2 (by rfl) ⟨265056, by rfl⟩ : syracuseStep 706817 = 530113) B530113
theorem B411907 : Blo 409770 411907 := bstep (se 1 (by rfl) ⟨308930, by rfl⟩ : syracuseStep 411907 = 617861) B617861
theorem B411923 : Blo 409770 411923 := bstep (se 1 (by rfl) ⟨308942, by rfl⟩ : syracuseStep 411923 = 617885) B617885
theorem B411939 : Blo 409770 411939 := bstep (se 1 (by rfl) ⟨308954, by rfl⟩ : syracuseStep 411939 = 617909) B617909
theorem B411955 : Blo 409770 411955 := bstep (se 1 (by rfl) ⟨308966, by rfl⟩ : syracuseStep 411955 = 617933) B617933
theorem B411971 : Blo 409770 411971 := bstep (se 1 (by rfl) ⟨308978, by rfl⟩ : syracuseStep 411971 = 617957) B617957
theorem B411987 : Blo 409770 411987 := bstep (se 1 (by rfl) ⟨308990, by rfl⟩ : syracuseStep 411987 = 617981) B617981
theorem B412003 : Blo 409770 412003 := bstep (se 1 (by rfl) ⟨309002, by rfl⟩ : syracuseStep 412003 = 618005) B618005
theorem B412019 : Blo 409770 412019 := bstep (se 1 (by rfl) ⟨309014, by rfl⟩ : syracuseStep 412019 = 618029) B618029
theorem B412035 : Blo 409770 412035 := bstep (se 1 (by rfl) ⟨309026, by rfl⟩ : syracuseStep 412035 = 618053) B618053
theorem B1395089 : Blo 409770 1395089 := bstep (se 2 (by rfl) ⟨523158, by rfl⟩ : syracuseStep 1395089 = 1046317) B1046317
theorem B412051 : Blo 409770 412051 := bstep (se 1 (by rfl) ⟨309038, by rfl⟩ : syracuseStep 412051 = 618077) B618077
theorem B412067 : Blo 409770 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B412083 : Blo 409770 412083 := bstep (se 1 (by rfl) ⟨309062, by rfl⟩ : syracuseStep 412083 = 618125) B618125
theorem B412099 : Blo 409770 412099 := bstep (se 1 (by rfl) ⟨309074, by rfl⟩ : syracuseStep 412099 = 618149) B618149
theorem B412115 : Blo 409770 412115 := bstep (se 1 (by rfl) ⟨309086, by rfl⟩ : syracuseStep 412115 = 618173) B618173
theorem B412131 : Blo 409770 412131 := bstep (se 1 (by rfl) ⟨309098, by rfl⟩ : syracuseStep 412131 = 618197) B618197
theorem B412147 : Blo 409770 412147 := bstep (se 1 (by rfl) ⟨309110, by rfl⟩ : syracuseStep 412147 = 618221) B618221
theorem B412163 : Blo 409770 412163 := bstep (se 1 (by rfl) ⟨309122, by rfl⟩ : syracuseStep 412163 = 618245) B618245
theorem B412179 : Blo 409770 412179 := bstep (se 1 (by rfl) ⟨309134, by rfl⟩ : syracuseStep 412179 = 618269) B618269
theorem B412195 : Blo 409770 412195 := bstep (se 1 (by rfl) ⟨309146, by rfl⟩ : syracuseStep 412195 = 618293) B618293
theorem B412211 : Blo 409770 412211 := bstep (se 1 (by rfl) ⟨309158, by rfl⟩ : syracuseStep 412211 = 618317) B618317
theorem B412227 : Blo 409770 412227 := bstep (se 1 (by rfl) ⟨309170, by rfl⟩ : syracuseStep 412227 = 618341) B618341
theorem B412243 : Blo 409770 412243 := bstep (se 1 (by rfl) ⟨309182, by rfl⟩ : syracuseStep 412243 = 618365) B618365
theorem B412259 : Blo 409770 412259 := bstep (se 1 (by rfl) ⟨309194, by rfl⟩ : syracuseStep 412259 = 618389) B618389
theorem B412275 : Blo 409770 412275 := bstep (se 1 (by rfl) ⟨309206, by rfl⟩ : syracuseStep 412275 = 618413) B618413
theorem B412291 : Blo 409770 412291 := bstep (se 1 (by rfl) ⟨309218, by rfl⟩ : syracuseStep 412291 = 618437) B618437
theorem B412307 : Blo 409770 412307 := bstep (se 1 (by rfl) ⟨309230, by rfl⟩ : syracuseStep 412307 = 618461) B618461
theorem B412323 : Blo 409770 412323 := bstep (se 1 (by rfl) ⟨309242, by rfl⟩ : syracuseStep 412323 = 618485) B618485
theorem B412339 : Blo 409770 412339 := bstep (se 1 (by rfl) ⟨309254, by rfl⟩ : syracuseStep 412339 = 618509) B618509
theorem B412355 : Blo 409770 412355 := bstep (se 1 (by rfl) ⟨309266, by rfl⟩ : syracuseStep 412355 = 618533) B618533
theorem B4704965 : Blo 409770 4704965 := bstep (se 4 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 4704965 = 882181) B882181
theorem B412371 : Blo 409770 412371 := bstep (se 1 (by rfl) ⟨309278, by rfl⟩ : syracuseStep 412371 = 618557) B618557
theorem B412387 : Blo 409770 412387 := bstep (se 1 (by rfl) ⟨309290, by rfl⟩ : syracuseStep 412387 = 618581) B618581
theorem B412403 : Blo 409770 412403 := bstep (se 1 (by rfl) ⟨309302, by rfl⟩ : syracuseStep 412403 = 618605) B618605
theorem B412419 : Blo 409770 412419 := bstep (se 1 (by rfl) ⟨309314, by rfl⟩ : syracuseStep 412419 = 618629) B618629
theorem B1002257 : Blo 409770 1002257 := bstep (se 2 (by rfl) ⟨375846, by rfl⟩ : syracuseStep 1002257 = 751693) B751693
theorem B412435 : Blo 409770 412435 := bstep (se 1 (by rfl) ⟨309326, by rfl⟩ : syracuseStep 412435 = 618653) B618653
theorem B412451 : Blo 409770 412451 := bstep (se 1 (by rfl) ⟨309338, by rfl⟩ : syracuseStep 412451 = 618677) B618677
theorem B412467 : Blo 409770 412467 := bstep (se 1 (by rfl) ⟨309350, by rfl⟩ : syracuseStep 412467 = 618701) B618701
theorem B412483 : Blo 409770 412483 := bstep (se 1 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 412483 = 618725) B618725
theorem B412499 : Blo 409770 412499 := bstep (se 1 (by rfl) ⟨309374, by rfl⟩ : syracuseStep 412499 = 618749) B618749
theorem B412515 : Blo 409770 412515 := bstep (se 1 (by rfl) ⟨309386, by rfl⟩ : syracuseStep 412515 = 618773) B618773
theorem B412531 : Blo 409770 412531 := bstep (se 1 (by rfl) ⟨309398, by rfl⟩ : syracuseStep 412531 = 618797) B618797
theorem B412547 : Blo 409770 412547 := bstep (se 1 (by rfl) ⟨309410, by rfl⟩ : syracuseStep 412547 = 618821) B618821
theorem B412563 : Blo 409770 412563 := bstep (se 1 (by rfl) ⟨309422, by rfl⟩ : syracuseStep 412563 = 618845) B618845
theorem B412579 : Blo 409770 412579 := bstep (se 1 (by rfl) ⟨309434, by rfl⟩ : syracuseStep 412579 = 618869) B618869
theorem B1395629 : Blo 409770 1395629 := bstep (se 3 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 1395629 = 523361) B523361
theorem B412595 : Blo 409770 412595 := bstep (se 1 (by rfl) ⟨309446, by rfl⟩ : syracuseStep 412595 = 618893) B618893
theorem B412611 : Blo 409770 412611 := bstep (se 1 (by rfl) ⟨309458, by rfl⟩ : syracuseStep 412611 = 618917) B618917
theorem B412627 : Blo 409770 412627 := bstep (se 1 (by rfl) ⟨309470, by rfl⟩ : syracuseStep 412627 = 618941) B618941
theorem B412643 : Blo 409770 412643 := bstep (se 1 (by rfl) ⟨309482, by rfl⟩ : syracuseStep 412643 = 618965) B618965
theorem B1395683 : Blo 409770 1395683 := bstep (se 1 (by rfl) ⟨1046762, by rfl⟩ : syracuseStep 1395683 = 2093525) B2093525
theorem B412659 : Blo 409770 412659 := bstep (se 1 (by rfl) ⟨309494, by rfl⟩ : syracuseStep 412659 = 618989) B618989
theorem B412675 : Blo 409770 412675 := bstep (se 1 (by rfl) ⟨309506, by rfl⟩ : syracuseStep 412675 = 619013) B619013
theorem B412691 : Blo 409770 412691 := bstep (se 1 (by rfl) ⟨309518, by rfl⟩ : syracuseStep 412691 = 619037) B619037
theorem B412707 : Blo 409770 412707 := bstep (se 1 (by rfl) ⟨309530, by rfl⟩ : syracuseStep 412707 = 619061) B619061
theorem B412723 : Blo 409770 412723 := bstep (se 1 (by rfl) ⟨309542, by rfl⟩ : syracuseStep 412723 = 619085) B619085
theorem B412739 : Blo 409770 412739 := bstep (se 1 (by rfl) ⟨309554, by rfl⟩ : syracuseStep 412739 = 619109) B619109
theorem B412755 : Blo 409770 412755 := bstep (se 1 (by rfl) ⟨309566, by rfl⟩ : syracuseStep 412755 = 619133) B619133
theorem B2346083 : Blo 409770 2346083 := bstep (se 1 (by rfl) ⟨1759562, by rfl⟩ : syracuseStep 2346083 = 3519125) B3519125
theorem B412771 : Blo 409770 412771 := bstep (se 1 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 412771 = 619157) B619157
theorem B412787 : Blo 409770 412787 := bstep (se 1 (by rfl) ⟨309590, by rfl⟩ : syracuseStep 412787 = 619181) B619181
theorem B412803 : Blo 409770 412803 := bstep (se 1 (by rfl) ⟨309602, by rfl⟩ : syracuseStep 412803 = 619205) B619205
theorem B412819 : Blo 409770 412819 := bstep (se 1 (by rfl) ⟨309614, by rfl⟩ : syracuseStep 412819 = 619229) B619229
theorem B412835 : Blo 409770 412835 := bstep (se 1 (by rfl) ⟨309626, by rfl⟩ : syracuseStep 412835 = 619253) B619253
theorem B412851 : Blo 409770 412851 := bstep (se 1 (by rfl) ⟨309638, by rfl⟩ : syracuseStep 412851 = 619277) B619277
theorem B412867 : Blo 409770 412867 := bstep (se 1 (by rfl) ⟨309650, by rfl⟩ : syracuseStep 412867 = 619301) B619301
theorem B412883 : Blo 409770 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B5950691 : Blo 409770 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B412899 : Blo 409770 412899 := bstep (se 1 (by rfl) ⟨309674, by rfl⟩ : syracuseStep 412899 = 619349) B619349
theorem B1395953 : Blo 409770 1395953 := bstep (se 2 (by rfl) ⟨523482, by rfl⟩ : syracuseStep 1395953 = 1046965) B1046965
theorem B412915 : Blo 409770 412915 := bstep (se 1 (by rfl) ⟨309686, by rfl⟩ : syracuseStep 412915 = 619373) B619373
theorem B412931 : Blo 409770 412931 := bstep (se 1 (by rfl) ⟨309698, by rfl⟩ : syracuseStep 412931 = 619397) B619397
theorem B412947 : Blo 409770 412947 := bstep (se 1 (by rfl) ⟨309710, by rfl⟩ : syracuseStep 412947 = 619421) B619421
theorem B412963 : Blo 409770 412963 := bstep (se 1 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 412963 = 619445) B619445
theorem B412979 : Blo 409770 412979 := bstep (se 1 (by rfl) ⟨309734, by rfl⟩ : syracuseStep 412979 = 619469) B619469
theorem B412995 : Blo 409770 412995 := bstep (se 1 (by rfl) ⟨309746, by rfl⟩ : syracuseStep 412995 = 619493) B619493
theorem B413011 : Blo 409770 413011 := bstep (se 1 (by rfl) ⟨309758, by rfl⟩ : syracuseStep 413011 = 619517) B619517
theorem B413027 : Blo 409770 413027 := bstep (se 1 (by rfl) ⟨309770, by rfl⟩ : syracuseStep 413027 = 619541) B619541
theorem B5000561 : Blo 409770 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B413043 : Blo 409770 413043 := bstep (se 1 (by rfl) ⟨309782, by rfl⟩ : syracuseStep 413043 = 619565) B619565
theorem B413059 : Blo 409770 413059 := bstep (se 1 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 413059 = 619589) B619589
theorem B413075 : Blo 409770 413075 := bstep (se 1 (by rfl) ⟨309806, by rfl⟩ : syracuseStep 413075 = 619613) B619613
theorem B413091 : Blo 409770 413091 := bstep (se 1 (by rfl) ⟨309818, by rfl⟩ : syracuseStep 413091 = 619637) B619637
theorem B413107 : Blo 409770 413107 := bstep (se 1 (by rfl) ⟨309830, by rfl⟩ : syracuseStep 413107 = 619661) B619661
theorem B413123 : Blo 409770 413123 := bstep (se 1 (by rfl) ⟨309842, by rfl⟩ : syracuseStep 413123 = 619685) B619685
theorem B413139 : Blo 409770 413139 := bstep (se 1 (by rfl) ⟨309854, by rfl⟩ : syracuseStep 413139 = 619709) B619709
theorem B413155 : Blo 409770 413155 := bstep (se 1 (by rfl) ⟨309866, by rfl⟩ : syracuseStep 413155 = 619733) B619733
theorem B413171 : Blo 409770 413171 := bstep (se 1 (by rfl) ⟨309878, by rfl⟩ : syracuseStep 413171 = 619757) B619757
theorem B413187 : Blo 409770 413187 := bstep (se 1 (by rfl) ⟨309890, by rfl⟩ : syracuseStep 413187 = 619781) B619781
theorem B413203 : Blo 409770 413203 := bstep (se 1 (by rfl) ⟨309902, by rfl⟩ : syracuseStep 413203 = 619805) B619805
theorem B413219 : Blo 409770 413219 := bstep (se 1 (by rfl) ⟨309914, by rfl⟩ : syracuseStep 413219 = 619829) B619829
theorem B413235 : Blo 409770 413235 := bstep (se 1 (by rfl) ⟨309926, by rfl⟩ : syracuseStep 413235 = 619853) B619853
theorem B413251 : Blo 409770 413251 := bstep (se 1 (by rfl) ⟨309938, by rfl⟩ : syracuseStep 413251 = 619877) B619877
theorem B413267 : Blo 409770 413267 := bstep (se 1 (by rfl) ⟨309950, by rfl⟩ : syracuseStep 413267 = 619901) B619901
theorem B413283 : Blo 409770 413283 := bstep (se 1 (by rfl) ⟨309962, by rfl⟩ : syracuseStep 413283 = 619925) B619925
theorem B3001969 : Blo 409770 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B413299 : Blo 409770 413299 := bstep (se 1 (by rfl) ⟨309974, by rfl⟩ : syracuseStep 413299 = 619949) B619949
theorem B413315 : Blo 409770 413315 := bstep (se 1 (by rfl) ⟨309986, by rfl⟩ : syracuseStep 413315 = 619973) B619973
theorem B1166993 : Blo 409770 1166993 := bstep (se 2 (by rfl) ⟨437622, by rfl⟩ : syracuseStep 1166993 = 875245) B875245
theorem B413331 : Blo 409770 413331 := bstep (se 1 (by rfl) ⟨309998, by rfl⟩ : syracuseStep 413331 = 619997) B619997
theorem B413347 : Blo 409770 413347 := bstep (se 1 (by rfl) ⟨310010, by rfl⟩ : syracuseStep 413347 = 620021) B620021
theorem B413363 : Blo 409770 413363 := bstep (se 1 (by rfl) ⟨310022, by rfl⟩ : syracuseStep 413363 = 620045) B620045
theorem B413379 : Blo 409770 413379 := bstep (se 1 (by rfl) ⟨310034, by rfl⟩ : syracuseStep 413379 = 620069) B620069
theorem B413395 : Blo 409770 413395 := bstep (se 1 (by rfl) ⟨310046, by rfl⟩ : syracuseStep 413395 = 620093) B620093
theorem B1986275 : Blo 409770 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B413411 : Blo 409770 413411 := bstep (se 1 (by rfl) ⟨310058, by rfl⟩ : syracuseStep 413411 = 620117) B620117
theorem B413427 : Blo 409770 413427 := bstep (se 1 (by rfl) ⟨310070, by rfl⟩ : syracuseStep 413427 = 620141) B620141
theorem B413443 : Blo 409770 413443 := bstep (se 1 (by rfl) ⟨310082, by rfl⟩ : syracuseStep 413443 = 620165) B620165
theorem B413459 : Blo 409770 413459 := bstep (se 1 (by rfl) ⟨310094, by rfl⟩ : syracuseStep 413459 = 620189) B620189
theorem B413475 : Blo 409770 413475 := bstep (se 1 (by rfl) ⟨310106, by rfl⟩ : syracuseStep 413475 = 620213) B620213
theorem B741169 : Blo 409770 741169 := bstep (se 2 (by rfl) ⟨277938, by rfl⟩ : syracuseStep 741169 = 555877) B555877
theorem B413491 : Blo 409770 413491 := bstep (se 1 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 413491 = 620237) B620237
theorem B413507 : Blo 409770 413507 := bstep (se 1 (by rfl) ⟨310130, by rfl⟩ : syracuseStep 413507 = 620261) B620261
theorem B413523 : Blo 409770 413523 := bstep (se 1 (by rfl) ⟨310142, by rfl⟩ : syracuseStep 413523 = 620285) B620285
theorem B413539 : Blo 409770 413539 := bstep (se 1 (by rfl) ⟨310154, by rfl⟩ : syracuseStep 413539 = 620309) B620309
theorem B413555 : Blo 409770 413555 := bstep (se 1 (by rfl) ⟨310166, by rfl⟩ : syracuseStep 413555 = 620333) B620333
theorem B413571 : Blo 409770 413571 := bstep (se 1 (by rfl) ⟨310178, by rfl⟩ : syracuseStep 413571 = 620357) B620357
theorem B2641805 : Blo 409770 2641805 := bstep (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) B990677
theorem B413587 : Blo 409770 413587 := bstep (se 1 (by rfl) ⟨310190, by rfl⟩ : syracuseStep 413587 = 620381) B620381
theorem B413603 : Blo 409770 413603 := bstep (se 1 (by rfl) ⟨310202, by rfl⟩ : syracuseStep 413603 = 620405) B620405
theorem B413619 : Blo 409770 413619 := bstep (se 1 (by rfl) ⟨310214, by rfl⟩ : syracuseStep 413619 = 620429) B620429
theorem B413635 : Blo 409770 413635 := bstep (se 1 (by rfl) ⟨310226, by rfl⟩ : syracuseStep 413635 = 620453) B620453
theorem B413651 : Blo 409770 413651 := bstep (se 1 (by rfl) ⟨310238, by rfl⟩ : syracuseStep 413651 = 620477) B620477
theorem B413667 : Blo 409770 413667 := bstep (se 1 (by rfl) ⟨310250, by rfl⟩ : syracuseStep 413667 = 620501) B620501
theorem B937969 : Blo 409770 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B413683 : Blo 409770 413683 := bstep (se 1 (by rfl) ⟨310262, by rfl⟩ : syracuseStep 413683 = 620525) B620525
theorem B413699 : Blo 409770 413699 := bstep (se 1 (by rfl) ⟨310274, by rfl⟩ : syracuseStep 413699 = 620549) B620549
theorem B413715 : Blo 409770 413715 := bstep (se 1 (by rfl) ⟨310286, by rfl⟩ : syracuseStep 413715 = 620573) B620573
theorem B413731 : Blo 409770 413731 := bstep (se 1 (by rfl) ⟨310298, by rfl⟩ : syracuseStep 413731 = 620597) B620597
theorem B413747 : Blo 409770 413747 := bstep (se 1 (by rfl) ⟨310310, by rfl⟩ : syracuseStep 413747 = 620621) B620621
theorem B413763 : Blo 409770 413763 := bstep (se 1 (by rfl) ⟨310322, by rfl⟩ : syracuseStep 413763 = 620645) B620645
theorem B1560653 : Blo 409770 1560653 := bstep (se 3 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 1560653 = 585245) B585245
theorem B2642033 : Blo 409770 2642033 := bstep (se 2 (by rfl) ⟨990762, by rfl⟩ : syracuseStep 2642033 = 1981525) B1981525
theorem B2216069 : Blo 409770 2216069 := bstep (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) B415513
theorem B1069283 : Blo 409770 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B17125829 : Blo 409770 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B2085425 : Blo 409770 2085425 := bstep (se 2 (by rfl) ⟨782034, by rfl⟩ : syracuseStep 2085425 = 1564069) B1564069
theorem B2380337 : Blo 409770 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B1167949 : Blo 409770 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B1168177 : Blo 409770 1168177 := bstep (se 2 (by rfl) ⟨438066, by rfl⟩ : syracuseStep 1168177 = 876133) B876133
theorem B1561457 : Blo 409770 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B2347973 : Blo 409770 2347973 := bstep (se 4 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 2347973 = 440245) B440245
theorem B1168337 : Blo 409770 1168337 := bstep (se 2 (by rfl) ⟨438126, by rfl⟩ : syracuseStep 1168337 = 876253) B876253
theorem B513011 : Blo 409770 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B1168451 : Blo 409770 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B1037681 : Blo 409770 1037681 := bstep (se 2 (by rfl) ⟨389130, by rfl⟩ : syracuseStep 1037681 = 778261) B778261
theorem B939377 : Blo 409770 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B1037731 : Blo 409770 1037731 := bstep (se 1 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 1037731 = 1556597) B1556597
theorem B1562125 : Blo 409770 1562125 := bstep (se 3 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 1562125 = 585797) B585797
theorem B1037873 : Blo 409770 1037873 := bstep (se 2 (by rfl) ⟨389202, by rfl⟩ : syracuseStep 1037873 = 778405) B778405
theorem B612145 : Blo 409770 612145 := bstep (se 2 (by rfl) ⟨229554, by rfl⟩ : syracuseStep 612145 = 459109) B459109
theorem B1005443 : Blo 409770 1005443 := bstep (se 1 (by rfl) ⟨754082, by rfl⟩ : syracuseStep 1005443 = 1508165) B1508165
theorem B2086883 : Blo 409770 2086883 := bstep (se 1 (by rfl) ⟨1565162, by rfl⟩ : syracuseStep 2086883 = 3130325) B3130325
theorem B1169453 : Blo 409770 1169453 := bstep (se 3 (by rfl) ⟨219272, by rfl⟩ : syracuseStep 1169453 = 438545) B438545
theorem B1169635 : Blo 409770 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B1267939 : Blo 409770 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B1562915 : Blo 409770 1562915 := bstep (se 1 (by rfl) ⟨1172186, by rfl⟩ : syracuseStep 1562915 = 2344373) B2344373
theorem B1169795 : Blo 409770 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B1759715 : Blo 409770 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B1038865 : Blo 409770 1038865 := bstep (se 2 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 1038865 = 779149) B779149
theorem B2087693 : Blo 409770 2087693 := bstep (se 3 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 2087693 = 782885) B782885
theorem B1039139 : Blo 409770 1039139 := bstep (se 1 (by rfl) ⟨779354, by rfl⟩ : syracuseStep 1039139 = 1558709) B1558709
theorem B940835 : Blo 409770 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B744241 : Blo 409770 744241 := bstep (se 2 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 744241 = 558181) B558181
theorem B3627917 : Blo 409770 3627917 := bstep (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) B1360469
theorem B1563569 : Blo 409770 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B1039331 : Blo 409770 1039331 := bstep (se 1 (by rfl) ⟨779498, by rfl⟩ : syracuseStep 1039331 = 1558997) B1558997
theorem B875843 : Blo 409770 875843 := bstep (se 1 (by rfl) ⟨656882, by rfl⟩ : syracuseStep 875843 = 1313765) B1313765
theorem B1007011 : Blo 409770 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B1170865 : Blo 409770 1170865 := bstep (se 2 (by rfl) ⟨439074, by rfl⟩ : syracuseStep 1170865 = 878149) B878149
theorem B876433 : Blo 409770 876433 := bstep (se 2 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 876433 = 657325) B657325
theorem B1040273 : Blo 409770 1040273 := bstep (se 2 (by rfl) ⟨390102, by rfl⟩ : syracuseStep 1040273 = 780205) B780205
theorem B417683 : Blo 409770 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B745379 : Blo 409770 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B1040323 : Blo 409770 1040323 := bstep (se 1 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 1040323 = 1560485) B1560485
theorem B1040465 : Blo 409770 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B418019 : Blo 409770 418019 := bstep (se 1 (by rfl) ⟨313514, by rfl⟩ : syracuseStep 418019 = 627029) B627029
theorem B2515171 : Blo 409770 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B778481 : Blo 409770 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B614657 : Blo 409770 614657 := bstep (se 2 (by rfl) ⟨230496, by rfl⟩ : syracuseStep 614657 = 460993) B460993
theorem B614675 : Blo 409770 614675 := bstep (se 1 (by rfl) ⟨461006, by rfl⟩ : syracuseStep 614675 = 922013) B922013
theorem B614705 : Blo 409770 614705 := bstep (se 2 (by rfl) ⟨230514, by rfl⟩ : syracuseStep 614705 = 461029) B461029
theorem B614723 : Blo 409770 614723 := bstep (se 1 (by rfl) ⟨461042, by rfl⟩ : syracuseStep 614723 = 922085) B922085
theorem B614753 : Blo 409770 614753 := bstep (se 2 (by rfl) ⟨230532, by rfl⟩ : syracuseStep 614753 = 461065) B461065
theorem B1565027 : Blo 409770 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B1565041 : Blo 409770 1565041 := bstep (se 2 (by rfl) ⟨586890, by rfl⟩ : syracuseStep 1565041 = 1173781) B1173781
theorem B614771 : Blo 409770 614771 := bstep (se 1 (by rfl) ⟨461078, by rfl⟩ : syracuseStep 614771 = 922157) B922157
theorem B4710797 : Blo 409770 4710797 := bstep (se 3 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 4710797 = 1766549) B1766549
theorem B614801 : Blo 409770 614801 := bstep (se 2 (by rfl) ⟨230550, by rfl⟩ : syracuseStep 614801 = 461101) B461101
theorem B614819 : Blo 409770 614819 := bstep (se 1 (by rfl) ⟨461114, by rfl⟩ : syracuseStep 614819 = 922229) B922229
theorem B614849 : Blo 409770 614849 := bstep (se 2 (by rfl) ⟨230568, by rfl⟩ : syracuseStep 614849 = 461137) B461137
theorem B614867 : Blo 409770 614867 := bstep (se 1 (by rfl) ⟨461150, by rfl⟩ : syracuseStep 614867 = 922301) B922301
theorem B614897 : Blo 409770 614897 := bstep (se 2 (by rfl) ⟨230586, by rfl⟩ : syracuseStep 614897 = 461173) B461173
theorem B614915 : Blo 409770 614915 := bstep (se 1 (by rfl) ⟨461186, by rfl⟩ : syracuseStep 614915 = 922373) B922373
theorem B614945 : Blo 409770 614945 := bstep (se 2 (by rfl) ⟨230604, by rfl⟩ : syracuseStep 614945 = 461209) B461209
theorem B614963 : Blo 409770 614963 := bstep (se 1 (by rfl) ⟨461222, by rfl⟩ : syracuseStep 614963 = 922445) B922445
theorem B614993 : Blo 409770 614993 := bstep (se 2 (by rfl) ⟨230622, by rfl⟩ : syracuseStep 614993 = 461245) B461245
theorem B615011 : Blo 409770 615011 := bstep (se 1 (by rfl) ⟨461258, by rfl⟩ : syracuseStep 615011 = 922517) B922517
theorem B615041 : Blo 409770 615041 := bstep (se 2 (by rfl) ⟨230640, by rfl⟩ : syracuseStep 615041 = 461281) B461281
theorem B11231885 : Blo 409770 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B615059 : Blo 409770 615059 := bstep (se 1 (by rfl) ⟨461294, by rfl⟩ : syracuseStep 615059 = 922589) B922589
theorem B1172141 : Blo 409770 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B615089 : Blo 409770 615089 := bstep (se 2 (by rfl) ⟨230658, by rfl⟩ : syracuseStep 615089 = 461317) B461317
theorem B615107 : Blo 409770 615107 := bstep (se 1 (by rfl) ⟨461330, by rfl⟩ : syracuseStep 615107 = 922661) B922661
theorem B942787 : Blo 409770 942787 := bstep (se 1 (by rfl) ⟨707090, by rfl⟩ : syracuseStep 942787 = 1414181) B1414181
theorem B615137 : Blo 409770 615137 := bstep (se 2 (by rfl) ⟨230676, by rfl⟩ : syracuseStep 615137 = 461353) B461353
theorem B615155 : Blo 409770 615155 := bstep (se 1 (by rfl) ⟨461366, by rfl⟩ : syracuseStep 615155 = 922733) B922733
theorem B615185 : Blo 409770 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B615203 : Blo 409770 615203 := bstep (se 1 (by rfl) ⟨461402, by rfl⟩ : syracuseStep 615203 = 922805) B922805
theorem B615233 : Blo 409770 615233 := bstep (se 2 (by rfl) ⟨230712, by rfl⟩ : syracuseStep 615233 = 461425) B461425
theorem B418627 : Blo 409770 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B615251 : Blo 409770 615251 := bstep (se 1 (by rfl) ⟨461438, by rfl⟩ : syracuseStep 615251 = 922877) B922877
theorem B1172323 : Blo 409770 1172323 := bstep (se 1 (by rfl) ⟨879242, by rfl⟩ : syracuseStep 1172323 = 1758485) B1758485
theorem B615281 : Blo 409770 615281 := bstep (se 2 (by rfl) ⟨230730, by rfl⟩ : syracuseStep 615281 = 461461) B461461
theorem B615299 : Blo 409770 615299 := bstep (se 1 (by rfl) ⟨461474, by rfl⟩ : syracuseStep 615299 = 922949) B922949
theorem B1172369 : Blo 409770 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B615329 : Blo 409770 615329 := bstep (se 2 (by rfl) ⟨230748, by rfl⟩ : syracuseStep 615329 = 461497) B461497
theorem B615347 : Blo 409770 615347 := bstep (se 1 (by rfl) ⟨461510, by rfl⟩ : syracuseStep 615347 = 923021) B923021
theorem B615377 : Blo 409770 615377 := bstep (se 2 (by rfl) ⟨230766, by rfl⟩ : syracuseStep 615377 = 461533) B461533
theorem B615395 : Blo 409770 615395 := bstep (se 1 (by rfl) ⟨461546, by rfl⟩ : syracuseStep 615395 = 923093) B923093
theorem B615425 : Blo 409770 615425 := bstep (se 2 (by rfl) ⟨230784, by rfl⟩ : syracuseStep 615425 = 461569) B461569
theorem B615443 : Blo 409770 615443 := bstep (se 1 (by rfl) ⟨461582, by rfl⟩ : syracuseStep 615443 = 923165) B923165
theorem B615473 : Blo 409770 615473 := bstep (se 2 (by rfl) ⟨230802, by rfl⟩ : syracuseStep 615473 = 461605) B461605
theorem B1041457 : Blo 409770 1041457 := bstep (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) B781093
theorem B615491 : Blo 409770 615491 := bstep (se 1 (by rfl) ⟨461618, by rfl⟩ : syracuseStep 615491 = 923237) B923237
theorem B615521 : Blo 409770 615521 := bstep (se 2 (by rfl) ⟨230820, by rfl⟩ : syracuseStep 615521 = 461641) B461641
theorem B779377 : Blo 409770 779377 := bstep (se 2 (by rfl) ⟨292266, by rfl⟩ : syracuseStep 779377 = 584533) B584533
theorem B615539 : Blo 409770 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B4220045 : Blo 409770 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B615569 : Blo 409770 615569 := bstep (se 2 (by rfl) ⟨230838, by rfl⟩ : syracuseStep 615569 = 461677) B461677
theorem B615587 : Blo 409770 615587 := bstep (se 1 (by rfl) ⟨461690, by rfl⟩ : syracuseStep 615587 = 923381) B923381
theorem B615617 : Blo 409770 615617 := bstep (se 2 (by rfl) ⟨230856, by rfl⟩ : syracuseStep 615617 = 461713) B461713
theorem B615635 : Blo 409770 615635 := bstep (se 1 (by rfl) ⟨461726, by rfl⟩ : syracuseStep 615635 = 923453) B923453
theorem B615665 : Blo 409770 615665 := bstep (se 2 (by rfl) ⟨230874, by rfl⟩ : syracuseStep 615665 = 461749) B461749
theorem B615683 : Blo 409770 615683 := bstep (se 1 (by rfl) ⟨461762, by rfl⟩ : syracuseStep 615683 = 923525) B923525
theorem B779537 : Blo 409770 779537 := bstep (se 2 (by rfl) ⟨292326, by rfl⟩ : syracuseStep 779537 = 584653) B584653
theorem B615713 : Blo 409770 615713 := bstep (se 2 (by rfl) ⟨230892, by rfl⟩ : syracuseStep 615713 = 461785) B461785
theorem B615731 : Blo 409770 615731 := bstep (se 1 (by rfl) ⟨461798, by rfl⟩ : syracuseStep 615731 = 923597) B923597
theorem B1041731 : Blo 409770 1041731 := bstep (se 1 (by rfl) ⟨781298, by rfl⟩ : syracuseStep 1041731 = 1562597) B1562597
theorem B2385229 : Blo 409770 2385229 := bstep (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) B894461
theorem B615761 : Blo 409770 615761 := bstep (se 2 (by rfl) ⟨230910, by rfl⟩ : syracuseStep 615761 = 461821) B461821
theorem B615779 : Blo 409770 615779 := bstep (se 1 (by rfl) ⟨461834, by rfl⟩ : syracuseStep 615779 = 923669) B923669
theorem B615809 : Blo 409770 615809 := bstep (se 2 (by rfl) ⟨230928, by rfl⟩ : syracuseStep 615809 = 461857) B461857
theorem B615827 : Blo 409770 615827 := bstep (se 1 (by rfl) ⟨461870, by rfl⟩ : syracuseStep 615827 = 923741) B923741
theorem B615857 : Blo 409770 615857 := bstep (se 2 (by rfl) ⟨230946, by rfl⟩ : syracuseStep 615857 = 461893) B461893
theorem B615875 : Blo 409770 615875 := bstep (se 1 (by rfl) ⟨461906, by rfl⟩ : syracuseStep 615875 = 923813) B923813
theorem B615905 : Blo 409770 615905 := bstep (se 2 (by rfl) ⟨230964, by rfl⟩ : syracuseStep 615905 = 461929) B461929
theorem B615923 : Blo 409770 615923 := bstep (se 1 (by rfl) ⟨461942, by rfl⟩ : syracuseStep 615923 = 923885) B923885
theorem B1041923 : Blo 409770 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B615953 : Blo 409770 615953 := bstep (se 2 (by rfl) ⟨230982, by rfl⟩ : syracuseStep 615953 = 461965) B461965
theorem B615971 : Blo 409770 615971 := bstep (se 1 (by rfl) ⟨461978, by rfl⟩ : syracuseStep 615971 = 923957) B923957
theorem B616001 : Blo 409770 616001 := bstep (se 2 (by rfl) ⟨231000, by rfl⟩ : syracuseStep 616001 = 462001) B462001
theorem B616019 : Blo 409770 616019 := bstep (se 1 (by rfl) ⟨462014, by rfl⟩ : syracuseStep 616019 = 924029) B924029
theorem B616049 : Blo 409770 616049 := bstep (se 2 (by rfl) ⟨231018, by rfl⟩ : syracuseStep 616049 = 462037) B462037
theorem B2090609 : Blo 409770 2090609 := bstep (se 2 (by rfl) ⟨783978, by rfl⟩ : syracuseStep 2090609 = 1567957) B1567957
theorem B616067 : Blo 409770 616067 := bstep (se 1 (by rfl) ⟨462050, by rfl⟩ : syracuseStep 616067 = 924101) B924101
theorem B616097 : Blo 409770 616097 := bstep (se 2 (by rfl) ⟨231036, by rfl⟩ : syracuseStep 616097 = 462073) B462073
theorem B779939 : Blo 409770 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B616115 : Blo 409770 616115 := bstep (se 1 (by rfl) ⟨462086, by rfl⟩ : syracuseStep 616115 = 924173) B924173
theorem B616145 : Blo 409770 616145 := bstep (se 2 (by rfl) ⟨231054, by rfl⟩ : syracuseStep 616145 = 462109) B462109
theorem B616163 : Blo 409770 616163 := bstep (se 1 (by rfl) ⟨462122, by rfl⟩ : syracuseStep 616163 = 924245) B924245
theorem B616193 : Blo 409770 616193 := bstep (se 2 (by rfl) ⟨231072, by rfl⟩ : syracuseStep 616193 = 462145) B462145
theorem B616211 : Blo 409770 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B1566499 : Blo 409770 1566499 := bstep (se 1 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 1566499 = 2349749) B2349749
theorem B616241 : Blo 409770 616241 := bstep (se 2 (by rfl) ⟨231090, by rfl⟩ : syracuseStep 616241 = 462181) B462181
theorem B616259 : Blo 409770 616259 := bstep (se 1 (by rfl) ⟨462194, by rfl⟩ : syracuseStep 616259 = 924389) B924389
theorem B616289 : Blo 409770 616289 := bstep (se 2 (by rfl) ⟨231108, by rfl⟩ : syracuseStep 616289 = 462217) B462217
theorem B616307 : Blo 409770 616307 := bstep (se 1 (by rfl) ⟨462230, by rfl⟩ : syracuseStep 616307 = 924461) B924461
theorem B616337 : Blo 409770 616337 := bstep (se 2 (by rfl) ⟨231126, by rfl⟩ : syracuseStep 616337 = 462253) B462253
theorem B616355 : Blo 409770 616355 := bstep (se 1 (by rfl) ⟨462266, by rfl⟩ : syracuseStep 616355 = 924533) B924533
theorem B616385 : Blo 409770 616385 := bstep (se 2 (by rfl) ⟨231144, by rfl⟩ : syracuseStep 616385 = 462289) B462289
theorem B583633 : Blo 409770 583633 := bstep (se 2 (by rfl) ⟨218862, by rfl⟩ : syracuseStep 583633 = 437725) B437725
theorem B616403 : Blo 409770 616403 := bstep (se 1 (by rfl) ⟨462302, by rfl⟩ : syracuseStep 616403 = 924605) B924605
theorem B616433 : Blo 409770 616433 := bstep (se 2 (by rfl) ⟨231162, by rfl⟩ : syracuseStep 616433 = 462325) B462325
theorem B616451 : Blo 409770 616451 := bstep (se 1 (by rfl) ⟨462338, by rfl⟩ : syracuseStep 616451 = 924677) B924677
theorem B616481 : Blo 409770 616481 := bstep (se 2 (by rfl) ⟨231180, by rfl⟩ : syracuseStep 616481 = 462361) B462361
theorem B616499 : Blo 409770 616499 := bstep (se 1 (by rfl) ⟨462374, by rfl⟩ : syracuseStep 616499 = 924749) B924749
theorem B616529 : Blo 409770 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B616547 : Blo 409770 616547 := bstep (se 1 (by rfl) ⟨462410, by rfl⟩ : syracuseStep 616547 = 924821) B924821
theorem B1763441 : Blo 409770 1763441 := bstep (se 2 (by rfl) ⟨661290, by rfl⟩ : syracuseStep 1763441 = 1322581) B1322581
theorem B616577 : Blo 409770 616577 := bstep (se 2 (by rfl) ⟨231216, by rfl⟩ : syracuseStep 616577 = 462433) B462433
theorem B616595 : Blo 409770 616595 := bstep (se 1 (by rfl) ⟨462446, by rfl⟩ : syracuseStep 616595 = 924893) B924893
theorem B616625 : Blo 409770 616625 := bstep (se 2 (by rfl) ⟨231234, by rfl⟩ : syracuseStep 616625 = 462469) B462469
theorem B616643 : Blo 409770 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B616673 : Blo 409770 616673 := bstep (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) B462505
theorem B38070499 : Blo 409770 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B616691 : Blo 409770 616691 := bstep (se 1 (by rfl) ⟨462518, by rfl⟩ : syracuseStep 616691 = 925037) B925037
theorem B616721 : Blo 409770 616721 := bstep (se 2 (by rfl) ⟨231270, by rfl⟩ : syracuseStep 616721 = 462541) B462541
theorem B616739 : Blo 409770 616739 := bstep (se 1 (by rfl) ⟨462554, by rfl⟩ : syracuseStep 616739 = 925109) B925109
theorem B616769 : Blo 409770 616769 := bstep (se 2 (by rfl) ⟨231288, by rfl⟩ : syracuseStep 616769 = 462577) B462577
theorem B1173827 : Blo 409770 1173827 := bstep (se 1 (by rfl) ⟨880370, by rfl⟩ : syracuseStep 1173827 = 1760741) B1760741
theorem B2648389 : Blo 409770 2648389 := bstep (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) B496573
theorem B616787 : Blo 409770 616787 := bstep (se 1 (by rfl) ⟨462590, by rfl⟩ : syracuseStep 616787 = 925181) B925181
theorem B616817 : Blo 409770 616817 := bstep (se 2 (by rfl) ⟨231306, by rfl⟩ : syracuseStep 616817 = 462613) B462613
theorem B2681201 : Blo 409770 2681201 := bstep (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) B2010901
theorem B616835 : Blo 409770 616835 := bstep (se 1 (by rfl) ⟨462626, by rfl⟩ : syracuseStep 616835 = 925253) B925253
theorem B616865 : Blo 409770 616865 := bstep (se 2 (by rfl) ⟨231324, by rfl⟩ : syracuseStep 616865 = 462649) B462649
theorem B1042865 : Blo 409770 1042865 := bstep (se 2 (by rfl) ⟨391074, by rfl⟩ : syracuseStep 1042865 = 782149) B782149
theorem B616883 : Blo 409770 616883 := bstep (se 1 (by rfl) ⟨462662, by rfl⟩ : syracuseStep 616883 = 925325) B925325
theorem B616913 : Blo 409770 616913 := bstep (se 2 (by rfl) ⟨231342, by rfl⟩ : syracuseStep 616913 = 462685) B462685
theorem B616931 : Blo 409770 616931 := bstep (se 1 (by rfl) ⟨462698, by rfl⟩ : syracuseStep 616931 = 925397) B925397
theorem B4450787 : Blo 409770 4450787 := bstep (se 1 (by rfl) ⟨3338090, by rfl⟩ : syracuseStep 4450787 = 6676181) B6676181
theorem B1042915 : Blo 409770 1042915 := bstep (se 1 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 1042915 = 1564373) B1564373
theorem B616961 : Blo 409770 616961 := bstep (se 2 (by rfl) ⟨231360, by rfl⟩ : syracuseStep 616961 = 462721) B462721
theorem B616979 : Blo 409770 616979 := bstep (se 1 (by rfl) ⟨462734, by rfl⟩ : syracuseStep 616979 = 925469) B925469
theorem B780835 : Blo 409770 780835 := bstep (se 1 (by rfl) ⟨585626, by rfl⟩ : syracuseStep 780835 = 1171253) B1171253
theorem B617009 : Blo 409770 617009 := bstep (se 2 (by rfl) ⟨231378, by rfl⟩ : syracuseStep 617009 = 462757) B462757
theorem B617027 : Blo 409770 617027 := bstep (se 1 (by rfl) ⟨462770, by rfl⟩ : syracuseStep 617027 = 925541) B925541
theorem B617057 : Blo 409770 617057 := bstep (se 2 (by rfl) ⟨231396, by rfl⟩ : syracuseStep 617057 = 462793) B462793
theorem B1043057 : Blo 409770 1043057 := bstep (se 2 (by rfl) ⟨391146, by rfl⟩ : syracuseStep 1043057 = 782293) B782293
theorem B617075 : Blo 409770 617075 := bstep (se 1 (by rfl) ⟨462806, by rfl⟩ : syracuseStep 617075 = 925613) B925613
theorem B2353805 : Blo 409770 2353805 := bstep (se 3 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 2353805 = 882677) B882677
theorem B617105 : Blo 409770 617105 := bstep (se 2 (by rfl) ⟨231414, by rfl⟩ : syracuseStep 617105 = 462829) B462829
theorem B584339 : Blo 409770 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B617123 : Blo 409770 617123 := bstep (se 1 (by rfl) ⟨462842, by rfl⟩ : syracuseStep 617123 = 925685) B925685
theorem B617153 : Blo 409770 617153 := bstep (se 2 (by rfl) ⟨231432, by rfl⟩ : syracuseStep 617153 = 462865) B462865
theorem B780995 : Blo 409770 780995 := bstep (se 1 (by rfl) ⟨585746, by rfl⟩ : syracuseStep 780995 = 1171493) B1171493
theorem B617171 : Blo 409770 617171 := bstep (se 1 (by rfl) ⟨462878, by rfl⟩ : syracuseStep 617171 = 925757) B925757
theorem B617201 : Blo 409770 617201 := bstep (se 2 (by rfl) ⟨231450, by rfl⟩ : syracuseStep 617201 = 462901) B462901
theorem B617219 : Blo 409770 617219 := bstep (se 1 (by rfl) ⟨462914, by rfl⟩ : syracuseStep 617219 = 925829) B925829
theorem B617249 : Blo 409770 617249 := bstep (se 2 (by rfl) ⟨231468, by rfl⟩ : syracuseStep 617249 = 462937) B462937
theorem B617267 : Blo 409770 617267 := bstep (se 1 (by rfl) ⟨462950, by rfl⟩ : syracuseStep 617267 = 925901) B925901
theorem B617297 : Blo 409770 617297 := bstep (se 2 (by rfl) ⟨231486, by rfl⟩ : syracuseStep 617297 = 462973) B462973
theorem B617315 : Blo 409770 617315 := bstep (se 1 (by rfl) ⟨462986, by rfl⟩ : syracuseStep 617315 = 925973) B925973
theorem B617345 : Blo 409770 617345 := bstep (se 2 (by rfl) ⟨231504, by rfl⟩ : syracuseStep 617345 = 463009) B463009
theorem B519043 : Blo 409770 519043 := bstep (se 1 (by rfl) ⟨389282, by rfl⟩ : syracuseStep 519043 = 778565) B778565
theorem B617363 : Blo 409770 617363 := bstep (se 1 (by rfl) ⟨463022, by rfl⟩ : syracuseStep 617363 = 926045) B926045
theorem B617393 : Blo 409770 617393 := bstep (se 2 (by rfl) ⟨231522, by rfl⟩ : syracuseStep 617393 = 463045) B463045
theorem B617411 : Blo 409770 617411 := bstep (se 1 (by rfl) ⟨463058, by rfl⟩ : syracuseStep 617411 = 926117) B926117
theorem B2812877 : Blo 409770 2812877 := bstep (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) B1054829
theorem B617441 : Blo 409770 617441 := bstep (se 2 (by rfl) ⟨231540, by rfl⟩ : syracuseStep 617441 = 463081) B463081
theorem B519139 : Blo 409770 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B617459 : Blo 409770 617459 := bstep (se 1 (by rfl) ⟨463094, by rfl⟩ : syracuseStep 617459 = 926189) B926189
theorem B879619 : Blo 409770 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B617489 : Blo 409770 617489 := bstep (se 2 (by rfl) ⟨231558, by rfl⟩ : syracuseStep 617489 = 463117) B463117
theorem B617507 : Blo 409770 617507 := bstep (se 1 (by rfl) ⟨463130, by rfl⟩ : syracuseStep 617507 = 926261) B926261
theorem B2092067 : Blo 409770 2092067 := bstep (se 1 (by rfl) ⟨1569050, by rfl⟩ : syracuseStep 2092067 = 3138101) B3138101
theorem B617537 : Blo 409770 617537 := bstep (se 2 (by rfl) ⟨231576, by rfl⟩ : syracuseStep 617537 = 463153) B463153
theorem B617555 : Blo 409770 617555 := bstep (se 1 (by rfl) ⟨463166, by rfl⟩ : syracuseStep 617555 = 926333) B926333
theorem B617585 : Blo 409770 617585 := bstep (se 2 (by rfl) ⟨231594, by rfl⟩ : syracuseStep 617585 = 463189) B463189
theorem B617603 : Blo 409770 617603 := bstep (se 1 (by rfl) ⟨463202, by rfl⟩ : syracuseStep 617603 = 926405) B926405
theorem B617633 : Blo 409770 617633 := bstep (se 2 (by rfl) ⟨231612, by rfl⟩ : syracuseStep 617633 = 463225) B463225
theorem B617651 : Blo 409770 617651 := bstep (se 1 (by rfl) ⟨463238, by rfl⟩ : syracuseStep 617651 = 926477) B926477
theorem B617681 : Blo 409770 617681 := bstep (se 2 (by rfl) ⟨231630, by rfl⟩ : syracuseStep 617681 = 463261) B463261
theorem B617699 : Blo 409770 617699 := bstep (se 1 (by rfl) ⟨463274, by rfl⟩ : syracuseStep 617699 = 926549) B926549
theorem B617729 : Blo 409770 617729 := bstep (se 2 (by rfl) ⟨231648, by rfl⟩ : syracuseStep 617729 = 463297) B463297
theorem B584977 : Blo 409770 584977 := bstep (se 2 (by rfl) ⟨219366, by rfl⟩ : syracuseStep 584977 = 438733) B438733
theorem B617747 : Blo 409770 617747 := bstep (se 1 (by rfl) ⟨463310, by rfl⟩ : syracuseStep 617747 = 926621) B926621
theorem B1404209 : Blo 409770 1404209 := bstep (se 2 (by rfl) ⟨526578, by rfl⟩ : syracuseStep 1404209 = 1053157) B1053157
theorem B617777 : Blo 409770 617777 := bstep (se 2 (by rfl) ⟨231666, by rfl⟩ : syracuseStep 617777 = 463333) B463333
theorem B617795 : Blo 409770 617795 := bstep (se 1 (by rfl) ⟨463346, by rfl⟩ : syracuseStep 617795 = 926693) B926693
theorem B617825 : Blo 409770 617825 := bstep (se 2 (by rfl) ⟨231684, by rfl⟩ : syracuseStep 617825 = 463369) B463369
theorem B617843 : Blo 409770 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B585091 : Blo 409770 585091 := bstep (se 1 (by rfl) ⟨438818, by rfl⟩ : syracuseStep 585091 = 877637) B877637
theorem B748945 : Blo 409770 748945 := bstep (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) B561709
theorem B617873 : Blo 409770 617873 := bstep (se 2 (by rfl) ⟨231702, by rfl⟩ : syracuseStep 617873 = 463405) B463405
theorem B617891 : Blo 409770 617891 := bstep (se 1 (by rfl) ⟨463418, by rfl⟩ : syracuseStep 617891 = 926837) B926837
theorem B617921 : Blo 409770 617921 := bstep (se 2 (by rfl) ⟨231720, by rfl⟩ : syracuseStep 617921 = 463441) B463441
theorem B519635 : Blo 409770 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B617939 : Blo 409770 617939 := bstep (se 1 (by rfl) ⟨463454, by rfl⟩ : syracuseStep 617939 = 926909) B926909
theorem B617969 : Blo 409770 617969 := bstep (se 2 (by rfl) ⟨231738, by rfl⟩ : syracuseStep 617969 = 463477) B463477
theorem B617987 : Blo 409770 617987 := bstep (se 1 (by rfl) ⟨463490, by rfl⟩ : syracuseStep 617987 = 926981) B926981
theorem B1175057 : Blo 409770 1175057 := bstep (se 2 (by rfl) ⟨440646, by rfl⟩ : syracuseStep 1175057 = 881293) B881293
theorem B618017 : Blo 409770 618017 := bstep (se 2 (by rfl) ⟨231756, by rfl⟩ : syracuseStep 618017 = 463513) B463513
theorem B618035 : Blo 409770 618035 := bstep (se 1 (by rfl) ⟨463526, by rfl⟩ : syracuseStep 618035 = 927053) B927053
theorem B618065 : Blo 409770 618065 := bstep (se 2 (by rfl) ⟨231774, by rfl⟩ : syracuseStep 618065 = 463549) B463549
theorem B1044049 : Blo 409770 1044049 := bstep (se 2 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 1044049 = 783037) B783037
theorem B618083 : Blo 409770 618083 := bstep (se 1 (by rfl) ⟨463562, by rfl⟩ : syracuseStep 618083 = 927125) B927125
theorem B618113 : Blo 409770 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B618131 : Blo 409770 618131 := bstep (se 1 (by rfl) ⟨463598, by rfl⟩ : syracuseStep 618131 = 927197) B927197
theorem B618161 : Blo 409770 618161 := bstep (se 2 (by rfl) ⟨231810, by rfl⟩ : syracuseStep 618161 = 463621) B463621
theorem B618179 : Blo 409770 618179 := bstep (se 1 (by rfl) ⟨463634, by rfl⟩ : syracuseStep 618179 = 927269) B927269
theorem B618209 : Blo 409770 618209 := bstep (se 2 (by rfl) ⟨231828, by rfl⟩ : syracuseStep 618209 = 463657) B463657
theorem B782065 : Blo 409770 782065 := bstep (se 2 (by rfl) ⟨293274, by rfl⟩ : syracuseStep 782065 = 586549) B586549
theorem B618227 : Blo 409770 618227 := bstep (se 1 (by rfl) ⟨463670, by rfl⟩ : syracuseStep 618227 = 927341) B927341
theorem B3960589 : Blo 409770 3960589 := bstep (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) B1485221
theorem B618257 : Blo 409770 618257 := bstep (se 2 (by rfl) ⟨231846, by rfl⟩ : syracuseStep 618257 = 463693) B463693
theorem B618275 : Blo 409770 618275 := bstep (se 1 (by rfl) ⟨463706, by rfl⟩ : syracuseStep 618275 = 927413) B927413
theorem B618305 : Blo 409770 618305 := bstep (se 2 (by rfl) ⟨231864, by rfl⟩ : syracuseStep 618305 = 463729) B463729
theorem B2092877 : Blo 409770 2092877 := bstep (se 3 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 2092877 = 784829) B784829
theorem B880465 : Blo 409770 880465 := bstep (se 2 (by rfl) ⟨330174, by rfl⟩ : syracuseStep 880465 = 660349) B660349
theorem B618323 : Blo 409770 618323 := bstep (se 1 (by rfl) ⟨463742, by rfl⟩ : syracuseStep 618323 = 927485) B927485
theorem B1044323 : Blo 409770 1044323 := bstep (se 1 (by rfl) ⟨783242, by rfl⟩ : syracuseStep 1044323 = 1566485) B1566485
theorem B618353 : Blo 409770 618353 := bstep (se 2 (by rfl) ⟨231882, by rfl⟩ : syracuseStep 618353 = 463765) B463765
theorem B618371 : Blo 409770 618371 := bstep (se 1 (by rfl) ⟨463778, by rfl⟩ : syracuseStep 618371 = 927557) B927557
theorem B618401 : Blo 409770 618401 := bstep (se 2 (by rfl) ⟨231900, by rfl⟩ : syracuseStep 618401 = 463801) B463801
theorem B618419 : Blo 409770 618419 := bstep (se 1 (by rfl) ⟨463814, by rfl⟩ : syracuseStep 618419 = 927629) B927629
theorem B1568717 : Blo 409770 1568717 := bstep (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) B588269
theorem B618449 : Blo 409770 618449 := bstep (se 2 (by rfl) ⟨231918, by rfl⟩ : syracuseStep 618449 = 463837) B463837
theorem B618467 : Blo 409770 618467 := bstep (se 1 (by rfl) ⟨463850, by rfl⟩ : syracuseStep 618467 = 927701) B927701
theorem B618497 : Blo 409770 618497 := bstep (se 2 (by rfl) ⟨231936, by rfl⟩ : syracuseStep 618497 = 463873) B463873
theorem B618515 : Blo 409770 618515 := bstep (se 1 (by rfl) ⟨463886, by rfl⟩ : syracuseStep 618515 = 927773) B927773
theorem B1044515 : Blo 409770 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B618545 : Blo 409770 618545 := bstep (se 2 (by rfl) ⟨231954, by rfl⟩ : syracuseStep 618545 = 463909) B463909
theorem B618563 : Blo 409770 618563 := bstep (se 1 (by rfl) ⟨463922, by rfl⟩ : syracuseStep 618563 = 927845) B927845
theorem B618593 : Blo 409770 618593 := bstep (se 2 (by rfl) ⟨231972, by rfl⟩ : syracuseStep 618593 = 463945) B463945
theorem B618611 : Blo 409770 618611 := bstep (se 1 (by rfl) ⟨463958, by rfl⟩ : syracuseStep 618611 = 927917) B927917
theorem B618641 : Blo 409770 618641 := bstep (se 2 (by rfl) ⟨231990, by rfl⟩ : syracuseStep 618641 = 463981) B463981
theorem B520339 : Blo 409770 520339 := bstep (se 1 (by rfl) ⟨390254, by rfl⟩ : syracuseStep 520339 = 780509) B780509
theorem B618659 : Blo 409770 618659 := bstep (se 1 (by rfl) ⟨463994, by rfl⟩ : syracuseStep 618659 = 927989) B927989
theorem B618689 : Blo 409770 618689 := bstep (se 2 (by rfl) ⟨232008, by rfl⟩ : syracuseStep 618689 = 464017) B464017
theorem B3502277 : Blo 409770 3502277 := bstep (se 4 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 3502277 = 656677) B656677
theorem B618707 : Blo 409770 618707 := bstep (se 1 (by rfl) ⟨464030, by rfl⟩ : syracuseStep 618707 = 928061) B928061
theorem B618737 : Blo 409770 618737 := bstep (se 2 (by rfl) ⟨232026, by rfl⟩ : syracuseStep 618737 = 464053) B464053
theorem B520435 : Blo 409770 520435 := bstep (se 1 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 520435 = 780653) B780653
theorem B618755 : Blo 409770 618755 := bstep (se 1 (by rfl) ⟨464066, by rfl⟩ : syracuseStep 618755 = 928133) B928133
theorem B618785 : Blo 409770 618785 := bstep (se 2 (by rfl) ⟨232044, by rfl⟩ : syracuseStep 618785 = 464089) B464089
theorem B618803 : Blo 409770 618803 := bstep (se 1 (by rfl) ⟨464102, by rfl⟩ : syracuseStep 618803 = 928205) B928205
theorem B1667405 : Blo 409770 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B618833 : Blo 409770 618833 := bstep (se 2 (by rfl) ⟨232062, by rfl⟩ : syracuseStep 618833 = 464125) B464125
theorem B618851 : Blo 409770 618851 := bstep (se 1 (by rfl) ⟨464138, by rfl⟩ : syracuseStep 618851 = 928277) B928277
theorem B618881 : Blo 409770 618881 := bstep (se 2 (by rfl) ⟨232080, by rfl⟩ : syracuseStep 618881 = 464161) B464161
theorem B618899 : Blo 409770 618899 := bstep (se 1 (by rfl) ⟨464174, by rfl⟩ : syracuseStep 618899 = 928349) B928349
theorem B618929 : Blo 409770 618929 := bstep (se 2 (by rfl) ⟨232098, by rfl⟩ : syracuseStep 618929 = 464197) B464197
theorem B618947 : Blo 409770 618947 := bstep (se 1 (by rfl) ⟨464210, by rfl⟩ : syracuseStep 618947 = 928421) B928421
theorem B2224589 : Blo 409770 2224589 := bstep (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) B834221
theorem B618977 : Blo 409770 618977 := bstep (se 2 (by rfl) ⟨232116, by rfl⟩ : syracuseStep 618977 = 464233) B464233
theorem B618995 : Blo 409770 618995 := bstep (se 1 (by rfl) ⟨464246, by rfl⟩ : syracuseStep 618995 = 928493) B928493
theorem B1765901 : Blo 409770 1765901 := bstep (se 3 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 1765901 = 662213) B662213
theorem B619025 : Blo 409770 619025 := bstep (se 2 (by rfl) ⟨232134, by rfl⟩ : syracuseStep 619025 = 464269) B464269
theorem B619043 : Blo 409770 619043 := bstep (se 1 (by rfl) ⟨464282, by rfl⟩ : syracuseStep 619043 = 928565) B928565
theorem B619073 : Blo 409770 619073 := bstep (se 2 (by rfl) ⟨232152, by rfl⟩ : syracuseStep 619073 = 464305) B464305
theorem B619091 : Blo 409770 619091 := bstep (se 1 (by rfl) ⟨464318, by rfl⟩ : syracuseStep 619091 = 928637) B928637
theorem B619121 : Blo 409770 619121 := bstep (se 2 (by rfl) ⟨232170, by rfl⟩ : syracuseStep 619121 = 464341) B464341
theorem B619139 : Blo 409770 619139 := bstep (se 1 (by rfl) ⟨464354, by rfl⟩ : syracuseStep 619139 = 928709) B928709
theorem B619169 : Blo 409770 619169 := bstep (se 2 (by rfl) ⟨232188, by rfl⟩ : syracuseStep 619169 = 464377) B464377
theorem B1340081 : Blo 409770 1340081 := bstep (se 2 (by rfl) ⟨502530, by rfl⟩ : syracuseStep 1340081 = 1005061) B1005061
theorem B619187 : Blo 409770 619187 := bstep (se 1 (by rfl) ⟨464390, by rfl⟩ : syracuseStep 619187 = 928781) B928781
theorem B586435 : Blo 409770 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B619217 : Blo 409770 619217 := bstep (se 2 (by rfl) ⟨232206, by rfl⟩ : syracuseStep 619217 = 464413) B464413
theorem B520931 : Blo 409770 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B619235 : Blo 409770 619235 := bstep (se 1 (by rfl) ⟨464426, by rfl⟩ : syracuseStep 619235 = 928853) B928853
theorem B619265 : Blo 409770 619265 := bstep (se 2 (by rfl) ⟨232224, by rfl⟩ : syracuseStep 619265 = 464449) B464449
theorem B783121 : Blo 409770 783121 := bstep (se 2 (by rfl) ⟨293670, by rfl⟩ : syracuseStep 783121 = 587341) B587341
theorem B619283 : Blo 409770 619283 := bstep (se 1 (by rfl) ⟨464462, by rfl⟩ : syracuseStep 619283 = 928925) B928925
theorem B619313 : Blo 409770 619313 := bstep (se 2 (by rfl) ⟨232242, by rfl⟩ : syracuseStep 619313 = 464485) B464485
theorem B5206837 : Blo 409770 5206837 := bstep (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) B488141
theorem B619331 : Blo 409770 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B2356037 : Blo 409770 2356037 := bstep (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) B441757
theorem B619361 : Blo 409770 619361 := bstep (se 2 (by rfl) ⟨232260, by rfl⟩ : syracuseStep 619361 = 464521) B464521
theorem B619379 : Blo 409770 619379 := bstep (se 1 (by rfl) ⟨464534, by rfl⟩ : syracuseStep 619379 = 929069) B929069
theorem B619409 : Blo 409770 619409 := bstep (se 2 (by rfl) ⟨232278, by rfl⟩ : syracuseStep 619409 = 464557) B464557
theorem B619427 : Blo 409770 619427 := bstep (se 1 (by rfl) ⟨464570, by rfl⟩ : syracuseStep 619427 = 929141) B929141
theorem B619457 : Blo 409770 619457 := bstep (se 2 (by rfl) ⟨232296, by rfl⟩ : syracuseStep 619457 = 464593) B464593
theorem B1176515 : Blo 409770 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B1045457 : Blo 409770 1045457 := bstep (se 2 (by rfl) ⟨392046, by rfl⟩ : syracuseStep 1045457 = 784093) B784093
theorem B619475 : Blo 409770 619475 := bstep (se 1 (by rfl) ⟨464606, by rfl⟩ : syracuseStep 619475 = 929213) B929213
theorem B553969 : Blo 409770 553969 := bstep (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) B415477
theorem B619505 : Blo 409770 619505 := bstep (se 2 (by rfl) ⟨232314, by rfl⟩ : syracuseStep 619505 = 464629) B464629
theorem B619523 : Blo 409770 619523 := bstep (se 1 (by rfl) ⟨464642, by rfl⟩ : syracuseStep 619523 = 929285) B929285
theorem B1045507 : Blo 409770 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B619553 : Blo 409770 619553 := bstep (se 2 (by rfl) ⟨232332, by rfl⟩ : syracuseStep 619553 = 464665) B464665
theorem B619571 : Blo 409770 619571 := bstep (se 1 (by rfl) ⟨464678, by rfl⟩ : syracuseStep 619571 = 929357) B929357
theorem B619601 : Blo 409770 619601 := bstep (se 2 (by rfl) ⟨232350, by rfl⟩ : syracuseStep 619601 = 464701) B464701
theorem B619619 : Blo 409770 619619 := bstep (se 1 (by rfl) ⟨464714, by rfl⟩ : syracuseStep 619619 = 929429) B929429
theorem B2290801 : Blo 409770 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B619649 : Blo 409770 619649 := bstep (se 2 (by rfl) ⟨232368, by rfl⟩ : syracuseStep 619649 = 464737) B464737
theorem B1045649 : Blo 409770 1045649 := bstep (se 2 (by rfl) ⟨392118, by rfl⟩ : syracuseStep 1045649 = 784237) B784237
theorem B619667 : Blo 409770 619667 := bstep (se 1 (by rfl) ⟨464750, by rfl⟩ : syracuseStep 619667 = 929501) B929501
theorem B783523 : Blo 409770 783523 := bstep (se 1 (by rfl) ⟨587642, by rfl⟩ : syracuseStep 783523 = 1175285) B1175285
theorem B619697 : Blo 409770 619697 := bstep (se 2 (by rfl) ⟨232386, by rfl⟩ : syracuseStep 619697 = 464773) B464773
theorem B619715 : Blo 409770 619715 := bstep (se 1 (by rfl) ⟨464786, by rfl⟩ : syracuseStep 619715 = 929573) B929573
theorem B783569 : Blo 409770 783569 := bstep (se 2 (by rfl) ⟨293838, by rfl⟩ : syracuseStep 783569 = 587677) B587677
theorem B619745 : Blo 409770 619745 := bstep (se 2 (by rfl) ⟨232404, by rfl⟩ : syracuseStep 619745 = 464809) B464809
theorem B619763 : Blo 409770 619763 := bstep (se 1 (by rfl) ⟨464822, by rfl⟩ : syracuseStep 619763 = 929645) B929645
theorem B619793 : Blo 409770 619793 := bstep (se 2 (by rfl) ⟨232422, by rfl⟩ : syracuseStep 619793 = 464845) B464845
theorem B619811 : Blo 409770 619811 := bstep (se 1 (by rfl) ⟨464858, by rfl⟩ : syracuseStep 619811 = 929717) B929717
theorem B619841 : Blo 409770 619841 := bstep (se 2 (by rfl) ⟨232440, by rfl⟩ : syracuseStep 619841 = 464881) B464881
theorem B619859 : Blo 409770 619859 := bstep (se 1 (by rfl) ⟨464894, by rfl⟩ : syracuseStep 619859 = 929789) B929789
theorem B619889 : Blo 409770 619889 := bstep (se 2 (by rfl) ⟨232458, by rfl⟩ : syracuseStep 619889 = 464917) B464917
theorem B619907 : Blo 409770 619907 := bstep (se 1 (by rfl) ⟨464930, by rfl⟩ : syracuseStep 619907 = 929861) B929861
theorem B619937 : Blo 409770 619937 := bstep (se 2 (by rfl) ⟨232476, by rfl⟩ : syracuseStep 619937 = 464953) B464953
theorem B521635 : Blo 409770 521635 := bstep (se 1 (by rfl) ⟨391226, by rfl⟩ : syracuseStep 521635 = 782453) B782453
theorem B619955 : Blo 409770 619955 := bstep (se 1 (by rfl) ⟨464966, by rfl⟩ : syracuseStep 619955 = 929933) B929933
theorem B619985 : Blo 409770 619985 := bstep (se 2 (by rfl) ⟨232494, by rfl⟩ : syracuseStep 619985 = 464989) B464989
theorem B620003 : Blo 409770 620003 := bstep (se 1 (by rfl) ⟨465002, by rfl⟩ : syracuseStep 620003 = 930005) B930005
theorem B783857 : Blo 409770 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B620033 : Blo 409770 620033 := bstep (se 2 (by rfl) ⟨232512, by rfl⟩ : syracuseStep 620033 = 465025) B465025
theorem B521731 : Blo 409770 521731 := bstep (se 1 (by rfl) ⟨391298, by rfl⟩ : syracuseStep 521731 = 782597) B782597
theorem B620051 : Blo 409770 620051 := bstep (se 1 (by rfl) ⟨465038, by rfl⟩ : syracuseStep 620051 = 930077) B930077
theorem B620081 : Blo 409770 620081 := bstep (se 2 (by rfl) ⟨232530, by rfl⟩ : syracuseStep 620081 = 465061) B465061
theorem B620099 : Blo 409770 620099 := bstep (se 1 (by rfl) ⟨465074, by rfl⟩ : syracuseStep 620099 = 930149) B930149
theorem B620129 : Blo 409770 620129 := bstep (se 2 (by rfl) ⟨232548, by rfl⟩ : syracuseStep 620129 = 465097) B465097
theorem B620147 : Blo 409770 620147 := bstep (se 1 (by rfl) ⟨465110, by rfl⟩ : syracuseStep 620147 = 930221) B930221
theorem B620177 : Blo 409770 620177 := bstep (se 2 (by rfl) ⟨232566, by rfl⟩ : syracuseStep 620177 = 465133) B465133
theorem B620195 : Blo 409770 620195 := bstep (se 1 (by rfl) ⟨465146, by rfl⟩ : syracuseStep 620195 = 930293) B930293
theorem B882353 : Blo 409770 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B620225 : Blo 409770 620225 := bstep (se 2 (by rfl) ⟨232584, by rfl⟩ : syracuseStep 620225 = 465169) B465169
theorem B620243 : Blo 409770 620243 := bstep (se 1 (by rfl) ⟨465182, by rfl⟩ : syracuseStep 620243 = 930365) B930365
theorem B1177325 : Blo 409770 1177325 := bstep (se 3 (by rfl) ⟨220748, by rfl⟩ : syracuseStep 1177325 = 441497) B441497
theorem B620273 : Blo 409770 620273 := bstep (se 2 (by rfl) ⟨232602, by rfl⟩ : syracuseStep 620273 = 465205) B465205
theorem B620291 : Blo 409770 620291 := bstep (se 1 (by rfl) ⟨465218, by rfl⟩ : syracuseStep 620291 = 930437) B930437
theorem B620321 : Blo 409770 620321 := bstep (se 2 (by rfl) ⟨232620, by rfl⟩ : syracuseStep 620321 = 465241) B465241
theorem B587569 : Blo 409770 587569 := bstep (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) B440677
theorem B1767217 : Blo 409770 1767217 := bstep (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) B1325413
theorem B620339 : Blo 409770 620339 := bstep (se 1 (by rfl) ⟨465254, by rfl⟩ : syracuseStep 620339 = 930509) B930509
theorem B620369 : Blo 409770 620369 := bstep (se 2 (by rfl) ⟨232638, by rfl⟩ : syracuseStep 620369 = 465277) B465277
theorem B620387 : Blo 409770 620387 := bstep (se 1 (by rfl) ⟨465290, by rfl⟩ : syracuseStep 620387 = 930581) B930581
theorem B620417 : Blo 409770 620417 := bstep (se 2 (by rfl) ⟨232656, by rfl⟩ : syracuseStep 620417 = 465313) B465313
theorem B587665 : Blo 409770 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B620435 : Blo 409770 620435 := bstep (se 1 (by rfl) ⟨465326, by rfl⟩ : syracuseStep 620435 = 930653) B930653
theorem B1177517 : Blo 409770 1177517 := bstep (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) B441569
theorem B620465 : Blo 409770 620465 := bstep (se 2 (by rfl) ⟨232674, by rfl⟩ : syracuseStep 620465 = 465349) B465349
theorem B620483 : Blo 409770 620483 := bstep (se 1 (by rfl) ⟨465362, by rfl⟩ : syracuseStep 620483 = 930725) B930725
theorem B620513 : Blo 409770 620513 := bstep (se 2 (by rfl) ⟨232692, by rfl⟩ : syracuseStep 620513 = 465385) B465385
theorem B522227 : Blo 409770 522227 := bstep (se 1 (by rfl) ⟨391670, by rfl⟩ : syracuseStep 522227 = 783341) B783341
theorem B620531 : Blo 409770 620531 := bstep (se 1 (by rfl) ⟨465398, by rfl⟩ : syracuseStep 620531 = 930797) B930797
theorem B620561 : Blo 409770 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B620579 : Blo 409770 620579 := bstep (se 1 (by rfl) ⟨465434, by rfl⟩ : syracuseStep 620579 = 930869) B930869
theorem B620609 : Blo 409770 620609 := bstep (se 2 (by rfl) ⟨232728, by rfl⟩ : syracuseStep 620609 = 465457) B465457
theorem B620627 : Blo 409770 620627 := bstep (se 1 (by rfl) ⟨465470, by rfl⟩ : syracuseStep 620627 = 930941) B930941
theorem B1046641 : Blo 409770 1046641 := bstep (se 2 (by rfl) ⟨392490, by rfl⟩ : syracuseStep 1046641 = 784981) B784981
theorem B555185 : Blo 409770 555185 := bstep (se 2 (by rfl) ⟨208194, by rfl⟩ : syracuseStep 555185 = 416389) B416389
theorem B784579 : Blo 409770 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B555283 : Blo 409770 555283 := bstep (se 1 (by rfl) ⟨416462, by rfl⟩ : syracuseStep 555283 = 832925) B832925
theorem B588161 : Blo 409770 588161 := bstep (se 2 (by rfl) ⟨220560, by rfl⟩ : syracuseStep 588161 = 441121) B441121
theorem B1046915 : Blo 409770 1046915 := bstep (se 1 (by rfl) ⟨785186, by rfl⟩ : syracuseStep 1046915 = 1570373) B1570373
theorem B1047107 : Blo 409770 1047107 := bstep (se 1 (by rfl) ⟨785330, by rfl⟩ : syracuseStep 1047107 = 1570661) B1570661
theorem B785027 : Blo 409770 785027 := bstep (se 1 (by rfl) ⟨588770, by rfl⟩ : syracuseStep 785027 = 1177541) B1177541
theorem B522931 : Blo 409770 522931 := bstep (se 1 (by rfl) ⟨392198, by rfl⟩ : syracuseStep 522931 = 784397) B784397
theorem B523027 : Blo 409770 523027 := bstep (se 1 (by rfl) ⟨392270, by rfl⟩ : syracuseStep 523027 = 784541) B784541
theorem B785315 : Blo 409770 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B883651 : Blo 409770 883651 := bstep (se 1 (by rfl) ⟨662738, by rfl⟩ : syracuseStep 883651 = 1325477) B1325477
theorem B4062221 : Blo 409770 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B2817251 : Blo 409770 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B589027 : Blo 409770 589027 := bstep (se 1 (by rfl) ⟨441770, by rfl⟩ : syracuseStep 589027 = 883541) B883541
theorem B523523 : Blo 409770 523523 := bstep (se 1 (by rfl) ⟨392642, by rfl⟩ : syracuseStep 523523 = 785285) B785285
theorem B1113389 : Blo 409770 1113389 := bstep (se 3 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 1113389 = 417521) B417521
theorem B589123 : Blo 409770 589123 := bstep (se 1 (by rfl) ⟨441842, by rfl⟩ : syracuseStep 589123 = 883685) B883685
theorem B2227661 : Blo 409770 2227661 := bstep (se 3 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 2227661 = 835373) B835373
theorem B3604337 : Blo 409770 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B1343405 : Blo 409770 1343405 := bstep (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) B503777
theorem B1409501 : Blo 409770 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B2851421 : Blo 409770 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B1114717 : Blo 409770 1114717 := bstep (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) B418019
theorem B8422019 : Blo 409770 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B1114955 : Blo 409770 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B1672109 : Blo 409770 1672109 := bstep (se 3 (by rfl) ⟨313520, by rfl⟩ : syracuseStep 1672109 = 627041) B627041
theorem B5932237 : Blo 409770 5932237 := bstep (se 3 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 5932237 = 2224589) B2224589
theorem B984727 : Blo 409770 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B3180305 : Blo 409770 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B1115993 : Blo 409770 1115993 := bstep (se 2 (by rfl) ⟨418497, by rfl⟩ : syracuseStep 1115993 = 836995) B836995
theorem B2819933 : Blo 409770 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B657433 : Blo 409770 657433 := bstep (se 2 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 657433 = 493075) B493075
theorem B1312919 : Blo 409770 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B3967127 : Blo 409770 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B461047 : Blo 409770 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B6850861 : Blo 409770 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B592267 : Blo 409770 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B461227 : Blo 409770 461227 := bstep (se 1 (by rfl) ⟨345920, by rfl⟩ : syracuseStep 461227 = 691841) B691841
theorem B461335 : Blo 409770 461335 := bstep (se 1 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 461335 = 692003) B692003
theorem B461515 : Blo 409770 461515 := bstep (se 1 (by rfl) ⟨346136, by rfl⟩ : syracuseStep 461515 = 692273) B692273
theorem B1477379 : Blo 409770 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B461623 : Blo 409770 461623 := bstep (se 1 (by rfl) ⟨346217, by rfl⟩ : syracuseStep 461623 = 692435) B692435
theorem B50760665 : Blo 409770 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B461803 : Blo 409770 461803 := bstep (se 1 (by rfl) ⟨346352, by rfl⟩ : syracuseStep 461803 = 692705) B692705
theorem B461911 : Blo 409770 461911 := bstep (se 1 (by rfl) ⟨346433, by rfl⟩ : syracuseStep 461911 = 692867) B692867
theorem B1313995 : Blo 409770 1313995 := bstep (se 1 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 1313995 = 1970993) B1970993
theorem B462091 : Blo 409770 462091 := bstep (se 1 (by rfl) ⟨346568, by rfl⟩ : syracuseStep 462091 = 693137) B693137
theorem B1314137 : Blo 409770 1314137 := bstep (se 2 (by rfl) ⟨492801, by rfl⟩ : syracuseStep 1314137 = 985603) B985603
theorem B462199 : Blo 409770 462199 := bstep (se 1 (by rfl) ⟨346649, by rfl⟩ : syracuseStep 462199 = 693299) B693299
theorem B462379 : Blo 409770 462379 := bstep (se 1 (by rfl) ⟨346784, by rfl⟩ : syracuseStep 462379 = 693569) B693569
theorem B691787 : Blo 409770 691787 := bstep (se 1 (by rfl) ⟨518840, by rfl⟩ : syracuseStep 691787 = 1037681) B1037681
theorem B462487 : Blo 409770 462487 := bstep (se 1 (by rfl) ⟨346865, by rfl⟩ : syracuseStep 462487 = 693731) B693731
theorem B691915 : Blo 409770 691915 := bstep (se 1 (by rfl) ⟨518936, by rfl⟩ : syracuseStep 691915 = 1037873) B1037873
theorem B462667 : Blo 409770 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B692057 : Blo 409770 692057 := bstep (se 2 (by rfl) ⟨259521, by rfl⟩ : syracuseStep 692057 = 519043) B519043
theorem B462775 : Blo 409770 462775 := bstep (se 1 (by rfl) ⟨347081, by rfl⟩ : syracuseStep 462775 = 694163) B694163
theorem B692185 : Blo 409770 692185 := bstep (se 2 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 692185 = 519139) B519139
theorem B462955 : Blo 409770 462955 := bstep (se 1 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 462955 = 694433) B694433
theorem B463063 : Blo 409770 463063 := bstep (se 1 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 463063 = 694595) B694595
theorem B2232593 : Blo 409770 2232593 := bstep (se 2 (by rfl) ⟨837222, by rfl⟩ : syracuseStep 2232593 = 1674445) B1674445
theorem B2232677 : Blo 409770 2232677 := bstep (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) B418627
theorem B19960181 : Blo 409770 19960181 := bstep (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) B1871267
theorem B3019139 : Blo 409770 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B921995 : Blo 409770 921995 := bstep (se 1 (by rfl) ⟨691496, by rfl⟩ : syracuseStep 921995 = 1382993) B1382993
theorem B463243 : Blo 409770 463243 := bstep (se 1 (by rfl) ⟨347432, by rfl⟩ : syracuseStep 463243 = 694865) B694865
theorem B922049 : Blo 409770 922049 := bstep (se 2 (by rfl) ⟨345768, by rfl⟩ : syracuseStep 922049 = 691537) B691537
theorem B463351 : Blo 409770 463351 := bstep (se 1 (by rfl) ⟨347513, by rfl⟩ : syracuseStep 463351 = 695027) B695027
theorem B692759 : Blo 409770 692759 := bstep (se 1 (by rfl) ⟨519569, by rfl⟩ : syracuseStep 692759 = 1039139) B1039139
theorem B1315379 : Blo 409770 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B692887 : Blo 409770 692887 := bstep (se 1 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 692887 = 1039331) B1039331
theorem B922265 : Blo 409770 922265 := bstep (se 2 (by rfl) ⟨345849, by rfl⟩ : syracuseStep 922265 = 691699) B691699
theorem B463531 : Blo 409770 463531 := bstep (se 1 (by rfl) ⟨347648, by rfl⟩ : syracuseStep 463531 = 695297) B695297
theorem B922355 : Blo 409770 922355 := bstep (se 1 (by rfl) ⟨691766, by rfl⟩ : syracuseStep 922355 = 1383533) B1383533
theorem B922391 : Blo 409770 922391 := bstep (se 1 (by rfl) ⟨691793, by rfl⟩ : syracuseStep 922391 = 1383587) B1383587
theorem B463639 : Blo 409770 463639 := bstep (se 1 (by rfl) ⟨347729, by rfl⟩ : syracuseStep 463639 = 695459) B695459
theorem B4002625 : Blo 409770 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B1315777 : Blo 409770 1315777 := bstep (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) B986833
theorem B922571 : Blo 409770 922571 := bstep (se 1 (by rfl) ⟨691928, by rfl⟩ : syracuseStep 922571 = 1383857) B1383857
theorem B463819 : Blo 409770 463819 := bstep (se 1 (by rfl) ⟨347864, by rfl⟩ : syracuseStep 463819 = 695729) B695729
theorem B922625 : Blo 409770 922625 := bstep (se 2 (by rfl) ⟨345984, by rfl⟩ : syracuseStep 922625 = 691969) B691969
theorem B5280785 : Blo 409770 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B463927 : Blo 409770 463927 := bstep (se 1 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 463927 = 695891) B695891
theorem B922841 : Blo 409770 922841 := bstep (se 2 (by rfl) ⟨346065, by rfl⟩ : syracuseStep 922841 = 692131) B692131
theorem B464107 : Blo 409770 464107 := bstep (se 1 (by rfl) ⟨348080, by rfl⟩ : syracuseStep 464107 = 696161) B696161
theorem B2954501 : Blo 409770 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B693515 : Blo 409770 693515 := bstep (se 1 (by rfl) ⟨520136, by rfl⟩ : syracuseStep 693515 = 1040273) B1040273
theorem B496919 : Blo 409770 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B922931 : Blo 409770 922931 := bstep (se 1 (by rfl) ⟨692198, by rfl⟩ : syracuseStep 922931 = 1384397) B1384397
theorem B922967 : Blo 409770 922967 := bstep (se 1 (by rfl) ⟨692225, by rfl⟩ : syracuseStep 922967 = 1384451) B1384451
theorem B464215 : Blo 409770 464215 := bstep (se 1 (by rfl) ⟨348161, by rfl⟩ : syracuseStep 464215 = 696323) B696323
theorem B693643 : Blo 409770 693643 := bstep (se 1 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 693643 = 1040465) B1040465
theorem B923147 : Blo 409770 923147 := bstep (se 1 (by rfl) ⟨692360, by rfl⟩ : syracuseStep 923147 = 1384721) B1384721
theorem B464395 : Blo 409770 464395 := bstep (se 1 (by rfl) ⟨348296, by rfl⟩ : syracuseStep 464395 = 696593) B696593
theorem B693785 : Blo 409770 693785 := bstep (se 2 (by rfl) ⟨260169, by rfl⟩ : syracuseStep 693785 = 520339) B520339
theorem B923201 : Blo 409770 923201 := bstep (se 2 (by rfl) ⟨346200, by rfl⟩ : syracuseStep 923201 = 692401) B692401
theorem B464503 : Blo 409770 464503 := bstep (se 1 (by rfl) ⟨348377, by rfl⟩ : syracuseStep 464503 = 696755) B696755
theorem B693913 : Blo 409770 693913 := bstep (se 2 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 693913 = 520435) B520435
theorem B923417 : Blo 409770 923417 := bstep (se 2 (by rfl) ⟨346281, by rfl⟩ : syracuseStep 923417 = 692563) B692563
theorem B464683 : Blo 409770 464683 := bstep (se 1 (by rfl) ⟨348512, by rfl⟩ : syracuseStep 464683 = 697025) B697025
theorem B1480493 : Blo 409770 1480493 := bstep (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) B555185
theorem B923507 : Blo 409770 923507 := bstep (se 1 (by rfl) ⟨692630, by rfl⟩ : syracuseStep 923507 = 1385261) B1385261
theorem B923543 : Blo 409770 923543 := bstep (se 1 (by rfl) ⟨692657, by rfl⟩ : syracuseStep 923543 = 1385315) B1385315
theorem B464791 : Blo 409770 464791 := bstep (se 1 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 464791 = 697187) B697187
theorem B923723 : Blo 409770 923723 := bstep (se 1 (by rfl) ⟨692792, by rfl⟩ : syracuseStep 923723 = 1385585) B1385585
theorem B464971 : Blo 409770 464971 := bstep (se 1 (by rfl) ⟨348728, by rfl⟩ : syracuseStep 464971 = 697457) B697457
theorem B923777 : Blo 409770 923777 := bstep (se 2 (by rfl) ⟨346416, by rfl⟩ : syracuseStep 923777 = 692833) B692833
theorem B465079 : Blo 409770 465079 := bstep (se 1 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 465079 = 697619) B697619
theorem B694487 : Blo 409770 694487 := bstep (se 1 (by rfl) ⟨520865, by rfl⟩ : syracuseStep 694487 = 1041731) B1041731
theorem B694615 : Blo 409770 694615 := bstep (se 1 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 694615 = 1041923) B1041923
theorem B923993 : Blo 409770 923993 := bstep (se 2 (by rfl) ⟨346497, by rfl⟩ : syracuseStep 923993 = 692995) B692995
theorem B465259 : Blo 409770 465259 := bstep (se 1 (by rfl) ⟨348944, by rfl⟩ : syracuseStep 465259 = 697889) B697889
theorem B924083 : Blo 409770 924083 := bstep (se 1 (by rfl) ⟨693062, by rfl⟩ : syracuseStep 924083 = 1386125) B1386125
theorem B891329 : Blo 409770 891329 := bstep (se 2 (by rfl) ⟨334248, by rfl⟩ : syracuseStep 891329 = 668497) B668497
theorem B924119 : Blo 409770 924119 := bstep (se 1 (by rfl) ⟨693089, by rfl⟩ : syracuseStep 924119 = 1386179) B1386179
theorem B465367 : Blo 409770 465367 := bstep (se 1 (by rfl) ⟨349025, by rfl⟩ : syracuseStep 465367 = 698051) B698051
theorem B3119633 : Blo 409770 3119633 := bstep (se 2 (by rfl) ⟨1169862, by rfl⟩ : syracuseStep 3119633 = 2339725) B2339725
theorem B924299 : Blo 409770 924299 := bstep (se 1 (by rfl) ⟨693224, by rfl⟩ : syracuseStep 924299 = 1386449) B1386449
theorem B924353 : Blo 409770 924353 := bstep (se 2 (by rfl) ⟨346632, by rfl⟩ : syracuseStep 924353 = 693265) B693265
theorem B2235097 : Blo 409770 2235097 := bstep (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) B1676323
theorem B3054401 : Blo 409770 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B924569 : Blo 409770 924569 := bstep (se 2 (by rfl) ⟨346713, by rfl⟩ : syracuseStep 924569 = 693427) B693427
theorem B1383371 : Blo 409770 1383371 := bstep (se 1 (by rfl) ⟨1037528, by rfl⟩ : syracuseStep 1383371 = 2075057) B2075057
theorem B695243 : Blo 409770 695243 := bstep (se 1 (by rfl) ⟨521432, by rfl⟩ : syracuseStep 695243 = 1042865) B1042865
theorem B924659 : Blo 409770 924659 := bstep (se 1 (by rfl) ⟨693494, by rfl⟩ : syracuseStep 924659 = 1386989) B1386989
theorem B924695 : Blo 409770 924695 := bstep (se 1 (by rfl) ⟨693521, by rfl⟩ : syracuseStep 924695 = 1387043) B1387043
theorem B2628683 : Blo 409770 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B695371 : Blo 409770 695371 := bstep (se 1 (by rfl) ⟨521528, by rfl⟩ : syracuseStep 695371 = 1043057) B1043057
theorem B924875 : Blo 409770 924875 := bstep (se 1 (by rfl) ⟨693656, by rfl⟩ : syracuseStep 924875 = 1387313) B1387313
theorem B1383641 : Blo 409770 1383641 := bstep (se 2 (by rfl) ⟨518865, by rfl⟩ : syracuseStep 1383641 = 1037731) B1037731
theorem B695513 : Blo 409770 695513 := bstep (se 2 (by rfl) ⟨260817, by rfl⟩ : syracuseStep 695513 = 521635) B521635
theorem B924929 : Blo 409770 924929 := bstep (se 2 (by rfl) ⟨346848, by rfl⟩ : syracuseStep 924929 = 693697) B693697
theorem B1875251 : Blo 409770 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B695641 : Blo 409770 695641 := bstep (se 2 (by rfl) ⟨260865, by rfl⟩ : syracuseStep 695641 = 521731) B521731
theorem B925145 : Blo 409770 925145 := bstep (se 2 (by rfl) ⟨346929, by rfl⟩ : syracuseStep 925145 = 693859) B693859
theorem B925235 : Blo 409770 925235 := bstep (se 1 (by rfl) ⟨693926, by rfl⟩ : syracuseStep 925235 = 1387853) B1387853
theorem B925271 : Blo 409770 925271 := bstep (se 1 (by rfl) ⟨693953, by rfl⟩ : syracuseStep 925271 = 1387907) B1387907
theorem B925451 : Blo 409770 925451 := bstep (se 1 (by rfl) ⟨694088, by rfl⟩ : syracuseStep 925451 = 1388177) B1388177
theorem B925505 : Blo 409770 925505 := bstep (se 2 (by rfl) ⟨347064, by rfl⟩ : syracuseStep 925505 = 694129) B694129
theorem B1384343 : Blo 409770 1384343 := bstep (se 1 (by rfl) ⟨1038257, by rfl⟩ : syracuseStep 1384343 = 2076515) B2076515
theorem B696215 : Blo 409770 696215 := bstep (se 1 (by rfl) ⟨522161, by rfl⟩ : syracuseStep 696215 = 1044323) B1044323
theorem B3514373 : Blo 409770 3514373 := bstep (se 4 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 3514373 = 658945) B658945
theorem B696343 : Blo 409770 696343 := bstep (se 1 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 696343 = 1044515) B1044515
theorem B925721 : Blo 409770 925721 := bstep (se 2 (by rfl) ⟨347145, by rfl⟩ : syracuseStep 925721 = 694291) B694291
theorem B925811 : Blo 409770 925811 := bstep (se 1 (by rfl) ⟨694358, by rfl⟩ : syracuseStep 925811 = 1388717) B1388717
theorem B2334851 : Blo 409770 2334851 := bstep (se 1 (by rfl) ⟨1751138, by rfl⟩ : syracuseStep 2334851 = 3502277) B3502277
theorem B925847 : Blo 409770 925847 := bstep (se 1 (by rfl) ⟨694385, by rfl⟩ : syracuseStep 925847 = 1388771) B1388771
theorem B1974451 : Blo 409770 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B926027 : Blo 409770 926027 := bstep (se 1 (by rfl) ⟨694520, by rfl⟩ : syracuseStep 926027 = 1389041) B1389041
theorem B4432229 : Blo 409770 4432229 := bstep (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) B831043
theorem B926081 : Blo 409770 926081 := bstep (se 2 (by rfl) ⟨347280, by rfl⟩ : syracuseStep 926081 = 694561) B694561
theorem B1384883 : Blo 409770 1384883 := bstep (se 1 (by rfl) ⟨1038662, by rfl⟩ : syracuseStep 1384883 = 2077325) B2077325
theorem B6693299 : Blo 409770 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B3350963 : Blo 409770 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B893387 : Blo 409770 893387 := bstep (se 1 (by rfl) ⟨670040, by rfl⟩ : syracuseStep 893387 = 1340081) B1340081
theorem B926297 : Blo 409770 926297 := bstep (se 2 (by rfl) ⟨347361, by rfl⟩ : syracuseStep 926297 = 694723) B694723
theorem B696971 : Blo 409770 696971 := bstep (se 1 (by rfl) ⟨522728, by rfl⟩ : syracuseStep 696971 = 1045457) B1045457
theorem B926387 : Blo 409770 926387 := bstep (se 1 (by rfl) ⟨694790, by rfl⟩ : syracuseStep 926387 = 1389581) B1389581
theorem B1385153 : Blo 409770 1385153 := bstep (se 2 (by rfl) ⟨519432, by rfl⟩ : syracuseStep 1385153 = 1038865) B1038865
theorem B467671 : Blo 409770 467671 := bstep (se 1 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 467671 = 701507) B701507
theorem B926423 : Blo 409770 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B697099 : Blo 409770 697099 := bstep (se 1 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 697099 = 1045649) B1045649
theorem B926603 : Blo 409770 926603 := bstep (se 1 (by rfl) ⟨694952, by rfl⟩ : syracuseStep 926603 = 1389905) B1389905
theorem B2630551 : Blo 409770 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B697241 : Blo 409770 697241 := bstep (se 2 (by rfl) ⟨261465, by rfl⟩ : syracuseStep 697241 = 522931) B522931
theorem B926657 : Blo 409770 926657 := bstep (se 2 (by rfl) ⟨347496, by rfl⟩ : syracuseStep 926657 = 694993) B694993
theorem B697369 : Blo 409770 697369 := bstep (se 2 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 697369 = 523027) B523027
theorem B992321 : Blo 409770 992321 := bstep (se 2 (by rfl) ⟨372120, by rfl⟩ : syracuseStep 992321 = 744241) B744241
theorem B926873 : Blo 409770 926873 := bstep (se 2 (by rfl) ⟨347577, by rfl⟩ : syracuseStep 926873 = 695155) B695155
theorem B1385693 : Blo 409770 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B926963 : Blo 409770 926963 := bstep (se 1 (by rfl) ⟨695222, by rfl⟩ : syracuseStep 926963 = 1390445) B1390445
theorem B926999 : Blo 409770 926999 := bstep (se 1 (by rfl) ⟨695249, by rfl⟩ : syracuseStep 926999 = 1390499) B1390499
theorem B927179 : Blo 409770 927179 := bstep (se 1 (by rfl) ⟨695384, by rfl⟩ : syracuseStep 927179 = 1390769) B1390769
theorem B927233 : Blo 409770 927233 := bstep (se 2 (by rfl) ⟨347712, by rfl⟩ : syracuseStep 927233 = 695425) B695425
theorem B697943 : Blo 409770 697943 := bstep (se 1 (by rfl) ⟨523457, by rfl⟩ : syracuseStep 697943 = 1046915) B1046915
theorem B698071 : Blo 409770 698071 := bstep (se 1 (by rfl) ⟨523553, by rfl⟩ : syracuseStep 698071 = 1047107) B1047107
theorem B927449 : Blo 409770 927449 := bstep (se 2 (by rfl) ⟨347793, by rfl⟩ : syracuseStep 927449 = 695587) B695587
theorem B927539 : Blo 409770 927539 := bstep (se 1 (by rfl) ⟨695654, by rfl⟩ : syracuseStep 927539 = 1391309) B1391309
theorem B927575 : Blo 409770 927575 := bstep (se 1 (by rfl) ⟨695681, by rfl⟩ : syracuseStep 927575 = 1391363) B1391363
theorem B927755 : Blo 409770 927755 := bstep (se 1 (by rfl) ⟨695816, by rfl⟩ : syracuseStep 927755 = 1391633) B1391633
theorem B927809 : Blo 409770 927809 := bstep (se 2 (by rfl) ⟨347928, by rfl⟩ : syracuseStep 927809 = 695857) B695857
theorem B2631781 : Blo 409770 2631781 := bstep (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) B493459
theorem B1878167 : Blo 409770 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B928025 : Blo 409770 928025 := bstep (se 2 (by rfl) ⟨348009, by rfl⟩ : syracuseStep 928025 = 696019) B696019
theorem B3352877 : Blo 409770 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B1485107 : Blo 409770 1485107 := bstep (se 1 (by rfl) ⟨1113830, by rfl⟩ : syracuseStep 1485107 = 2227661) B2227661
theorem B3123521 : Blo 409770 3123521 := bstep (se 2 (by rfl) ⟨1171320, by rfl⟩ : syracuseStep 3123521 = 2342641) B2342641
theorem B1583425 : Blo 409770 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B1386827 : Blo 409770 1386827 := bstep (se 1 (by rfl) ⟨1040120, by rfl⟩ : syracuseStep 1386827 = 2080241) B2080241
theorem B928115 : Blo 409770 928115 := bstep (se 1 (by rfl) ⟨696086, by rfl⟩ : syracuseStep 928115 = 1392173) B1392173
theorem B928151 : Blo 409770 928151 := bstep (se 1 (by rfl) ⟨696113, by rfl⟩ : syracuseStep 928151 = 1392227) B1392227
theorem B3582413 : Blo 409770 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B2402891 : Blo 409770 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B928331 : Blo 409770 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B1387097 : Blo 409770 1387097 := bstep (se 2 (by rfl) ⟨520161, by rfl⟩ : syracuseStep 1387097 = 1040323) B1040323
theorem B928385 : Blo 409770 928385 := bstep (se 2 (by rfl) ⟨348144, by rfl⟩ : syracuseStep 928385 = 696289) B696289
theorem B928601 : Blo 409770 928601 := bstep (se 2 (by rfl) ⟨348225, by rfl⟩ : syracuseStep 928601 = 696451) B696451
theorem B2075543 : Blo 409770 2075543 := bstep (se 1 (by rfl) ⟨1556657, by rfl⟩ : syracuseStep 2075543 = 3113315) B3113315
theorem B928691 : Blo 409770 928691 := bstep (se 1 (by rfl) ⟨696518, by rfl⟩ : syracuseStep 928691 = 1393037) B1393037
theorem B928727 : Blo 409770 928727 := bstep (se 1 (by rfl) ⟨696545, by rfl⟩ : syracuseStep 928727 = 1393091) B1393091
theorem B3353561 : Blo 409770 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B9743435 : Blo 409770 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B1485913 : Blo 409770 1485913 := bstep (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) B1114435
theorem B470135 : Blo 409770 470135 := bstep (se 1 (by rfl) ⟨352601, by rfl⟩ : syracuseStep 470135 = 705203) B705203
theorem B928907 : Blo 409770 928907 := bstep (se 1 (by rfl) ⟨696680, by rfl⟩ : syracuseStep 928907 = 1393361) B1393361
theorem B928961 : Blo 409770 928961 := bstep (se 2 (by rfl) ⟨348360, by rfl⟩ : syracuseStep 928961 = 696721) B696721
theorem B1387799 : Blo 409770 1387799 := bstep (se 1 (by rfl) ⟨1040849, by rfl⟩ : syracuseStep 1387799 = 2081699) B2081699
theorem B3517789 : Blo 409770 3517789 := bstep (se 3 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 3517789 = 1319171) B1319171
theorem B929177 : Blo 409770 929177 := bstep (se 2 (by rfl) ⟨348441, by rfl⟩ : syracuseStep 929177 = 696883) B696883
theorem B929267 : Blo 409770 929267 := bstep (se 1 (by rfl) ⟨696950, by rfl⟩ : syracuseStep 929267 = 1393901) B1393901
theorem B929303 : Blo 409770 929303 := bstep (se 1 (by rfl) ⟨696977, by rfl⟩ : syracuseStep 929303 = 1393955) B1393955
theorem B2666029 : Blo 409770 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B4697675 : Blo 409770 4697675 := bstep (se 1 (by rfl) ⟨3523256, by rfl⟩ : syracuseStep 4697675 = 7046513) B7046513
theorem B1257049 : Blo 409770 1257049 := bstep (se 2 (by rfl) ⟨471393, by rfl⟩ : syracuseStep 1257049 = 942787) B942787
theorem B929483 : Blo 409770 929483 := bstep (se 1 (by rfl) ⟨697112, by rfl⟩ : syracuseStep 929483 = 1394225) B1394225
theorem B929537 : Blo 409770 929537 := bstep (se 2 (by rfl) ⟨348576, by rfl⟩ : syracuseStep 929537 = 697153) B697153
theorem B1486637 : Blo 409770 1486637 := bstep (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) B557489
theorem B1388339 : Blo 409770 1388339 := bstep (se 1 (by rfl) ⟨1041254, by rfl⟩ : syracuseStep 1388339 = 2082509) B2082509
theorem B6762341 : Blo 409770 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B929753 : Blo 409770 929753 := bstep (se 2 (by rfl) ⟨348657, by rfl⟩ : syracuseStep 929753 = 697315) B697315
theorem B929843 : Blo 409770 929843 := bstep (se 1 (by rfl) ⟨697382, by rfl⟩ : syracuseStep 929843 = 1394765) B1394765
theorem B1388609 : Blo 409770 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B929879 : Blo 409770 929879 := bstep (se 1 (by rfl) ⟨697409, by rfl⟩ : syracuseStep 929879 = 1394819) B1394819
theorem B438391 : Blo 409770 438391 := bstep (se 1 (by rfl) ⟨328793, by rfl⟩ : syracuseStep 438391 = 657587) B657587
theorem B3125465 : Blo 409770 3125465 := bstep (se 2 (by rfl) ⟨1172049, by rfl⟩ : syracuseStep 3125465 = 2344099) B2344099
theorem B10170629 : Blo 409770 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B930059 : Blo 409770 930059 := bstep (se 1 (by rfl) ⟨697544, by rfl⟩ : syracuseStep 930059 = 1395089) B1395089
theorem B438571 : Blo 409770 438571 := bstep (se 1 (by rfl) ⟨328928, by rfl⟩ : syracuseStep 438571 = 657857) B657857
theorem B930113 : Blo 409770 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B1814929 : Blo 409770 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B668171 : Blo 409770 668171 := bstep (se 1 (by rfl) ⟨501128, by rfl⟩ : syracuseStep 668171 = 1002257) B1002257
theorem B930329 : Blo 409770 930329 := bstep (se 2 (by rfl) ⟨348873, by rfl⟩ : syracuseStep 930329 = 697747) B697747
theorem B1389149 : Blo 409770 1389149 := bstep (se 3 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 1389149 = 520931) B520931
theorem B930419 : Blo 409770 930419 := bstep (se 1 (by rfl) ⟨697814, by rfl⟩ : syracuseStep 930419 = 1395629) B1395629
theorem B930455 : Blo 409770 930455 := bstep (se 1 (by rfl) ⟨697841, by rfl⟩ : syracuseStep 930455 = 1395683) B1395683
theorem B668377 : Blo 409770 668377 := bstep (se 2 (by rfl) ⟨250641, by rfl⟩ : syracuseStep 668377 = 501283) B501283
theorem B930635 : Blo 409770 930635 := bstep (se 1 (by rfl) ⟨697976, by rfl⟩ : syracuseStep 930635 = 1395953) B1395953
theorem B930689 : Blo 409770 930689 := bstep (se 2 (by rfl) ⟨349008, by rfl⟩ : syracuseStep 930689 = 698017) B698017
theorem B4469681 : Blo 409770 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B930905 : Blo 409770 930905 := bstep (se 2 (by rfl) ⟨349089, by rfl⟩ : syracuseStep 930905 = 698179) B698179
theorem B1324183 : Blo 409770 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B11417219 : Blo 409770 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B1750679 : Blo 409770 1750679 := bstep (se 1 (by rfl) ⟨1313009, by rfl⟩ : syracuseStep 1750679 = 2626019) B2626019
theorem B1390283 : Blo 409770 1390283 := bstep (se 1 (by rfl) ⟨1042712, by rfl⟩ : syracuseStep 1390283 = 2085425) B2085425
theorem B1586891 : Blo 409770 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B2340683 : Blo 409770 2340683 := bstep (se 1 (by rfl) ⟨1755512, by rfl⟩ : syracuseStep 2340683 = 3511025) B3511025
theorem B1390553 : Blo 409770 1390553 := bstep (se 2 (by rfl) ⟨521457, by rfl⟩ : syracuseStep 1390553 = 1042915) B1042915
theorem B6666371 : Blo 409770 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B637067 : Blo 409770 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B440587 : Blo 409770 440587 := bstep (se 1 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 440587 = 660881) B660881
theorem B2505005 : Blo 409770 2505005 := bstep (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) B939377
theorem B2079107 : Blo 409770 2079107 := bstep (se 1 (by rfl) ⟨1559330, by rfl⟩ : syracuseStep 2079107 = 3118661) B3118661
theorem B670295 : Blo 409770 670295 := bstep (se 1 (by rfl) ⟨502721, by rfl⟩ : syracuseStep 670295 = 1005443) B1005443
theorem B1391255 : Blo 409770 1391255 := bstep (se 1 (by rfl) ⟨1043441, by rfl⟩ : syracuseStep 1391255 = 2086883) B2086883
theorem B1391795 : Blo 409770 1391795 := bstep (se 1 (by rfl) ⟨1043846, by rfl⟩ : syracuseStep 1391795 = 2087693) B2087693
theorem B1359155 : Blo 409770 1359155 := bstep (se 1 (by rfl) ⟨1019366, by rfl⟩ : syracuseStep 1359155 = 2038733) B2038733
theorem B1392065 : Blo 409770 1392065 := bstep (se 2 (by rfl) ⟨522024, by rfl⟩ : syracuseStep 1392065 = 1044049) B1044049
theorem B3128867 : Blo 409770 3128867 := bstep (se 1 (by rfl) ⟨2346650, by rfl⟩ : syracuseStep 3128867 = 4693301) B4693301
theorem B1752779 : Blo 409770 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1392605 : Blo 409770 1392605 := bstep (se 3 (by rfl) ⟨261113, by rfl⟩ : syracuseStep 1392605 = 522227) B522227
theorem B1589341 : Blo 409770 1589341 := bstep (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) B596003
theorem B409771 : Blo 409770 409771 := bstep (se 1 (by rfl) ⟨307328, by rfl⟩ : syracuseStep 409771 = 614657) B614657
theorem B409783 : Blo 409770 409783 := bstep (se 1 (by rfl) ⟨307337, by rfl⟩ : syracuseStep 409783 = 614675) B614675
theorem B409803 : Blo 409770 409803 := bstep (se 1 (by rfl) ⟨307352, by rfl⟩ : syracuseStep 409803 = 614705) B614705
theorem B409815 : Blo 409770 409815 := bstep (se 1 (by rfl) ⟨307361, by rfl⟩ : syracuseStep 409815 = 614723) B614723
theorem B409835 : Blo 409770 409835 := bstep (se 1 (by rfl) ⟨307376, by rfl⟩ : syracuseStep 409835 = 614753) B614753
theorem B409847 : Blo 409770 409847 := bstep (se 1 (by rfl) ⟨307385, by rfl⟩ : syracuseStep 409847 = 614771) B614771
theorem B409867 : Blo 409770 409867 := bstep (se 1 (by rfl) ⟨307400, by rfl⟩ : syracuseStep 409867 = 614801) B614801
theorem B409879 : Blo 409770 409879 := bstep (se 1 (by rfl) ⟨307409, by rfl⟩ : syracuseStep 409879 = 614819) B614819
theorem B409899 : Blo 409770 409899 := bstep (se 1 (by rfl) ⟨307424, by rfl⟩ : syracuseStep 409899 = 614849) B614849
theorem B1786157 : Blo 409770 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B409911 : Blo 409770 409911 := bstep (se 1 (by rfl) ⟨307433, by rfl⟩ : syracuseStep 409911 = 614867) B614867
theorem B409931 : Blo 409770 409931 := bstep (se 1 (by rfl) ⟨307448, by rfl⟩ : syracuseStep 409931 = 614897) B614897
theorem B409943 : Blo 409770 409943 := bstep (se 1 (by rfl) ⟨307457, by rfl⟩ : syracuseStep 409943 = 614915) B614915
theorem B409963 : Blo 409770 409963 := bstep (se 1 (by rfl) ⟨307472, by rfl⟩ : syracuseStep 409963 = 614945) B614945
theorem B409975 : Blo 409770 409975 := bstep (se 1 (by rfl) ⟨307481, by rfl⟩ : syracuseStep 409975 = 614963) B614963
theorem B409995 : Blo 409770 409995 := bstep (se 1 (by rfl) ⟨307496, by rfl⟩ : syracuseStep 409995 = 614993) B614993
theorem B410007 : Blo 409770 410007 := bstep (se 1 (by rfl) ⟨307505, by rfl⟩ : syracuseStep 410007 = 615011) B615011
theorem B410027 : Blo 409770 410027 := bstep (se 1 (by rfl) ⟨307520, by rfl⟩ : syracuseStep 410027 = 615041) B615041
theorem B7487923 : Blo 409770 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B410039 : Blo 409770 410039 := bstep (se 1 (by rfl) ⟨307529, by rfl⟩ : syracuseStep 410039 = 615059) B615059
theorem B410059 : Blo 409770 410059 := bstep (se 1 (by rfl) ⟨307544, by rfl⟩ : syracuseStep 410059 = 615089) B615089
theorem B410071 : Blo 409770 410071 := bstep (se 1 (by rfl) ⟨307553, by rfl⟩ : syracuseStep 410071 = 615107) B615107
theorem B410091 : Blo 409770 410091 := bstep (se 1 (by rfl) ⟨307568, by rfl⟩ : syracuseStep 410091 = 615137) B615137
theorem B410103 : Blo 409770 410103 := bstep (se 1 (by rfl) ⟨307577, by rfl⟩ : syracuseStep 410103 = 615155) B615155
theorem B410123 : Blo 409770 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B410135 : Blo 409770 410135 := bstep (se 1 (by rfl) ⟨307601, by rfl⟩ : syracuseStep 410135 = 615203) B615203
theorem B410155 : Blo 409770 410155 := bstep (se 1 (by rfl) ⟨307616, by rfl⟩ : syracuseStep 410155 = 615233) B615233
theorem B410167 : Blo 409770 410167 := bstep (se 1 (by rfl) ⟨307625, by rfl⟩ : syracuseStep 410167 = 615251) B615251
theorem B410187 : Blo 409770 410187 := bstep (se 1 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 410187 = 615281) B615281
theorem B410199 : Blo 409770 410199 := bstep (se 1 (by rfl) ⟨307649, by rfl⟩ : syracuseStep 410199 = 615299) B615299
theorem B410219 : Blo 409770 410219 := bstep (se 1 (by rfl) ⟨307664, by rfl⟩ : syracuseStep 410219 = 615329) B615329
theorem B410231 : Blo 409770 410231 := bstep (se 1 (by rfl) ⟨307673, by rfl⟩ : syracuseStep 410231 = 615347) B615347
theorem B410251 : Blo 409770 410251 := bstep (se 1 (by rfl) ⟨307688, by rfl⟩ : syracuseStep 410251 = 615377) B615377
theorem B410263 : Blo 409770 410263 := bstep (se 1 (by rfl) ⟨307697, by rfl⟩ : syracuseStep 410263 = 615395) B615395
theorem B410283 : Blo 409770 410283 := bstep (se 1 (by rfl) ⟨307712, by rfl⟩ : syracuseStep 410283 = 615425) B615425
theorem B1884845 : Blo 409770 1884845 := bstep (se 3 (by rfl) ⟨353408, by rfl⟩ : syracuseStep 1884845 = 706817) B706817
theorem B410295 : Blo 409770 410295 := bstep (se 1 (by rfl) ⟨307721, by rfl⟩ : syracuseStep 410295 = 615443) B615443
theorem B410315 : Blo 409770 410315 := bstep (se 1 (by rfl) ⟨307736, by rfl⟩ : syracuseStep 410315 = 615473) B615473
theorem B410327 : Blo 409770 410327 := bstep (se 1 (by rfl) ⟨307745, by rfl⟩ : syracuseStep 410327 = 615491) B615491
theorem B3556057 : Blo 409770 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B410347 : Blo 409770 410347 := bstep (se 1 (by rfl) ⟨307760, by rfl⟩ : syracuseStep 410347 = 615521) B615521
theorem B410359 : Blo 409770 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B1557251 : Blo 409770 1557251 := bstep (se 1 (by rfl) ⟨1167938, by rfl⟩ : syracuseStep 1557251 = 2335877) B2335877
theorem B410379 : Blo 409770 410379 := bstep (se 1 (by rfl) ⟨307784, by rfl⟩ : syracuseStep 410379 = 615569) B615569
theorem B1557265 : Blo 409770 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B410391 : Blo 409770 410391 := bstep (se 1 (by rfl) ⟨307793, by rfl⟩ : syracuseStep 410391 = 615587) B615587
theorem B410411 : Blo 409770 410411 := bstep (se 1 (by rfl) ⟨307808, by rfl⟩ : syracuseStep 410411 = 615617) B615617
theorem B410423 : Blo 409770 410423 := bstep (se 1 (by rfl) ⟨307817, by rfl⟩ : syracuseStep 410423 = 615635) B615635
theorem B410443 : Blo 409770 410443 := bstep (se 1 (by rfl) ⟨307832, by rfl⟩ : syracuseStep 410443 = 615665) B615665
theorem B410455 : Blo 409770 410455 := bstep (se 1 (by rfl) ⟨307841, by rfl⟩ : syracuseStep 410455 = 615683) B615683
theorem B410475 : Blo 409770 410475 := bstep (se 1 (by rfl) ⟨307856, by rfl⟩ : syracuseStep 410475 = 615713) B615713
theorem B410487 : Blo 409770 410487 := bstep (se 1 (by rfl) ⟨307865, by rfl⟩ : syracuseStep 410487 = 615731) B615731
theorem B410507 : Blo 409770 410507 := bstep (se 1 (by rfl) ⟨307880, by rfl⟩ : syracuseStep 410507 = 615761) B615761
theorem B410519 : Blo 409770 410519 := bstep (se 1 (by rfl) ⟨307889, by rfl⟩ : syracuseStep 410519 = 615779) B615779
theorem B410539 : Blo 409770 410539 := bstep (se 1 (by rfl) ⟨307904, by rfl⟩ : syracuseStep 410539 = 615809) B615809
theorem B410551 : Blo 409770 410551 := bstep (se 1 (by rfl) ⟨307913, by rfl⟩ : syracuseStep 410551 = 615827) B615827
theorem B410571 : Blo 409770 410571 := bstep (se 1 (by rfl) ⟨307928, by rfl⟩ : syracuseStep 410571 = 615857) B615857
theorem B410583 : Blo 409770 410583 := bstep (se 1 (by rfl) ⟨307937, by rfl⟩ : syracuseStep 410583 = 615875) B615875
theorem B410603 : Blo 409770 410603 := bstep (se 1 (by rfl) ⟨307952, by rfl⟩ : syracuseStep 410603 = 615905) B615905
theorem B410615 : Blo 409770 410615 := bstep (se 1 (by rfl) ⟨307961, by rfl⟩ : syracuseStep 410615 = 615923) B615923
theorem B410635 : Blo 409770 410635 := bstep (se 1 (by rfl) ⟨307976, by rfl⟩ : syracuseStep 410635 = 615953) B615953
theorem B410647 : Blo 409770 410647 := bstep (se 1 (by rfl) ⟨307985, by rfl⟩ : syracuseStep 410647 = 615971) B615971
theorem B410667 : Blo 409770 410667 := bstep (se 1 (by rfl) ⟨308000, by rfl⟩ : syracuseStep 410667 = 616001) B616001
theorem B410679 : Blo 409770 410679 := bstep (se 1 (by rfl) ⟨308009, by rfl⟩ : syracuseStep 410679 = 616019) B616019
theorem B1557569 : Blo 409770 1557569 := bstep (se 2 (by rfl) ⟨584088, by rfl⟩ : syracuseStep 1557569 = 1168177) B1168177
theorem B410699 : Blo 409770 410699 := bstep (se 1 (by rfl) ⟨308024, by rfl⟩ : syracuseStep 410699 = 616049) B616049
theorem B1393739 : Blo 409770 1393739 := bstep (se 1 (by rfl) ⟨1045304, by rfl⟩ : syracuseStep 1393739 = 2090609) B2090609
theorem B410711 : Blo 409770 410711 := bstep (se 1 (by rfl) ⟨308033, by rfl⟩ : syracuseStep 410711 = 616067) B616067
theorem B410731 : Blo 409770 410731 := bstep (se 1 (by rfl) ⟨308048, by rfl⟩ : syracuseStep 410731 = 616097) B616097
theorem B410743 : Blo 409770 410743 := bstep (se 1 (by rfl) ⟨308057, by rfl⟩ : syracuseStep 410743 = 616115) B616115
theorem B410763 : Blo 409770 410763 := bstep (se 1 (by rfl) ⟨308072, by rfl⟩ : syracuseStep 410763 = 616145) B616145
theorem B410775 : Blo 409770 410775 := bstep (se 1 (by rfl) ⟨308081, by rfl⟩ : syracuseStep 410775 = 616163) B616163
theorem B410795 : Blo 409770 410795 := bstep (se 1 (by rfl) ⟨308096, by rfl⟩ : syracuseStep 410795 = 616193) B616193
theorem B410807 : Blo 409770 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B410827 : Blo 409770 410827 := bstep (se 1 (by rfl) ⟨308120, by rfl⟩ : syracuseStep 410827 = 616241) B616241
theorem B410839 : Blo 409770 410839 := bstep (se 1 (by rfl) ⟨308129, by rfl⟩ : syracuseStep 410839 = 616259) B616259
theorem B410859 : Blo 409770 410859 := bstep (se 1 (by rfl) ⟨308144, by rfl⟩ : syracuseStep 410859 = 616289) B616289
theorem B410871 : Blo 409770 410871 := bstep (se 1 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 410871 = 616307) B616307
theorem B410891 : Blo 409770 410891 := bstep (se 1 (by rfl) ⟨308168, by rfl⟩ : syracuseStep 410891 = 616337) B616337
theorem B410903 : Blo 409770 410903 := bstep (se 1 (by rfl) ⟨308177, by rfl⟩ : syracuseStep 410903 = 616355) B616355
theorem B410923 : Blo 409770 410923 := bstep (se 1 (by rfl) ⟨308192, by rfl⟩ : syracuseStep 410923 = 616385) B616385
theorem B1754419 : Blo 409770 1754419 := bstep (se 1 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 1754419 = 2631629) B2631629
theorem B410935 : Blo 409770 410935 := bstep (se 1 (by rfl) ⟨308201, by rfl⟩ : syracuseStep 410935 = 616403) B616403
theorem B410955 : Blo 409770 410955 := bstep (se 1 (by rfl) ⟨308216, by rfl⟩ : syracuseStep 410955 = 616433) B616433
theorem B410967 : Blo 409770 410967 := bstep (se 1 (by rfl) ⟨308225, by rfl⟩ : syracuseStep 410967 = 616451) B616451
theorem B1394009 : Blo 409770 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B410987 : Blo 409770 410987 := bstep (se 1 (by rfl) ⟨308240, by rfl⟩ : syracuseStep 410987 = 616481) B616481
theorem B410999 : Blo 409770 410999 := bstep (se 1 (by rfl) ⟨308249, by rfl⟩ : syracuseStep 410999 = 616499) B616499
theorem B411019 : Blo 409770 411019 := bstep (se 1 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 411019 = 616529) B616529
theorem B411031 : Blo 409770 411031 := bstep (se 1 (by rfl) ⟨308273, by rfl⟩ : syracuseStep 411031 = 616547) B616547
theorem B411051 : Blo 409770 411051 := bstep (se 1 (by rfl) ⟨308288, by rfl⟩ : syracuseStep 411051 = 616577) B616577
theorem B411063 : Blo 409770 411063 := bstep (se 1 (by rfl) ⟨308297, by rfl⟩ : syracuseStep 411063 = 616595) B616595
theorem B411083 : Blo 409770 411083 := bstep (se 1 (by rfl) ⟨308312, by rfl⟩ : syracuseStep 411083 = 616625) B616625
theorem B411095 : Blo 409770 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B411115 : Blo 409770 411115 := bstep (se 1 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 411115 = 616673) B616673
theorem B411127 : Blo 409770 411127 := bstep (se 1 (by rfl) ⟨308345, by rfl⟩ : syracuseStep 411127 = 616691) B616691
theorem B411147 : Blo 409770 411147 := bstep (se 1 (by rfl) ⟨308360, by rfl⟩ : syracuseStep 411147 = 616721) B616721
theorem B411159 : Blo 409770 411159 := bstep (se 1 (by rfl) ⟨308369, by rfl⟩ : syracuseStep 411159 = 616739) B616739
theorem B411179 : Blo 409770 411179 := bstep (se 1 (by rfl) ⟨308384, by rfl⟩ : syracuseStep 411179 = 616769) B616769
theorem B411191 : Blo 409770 411191 := bstep (se 1 (by rfl) ⟨308393, by rfl⟩ : syracuseStep 411191 = 616787) B616787
theorem B411211 : Blo 409770 411211 := bstep (se 1 (by rfl) ⟨308408, by rfl⟩ : syracuseStep 411211 = 616817) B616817
theorem B1787467 : Blo 409770 1787467 := bstep (se 1 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 1787467 = 2681201) B2681201
theorem B411223 : Blo 409770 411223 := bstep (se 1 (by rfl) ⟨308417, by rfl⟩ : syracuseStep 411223 = 616835) B616835
theorem B411243 : Blo 409770 411243 := bstep (se 1 (by rfl) ⟨308432, by rfl⟩ : syracuseStep 411243 = 616865) B616865
theorem B411255 : Blo 409770 411255 := bstep (se 1 (by rfl) ⟨308441, by rfl⟩ : syracuseStep 411255 = 616883) B616883
theorem B411275 : Blo 409770 411275 := bstep (se 1 (by rfl) ⟨308456, by rfl⟩ : syracuseStep 411275 = 616913) B616913
theorem B411287 : Blo 409770 411287 := bstep (se 1 (by rfl) ⟨308465, by rfl⟩ : syracuseStep 411287 = 616931) B616931
theorem B2967191 : Blo 409770 2967191 := bstep (se 1 (by rfl) ⟨2225393, by rfl⟩ : syracuseStep 2967191 = 4450787) B4450787
theorem B411307 : Blo 409770 411307 := bstep (se 1 (by rfl) ⟨308480, by rfl⟩ : syracuseStep 411307 = 616961) B616961
theorem B411319 : Blo 409770 411319 := bstep (se 1 (by rfl) ⟨308489, by rfl⟩ : syracuseStep 411319 = 616979) B616979
theorem B411339 : Blo 409770 411339 := bstep (se 1 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 411339 = 617009) B617009
theorem B411351 : Blo 409770 411351 := bstep (se 1 (by rfl) ⟨308513, by rfl⟩ : syracuseStep 411351 = 617027) B617027
theorem B837335 : Blo 409770 837335 := bstep (se 1 (by rfl) ⟨628001, by rfl⟩ : syracuseStep 837335 = 1256003) B1256003
theorem B1558237 : Blo 409770 1558237 := bstep (se 3 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 1558237 = 584339) B584339
theorem B411371 : Blo 409770 411371 := bstep (se 1 (by rfl) ⟨308528, by rfl⟩ : syracuseStep 411371 = 617057) B617057
theorem B411383 : Blo 409770 411383 := bstep (se 1 (by rfl) ⟨308537, by rfl⟩ : syracuseStep 411383 = 617075) B617075
theorem B411403 : Blo 409770 411403 := bstep (se 1 (by rfl) ⟨308552, by rfl⟩ : syracuseStep 411403 = 617105) B617105
theorem B411415 : Blo 409770 411415 := bstep (se 1 (by rfl) ⟨308561, by rfl⟩ : syracuseStep 411415 = 617123) B617123
theorem B411435 : Blo 409770 411435 := bstep (se 1 (by rfl) ⟨308576, by rfl⟩ : syracuseStep 411435 = 617153) B617153
theorem B411447 : Blo 409770 411447 := bstep (se 1 (by rfl) ⟨308585, by rfl⟩ : syracuseStep 411447 = 617171) B617171
theorem B411467 : Blo 409770 411467 := bstep (se 1 (by rfl) ⟨308600, by rfl⟩ : syracuseStep 411467 = 617201) B617201
theorem B411479 : Blo 409770 411479 := bstep (se 1 (by rfl) ⟨308609, by rfl⟩ : syracuseStep 411479 = 617219) B617219
theorem B411499 : Blo 409770 411499 := bstep (se 1 (by rfl) ⟨308624, by rfl⟩ : syracuseStep 411499 = 617249) B617249
theorem B411511 : Blo 409770 411511 := bstep (se 1 (by rfl) ⟨308633, by rfl⟩ : syracuseStep 411511 = 617267) B617267
theorem B411531 : Blo 409770 411531 := bstep (se 1 (by rfl) ⟨308648, by rfl⟩ : syracuseStep 411531 = 617297) B617297
theorem B411543 : Blo 409770 411543 := bstep (se 1 (by rfl) ⟨308657, by rfl⟩ : syracuseStep 411543 = 617315) B617315
theorem B411563 : Blo 409770 411563 := bstep (se 1 (by rfl) ⟨308672, by rfl⟩ : syracuseStep 411563 = 617345) B617345
theorem B1755053 : Blo 409770 1755053 := bstep (se 3 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 1755053 = 658145) B658145
theorem B411575 : Blo 409770 411575 := bstep (se 1 (by rfl) ⟨308681, by rfl⟩ : syracuseStep 411575 = 617363) B617363
theorem B411595 : Blo 409770 411595 := bstep (se 1 (by rfl) ⟨308696, by rfl⟩ : syracuseStep 411595 = 617393) B617393
theorem B411607 : Blo 409770 411607 := bstep (se 1 (by rfl) ⟨308705, by rfl⟩ : syracuseStep 411607 = 617411) B617411
theorem B411627 : Blo 409770 411627 := bstep (se 1 (by rfl) ⟨308720, by rfl⟩ : syracuseStep 411627 = 617441) B617441
theorem B411639 : Blo 409770 411639 := bstep (se 1 (by rfl) ⟨308729, by rfl⟩ : syracuseStep 411639 = 617459) B617459
theorem B411659 : Blo 409770 411659 := bstep (se 1 (by rfl) ⟨308744, by rfl⟩ : syracuseStep 411659 = 617489) B617489
theorem B837643 : Blo 409770 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B2082833 : Blo 409770 2082833 := bstep (se 2 (by rfl) ⟨781062, by rfl⟩ : syracuseStep 2082833 = 1562125) B1562125
theorem B411671 : Blo 409770 411671 := bstep (se 1 (by rfl) ⟨308753, by rfl⟩ : syracuseStep 411671 = 617507) B617507
theorem B1394711 : Blo 409770 1394711 := bstep (se 1 (by rfl) ⟨1046033, by rfl⟩ : syracuseStep 1394711 = 2092067) B2092067
theorem B411691 : Blo 409770 411691 := bstep (se 1 (by rfl) ⟨308768, by rfl⟩ : syracuseStep 411691 = 617537) B617537
theorem B411703 : Blo 409770 411703 := bstep (se 1 (by rfl) ⟨308777, by rfl⟩ : syracuseStep 411703 = 617555) B617555
theorem B411723 : Blo 409770 411723 := bstep (se 1 (by rfl) ⟨308792, by rfl⟩ : syracuseStep 411723 = 617585) B617585
theorem B411735 : Blo 409770 411735 := bstep (se 1 (by rfl) ⟨308801, by rfl⟩ : syracuseStep 411735 = 617603) B617603
theorem B2508893 : Blo 409770 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B411755 : Blo 409770 411755 := bstep (se 1 (by rfl) ⟨308816, by rfl⟩ : syracuseStep 411755 = 617633) B617633
theorem B411767 : Blo 409770 411767 := bstep (se 1 (by rfl) ⟨308825, by rfl⟩ : syracuseStep 411767 = 617651) B617651
theorem B1886339 : Blo 409770 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B411787 : Blo 409770 411787 := bstep (se 1 (by rfl) ⟨308840, by rfl⟩ : syracuseStep 411787 = 617681) B617681
theorem B411799 : Blo 409770 411799 := bstep (se 1 (by rfl) ⟨308849, by rfl⟩ : syracuseStep 411799 = 617699) B617699
theorem B411819 : Blo 409770 411819 := bstep (se 1 (by rfl) ⟨308864, by rfl⟩ : syracuseStep 411819 = 617729) B617729
theorem B2082995 : Blo 409770 2082995 := bstep (se 1 (by rfl) ⟨1562246, by rfl⟩ : syracuseStep 2082995 = 3124493) B3124493
theorem B411831 : Blo 409770 411831 := bstep (se 1 (by rfl) ⟨308873, by rfl⟩ : syracuseStep 411831 = 617747) B617747
theorem B936139 : Blo 409770 936139 := bstep (se 1 (by rfl) ⟨702104, by rfl⟩ : syracuseStep 936139 = 1404209) B1404209
theorem B411851 : Blo 409770 411851 := bstep (se 1 (by rfl) ⟨308888, by rfl⟩ : syracuseStep 411851 = 617777) B617777
theorem B411863 : Blo 409770 411863 := bstep (se 1 (by rfl) ⟨308897, by rfl⟩ : syracuseStep 411863 = 617795) B617795
theorem B411883 : Blo 409770 411883 := bstep (se 1 (by rfl) ⟨308912, by rfl⟩ : syracuseStep 411883 = 617825) B617825
theorem B411895 : Blo 409770 411895 := bstep (se 1 (by rfl) ⟨308921, by rfl⟩ : syracuseStep 411895 = 617843) B617843
theorem B411915 : Blo 409770 411915 := bstep (se 1 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 411915 = 617873) B617873
theorem B411927 : Blo 409770 411927 := bstep (se 1 (by rfl) ⟨308945, by rfl⟩ : syracuseStep 411927 = 617891) B617891
theorem B411947 : Blo 409770 411947 := bstep (se 1 (by rfl) ⟨308960, by rfl⟩ : syracuseStep 411947 = 617921) B617921
theorem B411959 : Blo 409770 411959 := bstep (se 1 (by rfl) ⟨308969, by rfl⟩ : syracuseStep 411959 = 617939) B617939
theorem B411979 : Blo 409770 411979 := bstep (se 1 (by rfl) ⟨308984, by rfl⟩ : syracuseStep 411979 = 617969) B617969
theorem B411991 : Blo 409770 411991 := bstep (se 1 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 411991 = 617987) B617987
theorem B412011 : Blo 409770 412011 := bstep (se 1 (by rfl) ⟨309008, by rfl⟩ : syracuseStep 412011 = 618017) B618017
theorem B412023 : Blo 409770 412023 := bstep (se 1 (by rfl) ⟨309017, by rfl⟩ : syracuseStep 412023 = 618035) B618035
theorem B412043 : Blo 409770 412043 := bstep (se 1 (by rfl) ⟨309032, by rfl⟩ : syracuseStep 412043 = 618065) B618065
theorem B412055 : Blo 409770 412055 := bstep (se 1 (by rfl) ⟨309041, by rfl⟩ : syracuseStep 412055 = 618083) B618083
theorem B412075 : Blo 409770 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B412087 : Blo 409770 412087 := bstep (se 1 (by rfl) ⟨309065, by rfl⟩ : syracuseStep 412087 = 618131) B618131
theorem B412107 : Blo 409770 412107 := bstep (se 1 (by rfl) ⟨309080, by rfl⟩ : syracuseStep 412107 = 618161) B618161
theorem B412119 : Blo 409770 412119 := bstep (se 1 (by rfl) ⟨309089, by rfl⟩ : syracuseStep 412119 = 618179) B618179
theorem B412139 : Blo 409770 412139 := bstep (se 1 (by rfl) ⟨309104, by rfl⟩ : syracuseStep 412139 = 618209) B618209
theorem B412151 : Blo 409770 412151 := bstep (se 1 (by rfl) ⟨309113, by rfl⟩ : syracuseStep 412151 = 618227) B618227
theorem B412171 : Blo 409770 412171 := bstep (se 1 (by rfl) ⟨309128, by rfl⟩ : syracuseStep 412171 = 618257) B618257
theorem B412183 : Blo 409770 412183 := bstep (se 1 (by rfl) ⟨309137, by rfl⟩ : syracuseStep 412183 = 618275) B618275
theorem B412203 : Blo 409770 412203 := bstep (se 1 (by rfl) ⟨309152, by rfl⟩ : syracuseStep 412203 = 618305) B618305
theorem B1395251 : Blo 409770 1395251 := bstep (se 1 (by rfl) ⟨1046438, by rfl⟩ : syracuseStep 1395251 = 2092877) B2092877
theorem B412215 : Blo 409770 412215 := bstep (se 1 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 412215 = 618323) B618323
theorem B412235 : Blo 409770 412235 := bstep (se 1 (by rfl) ⟨309176, by rfl⟩ : syracuseStep 412235 = 618353) B618353
theorem B412247 : Blo 409770 412247 := bstep (se 1 (by rfl) ⟨309185, by rfl⟩ : syracuseStep 412247 = 618371) B618371
theorem B412267 : Blo 409770 412267 := bstep (se 1 (by rfl) ⟨309200, by rfl⟩ : syracuseStep 412267 = 618401) B618401
theorem B412279 : Blo 409770 412279 := bstep (se 1 (by rfl) ⟨309209, by rfl⟩ : syracuseStep 412279 = 618419) B618419
theorem B412299 : Blo 409770 412299 := bstep (se 1 (by rfl) ⟨309224, by rfl⟩ : syracuseStep 412299 = 618449) B618449
theorem B412311 : Blo 409770 412311 := bstep (se 1 (by rfl) ⟨309233, by rfl⟩ : syracuseStep 412311 = 618467) B618467
theorem B412331 : Blo 409770 412331 := bstep (se 1 (by rfl) ⟨309248, by rfl⟩ : syracuseStep 412331 = 618497) B618497
theorem B412343 : Blo 409770 412343 := bstep (se 1 (by rfl) ⟨309257, by rfl⟩ : syracuseStep 412343 = 618515) B618515
theorem B412363 : Blo 409770 412363 := bstep (se 1 (by rfl) ⟨309272, by rfl⟩ : syracuseStep 412363 = 618545) B618545
theorem B412375 : Blo 409770 412375 := bstep (se 1 (by rfl) ⟨309281, by rfl⟩ : syracuseStep 412375 = 618563) B618563
theorem B412395 : Blo 409770 412395 := bstep (se 1 (by rfl) ⟨309296, by rfl⟩ : syracuseStep 412395 = 618593) B618593
theorem B412407 : Blo 409770 412407 := bstep (se 1 (by rfl) ⟨309305, by rfl⟩ : syracuseStep 412407 = 618611) B618611
theorem B412427 : Blo 409770 412427 := bstep (se 1 (by rfl) ⟨309320, by rfl⟩ : syracuseStep 412427 = 618641) B618641
theorem B412439 : Blo 409770 412439 := bstep (se 1 (by rfl) ⟨309329, by rfl⟩ : syracuseStep 412439 = 618659) B618659
theorem B412459 : Blo 409770 412459 := bstep (se 1 (by rfl) ⟨309344, by rfl⟩ : syracuseStep 412459 = 618689) B618689
theorem B412471 : Blo 409770 412471 := bstep (se 1 (by rfl) ⟨309353, by rfl⟩ : syracuseStep 412471 = 618707) B618707
theorem B1395521 : Blo 409770 1395521 := bstep (se 2 (by rfl) ⟨523320, by rfl⟩ : syracuseStep 1395521 = 1046641) B1046641
theorem B412491 : Blo 409770 412491 := bstep (se 1 (by rfl) ⟨309368, by rfl⟩ : syracuseStep 412491 = 618737) B618737
theorem B412503 : Blo 409770 412503 := bstep (se 1 (by rfl) ⟨309377, by rfl⟩ : syracuseStep 412503 = 618755) B618755
theorem B838487 : Blo 409770 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B1428317 : Blo 409770 1428317 := bstep (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) B535619
theorem B412523 : Blo 409770 412523 := bstep (se 1 (by rfl) ⟨309392, by rfl⟩ : syracuseStep 412523 = 618785) B618785
theorem B412535 : Blo 409770 412535 := bstep (se 1 (by rfl) ⟨309401, by rfl⟩ : syracuseStep 412535 = 618803) B618803
theorem B412555 : Blo 409770 412555 := bstep (se 1 (by rfl) ⟨309416, by rfl⟩ : syracuseStep 412555 = 618833) B618833
theorem B412567 : Blo 409770 412567 := bstep (se 1 (by rfl) ⟨309425, by rfl⟩ : syracuseStep 412567 = 618851) B618851
theorem B412587 : Blo 409770 412587 := bstep (se 1 (by rfl) ⟨309440, by rfl⟩ : syracuseStep 412587 = 618881) B618881
theorem B412599 : Blo 409770 412599 := bstep (se 1 (by rfl) ⟨309449, by rfl⟩ : syracuseStep 412599 = 618899) B618899
theorem B412619 : Blo 409770 412619 := bstep (se 1 (by rfl) ⟨309464, by rfl⟩ : syracuseStep 412619 = 618929) B618929
theorem B412631 : Blo 409770 412631 := bstep (se 1 (by rfl) ⟨309473, by rfl⟩ : syracuseStep 412631 = 618947) B618947
theorem B1559513 : Blo 409770 1559513 := bstep (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) B1169635
theorem B412651 : Blo 409770 412651 := bstep (se 1 (by rfl) ⟨309488, by rfl⟩ : syracuseStep 412651 = 618977) B618977
theorem B412663 : Blo 409770 412663 := bstep (se 1 (by rfl) ⟨309497, by rfl⟩ : syracuseStep 412663 = 618995) B618995
theorem B412683 : Blo 409770 412683 := bstep (se 1 (by rfl) ⟨309512, by rfl⟩ : syracuseStep 412683 = 619025) B619025
theorem B412695 : Blo 409770 412695 := bstep (se 1 (by rfl) ⟨309521, by rfl⟩ : syracuseStep 412695 = 619043) B619043
theorem B740377 : Blo 409770 740377 := bstep (se 2 (by rfl) ⟨277641, by rfl⟩ : syracuseStep 740377 = 555283) B555283
theorem B412715 : Blo 409770 412715 := bstep (se 1 (by rfl) ⟨309536, by rfl⟩ : syracuseStep 412715 = 619073) B619073
theorem B412727 : Blo 409770 412727 := bstep (se 1 (by rfl) ⟨309545, by rfl⟩ : syracuseStep 412727 = 619091) B619091
theorem B412747 : Blo 409770 412747 := bstep (se 1 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 412747 = 619121) B619121
theorem B412759 : Blo 409770 412759 := bstep (se 1 (by rfl) ⟨309569, by rfl⟩ : syracuseStep 412759 = 619139) B619139
theorem B412779 : Blo 409770 412779 := bstep (se 1 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 412779 = 619169) B619169
theorem B412791 : Blo 409770 412791 := bstep (se 1 (by rfl) ⟨309593, by rfl⟩ : syracuseStep 412791 = 619187) B619187
theorem B412811 : Blo 409770 412811 := bstep (se 1 (by rfl) ⟨309608, by rfl⟩ : syracuseStep 412811 = 619217) B619217
theorem B412823 : Blo 409770 412823 := bstep (se 1 (by rfl) ⟨309617, by rfl⟩ : syracuseStep 412823 = 619235) B619235
theorem B412843 : Blo 409770 412843 := bstep (se 1 (by rfl) ⟨309632, by rfl⟩ : syracuseStep 412843 = 619265) B619265
theorem B412855 : Blo 409770 412855 := bstep (se 1 (by rfl) ⟨309641, by rfl⟩ : syracuseStep 412855 = 619283) B619283
theorem B412875 : Blo 409770 412875 := bstep (se 1 (by rfl) ⟨309656, by rfl⟩ : syracuseStep 412875 = 619313) B619313
theorem B445655 : Blo 409770 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B412887 : Blo 409770 412887 := bstep (se 1 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 412887 = 619331) B619331
theorem B412907 : Blo 409770 412907 := bstep (se 1 (by rfl) ⟨309680, by rfl⟩ : syracuseStep 412907 = 619361) B619361
theorem B412919 : Blo 409770 412919 := bstep (se 1 (by rfl) ⟨309689, by rfl⟩ : syracuseStep 412919 = 619379) B619379
theorem B412939 : Blo 409770 412939 := bstep (se 1 (by rfl) ⟨309704, by rfl⟩ : syracuseStep 412939 = 619409) B619409
theorem B412951 : Blo 409770 412951 := bstep (se 1 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 412951 = 619427) B619427
theorem B412971 : Blo 409770 412971 := bstep (se 1 (by rfl) ⟨309728, by rfl⟩ : syracuseStep 412971 = 619457) B619457
theorem B412983 : Blo 409770 412983 := bstep (se 1 (by rfl) ⟨309737, by rfl⟩ : syracuseStep 412983 = 619475) B619475
theorem B413003 : Blo 409770 413003 := bstep (se 1 (by rfl) ⟨309752, by rfl⟩ : syracuseStep 413003 = 619505) B619505
theorem B413015 : Blo 409770 413015 := bstep (se 1 (by rfl) ⟨309761, by rfl⟩ : syracuseStep 413015 = 619523) B619523
theorem B1396061 : Blo 409770 1396061 := bstep (se 3 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 1396061 = 523523) B523523
theorem B413035 : Blo 409770 413035 := bstep (se 1 (by rfl) ⟨309776, by rfl⟩ : syracuseStep 413035 = 619553) B619553
theorem B413047 : Blo 409770 413047 := bstep (se 1 (by rfl) ⟨309785, by rfl⟩ : syracuseStep 413047 = 619571) B619571
theorem B413067 : Blo 409770 413067 := bstep (se 1 (by rfl) ⟨309800, by rfl⟩ : syracuseStep 413067 = 619601) B619601
theorem B413079 : Blo 409770 413079 := bstep (se 1 (by rfl) ⟨309809, by rfl⟩ : syracuseStep 413079 = 619619) B619619
theorem B413099 : Blo 409770 413099 := bstep (se 1 (by rfl) ⟨309824, by rfl⟩ : syracuseStep 413099 = 619649) B619649
theorem B413111 : Blo 409770 413111 := bstep (se 1 (by rfl) ⟨309833, by rfl⟩ : syracuseStep 413111 = 619667) B619667
theorem B413131 : Blo 409770 413131 := bstep (se 1 (by rfl) ⟨309848, by rfl⟩ : syracuseStep 413131 = 619697) B619697
theorem B413143 : Blo 409770 413143 := bstep (se 1 (by rfl) ⟨309857, by rfl⟩ : syracuseStep 413143 = 619715) B619715
theorem B413163 : Blo 409770 413163 := bstep (se 1 (by rfl) ⟨309872, by rfl⟩ : syracuseStep 413163 = 619745) B619745
theorem B413175 : Blo 409770 413175 := bstep (se 1 (by rfl) ⟨309881, by rfl⟩ : syracuseStep 413175 = 619763) B619763
theorem B413195 : Blo 409770 413195 := bstep (se 1 (by rfl) ⟨309896, by rfl⟩ : syracuseStep 413195 = 619793) B619793
theorem B413207 : Blo 409770 413207 := bstep (se 1 (by rfl) ⟨309905, by rfl⟩ : syracuseStep 413207 = 619811) B619811
theorem B413227 : Blo 409770 413227 := bstep (se 1 (by rfl) ⟨309920, by rfl⟩ : syracuseStep 413227 = 619841) B619841
theorem B413239 : Blo 409770 413239 := bstep (se 1 (by rfl) ⟨309929, by rfl⟩ : syracuseStep 413239 = 619859) B619859
theorem B2674241 : Blo 409770 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B413259 : Blo 409770 413259 := bstep (se 1 (by rfl) ⟨309944, by rfl⟩ : syracuseStep 413259 = 619889) B619889
theorem B413271 : Blo 409770 413271 := bstep (se 1 (by rfl) ⟨309953, by rfl⟩ : syracuseStep 413271 = 619907) B619907
theorem B413291 : Blo 409770 413291 := bstep (se 1 (by rfl) ⟨309968, by rfl⟩ : syracuseStep 413291 = 619937) B619937
theorem B413303 : Blo 409770 413303 := bstep (se 1 (by rfl) ⟨309977, by rfl⟩ : syracuseStep 413303 = 619955) B619955
theorem B413323 : Blo 409770 413323 := bstep (se 1 (by rfl) ⟨309992, by rfl⟩ : syracuseStep 413323 = 619985) B619985
theorem B413335 : Blo 409770 413335 := bstep (se 1 (by rfl) ⟨310001, by rfl⟩ : syracuseStep 413335 = 620003) B620003
theorem B413355 : Blo 409770 413355 := bstep (se 1 (by rfl) ⟨310016, by rfl⟩ : syracuseStep 413355 = 620033) B620033
theorem B413367 : Blo 409770 413367 := bstep (se 1 (by rfl) ⟨310025, by rfl⟩ : syracuseStep 413367 = 620051) B620051
theorem B413387 : Blo 409770 413387 := bstep (se 1 (by rfl) ⟨310040, by rfl⟩ : syracuseStep 413387 = 620081) B620081
theorem B6672077 : Blo 409770 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B413399 : Blo 409770 413399 := bstep (se 1 (by rfl) ⟨310049, by rfl⟩ : syracuseStep 413399 = 620099) B620099
theorem B413419 : Blo 409770 413419 := bstep (se 1 (by rfl) ⟨310064, by rfl⟩ : syracuseStep 413419 = 620129) B620129
theorem B413431 : Blo 409770 413431 := bstep (se 1 (by rfl) ⟨310073, by rfl⟩ : syracuseStep 413431 = 620147) B620147
theorem B413451 : Blo 409770 413451 := bstep (se 1 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 413451 = 620177) B620177
theorem B413463 : Blo 409770 413463 := bstep (se 1 (by rfl) ⟨310097, by rfl⟩ : syracuseStep 413463 = 620195) B620195
theorem B413483 : Blo 409770 413483 := bstep (se 1 (by rfl) ⟨310112, by rfl⟩ : syracuseStep 413483 = 620225) B620225
theorem B413495 : Blo 409770 413495 := bstep (se 1 (by rfl) ⟨310121, by rfl⟩ : syracuseStep 413495 = 620243) B620243
theorem B413515 : Blo 409770 413515 := bstep (se 1 (by rfl) ⟨310136, by rfl⟩ : syracuseStep 413515 = 620273) B620273
theorem B413527 : Blo 409770 413527 := bstep (se 1 (by rfl) ⟨310145, by rfl⟩ : syracuseStep 413527 = 620291) B620291
theorem B413547 : Blo 409770 413547 := bstep (se 1 (by rfl) ⟨310160, by rfl⟩ : syracuseStep 413547 = 620321) B620321
theorem B413559 : Blo 409770 413559 := bstep (se 1 (by rfl) ⟨310169, by rfl⟩ : syracuseStep 413559 = 620339) B620339
theorem B413579 : Blo 409770 413579 := bstep (se 1 (by rfl) ⟨310184, by rfl⟩ : syracuseStep 413579 = 620369) B620369
theorem B413591 : Blo 409770 413591 := bstep (se 1 (by rfl) ⟨310193, by rfl⟩ : syracuseStep 413591 = 620387) B620387
theorem B413611 : Blo 409770 413611 := bstep (se 1 (by rfl) ⟨310208, by rfl⟩ : syracuseStep 413611 = 620417) B620417
theorem B413623 : Blo 409770 413623 := bstep (se 1 (by rfl) ⟨310217, by rfl⟩ : syracuseStep 413623 = 620435) B620435
theorem B413643 : Blo 409770 413643 := bstep (se 1 (by rfl) ⟨310232, by rfl⟩ : syracuseStep 413643 = 620465) B620465
theorem B413655 : Blo 409770 413655 := bstep (se 1 (by rfl) ⟨310241, by rfl⟩ : syracuseStep 413655 = 620483) B620483
theorem B413675 : Blo 409770 413675 := bstep (se 1 (by rfl) ⟨310256, by rfl⟩ : syracuseStep 413675 = 620513) B620513
theorem B413687 : Blo 409770 413687 := bstep (se 1 (by rfl) ⟨310265, by rfl⟩ : syracuseStep 413687 = 620531) B620531
theorem B413707 : Blo 409770 413707 := bstep (se 1 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 413707 = 620561) B620561
theorem B413719 : Blo 409770 413719 := bstep (se 1 (by rfl) ⟨310289, by rfl⟩ : syracuseStep 413719 = 620579) B620579
theorem B413739 : Blo 409770 413739 := bstep (se 1 (by rfl) ⟨310304, by rfl⟩ : syracuseStep 413739 = 620609) B620609
theorem B413751 : Blo 409770 413751 := bstep (se 1 (by rfl) ⟨310313, by rfl⟩ : syracuseStep 413751 = 620627) B620627
theorem B2084939 : Blo 409770 2084939 := bstep (se 1 (by rfl) ⟨1563704, by rfl⟩ : syracuseStep 2084939 = 3127409) B3127409
theorem B3952901 : Blo 409770 3952901 := bstep (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) B741169
theorem B1167767 : Blo 409770 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B1561139 : Blo 409770 1561139 := bstep (se 1 (by rfl) ⟨1170854, by rfl⟩ : syracuseStep 1561139 = 2341709) B2341709
theorem B1561153 : Blo 409770 1561153 := bstep (se 2 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 1561153 = 1170865) B1170865
theorem B2708147 : Blo 409770 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B3134213 : Blo 409770 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B742259 : Blo 409770 742259 := bstep (se 1 (by rfl) ⟨556694, by rfl⟩ : syracuseStep 742259 = 1113389) B1113389
theorem B1037387 : Blo 409770 1037387 := bstep (se 1 (by rfl) ⟨778040, by rfl⟩ : syracuseStep 1037387 = 1556081) B1556081
theorem B1168577 : Blo 409770 1168577 := bstep (se 2 (by rfl) ⟨438216, by rfl⟩ : syracuseStep 1168577 = 876433) B876433
theorem B5002501 : Blo 409770 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B6313315 : Blo 409770 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B1758743 : Blo 409770 1758743 := bstep (se 1 (by rfl) ⟨1319057, by rfl⟩ : syracuseStep 1758743 = 2638115) B2638115
theorem B939595 : Blo 409770 939595 := bstep (se 1 (by rfl) ⟨704696, by rfl⟩ : syracuseStep 939595 = 1409393) B1409393
theorem B2643673 : Blo 409770 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B2086721 : Blo 409770 2086721 := bstep (se 2 (by rfl) ⟨782520, by rfl⟩ : syracuseStep 2086721 = 1565041) B1565041
theorem B1038359 : Blo 409770 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B4446413 : Blo 409770 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B2644289 : Blo 409770 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B1563083 : Blo 409770 1563083 := bstep (se 1 (by rfl) ⟨1172312, by rfl⟩ : syracuseStep 1563083 = 2344625) B2344625
theorem B1563097 : Blo 409770 1563097 := bstep (se 2 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 1563097 = 1172323) B1172323
theorem B744025 : Blo 409770 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B1039027 : Blo 409770 1039027 := bstep (se 1 (by rfl) ⟨779270, by rfl⟩ : syracuseStep 1039027 = 1558541) B1558541
theorem B1170227 : Blo 409770 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B1039169 : Blo 409770 1039169 := bstep (se 2 (by rfl) ⟨389688, by rfl⟩ : syracuseStep 1039169 = 779377) B779377
theorem B1170251 : Blo 409770 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B3136643 : Blo 409770 3136643 := bstep (se 1 (by rfl) ⟨2352482, by rfl⟩ : syracuseStep 3136643 = 4704965) B4704965
theorem B417079 : Blo 409770 417079 := bstep (se 1 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 417079 = 625619) B625619
theorem B1564055 : Blo 409770 1564055 := bstep (se 1 (by rfl) ⟨1173041, by rfl⟩ : syracuseStep 1564055 = 2346083) B2346083
theorem B3333581 : Blo 409770 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B3333707 : Blo 409770 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1171037 : Blo 409770 1171037 := bstep (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) B439139
theorem B4284109 : Blo 409770 4284109 := bstep (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) B1606541
theorem B2088665 : Blo 409770 2088665 := bstep (se 2 (by rfl) ⟨783249, by rfl⟩ : syracuseStep 2088665 = 1566499) B1566499
theorem B777995 : Blo 409770 777995 := bstep (se 1 (by rfl) ⟨583496, by rfl⟩ : syracuseStep 777995 = 1166993) B1166993
theorem B3563443 : Blo 409770 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B1761203 : Blo 409770 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B778177 : Blo 409770 778177 := bstep (se 2 (by rfl) ⟨291816, by rfl⟩ : syracuseStep 778177 = 583633) B583633
theorem B1368029 : Blo 409770 1368029 := bstep (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) B513011
theorem B876595 : Blo 409770 876595 := bstep (se 1 (by rfl) ⟨657446, by rfl⟩ : syracuseStep 876595 = 1314893) B1314893
theorem B1040435 : Blo 409770 1040435 := bstep (se 1 (by rfl) ⟨780326, by rfl⟩ : syracuseStep 1040435 = 1560653) B1560653
theorem B942131 : Blo 409770 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B1761355 : Blo 409770 1761355 := bstep (se 1 (by rfl) ⟨1321016, by rfl⟩ : syracuseStep 1761355 = 2642033) B2642033
theorem B1761425 : Blo 409770 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B745625 : Blo 409770 745625 := bstep (se 2 (by rfl) ⟨279609, by rfl⟩ : syracuseStep 745625 = 559219) B559219
theorem B614681 : Blo 409770 614681 := bstep (se 2 (by rfl) ⟨230505, by rfl⟩ : syracuseStep 614681 = 461011) B461011
theorem B614795 : Blo 409770 614795 := bstep (se 1 (by rfl) ⟨461096, by rfl⟩ : syracuseStep 614795 = 922193) B922193
theorem B614807 : Blo 409770 614807 := bstep (se 1 (by rfl) ⟨461105, by rfl⟩ : syracuseStep 614807 = 922211) B922211
theorem B876953 : Blo 409770 876953 := bstep (se 2 (by rfl) ⟨328857, by rfl⟩ : syracuseStep 876953 = 657715) B657715
theorem B3531185 : Blo 409770 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B614873 : Blo 409770 614873 := bstep (se 2 (by rfl) ⟨230577, by rfl⟩ : syracuseStep 614873 = 461155) B461155
theorem B614987 : Blo 409770 614987 := bstep (se 1 (by rfl) ⟨461240, by rfl⟩ : syracuseStep 614987 = 922481) B922481
theorem B1040971 : Blo 409770 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B614999 : Blo 409770 614999 := bstep (se 1 (by rfl) ⟨461249, by rfl⟩ : syracuseStep 614999 = 922499) B922499
theorem B1565315 : Blo 409770 1565315 := bstep (se 1 (by rfl) ⟨1173986, by rfl⟩ : syracuseStep 1565315 = 2347973) B2347973
theorem B778891 : Blo 409770 778891 := bstep (se 1 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 778891 = 1168337) B1168337
theorem B615065 : Blo 409770 615065 := bstep (se 2 (by rfl) ⟨230649, by rfl⟩ : syracuseStep 615065 = 461299) B461299
theorem B778967 : Blo 409770 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B1041113 : Blo 409770 1041113 := bstep (se 2 (by rfl) ⟨390417, by rfl⟩ : syracuseStep 1041113 = 780835) B780835
theorem B615179 : Blo 409770 615179 := bstep (se 1 (by rfl) ⟨461384, by rfl⟩ : syracuseStep 615179 = 922769) B922769
theorem B2974481 : Blo 409770 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B615191 : Blo 409770 615191 := bstep (se 1 (by rfl) ⟨461393, by rfl⟩ : syracuseStep 615191 = 922787) B922787
theorem B615257 : Blo 409770 615257 := bstep (se 2 (by rfl) ⟨230721, by rfl⟩ : syracuseStep 615257 = 461443) B461443
theorem B15000497 : Blo 409770 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B5923763 : Blo 409770 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B615371 : Blo 409770 615371 := bstep (se 1 (by rfl) ⟨461528, by rfl⟩ : syracuseStep 615371 = 923057) B923057
theorem B615383 : Blo 409770 615383 := bstep (se 1 (by rfl) ⟨461537, by rfl⟩ : syracuseStep 615383 = 923075) B923075
theorem B615449 : Blo 409770 615449 := bstep (se 2 (by rfl) ⟨230793, by rfl⟩ : syracuseStep 615449 = 461587) B461587
theorem B8479819 : Blo 409770 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B3531869 : Blo 409770 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B615563 : Blo 409770 615563 := bstep (se 1 (by rfl) ⟨461672, by rfl⟩ : syracuseStep 615563 = 923345) B923345
theorem B615575 : Blo 409770 615575 := bstep (se 1 (by rfl) ⟨461681, by rfl⟩ : syracuseStep 615575 = 923363) B923363
theorem B943319 : Blo 409770 943319 := bstep (se 1 (by rfl) ⟨707489, by rfl⟩ : syracuseStep 943319 = 1414979) B1414979
theorem B615641 : Blo 409770 615641 := bstep (se 2 (by rfl) ⟨230865, by rfl⟩ : syracuseStep 615641 = 461731) B461731
theorem B2090285 : Blo 409770 2090285 := bstep (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) B783857
theorem B615755 : Blo 409770 615755 := bstep (se 1 (by rfl) ⟨461816, by rfl⟩ : syracuseStep 615755 = 923633) B923633
theorem B615767 : Blo 409770 615767 := bstep (se 1 (by rfl) ⟨461825, by rfl⟩ : syracuseStep 615767 = 923651) B923651
theorem B1172825 : Blo 409770 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B779635 : Blo 409770 779635 := bstep (se 1 (by rfl) ⟨584726, by rfl⟩ : syracuseStep 779635 = 1169453) B1169453
theorem B615833 : Blo 409770 615833 := bstep (se 2 (by rfl) ⟨230937, by rfl⟩ : syracuseStep 615833 = 461875) B461875
theorem B615947 : Blo 409770 615947 := bstep (se 1 (by rfl) ⟨461960, by rfl⟩ : syracuseStep 615947 = 923921) B923921
theorem B615959 : Blo 409770 615959 := bstep (se 1 (by rfl) ⟨461969, by rfl⟩ : syracuseStep 615959 = 923939) B923939
theorem B1041943 : Blo 409770 1041943 := bstep (se 1 (by rfl) ⟨781457, by rfl⟩ : syracuseStep 1041943 = 1562915) B1562915
theorem B779863 : Blo 409770 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B616025 : Blo 409770 616025 := bstep (se 2 (by rfl) ⟨231009, by rfl⟩ : syracuseStep 616025 = 462019) B462019
theorem B1173143 : Blo 409770 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B779969 : Blo 409770 779969 := bstep (se 2 (by rfl) ⟨292488, by rfl⟩ : syracuseStep 779969 = 584977) B584977
theorem B616139 : Blo 409770 616139 := bstep (se 1 (by rfl) ⟨462104, by rfl⟩ : syracuseStep 616139 = 924209) B924209
theorem B616151 : Blo 409770 616151 := bstep (se 1 (by rfl) ⟨462113, by rfl⟩ : syracuseStep 616151 = 924227) B924227
theorem B616217 : Blo 409770 616217 := bstep (se 2 (by rfl) ⟨231081, by rfl⟩ : syracuseStep 616217 = 462163) B462163
theorem B1763117 : Blo 409770 1763117 := bstep (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) B661169
theorem B780121 : Blo 409770 780121 := bstep (se 2 (by rfl) ⟨292545, by rfl⟩ : syracuseStep 780121 = 585091) B585091
theorem B616331 : Blo 409770 616331 := bstep (se 1 (by rfl) ⟨462248, by rfl⟩ : syracuseStep 616331 = 924497) B924497
theorem B616343 : Blo 409770 616343 := bstep (se 1 (by rfl) ⟨462257, by rfl⟩ : syracuseStep 616343 = 924515) B924515
theorem B2418611 : Blo 409770 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B1042379 : Blo 409770 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B616409 : Blo 409770 616409 := bstep (se 2 (by rfl) ⟨231153, by rfl⟩ : syracuseStep 616409 = 462307) B462307
theorem B2680897 : Blo 409770 2680897 := bstep (se 2 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 2680897 = 2010673) B2010673
theorem B616523 : Blo 409770 616523 := bstep (se 1 (by rfl) ⟨462392, by rfl⟩ : syracuseStep 616523 = 924785) B924785
theorem B616535 : Blo 409770 616535 := bstep (se 1 (by rfl) ⟨462401, by rfl⟩ : syracuseStep 616535 = 924803) B924803
theorem B616601 : Blo 409770 616601 := bstep (se 2 (by rfl) ⟨231225, by rfl⟩ : syracuseStep 616601 = 462451) B462451
theorem B583895 : Blo 409770 583895 := bstep (se 1 (by rfl) ⟨437921, by rfl⟩ : syracuseStep 583895 = 875843) B875843
theorem B616715 : Blo 409770 616715 := bstep (se 1 (by rfl) ⟨462536, by rfl⟩ : syracuseStep 616715 = 925073) B925073
theorem B616727 : Blo 409770 616727 := bstep (se 1 (by rfl) ⟨462545, by rfl⟩ : syracuseStep 616727 = 925091) B925091
theorem B1042753 : Blo 409770 1042753 := bstep (se 2 (by rfl) ⟨391032, by rfl⟩ : syracuseStep 1042753 = 782065) B782065
theorem B616793 : Blo 409770 616793 := bstep (se 2 (by rfl) ⟨231297, by rfl⟩ : syracuseStep 616793 = 462595) B462595
theorem B878987 : Blo 409770 878987 := bstep (se 1 (by rfl) ⟨659240, by rfl⟩ : syracuseStep 878987 = 1318481) B1318481
theorem B1173953 : Blo 409770 1173953 := bstep (se 2 (by rfl) ⟨440232, by rfl⟩ : syracuseStep 1173953 = 880465) B880465
theorem B616907 : Blo 409770 616907 := bstep (se 1 (by rfl) ⟨462680, by rfl⟩ : syracuseStep 616907 = 925361) B925361
theorem B3140045 : Blo 409770 3140045 := bstep (se 3 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 3140045 = 1177517) B1177517
theorem B616919 : Blo 409770 616919 := bstep (se 1 (by rfl) ⟨462689, by rfl⟩ : syracuseStep 616919 = 925379) B925379
theorem B1763801 : Blo 409770 1763801 := bstep (se 2 (by rfl) ⟨661425, by rfl⟩ : syracuseStep 1763801 = 1322851) B1322851
theorem B616985 : Blo 409770 616985 := bstep (se 2 (by rfl) ⟨231369, by rfl⟩ : syracuseStep 616985 = 462739) B462739
theorem B617099 : Blo 409770 617099 := bstep (se 1 (by rfl) ⟨462824, by rfl⟩ : syracuseStep 617099 = 925649) B925649
theorem B617111 : Blo 409770 617111 := bstep (se 1 (by rfl) ⟨462833, by rfl⟩ : syracuseStep 617111 = 925667) B925667
theorem B617177 : Blo 409770 617177 := bstep (se 2 (by rfl) ⟨231441, by rfl⟩ : syracuseStep 617177 = 462883) B462883
theorem B518987 : Blo 409770 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B617291 : Blo 409770 617291 := bstep (se 1 (by rfl) ⟨462968, by rfl⟩ : syracuseStep 617291 = 925937) B925937
theorem B617303 : Blo 409770 617303 := bstep (se 1 (by rfl) ⟨462977, by rfl⟩ : syracuseStep 617303 = 925955) B925955
theorem B1043351 : Blo 409770 1043351 := bstep (se 1 (by rfl) ⟨782513, by rfl⟩ : syracuseStep 1043351 = 1565027) B1565027
theorem B617369 : Blo 409770 617369 := bstep (se 2 (by rfl) ⟨231513, by rfl⟩ : syracuseStep 617369 = 463027) B463027
theorem B3140531 : Blo 409770 3140531 := bstep (se 1 (by rfl) ⟨2355398, by rfl⟩ : syracuseStep 3140531 = 4710797) B4710797
theorem B617483 : Blo 409770 617483 := bstep (se 1 (by rfl) ⟨463112, by rfl⟩ : syracuseStep 617483 = 926225) B926225
theorem B617495 : Blo 409770 617495 := bstep (se 1 (by rfl) ⟨463121, by rfl⟩ : syracuseStep 617495 = 926243) B926243
theorem B617561 : Blo 409770 617561 := bstep (se 2 (by rfl) ⟨231585, by rfl⟩ : syracuseStep 617561 = 463171) B463171
theorem B781427 : Blo 409770 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B617675 : Blo 409770 617675 := bstep (se 1 (by rfl) ⟨463256, by rfl⟩ : syracuseStep 617675 = 926513) B926513
theorem B617687 : Blo 409770 617687 := bstep (se 1 (by rfl) ⟨463265, by rfl⟩ : syracuseStep 617687 = 926531) B926531
theorem B781579 : Blo 409770 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B617753 : Blo 409770 617753 := bstep (se 2 (by rfl) ⟨231657, by rfl⟩ : syracuseStep 617753 = 463315) B463315
theorem B617867 : Blo 409770 617867 := bstep (se 1 (by rfl) ⟨463400, by rfl⟩ : syracuseStep 617867 = 926801) B926801
theorem B617879 : Blo 409770 617879 := bstep (se 1 (by rfl) ⟨463409, by rfl⟩ : syracuseStep 617879 = 926819) B926819
theorem B2813363 : Blo 409770 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B617945 : Blo 409770 617945 := bstep (se 2 (by rfl) ⟨231729, by rfl⟩ : syracuseStep 617945 = 463459) B463459
theorem B519691 : Blo 409770 519691 := bstep (se 1 (by rfl) ⟨389768, by rfl⟩ : syracuseStep 519691 = 779537) B779537
theorem B618059 : Blo 409770 618059 := bstep (se 1 (by rfl) ⟨463544, by rfl⟩ : syracuseStep 618059 = 927089) B927089
theorem B618071 : Blo 409770 618071 := bstep (se 1 (by rfl) ⟨463553, by rfl⟩ : syracuseStep 618071 = 927107) B927107
theorem B781913 : Blo 409770 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B880217 : Blo 409770 880217 := bstep (se 2 (by rfl) ⟨330081, by rfl⟩ : syracuseStep 880217 = 660163) B660163
theorem B618137 : Blo 409770 618137 := bstep (se 2 (by rfl) ⟨231801, by rfl⟩ : syracuseStep 618137 = 463603) B463603
theorem B1568429 : Blo 409770 1568429 := bstep (se 3 (by rfl) ⟨294080, by rfl⟩ : syracuseStep 1568429 = 588161) B588161
theorem B1044161 : Blo 409770 1044161 := bstep (se 2 (by rfl) ⟨391560, by rfl⟩ : syracuseStep 1044161 = 783121) B783121
theorem B6942449 : Blo 409770 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B618251 : Blo 409770 618251 := bstep (se 1 (by rfl) ⟨463688, by rfl⟩ : syracuseStep 618251 = 927377) B927377
theorem B519959 : Blo 409770 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B618263 : Blo 409770 618263 := bstep (se 1 (by rfl) ⟨463697, by rfl⟩ : syracuseStep 618263 = 927395) B927395
theorem B618329 : Blo 409770 618329 := bstep (se 2 (by rfl) ⟨231873, by rfl⟩ : syracuseStep 618329 = 463747) B463747
theorem B618443 : Blo 409770 618443 := bstep (se 1 (by rfl) ⟨463832, by rfl⟩ : syracuseStep 618443 = 927665) B927665
theorem B618455 : Blo 409770 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B880627 : Blo 409770 880627 := bstep (se 1 (by rfl) ⟨660470, by rfl⟩ : syracuseStep 880627 = 1320941) B1320941
theorem B618521 : Blo 409770 618521 := bstep (se 2 (by rfl) ⟨231945, by rfl⟩ : syracuseStep 618521 = 463891) B463891
theorem B1175627 : Blo 409770 1175627 := bstep (se 1 (by rfl) ⟨881720, by rfl⟩ : syracuseStep 1175627 = 1763441) B1763441
theorem B618635 : Blo 409770 618635 := bstep (se 1 (by rfl) ⟨463976, by rfl⟩ : syracuseStep 618635 = 927953) B927953
theorem B618647 : Blo 409770 618647 := bstep (se 1 (by rfl) ⟨463985, by rfl⟩ : syracuseStep 618647 = 927971) B927971
theorem B8876213 : Blo 409770 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B782551 : Blo 409770 782551 := bstep (se 1 (by rfl) ⟨586913, by rfl⟩ : syracuseStep 782551 = 1173827) B1173827
theorem B618713 : Blo 409770 618713 := bstep (se 2 (by rfl) ⟨232017, by rfl⟩ : syracuseStep 618713 = 464035) B464035
theorem B1044697 : Blo 409770 1044697 := bstep (se 2 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 1044697 = 783523) B783523
theorem B880883 : Blo 409770 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B618827 : Blo 409770 618827 := bstep (se 1 (by rfl) ⟨464120, by rfl⟩ : syracuseStep 618827 = 928241) B928241
theorem B618839 : Blo 409770 618839 := bstep (se 1 (by rfl) ⟨464129, by rfl⟩ : syracuseStep 618839 = 928259) B928259
theorem B1110361 : Blo 409770 1110361 := bstep (se 2 (by rfl) ⟨416385, by rfl⟩ : syracuseStep 1110361 = 832771) B832771
theorem B3141989 : Blo 409770 3141989 := bstep (se 4 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 3141989 = 589123) B589123
theorem B618905 : Blo 409770 618905 := bstep (se 2 (by rfl) ⟨232089, by rfl⟩ : syracuseStep 618905 = 464179) B464179
theorem B1569203 : Blo 409770 1569203 := bstep (se 1 (by rfl) ⟨1176902, by rfl⟩ : syracuseStep 1569203 = 2353805) B2353805
theorem B520663 : Blo 409770 520663 := bstep (se 1 (by rfl) ⟨390497, by rfl⟩ : syracuseStep 520663 = 780995) B780995
theorem B619019 : Blo 409770 619019 := bstep (se 1 (by rfl) ⟨464264, by rfl⟩ : syracuseStep 619019 = 928529) B928529
theorem B619031 : Blo 409770 619031 := bstep (se 1 (by rfl) ⟨464273, by rfl⟩ : syracuseStep 619031 = 928547) B928547
theorem B619097 : Blo 409770 619097 := bstep (se 2 (by rfl) ⟨232161, by rfl⟩ : syracuseStep 619097 = 464323) B464323
theorem B619211 : Blo 409770 619211 := bstep (se 1 (by rfl) ⟨464408, by rfl⟩ : syracuseStep 619211 = 928817) B928817
theorem B619223 : Blo 409770 619223 := bstep (se 1 (by rfl) ⟨464417, by rfl⟩ : syracuseStep 619223 = 928835) B928835
theorem B3994373 : Blo 409770 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B619289 : Blo 409770 619289 := bstep (se 2 (by rfl) ⟨232233, by rfl⟩ : syracuseStep 619289 = 464467) B464467
theorem B5370725 : Blo 409770 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B619403 : Blo 409770 619403 := bstep (se 1 (by rfl) ⟨464552, by rfl⟩ : syracuseStep 619403 = 929105) B929105
theorem B619415 : Blo 409770 619415 := bstep (se 1 (by rfl) ⟨464561, by rfl⟩ : syracuseStep 619415 = 929123) B929123
theorem B3503027 : Blo 409770 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B619481 : Blo 409770 619481 := bstep (se 2 (by rfl) ⟨232305, by rfl⟩ : syracuseStep 619481 = 464611) B464611
theorem B783371 : Blo 409770 783371 := bstep (se 1 (by rfl) ⟨587528, by rfl⟩ : syracuseStep 783371 = 1175057) B1175057
theorem B586777 : Blo 409770 586777 := bstep (se 2 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 586777 = 440083) B440083
theorem B783425 : Blo 409770 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B816193 : Blo 409770 816193 := bstep (se 2 (by rfl) ⟨306072, by rfl⟩ : syracuseStep 816193 = 612145) B612145
theorem B2356289 : Blo 409770 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B3175499 : Blo 409770 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B619595 : Blo 409770 619595 := bstep (se 1 (by rfl) ⟨464696, by rfl⟩ : syracuseStep 619595 = 929393) B929393
theorem B619607 : Blo 409770 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B2094173 : Blo 409770 2094173 := bstep (se 3 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 2094173 = 785315) B785315
theorem B619673 : Blo 409770 619673 := bstep (se 2 (by rfl) ⟨232377, by rfl⟩ : syracuseStep 619673 = 464755) B464755
theorem B881857 : Blo 409770 881857 := bstep (se 2 (by rfl) ⟨330696, by rfl⟩ : syracuseStep 881857 = 661393) B661393
theorem B3339481 : Blo 409770 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B619787 : Blo 409770 619787 := bstep (se 1 (by rfl) ⟨464840, by rfl⟩ : syracuseStep 619787 = 929681) B929681
theorem B619799 : Blo 409770 619799 := bstep (se 1 (by rfl) ⟨464849, by rfl⟩ : syracuseStep 619799 = 929699) B929699
theorem B1668397 : Blo 409770 1668397 := bstep (se 3 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 1668397 = 625649) B625649
theorem B1045811 : Blo 409770 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B619865 : Blo 409770 619865 := bstep (se 2 (by rfl) ⟨232449, by rfl⟩ : syracuseStep 619865 = 464899) B464899
theorem B1176925 : Blo 409770 1176925 := bstep (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) B441347
theorem B619979 : Blo 409770 619979 := bstep (se 1 (by rfl) ⟨464984, by rfl⟩ : syracuseStep 619979 = 929969) B929969
theorem B619991 : Blo 409770 619991 := bstep (se 1 (by rfl) ⟨464993, by rfl⟩ : syracuseStep 619991 = 929987) B929987
theorem B620057 : Blo 409770 620057 := bstep (se 2 (by rfl) ⟨232521, by rfl⟩ : syracuseStep 620057 = 465043) B465043
theorem B1046105 : Blo 409770 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B620171 : Blo 409770 620171 := bstep (se 1 (by rfl) ⟨465128, by rfl⟩ : syracuseStep 620171 = 930257) B930257
theorem B620183 : Blo 409770 620183 := bstep (se 1 (by rfl) ⟨465137, by rfl⟩ : syracuseStep 620183 = 930275) B930275
theorem B1177267 : Blo 409770 1177267 := bstep (se 1 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 1177267 = 1765901) B1765901
theorem B1111745 : Blo 409770 1111745 := bstep (se 2 (by rfl) ⟨416904, by rfl⟩ : syracuseStep 1111745 = 833809) B833809
theorem B620249 : Blo 409770 620249 := bstep (se 2 (by rfl) ⟨232593, by rfl⟩ : syracuseStep 620249 = 465187) B465187
theorem B1767233 : Blo 409770 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B620363 : Blo 409770 620363 := bstep (se 1 (by rfl) ⟨465272, by rfl⟩ : syracuseStep 620363 = 930545) B930545
theorem B620375 : Blo 409770 620375 := bstep (se 1 (by rfl) ⟨465281, by rfl⟩ : syracuseStep 620375 = 930563) B930563
theorem B1570691 : Blo 409770 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B620441 : Blo 409770 620441 := bstep (se 2 (by rfl) ⟨232665, by rfl⟩ : syracuseStep 620441 = 465331) B465331
theorem B784343 : Blo 409770 784343 := bstep (se 1 (by rfl) ⟨588257, by rfl⟩ : syracuseStep 784343 = 1176515) B1176515
theorem B620555 : Blo 409770 620555 := bstep (se 1 (by rfl) ⟨465416, by rfl⟩ : syracuseStep 620555 = 930833) B930833
theorem B620567 : Blo 409770 620567 := bstep (se 1 (by rfl) ⟨465425, by rfl⟩ : syracuseStep 620567 = 930851) B930851
theorem B620633 : Blo 409770 620633 := bstep (se 2 (by rfl) ⟨232737, by rfl⟩ : syracuseStep 620633 = 465475) B465475
theorem B522379 : Blo 409770 522379 := bstep (se 1 (by rfl) ⟨391784, by rfl⟩ : syracuseStep 522379 = 783569) B783569
theorem B588235 : Blo 409770 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B784883 : Blo 409770 784883 := bstep (se 1 (by rfl) ⟨588662, by rfl⟩ : syracuseStep 784883 = 1177325) B1177325
theorem B1178201 : Blo 409770 1178201 := bstep (se 2 (by rfl) ⟨441825, by rfl⟩ : syracuseStep 1178201 = 883651) B883651
theorem B752395 : Blo 409770 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B3767057 : Blo 409770 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B3504941 : Blo 409770 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B3111857 : Blo 409770 3111857 := bstep (se 2 (by rfl) ⟨1166946, by rfl⟩ : syracuseStep 3111857 = 2333893) B2333893
theorem B785369 : Blo 409770 785369 := bstep (se 2 (by rfl) ⟨294513, by rfl⟩ : syracuseStep 785369 = 589027) B589027
theorem B523351 : Blo 409770 523351 := bstep (se 1 (by rfl) ⟨392513, by rfl⟩ : syracuseStep 523351 = 785027) B785027
theorem B3112343 : Blo 409770 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B3505625 : Blo 409770 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B1113821 : Blo 409770 1113821 := bstep (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) B417683
theorem B1671005 : Blo 409770 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B1114739 : Blo 409770 1114739 := bstep (se 1 (by rfl) ⟨836054, by rfl⟩ : syracuseStep 1114739 = 1672109) B1672109
theorem B623561 : Blo 409770 623561 := bstep (se 2 (by rfl) ⟨233835, by rfl⟩ : syracuseStep 623561 = 467671) B467671
theorem B3507401 : Blo 409770 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B1672595 : Blo 409770 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B11306425 : Blo 409770 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B36537925 : Blo 409770 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B7603789 : Blo 409770 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B558991 : Blo 409770 558991 := bstep (se 1 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 558991 = 838487) B838487
theorem B952211 : Blo 409770 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B10651661 : Blo 409770 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B461191 : Blo 409770 461191 := bstep (se 1 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 461191 = 691787) B691787
theorem B461371 : Blo 409770 461371 := bstep (se 1 (by rfl) ⟨346028, by rfl⟩ : syracuseStep 461371 = 692057) B692057
theorem B1116857 : Blo 409770 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B3574529 : Blo 409770 3574529 := bstep (se 2 (by rfl) ⟨1340448, by rfl⟩ : syracuseStep 3574529 = 2680897) B2680897
theorem B3509041 : Blo 409770 3509041 := bstep (se 2 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 3509041 = 2631781) B2631781
theorem B13306787 : Blo 409770 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B1248185 : Blo 409770 1248185 := bstep (se 2 (by rfl) ⟨468069, by rfl⟩ : syracuseStep 1248185 = 936139) B936139
theorem B461839 : Blo 409770 461839 := bstep (se 1 (by rfl) ⟨346379, by rfl⟩ : syracuseStep 461839 = 692759) B692759
theorem B1805431 : Blo 409770 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B789689 : Blo 409770 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B494839 : Blo 409770 494839 := bstep (se 1 (by rfl) ⟨371129, by rfl⟩ : syracuseStep 494839 = 742259) B742259
theorem B691591 : Blo 409770 691591 := bstep (se 1 (by rfl) ⟨518693, by rfl⟩ : syracuseStep 691591 = 1037387) B1037387
theorem B1969667 : Blo 409770 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B462343 : Blo 409770 462343 := bstep (se 1 (by rfl) ⟨346757, by rfl⟩ : syracuseStep 462343 = 693515) B693515
theorem B462523 : Blo 409770 462523 := bstep (se 1 (by rfl) ⟨346892, by rfl⟩ : syracuseStep 462523 = 693785) B693785
theorem B986995 : Blo 409770 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B692239 : Blo 409770 692239 := bstep (se 1 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 692239 = 1038359) B1038359
theorem B987169 : Blo 409770 987169 := bstep (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) B740377
theorem B462991 : Blo 409770 462991 := bstep (se 1 (by rfl) ⟨347243, by rfl⟩ : syracuseStep 462991 = 694487) B694487
theorem B4690385 : Blo 409770 4690385 := bstep (se 2 (by rfl) ⟨1758894, by rfl⟩ : syracuseStep 4690385 = 3517789) B3517789
theorem B4231709 : Blo 409770 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B692779 : Blo 409770 692779 := bstep (se 1 (by rfl) ⟨519584, by rfl⟩ : syracuseStep 692779 = 1039169) B1039169
theorem B2036267 : Blo 409770 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B2232893 : Blo 409770 2232893 := bstep (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) B837335
theorem B922247 : Blo 409770 922247 := bstep (se 1 (by rfl) ⟨691685, by rfl⟩ : syracuseStep 922247 = 1383371) B1383371
theorem B463495 : Blo 409770 463495 := bstep (se 1 (by rfl) ⟨347621, by rfl⟩ : syracuseStep 463495 = 695243) B695243
theorem B692921 : Blo 409770 692921 := bstep (se 2 (by rfl) ⟨259845, by rfl⟩ : syracuseStep 692921 = 519691) B519691
theorem B1676065 : Blo 409770 1676065 := bstep (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) B1257049
theorem B922427 : Blo 409770 922427 := bstep (se 1 (by rfl) ⟨691820, by rfl⟩ : syracuseStep 922427 = 1383641) B1383641
theorem B463675 : Blo 409770 463675 := bstep (se 1 (by rfl) ⟨347756, by rfl⟩ : syracuseStep 463675 = 695513) B695513
theorem B1250167 : Blo 409770 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B922553 : Blo 409770 922553 := bstep (se 2 (by rfl) ⟨345957, by rfl⟩ : syracuseStep 922553 = 691915) B691915
theorem B922895 : Blo 409770 922895 := bstep (se 1 (by rfl) ⟨692171, by rfl⟩ : syracuseStep 922895 = 1384343) B1384343
theorem B464143 : Blo 409770 464143 := bstep (se 1 (by rfl) ⟨348107, by rfl⟩ : syracuseStep 464143 = 696215) B696215
theorem B922913 : Blo 409770 922913 := bstep (se 2 (by rfl) ⟨346092, by rfl⟩ : syracuseStep 922913 = 692185) B692185
theorem B693623 : Blo 409770 693623 := bstep (se 1 (by rfl) ⟨520217, by rfl⟩ : syracuseStep 693623 = 1040435) B1040435
theorem B628087 : Blo 409770 628087 := bstep (se 1 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 628087 = 942131) B942131
theorem B2954819 : Blo 409770 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B923255 : Blo 409770 923255 := bstep (se 1 (by rfl) ⟨692441, by rfl⟩ : syracuseStep 923255 = 1384883) B1384883
theorem B4462199 : Blo 409770 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B2233975 : Blo 409770 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B464647 : Blo 409770 464647 := bstep (se 1 (by rfl) ⟨348485, by rfl⟩ : syracuseStep 464647 = 696971) B696971
theorem B1480481 : Blo 409770 1480481 := bstep (se 2 (by rfl) ⟨555180, by rfl⟩ : syracuseStep 1480481 = 1110361) B1110361
theorem B923435 : Blo 409770 923435 := bstep (se 1 (by rfl) ⟨692576, by rfl⟩ : syracuseStep 923435 = 1385153) B1385153
theorem B694075 : Blo 409770 694075 := bstep (se 1 (by rfl) ⟨520556, by rfl⟩ : syracuseStep 694075 = 1041113) B1041113
theorem B464827 : Blo 409770 464827 := bstep (se 1 (by rfl) ⟨348620, by rfl⟩ : syracuseStep 464827 = 697241) B697241
theorem B694217 : Blo 409770 694217 := bstep (se 2 (by rfl) ⟨260331, by rfl⟩ : syracuseStep 694217 = 520663) B520663
theorem B10000331 : Blo 409770 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B661547 : Blo 409770 661547 := bstep (se 1 (by rfl) ⟨496160, by rfl⟩ : syracuseStep 661547 = 992321) B992321
theorem B628879 : Blo 409770 628879 := bstep (se 1 (by rfl) ⟨471659, by rfl⟩ : syracuseStep 628879 = 943319) B943319
theorem B923795 : Blo 409770 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B923849 : Blo 409770 923849 := bstep (se 2 (by rfl) ⟨346443, by rfl⟩ : syracuseStep 923849 = 692887) B692887
theorem B891169 : Blo 409770 891169 := bstep (se 2 (by rfl) ⟨334188, by rfl⟩ : syracuseStep 891169 = 668377) B668377
theorem B465295 : Blo 409770 465295 := bstep (se 1 (by rfl) ⟨348971, by rfl⟩ : syracuseStep 465295 = 697943) B697943
theorem B694919 : Blo 409770 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B1088257 : Blo 409770 1088257 := bstep (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) B816193
theorem B1252111 : Blo 409770 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B2235251 : Blo 409770 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B990071 : Blo 409770 990071 := bstep (se 1 (by rfl) ⟨742553, by rfl⟩ : syracuseStep 990071 = 1485107) B1485107
theorem B924551 : Blo 409770 924551 := bstep (se 1 (by rfl) ⟨693413, by rfl⟩ : syracuseStep 924551 = 1386827) B1386827
theorem B924731 : Blo 409770 924731 := bstep (se 1 (by rfl) ⟨693548, by rfl⟩ : syracuseStep 924731 = 1387097) B1387097
theorem B924857 : Blo 409770 924857 := bstep (se 2 (by rfl) ⟨346821, by rfl⟩ : syracuseStep 924857 = 693643) B693643
theorem B1383695 : Blo 409770 1383695 := bstep (se 1 (by rfl) ⟨1037771, by rfl⟩ : syracuseStep 1383695 = 2075543) B2075543
theorem B695567 : Blo 409770 695567 := bstep (se 1 (by rfl) ⟨521675, by rfl⟩ : syracuseStep 695567 = 1043351) B1043351
theorem B2235707 : Blo 409770 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B3939677 : Blo 409770 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B6495623 : Blo 409770 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1252793 : Blo 409770 1252793 := bstep (se 2 (by rfl) ⟨469797, by rfl⟩ : syracuseStep 1252793 = 939595) B939595
theorem B3120605 : Blo 409770 3120605 := bstep (se 3 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 3120605 = 1170227) B1170227
theorem B925199 : Blo 409770 925199 := bstep (se 1 (by rfl) ⟨693899, by rfl⟩ : syracuseStep 925199 = 1387799) B1387799
theorem B1383965 : Blo 409770 1383965 := bstep (se 3 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 1383965 = 518987) B518987
theorem B925217 : Blo 409770 925217 := bstep (se 2 (by rfl) ⟨346956, by rfl⟩ : syracuseStep 925217 = 693913) B693913
theorem B1875575 : Blo 409770 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B696107 : Blo 409770 696107 := bstep (se 1 (by rfl) ⟨522080, by rfl⟩ : syracuseStep 696107 = 1044161) B1044161
theorem B991091 : Blo 409770 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B925559 : Blo 409770 925559 := bstep (se 1 (by rfl) ⟨694169, by rfl⟩ : syracuseStep 925559 = 1388339) B1388339
theorem B925739 : Blo 409770 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B696505 : Blo 409770 696505 := bstep (se 2 (by rfl) ⟨261189, by rfl⟩ : syracuseStep 696505 = 522379) B522379
theorem B1253693 : Blo 409770 1253693 := bstep (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) B470135
theorem B926099 : Blo 409770 926099 := bstep (se 1 (by rfl) ⟨694574, by rfl⟩ : syracuseStep 926099 = 1389149) B1389149
theorem B926153 : Blo 409770 926153 := bstep (se 2 (by rfl) ⟨347307, by rfl⟩ : syracuseStep 926153 = 694615) B694615
theorem B1188413 : Blo 409770 1188413 := bstep (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) B445655
theorem B3580483 : Blo 409770 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B2335351 : Blo 409770 2335351 := bstep (se 1 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 2335351 = 3503027) B3503027
theorem B992033 : Blo 409770 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B5251877 : Blo 409770 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B697207 : Blo 409770 697207 := bstep (se 1 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 697207 = 1045811) B1045811
theorem B1385369 : Blo 409770 1385369 := bstep (se 2 (by rfl) ⟨519513, by rfl⟩ : syracuseStep 1385369 = 1039027) B1039027
theorem B697403 : Blo 409770 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B22848581 : Blo 409770 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B7611479 : Blo 409770 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B926855 : Blo 409770 926855 := bstep (se 1 (by rfl) ⟨695141, by rfl⟩ : syracuseStep 926855 = 1390283) B1390283
theorem B927035 : Blo 409770 927035 := bstep (se 1 (by rfl) ⟨695276, by rfl⟩ : syracuseStep 927035 = 1390553) B1390553
theorem B927161 : Blo 409770 927161 := bstep (se 2 (by rfl) ⟨347685, by rfl⟩ : syracuseStep 927161 = 695371) B695371
theorem B697801 : Blo 409770 697801 := bstep (se 2 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 697801 = 523351) B523351
theorem B1386071 : Blo 409770 1386071 := bstep (se 1 (by rfl) ⟨1039553, by rfl⟩ : syracuseStep 1386071 = 2079107) B2079107
theorem B927503 : Blo 409770 927503 := bstep (se 1 (by rfl) ⟨695627, by rfl⟩ : syracuseStep 927503 = 1391255) B1391255
theorem B927521 : Blo 409770 927521 := bstep (se 2 (by rfl) ⟨347820, by rfl⟩ : syracuseStep 927521 = 695641) B695641
theorem B2336627 : Blo 409770 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B2074571 : Blo 409770 2074571 := bstep (se 1 (by rfl) ⟨1555928, by rfl⟩ : syracuseStep 2074571 = 3111857) B3111857
theorem B1386557 : Blo 409770 1386557 := bstep (se 3 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 1386557 = 519959) B519959
theorem B927863 : Blo 409770 927863 := bstep (se 1 (by rfl) ⟨695897, by rfl⟩ : syracuseStep 927863 = 1391795) B1391795
theorem B2074895 : Blo 409770 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B928043 : Blo 409770 928043 := bstep (se 1 (by rfl) ⟨696032, by rfl⟩ : syracuseStep 928043 = 1392065) B1392065
theorem B2337083 : Blo 409770 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B3648077 : Blo 409770 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B928403 : Blo 409770 928403 := bstep (se 1 (by rfl) ⟨696302, by rfl⟩ : syracuseStep 928403 = 1392605) B1392605
theorem B928457 : Blo 409770 928457 := bstep (se 2 (by rfl) ⟨348171, by rfl⟩ : syracuseStep 928457 = 696343) B696343
theorem B1190771 : Blo 409770 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B2632601 : Blo 409770 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B5614679 : Blo 409770 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B1256563 : Blo 409770 1256563 := bstep (se 1 (by rfl) ⟨942422, by rfl⟩ : syracuseStep 1256563 = 1884845) B1884845
theorem B2338085 : Blo 409770 2338085 := bstep (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) B438391
theorem B929159 : Blo 409770 929159 := bstep (se 1 (by rfl) ⟨696869, by rfl⟩ : syracuseStep 929159 = 1393739) B1393739
theorem B1387961 : Blo 409770 1387961 := bstep (se 2 (by rfl) ⟨520485, by rfl⟩ : syracuseStep 1387961 = 1040971) B1040971
theorem B1486289 : Blo 409770 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B929339 : Blo 409770 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B929465 : Blo 409770 929465 := bstep (se 2 (by rfl) ⟨348549, by rfl⟩ : syracuseStep 929465 = 697099) B697099
theorem B2076353 : Blo 409770 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B2338541 : Blo 409770 2338541 := bstep (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) B876953
theorem B1978127 : Blo 409770 1978127 := bstep (se 1 (by rfl) ⟨1483595, by rfl⟩ : syracuseStep 1978127 = 2967191) B2967191
theorem B1879955 : Blo 409770 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B1388555 : Blo 409770 1388555 := bstep (se 1 (by rfl) ⟨1041416, by rfl⟩ : syracuseStep 1388555 = 2082833) B2082833
theorem B929807 : Blo 409770 929807 := bstep (se 1 (by rfl) ⟨697355, by rfl⟩ : syracuseStep 929807 = 1394711) B1394711
theorem B929825 : Blo 409770 929825 := bstep (se 2 (by rfl) ⟨348684, by rfl⟩ : syracuseStep 929825 = 697369) B697369
theorem B1388663 : Blo 409770 1388663 := bstep (se 1 (by rfl) ⟨1041497, by rfl⟩ : syracuseStep 1388663 = 2082995) B2082995
theorem B7909649 : Blo 409770 7909649 := bstep (se 2 (by rfl) ⟨2966118, by rfl⟩ : syracuseStep 7909649 = 5932237) B5932237
theorem B930167 : Blo 409770 930167 := bstep (se 1 (by rfl) ⟨697625, by rfl⟩ : syracuseStep 930167 = 1395251) B1395251
theorem B2339225 : Blo 409770 2339225 := bstep (se 2 (by rfl) ⟨877209, by rfl⟩ : syracuseStep 2339225 = 1754419) B1754419
theorem B930347 : Blo 409770 930347 := bstep (se 1 (by rfl) ⟨697760, by rfl⟩ : syracuseStep 930347 = 1395521) B1395521
theorem B1389257 : Blo 409770 1389257 := bstep (se 2 (by rfl) ⟨520971, by rfl⟩ : syracuseStep 1389257 = 1041943) B1041943
theorem B9679621 : Blo 409770 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B930707 : Blo 409770 930707 := bstep (se 1 (by rfl) ⟨698030, by rfl⟩ : syracuseStep 930707 = 1396061) B1396061
theorem B930761 : Blo 409770 930761 := bstep (se 2 (by rfl) ⟨349035, by rfl⟩ : syracuseStep 930761 = 698071) B698071
theorem B2077649 : Blo 409770 2077649 := bstep (se 2 (by rfl) ⟨779118, by rfl⟩ : syracuseStep 2077649 = 1558237) B1558237
theorem B1782827 : Blo 409770 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B1389959 : Blo 409770 1389959 := bstep (se 1 (by rfl) ⟨1042469, by rfl⟩ : syracuseStep 1389959 = 2084939) B2084939
theorem B2635267 : Blo 409770 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B1488395 : Blo 409770 1488395 := bstep (se 1 (by rfl) ⟨1116296, by rfl⟩ : syracuseStep 1488395 = 2232593) B2232593
theorem B1488451 : Blo 409770 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B2012759 : Blo 409770 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B2111233 : Blo 409770 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B1390337 : Blo 409770 1390337 := bstep (se 2 (by rfl) ⟨521376, by rfl⟩ : syracuseStep 1390337 = 1042753) B1042753
theorem B3520523 : Blo 409770 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B1325117 : Blo 409770 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B1391147 : Blo 409770 1391147 := bstep (se 1 (by rfl) ⟨1043360, by rfl⟩ : syracuseStep 1391147 = 2086721) B2086721
theorem B1981217 : Blo 409770 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B2964275 : Blo 409770 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1751993 : Blo 409770 1751993 := bstep (se 2 (by rfl) ⟨656997, by rfl⟩ : syracuseStep 1751993 = 1313995) B1313995
theorem B2079755 : Blo 409770 2079755 := bstep (se 1 (by rfl) ⟨1559816, by rfl⟩ : syracuseStep 2079755 = 3119633) B3119633
theorem B3128381 : Blo 409770 3128381 := bstep (se 3 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 3128381 = 1173143) B1173143
theorem B2079917 : Blo 409770 2079917 := bstep (se 3 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 2079917 = 779969) B779969
theorem B1752455 : Blo 409770 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B3554705 : Blo 409770 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B1392443 : Blo 409770 1392443 := bstep (se 1 (by rfl) ⟨1044332, by rfl⟩ : syracuseStep 1392443 = 2088665) B2088665
theorem B2342915 : Blo 409770 2342915 := bstep (se 1 (by rfl) ⟨1757186, by rfl⟩ : syracuseStep 2342915 = 3514373) B3514373
theorem B1556567 : Blo 409770 1556567 := bstep (se 1 (by rfl) ⟨1167425, by rfl⟩ : syracuseStep 1556567 = 2334851) B2334851
theorem B409787 : Blo 409770 409787 := bstep (se 1 (by rfl) ⟨307340, by rfl⟩ : syracuseStep 409787 = 614681) B614681
theorem B409863 : Blo 409770 409863 := bstep (se 1 (by rfl) ⟨307397, by rfl⟩ : syracuseStep 409863 = 614795) B614795
theorem B409871 : Blo 409770 409871 := bstep (se 1 (by rfl) ⟨307403, by rfl⟩ : syracuseStep 409871 = 614807) B614807
theorem B1392929 : Blo 409770 1392929 := bstep (se 2 (by rfl) ⟨522348, by rfl⟩ : syracuseStep 1392929 = 1044697) B1044697
theorem B409915 : Blo 409770 409915 := bstep (se 1 (by rfl) ⟨307436, by rfl⟩ : syracuseStep 409915 = 614873) B614873
theorem B5030237 : Blo 409770 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B409991 : Blo 409770 409991 := bstep (se 1 (by rfl) ⟨307493, by rfl⟩ : syracuseStep 409991 = 614987) B614987
theorem B409999 : Blo 409770 409999 := bstep (se 1 (by rfl) ⟨307499, by rfl⟩ : syracuseStep 409999 = 614999) B614999
theorem B410043 : Blo 409770 410043 := bstep (se 1 (by rfl) ⟨307532, by rfl⟩ : syracuseStep 410043 = 615065) B615065
theorem B410119 : Blo 409770 410119 := bstep (se 1 (by rfl) ⟨307589, by rfl⟩ : syracuseStep 410119 = 615179) B615179
theorem B1982987 : Blo 409770 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B410127 : Blo 409770 410127 := bstep (se 1 (by rfl) ⟨307595, by rfl⟩ : syracuseStep 410127 = 615191) B615191
theorem B410171 : Blo 409770 410171 := bstep (se 1 (by rfl) ⟨307628, by rfl⟩ : syracuseStep 410171 = 615257) B615257
theorem B1557053 : Blo 409770 1557053 := bstep (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) B583895
theorem B3949175 : Blo 409770 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B410247 : Blo 409770 410247 := bstep (se 1 (by rfl) ⟨307685, by rfl⟩ : syracuseStep 410247 = 615371) B615371
theorem B410255 : Blo 409770 410255 := bstep (se 1 (by rfl) ⟨307691, by rfl⟩ : syracuseStep 410255 = 615383) B615383
theorem B410299 : Blo 409770 410299 := bstep (se 1 (by rfl) ⟨307724, by rfl⟩ : syracuseStep 410299 = 615449) B615449
theorem B2081537 : Blo 409770 2081537 := bstep (se 2 (by rfl) ⟨780576, by rfl⟩ : syracuseStep 2081537 = 1561153) B1561153
theorem B410375 : Blo 409770 410375 := bstep (se 1 (by rfl) ⟨307781, by rfl⟩ : syracuseStep 410375 = 615563) B615563
theorem B410383 : Blo 409770 410383 := bstep (se 1 (by rfl) ⟨307787, by rfl⟩ : syracuseStep 410383 = 615575) B615575
theorem B410427 : Blo 409770 410427 := bstep (se 1 (by rfl) ⟨307820, by rfl⟩ : syracuseStep 410427 = 615641) B615641
theorem B1393523 : Blo 409770 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B410503 : Blo 409770 410503 := bstep (se 1 (by rfl) ⟨307877, by rfl⟩ : syracuseStep 410503 = 615755) B615755
theorem B410511 : Blo 409770 410511 := bstep (se 1 (by rfl) ⟨307883, by rfl⟩ : syracuseStep 410511 = 615767) B615767
theorem B410555 : Blo 409770 410555 := bstep (se 1 (by rfl) ⟨307916, by rfl⟩ : syracuseStep 410555 = 615833) B615833
theorem B410631 : Blo 409770 410631 := bstep (se 1 (by rfl) ⟨307973, by rfl⟩ : syracuseStep 410631 = 615947) B615947
theorem B410639 : Blo 409770 410639 := bstep (se 1 (by rfl) ⟨307979, by rfl⟩ : syracuseStep 410639 = 615959) B615959
theorem B410683 : Blo 409770 410683 := bstep (se 1 (by rfl) ⟨308012, by rfl⟩ : syracuseStep 410683 = 616025) B616025
theorem B410759 : Blo 409770 410759 := bstep (se 1 (by rfl) ⟨308069, by rfl⟩ : syracuseStep 410759 = 616139) B616139
theorem B410767 : Blo 409770 410767 := bstep (se 1 (by rfl) ⟨308075, by rfl⟩ : syracuseStep 410767 = 616151) B616151
theorem B2376877 : Blo 409770 2376877 := bstep (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) B891329
theorem B410811 : Blo 409770 410811 := bstep (se 1 (by rfl) ⟨308108, by rfl⟩ : syracuseStep 410811 = 616217) B616217
theorem B1754369 : Blo 409770 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B410887 : Blo 409770 410887 := bstep (se 1 (by rfl) ⟨308165, by rfl⟩ : syracuseStep 410887 = 616331) B616331
theorem B410895 : Blo 409770 410895 := bstep (se 1 (by rfl) ⟨308171, by rfl⟩ : syracuseStep 410895 = 616343) B616343
theorem B410939 : Blo 409770 410939 := bstep (se 1 (by rfl) ⟨308204, by rfl⟩ : syracuseStep 410939 = 616409) B616409
theorem B411015 : Blo 409770 411015 := bstep (se 1 (by rfl) ⟨308261, by rfl⟩ : syracuseStep 411015 = 616523) B616523
theorem B411023 : Blo 409770 411023 := bstep (se 1 (by rfl) ⟨308267, by rfl⟩ : syracuseStep 411023 = 616535) B616535
theorem B411067 : Blo 409770 411067 := bstep (se 1 (by rfl) ⟨308300, by rfl⟩ : syracuseStep 411067 = 616601) B616601
theorem B411143 : Blo 409770 411143 := bstep (se 1 (by rfl) ⟨308357, by rfl⟩ : syracuseStep 411143 = 616715) B616715
theorem B411151 : Blo 409770 411151 := bstep (se 1 (by rfl) ⟨308363, by rfl⟩ : syracuseStep 411151 = 616727) B616727
theorem B2082347 : Blo 409770 2082347 := bstep (se 1 (by rfl) ⟨1561760, by rfl⟩ : syracuseStep 2082347 = 3123521) B3123521
theorem B411195 : Blo 409770 411195 := bstep (se 1 (by rfl) ⟨308396, by rfl⟩ : syracuseStep 411195 = 616793) B616793
theorem B411271 : Blo 409770 411271 := bstep (se 1 (by rfl) ⟨308453, by rfl⟩ : syracuseStep 411271 = 616907) B616907
theorem B411279 : Blo 409770 411279 := bstep (se 1 (by rfl) ⟨308459, by rfl⟩ : syracuseStep 411279 = 616919) B616919
theorem B6670001 : Blo 409770 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B411323 : Blo 409770 411323 := bstep (se 1 (by rfl) ⟨308492, by rfl⟩ : syracuseStep 411323 = 616985) B616985
theorem B411399 : Blo 409770 411399 := bstep (se 1 (by rfl) ⟨308549, by rfl⟩ : syracuseStep 411399 = 617099) B617099
theorem B411407 : Blo 409770 411407 := bstep (se 1 (by rfl) ⟨308555, by rfl⟩ : syracuseStep 411407 = 617111) B617111
theorem B411451 : Blo 409770 411451 := bstep (se 1 (by rfl) ⟨308588, by rfl⟩ : syracuseStep 411451 = 617177) B617177
theorem B411527 : Blo 409770 411527 := bstep (se 1 (by rfl) ⟨308645, by rfl⟩ : syracuseStep 411527 = 617291) B617291
theorem B411535 : Blo 409770 411535 := bstep (se 1 (by rfl) ⟨308651, by rfl⟩ : syracuseStep 411535 = 617303) B617303
theorem B411579 : Blo 409770 411579 := bstep (se 1 (by rfl) ⟨308684, by rfl⟩ : syracuseStep 411579 = 617369) B617369
theorem B411655 : Blo 409770 411655 := bstep (se 1 (by rfl) ⟨308741, by rfl⟩ : syracuseStep 411655 = 617483) B617483
theorem B411663 : Blo 409770 411663 := bstep (se 1 (by rfl) ⟨308747, by rfl⟩ : syracuseStep 411663 = 617495) B617495
theorem B411707 : Blo 409770 411707 := bstep (se 1 (by rfl) ⟨308780, by rfl⟩ : syracuseStep 411707 = 617561) B617561
theorem B411783 : Blo 409770 411783 := bstep (se 1 (by rfl) ⟨308837, by rfl⟩ : syracuseStep 411783 = 617675) B617675
theorem B411791 : Blo 409770 411791 := bstep (se 1 (by rfl) ⟨308843, by rfl⟩ : syracuseStep 411791 = 617687) B617687
theorem B411835 : Blo 409770 411835 := bstep (se 1 (by rfl) ⟨308876, by rfl⟩ : syracuseStep 411835 = 617753) B617753
theorem B411911 : Blo 409770 411911 := bstep (se 1 (by rfl) ⟨308933, by rfl⟩ : syracuseStep 411911 = 617867) B617867
theorem B411919 : Blo 409770 411919 := bstep (se 1 (by rfl) ⟨308939, by rfl⟩ : syracuseStep 411919 = 617879) B617879
theorem B3524897 : Blo 409770 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B411963 : Blo 409770 411963 := bstep (se 1 (by rfl) ⟨308972, by rfl⟩ : syracuseStep 411963 = 617945) B617945
theorem B412039 : Blo 409770 412039 := bstep (se 1 (by rfl) ⟨309029, by rfl⟩ : syracuseStep 412039 = 618059) B618059
theorem B3131783 : Blo 409770 3131783 := bstep (se 1 (by rfl) ⟨2348837, by rfl⟩ : syracuseStep 3131783 = 4697675) B4697675
theorem B412047 : Blo 409770 412047 := bstep (se 1 (by rfl) ⟨309035, by rfl⟩ : syracuseStep 412047 = 618071) B618071
theorem B412091 : Blo 409770 412091 := bstep (se 1 (by rfl) ⟨309068, by rfl⟩ : syracuseStep 412091 = 618137) B618137
theorem B412167 : Blo 409770 412167 := bstep (se 1 (by rfl) ⟨309125, by rfl⟩ : syracuseStep 412167 = 618251) B618251
theorem B412175 : Blo 409770 412175 := bstep (se 1 (by rfl) ⟨309131, by rfl⟩ : syracuseStep 412175 = 618263) B618263
theorem B412219 : Blo 409770 412219 := bstep (se 1 (by rfl) ⟨309164, by rfl⟩ : syracuseStep 412219 = 618329) B618329
theorem B4508227 : Blo 409770 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B412295 : Blo 409770 412295 := bstep (se 1 (by rfl) ⟨309221, by rfl⟩ : syracuseStep 412295 = 618443) B618443
theorem B412303 : Blo 409770 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B412347 : Blo 409770 412347 := bstep (se 1 (by rfl) ⟨309260, by rfl⟩ : syracuseStep 412347 = 618521) B618521
theorem B412423 : Blo 409770 412423 := bstep (se 1 (by rfl) ⟨309317, by rfl⟩ : syracuseStep 412423 = 618635) B618635
theorem B412431 : Blo 409770 412431 := bstep (se 1 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 412431 = 618647) B618647
theorem B5917475 : Blo 409770 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B2083643 : Blo 409770 2083643 := bstep (se 1 (by rfl) ⟨1562732, by rfl⟩ : syracuseStep 2083643 = 3125465) B3125465
theorem B412475 : Blo 409770 412475 := bstep (se 1 (by rfl) ⟨309356, by rfl⟩ : syracuseStep 412475 = 618713) B618713
theorem B412551 : Blo 409770 412551 := bstep (se 1 (by rfl) ⟨309413, by rfl⟩ : syracuseStep 412551 = 618827) B618827
theorem B412559 : Blo 409770 412559 := bstep (se 1 (by rfl) ⟨309419, by rfl⟩ : syracuseStep 412559 = 618839) B618839
theorem B412603 : Blo 409770 412603 := bstep (se 1 (by rfl) ⟨309452, by rfl⟩ : syracuseStep 412603 = 618905) B618905
theorem B2083805 : Blo 409770 2083805 := bstep (se 3 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 2083805 = 781427) B781427
theorem B445447 : Blo 409770 445447 := bstep (se 1 (by rfl) ⟨334085, by rfl⟩ : syracuseStep 445447 = 668171) B668171
theorem B412679 : Blo 409770 412679 := bstep (se 1 (by rfl) ⟨309509, by rfl⟩ : syracuseStep 412679 = 619019) B619019
theorem B412687 : Blo 409770 412687 := bstep (se 1 (by rfl) ⟨309515, by rfl⟩ : syracuseStep 412687 = 619031) B619031
theorem B412731 : Blo 409770 412731 := bstep (se 1 (by rfl) ⟨309548, by rfl⟩ : syracuseStep 412731 = 619097) B619097
theorem B412807 : Blo 409770 412807 := bstep (se 1 (by rfl) ⟨309605, by rfl⟩ : syracuseStep 412807 = 619211) B619211
theorem B412815 : Blo 409770 412815 := bstep (se 1 (by rfl) ⟨309611, by rfl⟩ : syracuseStep 412815 = 619223) B619223
theorem B412859 : Blo 409770 412859 := bstep (se 1 (by rfl) ⟨309644, by rfl⟩ : syracuseStep 412859 = 619289) B619289
theorem B412935 : Blo 409770 412935 := bstep (se 1 (by rfl) ⟨309701, by rfl⟩ : syracuseStep 412935 = 619403) B619403
theorem B412943 : Blo 409770 412943 := bstep (se 1 (by rfl) ⟨309707, by rfl⟩ : syracuseStep 412943 = 619415) B619415
theorem B2084129 : Blo 409770 2084129 := bstep (se 2 (by rfl) ⟨781548, by rfl⟩ : syracuseStep 2084129 = 1563097) B1563097
theorem B412987 : Blo 409770 412987 := bstep (se 1 (by rfl) ⟨309740, by rfl⟩ : syracuseStep 412987 = 619481) B619481
theorem B2116999 : Blo 409770 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B413063 : Blo 409770 413063 := bstep (se 1 (by rfl) ⟨309797, by rfl⟩ : syracuseStep 413063 = 619595) B619595
theorem B413071 : Blo 409770 413071 := bstep (se 1 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 413071 = 619607) B619607
theorem B1396115 : Blo 409770 1396115 := bstep (se 1 (by rfl) ⟨1047086, by rfl⟩ : syracuseStep 1396115 = 2094173) B2094173
theorem B413115 : Blo 409770 413115 := bstep (se 1 (by rfl) ⟨309836, by rfl⟩ : syracuseStep 413115 = 619673) B619673
theorem B413191 : Blo 409770 413191 := bstep (se 1 (by rfl) ⟨309893, by rfl⟩ : syracuseStep 413191 = 619787) B619787
theorem B413199 : Blo 409770 413199 := bstep (se 1 (by rfl) ⟨309899, by rfl⟩ : syracuseStep 413199 = 619799) B619799
theorem B413243 : Blo 409770 413243 := bstep (se 1 (by rfl) ⟨309932, by rfl⟩ : syracuseStep 413243 = 619865) B619865
theorem B413319 : Blo 409770 413319 := bstep (se 1 (by rfl) ⟨309989, by rfl⟩ : syracuseStep 413319 = 619979) B619979
theorem B413327 : Blo 409770 413327 := bstep (se 1 (by rfl) ⟨309995, by rfl⟩ : syracuseStep 413327 = 619991) B619991
theorem B1003193 : Blo 409770 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B413371 : Blo 409770 413371 := bstep (se 1 (by rfl) ⟨310028, by rfl⟩ : syracuseStep 413371 = 620057) B620057
theorem B413447 : Blo 409770 413447 := bstep (se 1 (by rfl) ⟨310085, by rfl⟩ : syracuseStep 413447 = 620171) B620171
theorem B1167119 : Blo 409770 1167119 := bstep (se 1 (by rfl) ⟨875339, by rfl⟩ : syracuseStep 1167119 = 1750679) B1750679
theorem B413455 : Blo 409770 413455 := bstep (se 1 (by rfl) ⟨310091, by rfl⟩ : syracuseStep 413455 = 620183) B620183
theorem B741163 : Blo 409770 741163 := bstep (se 1 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 741163 = 1111745) B1111745
theorem B413499 : Blo 409770 413499 := bstep (se 1 (by rfl) ⟨310124, by rfl⟩ : syracuseStep 413499 = 620249) B620249
theorem B1560455 : Blo 409770 1560455 := bstep (se 1 (by rfl) ⟨1170341, by rfl⟩ : syracuseStep 1560455 = 2340683) B2340683
theorem B413575 : Blo 409770 413575 := bstep (se 1 (by rfl) ⟨310181, by rfl⟩ : syracuseStep 413575 = 620363) B620363
theorem B413583 : Blo 409770 413583 := bstep (se 1 (by rfl) ⟨310187, by rfl⟩ : syracuseStep 413583 = 620375) B620375
theorem B413627 : Blo 409770 413627 := bstep (se 1 (by rfl) ⟨310220, by rfl⟩ : syracuseStep 413627 = 620441) B620441
theorem B413703 : Blo 409770 413703 := bstep (se 1 (by rfl) ⟨310277, by rfl⟩ : syracuseStep 413703 = 620555) B620555
theorem B413711 : Blo 409770 413711 := bstep (se 1 (by rfl) ⟨310283, by rfl⟩ : syracuseStep 413711 = 620567) B620567
theorem B413755 : Blo 409770 413755 := bstep (se 1 (by rfl) ⟨310316, by rfl⟩ : syracuseStep 413755 = 620633) B620633
theorem B4444247 : Blo 409770 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B2085101 : Blo 409770 2085101 := bstep (se 3 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 2085101 = 781913) B781913
theorem B446863 : Blo 409770 446863 := bstep (se 1 (by rfl) ⟨335147, by rfl⟩ : syracuseStep 446863 = 670295) B670295
theorem B2511371 : Blo 409770 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B906103 : Blo 409770 906103 := bstep (se 1 (by rfl) ⟨679577, by rfl⟩ : syracuseStep 906103 = 1359155) B1359155
theorem B2085911 : Blo 409770 2085911 := bstep (se 1 (by rfl) ⟨1564433, by rfl⟩ : syracuseStep 2085911 = 3128867) B3128867
theorem B1168519 : Blo 409770 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B742547 : Blo 409770 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B1037569 : Blo 409770 1037569 := bstep (se 2 (by rfl) ⟨389088, by rfl⟩ : syracuseStep 1037569 = 778177) B778177
theorem B1168793 : Blo 409770 1168793 := bstep (se 2 (by rfl) ⟨438297, by rfl⟩ : syracuseStep 1168793 = 876595) B876595
theorem B2348473 : Blo 409770 2348473 := bstep (se 2 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 2348473 = 1761355) B1761355
theorem B2119121 : Blo 409770 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B1988333 : Blo 409770 1988333 := bstep (se 3 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 1988333 = 745625) B745625
theorem B1038167 : Blo 409770 1038167 := bstep (se 1 (by rfl) ⟨778625, by rfl⟩ : syracuseStep 1038167 = 1557251) B1557251
theorem B743303 : Blo 409770 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B9983897 : Blo 409770 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B1038379 : Blo 409770 1038379 := bstep (se 1 (by rfl) ⟨778784, by rfl⟩ : syracuseStep 1038379 = 1557569) B1557569
theorem B1038521 : Blo 409770 1038521 := bstep (se 2 (by rfl) ⟨389445, by rfl⟩ : syracuseStep 1038521 = 778891) B778891
theorem B4741409 : Blo 409770 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B2120203 : Blo 409770 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B2382365 : Blo 409770 2382365 := bstep (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) B893387
theorem B743995 : Blo 409770 743995 := bstep (se 1 (by rfl) ⟨557996, by rfl⟩ : syracuseStep 743995 = 1115993) B1115993
theorem B3758669 : Blo 409770 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1170035 : Blo 409770 1170035 := bstep (se 1 (by rfl) ⟨877526, by rfl⟩ : syracuseStep 1170035 = 1755053) B1755053
theorem B875279 : Blo 409770 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B2644751 : Blo 409770 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B1039513 : Blo 409770 1039513 := bstep (se 2 (by rfl) ⟨389817, by rfl⟩ : syracuseStep 1039513 = 779635) B779635
theorem B1039675 : Blo 409770 1039675 := bstep (se 1 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 1039675 = 1559513) B1559513
theorem B33840443 : Blo 409770 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B2383289 : Blo 409770 2383289 := bstep (se 2 (by rfl) ⟨893733, by rfl⟩ : syracuseStep 2383289 = 1787467) B1787467
theorem B1039817 : Blo 409770 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B876091 : Blo 409770 876091 := bstep (se 1 (by rfl) ⟨657068, by rfl⟩ : syracuseStep 876091 = 1314137) B1314137
theorem B1040161 : Blo 409770 1040161 := bstep (se 2 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 1040161 = 780121) B780121
theorem B4448051 : Blo 409770 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B2088989 : Blo 409770 2088989 := bstep (se 3 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 2088989 = 783371) B783371
theorem B876577 : Blo 409770 876577 := bstep (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) B657433
theorem B614663 : Blo 409770 614663 := bstep (se 1 (by rfl) ⟨460997, by rfl⟩ : syracuseStep 614663 = 921995) B921995
theorem B778511 : Blo 409770 778511 := bstep (se 1 (by rfl) ⟨583883, by rfl⟩ : syracuseStep 778511 = 1167767) B1167767
theorem B614699 : Blo 409770 614699 := bstep (se 1 (by rfl) ⟨461024, by rfl⟩ : syracuseStep 614699 = 922049) B922049
theorem B614729 : Blo 409770 614729 := bstep (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) B461047
theorem B876919 : Blo 409770 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B1040759 : Blo 409770 1040759 := bstep (se 1 (by rfl) ⟨780569, by rfl⟩ : syracuseStep 1040759 = 1561139) B1561139
theorem B614843 : Blo 409770 614843 := bstep (se 1 (by rfl) ⟨461132, by rfl⟩ : syracuseStep 614843 = 922265) B922265
theorem B614903 : Blo 409770 614903 := bstep (se 1 (by rfl) ⟨461177, by rfl⟩ : syracuseStep 614903 = 922355) B922355
theorem B2089475 : Blo 409770 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B614927 : Blo 409770 614927 := bstep (se 1 (by rfl) ⟨461195, by rfl⟩ : syracuseStep 614927 = 922391) B922391
theorem B614969 : Blo 409770 614969 := bstep (se 2 (by rfl) ⟨230613, by rfl⟩ : syracuseStep 614969 = 461227) B461227
theorem B615047 : Blo 409770 615047 := bstep (se 1 (by rfl) ⟨461285, by rfl⟩ : syracuseStep 615047 = 922571) B922571
theorem B615083 : Blo 409770 615083 := bstep (se 1 (by rfl) ⟨461312, by rfl⟩ : syracuseStep 615083 = 922625) B922625
theorem B615113 : Blo 409770 615113 := bstep (se 2 (by rfl) ⟨230667, by rfl⟩ : syracuseStep 615113 = 461335) B461335
theorem B779051 : Blo 409770 779051 := bstep (se 1 (by rfl) ⟨584288, by rfl⟩ : syracuseStep 779051 = 1168577) B1168577
theorem B615227 : Blo 409770 615227 := bstep (se 1 (by rfl) ⟨461420, by rfl⟩ : syracuseStep 615227 = 922841) B922841
theorem B615287 : Blo 409770 615287 := bstep (se 1 (by rfl) ⟨461465, by rfl⟩ : syracuseStep 615287 = 922931) B922931
theorem B615311 : Blo 409770 615311 := bstep (se 1 (by rfl) ⟨461483, by rfl⟩ : syracuseStep 615311 = 922967) B922967
theorem B615353 : Blo 409770 615353 := bstep (se 2 (by rfl) ⟨230757, by rfl⟩ : syracuseStep 615353 = 461515) B461515
theorem B615431 : Blo 409770 615431 := bstep (se 1 (by rfl) ⟨461573, by rfl⟩ : syracuseStep 615431 = 923147) B923147
theorem B1172495 : Blo 409770 1172495 := bstep (se 1 (by rfl) ⟨879371, by rfl⟩ : syracuseStep 1172495 = 1758743) B1758743
theorem B615467 : Blo 409770 615467 := bstep (se 1 (by rfl) ⟨461600, by rfl⟩ : syracuseStep 615467 = 923201) B923201
theorem B615497 : Blo 409770 615497 := bstep (se 2 (by rfl) ⟨230811, by rfl⟩ : syracuseStep 615497 = 461623) B461623
theorem B11920517 : Blo 409770 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B615611 : Blo 409770 615611 := bstep (se 1 (by rfl) ⟨461708, by rfl⟩ : syracuseStep 615611 = 923417) B923417
theorem B615671 : Blo 409770 615671 := bstep (se 1 (by rfl) ⟨461753, by rfl⟩ : syracuseStep 615671 = 923507) B923507
theorem B615695 : Blo 409770 615695 := bstep (se 1 (by rfl) ⟨461771, by rfl⟩ : syracuseStep 615695 = 923543) B923543
theorem B615737 : Blo 409770 615737 := bstep (se 2 (by rfl) ⟨230901, by rfl⟩ : syracuseStep 615737 = 461803) B461803
theorem B615815 : Blo 409770 615815 := bstep (se 1 (by rfl) ⟨461861, by rfl⟩ : syracuseStep 615815 = 923723) B923723
theorem B615851 : Blo 409770 615851 := bstep (se 1 (by rfl) ⟨461888, by rfl⟩ : syracuseStep 615851 = 923777) B923777
theorem B615881 : Blo 409770 615881 := bstep (se 2 (by rfl) ⟨230955, by rfl⟩ : syracuseStep 615881 = 461911) B461911
theorem B1762859 : Blo 409770 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B615995 : Blo 409770 615995 := bstep (se 1 (by rfl) ⟨461996, by rfl⟩ : syracuseStep 615995 = 923993) B923993
theorem B616055 : Blo 409770 616055 := bstep (se 1 (by rfl) ⟨462041, by rfl⟩ : syracuseStep 616055 = 924083) B924083
theorem B1042055 : Blo 409770 1042055 := bstep (se 1 (by rfl) ⟨781541, by rfl⟩ : syracuseStep 1042055 = 1563083) B1563083
theorem B616079 : Blo 409770 616079 := bstep (se 1 (by rfl) ⟨462059, by rfl⟩ : syracuseStep 616079 = 924119) B924119
theorem B616121 : Blo 409770 616121 := bstep (se 2 (by rfl) ⟨231045, by rfl⟩ : syracuseStep 616121 = 462091) B462091
theorem B1042105 : Blo 409770 1042105 := bstep (se 2 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 1042105 = 781579) B781579
theorem B616199 : Blo 409770 616199 := bstep (se 1 (by rfl) ⟨462149, by rfl⟩ : syracuseStep 616199 = 924299) B924299
theorem B616235 : Blo 409770 616235 := bstep (se 1 (by rfl) ⟨462176, by rfl⟩ : syracuseStep 616235 = 924353) B924353
theorem B616265 : Blo 409770 616265 := bstep (se 2 (by rfl) ⟨231099, by rfl⟩ : syracuseStep 616265 = 462199) B462199
theorem B780167 : Blo 409770 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B616379 : Blo 409770 616379 := bstep (se 1 (by rfl) ⟨462284, by rfl⟩ : syracuseStep 616379 = 924569) B924569
theorem B616439 : Blo 409770 616439 := bstep (se 1 (by rfl) ⟨462329, by rfl⟩ : syracuseStep 616439 = 924659) B924659
theorem B616463 : Blo 409770 616463 := bstep (se 1 (by rfl) ⟨462347, by rfl⟩ : syracuseStep 616463 = 924695) B924695
theorem B616505 : Blo 409770 616505 := bstep (se 2 (by rfl) ⟨231189, by rfl⟩ : syracuseStep 616505 = 462379) B462379
theorem B2091095 : Blo 409770 2091095 := bstep (se 1 (by rfl) ⟨1568321, by rfl⟩ : syracuseStep 2091095 = 3136643) B3136643
theorem B616583 : Blo 409770 616583 := bstep (se 1 (by rfl) ⟨462437, by rfl⟩ : syracuseStep 616583 = 924875) B924875
theorem B616619 : Blo 409770 616619 := bstep (se 1 (by rfl) ⟨462464, by rfl⟩ : syracuseStep 616619 = 924929) B924929
theorem B616649 : Blo 409770 616649 := bstep (se 2 (by rfl) ⟨231243, by rfl⟩ : syracuseStep 616649 = 462487) B462487
theorem B1042703 : Blo 409770 1042703 := bstep (se 1 (by rfl) ⟨782027, by rfl⟩ : syracuseStep 1042703 = 1564055) B1564055
theorem B2222387 : Blo 409770 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B616763 : Blo 409770 616763 := bstep (se 1 (by rfl) ⟨462572, by rfl⟩ : syracuseStep 616763 = 925145) B925145
theorem B616823 : Blo 409770 616823 := bstep (se 1 (by rfl) ⟨462617, by rfl⟩ : syracuseStep 616823 = 925235) B925235
theorem B2222471 : Blo 409770 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B616847 : Blo 409770 616847 := bstep (se 1 (by rfl) ⟨462635, by rfl⟩ : syracuseStep 616847 = 925271) B925271
theorem B780691 : Blo 409770 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B616889 : Blo 409770 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B6449629 : Blo 409770 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B518663 : Blo 409770 518663 := bstep (se 1 (by rfl) ⟨388997, by rfl⟩ : syracuseStep 518663 = 777995) B777995
theorem B616967 : Blo 409770 616967 := bstep (se 1 (by rfl) ⟨462725, by rfl⟩ : syracuseStep 616967 = 925451) B925451
theorem B617003 : Blo 409770 617003 := bstep (se 1 (by rfl) ⟨462752, by rfl⟩ : syracuseStep 617003 = 925505) B925505
theorem B2091581 : Blo 409770 2091581 := bstep (se 3 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 2091581 = 784343) B784343
theorem B617033 : Blo 409770 617033 := bstep (se 2 (by rfl) ⟨231387, by rfl⟩ : syracuseStep 617033 = 462775) B462775
theorem B1174135 : Blo 409770 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B1174169 : Blo 409770 1174169 := bstep (se 2 (by rfl) ⟨440313, by rfl⟩ : syracuseStep 1174169 = 880627) B880627
theorem B617147 : Blo 409770 617147 := bstep (se 1 (by rfl) ⟨462860, by rfl⟩ : syracuseStep 617147 = 925721) B925721
theorem B617207 : Blo 409770 617207 := bstep (se 1 (by rfl) ⟨462905, by rfl⟩ : syracuseStep 617207 = 925811) B925811
theorem B1174283 : Blo 409770 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B617231 : Blo 409770 617231 := bstep (se 1 (by rfl) ⟨462923, by rfl⟩ : syracuseStep 617231 = 925847) B925847
theorem B617273 : Blo 409770 617273 := bstep (se 2 (by rfl) ⟨231477, by rfl⟩ : syracuseStep 617273 = 462955) B462955
theorem B617351 : Blo 409770 617351 := bstep (se 1 (by rfl) ⟨463013, by rfl⟩ : syracuseStep 617351 = 926027) B926027
theorem B617387 : Blo 409770 617387 := bstep (se 1 (by rfl) ⟨463040, by rfl⟩ : syracuseStep 617387 = 926081) B926081
theorem B617417 : Blo 409770 617417 := bstep (se 2 (by rfl) ⟨231531, by rfl⟩ : syracuseStep 617417 = 463063) B463063
theorem B1043401 : Blo 409770 1043401 := bstep (se 2 (by rfl) ⟨391275, by rfl⟩ : syracuseStep 1043401 = 782551) B782551
theorem B2354123 : Blo 409770 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B584761 : Blo 409770 584761 := bstep (se 2 (by rfl) ⟨219285, by rfl⟩ : syracuseStep 584761 = 438571) B438571
theorem B617531 : Blo 409770 617531 := bstep (se 1 (by rfl) ⟨463148, by rfl⟩ : syracuseStep 617531 = 926297) B926297
theorem B1043543 : Blo 409770 1043543 := bstep (se 1 (by rfl) ⟨782657, by rfl⟩ : syracuseStep 1043543 = 1565315) B1565315
theorem B617591 : Blo 409770 617591 := bstep (se 1 (by rfl) ⟨463193, by rfl⟩ : syracuseStep 617591 = 926387) B926387
theorem B519311 : Blo 409770 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B617615 : Blo 409770 617615 := bstep (se 1 (by rfl) ⟨463211, by rfl⟩ : syracuseStep 617615 = 926423) B926423
theorem B617657 : Blo 409770 617657 := bstep (se 2 (by rfl) ⟨231621, by rfl⟩ : syracuseStep 617657 = 463243) B463243
theorem B617735 : Blo 409770 617735 := bstep (se 1 (by rfl) ⟨463301, by rfl⟩ : syracuseStep 617735 = 926603) B926603
theorem B617771 : Blo 409770 617771 := bstep (se 1 (by rfl) ⟨463328, by rfl⟩ : syracuseStep 617771 = 926657) B926657
theorem B617801 : Blo 409770 617801 := bstep (se 2 (by rfl) ⟨231675, by rfl⟩ : syracuseStep 617801 = 463351) B463351
theorem B2354579 : Blo 409770 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B617915 : Blo 409770 617915 := bstep (se 1 (by rfl) ⟨463436, by rfl⟩ : syracuseStep 617915 = 926873) B926873
theorem B617975 : Blo 409770 617975 := bstep (se 1 (by rfl) ⟨463481, by rfl⟩ : syracuseStep 617975 = 926963) B926963
theorem B617999 : Blo 409770 617999 := bstep (se 1 (by rfl) ⟨463499, by rfl⟩ : syracuseStep 617999 = 926999) B926999
theorem B618041 : Blo 409770 618041 := bstep (se 2 (by rfl) ⟨231765, by rfl⟩ : syracuseStep 618041 = 463531) B463531
theorem B781883 : Blo 409770 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B618119 : Blo 409770 618119 := bstep (se 1 (by rfl) ⟨463589, by rfl⟩ : syracuseStep 618119 = 927179) B927179
theorem B618155 : Blo 409770 618155 := bstep (se 1 (by rfl) ⟨463616, by rfl⟩ : syracuseStep 618155 = 927233) B927233
theorem B618185 : Blo 409770 618185 := bstep (se 2 (by rfl) ⟨231819, by rfl⟩ : syracuseStep 618185 = 463639) B463639
theorem B5336833 : Blo 409770 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B618299 : Blo 409770 618299 := bstep (se 1 (by rfl) ⟨463724, by rfl⟩ : syracuseStep 618299 = 927449) B927449
theorem B1175411 : Blo 409770 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B618359 : Blo 409770 618359 := bstep (se 1 (by rfl) ⟨463769, by rfl⟩ : syracuseStep 618359 = 927539) B927539
theorem B618383 : Blo 409770 618383 := bstep (se 1 (by rfl) ⟨463787, by rfl⟩ : syracuseStep 618383 = 927575) B927575
theorem B618425 : Blo 409770 618425 := bstep (se 2 (by rfl) ⟨231909, by rfl⟩ : syracuseStep 618425 = 463819) B463819
theorem B618503 : Blo 409770 618503 := bstep (se 1 (by rfl) ⟨463877, by rfl⟩ : syracuseStep 618503 = 927755) B927755
theorem B782369 : Blo 409770 782369 := bstep (se 2 (by rfl) ⟨293388, by rfl⟩ : syracuseStep 782369 = 586777) B586777
theorem B618539 : Blo 409770 618539 := bstep (se 1 (by rfl) ⟨463904, by rfl⟩ : syracuseStep 618539 = 927809) B927809
theorem B618569 : Blo 409770 618569 := bstep (se 2 (by rfl) ⟨231963, by rfl⟩ : syracuseStep 618569 = 463927) B463927
theorem B618683 : Blo 409770 618683 := bstep (se 1 (by rfl) ⟨464012, by rfl⟩ : syracuseStep 618683 = 928025) B928025
theorem B1765577 : Blo 409770 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B618743 : Blo 409770 618743 := bstep (se 1 (by rfl) ⟨464057, by rfl⟩ : syracuseStep 618743 = 928115) B928115
theorem B1175809 : Blo 409770 1175809 := bstep (se 2 (by rfl) ⟨440928, by rfl⟩ : syracuseStep 1175809 = 881857) B881857
theorem B585991 : Blo 409770 585991 := bstep (se 1 (by rfl) ⟨439493, by rfl⟩ : syracuseStep 585991 = 878987) B878987
theorem B618767 : Blo 409770 618767 := bstep (se 1 (by rfl) ⟨464075, by rfl⟩ : syracuseStep 618767 = 928151) B928151
theorem B4452641 : Blo 409770 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B2224421 : Blo 409770 2224421 := bstep (se 4 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 2224421 = 417079) B417079
theorem B782635 : Blo 409770 782635 := bstep (se 1 (by rfl) ⟨586976, by rfl⟩ : syracuseStep 782635 = 1173953) B1173953
theorem B2093363 : Blo 409770 2093363 := bstep (se 1 (by rfl) ⟨1570022, by rfl⟩ : syracuseStep 2093363 = 3140045) B3140045
theorem B2388275 : Blo 409770 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B618809 : Blo 409770 618809 := bstep (se 2 (by rfl) ⟨232053, by rfl⟩ : syracuseStep 618809 = 464107) B464107
theorem B1175867 : Blo 409770 1175867 := bstep (se 1 (by rfl) ⟨881900, by rfl⟩ : syracuseStep 1175867 = 1763801) B1763801
theorem B1601927 : Blo 409770 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B618887 : Blo 409770 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B2224529 : Blo 409770 2224529 := bstep (se 2 (by rfl) ⟨834198, by rfl⟩ : syracuseStep 2224529 = 1668397) B1668397
theorem B618923 : Blo 409770 618923 := bstep (se 1 (by rfl) ⟨464192, by rfl⟩ : syracuseStep 618923 = 928385) B928385
theorem B618953 : Blo 409770 618953 := bstep (se 2 (by rfl) ⟨232107, by rfl⟩ : syracuseStep 618953 = 464215) B464215
theorem B1569233 : Blo 409770 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B8417753 : Blo 409770 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B619067 : Blo 409770 619067 := bstep (se 1 (by rfl) ⟨464300, by rfl⟩ : syracuseStep 619067 = 928601) B928601
theorem B619127 : Blo 409770 619127 := bstep (se 1 (by rfl) ⟨464345, by rfl⟩ : syracuseStep 619127 = 928691) B928691
theorem B2093687 : Blo 409770 2093687 := bstep (se 1 (by rfl) ⟨1570265, by rfl⟩ : syracuseStep 2093687 = 3140531) B3140531
theorem B619151 : Blo 409770 619151 := bstep (se 1 (by rfl) ⟨464363, by rfl⟩ : syracuseStep 619151 = 928727) B928727
theorem B619193 : Blo 409770 619193 := bstep (se 2 (by rfl) ⟨232197, by rfl⟩ : syracuseStep 619193 = 464395) B464395
theorem B619271 : Blo 409770 619271 := bstep (se 1 (by rfl) ⟨464453, by rfl⟩ : syracuseStep 619271 = 928907) B928907
theorem B619307 : Blo 409770 619307 := bstep (se 1 (by rfl) ⟨464480, by rfl⟩ : syracuseStep 619307 = 928961) B928961
theorem B619337 : Blo 409770 619337 := bstep (se 2 (by rfl) ⟨232251, by rfl⟩ : syracuseStep 619337 = 464503) B464503
theorem B1569689 : Blo 409770 1569689 := bstep (se 2 (by rfl) ⟨588633, by rfl⟩ : syracuseStep 1569689 = 1177267) B1177267
theorem B619451 : Blo 409770 619451 := bstep (se 1 (by rfl) ⟨464588, by rfl⟩ : syracuseStep 619451 = 929177) B929177
theorem B619511 : Blo 409770 619511 := bstep (se 1 (by rfl) ⟨464633, by rfl⟩ : syracuseStep 619511 = 929267) B929267
theorem B619535 : Blo 409770 619535 := bstep (se 1 (by rfl) ⟨464651, by rfl⟩ : syracuseStep 619535 = 929303) B929303
theorem B619577 : Blo 409770 619577 := bstep (se 2 (by rfl) ⟨232341, by rfl⟩ : syracuseStep 619577 = 464683) B464683
theorem B586811 : Blo 409770 586811 := bstep (se 1 (by rfl) ⟨440108, by rfl⟩ : syracuseStep 586811 = 880217) B880217
theorem B1045619 : Blo 409770 1045619 := bstep (se 1 (by rfl) ⟨784214, by rfl⟩ : syracuseStep 1045619 = 1568429) B1568429
theorem B619655 : Blo 409770 619655 := bstep (se 1 (by rfl) ⟨464741, by rfl⟩ : syracuseStep 619655 = 929483) B929483
theorem B619691 : Blo 409770 619691 := bstep (se 1 (by rfl) ⟨464768, by rfl⟩ : syracuseStep 619691 = 929537) B929537
theorem B619721 : Blo 409770 619721 := bstep (se 2 (by rfl) ⟨232395, by rfl⟩ : syracuseStep 619721 = 464791) B464791
theorem B619835 : Blo 409770 619835 := bstep (se 1 (by rfl) ⟨464876, by rfl⟩ : syracuseStep 619835 = 929753) B929753
theorem B619895 : Blo 409770 619895 := bstep (se 1 (by rfl) ⟨464921, by rfl⟩ : syracuseStep 619895 = 929843) B929843
theorem B783751 : Blo 409770 783751 := bstep (se 1 (by rfl) ⟨587813, by rfl⟩ : syracuseStep 783751 = 1175627) B1175627
theorem B619919 : Blo 409770 619919 := bstep (se 1 (by rfl) ⟨464939, by rfl⟩ : syracuseStep 619919 = 929879) B929879
theorem B619961 : Blo 409770 619961 := bstep (se 2 (by rfl) ⟨232485, by rfl⟩ : syracuseStep 619961 = 464971) B464971
theorem B587255 : Blo 409770 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B6780419 : Blo 409770 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B620039 : Blo 409770 620039 := bstep (se 1 (by rfl) ⟨465029, by rfl⟩ : syracuseStep 620039 = 930059) B930059
theorem B620075 : Blo 409770 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B2094659 : Blo 409770 2094659 := bstep (se 1 (by rfl) ⟨1570994, by rfl⟩ : syracuseStep 2094659 = 3141989) B3141989
theorem B620105 : Blo 409770 620105 := bstep (se 2 (by rfl) ⟨232539, by rfl⟩ : syracuseStep 620105 = 465079) B465079
theorem B1046135 : Blo 409770 1046135 := bstep (se 1 (by rfl) ⟨784601, by rfl⟩ : syracuseStep 1046135 = 1569203) B1569203
theorem B587449 : Blo 409770 587449 := bstep (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) B440587
theorem B620219 : Blo 409770 620219 := bstep (se 1 (by rfl) ⟨465164, by rfl⟩ : syracuseStep 620219 = 930329) B930329
theorem B620279 : Blo 409770 620279 := bstep (se 1 (by rfl) ⟨465209, by rfl⟩ : syracuseStep 620279 = 930419) B930419
theorem B620303 : Blo 409770 620303 := bstep (se 1 (by rfl) ⟨465227, by rfl⟩ : syracuseStep 620303 = 930455) B930455
theorem B620345 : Blo 409770 620345 := bstep (se 2 (by rfl) ⟨232629, by rfl⟩ : syracuseStep 620345 = 465259) B465259
theorem B620423 : Blo 409770 620423 := bstep (se 1 (by rfl) ⟨465317, by rfl⟩ : syracuseStep 620423 = 930635) B930635
theorem B620459 : Blo 409770 620459 := bstep (se 1 (by rfl) ⟨465344, by rfl⟩ : syracuseStep 620459 = 930689) B930689
theorem B784313 : Blo 409770 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B620489 : Blo 409770 620489 := bstep (se 2 (by rfl) ⟨232683, by rfl⟩ : syracuseStep 620489 = 465367) B465367
theorem B2979787 : Blo 409770 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B522283 : Blo 409770 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B1570859 : Blo 409770 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B620603 : Blo 409770 620603 := bstep (se 1 (by rfl) ⟨465452, by rfl⟩ : syracuseStep 620603 = 930905) B930905
theorem B1178155 : Blo 409770 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B1047127 : Blo 409770 1047127 := bstep (se 1 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 1047127 = 1570691) B1570691
theorem B424711 : Blo 409770 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B1670003 : Blo 409770 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B523255 : Blo 409770 523255 := bstep (se 1 (by rfl) ⟨392441, by rfl⟩ : syracuseStep 523255 = 784883) B784883
theorem B785467 : Blo 409770 785467 := bstep (se 1 (by rfl) ⟨589100, by rfl⟩ : syracuseStep 785467 = 1178201) B1178201
theorem B18513197 : Blo 409770 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B523579 : Blo 409770 523579 := bstep (se 1 (by rfl) ⟨392684, by rfl⟩ : syracuseStep 523579 = 785369) B785369
theorem B1114003 : Blo 409770 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B4751257 : Blo 409770 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B3113801 : Blo 409770 3113801 := bstep (se 2 (by rfl) ⟨1167675, by rfl⟩ : syracuseStep 3113801 = 2335351) B2335351
theorem B1115063 : Blo 409770 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B4752901 : Blo 409770 4752901 := bstep (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) B891169
theorem B15075233 : Blo 409770 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B1313111 : Blo 409770 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B2821139 : Blo 409770 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B461947 : Blo 409770 461947 := bstep (se 1 (by rfl) ⟨346460, by rfl⟩ : syracuseStep 461947 = 692921) B692921
theorem B462415 : Blo 409770 462415 := bstep (se 1 (by rfl) ⟨346811, by rfl⟩ : syracuseStep 462415 = 693623) B693623
theorem B1412747 : Blo 409770 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B1969879 : Blo 409770 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B986987 : Blo 409770 986987 := bstep (se 1 (by rfl) ⟨740240, by rfl⟩ : syracuseStep 986987 = 1480481) B1480481
theorem B692111 : Blo 409770 692111 := bstep (se 1 (by rfl) ⟨519083, by rfl⟩ : syracuseStep 692111 = 1038167) B1038167
theorem B6655931 : Blo 409770 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B462811 : Blo 409770 462811 := bstep (se 1 (by rfl) ⟨347108, by rfl⟩ : syracuseStep 462811 = 694217) B694217
theorem B593929 : Blo 409770 593929 := bstep (se 2 (by rfl) ⟨222723, by rfl⟩ : syracuseStep 593929 = 445447) B445447
theorem B692347 : Blo 409770 692347 := bstep (se 1 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 692347 = 1038521) B1038521
theorem B1675417 : Blo 409770 1675417 := bstep (se 2 (by rfl) ⟨628281, by rfl⟩ : syracuseStep 1675417 = 1256563) B1256563
theorem B463279 : Blo 409770 463279 := bstep (se 1 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 463279 = 694919) B694919
theorem B922121 : Blo 409770 922121 := bstep (se 2 (by rfl) ⟨345795, by rfl⟩ : syracuseStep 922121 = 691591) B691591
theorem B660047 : Blo 409770 660047 := bstep (se 1 (by rfl) ⟨495035, by rfl⟩ : syracuseStep 660047 = 990071) B990071
theorem B922463 : Blo 409770 922463 := bstep (se 1 (by rfl) ⟨691847, by rfl⟩ : syracuseStep 922463 = 1383695) B1383695
theorem B463711 : Blo 409770 463711 := bstep (se 1 (by rfl) ⟨347783, by rfl⟩ : syracuseStep 463711 = 695567) B695567
theorem B2626451 : Blo 409770 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B4330415 : Blo 409770 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B693211 : Blo 409770 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B7115777 : Blo 409770 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B922643 : Blo 409770 922643 := bstep (se 1 (by rfl) ⟨691982, by rfl⟩ : syracuseStep 922643 = 1383965) B1383965
theorem B988217 : Blo 409770 988217 := bstep (se 2 (by rfl) ⟨370581, by rfl⟩ : syracuseStep 988217 = 741163) B741163
theorem B464071 : Blo 409770 464071 := bstep (se 1 (by rfl) ⟨348053, by rfl⟩ : syracuseStep 464071 = 696107) B696107
theorem B660727 : Blo 409770 660727 := bstep (se 1 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 660727 = 991091) B991091
theorem B922985 : Blo 409770 922985 := bstep (se 2 (by rfl) ⟨346119, by rfl⟩ : syracuseStep 922985 = 692239) B692239
theorem B1316225 : Blo 409770 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B693839 : Blo 409770 693839 := bstep (se 1 (by rfl) ⟨520379, by rfl⟩ : syracuseStep 693839 = 1040759) B1040759
theorem B792275 : Blo 409770 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B595817 : Blo 409770 595817 := bstep (se 2 (by rfl) ⟨223431, by rfl⟩ : syracuseStep 595817 = 446863) B446863
theorem B661355 : Blo 409770 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B923579 : Blo 409770 923579 := bstep (se 1 (by rfl) ⟨692684, by rfl⟩ : syracuseStep 923579 = 1385369) B1385369
theorem B464935 : Blo 409770 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B923705 : Blo 409770 923705 := bstep (se 2 (by rfl) ⟨346389, by rfl⟩ : syracuseStep 923705 = 692779) B692779
theorem B2234753 : Blo 409770 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B924047 : Blo 409770 924047 := bstep (se 1 (by rfl) ⟨693035, by rfl⟩ : syracuseStep 924047 = 1386071) B1386071
theorem B694703 : Blo 409770 694703 := bstep (se 1 (by rfl) ⟨521027, by rfl⟩ : syracuseStep 694703 = 1042055) B1042055
theorem B1383047 : Blo 409770 1383047 := bstep (se 1 (by rfl) ⟨1037285, by rfl⟩ : syracuseStep 1383047 = 2074571) B2074571
theorem B1383101 : Blo 409770 1383101 := bstep (se 3 (by rfl) ⟨259331, by rfl⟩ : syracuseStep 1383101 = 518663) B518663
theorem B924371 : Blo 409770 924371 := bstep (se 1 (by rfl) ⟨693278, by rfl⟩ : syracuseStep 924371 = 1386557) B1386557
theorem B1383263 : Blo 409770 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B695135 : Blo 409770 695135 := bstep (se 1 (by rfl) ⟨521351, by rfl⟩ : syracuseStep 695135 = 1042703) B1042703
theorem B1481591 : Blo 409770 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1481647 : Blo 409770 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B1383425 : Blo 409770 1383425 := bstep (se 2 (by rfl) ⟨518784, by rfl⟩ : syracuseStep 1383425 = 1037569) B1037569
theorem B2432051 : Blo 409770 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B793847 : Blo 409770 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B3513689 : Blo 409770 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B3743119 : Blo 409770 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B695695 : Blo 409770 695695 := bstep (se 1 (by rfl) ⟨521771, by rfl⟩ : syracuseStep 695695 = 1043543) B1043543
theorem B5283245 : Blo 409770 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B925307 : Blo 409770 925307 := bstep (se 1 (by rfl) ⟨693980, by rfl⟩ : syracuseStep 925307 = 1387961) B1387961
theorem B7020269 : Blo 409770 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B925433 : Blo 409770 925433 := bstep (se 2 (by rfl) ⟨347037, by rfl⟩ : syracuseStep 925433 = 694075) B694075
theorem B1384235 : Blo 409770 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B1318751 : Blo 409770 1318751 := bstep (se 1 (by rfl) ⟨989063, by rfl⟩ : syracuseStep 1318751 = 1978127) B1978127
theorem B1253303 : Blo 409770 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B3973049 : Blo 409770 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B925703 : Blo 409770 925703 := bstep (se 1 (by rfl) ⟨694277, by rfl⟩ : syracuseStep 925703 = 1388555) B1388555
theorem B1384505 : Blo 409770 1384505 := bstep (se 2 (by rfl) ⟨519189, by rfl⟩ : syracuseStep 1384505 = 1038379) B1038379
theorem B696377 : Blo 409770 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B925775 : Blo 409770 925775 := bstep (se 1 (by rfl) ⟨694331, by rfl⟩ : syracuseStep 925775 = 1388663) B1388663
theorem B1482947 : Blo 409770 1482947 := bstep (se 1 (by rfl) ⟨1112210, by rfl⟩ : syracuseStep 1482947 = 2224421) B2224421
theorem B1483019 : Blo 409770 1483019 := bstep (se 1 (by rfl) ⟨1112264, by rfl⟩ : syracuseStep 1483019 = 2224529) B2224529
theorem B5611835 : Blo 409770 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B1384829 : Blo 409770 1384829 := bstep (se 3 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 1384829 = 519311) B519311
theorem B926171 : Blo 409770 926171 := bstep (se 1 (by rfl) ⟨694628, by rfl⟩ : syracuseStep 926171 = 1389257) B1389257
theorem B2105837 : Blo 409770 2105837 := bstep (se 3 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 2105837 = 789689) B789689
theorem B1385099 : Blo 409770 1385099 := bstep (se 1 (by rfl) ⟨1038824, by rfl⟩ : syracuseStep 1385099 = 2077649) B2077649
theorem B2826937 : Blo 409770 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B1188551 : Blo 409770 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B697079 : Blo 409770 697079 := bstep (se 1 (by rfl) ⟨522809, by rfl⟩ : syracuseStep 697079 = 1045619) B1045619
theorem B991993 : Blo 409770 991993 := bstep (se 2 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 991993 = 743995) B743995
theorem B926639 : Blo 409770 926639 := bstep (se 1 (by rfl) ⟨694979, by rfl⟩ : syracuseStep 926639 = 1389959) B1389959
theorem B1451009 : Blo 409770 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B992263 : Blo 409770 992263 := bstep (se 1 (by rfl) ⟨744197, by rfl⟩ : syracuseStep 992263 = 1488395) B1488395
theorem B566281 : Blo 409770 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B697423 : Blo 409770 697423 := bstep (se 1 (by rfl) ⟨523067, by rfl⟩ : syracuseStep 697423 = 1046135) B1046135
theorem B926891 : Blo 409770 926891 := bstep (se 1 (by rfl) ⟨695168, by rfl⟩ : syracuseStep 926891 = 1390337) B1390337
theorem B697673 : Blo 409770 697673 := bstep (se 2 (by rfl) ⟨261627, by rfl⟩ : syracuseStep 697673 = 523255) B523255
theorem B1386017 : Blo 409770 1386017 := bstep (se 2 (by rfl) ⟨519756, by rfl⟩ : syracuseStep 1386017 = 1039513) B1039513
theorem B927431 : Blo 409770 927431 := bstep (se 1 (by rfl) ⟨695573, by rfl⟩ : syracuseStep 927431 = 1391147) B1391147
theorem B1386233 : Blo 409770 1386233 := bstep (se 2 (by rfl) ⟨519837, by rfl⟩ : syracuseStep 1386233 = 1039675) B1039675
theorem B698105 : Blo 409770 698105 := bstep (se 2 (by rfl) ⟨261789, by rfl⟩ : syracuseStep 698105 = 523579) B523579
theorem B1976183 : Blo 409770 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B1386503 : Blo 409770 1386503 := bstep (se 1 (by rfl) ⟨1039877, by rfl⟩ : syracuseStep 1386503 = 2079755) B2079755
theorem B5941349 : Blo 409770 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B1386611 : Blo 409770 1386611 := bstep (se 1 (by rfl) ⟨1039958, by rfl⟩ : syracuseStep 1386611 = 2079917) B2079917
theorem B2369803 : Blo 409770 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B1386881 : Blo 409770 1386881 := bstep (se 2 (by rfl) ⟨520080, by rfl⟩ : syracuseStep 1386881 = 1040161) B1040161
theorem B6335009 : Blo 409770 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B928295 : Blo 409770 928295 := bstep (se 1 (by rfl) ⟨696221, by rfl⟩ : syracuseStep 928295 = 1392443) B1392443
theorem B928619 : Blo 409770 928619 := bstep (se 1 (by rfl) ⟨696464, by rfl⟩ : syracuseStep 928619 = 1392929) B1392929
theorem B3353491 : Blo 409770 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B928673 : Blo 409770 928673 := bstep (se 2 (by rfl) ⟨348252, by rfl⟩ : syracuseStep 928673 = 696505) B696505
theorem B1321991 : Blo 409770 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B2632783 : Blo 409770 2632783 := bstep (se 1 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 2632783 = 3949175) B3949175
theorem B1387691 : Blo 409770 1387691 := bstep (se 1 (by rfl) ⟨1040768, by rfl⟩ : syracuseStep 1387691 = 2081537) B2081537
theorem B929015 : Blo 409770 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B2076029 : Blo 409770 2076029 := bstep (se 3 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 2076029 = 778511) B778511
theorem B2338267 : Blo 409770 2338267 := bstep (se 1 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 2338267 = 3507401) B3507401
theorem B1388231 : Blo 409770 1388231 := bstep (se 1 (by rfl) ⟨1041173, by rfl⟩ : syracuseStep 1388231 = 2082347) B2082347
theorem B929609 : Blo 409770 929609 := bstep (se 2 (by rfl) ⟨348603, by rfl⟩ : syracuseStep 929609 = 697207) B697207
theorem B634807 : Blo 409770 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B6696989 : Blo 409770 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B3944983 : Blo 409770 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B1389095 : Blo 409770 1389095 := bstep (se 1 (by rfl) ⟨1041821, by rfl⟩ : syracuseStep 1389095 = 2083643) B2083643
theorem B930401 : Blo 409770 930401 := bstep (se 2 (by rfl) ⟨348900, by rfl⟩ : syracuseStep 930401 = 697801) B697801
theorem B832123 : Blo 409770 832123 := bstep (se 1 (by rfl) ⟨624092, by rfl⟩ : syracuseStep 832123 = 1248185) B1248185
theorem B1389203 : Blo 409770 1389203 := bstep (se 1 (by rfl) ⟨1041902, by rfl⟩ : syracuseStep 1389203 = 2083805) B2083805
theorem B10138385 : Blo 409770 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B1389419 : Blo 409770 1389419 := bstep (se 1 (by rfl) ⟨1042064, by rfl⟩ : syracuseStep 1389419 = 2084129) B2084129
theorem B1389473 : Blo 409770 1389473 := bstep (se 2 (by rfl) ⟨521052, by rfl⟩ : syracuseStep 1389473 = 1042105) B1042105
theorem B930743 : Blo 409770 930743 := bstep (se 1 (by rfl) ⟨698057, by rfl⟩ : syracuseStep 930743 = 1396115) B1396115
theorem B668795 : Blo 409770 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B2962831 : Blo 409770 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B1390067 : Blo 409770 1390067 := bstep (se 1 (by rfl) ⟨1042550, by rfl⟩ : syracuseStep 1390067 = 2085101) B2085101
theorem B3126923 : Blo 409770 3126923 := bstep (se 1 (by rfl) ⟨2345192, by rfl⟩ : syracuseStep 3126923 = 4690385) B4690385
theorem B1357511 : Blo 409770 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B1980125 : Blo 409770 1980125 := bstep (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) B742547
theorem B8599505 : Blo 409770 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B1390607 : Blo 409770 1390607 := bstep (se 1 (by rfl) ⟨1042955, by rfl⟩ : syracuseStep 1390607 = 2085911) B2085911
theorem B6010969 : Blo 409770 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B1325555 : Blo 409770 1325555 := bstep (se 1 (by rfl) ⟨994166, by rfl⟩ : syracuseStep 1325555 = 1988333) B1988333
theorem B1391201 : Blo 409770 1391201 := bstep (se 2 (by rfl) ⟨521700, by rfl⟩ : syracuseStep 1391201 = 1043401) B1043401
theorem B6666887 : Blo 409770 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B2407241 : Blo 409770 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B3160939 : Blo 409770 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B1588243 : Blo 409770 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B2505779 : Blo 409770 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1490167 : Blo 409770 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B22560295 : Blo 409770 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B1490471 : Blo 409770 1490471 := bstep (se 1 (by rfl) ⟨1117853, by rfl⟩ : syracuseStep 1490471 = 2235707) B2235707
theorem B835195 : Blo 409770 835195 := bstep (se 1 (by rfl) ⟨626396, by rfl⟩ : syracuseStep 835195 = 1252793) B1252793
theorem B1588859 : Blo 409770 1588859 := bstep (se 1 (by rfl) ⟨1191644, by rfl⟩ : syracuseStep 1588859 = 2383289) B2383289
theorem B2080403 : Blo 409770 2080403 := bstep (se 1 (by rfl) ⟨1560302, by rfl⟩ : syracuseStep 2080403 = 3120605) B3120605
theorem B1982141 : Blo 409770 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B2965367 : Blo 409770 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B1392659 : Blo 409770 1392659 := bstep (se 1 (by rfl) ⟨1044494, by rfl⟩ : syracuseStep 1392659 = 2088989) B2088989
theorem B409775 : Blo 409770 409775 := bstep (se 1 (by rfl) ⟨307331, by rfl⟩ : syracuseStep 409775 = 614663) B614663
theorem B409799 : Blo 409770 409799 := bstep (se 1 (by rfl) ⟨307349, by rfl⟩ : syracuseStep 409799 = 614699) B614699
theorem B835795 : Blo 409770 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B409819 : Blo 409770 409819 := bstep (se 1 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 409819 = 614729) B614729
theorem B409895 : Blo 409770 409895 := bstep (se 1 (by rfl) ⟨307421, by rfl⟩ : syracuseStep 409895 = 614843) B614843
theorem B409935 : Blo 409770 409935 := bstep (se 1 (by rfl) ⟨307451, by rfl⟩ : syracuseStep 409935 = 614903) B614903
theorem B1392983 : Blo 409770 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B409951 : Blo 409770 409951 := bstep (se 1 (by rfl) ⟨307463, by rfl⟩ : syracuseStep 409951 = 614927) B614927
theorem B409979 : Blo 409770 409979 := bstep (se 1 (by rfl) ⟨307484, by rfl⟩ : syracuseStep 409979 = 614969) B614969
theorem B410031 : Blo 409770 410031 := bstep (se 1 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 410031 = 615047) B615047
theorem B410055 : Blo 409770 410055 := bstep (se 1 (by rfl) ⟨307541, by rfl⟩ : syracuseStep 410055 = 615083) B615083
theorem B410075 : Blo 409770 410075 := bstep (se 1 (by rfl) ⟨307556, by rfl⟩ : syracuseStep 410075 = 615113) B615113
theorem B410151 : Blo 409770 410151 := bstep (se 1 (by rfl) ⟨307613, by rfl⟩ : syracuseStep 410151 = 615227) B615227
theorem B410191 : Blo 409770 410191 := bstep (se 1 (by rfl) ⟨307643, by rfl⟩ : syracuseStep 410191 = 615287) B615287
theorem B410207 : Blo 409770 410207 := bstep (se 1 (by rfl) ⟨307655, by rfl⟩ : syracuseStep 410207 = 615311) B615311
theorem B410235 : Blo 409770 410235 := bstep (se 1 (by rfl) ⟨307676, by rfl⟩ : syracuseStep 410235 = 615353) B615353
theorem B410287 : Blo 409770 410287 := bstep (se 1 (by rfl) ⟨307715, by rfl⟩ : syracuseStep 410287 = 615431) B615431
theorem B410311 : Blo 409770 410311 := bstep (se 1 (by rfl) ⟨307733, by rfl⟩ : syracuseStep 410311 = 615467) B615467
theorem B410331 : Blo 409770 410331 := bstep (se 1 (by rfl) ⟨307748, by rfl⟩ : syracuseStep 410331 = 615497) B615497
theorem B7947011 : Blo 409770 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B410407 : Blo 409770 410407 := bstep (se 1 (by rfl) ⟨307805, by rfl⟩ : syracuseStep 410407 = 615611) B615611
theorem B410447 : Blo 409770 410447 := bstep (se 1 (by rfl) ⟨307835, by rfl⟩ : syracuseStep 410447 = 615671) B615671
theorem B410463 : Blo 409770 410463 := bstep (se 1 (by rfl) ⟨307847, by rfl⟩ : syracuseStep 410463 = 615695) B615695
theorem B410491 : Blo 409770 410491 := bstep (se 1 (by rfl) ⟨307868, by rfl⟩ : syracuseStep 410491 = 615737) B615737
theorem B410543 : Blo 409770 410543 := bstep (se 1 (by rfl) ⟨307907, by rfl⟩ : syracuseStep 410543 = 615815) B615815
theorem B410567 : Blo 409770 410567 := bstep (se 1 (by rfl) ⟨307925, by rfl⟩ : syracuseStep 410567 = 615851) B615851
theorem B410587 : Blo 409770 410587 := bstep (se 1 (by rfl) ⟨307940, by rfl⟩ : syracuseStep 410587 = 615881) B615881
theorem B410663 : Blo 409770 410663 := bstep (se 1 (by rfl) ⟨307997, by rfl⟩ : syracuseStep 410663 = 615995) B615995
theorem B410703 : Blo 409770 410703 := bstep (se 1 (by rfl) ⟨308027, by rfl⟩ : syracuseStep 410703 = 616055) B616055
theorem B410719 : Blo 409770 410719 := bstep (se 1 (by rfl) ⟨308039, by rfl⟩ : syracuseStep 410719 = 616079) B616079
theorem B410747 : Blo 409770 410747 := bstep (se 1 (by rfl) ⟨308060, by rfl⟩ : syracuseStep 410747 = 616121) B616121
theorem B410799 : Blo 409770 410799 := bstep (se 1 (by rfl) ⟨308099, by rfl⟩ : syracuseStep 410799 = 616199) B616199
theorem B410823 : Blo 409770 410823 := bstep (se 1 (by rfl) ⟨308117, by rfl⟩ : syracuseStep 410823 = 616235) B616235
theorem B410843 : Blo 409770 410843 := bstep (se 1 (by rfl) ⟨308132, by rfl⟩ : syracuseStep 410843 = 616265) B616265
theorem B1557751 : Blo 409770 1557751 := bstep (se 1 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 1557751 = 2336627) B2336627
theorem B2639141 : Blo 409770 2639141 := bstep (se 4 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 2639141 = 494839) B494839
theorem B410919 : Blo 409770 410919 := bstep (se 1 (by rfl) ⟨308189, by rfl⟩ : syracuseStep 410919 = 616379) B616379
theorem B410959 : Blo 409770 410959 := bstep (se 1 (by rfl) ⟨308219, by rfl⟩ : syracuseStep 410959 = 616439) B616439
theorem B410975 : Blo 409770 410975 := bstep (se 1 (by rfl) ⟨308231, by rfl⟩ : syracuseStep 410975 = 616463) B616463
theorem B411003 : Blo 409770 411003 := bstep (se 1 (by rfl) ⟨308252, by rfl⟩ : syracuseStep 411003 = 616505) B616505
theorem B1394063 : Blo 409770 1394063 := bstep (se 1 (by rfl) ⟨1045547, by rfl⟩ : syracuseStep 1394063 = 2091095) B2091095
theorem B411055 : Blo 409770 411055 := bstep (se 1 (by rfl) ⟨308291, by rfl⟩ : syracuseStep 411055 = 616583) B616583
theorem B411079 : Blo 409770 411079 := bstep (se 1 (by rfl) ⟨308309, by rfl⟩ : syracuseStep 411079 = 616619) B616619
theorem B411099 : Blo 409770 411099 := bstep (se 1 (by rfl) ⟨308324, by rfl⟩ : syracuseStep 411099 = 616649) B616649
theorem B1558025 : Blo 409770 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B1558055 : Blo 409770 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B411175 : Blo 409770 411175 := bstep (se 1 (by rfl) ⟨308381, by rfl⟩ : syracuseStep 411175 = 616763) B616763
theorem B411215 : Blo 409770 411215 := bstep (se 1 (by rfl) ⟨308411, by rfl⟩ : syracuseStep 411215 = 616823) B616823
theorem B411231 : Blo 409770 411231 := bstep (se 1 (by rfl) ⟨308423, by rfl⟩ : syracuseStep 411231 = 616847) B616847
theorem B411259 : Blo 409770 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B411311 : Blo 409770 411311 := bstep (se 1 (by rfl) ⟨308483, by rfl⟩ : syracuseStep 411311 = 616967) B616967
theorem B411335 : Blo 409770 411335 := bstep (se 1 (by rfl) ⟨308501, by rfl⟩ : syracuseStep 411335 = 617003) B617003
theorem B1394387 : Blo 409770 1394387 := bstep (se 1 (by rfl) ⟨1045790, by rfl⟩ : syracuseStep 1394387 = 2091581) B2091581
theorem B411355 : Blo 409770 411355 := bstep (se 1 (by rfl) ⟨308516, by rfl⟩ : syracuseStep 411355 = 617033) B617033
theorem B411431 : Blo 409770 411431 := bstep (se 1 (by rfl) ⟨308573, by rfl⟩ : syracuseStep 411431 = 617147) B617147
theorem B837449 : Blo 409770 837449 := bstep (se 2 (by rfl) ⟨314043, by rfl⟩ : syracuseStep 837449 = 628087) B628087
theorem B411471 : Blo 409770 411471 := bstep (se 1 (by rfl) ⟨308603, by rfl⟩ : syracuseStep 411471 = 617207) B617207
theorem B411487 : Blo 409770 411487 := bstep (se 1 (by rfl) ⟨308615, by rfl⟩ : syracuseStep 411487 = 617231) B617231
theorem B411515 : Blo 409770 411515 := bstep (se 1 (by rfl) ⟨308636, by rfl⟩ : syracuseStep 411515 = 617273) B617273
theorem B3131297 : Blo 409770 3131297 := bstep (se 2 (by rfl) ⟨1174236, by rfl⟩ : syracuseStep 3131297 = 2348473) B2348473
theorem B411567 : Blo 409770 411567 := bstep (se 1 (by rfl) ⟨308675, by rfl⟩ : syracuseStep 411567 = 617351) B617351
theorem B411591 : Blo 409770 411591 := bstep (se 1 (by rfl) ⟨308693, by rfl⟩ : syracuseStep 411591 = 617387) B617387
theorem B411611 : Blo 409770 411611 := bstep (se 1 (by rfl) ⟨308708, by rfl⟩ : syracuseStep 411611 = 617417) B617417
theorem B11290661 : Blo 409770 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B411687 : Blo 409770 411687 := bstep (se 1 (by rfl) ⟨308765, by rfl⟩ : syracuseStep 411687 = 617531) B617531
theorem B411727 : Blo 409770 411727 := bstep (se 1 (by rfl) ⟨308795, by rfl⟩ : syracuseStep 411727 = 617591) B617591
theorem B1984601 : Blo 409770 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B411743 : Blo 409770 411743 := bstep (se 1 (by rfl) ⟨308807, by rfl⟩ : syracuseStep 411743 = 617615) B617615
theorem B411771 : Blo 409770 411771 := bstep (se 1 (by rfl) ⟨308828, by rfl⟩ : syracuseStep 411771 = 617657) B617657
theorem B411823 : Blo 409770 411823 := bstep (se 1 (by rfl) ⟨308867, by rfl⟩ : syracuseStep 411823 = 617735) B617735
theorem B1558723 : Blo 409770 1558723 := bstep (se 1 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 1558723 = 2338085) B2338085
theorem B411847 : Blo 409770 411847 := bstep (se 1 (by rfl) ⟨308885, by rfl⟩ : syracuseStep 411847 = 617771) B617771
theorem B411867 : Blo 409770 411867 := bstep (se 1 (by rfl) ⟨308900, by rfl⟩ : syracuseStep 411867 = 617801) B617801
theorem B411943 : Blo 409770 411943 := bstep (se 1 (by rfl) ⟨308957, by rfl⟩ : syracuseStep 411943 = 617915) B617915
theorem B411983 : Blo 409770 411983 := bstep (se 1 (by rfl) ⟨308987, by rfl⟩ : syracuseStep 411983 = 617975) B617975
theorem B411999 : Blo 409770 411999 := bstep (se 1 (by rfl) ⟨308999, by rfl⟩ : syracuseStep 411999 = 617999) B617999
theorem B412027 : Blo 409770 412027 := bstep (se 1 (by rfl) ⟨309020, by rfl⟩ : syracuseStep 412027 = 618041) B618041
theorem B412079 : Blo 409770 412079 := bstep (se 1 (by rfl) ⟨309059, by rfl⟩ : syracuseStep 412079 = 618119) B618119
theorem B412103 : Blo 409770 412103 := bstep (se 1 (by rfl) ⟨309077, by rfl⟩ : syracuseStep 412103 = 618155) B618155
theorem B412123 : Blo 409770 412123 := bstep (se 1 (by rfl) ⟨309092, by rfl⟩ : syracuseStep 412123 = 618185) B618185
theorem B1559027 : Blo 409770 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B412199 : Blo 409770 412199 := bstep (se 1 (by rfl) ⟨309149, by rfl⟩ : syracuseStep 412199 = 618299) B618299
theorem B412239 : Blo 409770 412239 := bstep (se 1 (by rfl) ⟨309179, by rfl⟩ : syracuseStep 412239 = 618359) B618359
theorem B412255 : Blo 409770 412255 := bstep (se 1 (by rfl) ⟨309191, by rfl⟩ : syracuseStep 412255 = 618383) B618383
theorem B412283 : Blo 409770 412283 := bstep (se 1 (by rfl) ⟨309212, by rfl⟩ : syracuseStep 412283 = 618425) B618425
theorem B412335 : Blo 409770 412335 := bstep (se 1 (by rfl) ⟨309251, by rfl⟩ : syracuseStep 412335 = 618503) B618503
theorem B412359 : Blo 409770 412359 := bstep (se 1 (by rfl) ⟨309269, by rfl⟩ : syracuseStep 412359 = 618539) B618539
theorem B412379 : Blo 409770 412379 := bstep (se 1 (by rfl) ⟨309284, by rfl⟩ : syracuseStep 412379 = 618569) B618569
theorem B412455 : Blo 409770 412455 := bstep (se 1 (by rfl) ⟨309341, by rfl⟩ : syracuseStep 412455 = 618683) B618683
theorem B412495 : Blo 409770 412495 := bstep (se 1 (by rfl) ⟨309371, by rfl⟩ : syracuseStep 412495 = 618743) B618743
theorem B412511 : Blo 409770 412511 := bstep (se 1 (by rfl) ⟨309383, by rfl⟩ : syracuseStep 412511 = 618767) B618767
theorem B838505 : Blo 409770 838505 := bstep (se 2 (by rfl) ⟨314439, by rfl⟩ : syracuseStep 838505 = 628879) B628879
theorem B2968427 : Blo 409770 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B1395575 : Blo 409770 1395575 := bstep (se 1 (by rfl) ⟨1046681, by rfl⟩ : syracuseStep 1395575 = 2093363) B2093363
theorem B1592183 : Blo 409770 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B412539 : Blo 409770 412539 := bstep (se 1 (by rfl) ⟨309404, by rfl⟩ : syracuseStep 412539 = 618809) B618809
theorem B1067951 : Blo 409770 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B412591 : Blo 409770 412591 := bstep (se 1 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 412591 = 618887) B618887
theorem B1559483 : Blo 409770 1559483 := bstep (se 1 (by rfl) ⟨1169612, by rfl⟩ : syracuseStep 1559483 = 2339225) B2339225
theorem B412615 : Blo 409770 412615 := bstep (se 1 (by rfl) ⟨309461, by rfl⟩ : syracuseStep 412615 = 618923) B618923
theorem B412635 : Blo 409770 412635 := bstep (se 1 (by rfl) ⟨309476, by rfl⟩ : syracuseStep 412635 = 618953) B618953
theorem B412711 : Blo 409770 412711 := bstep (se 1 (by rfl) ⟨309533, by rfl⟩ : syracuseStep 412711 = 619067) B619067
theorem B412751 : Blo 409770 412751 := bstep (se 1 (by rfl) ⟨309563, by rfl⟩ : syracuseStep 412751 = 619127) B619127
theorem B1395791 : Blo 409770 1395791 := bstep (se 1 (by rfl) ⟨1046843, by rfl⟩ : syracuseStep 1395791 = 2093687) B2093687
theorem B412767 : Blo 409770 412767 := bstep (se 1 (by rfl) ⟨309575, by rfl⟩ : syracuseStep 412767 = 619151) B619151
theorem B412795 : Blo 409770 412795 := bstep (se 1 (by rfl) ⟨309596, by rfl⟩ : syracuseStep 412795 = 619193) B619193
theorem B412847 : Blo 409770 412847 := bstep (se 1 (by rfl) ⟨309635, by rfl⟩ : syracuseStep 412847 = 619271) B619271
theorem B412871 : Blo 409770 412871 := bstep (se 1 (by rfl) ⟨309653, by rfl⟩ : syracuseStep 412871 = 619307) B619307
theorem B412891 : Blo 409770 412891 := bstep (se 1 (by rfl) ⟨309668, by rfl⟩ : syracuseStep 412891 = 619337) B619337
theorem B412967 : Blo 409770 412967 := bstep (se 1 (by rfl) ⟨309725, by rfl⟩ : syracuseStep 412967 = 619451) B619451
theorem B413007 : Blo 409770 413007 := bstep (se 1 (by rfl) ⟨309755, by rfl⟩ : syracuseStep 413007 = 619511) B619511
theorem B413023 : Blo 409770 413023 := bstep (se 1 (by rfl) ⟨309767, by rfl⟩ : syracuseStep 413023 = 619535) B619535
theorem B413051 : Blo 409770 413051 := bstep (se 1 (by rfl) ⟨309788, by rfl⟩ : syracuseStep 413051 = 619577) B619577
theorem B413103 : Blo 409770 413103 := bstep (se 1 (by rfl) ⟨309827, by rfl⟩ : syracuseStep 413103 = 619655) B619655
theorem B413127 : Blo 409770 413127 := bstep (se 1 (by rfl) ⟨309845, by rfl⟩ : syracuseStep 413127 = 619691) B619691
theorem B1396169 : Blo 409770 1396169 := bstep (se 2 (by rfl) ⟨523563, by rfl⟩ : syracuseStep 1396169 = 1047127) B1047127
theorem B413147 : Blo 409770 413147 := bstep (se 1 (by rfl) ⟨309860, by rfl⟩ : syracuseStep 413147 = 619721) B619721
theorem B413223 : Blo 409770 413223 := bstep (se 1 (by rfl) ⟨309917, by rfl⟩ : syracuseStep 413223 = 619835) B619835
theorem B413263 : Blo 409770 413263 := bstep (se 1 (by rfl) ⟨309947, by rfl⟩ : syracuseStep 413263 = 619895) B619895
theorem B413279 : Blo 409770 413279 := bstep (se 1 (by rfl) ⟨309959, by rfl⟩ : syracuseStep 413279 = 619919) B619919
theorem B413307 : Blo 409770 413307 := bstep (se 1 (by rfl) ⟨309980, by rfl⟩ : syracuseStep 413307 = 619961) B619961
theorem B413359 : Blo 409770 413359 := bstep (se 1 (by rfl) ⟨310019, by rfl⟩ : syracuseStep 413359 = 620039) B620039
theorem B413383 : Blo 409770 413383 := bstep (se 1 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 413383 = 620075) B620075
theorem B1396439 : Blo 409770 1396439 := bstep (se 1 (by rfl) ⟨1047329, by rfl⟩ : syracuseStep 1396439 = 2094659) B2094659
theorem B413403 : Blo 409770 413403 := bstep (se 1 (by rfl) ⟨310052, by rfl⟩ : syracuseStep 413403 = 620105) B620105
theorem B413479 : Blo 409770 413479 := bstep (se 1 (by rfl) ⟨310109, by rfl⟩ : syracuseStep 413479 = 620219) B620219
theorem B413519 : Blo 409770 413519 := bstep (se 1 (by rfl) ⟨310139, by rfl⟩ : syracuseStep 413519 = 620279) B620279
theorem B413535 : Blo 409770 413535 := bstep (se 1 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 413535 = 620303) B620303
theorem B413563 : Blo 409770 413563 := bstep (se 1 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 413563 = 620345) B620345
theorem B413615 : Blo 409770 413615 := bstep (se 1 (by rfl) ⟨310211, by rfl⟩ : syracuseStep 413615 = 620423) B620423
theorem B413639 : Blo 409770 413639 := bstep (se 1 (by rfl) ⟨310229, by rfl⟩ : syracuseStep 413639 = 620459) B620459
theorem B413659 : Blo 409770 413659 := bstep (se 1 (by rfl) ⟨310244, by rfl⟩ : syracuseStep 413659 = 620489) B620489
theorem B2347015 : Blo 409770 2347015 := bstep (se 1 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 2347015 = 3520523) B3520523
theorem B413735 : Blo 409770 413735 := bstep (se 1 (by rfl) ⟨310301, by rfl⟩ : syracuseStep 413735 = 620603) B620603
theorem B5001533 : Blo 409770 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B5263973 : Blo 409770 5263973 := bstep (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) B986995
theorem B1167995 : Blo 409770 1167995 := bstep (se 1 (by rfl) ⟨875996, by rfl⟩ : syracuseStep 1167995 = 1751993) B1751993
theorem B2085587 : Blo 409770 2085587 := bstep (se 1 (by rfl) ⟨1564190, by rfl⟩ : syracuseStep 2085587 = 3128381) B3128381
theorem B1168121 : Blo 409770 1168121 := bstep (se 2 (by rfl) ⟨438045, by rfl⟩ : syracuseStep 1168121 = 876091) B876091
theorem B12342131 : Blo 409770 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1168303 : Blo 409770 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B1561943 : Blo 409770 1561943 := bstep (se 1 (by rfl) ⟨1171457, by rfl⟩ : syracuseStep 1561943 = 2342915) B2342915
theorem B1168769 : Blo 409770 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B1037711 : Blo 409770 1037711 := bstep (se 1 (by rfl) ⟨778283, by rfl⟩ : syracuseStep 1037711 = 1556567) B1556567
theorem B1038035 : Blo 409770 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B743159 : Blo 409770 743159 := bstep (se 1 (by rfl) ⟨557369, by rfl⟩ : syracuseStep 743159 = 1114739) B1114739
theorem B1169225 : Blo 409770 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B4773977 : Blo 409770 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B1169579 : Blo 409770 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B4446667 : Blo 409770 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B7101107 : Blo 409770 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B5954381 : Blo 409770 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B2349931 : Blo 409770 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B3169169 : Blo 409770 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B2087855 : Blo 409770 2087855 := bstep (se 1 (by rfl) ⟨1565891, by rfl⟩ : syracuseStep 2087855 = 3131783) B3131783
theorem B744571 : Blo 409770 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B2383019 : Blo 409770 2383019 := bstep (se 1 (by rfl) ⟨1787264, by rfl⟩ : syracuseStep 2383019 = 3574529) B3574529
theorem B8871191 : Blo 409770 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B48717233 : Blo 409770 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B778079 : Blo 409770 778079 := bstep (se 1 (by rfl) ⟨583559, by rfl⟩ : syracuseStep 778079 = 1167119) B1167119
theorem B1040303 : Blo 409770 1040303 := bstep (se 1 (by rfl) ⟨780227, by rfl⟩ : syracuseStep 1040303 = 1560455) B1560455
theorem B1564829 : Blo 409770 1564829 := bstep (se 3 (by rfl) ⟨293405, by rfl⟩ : syracuseStep 1564829 = 586811) B586811
theorem B614831 : Blo 409770 614831 := bstep (se 1 (by rfl) ⟨461123, by rfl⟩ : syracuseStep 614831 = 922247) B922247
theorem B614921 : Blo 409770 614921 := bstep (se 2 (by rfl) ⟨230595, by rfl⟩ : syracuseStep 614921 = 461191) B461191
theorem B1040921 : Blo 409770 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B614951 : Blo 409770 614951 := bstep (se 1 (by rfl) ⟨461213, by rfl⟩ : syracuseStep 614951 = 922427) B922427
theorem B615035 : Blo 409770 615035 := bstep (se 1 (by rfl) ⟨461276, by rfl⟩ : syracuseStep 615035 = 922553) B922553
theorem B615161 : Blo 409770 615161 := bstep (se 2 (by rfl) ⟨230685, by rfl⟩ : syracuseStep 615161 = 461371) B461371
theorem B1565513 : Blo 409770 1565513 := bstep (se 2 (by rfl) ⟨587067, by rfl⟩ : syracuseStep 1565513 = 1174135) B1174135
theorem B615263 : Blo 409770 615263 := bstep (se 1 (by rfl) ⟨461447, by rfl⟩ : syracuseStep 615263 = 922895) B922895
theorem B615275 : Blo 409770 615275 := bstep (se 1 (by rfl) ⟨461456, by rfl⟩ : syracuseStep 615275 = 922913) B922913
theorem B779195 : Blo 409770 779195 := bstep (se 1 (by rfl) ⟨584396, by rfl⟩ : syracuseStep 779195 = 1168793) B1168793
theorem B4678721 : Blo 409770 4678721 := bstep (se 2 (by rfl) ⟨1754520, by rfl⟩ : syracuseStep 4678721 = 3509041) B3509041
theorem B615503 : Blo 409770 615503 := bstep (se 1 (by rfl) ⟨461627, by rfl⟩ : syracuseStep 615503 = 923255) B923255
theorem B2974799 : Blo 409770 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B615623 : Blo 409770 615623 := bstep (se 1 (by rfl) ⟨461717, by rfl⟩ : syracuseStep 615623 = 923435) B923435
theorem B1566013 : Blo 409770 1566013 := bstep (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) B587255
theorem B615785 : Blo 409770 615785 := bstep (se 2 (by rfl) ⟨230919, by rfl⟩ : syracuseStep 615785 = 461839) B461839
theorem B779681 : Blo 409770 779681 := bstep (se 2 (by rfl) ⟨292380, by rfl⟩ : syracuseStep 779681 = 584761) B584761
theorem B615863 : Blo 409770 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B615899 : Blo 409770 615899 := bstep (se 1 (by rfl) ⟨461924, by rfl⟩ : syracuseStep 615899 = 923849) B923849
theorem B780023 : Blo 409770 780023 := bstep (se 1 (by rfl) ⟨585017, by rfl⟩ : syracuseStep 780023 = 1170035) B1170035
theorem B583519 : Blo 409770 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B1763167 : Blo 409770 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B616367 : Blo 409770 616367 := bstep (se 1 (by rfl) ⟨462275, by rfl⟩ : syracuseStep 616367 = 924551) B924551
theorem B616457 : Blo 409770 616457 := bstep (se 2 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 616457 = 462343) B462343
theorem B616487 : Blo 409770 616487 := bstep (se 1 (by rfl) ⟨462365, by rfl⟩ : syracuseStep 616487 = 924731) B924731
theorem B616571 : Blo 409770 616571 := bstep (se 1 (by rfl) ⟨462428, by rfl⟩ : syracuseStep 616571 = 924857) B924857
theorem B616697 : Blo 409770 616697 := bstep (se 2 (by rfl) ⟨231261, by rfl⟩ : syracuseStep 616697 = 462523) B462523
theorem B616799 : Blo 409770 616799 := bstep (se 1 (by rfl) ⟨462599, by rfl⟩ : syracuseStep 616799 = 925199) B925199
theorem B616811 : Blo 409770 616811 := bstep (se 1 (by rfl) ⟨462608, by rfl⟩ : syracuseStep 616811 = 925217) B925217
theorem B617039 : Blo 409770 617039 := bstep (se 1 (by rfl) ⟨462779, by rfl⟩ : syracuseStep 617039 = 925559) B925559
theorem B617159 : Blo 409770 617159 := bstep (se 1 (by rfl) ⟨462869, by rfl⟩ : syracuseStep 617159 = 925739) B925739
theorem B1764125 : Blo 409770 1764125 := bstep (se 3 (by rfl) ⟨330773, by rfl⟩ : syracuseStep 1764125 = 661547) B661547
theorem B3533645 : Blo 409770 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B617321 : Blo 409770 617321 := bstep (se 2 (by rfl) ⟨231495, by rfl⟩ : syracuseStep 617321 = 462991) B462991
theorem B617399 : Blo 409770 617399 := bstep (se 1 (by rfl) ⟨463049, by rfl⟩ : syracuseStep 617399 = 926099) B926099
theorem B617435 : Blo 409770 617435 := bstep (se 1 (by rfl) ⟨463076, by rfl⟩ : syracuseStep 617435 = 926153) B926153
theorem B1567745 : Blo 409770 1567745 := bstep (se 2 (by rfl) ⟨587904, by rfl⟩ : syracuseStep 1567745 = 1175809) B1175809
theorem B781321 : Blo 409770 781321 := bstep (se 2 (by rfl) ⟨292995, by rfl⟩ : syracuseStep 781321 = 585991) B585991
theorem B1043513 : Blo 409770 1043513 := bstep (se 2 (by rfl) ⟨391317, by rfl⟩ : syracuseStep 1043513 = 782635) B782635
theorem B3501251 : Blo 409770 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B519367 : Blo 409770 519367 := bstep (se 1 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 519367 = 779051) B779051
theorem B781663 : Blo 409770 781663 := bstep (se 1 (by rfl) ⟨586247, by rfl⟩ : syracuseStep 781663 = 1172495) B1172495
theorem B15232387 : Blo 409770 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B5074319 : Blo 409770 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B617903 : Blo 409770 617903 := bstep (se 1 (by rfl) ⟨463427, by rfl⟩ : syracuseStep 617903 = 926855) B926855
theorem B617993 : Blo 409770 617993 := bstep (se 2 (by rfl) ⟨231747, by rfl⟩ : syracuseStep 617993 = 463495) B463495
theorem B618023 : Blo 409770 618023 := bstep (se 1 (by rfl) ⟨463517, by rfl⟩ : syracuseStep 618023 = 927035) B927035
theorem B618107 : Blo 409770 618107 := bstep (se 1 (by rfl) ⟨463580, by rfl⟩ : syracuseStep 618107 = 927161) B927161
theorem B12906161 : Blo 409770 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B1175239 : Blo 409770 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B618233 : Blo 409770 618233 := bstep (se 2 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 618233 = 463675) B463675
theorem B1666889 : Blo 409770 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B1208137 : Blo 409770 1208137 := bstep (se 2 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 1208137 = 906103) B906103
theorem B618335 : Blo 409770 618335 := bstep (se 1 (by rfl) ⟨463751, by rfl⟩ : syracuseStep 618335 = 927503) B927503
theorem B618347 : Blo 409770 618347 := bstep (se 1 (by rfl) ⟨463760, by rfl⟩ : syracuseStep 618347 = 927521) B927521
theorem B520111 : Blo 409770 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B618575 : Blo 409770 618575 := bstep (se 1 (by rfl) ⟨463931, by rfl⟩ : syracuseStep 618575 = 927863) B927863
theorem B618695 : Blo 409770 618695 := bstep (se 1 (by rfl) ⟨464021, by rfl⟩ : syracuseStep 618695 = 928043) B928043
theorem B618857 : Blo 409770 618857 := bstep (se 2 (by rfl) ⟨232071, by rfl⟩ : syracuseStep 618857 = 464143) B464143
theorem B618935 : Blo 409770 618935 := bstep (se 1 (by rfl) ⟨464201, by rfl⟩ : syracuseStep 618935 = 928403) B928403
theorem B782779 : Blo 409770 782779 := bstep (se 1 (by rfl) ⟨587084, by rfl⟩ : syracuseStep 782779 = 1174169) B1174169
theorem B618971 : Blo 409770 618971 := bstep (se 1 (by rfl) ⟨464228, by rfl⟩ : syracuseStep 618971 = 928457) B928457
theorem B782855 : Blo 409770 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B1045001 : Blo 409770 1045001 := bstep (se 2 (by rfl) ⟨391875, by rfl⟩ : syracuseStep 1045001 = 783751) B783751
theorem B1569415 : Blo 409770 1569415 := bstep (se 1 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 1569415 = 2354123) B2354123
theorem B2978633 : Blo 409770 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B783265 : Blo 409770 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B619439 : Blo 409770 619439 := bstep (se 1 (by rfl) ⟨464579, by rfl⟩ : syracuseStep 619439 = 929159) B929159
theorem B1569719 : Blo 409770 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B2814977 : Blo 409770 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B619529 : Blo 409770 619529 := bstep (se 2 (by rfl) ⟨232323, by rfl⟩ : syracuseStep 619529 = 464647) B464647
theorem B521255 : Blo 409770 521255 := bstep (se 1 (by rfl) ⟨390941, by rfl⟩ : syracuseStep 521255 = 781883) B781883
theorem B619559 : Blo 409770 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B619643 : Blo 409770 619643 := bstep (se 1 (by rfl) ⟨464732, by rfl⟩ : syracuseStep 619643 = 929465) B929465
theorem B783607 : Blo 409770 783607 := bstep (se 1 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 783607 = 1175411) B1175411
theorem B619769 : Blo 409770 619769 := bstep (se 2 (by rfl) ⟨232413, by rfl⟩ : syracuseStep 619769 = 464827) B464827
theorem B619871 : Blo 409770 619871 := bstep (se 1 (by rfl) ⟨464903, by rfl⟩ : syracuseStep 619871 = 929807) B929807
theorem B521579 : Blo 409770 521579 := bstep (se 1 (by rfl) ⟨391184, by rfl⟩ : syracuseStep 521579 = 782369) B782369
theorem B619883 : Blo 409770 619883 := bstep (se 1 (by rfl) ⟨464912, by rfl⟩ : syracuseStep 619883 = 929825) B929825
theorem B1177051 : Blo 409770 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B5273099 : Blo 409770 5273099 := bstep (se 1 (by rfl) ⟨3954824, by rfl⟩ : syracuseStep 5273099 = 7909649) B7909649
theorem B783911 : Blo 409770 783911 := bstep (se 1 (by rfl) ⟨587933, by rfl⟩ : syracuseStep 783911 = 1175867) B1175867
theorem B620111 : Blo 409770 620111 := bstep (se 1 (by rfl) ⟨465083, by rfl⟩ : syracuseStep 620111 = 930167) B930167
theorem B1046155 : Blo 409770 1046155 := bstep (se 1 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 1046155 = 1569233) B1569233
theorem B620231 : Blo 409770 620231 := bstep (se 1 (by rfl) ⟨465173, by rfl⟩ : syracuseStep 620231 = 930347) B930347
theorem B620393 : Blo 409770 620393 := bstep (se 2 (by rfl) ⟨232647, by rfl⟩ : syracuseStep 620393 = 465295) B465295
theorem B620471 : Blo 409770 620471 := bstep (se 1 (by rfl) ⟨465353, by rfl⟩ : syracuseStep 620471 = 930707) B930707
theorem B1046459 : Blo 409770 1046459 := bstep (se 1 (by rfl) ⟨784844, by rfl⟩ : syracuseStep 1046459 = 1569689) B1569689
theorem B620507 : Blo 409770 620507 := bstep (se 1 (by rfl) ⟨465380, by rfl⟩ : syracuseStep 620507 = 930761) B930761
theorem B1570873 : Blo 409770 1570873 := bstep (se 2 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 1570873 = 1178155) B1178155
theorem B4520279 : Blo 409770 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B1669481 : Blo 409770 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B1341839 : Blo 409770 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B3963437 : Blo 409770 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B522875 : Blo 409770 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B1047239 : Blo 409770 1047239 := bstep (se 1 (by rfl) ⟨785429, by rfl⟩ : syracuseStep 1047239 = 1570859) B1570859
theorem B1047289 : Blo 409770 1047289 := bstep (se 2 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 1047289 = 785467) B785467
theorem B1113335 : Blo 409770 1113335 := bstep (se 1 (by rfl) ⟨835001, by rfl⟩ : syracuseStep 1113335 = 1670003) B1670003
theorem B2981285 : Blo 409770 2981285 := bstep (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) B558991
theorem B6651317 : Blo 409770 6651317 := bstep (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) B623561
theorem B1114393 : Blo 409770 1114393 := bstep (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) B835795
theorem B3769249 : Blo 409770 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B558299 : Blo 409770 558299 := bstep (se 1 (by rfl) ⟨418724, by rfl⟩ : syracuseStep 558299 = 837449) B837449
theorem B559003 : Blo 409770 559003 := bstep (se 1 (by rfl) ⟨419252, by rfl⟩ : syracuseStep 559003 = 838505) B838505
theorem B657991 : Blo 409770 657991 := bstep (se 1 (by rfl) ⟨493493, by rfl⟩ : syracuseStep 657991 = 986987) B986987
theorem B461407 : Blo 409770 461407 := bstep (se 1 (by rfl) ⟨346055, by rfl⟩ : syracuseStep 461407 = 692111) B692111
theorem B3509315 : Blo 409770 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B8228087 : Blo 409770 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B2886943 : Blo 409770 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B658811 : Blo 409770 658811 := bstep (se 1 (by rfl) ⟨494108, by rfl⟩ : syracuseStep 658811 = 988217) B988217
theorem B691807 : Blo 409770 691807 := bstep (se 1 (by rfl) ⟨518855, by rfl⟩ : syracuseStep 691807 = 1037711) B1037711
theorem B3116717 : Blo 409770 3116717 := bstep (se 3 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 3116717 = 1168769) B1168769
theorem B462559 : Blo 409770 462559 := bstep (se 1 (by rfl) ⟨346919, by rfl⟩ : syracuseStep 462559 = 693839) B693839
theorem B692023 : Blo 409770 692023 := bstep (se 1 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 692023 = 1038035) B1038035
theorem B495439 : Blo 409770 495439 := bstep (se 1 (by rfl) ⟨371579, by rfl⟩ : syracuseStep 495439 = 743159) B743159
theorem B3182651 : Blo 409770 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B3510377 : Blo 409770 3510377 := bstep (se 2 (by rfl) ⟨1316391, by rfl⟩ : syracuseStep 3510377 = 2632783) B2632783
theorem B692489 : Blo 409770 692489 := bstep (se 2 (by rfl) ⟨259683, by rfl⟩ : syracuseStep 692489 = 519367) B519367
theorem B463135 : Blo 409770 463135 := bstep (se 1 (by rfl) ⟨347351, by rfl⟩ : syracuseStep 463135 = 694703) B694703
theorem B922031 : Blo 409770 922031 := bstep (se 1 (by rfl) ⟨691523, by rfl⟩ : syracuseStep 922031 = 1383047) B1383047
theorem B922067 : Blo 409770 922067 := bstep (se 1 (by rfl) ⟨691550, by rfl⟩ : syracuseStep 922067 = 1383101) B1383101
theorem B3969587 : Blo 409770 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B922175 : Blo 409770 922175 := bstep (se 1 (by rfl) ⟨691631, by rfl⟩ : syracuseStep 922175 = 1383263) B1383263
theorem B463423 : Blo 409770 463423 := bstep (se 1 (by rfl) ⟨347567, by rfl⟩ : syracuseStep 463423 = 695135) B695135
theorem B987727 : Blo 409770 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B3117689 : Blo 409770 3117689 := bstep (se 2 (by rfl) ⟨1169133, by rfl⟩ : syracuseStep 3117689 = 2338267) B2338267
theorem B922283 : Blo 409770 922283 := bstep (se 1 (by rfl) ⟨691712, by rfl⟩ : syracuseStep 922283 = 1383425) B1383425
theorem B2626505 : Blo 409770 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B32478155 : Blo 409770 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B1610849 : Blo 409770 1610849 := bstep (se 2 (by rfl) ⟨604068, by rfl⟩ : syracuseStep 1610849 = 1208137) B1208137
theorem B922823 : Blo 409770 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B693481 : Blo 409770 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B693535 : Blo 409770 693535 := bstep (se 1 (by rfl) ⟨520151, by rfl⟩ : syracuseStep 693535 = 1040303) B1040303
theorem B791905 : Blo 409770 791905 := bstep (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) B593929
theorem B923003 : Blo 409770 923003 := bstep (se 1 (by rfl) ⟨692252, by rfl⟩ : syracuseStep 923003 = 1384505) B1384505
theorem B464251 : Blo 409770 464251 := bstep (se 1 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 464251 = 696377) B696377
theorem B3020165 : Blo 409770 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B988631 : Blo 409770 988631 := bstep (se 1 (by rfl) ⟨741473, by rfl⟩ : syracuseStep 988631 = 1482947) B1482947
theorem B923129 : Blo 409770 923129 := bstep (se 2 (by rfl) ⟨346173, by rfl⟩ : syracuseStep 923129 = 692347) B692347
theorem B988679 : Blo 409770 988679 := bstep (se 1 (by rfl) ⟨741509, by rfl⟩ : syracuseStep 988679 = 1483019) B1483019
theorem B2233889 : Blo 409770 2233889 := bstep (se 2 (by rfl) ⟨837708, by rfl⟩ : syracuseStep 2233889 = 1675417) B1675417
theorem B3741223 : Blo 409770 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B923219 : Blo 409770 923219 := bstep (se 1 (by rfl) ⟨692414, by rfl⟩ : syracuseStep 923219 = 1384829) B1384829
theorem B693947 : Blo 409770 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B923399 : Blo 409770 923399 := bstep (se 1 (by rfl) ⟨692549, by rfl⟩ : syracuseStep 923399 = 1385099) B1385099
theorem B464719 : Blo 409770 464719 := bstep (se 1 (by rfl) ⟨348539, by rfl⟩ : syracuseStep 464719 = 697079) B697079
theorem B3971045 : Blo 409770 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B3119147 : Blo 409770 3119147 := bstep (se 1 (by rfl) ⟨2339360, by rfl⟩ : syracuseStep 3119147 = 4678721) B4678721
theorem B465115 : Blo 409770 465115 := bstep (se 1 (by rfl) ⟨348836, by rfl⟩ : syracuseStep 465115 = 697673) B697673
theorem B924011 : Blo 409770 924011 := bstep (se 1 (by rfl) ⟨693008, by rfl⟩ : syracuseStep 924011 = 1386017) B1386017
theorem B924155 : Blo 409770 924155 := bstep (se 1 (by rfl) ⟨693116, by rfl⟩ : syracuseStep 924155 = 1386233) B1386233
theorem B465403 : Blo 409770 465403 := bstep (se 1 (by rfl) ⟨349052, by rfl⟩ : syracuseStep 465403 = 698105) B698105
theorem B1317455 : Blo 409770 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B924281 : Blo 409770 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B924335 : Blo 409770 924335 := bstep (se 1 (by rfl) ⟨693251, by rfl⟩ : syracuseStep 924335 = 1386503) B1386503
theorem B924407 : Blo 409770 924407 := bstep (se 1 (by rfl) ⟨693305, by rfl⟩ : syracuseStep 924407 = 1386611) B1386611
theorem B924587 : Blo 409770 924587 := bstep (se 1 (by rfl) ⟨693440, by rfl⟩ : syracuseStep 924587 = 1386881) B1386881
theorem B695675 : Blo 409770 695675 := bstep (se 1 (by rfl) ⟨521756, by rfl⟩ : syracuseStep 695675 = 1043513) B1043513
theorem B925127 : Blo 409770 925127 := bstep (se 1 (by rfl) ⟨693845, by rfl⟩ : syracuseStep 925127 = 1387691) B1387691
theorem B2334167 : Blo 409770 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B1384019 : Blo 409770 1384019 := bstep (se 1 (by rfl) ⟨1038014, by rfl⟩ : syracuseStep 1384019 = 2076029) B2076029
theorem B3382879 : Blo 409770 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B925487 : Blo 409770 925487 := bstep (se 1 (by rfl) ⟨694115, by rfl⟩ : syracuseStep 925487 = 1388231) B1388231
theorem B4464659 : Blo 409770 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B696667 : Blo 409770 696667 := bstep (se 1 (by rfl) ⟨522500, by rfl⟩ : syracuseStep 696667 = 1045001) B1045001
theorem B926063 : Blo 409770 926063 := bstep (se 1 (by rfl) ⟨694547, by rfl⟩ : syracuseStep 926063 = 1389095) B1389095
theorem B926135 : Blo 409770 926135 := bstep (se 1 (by rfl) ⟨694601, by rfl⟩ : syracuseStep 926135 = 1389203) B1389203
theorem B6758923 : Blo 409770 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B926279 : Blo 409770 926279 := bstep (se 1 (by rfl) ⟨694709, by rfl⟩ : syracuseStep 926279 = 1389419) B1389419
theorem B926315 : Blo 409770 926315 := bstep (se 1 (by rfl) ⟨694736, by rfl⟩ : syracuseStep 926315 = 1389473) B1389473
theorem B1876651 : Blo 409770 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B926711 : Blo 409770 926711 := bstep (se 1 (by rfl) ⟨695033, by rfl⟩ : syracuseStep 926711 = 1390067) B1390067
theorem B3515399 : Blo 409770 3515399 := bstep (se 1 (by rfl) ⟨2636549, by rfl⟩ : syracuseStep 3515399 = 5273099) B5273099
theorem B1320083 : Blo 409770 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B1975529 : Blo 409770 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B697639 : Blo 409770 697639 := bstep (se 1 (by rfl) ⟨523229, by rfl⟩ : syracuseStep 697639 = 1046459) B1046459
theorem B927071 : Blo 409770 927071 := bstep (se 1 (by rfl) ⟨695303, by rfl⟩ : syracuseStep 927071 = 1390607) B1390607
theorem B894559 : Blo 409770 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B927467 : Blo 409770 927467 := bstep (se 1 (by rfl) ⟨695600, by rfl⟩ : syracuseStep 927467 = 1391201) B1391201
theorem B698159 : Blo 409770 698159 := bstep (se 1 (by rfl) ⟨523619, by rfl⟩ : syracuseStep 698159 = 1047239) B1047239
theorem B4990825 : Blo 409770 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B927593 : Blo 409770 927593 := bstep (se 2 (by rfl) ⟨347847, by rfl⟩ : syracuseStep 927593 = 695695) B695695
theorem B4434211 : Blo 409770 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B3385637 : Blo 409770 3385637 := bstep (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) B634807
theorem B7907645 : Blo 409770 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B993647 : Blo 409770 993647 := bstep (se 1 (by rfl) ⟨745235, by rfl⟩ : syracuseStep 993647 = 1490471) B1490471
theorem B1059239 : Blo 409770 1059239 := bstep (se 1 (by rfl) ⟨794429, by rfl⟩ : syracuseStep 1059239 = 1588859) B1588859
theorem B1386935 : Blo 409770 1386935 := bstep (se 1 (by rfl) ⟨1040201, by rfl⟩ : syracuseStep 1386935 = 2080403) B2080403
theorem B1321427 : Blo 409770 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B928439 : Blo 409770 928439 := bstep (se 1 (by rfl) ⟨696329, by rfl⟩ : syracuseStep 928439 = 1392659) B1392659
theorem B928655 : Blo 409770 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B2075867 : Blo 409770 2075867 := bstep (se 1 (by rfl) ⟨1556900, by rfl⟩ : syracuseStep 2075867 = 3113801) B3113801
theorem B929375 : Blo 409770 929375 := bstep (se 1 (by rfl) ⟨697031, by rfl⟩ : syracuseStep 929375 = 1394063) B1394063
theorem B1322657 : Blo 409770 1322657 := bstep (se 2 (by rfl) ⟨495996, by rfl⟩ : syracuseStep 1322657 = 991993) B991993
theorem B929591 : Blo 409770 929591 := bstep (se 1 (by rfl) ⟨697193, by rfl⟩ : syracuseStep 929591 = 1394387) B1394387
theorem B1323017 : Blo 409770 1323017 := bstep (se 2 (by rfl) ⟨496131, by rfl⟩ : syracuseStep 1323017 = 992263) B992263
theorem B1323067 : Blo 409770 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B929897 : Blo 409770 929897 := bstep (se 2 (by rfl) ⟨348711, by rfl⟩ : syracuseStep 929897 = 697423) B697423
theorem B2077001 : Blo 409770 2077001 := bstep (se 2 (by rfl) ⟨778875, by rfl⟩ : syracuseStep 2077001 = 1557751) B1557751
theorem B1978951 : Blo 409770 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B930383 : Blo 409770 930383 := bstep (se 1 (by rfl) ⟨697787, by rfl⟩ : syracuseStep 930383 = 1395575) B1395575
theorem B6337201 : Blo 409770 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B1880759 : Blo 409770 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B930527 : Blo 409770 930527 := bstep (se 1 (by rfl) ⟨697895, by rfl⟩ : syracuseStep 930527 = 1395791) B1395791
theorem B930779 : Blo 409770 930779 := bstep (se 1 (by rfl) ⟨698084, by rfl⟩ : syracuseStep 930779 = 1396169) B1396169
theorem B930959 : Blo 409770 930959 := bstep (se 1 (by rfl) ⟨698219, by rfl⟩ : syracuseStep 930959 = 1396439) B1396439
theorem B4437287 : Blo 409770 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B1390013 : Blo 409770 1390013 := bstep (se 3 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 1390013 = 521255) B521255
theorem B2078297 : Blo 409770 2078297 := bstep (se 2 (by rfl) ⟨779361, by rfl⟩ : syracuseStep 2078297 = 1558723) B1558723
theorem B1783453 : Blo 409770 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B3159737 : Blo 409770 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B1390391 : Blo 409770 1390391 := bstep (se 1 (by rfl) ⟨1042793, by rfl⟩ : syracuseStep 1390391 = 2085587) B2085587
theorem B1750967 : Blo 409770 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B1390877 : Blo 409770 1390877 := bstep (se 3 (by rfl) ⟨260789, by rfl⟩ : syracuseStep 1390877 = 521579) B521579
theorem B440903 : Blo 409770 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B1489835 : Blo 409770 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B4734071 : Blo 409770 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B2112733 : Blo 409770 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B2112779 : Blo 409770 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B1391903 : Blo 409770 1391903 := bstep (se 1 (by rfl) ⟨1043927, by rfl⟩ : syracuseStep 1391903 = 2087855) B2087855
theorem B1621367 : Blo 409770 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B1588679 : Blo 409770 1588679 := bstep (se 1 (by rfl) ⟨1191509, by rfl⟩ : syracuseStep 1588679 = 2383019) B2383019
theorem B5914127 : Blo 409770 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B2342459 : Blo 409770 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B3522163 : Blo 409770 3522163 := bstep (se 1 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 3522163 = 5283245) B5283245
theorem B835535 : Blo 409770 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B3129353 : Blo 409770 3129353 := bstep (se 2 (by rfl) ⟨1173507, by rfl⟩ : syracuseStep 3129353 = 2347015) B2347015
theorem B409887 : Blo 409770 409887 := bstep (se 1 (by rfl) ⟨307415, by rfl⟩ : syracuseStep 409887 = 614831) B614831
theorem B409947 : Blo 409770 409947 := bstep (se 1 (by rfl) ⟨307460, by rfl⟩ : syracuseStep 409947 = 614921) B614921
theorem B409967 : Blo 409770 409967 := bstep (se 1 (by rfl) ⟨307475, by rfl⟩ : syracuseStep 409967 = 614951) B614951
theorem B410023 : Blo 409770 410023 := bstep (se 1 (by rfl) ⟨307517, by rfl⟩ : syracuseStep 410023 = 615035) B615035
theorem B410107 : Blo 409770 410107 := bstep (se 1 (by rfl) ⟨307580, by rfl⟩ : syracuseStep 410107 = 615161) B615161
theorem B410175 : Blo 409770 410175 := bstep (se 1 (by rfl) ⟨307631, by rfl⟩ : syracuseStep 410175 = 615263) B615263
theorem B410183 : Blo 409770 410183 := bstep (se 1 (by rfl) ⟨307637, by rfl⟩ : syracuseStep 410183 = 615275) B615275
theorem B967339 : Blo 409770 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B5259977 : Blo 409770 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B410335 : Blo 409770 410335 := bstep (se 1 (by rfl) ⟨307751, by rfl⟩ : syracuseStep 410335 = 615503) B615503
theorem B1983199 : Blo 409770 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B410415 : Blo 409770 410415 := bstep (se 1 (by rfl) ⟨307811, by rfl⟩ : syracuseStep 410415 = 615623) B615623
theorem B410523 : Blo 409770 410523 := bstep (se 1 (by rfl) ⟨307892, by rfl⟩ : syracuseStep 410523 = 615785) B615785
theorem B410575 : Blo 409770 410575 := bstep (se 1 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 410575 = 615863) B615863
theorem B410599 : Blo 409770 410599 := bstep (se 1 (by rfl) ⟨307949, by rfl⟩ : syracuseStep 410599 = 615899) B615899
theorem B1557737 : Blo 409770 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B410911 : Blo 409770 410911 := bstep (se 1 (by rfl) ⟨308183, by rfl⟩ : syracuseStep 410911 = 616367) B616367
theorem B7947557 : Blo 409770 7947557 := bstep (se 4 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 7947557 = 1490167) B1490167
theorem B410971 : Blo 409770 410971 := bstep (se 1 (by rfl) ⟨308228, by rfl⟩ : syracuseStep 410971 = 616457) B616457
theorem B410991 : Blo 409770 410991 := bstep (se 1 (by rfl) ⟨308243, by rfl⟩ : syracuseStep 410991 = 616487) B616487
theorem B411047 : Blo 409770 411047 := bstep (se 1 (by rfl) ⟨308285, by rfl⟩ : syracuseStep 411047 = 616571) B616571
theorem B411131 : Blo 409770 411131 := bstep (se 1 (by rfl) ⟨308348, by rfl⟩ : syracuseStep 411131 = 616697) B616697
theorem B411199 : Blo 409770 411199 := bstep (se 1 (by rfl) ⟨308399, by rfl⟩ : syracuseStep 411199 = 616799) B616799
theorem B411207 : Blo 409770 411207 := bstep (se 1 (by rfl) ⟨308405, by rfl⟩ : syracuseStep 411207 = 616811) B616811
theorem B1394333 : Blo 409770 1394333 := bstep (se 3 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 1394333 = 522875) B522875
theorem B17778365 : Blo 409770 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B411359 : Blo 409770 411359 := bstep (se 1 (by rfl) ⟨308519, by rfl⟩ : syracuseStep 411359 = 617039) B617039
theorem B411439 : Blo 409770 411439 := bstep (se 1 (by rfl) ⟨308579, by rfl⟩ : syracuseStep 411439 = 617159) B617159
theorem B3950441 : Blo 409770 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B411547 : Blo 409770 411547 := bstep (se 1 (by rfl) ⟨308660, by rfl⟩ : syracuseStep 411547 = 617321) B617321
theorem B411599 : Blo 409770 411599 := bstep (se 1 (by rfl) ⟨308699, by rfl⟩ : syracuseStep 411599 = 617399) B617399
theorem B411623 : Blo 409770 411623 := bstep (se 1 (by rfl) ⟨308717, by rfl⟩ : syracuseStep 411623 = 617435) B617435
theorem B1394873 : Blo 409770 1394873 := bstep (se 2 (by rfl) ⟨523077, by rfl⟩ : syracuseStep 1394873 = 1046155) B1046155
theorem B411935 : Blo 409770 411935 := bstep (se 1 (by rfl) ⟨308951, by rfl⟩ : syracuseStep 411935 = 617903) B617903
theorem B4245821 : Blo 409770 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B411995 : Blo 409770 411995 := bstep (se 1 (by rfl) ⟨308996, by rfl⟩ : syracuseStep 411995 = 617993) B617993
theorem B412015 : Blo 409770 412015 := bstep (se 1 (by rfl) ⟨309011, by rfl⟩ : syracuseStep 412015 = 618023) B618023
theorem B412071 : Blo 409770 412071 := bstep (se 1 (by rfl) ⟨309053, by rfl⟩ : syracuseStep 412071 = 618107) B618107
theorem B8604107 : Blo 409770 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B412155 : Blo 409770 412155 := bstep (se 1 (by rfl) ⟨309116, by rfl⟩ : syracuseStep 412155 = 618233) B618233
theorem B412223 : Blo 409770 412223 := bstep (se 1 (by rfl) ⟨309167, by rfl⟩ : syracuseStep 412223 = 618335) B618335
theorem B412231 : Blo 409770 412231 := bstep (se 1 (by rfl) ⟨309173, by rfl⟩ : syracuseStep 412231 = 618347) B618347
theorem B412383 : Blo 409770 412383 := bstep (se 1 (by rfl) ⟨309287, by rfl⟩ : syracuseStep 412383 = 618575) B618575
theorem B8014625 : Blo 409770 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B412463 : Blo 409770 412463 := bstep (se 1 (by rfl) ⟨309347, by rfl⟩ : syracuseStep 412463 = 618695) B618695
theorem B412571 : Blo 409770 412571 := bstep (se 1 (by rfl) ⟨309428, by rfl⟩ : syracuseStep 412571 = 618857) B618857
theorem B412623 : Blo 409770 412623 := bstep (se 1 (by rfl) ⟨309467, by rfl⟩ : syracuseStep 412623 = 618935) B618935
theorem B412647 : Blo 409770 412647 := bstep (se 1 (by rfl) ⟨309485, by rfl⟩ : syracuseStep 412647 = 618971) B618971
theorem B1985755 : Blo 409770 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B412959 : Blo 409770 412959 := bstep (se 1 (by rfl) ⟨309719, by rfl⟩ : syracuseStep 412959 = 619439) B619439
theorem B2116925 : Blo 409770 2116925 := bstep (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) B793847
theorem B413019 : Blo 409770 413019 := bstep (se 1 (by rfl) ⟨309764, by rfl⟩ : syracuseStep 413019 = 619529) B619529
theorem B413039 : Blo 409770 413039 := bstep (se 1 (by rfl) ⟨309779, by rfl⟩ : syracuseStep 413039 = 619559) B619559
theorem B413095 : Blo 409770 413095 := bstep (se 1 (by rfl) ⟨309821, by rfl⟩ : syracuseStep 413095 = 619643) B619643
theorem B413179 : Blo 409770 413179 := bstep (se 1 (by rfl) ⟨309884, by rfl⟩ : syracuseStep 413179 = 619769) B619769
theorem B413247 : Blo 409770 413247 := bstep (se 1 (by rfl) ⟨309935, by rfl⟩ : syracuseStep 413247 = 619871) B619871
theorem B413255 : Blo 409770 413255 := bstep (se 1 (by rfl) ⟨309941, by rfl⟩ : syracuseStep 413255 = 619883) B619883
theorem B1396385 : Blo 409770 1396385 := bstep (se 2 (by rfl) ⟨523644, by rfl⟩ : syracuseStep 1396385 = 1047289) B1047289
theorem B413407 : Blo 409770 413407 := bstep (se 1 (by rfl) ⟨310055, by rfl⟩ : syracuseStep 413407 = 620111) B620111
theorem B2084615 : Blo 409770 2084615 := bstep (se 1 (by rfl) ⟨1563461, by rfl⟩ : syracuseStep 2084615 = 3126923) B3126923
theorem B413487 : Blo 409770 413487 := bstep (se 1 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 413487 = 620231) B620231
theorem B4214585 : Blo 409770 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B3133241 : Blo 409770 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B413595 : Blo 409770 413595 := bstep (se 1 (by rfl) ⟨310196, by rfl⟩ : syracuseStep 413595 = 620393) B620393
theorem B413647 : Blo 409770 413647 := bstep (se 1 (by rfl) ⟨310235, by rfl⟩ : syracuseStep 413647 = 620471) B620471
theorem B413671 : Blo 409770 413671 := bstep (se 1 (by rfl) ⟨310253, by rfl⟩ : syracuseStep 413671 = 620507) B620507
theorem B2117657 : Blo 409770 2117657 := bstep (se 2 (by rfl) ⟨794121, by rfl⟩ : syracuseStep 2117657 = 1588243) B1588243
theorem B2642291 : Blo 409770 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B742223 : Blo 409770 742223 := bstep (se 1 (by rfl) ⟨556667, by rfl⟩ : syracuseStep 742223 = 1113335) B1113335
theorem B1987523 : Blo 409770 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B5298007 : Blo 409770 5298007 := bstep (se 1 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 5298007 = 7947011) B7947011
theorem B743375 : Blo 409770 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B1759427 : Blo 409770 1759427 := bstep (se 1 (by rfl) ⟨1319570, by rfl⟩ : syracuseStep 1759427 = 2639141) B2639141
theorem B1038683 : Blo 409770 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B1038703 : Blo 409770 1038703 := bstep (se 1 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 1038703 = 1558055) B1558055
theorem B2087531 : Blo 409770 2087531 := bstep (se 1 (by rfl) ⟨1565648, by rfl⟩ : syracuseStep 2087531 = 3131297) B3131297
theorem B10050155 : Blo 409770 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B7527107 : Blo 409770 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B1760125 : Blo 409770 1760125 := bstep (se 3 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 1760125 = 660047) B660047
theorem B1039351 : Blo 409770 1039351 := bstep (se 1 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 1039351 = 1559027) B1559027
theorem B2088017 : Blo 409770 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B3169469 : Blo 409770 3169469 := bstep (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) B1188551
theorem B1039655 : Blo 409770 1039655 := bstep (se 1 (by rfl) ⟨779741, by rfl⟩ : syracuseStep 1039655 = 1559483) B1559483
theorem B941831 : Blo 409770 941831 := bstep (se 1 (by rfl) ⟨706373, by rfl⟩ : syracuseStep 941831 = 1412747) B1412747
theorem B778025 : Blo 409770 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B2350889 : Blo 409770 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B3334355 : Blo 409770 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B614747 : Blo 409770 614747 := bstep (se 1 (by rfl) ⟨461060, by rfl⟩ : syracuseStep 614747 = 922121) B922121
theorem B778663 : Blo 409770 778663 := bstep (se 1 (by rfl) ⟨583997, by rfl⟩ : syracuseStep 778663 = 1167995) B1167995
theorem B778747 : Blo 409770 778747 := bstep (se 1 (by rfl) ⟨584060, by rfl⟩ : syracuseStep 778747 = 1168121) B1168121
theorem B614975 : Blo 409770 614975 := bstep (se 1 (by rfl) ⟨461231, by rfl⟩ : syracuseStep 614975 = 922463) B922463
theorem B4743851 : Blo 409770 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B615095 : Blo 409770 615095 := bstep (se 1 (by rfl) ⟨461321, by rfl⟩ : syracuseStep 615095 = 922643) B922643
theorem B1041295 : Blo 409770 1041295 := bstep (se 1 (by rfl) ⟨780971, by rfl⟩ : syracuseStep 1041295 = 1561943) B1561943
theorem B615323 : Blo 409770 615323 := bstep (se 1 (by rfl) ⟨461492, by rfl⟩ : syracuseStep 615323 = 922985) B922985
theorem B877483 : Blo 409770 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B779483 : Blo 409770 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B615719 : Blo 409770 615719 := bstep (se 1 (by rfl) ⟨461789, by rfl⟩ : syracuseStep 615719 = 923579) B923579
theorem B1041761 : Blo 409770 1041761 := bstep (se 2 (by rfl) ⟨390660, by rfl⟩ : syracuseStep 1041761 = 781321) B781321
theorem B615803 : Blo 409770 615803 := bstep (se 1 (by rfl) ⟨461852, by rfl⟩ : syracuseStep 615803 = 923705) B923705
theorem B779719 : Blo 409770 779719 := bstep (se 1 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 779719 = 1169579) B1169579
theorem B615929 : Blo 409770 615929 := bstep (se 2 (by rfl) ⟨230973, by rfl⟩ : syracuseStep 615929 = 461947) B461947
theorem B616031 : Blo 409770 616031 := bstep (se 1 (by rfl) ⟨462023, by rfl⟩ : syracuseStep 616031 = 924047) B924047
theorem B1042217 : Blo 409770 1042217 := bstep (se 2 (by rfl) ⟨390831, by rfl⟩ : syracuseStep 1042217 = 781663) B781663
theorem B616247 : Blo 409770 616247 := bstep (se 1 (by rfl) ⟨462185, by rfl⟩ : syracuseStep 616247 = 924371) B924371
theorem B20309849 : Blo 409770 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B17885285 : Blo 409770 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B616553 : Blo 409770 616553 := bstep (se 2 (by rfl) ⟨231207, by rfl⟩ : syracuseStep 616553 = 462415) B462415
theorem B1566985 : Blo 409770 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B616871 : Blo 409770 616871 := bstep (se 1 (by rfl) ⟨462653, by rfl⟩ : syracuseStep 616871 = 925307) B925307
theorem B4680179 : Blo 409770 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B616955 : Blo 409770 616955 := bstep (se 1 (by rfl) ⟨462716, by rfl⟩ : syracuseStep 616955 = 925433) B925433
theorem B22932013 : Blo 409770 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B518719 : Blo 409770 518719 := bstep (se 1 (by rfl) ⟨389039, by rfl⟩ : syracuseStep 518719 = 778079) B778079
theorem B879167 : Blo 409770 879167 := bstep (se 1 (by rfl) ⟨659375, by rfl⟩ : syracuseStep 879167 = 1318751) B1318751
theorem B617081 : Blo 409770 617081 := bstep (se 2 (by rfl) ⟨231405, by rfl⟩ : syracuseStep 617081 = 462811) B462811
theorem B2648699 : Blo 409770 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B617135 : Blo 409770 617135 := bstep (se 1 (by rfl) ⟨462851, by rfl⟩ : syracuseStep 617135 = 925703) B925703
theorem B617183 : Blo 409770 617183 := bstep (se 1 (by rfl) ⟨462887, by rfl⟩ : syracuseStep 617183 = 925775) B925775
theorem B1043219 : Blo 409770 1043219 := bstep (se 1 (by rfl) ⟨782414, by rfl⟩ : syracuseStep 1043219 = 1564829) B1564829
theorem B617447 : Blo 409770 617447 := bstep (se 1 (by rfl) ⟨463085, by rfl⟩ : syracuseStep 617447 = 926171) B926171
theorem B1403891 : Blo 409770 1403891 := bstep (se 1 (by rfl) ⟨1052918, by rfl⟩ : syracuseStep 1403891 = 2105837) B2105837
theorem B1043675 : Blo 409770 1043675 := bstep (se 1 (by rfl) ⟨782756, by rfl⟩ : syracuseStep 1043675 = 1565513) B1565513
theorem B617705 : Blo 409770 617705 := bstep (se 2 (by rfl) ⟨231639, by rfl⟩ : syracuseStep 617705 = 463279) B463279
theorem B1043705 : Blo 409770 1043705 := bstep (se 2 (by rfl) ⟨391389, by rfl⟩ : syracuseStep 1043705 = 782779) B782779
theorem B617759 : Blo 409770 617759 := bstep (se 1 (by rfl) ⟨463319, by rfl⟩ : syracuseStep 617759 = 926639) B926639
theorem B519463 : Blo 409770 519463 := bstep (se 1 (by rfl) ⟨389597, by rfl⟩ : syracuseStep 519463 = 779195) B779195
theorem B617927 : Blo 409770 617927 := bstep (se 1 (by rfl) ⟨463445, by rfl⟩ : syracuseStep 617927 = 926891) B926891
theorem B1109497 : Blo 409770 1109497 := bstep (se 2 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 1109497 = 832123) B832123
theorem B2092553 : Blo 409770 2092553 := bstep (se 2 (by rfl) ⟨784707, by rfl⟩ : syracuseStep 2092553 = 1569415) B1569415
theorem B3501629 : Blo 409770 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B519787 : Blo 409770 519787 := bstep (se 1 (by rfl) ⟨389840, by rfl⟩ : syracuseStep 519787 = 779681) B779681
theorem B618281 : Blo 409770 618281 := bstep (se 2 (by rfl) ⟨231855, by rfl⟩ : syracuseStep 618281 = 463711) B463711
theorem B618287 : Blo 409770 618287 := bstep (se 1 (by rfl) ⟨463715, by rfl⟩ : syracuseStep 618287 = 927431) B927431
theorem B520015 : Blo 409770 520015 := bstep (se 1 (by rfl) ⟨390011, by rfl⟩ : syracuseStep 520015 = 780023) B780023
theorem B1044353 : Blo 409770 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B3960899 : Blo 409770 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B618761 : Blo 409770 618761 := bstep (se 2 (by rfl) ⟨232035, by rfl⟩ : syracuseStep 618761 = 464071) B464071
theorem B880969 : Blo 409770 880969 := bstep (se 2 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 880969 = 660727) B660727
theorem B1044809 : Blo 409770 1044809 := bstep (se 2 (by rfl) ⟨391803, by rfl⟩ : syracuseStep 1044809 = 783607) B783607
theorem B4223339 : Blo 409770 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B618863 : Blo 409770 618863 := bstep (se 1 (by rfl) ⟨464147, by rfl⟩ : syracuseStep 618863 = 928295) B928295
theorem B1176083 : Blo 409770 1176083 := bstep (se 1 (by rfl) ⟨882062, by rfl⟩ : syracuseStep 1176083 = 1764125) B1764125
theorem B2355763 : Blo 409770 2355763 := bstep (se 1 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 2355763 = 3533645) B3533645
theorem B619079 : Blo 409770 619079 := bstep (se 1 (by rfl) ⟨464309, by rfl⟩ : syracuseStep 619079 = 928619) B928619
theorem B619115 : Blo 409770 619115 := bstep (se 1 (by rfl) ⟨464336, by rfl⟩ : syracuseStep 619115 = 928673) B928673
theorem B1569401 : Blo 409770 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B1045163 : Blo 409770 1045163 := bstep (se 1 (by rfl) ⟨783872, by rfl⟩ : syracuseStep 1045163 = 1567745) B1567745
theorem B881327 : Blo 409770 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B14480117 : Blo 409770 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B619343 : Blo 409770 619343 := bstep (se 1 (by rfl) ⟨464507, by rfl⟩ : syracuseStep 619343 = 929015) B929015
theorem B2847869 : Blo 409770 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B1111259 : Blo 409770 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B619739 : Blo 409770 619739 := bstep (se 1 (by rfl) ⟨464804, by rfl⟩ : syracuseStep 619739 = 929609) B929609
theorem B619913 : Blo 409770 619913 := bstep (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) B464935
theorem B2094497 : Blo 409770 2094497 := bstep (se 2 (by rfl) ⟨785436, by rfl⟩ : syracuseStep 2094497 = 1570873) B1570873
theorem B521903 : Blo 409770 521903 := bstep (se 1 (by rfl) ⟨391427, by rfl⟩ : syracuseStep 521903 = 782855) B782855
theorem B620267 : Blo 409770 620267 := bstep (se 1 (by rfl) ⟨465200, by rfl⟩ : syracuseStep 620267 = 930401) B930401
theorem B5928889 : Blo 409770 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B1046479 : Blo 409770 1046479 := bstep (se 1 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 1046479 = 1569719) B1569719
theorem B620495 : Blo 409770 620495 := bstep (se 1 (by rfl) ⟨465371, by rfl⟩ : syracuseStep 620495 = 930743) B930743
theorem B522607 : Blo 409770 522607 := bstep (se 1 (by rfl) ⟨391955, by rfl⟩ : syracuseStep 522607 = 783911) B783911
theorem B6355381 : Blo 409770 6355381 := bstep (se 5 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 6355381 = 595817) B595817
theorem B3013519 : Blo 409770 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B1112987 : Blo 409770 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B883703 : Blo 409770 883703 := bstep (se 1 (by rfl) ⟨662777, by rfl⟩ : syracuseStep 883703 = 1325555) B1325555
theorem B1604827 : Blo 409770 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B1670519 : Blo 409770 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B30080393 : Blo 409770 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B1113593 : Blo 409770 1113593 := bstep (se 2 (by rfl) ⟨417597, by rfl⟩ : syracuseStep 1113593 = 835195) B835195
theorem B3506651 : Blo 409770 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B9011897 : Blo 409770 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B5736071 : Blo 409770 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B12650269 : Blo 409770 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B5343083 : Blo 409770 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B1411283 : Blo 409770 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B6654433 : Blo 409770 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B1411771 : Blo 409770 1411771 := bstep (se 1 (by rfl) ⟨1058828, by rfl⟩ : syracuseStep 1411771 = 2117657) B2117657
theorem B461659 : Blo 409770 461659 := bstep (se 1 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 461659 = 692489) B692489
theorem B494815 : Blo 409770 494815 := bstep (se 1 (by rfl) ⟨371111, by rfl⟩ : syracuseStep 494815 = 742223) B742223
theorem B30576017 : Blo 409770 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B691625 : Blo 409770 691625 := bstep (se 2 (by rfl) ⟨259359, by rfl⟩ : syracuseStep 691625 = 518719) B518719
theorem B659087 : Blo 409770 659087 := bstep (se 1 (by rfl) ⟨494315, by rfl⟩ : syracuseStep 659087 = 988631) B988631
theorem B659119 : Blo 409770 659119 := bstep (se 1 (by rfl) ⟨494339, by rfl⟩ : syracuseStep 659119 = 988679) B988679
theorem B462631 : Blo 409770 462631 := bstep (se 1 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 462631 = 693947) B693947
theorem B692455 : Blo 409770 692455 := bstep (se 1 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 692455 = 1038683) B1038683
theorem B692617 : Blo 409770 692617 := bstep (se 2 (by rfl) ⟨259731, by rfl⟩ : syracuseStep 692617 = 519463) B519463
theorem B1479329 : Blo 409770 1479329 := bstep (se 2 (by rfl) ⟨554748, by rfl⟩ : syracuseStep 1479329 = 1109497) B1109497
theorem B922409 : Blo 409770 922409 := bstep (se 2 (by rfl) ⟨345903, by rfl⟩ : syracuseStep 922409 = 691807) B691807
theorem B693049 : Blo 409770 693049 := bstep (se 2 (by rfl) ⟨259893, by rfl⟩ : syracuseStep 693049 = 519787) B519787
theorem B693103 : Blo 409770 693103 := bstep (se 1 (by rfl) ⟨519827, by rfl⟩ : syracuseStep 693103 = 1039655) B1039655
theorem B463783 : Blo 409770 463783 := bstep (se 1 (by rfl) ⟨347837, by rfl⟩ : syracuseStep 463783 = 695675) B695675
theorem B922679 : Blo 409770 922679 := bstep (se 1 (by rfl) ⟨692009, by rfl⟩ : syracuseStep 922679 = 1384019) B1384019
theorem B922697 : Blo 409770 922697 := bstep (se 2 (by rfl) ⟨346011, by rfl⟩ : syracuseStep 922697 = 692023) B692023
theorem B693353 : Blo 409770 693353 := bstep (se 2 (by rfl) ⟨260007, by rfl⟩ : syracuseStep 693353 = 520015) B520015
theorem B627887 : Blo 409770 627887 := bstep (se 1 (by rfl) ⟨470915, by rfl⟩ : syracuseStep 627887 = 941831) B941831
theorem B10589453 : Blo 409770 10589453 := bstep (se 3 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 10589453 = 3971045) B3971045
theorem B1316969 : Blo 409770 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B1317019 : Blo 409770 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B694507 : Blo 409770 694507 := bstep (se 1 (by rfl) ⟨520880, by rfl⟩ : syracuseStep 694507 = 1041761) B1041761
theorem B694811 : Blo 409770 694811 := bstep (se 1 (by rfl) ⟨521108, by rfl⟩ : syracuseStep 694811 = 1042217) B1042217
theorem B465439 : Blo 409770 465439 := bstep (se 1 (by rfl) ⟨349079, by rfl⟩ : syracuseStep 465439 = 698159) B698159
theorem B13539899 : Blo 409770 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B662431 : Blo 409770 662431 := bstep (se 1 (by rfl) ⟨496823, by rfl⟩ : syracuseStep 662431 = 993647) B993647
theorem B924623 : Blo 409770 924623 := bstep (se 1 (by rfl) ⟨693467, by rfl⟩ : syracuseStep 924623 = 1386935) B1386935
theorem B924641 : Blo 409770 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B3120119 : Blo 409770 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B924713 : Blo 409770 924713 := bstep (se 2 (by rfl) ⟨346767, by rfl⟩ : syracuseStep 924713 = 693535) B693535
theorem B1055873 : Blo 409770 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B695479 : Blo 409770 695479 := bstep (se 1 (by rfl) ⟨521609, by rfl⟩ : syracuseStep 695479 = 1043219) B1043219
theorem B4988297 : Blo 409770 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B1383911 : Blo 409770 1383911 := bstep (se 1 (by rfl) ⟨1037933, by rfl⟩ : syracuseStep 1383911 = 2075867) B2075867
theorem B695783 : Blo 409770 695783 := bstep (se 1 (by rfl) ⟨521837, by rfl⟩ : syracuseStep 695783 = 1043675) B1043675
theorem B695803 : Blo 409770 695803 := bstep (se 1 (by rfl) ⟨521852, by rfl⟩ : syracuseStep 695803 = 1043705) B1043705
theorem B2334419 : Blo 409770 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B7905185 : Blo 409770 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B696235 : Blo 409770 696235 := bstep (se 1 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 696235 = 1044353) B1044353
theorem B1384667 : Blo 409770 1384667 := bstep (se 1 (by rfl) ⟨1038500, by rfl⟩ : syracuseStep 1384667 = 2077001) B2077001
theorem B696539 : Blo 409770 696539 := bstep (se 1 (by rfl) ⟨522404, by rfl⟩ : syracuseStep 696539 = 1044809) B1044809
theorem B696775 : Blo 409770 696775 := bstep (se 1 (by rfl) ⟨522581, by rfl⟩ : syracuseStep 696775 = 1045163) B1045163
theorem B1253839 : Blo 409770 1253839 := bstep (se 1 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 1253839 = 1880759) B1880759
theorem B1384937 : Blo 409770 1384937 := bstep (se 2 (by rfl) ⟨519351, by rfl⟩ : syracuseStep 1384937 = 1038703) B1038703
theorem B696809 : Blo 409770 696809 := bstep (se 2 (by rfl) ⟨261303, by rfl⟩ : syracuseStep 696809 = 522607) B522607
theorem B2958191 : Blo 409770 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B926675 : Blo 409770 926675 := bstep (se 1 (by rfl) ⟨695006, by rfl⟩ : syracuseStep 926675 = 1390013) B1390013
theorem B1385531 : Blo 409770 1385531 := bstep (se 1 (by rfl) ⟨1039148, by rfl⟩ : syracuseStep 1385531 = 2078297) B2078297
theorem B2106491 : Blo 409770 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B926927 : Blo 409770 926927 := bstep (se 1 (by rfl) ⟨695195, by rfl⟩ : syracuseStep 926927 = 1390391) B1390391
theorem B1385801 : Blo 409770 1385801 := bstep (se 2 (by rfl) ⟨519675, by rfl⟩ : syracuseStep 1385801 = 1039351) B1039351
theorem B927251 : Blo 409770 927251 := bstep (se 1 (by rfl) ⟨695438, by rfl⟩ : syracuseStep 927251 = 1390877) B1390877
theorem B2139769 : Blo 409770 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B993223 : Blo 409770 993223 := bstep (se 1 (by rfl) ⟨744917, by rfl⟩ : syracuseStep 993223 = 1489835) B1489835
theorem B3156047 : Blo 409770 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B2074733 : Blo 409770 2074733 := bstep (se 3 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 2074733 = 778025) B778025
theorem B4696217 : Blo 409770 4696217 := bstep (se 2 (by rfl) ⟨1761081, by rfl⟩ : syracuseStep 4696217 = 3522163) B3522163
theorem B927935 : Blo 409770 927935 := bstep (se 1 (by rfl) ⟨695951, by rfl⟩ : syracuseStep 927935 = 1391903) B1391903
theorem B1059119 : Blo 409770 1059119 := bstep (se 1 (by rfl) ⟨794339, by rfl⟩ : syracuseStep 1059119 = 1588679) B1588679
theorem B3942751 : Blo 409770 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B1485857 : Blo 409770 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B928889 : Blo 409770 928889 := bstep (se 2 (by rfl) ⟨348333, by rfl⟩ : syracuseStep 928889 = 696667) B696667
theorem B1289785 : Blo 409770 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B929555 : Blo 409770 929555 := bstep (se 1 (by rfl) ⟨697166, by rfl⟩ : syracuseStep 929555 = 1394333) B1394333
theorem B1388393 : Blo 409770 1388393 := bstep (se 2 (by rfl) ⟨520647, by rfl⟩ : syracuseStep 1388393 = 1041295) B1041295
theorem B5025665 : Blo 409770 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B2633627 : Blo 409770 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B929915 : Blo 409770 929915 := bstep (se 1 (by rfl) ⟨697436, by rfl⟩ : syracuseStep 929915 = 1394873) B1394873
theorem B2830547 : Blo 409770 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B930185 : Blo 409770 930185 := bstep (se 2 (by rfl) ⟨348819, by rfl⟩ : syracuseStep 930185 = 697639) B697639
theorem B2339543 : Blo 409770 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B1192745 : Blo 409770 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B5485391 : Blo 409770 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B930923 : Blo 409770 930923 := bstep (se 1 (by rfl) ⟨698192, by rfl⟩ : syracuseStep 930923 = 1396385) B1396385
theorem B2077811 : Blo 409770 2077811 := bstep (se 1 (by rfl) ⟨1558358, by rfl⟩ : syracuseStep 2077811 = 3116717) B3116717
theorem B1389743 : Blo 409770 1389743 := bstep (se 1 (by rfl) ⟨1042307, by rfl⟩ : syracuseStep 1389743 = 2084615) B2084615
theorem B2340251 : Blo 409770 2340251 := bstep (se 1 (by rfl) ⟨1755188, by rfl⟩ : syracuseStep 2340251 = 3510377) B3510377
theorem B5912281 : Blo 409770 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B2078459 : Blo 409770 2078459 := bstep (se 1 (by rfl) ⟨1558844, by rfl⟩ : syracuseStep 2078459 = 3117689) B3117689
theorem B2078621 : Blo 409770 2078621 := bstep (se 3 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 2078621 = 779483) B779483
theorem B1488797 : Blo 409770 1488797 := bstep (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) B558299
theorem B1325015 : Blo 409770 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B1751003 : Blo 409770 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B2013443 : Blo 409770 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B1489259 : Blo 409770 1489259 := bstep (se 1 (by rfl) ⟨1116944, by rfl⟩ : syracuseStep 1489259 = 2233889) B2233889
theorem B2079431 : Blo 409770 2079431 := bstep (se 1 (by rfl) ⟨1559573, by rfl⟩ : syracuseStep 2079431 = 3119147) B3119147
theorem B3849257 : Blo 409770 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1391687 : Blo 409770 1391687 := bstep (se 1 (by rfl) ⟨1043765, by rfl⟩ : syracuseStep 1391687 = 2087531) B2087531
theorem B6700103 : Blo 409770 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B1391741 : Blo 409770 1391741 := bstep (se 3 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 1391741 = 521903) B521903
theorem B1392011 : Blo 409770 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B2112979 : Blo 409770 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B1556111 : Blo 409770 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1982333 : Blo 409770 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B409831 : Blo 409770 409831 := bstep (se 1 (by rfl) ⟨307373, by rfl⟩ : syracuseStep 409831 = 614747) B614747
theorem B409983 : Blo 409770 409983 := bstep (se 1 (by rfl) ⟨307487, by rfl⟩ : syracuseStep 409983 = 614975) B614975
theorem B410063 : Blo 409770 410063 := bstep (se 1 (by rfl) ⟨307547, by rfl⟩ : syracuseStep 410063 = 615095) B615095
theorem B410215 : Blo 409770 410215 := bstep (se 1 (by rfl) ⟨307661, by rfl⟩ : syracuseStep 410215 = 615323) B615323
theorem B2343599 : Blo 409770 2343599 := bstep (se 1 (by rfl) ⟨1757699, by rfl⟩ : syracuseStep 2343599 = 3515399) B3515399
theorem B2638601 : Blo 409770 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B410479 : Blo 409770 410479 := bstep (se 1 (by rfl) ⟨307859, by rfl⟩ : syracuseStep 410479 = 615719) B615719
theorem B410535 : Blo 409770 410535 := bstep (se 1 (by rfl) ⟨307901, by rfl⟩ : syracuseStep 410535 = 615803) B615803
theorem B410619 : Blo 409770 410619 := bstep (se 1 (by rfl) ⟨307964, by rfl⟩ : syracuseStep 410619 = 615929) B615929
theorem B410687 : Blo 409770 410687 := bstep (se 1 (by rfl) ⟨308015, by rfl⟩ : syracuseStep 410687 = 616031) B616031
theorem B410831 : Blo 409770 410831 := bstep (se 1 (by rfl) ⟨308123, by rfl⟩ : syracuseStep 410831 = 616247) B616247
theorem B411035 : Blo 409770 411035 := bstep (se 1 (by rfl) ⟨308276, by rfl⟩ : syracuseStep 411035 = 616553) B616553
theorem B411247 : Blo 409770 411247 := bstep (se 1 (by rfl) ⟨308435, by rfl⟩ : syracuseStep 411247 = 616871) B616871
theorem B706159 : Blo 409770 706159 := bstep (se 1 (by rfl) ⟨529619, by rfl⟩ : syracuseStep 706159 = 1059239) B1059239
theorem B411303 : Blo 409770 411303 := bstep (se 1 (by rfl) ⟨308477, by rfl⟩ : syracuseStep 411303 = 616955) B616955
theorem B411387 : Blo 409770 411387 := bstep (se 1 (by rfl) ⟨308540, by rfl⟩ : syracuseStep 411387 = 617081) B617081
theorem B411423 : Blo 409770 411423 := bstep (se 1 (by rfl) ⟨308567, by rfl⟩ : syracuseStep 411423 = 617135) B617135
theorem B411455 : Blo 409770 411455 := bstep (se 1 (by rfl) ⟨308591, by rfl⟩ : syracuseStep 411455 = 617183) B617183
theorem B20072285 : Blo 409770 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B411631 : Blo 409770 411631 := bstep (se 1 (by rfl) ⟨308723, by rfl⟩ : syracuseStep 411631 = 617447) B617447
theorem B935927 : Blo 409770 935927 := bstep (se 1 (by rfl) ⟨701945, by rfl⟩ : syracuseStep 935927 = 1403891) B1403891
theorem B411803 : Blo 409770 411803 := bstep (se 1 (by rfl) ⟨308852, by rfl⟩ : syracuseStep 411803 = 617705) B617705
theorem B411839 : Blo 409770 411839 := bstep (se 1 (by rfl) ⟨308879, by rfl⟩ : syracuseStep 411839 = 617759) B617759
theorem B2377937 : Blo 409770 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B411951 : Blo 409770 411951 := bstep (se 1 (by rfl) ⟨308963, by rfl⟩ : syracuseStep 411951 = 617927) B617927
theorem B1395035 : Blo 409770 1395035 := bstep (se 1 (by rfl) ⟨1046276, by rfl⟩ : syracuseStep 1395035 = 2092553) B2092553
theorem B2967965 : Blo 409770 2967965 := bstep (se 3 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 2967965 = 1112987) B1112987
theorem B7064009 : Blo 409770 7064009 := bstep (se 2 (by rfl) ⟨2649003, by rfl⟩ : syracuseStep 7064009 = 5298007) B5298007
theorem B412187 : Blo 409770 412187 := bstep (se 1 (by rfl) ⟨309140, by rfl⟩ : syracuseStep 412187 = 618281) B618281
theorem B412191 : Blo 409770 412191 := bstep (se 1 (by rfl) ⟨309143, by rfl⟩ : syracuseStep 412191 = 618287) B618287
theorem B1395305 : Blo 409770 1395305 := bstep (se 2 (by rfl) ⟨523239, by rfl⟩ : syracuseStep 1395305 = 1046479) B1046479
theorem B2640599 : Blo 409770 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B412507 : Blo 409770 412507 := bstep (se 1 (by rfl) ⟨309380, by rfl⟩ : syracuseStep 412507 = 618761) B618761
theorem B412575 : Blo 409770 412575 := bstep (se 1 (by rfl) ⟨309431, by rfl⟩ : syracuseStep 412575 = 618863) B618863
theorem B412719 : Blo 409770 412719 := bstep (se 1 (by rfl) ⟨309539, by rfl⟩ : syracuseStep 412719 = 619079) B619079
theorem B412743 : Blo 409770 412743 := bstep (se 1 (by rfl) ⟨309557, by rfl⟩ : syracuseStep 412743 = 619115) B619115
theorem B9653411 : Blo 409770 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B412895 : Blo 409770 412895 := bstep (se 1 (by rfl) ⟨309671, by rfl⟩ : syracuseStep 412895 = 619343) B619343
theorem B8473841 : Blo 409770 8473841 := bstep (se 2 (by rfl) ⟨3177690, by rfl⟩ : syracuseStep 8473841 = 6355381) B6355381
theorem B740839 : Blo 409770 740839 := bstep (se 1 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 740839 = 1111259) B1111259
theorem B413159 : Blo 409770 413159 := bstep (se 1 (by rfl) ⟨309869, by rfl⟩ : syracuseStep 413159 = 619739) B619739
theorem B413275 : Blo 409770 413275 := bstep (se 1 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 413275 = 619913) B619913
theorem B1396331 : Blo 409770 1396331 := bstep (se 1 (by rfl) ⟨1047248, by rfl⟩ : syracuseStep 1396331 = 2094497) B2094497
theorem B1756829 : Blo 409770 1756829 := bstep (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) B658811
theorem B413511 : Blo 409770 413511 := bstep (se 1 (by rfl) ⟨310133, by rfl⟩ : syracuseStep 413511 = 620267) B620267
theorem B2346833 : Blo 409770 2346833 := bstep (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) B1760125
theorem B4018025 : Blo 409770 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B1167311 : Blo 409770 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B413663 : Blo 409770 413663 := bstep (se 1 (by rfl) ⟨310247, by rfl⟩ : syracuseStep 413663 = 620495) B620495
theorem B2969581 : Blo 409770 2969581 := bstep (se 3 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 2969581 = 1113593) B1113593
theorem B2642341 : Blo 409770 2642341 := bstep (se 4 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 2642341 = 495439) B495439
theorem B4510505 : Blo 409770 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B1561639 : Blo 409770 1561639 := bstep (se 1 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 1561639 = 2342459) B2342459
theorem B2086235 : Blo 409770 2086235 := bstep (se 1 (by rfl) ⟨1564676, by rfl⟩ : syracuseStep 2086235 = 3129353) B3129353
theorem B1038217 : Blo 409770 1038217 := bstep (se 2 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 1038217 = 778663) B778663
theorem B1038329 : Blo 409770 1038329 := bstep (se 2 (by rfl) ⟨389373, by rfl⟩ : syracuseStep 1038329 = 778747) B778747
theorem B1038491 : Blo 409770 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B5298371 : Blo 409770 5298371 := bstep (se 1 (by rfl) ⟨3973778, by rfl⟩ : syracuseStep 5298371 = 7947557) B7947557
theorem B2644265 : Blo 409770 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B11852243 : Blo 409770 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B1169977 : Blo 409770 1169977 := bstep (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) B877483
theorem B2350205 : Blo 409770 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B1039625 : Blo 409770 1039625 := bstep (se 2 (by rfl) ⟨389859, by rfl⟩ : syracuseStep 1039625 = 779719) B779719
theorem B745337 : Blo 409770 745337 := bstep (se 2 (by rfl) ⟨279501, by rfl⟩ : syracuseStep 745337 = 559003) B559003
theorem B2809723 : Blo 409770 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B2088827 : Blo 409770 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B2121767 : Blo 409770 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B1761527 : Blo 409770 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B614687 : Blo 409770 614687 := bstep (se 1 (by rfl) ⟨461015, by rfl⟩ : syracuseStep 614687 = 922031) B922031
theorem B614711 : Blo 409770 614711 := bstep (se 1 (by rfl) ⟨461033, by rfl⟩ : syracuseStep 614711 = 922067) B922067
theorem B2089313 : Blo 409770 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B2646391 : Blo 409770 2646391 := bstep (se 1 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 2646391 = 3969587) B3969587
theorem B614783 : Blo 409770 614783 := bstep (se 1 (by rfl) ⟨461087, by rfl⟩ : syracuseStep 614783 = 922175) B922175
theorem B614855 : Blo 409770 614855 := bstep (se 1 (by rfl) ⟨461141, by rfl⟩ : syracuseStep 614855 = 922283) B922283
theorem B21652103 : Blo 409770 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B1073899 : Blo 409770 1073899 := bstep (se 1 (by rfl) ⟨805424, by rfl⟩ : syracuseStep 1073899 = 1610849) B1610849
theorem B877321 : Blo 409770 877321 := bstep (se 2 (by rfl) ⟨328995, by rfl⟩ : syracuseStep 877321 = 657991) B657991
theorem B615209 : Blo 409770 615209 := bstep (se 2 (by rfl) ⟨230703, by rfl⟩ : syracuseStep 615209 = 461407) B461407
theorem B615215 : Blo 409770 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B40035221 : Blo 409770 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B615335 : Blo 409770 615335 := bstep (se 1 (by rfl) ⟨461501, by rfl⟩ : syracuseStep 615335 = 923003) B923003
theorem B615419 : Blo 409770 615419 := bstep (se 1 (by rfl) ⟨461564, by rfl⟩ : syracuseStep 615419 = 923129) B923129
theorem B615479 : Blo 409770 615479 := bstep (se 1 (by rfl) ⟨461609, by rfl⟩ : syracuseStep 615479 = 923219) B923219
theorem B615599 : Blo 409770 615599 := bstep (se 1 (by rfl) ⟨461699, by rfl⟩ : syracuseStep 615599 = 923399) B923399
theorem B1172951 : Blo 409770 1172951 := bstep (se 1 (by rfl) ⟨879713, by rfl⟩ : syracuseStep 1172951 = 1759427) B1759427
theorem B616007 : Blo 409770 616007 := bstep (se 1 (by rfl) ⟨462005, by rfl⟩ : syracuseStep 616007 = 924011) B924011
theorem B2647673 : Blo 409770 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B616103 : Blo 409770 616103 := bstep (se 1 (by rfl) ⟨462077, by rfl⟩ : syracuseStep 616103 = 924155) B924155
theorem B878303 : Blo 409770 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B616187 : Blo 409770 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B616223 : Blo 409770 616223 := bstep (se 1 (by rfl) ⟨462167, by rfl⟩ : syracuseStep 616223 = 924335) B924335
theorem B616271 : Blo 409770 616271 := bstep (se 1 (by rfl) ⟨462203, by rfl⟩ : syracuseStep 616271 = 924407) B924407
theorem B616391 : Blo 409770 616391 := bstep (se 1 (by rfl) ⟨462293, by rfl⟩ : syracuseStep 616391 = 924587) B924587
theorem B616745 : Blo 409770 616745 := bstep (se 2 (by rfl) ⟨231279, by rfl⟩ : syracuseStep 616745 = 462559) B462559
theorem B616751 : Blo 409770 616751 := bstep (se 1 (by rfl) ⟨462563, by rfl⟩ : syracuseStep 616751 = 925127) B925127
theorem B1567259 : Blo 409770 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B616991 : Blo 409770 616991 := bstep (se 1 (by rfl) ⟨462743, by rfl⟩ : syracuseStep 616991 = 925487) B925487
theorem B2976439 : Blo 409770 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B1764089 : Blo 409770 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B2222903 : Blo 409770 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B617375 : Blo 409770 617375 := bstep (se 1 (by rfl) ⟨463031, by rfl⟩ : syracuseStep 617375 = 926063) B926063
theorem B617423 : Blo 409770 617423 := bstep (se 1 (by rfl) ⟨463067, by rfl⟩ : syracuseStep 617423 = 926135) B926135
theorem B617513 : Blo 409770 617513 := bstep (se 2 (by rfl) ⟨231567, by rfl⟩ : syracuseStep 617513 = 463135) B463135
theorem B617519 : Blo 409770 617519 := bstep (se 1 (by rfl) ⟨463139, by rfl⟩ : syracuseStep 617519 = 926279) B926279
theorem B617543 : Blo 409770 617543 := bstep (se 1 (by rfl) ⟨463157, by rfl⟩ : syracuseStep 617543 = 926315) B926315
theorem B1174625 : Blo 409770 1174625 := bstep (se 2 (by rfl) ⟨440484, by rfl⟩ : syracuseStep 1174625 = 880969) B880969
theorem B617807 : Blo 409770 617807 := bstep (se 1 (by rfl) ⟨463355, by rfl⟩ : syracuseStep 617807 = 926711) B926711
theorem B3141017 : Blo 409770 3141017 := bstep (se 2 (by rfl) ⟨1177881, by rfl⟩ : syracuseStep 3141017 = 2355763) B2355763
theorem B617897 : Blo 409770 617897 := bstep (se 2 (by rfl) ⟨231711, by rfl⟩ : syracuseStep 617897 = 463423) B463423
theorem B880055 : Blo 409770 880055 := bstep (se 1 (by rfl) ⟨660041, by rfl⟩ : syracuseStep 880055 = 1320083) B1320083
theorem B618047 : Blo 409770 618047 := bstep (se 1 (by rfl) ⟨463535, by rfl⟩ : syracuseStep 618047 = 927071) B927071
theorem B8449601 : Blo 409770 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B618311 : Blo 409770 618311 := bstep (se 1 (by rfl) ⟨463733, by rfl⟩ : syracuseStep 618311 = 927467) B927467
theorem B618395 : Blo 409770 618395 := bstep (se 1 (by rfl) ⟨463796, by rfl⟩ : syracuseStep 618395 = 927593) B927593
theorem B11923523 : Blo 409770 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B1175741 : Blo 409770 1175741 := bstep (se 3 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 1175741 = 440903) B440903
theorem B2257091 : Blo 409770 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B5271763 : Blo 409770 5271763 := bstep (se 1 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 5271763 = 7907645) B7907645
theorem B880951 : Blo 409770 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B586111 : Blo 409770 586111 := bstep (se 1 (by rfl) ⟨439583, by rfl⟩ : syracuseStep 586111 = 879167) B879167
theorem B1765799 : Blo 409770 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B618959 : Blo 409770 618959 := bstep (se 1 (by rfl) ⟨464219, by rfl⟩ : syracuseStep 618959 = 928439) B928439
theorem B619001 : Blo 409770 619001 := bstep (se 2 (by rfl) ⟨232125, by rfl⟩ : syracuseStep 619001 = 464251) B464251
theorem B619103 : Blo 409770 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B619583 : Blo 409770 619583 := bstep (se 1 (by rfl) ⟨464687, by rfl⟩ : syracuseStep 619583 = 929375) B929375
theorem B619625 : Blo 409770 619625 := bstep (se 2 (by rfl) ⟨232359, by rfl⟩ : syracuseStep 619625 = 464719) B464719
theorem B881771 : Blo 409770 881771 := bstep (se 1 (by rfl) ⟨661328, by rfl⟩ : syracuseStep 881771 = 1322657) B1322657
theorem B619727 : Blo 409770 619727 := bstep (se 1 (by rfl) ⟨464795, by rfl⟩ : syracuseStep 619727 = 929591) B929591
theorem B882011 : Blo 409770 882011 := bstep (se 1 (by rfl) ⟨661508, by rfl⟩ : syracuseStep 882011 = 1323017) B1323017
theorem B619931 : Blo 409770 619931 := bstep (se 1 (by rfl) ⟨464948, by rfl⟩ : syracuseStep 619931 = 929897) B929897
theorem B2815559 : Blo 409770 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B620153 : Blo 409770 620153 := bstep (se 2 (by rfl) ⟨232557, by rfl⟩ : syracuseStep 620153 = 465115) B465115
theorem B784055 : Blo 409770 784055 := bstep (se 1 (by rfl) ⟨588041, by rfl⟩ : syracuseStep 784055 = 1176083) B1176083
theorem B620255 : Blo 409770 620255 := bstep (se 1 (by rfl) ⟨465191, by rfl⟩ : syracuseStep 620255 = 930383) B930383
theorem B1046267 : Blo 409770 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B620351 : Blo 409770 620351 := bstep (se 1 (by rfl) ⟨465263, by rfl⟩ : syracuseStep 620351 = 930527) B930527
theorem B620519 : Blo 409770 620519 := bstep (se 1 (by rfl) ⟨465389, by rfl⟩ : syracuseStep 620519 = 930779) B930779
theorem B620537 : Blo 409770 620537 := bstep (se 2 (by rfl) ⟨232701, by rfl⟩ : syracuseStep 620537 = 465403) B465403
theorem B1898579 : Blo 409770 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B620639 : Blo 409770 620639 := bstep (se 1 (by rfl) ⟨465479, by rfl⟩ : syracuseStep 620639 = 930959) B930959
theorem B2816977 : Blo 409770 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B589135 : Blo 409770 589135 := bstep (se 1 (by rfl) ⟨441851, by rfl⟩ : syracuseStep 589135 = 883703) B883703
theorem B1408519 : Blo 409770 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B1080911 : Blo 409770 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B1113679 : Blo 409770 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B20053595 : Blo 409770 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B2228093 : Blo 409770 2228093 := bstep (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) B835535
theorem B1671785 : Blo 409770 1671785 := bstep (se 2 (by rfl) ⟨626919, by rfl⟩ : syracuseStep 1671785 = 1253839) B1253839
theorem B623951 : Blo 409770 623951 := bstep (se 1 (by rfl) ⟨467963, by rfl⟩ : syracuseStep 623951 = 935927) B935927
theorem B2853025 : Blo 409770 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B20384011 : Blo 409770 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B461083 : Blo 409770 461083 := bstep (se 1 (by rfl) ⟨345812, by rfl⟩ : syracuseStep 461083 = 691625) B691625
theorem B986219 : Blo 409770 986219 := bstep (se 1 (by rfl) ⟨739664, by rfl⟩ : syracuseStep 986219 = 1479329) B1479329
theorem B462235 : Blo 409770 462235 := bstep (se 1 (by rfl) ⟨346676, by rfl⟩ : syracuseStep 462235 = 693353) B693353
theorem B3968585 : Blo 409770 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B692219 : Blo 409770 692219 := bstep (se 1 (by rfl) ⟨519164, by rfl⟩ : syracuseStep 692219 = 1038329) B1038329
theorem B692327 : Blo 409770 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B659753 : Blo 409770 659753 := bstep (se 2 (by rfl) ⟨247407, by rfl⟩ : syracuseStep 659753 = 494815) B494815
theorem B7901495 : Blo 409770 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B463207 : Blo 409770 463207 := bstep (se 1 (by rfl) ⟨347405, by rfl⟩ : syracuseStep 463207 = 694811) B694811
theorem B987785 : Blo 409770 987785 := bstep (se 2 (by rfl) ⟨370419, by rfl⟩ : syracuseStep 987785 = 740839) B740839
theorem B693083 : Blo 409770 693083 := bstep (se 1 (by rfl) ⟨519812, by rfl⟩ : syracuseStep 693083 = 1039625) B1039625
theorem B922607 : Blo 409770 922607 := bstep (se 1 (by rfl) ⟨691955, by rfl⟩ : syracuseStep 922607 = 1383911) B1383911
theorem B463855 : Blo 409770 463855 := bstep (se 1 (by rfl) ⟨347891, by rfl⟩ : syracuseStep 463855 = 695783) B695783
theorem B496891 : Blo 409770 496891 := bstep (se 1 (by rfl) ⟨372668, by rfl⟩ : syracuseStep 496891 = 745337) B745337
theorem B1414511 : Blo 409770 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B923111 : Blo 409770 923111 := bstep (se 1 (by rfl) ⟨692333, by rfl⟩ : syracuseStep 923111 = 1384667) B1384667
theorem B464359 : Blo 409770 464359 := bstep (se 1 (by rfl) ⟨348269, by rfl⟩ : syracuseStep 464359 = 696539) B696539
theorem B923273 : Blo 409770 923273 := bstep (se 2 (by rfl) ⟨346227, by rfl⟩ : syracuseStep 923273 = 692455) B692455
theorem B923291 : Blo 409770 923291 := bstep (se 1 (by rfl) ⟨692468, by rfl⟩ : syracuseStep 923291 = 1384937) B1384937
theorem B464539 : Blo 409770 464539 := bstep (se 1 (by rfl) ⟨348404, by rfl⟩ : syracuseStep 464539 = 696809) B696809
theorem B923489 : Blo 409770 923489 := bstep (se 2 (by rfl) ⟨346308, by rfl⟩ : syracuseStep 923489 = 692617) B692617
theorem B1972127 : Blo 409770 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B923687 : Blo 409770 923687 := bstep (se 1 (by rfl) ⟨692765, by rfl⟩ : syracuseStep 923687 = 1385531) B1385531
theorem B923867 : Blo 409770 923867 := bstep (se 1 (by rfl) ⟨692900, by rfl⟩ : syracuseStep 923867 = 1385801) B1385801
theorem B924065 : Blo 409770 924065 := bstep (se 2 (by rfl) ⟨346524, by rfl⟩ : syracuseStep 924065 = 693049) B693049
theorem B924137 : Blo 409770 924137 := bstep (se 2 (by rfl) ⟨346551, by rfl⟩ : syracuseStep 924137 = 693103) B693103
theorem B2104031 : Blo 409770 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B1383155 : Blo 409770 1383155 := bstep (se 1 (by rfl) ⟨1037366, by rfl⟩ : syracuseStep 1383155 = 2074733) B2074733
theorem B990571 : Blo 409770 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B1384289 : Blo 409770 1384289 := bstep (se 2 (by rfl) ⟨519108, by rfl⟩ : syracuseStep 1384289 = 1038217) B1038217
theorem B925595 : Blo 409770 925595 := bstep (se 1 (by rfl) ⟨694196, by rfl⟩ : syracuseStep 925595 = 1388393) B1388393
theorem B3350443 : Blo 409770 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B926009 : Blo 409770 926009 := bstep (se 2 (by rfl) ⟨347253, by rfl⟩ : syracuseStep 926009 = 694507) B694507
theorem B795163 : Blo 409770 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B1385207 : Blo 409770 1385207 := bstep (se 1 (by rfl) ⟨1038905, by rfl⟩ : syracuseStep 1385207 = 2077811) B2077811
theorem B926495 : Blo 409770 926495 := bstep (se 1 (by rfl) ⟨694871, by rfl⟩ : syracuseStep 926495 = 1389743) B1389743
theorem B1877039 : Blo 409770 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B1385639 : Blo 409770 1385639 := bstep (se 1 (by rfl) ⟨1039229, by rfl⟩ : syracuseStep 1385639 = 2078459) B2078459
theorem B697511 : Blo 409770 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B1385747 : Blo 409770 1385747 := bstep (se 1 (by rfl) ⟨1039310, by rfl⟩ : syracuseStep 1385747 = 2078621) B2078621
theorem B992531 : Blo 409770 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B992839 : Blo 409770 992839 := bstep (se 1 (by rfl) ⟨744629, by rfl⟩ : syracuseStep 992839 = 1489259) B1489259
theorem B927305 : Blo 409770 927305 := bstep (se 2 (by rfl) ⟨347739, by rfl⟩ : syracuseStep 927305 = 695479) B695479
theorem B1386287 : Blo 409770 1386287 := bstep (se 1 (by rfl) ⟨1039715, by rfl⟩ : syracuseStep 1386287 = 2079431) B2079431
theorem B927737 : Blo 409770 927737 := bstep (se 2 (by rfl) ⟨347901, by rfl⟩ : syracuseStep 927737 = 695803) B695803
theorem B1878025 : Blo 409770 1878025 := bstep (se 2 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 1878025 = 1408519) B1408519
theorem B2566171 : Blo 409770 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B927791 : Blo 409770 927791 := bstep (se 1 (by rfl) ⟨695843, by rfl⟩ : syracuseStep 927791 = 1391687) B1391687
theorem B4466735 : Blo 409770 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B927827 : Blo 409770 927827 := bstep (se 1 (by rfl) ⟨695870, by rfl⟩ : syracuseStep 927827 = 1391741) B1391741
theorem B1484905 : Blo 409770 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B928007 : Blo 409770 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B5286221 : Blo 409770 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B3746297 : Blo 409770 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B928313 : Blo 409770 928313 := bstep (se 2 (by rfl) ⟨348117, by rfl⟩ : syracuseStep 928313 = 696235) B696235
theorem B1485395 : Blo 409770 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B2337767 : Blo 409770 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B6007931 : Blo 409770 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B929033 : Blo 409770 929033 := bstep (se 2 (by rfl) ⟨348387, by rfl⟩ : syracuseStep 929033 = 696775) B696775
theorem B13381523 : Blo 409770 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B1585291 : Blo 409770 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B930023 : Blo 409770 930023 := bstep (se 1 (by rfl) ⟨697517, by rfl⟩ : syracuseStep 930023 = 1395035) B1395035
theorem B1978643 : Blo 409770 1978643 := bstep (se 1 (by rfl) ⟨1483982, by rfl⟩ : syracuseStep 1978643 = 2967965) B2967965
theorem B930203 : Blo 409770 930203 := bstep (se 1 (by rfl) ⟨697652, by rfl⟩ : syracuseStep 930203 = 1395305) B1395305
theorem B6435607 : Blo 409770 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B5649227 : Blo 409770 5649227 := bstep (se 1 (by rfl) ⟨4236920, by rfl⟩ : syracuseStep 5649227 = 8473841) B8473841
theorem B930887 : Blo 409770 930887 := bstep (se 1 (by rfl) ⟨698165, by rfl⟩ : syracuseStep 930887 = 1396331) B1396331
theorem B439391 : Blo 409770 439391 := bstep (se 1 (by rfl) ⟨329543, by rfl⟩ : syracuseStep 439391 = 659087) B659087
theorem B1324297 : Blo 409770 1324297 := bstep (se 2 (by rfl) ⟨496611, by rfl⟩ : syracuseStep 1324297 = 993223) B993223
theorem B5617309 : Blo 409770 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B5257001 : Blo 409770 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B7059635 : Blo 409770 7059635 := bstep (se 1 (by rfl) ⟨5294726, by rfl⟩ : syracuseStep 7059635 = 10589453) B10589453
theorem B1390823 : Blo 409770 1390823 := bstep (se 1 (by rfl) ⟨1043117, by rfl⟩ : syracuseStep 1390823 = 2086235) B2086235
theorem B1882361 : Blo 409770 1882361 := bstep (se 2 (by rfl) ⟨705885, by rfl⟩ : syracuseStep 1882361 = 1411771) B1411771
theorem B9026599 : Blo 409770 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B2342141 : Blo 409770 2342141 := bstep (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) B878303
theorem B2080079 : Blo 409770 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B1719713 : Blo 409770 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B3325531 : Blo 409770 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B1556279 : Blo 409770 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B1392551 : Blo 409770 1392551 := bstep (se 1 (by rfl) ⟨1044413, by rfl⟩ : syracuseStep 1392551 = 2088827) B2088827
theorem B409791 : Blo 409770 409791 := bstep (se 1 (by rfl) ⟨307343, by rfl⟩ : syracuseStep 409791 = 614687) B614687
theorem B409807 : Blo 409770 409807 := bstep (se 1 (by rfl) ⟨307355, by rfl⟩ : syracuseStep 409807 = 614711) B614711
theorem B1392875 : Blo 409770 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B409855 : Blo 409770 409855 := bstep (se 1 (by rfl) ⟨307391, by rfl⟩ : syracuseStep 409855 = 614783) B614783
theorem B7029017 : Blo 409770 7029017 := bstep (se 2 (by rfl) ⟨2635881, by rfl⟩ : syracuseStep 7029017 = 5271763) B5271763
theorem B409903 : Blo 409770 409903 := bstep (se 1 (by rfl) ⟨307427, by rfl⟩ : syracuseStep 409903 = 614855) B614855
theorem B14434735 : Blo 409770 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B410139 : Blo 409770 410139 := bstep (se 1 (by rfl) ⟨307604, by rfl⟩ : syracuseStep 410139 = 615209) B615209
theorem B410143 : Blo 409770 410143 := bstep (se 1 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 410143 = 615215) B615215
theorem B3523121 : Blo 409770 3523121 := bstep (se 2 (by rfl) ⟨1321170, by rfl⟩ : syracuseStep 3523121 = 2642341) B2642341
theorem B26690147 : Blo 409770 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B410223 : Blo 409770 410223 := bstep (se 1 (by rfl) ⟨307667, by rfl⟩ : syracuseStep 410223 = 615335) B615335
theorem B410279 : Blo 409770 410279 := bstep (se 1 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 410279 = 615419) B615419
theorem B410319 : Blo 409770 410319 := bstep (se 1 (by rfl) ⟨307739, by rfl⟩ : syracuseStep 410319 = 615479) B615479
theorem B410399 : Blo 409770 410399 := bstep (se 1 (by rfl) ⟨307799, by rfl⟩ : syracuseStep 410399 = 615599) B615599
theorem B410671 : Blo 409770 410671 := bstep (se 1 (by rfl) ⟨308003, by rfl⟩ : syracuseStep 410671 = 616007) B616007
theorem B410735 : Blo 409770 410735 := bstep (se 1 (by rfl) ⟨308051, by rfl⟩ : syracuseStep 410735 = 616103) B616103
theorem B410791 : Blo 409770 410791 := bstep (se 1 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 410791 = 616187) B616187
theorem B410815 : Blo 409770 410815 := bstep (se 1 (by rfl) ⟨308111, by rfl⟩ : syracuseStep 410815 = 616223) B616223
theorem B410847 : Blo 409770 410847 := bstep (se 1 (by rfl) ⟨308135, by rfl⟩ : syracuseStep 410847 = 616271) B616271
theorem B410927 : Blo 409770 410927 := bstep (se 1 (by rfl) ⟨308195, by rfl⟩ : syracuseStep 410927 = 616391) B616391
theorem B2082185 : Blo 409770 2082185 := bstep (se 2 (by rfl) ⟨780819, by rfl⟩ : syracuseStep 2082185 = 1561639) B1561639
theorem B3130811 : Blo 409770 3130811 := bstep (se 1 (by rfl) ⟨2348108, by rfl⟩ : syracuseStep 3130811 = 4696217) B4696217
theorem B411163 : Blo 409770 411163 := bstep (se 1 (by rfl) ⟨308372, by rfl⟩ : syracuseStep 411163 = 616745) B616745
theorem B411167 : Blo 409770 411167 := bstep (se 1 (by rfl) ⟨308375, by rfl⟩ : syracuseStep 411167 = 616751) B616751
theorem B706079 : Blo 409770 706079 := bstep (se 1 (by rfl) ⟨529559, by rfl⟩ : syracuseStep 706079 = 1059119) B1059119
theorem B411327 : Blo 409770 411327 := bstep (se 1 (by rfl) ⟨308495, by rfl⟩ : syracuseStep 411327 = 616991) B616991
theorem B411583 : Blo 409770 411583 := bstep (se 1 (by rfl) ⟨308687, by rfl⟩ : syracuseStep 411583 = 617375) B617375
theorem B411615 : Blo 409770 411615 := bstep (se 1 (by rfl) ⟨308711, by rfl⟩ : syracuseStep 411615 = 617423) B617423
theorem B411675 : Blo 409770 411675 := bstep (se 1 (by rfl) ⟨308756, by rfl⟩ : syracuseStep 411675 = 617513) B617513
theorem B411679 : Blo 409770 411679 := bstep (se 1 (by rfl) ⟨308759, by rfl⟩ : syracuseStep 411679 = 617519) B617519
theorem B411695 : Blo 409770 411695 := bstep (se 1 (by rfl) ⟨308771, by rfl⟩ : syracuseStep 411695 = 617543) B617543
theorem B411871 : Blo 409770 411871 := bstep (se 1 (by rfl) ⟨308903, by rfl⟩ : syracuseStep 411871 = 617807) B617807
theorem B411931 : Blo 409770 411931 := bstep (se 1 (by rfl) ⟨308948, by rfl⟩ : syracuseStep 411931 = 617897) B617897
theorem B7883041 : Blo 409770 7883041 := bstep (se 2 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 7883041 = 5912281) B5912281
theorem B412031 : Blo 409770 412031 := bstep (se 1 (by rfl) ⟨309023, by rfl⟩ : syracuseStep 412031 = 618047) B618047
theorem B412207 : Blo 409770 412207 := bstep (se 1 (by rfl) ⟨309155, by rfl⟩ : syracuseStep 412207 = 618311) B618311
theorem B1755751 : Blo 409770 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B412263 : Blo 409770 412263 := bstep (se 1 (by rfl) ⟨309197, by rfl⟩ : syracuseStep 412263 = 618395) B618395
theorem B7949015 : Blo 409770 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B1887031 : Blo 409770 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B1756025 : Blo 409770 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B412639 : Blo 409770 412639 := bstep (se 1 (by rfl) ⟨309479, by rfl⟩ : syracuseStep 412639 = 618959) B618959
theorem B412667 : Blo 409770 412667 := bstep (se 1 (by rfl) ⟨309500, by rfl⟩ : syracuseStep 412667 = 619001) B619001
theorem B412735 : Blo 409770 412735 := bstep (se 1 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 412735 = 619103) B619103
theorem B1559695 : Blo 409770 1559695 := bstep (se 1 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 1559695 = 2339543) B2339543
theorem B3656927 : Blo 409770 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B413055 : Blo 409770 413055 := bstep (se 1 (by rfl) ⟨309791, by rfl⟩ : syracuseStep 413055 = 619583) B619583
theorem B413083 : Blo 409770 413083 := bstep (se 1 (by rfl) ⟨309812, by rfl⟩ : syracuseStep 413083 = 619625) B619625
theorem B1559969 : Blo 409770 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B413151 : Blo 409770 413151 := bstep (se 1 (by rfl) ⟨309863, by rfl⟩ : syracuseStep 413151 = 619727) B619727
theorem B1560167 : Blo 409770 1560167 := bstep (se 1 (by rfl) ⟨1170125, by rfl⟩ : syracuseStep 1560167 = 2340251) B2340251
theorem B413287 : Blo 409770 413287 := bstep (se 1 (by rfl) ⟨309965, by rfl⟩ : syracuseStep 413287 = 619931) B619931
theorem B413435 : Blo 409770 413435 := bstep (se 1 (by rfl) ⟨310076, by rfl⟩ : syracuseStep 413435 = 620153) B620153
theorem B413503 : Blo 409770 413503 := bstep (se 1 (by rfl) ⟨310127, by rfl⟩ : syracuseStep 413503 = 620255) B620255
theorem B413567 : Blo 409770 413567 := bstep (se 1 (by rfl) ⟨310175, by rfl⟩ : syracuseStep 413567 = 620351) B620351
theorem B3755969 : Blo 409770 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B1167335 : Blo 409770 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B413679 : Blo 409770 413679 := bstep (se 1 (by rfl) ⟨310259, by rfl⟩ : syracuseStep 413679 = 620519) B620519
theorem B413691 : Blo 409770 413691 := bstep (se 1 (by rfl) ⟨310268, by rfl⟩ : syracuseStep 413691 = 620537) B620537
theorem B1265719 : Blo 409770 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B413759 : Blo 409770 413759 := bstep (se 1 (by rfl) ⟨310319, by rfl⟩ : syracuseStep 413759 = 620639) B620639
theorem B22532269 : Blo 409770 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B1037407 : Blo 409770 1037407 := bstep (se 1 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 1037407 = 1556111) B1556111
theorem B1562399 : Blo 409770 1562399 := bstep (se 1 (by rfl) ⟨1171799, by rfl⟩ : syracuseStep 1562399 = 2343599) B2343599
theorem B3528521 : Blo 409770 3528521 := bstep (se 2 (by rfl) ⟨1323195, by rfl⟩ : syracuseStep 3528521 = 2646391) B2646391
theorem B1759067 : Blo 409770 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B1431865 : Blo 409770 1431865 := bstep (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) B1073899
theorem B1169761 : Blo 409770 1169761 := bstep (se 2 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 1169761 = 877321) B877321
theorem B3824047 : Blo 409770 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B3562055 : Blo 409770 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B940855 : Blo 409770 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B4709339 : Blo 409770 4709339 := bstep (se 1 (by rfl) ⟨3532004, by rfl⟩ : syracuseStep 4709339 = 7064009) B7064009
theorem B1760399 : Blo 409770 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B16867025 : Blo 409770 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B1171219 : Blo 409770 1171219 := bstep (se 1 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 1171219 = 1756829) B1756829
theorem B1564555 : Blo 409770 1564555 := bstep (se 1 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 1564555 = 2346833) B2346833
theorem B2678683 : Blo 409770 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B2351389 : Blo 409770 2351389 := bstep (se 3 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 2351389 = 881771) B881771
theorem B614939 : Blo 409770 614939 := bstep (se 1 (by rfl) ⟨461204, by rfl⟩ : syracuseStep 614939 = 922409) B922409
theorem B3007003 : Blo 409770 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B8872577 : Blo 409770 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B615119 : Blo 409770 615119 := bstep (se 1 (by rfl) ⟨461339, by rfl⟩ : syracuseStep 615119 = 922679) B922679
theorem B615131 : Blo 409770 615131 := bstep (se 1 (by rfl) ⟨461348, by rfl⟩ : syracuseStep 615131 = 922697) B922697
theorem B418591 : Blo 409770 418591 := bstep (se 1 (by rfl) ⟨313943, by rfl⟩ : syracuseStep 418591 = 627887) B627887
theorem B615545 : Blo 409770 615545 := bstep (se 2 (by rfl) ⟨230829, by rfl⟩ : syracuseStep 615545 = 461659) B461659
theorem B877979 : Blo 409770 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B3532247 : Blo 409770 3532247 := bstep (se 1 (by rfl) ⟨2649185, by rfl⟩ : syracuseStep 3532247 = 5298371) B5298371
theorem B1762843 : Blo 409770 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B616415 : Blo 409770 616415 := bstep (se 1 (by rfl) ⟨462311, by rfl⟩ : syracuseStep 616415 = 924623) B924623
theorem B616427 : Blo 409770 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B616475 : Blo 409770 616475 := bstep (se 1 (by rfl) ⟨462356, by rfl⟩ : syracuseStep 616475 = 924713) B924713
theorem B1566803 : Blo 409770 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B878825 : Blo 409770 878825 := bstep (se 2 (by rfl) ⟨329559, by rfl⟩ : syracuseStep 878825 = 659119) B659119
theorem B616841 : Blo 409770 616841 := bstep (se 2 (by rfl) ⟨231315, by rfl⟩ : syracuseStep 616841 = 462631) B462631
theorem B5270123 : Blo 409770 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B3959441 : Blo 409770 3959441 := bstep (se 2 (by rfl) ⟨1484790, by rfl⟩ : syracuseStep 3959441 = 2969581) B2969581
theorem B1174351 : Blo 409770 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1174601 : Blo 409770 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B781481 : Blo 409770 781481 := bstep (se 2 (by rfl) ⟨293055, by rfl⟩ : syracuseStep 781481 = 586111) B586111
theorem B617783 : Blo 409770 617783 := bstep (se 1 (by rfl) ⟨463337, by rfl⟩ : syracuseStep 617783 = 926675) B926675
theorem B617951 : Blo 409770 617951 := bstep (se 1 (by rfl) ⟨463463, by rfl⟩ : syracuseStep 617951 = 926927) B926927
theorem B781967 : Blo 409770 781967 := bstep (se 1 (by rfl) ⟨586475, by rfl⟩ : syracuseStep 781967 = 1172951) B1172951
theorem B618167 : Blo 409770 618167 := bstep (se 1 (by rfl) ⟨463625, by rfl⟩ : syracuseStep 618167 = 927251) B927251
theorem B1765115 : Blo 409770 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B618377 : Blo 409770 618377 := bstep (se 2 (by rfl) ⟨231891, by rfl⟩ : syracuseStep 618377 = 463783) B463783
theorem B618623 : Blo 409770 618623 := bstep (se 1 (by rfl) ⟨463967, by rfl⟩ : syracuseStep 618623 = 927935) B927935
theorem B1044839 : Blo 409770 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B1176059 : Blo 409770 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B783083 : Blo 409770 783083 := bstep (se 1 (by rfl) ⟨587312, by rfl⟩ : syracuseStep 783083 = 1174625) B1174625
theorem B619259 : Blo 409770 619259 := bstep (se 1 (by rfl) ⟨464444, by rfl⟩ : syracuseStep 619259 = 928889) B928889
theorem B5927741 : Blo 409770 5927741 := bstep (se 3 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 5927741 = 2222903) B2222903
theorem B2094011 : Blo 409770 2094011 := bstep (se 1 (by rfl) ⟨1570508, by rfl⟩ : syracuseStep 2094011 = 3141017) B3141017
theorem B586703 : Blo 409770 586703 := bstep (se 1 (by rfl) ⟨440027, by rfl⟩ : syracuseStep 586703 = 880055) B880055
theorem B619703 : Blo 409770 619703 := bstep (se 1 (by rfl) ⟨464777, by rfl⟩ : syracuseStep 619703 = 929555) B929555
theorem B619943 : Blo 409770 619943 := bstep (se 1 (by rfl) ⟨464957, by rfl⟩ : syracuseStep 619943 = 929915) B929915
theorem B783827 : Blo 409770 783827 := bstep (se 1 (by rfl) ⟨587870, by rfl⟩ : syracuseStep 783827 = 1175741) B1175741
theorem B1504727 : Blo 409770 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B620123 : Blo 409770 620123 := bstep (se 1 (by rfl) ⟨465092, by rfl⟩ : syracuseStep 620123 = 930185) B930185
theorem B1177199 : Blo 409770 1177199 := bstep (se 1 (by rfl) ⟨882899, by rfl⟩ : syracuseStep 1177199 = 1765799) B1765799
theorem B2815661 : Blo 409770 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B3766181 : Blo 409770 3766181 := bstep (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) B706159
theorem B620585 : Blo 409770 620585 := bstep (se 2 (by rfl) ⟨232719, by rfl⟩ : syracuseStep 620585 = 465439) B465439
theorem B620615 : Blo 409770 620615 := bstep (se 1 (by rfl) ⟨465461, by rfl⟩ : syracuseStep 620615 = 930923) B930923
theorem B588007 : Blo 409770 588007 := bstep (se 1 (by rfl) ⟨441005, by rfl⟩ : syracuseStep 588007 = 882011) B882011
theorem B522703 : Blo 409770 522703 := bstep (se 1 (by rfl) ⟨392027, by rfl⟩ : syracuseStep 522703 = 784055) B784055
theorem B883241 : Blo 409770 883241 := bstep (se 2 (by rfl) ⟨331215, by rfl⟩ : syracuseStep 883241 = 662431) B662431
theorem B883343 : Blo 409770 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B1342295 : Blo 409770 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B2882429 : Blo 409770 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B785513 : Blo 409770 785513 := bstep (se 2 (by rfl) ⟨294567, by rfl⟩ : syracuseStep 785513 = 589135) B589135
theorem B2817305 : Blo 409770 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B13369063 : Blo 409770 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B3112829 : Blo 409770 3112829 := bstep (se 3 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 3112829 = 1167311) B1167311
theorem B4686011 : Blo 409770 4686011 := bstep (se 1 (by rfl) ⟨3514508, by rfl⟩ : syracuseStep 4686011 = 7029017) B7029017
theorem B17793431 : Blo 409770 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B1114523 : Blo 409770 1114523 := bstep (se 1 (by rfl) ⟨835892, by rfl⟩ : syracuseStep 1114523 = 1671785) B1671785
theorem B558121 : Blo 409770 558121 := bstep (se 2 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 558121 = 418591) B418591
theorem B657479 : Blo 409770 657479 := bstep (se 1 (by rfl) ⟨493109, by rfl⟩ : syracuseStep 657479 = 986219) B986219
theorem B461479 : Blo 409770 461479 := bstep (se 1 (by rfl) ⟨346109, by rfl⟩ : syracuseStep 461479 = 692219) B692219
theorem B461551 : Blo 409770 461551 := bstep (se 1 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 461551 = 692327) B692327
theorem B658523 : Blo 409770 658523 := bstep (se 1 (by rfl) ⟨493892, by rfl⟩ : syracuseStep 658523 = 987785) B987785
theorem B462055 : Blo 409770 462055 := bstep (se 1 (by rfl) ⟨346541, by rfl⟩ : syracuseStep 462055 = 693083) B693083
theorem B922103 : Blo 409770 922103 := bstep (se 1 (by rfl) ⟨691577, by rfl⟩ : syracuseStep 922103 = 1383155) B1383155
theorem B11244683 : Blo 409770 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B922859 : Blo 409770 922859 := bstep (se 1 (by rfl) ⟨692144, by rfl⟩ : syracuseStep 922859 = 1384289) B1384289
theorem B923471 : Blo 409770 923471 := bstep (se 1 (by rfl) ⟨692603, by rfl⟩ : syracuseStep 923471 = 1385207) B1385207
theorem B1251359 : Blo 409770 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B923759 : Blo 409770 923759 := bstep (se 1 (by rfl) ⟨692819, by rfl⟩ : syracuseStep 923759 = 1385639) B1385639
theorem B465007 : Blo 409770 465007 := bstep (se 1 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 465007 = 697511) B697511
theorem B923831 : Blo 409770 923831 := bstep (se 1 (by rfl) ⟨692873, by rfl⟩ : syracuseStep 923831 = 1385747) B1385747
theorem B924191 : Blo 409770 924191 := bstep (se 1 (by rfl) ⟨693143, by rfl⟩ : syracuseStep 924191 = 1386287) B1386287
theorem B1383209 : Blo 409770 1383209 := bstep (se 2 (by rfl) ⟨518703, by rfl⟩ : syracuseStep 1383209 = 1037407) B1037407
theorem B662521 : Blo 409770 662521 := bstep (se 2 (by rfl) ⟨248445, by rfl⟩ : syracuseStep 662521 = 496891) B496891
theorem B990263 : Blo 409770 990263 := bstep (se 1 (by rfl) ⟨742697, by rfl⟩ : syracuseStep 990263 = 1485395) B1485395
theorem B3513415 : Blo 409770 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B4005287 : Blo 409770 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B8921015 : Blo 409770 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B1319095 : Blo 409770 1319095 := bstep (se 1 (by rfl) ⟨989321, by rfl⟩ : syracuseStep 1319095 = 1978643) B1978643
theorem B696559 : Blo 409770 696559 := bstep (se 1 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 696559 = 1044839) B1044839
theorem B1909153 : Blo 409770 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B696937 : Blo 409770 696937 := bstep (se 2 (by rfl) ⟨261351, by rfl⟩ : syracuseStep 696937 = 522703) B522703
theorem B1254473 : Blo 409770 1254473 := bstep (se 2 (by rfl) ⟨470427, by rfl⟩ : syracuseStep 1254473 = 940855) B940855
theorem B1877107 : Blo 409770 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B12035465 : Blo 409770 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B927215 : Blo 409770 927215 := bstep (se 1 (by rfl) ⟨695411, by rfl⟩ : syracuseStep 927215 = 1390823) B1390823
theorem B1254907 : Blo 409770 1254907 := bstep (se 1 (by rfl) ⟨941180, by rfl⟩ : syracuseStep 1254907 = 1882361) B1882361
theorem B1320761 : Blo 409770 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B894863 : Blo 409770 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B4434041 : Blo 409770 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B1878203 : Blo 409770 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B1386719 : Blo 409770 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B4467257 : Blo 409770 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B2075219 : Blo 409770 2075219 := bstep (se 1 (by rfl) ⟨1556414, by rfl⟩ : syracuseStep 2075219 = 3112829) B3112829
theorem B928367 : Blo 409770 928367 := bstep (se 1 (by rfl) ⟨696275, by rfl⟩ : syracuseStep 928367 = 1392551) B1392551
theorem B928583 : Blo 409770 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B19246313 : Blo 409770 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B4009337 : Blo 409770 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B1060217 : Blo 409770 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B15216133 : Blo 409770 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B1388123 : Blo 409770 1388123 := bstep (se 1 (by rfl) ⟨1041092, by rfl⟩ : syracuseStep 1388123 = 2082185) B2082185
theorem B470719 : Blo 409770 470719 := bstep (se 1 (by rfl) ⟨353039, by rfl⟩ : syracuseStep 470719 = 706079) B706079
theorem B1323785 : Blo 409770 1323785 := bstep (se 2 (by rfl) ⟨496419, by rfl⟩ : syracuseStep 1323785 = 992839) B992839
theorem B2437951 : Blo 409770 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B2503979 : Blo 409770 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B2504033 : Blo 409770 2504033 := bstep (se 2 (by rfl) ⟨939012, by rfl⟩ : syracuseStep 2504033 = 1878025) B1878025
theorem B1979873 : Blo 409770 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B439835 : Blo 409770 439835 := bstep (se 1 (by rfl) ⟨329876, by rfl⟩ : syracuseStep 439835 = 659753) B659753
theorem B27178681 : Blo 409770 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B2341001 : Blo 409770 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B2079593 : Blo 409770 2079593 := bstep (se 2 (by rfl) ⟨779847, by rfl⟩ : syracuseStep 2079593 = 1559695) B1559695
theorem B2374703 : Blo 409770 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B5259005 : Blo 409770 5259005 := bstep (se 3 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 5259005 = 1972127) B1972127
theorem B10043149 : Blo 409770 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B1687625 : Blo 409770 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B2113721 : Blo 409770 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B409959 : Blo 409770 409959 := bstep (se 1 (by rfl) ⟨307469, by rfl⟩ : syracuseStep 409959 = 614939) B614939
theorem B5915051 : Blo 409770 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B410079 : Blo 409770 410079 := bstep (se 1 (by rfl) ⟨307559, by rfl⟩ : syracuseStep 410079 = 615119) B615119
theorem B410087 : Blo 409770 410087 := bstep (se 1 (by rfl) ⟨307565, by rfl⟩ : syracuseStep 410087 = 615131) B615131
theorem B410363 : Blo 409770 410363 := bstep (se 1 (by rfl) ⟨307772, by rfl⟩ : syracuseStep 410363 = 615545) B615545
theorem B410943 : Blo 409770 410943 := bstep (se 1 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 410943 = 616415) B616415
theorem B410951 : Blo 409770 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B410983 : Blo 409770 410983 := bstep (se 1 (by rfl) ⟨308237, by rfl⟩ : syracuseStep 410983 = 616475) B616475
theorem B3524147 : Blo 409770 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B411227 : Blo 409770 411227 := bstep (se 1 (by rfl) ⟨308420, by rfl⟩ : syracuseStep 411227 = 616841) B616841
theorem B2639627 : Blo 409770 2639627 := bstep (se 1 (by rfl) ⟨1979720, by rfl⟩ : syracuseStep 2639627 = 3959441) B3959441
theorem B1558511 : Blo 409770 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B411855 : Blo 409770 411855 := bstep (se 1 (by rfl) ⟨308891, by rfl⟩ : syracuseStep 411855 = 617783) B617783
theorem B7489745 : Blo 409770 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B411967 : Blo 409770 411967 := bstep (se 1 (by rfl) ⟨308975, by rfl⟩ : syracuseStep 411967 = 617951) B617951
theorem B412111 : Blo 409770 412111 := bstep (se 1 (by rfl) ⟨309083, by rfl⟩ : syracuseStep 412111 = 618167) B618167
theorem B412251 : Blo 409770 412251 := bstep (se 1 (by rfl) ⟨309188, by rfl⟩ : syracuseStep 412251 = 618377) B618377
theorem B412415 : Blo 409770 412415 := bstep (se 1 (by rfl) ⟨309311, by rfl⟩ : syracuseStep 412415 = 618623) B618623
theorem B3132269 : Blo 409770 3132269 := bstep (se 3 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 3132269 = 1174601) B1174601
theorem B1559681 : Blo 409770 1559681 := bstep (se 2 (by rfl) ⟨584880, by rfl⟩ : syracuseStep 1559681 = 1169761) B1169761
theorem B412839 : Blo 409770 412839 := bstep (se 1 (by rfl) ⟨309629, by rfl⟩ : syracuseStep 412839 = 619259) B619259
theorem B3951827 : Blo 409770 3951827 := bstep (se 1 (by rfl) ⟨2963870, by rfl⟩ : syracuseStep 3951827 = 5927741) B5927741
theorem B5098729 : Blo 409770 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B1396007 : Blo 409770 1396007 := bstep (se 1 (by rfl) ⟨1047005, by rfl⟩ : syracuseStep 1396007 = 2094011) B2094011
theorem B413135 : Blo 409770 413135 := bstep (se 1 (by rfl) ⟨309851, by rfl⟩ : syracuseStep 413135 = 619703) B619703
theorem B413295 : Blo 409770 413295 := bstep (se 1 (by rfl) ⟨309971, by rfl⟩ : syracuseStep 413295 = 619943) B619943
theorem B1003151 : Blo 409770 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B413415 : Blo 409770 413415 := bstep (se 1 (by rfl) ⟨310061, by rfl⟩ : syracuseStep 413415 = 620123) B620123
theorem B413723 : Blo 409770 413723 := bstep (se 1 (by rfl) ⟨310292, by rfl⟩ : syracuseStep 413723 = 620585) B620585
theorem B413743 : Blo 409770 413743 := bstep (se 1 (by rfl) ⟨310307, by rfl⟩ : syracuseStep 413743 = 620615) B620615
theorem B4706423 : Blo 409770 4706423 := bstep (se 1 (by rfl) ⟨3529817, by rfl⟩ : syracuseStep 4706423 = 7059635) B7059635
theorem B1921619 : Blo 409770 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B1561427 : Blo 409770 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B1561625 : Blo 409770 1561625 := bstep (se 2 (by rfl) ⟨585609, by rfl⟩ : syracuseStep 1561625 = 1171219) B1171219
theorem B2086073 : Blo 409770 2086073 := bstep (se 2 (by rfl) ⟨782277, by rfl⟩ : syracuseStep 2086073 = 1564555) B1564555
theorem B1037519 : Blo 409770 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B13686245 : Blo 409770 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B2348747 : Blo 409770 2348747 := bstep (se 1 (by rfl) ⟨1761560, by rfl⟩ : syracuseStep 2348747 = 3523121) B3523121
theorem B3135185 : Blo 409770 3135185 := bstep (se 2 (by rfl) ⟨1175694, by rfl⟩ : syracuseStep 3135185 = 2351389) B2351389
theorem B415967 : Blo 409770 415967 := bstep (se 1 (by rfl) ⟨311975, by rfl⟩ : syracuseStep 415967 = 623951) B623951
theorem B2087207 : Blo 409770 2087207 := bstep (se 1 (by rfl) ⟨1565405, by rfl⟩ : syracuseStep 2087207 = 3130811) B3130811
theorem B3136157 : Blo 409770 3136157 := bstep (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) B1176059
theorem B5299343 : Blo 409770 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B1170683 : Blo 409770 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B2350457 : Blo 409770 2350457 := bstep (se 2 (by rfl) ⟨881421, by rfl⟩ : syracuseStep 2350457 = 1762843) B1762843
theorem B1039979 : Blo 409770 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B2645723 : Blo 409770 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B1040111 : Blo 409770 1040111 := bstep (se 1 (by rfl) ⟨780083, by rfl⟩ : syracuseStep 1040111 = 1560167) B1560167
theorem B1564541 : Blo 409770 1564541 := bstep (se 3 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 1564541 = 586703) B586703
theorem B778223 : Blo 409770 778223 := bstep (se 1 (by rfl) ⟨583667, by rfl⟩ : syracuseStep 778223 = 1167335) B1167335
theorem B5267663 : Blo 409770 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B1171709 : Blo 409770 1171709 := bstep (se 3 (by rfl) ⟨219695, by rfl⟩ : syracuseStep 1171709 = 439391) B439391
theorem B614777 : Blo 409770 614777 := bstep (se 2 (by rfl) ⟨230541, by rfl⟩ : syracuseStep 614777 = 461083) B461083
theorem B10510721 : Blo 409770 10510721 := bstep (se 2 (by rfl) ⟨3941520, by rfl⟩ : syracuseStep 10510721 = 7883041) B7883041
theorem B615071 : Blo 409770 615071 := bstep (se 1 (by rfl) ⟨461303, by rfl⟩ : syracuseStep 615071 = 922607) B922607
theorem B2646749 : Blo 409770 2646749 := bstep (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) B992531
theorem B943007 : Blo 409770 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B615407 : Blo 409770 615407 := bstep (se 1 (by rfl) ⟨461555, by rfl⟩ : syracuseStep 615407 = 923111) B923111
theorem B2516041 : Blo 409770 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B615515 : Blo 409770 615515 := bstep (se 1 (by rfl) ⟨461636, by rfl⟩ : syracuseStep 615515 = 923273) B923273
theorem B615527 : Blo 409770 615527 := bstep (se 1 (by rfl) ⟨461645, by rfl⟩ : syracuseStep 615527 = 923291) B923291
theorem B1565801 : Blo 409770 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B1041599 : Blo 409770 1041599 := bstep (se 1 (by rfl) ⟨781199, by rfl⟩ : syracuseStep 1041599 = 1562399) B1562399
theorem B2352347 : Blo 409770 2352347 := bstep (se 1 (by rfl) ⟨1764260, by rfl⟩ : syracuseStep 2352347 = 3528521) B3528521
theorem B1172711 : Blo 409770 1172711 := bstep (se 1 (by rfl) ⟨879533, by rfl⟩ : syracuseStep 1172711 = 1759067) B1759067
theorem B615659 : Blo 409770 615659 := bstep (se 1 (by rfl) ⟨461744, by rfl⟩ : syracuseStep 615659 = 923489) B923489
theorem B615791 : Blo 409770 615791 := bstep (se 1 (by rfl) ⟨461843, by rfl⟩ : syracuseStep 615791 = 923687) B923687
theorem B615911 : Blo 409770 615911 := bstep (se 1 (by rfl) ⟨461933, by rfl⟩ : syracuseStep 615911 = 923867) B923867
theorem B616043 : Blo 409770 616043 := bstep (se 1 (by rfl) ⟨462032, by rfl⟩ : syracuseStep 616043 = 924065) B924065
theorem B616091 : Blo 409770 616091 := bstep (se 1 (by rfl) ⟨462068, by rfl⟩ : syracuseStep 616091 = 924137) B924137
theorem B1402687 : Blo 409770 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B616313 : Blo 409770 616313 := bstep (se 2 (by rfl) ⟨231117, by rfl⟩ : syracuseStep 616313 = 462235) B462235
theorem B3139559 : Blo 409770 3139559 := bstep (se 1 (by rfl) ⟨2354669, by rfl⟩ : syracuseStep 3139559 = 4709339) B4709339
theorem B1173599 : Blo 409770 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B617063 : Blo 409770 617063 := bstep (se 1 (by rfl) ⟨462797, by rfl⟩ : syracuseStep 617063 = 925595) B925595
theorem B617339 : Blo 409770 617339 := bstep (se 1 (by rfl) ⟨463004, by rfl⟩ : syracuseStep 617339 = 926009) B926009
theorem B30043025 : Blo 409770 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B617609 : Blo 409770 617609 := bstep (se 2 (by rfl) ⟨231603, by rfl⟩ : syracuseStep 617609 = 463207) B463207
theorem B617663 : Blo 409770 617663 := bstep (se 1 (by rfl) ⟨463247, by rfl⟩ : syracuseStep 617663 = 926495) B926495
theorem B585319 : Blo 409770 585319 := bstep (se 1 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 585319 = 877979) B877979
theorem B2354831 : Blo 409770 2354831 := bstep (se 1 (by rfl) ⟨1766123, by rfl⟩ : syracuseStep 2354831 = 3532247) B3532247
theorem B8580809 : Blo 409770 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B618203 : Blo 409770 618203 := bstep (se 1 (by rfl) ⟨463652, by rfl⟩ : syracuseStep 618203 = 927305) B927305
theorem B618473 : Blo 409770 618473 := bstep (se 2 (by rfl) ⟨231927, by rfl⟩ : syracuseStep 618473 = 463855) B463855
theorem B9990125 : Blo 409770 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B618491 : Blo 409770 618491 := bstep (se 1 (by rfl) ⟨463868, by rfl⟩ : syracuseStep 618491 = 927737) B927737
theorem B618527 : Blo 409770 618527 := bstep (se 1 (by rfl) ⟨463895, by rfl⟩ : syracuseStep 618527 = 927791) B927791
theorem B2977823 : Blo 409770 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B618551 : Blo 409770 618551 := bstep (se 1 (by rfl) ⟨463913, by rfl⟩ : syracuseStep 618551 = 927827) B927827
theorem B1044535 : Blo 409770 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B585883 : Blo 409770 585883 := bstep (se 1 (by rfl) ⟨439412, by rfl⟩ : syracuseStep 585883 = 878825) B878825
theorem B618671 : Blo 409770 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B1765729 : Blo 409770 1765729 := bstep (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) B1324297
theorem B618875 : Blo 409770 618875 := bstep (se 1 (by rfl) ⟨464156, by rfl⟩ : syracuseStep 618875 = 928313) B928313
theorem B2355581 : Blo 409770 2355581 := bstep (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) B883343
theorem B619145 : Blo 409770 619145 := bstep (se 2 (by rfl) ⟨232179, by rfl⟩ : syracuseStep 619145 = 464359) B464359
theorem B520987 : Blo 409770 520987 := bstep (se 1 (by rfl) ⟨390740, by rfl⟩ : syracuseStep 520987 = 781481) B781481
theorem B619355 : Blo 409770 619355 := bstep (se 1 (by rfl) ⟨464516, by rfl⟩ : syracuseStep 619355 = 929033) B929033
theorem B619385 : Blo 409770 619385 := bstep (se 2 (by rfl) ⟨232269, by rfl⟩ : syracuseStep 619385 = 464539) B464539
theorem B521311 : Blo 409770 521311 := bstep (se 1 (by rfl) ⟨390983, by rfl⟩ : syracuseStep 521311 = 781967) B781967
theorem B1176743 : Blo 409770 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B620015 : Blo 409770 620015 := bstep (se 1 (by rfl) ⟨465011, by rfl⟩ : syracuseStep 620015 = 930023) B930023
theorem B620135 : Blo 409770 620135 := bstep (se 1 (by rfl) ⟨465101, by rfl⟩ : syracuseStep 620135 = 930203) B930203
theorem B784009 : Blo 409770 784009 := bstep (se 2 (by rfl) ⟨294003, by rfl⟩ : syracuseStep 784009 = 588007) B588007
theorem B522055 : Blo 409770 522055 := bstep (se 1 (by rfl) ⟨391541, by rfl⟩ : syracuseStep 522055 = 783083) B783083
theorem B3766151 : Blo 409770 3766151 := bstep (se 1 (by rfl) ⟨2824613, by rfl⟩ : syracuseStep 3766151 = 5649227) B5649227
theorem B620591 : Blo 409770 620591 := bstep (se 1 (by rfl) ⟨465443, by rfl⟩ : syracuseStep 620591 = 930887) B930887
theorem B522551 : Blo 409770 522551 := bstep (se 1 (by rfl) ⟨391913, by rfl⟩ : syracuseStep 522551 = 783827) B783827
theorem B784799 : Blo 409770 784799 := bstep (se 1 (by rfl) ⟨588599, by rfl⟩ : syracuseStep 784799 = 1177199) B1177199
theorem B3504667 : Blo 409770 3504667 := bstep (se 1 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 3504667 = 5257001) B5257001
theorem B588827 : Blo 409770 588827 := bstep (se 1 (by rfl) ⟨441620, by rfl⟩ : syracuseStep 588827 = 883241) B883241
theorem B523675 : Blo 409770 523675 := bstep (se 1 (by rfl) ⟨392756, by rfl⟩ : syracuseStep 523675 = 785513) B785513
theorem B1146475 : Blo 409770 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B17825417 : Blo 409770 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B3571577 : Blo 409770 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B1409147 : Blo 409770 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B11862287 : Blo 409770 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B1673209 : Blo 409770 1673209 := bstep (se 2 (by rfl) ⟨627453, by rfl⟩ : syracuseStep 1673209 = 1254907) B1254907
theorem B1870249 : Blo 409770 1870249 := bstep (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) B1402687
theorem B29985821 : Blo 409770 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B1281079 : Blo 409770 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B691679 : Blo 409770 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B922139 : Blo 409770 922139 := bstep (se 1 (by rfl) ⟨691604, by rfl⟩ : syracuseStep 922139 = 1383209) B1383209
theorem B20288177 : Blo 409770 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B627625 : Blo 409770 627625 := bstep (se 2 (by rfl) ⟨235359, by rfl⟩ : syracuseStep 627625 = 470719) B470719
theorem B693319 : Blo 409770 693319 := bstep (se 1 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 693319 = 1039979) B1039979
theorem B693407 : Blo 409770 693407 := bstep (se 1 (by rfl) ⟨520055, by rfl⟩ : syracuseStep 693407 = 1040111) B1040111
theorem B3511775 : Blo 409770 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B694399 : Blo 409770 694399 := bstep (se 1 (by rfl) ⟨520799, by rfl⟩ : syracuseStep 694399 = 1041599) B1041599
theorem B694649 : Blo 409770 694649 := bstep (se 2 (by rfl) ⟨260493, by rfl⟩ : syracuseStep 694649 = 520987) B520987
theorem B3250601 : Blo 409770 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B596575 : Blo 409770 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B2956027 : Blo 409770 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B1252135 : Blo 409770 1252135 := bstep (se 1 (by rfl) ⟨939101, by rfl⟩ : syracuseStep 1252135 = 1878203) B1878203
theorem B695081 : Blo 409770 695081 := bstep (se 2 (by rfl) ⟨260655, by rfl⟩ : syracuseStep 695081 = 521311) B521311
theorem B924479 : Blo 409770 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B1383479 : Blo 409770 1383479 := bstep (se 1 (by rfl) ⟨1037609, by rfl⟩ : syracuseStep 1383479 = 2075219) B2075219
theorem B20028683 : Blo 409770 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B925415 : Blo 409770 925415 := bstep (se 1 (by rfl) ⟨694061, by rfl⟩ : syracuseStep 925415 = 1388123) B1388123
theorem B696073 : Blo 409770 696073 := bstep (se 2 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 696073 = 522055) B522055
theorem B6660083 : Blo 409770 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B1319915 : Blo 409770 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B698233 : Blo 409770 698233 := bstep (se 2 (by rfl) ⟨261837, by rfl⟩ : syracuseStep 698233 = 523675) B523675
theorem B1386395 : Blo 409770 1386395 := bstep (se 1 (by rfl) ⟨1039796, by rfl⟩ : syracuseStep 1386395 = 2079593) B2079593
theorem B7055261 : Blo 409770 7055261 := bstep (se 3 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 7055261 = 2645723) B2645723
theorem B1583135 : Blo 409770 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B1125083 : Blo 409770 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B7940861 : Blo 409770 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B3124007 : Blo 409770 3124007 := bstep (se 1 (by rfl) ⟨2343005, by rfl⟩ : syracuseStep 3124007 = 4686011) B4686011
theorem B3943367 : Blo 409770 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B928745 : Blo 409770 928745 := bstep (se 2 (by rfl) ⟨348279, by rfl⟩ : syracuseStep 928745 = 696559) B696559
theorem B929249 : Blo 409770 929249 := bstep (se 2 (by rfl) ⟨348468, by rfl⟩ : syracuseStep 929249 = 696937) B696937
theorem B438319 : Blo 409770 438319 := bstep (se 1 (by rfl) ⟨328739, by rfl⟩ : syracuseStep 438319 = 657479) B657479
theorem B4993163 : Blo 409770 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B2502809 : Blo 409770 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B439015 : Blo 409770 439015 := bstep (se 1 (by rfl) ⟨329261, by rfl⟩ : syracuseStep 439015 = 658523) B658523
theorem B2634551 : Blo 409770 2634551 := bstep (se 1 (by rfl) ⟨1975913, by rfl⟩ : syracuseStep 2634551 = 3951827) B3951827
theorem B930671 : Blo 409770 930671 := bstep (se 1 (by rfl) ⟨698003, by rfl⟩ : syracuseStep 930671 = 1396007) B1396007
theorem B1390715 : Blo 409770 1390715 := bstep (se 1 (by rfl) ⟨1043036, by rfl⟩ : syracuseStep 1390715 = 2086073) B2086073
theorem B9124163 : Blo 409770 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B834239 : Blo 409770 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B1391471 : Blo 409770 1391471 := bstep (se 1 (by rfl) ⟨1043603, by rfl⟩ : syracuseStep 1391471 = 2087207) B2087207
theorem B6798305 : Blo 409770 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B2670191 : Blo 409770 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B5947343 : Blo 409770 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B1392713 : Blo 409770 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B409851 : Blo 409770 409851 := bstep (se 1 (by rfl) ⟨307388, by rfl⟩ : syracuseStep 409851 = 614777) B614777
theorem B13418885 : Blo 409770 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B410047 : Blo 409770 410047 := bstep (se 1 (by rfl) ⟨307535, by rfl⟩ : syracuseStep 410047 = 615071) B615071
theorem B410271 : Blo 409770 410271 := bstep (se 1 (by rfl) ⟨307703, by rfl⟩ : syracuseStep 410271 = 615407) B615407
theorem B836315 : Blo 409770 836315 := bstep (se 1 (by rfl) ⟨627236, by rfl⟩ : syracuseStep 836315 = 1254473) B1254473
theorem B410343 : Blo 409770 410343 := bstep (se 1 (by rfl) ⟨307757, by rfl⟩ : syracuseStep 410343 = 615515) B615515
theorem B410351 : Blo 409770 410351 := bstep (se 1 (by rfl) ⟨307763, by rfl⟩ : syracuseStep 410351 = 615527) B615527
theorem B1393469 : Blo 409770 1393469 := bstep (se 3 (by rfl) ⟨261275, by rfl⟩ : syracuseStep 1393469 = 522551) B522551
theorem B410439 : Blo 409770 410439 := bstep (se 1 (by rfl) ⟨307829, by rfl⟩ : syracuseStep 410439 = 615659) B615659
theorem B410527 : Blo 409770 410527 := bstep (se 1 (by rfl) ⟨307895, by rfl⟩ : syracuseStep 410527 = 615791) B615791
theorem B410607 : Blo 409770 410607 := bstep (se 1 (by rfl) ⟨307955, by rfl⟩ : syracuseStep 410607 = 615911) B615911
theorem B410695 : Blo 409770 410695 := bstep (se 1 (by rfl) ⟨308021, by rfl⟩ : syracuseStep 410695 = 616043) B616043
theorem B410727 : Blo 409770 410727 := bstep (se 1 (by rfl) ⟨308045, by rfl⟩ : syracuseStep 410727 = 616091) B616091
theorem B410875 : Blo 409770 410875 := bstep (se 1 (by rfl) ⟨308156, by rfl⟩ : syracuseStep 410875 = 616313) B616313
theorem B411375 : Blo 409770 411375 := bstep (se 1 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 411375 = 617063) B617063
theorem B411559 : Blo 409770 411559 := bstep (se 1 (by rfl) ⟨308669, by rfl⟩ : syracuseStep 411559 = 617339) B617339
theorem B411739 : Blo 409770 411739 := bstep (se 1 (by rfl) ⟨308804, by rfl⟩ : syracuseStep 411739 = 617609) B617609
theorem B411775 : Blo 409770 411775 := bstep (se 1 (by rfl) ⟨308831, by rfl⟩ : syracuseStep 411775 = 617663) B617663
theorem B12830875 : Blo 409770 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B2672891 : Blo 409770 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B706811 : Blo 409770 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B5720539 : Blo 409770 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B412135 : Blo 409770 412135 := bstep (se 1 (by rfl) ⟨309101, by rfl⟩ : syracuseStep 412135 = 618203) B618203
theorem B412315 : Blo 409770 412315 := bstep (se 1 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 412315 = 618473) B618473
theorem B412327 : Blo 409770 412327 := bstep (se 1 (by rfl) ⟨309245, by rfl⟩ : syracuseStep 412327 = 618491) B618491
theorem B412351 : Blo 409770 412351 := bstep (se 1 (by rfl) ⟨309263, by rfl⟩ : syracuseStep 412351 = 618527) B618527
theorem B412367 : Blo 409770 412367 := bstep (se 1 (by rfl) ⟨309275, by rfl⟩ : syracuseStep 412367 = 618551) B618551
theorem B412447 : Blo 409770 412447 := bstep (se 1 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 412447 = 618671) B618671
theorem B2640701 : Blo 409770 2640701 := bstep (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) B990263
theorem B412583 : Blo 409770 412583 := bstep (se 1 (by rfl) ⟨309437, by rfl⟩ : syracuseStep 412583 = 618875) B618875
theorem B412763 : Blo 409770 412763 := bstep (se 1 (by rfl) ⟨309572, by rfl⟩ : syracuseStep 412763 = 619145) B619145
theorem B412903 : Blo 409770 412903 := bstep (se 1 (by rfl) ⟨309677, by rfl⟩ : syracuseStep 412903 = 619355) B619355
theorem B412923 : Blo 409770 412923 := bstep (se 1 (by rfl) ⟨309692, by rfl⟩ : syracuseStep 412923 = 619385) B619385
theorem B4672889 : Blo 409770 4672889 := bstep (se 2 (by rfl) ⟨1752333, by rfl⟩ : syracuseStep 4672889 = 3504667) B3504667
theorem B413343 : Blo 409770 413343 := bstep (se 1 (by rfl) ⟨310007, by rfl⟩ : syracuseStep 413343 = 620015) B620015
theorem B413423 : Blo 409770 413423 := bstep (se 1 (by rfl) ⟨310067, by rfl⟩ : syracuseStep 413423 = 620135) B620135
theorem B2510767 : Blo 409770 2510767 := bstep (se 1 (by rfl) ⟨1883075, by rfl⟩ : syracuseStep 2510767 = 3766151) B3766151
theorem B413727 : Blo 409770 413727 := bstep (se 1 (by rfl) ⟨310295, by rfl⟩ : syracuseStep 413727 = 620591) B620591
theorem B1560667 : Blo 409770 1560667 := bstep (se 1 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 1560667 = 2341001) B2341001
theorem B2675069 : Blo 409770 2675069 := bstep (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) B1003151
theorem B1528633 : Blo 409770 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B13390865 : Blo 409770 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B11883611 : Blo 409770 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B2381051 : Blo 409770 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B1758793 : Blo 409770 1758793 := bstep (se 2 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 1758793 = 1319095) B1319095
theorem B743015 : Blo 409770 743015 := bstep (se 1 (by rfl) ⟨557261, by rfl⟩ : syracuseStep 743015 = 1114523) B1114523
theorem B2545537 : Blo 409770 2545537 := bstep (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) B1909153
theorem B2349431 : Blo 409770 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B1759751 : Blo 409770 1759751 := bstep (se 1 (by rfl) ⟨1319813, by rfl⟩ : syracuseStep 1759751 = 2639627) B2639627
theorem B1039007 : Blo 409770 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B744161 : Blo 409770 744161 := bstep (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) B558121
theorem B2088179 : Blo 409770 2088179 := bstep (se 1 (by rfl) ⟨1566134, by rfl⟩ : syracuseStep 2088179 = 3132269) B3132269
theorem B1039787 : Blo 409770 1039787 := bstep (se 1 (by rfl) ⟨779840, by rfl⟩ : syracuseStep 1039787 = 1559681) B1559681
theorem B2514685 : Blo 409770 2514685 := bstep (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) B943007
theorem B3137615 : Blo 409770 3137615 := bstep (se 1 (by rfl) ⟨2353211, by rfl⟩ : syracuseStep 3137615 = 4706423) B4706423
theorem B614735 : Blo 409770 614735 := bstep (se 1 (by rfl) ⟨461051, by rfl⟩ : syracuseStep 614735 = 922103) B922103
theorem B1040951 : Blo 409770 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B1041083 : Blo 409770 1041083 := bstep (se 1 (by rfl) ⟨780812, by rfl⟩ : syracuseStep 1041083 = 1561625) B1561625
theorem B615239 : Blo 409770 615239 := bstep (se 1 (by rfl) ⟨461429, by rfl⟩ : syracuseStep 615239 = 922859) B922859
theorem B615305 : Blo 409770 615305 := bstep (se 2 (by rfl) ⟨230739, by rfl⟩ : syracuseStep 615305 = 461479) B461479
theorem B615401 : Blo 409770 615401 := bstep (se 2 (by rfl) ⟨230775, by rfl⟩ : syracuseStep 615401 = 461551) B461551
theorem B1565831 : Blo 409770 1565831 := bstep (se 1 (by rfl) ⟨1174373, by rfl⟩ : syracuseStep 1565831 = 2348747) B2348747
theorem B2090123 : Blo 409770 2090123 := bstep (se 1 (by rfl) ⟨1567592, by rfl⟩ : syracuseStep 2090123 = 3135185) B3135185
theorem B615647 : Blo 409770 615647 := bstep (se 1 (by rfl) ⟨461735, by rfl⟩ : syracuseStep 615647 = 923471) B923471
theorem B1172893 : Blo 409770 1172893 := bstep (se 3 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 1172893 = 439835) B439835
theorem B615839 : Blo 409770 615839 := bstep (se 1 (by rfl) ⟨461879, by rfl⟩ : syracuseStep 615839 = 923759) B923759
theorem B615887 : Blo 409770 615887 := bstep (se 1 (by rfl) ⟨461915, by rfl⟩ : syracuseStep 615887 = 923831) B923831
theorem B616073 : Blo 409770 616073 := bstep (se 2 (by rfl) ⟨231027, by rfl⟩ : syracuseStep 616073 = 462055) B462055
theorem B616127 : Blo 409770 616127 := bstep (se 1 (by rfl) ⟨462095, by rfl⟩ : syracuseStep 616127 = 924191) B924191
theorem B2090771 : Blo 409770 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B3532895 : Blo 409770 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B780425 : Blo 409770 780425 := bstep (se 2 (by rfl) ⟨292659, by rfl⟩ : syracuseStep 780425 = 585319) B585319
theorem B780455 : Blo 409770 780455 := bstep (se 1 (by rfl) ⟨585341, by rfl⟩ : syracuseStep 780455 = 1170683) B1170683
theorem B1566971 : Blo 409770 1566971 := bstep (se 1 (by rfl) ⟨1175228, by rfl⟩ : syracuseStep 1566971 = 2350457) B2350457
theorem B1043027 : Blo 409770 1043027 := bstep (se 1 (by rfl) ⟨782270, by rfl⟩ : syracuseStep 1043027 = 1564541) B1564541
theorem B518815 : Blo 409770 518815 := bstep (se 1 (by rfl) ⟨389111, by rfl⟩ : syracuseStep 518815 = 778223) B778223
theorem B781139 : Blo 409770 781139 := bstep (se 1 (by rfl) ⟨585854, by rfl⟩ : syracuseStep 781139 = 1171709) B1171709
theorem B781177 : Blo 409770 781177 := bstep (se 2 (by rfl) ⟨292941, by rfl⟩ : syracuseStep 781177 = 585883) B585883
theorem B7007147 : Blo 409770 7007147 := bstep (se 1 (by rfl) ⟨5255360, by rfl⟩ : syracuseStep 7007147 = 10510721) B10510721
theorem B2354305 : Blo 409770 2354305 := bstep (se 2 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 2354305 = 1765729) B1765729
theorem B1764499 : Blo 409770 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B1109245 : Blo 409770 1109245 := bstep (se 3 (by rfl) ⟨207983, by rfl⟩ : syracuseStep 1109245 = 415967) B415967
theorem B1043867 : Blo 409770 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B1568231 : Blo 409770 1568231 := bstep (se 1 (by rfl) ⟨1176173, by rfl⟩ : syracuseStep 1568231 = 2352347) B2352347
theorem B781807 : Blo 409770 781807 := bstep (se 1 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 781807 = 1172711) B1172711
theorem B8023643 : Blo 409770 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B618143 : Blo 409770 618143 := bstep (se 1 (by rfl) ⟨463607, by rfl⟩ : syracuseStep 618143 = 927215) B927215
theorem B880507 : Blo 409770 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B2093039 : Blo 409770 2093039 := bstep (se 1 (by rfl) ⟨1569779, by rfl⟩ : syracuseStep 2093039 = 3139559) B3139559
theorem B782399 : Blo 409770 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B2978171 : Blo 409770 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B618911 : Blo 409770 618911 := bstep (se 1 (by rfl) ⟨464183, by rfl⟩ : syracuseStep 618911 = 928367) B928367
theorem B619055 : Blo 409770 619055 := bstep (se 1 (by rfl) ⟨464291, by rfl⟩ : syracuseStep 619055 = 928583) B928583
theorem B1045345 : Blo 409770 1045345 := bstep (se 2 (by rfl) ⟨392004, by rfl⟩ : syracuseStep 1045345 = 784009) B784009
theorem B36238241 : Blo 409770 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B1569887 : Blo 409770 1569887 := bstep (se 1 (by rfl) ⟨1177415, by rfl⟩ : syracuseStep 1569887 = 2354831) B2354831
theorem B1570205 : Blo 409770 1570205 := bstep (se 3 (by rfl) ⟨294413, by rfl⟩ : syracuseStep 1570205 = 588827) B588827
theorem B620009 : Blo 409770 620009 := bstep (se 2 (by rfl) ⟨232503, by rfl⟩ : syracuseStep 620009 = 465007) B465007
theorem B1570387 : Blo 409770 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B882523 : Blo 409770 882523 := bstep (se 1 (by rfl) ⟨661892, by rfl⟩ : syracuseStep 882523 = 1323785) B1323785
theorem B784495 : Blo 409770 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B1669319 : Blo 409770 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B1669355 : Blo 409770 1669355 := bstep (se 1 (by rfl) ⟨1252016, by rfl⟩ : syracuseStep 1669355 = 2504033) B2504033
theorem B883361 : Blo 409770 883361 := bstep (se 2 (by rfl) ⟨331260, by rfl⟩ : syracuseStep 883361 = 662521) B662521
theorem B4684553 : Blo 409770 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B523199 : Blo 409770 523199 := bstep (se 1 (by rfl) ⟨392399, by rfl⟩ : syracuseStep 523199 = 784799) B784799
theorem B3506003 : Blo 409770 3506003 := bstep (se 1 (by rfl) ⟨2629502, by rfl⟩ : syracuseStep 3506003 = 5259005) B5259005
theorem B557543 : Blo 409770 557543 := bstep (se 1 (by rfl) ⟨418157, by rfl⟩ : syracuseStep 557543 = 836315) B836315
theorem B35783693 : Blo 409770 35783693 := bstep (se 3 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 35783693 = 13418885) B13418885
theorem B19990547 : Blo 409770 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B3115259 : Blo 409770 3115259 := bstep (se 1 (by rfl) ⟨2336444, by rfl⟩ : syracuseStep 3115259 = 4672889) B4672889
theorem B461119 : Blo 409770 461119 := bstep (se 1 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 461119 = 691679) B691679
theorem B2230945 : Blo 409770 2230945 := bstep (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) B1673209
theorem B2493665 : Blo 409770 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B462271 : Blo 409770 462271 := bstep (se 1 (by rfl) ⟨346703, by rfl⟩ : syracuseStep 462271 = 693407) B693407
theorem B691753 : Blo 409770 691753 := bstep (se 2 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 691753 = 518815) B518815
theorem B495343 : Blo 409770 495343 := bstep (se 1 (by rfl) ⟨371507, by rfl⟩ : syracuseStep 495343 = 743015) B743015
theorem B463099 : Blo 409770 463099 := bstep (se 1 (by rfl) ⟨347324, by rfl⟩ : syracuseStep 463099 = 694649) B694649
theorem B2167067 : Blo 409770 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B1478993 : Blo 409770 1478993 := bstep (se 2 (by rfl) ⟨554622, by rfl⟩ : syracuseStep 1478993 = 1109245) B1109245
theorem B692671 : Blo 409770 692671 := bstep (se 1 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 692671 = 1039007) B1039007
theorem B463387 : Blo 409770 463387 := bstep (se 1 (by rfl) ⟨347540, by rfl⟩ : syracuseStep 463387 = 695081) B695081
theorem B922319 : Blo 409770 922319 := bstep (se 1 (by rfl) ⟨691739, by rfl⟩ : syracuseStep 922319 = 1383479) B1383479
theorem B693191 : Blo 409770 693191 := bstep (se 1 (by rfl) ⟨519893, by rfl⟩ : syracuseStep 693191 = 1039787) B1039787
theorem B3347689 : Blo 409770 3347689 := bstep (se 2 (by rfl) ⟨1255383, by rfl⟩ : syracuseStep 3347689 = 2510767) B2510767
theorem B693967 : Blo 409770 693967 := bstep (se 1 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 693967 = 1040951) B1040951
theorem B694055 : Blo 409770 694055 := bstep (se 1 (by rfl) ⟨520541, by rfl⟩ : syracuseStep 694055 = 1041083) B1041083
theorem B924263 : Blo 409770 924263 := bstep (se 1 (by rfl) ⟨693197, by rfl⟩ : syracuseStep 924263 = 1386395) B1386395
theorem B1055423 : Blo 409770 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B924425 : Blo 409770 924425 := bstep (se 2 (by rfl) ⟨346659, by rfl⟩ : syracuseStep 924425 = 693319) B693319
theorem B695351 : Blo 409770 695351 := bstep (se 1 (by rfl) ⟨521513, by rfl⟩ : syracuseStep 695351 = 1043027) B1043027
theorem B2628911 : Blo 409770 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B695911 : Blo 409770 695911 := bstep (se 1 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 695911 = 1043867) B1043867
theorem B5349095 : Blo 409770 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B925865 : Blo 409770 925865 := bstep (se 2 (by rfl) ⟨347199, by rfl⟩ : syracuseStep 925865 = 694399) B694399
theorem B24158827 : Blo 409770 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B795433 : Blo 409770 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B3941369 : Blo 409770 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B927143 : Blo 409770 927143 := bstep (se 1 (by rfl) ⟨695357, by rfl⟩ : syracuseStep 927143 = 1390715) B1390715
theorem B3123035 : Blo 409770 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B927647 : Blo 409770 927647 := bstep (se 1 (by rfl) ⟨695735, by rfl⟩ : syracuseStep 927647 = 1391471) B1391471
theorem B4532203 : Blo 409770 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B3352913 : Blo 409770 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B928097 : Blo 409770 928097 := bstep (se 2 (by rfl) ⟨348036, by rfl⟩ : syracuseStep 928097 = 696073) B696073
theorem B1780127 : Blo 409770 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B2337335 : Blo 409770 2337335 := bstep (se 1 (by rfl) ⟨1753001, by rfl⟩ : syracuseStep 2337335 = 3506003) B3506003
theorem B928475 : Blo 409770 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B7908191 : Blo 409770 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B928979 : Blo 409770 928979 := bstep (se 1 (by rfl) ⟨696734, by rfl⟩ : syracuseStep 928979 = 1393469) B1393469
theorem B68431333 : Blo 409770 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B1781927 : Blo 409770 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B930977 : Blo 409770 930977 := bstep (se 2 (by rfl) ⟨349116, by rfl⟩ : syracuseStep 930977 = 698233) B698233
theorem B3519773 : Blo 409770 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B1783379 : Blo 409770 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B8927243 : Blo 409770 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B1587367 : Blo 409770 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B2341183 : Blo 409770 2341183 := bstep (se 1 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 2341183 = 3511775) B3511775
theorem B1392119 : Blo 409770 1392119 := bstep (se 1 (by rfl) ⟨1044089, by rfl⟩ : syracuseStep 1392119 = 2088179) B2088179
theorem B13352455 : Blo 409770 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B4440055 : Blo 409770 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B2080889 : Blo 409770 2080889 := bstep (se 2 (by rfl) ⟨780333, by rfl⟩ : syracuseStep 2080889 = 1560667) B1560667
theorem B409823 : Blo 409770 409823 := bstep (se 1 (by rfl) ⟨307367, by rfl⟩ : syracuseStep 409823 = 614735) B614735
theorem B6832421 : Blo 409770 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B2081213 : Blo 409770 2081213 := bstep (se 3 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 2081213 = 780455) B780455
theorem B410159 : Blo 409770 410159 := bstep (se 1 (by rfl) ⟨307619, by rfl⟩ : syracuseStep 410159 = 615239) B615239
theorem B410203 : Blo 409770 410203 := bstep (se 1 (by rfl) ⟨307652, by rfl⟩ : syracuseStep 410203 = 615305) B615305
theorem B410267 : Blo 409770 410267 := bstep (se 1 (by rfl) ⟨307700, by rfl⟩ : syracuseStep 410267 = 615401) B615401
theorem B1884829 : Blo 409770 1884829 := bstep (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) B706811
theorem B1393415 : Blo 409770 1393415 := bstep (se 1 (by rfl) ⟨1045061, by rfl⟩ : syracuseStep 1393415 = 2090123) B2090123
theorem B410431 : Blo 409770 410431 := bstep (se 1 (by rfl) ⟨307823, by rfl⟩ : syracuseStep 410431 = 615647) B615647
theorem B410559 : Blo 409770 410559 := bstep (se 1 (by rfl) ⟨307919, by rfl⟩ : syracuseStep 410559 = 615839) B615839
theorem B410591 : Blo 409770 410591 := bstep (se 1 (by rfl) ⟨307943, by rfl⟩ : syracuseStep 410591 = 615887) B615887
theorem B410715 : Blo 409770 410715 := bstep (se 1 (by rfl) ⟨308036, by rfl⟩ : syracuseStep 410715 = 616073) B616073
theorem B410751 : Blo 409770 410751 := bstep (se 1 (by rfl) ⟨308063, by rfl⟩ : syracuseStep 410751 = 616127) B616127
theorem B1393793 : Blo 409770 1393793 := bstep (se 2 (by rfl) ⟨522672, by rfl⟩ : syracuseStep 1393793 = 1045345) B1045345
theorem B1393847 : Blo 409770 1393847 := bstep (se 1 (by rfl) ⟨1045385, by rfl⟩ : syracuseStep 1393847 = 2090771) B2090771
theorem B836833 : Blo 409770 836833 := bstep (se 2 (by rfl) ⟨313812, by rfl⟩ : syracuseStep 836833 = 627625) B627625
theorem B4703507 : Blo 409770 4703507 := bstep (se 1 (by rfl) ⟨3527630, by rfl⟩ : syracuseStep 4703507 = 7055261) B7055261
theorem B5293907 : Blo 409770 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B2082671 : Blo 409770 2082671 := bstep (se 1 (by rfl) ⟨1562003, by rfl⟩ : syracuseStep 2082671 = 3124007) B3124007
theorem B1984429 : Blo 409770 1984429 := bstep (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) B744161
theorem B4671431 : Blo 409770 4671431 := bstep (se 1 (by rfl) ⟨3503573, by rfl⟩ : syracuseStep 4671431 = 7007147) B7007147
theorem B2345057 : Blo 409770 2345057 := bstep (se 2 (by rfl) ⟨879396, by rfl⟩ : syracuseStep 2345057 = 1758793) B1758793
theorem B412095 : Blo 409770 412095 := bstep (se 1 (by rfl) ⟨309071, by rfl⟩ : syracuseStep 412095 = 618143) B618143
theorem B1395197 : Blo 409770 1395197 := bstep (se 3 (by rfl) ⟨261599, by rfl⟩ : syracuseStep 1395197 = 523199) B523199
theorem B3394049 : Blo 409770 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B1395359 : Blo 409770 1395359 := bstep (se 1 (by rfl) ⟨1046519, by rfl⟩ : syracuseStep 1395359 = 2093039) B2093039
theorem B3328775 : Blo 409770 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B1985447 : Blo 409770 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B412607 : Blo 409770 412607 := bstep (se 1 (by rfl) ⟨309455, by rfl⟩ : syracuseStep 412607 = 618911) B618911
theorem B412703 : Blo 409770 412703 := bstep (se 1 (by rfl) ⟨309527, by rfl⟩ : syracuseStep 412703 = 619055) B619055
theorem B1756367 : Blo 409770 1756367 := bstep (se 1 (by rfl) ⟨1317275, by rfl⟩ : syracuseStep 1756367 = 2634551) B2634551
theorem B413339 : Blo 409770 413339 := bstep (se 1 (by rfl) ⟨310004, by rfl⟩ : syracuseStep 413339 = 620009) B620009
theorem B6082775 : Blo 409770 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B939431 : Blo 409770 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B2086397 : Blo 409770 2086397 := bstep (se 3 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 2086397 = 782399) B782399
theorem B1563857 : Blo 409770 1563857 := bstep (se 2 (by rfl) ⟨586446, by rfl⟩ : syracuseStep 1563857 = 1172893) B1172893
theorem B1760467 : Blo 409770 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B614759 : Blo 409770 614759 := bstep (se 1 (by rfl) ⟨461069, by rfl⟩ : syracuseStep 614759 = 922139) B922139
theorem B13525451 : Blo 409770 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B7627385 : Blo 409770 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B7922407 : Blo 409770 7922407 := bstep (se 1 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 7922407 = 11883611) B11883611
theorem B1041569 : Blo 409770 1041569 := bstep (se 2 (by rfl) ⟨390588, by rfl⟩ : syracuseStep 1041569 = 781177) B781177
theorem B3139073 : Blo 409770 3139073 := bstep (se 2 (by rfl) ⟨1177152, by rfl⟩ : syracuseStep 3139073 = 2354305) B2354305
theorem B2352665 : Blo 409770 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B1566287 : Blo 409770 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B8152709 : Blo 409770 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B1173167 : Blo 409770 1173167 := bstep (se 1 (by rfl) ⟨879875, by rfl⟩ : syracuseStep 1173167 = 1759751) B1759751
theorem B616319 : Blo 409770 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B1042409 : Blo 409770 1042409 := bstep (se 2 (by rfl) ⟨390903, by rfl⟩ : syracuseStep 1042409 = 781807) B781807
theorem B616943 : Blo 409770 616943 := bstep (se 1 (by rfl) ⟨462707, by rfl⟩ : syracuseStep 616943 = 925415) B925415
theorem B1174009 : Blo 409770 1174009 := bstep (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) B880507
theorem B2091743 : Blo 409770 2091743 := bstep (se 1 (by rfl) ⟨1568807, by rfl⟩ : syracuseStep 2091743 = 3137615) B3137615
theorem B584425 : Blo 409770 584425 := bstep (se 2 (by rfl) ⟨219159, by rfl⟩ : syracuseStep 584425 = 438319) B438319
theorem B1043887 : Blo 409770 1043887 := bstep (se 1 (by rfl) ⟨782915, by rfl⟩ : syracuseStep 1043887 = 1565831) B1565831
theorem B585353 : Blo 409770 585353 := bstep (se 2 (by rfl) ⟨219507, by rfl⟩ : syracuseStep 585353 = 439015) B439015
theorem B2355263 : Blo 409770 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B520283 : Blo 409770 520283 := bstep (se 1 (by rfl) ⟨390212, by rfl⟩ : syracuseStep 520283 = 780425) B780425
theorem B1044647 : Blo 409770 1044647 := bstep (se 1 (by rfl) ⟨783485, by rfl⟩ : syracuseStep 1044647 = 1566971) B1566971
theorem B750055 : Blo 409770 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B520759 : Blo 409770 520759 := bstep (se 1 (by rfl) ⟨390569, by rfl⟩ : syracuseStep 520759 = 781139) B781139
theorem B619163 : Blo 409770 619163 := bstep (se 1 (by rfl) ⟨464372, by rfl⟩ : syracuseStep 619163 = 928745) B928745
theorem B2093849 : Blo 409770 2093849 := bstep (se 2 (by rfl) ⟨785193, by rfl⟩ : syracuseStep 2093849 = 1570387) B1570387
theorem B619499 : Blo 409770 619499 := bstep (se 1 (by rfl) ⟨464624, by rfl⟩ : syracuseStep 619499 = 929249) B929249
theorem B1045487 : Blo 409770 1045487 := bstep (se 1 (by rfl) ⟨784115, by rfl⟩ : syracuseStep 1045487 = 1568231) B1568231
theorem B1176697 : Blo 409770 1176697 := bstep (se 2 (by rfl) ⟨441261, by rfl⟩ : syracuseStep 1176697 = 882523) B882523
theorem B1668539 : Blo 409770 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B1045993 : Blo 409770 1045993 := bstep (se 2 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 1045993 = 784495) B784495
theorem B620447 : Blo 409770 620447 := bstep (se 1 (by rfl) ⟨465335, by rfl⟩ : syracuseStep 620447 = 930671) B930671
theorem B1046591 : Blo 409770 1046591 := bstep (se 1 (by rfl) ⟨784943, by rfl⟩ : syracuseStep 1046591 = 1569887) B1569887
theorem B1046803 : Blo 409770 1046803 := bstep (se 1 (by rfl) ⟨785102, by rfl⟩ : syracuseStep 1046803 = 1570205) B1570205
theorem B1669513 : Blo 409770 1669513 := bstep (se 2 (by rfl) ⟨626067, by rfl⟩ : syracuseStep 1669513 = 1252135) B1252135
theorem B1112879 : Blo 409770 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B1112903 : Blo 409770 1112903 := bstep (se 1 (by rfl) ⟨834677, by rfl⟩ : syracuseStep 1112903 = 1669355) B1669355
theorem B588907 : Blo 409770 588907 := bstep (se 1 (by rfl) ⟨441680, by rfl⟩ : syracuseStep 588907 = 883361) B883361
theorem B556159 : Blo 409770 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B3964895 : Blo 409770 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B4554947 : Blo 409770 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B23855795 : Blo 409770 23855795 := bstep (se 1 (by rfl) ⟨17891846, by rfl⟩ : syracuseStep 23855795 = 35783693) B35783693
theorem B32211769 : Blo 409770 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B3114287 : Blo 409770 3114287 := bstep (se 1 (by rfl) ⟨2335715, by rfl⟩ : syracuseStep 3114287 = 4671431) B4671431
theorem B1115777 : Blo 409770 1115777 := bstep (se 2 (by rfl) ⟨418416, by rfl⟩ : syracuseStep 1115777 = 836833) B836833
theorem B1444711 : Blo 409770 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B462127 : Blo 409770 462127 := bstep (se 1 (by rfl) ⟨346595, by rfl⟩ : syracuseStep 462127 = 693191) B693191
theorem B11898373 : Blo 409770 11898373 := bstep (se 4 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 11898373 = 2230945) B2230945
theorem B626287 : Blo 409770 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B462703 : Blo 409770 462703 := bstep (se 1 (by rfl) ⟨347027, by rfl⟩ : syracuseStep 462703 = 694055) B694055
theorem B463567 : Blo 409770 463567 := bstep (se 1 (by rfl) ⟨347675, by rfl⟩ : syracuseStep 463567 = 695351) B695351
theorem B922337 : Blo 409770 922337 := bstep (se 2 (by rfl) ⟨345876, by rfl⟩ : syracuseStep 922337 = 691753) B691753
theorem B660457 : Blo 409770 660457 := bstep (se 2 (by rfl) ⟨247671, by rfl⟩ : syracuseStep 660457 = 495343) B495343
theorem B9016967 : Blo 409770 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B923561 : Blo 409770 923561 := bstep (se 2 (by rfl) ⟨346335, by rfl⟩ : syracuseStep 923561 = 692671) B692671
theorem B2627579 : Blo 409770 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B694345 : Blo 409770 694345 := bstep (se 2 (by rfl) ⟨260379, by rfl⟩ : syracuseStep 694345 = 520759) B520759
theorem B694379 : Blo 409770 694379 := bstep (se 1 (by rfl) ⟨520784, by rfl⟩ : syracuseStep 694379 = 1041569) B1041569
theorem B694939 : Blo 409770 694939 := bstep (se 1 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 694939 = 1042409) B1042409
theorem B9050797 : Blo 409770 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B2235275 : Blo 409770 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B1186751 : Blo 409770 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B4463585 : Blo 409770 4463585 := bstep (se 2 (by rfl) ⟨1673844, by rfl⟩ : syracuseStep 4463585 = 3347689) B3347689
theorem B925289 : Blo 409770 925289 := bstep (se 2 (by rfl) ⟨346983, by rfl⟩ : syracuseStep 925289 = 693967) B693967
theorem B1187951 : Blo 409770 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B696431 : Blo 409770 696431 := bstep (se 1 (by rfl) ⟨522323, by rfl⟩ : syracuseStep 696431 = 1044647) B1044647
theorem B3121577 : Blo 409770 3121577 := bstep (se 2 (by rfl) ⟨1170591, by rfl⟩ : syracuseStep 3121577 = 2341183) B2341183
theorem B696991 : Blo 409770 696991 := bstep (se 1 (by rfl) ⟨522743, by rfl⟩ : syracuseStep 696991 = 1045487) B1045487
theorem B1188919 : Blo 409770 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B697727 : Blo 409770 697727 := bstep (se 1 (by rfl) ⟨523295, by rfl⟩ : syracuseStep 697727 = 1046591) B1046591
theorem B17803273 : Blo 409770 17803273 := bstep (se 2 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 17803273 = 13352455) B13352455
theorem B927881 : Blo 409770 927881 := bstep (se 2 (by rfl) ⟨347955, by rfl⟩ : syracuseStep 927881 = 695911) B695911
theorem B928079 : Blo 409770 928079 := bstep (se 1 (by rfl) ⟨696059, by rfl⟩ : syracuseStep 928079 = 1392119) B1392119
theorem B1387259 : Blo 409770 1387259 := bstep (se 1 (by rfl) ⟨1040444, by rfl⟩ : syracuseStep 1387259 = 2080889) B2080889
theorem B1387421 : Blo 409770 1387421 := bstep (se 3 (by rfl) ⟨260141, by rfl⟩ : syracuseStep 1387421 = 520283) B520283
theorem B1387475 : Blo 409770 1387475 := bstep (se 1 (by rfl) ⟨1040606, by rfl⟩ : syracuseStep 1387475 = 2081213) B2081213
theorem B928943 : Blo 409770 928943 := bstep (se 1 (by rfl) ⟨696707, by rfl⟩ : syracuseStep 928943 = 1393415) B1393415
theorem B929195 : Blo 409770 929195 := bstep (se 1 (by rfl) ⟨696896, by rfl⟩ : syracuseStep 929195 = 1393793) B1393793
theorem B929231 : Blo 409770 929231 := bstep (se 1 (by rfl) ⟨696923, by rfl⟩ : syracuseStep 929231 = 1393847) B1393847
theorem B3943981 : Blo 409770 3943981 := bstep (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) B1478993
theorem B10563209 : Blo 409770 10563209 := bstep (se 2 (by rfl) ⟨3961203, by rfl⟩ : syracuseStep 10563209 = 7922407) B7922407
theorem B1060577 : Blo 409770 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B1388447 : Blo 409770 1388447 := bstep (se 1 (by rfl) ⟨1041335, by rfl⟩ : syracuseStep 1388447 = 2082671) B2082671
theorem B1486781 : Blo 409770 1486781 := bstep (se 3 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 1486781 = 557543) B557543
theorem B2076839 : Blo 409770 2076839 := bstep (se 1 (by rfl) ⟨1557629, by rfl⟩ : syracuseStep 2076839 = 3115259) B3115259
theorem B930131 : Blo 409770 930131 := bstep (se 1 (by rfl) ⟨697598, by rfl⟩ : syracuseStep 930131 = 1395197) B1395197
theorem B930239 : Blo 409770 930239 := bstep (se 1 (by rfl) ⟨697679, by rfl⟩ : syracuseStep 930239 = 1395359) B1395359
theorem B1323631 : Blo 409770 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B6042937 : Blo 409770 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B1390931 : Blo 409770 1390931 := bstep (se 1 (by rfl) ⟨1043198, by rfl⟩ : syracuseStep 1390931 = 2086397) B2086397
theorem B21740557 : Blo 409770 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B703615 : Blo 409770 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B1391849 : Blo 409770 1391849 := bstep (se 2 (by rfl) ⟨521943, by rfl⟩ : syracuseStep 1391849 = 1043887) B1043887
theorem B91241777 : Blo 409770 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B1752607 : Blo 409770 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B409839 : Blo 409770 409839 := bstep (se 1 (by rfl) ⟨307379, by rfl⟩ : syracuseStep 409839 = 614759) B614759
theorem B1000073 : Blo 409770 1000073 := bstep (se 2 (by rfl) ⟨375027, by rfl⟩ : syracuseStep 1000073 = 750055) B750055
theorem B2082023 : Blo 409770 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B410879 : Blo 409770 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B411295 : Blo 409770 411295 := bstep (se 1 (by rfl) ⟨308471, by rfl⟩ : syracuseStep 411295 = 616943) B616943
theorem B1558223 : Blo 409770 1558223 := bstep (se 1 (by rfl) ⟨1168667, by rfl⟩ : syracuseStep 1558223 = 2337335) B2337335
theorem B1394495 : Blo 409770 1394495 := bstep (se 1 (by rfl) ⟨1045871, by rfl⟩ : syracuseStep 1394495 = 2091743) B2091743
theorem B1394657 : Blo 409770 1394657 := bstep (se 2 (by rfl) ⟨522996, by rfl⟩ : syracuseStep 1394657 = 1045993) B1045993
theorem B2967677 : Blo 409770 2967677 := bstep (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) B1112879
theorem B2116489 : Blo 409770 2116489 := bstep (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) B1587367
theorem B1395737 : Blo 409770 1395737 := bstep (se 2 (by rfl) ⟨523401, by rfl⟩ : syracuseStep 1395737 = 1046803) B1046803
theorem B412775 : Blo 409770 412775 := bstep (se 1 (by rfl) ⟨309581, by rfl⟩ : syracuseStep 412775 = 619163) B619163
theorem B1395899 : Blo 409770 1395899 := bstep (se 1 (by rfl) ⟨1046924, by rfl⟩ : syracuseStep 1395899 = 2093849) B2093849
theorem B412999 : Blo 409770 412999 := bstep (se 1 (by rfl) ⟨309749, by rfl⟩ : syracuseStep 412999 = 619499) B619499
theorem B2346515 : Blo 409770 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B413631 : Blo 409770 413631 := bstep (se 1 (by rfl) ⟨310223, by rfl⟩ : syracuseStep 413631 = 620447) B620447
theorem B5951495 : Blo 409770 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B741545 : Blo 409770 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B2347289 : Blo 409770 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B1560941 : Blo 409770 1560941 := bstep (se 3 (by rfl) ⟨292676, by rfl⟩ : syracuseStep 1560941 = 585353) B585353
theorem B741935 : Blo 409770 741935 := bstep (se 1 (by rfl) ⟨556451, by rfl⟩ : syracuseStep 741935 = 1112903) B1112903
theorem B2643263 : Blo 409770 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B5920073 : Blo 409770 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B3135671 : Blo 409770 3135671 := bstep (se 1 (by rfl) ⟨2351753, by rfl⟩ : syracuseStep 3135671 = 4703507) B4703507
theorem B2513105 : Blo 409770 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B3529271 : Blo 409770 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B13327031 : Blo 409770 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B1563371 : Blo 409770 1563371 := bstep (se 1 (by rfl) ⟨1172528, by rfl⟩ : syracuseStep 1563371 = 2345057) B2345057
theorem B20339693 : Blo 409770 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B2219183 : Blo 409770 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B1170911 : Blo 409770 1170911 := bstep (se 1 (by rfl) ⟨878183, by rfl⟩ : syracuseStep 1170911 = 1756367) B1756367
theorem B1662443 : Blo 409770 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B2645905 : Blo 409770 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B4055183 : Blo 409770 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B614825 : Blo 409770 614825 := bstep (se 2 (by rfl) ⟨230559, by rfl⟩ : syracuseStep 614825 = 461119) B461119
theorem B614879 : Blo 409770 614879 := bstep (se 1 (by rfl) ⟨461159, by rfl⟩ : syracuseStep 614879 = 922319) B922319
theorem B1565345 : Blo 409770 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B779233 : Blo 409770 779233 := bstep (se 2 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 779233 = 584425) B584425
theorem B4449437 : Blo 409770 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B616175 : Blo 409770 616175 := bstep (se 1 (by rfl) ⟨462131, by rfl⟩ : syracuseStep 616175 = 924263) B924263
theorem B616283 : Blo 409770 616283 := bstep (se 1 (by rfl) ⟨462212, by rfl⟩ : syracuseStep 616283 = 924425) B924425
theorem B616361 : Blo 409770 616361 := bstep (se 2 (by rfl) ⟨231135, by rfl⟩ : syracuseStep 616361 = 462271) B462271
theorem B1042571 : Blo 409770 1042571 := bstep (se 1 (by rfl) ⟨781928, by rfl⟩ : syracuseStep 1042571 = 1563857) B1563857
theorem B3566063 : Blo 409770 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B617243 : Blo 409770 617243 := bstep (se 1 (by rfl) ⟨462932, by rfl⟩ : syracuseStep 617243 = 925865) B925865
theorem B617465 : Blo 409770 617465 := bstep (se 2 (by rfl) ⟨231549, by rfl⟩ : syracuseStep 617465 = 463099) B463099
theorem B617849 : Blo 409770 617849 := bstep (se 2 (by rfl) ⟨231693, by rfl⟩ : syracuseStep 617849 = 463387) B463387
theorem B618095 : Blo 409770 618095 := bstep (se 1 (by rfl) ⟨463571, by rfl⟩ : syracuseStep 618095 = 927143) B927143
theorem B2092715 : Blo 409770 2092715 := bstep (se 1 (by rfl) ⟨1569536, by rfl⟩ : syracuseStep 2092715 = 3139073) B3139073
theorem B1568443 : Blo 409770 1568443 := bstep (se 1 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 1568443 = 2352665) B2352665
theorem B1044191 : Blo 409770 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B782111 : Blo 409770 782111 := bstep (se 1 (by rfl) ⟨586583, by rfl⟩ : syracuseStep 782111 = 1173167) B1173167
theorem B618431 : Blo 409770 618431 := bstep (se 1 (by rfl) ⟨463823, by rfl⟩ : syracuseStep 618431 = 927647) B927647
theorem B1568929 : Blo 409770 1568929 := bstep (se 2 (by rfl) ⟨588348, by rfl⟩ : syracuseStep 1568929 = 1176697) B1176697
theorem B618731 : Blo 409770 618731 := bstep (se 1 (by rfl) ⟨464048, by rfl⟩ : syracuseStep 618731 = 928097) B928097
theorem B618983 : Blo 409770 618983 := bstep (se 1 (by rfl) ⟨464237, by rfl⟩ : syracuseStep 618983 = 928475) B928475
theorem B5272127 : Blo 409770 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B619319 : Blo 409770 619319 := bstep (se 1 (by rfl) ⟨464489, by rfl⟩ : syracuseStep 619319 = 928979) B928979
theorem B1570175 : Blo 409770 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B2226017 : Blo 409770 2226017 := bstep (se 2 (by rfl) ⟨834756, by rfl⟩ : syracuseStep 2226017 = 1669513) B1669513
theorem B620651 : Blo 409770 620651 := bstep (se 1 (by rfl) ⟨465488, by rfl⟩ : syracuseStep 620651 = 930977) B930977
theorem B785209 : Blo 409770 785209 := bstep (se 2 (by rfl) ⟨294453, by rfl⟩ : syracuseStep 785209 = 588907) B588907
theorem B3967663 : Blo 409770 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B494363 : Blo 409770 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B494623 : Blo 409770 494623 := bstep (se 1 (by rfl) ⟨370967, by rfl⟩ : syracuseStep 494623 = 741935) B741935
theorem B48270917 : Blo 409770 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B2821985 : Blo 409770 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B462919 : Blo 409770 462919 := bstep (se 1 (by rfl) ⟨347189, by rfl⟩ : syracuseStep 462919 = 694379) B694379
theorem B1675403 : Blo 409770 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B8884687 : Blo 409770 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B791167 : Blo 409770 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B15864497 : Blo 409770 15864497 := bstep (se 2 (by rfl) ⟨5949186, by rfl⟩ : syracuseStep 15864497 = 11898373) B11898373
theorem B1479455 : Blo 409770 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B464287 : Blo 409770 464287 := bstep (se 1 (by rfl) ⟨348215, by rfl⟩ : syracuseStep 464287 = 696431) B696431
theorem B465151 : Blo 409770 465151 := bstep (se 1 (by rfl) ⟨348863, by rfl⟩ : syracuseStep 465151 = 697727) B697727
theorem B9509501 : Blo 409770 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B695047 : Blo 409770 695047 := bstep (se 1 (by rfl) ⟨521285, by rfl⟩ : syracuseStep 695047 = 1042571) B1042571
theorem B924839 : Blo 409770 924839 := bstep (se 1 (by rfl) ⟨693629, by rfl⟩ : syracuseStep 924839 = 1387259) B1387259
theorem B924947 : Blo 409770 924947 := bstep (se 1 (by rfl) ⟨693710, by rfl⟩ : syracuseStep 924947 = 1387421) B1387421
theorem B924983 : Blo 409770 924983 := bstep (se 1 (by rfl) ⟨693737, by rfl⟩ : syracuseStep 924983 = 1387475) B1387475
theorem B696127 : Blo 409770 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B925631 : Blo 409770 925631 := bstep (se 1 (by rfl) ⟨694223, by rfl⟩ : syracuseStep 925631 = 1388447) B1388447
theorem B991187 : Blo 409770 991187 := bstep (se 1 (by rfl) ⟨743390, by rfl⟩ : syracuseStep 991187 = 1486781) B1486781
theorem B925793 : Blo 409770 925793 := bstep (se 2 (by rfl) ⟨347172, by rfl⟩ : syracuseStep 925793 = 694345) B694345
theorem B1384559 : Blo 409770 1384559 := bstep (se 1 (by rfl) ⟨1038419, by rfl⟩ : syracuseStep 1384559 = 2076839) B2076839
theorem B3514751 : Blo 409770 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B926585 : Blo 409770 926585 := bstep (se 2 (by rfl) ⟨347469, by rfl⟩ : syracuseStep 926585 = 694939) B694939
theorem B1484011 : Blo 409770 1484011 := bstep (se 1 (by rfl) ⟨1113008, by rfl⟩ : syracuseStep 1484011 = 2226017) B2226017
theorem B927287 : Blo 409770 927287 := bstep (se 1 (by rfl) ⟨695465, by rfl⟩ : syracuseStep 927287 = 1390931) B1390931
theorem B2336809 : Blo 409770 2336809 := bstep (se 2 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 2336809 = 1752607) B1752607
theorem B927899 : Blo 409770 927899 := bstep (se 1 (by rfl) ⟨695924, by rfl⟩ : syracuseStep 927899 = 1391849) B1391849
theorem B60827851 : Blo 409770 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B666715 : Blo 409770 666715 := bstep (se 1 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 666715 = 1000073) B1000073
theorem B15903863 : Blo 409770 15903863 := bstep (se 1 (by rfl) ⟨11927897, by rfl⟩ : syracuseStep 15903863 = 23855795) B23855795
theorem B1388015 : Blo 409770 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B2076191 : Blo 409770 2076191 := bstep (se 1 (by rfl) ⟨1557143, by rfl⟩ : syracuseStep 2076191 = 3114287) B3114287
theorem B929321 : Blo 409770 929321 := bstep (se 2 (by rfl) ⟨348495, by rfl⟩ : syracuseStep 929321 = 696991) B696991
theorem B929663 : Blo 409770 929663 := bstep (se 1 (by rfl) ⟨697247, by rfl⟩ : syracuseStep 929663 = 1394495) B1394495
theorem B929771 : Blo 409770 929771 := bstep (se 1 (by rfl) ⟨697328, by rfl⟩ : syracuseStep 929771 = 1394657) B1394657
theorem B1585225 : Blo 409770 1585225 := bstep (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) B1188919
theorem B1978451 : Blo 409770 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B930491 : Blo 409770 930491 := bstep (se 1 (by rfl) ⟨697868, by rfl⟩ : syracuseStep 930491 = 1395737) B1395737
theorem B930599 : Blo 409770 930599 := bstep (se 1 (by rfl) ⟨697949, by rfl⟩ : syracuseStep 930599 = 1395899) B1395899
theorem B23737697 : Blo 409770 23737697 := bstep (se 2 (by rfl) ⟨8901636, by rfl⟩ : syracuseStep 23737697 = 17803273) B17803273
theorem B3946715 : Blo 409770 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B1751719 : Blo 409770 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B1490183 : Blo 409770 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B5258641 : Blo 409770 5258641 := bstep (se 2 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 5258641 = 3943981) B3943981
theorem B835049 : Blo 409770 835049 := bstep (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) B626287
theorem B3522437 : Blo 409770 3522437 := bstep (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) B660457
theorem B2703455 : Blo 409770 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B409883 : Blo 409770 409883 := bstep (se 1 (by rfl) ⟨307412, by rfl⟩ : syracuseStep 409883 = 614825) B614825
theorem B2081051 : Blo 409770 2081051 := bstep (se 1 (by rfl) ⟨1560788, by rfl⟩ : syracuseStep 2081051 = 3121577) B3121577
theorem B409919 : Blo 409770 409919 := bstep (se 1 (by rfl) ⟨307439, by rfl⟩ : syracuseStep 409919 = 614879) B614879
theorem B2966291 : Blo 409770 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B410783 : Blo 409770 410783 := bstep (se 1 (by rfl) ⟨308087, by rfl⟩ : syracuseStep 410783 = 616175) B616175
theorem B410855 : Blo 409770 410855 := bstep (se 1 (by rfl) ⟨308141, by rfl⟩ : syracuseStep 410855 = 616283) B616283
theorem B410907 : Blo 409770 410907 := bstep (se 1 (by rfl) ⟨308180, by rfl⟩ : syracuseStep 410907 = 616361) B616361
theorem B411495 : Blo 409770 411495 := bstep (se 1 (by rfl) ⟨308621, by rfl⟩ : syracuseStep 411495 = 617243) B617243
theorem B411643 : Blo 409770 411643 := bstep (se 1 (by rfl) ⟨308732, by rfl⟩ : syracuseStep 411643 = 617465) B617465
theorem B411899 : Blo 409770 411899 := bstep (se 1 (by rfl) ⟨308924, by rfl⟩ : syracuseStep 411899 = 617849) B617849
theorem B412063 : Blo 409770 412063 := bstep (se 1 (by rfl) ⟨309047, by rfl⟩ : syracuseStep 412063 = 618095) B618095
theorem B1395143 : Blo 409770 1395143 := bstep (se 1 (by rfl) ⟨1046357, by rfl⟩ : syracuseStep 1395143 = 2092715) B2092715
theorem B707051 : Blo 409770 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B412287 : Blo 409770 412287 := bstep (se 1 (by rfl) ⟨309215, by rfl⟩ : syracuseStep 412287 = 618431) B618431
theorem B412487 : Blo 409770 412487 := bstep (se 1 (by rfl) ⟨309365, by rfl⟩ : syracuseStep 412487 = 618731) B618731
theorem B412655 : Blo 409770 412655 := bstep (se 1 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 412655 = 618983) B618983
theorem B412879 : Blo 409770 412879 := bstep (se 1 (by rfl) ⟨309659, by rfl⟩ : syracuseStep 412879 = 619319) B619319
theorem B28987409 : Blo 409770 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B413767 : Blo 409770 413767 := bstep (se 1 (by rfl) ⟨310325, by rfl⟩ : syracuseStep 413767 = 620651) B620651
theorem B938153 : Blo 409770 938153 := bstep (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) B703615
theorem B3527873 : Blo 409770 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B3036631 : Blo 409770 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B42949025 : Blo 409770 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B743851 : Blo 409770 743851 := bstep (se 1 (by rfl) ⟨557888, by rfl⟩ : syracuseStep 743851 = 1115777) B1115777
theorem B1038815 : Blo 409770 1038815 := bstep (se 1 (by rfl) ⟨779111, by rfl⟩ : syracuseStep 1038815 = 1558223) B1558223
theorem B12671477 : Blo 409770 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B1038977 : Blo 409770 1038977 := bstep (se 2 (by rfl) ⟨389616, by rfl⟩ : syracuseStep 1038977 = 779233) B779233
theorem B1564343 : Blo 409770 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B1564859 : Blo 409770 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B1040627 : Blo 409770 1040627 := bstep (se 1 (by rfl) ⟨780470, by rfl⟩ : syracuseStep 1040627 = 1560941) B1560941
theorem B614891 : Blo 409770 614891 := bstep (se 1 (by rfl) ⟨461168, by rfl⟩ : syracuseStep 614891 = 922337) B922337
theorem B1762175 : Blo 409770 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B1926281 : Blo 409770 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B615707 : Blo 409770 615707 := bstep (se 1 (by rfl) ⟨461780, by rfl⟩ : syracuseStep 615707 = 923561) B923561
theorem B2090447 : Blo 409770 2090447 := bstep (se 1 (by rfl) ⟨1567835, by rfl⟩ : syracuseStep 2090447 = 3135671) B3135671
theorem B24045245 : Blo 409770 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B2352847 : Blo 409770 2352847 := bstep (se 1 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 2352847 = 3529271) B3529271
theorem B616169 : Blo 409770 616169 := bstep (se 2 (by rfl) ⟨231063, by rfl⟩ : syracuseStep 616169 = 462127) B462127
theorem B1042247 : Blo 409770 1042247 := bstep (se 1 (by rfl) ⟨781685, by rfl⟩ : syracuseStep 1042247 = 1563371) B1563371
theorem B2975723 : Blo 409770 2975723 := bstep (se 1 (by rfl) ⟨2231792, by rfl⟩ : syracuseStep 2975723 = 4463585) B4463585
theorem B13559795 : Blo 409770 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B2091257 : Blo 409770 2091257 := bstep (se 2 (by rfl) ⟨784221, by rfl⟩ : syracuseStep 2091257 = 1568443) B1568443
theorem B780607 : Blo 409770 780607 := bstep (se 1 (by rfl) ⟨585455, by rfl⟩ : syracuseStep 780607 = 1170911) B1170911
theorem B1108295 : Blo 409770 1108295 := bstep (se 1 (by rfl) ⟨831221, by rfl⟩ : syracuseStep 1108295 = 1662443) B1662443
theorem B616859 : Blo 409770 616859 := bstep (se 1 (by rfl) ⟨462644, by rfl⟩ : syracuseStep 616859 = 925289) B925289
theorem B616937 : Blo 409770 616937 := bstep (se 2 (by rfl) ⟨231351, by rfl⟩ : syracuseStep 616937 = 462703) B462703
theorem B2091905 : Blo 409770 2091905 := bstep (se 2 (by rfl) ⟨784464, by rfl⟩ : syracuseStep 2091905 = 1568929) B1568929
theorem B1043563 : Blo 409770 1043563 := bstep (se 1 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 1043563 = 1565345) B1565345
theorem B1764841 : Blo 409770 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B618089 : Blo 409770 618089 := bstep (se 2 (by rfl) ⟨231783, by rfl⟩ : syracuseStep 618089 = 463567) B463567
theorem B618587 : Blo 409770 618587 := bstep (se 1 (by rfl) ⟨463940, by rfl⟩ : syracuseStep 618587 = 927881) B927881
theorem B618719 : Blo 409770 618719 := bstep (se 1 (by rfl) ⟨464039, by rfl⟩ : syracuseStep 618719 = 928079) B928079
theorem B8057249 : Blo 409770 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B619295 : Blo 409770 619295 := bstep (se 1 (by rfl) ⟨464471, by rfl⟩ : syracuseStep 619295 = 928943) B928943
theorem B619463 : Blo 409770 619463 := bstep (se 1 (by rfl) ⟨464597, by rfl⟩ : syracuseStep 619463 = 929195) B929195
theorem B619487 : Blo 409770 619487 := bstep (se 1 (by rfl) ⟨464615, by rfl⟩ : syracuseStep 619487 = 929231) B929231
theorem B7042139 : Blo 409770 7042139 := bstep (se 1 (by rfl) ⟨5281604, by rfl⟩ : syracuseStep 7042139 = 10563209) B10563209
theorem B521407 : Blo 409770 521407 := bstep (se 1 (by rfl) ⟨391055, by rfl⟩ : syracuseStep 521407 = 782111) B782111
theorem B620087 : Blo 409770 620087 := bstep (se 1 (by rfl) ⟨465065, by rfl⟩ : syracuseStep 620087 = 930131) B930131
theorem B620159 : Blo 409770 620159 := bstep (se 1 (by rfl) ⟨465119, by rfl⟩ : syracuseStep 620159 = 930239) B930239
theorem B1046783 : Blo 409770 1046783 := bstep (se 1 (by rfl) ⟨785087, by rfl⟩ : syracuseStep 1046783 = 1570175) B1570175
theorem B1046945 : Blo 409770 1046945 := bstep (se 2 (by rfl) ⟨392604, by rfl⟩ : syracuseStep 1046945 = 785209) B785209
theorem B77299757 : Blo 409770 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B1802303 : Blo 409770 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B3115745 : Blo 409770 3115745 := bstep (se 2 (by rfl) ⟨1168404, by rfl⟩ : syracuseStep 3115745 = 2336809) B2336809
theorem B1116935 : Blo 409770 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B81103801 : Blo 409770 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B986303 : Blo 409770 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B659497 : Blo 409770 659497 := bstep (se 2 (by rfl) ⟨247311, by rfl⟩ : syracuseStep 659497 = 494623) B494623
theorem B888953 : Blo 409770 888953 := bstep (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) B666715
theorem B692543 : Blo 409770 692543 := bstep (se 1 (by rfl) ⟨519407, by rfl⟩ : syracuseStep 692543 = 1038815) B1038815
theorem B692651 : Blo 409770 692651 := bstep (se 1 (by rfl) ⟨519488, by rfl⟩ : syracuseStep 692651 = 1038977) B1038977
theorem B660791 : Blo 409770 660791 := bstep (se 1 (by rfl) ⟨495593, by rfl⟩ : syracuseStep 660791 = 991187) B991187
theorem B923039 : Blo 409770 923039 := bstep (se 1 (by rfl) ⟨692279, by rfl⟩ : syracuseStep 923039 = 1384559) B1384559
theorem B693751 : Blo 409770 693751 := bstep (se 1 (by rfl) ⟨520313, by rfl⟩ : syracuseStep 693751 = 1040627) B1040627
theorem B1284187 : Blo 409770 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1054889 : Blo 409770 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B16030163 : Blo 409770 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B694831 : Blo 409770 694831 := bstep (se 1 (by rfl) ⟨521123, by rfl⟩ : syracuseStep 694831 = 1042247) B1042247
theorem B695209 : Blo 409770 695209 := bstep (se 2 (by rfl) ⟨260703, by rfl⟩ : syracuseStep 695209 = 521407) B521407
theorem B1318301 : Blo 409770 1318301 := bstep (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) B494363
theorem B925343 : Blo 409770 925343 := bstep (se 1 (by rfl) ⟨694007, by rfl⟩ : syracuseStep 925343 = 1388015) B1388015
theorem B1384127 : Blo 409770 1384127 := bstep (se 1 (by rfl) ⟨1038095, by rfl⟩ : syracuseStep 1384127 = 2076191) B2076191
theorem B1318967 : Blo 409770 1318967 := bstep (se 1 (by rfl) ⟨989225, by rfl⟩ : syracuseStep 1318967 = 1978451) B1978451
theorem B991801 : Blo 409770 991801 := bstep (se 2 (by rfl) ⟨371925, by rfl⟩ : syracuseStep 991801 = 743851) B743851
theorem B4694759 : Blo 409770 4694759 := bstep (se 1 (by rfl) ⟨3521069, by rfl⟩ : syracuseStep 4694759 = 7042139) B7042139
theorem B2335625 : Blo 409770 2335625 := bstep (se 2 (by rfl) ⟨875859, by rfl⟩ : syracuseStep 2335625 = 1751719) B1751719
theorem B926729 : Blo 409770 926729 := bstep (se 2 (by rfl) ⟨347523, by rfl⟩ : syracuseStep 926729 = 695047) B695047
theorem B2631143 : Blo 409770 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B697855 : Blo 409770 697855 := bstep (se 1 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 697855 = 1046783) B1046783
theorem B128722445 : Blo 409770 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B697963 : Blo 409770 697963 := bstep (se 1 (by rfl) ⟨523472, by rfl⟩ : syracuseStep 697963 = 1046945) B1046945
theorem B993455 : Blo 409770 993455 := bstep (se 1 (by rfl) ⟨745091, by rfl⟩ : syracuseStep 993455 = 1490183) B1490183
theorem B928169 : Blo 409770 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B1387367 : Blo 409770 1387367 := bstep (se 1 (by rfl) ⟨1040525, by rfl⟩ : syracuseStep 1387367 = 2081051) B2081051
theorem B2501741 : Blo 409770 2501741 := bstep (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) B938153
theorem B1977527 : Blo 409770 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B930095 : Blo 409770 930095 := bstep (se 1 (by rfl) ⟨697571, by rfl⟩ : syracuseStep 930095 = 1395143) B1395143
theorem B1978681 : Blo 409770 1978681 := bstep (se 2 (by rfl) ⟨742005, by rfl⟩ : syracuseStep 1978681 = 1484011) B1484011
theorem B471367 : Blo 409770 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B4699133 : Blo 409770 4699133 := bstep (se 3 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 4699133 = 1762175) B1762175
theorem B1881323 : Blo 409770 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B5290217 : Blo 409770 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B1391417 : Blo 409770 1391417 := bstep (se 2 (by rfl) ⟨521781, by rfl⟩ : syracuseStep 1391417 = 1043563) B1043563
theorem B6339667 : Blo 409770 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B2113633 : Blo 409770 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B2343167 : Blo 409770 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B409927 : Blo 409770 409927 := bstep (se 1 (by rfl) ⟨307445, by rfl⟩ : syracuseStep 409927 = 614891) B614891
theorem B11846249 : Blo 409770 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B410471 : Blo 409770 410471 := bstep (se 1 (by rfl) ⟨307853, by rfl⟩ : syracuseStep 410471 = 615707) B615707
theorem B1393631 : Blo 409770 1393631 := bstep (se 1 (by rfl) ⟨1045223, by rfl⟩ : syracuseStep 1393631 = 2090447) B2090447
theorem B410779 : Blo 409770 410779 := bstep (se 1 (by rfl) ⟨308084, by rfl⟩ : syracuseStep 410779 = 616169) B616169
theorem B1983815 : Blo 409770 1983815 := bstep (se 1 (by rfl) ⟨1487861, by rfl⟩ : syracuseStep 1983815 = 2975723) B2975723
theorem B1394171 : Blo 409770 1394171 := bstep (se 1 (by rfl) ⟨1045628, by rfl⟩ : syracuseStep 1394171 = 2091257) B2091257
theorem B738863 : Blo 409770 738863 := bstep (se 1 (by rfl) ⟨554147, by rfl⟩ : syracuseStep 738863 = 1108295) B1108295
theorem B411239 : Blo 409770 411239 := bstep (se 1 (by rfl) ⟨308429, by rfl⟩ : syracuseStep 411239 = 616859) B616859
theorem B411291 : Blo 409770 411291 := bstep (se 1 (by rfl) ⟨308468, by rfl⟩ : syracuseStep 411291 = 616937) B616937
theorem B1394603 : Blo 409770 1394603 := bstep (se 1 (by rfl) ⟨1045952, by rfl⟩ : syracuseStep 1394603 = 2091905) B2091905
theorem B4048841 : Blo 409770 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B10602575 : Blo 409770 10602575 := bstep (se 1 (by rfl) ⟨7951931, by rfl⟩ : syracuseStep 10602575 = 15903863) B15903863
theorem B412059 : Blo 409770 412059 := bstep (se 1 (by rfl) ⟨309044, by rfl⟩ : syracuseStep 412059 = 618089) B618089
theorem B412391 : Blo 409770 412391 := bstep (se 1 (by rfl) ⟨309293, by rfl⟩ : syracuseStep 412391 = 618587) B618587
theorem B412479 : Blo 409770 412479 := bstep (se 1 (by rfl) ⟨309359, by rfl⟩ : syracuseStep 412479 = 618719) B618719
theorem B412863 : Blo 409770 412863 := bstep (se 1 (by rfl) ⟨309647, by rfl⟩ : syracuseStep 412863 = 619295) B619295
theorem B412975 : Blo 409770 412975 := bstep (se 1 (by rfl) ⟨309731, by rfl⟩ : syracuseStep 412975 = 619463) B619463
theorem B412991 : Blo 409770 412991 := bstep (se 1 (by rfl) ⟨309743, by rfl⟩ : syracuseStep 412991 = 619487) B619487
theorem B413391 : Blo 409770 413391 := bstep (se 1 (by rfl) ⟨310043, by rfl⟩ : syracuseStep 413391 = 620087) B620087
theorem B413439 : Blo 409770 413439 := bstep (se 1 (by rfl) ⟨310079, by rfl⟩ : syracuseStep 413439 = 620159) B620159
theorem B2348291 : Blo 409770 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B3137129 : Blo 409770 3137129 := bstep (se 2 (by rfl) ⟨1176423, by rfl⟩ : syracuseStep 3137129 = 2352847) B2352847
theorem B1040809 : Blo 409770 1040809 := bstep (se 2 (by rfl) ⟨390303, by rfl⟩ : syracuseStep 1040809 = 780607) B780607
theorem B10576331 : Blo 409770 10576331 := bstep (se 1 (by rfl) ⟨7932248, by rfl⟩ : syracuseStep 10576331 = 15864497) B15864497
theorem B2351915 : Blo 409770 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B28632683 : Blo 409770 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B8447651 : Blo 409770 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B2353121 : Blo 409770 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B616559 : Blo 409770 616559 := bstep (se 1 (by rfl) ⟨462419, by rfl⟩ : syracuseStep 616559 = 924839) B924839
theorem B616631 : Blo 409770 616631 := bstep (se 1 (by rfl) ⟨462473, by rfl⟩ : syracuseStep 616631 = 924947) B924947
theorem B616655 : Blo 409770 616655 := bstep (se 1 (by rfl) ⟨462491, by rfl⟩ : syracuseStep 616655 = 924983) B924983
theorem B1042895 : Blo 409770 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B617087 : Blo 409770 617087 := bstep (se 1 (by rfl) ⟨462815, by rfl⟩ : syracuseStep 617087 = 925631) B925631
theorem B617195 : Blo 409770 617195 := bstep (se 1 (by rfl) ⟨462896, by rfl⟩ : syracuseStep 617195 = 925793) B925793
theorem B617225 : Blo 409770 617225 := bstep (se 2 (by rfl) ⟨231459, by rfl⟩ : syracuseStep 617225 = 462919) B462919
theorem B1043239 : Blo 409770 1043239 := bstep (se 1 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 1043239 = 1564859) B1564859
theorem B617723 : Blo 409770 617723 := bstep (se 1 (by rfl) ⟨463292, by rfl⟩ : syracuseStep 617723 = 926585) B926585
theorem B618191 : Blo 409770 618191 := bstep (se 1 (by rfl) ⟨463643, by rfl⟩ : syracuseStep 618191 = 927287) B927287
theorem B9039863 : Blo 409770 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B618599 : Blo 409770 618599 := bstep (se 1 (by rfl) ⟨463949, by rfl⟩ : syracuseStep 618599 = 927899) B927899
theorem B619049 : Blo 409770 619049 := bstep (se 2 (by rfl) ⟨232143, by rfl⟩ : syracuseStep 619049 = 464287) B464287
theorem B619547 : Blo 409770 619547 := bstep (se 1 (by rfl) ⟨464660, by rfl⟩ : syracuseStep 619547 = 929321) B929321
theorem B619775 : Blo 409770 619775 := bstep (se 1 (by rfl) ⟨464831, by rfl⟩ : syracuseStep 619775 = 929663) B929663
theorem B619847 : Blo 409770 619847 := bstep (se 1 (by rfl) ⟨464885, by rfl⟩ : syracuseStep 619847 = 929771) B929771
theorem B5371499 : Blo 409770 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B620201 : Blo 409770 620201 := bstep (se 2 (by rfl) ⟨232575, by rfl⟩ : syracuseStep 620201 = 465151) B465151
theorem B620327 : Blo 409770 620327 := bstep (se 1 (by rfl) ⟨465245, by rfl⟩ : syracuseStep 620327 = 930491) B930491
theorem B620399 : Blo 409770 620399 := bstep (se 1 (by rfl) ⟨465299, by rfl⟩ : syracuseStep 620399 = 930599) B930599
theorem B15825131 : Blo 409770 15825131 := bstep (se 1 (by rfl) ⟨11868848, by rfl⟩ : syracuseStep 15825131 = 23737697) B23737697
theorem B7011521 : Blo 409770 7011521 := bstep (se 2 (by rfl) ⟨2629320, by rfl⟩ : syracuseStep 7011521 = 5258641) B5258641
theorem B556699 : Blo 409770 556699 := bstep (se 1 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 556699 = 835049) B835049
theorem B7897499 : Blo 409770 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B11272709 : Blo 409770 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B492575 : Blo 409770 492575 := bstep (se 1 (by rfl) ⟨369431, by rfl⟩ : syracuseStep 492575 = 738863) B738863
theorem B461695 : Blo 409770 461695 := bstep (se 1 (by rfl) ⟨346271, by rfl⟩ : syracuseStep 461695 = 692543) B692543
theorem B461767 : Blo 409770 461767 := bstep (se 1 (by rfl) ⟨346325, by rfl⟩ : syracuseStep 461767 = 692651) B692651
theorem B108138401 : Blo 409770 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B922751 : Blo 409770 922751 := bstep (se 1 (by rfl) ⟨692063, by rfl⟩ : syracuseStep 922751 = 1384127) B1384127
theorem B7050887 : Blo 409770 7050887 := bstep (se 1 (by rfl) ⟨5288165, by rfl⟩ : syracuseStep 7050887 = 10576331) B10576331
theorem B628489 : Blo 409770 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B662303 : Blo 409770 662303 := bstep (se 1 (by rfl) ⟨496727, by rfl⟩ : syracuseStep 662303 = 993455) B993455
theorem B695263 : Blo 409770 695263 := bstep (se 1 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 695263 = 1042895) B1042895
theorem B924911 : Blo 409770 924911 := bstep (se 1 (by rfl) ⟨693683, by rfl⟩ : syracuseStep 924911 = 1387367) B1387367
theorem B925001 : Blo 409770 925001 := bstep (se 2 (by rfl) ⟨346875, by rfl⟩ : syracuseStep 925001 = 693751) B693751
theorem B1318351 : Blo 409770 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B1712249 : Blo 409770 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B2630141 : Blo 409770 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B926441 : Blo 409770 926441 := bstep (se 2 (by rfl) ⟨347415, by rfl⟩ : syracuseStep 926441 = 694831) B694831
theorem B1254215 : Blo 409770 1254215 := bstep (se 1 (by rfl) ⟨940661, by rfl⟩ : syracuseStep 1254215 = 1881323) B1881323
theorem B3580999 : Blo 409770 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B926945 : Blo 409770 926945 := bstep (se 2 (by rfl) ⟨347604, by rfl⟩ : syracuseStep 926945 = 695209) B695209
theorem B927611 : Blo 409770 927611 := bstep (se 1 (by rfl) ⟨695708, by rfl⟩ : syracuseStep 927611 = 1391417) B1391417
theorem B2370541 : Blo 409770 2370541 := bstep (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) B888953
theorem B1387745 : Blo 409770 1387745 := bstep (se 2 (by rfl) ⟨520404, by rfl⟩ : syracuseStep 1387745 = 1040809) B1040809
theorem B929087 : Blo 409770 929087 := bstep (se 1 (by rfl) ⟨696815, by rfl⟩ : syracuseStep 929087 = 1393631) B1393631
theorem B1322401 : Blo 409770 1322401 := bstep (se 2 (by rfl) ⟨495900, by rfl⟩ : syracuseStep 1322401 = 991801) B991801
theorem B1322543 : Blo 409770 1322543 := bstep (se 1 (by rfl) ⟨991907, by rfl⟩ : syracuseStep 1322543 = 1983815) B1983815
theorem B929447 : Blo 409770 929447 := bstep (se 1 (by rfl) ⟨697085, by rfl⟩ : syracuseStep 929447 = 1394171) B1394171
theorem B929735 : Blo 409770 929735 := bstep (se 1 (by rfl) ⟨697301, by rfl⟩ : syracuseStep 929735 = 1394603) B1394603
theorem B2699227 : Blo 409770 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B2077163 : Blo 409770 2077163 := bstep (se 1 (by rfl) ⟨1557872, by rfl⟩ : syracuseStep 2077163 = 3115745) B3115745
theorem B930473 : Blo 409770 930473 := bstep (se 2 (by rfl) ⟨348927, by rfl⟩ : syracuseStep 930473 = 697855) B697855
theorem B930617 : Blo 409770 930617 := bstep (se 2 (by rfl) ⟨348981, by rfl⟩ : syracuseStep 930617 = 697963) B697963
theorem B440527 : Blo 409770 440527 := bstep (se 1 (by rfl) ⟨330395, by rfl⟩ : syracuseStep 440527 = 660791) B660791
theorem B1390985 : Blo 409770 1390985 := bstep (se 2 (by rfl) ⟨521619, by rfl⟩ : syracuseStep 1390985 = 1043239) B1043239
theorem B703259 : Blo 409770 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B2638241 : Blo 409770 2638241 := bstep (se 2 (by rfl) ⟨989340, by rfl⟩ : syracuseStep 2638241 = 1978681) B1978681
theorem B3129839 : Blo 409770 3129839 := bstep (se 1 (by rfl) ⟨2347379, by rfl⟩ : syracuseStep 3129839 = 4694759) B4694759
theorem B1557083 : Blo 409770 1557083 := bstep (se 1 (by rfl) ⟨1167812, by rfl⟩ : syracuseStep 1557083 = 2335625) B2335625
theorem B1754095 : Blo 409770 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B19088455 : Blo 409770 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B42747101 : Blo 409770 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B411039 : Blo 409770 411039 := bstep (se 1 (by rfl) ⟨308279, by rfl⟩ : syracuseStep 411039 = 616559) B616559
theorem B411087 : Blo 409770 411087 := bstep (se 1 (by rfl) ⟨308315, by rfl⟩ : syracuseStep 411087 = 616631) B616631
theorem B411103 : Blo 409770 411103 := bstep (se 1 (by rfl) ⟨308327, by rfl⟩ : syracuseStep 411103 = 616655) B616655
theorem B411391 : Blo 409770 411391 := bstep (se 1 (by rfl) ⟨308543, by rfl⟩ : syracuseStep 411391 = 617087) B617087
theorem B411463 : Blo 409770 411463 := bstep (se 1 (by rfl) ⟨308597, by rfl⟩ : syracuseStep 411463 = 617195) B617195
theorem B411483 : Blo 409770 411483 := bstep (se 1 (by rfl) ⟨308612, by rfl⟩ : syracuseStep 411483 = 617225) B617225
theorem B411815 : Blo 409770 411815 := bstep (se 1 (by rfl) ⟨308861, by rfl⟩ : syracuseStep 411815 = 617723) B617723
theorem B412127 : Blo 409770 412127 := bstep (se 1 (by rfl) ⟨309095, by rfl⟩ : syracuseStep 412127 = 618191) B618191
theorem B412399 : Blo 409770 412399 := bstep (se 1 (by rfl) ⟨309299, by rfl⟩ : syracuseStep 412399 = 618599) B618599
theorem B412699 : Blo 409770 412699 := bstep (se 1 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 412699 = 619049) B619049
theorem B3132755 : Blo 409770 3132755 := bstep (se 1 (by rfl) ⟨2349566, by rfl⟩ : syracuseStep 3132755 = 4699133) B4699133
theorem B413031 : Blo 409770 413031 := bstep (se 1 (by rfl) ⟨309773, by rfl⟩ : syracuseStep 413031 = 619547) B619547
theorem B413183 : Blo 409770 413183 := bstep (se 1 (by rfl) ⟨309887, by rfl⟩ : syracuseStep 413183 = 619775) B619775
theorem B413231 : Blo 409770 413231 := bstep (se 1 (by rfl) ⟨309923, by rfl⟩ : syracuseStep 413231 = 619847) B619847
theorem B413467 : Blo 409770 413467 := bstep (se 1 (by rfl) ⟨310100, by rfl⟩ : syracuseStep 413467 = 620201) B620201
theorem B413551 : Blo 409770 413551 := bstep (se 1 (by rfl) ⟨310163, by rfl⟩ : syracuseStep 413551 = 620327) B620327
theorem B413599 : Blo 409770 413599 := bstep (se 1 (by rfl) ⟨310199, by rfl⟩ : syracuseStep 413599 = 620399) B620399
theorem B3526811 : Blo 409770 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B4674347 : Blo 409770 4674347 := bstep (se 1 (by rfl) ⟨3505760, by rfl⟩ : syracuseStep 4674347 = 7011521) B7011521
theorem B742265 : Blo 409770 742265 := bstep (se 2 (by rfl) ⟨278349, by rfl⟩ : syracuseStep 742265 = 556699) B556699
theorem B51533171 : Blo 409770 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B1201535 : Blo 409770 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B1562111 : Blo 409770 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B7068383 : Blo 409770 7068383 := bstep (se 1 (by rfl) ⟨5301287, by rfl⟩ : syracuseStep 7068383 = 10602575) B10602575
theorem B744623 : Blo 409770 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B1565527 : Blo 409770 1565527 := bstep (se 1 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 1565527 = 2348291) B2348291
theorem B615359 : Blo 409770 615359 := bstep (se 1 (by rfl) ⟨461519, by rfl⟩ : syracuseStep 615359 = 923039) B923039
theorem B878867 : Blo 409770 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B2091419 : Blo 409770 2091419 := bstep (se 1 (by rfl) ⟨1568564, by rfl⟩ : syracuseStep 2091419 = 3137129) B3137129
theorem B616895 : Blo 409770 616895 := bstep (se 1 (by rfl) ⟨462671, by rfl⟩ : syracuseStep 616895 = 925343) B925343
theorem B879311 : Blo 409770 879311 := bstep (se 1 (by rfl) ⟨659483, by rfl⟩ : syracuseStep 879311 = 1318967) B1318967
theorem B879329 : Blo 409770 879329 := bstep (se 2 (by rfl) ⟨329748, by rfl⟩ : syracuseStep 879329 = 659497) B659497
theorem B1567943 : Blo 409770 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B617819 : Blo 409770 617819 := bstep (se 1 (by rfl) ⟨463364, by rfl⟩ : syracuseStep 617819 = 926729) B926729
theorem B85814963 : Blo 409770 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B5631767 : Blo 409770 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B1568747 : Blo 409770 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B618779 : Blo 409770 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B1667827 : Blo 409770 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B6026575 : Blo 409770 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B620063 : Blo 409770 620063 := bstep (se 1 (by rfl) ⟨465047, by rfl⟩ : syracuseStep 620063 = 930095) B930095
theorem B8452889 : Blo 409770 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B10550087 : Blo 409770 10550087 := bstep (se 1 (by rfl) ⟨7912565, by rfl⟩ : syracuseStep 10550087 = 15825131) B15825131
theorem B3344573 : Blo 409770 3344573 := bstep (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) B1254215
theorem B72092267 : Blo 409770 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B1313533 : Blo 409770 1313533 := bstep (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) B492575
theorem B3116231 : Blo 409770 3116231 := bstep (se 1 (by rfl) ⟨2337173, by rfl⟩ : syracuseStep 3116231 = 4674347) B4674347
theorem B494843 : Blo 409770 494843 := bstep (se 1 (by rfl) ⟨371132, by rfl⟩ : syracuseStep 494843 = 742265) B742265
theorem B12816373 : Blo 409770 12816373 := bstep (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) B1201535
theorem B496415 : Blo 409770 496415 := bstep (se 1 (by rfl) ⟨372311, by rfl⟩ : syracuseStep 496415 = 744623) B744623
theorem B8035433 : Blo 409770 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B925163 : Blo 409770 925163 := bstep (se 1 (by rfl) ⟨693872, by rfl⟩ : syracuseStep 925163 = 1387745) B1387745
theorem B1384775 : Blo 409770 1384775 := bstep (se 1 (by rfl) ⟨1038581, by rfl⟩ : syracuseStep 1384775 = 2077163) B2077163
theorem B927017 : Blo 409770 927017 := bstep (se 2 (by rfl) ⟨347631, by rfl⟩ : syracuseStep 927017 = 695263) B695263
theorem B3351941 : Blo 409770 3351941 := bstep (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) B628489
theorem B927323 : Blo 409770 927323 := bstep (se 1 (by rfl) ⟨695492, by rfl⟩ : syracuseStep 927323 = 1390985) B1390985
theorem B468839 : Blo 409770 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B14395877 : Blo 409770 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B2338793 : Blo 409770 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B30060557 : Blo 409770 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B34355447 : Blo 409770 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B4700591 : Blo 409770 4700591 := bstep (se 1 (by rfl) ⟨3525443, by rfl⟩ : syracuseStep 4700591 = 7050887) B7050887
theorem B3160721 : Blo 409770 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B441535 : Blo 409770 441535 := bstep (se 1 (by rfl) ⟨331151, by rfl⟩ : syracuseStep 441535 = 662303) B662303
theorem B1753427 : Blo 409770 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B410239 : Blo 409770 410239 := bstep (se 1 (by rfl) ⟨307679, by rfl⟩ : syracuseStep 410239 = 615359) B615359
theorem B1394279 : Blo 409770 1394279 := bstep (se 1 (by rfl) ⟨1045709, by rfl⟩ : syracuseStep 1394279 = 2091419) B2091419
theorem B411263 : Blo 409770 411263 := bstep (se 1 (by rfl) ⟨308447, by rfl⟩ : syracuseStep 411263 = 616895) B616895
theorem B411879 : Blo 409770 411879 := bstep (se 1 (by rfl) ⟨308909, by rfl⟩ : syracuseStep 411879 = 617819) B617819
theorem B3754511 : Blo 409770 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B412519 : Blo 409770 412519 := bstep (se 1 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 412519 = 618779) B618779
theorem B413375 : Blo 409770 413375 := bstep (se 1 (by rfl) ⟨310031, by rfl⟩ : syracuseStep 413375 = 620063) B620063
theorem B7033391 : Blo 409770 7033391 := bstep (se 1 (by rfl) ⟨5275043, by rfl⟩ : syracuseStep 7033391 = 10550087) B10550087
theorem B1757801 : Blo 409770 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B5264999 : Blo 409770 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B1758827 : Blo 409770 1758827 := bstep (se 1 (by rfl) ⟨1319120, by rfl⟩ : syracuseStep 1758827 = 2638241) B2638241
theorem B2086559 : Blo 409770 2086559 := bstep (se 1 (by rfl) ⟨1564919, by rfl⟩ : syracuseStep 2086559 = 3129839) B3129839
theorem B1038055 : Blo 409770 1038055 := bstep (se 1 (by rfl) ⟨778541, by rfl⟩ : syracuseStep 1038055 = 1557083) B1557083
theorem B28498067 : Blo 409770 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B2087369 : Blo 409770 2087369 := bstep (se 2 (by rfl) ⟨782763, by rfl⟩ : syracuseStep 2087369 = 1565527) B1565527
theorem B25451273 : Blo 409770 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B2088503 : Blo 409770 2088503 := bstep (se 1 (by rfl) ⟨1566377, by rfl⟩ : syracuseStep 2088503 = 3132755) B3132755
theorem B2351207 : Blo 409770 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B615167 : Blo 409770 615167 := bstep (se 1 (by rfl) ⟨461375, by rfl⟩ : syracuseStep 615167 = 922751) B922751
theorem B1041407 : Blo 409770 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B615593 : Blo 409770 615593 := bstep (se 2 (by rfl) ⟨230847, by rfl⟩ : syracuseStep 615593 = 461695) B461695
theorem B615689 : Blo 409770 615689 := bstep (se 2 (by rfl) ⟨230883, by rfl⟩ : syracuseStep 615689 = 461767) B461767
theorem B4712255 : Blo 409770 4712255 := bstep (se 1 (by rfl) ⟨3534191, by rfl⟩ : syracuseStep 4712255 = 7068383) B7068383
theorem B1763201 : Blo 409770 1763201 := bstep (se 2 (by rfl) ⟨661200, by rfl⟩ : syracuseStep 1763201 = 1322401) B1322401
theorem B616607 : Blo 409770 616607 := bstep (se 1 (by rfl) ⟨462455, by rfl⟩ : syracuseStep 616607 = 924911) B924911
theorem B616667 : Blo 409770 616667 := bstep (se 1 (by rfl) ⟨462500, by rfl⟩ : syracuseStep 616667 = 925001) B925001
theorem B1141499 : Blo 409770 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B19098661 : Blo 409770 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B617627 : Blo 409770 617627 := bstep (se 1 (by rfl) ⟨463220, by rfl⟩ : syracuseStep 617627 = 926441) B926441
theorem B617963 : Blo 409770 617963 := bstep (se 1 (by rfl) ⟨463472, by rfl⟩ : syracuseStep 617963 = 926945) B926945
theorem B2223769 : Blo 409770 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B618407 : Blo 409770 618407 := bstep (se 1 (by rfl) ⟨463805, by rfl⟩ : syracuseStep 618407 = 927611) B927611
theorem B585911 : Blo 409770 585911 := bstep (se 1 (by rfl) ⟨439433, by rfl⟩ : syracuseStep 585911 = 878867) B878867
theorem B586207 : Blo 409770 586207 := bstep (se 1 (by rfl) ⟨439655, by rfl⟩ : syracuseStep 586207 = 879311) B879311
theorem B586219 : Blo 409770 586219 := bstep (se 1 (by rfl) ⟨439664, by rfl⟩ : syracuseStep 586219 = 879329) B879329
theorem B1045295 : Blo 409770 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B619391 : Blo 409770 619391 := bstep (se 1 (by rfl) ⟨464543, by rfl⟩ : syracuseStep 619391 = 929087) B929087
theorem B881695 : Blo 409770 881695 := bstep (se 1 (by rfl) ⟨661271, by rfl⟩ : syracuseStep 881695 = 1322543) B1322543
theorem B619631 : Blo 409770 619631 := bstep (se 1 (by rfl) ⟨464723, by rfl⟩ : syracuseStep 619631 = 929447) B929447
theorem B57209975 : Blo 409770 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B619823 : Blo 409770 619823 := bstep (se 1 (by rfl) ⟨464867, by rfl⟩ : syracuseStep 619823 = 929735) B929735
theorem B1045831 : Blo 409770 1045831 := bstep (se 1 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 1045831 = 1568747) B1568747
theorem B587369 : Blo 409770 587369 := bstep (se 2 (by rfl) ⟨220263, by rfl⟩ : syracuseStep 587369 = 440527) B440527
theorem B620315 : Blo 409770 620315 := bstep (se 1 (by rfl) ⟨465236, by rfl⟩ : syracuseStep 620315 = 930473) B930473
theorem B620411 : Blo 409770 620411 := bstep (se 1 (by rfl) ⟨465308, by rfl⟩ : syracuseStep 620411 = 930617) B930617
theorem B5635259 : Blo 409770 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B2229715 : Blo 409770 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B4687469 : Blo 409770 4687469 := bstep (se 3 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 4687469 = 1757801) B1757801
theorem B4688927 : Blo 409770 4688927 := bstep (se 1 (by rfl) ⟨3516695, by rfl⟩ : syracuseStep 4688927 = 7033391) B7033391
theorem B3509999 : Blo 409770 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B25464881 : Blo 409770 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B1250237 : Blo 409770 1250237 := bstep (se 3 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 1250237 = 468839) B468839
theorem B923183 : Blo 409770 923183 := bstep (se 1 (by rfl) ⟨692387, by rfl⟩ : syracuseStep 923183 = 1384775) B1384775
theorem B694271 : Blo 409770 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B2234627 : Blo 409770 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B67870061 : Blo 409770 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B1384073 : Blo 409770 1384073 := bstep (se 2 (by rfl) ⟨519027, by rfl⟩ : syracuseStep 1384073 = 1038055) B1038055
theorem B696863 : Blo 409770 696863 := bstep (se 1 (by rfl) ⟨522647, by rfl⟩ : syracuseStep 696863 = 1045295) B1045295
theorem B1319581 : Blo 409770 1319581 := bstep (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) B494843
theorem B2107147 : Blo 409770 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B929519 : Blo 409770 929519 := bstep (se 1 (by rfl) ⟨697139, by rfl⟩ : syracuseStep 929519 = 1394279) B1394279
theorem B2503007 : Blo 409770 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B1323773 : Blo 409770 1323773 := bstep (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) B496415
theorem B2077487 : Blo 409770 2077487 := bstep (se 1 (by rfl) ⟨1558115, by rfl⟩ : syracuseStep 2077487 = 3116231) B3116231
theorem B3126437 : Blo 409770 3126437 := bstep (se 4 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 3126437 = 586207) B586207
theorem B1751377 : Blo 409770 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B1391039 : Blo 409770 1391039 := bstep (se 1 (by rfl) ⟨1043279, by rfl⟩ : syracuseStep 1391039 = 2086559) B2086559
theorem B1391579 : Blo 409770 1391579 := bstep (se 1 (by rfl) ⟨1043684, by rfl⟩ : syracuseStep 1391579 = 2087369) B2087369
theorem B5356955 : Blo 409770 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B2965025 : Blo 409770 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B1392335 : Blo 409770 1392335 := bstep (se 1 (by rfl) ⟨1044251, by rfl⟩ : syracuseStep 1392335 = 2088503) B2088503
theorem B17088497 : Blo 409770 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B410111 : Blo 409770 410111 := bstep (se 1 (by rfl) ⟨307583, by rfl⟩ : syracuseStep 410111 = 615167) B615167
theorem B410395 : Blo 409770 410395 := bstep (se 1 (by rfl) ⟨307796, by rfl⟩ : syracuseStep 410395 = 615593) B615593
theorem B410459 : Blo 409770 410459 := bstep (se 1 (by rfl) ⟨307844, by rfl⟩ : syracuseStep 410459 = 615689) B615689
theorem B411071 : Blo 409770 411071 := bstep (se 1 (by rfl) ⟨308303, by rfl⟩ : syracuseStep 411071 = 616607) B616607
theorem B411111 : Blo 409770 411111 := bstep (se 1 (by rfl) ⟨308333, by rfl⟩ : syracuseStep 411111 = 616667) B616667
theorem B1394441 : Blo 409770 1394441 := bstep (se 2 (by rfl) ⟨522915, by rfl⟩ : syracuseStep 1394441 = 1045831) B1045831
theorem B411751 : Blo 409770 411751 := bstep (se 1 (by rfl) ⟨308813, by rfl⟩ : syracuseStep 411751 = 617627) B617627
theorem B411975 : Blo 409770 411975 := bstep (se 1 (by rfl) ⟨308981, by rfl⟩ : syracuseStep 411975 = 617963) B617963
theorem B412271 : Blo 409770 412271 := bstep (se 1 (by rfl) ⟨309203, by rfl⟩ : syracuseStep 412271 = 618407) B618407
theorem B1559195 : Blo 409770 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B20040371 : Blo 409770 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B412927 : Blo 409770 412927 := bstep (se 1 (by rfl) ⟨309695, by rfl⟩ : syracuseStep 412927 = 619391) B619391
theorem B413087 : Blo 409770 413087 := bstep (se 1 (by rfl) ⟨309815, by rfl⟩ : syracuseStep 413087 = 619631) B619631
theorem B413215 : Blo 409770 413215 := bstep (se 1 (by rfl) ⟨309911, by rfl⟩ : syracuseStep 413215 = 619823) B619823
theorem B413543 : Blo 409770 413543 := bstep (se 1 (by rfl) ⟨310157, by rfl⟩ : syracuseStep 413543 = 620315) B620315
theorem B413607 : Blo 409770 413607 := bstep (se 1 (by rfl) ⟨310205, by rfl⟩ : syracuseStep 413607 = 620411) B620411
theorem B3133727 : Blo 409770 3133727 := bstep (se 1 (by rfl) ⟨2350295, by rfl⟩ : syracuseStep 3133727 = 4700591) B4700591
theorem B3756839 : Blo 409770 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B1562429 : Blo 409770 1562429 := bstep (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) B585911
theorem B4675805 : Blo 409770 4675805 := bstep (se 3 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 4675805 = 1753427) B1753427
theorem B48061511 : Blo 409770 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B1172551 : Blo 409770 1172551 := bstep (se 1 (by rfl) ⟨879413, by rfl⟩ : syracuseStep 1172551 = 1758827) B1758827
theorem B18998711 : Blo 409770 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B1566317 : Blo 409770 1566317 := bstep (se 3 (by rfl) ⟨293684, by rfl⟩ : syracuseStep 1566317 = 587369) B587369
theorem B616775 : Blo 409770 616775 := bstep (se 1 (by rfl) ⟨462581, by rfl⟩ : syracuseStep 616775 = 925163) B925163
theorem B1567471 : Blo 409770 1567471 := bstep (se 1 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 1567471 = 2351207) B2351207
theorem B781625 : Blo 409770 781625 := bstep (se 2 (by rfl) ⟨293109, by rfl⟩ : syracuseStep 781625 = 586219) B586219
theorem B618011 : Blo 409770 618011 := bstep (se 1 (by rfl) ⟨463508, by rfl⟩ : syracuseStep 618011 = 927017) B927017
theorem B618215 : Blo 409770 618215 := bstep (se 1 (by rfl) ⟨463661, by rfl⟩ : syracuseStep 618215 = 927323) B927323
theorem B3141503 : Blo 409770 3141503 := bstep (se 1 (by rfl) ⟨2356127, by rfl⟩ : syracuseStep 3141503 = 4712255) B4712255
theorem B1175467 : Blo 409770 1175467 := bstep (se 1 (by rfl) ⟨881600, by rfl⟩ : syracuseStep 1175467 = 1763201) B1763201
theorem B1175593 : Blo 409770 1175593 := bstep (se 2 (by rfl) ⟨440847, by rfl⟩ : syracuseStep 1175593 = 881695) B881695
theorem B9597251 : Blo 409770 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B3043997 : Blo 409770 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B38139983 : Blo 409770 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B22903631 : Blo 409770 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B588713 : Blo 409770 588713 := bstep (se 2 (by rfl) ⟨220767, by rfl⟩ : syracuseStep 588713 = 441535) B441535
theorem B25592669 : Blo 409770 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B16976587 : Blo 409770 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B462847 : Blo 409770 462847 := bstep (se 1 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 462847 = 694271) B694271
theorem B3117203 : Blo 409770 3117203 := bstep (se 1 (by rfl) ⟨2337902, by rfl⟩ : syracuseStep 3117203 = 4675805) B4675805
theorem B922715 : Blo 409770 922715 := bstep (se 1 (by rfl) ⟨692036, by rfl⟩ : syracuseStep 922715 = 1384073) B1384073
theorem B464575 : Blo 409770 464575 := bstep (se 1 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 464575 = 696863) B696863
theorem B2335169 : Blo 409770 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B1384991 : Blo 409770 1384991 := bstep (se 1 (by rfl) ⟨1038743, by rfl⟩ : syracuseStep 1384991 = 2077487) B2077487
theorem B927359 : Blo 409770 927359 := bstep (se 1 (by rfl) ⟨695519, by rfl⟩ : syracuseStep 927359 = 1391039) B1391039
theorem B927719 : Blo 409770 927719 := bstep (se 1 (by rfl) ⟨695789, by rfl⟩ : syracuseStep 927719 = 1391579) B1391579
theorem B1976683 : Blo 409770 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B928223 : Blo 409770 928223 := bstep (se 1 (by rfl) ⟨696167, by rfl⟩ : syracuseStep 928223 = 1392335) B1392335
theorem B3124979 : Blo 409770 3124979 := bstep (se 1 (by rfl) ⟨2343734, by rfl⟩ : syracuseStep 3124979 = 4687469) B4687469
theorem B929627 : Blo 409770 929627 := bstep (se 1 (by rfl) ⟨697220, by rfl⟩ : syracuseStep 929627 = 1394441) B1394441
theorem B3125951 : Blo 409770 3125951 := bstep (se 1 (by rfl) ⟨2344463, by rfl⟩ : syracuseStep 3125951 = 4688927) B4688927
theorem B2339999 : Blo 409770 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B833491 : Blo 409770 833491 := bstep (se 1 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 833491 = 1250237) B1250237
theorem B1489751 : Blo 409770 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B12665807 : Blo 409770 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B411183 : Blo 409770 411183 := bstep (se 1 (by rfl) ⟨308387, by rfl⟩ : syracuseStep 411183 = 616775) B616775
theorem B412007 : Blo 409770 412007 := bstep (se 1 (by rfl) ⟨309005, by rfl⟩ : syracuseStep 412007 = 618011) B618011
theorem B412143 : Blo 409770 412143 := bstep (se 1 (by rfl) ⟨309107, by rfl⟩ : syracuseStep 412143 = 618215) B618215
theorem B2084291 : Blo 409770 2084291 := bstep (se 1 (by rfl) ⟨1563218, by rfl⟩ : syracuseStep 2084291 = 3126437) B3126437
theorem B11392331 : Blo 409770 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B1563401 : Blo 409770 1563401 := bstep (se 2 (by rfl) ⟨586275, by rfl⟩ : syracuseStep 1563401 = 1172551) B1172551
theorem B1039463 : Blo 409770 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B13360247 : Blo 409770 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B2972953 : Blo 409770 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B10018237 : Blo 409770 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B2809529 : Blo 409770 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B2089151 : Blo 409770 2089151 := bstep (se 1 (by rfl) ⟨1566863, by rfl⟩ : syracuseStep 2089151 = 3133727) B3133727
theorem B7037765 : Blo 409770 7037765 := bstep (se 4 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 7037765 = 1319581) B1319581
theorem B2089961 : Blo 409770 2089961 := bstep (se 2 (by rfl) ⟨783735, by rfl⟩ : syracuseStep 2089961 = 1567471) B1567471
theorem B615455 : Blo 409770 615455 := bstep (se 1 (by rfl) ⟨461591, by rfl⟩ : syracuseStep 615455 = 923183) B923183
theorem B1041619 : Blo 409770 1041619 := bstep (se 1 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 1041619 = 1562429) B1562429
theorem B32041007 : Blo 409770 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B45246707 : Blo 409770 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B1567289 : Blo 409770 1567289 := bstep (se 2 (by rfl) ⟨587733, by rfl⟩ : syracuseStep 1567289 = 1175467) B1175467
theorem B1567457 : Blo 409770 1567457 := bstep (se 2 (by rfl) ⟨587796, by rfl⟩ : syracuseStep 1567457 = 1175593) B1175593
theorem B1044211 : Blo 409770 1044211 := bstep (se 1 (by rfl) ⟨783158, by rfl⟩ : syracuseStep 1044211 = 1566317) B1566317
theorem B521083 : Blo 409770 521083 := bstep (se 1 (by rfl) ⟨390812, by rfl⟩ : syracuseStep 521083 = 781625) B781625
theorem B1569901 : Blo 409770 1569901 := bstep (se 3 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 1569901 = 588713) B588713
theorem B619679 : Blo 409770 619679 := bstep (se 1 (by rfl) ⟨464759, by rfl⟩ : syracuseStep 619679 = 929519) B929519
theorem B2094335 : Blo 409770 2094335 := bstep (se 1 (by rfl) ⟨1570751, by rfl⟩ : syracuseStep 2094335 = 3141503) B3141503
theorem B1668671 : Blo 409770 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B2029331 : Blo 409770 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B882515 : Blo 409770 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B25426655 : Blo 409770 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B15269087 : Blo 409770 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B3571303 : Blo 409770 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B30379549 : Blo 409770 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B5411549 : Blo 409770 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B692975 : Blo 409770 692975 := bstep (se 1 (by rfl) ⟨519731, by rfl⟩ : syracuseStep 692975 = 1039463) B1039463
theorem B1873019 : Blo 409770 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B923327 : Blo 409770 923327 := bstep (se 1 (by rfl) ⟨692495, by rfl⟩ : syracuseStep 923327 = 1384991) B1384991
theorem B4691843 : Blo 409770 4691843 := bstep (se 1 (by rfl) ⟨3518882, by rfl⟩ : syracuseStep 4691843 = 7037765) B7037765
theorem B694777 : Blo 409770 694777 := bstep (se 2 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 694777 = 521083) B521083
theorem B16951103 : Blo 409770 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B993167 : Blo 409770 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B4761737 : Blo 409770 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B1388825 : Blo 409770 1388825 := bstep (se 2 (by rfl) ⟨520809, by rfl⟩ : syracuseStep 1388825 = 1041619) B1041619
theorem B1389527 : Blo 409770 1389527 := bstep (se 1 (by rfl) ⟨1042145, by rfl⟩ : syracuseStep 1389527 = 2084291) B2084291
theorem B2078135 : Blo 409770 2078135 := bstep (se 1 (by rfl) ⟨1558601, by rfl⟩ : syracuseStep 2078135 = 3117203) B3117203
theorem B2635577 : Blo 409770 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B1392281 : Blo 409770 1392281 := bstep (se 2 (by rfl) ⟨522105, by rfl⟩ : syracuseStep 1392281 = 1044211) B1044211
theorem B1392767 : Blo 409770 1392767 := bstep (se 1 (by rfl) ⟨1044575, by rfl⟩ : syracuseStep 1392767 = 2089151) B2089151
theorem B1556779 : Blo 409770 1556779 := bstep (se 1 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 1556779 = 2335169) B2335169
theorem B1393307 : Blo 409770 1393307 := bstep (se 1 (by rfl) ⟨1044980, by rfl⟩ : syracuseStep 1393307 = 2089961) B2089961
theorem B410303 : Blo 409770 410303 := bstep (se 1 (by rfl) ⟨307727, by rfl⟩ : syracuseStep 410303 = 615455) B615455
theorem B30164471 : Blo 409770 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B2083319 : Blo 409770 2083319 := bstep (se 1 (by rfl) ⟨1562489, by rfl⟩ : syracuseStep 2083319 = 3124979) B3124979
theorem B2083967 : Blo 409770 2083967 := bstep (se 1 (by rfl) ⟨1562975, by rfl⟩ : syracuseStep 2083967 = 3125951) B3125951
theorem B40717565 : Blo 409770 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B1559999 : Blo 409770 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B413119 : Blo 409770 413119 := bstep (se 1 (by rfl) ⟨309839, by rfl⟩ : syracuseStep 413119 = 619679) B619679
theorem B1396223 : Blo 409770 1396223 := bstep (se 1 (by rfl) ⟨1047167, by rfl⟩ : syracuseStep 1396223 = 2094335) B2094335
theorem B13357649 : Blo 409770 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B17061779 : Blo 409770 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B8443871 : Blo 409770 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B615143 : Blo 409770 615143 := bstep (se 1 (by rfl) ⟨461357, by rfl⟩ : syracuseStep 615143 = 922715) B922715
theorem B22635449 : Blo 409770 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B1042267 : Blo 409770 1042267 := bstep (se 1 (by rfl) ⟨781700, by rfl⟩ : syracuseStep 1042267 = 1563401) B1563401
theorem B8906831 : Blo 409770 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B2353373 : Blo 409770 2353373 := bstep (se 3 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 2353373 = 882515) B882515
theorem B617129 : Blo 409770 617129 := bstep (se 2 (by rfl) ⟨231423, by rfl⟩ : syracuseStep 617129 = 462847) B462847
theorem B618239 : Blo 409770 618239 := bstep (se 1 (by rfl) ⟨463679, by rfl⟩ : syracuseStep 618239 = 927359) B927359
theorem B618479 : Blo 409770 618479 := bstep (se 1 (by rfl) ⟨463859, by rfl⟩ : syracuseStep 618479 = 927719) B927719
theorem B21360671 : Blo 409770 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B2093201 : Blo 409770 2093201 := bstep (se 2 (by rfl) ⟨784950, by rfl⟩ : syracuseStep 2093201 = 1569901) B1569901
theorem B618815 : Blo 409770 618815 := bstep (se 1 (by rfl) ⟨464111, by rfl⟩ : syracuseStep 618815 = 928223) B928223
theorem B1044859 : Blo 409770 1044859 := bstep (se 1 (by rfl) ⟨783644, by rfl⟩ : syracuseStep 1044859 = 1567289) B1567289
theorem B1044971 : Blo 409770 1044971 := bstep (se 1 (by rfl) ⟨783728, by rfl⟩ : syracuseStep 1044971 = 1567457) B1567457
theorem B619433 : Blo 409770 619433 := bstep (se 2 (by rfl) ⟨232287, by rfl⟩ : syracuseStep 619433 = 464575) B464575
theorem B619751 : Blo 409770 619751 := bstep (se 1 (by rfl) ⟨464813, by rfl⟩ : syracuseStep 619751 = 929627) B929627
theorem B1111321 : Blo 409770 1111321 := bstep (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) B833491
theorem B1112447 : Blo 409770 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B3963937 : Blo 409770 3963937 := bstep (se 2 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 3963937 = 2972953) B2972953
theorem B461983 : Blo 409770 461983 := bstep (se 1 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 461983 = 692975) B692975
theorem B1248679 : Blo 409770 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B11374519 : Blo 409770 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B40506065 : Blo 409770 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B662111 : Blo 409770 662111 := bstep (se 1 (by rfl) ⟨496583, by rfl⟩ : syracuseStep 662111 = 993167) B993167
theorem B5937887 : Blo 409770 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B1481761 : Blo 409770 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B925883 : Blo 409770 925883 := bstep (se 1 (by rfl) ⟨694412, by rfl⟩ : syracuseStep 925883 = 1388825) B1388825
theorem B696647 : Blo 409770 696647 := bstep (se 1 (by rfl) ⟨522485, by rfl⟩ : syracuseStep 696647 = 1044971) B1044971
theorem B926351 : Blo 409770 926351 := bstep (se 1 (by rfl) ⟨694763, by rfl⟩ : syracuseStep 926351 = 1389527) B1389527
theorem B926369 : Blo 409770 926369 := bstep (se 2 (by rfl) ⟨347388, by rfl⟩ : syracuseStep 926369 = 694777) B694777
theorem B1385423 : Blo 409770 1385423 := bstep (se 1 (by rfl) ⟨1039067, by rfl⟩ : syracuseStep 1385423 = 2078135) B2078135
theorem B5285249 : Blo 409770 5285249 := bstep (se 2 (by rfl) ⟨1981968, by rfl⟩ : syracuseStep 5285249 = 3963937) B3963937
theorem B928187 : Blo 409770 928187 := bstep (se 1 (by rfl) ⟨696140, by rfl⟩ : syracuseStep 928187 = 1392281) B1392281
theorem B928511 : Blo 409770 928511 := bstep (se 1 (by rfl) ⟨696383, by rfl⟩ : syracuseStep 928511 = 1392767) B1392767
theorem B2075705 : Blo 409770 2075705 := bstep (se 2 (by rfl) ⟨778389, by rfl⟩ : syracuseStep 2075705 = 1556779) B1556779
theorem B928871 : Blo 409770 928871 := bstep (se 1 (by rfl) ⟨696653, by rfl⟩ : syracuseStep 928871 = 1393307) B1393307
theorem B1388879 : Blo 409770 1388879 := bstep (se 1 (by rfl) ⟨1041659, by rfl⟩ : syracuseStep 1388879 = 2083319) B2083319
theorem B14430797 : Blo 409770 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B1389311 : Blo 409770 1389311 := bstep (se 1 (by rfl) ⟨1041983, by rfl⟩ : syracuseStep 1389311 = 2083967) B2083967
theorem B27145043 : Blo 409770 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B930815 : Blo 409770 930815 := bstep (se 1 (by rfl) ⟨698111, by rfl⟩ : syracuseStep 930815 = 1396223) B1396223
theorem B1389689 : Blo 409770 1389689 := bstep (se 2 (by rfl) ⟨521133, by rfl⟩ : syracuseStep 1389689 = 1042267) B1042267
theorem B3127895 : Blo 409770 3127895 := bstep (se 1 (by rfl) ⟨2345921, by rfl⟩ : syracuseStep 3127895 = 4691843) B4691843
theorem B410095 : Blo 409770 410095 := bstep (se 1 (by rfl) ⟨307571, by rfl⟩ : syracuseStep 410095 = 615143) B615143
theorem B1393145 : Blo 409770 1393145 := bstep (se 2 (by rfl) ⟨522429, by rfl⟩ : syracuseStep 1393145 = 1044859) B1044859
theorem B15090299 : Blo 409770 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B411419 : Blo 409770 411419 := bstep (se 1 (by rfl) ⟨308564, by rfl⟩ : syracuseStep 411419 = 617129) B617129
theorem B412159 : Blo 409770 412159 := bstep (se 1 (by rfl) ⟨309119, by rfl⟩ : syracuseStep 412159 = 618239) B618239
theorem B412319 : Blo 409770 412319 := bstep (se 1 (by rfl) ⟨309239, by rfl⟩ : syracuseStep 412319 = 618479) B618479
theorem B14240447 : Blo 409770 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B1395467 : Blo 409770 1395467 := bstep (se 1 (by rfl) ⟨1046600, by rfl⟩ : syracuseStep 1395467 = 2093201) B2093201
theorem B412543 : Blo 409770 412543 := bstep (se 1 (by rfl) ⟨309407, by rfl⟩ : syracuseStep 412543 = 618815) B618815
theorem B412955 : Blo 409770 412955 := bstep (se 1 (by rfl) ⟨309716, by rfl⟩ : syracuseStep 412955 = 619433) B619433
theorem B413167 : Blo 409770 413167 := bstep (se 1 (by rfl) ⟨309875, by rfl⟩ : syracuseStep 413167 = 619751) B619751
theorem B1757051 : Blo 409770 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B741631 : Blo 409770 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B20109647 : Blo 409770 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B1039999 : Blo 409770 1039999 := bstep (se 1 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 1039999 = 1559999) B1559999
theorem B8905099 : Blo 409770 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B615551 : Blo 409770 615551 := bstep (se 1 (by rfl) ⟨461663, by rfl⟩ : syracuseStep 615551 = 923327) B923327
theorem B5629247 : Blo 409770 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B11300735 : Blo 409770 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B3174491 : Blo 409770 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B1568915 : Blo 409770 1568915 := bstep (se 1 (by rfl) ⟨1176686, by rfl⟩ : syracuseStep 1568915 = 2353373) B2353373
theorem B10060199 : Blo 409770 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B27004043 : Blo 409770 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B13406431 : Blo 409770 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B464431 : Blo 409770 464431 := bstep (se 1 (by rfl) ⟨348323, by rfl⟩ : syracuseStep 464431 = 696647) B696647
theorem B988841 : Blo 409770 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B923615 : Blo 409770 923615 := bstep (se 1 (by rfl) ⟨692711, by rfl⟩ : syracuseStep 923615 = 1385423) B1385423
theorem B1383803 : Blo 409770 1383803 := bstep (se 1 (by rfl) ⟨1037852, by rfl⟩ : syracuseStep 1383803 = 2075705) B2075705
theorem B6659621 : Blo 409770 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B925919 : Blo 409770 925919 := bstep (se 1 (by rfl) ⟨694439, by rfl⟩ : syracuseStep 925919 = 1388879) B1388879
theorem B926207 : Blo 409770 926207 := bstep (se 1 (by rfl) ⟨694655, by rfl⟩ : syracuseStep 926207 = 1389311) B1389311
theorem B18096695 : Blo 409770 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B926459 : Blo 409770 926459 := bstep (se 1 (by rfl) ⟨694844, by rfl⟩ : syracuseStep 926459 = 1389689) B1389689
theorem B1975681 : Blo 409770 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B1386665 : Blo 409770 1386665 := bstep (se 2 (by rfl) ⟨519999, by rfl⟩ : syracuseStep 1386665 = 1039999) B1039999
theorem B8465309 : Blo 409770 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B928763 : Blo 409770 928763 := bstep (se 1 (by rfl) ⟨696572, by rfl⟩ : syracuseStep 928763 = 1393145) B1393145
theorem B11873465 : Blo 409770 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B930311 : Blo 409770 930311 := bstep (se 1 (by rfl) ⟨697733, by rfl⟩ : syracuseStep 930311 = 1395467) B1395467
theorem B441407 : Blo 409770 441407 := bstep (se 1 (by rfl) ⟨331055, by rfl⟩ : syracuseStep 441407 = 662111) B662111
theorem B410367 : Blo 409770 410367 := bstep (se 1 (by rfl) ⟨307775, by rfl⟩ : syracuseStep 410367 = 615551) B615551
theorem B3752831 : Blo 409770 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B3523499 : Blo 409770 3523499 := bstep (se 1 (by rfl) ⟨2642624, by rfl⟩ : syracuseStep 3523499 = 5285249) B5285249
theorem B9620531 : Blo 409770 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B2085263 : Blo 409770 2085263 := bstep (se 1 (by rfl) ⟨1563947, by rfl⟩ : syracuseStep 2085263 = 3127895) B3127895
theorem B9493631 : Blo 409770 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B1171367 : Blo 409770 1171367 := bstep (se 1 (by rfl) ⟨878525, by rfl⟩ : syracuseStep 1171367 = 1757051) B1757051
theorem B615977 : Blo 409770 615977 := bstep (se 2 (by rfl) ⟨230991, by rfl⟩ : syracuseStep 615977 = 461983) B461983
theorem B3958591 : Blo 409770 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B15166025 : Blo 409770 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B617255 : Blo 409770 617255 := bstep (se 1 (by rfl) ⟨462941, by rfl⟩ : syracuseStep 617255 = 925883) B925883
theorem B617567 : Blo 409770 617567 := bstep (se 1 (by rfl) ⟨463175, by rfl⟩ : syracuseStep 617567 = 926351) B926351
theorem B617579 : Blo 409770 617579 := bstep (se 1 (by rfl) ⟨463184, by rfl⟩ : syracuseStep 617579 = 926369) B926369
theorem B618791 : Blo 409770 618791 := bstep (se 1 (by rfl) ⟨464093, by rfl⟩ : syracuseStep 618791 = 928187) B928187
theorem B619007 : Blo 409770 619007 := bstep (se 1 (by rfl) ⟨464255, by rfl⟩ : syracuseStep 619007 = 928511) B928511
theorem B619247 : Blo 409770 619247 := bstep (se 1 (by rfl) ⟨464435, by rfl⟩ : syracuseStep 619247 = 928871) B928871
theorem B7533823 : Blo 409770 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B1045943 : Blo 409770 1045943 := bstep (se 1 (by rfl) ⟨784457, by rfl⟩ : syracuseStep 1045943 = 1568915) B1568915
theorem B620543 : Blo 409770 620543 := bstep (se 1 (by rfl) ⟨465407, by rfl⟩ : syracuseStep 620543 = 930815) B930815
theorem B5278121 : Blo 409770 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B659227 : Blo 409770 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B6329087 : Blo 409770 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B922535 : Blo 409770 922535 := bstep (se 1 (by rfl) ⟨691901, by rfl⟩ : syracuseStep 922535 = 1383803) B1383803
theorem B12064463 : Blo 409770 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B924443 : Blo 409770 924443 := bstep (se 1 (by rfl) ⟨693332, by rfl⟩ : syracuseStep 924443 = 1386665) B1386665
theorem B5643539 : Blo 409770 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B697295 : Blo 409770 697295 := bstep (se 1 (by rfl) ⟨522971, by rfl⟩ : syracuseStep 697295 = 1045943) B1045943
theorem B2501887 : Blo 409770 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B1390175 : Blo 409770 1390175 := bstep (se 1 (by rfl) ⟨1042631, by rfl⟩ : syracuseStep 1390175 = 2085263) B2085263
theorem B4439747 : Blo 409770 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B17875241 : Blo 409770 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B410651 : Blo 409770 410651 := bstep (se 1 (by rfl) ⟨307988, by rfl⟩ : syracuseStep 410651 = 615977) B615977
theorem B10045097 : Blo 409770 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B10110683 : Blo 409770 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B411503 : Blo 409770 411503 := bstep (se 1 (by rfl) ⟨308627, by rfl⟩ : syracuseStep 411503 = 617255) B617255
theorem B10536965 : Blo 409770 10536965 := bstep (se 4 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 10536965 = 1975681) B1975681
theorem B411711 : Blo 409770 411711 := bstep (se 1 (by rfl) ⟨308783, by rfl⟩ : syracuseStep 411711 = 617567) B617567
theorem B411719 : Blo 409770 411719 := bstep (se 1 (by rfl) ⟨308789, by rfl⟩ : syracuseStep 411719 = 617579) B617579
theorem B7915643 : Blo 409770 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B412527 : Blo 409770 412527 := bstep (se 1 (by rfl) ⟨309395, by rfl⟩ : syracuseStep 412527 = 618791) B618791
theorem B412671 : Blo 409770 412671 := bstep (se 1 (by rfl) ⟨309503, by rfl⟩ : syracuseStep 412671 = 619007) B619007
theorem B72010781 : Blo 409770 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B412831 : Blo 409770 412831 := bstep (se 1 (by rfl) ⟨309623, by rfl⟩ : syracuseStep 412831 = 619247) B619247
theorem B413695 : Blo 409770 413695 := bstep (se 1 (by rfl) ⟨310271, by rfl⟩ : syracuseStep 413695 = 620543) B620543
theorem B6706799 : Blo 409770 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B2348999 : Blo 409770 2348999 := bstep (se 1 (by rfl) ⟨1761749, by rfl⟩ : syracuseStep 2348999 = 3523499) B3523499
theorem B6413687 : Blo 409770 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B615743 : Blo 409770 615743 := bstep (se 1 (by rfl) ⟨461807, by rfl⟩ : syracuseStep 615743 = 923615) B923615
theorem B780911 : Blo 409770 780911 := bstep (se 1 (by rfl) ⟨585683, by rfl⟩ : syracuseStep 780911 = 1171367) B1171367
theorem B617279 : Blo 409770 617279 := bstep (se 1 (by rfl) ⟨462959, by rfl⟩ : syracuseStep 617279 = 925919) B925919
theorem B617471 : Blo 409770 617471 := bstep (se 1 (by rfl) ⟨463103, by rfl⟩ : syracuseStep 617471 = 926207) B926207
theorem B617639 : Blo 409770 617639 := bstep (se 1 (by rfl) ⟨463229, by rfl⟩ : syracuseStep 617639 = 926459) B926459
theorem B619175 : Blo 409770 619175 := bstep (se 1 (by rfl) ⟨464381, by rfl⟩ : syracuseStep 619175 = 928763) B928763
theorem B619241 : Blo 409770 619241 := bstep (se 2 (by rfl) ⟨232215, by rfl⟩ : syracuseStep 619241 = 464431) B464431
theorem B1177085 : Blo 409770 1177085 := bstep (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) B441407
theorem B620207 : Blo 409770 620207 := bstep (se 1 (by rfl) ⟨465155, by rfl⟩ : syracuseStep 620207 = 930311) B930311
theorem B5277095 : Blo 409770 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B48007187 : Blo 409770 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B464863 : Blo 409770 464863 := bstep (se 1 (by rfl) ⟨348647, by rfl⟩ : syracuseStep 464863 = 697295) B697295
theorem B926783 : Blo 409770 926783 := bstep (se 1 (by rfl) ⟨695087, by rfl⟩ : syracuseStep 926783 = 1390175) B1390175
theorem B2959831 : Blo 409770 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B6696731 : Blo 409770 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B7024643 : Blo 409770 7024643 := bstep (se 1 (by rfl) ⟨5268482, by rfl⟩ : syracuseStep 7024643 = 10536965) B10536965
theorem B3518747 : Blo 409770 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B4471199 : Blo 409770 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B8042975 : Blo 409770 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B4275791 : Blo 409770 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B410495 : Blo 409770 410495 := bstep (se 1 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 410495 = 615743) B615743
theorem B411519 : Blo 409770 411519 := bstep (se 1 (by rfl) ⟨308639, by rfl⟩ : syracuseStep 411519 = 617279) B617279
theorem B411647 : Blo 409770 411647 := bstep (se 1 (by rfl) ⟨308735, by rfl⟩ : syracuseStep 411647 = 617471) B617471
theorem B411759 : Blo 409770 411759 := bstep (se 1 (by rfl) ⟨308819, by rfl⟩ : syracuseStep 411759 = 617639) B617639
theorem B412783 : Blo 409770 412783 := bstep (se 1 (by rfl) ⟨309587, by rfl⟩ : syracuseStep 412783 = 619175) B619175
theorem B412827 : Blo 409770 412827 := bstep (se 1 (by rfl) ⟨309620, by rfl⟩ : syracuseStep 412827 = 619241) B619241
theorem B413471 : Blo 409770 413471 := bstep (se 1 (by rfl) ⟨310103, by rfl⟩ : syracuseStep 413471 = 620207) B620207
theorem B11916827 : Blo 409770 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B6740455 : Blo 409770 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B4219391 : Blo 409770 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B615023 : Blo 409770 615023 := bstep (se 1 (by rfl) ⟨461267, by rfl⟩ : syracuseStep 615023 = 922535) B922535
theorem B1565999 : Blo 409770 1565999 := bstep (se 1 (by rfl) ⟨1174499, by rfl⟩ : syracuseStep 1565999 = 2348999) B2348999
theorem B3335849 : Blo 409770 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B616295 : Blo 409770 616295 := bstep (se 1 (by rfl) ⟨462221, by rfl⟩ : syracuseStep 616295 = 924443) B924443
theorem B3762359 : Blo 409770 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B878969 : Blo 409770 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B520607 : Blo 409770 520607 := bstep (se 1 (by rfl) ⟨390455, by rfl⟩ : syracuseStep 520607 = 780911) B780911
theorem B784723 : Blo 409770 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B4464487 : Blo 409770 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B8987273 : Blo 409770 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B3518063 : Blo 409770 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B1388285 : Blo 409770 1388285 := bstep (se 3 (by rfl) ⟨260303, by rfl⟩ : syracuseStep 1388285 = 520607) B520607
theorem B7944551 : Blo 409770 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B410015 : Blo 409770 410015 := bstep (se 1 (by rfl) ⟨307511, by rfl⟩ : syracuseStep 410015 = 615023) B615023
theorem B2343917 : Blo 409770 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B410863 : Blo 409770 410863 := bstep (se 1 (by rfl) ⟨308147, by rfl⟩ : syracuseStep 410863 = 616295) B616295
theorem B2508239 : Blo 409770 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B2345831 : Blo 409770 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B5361983 : Blo 409770 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B32004791 : Blo 409770 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B15785765 : Blo 409770 15785765 := bstep (se 4 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 15785765 = 2959831) B2959831
theorem B2812927 : Blo 409770 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B617855 : Blo 409770 617855 := bstep (se 1 (by rfl) ⟨463391, by rfl⟩ : syracuseStep 617855 = 926783) B926783
theorem B1043999 : Blo 409770 1043999 := bstep (se 1 (by rfl) ⟨782999, by rfl⟩ : syracuseStep 1043999 = 1565999) B1565999
theorem B2223899 : Blo 409770 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B619817 : Blo 409770 619817 := bstep (se 2 (by rfl) ⟨232431, by rfl⟩ : syracuseStep 619817 = 464863) B464863
theorem B4683095 : Blo 409770 4683095 := bstep (se 1 (by rfl) ⟨3512321, by rfl⟩ : syracuseStep 4683095 = 7024643) B7024643
theorem B1046297 : Blo 409770 1046297 := bstep (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) B784723
theorem B2980799 : Blo 409770 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B2850527 : Blo 409770 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B1672159 : Blo 409770 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B3574655 : Blo 409770 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B21336527 : Blo 409770 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B10523843 : Blo 409770 10523843 := bstep (se 1 (by rfl) ⟨7892882, by rfl⟩ : syracuseStep 10523843 = 15785765) B15785765
theorem B695999 : Blo 409770 695999 := bstep (se 1 (by rfl) ⟨521999, by rfl⟩ : syracuseStep 695999 = 1043999) B1043999
theorem B925523 : Blo 409770 925523 := bstep (se 1 (by rfl) ⟨694142, by rfl⟩ : syracuseStep 925523 = 1388285) B1388285
theorem B1482599 : Blo 409770 1482599 := bstep (se 1 (by rfl) ⟨1111949, by rfl⟩ : syracuseStep 1482599 = 2223899) B2223899
theorem B3122063 : Blo 409770 3122063 := bstep (se 1 (by rfl) ⟨2341547, by rfl⟩ : syracuseStep 3122063 = 4683095) B4683095
theorem B697531 : Blo 409770 697531 := bstep (se 1 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 697531 = 1046297) B1046297
theorem B3750569 : Blo 409770 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B411903 : Blo 409770 411903 := bstep (se 1 (by rfl) ⟨308927, by rfl⟩ : syracuseStep 411903 = 617855) B617855
theorem B2345375 : Blo 409770 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B413211 : Blo 409770 413211 := bstep (se 1 (by rfl) ⟨309908, by rfl⟩ : syracuseStep 413211 = 619817) B619817
theorem B5296367 : Blo 409770 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B1987199 : Blo 409770 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B5952649 : Blo 409770 5952649 := bstep (se 2 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 5952649 = 4464487) B4464487
theorem B1562611 : Blo 409770 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B1563887 : Blo 409770 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B5991515 : Blo 409770 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B1900351 : Blo 409770 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B2229545 : Blo 409770 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B14224351 : Blo 409770 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B7015895 : Blo 409770 7015895 := bstep (se 1 (by rfl) ⟨5261921, by rfl⟩ : syracuseStep 7015895 = 10523843) B10523843
theorem B463999 : Blo 409770 463999 := bstep (se 1 (by rfl) ⟨347999, by rfl⟩ : syracuseStep 463999 = 695999) B695999
theorem B988399 : Blo 409770 988399 := bstep (se 1 (by rfl) ⟨741299, by rfl⟩ : syracuseStep 988399 = 1482599) B1482599
theorem B7936865 : Blo 409770 7936865 := bstep (se 2 (by rfl) ⟨2976324, by rfl⟩ : syracuseStep 7936865 = 5952649) B5952649
theorem B10135205 : Blo 409770 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B2500379 : Blo 409770 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B930041 : Blo 409770 930041 := bstep (se 2 (by rfl) ⟨348765, by rfl⟩ : syracuseStep 930041 = 697531) B697531
theorem B1324799 : Blo 409770 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B2081375 : Blo 409770 2081375 := bstep (se 1 (by rfl) ⟨1561031, by rfl⟩ : syracuseStep 2081375 = 3122063) B3122063
theorem B2083481 : Blo 409770 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B1563583 : Blo 409770 1563583 := bstep (se 1 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 1563583 = 2345375) B2345375
theorem B2383103 : Blo 409770 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B3530911 : Blo 409770 3530911 := bstep (se 1 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 3530911 = 5296367) B5296367
theorem B1042591 : Blo 409770 1042591 := bstep (se 1 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 1042591 = 1563887) B1563887
theorem B617015 : Blo 409770 617015 := bstep (se 1 (by rfl) ⟨462761, by rfl⟩ : syracuseStep 617015 = 925523) B925523
theorem B3994343 : Blo 409770 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B6756803 : Blo 409770 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B1317865 : Blo 409770 1317865 := bstep (se 2 (by rfl) ⟨494199, by rfl⟩ : syracuseStep 1317865 = 988399) B988399
theorem B2662895 : Blo 409770 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B1387583 : Blo 409770 1387583 := bstep (se 1 (by rfl) ⟨1040687, by rfl⟩ : syracuseStep 1387583 = 2081375) B2081375
theorem B1486363 : Blo 409770 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B1388987 : Blo 409770 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B1390121 : Blo 409770 1390121 := bstep (se 2 (by rfl) ⟨521295, by rfl⟩ : syracuseStep 1390121 = 1042591) B1042591
theorem B5291243 : Blo 409770 5291243 := bstep (se 1 (by rfl) ⟨3968432, by rfl⟩ : syracuseStep 5291243 = 7936865) B7936865
theorem B1588735 : Blo 409770 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B411343 : Blo 409770 411343 := bstep (se 1 (by rfl) ⟨308507, by rfl⟩ : syracuseStep 411343 = 617015) B617015
theorem B2084777 : Blo 409770 2084777 := bstep (se 2 (by rfl) ⟨781791, by rfl⟩ : syracuseStep 2084777 = 1563583) B1563583
theorem B4707881 : Blo 409770 4707881 := bstep (se 2 (by rfl) ⟨1765455, by rfl⟩ : syracuseStep 4707881 = 3530911) B3530911
theorem B4677263 : Blo 409770 4677263 := bstep (se 1 (by rfl) ⟨3507947, by rfl⟩ : syracuseStep 4677263 = 7015895) B7015895
theorem B18965801 : Blo 409770 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B1666919 : Blo 409770 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B618665 : Blo 409770 618665 := bstep (se 2 (by rfl) ⟨231999, by rfl⟩ : syracuseStep 618665 = 463999) B463999
theorem B620027 : Blo 409770 620027 := bstep (se 1 (by rfl) ⟨465020, by rfl⟩ : syracuseStep 620027 = 930041) B930041
theorem B883199 : Blo 409770 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B3118175 : Blo 409770 3118175 := bstep (se 1 (by rfl) ⟨2338631, by rfl⟩ : syracuseStep 3118175 = 4677263) B4677263
theorem B925055 : Blo 409770 925055 := bstep (se 1 (by rfl) ⟨693791, by rfl⟩ : syracuseStep 925055 = 1387583) B1387583
theorem B925991 : Blo 409770 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B926747 : Blo 409770 926747 := bstep (se 1 (by rfl) ⟨695060, by rfl⟩ : syracuseStep 926747 = 1390121) B1390121
theorem B1389851 : Blo 409770 1389851 := bstep (se 1 (by rfl) ⟨1042388, by rfl⟩ : syracuseStep 1389851 = 2084777) B2084777
theorem B4504535 : Blo 409770 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B1981817 : Blo 409770 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B412443 : Blo 409770 412443 := bstep (se 1 (by rfl) ⟨309332, by rfl⟩ : syracuseStep 412443 = 618665) B618665
theorem B413351 : Blo 409770 413351 := bstep (se 1 (by rfl) ⟨310013, by rfl⟩ : syracuseStep 413351 = 620027) B620027
theorem B1757153 : Blo 409770 1757153 := bstep (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) B1317865
theorem B2118313 : Blo 409770 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B3527495 : Blo 409770 3527495 := bstep (se 1 (by rfl) ⟨2645621, by rfl⟩ : syracuseStep 3527495 = 5291243) B5291243
theorem B7101053 : Blo 409770 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B3138587 : Blo 409770 3138587 := bstep (se 1 (by rfl) ⟨2353940, by rfl⟩ : syracuseStep 3138587 = 4707881) B4707881
theorem B12643867 : Blo 409770 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B1111279 : Blo 409770 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B588799 : Blo 409770 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B2824417 : Blo 409770 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B1481705 : Blo 409770 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B926567 : Blo 409770 926567 := bstep (se 1 (by rfl) ⟨694925, by rfl⟩ : syracuseStep 926567 = 1389851) B1389851
theorem B1321211 : Blo 409770 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B2078783 : Blo 409770 2078783 := bstep (se 1 (by rfl) ⟨1559087, by rfl⟩ : syracuseStep 2078783 = 3118175) B3118175
theorem B4734035 : Blo 409770 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B3003023 : Blo 409770 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B1171435 : Blo 409770 1171435 := bstep (se 1 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 1171435 = 1757153) B1757153
theorem B2351663 : Blo 409770 2351663 := bstep (se 1 (by rfl) ⟨1763747, by rfl⟩ : syracuseStep 2351663 = 3527495) B3527495
theorem B616703 : Blo 409770 616703 := bstep (se 1 (by rfl) ⟨462527, by rfl⟩ : syracuseStep 616703 = 925055) B925055
theorem B617327 : Blo 409770 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B617831 : Blo 409770 617831 := bstep (se 1 (by rfl) ⟨463373, by rfl⟩ : syracuseStep 617831 = 926747) B926747
theorem B2092391 : Blo 409770 2092391 := bstep (se 1 (by rfl) ⟨1569293, by rfl⟩ : syracuseStep 2092391 = 3138587) B3138587
theorem B67433957 : Blo 409770 67433957 := bstep (se 4 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 67433957 = 12643867) B12643867
theorem B785065 : Blo 409770 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B2002015 : Blo 409770 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B987803 : Blo 409770 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B1385855 : Blo 409770 1385855 := bstep (se 1 (by rfl) ⟨1039391, by rfl⟩ : syracuseStep 1385855 = 2078783) B2078783
theorem B3156023 : Blo 409770 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B411135 : Blo 409770 411135 := bstep (se 1 (by rfl) ⟨308351, by rfl⟩ : syracuseStep 411135 = 616703) B616703
theorem B411551 : Blo 409770 411551 := bstep (se 1 (by rfl) ⟨308663, by rfl⟩ : syracuseStep 411551 = 617327) B617327
theorem B411887 : Blo 409770 411887 := bstep (se 1 (by rfl) ⟨308915, by rfl⟩ : syracuseStep 411887 = 617831) B617831
theorem B1394927 : Blo 409770 1394927 := bstep (se 1 (by rfl) ⟨1046195, by rfl⟩ : syracuseStep 1394927 = 2092391) B2092391
theorem B1561913 : Blo 409770 1561913 := bstep (se 2 (by rfl) ⟨585717, by rfl⟩ : syracuseStep 1561913 = 1171435) B1171435
theorem B1567775 : Blo 409770 1567775 := bstep (se 1 (by rfl) ⟨1175831, by rfl⟩ : syracuseStep 1567775 = 2351663) B2351663
theorem B617711 : Blo 409770 617711 := bstep (se 1 (by rfl) ⟨463283, by rfl⟩ : syracuseStep 617711 = 926567) B926567
theorem B880807 : Blo 409770 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B3765889 : Blo 409770 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B1046753 : Blo 409770 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B44955971 : Blo 409770 44955971 := bstep (se 1 (by rfl) ⟨33716978, by rfl⟩ : syracuseStep 44955971 = 67433957) B67433957
theorem B658535 : Blo 409770 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B923903 : Blo 409770 923903 := bstep (se 1 (by rfl) ⟨692927, by rfl⟩ : syracuseStep 923903 = 1385855) B1385855
theorem B2104015 : Blo 409770 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B5021185 : Blo 409770 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B697835 : Blo 409770 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B929951 : Blo 409770 929951 := bstep (se 1 (by rfl) ⟨697463, by rfl⟩ : syracuseStep 929951 = 1394927) B1394927
theorem B411807 : Blo 409770 411807 := bstep (se 1 (by rfl) ⟨308855, by rfl⟩ : syracuseStep 411807 = 617711) B617711
theorem B29970647 : Blo 409770 29970647 := bstep (se 1 (by rfl) ⟨22477985, by rfl⟩ : syracuseStep 29970647 = 44955971) B44955971
theorem B1041275 : Blo 409770 1041275 := bstep (se 1 (by rfl) ⟨780956, by rfl⟩ : syracuseStep 1041275 = 1561913) B1561913
theorem B1174409 : Blo 409770 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B10677413 : Blo 409770 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B1045183 : Blo 409770 1045183 := bstep (se 1 (by rfl) ⟨783887, by rfl⟩ : syracuseStep 1045183 = 1567775) B1567775
theorem B694183 : Blo 409770 694183 := bstep (se 1 (by rfl) ⟨520637, by rfl⟩ : syracuseStep 694183 = 1041275) B1041275
theorem B465223 : Blo 409770 465223 := bstep (se 1 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 465223 = 697835) B697835
theorem B7118275 : Blo 409770 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B6694913 : Blo 409770 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B1393577 : Blo 409770 1393577 := bstep (se 2 (by rfl) ⟨522591, by rfl⟩ : syracuseStep 1393577 = 1045183) B1045183
theorem B1756093 : Blo 409770 1756093 := bstep (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) B658535
theorem B2805353 : Blo 409770 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B19980431 : Blo 409770 19980431 := bstep (se 1 (by rfl) ⟨14985323, by rfl⟩ : syracuseStep 19980431 = 29970647) B29970647
theorem B615935 : Blo 409770 615935 := bstep (se 1 (by rfl) ⟨461951, by rfl⟩ : syracuseStep 615935 = 923903) B923903
theorem B782939 : Blo 409770 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B619967 : Blo 409770 619967 := bstep (se 1 (by rfl) ⟨464975, by rfl⟩ : syracuseStep 619967 = 929951) B929951
theorem B1870235 : Blo 409770 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B4463275 : Blo 409770 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B925577 : Blo 409770 925577 := bstep (se 2 (by rfl) ⟨347091, by rfl⟩ : syracuseStep 925577 = 694183) B694183
theorem B929051 : Blo 409770 929051 := bstep (se 1 (by rfl) ⟨696788, by rfl⟩ : syracuseStep 929051 = 1393577) B1393577
theorem B2341457 : Blo 409770 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B13320287 : Blo 409770 13320287 := bstep (se 1 (by rfl) ⟨9990215, by rfl⟩ : syracuseStep 13320287 = 19980431) B19980431
theorem B410623 : Blo 409770 410623 := bstep (se 1 (by rfl) ⟨307967, by rfl⟩ : syracuseStep 410623 = 615935) B615935
theorem B413311 : Blo 409770 413311 := bstep (se 1 (by rfl) ⟨309983, by rfl⟩ : syracuseStep 413311 = 619967) B619967
theorem B9491033 : Blo 409770 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B521959 : Blo 409770 521959 := bstep (se 1 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 521959 = 782939) B782939
theorem B620297 : Blo 409770 620297 := bstep (se 2 (by rfl) ⟨232611, by rfl⟩ : syracuseStep 620297 = 465223) B465223
theorem B8880191 : Blo 409770 8880191 := bstep (se 1 (by rfl) ⟨6660143, by rfl⟩ : syracuseStep 8880191 = 13320287) B13320287
theorem B1246823 : Blo 409770 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B695945 : Blo 409770 695945 := bstep (se 2 (by rfl) ⟨260979, by rfl⟩ : syracuseStep 695945 = 521959) B521959
theorem B25309421 : Blo 409770 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B5951033 : Blo 409770 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B413531 : Blo 409770 413531 := bstep (se 1 (by rfl) ⟨310148, by rfl⟩ : syracuseStep 413531 = 620297) B620297
theorem B1560971 : Blo 409770 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B617051 : Blo 409770 617051 := bstep (se 1 (by rfl) ⟨462788, by rfl⟩ : syracuseStep 617051 = 925577) B925577
theorem B619367 : Blo 409770 619367 := bstep (se 1 (by rfl) ⟨464525, by rfl⟩ : syracuseStep 619367 = 929051) B929051
theorem B3967355 : Blo 409770 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B463963 : Blo 409770 463963 := bstep (se 1 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 463963 = 695945) B695945
theorem B831215 : Blo 409770 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B411367 : Blo 409770 411367 := bstep (se 1 (by rfl) ⟨308525, by rfl⟩ : syracuseStep 411367 = 617051) B617051
theorem B412911 : Blo 409770 412911 := bstep (se 1 (by rfl) ⟨309683, by rfl⟩ : syracuseStep 412911 = 619367) B619367
theorem B5920127 : Blo 409770 5920127 := bstep (se 1 (by rfl) ⟨4440095, by rfl⟩ : syracuseStep 5920127 = 8880191) B8880191
theorem B1040647 : Blo 409770 1040647 := bstep (se 1 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 1040647 = 1560971) B1560971
theorem B16872947 : Blo 409770 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B11248631 : Blo 409770 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B1387529 : Blo 409770 1387529 := bstep (se 2 (by rfl) ⟨520323, by rfl⟩ : syracuseStep 1387529 = 1040647) B1040647
theorem B3946751 : Blo 409770 3946751 := bstep (se 1 (by rfl) ⟨2960063, by rfl⟩ : syracuseStep 3946751 = 5920127) B5920127
theorem B2644903 : Blo 409770 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B618617 : Blo 409770 618617 := bstep (se 2 (by rfl) ⟨231981, by rfl⟩ : syracuseStep 618617 = 463963) B463963
theorem B554143 : Blo 409770 554143 := bstep (se 1 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 554143 = 831215) B831215
theorem B925019 : Blo 409770 925019 := bstep (se 1 (by rfl) ⟨693764, by rfl⟩ : syracuseStep 925019 = 1387529) B1387529
theorem B2631167 : Blo 409770 2631167 := bstep (se 1 (by rfl) ⟨1973375, by rfl⟩ : syracuseStep 2631167 = 3946751) B3946751
theorem B738857 : Blo 409770 738857 := bstep (se 2 (by rfl) ⟨277071, by rfl⟩ : syracuseStep 738857 = 554143) B554143
theorem B412411 : Blo 409770 412411 := bstep (se 1 (by rfl) ⟨309308, by rfl⟩ : syracuseStep 412411 = 618617) B618617
theorem B3526537 : Blo 409770 3526537 := bstep (se 2 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 3526537 = 2644903) B2644903
theorem B7499087 : Blo 409770 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B492571 : Blo 409770 492571 := bstep (se 1 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 492571 = 738857) B738857
theorem B4702049 : Blo 409770 4702049 := bstep (se 2 (by rfl) ⟨1763268, by rfl⟩ : syracuseStep 4702049 = 3526537) B3526537
theorem B1754111 : Blo 409770 1754111 := bstep (se 1 (by rfl) ⟨1315583, by rfl⟩ : syracuseStep 1754111 = 2631167) B2631167
theorem B4999391 : Blo 409770 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B616679 : Blo 409770 616679 := bstep (se 1 (by rfl) ⟨462509, by rfl⟩ : syracuseStep 616679 = 925019) B925019
theorem B656761 : Blo 409770 656761 := bstep (se 2 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 656761 = 492571) B492571
theorem B411119 : Blo 409770 411119 := bstep (se 1 (by rfl) ⟨308339, by rfl⟩ : syracuseStep 411119 = 616679) B616679
theorem B3134699 : Blo 409770 3134699 := bstep (se 1 (by rfl) ⟨2351024, by rfl⟩ : syracuseStep 3134699 = 4702049) B4702049
theorem B1169407 : Blo 409770 1169407 := bstep (se 1 (by rfl) ⟨877055, by rfl⟩ : syracuseStep 1169407 = 1754111) B1754111
theorem B3332927 : Blo 409770 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B1559209 : Blo 409770 1559209 := bstep (se 2 (by rfl) ⟨584703, by rfl⟩ : syracuseStep 1559209 = 1169407) B1169407
theorem B875681 : Blo 409770 875681 := bstep (se 2 (by rfl) ⟨328380, by rfl⟩ : syracuseStep 875681 = 656761) B656761
theorem B2089799 : Blo 409770 2089799 := bstep (se 1 (by rfl) ⟨1567349, by rfl⟩ : syracuseStep 2089799 = 3134699) B3134699
theorem B2221951 : Blo 409770 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B2962601 : Blo 409770 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B2078945 : Blo 409770 2078945 := bstep (se 2 (by rfl) ⟨779604, by rfl⟩ : syracuseStep 2078945 = 1559209) B1559209
theorem B1393199 : Blo 409770 1393199 := bstep (se 1 (by rfl) ⟨1044899, by rfl⟩ : syracuseStep 1393199 = 2089799) B2089799
theorem B583787 : Blo 409770 583787 := bstep (se 1 (by rfl) ⟨437840, by rfl⟩ : syracuseStep 583787 = 875681) B875681
theorem B1975067 : Blo 409770 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B1385963 : Blo 409770 1385963 := bstep (se 1 (by rfl) ⟨1039472, by rfl⟩ : syracuseStep 1385963 = 2078945) B2078945
theorem B928799 : Blo 409770 928799 := bstep (se 1 (by rfl) ⟨696599, by rfl⟩ : syracuseStep 928799 = 1393199) B1393199
theorem B1556765 : Blo 409770 1556765 := bstep (se 3 (by rfl) ⟨291893, by rfl⟩ : syracuseStep 1556765 = 583787) B583787
theorem B1316711 : Blo 409770 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B923975 : Blo 409770 923975 := bstep (se 1 (by rfl) ⟨692981, by rfl⟩ : syracuseStep 923975 = 1385963) B1385963
theorem B1037843 : Blo 409770 1037843 := bstep (se 1 (by rfl) ⟨778382, by rfl⟩ : syracuseStep 1037843 = 1556765) B1556765
theorem B619199 : Blo 409770 619199 := bstep (se 1 (by rfl) ⟨464399, by rfl⟩ : syracuseStep 619199 = 928799) B928799
theorem B691895 : Blo 409770 691895 := bstep (se 1 (by rfl) ⟨518921, by rfl⟩ : syracuseStep 691895 = 1037843) B1037843
theorem B412799 : Blo 409770 412799 := bstep (se 1 (by rfl) ⟨309599, by rfl⟩ : syracuseStep 412799 = 619199) B619199
theorem B877807 : Blo 409770 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B615983 : Blo 409770 615983 := bstep (se 1 (by rfl) ⟨461987, by rfl⟩ : syracuseStep 615983 = 923975) B923975
theorem B461263 : Blo 409770 461263 := bstep (se 1 (by rfl) ⟨345947, by rfl⟩ : syracuseStep 461263 = 691895) B691895
theorem B410655 : Blo 409770 410655 := bstep (se 1 (by rfl) ⟨307991, by rfl⟩ : syracuseStep 410655 = 615983) B615983
theorem B4681637 : Blo 409770 4681637 := bstep (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) B877807
theorem B3121091 : Blo 409770 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B615017 : Blo 409770 615017 := bstep (se 2 (by rfl) ⟨230631, by rfl⟩ : syracuseStep 615017 = 461263) B461263
theorem B2080727 : Blo 409770 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B410011 : Blo 409770 410011 := bstep (se 1 (by rfl) ⟨307508, by rfl⟩ : syracuseStep 410011 = 615017) B615017
theorem B1387151 : Blo 409770 1387151 := bstep (se 1 (by rfl) ⟨1040363, by rfl⟩ : syracuseStep 1387151 = 2080727) B2080727
theorem B924767 : Blo 409770 924767 := bstep (se 1 (by rfl) ⟨693575, by rfl⟩ : syracuseStep 924767 = 1387151) B1387151
theorem B616511 : Blo 409770 616511 := bstep (se 1 (by rfl) ⟨462383, by rfl⟩ : syracuseStep 616511 = 924767) B924767
theorem B411007 : Blo 409770 411007 := bstep (se 1 (by rfl) ⟨308255, by rfl⟩ : syracuseStep 411007 = 616511) B616511

theorem C0 (j : ℕ) (h1 : 102442 ≤ j) (h2 : j ≤ 103141) : Blo 409770 (4 * j + 3) := by
  interval_cases j
  · exact B409771
  · exact B409775
  · exact B409779
  · exact B409783
  · exact B409787
  · exact B409791
  · exact B409795
  · exact B409799
  · exact B409803
  · exact B409807
  · exact B409811
  · exact B409815
  · exact B409819
  · exact B409823
  · exact B409827
  · exact B409831
  · exact B409835
  · exact B409839
  · exact B409843
  · exact B409847
  · exact B409851
  · exact B409855
  · exact B409859
  · exact B409863
  · exact B409867
  · exact B409871
  · exact B409875
  · exact B409879
  · exact B409883
  · exact B409887
  · exact B409891
  · exact B409895
  · exact B409899
  · exact B409903
  · exact B409907
  · exact B409911
  · exact B409915
  · exact B409919
  · exact B409923
  · exact B409927
  · exact B409931
  · exact B409935
  · exact B409939
  · exact B409943
  · exact B409947
  · exact B409951
  · exact B409955
  · exact B409959
  · exact B409963
  · exact B409967
  · exact B409971
  · exact B409975
  · exact B409979
  · exact B409983
  · exact B409987
  · exact B409991
  · exact B409995
  · exact B409999
  · exact B410003
  · exact B410007
  · exact B410011
  · exact B410015
  · exact B410019
  · exact B410023
  · exact B410027
  · exact B410031
  · exact B410035
  · exact B410039
  · exact B410043
  · exact B410047
  · exact B410051
  · exact B410055
  · exact B410059
  · exact B410063
  · exact B410067
  · exact B410071
  · exact B410075
  · exact B410079
  · exact B410083
  · exact B410087
  · exact B410091
  · exact B410095
  · exact B410099
  · exact B410103
  · exact B410107
  · exact B410111
  · exact B410115
  · exact B410119
  · exact B410123
  · exact B410127
  · exact B410131
  · exact B410135
  · exact B410139
  · exact B410143
  · exact B410147
  · exact B410151
  · exact B410155
  · exact B410159
  · exact B410163
  · exact B410167
  · exact B410171
  · exact B410175
  · exact B410179
  · exact B410183
  · exact B410187
  · exact B410191
  · exact B410195
  · exact B410199
  · exact B410203
  · exact B410207
  · exact B410211
  · exact B410215
  · exact B410219
  · exact B410223
  · exact B410227
  · exact B410231
  · exact B410235
  · exact B410239
  · exact B410243
  · exact B410247
  · exact B410251
  · exact B410255
  · exact B410259
  · exact B410263
  · exact B410267
  · exact B410271
  · exact B410275
  · exact B410279
  · exact B410283
  · exact B410287
  · exact B410291
  · exact B410295
  · exact B410299
  · exact B410303
  · exact B410307
  · exact B410311
  · exact B410315
  · exact B410319
  · exact B410323
  · exact B410327
  · exact B410331
  · exact B410335
  · exact B410339
  · exact B410343
  · exact B410347
  · exact B410351
  · exact B410355
  · exact B410359
  · exact B410363
  · exact B410367
  · exact B410371
  · exact B410375
  · exact B410379
  · exact B410383
  · exact B410387
  · exact B410391
  · exact B410395
  · exact B410399
  · exact B410403
  · exact B410407
  · exact B410411
  · exact B410415
  · exact B410419
  · exact B410423
  · exact B410427
  · exact B410431
  · exact B410435
  · exact B410439
  · exact B410443
  · exact B410447
  · exact B410451
  · exact B410455
  · exact B410459
  · exact B410463
  · exact B410467
  · exact B410471
  · exact B410475
  · exact B410479
  · exact B410483
  · exact B410487
  · exact B410491
  · exact B410495
  · exact B410499
  · exact B410503
  · exact B410507
  · exact B410511
  · exact B410515
  · exact B410519
  · exact B410523
  · exact B410527
  · exact B410531
  · exact B410535
  · exact B410539
  · exact B410543
  · exact B410547
  · exact B410551
  · exact B410555
  · exact B410559
  · exact B410563
  · exact B410567
  · exact B410571
  · exact B410575
  · exact B410579
  · exact B410583
  · exact B410587
  · exact B410591
  · exact B410595
  · exact B410599
  · exact B410603
  · exact B410607
  · exact B410611
  · exact B410615
  · exact B410619
  · exact B410623
  · exact B410627
  · exact B410631
  · exact B410635
  · exact B410639
  · exact B410643
  · exact B410647
  · exact B410651
  · exact B410655
  · exact B410659
  · exact B410663
  · exact B410667
  · exact B410671
  · exact B410675
  · exact B410679
  · exact B410683
  · exact B410687
  · exact B410691
  · exact B410695
  · exact B410699
  · exact B410703
  · exact B410707
  · exact B410711
  · exact B410715
  · exact B410719
  · exact B410723
  · exact B410727
  · exact B410731
  · exact B410735
  · exact B410739
  · exact B410743
  · exact B410747
  · exact B410751
  · exact B410755
  · exact B410759
  · exact B410763
  · exact B410767
  · exact B410771
  · exact B410775
  · exact B410779
  · exact B410783
  · exact B410787
  · exact B410791
  · exact B410795
  · exact B410799
  · exact B410803
  · exact B410807
  · exact B410811
  · exact B410815
  · exact B410819
  · exact B410823
  · exact B410827
  · exact B410831
  · exact B410835
  · exact B410839
  · exact B410843
  · exact B410847
  · exact B410851
  · exact B410855
  · exact B410859
  · exact B410863
  · exact B410867
  · exact B410871
  · exact B410875
  · exact B410879
  · exact B410883
  · exact B410887
  · exact B410891
  · exact B410895
  · exact B410899
  · exact B410903
  · exact B410907
  · exact B410911
  · exact B410915
  · exact B410919
  · exact B410923
  · exact B410927
  · exact B410931
  · exact B410935
  · exact B410939
  · exact B410943
  · exact B410947
  · exact B410951
  · exact B410955
  · exact B410959
  · exact B410963
  · exact B410967
  · exact B410971
  · exact B410975
  · exact B410979
  · exact B410983
  · exact B410987
  · exact B410991
  · exact B410995
  · exact B410999
  · exact B411003
  · exact B411007
  · exact B411011
  · exact B411015
  · exact B411019
  · exact B411023
  · exact B411027
  · exact B411031
  · exact B411035
  · exact B411039
  · exact B411043
  · exact B411047
  · exact B411051
  · exact B411055
  · exact B411059
  · exact B411063
  · exact B411067
  · exact B411071
  · exact B411075
  · exact B411079
  · exact B411083
  · exact B411087
  · exact B411091
  · exact B411095
  · exact B411099
  · exact B411103
  · exact B411107
  · exact B411111
  · exact B411115
  · exact B411119
  · exact B411123
  · exact B411127
  · exact B411131
  · exact B411135
  · exact B411139
  · exact B411143
  · exact B411147
  · exact B411151
  · exact B411155
  · exact B411159
  · exact B411163
  · exact B411167
  · exact B411171
  · exact B411175
  · exact B411179
  · exact B411183
  · exact B411187
  · exact B411191
  · exact B411195
  · exact B411199
  · exact B411203
  · exact B411207
  · exact B411211
  · exact B411215
  · exact B411219
  · exact B411223
  · exact B411227
  · exact B411231
  · exact B411235
  · exact B411239
  · exact B411243
  · exact B411247
  · exact B411251
  · exact B411255
  · exact B411259
  · exact B411263
  · exact B411267
  · exact B411271
  · exact B411275
  · exact B411279
  · exact B411283
  · exact B411287
  · exact B411291
  · exact B411295
  · exact B411299
  · exact B411303
  · exact B411307
  · exact B411311
  · exact B411315
  · exact B411319
  · exact B411323
  · exact B411327
  · exact B411331
  · exact B411335
  · exact B411339
  · exact B411343
  · exact B411347
  · exact B411351
  · exact B411355
  · exact B411359
  · exact B411363
  · exact B411367
  · exact B411371
  · exact B411375
  · exact B411379
  · exact B411383
  · exact B411387
  · exact B411391
  · exact B411395
  · exact B411399
  · exact B411403
  · exact B411407
  · exact B411411
  · exact B411415
  · exact B411419
  · exact B411423
  · exact B411427
  · exact B411431
  · exact B411435
  · exact B411439
  · exact B411443
  · exact B411447
  · exact B411451
  · exact B411455
  · exact B411459
  · exact B411463
  · exact B411467
  · exact B411471
  · exact B411475
  · exact B411479
  · exact B411483
  · exact B411487
  · exact B411491
  · exact B411495
  · exact B411499
  · exact B411503
  · exact B411507
  · exact B411511
  · exact B411515
  · exact B411519
  · exact B411523
  · exact B411527
  · exact B411531
  · exact B411535
  · exact B411539
  · exact B411543
  · exact B411547
  · exact B411551
  · exact B411555
  · exact B411559
  · exact B411563
  · exact B411567
  · exact B411571
  · exact B411575
  · exact B411579
  · exact B411583
  · exact B411587
  · exact B411591
  · exact B411595
  · exact B411599
  · exact B411603
  · exact B411607
  · exact B411611
  · exact B411615
  · exact B411619
  · exact B411623
  · exact B411627
  · exact B411631
  · exact B411635
  · exact B411639
  · exact B411643
  · exact B411647
  · exact B411651
  · exact B411655
  · exact B411659
  · exact B411663
  · exact B411667
  · exact B411671
  · exact B411675
  · exact B411679
  · exact B411683
  · exact B411687
  · exact B411691
  · exact B411695
  · exact B411699
  · exact B411703
  · exact B411707
  · exact B411711
  · exact B411715
  · exact B411719
  · exact B411723
  · exact B411727
  · exact B411731
  · exact B411735
  · exact B411739
  · exact B411743
  · exact B411747
  · exact B411751
  · exact B411755
  · exact B411759
  · exact B411763
  · exact B411767
  · exact B411771
  · exact B411775
  · exact B411779
  · exact B411783
  · exact B411787
  · exact B411791
  · exact B411795
  · exact B411799
  · exact B411803
  · exact B411807
  · exact B411811
  · exact B411815
  · exact B411819
  · exact B411823
  · exact B411827
  · exact B411831
  · exact B411835
  · exact B411839
  · exact B411843
  · exact B411847
  · exact B411851
  · exact B411855
  · exact B411859
  · exact B411863
  · exact B411867
  · exact B411871
  · exact B411875
  · exact B411879
  · exact B411883
  · exact B411887
  · exact B411891
  · exact B411895
  · exact B411899
  · exact B411903
  · exact B411907
  · exact B411911
  · exact B411915
  · exact B411919
  · exact B411923
  · exact B411927
  · exact B411931
  · exact B411935
  · exact B411939
  · exact B411943
  · exact B411947
  · exact B411951
  · exact B411955
  · exact B411959
  · exact B411963
  · exact B411967
  · exact B411971
  · exact B411975
  · exact B411979
  · exact B411983
  · exact B411987
  · exact B411991
  · exact B411995
  · exact B411999
  · exact B412003
  · exact B412007
  · exact B412011
  · exact B412015
  · exact B412019
  · exact B412023
  · exact B412027
  · exact B412031
  · exact B412035
  · exact B412039
  · exact B412043
  · exact B412047
  · exact B412051
  · exact B412055
  · exact B412059
  · exact B412063
  · exact B412067
  · exact B412071
  · exact B412075
  · exact B412079
  · exact B412083
  · exact B412087
  · exact B412091
  · exact B412095
  · exact B412099
  · exact B412103
  · exact B412107
  · exact B412111
  · exact B412115
  · exact B412119
  · exact B412123
  · exact B412127
  · exact B412131
  · exact B412135
  · exact B412139
  · exact B412143
  · exact B412147
  · exact B412151
  · exact B412155
  · exact B412159
  · exact B412163
  · exact B412167
  · exact B412171
  · exact B412175
  · exact B412179
  · exact B412183
  · exact B412187
  · exact B412191
  · exact B412195
  · exact B412199
  · exact B412203
  · exact B412207
  · exact B412211
  · exact B412215
  · exact B412219
  · exact B412223
  · exact B412227
  · exact B412231
  · exact B412235
  · exact B412239
  · exact B412243
  · exact B412247
  · exact B412251
  · exact B412255
  · exact B412259
  · exact B412263
  · exact B412267
  · exact B412271
  · exact B412275
  · exact B412279
  · exact B412283
  · exact B412287
  · exact B412291
  · exact B412295
  · exact B412299
  · exact B412303
  · exact B412307
  · exact B412311
  · exact B412315
  · exact B412319
  · exact B412323
  · exact B412327
  · exact B412331
  · exact B412335
  · exact B412339
  · exact B412343
  · exact B412347
  · exact B412351
  · exact B412355
  · exact B412359
  · exact B412363
  · exact B412367
  · exact B412371
  · exact B412375
  · exact B412379
  · exact B412383
  · exact B412387
  · exact B412391
  · exact B412395
  · exact B412399
  · exact B412403
  · exact B412407
  · exact B412411
  · exact B412415
  · exact B412419
  · exact B412423
  · exact B412427
  · exact B412431
  · exact B412435
  · exact B412439
  · exact B412443
  · exact B412447
  · exact B412451
  · exact B412455
  · exact B412459
  · exact B412463
  · exact B412467
  · exact B412471
  · exact B412475
  · exact B412479
  · exact B412483
  · exact B412487
  · exact B412491
  · exact B412495
  · exact B412499
  · exact B412503
  · exact B412507
  · exact B412511
  · exact B412515
  · exact B412519
  · exact B412523
  · exact B412527
  · exact B412531
  · exact B412535
  · exact B412539
  · exact B412543
  · exact B412547
  · exact B412551
  · exact B412555
  · exact B412559
  · exact B412563
  · exact B412567

theorem C1 (j : ℕ) (h1 : 103142 ≤ j) (h2 : j ≤ 103441) : Blo 409770 (4 * j + 3) := by
  interval_cases j
  · exact B412571
  · exact B412575
  · exact B412579
  · exact B412583
  · exact B412587
  · exact B412591
  · exact B412595
  · exact B412599
  · exact B412603
  · exact B412607
  · exact B412611
  · exact B412615
  · exact B412619
  · exact B412623
  · exact B412627
  · exact B412631
  · exact B412635
  · exact B412639
  · exact B412643
  · exact B412647
  · exact B412651
  · exact B412655
  · exact B412659
  · exact B412663
  · exact B412667
  · exact B412671
  · exact B412675
  · exact B412679
  · exact B412683
  · exact B412687
  · exact B412691
  · exact B412695
  · exact B412699
  · exact B412703
  · exact B412707
  · exact B412711
  · exact B412715
  · exact B412719
  · exact B412723
  · exact B412727
  · exact B412731
  · exact B412735
  · exact B412739
  · exact B412743
  · exact B412747
  · exact B412751
  · exact B412755
  · exact B412759
  · exact B412763
  · exact B412767
  · exact B412771
  · exact B412775
  · exact B412779
  · exact B412783
  · exact B412787
  · exact B412791
  · exact B412795
  · exact B412799
  · exact B412803
  · exact B412807
  · exact B412811
  · exact B412815
  · exact B412819
  · exact B412823
  · exact B412827
  · exact B412831
  · exact B412835
  · exact B412839
  · exact B412843
  · exact B412847
  · exact B412851
  · exact B412855
  · exact B412859
  · exact B412863
  · exact B412867
  · exact B412871
  · exact B412875
  · exact B412879
  · exact B412883
  · exact B412887
  · exact B412891
  · exact B412895
  · exact B412899
  · exact B412903
  · exact B412907
  · exact B412911
  · exact B412915
  · exact B412919
  · exact B412923
  · exact B412927
  · exact B412931
  · exact B412935
  · exact B412939
  · exact B412943
  · exact B412947
  · exact B412951
  · exact B412955
  · exact B412959
  · exact B412963
  · exact B412967
  · exact B412971
  · exact B412975
  · exact B412979
  · exact B412983
  · exact B412987
  · exact B412991
  · exact B412995
  · exact B412999
  · exact B413003
  · exact B413007
  · exact B413011
  · exact B413015
  · exact B413019
  · exact B413023
  · exact B413027
  · exact B413031
  · exact B413035
  · exact B413039
  · exact B413043
  · exact B413047
  · exact B413051
  · exact B413055
  · exact B413059
  · exact B413063
  · exact B413067
  · exact B413071
  · exact B413075
  · exact B413079
  · exact B413083
  · exact B413087
  · exact B413091
  · exact B413095
  · exact B413099
  · exact B413103
  · exact B413107
  · exact B413111
  · exact B413115
  · exact B413119
  · exact B413123
  · exact B413127
  · exact B413131
  · exact B413135
  · exact B413139
  · exact B413143
  · exact B413147
  · exact B413151
  · exact B413155
  · exact B413159
  · exact B413163
  · exact B413167
  · exact B413171
  · exact B413175
  · exact B413179
  · exact B413183
  · exact B413187
  · exact B413191
  · exact B413195
  · exact B413199
  · exact B413203
  · exact B413207
  · exact B413211
  · exact B413215
  · exact B413219
  · exact B413223
  · exact B413227
  · exact B413231
  · exact B413235
  · exact B413239
  · exact B413243
  · exact B413247
  · exact B413251
  · exact B413255
  · exact B413259
  · exact B413263
  · exact B413267
  · exact B413271
  · exact B413275
  · exact B413279
  · exact B413283
  · exact B413287
  · exact B413291
  · exact B413295
  · exact B413299
  · exact B413303
  · exact B413307
  · exact B413311
  · exact B413315
  · exact B413319
  · exact B413323
  · exact B413327
  · exact B413331
  · exact B413335
  · exact B413339
  · exact B413343
  · exact B413347
  · exact B413351
  · exact B413355
  · exact B413359
  · exact B413363
  · exact B413367
  · exact B413371
  · exact B413375
  · exact B413379
  · exact B413383
  · exact B413387
  · exact B413391
  · exact B413395
  · exact B413399
  · exact B413403
  · exact B413407
  · exact B413411
  · exact B413415
  · exact B413419
  · exact B413423
  · exact B413427
  · exact B413431
  · exact B413435
  · exact B413439
  · exact B413443
  · exact B413447
  · exact B413451
  · exact B413455
  · exact B413459
  · exact B413463
  · exact B413467
  · exact B413471
  · exact B413475
  · exact B413479
  · exact B413483
  · exact B413487
  · exact B413491
  · exact B413495
  · exact B413499
  · exact B413503
  · exact B413507
  · exact B413511
  · exact B413515
  · exact B413519
  · exact B413523
  · exact B413527
  · exact B413531
  · exact B413535
  · exact B413539
  · exact B413543
  · exact B413547
  · exact B413551
  · exact B413555
  · exact B413559
  · exact B413563
  · exact B413567
  · exact B413571
  · exact B413575
  · exact B413579
  · exact B413583
  · exact B413587
  · exact B413591
  · exact B413595
  · exact B413599
  · exact B413603
  · exact B413607
  · exact B413611
  · exact B413615
  · exact B413619
  · exact B413623
  · exact B413627
  · exact B413631
  · exact B413635
  · exact B413639
  · exact B413643
  · exact B413647
  · exact B413651
  · exact B413655
  · exact B413659
  · exact B413663
  · exact B413667
  · exact B413671
  · exact B413675
  · exact B413679
  · exact B413683
  · exact B413687
  · exact B413691
  · exact B413695
  · exact B413699
  · exact B413703
  · exact B413707
  · exact B413711
  · exact B413715
  · exact B413719
  · exact B413723
  · exact B413727
  · exact B413731
  · exact B413735
  · exact B413739
  · exact B413743
  · exact B413747
  · exact B413751
  · exact B413755
  · exact B413759
  · exact B413763
  · exact B413767

theorem solution (m : ℕ) (hlo : 409770 ≤ m) (hhi : m ≤ 413770) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 102442 ≤ j := by omega
    have hj2 : j ≤ 103441 := by omega
    have hb : Blo 409770 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 103142 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
