-- Prove2me | solution 1 for syracuse_descends_range_1268452_1270452
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:27.133285+00:00
-- url     : https://prove2.me/submissions/f0342355-0c6a-4f8f-811f-f5d1260e4363

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


theorem B3964933 : Blo 1268452 3964933 := bbase (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) (by norm_num)
theorem B3211285 : Blo 1268452 3211285 := bbase (se 6 (by rfl) ⟨75264, by rfl⟩ : syracuseStep 3211285 = 150529) (by norm_num)
theorem B2711573 : Blo 1268452 2711573 := bbase (se 6 (by rfl) ⟨63552, by rfl⟩ : syracuseStep 2711573 = 127105) (by norm_num)
theorem B1605673 : Blo 1268452 1605673 := bbase (se 2 (by rfl) ⟨602127, by rfl⟩ : syracuseStep 1605673 = 1204255) (by norm_num)
theorem B2408525 : Blo 1268452 2408525 := bbase (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) (by norm_num)
theorem B3211397 : Blo 1268452 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B5791877 : Blo 1268452 5791877 := bbase (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) (by norm_num)
theorem B2711693 : Blo 1268452 2711693 := bbase (se 3 (by rfl) ⟨508442, by rfl⟩ : syracuseStep 2711693 = 1016885) (by norm_num)
theorem B1605845 : Blo 1268452 1605845 := bbase (se 7 (by rfl) ⟨18818, by rfl⟩ : syracuseStep 1605845 = 37637) (by norm_num)
theorem B4284629 : Blo 1268452 4284629 := bbase (se 7 (by rfl) ⟨50210, by rfl⟩ : syracuseStep 4284629 = 100421) (by norm_num)
theorem B4817141 : Blo 1268452 4817141 := bbase (se 5 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 4817141 = 451607) (by norm_num)
theorem B2285837 : Blo 1268452 2285837 := bbase (se 3 (by rfl) ⟨428594, by rfl⟩ : syracuseStep 2285837 = 857189) (by norm_num)
theorem B1605901 : Blo 1268452 1605901 := bbase (se 3 (by rfl) ⟨301106, by rfl⟩ : syracuseStep 1605901 = 602213) (by norm_num)
theorem B17367317 : Blo 1268452 17367317 := bbase (se 6 (by rfl) ⟨407046, by rfl⟩ : syracuseStep 17367317 = 814093) (by norm_num)
theorem B3211589 : Blo 1268452 3211589 := bbase (se 4 (by rfl) ⟨301086, by rfl⟩ : syracuseStep 3211589 = 602173) (by norm_num)
theorem B1605997 : Blo 1268452 1605997 := bbase (se 3 (by rfl) ⟨301124, by rfl⟩ : syracuseStep 1605997 = 602249) (by norm_num)
theorem B3613061 : Blo 1268452 3613061 := bbase (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) (by norm_num)
theorem B1286533 : Blo 1268452 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B2318725 : Blo 1268452 2318725 := bbase (se 4 (by rfl) ⟨217380, by rfl⟩ : syracuseStep 2318725 = 434761) (by norm_num)
theorem B4882837 : Blo 1268452 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B7717301 : Blo 1268452 7717301 := bbase (se 5 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 7717301 = 723497) (by norm_num)
theorem B4882949 : Blo 1268452 4882949 := bbase (se 4 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 4882949 = 915553) (by norm_num)
theorem B6431237 : Blo 1268452 6431237 := bbase (se 4 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 6431237 = 1205857) (by norm_num)
theorem B1524241 : Blo 1268452 1524241 := bbase (se 2 (by rfl) ⟨571590, by rfl⟩ : syracuseStep 1524241 = 1143181) (by norm_num)
theorem B1606169 : Blo 1268452 1606169 := bbase (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) (by norm_num)
theorem B5145157 : Blo 1268452 5145157 := bbase (se 4 (by rfl) ⟨482358, by rfl⟩ : syracuseStep 5145157 = 964717) (by norm_num)
theorem B1606225 : Blo 1268452 1606225 := bbase (se 2 (by rfl) ⟨602334, by rfl⟩ : syracuseStep 1606225 = 1204669) (by norm_num)
theorem B4285061 : Blo 1268452 4285061 := bbase (se 4 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 4285061 = 803449) (by norm_num)
theorem B14467733 : Blo 1268452 14467733 := bbase (se 6 (by rfl) ⟨339087, by rfl⟩ : syracuseStep 14467733 = 678175) (by norm_num)
theorem B3211933 : Blo 1268452 3211933 := bbase (se 3 (by rfl) ⟨602237, by rfl⟩ : syracuseStep 3211933 = 1204475) (by norm_num)
theorem B1606321 : Blo 1268452 1606321 := bbase (se 2 (by rfl) ⟨602370, by rfl⟩ : syracuseStep 1606321 = 1204741) (by norm_num)
theorem B4063925 : Blo 1268452 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B2032373 : Blo 1268452 2032373 := bbase (se 5 (by rfl) ⟨95267, by rfl⟩ : syracuseStep 2032373 = 190535) (by norm_num)
theorem B4342517 : Blo 1268452 4342517 := bbase (se 5 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 4342517 = 407111) (by norm_num)
theorem B2712325 : Blo 1268452 2712325 := bbase (se 4 (by rfl) ⟨254280, by rfl⟩ : syracuseStep 2712325 = 508561) (by norm_num)
theorem B3212045 : Blo 1268452 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B2409277 : Blo 1268452 2409277 := bbase (se 3 (by rfl) ⟨451739, by rfl⟩ : syracuseStep 2409277 = 903479) (by norm_num)
theorem B1606493 : Blo 1268452 1606493 := bbase (se 3 (by rfl) ⟨301217, by rfl⟩ : syracuseStep 1606493 = 602435) (by norm_num)
theorem B3433349 : Blo 1268452 3433349 := bbase (se 4 (by rfl) ⟨321876, by rfl⟩ : syracuseStep 3433349 = 643753) (by norm_num)
theorem B1606549 : Blo 1268452 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B6865813 : Blo 1268452 6865813 := bbase (se 6 (by rfl) ⟨160917, by rfl⟩ : syracuseStep 6865813 = 321835) (by norm_num)
theorem B6423461 : Blo 1268452 6423461 := bbase (se 4 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 6423461 = 1204399) (by norm_num)
theorem B2171845 : Blo 1268452 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B3212237 : Blo 1268452 3212237 := bbase (se 3 (by rfl) ⟨602294, by rfl⟩ : syracuseStep 3212237 = 1204589) (by norm_num)
theorem B2409421 : Blo 1268452 2409421 := bbase (se 3 (by rfl) ⟨451766, by rfl⟩ : syracuseStep 2409421 = 903533) (by norm_num)
theorem B18301909 : Blo 1268452 18301909 := bbase (se 7 (by rfl) ⟨214475, by rfl⟩ : syracuseStep 18301909 = 428951) (by norm_num)
theorem B1287133 : Blo 1268452 1287133 := bbase (se 3 (by rfl) ⟨241337, by rfl⟩ : syracuseStep 1287133 = 482675) (by norm_num)
theorem B1606645 : Blo 1268452 1606645 := bbase (se 5 (by rfl) ⟨75311, by rfl⟩ : syracuseStep 1606645 = 150623) (by norm_num)
theorem B4285493 : Blo 1268452 4285493 := bbase (se 5 (by rfl) ⟨200882, by rfl⟩ : syracuseStep 4285493 = 401765) (by norm_num)
theorem B2573389 : Blo 1268452 2573389 := bbase (se 3 (by rfl) ⟨482510, by rfl⟩ : syracuseStep 2573389 = 965021) (by norm_num)
theorem B2409581 : Blo 1268452 2409581 := bbase (se 3 (by rfl) ⟨451796, by rfl⟩ : syracuseStep 2409581 = 903593) (by norm_num)
theorem B1606817 : Blo 1268452 1606817 := bbase (se 2 (by rfl) ⟨602556, by rfl⟩ : syracuseStep 1606817 = 1205113) (by norm_num)
theorem B1606873 : Blo 1268452 1606873 := bbase (se 2 (by rfl) ⟨602577, by rfl⟩ : syracuseStep 1606873 = 1205155) (by norm_num)
theorem B3302621 : Blo 1268452 3302621 := bbase (se 3 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 3302621 = 1238483) (by norm_num)
theorem B2032885 : Blo 1268452 2032885 := bbase (se 5 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 2032885 = 190583) (by norm_num)
theorem B2409725 : Blo 1268452 2409725 := bbase (se 3 (by rfl) ⟨451823, by rfl⟩ : syracuseStep 2409725 = 903647) (by norm_num)
theorem B3212581 : Blo 1268452 3212581 := bbase (se 4 (by rfl) ⟨301179, by rfl⟩ : syracuseStep 3212581 = 602359) (by norm_num)
theorem B1606969 : Blo 1268452 1606969 := bbase (se 2 (by rfl) ⟨602613, by rfl⟩ : syracuseStep 1606969 = 1205227) (by norm_num)
theorem B3048781 : Blo 1268452 3048781 := bbase (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) (by norm_num)
theorem B4818325 : Blo 1268452 4818325 := bbase (se 6 (by rfl) ⟨112929, by rfl⟩ : syracuseStep 4818325 = 225859) (by norm_num)
theorem B3212693 : Blo 1268452 3212693 := bbase (se 6 (by rfl) ⟨75297, by rfl⟩ : syracuseStep 3212693 = 150595) (by norm_num)
theorem B7333301 : Blo 1268452 7333301 := bbase (se 5 (by rfl) ⟨343748, by rfl⟩ : syracuseStep 7333301 = 687497) (by norm_num)
theorem B1607141 : Blo 1268452 1607141 := bbase (se 4 (by rfl) ⟨150669, by rfl⟩ : syracuseStep 1607141 = 301339) (by norm_num)
theorem B4285925 : Blo 1268452 4285925 := bbase (se 4 (by rfl) ⟨401805, by rfl⟩ : syracuseStep 4285925 = 803611) (by norm_num)
theorem B2410013 : Blo 1268452 2410013 := bbase (se 3 (by rfl) ⟨451877, by rfl⟩ : syracuseStep 2410013 = 903755) (by norm_num)
theorem B1607197 : Blo 1268452 1607197 := bbase (se 3 (by rfl) ⟨301349, by rfl⟩ : syracuseStep 1607197 = 602699) (by norm_num)
theorem B1427017 : Blo 1268452 1427017 := bbase (se 2 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 1427017 = 1070263) (by norm_num)
theorem B3212885 : Blo 1268452 3212885 := bbase (se 8 (by rfl) ⟨18825, by rfl⟩ : syracuseStep 3212885 = 37651) (by norm_num)
theorem B1427053 : Blo 1268452 1427053 := bbase (se 3 (by rfl) ⟨267572, by rfl⟩ : syracuseStep 1427053 = 535145) (by norm_num)
theorem B7235189 : Blo 1268452 7235189 := bbase (se 5 (by rfl) ⟨339149, by rfl⟩ : syracuseStep 7235189 = 678299) (by norm_num)
theorem B1607293 : Blo 1268452 1607293 := bbase (se 3 (by rfl) ⟨301367, by rfl⟩ : syracuseStep 1607293 = 602735) (by norm_num)
theorem B2713213 : Blo 1268452 2713213 := bbase (se 3 (by rfl) ⟨508727, by rfl⟩ : syracuseStep 2713213 = 1017455) (by norm_num)
theorem B1427089 : Blo 1268452 1427089 := bbase (se 2 (by rfl) ⟨535158, by rfl⟩ : syracuseStep 1427089 = 1070317) (by norm_num)
theorem B1427125 : Blo 1268452 1427125 := bbase (se 5 (by rfl) ⟨66896, by rfl⟩ : syracuseStep 1427125 = 133793) (by norm_num)
theorem B2410165 : Blo 1268452 2410165 := bbase (se 5 (by rfl) ⟨112976, by rfl⟩ : syracuseStep 2410165 = 225953) (by norm_num)
theorem B1525429 : Blo 1268452 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B4818629 : Blo 1268452 4818629 := bbase (se 4 (by rfl) ⟨451746, by rfl⟩ : syracuseStep 4818629 = 903493) (by norm_num)
theorem B1427161 : Blo 1268452 1427161 := bbase (se 2 (by rfl) ⟨535185, by rfl⟩ : syracuseStep 1427161 = 1070371) (by norm_num)
theorem B2713333 : Blo 1268452 2713333 := bbase (se 5 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 2713333 = 254375) (by norm_num)
theorem B2746109 : Blo 1268452 2746109 := bbase (se 3 (by rfl) ⟨514895, by rfl⟩ : syracuseStep 2746109 = 1029791) (by norm_num)
theorem B1427197 : Blo 1268452 1427197 := bbase (se 3 (by rfl) ⟨267599, by rfl⟩ : syracuseStep 1427197 = 535199) (by norm_num)
theorem B12535573 : Blo 1268452 12535573 := bbase (se 6 (by rfl) ⟨293802, by rfl⟩ : syracuseStep 12535573 = 587605) (by norm_num)
theorem B1427233 : Blo 1268452 1427233 := bbase (se 2 (by rfl) ⟨535212, by rfl⟩ : syracuseStep 1427233 = 1070425) (by norm_num)
theorem B1607465 : Blo 1268452 1607465 := bbase (se 2 (by rfl) ⟨602799, by rfl⟩ : syracuseStep 1607465 = 1205599) (by norm_num)
theorem B1427269 : Blo 1268452 1427269 := bbase (se 4 (by rfl) ⟨133806, by rfl⟩ : syracuseStep 1427269 = 267613) (by norm_num)
theorem B1607521 : Blo 1268452 1607521 := bbase (se 2 (by rfl) ⟨602820, by rfl⟩ : syracuseStep 1607521 = 1205641) (by norm_num)
theorem B1427305 : Blo 1268452 1427305 := bbase (se 2 (by rfl) ⟨535239, by rfl⟩ : syracuseStep 1427305 = 1070479) (by norm_num)
theorem B1525621 : Blo 1268452 1525621 := bbase (se 5 (by rfl) ⟨71513, by rfl⟩ : syracuseStep 1525621 = 143027) (by norm_num)
theorem B1427341 : Blo 1268452 1427341 := bbase (se 3 (by rfl) ⟨267626, by rfl⟩ : syracuseStep 1427341 = 535253) (by norm_num)
theorem B4286357 : Blo 1268452 4286357 := bbase (se 6 (by rfl) ⟨100461, by rfl⟩ : syracuseStep 4286357 = 200923) (by norm_num)
theorem B3213229 : Blo 1268452 3213229 := bbase (se 3 (by rfl) ⟨602480, by rfl⟩ : syracuseStep 3213229 = 1204961) (by norm_num)
theorem B1427377 : Blo 1268452 1427377 := bbase (se 2 (by rfl) ⟨535266, by rfl⟩ : syracuseStep 1427377 = 1070533) (by norm_num)
theorem B3049397 : Blo 1268452 3049397 := bbase (se 5 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 3049397 = 285881) (by norm_num)
theorem B3614645 : Blo 1268452 3614645 := bbase (se 5 (by rfl) ⟨169436, by rfl⟩ : syracuseStep 3614645 = 338873) (by norm_num)
theorem B6866869 : Blo 1268452 6866869 := bbase (se 5 (by rfl) ⟨321884, by rfl⟩ : syracuseStep 6866869 = 643769) (by norm_num)
theorem B1607617 : Blo 1268452 1607617 := bbase (se 2 (by rfl) ⟨602856, by rfl⟩ : syracuseStep 1607617 = 1205713) (by norm_num)
theorem B1427413 : Blo 1268452 1427413 := bbase (se 7 (by rfl) ⟨16727, by rfl⟩ : syracuseStep 1427413 = 33455) (by norm_num)
theorem B1468373 : Blo 1268452 1468373 := bbase (se 7 (by rfl) ⟨17207, by rfl⟩ : syracuseStep 1468373 = 34415) (by norm_num)
theorem B1525721 : Blo 1268452 1525721 := bbase (se 2 (by rfl) ⟨572145, by rfl⟩ : syracuseStep 1525721 = 1144291) (by norm_num)
theorem B2934749 : Blo 1268452 2934749 := bbase (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) (by norm_num)
theorem B2410469 : Blo 1268452 2410469 := bbase (se 4 (by rfl) ⟨225981, by rfl⟩ : syracuseStep 2410469 = 451963) (by norm_num)
theorem B1427449 : Blo 1268452 1427449 := bbase (se 2 (by rfl) ⟨535293, by rfl⟩ : syracuseStep 1427449 = 1070587) (by norm_num)
theorem B1427485 : Blo 1268452 1427485 := bbase (se 3 (by rfl) ⟨267653, by rfl⟩ : syracuseStep 1427485 = 535307) (by norm_num)
theorem B3213341 : Blo 1268452 3213341 := bbase (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) (by norm_num)
theorem B1427521 : Blo 1268452 1427521 := bbase (se 2 (by rfl) ⟨535320, by rfl⟩ : syracuseStep 1427521 = 1070641) (by norm_num)
theorem B4065349 : Blo 1268452 4065349 := bbase (se 4 (by rfl) ⟨381126, by rfl⟩ : syracuseStep 4065349 = 762253) (by norm_num)
theorem B1427557 : Blo 1268452 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B1902701 : Blo 1268452 1902701 := bbase (se 3 (by rfl) ⟨356756, by rfl⟩ : syracuseStep 1902701 = 713513) (by norm_num)
theorem B1607789 : Blo 1268452 1607789 := bbase (se 3 (by rfl) ⟨301460, by rfl⟩ : syracuseStep 1607789 = 602921) (by norm_num)
theorem B3049597 : Blo 1268452 3049597 := bbase (se 3 (by rfl) ⟨571799, by rfl⟩ : syracuseStep 3049597 = 1143599) (by norm_num)
theorem B1902725 : Blo 1268452 1902725 := bbase (se 4 (by rfl) ⟨178380, by rfl⟩ : syracuseStep 1902725 = 356761) (by norm_num)
theorem B1427593 : Blo 1268452 1427593 := bbase (se 2 (by rfl) ⟨535347, by rfl⟩ : syracuseStep 1427593 = 1070695) (by norm_num)
theorem B1902749 : Blo 1268452 1902749 := bbase (se 3 (by rfl) ⟨356765, by rfl⟩ : syracuseStep 1902749 = 713531) (by norm_num)
theorem B1607845 : Blo 1268452 1607845 := bbase (se 4 (by rfl) ⟨150735, by rfl⟩ : syracuseStep 1607845 = 301471) (by norm_num)
theorem B1427629 : Blo 1268452 1427629 := bbase (se 3 (by rfl) ⟨267680, by rfl⟩ : syracuseStep 1427629 = 535361) (by norm_num)
theorem B2574509 : Blo 1268452 2574509 := bbase (se 3 (by rfl) ⟨482720, by rfl⟩ : syracuseStep 2574509 = 965441) (by norm_num)
theorem B1902773 : Blo 1268452 1902773 := bbase (se 5 (by rfl) ⟨89192, by rfl⟩ : syracuseStep 1902773 = 178385) (by norm_num)
theorem B6424757 : Blo 1268452 6424757 := bbase (se 5 (by rfl) ⟨301160, by rfl⟩ : syracuseStep 6424757 = 602321) (by norm_num)
theorem B1902797 : Blo 1268452 1902797 := bbase (se 3 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 1902797 = 713549) (by norm_num)
theorem B1427665 : Blo 1268452 1427665 := bbase (se 2 (by rfl) ⟨535374, by rfl⟩ : syracuseStep 1427665 = 1070749) (by norm_num)
theorem B3213533 : Blo 1268452 3213533 := bbase (se 3 (by rfl) ⟨602537, by rfl⟩ : syracuseStep 3213533 = 1205075) (by norm_num)
theorem B2033885 : Blo 1268452 2033885 := bbase (se 3 (by rfl) ⟨381353, by rfl⟩ : syracuseStep 2033885 = 762707) (by norm_num)
theorem B1902821 : Blo 1268452 1902821 := bbase (se 4 (by rfl) ⟨178389, by rfl⟩ : syracuseStep 1902821 = 356779) (by norm_num)
theorem B1427701 : Blo 1268452 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B1902845 : Blo 1268452 1902845 := bbase (se 3 (by rfl) ⟨356783, by rfl⟩ : syracuseStep 1902845 = 713567) (by norm_num)
theorem B1902869 : Blo 1268452 1902869 := bbase (se 6 (by rfl) ⟨44598, by rfl⟩ : syracuseStep 1902869 = 89197) (by norm_num)
theorem B1427737 : Blo 1268452 1427737 := bbase (se 2 (by rfl) ⟨535401, by rfl⟩ : syracuseStep 1427737 = 1070803) (by norm_num)
theorem B1902893 : Blo 1268452 1902893 := bbase (se 3 (by rfl) ⟨356792, by rfl⟩ : syracuseStep 1902893 = 713585) (by norm_num)
theorem B1427773 : Blo 1268452 1427773 := bbase (se 3 (by rfl) ⟨267707, by rfl⟩ : syracuseStep 1427773 = 535415) (by norm_num)
theorem B1902917 : Blo 1268452 1902917 := bbase (se 4 (by rfl) ⟨178398, by rfl⟩ : syracuseStep 1902917 = 356797) (by norm_num)
theorem B4286789 : Blo 1268452 4286789 := bbase (se 4 (by rfl) ⟨401886, by rfl⟩ : syracuseStep 4286789 = 803773) (by norm_num)
theorem B1902941 : Blo 1268452 1902941 := bbase (se 3 (by rfl) ⟨356801, by rfl⟩ : syracuseStep 1902941 = 713603) (by norm_num)
theorem B2034013 : Blo 1268452 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B1427809 : Blo 1268452 1427809 := bbase (se 2 (by rfl) ⟨535428, by rfl⟩ : syracuseStep 1427809 = 1070857) (by norm_num)
theorem B1902965 : Blo 1268452 1902965 := bbase (se 5 (by rfl) ⟨89201, by rfl⟩ : syracuseStep 1902965 = 178403) (by norm_num)
theorem B1427845 : Blo 1268452 1427845 := bbase (se 4 (by rfl) ⟨133860, by rfl⟩ : syracuseStep 1427845 = 267721) (by norm_num)
theorem B1902989 : Blo 1268452 1902989 := bbase (se 3 (by rfl) ⟨356810, by rfl⟩ : syracuseStep 1902989 = 713621) (by norm_num)
theorem B2140573 : Blo 1268452 2140573 := bbase (se 3 (by rfl) ⟨401357, by rfl⟩ : syracuseStep 2140573 = 802715) (by norm_num)
theorem B2034077 : Blo 1268452 2034077 := bbase (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) (by norm_num)
theorem B1903013 : Blo 1268452 1903013 := bbase (se 4 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 1903013 = 356815) (by norm_num)
theorem B1427881 : Blo 1268452 1427881 := bbase (se 2 (by rfl) ⟨535455, by rfl⟩ : syracuseStep 1427881 = 1070911) (by norm_num)
theorem B1903037 : Blo 1268452 1903037 := bbase (se 3 (by rfl) ⟨356819, by rfl⟩ : syracuseStep 1903037 = 713639) (by norm_num)
theorem B6097349 : Blo 1268452 6097349 := bbase (se 4 (by rfl) ⟨571626, by rfl⟩ : syracuseStep 6097349 = 1143253) (by norm_num)
theorem B1427917 : Blo 1268452 1427917 := bbase (se 3 (by rfl) ⟨267734, by rfl⟩ : syracuseStep 1427917 = 535469) (by norm_num)
theorem B1903061 : Blo 1268452 1903061 := bbase (se 7 (by rfl) ⟨22301, by rfl⟩ : syracuseStep 1903061 = 44603) (by norm_num)
theorem B1903085 : Blo 1268452 1903085 := bbase (se 3 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 1903085 = 713657) (by norm_num)
theorem B1427953 : Blo 1268452 1427953 := bbase (se 2 (by rfl) ⟨535482, by rfl⟩ : syracuseStep 1427953 = 1070965) (by norm_num)
theorem B2140661 : Blo 1268452 2140661 := bbase (se 5 (by rfl) ⟨100343, by rfl⟩ : syracuseStep 2140661 = 200687) (by norm_num)
theorem B1903109 : Blo 1268452 1903109 := bbase (se 4 (by rfl) ⟨178416, by rfl⟩ : syracuseStep 1903109 = 356833) (by norm_num)
theorem B1427989 : Blo 1268452 1427989 := bbase (se 6 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 1427989 = 66937) (by norm_num)
theorem B23169557 : Blo 1268452 23169557 := bbase (se 6 (by rfl) ⟨543036, by rfl⟩ : syracuseStep 23169557 = 1086073) (by norm_num)
theorem B1903133 : Blo 1268452 1903133 := bbase (se 3 (by rfl) ⟨356837, by rfl⟩ : syracuseStep 1903133 = 713675) (by norm_num)
theorem B1903157 : Blo 1268452 1903157 := bbase (se 5 (by rfl) ⟨89210, by rfl⟩ : syracuseStep 1903157 = 178421) (by norm_num)
theorem B3213877 : Blo 1268452 3213877 := bbase (se 5 (by rfl) ⟨150650, by rfl⟩ : syracuseStep 3213877 = 301301) (by norm_num)
theorem B1428025 : Blo 1268452 1428025 := bbase (se 2 (by rfl) ⟨535509, by rfl⟩ : syracuseStep 1428025 = 1071019) (by norm_num)
theorem B1903181 : Blo 1268452 1903181 := bbase (se 3 (by rfl) ⟨356846, by rfl⟩ : syracuseStep 1903181 = 713693) (by norm_num)
theorem B3615317 : Blo 1268452 3615317 := bbase (se 8 (by rfl) ⟨21183, by rfl⟩ : syracuseStep 3615317 = 42367) (by norm_num)
theorem B1428061 : Blo 1268452 1428061 := bbase (se 3 (by rfl) ⟨267761, by rfl⟩ : syracuseStep 1428061 = 535523) (by norm_num)
theorem B1903205 : Blo 1268452 1903205 := bbase (se 4 (by rfl) ⟨178425, by rfl⟩ : syracuseStep 1903205 = 356851) (by norm_num)
theorem B2140789 : Blo 1268452 2140789 := bbase (se 5 (by rfl) ⟨100349, by rfl⟩ : syracuseStep 2140789 = 200699) (by norm_num)
theorem B1903229 : Blo 1268452 1903229 := bbase (se 3 (by rfl) ⟨356855, by rfl⟩ : syracuseStep 1903229 = 713711) (by norm_num)
theorem B1428097 : Blo 1268452 1428097 := bbase (se 2 (by rfl) ⟨535536, by rfl⟩ : syracuseStep 1428097 = 1071073) (by norm_num)
theorem B1903253 : Blo 1268452 1903253 := bbase (se 6 (by rfl) ⟨44607, by rfl⟩ : syracuseStep 1903253 = 89215) (by norm_num)
theorem B1428133 : Blo 1268452 1428133 := bbase (se 4 (by rfl) ⟨133887, by rfl⟩ : syracuseStep 1428133 = 267775) (by norm_num)
theorem B3213989 : Blo 1268452 3213989 := bbase (se 4 (by rfl) ⟨301311, by rfl⟩ : syracuseStep 3213989 = 602623) (by norm_num)
theorem B1903277 : Blo 1268452 1903277 := bbase (se 3 (by rfl) ⟨356864, by rfl⟩ : syracuseStep 1903277 = 713729) (by norm_num)
theorem B1903301 : Blo 1268452 1903301 := bbase (se 4 (by rfl) ⟨178434, by rfl⟩ : syracuseStep 1903301 = 356869) (by norm_num)
theorem B1428169 : Blo 1268452 1428169 := bbase (se 2 (by rfl) ⟨535563, by rfl⟩ : syracuseStep 1428169 = 1071127) (by norm_num)
theorem B2140877 : Blo 1268452 2140877 := bbase (se 3 (by rfl) ⟨401414, by rfl⟩ : syracuseStep 2140877 = 802829) (by norm_num)
theorem B2411221 : Blo 1268452 2411221 := bbase (se 7 (by rfl) ⟨28256, by rfl⟩ : syracuseStep 2411221 = 56513) (by norm_num)
theorem B1903325 : Blo 1268452 1903325 := bbase (se 3 (by rfl) ⟨356873, by rfl⟩ : syracuseStep 1903325 = 713747) (by norm_num)
theorem B1428205 : Blo 1268452 1428205 := bbase (se 3 (by rfl) ⟨267788, by rfl⟩ : syracuseStep 1428205 = 535577) (by norm_num)
theorem B1903349 : Blo 1268452 1903349 := bbase (se 5 (by rfl) ⟨89219, by rfl⟩ : syracuseStep 1903349 = 178439) (by norm_num)
theorem B4287221 : Blo 1268452 4287221 := bbase (se 5 (by rfl) ⟨200963, by rfl⟩ : syracuseStep 4287221 = 401927) (by norm_num)
theorem B1903373 : Blo 1268452 1903373 := bbase (se 3 (by rfl) ⟨356882, by rfl⟩ : syracuseStep 1903373 = 713765) (by norm_num)
theorem B1428241 : Blo 1268452 1428241 := bbase (se 2 (by rfl) ⟨535590, by rfl⟩ : syracuseStep 1428241 = 1071181) (by norm_num)
theorem B1903397 : Blo 1268452 1903397 := bbase (se 4 (by rfl) ⟨178443, by rfl⟩ : syracuseStep 1903397 = 356887) (by norm_num)
theorem B1428277 : Blo 1268452 1428277 := bbase (se 5 (by rfl) ⟨66950, by rfl⟩ : syracuseStep 1428277 = 133901) (by norm_num)
theorem B1903421 : Blo 1268452 1903421 := bbase (se 3 (by rfl) ⟨356891, by rfl⟩ : syracuseStep 1903421 = 713783) (by norm_num)
theorem B6097733 : Blo 1268452 6097733 := bbase (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) (by norm_num)
theorem B2141005 : Blo 1268452 2141005 := bbase (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) (by norm_num)
theorem B1903445 : Blo 1268452 1903445 := bbase (se 9 (by rfl) ⟨5576, by rfl⟩ : syracuseStep 1903445 = 11153) (by norm_num)
theorem B1428313 : Blo 1268452 1428313 := bbase (se 2 (by rfl) ⟨535617, by rfl⟩ : syracuseStep 1428313 = 1071235) (by norm_num)
theorem B3214181 : Blo 1268452 3214181 := bbase (se 4 (by rfl) ⟨301329, by rfl⟩ : syracuseStep 3214181 = 602659) (by norm_num)
theorem B2411365 : Blo 1268452 2411365 := bbase (se 4 (by rfl) ⟨226065, by rfl⟩ : syracuseStep 2411365 = 452131) (by norm_num)
theorem B1903469 : Blo 1268452 1903469 := bbase (se 3 (by rfl) ⟨356900, by rfl⟩ : syracuseStep 1903469 = 713801) (by norm_num)
theorem B1428349 : Blo 1268452 1428349 := bbase (se 3 (by rfl) ⟨267815, by rfl⟩ : syracuseStep 1428349 = 535631) (by norm_num)
theorem B1903493 : Blo 1268452 1903493 := bbase (se 4 (by rfl) ⟨178452, by rfl⟩ : syracuseStep 1903493 = 356905) (by norm_num)
theorem B1903517 : Blo 1268452 1903517 := bbase (se 3 (by rfl) ⟨356909, by rfl⟩ : syracuseStep 1903517 = 713819) (by norm_num)
theorem B1428385 : Blo 1268452 1428385 := bbase (se 2 (by rfl) ⟨535644, by rfl⟩ : syracuseStep 1428385 = 1071289) (by norm_num)
theorem B2141093 : Blo 1268452 2141093 := bbase (se 4 (by rfl) ⟨200727, by rfl⟩ : syracuseStep 2141093 = 401455) (by norm_num)
theorem B3050405 : Blo 1268452 3050405 := bbase (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) (by norm_num)
theorem B1903541 : Blo 1268452 1903541 := bbase (se 5 (by rfl) ⟨89228, by rfl⟩ : syracuseStep 1903541 = 178457) (by norm_num)
theorem B1354693 : Blo 1268452 1354693 := bbase (se 4 (by rfl) ⟨127002, by rfl⟩ : syracuseStep 1354693 = 254005) (by norm_num)
theorem B1428421 : Blo 1268452 1428421 := bbase (se 4 (by rfl) ⟨133914, by rfl⟩ : syracuseStep 1428421 = 267829) (by norm_num)
theorem B1903565 : Blo 1268452 1903565 := bbase (se 3 (by rfl) ⟨356918, by rfl⟩ : syracuseStep 1903565 = 713837) (by norm_num)
theorem B1903589 : Blo 1268452 1903589 := bbase (se 4 (by rfl) ⟨178461, by rfl⟩ : syracuseStep 1903589 = 356923) (by norm_num)
theorem B1428457 : Blo 1268452 1428457 := bbase (se 2 (by rfl) ⟨535671, by rfl⟩ : syracuseStep 1428457 = 1071343) (by norm_num)
theorem B1903613 : Blo 1268452 1903613 := bbase (se 3 (by rfl) ⟨356927, by rfl⟩ : syracuseStep 1903613 = 713855) (by norm_num)
theorem B1354753 : Blo 1268452 1354753 := bbase (se 2 (by rfl) ⟨508032, by rfl⟩ : syracuseStep 1354753 = 1016065) (by norm_num)
theorem B3615749 : Blo 1268452 3615749 := bbase (se 4 (by rfl) ⟨338976, by rfl⟩ : syracuseStep 3615749 = 677953) (by norm_num)
theorem B2411525 : Blo 1268452 2411525 := bbase (se 4 (by rfl) ⟨226080, by rfl⟩ : syracuseStep 2411525 = 452161) (by norm_num)
theorem B1428493 : Blo 1268452 1428493 := bbase (se 3 (by rfl) ⟨267842, by rfl⟩ : syracuseStep 1428493 = 535685) (by norm_num)
theorem B1903637 : Blo 1268452 1903637 := bbase (se 6 (by rfl) ⟨44616, by rfl⟩ : syracuseStep 1903637 = 89233) (by norm_num)
theorem B2141221 : Blo 1268452 2141221 := bbase (se 4 (by rfl) ⟨200739, by rfl⟩ : syracuseStep 2141221 = 401479) (by norm_num)
theorem B1903661 : Blo 1268452 1903661 := bbase (se 3 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 1903661 = 713873) (by norm_num)
theorem B1428529 : Blo 1268452 1428529 := bbase (se 2 (by rfl) ⟨535698, by rfl⟩ : syracuseStep 1428529 = 1071397) (by norm_num)
theorem B1903685 : Blo 1268452 1903685 := bbase (se 4 (by rfl) ⟨178470, by rfl⟩ : syracuseStep 1903685 = 356941) (by norm_num)
theorem B1428565 : Blo 1268452 1428565 := bbase (se 8 (by rfl) ⟨8370, by rfl⟩ : syracuseStep 1428565 = 16741) (by norm_num)
theorem B1903709 : Blo 1268452 1903709 := bbase (se 3 (by rfl) ⟨356945, by rfl⟩ : syracuseStep 1903709 = 713891) (by norm_num)
theorem B2288741 : Blo 1268452 2288741 := bbase (se 4 (by rfl) ⟨214569, by rfl⟩ : syracuseStep 2288741 = 429139) (by norm_num)
theorem B1903733 : Blo 1268452 1903733 := bbase (se 5 (by rfl) ⟨89237, by rfl⟩ : syracuseStep 1903733 = 178475) (by norm_num)
theorem B1428601 : Blo 1268452 1428601 := bbase (se 2 (by rfl) ⟨535725, by rfl⟩ : syracuseStep 1428601 = 1071451) (by norm_num)
theorem B2141309 : Blo 1268452 2141309 := bbase (se 3 (by rfl) ⟨401495, by rfl⟩ : syracuseStep 2141309 = 802991) (by norm_num)
theorem B1903757 : Blo 1268452 1903757 := bbase (se 3 (by rfl) ⟨356954, by rfl⟩ : syracuseStep 1903757 = 713909) (by norm_num)
theorem B2411669 : Blo 1268452 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B1428637 : Blo 1268452 1428637 := bbase (se 3 (by rfl) ⟨267869, by rfl⟩ : syracuseStep 1428637 = 535739) (by norm_num)
theorem B1903781 : Blo 1268452 1903781 := bbase (se 4 (by rfl) ⟨178479, by rfl⟩ : syracuseStep 1903781 = 356959) (by norm_num)
theorem B4287653 : Blo 1268452 4287653 := bbase (se 4 (by rfl) ⟨401967, by rfl⟩ : syracuseStep 4287653 = 803935) (by norm_num)
theorem B2854061 : Blo 1268452 2854061 := bbase (se 3 (by rfl) ⟨535136, by rfl⟩ : syracuseStep 2854061 = 1070273) (by norm_num)
theorem B1903805 : Blo 1268452 1903805 := bbase (se 3 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 1903805 = 713927) (by norm_num)
theorem B3214525 : Blo 1268452 3214525 := bbase (se 3 (by rfl) ⟨602723, by rfl⟩ : syracuseStep 3214525 = 1205447) (by norm_num)
theorem B1428673 : Blo 1268452 1428673 := bbase (se 2 (by rfl) ⟨535752, by rfl⟩ : syracuseStep 1428673 = 1071505) (by norm_num)
theorem B16256213 : Blo 1268452 16256213 := bbase (se 7 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 16256213 = 381005) (by norm_num)
theorem B1903829 : Blo 1268452 1903829 := bbase (se 7 (by rfl) ⟨22310, by rfl⟩ : syracuseStep 1903829 = 44621) (by norm_num)
theorem B9153749 : Blo 1268452 9153749 := bbase (se 7 (by rfl) ⟨107270, by rfl⟩ : syracuseStep 9153749 = 214541) (by norm_num)
theorem B1428709 : Blo 1268452 1428709 := bbase (se 4 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 1428709 = 267883) (by norm_num)
theorem B1903853 : Blo 1268452 1903853 := bbase (se 3 (by rfl) ⟨356972, by rfl⟩ : syracuseStep 1903853 = 713945) (by norm_num)
theorem B2854133 : Blo 1268452 2854133 := bbase (se 5 (by rfl) ⟨133787, by rfl⟩ : syracuseStep 2854133 = 267575) (by norm_num)
theorem B2141437 : Blo 1268452 2141437 := bbase (se 3 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 2141437 = 803039) (by norm_num)
theorem B2288893 : Blo 1268452 2288893 := bbase (se 3 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 2288893 = 858335) (by norm_num)
theorem B1903877 : Blo 1268452 1903877 := bbase (se 4 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 1903877 = 356977) (by norm_num)
theorem B1428745 : Blo 1268452 1428745 := bbase (se 2 (by rfl) ⟨535779, by rfl⟩ : syracuseStep 1428745 = 1071559) (by norm_num)
theorem B1903901 : Blo 1268452 1903901 := bbase (se 3 (by rfl) ⟨356981, by rfl⟩ : syracuseStep 1903901 = 713963) (by norm_num)
theorem B3214637 : Blo 1268452 3214637 := bbase (se 3 (by rfl) ⟨602744, by rfl⟩ : syracuseStep 3214637 = 1205489) (by norm_num)
theorem B1428781 : Blo 1268452 1428781 := bbase (se 3 (by rfl) ⟨267896, by rfl⟩ : syracuseStep 1428781 = 535793) (by norm_num)
theorem B1903925 : Blo 1268452 1903925 := bbase (se 5 (by rfl) ⟨89246, by rfl⟩ : syracuseStep 1903925 = 178493) (by norm_num)
theorem B2854205 : Blo 1268452 2854205 := bbase (se 3 (by rfl) ⟨535163, by rfl⟩ : syracuseStep 2854205 = 1070327) (by norm_num)
theorem B1355069 : Blo 1268452 1355069 := bbase (se 3 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 1355069 = 508151) (by norm_num)
theorem B1903949 : Blo 1268452 1903949 := bbase (se 3 (by rfl) ⟨356990, by rfl⟩ : syracuseStep 1903949 = 713981) (by norm_num)
theorem B1428817 : Blo 1268452 1428817 := bbase (se 2 (by rfl) ⟨535806, by rfl⟩ : syracuseStep 1428817 = 1071613) (by norm_num)
theorem B2141525 : Blo 1268452 2141525 := bbase (se 11 (by rfl) ⟨1568, by rfl⟩ : syracuseStep 2141525 = 3137) (by norm_num)
theorem B1903973 : Blo 1268452 1903973 := bbase (se 4 (by rfl) ⟨178497, by rfl⟩ : syracuseStep 1903973 = 356995) (by norm_num)
theorem B1428853 : Blo 1268452 1428853 := bbase (se 5 (by rfl) ⟨66977, by rfl⟩ : syracuseStep 1428853 = 133955) (by norm_num)
theorem B1903997 : Blo 1268452 1903997 := bbase (se 3 (by rfl) ⟨356999, by rfl⟩ : syracuseStep 1903997 = 713999) (by norm_num)
theorem B2854277 : Blo 1268452 2854277 := bbase (se 4 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 2854277 = 535177) (by norm_num)
theorem B1904021 : Blo 1268452 1904021 := bbase (se 6 (by rfl) ⟨44625, by rfl⟩ : syracuseStep 1904021 = 89251) (by norm_num)
theorem B1428889 : Blo 1268452 1428889 := bbase (se 2 (by rfl) ⟨535833, by rfl⟩ : syracuseStep 1428889 = 1071667) (by norm_num)
theorem B1904045 : Blo 1268452 1904045 := bbase (se 3 (by rfl) ⟨357008, by rfl⟩ : syracuseStep 1904045 = 714017) (by norm_num)
theorem B1428925 : Blo 1268452 1428925 := bbase (se 3 (by rfl) ⟨267923, by rfl⟩ : syracuseStep 1428925 = 535847) (by norm_num)
theorem B6426053 : Blo 1268452 6426053 := bbase (se 4 (by rfl) ⟨602442, by rfl⟩ : syracuseStep 6426053 = 1204885) (by norm_num)
theorem B1904069 : Blo 1268452 1904069 := bbase (se 4 (by rfl) ⟨178506, by rfl⟩ : syracuseStep 1904069 = 357013) (by norm_num)
theorem B2854349 : Blo 1268452 2854349 := bbase (se 3 (by rfl) ⟨535190, by rfl⟩ : syracuseStep 2854349 = 1070381) (by norm_num)
theorem B2141653 : Blo 1268452 2141653 := bbase (se 7 (by rfl) ⟨25097, by rfl⟩ : syracuseStep 2141653 = 50195) (by norm_num)
theorem B1904093 : Blo 1268452 1904093 := bbase (se 3 (by rfl) ⟨357017, by rfl⟩ : syracuseStep 1904093 = 714035) (by norm_num)
theorem B1428961 : Blo 1268452 1428961 := bbase (se 2 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 1428961 = 1071721) (by norm_num)
theorem B3214829 : Blo 1268452 3214829 := bbase (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) (by norm_num)
theorem B1904117 : Blo 1268452 1904117 := bbase (se 5 (by rfl) ⟨89255, by rfl⟩ : syracuseStep 1904117 = 178511) (by norm_num)
theorem B1428997 : Blo 1268452 1428997 := bbase (se 4 (by rfl) ⟨133968, by rfl⟩ : syracuseStep 1428997 = 267937) (by norm_num)
theorem B1904141 : Blo 1268452 1904141 := bbase (se 3 (by rfl) ⟨357026, by rfl⟩ : syracuseStep 1904141 = 714053) (by norm_num)
theorem B2854421 : Blo 1268452 2854421 := bbase (se 6 (by rfl) ⟨66900, by rfl⟩ : syracuseStep 2854421 = 133801) (by norm_num)
theorem B1904165 : Blo 1268452 1904165 := bbase (se 4 (by rfl) ⟨178515, by rfl⟩ : syracuseStep 1904165 = 357031) (by norm_num)
theorem B1429033 : Blo 1268452 1429033 := bbase (se 2 (by rfl) ⟨535887, by rfl⟩ : syracuseStep 1429033 = 1071775) (by norm_num)
theorem B2141741 : Blo 1268452 2141741 := bbase (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) (by norm_num)
theorem B1904189 : Blo 1268452 1904189 := bbase (se 3 (by rfl) ⟨357035, by rfl⟩ : syracuseStep 1904189 = 714071) (by norm_num)
theorem B1429069 : Blo 1268452 1429069 := bbase (se 3 (by rfl) ⟨267950, by rfl⟩ : syracuseStep 1429069 = 535901) (by norm_num)
theorem B1904213 : Blo 1268452 1904213 := bbase (se 8 (by rfl) ⟨11157, by rfl⟩ : syracuseStep 1904213 = 22315) (by norm_num)
theorem B2854493 : Blo 1268452 2854493 := bbase (se 3 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 2854493 = 1070435) (by norm_num)
theorem B3862117 : Blo 1268452 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B1904237 : Blo 1268452 1904237 := bbase (se 3 (by rfl) ⟨357044, by rfl⟩ : syracuseStep 1904237 = 714089) (by norm_num)
theorem B1429105 : Blo 1268452 1429105 := bbase (se 2 (by rfl) ⟨535914, by rfl⟩ : syracuseStep 1429105 = 1071829) (by norm_num)
theorem B4066949 : Blo 1268452 4066949 := bbase (se 4 (by rfl) ⟨381276, by rfl⟩ : syracuseStep 4066949 = 762553) (by norm_num)
theorem B1904261 : Blo 1268452 1904261 := bbase (se 4 (by rfl) ⟨178524, by rfl⟩ : syracuseStep 1904261 = 357049) (by norm_num)
theorem B17370773 : Blo 1268452 17370773 := bbase (se 6 (by rfl) ⟨407127, by rfl⟩ : syracuseStep 17370773 = 814255) (by norm_num)
theorem B1429141 : Blo 1268452 1429141 := bbase (se 6 (by rfl) ⟨33495, by rfl⟩ : syracuseStep 1429141 = 66991) (by norm_num)
theorem B1904285 : Blo 1268452 1904285 := bbase (se 3 (by rfl) ⟨357053, by rfl⟩ : syracuseStep 1904285 = 714107) (by norm_num)
theorem B2854565 : Blo 1268452 2854565 := bbase (se 4 (by rfl) ⟨267615, by rfl⟩ : syracuseStep 2854565 = 535231) (by norm_num)
theorem B3051173 : Blo 1268452 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B2141869 : Blo 1268452 2141869 := bbase (se 3 (by rfl) ⟨401600, by rfl⟩ : syracuseStep 2141869 = 803201) (by norm_num)
theorem B1904309 : Blo 1268452 1904309 := bbase (se 5 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 1904309 = 178529) (by norm_num)
theorem B1429177 : Blo 1268452 1429177 := bbase (se 2 (by rfl) ⟨535941, by rfl⟩ : syracuseStep 1429177 = 1071883) (by norm_num)
theorem B1904333 : Blo 1268452 1904333 := bbase (se 3 (by rfl) ⟨357062, by rfl⟩ : syracuseStep 1904333 = 714125) (by norm_num)
theorem B2059997 : Blo 1268452 2059997 := bbase (se 3 (by rfl) ⟨386249, by rfl⟩ : syracuseStep 2059997 = 772499) (by norm_num)
theorem B1429213 : Blo 1268452 1429213 := bbase (se 3 (by rfl) ⟨267977, by rfl⟩ : syracuseStep 1429213 = 535955) (by norm_num)
theorem B1904357 : Blo 1268452 1904357 := bbase (se 4 (by rfl) ⟨178533, by rfl⟩ : syracuseStep 1904357 = 357067) (by norm_num)
theorem B2854637 : Blo 1268452 2854637 := bbase (se 3 (by rfl) ⟨535244, by rfl⟩ : syracuseStep 2854637 = 1070489) (by norm_num)
theorem B3616501 : Blo 1268452 3616501 := bbase (se 5 (by rfl) ⟨169523, by rfl⟩ : syracuseStep 3616501 = 339047) (by norm_num)
theorem B1355513 : Blo 1268452 1355513 := bbase (se 2 (by rfl) ⟨508317, by rfl⟩ : syracuseStep 1355513 = 1016635) (by norm_num)
theorem B1904381 : Blo 1268452 1904381 := bbase (se 3 (by rfl) ⟨357071, by rfl⟩ : syracuseStep 1904381 = 714143) (by norm_num)
theorem B1429249 : Blo 1268452 1429249 := bbase (se 2 (by rfl) ⟨535968, by rfl⟩ : syracuseStep 1429249 = 1071937) (by norm_num)
theorem B2141957 : Blo 1268452 2141957 := bbase (se 4 (by rfl) ⟨200808, by rfl⟩ : syracuseStep 2141957 = 401617) (by norm_num)
theorem B4820741 : Blo 1268452 4820741 := bbase (se 4 (by rfl) ⟨451944, by rfl⟩ : syracuseStep 4820741 = 903889) (by norm_num)
theorem B1904405 : Blo 1268452 1904405 := bbase (se 6 (by rfl) ⟨44634, by rfl⟩ : syracuseStep 1904405 = 89269) (by norm_num)
theorem B1904429 : Blo 1268452 1904429 := bbase (se 3 (by rfl) ⟨357080, by rfl⟩ : syracuseStep 1904429 = 714161) (by norm_num)
theorem B2854709 : Blo 1268452 2854709 := bbase (se 5 (by rfl) ⟨133814, by rfl⟩ : syracuseStep 2854709 = 267629) (by norm_num)
theorem B1355573 : Blo 1268452 1355573 := bbase (se 5 (by rfl) ⟨63542, by rfl⟩ : syracuseStep 1355573 = 127085) (by norm_num)
theorem B1904453 : Blo 1268452 1904453 := bbase (se 4 (by rfl) ⟨178542, by rfl⟩ : syracuseStep 1904453 = 357085) (by norm_num)
theorem B3215173 : Blo 1268452 3215173 := bbase (se 4 (by rfl) ⟨301422, by rfl⟩ : syracuseStep 3215173 = 602845) (by norm_num)
theorem B1904477 : Blo 1268452 1904477 := bbase (se 3 (by rfl) ⟨357089, by rfl⟩ : syracuseStep 1904477 = 714179) (by norm_num)
theorem B1904501 : Blo 1268452 1904501 := bbase (se 5 (by rfl) ⟨89273, by rfl⟩ : syracuseStep 1904501 = 178547) (by norm_num)
theorem B2854781 : Blo 1268452 2854781 := bbase (se 3 (by rfl) ⟨535271, by rfl⟩ : syracuseStep 2854781 = 1070543) (by norm_num)
theorem B2142085 : Blo 1268452 2142085 := bbase (se 4 (by rfl) ⟨200820, by rfl⟩ : syracuseStep 2142085 = 401641) (by norm_num)
theorem B1904525 : Blo 1268452 1904525 := bbase (se 3 (by rfl) ⟨357098, by rfl⟩ : syracuseStep 1904525 = 714197) (by norm_num)
theorem B1806229 : Blo 1268452 1806229 := bbase (se 6 (by rfl) ⟨42333, by rfl⟩ : syracuseStep 1806229 = 84667) (by norm_num)
theorem B1904549 : Blo 1268452 1904549 := bbase (se 4 (by rfl) ⟨178551, by rfl⟩ : syracuseStep 1904549 = 357103) (by norm_num)
theorem B1355701 : Blo 1268452 1355701 := bbase (se 5 (by rfl) ⟨63548, by rfl⟩ : syracuseStep 1355701 = 127097) (by norm_num)
theorem B3215285 : Blo 1268452 3215285 := bbase (se 5 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 3215285 = 301433) (by norm_num)
theorem B1904573 : Blo 1268452 1904573 := bbase (se 3 (by rfl) ⟨357107, by rfl⟩ : syracuseStep 1904573 = 714215) (by norm_num)
theorem B2854853 : Blo 1268452 2854853 := bbase (se 4 (by rfl) ⟨267642, by rfl⟩ : syracuseStep 2854853 = 535285) (by norm_num)
theorem B1904597 : Blo 1268452 1904597 := bbase (se 7 (by rfl) ⟨22319, by rfl⟩ : syracuseStep 1904597 = 44639) (by norm_num)
theorem B2142173 : Blo 1268452 2142173 := bbase (se 3 (by rfl) ⟨401657, by rfl⟩ : syracuseStep 2142173 = 803315) (by norm_num)
theorem B1904621 : Blo 1268452 1904621 := bbase (se 3 (by rfl) ⟨357116, by rfl⟩ : syracuseStep 1904621 = 714233) (by norm_num)
theorem B11579381 : Blo 1268452 11579381 := bbase (se 5 (by rfl) ⟨542783, by rfl⟩ : syracuseStep 11579381 = 1085567) (by norm_num)
theorem B1904645 : Blo 1268452 1904645 := bbase (se 4 (by rfl) ⟨178560, by rfl⟩ : syracuseStep 1904645 = 357121) (by norm_num)
theorem B2854925 : Blo 1268452 2854925 := bbase (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) (by norm_num)
theorem B1904669 : Blo 1268452 1904669 := bbase (se 3 (by rfl) ⟨357125, by rfl⟩ : syracuseStep 1904669 = 714251) (by norm_num)
theorem B4821029 : Blo 1268452 4821029 := bbase (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) (by norm_num)
theorem B1904693 : Blo 1268452 1904693 := bbase (se 5 (by rfl) ⟨89282, by rfl⟩ : syracuseStep 1904693 = 178565) (by norm_num)
theorem B1904717 : Blo 1268452 1904717 := bbase (se 3 (by rfl) ⟨357134, by rfl⟩ : syracuseStep 1904717 = 714269) (by norm_num)
theorem B2854997 : Blo 1268452 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B2142301 : Blo 1268452 2142301 := bbase (se 3 (by rfl) ⟨401681, by rfl⟩ : syracuseStep 2142301 = 803363) (by norm_num)
theorem B1904741 : Blo 1268452 1904741 := bbase (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) (by norm_num)
theorem B3215477 : Blo 1268452 3215477 := bbase (se 5 (by rfl) ⟨150725, by rfl⟩ : syracuseStep 3215477 = 301451) (by norm_num)
theorem B1904765 : Blo 1268452 1904765 := bbase (se 3 (by rfl) ⟨357143, by rfl⟩ : syracuseStep 1904765 = 714287) (by norm_num)
theorem B4575365 : Blo 1268452 4575365 := bbase (se 4 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 4575365 = 857881) (by norm_num)
theorem B2896013 : Blo 1268452 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B15429781 : Blo 1268452 15429781 := bbase (se 6 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 15429781 = 723271) (by norm_num)
theorem B1904789 : Blo 1268452 1904789 := bbase (se 6 (by rfl) ⟨44643, by rfl⟩ : syracuseStep 1904789 = 89287) (by norm_num)
theorem B2855069 : Blo 1268452 2855069 := bbase (se 3 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 2855069 = 1070651) (by norm_num)
theorem B1904813 : Blo 1268452 1904813 := bbase (se 3 (by rfl) ⟨357152, by rfl⟩ : syracuseStep 1904813 = 714305) (by norm_num)
theorem B2142389 : Blo 1268452 2142389 := bbase (se 5 (by rfl) ⟨100424, by rfl⟩ : syracuseStep 2142389 = 200849) (by norm_num)
theorem B1904837 : Blo 1268452 1904837 := bbase (se 4 (by rfl) ⟨178578, by rfl⟩ : syracuseStep 1904837 = 357157) (by norm_num)
theorem B1904861 : Blo 1268452 1904861 := bbase (se 3 (by rfl) ⟨357161, by rfl⟩ : syracuseStep 1904861 = 714323) (by norm_num)
theorem B1806565 : Blo 1268452 1806565 := bbase (se 4 (by rfl) ⟨169365, by rfl⟩ : syracuseStep 1806565 = 338731) (by norm_num)
theorem B2855141 : Blo 1268452 2855141 := bbase (se 4 (by rfl) ⟨267669, by rfl⟩ : syracuseStep 2855141 = 535339) (by norm_num)
theorem B1904885 : Blo 1268452 1904885 := bbase (se 5 (by rfl) ⟨89291, by rfl⟩ : syracuseStep 1904885 = 178583) (by norm_num)
theorem B1904909 : Blo 1268452 1904909 := bbase (se 3 (by rfl) ⟨357170, by rfl⟩ : syracuseStep 1904909 = 714341) (by norm_num)
theorem B1904933 : Blo 1268452 1904933 := bbase (se 4 (by rfl) ⟨178587, by rfl⟩ : syracuseStep 1904933 = 357175) (by norm_num)
theorem B2855213 : Blo 1268452 2855213 := bbase (se 3 (by rfl) ⟨535352, by rfl⟩ : syracuseStep 2855213 = 1070705) (by norm_num)
theorem B2142517 : Blo 1268452 2142517 := bbase (se 5 (by rfl) ⟨100430, by rfl⟩ : syracuseStep 2142517 = 200861) (by norm_num)
theorem B4641077 : Blo 1268452 4641077 := bbase (se 5 (by rfl) ⟨217550, by rfl⟩ : syracuseStep 4641077 = 435101) (by norm_num)
theorem B1904957 : Blo 1268452 1904957 := bbase (se 3 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 1904957 = 714359) (by norm_num)
theorem B8130901 : Blo 1268452 8130901 := bbase (se 10 (by rfl) ⟨11910, by rfl⟩ : syracuseStep 8130901 = 23821) (by norm_num)
theorem B1929557 : Blo 1268452 1929557 := bbase (se 10 (by rfl) ⟨2826, by rfl⟩ : syracuseStep 1929557 = 5653) (by norm_num)
theorem B1904981 : Blo 1268452 1904981 := bbase (se 10 (by rfl) ⟨2790, by rfl⟩ : syracuseStep 1904981 = 5581) (by norm_num)
theorem B1905005 : Blo 1268452 1905005 := bbase (se 3 (by rfl) ⟨357188, by rfl⟩ : syracuseStep 1905005 = 714377) (by norm_num)
theorem B1356145 : Blo 1268452 1356145 := bbase (se 2 (by rfl) ⟨508554, by rfl⟩ : syracuseStep 1356145 = 1017109) (by norm_num)
theorem B2855285 : Blo 1268452 2855285 := bbase (se 5 (by rfl) ⟨133841, by rfl⟩ : syracuseStep 2855285 = 267683) (by norm_num)
theorem B1905029 : Blo 1268452 1905029 := bbase (se 4 (by rfl) ⟨178596, by rfl⟩ : syracuseStep 1905029 = 357193) (by norm_num)
theorem B2142605 : Blo 1268452 2142605 := bbase (se 3 (by rfl) ⟨401738, by rfl⟩ : syracuseStep 2142605 = 803477) (by norm_num)
theorem B1905053 : Blo 1268452 1905053 := bbase (se 3 (by rfl) ⟨357197, by rfl⟩ : syracuseStep 1905053 = 714395) (by norm_num)
theorem B1905077 : Blo 1268452 1905077 := bbase (se 5 (by rfl) ⟨89300, by rfl⟩ : syracuseStep 1905077 = 178601) (by norm_num)
theorem B1806781 : Blo 1268452 1806781 := bbase (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) (by norm_num)
theorem B2855357 : Blo 1268452 2855357 := bbase (se 3 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 2855357 = 1070759) (by norm_num)
theorem B1905101 : Blo 1268452 1905101 := bbase (se 3 (by rfl) ⟨357206, by rfl⟩ : syracuseStep 1905101 = 714413) (by norm_num)
theorem B3215821 : Blo 1268452 3215821 := bbase (se 3 (by rfl) ⟨602966, by rfl⟩ : syracuseStep 3215821 = 1205933) (by norm_num)
theorem B1905125 : Blo 1268452 1905125 := bbase (se 4 (by rfl) ⟨178605, by rfl⟩ : syracuseStep 1905125 = 357211) (by norm_num)
theorem B1356265 : Blo 1268452 1356265 := bbase (se 2 (by rfl) ⟨508599, by rfl⟩ : syracuseStep 1356265 = 1017199) (by norm_num)
theorem B1905149 : Blo 1268452 1905149 := bbase (se 3 (by rfl) ⟨357215, by rfl⟩ : syracuseStep 1905149 = 714431) (by norm_num)
theorem B2855429 : Blo 1268452 2855429 := bbase (se 4 (by rfl) ⟨267696, by rfl⟩ : syracuseStep 2855429 = 535393) (by norm_num)
theorem B2142733 : Blo 1268452 2142733 := bbase (se 3 (by rfl) ⟨401762, by rfl⟩ : syracuseStep 2142733 = 803525) (by norm_num)
theorem B1905173 : Blo 1268452 1905173 := bbase (se 6 (by rfl) ⟨44652, by rfl⟩ : syracuseStep 1905173 = 89305) (by norm_num)
theorem B9646613 : Blo 1268452 9646613 := bbase (se 6 (by rfl) ⟨226092, by rfl⟩ : syracuseStep 9646613 = 452185) (by norm_num)
theorem B1905197 : Blo 1268452 1905197 := bbase (se 3 (by rfl) ⟨357224, by rfl⟩ : syracuseStep 1905197 = 714449) (by norm_num)
theorem B1905221 : Blo 1268452 1905221 := bbase (se 4 (by rfl) ⟨178614, by rfl⟩ : syracuseStep 1905221 = 357229) (by norm_num)
theorem B2855501 : Blo 1268452 2855501 := bbase (se 3 (by rfl) ⟨535406, by rfl⟩ : syracuseStep 2855501 = 1070813) (by norm_num)
theorem B1905245 : Blo 1268452 1905245 := bbase (se 3 (by rfl) ⟨357233, by rfl⟩ : syracuseStep 1905245 = 714467) (by norm_num)
theorem B2142821 : Blo 1268452 2142821 := bbase (se 4 (by rfl) ⟨200889, by rfl⟩ : syracuseStep 2142821 = 401779) (by norm_num)
theorem B6509173 : Blo 1268452 6509173 := bbase (se 5 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 6509173 = 610235) (by norm_num)
theorem B1905269 : Blo 1268452 1905269 := bbase (se 5 (by rfl) ⟨89309, by rfl⟩ : syracuseStep 1905269 = 178619) (by norm_num)
theorem B1905293 : Blo 1268452 1905293 := bbase (se 3 (by rfl) ⟨357242, by rfl⟩ : syracuseStep 1905293 = 714485) (by norm_num)
theorem B2855573 : Blo 1268452 2855573 := bbase (se 6 (by rfl) ⟨66927, by rfl⟩ : syracuseStep 2855573 = 133855) (by norm_num)
theorem B1905317 : Blo 1268452 1905317 := bbase (se 4 (by rfl) ⟨178623, by rfl⟩ : syracuseStep 1905317 = 357247) (by norm_num)
theorem B1905341 : Blo 1268452 1905341 := bbase (se 3 (by rfl) ⟨357251, by rfl⟩ : syracuseStep 1905341 = 714503) (by norm_num)
theorem B6427349 : Blo 1268452 6427349 := bbase (se 7 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 6427349 = 150641) (by norm_num)
theorem B4068053 : Blo 1268452 4068053 := bbase (se 7 (by rfl) ⟨47672, by rfl⟩ : syracuseStep 4068053 = 95345) (by norm_num)
theorem B1905365 : Blo 1268452 1905365 := bbase (se 7 (by rfl) ⟨22328, by rfl⟩ : syracuseStep 1905365 = 44657) (by norm_num)
theorem B2855645 : Blo 1268452 2855645 := bbase (se 3 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 2855645 = 1070867) (by norm_num)
theorem B2142949 : Blo 1268452 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B1356517 : Blo 1268452 1356517 := bbase (se 4 (by rfl) ⟨127173, by rfl⟩ : syracuseStep 1356517 = 254347) (by norm_num)
theorem B1356521 : Blo 1268452 1356521 := bbase (se 2 (by rfl) ⟨508695, by rfl⟩ : syracuseStep 1356521 = 1017391) (by norm_num)
theorem B1905389 : Blo 1268452 1905389 := bbase (se 3 (by rfl) ⟨357260, by rfl⟩ : syracuseStep 1905389 = 714521) (by norm_num)
theorem B3863285 : Blo 1268452 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B5419781 : Blo 1268452 5419781 := bbase (se 4 (by rfl) ⟨508104, by rfl⟩ : syracuseStep 5419781 = 1016209) (by norm_num)
theorem B1905413 : Blo 1268452 1905413 := bbase (se 4 (by rfl) ⟨178632, by rfl⟩ : syracuseStep 1905413 = 357265) (by norm_num)
theorem B2896669 : Blo 1268452 2896669 := bbase (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) (by norm_num)
theorem B1905437 : Blo 1268452 1905437 := bbase (se 3 (by rfl) ⟨357269, by rfl⟩ : syracuseStep 1905437 = 714539) (by norm_num)
theorem B2855717 : Blo 1268452 2855717 := bbase (se 4 (by rfl) ⟨267723, by rfl⟩ : syracuseStep 2855717 = 535447) (by norm_num)
theorem B1807157 : Blo 1268452 1807157 := bbase (se 5 (by rfl) ⟨84710, by rfl⟩ : syracuseStep 1807157 = 169421) (by norm_num)
theorem B1905461 : Blo 1268452 1905461 := bbase (se 5 (by rfl) ⟨89318, by rfl⟩ : syracuseStep 1905461 = 178637) (by norm_num)
theorem B2143037 : Blo 1268452 2143037 := bbase (se 3 (by rfl) ⟨401819, by rfl⟩ : syracuseStep 2143037 = 803639) (by norm_num)
theorem B1905485 : Blo 1268452 1905485 := bbase (se 3 (by rfl) ⟨357278, by rfl⟩ : syracuseStep 1905485 = 714557) (by norm_num)
theorem B4281173 : Blo 1268452 4281173 := bbase (se 9 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 4281173 = 25085) (by norm_num)
theorem B1905509 : Blo 1268452 1905509 := bbase (se 4 (by rfl) ⟨178641, by rfl⟩ : syracuseStep 1905509 = 357283) (by norm_num)
theorem B2855789 : Blo 1268452 2855789 := bbase (se 3 (by rfl) ⟨535460, by rfl⟩ : syracuseStep 2855789 = 1070921) (by norm_num)
theorem B1905533 : Blo 1268452 1905533 := bbase (se 3 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 1905533 = 714575) (by norm_num)
theorem B1905557 : Blo 1268452 1905557 := bbase (se 6 (by rfl) ⟨44661, by rfl⟩ : syracuseStep 1905557 = 89323) (by norm_num)
theorem B1905581 : Blo 1268452 1905581 := bbase (se 3 (by rfl) ⟨357296, by rfl⟩ : syracuseStep 1905581 = 714593) (by norm_num)
theorem B5788597 : Blo 1268452 5788597 := bbase (se 5 (by rfl) ⟨271340, by rfl⟩ : syracuseStep 5788597 = 542681) (by norm_num)
theorem B2855861 : Blo 1268452 2855861 := bbase (se 5 (by rfl) ⟨133868, by rfl⟩ : syracuseStep 2855861 = 267737) (by norm_num)
theorem B9638837 : Blo 1268452 9638837 := bbase (se 5 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 9638837 = 903641) (by norm_num)
theorem B2143165 : Blo 1268452 2143165 := bbase (se 3 (by rfl) ⟨401843, by rfl⟩ : syracuseStep 2143165 = 803687) (by norm_num)
theorem B1905605 : Blo 1268452 1905605 := bbase (se 4 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 1905605 = 357301) (by norm_num)
theorem B1905629 : Blo 1268452 1905629 := bbase (se 3 (by rfl) ⟨357305, by rfl⟩ : syracuseStep 1905629 = 714611) (by norm_num)
theorem B1905653 : Blo 1268452 1905653 := bbase (se 5 (by rfl) ⟨89327, by rfl⟩ : syracuseStep 1905653 = 178655) (by norm_num)
theorem B2855933 : Blo 1268452 2855933 := bbase (se 3 (by rfl) ⟨535487, by rfl⟩ : syracuseStep 2855933 = 1070975) (by norm_num)
theorem B1905677 : Blo 1268452 1905677 := bbase (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) (by norm_num)
theorem B2143253 : Blo 1268452 2143253 := bbase (se 6 (by rfl) ⟨50232, by rfl⟩ : syracuseStep 2143253 = 100465) (by norm_num)
theorem B2856005 : Blo 1268452 2856005 := bbase (se 4 (by rfl) ⟨267750, by rfl⟩ : syracuseStep 2856005 = 535501) (by norm_num)
theorem B6861941 : Blo 1268452 6861941 := bbase (se 5 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 6861941 = 643307) (by norm_num)
theorem B2856077 : Blo 1268452 2856077 := bbase (se 3 (by rfl) ⟨535514, by rfl⟩ : syracuseStep 2856077 = 1071029) (by norm_num)
theorem B2143381 : Blo 1268452 2143381 := bbase (se 6 (by rfl) ⟨50235, by rfl⟩ : syracuseStep 2143381 = 100471) (by norm_num)
theorem B4822213 : Blo 1268452 4822213 := bbase (se 4 (by rfl) ⟨452082, by rfl⟩ : syracuseStep 4822213 = 904165) (by norm_num)
theorem B2856149 : Blo 1268452 2856149 := bbase (se 7 (by rfl) ⟨33470, by rfl⟩ : syracuseStep 2856149 = 66941) (by norm_num)
theorem B2143469 : Blo 1268452 2143469 := bbase (se 3 (by rfl) ⟨401900, by rfl⟩ : syracuseStep 2143469 = 803801) (by norm_num)
theorem B4281605 : Blo 1268452 4281605 := bbase (se 4 (by rfl) ⟨401400, by rfl⟩ : syracuseStep 4281605 = 802801) (by norm_num)
theorem B3257605 : Blo 1268452 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B2856221 : Blo 1268452 2856221 := bbase (se 3 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 2856221 = 1071083) (by norm_num)
theorem B1447213 : Blo 1268452 1447213 := bbase (se 3 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 1447213 = 542705) (by norm_num)
theorem B12195157 : Blo 1268452 12195157 := bbase (se 14 (by rfl) ⟨1116, by rfl⟩ : syracuseStep 12195157 = 2233) (by norm_num)
theorem B1627489 : Blo 1268452 1627489 := bbase (se 2 (by rfl) ⟨610308, by rfl⟩ : syracuseStep 1627489 = 1220617) (by norm_num)
theorem B2856293 : Blo 1268452 2856293 := bbase (se 4 (by rfl) ⟨267777, by rfl⟩ : syracuseStep 2856293 = 535555) (by norm_num)
theorem B2143597 : Blo 1268452 2143597 := bbase (se 3 (by rfl) ⟨401924, by rfl⟩ : syracuseStep 2143597 = 803849) (by norm_num)
theorem B2856365 : Blo 1268452 2856365 := bbase (se 3 (by rfl) ⟨535568, by rfl⟩ : syracuseStep 2856365 = 1071137) (by norm_num)
theorem B2143685 : Blo 1268452 2143685 := bbase (se 4 (by rfl) ⟨200970, by rfl⟩ : syracuseStep 2143685 = 401941) (by norm_num)
theorem B2856437 : Blo 1268452 2856437 := bbase (se 5 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 2856437 = 267791) (by norm_num)
theorem B4822517 : Blo 1268452 4822517 := bbase (se 5 (by rfl) ⟨226055, by rfl⟩ : syracuseStep 4822517 = 452111) (by norm_num)
theorem B2856509 : Blo 1268452 2856509 := bbase (se 3 (by rfl) ⟨535595, by rfl⟩ : syracuseStep 2856509 = 1071191) (by norm_num)
theorem B2143813 : Blo 1268452 2143813 := bbase (se 4 (by rfl) ⟨200982, by rfl⟩ : syracuseStep 2143813 = 401965) (by norm_num)
theorem B2856581 : Blo 1268452 2856581 := bbase (se 4 (by rfl) ⟨267804, by rfl⟩ : syracuseStep 2856581 = 535609) (by norm_num)
theorem B4282037 : Blo 1268452 4282037 := bbase (se 5 (by rfl) ⟨200720, by rfl⟩ : syracuseStep 4282037 = 401441) (by norm_num)
theorem B7722677 : Blo 1268452 7722677 := bbase (se 5 (by rfl) ⟨362000, by rfl⟩ : syracuseStep 7722677 = 724001) (by norm_num)
theorem B2856653 : Blo 1268452 2856653 := bbase (se 3 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 2856653 = 1071245) (by norm_num)
theorem B21968597 : Blo 1268452 21968597 := bbase (se 7 (by rfl) ⟨257444, by rfl⟩ : syracuseStep 21968597 = 514889) (by norm_num)
theorem B1373917 : Blo 1268452 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B5420789 : Blo 1268452 5420789 := bbase (se 5 (by rfl) ⟨254099, by rfl⟩ : syracuseStep 5420789 = 508199) (by norm_num)
theorem B2856725 : Blo 1268452 2856725 := bbase (se 6 (by rfl) ⟨66954, by rfl⟩ : syracuseStep 2856725 = 133909) (by norm_num)
theorem B2709301 : Blo 1268452 2709301 := bbase (se 5 (by rfl) ⟨126998, by rfl⟩ : syracuseStep 2709301 = 253997) (by norm_num)
theorem B22288213 : Blo 1268452 22288213 := bbase (se 9 (by rfl) ⟨65297, by rfl⟩ : syracuseStep 22288213 = 130595) (by norm_num)
theorem B2856797 : Blo 1268452 2856797 := bbase (se 3 (by rfl) ⟨535649, by rfl⟩ : syracuseStep 2856797 = 1071299) (by norm_num)
theorem B2856869 : Blo 1268452 2856869 := bbase (se 4 (by rfl) ⟨267831, by rfl⟩ : syracuseStep 2856869 = 535663) (by norm_num)
theorem B1447861 : Blo 1268452 1447861 := bbase (se 5 (by rfl) ⟨67868, by rfl⟩ : syracuseStep 1447861 = 135737) (by norm_num)
theorem B6428645 : Blo 1268452 6428645 := bbase (se 4 (by rfl) ⟨602685, by rfl⟩ : syracuseStep 6428645 = 1205371) (by norm_num)
theorem B2856941 : Blo 1268452 2856941 := bbase (se 3 (by rfl) ⟨535676, by rfl⟩ : syracuseStep 2856941 = 1071353) (by norm_num)
theorem B8681525 : Blo 1268452 8681525 := bbase (se 5 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 8681525 = 813893) (by norm_num)
theorem B2857013 : Blo 1268452 2857013 := bbase (se 5 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 2857013 = 267845) (by norm_num)
theorem B5150789 : Blo 1268452 5150789 := bbase (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) (by norm_num)
theorem B1931357 : Blo 1268452 1931357 := bbase (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) (by norm_num)
theorem B4282469 : Blo 1268452 4282469 := bbase (se 4 (by rfl) ⟨401481, by rfl⟩ : syracuseStep 4282469 = 802963) (by norm_num)
theorem B3479669 : Blo 1268452 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B1931381 : Blo 1268452 1931381 := bbase (se 5 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 1931381 = 181067) (by norm_num)
theorem B2857085 : Blo 1268452 2857085 := bbase (se 3 (by rfl) ⟨535703, by rfl⟩ : syracuseStep 2857085 = 1071407) (by norm_num)
theorem B1628309 : Blo 1268452 1628309 := bbase (se 6 (by rfl) ⟨38163, by rfl⟩ : syracuseStep 1628309 = 76327) (by norm_num)
theorem B2857157 : Blo 1268452 2857157 := bbase (se 4 (by rfl) ⟨267858, by rfl⟩ : syracuseStep 2857157 = 535717) (by norm_num)
theorem B1808581 : Blo 1268452 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B2857229 : Blo 1268452 2857229 := bbase (se 3 (by rfl) ⟨535730, by rfl⟩ : syracuseStep 2857229 = 1071461) (by norm_num)
theorem B1833293 : Blo 1268452 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B2857301 : Blo 1268452 2857301 := bbase (se 10 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 2857301 = 8371) (by norm_num)
theorem B2857373 : Blo 1268452 2857373 := bbase (se 3 (by rfl) ⟨535757, by rfl⟩ : syracuseStep 2857373 = 1071515) (by norm_num)
theorem B1448381 : Blo 1268452 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B2857445 : Blo 1268452 2857445 := bbase (se 4 (by rfl) ⟨267885, by rfl⟩ : syracuseStep 2857445 = 535771) (by norm_num)
theorem B4282901 : Blo 1268452 4282901 := bbase (se 6 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 4282901 = 200761) (by norm_num)
theorem B2857517 : Blo 1268452 2857517 := bbase (se 3 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 2857517 = 1071569) (by norm_num)
theorem B4069973 : Blo 1268452 4069973 := bbase (se 8 (by rfl) ⟨23847, by rfl⟩ : syracuseStep 4069973 = 47695) (by norm_num)
theorem B2857589 : Blo 1268452 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B2710189 : Blo 1268452 2710189 := bbase (se 3 (by rfl) ⟨508160, by rfl⟩ : syracuseStep 2710189 = 1016321) (by norm_num)
theorem B2857661 : Blo 1268452 2857661 := bbase (se 3 (by rfl) ⟨535811, by rfl⟩ : syracuseStep 2857661 = 1071623) (by norm_num)
theorem B2857733 : Blo 1268452 2857733 := bbase (se 4 (by rfl) ⟨267912, by rfl⟩ : syracuseStep 2857733 = 535825) (by norm_num)
theorem B2857805 : Blo 1268452 2857805 := bbase (se 3 (by rfl) ⟨535838, by rfl⟩ : syracuseStep 2857805 = 1071677) (by norm_num)
theorem B21699413 : Blo 1268452 21699413 := bbase (se 9 (by rfl) ⟨63572, by rfl⟩ : syracuseStep 21699413 = 127145) (by norm_num)
theorem B2857877 : Blo 1268452 2857877 := bbase (se 6 (by rfl) ⟨66981, by rfl⟩ : syracuseStep 2857877 = 133963) (by norm_num)
theorem B4283333 : Blo 1268452 4283333 := bbase (se 4 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 4283333 = 803125) (by norm_num)
theorem B18799573 : Blo 1268452 18799573 := bbase (se 7 (by rfl) ⟨220307, by rfl⟩ : syracuseStep 18799573 = 440615) (by norm_num)
theorem B2169821 : Blo 1268452 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B2857949 : Blo 1268452 2857949 := bbase (se 3 (by rfl) ⟨535865, by rfl⟩ : syracuseStep 2857949 = 1071731) (by norm_num)
theorem B5790709 : Blo 1268452 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B2858021 : Blo 1268452 2858021 := bbase (se 4 (by rfl) ⟨267939, by rfl⟩ : syracuseStep 2858021 = 535879) (by norm_num)
theorem B2858093 : Blo 1268452 2858093 := bbase (se 3 (by rfl) ⟨535892, by rfl⟩ : syracuseStep 2858093 = 1071785) (by norm_num)
theorem B2710685 : Blo 1268452 2710685 := bbase (se 3 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 2710685 = 1016507) (by norm_num)
theorem B2858165 : Blo 1268452 2858165 := bbase (se 5 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 2858165 = 267953) (by norm_num)
theorem B6429941 : Blo 1268452 6429941 := bbase (se 5 (by rfl) ⟨301403, by rfl⟩ : syracuseStep 6429941 = 602807) (by norm_num)
theorem B2858237 : Blo 1268452 2858237 := bbase (se 3 (by rfl) ⟨535919, by rfl⟩ : syracuseStep 2858237 = 1071839) (by norm_num)
theorem B2858309 : Blo 1268452 2858309 := bbase (se 4 (by rfl) ⟨267966, by rfl⟩ : syracuseStep 2858309 = 535933) (by norm_num)
theorem B7716181 : Blo 1268452 7716181 := bbase (se 11 (by rfl) ⟨5651, by rfl⟩ : syracuseStep 7716181 = 11303) (by norm_num)
theorem B5143925 : Blo 1268452 5143925 := bbase (se 5 (by rfl) ⟨241121, by rfl⟩ : syracuseStep 5143925 = 482243) (by norm_num)
theorem B4283765 : Blo 1268452 4283765 := bbase (se 5 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 4283765 = 401603) (by norm_num)
theorem B3431813 : Blo 1268452 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B2170253 : Blo 1268452 2170253 := bbase (se 3 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 2170253 = 813845) (by norm_num)
theorem B2858381 : Blo 1268452 2858381 := bbase (se 3 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 2858381 = 1071893) (by norm_num)
theorem B2858453 : Blo 1268452 2858453 := bbase (se 7 (by rfl) ⟨33497, by rfl⟩ : syracuseStep 2858453 = 66995) (by norm_num)
theorem B5422565 : Blo 1268452 5422565 := bbase (se 4 (by rfl) ⟨508365, by rfl⟩ : syracuseStep 5422565 = 1016731) (by norm_num)
theorem B6422165 : Blo 1268452 6422165 := bbase (se 6 (by rfl) ⟨150519, by rfl⟩ : syracuseStep 6422165 = 301039) (by norm_num)
theorem B3210941 : Blo 1268452 3210941 := bbase (se 3 (by rfl) ⟨602051, by rfl⟩ : syracuseStep 3210941 = 1204103) (by norm_num)
theorem B2408221 : Blo 1268452 2408221 := bbase (se 3 (by rfl) ⟨451541, by rfl⟩ : syracuseStep 2408221 = 903083) (by norm_num)
theorem B4284197 : Blo 1268452 4284197 := bbase (se 4 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 4284197 = 803287) (by norm_num)
theorem B1605521 : Blo 1268452 1605521 := bbase (se 2 (by rfl) ⟨602070, by rfl⟩ : syracuseStep 1605521 = 1204141) (by norm_num)
theorem B1605577 : Blo 1268452 1605577 := bbase (se 2 (by rfl) ⟨602091, by rfl⟩ : syracuseStep 1605577 = 1204183) (by norm_num)
theorem B4816853 : Blo 1268452 4816853 := bbase (se 7 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 4816853 = 112895) (by norm_num)
theorem B7225301 : Blo 1268452 7225301 := bbase (se 7 (by rfl) ⟨84671, by rfl⟩ : syracuseStep 7225301 = 169343) (by norm_num)
theorem B1933301 : Blo 1268452 1933301 := bbase (se 5 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 1933301 = 181247) (by norm_num)
theorem B1269763 : Blo 1268452 1269763 := bstep (se 1 (by rfl) ⟨952322, by rfl⟩ : syracuseStep 1269763 = 1904645) B1904645
theorem B1269779 : Blo 1268452 1269779 := bstep (se 1 (by rfl) ⟨952334, by rfl⟩ : syracuseStep 1269779 = 1904669) B1904669
theorem B1269795 : Blo 1268452 1269795 := bstep (se 1 (by rfl) ⟨952346, by rfl⟩ : syracuseStep 1269795 = 1904693) B1904693
theorem B1605683 : Blo 1268452 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B1269811 : Blo 1268452 1269811 := bstep (se 1 (by rfl) ⟨952358, by rfl⟩ : syracuseStep 1269811 = 1904717) B1904717
theorem B1269827 : Blo 1268452 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B1269843 : Blo 1268452 1269843 := bstep (se 1 (by rfl) ⟨952382, by rfl⟩ : syracuseStep 1269843 = 1904765) B1904765
theorem B1269859 : Blo 1268452 1269859 := bstep (se 1 (by rfl) ⟨952394, by rfl⟩ : syracuseStep 1269859 = 1904789) B1904789
theorem B1269875 : Blo 1268452 1269875 := bstep (se 1 (by rfl) ⟨952406, by rfl⟩ : syracuseStep 1269875 = 1904813) B1904813
theorem B1269891 : Blo 1268452 1269891 := bstep (se 1 (by rfl) ⟨952418, by rfl⟩ : syracuseStep 1269891 = 1904837) B1904837
theorem B1269907 : Blo 1268452 1269907 := bstep (se 1 (by rfl) ⟨952430, by rfl⟩ : syracuseStep 1269907 = 1904861) B1904861
theorem B3211427 : Blo 1268452 3211427 := bstep (se 1 (by rfl) ⟨2408570, by rfl⟩ : syracuseStep 3211427 = 4817141) B4817141
theorem B1269923 : Blo 1268452 1269923 := bstep (se 1 (by rfl) ⟨952442, by rfl⟩ : syracuseStep 1269923 = 1904885) B1904885
theorem B1523891 : Blo 1268452 1523891 := bstep (se 1 (by rfl) ⟨1142918, by rfl⟩ : syracuseStep 1523891 = 2285837) B2285837
theorem B1269939 : Blo 1268452 1269939 := bstep (se 1 (by rfl) ⟨952454, by rfl⟩ : syracuseStep 1269939 = 1904909) B1904909
theorem B1269955 : Blo 1268452 1269955 := bstep (se 1 (by rfl) ⟨952466, by rfl⟩ : syracuseStep 1269955 = 1904933) B1904933
theorem B1269971 : Blo 1268452 1269971 := bstep (se 1 (by rfl) ⟨952478, by rfl⟩ : syracuseStep 1269971 = 1904957) B1904957
theorem B1286371 : Blo 1268452 1286371 := bstep (se 1 (by rfl) ⟨964778, by rfl⟩ : syracuseStep 1286371 = 1929557) B1929557
theorem B1269987 : Blo 1268452 1269987 := bstep (se 1 (by rfl) ⟨952490, by rfl⟩ : syracuseStep 1269987 = 1904981) B1904981
theorem B1270003 : Blo 1268452 1270003 := bstep (se 1 (by rfl) ⟨952502, by rfl⟩ : syracuseStep 1270003 = 1905005) B1905005
theorem B2408707 : Blo 1268452 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B1270019 : Blo 1268452 1270019 := bstep (se 1 (by rfl) ⟨952514, by rfl⟩ : syracuseStep 1270019 = 1905029) B1905029
theorem B6103309 : Blo 1268452 6103309 := bstep (se 3 (by rfl) ⟨1144370, by rfl⟩ : syracuseStep 6103309 = 2288741) B2288741
theorem B1270035 : Blo 1268452 1270035 := bstep (se 1 (by rfl) ⟨952526, by rfl⟩ : syracuseStep 1270035 = 1905053) B1905053
theorem B5144867 : Blo 1268452 5144867 := bstep (se 1 (by rfl) ⟨3858650, by rfl⟩ : syracuseStep 5144867 = 7717301) B7717301
theorem B1270051 : Blo 1268452 1270051 := bstep (se 1 (by rfl) ⟨952538, by rfl⟩ : syracuseStep 1270051 = 1905077) B1905077
theorem B2408753 : Blo 1268452 2408753 := bstep (se 2 (by rfl) ⟨903282, by rfl⟩ : syracuseStep 2408753 = 1806565) B1806565
theorem B1270067 : Blo 1268452 1270067 := bstep (se 1 (by rfl) ⟨952550, by rfl⟩ : syracuseStep 1270067 = 1905101) B1905101
theorem B1270083 : Blo 1268452 1270083 := bstep (se 1 (by rfl) ⟨952562, by rfl⟩ : syracuseStep 1270083 = 1905125) B1905125
theorem B1270099 : Blo 1268452 1270099 := bstep (se 1 (by rfl) ⟨952574, by rfl⟩ : syracuseStep 1270099 = 1905149) B1905149
theorem B1270115 : Blo 1268452 1270115 := bstep (se 1 (by rfl) ⟨952586, by rfl⟩ : syracuseStep 1270115 = 1905173) B1905173
theorem B6431075 : Blo 1268452 6431075 := bstep (se 1 (by rfl) ⟨4823306, by rfl⟩ : syracuseStep 6431075 = 9646613) B9646613
theorem B1270131 : Blo 1268452 1270131 := bstep (se 1 (by rfl) ⟨952598, by rfl⟩ : syracuseStep 1270131 = 1905197) B1905197
theorem B1270147 : Blo 1268452 1270147 := bstep (se 1 (by rfl) ⟨952610, by rfl⟩ : syracuseStep 1270147 = 1905221) B1905221
theorem B4342157 : Blo 1268452 4342157 := bstep (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) B1628309
theorem B1270163 : Blo 1268452 1270163 := bstep (se 1 (by rfl) ⟨952622, by rfl⟩ : syracuseStep 1270163 = 1905245) B1905245
theorem B1270179 : Blo 1268452 1270179 := bstep (se 1 (by rfl) ⟨952634, by rfl⟩ : syracuseStep 1270179 = 1905269) B1905269
theorem B4284845 : Blo 1268452 4284845 := bstep (se 3 (by rfl) ⟨803408, by rfl⟩ : syracuseStep 4284845 = 1606817) B1606817
theorem B1270195 : Blo 1268452 1270195 := bstep (se 1 (by rfl) ⟨952646, by rfl⟩ : syracuseStep 1270195 = 1905293) B1905293
theorem B1270211 : Blo 1268452 1270211 := bstep (se 1 (by rfl) ⟨952658, by rfl⟩ : syracuseStep 1270211 = 1905317) B1905317
theorem B2712017 : Blo 1268452 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B1270227 : Blo 1268452 1270227 := bstep (se 1 (by rfl) ⟨952670, by rfl⟩ : syracuseStep 1270227 = 1905341) B1905341
theorem B4284899 : Blo 1268452 4284899 := bstep (se 1 (by rfl) ⟨3213674, by rfl⟩ : syracuseStep 4284899 = 6427349) B6427349
theorem B2712035 : Blo 1268452 2712035 := bstep (se 1 (by rfl) ⟨2034026, by rfl⟩ : syracuseStep 2712035 = 4068053) B4068053
theorem B1270243 : Blo 1268452 1270243 := bstep (se 1 (by rfl) ⟨952682, by rfl⟩ : syracuseStep 1270243 = 1905365) B1905365
theorem B1270259 : Blo 1268452 1270259 := bstep (se 1 (by rfl) ⟨952694, by rfl⟩ : syracuseStep 1270259 = 1905389) B1905389
theorem B3613187 : Blo 1268452 3613187 := bstep (se 1 (by rfl) ⟨2709890, by rfl⟩ : syracuseStep 3613187 = 5419781) B5419781
theorem B1270275 : Blo 1268452 1270275 := bstep (se 1 (by rfl) ⟨952706, by rfl⟩ : syracuseStep 1270275 = 1905413) B1905413
theorem B1270291 : Blo 1268452 1270291 := bstep (se 1 (by rfl) ⟨952718, by rfl⟩ : syracuseStep 1270291 = 1905437) B1905437
theorem B1270307 : Blo 1268452 1270307 := bstep (se 1 (by rfl) ⟨952730, by rfl⟩ : syracuseStep 1270307 = 1905461) B1905461
theorem B1270323 : Blo 1268452 1270323 := bstep (se 1 (by rfl) ⟨952742, by rfl⟩ : syracuseStep 1270323 = 1905485) B1905485
theorem B1270339 : Blo 1268452 1270339 := bstep (se 1 (by rfl) ⟨952754, by rfl⟩ : syracuseStep 1270339 = 1905509) B1905509
theorem B2409041 : Blo 1268452 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B1270355 : Blo 1268452 1270355 := bstep (se 1 (by rfl) ⟨952766, by rfl⟩ : syracuseStep 1270355 = 1905533) B1905533
theorem B1270371 : Blo 1268452 1270371 := bstep (se 1 (by rfl) ⟨952778, by rfl⟩ : syracuseStep 1270371 = 1905557) B1905557
theorem B1270387 : Blo 1268452 1270387 := bstep (se 1 (by rfl) ⟨952790, by rfl⟩ : syracuseStep 1270387 = 1905581) B1905581
theorem B1270403 : Blo 1268452 1270403 := bstep (se 1 (by rfl) ⟨952802, by rfl⟩ : syracuseStep 1270403 = 1905605) B1905605
theorem B1270419 : Blo 1268452 1270419 := bstep (se 1 (by rfl) ⟨952814, by rfl⟩ : syracuseStep 1270419 = 1905629) B1905629
theorem B1270435 : Blo 1268452 1270435 := bstep (se 1 (by rfl) ⟨952826, by rfl⟩ : syracuseStep 1270435 = 1905653) B1905653
theorem B1270451 : Blo 1268452 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B4285169 : Blo 1268452 4285169 := bstep (se 2 (by rfl) ⟨1606938, by rfl⟩ : syracuseStep 4285169 = 3213877) B3213877
theorem B1606387 : Blo 1268452 1606387 := bstep (se 1 (by rfl) ⟨1204790, by rfl⟩ : syracuseStep 1606387 = 2409581) B2409581
theorem B3613517 : Blo 1268452 3613517 := bstep (se 3 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 3613517 = 1355069) B1355069
theorem B1606483 : Blo 1268452 1606483 := bstep (se 1 (by rfl) ⟨1204862, by rfl⟩ : syracuseStep 1606483 = 2409725) B2409725
theorem B3613585 : Blo 1268452 3613585 := bstep (se 2 (by rfl) ⟨1355094, by rfl⟩ : syracuseStep 3613585 = 2710189) B2710189
theorem B5424205 : Blo 1268452 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B3212369 : Blo 1268452 3212369 := bstep (se 2 (by rfl) ⟨1204638, by rfl⟩ : syracuseStep 3212369 = 2409277) B2409277
theorem B3212419 : Blo 1268452 3212419 := bstep (se 1 (by rfl) ⟨2409314, by rfl⟩ : syracuseStep 3212419 = 4818629) B4818629
theorem B3613859 : Blo 1268452 3613859 := bstep (se 1 (by rfl) ⟨2710394, by rfl⟩ : syracuseStep 3613859 = 5420789) B5420789
theorem B7234757 : Blo 1268452 7234757 := bstep (se 4 (by rfl) ⟨678258, by rfl⟩ : syracuseStep 7234757 = 1356517) B1356517
theorem B7718129 : Blo 1268452 7718129 := bstep (se 2 (by rfl) ⟨2894298, by rfl⟩ : syracuseStep 7718129 = 5788597) B5788597
theorem B4285709 : Blo 1268452 4285709 := bstep (se 3 (by rfl) ⟨803570, by rfl⟩ : syracuseStep 4285709 = 1607141) B1607141
theorem B3212561 : Blo 1268452 3212561 := bstep (se 2 (by rfl) ⟨1204710, by rfl⟩ : syracuseStep 3212561 = 2409421) B2409421
theorem B2032931 : Blo 1268452 2032931 := bstep (se 1 (by rfl) ⟨1524698, by rfl⟩ : syracuseStep 2032931 = 3049397) B3049397
theorem B2409763 : Blo 1268452 2409763 := bstep (se 1 (by rfl) ⟨1807322, by rfl⟩ : syracuseStep 2409763 = 3614645) B3614645
theorem B1606979 : Blo 1268452 1606979 := bstep (se 1 (by rfl) ⟨1205234, by rfl⟩ : syracuseStep 1606979 = 2410469) B2410469
theorem B4285763 : Blo 1268452 4285763 := bstep (se 1 (by rfl) ⟨3214322, by rfl⟩ : syracuseStep 4285763 = 6428645) B6428645
theorem B3433859 : Blo 1268452 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B1287571 : Blo 1268452 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B2319779 : Blo 1268452 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B1287587 : Blo 1268452 1287587 := bstep (se 1 (by rfl) ⟨965690, by rfl⟩ : syracuseStep 1287587 = 1931381) B1931381
theorem B4286033 : Blo 1268452 4286033 := bstep (se 2 (by rfl) ⟨1607262, by rfl⟩ : syracuseStep 4286033 = 3214525) B3214525
theorem B4064899 : Blo 1268452 4064899 := bstep (se 1 (by rfl) ⟨3048674, by rfl⟩ : syracuseStep 4064899 = 6097349) B6097349
theorem B1427107 : Blo 1268452 1427107 := bstep (se 1 (by rfl) ⟨1070330, by rfl⟩ : syracuseStep 1427107 = 2140661) B2140661
theorem B4343473 : Blo 1268452 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B2410211 : Blo 1268452 2410211 := bstep (se 1 (by rfl) ⟨1807658, by rfl⟩ : syracuseStep 2410211 = 3615317) B3615317
theorem B4065041 : Blo 1268452 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B1427251 : Blo 1268452 1427251 := bstep (se 1 (by rfl) ⟨1070438, by rfl⟩ : syracuseStep 1427251 = 2140877) B2140877
theorem B27461429 : Blo 1268452 27461429 := bstep (se 5 (by rfl) ⟨1287254, by rfl⟩ : syracuseStep 27461429 = 2574509) B2574509
theorem B6424433 : Blo 1268452 6424433 := bstep (se 2 (by rfl) ⟨2409162, by rfl⟩ : syracuseStep 6424433 = 4818325) B4818325
theorem B4065155 : Blo 1268452 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B1427395 : Blo 1268452 1427395 := bstep (se 1 (by rfl) ⟨1070546, by rfl⟩ : syracuseStep 1427395 = 2141093) B2141093
theorem B2033603 : Blo 1268452 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B3614701 : Blo 1268452 3614701 := bstep (se 3 (by rfl) ⟨677756, by rfl⟩ : syracuseStep 3614701 = 1355513) B1355513
theorem B2410499 : Blo 1268452 2410499 := bstep (se 1 (by rfl) ⟨1807874, by rfl⟩ : syracuseStep 2410499 = 3615749) B3615749
theorem B1607683 : Blo 1268452 1607683 := bstep (se 1 (by rfl) ⟨1205762, by rfl⟩ : syracuseStep 1607683 = 2411525) B2411525
theorem B1427539 : Blo 1268452 1427539 := bstep (se 1 (by rfl) ⟨1070654, by rfl⟩ : syracuseStep 1427539 = 2141309) B2141309
theorem B1902689 : Blo 1268452 1902689 := bstep (se 2 (by rfl) ⟨713508, by rfl⟩ : syracuseStep 1902689 = 1427017) B1427017
theorem B1607779 : Blo 1268452 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B4286573 : Blo 1268452 4286573 := bstep (se 3 (by rfl) ⟨803732, by rfl⟩ : syracuseStep 4286573 = 1607465) B1607465
theorem B1902707 : Blo 1268452 1902707 := bstep (se 1 (by rfl) ⟨1427030, by rfl⟩ : syracuseStep 1902707 = 2854061) B2854061
theorem B4819085 : Blo 1268452 4819085 := bstep (se 3 (by rfl) ⟨903578, by rfl⟩ : syracuseStep 4819085 = 1807157) B1807157
theorem B3614861 : Blo 1268452 3614861 := bstep (se 3 (by rfl) ⟨677786, by rfl⟩ : syracuseStep 3614861 = 1355573) B1355573
theorem B1902737 : Blo 1268452 1902737 := bstep (se 2 (by rfl) ⟨713526, by rfl⟩ : syracuseStep 1902737 = 1427053) B1427053
theorem B1902755 : Blo 1268452 1902755 := bstep (se 1 (by rfl) ⟨1427066, by rfl⟩ : syracuseStep 1902755 = 2854133) B2854133
theorem B4286627 : Blo 1268452 4286627 := bstep (se 1 (by rfl) ⟨3214970, by rfl⟩ : syracuseStep 4286627 = 6429941) B6429941
theorem B1902785 : Blo 1268452 1902785 := bstep (se 2 (by rfl) ⟨713544, by rfl⟩ : syracuseStep 1902785 = 1427089) B1427089
theorem B1902803 : Blo 1268452 1902803 := bstep (se 1 (by rfl) ⟨1427102, by rfl⟩ : syracuseStep 1902803 = 2854205) B2854205
theorem B1427683 : Blo 1268452 1427683 := bstep (se 1 (by rfl) ⟨1070762, by rfl⟩ : syracuseStep 1427683 = 2141525) B2141525
theorem B1902833 : Blo 1268452 1902833 := bstep (se 2 (by rfl) ⟨713562, by rfl⟩ : syracuseStep 1902833 = 1427125) B1427125
theorem B3213553 : Blo 1268452 3213553 := bstep (se 2 (by rfl) ⟨1205082, by rfl⟩ : syracuseStep 3213553 = 2410165) B2410165
theorem B2033905 : Blo 1268452 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B1902851 : Blo 1268452 1902851 := bstep (se 1 (by rfl) ⟨1427138, by rfl⟩ : syracuseStep 1902851 = 2854277) B2854277
theorem B1902881 : Blo 1268452 1902881 := bstep (se 2 (by rfl) ⟨713580, by rfl⟩ : syracuseStep 1902881 = 1427161) B1427161
theorem B1902899 : Blo 1268452 1902899 := bstep (se 1 (by rfl) ⟨1427174, by rfl⟩ : syracuseStep 1902899 = 2854349) B2854349
theorem B35227957 : Blo 1268452 35227957 := bstep (se 5 (by rfl) ⟨1651310, by rfl⟩ : syracuseStep 35227957 = 3302621) B3302621
theorem B3615043 : Blo 1268452 3615043 := bstep (se 1 (by rfl) ⟨2711282, by rfl⟩ : syracuseStep 3615043 = 5422565) B5422565
theorem B1902929 : Blo 1268452 1902929 := bstep (se 2 (by rfl) ⟨713598, by rfl⟩ : syracuseStep 1902929 = 1427197) B1427197
theorem B1902947 : Blo 1268452 1902947 := bstep (se 1 (by rfl) ⟨1427210, by rfl⟩ : syracuseStep 1902947 = 2854421) B2854421
theorem B16714097 : Blo 1268452 16714097 := bstep (se 2 (by rfl) ⟨6267786, by rfl⟩ : syracuseStep 16714097 = 12535573) B12535573
theorem B1427827 : Blo 1268452 1427827 := bstep (se 1 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 1427827 = 2141741) B2141741
theorem B1902977 : Blo 1268452 1902977 := bstep (se 2 (by rfl) ⟨713616, by rfl⟩ : syracuseStep 1902977 = 1427233) B1427233
theorem B1902995 : Blo 1268452 1902995 := bstep (se 1 (by rfl) ⟨1427246, by rfl⟩ : syracuseStep 1902995 = 2854493) B2854493
theorem B1903025 : Blo 1268452 1903025 := bstep (se 2 (by rfl) ⟨713634, by rfl⟩ : syracuseStep 1903025 = 1427269) B1427269
theorem B4286897 : Blo 1268452 4286897 := bstep (se 2 (by rfl) ⟨1607586, by rfl⟩ : syracuseStep 4286897 = 3215173) B3215173
theorem B1903043 : Blo 1268452 1903043 := bstep (se 1 (by rfl) ⟨1427282, by rfl⟩ : syracuseStep 1903043 = 2854565) B2854565
theorem B2034115 : Blo 1268452 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B2140627 : Blo 1268452 2140627 := bstep (se 1 (by rfl) ⟨1605470, by rfl⟩ : syracuseStep 2140627 = 3210941) B3210941
theorem B1903073 : Blo 1268452 1903073 := bstep (se 2 (by rfl) ⟨713652, by rfl⟩ : syracuseStep 1903073 = 1427305) B1427305
theorem B2034161 : Blo 1268452 2034161 := bstep (se 2 (by rfl) ⟨762810, by rfl⟩ : syracuseStep 2034161 = 1525621) B1525621
theorem B1903091 : Blo 1268452 1903091 := bstep (se 1 (by rfl) ⟨1427318, by rfl⟩ : syracuseStep 1903091 = 2854637) B2854637
theorem B1427971 : Blo 1268452 1427971 := bstep (se 1 (by rfl) ⟨1070978, by rfl⟩ : syracuseStep 1427971 = 2141957) B2141957
theorem B3213827 : Blo 1268452 3213827 := bstep (se 1 (by rfl) ⟨2410370, by rfl⟩ : syracuseStep 3213827 = 4820741) B4820741
theorem B1903121 : Blo 1268452 1903121 := bstep (se 2 (by rfl) ⟨713670, by rfl⟩ : syracuseStep 1903121 = 1427341) B1427341
theorem B1903139 : Blo 1268452 1903139 := bstep (se 1 (by rfl) ⟨1427354, by rfl⟩ : syracuseStep 1903139 = 2854709) B2854709
theorem B1903169 : Blo 1268452 1903169 := bstep (se 2 (by rfl) ⟨713688, by rfl⟩ : syracuseStep 1903169 = 1427377) B1427377
theorem B7825997 : Blo 1268452 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B1903187 : Blo 1268452 1903187 := bstep (se 1 (by rfl) ⟨1427390, by rfl⟩ : syracuseStep 1903187 = 2854781) B2854781
theorem B2140769 : Blo 1268452 2140769 := bstep (se 2 (by rfl) ⟨802788, by rfl⟩ : syracuseStep 2140769 = 1605577) B1605577
theorem B1903217 : Blo 1268452 1903217 := bstep (se 2 (by rfl) ⟨713706, by rfl⟩ : syracuseStep 1903217 = 1427413) B1427413
theorem B1903235 : Blo 1268452 1903235 := bstep (se 1 (by rfl) ⟨1427426, by rfl⟩ : syracuseStep 1903235 = 2854853) B2854853
theorem B1428115 : Blo 1268452 1428115 := bstep (se 1 (by rfl) ⟨1071086, by rfl⟩ : syracuseStep 1428115 = 2142173) B2142173
theorem B1903265 : Blo 1268452 1903265 := bstep (se 2 (by rfl) ⟨713724, by rfl⟩ : syracuseStep 1903265 = 1427449) B1427449
theorem B1288867 : Blo 1268452 1288867 := bstep (se 1 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 1288867 = 1933301) B1933301
theorem B7719587 : Blo 1268452 7719587 := bstep (se 1 (by rfl) ⟨5789690, by rfl⟩ : syracuseStep 7719587 = 11579381) B11579381
theorem B1903283 : Blo 1268452 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B3214019 : Blo 1268452 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B21146309 : Blo 1268452 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B1903313 : Blo 1268452 1903313 := bstep (se 2 (by rfl) ⟨713742, by rfl⟩ : syracuseStep 1903313 = 1427485) B1427485
theorem B2140897 : Blo 1268452 2140897 := bstep (se 2 (by rfl) ⟨802836, by rfl⟩ : syracuseStep 2140897 = 1605673) B1605673
theorem B1903331 : Blo 1268452 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B1903361 : Blo 1268452 1903361 := bstep (se 2 (by rfl) ⟨713760, by rfl⟩ : syracuseStep 1903361 = 1427521) B1427521
theorem B2140931 : Blo 1268452 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B3050243 : Blo 1268452 3050243 := bstep (se 1 (by rfl) ⟨2287682, by rfl⟩ : syracuseStep 3050243 = 4575365) B4575365
theorem B8129285 : Blo 1268452 8129285 := bstep (se 4 (by rfl) ⟨762120, by rfl⟩ : syracuseStep 8129285 = 1524241) B1524241
theorem B3861251 : Blo 1268452 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B1903379 : Blo 1268452 1903379 := bstep (se 1 (by rfl) ⟨1427534, by rfl⟩ : syracuseStep 1903379 = 2855069) B2855069
theorem B1428259 : Blo 1268452 1428259 := bstep (se 1 (by rfl) ⟨1071194, by rfl⟩ : syracuseStep 1428259 = 2142389) B2142389
theorem B1903409 : Blo 1268452 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B1903427 : Blo 1268452 1903427 := bstep (se 1 (by rfl) ⟨1427570, by rfl⟩ : syracuseStep 1903427 = 2855141) B2855141
theorem B4066129 : Blo 1268452 4066129 := bstep (se 2 (by rfl) ⟨1524798, by rfl⟩ : syracuseStep 4066129 = 3049597) B3049597
theorem B1903457 : Blo 1268452 1903457 := bstep (se 2 (by rfl) ⟨713796, by rfl⟩ : syracuseStep 1903457 = 1427593) B1427593
theorem B11578211 : Blo 1268452 11578211 := bstep (se 1 (by rfl) ⟨8683658, by rfl⟩ : syracuseStep 11578211 = 17367317) B17367317
theorem B20573041 : Blo 1268452 20573041 := bstep (se 2 (by rfl) ⟨7714890, by rfl⟩ : syracuseStep 20573041 = 15429781) B15429781
theorem B1903475 : Blo 1268452 1903475 := bstep (se 1 (by rfl) ⟨1427606, by rfl⟩ : syracuseStep 1903475 = 2855213) B2855213
theorem B2141059 : Blo 1268452 2141059 := bstep (se 1 (by rfl) ⟨1605794, by rfl⟩ : syracuseStep 2141059 = 3211589) B3211589
theorem B1903505 : Blo 1268452 1903505 := bstep (se 2 (by rfl) ⟨713814, by rfl⟩ : syracuseStep 1903505 = 1427629) B1427629
theorem B1903523 : Blo 1268452 1903523 := bstep (se 1 (by rfl) ⟨1427642, by rfl⟩ : syracuseStep 1903523 = 2855285) B2855285
theorem B2411441 : Blo 1268452 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B1428403 : Blo 1268452 1428403 := bstep (se 1 (by rfl) ⟨1071302, by rfl⟩ : syracuseStep 1428403 = 2142605) B2142605
theorem B1903553 : Blo 1268452 1903553 := bstep (se 2 (by rfl) ⟨713832, by rfl⟩ : syracuseStep 1903553 = 1427665) B1427665
theorem B4287437 : Blo 1268452 4287437 := bstep (se 3 (by rfl) ⟨803894, by rfl⟩ : syracuseStep 4287437 = 1607789) B1607789
theorem B1903571 : Blo 1268452 1903571 := bstep (se 1 (by rfl) ⟨1427678, by rfl⟩ : syracuseStep 1903571 = 2855357) B2855357
theorem B1903601 : Blo 1268452 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B3255299 : Blo 1268452 3255299 := bstep (se 1 (by rfl) ⟨2441474, by rfl⟩ : syracuseStep 3255299 = 4882949) B4882949
theorem B1903619 : Blo 1268452 1903619 := bstep (se 1 (by rfl) ⟨1427714, by rfl⟩ : syracuseStep 1903619 = 2855429) B2855429
theorem B4287491 : Blo 1268452 4287491 := bstep (se 1 (by rfl) ⟨3215618, by rfl⟩ : syracuseStep 4287491 = 6431237) B6431237
theorem B2141201 : Blo 1268452 2141201 := bstep (se 2 (by rfl) ⟨802950, by rfl⟩ : syracuseStep 2141201 = 1605901) B1605901
theorem B1903649 : Blo 1268452 1903649 := bstep (se 2 (by rfl) ⟨713868, by rfl⟩ : syracuseStep 1903649 = 1427737) B1427737
theorem B1903667 : Blo 1268452 1903667 := bstep (se 1 (by rfl) ⟨1427750, by rfl⟩ : syracuseStep 1903667 = 2855501) B2855501
theorem B1428547 : Blo 1268452 1428547 := bstep (se 1 (by rfl) ⟨1071410, by rfl⟩ : syracuseStep 1428547 = 2142821) B2142821
theorem B13724741 : Blo 1268452 13724741 := bstep (se 4 (by rfl) ⟨1286694, by rfl⟩ : syracuseStep 13724741 = 2573389) B2573389
theorem B1903697 : Blo 1268452 1903697 := bstep (se 2 (by rfl) ⟨713886, by rfl⟩ : syracuseStep 1903697 = 1427773) B1427773
theorem B1903715 : Blo 1268452 1903715 := bstep (se 1 (by rfl) ⟨1427786, by rfl⟩ : syracuseStep 1903715 = 2855573) B2855573
theorem B9645155 : Blo 1268452 9645155 := bstep (se 1 (by rfl) ⟨7233866, by rfl⟩ : syracuseStep 9645155 = 14467733) B14467733
theorem B10841201 : Blo 1268452 10841201 := bstep (se 2 (by rfl) ⟨4065450, by rfl⟩ : syracuseStep 10841201 = 8130901) B8130901
theorem B1903745 : Blo 1268452 1903745 := bstep (se 2 (by rfl) ⟨713904, by rfl⟩ : syracuseStep 1903745 = 1427809) B1427809
theorem B2141329 : Blo 1268452 2141329 := bstep (se 2 (by rfl) ⟨802998, by rfl⟩ : syracuseStep 2141329 = 1605997) B1605997
theorem B1903763 : Blo 1268452 1903763 := bstep (se 1 (by rfl) ⟨1427822, by rfl⟩ : syracuseStep 1903763 = 2855645) B2855645
theorem B1354915 : Blo 1268452 1354915 := bstep (se 1 (by rfl) ⟨1016186, by rfl⟩ : syracuseStep 1354915 = 2032373) B2032373
theorem B2895011 : Blo 1268452 2895011 := bstep (se 1 (by rfl) ⟨2171258, by rfl⟩ : syracuseStep 2895011 = 4342517) B4342517
theorem B2575523 : Blo 1268452 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B1903793 : Blo 1268452 1903793 := bstep (se 2 (by rfl) ⟨713922, by rfl⟩ : syracuseStep 1903793 = 1427845) B1427845
theorem B2141363 : Blo 1268452 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B1903811 : Blo 1268452 1903811 := bstep (se 1 (by rfl) ⟨1427858, by rfl⟩ : syracuseStep 1903811 = 2855717) B2855717
theorem B2854097 : Blo 1268452 2854097 := bstep (se 2 (by rfl) ⟨1070286, by rfl⟩ : syracuseStep 2854097 = 2140573) B2140573
theorem B1428691 : Blo 1268452 1428691 := bstep (se 1 (by rfl) ⟨1071518, by rfl⟩ : syracuseStep 1428691 = 2143037) B2143037
theorem B1903841 : Blo 1268452 1903841 := bstep (se 2 (by rfl) ⟨713940, by rfl⟩ : syracuseStep 1903841 = 1427881) B1427881
theorem B2854115 : Blo 1268452 2854115 := bstep (se 1 (by rfl) ⟨2140586, by rfl⟩ : syracuseStep 2854115 = 4281173) B4281173
theorem B1903859 : Blo 1268452 1903859 := bstep (se 1 (by rfl) ⟨1427894, by rfl⟩ : syracuseStep 1903859 = 2855789) B2855789
theorem B2288899 : Blo 1268452 2288899 := bstep (se 1 (by rfl) ⟨1716674, by rfl⟩ : syracuseStep 2288899 = 3433349) B3433349
theorem B1903889 : Blo 1268452 1903889 := bstep (se 2 (by rfl) ⟨713958, by rfl⟩ : syracuseStep 1903889 = 1427917) B1427917
theorem B4287761 : Blo 1268452 4287761 := bstep (se 2 (by rfl) ⟨1607910, by rfl⟩ : syracuseStep 4287761 = 3215821) B3215821
theorem B1903907 : Blo 1268452 1903907 := bstep (se 1 (by rfl) ⟨1427930, by rfl⟩ : syracuseStep 1903907 = 2855861) B2855861
theorem B6425891 : Blo 1268452 6425891 := bstep (se 1 (by rfl) ⟨4819418, by rfl⟩ : syracuseStep 6425891 = 9638837) B9638837
theorem B2141491 : Blo 1268452 2141491 := bstep (se 1 (by rfl) ⟨1606118, by rfl⟩ : syracuseStep 2141491 = 3212237) B3212237
theorem B1903937 : Blo 1268452 1903937 := bstep (se 2 (by rfl) ⟨713976, by rfl⟩ : syracuseStep 1903937 = 1427953) B1427953
theorem B1903955 : Blo 1268452 1903955 := bstep (se 1 (by rfl) ⟨1427966, by rfl⟩ : syracuseStep 1903955 = 2855933) B2855933
theorem B1428835 : Blo 1268452 1428835 := bstep (se 1 (by rfl) ⟨1071626, by rfl⟩ : syracuseStep 1428835 = 2143253) B2143253
theorem B1903985 : Blo 1268452 1903985 := bstep (se 2 (by rfl) ⟨713994, by rfl⟩ : syracuseStep 1903985 = 1427989) B1427989
theorem B1904003 : Blo 1268452 1904003 := bstep (se 1 (by rfl) ⟨1428002, by rfl⟩ : syracuseStep 1904003 = 2856005) B2856005
theorem B1904033 : Blo 1268452 1904033 := bstep (se 2 (by rfl) ⟨714012, by rfl⟩ : syracuseStep 1904033 = 1428025) B1428025
theorem B4574627 : Blo 1268452 4574627 := bstep (se 1 (by rfl) ⟨3430970, by rfl⟩ : syracuseStep 4574627 = 6861941) B6861941
theorem B6860209 : Blo 1268452 6860209 := bstep (se 2 (by rfl) ⟨2572578, by rfl⟩ : syracuseStep 6860209 = 5145157) B5145157
theorem B1904051 : Blo 1268452 1904051 := bstep (se 1 (by rfl) ⟨1428038, by rfl⟩ : syracuseStep 1904051 = 2856077) B2856077
theorem B2141633 : Blo 1268452 2141633 := bstep (se 2 (by rfl) ⟨803112, by rfl⟩ : syracuseStep 2141633 = 1606225) B1606225
theorem B1904081 : Blo 1268452 1904081 := bstep (se 2 (by rfl) ⟨714030, by rfl⟩ : syracuseStep 1904081 = 1428061) B1428061
theorem B1904099 : Blo 1268452 1904099 := bstep (se 1 (by rfl) ⟨1428074, by rfl⟩ : syracuseStep 1904099 = 2856149) B2856149
theorem B8678897 : Blo 1268452 8678897 := bstep (se 2 (by rfl) ⟨3254586, by rfl⟩ : syracuseStep 8678897 = 6509173) B6509173
theorem B2854385 : Blo 1268452 2854385 := bstep (se 2 (by rfl) ⟨1070394, by rfl⟩ : syracuseStep 2854385 = 2140789) B2140789
theorem B1428979 : Blo 1268452 1428979 := bstep (se 1 (by rfl) ⟨1071734, by rfl⟩ : syracuseStep 1428979 = 2143469) B2143469
theorem B1904129 : Blo 1268452 1904129 := bstep (se 2 (by rfl) ⟨714048, by rfl⟩ : syracuseStep 1904129 = 1428097) B1428097
theorem B2854403 : Blo 1268452 2854403 := bstep (se 1 (by rfl) ⟨2140802, by rfl⟩ : syracuseStep 2854403 = 4281605) B4281605
theorem B1904147 : Blo 1268452 1904147 := bstep (se 1 (by rfl) ⟨1428110, by rfl⟩ : syracuseStep 1904147 = 2856221) B2856221
theorem B1904177 : Blo 1268452 1904177 := bstep (se 2 (by rfl) ⟨714066, by rfl⟩ : syracuseStep 1904177 = 1428133) B1428133
theorem B2141761 : Blo 1268452 2141761 := bstep (se 2 (by rfl) ⟨803160, by rfl⟩ : syracuseStep 2141761 = 1606321) B1606321
theorem B1904195 : Blo 1268452 1904195 := bstep (se 1 (by rfl) ⟨1428146, by rfl⟩ : syracuseStep 1904195 = 2856293) B2856293
theorem B1904225 : Blo 1268452 1904225 := bstep (se 2 (by rfl) ⟨714084, by rfl⟩ : syracuseStep 1904225 = 1428169) B1428169
theorem B2141795 : Blo 1268452 2141795 := bstep (se 1 (by rfl) ⟨1606346, by rfl⟩ : syracuseStep 2141795 = 3212693) B3212693
theorem B3214961 : Blo 1268452 3214961 := bstep (se 2 (by rfl) ⟨1205610, by rfl⟩ : syracuseStep 3214961 = 2411221) B2411221
theorem B1904243 : Blo 1268452 1904243 := bstep (se 1 (by rfl) ⟨1428182, by rfl⟩ : syracuseStep 1904243 = 2856365) B2856365
theorem B1429123 : Blo 1268452 1429123 := bstep (se 1 (by rfl) ⟨1071842, by rfl⟩ : syracuseStep 1429123 = 2143685) B2143685
theorem B1904273 : Blo 1268452 1904273 := bstep (se 2 (by rfl) ⟨714102, by rfl⟩ : syracuseStep 1904273 = 1428205) B1428205
theorem B1904291 : Blo 1268452 1904291 := bstep (se 1 (by rfl) ⟨1428218, by rfl⟩ : syracuseStep 1904291 = 2856437) B2856437
theorem B3215011 : Blo 1268452 3215011 := bstep (se 1 (by rfl) ⟨2411258, by rfl⟩ : syracuseStep 3215011 = 4822517) B4822517
theorem B3616433 : Blo 1268452 3616433 := bstep (se 2 (by rfl) ⟨1356162, by rfl⟩ : syracuseStep 3616433 = 2712325) B2712325
theorem B1904321 : Blo 1268452 1904321 := bstep (se 2 (by rfl) ⟨714120, by rfl⟩ : syracuseStep 1904321 = 1428241) B1428241
theorem B3862225 : Blo 1268452 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B1904339 : Blo 1268452 1904339 := bstep (se 1 (by rfl) ⟨1428254, by rfl⟩ : syracuseStep 1904339 = 2856509) B2856509
theorem B2141923 : Blo 1268452 2141923 := bstep (se 1 (by rfl) ⟨1606442, by rfl⟩ : syracuseStep 2141923 = 3212885) B3212885
theorem B1904369 : Blo 1268452 1904369 := bstep (se 2 (by rfl) ⟨714138, by rfl⟩ : syracuseStep 1904369 = 1428277) B1428277
theorem B1904387 : Blo 1268452 1904387 := bstep (se 1 (by rfl) ⟨1428290, by rfl⟩ : syracuseStep 1904387 = 2856581) B2856581
theorem B2854673 : Blo 1268452 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B1904417 : Blo 1268452 1904417 := bstep (se 2 (by rfl) ⟨714156, by rfl⟩ : syracuseStep 1904417 = 1428313) B1428313
theorem B2854691 : Blo 1268452 2854691 := bstep (se 1 (by rfl) ⟨2141018, by rfl⟩ : syracuseStep 2854691 = 4282037) B4282037
theorem B5148451 : Blo 1268452 5148451 := bstep (se 1 (by rfl) ⟨3861338, by rfl⟩ : syracuseStep 5148451 = 7722677) B7722677
theorem B3215153 : Blo 1268452 3215153 := bstep (se 2 (by rfl) ⟨1205682, by rfl⟩ : syracuseStep 3215153 = 2411365) B2411365
theorem B1904435 : Blo 1268452 1904435 := bstep (se 1 (by rfl) ⟨1428326, by rfl⟩ : syracuseStep 1904435 = 2856653) B2856653
theorem B3862349 : Blo 1268452 3862349 := bstep (se 3 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 3862349 = 1448381) B1448381
theorem B1904465 : Blo 1268452 1904465 := bstep (se 2 (by rfl) ⟨714174, by rfl⟩ : syracuseStep 1904465 = 1428349) B1428349
theorem B1904483 : Blo 1268452 1904483 := bstep (se 1 (by rfl) ⟨1428362, by rfl⟩ : syracuseStep 1904483 = 2856725) B2856725
theorem B2142065 : Blo 1268452 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B9154417 : Blo 1268452 9154417 := bstep (se 2 (by rfl) ⟨3432906, by rfl⟩ : syracuseStep 9154417 = 6865813) B6865813
theorem B1904513 : Blo 1268452 1904513 := bstep (se 2 (by rfl) ⟨714192, by rfl⟩ : syracuseStep 1904513 = 1428385) B1428385
theorem B1904531 : Blo 1268452 1904531 := bstep (se 1 (by rfl) ⟨1428398, by rfl⟩ : syracuseStep 1904531 = 2856797) B2856797
theorem B1806257 : Blo 1268452 1806257 := bstep (se 2 (by rfl) ⟨677346, by rfl⟩ : syracuseStep 1806257 = 1354693) B1354693
theorem B2895793 : Blo 1268452 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B1904561 : Blo 1268452 1904561 := bstep (se 2 (by rfl) ⟨714210, by rfl⟩ : syracuseStep 1904561 = 1428421) B1428421
theorem B1904579 : Blo 1268452 1904579 := bstep (se 1 (by rfl) ⟨1428434, by rfl⟩ : syracuseStep 1904579 = 2856869) B2856869
theorem B1904609 : Blo 1268452 1904609 := bstep (se 2 (by rfl) ⟨714228, by rfl⟩ : syracuseStep 1904609 = 1428457) B1428457
theorem B2142193 : Blo 1268452 2142193 := bstep (se 2 (by rfl) ⟨803322, by rfl⟩ : syracuseStep 2142193 = 1606645) B1606645
theorem B1904627 : Blo 1268452 1904627 := bstep (se 1 (by rfl) ⟨1428470, by rfl⟩ : syracuseStep 1904627 = 2856941) B2856941
theorem B1806337 : Blo 1268452 1806337 := bstep (se 2 (by rfl) ⟨677376, by rfl⟩ : syracuseStep 1806337 = 1354753) B1354753
theorem B1904657 : Blo 1268452 1904657 := bstep (se 2 (by rfl) ⟨714246, by rfl⟩ : syracuseStep 1904657 = 1428493) B1428493
theorem B2142227 : Blo 1268452 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B5787683 : Blo 1268452 5787683 := bstep (se 1 (by rfl) ⟨4340762, by rfl⟩ : syracuseStep 5787683 = 8681525) B8681525
theorem B1904675 : Blo 1268452 1904675 := bstep (se 1 (by rfl) ⟨1428506, by rfl⟩ : syracuseStep 1904675 = 2857013) B2857013
theorem B2854961 : Blo 1268452 2854961 := bstep (se 2 (by rfl) ⟨1070610, by rfl⟩ : syracuseStep 2854961 = 2141221) B2141221
theorem B36606005 : Blo 1268452 36606005 := bstep (se 5 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 36606005 = 3431813) B3431813
theorem B1904705 : Blo 1268452 1904705 := bstep (se 2 (by rfl) ⟨714264, by rfl⟩ : syracuseStep 1904705 = 1428529) B1428529
theorem B2854979 : Blo 1268452 2854979 := bstep (se 1 (by rfl) ⟨2141234, by rfl⟩ : syracuseStep 2854979 = 4282469) B4282469
theorem B6426701 : Blo 1268452 6426701 := bstep (se 3 (by rfl) ⟨1205006, by rfl⟩ : syracuseStep 6426701 = 2410013) B2410013
theorem B1904723 : Blo 1268452 1904723 := bstep (se 1 (by rfl) ⟨1428542, by rfl⟩ : syracuseStep 1904723 = 2857085) B2857085
theorem B1904753 : Blo 1268452 1904753 := bstep (se 2 (by rfl) ⟨714282, by rfl⟩ : syracuseStep 1904753 = 1428565) B1428565
theorem B1904771 : Blo 1268452 1904771 := bstep (se 1 (by rfl) ⟨1428578, by rfl⟩ : syracuseStep 1904771 = 2857157) B2857157
theorem B2142355 : Blo 1268452 2142355 := bstep (se 1 (by rfl) ⟨1606766, by rfl⟩ : syracuseStep 2142355 = 3213533) B3213533
theorem B1355923 : Blo 1268452 1355923 := bstep (se 1 (by rfl) ⟨1016942, by rfl⟩ : syracuseStep 1355923 = 2033885) B2033885
theorem B1904801 : Blo 1268452 1904801 := bstep (se 2 (by rfl) ⟨714300, by rfl⟩ : syracuseStep 1904801 = 1428601) B1428601
theorem B1904819 : Blo 1268452 1904819 := bstep (se 1 (by rfl) ⟨1428614, by rfl⟩ : syracuseStep 1904819 = 2857229) B2857229
theorem B1904849 : Blo 1268452 1904849 := bstep (se 2 (by rfl) ⟨714318, by rfl⟩ : syracuseStep 1904849 = 1428637) B1428637
theorem B1904867 : Blo 1268452 1904867 := bstep (se 1 (by rfl) ⟨1428650, by rfl⟩ : syracuseStep 1904867 = 2857301) B2857301
theorem B1904897 : Blo 1268452 1904897 := bstep (se 2 (by rfl) ⟨714336, by rfl⟩ : syracuseStep 1904897 = 1428673) B1428673
theorem B1904915 : Blo 1268452 1904915 := bstep (se 1 (by rfl) ⟨1428686, by rfl⟩ : syracuseStep 1904915 = 2857373) B2857373
theorem B2142497 : Blo 1268452 2142497 := bstep (se 2 (by rfl) ⟨803436, by rfl⟩ : syracuseStep 2142497 = 1606873) B1606873
theorem B1904945 : Blo 1268452 1904945 := bstep (se 2 (by rfl) ⟨714354, by rfl⟩ : syracuseStep 1904945 = 1428709) B1428709
theorem B1904963 : Blo 1268452 1904963 := bstep (se 1 (by rfl) ⟨1428722, by rfl⟩ : syracuseStep 1904963 = 2857445) B2857445
theorem B2855249 : Blo 1268452 2855249 := bstep (se 2 (by rfl) ⟨1070718, by rfl⟩ : syracuseStep 2855249 = 2141437) B2141437
theorem B3051857 : Blo 1268452 3051857 := bstep (se 2 (by rfl) ⟨1144446, by rfl⟩ : syracuseStep 3051857 = 2288893) B2288893
theorem B1904993 : Blo 1268452 1904993 := bstep (se 2 (by rfl) ⟨714372, by rfl⟩ : syracuseStep 1904993 = 1428745) B1428745
theorem B2855267 : Blo 1268452 2855267 := bstep (se 1 (by rfl) ⟨2141450, by rfl⟩ : syracuseStep 2855267 = 4282901) B4282901
theorem B15446371 : Blo 1268452 15446371 := bstep (se 1 (by rfl) ⟨11584778, by rfl⟩ : syracuseStep 15446371 = 23169557) B23169557
theorem B1905011 : Blo 1268452 1905011 := bstep (se 1 (by rfl) ⟨1428758, by rfl⟩ : syracuseStep 1905011 = 2857517) B2857517
theorem B1929617 : Blo 1268452 1929617 := bstep (se 2 (by rfl) ⟨723606, by rfl⟩ : syracuseStep 1929617 = 1447213) B1447213
theorem B1905041 : Blo 1268452 1905041 := bstep (se 2 (by rfl) ⟨714390, by rfl⟩ : syracuseStep 1905041 = 1428781) B1428781
theorem B2142625 : Blo 1268452 2142625 := bstep (se 2 (by rfl) ⟨803484, by rfl⟩ : syracuseStep 2142625 = 1606969) B1606969
theorem B1905059 : Blo 1268452 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B1905089 : Blo 1268452 1905089 := bstep (se 2 (by rfl) ⟨714408, by rfl⟩ : syracuseStep 1905089 = 1428817) B1428817
theorem B2142659 : Blo 1268452 2142659 := bstep (se 1 (by rfl) ⟨1606994, by rfl⟩ : syracuseStep 2142659 = 3213989) B3213989
theorem B1905107 : Blo 1268452 1905107 := bstep (se 1 (by rfl) ⟨1428830, by rfl⟩ : syracuseStep 1905107 = 2857661) B2857661
theorem B1905137 : Blo 1268452 1905137 := bstep (se 2 (by rfl) ⟨714426, by rfl⟩ : syracuseStep 1905137 = 1428853) B1428853
theorem B1905155 : Blo 1268452 1905155 := bstep (se 1 (by rfl) ⟨1428866, by rfl⟩ : syracuseStep 1905155 = 2857733) B2857733
theorem B1905185 : Blo 1268452 1905185 := bstep (se 2 (by rfl) ⟨714444, by rfl⟩ : syracuseStep 1905185 = 1428889) B1428889
theorem B1905203 : Blo 1268452 1905203 := bstep (se 1 (by rfl) ⟨1428902, by rfl⟩ : syracuseStep 1905203 = 2857805) B2857805
theorem B2142787 : Blo 1268452 2142787 := bstep (se 1 (by rfl) ⟨1607090, by rfl⟩ : syracuseStep 2142787 = 3214181) B3214181
theorem B5493325 : Blo 1268452 5493325 := bstep (se 3 (by rfl) ⟨1029998, by rfl⟩ : syracuseStep 5493325 = 2059997) B2059997
theorem B1905233 : Blo 1268452 1905233 := bstep (se 2 (by rfl) ⟨714462, by rfl⟩ : syracuseStep 1905233 = 1428925) B1428925
theorem B1905251 : Blo 1268452 1905251 := bstep (se 1 (by rfl) ⟨1428938, by rfl⟩ : syracuseStep 1905251 = 2857877) B2857877
theorem B3617389 : Blo 1268452 3617389 := bstep (se 3 (by rfl) ⟨678260, by rfl⟩ : syracuseStep 3617389 = 1356521) B1356521
theorem B2855537 : Blo 1268452 2855537 := bstep (se 2 (by rfl) ⟨1070826, by rfl⟩ : syracuseStep 2855537 = 2141653) B2141653
theorem B1905281 : Blo 1268452 1905281 := bstep (se 2 (by rfl) ⟨714480, by rfl⟩ : syracuseStep 1905281 = 1428961) B1428961
theorem B2855555 : Blo 1268452 2855555 := bstep (se 1 (by rfl) ⟨2141666, by rfl⟩ : syracuseStep 2855555 = 4283333) B4283333
theorem B1446547 : Blo 1268452 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B1905299 : Blo 1268452 1905299 := bstep (se 1 (by rfl) ⟨1428974, by rfl⟩ : syracuseStep 1905299 = 2857949) B2857949
theorem B1905329 : Blo 1268452 1905329 := bstep (se 2 (by rfl) ⟨714498, by rfl⟩ : syracuseStep 1905329 = 1428997) B1428997
theorem B1905347 : Blo 1268452 1905347 := bstep (se 1 (by rfl) ⟨1429010, by rfl⟩ : syracuseStep 1905347 = 2858021) B2858021
theorem B6861509 : Blo 1268452 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B12366533 : Blo 1268452 12366533 := bstep (se 4 (by rfl) ⟨1159362, by rfl⟩ : syracuseStep 12366533 = 2318725) B2318725
theorem B2142929 : Blo 1268452 2142929 := bstep (se 2 (by rfl) ⟨803598, by rfl⟩ : syracuseStep 2142929 = 1607197) B1607197
theorem B1905377 : Blo 1268452 1905377 := bstep (se 2 (by rfl) ⟨714516, by rfl⟩ : syracuseStep 1905377 = 1429033) B1429033
theorem B1905395 : Blo 1268452 1905395 := bstep (se 1 (by rfl) ⟨1429046, by rfl⟩ : syracuseStep 1905395 = 2858093) B2858093
theorem B1905425 : Blo 1268452 1905425 := bstep (se 2 (by rfl) ⟨714534, by rfl⟩ : syracuseStep 1905425 = 1429069) B1429069
theorem B1807123 : Blo 1268452 1807123 := bstep (se 1 (by rfl) ⟨1355342, by rfl⟩ : syracuseStep 1807123 = 2710685) B2710685
theorem B1905443 : Blo 1268452 1905443 := bstep (se 1 (by rfl) ⟨1429082, by rfl⟩ : syracuseStep 1905443 = 2858165) B2858165
theorem B5149489 : Blo 1268452 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B1905473 : Blo 1268452 1905473 := bstep (se 2 (by rfl) ⟨714552, by rfl⟩ : syracuseStep 1905473 = 1429105) B1429105
theorem B2143057 : Blo 1268452 2143057 := bstep (se 2 (by rfl) ⟨803646, by rfl⟩ : syracuseStep 2143057 = 1607293) B1607293
theorem B1905491 : Blo 1268452 1905491 := bstep (se 1 (by rfl) ⟨1429118, by rfl⟩ : syracuseStep 1905491 = 2858237) B2858237
theorem B3617617 : Blo 1268452 3617617 := bstep (se 2 (by rfl) ⟨1356606, by rfl⟩ : syracuseStep 3617617 = 2713213) B2713213
theorem B1905521 : Blo 1268452 1905521 := bstep (se 2 (by rfl) ⟨714570, by rfl⟩ : syracuseStep 1905521 = 1429141) B1429141
theorem B2143091 : Blo 1268452 2143091 := bstep (se 1 (by rfl) ⟨1607318, by rfl⟩ : syracuseStep 2143091 = 3214637) B3214637
theorem B1905539 : Blo 1268452 1905539 := bstep (se 1 (by rfl) ⟨1429154, by rfl⟩ : syracuseStep 1905539 = 2858309) B2858309
theorem B2855825 : Blo 1268452 2855825 := bstep (se 2 (by rfl) ⟨1070934, by rfl⟩ : syracuseStep 2855825 = 2141869) B2141869
theorem B1905569 : Blo 1268452 1905569 := bstep (se 2 (by rfl) ⟨714588, by rfl⟩ : syracuseStep 1905569 = 1429177) B1429177
theorem B3429283 : Blo 1268452 3429283 := bstep (se 1 (by rfl) ⟨2571962, by rfl⟩ : syracuseStep 3429283 = 5143925) B5143925
theorem B2855843 : Blo 1268452 2855843 := bstep (se 1 (by rfl) ⟨2141882, by rfl⟩ : syracuseStep 2855843 = 4283765) B4283765
theorem B1446835 : Blo 1268452 1446835 := bstep (se 1 (by rfl) ⟨1085126, by rfl⟩ : syracuseStep 1446835 = 2170253) B2170253
theorem B1905587 : Blo 1268452 1905587 := bstep (se 1 (by rfl) ⟨1429190, by rfl⟩ : syracuseStep 1905587 = 2858381) B2858381
theorem B16274357 : Blo 1268452 16274357 := bstep (se 5 (by rfl) ⟨762860, by rfl⟩ : syracuseStep 16274357 = 1525721) B1525721
theorem B1831889 : Blo 1268452 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B1905617 : Blo 1268452 1905617 := bstep (se 2 (by rfl) ⟨714606, by rfl⟩ : syracuseStep 1905617 = 1429213) B1429213
theorem B1905635 : Blo 1268452 1905635 := bstep (se 1 (by rfl) ⟨1429226, by rfl⟩ : syracuseStep 1905635 = 2858453) B2858453
theorem B4822001 : Blo 1268452 4822001 := bstep (se 2 (by rfl) ⟨1808250, by rfl⟩ : syracuseStep 4822001 = 3616501) B3616501
theorem B3617777 : Blo 1268452 3617777 := bstep (se 2 (by rfl) ⟨1356666, by rfl⟩ : syracuseStep 3617777 = 2713333) B2713333
theorem B2143219 : Blo 1268452 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B1905665 : Blo 1268452 1905665 := bstep (se 2 (by rfl) ⟨714624, by rfl⟩ : syracuseStep 1905665 = 1429249) B1429249
theorem B4281389 : Blo 1268452 4281389 := bstep (se 3 (by rfl) ⟨802760, by rfl⟩ : syracuseStep 4281389 = 1605521) B1605521
theorem B4281443 : Blo 1268452 4281443 := bstep (se 1 (by rfl) ⟨3211082, by rfl⟩ : syracuseStep 4281443 = 6422165) B6422165
theorem B11580515 : Blo 1268452 11580515 := bstep (se 1 (by rfl) ⟨8685386, by rfl⟩ : syracuseStep 11580515 = 17370773) B17370773
theorem B29717617 : Blo 1268452 29717617 := bstep (se 2 (by rfl) ⟨11144106, by rfl⟩ : syracuseStep 29717617 = 22288213) B22288213
theorem B2143361 : Blo 1268452 2143361 := bstep (se 2 (by rfl) ⟨803760, by rfl⟩ : syracuseStep 2143361 = 1607521) B1607521
theorem B2856113 : Blo 1268452 2856113 := bstep (se 2 (by rfl) ⟨1071042, by rfl⟩ : syracuseStep 2856113 = 2142085) B2142085
theorem B2856131 : Blo 1268452 2856131 := bstep (se 1 (by rfl) ⟨2142098, by rfl⟩ : syracuseStep 2856131 = 4284197) B4284197
theorem B1807601 : Blo 1268452 1807601 := bstep (se 2 (by rfl) ⟨677850, by rfl⟩ : syracuseStep 1807601 = 1355701) B1355701
theorem B1930481 : Blo 1268452 1930481 := bstep (se 2 (by rfl) ⟨723930, by rfl⟩ : syracuseStep 1930481 = 1447861) B1447861
theorem B9155825 : Blo 1268452 9155825 := bstep (se 2 (by rfl) ⟨3433434, by rfl⟩ : syracuseStep 9155825 = 6866869) B6866869
theorem B2143489 : Blo 1268452 2143489 := bstep (se 2 (by rfl) ⟨803808, by rfl⟩ : syracuseStep 2143489 = 1607617) B1607617
theorem B2143523 : Blo 1268452 2143523 := bstep (se 1 (by rfl) ⟨1607642, by rfl⟩ : syracuseStep 2143523 = 3215285) B3215285
theorem B1807715 : Blo 1268452 1807715 := bstep (se 1 (by rfl) ⟨1355786, by rfl⟩ : syracuseStep 1807715 = 2711573) B2711573
theorem B4281713 : Blo 1268452 4281713 := bstep (se 2 (by rfl) ⟨1605642, by rfl⟩ : syracuseStep 4281713 = 3211285) B3211285
theorem B2143651 : Blo 1268452 2143651 := bstep (se 1 (by rfl) ⟨1607738, by rfl⟩ : syracuseStep 2143651 = 3215477) B3215477
theorem B5420465 : Blo 1268452 5420465 := bstep (se 2 (by rfl) ⟨2032674, by rfl⟩ : syracuseStep 5420465 = 4065349) B4065349
theorem B1807795 : Blo 1268452 1807795 := bstep (se 1 (by rfl) ⟨1355846, by rfl⟩ : syracuseStep 1807795 = 2711693) B2711693
theorem B2856401 : Blo 1268452 2856401 := bstep (se 2 (by rfl) ⟨1071150, by rfl⟩ : syracuseStep 2856401 = 2142301) B2142301
theorem B2856419 : Blo 1268452 2856419 := bstep (se 1 (by rfl) ⟨2142314, by rfl⟩ : syracuseStep 2856419 = 4284629) B4284629
theorem B3094051 : Blo 1268452 3094051 := bstep (se 1 (by rfl) ⟨2320538, by rfl⟩ : syracuseStep 3094051 = 4641077) B4641077
theorem B2143793 : Blo 1268452 2143793 := bstep (se 2 (by rfl) ⟨803922, by rfl⟩ : syracuseStep 2143793 = 1607845) B1607845
theorem B7722701 : Blo 1268452 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B2856689 : Blo 1268452 2856689 := bstep (se 2 (by rfl) ⟨1071258, by rfl⟩ : syracuseStep 2856689 = 2142517) B2142517
theorem B2856707 : Blo 1268452 2856707 := bstep (se 1 (by rfl) ⟨2142530, by rfl⟩ : syracuseStep 2856707 = 4285061) B4285061
theorem B2709283 : Blo 1268452 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B6510449 : Blo 1268452 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B4282253 : Blo 1268452 4282253 := bstep (se 3 (by rfl) ⟨802922, by rfl⟩ : syracuseStep 4282253 = 1605845) B1605845
theorem B24409997 : Blo 1268452 24409997 := bstep (se 3 (by rfl) ⟨4576874, by rfl⟩ : syracuseStep 24409997 = 9153749) B9153749
theorem B4282307 : Blo 1268452 4282307 := bstep (se 1 (by rfl) ⟨3211730, by rfl⟩ : syracuseStep 4282307 = 6423461) B6423461
theorem B1808353 : Blo 1268452 1808353 := bstep (se 2 (by rfl) ⟨678132, by rfl⟩ : syracuseStep 1808353 = 1356265) B1356265
theorem B2856977 : Blo 1268452 2856977 := bstep (se 2 (by rfl) ⟨1071366, by rfl⟩ : syracuseStep 2856977 = 2142733) B2142733
theorem B2856995 : Blo 1268452 2856995 := bstep (se 1 (by rfl) ⟨2142746, by rfl⟩ : syracuseStep 2856995 = 4285493) B4285493
theorem B4888781 : Blo 1268452 4888781 := bstep (se 3 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 4888781 = 1833293) B1833293
theorem B4282577 : Blo 1268452 4282577 := bstep (se 2 (by rfl) ⟨1605966, by rfl⟩ : syracuseStep 4282577 = 3211933) B3211933
theorem B4888867 : Blo 1268452 4888867 := bstep (se 1 (by rfl) ⟨3666650, by rfl⟩ : syracuseStep 4888867 = 7333301) B7333301
theorem B2857265 : Blo 1268452 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B2857283 : Blo 1268452 2857283 := bstep (se 1 (by rfl) ⟨2142962, by rfl⟩ : syracuseStep 2857283 = 4285925) B4285925
theorem B4823459 : Blo 1268452 4823459 := bstep (se 1 (by rfl) ⟨3617594, by rfl⟩ : syracuseStep 4823459 = 7235189) B7235189
theorem B14645731 : Blo 1268452 14645731 := bstep (se 1 (by rfl) ⟨10984298, by rfl⟩ : syracuseStep 14645731 = 21968597) B21968597
theorem B2857553 : Blo 1268452 2857553 := bstep (se 2 (by rfl) ⟨1071582, by rfl⟩ : syracuseStep 2857553 = 2143165) B2143165
theorem B2857571 : Blo 1268452 2857571 := bstep (se 1 (by rfl) ⟨2143178, by rfl⟩ : syracuseStep 2857571 = 4286357) B4286357
theorem B25066097 : Blo 1268452 25066097 := bstep (se 2 (by rfl) ⟨9399786, by rfl⟩ : syracuseStep 25066097 = 18799573) B18799573
theorem B24402545 : Blo 1268452 24402545 := bstep (se 2 (by rfl) ⟨9150954, by rfl⟩ : syracuseStep 24402545 = 18301909) B18301909
theorem B4283117 : Blo 1268452 4283117 := bstep (se 3 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 4283117 = 1606169) B1606169
theorem B1268467 : Blo 1268452 1268467 := bstep (se 1 (by rfl) ⟨951350, by rfl⟩ : syracuseStep 1268467 = 1902701) B1902701
theorem B1268483 : Blo 1268452 1268483 := bstep (se 1 (by rfl) ⟨951362, by rfl⟩ : syracuseStep 1268483 = 1902725) B1902725
theorem B1268499 : Blo 1268452 1268499 := bstep (se 1 (by rfl) ⟨951374, by rfl⟩ : syracuseStep 1268499 = 1902749) B1902749
theorem B1268515 : Blo 1268452 1268515 := bstep (se 1 (by rfl) ⟨951386, by rfl⟩ : syracuseStep 1268515 = 1902773) B1902773
theorem B4283171 : Blo 1268452 4283171 := bstep (se 1 (by rfl) ⟨3212378, by rfl⟩ : syracuseStep 4283171 = 6424757) B6424757
theorem B1268531 : Blo 1268452 1268531 := bstep (se 1 (by rfl) ⟨951398, by rfl⟩ : syracuseStep 1268531 = 1902797) B1902797
theorem B1268547 : Blo 1268452 1268547 := bstep (se 1 (by rfl) ⟨951410, by rfl⟩ : syracuseStep 1268547 = 1902821) B1902821
theorem B1268563 : Blo 1268452 1268563 := bstep (se 1 (by rfl) ⟨951422, by rfl⟩ : syracuseStep 1268563 = 1902845) B1902845
theorem B1268579 : Blo 1268452 1268579 := bstep (se 1 (by rfl) ⟨951434, by rfl⟩ : syracuseStep 1268579 = 1902869) B1902869
theorem B2857841 : Blo 1268452 2857841 := bstep (se 2 (by rfl) ⟨1071690, by rfl⟩ : syracuseStep 2857841 = 2143381) B2143381
theorem B1268595 : Blo 1268452 1268595 := bstep (se 1 (by rfl) ⟨951446, by rfl⟩ : syracuseStep 1268595 = 1902893) B1902893
theorem B1268611 : Blo 1268452 1268611 := bstep (se 1 (by rfl) ⟨951458, by rfl⟩ : syracuseStep 1268611 = 1902917) B1902917
theorem B2857859 : Blo 1268452 2857859 := bstep (se 1 (by rfl) ⟨2143394, by rfl⟩ : syracuseStep 2857859 = 4286789) B4286789
theorem B10853261 : Blo 1268452 10853261 := bstep (se 3 (by rfl) ⟨2034986, by rfl⟩ : syracuseStep 10853261 = 4069973) B4069973
theorem B1268627 : Blo 1268452 1268627 := bstep (se 1 (by rfl) ⟨951470, by rfl⟩ : syracuseStep 1268627 = 1902941) B1902941
theorem B1268643 : Blo 1268452 1268643 := bstep (se 1 (by rfl) ⟨951482, by rfl⟩ : syracuseStep 1268643 = 1902965) B1902965
theorem B6429617 : Blo 1268452 6429617 := bstep (se 2 (by rfl) ⟨2411106, by rfl⟩ : syracuseStep 6429617 = 4822213) B4822213
theorem B1268659 : Blo 1268452 1268659 := bstep (se 1 (by rfl) ⟨951494, by rfl⟩ : syracuseStep 1268659 = 1902989) B1902989
theorem B1268675 : Blo 1268452 1268675 := bstep (se 1 (by rfl) ⟨951506, by rfl⟩ : syracuseStep 1268675 = 1903013) B1903013
theorem B1268691 : Blo 1268452 1268691 := bstep (se 1 (by rfl) ⟨951518, by rfl⟩ : syracuseStep 1268691 = 1903037) B1903037
theorem B1268707 : Blo 1268452 1268707 := bstep (se 1 (by rfl) ⟨951530, by rfl⟩ : syracuseStep 1268707 = 1903061) B1903061
theorem B2710513 : Blo 1268452 2710513 := bstep (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) B2032885
theorem B1268723 : Blo 1268452 1268723 := bstep (se 1 (by rfl) ⟨951542, by rfl⟩ : syracuseStep 1268723 = 1903085) B1903085
theorem B1268739 : Blo 1268452 1268739 := bstep (se 1 (by rfl) ⟨951554, by rfl⟩ : syracuseStep 1268739 = 1903109) B1903109
theorem B10845197 : Blo 1268452 10845197 := bstep (se 3 (by rfl) ⟨2033474, by rfl⟩ : syracuseStep 10845197 = 4066949) B4066949
theorem B1268755 : Blo 1268452 1268755 := bstep (se 1 (by rfl) ⟨951566, by rfl⟩ : syracuseStep 1268755 = 1903133) B1903133
theorem B1268771 : Blo 1268452 1268771 := bstep (se 1 (by rfl) ⟨951578, by rfl⟩ : syracuseStep 1268771 = 1903157) B1903157
theorem B4283441 : Blo 1268452 4283441 := bstep (se 2 (by rfl) ⟨1606290, by rfl⟩ : syracuseStep 4283441 = 3212581) B3212581
theorem B1268787 : Blo 1268452 1268787 := bstep (se 1 (by rfl) ⟨951590, by rfl⟩ : syracuseStep 1268787 = 1903181) B1903181
theorem B1268803 : Blo 1268452 1268803 := bstep (se 1 (by rfl) ⟨951602, by rfl⟩ : syracuseStep 1268803 = 1903205) B1903205
theorem B1268819 : Blo 1268452 1268819 := bstep (se 1 (by rfl) ⟨951614, by rfl⟩ : syracuseStep 1268819 = 1903229) B1903229
theorem B1268835 : Blo 1268452 1268835 := bstep (se 1 (by rfl) ⟨951626, by rfl⟩ : syracuseStep 1268835 = 1903253) B1903253
theorem B10288241 : Blo 1268452 10288241 := bstep (se 2 (by rfl) ⟨3858090, by rfl⟩ : syracuseStep 10288241 = 7716181) B7716181
theorem B16260209 : Blo 1268452 16260209 := bstep (se 2 (by rfl) ⟨6097578, by rfl⟩ : syracuseStep 16260209 = 12195157) B12195157
theorem B1268851 : Blo 1268452 1268851 := bstep (se 1 (by rfl) ⟨951638, by rfl⟩ : syracuseStep 1268851 = 1903277) B1903277
theorem B2169985 : Blo 1268452 2169985 := bstep (se 2 (by rfl) ⟨813744, by rfl⟩ : syracuseStep 2169985 = 1627489) B1627489
theorem B1268867 : Blo 1268452 1268867 := bstep (se 1 (by rfl) ⟨951650, by rfl⟩ : syracuseStep 1268867 = 1903301) B1903301
theorem B2858129 : Blo 1268452 2858129 := bstep (se 2 (by rfl) ⟨1071798, by rfl⟩ : syracuseStep 2858129 = 2143597) B2143597
theorem B1268883 : Blo 1268452 1268883 := bstep (se 1 (by rfl) ⟨951662, by rfl⟩ : syracuseStep 1268883 = 1903325) B1903325
theorem B1268899 : Blo 1268452 1268899 := bstep (se 1 (by rfl) ⟨951674, by rfl⟩ : syracuseStep 1268899 = 1903349) B1903349
theorem B2858147 : Blo 1268452 2858147 := bstep (se 1 (by rfl) ⟨2143610, by rfl⟩ : syracuseStep 2858147 = 4287221) B4287221
theorem B1268915 : Blo 1268452 1268915 := bstep (se 1 (by rfl) ⟨951686, by rfl⟩ : syracuseStep 1268915 = 1903373) B1903373
theorem B1268931 : Blo 1268452 1268931 := bstep (se 1 (by rfl) ⟨951698, by rfl⟩ : syracuseStep 1268931 = 1903397) B1903397
theorem B1268947 : Blo 1268452 1268947 := bstep (se 1 (by rfl) ⟨951710, by rfl⟩ : syracuseStep 1268947 = 1903421) B1903421
theorem B1268963 : Blo 1268452 1268963 := bstep (se 1 (by rfl) ⟨951722, by rfl⟩ : syracuseStep 1268963 = 1903445) B1903445
theorem B14466275 : Blo 1268452 14466275 := bstep (se 1 (by rfl) ⟨10849706, by rfl⟩ : syracuseStep 14466275 = 21699413) B21699413
theorem B1268979 : Blo 1268452 1268979 := bstep (se 1 (by rfl) ⟨951734, by rfl⟩ : syracuseStep 1268979 = 1903469) B1903469
theorem B1268995 : Blo 1268452 1268995 := bstep (se 1 (by rfl) ⟨951746, by rfl⟩ : syracuseStep 1268995 = 1903493) B1903493
theorem B7232773 : Blo 1268452 7232773 := bstep (se 4 (by rfl) ⟨678072, by rfl⟩ : syracuseStep 7232773 = 1356145) B1356145
theorem B1269011 : Blo 1268452 1269011 := bstep (se 1 (by rfl) ⟨951758, by rfl⟩ : syracuseStep 1269011 = 1903517) B1903517
theorem B1269027 : Blo 1268452 1269027 := bstep (se 1 (by rfl) ⟨951770, by rfl⟩ : syracuseStep 1269027 = 1903541) B1903541
theorem B1269043 : Blo 1268452 1269043 := bstep (se 1 (by rfl) ⟨951782, by rfl⟩ : syracuseStep 1269043 = 1903565) B1903565
theorem B1269059 : Blo 1268452 1269059 := bstep (se 1 (by rfl) ⟨951794, by rfl⟩ : syracuseStep 1269059 = 1903589) B1903589
theorem B7322957 : Blo 1268452 7322957 := bstep (se 3 (by rfl) ⟨1373054, by rfl⟩ : syracuseStep 7322957 = 2746109) B2746109
theorem B1269075 : Blo 1268452 1269075 := bstep (se 1 (by rfl) ⟨951806, by rfl⟩ : syracuseStep 1269075 = 1903613) B1903613
theorem B1269091 : Blo 1268452 1269091 := bstep (se 1 (by rfl) ⟨951818, by rfl⟩ : syracuseStep 1269091 = 1903637) B1903637
theorem B1269107 : Blo 1268452 1269107 := bstep (se 1 (by rfl) ⟨951830, by rfl⟩ : syracuseStep 1269107 = 1903661) B1903661
theorem B1269123 : Blo 1268452 1269123 := bstep (se 1 (by rfl) ⟨951842, by rfl⟩ : syracuseStep 1269123 = 1903685) B1903685
theorem B1269139 : Blo 1268452 1269139 := bstep (se 1 (by rfl) ⟨951854, by rfl⟩ : syracuseStep 1269139 = 1903709) B1903709
theorem B1269155 : Blo 1268452 1269155 := bstep (se 1 (by rfl) ⟨951866, by rfl⟩ : syracuseStep 1269155 = 1903733) B1903733
theorem B2858417 : Blo 1268452 2858417 := bstep (se 2 (by rfl) ⟨1071906, by rfl⟩ : syracuseStep 2858417 = 2143813) B2143813
theorem B1269171 : Blo 1268452 1269171 := bstep (se 1 (by rfl) ⟨951878, by rfl⟩ : syracuseStep 1269171 = 1903757) B1903757
theorem B1269187 : Blo 1268452 1269187 := bstep (se 1 (by rfl) ⟨951890, by rfl⟩ : syracuseStep 1269187 = 1903781) B1903781
theorem B2858435 : Blo 1268452 2858435 := bstep (se 1 (by rfl) ⟨2143826, by rfl⟩ : syracuseStep 2858435 = 4287653) B4287653
theorem B1269203 : Blo 1268452 1269203 := bstep (se 1 (by rfl) ⟨951902, by rfl⟩ : syracuseStep 1269203 = 1903805) B1903805
theorem B10837475 : Blo 1268452 10837475 := bstep (se 1 (by rfl) ⟨8128106, by rfl⟩ : syracuseStep 10837475 = 16256213) B16256213
theorem B1269219 : Blo 1268452 1269219 := bstep (se 1 (by rfl) ⟨951914, by rfl⟩ : syracuseStep 1269219 = 1903829) B1903829
theorem B1269235 : Blo 1268452 1269235 := bstep (se 1 (by rfl) ⟨951926, by rfl⟩ : syracuseStep 1269235 = 1903853) B1903853
theorem B1269251 : Blo 1268452 1269251 := bstep (se 1 (by rfl) ⟨951938, by rfl⟩ : syracuseStep 1269251 = 1903877) B1903877
theorem B1269267 : Blo 1268452 1269267 := bstep (se 1 (by rfl) ⟨951950, by rfl⟩ : syracuseStep 1269267 = 1903901) B1903901
theorem B1269283 : Blo 1268452 1269283 := bstep (se 1 (by rfl) ⟨951962, by rfl⟩ : syracuseStep 1269283 = 1903925) B1903925
theorem B1269299 : Blo 1268452 1269299 := bstep (se 1 (by rfl) ⟨951974, by rfl⟩ : syracuseStep 1269299 = 1903949) B1903949
theorem B1269315 : Blo 1268452 1269315 := bstep (se 1 (by rfl) ⟨951986, by rfl⟩ : syracuseStep 1269315 = 1903973) B1903973
theorem B4283981 : Blo 1268452 4283981 := bstep (se 3 (by rfl) ⟨803246, by rfl⟩ : syracuseStep 4283981 = 1606493) B1606493
theorem B1269331 : Blo 1268452 1269331 := bstep (se 1 (by rfl) ⟨951998, by rfl⟩ : syracuseStep 1269331 = 1903997) B1903997
theorem B1269347 : Blo 1268452 1269347 := bstep (se 1 (by rfl) ⟨952010, by rfl⟩ : syracuseStep 1269347 = 1904021) B1904021
theorem B1269363 : Blo 1268452 1269363 := bstep (se 1 (by rfl) ⟨952022, by rfl⟩ : syracuseStep 1269363 = 1904045) B1904045
theorem B4284035 : Blo 1268452 4284035 := bstep (se 1 (by rfl) ⟨3213026, by rfl⟩ : syracuseStep 4284035 = 6426053) B6426053
theorem B1269379 : Blo 1268452 1269379 := bstep (se 1 (by rfl) ⟨952034, by rfl⟩ : syracuseStep 1269379 = 1904069) B1904069
theorem B1269395 : Blo 1268452 1269395 := bstep (se 1 (by rfl) ⟨952046, by rfl⟩ : syracuseStep 1269395 = 1904093) B1904093
theorem B1269411 : Blo 1268452 1269411 := bstep (se 1 (by rfl) ⟨952058, by rfl⟩ : syracuseStep 1269411 = 1904117) B1904117
theorem B1269427 : Blo 1268452 1269427 := bstep (se 1 (by rfl) ⟨952070, by rfl⟩ : syracuseStep 1269427 = 1904141) B1904141
theorem B1269443 : Blo 1268452 1269443 := bstep (se 1 (by rfl) ⟨952082, by rfl⟩ : syracuseStep 1269443 = 1904165) B1904165
theorem B3210961 : Blo 1268452 3210961 := bstep (se 2 (by rfl) ⟨1204110, by rfl⟩ : syracuseStep 3210961 = 2408221) B2408221
theorem B1269459 : Blo 1268452 1269459 := bstep (se 1 (by rfl) ⟨952094, by rfl⟩ : syracuseStep 1269459 = 1904189) B1904189
theorem B1269475 : Blo 1268452 1269475 := bstep (se 1 (by rfl) ⟨952106, by rfl⟩ : syracuseStep 1269475 = 1904213) B1904213
theorem B3612401 : Blo 1268452 3612401 := bstep (se 2 (by rfl) ⟨1354650, by rfl⟩ : syracuseStep 3612401 = 2709301) B2709301
theorem B1269491 : Blo 1268452 1269491 := bstep (se 1 (by rfl) ⟨952118, by rfl⟩ : syracuseStep 1269491 = 1904237) B1904237
theorem B1269507 : Blo 1268452 1269507 := bstep (se 1 (by rfl) ⟨952130, by rfl⟩ : syracuseStep 1269507 = 1904261) B1904261
theorem B1269523 : Blo 1268452 1269523 := bstep (se 1 (by rfl) ⟨952142, by rfl⟩ : syracuseStep 1269523 = 1904285) B1904285
theorem B1269539 : Blo 1268452 1269539 := bstep (se 1 (by rfl) ⟨952154, by rfl⟩ : syracuseStep 1269539 = 1904309) B1904309
theorem B1269555 : Blo 1268452 1269555 := bstep (se 1 (by rfl) ⟨952166, by rfl⟩ : syracuseStep 1269555 = 1904333) B1904333
theorem B1269571 : Blo 1268452 1269571 := bstep (se 1 (by rfl) ⟨952178, by rfl⟩ : syracuseStep 1269571 = 1904357) B1904357
theorem B6864709 : Blo 1268452 6864709 := bstep (se 4 (by rfl) ⟨643566, by rfl⟩ : syracuseStep 6864709 = 1287133) B1287133
theorem B1269587 : Blo 1268452 1269587 := bstep (se 1 (by rfl) ⟨952190, by rfl⟩ : syracuseStep 1269587 = 1904381) B1904381
theorem B1269603 : Blo 1268452 1269603 := bstep (se 1 (by rfl) ⟨952202, by rfl⟩ : syracuseStep 1269603 = 1904405) B1904405
theorem B2408305 : Blo 1268452 2408305 := bstep (se 2 (by rfl) ⟨903114, by rfl⟩ : syracuseStep 2408305 = 1806229) B1806229
theorem B1269619 : Blo 1268452 1269619 := bstep (se 1 (by rfl) ⟨952214, by rfl⟩ : syracuseStep 1269619 = 1904429) B1904429
theorem B1269635 : Blo 1268452 1269635 := bstep (se 1 (by rfl) ⟨952226, by rfl⟩ : syracuseStep 1269635 = 1904453) B1904453
theorem B3915661 : Blo 1268452 3915661 := bstep (se 3 (by rfl) ⟨734186, by rfl⟩ : syracuseStep 3915661 = 1468373) B1468373
theorem B4284305 : Blo 1268452 4284305 := bstep (se 2 (by rfl) ⟨1606614, by rfl⟩ : syracuseStep 4284305 = 3213229) B3213229
theorem B1269651 : Blo 1268452 1269651 := bstep (se 1 (by rfl) ⟨952238, by rfl⟩ : syracuseStep 1269651 = 1904477) B1904477
theorem B1269667 : Blo 1268452 1269667 := bstep (se 1 (by rfl) ⟨952250, by rfl⟩ : syracuseStep 1269667 = 1904501) B1904501
theorem B1269683 : Blo 1268452 1269683 := bstep (se 1 (by rfl) ⟨952262, by rfl⟩ : syracuseStep 1269683 = 1904525) B1904525
theorem B1269699 : Blo 1268452 1269699 := bstep (se 1 (by rfl) ⟨952274, by rfl⟩ : syracuseStep 1269699 = 1904549) B1904549
theorem B30883781 : Blo 1268452 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B1269715 : Blo 1268452 1269715 := bstep (se 1 (by rfl) ⟨952286, by rfl⟩ : syracuseStep 1269715 = 1904573) B1904573
theorem B3211235 : Blo 1268452 3211235 := bstep (se 1 (by rfl) ⟨2408426, by rfl⟩ : syracuseStep 3211235 = 4816853) B4816853
theorem B4816867 : Blo 1268452 4816867 := bstep (se 1 (by rfl) ⟨3612650, by rfl⟩ : syracuseStep 4816867 = 7225301) B7225301
theorem B1269731 : Blo 1268452 1269731 := bstep (se 1 (by rfl) ⟨952298, by rfl⟩ : syracuseStep 1269731 = 1904597) B1904597
theorem B1269747 : Blo 1268452 1269747 := bstep (se 1 (by rfl) ⟨952310, by rfl⟩ : syracuseStep 1269747 = 1904621) B1904621
theorem B2408449 : Blo 1268452 2408449 := bstep (se 2 (by rfl) ⟨903168, by rfl⟩ : syracuseStep 2408449 = 1806337) B1806337
theorem B1269771 : Blo 1268452 1269771 := bstep (se 1 (by rfl) ⟨952328, by rfl⟩ : syracuseStep 1269771 = 1904657) B1904657
theorem B3858455 : Blo 1268452 3858455 := bstep (se 1 (by rfl) ⟨2893841, by rfl⟩ : syracuseStep 3858455 = 5787683) B5787683
theorem B1269783 : Blo 1268452 1269783 := bstep (se 1 (by rfl) ⟨952337, by rfl⟩ : syracuseStep 1269783 = 1904675) B1904675
theorem B24404003 : Blo 1268452 24404003 := bstep (se 1 (by rfl) ⟨18303002, by rfl⟩ : syracuseStep 24404003 = 36606005) B36606005
theorem B1269803 : Blo 1268452 1269803 := bstep (se 1 (by rfl) ⟨952352, by rfl⟩ : syracuseStep 1269803 = 1904705) B1904705
theorem B4284467 : Blo 1268452 4284467 := bstep (se 1 (by rfl) ⟨3213350, by rfl⟩ : syracuseStep 4284467 = 6426701) B6426701
theorem B1269815 : Blo 1268452 1269815 := bstep (se 1 (by rfl) ⟨952361, by rfl⟩ : syracuseStep 1269815 = 1904723) B1904723
theorem B1269835 : Blo 1268452 1269835 := bstep (se 1 (by rfl) ⟨952376, by rfl⟩ : syracuseStep 1269835 = 1904753) B1904753
theorem B1269847 : Blo 1268452 1269847 := bstep (se 1 (by rfl) ⟨952385, by rfl⟩ : syracuseStep 1269847 = 1904771) B1904771
theorem B1269867 : Blo 1268452 1269867 := bstep (se 1 (by rfl) ⟨952400, by rfl⟩ : syracuseStep 1269867 = 1904801) B1904801
theorem B1269879 : Blo 1268452 1269879 := bstep (se 1 (by rfl) ⟨952409, by rfl⟩ : syracuseStep 1269879 = 1904819) B1904819
theorem B1269899 : Blo 1268452 1269899 := bstep (se 1 (by rfl) ⟨952424, by rfl⟩ : syracuseStep 1269899 = 1904849) B1904849
theorem B1269911 : Blo 1268452 1269911 := bstep (se 1 (by rfl) ⟨952433, by rfl⟩ : syracuseStep 1269911 = 1904867) B1904867
theorem B1269931 : Blo 1268452 1269931 := bstep (se 1 (by rfl) ⟨952448, by rfl⟩ : syracuseStep 1269931 = 1904897) B1904897
theorem B1269943 : Blo 1268452 1269943 := bstep (se 1 (by rfl) ⟨952457, by rfl⟩ : syracuseStep 1269943 = 1904915) B1904915
theorem B1605835 : Blo 1268452 1605835 := bstep (se 1 (by rfl) ⟨1204376, by rfl⟩ : syracuseStep 1605835 = 2408753) B2408753
theorem B1269963 : Blo 1268452 1269963 := bstep (se 1 (by rfl) ⟨952472, by rfl⟩ : syracuseStep 1269963 = 1904945) B1904945
theorem B1269975 : Blo 1268452 1269975 := bstep (se 1 (by rfl) ⟨952481, by rfl⟩ : syracuseStep 1269975 = 1904963) B1904963
theorem B1269995 : Blo 1268452 1269995 := bstep (se 1 (by rfl) ⟨952496, by rfl⟩ : syracuseStep 1269995 = 1904993) B1904993
theorem B1270007 : Blo 1268452 1270007 := bstep (se 1 (by rfl) ⟨952505, by rfl⟩ : syracuseStep 1270007 = 1905011) B1905011
theorem B1286411 : Blo 1268452 1286411 := bstep (se 1 (by rfl) ⟨964808, by rfl⟩ : syracuseStep 1286411 = 1929617) B1929617
theorem B1270027 : Blo 1268452 1270027 := bstep (se 1 (by rfl) ⟨952520, by rfl⟩ : syracuseStep 1270027 = 1905041) B1905041
theorem B1270039 : Blo 1268452 1270039 := bstep (se 1 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 1270039 = 1905059) B1905059
theorem B1270059 : Blo 1268452 1270059 := bstep (se 1 (by rfl) ⟨952544, by rfl⟩ : syracuseStep 1270059 = 1905089) B1905089
theorem B1270071 : Blo 1268452 1270071 := bstep (se 1 (by rfl) ⟨952553, by rfl⟩ : syracuseStep 1270071 = 1905107) B1905107
theorem B4284737 : Blo 1268452 4284737 := bstep (se 2 (by rfl) ⟨1606776, by rfl⟩ : syracuseStep 4284737 = 3213553) B3213553
theorem B2711873 : Blo 1268452 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B1270091 : Blo 1268452 1270091 := bstep (se 1 (by rfl) ⟨952568, by rfl⟩ : syracuseStep 1270091 = 1905137) B1905137
theorem B2408791 : Blo 1268452 2408791 := bstep (se 1 (by rfl) ⟨1806593, by rfl⟩ : syracuseStep 2408791 = 3613187) B3613187
theorem B3211609 : Blo 1268452 3211609 := bstep (se 2 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 3211609 = 2408707) B2408707
theorem B1270103 : Blo 1268452 1270103 := bstep (se 1 (by rfl) ⟨952577, by rfl⟩ : syracuseStep 1270103 = 1905155) B1905155
theorem B1270123 : Blo 1268452 1270123 := bstep (se 1 (by rfl) ⟨952592, by rfl⟩ : syracuseStep 1270123 = 1905185) B1905185
theorem B1270135 : Blo 1268452 1270135 := bstep (se 1 (by rfl) ⟨952601, by rfl⟩ : syracuseStep 1270135 = 1905203) B1905203
theorem B1270155 : Blo 1268452 1270155 := bstep (se 1 (by rfl) ⟨952616, by rfl⟩ : syracuseStep 1270155 = 1905233) B1905233
theorem B1270167 : Blo 1268452 1270167 := bstep (se 1 (by rfl) ⟨952625, by rfl⟩ : syracuseStep 1270167 = 1905251) B1905251
theorem B1270187 : Blo 1268452 1270187 := bstep (se 1 (by rfl) ⟨952640, by rfl⟩ : syracuseStep 1270187 = 1905281) B1905281
theorem B1270199 : Blo 1268452 1270199 := bstep (se 1 (by rfl) ⟨952649, by rfl⟩ : syracuseStep 1270199 = 1905299) B1905299
theorem B1270219 : Blo 1268452 1270219 := bstep (se 1 (by rfl) ⟨952664, by rfl⟩ : syracuseStep 1270219 = 1905329) B1905329
theorem B1270231 : Blo 1268452 1270231 := bstep (se 1 (by rfl) ⟨952673, by rfl⟩ : syracuseStep 1270231 = 1905347) B1905347
theorem B20595161 : Blo 1268452 20595161 := bstep (se 2 (by rfl) ⟨7723185, by rfl⟩ : syracuseStep 20595161 = 15446371) B15446371
theorem B4063709 : Blo 1268452 4063709 := bstep (se 3 (by rfl) ⟨761945, by rfl⟩ : syracuseStep 4063709 = 1523891) B1523891
theorem B1270251 : Blo 1268452 1270251 := bstep (se 1 (by rfl) ⟨952688, by rfl⟩ : syracuseStep 1270251 = 1905377) B1905377
theorem B1270263 : Blo 1268452 1270263 := bstep (se 1 (by rfl) ⟨952697, by rfl⟩ : syracuseStep 1270263 = 1905395) B1905395
theorem B1270283 : Blo 1268452 1270283 := bstep (se 1 (by rfl) ⟨952712, by rfl⟩ : syracuseStep 1270283 = 1905425) B1905425
theorem B1270295 : Blo 1268452 1270295 := bstep (se 1 (by rfl) ⟨952721, by rfl⟩ : syracuseStep 1270295 = 1905443) B1905443
theorem B1270315 : Blo 1268452 1270315 := bstep (se 1 (by rfl) ⟨952736, by rfl⟩ : syracuseStep 1270315 = 1905473) B1905473
theorem B2409011 : Blo 1268452 2409011 := bstep (se 1 (by rfl) ⟨1806758, by rfl⟩ : syracuseStep 2409011 = 3613517) B3613517
theorem B1270327 : Blo 1268452 1270327 := bstep (se 1 (by rfl) ⟨952745, by rfl⟩ : syracuseStep 1270327 = 1905491) B1905491
theorem B1270347 : Blo 1268452 1270347 := bstep (se 1 (by rfl) ⟨952760, by rfl⟩ : syracuseStep 1270347 = 1905521) B1905521
theorem B1270359 : Blo 1268452 1270359 := bstep (se 1 (by rfl) ⟨952769, by rfl⟩ : syracuseStep 1270359 = 1905539) B1905539
theorem B1270379 : Blo 1268452 1270379 := bstep (se 1 (by rfl) ⟨952784, by rfl⟩ : syracuseStep 1270379 = 1905569) B1905569
theorem B1270391 : Blo 1268452 1270391 := bstep (se 1 (by rfl) ⟨952793, by rfl⟩ : syracuseStep 1270391 = 1905587) B1905587
theorem B1270411 : Blo 1268452 1270411 := bstep (se 1 (by rfl) ⟨952808, by rfl⟩ : syracuseStep 1270411 = 1905617) B1905617
theorem B1270423 : Blo 1268452 1270423 := bstep (se 1 (by rfl) ⟨952817, by rfl⟩ : syracuseStep 1270423 = 1905635) B1905635
theorem B1270443 : Blo 1268452 1270443 := bstep (se 1 (by rfl) ⟨952832, by rfl⟩ : syracuseStep 1270443 = 1905665) B1905665
theorem B7324433 : Blo 1268452 7324433 := bstep (se 2 (by rfl) ⟨2746662, by rfl⟩ : syracuseStep 7324433 = 5493325) B5493325
theorem B2409239 : Blo 1268452 2409239 := bstep (se 1 (by rfl) ⟨1806929, by rfl⟩ : syracuseStep 2409239 = 3613859) B3613859
theorem B5145419 : Blo 1268452 5145419 := bstep (se 1 (by rfl) ⟨3859064, by rfl⟩ : syracuseStep 5145419 = 7718129) B7718129
theorem B1286987 : Blo 1268452 1286987 := bstep (se 1 (by rfl) ⟨965240, by rfl⟩ : syracuseStep 1286987 = 1930481) B1930481
theorem B6103883 : Blo 1268452 6103883 := bstep (se 1 (by rfl) ⟨4577912, by rfl⟩ : syracuseStep 6103883 = 9155825) B9155825
theorem B4285277 : Blo 1268452 4285277 := bstep (se 3 (by rfl) ⟨803489, by rfl⟩ : syracuseStep 4285277 = 1606979) B1606979
theorem B3613643 : Blo 1268452 3613643 := bstep (se 1 (by rfl) ⟨2710232, by rfl⟩ : syracuseStep 3613643 = 5420465) B5420465
theorem B2409497 : Blo 1268452 2409497 := bstep (se 2 (by rfl) ⟨903561, by rfl⟩ : syracuseStep 2409497 = 1807123) B1807123
theorem B6865985 : Blo 1268452 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B6186077 : Blo 1268452 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B3433565 : Blo 1268452 3433565 := bstep (se 3 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 3433565 = 1287587) B1287587
theorem B1606807 : Blo 1268452 1606807 := bstep (se 1 (by rfl) ⟨1205105, by rfl⟩ : syracuseStep 1606807 = 2410211) B2410211
theorem B4818113 : Blo 1268452 4818113 := bstep (se 2 (by rfl) ⟨1806792, by rfl⟩ : syracuseStep 4818113 = 3613585) B3613585
theorem B4572377 : Blo 1268452 4572377 := bstep (se 2 (by rfl) ⟨1714641, by rfl⟩ : syracuseStep 4572377 = 3429283) B3429283
theorem B3212723 : Blo 1268452 3212723 := bstep (se 1 (by rfl) ⟨2409542, by rfl⟩ : syracuseStep 3212723 = 4819085) B4819085
theorem B2409907 : Blo 1268452 2409907 := bstep (se 1 (by rfl) ⟨1807430, by rfl⟩ : syracuseStep 2409907 = 3614861) B3614861
theorem B2893313 : Blo 1268452 2893313 := bstep (se 2 (by rfl) ⟨1084992, by rfl⟩ : syracuseStep 2893313 = 2169985) B2169985
theorem B6424109 : Blo 1268452 6424109 := bstep (se 3 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 6424109 = 2409041) B2409041
theorem B11142731 : Blo 1268452 11142731 := bstep (se 1 (by rfl) ⟨8357048, by rfl⟩ : syracuseStep 11142731 = 16714097) B16714097
theorem B9643697 : Blo 1268452 9643697 := bstep (se 2 (by rfl) ⟨3616386, by rfl⟩ : syracuseStep 9643697 = 7232773) B7232773
theorem B3213017 : Blo 1268452 3213017 := bstep (se 2 (by rfl) ⟨1204881, by rfl⟩ : syracuseStep 3213017 = 2409763) B2409763
theorem B1427179 : Blo 1268452 1427179 := bstep (se 1 (by rfl) ⟨1070384, by rfl⟩ : syracuseStep 1427179 = 2140769) B2140769
theorem B5146391 : Blo 1268452 5146391 := bstep (se 1 (by rfl) ⟨3859793, by rfl⟩ : syracuseStep 5146391 = 7719587) B7719587
theorem B1427287 : Blo 1268452 1427287 := bstep (se 1 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 1427287 = 2140931) B2140931
theorem B2033495 : Blo 1268452 2033495 := bstep (se 1 (by rfl) ⟨1525121, by rfl⟩ : syracuseStep 2033495 = 3050243) B3050243
theorem B7718807 : Blo 1268452 7718807 := bstep (se 1 (by rfl) ⟨5789105, by rfl⟩ : syracuseStep 7718807 = 11578211) B11578211
theorem B2410393 : Blo 1268452 2410393 := bstep (se 2 (by rfl) ⟨903897, by rfl⟩ : syracuseStep 2410393 = 1807795) B1807795
theorem B7235507 : Blo 1268452 7235507 := bstep (se 1 (by rfl) ⟨5426630, by rfl⟩ : syracuseStep 7235507 = 10853261) B10853261
theorem B4286411 : Blo 1268452 4286411 := bstep (se 1 (by rfl) ⟨3214808, by rfl⟩ : syracuseStep 4286411 = 6429617) B6429617
theorem B1607627 : Blo 1268452 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B1427467 : Blo 1268452 1427467 := bstep (se 1 (by rfl) ⟨1070600, by rfl⟩ : syracuseStep 1427467 = 2141201) B2141201
theorem B6858827 : Blo 1268452 6858827 := bstep (se 1 (by rfl) ⟨5144120, by rfl⟩ : syracuseStep 6858827 = 10288241) B10288241
theorem B10840139 : Blo 1268452 10840139 := bstep (se 1 (by rfl) ⟨8130104, by rfl⟩ : syracuseStep 10840139 = 16260209) B16260209
theorem B7227467 : Blo 1268452 7227467 := bstep (se 1 (by rfl) ⟨5420600, by rfl⟩ : syracuseStep 7227467 = 10841201) B10841201
theorem B1427575 : Blo 1268452 1427575 := bstep (se 1 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 1427575 = 2141363) B2141363
theorem B1902731 : Blo 1268452 1902731 := bstep (se 1 (by rfl) ⟨1427048, by rfl⟩ : syracuseStep 1902731 = 2854097) B2854097
theorem B1902743 : Blo 1268452 1902743 := bstep (se 1 (by rfl) ⟨1427057, by rfl⟩ : syracuseStep 1902743 = 2854115) B2854115
theorem B9644183 : Blo 1268452 9644183 := bstep (se 1 (by rfl) ⟨7233137, by rfl⟩ : syracuseStep 9644183 = 14466275) B14466275
theorem B1902809 : Blo 1268452 1902809 := bstep (se 2 (by rfl) ⟨713553, by rfl⟩ : syracuseStep 1902809 = 1427107) B1427107
theorem B4286681 : Blo 1268452 4286681 := bstep (se 2 (by rfl) ⟨1607505, by rfl⟩ : syracuseStep 4286681 = 3215011) B3215011
theorem B15444229 : Blo 1268452 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B3049751 : Blo 1268452 3049751 := bstep (se 1 (by rfl) ⟨2287313, by rfl⟩ : syracuseStep 3049751 = 4574627) B4574627
theorem B1427755 : Blo 1268452 1427755 := bstep (se 1 (by rfl) ⟨1070816, by rfl⟩ : syracuseStep 1427755 = 2141633) B2141633
theorem B5785931 : Blo 1268452 5785931 := bstep (se 1 (by rfl) ⟨4339448, by rfl⟩ : syracuseStep 5785931 = 8678897) B8678897
theorem B1902923 : Blo 1268452 1902923 := bstep (se 1 (by rfl) ⟨1427192, by rfl⟩ : syracuseStep 1902923 = 2854385) B2854385
theorem B1902935 : Blo 1268452 1902935 := bstep (se 1 (by rfl) ⟨1427201, by rfl⟩ : syracuseStep 1902935 = 2854403) B2854403
theorem B10848613 : Blo 1268452 10848613 := bstep (se 4 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 10848613 = 2034115) B2034115
theorem B1427863 : Blo 1268452 1427863 := bstep (se 1 (by rfl) ⟨1070897, by rfl⟩ : syracuseStep 1427863 = 2141795) B2141795
theorem B1903001 : Blo 1268452 1903001 := bstep (se 2 (by rfl) ⟨713625, by rfl⟩ : syracuseStep 1903001 = 1427251) B1427251
theorem B9152945 : Blo 1268452 9152945 := bstep (se 2 (by rfl) ⟨3432354, by rfl⟩ : syracuseStep 9152945 = 6864709) B6864709
theorem B2410955 : Blo 1268452 2410955 := bstep (se 1 (by rfl) ⟨1808216, by rfl⟩ : syracuseStep 2410955 = 3616433) B3616433
theorem B1903115 : Blo 1268452 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B82356749 : Blo 1268452 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B5220881 : Blo 1268452 5220881 := bstep (se 2 (by rfl) ⟨1957830, by rfl⟩ : syracuseStep 5220881 = 3915661) B3915661
theorem B1903127 : Blo 1268452 1903127 := bstep (se 1 (by rfl) ⟨1427345, by rfl⟩ : syracuseStep 1903127 = 2854691) B2854691
theorem B4885037 : Blo 1268452 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B2574899 : Blo 1268452 2574899 := bstep (se 1 (by rfl) ⟨1931174, by rfl⟩ : syracuseStep 2574899 = 3862349) B3862349
theorem B1428043 : Blo 1268452 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B1903193 : Blo 1268452 1903193 := bstep (se 2 (by rfl) ⟨713697, by rfl⟩ : syracuseStep 1903193 = 1427395) B1427395
theorem B2411137 : Blo 1268452 2411137 := bstep (se 2 (by rfl) ⟨904176, by rfl⟩ : syracuseStep 2411137 = 1808353) B1808353
theorem B4819601 : Blo 1268452 4819601 := bstep (se 2 (by rfl) ⟨1807350, by rfl⟩ : syracuseStep 4819601 = 3614701) B3614701
theorem B2140823 : Blo 1268452 2140823 := bstep (se 1 (by rfl) ⟨1605617, by rfl⟩ : syracuseStep 2140823 = 3211235) B3211235
theorem B1428151 : Blo 1268452 1428151 := bstep (se 1 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 1428151 = 2142227) B2142227
theorem B1903307 : Blo 1268452 1903307 := bstep (se 1 (by rfl) ⟨1427480, by rfl⟩ : syracuseStep 1903307 = 2854961) B2854961
theorem B1903319 : Blo 1268452 1903319 := bstep (se 1 (by rfl) ⟨1427489, by rfl⟩ : syracuseStep 1903319 = 2854979) B2854979
theorem B2140951 : Blo 1268452 2140951 := bstep (se 1 (by rfl) ⟨1605713, by rfl⟩ : syracuseStep 2140951 = 3211427) B3211427
theorem B1903385 : Blo 1268452 1903385 := bstep (se 2 (by rfl) ⟨713769, by rfl⟩ : syracuseStep 1903385 = 1427539) B1427539
theorem B1428331 : Blo 1268452 1428331 := bstep (se 1 (by rfl) ⟨1071248, by rfl⟩ : syracuseStep 1428331 = 2142497) B2142497
theorem B1903499 : Blo 1268452 1903499 := bstep (se 1 (by rfl) ⟨1427624, by rfl⟩ : syracuseStep 1903499 = 2855249) B2855249
theorem B2034571 : Blo 1268452 2034571 := bstep (se 1 (by rfl) ⟨1525928, by rfl⟩ : syracuseStep 2034571 = 3051857) B3051857
theorem B1903511 : Blo 1268452 1903511 := bstep (se 1 (by rfl) ⟨1427633, by rfl⟩ : syracuseStep 1903511 = 2855267) B2855267
theorem B4287383 : Blo 1268452 4287383 := bstep (se 1 (by rfl) ⟨3215537, by rfl⟩ : syracuseStep 4287383 = 6431075) B6431075
theorem B2894771 : Blo 1268452 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B1428439 : Blo 1268452 1428439 := bstep (se 1 (by rfl) ⟨1071329, by rfl⟩ : syracuseStep 1428439 = 2142659) B2142659
theorem B1903577 : Blo 1268452 1903577 := bstep (se 2 (by rfl) ⟨713841, by rfl⟩ : syracuseStep 1903577 = 1427683) B1427683
theorem B1715161 : Blo 1268452 1715161 := bstep (se 2 (by rfl) ⟨643185, by rfl⟩ : syracuseStep 1715161 = 1286371) B1286371
theorem B8137745 : Blo 1268452 8137745 := bstep (se 2 (by rfl) ⟨3051654, by rfl⟩ : syracuseStep 8137745 = 6103309) B6103309
theorem B1903691 : Blo 1268452 1903691 := bstep (se 1 (by rfl) ⟨1427768, by rfl⟩ : syracuseStep 1903691 = 2855537) B2855537
theorem B1903703 : Blo 1268452 1903703 := bstep (se 1 (by rfl) ⟨1427777, by rfl⟩ : syracuseStep 1903703 = 2855555) B2855555
theorem B4820057 : Blo 1268452 4820057 := bstep (se 2 (by rfl) ⟨1807521, by rfl⟩ : syracuseStep 4820057 = 3615043) B3615043
theorem B6868061 : Blo 1268452 6868061 := bstep (se 3 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 6868061 = 2575523) B2575523
theorem B4574339 : Blo 1268452 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B8244355 : Blo 1268452 8244355 := bstep (se 1 (by rfl) ⟨6183266, by rfl⟩ : syracuseStep 8244355 = 12366533) B12366533
theorem B1428619 : Blo 1268452 1428619 := bstep (se 1 (by rfl) ⟨1071464, by rfl⟩ : syracuseStep 1428619 = 2142929) B2142929
theorem B1903769 : Blo 1268452 1903769 := bstep (se 2 (by rfl) ⟨713913, by rfl⟩ : syracuseStep 1903769 = 1427827) B1427827
theorem B1428727 : Blo 1268452 1428727 := bstep (se 1 (by rfl) ⟨1071545, by rfl⟩ : syracuseStep 1428727 = 2143091) B2143091
theorem B1903883 : Blo 1268452 1903883 := bstep (se 1 (by rfl) ⟨1427912, by rfl⟩ : syracuseStep 1903883 = 2855825) B2855825
theorem B1903895 : Blo 1268452 1903895 := bstep (se 1 (by rfl) ⟨1427921, by rfl⟩ : syracuseStep 1903895 = 2855843) B2855843
theorem B2854169 : Blo 1268452 2854169 := bstep (se 2 (by rfl) ⟨1070313, by rfl⟩ : syracuseStep 2854169 = 2140627) B2140627
theorem B10849571 : Blo 1268452 10849571 := bstep (se 1 (by rfl) ⟨8137178, by rfl⟩ : syracuseStep 10849571 = 16274357) B16274357
theorem B4820269 : Blo 1268452 4820269 := bstep (se 3 (by rfl) ⟨903800, by rfl⟩ : syracuseStep 4820269 = 1807601) B1807601
theorem B3214667 : Blo 1268452 3214667 := bstep (se 1 (by rfl) ⟨2411000, by rfl⟩ : syracuseStep 3214667 = 4822001) B4822001
theorem B2411851 : Blo 1268452 2411851 := bstep (se 1 (by rfl) ⟨1808888, by rfl⟩ : syracuseStep 2411851 = 3617777) B3617777
theorem B1903961 : Blo 1268452 1903961 := bstep (se 2 (by rfl) ⟨713985, by rfl⟩ : syracuseStep 1903961 = 1427971) B1427971
theorem B2854259 : Blo 1268452 2854259 := bstep (se 1 (by rfl) ⟨2140694, by rfl⟩ : syracuseStep 2854259 = 4281389) B4281389
theorem B2141579 : Blo 1268452 2141579 := bstep (se 1 (by rfl) ⟨1606184, by rfl⟩ : syracuseStep 2141579 = 3212369) B3212369
theorem B2854295 : Blo 1268452 2854295 := bstep (se 1 (by rfl) ⟨2140721, by rfl⟩ : syracuseStep 2854295 = 4281443) B4281443
theorem B7720343 : Blo 1268452 7720343 := bstep (se 1 (by rfl) ⟨5790257, by rfl⟩ : syracuseStep 7720343 = 11580515) B11580515
theorem B1428907 : Blo 1268452 1428907 := bstep (se 1 (by rfl) ⟨1071680, by rfl⟩ : syracuseStep 1428907 = 2143361) B2143361
theorem B1904075 : Blo 1268452 1904075 := bstep (se 1 (by rfl) ⟨1428056, by rfl⟩ : syracuseStep 1904075 = 2856113) B2856113
theorem B1904087 : Blo 1268452 1904087 := bstep (se 1 (by rfl) ⟨1428065, by rfl⟩ : syracuseStep 1904087 = 2856131) B2856131
theorem B2141707 : Blo 1268452 2141707 := bstep (se 1 (by rfl) ⟨1606280, by rfl⟩ : syracuseStep 2141707 = 3212561) B3212561
theorem B1355287 : Blo 1268452 1355287 := bstep (se 1 (by rfl) ⟨1016465, by rfl⟩ : syracuseStep 1355287 = 2032931) B2032931
theorem B1429015 : Blo 1268452 1429015 := bstep (se 1 (by rfl) ⟨1071761, by rfl⟩ : syracuseStep 1429015 = 2143523) B2143523
theorem B1928729 : Blo 1268452 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B1904153 : Blo 1268452 1904153 := bstep (se 2 (by rfl) ⟨714057, by rfl⟩ : syracuseStep 1904153 = 1428115) B1428115
theorem B2854475 : Blo 1268452 2854475 := bstep (se 1 (by rfl) ⟨2140856, by rfl⟩ : syracuseStep 2854475 = 4281713) B4281713
theorem B2289239 : Blo 1268452 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B4820573 : Blo 1268452 4820573 := bstep (se 3 (by rfl) ⟨903857, by rfl⟩ : syracuseStep 4820573 = 1807715) B1807715
theorem B2854529 : Blo 1268452 2854529 := bstep (se 2 (by rfl) ⟨1070448, by rfl⟩ : syracuseStep 2854529 = 2140897) B2140897
theorem B1904267 : Blo 1268452 1904267 := bstep (se 1 (by rfl) ⟨1428200, by rfl⟩ : syracuseStep 1904267 = 2856401) B2856401
theorem B1904279 : Blo 1268452 1904279 := bstep (se 1 (by rfl) ⟨1428209, by rfl⟩ : syracuseStep 1904279 = 2856419) B2856419
theorem B2141849 : Blo 1268452 2141849 := bstep (se 2 (by rfl) ⟨803193, by rfl⟩ : syracuseStep 2141849 = 1606387) B1606387
theorem B1429195 : Blo 1268452 1429195 := bstep (se 1 (by rfl) ⟨1071896, by rfl⟩ : syracuseStep 1429195 = 2143793) B2143793
theorem B1904345 : Blo 1268452 1904345 := bstep (se 2 (by rfl) ⟨714129, by rfl⟩ : syracuseStep 1904345 = 1428259) B1428259
theorem B20598533 : Blo 1268452 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B2141977 : Blo 1268452 2141977 := bstep (se 2 (by rfl) ⟨803241, by rfl⟩ : syracuseStep 2141977 = 1606483) B1606483
theorem B5148467 : Blo 1268452 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B27430721 : Blo 1268452 27430721 := bstep (se 2 (by rfl) ⟨10286520, by rfl⟩ : syracuseStep 27430721 = 20573041) B20573041
theorem B1904459 : Blo 1268452 1904459 := bstep (se 1 (by rfl) ⟨1428344, by rfl⟩ : syracuseStep 1904459 = 2856689) B2856689
theorem B1904471 : Blo 1268452 1904471 := bstep (se 1 (by rfl) ⟨1428353, by rfl⟩ : syracuseStep 1904471 = 2856707) B2856707
theorem B2854745 : Blo 1268452 2854745 := bstep (se 2 (by rfl) ⟨1070529, by rfl⟩ : syracuseStep 2854745 = 2141059) B2141059
theorem B1929113 : Blo 1268452 1929113 := bstep (se 2 (by rfl) ⟨723417, by rfl⟩ : syracuseStep 1929113 = 1446835) B1446835
theorem B1904537 : Blo 1268452 1904537 := bstep (se 2 (by rfl) ⟨714201, by rfl⟩ : syracuseStep 1904537 = 1428403) B1428403
theorem B2854835 : Blo 1268452 2854835 := bstep (se 1 (by rfl) ⟨2141126, by rfl⟩ : syracuseStep 2854835 = 4282253) B4282253
theorem B16273331 : Blo 1268452 16273331 := bstep (se 1 (by rfl) ⟨12204998, by rfl⟩ : syracuseStep 16273331 = 24409997) B24409997
theorem B2854871 : Blo 1268452 2854871 := bstep (se 1 (by rfl) ⟨2141153, by rfl⟩ : syracuseStep 2854871 = 4282307) B4282307
theorem B1355735 : Blo 1268452 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B1904651 : Blo 1268452 1904651 := bstep (se 1 (by rfl) ⟨1428488, by rfl⟩ : syracuseStep 1904651 = 2856977) B2856977
theorem B1904663 : Blo 1268452 1904663 := bstep (se 1 (by rfl) ⟨1428497, by rfl⟩ : syracuseStep 1904663 = 2856995) B2856995
theorem B1904729 : Blo 1268452 1904729 := bstep (se 2 (by rfl) ⟨714273, by rfl⟩ : syracuseStep 1904729 = 1428547) B1428547
theorem B2855051 : Blo 1268452 2855051 := bstep (se 1 (by rfl) ⟨2141288, by rfl⟩ : syracuseStep 2855051 = 4282577) B4282577
theorem B2855105 : Blo 1268452 2855105 := bstep (se 2 (by rfl) ⟨1070664, by rfl⟩ : syracuseStep 2855105 = 2141329) B2141329
theorem B1904843 : Blo 1268452 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B1904855 : Blo 1268452 1904855 := bstep (se 1 (by rfl) ⟨1428641, by rfl⟩ : syracuseStep 1904855 = 2857283) B2857283
theorem B1806553 : Blo 1268452 1806553 := bstep (se 2 (by rfl) ⟨677457, by rfl⟩ : syracuseStep 1806553 = 1354915) B1354915
theorem B3215639 : Blo 1268452 3215639 := bstep (se 1 (by rfl) ⟨2411729, by rfl⟩ : syracuseStep 3215639 = 4823459) B4823459
theorem B1904921 : Blo 1268452 1904921 := bstep (se 2 (by rfl) ⟨714345, by rfl⟩ : syracuseStep 1904921 = 1428691) B1428691
theorem B1356107 : Blo 1268452 1356107 := bstep (se 1 (by rfl) ⟨1017080, by rfl⟩ : syracuseStep 1356107 = 2034161) B2034161
theorem B2142551 : Blo 1268452 2142551 := bstep (se 1 (by rfl) ⟨1606913, by rfl⟩ : syracuseStep 2142551 = 3213827) B3213827
theorem B3051865 : Blo 1268452 3051865 := bstep (se 2 (by rfl) ⟨1144449, by rfl⟩ : syracuseStep 3051865 = 2288899) B2288899
theorem B1905035 : Blo 1268452 1905035 := bstep (se 1 (by rfl) ⟨1428776, by rfl⟩ : syracuseStep 1905035 = 2857553) B2857553
theorem B1905047 : Blo 1268452 1905047 := bstep (se 1 (by rfl) ⟨1428785, by rfl⟩ : syracuseStep 1905047 = 2857571) B2857571
theorem B2855321 : Blo 1268452 2855321 := bstep (se 2 (by rfl) ⟨1070745, by rfl⟩ : syracuseStep 2855321 = 2141491) B2141491
theorem B2142679 : Blo 1268452 2142679 := bstep (se 1 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 2142679 = 3214019) B3214019
theorem B1905113 : Blo 1268452 1905113 := bstep (se 2 (by rfl) ⟨714417, by rfl⟩ : syracuseStep 1905113 = 1428835) B1428835
theorem B2855411 : Blo 1268452 2855411 := bstep (se 1 (by rfl) ⟨2141558, by rfl⟩ : syracuseStep 2855411 = 4283117) B4283117
theorem B5419523 : Blo 1268452 5419523 := bstep (se 1 (by rfl) ⟨4064642, by rfl⟩ : syracuseStep 5419523 = 8129285) B8129285
theorem B2855447 : Blo 1268452 2855447 := bstep (se 1 (by rfl) ⟨2141585, by rfl⟩ : syracuseStep 2855447 = 4283171) B4283171
theorem B1716761 : Blo 1268452 1716761 := bstep (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) B1287571
theorem B9146945 : Blo 1268452 9146945 := bstep (se 2 (by rfl) ⟨3430104, by rfl⟩ : syracuseStep 9146945 = 6860209) B6860209
theorem B1905227 : Blo 1268452 1905227 := bstep (se 1 (by rfl) ⟨1428920, by rfl⟩ : syracuseStep 1905227 = 2857841) B2857841
theorem B1905239 : Blo 1268452 1905239 := bstep (se 1 (by rfl) ⟨1428929, by rfl⟩ : syracuseStep 1905239 = 2857859) B2857859
theorem B1905305 : Blo 1268452 1905305 := bstep (se 2 (by rfl) ⟨714489, by rfl⟩ : syracuseStep 1905305 = 1428979) B1428979
theorem B7230131 : Blo 1268452 7230131 := bstep (se 1 (by rfl) ⟨5422598, by rfl⟩ : syracuseStep 7230131 = 10845197) B10845197
theorem B2855627 : Blo 1268452 2855627 := bstep (se 1 (by rfl) ⟨2141720, by rfl⟩ : syracuseStep 2855627 = 4283441) B4283441
theorem B4125401 : Blo 1268452 4125401 := bstep (se 2 (by rfl) ⟨1547025, by rfl⟩ : syracuseStep 4125401 = 3094051) B3094051
theorem B2855681 : Blo 1268452 2855681 := bstep (se 2 (by rfl) ⟨1070880, by rfl⟩ : syracuseStep 2855681 = 2141761) B2141761
theorem B1905419 : Blo 1268452 1905419 := bstep (se 1 (by rfl) ⟨1429064, by rfl⟩ : syracuseStep 1905419 = 2858129) B2858129
theorem B1930007 : Blo 1268452 1930007 := bstep (se 1 (by rfl) ⟨1447505, by rfl⟩ : syracuseStep 1930007 = 2895011) B2895011
theorem B1905431 : Blo 1268452 1905431 := bstep (se 1 (by rfl) ⟨1429073, by rfl⟩ : syracuseStep 1905431 = 2858147) B2858147
theorem B5419865 : Blo 1268452 5419865 := bstep (se 2 (by rfl) ⟨2032449, by rfl⟩ : syracuseStep 5419865 = 4064899) B4064899
theorem B1905497 : Blo 1268452 1905497 := bstep (se 2 (by rfl) ⟨714561, by rfl⟩ : syracuseStep 1905497 = 1429123) B1429123
theorem B4281281 : Blo 1268452 4281281 := bstep (se 2 (by rfl) ⟨1605480, by rfl⟩ : syracuseStep 4281281 = 3210961) B3210961
theorem B1905611 : Blo 1268452 1905611 := bstep (se 1 (by rfl) ⟨1429208, by rfl⟩ : syracuseStep 1905611 = 2858417) B2858417
theorem B1905623 : Blo 1268452 1905623 := bstep (se 1 (by rfl) ⟨1429217, by rfl⟩ : syracuseStep 1905623 = 2858435) B2858435
theorem B2855897 : Blo 1268452 2855897 := bstep (se 2 (by rfl) ⟨1070961, by rfl⟩ : syracuseStep 2855897 = 2141923) B2141923
theorem B2855987 : Blo 1268452 2855987 := bstep (se 1 (by rfl) ⟨2141990, by rfl⟩ : syracuseStep 2855987 = 4283981) B4283981
theorem B2143307 : Blo 1268452 2143307 := bstep (se 1 (by rfl) ⟨1607480, by rfl⟩ : syracuseStep 2143307 = 3214961) B3214961
theorem B2856023 : Blo 1268452 2856023 := bstep (se 1 (by rfl) ⟨2142017, by rfl⟩ : syracuseStep 2856023 = 4284035) B4284035
theorem B2143435 : Blo 1268452 2143435 := bstep (se 1 (by rfl) ⟨1607576, by rfl⟩ : syracuseStep 2143435 = 3215153) B3215153
theorem B14456069 : Blo 1268452 14456069 := bstep (se 4 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 14456069 = 2710513) B2710513
theorem B2856203 : Blo 1268452 2856203 := bstep (se 1 (by rfl) ⟨2142152, by rfl⟩ : syracuseStep 2856203 = 4284305) B4284305
theorem B2856257 : Blo 1268452 2856257 := bstep (se 2 (by rfl) ⟨1071096, by rfl⟩ : syracuseStep 2856257 = 2142193) B2142193
theorem B2143577 : Blo 1268452 2143577 := bstep (se 2 (by rfl) ⟨803841, by rfl⟩ : syracuseStep 2143577 = 1607683) B1607683
theorem B6427997 : Blo 1268452 6427997 := bstep (se 3 (by rfl) ⟨1205249, by rfl⟩ : syracuseStep 6427997 = 2410499) B2410499
theorem B164746709 : Blo 1268452 164746709 := bstep (se 7 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 164746709 = 3861251) B3861251
theorem B2143705 : Blo 1268452 2143705 := bstep (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) B1607779
theorem B4281821 : Blo 1268452 4281821 := bstep (se 3 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 4281821 = 1605683) B1605683
theorem B36599309 : Blo 1268452 36599309 := bstep (se 3 (by rfl) ⟨6862370, by rfl⟩ : syracuseStep 36599309 = 13724741) B13724741
theorem B3429911 : Blo 1268452 3429911 := bstep (se 1 (by rfl) ⟨2572433, by rfl⟩ : syracuseStep 3429911 = 5144867) B5144867
theorem B2856473 : Blo 1268452 2856473 := bstep (se 2 (by rfl) ⟨1071177, by rfl⟩ : syracuseStep 2856473 = 2142355) B2142355
theorem B2856563 : Blo 1268452 2856563 := bstep (se 1 (by rfl) ⟨2142422, by rfl⟩ : syracuseStep 2856563 = 4284845) B4284845
theorem B1808011 : Blo 1268452 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B2856599 : Blo 1268452 2856599 := bstep (se 1 (by rfl) ⟨2142449, by rfl⟩ : syracuseStep 2856599 = 4284899) B4284899
theorem B1808023 : Blo 1268452 1808023 := bstep (se 1 (by rfl) ⟨1356017, by rfl⟩ : syracuseStep 1808023 = 2712035) B2712035
theorem B6518489 : Blo 1268452 6518489 := bstep (se 2 (by rfl) ⟨2444433, by rfl⟩ : syracuseStep 6518489 = 4888867) B4888867
theorem B46970609 : Blo 1268452 46970609 := bstep (se 2 (by rfl) ⟨17613978, by rfl⟩ : syracuseStep 46970609 = 35227957) B35227957
theorem B2856779 : Blo 1268452 2856779 := bstep (se 1 (by rfl) ⟨2142584, by rfl⟩ : syracuseStep 2856779 = 4285169) B4285169
theorem B2856833 : Blo 1268452 2856833 := bstep (se 2 (by rfl) ⟨1071312, by rfl⟩ : syracuseStep 2856833 = 2142625) B2142625
theorem B19527641 : Blo 1268452 19527641 := bstep (se 2 (by rfl) ⟨7322865, by rfl⟩ : syracuseStep 19527641 = 14645731) B14645731
theorem B2857049 : Blo 1268452 2857049 := bstep (se 2 (by rfl) ⟨1071393, by rfl⟩ : syracuseStep 2857049 = 2142787) B2142787
theorem B7231589 : Blo 1268452 7231589 := bstep (se 4 (by rfl) ⟨677961, by rfl⟩ : syracuseStep 7231589 = 1355923) B1355923
theorem B4823171 : Blo 1268452 4823171 := bstep (se 1 (by rfl) ⟨3617378, by rfl⟩ : syracuseStep 4823171 = 7234757) B7234757
theorem B4823185 : Blo 1268452 4823185 := bstep (se 2 (by rfl) ⟨1808694, by rfl⟩ : syracuseStep 4823185 = 3617389) B3617389
theorem B2857139 : Blo 1268452 2857139 := bstep (se 1 (by rfl) ⟨2142854, by rfl⟩ : syracuseStep 2857139 = 4285709) B4285709
theorem B1718489 : Blo 1268452 1718489 := bstep (se 2 (by rfl) ⟨644433, by rfl⟩ : syracuseStep 1718489 = 1288867) B1288867
theorem B2857175 : Blo 1268452 2857175 := bstep (se 1 (by rfl) ⟨2142881, by rfl⟩ : syracuseStep 2857175 = 4285763) B4285763
theorem B2857355 : Blo 1268452 2857355 := bstep (se 1 (by rfl) ⟨2143016, by rfl⟩ : syracuseStep 2857355 = 4286033) B4286033
theorem B5421505 : Blo 1268452 5421505 := bstep (se 2 (by rfl) ⟨2033064, by rfl⟩ : syracuseStep 5421505 = 4066129) B4066129
theorem B2857409 : Blo 1268452 2857409 := bstep (se 2 (by rfl) ⟨1071528, by rfl⟩ : syracuseStep 2857409 = 2143057) B2143057
theorem B4823489 : Blo 1268452 4823489 := bstep (se 2 (by rfl) ⟨1808808, by rfl⟩ : syracuseStep 4823489 = 3617617) B3617617
theorem B2710027 : Blo 1268452 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B18307619 : Blo 1268452 18307619 := bstep (se 1 (by rfl) ⟨13730714, by rfl⟩ : syracuseStep 18307619 = 27461429) B27461429
theorem B4340299 : Blo 1268452 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B4282955 : Blo 1268452 4282955 := bstep (se 1 (by rfl) ⟨3212216, by rfl⟩ : syracuseStep 4282955 = 6424433) B6424433
theorem B2710103 : Blo 1268452 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B2857625 : Blo 1268452 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B1268459 : Blo 1268452 1268459 := bstep (se 1 (by rfl) ⟨951344, by rfl⟩ : syracuseStep 1268459 = 1902689) B1902689
theorem B2857715 : Blo 1268452 2857715 := bstep (se 1 (by rfl) ⟨2143286, by rfl⟩ : syracuseStep 2857715 = 4286573) B4286573
theorem B1268471 : Blo 1268452 1268471 := bstep (se 1 (by rfl) ⟨951353, by rfl⟩ : syracuseStep 1268471 = 1902707) B1902707
theorem B1268491 : Blo 1268452 1268491 := bstep (se 1 (by rfl) ⟨951368, by rfl⟩ : syracuseStep 1268491 = 1902737) B1902737
theorem B7232273 : Blo 1268452 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B1268503 : Blo 1268452 1268503 := bstep (se 1 (by rfl) ⟨951377, by rfl⟩ : syracuseStep 1268503 = 1902755) B1902755
theorem B2857751 : Blo 1268452 2857751 := bstep (se 1 (by rfl) ⟨2143313, by rfl⟩ : syracuseStep 2857751 = 4286627) B4286627
theorem B1268523 : Blo 1268452 1268523 := bstep (se 1 (by rfl) ⟨951392, by rfl⟩ : syracuseStep 1268523 = 1902785) B1902785
theorem B3259187 : Blo 1268452 3259187 := bstep (se 1 (by rfl) ⟨2444390, by rfl⟩ : syracuseStep 3259187 = 4888781) B4888781
theorem B1268535 : Blo 1268452 1268535 := bstep (se 1 (by rfl) ⟨951401, by rfl⟩ : syracuseStep 1268535 = 1902803) B1902803
theorem B39623489 : Blo 1268452 39623489 := bstep (se 2 (by rfl) ⟨14858808, by rfl⟩ : syracuseStep 39623489 = 29717617) B29717617
theorem B1268555 : Blo 1268452 1268555 := bstep (se 1 (by rfl) ⟨951416, by rfl⟩ : syracuseStep 1268555 = 1902833) B1902833
theorem B1268567 : Blo 1268452 1268567 := bstep (se 1 (by rfl) ⟨951425, by rfl⟩ : syracuseStep 1268567 = 1902851) B1902851
theorem B4283225 : Blo 1268452 4283225 := bstep (se 2 (by rfl) ⟨1606209, by rfl⟩ : syracuseStep 4283225 = 3212419) B3212419
theorem B1268587 : Blo 1268452 1268587 := bstep (se 1 (by rfl) ⟨951440, by rfl⟩ : syracuseStep 1268587 = 1902881) B1902881
theorem B1268599 : Blo 1268452 1268599 := bstep (se 1 (by rfl) ⟨951449, by rfl⟩ : syracuseStep 1268599 = 1902899) B1902899
theorem B1268619 : Blo 1268452 1268619 := bstep (se 1 (by rfl) ⟨951464, by rfl⟩ : syracuseStep 1268619 = 1902929) B1902929
theorem B1268631 : Blo 1268452 1268631 := bstep (se 1 (by rfl) ⟨951473, by rfl⟩ : syracuseStep 1268631 = 1902947) B1902947
theorem B1268651 : Blo 1268452 1268651 := bstep (se 1 (by rfl) ⟨951488, by rfl⟩ : syracuseStep 1268651 = 1902977) B1902977
theorem B1268663 : Blo 1268452 1268663 := bstep (se 1 (by rfl) ⟨951497, by rfl⟩ : syracuseStep 1268663 = 1902995) B1902995
theorem B1268683 : Blo 1268452 1268683 := bstep (se 1 (by rfl) ⟨951512, by rfl⟩ : syracuseStep 1268683 = 1903025) B1903025
theorem B2857931 : Blo 1268452 2857931 := bstep (se 1 (by rfl) ⟨2143448, by rfl⟩ : syracuseStep 2857931 = 4286897) B4286897
theorem B1268695 : Blo 1268452 1268695 := bstep (se 1 (by rfl) ⟨951521, by rfl⟩ : syracuseStep 1268695 = 1903043) B1903043
theorem B1268715 : Blo 1268452 1268715 := bstep (se 1 (by rfl) ⟨951536, by rfl⟩ : syracuseStep 1268715 = 1903073) B1903073
theorem B1268727 : Blo 1268452 1268727 := bstep (se 1 (by rfl) ⟨951545, by rfl⟩ : syracuseStep 1268727 = 1903091) B1903091
theorem B2857985 : Blo 1268452 2857985 := bstep (se 2 (by rfl) ⟨1071744, by rfl⟩ : syracuseStep 2857985 = 2143489) B2143489
theorem B1268747 : Blo 1268452 1268747 := bstep (se 1 (by rfl) ⟨951560, by rfl⟩ : syracuseStep 1268747 = 1903121) B1903121
theorem B1268759 : Blo 1268452 1268759 := bstep (se 1 (by rfl) ⟨951569, by rfl⟩ : syracuseStep 1268759 = 1903139) B1903139
theorem B1268779 : Blo 1268452 1268779 := bstep (se 1 (by rfl) ⟨951584, by rfl⟩ : syracuseStep 1268779 = 1903169) B1903169
theorem B5217331 : Blo 1268452 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B1268791 : Blo 1268452 1268791 := bstep (se 1 (by rfl) ⟨951593, by rfl⟩ : syracuseStep 1268791 = 1903187) B1903187
theorem B1268811 : Blo 1268452 1268811 := bstep (se 1 (by rfl) ⟨951608, by rfl⟩ : syracuseStep 1268811 = 1903217) B1903217
theorem B16710731 : Blo 1268452 16710731 := bstep (se 1 (by rfl) ⟨12533048, by rfl⟩ : syracuseStep 16710731 = 25066097) B25066097
theorem B16268363 : Blo 1268452 16268363 := bstep (se 1 (by rfl) ⟨12201272, by rfl⟩ : syracuseStep 16268363 = 24402545) B24402545
theorem B1268823 : Blo 1268452 1268823 := bstep (se 1 (by rfl) ⟨951617, by rfl⟩ : syracuseStep 1268823 = 1903235) B1903235
theorem B1268843 : Blo 1268452 1268843 := bstep (se 1 (by rfl) ⟨951632, by rfl⟩ : syracuseStep 1268843 = 1903265) B1903265
theorem B1268855 : Blo 1268452 1268855 := bstep (se 1 (by rfl) ⟨951641, by rfl⟩ : syracuseStep 1268855 = 1903283) B1903283
theorem B14097539 : Blo 1268452 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B1268875 : Blo 1268452 1268875 := bstep (se 1 (by rfl) ⟨951656, by rfl⟩ : syracuseStep 1268875 = 1903313) B1903313
theorem B1268887 : Blo 1268452 1268887 := bstep (se 1 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 1268887 = 1903331) B1903331
theorem B1268907 : Blo 1268452 1268907 := bstep (se 1 (by rfl) ⟨951680, by rfl⟩ : syracuseStep 1268907 = 1903361) B1903361
theorem B1268919 : Blo 1268452 1268919 := bstep (se 1 (by rfl) ⟨951689, by rfl⟩ : syracuseStep 1268919 = 1903379) B1903379
theorem B1268939 : Blo 1268452 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1268951 : Blo 1268452 1268951 := bstep (se 1 (by rfl) ⟨951713, by rfl⟩ : syracuseStep 1268951 = 1903427) B1903427
theorem B2858201 : Blo 1268452 2858201 := bstep (se 2 (by rfl) ⟨1071825, by rfl⟩ : syracuseStep 2858201 = 2143651) B2143651
theorem B1268971 : Blo 1268452 1268971 := bstep (se 1 (by rfl) ⟨951728, by rfl⟩ : syracuseStep 1268971 = 1903457) B1903457
theorem B1268983 : Blo 1268452 1268983 := bstep (se 1 (by rfl) ⟨951737, by rfl⟩ : syracuseStep 1268983 = 1903475) B1903475
theorem B1269003 : Blo 1268452 1269003 := bstep (se 1 (by rfl) ⟨951752, by rfl⟩ : syracuseStep 1269003 = 1903505) B1903505
theorem B1269015 : Blo 1268452 1269015 := bstep (se 1 (by rfl) ⟨951761, by rfl⟩ : syracuseStep 1269015 = 1903523) B1903523
theorem B1269035 : Blo 1268452 1269035 := bstep (se 1 (by rfl) ⟨951776, by rfl⟩ : syracuseStep 1269035 = 1903553) B1903553
theorem B2858291 : Blo 1268452 2858291 := bstep (se 1 (by rfl) ⟨2143718, by rfl⟩ : syracuseStep 2858291 = 4287437) B4287437
theorem B1269047 : Blo 1268452 1269047 := bstep (se 1 (by rfl) ⟨951785, by rfl⟩ : syracuseStep 1269047 = 1903571) B1903571
theorem B1269067 : Blo 1268452 1269067 := bstep (se 1 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 1269067 = 1903601) B1903601
theorem B2170199 : Blo 1268452 2170199 := bstep (se 1 (by rfl) ⟨1627649, by rfl⟩ : syracuseStep 2170199 = 3255299) B3255299
theorem B1269079 : Blo 1268452 1269079 := bstep (se 1 (by rfl) ⟨951809, by rfl⟩ : syracuseStep 1269079 = 1903619) B1903619
theorem B2858327 : Blo 1268452 2858327 := bstep (se 1 (by rfl) ⟨2143745, by rfl⟩ : syracuseStep 2858327 = 4287491) B4287491
theorem B1269099 : Blo 1268452 1269099 := bstep (se 1 (by rfl) ⟨951824, by rfl⟩ : syracuseStep 1269099 = 1903649) B1903649
theorem B1269111 : Blo 1268452 1269111 := bstep (se 1 (by rfl) ⟨951833, by rfl⟩ : syracuseStep 1269111 = 1903667) B1903667
theorem B1269131 : Blo 1268452 1269131 := bstep (se 1 (by rfl) ⟨951848, by rfl⟩ : syracuseStep 1269131 = 1903697) B1903697
theorem B1269143 : Blo 1268452 1269143 := bstep (se 1 (by rfl) ⟨951857, by rfl⟩ : syracuseStep 1269143 = 1903715) B1903715
theorem B6430103 : Blo 1268452 6430103 := bstep (se 1 (by rfl) ⟨4822577, by rfl⟩ : syracuseStep 6430103 = 9645155) B9645155
theorem B1269163 : Blo 1268452 1269163 := bstep (se 1 (by rfl) ⟨951872, by rfl⟩ : syracuseStep 1269163 = 1903745) B1903745
theorem B1269175 : Blo 1268452 1269175 := bstep (se 1 (by rfl) ⟨951881, by rfl⟩ : syracuseStep 1269175 = 1903763) B1903763
theorem B1269195 : Blo 1268452 1269195 := bstep (se 1 (by rfl) ⟨951896, by rfl⟩ : syracuseStep 1269195 = 1903793) B1903793
theorem B1269207 : Blo 1268452 1269207 := bstep (se 1 (by rfl) ⟨951905, by rfl⟩ : syracuseStep 1269207 = 1903811) B1903811
theorem B1269227 : Blo 1268452 1269227 := bstep (se 1 (by rfl) ⟨951920, by rfl⟩ : syracuseStep 1269227 = 1903841) B1903841
theorem B1269239 : Blo 1268452 1269239 := bstep (se 1 (by rfl) ⟨951929, by rfl⟩ : syracuseStep 1269239 = 1903859) B1903859
theorem B1269259 : Blo 1268452 1269259 := bstep (se 1 (by rfl) ⟨951944, by rfl⟩ : syracuseStep 1269259 = 1903889) B1903889
theorem B2858507 : Blo 1268452 2858507 := bstep (se 1 (by rfl) ⟨2143880, by rfl⟩ : syracuseStep 2858507 = 4287761) B4287761
theorem B1269271 : Blo 1268452 1269271 := bstep (se 1 (by rfl) ⟨951953, by rfl⟩ : syracuseStep 1269271 = 1903907) B1903907
theorem B4283927 : Blo 1268452 4283927 := bstep (se 1 (by rfl) ⟨3212945, by rfl⟩ : syracuseStep 4283927 = 6425891) B6425891
theorem B1269291 : Blo 1268452 1269291 := bstep (se 1 (by rfl) ⟨951968, by rfl⟩ : syracuseStep 1269291 = 1903937) B1903937
theorem B4881971 : Blo 1268452 4881971 := bstep (se 1 (by rfl) ⟨3661478, by rfl⟩ : syracuseStep 4881971 = 7322957) B7322957
theorem B1269303 : Blo 1268452 1269303 := bstep (se 1 (by rfl) ⟨951977, by rfl⟩ : syracuseStep 1269303 = 1903955) B1903955
theorem B5791297 : Blo 1268452 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B1269323 : Blo 1268452 1269323 := bstep (se 1 (by rfl) ⟨951992, by rfl⟩ : syracuseStep 1269323 = 1903985) B1903985
theorem B1269335 : Blo 1268452 1269335 := bstep (se 1 (by rfl) ⟨952001, by rfl⟩ : syracuseStep 1269335 = 1904003) B1904003
theorem B1269355 : Blo 1268452 1269355 := bstep (se 1 (by rfl) ⟨952016, by rfl⟩ : syracuseStep 1269355 = 1904033) B1904033
theorem B1269367 : Blo 1268452 1269367 := bstep (se 1 (by rfl) ⟨952025, by rfl⟩ : syracuseStep 1269367 = 1904051) B1904051
theorem B1269387 : Blo 1268452 1269387 := bstep (se 1 (by rfl) ⟨952040, by rfl⟩ : syracuseStep 1269387 = 1904081) B1904081
theorem B7224983 : Blo 1268452 7224983 := bstep (se 1 (by rfl) ⟨5418737, by rfl⟩ : syracuseStep 7224983 = 10837475) B10837475
theorem B1269399 : Blo 1268452 1269399 := bstep (se 1 (by rfl) ⟨952049, by rfl⟩ : syracuseStep 1269399 = 1904099) B1904099
theorem B1269419 : Blo 1268452 1269419 := bstep (se 1 (by rfl) ⟨952064, by rfl⟩ : syracuseStep 1269419 = 1904129) B1904129
theorem B1269431 : Blo 1268452 1269431 := bstep (se 1 (by rfl) ⟨952073, by rfl⟩ : syracuseStep 1269431 = 1904147) B1904147
theorem B1269451 : Blo 1268452 1269451 := bstep (se 1 (by rfl) ⟨952088, by rfl⟩ : syracuseStep 1269451 = 1904177) B1904177
theorem B1269463 : Blo 1268452 1269463 := bstep (se 1 (by rfl) ⟨952097, by rfl⟩ : syracuseStep 1269463 = 1904195) B1904195
theorem B3612377 : Blo 1268452 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B6864601 : Blo 1268452 6864601 := bstep (se 2 (by rfl) ⟨2574225, by rfl⟩ : syracuseStep 6864601 = 5148451) B5148451
theorem B1269483 : Blo 1268452 1269483 := bstep (se 1 (by rfl) ⟨952112, by rfl⟩ : syracuseStep 1269483 = 1904225) B1904225
theorem B1269495 : Blo 1268452 1269495 := bstep (se 1 (by rfl) ⟨952121, by rfl⟩ : syracuseStep 1269495 = 1904243) B1904243
theorem B1269515 : Blo 1268452 1269515 := bstep (se 1 (by rfl) ⟨952136, by rfl⟩ : syracuseStep 1269515 = 1904273) B1904273
theorem B1269527 : Blo 1268452 1269527 := bstep (se 1 (by rfl) ⟨952145, by rfl⟩ : syracuseStep 1269527 = 1904291) B1904291
theorem B1269547 : Blo 1268452 1269547 := bstep (se 1 (by rfl) ⟨952160, by rfl⟩ : syracuseStep 1269547 = 1904321) B1904321
theorem B4816685 : Blo 1268452 4816685 := bstep (se 3 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 4816685 = 1806257) B1806257
theorem B1269559 : Blo 1268452 1269559 := bstep (se 1 (by rfl) ⟨952169, by rfl⟩ : syracuseStep 1269559 = 1904339) B1904339
theorem B3211073 : Blo 1268452 3211073 := bstep (se 2 (by rfl) ⟨1204152, by rfl⟩ : syracuseStep 3211073 = 2408305) B2408305
theorem B12205889 : Blo 1268452 12205889 := bstep (se 2 (by rfl) ⟨4577208, by rfl⟩ : syracuseStep 12205889 = 9154417) B9154417
theorem B2408267 : Blo 1268452 2408267 := bstep (se 1 (by rfl) ⟨1806200, by rfl⟩ : syracuseStep 2408267 = 3612401) B3612401
theorem B1269579 : Blo 1268452 1269579 := bstep (se 1 (by rfl) ⟨952184, by rfl⟩ : syracuseStep 1269579 = 1904369) B1904369
theorem B1269591 : Blo 1268452 1269591 := bstep (se 1 (by rfl) ⟨952193, by rfl⟩ : syracuseStep 1269591 = 1904387) B1904387
theorem B1269611 : Blo 1268452 1269611 := bstep (se 1 (by rfl) ⟨952208, by rfl⟩ : syracuseStep 1269611 = 1904417) B1904417
theorem B1269623 : Blo 1268452 1269623 := bstep (se 1 (by rfl) ⟨952217, by rfl⟩ : syracuseStep 1269623 = 1904435) B1904435
theorem B1269643 : Blo 1268452 1269643 := bstep (se 1 (by rfl) ⟨952232, by rfl⟩ : syracuseStep 1269643 = 1904465) B1904465
theorem B1269655 : Blo 1268452 1269655 := bstep (se 1 (by rfl) ⟨952241, by rfl⟩ : syracuseStep 1269655 = 1904483) B1904483
theorem B1269675 : Blo 1268452 1269675 := bstep (se 1 (by rfl) ⟨952256, by rfl⟩ : syracuseStep 1269675 = 1904513) B1904513
theorem B1269687 : Blo 1268452 1269687 := bstep (se 1 (by rfl) ⟨952265, by rfl⟩ : syracuseStep 1269687 = 1904531) B1904531
theorem B1269707 : Blo 1268452 1269707 := bstep (se 1 (by rfl) ⟨952280, by rfl⟩ : syracuseStep 1269707 = 1904561) B1904561
theorem B1269719 : Blo 1268452 1269719 := bstep (se 1 (by rfl) ⟨952289, by rfl⟩ : syracuseStep 1269719 = 1904579) B1904579
theorem B6422489 : Blo 1268452 6422489 := bstep (se 2 (by rfl) ⟨2408433, by rfl⟩ : syracuseStep 6422489 = 4816867) B4816867
theorem B1269739 : Blo 1268452 1269739 := bstep (se 1 (by rfl) ⟨952304, by rfl⟩ : syracuseStep 1269739 = 1904609) B1904609
theorem B1269751 : Blo 1268452 1269751 := bstep (se 1 (by rfl) ⟨952313, by rfl⟩ : syracuseStep 1269751 = 1904627) B1904627
theorem B3211265 : Blo 1268452 3211265 := bstep (se 2 (by rfl) ⟨1204224, by rfl⟩ : syracuseStep 3211265 = 2408449) B2408449
theorem B1269767 : Blo 1268452 1269767 := bstep (se 1 (by rfl) ⟨952325, by rfl⟩ : syracuseStep 1269767 = 1904651) B1904651
theorem B1269775 : Blo 1268452 1269775 := bstep (se 1 (by rfl) ⟨952331, by rfl⟩ : syracuseStep 1269775 = 1904663) B1904663
theorem B16269335 : Blo 1268452 16269335 := bstep (se 1 (by rfl) ⟨12202001, by rfl⟩ : syracuseStep 16269335 = 24404003) B24404003
theorem B1269819 : Blo 1268452 1269819 := bstep (se 1 (by rfl) ⟨952364, by rfl⟩ : syracuseStep 1269819 = 1904729) B1904729
theorem B10289213 : Blo 1268452 10289213 := bstep (se 3 (by rfl) ⟨1929227, by rfl⟩ : syracuseStep 10289213 = 3858455) B3858455
theorem B13721717 : Blo 1268452 13721717 := bstep (se 5 (by rfl) ⟨643205, by rfl⟩ : syracuseStep 13721717 = 1286411) B1286411
theorem B1269895 : Blo 1268452 1269895 := bstep (se 1 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 1269895 = 1904843) B1904843
theorem B1269903 : Blo 1268452 1269903 := bstep (se 1 (by rfl) ⟨952427, by rfl⟩ : syracuseStep 1269903 = 1904855) B1904855
theorem B1269947 : Blo 1268452 1269947 := bstep (se 1 (by rfl) ⟨952460, by rfl⟩ : syracuseStep 1269947 = 1904921) B1904921
theorem B6430913 : Blo 1268452 6430913 := bstep (se 2 (by rfl) ⟨2411592, by rfl⟩ : syracuseStep 6430913 = 4823185) B4823185
theorem B1270023 : Blo 1268452 1270023 := bstep (se 1 (by rfl) ⟨952517, by rfl⟩ : syracuseStep 1270023 = 1905035) B1905035
theorem B1270031 : Blo 1268452 1270031 := bstep (se 1 (by rfl) ⟨952523, by rfl⟩ : syracuseStep 1270031 = 1905047) B1905047
theorem B13730107 : Blo 1268452 13730107 := bstep (se 1 (by rfl) ⟨10297580, by rfl⟩ : syracuseStep 13730107 = 20595161) B20595161
theorem B1270075 : Blo 1268452 1270075 := bstep (se 1 (by rfl) ⟨952556, by rfl⟩ : syracuseStep 1270075 = 1905113) B1905113
theorem B3613015 : Blo 1268452 3613015 := bstep (se 1 (by rfl) ⟨2709761, by rfl⟩ : syracuseStep 3613015 = 5419523) B5419523
theorem B1606007 : Blo 1268452 1606007 := bstep (se 1 (by rfl) ⟨1204505, by rfl⟩ : syracuseStep 1606007 = 2409011) B2409011
theorem B1270151 : Blo 1268452 1270151 := bstep (se 1 (by rfl) ⟨952613, by rfl⟩ : syracuseStep 1270151 = 1905227) B1905227
theorem B1270159 : Blo 1268452 1270159 := bstep (se 1 (by rfl) ⟨952619, by rfl⟩ : syracuseStep 1270159 = 1905239) B1905239
theorem B1270203 : Blo 1268452 1270203 := bstep (se 1 (by rfl) ⟨952652, by rfl⟩ : syracuseStep 1270203 = 1905305) B1905305
theorem B3211721 : Blo 1268452 3211721 := bstep (se 2 (by rfl) ⟨1204395, by rfl⟩ : syracuseStep 3211721 = 2408791) B2408791
theorem B1270279 : Blo 1268452 1270279 := bstep (se 1 (by rfl) ⟨952709, by rfl⟩ : syracuseStep 1270279 = 1905419) B1905419
theorem B4882955 : Blo 1268452 4882955 := bstep (se 1 (by rfl) ⟨3662216, by rfl⟩ : syracuseStep 4882955 = 7324433) B7324433
theorem B1606159 : Blo 1268452 1606159 := bstep (se 1 (by rfl) ⟨1204619, by rfl⟩ : syracuseStep 1606159 = 2409239) B2409239
theorem B1270287 : Blo 1268452 1270287 := bstep (se 1 (by rfl) ⟨952715, by rfl⟩ : syracuseStep 1270287 = 1905431) B1905431
theorem B3613243 : Blo 1268452 3613243 := bstep (se 1 (by rfl) ⟨2709932, by rfl⟩ : syracuseStep 3613243 = 5419865) B5419865
theorem B1270331 : Blo 1268452 1270331 := bstep (se 1 (by rfl) ⟨952748, by rfl⟩ : syracuseStep 1270331 = 1905497) B1905497
theorem B2409095 : Blo 1268452 2409095 := bstep (se 1 (by rfl) ⟨1806821, by rfl⟩ : syracuseStep 2409095 = 3613643) B3613643
theorem B1270407 : Blo 1268452 1270407 := bstep (se 1 (by rfl) ⟨952805, by rfl⟩ : syracuseStep 1270407 = 1905611) B1905611
theorem B1270415 : Blo 1268452 1270415 := bstep (se 1 (by rfl) ⟨952811, by rfl⟩ : syracuseStep 1270415 = 1905623) B1905623
theorem B3613369 : Blo 1268452 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B1606331 : Blo 1268452 1606331 := bstep (se 1 (by rfl) ⟨1204748, by rfl⟩ : syracuseStep 1606331 = 2409497) B2409497
theorem B9642725 : Blo 1268452 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B3212075 : Blo 1268452 3212075 := bstep (se 1 (by rfl) ⟨2409056, by rfl⟩ : syracuseStep 3212075 = 4818113) B4818113
theorem B3048251 : Blo 1268452 3048251 := bstep (se 1 (by rfl) ⟨2286188, by rfl⟩ : syracuseStep 3048251 = 4572377) B4572377
theorem B4285331 : Blo 1268452 4285331 := bstep (se 1 (by rfl) ⟨3213998, by rfl⟩ : syracuseStep 4285331 = 6427997) B6427997
theorem B109831139 : Blo 1268452 109831139 := bstep (se 1 (by rfl) ⟨82373354, by rfl⟩ : syracuseStep 109831139 = 164746709) B164746709
theorem B9634949 : Blo 1268452 9634949 := bstep (se 4 (by rfl) ⟨903276, by rfl⟩ : syracuseStep 9634949 = 1806553) B1806553
theorem B2712761 : Blo 1268452 2712761 := bstep (se 2 (by rfl) ⟨1017285, by rfl⟩ : syracuseStep 2712761 = 2034571) B2034571
theorem B5145871 : Blo 1268452 5145871 := bstep (se 1 (by rfl) ⟨3859403, by rfl⟩ : syracuseStep 5145871 = 7718807) B7718807
theorem B2286881 : Blo 1268452 2286881 := bstep (se 2 (by rfl) ⟨857580, by rfl⟩ : syracuseStep 2286881 = 1715161) B1715161
theorem B13018427 : Blo 1268452 13018427 := bstep (se 1 (by rfl) ⟨9763820, by rfl⟩ : syracuseStep 13018427 = 19527641) B19527641
theorem B4572551 : Blo 1268452 4572551 := bstep (se 1 (by rfl) ⟨3429413, by rfl⟩ : syracuseStep 4572551 = 6858827) B6858827
theorem B7226759 : Blo 1268452 7226759 := bstep (se 1 (by rfl) ⟨5420069, by rfl⟩ : syracuseStep 7226759 = 10840139) B10840139
theorem B4818311 : Blo 1268452 4818311 := bstep (se 1 (by rfl) ⟨3613733, by rfl⟩ : syracuseStep 4818311 = 7227467) B7227467
theorem B6956441 : Blo 1268452 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B13018589 : Blo 1268452 13018589 := bstep (se 3 (by rfl) ⟨2440985, by rfl⟩ : syracuseStep 13018589 = 4881971) B4881971
theorem B29713949 : Blo 1268452 29713949 := bstep (se 3 (by rfl) ⟨5571365, by rfl⟩ : syracuseStep 29713949 = 11142731) B11142731
theorem B7226941 : Blo 1268452 7226941 := bstep (se 3 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 7226941 = 2710103) B2710103
theorem B1607303 : Blo 1268452 1607303 := bstep (se 1 (by rfl) ⟨1205477, by rfl⟩ : syracuseStep 1607303 = 2410955) B2410955
theorem B54904499 : Blo 1268452 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B3213067 : Blo 1268452 3213067 := bstep (se 1 (by rfl) ⟨2409800, by rfl⟩ : syracuseStep 3213067 = 4819601) B4819601
theorem B1427215 : Blo 1268452 1427215 := bstep (se 1 (by rfl) ⟨1070411, by rfl⟩ : syracuseStep 1427215 = 2140823) B2140823
theorem B2172791 : Blo 1268452 2172791 := bstep (se 1 (by rfl) ⟨1629593, by rfl⟩ : syracuseStep 2172791 = 3259187) B3259187
theorem B3213209 : Blo 1268452 3213209 := bstep (se 2 (by rfl) ⟨1204953, by rfl⟩ : syracuseStep 3213209 = 2409907) B2409907
theorem B5425163 : Blo 1268452 5425163 := bstep (se 1 (by rfl) ⟨4068872, by rfl⟩ : syracuseStep 5425163 = 8137745) B8137745
theorem B3213371 : Blo 1268452 3213371 := bstep (se 1 (by rfl) ⟨2410028, by rfl⟩ : syracuseStep 3213371 = 4820057) B4820057
theorem B5146685 : Blo 1268452 5146685 := bstep (se 3 (by rfl) ⟨965003, by rfl⟩ : syracuseStep 5146685 = 1930007) B1930007
theorem B9398359 : Blo 1268452 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B3049559 : Blo 1268452 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B1902779 : Blo 1268452 1902779 := bstep (se 1 (by rfl) ⟨1427084, by rfl⟩ : syracuseStep 1902779 = 2854169) B2854169
theorem B2410697 : Blo 1268452 2410697 := bstep (se 2 (by rfl) ⟨904011, by rfl⟩ : syracuseStep 2410697 = 1808023) B1808023
theorem B1902839 : Blo 1268452 1902839 := bstep (se 1 (by rfl) ⟨1427129, by rfl⟩ : syracuseStep 1902839 = 2854259) B2854259
theorem B1427719 : Blo 1268452 1427719 := bstep (se 1 (by rfl) ⟨1070789, by rfl⟩ : syracuseStep 1427719 = 2141579) B2141579
theorem B1902863 : Blo 1268452 1902863 := bstep (se 1 (by rfl) ⟨1427147, by rfl⟩ : syracuseStep 1902863 = 2854295) B2854295
theorem B5146895 : Blo 1268452 5146895 := bstep (se 1 (by rfl) ⟨3860171, by rfl⟩ : syracuseStep 5146895 = 7720343) B7720343
theorem B4286735 : Blo 1268452 4286735 := bstep (se 1 (by rfl) ⟨3215051, by rfl⟩ : syracuseStep 4286735 = 6430103) B6430103
theorem B9152801 : Blo 1268452 9152801 := bstep (se 2 (by rfl) ⟨3432300, by rfl⟩ : syracuseStep 9152801 = 6864601) B6864601
theorem B1902905 : Blo 1268452 1902905 := bstep (se 2 (by rfl) ⟨713589, by rfl⟩ : syracuseStep 1902905 = 1427179) B1427179
theorem B1902983 : Blo 1268452 1902983 := bstep (se 1 (by rfl) ⟨1427237, by rfl⟩ : syracuseStep 1902983 = 2854475) B2854475
theorem B1526159 : Blo 1268452 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B3213715 : Blo 1268452 3213715 := bstep (se 1 (by rfl) ⟨2410286, by rfl⟩ : syracuseStep 3213715 = 4820573) B4820573
theorem B1903019 : Blo 1268452 1903019 := bstep (se 1 (by rfl) ⟨1427264, by rfl⟩ : syracuseStep 1903019 = 2854529) B2854529
theorem B1427899 : Blo 1268452 1427899 := bstep (se 1 (by rfl) ⟨1070924, by rfl⟩ : syracuseStep 1427899 = 2141849) B2141849
theorem B1903049 : Blo 1268452 1903049 := bstep (se 2 (by rfl) ⟨713643, by rfl⟩ : syracuseStep 1903049 = 1427287) B1427287
theorem B7719389 : Blo 1268452 7719389 := bstep (se 3 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 7719389 = 2894771) B2894771
theorem B13732355 : Blo 1268452 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B4287005 : Blo 1268452 4287005 := bstep (se 3 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 4287005 = 1607627) B1607627
theorem B3213857 : Blo 1268452 3213857 := bstep (se 2 (by rfl) ⟨1205196, by rfl⟩ : syracuseStep 3213857 = 2410393) B2410393
theorem B18287147 : Blo 1268452 18287147 := bstep (se 1 (by rfl) ⟨13715360, by rfl⟩ : syracuseStep 18287147 = 27430721) B27430721
theorem B2140715 : Blo 1268452 2140715 := bstep (se 1 (by rfl) ⟨1605536, by rfl⟩ : syracuseStep 2140715 = 3211073) B3211073
theorem B8137259 : Blo 1268452 8137259 := bstep (se 1 (by rfl) ⟨6102944, by rfl⟩ : syracuseStep 8137259 = 12205889) B12205889
theorem B1903163 : Blo 1268452 1903163 := bstep (se 1 (by rfl) ⟨1427372, by rfl⟩ : syracuseStep 1903163 = 2854745) B2854745
theorem B3615293 : Blo 1268452 3615293 := bstep (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) B1355735
theorem B1903223 : Blo 1268452 1903223 := bstep (se 1 (by rfl) ⟨1427417, by rfl⟩ : syracuseStep 1903223 = 2854835) B2854835
theorem B10848887 : Blo 1268452 10848887 := bstep (se 1 (by rfl) ⟨8136665, by rfl⟩ : syracuseStep 10848887 = 16273331) B16273331
theorem B1903247 : Blo 1268452 1903247 := bstep (se 1 (by rfl) ⟨1427435, by rfl⟩ : syracuseStep 1903247 = 2854871) B2854871
theorem B1903289 : Blo 1268452 1903289 := bstep (se 2 (by rfl) ⟨713733, by rfl⟩ : syracuseStep 1903289 = 1427467) B1427467
theorem B1903367 : Blo 1268452 1903367 := bstep (se 1 (by rfl) ⟨1427525, by rfl⟩ : syracuseStep 1903367 = 2855051) B2855051
theorem B1903403 : Blo 1268452 1903403 := bstep (se 1 (by rfl) ⟨1427552, by rfl⟩ : syracuseStep 1903403 = 2855105) B2855105
theorem B1903433 : Blo 1268452 1903433 := bstep (se 2 (by rfl) ⟨713787, by rfl⟩ : syracuseStep 1903433 = 1427575) B1427575
theorem B1428367 : Blo 1268452 1428367 := bstep (se 1 (by rfl) ⟨1071275, by rfl⟩ : syracuseStep 1428367 = 2142551) B2142551
theorem B2141113 : Blo 1268452 2141113 := bstep (se 2 (by rfl) ⟨802917, by rfl⟩ : syracuseStep 2141113 = 1605835) B1605835
theorem B1903547 : Blo 1268452 1903547 := bstep (se 1 (by rfl) ⟨1427660, by rfl⟩ : syracuseStep 1903547 = 2855321) B2855321
theorem B1903607 : Blo 1268452 1903607 := bstep (se 1 (by rfl) ⟨1427705, by rfl⟩ : syracuseStep 1903607 = 2855411) B2855411
theorem B1903631 : Blo 1268452 1903631 := bstep (se 1 (by rfl) ⟨1427723, by rfl⟩ : syracuseStep 1903631 = 2855447) B2855447
theorem B1903673 : Blo 1268452 1903673 := bstep (se 2 (by rfl) ⟨713877, by rfl⟩ : syracuseStep 1903673 = 1427755) B1427755
theorem B4820087 : Blo 1268452 4820087 := bstep (se 1 (by rfl) ⟨3615065, by rfl⟩ : syracuseStep 4820087 = 7230131) B7230131
theorem B1903751 : Blo 1268452 1903751 := bstep (se 1 (by rfl) ⟨1427813, by rfl⟩ : syracuseStep 1903751 = 2855627) B2855627
theorem B1903787 : Blo 1268452 1903787 := bstep (se 1 (by rfl) ⟨1427840, by rfl⟩ : syracuseStep 1903787 = 2855681) B2855681
theorem B1903817 : Blo 1268452 1903817 := bstep (se 2 (by rfl) ⟨713931, by rfl⟩ : syracuseStep 1903817 = 1427863) B1427863
theorem B4582637 : Blo 1268452 4582637 := bstep (se 3 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 4582637 = 1718489) B1718489
theorem B7228673 : Blo 1268452 7228673 := bstep (se 2 (by rfl) ⟨2710752, by rfl⟩ : syracuseStep 7228673 = 5421505) B5421505
theorem B2854187 : Blo 1268452 2854187 := bstep (se 1 (by rfl) ⟨2140640, by rfl⟩ : syracuseStep 2854187 = 4281281) B4281281
theorem B1903931 : Blo 1268452 1903931 := bstep (se 1 (by rfl) ⟨1427948, by rfl⟩ : syracuseStep 1903931 = 2855897) B2855897
theorem B1903991 : Blo 1268452 1903991 := bstep (se 1 (by rfl) ⟨1427993, by rfl⟩ : syracuseStep 1903991 = 2855987) B2855987
theorem B1428871 : Blo 1268452 1428871 := bstep (se 1 (by rfl) ⟨1071653, by rfl⟩ : syracuseStep 1428871 = 2143307) B2143307
theorem B1904015 : Blo 1268452 1904015 := bstep (se 1 (by rfl) ⟨1428011, by rfl⟩ : syracuseStep 1904015 = 2856023) B2856023
theorem B4124051 : Blo 1268452 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B2289043 : Blo 1268452 2289043 := bstep (se 1 (by rfl) ⟨1716782, by rfl⟩ : syracuseStep 2289043 = 3433565) B3433565
theorem B5787065 : Blo 1268452 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B1904057 : Blo 1268452 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B3214849 : Blo 1268452 3214849 := bstep (se 2 (by rfl) ⟨1205568, by rfl⟩ : syracuseStep 3214849 = 2411137) B2411137
theorem B9637379 : Blo 1268452 9637379 := bstep (se 1 (by rfl) ⟨7228034, by rfl⟩ : syracuseStep 9637379 = 14456069) B14456069
theorem B1904135 : Blo 1268452 1904135 := bstep (se 1 (by rfl) ⟨1428101, by rfl⟩ : syracuseStep 1904135 = 2856203) B2856203
theorem B15429149 : Blo 1268452 15429149 := bstep (se 3 (by rfl) ⟨2892965, by rfl⟩ : syracuseStep 15429149 = 5785931) B5785931
theorem B3616285 : Blo 1268452 3616285 := bstep (se 3 (by rfl) ⟨678053, by rfl⟩ : syracuseStep 3616285 = 1356107) B1356107
theorem B1904171 : Blo 1268452 1904171 := bstep (se 1 (by rfl) ⟨1428128, by rfl⟩ : syracuseStep 1904171 = 2856257) B2856257
theorem B1429051 : Blo 1268452 1429051 := bstep (se 1 (by rfl) ⟨1071788, by rfl⟩ : syracuseStep 1429051 = 2143577) B2143577
theorem B5787197 : Blo 1268452 5787197 := bstep (se 3 (by rfl) ⟨1085099, by rfl⟩ : syracuseStep 5787197 = 2170199) B2170199
theorem B1904201 : Blo 1268452 1904201 := bstep (se 2 (by rfl) ⟨714075, by rfl⟩ : syracuseStep 1904201 = 1428151) B1428151
theorem B2141815 : Blo 1268452 2141815 := bstep (se 1 (by rfl) ⟨1606361, by rfl⟩ : syracuseStep 2141815 = 3212723) B3212723
theorem B2854547 : Blo 1268452 2854547 := bstep (se 1 (by rfl) ⟨2140910, by rfl⟩ : syracuseStep 2854547 = 4281821) B4281821
theorem B1928875 : Blo 1268452 1928875 := bstep (se 1 (by rfl) ⟨1446656, by rfl⟩ : syracuseStep 1928875 = 2893313) B2893313
theorem B24399539 : Blo 1268452 24399539 := bstep (se 1 (by rfl) ⟨18299654, by rfl⟩ : syracuseStep 24399539 = 36599309) B36599309
theorem B1904315 : Blo 1268452 1904315 := bstep (se 1 (by rfl) ⟨1428236, by rfl⟩ : syracuseStep 1904315 = 2856473) B2856473
theorem B2854601 : Blo 1268452 2854601 := bstep (se 2 (by rfl) ⟨1070475, by rfl⟩ : syracuseStep 2854601 = 2140951) B2140951
theorem B1904375 : Blo 1268452 1904375 := bstep (se 1 (by rfl) ⟨1428281, by rfl⟩ : syracuseStep 1904375 = 2856563) B2856563
theorem B1904399 : Blo 1268452 1904399 := bstep (se 1 (by rfl) ⟨1428299, by rfl⟩ : syracuseStep 1904399 = 2856599) B2856599
theorem B1904441 : Blo 1268452 1904441 := bstep (se 2 (by rfl) ⟨714165, by rfl⟩ : syracuseStep 1904441 = 1428331) B1428331
theorem B2142011 : Blo 1268452 2142011 := bstep (se 1 (by rfl) ⟨1606508, by rfl⟩ : syracuseStep 2142011 = 3213017) B3213017
theorem B1904519 : Blo 1268452 1904519 := bstep (se 1 (by rfl) ⟨1428389, by rfl⟩ : syracuseStep 1904519 = 2856779) B2856779
theorem B1355663 : Blo 1268452 1355663 := bstep (se 1 (by rfl) ⟨1016747, by rfl⟩ : syracuseStep 1355663 = 2033495) B2033495
theorem B1904555 : Blo 1268452 1904555 := bstep (se 1 (by rfl) ⟨1428416, by rfl⟩ : syracuseStep 1904555 = 2856833) B2856833
theorem B1904585 : Blo 1268452 1904585 := bstep (se 2 (by rfl) ⟨714219, by rfl⟩ : syracuseStep 1904585 = 1428439) B1428439
theorem B1904699 : Blo 1268452 1904699 := bstep (se 1 (by rfl) ⟨1428524, by rfl⟩ : syracuseStep 1904699 = 2857049) B2857049
theorem B9146429 : Blo 1268452 9146429 := bstep (se 3 (by rfl) ⟨1714955, by rfl⟩ : syracuseStep 9146429 = 3429911) B3429911
theorem B4821059 : Blo 1268452 4821059 := bstep (se 1 (by rfl) ⟨3615794, by rfl⟩ : syracuseStep 4821059 = 7231589) B7231589
theorem B3215447 : Blo 1268452 3215447 := bstep (se 1 (by rfl) ⟨2411585, by rfl⟩ : syracuseStep 3215447 = 4823171) B4823171
theorem B1904759 : Blo 1268452 1904759 := bstep (se 1 (by rfl) ⟨1428569, by rfl⟩ : syracuseStep 1904759 = 2857139) B2857139
theorem B1904783 : Blo 1268452 1904783 := bstep (se 1 (by rfl) ⟨1428587, by rfl⟩ : syracuseStep 1904783 = 2857175) B2857175
theorem B24391853 : Blo 1268452 24391853 := bstep (se 3 (by rfl) ⟨4573472, by rfl⟩ : syracuseStep 24391853 = 9146945) B9146945
theorem B1904825 : Blo 1268452 1904825 := bstep (se 2 (by rfl) ⟨714309, by rfl⟩ : syracuseStep 1904825 = 1428619) B1428619
theorem B2142409 : Blo 1268452 2142409 := bstep (se 2 (by rfl) ⟨803403, by rfl⟩ : syracuseStep 2142409 = 1606807) B1606807
theorem B1904903 : Blo 1268452 1904903 := bstep (se 1 (by rfl) ⟨1428677, by rfl⟩ : syracuseStep 1904903 = 2857355) B2857355
theorem B1904939 : Blo 1268452 1904939 := bstep (se 1 (by rfl) ⟨1428704, by rfl⟩ : syracuseStep 1904939 = 2857409) B2857409
theorem B3215659 : Blo 1268452 3215659 := bstep (se 1 (by rfl) ⟨2411744, by rfl⟩ : syracuseStep 3215659 = 4823489) B4823489
theorem B1904969 : Blo 1268452 1904969 := bstep (se 2 (by rfl) ⟨714363, by rfl⟩ : syracuseStep 1904969 = 1428727) B1428727
theorem B3256691 : Blo 1268452 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B1716599 : Blo 1268452 1716599 := bstep (se 1 (by rfl) ⟨1287449, by rfl⟩ : syracuseStep 1716599 = 2574899) B2574899
theorem B2855303 : Blo 1268452 2855303 := bstep (se 1 (by rfl) ⟨2141477, by rfl⟩ : syracuseStep 2855303 = 4282955) B4282955
theorem B6427025 : Blo 1268452 6427025 := bstep (se 2 (by rfl) ⟨2410134, by rfl⟩ : syracuseStep 6427025 = 4820269) B4820269
theorem B3215801 : Blo 1268452 3215801 := bstep (se 2 (by rfl) ⟨1205925, by rfl⟩ : syracuseStep 3215801 = 2411851) B2411851
theorem B1905083 : Blo 1268452 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B1905143 : Blo 1268452 1905143 := bstep (se 1 (by rfl) ⟨1428857, by rfl⟩ : syracuseStep 1905143 = 2857715) B2857715
theorem B4821515 : Blo 1268452 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B1905167 : Blo 1268452 1905167 := bstep (se 1 (by rfl) ⟨1428875, by rfl⟩ : syracuseStep 1905167 = 2857751) B2857751
theorem B26415659 : Blo 1268452 26415659 := bstep (se 1 (by rfl) ⟨19811744, by rfl⟩ : syracuseStep 26415659 = 39623489) B39623489
theorem B1905209 : Blo 1268452 1905209 := bstep (se 2 (by rfl) ⟨714453, by rfl⟩ : syracuseStep 1905209 = 1428907) B1428907
theorem B2855483 : Blo 1268452 2855483 := bstep (se 1 (by rfl) ⟨2141612, by rfl⟩ : syracuseStep 2855483 = 4283225) B4283225
theorem B1905287 : Blo 1268452 1905287 := bstep (se 1 (by rfl) ⟨1428965, by rfl⟩ : syracuseStep 1905287 = 2857931) B2857931
theorem B1905323 : Blo 1268452 1905323 := bstep (se 1 (by rfl) ⟨1428992, by rfl⟩ : syracuseStep 1905323 = 2857985) B2857985
theorem B2855609 : Blo 1268452 2855609 := bstep (se 2 (by rfl) ⟨1070853, by rfl⟩ : syracuseStep 2855609 = 2141707) B2141707
theorem B1807049 : Blo 1268452 1807049 := bstep (se 2 (by rfl) ⟨677643, by rfl⟩ : syracuseStep 1807049 = 1355287) B1355287
theorem B1905353 : Blo 1268452 1905353 := bstep (se 2 (by rfl) ⟨714507, by rfl⟩ : syracuseStep 1905353 = 1429015) B1429015
theorem B7721729 : Blo 1268452 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B1905467 : Blo 1268452 1905467 := bstep (se 1 (by rfl) ⟨1429100, by rfl⟩ : syracuseStep 1905467 = 2858201) B2858201
theorem B1905527 : Blo 1268452 1905527 := bstep (se 1 (by rfl) ⟨1429145, by rfl⟩ : syracuseStep 1905527 = 2858291) B2858291
theorem B2143111 : Blo 1268452 2143111 := bstep (se 1 (by rfl) ⟨1607333, by rfl⟩ : syracuseStep 2143111 = 3214667) B3214667
theorem B1905551 : Blo 1268452 1905551 := bstep (se 1 (by rfl) ⟨1429163, by rfl⟩ : syracuseStep 1905551 = 2858327) B2858327
theorem B1905593 : Blo 1268452 1905593 := bstep (se 2 (by rfl) ⟨714597, by rfl⟩ : syracuseStep 1905593 = 1429195) B1429195
theorem B1905671 : Blo 1268452 1905671 := bstep (se 1 (by rfl) ⟨1429253, by rfl⟩ : syracuseStep 1905671 = 2858507) B2858507
theorem B2855951 : Blo 1268452 2855951 := bstep (se 1 (by rfl) ⟨2141963, by rfl⟩ : syracuseStep 2855951 = 4283927) B4283927
theorem B2855969 : Blo 1268452 2855969 := bstep (se 2 (by rfl) ⟨1070988, by rfl⟩ : syracuseStep 2855969 = 2141977) B2141977
theorem B4281659 : Blo 1268452 4281659 := bstep (se 1 (by rfl) ⟨3211244, by rfl⟩ : syracuseStep 4281659 = 6422489) B6422489
theorem B2856311 : Blo 1268452 2856311 := bstep (se 1 (by rfl) ⟨2142233, by rfl⟩ : syracuseStep 2856311 = 4284467) B4284467
theorem B2143759 : Blo 1268452 2143759 := bstep (se 1 (by rfl) ⟨1607819, by rfl⟩ : syracuseStep 2143759 = 3215639) B3215639
theorem B2856491 : Blo 1268452 2856491 := bstep (se 1 (by rfl) ⟨2142368, by rfl⟩ : syracuseStep 2856491 = 4284737) B4284737
theorem B1807915 : Blo 1268452 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B2709139 : Blo 1268452 2709139 := bstep (se 1 (by rfl) ⟨2031854, by rfl⟩ : syracuseStep 2709139 = 4063709) B4063709
theorem B20592305 : Blo 1268452 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B4282145 : Blo 1268452 4282145 := bstep (se 2 (by rfl) ⟨1605804, by rfl⟩ : syracuseStep 4282145 = 3211609) B3211609
theorem B4069153 : Blo 1268452 4069153 := bstep (se 2 (by rfl) ⟨1525932, by rfl⟩ : syracuseStep 4069153 = 3051865) B3051865
theorem B14464817 : Blo 1268452 14464817 := bstep (se 2 (by rfl) ⟨5424306, by rfl⟩ : syracuseStep 14464817 = 10848613) B10848613
theorem B2750267 : Blo 1268452 2750267 := bstep (se 1 (by rfl) ⟨2062700, by rfl⟩ : syracuseStep 2750267 = 4125401) B4125401
theorem B3430279 : Blo 1268452 3430279 := bstep (se 1 (by rfl) ⟨2572709, by rfl⟩ : syracuseStep 3430279 = 5145419) B5145419
theorem B2856851 : Blo 1268452 2856851 := bstep (se 1 (by rfl) ⟨2142638, by rfl⟩ : syracuseStep 2856851 = 4285277) B4285277
theorem B2856905 : Blo 1268452 2856905 := bstep (se 2 (by rfl) ⟨1071339, by rfl⟩ : syracuseStep 2856905 = 2142679) B2142679
theorem B4577323 : Blo 1268452 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B8132669 : Blo 1268452 8132669 := bstep (se 3 (by rfl) ⟨1524875, by rfl⟩ : syracuseStep 8132669 = 3049751) B3049751
theorem B4282739 : Blo 1268452 4282739 := bstep (se 1 (by rfl) ⟨3212054, by rfl⟩ : syracuseStep 4282739 = 6424109) B6424109
theorem B6429131 : Blo 1268452 6429131 := bstep (se 1 (by rfl) ⟨4821848, by rfl⟩ : syracuseStep 6429131 = 9643697) B9643697
theorem B3430927 : Blo 1268452 3430927 := bstep (se 1 (by rfl) ⟨2573195, by rfl⟩ : syracuseStep 3430927 = 5146391) B5146391
theorem B4823671 : Blo 1268452 4823671 := bstep (se 1 (by rfl) ⟨3617753, by rfl⟩ : syracuseStep 4823671 = 7235507) B7235507
theorem B2857607 : Blo 1268452 2857607 := bstep (se 1 (by rfl) ⟨2143205, by rfl⟩ : syracuseStep 2857607 = 4286411) B4286411
theorem B5143277 : Blo 1268452 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B4578029 : Blo 1268452 4578029 := bstep (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) B1716761
theorem B1268487 : Blo 1268452 1268487 := bstep (se 1 (by rfl) ⟨951365, by rfl⟩ : syracuseStep 1268487 = 1902731) B1902731
theorem B1268495 : Blo 1268452 1268495 := bstep (se 1 (by rfl) ⟨951371, by rfl⟩ : syracuseStep 1268495 = 1902743) B1902743
theorem B6429455 : Blo 1268452 6429455 := bstep (se 1 (by rfl) ⟨4822091, by rfl⟩ : syracuseStep 6429455 = 9644183) B9644183
theorem B1268539 : Blo 1268452 1268539 := bstep (se 1 (by rfl) ⟨951404, by rfl⟩ : syracuseStep 1268539 = 1902809) B1902809
theorem B2857787 : Blo 1268452 2857787 := bstep (se 1 (by rfl) ⟨2143340, by rfl⟩ : syracuseStep 2857787 = 4286681) B4286681
theorem B10992473 : Blo 1268452 10992473 := bstep (se 2 (by rfl) ⟨4122177, by rfl⟩ : syracuseStep 10992473 = 8244355) B8244355
theorem B1268615 : Blo 1268452 1268615 := bstep (se 1 (by rfl) ⟨951461, by rfl⟩ : syracuseStep 1268615 = 1902923) B1902923
theorem B1268623 : Blo 1268452 1268623 := bstep (se 1 (by rfl) ⟨951467, by rfl⟩ : syracuseStep 1268623 = 1902935) B1902935
theorem B2857913 : Blo 1268452 2857913 := bstep (se 2 (by rfl) ⟨1071717, by rfl⟩ : syracuseStep 2857913 = 2143435) B2143435
theorem B1268667 : Blo 1268452 1268667 := bstep (se 1 (by rfl) ⟨951500, by rfl⟩ : syracuseStep 1268667 = 1903001) B1903001
theorem B6101963 : Blo 1268452 6101963 := bstep (se 1 (by rfl) ⟨4576472, by rfl⟩ : syracuseStep 6101963 = 9152945) B9152945
theorem B1268743 : Blo 1268452 1268743 := bstep (se 1 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 1268743 = 1903115) B1903115
theorem B3480587 : Blo 1268452 3480587 := bstep (se 1 (by rfl) ⟨2610440, by rfl⟩ : syracuseStep 3480587 = 5220881) B5220881
theorem B1268751 : Blo 1268452 1268751 := bstep (se 1 (by rfl) ⟨951563, by rfl⟩ : syracuseStep 1268751 = 1903127) B1903127
theorem B12205079 : Blo 1268452 12205079 := bstep (se 1 (by rfl) ⟨9153809, by rfl⟩ : syracuseStep 12205079 = 18307619) B18307619
theorem B1268795 : Blo 1268452 1268795 := bstep (se 1 (by rfl) ⟨951596, by rfl⟩ : syracuseStep 1268795 = 1903193) B1903193
theorem B1268871 : Blo 1268452 1268871 := bstep (se 1 (by rfl) ⟨951653, by rfl⟩ : syracuseStep 1268871 = 1903307) B1903307
theorem B1268879 : Blo 1268452 1268879 := bstep (se 1 (by rfl) ⟨951659, by rfl⟩ : syracuseStep 1268879 = 1903319) B1903319
theorem B1268923 : Blo 1268452 1268923 := bstep (se 1 (by rfl) ⟨951692, by rfl⟩ : syracuseStep 1268923 = 1903385) B1903385
theorem B9633005 : Blo 1268452 9633005 := bstep (se 3 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 9633005 = 3612377) B3612377
theorem B17382637 : Blo 1268452 17382637 := bstep (se 3 (by rfl) ⟨3259244, by rfl⟩ : syracuseStep 17382637 = 6518489) B6518489
theorem B1268999 : Blo 1268452 1268999 := bstep (se 1 (by rfl) ⟨951749, by rfl⟩ : syracuseStep 1268999 = 1903499) B1903499
theorem B1269007 : Blo 1268452 1269007 := bstep (se 1 (by rfl) ⟨951755, by rfl⟩ : syracuseStep 1269007 = 1903511) B1903511
theorem B2858255 : Blo 1268452 2858255 := bstep (se 1 (by rfl) ⟨2143691, by rfl⟩ : syracuseStep 2858255 = 4287383) B4287383
theorem B2858273 : Blo 1268452 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B125254957 : Blo 1268452 125254957 := bstep (se 3 (by rfl) ⟨23485304, by rfl⟩ : syracuseStep 125254957 = 46970609) B46970609
theorem B1269051 : Blo 1268452 1269051 := bstep (se 1 (by rfl) ⟨951788, by rfl⟩ : syracuseStep 1269051 = 1903577) B1903577
theorem B11140487 : Blo 1268452 11140487 := bstep (se 1 (by rfl) ⟨8355365, by rfl⟩ : syracuseStep 11140487 = 16710731) B16710731
theorem B1269127 : Blo 1268452 1269127 := bstep (se 1 (by rfl) ⟨951845, by rfl⟩ : syracuseStep 1269127 = 1903691) B1903691
theorem B10845575 : Blo 1268452 10845575 := bstep (se 1 (by rfl) ⟨8134181, by rfl⟩ : syracuseStep 10845575 = 16268363) B16268363
theorem B1269135 : Blo 1268452 1269135 := bstep (se 1 (by rfl) ⟨951851, by rfl⟩ : syracuseStep 1269135 = 1903703) B1903703
theorem B4578707 : Blo 1268452 4578707 := bstep (se 1 (by rfl) ⟨3434030, by rfl⟩ : syracuseStep 4578707 = 6868061) B6868061
theorem B1269179 : Blo 1268452 1269179 := bstep (se 1 (by rfl) ⟨951884, by rfl⟩ : syracuseStep 1269179 = 1903769) B1903769
theorem B1269255 : Blo 1268452 1269255 := bstep (se 1 (by rfl) ⟨951941, by rfl⟩ : syracuseStep 1269255 = 1903883) B1903883
theorem B1269263 : Blo 1268452 1269263 := bstep (se 1 (by rfl) ⟨951947, by rfl⟩ : syracuseStep 1269263 = 1903895) B1903895
theorem B7233047 : Blo 1268452 7233047 := bstep (se 1 (by rfl) ⟨5424785, by rfl⟩ : syracuseStep 7233047 = 10849571) B10849571
theorem B3431965 : Blo 1268452 3431965 := bstep (se 3 (by rfl) ⟨643493, by rfl⟩ : syracuseStep 3431965 = 1286987) B1286987
theorem B16277021 : Blo 1268452 16277021 := bstep (se 3 (by rfl) ⟨3051941, by rfl⟩ : syracuseStep 16277021 = 6103883) B6103883
theorem B1269307 : Blo 1268452 1269307 := bstep (se 1 (by rfl) ⟨951980, by rfl⟩ : syracuseStep 1269307 = 1903961) B1903961
theorem B1269383 : Blo 1268452 1269383 := bstep (se 1 (by rfl) ⟨952037, by rfl⟩ : syracuseStep 1269383 = 1904075) B1904075
theorem B1269391 : Blo 1268452 1269391 := bstep (se 1 (by rfl) ⟨952043, by rfl⟩ : syracuseStep 1269391 = 1904087) B1904087
theorem B1269435 : Blo 1268452 1269435 := bstep (se 1 (by rfl) ⟨952076, by rfl⟩ : syracuseStep 1269435 = 1904153) B1904153
theorem B1269511 : Blo 1268452 1269511 := bstep (se 1 (by rfl) ⟨952133, by rfl⟩ : syracuseStep 1269511 = 1904267) B1904267
theorem B4816655 : Blo 1268452 4816655 := bstep (se 1 (by rfl) ⟨3612491, by rfl⟩ : syracuseStep 4816655 = 7224983) B7224983
theorem B1269519 : Blo 1268452 1269519 := bstep (se 1 (by rfl) ⟨952139, by rfl⟩ : syracuseStep 1269519 = 1904279) B1904279
theorem B1269563 : Blo 1268452 1269563 := bstep (se 1 (by rfl) ⟨952172, by rfl⟩ : syracuseStep 1269563 = 1904345) B1904345
theorem B3211123 : Blo 1268452 3211123 := bstep (se 1 (by rfl) ⟨2408342, by rfl⟩ : syracuseStep 3211123 = 4816685) B4816685
theorem B3432311 : Blo 1268452 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B1605511 : Blo 1268452 1605511 := bstep (se 1 (by rfl) ⟨1204133, by rfl⟩ : syracuseStep 1605511 = 2408267) B2408267
theorem B1269639 : Blo 1268452 1269639 := bstep (se 1 (by rfl) ⟨952229, by rfl⟩ : syracuseStep 1269639 = 1904459) B1904459
theorem B1269647 : Blo 1268452 1269647 := bstep (se 1 (by rfl) ⟨952235, by rfl⟩ : syracuseStep 1269647 = 1904471) B1904471
theorem B1286075 : Blo 1268452 1286075 := bstep (se 1 (by rfl) ⟨964556, by rfl⟩ : syracuseStep 1286075 = 1929113) B1929113
theorem B1269691 : Blo 1268452 1269691 := bstep (se 1 (by rfl) ⟨952268, by rfl⟩ : syracuseStep 1269691 = 1904537) B1904537
theorem B10846223 : Blo 1268452 10846223 := bstep (se 1 (by rfl) ⟨8134667, by rfl⟩ : syracuseStep 10846223 = 16269335) B16269335
theorem B1269799 : Blo 1268452 1269799 := bstep (se 1 (by rfl) ⟨952349, by rfl⟩ : syracuseStep 1269799 = 1904699) B1904699
theorem B6103097 : Blo 1268452 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B1269839 : Blo 1268452 1269839 := bstep (se 1 (by rfl) ⟨952379, by rfl⟩ : syracuseStep 1269839 = 1904759) B1904759
theorem B1269855 : Blo 1268452 1269855 := bstep (se 1 (by rfl) ⟨952391, by rfl⟩ : syracuseStep 1269855 = 1904783) B1904783
theorem B16261235 : Blo 1268452 16261235 := bstep (se 1 (by rfl) ⟨12195926, by rfl⟩ : syracuseStep 16261235 = 24391853) B24391853
theorem B52084853 : Blo 1268452 52084853 := bstep (se 5 (by rfl) ⟨2441477, by rfl⟩ : syracuseStep 52084853 = 4882955) B4882955
theorem B1269883 : Blo 1268452 1269883 := bstep (se 1 (by rfl) ⟨952412, by rfl⟩ : syracuseStep 1269883 = 1904825) B1904825
theorem B1269935 : Blo 1268452 1269935 := bstep (se 1 (by rfl) ⟨952451, by rfl⟩ : syracuseStep 1269935 = 1904903) B1904903
theorem B1269959 : Blo 1268452 1269959 := bstep (se 1 (by rfl) ⟨952469, by rfl⟩ : syracuseStep 1269959 = 1904939) B1904939
theorem B1269979 : Blo 1268452 1269979 := bstep (se 1 (by rfl) ⟨952484, by rfl⟩ : syracuseStep 1269979 = 1904969) B1904969
theorem B4284683 : Blo 1268452 4284683 := bstep (se 1 (by rfl) ⟨3213512, by rfl⟩ : syracuseStep 4284683 = 6427025) B6427025
theorem B1270055 : Blo 1268452 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B1270095 : Blo 1268452 1270095 := bstep (se 1 (by rfl) ⟨952571, by rfl⟩ : syracuseStep 1270095 = 1905143) B1905143
theorem B1270111 : Blo 1268452 1270111 := bstep (se 1 (by rfl) ⟨952583, by rfl⟩ : syracuseStep 1270111 = 1905167) B1905167
theorem B1270139 : Blo 1268452 1270139 := bstep (se 1 (by rfl) ⟨952604, by rfl⟩ : syracuseStep 1270139 = 1905209) B1905209
theorem B1606063 : Blo 1268452 1606063 := bstep (se 1 (by rfl) ⟨1204547, by rfl⟩ : syracuseStep 1606063 = 2409095) B2409095
theorem B1270191 : Blo 1268452 1270191 := bstep (se 1 (by rfl) ⟨952643, by rfl⟩ : syracuseStep 1270191 = 1905287) B1905287
theorem B1270215 : Blo 1268452 1270215 := bstep (se 1 (by rfl) ⟨952661, by rfl⟩ : syracuseStep 1270215 = 1905323) B1905323
theorem B4817353 : Blo 1268452 4817353 := bstep (se 2 (by rfl) ⟨1806507, by rfl⟩ : syracuseStep 4817353 = 3613015) B3613015
theorem B1270235 : Blo 1268452 1270235 := bstep (se 1 (by rfl) ⟨952676, by rfl⟩ : syracuseStep 1270235 = 1905353) B1905353
theorem B4284953 : Blo 1268452 4284953 := bstep (se 2 (by rfl) ⟨1606857, by rfl⟩ : syracuseStep 4284953 = 3213715) B3213715
theorem B1270311 : Blo 1268452 1270311 := bstep (se 1 (by rfl) ⟨952733, by rfl⟩ : syracuseStep 1270311 = 1905467) B1905467
theorem B1270351 : Blo 1268452 1270351 := bstep (se 1 (by rfl) ⟨952763, by rfl⟩ : syracuseStep 1270351 = 1905527) B1905527
theorem B1270367 : Blo 1268452 1270367 := bstep (se 1 (by rfl) ⟨952775, by rfl⟩ : syracuseStep 1270367 = 1905551) B1905551
theorem B1270395 : Blo 1268452 1270395 := bstep (se 1 (by rfl) ⟨952796, by rfl⟩ : syracuseStep 1270395 = 1905593) B1905593
theorem B73220759 : Blo 1268452 73220759 := bstep (se 1 (by rfl) ⟨54915569, by rfl⟩ : syracuseStep 73220759 = 109831139) B109831139
theorem B1270447 : Blo 1268452 1270447 := bstep (se 1 (by rfl) ⟨952835, by rfl⟩ : syracuseStep 1270447 = 1905671) B1905671
theorem B4817657 : Blo 1268452 4817657 := bstep (se 2 (by rfl) ⟨1806621, by rfl⟩ : syracuseStep 4817657 = 3613243) B3613243
theorem B6423299 : Blo 1268452 6423299 := bstep (se 1 (by rfl) ⟨4817474, by rfl⟩ : syracuseStep 6423299 = 9634949) B9634949
theorem B6431561 : Blo 1268452 6431561 := bstep (se 2 (by rfl) ⟨2411835, by rfl⟩ : syracuseStep 6431561 = 4823671) B4823671
theorem B1524587 : Blo 1268452 1524587 := bstep (se 1 (by rfl) ⟨1143440, by rfl⟩ : syracuseStep 1524587 = 2286881) B2286881
theorem B4817825 : Blo 1268452 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B3048367 : Blo 1268452 3048367 := bstep (se 1 (by rfl) ⟨2286275, by rfl⟩ : syracuseStep 3048367 = 4572551) B4572551
theorem B4817839 : Blo 1268452 4817839 := bstep (se 1 (by rfl) ⟨3613379, by rfl⟩ : syracuseStep 4817839 = 7226759) B7226759
theorem B3212207 : Blo 1268452 3212207 := bstep (se 1 (by rfl) ⟨2409155, by rfl⟩ : syracuseStep 3212207 = 4818311) B4818311
theorem B4637627 : Blo 1268452 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B8684509 : Blo 1268452 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B19809299 : Blo 1268452 19809299 := bstep (se 1 (by rfl) ⟨14856974, by rfl⟩ : syracuseStep 19809299 = 29713949) B29713949
theorem B36602999 : Blo 1268452 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B9643211 : Blo 1268452 9643211 := bstep (se 1 (by rfl) ⟨7232408, by rfl⟩ : syracuseStep 9643211 = 14464817) B14464817
theorem B2033039 : Blo 1268452 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B1607131 : Blo 1268452 1607131 := bstep (se 1 (by rfl) ⟨1205348, by rfl⟩ : syracuseStep 1607131 = 2410697) B2410697
theorem B4286087 : Blo 1268452 4286087 := bstep (se 1 (by rfl) ⟨3214565, by rfl⟩ : syracuseStep 4286087 = 6429131) B6429131
theorem B23176849 : Blo 1268452 23176849 := bstep (se 2 (by rfl) ⟨8691318, by rfl⟩ : syracuseStep 23176849 = 17382637) B17382637
theorem B5146259 : Blo 1268452 5146259 := bstep (se 1 (by rfl) ⟨3859694, by rfl⟩ : syracuseStep 5146259 = 7719389) B7719389
theorem B4286141 : Blo 1268452 4286141 := bstep (se 3 (by rfl) ⟨803651, by rfl⟩ : syracuseStep 4286141 = 1607303) B1607303
theorem B12191431 : Blo 1268452 12191431 := bstep (se 1 (by rfl) ⟨9143573, by rfl⟩ : syracuseStep 12191431 = 18287147) B18287147
theorem B1427143 : Blo 1268452 1427143 := bstep (se 1 (by rfl) ⟨1070357, by rfl⟩ : syracuseStep 1427143 = 2140715) B2140715
theorem B5424839 : Blo 1268452 5424839 := bstep (se 1 (by rfl) ⟨4068629, by rfl⟩ : syracuseStep 5424839 = 8137259) B8137259
theorem B4286303 : Blo 1268452 4286303 := bstep (se 1 (by rfl) ⟨3214727, by rfl⟩ : syracuseStep 4286303 = 6429455) B6429455
theorem B4818797 : Blo 1268452 4818797 := bstep (se 3 (by rfl) ⟨903524, by rfl⟩ : syracuseStep 4818797 = 1807049) B1807049
theorem B13715405 : Blo 1268452 13715405 := bstep (se 3 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 13715405 = 5143277) B5143277
theorem B4286465 : Blo 1268452 4286465 := bstep (se 2 (by rfl) ⟨1607424, by rfl⟩ : syracuseStep 4286465 = 3214849) B3214849
theorem B2320391 : Blo 1268452 2320391 := bstep (se 1 (by rfl) ⟨1740293, by rfl⟩ : syracuseStep 2320391 = 3480587) B3480587
theorem B8136719 : Blo 1268452 8136719 := bstep (se 1 (by rfl) ⟨6102539, by rfl⟩ : syracuseStep 8136719 = 12205079) B12205079
theorem B2410553 : Blo 1268452 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B3213391 : Blo 1268452 3213391 := bstep (se 1 (by rfl) ⟨2410043, by rfl⟩ : syracuseStep 3213391 = 4820087) B4820087
theorem B9635921 : Blo 1268452 9635921 := bstep (se 2 (by rfl) ⟨3613470, by rfl⟩ : syracuseStep 9635921 = 7226941) B7226941
theorem B12208229 : Blo 1268452 12208229 := bstep (se 4 (by rfl) ⟨1144521, by rfl⟩ : syracuseStep 12208229 = 2289043) B2289043
theorem B8128669 : Blo 1268452 8128669 := bstep (se 3 (by rfl) ⟨1524125, by rfl⟩ : syracuseStep 8128669 = 3048251) B3048251
theorem B4819115 : Blo 1268452 4819115 := bstep (se 1 (by rfl) ⟨3614336, by rfl⟩ : syracuseStep 4819115 = 7228673) B7228673
theorem B1902791 : Blo 1268452 1902791 := bstep (se 1 (by rfl) ⟨1427093, by rfl⟩ : syracuseStep 1902791 = 2854187) B2854187
theorem B6424919 : Blo 1268452 6424919 := bstep (se 1 (by rfl) ⟨4818689, by rfl⟩ : syracuseStep 6424919 = 9637379) B9637379
theorem B1902953 : Blo 1268452 1902953 := bstep (se 2 (by rfl) ⟨713607, by rfl⟩ : syracuseStep 1902953 = 1427215) B1427215
theorem B3615101 : Blo 1268452 3615101 := bstep (se 3 (by rfl) ⟨677831, by rfl⟩ : syracuseStep 3615101 = 1355663) B1355663
theorem B5425537 : Blo 1268452 5425537 := bstep (se 2 (by rfl) ⟨2034576, by rfl⟩ : syracuseStep 5425537 = 4069153) B4069153
theorem B1903031 : Blo 1268452 1903031 := bstep (se 1 (by rfl) ⟨1427273, by rfl⟩ : syracuseStep 1903031 = 2854547) B2854547
theorem B1903067 : Blo 1268452 1903067 := bstep (se 1 (by rfl) ⟨1427300, by rfl⟩ : syracuseStep 1903067 = 2854601) B2854601
theorem B2140681 : Blo 1268452 2140681 := bstep (se 2 (by rfl) ⟨802755, by rfl⟩ : syracuseStep 2140681 = 1605511) B1605511
theorem B4573705 : Blo 1268452 4573705 := bstep (se 2 (by rfl) ⟨1715139, by rfl⟩ : syracuseStep 4573705 = 3430279) B3430279
theorem B1428007 : Blo 1268452 1428007 := bstep (se 1 (by rfl) ⟨1071005, by rfl⟩ : syracuseStep 1428007 = 2142011) B2142011
theorem B2288207 : Blo 1268452 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B2140843 : Blo 1268452 2140843 := bstep (se 1 (by rfl) ⟨1605632, by rfl⟩ : syracuseStep 2140843 = 3211265) B3211265
theorem B6859475 : Blo 1268452 6859475 := bstep (se 1 (by rfl) ⟨5144606, by rfl⟩ : syracuseStep 6859475 = 10289213) B10289213
theorem B6097619 : Blo 1268452 6097619 := bstep (se 1 (by rfl) ⟨4573214, by rfl⟩ : syracuseStep 6097619 = 9146429) B9146429
theorem B3214039 : Blo 1268452 3214039 := bstep (se 1 (by rfl) ⟨2410529, by rfl⟩ : syracuseStep 3214039 = 4821059) B4821059
theorem B4287275 : Blo 1268452 4287275 := bstep (se 1 (by rfl) ⟨3215456, by rfl⟩ : syracuseStep 4287275 = 6430913) B6430913
theorem B1903535 : Blo 1268452 1903535 := bstep (se 1 (by rfl) ⟨1427651, by rfl⟩ : syracuseStep 1903535 = 2855303) B2855303
theorem B2141147 : Blo 1268452 2141147 := bstep (se 1 (by rfl) ⟨1605860, by rfl⟩ : syracuseStep 2141147 = 3211721) B3211721
theorem B3214343 : Blo 1268452 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B1903625 : Blo 1268452 1903625 := bstep (se 2 (by rfl) ⟨713859, by rfl⟩ : syracuseStep 1903625 = 1427719) B1427719
theorem B1903655 : Blo 1268452 1903655 := bstep (se 1 (by rfl) ⟨1427741, by rfl⟩ : syracuseStep 1903655 = 2855483) B2855483
theorem B4287545 : Blo 1268452 4287545 := bstep (se 2 (by rfl) ⟨1607829, by rfl⟩ : syracuseStep 4287545 = 3215659) B3215659
theorem B1903739 : Blo 1268452 1903739 := bstep (se 1 (by rfl) ⟨1427804, by rfl⟩ : syracuseStep 1903739 = 2855609) B2855609
theorem B5147819 : Blo 1268452 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B2141383 : Blo 1268452 2141383 := bstep (se 1 (by rfl) ⟨1606037, by rfl⟩ : syracuseStep 2141383 = 3212075) B3212075
theorem B1903865 : Blo 1268452 1903865 := bstep (se 2 (by rfl) ⟨713949, by rfl⟩ : syracuseStep 1903865 = 1427899) B1427899
theorem B1903967 : Blo 1268452 1903967 := bstep (se 1 (by rfl) ⟨1427975, by rfl⟩ : syracuseStep 1903967 = 2855951) B2855951
theorem B2141545 : Blo 1268452 2141545 := bstep (se 2 (by rfl) ⟨803079, by rfl⟩ : syracuseStep 2141545 = 1606159) B1606159
theorem B4574569 : Blo 1268452 4574569 := bstep (se 2 (by rfl) ⟨1715463, by rfl⟩ : syracuseStep 4574569 = 3430927) B3430927
theorem B1903979 : Blo 1268452 1903979 := bstep (se 1 (by rfl) ⟨1427984, by rfl⟩ : syracuseStep 1903979 = 2855969) B2855969
theorem B8678951 : Blo 1268452 8678951 := bstep (se 1 (by rfl) ⟨6509213, by rfl⟩ : syracuseStep 8678951 = 13018427) B13018427
theorem B2854439 : Blo 1268452 2854439 := bstep (se 1 (by rfl) ⟨2140829, by rfl⟩ : syracuseStep 2854439 = 4281659) B4281659
theorem B1904207 : Blo 1268452 1904207 := bstep (se 1 (by rfl) ⟨1428155, by rfl⟩ : syracuseStep 1904207 = 2856311) B2856311
theorem B8679059 : Blo 1268452 8679059 := bstep (se 1 (by rfl) ⟨6509294, by rfl⟩ : syracuseStep 8679059 = 13018589) B13018589
theorem B1904327 : Blo 1268452 1904327 := bstep (se 1 (by rfl) ⟨1428245, by rfl⟩ : syracuseStep 1904327 = 2856491) B2856491
theorem B12209885 : Blo 1268452 12209885 := bstep (se 3 (by rfl) ⟨2289353, by rfl⟩ : syracuseStep 12209885 = 4578707) B4578707
theorem B1904489 : Blo 1268452 1904489 := bstep (se 2 (by rfl) ⟨714183, by rfl⟩ : syracuseStep 1904489 = 1428367) B1428367
theorem B2854763 : Blo 1268452 2854763 := bstep (se 1 (by rfl) ⟨2141072, by rfl⟩ : syracuseStep 2854763 = 4282145) B4282145
theorem B2854817 : Blo 1268452 2854817 := bstep (se 2 (by rfl) ⟨1070556, by rfl⟩ : syracuseStep 2854817 = 2141113) B2141113
theorem B1904567 : Blo 1268452 1904567 := bstep (se 1 (by rfl) ⟨1428425, by rfl⟩ : syracuseStep 1904567 = 2856851) B2856851
theorem B2142139 : Blo 1268452 2142139 := bstep (se 1 (by rfl) ⟨1606604, by rfl⟩ : syracuseStep 2142139 = 3213209) B3213209
theorem B1904603 : Blo 1268452 1904603 := bstep (se 1 (by rfl) ⟨1428452, by rfl⟩ : syracuseStep 1904603 = 2856905) B2856905
theorem B3616775 : Blo 1268452 3616775 := bstep (se 1 (by rfl) ⟨2712581, by rfl⟩ : syracuseStep 3616775 = 5425163) B5425163
theorem B2142247 : Blo 1268452 2142247 := bstep (se 1 (by rfl) ⟨1606685, by rfl⟩ : syracuseStep 2142247 = 3213371) B3213371
theorem B2855159 : Blo 1268452 2855159 := bstep (se 1 (by rfl) ⟨2141369, by rfl⟩ : syracuseStep 2855159 = 4282739) B4282739
theorem B9154903 : Blo 1268452 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B6861161 : Blo 1268452 6861161 := bstep (se 2 (by rfl) ⟨2572935, by rfl⟩ : syracuseStep 6861161 = 5145871) B5145871
theorem B2142571 : Blo 1268452 2142571 := bstep (se 1 (by rfl) ⟨1606928, by rfl⟩ : syracuseStep 2142571 = 3213857) B3213857
theorem B167006609 : Blo 1268452 167006609 := bstep (se 2 (by rfl) ⟨62627478, by rfl⟩ : syracuseStep 167006609 = 125254957) B125254957
theorem B1905071 : Blo 1268452 1905071 := bstep (se 1 (by rfl) ⟨1428803, by rfl⟩ : syracuseStep 1905071 = 2857607) B2857607
theorem B3052019 : Blo 1268452 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B1905161 : Blo 1268452 1905161 := bstep (se 2 (by rfl) ⟨714435, by rfl⟩ : syracuseStep 1905161 = 1428871) B1428871
theorem B1905191 : Blo 1268452 1905191 := bstep (se 1 (by rfl) ⟨1428893, by rfl⟩ : syracuseStep 1905191 = 2857787) B2857787
theorem B7328315 : Blo 1268452 7328315 := bstep (se 1 (by rfl) ⟨5496236, by rfl⟩ : syracuseStep 7328315 = 10992473) B10992473
theorem B1905275 : Blo 1268452 1905275 := bstep (se 1 (by rfl) ⟨1428956, by rfl⟩ : syracuseStep 1905275 = 2857913) B2857913
theorem B4067975 : Blo 1268452 4067975 := bstep (se 1 (by rfl) ⟨3050981, by rfl⟩ : syracuseStep 4067975 = 6101963) B6101963
theorem B4575953 : Blo 1268452 4575953 := bstep (se 2 (by rfl) ⟨1715982, by rfl⟩ : syracuseStep 4575953 = 3431965) B3431965
theorem B4821713 : Blo 1268452 4821713 := bstep (se 2 (by rfl) ⟨1808142, by rfl⟩ : syracuseStep 4821713 = 3616285) B3616285
theorem B1905401 : Blo 1268452 1905401 := bstep (se 2 (by rfl) ⟨714525, by rfl⟩ : syracuseStep 1905401 = 1429051) B1429051
theorem B2855753 : Blo 1268452 2855753 := bstep (se 2 (by rfl) ⟨1070907, by rfl⟩ : syracuseStep 2855753 = 2141815) B2141815
theorem B1905503 : Blo 1268452 1905503 := bstep (se 1 (by rfl) ⟨1429127, by rfl⟩ : syracuseStep 1905503 = 2858255) B2858255
theorem B1905515 : Blo 1268452 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B7426991 : Blo 1268452 7426991 := bstep (se 1 (by rfl) ⟨5570243, by rfl⟩ : syracuseStep 7426991 = 11140487) B11140487
theorem B7230383 : Blo 1268452 7230383 := bstep (se 1 (by rfl) ⟨5422787, by rfl⟩ : syracuseStep 7230383 = 10845575) B10845575
theorem B2749367 : Blo 1268452 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B4822031 : Blo 1268452 4822031 := bstep (se 1 (by rfl) ⟨3616523, by rfl⟩ : syracuseStep 4822031 = 7233047) B7233047
theorem B10286099 : Blo 1268452 10286099 := bstep (se 1 (by rfl) ⟨7714574, by rfl⟩ : syracuseStep 10286099 = 15429149) B15429149
theorem B10851347 : Blo 1268452 10851347 := bstep (se 1 (by rfl) ⟨8138510, by rfl⟩ : syracuseStep 10851347 = 16277021) B16277021
theorem B16266359 : Blo 1268452 16266359 := bstep (se 1 (by rfl) ⟨12199769, by rfl⟩ : syracuseStep 16266359 = 24399539) B24399539
theorem B4281497 : Blo 1268452 4281497 := bstep (se 2 (by rfl) ⟨1605561, by rfl⟩ : syracuseStep 4281497 = 3211123) B3211123
theorem B3429533 : Blo 1268452 3429533 := bstep (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) B1286075
theorem B2143631 : Blo 1268452 2143631 := bstep (se 1 (by rfl) ⟨1607723, by rfl⟩ : syracuseStep 2143631 = 3215447) B3215447
theorem B9147811 : Blo 1268452 9147811 := bstep (se 1 (by rfl) ⟨6860858, by rfl⟩ : syracuseStep 9147811 = 13721717) B13721717
theorem B12531145 : Blo 1268452 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B2856545 : Blo 1268452 2856545 := bstep (se 2 (by rfl) ⟨1071204, by rfl⟩ : syracuseStep 2856545 = 2142409) B2142409
theorem B2143867 : Blo 1268452 2143867 := bstep (se 1 (by rfl) ⟨1607900, by rfl⟩ : syracuseStep 2143867 = 3215801) B3215801
theorem B18306809 : Blo 1268452 18306809 := bstep (se 2 (by rfl) ⟨6865053, by rfl⟩ : syracuseStep 18306809 = 13730107) B13730107
theorem B6428483 : Blo 1268452 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B2856887 : Blo 1268452 2856887 := bstep (se 1 (by rfl) ⟨2142665, by rfl⟩ : syracuseStep 2856887 = 4285331) B4285331
theorem B1808507 : Blo 1268452 1808507 := bstep (se 1 (by rfl) ⟨1356380, by rfl⟩ : syracuseStep 1808507 = 2712761) B2712761
theorem B4282685 : Blo 1268452 4282685 := bstep (se 3 (by rfl) ⟨803003, by rfl⟩ : syracuseStep 4282685 = 1606007) B1606007
theorem B4577597 : Blo 1268452 4577597 := bstep (se 3 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 4577597 = 1716599) B1716599
theorem B4069757 : Blo 1268452 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B13728203 : Blo 1268452 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B2857481 : Blo 1268452 2857481 := bstep (se 2 (by rfl) ⟨1071555, by rfl⟩ : syracuseStep 2857481 = 2143111) B2143111
theorem B1833511 : Blo 1268452 1833511 := bstep (se 1 (by rfl) ⟨1375133, by rfl⟩ : syracuseStep 1833511 = 2750267) B2750267
theorem B1448527 : Blo 1268452 1448527 := bstep (se 1 (by rfl) ⟨1086395, by rfl⟩ : syracuseStep 1448527 = 2172791) B2172791
theorem B5421779 : Blo 1268452 5421779 := bstep (se 1 (by rfl) ⟨4066334, by rfl⟩ : syracuseStep 5421779 = 8132669) B8132669
theorem B3431123 : Blo 1268452 3431123 := bstep (se 1 (by rfl) ⟨2573342, by rfl⟩ : syracuseStep 3431123 = 5146685) B5146685
theorem B70441757 : Blo 1268452 70441757 := bstep (se 3 (by rfl) ⟨13207829, by rfl⟩ : syracuseStep 70441757 = 26415659) B26415659
theorem B1268519 : Blo 1268452 1268519 := bstep (se 1 (by rfl) ⟨951389, by rfl⟩ : syracuseStep 1268519 = 1902779) B1902779
theorem B9640781 : Blo 1268452 9640781 := bstep (se 3 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 9640781 = 3615293) B3615293
theorem B1268559 : Blo 1268452 1268559 := bstep (se 1 (by rfl) ⟨951419, by rfl⟩ : syracuseStep 1268559 = 1902839) B1902839
theorem B1268575 : Blo 1268452 1268575 := bstep (se 1 (by rfl) ⟨951431, by rfl⟩ : syracuseStep 1268575 = 1902863) B1902863
theorem B3431263 : Blo 1268452 3431263 := bstep (se 1 (by rfl) ⟨2573447, by rfl⟩ : syracuseStep 3431263 = 5146895) B5146895
theorem B2857823 : Blo 1268452 2857823 := bstep (se 1 (by rfl) ⟨2143367, by rfl⟩ : syracuseStep 2857823 = 4286735) B4286735
theorem B6101867 : Blo 1268452 6101867 := bstep (se 1 (by rfl) ⟨4576400, by rfl⟩ : syracuseStep 6101867 = 9152801) B9152801
theorem B1268603 : Blo 1268452 1268603 := bstep (se 1 (by rfl) ⟨951452, by rfl⟩ : syracuseStep 1268603 = 1902905) B1902905
theorem B1268655 : Blo 1268452 1268655 := bstep (se 1 (by rfl) ⟨951491, by rfl⟩ : syracuseStep 1268655 = 1902983) B1902983
theorem B1268679 : Blo 1268452 1268679 := bstep (se 1 (by rfl) ⟨951509, by rfl⟩ : syracuseStep 1268679 = 1903019) B1903019
theorem B1268699 : Blo 1268452 1268699 := bstep (se 1 (by rfl) ⟨951524, by rfl⟩ : syracuseStep 1268699 = 1903049) B1903049
theorem B2858003 : Blo 1268452 2858003 := bstep (se 1 (by rfl) ⟨2143502, by rfl⟩ : syracuseStep 2858003 = 4287005) B4287005
theorem B1268775 : Blo 1268452 1268775 := bstep (se 1 (by rfl) ⟨951581, by rfl⟩ : syracuseStep 1268775 = 1903163) B1903163
theorem B1268815 : Blo 1268452 1268815 := bstep (se 1 (by rfl) ⟨951611, by rfl⟩ : syracuseStep 1268815 = 1903223) B1903223
theorem B7232591 : Blo 1268452 7232591 := bstep (se 1 (by rfl) ⟨5424443, by rfl⟩ : syracuseStep 7232591 = 10848887) B10848887
theorem B1268831 : Blo 1268452 1268831 := bstep (se 1 (by rfl) ⟨951623, by rfl⟩ : syracuseStep 1268831 = 1903247) B1903247
theorem B1268859 : Blo 1268452 1268859 := bstep (se 1 (by rfl) ⟨951644, by rfl⟩ : syracuseStep 1268859 = 1903289) B1903289
theorem B4283549 : Blo 1268452 4283549 := bstep (se 3 (by rfl) ⟨803165, by rfl⟩ : syracuseStep 4283549 = 1606331) B1606331
theorem B1268911 : Blo 1268452 1268911 := bstep (se 1 (by rfl) ⟨951683, by rfl⟩ : syracuseStep 1268911 = 1903367) B1903367
theorem B1268935 : Blo 1268452 1268935 := bstep (se 1 (by rfl) ⟨951701, by rfl⟩ : syracuseStep 1268935 = 1903403) B1903403
theorem B1268955 : Blo 1268452 1268955 := bstep (se 1 (by rfl) ⟨951716, by rfl⟩ : syracuseStep 1268955 = 1903433) B1903433
theorem B1269031 : Blo 1268452 1269031 := bstep (se 1 (by rfl) ⟨951773, by rfl⟩ : syracuseStep 1269031 = 1903547) B1903547
theorem B1269071 : Blo 1268452 1269071 := bstep (se 1 (by rfl) ⟨951803, by rfl⟩ : syracuseStep 1269071 = 1903607) B1903607
theorem B1269087 : Blo 1268452 1269087 := bstep (se 1 (by rfl) ⟨951815, by rfl⟩ : syracuseStep 1269087 = 1903631) B1903631
theorem B2858345 : Blo 1268452 2858345 := bstep (se 2 (by rfl) ⟨1071879, by rfl⟩ : syracuseStep 2858345 = 2143759) B2143759
theorem B1269115 : Blo 1268452 1269115 := bstep (se 1 (by rfl) ⟨951836, by rfl⟩ : syracuseStep 1269115 = 1903673) B1903673
theorem B1269167 : Blo 1268452 1269167 := bstep (se 1 (by rfl) ⟨951875, by rfl⟩ : syracuseStep 1269167 = 1903751) B1903751
theorem B1269191 : Blo 1268452 1269191 := bstep (se 1 (by rfl) ⟨951893, by rfl⟩ : syracuseStep 1269191 = 1903787) B1903787
theorem B1269211 : Blo 1268452 1269211 := bstep (se 1 (by rfl) ⟨951908, by rfl⟩ : syracuseStep 1269211 = 1903817) B1903817
theorem B6422003 : Blo 1268452 6422003 := bstep (se 1 (by rfl) ⟨4816502, by rfl⟩ : syracuseStep 6422003 = 9633005) B9633005
theorem B3055091 : Blo 1268452 3055091 := bstep (se 1 (by rfl) ⟨2291318, by rfl⟩ : syracuseStep 3055091 = 4582637) B4582637
theorem B3612185 : Blo 1268452 3612185 := bstep (se 2 (by rfl) ⟨1354569, by rfl⟩ : syracuseStep 3612185 = 2709139) B2709139
theorem B1269287 : Blo 1268452 1269287 := bstep (se 1 (by rfl) ⟨951965, by rfl⟩ : syracuseStep 1269287 = 1903931) B1903931
theorem B2571833 : Blo 1268452 2571833 := bstep (se 2 (by rfl) ⟨964437, by rfl⟩ : syracuseStep 2571833 = 1928875) B1928875
theorem B1269327 : Blo 1268452 1269327 := bstep (se 1 (by rfl) ⟨951995, by rfl⟩ : syracuseStep 1269327 = 1903991) B1903991
theorem B1269343 : Blo 1268452 1269343 := bstep (se 1 (by rfl) ⟨952007, by rfl⟩ : syracuseStep 1269343 = 1904015) B1904015
theorem B3858043 : Blo 1268452 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1269371 : Blo 1268452 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B1269423 : Blo 1268452 1269423 := bstep (se 1 (by rfl) ⟨952067, by rfl⟩ : syracuseStep 1269423 = 1904135) B1904135
theorem B4284089 : Blo 1268452 4284089 := bstep (se 2 (by rfl) ⟨1606533, by rfl⟩ : syracuseStep 4284089 = 3213067) B3213067
theorem B1269447 : Blo 1268452 1269447 := bstep (se 1 (by rfl) ⟨952085, by rfl⟩ : syracuseStep 1269447 = 1904171) B1904171
theorem B3858131 : Blo 1268452 3858131 := bstep (se 1 (by rfl) ⟨2893598, by rfl⟩ : syracuseStep 3858131 = 5787197) B5787197
theorem B1269467 : Blo 1268452 1269467 := bstep (se 1 (by rfl) ⟨952100, by rfl⟩ : syracuseStep 1269467 = 1904201) B1904201
theorem B1269543 : Blo 1268452 1269543 := bstep (se 1 (by rfl) ⟨952157, by rfl⟩ : syracuseStep 1269543 = 1904315) B1904315
theorem B1269583 : Blo 1268452 1269583 := bstep (se 1 (by rfl) ⟨952187, by rfl⟩ : syracuseStep 1269583 = 1904375) B1904375
theorem B3211103 : Blo 1268452 3211103 := bstep (se 1 (by rfl) ⟨2408327, by rfl⟩ : syracuseStep 3211103 = 4816655) B4816655
theorem B1269599 : Blo 1268452 1269599 := bstep (se 1 (by rfl) ⟨952199, by rfl⟩ : syracuseStep 1269599 = 1904399) B1904399
theorem B1269627 : Blo 1268452 1269627 := bstep (se 1 (by rfl) ⟨952220, by rfl⟩ : syracuseStep 1269627 = 1904441) B1904441
theorem B1269679 : Blo 1268452 1269679 := bstep (se 1 (by rfl) ⟨952259, by rfl⟩ : syracuseStep 1269679 = 1904519) B1904519
theorem B1269703 : Blo 1268452 1269703 := bstep (se 1 (by rfl) ⟨952277, by rfl⟩ : syracuseStep 1269703 = 1904555) B1904555
theorem B1269723 : Blo 1268452 1269723 := bstep (se 1 (by rfl) ⟨952292, by rfl⟩ : syracuseStep 1269723 = 1904585) B1904585
theorem B4284521 : Blo 1268452 4284521 := bstep (se 2 (by rfl) ⟨1606695, by rfl⟩ : syracuseStep 4284521 = 3213391) B3213391
theorem B10838225 : Blo 1268452 10838225 := bstep (se 2 (by rfl) ⟨4064334, by rfl⟩ : syracuseStep 10838225 = 8128669) B8128669
theorem B111337739 : Blo 1268452 111337739 := bstep (se 1 (by rfl) ⟨83503304, by rfl⟩ : syracuseStep 111337739 = 167006609) B167006609
theorem B1270047 : Blo 1268452 1270047 := bstep (se 1 (by rfl) ⟨952535, by rfl⟩ : syracuseStep 1270047 = 1905071) B1905071
theorem B1270107 : Blo 1268452 1270107 := bstep (se 1 (by rfl) ⟨952580, by rfl⟩ : syracuseStep 1270107 = 1905161) B1905161
theorem B1270127 : Blo 1268452 1270127 := bstep (se 1 (by rfl) ⟨952595, by rfl⟩ : syracuseStep 1270127 = 1905191) B1905191
theorem B1270183 : Blo 1268452 1270183 := bstep (se 1 (by rfl) ⟨952637, by rfl⟩ : syracuseStep 1270183 = 1905275) B1905275
theorem B2711983 : Blo 1268452 2711983 := bstep (se 1 (by rfl) ⟨2033987, by rfl⟩ : syracuseStep 2711983 = 4067975) B4067975
theorem B12206537 : Blo 1268452 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B3211771 : Blo 1268452 3211771 := bstep (se 1 (by rfl) ⟨2408828, by rfl⟩ : syracuseStep 3211771 = 4817657) B4817657
theorem B1270267 : Blo 1268452 1270267 := bstep (se 1 (by rfl) ⟨952700, by rfl⟩ : syracuseStep 1270267 = 1905401) B1905401
theorem B7234049 : Blo 1268452 7234049 := bstep (se 2 (by rfl) ⟨2712768, by rfl⟩ : syracuseStep 7234049 = 5425537) B5425537
theorem B1270335 : Blo 1268452 1270335 := bstep (se 1 (by rfl) ⟨952751, by rfl⟩ : syracuseStep 1270335 = 1905503) B1905503
theorem B1270343 : Blo 1268452 1270343 := bstep (se 1 (by rfl) ⟨952757, by rfl⟩ : syracuseStep 1270343 = 1905515) B1905515
theorem B6423137 : Blo 1268452 6423137 := bstep (se 2 (by rfl) ⟨2408676, by rfl⟩ : syracuseStep 6423137 = 4817353) B4817353
theorem B3211883 : Blo 1268452 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B6857399 : Blo 1268452 6857399 := bstep (se 1 (by rfl) ⟨5143049, by rfl⟩ : syracuseStep 6857399 = 10286099) B10286099
theorem B7234231 : Blo 1268452 7234231 := bstep (se 1 (by rfl) ⟨5425673, by rfl⟩ : syracuseStep 7234231 = 10851347) B10851347
theorem B2286355 : Blo 1268452 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B4285385 : Blo 1268452 4285385 := bstep (se 2 (by rfl) ⟨1607019, by rfl⟩ : syracuseStep 4285385 = 3214039) B3214039
theorem B4285655 : Blo 1268452 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B4064489 : Blo 1268452 4064489 := bstep (se 2 (by rfl) ⟨1524183, by rfl⟩ : syracuseStep 4064489 = 3048367) B3048367
theorem B6423785 : Blo 1268452 6423785 := bstep (se 2 (by rfl) ⟨2408919, by rfl⟩ : syracuseStep 6423785 = 4817839) B4817839
theorem B3212531 : Blo 1268452 3212531 := bstep (se 1 (by rfl) ⟨2409398, by rfl⟩ : syracuseStep 3212531 = 4818797) B4818797
theorem B9143603 : Blo 1268452 9143603 := bstep (se 1 (by rfl) ⟨6857702, by rfl⟩ : syracuseStep 9143603 = 13715405) B13715405
theorem B5424479 : Blo 1268452 5424479 := bstep (se 1 (by rfl) ⟨4068359, by rfl⟩ : syracuseStep 5424479 = 8136719) B8136719
theorem B1607035 : Blo 1268452 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B6423947 : Blo 1268452 6423947 := bstep (se 1 (by rfl) ⟨4817960, by rfl⟩ : syracuseStep 6423947 = 9635921) B9635921
theorem B3212743 : Blo 1268452 3212743 := bstep (se 1 (by rfl) ⟨2409557, by rfl⟩ : syracuseStep 3212743 = 4819115) B4819115
theorem B2410067 : Blo 1268452 2410067 := bstep (se 1 (by rfl) ⟨1807550, by rfl⟩ : syracuseStep 2410067 = 3615101) B3615101
theorem B2713171 : Blo 1268452 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B9152135 : Blo 1268452 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B13723357 : Blo 1268452 13723357 := bstep (se 3 (by rfl) ⟨2573129, by rfl⟩ : syracuseStep 13723357 = 5146259) B5146259
theorem B4572983 : Blo 1268452 4572983 := bstep (se 1 (by rfl) ⟨3429737, by rfl⟩ : syracuseStep 4572983 = 6859475) B6859475
theorem B4065079 : Blo 1268452 4065079 := bstep (se 1 (by rfl) ⟨3048809, by rfl⟩ : syracuseStep 4065079 = 6097619) B6097619
theorem B3614519 : Blo 1268452 3614519 := bstep (se 1 (by rfl) ⟨2710889, by rfl⟩ : syracuseStep 3614519 = 5421779) B5421779
theorem B2287415 : Blo 1268452 2287415 := bstep (se 1 (by rfl) ⟨1715561, by rfl⟩ : syracuseStep 2287415 = 3431123) B3431123
theorem B1427431 : Blo 1268452 1427431 := bstep (se 1 (by rfl) ⟨1070573, by rfl⟩ : syracuseStep 1427431 = 2141147) B2141147
theorem B30902465 : Blo 1268452 30902465 := bstep (se 2 (by rfl) ⟨11588424, by rfl⟩ : syracuseStep 30902465 = 23176849) B23176849
theorem B16255241 : Blo 1268452 16255241 := bstep (se 2 (by rfl) ⟨6095715, by rfl⟩ : syracuseStep 16255241 = 12191431) B12191431
theorem B1902857 : Blo 1268452 1902857 := bstep (se 2 (by rfl) ⟨713571, by rfl⟩ : syracuseStep 1902857 = 1427143) B1427143
theorem B4065565 : Blo 1268452 4065565 := bstep (se 3 (by rfl) ⟨762293, by rfl⟩ : syracuseStep 4065565 = 1524587) B1524587
theorem B5785967 : Blo 1268452 5785967 := bstep (se 1 (by rfl) ⟨4339475, by rfl⟩ : syracuseStep 5785967 = 8678951) B8678951
theorem B1902959 : Blo 1268452 1902959 := bstep (se 1 (by rfl) ⟨1427219, by rfl⟩ : syracuseStep 1902959 = 2854439) B2854439
theorem B1714555 : Blo 1268452 1714555 := bstep (se 1 (by rfl) ⟨1285916, by rfl⟩ : syracuseStep 1714555 = 2571833) B2571833
theorem B5786039 : Blo 1268452 5786039 := bstep (se 1 (by rfl) ⟨4339529, by rfl⟩ : syracuseStep 5786039 = 8679059) B8679059
theorem B2140735 : Blo 1268452 2140735 := bstep (se 1 (by rfl) ⟨1605551, by rfl⟩ : syracuseStep 2140735 = 3211103) B3211103
theorem B1903175 : Blo 1268452 1903175 := bstep (se 1 (by rfl) ⟨1427381, by rfl⟩ : syracuseStep 1903175 = 2854763) B2854763
theorem B1903211 : Blo 1268452 1903211 := bstep (se 1 (by rfl) ⟨1427408, by rfl⟩ : syracuseStep 1903211 = 2854817) B2854817
theorem B2411183 : Blo 1268452 2411183 := bstep (se 1 (by rfl) ⟨1808387, by rfl⟩ : syracuseStep 2411183 = 3616775) B3616775
theorem B6187709 : Blo 1268452 6187709 := bstep (se 3 (by rfl) ⟨1160195, by rfl⟩ : syracuseStep 6187709 = 2320391) B2320391
theorem B52824797 : Blo 1268452 52824797 := bstep (se 3 (by rfl) ⟨9904649, by rfl⟩ : syracuseStep 52824797 = 19809299) B19809299
theorem B10840823 : Blo 1268452 10840823 := bstep (se 1 (by rfl) ⟨8130617, by rfl⟩ : syracuseStep 10840823 = 16261235) B16261235
theorem B1903439 : Blo 1268452 1903439 := bstep (se 1 (by rfl) ⟨1427579, by rfl⟩ : syracuseStep 1903439 = 2855159) B2855159
theorem B4574107 : Blo 1268452 4574107 := bstep (se 1 (by rfl) ⟨3430580, by rfl⟩ : syracuseStep 4574107 = 6861161) B6861161
theorem B4885543 : Blo 1268452 4885543 := bstep (se 1 (by rfl) ⟨3664157, by rfl⟩ : syracuseStep 4885543 = 7328315) B7328315
theorem B3050635 : Blo 1268452 3050635 := bstep (se 1 (by rfl) ⟨2287976, by rfl⟩ : syracuseStep 3050635 = 4575953) B4575953
theorem B3214475 : Blo 1268452 3214475 := bstep (se 1 (by rfl) ⟨2410856, by rfl⟩ : syracuseStep 3214475 = 4821713) B4821713
theorem B1903835 : Blo 1268452 1903835 := bstep (se 1 (by rfl) ⟨1427876, by rfl⟩ : syracuseStep 1903835 = 2855753) B2855753
theorem B4287707 : Blo 1268452 4287707 := bstep (se 1 (by rfl) ⟨3215780, by rfl⟩ : syracuseStep 4287707 = 6431561) B6431561
theorem B2141417 : Blo 1268452 2141417 := bstep (se 2 (by rfl) ⟨803031, by rfl⟩ : syracuseStep 2141417 = 1606063) B1606063
theorem B2141471 : Blo 1268452 2141471 := bstep (se 1 (by rfl) ⟨1606103, by rfl⟩ : syracuseStep 2141471 = 3212207) B3212207
theorem B4951327 : Blo 1268452 4951327 := bstep (se 1 (by rfl) ⟨3713495, by rfl⟩ : syracuseStep 4951327 = 7426991) B7426991
theorem B4820255 : Blo 1268452 4820255 := bstep (se 1 (by rfl) ⟨3615191, by rfl⟩ : syracuseStep 4820255 = 7230383) B7230383
theorem B3091751 : Blo 1268452 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B3214687 : Blo 1268452 3214687 := bstep (se 1 (by rfl) ⟨2411015, by rfl⟩ : syracuseStep 3214687 = 4822031) B4822031
theorem B2854241 : Blo 1268452 2854241 := bstep (se 2 (by rfl) ⟨1070340, by rfl⟩ : syracuseStep 2854241 = 2140681) B2140681
theorem B6098273 : Blo 1268452 6098273 := bstep (se 2 (by rfl) ⟨2286852, by rfl⟩ : syracuseStep 6098273 = 4573705) B4573705
theorem B1904009 : Blo 1268452 1904009 := bstep (se 2 (by rfl) ⟨714003, by rfl⟩ : syracuseStep 1904009 = 1428007) B1428007
theorem B2444681 : Blo 1268452 2444681 := bstep (se 2 (by rfl) ⟨916755, by rfl⟩ : syracuseStep 2444681 = 1833511) B1833511
theorem B2854331 : Blo 1268452 2854331 := bstep (se 1 (by rfl) ⟨2140748, by rfl⟩ : syracuseStep 2854331 = 4281497) B4281497
theorem B2854457 : Blo 1268452 2854457 := bstep (se 2 (by rfl) ⟨1070421, by rfl⟩ : syracuseStep 2854457 = 2140843) B2140843
theorem B1429087 : Blo 1268452 1429087 := bstep (se 1 (by rfl) ⟨1071815, by rfl⟩ : syracuseStep 1429087 = 2143631) B2143631
theorem B1904363 : Blo 1268452 1904363 := bstep (se 1 (by rfl) ⟨1428272, by rfl⟩ : syracuseStep 1904363 = 2856545) B2856545
theorem B4575017 : Blo 1268452 4575017 := bstep (se 2 (by rfl) ⟨1715631, by rfl⟩ : syracuseStep 4575017 = 3431263) B3431263
theorem B3616559 : Blo 1268452 3616559 := bstep (se 1 (by rfl) ⟨2712419, by rfl⟩ : syracuseStep 3616559 = 5424839) B5424839
theorem B1904591 : Blo 1268452 1904591 := bstep (se 1 (by rfl) ⟨1428443, by rfl⟩ : syracuseStep 1904591 = 2856887) B2856887
theorem B11579345 : Blo 1268452 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B8146909 : Blo 1268452 8146909 := bstep (se 3 (by rfl) ⟨1527545, by rfl⟩ : syracuseStep 8146909 = 3055091) B3055091
theorem B8138717 : Blo 1268452 8138717 := bstep (se 3 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 8138717 = 3052019) B3052019
theorem B8138819 : Blo 1268452 8138819 := bstep (se 1 (by rfl) ⟨6104114, by rfl⟩ : syracuseStep 8138819 = 12208229) B12208229
theorem B2855123 : Blo 1268452 2855123 := bstep (se 1 (by rfl) ⟨2141342, by rfl⟩ : syracuseStep 2855123 = 4282685) B4282685
theorem B3051731 : Blo 1268452 3051731 := bstep (se 1 (by rfl) ⟨2288798, by rfl⟩ : syracuseStep 3051731 = 4577597) B4577597
theorem B2855177 : Blo 1268452 2855177 := bstep (se 2 (by rfl) ⟨1070691, by rfl⟩ : syracuseStep 2855177 = 2141383) B2141383
theorem B1904987 : Blo 1268452 1904987 := bstep (se 1 (by rfl) ⟨1428740, by rfl⟩ : syracuseStep 1904987 = 2857481) B2857481
theorem B2855393 : Blo 1268452 2855393 := bstep (se 2 (by rfl) ⟨1070772, by rfl⟩ : syracuseStep 2855393 = 2141545) B2141545
theorem B6099425 : Blo 1268452 6099425 := bstep (se 2 (by rfl) ⟨2287284, by rfl⟩ : syracuseStep 6099425 = 4574569) B4574569
theorem B46961171 : Blo 1268452 46961171 := bstep (se 1 (by rfl) ⟨35220878, by rfl⟩ : syracuseStep 46961171 = 70441757) B70441757
theorem B6427187 : Blo 1268452 6427187 := bstep (se 1 (by rfl) ⟨4820390, by rfl⟩ : syracuseStep 6427187 = 9640781) B9640781
theorem B1905215 : Blo 1268452 1905215 := bstep (se 1 (by rfl) ⟨1428911, by rfl⟩ : syracuseStep 1905215 = 2857823) B2857823
theorem B4067911 : Blo 1268452 4067911 := bstep (se 1 (by rfl) ⟨3050933, by rfl⟩ : syracuseStep 4067911 = 6101867) B6101867
theorem B16708193 : Blo 1268452 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B2142841 : Blo 1268452 2142841 := bstep (se 2 (by rfl) ⟨803565, by rfl⟩ : syracuseStep 2142841 = 1607131) B1607131
theorem B2142895 : Blo 1268452 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B1905335 : Blo 1268452 1905335 := bstep (se 1 (by rfl) ⟨1429001, by rfl⟩ : syracuseStep 1905335 = 2858003) B2858003
theorem B4821727 : Blo 1268452 4821727 := bstep (se 1 (by rfl) ⟨3616295, by rfl⟩ : syracuseStep 4821727 = 7232591) B7232591
theorem B2855699 : Blo 1268452 2855699 := bstep (se 1 (by rfl) ⟨2141774, by rfl⟩ : syracuseStep 2855699 = 4283549) B4283549
theorem B1905563 : Blo 1268452 1905563 := bstep (se 1 (by rfl) ⟨1429172, by rfl⟩ : syracuseStep 1905563 = 2858345) B2858345
theorem B4281335 : Blo 1268452 4281335 := bstep (se 1 (by rfl) ⟨3211001, by rfl⟩ : syracuseStep 4281335 = 6422003) B6422003
theorem B2856059 : Blo 1268452 2856059 := bstep (se 1 (by rfl) ⟨2142044, by rfl⟩ : syracuseStep 2856059 = 4284089) B4284089
theorem B8139923 : Blo 1268452 8139923 := bstep (se 1 (by rfl) ⟨6104942, by rfl⟩ : syracuseStep 8139923 = 12209885) B12209885
theorem B2856185 : Blo 1268452 2856185 := bstep (se 2 (by rfl) ⟨1071069, by rfl⟩ : syracuseStep 2856185 = 2142139) B2142139
theorem B7230815 : Blo 1268452 7230815 := bstep (se 1 (by rfl) ⟨5423111, by rfl⟩ : syracuseStep 7230815 = 10846223) B10846223
theorem B4068731 : Blo 1268452 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B2856329 : Blo 1268452 2856329 := bstep (se 2 (by rfl) ⟨1071123, by rfl⟩ : syracuseStep 2856329 = 2142247) B2142247
theorem B34723235 : Blo 1268452 34723235 := bstep (se 1 (by rfl) ⟨26042426, by rfl⟩ : syracuseStep 34723235 = 52084853) B52084853
theorem B2856455 : Blo 1268452 2856455 := bstep (se 1 (by rfl) ⟨2142341, by rfl⟩ : syracuseStep 2856455 = 4284683) B4284683
theorem B4822685 : Blo 1268452 4822685 := bstep (se 3 (by rfl) ⟨904253, by rfl⟩ : syracuseStep 4822685 = 1808507) B1808507
theorem B2856635 : Blo 1268452 2856635 := bstep (se 1 (by rfl) ⟨2142476, by rfl⟩ : syracuseStep 2856635 = 4284953) B4284953
theorem B48813839 : Blo 1268452 48813839 := bstep (se 1 (by rfl) ⟨36610379, by rfl⟩ : syracuseStep 48813839 = 73220759) B73220759
theorem B2856761 : Blo 1268452 2856761 := bstep (se 2 (by rfl) ⟨1071285, by rfl⟩ : syracuseStep 2856761 = 2142571) B2142571
theorem B4282199 : Blo 1268452 4282199 := bstep (se 1 (by rfl) ⟨3211649, by rfl⟩ : syracuseStep 4282199 = 6423299) B6423299
theorem B1832911 : Blo 1268452 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B10844239 : Blo 1268452 10844239 := bstep (se 1 (by rfl) ⟨8133179, by rfl⟩ : syracuseStep 10844239 = 16266359) B16266359
theorem B24401999 : Blo 1268452 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B1931369 : Blo 1268452 1931369 := bstep (se 2 (by rfl) ⟨724263, by rfl⟩ : syracuseStep 1931369 = 1448527) B1448527
theorem B6428807 : Blo 1268452 6428807 := bstep (se 1 (by rfl) ⟨4821605, by rfl⟩ : syracuseStep 6428807 = 9643211) B9643211
theorem B5421437 : Blo 1268452 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B2857391 : Blo 1268452 2857391 := bstep (se 1 (by rfl) ⟨2143043, by rfl⟩ : syracuseStep 2857391 = 4286087) B4286087
theorem B2857427 : Blo 1268452 2857427 := bstep (se 1 (by rfl) ⟨2143070, by rfl⟩ : syracuseStep 2857427 = 4286141) B4286141
theorem B12204539 : Blo 1268452 12204539 := bstep (se 1 (by rfl) ⟨9153404, by rfl⟩ : syracuseStep 12204539 = 18306809) B18306809
theorem B2857535 : Blo 1268452 2857535 := bstep (se 1 (by rfl) ⟨2143151, by rfl⟩ : syracuseStep 2857535 = 4286303) B4286303
theorem B2857643 : Blo 1268452 2857643 := bstep (se 1 (by rfl) ⟨2143232, by rfl⟩ : syracuseStep 2857643 = 4286465) B4286465
theorem B1268527 : Blo 1268452 1268527 := bstep (se 1 (by rfl) ⟨951395, by rfl⟩ : syracuseStep 1268527 = 1902791) B1902791
theorem B6101885 : Blo 1268452 6101885 := bstep (se 3 (by rfl) ⟨1144103, by rfl⟩ : syracuseStep 6101885 = 2288207) B2288207
theorem B4283279 : Blo 1268452 4283279 := bstep (se 1 (by rfl) ⟨3212459, by rfl⟩ : syracuseStep 4283279 = 6424919) B6424919
theorem B1268635 : Blo 1268452 1268635 := bstep (se 1 (by rfl) ⟨951476, by rfl⟩ : syracuseStep 1268635 = 1902953) B1902953
theorem B1268687 : Blo 1268452 1268687 := bstep (se 1 (by rfl) ⟨951515, by rfl⟩ : syracuseStep 1268687 = 1903031) B1903031
theorem B1268711 : Blo 1268452 1268711 := bstep (se 1 (by rfl) ⟨951533, by rfl⟩ : syracuseStep 1268711 = 1903067) B1903067
theorem B2858183 : Blo 1268452 2858183 := bstep (se 1 (by rfl) ⟨2143637, by rfl⟩ : syracuseStep 2858183 = 4287275) B4287275
theorem B12197081 : Blo 1268452 12197081 := bstep (se 2 (by rfl) ⟨4573905, by rfl⟩ : syracuseStep 12197081 = 9147811) B9147811
theorem B1269023 : Blo 1268452 1269023 := bstep (se 1 (by rfl) ⟨951767, by rfl⟩ : syracuseStep 1269023 = 1903535) B1903535
theorem B1269083 : Blo 1268452 1269083 := bstep (se 1 (by rfl) ⟨951812, by rfl⟩ : syracuseStep 1269083 = 1903625) B1903625
theorem B1269103 : Blo 1268452 1269103 := bstep (se 1 (by rfl) ⟨951827, by rfl⟩ : syracuseStep 1269103 = 1903655) B1903655
theorem B2858363 : Blo 1268452 2858363 := bstep (se 1 (by rfl) ⟨2143772, by rfl⟩ : syracuseStep 2858363 = 4287545) B4287545
theorem B1269159 : Blo 1268452 1269159 := bstep (se 1 (by rfl) ⟨951869, by rfl⟩ : syracuseStep 1269159 = 1903739) B1903739
theorem B3431879 : Blo 1268452 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B5144057 : Blo 1268452 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B2858489 : Blo 1268452 2858489 := bstep (se 2 (by rfl) ⟨1071933, by rfl⟩ : syracuseStep 2858489 = 2143867) B2143867
theorem B1269243 : Blo 1268452 1269243 := bstep (se 1 (by rfl) ⟨951932, by rfl⟩ : syracuseStep 1269243 = 1903865) B1903865
theorem B1269311 : Blo 1268452 1269311 := bstep (se 1 (by rfl) ⟨951983, by rfl⟩ : syracuseStep 1269311 = 1903967) B1903967
theorem B1269319 : Blo 1268452 1269319 := bstep (se 1 (by rfl) ⟨951989, by rfl⟩ : syracuseStep 1269319 = 1903979) B1903979
theorem B2408123 : Blo 1268452 2408123 := bstep (se 1 (by rfl) ⟨1806092, by rfl⟩ : syracuseStep 2408123 = 3612185) B3612185
theorem B1269471 : Blo 1268452 1269471 := bstep (se 1 (by rfl) ⟨952103, by rfl⟩ : syracuseStep 1269471 = 1904207) B1904207
theorem B1269551 : Blo 1268452 1269551 := bstep (se 1 (by rfl) ⟨952163, by rfl⟩ : syracuseStep 1269551 = 1904327) B1904327
theorem B2572087 : Blo 1268452 2572087 := bstep (se 1 (by rfl) ⟨1929065, by rfl⟩ : syracuseStep 2572087 = 3858131) B3858131
theorem B1269659 : Blo 1268452 1269659 := bstep (se 1 (by rfl) ⟨952244, by rfl⟩ : syracuseStep 1269659 = 1904489) B1904489
theorem B1269711 : Blo 1268452 1269711 := bstep (se 1 (by rfl) ⟨952283, by rfl⟩ : syracuseStep 1269711 = 1904567) B1904567
theorem B1269735 : Blo 1268452 1269735 := bstep (se 1 (by rfl) ⟨952301, by rfl⟩ : syracuseStep 1269735 = 1904603) B1904603
theorem B14458985 : Blo 1268452 14458985 := bstep (se 2 (by rfl) ⟨5422119, by rfl⟩ : syracuseStep 14458985 = 10844239) B10844239
theorem B7225483 : Blo 1268452 7225483 := bstep (se 1 (by rfl) ⟨5419112, by rfl⟩ : syracuseStep 7225483 = 10838225) B10838225
theorem B1269991 : Blo 1268452 1269991 := bstep (se 1 (by rfl) ⟨952493, by rfl⟩ : syracuseStep 1269991 = 1904987) B1904987
theorem B4284791 : Blo 1268452 4284791 := bstep (se 1 (by rfl) ⟨3213593, by rfl⟩ : syracuseStep 4284791 = 6427187) B6427187
theorem B1270143 : Blo 1268452 1270143 := bstep (se 1 (by rfl) ⟨952607, by rfl⟩ : syracuseStep 1270143 = 1905215) B1905215
theorem B1270223 : Blo 1268452 1270223 := bstep (se 1 (by rfl) ⟨952667, by rfl⟩ : syracuseStep 1270223 = 1905335) B1905335
theorem B2286073 : Blo 1268452 2286073 := bstep (se 2 (by rfl) ⟨857277, by rfl⟩ : syracuseStep 2286073 = 1714555) B1714555
theorem B1270375 : Blo 1268452 1270375 := bstep (se 1 (by rfl) ⟨952781, by rfl⟩ : syracuseStep 1270375 = 1905563) B1905563
theorem B5423881 : Blo 1268452 5423881 := bstep (se 2 (by rfl) ⟨2033955, by rfl⟩ : syracuseStep 5423881 = 4067911) B4067911
theorem B6095735 : Blo 1268452 6095735 := bstep (se 1 (by rfl) ⟨4571801, by rfl⟩ : syracuseStep 6095735 = 9143603) B9143603
theorem B3048473 : Blo 1268452 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B1606711 : Blo 1268452 1606711 := bstep (se 1 (by rfl) ⟨1205033, by rfl⟩ : syracuseStep 1606711 = 2410067) B2410067
theorem B2409679 : Blo 1268452 2409679 := bstep (se 1 (by rfl) ⟨1807259, by rfl⟩ : syracuseStep 2409679 = 3614519) B3614519
theorem B1524943 : Blo 1268452 1524943 := bstep (se 1 (by rfl) ⟨1143707, by rfl⟩ : syracuseStep 1524943 = 2287415) B2287415
theorem B6514057 : Blo 1268452 6514057 := bstep (se 2 (by rfl) ⟨2442771, by rfl⟩ : syracuseStep 6514057 = 4885543) B4885543
theorem B4285871 : Blo 1268452 4285871 := bstep (se 1 (by rfl) ⟨3214403, by rfl⟩ : syracuseStep 4285871 = 6428807) B6428807
theorem B3614291 : Blo 1268452 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B8136359 : Blo 1268452 8136359 := bstep (se 1 (by rfl) ⟨6102269, by rfl⟩ : syracuseStep 8136359 = 12204539) B12204539
theorem B1607455 : Blo 1268452 1607455 := bstep (se 1 (by rfl) ⟨1205591, by rfl⟩ : syracuseStep 1607455 = 2411183) B2411183
theorem B4286249 : Blo 1268452 4286249 := bstep (se 2 (by rfl) ⟨1607343, by rfl⟩ : syracuseStep 4286249 = 3214687) B3214687
theorem B18286397 : Blo 1268452 18286397 := bstep (se 3 (by rfl) ⟨3428699, by rfl⟩ : syracuseStep 18286397 = 6857399) B6857399
theorem B16500557 : Blo 1268452 16500557 := bstep (se 3 (by rfl) ⟨3093854, by rfl⟩ : syracuseStep 16500557 = 6187709) B6187709
theorem B7227215 : Blo 1268452 7227215 := bstep (se 1 (by rfl) ⟨5420411, by rfl⟩ : syracuseStep 7227215 = 10840823) B10840823
theorem B1427611 : Blo 1268452 1427611 := bstep (se 1 (by rfl) ⟨1070708, by rfl⟩ : syracuseStep 1427611 = 2141417) B2141417
theorem B1427647 : Blo 1268452 1427647 := bstep (se 1 (by rfl) ⟨1070735, by rfl⟩ : syracuseStep 1427647 = 2141471) B2141471
theorem B3213503 : Blo 1268452 3213503 := bstep (se 1 (by rfl) ⟨2410127, by rfl⟩ : syracuseStep 3213503 = 4820255) B4820255
theorem B1902827 : Blo 1268452 1902827 := bstep (se 1 (by rfl) ⟨1427120, by rfl⟩ : syracuseStep 1902827 = 2854241) B2854241
theorem B4065515 : Blo 1268452 4065515 := bstep (se 1 (by rfl) ⟨3049136, by rfl⟩ : syracuseStep 4065515 = 6098273) B6098273
theorem B1902887 : Blo 1268452 1902887 := bstep (se 1 (by rfl) ⟨1427165, by rfl⟩ : syracuseStep 1902887 = 2854331) B2854331
theorem B2287919 : Blo 1268452 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B1902971 : Blo 1268452 1902971 := bstep (se 1 (by rfl) ⟨1427228, by rfl⟩ : syracuseStep 1902971 = 2854457) B2854457
theorem B9775525 : Blo 1268452 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B3050011 : Blo 1268452 3050011 := bstep (se 1 (by rfl) ⟨2287508, by rfl⟩ : syracuseStep 3050011 = 4575017) B4575017
theorem B2411039 : Blo 1268452 2411039 := bstep (se 1 (by rfl) ⟨1808279, by rfl⟩ : syracuseStep 2411039 = 3616559) B3616559
theorem B1903241 : Blo 1268452 1903241 := bstep (se 2 (by rfl) ⟨713715, by rfl⟩ : syracuseStep 1903241 = 1427431) B1427431
theorem B7719563 : Blo 1268452 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B5425811 : Blo 1268452 5425811 := bstep (se 1 (by rfl) ⟨4069358, by rfl⟩ : syracuseStep 5425811 = 8138717) B8138717
theorem B5425879 : Blo 1268452 5425879 := bstep (se 1 (by rfl) ⟨4069409, by rfl⟩ : syracuseStep 5425879 = 8138819) B8138819
theorem B1903415 : Blo 1268452 1903415 := bstep (se 1 (by rfl) ⟨1427561, by rfl⟩ : syracuseStep 1903415 = 2855123) B2855123
theorem B2034487 : Blo 1268452 2034487 := bstep (se 1 (by rfl) ⟨1525865, by rfl⟩ : syracuseStep 2034487 = 3051731) B3051731
theorem B1903451 : Blo 1268452 1903451 := bstep (se 1 (by rfl) ⟨1427588, by rfl⟩ : syracuseStep 1903451 = 2855177) B2855177
theorem B8137691 : Blo 1268452 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B1903595 : Blo 1268452 1903595 := bstep (se 1 (by rfl) ⟨1427696, by rfl⟩ : syracuseStep 1903595 = 2855393) B2855393
theorem B4066283 : Blo 1268452 4066283 := bstep (se 1 (by rfl) ⟨3049712, by rfl⟩ : syracuseStep 4066283 = 6099425) B6099425
theorem B2141255 : Blo 1268452 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B1903799 : Blo 1268452 1903799 := bstep (se 1 (by rfl) ⟨1427849, by rfl⟩ : syracuseStep 1903799 = 2855699) B2855699
theorem B3615977 : Blo 1268452 3615977 := bstep (se 2 (by rfl) ⟨1355991, by rfl⟩ : syracuseStep 3615977 = 2711983) B2711983
theorem B2854223 : Blo 1268452 2854223 := bstep (se 1 (by rfl) ⟨2140667, by rfl⟩ : syracuseStep 2854223 = 4281335) B4281335
theorem B1904039 : Blo 1268452 1904039 := bstep (se 1 (by rfl) ⟨1428029, by rfl⟩ : syracuseStep 1904039 = 2856059) B2856059
theorem B2854313 : Blo 1268452 2854313 := bstep (se 2 (by rfl) ⟨1070367, by rfl⟩ : syracuseStep 2854313 = 2140735) B2140735
theorem B5426615 : Blo 1268452 5426615 := bstep (se 1 (by rfl) ⟨4069961, by rfl⟩ : syracuseStep 5426615 = 8139923) B8139923
theorem B2141687 : Blo 1268452 2141687 := bstep (se 1 (by rfl) ⟨1606265, by rfl⟩ : syracuseStep 2141687 = 3212531) B3212531
theorem B1904123 : Blo 1268452 1904123 := bstep (se 1 (by rfl) ⟨1428092, by rfl⟩ : syracuseStep 1904123 = 2856185) B2856185
theorem B4820543 : Blo 1268452 4820543 := bstep (se 1 (by rfl) ⟨3615407, by rfl⟩ : syracuseStep 4820543 = 7230815) B7230815
theorem B3616319 : Blo 1268452 3616319 := bstep (se 1 (by rfl) ⟨2712239, by rfl⟩ : syracuseStep 3616319 = 5424479) B5424479
theorem B9645641 : Blo 1268452 9645641 := bstep (se 2 (by rfl) ⟨3617115, by rfl⟩ : syracuseStep 9645641 = 7234231) B7234231
theorem B1904219 : Blo 1268452 1904219 := bstep (se 1 (by rfl) ⟨1428164, by rfl⟩ : syracuseStep 1904219 = 2856329) B2856329
theorem B10849949 : Blo 1268452 10849949 := bstep (se 3 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 10849949 = 4068731) B4068731
theorem B1904303 : Blo 1268452 1904303 := bstep (se 1 (by rfl) ⟨1428227, by rfl⟩ : syracuseStep 1904303 = 2856455) B2856455
theorem B3215123 : Blo 1268452 3215123 := bstep (se 1 (by rfl) ⟨2411342, by rfl⟩ : syracuseStep 3215123 = 4822685) B4822685
theorem B1904423 : Blo 1268452 1904423 := bstep (se 1 (by rfl) ⟨1428317, by rfl⟩ : syracuseStep 1904423 = 2856635) B2856635
theorem B15429437 : Blo 1268452 15429437 := bstep (se 3 (by rfl) ⟨2893019, by rfl⟩ : syracuseStep 15429437 = 5786039) B5786039
theorem B32542559 : Blo 1268452 32542559 := bstep (se 1 (by rfl) ⟨24406919, by rfl⟩ : syracuseStep 32542559 = 48813839) B48813839
theorem B6098809 : Blo 1268452 6098809 := bstep (se 2 (by rfl) ⟨2287053, by rfl⟩ : syracuseStep 6098809 = 4574107) B4574107
theorem B1904507 : Blo 1268452 1904507 := bstep (se 1 (by rfl) ⟨1428380, by rfl⟩ : syracuseStep 1904507 = 2856761) B2856761
theorem B2854799 : Blo 1268452 2854799 := bstep (se 1 (by rfl) ⟨2141099, by rfl⟩ : syracuseStep 2854799 = 4282199) B4282199
theorem B4067513 : Blo 1268452 4067513 := bstep (se 2 (by rfl) ⟨1525317, by rfl⟩ : syracuseStep 4067513 = 3050635) B3050635
theorem B1904927 : Blo 1268452 1904927 := bstep (se 1 (by rfl) ⟨1428695, by rfl⟩ : syracuseStep 1904927 = 2857391) B2857391
theorem B1904951 : Blo 1268452 1904951 := bstep (se 1 (by rfl) ⟨1428713, by rfl⟩ : syracuseStep 1904951 = 2857427) B2857427
theorem B1905023 : Blo 1268452 1905023 := bstep (se 1 (by rfl) ⟨1428767, by rfl⟩ : syracuseStep 1905023 = 2857535) B2857535
theorem B1905095 : Blo 1268452 1905095 := bstep (se 1 (by rfl) ⟨1428821, by rfl⟩ : syracuseStep 1905095 = 2857643) B2857643
theorem B2142713 : Blo 1268452 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B4067923 : Blo 1268452 4067923 := bstep (se 1 (by rfl) ⟨3050942, by rfl⟩ : syracuseStep 4067923 = 6101885) B6101885
theorem B2855519 : Blo 1268452 2855519 := bstep (se 1 (by rfl) ⟨2141639, by rfl⟩ : syracuseStep 2855519 = 4283279) B4283279
theorem B2142983 : Blo 1268452 2142983 := bstep (se 1 (by rfl) ⟨1607237, by rfl⟩ : syracuseStep 2142983 = 3214475) B3214475
theorem B3617561 : Blo 1268452 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B1905449 : Blo 1268452 1905449 := bstep (se 2 (by rfl) ⟨714543, by rfl⟩ : syracuseStep 1905449 = 1429087) B1429087
theorem B1905455 : Blo 1268452 1905455 := bstep (se 1 (by rfl) ⟨1429091, by rfl⟩ : syracuseStep 1905455 = 2858183) B2858183
theorem B8131387 : Blo 1268452 8131387 := bstep (se 1 (by rfl) ⟨6098540, by rfl⟩ : syracuseStep 8131387 = 12197081) B12197081
theorem B12194621 : Blo 1268452 12194621 := bstep (se 3 (by rfl) ⟨2286491, by rfl⟩ : syracuseStep 12194621 = 4572983) B4572983
theorem B2061167 : Blo 1268452 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1905575 : Blo 1268452 1905575 := bstep (se 1 (by rfl) ⟨1429181, by rfl⟩ : syracuseStep 1905575 = 2858363) B2858363
theorem B18297809 : Blo 1268452 18297809 := bstep (se 2 (by rfl) ⟨6861678, by rfl⟩ : syracuseStep 18297809 = 13723357) B13723357
theorem B3429371 : Blo 1268452 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B1905659 : Blo 1268452 1905659 := bstep (se 1 (by rfl) ⟨1429244, by rfl⟩ : syracuseStep 1905659 = 2858489) B2858489
theorem B3429449 : Blo 1268452 3429449 := bstep (se 2 (by rfl) ⟨1286043, by rfl⟩ : syracuseStep 3429449 = 2572087) B2572087
theorem B5420105 : Blo 1268452 5420105 := bstep (se 2 (by rfl) ⟨2032539, by rfl⟩ : syracuseStep 5420105 = 4065079) B4065079
theorem B2856347 : Blo 1268452 2856347 := bstep (se 1 (by rfl) ⟨2142260, by rfl⟩ : syracuseStep 2856347 = 4284521) B4284521
theorem B74225159 : Blo 1268452 74225159 := bstep (se 1 (by rfl) ⟨55668869, by rfl⟩ : syracuseStep 74225159 = 111337739) B111337739
theorem B5150317 : Blo 1268452 5150317 := bstep (se 3 (by rfl) ⟨965684, by rfl⟩ : syracuseStep 5150317 = 1931369) B1931369
theorem B4822699 : Blo 1268452 4822699 := bstep (se 1 (by rfl) ⟨3617024, by rfl⟩ : syracuseStep 4822699 = 7234049) B7234049
theorem B31307447 : Blo 1268452 31307447 := bstep (se 1 (by rfl) ⟨23480585, by rfl⟩ : syracuseStep 31307447 = 46961171) B46961171
theorem B5420753 : Blo 1268452 5420753 := bstep (se 2 (by rfl) ⟨2032782, by rfl⟩ : syracuseStep 5420753 = 4065565) B4065565
theorem B4282091 : Blo 1268452 4282091 := bstep (se 1 (by rfl) ⟨3211568, by rfl⟩ : syracuseStep 4282091 = 6423137) B6423137
theorem B11138795 : Blo 1268452 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B2856923 : Blo 1268452 2856923 := bstep (se 1 (by rfl) ⟨2142692, by rfl⟩ : syracuseStep 2856923 = 4285385) B4285385
theorem B4282361 : Blo 1268452 4282361 := bstep (se 2 (by rfl) ⟨1605885, by rfl⟩ : syracuseStep 4282361 = 3211771) B3211771
theorem B2857103 : Blo 1268452 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B2709659 : Blo 1268452 2709659 := bstep (se 1 (by rfl) ⟨2032244, by rfl⟩ : syracuseStep 2709659 = 4064489) B4064489
theorem B4282523 : Blo 1268452 4282523 := bstep (se 1 (by rfl) ⟨3211892, by rfl⟩ : syracuseStep 4282523 = 6423785) B6423785
theorem B2857121 : Blo 1268452 2857121 := bstep (se 2 (by rfl) ⟨1071420, by rfl⟩ : syracuseStep 2857121 = 2142841) B2142841
theorem B2857193 : Blo 1268452 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B4282631 : Blo 1268452 4282631 := bstep (se 1 (by rfl) ⟨3211973, by rfl⟩ : syracuseStep 4282631 = 6423947) B6423947
theorem B23148823 : Blo 1268452 23148823 := bstep (se 1 (by rfl) ⟨17361617, by rfl⟩ : syracuseStep 23148823 = 34723235) B34723235
theorem B6428969 : Blo 1268452 6428969 := bstep (se 2 (by rfl) ⟨2410863, by rfl⟩ : syracuseStep 6428969 = 4821727) B4821727
theorem B6519149 : Blo 1268452 6519149 := bstep (se 3 (by rfl) ⟨1222340, by rfl⟩ : syracuseStep 6519149 = 2444681) B2444681
theorem B6101423 : Blo 1268452 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B16267999 : Blo 1268452 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B20601643 : Blo 1268452 20601643 := bstep (se 1 (by rfl) ⟨15451232, by rfl⟩ : syracuseStep 20601643 = 30902465) B30902465
theorem B10836827 : Blo 1268452 10836827 := bstep (se 1 (by rfl) ⟨8127620, by rfl⟩ : syracuseStep 10836827 = 16255241) B16255241
theorem B1268571 : Blo 1268452 1268571 := bstep (se 1 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 1268571 = 1902857) B1902857
theorem B3857311 : Blo 1268452 3857311 := bstep (se 1 (by rfl) ⟨2892983, by rfl⟩ : syracuseStep 3857311 = 5785967) B5785967
theorem B1268639 : Blo 1268452 1268639 := bstep (se 1 (by rfl) ⟨951479, by rfl⟩ : syracuseStep 1268639 = 1902959) B1902959
theorem B6601769 : Blo 1268452 6601769 := bstep (se 2 (by rfl) ⟨2475663, by rfl⟩ : syracuseStep 6601769 = 4951327) B4951327
theorem B1268783 : Blo 1268452 1268783 := bstep (se 1 (by rfl) ⟨951587, by rfl⟩ : syracuseStep 1268783 = 1903175) B1903175
theorem B1268807 : Blo 1268452 1268807 := bstep (se 1 (by rfl) ⟨951605, by rfl⟩ : syracuseStep 1268807 = 1903211) B1903211
theorem B35216531 : Blo 1268452 35216531 := bstep (se 1 (by rfl) ⟨26412398, by rfl⟩ : syracuseStep 35216531 = 52824797) B52824797
theorem B1268959 : Blo 1268452 1268959 := bstep (se 1 (by rfl) ⟨951719, by rfl⟩ : syracuseStep 1268959 = 1903439) B1903439
theorem B4283657 : Blo 1268452 4283657 := bstep (se 2 (by rfl) ⟨1606371, by rfl⟩ : syracuseStep 4283657 = 3212743) B3212743
theorem B1269223 : Blo 1268452 1269223 := bstep (se 1 (by rfl) ⟨951917, by rfl⟩ : syracuseStep 1269223 = 1903835) B1903835
theorem B2858471 : Blo 1268452 2858471 := bstep (se 1 (by rfl) ⟨2143853, by rfl⟩ : syracuseStep 2858471 = 4287707) B4287707
theorem B1269339 : Blo 1268452 1269339 := bstep (se 1 (by rfl) ⟨952004, by rfl⟩ : syracuseStep 1269339 = 1904009) B1904009
theorem B1605415 : Blo 1268452 1605415 := bstep (se 1 (by rfl) ⟨1204061, by rfl⟩ : syracuseStep 1605415 = 2408123) B2408123
theorem B1269575 : Blo 1268452 1269575 := bstep (se 1 (by rfl) ⟨952181, by rfl⟩ : syracuseStep 1269575 = 1904363) B1904363
theorem B10862545 : Blo 1268452 10862545 := bstep (se 2 (by rfl) ⟨4073454, by rfl⟩ : syracuseStep 10862545 = 8146909) B8146909
theorem B1269727 : Blo 1268452 1269727 := bstep (se 1 (by rfl) ⟨952295, by rfl⟩ : syracuseStep 1269727 = 1904591) B1904591
theorem B2711675 : Blo 1268452 2711675 := bstep (se 1 (by rfl) ⟨2033756, by rfl⟩ : syracuseStep 2711675 = 4067513) B4067513
theorem B9633977 : Blo 1268452 9633977 := bstep (se 2 (by rfl) ⟨3612741, by rfl⟩ : syracuseStep 9633977 = 7225483) B7225483
theorem B1269951 : Blo 1268452 1269951 := bstep (se 1 (by rfl) ⟨952463, by rfl⟩ : syracuseStep 1269951 = 1904927) B1904927
theorem B1269967 : Blo 1268452 1269967 := bstep (se 1 (by rfl) ⟨952475, by rfl⟩ : syracuseStep 1269967 = 1904951) B1904951
theorem B1270015 : Blo 1268452 1270015 := bstep (se 1 (by rfl) ⟨952511, by rfl⟩ : syracuseStep 1270015 = 1905023) B1905023
theorem B1270063 : Blo 1268452 1270063 := bstep (se 1 (by rfl) ⟨952547, by rfl⟩ : syracuseStep 1270063 = 1905095) B1905095
theorem B7225757 : Blo 1268452 7225757 := bstep (se 3 (by rfl) ⟨1354829, by rfl⟩ : syracuseStep 7225757 = 2709659) B2709659
theorem B1270299 : Blo 1268452 1270299 := bstep (se 1 (by rfl) ⟨952724, by rfl⟩ : syracuseStep 1270299 = 1905449) B1905449
theorem B1270303 : Blo 1268452 1270303 := bstep (se 1 (by rfl) ⟨952727, by rfl⟩ : syracuseStep 1270303 = 1905455) B1905455
theorem B13034033 : Blo 1268452 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B4063823 : Blo 1268452 4063823 := bstep (se 1 (by rfl) ⟨3047867, by rfl⟩ : syracuseStep 4063823 = 6095735) B6095735
theorem B1270383 : Blo 1268452 1270383 := bstep (se 1 (by rfl) ⟨952787, by rfl⟩ : syracuseStep 1270383 = 1905575) B1905575
theorem B12198539 : Blo 1268452 12198539 := bstep (se 1 (by rfl) ⟨9148904, by rfl⟩ : syracuseStep 12198539 = 18297809) B18297809
theorem B2286247 : Blo 1268452 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B1270439 : Blo 1268452 1270439 := bstep (se 1 (by rfl) ⟨952829, by rfl⟩ : syracuseStep 1270439 = 1905659) B1905659
theorem B2286299 : Blo 1268452 2286299 := bstep (se 1 (by rfl) ⟨1714724, by rfl⟩ : syracuseStep 2286299 = 3429449) B3429449
theorem B3613403 : Blo 1268452 3613403 := bstep (se 1 (by rfl) ⟨2710052, by rfl⟩ : syracuseStep 3613403 = 5420105) B5420105
theorem B5423897 : Blo 1268452 5423897 := bstep (se 2 (by rfl) ⟨2033961, by rfl⟩ : syracuseStep 5423897 = 4067923) B4067923
theorem B7234505 : Blo 1268452 7234505 := bstep (se 2 (by rfl) ⟨2712939, by rfl⟩ : syracuseStep 7234505 = 5425879) B5425879
theorem B2409527 : Blo 1268452 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B27468857 : Blo 1268452 27468857 := bstep (se 2 (by rfl) ⟨10300821, by rfl⟩ : syracuseStep 27468857 = 20601643) B20601643
theorem B5424239 : Blo 1268452 5424239 := bstep (se 1 (by rfl) ⟨4068179, by rfl⟩ : syracuseStep 5424239 = 8136359) B8136359
theorem B3613835 : Blo 1268452 3613835 := bstep (se 1 (by rfl) ⟨2710376, by rfl⟩ : syracuseStep 3613835 = 5420753) B5420753
theorem B12190931 : Blo 1268452 12190931 := bstep (se 1 (by rfl) ⟨9143198, by rfl⟩ : syracuseStep 12190931 = 18286397) B18286397
theorem B4818143 : Blo 1268452 4818143 := bstep (se 1 (by rfl) ⟨3613607, by rfl⟩ : syracuseStep 4818143 = 7227215) B7227215
theorem B4285979 : Blo 1268452 4285979 := bstep (se 1 (by rfl) ⟨3214484, by rfl⟩ : syracuseStep 4285979 = 6428969) B6428969
theorem B1525279 : Blo 1268452 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B3212905 : Blo 1268452 3212905 := bstep (se 2 (by rfl) ⟨1204839, by rfl⟩ : syracuseStep 3212905 = 2409679) B2409679
theorem B2033257 : Blo 1268452 2033257 := bstep (se 2 (by rfl) ⟨762471, by rfl⟩ : syracuseStep 2033257 = 1524943) B1524943
theorem B1607359 : Blo 1268452 1607359 := bstep (se 1 (by rfl) ⟨1205519, by rfl⟩ : syracuseStep 1607359 = 2411039) B2411039
theorem B8685409 : Blo 1268452 8685409 := bstep (se 2 (by rfl) ⟨3257028, by rfl⟩ : syracuseStep 8685409 = 6514057) B6514057
theorem B5425127 : Blo 1268452 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B4401179 : Blo 1268452 4401179 := bstep (se 1 (by rfl) ⟨3300884, by rfl⟩ : syracuseStep 4401179 = 6601769) B6601769
theorem B1427503 : Blo 1268452 1427503 := bstep (se 1 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 1427503 = 2141255) B2141255
theorem B6867089 : Blo 1268452 6867089 := bstep (se 2 (by rfl) ⟨2575158, by rfl⟩ : syracuseStep 6867089 = 5150317) B5150317
theorem B2410651 : Blo 1268452 2410651 := bstep (se 1 (by rfl) ⟨1807988, by rfl⟩ : syracuseStep 2410651 = 3615977) B3615977
theorem B20572325 : Blo 1268452 20572325 := bstep (se 4 (by rfl) ⟨1928655, by rfl⟩ : syracuseStep 20572325 = 3857311) B3857311
theorem B1902815 : Blo 1268452 1902815 := bstep (se 1 (by rfl) ⟨1427111, by rfl⟩ : syracuseStep 1902815 = 2854223) B2854223
theorem B1902875 : Blo 1268452 1902875 := bstep (se 1 (by rfl) ⟨1427156, by rfl⟩ : syracuseStep 1902875 = 2854313) B2854313
theorem B1427791 : Blo 1268452 1427791 := bstep (se 1 (by rfl) ⟨1070843, by rfl⟩ : syracuseStep 1427791 = 2141687) B2141687
theorem B3213695 : Blo 1268452 3213695 := bstep (se 1 (by rfl) ⟨2410271, by rfl⟩ : syracuseStep 3213695 = 4820543) B4820543
theorem B2410879 : Blo 1268452 2410879 := bstep (se 1 (by rfl) ⟨1808159, by rfl⟩ : syracuseStep 2410879 = 3616319) B3616319
theorem B2140553 : Blo 1268452 2140553 := bstep (se 2 (by rfl) ⟨802707, by rfl⟩ : syracuseStep 2140553 = 1605415) B1605415
theorem B21695039 : Blo 1268452 21695039 := bstep (se 1 (by rfl) ⟨16271279, by rfl⟩ : syracuseStep 21695039 = 32542559) B32542559
theorem B1903199 : Blo 1268452 1903199 := bstep (se 1 (by rfl) ⟨1427399, by rfl⟩ : syracuseStep 1903199 = 2854799) B2854799
theorem B12192389 : Blo 1268452 12192389 := bstep (se 4 (by rfl) ⟨1143036, by rfl⟩ : syracuseStep 12192389 = 2286073) B2286073
theorem B8129261 : Blo 1268452 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B1903481 : Blo 1268452 1903481 := bstep (se 2 (by rfl) ⟨713805, by rfl⟩ : syracuseStep 1903481 = 1427611) B1427611
theorem B1903529 : Blo 1268452 1903529 := bstep (se 2 (by rfl) ⟨713823, by rfl⟩ : syracuseStep 1903529 = 1427647) B1427647
theorem B1428475 : Blo 1268452 1428475 := bstep (se 1 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 1428475 = 2142713) B2142713
theorem B1903679 : Blo 1268452 1903679 := bstep (se 1 (by rfl) ⟨1427759, by rfl⟩ : syracuseStep 1903679 = 2855519) B2855519
theorem B1428655 : Blo 1268452 1428655 := bstep (se 1 (by rfl) ⟨1071491, by rfl⟩ : syracuseStep 1428655 = 2142983) B2142983
theorem B2411707 : Blo 1268452 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B8129747 : Blo 1268452 8129747 := bstep (se 1 (by rfl) ⟨6097310, by rfl⟩ : syracuseStep 8129747 = 12194621) B12194621
theorem B4066681 : Blo 1268452 4066681 := bstep (se 2 (by rfl) ⟨1525005, by rfl⟩ : syracuseStep 4066681 = 3050011) B3050011
theorem B1904231 : Blo 1268452 1904231 := bstep (se 1 (by rfl) ⟨1428173, by rfl⟩ : syracuseStep 1904231 = 2856347) B2856347
theorem B49483439 : Blo 1268452 49483439 := bstep (se 1 (by rfl) ⟨37112579, by rfl⟩ : syracuseStep 49483439 = 74225159) B74225159
theorem B10841849 : Blo 1268452 10841849 := bstep (se 2 (by rfl) ⟨4065693, by rfl⟩ : syracuseStep 10841849 = 8131387) B8131387
theorem B2854727 : Blo 1268452 2854727 := bstep (se 1 (by rfl) ⟨2141045, by rfl⟩ : syracuseStep 2854727 = 4282091) B4282091
theorem B7425863 : Blo 1268452 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B1904615 : Blo 1268452 1904615 := bstep (se 1 (by rfl) ⟨1428461, by rfl⟩ : syracuseStep 1904615 = 2856923) B2856923
theorem B2854907 : Blo 1268452 2854907 := bstep (se 1 (by rfl) ⟨2141180, by rfl⟩ : syracuseStep 2854907 = 4282361) B4282361
theorem B2142281 : Blo 1268452 2142281 := bstep (se 2 (by rfl) ⟨803355, by rfl⟩ : syracuseStep 2142281 = 1606711) B1606711
theorem B1904735 : Blo 1268452 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B2855015 : Blo 1268452 2855015 := bstep (se 1 (by rfl) ⟨2141261, by rfl⟩ : syracuseStep 2855015 = 4282523) B4282523
theorem B1904747 : Blo 1268452 1904747 := bstep (se 1 (by rfl) ⟨1428560, by rfl⟩ : syracuseStep 1904747 = 2857121) B2857121
theorem B2142335 : Blo 1268452 2142335 := bstep (se 1 (by rfl) ⟨1606751, by rfl⟩ : syracuseStep 2142335 = 3213503) B3213503
theorem B1904795 : Blo 1268452 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B2855087 : Blo 1268452 2855087 := bstep (se 1 (by rfl) ⟨2141315, by rfl⟩ : syracuseStep 2855087 = 4282631) B4282631
theorem B4346099 : Blo 1268452 4346099 := bstep (se 1 (by rfl) ⟨3259574, by rfl⟩ : syracuseStep 4346099 = 6519149) B6519149
theorem B4067615 : Blo 1268452 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B10850597 : Blo 1268452 10850597 := bstep (se 4 (by rfl) ⟨1017243, by rfl⟩ : syracuseStep 10850597 = 2034487) B2034487
theorem B3617207 : Blo 1268452 3617207 := bstep (se 1 (by rfl) ⟨2712905, by rfl⟩ : syracuseStep 3617207 = 5425811) B5425811
theorem B2855771 : Blo 1268452 2855771 := bstep (se 1 (by rfl) ⟨2141828, by rfl⟩ : syracuseStep 2855771 = 4283657) B4283657
theorem B3617743 : Blo 1268452 3617743 := bstep (se 1 (by rfl) ⟨2713307, by rfl⟩ : syracuseStep 3617743 = 5426615) B5426615
theorem B1905647 : Blo 1268452 1905647 := bstep (se 1 (by rfl) ⟨1429235, by rfl⟩ : syracuseStep 1905647 = 2858471) B2858471
theorem B2143273 : Blo 1268452 2143273 := bstep (se 2 (by rfl) ⟨803727, by rfl⟩ : syracuseStep 2143273 = 1607455) B1607455
theorem B8131745 : Blo 1268452 8131745 := bstep (se 2 (by rfl) ⟨3049404, by rfl⟩ : syracuseStep 8131745 = 6098809) B6098809
theorem B2143415 : Blo 1268452 2143415 := bstep (se 1 (by rfl) ⟨1607561, by rfl⟩ : syracuseStep 2143415 = 3215123) B3215123
theorem B10286291 : Blo 1268452 10286291 := bstep (se 1 (by rfl) ⟨7714718, by rfl⟩ : syracuseStep 10286291 = 15429437) B15429437
theorem B9639323 : Blo 1268452 9639323 := bstep (se 1 (by rfl) ⟨7229492, by rfl⟩ : syracuseStep 9639323 = 14458985) B14458985
theorem B2856527 : Blo 1268452 2856527 := bstep (se 1 (by rfl) ⟨2142395, by rfl⟩ : syracuseStep 2856527 = 4284791) B4284791
theorem B30865097 : Blo 1268452 30865097 := bstep (se 2 (by rfl) ⟨11574411, by rfl⟩ : syracuseStep 30865097 = 23148823) B23148823
theorem B2857247 : Blo 1268452 2857247 := bstep (se 1 (by rfl) ⟨2142935, by rfl⟩ : syracuseStep 2857247 = 4285871) B4285871
theorem B21690665 : Blo 1268452 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B7231841 : Blo 1268452 7231841 := bstep (se 2 (by rfl) ⟨2711940, by rfl⟩ : syracuseStep 7231841 = 5423881) B5423881
theorem B20871631 : Blo 1268452 20871631 := bstep (se 1 (by rfl) ⟨15653723, by rfl⟩ : syracuseStep 20871631 = 31307447) B31307447
theorem B2857499 : Blo 1268452 2857499 := bstep (se 1 (by rfl) ⟨2143124, by rfl⟩ : syracuseStep 2857499 = 4286249) B4286249
theorem B11000371 : Blo 1268452 11000371 := bstep (se 1 (by rfl) ⟨8250278, by rfl⟩ : syracuseStep 11000371 = 16500557) B16500557
theorem B1268551 : Blo 1268452 1268551 := bstep (se 1 (by rfl) ⟨951413, by rfl⟩ : syracuseStep 1268551 = 1902827) B1902827
theorem B2710343 : Blo 1268452 2710343 := bstep (se 1 (by rfl) ⟨2032757, by rfl⟩ : syracuseStep 2710343 = 4065515) B4065515
theorem B1268591 : Blo 1268452 1268591 := bstep (se 1 (by rfl) ⟨951443, by rfl⟩ : syracuseStep 1268591 = 1902887) B1902887
theorem B1268647 : Blo 1268452 1268647 := bstep (se 1 (by rfl) ⟨951485, by rfl⟩ : syracuseStep 1268647 = 1902971) B1902971
theorem B20585501 : Blo 1268452 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B1268827 : Blo 1268452 1268827 := bstep (se 1 (by rfl) ⟨951620, by rfl⟩ : syracuseStep 1268827 = 1903241) B1903241
theorem B1268943 : Blo 1268452 1268943 := bstep (se 1 (by rfl) ⟨951707, by rfl⟩ : syracuseStep 1268943 = 1903415) B1903415
theorem B7224551 : Blo 1268452 7224551 := bstep (se 1 (by rfl) ⟨5418413, by rfl⟩ : syracuseStep 7224551 = 10836827) B10836827
theorem B1268967 : Blo 1268452 1268967 := bstep (se 1 (by rfl) ⟨951725, by rfl⟩ : syracuseStep 1268967 = 1903451) B1903451
theorem B1269063 : Blo 1268452 1269063 := bstep (se 1 (by rfl) ⟨951797, by rfl⟩ : syracuseStep 1269063 = 1903595) B1903595
theorem B2710855 : Blo 1268452 2710855 := bstep (se 1 (by rfl) ⟨2033141, by rfl⟩ : syracuseStep 2710855 = 4066283) B4066283
theorem B23477687 : Blo 1268452 23477687 := bstep (se 1 (by rfl) ⟨17608265, by rfl⟩ : syracuseStep 23477687 = 35216531) B35216531
theorem B1269199 : Blo 1268452 1269199 := bstep (se 1 (by rfl) ⟨951899, by rfl⟩ : syracuseStep 1269199 = 1903799) B1903799
theorem B6430265 : Blo 1268452 6430265 := bstep (se 2 (by rfl) ⟨2411349, by rfl⟩ : syracuseStep 6430265 = 4822699) B4822699
theorem B1269359 : Blo 1268452 1269359 := bstep (se 1 (by rfl) ⟨952019, by rfl⟩ : syracuseStep 1269359 = 1904039) B1904039
theorem B5496445 : Blo 1268452 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B1269415 : Blo 1268452 1269415 := bstep (se 1 (by rfl) ⟨952061, by rfl⟩ : syracuseStep 1269415 = 1904123) B1904123
theorem B6430427 : Blo 1268452 6430427 := bstep (se 1 (by rfl) ⟨4822820, by rfl⟩ : syracuseStep 6430427 = 9645641) B9645641
theorem B1269479 : Blo 1268452 1269479 := bstep (se 1 (by rfl) ⟨952109, by rfl⟩ : syracuseStep 1269479 = 1904219) B1904219
theorem B7233299 : Blo 1268452 7233299 := bstep (se 1 (by rfl) ⟨5424974, by rfl⟩ : syracuseStep 7233299 = 10849949) B10849949
theorem B1269535 : Blo 1268452 1269535 := bstep (se 1 (by rfl) ⟨952151, by rfl⟩ : syracuseStep 1269535 = 1904303) B1904303
theorem B1269615 : Blo 1268452 1269615 := bstep (se 1 (by rfl) ⟨952211, by rfl⟩ : syracuseStep 1269615 = 1904423) B1904423
theorem B1269671 : Blo 1268452 1269671 := bstep (se 1 (by rfl) ⟨952253, by rfl⟩ : syracuseStep 1269671 = 1904507) B1904507
theorem B14483393 : Blo 1268452 14483393 := bstep (se 2 (by rfl) ⟨5431272, by rfl⟩ : syracuseStep 14483393 = 10862545) B10862545
theorem B1269823 : Blo 1268452 1269823 := bstep (se 1 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 1269823 = 1904735) B1904735
theorem B1269831 : Blo 1268452 1269831 := bstep (se 1 (by rfl) ⟨952373, by rfl⟩ : syracuseStep 1269831 = 1904747) B1904747
theorem B1269863 : Blo 1268452 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B6422651 : Blo 1268452 6422651 := bstep (se 1 (by rfl) ⟨4816988, by rfl⟩ : syracuseStep 6422651 = 9633977) B9633977
theorem B7233731 : Blo 1268452 7233731 := bstep (se 1 (by rfl) ⟨5425298, by rfl⟩ : syracuseStep 7233731 = 10850597) B10850597
theorem B4817171 : Blo 1268452 4817171 := bstep (se 1 (by rfl) ⟨3612878, by rfl⟩ : syracuseStep 4817171 = 7225757) B7225757
theorem B1524199 : Blo 1268452 1524199 := bstep (se 1 (by rfl) ⟨1143149, by rfl⟩ : syracuseStep 1524199 = 2286299) B2286299
theorem B2408935 : Blo 1268452 2408935 := bstep (se 1 (by rfl) ⟨1806701, by rfl⟩ : syracuseStep 2408935 = 3613403) B3613403
theorem B27828841 : Blo 1268452 27828841 := bstep (se 2 (by rfl) ⟨10435815, by rfl⟩ : syracuseStep 27828841 = 20871631) B20871631
theorem B1270431 : Blo 1268452 1270431 := bstep (se 1 (by rfl) ⟨952823, by rfl⟩ : syracuseStep 1270431 = 1905647) B1905647
theorem B10846973 : Blo 1268452 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B8127287 : Blo 1268452 8127287 := bstep (se 1 (by rfl) ⟨6095465, by rfl⟩ : syracuseStep 8127287 = 12190931) B12190931
theorem B6857527 : Blo 1268452 6857527 := bstep (se 1 (by rfl) ⟨5143145, by rfl⟩ : syracuseStep 6857527 = 10286291) B10286291
theorem B3212095 : Blo 1268452 3212095 := bstep (se 1 (by rfl) ⟨2409071, by rfl⟩ : syracuseStep 3212095 = 4818143) B4818143
theorem B3048329 : Blo 1268452 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B2934119 : Blo 1268452 2934119 := bstep (se 1 (by rfl) ⟨2200589, by rfl⟩ : syracuseStep 2934119 = 4401179) B4401179
theorem B13714883 : Blo 1268452 13714883 := bstep (se 1 (by rfl) ⟨10286162, by rfl⟩ : syracuseStep 13714883 = 20572325) B20572325
theorem B14460443 : Blo 1268452 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B1427035 : Blo 1268452 1427035 := bstep (se 1 (by rfl) ⟨1070276, by rfl⟩ : syracuseStep 1427035 = 2140553) B2140553
theorem B8128259 : Blo 1268452 8128259 := bstep (se 1 (by rfl) ⟨6096194, by rfl⟩ : syracuseStep 8128259 = 12192389) B12192389
theorem B3614473 : Blo 1268452 3614473 := bstep (se 2 (by rfl) ⟨1355427, by rfl⟩ : syracuseStep 3614473 = 2710855) B2710855
theorem B82306925 : Blo 1268452 82306925 := bstep (se 3 (by rfl) ⟨15432548, by rfl⟩ : syracuseStep 82306925 = 30865097) B30865097
theorem B13723667 : Blo 1268452 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B2033705 : Blo 1268452 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B4286843 : Blo 1268452 4286843 := bstep (se 1 (by rfl) ⟨3215132, by rfl⟩ : syracuseStep 4286843 = 6430265) B6430265
theorem B4286951 : Blo 1268452 4286951 := bstep (se 1 (by rfl) ⟨3215213, by rfl⟩ : syracuseStep 4286951 = 6430427) B6430427
theorem B7227899 : Blo 1268452 7227899 := bstep (se 1 (by rfl) ⟨5420924, by rfl⟩ : syracuseStep 7227899 = 10841849) B10841849
theorem B1903151 : Blo 1268452 1903151 := bstep (se 1 (by rfl) ⟨1427363, by rfl⟩ : syracuseStep 1903151 = 2854727) B2854727
theorem B4950575 : Blo 1268452 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B1903271 : Blo 1268452 1903271 := bstep (se 1 (by rfl) ⟨1427453, by rfl⟩ : syracuseStep 1903271 = 2854907) B2854907
theorem B1428187 : Blo 1268452 1428187 := bstep (se 1 (by rfl) ⟨1071140, by rfl⟩ : syracuseStep 1428187 = 2142281) B2142281
theorem B1903337 : Blo 1268452 1903337 := bstep (se 2 (by rfl) ⟨713751, by rfl⟩ : syracuseStep 1903337 = 1427503) B1427503
theorem B1903343 : Blo 1268452 1903343 := bstep (se 1 (by rfl) ⟨1427507, by rfl⟩ : syracuseStep 1903343 = 2855015) B2855015
theorem B1428223 : Blo 1268452 1428223 := bstep (se 1 (by rfl) ⟨1071167, by rfl⟩ : syracuseStep 1428223 = 2142335) B2142335
theorem B1903391 : Blo 1268452 1903391 := bstep (se 1 (by rfl) ⟨1427543, by rfl⟩ : syracuseStep 1903391 = 2855087) B2855087
theorem B6425405 : Blo 1268452 6425405 := bstep (se 3 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 6425405 = 2409527) B2409527
theorem B3214201 : Blo 1268452 3214201 := bstep (se 2 (by rfl) ⟨1205325, by rfl⟩ : syracuseStep 3214201 = 2410651) B2410651
theorem B2411471 : Blo 1268452 2411471 := bstep (se 1 (by rfl) ⟨1808603, by rfl⟩ : syracuseStep 2411471 = 3617207) B3617207
theorem B9636893 : Blo 1268452 9636893 := bstep (se 3 (by rfl) ⟨1806917, by rfl⟩ : syracuseStep 9636893 = 3613835) B3613835
theorem B1903721 : Blo 1268452 1903721 := bstep (se 2 (by rfl) ⟨713895, by rfl⟩ : syracuseStep 1903721 = 1427791) B1427791
theorem B3214505 : Blo 1268452 3214505 := bstep (se 2 (by rfl) ⟨1205439, by rfl⟩ : syracuseStep 3214505 = 2410879) B2410879
theorem B3615931 : Blo 1268452 3615931 := bstep (se 1 (by rfl) ⟨2711948, by rfl⟩ : syracuseStep 3615931 = 5423897) B5423897
theorem B1903847 : Blo 1268452 1903847 := bstep (se 1 (by rfl) ⟨1427885, by rfl⟩ : syracuseStep 1903847 = 2855771) B2855771
theorem B18312571 : Blo 1268452 18312571 := bstep (se 1 (by rfl) ⟨13734428, by rfl⟩ : syracuseStep 18312571 = 27468857) B27468857
theorem B14667161 : Blo 1268452 14667161 := bstep (se 2 (by rfl) ⟨5500185, by rfl⟩ : syracuseStep 14667161 = 11000371) B11000371
theorem B3616159 : Blo 1268452 3616159 := bstep (se 1 (by rfl) ⟨2712119, by rfl⟩ : syracuseStep 3616159 = 5424239) B5424239
theorem B1428943 : Blo 1268452 1428943 := bstep (se 1 (by rfl) ⟨1071707, by rfl⟩ : syracuseStep 1428943 = 2143415) B2143415
theorem B6426215 : Blo 1268452 6426215 := bstep (se 1 (by rfl) ⟨4819661, by rfl⟩ : syracuseStep 6426215 = 9639323) B9639323
theorem B1904351 : Blo 1268452 1904351 := bstep (se 1 (by rfl) ⟨1428263, by rfl⟩ : syracuseStep 1904351 = 2856527) B2856527
theorem B3616751 : Blo 1268452 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B1904633 : Blo 1268452 1904633 := bstep (se 2 (by rfl) ⟨714237, by rfl⟩ : syracuseStep 1904633 = 1428475) B1428475
theorem B1904831 : Blo 1268452 1904831 := bstep (se 1 (by rfl) ⟨1428623, by rfl⟩ : syracuseStep 1904831 = 2857247) B2857247
theorem B1904873 : Blo 1268452 1904873 := bstep (se 2 (by rfl) ⟨714327, by rfl⟩ : syracuseStep 1904873 = 1428655) B1428655
theorem B4821227 : Blo 1268452 4821227 := bstep (se 1 (by rfl) ⟨3615920, by rfl⟩ : syracuseStep 4821227 = 7231841) B7231841
theorem B3215609 : Blo 1268452 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B2142463 : Blo 1268452 2142463 := bstep (se 1 (by rfl) ⟨1606847, by rfl⟩ : syracuseStep 2142463 = 3213695) B3213695
theorem B1904999 : Blo 1268452 1904999 := bstep (se 1 (by rfl) ⟨1428749, by rfl⟩ : syracuseStep 1904999 = 2857499) B2857499
theorem B14463359 : Blo 1268452 14463359 := bstep (se 1 (by rfl) ⟨10847519, by rfl⟩ : syracuseStep 14463359 = 21695039) B21695039
theorem B5419507 : Blo 1268452 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B1806895 : Blo 1268452 1806895 := bstep (se 1 (by rfl) ⟨1355171, by rfl⟩ : syracuseStep 1806895 = 2710343) B2710343
theorem B5419831 : Blo 1268452 5419831 := bstep (se 1 (by rfl) ⟨4064873, by rfl⟩ : syracuseStep 5419831 = 8129747) B8129747
theorem B7328593 : Blo 1268452 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B2143145 : Blo 1268452 2143145 := bstep (se 2 (by rfl) ⟨803679, by rfl⟩ : syracuseStep 2143145 = 1607359) B1607359
theorem B15651791 : Blo 1268452 15651791 := bstep (se 1 (by rfl) ⟨11738843, by rfl⟩ : syracuseStep 15651791 = 23477687) B23477687
theorem B11580545 : Blo 1268452 11580545 := bstep (se 2 (by rfl) ⟨4342704, by rfl⟩ : syracuseStep 11580545 = 8685409) B8685409
theorem B4822199 : Blo 1268452 4822199 := bstep (se 1 (by rfl) ⟨3616649, by rfl⟩ : syracuseStep 4822199 = 7233299) B7233299
theorem B9655595 : Blo 1268452 9655595 := bstep (se 1 (by rfl) ⟨7241696, by rfl⟩ : syracuseStep 9655595 = 14483393) B14483393
theorem B2897399 : Blo 1268452 2897399 := bstep (se 1 (by rfl) ⟨2173049, by rfl⟩ : syracuseStep 2897399 = 4346099) B4346099
theorem B7231133 : Blo 1268452 7231133 := bstep (se 3 (by rfl) ⟨1355837, by rfl⟩ : syracuseStep 7231133 = 2711675) B2711675
theorem B8689355 : Blo 1268452 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B2709215 : Blo 1268452 2709215 := bstep (se 1 (by rfl) ⟨2031911, by rfl⟩ : syracuseStep 2709215 = 4063823) B4063823
theorem B4823003 : Blo 1268452 4823003 := bstep (se 1 (by rfl) ⟨3617252, by rfl⟩ : syracuseStep 4823003 = 7234505) B7234505
theorem B5421163 : Blo 1268452 5421163 := bstep (se 1 (by rfl) ⟨4065872, by rfl⟩ : syracuseStep 5421163 = 8131745) B8131745
theorem B2857319 : Blo 1268452 2857319 := bstep (se 1 (by rfl) ⟨2142989, by rfl⟩ : syracuseStep 2857319 = 4285979) B4285979
theorem B4823657 : Blo 1268452 4823657 := bstep (se 2 (by rfl) ⟨1808871, by rfl⟩ : syracuseStep 4823657 = 3617743) B3617743
theorem B2857697 : Blo 1268452 2857697 := bstep (se 2 (by rfl) ⟨1071636, by rfl⟩ : syracuseStep 2857697 = 2143273) B2143273
theorem B4578059 : Blo 1268452 4578059 := bstep (se 1 (by rfl) ⟨3433544, by rfl⟩ : syracuseStep 4578059 = 6867089) B6867089
theorem B1268543 : Blo 1268452 1268543 := bstep (se 1 (by rfl) ⟨951407, by rfl⟩ : syracuseStep 1268543 = 1902815) B1902815
theorem B1268583 : Blo 1268452 1268583 := bstep (se 1 (by rfl) ⟨951437, by rfl⟩ : syracuseStep 1268583 = 1902875) B1902875
theorem B32529437 : Blo 1268452 32529437 := bstep (se 3 (by rfl) ⟨6099269, by rfl⟩ : syracuseStep 32529437 = 12198539) B12198539
theorem B1268799 : Blo 1268452 1268799 := bstep (se 1 (by rfl) ⟨951599, by rfl⟩ : syracuseStep 1268799 = 1903199) B1903199
theorem B5422241 : Blo 1268452 5422241 := bstep (se 2 (by rfl) ⟨2033340, by rfl⟩ : syracuseStep 5422241 = 4066681) B4066681
theorem B1268987 : Blo 1268452 1268987 := bstep (se 1 (by rfl) ⟨951740, by rfl⟩ : syracuseStep 1268987 = 1903481) B1903481
theorem B1269019 : Blo 1268452 1269019 := bstep (se 1 (by rfl) ⟨951764, by rfl⟩ : syracuseStep 1269019 = 1903529) B1903529
theorem B1269119 : Blo 1268452 1269119 := bstep (se 1 (by rfl) ⟨951839, by rfl⟩ : syracuseStep 1269119 = 1903679) B1903679
theorem B4283873 : Blo 1268452 4283873 := bstep (se 2 (by rfl) ⟨1606452, by rfl⟩ : syracuseStep 4283873 = 3212905) B3212905
theorem B2711009 : Blo 1268452 2711009 := bstep (se 2 (by rfl) ⟨1016628, by rfl⟩ : syracuseStep 2711009 = 2033257) B2033257
theorem B4816367 : Blo 1268452 4816367 := bstep (se 1 (by rfl) ⟨3612275, by rfl⟩ : syracuseStep 4816367 = 7224551) B7224551
theorem B1269487 : Blo 1268452 1269487 := bstep (se 1 (by rfl) ⟨952115, by rfl⟩ : syracuseStep 1269487 = 1904231) B1904231
theorem B32988959 : Blo 1268452 32988959 := bstep (se 1 (by rfl) ⟨24741719, by rfl⟩ : syracuseStep 32988959 = 49483439) B49483439
theorem B1269743 : Blo 1268452 1269743 := bstep (se 1 (by rfl) ⟨952307, by rfl⟩ : syracuseStep 1269743 = 1904615) B1904615
theorem B5423213 : Blo 1268452 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B1269887 : Blo 1268452 1269887 := bstep (se 1 (by rfl) ⟨952415, by rfl⟩ : syracuseStep 1269887 = 1904831) B1904831
theorem B1269915 : Blo 1268452 1269915 := bstep (se 1 (by rfl) ⟨952436, by rfl⟩ : syracuseStep 1269915 = 1904873) B1904873
theorem B3211447 : Blo 1268452 3211447 := bstep (se 1 (by rfl) ⟨2408585, by rfl⟩ : syracuseStep 3211447 = 4817171) B4817171
theorem B1269999 : Blo 1268452 1269999 := bstep (se 1 (by rfl) ⟨952499, by rfl⟩ : syracuseStep 1269999 = 1904999) B1904999
theorem B9642239 : Blo 1268452 9642239 := bstep (se 1 (by rfl) ⟨7231679, by rfl⟩ : syracuseStep 9642239 = 14463359) B14463359
theorem B2032219 : Blo 1268452 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B2032265 : Blo 1268452 2032265 := bstep (se 2 (by rfl) ⟨762099, by rfl⟩ : syracuseStep 2032265 = 1524199) B1524199
theorem B3211913 : Blo 1268452 3211913 := bstep (se 2 (by rfl) ⟨1204467, by rfl⟩ : syracuseStep 3211913 = 2408935) B2408935
theorem B7226009 : Blo 1268452 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B2409193 : Blo 1268452 2409193 := bstep (se 2 (by rfl) ⟨903447, by rfl⟩ : syracuseStep 2409193 = 1806895) B1806895
theorem B9143255 : Blo 1268452 9143255 := bstep (se 1 (by rfl) ⟨6857441, by rfl⟩ : syracuseStep 9143255 = 13714883) B13714883
theorem B9143369 : Blo 1268452 9143369 := bstep (se 2 (by rfl) ⟨3428763, by rfl⟩ : syracuseStep 9143369 = 6857527) B6857527
theorem B7226441 : Blo 1268452 7226441 := bstep (se 2 (by rfl) ⟨2709915, by rfl⟩ : syracuseStep 7226441 = 5419831) B5419831
theorem B5792903 : Blo 1268452 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B4285601 : Blo 1268452 4285601 := bstep (se 2 (by rfl) ⟨1607100, by rfl⟩ : syracuseStep 4285601 = 3214201) B3214201
theorem B54871283 : Blo 1268452 54871283 := bstep (se 1 (by rfl) ⟨41153462, by rfl⟩ : syracuseStep 54871283 = 82306925) B82306925
theorem B4818599 : Blo 1268452 4818599 := bstep (se 1 (by rfl) ⟨3613949, by rfl⟩ : syracuseStep 4818599 = 7227899) B7227899
theorem B6424595 : Blo 1268452 6424595 := bstep (se 1 (by rfl) ⟨4818446, by rfl⟩ : syracuseStep 6424595 = 9636893) B9636893
theorem B21686291 : Blo 1268452 21686291 := bstep (se 1 (by rfl) ⟨16264718, by rfl⟩ : syracuseStep 21686291 = 32529437) B32529437
theorem B3614827 : Blo 1268452 3614827 := bstep (se 1 (by rfl) ⟨2711120, by rfl⟩ : syracuseStep 3614827 = 5422241) B5422241
theorem B1902713 : Blo 1268452 1902713 := bstep (se 2 (by rfl) ⟨713517, by rfl⟩ : syracuseStep 1902713 = 1427035) B1427035
theorem B4819297 : Blo 1268452 4819297 := bstep (se 2 (by rfl) ⟨1807236, by rfl⟩ : syracuseStep 4819297 = 3614473) B3614473
theorem B9644669 : Blo 1268452 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B7228217 : Blo 1268452 7228217 := bstep (se 2 (by rfl) ⟨2710581, by rfl⟩ : syracuseStep 7228217 = 5421163) B5421163
theorem B3214151 : Blo 1268452 3214151 := bstep (se 1 (by rfl) ⟨2410613, by rfl⟩ : syracuseStep 3214151 = 4821227) B4821227
theorem B5418191 : Blo 1268452 5418191 := bstep (se 1 (by rfl) ⟨4063643, by rfl⟩ : syracuseStep 5418191 = 8127287) B8127287
theorem B1428763 : Blo 1268452 1428763 := bstep (se 1 (by rfl) ⟨1071572, by rfl⟩ : syracuseStep 1428763 = 2143145) B2143145
theorem B7720363 : Blo 1268452 7720363 := bstep (se 1 (by rfl) ⟨5790272, by rfl⟩ : syracuseStep 7720363 = 11580545) B11580545
theorem B3214799 : Blo 1268452 3214799 := bstep (se 1 (by rfl) ⟨2411099, by rfl⟩ : syracuseStep 3214799 = 4822199) B4822199
theorem B37105121 : Blo 1268452 37105121 := bstep (se 2 (by rfl) ⟨13914420, by rfl⟩ : syracuseStep 37105121 = 27828841) B27828841
theorem B1904249 : Blo 1268452 1904249 := bstep (se 2 (by rfl) ⟨714093, by rfl⟩ : syracuseStep 1904249 = 1428187) B1428187
theorem B1904297 : Blo 1268452 1904297 := bstep (se 2 (by rfl) ⟨714111, by rfl⟩ : syracuseStep 1904297 = 1428223) B1428223
theorem B39112429 : Blo 1268452 39112429 := bstep (se 3 (by rfl) ⟨7333580, by rfl⟩ : syracuseStep 39112429 = 14667161) B14667161
theorem B4820755 : Blo 1268452 4820755 := bstep (se 1 (by rfl) ⟨3615566, by rfl⟩ : syracuseStep 4820755 = 7231133) B7231133
theorem B1806143 : Blo 1268452 1806143 := bstep (se 1 (by rfl) ⟨1354607, by rfl⟩ : syracuseStep 1806143 = 2709215) B2709215
theorem B5418839 : Blo 1268452 5418839 := bstep (se 1 (by rfl) ⟨4064129, by rfl⟩ : syracuseStep 5418839 = 8128259) B8128259
theorem B7229357 : Blo 1268452 7229357 := bstep (se 3 (by rfl) ⟨1355504, by rfl⟩ : syracuseStep 7229357 = 2711009) B2711009
theorem B3215335 : Blo 1268452 3215335 := bstep (se 1 (by rfl) ⟨2411501, by rfl⟩ : syracuseStep 3215335 = 4823003) B4823003
theorem B1904879 : Blo 1268452 1904879 := bstep (se 1 (by rfl) ⟨1428659, by rfl⟩ : syracuseStep 1904879 = 2857319) B2857319
theorem B4821241 : Blo 1268452 4821241 := bstep (se 2 (by rfl) ⟨1807965, by rfl⟩ : syracuseStep 4821241 = 3615931) B3615931
theorem B3215771 : Blo 1268452 3215771 := bstep (se 1 (by rfl) ⟨2411828, by rfl⟩ : syracuseStep 3215771 = 4823657) B4823657
theorem B1905131 : Blo 1268452 1905131 := bstep (se 1 (by rfl) ⟨1428848, by rfl⟩ : syracuseStep 1905131 = 2857697) B2857697
theorem B24416761 : Blo 1268452 24416761 := bstep (se 2 (by rfl) ⟨9156285, by rfl⟩ : syracuseStep 24416761 = 18312571) B18312571
theorem B3052039 : Blo 1268452 3052039 := bstep (se 1 (by rfl) ⟨2289029, by rfl⟩ : syracuseStep 3052039 = 4578059) B4578059
theorem B4821545 : Blo 1268452 4821545 := bstep (se 2 (by rfl) ⟨1808079, by rfl⟩ : syracuseStep 4821545 = 3616159) B3616159
theorem B1905257 : Blo 1268452 1905257 := bstep (se 2 (by rfl) ⟨714471, by rfl⟩ : syracuseStep 1905257 = 1428943) B1428943
theorem B2143003 : Blo 1268452 2143003 := bstep (se 1 (by rfl) ⟨1607252, by rfl⟩ : syracuseStep 2143003 = 3214505) B3214505
theorem B2855915 : Blo 1268452 2855915 := bstep (se 1 (by rfl) ⟨2141936, by rfl⟩ : syracuseStep 2855915 = 4283873) B4283873
theorem B21992639 : Blo 1268452 21992639 := bstep (se 1 (by rfl) ⟨16494479, by rfl⟩ : syracuseStep 21992639 = 32988959) B32988959
theorem B4281767 : Blo 1268452 4281767 := bstep (se 1 (by rfl) ⟨3211325, by rfl⟩ : syracuseStep 4281767 = 6422651) B6422651
theorem B4822487 : Blo 1268452 4822487 := bstep (se 1 (by rfl) ⟨3616865, by rfl⟩ : syracuseStep 4822487 = 7233731) B7233731
theorem B2143739 : Blo 1268452 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B2856617 : Blo 1268452 2856617 := bstep (se 2 (by rfl) ⟨1071231, by rfl⟩ : syracuseStep 2856617 = 2142463) B2142463
theorem B7231315 : Blo 1268452 7231315 := bstep (se 1 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 7231315 = 10846973) B10846973
theorem B10434527 : Blo 1268452 10434527 := bstep (se 1 (by rfl) ⟨7825895, by rfl⟩ : syracuseStep 10434527 = 15651791) B15651791
theorem B6437063 : Blo 1268452 6437063 := bstep (se 1 (by rfl) ⟨4827797, by rfl⟩ : syracuseStep 6437063 = 9655595) B9655595
theorem B1956079 : Blo 1268452 1956079 := bstep (se 1 (by rfl) ⟨1467059, by rfl⟩ : syracuseStep 1956079 = 2934119) B2934119
theorem B1931599 : Blo 1268452 1931599 := bstep (se 1 (by rfl) ⟨1448699, by rfl⟩ : syracuseStep 1931599 = 2897399) B2897399
theorem B9640295 : Blo 1268452 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B4282793 : Blo 1268452 4282793 := bstep (se 2 (by rfl) ⟨1606047, by rfl⟩ : syracuseStep 4282793 = 3212095) B3212095
theorem B9771457 : Blo 1268452 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B9149111 : Blo 1268452 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B2857895 : Blo 1268452 2857895 := bstep (se 1 (by rfl) ⟨2143421, by rfl⟩ : syracuseStep 2857895 = 4286843) B4286843
theorem B2857967 : Blo 1268452 2857967 := bstep (se 1 (by rfl) ⟨2143475, by rfl⟩ : syracuseStep 2857967 = 4286951) B4286951
theorem B1268767 : Blo 1268452 1268767 := bstep (se 1 (by rfl) ⟨951575, by rfl⟩ : syracuseStep 1268767 = 1903151) B1903151
theorem B3300383 : Blo 1268452 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B1268847 : Blo 1268452 1268847 := bstep (se 1 (by rfl) ⟨951635, by rfl⟩ : syracuseStep 1268847 = 1903271) B1903271
theorem B1268891 : Blo 1268452 1268891 := bstep (se 1 (by rfl) ⟨951668, by rfl⟩ : syracuseStep 1268891 = 1903337) B1903337
theorem B1268895 : Blo 1268452 1268895 := bstep (se 1 (by rfl) ⟨951671, by rfl⟩ : syracuseStep 1268895 = 1903343) B1903343
theorem B1268927 : Blo 1268452 1268927 := bstep (se 1 (by rfl) ⟨951695, by rfl⟩ : syracuseStep 1268927 = 1903391) B1903391
theorem B4283603 : Blo 1268452 4283603 := bstep (se 1 (by rfl) ⟨3212702, by rfl⟩ : syracuseStep 4283603 = 6425405) B6425405
theorem B1269147 : Blo 1268452 1269147 := bstep (se 1 (by rfl) ⟨951860, by rfl⟩ : syracuseStep 1269147 = 1903721) B1903721
theorem B1269231 : Blo 1268452 1269231 := bstep (se 1 (by rfl) ⟨951923, by rfl⟩ : syracuseStep 1269231 = 1903847) B1903847
theorem B3210911 : Blo 1268452 3210911 := bstep (se 1 (by rfl) ⟨2408183, by rfl⟩ : syracuseStep 3210911 = 4816367) B4816367
theorem B4284143 : Blo 1268452 4284143 := bstep (se 1 (by rfl) ⟨3213107, by rfl⟩ : syracuseStep 4284143 = 6426215) B6426215
theorem B1269567 : Blo 1268452 1269567 := bstep (se 1 (by rfl) ⟨952175, by rfl⟩ : syracuseStep 1269567 = 1904351) B1904351
theorem B6430589 : Blo 1268452 6430589 := bstep (se 3 (by rfl) ⟨1205735, by rfl⟩ : syracuseStep 6430589 = 2411471) B2411471
theorem B1269755 : Blo 1268452 1269755 := bstep (se 1 (by rfl) ⟨952316, by rfl⟩ : syracuseStep 1269755 = 1904633) B1904633
theorem B1269919 : Blo 1268452 1269919 := bstep (se 1 (by rfl) ⟨952439, by rfl⟩ : syracuseStep 1269919 = 1904879) B1904879
theorem B1270087 : Blo 1268452 1270087 := bstep (se 1 (by rfl) ⟨952565, by rfl⟩ : syracuseStep 1270087 = 1905131) B1905131
theorem B1270171 : Blo 1268452 1270171 := bstep (se 1 (by rfl) ⟨952628, by rfl⟩ : syracuseStep 1270171 = 1905257) B1905257
theorem B4817339 : Blo 1268452 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B58647037 : Blo 1268452 58647037 := bstep (se 3 (by rfl) ⟨10996319, by rfl⟩ : syracuseStep 58647037 = 21992639) B21992639
theorem B6095503 : Blo 1268452 6095503 := bstep (se 1 (by rfl) ⟨4571627, by rfl⟩ : syracuseStep 6095503 = 9143255) B9143255
theorem B32555681 : Blo 1268452 32555681 := bstep (se 2 (by rfl) ⟨12208380, by rfl⟩ : syracuseStep 32555681 = 24416761) B24416761
theorem B6095579 : Blo 1268452 6095579 := bstep (se 1 (by rfl) ⟨4571684, by rfl⟩ : syracuseStep 6095579 = 9143369) B9143369
theorem B4817627 : Blo 1268452 4817627 := bstep (se 1 (by rfl) ⟨3613220, by rfl⟩ : syracuseStep 4817627 = 7226441) B7226441
theorem B3212257 : Blo 1268452 3212257 := bstep (se 2 (by rfl) ⟨1204596, by rfl⟩ : syracuseStep 3212257 = 2409193) B2409193
theorem B3212399 : Blo 1268452 3212399 := bstep (se 1 (by rfl) ⟨2409299, by rfl⟩ : syracuseStep 3212399 = 4818599) B4818599
theorem B6956351 : Blo 1268452 6956351 := bstep (se 1 (by rfl) ⟨5217263, by rfl⟩ : syracuseStep 6956351 = 10434527) B10434527
theorem B4818811 : Blo 1268452 4818811 := bstep (se 1 (by rfl) ⟨3614108, by rfl⟩ : syracuseStep 4818811 = 7228217) B7228217
theorem B2140607 : Blo 1268452 2140607 := bstep (se 1 (by rfl) ⟨1605455, by rfl⟩ : syracuseStep 2140607 = 3210911) B3210911
theorem B4287059 : Blo 1268452 4287059 := bstep (se 1 (by rfl) ⟨3215294, by rfl⟩ : syracuseStep 4287059 = 6430589) B6430589
theorem B4819571 : Blo 1268452 4819571 := bstep (se 1 (by rfl) ⟨3614678, by rfl⟩ : syracuseStep 4819571 = 7229357) B7229357
theorem B4287113 : Blo 1268452 4287113 := bstep (se 2 (by rfl) ⟨1607667, by rfl⟩ : syracuseStep 4287113 = 3215335) B3215335
theorem B4819769 : Blo 1268452 4819769 := bstep (se 2 (by rfl) ⟨1807413, by rfl⟩ : syracuseStep 4819769 = 3614827) B3614827
theorem B14461901 : Blo 1268452 14461901 := bstep (se 3 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 14461901 = 5423213) B5423213
theorem B2608105 : Blo 1268452 2608105 := bstep (se 2 (by rfl) ⟨978039, by rfl⟩ : syracuseStep 2608105 = 1956079) B1956079
theorem B3214363 : Blo 1268452 3214363 := bstep (se 1 (by rfl) ⟨2410772, by rfl⟩ : syracuseStep 3214363 = 4821545) B4821545
theorem B1354843 : Blo 1268452 1354843 := bstep (se 1 (by rfl) ⟨1016132, by rfl⟩ : syracuseStep 1354843 = 2032265) B2032265
theorem B2141275 : Blo 1268452 2141275 := bstep (se 1 (by rfl) ⟨1605956, by rfl⟩ : syracuseStep 2141275 = 3211913) B3211913
theorem B2575465 : Blo 1268452 2575465 := bstep (se 2 (by rfl) ⟨965799, by rfl⟩ : syracuseStep 2575465 = 1931599) B1931599
theorem B6425729 : Blo 1268452 6425729 := bstep (se 2 (by rfl) ⟨2409648, by rfl⟩ : syracuseStep 6425729 = 4819297) B4819297
theorem B13028609 : Blo 1268452 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B1903943 : Blo 1268452 1903943 := bstep (se 1 (by rfl) ⟨1427957, by rfl⟩ : syracuseStep 1903943 = 2855915) B2855915
theorem B3861935 : Blo 1268452 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B36580855 : Blo 1268452 36580855 := bstep (se 1 (by rfl) ⟨27435641, by rfl⟩ : syracuseStep 36580855 = 54871283) B54871283
theorem B2854511 : Blo 1268452 2854511 := bstep (se 1 (by rfl) ⟨2140883, by rfl⟩ : syracuseStep 2854511 = 4281767) B4281767
theorem B3214991 : Blo 1268452 3214991 := bstep (se 1 (by rfl) ⟨2411243, by rfl⟩ : syracuseStep 3214991 = 4822487) B4822487
theorem B1429159 : Blo 1268452 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B1904411 : Blo 1268452 1904411 := bstep (se 1 (by rfl) ⟨1428308, by rfl⟩ : syracuseStep 1904411 = 2856617) B2856617
theorem B6426863 : Blo 1268452 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B2855195 : Blo 1268452 2855195 := bstep (se 1 (by rfl) ⟨2141396, by rfl⟩ : syracuseStep 2855195 = 4282793) B4282793
theorem B1905017 : Blo 1268452 1905017 := bstep (se 2 (by rfl) ⟨714381, by rfl⟩ : syracuseStep 1905017 = 1428763) B1428763
theorem B6099407 : Blo 1268452 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B2142767 : Blo 1268452 2142767 := bstep (se 1 (by rfl) ⟨1607075, by rfl⟩ : syracuseStep 2142767 = 3214151) B3214151
theorem B10293817 : Blo 1268452 10293817 := bstep (se 2 (by rfl) ⟨3860181, by rfl⟩ : syracuseStep 10293817 = 7720363) B7720363
theorem B1905263 : Blo 1268452 1905263 := bstep (se 1 (by rfl) ⟨1428947, by rfl⟩ : syracuseStep 1905263 = 2857895) B2857895
theorem B1905311 : Blo 1268452 1905311 := bstep (se 1 (by rfl) ⟨1428983, by rfl⟩ : syracuseStep 1905311 = 2857967) B2857967
theorem B2200255 : Blo 1268452 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B2855735 : Blo 1268452 2855735 := bstep (se 1 (by rfl) ⟨2141801, by rfl⟩ : syracuseStep 2855735 = 4283603) B4283603
theorem B2143199 : Blo 1268452 2143199 := bstep (se 1 (by rfl) ⟨1607399, by rfl⟩ : syracuseStep 2143199 = 3214799) B3214799
theorem B24736747 : Blo 1268452 24736747 := bstep (se 1 (by rfl) ⟨18552560, by rfl⟩ : syracuseStep 24736747 = 37105121) B37105121
theorem B6427673 : Blo 1268452 6427673 := bstep (se 2 (by rfl) ⟨2410377, by rfl⟩ : syracuseStep 6427673 = 4820755) B4820755
theorem B2856095 : Blo 1268452 2856095 := bstep (se 1 (by rfl) ⟨2142071, by rfl⟩ : syracuseStep 2856095 = 4284143) B4284143
theorem B6428159 : Blo 1268452 6428159 := bstep (se 1 (by rfl) ⟨4821119, by rfl⟩ : syracuseStep 6428159 = 9642239) B9642239
theorem B4281929 : Blo 1268452 4281929 := bstep (se 2 (by rfl) ⟨1605723, by rfl⟩ : syracuseStep 4281929 = 3211447) B3211447
theorem B2143847 : Blo 1268452 2143847 := bstep (se 1 (by rfl) ⟨1607885, by rfl⟩ : syracuseStep 2143847 = 3215771) B3215771
theorem B6428321 : Blo 1268452 6428321 := bstep (se 2 (by rfl) ⟨2410620, by rfl⟩ : syracuseStep 6428321 = 4821241) B4821241
theorem B4069385 : Blo 1268452 4069385 := bstep (se 2 (by rfl) ⟨1526019, by rfl⟩ : syracuseStep 4069385 = 3052039) B3052039
theorem B2857067 : Blo 1268452 2857067 := bstep (se 1 (by rfl) ⟨2142800, by rfl⟩ : syracuseStep 2857067 = 4285601) B4285601
theorem B2709625 : Blo 1268452 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B2857337 : Blo 1268452 2857337 := bstep (se 2 (by rfl) ⟨1071501, by rfl⟩ : syracuseStep 2857337 = 2143003) B2143003
theorem B4283063 : Blo 1268452 4283063 := bstep (se 1 (by rfl) ⟨3212297, by rfl⟩ : syracuseStep 4283063 = 6424595) B6424595
theorem B14457527 : Blo 1268452 14457527 := bstep (se 1 (by rfl) ⟨10843145, by rfl⟩ : syracuseStep 14457527 = 21686291) B21686291
theorem B1268475 : Blo 1268452 1268475 := bstep (se 1 (by rfl) ⟨951356, by rfl⟩ : syracuseStep 1268475 = 1902713) B1902713
theorem B4291375 : Blo 1268452 4291375 := bstep (se 1 (by rfl) ⟨3218531, by rfl⟩ : syracuseStep 4291375 = 6437063) B6437063
theorem B6429779 : Blo 1268452 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B3612127 : Blo 1268452 3612127 := bstep (se 1 (by rfl) ⟨2709095, by rfl⟩ : syracuseStep 3612127 = 5418191) B5418191
theorem B4816381 : Blo 1268452 4816381 := bstep (se 3 (by rfl) ⟨903071, by rfl⟩ : syracuseStep 4816381 = 1806143) B1806143
theorem B14450237 : Blo 1268452 14450237 := bstep (se 3 (by rfl) ⟨2709419, by rfl⟩ : syracuseStep 14450237 = 5418839) B5418839
theorem B52149905 : Blo 1268452 52149905 := bstep (se 2 (by rfl) ⟨19556214, by rfl⟩ : syracuseStep 52149905 = 39112429) B39112429
theorem B1269499 : Blo 1268452 1269499 := bstep (se 1 (by rfl) ⟨952124, by rfl⟩ : syracuseStep 1269499 = 1904249) B1904249
theorem B9641753 : Blo 1268452 9641753 := bstep (se 2 (by rfl) ⟨3615657, by rfl⟩ : syracuseStep 9641753 = 7231315) B7231315
theorem B1269531 : Blo 1268452 1269531 := bstep (se 1 (by rfl) ⟨952148, by rfl⟩ : syracuseStep 1269531 = 1904297) B1904297
theorem B4284575 : Blo 1268452 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B3612833 : Blo 1268452 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B1270011 : Blo 1268452 1270011 := bstep (se 1 (by rfl) ⟨952508, by rfl⟩ : syracuseStep 1270011 = 1905017) B1905017
theorem B3211559 : Blo 1268452 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B1270175 : Blo 1268452 1270175 := bstep (se 1 (by rfl) ⟨952631, by rfl⟩ : syracuseStep 1270175 = 1905263) B1905263
theorem B1270207 : Blo 1268452 1270207 := bstep (se 1 (by rfl) ⟨952655, by rfl⟩ : syracuseStep 1270207 = 1905311) B1905311
theorem B3211751 : Blo 1268452 3211751 := bstep (se 1 (by rfl) ⟨2408813, by rfl⟩ : syracuseStep 3211751 = 4817627) B4817627
theorem B4285115 : Blo 1268452 4285115 := bstep (se 1 (by rfl) ⟨3213836, by rfl⟩ : syracuseStep 4285115 = 6427673) B6427673
theorem B8127337 : Blo 1268452 8127337 := bstep (se 2 (by rfl) ⟨3047751, by rfl⟩ : syracuseStep 8127337 = 6095503) B6095503
theorem B4637567 : Blo 1268452 4637567 := bstep (se 1 (by rfl) ⟨3478175, by rfl⟩ : syracuseStep 4637567 = 6956351) B6956351
theorem B4285439 : Blo 1268452 4285439 := bstep (se 1 (by rfl) ⟨3214079, by rfl⟩ : syracuseStep 4285439 = 6428159) B6428159
theorem B4285547 : Blo 1268452 4285547 := bstep (se 1 (by rfl) ⟨3214160, by rfl⟩ : syracuseStep 4285547 = 6428321) B6428321
theorem B32982329 : Blo 1268452 32982329 := bstep (se 2 (by rfl) ⟨12368373, by rfl⟩ : syracuseStep 32982329 = 24736747) B24736747
theorem B2712923 : Blo 1268452 2712923 := bstep (se 1 (by rfl) ⟨2034692, by rfl⟩ : syracuseStep 2712923 = 4069385) B4069385
theorem B4285817 : Blo 1268452 4285817 := bstep (se 2 (by rfl) ⟨1607181, by rfl⟩ : syracuseStep 4285817 = 3214363) B3214363
theorem B1427071 : Blo 1268452 1427071 := bstep (se 1 (by rfl) ⟨1070303, by rfl⟩ : syracuseStep 1427071 = 2140607) B2140607
theorem B3213047 : Blo 1268452 3213047 := bstep (se 1 (by rfl) ⟨2409785, by rfl⟩ : syracuseStep 3213047 = 4819571) B4819571
theorem B3213179 : Blo 1268452 3213179 := bstep (se 1 (by rfl) ⟨2409884, by rfl⟩ : syracuseStep 3213179 = 4819769) B4819769
theorem B16254877 : Blo 1268452 16254877 := bstep (se 3 (by rfl) ⟨3047789, by rfl⟩ : syracuseStep 16254877 = 6095579) B6095579
theorem B4286519 : Blo 1268452 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B8685739 : Blo 1268452 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B2574623 : Blo 1268452 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B1903007 : Blo 1268452 1903007 := bstep (se 1 (by rfl) ⟨1427255, by rfl⟩ : syracuseStep 1903007 = 2854511) B2854511
theorem B6425081 : Blo 1268452 6425081 := bstep (se 2 (by rfl) ⟨2409405, by rfl⟩ : syracuseStep 6425081 = 4818811) B4818811
theorem B1903463 : Blo 1268452 1903463 := bstep (se 1 (by rfl) ⟨1427597, by rfl⟩ : syracuseStep 1903463 = 2855195) B2855195
theorem B4066271 : Blo 1268452 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B1428511 : Blo 1268452 1428511 := bstep (se 1 (by rfl) ⟨1071383, by rfl⟩ : syracuseStep 1428511 = 2142767) B2142767
theorem B21703787 : Blo 1268452 21703787 := bstep (se 1 (by rfl) ⟨16277840, by rfl⟩ : syracuseStep 21703787 = 32555681) B32555681
theorem B1903823 : Blo 1268452 1903823 := bstep (se 1 (by rfl) ⟨1427867, by rfl⟩ : syracuseStep 1903823 = 2855735) B2855735
theorem B1428799 : Blo 1268452 1428799 := bstep (se 1 (by rfl) ⟨1071599, by rfl⟩ : syracuseStep 1428799 = 2143199) B2143199
theorem B78196049 : Blo 1268452 78196049 := bstep (se 2 (by rfl) ⟨29323518, by rfl⟩ : syracuseStep 78196049 = 58647037) B58647037
theorem B2141599 : Blo 1268452 2141599 := bstep (se 1 (by rfl) ⟨1606199, by rfl⟩ : syracuseStep 2141599 = 3212399) B3212399
theorem B13725089 : Blo 1268452 13725089 := bstep (se 2 (by rfl) ⟨5146908, by rfl⟩ : syracuseStep 13725089 = 10293817) B10293817
theorem B1904063 : Blo 1268452 1904063 := bstep (se 1 (by rfl) ⟨1428047, by rfl⟩ : syracuseStep 1904063 = 2856095) B2856095
theorem B2854619 : Blo 1268452 2854619 := bstep (se 1 (by rfl) ⟨2140964, by rfl⟩ : syracuseStep 2854619 = 4281929) B4281929
theorem B5721833 : Blo 1268452 5721833 := bstep (se 2 (by rfl) ⟨2145687, by rfl⟩ : syracuseStep 5721833 = 4291375) B4291375
theorem B1429231 : Blo 1268452 1429231 := bstep (se 1 (by rfl) ⟨1071923, by rfl⟩ : syracuseStep 1429231 = 2143847) B2143847
theorem B3477473 : Blo 1268452 3477473 := bstep (se 2 (by rfl) ⟨1304052, by rfl⟩ : syracuseStep 3477473 = 2608105) B2608105
theorem B1904711 : Blo 1268452 1904711 := bstep (se 1 (by rfl) ⟨1428533, by rfl⟩ : syracuseStep 1904711 = 2857067) B2857067
theorem B1806457 : Blo 1268452 1806457 := bstep (se 2 (by rfl) ⟨677421, by rfl⟩ : syracuseStep 1806457 = 1354843) B1354843
theorem B2855033 : Blo 1268452 2855033 := bstep (se 2 (by rfl) ⟨1070637, by rfl⟩ : syracuseStep 2855033 = 2141275) B2141275
theorem B1904891 : Blo 1268452 1904891 := bstep (se 1 (by rfl) ⟨1428668, by rfl⟩ : syracuseStep 1904891 = 2857337) B2857337
theorem B2855375 : Blo 1268452 2855375 := bstep (se 1 (by rfl) ⟨2141531, by rfl⟩ : syracuseStep 2855375 = 4283063) B4283063
theorem B9638351 : Blo 1268452 9638351 := bstep (se 1 (by rfl) ⟨7228763, by rfl⟩ : syracuseStep 9638351 = 14457527) B14457527
theorem B1905545 : Blo 1268452 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B2143327 : Blo 1268452 2143327 := bstep (se 1 (by rfl) ⟨1607495, by rfl⟩ : syracuseStep 2143327 = 3214991) B3214991
theorem B6427835 : Blo 1268452 6427835 := bstep (se 1 (by rfl) ⟨4820876, by rfl⟩ : syracuseStep 6427835 = 9641753) B9641753
theorem B13735813 : Blo 1268452 13735813 := bstep (se 4 (by rfl) ⟨1287732, by rfl⟩ : syracuseStep 13735813 = 2575465) B2575465
theorem B4283009 : Blo 1268452 4283009 := bstep (se 2 (by rfl) ⟨1606128, by rfl⟩ : syracuseStep 4283009 = 3212257) B3212257
theorem B46938773 : Blo 1268452 46938773 := bstep (se 6 (by rfl) ⟨1100127, by rfl⟩ : syracuseStep 46938773 = 2200255) B2200255
theorem B2858039 : Blo 1268452 2858039 := bstep (se 1 (by rfl) ⟨2143529, by rfl⟩ : syracuseStep 2858039 = 4287059) B4287059
theorem B2858075 : Blo 1268452 2858075 := bstep (se 1 (by rfl) ⟨2143556, by rfl⟩ : syracuseStep 2858075 = 4287113) B4287113
theorem B4816169 : Blo 1268452 4816169 := bstep (se 2 (by rfl) ⟨1806063, by rfl⟩ : syracuseStep 4816169 = 3612127) B3612127
theorem B9641267 : Blo 1268452 9641267 := bstep (se 1 (by rfl) ⟨7230950, by rfl⟩ : syracuseStep 9641267 = 14461901) B14461901
theorem B48774473 : Blo 1268452 48774473 := bstep (se 2 (by rfl) ⟨18290427, by rfl⟩ : syracuseStep 48774473 = 36580855) B36580855
theorem B6421841 : Blo 1268452 6421841 := bstep (se 2 (by rfl) ⟨2408190, by rfl⟩ : syracuseStep 6421841 = 4816381) B4816381
theorem B4283819 : Blo 1268452 4283819 := bstep (se 1 (by rfl) ⟨3212864, by rfl⟩ : syracuseStep 4283819 = 6425729) B6425729
theorem B1269295 : Blo 1268452 1269295 := bstep (se 1 (by rfl) ⟨951971, by rfl⟩ : syracuseStep 1269295 = 1903943) B1903943
theorem B9633491 : Blo 1268452 9633491 := bstep (se 1 (by rfl) ⟨7225118, by rfl⟩ : syracuseStep 9633491 = 14450237) B14450237
theorem B34766603 : Blo 1268452 34766603 := bstep (se 1 (by rfl) ⟨26074952, by rfl⟩ : syracuseStep 34766603 = 52149905) B52149905
theorem B1269607 : Blo 1268452 1269607 := bstep (se 1 (by rfl) ⟨952205, by rfl⟩ : syracuseStep 1269607 = 1904411) B1904411
theorem B1269807 : Blo 1268452 1269807 := bstep (se 1 (by rfl) ⟨952355, by rfl⟩ : syracuseStep 1269807 = 1904711) B1904711
theorem B2408555 : Blo 1268452 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B2408609 : Blo 1268452 2408609 := bstep (se 2 (by rfl) ⟨903228, by rfl⟩ : syracuseStep 2408609 = 1806457) B1806457
theorem B1269927 : Blo 1268452 1269927 := bstep (se 1 (by rfl) ⟨952445, by rfl⟩ : syracuseStep 1269927 = 1904891) B1904891
theorem B1270363 : Blo 1268452 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B6865661 : Blo 1268452 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B4285223 : Blo 1268452 4285223 := bstep (se 1 (by rfl) ⟨3213917, by rfl⟩ : syracuseStep 4285223 = 6427835) B6427835
theorem B21988219 : Blo 1268452 21988219 := bstep (se 1 (by rfl) ⟨16491164, by rfl⟩ : syracuseStep 21988219 = 32982329) B32982329
theorem B14469191 : Blo 1268452 14469191 := bstep (se 1 (by rfl) ⟨10851893, by rfl⟩ : syracuseStep 14469191 = 21703787) B21703787
theorem B1902761 : Blo 1268452 1902761 := bstep (se 2 (by rfl) ⟨713535, by rfl⟩ : syracuseStep 1902761 = 1427071) B1427071
theorem B32516315 : Blo 1268452 32516315 := bstep (se 1 (by rfl) ⟨24387236, by rfl⟩ : syracuseStep 32516315 = 48774473) B48774473
theorem B1903079 : Blo 1268452 1903079 := bstep (se 1 (by rfl) ⟨1427309, by rfl⟩ : syracuseStep 1903079 = 2854619) B2854619
theorem B23177735 : Blo 1268452 23177735 := bstep (se 1 (by rfl) ⟨17383301, by rfl⟩ : syracuseStep 23177735 = 34766603) B34766603
theorem B1903355 : Blo 1268452 1903355 := bstep (se 1 (by rfl) ⟨1427516, by rfl⟩ : syracuseStep 1903355 = 2855033) B2855033
theorem B2141039 : Blo 1268452 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B1903583 : Blo 1268452 1903583 := bstep (se 1 (by rfl) ⟨1427687, by rfl⟩ : syracuseStep 1903583 = 2855375) B2855375
theorem B6425567 : Blo 1268452 6425567 := bstep (se 1 (by rfl) ⟨4819175, by rfl⟩ : syracuseStep 6425567 = 9638351) B9638351
theorem B2141167 : Blo 1268452 2141167 := bstep (se 1 (by rfl) ⟨1605875, by rfl⟩ : syracuseStep 2141167 = 3211751) B3211751
theorem B2142031 : Blo 1268452 2142031 := bstep (se 1 (by rfl) ⟨1606523, by rfl⟩ : syracuseStep 2142031 = 3213047) B3213047
theorem B2142119 : Blo 1268452 2142119 := bstep (se 1 (by rfl) ⟨1606589, by rfl⟩ : syracuseStep 2142119 = 3213179) B3213179
theorem B1904681 : Blo 1268452 1904681 := bstep (se 2 (by rfl) ⟨714255, by rfl⟩ : syracuseStep 1904681 = 1428511) B1428511
theorem B1905065 : Blo 1268452 1905065 := bstep (se 2 (by rfl) ⟨714399, by rfl⟩ : syracuseStep 1905065 = 1428799) B1428799
theorem B2855339 : Blo 1268452 2855339 := bstep (se 1 (by rfl) ⟨2141504, by rfl⟩ : syracuseStep 2855339 = 4283009) B4283009
theorem B2855465 : Blo 1268452 2855465 := bstep (se 2 (by rfl) ⟨1070799, by rfl⟩ : syracuseStep 2855465 = 2141599) B2141599
theorem B1905359 : Blo 1268452 1905359 := bstep (se 1 (by rfl) ⟨1429019, by rfl⟩ : syracuseStep 1905359 = 2858039) B2858039
theorem B1905383 : Blo 1268452 1905383 := bstep (se 1 (by rfl) ⟨1429037, by rfl⟩ : syracuseStep 1905383 = 2858075) B2858075
theorem B6427511 : Blo 1268452 6427511 := bstep (se 1 (by rfl) ⟨4820633, by rfl⟩ : syracuseStep 6427511 = 9641267) B9641267
theorem B4281227 : Blo 1268452 4281227 := bstep (se 1 (by rfl) ⟨3210920, by rfl⟩ : syracuseStep 4281227 = 6421841) B6421841
theorem B52130699 : Blo 1268452 52130699 := bstep (se 1 (by rfl) ⟨39098024, by rfl⟩ : syracuseStep 52130699 = 78196049) B78196049
theorem B2855879 : Blo 1268452 2855879 := bstep (se 1 (by rfl) ⟨2141909, by rfl⟩ : syracuseStep 2855879 = 4283819) B4283819
theorem B1905641 : Blo 1268452 1905641 := bstep (se 2 (by rfl) ⟨714615, by rfl⟩ : syracuseStep 1905641 = 1429231) B1429231
theorem B12366845 : Blo 1268452 12366845 := bstep (se 3 (by rfl) ⟨2318783, by rfl⟩ : syracuseStep 12366845 = 4637567) B4637567
theorem B3814555 : Blo 1268452 3814555 := bstep (se 1 (by rfl) ⟨2860916, by rfl⟩ : syracuseStep 3814555 = 5721833) B5721833
theorem B18314417 : Blo 1268452 18314417 := bstep (se 2 (by rfl) ⟨6867906, by rfl⟩ : syracuseStep 18314417 = 13735813) B13735813
theorem B21673169 : Blo 1268452 21673169 := bstep (se 2 (by rfl) ⟨8127438, by rfl⟩ : syracuseStep 21673169 = 16254877) B16254877
theorem B2856383 : Blo 1268452 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B11580985 : Blo 1268452 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B2856743 : Blo 1268452 2856743 := bstep (se 1 (by rfl) ⟨2142557, by rfl⟩ : syracuseStep 2856743 = 4285115) B4285115
theorem B2856959 : Blo 1268452 2856959 := bstep (se 1 (by rfl) ⟨2142719, by rfl⟩ : syracuseStep 2856959 = 4285439) B4285439
theorem B2857031 : Blo 1268452 2857031 := bstep (se 1 (by rfl) ⟨2142773, by rfl⟩ : syracuseStep 2857031 = 4285547) B4285547
theorem B1808615 : Blo 1268452 1808615 := bstep (se 1 (by rfl) ⟨1356461, by rfl⟩ : syracuseStep 1808615 = 2712923) B2712923
theorem B2857211 : Blo 1268452 2857211 := bstep (se 1 (by rfl) ⟨2142908, by rfl⟩ : syracuseStep 2857211 = 4285817) B4285817
theorem B10836449 : Blo 1268452 10836449 := bstep (se 2 (by rfl) ⟨4063668, by rfl⟩ : syracuseStep 10836449 = 8127337) B8127337
theorem B2857679 : Blo 1268452 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B2857769 : Blo 1268452 2857769 := bstep (se 2 (by rfl) ⟨1071663, by rfl⟩ : syracuseStep 2857769 = 2143327) B2143327
theorem B1268671 : Blo 1268452 1268671 := bstep (se 1 (by rfl) ⟨951503, by rfl⟩ : syracuseStep 1268671 = 1903007) B1903007
theorem B4283387 : Blo 1268452 4283387 := bstep (se 1 (by rfl) ⟨3212540, by rfl⟩ : syracuseStep 4283387 = 6425081) B6425081
theorem B31292515 : Blo 1268452 31292515 := bstep (se 1 (by rfl) ⟨23469386, by rfl⟩ : syracuseStep 31292515 = 46938773) B46938773
theorem B1268975 : Blo 1268452 1268975 := bstep (se 1 (by rfl) ⟨951731, by rfl⟩ : syracuseStep 1268975 = 1903463) B1903463
theorem B2710847 : Blo 1268452 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B1269215 : Blo 1268452 1269215 := bstep (se 1 (by rfl) ⟨951911, by rfl⟩ : syracuseStep 1269215 = 1903823) B1903823
theorem B3210779 : Blo 1268452 3210779 := bstep (se 1 (by rfl) ⟨2408084, by rfl⟩ : syracuseStep 3210779 = 4816169) B4816169
theorem B9150059 : Blo 1268452 9150059 := bstep (se 1 (by rfl) ⟨6862544, by rfl⟩ : syracuseStep 9150059 = 13725089) B13725089
theorem B1269375 : Blo 1268452 1269375 := bstep (se 1 (by rfl) ⟨952031, by rfl⟩ : syracuseStep 1269375 = 1904063) B1904063
theorem B6422327 : Blo 1268452 6422327 := bstep (se 1 (by rfl) ⟨4816745, by rfl⟩ : syracuseStep 6422327 = 9633491) B9633491
theorem B2318315 : Blo 1268452 2318315 := bstep (se 1 (by rfl) ⟨1738736, by rfl⟩ : syracuseStep 2318315 = 3477473) B3477473
theorem B1269787 : Blo 1268452 1269787 := bstep (se 1 (by rfl) ⟨952340, by rfl⟩ : syracuseStep 1269787 = 1904681) B1904681
theorem B1605739 : Blo 1268452 1605739 := bstep (se 1 (by rfl) ⟨1204304, by rfl⟩ : syracuseStep 1605739 = 2408609) B2408609
theorem B1270043 : Blo 1268452 1270043 := bstep (se 1 (by rfl) ⟨952532, by rfl⟩ : syracuseStep 1270043 = 1905065) B1905065
theorem B6422813 : Blo 1268452 6422813 := bstep (se 3 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 6422813 = 2408555) B2408555
theorem B1270239 : Blo 1268452 1270239 := bstep (se 1 (by rfl) ⟨952679, by rfl⟩ : syracuseStep 1270239 = 1905359) B1905359
theorem B1270255 : Blo 1268452 1270255 := bstep (se 1 (by rfl) ⟨952691, by rfl⟩ : syracuseStep 1270255 = 1905383) B1905383
theorem B4285007 : Blo 1268452 4285007 := bstep (se 1 (by rfl) ⟨3213755, by rfl⟩ : syracuseStep 4285007 = 6427511) B6427511
theorem B1270427 : Blo 1268452 1270427 := bstep (se 1 (by rfl) ⟨952820, by rfl⟩ : syracuseStep 1270427 = 1905641) B1905641
theorem B41723353 : Blo 1268452 41723353 := bstep (se 2 (by rfl) ⟨15646257, by rfl⟩ : syracuseStep 41723353 = 31292515) B31292515
theorem B21677543 : Blo 1268452 21677543 := bstep (se 1 (by rfl) ⟨16258157, by rfl⟩ : syracuseStep 21677543 = 32516315) B32516315
theorem B15451823 : Blo 1268452 15451823 := bstep (se 1 (by rfl) ⟨11588867, by rfl⟩ : syracuseStep 15451823 = 23177735) B23177735
theorem B1427359 : Blo 1268452 1427359 := bstep (se 1 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 1427359 = 2141039) B2141039
theorem B2140519 : Blo 1268452 2140519 := bstep (se 1 (by rfl) ⟨1605389, by rfl⟩ : syracuseStep 2140519 = 3210779) B3210779
theorem B1428079 : Blo 1268452 1428079 := bstep (se 1 (by rfl) ⟨1071059, by rfl⟩ : syracuseStep 1428079 = 2142119) B2142119
theorem B1903559 : Blo 1268452 1903559 := bstep (se 1 (by rfl) ⟨1427669, by rfl⟩ : syracuseStep 1903559 = 2855339) B2855339
theorem B1903643 : Blo 1268452 1903643 := bstep (se 1 (by rfl) ⟨1427732, by rfl⟩ : syracuseStep 1903643 = 2855465) B2855465
theorem B2854151 : Blo 1268452 2854151 := bstep (se 1 (by rfl) ⟨2140613, by rfl⟩ : syracuseStep 2854151 = 4281227) B4281227
theorem B34753799 : Blo 1268452 34753799 := bstep (se 1 (by rfl) ⟨26065349, by rfl⟩ : syracuseStep 34753799 = 52130699) B52130699
theorem B1903919 : Blo 1268452 1903919 := bstep (se 1 (by rfl) ⟨1427939, by rfl⟩ : syracuseStep 1903919 = 2855879) B2855879
theorem B8244563 : Blo 1268452 8244563 := bstep (se 1 (by rfl) ⟨6183422, by rfl⟩ : syracuseStep 8244563 = 12366845) B12366845
theorem B12209611 : Blo 1268452 12209611 := bstep (se 1 (by rfl) ⟨9157208, by rfl⟩ : syracuseStep 12209611 = 18314417) B18314417
theorem B7228925 : Blo 1268452 7228925 := bstep (se 3 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 7228925 = 2710847) B2710847
theorem B1904255 : Blo 1268452 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B1904495 : Blo 1268452 1904495 := bstep (se 1 (by rfl) ⟨1428371, by rfl⟩ : syracuseStep 1904495 = 2856743) B2856743
theorem B2854889 : Blo 1268452 2854889 := bstep (se 2 (by rfl) ⟨1070583, by rfl⟩ : syracuseStep 2854889 = 2141167) B2141167
theorem B1904639 : Blo 1268452 1904639 := bstep (se 1 (by rfl) ⟨1428479, by rfl⟩ : syracuseStep 1904639 = 2856959) B2856959
theorem B1904687 : Blo 1268452 1904687 := bstep (se 1 (by rfl) ⟨1428515, by rfl⟩ : syracuseStep 1904687 = 2857031) B2857031
theorem B9646127 : Blo 1268452 9646127 := bstep (se 1 (by rfl) ⟨7234595, by rfl⟩ : syracuseStep 9646127 = 14469191) B14469191
theorem B1904807 : Blo 1268452 1904807 := bstep (se 1 (by rfl) ⟨1428605, by rfl⟩ : syracuseStep 1904807 = 2857211) B2857211
theorem B1905119 : Blo 1268452 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B1905179 : Blo 1268452 1905179 := bstep (se 1 (by rfl) ⟨1428884, by rfl⟩ : syracuseStep 1905179 = 2857769) B2857769
theorem B2855591 : Blo 1268452 2855591 := bstep (se 1 (by rfl) ⟨2141693, by rfl⟩ : syracuseStep 2855591 = 4283387) B4283387
theorem B6100039 : Blo 1268452 6100039 := bstep (se 1 (by rfl) ⟨4575029, by rfl⟩ : syracuseStep 6100039 = 9150059) B9150059
theorem B2856041 : Blo 1268452 2856041 := bstep (se 2 (by rfl) ⟨1071015, by rfl⟩ : syracuseStep 2856041 = 2142031) B2142031
theorem B4281551 : Blo 1268452 4281551 := bstep (se 1 (by rfl) ⟨3211163, by rfl⟩ : syracuseStep 4281551 = 6422327) B6422327
theorem B6182173 : Blo 1268452 6182173 := bstep (se 3 (by rfl) ⟨1159157, by rfl⟩ : syracuseStep 6182173 = 2318315) B2318315
theorem B61765253 : Blo 1268452 61765253 := bstep (se 4 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 61765253 = 11580985) B11580985
theorem B4577107 : Blo 1268452 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B2856815 : Blo 1268452 2856815 := bstep (se 1 (by rfl) ⟨2142611, by rfl⟩ : syracuseStep 2856815 = 4285223) B4285223
theorem B4822973 : Blo 1268452 4822973 := bstep (se 3 (by rfl) ⟨904307, by rfl⟩ : syracuseStep 4822973 = 1808615) B1808615
theorem B14448779 : Blo 1268452 14448779 := bstep (se 1 (by rfl) ⟨10836584, by rfl⟩ : syracuseStep 14448779 = 21673169) B21673169
theorem B29317625 : Blo 1268452 29317625 := bstep (se 2 (by rfl) ⟨10994109, by rfl⟩ : syracuseStep 29317625 = 21988219) B21988219
theorem B1268507 : Blo 1268452 1268507 := bstep (se 1 (by rfl) ⟨951380, by rfl⟩ : syracuseStep 1268507 = 1902761) B1902761
theorem B5086073 : Blo 1268452 5086073 := bstep (se 2 (by rfl) ⟨1907277, by rfl⟩ : syracuseStep 5086073 = 3814555) B3814555
theorem B7224299 : Blo 1268452 7224299 := bstep (se 1 (by rfl) ⟨5418224, by rfl⟩ : syracuseStep 7224299 = 10836449) B10836449
theorem B1268719 : Blo 1268452 1268719 := bstep (se 1 (by rfl) ⟨951539, by rfl⟩ : syracuseStep 1268719 = 1903079) B1903079
theorem B1268903 : Blo 1268452 1268903 := bstep (se 1 (by rfl) ⟨951677, by rfl⟩ : syracuseStep 1268903 = 1903355) B1903355
theorem B1269055 : Blo 1268452 1269055 := bstep (se 1 (by rfl) ⟨951791, by rfl⟩ : syracuseStep 1269055 = 1903583) B1903583
theorem B4283711 : Blo 1268452 4283711 := bstep (se 1 (by rfl) ⟨3212783, by rfl⟩ : syracuseStep 4283711 = 6425567) B6425567
theorem B1269791 : Blo 1268452 1269791 := bstep (se 1 (by rfl) ⟨952343, by rfl⟩ : syracuseStep 1269791 = 1904687) B1904687
theorem B6430751 : Blo 1268452 6430751 := bstep (se 1 (by rfl) ⟨4823063, by rfl⟩ : syracuseStep 6430751 = 9646127) B9646127
theorem B1269871 : Blo 1268452 1269871 := bstep (se 1 (by rfl) ⟨952403, by rfl⟩ : syracuseStep 1269871 = 1904807) B1904807
theorem B1270079 : Blo 1268452 1270079 := bstep (se 1 (by rfl) ⟨952559, by rfl⟩ : syracuseStep 1270079 = 1905119) B1905119
theorem B1270119 : Blo 1268452 1270119 := bstep (se 1 (by rfl) ⟨952589, by rfl⟩ : syracuseStep 1270119 = 1905179) B1905179
theorem B14451695 : Blo 1268452 14451695 := bstep (se 1 (by rfl) ⟨10838771, by rfl⟩ : syracuseStep 14451695 = 21677543) B21677543
theorem B16279481 : Blo 1268452 16279481 := bstep (se 2 (by rfl) ⟨6104805, by rfl⟩ : syracuseStep 16279481 = 12209611) B12209611
theorem B1902767 : Blo 1268452 1902767 := bstep (se 1 (by rfl) ⟨1427075, by rfl⟩ : syracuseStep 1902767 = 2854151) B2854151
theorem B23169199 : Blo 1268452 23169199 := bstep (se 1 (by rfl) ⟨17376899, by rfl⟩ : syracuseStep 23169199 = 34753799) B34753799
theorem B4819283 : Blo 1268452 4819283 := bstep (se 1 (by rfl) ⟨3614462, by rfl⟩ : syracuseStep 4819283 = 7228925) B7228925
theorem B1903145 : Blo 1268452 1903145 := bstep (se 2 (by rfl) ⟨713679, by rfl⟩ : syracuseStep 1903145 = 1427359) B1427359
theorem B1903259 : Blo 1268452 1903259 := bstep (se 1 (by rfl) ⟨1427444, by rfl⟩ : syracuseStep 1903259 = 2854889) B2854889
theorem B2140985 : Blo 1268452 2140985 := bstep (se 2 (by rfl) ⟨802869, by rfl⟩ : syracuseStep 2140985 = 1605739) B1605739
theorem B1903727 : Blo 1268452 1903727 := bstep (se 1 (by rfl) ⟨1427795, by rfl⟩ : syracuseStep 1903727 = 2855591) B2855591
theorem B2854025 : Blo 1268452 2854025 := bstep (se 2 (by rfl) ⟨1070259, by rfl⟩ : syracuseStep 2854025 = 2140519) B2140519
theorem B1904027 : Blo 1268452 1904027 := bstep (se 1 (by rfl) ⟨1428020, by rfl⟩ : syracuseStep 1904027 = 2856041) B2856041
theorem B2854367 : Blo 1268452 2854367 := bstep (se 1 (by rfl) ⟨2140775, by rfl⟩ : syracuseStep 2854367 = 4281551) B4281551
theorem B1904105 : Blo 1268452 1904105 := bstep (se 2 (by rfl) ⟨714039, by rfl⟩ : syracuseStep 1904105 = 1428079) B1428079
theorem B41176835 : Blo 1268452 41176835 := bstep (se 1 (by rfl) ⟨30882626, by rfl⟩ : syracuseStep 41176835 = 61765253) B61765253
theorem B10301215 : Blo 1268452 10301215 := bstep (se 1 (by rfl) ⟨7725911, by rfl⟩ : syracuseStep 10301215 = 15451823) B15451823
theorem B1904543 : Blo 1268452 1904543 := bstep (se 1 (by rfl) ⟨1428407, by rfl⟩ : syracuseStep 1904543 = 2856815) B2856815
theorem B3215315 : Blo 1268452 3215315 := bstep (se 1 (by rfl) ⟨2411486, by rfl⟩ : syracuseStep 3215315 = 4822973) B4822973
theorem B2855807 : Blo 1268452 2855807 := bstep (se 1 (by rfl) ⟨2141855, by rfl⟩ : syracuseStep 2855807 = 4283711) B4283711
theorem B13562861 : Blo 1268452 13562861 := bstep (se 3 (by rfl) ⟨2543036, by rfl⟩ : syracuseStep 13562861 = 5086073) B5086073
theorem B4281875 : Blo 1268452 4281875 := bstep (se 1 (by rfl) ⟨3211406, by rfl⟩ : syracuseStep 4281875 = 6422813) B6422813
theorem B2856671 : Blo 1268452 2856671 := bstep (se 1 (by rfl) ⟨2142503, by rfl⟩ : syracuseStep 2856671 = 4285007) B4285007
theorem B21985501 : Blo 1268452 21985501 := bstep (se 3 (by rfl) ⟨4122281, by rfl⟩ : syracuseStep 21985501 = 8244563) B8244563
theorem B9632519 : Blo 1268452 9632519 := bstep (se 1 (by rfl) ⟨7224389, by rfl⟩ : syracuseStep 9632519 = 14448779) B14448779
theorem B8133385 : Blo 1268452 8133385 := bstep (se 2 (by rfl) ⟨3050019, by rfl⟩ : syracuseStep 8133385 = 6100039) B6100039
theorem B32971589 : Blo 1268452 32971589 := bstep (se 4 (by rfl) ⟨3091086, by rfl⟩ : syracuseStep 32971589 = 6182173) B6182173
theorem B19545083 : Blo 1268452 19545083 := bstep (se 1 (by rfl) ⟨14658812, by rfl⟩ : syracuseStep 19545083 = 29317625) B29317625
theorem B55631137 : Blo 1268452 55631137 := bstep (se 2 (by rfl) ⟨20861676, by rfl⟩ : syracuseStep 55631137 = 41723353) B41723353
theorem B1269039 : Blo 1268452 1269039 := bstep (se 1 (by rfl) ⟨951779, by rfl⟩ : syracuseStep 1269039 = 1903559) B1903559
theorem B4816199 : Blo 1268452 4816199 := bstep (se 1 (by rfl) ⟨3612149, by rfl⟩ : syracuseStep 4816199 = 7224299) B7224299
theorem B1269095 : Blo 1268452 1269095 := bstep (se 1 (by rfl) ⟨951821, by rfl⟩ : syracuseStep 1269095 = 1903643) B1903643
theorem B1269279 : Blo 1268452 1269279 := bstep (se 1 (by rfl) ⟨951959, by rfl⟩ : syracuseStep 1269279 = 1903919) B1903919
theorem B1269503 : Blo 1268452 1269503 := bstep (se 1 (by rfl) ⟨952127, by rfl⟩ : syracuseStep 1269503 = 1904255) B1904255
theorem B6102809 : Blo 1268452 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B1269663 : Blo 1268452 1269663 := bstep (se 1 (by rfl) ⟨952247, by rfl⟩ : syracuseStep 1269663 = 1904495) B1904495
theorem B1269759 : Blo 1268452 1269759 := bstep (se 1 (by rfl) ⟨952319, by rfl⟩ : syracuseStep 1269759 = 1904639) B1904639
theorem B30892265 : Blo 1268452 30892265 := bstep (se 2 (by rfl) ⟨11584599, by rfl⟩ : syracuseStep 30892265 = 23169199) B23169199
theorem B9634463 : Blo 1268452 9634463 := bstep (se 1 (by rfl) ⟨7225847, by rfl⟩ : syracuseStep 9634463 = 14451695) B14451695
theorem B3212855 : Blo 1268452 3212855 := bstep (se 1 (by rfl) ⟨2409641, by rfl⟩ : syracuseStep 3212855 = 4819283) B4819283
theorem B1427323 : Blo 1268452 1427323 := bstep (se 1 (by rfl) ⟨1070492, by rfl⟩ : syracuseStep 1427323 = 2140985) B2140985
theorem B21981059 : Blo 1268452 21981059 := bstep (se 1 (by rfl) ⟨16485794, by rfl⟩ : syracuseStep 21981059 = 32971589) B32971589
theorem B1902683 : Blo 1268452 1902683 := bstep (se 1 (by rfl) ⟨1427012, by rfl⟩ : syracuseStep 1902683 = 2854025) B2854025
theorem B1902911 : Blo 1268452 1902911 := bstep (se 1 (by rfl) ⟨1427183, by rfl⟩ : syracuseStep 1902911 = 2854367) B2854367
theorem B4287167 : Blo 1268452 4287167 := bstep (se 1 (by rfl) ⟨3215375, by rfl⟩ : syracuseStep 4287167 = 6430751) B6430751
theorem B29314001 : Blo 1268452 29314001 := bstep (se 2 (by rfl) ⟨10992750, by rfl⟩ : syracuseStep 29314001 = 21985501) B21985501
theorem B1903871 : Blo 1268452 1903871 := bstep (se 1 (by rfl) ⟨1427903, by rfl⟩ : syracuseStep 1903871 = 2855807) B2855807
theorem B2854583 : Blo 1268452 2854583 := bstep (se 1 (by rfl) ⟨2140937, by rfl⟩ : syracuseStep 2854583 = 4281875) B4281875
theorem B1904447 : Blo 1268452 1904447 := bstep (se 1 (by rfl) ⟨1428335, by rfl⟩ : syracuseStep 1904447 = 2856671) B2856671
theorem B74174849 : Blo 1268452 74174849 := bstep (se 2 (by rfl) ⟨27815568, by rfl⟩ : syracuseStep 74174849 = 55631137) B55631137
theorem B13030055 : Blo 1268452 13030055 := bstep (se 1 (by rfl) ⟨9772541, by rfl⟩ : syracuseStep 13030055 = 19545083) B19545083
theorem B13734953 : Blo 1268452 13734953 := bstep (se 2 (by rfl) ⟨5150607, by rfl⟩ : syracuseStep 13734953 = 10301215) B10301215
theorem B4068539 : Blo 1268452 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B2143543 : Blo 1268452 2143543 := bstep (se 1 (by rfl) ⟨1607657, by rfl⟩ : syracuseStep 2143543 = 3215315) B3215315
theorem B10844513 : Blo 1268452 10844513 := bstep (se 2 (by rfl) ⟨4066692, by rfl⟩ : syracuseStep 10844513 = 8133385) B8133385
theorem B10852987 : Blo 1268452 10852987 := bstep (se 1 (by rfl) ⟨8139740, by rfl⟩ : syracuseStep 10852987 = 16279481) B16279481
theorem B1268511 : Blo 1268452 1268511 := bstep (se 1 (by rfl) ⟨951383, by rfl⟩ : syracuseStep 1268511 = 1902767) B1902767
theorem B1268763 : Blo 1268452 1268763 := bstep (se 1 (by rfl) ⟨951572, by rfl⟩ : syracuseStep 1268763 = 1903145) B1903145
theorem B1268839 : Blo 1268452 1268839 := bstep (se 1 (by rfl) ⟨951629, by rfl⟩ : syracuseStep 1268839 = 1903259) B1903259
theorem B6421679 : Blo 1268452 6421679 := bstep (se 1 (by rfl) ⟨4816259, by rfl⟩ : syracuseStep 6421679 = 9632519) B9632519
theorem B1269151 : Blo 1268452 1269151 := bstep (se 1 (by rfl) ⟨951863, by rfl⟩ : syracuseStep 1269151 = 1903727) B1903727
theorem B3210799 : Blo 1268452 3210799 := bstep (se 1 (by rfl) ⟨2408099, by rfl⟩ : syracuseStep 3210799 = 4816199) B4816199
theorem B1269351 : Blo 1268452 1269351 := bstep (se 1 (by rfl) ⟨952013, by rfl⟩ : syracuseStep 1269351 = 1904027) B1904027
theorem B1269403 : Blo 1268452 1269403 := bstep (se 1 (by rfl) ⟨952052, by rfl⟩ : syracuseStep 1269403 = 1904105) B1904105
theorem B27451223 : Blo 1268452 27451223 := bstep (se 1 (by rfl) ⟨20588417, by rfl⟩ : syracuseStep 27451223 = 41176835) B41176835
theorem B1269695 : Blo 1268452 1269695 := bstep (se 1 (by rfl) ⟨952271, by rfl⟩ : syracuseStep 1269695 = 1904543) B1904543
theorem B36167629 : Blo 1268452 36167629 := bstep (se 3 (by rfl) ⟨6781430, by rfl⟩ : syracuseStep 36167629 = 13562861) B13562861
theorem B20594843 : Blo 1268452 20594843 := bstep (se 1 (by rfl) ⟨15446132, by rfl⟩ : syracuseStep 20594843 = 30892265) B30892265
theorem B6422975 : Blo 1268452 6422975 := bstep (se 1 (by rfl) ⟨4817231, by rfl⟩ : syracuseStep 6422975 = 9634463) B9634463
theorem B2712359 : Blo 1268452 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B1903055 : Blo 1268452 1903055 := bstep (se 1 (by rfl) ⟨1427291, by rfl⟩ : syracuseStep 1903055 = 2854583) B2854583
theorem B1903097 : Blo 1268452 1903097 := bstep (se 2 (by rfl) ⟨713661, by rfl⟩ : syracuseStep 1903097 = 1427323) B1427323
theorem B49449899 : Blo 1268452 49449899 := bstep (se 1 (by rfl) ⟨37087424, by rfl⟩ : syracuseStep 49449899 = 74174849) B74174849
theorem B8686703 : Blo 1268452 8686703 := bstep (se 1 (by rfl) ⟨6515027, by rfl⟩ : syracuseStep 8686703 = 13030055) B13030055
theorem B14470649 : Blo 1268452 14470649 := bstep (se 2 (by rfl) ⟨5426493, by rfl⟩ : syracuseStep 14470649 = 10852987) B10852987
theorem B2141903 : Blo 1268452 2141903 := bstep (se 1 (by rfl) ⟨1606427, by rfl⟩ : syracuseStep 2141903 = 3212855) B3212855
theorem B7229675 : Blo 1268452 7229675 := bstep (se 1 (by rfl) ⟨5422256, by rfl⟩ : syracuseStep 7229675 = 10844513) B10844513
theorem B19542667 : Blo 1268452 19542667 := bstep (se 1 (by rfl) ⟨14657000, by rfl⟩ : syracuseStep 19542667 = 29314001) B29314001
theorem B4281065 : Blo 1268452 4281065 := bstep (se 2 (by rfl) ⟨1605399, by rfl⟩ : syracuseStep 4281065 = 3210799) B3210799
theorem B4281119 : Blo 1268452 4281119 := bstep (se 1 (by rfl) ⟨3210839, by rfl⟩ : syracuseStep 4281119 = 6421679) B6421679
theorem B48223505 : Blo 1268452 48223505 := bstep (se 2 (by rfl) ⟨18083814, by rfl⟩ : syracuseStep 48223505 = 36167629) B36167629
theorem B9156635 : Blo 1268452 9156635 := bstep (se 1 (by rfl) ⟨6867476, by rfl⟩ : syracuseStep 9156635 = 13734953) B13734953
theorem B14654039 : Blo 1268452 14654039 := bstep (se 1 (by rfl) ⟨10990529, by rfl⟩ : syracuseStep 14654039 = 21981059) B21981059
theorem B1268455 : Blo 1268452 1268455 := bstep (se 1 (by rfl) ⟨951341, by rfl⟩ : syracuseStep 1268455 = 1902683) B1902683
theorem B1268607 : Blo 1268452 1268607 := bstep (se 1 (by rfl) ⟨951455, by rfl⟩ : syracuseStep 1268607 = 1902911) B1902911
theorem B2858057 : Blo 1268452 2858057 := bstep (se 2 (by rfl) ⟨1071771, by rfl⟩ : syracuseStep 2858057 = 2143543) B2143543
theorem B2858111 : Blo 1268452 2858111 := bstep (se 1 (by rfl) ⟨2143583, by rfl⟩ : syracuseStep 2858111 = 4287167) B4287167
theorem B1269247 : Blo 1268452 1269247 := bstep (se 1 (by rfl) ⟨951935, by rfl⟩ : syracuseStep 1269247 = 1903871) B1903871
theorem B1269631 : Blo 1268452 1269631 := bstep (se 1 (by rfl) ⟨952223, by rfl⟩ : syracuseStep 1269631 = 1904447) B1904447
theorem B18300815 : Blo 1268452 18300815 := bstep (se 1 (by rfl) ⟨13725611, by rfl⟩ : syracuseStep 18300815 = 27451223) B27451223
theorem B13729895 : Blo 1268452 13729895 := bstep (se 1 (by rfl) ⟨10297421, by rfl⟩ : syracuseStep 13729895 = 20594843) B20594843
theorem B6104423 : Blo 1268452 6104423 := bstep (se 1 (by rfl) ⟨4578317, by rfl⟩ : syracuseStep 6104423 = 9156635) B9156635
theorem B39077437 : Blo 1268452 39077437 := bstep (se 3 (by rfl) ⟨7327019, by rfl⟩ : syracuseStep 39077437 = 14654039) B14654039
theorem B32966599 : Blo 1268452 32966599 := bstep (se 1 (by rfl) ⟨24724949, by rfl⟩ : syracuseStep 32966599 = 49449899) B49449899
theorem B1427935 : Blo 1268452 1427935 := bstep (se 1 (by rfl) ⟨1070951, by rfl⟩ : syracuseStep 1427935 = 2141903) B2141903
theorem B12200543 : Blo 1268452 12200543 := bstep (se 1 (by rfl) ⟨9150407, by rfl⟩ : syracuseStep 12200543 = 18300815) B18300815
theorem B4819783 : Blo 1268452 4819783 := bstep (se 1 (by rfl) ⟨3614837, by rfl⟩ : syracuseStep 4819783 = 7229675) B7229675
theorem B2854043 : Blo 1268452 2854043 := bstep (se 1 (by rfl) ⟨2140532, by rfl⟩ : syracuseStep 2854043 = 4281065) B4281065
theorem B2854079 : Blo 1268452 2854079 := bstep (se 1 (by rfl) ⟨2140559, by rfl⟩ : syracuseStep 2854079 = 4281119) B4281119
theorem B32149003 : Blo 1268452 32149003 := bstep (se 1 (by rfl) ⟨24111752, by rfl⟩ : syracuseStep 32149003 = 48223505) B48223505
theorem B1905371 : Blo 1268452 1905371 := bstep (se 1 (by rfl) ⟨1429028, by rfl⟩ : syracuseStep 1905371 = 2858057) B2858057
theorem B1905407 : Blo 1268452 1905407 := bstep (se 1 (by rfl) ⟨1429055, by rfl⟩ : syracuseStep 1905407 = 2858111) B2858111
theorem B9647099 : Blo 1268452 9647099 := bstep (se 1 (by rfl) ⟨7235324, by rfl⟩ : syracuseStep 9647099 = 14470649) B14470649
theorem B4281983 : Blo 1268452 4281983 := bstep (se 1 (by rfl) ⟨3211487, by rfl⟩ : syracuseStep 4281983 = 6422975) B6422975
theorem B1808239 : Blo 1268452 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B26056889 : Blo 1268452 26056889 := bstep (se 2 (by rfl) ⟨9771333, by rfl⟩ : syracuseStep 26056889 = 19542667) B19542667
theorem B1268703 : Blo 1268452 1268703 := bstep (se 1 (by rfl) ⟨951527, by rfl⟩ : syracuseStep 1268703 = 1903055) B1903055
theorem B1268731 : Blo 1268452 1268731 := bstep (se 1 (by rfl) ⟨951548, by rfl⟩ : syracuseStep 1268731 = 1903097) B1903097
theorem B5791135 : Blo 1268452 5791135 := bstep (se 1 (by rfl) ⟨4343351, by rfl⟩ : syracuseStep 5791135 = 8686703) B8686703
theorem B1270247 : Blo 1268452 1270247 := bstep (se 1 (by rfl) ⟨952685, by rfl⟩ : syracuseStep 1270247 = 1905371) B1905371
theorem B1270271 : Blo 1268452 1270271 := bstep (se 1 (by rfl) ⟨952703, by rfl⟩ : syracuseStep 1270271 = 1905407) B1905407
theorem B6431399 : Blo 1268452 6431399 := bstep (se 1 (by rfl) ⟨4823549, by rfl⟩ : syracuseStep 6431399 = 9647099) B9647099
theorem B52103249 : Blo 1268452 52103249 := bstep (se 2 (by rfl) ⟨19538718, by rfl⟩ : syracuseStep 52103249 = 39077437) B39077437
theorem B1902695 : Blo 1268452 1902695 := bstep (se 1 (by rfl) ⟨1427021, by rfl⟩ : syracuseStep 1902695 = 2854043) B2854043
theorem B1902719 : Blo 1268452 1902719 := bstep (se 1 (by rfl) ⟨1427039, by rfl⟩ : syracuseStep 1902719 = 2854079) B2854079
theorem B2410985 : Blo 1268452 2410985 := bstep (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) B1808239
theorem B9153263 : Blo 1268452 9153263 := bstep (se 1 (by rfl) ⟨6864947, by rfl⟩ : syracuseStep 9153263 = 13729895) B13729895
theorem B1903913 : Blo 1268452 1903913 := bstep (se 2 (by rfl) ⟨713967, by rfl⟩ : syracuseStep 1903913 = 1427935) B1427935
theorem B2854655 : Blo 1268452 2854655 := bstep (se 1 (by rfl) ⟨2140991, by rfl⟩ : syracuseStep 2854655 = 4281983) B4281983
theorem B6426377 : Blo 1268452 6426377 := bstep (se 2 (by rfl) ⟨2409891, by rfl⟩ : syracuseStep 6426377 = 4819783) B4819783
theorem B17371259 : Blo 1268452 17371259 := bstep (se 1 (by rfl) ⟨13028444, by rfl⟩ : syracuseStep 17371259 = 26056889) B26056889
theorem B7721513 : Blo 1268452 7721513 := bstep (se 2 (by rfl) ⟨2895567, by rfl⟩ : syracuseStep 7721513 = 5791135) B5791135
theorem B42865337 : Blo 1268452 42865337 := bstep (se 2 (by rfl) ⟨16074501, by rfl⟩ : syracuseStep 42865337 = 32149003) B32149003
theorem B43955465 : Blo 1268452 43955465 := bstep (se 2 (by rfl) ⟨16483299, by rfl⟩ : syracuseStep 43955465 = 32966599) B32966599
theorem B4069615 : Blo 1268452 4069615 := bstep (se 1 (by rfl) ⟨3052211, by rfl⟩ : syracuseStep 4069615 = 6104423) B6104423
theorem B8133695 : Blo 1268452 8133695 := bstep (se 1 (by rfl) ⟨6100271, by rfl⟩ : syracuseStep 8133695 = 12200543) B12200543
theorem B34735499 : Blo 1268452 34735499 := bstep (se 1 (by rfl) ⟨26051624, by rfl⟩ : syracuseStep 34735499 = 52103249) B52103249
theorem B1903103 : Blo 1268452 1903103 := bstep (se 1 (by rfl) ⟨1427327, by rfl⟩ : syracuseStep 1903103 = 2854655) B2854655
theorem B5426153 : Blo 1268452 5426153 := bstep (se 2 (by rfl) ⟨2034807, by rfl⟩ : syracuseStep 5426153 = 4069615) B4069615
theorem B5147675 : Blo 1268452 5147675 := bstep (se 1 (by rfl) ⟨3860756, by rfl⟩ : syracuseStep 5147675 = 7721513) B7721513
theorem B4287599 : Blo 1268452 4287599 := bstep (se 1 (by rfl) ⟨3215699, by rfl⟩ : syracuseStep 4287599 = 6431399) B6431399
theorem B28576891 : Blo 1268452 28576891 := bstep (se 1 (by rfl) ⟨21432668, by rfl⟩ : syracuseStep 28576891 = 42865337) B42865337
theorem B117214573 : Blo 1268452 117214573 := bstep (se 3 (by rfl) ⟨21977732, by rfl⟩ : syracuseStep 117214573 = 43955465) B43955465
theorem B11580839 : Blo 1268452 11580839 := bstep (se 1 (by rfl) ⟨8685629, by rfl⟩ : syracuseStep 11580839 = 17371259) B17371259
theorem B6429293 : Blo 1268452 6429293 := bstep (se 3 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 6429293 = 2410985) B2410985
theorem B1268463 : Blo 1268452 1268463 := bstep (se 1 (by rfl) ⟨951347, by rfl⟩ : syracuseStep 1268463 = 1902695) B1902695
theorem B1268479 : Blo 1268452 1268479 := bstep (se 1 (by rfl) ⟨951359, by rfl⟩ : syracuseStep 1268479 = 1902719) B1902719
theorem B6102175 : Blo 1268452 6102175 := bstep (se 1 (by rfl) ⟨4576631, by rfl⟩ : syracuseStep 6102175 = 9153263) B9153263
theorem B5422463 : Blo 1268452 5422463 := bstep (se 1 (by rfl) ⟨4066847, by rfl⟩ : syracuseStep 5422463 = 8133695) B8133695
theorem B1269275 : Blo 1268452 1269275 := bstep (se 1 (by rfl) ⟨951956, by rfl⟩ : syracuseStep 1269275 = 1903913) B1903913
theorem B4284251 : Blo 1268452 4284251 := bstep (se 1 (by rfl) ⟨3213188, by rfl⟩ : syracuseStep 4284251 = 6426377) B6426377
theorem B8136233 : Blo 1268452 8136233 := bstep (se 2 (by rfl) ⟨3051087, by rfl⟩ : syracuseStep 8136233 = 6102175) B6102175
theorem B4286195 : Blo 1268452 4286195 := bstep (se 1 (by rfl) ⟨3214646, by rfl⟩ : syracuseStep 4286195 = 6429293) B6429293
theorem B3614975 : Blo 1268452 3614975 := bstep (se 1 (by rfl) ⟨2711231, by rfl⟩ : syracuseStep 3614975 = 5422463) B5422463
theorem B7720559 : Blo 1268452 7720559 := bstep (se 1 (by rfl) ⟨5790419, by rfl⟩ : syracuseStep 7720559 = 11580839) B11580839
theorem B3617435 : Blo 1268452 3617435 := bstep (se 1 (by rfl) ⟨2713076, by rfl⟩ : syracuseStep 3617435 = 5426153) B5426153
theorem B2856167 : Blo 1268452 2856167 := bstep (se 1 (by rfl) ⟨2142125, by rfl⟩ : syracuseStep 2856167 = 4284251) B4284251
theorem B152410085 : Blo 1268452 152410085 := bstep (se 4 (by rfl) ⟨14288445, by rfl⟩ : syracuseStep 152410085 = 28576891) B28576891
theorem B23156999 : Blo 1268452 23156999 := bstep (se 1 (by rfl) ⟨17367749, by rfl⟩ : syracuseStep 23156999 = 34735499) B34735499
theorem B1268735 : Blo 1268452 1268735 := bstep (se 1 (by rfl) ⟨951551, by rfl⟩ : syracuseStep 1268735 = 1903103) B1903103
theorem B156286097 : Blo 1268452 156286097 := bstep (se 2 (by rfl) ⟨58607286, by rfl⟩ : syracuseStep 156286097 = 117214573) B117214573
theorem B3431783 : Blo 1268452 3431783 := bstep (se 1 (by rfl) ⟨2573837, by rfl⟩ : syracuseStep 3431783 = 5147675) B5147675
theorem B2858399 : Blo 1268452 2858399 := bstep (se 1 (by rfl) ⟨2143799, by rfl⟩ : syracuseStep 2858399 = 4287599) B4287599
theorem B5424155 : Blo 1268452 5424155 := bstep (se 1 (by rfl) ⟨4068116, by rfl⟩ : syracuseStep 5424155 = 8136233) B8136233
theorem B101606723 : Blo 1268452 101606723 := bstep (se 1 (by rfl) ⟨76205042, by rfl⟩ : syracuseStep 101606723 = 152410085) B152410085
theorem B2409983 : Blo 1268452 2409983 := bstep (se 1 (by rfl) ⟨1807487, by rfl⟩ : syracuseStep 2409983 = 3614975) B3614975
theorem B2287855 : Blo 1268452 2287855 := bstep (se 1 (by rfl) ⟨1715891, by rfl⟩ : syracuseStep 2287855 = 3431783) B3431783
theorem B5147039 : Blo 1268452 5147039 := bstep (se 1 (by rfl) ⟨3860279, by rfl⟩ : syracuseStep 5147039 = 7720559) B7720559
theorem B2411623 : Blo 1268452 2411623 := bstep (se 1 (by rfl) ⟨1808717, by rfl⟩ : syracuseStep 2411623 = 3617435) B3617435
theorem B1904111 : Blo 1268452 1904111 := bstep (se 1 (by rfl) ⟨1428083, by rfl⟩ : syracuseStep 1904111 = 2856167) B2856167
theorem B15437999 : Blo 1268452 15437999 := bstep (se 1 (by rfl) ⟨11578499, by rfl⟩ : syracuseStep 15437999 = 23156999) B23156999
theorem B104190731 : Blo 1268452 104190731 := bstep (se 1 (by rfl) ⟨78143048, by rfl⟩ : syracuseStep 104190731 = 156286097) B156286097
theorem B1905599 : Blo 1268452 1905599 := bstep (se 1 (by rfl) ⟨1429199, by rfl⟩ : syracuseStep 1905599 = 2858399) B2858399
theorem B2857463 : Blo 1268452 2857463 := bstep (se 1 (by rfl) ⟨2143097, by rfl⟩ : syracuseStep 2857463 = 4286195) B4286195
theorem B69460487 : Blo 1268452 69460487 := bstep (se 1 (by rfl) ⟨52095365, by rfl⟩ : syracuseStep 69460487 = 104190731) B104190731
theorem B1270399 : Blo 1268452 1270399 := bstep (se 1 (by rfl) ⟨952799, by rfl⟩ : syracuseStep 1270399 = 1905599) B1905599
theorem B1606655 : Blo 1268452 1606655 := bstep (se 1 (by rfl) ⟨1204991, by rfl⟩ : syracuseStep 1606655 = 2409983) B2409983
theorem B3050473 : Blo 1268452 3050473 := bstep (se 2 (by rfl) ⟨1143927, by rfl⟩ : syracuseStep 3050473 = 2287855) B2287855
theorem B41167997 : Blo 1268452 41167997 := bstep (se 3 (by rfl) ⟨7718999, by rfl⟩ : syracuseStep 41167997 = 15437999) B15437999
theorem B3616103 : Blo 1268452 3616103 := bstep (se 1 (by rfl) ⟨2712077, by rfl⟩ : syracuseStep 3616103 = 5424155) B5424155
theorem B3215497 : Blo 1268452 3215497 := bstep (se 2 (by rfl) ⟨1205811, by rfl⟩ : syracuseStep 3215497 = 2411623) B2411623
theorem B1904975 : Blo 1268452 1904975 := bstep (se 1 (by rfl) ⟨1428731, by rfl⟩ : syracuseStep 1904975 = 2857463) B2857463
theorem B67737815 : Blo 1268452 67737815 := bstep (se 1 (by rfl) ⟨50803361, by rfl⟩ : syracuseStep 67737815 = 101606723) B101606723
theorem B3431359 : Blo 1268452 3431359 := bstep (se 1 (by rfl) ⟨2573519, by rfl⟩ : syracuseStep 3431359 = 5147039) B5147039
theorem B1269407 : Blo 1268452 1269407 := bstep (se 1 (by rfl) ⟨952055, by rfl⟩ : syracuseStep 1269407 = 1904111) B1904111
theorem B1269983 : Blo 1268452 1269983 := bstep (se 1 (by rfl) ⟨952487, by rfl⟩ : syracuseStep 1269983 = 1904975) B1904975
theorem B27445331 : Blo 1268452 27445331 := bstep (se 1 (by rfl) ⟨20583998, by rfl⟩ : syracuseStep 27445331 = 41167997) B41167997
theorem B2410735 : Blo 1268452 2410735 := bstep (se 1 (by rfl) ⟨1808051, by rfl⟩ : syracuseStep 2410735 = 3616103) B3616103
theorem B4287329 : Blo 1268452 4287329 := bstep (se 2 (by rfl) ⟨1607748, by rfl⟩ : syracuseStep 4287329 = 3215497) B3215497
theorem B4575145 : Blo 1268452 4575145 := bstep (se 2 (by rfl) ⟨1715679, by rfl⟩ : syracuseStep 4575145 = 3431359) B3431359
theorem B4067297 : Blo 1268452 4067297 := bstep (se 2 (by rfl) ⟨1525236, by rfl⟩ : syracuseStep 4067297 = 3050473) B3050473
theorem B45158543 : Blo 1268452 45158543 := bstep (se 1 (by rfl) ⟨33868907, by rfl⟩ : syracuseStep 45158543 = 67737815) B67737815
theorem B46306991 : Blo 1268452 46306991 := bstep (se 1 (by rfl) ⟨34730243, by rfl⟩ : syracuseStep 46306991 = 69460487) B69460487
theorem B4284413 : Blo 1268452 4284413 := bstep (se 3 (by rfl) ⟨803327, by rfl⟩ : syracuseStep 4284413 = 1606655) B1606655
theorem B30105695 : Blo 1268452 30105695 := bstep (se 1 (by rfl) ⟨22579271, by rfl⟩ : syracuseStep 30105695 = 45158543) B45158543
theorem B3214313 : Blo 1268452 3214313 := bstep (se 2 (by rfl) ⟨1205367, by rfl⟩ : syracuseStep 3214313 = 2410735) B2410735
theorem B30871327 : Blo 1268452 30871327 := bstep (se 1 (by rfl) ⟨23153495, by rfl⟩ : syracuseStep 30871327 = 46306991) B46306991
theorem B18296887 : Blo 1268452 18296887 := bstep (se 1 (by rfl) ⟨13722665, by rfl⟩ : syracuseStep 18296887 = 27445331) B27445331
theorem B6100193 : Blo 1268452 6100193 := bstep (se 2 (by rfl) ⟨2287572, by rfl⟩ : syracuseStep 6100193 = 4575145) B4575145
theorem B2856275 : Blo 1268452 2856275 := bstep (se 1 (by rfl) ⟨2142206, by rfl⟩ : syracuseStep 2856275 = 4284413) B4284413
theorem B2858219 : Blo 1268452 2858219 := bstep (se 1 (by rfl) ⟨2143664, by rfl⟩ : syracuseStep 2858219 = 4287329) B4287329
theorem B2711531 : Blo 1268452 2711531 := bstep (se 1 (by rfl) ⟨2033648, by rfl⟩ : syracuseStep 2711531 = 4067297) B4067297
theorem B24395849 : Blo 1268452 24395849 := bstep (se 2 (by rfl) ⟨9148443, by rfl⟩ : syracuseStep 24395849 = 18296887) B18296887
theorem B80281853 : Blo 1268452 80281853 := bstep (se 3 (by rfl) ⟨15052847, by rfl⟩ : syracuseStep 80281853 = 30105695) B30105695
theorem B4066795 : Blo 1268452 4066795 := bstep (se 1 (by rfl) ⟨3050096, by rfl⟩ : syracuseStep 4066795 = 6100193) B6100193
theorem B1904183 : Blo 1268452 1904183 := bstep (se 1 (by rfl) ⟨1428137, by rfl⟩ : syracuseStep 1904183 = 2856275) B2856275
theorem B2142875 : Blo 1268452 2142875 := bstep (se 1 (by rfl) ⟨1607156, by rfl⟩ : syracuseStep 2142875 = 3214313) B3214313
theorem B1905479 : Blo 1268452 1905479 := bstep (se 1 (by rfl) ⟨1429109, by rfl⟩ : syracuseStep 1905479 = 2858219) B2858219
theorem B41161769 : Blo 1268452 41161769 := bstep (se 2 (by rfl) ⟨15435663, by rfl⟩ : syracuseStep 41161769 = 30871327) B30871327
theorem B1807687 : Blo 1268452 1807687 := bstep (se 1 (by rfl) ⟨1355765, by rfl⟩ : syracuseStep 1807687 = 2711531) B2711531
theorem B1270319 : Blo 1268452 1270319 := bstep (se 1 (by rfl) ⟨952739, by rfl⟩ : syracuseStep 1270319 = 1905479) B1905479
theorem B2410249 : Blo 1268452 2410249 := bstep (se 2 (by rfl) ⟨903843, by rfl⟩ : syracuseStep 2410249 = 1807687) B1807687
theorem B16263899 : Blo 1268452 16263899 := bstep (se 1 (by rfl) ⟨12197924, by rfl⟩ : syracuseStep 16263899 = 24395849) B24395849
theorem B53521235 : Blo 1268452 53521235 := bstep (se 1 (by rfl) ⟨40140926, by rfl⟩ : syracuseStep 53521235 = 80281853) B80281853
theorem B1428583 : Blo 1268452 1428583 := bstep (se 1 (by rfl) ⟨1071437, by rfl⟩ : syracuseStep 1428583 = 2142875) B2142875
theorem B27441179 : Blo 1268452 27441179 := bstep (se 1 (by rfl) ⟨20580884, by rfl⟩ : syracuseStep 27441179 = 41161769) B41161769
theorem B5422393 : Blo 1268452 5422393 := bstep (se 2 (by rfl) ⟨2033397, by rfl⟩ : syracuseStep 5422393 = 4066795) B4066795
theorem B1269455 : Blo 1268452 1269455 := bstep (se 1 (by rfl) ⟨952091, by rfl⟩ : syracuseStep 1269455 = 1904183) B1904183
theorem B18294119 : Blo 1268452 18294119 := bstep (se 1 (by rfl) ⟨13720589, by rfl⟩ : syracuseStep 18294119 = 27441179) B27441179
theorem B3213665 : Blo 1268452 3213665 := bstep (se 2 (by rfl) ⟨1205124, by rfl⟩ : syracuseStep 3213665 = 2410249) B2410249
theorem B1904777 : Blo 1268452 1904777 := bstep (se 2 (by rfl) ⟨714291, by rfl⟩ : syracuseStep 1904777 = 1428583) B1428583
theorem B7229857 : Blo 1268452 7229857 := bstep (se 2 (by rfl) ⟨2711196, by rfl⟩ : syracuseStep 7229857 = 5422393) B5422393
theorem B10842599 : Blo 1268452 10842599 := bstep (se 1 (by rfl) ⟨8131949, by rfl⟩ : syracuseStep 10842599 = 16263899) B16263899
theorem B35680823 : Blo 1268452 35680823 := bstep (se 1 (by rfl) ⟨26760617, by rfl⟩ : syracuseStep 35680823 = 53521235) B53521235
theorem B1269851 : Blo 1268452 1269851 := bstep (se 1 (by rfl) ⟨952388, by rfl⟩ : syracuseStep 1269851 = 1904777) B1904777
theorem B7228399 : Blo 1268452 7228399 := bstep (se 1 (by rfl) ⟨5421299, by rfl⟩ : syracuseStep 7228399 = 10842599) B10842599
theorem B2142443 : Blo 1268452 2142443 := bstep (se 1 (by rfl) ⟨1606832, by rfl⟩ : syracuseStep 2142443 = 3213665) B3213665
theorem B23787215 : Blo 1268452 23787215 := bstep (se 1 (by rfl) ⟨17840411, by rfl⟩ : syracuseStep 23787215 = 35680823) B35680823
theorem B9639809 : Blo 1268452 9639809 := bstep (se 2 (by rfl) ⟨3614928, by rfl⟩ : syracuseStep 9639809 = 7229857) B7229857
theorem B12196079 : Blo 1268452 12196079 := bstep (se 1 (by rfl) ⟨9147059, by rfl⟩ : syracuseStep 12196079 = 18294119) B18294119
theorem B1428295 : Blo 1268452 1428295 := bstep (se 1 (by rfl) ⟨1071221, by rfl⟩ : syracuseStep 1428295 = 2142443) B2142443
theorem B6426539 : Blo 1268452 6426539 := bstep (se 1 (by rfl) ⟨4819904, by rfl⟩ : syracuseStep 6426539 = 9639809) B9639809
theorem B9637865 : Blo 1268452 9637865 := bstep (se 2 (by rfl) ⟨3614199, by rfl⟩ : syracuseStep 9637865 = 7228399) B7228399
theorem B8130719 : Blo 1268452 8130719 := bstep (se 1 (by rfl) ⟨6098039, by rfl⟩ : syracuseStep 8130719 = 12196079) B12196079
theorem B15858143 : Blo 1268452 15858143 := bstep (se 1 (by rfl) ⟨11893607, by rfl⟩ : syracuseStep 15858143 = 23787215) B23787215
theorem B6425243 : Blo 1268452 6425243 := bstep (se 1 (by rfl) ⟨4818932, by rfl⟩ : syracuseStep 6425243 = 9637865) B9637865
theorem B1904393 : Blo 1268452 1904393 := bstep (se 2 (by rfl) ⟨714147, by rfl⟩ : syracuseStep 1904393 = 1428295) B1428295
theorem B10572095 : Blo 1268452 10572095 := bstep (se 1 (by rfl) ⟨7929071, by rfl⟩ : syracuseStep 10572095 = 15858143) B15858143
theorem B21681917 : Blo 1268452 21681917 := bstep (se 3 (by rfl) ⟨4065359, by rfl⟩ : syracuseStep 21681917 = 8130719) B8130719
theorem B4284359 : Blo 1268452 4284359 := bstep (se 1 (by rfl) ⟨3213269, by rfl⟩ : syracuseStep 4284359 = 6426539) B6426539
theorem B7048063 : Blo 1268452 7048063 := bstep (se 1 (by rfl) ⟨5286047, by rfl⟩ : syracuseStep 7048063 = 10572095) B10572095
theorem B14454611 : Blo 1268452 14454611 := bstep (se 1 (by rfl) ⟨10840958, by rfl⟩ : syracuseStep 14454611 = 21681917) B21681917
theorem B2856239 : Blo 1268452 2856239 := bstep (se 1 (by rfl) ⟨2142179, by rfl⟩ : syracuseStep 2856239 = 4284359) B4284359
theorem B4283495 : Blo 1268452 4283495 := bstep (se 1 (by rfl) ⟨3212621, by rfl⟩ : syracuseStep 4283495 = 6425243) B6425243
theorem B1269595 : Blo 1268452 1269595 := bstep (se 1 (by rfl) ⟨952196, by rfl⟩ : syracuseStep 1269595 = 1904393) B1904393
theorem B9397417 : Blo 1268452 9397417 := bstep (se 2 (by rfl) ⟨3524031, by rfl⟩ : syracuseStep 9397417 = 7048063) B7048063
theorem B9636407 : Blo 1268452 9636407 := bstep (se 1 (by rfl) ⟨7227305, by rfl⟩ : syracuseStep 9636407 = 14454611) B14454611
theorem B1904159 : Blo 1268452 1904159 := bstep (se 1 (by rfl) ⟨1428119, by rfl⟩ : syracuseStep 1904159 = 2856239) B2856239
theorem B2855663 : Blo 1268452 2855663 := bstep (se 1 (by rfl) ⟨2141747, by rfl⟩ : syracuseStep 2855663 = 4283495) B4283495
theorem B6424271 : Blo 1268452 6424271 := bstep (se 1 (by rfl) ⟨4818203, by rfl⟩ : syracuseStep 6424271 = 9636407) B9636407
theorem B1903775 : Blo 1268452 1903775 := bstep (se 1 (by rfl) ⟨1427831, by rfl⟩ : syracuseStep 1903775 = 2855663) B2855663
theorem B12529889 : Blo 1268452 12529889 := bstep (se 2 (by rfl) ⟨4698708, by rfl⟩ : syracuseStep 12529889 = 9397417) B9397417
theorem B1269439 : Blo 1268452 1269439 := bstep (se 1 (by rfl) ⟨952079, by rfl⟩ : syracuseStep 1269439 = 1904159) B1904159
theorem B8353259 : Blo 1268452 8353259 := bstep (se 1 (by rfl) ⟨6264944, by rfl⟩ : syracuseStep 8353259 = 12529889) B12529889
theorem B4282847 : Blo 1268452 4282847 := bstep (se 1 (by rfl) ⟨3212135, by rfl⟩ : syracuseStep 4282847 = 6424271) B6424271
theorem B1269183 : Blo 1268452 1269183 := bstep (se 1 (by rfl) ⟨951887, by rfl⟩ : syracuseStep 1269183 = 1903775) B1903775
theorem B2855231 : Blo 1268452 2855231 := bstep (se 1 (by rfl) ⟨2141423, by rfl⟩ : syracuseStep 2855231 = 4282847) B4282847
theorem B5568839 : Blo 1268452 5568839 := bstep (se 1 (by rfl) ⟨4176629, by rfl⟩ : syracuseStep 5568839 = 8353259) B8353259
theorem B3712559 : Blo 1268452 3712559 := bstep (se 1 (by rfl) ⟨2784419, by rfl⟩ : syracuseStep 3712559 = 5568839) B5568839
theorem B1903487 : Blo 1268452 1903487 := bstep (se 1 (by rfl) ⟨1427615, by rfl⟩ : syracuseStep 1903487 = 2855231) B2855231
theorem B9900157 : Blo 1268452 9900157 := bstep (se 3 (by rfl) ⟨1856279, by rfl⟩ : syracuseStep 9900157 = 3712559) B3712559
theorem B1268991 : Blo 1268452 1268991 := bstep (se 1 (by rfl) ⟨951743, by rfl⟩ : syracuseStep 1268991 = 1903487) B1903487
theorem B13200209 : Blo 1268452 13200209 := bstep (se 2 (by rfl) ⟨4950078, by rfl⟩ : syracuseStep 13200209 = 9900157) B9900157
theorem B8800139 : Blo 1268452 8800139 := bstep (se 1 (by rfl) ⟨6600104, by rfl⟩ : syracuseStep 8800139 = 13200209) B13200209
theorem B5866759 : Blo 1268452 5866759 := bstep (se 1 (by rfl) ⟨4400069, by rfl⟩ : syracuseStep 5866759 = 8800139) B8800139
theorem B7822345 : Blo 1268452 7822345 := bstep (se 2 (by rfl) ⟨2933379, by rfl⟩ : syracuseStep 7822345 = 5866759) B5866759
theorem B10429793 : Blo 1268452 10429793 := bstep (se 2 (by rfl) ⟨3911172, by rfl⟩ : syracuseStep 10429793 = 7822345) B7822345
theorem B6953195 : Blo 1268452 6953195 := bstep (se 1 (by rfl) ⟨5214896, by rfl⟩ : syracuseStep 6953195 = 10429793) B10429793
theorem B4635463 : Blo 1268452 4635463 := bstep (se 1 (by rfl) ⟨3476597, by rfl⟩ : syracuseStep 4635463 = 6953195) B6953195
theorem B6180617 : Blo 1268452 6180617 := bstep (se 2 (by rfl) ⟨2317731, by rfl⟩ : syracuseStep 6180617 = 4635463) B4635463
theorem B4120411 : Blo 1268452 4120411 := bstep (se 1 (by rfl) ⟨3090308, by rfl⟩ : syracuseStep 4120411 = 6180617) B6180617
theorem B5493881 : Blo 1268452 5493881 := bstep (se 2 (by rfl) ⟨2060205, by rfl⟩ : syracuseStep 5493881 = 4120411) B4120411
theorem B3662587 : Blo 1268452 3662587 := bstep (se 1 (by rfl) ⟨2746940, by rfl⟩ : syracuseStep 3662587 = 5493881) B5493881
theorem B19533797 : Blo 1268452 19533797 := bstep (se 4 (by rfl) ⟨1831293, by rfl⟩ : syracuseStep 19533797 = 3662587) B3662587
theorem B13022531 : Blo 1268452 13022531 := bstep (se 1 (by rfl) ⟨9766898, by rfl⟩ : syracuseStep 13022531 = 19533797) B19533797
theorem B8681687 : Blo 1268452 8681687 := bstep (se 1 (by rfl) ⟨6511265, by rfl⟩ : syracuseStep 8681687 = 13022531) B13022531
theorem B5787791 : Blo 1268452 5787791 := bstep (se 1 (by rfl) ⟨4340843, by rfl⟩ : syracuseStep 5787791 = 8681687) B8681687
theorem B3858527 : Blo 1268452 3858527 := bstep (se 1 (by rfl) ⟨2893895, by rfl⟩ : syracuseStep 3858527 = 5787791) B5787791
theorem B10289405 : Blo 1268452 10289405 := bstep (se 3 (by rfl) ⟨1929263, by rfl⟩ : syracuseStep 10289405 = 3858527) B3858527
theorem B6859603 : Blo 1268452 6859603 := bstep (se 1 (by rfl) ⟨5144702, by rfl⟩ : syracuseStep 6859603 = 10289405) B10289405
theorem B9146137 : Blo 1268452 9146137 := bstep (se 2 (by rfl) ⟨3429801, by rfl⟩ : syracuseStep 9146137 = 6859603) B6859603
theorem B12194849 : Blo 1268452 12194849 := bstep (se 2 (by rfl) ⟨4573068, by rfl⟩ : syracuseStep 12194849 = 9146137) B9146137
theorem B8129899 : Blo 1268452 8129899 := bstep (se 1 (by rfl) ⟨6097424, by rfl⟩ : syracuseStep 8129899 = 12194849) B12194849
theorem B10839865 : Blo 1268452 10839865 := bstep (se 2 (by rfl) ⟨4064949, by rfl⟩ : syracuseStep 10839865 = 8129899) B8129899
theorem B14453153 : Blo 1268452 14453153 := bstep (se 2 (by rfl) ⟨5419932, by rfl⟩ : syracuseStep 14453153 = 10839865) B10839865
theorem B9635435 : Blo 1268452 9635435 := bstep (se 1 (by rfl) ⟨7226576, by rfl⟩ : syracuseStep 9635435 = 14453153) B14453153
theorem B6423623 : Blo 1268452 6423623 := bstep (se 1 (by rfl) ⟨4817717, by rfl⟩ : syracuseStep 6423623 = 9635435) B9635435
theorem B4282415 : Blo 1268452 4282415 := bstep (se 1 (by rfl) ⟨3211811, by rfl⟩ : syracuseStep 4282415 = 6423623) B6423623
theorem B2854943 : Blo 1268452 2854943 := bstep (se 1 (by rfl) ⟨2141207, by rfl⟩ : syracuseStep 2854943 = 4282415) B4282415
theorem B1903295 : Blo 1268452 1903295 := bstep (se 1 (by rfl) ⟨1427471, by rfl⟩ : syracuseStep 1903295 = 2854943) B2854943
theorem B1268863 : Blo 1268452 1268863 := bstep (se 1 (by rfl) ⟨951647, by rfl⟩ : syracuseStep 1268863 = 1903295) B1903295

theorem C0 (j : ℕ) (h1 : 317113 ≤ j) (h2 : j ≤ 317612) : Blo 1268452 (4 * j + 3) := by
  interval_cases j
  · exact B1268455
  · exact B1268459
  · exact B1268463
  · exact B1268467
  · exact B1268471
  · exact B1268475
  · exact B1268479
  · exact B1268483
  · exact B1268487
  · exact B1268491
  · exact B1268495
  · exact B1268499
  · exact B1268503
  · exact B1268507
  · exact B1268511
  · exact B1268515
  · exact B1268519
  · exact B1268523
  · exact B1268527
  · exact B1268531
  · exact B1268535
  · exact B1268539
  · exact B1268543
  · exact B1268547
  · exact B1268551
  · exact B1268555
  · exact B1268559
  · exact B1268563
  · exact B1268567
  · exact B1268571
  · exact B1268575
  · exact B1268579
  · exact B1268583
  · exact B1268587
  · exact B1268591
  · exact B1268595
  · exact B1268599
  · exact B1268603
  · exact B1268607
  · exact B1268611
  · exact B1268615
  · exact B1268619
  · exact B1268623
  · exact B1268627
  · exact B1268631
  · exact B1268635
  · exact B1268639
  · exact B1268643
  · exact B1268647
  · exact B1268651
  · exact B1268655
  · exact B1268659
  · exact B1268663
  · exact B1268667
  · exact B1268671
  · exact B1268675
  · exact B1268679
  · exact B1268683
  · exact B1268687
  · exact B1268691
  · exact B1268695
  · exact B1268699
  · exact B1268703
  · exact B1268707
  · exact B1268711
  · exact B1268715
  · exact B1268719
  · exact B1268723
  · exact B1268727
  · exact B1268731
  · exact B1268735
  · exact B1268739
  · exact B1268743
  · exact B1268747
  · exact B1268751
  · exact B1268755
  · exact B1268759
  · exact B1268763
  · exact B1268767
  · exact B1268771
  · exact B1268775
  · exact B1268779
  · exact B1268783
  · exact B1268787
  · exact B1268791
  · exact B1268795
  · exact B1268799
  · exact B1268803
  · exact B1268807
  · exact B1268811
  · exact B1268815
  · exact B1268819
  · exact B1268823
  · exact B1268827
  · exact B1268831
  · exact B1268835
  · exact B1268839
  · exact B1268843
  · exact B1268847
  · exact B1268851
  · exact B1268855
  · exact B1268859
  · exact B1268863
  · exact B1268867
  · exact B1268871
  · exact B1268875
  · exact B1268879
  · exact B1268883
  · exact B1268887
  · exact B1268891
  · exact B1268895
  · exact B1268899
  · exact B1268903
  · exact B1268907
  · exact B1268911
  · exact B1268915
  · exact B1268919
  · exact B1268923
  · exact B1268927
  · exact B1268931
  · exact B1268935
  · exact B1268939
  · exact B1268943
  · exact B1268947
  · exact B1268951
  · exact B1268955
  · exact B1268959
  · exact B1268963
  · exact B1268967
  · exact B1268971
  · exact B1268975
  · exact B1268979
  · exact B1268983
  · exact B1268987
  · exact B1268991
  · exact B1268995
  · exact B1268999
  · exact B1269003
  · exact B1269007
  · exact B1269011
  · exact B1269015
  · exact B1269019
  · exact B1269023
  · exact B1269027
  · exact B1269031
  · exact B1269035
  · exact B1269039
  · exact B1269043
  · exact B1269047
  · exact B1269051
  · exact B1269055
  · exact B1269059
  · exact B1269063
  · exact B1269067
  · exact B1269071
  · exact B1269075
  · exact B1269079
  · exact B1269083
  · exact B1269087
  · exact B1269091
  · exact B1269095
  · exact B1269099
  · exact B1269103
  · exact B1269107
  · exact B1269111
  · exact B1269115
  · exact B1269119
  · exact B1269123
  · exact B1269127
  · exact B1269131
  · exact B1269135
  · exact B1269139
  · exact B1269143
  · exact B1269147
  · exact B1269151
  · exact B1269155
  · exact B1269159
  · exact B1269163
  · exact B1269167
  · exact B1269171
  · exact B1269175
  · exact B1269179
  · exact B1269183
  · exact B1269187
  · exact B1269191
  · exact B1269195
  · exact B1269199
  · exact B1269203
  · exact B1269207
  · exact B1269211
  · exact B1269215
  · exact B1269219
  · exact B1269223
  · exact B1269227
  · exact B1269231
  · exact B1269235
  · exact B1269239
  · exact B1269243
  · exact B1269247
  · exact B1269251
  · exact B1269255
  · exact B1269259
  · exact B1269263
  · exact B1269267
  · exact B1269271
  · exact B1269275
  · exact B1269279
  · exact B1269283
  · exact B1269287
  · exact B1269291
  · exact B1269295
  · exact B1269299
  · exact B1269303
  · exact B1269307
  · exact B1269311
  · exact B1269315
  · exact B1269319
  · exact B1269323
  · exact B1269327
  · exact B1269331
  · exact B1269335
  · exact B1269339
  · exact B1269343
  · exact B1269347
  · exact B1269351
  · exact B1269355
  · exact B1269359
  · exact B1269363
  · exact B1269367
  · exact B1269371
  · exact B1269375
  · exact B1269379
  · exact B1269383
  · exact B1269387
  · exact B1269391
  · exact B1269395
  · exact B1269399
  · exact B1269403
  · exact B1269407
  · exact B1269411
  · exact B1269415
  · exact B1269419
  · exact B1269423
  · exact B1269427
  · exact B1269431
  · exact B1269435
  · exact B1269439
  · exact B1269443
  · exact B1269447
  · exact B1269451
  · exact B1269455
  · exact B1269459
  · exact B1269463
  · exact B1269467
  · exact B1269471
  · exact B1269475
  · exact B1269479
  · exact B1269483
  · exact B1269487
  · exact B1269491
  · exact B1269495
  · exact B1269499
  · exact B1269503
  · exact B1269507
  · exact B1269511
  · exact B1269515
  · exact B1269519
  · exact B1269523
  · exact B1269527
  · exact B1269531
  · exact B1269535
  · exact B1269539
  · exact B1269543
  · exact B1269547
  · exact B1269551
  · exact B1269555
  · exact B1269559
  · exact B1269563
  · exact B1269567
  · exact B1269571
  · exact B1269575
  · exact B1269579
  · exact B1269583
  · exact B1269587
  · exact B1269591
  · exact B1269595
  · exact B1269599
  · exact B1269603
  · exact B1269607
  · exact B1269611
  · exact B1269615
  · exact B1269619
  · exact B1269623
  · exact B1269627
  · exact B1269631
  · exact B1269635
  · exact B1269639
  · exact B1269643
  · exact B1269647
  · exact B1269651
  · exact B1269655
  · exact B1269659
  · exact B1269663
  · exact B1269667
  · exact B1269671
  · exact B1269675
  · exact B1269679
  · exact B1269683
  · exact B1269687
  · exact B1269691
  · exact B1269695
  · exact B1269699
  · exact B1269703
  · exact B1269707
  · exact B1269711
  · exact B1269715
  · exact B1269719
  · exact B1269723
  · exact B1269727
  · exact B1269731
  · exact B1269735
  · exact B1269739
  · exact B1269743
  · exact B1269747
  · exact B1269751
  · exact B1269755
  · exact B1269759
  · exact B1269763
  · exact B1269767
  · exact B1269771
  · exact B1269775
  · exact B1269779
  · exact B1269783
  · exact B1269787
  · exact B1269791
  · exact B1269795
  · exact B1269799
  · exact B1269803
  · exact B1269807
  · exact B1269811
  · exact B1269815
  · exact B1269819
  · exact B1269823
  · exact B1269827
  · exact B1269831
  · exact B1269835
  · exact B1269839
  · exact B1269843
  · exact B1269847
  · exact B1269851
  · exact B1269855
  · exact B1269859
  · exact B1269863
  · exact B1269867
  · exact B1269871
  · exact B1269875
  · exact B1269879
  · exact B1269883
  · exact B1269887
  · exact B1269891
  · exact B1269895
  · exact B1269899
  · exact B1269903
  · exact B1269907
  · exact B1269911
  · exact B1269915
  · exact B1269919
  · exact B1269923
  · exact B1269927
  · exact B1269931
  · exact B1269935
  · exact B1269939
  · exact B1269943
  · exact B1269947
  · exact B1269951
  · exact B1269955
  · exact B1269959
  · exact B1269963
  · exact B1269967
  · exact B1269971
  · exact B1269975
  · exact B1269979
  · exact B1269983
  · exact B1269987
  · exact B1269991
  · exact B1269995
  · exact B1269999
  · exact B1270003
  · exact B1270007
  · exact B1270011
  · exact B1270015
  · exact B1270019
  · exact B1270023
  · exact B1270027
  · exact B1270031
  · exact B1270035
  · exact B1270039
  · exact B1270043
  · exact B1270047
  · exact B1270051
  · exact B1270055
  · exact B1270059
  · exact B1270063
  · exact B1270067
  · exact B1270071
  · exact B1270075
  · exact B1270079
  · exact B1270083
  · exact B1270087
  · exact B1270091
  · exact B1270095
  · exact B1270099
  · exact B1270103
  · exact B1270107
  · exact B1270111
  · exact B1270115
  · exact B1270119
  · exact B1270123
  · exact B1270127
  · exact B1270131
  · exact B1270135
  · exact B1270139
  · exact B1270143
  · exact B1270147
  · exact B1270151
  · exact B1270155
  · exact B1270159
  · exact B1270163
  · exact B1270167
  · exact B1270171
  · exact B1270175
  · exact B1270179
  · exact B1270183
  · exact B1270187
  · exact B1270191
  · exact B1270195
  · exact B1270199
  · exact B1270203
  · exact B1270207
  · exact B1270211
  · exact B1270215
  · exact B1270219
  · exact B1270223
  · exact B1270227
  · exact B1270231
  · exact B1270235
  · exact B1270239
  · exact B1270243
  · exact B1270247
  · exact B1270251
  · exact B1270255
  · exact B1270259
  · exact B1270263
  · exact B1270267
  · exact B1270271
  · exact B1270275
  · exact B1270279
  · exact B1270283
  · exact B1270287
  · exact B1270291
  · exact B1270295
  · exact B1270299
  · exact B1270303
  · exact B1270307
  · exact B1270311
  · exact B1270315
  · exact B1270319
  · exact B1270323
  · exact B1270327
  · exact B1270331
  · exact B1270335
  · exact B1270339
  · exact B1270343
  · exact B1270347
  · exact B1270351
  · exact B1270355
  · exact B1270359
  · exact B1270363
  · exact B1270367
  · exact B1270371
  · exact B1270375
  · exact B1270379
  · exact B1270383
  · exact B1270387
  · exact B1270391
  · exact B1270395
  · exact B1270399
  · exact B1270403
  · exact B1270407
  · exact B1270411
  · exact B1270415
  · exact B1270419
  · exact B1270423
  · exact B1270427
  · exact B1270431
  · exact B1270435
  · exact B1270439
  · exact B1270443
  · exact B1270447
  · exact B1270451

theorem solution (m : ℕ) (hlo : 1268452 ≤ m) (hhi : m ≤ 1270452) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 317113 ≤ j := by omega
    have hj2 : j ≤ 317612 := by omega
    have hb : Blo 1268452 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
