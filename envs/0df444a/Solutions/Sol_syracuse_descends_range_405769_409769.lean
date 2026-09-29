-- Prove2me | solution 1 for syracuse_descends_range_405769_409769
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:49.701757+00:00
-- url     : https://prove2.me/submissions/7607b8a8-57b3-4059-bd32-9178c16fcb55

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


theorem B458761 : Blo 405769 458761 := bbase (se 2 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 458761 = 344071) (by norm_num)
theorem B917549 : Blo 405769 917549 := bbase (se 3 (by rfl) ⟨172040, by rfl⟩ : syracuseStep 917549 = 344081) (by norm_num)
theorem B458797 : Blo 405769 458797 := bbase (se 3 (by rfl) ⟨86024, by rfl⟩ : syracuseStep 458797 = 172049) (by norm_num)
theorem B688189 : Blo 405769 688189 := bbase (se 3 (by rfl) ⟨129035, by rfl⟩ : syracuseStep 688189 = 258071) (by norm_num)
theorem B458833 : Blo 405769 458833 := bbase (se 2 (by rfl) ⟨172062, by rfl⟩ : syracuseStep 458833 = 344125) (by norm_num)
theorem B917621 : Blo 405769 917621 := bbase (se 5 (by rfl) ⟨43013, by rfl⟩ : syracuseStep 917621 = 86027) (by norm_num)
theorem B458869 : Blo 405769 458869 := bbase (se 5 (by rfl) ⟨21509, by rfl⟩ : syracuseStep 458869 = 43019) (by norm_num)
theorem B1376405 : Blo 405769 1376405 := bbase (se 6 (by rfl) ⟨32259, by rfl⟩ : syracuseStep 1376405 = 64519) (by norm_num)
theorem B688277 : Blo 405769 688277 := bbase (se 6 (by rfl) ⟨16131, by rfl⟩ : syracuseStep 688277 = 32263) (by norm_num)
theorem B458905 : Blo 405769 458905 := bbase (se 2 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 458905 = 344179) (by norm_num)
theorem B917693 : Blo 405769 917693 := bbase (se 3 (by rfl) ⟨172067, by rfl⟩ : syracuseStep 917693 = 344135) (by norm_num)
theorem B458941 : Blo 405769 458941 := bbase (se 3 (by rfl) ⟨86051, by rfl⟩ : syracuseStep 458941 = 172103) (by norm_num)
theorem B524485 : Blo 405769 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B1474757 : Blo 405769 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B458977 : Blo 405769 458977 := bbase (se 2 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 458977 = 344233) (by norm_num)
theorem B917765 : Blo 405769 917765 := bbase (se 4 (by rfl) ⟨86040, by rfl⟩ : syracuseStep 917765 = 172081) (by norm_num)
theorem B459013 : Blo 405769 459013 := bbase (se 4 (by rfl) ⟨43032, by rfl⟩ : syracuseStep 459013 = 86065) (by norm_num)
theorem B688405 : Blo 405769 688405 := bbase (se 6 (by rfl) ⟨16134, by rfl⟩ : syracuseStep 688405 = 32269) (by norm_num)
theorem B459049 : Blo 405769 459049 := bbase (se 2 (by rfl) ⟨172143, by rfl⟩ : syracuseStep 459049 = 344287) (by norm_num)
theorem B655685 : Blo 405769 655685 := bbase (se 4 (by rfl) ⟨61470, by rfl⟩ : syracuseStep 655685 = 122941) (by norm_num)
theorem B491845 : Blo 405769 491845 := bbase (se 4 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 491845 = 92221) (by norm_num)
theorem B917837 : Blo 405769 917837 := bbase (se 3 (by rfl) ⟨172094, by rfl⟩ : syracuseStep 917837 = 344189) (by norm_num)
theorem B459085 : Blo 405769 459085 := bbase (se 3 (by rfl) ⟨86078, by rfl⟩ : syracuseStep 459085 = 172157) (by norm_num)
theorem B1311061 : Blo 405769 1311061 := bbase (se 10 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 1311061 = 3841) (by norm_num)
theorem B688493 : Blo 405769 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B459121 : Blo 405769 459121 := bbase (se 2 (by rfl) ⟨172170, by rfl⟩ : syracuseStep 459121 = 344341) (by norm_num)
theorem B1245557 : Blo 405769 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B917909 : Blo 405769 917909 := bbase (se 6 (by rfl) ⟨21513, by rfl⟩ : syracuseStep 917909 = 43027) (by norm_num)
theorem B459157 : Blo 405769 459157 := bbase (se 6 (by rfl) ⟨10761, by rfl⟩ : syracuseStep 459157 = 21523) (by norm_num)
theorem B459193 : Blo 405769 459193 := bbase (se 2 (by rfl) ⟨172197, by rfl⟩ : syracuseStep 459193 = 344395) (by norm_num)
theorem B885181 : Blo 405769 885181 := bbase (se 3 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 885181 = 331943) (by norm_num)
theorem B917981 : Blo 405769 917981 := bbase (se 3 (by rfl) ⟨172121, by rfl⟩ : syracuseStep 917981 = 344243) (by norm_num)
theorem B459229 : Blo 405769 459229 := bbase (se 3 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 459229 = 172211) (by norm_num)
theorem B688621 : Blo 405769 688621 := bbase (se 3 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 688621 = 258233) (by norm_num)
theorem B459265 : Blo 405769 459265 := bbase (se 2 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 459265 = 344449) (by norm_num)
theorem B918053 : Blo 405769 918053 := bbase (se 4 (by rfl) ⟨86067, by rfl⟩ : syracuseStep 918053 = 172135) (by norm_num)
theorem B459301 : Blo 405769 459301 := bbase (se 4 (by rfl) ⟨43059, by rfl⟩ : syracuseStep 459301 = 86119) (by norm_num)
theorem B1376837 : Blo 405769 1376837 := bbase (se 4 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 1376837 = 258157) (by norm_num)
theorem B688709 : Blo 405769 688709 := bbase (se 4 (by rfl) ⟨64566, by rfl⟩ : syracuseStep 688709 = 129133) (by norm_num)
theorem B459337 : Blo 405769 459337 := bbase (se 2 (by rfl) ⟨172251, by rfl⟩ : syracuseStep 459337 = 344503) (by norm_num)
theorem B918125 : Blo 405769 918125 := bbase (se 3 (by rfl) ⟨172148, by rfl⟩ : syracuseStep 918125 = 344297) (by norm_num)
theorem B459373 : Blo 405769 459373 := bbase (se 3 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 459373 = 172265) (by norm_num)
theorem B2065013 : Blo 405769 2065013 := bbase (se 5 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 2065013 = 193595) (by norm_num)
theorem B1540741 : Blo 405769 1540741 := bbase (se 4 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 1540741 = 288889) (by norm_num)
theorem B459409 : Blo 405769 459409 := bbase (se 2 (by rfl) ⟨172278, by rfl⟩ : syracuseStep 459409 = 344557) (by norm_num)
theorem B918197 : Blo 405769 918197 := bbase (se 5 (by rfl) ⟨43040, by rfl⟩ : syracuseStep 918197 = 86081) (by norm_num)
theorem B459445 : Blo 405769 459445 := bbase (se 5 (by rfl) ⟨21536, by rfl⟩ : syracuseStep 459445 = 43073) (by norm_num)
theorem B688837 : Blo 405769 688837 := bbase (se 4 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 688837 = 129157) (by norm_num)
theorem B492229 : Blo 405769 492229 := bbase (se 4 (by rfl) ⟨46146, by rfl⟩ : syracuseStep 492229 = 92293) (by norm_num)
theorem B459481 : Blo 405769 459481 := bbase (se 2 (by rfl) ⟨172305, by rfl⟩ : syracuseStep 459481 = 344611) (by norm_num)
theorem B918269 : Blo 405769 918269 := bbase (se 3 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 918269 = 344351) (by norm_num)
theorem B459517 : Blo 405769 459517 := bbase (se 3 (by rfl) ⟨86159, by rfl⟩ : syracuseStep 459517 = 172319) (by norm_num)
theorem B688925 : Blo 405769 688925 := bbase (se 3 (by rfl) ⟨129173, by rfl⟩ : syracuseStep 688925 = 258347) (by norm_num)
theorem B459553 : Blo 405769 459553 := bbase (se 2 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 459553 = 344665) (by norm_num)
theorem B918341 : Blo 405769 918341 := bbase (se 4 (by rfl) ⟨86094, by rfl⟩ : syracuseStep 918341 = 172189) (by norm_num)
theorem B459589 : Blo 405769 459589 := bbase (se 4 (by rfl) ⟨43086, by rfl⟩ : syracuseStep 459589 = 86173) (by norm_num)
theorem B1737557 : Blo 405769 1737557 := bbase (se 9 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 1737557 = 10181) (by norm_num)
theorem B525145 : Blo 405769 525145 := bbase (se 2 (by rfl) ⟨196929, by rfl⟩ : syracuseStep 525145 = 393859) (by norm_num)
theorem B459625 : Blo 405769 459625 := bbase (se 2 (by rfl) ⟨172359, by rfl⟩ : syracuseStep 459625 = 344719) (by norm_num)
theorem B918413 : Blo 405769 918413 := bbase (se 3 (by rfl) ⟨172202, by rfl⟩ : syracuseStep 918413 = 344405) (by norm_num)
theorem B459661 : Blo 405769 459661 := bbase (se 3 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 459661 = 172373) (by norm_num)
theorem B689053 : Blo 405769 689053 := bbase (se 3 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 689053 = 258395) (by norm_num)
theorem B459697 : Blo 405769 459697 := bbase (se 2 (by rfl) ⟨172386, by rfl⟩ : syracuseStep 459697 = 344773) (by norm_num)
theorem B1541045 : Blo 405769 1541045 := bbase (se 5 (by rfl) ⟨72236, by rfl⟩ : syracuseStep 1541045 = 144473) (by norm_num)
theorem B918485 : Blo 405769 918485 := bbase (se 7 (by rfl) ⟨10763, by rfl⟩ : syracuseStep 918485 = 21527) (by norm_num)
theorem B459733 : Blo 405769 459733 := bbase (se 7 (by rfl) ⟨5387, by rfl⟩ : syracuseStep 459733 = 10775) (by norm_num)
theorem B1377269 : Blo 405769 1377269 := bbase (se 5 (by rfl) ⟨64559, by rfl⟩ : syracuseStep 1377269 = 129119) (by norm_num)
theorem B689141 : Blo 405769 689141 := bbase (se 5 (by rfl) ⟨32303, by rfl⟩ : syracuseStep 689141 = 64607) (by norm_num)
theorem B459769 : Blo 405769 459769 := bbase (se 2 (by rfl) ⟨172413, by rfl⟩ : syracuseStep 459769 = 344827) (by norm_num)
theorem B918557 : Blo 405769 918557 := bbase (se 3 (by rfl) ⟨172229, by rfl⟩ : syracuseStep 918557 = 344459) (by norm_num)
theorem B459805 : Blo 405769 459805 := bbase (se 3 (by rfl) ⟨86213, by rfl⟩ : syracuseStep 459805 = 172427) (by norm_num)
theorem B459841 : Blo 405769 459841 := bbase (se 2 (by rfl) ⟨172440, by rfl⟩ : syracuseStep 459841 = 344881) (by norm_num)
theorem B918629 : Blo 405769 918629 := bbase (se 4 (by rfl) ⟨86121, by rfl⟩ : syracuseStep 918629 = 172243) (by norm_num)
theorem B459877 : Blo 405769 459877 := bbase (se 4 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 459877 = 86227) (by norm_num)
theorem B1737845 : Blo 405769 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B689269 : Blo 405769 689269 := bbase (se 5 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 689269 = 64619) (by norm_num)
theorem B459913 : Blo 405769 459913 := bbase (se 2 (by rfl) ⟨172467, by rfl⟩ : syracuseStep 459913 = 344935) (by norm_num)
theorem B1311893 : Blo 405769 1311893 := bbase (se 6 (by rfl) ⟨30747, by rfl⟩ : syracuseStep 1311893 = 61495) (by norm_num)
theorem B918701 : Blo 405769 918701 := bbase (se 3 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 918701 = 344513) (by norm_num)
theorem B459949 : Blo 405769 459949 := bbase (se 3 (by rfl) ⟨86240, by rfl⟩ : syracuseStep 459949 = 172481) (by norm_num)
theorem B1475765 : Blo 405769 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B689357 : Blo 405769 689357 := bbase (se 3 (by rfl) ⟨129254, by rfl⟩ : syracuseStep 689357 = 258509) (by norm_num)
theorem B459985 : Blo 405769 459985 := bbase (se 2 (by rfl) ⟨172494, by rfl⟩ : syracuseStep 459985 = 344989) (by norm_num)
theorem B918773 : Blo 405769 918773 := bbase (se 5 (by rfl) ⟨43067, by rfl⟩ : syracuseStep 918773 = 86135) (by norm_num)
theorem B460021 : Blo 405769 460021 := bbase (se 5 (by rfl) ⟨21563, by rfl⟩ : syracuseStep 460021 = 43127) (by norm_num)
theorem B984325 : Blo 405769 984325 := bbase (se 4 (by rfl) ⟨92280, by rfl⟩ : syracuseStep 984325 = 184561) (by norm_num)
theorem B460057 : Blo 405769 460057 := bbase (se 2 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 460057 = 345043) (by norm_num)
theorem B591157 : Blo 405769 591157 := bbase (se 5 (by rfl) ⟨27710, by rfl⟩ : syracuseStep 591157 = 55421) (by norm_num)
theorem B918845 : Blo 405769 918845 := bbase (se 3 (by rfl) ⟨172283, by rfl⟩ : syracuseStep 918845 = 344567) (by norm_num)
theorem B460093 : Blo 405769 460093 := bbase (se 3 (by rfl) ⟨86267, by rfl⟩ : syracuseStep 460093 = 172535) (by norm_num)
theorem B689485 : Blo 405769 689485 := bbase (se 3 (by rfl) ⟨129278, by rfl⟩ : syracuseStep 689485 = 258557) (by norm_num)
theorem B460129 : Blo 405769 460129 := bbase (se 2 (by rfl) ⟨172548, by rfl⟩ : syracuseStep 460129 = 345097) (by norm_num)
theorem B918917 : Blo 405769 918917 := bbase (se 4 (by rfl) ⟨86148, by rfl⟩ : syracuseStep 918917 = 172297) (by norm_num)
theorem B460165 : Blo 405769 460165 := bbase (se 4 (by rfl) ⟨43140, by rfl⟩ : syracuseStep 460165 = 86281) (by norm_num)
theorem B1377701 : Blo 405769 1377701 := bbase (se 4 (by rfl) ⟨129159, by rfl⟩ : syracuseStep 1377701 = 258319) (by norm_num)
theorem B689573 : Blo 405769 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B460201 : Blo 405769 460201 := bbase (se 2 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 460201 = 345151) (by norm_num)
theorem B918989 : Blo 405769 918989 := bbase (se 3 (by rfl) ⟨172310, by rfl⟩ : syracuseStep 918989 = 344621) (by norm_num)
theorem B460237 : Blo 405769 460237 := bbase (se 3 (by rfl) ⟨86294, by rfl⟩ : syracuseStep 460237 = 172589) (by norm_num)
theorem B460273 : Blo 405769 460273 := bbase (se 2 (by rfl) ⟨172602, by rfl⟩ : syracuseStep 460273 = 345205) (by norm_num)
theorem B919061 : Blo 405769 919061 := bbase (se 6 (by rfl) ⟨21540, by rfl⟩ : syracuseStep 919061 = 43081) (by norm_num)
theorem B460309 : Blo 405769 460309 := bbase (se 6 (by rfl) ⟨10788, by rfl⟩ : syracuseStep 460309 = 21577) (by norm_num)
theorem B689701 : Blo 405769 689701 := bbase (se 4 (by rfl) ⟨64659, by rfl⟩ : syracuseStep 689701 = 129319) (by norm_num)
theorem B460345 : Blo 405769 460345 := bbase (se 2 (by rfl) ⟨172629, by rfl⟩ : syracuseStep 460345 = 345259) (by norm_num)
theorem B919133 : Blo 405769 919133 := bbase (se 3 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 919133 = 344675) (by norm_num)
theorem B460381 : Blo 405769 460381 := bbase (se 3 (by rfl) ⟨86321, by rfl⟩ : syracuseStep 460381 = 172643) (by norm_num)
theorem B689789 : Blo 405769 689789 := bbase (se 3 (by rfl) ⟨129335, by rfl⟩ : syracuseStep 689789 = 258671) (by norm_num)
theorem B460417 : Blo 405769 460417 := bbase (se 2 (by rfl) ⟨172656, by rfl⟩ : syracuseStep 460417 = 345313) (by norm_num)
theorem B919205 : Blo 405769 919205 := bbase (se 4 (by rfl) ⟨86175, by rfl⟩ : syracuseStep 919205 = 172351) (by norm_num)
theorem B460453 : Blo 405769 460453 := bbase (se 4 (by rfl) ⟨43167, by rfl⟩ : syracuseStep 460453 = 86335) (by norm_num)
theorem B460489 : Blo 405769 460489 := bbase (se 2 (by rfl) ⟨172683, by rfl⟩ : syracuseStep 460489 = 345367) (by norm_num)
theorem B919277 : Blo 405769 919277 := bbase (se 3 (by rfl) ⟨172364, by rfl⟩ : syracuseStep 919277 = 344729) (by norm_num)
theorem B460525 : Blo 405769 460525 := bbase (se 3 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 460525 = 172697) (by norm_num)
theorem B689917 : Blo 405769 689917 := bbase (se 3 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 689917 = 258719) (by norm_num)
theorem B460561 : Blo 405769 460561 := bbase (se 2 (by rfl) ⟨172710, by rfl⟩ : syracuseStep 460561 = 345421) (by norm_num)
theorem B919349 : Blo 405769 919349 := bbase (se 5 (by rfl) ⟨43094, by rfl⟩ : syracuseStep 919349 = 86189) (by norm_num)
theorem B460597 : Blo 405769 460597 := bbase (se 5 (by rfl) ⟨21590, by rfl⟩ : syracuseStep 460597 = 43181) (by norm_num)
theorem B1378133 : Blo 405769 1378133 := bbase (se 9 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 1378133 = 8075) (by norm_num)
theorem B690005 : Blo 405769 690005 := bbase (se 9 (by rfl) ⟨2021, by rfl⟩ : syracuseStep 690005 = 4043) (by norm_num)
theorem B460633 : Blo 405769 460633 := bbase (se 2 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 460633 = 345475) (by norm_num)
theorem B1738597 : Blo 405769 1738597 := bbase (se 4 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 1738597 = 325987) (by norm_num)
theorem B919421 : Blo 405769 919421 := bbase (se 3 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 919421 = 344783) (by norm_num)
theorem B460669 : Blo 405769 460669 := bbase (se 3 (by rfl) ⟨86375, by rfl⟩ : syracuseStep 460669 = 172751) (by norm_num)
theorem B2066309 : Blo 405769 2066309 := bbase (se 4 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 2066309 = 387433) (by norm_num)
theorem B460705 : Blo 405769 460705 := bbase (se 2 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 460705 = 345529) (by norm_num)
theorem B919493 : Blo 405769 919493 := bbase (se 4 (by rfl) ⟨86202, by rfl⟩ : syracuseStep 919493 = 172405) (by norm_num)
theorem B460741 : Blo 405769 460741 := bbase (se 4 (by rfl) ⟨43194, by rfl⟩ : syracuseStep 460741 = 86389) (by norm_num)
theorem B690133 : Blo 405769 690133 := bbase (se 7 (by rfl) ⟨8087, by rfl⟩ : syracuseStep 690133 = 16175) (by norm_num)
theorem B460777 : Blo 405769 460777 := bbase (se 2 (by rfl) ⟨172791, by rfl⟩ : syracuseStep 460777 = 345583) (by norm_num)
theorem B919565 : Blo 405769 919565 := bbase (se 3 (by rfl) ⟨172418, by rfl⟩ : syracuseStep 919565 = 344837) (by norm_num)
theorem B460813 : Blo 405769 460813 := bbase (se 3 (by rfl) ⟨86402, by rfl⟩ : syracuseStep 460813 = 172805) (by norm_num)
theorem B690221 : Blo 405769 690221 := bbase (se 3 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 690221 = 258833) (by norm_num)
theorem B460849 : Blo 405769 460849 := bbase (se 2 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 460849 = 345637) (by norm_num)
theorem B919637 : Blo 405769 919637 := bbase (se 8 (by rfl) ⟨5388, by rfl⟩ : syracuseStep 919637 = 10777) (by norm_num)
theorem B460885 : Blo 405769 460885 := bbase (se 8 (by rfl) ⟨2700, by rfl⟩ : syracuseStep 460885 = 5401) (by norm_num)
theorem B460921 : Blo 405769 460921 := bbase (se 2 (by rfl) ⟨172845, by rfl⟩ : syracuseStep 460921 = 345691) (by norm_num)
theorem B919709 : Blo 405769 919709 := bbase (se 3 (by rfl) ⟨172445, by rfl⟩ : syracuseStep 919709 = 344891) (by norm_num)
theorem B460957 : Blo 405769 460957 := bbase (se 3 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 460957 = 172859) (by norm_num)
theorem B690349 : Blo 405769 690349 := bbase (se 3 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 690349 = 258881) (by norm_num)
theorem B919781 : Blo 405769 919781 := bbase (se 4 (by rfl) ⟨86229, by rfl⟩ : syracuseStep 919781 = 172459) (by norm_num)
theorem B1378565 : Blo 405769 1378565 := bbase (se 4 (by rfl) ⟨129240, by rfl⟩ : syracuseStep 1378565 = 258481) (by norm_num)
theorem B690437 : Blo 405769 690437 := bbase (se 4 (by rfl) ⟨64728, by rfl⟩ : syracuseStep 690437 = 129457) (by norm_num)
theorem B919853 : Blo 405769 919853 := bbase (se 3 (by rfl) ⟨172472, by rfl⟩ : syracuseStep 919853 = 344945) (by norm_num)
theorem B1968437 : Blo 405769 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B919925 : Blo 405769 919925 := bbase (se 5 (by rfl) ⟨43121, by rfl⟩ : syracuseStep 919925 = 86243) (by norm_num)
theorem B690565 : Blo 405769 690565 := bbase (se 4 (by rfl) ⟨64740, by rfl⟩ : syracuseStep 690565 = 129481) (by norm_num)
theorem B1968533 : Blo 405769 1968533 := bbase (se 6 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 1968533 = 92275) (by norm_num)
theorem B919997 : Blo 405769 919997 := bbase (se 3 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 919997 = 344999) (by norm_num)
theorem B690653 : Blo 405769 690653 := bbase (se 3 (by rfl) ⟨129497, by rfl⟩ : syracuseStep 690653 = 258995) (by norm_num)
theorem B920069 : Blo 405769 920069 := bbase (se 4 (by rfl) ⟨86256, by rfl⟩ : syracuseStep 920069 = 172513) (by norm_num)
theorem B1739333 : Blo 405769 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B920141 : Blo 405769 920141 := bbase (se 3 (by rfl) ⟨172526, by rfl⟩ : syracuseStep 920141 = 345053) (by norm_num)
theorem B690781 : Blo 405769 690781 := bbase (se 3 (by rfl) ⟨129521, by rfl⟩ : syracuseStep 690781 = 259043) (by norm_num)
theorem B920213 : Blo 405769 920213 := bbase (se 6 (by rfl) ⟨21567, by rfl⟩ : syracuseStep 920213 = 43135) (by norm_num)
theorem B1378997 : Blo 405769 1378997 := bbase (se 5 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 1378997 = 129281) (by norm_num)
theorem B690869 : Blo 405769 690869 := bbase (se 5 (by rfl) ⟨32384, by rfl⟩ : syracuseStep 690869 = 64769) (by norm_num)
theorem B920285 : Blo 405769 920285 := bbase (se 3 (by rfl) ⟨172553, by rfl⟩ : syracuseStep 920285 = 345107) (by norm_num)
theorem B920357 : Blo 405769 920357 := bbase (se 4 (by rfl) ⟨86283, by rfl⟩ : syracuseStep 920357 = 172567) (by norm_num)
theorem B690997 : Blo 405769 690997 := bbase (se 5 (by rfl) ⟨32390, by rfl⟩ : syracuseStep 690997 = 64781) (by norm_num)
theorem B920429 : Blo 405769 920429 := bbase (se 3 (by rfl) ⟨172580, by rfl⟩ : syracuseStep 920429 = 345161) (by norm_num)
theorem B691085 : Blo 405769 691085 := bbase (se 3 (by rfl) ⟨129578, by rfl⟩ : syracuseStep 691085 = 259157) (by norm_num)
theorem B920501 : Blo 405769 920501 := bbase (se 5 (by rfl) ⟨43148, by rfl⟩ : syracuseStep 920501 = 86297) (by norm_num)
theorem B4623317 : Blo 405769 4623317 := bbase (se 7 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 4623317 = 108359) (by norm_num)
theorem B1543157 : Blo 405769 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B920573 : Blo 405769 920573 := bbase (se 3 (by rfl) ⟨172607, by rfl⟩ : syracuseStep 920573 = 345215) (by norm_num)
theorem B691213 : Blo 405769 691213 := bbase (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) (by norm_num)
theorem B920645 : Blo 405769 920645 := bbase (se 4 (by rfl) ⟨86310, by rfl⟩ : syracuseStep 920645 = 172621) (by norm_num)
theorem B1379429 : Blo 405769 1379429 := bbase (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) (by norm_num)
theorem B691301 : Blo 405769 691301 := bbase (se 4 (by rfl) ⟨64809, by rfl⟩ : syracuseStep 691301 = 129619) (by norm_num)
theorem B494717 : Blo 405769 494717 := bbase (se 3 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 494717 = 185519) (by norm_num)
theorem B920717 : Blo 405769 920717 := bbase (se 3 (by rfl) ⟨172634, by rfl⟩ : syracuseStep 920717 = 345269) (by norm_num)
theorem B2067605 : Blo 405769 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B11144405 : Blo 405769 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B920789 : Blo 405769 920789 := bbase (se 7 (by rfl) ⟨10790, by rfl⟩ : syracuseStep 920789 = 21581) (by norm_num)
theorem B691429 : Blo 405769 691429 := bbase (se 4 (by rfl) ⟨64821, by rfl⟩ : syracuseStep 691429 = 129643) (by norm_num)
theorem B1543445 : Blo 405769 1543445 := bbase (se 6 (by rfl) ⟨36174, by rfl⟩ : syracuseStep 1543445 = 72349) (by norm_num)
theorem B920861 : Blo 405769 920861 := bbase (se 3 (by rfl) ⟨172661, by rfl⟩ : syracuseStep 920861 = 345323) (by norm_num)
theorem B920933 : Blo 405769 920933 := bbase (se 4 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 920933 = 172675) (by norm_num)
theorem B3083669 : Blo 405769 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B921005 : Blo 405769 921005 := bbase (se 3 (by rfl) ⟨172688, by rfl⟩ : syracuseStep 921005 = 345377) (by norm_num)
theorem B921077 : Blo 405769 921077 := bbase (se 5 (by rfl) ⟨43175, by rfl⟩ : syracuseStep 921077 = 86351) (by norm_num)
theorem B2100725 : Blo 405769 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B1379861 : Blo 405769 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B921149 : Blo 405769 921149 := bbase (se 3 (by rfl) ⟨172715, by rfl⟩ : syracuseStep 921149 = 345431) (by norm_num)
theorem B822917 : Blo 405769 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B921221 : Blo 405769 921221 := bbase (se 4 (by rfl) ⟨86364, by rfl⟩ : syracuseStep 921221 = 172729) (by norm_num)
theorem B921293 : Blo 405769 921293 := bbase (se 3 (by rfl) ⟨172742, by rfl⟩ : syracuseStep 921293 = 345485) (by norm_num)
theorem B921365 : Blo 405769 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B921437 : Blo 405769 921437 := bbase (se 3 (by rfl) ⟨172769, by rfl⟩ : syracuseStep 921437 = 345539) (by norm_num)
theorem B1576853 : Blo 405769 1576853 := bbase (se 6 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 1576853 = 73915) (by norm_num)
theorem B921509 : Blo 405769 921509 := bbase (se 4 (by rfl) ⟨86391, by rfl⟩ : syracuseStep 921509 = 172783) (by norm_num)
theorem B1380293 : Blo 405769 1380293 := bbase (se 4 (by rfl) ⟨129402, by rfl⟩ : syracuseStep 1380293 = 258805) (by norm_num)
theorem B921581 : Blo 405769 921581 := bbase (se 3 (by rfl) ⟨172796, by rfl⟩ : syracuseStep 921581 = 345593) (by norm_num)
theorem B921653 : Blo 405769 921653 := bbase (se 5 (by rfl) ⟨43202, by rfl⟩ : syracuseStep 921653 = 86405) (by norm_num)
theorem B921725 : Blo 405769 921725 := bbase (se 3 (by rfl) ⟨172823, by rfl⟩ : syracuseStep 921725 = 345647) (by norm_num)
theorem B921797 : Blo 405769 921797 := bbase (se 4 (by rfl) ⟨86418, by rfl⟩ : syracuseStep 921797 = 172837) (by norm_num)
theorem B921869 : Blo 405769 921869 := bbase (se 3 (by rfl) ⟨172850, by rfl⟩ : syracuseStep 921869 = 345701) (by norm_num)
theorem B921941 : Blo 405769 921941 := bbase (se 10 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 921941 = 2701) (by norm_num)
theorem B1380725 : Blo 405769 1380725 := bbase (se 5 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 1380725 = 129443) (by norm_num)
theorem B2068901 : Blo 405769 2068901 := bbase (se 4 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 2068901 = 387919) (by norm_num)
theorem B1544629 : Blo 405769 1544629 := bbase (se 5 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 1544629 = 144809) (by norm_num)
theorem B463325 : Blo 405769 463325 := bbase (se 3 (by rfl) ⟨86873, by rfl⟩ : syracuseStep 463325 = 173747) (by norm_num)
theorem B1544933 : Blo 405769 1544933 := bbase (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) (by norm_num)
theorem B1381157 : Blo 405769 1381157 := bbase (se 4 (by rfl) ⟨129483, by rfl⟩ : syracuseStep 1381157 = 258967) (by norm_num)
theorem B824149 : Blo 405769 824149 := bbase (se 9 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 824149 = 4829) (by norm_num)
theorem B463849 : Blo 405769 463849 := bbase (se 2 (by rfl) ⟨173943, by rfl⟩ : syracuseStep 463849 = 347887) (by norm_num)
theorem B463909 : Blo 405769 463909 := bbase (se 4 (by rfl) ⟨43491, by rfl⟩ : syracuseStep 463909 = 86983) (by norm_num)
theorem B1381589 : Blo 405769 1381589 := bbase (se 7 (by rfl) ⟨16190, by rfl⟩ : syracuseStep 1381589 = 32381) (by norm_num)
theorem B7804309 : Blo 405769 7804309 := bbase (se 6 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 7804309 = 365827) (by norm_num)
theorem B1382021 : Blo 405769 1382021 := bbase (se 4 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 1382021 = 259129) (by norm_num)
theorem B2070197 : Blo 405769 2070197 := bbase (se 5 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 2070197 = 194081) (by norm_num)
theorem B530101 : Blo 405769 530101 := bbase (se 5 (by rfl) ⟨24848, by rfl⟩ : syracuseStep 530101 = 49697) (by norm_num)
theorem B1742629 : Blo 405769 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B3479381 : Blo 405769 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B464789 : Blo 405769 464789 := bbase (se 6 (by rfl) ⟨10893, by rfl⟩ : syracuseStep 464789 = 21787) (by norm_num)
theorem B1382453 : Blo 405769 1382453 := bbase (se 5 (by rfl) ⟨64802, by rfl⟩ : syracuseStep 1382453 = 129605) (by norm_num)
theorem B1382885 : Blo 405769 1382885 := bbase (se 4 (by rfl) ⟨129645, by rfl⟩ : syracuseStep 1382885 = 259291) (by norm_num)
theorem B694829 : Blo 405769 694829 := bbase (se 3 (by rfl) ⟨130280, by rfl⟩ : syracuseStep 694829 = 260561) (by norm_num)
theorem B1547045 : Blo 405769 1547045 := bbase (se 4 (by rfl) ⟨145035, by rfl⟩ : syracuseStep 1547045 = 290071) (by norm_num)
theorem B695117 : Blo 405769 695117 := bbase (se 3 (by rfl) ⟨130334, by rfl⟩ : syracuseStep 695117 = 260669) (by norm_num)
theorem B2071493 : Blo 405769 2071493 := bbase (se 4 (by rfl) ⟨194202, by rfl⟩ : syracuseStep 2071493 = 388405) (by norm_num)
theorem B1547333 : Blo 405769 1547333 := bbase (se 4 (by rfl) ⟨145062, by rfl⟩ : syracuseStep 1547333 = 290125) (by norm_num)
theorem B826453 : Blo 405769 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B695461 : Blo 405769 695461 := bbase (se 4 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 695461 = 130399) (by norm_num)
theorem B466273 : Blo 405769 466273 := bbase (se 2 (by rfl) ⟨174852, by rfl⟩ : syracuseStep 466273 = 349705) (by norm_num)
theorem B466285 : Blo 405769 466285 := bbase (se 3 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 466285 = 174857) (by norm_num)
theorem B827005 : Blo 405769 827005 := bbase (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) (by norm_num)
theorem B466649 : Blo 405769 466649 := bbase (se 2 (by rfl) ⟨174993, by rfl⟩ : syracuseStep 466649 = 349987) (by norm_num)
theorem B3907349 : Blo 405769 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B433945 : Blo 405769 433945 := bbase (se 2 (by rfl) ⟨162729, by rfl⟩ : syracuseStep 433945 = 325459) (by norm_num)
theorem B466741 : Blo 405769 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B434017 : Blo 405769 434017 := bbase (se 2 (by rfl) ⟨162756, by rfl⟩ : syracuseStep 434017 = 325513) (by norm_num)
theorem B1056629 : Blo 405769 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B663437 : Blo 405769 663437 := bbase (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) (by norm_num)
theorem B434197 : Blo 405769 434197 := bbase (se 6 (by rfl) ⟨10176, by rfl⟩ : syracuseStep 434197 = 20353) (by norm_num)
theorem B1646741 : Blo 405769 1646741 := bbase (se 6 (by rfl) ⟨38595, by rfl⟩ : syracuseStep 1646741 = 77191) (by norm_num)
theorem B827605 : Blo 405769 827605 := bbase (se 7 (by rfl) ⟨9698, by rfl⟩ : syracuseStep 827605 = 19397) (by norm_num)
theorem B2072789 : Blo 405769 2072789 := bbase (se 7 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 2072789 = 48581) (by norm_num)
theorem B1548517 : Blo 405769 1548517 := bbase (se 4 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 1548517 = 290347) (by norm_num)
theorem B827653 : Blo 405769 827653 := bbase (se 4 (by rfl) ⟨77592, by rfl⟩ : syracuseStep 827653 = 155185) (by norm_num)
theorem B434641 : Blo 405769 434641 := bbase (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) (by norm_num)
theorem B1548821 : Blo 405769 1548821 := bbase (se 6 (by rfl) ⟨36300, by rfl⟩ : syracuseStep 1548821 = 72601) (by norm_num)
theorem B434765 : Blo 405769 434765 := bbase (se 3 (by rfl) ⟨81518, by rfl⟩ : syracuseStep 434765 = 163037) (by norm_num)
theorem B926357 : Blo 405769 926357 := bbase (se 6 (by rfl) ⟨21711, by rfl⟩ : syracuseStep 926357 = 43423) (by norm_num)
theorem B1745621 : Blo 405769 1745621 := bbase (se 7 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 1745621 = 40913) (by norm_num)
theorem B435017 : Blo 405769 435017 := bbase (se 2 (by rfl) ⟨163131, by rfl⟩ : syracuseStep 435017 = 326263) (by norm_num)
theorem B664789 : Blo 405769 664789 := bbase (se 7 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 664789 = 15581) (by norm_num)
theorem B435461 : Blo 405769 435461 := bbase (se 4 (by rfl) ⟨40824, by rfl⟩ : syracuseStep 435461 = 81649) (by norm_num)
theorem B664949 : Blo 405769 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B2074085 : Blo 405769 2074085 := bbase (se 4 (by rfl) ⟨194445, by rfl⟩ : syracuseStep 2074085 = 388891) (by norm_num)
theorem B435709 : Blo 405769 435709 := bbase (se 3 (by rfl) ⟨81695, by rfl⟩ : syracuseStep 435709 = 163391) (by norm_num)
theorem B1746629 : Blo 405769 1746629 := bbase (se 4 (by rfl) ⟨163746, by rfl⟩ : syracuseStep 1746629 = 327493) (by norm_num)
theorem B436153 : Blo 405769 436153 := bbase (se 2 (by rfl) ⟨163557, by rfl⟩ : syracuseStep 436153 = 327115) (by norm_num)
theorem B829397 : Blo 405769 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B436213 : Blo 405769 436213 := bbase (se 5 (by rfl) ⟨20447, by rfl⟩ : syracuseStep 436213 = 40895) (by norm_num)
theorem B6629525 : Blo 405769 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B436529 : Blo 405769 436529 := bbase (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) (by norm_num)
theorem B731597 : Blo 405769 731597 := bbase (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) (by norm_num)
theorem B1550933 : Blo 405769 1550933 := bbase (se 8 (by rfl) ⟨9087, by rfl⟩ : syracuseStep 1550933 = 18175) (by norm_num)
theorem B830069 : Blo 405769 830069 := bbase (se 5 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 830069 = 77819) (by norm_num)
theorem B2927285 : Blo 405769 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B436973 : Blo 405769 436973 := bbase (se 3 (by rfl) ⟨81932, by rfl⟩ : syracuseStep 436973 = 163865) (by norm_num)
theorem B437033 : Blo 405769 437033 := bbase (se 2 (by rfl) ⟨163887, by rfl⟩ : syracuseStep 437033 = 327775) (by norm_num)
theorem B1551221 : Blo 405769 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B6269845 : Blo 405769 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B437161 : Blo 405769 437161 := bbase (se 2 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 437161 = 327871) (by norm_num)
theorem B3091445 : Blo 405769 3091445 := bbase (se 5 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 3091445 = 289823) (by norm_num)
theorem B1158245 : Blo 405769 1158245 := bbase (se 4 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 1158245 = 217171) (by norm_num)
theorem B1027181 : Blo 405769 1027181 := bbase (se 3 (by rfl) ⟨192596, by rfl⟩ : syracuseStep 1027181 = 385193) (by norm_num)
theorem B1748405 : Blo 405769 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B1027525 : Blo 405769 1027525 := bbase (se 4 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 1027525 = 192661) (by norm_num)
theorem B1027637 : Blo 405769 1027637 := bbase (se 5 (by rfl) ⟨48170, by rfl⟩ : syracuseStep 1027637 = 96341) (by norm_num)
theorem B1027829 : Blo 405769 1027829 := bbase (se 5 (by rfl) ⟨48179, by rfl⟩ : syracuseStep 1027829 = 96359) (by norm_num)
theorem B1552405 : Blo 405769 1552405 := bbase (se 6 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 1552405 = 72769) (by norm_num)
theorem B1028173 : Blo 405769 1028173 := bbase (se 3 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 1028173 = 385565) (by norm_num)
theorem B1028285 : Blo 405769 1028285 := bbase (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) (by norm_num)
theorem B1159429 : Blo 405769 1159429 := bbase (se 4 (by rfl) ⟨108696, by rfl⟩ : syracuseStep 1159429 = 217393) (by norm_num)
theorem B1552709 : Blo 405769 1552709 := bbase (se 4 (by rfl) ⟨145566, by rfl⟩ : syracuseStep 1552709 = 291133) (by norm_num)
theorem B1028477 : Blo 405769 1028477 := bbase (se 3 (by rfl) ⟨192839, by rfl⟩ : syracuseStep 1028477 = 385679) (by norm_num)
theorem B1159589 : Blo 405769 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B930253 : Blo 405769 930253 := bbase (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) (by norm_num)
theorem B2142773 : Blo 405769 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B471685 : Blo 405769 471685 := bbase (se 4 (by rfl) ⟨44220, by rfl⟩ : syracuseStep 471685 = 88441) (by norm_num)
theorem B1159829 : Blo 405769 1159829 := bbase (se 6 (by rfl) ⟨27183, by rfl⟩ : syracuseStep 1159829 = 54367) (by norm_num)
theorem B1028821 : Blo 405769 1028821 := bbase (se 7 (by rfl) ⟨12056, by rfl⟩ : syracuseStep 1028821 = 24113) (by norm_num)
theorem B1028933 : Blo 405769 1028933 := bbase (se 4 (by rfl) ⟨96462, by rfl⟩ : syracuseStep 1028933 = 192925) (by norm_num)
theorem B1160021 : Blo 405769 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B1029125 : Blo 405769 1029125 := bbase (se 4 (by rfl) ⟨96480, by rfl⟩ : syracuseStep 1029125 = 192961) (by norm_num)
theorem B1029469 : Blo 405769 1029469 := bbase (se 3 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 1029469 = 386051) (by norm_num)
theorem B439741 : Blo 405769 439741 := bbase (se 3 (by rfl) ⟨82451, by rfl⟩ : syracuseStep 439741 = 164903) (by norm_num)
theorem B734653 : Blo 405769 734653 := bbase (se 3 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 734653 = 275495) (by norm_num)
theorem B1029581 : Blo 405769 1029581 := bbase (se 3 (by rfl) ⟨193046, by rfl⟩ : syracuseStep 1029581 = 386093) (by norm_num)
theorem B1029773 : Blo 405769 1029773 := bbase (se 3 (by rfl) ⟨193082, by rfl⟩ : syracuseStep 1029773 = 386165) (by norm_num)
theorem B3487445 : Blo 405769 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B1161013 : Blo 405769 1161013 := bbase (se 5 (by rfl) ⟨54422, by rfl⟩ : syracuseStep 1161013 = 108845) (by norm_num)
theorem B1030117 : Blo 405769 1030117 := bbase (se 4 (by rfl) ⟨96573, by rfl⟩ : syracuseStep 1030117 = 193147) (by norm_num)
theorem B1030229 : Blo 405769 1030229 := bbase (se 8 (by rfl) ⟨6036, by rfl⟩ : syracuseStep 1030229 = 12073) (by norm_num)
theorem B932077 : Blo 405769 932077 := bbase (se 3 (by rfl) ⟨174764, by rfl⟩ : syracuseStep 932077 = 349529) (by norm_num)
theorem B1030421 : Blo 405769 1030421 := bbase (se 6 (by rfl) ⟨24150, by rfl⟩ : syracuseStep 1030421 = 48301) (by norm_num)
theorem B4405589 : Blo 405769 4405589 := bbase (se 10 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 4405589 = 12907) (by norm_num)
theorem B1554821 : Blo 405769 1554821 := bbase (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) (by norm_num)
theorem B1030765 : Blo 405769 1030765 := bbase (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) (by norm_num)
theorem B866933 : Blo 405769 866933 := bbase (se 5 (by rfl) ⟨40637, by rfl⟩ : syracuseStep 866933 = 81275) (by norm_num)
theorem B1555109 : Blo 405769 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1030877 : Blo 405769 1030877 := bbase (se 3 (by rfl) ⟨193289, by rfl⟩ : syracuseStep 1030877 = 386579) (by norm_num)
theorem B1653605 : Blo 405769 1653605 := bbase (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) (by norm_num)
theorem B1162117 : Blo 405769 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B1031069 : Blo 405769 1031069 := bbase (se 3 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 1031069 = 386651) (by norm_num)
theorem B932789 : Blo 405769 932789 := bbase (se 5 (by rfl) ⟨43724, by rfl⟩ : syracuseStep 932789 = 87449) (by norm_num)
theorem B1391573 : Blo 405769 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B1653749 : Blo 405769 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B1031413 : Blo 405769 1031413 := bbase (se 5 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 1031413 = 96695) (by norm_num)
theorem B867685 : Blo 405769 867685 := bbase (se 4 (by rfl) ⟨81345, by rfl⟩ : syracuseStep 867685 = 162691) (by norm_num)
theorem B1031525 : Blo 405769 1031525 := bbase (se 4 (by rfl) ⟨96705, by rfl⟩ : syracuseStep 1031525 = 193411) (by norm_num)
theorem B867829 : Blo 405769 867829 := bbase (se 5 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 867829 = 81359) (by norm_num)
theorem B1031717 : Blo 405769 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B933445 : Blo 405769 933445 := bbase (se 4 (by rfl) ⟨87510, by rfl⟩ : syracuseStep 933445 = 175021) (by norm_num)
theorem B442013 : Blo 405769 442013 := bbase (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) (by norm_num)
theorem B868205 : Blo 405769 868205 := bbase (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) (by norm_num)
theorem B1032061 : Blo 405769 1032061 := bbase (se 3 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 1032061 = 387023) (by norm_num)
theorem B1032173 : Blo 405769 1032173 := bbase (se 3 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 1032173 = 387065) (by norm_num)
theorem B442433 : Blo 405769 442433 := bbase (se 2 (by rfl) ⟨165912, by rfl⟩ : syracuseStep 442433 = 331825) (by norm_num)
theorem B1032365 : Blo 405769 1032365 := bbase (se 3 (by rfl) ⟨193568, by rfl⟩ : syracuseStep 1032365 = 387137) (by norm_num)
theorem B868573 : Blo 405769 868573 := bbase (se 3 (by rfl) ⟨162857, by rfl⟩ : syracuseStep 868573 = 325715) (by norm_num)
theorem B1163621 : Blo 405769 1163621 := bbase (se 4 (by rfl) ⟨109089, by rfl⟩ : syracuseStep 1163621 = 218179) (by norm_num)
theorem B770485 : Blo 405769 770485 := bbase (se 5 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 770485 = 72233) (by norm_num)
theorem B3228149 : Blo 405769 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B1032709 : Blo 405769 1032709 := bbase (se 4 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 1032709 = 193633) (by norm_num)
theorem B7225877 : Blo 405769 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B770629 : Blo 405769 770629 := bbase (se 4 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 770629 = 144493) (by norm_num)
theorem B1032821 : Blo 405769 1032821 := bbase (se 5 (by rfl) ⟨48413, by rfl⟩ : syracuseStep 1032821 = 96827) (by norm_num)
theorem B934541 : Blo 405769 934541 := bbase (se 3 (by rfl) ⟨175226, by rfl⟩ : syracuseStep 934541 = 350453) (by norm_num)
theorem B1491605 : Blo 405769 1491605 := bbase (se 6 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 1491605 = 69919) (by norm_num)
theorem B770789 : Blo 405769 770789 := bbase (se 4 (by rfl) ⟨72261, by rfl⟩ : syracuseStep 770789 = 144523) (by norm_num)
theorem B738085 : Blo 405769 738085 := bbase (se 4 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 738085 = 138391) (by norm_num)
theorem B1033013 : Blo 405769 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B770933 : Blo 405769 770933 := bbase (se 5 (by rfl) ⟨36137, by rfl⟩ : syracuseStep 770933 = 72275) (by norm_num)
theorem B1524629 : Blo 405769 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B738229 : Blo 405769 738229 := bbase (se 5 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 738229 = 69209) (by norm_num)
theorem B738301 : Blo 405769 738301 := bbase (se 3 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 738301 = 276863) (by norm_num)
theorem B967717 : Blo 405769 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B1033357 : Blo 405769 1033357 := bbase (se 3 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 1033357 = 387509) (by norm_num)
theorem B771221 : Blo 405769 771221 := bbase (se 6 (by rfl) ⟨18075, by rfl⟩ : syracuseStep 771221 = 36151) (by norm_num)
theorem B1950965 : Blo 405769 1950965 := bbase (se 5 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 1950965 = 182903) (by norm_num)
theorem B1033469 : Blo 405769 1033469 := bbase (se 3 (by rfl) ⟨193775, by rfl⟩ : syracuseStep 1033469 = 387551) (by norm_num)
theorem B2606357 : Blo 405769 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B771373 : Blo 405769 771373 := bbase (se 3 (by rfl) ⟨144632, by rfl⟩ : syracuseStep 771373 = 289265) (by norm_num)
theorem B1033661 : Blo 405769 1033661 := bbase (se 3 (by rfl) ⟨193811, by rfl⟩ : syracuseStep 1033661 = 387623) (by norm_num)
theorem B2803157 : Blo 405769 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1590821 : Blo 405769 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B771677 : Blo 405769 771677 := bbase (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) (by norm_num)
theorem B870077 : Blo 405769 870077 := bbase (se 3 (by rfl) ⟨163139, by rfl⟩ : syracuseStep 870077 = 326279) (by norm_num)
theorem B4703957 : Blo 405769 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B411361 : Blo 405769 411361 := bbase (se 2 (by rfl) ⟨154260, by rfl⟩ : syracuseStep 411361 = 308521) (by norm_num)
theorem B1034005 : Blo 405769 1034005 := bbase (se 6 (by rfl) ⟨24234, by rfl⟩ : syracuseStep 1034005 = 48469) (by norm_num)
theorem B870221 : Blo 405769 870221 := bbase (se 3 (by rfl) ⟨163166, by rfl⟩ : syracuseStep 870221 = 326333) (by norm_num)
theorem B1034117 : Blo 405769 1034117 := bbase (se 4 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 1034117 = 193897) (by norm_num)
theorem B1165205 : Blo 405769 1165205 := bbase (se 6 (by rfl) ⟨27309, by rfl⟩ : syracuseStep 1165205 = 54619) (by norm_num)
theorem B411589 : Blo 405769 411589 := bbase (se 4 (by rfl) ⟨38586, by rfl⟩ : syracuseStep 411589 = 77173) (by norm_num)
theorem B4769813 : Blo 405769 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1034309 : Blo 405769 1034309 := bbase (se 4 (by rfl) ⟨96966, by rfl⟩ : syracuseStep 1034309 = 193933) (by norm_num)
theorem B870581 : Blo 405769 870581 := bbase (se 5 (by rfl) ⟨40808, by rfl⟩ : syracuseStep 870581 = 81617) (by norm_num)
theorem B2017493 : Blo 405769 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B411889 : Blo 405769 411889 := bbase (se 2 (by rfl) ⟨154458, by rfl⟩ : syracuseStep 411889 = 308917) (by norm_num)
theorem B772429 : Blo 405769 772429 := bbase (se 3 (by rfl) ⟨144830, by rfl⟩ : syracuseStep 772429 = 289661) (by norm_num)
theorem B608669 : Blo 405769 608669 := bbase (se 3 (by rfl) ⟨114125, by rfl⟩ : syracuseStep 608669 = 228251) (by norm_num)
theorem B1034653 : Blo 405769 1034653 := bbase (se 3 (by rfl) ⟨193997, by rfl⟩ : syracuseStep 1034653 = 387995) (by norm_num)
theorem B608693 : Blo 405769 608693 := bbase (se 5 (by rfl) ⟨28532, by rfl⟩ : syracuseStep 608693 = 57065) (by norm_num)
theorem B608717 : Blo 405769 608717 := bbase (se 3 (by rfl) ⟨114134, by rfl⟩ : syracuseStep 608717 = 228269) (by norm_num)
theorem B772573 : Blo 405769 772573 := bbase (se 3 (by rfl) ⟨144857, by rfl⟩ : syracuseStep 772573 = 289715) (by norm_num)
theorem B608741 : Blo 405769 608741 := bbase (se 4 (by rfl) ⟨57069, by rfl⟩ : syracuseStep 608741 = 114139) (by norm_num)
theorem B608765 : Blo 405769 608765 := bbase (se 3 (by rfl) ⟨114143, by rfl⟩ : syracuseStep 608765 = 228287) (by norm_num)
theorem B1034765 : Blo 405769 1034765 := bbase (se 3 (by rfl) ⟨194018, by rfl⟩ : syracuseStep 1034765 = 388037) (by norm_num)
theorem B608789 : Blo 405769 608789 := bbase (se 6 (by rfl) ⟨14268, by rfl⟩ : syracuseStep 608789 = 28537) (by norm_num)
theorem B608813 : Blo 405769 608813 := bbase (se 3 (by rfl) ⟨114152, by rfl⟩ : syracuseStep 608813 = 228305) (by norm_num)
theorem B1165877 : Blo 405769 1165877 := bbase (se 5 (by rfl) ⟨54650, by rfl⟩ : syracuseStep 1165877 = 109301) (by norm_num)
theorem B608837 : Blo 405769 608837 := bbase (se 4 (by rfl) ⟨57078, by rfl⟩ : syracuseStep 608837 = 114157) (by norm_num)
theorem B412237 : Blo 405769 412237 := bbase (se 3 (by rfl) ⟨77294, by rfl⟩ : syracuseStep 412237 = 154589) (by norm_num)
theorem B3099221 : Blo 405769 3099221 := bbase (se 8 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 3099221 = 36319) (by norm_num)
theorem B608861 : Blo 405769 608861 := bbase (se 3 (by rfl) ⟨114161, by rfl⟩ : syracuseStep 608861 = 228323) (by norm_num)
theorem B608885 : Blo 405769 608885 := bbase (se 5 (by rfl) ⟨28541, by rfl⟩ : syracuseStep 608885 = 57083) (by norm_num)
theorem B772733 : Blo 405769 772733 := bbase (se 3 (by rfl) ⟨144887, by rfl⟩ : syracuseStep 772733 = 289775) (by norm_num)
theorem B608909 : Blo 405769 608909 := bbase (se 3 (by rfl) ⟨114170, by rfl⟩ : syracuseStep 608909 = 228341) (by norm_num)
theorem B608933 : Blo 405769 608933 := bbase (se 4 (by rfl) ⟨57087, by rfl⟩ : syracuseStep 608933 = 114175) (by norm_num)
theorem B608957 : Blo 405769 608957 := bbase (se 3 (by rfl) ⟨114179, by rfl⟩ : syracuseStep 608957 = 228359) (by norm_num)
theorem B1034957 : Blo 405769 1034957 := bbase (se 3 (by rfl) ⟨194054, by rfl⟩ : syracuseStep 1034957 = 388109) (by norm_num)
theorem B608981 : Blo 405769 608981 := bbase (se 7 (by rfl) ⟨7136, by rfl⟩ : syracuseStep 608981 = 14273) (by norm_num)
theorem B609005 : Blo 405769 609005 := bbase (se 3 (by rfl) ⟨114188, by rfl⟩ : syracuseStep 609005 = 228377) (by norm_num)
theorem B609029 : Blo 405769 609029 := bbase (se 4 (by rfl) ⟨57096, by rfl⟩ : syracuseStep 609029 = 114193) (by norm_num)
theorem B772877 : Blo 405769 772877 := bbase (se 3 (by rfl) ⟨144914, by rfl⟩ : syracuseStep 772877 = 289829) (by norm_num)
theorem B2312981 : Blo 405769 2312981 := bbase (se 6 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 2312981 = 108421) (by norm_num)
theorem B609053 : Blo 405769 609053 := bbase (se 3 (by rfl) ⟨114197, by rfl⟩ : syracuseStep 609053 = 228395) (by norm_num)
theorem B609077 : Blo 405769 609077 := bbase (se 5 (by rfl) ⟨28550, by rfl⟩ : syracuseStep 609077 = 57101) (by norm_num)
theorem B609101 : Blo 405769 609101 := bbase (se 3 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 609101 = 228413) (by norm_num)
theorem B609125 : Blo 405769 609125 := bbase (se 4 (by rfl) ⟨57105, by rfl⟩ : syracuseStep 609125 = 114211) (by norm_num)
theorem B609149 : Blo 405769 609149 := bbase (se 3 (by rfl) ⟨114215, by rfl⟩ : syracuseStep 609149 = 228431) (by norm_num)
theorem B609173 : Blo 405769 609173 := bbase (se 6 (by rfl) ⟨14277, by rfl⟩ : syracuseStep 609173 = 28555) (by norm_num)
theorem B609197 : Blo 405769 609197 := bbase (se 3 (by rfl) ⟨114224, by rfl⟩ : syracuseStep 609197 = 228449) (by norm_num)
theorem B609221 : Blo 405769 609221 := bbase (se 4 (by rfl) ⟨57114, by rfl⟩ : syracuseStep 609221 = 114229) (by norm_num)
theorem B609245 : Blo 405769 609245 := bbase (se 3 (by rfl) ⟨114233, by rfl⟩ : syracuseStep 609245 = 228467) (by norm_num)
theorem B1166309 : Blo 405769 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B609269 : Blo 405769 609269 := bbase (se 5 (by rfl) ⟨28559, by rfl⟩ : syracuseStep 609269 = 57119) (by norm_num)
theorem B609293 : Blo 405769 609293 := bbase (se 3 (by rfl) ⟨114242, by rfl⟩ : syracuseStep 609293 = 228485) (by norm_num)
theorem B609317 : Blo 405769 609317 := bbase (se 4 (by rfl) ⟨57123, by rfl⟩ : syracuseStep 609317 = 114247) (by norm_num)
theorem B1035301 : Blo 405769 1035301 := bbase (se 4 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 1035301 = 194119) (by norm_num)
theorem B773165 : Blo 405769 773165 := bbase (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) (by norm_num)
theorem B871469 : Blo 405769 871469 := bbase (se 3 (by rfl) ⟨163400, by rfl⟩ : syracuseStep 871469 = 326801) (by norm_num)
theorem B609341 : Blo 405769 609341 := bbase (se 3 (by rfl) ⟨114251, by rfl⟩ : syracuseStep 609341 = 228503) (by norm_num)
theorem B609365 : Blo 405769 609365 := bbase (se 8 (by rfl) ⟨3570, by rfl⟩ : syracuseStep 609365 = 7141) (by norm_num)
theorem B609389 : Blo 405769 609389 := bbase (se 3 (by rfl) ⟨114260, by rfl⟩ : syracuseStep 609389 = 228521) (by norm_num)
theorem B609413 : Blo 405769 609413 := bbase (se 4 (by rfl) ⟨57132, by rfl⟩ : syracuseStep 609413 = 114265) (by norm_num)
theorem B1035413 : Blo 405769 1035413 := bbase (se 6 (by rfl) ⟨24267, by rfl⟩ : syracuseStep 1035413 = 48535) (by norm_num)
theorem B609437 : Blo 405769 609437 := bbase (se 3 (by rfl) ⟨114269, by rfl⟩ : syracuseStep 609437 = 228539) (by norm_num)
theorem B609461 : Blo 405769 609461 := bbase (se 5 (by rfl) ⟨28568, by rfl⟩ : syracuseStep 609461 = 57137) (by norm_num)
theorem B412853 : Blo 405769 412853 := bbase (se 5 (by rfl) ⟨19352, by rfl⟩ : syracuseStep 412853 = 38705) (by norm_num)
theorem B773317 : Blo 405769 773317 := bbase (se 4 (by rfl) ⟨72498, by rfl⟩ : syracuseStep 773317 = 144997) (by norm_num)
theorem B609485 : Blo 405769 609485 := bbase (se 3 (by rfl) ⟨114278, by rfl⟩ : syracuseStep 609485 = 228557) (by norm_num)
theorem B609509 : Blo 405769 609509 := bbase (se 4 (by rfl) ⟨57141, by rfl⟩ : syracuseStep 609509 = 114283) (by norm_num)
theorem B511213 : Blo 405769 511213 := bbase (se 3 (by rfl) ⟨95852, by rfl⟩ : syracuseStep 511213 = 191705) (by norm_num)
theorem B609533 : Blo 405769 609533 := bbase (se 3 (by rfl) ⟨114287, by rfl⟩ : syracuseStep 609533 = 228575) (by norm_num)
theorem B609557 : Blo 405769 609557 := bbase (se 6 (by rfl) ⟨14286, by rfl⟩ : syracuseStep 609557 = 28573) (by norm_num)
theorem B871717 : Blo 405769 871717 := bbase (se 4 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 871717 = 163447) (by norm_num)
theorem B609581 : Blo 405769 609581 := bbase (se 3 (by rfl) ⟨114296, by rfl⟩ : syracuseStep 609581 = 228593) (by norm_num)
theorem B609605 : Blo 405769 609605 := bbase (se 4 (by rfl) ⟨57150, by rfl⟩ : syracuseStep 609605 = 114301) (by norm_num)
theorem B1035605 : Blo 405769 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B609629 : Blo 405769 609629 := bbase (se 3 (by rfl) ⟨114305, by rfl⟩ : syracuseStep 609629 = 228611) (by norm_num)
theorem B609653 : Blo 405769 609653 := bbase (se 5 (by rfl) ⟨28577, by rfl⟩ : syracuseStep 609653 = 57155) (by norm_num)
theorem B609677 : Blo 405769 609677 := bbase (se 3 (by rfl) ⟨114314, by rfl⟩ : syracuseStep 609677 = 228629) (by norm_num)
theorem B609701 : Blo 405769 609701 := bbase (se 4 (by rfl) ⟨57159, by rfl⟩ : syracuseStep 609701 = 114319) (by norm_num)
theorem B609725 : Blo 405769 609725 := bbase (se 3 (by rfl) ⟨114323, by rfl⟩ : syracuseStep 609725 = 228647) (by norm_num)
theorem B609749 : Blo 405769 609749 := bbase (se 7 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 609749 = 14291) (by norm_num)
theorem B609773 : Blo 405769 609773 := bbase (se 3 (by rfl) ⟨114332, by rfl⟩ : syracuseStep 609773 = 228665) (by norm_num)
theorem B773621 : Blo 405769 773621 := bbase (se 5 (by rfl) ⟨36263, by rfl⟩ : syracuseStep 773621 = 72527) (by norm_num)
theorem B609797 : Blo 405769 609797 := bbase (se 4 (by rfl) ⟨57168, by rfl⟩ : syracuseStep 609797 = 114337) (by norm_num)
theorem B609821 : Blo 405769 609821 := bbase (se 3 (by rfl) ⟨114341, by rfl⟩ : syracuseStep 609821 = 228683) (by norm_num)
theorem B609845 : Blo 405769 609845 := bbase (se 5 (by rfl) ⟨28586, by rfl⟩ : syracuseStep 609845 = 57173) (by norm_num)
theorem B609869 : Blo 405769 609869 := bbase (se 3 (by rfl) ⟨114350, by rfl⟩ : syracuseStep 609869 = 228701) (by norm_num)
theorem B609893 : Blo 405769 609893 := bbase (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) (by norm_num)
theorem B609917 : Blo 405769 609917 := bbase (se 3 (by rfl) ⟨114359, by rfl⟩ : syracuseStep 609917 = 228719) (by norm_num)
theorem B609941 : Blo 405769 609941 := bbase (se 6 (by rfl) ⟨14295, by rfl⟩ : syracuseStep 609941 = 28591) (by norm_num)
theorem B609965 : Blo 405769 609965 := bbase (se 3 (by rfl) ⟨114368, by rfl⟩ : syracuseStep 609965 = 228737) (by norm_num)
theorem B1035949 : Blo 405769 1035949 := bbase (se 3 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 1035949 = 388481) (by norm_num)
theorem B609989 : Blo 405769 609989 := bbase (se 4 (by rfl) ⟨57186, by rfl⟩ : syracuseStep 609989 = 114373) (by norm_num)
theorem B610013 : Blo 405769 610013 := bbase (se 3 (by rfl) ⟨114377, by rfl⟩ : syracuseStep 610013 = 228755) (by norm_num)
theorem B610037 : Blo 405769 610037 := bbase (se 5 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 610037 = 57191) (by norm_num)
theorem B610061 : Blo 405769 610061 := bbase (se 3 (by rfl) ⟨114386, by rfl⟩ : syracuseStep 610061 = 228773) (by norm_num)
theorem B872221 : Blo 405769 872221 := bbase (se 3 (by rfl) ⟨163541, by rfl⟩ : syracuseStep 872221 = 327083) (by norm_num)
theorem B1036061 : Blo 405769 1036061 := bbase (se 3 (by rfl) ⟨194261, by rfl⟩ : syracuseStep 1036061 = 388523) (by norm_num)
theorem B610085 : Blo 405769 610085 := bbase (se 4 (by rfl) ⟨57195, by rfl⟩ : syracuseStep 610085 = 114391) (by norm_num)
theorem B610109 : Blo 405769 610109 := bbase (se 3 (by rfl) ⟨114395, by rfl⟩ : syracuseStep 610109 = 228791) (by norm_num)
theorem B610133 : Blo 405769 610133 := bbase (se 9 (by rfl) ⟨1787, by rfl⟩ : syracuseStep 610133 = 3575) (by norm_num)
theorem B610157 : Blo 405769 610157 := bbase (se 3 (by rfl) ⟨114404, by rfl⟩ : syracuseStep 610157 = 228809) (by norm_num)
theorem B610181 : Blo 405769 610181 := bbase (se 4 (by rfl) ⟨57204, by rfl⟩ : syracuseStep 610181 = 114409) (by norm_num)
theorem B610205 : Blo 405769 610205 := bbase (se 3 (by rfl) ⟨114413, by rfl⟩ : syracuseStep 610205 = 228827) (by norm_num)
theorem B610229 : Blo 405769 610229 := bbase (se 5 (by rfl) ⟨28604, by rfl⟩ : syracuseStep 610229 = 57209) (by norm_num)
theorem B610253 : Blo 405769 610253 := bbase (se 3 (by rfl) ⟨114422, by rfl⟩ : syracuseStep 610253 = 228845) (by norm_num)
theorem B1036253 : Blo 405769 1036253 := bbase (se 3 (by rfl) ⟨194297, by rfl⟩ : syracuseStep 1036253 = 388595) (by norm_num)
theorem B610277 : Blo 405769 610277 := bbase (se 4 (by rfl) ⟨57213, by rfl⟩ : syracuseStep 610277 = 114427) (by norm_num)
theorem B610301 : Blo 405769 610301 := bbase (se 3 (by rfl) ⟨114431, by rfl⟩ : syracuseStep 610301 = 228863) (by norm_num)
theorem B610325 : Blo 405769 610325 := bbase (se 6 (by rfl) ⟨14304, by rfl⟩ : syracuseStep 610325 = 28609) (by norm_num)
theorem B610349 : Blo 405769 610349 := bbase (se 3 (by rfl) ⟨114440, by rfl⟩ : syracuseStep 610349 = 228881) (by norm_num)
theorem B610373 : Blo 405769 610373 := bbase (se 4 (by rfl) ⟨57222, by rfl⟩ : syracuseStep 610373 = 114445) (by norm_num)
theorem B610397 : Blo 405769 610397 := bbase (se 3 (by rfl) ⟨114449, by rfl⟩ : syracuseStep 610397 = 228899) (by norm_num)
theorem B610421 : Blo 405769 610421 := bbase (se 5 (by rfl) ⟨28613, by rfl⟩ : syracuseStep 610421 = 57227) (by norm_num)
theorem B610445 : Blo 405769 610445 := bbase (se 3 (by rfl) ⟨114458, by rfl⟩ : syracuseStep 610445 = 228917) (by norm_num)
theorem B610469 : Blo 405769 610469 := bbase (se 4 (by rfl) ⟨57231, by rfl⟩ : syracuseStep 610469 = 114463) (by norm_num)
theorem B2609333 : Blo 405769 2609333 := bbase (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) (by norm_num)
theorem B610493 : Blo 405769 610493 := bbase (se 3 (by rfl) ⟨114467, by rfl⟩ : syracuseStep 610493 = 228935) (by norm_num)
theorem B610517 : Blo 405769 610517 := bbase (se 7 (by rfl) ⟨7154, by rfl⟩ : syracuseStep 610517 = 14309) (by norm_num)
theorem B774373 : Blo 405769 774373 := bbase (se 4 (by rfl) ⟨72597, by rfl⟩ : syracuseStep 774373 = 145195) (by norm_num)
theorem B610541 : Blo 405769 610541 := bbase (se 3 (by rfl) ⟨114476, by rfl⟩ : syracuseStep 610541 = 228953) (by norm_num)
theorem B610565 : Blo 405769 610565 := bbase (se 4 (by rfl) ⟨57240, by rfl⟩ : syracuseStep 610565 = 114481) (by norm_num)
theorem B610589 : Blo 405769 610589 := bbase (se 3 (by rfl) ⟨114485, by rfl⟩ : syracuseStep 610589 = 228971) (by norm_num)
theorem B610613 : Blo 405769 610613 := bbase (se 5 (by rfl) ⟨28622, by rfl⟩ : syracuseStep 610613 = 57245) (by norm_num)
theorem B1036597 : Blo 405769 1036597 := bbase (se 5 (by rfl) ⟨48590, by rfl⟩ : syracuseStep 1036597 = 97181) (by norm_num)
theorem B610637 : Blo 405769 610637 := bbase (se 3 (by rfl) ⟨114494, by rfl⟩ : syracuseStep 610637 = 228989) (by norm_num)
theorem B610661 : Blo 405769 610661 := bbase (se 4 (by rfl) ⟨57249, by rfl⟩ : syracuseStep 610661 = 114499) (by norm_num)
theorem B774517 : Blo 405769 774517 := bbase (se 5 (by rfl) ⟨36305, by rfl⟩ : syracuseStep 774517 = 72611) (by norm_num)
theorem B610685 : Blo 405769 610685 := bbase (se 3 (by rfl) ⟨114503, by rfl⟩ : syracuseStep 610685 = 229007) (by norm_num)
theorem B610709 : Blo 405769 610709 := bbase (se 6 (by rfl) ⟨14313, by rfl⟩ : syracuseStep 610709 = 28627) (by norm_num)
theorem B1036709 : Blo 405769 1036709 := bbase (se 4 (by rfl) ⟨97191, by rfl⟩ : syracuseStep 1036709 = 194383) (by norm_num)
theorem B610733 : Blo 405769 610733 := bbase (se 3 (by rfl) ⟨114512, by rfl⟩ : syracuseStep 610733 = 229025) (by norm_num)
theorem B610757 : Blo 405769 610757 := bbase (se 4 (by rfl) ⟨57258, by rfl⟩ : syracuseStep 610757 = 114517) (by norm_num)
theorem B610781 : Blo 405769 610781 := bbase (se 3 (by rfl) ⟨114521, by rfl⟩ : syracuseStep 610781 = 229043) (by norm_num)
theorem B578029 : Blo 405769 578029 := bbase (se 3 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 578029 = 216761) (by norm_num)
theorem B610805 : Blo 405769 610805 := bbase (se 5 (by rfl) ⟨28631, by rfl⟩ : syracuseStep 610805 = 57263) (by norm_num)
theorem B610829 : Blo 405769 610829 := bbase (se 3 (by rfl) ⟨114530, by rfl⟩ : syracuseStep 610829 = 229061) (by norm_num)
theorem B774677 : Blo 405769 774677 := bbase (se 6 (by rfl) ⟨18156, by rfl⟩ : syracuseStep 774677 = 36313) (by norm_num)
theorem B610853 : Blo 405769 610853 := bbase (se 4 (by rfl) ⟨57267, by rfl⟩ : syracuseStep 610853 = 114535) (by norm_num)
theorem B610877 : Blo 405769 610877 := bbase (se 3 (by rfl) ⟨114539, by rfl⟩ : syracuseStep 610877 = 229079) (by norm_num)
theorem B610901 : Blo 405769 610901 := bbase (se 8 (by rfl) ⟨3579, by rfl⟩ : syracuseStep 610901 = 7159) (by norm_num)
theorem B971365 : Blo 405769 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B1036901 : Blo 405769 1036901 := bbase (se 4 (by rfl) ⟨97209, by rfl⟩ : syracuseStep 1036901 = 194419) (by norm_num)
theorem B610925 : Blo 405769 610925 := bbase (se 3 (by rfl) ⟨114548, by rfl⟩ : syracuseStep 610925 = 229097) (by norm_num)
theorem B610949 : Blo 405769 610949 := bbase (se 4 (by rfl) ⟨57276, by rfl⟩ : syracuseStep 610949 = 114553) (by norm_num)
theorem B873109 : Blo 405769 873109 := bbase (se 6 (by rfl) ⟨20463, by rfl⟩ : syracuseStep 873109 = 40927) (by norm_num)
theorem B610973 : Blo 405769 610973 := bbase (se 3 (by rfl) ⟨114557, by rfl⟩ : syracuseStep 610973 = 229115) (by norm_num)
theorem B774821 : Blo 405769 774821 := bbase (se 4 (by rfl) ⟨72639, by rfl⟩ : syracuseStep 774821 = 145279) (by norm_num)
theorem B610997 : Blo 405769 610997 := bbase (se 5 (by rfl) ⟨28640, by rfl⟩ : syracuseStep 610997 = 57281) (by norm_num)
theorem B611021 : Blo 405769 611021 := bbase (se 3 (by rfl) ⟨114566, by rfl⟩ : syracuseStep 611021 = 229133) (by norm_num)
theorem B611045 : Blo 405769 611045 := bbase (se 4 (by rfl) ⟨57285, by rfl⟩ : syracuseStep 611045 = 114571) (by norm_num)
theorem B611069 : Blo 405769 611069 := bbase (se 3 (by rfl) ⟨114575, by rfl⟩ : syracuseStep 611069 = 229151) (by norm_num)
theorem B1659653 : Blo 405769 1659653 := bbase (se 4 (by rfl) ⟨155592, by rfl⟩ : syracuseStep 1659653 = 311185) (by norm_num)
theorem B611093 : Blo 405769 611093 := bbase (se 6 (by rfl) ⟨14322, by rfl⟩ : syracuseStep 611093 = 28645) (by norm_num)
theorem B611117 : Blo 405769 611117 := bbase (se 3 (by rfl) ⟨114584, by rfl⟩ : syracuseStep 611117 = 229169) (by norm_num)
theorem B611141 : Blo 405769 611141 := bbase (se 4 (by rfl) ⟨57294, by rfl⟩ : syracuseStep 611141 = 114589) (by norm_num)
theorem B611165 : Blo 405769 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B611189 : Blo 405769 611189 := bbase (se 5 (by rfl) ⟨28649, by rfl⟩ : syracuseStep 611189 = 57299) (by norm_num)
theorem B611213 : Blo 405769 611213 := bbase (se 3 (by rfl) ⟨114602, by rfl⟩ : syracuseStep 611213 = 229205) (by norm_num)
theorem B611237 : Blo 405769 611237 := bbase (se 4 (by rfl) ⟨57303, by rfl⟩ : syracuseStep 611237 = 114607) (by norm_num)
theorem B611261 : Blo 405769 611261 := bbase (se 3 (by rfl) ⟨114611, by rfl⟩ : syracuseStep 611261 = 229223) (by norm_num)
theorem B775109 : Blo 405769 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B611285 : Blo 405769 611285 := bbase (se 7 (by rfl) ⟨7163, by rfl⟩ : syracuseStep 611285 = 14327) (by norm_num)
theorem B611309 : Blo 405769 611309 := bbase (se 3 (by rfl) ⟨114620, by rfl⟩ : syracuseStep 611309 = 229241) (by norm_num)
theorem B611333 : Blo 405769 611333 := bbase (se 4 (by rfl) ⟨57312, by rfl⟩ : syracuseStep 611333 = 114625) (by norm_num)
theorem B611357 : Blo 405769 611357 := bbase (se 3 (by rfl) ⟨114629, by rfl⟩ : syracuseStep 611357 = 229259) (by norm_num)
theorem B611381 : Blo 405769 611381 := bbase (se 5 (by rfl) ⟨28658, by rfl⟩ : syracuseStep 611381 = 57317) (by norm_num)
theorem B578621 : Blo 405769 578621 := bbase (se 3 (by rfl) ⟨108491, by rfl⟩ : syracuseStep 578621 = 216983) (by norm_num)
theorem B611405 : Blo 405769 611405 := bbase (se 3 (by rfl) ⟨114638, by rfl⟩ : syracuseStep 611405 = 229277) (by norm_num)
theorem B775261 : Blo 405769 775261 := bbase (se 3 (by rfl) ⟨145361, by rfl⟩ : syracuseStep 775261 = 290723) (by norm_num)
theorem B611429 : Blo 405769 611429 := bbase (se 4 (by rfl) ⟨57321, by rfl⟩ : syracuseStep 611429 = 114643) (by norm_num)
theorem B611453 : Blo 405769 611453 := bbase (se 3 (by rfl) ⟨114647, by rfl⟩ : syracuseStep 611453 = 229295) (by norm_num)
theorem B873605 : Blo 405769 873605 := bbase (se 4 (by rfl) ⟨81900, by rfl⟩ : syracuseStep 873605 = 163801) (by norm_num)
theorem B578701 : Blo 405769 578701 := bbase (se 3 (by rfl) ⟨108506, by rfl⟩ : syracuseStep 578701 = 217013) (by norm_num)
theorem B611477 : Blo 405769 611477 := bbase (se 6 (by rfl) ⟨14331, by rfl⟩ : syracuseStep 611477 = 28663) (by norm_num)
theorem B611501 : Blo 405769 611501 := bbase (se 3 (by rfl) ⟨114656, by rfl⟩ : syracuseStep 611501 = 229313) (by norm_num)
theorem B611525 : Blo 405769 611525 := bbase (se 4 (by rfl) ⟨57330, by rfl⟩ : syracuseStep 611525 = 114661) (by norm_num)
theorem B611549 : Blo 405769 611549 := bbase (se 3 (by rfl) ⟨114665, by rfl⟩ : syracuseStep 611549 = 229331) (by norm_num)
theorem B611573 : Blo 405769 611573 := bbase (se 5 (by rfl) ⟨28667, by rfl⟩ : syracuseStep 611573 = 57335) (by norm_num)
theorem B578821 : Blo 405769 578821 := bbase (se 4 (by rfl) ⟨54264, by rfl⟩ : syracuseStep 578821 = 108529) (by norm_num)
theorem B611597 : Blo 405769 611597 := bbase (se 3 (by rfl) ⟨114674, by rfl⟩ : syracuseStep 611597 = 229349) (by norm_num)
theorem B611621 : Blo 405769 611621 := bbase (se 4 (by rfl) ⟨57339, by rfl⟩ : syracuseStep 611621 = 114679) (by norm_num)
theorem B611645 : Blo 405769 611645 := bbase (se 3 (by rfl) ⟨114683, by rfl⟩ : syracuseStep 611645 = 229367) (by norm_num)
theorem B611669 : Blo 405769 611669 := bbase (se 18 (by rfl) ⟨3, by rfl⟩ : syracuseStep 611669 = 7) (by norm_num)
theorem B578917 : Blo 405769 578917 := bbase (se 4 (by rfl) ⟨54273, by rfl⟩ : syracuseStep 578917 = 108547) (by norm_num)
theorem B611693 : Blo 405769 611693 := bbase (se 3 (by rfl) ⟨114692, by rfl⟩ : syracuseStep 611693 = 229385) (by norm_num)
theorem B611717 : Blo 405769 611717 := bbase (se 4 (by rfl) ⟨57348, by rfl⟩ : syracuseStep 611717 = 114697) (by norm_num)
theorem B775565 : Blo 405769 775565 := bbase (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) (by norm_num)
theorem B611741 : Blo 405769 611741 := bbase (se 3 (by rfl) ⟨114701, by rfl⟩ : syracuseStep 611741 = 229403) (by norm_num)
theorem B611765 : Blo 405769 611765 := bbase (se 5 (by rfl) ⟨28676, by rfl⟩ : syracuseStep 611765 = 57353) (by norm_num)
theorem B1955269 : Blo 405769 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B611789 : Blo 405769 611789 := bbase (se 3 (by rfl) ⟨114710, by rfl⟩ : syracuseStep 611789 = 229421) (by norm_num)
theorem B611813 : Blo 405769 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B611837 : Blo 405769 611837 := bbase (se 3 (by rfl) ⟨114719, by rfl⟩ : syracuseStep 611837 = 229439) (by norm_num)
theorem B1299989 : Blo 405769 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B611861 : Blo 405769 611861 := bbase (se 6 (by rfl) ⟨14340, by rfl⟩ : syracuseStep 611861 = 28681) (by norm_num)
theorem B611885 : Blo 405769 611885 := bbase (se 3 (by rfl) ⟨114728, by rfl⟩ : syracuseStep 611885 = 229457) (by norm_num)
theorem B611909 : Blo 405769 611909 := bbase (se 4 (by rfl) ⟨57366, by rfl⟩ : syracuseStep 611909 = 114733) (by norm_num)
theorem B611933 : Blo 405769 611933 := bbase (se 3 (by rfl) ⟨114737, by rfl⟩ : syracuseStep 611933 = 229475) (by norm_num)
theorem B513641 : Blo 405769 513641 := bbase (se 2 (by rfl) ⟨192615, by rfl⟩ : syracuseStep 513641 = 385231) (by norm_num)
theorem B611957 : Blo 405769 611957 := bbase (se 5 (by rfl) ⟨28685, by rfl⟩ : syracuseStep 611957 = 57371) (by norm_num)
theorem B611981 : Blo 405769 611981 := bbase (se 3 (by rfl) ⟨114746, by rfl⟩ : syracuseStep 611981 = 229493) (by norm_num)
theorem B513697 : Blo 405769 513697 := bbase (se 2 (by rfl) ⟨192636, by rfl⟩ : syracuseStep 513697 = 385273) (by norm_num)
theorem B612005 : Blo 405769 612005 := bbase (se 4 (by rfl) ⟨57375, by rfl⟩ : syracuseStep 612005 = 114751) (by norm_num)
theorem B612029 : Blo 405769 612029 := bbase (se 3 (by rfl) ⟨114755, by rfl⟩ : syracuseStep 612029 = 229511) (by norm_num)
theorem B612053 : Blo 405769 612053 := bbase (se 7 (by rfl) ⟨7172, by rfl⟩ : syracuseStep 612053 = 14345) (by norm_num)
theorem B612077 : Blo 405769 612077 := bbase (se 3 (by rfl) ⟨114764, by rfl⟩ : syracuseStep 612077 = 229529) (by norm_num)
theorem B513793 : Blo 405769 513793 := bbase (se 2 (by rfl) ⟨192672, by rfl⟩ : syracuseStep 513793 = 385345) (by norm_num)
theorem B612101 : Blo 405769 612101 := bbase (se 4 (by rfl) ⟨57384, by rfl⟩ : syracuseStep 612101 = 114769) (by norm_num)
theorem B612125 : Blo 405769 612125 := bbase (se 3 (by rfl) ⟨114773, by rfl⟩ : syracuseStep 612125 = 229547) (by norm_num)
theorem B612149 : Blo 405769 612149 := bbase (se 5 (by rfl) ⟨28694, by rfl⟩ : syracuseStep 612149 = 57389) (by norm_num)
theorem B612173 : Blo 405769 612173 := bbase (se 3 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 612173 = 229565) (by norm_num)
theorem B579413 : Blo 405769 579413 := bbase (se 9 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 579413 = 3395) (by norm_num)
theorem B1103701 : Blo 405769 1103701 := bbase (se 9 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 1103701 = 6467) (by norm_num)
theorem B612197 : Blo 405769 612197 := bbase (se 4 (by rfl) ⟨57393, by rfl⟩ : syracuseStep 612197 = 114787) (by norm_num)
theorem B612221 : Blo 405769 612221 := bbase (se 3 (by rfl) ⟨114791, by rfl⟩ : syracuseStep 612221 = 229583) (by norm_num)
theorem B612245 : Blo 405769 612245 := bbase (se 6 (by rfl) ⟨14349, by rfl⟩ : syracuseStep 612245 = 28699) (by norm_num)
theorem B513965 : Blo 405769 513965 := bbase (se 3 (by rfl) ⟨96368, by rfl⟩ : syracuseStep 513965 = 192737) (by norm_num)
theorem B612269 : Blo 405769 612269 := bbase (se 3 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 612269 = 229601) (by norm_num)
theorem B1103797 : Blo 405769 1103797 := bbase (se 5 (by rfl) ⟨51740, by rfl⟩ : syracuseStep 1103797 = 103481) (by norm_num)
theorem B612293 : Blo 405769 612293 := bbase (se 4 (by rfl) ⟨57402, by rfl⟩ : syracuseStep 612293 = 114805) (by norm_num)
theorem B612317 : Blo 405769 612317 := bbase (se 3 (by rfl) ⟨114809, by rfl⟩ : syracuseStep 612317 = 229619) (by norm_num)
theorem B514021 : Blo 405769 514021 := bbase (se 4 (by rfl) ⟨48189, by rfl⟩ : syracuseStep 514021 = 96379) (by norm_num)
theorem B612341 : Blo 405769 612341 := bbase (se 5 (by rfl) ⟨28703, by rfl⟩ : syracuseStep 612341 = 57407) (by norm_num)
theorem B874493 : Blo 405769 874493 := bbase (se 3 (by rfl) ⟨163967, by rfl⟩ : syracuseStep 874493 = 327935) (by norm_num)
theorem B612365 : Blo 405769 612365 := bbase (se 3 (by rfl) ⟨114818, by rfl⟩ : syracuseStep 612365 = 229637) (by norm_num)
theorem B612389 : Blo 405769 612389 := bbase (se 4 (by rfl) ⟨57411, by rfl⟩ : syracuseStep 612389 = 114823) (by norm_num)
theorem B612413 : Blo 405769 612413 := bbase (se 3 (by rfl) ⟨114827, by rfl⟩ : syracuseStep 612413 = 229655) (by norm_num)
theorem B514117 : Blo 405769 514117 := bbase (se 4 (by rfl) ⟨48198, by rfl⟩ : syracuseStep 514117 = 96397) (by norm_num)
theorem B2480213 : Blo 405769 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B612437 : Blo 405769 612437 := bbase (se 8 (by rfl) ⟨3588, by rfl⟩ : syracuseStep 612437 = 7177) (by norm_num)
theorem B612461 : Blo 405769 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B874613 : Blo 405769 874613 := bbase (se 5 (by rfl) ⟨40997, by rfl⟩ : syracuseStep 874613 = 81995) (by norm_num)
theorem B776317 : Blo 405769 776317 := bbase (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) (by norm_num)
theorem B612485 : Blo 405769 612485 := bbase (se 4 (by rfl) ⟨57420, by rfl⟩ : syracuseStep 612485 = 114841) (by norm_num)
theorem B612509 : Blo 405769 612509 := bbase (se 3 (by rfl) ⟨114845, by rfl⟩ : syracuseStep 612509 = 229691) (by norm_num)
theorem B612533 : Blo 405769 612533 := bbase (se 5 (by rfl) ⟨28712, by rfl⟩ : syracuseStep 612533 = 57425) (by norm_num)
theorem B612557 : Blo 405769 612557 := bbase (se 3 (by rfl) ⟨114854, by rfl⟩ : syracuseStep 612557 = 229709) (by norm_num)
theorem B612581 : Blo 405769 612581 := bbase (se 4 (by rfl) ⟨57429, by rfl⟩ : syracuseStep 612581 = 114859) (by norm_num)
theorem B514289 : Blo 405769 514289 := bbase (se 2 (by rfl) ⟨192858, by rfl⟩ : syracuseStep 514289 = 385717) (by norm_num)
theorem B612605 : Blo 405769 612605 := bbase (se 3 (by rfl) ⟨114863, by rfl⟩ : syracuseStep 612605 = 229727) (by norm_num)
theorem B776461 : Blo 405769 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B612629 : Blo 405769 612629 := bbase (se 6 (by rfl) ⟨14358, by rfl⟩ : syracuseStep 612629 = 28717) (by norm_num)
theorem B514345 : Blo 405769 514345 := bbase (se 2 (by rfl) ⟨192879, by rfl⟩ : syracuseStep 514345 = 385759) (by norm_num)
theorem B612653 : Blo 405769 612653 := bbase (se 3 (by rfl) ⟨114872, by rfl⟩ : syracuseStep 612653 = 229745) (by norm_num)
theorem B612677 : Blo 405769 612677 := bbase (se 4 (by rfl) ⟨57438, by rfl⟩ : syracuseStep 612677 = 114877) (by norm_num)
theorem B612701 : Blo 405769 612701 := bbase (se 3 (by rfl) ⟨114881, by rfl⟩ : syracuseStep 612701 = 229763) (by norm_num)
theorem B612725 : Blo 405769 612725 := bbase (se 5 (by rfl) ⟨28721, by rfl⟩ : syracuseStep 612725 = 57443) (by norm_num)
theorem B579965 : Blo 405769 579965 := bbase (se 3 (by rfl) ⟨108743, by rfl⟩ : syracuseStep 579965 = 217487) (by norm_num)
theorem B514441 : Blo 405769 514441 := bbase (se 2 (by rfl) ⟨192915, by rfl⟩ : syracuseStep 514441 = 385831) (by norm_num)
theorem B612749 : Blo 405769 612749 := bbase (se 3 (by rfl) ⟨114890, by rfl⟩ : syracuseStep 612749 = 229781) (by norm_num)
theorem B612773 : Blo 405769 612773 := bbase (se 4 (by rfl) ⟨57447, by rfl⟩ : syracuseStep 612773 = 114895) (by norm_num)
theorem B776621 : Blo 405769 776621 := bbase (se 3 (by rfl) ⟨145616, by rfl⟩ : syracuseStep 776621 = 291233) (by norm_num)
theorem B612797 : Blo 405769 612797 := bbase (se 3 (by rfl) ⟨114899, by rfl⟩ : syracuseStep 612797 = 229799) (by norm_num)
theorem B612821 : Blo 405769 612821 := bbase (se 7 (by rfl) ⟨7181, by rfl⟩ : syracuseStep 612821 = 14363) (by norm_num)
theorem B612845 : Blo 405769 612845 := bbase (se 3 (by rfl) ⟨114908, by rfl⟩ : syracuseStep 612845 = 229817) (by norm_num)
theorem B2054645 : Blo 405769 2054645 := bbase (se 5 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 2054645 = 192623) (by norm_num)
theorem B612869 : Blo 405769 612869 := bbase (se 4 (by rfl) ⟨57456, by rfl⟩ : syracuseStep 612869 = 114913) (by norm_num)
theorem B612893 : Blo 405769 612893 := bbase (se 3 (by rfl) ⟨114917, by rfl⟩ : syracuseStep 612893 = 229835) (by norm_num)
theorem B514613 : Blo 405769 514613 := bbase (se 5 (by rfl) ⟨24122, by rfl⟩ : syracuseStep 514613 = 48245) (by norm_num)
theorem B612917 : Blo 405769 612917 := bbase (se 5 (by rfl) ⟨28730, by rfl⟩ : syracuseStep 612917 = 57461) (by norm_num)
theorem B776765 : Blo 405769 776765 := bbase (se 3 (by rfl) ⟨145643, by rfl⟩ : syracuseStep 776765 = 291287) (by norm_num)
theorem B612941 : Blo 405769 612941 := bbase (se 3 (by rfl) ⟨114926, by rfl⟩ : syracuseStep 612941 = 229853) (by norm_num)
theorem B612965 : Blo 405769 612965 := bbase (se 4 (by rfl) ⟨57465, by rfl⟩ : syracuseStep 612965 = 114931) (by norm_num)
theorem B514669 : Blo 405769 514669 := bbase (se 3 (by rfl) ⟨96500, by rfl⟩ : syracuseStep 514669 = 193001) (by norm_num)
theorem B612989 : Blo 405769 612989 := bbase (se 3 (by rfl) ⟨114935, by rfl⟩ : syracuseStep 612989 = 229871) (by norm_num)
theorem B613013 : Blo 405769 613013 := bbase (se 6 (by rfl) ⟨14367, by rfl⟩ : syracuseStep 613013 = 28735) (by norm_num)
theorem B613037 : Blo 405769 613037 := bbase (se 3 (by rfl) ⟨114944, by rfl⟩ : syracuseStep 613037 = 229889) (by norm_num)
theorem B613061 : Blo 405769 613061 := bbase (se 4 (by rfl) ⟨57474, by rfl⟩ : syracuseStep 613061 = 114949) (by norm_num)
theorem B514765 : Blo 405769 514765 := bbase (se 3 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 514765 = 193037) (by norm_num)
theorem B613085 : Blo 405769 613085 := bbase (se 3 (by rfl) ⟨114953, by rfl⟩ : syracuseStep 613085 = 229907) (by norm_num)
theorem B613109 : Blo 405769 613109 := bbase (se 5 (by rfl) ⟨28739, by rfl⟩ : syracuseStep 613109 = 57479) (by norm_num)
theorem B613133 : Blo 405769 613133 := bbase (se 3 (by rfl) ⟨114962, by rfl⟩ : syracuseStep 613133 = 229925) (by norm_num)
theorem B613157 : Blo 405769 613157 := bbase (se 4 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 613157 = 114967) (by norm_num)
theorem B613181 : Blo 405769 613181 := bbase (se 3 (by rfl) ⟨114971, by rfl⟩ : syracuseStep 613181 = 229943) (by norm_num)
theorem B1399621 : Blo 405769 1399621 := bbase (se 4 (by rfl) ⟨131214, by rfl⟩ : syracuseStep 1399621 = 262429) (by norm_num)
theorem B613205 : Blo 405769 613205 := bbase (se 9 (by rfl) ⟨1796, by rfl⟩ : syracuseStep 613205 = 3593) (by norm_num)
theorem B777053 : Blo 405769 777053 := bbase (se 3 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 777053 = 291395) (by norm_num)
theorem B613229 : Blo 405769 613229 := bbase (se 3 (by rfl) ⟨114980, by rfl⟩ : syracuseStep 613229 = 229961) (by norm_num)
theorem B514937 : Blo 405769 514937 := bbase (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) (by norm_num)
theorem B613253 : Blo 405769 613253 := bbase (se 4 (by rfl) ⟨57492, by rfl⟩ : syracuseStep 613253 = 114985) (by norm_num)
theorem B613277 : Blo 405769 613277 := bbase (se 3 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 613277 = 229979) (by norm_num)
theorem B514993 : Blo 405769 514993 := bbase (se 2 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 514993 = 386245) (by norm_num)
theorem B613301 : Blo 405769 613301 := bbase (se 5 (by rfl) ⟨28748, by rfl⟩ : syracuseStep 613301 = 57497) (by norm_num)
theorem B613325 : Blo 405769 613325 := bbase (se 3 (by rfl) ⟨114998, by rfl⟩ : syracuseStep 613325 = 229997) (by norm_num)
theorem B613349 : Blo 405769 613349 := bbase (se 4 (by rfl) ⟨57501, by rfl⟩ : syracuseStep 613349 = 115003) (by norm_num)
theorem B777205 : Blo 405769 777205 := bbase (se 5 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 777205 = 72863) (by norm_num)
theorem B613373 : Blo 405769 613373 := bbase (se 3 (by rfl) ⟨115007, by rfl⟩ : syracuseStep 613373 = 230015) (by norm_num)
theorem B515089 : Blo 405769 515089 := bbase (se 2 (by rfl) ⟨193158, by rfl⟩ : syracuseStep 515089 = 386317) (by norm_num)
theorem B613397 : Blo 405769 613397 := bbase (se 6 (by rfl) ⟨14376, by rfl⟩ : syracuseStep 613397 = 28753) (by norm_num)
theorem B613421 : Blo 405769 613421 := bbase (se 3 (by rfl) ⟨115016, by rfl⟩ : syracuseStep 613421 = 230033) (by norm_num)
theorem B613445 : Blo 405769 613445 := bbase (se 4 (by rfl) ⟨57510, by rfl⟩ : syracuseStep 613445 = 115021) (by norm_num)
theorem B613469 : Blo 405769 613469 := bbase (se 3 (by rfl) ⟨115025, by rfl⟩ : syracuseStep 613469 = 230051) (by norm_num)
theorem B580717 : Blo 405769 580717 := bbase (se 3 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 580717 = 217769) (by norm_num)
theorem B613493 : Blo 405769 613493 := bbase (se 5 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 613493 = 57515) (by norm_num)
theorem B613517 : Blo 405769 613517 := bbase (se 3 (by rfl) ⟨115034, by rfl⟩ : syracuseStep 613517 = 230069) (by norm_num)
theorem B613541 : Blo 405769 613541 := bbase (se 4 (by rfl) ⟨57519, by rfl⟩ : syracuseStep 613541 = 115039) (by norm_num)
theorem B515261 : Blo 405769 515261 := bbase (se 3 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 515261 = 193223) (by norm_num)
theorem B613565 : Blo 405769 613565 := bbase (se 3 (by rfl) ⟨115043, by rfl⟩ : syracuseStep 613565 = 230087) (by norm_num)
theorem B1105093 : Blo 405769 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B613589 : Blo 405769 613589 := bbase (se 7 (by rfl) ⟨7190, by rfl⟩ : syracuseStep 613589 = 14381) (by norm_num)
theorem B613613 : Blo 405769 613613 := bbase (se 3 (by rfl) ⟨115052, by rfl⟩ : syracuseStep 613613 = 230105) (by norm_num)
theorem B515317 : Blo 405769 515317 := bbase (se 5 (by rfl) ⟨24155, by rfl⟩ : syracuseStep 515317 = 48311) (by norm_num)
theorem B613637 : Blo 405769 613637 := bbase (se 4 (by rfl) ⟨57528, by rfl⟩ : syracuseStep 613637 = 115057) (by norm_num)
theorem B613661 : Blo 405769 613661 := bbase (se 3 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 613661 = 230123) (by norm_num)
theorem B777509 : Blo 405769 777509 := bbase (se 4 (by rfl) ⟨72891, by rfl⟩ : syracuseStep 777509 = 145783) (by norm_num)
theorem B613685 : Blo 405769 613685 := bbase (se 5 (by rfl) ⟨28766, by rfl⟩ : syracuseStep 613685 = 57533) (by norm_num)
theorem B613709 : Blo 405769 613709 := bbase (se 3 (by rfl) ⟨115070, by rfl⟩ : syracuseStep 613709 = 230141) (by norm_num)
theorem B515413 : Blo 405769 515413 := bbase (se 11 (by rfl) ⟨377, by rfl⟩ : syracuseStep 515413 = 755) (by norm_num)
theorem B613733 : Blo 405769 613733 := bbase (se 4 (by rfl) ⟨57537, by rfl⟩ : syracuseStep 613733 = 115075) (by norm_num)
theorem B613757 : Blo 405769 613757 := bbase (se 3 (by rfl) ⟨115079, by rfl⟩ : syracuseStep 613757 = 230159) (by norm_num)
theorem B613781 : Blo 405769 613781 := bbase (se 6 (by rfl) ⟨14385, by rfl⟩ : syracuseStep 613781 = 28771) (by norm_num)
theorem B613805 : Blo 405769 613805 := bbase (se 3 (by rfl) ⟨115088, by rfl⟩ : syracuseStep 613805 = 230177) (by norm_num)
theorem B613829 : Blo 405769 613829 := bbase (se 4 (by rfl) ⟨57546, by rfl⟩ : syracuseStep 613829 = 115093) (by norm_num)
theorem B613853 : Blo 405769 613853 := bbase (se 3 (by rfl) ⟨115097, by rfl⟩ : syracuseStep 613853 = 230195) (by norm_num)
theorem B613877 : Blo 405769 613877 := bbase (se 5 (by rfl) ⟨28775, by rfl⟩ : syracuseStep 613877 = 57551) (by norm_num)
theorem B515585 : Blo 405769 515585 := bbase (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) (by norm_num)
theorem B613901 : Blo 405769 613901 := bbase (se 3 (by rfl) ⟨115106, by rfl⟩ : syracuseStep 613901 = 230213) (by norm_num)
theorem B613925 : Blo 405769 613925 := bbase (se 4 (by rfl) ⟨57555, by rfl⟩ : syracuseStep 613925 = 115111) (by norm_num)
theorem B515641 : Blo 405769 515641 := bbase (se 2 (by rfl) ⟨193365, by rfl⟩ : syracuseStep 515641 = 386731) (by norm_num)
theorem B613949 : Blo 405769 613949 := bbase (se 3 (by rfl) ⟨115115, by rfl⟩ : syracuseStep 613949 = 230231) (by norm_num)
theorem B613973 : Blo 405769 613973 := bbase (se 8 (by rfl) ⟨3597, by rfl⟩ : syracuseStep 613973 = 7195) (by norm_num)
theorem B548461 : Blo 405769 548461 := bbase (se 3 (by rfl) ⟨102836, by rfl⟩ : syracuseStep 548461 = 205673) (by norm_num)
theorem B613997 : Blo 405769 613997 := bbase (se 3 (by rfl) ⟨115124, by rfl⟩ : syracuseStep 613997 = 230249) (by norm_num)
theorem B1793669 : Blo 405769 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B614021 : Blo 405769 614021 := bbase (se 4 (by rfl) ⟨57564, by rfl⟩ : syracuseStep 614021 = 115129) (by norm_num)
theorem B515737 : Blo 405769 515737 := bbase (se 2 (by rfl) ⟨193401, by rfl⟩ : syracuseStep 515737 = 386803) (by norm_num)
theorem B614045 : Blo 405769 614045 := bbase (se 3 (by rfl) ⟨115133, by rfl⟩ : syracuseStep 614045 = 230267) (by norm_num)
theorem B614069 : Blo 405769 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B614093 : Blo 405769 614093 := bbase (se 3 (by rfl) ⟨115142, by rfl⟩ : syracuseStep 614093 = 230285) (by norm_num)
theorem B614117 : Blo 405769 614117 := bbase (se 4 (by rfl) ⟨57573, by rfl⟩ : syracuseStep 614117 = 115147) (by norm_num)
theorem B614141 : Blo 405769 614141 := bbase (se 3 (by rfl) ⟨115151, by rfl⟩ : syracuseStep 614141 = 230303) (by norm_num)
theorem B2055941 : Blo 405769 2055941 := bbase (se 4 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 2055941 = 385489) (by norm_num)
theorem B614165 : Blo 405769 614165 := bbase (se 6 (by rfl) ⟨14394, by rfl⟩ : syracuseStep 614165 = 28789) (by norm_num)
theorem B614189 : Blo 405769 614189 := bbase (se 3 (by rfl) ⟨115160, by rfl⟩ : syracuseStep 614189 = 230321) (by norm_num)
theorem B515909 : Blo 405769 515909 := bbase (se 4 (by rfl) ⟨48366, by rfl⟩ : syracuseStep 515909 = 96733) (by norm_num)
theorem B614213 : Blo 405769 614213 := bbase (se 4 (by rfl) ⟨57582, by rfl⟩ : syracuseStep 614213 = 115165) (by norm_num)
theorem B614237 : Blo 405769 614237 := bbase (se 3 (by rfl) ⟨115169, by rfl⟩ : syracuseStep 614237 = 230339) (by norm_num)
theorem B614261 : Blo 405769 614261 := bbase (se 5 (by rfl) ⟨28793, by rfl⟩ : syracuseStep 614261 = 57587) (by norm_num)
theorem B515965 : Blo 405769 515965 := bbase (se 3 (by rfl) ⟨96743, by rfl⟩ : syracuseStep 515965 = 193487) (by norm_num)
theorem B581509 : Blo 405769 581509 := bbase (se 4 (by rfl) ⟨54516, by rfl⟩ : syracuseStep 581509 = 109033) (by norm_num)
theorem B614285 : Blo 405769 614285 := bbase (se 3 (by rfl) ⟨115178, by rfl⟩ : syracuseStep 614285 = 230357) (by norm_num)
theorem B614309 : Blo 405769 614309 := bbase (se 4 (by rfl) ⟨57591, by rfl⟩ : syracuseStep 614309 = 115183) (by norm_num)
theorem B614333 : Blo 405769 614333 := bbase (se 3 (by rfl) ⟨115187, by rfl⟩ : syracuseStep 614333 = 230375) (by norm_num)
theorem B614357 : Blo 405769 614357 := bbase (se 7 (by rfl) ⟨7199, by rfl⟩ : syracuseStep 614357 = 14399) (by norm_num)
theorem B516061 : Blo 405769 516061 := bbase (se 3 (by rfl) ⟨96761, by rfl⟩ : syracuseStep 516061 = 193523) (by norm_num)
theorem B614381 : Blo 405769 614381 := bbase (se 3 (by rfl) ⟨115196, by rfl⟩ : syracuseStep 614381 = 230393) (by norm_num)
theorem B417793 : Blo 405769 417793 := bbase (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) (by norm_num)
theorem B614405 : Blo 405769 614405 := bbase (se 4 (by rfl) ⟨57600, by rfl⟩ : syracuseStep 614405 = 115201) (by norm_num)
theorem B548893 : Blo 405769 548893 := bbase (se 3 (by rfl) ⟨102917, by rfl⟩ : syracuseStep 548893 = 205835) (by norm_num)
theorem B614429 : Blo 405769 614429 := bbase (se 3 (by rfl) ⟨115205, by rfl⟩ : syracuseStep 614429 = 230411) (by norm_num)
theorem B614453 : Blo 405769 614453 := bbase (se 5 (by rfl) ⟨28802, by rfl⟩ : syracuseStep 614453 = 57605) (by norm_num)
theorem B614477 : Blo 405769 614477 := bbase (se 3 (by rfl) ⟨115214, by rfl⟩ : syracuseStep 614477 = 230429) (by norm_num)
theorem B614501 : Blo 405769 614501 := bbase (se 4 (by rfl) ⟨57609, by rfl⟩ : syracuseStep 614501 = 115219) (by norm_num)
theorem B614525 : Blo 405769 614525 := bbase (se 3 (by rfl) ⟨115223, by rfl⟩ : syracuseStep 614525 = 230447) (by norm_num)
theorem B516233 : Blo 405769 516233 := bbase (se 2 (by rfl) ⟨193587, by rfl⟩ : syracuseStep 516233 = 387175) (by norm_num)
theorem B614549 : Blo 405769 614549 := bbase (se 6 (by rfl) ⟨14403, by rfl⟩ : syracuseStep 614549 = 28807) (by norm_num)
theorem B614573 : Blo 405769 614573 := bbase (se 3 (by rfl) ⟨115232, by rfl⟩ : syracuseStep 614573 = 230465) (by norm_num)
theorem B516289 : Blo 405769 516289 := bbase (se 2 (by rfl) ⟨193608, by rfl⟩ : syracuseStep 516289 = 387217) (by norm_num)
theorem B614597 : Blo 405769 614597 := bbase (se 4 (by rfl) ⟨57618, by rfl⟩ : syracuseStep 614597 = 115237) (by norm_num)
theorem B581845 : Blo 405769 581845 := bbase (se 7 (by rfl) ⟨6818, by rfl⟩ : syracuseStep 581845 = 13637) (by norm_num)
theorem B614621 : Blo 405769 614621 := bbase (se 3 (by rfl) ⟨115241, by rfl⟩ : syracuseStep 614621 = 230483) (by norm_num)
theorem B614645 : Blo 405769 614645 := bbase (se 5 (by rfl) ⟨28811, by rfl⟩ : syracuseStep 614645 = 57623) (by norm_num)
theorem B516385 : Blo 405769 516385 := bbase (se 2 (by rfl) ⟨193644, by rfl⟩ : syracuseStep 516385 = 387289) (by norm_num)
theorem B582061 : Blo 405769 582061 := bbase (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) (by norm_num)
theorem B516557 : Blo 405769 516557 := bbase (se 3 (by rfl) ⟨96854, by rfl⟩ : syracuseStep 516557 = 193709) (by norm_num)
theorem B1171925 : Blo 405769 1171925 := bbase (se 7 (by rfl) ⟨13733, by rfl⟩ : syracuseStep 1171925 = 27467) (by norm_num)
theorem B1466885 : Blo 405769 1466885 := bbase (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) (by norm_num)
theorem B516613 : Blo 405769 516613 := bbase (se 4 (by rfl) ⟨48432, by rfl⟩ : syracuseStep 516613 = 96865) (by norm_num)
theorem B2482741 : Blo 405769 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B516709 : Blo 405769 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B1237637 : Blo 405769 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B516881 : Blo 405769 516881 := bbase (se 2 (by rfl) ⟨193830, by rfl⟩ : syracuseStep 516881 = 387661) (by norm_num)
theorem B1237781 : Blo 405769 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B549661 : Blo 405769 549661 := bbase (se 3 (by rfl) ⟨103061, by rfl⟩ : syracuseStep 549661 = 206123) (by norm_num)
theorem B1467173 : Blo 405769 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B582437 : Blo 405769 582437 := bbase (se 4 (by rfl) ⟨54603, by rfl⟩ : syracuseStep 582437 = 109207) (by norm_num)
theorem B516937 : Blo 405769 516937 := bbase (se 2 (by rfl) ⟨193851, by rfl⟩ : syracuseStep 516937 = 387703) (by norm_num)
theorem B517033 : Blo 405769 517033 := bbase (se 2 (by rfl) ⟨193887, by rfl⟩ : syracuseStep 517033 = 387775) (by norm_num)
theorem B549877 : Blo 405769 549877 := bbase (se 5 (by rfl) ⟨25775, by rfl⟩ : syracuseStep 549877 = 51551) (by norm_num)
theorem B2057237 : Blo 405769 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B1303589 : Blo 405769 1303589 := bbase (se 4 (by rfl) ⟨122211, by rfl⟩ : syracuseStep 1303589 = 244423) (by norm_num)
theorem B517205 : Blo 405769 517205 := bbase (se 8 (by rfl) ⟨3030, by rfl⟩ : syracuseStep 517205 = 6061) (by norm_num)
theorem B517261 : Blo 405769 517261 := bbase (se 3 (by rfl) ⟨96986, by rfl⟩ : syracuseStep 517261 = 193973) (by norm_num)
theorem B517357 : Blo 405769 517357 := bbase (se 3 (by rfl) ⟨97004, by rfl⟩ : syracuseStep 517357 = 194009) (by norm_num)
theorem B3368213 : Blo 405769 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B1369493 : Blo 405769 1369493 := bbase (se 6 (by rfl) ⟨32097, by rfl⟩ : syracuseStep 1369493 = 64195) (by norm_num)
theorem B517529 : Blo 405769 517529 := bbase (se 2 (by rfl) ⟨194073, by rfl⟩ : syracuseStep 517529 = 388147) (by norm_num)
theorem B517585 : Blo 405769 517585 := bbase (se 2 (by rfl) ⟨194094, by rfl⟩ : syracuseStep 517585 = 388189) (by norm_num)
theorem B1959461 : Blo 405769 1959461 := bbase (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) (by norm_num)
theorem B517681 : Blo 405769 517681 := bbase (se 2 (by rfl) ⟨194130, by rfl⟩ : syracuseStep 517681 = 388261) (by norm_num)
theorem B1893989 : Blo 405769 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B4187861 : Blo 405769 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B517853 : Blo 405769 517853 := bbase (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) (by norm_num)
theorem B517909 : Blo 405769 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B976693 : Blo 405769 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B1369925 : Blo 405769 1369925 := bbase (se 4 (by rfl) ⟨128430, by rfl⟩ : syracuseStep 1369925 = 256861) (by norm_num)
theorem B518005 : Blo 405769 518005 := bbase (se 5 (by rfl) ⟨24281, by rfl⟩ : syracuseStep 518005 = 48563) (by norm_num)
theorem B550813 : Blo 405769 550813 := bbase (se 3 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 550813 = 206555) (by norm_num)
theorem B7858133 : Blo 405769 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B3467285 : Blo 405769 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B518177 : Blo 405769 518177 := bbase (se 2 (by rfl) ⟨194316, by rfl⟩ : syracuseStep 518177 = 388633) (by norm_num)
theorem B1173541 : Blo 405769 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B518233 : Blo 405769 518233 := bbase (se 2 (by rfl) ⟨194337, by rfl⟩ : syracuseStep 518233 = 388675) (by norm_num)
theorem B944261 : Blo 405769 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B3106997 : Blo 405769 3106997 := bbase (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) (by norm_num)
theorem B518329 : Blo 405769 518329 := bbase (se 2 (by rfl) ⟨194373, by rfl⟩ : syracuseStep 518329 = 388747) (by norm_num)
theorem B1370357 : Blo 405769 1370357 := bbase (se 5 (by rfl) ⟨64235, by rfl⟩ : syracuseStep 1370357 = 128471) (by norm_num)
theorem B1009925 : Blo 405769 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B2058533 : Blo 405769 2058533 := bbase (se 4 (by rfl) ⟨192987, by rfl⟩ : syracuseStep 2058533 = 385975) (by norm_num)
theorem B518501 : Blo 405769 518501 := bbase (se 4 (by rfl) ⟨48609, by rfl⟩ : syracuseStep 518501 = 97219) (by norm_num)
theorem B977309 : Blo 405769 977309 := bbase (se 3 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 977309 = 366491) (by norm_num)
theorem B518557 : Blo 405769 518557 := bbase (se 3 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 518557 = 194459) (by norm_num)
theorem B977501 : Blo 405769 977501 := bbase (se 3 (by rfl) ⟨183281, by rfl⟩ : syracuseStep 977501 = 366563) (by norm_num)
theorem B2321045 : Blo 405769 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B1370789 : Blo 405769 1370789 := bbase (se 4 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 1370789 = 257023) (by norm_num)
theorem B617237 : Blo 405769 617237 := bbase (se 6 (by rfl) ⟨14466, by rfl⟩ : syracuseStep 617237 = 28933) (by norm_num)
theorem B1043333 : Blo 405769 1043333 := bbase (se 4 (by rfl) ⟨97812, by rfl⟩ : syracuseStep 1043333 = 195625) (by norm_num)
theorem B3959765 : Blo 405769 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B7826453 : Blo 405769 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B1371221 : Blo 405769 1371221 := bbase (se 8 (by rfl) ⟨8034, by rfl⟩ : syracuseStep 1371221 = 16069) (by norm_num)
theorem B978077 : Blo 405769 978077 := bbase (se 3 (by rfl) ⟨183389, by rfl⟩ : syracuseStep 978077 = 366779) (by norm_num)
theorem B650405 : Blo 405769 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B1305845 : Blo 405769 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B552197 : Blo 405769 552197 := bbase (se 4 (by rfl) ⟨51768, by rfl⟩ : syracuseStep 552197 = 103537) (by norm_num)
theorem B1305973 : Blo 405769 1305973 := bbase (se 5 (by rfl) ⟨61217, by rfl⟩ : syracuseStep 1305973 = 122435) (by norm_num)
theorem B650629 : Blo 405769 650629 := bbase (se 4 (by rfl) ⟨60996, by rfl⟩ : syracuseStep 650629 = 121993) (by norm_num)
theorem B650693 : Blo 405769 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B1371653 : Blo 405769 1371653 := bbase (se 4 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 1371653 = 257185) (by norm_num)
theorem B978461 : Blo 405769 978461 := bbase (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) (by norm_num)
theorem B2059829 : Blo 405769 2059829 := bbase (se 5 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 2059829 = 193109) (by norm_num)
theorem B650821 : Blo 405769 650821 := bbase (se 4 (by rfl) ⟨61014, by rfl⟩ : syracuseStep 650821 = 122029) (by norm_num)
theorem B913013 : Blo 405769 913013 := bbase (se 5 (by rfl) ⟨42797, by rfl⟩ : syracuseStep 913013 = 85595) (by norm_num)
theorem B913085 : Blo 405769 913085 := bbase (se 3 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 913085 = 342407) (by norm_num)
theorem B913157 : Blo 405769 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B2322229 : Blo 405769 2322229 := bbase (se 5 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 2322229 = 217709) (by norm_num)
theorem B913229 : Blo 405769 913229 := bbase (se 3 (by rfl) ⟨171230, by rfl⟩ : syracuseStep 913229 = 342461) (by norm_num)
theorem B1699717 : Blo 405769 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B913301 : Blo 405769 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B1372085 : Blo 405769 1372085 := bbase (se 5 (by rfl) ⟨64316, by rfl⟩ : syracuseStep 1372085 = 128633) (by norm_num)
theorem B3927989 : Blo 405769 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B913373 : Blo 405769 913373 := bbase (se 3 (by rfl) ⟨171257, by rfl⟩ : syracuseStep 913373 = 342515) (by norm_num)
theorem B913445 : Blo 405769 913445 := bbase (se 4 (by rfl) ⟨85635, by rfl⟩ : syracuseStep 913445 = 171271) (by norm_num)
theorem B2617429 : Blo 405769 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B913517 : Blo 405769 913517 := bbase (se 3 (by rfl) ⟨171284, by rfl⟩ : syracuseStep 913517 = 342569) (by norm_num)
theorem B487549 : Blo 405769 487549 := bbase (se 3 (by rfl) ⟨91415, by rfl⟩ : syracuseStep 487549 = 182831) (by norm_num)
theorem B1241237 : Blo 405769 1241237 := bbase (se 6 (by rfl) ⟨29091, by rfl⟩ : syracuseStep 1241237 = 58183) (by norm_num)
theorem B553109 : Blo 405769 553109 := bbase (se 6 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 553109 = 25927) (by norm_num)
theorem B1962149 : Blo 405769 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B913589 : Blo 405769 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B913661 : Blo 405769 913661 := bbase (se 3 (by rfl) ⟨171311, by rfl⟩ : syracuseStep 913661 = 342623) (by norm_num)
theorem B913733 : Blo 405769 913733 := bbase (se 4 (by rfl) ⟨85662, by rfl⟩ : syracuseStep 913733 = 171325) (by norm_num)
theorem B782669 : Blo 405769 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B1372517 : Blo 405769 1372517 := bbase (se 4 (by rfl) ⟨128673, by rfl⟩ : syracuseStep 1372517 = 257347) (by norm_num)
theorem B913805 : Blo 405769 913805 := bbase (se 3 (by rfl) ⟨171338, by rfl⟩ : syracuseStep 913805 = 342677) (by norm_num)
theorem B913877 : Blo 405769 913877 := bbase (se 7 (by rfl) ⟨10709, by rfl⟩ : syracuseStep 913877 = 21419) (by norm_num)
theorem B913949 : Blo 405769 913949 := bbase (se 3 (by rfl) ⟨171365, by rfl⟩ : syracuseStep 913949 = 342731) (by norm_num)
theorem B914021 : Blo 405769 914021 := bbase (se 4 (by rfl) ⟨85689, by rfl⟩ : syracuseStep 914021 = 171379) (by norm_num)
theorem B914093 : Blo 405769 914093 := bbase (se 3 (by rfl) ⟨171392, by rfl⟩ : syracuseStep 914093 = 342785) (by norm_num)
theorem B1569461 : Blo 405769 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B7533269 : Blo 405769 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B914165 : Blo 405769 914165 := bbase (se 5 (by rfl) ⟨42851, by rfl⟩ : syracuseStep 914165 = 85703) (by norm_num)
theorem B783101 : Blo 405769 783101 := bbase (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) (by norm_num)
theorem B652045 : Blo 405769 652045 := bbase (se 3 (by rfl) ⟨122258, by rfl⟩ : syracuseStep 652045 = 244517) (by norm_num)
theorem B684821 : Blo 405769 684821 := bbase (se 6 (by rfl) ⟨16050, by rfl⟩ : syracuseStep 684821 = 32101) (by norm_num)
theorem B1372949 : Blo 405769 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B1766165 : Blo 405769 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B914237 : Blo 405769 914237 := bbase (se 3 (by rfl) ⟨171419, by rfl⟩ : syracuseStep 914237 = 342839) (by norm_num)
theorem B2061125 : Blo 405769 2061125 := bbase (se 4 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 2061125 = 386461) (by norm_num)
theorem B914309 : Blo 405769 914309 := bbase (se 4 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 914309 = 171433) (by norm_num)
theorem B684949 : Blo 405769 684949 := bbase (se 6 (by rfl) ⟨16053, by rfl⟩ : syracuseStep 684949 = 32107) (by norm_num)
theorem B914381 : Blo 405769 914381 := bbase (se 3 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 914381 = 342893) (by norm_num)
theorem B685037 : Blo 405769 685037 := bbase (se 3 (by rfl) ⟨128444, by rfl⟩ : syracuseStep 685037 = 256889) (by norm_num)
theorem B914453 : Blo 405769 914453 := bbase (se 6 (by rfl) ⟨21432, by rfl⟩ : syracuseStep 914453 = 42865) (by norm_num)
theorem B947285 : Blo 405769 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B914525 : Blo 405769 914525 := bbase (se 3 (by rfl) ⟨171473, by rfl⟩ : syracuseStep 914525 = 342947) (by norm_num)
theorem B685165 : Blo 405769 685165 := bbase (se 3 (by rfl) ⟨128468, by rfl⟩ : syracuseStep 685165 = 256937) (by norm_num)
theorem B914597 : Blo 405769 914597 := bbase (se 4 (by rfl) ⟨85743, by rfl⟩ : syracuseStep 914597 = 171487) (by norm_num)
theorem B685253 : Blo 405769 685253 := bbase (se 4 (by rfl) ⟨64242, by rfl⟩ : syracuseStep 685253 = 128485) (by norm_num)
theorem B1373381 : Blo 405769 1373381 := bbase (se 4 (by rfl) ⟨128754, by rfl⟩ : syracuseStep 1373381 = 257509) (by norm_num)
theorem B914669 : Blo 405769 914669 := bbase (se 3 (by rfl) ⟨171500, by rfl⟩ : syracuseStep 914669 = 343001) (by norm_num)
theorem B980221 : Blo 405769 980221 := bbase (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) (by norm_num)
theorem B914741 : Blo 405769 914741 := bbase (se 5 (by rfl) ⟨42878, by rfl⟩ : syracuseStep 914741 = 85757) (by norm_num)
theorem B685381 : Blo 405769 685381 := bbase (se 4 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 685381 = 128509) (by norm_num)
theorem B914813 : Blo 405769 914813 := bbase (se 3 (by rfl) ⟨171527, by rfl⟩ : syracuseStep 914813 = 343055) (by norm_num)
theorem B685469 : Blo 405769 685469 := bbase (se 3 (by rfl) ⟨128525, by rfl⟩ : syracuseStep 685469 = 257051) (by norm_num)
theorem B652717 : Blo 405769 652717 := bbase (se 3 (by rfl) ⟨122384, by rfl⟩ : syracuseStep 652717 = 244769) (by norm_num)
theorem B914885 : Blo 405769 914885 := bbase (se 4 (by rfl) ⟨85770, by rfl⟩ : syracuseStep 914885 = 171541) (by norm_num)
theorem B521677 : Blo 405769 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B914957 : Blo 405769 914957 := bbase (se 3 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 914957 = 343109) (by norm_num)
theorem B685597 : Blo 405769 685597 := bbase (se 3 (by rfl) ⟨128549, by rfl⟩ : syracuseStep 685597 = 257099) (by norm_num)
theorem B915029 : Blo 405769 915029 := bbase (se 8 (by rfl) ⟨5361, by rfl⟩ : syracuseStep 915029 = 10723) (by norm_num)
theorem B685685 : Blo 405769 685685 := bbase (se 5 (by rfl) ⟨32141, by rfl⟩ : syracuseStep 685685 = 64283) (by norm_num)
theorem B1373813 : Blo 405769 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B915101 : Blo 405769 915101 := bbase (se 3 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 915101 = 343163) (by norm_num)
theorem B489125 : Blo 405769 489125 := bbase (se 4 (by rfl) ⟨45855, by rfl⟩ : syracuseStep 489125 = 91711) (by norm_num)
theorem B915173 : Blo 405769 915173 := bbase (se 4 (by rfl) ⟨85797, by rfl⟩ : syracuseStep 915173 = 171595) (by norm_num)
theorem B685813 : Blo 405769 685813 := bbase (se 5 (by rfl) ⟨32147, by rfl⟩ : syracuseStep 685813 = 64295) (by norm_num)
theorem B2324213 : Blo 405769 2324213 := bbase (se 5 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 2324213 = 217895) (by norm_num)
theorem B456493 : Blo 405769 456493 := bbase (se 3 (by rfl) ⟨85592, by rfl⟩ : syracuseStep 456493 = 171185) (by norm_num)
theorem B915245 : Blo 405769 915245 := bbase (se 3 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 915245 = 343217) (by norm_num)
theorem B685901 : Blo 405769 685901 := bbase (se 3 (by rfl) ⟨128606, by rfl⟩ : syracuseStep 685901 = 257213) (by norm_num)
theorem B456529 : Blo 405769 456529 := bbase (se 2 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 456529 = 342397) (by norm_num)
theorem B1242965 : Blo 405769 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B456565 : Blo 405769 456565 := bbase (se 5 (by rfl) ⟨21401, by rfl⟩ : syracuseStep 456565 = 42803) (by norm_num)
theorem B915317 : Blo 405769 915317 := bbase (se 5 (by rfl) ⟨42905, by rfl⟩ : syracuseStep 915317 = 85811) (by norm_num)
theorem B456601 : Blo 405769 456601 := bbase (se 2 (by rfl) ⟨171225, by rfl⟩ : syracuseStep 456601 = 342451) (by norm_num)
theorem B456637 : Blo 405769 456637 := bbase (se 3 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 456637 = 171239) (by norm_num)
theorem B915389 : Blo 405769 915389 := bbase (se 3 (by rfl) ⟨171635, by rfl⟩ : syracuseStep 915389 = 343271) (by norm_num)
theorem B686029 : Blo 405769 686029 := bbase (se 3 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 686029 = 257261) (by norm_num)
theorem B653261 : Blo 405769 653261 := bbase (se 3 (by rfl) ⟨122486, by rfl⟩ : syracuseStep 653261 = 244973) (by norm_num)
theorem B456673 : Blo 405769 456673 := bbase (se 2 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 456673 = 342505) (by norm_num)
theorem B489461 : Blo 405769 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B456709 : Blo 405769 456709 := bbase (se 4 (by rfl) ⟨42816, by rfl⟩ : syracuseStep 456709 = 85633) (by norm_num)
theorem B915461 : Blo 405769 915461 := bbase (se 4 (by rfl) ⟨85824, by rfl⟩ : syracuseStep 915461 = 171649) (by norm_num)
theorem B686117 : Blo 405769 686117 := bbase (se 4 (by rfl) ⟨64323, by rfl⟩ : syracuseStep 686117 = 128647) (by norm_num)
theorem B1374245 : Blo 405769 1374245 := bbase (se 4 (by rfl) ⟨128835, by rfl⟩ : syracuseStep 1374245 = 257671) (by norm_num)
theorem B456745 : Blo 405769 456745 := bbase (se 2 (by rfl) ⟨171279, by rfl⟩ : syracuseStep 456745 = 342559) (by norm_num)
theorem B456781 : Blo 405769 456781 := bbase (se 3 (by rfl) ⟨85646, by rfl⟩ : syracuseStep 456781 = 171293) (by norm_num)
theorem B915533 : Blo 405769 915533 := bbase (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) (by norm_num)
theorem B2062421 : Blo 405769 2062421 := bbase (se 8 (by rfl) ⟨12084, by rfl⟩ : syracuseStep 2062421 = 24169) (by norm_num)
theorem B489577 : Blo 405769 489577 := bbase (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) (by norm_num)
theorem B456817 : Blo 405769 456817 := bbase (se 2 (by rfl) ⟨171306, by rfl⟩ : syracuseStep 456817 = 342613) (by norm_num)
theorem B456853 : Blo 405769 456853 := bbase (se 6 (by rfl) ⟨10707, by rfl⟩ : syracuseStep 456853 = 21415) (by norm_num)
theorem B915605 : Blo 405769 915605 := bbase (se 6 (by rfl) ⟨21459, by rfl⟩ : syracuseStep 915605 = 42919) (by norm_num)
theorem B8485013 : Blo 405769 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B686245 : Blo 405769 686245 := bbase (se 4 (by rfl) ⟨64335, by rfl⟩ : syracuseStep 686245 = 128671) (by norm_num)
theorem B489649 : Blo 405769 489649 := bbase (se 2 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 489649 = 367237) (by norm_num)
theorem B456889 : Blo 405769 456889 := bbase (se 2 (by rfl) ⟨171333, by rfl⟩ : syracuseStep 456889 = 342667) (by norm_num)
theorem B1308869 : Blo 405769 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B489673 : Blo 405769 489673 := bbase (se 2 (by rfl) ⟨183627, by rfl⟩ : syracuseStep 489673 = 367255) (by norm_num)
theorem B456925 : Blo 405769 456925 := bbase (se 3 (by rfl) ⟨85673, by rfl⟩ : syracuseStep 456925 = 171347) (by norm_num)
theorem B915677 : Blo 405769 915677 := bbase (se 3 (by rfl) ⟨171689, by rfl⟩ : syracuseStep 915677 = 343379) (by norm_num)
theorem B620765 : Blo 405769 620765 := bbase (se 3 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 620765 = 232787) (by norm_num)
theorem B981229 : Blo 405769 981229 := bbase (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) (by norm_num)
theorem B686333 : Blo 405769 686333 := bbase (se 3 (by rfl) ⟨128687, by rfl⟩ : syracuseStep 686333 = 257375) (by norm_num)
theorem B456961 : Blo 405769 456961 := bbase (se 2 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 456961 = 342721) (by norm_num)
theorem B620813 : Blo 405769 620813 := bbase (se 3 (by rfl) ⟨116402, by rfl⟩ : syracuseStep 620813 = 232805) (by norm_num)
theorem B456997 : Blo 405769 456997 := bbase (se 4 (by rfl) ⟨42843, by rfl⟩ : syracuseStep 456997 = 85687) (by norm_num)
theorem B915749 : Blo 405769 915749 := bbase (se 4 (by rfl) ⟨85851, by rfl⟩ : syracuseStep 915749 = 171703) (by norm_num)
theorem B457033 : Blo 405769 457033 := bbase (se 2 (by rfl) ⟨171387, by rfl⟩ : syracuseStep 457033 = 342775) (by norm_num)
theorem B981325 : Blo 405769 981325 := bbase (se 3 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 981325 = 367997) (by norm_num)
theorem B489817 : Blo 405769 489817 := bbase (se 2 (by rfl) ⟨183681, by rfl⟩ : syracuseStep 489817 = 367363) (by norm_num)
theorem B457069 : Blo 405769 457069 := bbase (se 3 (by rfl) ⟨85700, by rfl⟩ : syracuseStep 457069 = 171401) (by norm_num)
theorem B915821 : Blo 405769 915821 := bbase (se 3 (by rfl) ⟨171716, by rfl⟩ : syracuseStep 915821 = 343433) (by norm_num)
theorem B686461 : Blo 405769 686461 := bbase (se 3 (by rfl) ⟨128711, by rfl⟩ : syracuseStep 686461 = 257423) (by norm_num)
theorem B457105 : Blo 405769 457105 := bbase (se 2 (by rfl) ⟨171414, by rfl⟩ : syracuseStep 457105 = 342829) (by norm_num)
theorem B653717 : Blo 405769 653717 := bbase (se 6 (by rfl) ⟨15321, by rfl⟩ : syracuseStep 653717 = 30643) (by norm_num)
theorem B5896597 : Blo 405769 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B457141 : Blo 405769 457141 := bbase (se 5 (by rfl) ⟨21428, by rfl⟩ : syracuseStep 457141 = 42857) (by norm_num)
theorem B915893 : Blo 405769 915893 := bbase (se 5 (by rfl) ⟨42932, by rfl⟩ : syracuseStep 915893 = 85865) (by norm_num)
theorem B686549 : Blo 405769 686549 := bbase (se 7 (by rfl) ⟨8045, by rfl⟩ : syracuseStep 686549 = 16091) (by norm_num)
theorem B1374677 : Blo 405769 1374677 := bbase (se 7 (by rfl) ⟨16109, by rfl⟩ : syracuseStep 1374677 = 32219) (by norm_num)
theorem B457177 : Blo 405769 457177 := bbase (se 2 (by rfl) ⟨171441, by rfl⟩ : syracuseStep 457177 = 342883) (by norm_num)
theorem B457213 : Blo 405769 457213 := bbase (se 3 (by rfl) ⟨85727, by rfl⟩ : syracuseStep 457213 = 171455) (by norm_num)
theorem B915965 : Blo 405769 915965 := bbase (se 3 (by rfl) ⟨171743, by rfl⟩ : syracuseStep 915965 = 343487) (by norm_num)
theorem B4946453 : Blo 405769 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B457249 : Blo 405769 457249 := bbase (se 2 (by rfl) ⟨171468, by rfl⟩ : syracuseStep 457249 = 342937) (by norm_num)
theorem B457285 : Blo 405769 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B916037 : Blo 405769 916037 := bbase (se 4 (by rfl) ⟨85878, by rfl⟩ : syracuseStep 916037 = 171757) (by norm_num)
theorem B686677 : Blo 405769 686677 := bbase (se 8 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 686677 = 8047) (by norm_num)
theorem B1342037 : Blo 405769 1342037 := bbase (se 8 (by rfl) ⟨7863, by rfl⟩ : syracuseStep 1342037 = 15727) (by norm_num)
theorem B457321 : Blo 405769 457321 := bbase (se 2 (by rfl) ⟨171495, by rfl⟩ : syracuseStep 457321 = 342991) (by norm_num)
theorem B457357 : Blo 405769 457357 := bbase (se 3 (by rfl) ⟨85754, by rfl⟩ : syracuseStep 457357 = 171509) (by norm_num)
theorem B916109 : Blo 405769 916109 := bbase (se 3 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 916109 = 343541) (by norm_num)
theorem B686765 : Blo 405769 686765 := bbase (se 3 (by rfl) ⟨128768, by rfl⟩ : syracuseStep 686765 = 257537) (by norm_num)
theorem B457393 : Blo 405769 457393 := bbase (se 2 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 457393 = 343045) (by norm_num)
theorem B457429 : Blo 405769 457429 := bbase (se 7 (by rfl) ⟨5360, by rfl⟩ : syracuseStep 457429 = 10721) (by norm_num)
theorem B916181 : Blo 405769 916181 := bbase (se 7 (by rfl) ⟨10736, by rfl⟩ : syracuseStep 916181 = 21473) (by norm_num)
theorem B457465 : Blo 405769 457465 := bbase (se 2 (by rfl) ⟨171549, by rfl⟩ : syracuseStep 457465 = 343099) (by norm_num)
theorem B457501 : Blo 405769 457501 := bbase (se 3 (by rfl) ⟨85781, by rfl⟩ : syracuseStep 457501 = 171563) (by norm_num)
theorem B916253 : Blo 405769 916253 := bbase (se 3 (by rfl) ⟨171797, by rfl⟩ : syracuseStep 916253 = 343595) (by norm_num)
theorem B686893 : Blo 405769 686893 := bbase (se 3 (by rfl) ⟨128792, by rfl⟩ : syracuseStep 686893 = 257585) (by norm_num)
theorem B457537 : Blo 405769 457537 := bbase (se 2 (by rfl) ⟨171576, by rfl⟩ : syracuseStep 457537 = 343153) (by norm_num)
theorem B981845 : Blo 405769 981845 := bbase (se 9 (by rfl) ⟨2876, by rfl⟩ : syracuseStep 981845 = 5753) (by norm_num)
theorem B457573 : Blo 405769 457573 := bbase (se 4 (by rfl) ⟨42897, by rfl⟩ : syracuseStep 457573 = 85795) (by norm_num)
theorem B916325 : Blo 405769 916325 := bbase (se 4 (by rfl) ⟨85905, by rfl⟩ : syracuseStep 916325 = 171811) (by norm_num)
theorem B686981 : Blo 405769 686981 := bbase (se 4 (by rfl) ⟨64404, by rfl⟩ : syracuseStep 686981 = 128809) (by norm_num)
theorem B1375109 : Blo 405769 1375109 := bbase (se 4 (by rfl) ⟨128916, by rfl⟩ : syracuseStep 1375109 = 257833) (by norm_num)
theorem B457609 : Blo 405769 457609 := bbase (se 2 (by rfl) ⟨171603, by rfl⟩ : syracuseStep 457609 = 343207) (by norm_num)
theorem B457645 : Blo 405769 457645 := bbase (se 3 (by rfl) ⟨85808, by rfl⟩ : syracuseStep 457645 = 171617) (by norm_num)
theorem B916397 : Blo 405769 916397 := bbase (se 3 (by rfl) ⟨171824, by rfl⟩ : syracuseStep 916397 = 343649) (by norm_num)
theorem B457681 : Blo 405769 457681 := bbase (se 2 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 457681 = 343261) (by norm_num)
theorem B457717 : Blo 405769 457717 := bbase (se 5 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 457717 = 42911) (by norm_num)
theorem B916469 : Blo 405769 916469 := bbase (se 5 (by rfl) ⟨42959, by rfl⟩ : syracuseStep 916469 = 85919) (by norm_num)
theorem B687109 : Blo 405769 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B457753 : Blo 405769 457753 := bbase (se 2 (by rfl) ⟨171657, by rfl⟩ : syracuseStep 457753 = 343315) (by norm_num)
theorem B457789 : Blo 405769 457789 := bbase (se 3 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 457789 = 171671) (by norm_num)
theorem B916541 : Blo 405769 916541 := bbase (se 3 (by rfl) ⟨171851, by rfl⟩ : syracuseStep 916541 = 343703) (by norm_num)
theorem B687197 : Blo 405769 687197 := bbase (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) (by norm_num)
theorem B785501 : Blo 405769 785501 := bbase (se 3 (by rfl) ⟨147281, by rfl⟩ : syracuseStep 785501 = 294563) (by norm_num)
theorem B457825 : Blo 405769 457825 := bbase (se 2 (by rfl) ⟨171684, by rfl⟩ : syracuseStep 457825 = 343369) (by norm_num)
theorem B457861 : Blo 405769 457861 := bbase (se 4 (by rfl) ⟨42924, by rfl⟩ : syracuseStep 457861 = 85849) (by norm_num)
theorem B916613 : Blo 405769 916613 := bbase (se 4 (by rfl) ⟨85932, by rfl⟩ : syracuseStep 916613 = 171865) (by norm_num)
theorem B457897 : Blo 405769 457897 := bbase (se 2 (by rfl) ⟨171711, by rfl⟩ : syracuseStep 457897 = 343423) (by norm_num)
theorem B457933 : Blo 405769 457933 := bbase (se 3 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 457933 = 171725) (by norm_num)
theorem B916685 : Blo 405769 916685 := bbase (se 3 (by rfl) ⟨171878, by rfl⟩ : syracuseStep 916685 = 343757) (by norm_num)
theorem B687325 : Blo 405769 687325 := bbase (se 3 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 687325 = 257747) (by norm_num)
theorem B457969 : Blo 405769 457969 := bbase (se 2 (by rfl) ⟨171738, by rfl⟩ : syracuseStep 457969 = 343477) (by norm_num)
theorem B458005 : Blo 405769 458005 := bbase (se 6 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 458005 = 21469) (by norm_num)
theorem B916757 : Blo 405769 916757 := bbase (se 6 (by rfl) ⟨21486, by rfl⟩ : syracuseStep 916757 = 42973) (by norm_num)
theorem B687413 : Blo 405769 687413 := bbase (se 5 (by rfl) ⟨32222, by rfl⟩ : syracuseStep 687413 = 64445) (by norm_num)
theorem B1375541 : Blo 405769 1375541 := bbase (se 5 (by rfl) ⟨64478, by rfl⟩ : syracuseStep 1375541 = 128957) (by norm_num)
theorem B458041 : Blo 405769 458041 := bbase (se 2 (by rfl) ⟨171765, by rfl⟩ : syracuseStep 458041 = 343531) (by norm_num)
theorem B458077 : Blo 405769 458077 := bbase (se 3 (by rfl) ⟨85889, by rfl⟩ : syracuseStep 458077 = 171779) (by norm_num)
theorem B916829 : Blo 405769 916829 := bbase (se 3 (by rfl) ⟨171905, by rfl⟩ : syracuseStep 916829 = 343811) (by norm_num)
theorem B2063717 : Blo 405769 2063717 := bbase (se 4 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 2063717 = 386947) (by norm_num)
theorem B982373 : Blo 405769 982373 := bbase (se 4 (by rfl) ⟨92097, by rfl⟩ : syracuseStep 982373 = 184195) (by norm_num)
theorem B458113 : Blo 405769 458113 := bbase (se 2 (by rfl) ⟨171792, by rfl⟩ : syracuseStep 458113 = 343585) (by norm_num)
theorem B458149 : Blo 405769 458149 := bbase (se 4 (by rfl) ⟨42951, by rfl⟩ : syracuseStep 458149 = 85903) (by norm_num)
theorem B916901 : Blo 405769 916901 := bbase (se 4 (by rfl) ⟨85959, by rfl⟩ : syracuseStep 916901 = 171919) (by norm_num)
theorem B687541 : Blo 405769 687541 := bbase (se 5 (by rfl) ⟨32228, by rfl⟩ : syracuseStep 687541 = 64457) (by norm_num)
theorem B458185 : Blo 405769 458185 := bbase (se 2 (by rfl) ⟨171819, by rfl⟩ : syracuseStep 458185 = 343639) (by norm_num)
theorem B458221 : Blo 405769 458221 := bbase (se 3 (by rfl) ⟨85916, by rfl⟩ : syracuseStep 458221 = 171833) (by norm_num)
theorem B916973 : Blo 405769 916973 := bbase (se 3 (by rfl) ⟨171932, by rfl⟩ : syracuseStep 916973 = 343865) (by norm_num)
theorem B687629 : Blo 405769 687629 := bbase (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) (by norm_num)
theorem B458257 : Blo 405769 458257 := bbase (se 2 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 458257 = 343693) (by norm_num)
theorem B491033 : Blo 405769 491033 := bbase (se 2 (by rfl) ⟨184137, by rfl⟩ : syracuseStep 491033 = 368275) (by norm_num)
theorem B458293 : Blo 405769 458293 := bbase (se 5 (by rfl) ⟨21482, by rfl⟩ : syracuseStep 458293 = 42965) (by norm_num)
theorem B917045 : Blo 405769 917045 := bbase (se 5 (by rfl) ⟨42986, by rfl⟩ : syracuseStep 917045 = 85973) (by norm_num)
theorem B982613 : Blo 405769 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B458329 : Blo 405769 458329 := bbase (se 2 (by rfl) ⟨171873, by rfl⟩ : syracuseStep 458329 = 343747) (by norm_num)
theorem B458365 : Blo 405769 458365 := bbase (se 3 (by rfl) ⟨85943, by rfl⟩ : syracuseStep 458365 = 171887) (by norm_num)
theorem B917117 : Blo 405769 917117 := bbase (se 3 (by rfl) ⟨171959, by rfl⟩ : syracuseStep 917117 = 343919) (by norm_num)
theorem B687757 : Blo 405769 687757 := bbase (se 3 (by rfl) ⟨128954, by rfl⟩ : syracuseStep 687757 = 257909) (by norm_num)
theorem B458401 : Blo 405769 458401 := bbase (se 2 (by rfl) ⟨171900, by rfl⟩ : syracuseStep 458401 = 343801) (by norm_num)
theorem B458437 : Blo 405769 458437 := bbase (se 4 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 458437 = 85957) (by norm_num)
theorem B917189 : Blo 405769 917189 := bbase (se 4 (by rfl) ⟨85986, by rfl⟩ : syracuseStep 917189 = 171973) (by norm_num)
theorem B687845 : Blo 405769 687845 := bbase (se 4 (by rfl) ⟨64485, by rfl⟩ : syracuseStep 687845 = 128971) (by norm_num)
theorem B1375973 : Blo 405769 1375973 := bbase (se 4 (by rfl) ⟨128997, by rfl⟩ : syracuseStep 1375973 = 257995) (by norm_num)
theorem B458473 : Blo 405769 458473 := bbase (se 2 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 458473 = 343855) (by norm_num)
theorem B786181 : Blo 405769 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B458509 : Blo 405769 458509 := bbase (se 3 (by rfl) ⟨85970, by rfl⟩ : syracuseStep 458509 = 171941) (by norm_num)
theorem B917261 : Blo 405769 917261 := bbase (se 3 (by rfl) ⟨171986, by rfl⟩ : syracuseStep 917261 = 343973) (by norm_num)
theorem B458545 : Blo 405769 458545 := bbase (se 2 (by rfl) ⟨171954, by rfl⟩ : syracuseStep 458545 = 343909) (by norm_num)
theorem B491341 : Blo 405769 491341 := bbase (se 3 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 491341 = 184253) (by norm_num)
theorem B458581 : Blo 405769 458581 := bbase (se 9 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 458581 = 2687) (by norm_num)
theorem B917333 : Blo 405769 917333 := bbase (se 9 (by rfl) ⟨2687, by rfl⟩ : syracuseStep 917333 = 5375) (by norm_num)
theorem B687973 : Blo 405769 687973 := bbase (se 4 (by rfl) ⟨64497, by rfl⟩ : syracuseStep 687973 = 128995) (by norm_num)
theorem B458617 : Blo 405769 458617 := bbase (se 2 (by rfl) ⟨171981, by rfl⟩ : syracuseStep 458617 = 343963) (by norm_num)
theorem B655229 : Blo 405769 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B2326421 : Blo 405769 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B458653 : Blo 405769 458653 := bbase (se 3 (by rfl) ⟨85997, by rfl⟩ : syracuseStep 458653 = 171995) (by norm_num)
theorem B917405 : Blo 405769 917405 := bbase (se 3 (by rfl) ⟨172013, by rfl⟩ : syracuseStep 917405 = 344027) (by norm_num)
theorem B491441 : Blo 405769 491441 := bbase (se 2 (by rfl) ⟨184290, by rfl⟩ : syracuseStep 491441 = 368581) (by norm_num)
theorem B688061 : Blo 405769 688061 := bbase (se 3 (by rfl) ⟨129011, by rfl⟩ : syracuseStep 688061 = 258023) (by norm_num)
theorem B458689 : Blo 405769 458689 := bbase (se 2 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 458689 = 344017) (by norm_num)
theorem B458725 : Blo 405769 458725 := bbase (se 4 (by rfl) ⟨43005, by rfl⟩ : syracuseStep 458725 = 86011) (by norm_num)
theorem B917477 : Blo 405769 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B2621429 : Blo 405769 2621429 := bbase (se 5 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 2621429 = 245759) (by norm_num)
theorem B557057 : Blo 405769 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B917585 : Blo 405769 917585 := bstep (se 2 (by rfl) ⟨344094, by rfl⟩ : syracuseStep 917585 = 688189) B688189
theorem B917603 : Blo 405769 917603 := bstep (se 1 (by rfl) ⟨688202, by rfl⟩ : syracuseStep 917603 = 1376405) B1376405
theorem B458851 : Blo 405769 458851 := bstep (se 1 (by rfl) ⟨344138, by rfl⟩ : syracuseStep 458851 = 688277) B688277
theorem B688243 : Blo 405769 688243 := bstep (se 1 (by rfl) ⟨516182, by rfl⟩ : syracuseStep 688243 = 1032365) B1032365
theorem B983171 : Blo 405769 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B1179821 : Blo 405769 1179821 := bstep (se 3 (by rfl) ⟨221216, by rfl⟩ : syracuseStep 1179821 = 442433) B442433
theorem B458995 : Blo 405769 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B688385 : Blo 405769 688385 := bstep (se 2 (by rfl) ⟨258144, by rfl⟩ : syracuseStep 688385 = 516289) B516289
theorem B2064689 : Blo 405769 2064689 := bstep (se 2 (by rfl) ⟨774258, by rfl⟩ : syracuseStep 2064689 = 1548517) B1548517
theorem B4817251 : Blo 405769 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B1376621 : Blo 405769 1376621 := bstep (se 3 (by rfl) ⟨258116, by rfl⟩ : syracuseStep 1376621 = 516233) B516233
theorem B917873 : Blo 405769 917873 := bstep (se 2 (by rfl) ⟨344202, by rfl⟩ : syracuseStep 917873 = 688405) B688405
theorem B688513 : Blo 405769 688513 := bstep (se 2 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 688513 = 516385) B516385
theorem B917891 : Blo 405769 917891 := bstep (se 1 (by rfl) ⟨688418, by rfl⟩ : syracuseStep 917891 = 1376837) B1376837
theorem B459139 : Blo 405769 459139 := bstep (se 1 (by rfl) ⟨344354, by rfl⟩ : syracuseStep 459139 = 688709) B688709
theorem B4391309 : Blo 405769 4391309 := bstep (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) B1646741
theorem B1474957 : Blo 405769 1474957 := bstep (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) B553109
theorem B1376675 : Blo 405769 1376675 := bstep (se 1 (by rfl) ⟨1032506, by rfl⟩ : syracuseStep 1376675 = 2065013) B2065013
theorem B688547 : Blo 405769 688547 := bstep (se 1 (by rfl) ⟨516410, by rfl⟩ : syracuseStep 688547 = 1032821) B1032821
theorem B655793 : Blo 405769 655793 := bstep (se 2 (by rfl) ⟨245922, by rfl⟩ : syracuseStep 655793 = 491845) B491845
theorem B623027 : Blo 405769 623027 := bstep (se 1 (by rfl) ⟨467270, by rfl⟩ : syracuseStep 623027 = 934541) B934541
theorem B459283 : Blo 405769 459283 := bstep (se 1 (by rfl) ⟨344462, by rfl⟩ : syracuseStep 459283 = 688925) B688925
theorem B688675 : Blo 405769 688675 := bstep (se 1 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 688675 = 1033013) B1033013
theorem B1180241 : Blo 405769 1180241 := bstep (se 2 (by rfl) ⟨442590, by rfl⟩ : syracuseStep 1180241 = 885181) B885181
theorem B918161 : Blo 405769 918161 := bstep (se 2 (by rfl) ⟨344310, by rfl⟩ : syracuseStep 918161 = 688621) B688621
theorem B918179 : Blo 405769 918179 := bstep (se 1 (by rfl) ⟨688634, by rfl⟩ : syracuseStep 918179 = 1377269) B1377269
theorem B459427 : Blo 405769 459427 := bstep (se 1 (by rfl) ⟨344570, by rfl⟩ : syracuseStep 459427 = 689141) B689141
theorem B1376945 : Blo 405769 1376945 := bstep (se 2 (by rfl) ⟨516354, by rfl⟩ : syracuseStep 1376945 = 1032709) B1032709
theorem B688817 : Blo 405769 688817 := bstep (se 2 (by rfl) ⟨258306, by rfl⟩ : syracuseStep 688817 = 516613) B516613
theorem B3310321 : Blo 405769 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B983843 : Blo 405769 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B688945 : Blo 405769 688945 := bstep (se 2 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 688945 = 516709) B516709
theorem B459571 : Blo 405769 459571 := bstep (se 1 (by rfl) ⟨344678, by rfl⟩ : syracuseStep 459571 = 689357) B689357
theorem B688979 : Blo 405769 688979 := bstep (se 1 (by rfl) ⟨516734, by rfl⟩ : syracuseStep 688979 = 1033469) B1033469
theorem B918449 : Blo 405769 918449 := bstep (se 2 (by rfl) ⟨344418, by rfl⟩ : syracuseStep 918449 = 688837) B688837
theorem B656305 : Blo 405769 656305 := bstep (se 2 (by rfl) ⟨246114, by rfl⟩ : syracuseStep 656305 = 492229) B492229
theorem B918467 : Blo 405769 918467 := bstep (se 1 (by rfl) ⟨688850, by rfl⟩ : syracuseStep 918467 = 1377701) B1377701
theorem B459715 : Blo 405769 459715 := bstep (se 1 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 459715 = 689573) B689573
theorem B689107 : Blo 405769 689107 := bstep (se 1 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 689107 = 1033661) B1033661
theorem B1868771 : Blo 405769 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B984113 : Blo 405769 984113 := bstep (se 2 (by rfl) ⟨369042, by rfl⟩ : syracuseStep 984113 = 738085) B738085
theorem B459859 : Blo 405769 459859 := bstep (se 1 (by rfl) ⟨344894, by rfl⟩ : syracuseStep 459859 = 689789) B689789
theorem B689249 : Blo 405769 689249 := bstep (se 2 (by rfl) ⟨258468, by rfl⟩ : syracuseStep 689249 = 516937) B516937
theorem B1377485 : Blo 405769 1377485 := bstep (se 3 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 1377485 = 516557) B516557
theorem B918737 : Blo 405769 918737 := bstep (se 2 (by rfl) ⟨344526, by rfl⟩ : syracuseStep 918737 = 689053) B689053
theorem B689377 : Blo 405769 689377 := bstep (se 2 (by rfl) ⟨258516, by rfl⟩ : syracuseStep 689377 = 517033) B517033
theorem B918755 : Blo 405769 918755 := bstep (se 1 (by rfl) ⟨689066, by rfl⟩ : syracuseStep 918755 = 1378133) B1378133
theorem B460003 : Blo 405769 460003 := bstep (se 1 (by rfl) ⟨345002, by rfl⟩ : syracuseStep 460003 = 690005) B690005
theorem B984305 : Blo 405769 984305 := bstep (se 2 (by rfl) ⟨369114, by rfl⟩ : syracuseStep 984305 = 738229) B738229
theorem B1377539 : Blo 405769 1377539 := bstep (se 1 (by rfl) ⟨1033154, by rfl⟩ : syracuseStep 1377539 = 2066309) B2066309
theorem B689411 : Blo 405769 689411 := bstep (se 1 (by rfl) ⟨517058, by rfl⟩ : syracuseStep 689411 = 1034117) B1034117
theorem B5276981 : Blo 405769 5276981 := bstep (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) B494717
theorem B984401 : Blo 405769 984401 := bstep (se 2 (by rfl) ⟨369150, by rfl⟩ : syracuseStep 984401 = 738301) B738301
theorem B460147 : Blo 405769 460147 := bstep (se 1 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 460147 = 690221) B690221
theorem B689539 : Blo 405769 689539 := bstep (se 1 (by rfl) ⟨517154, by rfl⟩ : syracuseStep 689539 = 1034309) B1034309
theorem B1344995 : Blo 405769 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B919025 : Blo 405769 919025 := bstep (se 2 (by rfl) ⟨344634, by rfl⟩ : syracuseStep 919025 = 689269) B689269
theorem B919043 : Blo 405769 919043 := bstep (se 1 (by rfl) ⟨689282, by rfl⟩ : syracuseStep 919043 = 1378565) B1378565
theorem B460291 : Blo 405769 460291 := bstep (se 1 (by rfl) ⟨345218, by rfl⟩ : syracuseStep 460291 = 690437) B690437
theorem B1377809 : Blo 405769 1377809 := bstep (se 2 (by rfl) ⟨516678, by rfl⟩ : syracuseStep 1377809 = 1033357) B1033357
theorem B689681 : Blo 405769 689681 := bstep (se 2 (by rfl) ⟨258630, by rfl⟩ : syracuseStep 689681 = 517261) B517261
theorem B1312291 : Blo 405769 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B1312355 : Blo 405769 1312355 := bstep (se 1 (by rfl) ⟨984266, by rfl⟩ : syracuseStep 1312355 = 1968533) B1968533
theorem B886385 : Blo 405769 886385 := bstep (se 2 (by rfl) ⟨332394, by rfl⟩ : syracuseStep 886385 = 664789) B664789
theorem B689809 : Blo 405769 689809 := bstep (se 2 (by rfl) ⟨258678, by rfl⟩ : syracuseStep 689809 = 517357) B517357
theorem B460435 : Blo 405769 460435 := bstep (se 1 (by rfl) ⟨345326, by rfl⟩ : syracuseStep 460435 = 690653) B690653
theorem B1312433 : Blo 405769 1312433 := bstep (se 2 (by rfl) ⟨492162, by rfl⟩ : syracuseStep 1312433 = 984325) B984325
theorem B689843 : Blo 405769 689843 := bstep (se 1 (by rfl) ⟨517382, by rfl⟩ : syracuseStep 689843 = 1034765) B1034765
theorem B2066147 : Blo 405769 2066147 := bstep (se 1 (by rfl) ⟨1549610, by rfl⟩ : syracuseStep 2066147 = 3099221) B3099221
theorem B919313 : Blo 405769 919313 := bstep (se 2 (by rfl) ⟨344742, by rfl⟩ : syracuseStep 919313 = 689485) B689485
theorem B919331 : Blo 405769 919331 := bstep (se 1 (by rfl) ⟨689498, by rfl⟩ : syracuseStep 919331 = 1378997) B1378997
theorem B460579 : Blo 405769 460579 := bstep (se 1 (by rfl) ⟨345434, by rfl⟩ : syracuseStep 460579 = 690869) B690869
theorem B689971 : Blo 405769 689971 := bstep (se 1 (by rfl) ⟨517478, by rfl⟩ : syracuseStep 689971 = 1034957) B1034957
theorem B1541987 : Blo 405769 1541987 := bstep (se 1 (by rfl) ⟨1156490, by rfl⟩ : syracuseStep 1541987 = 2312981) B2312981
theorem B460723 : Blo 405769 460723 := bstep (se 1 (by rfl) ⟨345542, by rfl⟩ : syracuseStep 460723 = 691085) B691085
theorem B690113 : Blo 405769 690113 := bstep (se 2 (by rfl) ⟨258792, by rfl⟩ : syracuseStep 690113 = 517585) B517585
theorem B3082211 : Blo 405769 3082211 := bstep (se 1 (by rfl) ⟨2311658, by rfl⟩ : syracuseStep 3082211 = 4623317) B4623317
theorem B1378349 : Blo 405769 1378349 := bstep (se 3 (by rfl) ⟨258440, by rfl⟩ : syracuseStep 1378349 = 516881) B516881
theorem B919601 : Blo 405769 919601 := bstep (se 2 (by rfl) ⟨344850, by rfl⟩ : syracuseStep 919601 = 689701) B689701
theorem B690241 : Blo 405769 690241 := bstep (se 2 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 690241 = 517681) B517681
theorem B919619 : Blo 405769 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B460867 : Blo 405769 460867 := bstep (se 1 (by rfl) ⟨345650, by rfl⟩ : syracuseStep 460867 = 691301) B691301
theorem B1378403 : Blo 405769 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B690275 : Blo 405769 690275 := bstep (se 1 (by rfl) ⟨517706, by rfl⟩ : syracuseStep 690275 = 1035413) B1035413
theorem B690403 : Blo 405769 690403 := bstep (se 1 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 690403 = 1035605) B1035605
theorem B919889 : Blo 405769 919889 := bstep (se 2 (by rfl) ⟨344958, by rfl⟩ : syracuseStep 919889 = 689917) B689917
theorem B919907 : Blo 405769 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B1378673 : Blo 405769 1378673 := bstep (se 2 (by rfl) ⟨517002, by rfl⟩ : syracuseStep 1378673 = 1034005) B1034005
theorem B690545 : Blo 405769 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B4065677 : Blo 405769 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B690673 : Blo 405769 690673 := bstep (se 2 (by rfl) ⟨259002, by rfl⟩ : syracuseStep 690673 = 518005) B518005
theorem B2066957 : Blo 405769 2066957 := bstep (se 3 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 2066957 = 775109) B775109
theorem B690707 : Blo 405769 690707 := bstep (se 1 (by rfl) ⟨518030, by rfl⟩ : syracuseStep 690707 = 1036061) B1036061
theorem B1051235 : Blo 405769 1051235 := bstep (se 1 (by rfl) ⟨788426, by rfl⟩ : syracuseStep 1051235 = 1576853) B1576853
theorem B920177 : Blo 405769 920177 := bstep (se 2 (by rfl) ⟨345066, by rfl⟩ : syracuseStep 920177 = 690133) B690133
theorem B920195 : Blo 405769 920195 := bstep (se 1 (by rfl) ⟨690146, by rfl⟩ : syracuseStep 920195 = 1380293) B1380293
theorem B690835 : Blo 405769 690835 := bstep (se 1 (by rfl) ⟨518126, by rfl⟩ : syracuseStep 690835 = 1036253) B1036253
theorem B690977 : Blo 405769 690977 := bstep (se 2 (by rfl) ⟨259116, by rfl⟩ : syracuseStep 690977 = 518233) B518233
theorem B1739555 : Blo 405769 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B1542989 : Blo 405769 1542989 := bstep (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) B578621
theorem B1379213 : Blo 405769 1379213 := bstep (se 3 (by rfl) ⟨258602, by rfl⟩ : syracuseStep 1379213 = 517205) B517205
theorem B920465 : Blo 405769 920465 := bstep (se 2 (by rfl) ⟨345174, by rfl⟩ : syracuseStep 920465 = 690349) B690349
theorem B691105 : Blo 405769 691105 := bstep (se 2 (by rfl) ⟨259164, by rfl⟩ : syracuseStep 691105 = 518329) B518329
theorem B920483 : Blo 405769 920483 := bstep (se 1 (by rfl) ⟨690362, by rfl⟩ : syracuseStep 920483 = 1380725) B1380725
theorem B1379267 : Blo 405769 1379267 := bstep (se 1 (by rfl) ⟨1034450, by rfl⟩ : syracuseStep 1379267 = 2068901) B2068901
theorem B691139 : Blo 405769 691139 := bstep (se 1 (by rfl) ⟨518354, by rfl⟩ : syracuseStep 691139 = 1036709) B1036709
theorem B691267 : Blo 405769 691267 := bstep (se 1 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 691267 = 1036901) B1036901
theorem B920753 : Blo 405769 920753 := bstep (se 2 (by rfl) ⟨345282, by rfl⟩ : syracuseStep 920753 = 690565) B690565
theorem B920771 : Blo 405769 920771 := bstep (se 1 (by rfl) ⟨690578, by rfl⟩ : syracuseStep 920771 = 1381157) B1381157
theorem B1379537 : Blo 405769 1379537 := bstep (se 2 (by rfl) ⟨517326, by rfl⟩ : syracuseStep 1379537 = 1034653) B1034653
theorem B691409 : Blo 405769 691409 := bstep (se 2 (by rfl) ⟨259278, by rfl⟩ : syracuseStep 691409 = 518557) B518557
theorem B6950285 : Blo 405769 6950285 := bstep (se 3 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 6950285 = 2606357) B2606357
theorem B921041 : Blo 405769 921041 := bstep (se 2 (by rfl) ⟨345390, by rfl⟩ : syracuseStep 921041 = 690781) B690781
theorem B921059 : Blo 405769 921059 := bstep (se 1 (by rfl) ⟨690794, by rfl⟩ : syracuseStep 921059 = 1381589) B1381589
theorem B1773197 : Blo 405769 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B1380077 : Blo 405769 1380077 := bstep (se 3 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 1380077 = 517529) B517529
theorem B921329 : Blo 405769 921329 := bstep (se 2 (by rfl) ⟨345498, by rfl⟩ : syracuseStep 921329 = 690997) B690997
theorem B921347 : Blo 405769 921347 := bstep (se 1 (by rfl) ⟨691010, by rfl⟩ : syracuseStep 921347 = 1382021) B1382021
theorem B1380131 : Blo 405769 1380131 := bstep (se 1 (by rfl) ⟨1035098, by rfl⟩ : syracuseStep 1380131 = 2070197) B2070197
theorem B8359793 : Blo 405769 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B921617 : Blo 405769 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B921635 : Blo 405769 921635 := bstep (se 1 (by rfl) ⟨691226, by rfl⟩ : syracuseStep 921635 = 1382453) B1382453
theorem B1380401 : Blo 405769 1380401 := bstep (se 2 (by rfl) ⟨517650, by rfl⟩ : syracuseStep 1380401 = 1035301) B1035301
theorem B921905 : Blo 405769 921905 := bstep (se 2 (by rfl) ⟨345714, by rfl⟩ : syracuseStep 921905 = 691429) B691429
theorem B921923 : Blo 405769 921923 := bstep (se 1 (by rfl) ⟨691442, by rfl⟩ : syracuseStep 921923 = 1382885) B1382885
theorem B1741297 : Blo 405769 1741297 := bstep (se 2 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 1741297 = 1305973) B1305973
theorem B463411 : Blo 405769 463411 := bstep (se 1 (by rfl) ⟨347558, by rfl⟩ : syracuseStep 463411 = 695117) B695117
theorem B1380941 : Blo 405769 1380941 := bstep (se 3 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 1380941 = 517853) B517853
theorem B1380995 : Blo 405769 1380995 := bstep (se 1 (by rfl) ⟨1035746, by rfl⟩ : syracuseStep 1380995 = 2071493) B2071493
theorem B1545101 : Blo 405769 1545101 := bstep (se 3 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 1545101 = 579413) B579413
theorem B1381265 : Blo 405769 1381265 := bstep (se 2 (by rfl) ⟨517974, by rfl⟩ : syracuseStep 1381265 = 1035949) B1035949
theorem B2266289 : Blo 405769 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B1742029 : Blo 405769 1742029 := bstep (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) B653261
theorem B2069873 : Blo 405769 2069873 := bstep (se 2 (by rfl) ⟨776202, by rfl⟩ : syracuseStep 2069873 = 1552405) B1552405
theorem B12719501 : Blo 405769 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1381805 : Blo 405769 1381805 := bstep (se 3 (by rfl) ⟨259088, by rfl⟩ : syracuseStep 1381805 = 518177) B518177
theorem B1381859 : Blo 405769 1381859 := bstep (se 1 (by rfl) ⟨1036394, by rfl⟩ : syracuseStep 1381859 = 2072789) B2072789
theorem B1545905 : Blo 405769 1545905 := bstep (se 2 (by rfl) ⟨579714, by rfl⟩ : syracuseStep 1545905 = 1159429) B1159429
theorem B1382129 : Blo 405769 1382129 := bstep (se 2 (by rfl) ⟨518298, by rfl⟩ : syracuseStep 1382129 = 1036597) B1036597
theorem B628913 : Blo 405769 628913 := bstep (se 2 (by rfl) ⟨235842, by rfl⟩ : syracuseStep 628913 = 471685) B471685
theorem B1382669 : Blo 405769 1382669 := bstep (se 3 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 1382669 = 518501) B518501
theorem B1382723 : Blo 405769 1382723 := bstep (se 1 (by rfl) ⟨1037042, by rfl⟩ : syracuseStep 1382723 = 2074085) B2074085
theorem B1546573 : Blo 405769 1546573 := bstep (se 3 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 1546573 = 579965) B579965
theorem B1743245 : Blo 405769 1743245 := bstep (se 3 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 1743245 = 653717) B653717
theorem B2791907 : Blo 405769 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B8854069 : Blo 405769 8854069 := bstep (se 5 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 8854069 = 830069) B830069
theorem B629507 : Blo 405769 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B2071331 : Blo 405769 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B3152837 : Blo 405769 3152837 := bstep (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) B591157
theorem B1547363 : Blo 405769 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B3087557 : Blo 405769 3087557 := bstep (se 4 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 3087557 = 578917) B578917
theorem B695555 : Blo 405769 695555 := bstep (se 1 (by rfl) ⟨521666, by rfl⟩ : syracuseStep 695555 = 1043333) B1043333
theorem B695569 : Blo 405769 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B5217635 : Blo 405769 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B433603 : Blo 405769 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B3481157 : Blo 405769 3481157 := bstep (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) B652717
theorem B2072141 : Blo 405769 2072141 := bstep (se 3 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 2072141 = 777053) B777053
theorem B1548017 : Blo 405769 1548017 := bstep (se 2 (by rfl) ⟨580506, by rfl⟩ : syracuseStep 1548017 = 1161013) B1161013
theorem B3710861 : Blo 405769 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B827491 : Blo 405769 827491 := bstep (se 1 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 827491 = 1241237) B1241237
theorem B5022179 : Blo 405769 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B631523 : Blo 405769 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B1549475 : Blo 405769 1549475 := bstep (se 1 (by rfl) ⟨1162106, by rfl⟩ : syracuseStep 1549475 = 2324213) B2324213
theorem B1549489 : Blo 405769 1549489 := bstep (se 2 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 1549489 = 1162117) B1162117
theorem B828643 : Blo 405769 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B927281 : Blo 405769 927281 := bstep (se 2 (by rfl) ⟨347730, by rfl⟩ : syracuseStep 927281 = 695461) B695461
theorem B894691 : Blo 405769 894691 := bstep (se 1 (by rfl) ⟨671018, by rfl⟩ : syracuseStep 894691 = 1342037) B1342037
theorem B1156913 : Blo 405769 1156913 := bstep (se 2 (by rfl) ⟨433842, by rfl⟩ : syracuseStep 1156913 = 867685) B867685
theorem B1157105 : Blo 405769 1157105 := bstep (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) B867829
theorem B731281 : Blo 405769 731281 := bstep (se 2 (by rfl) ⟨274230, by rfl⟩ : syracuseStep 731281 = 548461) B548461
theorem B1747277 : Blo 405769 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B1550947 : Blo 405769 1550947 := bstep (se 1 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 1550947 = 2326421) B2326421
theorem B1747619 : Blo 405769 1747619 := bstep (se 1 (by rfl) ⟨1310714, by rfl⟩ : syracuseStep 1747619 = 2621429) B2621429
theorem B731857 : Blo 405769 731857 := bstep (se 2 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 731857 = 548893) B548893
theorem B437123 : Blo 405769 437123 := bstep (se 1 (by rfl) ⟨327842, by rfl⟩ : syracuseStep 437123 = 655685) B655685
theorem B699313 : Blo 405769 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B1158097 : Blo 405769 1158097 := bstep (se 2 (by rfl) ⟨434286, by rfl⟩ : syracuseStep 1158097 = 868573) B868573
theorem B994403 : Blo 405769 994403 := bstep (se 1 (by rfl) ⟨745802, by rfl⟩ : syracuseStep 994403 = 1491605) B1491605
theorem B1748081 : Blo 405769 1748081 := bstep (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) B1311061
theorem B1158371 : Blo 405769 1158371 := bstep (se 1 (by rfl) ⟨868778, by rfl⟩ : syracuseStep 1158371 = 1737557) B1737557
theorem B1027313 : Blo 405769 1027313 := bstep (se 2 (by rfl) ⟨385242, by rfl⟩ : syracuseStep 1027313 = 770485) B770485
theorem B1027363 : Blo 405769 1027363 := bstep (se 1 (by rfl) ⟨770522, by rfl⟩ : syracuseStep 1027363 = 1541045) B1541045
theorem B2600261 : Blo 405769 2600261 := bstep (se 4 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 2600261 = 487549) B487549
theorem B1158563 : Blo 405769 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B1027505 : Blo 405769 1027505 := bstep (se 2 (by rfl) ⟨385314, by rfl⟩ : syracuseStep 1027505 = 770629) B770629
theorem B3321485 : Blo 405769 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B1060547 : Blo 405769 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B732881 : Blo 405769 732881 := bstep (se 2 (by rfl) ⟨274830, by rfl⟩ : syracuseStep 732881 = 549661) B549661
theorem B700193 : Blo 405769 700193 := bstep (se 2 (by rfl) ⟨262572, by rfl⟩ : syracuseStep 700193 = 525145) B525145
theorem B733169 : Blo 405769 733169 := bstep (se 2 (by rfl) ⟨274938, by rfl⟩ : syracuseStep 733169 = 549877) B549877
theorem B1290289 : Blo 405769 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B1159373 : Blo 405769 1159373 := bstep (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) B434765
theorem B405779 : Blo 405769 405779 := bstep (se 1 (by rfl) ⟨304334, by rfl⟩ : syracuseStep 405779 = 608669) B608669
theorem B405795 : Blo 405769 405795 := bstep (se 1 (by rfl) ⟨304346, by rfl⟩ : syracuseStep 405795 = 608693) B608693
theorem B405811 : Blo 405769 405811 := bstep (se 1 (by rfl) ⟨304358, by rfl⟩ : syracuseStep 405811 = 608717) B608717
theorem B405827 : Blo 405769 405827 := bstep (se 1 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 405827 = 608741) B608741
theorem B405843 : Blo 405769 405843 := bstep (se 1 (by rfl) ⟨304382, by rfl⟩ : syracuseStep 405843 = 608765) B608765
theorem B405859 : Blo 405769 405859 := bstep (se 1 (by rfl) ⟨304394, by rfl⟩ : syracuseStep 405859 = 608789) B608789
theorem B405875 : Blo 405769 405875 := bstep (se 1 (by rfl) ⟨304406, by rfl⟩ : syracuseStep 405875 = 608813) B608813
theorem B405891 : Blo 405769 405891 := bstep (se 1 (by rfl) ⟨304418, by rfl⟩ : syracuseStep 405891 = 608837) B608837
theorem B1159555 : Blo 405769 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B2470285 : Blo 405769 2470285 := bstep (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) B926357
theorem B1028497 : Blo 405769 1028497 := bstep (se 2 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 1028497 = 771373) B771373
theorem B405907 : Blo 405769 405907 := bstep (se 1 (by rfl) ⟨304430, by rfl⟩ : syracuseStep 405907 = 608861) B608861
theorem B405923 : Blo 405769 405923 := bstep (se 1 (by rfl) ⟨304442, by rfl⟩ : syracuseStep 405923 = 608885) B608885
theorem B405939 : Blo 405769 405939 := bstep (se 1 (by rfl) ⟨304454, by rfl⟩ : syracuseStep 405939 = 608909) B608909
theorem B405955 : Blo 405769 405955 := bstep (se 1 (by rfl) ⟨304466, by rfl⟩ : syracuseStep 405955 = 608933) B608933
theorem B405971 : Blo 405769 405971 := bstep (se 1 (by rfl) ⟨304478, by rfl⟩ : syracuseStep 405971 = 608957) B608957
theorem B405987 : Blo 405769 405987 := bstep (se 1 (by rfl) ⟨304490, by rfl⟩ : syracuseStep 405987 = 608981) B608981
theorem B406003 : Blo 405769 406003 := bstep (se 1 (by rfl) ⟨304502, by rfl⟩ : syracuseStep 406003 = 609005) B609005
theorem B406019 : Blo 405769 406019 := bstep (se 1 (by rfl) ⟨304514, by rfl⟩ : syracuseStep 406019 = 609029) B609029
theorem B406035 : Blo 405769 406035 := bstep (se 1 (by rfl) ⟨304526, by rfl⟩ : syracuseStep 406035 = 609053) B609053
theorem B406051 : Blo 405769 406051 := bstep (se 1 (by rfl) ⟨304538, by rfl⟩ : syracuseStep 406051 = 609077) B609077
theorem B406067 : Blo 405769 406067 := bstep (se 1 (by rfl) ⟨304550, by rfl⟩ : syracuseStep 406067 = 609101) B609101
theorem B406083 : Blo 405769 406083 := bstep (se 1 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 406083 = 609125) B609125
theorem B406099 : Blo 405769 406099 := bstep (se 1 (by rfl) ⟨304574, by rfl⟩ : syracuseStep 406099 = 609149) B609149
theorem B406115 : Blo 405769 406115 := bstep (se 1 (by rfl) ⟨304586, by rfl⟩ : syracuseStep 406115 = 609173) B609173
theorem B406131 : Blo 405769 406131 := bstep (se 1 (by rfl) ⟨304598, by rfl⟩ : syracuseStep 406131 = 609197) B609197
theorem B406147 : Blo 405769 406147 := bstep (se 1 (by rfl) ⟨304610, by rfl⟩ : syracuseStep 406147 = 609221) B609221
theorem B406163 : Blo 405769 406163 := bstep (se 1 (by rfl) ⟨304622, by rfl⟩ : syracuseStep 406163 = 609245) B609245
theorem B406179 : Blo 405769 406179 := bstep (se 1 (by rfl) ⟨304634, by rfl⟩ : syracuseStep 406179 = 609269) B609269
theorem B1028771 : Blo 405769 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B406195 : Blo 405769 406195 := bstep (se 1 (by rfl) ⟨304646, by rfl⟩ : syracuseStep 406195 = 609293) B609293
theorem B406211 : Blo 405769 406211 := bstep (se 1 (by rfl) ⟨304658, by rfl⟩ : syracuseStep 406211 = 609317) B609317
theorem B406227 : Blo 405769 406227 := bstep (se 1 (by rfl) ⟨304670, by rfl⟩ : syracuseStep 406227 = 609341) B609341
theorem B406243 : Blo 405769 406243 := bstep (se 1 (by rfl) ⟨304682, by rfl⟩ : syracuseStep 406243 = 609365) B609365
theorem B406259 : Blo 405769 406259 := bstep (se 1 (by rfl) ⟨304694, by rfl⟩ : syracuseStep 406259 = 609389) B609389
theorem B406275 : Blo 405769 406275 := bstep (se 1 (by rfl) ⟨304706, by rfl⟩ : syracuseStep 406275 = 609413) B609413
theorem B3912461 : Blo 405769 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B1553165 : Blo 405769 1553165 := bstep (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) B582437
theorem B406291 : Blo 405769 406291 := bstep (se 1 (by rfl) ⟨304718, by rfl⟩ : syracuseStep 406291 = 609437) B609437
theorem B406307 : Blo 405769 406307 := bstep (se 1 (by rfl) ⟨304730, by rfl⟩ : syracuseStep 406307 = 609461) B609461
theorem B406323 : Blo 405769 406323 := bstep (se 1 (by rfl) ⟨304742, by rfl⟩ : syracuseStep 406323 = 609485) B609485
theorem B406339 : Blo 405769 406339 := bstep (se 1 (by rfl) ⟨304754, by rfl⟩ : syracuseStep 406339 = 609509) B609509
theorem B406355 : Blo 405769 406355 := bstep (se 1 (by rfl) ⟨304766, by rfl⟩ : syracuseStep 406355 = 609533) B609533
theorem B406371 : Blo 405769 406371 := bstep (se 1 (by rfl) ⟨304778, by rfl⟩ : syracuseStep 406371 = 609557) B609557
theorem B1028963 : Blo 405769 1028963 := bstep (se 1 (by rfl) ⟨771722, by rfl⟩ : syracuseStep 1028963 = 1543445) B1543445
theorem B1160045 : Blo 405769 1160045 := bstep (se 3 (by rfl) ⟨217508, by rfl⟩ : syracuseStep 1160045 = 435017) B435017
theorem B406387 : Blo 405769 406387 := bstep (se 1 (by rfl) ⟨304790, by rfl⟩ : syracuseStep 406387 = 609581) B609581
theorem B406403 : Blo 405769 406403 := bstep (se 1 (by rfl) ⟨304802, by rfl⟩ : syracuseStep 406403 = 609605) B609605
theorem B3093389 : Blo 405769 3093389 := bstep (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) B1160021
theorem B406419 : Blo 405769 406419 := bstep (se 1 (by rfl) ⟨304814, by rfl⟩ : syracuseStep 406419 = 609629) B609629
theorem B406435 : Blo 405769 406435 := bstep (se 1 (by rfl) ⟨304826, by rfl⟩ : syracuseStep 406435 = 609653) B609653
theorem B406451 : Blo 405769 406451 := bstep (se 1 (by rfl) ⟨304838, by rfl⟩ : syracuseStep 406451 = 609677) B609677
theorem B406467 : Blo 405769 406467 := bstep (se 1 (by rfl) ⟨304850, by rfl⟩ : syracuseStep 406467 = 609701) B609701
theorem B406483 : Blo 405769 406483 := bstep (se 1 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 406483 = 609725) B609725
theorem B406499 : Blo 405769 406499 := bstep (se 1 (by rfl) ⟨304874, by rfl⟩ : syracuseStep 406499 = 609749) B609749
theorem B406515 : Blo 405769 406515 := bstep (se 1 (by rfl) ⟨304886, by rfl⟩ : syracuseStep 406515 = 609773) B609773
theorem B406531 : Blo 405769 406531 := bstep (se 1 (by rfl) ⟨304898, by rfl⟩ : syracuseStep 406531 = 609797) B609797
theorem B406547 : Blo 405769 406547 := bstep (se 1 (by rfl) ⟨304910, by rfl⟩ : syracuseStep 406547 = 609821) B609821
theorem B406563 : Blo 405769 406563 := bstep (se 1 (by rfl) ⟨304922, by rfl⟩ : syracuseStep 406563 = 609845) B609845
theorem B406579 : Blo 405769 406579 := bstep (se 1 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 406579 = 609869) B609869
theorem B406595 : Blo 405769 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B406611 : Blo 405769 406611 := bstep (se 1 (by rfl) ⟨304958, by rfl⟩ : syracuseStep 406611 = 609917) B609917
theorem B406627 : Blo 405769 406627 := bstep (se 1 (by rfl) ⟨304970, by rfl⟩ : syracuseStep 406627 = 609941) B609941
theorem B406643 : Blo 405769 406643 := bstep (se 1 (by rfl) ⟨304982, by rfl⟩ : syracuseStep 406643 = 609965) B609965
theorem B406659 : Blo 405769 406659 := bstep (se 1 (by rfl) ⟨304994, by rfl⟩ : syracuseStep 406659 = 609989) B609989
theorem B406675 : Blo 405769 406675 := bstep (se 1 (by rfl) ⟨305006, by rfl⟩ : syracuseStep 406675 = 610013) B610013
theorem B406691 : Blo 405769 406691 := bstep (se 1 (by rfl) ⟨305018, by rfl⟩ : syracuseStep 406691 = 610037) B610037
theorem B406707 : Blo 405769 406707 := bstep (se 1 (by rfl) ⟨305030, by rfl⟩ : syracuseStep 406707 = 610061) B610061
theorem B406723 : Blo 405769 406723 := bstep (se 1 (by rfl) ⟨305042, by rfl⟩ : syracuseStep 406723 = 610085) B610085
theorem B734417 : Blo 405769 734417 := bstep (se 2 (by rfl) ⟨275406, by rfl⟩ : syracuseStep 734417 = 550813) B550813
theorem B406739 : Blo 405769 406739 := bstep (se 1 (by rfl) ⟨305054, by rfl⟩ : syracuseStep 406739 = 610109) B610109
theorem B406755 : Blo 405769 406755 := bstep (se 1 (by rfl) ⟨305066, by rfl⟩ : syracuseStep 406755 = 610133) B610133
theorem B406771 : Blo 405769 406771 := bstep (se 1 (by rfl) ⟨305078, by rfl⟩ : syracuseStep 406771 = 610157) B610157
theorem B406787 : Blo 405769 406787 := bstep (se 1 (by rfl) ⟨305090, by rfl⟩ : syracuseStep 406787 = 610181) B610181
theorem B406803 : Blo 405769 406803 := bstep (se 1 (by rfl) ⟨305102, by rfl⟩ : syracuseStep 406803 = 610205) B610205
theorem B406819 : Blo 405769 406819 := bstep (se 1 (by rfl) ⟨305114, by rfl⟩ : syracuseStep 406819 = 610229) B610229
theorem B406835 : Blo 405769 406835 := bstep (se 1 (by rfl) ⟨305126, by rfl⟩ : syracuseStep 406835 = 610253) B610253
theorem B406851 : Blo 405769 406851 := bstep (se 1 (by rfl) ⟨305138, by rfl⟩ : syracuseStep 406851 = 610277) B610277
theorem B406867 : Blo 405769 406867 := bstep (se 1 (by rfl) ⟨305150, by rfl⟩ : syracuseStep 406867 = 610301) B610301
theorem B406883 : Blo 405769 406883 := bstep (se 1 (by rfl) ⟨305162, by rfl⟩ : syracuseStep 406883 = 610325) B610325
theorem B406899 : Blo 405769 406899 := bstep (se 1 (by rfl) ⟨305174, by rfl⟩ : syracuseStep 406899 = 610349) B610349
theorem B406915 : Blo 405769 406915 := bstep (se 1 (by rfl) ⟨305186, by rfl⟩ : syracuseStep 406915 = 610373) B610373
theorem B406931 : Blo 405769 406931 := bstep (se 1 (by rfl) ⟨305198, by rfl⟩ : syracuseStep 406931 = 610397) B610397
theorem B406947 : Blo 405769 406947 := bstep (se 1 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 406947 = 610421) B610421
theorem B406963 : Blo 405769 406963 := bstep (se 1 (by rfl) ⟨305222, by rfl⟩ : syracuseStep 406963 = 610445) B610445
theorem B406979 : Blo 405769 406979 := bstep (se 1 (by rfl) ⟨305234, by rfl⟩ : syracuseStep 406979 = 610469) B610469
theorem B406995 : Blo 405769 406995 := bstep (se 1 (by rfl) ⟨305246, by rfl⟩ : syracuseStep 406995 = 610493) B610493
theorem B407011 : Blo 405769 407011 := bstep (se 1 (by rfl) ⟨305258, by rfl⟩ : syracuseStep 407011 = 610517) B610517
theorem B407027 : Blo 405769 407027 := bstep (se 1 (by rfl) ⟨305270, by rfl⟩ : syracuseStep 407027 = 610541) B610541
theorem B407043 : Blo 405769 407043 := bstep (se 1 (by rfl) ⟨305282, by rfl⟩ : syracuseStep 407043 = 610565) B610565
theorem B407059 : Blo 405769 407059 := bstep (se 1 (by rfl) ⟨305294, by rfl⟩ : syracuseStep 407059 = 610589) B610589
theorem B407075 : Blo 405769 407075 := bstep (se 1 (by rfl) ⟨305306, by rfl⟩ : syracuseStep 407075 = 610613) B610613
theorem B407091 : Blo 405769 407091 := bstep (se 1 (by rfl) ⟨305318, by rfl⟩ : syracuseStep 407091 = 610637) B610637
theorem B407107 : Blo 405769 407107 := bstep (se 1 (by rfl) ⟨305330, by rfl⟩ : syracuseStep 407107 = 610661) B610661
theorem B407123 : Blo 405769 407123 := bstep (se 1 (by rfl) ⟨305342, by rfl⟩ : syracuseStep 407123 = 610685) B610685
theorem B407139 : Blo 405769 407139 := bstep (se 1 (by rfl) ⟨305354, by rfl⟩ : syracuseStep 407139 = 610709) B610709
theorem B407155 : Blo 405769 407155 := bstep (se 1 (by rfl) ⟨305366, by rfl⟩ : syracuseStep 407155 = 610733) B610733
theorem B407171 : Blo 405769 407171 := bstep (se 1 (by rfl) ⟨305378, by rfl⟩ : syracuseStep 407171 = 610757) B610757
theorem B407187 : Blo 405769 407187 := bstep (se 1 (by rfl) ⟨305390, by rfl⟩ : syracuseStep 407187 = 610781) B610781
theorem B407203 : Blo 405769 407203 := bstep (se 1 (by rfl) ⟨305402, by rfl⟩ : syracuseStep 407203 = 610805) B610805
theorem B407219 : Blo 405769 407219 := bstep (se 1 (by rfl) ⟨305414, by rfl⟩ : syracuseStep 407219 = 610829) B610829
theorem B407235 : Blo 405769 407235 := bstep (se 1 (by rfl) ⟨305426, by rfl⟩ : syracuseStep 407235 = 610853) B610853
theorem B407251 : Blo 405769 407251 := bstep (se 1 (by rfl) ⟨305438, by rfl⟩ : syracuseStep 407251 = 610877) B610877
theorem B407267 : Blo 405769 407267 := bstep (se 1 (by rfl) ⟨305450, by rfl⟩ : syracuseStep 407267 = 610901) B610901
theorem B407283 : Blo 405769 407283 := bstep (se 1 (by rfl) ⟨305462, by rfl⟩ : syracuseStep 407283 = 610925) B610925
theorem B407299 : Blo 405769 407299 := bstep (se 1 (by rfl) ⟨305474, by rfl⟩ : syracuseStep 407299 = 610949) B610949
theorem B1029905 : Blo 405769 1029905 := bstep (se 2 (by rfl) ⟨386214, by rfl⟩ : syracuseStep 1029905 = 772429) B772429
theorem B407315 : Blo 405769 407315 := bstep (se 1 (by rfl) ⟨305486, by rfl⟩ : syracuseStep 407315 = 610973) B610973
theorem B407331 : Blo 405769 407331 := bstep (se 1 (by rfl) ⟨305498, by rfl⟩ : syracuseStep 407331 = 610997) B610997
theorem B407347 : Blo 405769 407347 := bstep (se 1 (by rfl) ⟨305510, by rfl⟩ : syracuseStep 407347 = 611021) B611021
theorem B1029955 : Blo 405769 1029955 := bstep (se 1 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 1029955 = 1544933) B1544933
theorem B407363 : Blo 405769 407363 := bstep (se 1 (by rfl) ⟨305522, by rfl⟩ : syracuseStep 407363 = 611045) B611045
theorem B407379 : Blo 405769 407379 := bstep (se 1 (by rfl) ⟨305534, by rfl⟩ : syracuseStep 407379 = 611069) B611069
theorem B407395 : Blo 405769 407395 := bstep (se 1 (by rfl) ⟨305546, by rfl⟩ : syracuseStep 407395 = 611093) B611093
theorem B407411 : Blo 405769 407411 := bstep (se 1 (by rfl) ⟨305558, by rfl⟩ : syracuseStep 407411 = 611117) B611117
theorem B407427 : Blo 405769 407427 := bstep (se 1 (by rfl) ⟨305570, by rfl⟩ : syracuseStep 407427 = 611141) B611141
theorem B407443 : Blo 405769 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B407459 : Blo 405769 407459 := bstep (se 1 (by rfl) ⟨305594, by rfl⟩ : syracuseStep 407459 = 611189) B611189
theorem B407475 : Blo 405769 407475 := bstep (se 1 (by rfl) ⟨305606, by rfl⟩ : syracuseStep 407475 = 611213) B611213
theorem B407491 : Blo 405769 407491 := bstep (se 1 (by rfl) ⟨305618, by rfl⟩ : syracuseStep 407491 = 611237) B611237
theorem B1030097 : Blo 405769 1030097 := bstep (se 2 (by rfl) ⟨386286, by rfl⟩ : syracuseStep 1030097 = 772573) B772573
theorem B407507 : Blo 405769 407507 := bstep (se 1 (by rfl) ⟨305630, by rfl⟩ : syracuseStep 407507 = 611261) B611261
theorem B407523 : Blo 405769 407523 := bstep (se 1 (by rfl) ⟨305642, by rfl⟩ : syracuseStep 407523 = 611285) B611285
theorem B407539 : Blo 405769 407539 := bstep (se 1 (by rfl) ⟨305654, by rfl⟩ : syracuseStep 407539 = 611309) B611309
theorem B407555 : Blo 405769 407555 := bstep (se 1 (by rfl) ⟨305666, by rfl⟩ : syracuseStep 407555 = 611333) B611333
theorem B1161229 : Blo 405769 1161229 := bstep (se 3 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 1161229 = 435461) B435461
theorem B407571 : Blo 405769 407571 := bstep (se 1 (by rfl) ⟨305678, by rfl⟩ : syracuseStep 407571 = 611357) B611357
theorem B407587 : Blo 405769 407587 := bstep (se 1 (by rfl) ⟨305690, by rfl⟩ : syracuseStep 407587 = 611381) B611381
theorem B407603 : Blo 405769 407603 := bstep (se 1 (by rfl) ⟨305702, by rfl⟩ : syracuseStep 407603 = 611405) B611405
theorem B407619 : Blo 405769 407619 := bstep (se 1 (by rfl) ⟨305714, by rfl⟩ : syracuseStep 407619 = 611429) B611429
theorem B407635 : Blo 405769 407635 := bstep (se 1 (by rfl) ⟨305726, by rfl⟩ : syracuseStep 407635 = 611453) B611453
theorem B407651 : Blo 405769 407651 := bstep (se 1 (by rfl) ⟨305738, by rfl⟩ : syracuseStep 407651 = 611477) B611477
theorem B407667 : Blo 405769 407667 := bstep (se 1 (by rfl) ⟨305750, by rfl⟩ : syracuseStep 407667 = 611501) B611501
theorem B407683 : Blo 405769 407683 := bstep (se 1 (by rfl) ⟨305762, by rfl⟩ : syracuseStep 407683 = 611525) B611525
theorem B407699 : Blo 405769 407699 := bstep (se 1 (by rfl) ⟨305774, by rfl⟩ : syracuseStep 407699 = 611549) B611549
theorem B407715 : Blo 405769 407715 := bstep (se 1 (by rfl) ⟨305786, by rfl⟩ : syracuseStep 407715 = 611573) B611573
theorem B407731 : Blo 405769 407731 := bstep (se 1 (by rfl) ⟨305798, by rfl⟩ : syracuseStep 407731 = 611597) B611597
theorem B407747 : Blo 405769 407747 := bstep (se 1 (by rfl) ⟨305810, by rfl⟩ : syracuseStep 407747 = 611621) B611621
theorem B407763 : Blo 405769 407763 := bstep (se 1 (by rfl) ⟨305822, by rfl⟩ : syracuseStep 407763 = 611645) B611645
theorem B407779 : Blo 405769 407779 := bstep (se 1 (by rfl) ⟨305834, by rfl⟩ : syracuseStep 407779 = 611669) B611669
theorem B407795 : Blo 405769 407795 := bstep (se 1 (by rfl) ⟨305846, by rfl⟩ : syracuseStep 407795 = 611693) B611693
theorem B407811 : Blo 405769 407811 := bstep (se 1 (by rfl) ⟨305858, by rfl⟩ : syracuseStep 407811 = 611717) B611717
theorem B407827 : Blo 405769 407827 := bstep (se 1 (by rfl) ⟨305870, by rfl⟩ : syracuseStep 407827 = 611741) B611741
theorem B407843 : Blo 405769 407843 := bstep (se 1 (by rfl) ⟨305882, by rfl⟩ : syracuseStep 407843 = 611765) B611765
theorem B407859 : Blo 405769 407859 := bstep (se 1 (by rfl) ⟨305894, by rfl⟩ : syracuseStep 407859 = 611789) B611789
theorem B407875 : Blo 405769 407875 := bstep (se 1 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 407875 = 611813) B611813
theorem B407891 : Blo 405769 407891 := bstep (se 1 (by rfl) ⟨305918, by rfl⟩ : syracuseStep 407891 = 611837) B611837
theorem B407907 : Blo 405769 407907 := bstep (se 1 (by rfl) ⟨305930, by rfl⟩ : syracuseStep 407907 = 611861) B611861
theorem B407923 : Blo 405769 407923 := bstep (se 1 (by rfl) ⟨305942, by rfl⟩ : syracuseStep 407923 = 611885) B611885
theorem B407939 : Blo 405769 407939 := bstep (se 1 (by rfl) ⟨305954, by rfl⟩ : syracuseStep 407939 = 611909) B611909
theorem B407955 : Blo 405769 407955 := bstep (se 1 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 407955 = 611933) B611933
theorem B407971 : Blo 405769 407971 := bstep (se 1 (by rfl) ⟨305978, by rfl⟩ : syracuseStep 407971 = 611957) B611957
theorem B407987 : Blo 405769 407987 := bstep (se 1 (by rfl) ⟨305990, by rfl⟩ : syracuseStep 407987 = 611981) B611981
theorem B408003 : Blo 405769 408003 := bstep (se 1 (by rfl) ⟨306002, by rfl⟩ : syracuseStep 408003 = 612005) B612005
theorem B408019 : Blo 405769 408019 := bstep (se 1 (by rfl) ⟨306014, by rfl⟩ : syracuseStep 408019 = 612029) B612029
theorem B408035 : Blo 405769 408035 := bstep (se 1 (by rfl) ⟨306026, by rfl⟩ : syracuseStep 408035 = 612053) B612053
theorem B408051 : Blo 405769 408051 := bstep (se 1 (by rfl) ⟨306038, by rfl⟩ : syracuseStep 408051 = 612077) B612077
theorem B408067 : Blo 405769 408067 := bstep (se 1 (by rfl) ⟨306050, by rfl⟩ : syracuseStep 408067 = 612101) B612101
theorem B408083 : Blo 405769 408083 := bstep (se 1 (by rfl) ⟨306062, by rfl⟩ : syracuseStep 408083 = 612125) B612125
theorem B408099 : Blo 405769 408099 := bstep (se 1 (by rfl) ⟨306074, by rfl⟩ : syracuseStep 408099 = 612149) B612149
theorem B408115 : Blo 405769 408115 := bstep (se 1 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 408115 = 612173) B612173
theorem B408131 : Blo 405769 408131 := bstep (se 1 (by rfl) ⟨306098, by rfl⟩ : syracuseStep 408131 = 612197) B612197
theorem B408147 : Blo 405769 408147 := bstep (se 1 (by rfl) ⟨306110, by rfl⟩ : syracuseStep 408147 = 612221) B612221
theorem B408163 : Blo 405769 408163 := bstep (se 1 (by rfl) ⟨306122, by rfl⟩ : syracuseStep 408163 = 612245) B612245
theorem B408179 : Blo 405769 408179 := bstep (se 1 (by rfl) ⟨306134, by rfl⟩ : syracuseStep 408179 = 612269) B612269
theorem B408195 : Blo 405769 408195 := bstep (se 1 (by rfl) ⟨306146, by rfl⟩ : syracuseStep 408195 = 612293) B612293
theorem B408211 : Blo 405769 408211 := bstep (se 1 (by rfl) ⟨306158, by rfl⟩ : syracuseStep 408211 = 612317) B612317
theorem B408227 : Blo 405769 408227 := bstep (se 1 (by rfl) ⟨306170, by rfl⟩ : syracuseStep 408227 = 612341) B612341
theorem B408243 : Blo 405769 408243 := bstep (se 1 (by rfl) ⟨306182, by rfl⟩ : syracuseStep 408243 = 612365) B612365
theorem B408259 : Blo 405769 408259 := bstep (se 1 (by rfl) ⟨306194, by rfl⟩ : syracuseStep 408259 = 612389) B612389
theorem B408275 : Blo 405769 408275 := bstep (se 1 (by rfl) ⟨306206, by rfl⟩ : syracuseStep 408275 = 612413) B612413
theorem B1653475 : Blo 405769 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B408291 : Blo 405769 408291 := bstep (se 1 (by rfl) ⟨306218, by rfl⟩ : syracuseStep 408291 = 612437) B612437
theorem B408307 : Blo 405769 408307 := bstep (se 1 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 408307 = 612461) B612461
theorem B408323 : Blo 405769 408323 := bstep (se 1 (by rfl) ⟨306242, by rfl⟩ : syracuseStep 408323 = 612485) B612485
theorem B408339 : Blo 405769 408339 := bstep (se 1 (by rfl) ⟨306254, by rfl⟩ : syracuseStep 408339 = 612509) B612509
theorem B408355 : Blo 405769 408355 := bstep (se 1 (by rfl) ⟨306266, by rfl⟩ : syracuseStep 408355 = 612533) B612533
theorem B408371 : Blo 405769 408371 := bstep (se 1 (by rfl) ⟨306278, by rfl⟩ : syracuseStep 408371 = 612557) B612557
theorem B408387 : Blo 405769 408387 := bstep (se 1 (by rfl) ⟨306290, by rfl⟩ : syracuseStep 408387 = 612581) B612581
theorem B408403 : Blo 405769 408403 := bstep (se 1 (by rfl) ⟨306302, by rfl⟩ : syracuseStep 408403 = 612605) B612605
theorem B408419 : Blo 405769 408419 := bstep (se 1 (by rfl) ⟨306314, by rfl⟩ : syracuseStep 408419 = 612629) B612629
theorem B408435 : Blo 405769 408435 := bstep (se 1 (by rfl) ⟨306326, by rfl⟩ : syracuseStep 408435 = 612653) B612653
theorem B408451 : Blo 405769 408451 := bstep (se 1 (by rfl) ⟨306338, by rfl⟩ : syracuseStep 408451 = 612677) B612677
theorem B408467 : Blo 405769 408467 := bstep (se 1 (by rfl) ⟨306350, by rfl⟩ : syracuseStep 408467 = 612701) B612701
theorem B408483 : Blo 405769 408483 := bstep (se 1 (by rfl) ⟨306362, by rfl⟩ : syracuseStep 408483 = 612725) B612725
theorem B1031089 : Blo 405769 1031089 := bstep (se 2 (by rfl) ⟨386658, by rfl⟩ : syracuseStep 1031089 = 773317) B773317
theorem B408499 : Blo 405769 408499 := bstep (se 1 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 408499 = 612749) B612749
theorem B408515 : Blo 405769 408515 := bstep (se 1 (by rfl) ⟨306386, by rfl⟩ : syracuseStep 408515 = 612773) B612773
theorem B408531 : Blo 405769 408531 := bstep (se 1 (by rfl) ⟨306398, by rfl⟩ : syracuseStep 408531 = 612797) B612797
theorem B408547 : Blo 405769 408547 := bstep (se 1 (by rfl) ⟨306410, by rfl⟩ : syracuseStep 408547 = 612821) B612821
theorem B408563 : Blo 405769 408563 := bstep (se 1 (by rfl) ⟨306422, by rfl⟩ : syracuseStep 408563 = 612845) B612845
theorem B408579 : Blo 405769 408579 := bstep (se 1 (by rfl) ⟨306434, by rfl⟩ : syracuseStep 408579 = 612869) B612869
theorem B408595 : Blo 405769 408595 := bstep (se 1 (by rfl) ⟨306446, by rfl⟩ : syracuseStep 408595 = 612893) B612893
theorem B408611 : Blo 405769 408611 := bstep (se 1 (by rfl) ⟨306458, by rfl⟩ : syracuseStep 408611 = 612917) B612917
theorem B1162289 : Blo 405769 1162289 := bstep (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) B871717
theorem B408627 : Blo 405769 408627 := bstep (se 1 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 408627 = 612941) B612941
theorem B408643 : Blo 405769 408643 := bstep (se 1 (by rfl) ⟨306482, by rfl⟩ : syracuseStep 408643 = 612965) B612965
theorem B408659 : Blo 405769 408659 := bstep (se 1 (by rfl) ⟨306494, by rfl⟩ : syracuseStep 408659 = 612989) B612989
theorem B408675 : Blo 405769 408675 := bstep (se 1 (by rfl) ⟨306506, by rfl⟩ : syracuseStep 408675 = 613013) B613013
theorem B408691 : Blo 405769 408691 := bstep (se 1 (by rfl) ⟨306518, by rfl⟩ : syracuseStep 408691 = 613037) B613037
theorem B408707 : Blo 405769 408707 := bstep (se 1 (by rfl) ⟨306530, by rfl⟩ : syracuseStep 408707 = 613061) B613061
theorem B408723 : Blo 405769 408723 := bstep (se 1 (by rfl) ⟨306542, by rfl⟩ : syracuseStep 408723 = 613085) B613085
theorem B408739 : Blo 405769 408739 := bstep (se 1 (by rfl) ⟨306554, by rfl⟩ : syracuseStep 408739 = 613109) B613109
theorem B867505 : Blo 405769 867505 := bstep (se 2 (by rfl) ⟨325314, by rfl⟩ : syracuseStep 867505 = 650629) B650629
theorem B408755 : Blo 405769 408755 := bstep (se 1 (by rfl) ⟨306566, by rfl⟩ : syracuseStep 408755 = 613133) B613133
theorem B1031363 : Blo 405769 1031363 := bstep (se 1 (by rfl) ⟨773522, by rfl⟩ : syracuseStep 1031363 = 1547045) B1547045
theorem B408771 : Blo 405769 408771 := bstep (se 1 (by rfl) ⟨306578, by rfl⟩ : syracuseStep 408771 = 613157) B613157
theorem B408787 : Blo 405769 408787 := bstep (se 1 (by rfl) ⟨306590, by rfl⟩ : syracuseStep 408787 = 613181) B613181
theorem B408803 : Blo 405769 408803 := bstep (se 1 (by rfl) ⟨306602, by rfl⟩ : syracuseStep 408803 = 613205) B613205
theorem B408819 : Blo 405769 408819 := bstep (se 1 (by rfl) ⟨306614, by rfl⟩ : syracuseStep 408819 = 613229) B613229
theorem B408835 : Blo 405769 408835 := bstep (se 1 (by rfl) ⟨306626, by rfl⟩ : syracuseStep 408835 = 613253) B613253
theorem B408851 : Blo 405769 408851 := bstep (se 1 (by rfl) ⟨306638, by rfl⟩ : syracuseStep 408851 = 613277) B613277
theorem B408867 : Blo 405769 408867 := bstep (se 1 (by rfl) ⟨306650, by rfl⟩ : syracuseStep 408867 = 613301) B613301
theorem B408883 : Blo 405769 408883 := bstep (se 1 (by rfl) ⟨306662, by rfl⟩ : syracuseStep 408883 = 613325) B613325
theorem B408899 : Blo 405769 408899 := bstep (se 1 (by rfl) ⟨306674, by rfl⟩ : syracuseStep 408899 = 613349) B613349
theorem B408915 : Blo 405769 408915 := bstep (se 1 (by rfl) ⟨306686, by rfl⟩ : syracuseStep 408915 = 613373) B613373
theorem B408931 : Blo 405769 408931 := bstep (se 1 (by rfl) ⟨306698, by rfl⟩ : syracuseStep 408931 = 613397) B613397
theorem B408947 : Blo 405769 408947 := bstep (se 1 (by rfl) ⟨306710, by rfl⟩ : syracuseStep 408947 = 613421) B613421
theorem B1031555 : Blo 405769 1031555 := bstep (se 1 (by rfl) ⟨773666, by rfl⟩ : syracuseStep 1031555 = 1547333) B1547333
theorem B408963 : Blo 405769 408963 := bstep (se 1 (by rfl) ⟨306722, by rfl⟩ : syracuseStep 408963 = 613445) B613445
theorem B408979 : Blo 405769 408979 := bstep (se 1 (by rfl) ⟨306734, by rfl⟩ : syracuseStep 408979 = 613469) B613469
theorem B408995 : Blo 405769 408995 := bstep (se 1 (by rfl) ⟨306746, by rfl⟩ : syracuseStep 408995 = 613493) B613493
theorem B867761 : Blo 405769 867761 := bstep (se 2 (by rfl) ⟨325410, by rfl⟩ : syracuseStep 867761 = 650821) B650821
theorem B409011 : Blo 405769 409011 := bstep (se 1 (by rfl) ⟨306758, by rfl⟩ : syracuseStep 409011 = 613517) B613517
theorem B409027 : Blo 405769 409027 := bstep (se 1 (by rfl) ⟨306770, by rfl⟩ : syracuseStep 409027 = 613541) B613541
theorem B409043 : Blo 405769 409043 := bstep (se 1 (by rfl) ⟨306782, by rfl⟩ : syracuseStep 409043 = 613565) B613565
theorem B409059 : Blo 405769 409059 := bstep (se 1 (by rfl) ⟨306794, by rfl⟩ : syracuseStep 409059 = 613589) B613589
theorem B409075 : Blo 405769 409075 := bstep (se 1 (by rfl) ⟨306806, by rfl⟩ : syracuseStep 409075 = 613613) B613613
theorem B409091 : Blo 405769 409091 := bstep (se 1 (by rfl) ⟨306818, by rfl⟩ : syracuseStep 409091 = 613637) B613637
theorem B409107 : Blo 405769 409107 := bstep (se 1 (by rfl) ⟨306830, by rfl⟩ : syracuseStep 409107 = 613661) B613661
theorem B409123 : Blo 405769 409123 := bstep (se 1 (by rfl) ⟨306842, by rfl⟩ : syracuseStep 409123 = 613685) B613685
theorem B409139 : Blo 405769 409139 := bstep (se 1 (by rfl) ⟨306854, by rfl⟩ : syracuseStep 409139 = 613709) B613709
theorem B409155 : Blo 405769 409155 := bstep (se 1 (by rfl) ⟨306866, by rfl⟩ : syracuseStep 409155 = 613733) B613733
theorem B409171 : Blo 405769 409171 := bstep (se 1 (by rfl) ⟨306878, by rfl⟩ : syracuseStep 409171 = 613757) B613757
theorem B409187 : Blo 405769 409187 := bstep (se 1 (by rfl) ⟨306890, by rfl⟩ : syracuseStep 409187 = 613781) B613781
theorem B409203 : Blo 405769 409203 := bstep (se 1 (by rfl) ⟨306902, by rfl⟩ : syracuseStep 409203 = 613805) B613805
theorem B409219 : Blo 405769 409219 := bstep (se 1 (by rfl) ⟨306914, by rfl⟩ : syracuseStep 409219 = 613829) B613829
theorem B409235 : Blo 405769 409235 := bstep (se 1 (by rfl) ⟨306926, by rfl⟩ : syracuseStep 409235 = 613853) B613853
theorem B409251 : Blo 405769 409251 := bstep (se 1 (by rfl) ⟨306938, by rfl⟩ : syracuseStep 409251 = 613877) B613877
theorem B409267 : Blo 405769 409267 := bstep (se 1 (by rfl) ⟨306950, by rfl⟩ : syracuseStep 409267 = 613901) B613901
theorem B409283 : Blo 405769 409283 := bstep (se 1 (by rfl) ⟨306962, by rfl⟩ : syracuseStep 409283 = 613925) B613925
theorem B1162961 : Blo 405769 1162961 := bstep (se 2 (by rfl) ⟨436110, by rfl⟩ : syracuseStep 1162961 = 872221) B872221
theorem B409299 : Blo 405769 409299 := bstep (se 1 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 409299 = 613949) B613949
theorem B409315 : Blo 405769 409315 := bstep (se 1 (by rfl) ⟨306986, by rfl⟩ : syracuseStep 409315 = 613973) B613973
theorem B3096305 : Blo 405769 3096305 := bstep (se 2 (by rfl) ⟨1161114, by rfl⟩ : syracuseStep 3096305 = 2322229) B2322229
theorem B409331 : Blo 405769 409331 := bstep (se 1 (by rfl) ⟨306998, by rfl⟩ : syracuseStep 409331 = 613997) B613997
theorem B409347 : Blo 405769 409347 := bstep (se 1 (by rfl) ⟨307010, by rfl⟩ : syracuseStep 409347 = 614021) B614021
theorem B409363 : Blo 405769 409363 := bstep (se 1 (by rfl) ⟨307022, by rfl⟩ : syracuseStep 409363 = 614045) B614045
theorem B409379 : Blo 405769 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B409395 : Blo 405769 409395 := bstep (se 1 (by rfl) ⟨307046, by rfl⟩ : syracuseStep 409395 = 614093) B614093
theorem B409411 : Blo 405769 409411 := bstep (se 1 (by rfl) ⟨307058, by rfl⟩ : syracuseStep 409411 = 614117) B614117
theorem B409427 : Blo 405769 409427 := bstep (se 1 (by rfl) ⟨307070, by rfl⟩ : syracuseStep 409427 = 614141) B614141
theorem B2604899 : Blo 405769 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B409443 : Blo 405769 409443 := bstep (se 1 (by rfl) ⟨307082, by rfl⟩ : syracuseStep 409443 = 614165) B614165
theorem B409459 : Blo 405769 409459 := bstep (se 1 (by rfl) ⟨307094, by rfl⟩ : syracuseStep 409459 = 614189) B614189
theorem B409475 : Blo 405769 409475 := bstep (se 1 (by rfl) ⟨307106, by rfl⟩ : syracuseStep 409475 = 614213) B614213
theorem B2211725 : Blo 405769 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B409491 : Blo 405769 409491 := bstep (se 1 (by rfl) ⟨307118, by rfl⟩ : syracuseStep 409491 = 614237) B614237
theorem B409507 : Blo 405769 409507 := bstep (se 1 (by rfl) ⟨307130, by rfl⟩ : syracuseStep 409507 = 614261) B614261
theorem B409523 : Blo 405769 409523 := bstep (se 1 (by rfl) ⟨307142, by rfl⟩ : syracuseStep 409523 = 614285) B614285
theorem B409539 : Blo 405769 409539 := bstep (se 1 (by rfl) ⟨307154, by rfl⟩ : syracuseStep 409539 = 614309) B614309
theorem B409555 : Blo 405769 409555 := bstep (se 1 (by rfl) ⟨307166, by rfl⟩ : syracuseStep 409555 = 614333) B614333
theorem B409571 : Blo 405769 409571 := bstep (se 1 (by rfl) ⟨307178, by rfl⟩ : syracuseStep 409571 = 614357) B614357
theorem B409587 : Blo 405769 409587 := bstep (se 1 (by rfl) ⟨307190, by rfl⟩ : syracuseStep 409587 = 614381) B614381
theorem B409603 : Blo 405769 409603 := bstep (se 1 (by rfl) ⟨307202, by rfl⟩ : syracuseStep 409603 = 614405) B614405
theorem B409619 : Blo 405769 409619 := bstep (se 1 (by rfl) ⟨307214, by rfl⟩ : syracuseStep 409619 = 614429) B614429
theorem B409635 : Blo 405769 409635 := bstep (se 1 (by rfl) ⟨307226, by rfl⟩ : syracuseStep 409635 = 614453) B614453
theorem B409651 : Blo 405769 409651 := bstep (se 1 (by rfl) ⟨307238, by rfl⟩ : syracuseStep 409651 = 614477) B614477
theorem B409667 : Blo 405769 409667 := bstep (se 1 (by rfl) ⟨307250, by rfl⟩ : syracuseStep 409667 = 614501) B614501
theorem B409683 : Blo 405769 409683 := bstep (se 1 (by rfl) ⟨307262, by rfl⟩ : syracuseStep 409683 = 614525) B614525
theorem B409699 : Blo 405769 409699 := bstep (se 1 (by rfl) ⟨307274, by rfl⟩ : syracuseStep 409699 = 614549) B614549
theorem B3489905 : Blo 405769 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B409715 : Blo 405769 409715 := bstep (se 1 (by rfl) ⟨307286, by rfl⟩ : syracuseStep 409715 = 614573) B614573
theorem B409731 : Blo 405769 409731 := bstep (se 1 (by rfl) ⟨307298, by rfl⟩ : syracuseStep 409731 = 614597) B614597
theorem B409747 : Blo 405769 409747 := bstep (se 1 (by rfl) ⟨307310, by rfl⟩ : syracuseStep 409747 = 614621) B614621
theorem B409763 : Blo 405769 409763 := bstep (se 1 (by rfl) ⟨307322, by rfl⟩ : syracuseStep 409763 = 614645) B614645
theorem B1032497 : Blo 405769 1032497 := bstep (se 2 (by rfl) ⟨387186, by rfl⟩ : syracuseStep 1032497 = 774373) B774373
theorem B1032547 : Blo 405769 1032547 := bstep (se 1 (by rfl) ⟨774410, by rfl⟩ : syracuseStep 1032547 = 1548821) B1548821
theorem B1163747 : Blo 405769 1163747 := bstep (se 1 (by rfl) ⟨872810, by rfl⟩ : syracuseStep 1163747 = 1745621) B1745621
theorem B1032689 : Blo 405769 1032689 := bstep (se 2 (by rfl) ⟨387258, by rfl⟩ : syracuseStep 1032689 = 774517) B774517
theorem B770705 : Blo 405769 770705 := bstep (se 2 (by rfl) ⟨289014, by rfl⟩ : syracuseStep 770705 = 578029) B578029
theorem B869059 : Blo 405769 869059 := bstep (se 1 (by rfl) ⟨651794, by rfl⟩ : syracuseStep 869059 = 1303589) B1303589
theorem B1164077 : Blo 405769 1164077 := bstep (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) B436529
theorem B1295153 : Blo 405769 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B2245475 : Blo 405769 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B1164145 : Blo 405769 1164145 := bstep (se 2 (by rfl) ⟨436554, by rfl⟩ : syracuseStep 1164145 = 873109) B873109
theorem B869393 : Blo 405769 869393 := bstep (se 2 (by rfl) ⟨326022, by rfl⟩ : syracuseStep 869393 = 652045) B652045
theorem B1262659 : Blo 405769 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B1098865 : Blo 405769 1098865 := bstep (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) B824149
theorem B1164419 : Blo 405769 1164419 := bstep (se 1 (by rfl) ⟨873314, by rfl⟩ : syracuseStep 1164419 = 1746629) B1746629
theorem B1950925 : Blo 405769 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B2311523 : Blo 405769 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B1852877 : Blo 405769 1852877 := bstep (se 3 (by rfl) ⟨347414, by rfl⟩ : syracuseStep 1852877 = 694829) B694829
theorem B1033681 : Blo 405769 1033681 := bstep (se 2 (by rfl) ⟨387630, by rfl⟩ : syracuseStep 1033681 = 775261) B775261
theorem B673283 : Blo 405769 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B771601 : Blo 405769 771601 := bstep (se 2 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 771601 = 578701) B578701
theorem B771761 : Blo 405769 771761 := bstep (se 2 (by rfl) ⟨289410, by rfl⟩ : syracuseStep 771761 = 578821) B578821
theorem B1033955 : Blo 405769 1033955 := bstep (se 1 (by rfl) ⟨775466, by rfl⟩ : syracuseStep 1033955 = 1550933) B1550933
theorem B1951523 : Blo 405769 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B411491 : Blo 405769 411491 := bstep (se 1 (by rfl) ⟨308618, by rfl⟩ : syracuseStep 411491 = 617237) B617237
theorem B10405745 : Blo 405769 10405745 := bstep (se 2 (by rfl) ⟨3902154, by rfl⟩ : syracuseStep 10405745 = 7804309) B7804309
theorem B1034147 : Blo 405769 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B2607025 : Blo 405769 2607025 := bstep (se 2 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 2607025 = 1955269) B1955269
theorem B1165261 : Blo 405769 1165261 := bstep (se 3 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 1165261 = 436973) B436973
theorem B2639843 : Blo 405769 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B772163 : Blo 405769 772163 := bstep (se 1 (by rfl) ⟨579122, by rfl⟩ : syracuseStep 772163 = 1158245) B1158245
theorem B1165421 : Blo 405769 1165421 := bstep (se 3 (by rfl) ⟨218516, by rfl⟩ : syracuseStep 1165421 = 437033) B437033
theorem B870563 : Blo 405769 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B706801 : Blo 405769 706801 := bstep (se 2 (by rfl) ⟨265050, by rfl⟩ : syracuseStep 706801 = 530101) B530101
theorem B1165603 : Blo 405769 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B608657 : Blo 405769 608657 := bstep (se 2 (by rfl) ⟨228246, by rfl⟩ : syracuseStep 608657 = 456493) B456493
theorem B608675 : Blo 405769 608675 := bstep (se 1 (by rfl) ⟨456506, by rfl⟩ : syracuseStep 608675 = 913013) B913013
theorem B608705 : Blo 405769 608705 := bstep (se 2 (by rfl) ⟨228264, by rfl⟩ : syracuseStep 608705 = 456529) B456529
theorem B608723 : Blo 405769 608723 := bstep (se 1 (by rfl) ⟨456542, by rfl⟩ : syracuseStep 608723 = 913085) B913085
theorem B608753 : Blo 405769 608753 := bstep (se 2 (by rfl) ⟨228282, by rfl⟩ : syracuseStep 608753 = 456565) B456565
theorem B608771 : Blo 405769 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B608801 : Blo 405769 608801 := bstep (se 2 (by rfl) ⟨228300, by rfl⟩ : syracuseStep 608801 = 456601) B456601
theorem B608819 : Blo 405769 608819 := bstep (se 1 (by rfl) ⟨456614, by rfl⟩ : syracuseStep 608819 = 913229) B913229
theorem B608849 : Blo 405769 608849 := bstep (se 2 (by rfl) ⟨228318, by rfl⟩ : syracuseStep 608849 = 456637) B456637
theorem B608867 : Blo 405769 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B608897 : Blo 405769 608897 := bstep (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) B456673
theorem B608915 : Blo 405769 608915 := bstep (se 1 (by rfl) ⟨456686, by rfl⟩ : syracuseStep 608915 = 913373) B913373
theorem B608945 : Blo 405769 608945 := bstep (se 2 (by rfl) ⟨228354, by rfl⟩ : syracuseStep 608945 = 456709) B456709
theorem B608963 : Blo 405769 608963 := bstep (se 1 (by rfl) ⟨456722, by rfl⟩ : syracuseStep 608963 = 913445) B913445
theorem B608993 : Blo 405769 608993 := bstep (se 2 (by rfl) ⟨228372, by rfl⟩ : syracuseStep 608993 = 456745) B456745
theorem B609011 : Blo 405769 609011 := bstep (se 1 (by rfl) ⟨456758, by rfl⟩ : syracuseStep 609011 = 913517) B913517
theorem B609041 : Blo 405769 609041 := bstep (se 2 (by rfl) ⟨228390, by rfl⟩ : syracuseStep 609041 = 456781) B456781
theorem B609059 : Blo 405769 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B609089 : Blo 405769 609089 := bstep (se 2 (by rfl) ⟨228408, by rfl⟩ : syracuseStep 609089 = 456817) B456817
theorem B1035089 : Blo 405769 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B609107 : Blo 405769 609107 := bstep (se 1 (by rfl) ⟨456830, by rfl⟩ : syracuseStep 609107 = 913661) B913661
theorem B609137 : Blo 405769 609137 := bstep (se 2 (by rfl) ⟨228426, by rfl⟩ : syracuseStep 609137 = 456853) B456853
theorem B609155 : Blo 405769 609155 := bstep (se 1 (by rfl) ⟨456866, by rfl⟩ : syracuseStep 609155 = 913733) B913733
theorem B1035139 : Blo 405769 1035139 := bstep (se 1 (by rfl) ⟨776354, by rfl⟩ : syracuseStep 1035139 = 1552709) B1552709
theorem B609185 : Blo 405769 609185 := bstep (se 2 (by rfl) ⟨228444, by rfl⟩ : syracuseStep 609185 = 456889) B456889
theorem B609203 : Blo 405769 609203 := bstep (se 1 (by rfl) ⟨456902, by rfl⟩ : syracuseStep 609203 = 913805) B913805
theorem B773059 : Blo 405769 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B609233 : Blo 405769 609233 := bstep (se 2 (by rfl) ⟨228462, by rfl⟩ : syracuseStep 609233 = 456925) B456925
theorem B609251 : Blo 405769 609251 := bstep (se 1 (by rfl) ⟨456938, by rfl⟩ : syracuseStep 609251 = 913877) B913877
theorem B609281 : Blo 405769 609281 := bstep (se 2 (by rfl) ⟨228480, by rfl⟩ : syracuseStep 609281 = 456961) B456961
theorem B1035281 : Blo 405769 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B609299 : Blo 405769 609299 := bstep (se 1 (by rfl) ⟨456974, by rfl⟩ : syracuseStep 609299 = 913949) B913949
theorem B1428515 : Blo 405769 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B609329 : Blo 405769 609329 := bstep (se 2 (by rfl) ⟨228498, by rfl⟩ : syracuseStep 609329 = 456997) B456997
theorem B609347 : Blo 405769 609347 := bstep (se 1 (by rfl) ⟨457010, by rfl⟩ : syracuseStep 609347 = 914021) B914021
theorem B609377 : Blo 405769 609377 := bstep (se 2 (by rfl) ⟨228516, by rfl⟩ : syracuseStep 609377 = 457033) B457033
theorem B773219 : Blo 405769 773219 := bstep (se 1 (by rfl) ⟨579914, by rfl⟩ : syracuseStep 773219 = 1159829) B1159829
theorem B609395 : Blo 405769 609395 := bstep (se 1 (by rfl) ⟨457046, by rfl⟩ : syracuseStep 609395 = 914093) B914093
theorem B1100941 : Blo 405769 1100941 := bstep (se 3 (by rfl) ⟨206426, by rfl⟩ : syracuseStep 1100941 = 412853) B412853
theorem B609425 : Blo 405769 609425 := bstep (se 2 (by rfl) ⟨228534, by rfl⟩ : syracuseStep 609425 = 457069) B457069
theorem B609443 : Blo 405769 609443 := bstep (se 1 (by rfl) ⟨457082, by rfl⟩ : syracuseStep 609443 = 914165) B914165
theorem B609473 : Blo 405769 609473 := bstep (se 2 (by rfl) ⟨228552, by rfl⟩ : syracuseStep 609473 = 457105) B457105
theorem B609491 : Blo 405769 609491 := bstep (se 1 (by rfl) ⟨457118, by rfl⟩ : syracuseStep 609491 = 914237) B914237
theorem B609521 : Blo 405769 609521 := bstep (se 2 (by rfl) ⟨228570, by rfl⟩ : syracuseStep 609521 = 457141) B457141
theorem B609539 : Blo 405769 609539 := bstep (se 1 (by rfl) ⟨457154, by rfl⟩ : syracuseStep 609539 = 914309) B914309
theorem B609569 : Blo 405769 609569 := bstep (se 2 (by rfl) ⟨228588, by rfl⟩ : syracuseStep 609569 = 457177) B457177
theorem B609587 : Blo 405769 609587 := bstep (se 1 (by rfl) ⟨457190, by rfl⟩ : syracuseStep 609587 = 914381) B914381
theorem B609617 : Blo 405769 609617 := bstep (se 2 (by rfl) ⟨228606, by rfl⟩ : syracuseStep 609617 = 457213) B457213
theorem B609635 : Blo 405769 609635 := bstep (se 1 (by rfl) ⟨457226, by rfl⟩ : syracuseStep 609635 = 914453) B914453
theorem B609665 : Blo 405769 609665 := bstep (se 2 (by rfl) ⟨228624, by rfl⟩ : syracuseStep 609665 = 457249) B457249
theorem B609683 : Blo 405769 609683 := bstep (se 1 (by rfl) ⟨457262, by rfl⟩ : syracuseStep 609683 = 914525) B914525
theorem B609713 : Blo 405769 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B609731 : Blo 405769 609731 := bstep (se 1 (by rfl) ⟨457298, by rfl⟩ : syracuseStep 609731 = 914597) B914597
theorem B609761 : Blo 405769 609761 := bstep (se 2 (by rfl) ⟨228660, by rfl⟩ : syracuseStep 609761 = 457321) B457321
theorem B609779 : Blo 405769 609779 := bstep (se 1 (by rfl) ⟨457334, by rfl⟩ : syracuseStep 609779 = 914669) B914669
theorem B609809 : Blo 405769 609809 := bstep (se 2 (by rfl) ⟨228678, by rfl⟩ : syracuseStep 609809 = 457357) B457357
theorem B609827 : Blo 405769 609827 := bstep (se 1 (by rfl) ⟨457370, by rfl⟩ : syracuseStep 609827 = 914741) B914741
theorem B609857 : Blo 405769 609857 := bstep (se 2 (by rfl) ⟨228696, by rfl⟩ : syracuseStep 609857 = 457393) B457393
theorem B609875 : Blo 405769 609875 := bstep (se 1 (by rfl) ⟨457406, by rfl⟩ : syracuseStep 609875 = 914813) B914813
theorem B609905 : Blo 405769 609905 := bstep (se 2 (by rfl) ⟨228714, by rfl⟩ : syracuseStep 609905 = 457429) B457429
theorem B609923 : Blo 405769 609923 := bstep (se 1 (by rfl) ⟨457442, by rfl⟩ : syracuseStep 609923 = 914885) B914885
theorem B609953 : Blo 405769 609953 := bstep (se 2 (by rfl) ⟨228732, by rfl⟩ : syracuseStep 609953 = 457465) B457465
theorem B609971 : Blo 405769 609971 := bstep (se 1 (by rfl) ⟨457478, by rfl⟩ : syracuseStep 609971 = 914957) B914957
theorem B610001 : Blo 405769 610001 := bstep (se 2 (by rfl) ⟨228750, by rfl⟩ : syracuseStep 610001 = 457501) B457501
theorem B19910357 : Blo 405769 19910357 := bstep (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) B466649
theorem B610019 : Blo 405769 610019 := bstep (se 1 (by rfl) ⟨457514, by rfl⟩ : syracuseStep 610019 = 915029) B915029
theorem B610049 : Blo 405769 610049 := bstep (se 2 (by rfl) ⟨228768, by rfl⟩ : syracuseStep 610049 = 457537) B457537
theorem B610067 : Blo 405769 610067 := bstep (se 1 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 610067 = 915101) B915101
theorem B610097 : Blo 405769 610097 := bstep (se 2 (by rfl) ⟨228786, by rfl⟩ : syracuseStep 610097 = 457573) B457573
theorem B610115 : Blo 405769 610115 := bstep (se 1 (by rfl) ⟨457586, by rfl⟩ : syracuseStep 610115 = 915173) B915173
theorem B610145 : Blo 405769 610145 := bstep (se 2 (by rfl) ⟨228804, by rfl⟩ : syracuseStep 610145 = 457609) B457609
theorem B610163 : Blo 405769 610163 := bstep (se 1 (by rfl) ⟨457622, by rfl⟩ : syracuseStep 610163 = 915245) B915245
theorem B610193 : Blo 405769 610193 := bstep (se 2 (by rfl) ⟨228822, by rfl⟩ : syracuseStep 610193 = 457645) B457645
theorem B610211 : Blo 405769 610211 := bstep (se 1 (by rfl) ⟨457658, by rfl⟩ : syracuseStep 610211 = 915317) B915317
theorem B610241 : Blo 405769 610241 := bstep (se 2 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 610241 = 457681) B457681
theorem B610259 : Blo 405769 610259 := bstep (se 1 (by rfl) ⟨457694, by rfl⟩ : syracuseStep 610259 = 915389) B915389
theorem B610289 : Blo 405769 610289 := bstep (se 2 (by rfl) ⟨228858, by rfl⟩ : syracuseStep 610289 = 457717) B457717
theorem B1036273 : Blo 405769 1036273 := bstep (se 2 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 1036273 = 777205) B777205
theorem B610307 : Blo 405769 610307 := bstep (se 1 (by rfl) ⟨457730, by rfl⟩ : syracuseStep 610307 = 915461) B915461
theorem B610337 : Blo 405769 610337 := bstep (se 2 (by rfl) ⟨228876, by rfl⟩ : syracuseStep 610337 = 457753) B457753
theorem B610355 : Blo 405769 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B610385 : Blo 405769 610385 := bstep (se 2 (by rfl) ⟨228894, by rfl⟩ : syracuseStep 610385 = 457789) B457789
theorem B610403 : Blo 405769 610403 := bstep (se 1 (by rfl) ⟨457802, by rfl⟩ : syracuseStep 610403 = 915605) B915605
theorem B5656675 : Blo 405769 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B1101937 : Blo 405769 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B610433 : Blo 405769 610433 := bstep (se 2 (by rfl) ⟨228912, by rfl⟩ : syracuseStep 610433 = 457825) B457825
theorem B872579 : Blo 405769 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B774289 : Blo 405769 774289 := bstep (se 2 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 774289 = 580717) B580717
theorem B610451 : Blo 405769 610451 := bstep (se 1 (by rfl) ⟨457838, by rfl⟩ : syracuseStep 610451 = 915677) B915677
theorem B413843 : Blo 405769 413843 := bstep (se 1 (by rfl) ⟨310382, by rfl⟩ : syracuseStep 413843 = 620765) B620765
theorem B610481 : Blo 405769 610481 := bstep (se 2 (by rfl) ⟨228930, by rfl⟩ : syracuseStep 610481 = 457861) B457861
theorem B413875 : Blo 405769 413875 := bstep (se 1 (by rfl) ⟨310406, by rfl⟩ : syracuseStep 413875 = 620813) B620813
theorem B610499 : Blo 405769 610499 := bstep (se 1 (by rfl) ⟨457874, by rfl⟩ : syracuseStep 610499 = 915749) B915749
theorem B610529 : Blo 405769 610529 := bstep (se 2 (by rfl) ⟨228948, by rfl⟩ : syracuseStep 610529 = 457897) B457897
theorem B2937059 : Blo 405769 2937059 := bstep (se 1 (by rfl) ⟨2202794, by rfl⟩ : syracuseStep 2937059 = 4405589) B4405589
theorem B610547 : Blo 405769 610547 := bstep (se 1 (by rfl) ⟨457910, by rfl⟩ : syracuseStep 610547 = 915821) B915821
theorem B1036547 : Blo 405769 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B610577 : Blo 405769 610577 := bstep (se 2 (by rfl) ⟨228966, by rfl⟩ : syracuseStep 610577 = 457933) B457933
theorem B610595 : Blo 405769 610595 := bstep (se 1 (by rfl) ⟨457946, by rfl⟩ : syracuseStep 610595 = 915893) B915893
theorem B610625 : Blo 405769 610625 := bstep (se 2 (by rfl) ⟨228984, by rfl⟩ : syracuseStep 610625 = 457969) B457969
theorem B610643 : Blo 405769 610643 := bstep (se 1 (by rfl) ⟨457982, by rfl⟩ : syracuseStep 610643 = 915965) B915965
theorem B3297635 : Blo 405769 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B610673 : Blo 405769 610673 := bstep (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) B458005
theorem B610691 : Blo 405769 610691 := bstep (se 1 (by rfl) ⟨458018, by rfl⟩ : syracuseStep 610691 = 916037) B916037
theorem B610721 : Blo 405769 610721 := bstep (se 2 (by rfl) ⟨229020, by rfl⟩ : syracuseStep 610721 = 458041) B458041
theorem B577955 : Blo 405769 577955 := bstep (se 1 (by rfl) ⟨433466, by rfl⟩ : syracuseStep 577955 = 866933) B866933
theorem B610739 : Blo 405769 610739 := bstep (se 1 (by rfl) ⟨458054, by rfl⟩ : syracuseStep 610739 = 916109) B916109
theorem B1036739 : Blo 405769 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B610769 : Blo 405769 610769 := bstep (se 2 (by rfl) ⟨229038, by rfl⟩ : syracuseStep 610769 = 458077) B458077
theorem B610787 : Blo 405769 610787 := bstep (se 1 (by rfl) ⟨458090, by rfl⟩ : syracuseStep 610787 = 916181) B916181
theorem B610817 : Blo 405769 610817 := bstep (se 2 (by rfl) ⟨229056, by rfl⟩ : syracuseStep 610817 = 458113) B458113
theorem B2314757 : Blo 405769 2314757 := bstep (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) B434017
theorem B610835 : Blo 405769 610835 := bstep (se 1 (by rfl) ⟨458126, by rfl⟩ : syracuseStep 610835 = 916253) B916253
theorem B610865 : Blo 405769 610865 := bstep (se 2 (by rfl) ⟨229074, by rfl⟩ : syracuseStep 610865 = 458149) B458149
theorem B610883 : Blo 405769 610883 := bstep (se 1 (by rfl) ⟨458162, by rfl⟩ : syracuseStep 610883 = 916325) B916325
theorem B1102403 : Blo 405769 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B610913 : Blo 405769 610913 := bstep (se 2 (by rfl) ⟨229092, by rfl⟩ : syracuseStep 610913 = 458185) B458185
theorem B610931 : Blo 405769 610931 := bstep (se 1 (by rfl) ⟨458198, by rfl⟩ : syracuseStep 610931 = 916397) B916397
theorem B610961 : Blo 405769 610961 := bstep (se 2 (by rfl) ⟨229110, by rfl⟩ : syracuseStep 610961 = 458221) B458221
theorem B610979 : Blo 405769 610979 := bstep (se 1 (by rfl) ⟨458234, by rfl⟩ : syracuseStep 610979 = 916469) B916469
theorem B1102499 : Blo 405769 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B611009 : Blo 405769 611009 := bstep (se 2 (by rfl) ⟨229128, by rfl⟩ : syracuseStep 611009 = 458257) B458257
theorem B611027 : Blo 405769 611027 := bstep (se 1 (by rfl) ⟨458270, by rfl⟩ : syracuseStep 611027 = 916541) B916541
theorem B611057 : Blo 405769 611057 := bstep (se 2 (by rfl) ⟨229146, by rfl⟩ : syracuseStep 611057 = 458293) B458293
theorem B611075 : Blo 405769 611075 := bstep (se 1 (by rfl) ⟨458306, by rfl⟩ : syracuseStep 611075 = 916613) B916613
theorem B611105 : Blo 405769 611105 := bstep (se 2 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 611105 = 458329) B458329
theorem B611123 : Blo 405769 611123 := bstep (se 1 (by rfl) ⟨458342, by rfl⟩ : syracuseStep 611123 = 916685) B916685
theorem B611153 : Blo 405769 611153 := bstep (se 2 (by rfl) ⟨229182, by rfl⟩ : syracuseStep 611153 = 458365) B458365
theorem B1102673 : Blo 405769 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B611171 : Blo 405769 611171 := bstep (se 1 (by rfl) ⟨458378, by rfl⟩ : syracuseStep 611171 = 916757) B916757
theorem B611201 : Blo 405769 611201 := bstep (se 2 (by rfl) ⟨229200, by rfl⟩ : syracuseStep 611201 = 458401) B458401
theorem B611219 : Blo 405769 611219 := bstep (se 1 (by rfl) ⟨458414, by rfl⟩ : syracuseStep 611219 = 916829) B916829
theorem B611249 : Blo 405769 611249 := bstep (se 2 (by rfl) ⟨229218, by rfl⟩ : syracuseStep 611249 = 458437) B458437
theorem B611267 : Blo 405769 611267 := bstep (se 1 (by rfl) ⟨458450, by rfl⟩ : syracuseStep 611267 = 916901) B916901
theorem B2315213 : Blo 405769 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B611297 : Blo 405769 611297 := bstep (se 2 (by rfl) ⟨229236, by rfl⟩ : syracuseStep 611297 = 458473) B458473
theorem B611315 : Blo 405769 611315 := bstep (se 1 (by rfl) ⟨458486, by rfl⟩ : syracuseStep 611315 = 916973) B916973
theorem B611345 : Blo 405769 611345 := bstep (se 2 (by rfl) ⟨229254, by rfl⟩ : syracuseStep 611345 = 458509) B458509
theorem B578593 : Blo 405769 578593 := bstep (se 2 (by rfl) ⟨216972, by rfl⟩ : syracuseStep 578593 = 433945) B433945
theorem B611363 : Blo 405769 611363 := bstep (se 1 (by rfl) ⟨458522, by rfl⟩ : syracuseStep 611363 = 917045) B917045
theorem B611393 : Blo 405769 611393 := bstep (se 2 (by rfl) ⟨229272, by rfl⟩ : syracuseStep 611393 = 458545) B458545
theorem B611411 : Blo 405769 611411 := bstep (se 1 (by rfl) ⟨458558, by rfl⟩ : syracuseStep 611411 = 917117) B917117
theorem B611441 : Blo 405769 611441 := bstep (se 2 (by rfl) ⟨229290, by rfl⟩ : syracuseStep 611441 = 458581) B458581
theorem B611459 : Blo 405769 611459 := bstep (se 1 (by rfl) ⟨458594, by rfl⟩ : syracuseStep 611459 = 917189) B917189
theorem B611489 : Blo 405769 611489 := bstep (se 2 (by rfl) ⟨229308, by rfl⟩ : syracuseStep 611489 = 458617) B458617
theorem B775345 : Blo 405769 775345 := bstep (se 2 (by rfl) ⟨290754, by rfl⟩ : syracuseStep 775345 = 581509) B581509
theorem B611507 : Blo 405769 611507 := bstep (se 1 (by rfl) ⟨458630, by rfl⟩ : syracuseStep 611507 = 917261) B917261
theorem B611537 : Blo 405769 611537 := bstep (se 2 (by rfl) ⟨229326, by rfl⟩ : syracuseStep 611537 = 458653) B458653
theorem B611555 : Blo 405769 611555 := bstep (se 1 (by rfl) ⟨458666, by rfl⟩ : syracuseStep 611555 = 917333) B917333
theorem B611585 : Blo 405769 611585 := bstep (se 2 (by rfl) ⟨229344, by rfl⟩ : syracuseStep 611585 = 458689) B458689
theorem B611603 : Blo 405769 611603 := bstep (se 1 (by rfl) ⟨458702, by rfl⟩ : syracuseStep 611603 = 917405) B917405
theorem B611633 : Blo 405769 611633 := bstep (se 2 (by rfl) ⟨229362, by rfl⟩ : syracuseStep 611633 = 458725) B458725
theorem B611651 : Blo 405769 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B611681 : Blo 405769 611681 := bstep (se 2 (by rfl) ⟨229380, by rfl⟩ : syracuseStep 611681 = 458761) B458761
theorem B578929 : Blo 405769 578929 := bstep (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) B434197
theorem B611699 : Blo 405769 611699 := bstep (se 1 (by rfl) ⟨458774, by rfl⟩ : syracuseStep 611699 = 917549) B917549
theorem B611729 : Blo 405769 611729 := bstep (se 2 (by rfl) ⟨229398, by rfl⟩ : syracuseStep 611729 = 458797) B458797
theorem B611747 : Blo 405769 611747 := bstep (se 1 (by rfl) ⟨458810, by rfl⟩ : syracuseStep 611747 = 917621) B917621
theorem B611777 : Blo 405769 611777 := bstep (se 2 (by rfl) ⟨229416, by rfl⟩ : syracuseStep 611777 = 458833) B458833
theorem B611795 : Blo 405769 611795 := bstep (se 1 (by rfl) ⟨458846, by rfl⟩ : syracuseStep 611795 = 917693) B917693
theorem B611825 : Blo 405769 611825 := bstep (se 2 (by rfl) ⟨229434, by rfl⟩ : syracuseStep 611825 = 458869) B458869
theorem B611843 : Blo 405769 611843 := bstep (se 1 (by rfl) ⟨458882, by rfl⟩ : syracuseStep 611843 = 917765) B917765
theorem B611873 : Blo 405769 611873 := bstep (se 2 (by rfl) ⟨229452, by rfl⟩ : syracuseStep 611873 = 458905) B458905
theorem B611891 : Blo 405769 611891 := bstep (se 1 (by rfl) ⟨458918, by rfl⟩ : syracuseStep 611891 = 917837) B917837
theorem B775747 : Blo 405769 775747 := bstep (se 1 (by rfl) ⟨581810, by rfl⟩ : syracuseStep 775747 = 1163621) B1163621
theorem B611921 : Blo 405769 611921 := bstep (se 2 (by rfl) ⟨229470, by rfl⟩ : syracuseStep 611921 = 458941) B458941
theorem B611939 : Blo 405769 611939 := bstep (se 1 (by rfl) ⟨458954, by rfl⟩ : syracuseStep 611939 = 917909) B917909
theorem B775793 : Blo 405769 775793 := bstep (se 2 (by rfl) ⟨290922, by rfl⟩ : syracuseStep 775793 = 581845) B581845
theorem B1103473 : Blo 405769 1103473 := bstep (se 2 (by rfl) ⟨413802, by rfl⟩ : syracuseStep 1103473 = 827605) B827605
theorem B611969 : Blo 405769 611969 := bstep (se 2 (by rfl) ⟨229488, by rfl⟩ : syracuseStep 611969 = 458977) B458977
theorem B611987 : Blo 405769 611987 := bstep (se 1 (by rfl) ⟨458990, by rfl⟩ : syracuseStep 611987 = 917981) B917981
theorem B2152099 : Blo 405769 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B612017 : Blo 405769 612017 := bstep (se 2 (by rfl) ⟨229506, by rfl⟩ : syracuseStep 612017 = 459013) B459013
theorem B1103537 : Blo 405769 1103537 := bstep (se 2 (by rfl) ⟨413826, by rfl⟩ : syracuseStep 1103537 = 827653) B827653
theorem B612035 : Blo 405769 612035 := bstep (se 1 (by rfl) ⟨459026, by rfl⟩ : syracuseStep 612035 = 918053) B918053
theorem B612065 : Blo 405769 612065 := bstep (se 2 (by rfl) ⟨229524, by rfl⟩ : syracuseStep 612065 = 459049) B459049
theorem B612083 : Blo 405769 612083 := bstep (se 1 (by rfl) ⟨459062, by rfl⟩ : syracuseStep 612083 = 918125) B918125
theorem B5232397 : Blo 405769 5232397 := bstep (se 3 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 5232397 = 1962149) B1962149
theorem B612113 : Blo 405769 612113 := bstep (se 2 (by rfl) ⟨229542, by rfl⟩ : syracuseStep 612113 = 459085) B459085
theorem B612131 : Blo 405769 612131 := bstep (se 1 (by rfl) ⟨459098, by rfl⟩ : syracuseStep 612131 = 918197) B918197
theorem B612161 : Blo 405769 612161 := bstep (se 2 (by rfl) ⟨229560, by rfl⟩ : syracuseStep 612161 = 459121) B459121
theorem B513859 : Blo 405769 513859 := bstep (se 1 (by rfl) ⟨385394, by rfl⟩ : syracuseStep 513859 = 770789) B770789
theorem B612179 : Blo 405769 612179 := bstep (se 1 (by rfl) ⟨459134, by rfl⟩ : syracuseStep 612179 = 918269) B918269
theorem B612209 : Blo 405769 612209 := bstep (se 2 (by rfl) ⟨229578, by rfl⟩ : syracuseStep 612209 = 459157) B459157
theorem B612227 : Blo 405769 612227 := bstep (se 1 (by rfl) ⟨459170, by rfl⟩ : syracuseStep 612227 = 918341) B918341
theorem B776081 : Blo 405769 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B612257 : Blo 405769 612257 := bstep (se 2 (by rfl) ⟨229596, by rfl⟩ : syracuseStep 612257 = 459193) B459193
theorem B513955 : Blo 405769 513955 := bstep (se 1 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 513955 = 770933) B770933
theorem B612275 : Blo 405769 612275 := bstep (se 1 (by rfl) ⟨459206, by rfl⟩ : syracuseStep 612275 = 918413) B918413
theorem B579521 : Blo 405769 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B612305 : Blo 405769 612305 := bstep (se 2 (by rfl) ⟨229614, by rfl⟩ : syracuseStep 612305 = 459229) B459229
theorem B612323 : Blo 405769 612323 := bstep (se 1 (by rfl) ⟨459242, by rfl⟩ : syracuseStep 612323 = 918485) B918485
theorem B612353 : Blo 405769 612353 := bstep (se 2 (by rfl) ⟨229632, by rfl⟩ : syracuseStep 612353 = 459265) B459265
theorem B612371 : Blo 405769 612371 := bstep (se 1 (by rfl) ⟨459278, by rfl⟩ : syracuseStep 612371 = 918557) B918557
theorem B612401 : Blo 405769 612401 := bstep (se 2 (by rfl) ⟨229650, by rfl⟩ : syracuseStep 612401 = 459301) B459301
theorem B612419 : Blo 405769 612419 := bstep (se 1 (by rfl) ⟨459314, by rfl⟩ : syracuseStep 612419 = 918629) B918629
theorem B612449 : Blo 405769 612449 := bstep (se 2 (by rfl) ⟨229668, by rfl⟩ : syracuseStep 612449 = 459337) B459337
theorem B874595 : Blo 405769 874595 := bstep (se 1 (by rfl) ⟨655946, by rfl⟩ : syracuseStep 874595 = 1311893) B1311893
theorem B612467 : Blo 405769 612467 := bstep (se 1 (by rfl) ⟨459350, by rfl⟩ : syracuseStep 612467 = 918701) B918701
theorem B612497 : Blo 405769 612497 := bstep (se 2 (by rfl) ⟨229686, by rfl⟩ : syracuseStep 612497 = 459373) B459373
theorem B612515 : Blo 405769 612515 := bstep (se 1 (by rfl) ⟨459386, by rfl⟩ : syracuseStep 612515 = 918773) B918773
theorem B1300643 : Blo 405769 1300643 := bstep (se 1 (by rfl) ⟨975482, by rfl⟩ : syracuseStep 1300643 = 1950965) B1950965
theorem B2054321 : Blo 405769 2054321 := bstep (se 2 (by rfl) ⟨770370, by rfl⟩ : syracuseStep 2054321 = 1540741) B1540741
theorem B612545 : Blo 405769 612545 := bstep (se 2 (by rfl) ⟨229704, by rfl⟩ : syracuseStep 612545 = 459409) B459409
theorem B2087117 : Blo 405769 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B612563 : Blo 405769 612563 := bstep (se 1 (by rfl) ⟨459422, by rfl⟩ : syracuseStep 612563 = 918845) B918845
theorem B612593 : Blo 405769 612593 := bstep (se 2 (by rfl) ⟨229722, by rfl⟩ : syracuseStep 612593 = 459445) B459445
theorem B612611 : Blo 405769 612611 := bstep (se 1 (by rfl) ⟨459458, by rfl⟩ : syracuseStep 612611 = 918917) B918917
theorem B612641 : Blo 405769 612641 := bstep (se 2 (by rfl) ⟨229740, by rfl⟩ : syracuseStep 612641 = 459481) B459481
theorem B612659 : Blo 405769 612659 := bstep (se 1 (by rfl) ⟨459494, by rfl⟩ : syracuseStep 612659 = 918989) B918989
theorem B612689 : Blo 405769 612689 := bstep (se 2 (by rfl) ⟨229758, by rfl⟩ : syracuseStep 612689 = 459517) B459517
theorem B612707 : Blo 405769 612707 := bstep (se 1 (by rfl) ⟨459530, by rfl⟩ : syracuseStep 612707 = 919061) B919061
theorem B612737 : Blo 405769 612737 := bstep (se 2 (by rfl) ⟨229776, by rfl⟩ : syracuseStep 612737 = 459553) B459553
theorem B514451 : Blo 405769 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B612755 : Blo 405769 612755 := bstep (se 1 (by rfl) ⟨459566, by rfl⟩ : syracuseStep 612755 = 919133) B919133
theorem B612785 : Blo 405769 612785 := bstep (se 2 (by rfl) ⟨229794, by rfl⟩ : syracuseStep 612785 = 459589) B459589
theorem B612803 : Blo 405769 612803 := bstep (se 1 (by rfl) ⟨459602, by rfl⟩ : syracuseStep 612803 = 919205) B919205
theorem B580051 : Blo 405769 580051 := bstep (se 1 (by rfl) ⟨435038, by rfl⟩ : syracuseStep 580051 = 870077) B870077
theorem B612833 : Blo 405769 612833 := bstep (se 2 (by rfl) ⟨229812, by rfl⟩ : syracuseStep 612833 = 459625) B459625
theorem B3135971 : Blo 405769 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B612851 : Blo 405769 612851 := bstep (se 1 (by rfl) ⟨459638, by rfl⟩ : syracuseStep 612851 = 919277) B919277
theorem B612881 : Blo 405769 612881 := bstep (se 2 (by rfl) ⟨229830, by rfl⟩ : syracuseStep 612881 = 459661) B459661
theorem B612899 : Blo 405769 612899 := bstep (se 1 (by rfl) ⟨459674, by rfl⟩ : syracuseStep 612899 = 919349) B919349
theorem B612929 : Blo 405769 612929 := bstep (se 2 (by rfl) ⟨229848, by rfl⟩ : syracuseStep 612929 = 459697) B459697
theorem B1235533 : Blo 405769 1235533 := bstep (se 3 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 1235533 = 463325) B463325
theorem B612947 : Blo 405769 612947 := bstep (se 1 (by rfl) ⟨459710, by rfl⟩ : syracuseStep 612947 = 919421) B919421
theorem B776803 : Blo 405769 776803 := bstep (se 1 (by rfl) ⟨582602, by rfl⟩ : syracuseStep 776803 = 1165205) B1165205
theorem B612977 : Blo 405769 612977 := bstep (se 2 (by rfl) ⟨229866, by rfl⟩ : syracuseStep 612977 = 459733) B459733
theorem B612995 : Blo 405769 612995 := bstep (se 1 (by rfl) ⟨459746, by rfl⟩ : syracuseStep 612995 = 919493) B919493
theorem B613025 : Blo 405769 613025 := bstep (se 2 (by rfl) ⟨229884, by rfl⟩ : syracuseStep 613025 = 459769) B459769
theorem B613043 : Blo 405769 613043 := bstep (se 1 (by rfl) ⟨459782, by rfl⟩ : syracuseStep 613043 = 919565) B919565
theorem B613073 : Blo 405769 613073 := bstep (se 2 (by rfl) ⟨229902, by rfl⟩ : syracuseStep 613073 = 459805) B459805
theorem B613091 : Blo 405769 613091 := bstep (se 1 (by rfl) ⟨459818, by rfl⟩ : syracuseStep 613091 = 919637) B919637
theorem B613121 : Blo 405769 613121 := bstep (se 2 (by rfl) ⟨229920, by rfl⟩ : syracuseStep 613121 = 459841) B459841
theorem B613139 : Blo 405769 613139 := bstep (se 1 (by rfl) ⟨459854, by rfl⟩ : syracuseStep 613139 = 919709) B919709
theorem B580387 : Blo 405769 580387 := bstep (se 1 (by rfl) ⟨435290, by rfl⟩ : syracuseStep 580387 = 870581) B870581
theorem B613169 : Blo 405769 613169 := bstep (se 2 (by rfl) ⟨229938, by rfl⟩ : syracuseStep 613169 = 459877) B459877
theorem B613187 : Blo 405769 613187 := bstep (se 1 (by rfl) ⟨459890, by rfl⟩ : syracuseStep 613187 = 919781) B919781
theorem B613217 : Blo 405769 613217 := bstep (se 2 (by rfl) ⟨229956, by rfl⟩ : syracuseStep 613217 = 459913) B459913
theorem B613235 : Blo 405769 613235 := bstep (se 1 (by rfl) ⟨459926, by rfl⟩ : syracuseStep 613235 = 919853) B919853
theorem B613265 : Blo 405769 613265 := bstep (se 2 (by rfl) ⟨229974, by rfl⟩ : syracuseStep 613265 = 459949) B459949
theorem B613283 : Blo 405769 613283 := bstep (se 1 (by rfl) ⟨459962, by rfl⟩ : syracuseStep 613283 = 919925) B919925
theorem B613313 : Blo 405769 613313 := bstep (se 2 (by rfl) ⟨229992, by rfl⟩ : syracuseStep 613313 = 459985) B459985
theorem B613331 : Blo 405769 613331 := bstep (se 1 (by rfl) ⟨459998, by rfl⟩ : syracuseStep 613331 = 919997) B919997
theorem B613361 : Blo 405769 613361 := bstep (se 2 (by rfl) ⟨230010, by rfl⟩ : syracuseStep 613361 = 460021) B460021
theorem B613379 : Blo 405769 613379 := bstep (se 1 (by rfl) ⟨460034, by rfl⟩ : syracuseStep 613379 = 920069) B920069
theorem B3300365 : Blo 405769 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B613409 : Blo 405769 613409 := bstep (se 2 (by rfl) ⟨230028, by rfl⟩ : syracuseStep 613409 = 460057) B460057
theorem B777251 : Blo 405769 777251 := bstep (se 1 (by rfl) ⟨582938, by rfl⟩ : syracuseStep 777251 = 1165877) B1165877
theorem B613427 : Blo 405769 613427 := bstep (se 1 (by rfl) ⟨460070, by rfl⟩ : syracuseStep 613427 = 920141) B920141
theorem B5233733 : Blo 405769 5233733 := bstep (se 4 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 5233733 = 981325) B981325
theorem B613457 : Blo 405769 613457 := bstep (se 2 (by rfl) ⟨230046, by rfl⟩ : syracuseStep 613457 = 460093) B460093
theorem B515155 : Blo 405769 515155 := bstep (se 1 (by rfl) ⟨386366, by rfl⟩ : syracuseStep 515155 = 772733) B772733
theorem B613475 : Blo 405769 613475 := bstep (se 1 (by rfl) ⟨460106, by rfl⟩ : syracuseStep 613475 = 920213) B920213
theorem B613505 : Blo 405769 613505 := bstep (se 2 (by rfl) ⟨230064, by rfl⟩ : syracuseStep 613505 = 460129) B460129
theorem B2612357 : Blo 405769 2612357 := bstep (se 4 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 2612357 = 489817) B489817
theorem B613523 : Blo 405769 613523 := bstep (se 1 (by rfl) ⟨460142, by rfl⟩ : syracuseStep 613523 = 920285) B920285
theorem B613553 : Blo 405769 613553 := bstep (se 2 (by rfl) ⟨230082, by rfl⟩ : syracuseStep 613553 = 460165) B460165
theorem B515251 : Blo 405769 515251 := bstep (se 1 (by rfl) ⟨386438, by rfl⟩ : syracuseStep 515251 = 772877) B772877
theorem B613571 : Blo 405769 613571 := bstep (se 1 (by rfl) ⟨460178, by rfl⟩ : syracuseStep 613571 = 920357) B920357
theorem B613601 : Blo 405769 613601 := bstep (se 2 (by rfl) ⟨230100, by rfl⟩ : syracuseStep 613601 = 460201) B460201
theorem B613619 : Blo 405769 613619 := bstep (se 1 (by rfl) ⟨460214, by rfl⟩ : syracuseStep 613619 = 920429) B920429
theorem B613649 : Blo 405769 613649 := bstep (se 2 (by rfl) ⟨230118, by rfl⟩ : syracuseStep 613649 = 460237) B460237
theorem B613667 : Blo 405769 613667 := bstep (se 1 (by rfl) ⟨460250, by rfl⟩ : syracuseStep 613667 = 920501) B920501
theorem B613697 : Blo 405769 613697 := bstep (se 2 (by rfl) ⟨230136, by rfl⟩ : syracuseStep 613697 = 460273) B460273
theorem B777539 : Blo 405769 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B580945 : Blo 405769 580945 := bstep (se 2 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 580945 = 435709) B435709
theorem B613715 : Blo 405769 613715 := bstep (se 1 (by rfl) ⟨460286, by rfl⟩ : syracuseStep 613715 = 920573) B920573
theorem B613745 : Blo 405769 613745 := bstep (se 2 (by rfl) ⟨230154, by rfl⟩ : syracuseStep 613745 = 460309) B460309
theorem B580979 : Blo 405769 580979 := bstep (se 1 (by rfl) ⟨435734, by rfl⟩ : syracuseStep 580979 = 871469) B871469
theorem B613763 : Blo 405769 613763 := bstep (se 1 (by rfl) ⟨460322, by rfl⟩ : syracuseStep 613763 = 920645) B920645
theorem B3300749 : Blo 405769 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B4709773 : Blo 405769 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B613793 : Blo 405769 613793 := bstep (se 2 (by rfl) ⟨230172, by rfl⟩ : syracuseStep 613793 = 460345) B460345
theorem B613811 : Blo 405769 613811 := bstep (se 1 (by rfl) ⟨460358, by rfl⟩ : syracuseStep 613811 = 920717) B920717
theorem B613841 : Blo 405769 613841 := bstep (se 2 (by rfl) ⟨230190, by rfl⟩ : syracuseStep 613841 = 460381) B460381
theorem B613859 : Blo 405769 613859 := bstep (se 1 (by rfl) ⟨460394, by rfl⟩ : syracuseStep 613859 = 920789) B920789
theorem B613889 : Blo 405769 613889 := bstep (se 2 (by rfl) ⟨230208, by rfl⟩ : syracuseStep 613889 = 460417) B460417
theorem B613907 : Blo 405769 613907 := bstep (se 1 (by rfl) ⟨460430, by rfl⟩ : syracuseStep 613907 = 920861) B920861
theorem B613937 : Blo 405769 613937 := bstep (se 2 (by rfl) ⟨230226, by rfl⟩ : syracuseStep 613937 = 460453) B460453
theorem B613955 : Blo 405769 613955 := bstep (se 1 (by rfl) ⟨460466, by rfl⟩ : syracuseStep 613955 = 920933) B920933
theorem B613985 : Blo 405769 613985 := bstep (se 2 (by rfl) ⟨230244, by rfl⟩ : syracuseStep 613985 = 460489) B460489
theorem B2055779 : Blo 405769 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B614003 : Blo 405769 614003 := bstep (se 1 (by rfl) ⟨460502, by rfl⟩ : syracuseStep 614003 = 921005) B921005
theorem B614033 : Blo 405769 614033 := bstep (se 2 (by rfl) ⟨230262, by rfl⟩ : syracuseStep 614033 = 460525) B460525
theorem B515747 : Blo 405769 515747 := bstep (se 1 (by rfl) ⟨386810, by rfl⟩ : syracuseStep 515747 = 773621) B773621
theorem B614051 : Blo 405769 614051 := bstep (se 1 (by rfl) ⟨460538, by rfl⟩ : syracuseStep 614051 = 921077) B921077
theorem B1400483 : Blo 405769 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B614081 : Blo 405769 614081 := bstep (se 2 (by rfl) ⟨230280, by rfl⟩ : syracuseStep 614081 = 460561) B460561
theorem B614099 : Blo 405769 614099 := bstep (se 1 (by rfl) ⟨460574, by rfl⟩ : syracuseStep 614099 = 921149) B921149
theorem B1302257 : Blo 405769 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B614129 : Blo 405769 614129 := bstep (se 2 (by rfl) ⟨230298, by rfl⟩ : syracuseStep 614129 = 460597) B460597
theorem B614147 : Blo 405769 614147 := bstep (se 1 (by rfl) ⟨460610, by rfl⟩ : syracuseStep 614147 = 921221) B921221
theorem B614177 : Blo 405769 614177 := bstep (se 2 (by rfl) ⟨230316, by rfl⟩ : syracuseStep 614177 = 460633) B460633
theorem B2318129 : Blo 405769 2318129 := bstep (se 2 (by rfl) ⟨869298, by rfl⟩ : syracuseStep 2318129 = 1738597) B1738597
theorem B614195 : Blo 405769 614195 := bstep (se 1 (by rfl) ⟨460646, by rfl⟩ : syracuseStep 614195 = 921293) B921293
theorem B614225 : Blo 405769 614225 := bstep (se 2 (by rfl) ⟨230334, by rfl⟩ : syracuseStep 614225 = 460669) B460669
theorem B614243 : Blo 405769 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B614273 : Blo 405769 614273 := bstep (se 2 (by rfl) ⟨230352, by rfl⟩ : syracuseStep 614273 = 460705) B460705
theorem B614291 : Blo 405769 614291 := bstep (se 1 (by rfl) ⟨460718, by rfl⟩ : syracuseStep 614291 = 921437) B921437
theorem B581537 : Blo 405769 581537 := bstep (se 2 (by rfl) ⟨218076, by rfl⟩ : syracuseStep 581537 = 436153) B436153
theorem B548785 : Blo 405769 548785 := bstep (se 2 (by rfl) ⟨205794, by rfl⟩ : syracuseStep 548785 = 411589) B411589
theorem B614321 : Blo 405769 614321 := bstep (se 2 (by rfl) ⟨230370, by rfl⟩ : syracuseStep 614321 = 460741) B460741
theorem B614339 : Blo 405769 614339 := bstep (se 1 (by rfl) ⟨460754, by rfl⟩ : syracuseStep 614339 = 921509) B921509
theorem B614369 : Blo 405769 614369 := bstep (se 2 (by rfl) ⟨230388, by rfl⟩ : syracuseStep 614369 = 460777) B460777
theorem B581617 : Blo 405769 581617 := bstep (se 2 (by rfl) ⟨218106, by rfl⟩ : syracuseStep 581617 = 436213) B436213
theorem B614387 : Blo 405769 614387 := bstep (se 1 (by rfl) ⟨460790, by rfl⟩ : syracuseStep 614387 = 921581) B921581
theorem B614417 : Blo 405769 614417 := bstep (se 2 (by rfl) ⟨230406, by rfl⟩ : syracuseStep 614417 = 460813) B460813
theorem B614435 : Blo 405769 614435 := bstep (se 1 (by rfl) ⟨460826, by rfl⟩ : syracuseStep 614435 = 921653) B921653
theorem B1564721 : Blo 405769 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B614465 : Blo 405769 614465 := bstep (se 2 (by rfl) ⟨230424, by rfl⟩ : syracuseStep 614465 = 460849) B460849
theorem B614483 : Blo 405769 614483 := bstep (se 1 (by rfl) ⟨460862, by rfl⟩ : syracuseStep 614483 = 921725) B921725
theorem B614513 : Blo 405769 614513 := bstep (se 2 (by rfl) ⟨230442, by rfl⟩ : syracuseStep 614513 = 460885) B460885
theorem B614531 : Blo 405769 614531 := bstep (se 1 (by rfl) ⟨460898, by rfl⟩ : syracuseStep 614531 = 921797) B921797
theorem B614561 : Blo 405769 614561 := bstep (se 2 (by rfl) ⟨230460, by rfl⟩ : syracuseStep 614561 = 460921) B460921
theorem B614579 : Blo 405769 614579 := bstep (se 1 (by rfl) ⟨460934, by rfl⟩ : syracuseStep 614579 = 921869) B921869
theorem B614609 : Blo 405769 614609 := bstep (se 2 (by rfl) ⟨230478, by rfl⟩ : syracuseStep 614609 = 460957) B460957
theorem B614627 : Blo 405769 614627 := bstep (se 1 (by rfl) ⟨460970, by rfl⟩ : syracuseStep 614627 = 921941) B921941
theorem B549185 : Blo 405769 549185 := bstep (se 2 (by rfl) ⟨205944, by rfl⟩ : syracuseStep 549185 = 411889) B411889
theorem B516451 : Blo 405769 516451 := bstep (se 1 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 516451 = 774677) B774677
theorem B2056589 : Blo 405769 2056589 := bstep (se 3 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 2056589 = 771221) B771221
theorem B516547 : Blo 405769 516547 := bstep (se 1 (by rfl) ⟨387410, by rfl⟩ : syracuseStep 516547 = 774821) B774821
theorem B1106435 : Blo 405769 1106435 := bstep (se 1 (by rfl) ⟨829826, by rfl⟩ : syracuseStep 1106435 = 1659653) B1659653
theorem B582403 : Blo 405769 582403 := bstep (se 1 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 582403 = 873605) B873605
theorem B549649 : Blo 405769 549649 := bstep (se 2 (by rfl) ⟨206118, by rfl⟩ : syracuseStep 549649 = 412237) B412237
theorem B517043 : Blo 405769 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B582881 : Blo 405769 582881 := bstep (se 2 (by rfl) ⟨218580, by rfl⟩ : syracuseStep 582881 = 437161) B437161
theorem B2319587 : Blo 405769 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B582995 : Blo 405769 582995 := bstep (se 1 (by rfl) ⟨437246, by rfl⟩ : syracuseStep 582995 = 874493) B874493
theorem B3466637 : Blo 405769 3466637 := bstep (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) B1299989
theorem B583075 : Blo 405769 583075 := bstep (se 1 (by rfl) ⟨437306, by rfl⟩ : syracuseStep 583075 = 874613) B874613
theorem B1369709 : Blo 405769 1369709 := bstep (se 3 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 1369709 = 513641) B513641
theorem B517747 : Blo 405769 517747 := bstep (se 1 (by rfl) ⟨388310, by rfl⟩ : syracuseStep 517747 = 776621) B776621
theorem B681617 : Blo 405769 681617 := bstep (se 2 (by rfl) ⟨255606, by rfl⟩ : syracuseStep 681617 = 511213) B511213
theorem B1369763 : Blo 405769 1369763 := bstep (se 1 (by rfl) ⟨1027322, by rfl⟩ : syracuseStep 1369763 = 2054645) B2054645
theorem B517843 : Blo 405769 517843 := bstep (se 1 (by rfl) ⟨388382, by rfl⟩ : syracuseStep 517843 = 776765) B776765
theorem B1304333 : Blo 405769 1304333 := bstep (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) B489125
theorem B1370033 : Blo 405769 1370033 := bstep (se 2 (by rfl) ⟨513762, by rfl⟩ : syracuseStep 1370033 = 1027525) B1027525
theorem B8775701 : Blo 405769 8775701 := bstep (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) B411361
theorem B518339 : Blo 405769 518339 := bstep (se 1 (by rfl) ⟨388754, by rfl⟩ : syracuseStep 518339 = 777509) B777509
theorem B2320589 : Blo 405769 2320589 := bstep (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) B870221
theorem B1239437 : Blo 405769 1239437 := bstep (se 3 (by rfl) ⟨232394, by rfl⟩ : syracuseStep 1239437 = 464789) B464789
theorem B1370573 : Blo 405769 1370573 := bstep (se 3 (by rfl) ⟨256982, by rfl⟩ : syracuseStep 1370573 = 513965) B513965
theorem B1370627 : Blo 405769 1370627 := bstep (se 1 (by rfl) ⟨1027970, by rfl⟩ : syracuseStep 1370627 = 2055941) B2055941
theorem B1305229 : Blo 405769 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B1370897 : Blo 405769 1370897 := bstep (se 2 (by rfl) ⟨514086, by rfl⟩ : syracuseStep 1370897 = 1028173) B1028173
theorem B781283 : Blo 405769 781283 := bstep (se 1 (by rfl) ⟨585962, by rfl⟩ : syracuseStep 781283 = 1171925) B1171925
theorem B977923 : Blo 405769 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B2059505 : Blo 405769 2059505 := bstep (se 2 (by rfl) ⟨772314, by rfl⟩ : syracuseStep 2059505 = 1544629) B1544629
theorem B1240337 : Blo 405769 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B1371437 : Blo 405769 1371437 := bstep (se 3 (by rfl) ⟨257144, by rfl⟩ : syracuseStep 1371437 = 514289) B514289
theorem B1371491 : Blo 405769 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B912995 : Blo 405769 912995 := bstep (se 1 (by rfl) ⟨684746, by rfl⟩ : syracuseStep 912995 = 1369493) B1369493
theorem B1371761 : Blo 405769 1371761 := bstep (se 2 (by rfl) ⟨514410, by rfl⟩ : syracuseStep 1371761 = 1028821) B1028821
theorem B1306307 : Blo 405769 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B5893829 : Blo 405769 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B913265 : Blo 405769 913265 := bstep (se 2 (by rfl) ⟨342474, by rfl⟩ : syracuseStep 913265 = 684949) B684949
theorem B913283 : Blo 405769 913283 := bstep (se 1 (by rfl) ⟨684962, by rfl⟩ : syracuseStep 913283 = 1369925) B1369925
theorem B5238755 : Blo 405769 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B618545 : Blo 405769 618545 := bstep (se 2 (by rfl) ⟨231954, by rfl⟩ : syracuseStep 618545 = 463909) B463909
theorem B19132469 : Blo 405769 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B4419683 : Blo 405769 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B1372301 : Blo 405769 1372301 := bstep (se 3 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 1372301 = 514613) B514613
theorem B913553 : Blo 405769 913553 := bstep (se 2 (by rfl) ⟨342582, by rfl⟩ : syracuseStep 913553 = 685165) B685165
theorem B913571 : Blo 405769 913571 := bstep (se 1 (by rfl) ⟨685178, by rfl⟩ : syracuseStep 913571 = 1370357) B1370357
theorem B1372355 : Blo 405769 1372355 := bstep (se 1 (by rfl) ⟨1029266, by rfl⟩ : syracuseStep 1372355 = 2058533) B2058533
theorem B651539 : Blo 405769 651539 := bstep (se 1 (by rfl) ⟨488654, by rfl⟩ : syracuseStep 651539 = 977309) B977309
theorem B4714805 : Blo 405769 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B1306961 : Blo 405769 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B651667 : Blo 405769 651667 := bstep (se 1 (by rfl) ⟨488750, by rfl⟩ : syracuseStep 651667 = 977501) B977501
theorem B913841 : Blo 405769 913841 := bstep (se 2 (by rfl) ⟨342690, by rfl⟩ : syracuseStep 913841 = 685381) B685381
theorem B913859 : Blo 405769 913859 := bstep (se 1 (by rfl) ⟨685394, by rfl⟩ : syracuseStep 913859 = 1370789) B1370789
theorem B1372625 : Blo 405769 1372625 := bstep (se 2 (by rfl) ⟨514734, by rfl⟩ : syracuseStep 1372625 = 1029469) B1029469
theorem B16740917 : Blo 405769 16740917 := bstep (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) B1569461
theorem B586321 : Blo 405769 586321 := bstep (se 2 (by rfl) ⟨219870, by rfl⟩ : syracuseStep 586321 = 439741) B439741
theorem B979537 : Blo 405769 979537 := bstep (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) B734653
theorem B2060963 : Blo 405769 2060963 := bstep (se 1 (by rfl) ⟨1545722, by rfl⟩ : syracuseStep 2060963 = 3091445) B3091445
theorem B914129 : Blo 405769 914129 := bstep (se 2 (by rfl) ⟨342798, by rfl⟩ : syracuseStep 914129 = 685597) B685597
theorem B914147 : Blo 405769 914147 := bstep (se 1 (by rfl) ⟨685610, by rfl⟩ : syracuseStep 914147 = 1371221) B1371221
theorem B684787 : Blo 405769 684787 := bstep (se 1 (by rfl) ⟨513590, by rfl⟩ : syracuseStep 684787 = 1027181) B1027181
theorem B652051 : Blo 405769 652051 := bstep (se 1 (by rfl) ⟨489038, by rfl⟩ : syracuseStep 652051 = 978077) B978077
theorem B684929 : Blo 405769 684929 := bstep (se 2 (by rfl) ⟨256848, by rfl⟩ : syracuseStep 684929 = 513697) B513697
theorem B1373165 : Blo 405769 1373165 := bstep (se 3 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 1373165 = 514937) B514937
theorem B914417 : Blo 405769 914417 := bstep (se 2 (by rfl) ⟨342906, by rfl⟩ : syracuseStep 914417 = 685813) B685813
theorem B685057 : Blo 405769 685057 := bstep (se 2 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 685057 = 513793) B513793
theorem B914435 : Blo 405769 914435 := bstep (se 1 (by rfl) ⟨685826, by rfl⟩ : syracuseStep 914435 = 1371653) B1371653
theorem B652307 : Blo 405769 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B685091 : Blo 405769 685091 := bstep (se 1 (by rfl) ⟨513818, by rfl⟩ : syracuseStep 685091 = 1027637) B1027637
theorem B1373219 : Blo 405769 1373219 := bstep (se 1 (by rfl) ⟨1029914, by rfl⟩ : syracuseStep 1373219 = 2059829) B2059829
theorem B2323505 : Blo 405769 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B1471601 : Blo 405769 1471601 := bstep (se 2 (by rfl) ⟨551850, by rfl⟩ : syracuseStep 1471601 = 1103701) B1103701
theorem B685219 : Blo 405769 685219 := bstep (se 1 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 685219 = 1027829) B1027829
theorem B1471729 : Blo 405769 1471729 := bstep (se 2 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 1471729 = 1103797) B1103797
theorem B914705 : Blo 405769 914705 := bstep (se 2 (by rfl) ⟨343014, by rfl⟩ : syracuseStep 914705 = 686029) B686029
theorem B914723 : Blo 405769 914723 := bstep (se 1 (by rfl) ⟨686042, by rfl⟩ : syracuseStep 914723 = 1372085) B1372085
theorem B2618659 : Blo 405769 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B685361 : Blo 405769 685361 := bstep (se 2 (by rfl) ⟨257010, by rfl⟩ : syracuseStep 685361 = 514021) B514021
theorem B1373489 : Blo 405769 1373489 := bstep (se 2 (by rfl) ⟨515058, by rfl⟩ : syracuseStep 1373489 = 1030117) B1030117
theorem B685489 : Blo 405769 685489 := bstep (se 2 (by rfl) ⟨257058, by rfl⟩ : syracuseStep 685489 = 514117) B514117
theorem B2061773 : Blo 405769 2061773 := bstep (se 3 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 2061773 = 773165) B773165
theorem B685523 : Blo 405769 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B652769 : Blo 405769 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B914993 : Blo 405769 914993 := bstep (se 2 (by rfl) ⟨343122, by rfl⟩ : syracuseStep 914993 = 686245) B686245
theorem B652865 : Blo 405769 652865 := bstep (se 2 (by rfl) ⟨244824, by rfl⟩ : syracuseStep 652865 = 489649) B489649
theorem B915011 : Blo 405769 915011 := bstep (se 1 (by rfl) ⟨686258, by rfl⟩ : syracuseStep 915011 = 1372517) B1372517
theorem B685651 : Blo 405769 685651 := bstep (se 1 (by rfl) ⟨514238, by rfl⟩ : syracuseStep 685651 = 1028477) B1028477
theorem B652897 : Blo 405769 652897 := bstep (se 2 (by rfl) ⟨244836, by rfl⟩ : syracuseStep 652897 = 489673) B489673
theorem B1308305 : Blo 405769 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B1242769 : Blo 405769 1242769 := bstep (se 2 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 1242769 = 932077) B932077
theorem B685793 : Blo 405769 685793 := bstep (se 2 (by rfl) ⟨257172, by rfl⟩ : syracuseStep 685793 = 514345) B514345
theorem B1374029 : Blo 405769 1374029 := bstep (se 3 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 1374029 = 515261) B515261
theorem B915281 : Blo 405769 915281 := bstep (se 2 (by rfl) ⟨343230, by rfl⟩ : syracuseStep 915281 = 686461) B686461
theorem B522067 : Blo 405769 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B685921 : Blo 405769 685921 := bstep (se 2 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 685921 = 514441) B514441
theorem B456547 : Blo 405769 456547 := bstep (se 1 (by rfl) ⟨342410, by rfl⟩ : syracuseStep 456547 = 684821) B684821
theorem B915299 : Blo 405769 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B7862129 : Blo 405769 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B685955 : Blo 405769 685955 := bstep (se 1 (by rfl) ⟨514466, by rfl⟩ : syracuseStep 685955 = 1028933) B1028933
theorem B1374083 : Blo 405769 1374083 := bstep (se 1 (by rfl) ⟨1030562, by rfl⟩ : syracuseStep 1374083 = 2061125) B2061125
theorem B29718413 : Blo 405769 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B456691 : Blo 405769 456691 := bstep (se 1 (by rfl) ⟨342518, by rfl⟩ : syracuseStep 456691 = 685037) B685037
theorem B686083 : Blo 405769 686083 := bstep (se 1 (by rfl) ⟨514562, by rfl⟩ : syracuseStep 686083 = 1029125) B1029125
theorem B1472525 : Blo 405769 1472525 := bstep (se 3 (by rfl) ⟨276098, by rfl⟩ : syracuseStep 1472525 = 552197) B552197
theorem B915569 : Blo 405769 915569 := bstep (se 2 (by rfl) ⟨343338, by rfl⟩ : syracuseStep 915569 = 686677) B686677
theorem B456835 : Blo 405769 456835 := bstep (se 1 (by rfl) ⟨342626, by rfl⟩ : syracuseStep 456835 = 685253) B685253
theorem B915587 : Blo 405769 915587 := bstep (se 1 (by rfl) ⟨686690, by rfl⟩ : syracuseStep 915587 = 1373381) B1373381
theorem B686225 : Blo 405769 686225 := bstep (se 2 (by rfl) ⟨257334, by rfl⟩ : syracuseStep 686225 = 514669) B514669
theorem B1374353 : Blo 405769 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B2619661 : Blo 405769 2619661 := bstep (se 3 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 2619661 = 982373) B982373
theorem B686353 : Blo 405769 686353 := bstep (se 2 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 686353 = 514765) B514765
theorem B456979 : Blo 405769 456979 := bstep (se 1 (by rfl) ⟨342734, by rfl⟩ : syracuseStep 456979 = 685469) B685469
theorem B686387 : Blo 405769 686387 := bstep (se 1 (by rfl) ⟨514790, by rfl⟩ : syracuseStep 686387 = 1029581) B1029581
theorem B915857 : Blo 405769 915857 := bstep (se 2 (by rfl) ⟨343446, by rfl⟩ : syracuseStep 915857 = 686893) B686893
theorem B457123 : Blo 405769 457123 := bstep (se 1 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 457123 = 685685) B685685
theorem B915875 : Blo 405769 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B1866161 : Blo 405769 1866161 := bstep (se 2 (by rfl) ⟨699810, by rfl⟩ : syracuseStep 1866161 = 1399621) B1399621
theorem B686515 : Blo 405769 686515 := bstep (se 1 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 686515 = 1029773) B1029773
theorem B2324963 : Blo 405769 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B1735181 : Blo 405769 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B457267 : Blo 405769 457267 := bstep (se 1 (by rfl) ⟨342950, by rfl⟩ : syracuseStep 457267 = 685901) B685901
theorem B686657 : Blo 405769 686657 := bstep (se 2 (by rfl) ⟨257496, by rfl⟩ : syracuseStep 686657 = 514993) B514993
theorem B1374893 : Blo 405769 1374893 := bstep (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) B515585
theorem B916145 : Blo 405769 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B686785 : Blo 405769 686785 := bstep (se 2 (by rfl) ⟨257544, by rfl⟩ : syracuseStep 686785 = 515089) B515089
theorem B457411 : Blo 405769 457411 := bstep (se 1 (by rfl) ⟨343058, by rfl⟩ : syracuseStep 457411 = 686117) B686117
theorem B916163 : Blo 405769 916163 := bstep (se 1 (by rfl) ⟨687122, by rfl⟩ : syracuseStep 916163 = 1374245) B1374245
theorem B686819 : Blo 405769 686819 := bstep (se 1 (by rfl) ⟨515114, by rfl⟩ : syracuseStep 686819 = 1030229) B1030229
theorem B1374947 : Blo 405769 1374947 := bstep (se 1 (by rfl) ⟨1031210, by rfl⟩ : syracuseStep 1374947 = 2062421) B2062421
theorem B1309421 : Blo 405769 1309421 := bstep (se 3 (by rfl) ⟨245516, by rfl⟩ : syracuseStep 1309421 = 491033) B491033
theorem B457555 : Blo 405769 457555 := bstep (se 1 (by rfl) ⟨343166, by rfl⟩ : syracuseStep 457555 = 686333) B686333
theorem B686947 : Blo 405769 686947 := bstep (se 1 (by rfl) ⟨515210, by rfl⟩ : syracuseStep 686947 = 1030421) B1030421
theorem B2489285 : Blo 405769 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B916433 : Blo 405769 916433 := bstep (se 2 (by rfl) ⟨343662, by rfl⟩ : syracuseStep 916433 = 687325) B687325
theorem B457699 : Blo 405769 457699 := bstep (se 1 (by rfl) ⟨343274, by rfl⟩ : syracuseStep 457699 = 686549) B686549
theorem B916451 : Blo 405769 916451 := bstep (se 1 (by rfl) ⟨687338, by rfl⟩ : syracuseStep 916451 = 1374677) B1374677
theorem B687089 : Blo 405769 687089 := bstep (se 2 (by rfl) ⟨257658, by rfl⟩ : syracuseStep 687089 = 515317) B515317
theorem B1375217 : Blo 405769 1375217 := bstep (se 2 (by rfl) ⟨515706, by rfl⟩ : syracuseStep 1375217 = 1031413) B1031413
theorem B2194445 : Blo 405769 2194445 := bstep (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) B822917
theorem B687217 : Blo 405769 687217 := bstep (se 2 (by rfl) ⟨257706, by rfl⟩ : syracuseStep 687217 = 515413) B515413
theorem B457843 : Blo 405769 457843 := bstep (se 1 (by rfl) ⟨343382, by rfl⟩ : syracuseStep 457843 = 686765) B686765
theorem B621697 : Blo 405769 621697 := bstep (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) B466273
theorem B621713 : Blo 405769 621713 := bstep (se 2 (by rfl) ⟨233142, by rfl⟩ : syracuseStep 621713 = 466285) B466285
theorem B687251 : Blo 405769 687251 := bstep (se 1 (by rfl) ⟨515438, by rfl⟩ : syracuseStep 687251 = 1030877) B1030877
theorem B654563 : Blo 405769 654563 := bstep (se 1 (by rfl) ⟨490922, by rfl⟩ : syracuseStep 654563 = 981845) B981845
theorem B916721 : Blo 405769 916721 := bstep (se 2 (by rfl) ⟨343770, by rfl⟩ : syracuseStep 916721 = 687541) B687541
theorem B457987 : Blo 405769 457987 := bstep (se 1 (by rfl) ⟨343490, by rfl⟩ : syracuseStep 457987 = 686981) B686981
theorem B916739 : Blo 405769 916739 := bstep (se 1 (by rfl) ⟨687554, by rfl⟩ : syracuseStep 916739 = 1375109) B1375109
theorem B687379 : Blo 405769 687379 := bstep (se 1 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 687379 = 1031069) B1031069
theorem B621859 : Blo 405769 621859 := bstep (se 1 (by rfl) ⟨466394, by rfl⟩ : syracuseStep 621859 = 932789) B932789
theorem B458131 : Blo 405769 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B523667 : Blo 405769 523667 := bstep (se 1 (by rfl) ⟨392750, by rfl⟩ : syracuseStep 523667 = 785501) B785501
theorem B687521 : Blo 405769 687521 := bstep (se 2 (by rfl) ⟨257820, by rfl⟩ : syracuseStep 687521 = 515641) B515641
theorem B1244593 : Blo 405769 1244593 := bstep (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) B933445
theorem B1375757 : Blo 405769 1375757 := bstep (se 3 (by rfl) ⟨257954, by rfl⟩ : syracuseStep 1375757 = 515909) B515909
theorem B917009 : Blo 405769 917009 := bstep (se 2 (by rfl) ⟨343878, by rfl⟩ : syracuseStep 917009 = 687757) B687757
theorem B9895445 : Blo 405769 9895445 := bstep (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) B463849
theorem B687649 : Blo 405769 687649 := bstep (se 2 (by rfl) ⟨257868, by rfl⟩ : syracuseStep 687649 = 515737) B515737
theorem B458275 : Blo 405769 458275 := bstep (se 1 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 458275 = 687413) B687413
theorem B917027 : Blo 405769 917027 := bstep (se 1 (by rfl) ⟨687770, by rfl⟩ : syracuseStep 917027 = 1375541) B1375541
theorem B687683 : Blo 405769 687683 := bstep (se 1 (by rfl) ⟨515762, by rfl⟩ : syracuseStep 687683 = 1031525) B1031525
theorem B1375811 : Blo 405769 1375811 := bstep (se 1 (by rfl) ⟨1031858, by rfl⟩ : syracuseStep 1375811 = 2063717) B2063717
theorem B2817677 : Blo 405769 2817677 := bstep (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) B1056629
theorem B1048241 : Blo 405769 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B458419 : Blo 405769 458419 := bstep (se 1 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 458419 = 687629) B687629
theorem B687811 : Blo 405769 687811 := bstep (se 1 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 687811 = 1031717) B1031717
theorem B1769165 : Blo 405769 1769165 := bstep (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) B663437
theorem B655075 : Blo 405769 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B655121 : Blo 405769 655121 := bstep (se 2 (by rfl) ⟨245670, by rfl⟩ : syracuseStep 655121 = 491341) B491341
theorem B1310509 : Blo 405769 1310509 := bstep (se 3 (by rfl) ⟨245720, by rfl⟩ : syracuseStep 1310509 = 491441) B491441
theorem B917297 : Blo 405769 917297 := bstep (se 2 (by rfl) ⟨343986, by rfl⟩ : syracuseStep 917297 = 687973) B687973
theorem B458563 : Blo 405769 458563 := bstep (se 1 (by rfl) ⟨343922, by rfl⟩ : syracuseStep 458563 = 687845) B687845
theorem B917315 : Blo 405769 917315 := bstep (se 1 (by rfl) ⟨687986, by rfl⟩ : syracuseStep 917315 = 1375973) B1375973
theorem B687953 : Blo 405769 687953 := bstep (se 2 (by rfl) ⟨257982, by rfl⟩ : syracuseStep 687953 = 515965) B515965
theorem B1376081 : Blo 405769 1376081 := bstep (se 2 (by rfl) ⟨516030, by rfl⟩ : syracuseStep 1376081 = 1032061) B1032061
theorem B688081 : Blo 405769 688081 := bstep (se 2 (by rfl) ⟨258030, by rfl⟩ : syracuseStep 688081 = 516061) B516061
theorem B458707 : Blo 405769 458707 := bstep (se 1 (by rfl) ⟨344030, by rfl⟩ : syracuseStep 458707 = 688061) B688061
theorem B688115 : Blo 405769 688115 := bstep (se 1 (by rfl) ⟨516086, by rfl⟩ : syracuseStep 688115 = 1032173) B1032173
theorem B2326603 : Blo 405769 2326603 := bstep (se 1 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 2326603 = 3489905) B3489905
theorem B655447 : Blo 405769 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B786547 : Blo 405769 786547 := bstep (se 1 (by rfl) ⟨589910, by rfl⟩ : syracuseStep 786547 = 1179821) B1179821
theorem B917657 : Blo 405769 917657 := bstep (se 2 (by rfl) ⟨344121, by rfl⟩ : syracuseStep 917657 = 688243) B688243
theorem B458923 : Blo 405769 458923 := bstep (se 1 (by rfl) ⟨344192, by rfl⟩ : syracuseStep 458923 = 688385) B688385
theorem B1376459 : Blo 405769 1376459 := bstep (se 1 (by rfl) ⟨1032344, by rfl⟩ : syracuseStep 1376459 = 2064689) B2064689
theorem B688331 : Blo 405769 688331 := bstep (se 1 (by rfl) ⟨516248, by rfl⟩ : syracuseStep 688331 = 1032497) B1032497
theorem B917747 : Blo 405769 917747 := bstep (se 1 (by rfl) ⟨688310, by rfl⟩ : syracuseStep 917747 = 1376621) B1376621
theorem B917783 : Blo 405769 917783 := bstep (se 1 (by rfl) ⟨688337, by rfl⟩ : syracuseStep 917783 = 1376675) B1376675
theorem B459031 : Blo 405769 459031 := bstep (se 1 (by rfl) ⟨344273, by rfl⟩ : syracuseStep 459031 = 688547) B688547
theorem B688459 : Blo 405769 688459 := bstep (se 1 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 688459 = 1032689) B1032689
theorem B2326877 : Blo 405769 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B786827 : Blo 405769 786827 := bstep (se 1 (by rfl) ⟨590120, by rfl⟩ : syracuseStep 786827 = 1180241) B1180241
theorem B917963 : Blo 405769 917963 := bstep (se 1 (by rfl) ⟨688472, by rfl⟩ : syracuseStep 917963 = 1376945) B1376945
theorem B459211 : Blo 405769 459211 := bstep (se 1 (by rfl) ⟨344408, by rfl⟩ : syracuseStep 459211 = 688817) B688817
theorem B1376729 : Blo 405769 1376729 := bstep (se 2 (by rfl) ⟨516273, by rfl⟩ : syracuseStep 1376729 = 1032547) B1032547
theorem B688601 : Blo 405769 688601 := bstep (se 2 (by rfl) ⟨258225, by rfl⟩ : syracuseStep 688601 = 516451) B516451
theorem B918017 : Blo 405769 918017 := bstep (se 2 (by rfl) ⟨344256, by rfl⟩ : syracuseStep 918017 = 688513) B688513
theorem B1966609 : Blo 405769 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B655895 : Blo 405769 655895 := bstep (se 1 (by rfl) ⟨491921, by rfl⟩ : syracuseStep 655895 = 983843) B983843
theorem B459319 : Blo 405769 459319 := bstep (se 1 (by rfl) ⟨344489, by rfl⟩ : syracuseStep 459319 = 688979) B688979
theorem B688729 : Blo 405769 688729 := bstep (se 2 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 688729 = 516547) B516547
theorem B656075 : Blo 405769 656075 := bstep (se 1 (by rfl) ⟨492056, by rfl⟩ : syracuseStep 656075 = 984113) B984113
theorem B918233 : Blo 405769 918233 := bstep (se 2 (by rfl) ⟨344337, by rfl⟩ : syracuseStep 918233 = 688675) B688675
theorem B459499 : Blo 405769 459499 := bstep (se 1 (by rfl) ⟨344624, by rfl⟩ : syracuseStep 459499 = 689249) B689249
theorem B918323 : Blo 405769 918323 := bstep (se 1 (by rfl) ⟨688742, by rfl⟩ : syracuseStep 918323 = 1377485) B1377485
theorem B656203 : Blo 405769 656203 := bstep (se 1 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 656203 = 984305) B984305
theorem B918359 : Blo 405769 918359 := bstep (se 1 (by rfl) ⟨688769, by rfl⟩ : syracuseStep 918359 = 1377539) B1377539
theorem B459607 : Blo 405769 459607 := bstep (se 1 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 459607 = 689411) B689411
theorem B656267 : Blo 405769 656267 := bstep (se 1 (by rfl) ⟨492200, by rfl⟩ : syracuseStep 656267 = 984401) B984401
theorem B1541015 : Blo 405769 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B918539 : Blo 405769 918539 := bstep (se 1 (by rfl) ⟨688904, by rfl⟩ : syracuseStep 918539 = 1377809) B1377809
theorem B459787 : Blo 405769 459787 := bstep (se 1 (by rfl) ⟨344840, by rfl⟩ : syracuseStep 459787 = 689681) B689681
theorem B918593 : Blo 405769 918593 := bstep (se 2 (by rfl) ⟨344472, by rfl⟩ : syracuseStep 918593 = 688945) B688945
theorem B590923 : Blo 405769 590923 := bstep (se 1 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 590923 = 886385) B886385
theorem B1541213 : Blo 405769 1541213 := bstep (se 3 (by rfl) ⟨288977, by rfl⟩ : syracuseStep 1541213 = 577955) B577955
theorem B459895 : Blo 405769 459895 := bstep (se 1 (by rfl) ⟨344921, by rfl⟩ : syracuseStep 459895 = 689843) B689843
theorem B1377431 : Blo 405769 1377431 := bstep (se 1 (by rfl) ⟨1033073, by rfl⟩ : syracuseStep 1377431 = 2066147) B2066147
theorem B689303 : Blo 405769 689303 := bstep (se 1 (by rfl) ⟨516977, by rfl⟩ : syracuseStep 689303 = 1033955) B1033955
theorem B689431 : Blo 405769 689431 := bstep (se 1 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 689431 = 1034147) B1034147
theorem B918809 : Blo 405769 918809 := bstep (se 2 (by rfl) ⟨344553, by rfl⟩ : syracuseStep 918809 = 689107) B689107
theorem B460075 : Blo 405769 460075 := bstep (se 1 (by rfl) ⟨345056, by rfl⟩ : syracuseStep 460075 = 690113) B690113
theorem B918899 : Blo 405769 918899 := bstep (se 1 (by rfl) ⟨689174, by rfl⟩ : syracuseStep 918899 = 1378349) B1378349
theorem B26936725 : Blo 405769 26936725 := bstep (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) B1262659
theorem B918935 : Blo 405769 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B460183 : Blo 405769 460183 := bstep (se 1 (by rfl) ⟨345137, by rfl⟩ : syracuseStep 460183 = 690275) B690275
theorem B2065985 : Blo 405769 2065985 := bstep (se 2 (by rfl) ⟨774744, by rfl⟩ : syracuseStep 2065985 = 1549489) B1549489
theorem B919115 : Blo 405769 919115 := bstep (se 1 (by rfl) ⟨689336, by rfl⟩ : syracuseStep 919115 = 1378673) B1378673
theorem B460363 : Blo 405769 460363 := bstep (se 1 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 460363 = 690545) B690545
theorem B919169 : Blo 405769 919169 := bstep (se 2 (by rfl) ⟨344688, by rfl⟩ : syracuseStep 919169 = 689377) B689377
theorem B1377971 : Blo 405769 1377971 := bstep (se 1 (by rfl) ⟨1033478, by rfl⟩ : syracuseStep 1377971 = 2066957) B2066957
theorem B460471 : Blo 405769 460471 := bstep (se 1 (by rfl) ⟨345353, by rfl⟩ : syracuseStep 460471 = 690707) B690707
theorem B919385 : Blo 405769 919385 := bstep (se 2 (by rfl) ⟨344769, by rfl⟩ : syracuseStep 919385 = 689539) B689539
theorem B25692005 : Blo 405769 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B460651 : Blo 405769 460651 := bstep (se 1 (by rfl) ⟨345488, by rfl⟩ : syracuseStep 460651 = 690977) B690977
theorem B690059 : Blo 405769 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B919475 : Blo 405769 919475 := bstep (se 1 (by rfl) ⟨689606, by rfl⟩ : syracuseStep 919475 = 1379213) B1379213
theorem B1378241 : Blo 405769 1378241 := bstep (se 2 (by rfl) ⟨516840, by rfl⟩ : syracuseStep 1378241 = 1033681) B1033681
theorem B919511 : Blo 405769 919511 := bstep (se 1 (by rfl) ⟨689633, by rfl⟩ : syracuseStep 919511 = 1379267) B1379267
theorem B460759 : Blo 405769 460759 := bstep (se 1 (by rfl) ⟨345569, by rfl⟩ : syracuseStep 460759 = 691139) B691139
theorem B690187 : Blo 405769 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B952343 : Blo 405769 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B919691 : Blo 405769 919691 := bstep (se 1 (by rfl) ⟨689768, by rfl⟩ : syracuseStep 919691 = 1379537) B1379537
theorem B460939 : Blo 405769 460939 := bstep (se 1 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 460939 = 691409) B691409
theorem B690329 : Blo 405769 690329 := bstep (se 2 (by rfl) ⟨258873, by rfl⟩ : syracuseStep 690329 = 517747) B517747
theorem B919745 : Blo 405769 919745 := bstep (se 2 (by rfl) ⟨344904, by rfl⟩ : syracuseStep 919745 = 689809) B689809
theorem B690457 : Blo 405769 690457 := bstep (se 2 (by rfl) ⟨258921, by rfl⟩ : syracuseStep 690457 = 517843) B517843
theorem B919961 : Blo 405769 919961 := bstep (se 2 (by rfl) ⟨344985, by rfl⟩ : syracuseStep 919961 = 689971) B689971
theorem B1182131 : Blo 405769 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B1378781 : Blo 405769 1378781 := bstep (se 3 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 1378781 = 517043) B517043
theorem B13273571 : Blo 405769 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B920051 : Blo 405769 920051 := bstep (se 1 (by rfl) ⟨690038, by rfl⟩ : syracuseStep 920051 = 1380077) B1380077
theorem B920087 : Blo 405769 920087 := bstep (se 1 (by rfl) ⟨690065, by rfl⟩ : syracuseStep 920087 = 1380131) B1380131
theorem B3476033 : Blo 405769 3476033 := bstep (se 2 (by rfl) ⟨1303512, by rfl⟩ : syracuseStep 3476033 = 2607025) B2607025
theorem B5573195 : Blo 405769 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B4983389 : Blo 405769 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B920267 : Blo 405769 920267 := bstep (se 1 (by rfl) ⟨690200, by rfl⟩ : syracuseStep 920267 = 1380401) B1380401
theorem B1739485 : Blo 405769 1739485 := bstep (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) B652307
theorem B920321 : Blo 405769 920321 := bstep (se 2 (by rfl) ⟨345120, by rfl⟩ : syracuseStep 920321 = 690241) B690241
theorem B691031 : Blo 405769 691031 := bstep (se 1 (by rfl) ⟨518273, by rfl⟩ : syracuseStep 691031 = 1036547) B1036547
theorem B2198423 : Blo 405769 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B691159 : Blo 405769 691159 := bstep (se 1 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 691159 = 1036739) B1036739
theorem B920537 : Blo 405769 920537 := bstep (se 2 (by rfl) ⟨345201, by rfl⟩ : syracuseStep 920537 = 690403) B690403
theorem B1543171 : Blo 405769 1543171 := bstep (se 1 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 1543171 = 2314757) B2314757
theorem B920627 : Blo 405769 920627 := bstep (se 1 (by rfl) ⟨690470, by rfl⟩ : syracuseStep 920627 = 1380941) B1380941
theorem B920663 : Blo 405769 920663 := bstep (se 1 (by rfl) ⟨690497, by rfl⟩ : syracuseStep 920663 = 1380995) B1380995
theorem B920843 : Blo 405769 920843 := bstep (se 1 (by rfl) ⟨690632, by rfl⟩ : syracuseStep 920843 = 1381265) B1381265
theorem B1543475 : Blo 405769 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B920897 : Blo 405769 920897 := bstep (se 2 (by rfl) ⟨345336, by rfl⟩ : syracuseStep 920897 = 690673) B690673
theorem B1510859 : Blo 405769 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B2067929 : Blo 405769 2067929 := bstep (se 2 (by rfl) ⟨775473, by rfl⟩ : syracuseStep 2067929 = 1550947) B1550947
theorem B1740305 : Blo 405769 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B921113 : Blo 405769 921113 := bstep (se 2 (by rfl) ⟨345417, by rfl⟩ : syracuseStep 921113 = 690835) B690835
theorem B1379915 : Blo 405769 1379915 := bstep (se 1 (by rfl) ⟨1034936, by rfl⟩ : syracuseStep 1379915 = 2069873) B2069873
theorem B921203 : Blo 405769 921203 := bstep (se 1 (by rfl) ⟨690902, by rfl⟩ : syracuseStep 921203 = 1381805) B1381805
theorem B921239 : Blo 405769 921239 := bstep (se 1 (by rfl) ⟨690929, by rfl⟩ : syracuseStep 921239 = 1381859) B1381859
theorem B921419 : Blo 405769 921419 := bstep (se 1 (by rfl) ⟨691064, by rfl⟩ : syracuseStep 921419 = 1382129) B1382129
theorem B1380185 : Blo 405769 1380185 := bstep (se 2 (by rfl) ⟨517569, by rfl⟩ : syracuseStep 1380185 = 1035139) B1035139
theorem B921473 : Blo 405769 921473 := bstep (se 2 (by rfl) ⟨345552, by rfl⟩ : syracuseStep 921473 = 691105) B691105
theorem B1544129 : Blo 405769 1544129 := bstep (se 2 (by rfl) ⟨579048, by rfl⟩ : syracuseStep 1544129 = 1158097) B1158097
theorem B921689 : Blo 405769 921689 := bstep (se 2 (by rfl) ⟨345633, by rfl⟩ : syracuseStep 921689 = 691267) B691267
theorem B1740973 : Blo 405769 1740973 := bstep (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) B652865
theorem B921779 : Blo 405769 921779 := bstep (se 1 (by rfl) ⟨691334, by rfl⟩ : syracuseStep 921779 = 1382669) B1382669
theorem B921815 : Blo 405769 921815 := bstep (se 1 (by rfl) ⟨691361, by rfl⟩ : syracuseStep 921815 = 1382723) B1382723
theorem B1380887 : Blo 405769 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B2101891 : Blo 405769 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B2200243 : Blo 405769 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B1741571 : Blo 405769 1741571 := bstep (se 1 (by rfl) ⟨1306178, by rfl⟩ : syracuseStep 1741571 = 2612357) B2612357
theorem B463703 : Blo 405769 463703 := bstep (se 1 (by rfl) ⟨347777, by rfl⟩ : syracuseStep 463703 = 695555) B695555
theorem B3478423 : Blo 405769 3478423 := bstep (se 1 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 3478423 = 5217635) B5217635
theorem B2200499 : Blo 405769 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B2069549 : Blo 405769 2069549 := bstep (se 3 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 2069549 = 776081) B776081
theorem B1381427 : Blo 405769 1381427 := bstep (se 1 (by rfl) ⟨1036070, by rfl⟩ : syracuseStep 1381427 = 2072141) B2072141
theorem B1545389 : Blo 405769 1545389 := bstep (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) B579521
theorem B1545419 : Blo 405769 1545419 := bstep (se 1 (by rfl) ⟨1159064, by rfl⟩ : syracuseStep 1545419 = 2318129) B2318129
theorem B3085613 : Blo 405769 3085613 := bstep (se 3 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 3085613 = 1157105) B1157105
theorem B1381697 : Blo 405769 1381697 := bstep (se 2 (by rfl) ⟨518136, by rfl⟩ : syracuseStep 1381697 = 1036273) B1036273
theorem B7542233 : Blo 405769 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B2332253 : Blo 405769 2332253 := bstep (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) B874595
theorem B3348119 : Blo 405769 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B1546073 : Blo 405769 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B1382237 : Blo 405769 1382237 := bstep (se 3 (by rfl) ⟨259169, by rfl⟩ : syracuseStep 1382237 = 518339) B518339
theorem B5871685 : Blo 405769 5871685 := bstep (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) B1100941
theorem B1546391 : Blo 405769 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B1547059 : Blo 405769 1547059 := bstep (se 1 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 1547059 = 2320589) B2320589
theorem B826291 : Blo 405769 826291 := bstep (se 1 (by rfl) ⟨619718, by rfl⟩ : syracuseStep 826291 = 1239437) B1239437
theorem B826891 : Blo 405769 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B696089 : Blo 405769 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B466795 : Blo 405769 466795 := bstep (se 1 (by rfl) ⟨350096, by rfl⟩ : syracuseStep 466795 = 700193) B700193
theorem B1548305 : Blo 405769 1548305 := bstep (se 2 (by rfl) ⟨580614, by rfl⟩ : syracuseStep 1548305 = 1161229) B1161229
theorem B12754979 : Blo 405769 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B434359 : Blo 405769 434359 := bstep (se 1 (by rfl) ⟨325769, by rfl⟩ : syracuseStep 434359 = 651539) B651539
theorem B1549003 : Blo 405769 1549003 := bstep (se 1 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 1549003 = 2323505) B2323505
theorem B11805425 : Blo 405769 11805425 := bstep (se 2 (by rfl) ⟨4427034, by rfl⟩ : syracuseStep 11805425 = 8854069) B8854069
theorem B1647377 : Blo 405769 1647377 := bstep (se 2 (by rfl) ⟨617766, by rfl⟩ : syracuseStep 1647377 = 1235533) B1235533
theorem B2073437 : Blo 405769 2073437 := bstep (se 3 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 2073437 = 777539) B777539
theorem B2204633 : Blo 405769 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B1549277 : Blo 405769 1549277 := bstep (se 3 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 1549277 = 580979) B580979
theorem B435179 : Blo 405769 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B3089501 : Blo 405769 3089501 := bstep (se 3 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 3089501 = 1158563) B1158563
theorem B828929 : Blo 405769 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B1156673 : Blo 405769 1156673 := bstep (se 2 (by rfl) ⟨433752, by rfl⟩ : syracuseStep 1156673 = 867505) B867505
theorem B1549975 : Blo 405769 1549975 := bstep (se 1 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 1549975 = 2324963) B2324963
theorem B1156787 : Blo 405769 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B927425 : Blo 405769 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B7513805 : Blo 405769 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B829145 : Blo 405769 829145 := bstep (se 2 (by rfl) ⟨310929, by rfl⟩ : syracuseStep 829145 = 621859) B621859
theorem B2828125 : Blo 405769 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B436375 : Blo 405769 436375 := bstep (se 1 (by rfl) ⟨327281, by rfl⟩ : syracuseStep 436375 = 654563) B654563
theorem B6596963 : Blo 405769 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B1747345 : Blo 405769 1747345 := bstep (se 2 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 1747345 = 1310509) B1310509
theorem B1550765 : Blo 405769 1550765 := bstep (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) B581537
theorem B698827 : Blo 405769 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B436747 : Blo 405769 436747 := bstep (se 1 (by rfl) ⟨327560, by rfl⟩ : syracuseStep 436747 = 655121) B655121
theorem B731713 : Blo 405769 731713 := bstep (se 2 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 731713 = 548785) B548785
theorem B1485485 : Blo 405769 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B2927539 : Blo 405769 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B437195 : Blo 405769 437195 := bstep (se 1 (by rfl) ⟨327896, by rfl⟩ : syracuseStep 437195 = 655793) B655793
theorem B863435 : Blo 405769 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B3517987 : Blo 405769 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B2207333 : Blo 405769 2207333 := bstep (se 4 (by rfl) ⟨206937, by rfl⟩ : syracuseStep 2207333 = 413875) B413875
theorem B896663 : Blo 405769 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B1552193 : Blo 405769 1552193 := bstep (se 2 (by rfl) ⟨582072, by rfl⟩ : syracuseStep 1552193 = 1164145) B1164145
theorem B1027991 : Blo 405769 1027991 := bstep (se 1 (by rfl) ⟨770993, by rfl⟩ : syracuseStep 1027991 = 1541987) B1541987
theorem B405771 : Blo 405769 405771 := bstep (se 1 (by rfl) ⟨304328, by rfl⟩ : syracuseStep 405771 = 608657) B608657
theorem B2601233 : Blo 405769 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B405783 : Blo 405769 405783 := bstep (se 1 (by rfl) ⟨304337, by rfl⟩ : syracuseStep 405783 = 608675) B608675
theorem B405803 : Blo 405769 405803 := bstep (se 1 (by rfl) ⟨304352, by rfl⟩ : syracuseStep 405803 = 608705) B608705
theorem B405815 : Blo 405769 405815 := bstep (se 1 (by rfl) ⟨304361, by rfl⟩ : syracuseStep 405815 = 608723) B608723
theorem B405835 : Blo 405769 405835 := bstep (se 1 (by rfl) ⟨304376, by rfl⟩ : syracuseStep 405835 = 608753) B608753
theorem B405847 : Blo 405769 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B405867 : Blo 405769 405867 := bstep (se 1 (by rfl) ⟨304400, by rfl⟩ : syracuseStep 405867 = 608801) B608801
theorem B405879 : Blo 405769 405879 := bstep (se 1 (by rfl) ⟨304409, by rfl⟩ : syracuseStep 405879 = 608819) B608819
theorem B405899 : Blo 405769 405899 := bstep (se 1 (by rfl) ⟨304424, by rfl⟩ : syracuseStep 405899 = 608849) B608849
theorem B405911 : Blo 405769 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B700823 : Blo 405769 700823 := bstep (se 1 (by rfl) ⟨525617, by rfl⟩ : syracuseStep 700823 = 1051235) B1051235
theorem B405931 : Blo 405769 405931 := bstep (se 1 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 405931 = 608897) B608897
theorem B405943 : Blo 405769 405943 := bstep (se 1 (by rfl) ⟨304457, by rfl⟩ : syracuseStep 405943 = 608915) B608915
theorem B405963 : Blo 405769 405963 := bstep (se 1 (by rfl) ⟨304472, by rfl⟩ : syracuseStep 405963 = 608945) B608945
theorem B405975 : Blo 405769 405975 := bstep (se 1 (by rfl) ⟨304481, by rfl⟩ : syracuseStep 405975 = 608963) B608963
theorem B405995 : Blo 405769 405995 := bstep (se 1 (by rfl) ⟨304496, by rfl⟩ : syracuseStep 405995 = 608993) B608993
theorem B406007 : Blo 405769 406007 := bstep (se 1 (by rfl) ⟨304505, by rfl⟩ : syracuseStep 406007 = 609011) B609011
theorem B406027 : Blo 405769 406027 := bstep (se 1 (by rfl) ⟨304520, by rfl⟩ : syracuseStep 406027 = 609041) B609041
theorem B406039 : Blo 405769 406039 := bstep (se 1 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 406039 = 609059) B609059
theorem B1159703 : Blo 405769 1159703 := bstep (se 1 (by rfl) ⟨869777, by rfl⟩ : syracuseStep 1159703 = 1739555) B1739555
theorem B406059 : Blo 405769 406059 := bstep (se 1 (by rfl) ⟨304544, by rfl⟩ : syracuseStep 406059 = 609089) B609089
theorem B1028659 : Blo 405769 1028659 := bstep (se 1 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 1028659 = 1542989) B1542989
theorem B406071 : Blo 405769 406071 := bstep (se 1 (by rfl) ⟨304553, by rfl⟩ : syracuseStep 406071 = 609107) B609107
theorem B406091 : Blo 405769 406091 := bstep (se 1 (by rfl) ⟨304568, by rfl⟩ : syracuseStep 406091 = 609137) B609137
theorem B406103 : Blo 405769 406103 := bstep (se 1 (by rfl) ⟨304577, by rfl⟩ : syracuseStep 406103 = 609155) B609155
theorem B1684061 : Blo 405769 1684061 := bstep (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) B631523
theorem B406123 : Blo 405769 406123 := bstep (se 1 (by rfl) ⟨304592, by rfl⟩ : syracuseStep 406123 = 609185) B609185
theorem B406135 : Blo 405769 406135 := bstep (se 1 (by rfl) ⟨304601, by rfl⟩ : syracuseStep 406135 = 609203) B609203
theorem B406155 : Blo 405769 406155 := bstep (se 1 (by rfl) ⟨304616, by rfl⟩ : syracuseStep 406155 = 609233) B609233
theorem B406167 : Blo 405769 406167 := bstep (se 1 (by rfl) ⟨304625, by rfl⟩ : syracuseStep 406167 = 609251) B609251
theorem B406187 : Blo 405769 406187 := bstep (se 1 (by rfl) ⟨304640, by rfl⟩ : syracuseStep 406187 = 609281) B609281
theorem B406199 : Blo 405769 406199 := bstep (se 1 (by rfl) ⟨304649, by rfl⟩ : syracuseStep 406199 = 609299) B609299
theorem B1028801 : Blo 405769 1028801 := bstep (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) B771601
theorem B406219 : Blo 405769 406219 := bstep (se 1 (by rfl) ⟨304664, by rfl⟩ : syracuseStep 406219 = 609329) B609329
theorem B406231 : Blo 405769 406231 := bstep (se 1 (by rfl) ⟨304673, by rfl⟩ : syracuseStep 406231 = 609347) B609347
theorem B1749721 : Blo 405769 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B406251 : Blo 405769 406251 := bstep (se 1 (by rfl) ⟨304688, by rfl⟩ : syracuseStep 406251 = 609377) B609377
theorem B406263 : Blo 405769 406263 := bstep (se 1 (by rfl) ⟨304697, by rfl⟩ : syracuseStep 406263 = 609395) B609395
theorem B406283 : Blo 405769 406283 := bstep (se 1 (by rfl) ⟨304712, by rfl⟩ : syracuseStep 406283 = 609425) B609425
theorem B406295 : Blo 405769 406295 := bstep (se 1 (by rfl) ⟨304721, by rfl⟩ : syracuseStep 406295 = 609443) B609443
theorem B406315 : Blo 405769 406315 := bstep (se 1 (by rfl) ⟨304736, by rfl⟩ : syracuseStep 406315 = 609473) B609473
theorem B406327 : Blo 405769 406327 := bstep (se 1 (by rfl) ⟨304745, by rfl⟩ : syracuseStep 406327 = 609491) B609491
theorem B406347 : Blo 405769 406347 := bstep (se 1 (by rfl) ⟨304760, by rfl⟩ : syracuseStep 406347 = 609521) B609521
theorem B406359 : Blo 405769 406359 := bstep (se 1 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 406359 = 609539) B609539
theorem B406379 : Blo 405769 406379 := bstep (se 1 (by rfl) ⟨304784, by rfl⟩ : syracuseStep 406379 = 609569) B609569
theorem B406391 : Blo 405769 406391 := bstep (se 1 (by rfl) ⟨304793, by rfl⟩ : syracuseStep 406391 = 609587) B609587
theorem B406411 : Blo 405769 406411 := bstep (se 1 (by rfl) ⟨304808, by rfl⟩ : syracuseStep 406411 = 609617) B609617
theorem B406423 : Blo 405769 406423 := bstep (se 1 (by rfl) ⟨304817, by rfl⟩ : syracuseStep 406423 = 609635) B609635
theorem B406443 : Blo 405769 406443 := bstep (se 1 (by rfl) ⟨304832, by rfl⟩ : syracuseStep 406443 = 609665) B609665
theorem B4633523 : Blo 405769 4633523 := bstep (se 1 (by rfl) ⟨3475142, by rfl⟩ : syracuseStep 4633523 = 6950285) B6950285
theorem B406455 : Blo 405769 406455 := bstep (se 1 (by rfl) ⟨304841, by rfl⟩ : syracuseStep 406455 = 609683) B609683
theorem B406475 : Blo 405769 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B406487 : Blo 405769 406487 := bstep (se 1 (by rfl) ⟨304865, by rfl⟩ : syracuseStep 406487 = 609731) B609731
theorem B406507 : Blo 405769 406507 := bstep (se 1 (by rfl) ⟨304880, by rfl⟩ : syracuseStep 406507 = 609761) B609761
theorem B406519 : Blo 405769 406519 := bstep (se 1 (by rfl) ⟨304889, by rfl⟩ : syracuseStep 406519 = 609779) B609779
theorem B406539 : Blo 405769 406539 := bstep (se 1 (by rfl) ⟨304904, by rfl⟩ : syracuseStep 406539 = 609809) B609809
theorem B406551 : Blo 405769 406551 := bstep (se 1 (by rfl) ⟨304913, by rfl⟩ : syracuseStep 406551 = 609827) B609827
theorem B406571 : Blo 405769 406571 := bstep (se 1 (by rfl) ⟨304928, by rfl⟩ : syracuseStep 406571 = 609857) B609857
theorem B406583 : Blo 405769 406583 := bstep (se 1 (by rfl) ⟨304937, by rfl⟩ : syracuseStep 406583 = 609875) B609875
theorem B406603 : Blo 405769 406603 := bstep (se 1 (by rfl) ⟨304952, by rfl⟩ : syracuseStep 406603 = 609905) B609905
theorem B406615 : Blo 405769 406615 := bstep (se 1 (by rfl) ⟨304961, by rfl⟩ : syracuseStep 406615 = 609923) B609923
theorem B406635 : Blo 405769 406635 := bstep (se 1 (by rfl) ⟨304976, by rfl⟩ : syracuseStep 406635 = 609953) B609953
theorem B406647 : Blo 405769 406647 := bstep (se 1 (by rfl) ⟨304985, by rfl⟩ : syracuseStep 406647 = 609971) B609971
theorem B406667 : Blo 405769 406667 := bstep (se 1 (by rfl) ⟨305000, by rfl⟩ : syracuseStep 406667 = 610001) B610001
theorem B406679 : Blo 405769 406679 := bstep (se 1 (by rfl) ⟨305009, by rfl⟩ : syracuseStep 406679 = 610019) B610019
theorem B406699 : Blo 405769 406699 := bstep (se 1 (by rfl) ⟨305024, by rfl⟩ : syracuseStep 406699 = 610049) B610049
theorem B406711 : Blo 405769 406711 := bstep (se 1 (by rfl) ⟨305033, by rfl⟩ : syracuseStep 406711 = 610067) B610067
theorem B406731 : Blo 405769 406731 := bstep (se 1 (by rfl) ⟨305048, by rfl⟩ : syracuseStep 406731 = 610097) B610097
theorem B406743 : Blo 405769 406743 := bstep (se 1 (by rfl) ⟨305057, by rfl⟩ : syracuseStep 406743 = 610115) B610115
theorem B406763 : Blo 405769 406763 := bstep (se 1 (by rfl) ⟨305072, by rfl⟩ : syracuseStep 406763 = 610145) B610145
theorem B406775 : Blo 405769 406775 := bstep (se 1 (by rfl) ⟨305081, by rfl⟩ : syracuseStep 406775 = 610163) B610163
theorem B406795 : Blo 405769 406795 := bstep (se 1 (by rfl) ⟨305096, by rfl⟩ : syracuseStep 406795 = 610193) B610193
theorem B1553681 : Blo 405769 1553681 := bstep (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) B1165261
theorem B406807 : Blo 405769 406807 := bstep (se 1 (by rfl) ⟨305105, by rfl⟩ : syracuseStep 406807 = 610211) B610211
theorem B406827 : Blo 405769 406827 := bstep (se 1 (by rfl) ⟨305120, by rfl⟩ : syracuseStep 406827 = 610241) B610241
theorem B406839 : Blo 405769 406839 := bstep (se 1 (by rfl) ⟨305129, by rfl⟩ : syracuseStep 406839 = 610259) B610259
theorem B406859 : Blo 405769 406859 := bstep (se 1 (by rfl) ⟨305144, by rfl⟩ : syracuseStep 406859 = 610289) B610289
theorem B406871 : Blo 405769 406871 := bstep (se 1 (by rfl) ⟨305153, by rfl⟩ : syracuseStep 406871 = 610307) B610307
theorem B406891 : Blo 405769 406891 := bstep (se 1 (by rfl) ⟨305168, by rfl⟩ : syracuseStep 406891 = 610337) B610337
theorem B406903 : Blo 405769 406903 := bstep (se 1 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 406903 = 610355) B610355
theorem B406923 : Blo 405769 406923 := bstep (se 1 (by rfl) ⟨305192, by rfl⟩ : syracuseStep 406923 = 610385) B610385
theorem B406935 : Blo 405769 406935 := bstep (se 1 (by rfl) ⟨305201, by rfl⟩ : syracuseStep 406935 = 610403) B610403
theorem B406955 : Blo 405769 406955 := bstep (se 1 (by rfl) ⟨305216, by rfl⟩ : syracuseStep 406955 = 610433) B610433
theorem B406967 : Blo 405769 406967 := bstep (se 1 (by rfl) ⟨305225, by rfl⟩ : syracuseStep 406967 = 610451) B610451
theorem B406987 : Blo 405769 406987 := bstep (se 1 (by rfl) ⟨305240, by rfl⟩ : syracuseStep 406987 = 610481) B610481
theorem B406999 : Blo 405769 406999 := bstep (se 1 (by rfl) ⟨305249, by rfl⟩ : syracuseStep 406999 = 610499) B610499
theorem B407019 : Blo 405769 407019 := bstep (se 1 (by rfl) ⟨305264, by rfl⟩ : syracuseStep 407019 = 610529) B610529
theorem B407031 : Blo 405769 407031 := bstep (se 1 (by rfl) ⟨305273, by rfl⟩ : syracuseStep 407031 = 610547) B610547
theorem B407051 : Blo 405769 407051 := bstep (se 1 (by rfl) ⟨305288, by rfl⟩ : syracuseStep 407051 = 610577) B610577
theorem B407063 : Blo 405769 407063 := bstep (se 1 (by rfl) ⟨305297, by rfl⟩ : syracuseStep 407063 = 610595) B610595
theorem B407083 : Blo 405769 407083 := bstep (se 1 (by rfl) ⟨305312, by rfl⟩ : syracuseStep 407083 = 610625) B610625
theorem B407095 : Blo 405769 407095 := bstep (se 1 (by rfl) ⟨305321, by rfl⟩ : syracuseStep 407095 = 610643) B610643
theorem B407115 : Blo 405769 407115 := bstep (se 1 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 407115 = 610673) B610673
theorem B407127 : Blo 405769 407127 := bstep (se 1 (by rfl) ⟨305345, by rfl⟩ : syracuseStep 407127 = 610691) B610691
theorem B2471525 : Blo 405769 2471525 := bstep (se 4 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 2471525 = 463411) B463411
theorem B407147 : Blo 405769 407147 := bstep (se 1 (by rfl) ⟨305360, by rfl⟩ : syracuseStep 407147 = 610721) B610721
theorem B407159 : Blo 405769 407159 := bstep (se 1 (by rfl) ⟨305369, by rfl⟩ : syracuseStep 407159 = 610739) B610739
theorem B407179 : Blo 405769 407179 := bstep (se 1 (by rfl) ⟨305384, by rfl⟩ : syracuseStep 407179 = 610769) B610769
theorem B407191 : Blo 405769 407191 := bstep (se 1 (by rfl) ⟨305393, by rfl⟩ : syracuseStep 407191 = 610787) B610787
theorem B407211 : Blo 405769 407211 := bstep (se 1 (by rfl) ⟨305408, by rfl⟩ : syracuseStep 407211 = 610817) B610817
theorem B407223 : Blo 405769 407223 := bstep (se 1 (by rfl) ⟨305417, by rfl⟩ : syracuseStep 407223 = 610835) B610835
theorem B407243 : Blo 405769 407243 := bstep (se 1 (by rfl) ⟨305432, by rfl⟩ : syracuseStep 407243 = 610865) B610865
theorem B407255 : Blo 405769 407255 := bstep (se 1 (by rfl) ⟨305441, by rfl⟩ : syracuseStep 407255 = 610883) B610883
theorem B734935 : Blo 405769 734935 := bstep (se 1 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 734935 = 1102403) B1102403
theorem B1554137 : Blo 405769 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B407275 : Blo 405769 407275 := bstep (se 1 (by rfl) ⟨305456, by rfl⟩ : syracuseStep 407275 = 610913) B610913
theorem B407287 : Blo 405769 407287 := bstep (se 1 (by rfl) ⟨305465, by rfl⟩ : syracuseStep 407287 = 610931) B610931
theorem B3127045 : Blo 405769 3127045 := bstep (se 4 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 3127045 = 586321) B586321
theorem B407307 : Blo 405769 407307 := bstep (se 1 (by rfl) ⟨305480, by rfl⟩ : syracuseStep 407307 = 610961) B610961
theorem B407319 : Blo 405769 407319 := bstep (se 1 (by rfl) ⟨305489, by rfl⟩ : syracuseStep 407319 = 610979) B610979
theorem B734999 : Blo 405769 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B407339 : Blo 405769 407339 := bstep (se 1 (by rfl) ⟨305504, by rfl⟩ : syracuseStep 407339 = 611009) B611009
theorem B407351 : Blo 405769 407351 := bstep (se 1 (by rfl) ⟨305513, by rfl⟩ : syracuseStep 407351 = 611027) B611027
theorem B407371 : Blo 405769 407371 := bstep (se 1 (by rfl) ⟨305528, by rfl⟩ : syracuseStep 407371 = 611057) B611057
theorem B407383 : Blo 405769 407383 := bstep (se 1 (by rfl) ⟨305537, by rfl⟩ : syracuseStep 407383 = 611075) B611075
theorem B407403 : Blo 405769 407403 := bstep (se 1 (by rfl) ⟨305552, by rfl⟩ : syracuseStep 407403 = 611105) B611105
theorem B407415 : Blo 405769 407415 := bstep (se 1 (by rfl) ⟨305561, by rfl⟩ : syracuseStep 407415 = 611123) B611123
theorem B407435 : Blo 405769 407435 := bstep (se 1 (by rfl) ⟨305576, by rfl⟩ : syracuseStep 407435 = 611153) B611153
theorem B735115 : Blo 405769 735115 := bstep (se 1 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 735115 = 1102673) B1102673
theorem B407447 : Blo 405769 407447 := bstep (se 1 (by rfl) ⟨305585, by rfl⟩ : syracuseStep 407447 = 611171) B611171
theorem B407467 : Blo 405769 407467 := bstep (se 1 (by rfl) ⟨305600, by rfl⟩ : syracuseStep 407467 = 611201) B611201
theorem B1554349 : Blo 405769 1554349 := bstep (se 3 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 1554349 = 582881) B582881
theorem B1030067 : Blo 405769 1030067 := bstep (se 1 (by rfl) ⟨772550, by rfl⟩ : syracuseStep 1030067 = 1545101) B1545101
theorem B407479 : Blo 405769 407479 := bstep (se 1 (by rfl) ⟨305609, by rfl⟩ : syracuseStep 407479 = 611219) B611219
theorem B407499 : Blo 405769 407499 := bstep (se 1 (by rfl) ⟨305624, by rfl⟩ : syracuseStep 407499 = 611249) B611249
theorem B458743 : Blo 405769 458743 := bstep (se 1 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 458743 = 688115) B688115
theorem B407511 : Blo 405769 407511 := bstep (se 1 (by rfl) ⟨305633, by rfl⟩ : syracuseStep 407511 = 611267) B611267
theorem B407531 : Blo 405769 407531 := bstep (se 1 (by rfl) ⟨305648, by rfl⟩ : syracuseStep 407531 = 611297) B611297
theorem B407543 : Blo 405769 407543 := bstep (se 1 (by rfl) ⟨305657, by rfl⟩ : syracuseStep 407543 = 611315) B611315
theorem B407563 : Blo 405769 407563 := bstep (se 1 (by rfl) ⟨305672, by rfl⟩ : syracuseStep 407563 = 611345) B611345
theorem B407575 : Blo 405769 407575 := bstep (se 1 (by rfl) ⟨305681, by rfl⟩ : syracuseStep 407575 = 611363) B611363
theorem B407595 : Blo 405769 407595 := bstep (se 1 (by rfl) ⟨305696, by rfl⟩ : syracuseStep 407595 = 611393) B611393
theorem B407607 : Blo 405769 407607 := bstep (se 1 (by rfl) ⟨305705, by rfl⟩ : syracuseStep 407607 = 611411) B611411
theorem B407627 : Blo 405769 407627 := bstep (se 1 (by rfl) ⟨305720, by rfl⟩ : syracuseStep 407627 = 611441) B611441
theorem B407639 : Blo 405769 407639 := bstep (se 1 (by rfl) ⟨305729, by rfl⟩ : syracuseStep 407639 = 611459) B611459
theorem B407659 : Blo 405769 407659 := bstep (se 1 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 407659 = 611489) B611489
theorem B407671 : Blo 405769 407671 := bstep (se 1 (by rfl) ⟨305753, by rfl⟩ : syracuseStep 407671 = 611507) B611507
theorem B407691 : Blo 405769 407691 := bstep (se 1 (by rfl) ⟨305768, by rfl⟩ : syracuseStep 407691 = 611537) B611537
theorem B407703 : Blo 405769 407703 := bstep (se 1 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 407703 = 611555) B611555
theorem B407723 : Blo 405769 407723 := bstep (se 1 (by rfl) ⟨305792, by rfl⟩ : syracuseStep 407723 = 611585) B611585
theorem B407735 : Blo 405769 407735 := bstep (se 1 (by rfl) ⟨305801, by rfl⟩ : syracuseStep 407735 = 611603) B611603
theorem B407755 : Blo 405769 407755 := bstep (se 1 (by rfl) ⟨305816, by rfl⟩ : syracuseStep 407755 = 611633) B611633
theorem B407767 : Blo 405769 407767 := bstep (se 1 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 407767 = 611651) B611651
theorem B1554653 : Blo 405769 1554653 := bstep (se 3 (by rfl) ⟨291497, by rfl⟩ : syracuseStep 1554653 = 582995) B582995
theorem B407787 : Blo 405769 407787 := bstep (se 1 (by rfl) ⟨305840, by rfl⟩ : syracuseStep 407787 = 611681) B611681
theorem B407799 : Blo 405769 407799 := bstep (se 1 (by rfl) ⟨305849, by rfl⟩ : syracuseStep 407799 = 611699) B611699
theorem B407819 : Blo 405769 407819 := bstep (se 1 (by rfl) ⟨305864, by rfl⟩ : syracuseStep 407819 = 611729) B611729
theorem B407831 : Blo 405769 407831 := bstep (se 1 (by rfl) ⟨305873, by rfl⟩ : syracuseStep 407831 = 611747) B611747
theorem B407851 : Blo 405769 407851 := bstep (se 1 (by rfl) ⟨305888, by rfl⟩ : syracuseStep 407851 = 611777) B611777
theorem B407863 : Blo 405769 407863 := bstep (se 1 (by rfl) ⟨305897, by rfl⟩ : syracuseStep 407863 = 611795) B611795
theorem B407883 : Blo 405769 407883 := bstep (se 1 (by rfl) ⟨305912, by rfl⟩ : syracuseStep 407883 = 611825) B611825
theorem B407895 : Blo 405769 407895 := bstep (se 1 (by rfl) ⟨305921, by rfl⟩ : syracuseStep 407895 = 611843) B611843
theorem B4634981 : Blo 405769 4634981 := bstep (se 4 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 4634981 = 869059) B869059
theorem B407915 : Blo 405769 407915 := bstep (se 1 (by rfl) ⟨305936, by rfl⟩ : syracuseStep 407915 = 611873) B611873
theorem B407927 : Blo 405769 407927 := bstep (se 1 (by rfl) ⟨305945, by rfl⟩ : syracuseStep 407927 = 611891) B611891
theorem B407947 : Blo 405769 407947 := bstep (se 1 (by rfl) ⟨305960, by rfl⟩ : syracuseStep 407947 = 611921) B611921
theorem B407959 : Blo 405769 407959 := bstep (se 1 (by rfl) ⟨305969, by rfl⟩ : syracuseStep 407959 = 611939) B611939
theorem B407979 : Blo 405769 407979 := bstep (se 1 (by rfl) ⟨305984, by rfl⟩ : syracuseStep 407979 = 611969) B611969
theorem B407991 : Blo 405769 407991 := bstep (se 1 (by rfl) ⟨305993, by rfl⟩ : syracuseStep 407991 = 611987) B611987
theorem B1030603 : Blo 405769 1030603 := bstep (se 1 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 1030603 = 1545905) B1545905
theorem B408011 : Blo 405769 408011 := bstep (se 1 (by rfl) ⟨306008, by rfl⟩ : syracuseStep 408011 = 612017) B612017
theorem B735691 : Blo 405769 735691 := bstep (se 1 (by rfl) ⟨551768, by rfl⟩ : syracuseStep 735691 = 1103537) B1103537
theorem B408023 : Blo 405769 408023 := bstep (se 1 (by rfl) ⟨306017, by rfl⟩ : syracuseStep 408023 = 612035) B612035
theorem B408043 : Blo 405769 408043 := bstep (se 1 (by rfl) ⟨306032, by rfl⟩ : syracuseStep 408043 = 612065) B612065
theorem B408055 : Blo 405769 408055 := bstep (se 1 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 408055 = 612083) B612083
theorem B408075 : Blo 405769 408075 := bstep (se 1 (by rfl) ⟨306056, by rfl⟩ : syracuseStep 408075 = 612113) B612113
theorem B408087 : Blo 405769 408087 := bstep (se 1 (by rfl) ⟨306065, by rfl⟩ : syracuseStep 408087 = 612131) B612131
theorem B408107 : Blo 405769 408107 := bstep (se 1 (by rfl) ⟨306080, by rfl⟩ : syracuseStep 408107 = 612161) B612161
theorem B408119 : Blo 405769 408119 := bstep (se 1 (by rfl) ⟨306089, by rfl⟩ : syracuseStep 408119 = 612179) B612179
theorem B932417 : Blo 405769 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B408139 : Blo 405769 408139 := bstep (se 1 (by rfl) ⟨306104, by rfl⟩ : syracuseStep 408139 = 612209) B612209
theorem B408151 : Blo 405769 408151 := bstep (se 1 (by rfl) ⟨306113, by rfl⟩ : syracuseStep 408151 = 612227) B612227
theorem B1030745 : Blo 405769 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B408171 : Blo 405769 408171 := bstep (se 1 (by rfl) ⟨306128, by rfl⟩ : syracuseStep 408171 = 612257) B612257
theorem B408183 : Blo 405769 408183 := bstep (se 1 (by rfl) ⟨306137, by rfl⟩ : syracuseStep 408183 = 612275) B612275
theorem B408203 : Blo 405769 408203 := bstep (se 1 (by rfl) ⟨306152, by rfl⟩ : syracuseStep 408203 = 612305) B612305
theorem B408215 : Blo 405769 408215 := bstep (se 1 (by rfl) ⟨306161, by rfl⟩ : syracuseStep 408215 = 612323) B612323
theorem B408235 : Blo 405769 408235 := bstep (se 1 (by rfl) ⟨306176, by rfl⟩ : syracuseStep 408235 = 612353) B612353
theorem B408247 : Blo 405769 408247 := bstep (se 1 (by rfl) ⟨306185, by rfl⟩ : syracuseStep 408247 = 612371) B612371
theorem B408267 : Blo 405769 408267 := bstep (se 1 (by rfl) ⟨306200, by rfl⟩ : syracuseStep 408267 = 612401) B612401
theorem B408279 : Blo 405769 408279 := bstep (se 1 (by rfl) ⟨306209, by rfl⟩ : syracuseStep 408279 = 612419) B612419
theorem B408299 : Blo 405769 408299 := bstep (se 1 (by rfl) ⟨306224, by rfl⟩ : syracuseStep 408299 = 612449) B612449
theorem B408311 : Blo 405769 408311 := bstep (se 1 (by rfl) ⟨306233, by rfl⟩ : syracuseStep 408311 = 612467) B612467
theorem B2931461 : Blo 405769 2931461 := bstep (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) B549649
theorem B408331 : Blo 405769 408331 := bstep (se 1 (by rfl) ⟨306248, by rfl⟩ : syracuseStep 408331 = 612497) B612497
theorem B867095 : Blo 405769 867095 := bstep (se 1 (by rfl) ⟨650321, by rfl⟩ : syracuseStep 867095 = 1300643) B1300643
theorem B408343 : Blo 405769 408343 := bstep (se 1 (by rfl) ⟨306257, by rfl⟩ : syracuseStep 408343 = 612515) B612515
theorem B408363 : Blo 405769 408363 := bstep (se 1 (by rfl) ⟨306272, by rfl⟩ : syracuseStep 408363 = 612545) B612545
theorem B1391411 : Blo 405769 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B408375 : Blo 405769 408375 := bstep (se 1 (by rfl) ⟨306281, by rfl⟩ : syracuseStep 408375 = 612563) B612563
theorem B408395 : Blo 405769 408395 := bstep (se 1 (by rfl) ⟨306296, by rfl⟩ : syracuseStep 408395 = 612593) B612593
theorem B408407 : Blo 405769 408407 := bstep (se 1 (by rfl) ⟨306305, by rfl⟩ : syracuseStep 408407 = 612611) B612611
theorem B408427 : Blo 405769 408427 := bstep (se 1 (by rfl) ⟨306320, by rfl⟩ : syracuseStep 408427 = 612641) B612641
theorem B408439 : Blo 405769 408439 := bstep (se 1 (by rfl) ⟨306329, by rfl⟩ : syracuseStep 408439 = 612659) B612659
theorem B408459 : Blo 405769 408459 := bstep (se 1 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 408459 = 612689) B612689
theorem B408471 : Blo 405769 408471 := bstep (se 1 (by rfl) ⟨306353, by rfl⟩ : syracuseStep 408471 = 612707) B612707
theorem B408491 : Blo 405769 408491 := bstep (se 1 (by rfl) ⟨306368, by rfl⟩ : syracuseStep 408491 = 612737) B612737
theorem B1162163 : Blo 405769 1162163 := bstep (se 1 (by rfl) ⟨871622, by rfl⟩ : syracuseStep 1162163 = 1743245) B1743245
theorem B408503 : Blo 405769 408503 := bstep (se 1 (by rfl) ⟨306377, by rfl⟩ : syracuseStep 408503 = 612755) B612755
theorem B408523 : Blo 405769 408523 := bstep (se 1 (by rfl) ⟨306392, by rfl⟩ : syracuseStep 408523 = 612785) B612785
theorem B408535 : Blo 405769 408535 := bstep (se 1 (by rfl) ⟨306401, by rfl⟩ : syracuseStep 408535 = 612803) B612803
theorem B408555 : Blo 405769 408555 := bstep (se 1 (by rfl) ⟨306416, by rfl⟩ : syracuseStep 408555 = 612833) B612833
theorem B408567 : Blo 405769 408567 := bstep (se 1 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 408567 = 612851) B612851
theorem B408587 : Blo 405769 408587 := bstep (se 1 (by rfl) ⟨306440, by rfl⟩ : syracuseStep 408587 = 612881) B612881
theorem B408599 : Blo 405769 408599 := bstep (se 1 (by rfl) ⟨306449, by rfl⟩ : syracuseStep 408599 = 612899) B612899
theorem B408619 : Blo 405769 408619 := bstep (se 1 (by rfl) ⟨306464, by rfl⟩ : syracuseStep 408619 = 612929) B612929
theorem B408631 : Blo 405769 408631 := bstep (se 1 (by rfl) ⟨306473, by rfl⟩ : syracuseStep 408631 = 612947) B612947
theorem B408651 : Blo 405769 408651 := bstep (se 1 (by rfl) ⟨306488, by rfl⟩ : syracuseStep 408651 = 612977) B612977
theorem B408663 : Blo 405769 408663 := bstep (se 1 (by rfl) ⟨306497, by rfl⟩ : syracuseStep 408663 = 612995) B612995
theorem B408683 : Blo 405769 408683 := bstep (se 1 (by rfl) ⟨306512, by rfl⟩ : syracuseStep 408683 = 613025) B613025
theorem B408695 : Blo 405769 408695 := bstep (se 1 (by rfl) ⟨306521, by rfl⟩ : syracuseStep 408695 = 613043) B613043
theorem B408715 : Blo 405769 408715 := bstep (se 1 (by rfl) ⟨306536, by rfl⟩ : syracuseStep 408715 = 613073) B613073
theorem B408727 : Blo 405769 408727 := bstep (se 1 (by rfl) ⟨306545, by rfl⟩ : syracuseStep 408727 = 613091) B613091
theorem B408747 : Blo 405769 408747 := bstep (se 1 (by rfl) ⟨306560, by rfl⟩ : syracuseStep 408747 = 613121) B613121
theorem B408759 : Blo 405769 408759 := bstep (se 1 (by rfl) ⟨306569, by rfl⟩ : syracuseStep 408759 = 613139) B613139
theorem B408779 : Blo 405769 408779 := bstep (se 1 (by rfl) ⟨306584, by rfl⟩ : syracuseStep 408779 = 613169) B613169
theorem B408791 : Blo 405769 408791 := bstep (se 1 (by rfl) ⟨306593, by rfl⟩ : syracuseStep 408791 = 613187) B613187
theorem B408811 : Blo 405769 408811 := bstep (se 1 (by rfl) ⟨306608, by rfl⟩ : syracuseStep 408811 = 613217) B613217
theorem B408823 : Blo 405769 408823 := bstep (se 1 (by rfl) ⟨306617, by rfl⟩ : syracuseStep 408823 = 613235) B613235
theorem B408843 : Blo 405769 408843 := bstep (se 1 (by rfl) ⟨306632, by rfl⟩ : syracuseStep 408843 = 613265) B613265
theorem B408855 : Blo 405769 408855 := bstep (se 1 (by rfl) ⟨306641, by rfl⟩ : syracuseStep 408855 = 613283) B613283
theorem B408875 : Blo 405769 408875 := bstep (se 1 (by rfl) ⟨306656, by rfl⟩ : syracuseStep 408875 = 613313) B613313
theorem B408887 : Blo 405769 408887 := bstep (se 1 (by rfl) ⟨306665, by rfl⟩ : syracuseStep 408887 = 613331) B613331
theorem B408907 : Blo 405769 408907 := bstep (se 1 (by rfl) ⟨306680, by rfl⟩ : syracuseStep 408907 = 613361) B613361
theorem B408919 : Blo 405769 408919 := bstep (se 1 (by rfl) ⟨306689, by rfl⟩ : syracuseStep 408919 = 613379) B613379
theorem B408939 : Blo 405769 408939 := bstep (se 1 (by rfl) ⟨306704, by rfl⟩ : syracuseStep 408939 = 613409) B613409
theorem B408951 : Blo 405769 408951 := bstep (se 1 (by rfl) ⟨306713, by rfl⟩ : syracuseStep 408951 = 613427) B613427
theorem B3489155 : Blo 405769 3489155 := bstep (se 1 (by rfl) ⟨2616866, by rfl⟩ : syracuseStep 3489155 = 5233733) B5233733
theorem B408971 : Blo 405769 408971 := bstep (se 1 (by rfl) ⟨306728, by rfl⟩ : syracuseStep 408971 = 613457) B613457
theorem B1031575 : Blo 405769 1031575 := bstep (se 1 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 1031575 = 1547363) B1547363
theorem B408983 : Blo 405769 408983 := bstep (se 1 (by rfl) ⟨306737, by rfl⟩ : syracuseStep 408983 = 613475) B613475
theorem B409003 : Blo 405769 409003 := bstep (se 1 (by rfl) ⟨306752, by rfl⟩ : syracuseStep 409003 = 613505) B613505
theorem B409015 : Blo 405769 409015 := bstep (se 1 (by rfl) ⟨306761, by rfl⟩ : syracuseStep 409015 = 613523) B613523
theorem B409035 : Blo 405769 409035 := bstep (se 1 (by rfl) ⟨306776, by rfl⟩ : syracuseStep 409035 = 613553) B613553
theorem B409047 : Blo 405769 409047 := bstep (se 1 (by rfl) ⟨306785, by rfl⟩ : syracuseStep 409047 = 613571) B613571
theorem B409067 : Blo 405769 409067 := bstep (se 1 (by rfl) ⟨306800, by rfl⟩ : syracuseStep 409067 = 613601) B613601
theorem B409079 : Blo 405769 409079 := bstep (se 1 (by rfl) ⟨306809, by rfl⟩ : syracuseStep 409079 = 613619) B613619
theorem B409099 : Blo 405769 409099 := bstep (se 1 (by rfl) ⟨306824, by rfl⟩ : syracuseStep 409099 = 613649) B613649
theorem B409111 : Blo 405769 409111 := bstep (se 1 (by rfl) ⟨306833, by rfl⟩ : syracuseStep 409111 = 613667) B613667
theorem B409131 : Blo 405769 409131 := bstep (se 1 (by rfl) ⟨306848, by rfl⟩ : syracuseStep 409131 = 613697) B613697
theorem B409143 : Blo 405769 409143 := bstep (se 1 (by rfl) ⟨306857, by rfl⟩ : syracuseStep 409143 = 613715) B613715
theorem B409163 : Blo 405769 409163 := bstep (se 1 (by rfl) ⟨306872, by rfl⟩ : syracuseStep 409163 = 613745) B613745
theorem B409175 : Blo 405769 409175 := bstep (se 1 (by rfl) ⟨306881, by rfl⟩ : syracuseStep 409175 = 613763) B613763
theorem B1097309 : Blo 405769 1097309 := bstep (se 3 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 1097309 = 411491) B411491
theorem B409195 : Blo 405769 409195 := bstep (se 1 (by rfl) ⟨306896, by rfl⟩ : syracuseStep 409195 = 613793) B613793
theorem B409207 : Blo 405769 409207 := bstep (se 1 (by rfl) ⟨306905, by rfl⟩ : syracuseStep 409207 = 613811) B613811
theorem B409227 : Blo 405769 409227 := bstep (se 1 (by rfl) ⟨306920, by rfl⟩ : syracuseStep 409227 = 613841) B613841
theorem B409239 : Blo 405769 409239 := bstep (se 1 (by rfl) ⟨306929, by rfl⟩ : syracuseStep 409239 = 613859) B613859
theorem B409259 : Blo 405769 409259 := bstep (se 1 (by rfl) ⟨306944, by rfl⟩ : syracuseStep 409259 = 613889) B613889
theorem B409271 : Blo 405769 409271 := bstep (se 1 (by rfl) ⟨306953, by rfl⟩ : syracuseStep 409271 = 613907) B613907
theorem B409291 : Blo 405769 409291 := bstep (se 1 (by rfl) ⟨306968, by rfl⟩ : syracuseStep 409291 = 613937) B613937
theorem B409303 : Blo 405769 409303 := bstep (se 1 (by rfl) ⟨306977, by rfl⟩ : syracuseStep 409303 = 613955) B613955
theorem B409323 : Blo 405769 409323 := bstep (se 1 (by rfl) ⟨306992, by rfl⟩ : syracuseStep 409323 = 613985) B613985
theorem B409335 : Blo 405769 409335 := bstep (se 1 (by rfl) ⟨307001, by rfl⟩ : syracuseStep 409335 = 614003) B614003
theorem B409355 : Blo 405769 409355 := bstep (se 1 (by rfl) ⟨307016, by rfl⟩ : syracuseStep 409355 = 614033) B614033
theorem B409367 : Blo 405769 409367 := bstep (se 1 (by rfl) ⟨307025, by rfl⟩ : syracuseStep 409367 = 614051) B614051
theorem B933655 : Blo 405769 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B409387 : Blo 405769 409387 := bstep (se 1 (by rfl) ⟨307040, by rfl⟩ : syracuseStep 409387 = 614081) B614081
theorem B409399 : Blo 405769 409399 := bstep (se 1 (by rfl) ⟨307049, by rfl⟩ : syracuseStep 409399 = 614099) B614099
theorem B868171 : Blo 405769 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B1032011 : Blo 405769 1032011 := bstep (se 1 (by rfl) ⟨774008, by rfl⟩ : syracuseStep 1032011 = 1548017) B1548017
theorem B409419 : Blo 405769 409419 := bstep (se 1 (by rfl) ⟨307064, by rfl⟩ : syracuseStep 409419 = 614129) B614129
theorem B409431 : Blo 405769 409431 := bstep (se 1 (by rfl) ⟨307073, by rfl⟩ : syracuseStep 409431 = 614147) B614147
theorem B409451 : Blo 405769 409451 := bstep (se 1 (by rfl) ⟨307088, by rfl⟩ : syracuseStep 409451 = 614177) B614177
theorem B409463 : Blo 405769 409463 := bstep (se 1 (by rfl) ⟨307097, by rfl⟩ : syracuseStep 409463 = 614195) B614195
theorem B409483 : Blo 405769 409483 := bstep (se 1 (by rfl) ⟨307112, by rfl⟩ : syracuseStep 409483 = 614225) B614225
theorem B409495 : Blo 405769 409495 := bstep (se 1 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 409495 = 614243) B614243
theorem B409515 : Blo 405769 409515 := bstep (se 1 (by rfl) ⟨307136, by rfl⟩ : syracuseStep 409515 = 614273) B614273
theorem B2473907 : Blo 405769 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B409527 : Blo 405769 409527 := bstep (se 1 (by rfl) ⟨307145, by rfl⟩ : syracuseStep 409527 = 614291) B614291
theorem B409547 : Blo 405769 409547 := bstep (se 1 (by rfl) ⟨307160, by rfl⟩ : syracuseStep 409547 = 614321) B614321
theorem B409559 : Blo 405769 409559 := bstep (se 1 (by rfl) ⟨307169, by rfl⟩ : syracuseStep 409559 = 614339) B614339
theorem B409579 : Blo 405769 409579 := bstep (se 1 (by rfl) ⟨307184, by rfl⟩ : syracuseStep 409579 = 614369) B614369
theorem B409591 : Blo 405769 409591 := bstep (se 1 (by rfl) ⟨307193, by rfl⟩ : syracuseStep 409591 = 614387) B614387
theorem B409611 : Blo 405769 409611 := bstep (se 1 (by rfl) ⟨307208, by rfl⟩ : syracuseStep 409611 = 614417) B614417
theorem B409623 : Blo 405769 409623 := bstep (se 1 (by rfl) ⟨307217, by rfl⟩ : syracuseStep 409623 = 614435) B614435
theorem B409643 : Blo 405769 409643 := bstep (se 1 (by rfl) ⟨307232, by rfl⟩ : syracuseStep 409643 = 614465) B614465
theorem B409655 : Blo 405769 409655 := bstep (se 1 (by rfl) ⟨307241, by rfl⟩ : syracuseStep 409655 = 614483) B614483
theorem B1720385 : Blo 405769 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B409675 : Blo 405769 409675 := bstep (se 1 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 409675 = 614513) B614513
theorem B409687 : Blo 405769 409687 := bstep (se 1 (by rfl) ⟨307265, by rfl⟩ : syracuseStep 409687 = 614531) B614531
theorem B409707 : Blo 405769 409707 := bstep (se 1 (by rfl) ⟨307280, by rfl⟩ : syracuseStep 409707 = 614561) B614561
theorem B409719 : Blo 405769 409719 := bstep (se 1 (by rfl) ⟨307289, by rfl⟩ : syracuseStep 409719 = 614579) B614579
theorem B409739 : Blo 405769 409739 := bstep (se 1 (by rfl) ⟨307304, by rfl⟩ : syracuseStep 409739 = 614609) B614609
theorem B409751 : Blo 405769 409751 := bstep (se 1 (by rfl) ⟨307313, by rfl⟩ : syracuseStep 409751 = 614627) B614627
theorem B1032385 : Blo 405769 1032385 := bstep (se 2 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 1032385 = 774289) B774289
theorem B737623 : Blo 405769 737623 := bstep (se 1 (by rfl) ⟨553217, by rfl⟩ : syracuseStep 737623 = 1106435) B1106435
theorem B3293713 : Blo 405769 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B868889 : Blo 405769 868889 := bstep (se 2 (by rfl) ⟨325833, by rfl⟩ : syracuseStep 868889 = 651667) B651667
theorem B1032983 : Blo 405769 1032983 := bstep (se 1 (by rfl) ⟨774737, by rfl⟩ : syracuseStep 1032983 = 1549475) B1549475
theorem B2311091 : Blo 405769 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B869401 : Blo 405769 869401 := bstep (se 2 (by rfl) ⟨326025, by rfl⟩ : syracuseStep 869401 = 652051) B652051
theorem B9290821 : Blo 405769 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B869555 : Blo 405769 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B771275 : Blo 405769 771275 := bstep (se 1 (by rfl) ⟨578456, by rfl⟩ : syracuseStep 771275 = 1156913) B1156913
theorem B5850467 : Blo 405769 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B771457 : Blo 405769 771457 := bstep (se 2 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 771457 = 578593) B578593
theorem B1164851 : Blo 405769 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B1033793 : Blo 405769 1033793 := bstep (se 2 (by rfl) ⟨387672, by rfl⟩ : syracuseStep 1033793 = 775345) B775345
theorem B3491545 : Blo 405769 3491545 := bstep (se 2 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 3491545 = 2618659) B2618659
theorem B1165079 : Blo 405769 1165079 := bstep (se 1 (by rfl) ⟨873809, by rfl⟩ : syracuseStep 1165079 = 1747619) B1747619
theorem B771905 : Blo 405769 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B1165387 : Blo 405769 1165387 := bstep (se 1 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 1165387 = 1748081) B1748081
theorem B1034329 : Blo 405769 1034329 := bstep (se 2 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 1034329 = 775747) B775747
theorem B870529 : Blo 405769 870529 := bstep (se 2 (by rfl) ⟨326448, by rfl⟩ : syracuseStep 870529 = 652897) B652897
theorem B772247 : Blo 405769 772247 := bstep (se 1 (by rfl) ⟨579185, by rfl⟩ : syracuseStep 772247 = 1158371) B1158371
theorem B1657025 : Blo 405769 1657025 := bstep (se 2 (by rfl) ⟨621384, by rfl⟩ : syracuseStep 1657025 = 1242769) B1242769
theorem B2869465 : Blo 405769 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B1165661 : Blo 405769 1165661 := bstep (se 3 (by rfl) ⟨218561, by rfl⟩ : syracuseStep 1165661 = 437123) B437123
theorem B2312549 : Blo 405769 2312549 := bstep (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) B433603
theorem B608663 : Blo 405769 608663 := bstep (se 1 (by rfl) ⟨456497, by rfl⟩ : syracuseStep 608663 = 912995) B912995
theorem B2214323 : Blo 405769 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B870871 : Blo 405769 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B608729 : Blo 405769 608729 := bstep (se 2 (by rfl) ⟨228273, by rfl⟩ : syracuseStep 608729 = 456547) B456547
theorem B608843 : Blo 405769 608843 := bstep (se 1 (by rfl) ⟨456632, by rfl⟩ : syracuseStep 608843 = 913265) B913265
theorem B608855 : Blo 405769 608855 := bstep (se 1 (by rfl) ⟨456641, by rfl⟩ : syracuseStep 608855 = 913283) B913283
theorem B2083421 : Blo 405769 2083421 := bstep (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) B781283
theorem B3492503 : Blo 405769 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B608921 : Blo 405769 608921 := bstep (se 2 (by rfl) ⟨228345, by rfl⟩ : syracuseStep 608921 = 456691) B456691
theorem B412363 : Blo 405769 412363 := bstep (se 1 (by rfl) ⟨309272, by rfl⟩ : syracuseStep 412363 = 618545) B618545
theorem B609035 : Blo 405769 609035 := bstep (se 1 (by rfl) ⟨456776, by rfl⟩ : syracuseStep 609035 = 913553) B913553
theorem B609047 : Blo 405769 609047 := bstep (se 1 (by rfl) ⟨456785, by rfl⟩ : syracuseStep 609047 = 913571) B913571
theorem B772915 : Blo 405769 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B609113 : Blo 405769 609113 := bstep (se 2 (by rfl) ⟨228417, by rfl⟩ : syracuseStep 609113 = 456835) B456835
theorem B871307 : Blo 405769 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B609227 : Blo 405769 609227 := bstep (se 1 (by rfl) ⟨456920, by rfl⟩ : syracuseStep 609227 = 913841) B913841
theorem B609239 : Blo 405769 609239 := bstep (se 1 (by rfl) ⟨456929, by rfl⟩ : syracuseStep 609239 = 913859) B913859
theorem B3492881 : Blo 405769 3492881 := bstep (se 2 (by rfl) ⟨1309830, by rfl⟩ : syracuseStep 3492881 = 2619661) B2619661
theorem B609305 : Blo 405769 609305 := bstep (se 2 (by rfl) ⟨228489, by rfl⟩ : syracuseStep 609305 = 456979) B456979
theorem B11160611 : Blo 405769 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B1657901 : Blo 405769 1657901 := bstep (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) B621713
theorem B609419 : Blo 405769 609419 := bstep (se 1 (by rfl) ⟨457064, by rfl⟩ : syracuseStep 609419 = 914129) B914129
theorem B609431 : Blo 405769 609431 := bstep (se 1 (by rfl) ⟨457073, by rfl⟩ : syracuseStep 609431 = 914147) B914147
theorem B2608307 : Blo 405769 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B1035443 : Blo 405769 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B609497 : Blo 405769 609497 := bstep (se 2 (by rfl) ⟨228561, by rfl⟩ : syracuseStep 609497 = 457123) B457123
theorem B773363 : Blo 405769 773363 := bstep (se 1 (by rfl) ⟨580022, by rfl⟩ : syracuseStep 773363 = 1160045) B1160045
theorem B773401 : Blo 405769 773401 := bstep (se 2 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 773401 = 580051) B580051
theorem B609611 : Blo 405769 609611 := bstep (se 1 (by rfl) ⟨457208, by rfl⟩ : syracuseStep 609611 = 914417) B914417
theorem B609623 : Blo 405769 609623 := bstep (se 1 (by rfl) ⟨457217, by rfl⟩ : syracuseStep 609623 = 914435) B914435
theorem B609689 : Blo 405769 609689 := bstep (se 2 (by rfl) ⟨228633, by rfl⟩ : syracuseStep 609689 = 457267) B457267
theorem B1035737 : Blo 405769 1035737 := bstep (se 2 (by rfl) ⟨388401, by rfl⟩ : syracuseStep 1035737 = 776803) B776803
theorem B609803 : Blo 405769 609803 := bstep (se 1 (by rfl) ⟨457352, by rfl⟩ : syracuseStep 609803 = 914705) B914705
theorem B609815 : Blo 405769 609815 := bstep (se 1 (by rfl) ⟨457361, by rfl⟩ : syracuseStep 609815 = 914723) B914723
theorem B609881 : Blo 405769 609881 := bstep (se 2 (by rfl) ⟨228705, by rfl⟩ : syracuseStep 609881 = 457411) B457411
theorem B609995 : Blo 405769 609995 := bstep (se 1 (by rfl) ⟨457496, by rfl⟩ : syracuseStep 609995 = 914993) B914993
theorem B610007 : Blo 405769 610007 := bstep (se 1 (by rfl) ⟨457505, by rfl⟩ : syracuseStep 610007 = 915011) B915011
theorem B773849 : Blo 405769 773849 := bstep (se 2 (by rfl) ⟨290193, by rfl⟩ : syracuseStep 773849 = 580387) B580387
theorem B1396445 : Blo 405769 1396445 := bstep (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) B523667
theorem B872203 : Blo 405769 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B610073 : Blo 405769 610073 := bstep (se 2 (by rfl) ⟨228777, by rfl⟩ : syracuseStep 610073 = 457555) B457555
theorem B4771685 : Blo 405769 4771685 := bstep (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) B894691
theorem B610187 : Blo 405769 610187 := bstep (se 1 (by rfl) ⟨457640, by rfl⟩ : syracuseStep 610187 = 915281) B915281
theorem B610199 : Blo 405769 610199 := bstep (se 1 (by rfl) ⟨457649, by rfl⟩ : syracuseStep 610199 = 915299) B915299
theorem B19812275 : Blo 405769 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B610265 : Blo 405769 610265 := bstep (se 2 (by rfl) ⟨228849, by rfl⟩ : syracuseStep 610265 = 457699) B457699
theorem B610379 : Blo 405769 610379 := bstep (se 1 (by rfl) ⟨457784, by rfl⟩ : syracuseStep 610379 = 915569) B915569
theorem B610391 : Blo 405769 610391 := bstep (se 1 (by rfl) ⟨457793, by rfl⟩ : syracuseStep 610391 = 915587) B915587
theorem B610457 : Blo 405769 610457 := bstep (se 2 (by rfl) ⟨228921, by rfl⟩ : syracuseStep 610457 = 457843) B457843
theorem B610571 : Blo 405769 610571 := bstep (se 1 (by rfl) ⟨457928, by rfl⟩ : syracuseStep 610571 = 915857) B915857
theorem B610583 : Blo 405769 610583 := bstep (se 1 (by rfl) ⟨457937, by rfl⟩ : syracuseStep 610583 = 915875) B915875
theorem B610649 : Blo 405769 610649 := bstep (se 2 (by rfl) ⟨228993, by rfl⟩ : syracuseStep 610649 = 457987) B457987
theorem B774593 : Blo 405769 774593 := bstep (se 2 (by rfl) ⟨290472, by rfl⟩ : syracuseStep 774593 = 580945) B580945
theorem B610763 : Blo 405769 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B610775 : Blo 405769 610775 := bstep (se 1 (by rfl) ⟨458081, by rfl⟩ : syracuseStep 610775 = 916163) B916163
theorem B872947 : Blo 405769 872947 := bstep (se 1 (by rfl) ⟨654710, by rfl⟩ : syracuseStep 872947 = 1309421) B1309421
theorem B6279697 : Blo 405769 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B610841 : Blo 405769 610841 := bstep (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) B458131
theorem B1659457 : Blo 405769 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B1659523 : Blo 405769 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B610955 : Blo 405769 610955 := bstep (se 1 (by rfl) ⟨458216, by rfl⟩ : syracuseStep 610955 = 916433) B916433
theorem B610967 : Blo 405769 610967 := bstep (se 1 (by rfl) ⟨458225, by rfl⟩ : syracuseStep 610967 = 916451) B916451
theorem B1462963 : Blo 405769 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B774859 : Blo 405769 774859 := bstep (se 1 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 774859 = 1162289) B1162289
theorem B611033 : Blo 405769 611033 := bstep (se 2 (by rfl) ⟨229137, by rfl⟩ : syracuseStep 611033 = 458275) B458275
theorem B611147 : Blo 405769 611147 := bstep (se 1 (by rfl) ⟨458360, by rfl⟩ : syracuseStep 611147 = 916721) B916721
theorem B611159 : Blo 405769 611159 := bstep (se 1 (by rfl) ⟨458369, by rfl⟩ : syracuseStep 611159 = 916739) B916739
theorem B611225 : Blo 405769 611225 := bstep (se 2 (by rfl) ⟨229209, by rfl⟩ : syracuseStep 611225 = 458419) B458419
theorem B578507 : Blo 405769 578507 := bstep (se 1 (by rfl) ⟨433880, by rfl⟩ : syracuseStep 578507 = 867761) B867761
theorem B873433 : Blo 405769 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B611339 : Blo 405769 611339 := bstep (se 1 (by rfl) ⟨458504, by rfl⟩ : syracuseStep 611339 = 917009) B917009
theorem B611351 : Blo 405769 611351 := bstep (se 1 (by rfl) ⟨458513, by rfl⟩ : syracuseStep 611351 = 917027) B917027
theorem B611417 : Blo 405769 611417 := bstep (se 2 (by rfl) ⟨229281, by rfl⟩ : syracuseStep 611417 = 458563) B458563
theorem B775307 : Blo 405769 775307 := bstep (se 1 (by rfl) ⟨581480, by rfl⟩ : syracuseStep 775307 = 1162961) B1162961
theorem B611531 : Blo 405769 611531 := bstep (se 1 (by rfl) ⟨458648, by rfl⟩ : syracuseStep 611531 = 917297) B917297
theorem B611543 : Blo 405769 611543 := bstep (se 1 (by rfl) ⟨458657, by rfl⟩ : syracuseStep 611543 = 917315) B917315
theorem B611609 : Blo 405769 611609 := bstep (se 2 (by rfl) ⟨229353, by rfl⟩ : syracuseStep 611609 = 458707) B458707
theorem B1955117 : Blo 405769 1955117 := bstep (se 3 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 1955117 = 733169) B733169
theorem B775489 : Blo 405769 775489 := bstep (se 2 (by rfl) ⟨290808, by rfl⟩ : syracuseStep 775489 = 581617) B581617
theorem B611723 : Blo 405769 611723 := bstep (se 1 (by rfl) ⟨458792, by rfl⟩ : syracuseStep 611723 = 917585) B917585
theorem B611735 : Blo 405769 611735 := bstep (se 1 (by rfl) ⟨458801, by rfl⟩ : syracuseStep 611735 = 917603) B917603
theorem B611801 : Blo 405769 611801 := bstep (se 2 (by rfl) ⟨229425, by rfl⟩ : syracuseStep 611801 = 458851) B458851
theorem B1103321 : Blo 405769 1103321 := bstep (se 2 (by rfl) ⟨413745, by rfl⟩ : syracuseStep 1103321 = 827491) B827491
theorem B611915 : Blo 405769 611915 := bstep (se 1 (by rfl) ⟨458936, by rfl⟩ : syracuseStep 611915 = 917873) B917873
theorem B611927 : Blo 405769 611927 := bstep (se 1 (by rfl) ⟨458945, by rfl⟩ : syracuseStep 611927 = 917891) B917891
theorem B415351 : Blo 405769 415351 := bstep (se 1 (by rfl) ⟨311513, by rfl⟩ : syracuseStep 415351 = 623027) B623027
theorem B775831 : Blo 405769 775831 := bstep (se 1 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 775831 = 1163747) B1163747
theorem B611993 : Blo 405769 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B1103581 : Blo 405769 1103581 := bstep (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) B413843
theorem B513803 : Blo 405769 513803 := bstep (se 1 (by rfl) ⟨385352, by rfl⟩ : syracuseStep 513803 = 770705) B770705
theorem B612107 : Blo 405769 612107 := bstep (se 1 (by rfl) ⟨459080, by rfl⟩ : syracuseStep 612107 = 918161) B918161
theorem B612119 : Blo 405769 612119 := bstep (se 1 (by rfl) ⟨459089, by rfl⟩ : syracuseStep 612119 = 918179) B918179
theorem B612185 : Blo 405769 612185 := bstep (se 2 (by rfl) ⟨229569, by rfl⟩ : syracuseStep 612185 = 459139) B459139
theorem B776051 : Blo 405769 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B1496983 : Blo 405769 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B612299 : Blo 405769 612299 := bstep (se 1 (by rfl) ⟨459224, by rfl⟩ : syracuseStep 612299 = 918449) B918449
theorem B612311 : Blo 405769 612311 := bstep (se 1 (by rfl) ⟨459233, by rfl⟩ : syracuseStep 612311 = 918467) B918467
theorem B612377 : Blo 405769 612377 := bstep (se 2 (by rfl) ⟨229641, by rfl⟩ : syracuseStep 612377 = 459283) B459283
theorem B776279 : Blo 405769 776279 := bstep (se 1 (by rfl) ⟨582209, by rfl⟩ : syracuseStep 776279 = 1164419) B1164419
theorem B612491 : Blo 405769 612491 := bstep (se 1 (by rfl) ⟨459368, by rfl⟩ : syracuseStep 612491 = 918737) B918737
theorem B12572813 : Blo 405769 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B612503 : Blo 405769 612503 := bstep (se 1 (by rfl) ⟨459377, by rfl⟩ : syracuseStep 612503 = 918755) B918755
theorem B1464493 : Blo 405769 1464493 := bstep (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) B549185
theorem B612569 : Blo 405769 612569 := bstep (se 2 (by rfl) ⟨229713, by rfl⟩ : syracuseStep 612569 = 459427) B459427
theorem B1235251 : Blo 405769 1235251 := bstep (se 1 (by rfl) ⟨926438, by rfl⟩ : syracuseStep 1235251 = 1852877) B1852877
theorem B4413761 : Blo 405769 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B612683 : Blo 405769 612683 := bstep (se 1 (by rfl) ⟨459512, by rfl⟩ : syracuseStep 612683 = 919025) B919025
theorem B612695 : Blo 405769 612695 := bstep (se 1 (by rfl) ⟨459521, by rfl⟩ : syracuseStep 612695 = 919043) B919043
theorem B776537 : Blo 405769 776537 := bstep (se 2 (by rfl) ⟨291201, by rfl⟩ : syracuseStep 776537 = 582403) B582403
theorem B874903 : Blo 405769 874903 := bstep (se 1 (by rfl) ⟨656177, by rfl⟩ : syracuseStep 874903 = 1312355) B1312355
theorem B612761 : Blo 405769 612761 := bstep (se 2 (by rfl) ⟨229785, by rfl⟩ : syracuseStep 612761 = 459571) B459571
theorem B514507 : Blo 405769 514507 := bstep (se 1 (by rfl) ⟨385880, by rfl⟩ : syracuseStep 514507 = 771761) B771761
theorem B874955 : Blo 405769 874955 := bstep (se 1 (by rfl) ⟨656216, by rfl⟩ : syracuseStep 874955 = 1312433) B1312433
theorem B612875 : Blo 405769 612875 := bstep (se 1 (by rfl) ⟨459656, by rfl⟩ : syracuseStep 612875 = 919313) B919313
theorem B1301015 : Blo 405769 1301015 := bstep (se 1 (by rfl) ⟨975761, by rfl⟩ : syracuseStep 1301015 = 1951523) B1951523
theorem B612887 : Blo 405769 612887 := bstep (se 1 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 612887 = 919331) B919331
theorem B6937163 : Blo 405769 6937163 := bstep (se 1 (by rfl) ⟨5202872, by rfl⟩ : syracuseStep 6937163 = 10405745) B10405745
theorem B612953 : Blo 405769 612953 := bstep (se 2 (by rfl) ⟨229857, by rfl⟩ : syracuseStep 612953 = 459715) B459715
theorem B2054807 : Blo 405769 2054807 := bstep (se 1 (by rfl) ⟨1541105, by rfl⟩ : syracuseStep 2054807 = 3082211) B3082211
theorem B1759895 : Blo 405769 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B613067 : Blo 405769 613067 := bstep (se 1 (by rfl) ⟨459800, by rfl⟩ : syracuseStep 613067 = 919601) B919601
theorem B514775 : Blo 405769 514775 := bstep (se 1 (by rfl) ⟨386081, by rfl⟩ : syracuseStep 514775 = 772163) B772163
theorem B613079 : Blo 405769 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B776947 : Blo 405769 776947 := bstep (se 1 (by rfl) ⟨582710, by rfl⟩ : syracuseStep 776947 = 1165421) B1165421
theorem B580375 : Blo 405769 580375 := bstep (se 1 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 580375 = 870563) B870563
theorem B613145 : Blo 405769 613145 := bstep (se 2 (by rfl) ⟨229929, by rfl⟩ : syracuseStep 613145 = 459859) B459859
theorem B613259 : Blo 405769 613259 := bstep (se 1 (by rfl) ⟨459944, by rfl⟩ : syracuseStep 613259 = 919889) B919889
theorem B613271 : Blo 405769 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B2710451 : Blo 405769 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B1104857 : Blo 405769 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B613337 : Blo 405769 613337 := bstep (se 2 (by rfl) ⟨230001, by rfl⟩ : syracuseStep 613337 = 460003) B460003
theorem B613451 : Blo 405769 613451 := bstep (se 1 (by rfl) ⟨460088, by rfl⟩ : syracuseStep 613451 = 920177) B920177
theorem B613463 : Blo 405769 613463 := bstep (se 1 (by rfl) ⟨460097, by rfl⟩ : syracuseStep 613463 = 920195) B920195
theorem B613529 : Blo 405769 613529 := bstep (se 2 (by rfl) ⟨230073, by rfl⟩ : syracuseStep 613529 = 460147) B460147
theorem B777433 : Blo 405769 777433 := bstep (se 2 (by rfl) ⟨291537, by rfl⟩ : syracuseStep 777433 = 583075) B583075
theorem B613643 : Blo 405769 613643 := bstep (se 1 (by rfl) ⟨460232, by rfl⟩ : syracuseStep 613643 = 920465) B920465
theorem B613655 : Blo 405769 613655 := bstep (se 1 (by rfl) ⟨460241, by rfl⟩ : syracuseStep 613655 = 920483) B920483
theorem B613721 : Blo 405769 613721 := bstep (se 2 (by rfl) ⟨230145, by rfl⟩ : syracuseStep 613721 = 460291) B460291
theorem B515479 : Blo 405769 515479 := bstep (se 1 (by rfl) ⟨386609, by rfl⟩ : syracuseStep 515479 = 773219) B773219
theorem B613835 : Blo 405769 613835 := bstep (se 1 (by rfl) ⟨460376, by rfl⟩ : syracuseStep 613835 = 920753) B920753
theorem B613847 : Blo 405769 613847 := bstep (se 1 (by rfl) ⟨460385, by rfl⟩ : syracuseStep 613847 = 920771) B920771
theorem B613913 : Blo 405769 613913 := bstep (se 2 (by rfl) ⟨230217, by rfl⟩ : syracuseStep 613913 = 460435) B460435
theorem B614027 : Blo 405769 614027 := bstep (se 1 (by rfl) ⟨460520, by rfl⟩ : syracuseStep 614027 = 921041) B921041
theorem B614039 : Blo 405769 614039 := bstep (se 1 (by rfl) ⟨460529, by rfl⟩ : syracuseStep 614039 = 921059) B921059
theorem B614105 : Blo 405769 614105 := bstep (se 2 (by rfl) ⟨230289, by rfl⟩ : syracuseStep 614105 = 460579) B460579
theorem B614219 : Blo 405769 614219 := bstep (se 1 (by rfl) ⟨460664, by rfl⟩ : syracuseStep 614219 = 921329) B921329
theorem B614231 : Blo 405769 614231 := bstep (se 1 (by rfl) ⟨460673, by rfl⟩ : syracuseStep 614231 = 921347) B921347
theorem B614297 : Blo 405769 614297 := bstep (se 2 (by rfl) ⟨230361, by rfl⟩ : syracuseStep 614297 = 460723) B460723
theorem B614411 : Blo 405769 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B614423 : Blo 405769 614423 := bstep (se 1 (by rfl) ⟨460817, by rfl⟩ : syracuseStep 614423 = 921635) B921635
theorem B2318381 : Blo 405769 2318381 := bstep (se 3 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 2318381 = 869393) B869393
theorem B614489 : Blo 405769 614489 := bstep (se 2 (by rfl) ⟨230433, by rfl⟩ : syracuseStep 614489 = 460867) B460867
theorem B1958039 : Blo 405769 1958039 := bstep (se 1 (by rfl) ⟨1468529, by rfl⟩ : syracuseStep 1958039 = 2937059) B2937059
theorem B975041 : Blo 405769 975041 := bstep (se 2 (by rfl) ⟨365640, by rfl⟩ : syracuseStep 975041 = 731281) B731281
theorem B614603 : Blo 405769 614603 := bstep (se 1 (by rfl) ⟨460952, by rfl⟩ : syracuseStep 614603 = 921905) B921905
theorem B614615 : Blo 405769 614615 := bstep (se 1 (by rfl) ⟨460961, by rfl⟩ : syracuseStep 614615 = 921923) B921923
theorem B942401 : Blo 405769 942401 := bstep (se 2 (by rfl) ⟨353400, by rfl⟩ : syracuseStep 942401 = 706801) B706801
theorem B8479667 : Blo 405769 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B975809 : Blo 405769 975809 := bstep (se 2 (by rfl) ⟨365928, by rfl⟩ : syracuseStep 975809 = 731857) B731857
theorem B517195 : Blo 405769 517195 := bstep (se 1 (by rfl) ⟨387896, by rfl⟩ : syracuseStep 517195 = 775793) B775793
theorem B1303897 : Blo 405769 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B1795421 : Blo 405769 1795421 := bstep (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) B673283
theorem B1369547 : Blo 405769 1369547 := bstep (se 1 (by rfl) ⟨1027160, by rfl⟩ : syracuseStep 1369547 = 2054321) B2054321
theorem B419275 : Blo 405769 419275 := bstep (se 1 (by rfl) ⟨314456, by rfl⟩ : syracuseStep 419275 = 628913) B628913
theorem B2090647 : Blo 405769 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B1861271 : Blo 405769 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B1369817 : Blo 405769 1369817 := bstep (se 2 (by rfl) ⟨513681, by rfl⟩ : syracuseStep 1369817 = 1027363) B1027363
theorem B419671 : Blo 405769 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B518167 : Blo 405769 518167 := bstep (se 1 (by rfl) ⟨388625, by rfl⟩ : syracuseStep 518167 = 777251) B777251
theorem B2058371 : Blo 405769 2058371 := bstep (se 1 (by rfl) ⟨1543778, by rfl⟩ : syracuseStep 2058371 = 3087557) B3087557
theorem B3500293 : Blo 405769 3500293 := bstep (se 4 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 3500293 = 656305) B656305
theorem B2320771 : Blo 405769 2320771 := bstep (se 1 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 2320771 = 3481157) B3481157
theorem B1370519 : Blo 405769 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B1043147 : Blo 405769 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B1469249 : Blo 405769 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B1371059 : Blo 405769 1371059 := bstep (se 1 (by rfl) ⟨1028294, by rfl⟩ : syracuseStep 1371059 = 2056589) B2056589
theorem B1371329 : Blo 405769 1371329 := bstep (se 2 (by rfl) ⟨514248, by rfl⟩ : syracuseStep 1371329 = 1028497) B1028497
theorem B5860613 : Blo 405769 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B2321729 : Blo 405769 2321729 := bstep (se 2 (by rfl) ⟨870648, by rfl⟩ : syracuseStep 2321729 = 1741297) B1741297
theorem B1306049 : Blo 405769 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B913049 : Blo 405769 913049 := bstep (se 2 (by rfl) ⟨342393, by rfl⟩ : syracuseStep 913049 = 684787) B684787
theorem B618187 : Blo 405769 618187 := bstep (se 1 (by rfl) ⟨463640, by rfl⟩ : syracuseStep 618187 = 927281) B927281
theorem B1371869 : Blo 405769 1371869 := bstep (se 3 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 1371869 = 514451) B514451
theorem B913139 : Blo 405769 913139 := bstep (se 1 (by rfl) ⟨684854, by rfl⟩ : syracuseStep 913139 = 1369709) B1369709
theorem B454411 : Blo 405769 454411 := bstep (se 1 (by rfl) ⟨340808, by rfl⟩ : syracuseStep 454411 = 681617) B681617
theorem B913175 : Blo 405769 913175 := bstep (se 1 (by rfl) ⟨684881, by rfl⟩ : syracuseStep 913175 = 1369763) B1369763
theorem B913355 : Blo 405769 913355 := bstep (se 1 (by rfl) ⟨685016, by rfl⟩ : syracuseStep 913355 = 1370033) B1370033
theorem B913409 : Blo 405769 913409 := bstep (se 2 (by rfl) ⟨342528, by rfl⟩ : syracuseStep 913409 = 685057) B685057
theorem B913625 : Blo 405769 913625 := bstep (se 2 (by rfl) ⟨342609, by rfl⟩ : syracuseStep 913625 = 685219) B685219
theorem B913715 : Blo 405769 913715 := bstep (se 1 (by rfl) ⟨685286, by rfl⟩ : syracuseStep 913715 = 1370573) B1370573
theorem B1962305 : Blo 405769 1962305 := bstep (se 2 (by rfl) ⟨735864, by rfl⟩ : syracuseStep 1962305 = 1471729) B1471729
theorem B913751 : Blo 405769 913751 := bstep (se 1 (by rfl) ⟨685313, by rfl⟩ : syracuseStep 913751 = 1370627) B1370627
theorem B913931 : Blo 405769 913931 := bstep (se 1 (by rfl) ⟨685448, by rfl⟩ : syracuseStep 913931 = 1370897) B1370897
theorem B913985 : Blo 405769 913985 := bstep (se 2 (by rfl) ⟨342744, by rfl⟩ : syracuseStep 913985 = 685489) B685489
theorem B914201 : Blo 405769 914201 := bstep (se 2 (by rfl) ⟨342825, by rfl⟩ : syracuseStep 914201 = 685651) B685651
theorem B1471297 : Blo 405769 1471297 := bstep (se 2 (by rfl) ⟨551736, by rfl⟩ : syracuseStep 1471297 = 1103473) B1103473
theorem B684875 : Blo 405769 684875 := bstep (se 1 (by rfl) ⟨513656, by rfl⟩ : syracuseStep 684875 = 1027313) B1027313
theorem B1373003 : Blo 405769 1373003 := bstep (se 1 (by rfl) ⟨1029752, by rfl⟩ : syracuseStep 1373003 = 2059505) B2059505
theorem B914291 : Blo 405769 914291 := bstep (se 1 (by rfl) ⟨685718, by rfl⟩ : syracuseStep 914291 = 1371437) B1371437
theorem B1733507 : Blo 405769 1733507 := bstep (se 1 (by rfl) ⟨1300130, by rfl⟩ : syracuseStep 1733507 = 2600261) B2600261
theorem B914327 : Blo 405769 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B685003 : Blo 405769 685003 := bstep (se 1 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 685003 = 1027505) B1027505
theorem B6976529 : Blo 405769 6976529 := bstep (se 2 (by rfl) ⟨2616198, by rfl⟩ : syracuseStep 6976529 = 5232397) B5232397
theorem B914507 : Blo 405769 914507 := bstep (se 1 (by rfl) ⟨685880, by rfl⟩ : syracuseStep 914507 = 1371761) B1371761
theorem B685145 : Blo 405769 685145 := bstep (se 2 (by rfl) ⟨256929, by rfl⟩ : syracuseStep 685145 = 513859) B513859
theorem B1373273 : Blo 405769 1373273 := bstep (se 2 (by rfl) ⟨514977, by rfl⟩ : syracuseStep 1373273 = 1029955) B1029955
theorem B914561 : Blo 405769 914561 := bstep (se 2 (by rfl) ⟨342960, by rfl⟩ : syracuseStep 914561 = 685921) B685921
theorem B3929219 : Blo 405769 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B488587 : Blo 405769 488587 := bstep (se 1 (by rfl) ⟨366440, by rfl⟩ : syracuseStep 488587 = 732881) B732881
theorem B685273 : Blo 405769 685273 := bstep (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) B513955
theorem B914777 : Blo 405769 914777 := bstep (se 2 (by rfl) ⟨343041, by rfl⟩ : syracuseStep 914777 = 686083) B686083
theorem B2946455 : Blo 405769 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B914867 : Blo 405769 914867 := bstep (se 1 (by rfl) ⟨686150, by rfl⟩ : syracuseStep 914867 = 1372301) B1372301
theorem B914903 : Blo 405769 914903 := bstep (se 1 (by rfl) ⟨686177, by rfl⟩ : syracuseStep 914903 = 1372355) B1372355
theorem B2651741 : Blo 405769 2651741 := bstep (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) B994403
theorem B915083 : Blo 405769 915083 := bstep (se 1 (by rfl) ⟨686312, by rfl⟩ : syracuseStep 915083 = 1372625) B1372625
theorem B915137 : Blo 405769 915137 := bstep (se 2 (by rfl) ⟨343176, by rfl⟩ : syracuseStep 915137 = 686353) B686353
theorem B2062097 : Blo 405769 2062097 := bstep (se 2 (by rfl) ⟨773286, by rfl⟩ : syracuseStep 2062097 = 1546573) B1546573
theorem B685847 : Blo 405769 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B1373975 : Blo 405769 1373975 := bstep (se 1 (by rfl) ⟨1030481, by rfl⟩ : syracuseStep 1373975 = 2060963) B2060963
theorem B685975 : Blo 405769 685975 := bstep (se 1 (by rfl) ⟨514481, by rfl⟩ : syracuseStep 685975 = 1028963) B1028963
theorem B915353 : Blo 405769 915353 := bstep (se 2 (by rfl) ⟨343257, by rfl⟩ : syracuseStep 915353 = 686515) B686515
theorem B456619 : Blo 405769 456619 := bstep (se 1 (by rfl) ⟨342464, by rfl⟩ : syracuseStep 456619 = 684929) B684929
theorem B2062259 : Blo 405769 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B915443 : Blo 405769 915443 := bstep (se 1 (by rfl) ⟨686582, by rfl⟩ : syracuseStep 915443 = 1373165) B1373165
theorem B456727 : Blo 405769 456727 := bstep (se 1 (by rfl) ⟨342545, by rfl⟩ : syracuseStep 456727 = 685091) B685091
theorem B915479 : Blo 405769 915479 := bstep (se 1 (by rfl) ⟨686609, by rfl⟩ : syracuseStep 915479 = 1373219) B1373219
theorem B981067 : Blo 405769 981067 := bstep (se 1 (by rfl) ⟨735800, by rfl⟩ : syracuseStep 981067 = 1471601) B1471601
theorem B489611 : Blo 405769 489611 := bstep (se 1 (by rfl) ⟨367208, by rfl⟩ : syracuseStep 489611 = 734417) B734417
theorem B456907 : Blo 405769 456907 := bstep (se 1 (by rfl) ⟨342680, by rfl⟩ : syracuseStep 456907 = 685361) B685361
theorem B915659 : Blo 405769 915659 := bstep (se 1 (by rfl) ⟨686744, by rfl⟩ : syracuseStep 915659 = 1373489) B1373489
theorem B915713 : Blo 405769 915713 := bstep (se 2 (by rfl) ⟨343392, by rfl⟩ : syracuseStep 915713 = 686785) B686785
theorem B1374515 : Blo 405769 1374515 := bstep (se 1 (by rfl) ⟨1030886, by rfl⟩ : syracuseStep 1374515 = 2061773) B2061773
theorem B457015 : Blo 405769 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B915929 : Blo 405769 915929 := bstep (se 2 (by rfl) ⟨343473, by rfl⟩ : syracuseStep 915929 = 686947) B686947
theorem B457195 : Blo 405769 457195 := bstep (se 1 (by rfl) ⟨342896, by rfl⟩ : syracuseStep 457195 = 685793) B685793
theorem B686603 : Blo 405769 686603 := bstep (se 1 (by rfl) ⟨514952, by rfl⟩ : syracuseStep 686603 = 1029905) B1029905
theorem B916019 : Blo 405769 916019 := bstep (se 1 (by rfl) ⟨687014, by rfl⟩ : syracuseStep 916019 = 1374029) B1374029
theorem B1374785 : Blo 405769 1374785 := bstep (se 2 (by rfl) ⟨515544, by rfl⟩ : syracuseStep 1374785 = 1031089) B1031089
theorem B5241419 : Blo 405769 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B457303 : Blo 405769 457303 := bstep (se 1 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 457303 = 685955) B685955
theorem B916055 : Blo 405769 916055 := bstep (se 1 (by rfl) ⟨687041, by rfl⟩ : syracuseStep 916055 = 1374083) B1374083
theorem B686731 : Blo 405769 686731 := bstep (se 1 (by rfl) ⟨515048, by rfl⟩ : syracuseStep 686731 = 1030097) B1030097
theorem B981683 : Blo 405769 981683 := bstep (se 1 (by rfl) ⟨736262, by rfl⟩ : syracuseStep 981683 = 1472525) B1472525
theorem B457483 : Blo 405769 457483 := bstep (se 1 (by rfl) ⟨343112, by rfl⟩ : syracuseStep 457483 = 686225) B686225
theorem B916235 : Blo 405769 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B686873 : Blo 405769 686873 := bstep (se 2 (by rfl) ⟨257577, by rfl⟩ : syracuseStep 686873 = 515155) B515155
theorem B916289 : Blo 405769 916289 := bstep (se 2 (by rfl) ⟨343608, by rfl⟩ : syracuseStep 916289 = 687217) B687217
theorem B457591 : Blo 405769 457591 := bstep (se 1 (by rfl) ⟨343193, by rfl⟩ : syracuseStep 457591 = 686387) B686387
theorem B687001 : Blo 405769 687001 := bstep (se 2 (by rfl) ⟨257625, by rfl⟩ : syracuseStep 687001 = 515251) B515251
theorem B1244107 : Blo 405769 1244107 := bstep (se 1 (by rfl) ⟨933080, by rfl⟩ : syracuseStep 1244107 = 1866161) B1866161
theorem B916505 : Blo 405769 916505 := bstep (se 2 (by rfl) ⟨343689, by rfl⟩ : syracuseStep 916505 = 687379) B687379
theorem B457771 : Blo 405769 457771 := bstep (se 1 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 457771 = 686657) B686657
theorem B1375325 : Blo 405769 1375325 := bstep (se 3 (by rfl) ⟨257873, by rfl⟩ : syracuseStep 1375325 = 515747) B515747
theorem B916595 : Blo 405769 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B457879 : Blo 405769 457879 := bstep (se 1 (by rfl) ⟨343409, by rfl⟩ : syracuseStep 457879 = 686819) B686819
theorem B916631 : Blo 405769 916631 := bstep (se 1 (by rfl) ⟨687473, by rfl⟩ : syracuseStep 916631 = 1374947) B1374947
theorem B458059 : Blo 405769 458059 := bstep (se 1 (by rfl) ⟨343544, by rfl⟩ : syracuseStep 458059 = 687089) B687089
theorem B916811 : Blo 405769 916811 := bstep (se 1 (by rfl) ⟨687608, by rfl⟩ : syracuseStep 916811 = 1375217) B1375217
theorem B916865 : Blo 405769 916865 := bstep (se 2 (by rfl) ⟨343824, by rfl⟩ : syracuseStep 916865 = 687649) B687649
theorem B458167 : Blo 405769 458167 := bstep (se 1 (by rfl) ⟨343625, by rfl⟩ : syracuseStep 458167 = 687251) B687251
theorem B687575 : Blo 405769 687575 := bstep (se 1 (by rfl) ⟨515681, by rfl⟩ : syracuseStep 687575 = 1031363) B1031363
theorem B687703 : Blo 405769 687703 := bstep (se 1 (by rfl) ⟨515777, by rfl⟩ : syracuseStep 687703 = 1031555) B1031555
theorem B917081 : Blo 405769 917081 := bstep (se 2 (by rfl) ⟨343905, by rfl⟩ : syracuseStep 917081 = 687811) B687811
theorem B458347 : Blo 405769 458347 := bstep (se 1 (by rfl) ⟨343760, by rfl⟩ : syracuseStep 458347 = 687521) B687521
theorem B917171 : Blo 405769 917171 := bstep (se 1 (by rfl) ⟨687878, by rfl⟩ : syracuseStep 917171 = 1375757) B1375757
theorem B458455 : Blo 405769 458455 := bstep (se 1 (by rfl) ⟨343841, by rfl⟩ : syracuseStep 458455 = 687683) B687683
theorem B917207 : Blo 405769 917207 := bstep (se 1 (by rfl) ⟨687905, by rfl⟩ : syracuseStep 917207 = 1375811) B1375811
theorem B1179443 : Blo 405769 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B2064203 : Blo 405769 2064203 := bstep (se 1 (by rfl) ⟨1548152, by rfl⟩ : syracuseStep 2064203 = 3096305) B3096305
theorem B458635 : Blo 405769 458635 := bstep (se 1 (by rfl) ⟨343976, by rfl⟩ : syracuseStep 458635 = 687953) B687953
theorem B917387 : Blo 405769 917387 := bstep (se 1 (by rfl) ⟨688040, by rfl⟩ : syracuseStep 917387 = 1376081) B1376081
theorem B1736599 : Blo 405769 1736599 := bstep (se 1 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 1736599 = 2604899) B2604899
theorem B1474483 : Blo 405769 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B917441 : Blo 405769 917441 := bstep (se 2 (by rfl) ⟨344040, by rfl⟩ : syracuseStep 917441 = 688081) B688081
theorem B1146923 : Blo 405769 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B917639 : Blo 405769 917639 := bstep (se 1 (by rfl) ⟨688229, by rfl⟩ : syracuseStep 917639 = 1376459) B1376459
theorem B458887 : Blo 405769 458887 := bstep (se 1 (by rfl) ⟨344165, by rfl⟩ : syracuseStep 458887 = 688331) B688331
theorem B1376513 : Blo 405769 1376513 := bstep (se 2 (by rfl) ⟨516192, by rfl⟩ : syracuseStep 1376513 = 1032385) B1032385
theorem B524551 : Blo 405769 524551 := bstep (se 1 (by rfl) ⟨393413, by rfl⟩ : syracuseStep 524551 = 786827) B786827
theorem B917819 : Blo 405769 917819 := bstep (se 1 (by rfl) ⟨688364, by rfl⟩ : syracuseStep 917819 = 1376729) B1376729
theorem B459067 : Blo 405769 459067 := bstep (se 1 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 459067 = 688601) B688601
theorem B917945 : Blo 405769 917945 := bstep (se 2 (by rfl) ⟨344229, by rfl⟩ : syracuseStep 917945 = 688459) B688459
theorem B983497 : Blo 405769 983497 := bstep (se 2 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 983497 = 737623) B737623
theorem B688655 : Blo 405769 688655 := bstep (se 1 (by rfl) ⟨516491, by rfl⟩ : syracuseStep 688655 = 1032983) B1032983
theorem B4194917 : Blo 405769 4194917 := bstep (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) B786547
theorem B1540727 : Blo 405769 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B4391617 : Blo 405769 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B2622145 : Blo 405769 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B918287 : Blo 405769 918287 := bstep (se 1 (by rfl) ⟨688715, by rfl⟩ : syracuseStep 918287 = 1377431) B1377431
theorem B459535 : Blo 405769 459535 := bstep (se 1 (by rfl) ⟨344651, by rfl⟩ : syracuseStep 459535 = 689303) B689303
theorem B918305 : Blo 405769 918305 := bstep (se 2 (by rfl) ⟨344364, by rfl⟩ : syracuseStep 918305 = 688729) B688729
theorem B3900311 : Blo 405769 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B2065337 : Blo 405769 2065337 := bstep (se 2 (by rfl) ⟨774501, by rfl⟩ : syracuseStep 2065337 = 1549003) B1549003
theorem B1377323 : Blo 405769 1377323 := bstep (se 1 (by rfl) ⟨1032992, by rfl⟩ : syracuseStep 1377323 = 2065985) B2065985
theorem B689195 : Blo 405769 689195 := bstep (se 1 (by rfl) ⟨516896, by rfl⟩ : syracuseStep 689195 = 1033793) B1033793
theorem B918647 : Blo 405769 918647 := bstep (se 1 (by rfl) ⟨688985, by rfl⟩ : syracuseStep 918647 = 1377971) B1377971
theorem B460039 : Blo 405769 460039 := bstep (se 1 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 460039 = 690059) B690059
theorem B918827 : Blo 405769 918827 := bstep (se 1 (by rfl) ⟨689120, by rfl⟩ : syracuseStep 918827 = 1378241) B1378241
theorem B12387761 : Blo 405769 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B689593 : Blo 405769 689593 := bstep (se 2 (by rfl) ⟨258597, by rfl⟩ : syracuseStep 689593 = 517195) B517195
theorem B787897 : Blo 405769 787897 := bstep (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) B590923
theorem B460219 : Blo 405769 460219 := bstep (se 1 (by rfl) ⟨345164, by rfl⟩ : syracuseStep 460219 = 690329) B690329
theorem B1541699 : Blo 405769 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B788087 : Blo 405769 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B1476215 : Blo 405769 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B919187 : Blo 405769 919187 := bstep (se 1 (by rfl) ⟨689390, by rfl⟩ : syracuseStep 919187 = 1378781) B1378781
theorem B8849047 : Blo 405769 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B919241 : Blo 405769 919241 := bstep (se 2 (by rfl) ⟨344715, by rfl⟩ : syracuseStep 919241 = 689431) B689431
theorem B2328335 : Blo 405769 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B1738529 : Blo 405769 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B35915633 : Blo 405769 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B460687 : Blo 405769 460687 := bstep (se 1 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 460687 = 691031) B691031
theorem B559033 : Blo 405769 559033 := bstep (se 2 (by rfl) ⟨209637, by rfl⟩ : syracuseStep 559033 = 419275) B419275
theorem B2328587 : Blo 405769 2328587 := bstep (se 1 (by rfl) ⟨1746440, by rfl⟩ : syracuseStep 2328587 = 3492881) B3492881
theorem B7440407 : Blo 405769 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B1738871 : Blo 405769 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B690295 : Blo 405769 690295 := bstep (se 1 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 690295 = 1035443) B1035443
theorem B2787529 : Blo 405769 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B2066633 : Blo 405769 2066633 := bstep (se 2 (by rfl) ⟨774987, by rfl⟩ : syracuseStep 2066633 = 1549975) B1549975
theorem B4655393 : Blo 405769 4655393 := bstep (se 2 (by rfl) ⟨1745772, by rfl⟩ : syracuseStep 4655393 = 3491545) B3491545
theorem B1378619 : Blo 405769 1378619 := bstep (se 1 (by rfl) ⟨1033964, by rfl⟩ : syracuseStep 1378619 = 2067929) B2067929
theorem B690491 : Blo 405769 690491 := bstep (se 1 (by rfl) ⟨517868, by rfl⟩ : syracuseStep 690491 = 1035737) B1035737
theorem B919943 : Blo 405769 919943 := bstep (se 1 (by rfl) ⟨689957, by rfl⟩ : syracuseStep 919943 = 1379915) B1379915
theorem B559561 : Blo 405769 559561 := bstep (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) B419671
theorem B3770833 : Blo 405769 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B1542685 : Blo 405769 1542685 := bstep (se 3 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 1542685 = 578507) B578507
theorem B920123 : Blo 405769 920123 := bstep (se 1 (by rfl) ⟨690092, by rfl⟩ : syracuseStep 920123 = 1380185) B1380185
theorem B3181123 : Blo 405769 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B13208183 : Blo 405769 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B920249 : Blo 405769 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B690889 : Blo 405769 690889 := bstep (se 2 (by rfl) ⟨259083, by rfl⟩ : syracuseStep 690889 = 518167) B518167
theorem B1379105 : Blo 405769 1379105 := bstep (se 2 (by rfl) ⟨517164, by rfl⟩ : syracuseStep 1379105 = 1034329) B1034329
theorem B920591 : Blo 405769 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B920609 : Blo 405769 920609 := bstep (se 2 (by rfl) ⟨345228, by rfl⟩ : syracuseStep 920609 = 690457) B690457
theorem B2329793 : Blo 405769 2329793 := bstep (se 2 (by rfl) ⟨873672, by rfl⟩ : syracuseStep 2329793 = 1747345) B1747345
theorem B1379699 : Blo 405769 1379699 := bstep (se 1 (by rfl) ⟨1034774, by rfl⟩ : syracuseStep 1379699 = 2069549) B2069549
theorem B920951 : Blo 405769 920951 := bstep (se 1 (by rfl) ⟨690713, by rfl⟩ : syracuseStep 920951 = 1381427) B1381427
theorem B921131 : Blo 405769 921131 := bstep (se 1 (by rfl) ⟨690848, by rfl⟩ : syracuseStep 921131 = 1381697) B1381697
theorem B921491 : Blo 405769 921491 := bstep (se 1 (by rfl) ⟨691118, by rfl⟩ : syracuseStep 921491 = 1382237) B1382237
theorem B3903385 : Blo 405769 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B921545 : Blo 405769 921545 := bstep (se 2 (by rfl) ⟨345579, by rfl⟩ : syracuseStep 921545 = 691159) B691159
theorem B4624775 : Blo 405769 4624775 := bstep (se 1 (by rfl) ⟨3468581, by rfl⟩ : syracuseStep 4624775 = 6937163) B6937163
theorem B1806967 : Blo 405769 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B4690649 : Blo 405769 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B824249 : Blo 405769 824249 := bstep (se 2 (by rfl) ⟨309093, by rfl⟩ : syracuseStep 824249 = 618187) B618187
theorem B4658309 : Blo 405769 4658309 := bstep (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) B873433
theorem B464059 : Blo 405769 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B1545587 : Blo 405769 1545587 := bstep (se 1 (by rfl) ⟨1159190, by rfl⟩ : syracuseStep 1545587 = 2318381) B2318381
theorem B7870283 : Blo 405769 7870283 := bstep (se 1 (by rfl) ⟨5902712, by rfl⟩ : syracuseStep 7870283 = 11805425) B11805425
theorem B1382291 : Blo 405769 1382291 := bstep (se 1 (by rfl) ⟨1036718, by rfl⟩ : syracuseStep 1382291 = 2073437) B2073437
theorem B2332961 : Blo 405769 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B4397975 : Blo 405769 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B990323 : Blo 405769 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B695431 : Blo 405769 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B1547819 : Blo 405769 1547819 := bstep (se 1 (by rfl) ⟨1160864, by rfl⟩ : syracuseStep 1547819 = 2321729) B2321729
theorem B4169393 : Blo 405769 4169393 := bstep (se 2 (by rfl) ⟨1563522, by rfl⟩ : syracuseStep 4169393 = 3127045) B3127045
theorem B597775 : Blo 405769 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B2072465 : Blo 405769 2072465 := bstep (se 2 (by rfl) ⟨777174, by rfl⟩ : syracuseStep 2072465 = 1554349) B1554349
theorem B467215 : Blo 405769 467215 := bstep (se 1 (by rfl) ⟨350411, by rfl⟩ : syracuseStep 467215 = 700823) B700823
theorem B1122707 : Blo 405769 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B1647001 : Blo 405769 1647001 := bstep (se 2 (by rfl) ⟨617625, by rfl⟩ : syracuseStep 1647001 = 1235251) B1235251
theorem B1155671 : Blo 405769 1155671 := bstep (se 1 (by rfl) ⟨866753, by rfl⟩ : syracuseStep 1155671 = 1733507) B1733507
theorem B3089015 : Blo 405769 3089015 := bstep (se 1 (by rfl) ⟨2316761, by rfl⟩ : syracuseStep 3089015 = 4633523) B4633523
theorem B1647683 : Blo 405769 1647683 := bstep (se 1 (by rfl) ⟨1235762, by rfl⟩ : syracuseStep 1647683 = 2471525) B2471525
theorem B3482797 : Blo 405769 3482797 := bstep (se 3 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 3482797 = 1306049) B1306049
theorem B3089987 : Blo 405769 3089987 := bstep (se 1 (by rfl) ⟨2317490, by rfl⟩ : syracuseStep 3089987 = 4634981) B4634981
theorem B26388341 : Blo 405769 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B927607 : Blo 405769 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B731539 : Blo 405769 731539 := bstep (se 1 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 731539 = 1097309) B1097309
theorem B1157561 : Blo 405769 1157561 := bstep (se 2 (by rfl) ⟨434085, by rfl⟩ : syracuseStep 1157561 = 868171) B868171
theorem B1551251 : Blo 405769 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B437383 : Blo 405769 437383 := bstep (se 1 (by rfl) ⟨328037, by rfl⟩ : syracuseStep 437383 = 656075) B656075
theorem B1027343 : Blo 405769 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B1027475 : Blo 405769 1027475 := bstep (se 1 (by rfl) ⟨770606, by rfl⟩ : syracuseStep 1027475 = 1541213) B1541213
theorem B634895 : Blo 405769 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B1159201 : Blo 405769 1159201 := bstep (se 2 (by rfl) ⟨434700, by rfl⟩ : syracuseStep 1159201 = 869401) B869401
theorem B1749053 : Blo 405769 1749053 := bstep (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) B655895
theorem B405775 : Blo 405769 405775 := bstep (se 1 (by rfl) ⟨304331, by rfl⟩ : syracuseStep 405775 = 608663) B608663
theorem B405819 : Blo 405769 405819 := bstep (se 1 (by rfl) ⟨304364, by rfl⟩ : syracuseStep 405819 = 608729) B608729
theorem B405895 : Blo 405769 405895 := bstep (se 1 (by rfl) ⟨304421, by rfl⟩ : syracuseStep 405895 = 608843) B608843
theorem B3715463 : Blo 405769 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B405903 : Blo 405769 405903 := bstep (se 1 (by rfl) ⟨304427, by rfl⟩ : syracuseStep 405903 = 608855) B608855
theorem B1388947 : Blo 405769 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B3322259 : Blo 405769 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B405947 : Blo 405769 405947 := bstep (se 1 (by rfl) ⟨304460, by rfl⟩ : syracuseStep 405947 = 608921) B608921
theorem B1028609 : Blo 405769 1028609 := bstep (se 2 (by rfl) ⟨385728, by rfl⟩ : syracuseStep 1028609 = 771457) B771457
theorem B406023 : Blo 405769 406023 := bstep (se 1 (by rfl) ⟨304517, by rfl⟩ : syracuseStep 406023 = 609035) B609035
theorem B406031 : Blo 405769 406031 := bstep (se 1 (by rfl) ⟨304523, by rfl⟩ : syracuseStep 406031 = 609047) B609047
theorem B406075 : Blo 405769 406075 := bstep (se 1 (by rfl) ⟨304556, by rfl⟩ : syracuseStep 406075 = 609113) B609113
theorem B406151 : Blo 405769 406151 := bstep (se 1 (by rfl) ⟨304613, by rfl⟩ : syracuseStep 406151 = 609227) B609227
theorem B406159 : Blo 405769 406159 := bstep (se 1 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 406159 = 609239) B609239
theorem B406203 : Blo 405769 406203 := bstep (se 1 (by rfl) ⟨304652, by rfl⟩ : syracuseStep 406203 = 609305) B609305
theorem B406279 : Blo 405769 406279 := bstep (se 1 (by rfl) ⟨304709, by rfl⟩ : syracuseStep 406279 = 609419) B609419
theorem B406287 : Blo 405769 406287 := bstep (se 1 (by rfl) ⟨304715, by rfl⟩ : syracuseStep 406287 = 609431) B609431
theorem B406331 : Blo 405769 406331 := bstep (se 1 (by rfl) ⟨304748, by rfl⟩ : syracuseStep 406331 = 609497) B609497
theorem B1028983 : Blo 405769 1028983 := bstep (se 1 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 1028983 = 1543475) B1543475
theorem B406407 : Blo 405769 406407 := bstep (se 1 (by rfl) ⟨304805, by rfl⟩ : syracuseStep 406407 = 609611) B609611
theorem B406415 : Blo 405769 406415 := bstep (se 1 (by rfl) ⟨304811, by rfl⟩ : syracuseStep 406415 = 609623) B609623
theorem B406459 : Blo 405769 406459 := bstep (se 1 (by rfl) ⟨304844, by rfl⟩ : syracuseStep 406459 = 609689) B609689
theorem B406535 : Blo 405769 406535 := bstep (se 1 (by rfl) ⟨304901, by rfl⟩ : syracuseStep 406535 = 609803) B609803
theorem B406543 : Blo 405769 406543 := bstep (se 1 (by rfl) ⟨304907, by rfl⟩ : syracuseStep 406543 = 609815) B609815
theorem B1750045 : Blo 405769 1750045 := bstep (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) B656267
theorem B406587 : Blo 405769 406587 := bstep (se 1 (by rfl) ⟨304940, by rfl⟩ : syracuseStep 406587 = 609881) B609881
theorem B406663 : Blo 405769 406663 := bstep (se 1 (by rfl) ⟨304997, by rfl⟩ : syracuseStep 406663 = 609995) B609995
theorem B406671 : Blo 405769 406671 := bstep (se 1 (by rfl) ⟨305003, by rfl⟩ : syracuseStep 406671 = 610007) B610007
theorem B406715 : Blo 405769 406715 := bstep (se 1 (by rfl) ⟨305036, by rfl⟩ : syracuseStep 406715 = 610073) B610073
theorem B406791 : Blo 405769 406791 := bstep (se 1 (by rfl) ⟨305093, by rfl⟩ : syracuseStep 406791 = 610187) B610187
theorem B406799 : Blo 405769 406799 := bstep (se 1 (by rfl) ⟨305099, by rfl⟩ : syracuseStep 406799 = 610199) B610199
theorem B1160477 : Blo 405769 1160477 := bstep (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) B435179
theorem B1029419 : Blo 405769 1029419 := bstep (se 1 (by rfl) ⟨772064, by rfl⟩ : syracuseStep 1029419 = 1544129) B1544129
theorem B406843 : Blo 405769 406843 := bstep (se 1 (by rfl) ⟨305132, by rfl⟩ : syracuseStep 406843 = 610265) B610265
theorem B406919 : Blo 405769 406919 := bstep (se 1 (by rfl) ⟨305189, by rfl⟩ : syracuseStep 406919 = 610379) B610379
theorem B406927 : Blo 405769 406927 := bstep (se 1 (by rfl) ⟨305195, by rfl⟩ : syracuseStep 406927 = 610391) B610391
theorem B1553849 : Blo 405769 1553849 := bstep (se 2 (by rfl) ⟨582693, by rfl⟩ : syracuseStep 1553849 = 1165387) B1165387
theorem B406971 : Blo 405769 406971 := bstep (se 1 (by rfl) ⟨305228, by rfl⟩ : syracuseStep 406971 = 610457) B610457
theorem B1160705 : Blo 405769 1160705 := bstep (se 2 (by rfl) ⟨435264, by rfl⟩ : syracuseStep 1160705 = 870529) B870529
theorem B407047 : Blo 405769 407047 := bstep (se 1 (by rfl) ⟨305285, by rfl⟩ : syracuseStep 407047 = 610571) B610571
theorem B407055 : Blo 405769 407055 := bstep (se 1 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 407055 = 610583) B610583
theorem B407099 : Blo 405769 407099 := bstep (se 1 (by rfl) ⟨305324, by rfl⟩ : syracuseStep 407099 = 610649) B610649
theorem B407175 : Blo 405769 407175 := bstep (se 1 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 407175 = 610763) B610763
theorem B407183 : Blo 405769 407183 := bstep (se 1 (by rfl) ⟨305387, by rfl⟩ : syracuseStep 407183 = 610775) B610775
theorem B4667057 : Blo 405769 4667057 := bstep (se 2 (by rfl) ⟨1750146, by rfl⟩ : syracuseStep 4667057 = 3500293) B3500293
theorem B407227 : Blo 405769 407227 := bstep (se 1 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 407227 = 610841) B610841
theorem B407303 : Blo 405769 407303 := bstep (se 1 (by rfl) ⟨305477, by rfl⟩ : syracuseStep 407303 = 610955) B610955
theorem B407311 : Blo 405769 407311 := bstep (se 1 (by rfl) ⟨305483, by rfl⟩ : syracuseStep 407311 = 610967) B610967
theorem B407355 : Blo 405769 407355 := bstep (se 1 (by rfl) ⟨305516, by rfl⟩ : syracuseStep 407355 = 611033) B611033
theorem B1161047 : Blo 405769 1161047 := bstep (se 1 (by rfl) ⟨870785, by rfl⟩ : syracuseStep 1161047 = 1741571) B1741571
theorem B3094361 : Blo 405769 3094361 := bstep (se 2 (by rfl) ⟨1160385, by rfl⟩ : syracuseStep 3094361 = 2320771) B2320771
theorem B407431 : Blo 405769 407431 := bstep (se 1 (by rfl) ⟨305573, by rfl⟩ : syracuseStep 407431 = 611147) B611147
theorem B407439 : Blo 405769 407439 := bstep (se 1 (by rfl) ⟨305579, by rfl⟩ : syracuseStep 407439 = 611159) B611159
theorem B931769 : Blo 405769 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B407483 : Blo 405769 407483 := bstep (se 1 (by rfl) ⟨305612, by rfl⟩ : syracuseStep 407483 = 611225) B611225
theorem B1161161 : Blo 405769 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B407559 : Blo 405769 407559 := bstep (se 1 (by rfl) ⟨305669, by rfl⟩ : syracuseStep 407559 = 611339) B611339
theorem B407567 : Blo 405769 407567 := bstep (se 1 (by rfl) ⟨305675, by rfl⟩ : syracuseStep 407567 = 611351) B611351
theorem B407611 : Blo 405769 407611 := bstep (se 1 (by rfl) ⟨305708, by rfl⟩ : syracuseStep 407611 = 611417) B611417
theorem B1030259 : Blo 405769 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B1030279 : Blo 405769 1030279 := bstep (se 1 (by rfl) ⟨772709, by rfl⟩ : syracuseStep 1030279 = 1545419) B1545419
theorem B407687 : Blo 405769 407687 := bstep (se 1 (by rfl) ⟨305765, by rfl⟩ : syracuseStep 407687 = 611531) B611531
theorem B407695 : Blo 405769 407695 := bstep (se 1 (by rfl) ⟨305771, by rfl⟩ : syracuseStep 407695 = 611543) B611543
theorem B407739 : Blo 405769 407739 := bstep (se 1 (by rfl) ⟨305804, by rfl⟩ : syracuseStep 407739 = 611609) B611609
theorem B407815 : Blo 405769 407815 := bstep (se 1 (by rfl) ⟨305861, by rfl⟩ : syracuseStep 407815 = 611723) B611723
theorem B407823 : Blo 405769 407823 := bstep (se 1 (by rfl) ⟨305867, by rfl⟩ : syracuseStep 407823 = 611735) B611735
theorem B5028155 : Blo 405769 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B407867 : Blo 405769 407867 := bstep (se 1 (by rfl) ⟨305900, by rfl⟩ : syracuseStep 407867 = 611801) B611801
theorem B407943 : Blo 405769 407943 := bstep (se 1 (by rfl) ⟨305957, by rfl⟩ : syracuseStep 407943 = 611915) B611915
theorem B407951 : Blo 405769 407951 := bstep (se 1 (by rfl) ⟨305963, by rfl⟩ : syracuseStep 407951 = 611927) B611927
theorem B1554835 : Blo 405769 1554835 := bstep (se 1 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 1554835 = 2332253) B2332253
theorem B1030553 : Blo 405769 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B407995 : Blo 405769 407995 := bstep (se 1 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 407995 = 611993) B611993
theorem B408071 : Blo 405769 408071 := bstep (se 1 (by rfl) ⟨306053, by rfl⟩ : syracuseStep 408071 = 612107) B612107
theorem B408079 : Blo 405769 408079 := bstep (se 1 (by rfl) ⟨306059, by rfl⟩ : syracuseStep 408079 = 612119) B612119
theorem B1030715 : Blo 405769 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B408123 : Blo 405769 408123 := bstep (se 1 (by rfl) ⟨306092, by rfl⟩ : syracuseStep 408123 = 612185) B612185
theorem B408199 : Blo 405769 408199 := bstep (se 1 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 408199 = 612299) B612299
theorem B408207 : Blo 405769 408207 := bstep (se 1 (by rfl) ⟨306155, by rfl⟩ : syracuseStep 408207 = 612311) B612311
theorem B408251 : Blo 405769 408251 := bstep (se 1 (by rfl) ⟨306188, by rfl⟩ : syracuseStep 408251 = 612377) B612377
theorem B408327 : Blo 405769 408327 := bstep (se 1 (by rfl) ⟨306245, by rfl⟩ : syracuseStep 408327 = 612491) B612491
theorem B1030927 : Blo 405769 1030927 := bstep (se 1 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 1030927 = 1546391) B1546391
theorem B408335 : Blo 405769 408335 := bstep (se 1 (by rfl) ⟨306251, by rfl⟩ : syracuseStep 408335 = 612503) B612503
theorem B3095333 : Blo 405769 3095333 := bstep (se 4 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 3095333 = 580375) B580375
theorem B408379 : Blo 405769 408379 := bstep (se 1 (by rfl) ⟨306284, by rfl⟩ : syracuseStep 408379 = 612569) B612569
theorem B408455 : Blo 405769 408455 := bstep (se 1 (by rfl) ⟨306341, by rfl⟩ : syracuseStep 408455 = 612683) B612683
theorem B408463 : Blo 405769 408463 := bstep (se 1 (by rfl) ⟨306347, by rfl⟩ : syracuseStep 408463 = 612695) B612695
theorem B408507 : Blo 405769 408507 := bstep (se 1 (by rfl) ⟨306380, by rfl⟩ : syracuseStep 408507 = 612761) B612761
theorem B408583 : Blo 405769 408583 := bstep (se 1 (by rfl) ⟨306437, by rfl⟩ : syracuseStep 408583 = 612875) B612875
theorem B867343 : Blo 405769 867343 := bstep (se 1 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 867343 = 1301015) B1301015
theorem B408591 : Blo 405769 408591 := bstep (se 1 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 408591 = 612887) B612887
theorem B1031201 : Blo 405769 1031201 := bstep (se 2 (by rfl) ⟨386700, by rfl⟩ : syracuseStep 1031201 = 773401) B773401
theorem B408635 : Blo 405769 408635 := bstep (se 1 (by rfl) ⟨306476, by rfl⟩ : syracuseStep 408635 = 612953) B612953
theorem B8928317 : Blo 405769 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B408711 : Blo 405769 408711 := bstep (se 1 (by rfl) ⟨306533, by rfl⟩ : syracuseStep 408711 = 613067) B613067
theorem B408719 : Blo 405769 408719 := bstep (se 1 (by rfl) ⟨306539, by rfl⟩ : syracuseStep 408719 = 613079) B613079
theorem B408763 : Blo 405769 408763 := bstep (se 1 (by rfl) ⟨306572, by rfl⟩ : syracuseStep 408763 = 613145) B613145
theorem B408839 : Blo 405769 408839 := bstep (se 1 (by rfl) ⟨306629, by rfl⟩ : syracuseStep 408839 = 613259) B613259
theorem B408847 : Blo 405769 408847 := bstep (se 1 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 408847 = 613271) B613271
theorem B736571 : Blo 405769 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B408891 : Blo 405769 408891 := bstep (se 1 (by rfl) ⟨306668, by rfl⟩ : syracuseStep 408891 = 613337) B613337
theorem B408967 : Blo 405769 408967 := bstep (se 1 (by rfl) ⟨306725, by rfl⟩ : syracuseStep 408967 = 613451) B613451
theorem B408975 : Blo 405769 408975 := bstep (se 1 (by rfl) ⟨306731, by rfl⟩ : syracuseStep 408975 = 613463) B613463
theorem B409019 : Blo 405769 409019 := bstep (se 1 (by rfl) ⟨306764, by rfl⟩ : syracuseStep 409019 = 613529) B613529
theorem B409095 : Blo 405769 409095 := bstep (se 1 (by rfl) ⟨306821, by rfl⟩ : syracuseStep 409095 = 613643) B613643
theorem B409103 : Blo 405769 409103 := bstep (se 1 (by rfl) ⟨306827, by rfl⟩ : syracuseStep 409103 = 613655) B613655
theorem B409147 : Blo 405769 409147 := bstep (se 1 (by rfl) ⟨306860, by rfl⟩ : syracuseStep 409147 = 613721) B613721
theorem B409223 : Blo 405769 409223 := bstep (se 1 (by rfl) ⟨306917, by rfl⟩ : syracuseStep 409223 = 613835) B613835
theorem B409231 : Blo 405769 409231 := bstep (se 1 (by rfl) ⟨306923, by rfl⟩ : syracuseStep 409231 = 613847) B613847
theorem B1162937 : Blo 405769 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B605881 : Blo 405769 605881 := bstep (se 2 (by rfl) ⟨227205, by rfl⟩ : syracuseStep 605881 = 454411) B454411
theorem B409275 : Blo 405769 409275 := bstep (se 1 (by rfl) ⟨306956, by rfl⟩ : syracuseStep 409275 = 613913) B613913
theorem B409351 : Blo 405769 409351 := bstep (se 1 (by rfl) ⟨307013, by rfl⟩ : syracuseStep 409351 = 614027) B614027
theorem B409359 : Blo 405769 409359 := bstep (se 1 (by rfl) ⟨307019, by rfl⟩ : syracuseStep 409359 = 614039) B614039
theorem B409403 : Blo 405769 409403 := bstep (se 1 (by rfl) ⟨307052, by rfl⟩ : syracuseStep 409403 = 614105) B614105
theorem B409479 : Blo 405769 409479 := bstep (se 1 (by rfl) ⟨307109, by rfl⟩ : syracuseStep 409479 = 614219) B614219
theorem B409487 : Blo 405769 409487 := bstep (se 1 (by rfl) ⟨307115, by rfl⟩ : syracuseStep 409487 = 614231) B614231
theorem B409531 : Blo 405769 409531 := bstep (se 1 (by rfl) ⟨307148, by rfl⟩ : syracuseStep 409531 = 614297) B614297
theorem B409607 : Blo 405769 409607 := bstep (se 1 (by rfl) ⟨307205, by rfl⟩ : syracuseStep 409607 = 614411) B614411
theorem B1032203 : Blo 405769 1032203 := bstep (se 1 (by rfl) ⟨774152, by rfl⟩ : syracuseStep 1032203 = 1548305) B1548305
theorem B409615 : Blo 405769 409615 := bstep (se 1 (by rfl) ⟨307211, by rfl⟩ : syracuseStep 409615 = 614423) B614423
theorem B8503319 : Blo 405769 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B409659 : Blo 405769 409659 := bstep (se 1 (by rfl) ⟨307244, by rfl⟩ : syracuseStep 409659 = 614489) B614489
theorem B409735 : Blo 405769 409735 := bstep (se 1 (by rfl) ⟨307301, by rfl⟩ : syracuseStep 409735 = 614603) B614603
theorem B409743 : Blo 405769 409743 := bstep (se 1 (by rfl) ⟨307307, by rfl⟩ : syracuseStep 409743 = 614615) B614615
theorem B1098251 : Blo 405769 1098251 := bstep (se 1 (by rfl) ⟨823688, by rfl⟩ : syracuseStep 1098251 = 1647377) B1647377
theorem B5653111 : Blo 405769 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B1032851 : Blo 405769 1032851 := bstep (se 1 (by rfl) ⟨774638, by rfl⟩ : syracuseStep 1032851 = 1549277) B1549277
theorem B1163929 : Blo 405769 1163929 := bstep (se 2 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 1163929 = 872947) B872947
theorem B8372929 : Blo 405769 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B2212609 : Blo 405769 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B2212697 : Blo 405769 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B2802521 : Blo 405769 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B1196947 : Blo 405769 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1950617 : Blo 405769 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B2933657 : Blo 405769 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B1033145 : Blo 405769 1033145 := bstep (se 2 (by rfl) ⟨387429, by rfl⟩ : syracuseStep 1033145 = 774859) B774859
theorem B771115 : Blo 405769 771115 := bstep (se 1 (by rfl) ⟨578336, by rfl⟩ : syracuseStep 771115 = 1156673) B1156673
theorem B771191 : Blo 405769 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B4637897 : Blo 405769 4637897 := bstep (se 2 (by rfl) ⟨1739211, by rfl⟩ : syracuseStep 4637897 = 3478423) B3478423
theorem B1033843 : Blo 405769 1033843 := bstep (se 1 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 1033843 = 1550765) B1550765
theorem B1033985 : Blo 405769 1033985 := bstep (se 2 (by rfl) ⟨387744, by rfl⟩ : syracuseStep 1033985 = 775489) B775489
theorem B575623 : Blo 405769 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B1034441 : Blo 405769 1034441 := bstep (se 2 (by rfl) ⟨387915, by rfl⟩ : syracuseStep 1034441 = 775831) B775831
theorem B608699 : Blo 405769 608699 := bstep (se 1 (by rfl) ⟨456524, by rfl⟩ : syracuseStep 608699 = 913049) B913049
theorem B608759 : Blo 405769 608759 := bstep (se 1 (by rfl) ⟨456569, by rfl⟩ : syracuseStep 608759 = 913139) B913139
theorem B608783 : Blo 405769 608783 := bstep (se 1 (by rfl) ⟨456587, by rfl⟩ : syracuseStep 608783 = 913175) B913175
theorem B1165853 : Blo 405769 1165853 := bstep (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) B437195
theorem B1034795 : Blo 405769 1034795 := bstep (se 1 (by rfl) ⟨776096, by rfl⟩ : syracuseStep 1034795 = 1552193) B1552193
theorem B608825 : Blo 405769 608825 := bstep (se 2 (by rfl) ⟨228309, by rfl⟩ : syracuseStep 608825 = 456619) B456619
theorem B608903 : Blo 405769 608903 := bstep (se 1 (by rfl) ⟨456677, by rfl⟩ : syracuseStep 608903 = 913355) B913355
theorem B608939 : Blo 405769 608939 := bstep (se 1 (by rfl) ⟨456704, by rfl⟩ : syracuseStep 608939 = 913409) B913409
theorem B608969 : Blo 405769 608969 := bstep (se 2 (by rfl) ⟨228363, by rfl⟩ : syracuseStep 608969 = 456727) B456727
theorem B4410085 : Blo 405769 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B609083 : Blo 405769 609083 := bstep (se 1 (by rfl) ⟨456812, by rfl⟩ : syracuseStep 609083 = 913625) B913625
theorem B609143 : Blo 405769 609143 := bstep (se 1 (by rfl) ⟨456857, by rfl⟩ : syracuseStep 609143 = 913715) B913715
theorem B609167 : Blo 405769 609167 := bstep (se 1 (by rfl) ⟨456875, by rfl⟩ : syracuseStep 609167 = 913751) B913751
theorem B1952657 : Blo 405769 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B609209 : Blo 405769 609209 := bstep (se 2 (by rfl) ⟨228453, by rfl⟩ : syracuseStep 609209 = 456907) B456907
theorem B609287 : Blo 405769 609287 := bstep (se 1 (by rfl) ⟨456965, by rfl⟩ : syracuseStep 609287 = 913931) B913931
theorem B773135 : Blo 405769 773135 := bstep (se 1 (by rfl) ⟨579851, by rfl⟩ : syracuseStep 773135 = 1159703) B1159703
theorem B609323 : Blo 405769 609323 := bstep (se 1 (by rfl) ⟨456992, by rfl⟩ : syracuseStep 609323 = 913985) B913985
theorem B609353 : Blo 405769 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B609467 : Blo 405769 609467 := bstep (se 1 (by rfl) ⟨457100, by rfl⟩ : syracuseStep 609467 = 914201) B914201
theorem B1166537 : Blo 405769 1166537 := bstep (se 2 (by rfl) ⟨437451, by rfl⟩ : syracuseStep 1166537 = 874903) B874903
theorem B609527 : Blo 405769 609527 := bstep (se 1 (by rfl) ⟨457145, by rfl⟩ : syracuseStep 609527 = 914291) B914291
theorem B609551 : Blo 405769 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B609593 : Blo 405769 609593 := bstep (se 2 (by rfl) ⟨228597, by rfl⟩ : syracuseStep 609593 = 457195) B457195
theorem B609671 : Blo 405769 609671 := bstep (se 1 (by rfl) ⟨457253, by rfl⟩ : syracuseStep 609671 = 914507) B914507
theorem B609707 : Blo 405769 609707 := bstep (se 1 (by rfl) ⟨457280, by rfl⟩ : syracuseStep 609707 = 914561) B914561
theorem B609737 : Blo 405769 609737 := bstep (se 2 (by rfl) ⟨228651, by rfl⟩ : syracuseStep 609737 = 457303) B457303
theorem B1035787 : Blo 405769 1035787 := bstep (se 1 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 1035787 = 1553681) B1553681
theorem B609851 : Blo 405769 609851 := bstep (se 1 (by rfl) ⟨457388, by rfl⟩ : syracuseStep 609851 = 914777) B914777
theorem B609911 : Blo 405769 609911 := bstep (se 1 (by rfl) ⟨457433, by rfl⟩ : syracuseStep 609911 = 914867) B914867
theorem B609935 : Blo 405769 609935 := bstep (se 1 (by rfl) ⟨457451, by rfl⟩ : syracuseStep 609935 = 914903) B914903
theorem B1035929 : Blo 405769 1035929 := bstep (se 2 (by rfl) ⟨388473, by rfl⟩ : syracuseStep 1035929 = 776947) B776947
theorem B609977 : Blo 405769 609977 := bstep (se 2 (by rfl) ⟨228741, by rfl⟩ : syracuseStep 609977 = 457483) B457483
theorem B610055 : Blo 405769 610055 := bstep (se 1 (by rfl) ⟨457541, by rfl⟩ : syracuseStep 610055 = 915083) B915083
theorem B610091 : Blo 405769 610091 := bstep (se 1 (by rfl) ⟨457568, by rfl⟩ : syracuseStep 610091 = 915137) B915137
theorem B1036091 : Blo 405769 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B610121 : Blo 405769 610121 := bstep (se 2 (by rfl) ⟨228795, by rfl⟩ : syracuseStep 610121 = 457591) B457591
theorem B1101721 : Blo 405769 1101721 := bstep (se 2 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 1101721 = 826291) B826291
theorem B1658809 : Blo 405769 1658809 := bstep (se 2 (by rfl) ⟨622053, by rfl⟩ : syracuseStep 1658809 = 1244107) B1244107
theorem B610235 : Blo 405769 610235 := bstep (se 1 (by rfl) ⟨457676, by rfl⟩ : syracuseStep 610235 = 915353) B915353
theorem B610295 : Blo 405769 610295 := bstep (se 1 (by rfl) ⟨457721, by rfl⟩ : syracuseStep 610295 = 915443) B915443
theorem B610319 : Blo 405769 610319 := bstep (se 1 (by rfl) ⟨457739, by rfl⟩ : syracuseStep 610319 = 915479) B915479
theorem B4640813 : Blo 405769 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B610361 : Blo 405769 610361 := bstep (se 2 (by rfl) ⟨228885, by rfl⟩ : syracuseStep 610361 = 457771) B457771
theorem B610439 : Blo 405769 610439 := bstep (se 1 (by rfl) ⟨457829, by rfl⟩ : syracuseStep 610439 = 915659) B915659
theorem B1036435 : Blo 405769 1036435 := bstep (se 1 (by rfl) ⟨777326, by rfl⟩ : syracuseStep 1036435 = 1554653) B1554653
theorem B610475 : Blo 405769 610475 := bstep (se 1 (by rfl) ⟨457856, by rfl⟩ : syracuseStep 610475 = 915713) B915713
theorem B610505 : Blo 405769 610505 := bstep (se 2 (by rfl) ⟨228939, by rfl⟩ : syracuseStep 610505 = 457879) B457879
theorem B1036577 : Blo 405769 1036577 := bstep (se 2 (by rfl) ⟨388716, by rfl⟩ : syracuseStep 1036577 = 777433) B777433
theorem B610619 : Blo 405769 610619 := bstep (se 1 (by rfl) ⟨457964, by rfl⟩ : syracuseStep 610619 = 915929) B915929
theorem B610679 : Blo 405769 610679 := bstep (se 1 (by rfl) ⟨458009, by rfl⟩ : syracuseStep 610679 = 916019) B916019
theorem B3494279 : Blo 405769 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B610703 : Blo 405769 610703 := bstep (se 1 (by rfl) ⟨458027, by rfl⟩ : syracuseStep 610703 = 916055) B916055
theorem B610745 : Blo 405769 610745 := bstep (se 2 (by rfl) ⟨229029, by rfl⟩ : syracuseStep 610745 = 458059) B458059
theorem B1954307 : Blo 405769 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B610823 : Blo 405769 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B578063 : Blo 405769 578063 := bstep (se 1 (by rfl) ⟨433547, by rfl⟩ : syracuseStep 578063 = 867095) B867095
theorem B610859 : Blo 405769 610859 := bstep (se 1 (by rfl) ⟨458144, by rfl⟩ : syracuseStep 610859 = 916289) B916289
theorem B610889 : Blo 405769 610889 := bstep (se 2 (by rfl) ⟨229083, by rfl⟩ : syracuseStep 610889 = 458167) B458167
theorem B3723853 : Blo 405769 3723853 := bstep (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) B1396445
theorem B774775 : Blo 405769 774775 := bstep (se 1 (by rfl) ⟨581081, by rfl⟩ : syracuseStep 774775 = 1162163) B1162163
theorem B611003 : Blo 405769 611003 := bstep (se 1 (by rfl) ⟨458252, by rfl⟩ : syracuseStep 611003 = 916505) B916505
theorem B611063 : Blo 405769 611063 := bstep (se 1 (by rfl) ⟨458297, by rfl⟩ : syracuseStep 611063 = 916595) B916595
theorem B611087 : Blo 405769 611087 := bstep (se 1 (by rfl) ⟨458315, by rfl⟩ : syracuseStep 611087 = 916631) B916631
theorem B611129 : Blo 405769 611129 := bstep (se 2 (by rfl) ⟨229173, by rfl⟩ : syracuseStep 611129 = 458347) B458347
theorem B611207 : Blo 405769 611207 := bstep (se 1 (by rfl) ⟨458405, by rfl⟩ : syracuseStep 611207 = 916811) B916811
theorem B611243 : Blo 405769 611243 := bstep (se 1 (by rfl) ⟨458432, by rfl⟩ : syracuseStep 611243 = 916865) B916865
theorem B611273 : Blo 405769 611273 := bstep (se 2 (by rfl) ⟨229227, by rfl⟩ : syracuseStep 611273 = 458455) B458455
theorem B611387 : Blo 405769 611387 := bstep (se 1 (by rfl) ⟨458540, by rfl⟩ : syracuseStep 611387 = 917081) B917081
theorem B611447 : Blo 405769 611447 := bstep (se 1 (by rfl) ⟨458585, by rfl⟩ : syracuseStep 611447 = 917171) B917171
theorem B611471 : Blo 405769 611471 := bstep (se 1 (by rfl) ⟨458603, by rfl⟩ : syracuseStep 611471 = 917207) B917207
theorem B611513 : Blo 405769 611513 := bstep (se 2 (by rfl) ⟨229317, by rfl⟩ : syracuseStep 611513 = 458635) B458635
theorem B2315465 : Blo 405769 2315465 := bstep (se 2 (by rfl) ⟨868299, by rfl⟩ : syracuseStep 2315465 = 1736599) B1736599
theorem B611591 : Blo 405769 611591 := bstep (se 1 (by rfl) ⟨458693, by rfl⟩ : syracuseStep 611591 = 917387) B917387
theorem B611627 : Blo 405769 611627 := bstep (se 1 (by rfl) ⟨458720, by rfl⟩ : syracuseStep 611627 = 917441) B917441
theorem B611657 : Blo 405769 611657 := bstep (se 2 (by rfl) ⟨229371, by rfl⟩ : syracuseStep 611657 = 458743) B458743
theorem B3102137 : Blo 405769 3102137 := bstep (se 2 (by rfl) ⟨1163301, by rfl⟩ : syracuseStep 3102137 = 2326603) B2326603
theorem B611771 : Blo 405769 611771 := bstep (se 1 (by rfl) ⟨458828, by rfl⟩ : syracuseStep 611771 = 917657) B917657
theorem B873929 : Blo 405769 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B611831 : Blo 405769 611831 := bstep (se 1 (by rfl) ⟨458873, by rfl⟩ : syracuseStep 611831 = 917747) B917747
theorem B611855 : Blo 405769 611855 := bstep (se 1 (by rfl) ⟨458891, by rfl⟩ : syracuseStep 611855 = 917783) B917783
theorem B611897 : Blo 405769 611897 := bstep (se 2 (by rfl) ⟨229461, by rfl⟩ : syracuseStep 611897 = 458923) B458923
theorem B579145 : Blo 405769 579145 := bstep (se 2 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 579145 = 434359) B434359
theorem B611975 : Blo 405769 611975 := bstep (se 1 (by rfl) ⟨458981, by rfl⟩ : syracuseStep 611975 = 917963) B917963
theorem B612011 : Blo 405769 612011 := bstep (se 1 (by rfl) ⟨459008, by rfl⟩ : syracuseStep 612011 = 918017) B918017
theorem B579259 : Blo 405769 579259 := bstep (se 1 (by rfl) ⟨434444, by rfl⟩ : syracuseStep 579259 = 868889) B868889
theorem B612041 : Blo 405769 612041 := bstep (se 2 (by rfl) ⟨229515, by rfl⟩ : syracuseStep 612041 = 459031) B459031
theorem B612155 : Blo 405769 612155 := bstep (se 1 (by rfl) ⟨459116, by rfl⟩ : syracuseStep 612155 = 918233) B918233
theorem B612215 : Blo 405769 612215 := bstep (se 1 (by rfl) ⟨459161, by rfl⟩ : syracuseStep 612215 = 918323) B918323
theorem B612239 : Blo 405769 612239 := bstep (se 1 (by rfl) ⟨459179, by rfl⟩ : syracuseStep 612239 = 918359) B918359
theorem B612281 : Blo 405769 612281 := bstep (se 2 (by rfl) ⟨229605, by rfl⟩ : syracuseStep 612281 = 459211) B459211
theorem B612359 : Blo 405769 612359 := bstep (se 1 (by rfl) ⟨459269, by rfl⟩ : syracuseStep 612359 = 918539) B918539
theorem B612395 : Blo 405769 612395 := bstep (se 1 (by rfl) ⟨459296, by rfl⟩ : syracuseStep 612395 = 918593) B918593
theorem B612425 : Blo 405769 612425 := bstep (se 2 (by rfl) ⟨229659, by rfl⟩ : syracuseStep 612425 = 459319) B459319
theorem B514183 : Blo 405769 514183 := bstep (se 1 (by rfl) ⟨385637, by rfl⟩ : syracuseStep 514183 = 771275) B771275
theorem B2513069 : Blo 405769 2513069 := bstep (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) B942401
theorem B612539 : Blo 405769 612539 := bstep (se 1 (by rfl) ⟨459404, by rfl⟩ : syracuseStep 612539 = 918809) B918809
theorem B612599 : Blo 405769 612599 := bstep (se 1 (by rfl) ⟨459449, by rfl⟩ : syracuseStep 612599 = 918899) B918899
theorem B612623 : Blo 405769 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B612665 : Blo 405769 612665 := bstep (se 2 (by rfl) ⟨229749, by rfl⟩ : syracuseStep 612665 = 459499) B459499
theorem B776567 : Blo 405769 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B612743 : Blo 405769 612743 := bstep (se 1 (by rfl) ⟨459557, by rfl⟩ : syracuseStep 612743 = 919115) B919115
theorem B612779 : Blo 405769 612779 := bstep (se 1 (by rfl) ⟨459584, by rfl⟩ : syracuseStep 612779 = 919169) B919169
theorem B874937 : Blo 405769 874937 := bstep (se 2 (by rfl) ⟨328101, by rfl⟩ : syracuseStep 874937 = 656203) B656203
theorem B612809 : Blo 405769 612809 := bstep (se 2 (by rfl) ⟨229803, by rfl⟩ : syracuseStep 612809 = 459607) B459607
theorem B776719 : Blo 405769 776719 := bstep (se 1 (by rfl) ⟨582539, by rfl⟩ : syracuseStep 776719 = 1165079) B1165079
theorem B514603 : Blo 405769 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B612923 : Blo 405769 612923 := bstep (se 1 (by rfl) ⟨459692, by rfl⟩ : syracuseStep 612923 = 919385) B919385
theorem B612983 : Blo 405769 612983 := bstep (se 1 (by rfl) ⟨459737, by rfl⟩ : syracuseStep 612983 = 919475) B919475
theorem B613007 : Blo 405769 613007 := bstep (se 1 (by rfl) ⟨459755, by rfl⟩ : syracuseStep 613007 = 919511) B919511
theorem B613049 : Blo 405769 613049 := bstep (se 2 (by rfl) ⟨229893, by rfl⟩ : syracuseStep 613049 = 459787) B459787
theorem B613127 : Blo 405769 613127 := bstep (se 1 (by rfl) ⟨459845, by rfl⟩ : syracuseStep 613127 = 919691) B919691
theorem B514831 : Blo 405769 514831 := bstep (se 1 (by rfl) ⟨386123, by rfl⟩ : syracuseStep 514831 = 772247) B772247
theorem B1104683 : Blo 405769 1104683 := bstep (se 1 (by rfl) ⟨828512, by rfl⟩ : syracuseStep 1104683 = 1657025) B1657025
theorem B613163 : Blo 405769 613163 := bstep (se 1 (by rfl) ⟨459872, by rfl⟩ : syracuseStep 613163 = 919745) B919745
theorem B613193 : Blo 405769 613193 := bstep (se 2 (by rfl) ⟨229947, by rfl⟩ : syracuseStep 613193 = 459895) B459895
theorem B777107 : Blo 405769 777107 := bstep (se 1 (by rfl) ⟨582830, by rfl⟩ : syracuseStep 777107 = 1165661) B1165661
theorem B613307 : Blo 405769 613307 := bstep (se 1 (by rfl) ⟨459980, by rfl⟩ : syracuseStep 613307 = 919961) B919961
theorem B613367 : Blo 405769 613367 := bstep (se 1 (by rfl) ⟨460025, by rfl⟩ : syracuseStep 613367 = 920051) B920051
theorem B613391 : Blo 405769 613391 := bstep (se 1 (by rfl) ⟨460043, by rfl⟩ : syracuseStep 613391 = 920087) B920087
theorem B2317355 : Blo 405769 2317355 := bstep (se 1 (by rfl) ⟨1738016, by rfl⟩ : syracuseStep 2317355 = 3476033) B3476033
theorem B613433 : Blo 405769 613433 := bstep (se 2 (by rfl) ⟨230037, by rfl⟩ : syracuseStep 613433 = 460075) B460075
theorem B613511 : Blo 405769 613511 := bstep (se 1 (by rfl) ⟨460133, by rfl⟩ : syracuseStep 613511 = 920267) B920267
theorem B613547 : Blo 405769 613547 := bstep (se 1 (by rfl) ⟨460160, by rfl⟩ : syracuseStep 613547 = 920321) B920321
theorem B613577 : Blo 405769 613577 := bstep (se 2 (by rfl) ⟨230091, by rfl⟩ : syracuseStep 613577 = 460183) B460183
theorem B580871 : Blo 405769 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B1465615 : Blo 405769 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B613691 : Blo 405769 613691 := bstep (se 1 (by rfl) ⟨460268, by rfl⟩ : syracuseStep 613691 = 920537) B920537
theorem B1105267 : Blo 405769 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B613751 : Blo 405769 613751 := bstep (se 1 (by rfl) ⟨460313, by rfl⟩ : syracuseStep 613751 = 920627) B920627
theorem B613775 : Blo 405769 613775 := bstep (se 1 (by rfl) ⟨460331, by rfl⟩ : syracuseStep 613775 = 920663) B920663
theorem B613817 : Blo 405769 613817 := bstep (se 2 (by rfl) ⟨230181, by rfl⟩ : syracuseStep 613817 = 460363) B460363
theorem B515575 : Blo 405769 515575 := bstep (se 1 (by rfl) ⟨386681, by rfl⟩ : syracuseStep 515575 = 773363) B773363
theorem B613895 : Blo 405769 613895 := bstep (se 1 (by rfl) ⟨460421, by rfl⟩ : syracuseStep 613895 = 920843) B920843
theorem B613931 : Blo 405769 613931 := bstep (se 1 (by rfl) ⟨460448, by rfl⟩ : syracuseStep 613931 = 920897) B920897
theorem B1236541 : Blo 405769 1236541 := bstep (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) B463703
theorem B613961 : Blo 405769 613961 := bstep (se 2 (by rfl) ⟨230235, by rfl⟩ : syracuseStep 613961 = 460471) B460471
theorem B1007239 : Blo 405769 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B614075 : Blo 405769 614075 := bstep (se 1 (by rfl) ⟨460556, by rfl⟩ : syracuseStep 614075 = 921113) B921113
theorem B614135 : Blo 405769 614135 := bstep (se 1 (by rfl) ⟨460601, by rfl⟩ : syracuseStep 614135 = 921203) B921203
theorem B614159 : Blo 405769 614159 := bstep (se 1 (by rfl) ⟨460619, by rfl⟩ : syracuseStep 614159 = 921239) B921239
theorem B614201 : Blo 405769 614201 := bstep (se 2 (by rfl) ⟨230325, by rfl⟩ : syracuseStep 614201 = 460651) B460651
theorem B515899 : Blo 405769 515899 := bstep (se 1 (by rfl) ⟨386924, by rfl⟩ : syracuseStep 515899 = 773849) B773849
theorem B614279 : Blo 405769 614279 := bstep (se 1 (by rfl) ⟨460709, by rfl⟩ : syracuseStep 614279 = 921419) B921419
theorem B614315 : Blo 405769 614315 := bstep (se 1 (by rfl) ⟨460736, by rfl⟩ : syracuseStep 614315 = 921473) B921473
theorem B614345 : Blo 405769 614345 := bstep (se 2 (by rfl) ⟨230379, by rfl⟩ : syracuseStep 614345 = 460759) B460759
theorem B614459 : Blo 405769 614459 := bstep (se 1 (by rfl) ⟨460844, by rfl⟩ : syracuseStep 614459 = 921689) B921689
theorem B614519 : Blo 405769 614519 := bstep (se 1 (by rfl) ⟨460889, by rfl⟩ : syracuseStep 614519 = 921779) B921779
theorem B614543 : Blo 405769 614543 := bstep (se 1 (by rfl) ⟨460907, by rfl⟩ : syracuseStep 614543 = 921815) B921815
theorem B614585 : Blo 405769 614585 := bstep (se 2 (by rfl) ⟨230469, by rfl⟩ : syracuseStep 614585 = 460939) B460939
theorem B581833 : Blo 405769 581833 := bstep (se 2 (by rfl) ⟨218187, by rfl⟩ : syracuseStep 581833 = 436375) B436375
theorem B3825953 : Blo 405769 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B516395 : Blo 405769 516395 := bstep (se 1 (by rfl) ⟨387296, by rfl⟩ : syracuseStep 516395 = 774593) B774593
theorem B2318813 : Blo 405769 2318813 := bstep (se 3 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 2318813 = 869555) B869555
theorem B1466999 : Blo 405769 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B582329 : Blo 405769 582329 := bstep (se 2 (by rfl) ⟨218373, by rfl⟩ : syracuseStep 582329 = 436747) B436747
theorem B975617 : Blo 405769 975617 := bstep (se 2 (by rfl) ⟨365856, by rfl⟩ : syracuseStep 975617 = 731713) B731713
theorem B516871 : Blo 405769 516871 := bstep (se 1 (by rfl) ⟨387653, by rfl⟩ : syracuseStep 516871 = 775307) B775307
theorem B2057075 : Blo 405769 2057075 := bstep (se 1 (by rfl) ⟨1542806, by rfl⟩ : syracuseStep 2057075 = 3085613) B3085613
theorem B1303411 : Blo 405769 1303411 := bstep (se 1 (by rfl) ⟨977558, by rfl⟩ : syracuseStep 1303411 = 1955117) B1955117
theorem B549817 : Blo 405769 549817 := bstep (se 2 (by rfl) ⟨206181, by rfl⟩ : syracuseStep 549817 = 412363) B412363
theorem B2319313 : Blo 405769 2319313 := bstep (se 2 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 2319313 = 1739485) B1739485
theorem B2942189 : Blo 405769 2942189 := bstep (se 3 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 2942189 = 1103321) B1103321
theorem B517367 : Blo 405769 517367 := bstep (se 1 (by rfl) ⟨388025, by rfl⟩ : syracuseStep 517367 = 776051) B776051
theorem B2057561 : Blo 405769 2057561 := bstep (se 2 (by rfl) ⟨771585, by rfl⟩ : syracuseStep 2057561 = 1543171) B1543171
theorem B517519 : Blo 405769 517519 := bstep (se 1 (by rfl) ⟨388139, by rfl⟩ : syracuseStep 517519 = 776279) B776279
theorem B8381875 : Blo 405769 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B2942507 : Blo 405769 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B517691 : Blo 405769 517691 := bstep (se 1 (by rfl) ⟨388268, by rfl⟩ : syracuseStep 517691 = 776537) B776537
theorem B583303 : Blo 405769 583303 := bstep (se 1 (by rfl) ⟨437477, by rfl⟩ : syracuseStep 583303 = 874955) B874955
theorem B1369871 : Blo 405769 1369871 := bstep (se 1 (by rfl) ⟨1027403, by rfl⟩ : syracuseStep 1369871 = 2054807) B2054807
theorem B1173263 : Blo 405769 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B1370141 : Blo 405769 1370141 := bstep (se 3 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 1370141 = 513803) B513803
theorem B1959997 : Blo 405769 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B68512013 : Blo 405769 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B1305359 : Blo 405769 1305359 := bstep (se 1 (by rfl) ⟨979019, by rfl⟩ : syracuseStep 1305359 = 1958039) B1958039
theorem B650027 : Blo 405769 650027 := bstep (se 1 (by rfl) ⟨487520, by rfl⟩ : syracuseStep 650027 = 975041) B975041
theorem B2321297 : Blo 405769 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B1305629 : Blo 405769 1305629 := bstep (se 3 (by rfl) ⟨244805, by rfl⟩ : syracuseStep 1305629 = 489611) B489611
theorem B650539 : Blo 405769 650539 := bstep (se 1 (by rfl) ⟨487904, by rfl⟩ : syracuseStep 650539 = 975809) B975809
theorem B1469755 : Blo 405769 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B2059667 : Blo 405769 2059667 := bstep (se 1 (by rfl) ⟨1544750, by rfl⟩ : syracuseStep 2059667 = 3089501) B3089501
theorem B1371545 : Blo 405769 1371545 := bstep (se 2 (by rfl) ⟨514329, by rfl⟩ : syracuseStep 1371545 = 1028659) B1028659
theorem B913031 : Blo 405769 913031 := bstep (se 1 (by rfl) ⟨684773, by rfl⟩ : syracuseStep 913031 = 1369547) B1369547
theorem B552619 : Blo 405769 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B1961729 : Blo 405769 1961729 := bstep (se 2 (by rfl) ⟨735648, by rfl⟩ : syracuseStep 1961729 = 1471297) B1471297
theorem B1240847 : Blo 405769 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B618283 : Blo 405769 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B5009203 : Blo 405769 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B913211 : Blo 405769 913211 := bstep (se 1 (by rfl) ⟨684908, by rfl⟩ : syracuseStep 913211 = 1369817) B1369817
theorem B552763 : Blo 405769 552763 := bstep (se 1 (by rfl) ⟨414572, by rfl⟩ : syracuseStep 552763 = 829145) B829145
theorem B913337 : Blo 405769 913337 := bstep (se 2 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 913337 = 685003) B685003
theorem B1372247 : Blo 405769 1372247 := bstep (se 1 (by rfl) ⟨1029185, by rfl⟩ : syracuseStep 1372247 = 2058371) B2058371
theorem B651449 : Blo 405769 651449 := bstep (se 2 (by rfl) ⟨244293, by rfl⟩ : syracuseStep 651449 = 488587) B488587
theorem B913679 : Blo 405769 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B913697 : Blo 405769 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B979499 : Blo 405769 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B1372733 : Blo 405769 1372733 := bstep (se 3 (by rfl) ⟨257387, by rfl⟩ : syracuseStep 1372733 = 514775) B514775
theorem B914039 : Blo 405769 914039 := bstep (se 1 (by rfl) ⟨685529, by rfl⟩ : syracuseStep 914039 = 1371059) B1371059
theorem B914219 : Blo 405769 914219 := bstep (se 1 (by rfl) ⟨685664, by rfl⟩ : syracuseStep 914219 = 1371329) B1371329
theorem B553801 : Blo 405769 553801 := bstep (se 2 (by rfl) ⟨207675, by rfl⟩ : syracuseStep 553801 = 415351) B415351
theorem B979913 : Blo 405769 979913 := bstep (se 2 (by rfl) ⟨367467, by rfl⟩ : syracuseStep 979913 = 734935) B734935
theorem B1471441 : Blo 405769 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B1471555 : Blo 405769 1471555 := bstep (se 1 (by rfl) ⟨1103666, by rfl⟩ : syracuseStep 1471555 = 2207333) B2207333
theorem B914579 : Blo 405769 914579 := bstep (se 1 (by rfl) ⟨685934, by rfl⟩ : syracuseStep 914579 = 1371869) B1371869
theorem B980153 : Blo 405769 980153 := bstep (se 2 (by rfl) ⟨367557, by rfl⟩ : syracuseStep 980153 = 735115) B735115
theorem B914633 : Blo 405769 914633 := bstep (se 2 (by rfl) ⟨342987, by rfl⟩ : syracuseStep 914633 = 685975) B685975
theorem B1995977 : Blo 405769 1995977 := bstep (se 2 (by rfl) ⟨748491, by rfl⟩ : syracuseStep 1995977 = 1496983) B1496983
theorem B685327 : Blo 405769 685327 := bstep (se 1 (by rfl) ⟨513995, by rfl⟩ : syracuseStep 685327 = 1027991) B1027991
theorem B7828913 : Blo 405769 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B1308089 : Blo 405769 1308089 := bstep (se 2 (by rfl) ⟨490533, by rfl⟩ : syracuseStep 1308089 = 981067) B981067
theorem B1734155 : Blo 405769 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B1308203 : Blo 405769 1308203 := bstep (se 1 (by rfl) ⟨981152, by rfl⟩ : syracuseStep 1308203 = 1962305) B1962305
theorem B685867 : Blo 405769 685867 := bstep (se 1 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 685867 = 1028801) B1028801
theorem B456583 : Blo 405769 456583 := bstep (se 1 (by rfl) ⟨342437, by rfl⟩ : syracuseStep 456583 = 684875) B684875
theorem B915335 : Blo 405769 915335 := bstep (se 1 (by rfl) ⟨686501, by rfl⟩ : syracuseStep 915335 = 1373003) B1373003
theorem B980921 : Blo 405769 980921 := bstep (se 2 (by rfl) ⟨367845, by rfl⟩ : syracuseStep 980921 = 735691) B735691
theorem B686009 : Blo 405769 686009 := bstep (se 2 (by rfl) ⟨257253, by rfl⟩ : syracuseStep 686009 = 514507) B514507
theorem B1374137 : Blo 405769 1374137 := bstep (se 2 (by rfl) ⟨515301, by rfl⟩ : syracuseStep 1374137 = 1030603) B1030603
theorem B4651019 : Blo 405769 4651019 := bstep (se 1 (by rfl) ⟨3488264, by rfl⟩ : syracuseStep 4651019 = 6976529) B6976529
theorem B15628301 : Blo 405769 15628301 := bstep (se 3 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 15628301 = 5860613) B5860613
theorem B456763 : Blo 405769 456763 := bstep (se 1 (by rfl) ⟨342572, by rfl⟩ : syracuseStep 456763 = 685145) B685145
theorem B915515 : Blo 405769 915515 := bstep (se 1 (by rfl) ⟨686636, by rfl⟩ : syracuseStep 915515 = 1373273) B1373273
theorem B2619479 : Blo 405769 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B915641 : Blo 405769 915641 := bstep (se 2 (by rfl) ⟨343365, by rfl⟩ : syracuseStep 915641 = 686731) B686731
theorem B1964303 : Blo 405769 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B1767827 : Blo 405769 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B2062745 : Blo 405769 2062745 := bstep (se 2 (by rfl) ⟨773529, by rfl⟩ : syracuseStep 2062745 = 1547059) B1547059
theorem B1374731 : Blo 405769 1374731 := bstep (se 1 (by rfl) ⟨1031048, by rfl⟩ : syracuseStep 1374731 = 2062097) B2062097
theorem B457231 : Blo 405769 457231 := bstep (se 1 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 457231 = 685847) B685847
theorem B915983 : Blo 405769 915983 := bstep (se 1 (by rfl) ⟨686987, by rfl⟩ : syracuseStep 915983 = 1373975) B1373975
theorem B916001 : Blo 405769 916001 := bstep (se 2 (by rfl) ⟨343500, by rfl⟩ : syracuseStep 916001 = 687001) B687001
theorem B686711 : Blo 405769 686711 := bstep (se 1 (by rfl) ⟨515033, by rfl⟩ : syracuseStep 686711 = 1030067) B1030067
theorem B1374839 : Blo 405769 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B916343 : Blo 405769 916343 := bstep (se 1 (by rfl) ⟨687257, by rfl⟩ : syracuseStep 916343 = 1374515) B1374515
theorem B457735 : Blo 405769 457735 := bstep (se 1 (by rfl) ⟨343301, by rfl⟩ : syracuseStep 457735 = 686603) B686603
theorem B916523 : Blo 405769 916523 := bstep (se 1 (by rfl) ⟨687392, by rfl⟩ : syracuseStep 916523 = 1374785) B1374785
theorem B621611 : Blo 405769 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B687163 : Blo 405769 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B654455 : Blo 405769 654455 := bstep (se 1 (by rfl) ⟨490841, by rfl⟩ : syracuseStep 654455 = 981683) B981683
theorem B457915 : Blo 405769 457915 := bstep (se 1 (by rfl) ⟨343436, by rfl⟩ : syracuseStep 457915 = 686873) B686873
theorem B687305 : Blo 405769 687305 := bstep (se 2 (by rfl) ⟨257739, by rfl⟩ : syracuseStep 687305 = 515479) B515479
theorem B1375433 : Blo 405769 1375433 := bstep (se 2 (by rfl) ⟨515787, by rfl⟩ : syracuseStep 1375433 = 1031575) B1031575
theorem B2489573 : Blo 405769 2489573 := bstep (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) B466795
theorem B916883 : Blo 405769 916883 := bstep (se 1 (by rfl) ⟨687662, by rfl⟩ : syracuseStep 916883 = 1375325) B1375325
theorem B916937 : Blo 405769 916937 := bstep (se 2 (by rfl) ⟨343851, by rfl⟩ : syracuseStep 916937 = 687703) B687703
theorem B2326103 : Blo 405769 2326103 := bstep (se 1 (by rfl) ⟨1744577, by rfl⟩ : syracuseStep 2326103 = 3489155) B3489155
theorem B458383 : Blo 405769 458383 := bstep (se 1 (by rfl) ⟨343787, by rfl⟩ : syracuseStep 458383 = 687575) B687575
theorem B1244873 : Blo 405769 1244873 := bstep (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) B933655
theorem B786295 : Blo 405769 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B688007 : Blo 405769 688007 := bstep (se 1 (by rfl) ⟨516005, by rfl⟩ : syracuseStep 688007 = 1032011) B1032011
theorem B1376135 : Blo 405769 1376135 := bstep (se 1 (by rfl) ⟨1032101, by rfl⟩ : syracuseStep 1376135 = 2064203) B2064203
theorem B1965977 : Blo 405769 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B688135 : Blo 405769 688135 := bstep (se 1 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 688135 = 1032203) B1032203
theorem B5668879 : Blo 405769 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B917675 : Blo 405769 917675 := bstep (se 1 (by rfl) ⟨688256, by rfl⟩ : syracuseStep 917675 = 1376513) B1376513
theorem B459103 : Blo 405769 459103 := bstep (se 1 (by rfl) ⟨344327, by rfl⟩ : syracuseStep 459103 = 688655) B688655
theorem B688567 : Blo 405769 688567 := bstep (se 1 (by rfl) ⟨516425, by rfl⟩ : syracuseStep 688567 = 1032851) B1032851
theorem B1737197 : Blo 405769 1737197 := bstep (se 3 (by rfl) ⟨325724, by rfl⟩ : syracuseStep 1737197 = 651449) B651449
theorem B2196001 : Blo 405769 2196001 := bstep (se 2 (by rfl) ⟨823500, by rfl⟩ : syracuseStep 2196001 = 1647001) B1647001
theorem B1311329 : Blo 405769 1311329 := bstep (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) B983497
theorem B1376891 : Blo 405769 1376891 := bstep (se 1 (by rfl) ⟨1032668, by rfl⟩ : syracuseStep 1376891 = 2065337) B2065337
theorem B688763 : Blo 405769 688763 := bstep (se 1 (by rfl) ⟨516572, by rfl⟩ : syracuseStep 688763 = 1033145) B1033145
theorem B918215 : Blo 405769 918215 := bstep (se 1 (by rfl) ⟨688661, by rfl⟩ : syracuseStep 918215 = 1377323) B1377323
theorem B459463 : Blo 405769 459463 := bstep (se 1 (by rfl) ⟨344597, by rfl⟩ : syracuseStep 459463 = 689195) B689195
theorem B1377053 : Blo 405769 1377053 := bstep (se 3 (by rfl) ⟨258197, by rfl⟩ : syracuseStep 1377053 = 516395) B516395
theorem B7537481 : Blo 405769 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B8258507 : Blo 405769 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B2950145 : Blo 405769 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B689161 : Blo 405769 689161 := bstep (se 2 (by rfl) ⟨258435, by rfl⟩ : syracuseStep 689161 = 516871) B516871
theorem B984143 : Blo 405769 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B1737881 : Blo 405769 1737881 := bstep (se 2 (by rfl) ⟨651705, by rfl⟩ : syracuseStep 1737881 = 1303411) B1303411
theorem B689323 : Blo 405769 689323 := bstep (se 1 (by rfl) ⟨516992, by rfl⟩ : syracuseStep 689323 = 1033985) B1033985
theorem B5211485 : Blo 405769 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B1541501 : Blo 405769 1541501 := bstep (se 3 (by rfl) ⟨289031, by rfl⟩ : syracuseStep 1541501 = 578063) B578063
theorem B2491813 : Blo 405769 2491813 := bstep (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) B467215
theorem B1377755 : Blo 405769 1377755 := bstep (se 1 (by rfl) ⟨1033316, by rfl⟩ : syracuseStep 1377755 = 2066633) B2066633
theorem B689627 : Blo 405769 689627 := bstep (se 1 (by rfl) ⟨517220, by rfl⟩ : syracuseStep 689627 = 1034441) B1034441
theorem B919079 : Blo 405769 919079 := bstep (se 1 (by rfl) ⟨689309, by rfl⟩ : syracuseStep 919079 = 1378619) B1378619
theorem B460327 : Blo 405769 460327 := bstep (se 1 (by rfl) ⟨345245, by rfl⟩ : syracuseStep 460327 = 690491) B690491
theorem B689863 : Blo 405769 689863 := bstep (se 1 (by rfl) ⟨517397, by rfl⟩ : syracuseStep 689863 = 1034795) B1034795
theorem B690025 : Blo 405769 690025 := bstep (se 2 (by rfl) ⟨258759, by rfl⟩ : syracuseStep 690025 = 517519) B517519
theorem B919403 : Blo 405769 919403 := bstep (se 1 (by rfl) ⟨689552, by rfl⟩ : syracuseStep 919403 = 1379105) B1379105
theorem B11175833 : Blo 405769 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B919457 : Blo 405769 919457 := bstep (se 2 (by rfl) ⟨344796, by rfl⟩ : syracuseStep 919457 = 689593) B689593
theorem B1378457 : Blo 405769 1378457 := bstep (se 2 (by rfl) ⟨516921, by rfl⟩ : syracuseStep 1378457 = 1033843) B1033843
theorem B11798729 : Blo 405769 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B5900525 : Blo 405769 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B7473389 : Blo 405769 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B919799 : Blo 405769 919799 := bstep (se 1 (by rfl) ⟨689849, by rfl⟩ : syracuseStep 919799 = 1379699) B1379699
theorem B690619 : Blo 405769 690619 := bstep (se 1 (by rfl) ⟨517964, by rfl⟩ : syracuseStep 690619 = 1035929) B1035929
theorem B690727 : Blo 405769 690727 := bstep (se 1 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 690727 = 1036091) B1036091
theorem B920393 : Blo 405769 920393 := bstep (se 2 (by rfl) ⟨345147, by rfl⟩ : syracuseStep 920393 = 690295) B690295
theorem B691051 : Blo 405769 691051 := bstep (se 1 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 691051 = 1036577) B1036577
theorem B3083183 : Blo 405769 3083183 := bstep (se 1 (by rfl) ⟨2312387, by rfl⟩ : syracuseStep 3083183 = 4624775) B4624775
theorem B2329519 : Blo 405769 2329519 := bstep (se 1 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 2329519 = 3494279) B3494279
theorem B9637157 : Blo 405769 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B1379645 : Blo 405769 1379645 := bstep (se 3 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 1379645 = 517367) B517367
theorem B1543643 : Blo 405769 1543643 := bstep (se 1 (by rfl) ⟨1157732, by rfl⟩ : syracuseStep 1543643 = 2315465) B2315465
theorem B921185 : Blo 405769 921185 := bstep (se 2 (by rfl) ⟨345444, by rfl⟩ : syracuseStep 921185 = 690889) B690889
theorem B2068091 : Blo 405769 2068091 := bstep (se 1 (by rfl) ⟨1551068, by rfl⟩ : syracuseStep 2068091 = 3102137) B3102137
theorem B2330477 : Blo 405769 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B5246855 : Blo 405769 5246855 := bstep (se 1 (by rfl) ⟨3935141, by rfl⟩ : syracuseStep 5246855 = 7870283) B7870283
theorem B921527 : Blo 405769 921527 := bstep (se 1 (by rfl) ⟨691145, by rfl⟩ : syracuseStep 921527 = 1382291) B1382291
theorem B1675379 : Blo 405769 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B1380509 : Blo 405769 1380509 := bstep (se 3 (by rfl) ⟨258845, by rfl⟩ : syracuseStep 1380509 = 517691) B517691
theorem B2101565 : Blo 405769 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B1381049 : Blo 405769 1381049 := bstep (se 2 (by rfl) ⟨517893, by rfl⟩ : syracuseStep 1381049 = 1035787) B1035787
theorem B1544903 : Blo 405769 1544903 := bstep (se 1 (by rfl) ⟨1158677, by rfl⟩ : syracuseStep 1544903 = 2317355) B2317355
theorem B660215 : Blo 405769 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B1381643 : Blo 405769 1381643 := bstep (se 1 (by rfl) ⟨1036232, by rfl⟩ : syracuseStep 1381643 = 2072465) B2072465
theorem B1545601 : Blo 405769 1545601 := bstep (se 2 (by rfl) ⟨579600, by rfl⟩ : syracuseStep 1545601 = 1159201) B1159201
theorem B1381913 : Blo 405769 1381913 := bstep (se 2 (by rfl) ⟨518217, by rfl⟩ : syracuseStep 1381913 = 1036435) B1036435
theorem B6985277 : Blo 405769 6985277 := bstep (se 3 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 6985277 = 2619479) B2619479
theorem B1545875 : Blo 405769 1545875 := bstep (se 1 (by rfl) ⟨1159406, by rfl⟩ : syracuseStep 1545875 = 2318813) B2318813
theorem B3708965 : Blo 405769 3708965 := bstep (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) B695431
theorem B2332709 : Blo 405769 2332709 := bstep (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) B437383
theorem B2070845 : Blo 405769 2070845 := bstep (se 3 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 2070845 = 776567) B776567
theorem B2333393 : Blo 405769 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B433351 : Blo 405769 433351 := bstep (se 1 (by rfl) ⟨325013, by rfl⟩ : syracuseStep 433351 = 650027) B650027
theorem B1547531 : Blo 405769 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B4202117 : Blo 405769 4202117 := bstep (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) B787897
theorem B827231 : Blo 405769 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B2073113 : Blo 405769 2073113 := bstep (se 2 (by rfl) ⟨777417, by rfl⟩ : syracuseStep 2073113 = 1554835) B1554835
theorem B1548989 : Blo 405769 1548989 := bstep (se 3 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 1548989 = 580871) B580871
theorem B5219275 : Blo 405769 5219275 := bstep (se 1 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 5219275 = 7828913) B7828913
theorem B1156103 : Blo 405769 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B1156457 : Blo 405769 1156457 := bstep (se 2 (by rfl) ⟨433671, by rfl⟩ : syracuseStep 1156457 = 867343) B867343
theorem B3352103 : Blo 405769 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B3319661 : Blo 405769 3319661 := bstep (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) B1244873
theorem B436303 : Blo 405769 436303 := bstep (se 1 (by rfl) ⟨327227, by rfl⟩ : syracuseStep 436303 = 654455) B654455
theorem B1648721 : Blo 405769 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B797033 : Blo 405769 797033 := bstep (se 2 (by rfl) ⟨298887, by rfl⟩ : syracuseStep 797033 = 597775) B597775
theorem B1550735 : Blo 405769 1550735 := bstep (se 1 (by rfl) ⟨1163051, by rfl⟩ : syracuseStep 1550735 = 2326103) B2326103
theorem B764615 : Blo 405769 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B4664141 : Blo 405769 4664141 := bstep (se 3 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 4664141 = 1749053) B1749053
theorem B732167 : Blo 405769 732167 := bstep (se 1 (by rfl) ⟨549125, by rfl⟩ : syracuseStep 732167 = 1098251) B1098251
theorem B699401 : Blo 405769 699401 := bstep (se 2 (by rfl) ⟨262275, by rfl⟩ : syracuseStep 699401 = 524551) B524551
theorem B2796611 : Blo 405769 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B1027151 : Blo 405769 1027151 := bstep (se 1 (by rfl) ⟨770363, by rfl⟩ : syracuseStep 1027151 = 1540727) B1540727
theorem B2600207 : Blo 405769 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B3091931 : Blo 405769 3091931 := bstep (se 1 (by rfl) ⟨2318948, by rfl⟩ : syracuseStep 3091931 = 4637897) B4637897
theorem B1551905 : Blo 405769 1551905 := bstep (se 2 (by rfl) ⟨581964, by rfl⟩ : syracuseStep 1551905 = 1163929) B1163929
theorem B1027799 : Blo 405769 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B2993885 : Blo 405769 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B1552223 : Blo 405769 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B1159019 : Blo 405769 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B3092417 : Blo 405769 3092417 := bstep (se 2 (by rfl) ⟨1159656, by rfl⟩ : syracuseStep 3092417 = 2319313) B2319313
theorem B1552391 : Blo 405769 1552391 := bstep (se 1 (by rfl) ⟨1164293, by rfl⟩ : syracuseStep 1552391 = 2328587) B2328587
theorem B4960271 : Blo 405769 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B1028153 : Blo 405769 1028153 := bstep (se 2 (by rfl) ⟨385557, by rfl⟩ : syracuseStep 1028153 = 771115) B771115
theorem B1159247 : Blo 405769 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B405799 : Blo 405769 405799 := bstep (se 1 (by rfl) ⟨304349, by rfl⟩ : syracuseStep 405799 = 608699) B608699
theorem B405839 : Blo 405769 405839 := bstep (se 1 (by rfl) ⟨304379, by rfl⟩ : syracuseStep 405839 = 608759) B608759
theorem B405855 : Blo 405769 405855 := bstep (se 1 (by rfl) ⟨304391, by rfl⟩ : syracuseStep 405855 = 608783) B608783
theorem B405883 : Blo 405769 405883 := bstep (se 1 (by rfl) ⟨304412, by rfl⟩ : syracuseStep 405883 = 608825) B608825
theorem B405935 : Blo 405769 405935 := bstep (se 1 (by rfl) ⟨304451, by rfl⟩ : syracuseStep 405935 = 608903) B608903
theorem B405959 : Blo 405769 405959 := bstep (se 1 (by rfl) ⟨304469, by rfl⟩ : syracuseStep 405959 = 608939) B608939
theorem B405979 : Blo 405769 405979 := bstep (se 1 (by rfl) ⟨304484, by rfl⟩ : syracuseStep 405979 = 608969) B608969
theorem B1552877 : Blo 405769 1552877 := bstep (se 3 (by rfl) ⟨291164, by rfl⟩ : syracuseStep 1552877 = 582329) B582329
theorem B406055 : Blo 405769 406055 := bstep (se 1 (by rfl) ⟨304541, by rfl⟩ : syracuseStep 406055 = 609083) B609083
theorem B406095 : Blo 405769 406095 := bstep (se 1 (by rfl) ⟨304571, by rfl⟩ : syracuseStep 406095 = 609143) B609143
theorem B406111 : Blo 405769 406111 := bstep (se 1 (by rfl) ⟨304583, by rfl⟩ : syracuseStep 406111 = 609167) B609167
theorem B406139 : Blo 405769 406139 := bstep (se 1 (by rfl) ⟨304604, by rfl⟩ : syracuseStep 406139 = 609209) B609209
theorem B406191 : Blo 405769 406191 := bstep (se 1 (by rfl) ⟨304643, by rfl⟩ : syracuseStep 406191 = 609287) B609287
theorem B406215 : Blo 405769 406215 := bstep (se 1 (by rfl) ⟨304661, by rfl⟩ : syracuseStep 406215 = 609323) B609323
theorem B406235 : Blo 405769 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B406311 : Blo 405769 406311 := bstep (se 1 (by rfl) ⟨304733, by rfl⟩ : syracuseStep 406311 = 609467) B609467
theorem B1553195 : Blo 405769 1553195 := bstep (se 1 (by rfl) ⟨1164896, by rfl⟩ : syracuseStep 1553195 = 2329793) B2329793
theorem B406351 : Blo 405769 406351 := bstep (se 1 (by rfl) ⟨304763, by rfl⟩ : syracuseStep 406351 = 609527) B609527
theorem B406367 : Blo 405769 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B406395 : Blo 405769 406395 := bstep (se 1 (by rfl) ⟨304796, by rfl⟩ : syracuseStep 406395 = 609593) B609593
theorem B406447 : Blo 405769 406447 := bstep (se 1 (by rfl) ⟨304835, by rfl⟩ : syracuseStep 406447 = 609671) B609671
theorem B406471 : Blo 405769 406471 := bstep (se 1 (by rfl) ⟨304853, by rfl⟩ : syracuseStep 406471 = 609707) B609707
theorem B406491 : Blo 405769 406491 := bstep (se 1 (by rfl) ⟨304868, by rfl⟩ : syracuseStep 406491 = 609737) B609737
theorem B406567 : Blo 405769 406567 := bstep (se 1 (by rfl) ⟨304925, by rfl⟩ : syracuseStep 406567 = 609851) B609851
theorem B406607 : Blo 405769 406607 := bstep (se 1 (by rfl) ⟨304955, by rfl⟩ : syracuseStep 406607 = 609911) B609911
theorem B406623 : Blo 405769 406623 := bstep (se 1 (by rfl) ⟨304967, by rfl⟩ : syracuseStep 406623 = 609935) B609935
theorem B406651 : Blo 405769 406651 := bstep (se 1 (by rfl) ⟨304988, by rfl⟩ : syracuseStep 406651 = 609977) B609977
theorem B406703 : Blo 405769 406703 := bstep (se 1 (by rfl) ⟨305027, by rfl⟩ : syracuseStep 406703 = 610055) B610055
theorem B406727 : Blo 405769 406727 := bstep (se 1 (by rfl) ⟨305045, by rfl⟩ : syracuseStep 406727 = 610091) B610091
theorem B406747 : Blo 405769 406747 := bstep (se 1 (by rfl) ⟨305060, by rfl⟩ : syracuseStep 406747 = 610121) B610121
theorem B406823 : Blo 405769 406823 := bstep (se 1 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 406823 = 610235) B610235
theorem B406863 : Blo 405769 406863 := bstep (se 1 (by rfl) ⟨305147, by rfl⟩ : syracuseStep 406863 = 610295) B610295
theorem B406879 : Blo 405769 406879 := bstep (se 1 (by rfl) ⟨305159, by rfl⟩ : syracuseStep 406879 = 610319) B610319
theorem B3093875 : Blo 405769 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B406907 : Blo 405769 406907 := bstep (se 1 (by rfl) ⟨305180, by rfl⟩ : syracuseStep 406907 = 610361) B610361
theorem B406959 : Blo 405769 406959 := bstep (se 1 (by rfl) ⟨305219, by rfl⟩ : syracuseStep 406959 = 610439) B610439
theorem B406983 : Blo 405769 406983 := bstep (se 1 (by rfl) ⟨305237, by rfl⟩ : syracuseStep 406983 = 610475) B610475
theorem B407003 : Blo 405769 407003 := bstep (se 1 (by rfl) ⟨305252, by rfl⟩ : syracuseStep 407003 = 610505) B610505
theorem B767497 : Blo 405769 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B407079 : Blo 405769 407079 := bstep (se 1 (by rfl) ⟨305309, by rfl⟩ : syracuseStep 407079 = 610619) B610619
theorem B407119 : Blo 405769 407119 := bstep (se 1 (by rfl) ⟨305339, by rfl⟩ : syracuseStep 407119 = 610679) B610679
theorem B407135 : Blo 405769 407135 := bstep (se 1 (by rfl) ⟨305351, by rfl⟩ : syracuseStep 407135 = 610703) B610703
theorem B3716705 : Blo 405769 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B407163 : Blo 405769 407163 := bstep (se 1 (by rfl) ⟨305372, by rfl⟩ : syracuseStep 407163 = 610745) B610745
theorem B407215 : Blo 405769 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B407239 : Blo 405769 407239 := bstep (se 1 (by rfl) ⟨305429, by rfl⟩ : syracuseStep 407239 = 610859) B610859
theorem B407259 : Blo 405769 407259 := bstep (se 1 (by rfl) ⟨305444, by rfl⟩ : syracuseStep 407259 = 610889) B610889
theorem B407335 : Blo 405769 407335 := bstep (se 1 (by rfl) ⟨305501, by rfl⟩ : syracuseStep 407335 = 611003) B611003
theorem B3127099 : Blo 405769 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B407375 : Blo 405769 407375 := bstep (se 1 (by rfl) ⟨305531, by rfl⟩ : syracuseStep 407375 = 611063) B611063
theorem B407391 : Blo 405769 407391 := bstep (se 1 (by rfl) ⟨305543, by rfl⟩ : syracuseStep 407391 = 611087) B611087
theorem B407419 : Blo 405769 407419 := bstep (se 1 (by rfl) ⟨305564, by rfl⟩ : syracuseStep 407419 = 611129) B611129
theorem B407471 : Blo 405769 407471 := bstep (se 1 (by rfl) ⟨305603, by rfl⟩ : syracuseStep 407471 = 611207) B611207
theorem B5027777 : Blo 405769 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B407495 : Blo 405769 407495 := bstep (se 1 (by rfl) ⟨305621, by rfl⟩ : syracuseStep 407495 = 611243) B611243
theorem B407515 : Blo 405769 407515 := bstep (se 1 (by rfl) ⟨305636, by rfl⟩ : syracuseStep 407515 = 611273) B611273
theorem B407591 : Blo 405769 407591 := bstep (se 1 (by rfl) ⟨305693, by rfl⟩ : syracuseStep 407591 = 611387) B611387
theorem B407631 : Blo 405769 407631 := bstep (se 1 (by rfl) ⟨305723, by rfl⟩ : syracuseStep 407631 = 611447) B611447
theorem B4241497 : Blo 405769 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B407647 : Blo 405769 407647 := bstep (se 1 (by rfl) ⟨305735, by rfl⟩ : syracuseStep 407647 = 611471) B611471
theorem B407675 : Blo 405769 407675 := bstep (se 1 (by rfl) ⟨305756, by rfl⟩ : syracuseStep 407675 = 611513) B611513
theorem B407727 : Blo 405769 407727 := bstep (se 1 (by rfl) ⟨305795, by rfl⟩ : syracuseStep 407727 = 611591) B611591
theorem B407751 : Blo 405769 407751 := bstep (se 1 (by rfl) ⟨305813, by rfl⟩ : syracuseStep 407751 = 611627) B611627
theorem B407771 : Blo 405769 407771 := bstep (se 1 (by rfl) ⟨305828, by rfl⟩ : syracuseStep 407771 = 611657) B611657
theorem B1030391 : Blo 405769 1030391 := bstep (se 1 (by rfl) ⟨772793, by rfl⟩ : syracuseStep 1030391 = 1545587) B1545587
theorem B407847 : Blo 405769 407847 := bstep (se 1 (by rfl) ⟨305885, by rfl⟩ : syracuseStep 407847 = 611771) B611771
theorem B5880113 : Blo 405769 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B407887 : Blo 405769 407887 := bstep (se 1 (by rfl) ⟨305915, by rfl⟩ : syracuseStep 407887 = 611831) B611831
theorem B188627285 : Blo 405769 188627285 := bstep (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) B552619
theorem B407903 : Blo 405769 407903 := bstep (se 1 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 407903 = 611855) B611855
theorem B407931 : Blo 405769 407931 := bstep (se 1 (by rfl) ⟨305948, by rfl⟩ : syracuseStep 407931 = 611897) B611897
theorem B407983 : Blo 405769 407983 := bstep (se 1 (by rfl) ⟨305987, by rfl⟩ : syracuseStep 407983 = 611975) B611975
theorem B408007 : Blo 405769 408007 := bstep (se 1 (by rfl) ⟨306005, by rfl⟩ : syracuseStep 408007 = 612011) B612011
theorem B408027 : Blo 405769 408027 := bstep (se 1 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 408027 = 612041) B612041
theorem B408103 : Blo 405769 408103 := bstep (se 1 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 408103 = 612155) B612155
theorem B408143 : Blo 405769 408143 := bstep (se 1 (by rfl) ⟨306107, by rfl⟩ : syracuseStep 408143 = 612215) B612215
theorem B408159 : Blo 405769 408159 := bstep (se 1 (by rfl) ⟨306119, by rfl⟩ : syracuseStep 408159 = 612239) B612239
theorem B408187 : Blo 405769 408187 := bstep (se 1 (by rfl) ⟨306140, by rfl⟩ : syracuseStep 408187 = 612281) B612281
theorem B408239 : Blo 405769 408239 := bstep (se 1 (by rfl) ⟨306179, by rfl⟩ : syracuseStep 408239 = 612359) B612359
theorem B408263 : Blo 405769 408263 := bstep (se 1 (by rfl) ⟨306197, by rfl⟩ : syracuseStep 408263 = 612395) B612395
theorem B408283 : Blo 405769 408283 := bstep (se 1 (by rfl) ⟨306212, by rfl⟩ : syracuseStep 408283 = 612425) B612425
theorem B408359 : Blo 405769 408359 := bstep (se 1 (by rfl) ⟨306269, by rfl⟩ : syracuseStep 408359 = 612539) B612539
theorem B408399 : Blo 405769 408399 := bstep (se 1 (by rfl) ⟨306299, by rfl⟩ : syracuseStep 408399 = 612599) B612599
theorem B408415 : Blo 405769 408415 := bstep (se 1 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 408415 = 612623) B612623
theorem B1555307 : Blo 405769 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B408443 : Blo 405769 408443 := bstep (se 1 (by rfl) ⟨306332, by rfl⟩ : syracuseStep 408443 = 612665) B612665
theorem B408495 : Blo 405769 408495 := bstep (se 1 (by rfl) ⟨306371, by rfl⟩ : syracuseStep 408495 = 612743) B612743
theorem B408519 : Blo 405769 408519 := bstep (se 1 (by rfl) ⟨306389, by rfl⟩ : syracuseStep 408519 = 612779) B612779
theorem B408539 : Blo 405769 408539 := bstep (se 1 (by rfl) ⟨306404, by rfl⟩ : syracuseStep 408539 = 612809) B612809
theorem B408615 : Blo 405769 408615 := bstep (se 1 (by rfl) ⟨306461, by rfl⟩ : syracuseStep 408615 = 612923) B612923
theorem B867385 : Blo 405769 867385 := bstep (se 2 (by rfl) ⟨325269, by rfl⟩ : syracuseStep 867385 = 650539) B650539
theorem B408655 : Blo 405769 408655 := bstep (se 1 (by rfl) ⟨306491, by rfl⟩ : syracuseStep 408655 = 612983) B612983
theorem B408671 : Blo 405769 408671 := bstep (se 1 (by rfl) ⟨306503, by rfl⟩ : syracuseStep 408671 = 613007) B613007
theorem B408699 : Blo 405769 408699 := bstep (se 1 (by rfl) ⟨306524, by rfl⟩ : syracuseStep 408699 = 613049) B613049
theorem B408751 : Blo 405769 408751 := bstep (se 1 (by rfl) ⟨306563, by rfl⟩ : syracuseStep 408751 = 613127) B613127
theorem B408775 : Blo 405769 408775 := bstep (se 1 (by rfl) ⟨306581, by rfl⟩ : syracuseStep 408775 = 613163) B613163
theorem B408795 : Blo 405769 408795 := bstep (se 1 (by rfl) ⟨306596, by rfl⟩ : syracuseStep 408795 = 613193) B613193
theorem B2931983 : Blo 405769 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B408871 : Blo 405769 408871 := bstep (se 1 (by rfl) ⟨306653, by rfl⟩ : syracuseStep 408871 = 613307) B613307
theorem B408911 : Blo 405769 408911 := bstep (se 1 (by rfl) ⟨306683, by rfl⟩ : syracuseStep 408911 = 613367) B613367
theorem B408927 : Blo 405769 408927 := bstep (se 1 (by rfl) ⟨306695, by rfl⟩ : syracuseStep 408927 = 613391) B613391
theorem B408955 : Blo 405769 408955 := bstep (se 1 (by rfl) ⟨306716, by rfl⟩ : syracuseStep 408955 = 613433) B613433
theorem B3128701 : Blo 405769 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B409007 : Blo 405769 409007 := bstep (se 1 (by rfl) ⟨306755, by rfl⟩ : syracuseStep 409007 = 613511) B613511
theorem B409031 : Blo 405769 409031 := bstep (se 1 (by rfl) ⟨306773, by rfl⟩ : syracuseStep 409031 = 613547) B613547
theorem B409051 : Blo 405769 409051 := bstep (se 1 (by rfl) ⟨306788, by rfl⟩ : syracuseStep 409051 = 613577) B613577
theorem B409127 : Blo 405769 409127 := bstep (se 1 (by rfl) ⟨306845, by rfl⟩ : syracuseStep 409127 = 613691) B613691
theorem B409167 : Blo 405769 409167 := bstep (se 1 (by rfl) ⟨306875, by rfl⟩ : syracuseStep 409167 = 613751) B613751
theorem B409183 : Blo 405769 409183 := bstep (se 1 (by rfl) ⟨306887, by rfl⟩ : syracuseStep 409183 = 613775) B613775
theorem B409211 : Blo 405769 409211 := bstep (se 1 (by rfl) ⟨306908, by rfl⟩ : syracuseStep 409211 = 613817) B613817
theorem B2932357 : Blo 405769 2932357 := bstep (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) B549817
theorem B409263 : Blo 405769 409263 := bstep (se 1 (by rfl) ⟨306947, by rfl⟩ : syracuseStep 409263 = 613895) B613895
theorem B1031879 : Blo 405769 1031879 := bstep (se 1 (by rfl) ⟨773909, by rfl⟩ : syracuseStep 1031879 = 1547819) B1547819
theorem B409287 : Blo 405769 409287 := bstep (se 1 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 409287 = 613931) B613931
theorem B409307 : Blo 405769 409307 := bstep (se 1 (by rfl) ⟨306980, by rfl⟩ : syracuseStep 409307 = 613961) B613961
theorem B409383 : Blo 405769 409383 := bstep (se 1 (by rfl) ⟨307037, by rfl⟩ : syracuseStep 409383 = 614075) B614075
theorem B409423 : Blo 405769 409423 := bstep (se 1 (by rfl) ⟨307067, by rfl⟩ : syracuseStep 409423 = 614135) B614135
theorem B409439 : Blo 405769 409439 := bstep (se 1 (by rfl) ⟨307079, by rfl⟩ : syracuseStep 409439 = 614159) B614159
theorem B409467 : Blo 405769 409467 := bstep (se 1 (by rfl) ⟨307100, by rfl⟩ : syracuseStep 409467 = 614201) B614201
theorem B2211745 : Blo 405769 2211745 := bstep (se 2 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 2211745 = 1658809) B1658809
theorem B409519 : Blo 405769 409519 := bstep (se 1 (by rfl) ⟨307139, by rfl⟩ : syracuseStep 409519 = 614279) B614279
theorem B409543 : Blo 405769 409543 := bstep (se 1 (by rfl) ⟨307157, by rfl⟩ : syracuseStep 409543 = 614315) B614315
theorem B409563 : Blo 405769 409563 := bstep (se 1 (by rfl) ⟨307172, by rfl⟩ : syracuseStep 409563 = 614345) B614345
theorem B409639 : Blo 405769 409639 := bstep (se 1 (by rfl) ⟨307229, by rfl⟩ : syracuseStep 409639 = 614459) B614459
theorem B409679 : Blo 405769 409679 := bstep (se 1 (by rfl) ⟨307259, by rfl⟩ : syracuseStep 409679 = 614519) B614519
theorem B409695 : Blo 405769 409695 := bstep (se 1 (by rfl) ⟨307271, by rfl⟩ : syracuseStep 409695 = 614543) B614543
theorem B409723 : Blo 405769 409723 := bstep (se 1 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 409723 = 614585) B614585
theorem B770447 : Blo 405769 770447 := bstep (se 1 (by rfl) ⟨577835, by rfl⟩ : syracuseStep 770447 = 1155671) B1155671
theorem B1851929 : Blo 405769 1851929 := bstep (se 2 (by rfl) ⟨694473, by rfl⟩ : syracuseStep 1851929 = 1388947) B1388947
theorem B1098455 : Blo 405769 1098455 := bstep (se 1 (by rfl) ⟨823841, by rfl⟩ : syracuseStep 1098455 = 1647683) B1647683
theorem B4965137 : Blo 405769 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B1033033 : Blo 405769 1033033 := bstep (se 2 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 1033033 = 774775) B774775
theorem B738401 : Blo 405769 738401 := bstep (se 2 (by rfl) ⟨276900, by rfl⟩ : syracuseStep 738401 = 553801) B553801
theorem B771707 : Blo 405769 771707 := bstep (se 1 (by rfl) ⟨578780, by rfl⟩ : syracuseStep 771707 = 1157561) B1157561
theorem B870239 : Blo 405769 870239 := bstep (se 1 (by rfl) ⟨652679, by rfl⟩ : syracuseStep 870239 = 1305359) B1305359
theorem B1034167 : Blo 405769 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B870419 : Blo 405769 870419 := bstep (se 1 (by rfl) ⟨652814, by rfl⟩ : syracuseStep 870419 = 1305629) B1305629
theorem B772193 : Blo 405769 772193 := bstep (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) B579145
theorem B772345 : Blo 405769 772345 := bstep (se 2 (by rfl) ⟨289629, by rfl⟩ : syracuseStep 772345 = 579259) B579259
theorem B608687 : Blo 405769 608687 := bstep (se 1 (by rfl) ⟨456515, by rfl⟩ : syracuseStep 608687 = 913031) B913031
theorem B608777 : Blo 405769 608777 := bstep (se 2 (by rfl) ⟨228291, by rfl⟩ : syracuseStep 608777 = 456583) B456583
theorem B608807 : Blo 405769 608807 := bstep (se 1 (by rfl) ⟨456605, by rfl⟩ : syracuseStep 608807 = 913211) B913211
theorem B608891 : Blo 405769 608891 := bstep (se 1 (by rfl) ⟨456668, by rfl⟩ : syracuseStep 608891 = 913337) B913337
theorem B609017 : Blo 405769 609017 := bstep (se 2 (by rfl) ⟨228381, by rfl⟩ : syracuseStep 609017 = 456763) B456763
theorem B609119 : Blo 405769 609119 := bstep (se 1 (by rfl) ⟨456839, by rfl⟩ : syracuseStep 609119 = 913679) B913679
theorem B609131 : Blo 405769 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B2476975 : Blo 405769 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B2214839 : Blo 405769 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B609359 : Blo 405769 609359 := bstep (se 1 (by rfl) ⟨457019, by rfl⟩ : syracuseStep 609359 = 914039) B914039
theorem B609479 : Blo 405769 609479 := bstep (se 1 (by rfl) ⟨457109, by rfl⟩ : syracuseStep 609479 = 914219) B914219
theorem B6638861 : Blo 405769 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B609641 : Blo 405769 609641 := bstep (se 2 (by rfl) ⟨228615, by rfl⟩ : syracuseStep 609641 = 457231) B457231
theorem B1035625 : Blo 405769 1035625 := bstep (se 2 (by rfl) ⟨388359, by rfl⟩ : syracuseStep 1035625 = 776719) B776719
theorem B609719 : Blo 405769 609719 := bstep (se 1 (by rfl) ⟨457289, by rfl⟩ : syracuseStep 609719 = 914579) B914579
theorem B609755 : Blo 405769 609755 := bstep (se 1 (by rfl) ⟨457316, by rfl⟩ : syracuseStep 609755 = 914633) B914633
theorem B1330651 : Blo 405769 1330651 := bstep (se 1 (by rfl) ⟨997988, by rfl⟩ : syracuseStep 1330651 = 1995977) B1995977
theorem B773651 : Blo 405769 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B872059 : Blo 405769 872059 := bstep (se 1 (by rfl) ⟨654044, by rfl⟩ : syracuseStep 872059 = 1308089) B1308089
theorem B1035899 : Blo 405769 1035899 := bstep (se 1 (by rfl) ⟨776924, by rfl⟩ : syracuseStep 1035899 = 1553849) B1553849
theorem B773803 : Blo 405769 773803 := bstep (se 1 (by rfl) ⟨580352, by rfl⟩ : syracuseStep 773803 = 1160705) B1160705
theorem B872135 : Blo 405769 872135 := bstep (se 1 (by rfl) ⟨654101, by rfl⟩ : syracuseStep 872135 = 1308203) B1308203
theorem B774031 : Blo 405769 774031 := bstep (se 1 (by rfl) ⟨580523, by rfl⟩ : syracuseStep 774031 = 1161047) B1161047
theorem B610223 : Blo 405769 610223 := bstep (se 1 (by rfl) ⟨457667, by rfl⟩ : syracuseStep 610223 = 915335) B915335
theorem B774107 : Blo 405769 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B3100679 : Blo 405769 3100679 := bstep (se 1 (by rfl) ⟨2325509, by rfl⟩ : syracuseStep 3100679 = 4651019) B4651019
theorem B610313 : Blo 405769 610313 := bstep (se 2 (by rfl) ⟨228867, by rfl⟩ : syracuseStep 610313 = 457735) B457735
theorem B610343 : Blo 405769 610343 := bstep (se 1 (by rfl) ⟨457757, by rfl⟩ : syracuseStep 610343 = 915515) B915515
theorem B610427 : Blo 405769 610427 := bstep (se 1 (by rfl) ⟨457820, by rfl⟩ : syracuseStep 610427 = 915641) B915641
theorem B3297509 : Blo 405769 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B610553 : Blo 405769 610553 := bstep (se 2 (by rfl) ⟨228957, by rfl⟩ : syracuseStep 610553 = 457915) B457915
theorem B610655 : Blo 405769 610655 := bstep (se 1 (by rfl) ⟨457991, by rfl⟩ : syracuseStep 610655 = 915983) B915983
theorem B1954153 : Blo 405769 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B610667 : Blo 405769 610667 := bstep (se 1 (by rfl) ⟨458000, by rfl⟩ : syracuseStep 610667 = 916001) B916001
theorem B3101165 : Blo 405769 3101165 := bstep (se 3 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 3101165 = 1162937) B1162937
theorem B610895 : Blo 405769 610895 := bstep (se 1 (by rfl) ⟨458171, by rfl⟩ : syracuseStep 610895 = 916343) B916343
theorem B611015 : Blo 405769 611015 := bstep (se 1 (by rfl) ⟨458261, by rfl⟩ : syracuseStep 611015 = 916523) B916523
theorem B414407 : Blo 405769 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B5952211 : Blo 405769 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B611177 : Blo 405769 611177 := bstep (se 2 (by rfl) ⟨229191, by rfl⟩ : syracuseStep 611177 = 458383) B458383
theorem B807841 : Blo 405769 807841 := bstep (se 2 (by rfl) ⟨302940, by rfl⟩ : syracuseStep 807841 = 605881) B605881
theorem B611255 : Blo 405769 611255 := bstep (se 1 (by rfl) ⟨458441, by rfl⟩ : syracuseStep 611255 = 916883) B916883
theorem B611291 : Blo 405769 611291 := bstep (se 1 (by rfl) ⟨458468, by rfl⟩ : syracuseStep 611291 = 916937) B916937
theorem B611759 : Blo 405769 611759 := bstep (se 1 (by rfl) ⟨458819, by rfl⟩ : syracuseStep 611759 = 917639) B917639
theorem B611849 : Blo 405769 611849 := bstep (se 2 (by rfl) ⟨229443, by rfl⟩ : syracuseStep 611849 = 458887) B458887
theorem B611879 : Blo 405769 611879 := bstep (se 1 (by rfl) ⟨458909, by rfl⟩ : syracuseStep 611879 = 917819) B917819
theorem B611963 : Blo 405769 611963 := bstep (se 1 (by rfl) ⟨458972, by rfl⟩ : syracuseStep 611963 = 917945) B917945
theorem B612089 : Blo 405769 612089 := bstep (se 2 (by rfl) ⟨229533, by rfl⟩ : syracuseStep 612089 = 459067) B459067
theorem B612191 : Blo 405769 612191 := bstep (se 1 (by rfl) ⟨459143, by rfl⟩ : syracuseStep 612191 = 918287) B918287
theorem B612203 : Blo 405769 612203 := bstep (se 1 (by rfl) ⟨459152, by rfl⟩ : syracuseStep 612203 = 918305) B918305
theorem B1300411 : Blo 405769 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B1955771 : Blo 405769 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B514127 : Blo 405769 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B612431 : Blo 405769 612431 := bstep (se 1 (by rfl) ⟨459323, by rfl⟩ : syracuseStep 612431 = 918647) B918647
theorem B612551 : Blo 405769 612551 := bstep (se 1 (by rfl) ⟨459413, by rfl⟩ : syracuseStep 612551 = 918827) B918827
theorem B5855489 : Blo 405769 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B11163905 : Blo 405769 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B3496193 : Blo 405769 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B612713 : Blo 405769 612713 := bstep (se 2 (by rfl) ⟨229767, by rfl⟩ : syracuseStep 612713 = 459535) B459535
theorem B3103109 : Blo 405769 3103109 := bstep (se 4 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 3103109 = 581833) B581833
theorem B612791 : Blo 405769 612791 := bstep (se 1 (by rfl) ⟨459593, by rfl⟩ : syracuseStep 612791 = 919187) B919187
theorem B612827 : Blo 405769 612827 := bstep (se 1 (by rfl) ⟨459620, by rfl⟩ : syracuseStep 612827 = 919241) B919241
theorem B23943755 : Blo 405769 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B2611997 : Blo 405769 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B3103595 : Blo 405769 3103595 := bstep (se 1 (by rfl) ⟨2327696, by rfl⟩ : syracuseStep 3103595 = 4655393) B4655393
theorem B4643729 : Blo 405769 4643729 := bstep (se 2 (by rfl) ⟨1741398, by rfl⟩ : syracuseStep 4643729 = 3482797) B3482797
theorem B613295 : Blo 405769 613295 := bstep (se 1 (by rfl) ⟨459971, by rfl⟩ : syracuseStep 613295 = 919943) B919943
theorem B613385 : Blo 405769 613385 := bstep (se 2 (by rfl) ⟨230019, by rfl⟩ : syracuseStep 613385 = 460039) B460039
theorem B613415 : Blo 405769 613415 := bstep (se 1 (by rfl) ⟨460061, by rfl⟩ : syracuseStep 613415 = 920123) B920123
theorem B8805455 : Blo 405769 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B613499 : Blo 405769 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B613625 : Blo 405769 613625 := bstep (se 2 (by rfl) ⟨230109, by rfl⟩ : syracuseStep 613625 = 460219) B460219
theorem B1301771 : Blo 405769 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B515423 : Blo 405769 515423 := bstep (se 1 (by rfl) ⟨386567, by rfl⟩ : syracuseStep 515423 = 773135) B773135
theorem B613727 : Blo 405769 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B613739 : Blo 405769 613739 := bstep (se 1 (by rfl) ⟨460304, by rfl⟩ : syracuseStep 613739 = 920609) B920609
theorem B777691 : Blo 405769 777691 := bstep (se 1 (by rfl) ⟨583268, by rfl⟩ : syracuseStep 777691 = 1166537) B1166537
theorem B777737 : Blo 405769 777737 := bstep (se 2 (by rfl) ⟨291651, by rfl⟩ : syracuseStep 777737 = 583303) B583303
theorem B613967 : Blo 405769 613967 := bstep (se 1 (by rfl) ⟨460475, by rfl⟩ : syracuseStep 613967 = 920951) B920951
theorem B614087 : Blo 405769 614087 := bstep (se 1 (by rfl) ⟨460565, by rfl⟩ : syracuseStep 614087 = 921131) B921131
theorem B1236809 : Blo 405769 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B614249 : Blo 405769 614249 := bstep (se 2 (by rfl) ⟨230343, by rfl⟩ : syracuseStep 614249 = 460687) B460687
theorem B614327 : Blo 405769 614327 := bstep (se 1 (by rfl) ⟨460745, by rfl⟩ : syracuseStep 614327 = 921491) B921491
theorem B614363 : Blo 405769 614363 := bstep (se 1 (by rfl) ⟨460772, by rfl⟩ : syracuseStep 614363 = 921545) B921545
theorem B2613329 : Blo 405769 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B975385 : Blo 405769 975385 := bstep (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) B731539
theorem B746081 : Blo 405769 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B549499 : Blo 405769 549499 := bstep (se 1 (by rfl) ⟨412124, by rfl⟩ : syracuseStep 549499 = 824249) B824249
theorem B2056913 : Blo 405769 2056913 := bstep (se 2 (by rfl) ⟨771342, by rfl⟩ : syracuseStep 2056913 = 1542685) B1542685
theorem B3105539 : Blo 405769 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B583291 : Blo 405769 583291 := bstep (se 1 (by rfl) ⟨437468, by rfl⟩ : syracuseStep 583291 = 874937) B874937
theorem B1959673 : Blo 405769 1959673 := bstep (se 2 (by rfl) ⟨734877, by rfl⟩ : syracuseStep 1959673 = 1469755) B1469755
theorem B518071 : Blo 405769 518071 := bstep (se 1 (by rfl) ⟨388553, by rfl⟩ : syracuseStep 518071 = 777107) B777107
theorem B6383717 : Blo 405769 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B6678937 : Blo 405769 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B2779595 : Blo 405769 2779595 := bstep (se 1 (by rfl) ⟨2084696, by rfl⟩ : syracuseStep 2779595 = 4169393) B4169393
theorem B2615789 : Blo 405769 2615789 := bstep (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) B980921
theorem B5204513 : Blo 405769 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B1468961 : Blo 405769 1468961 := bstep (se 2 (by rfl) ⟨550860, by rfl⟩ : syracuseStep 1468961 = 1101721) B1101721
theorem B2550635 : Blo 405769 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B2059343 : Blo 405769 2059343 := bstep (se 1 (by rfl) ⟨1544507, by rfl⟩ : syracuseStep 2059343 = 3089015) B3089015
theorem B977999 : Blo 405769 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B650411 : Blo 405769 650411 := bstep (se 1 (by rfl) ⟨487808, by rfl⟩ : syracuseStep 650411 = 975617) B975617
theorem B1371383 : Blo 405769 1371383 := bstep (se 1 (by rfl) ⟨1028537, by rfl⟩ : syracuseStep 1371383 = 2057075) B2057075
theorem B1961459 : Blo 405769 1961459 := bstep (se 1 (by rfl) ⟨1471094, by rfl⟩ : syracuseStep 1961459 = 2942189) B2942189
theorem B1371707 : Blo 405769 1371707 := bstep (se 1 (by rfl) ⟨1028780, by rfl⟩ : syracuseStep 1371707 = 2057561) B2057561
theorem B1961671 : Blo 405769 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B2059991 : Blo 405769 2059991 := bstep (se 1 (by rfl) ⟨1544993, by rfl⟩ : syracuseStep 2059991 = 3089987) B3089987
theorem B1371977 : Blo 405769 1371977 := bstep (se 2 (by rfl) ⟨514491, by rfl⟩ : syracuseStep 1371977 = 1028983) B1028983
theorem B913247 : Blo 405769 913247 := bstep (se 1 (by rfl) ⟨684935, by rfl⟩ : syracuseStep 913247 = 1369871) B1369871
theorem B17592227 : Blo 405769 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B1961921 : Blo 405769 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B913427 : Blo 405769 913427 := bstep (se 1 (by rfl) ⟨685070, by rfl⟩ : syracuseStep 913427 = 1370141) B1370141
theorem B3108941 : Blo 405769 3108941 := bstep (se 3 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 3108941 = 1165853) B1165853
theorem B1962073 : Blo 405769 1962073 := bstep (se 2 (by rfl) ⟨735777, by rfl⟩ : syracuseStep 1962073 = 1471555) B1471555
theorem B45674675 : Blo 405769 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B618745 : Blo 405769 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B913769 : Blo 405769 913769 := bstep (se 2 (by rfl) ⟨342663, by rfl⟩ : syracuseStep 913769 = 685327) B685327
theorem B2945821 : Blo 405769 2945821 := bstep (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) B1104683
theorem B684895 : Blo 405769 684895 := bstep (se 1 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 684895 = 1027343) B1027343
theorem B684983 : Blo 405769 684983 := bstep (se 1 (by rfl) ⟨513737, by rfl⟩ : syracuseStep 684983 = 1027475) B1027475
theorem B1373111 : Blo 405769 1373111 := bstep (se 1 (by rfl) ⟨1029833, by rfl⟩ : syracuseStep 1373111 = 2059667) B2059667
theorem B914363 : Blo 405769 914363 := bstep (se 1 (by rfl) ⟨685772, by rfl⟩ : syracuseStep 914363 = 1371545) B1371545
theorem B914489 : Blo 405769 914489 := bstep (se 2 (by rfl) ⟨342933, by rfl⟩ : syracuseStep 914489 = 685867) B685867
theorem B1307819 : Blo 405769 1307819 := bstep (se 1 (by rfl) ⟨980864, by rfl⟩ : syracuseStep 1307819 = 1961729) B1961729
theorem B423263 : Blo 405769 423263 := bstep (se 1 (by rfl) ⟨317447, by rfl⟩ : syracuseStep 423263 = 634895) B634895
theorem B914831 : Blo 405769 914831 := bstep (se 1 (by rfl) ⟨686123, by rfl⟩ : syracuseStep 914831 = 1372247) B1372247
theorem B685577 : Blo 405769 685577 := bstep (se 2 (by rfl) ⟨257091, by rfl⟩ : syracuseStep 685577 = 514183) B514183
theorem B1373705 : Blo 405769 1373705 := bstep (se 2 (by rfl) ⟨515139, by rfl⟩ : syracuseStep 1373705 = 1030279) B1030279
theorem B685739 : Blo 405769 685739 := bstep (se 1 (by rfl) ⟨514304, by rfl⟩ : syracuseStep 685739 = 1028609) B1028609
theorem B915155 : Blo 405769 915155 := bstep (se 1 (by rfl) ⟨686366, by rfl⟩ : syracuseStep 915155 = 1372733) B1372733
theorem B653275 : Blo 405769 653275 := bstep (se 1 (by rfl) ⟨489956, by rfl⟩ : syracuseStep 653275 = 979913) B979913
theorem B686137 : Blo 405769 686137 := bstep (se 2 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 686137 = 514603) B514603
theorem B653435 : Blo 405769 653435 := bstep (se 1 (by rfl) ⟨490076, by rfl⟩ : syracuseStep 653435 = 980153) B980153
theorem B1964189 : Blo 405769 1964189 := bstep (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) B736571
theorem B686279 : Blo 405769 686279 := bstep (se 1 (by rfl) ⟨514709, by rfl⟩ : syracuseStep 686279 = 1029419) B1029419
theorem B686441 : Blo 405769 686441 := bstep (se 2 (by rfl) ⟨257415, by rfl⟩ : syracuseStep 686441 = 514831) B514831
theorem B1374569 : Blo 405769 1374569 := bstep (se 2 (by rfl) ⟨515463, by rfl⟩ : syracuseStep 1374569 = 1030927) B1030927
theorem B3111371 : Blo 405769 3111371 := bstep (se 1 (by rfl) ⟨2333528, by rfl⟩ : syracuseStep 3111371 = 4667057) B4667057
theorem B2062907 : Blo 405769 2062907 := bstep (se 1 (by rfl) ⟨1547180, by rfl⟩ : syracuseStep 2062907 = 3094361) B3094361
theorem B457339 : Blo 405769 457339 := bstep (se 1 (by rfl) ⟨343004, by rfl⟩ : syracuseStep 457339 = 686009) B686009
theorem B916091 : Blo 405769 916091 := bstep (se 1 (by rfl) ⟨687068, by rfl⟩ : syracuseStep 916091 = 1374137) B1374137
theorem B621179 : Blo 405769 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B10418867 : Blo 405769 10418867 := bstep (se 1 (by rfl) ⟨7814150, by rfl⟩ : syracuseStep 10418867 = 15628301) B15628301
theorem B686839 : Blo 405769 686839 := bstep (se 1 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 686839 = 1030259) B1030259
theorem B916217 : Blo 405769 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B1309535 : Blo 405769 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B1178551 : Blo 405769 1178551 := bstep (se 1 (by rfl) ⟨883913, by rfl⟩ : syracuseStep 1178551 = 1767827) B1767827
theorem B687035 : Blo 405769 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B1375163 : Blo 405769 1375163 := bstep (se 1 (by rfl) ⟨1031372, by rfl⟩ : syracuseStep 1375163 = 2062745) B2062745
theorem B2948069 : Blo 405769 2948069 := bstep (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) B552763
theorem B916487 : Blo 405769 916487 := bstep (se 1 (by rfl) ⟨687365, by rfl⟩ : syracuseStep 916487 = 1374731) B1374731
theorem B687143 : Blo 405769 687143 := bstep (se 1 (by rfl) ⟨515357, by rfl⟩ : syracuseStep 687143 = 1030715) B1030715
theorem B457807 : Blo 405769 457807 := bstep (se 1 (by rfl) ⟨343355, by rfl⟩ : syracuseStep 457807 = 686711) B686711
theorem B916559 : Blo 405769 916559 := bstep (se 1 (by rfl) ⟨687419, by rfl⟩ : syracuseStep 916559 = 1374839) B1374839
theorem B1473689 : Blo 405769 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B2063555 : Blo 405769 2063555 := bstep (se 1 (by rfl) ⟨1547666, by rfl⟩ : syracuseStep 2063555 = 3095333) B3095333
theorem B687433 : Blo 405769 687433 := bstep (se 2 (by rfl) ⟨257787, by rfl⟩ : syracuseStep 687433 = 515575) B515575
theorem B687467 : Blo 405769 687467 := bstep (se 1 (by rfl) ⟨515600, by rfl⟩ : syracuseStep 687467 = 1031201) B1031201
theorem B458203 : Blo 405769 458203 := bstep (se 1 (by rfl) ⟨343652, by rfl⟩ : syracuseStep 458203 = 687305) B687305
theorem B916955 : Blo 405769 916955 := bstep (se 1 (by rfl) ⟨687716, by rfl⟩ : syracuseStep 916955 = 1375433) B1375433
theorem B1342985 : Blo 405769 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B2981509 : Blo 405769 2981509 := bstep (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) B559033
theorem B687865 : Blo 405769 687865 := bstep (se 2 (by rfl) ⟨257949, by rfl⟩ : syracuseStep 687865 = 515899) B515899
theorem B1048393 : Blo 405769 1048393 := bstep (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) B786295
theorem B458671 : Blo 405769 458671 := bstep (se 1 (by rfl) ⟨344003, by rfl⟩ : syracuseStep 458671 = 688007) B688007
theorem B917423 : Blo 405769 917423 := bstep (se 1 (by rfl) ⟨688067, by rfl⟩ : syracuseStep 917423 = 1376135) B1376135
theorem B1310651 : Blo 405769 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B917513 : Blo 405769 917513 := bstep (se 2 (by rfl) ⟨344067, by rfl⟩ : syracuseStep 917513 = 688135) B688135
theorem B917927 : Blo 405769 917927 := bstep (se 1 (by rfl) ⟨688445, by rfl⟩ : syracuseStep 917927 = 1376891) B1376891
theorem B459175 : Blo 405769 459175 := bstep (se 1 (by rfl) ⟨344381, by rfl⟩ : syracuseStep 459175 = 688763) B688763
theorem B3310091 : Blo 405769 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B918035 : Blo 405769 918035 := bstep (se 1 (by rfl) ⟨688526, by rfl⟩ : syracuseStep 918035 = 1377053) B1377053
theorem B918089 : Blo 405769 918089 := bstep (se 2 (by rfl) ⟨344283, by rfl⟩ : syracuseStep 918089 = 688567) B688567
theorem B5505671 : Blo 405769 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B1966763 : Blo 405769 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B656095 : Blo 405769 656095 := bstep (se 1 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 656095 = 984143) B984143
theorem B5604173 : Blo 405769 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B3474323 : Blo 405769 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B918503 : Blo 405769 918503 := bstep (se 1 (by rfl) ⟨688877, by rfl⟩ : syracuseStep 918503 = 1377755) B1377755
theorem B459751 : Blo 405769 459751 := bstep (se 1 (by rfl) ⟨344813, by rfl⟩ : syracuseStep 459751 = 689627) B689627
theorem B1377377 : Blo 405769 1377377 := bstep (se 2 (by rfl) ⟨516516, by rfl⟩ : syracuseStep 1377377 = 1033033) B1033033
theorem B918881 : Blo 405769 918881 := bstep (se 2 (by rfl) ⟨344580, by rfl⟩ : syracuseStep 918881 = 689161) B689161
theorem B918971 : Blo 405769 918971 := bstep (se 1 (by rfl) ⟨689228, by rfl⟩ : syracuseStep 918971 = 1378457) B1378457
theorem B7865819 : Blo 405769 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B3933683 : Blo 405769 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B919097 : Blo 405769 919097 := bstep (se 2 (by rfl) ⟨344661, by rfl⟩ : syracuseStep 919097 = 689323) B689323
theorem B1476559 : Blo 405769 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B6424771 : Blo 405769 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B919763 : Blo 405769 919763 := bstep (se 1 (by rfl) ⟨689822, by rfl⟩ : syracuseStep 919763 = 1379645) B1379645
theorem B919817 : Blo 405769 919817 := bstep (se 2 (by rfl) ⟨344931, by rfl⟩ : syracuseStep 919817 = 689863) B689863
theorem B1378727 : Blo 405769 1378727 := bstep (se 1 (by rfl) ⟨1034045, by rfl⟩ : syracuseStep 1378727 = 2068091) B2068091
theorem B690599 : Blo 405769 690599 := bstep (se 1 (by rfl) ⟨517949, by rfl⟩ : syracuseStep 690599 = 1035899) B1035899
theorem B920033 : Blo 405769 920033 := bstep (se 2 (by rfl) ⟨345012, by rfl⟩ : syracuseStep 920033 = 690025) B690025
theorem B1378889 : Blo 405769 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B690761 : Blo 405769 690761 := bstep (se 2 (by rfl) ⟨259035, by rfl⟩ : syracuseStep 690761 = 518071) B518071
theorem B2067119 : Blo 405769 2067119 := bstep (se 1 (by rfl) ⟨1550339, by rfl⟩ : syracuseStep 2067119 = 3100679) B3100679
theorem B1116919 : Blo 405769 1116919 := bstep (se 1 (by rfl) ⟨837689, by rfl⟩ : syracuseStep 1116919 = 1675379) B1675379
theorem B920339 : Blo 405769 920339 := bstep (se 1 (by rfl) ⟨690254, by rfl⟩ : syracuseStep 920339 = 1380509) B1380509
theorem B2198339 : Blo 405769 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B2067443 : Blo 405769 2067443 := bstep (se 1 (by rfl) ⟨1550582, by rfl⟩ : syracuseStep 2067443 = 3101165) B3101165
theorem B920699 : Blo 405769 920699 := bstep (se 1 (by rfl) ⟨690524, by rfl⟩ : syracuseStep 920699 = 1381049) B1381049
theorem B920825 : Blo 405769 920825 := bstep (se 2 (by rfl) ⟨345309, by rfl⟩ : syracuseStep 920825 = 690619) B690619
theorem B920969 : Blo 405769 920969 := bstep (se 2 (by rfl) ⟨345363, by rfl⟩ : syracuseStep 920969 = 690727) B690727
theorem B921095 : Blo 405769 921095 := bstep (se 1 (by rfl) ⟨690821, by rfl⟩ : syracuseStep 921095 = 1381643) B1381643
theorem B921275 : Blo 405769 921275 := bstep (se 1 (by rfl) ⟨690956, by rfl⟩ : syracuseStep 921275 = 1381913) B1381913
theorem B4656851 : Blo 405769 4656851 := bstep (se 1 (by rfl) ⟨3492638, by rfl⟩ : syracuseStep 4656851 = 6985277) B6985277
theorem B921401 : Blo 405769 921401 := bstep (se 2 (by rfl) ⟨345525, by rfl⟩ : syracuseStep 921401 = 691051) B691051
theorem B3903659 : Blo 405769 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B7442603 : Blo 405769 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B2330795 : Blo 405769 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B1380563 : Blo 405769 1380563 := bstep (se 1 (by rfl) ⟨1035422, by rfl⟩ : syracuseStep 1380563 = 2070845) B2070845
theorem B2068739 : Blo 405769 2068739 := bstep (se 1 (by rfl) ⟨1551554, by rfl⟩ : syracuseStep 2068739 = 3103109) B3103109
theorem B15962503 : Blo 405769 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B1380833 : Blo 405769 1380833 := bstep (se 2 (by rfl) ⟨517812, by rfl⟩ : syracuseStep 1380833 = 1035625) B1035625
theorem B1741331 : Blo 405769 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B2069063 : Blo 405769 2069063 := bstep (se 1 (by rfl) ⟨1551797, by rfl⟩ : syracuseStep 2069063 = 3103595) B3103595
theorem B5870303 : Blo 405769 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B8852429 : Blo 405769 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B1742219 : Blo 405769 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B4396589 : Blo 405769 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B824993 : Blo 405769 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B1382075 : Blo 405769 1382075 := bstep (se 1 (by rfl) ⟨1036556, by rfl⟩ : syracuseStep 1382075 = 2073113) B2073113
theorem B497387 : Blo 405769 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B2070359 : Blo 405769 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B2234735 : Blo 405769 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B531355 : Blo 405769 531355 := bstep (se 1 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 531355 = 797033) B797033
theorem B1743859 : Blo 405769 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B466267 : Blo 405769 466267 := bstep (se 1 (by rfl) ⟨349700, by rfl⟩ : syracuseStep 466267 = 699401) B699401
theorem B1023329 : Blo 405769 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B433607 : Blo 405769 433607 := bstep (se 1 (by rfl) ⟨325205, by rfl⟩ : syracuseStep 433607 = 650411) B650411
theorem B4169465 : Blo 405769 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B2072627 : Blo 405769 2072627 := bstep (se 1 (by rfl) ⟨1554470, by rfl⟩ : syracuseStep 2072627 = 3108941) B3108941
theorem B30449783 : Blo 405769 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B15901381 : Blo 405769 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B17703629 : Blo 405769 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B3351851 : Blo 405769 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B3581293 : Blo 405769 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B1156513 : Blo 405769 1156513 := bstep (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) B867385
theorem B435623 : Blo 405769 435623 := bstep (se 1 (by rfl) ⟨326717, by rfl⟩ : syracuseStep 435623 = 653435) B653435
theorem B2074247 : Blo 405769 2074247 := bstep (se 1 (by rfl) ⟨1555685, by rfl⟩ : syracuseStep 2074247 = 3111371) B3111371
theorem B4171601 : Blo 405769 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B3909809 : Blo 405769 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B2205949 : Blo 405769 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B3484133 : Blo 405769 3484133 := bstep (se 4 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 3484133 = 653275) B653275
theorem B1158131 : Blo 405769 1158131 := bstep (se 1 (by rfl) ⟨868598, by rfl⟩ : syracuseStep 1158131 = 1737197) B1737197
theorem B5024987 : Blo 405769 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B2928001 : Blo 405769 2928001 := bstep (se 2 (by rfl) ⟨1098000, by rfl⟩ : syracuseStep 2928001 = 2196001) B2196001
theorem B1158587 : Blo 405769 1158587 := bstep (se 1 (by rfl) ⟨868940, by rfl⟩ : syracuseStep 1158587 = 1737881) B1737881
theorem B10431989 : Blo 405769 10431989 := bstep (se 5 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 10431989 = 977999) B977999
theorem B732665 : Blo 405769 732665 := bstep (se 2 (by rfl) ⟨274749, by rfl⟩ : syracuseStep 732665 = 549499) B549499
theorem B1027667 : Blo 405769 1027667 := bstep (se 1 (by rfl) ⟨770750, by rfl⟩ : syracuseStep 1027667 = 1541501) B1541501
theorem B7876277 : Blo 405769 7876277 := bstep (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) B738401
theorem B6959033 : Blo 405769 6959033 := bstep (se 2 (by rfl) ⟨2609637, by rfl⟩ : syracuseStep 6959033 = 5219275) B5219275
theorem B7450555 : Blo 405769 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B405791 : Blo 405769 405791 := bstep (se 1 (by rfl) ⟨304343, by rfl⟩ : syracuseStep 405791 = 608687) B608687
theorem B405851 : Blo 405769 405851 := bstep (se 1 (by rfl) ⟨304388, by rfl⟩ : syracuseStep 405851 = 608777) B608777
theorem B405871 : Blo 405769 405871 := bstep (se 1 (by rfl) ⟨304403, by rfl⟩ : syracuseStep 405871 = 608807) B608807
theorem B405927 : Blo 405769 405927 := bstep (se 1 (by rfl) ⟨304445, by rfl⟩ : syracuseStep 405927 = 608891) B608891
theorem B406011 : Blo 405769 406011 := bstep (se 1 (by rfl) ⟨304508, by rfl⟩ : syracuseStep 406011 = 609017) B609017
theorem B2929213 : Blo 405769 2929213 := bstep (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) B1098455
theorem B406079 : Blo 405769 406079 := bstep (se 1 (by rfl) ⟨304559, by rfl⟩ : syracuseStep 406079 = 609119) B609119
theorem B406087 : Blo 405769 406087 := bstep (se 1 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 406087 = 609131) B609131
theorem B406239 : Blo 405769 406239 := bstep (se 1 (by rfl) ⟨304679, by rfl⟩ : syracuseStep 406239 = 609359) B609359
theorem B406319 : Blo 405769 406319 := bstep (se 1 (by rfl) ⟨304739, by rfl⟩ : syracuseStep 406319 = 609479) B609479
theorem B406427 : Blo 405769 406427 := bstep (se 1 (by rfl) ⟨304820, by rfl⟩ : syracuseStep 406427 = 609641) B609641
theorem B406479 : Blo 405769 406479 := bstep (se 1 (by rfl) ⟨304859, by rfl⟩ : syracuseStep 406479 = 609719) B609719
theorem B406503 : Blo 405769 406503 := bstep (se 1 (by rfl) ⟨304877, by rfl⟩ : syracuseStep 406503 = 609755) B609755
theorem B1029095 : Blo 405769 1029095 := bstep (se 1 (by rfl) ⟨771821, by rfl⟩ : syracuseStep 1029095 = 1543643) B1543643
theorem B1553651 : Blo 405769 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B406815 : Blo 405769 406815 := bstep (se 1 (by rfl) ⟨305111, by rfl⟩ : syracuseStep 406815 = 610223) B610223
theorem B406875 : Blo 405769 406875 := bstep (se 1 (by rfl) ⟨305156, by rfl⟩ : syracuseStep 406875 = 610313) B610313
theorem B406895 : Blo 405769 406895 := bstep (se 1 (by rfl) ⟨305171, by rfl⟩ : syracuseStep 406895 = 610343) B610343
theorem B406951 : Blo 405769 406951 := bstep (se 1 (by rfl) ⟨305213, by rfl⟩ : syracuseStep 406951 = 610427) B610427
theorem B407035 : Blo 405769 407035 := bstep (se 1 (by rfl) ⟨305276, by rfl⟩ : syracuseStep 407035 = 610553) B610553
theorem B407103 : Blo 405769 407103 := bstep (se 1 (by rfl) ⟨305327, by rfl⟩ : syracuseStep 407103 = 610655) B610655
theorem B407111 : Blo 405769 407111 := bstep (se 1 (by rfl) ⟨305333, by rfl⟩ : syracuseStep 407111 = 610667) B610667
theorem B1029793 : Blo 405769 1029793 := bstep (se 2 (by rfl) ⟨386172, by rfl⟩ : syracuseStep 1029793 = 772345) B772345
theorem B407263 : Blo 405769 407263 := bstep (se 1 (by rfl) ⟨305447, by rfl⟩ : syracuseStep 407263 = 610895) B610895
theorem B1029935 : Blo 405769 1029935 := bstep (se 1 (by rfl) ⟨772451, by rfl⟩ : syracuseStep 1029935 = 1544903) B1544903
theorem B407343 : Blo 405769 407343 := bstep (se 1 (by rfl) ⟨305507, by rfl⟩ : syracuseStep 407343 = 611015) B611015
theorem B440143 : Blo 405769 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B407451 : Blo 405769 407451 := bstep (se 1 (by rfl) ⟨305588, by rfl⟩ : syracuseStep 407451 = 611177) B611177
theorem B407503 : Blo 405769 407503 := bstep (se 1 (by rfl) ⟨305627, by rfl⟩ : syracuseStep 407503 = 611255) B611255
theorem B407527 : Blo 405769 407527 := bstep (se 1 (by rfl) ⟨305645, by rfl⟩ : syracuseStep 407527 = 611291) B611291
theorem B1128701 : Blo 405769 1128701 := bstep (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) B423263
theorem B407839 : Blo 405769 407839 := bstep (se 1 (by rfl) ⟨305879, by rfl⟩ : syracuseStep 407839 = 611759) B611759
theorem B407899 : Blo 405769 407899 := bstep (se 1 (by rfl) ⟨305924, by rfl⟩ : syracuseStep 407899 = 611849) B611849
theorem B407919 : Blo 405769 407919 := bstep (se 1 (by rfl) ⟨305939, by rfl⟩ : syracuseStep 407919 = 611879) B611879
theorem B407975 : Blo 405769 407975 := bstep (se 1 (by rfl) ⟨305981, by rfl⟩ : syracuseStep 407975 = 611963) B611963
theorem B1030583 : Blo 405769 1030583 := bstep (se 1 (by rfl) ⟨772937, by rfl⟩ : syracuseStep 1030583 = 1545875) B1545875
theorem B408059 : Blo 405769 408059 := bstep (se 1 (by rfl) ⟨306044, by rfl⟩ : syracuseStep 408059 = 612089) B612089
theorem B408127 : Blo 405769 408127 := bstep (se 1 (by rfl) ⟨306095, by rfl⟩ : syracuseStep 408127 = 612191) B612191
theorem B408135 : Blo 405769 408135 := bstep (se 1 (by rfl) ⟨306101, by rfl⟩ : syracuseStep 408135 = 612203) B612203
theorem B2472643 : Blo 405769 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B1555139 : Blo 405769 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B408287 : Blo 405769 408287 := bstep (se 1 (by rfl) ⟨306215, by rfl⟩ : syracuseStep 408287 = 612431) B612431
theorem B408367 : Blo 405769 408367 := bstep (se 1 (by rfl) ⟨306275, by rfl⟩ : syracuseStep 408367 = 612551) B612551
theorem B408475 : Blo 405769 408475 := bstep (se 1 (by rfl) ⟨306356, by rfl⟩ : syracuseStep 408475 = 612713) B612713
theorem B408527 : Blo 405769 408527 := bstep (se 1 (by rfl) ⟨306395, by rfl⟩ : syracuseStep 408527 = 612791) B612791
theorem B408551 : Blo 405769 408551 := bstep (se 1 (by rfl) ⟨306413, by rfl⟩ : syracuseStep 408551 = 612827) B612827
theorem B1555595 : Blo 405769 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B3095819 : Blo 405769 3095819 := bstep (se 1 (by rfl) ⟨2321864, by rfl⟩ : syracuseStep 3095819 = 4643729) B4643729
theorem B408863 : Blo 405769 408863 := bstep (se 1 (by rfl) ⟨306647, by rfl⟩ : syracuseStep 408863 = 613295) B613295
theorem B408923 : Blo 405769 408923 := bstep (se 1 (by rfl) ⟨306692, by rfl⟩ : syracuseStep 408923 = 613385) B613385
theorem B408943 : Blo 405769 408943 := bstep (se 1 (by rfl) ⟨306707, by rfl⟩ : syracuseStep 408943 = 613415) B613415
theorem B408999 : Blo 405769 408999 := bstep (se 1 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 408999 = 613499) B613499
theorem B1162745 : Blo 405769 1162745 := bstep (se 2 (by rfl) ⟨436029, by rfl⟩ : syracuseStep 1162745 = 872059) B872059
theorem B409083 : Blo 405769 409083 := bstep (se 1 (by rfl) ⟨306812, by rfl⟩ : syracuseStep 409083 = 613625) B613625
theorem B867847 : Blo 405769 867847 := bstep (se 1 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 867847 = 1301771) B1301771
theorem B1031687 : Blo 405769 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B1031737 : Blo 405769 1031737 := bstep (se 2 (by rfl) ⟨386901, by rfl⟩ : syracuseStep 1031737 = 773803) B773803
theorem B409151 : Blo 405769 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B409159 : Blo 405769 409159 := bstep (se 1 (by rfl) ⟨306869, by rfl⟩ : syracuseStep 409159 = 613739) B613739
theorem B409311 : Blo 405769 409311 := bstep (se 1 (by rfl) ⟨306983, by rfl⟩ : syracuseStep 409311 = 613967) B613967
theorem B2801411 : Blo 405769 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B409391 : Blo 405769 409391 := bstep (se 1 (by rfl) ⟨307043, by rfl⟩ : syracuseStep 409391 = 614087) B614087
theorem B1032041 : Blo 405769 1032041 := bstep (se 2 (by rfl) ⟨387015, by rfl⟩ : syracuseStep 1032041 = 774031) B774031
theorem B409499 : Blo 405769 409499 := bstep (se 1 (by rfl) ⟨307124, by rfl⟩ : syracuseStep 409499 = 614249) B614249
theorem B409551 : Blo 405769 409551 := bstep (se 1 (by rfl) ⟨307163, by rfl⟩ : syracuseStep 409551 = 614327) B614327
theorem B409575 : Blo 405769 409575 := bstep (se 1 (by rfl) ⟨307181, by rfl⟩ : syracuseStep 409575 = 614363) B614363
theorem B1032659 : Blo 405769 1032659 := bstep (se 1 (by rfl) ⟨774494, by rfl⟩ : syracuseStep 1032659 = 1548989) B1548989
theorem B2605537 : Blo 405769 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B770735 : Blo 405769 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B770971 : Blo 405769 770971 := bstep (se 1 (by rfl) ⟨578228, by rfl⟩ : syracuseStep 770971 = 1156457) B1156457
theorem B1033823 : Blo 405769 1033823 := bstep (se 1 (by rfl) ⟨775367, by rfl⟩ : syracuseStep 1033823 = 1550735) B1550735
theorem B1853063 : Blo 405769 1853063 := bstep (se 1 (by rfl) ⟨1389797, by rfl⟩ : syracuseStep 1853063 = 2779595) B2779595
theorem B509743 : Blo 405769 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B13289669 : Blo 405769 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B1034603 : Blo 405769 1034603 := bstep (se 1 (by rfl) ⟨775952, by rfl⟩ : syracuseStep 1034603 = 1551905) B1551905
theorem B7096805 : Blo 405769 7096805 := bstep (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) B1330651
theorem B608831 : Blo 405769 608831 := bstep (se 1 (by rfl) ⟨456623, by rfl⟩ : syracuseStep 608831 = 913247) B913247
theorem B1034815 : Blo 405769 1034815 := bstep (se 1 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 1034815 = 1552223) B1552223
theorem B772679 : Blo 405769 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B1034927 : Blo 405769 1034927 := bstep (se 1 (by rfl) ⟨776195, by rfl⟩ : syracuseStep 1034927 = 1552391) B1552391
theorem B608951 : Blo 405769 608951 := bstep (se 1 (by rfl) ⟨456713, by rfl⟩ : syracuseStep 608951 = 913427) B913427
theorem B772831 : Blo 405769 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B5655329 : Blo 405769 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B7457629 : Blo 405769 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B609179 : Blo 405769 609179 := bstep (se 1 (by rfl) ⟨456884, by rfl⟩ : syracuseStep 609179 = 913769) B913769
theorem B1035251 : Blo 405769 1035251 := bstep (se 1 (by rfl) ⟨776438, by rfl⟩ : syracuseStep 1035251 = 1552877) B1552877
theorem B1035463 : Blo 405769 1035463 := bstep (se 1 (by rfl) ⟨776597, by rfl⟩ : syracuseStep 1035463 = 1553195) B1553195
theorem B609575 : Blo 405769 609575 := bstep (se 1 (by rfl) ⟨457181, by rfl⟩ : syracuseStep 609575 = 914363) B914363
theorem B609659 : Blo 405769 609659 := bstep (se 1 (by rfl) ⟨457244, by rfl⟩ : syracuseStep 609659 = 914489) B914489
theorem B871879 : Blo 405769 871879 := bstep (se 1 (by rfl) ⟨653909, by rfl⟩ : syracuseStep 871879 = 1307819) B1307819
theorem B609785 : Blo 405769 609785 := bstep (se 2 (by rfl) ⟨228669, by rfl⟩ : syracuseStep 609785 = 457339) B457339
theorem B609887 : Blo 405769 609887 := bstep (se 1 (by rfl) ⟨457415, by rfl⟩ : syracuseStep 609887 = 914831) B914831
theorem B2477803 : Blo 405769 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B610103 : Blo 405769 610103 := bstep (se 1 (by rfl) ⟨457577, by rfl⟩ : syracuseStep 610103 = 915155) B915155
theorem B610409 : Blo 405769 610409 := bstep (se 2 (by rfl) ⟨228903, by rfl⟩ : syracuseStep 610409 = 457807) B457807
theorem B3920075 : Blo 405769 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B125751523 : Blo 405769 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B577801 : Blo 405769 577801 := bstep (se 2 (by rfl) ⟨216675, by rfl⟩ : syracuseStep 577801 = 433351) B433351
theorem B5591429 : Blo 405769 5591429 := bstep (se 4 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 5591429 = 1048393) B1048393
theorem B610727 : Blo 405769 610727 := bstep (se 1 (by rfl) ⟨458045, by rfl⟩ : syracuseStep 610727 = 916091) B916091
theorem B414119 : Blo 405769 414119 := bstep (se 1 (by rfl) ⟨310589, by rfl⟩ : syracuseStep 414119 = 621179) B621179
theorem B610811 : Blo 405769 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B873023 : Blo 405769 873023 := bstep (se 1 (by rfl) ⟨654767, by rfl⟩ : syracuseStep 873023 = 1309535) B1309535
theorem B1036871 : Blo 405769 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B610937 : Blo 405769 610937 := bstep (se 2 (by rfl) ⟨229101, by rfl⟩ : syracuseStep 610937 = 458203) B458203
theorem B1036921 : Blo 405769 1036921 := bstep (se 2 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 1036921 = 777691) B777691
theorem B610991 : Blo 405769 610991 := bstep (se 1 (by rfl) ⟨458243, by rfl⟩ : syracuseStep 610991 = 916487) B916487
theorem B611039 : Blo 405769 611039 := bstep (se 1 (by rfl) ⟨458279, by rfl⟩ : syracuseStep 611039 = 916559) B916559
theorem B1954655 : Blo 405769 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B3298157 : Blo 405769 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B611303 : Blo 405769 611303 := bstep (se 1 (by rfl) ⟨458477, by rfl⟩ : syracuseStep 611303 = 916955) B916955
theorem B611561 : Blo 405769 611561 := bstep (se 2 (by rfl) ⟨229335, by rfl⟩ : syracuseStep 611561 = 458671) B458671
theorem B611615 : Blo 405769 611615 := bstep (se 1 (by rfl) ⟨458711, by rfl⟩ : syracuseStep 611615 = 917423) B917423
theorem B873767 : Blo 405769 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B7558505 : Blo 405769 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B611783 : Blo 405769 611783 := bstep (se 1 (by rfl) ⟨458837, by rfl⟩ : syracuseStep 611783 = 917675) B917675
theorem B513631 : Blo 405769 513631 := bstep (se 1 (by rfl) ⟨385223, by rfl⟩ : syracuseStep 513631 = 770447) B770447
theorem B1234619 : Blo 405769 1234619 := bstep (se 1 (by rfl) ⟨925964, by rfl⟩ : syracuseStep 1234619 = 1851929) B1851929
theorem B612137 : Blo 405769 612137 := bstep (se 2 (by rfl) ⟨229551, by rfl⟩ : syracuseStep 612137 = 459103) B459103
theorem B612143 : Blo 405769 612143 := bstep (se 1 (by rfl) ⟨459107, by rfl⟩ : syracuseStep 612143 = 918215) B918215
theorem B612617 : Blo 405769 612617 := bstep (se 2 (by rfl) ⟨229731, by rfl⟩ : syracuseStep 612617 = 459463) B459463
theorem B612719 : Blo 405769 612719 := bstep (se 1 (by rfl) ⟨459539, by rfl⟩ : syracuseStep 612719 = 919079) B919079
theorem B580159 : Blo 405769 580159 := bstep (se 1 (by rfl) ⟨435119, by rfl⟩ : syracuseStep 580159 = 870239) B870239
theorem B612935 : Blo 405769 612935 := bstep (se 1 (by rfl) ⟨459701, by rfl⟩ : syracuseStep 612935 = 919403) B919403
theorem B612971 : Blo 405769 612971 := bstep (se 1 (by rfl) ⟨459728, by rfl⟩ : syracuseStep 612971 = 919457) B919457
theorem B580279 : Blo 405769 580279 := bstep (se 1 (by rfl) ⟨435209, by rfl⟩ : syracuseStep 580279 = 870419) B870419
theorem B613199 : Blo 405769 613199 := bstep (se 1 (by rfl) ⟨459899, by rfl⟩ : syracuseStep 613199 = 919799) B919799
theorem B3496877 : Blo 405769 3496877 := bstep (se 3 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 3496877 = 1311329) B1311329
theorem B1105085 : Blo 405769 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B613595 : Blo 405769 613595 := bstep (se 1 (by rfl) ⟨460196, by rfl⟩ : syracuseStep 613595 = 920393) B920393
theorem B2055455 : Blo 405769 2055455 := bstep (se 1 (by rfl) ⟨1541591, by rfl⟩ : syracuseStep 2055455 = 3083183) B3083183
theorem B613769 : Blo 405769 613769 := bstep (se 2 (by rfl) ⟨230163, by rfl⟩ : syracuseStep 613769 = 460327) B460327
theorem B2612897 : Blo 405769 2612897 := bstep (se 2 (by rfl) ⟨979836, by rfl⟩ : syracuseStep 2612897 = 1959673) B1959673
theorem B614123 : Blo 405769 614123 := bstep (se 1 (by rfl) ⟨460592, by rfl⟩ : syracuseStep 614123 = 921185) B921185
theorem B581423 : Blo 405769 581423 := bstep (se 1 (by rfl) ⟨436067, by rfl⟩ : syracuseStep 581423 = 872135) B872135
theorem B79716149 : Blo 405769 79716149 := bstep (se 5 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 79716149 = 7473389) B7473389
theorem B3497903 : Blo 405769 3497903 := bstep (se 1 (by rfl) ⟨2623427, by rfl⟩ : syracuseStep 3497903 = 5246855) B5246855
theorem B614351 : Blo 405769 614351 := bstep (se 1 (by rfl) ⟨460763, by rfl⟩ : syracuseStep 614351 = 921527) B921527
theorem B516071 : Blo 405769 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B581737 : Blo 405769 581737 := bstep (se 2 (by rfl) ⟨218151, by rfl⟩ : syracuseStep 581737 = 436303) B436303
theorem B5202053 : Blo 405769 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B8905249 : Blo 405769 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B31745125 : Blo 405769 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B3302633 : Blo 405769 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B3106025 : Blo 405769 3106025 := bstep (se 2 (by rfl) ⟨1164759, by rfl⟩ : syracuseStep 3106025 = 2329519) B2329519
theorem B1303847 : Blo 405769 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B2057885 : Blo 405769 2057885 := bstep (se 3 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 2057885 = 771707) B771707
theorem B2615561 : Blo 405769 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B6285605 : Blo 405769 6285605 := bstep (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) B1178551
theorem B518491 : Blo 405769 518491 := bstep (se 1 (by rfl) ⟨388868, by rfl⟩ : syracuseStep 518491 = 777737) B777737
theorem B2616097 : Blo 405769 2616097 := bstep (se 2 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 2616097 = 1962073) B1962073
theorem B1371005 : Blo 405769 1371005 := bstep (se 3 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 1371005 = 514127) B514127
theorem B2059181 : Blo 405769 2059181 := bstep (se 3 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 2059181 = 772193) B772193
theorem B1371275 : Blo 405769 1371275 := bstep (se 1 (by rfl) ⟨1028456, by rfl⟩ : syracuseStep 1371275 = 2056913) B2056913
theorem B3927761 : Blo 405769 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B913193 : Blo 405769 913193 := bstep (se 2 (by rfl) ⟨342447, by rfl⟩ : syracuseStep 913193 = 684895) B684895
theorem B1077121 : Blo 405769 1077121 := bstep (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) B807841
theorem B4255811 : Blo 405769 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B3469675 : Blo 405769 3469675 := bstep (se 1 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 3469675 = 5204513) B5204513
theorem B979307 : Blo 405769 979307 := bstep (se 1 (by rfl) ⟨734480, by rfl⟩ : syracuseStep 979307 = 1468961) B1468961
theorem B2060801 : Blo 405769 2060801 := bstep (se 2 (by rfl) ⟨772800, by rfl⟩ : syracuseStep 2060801 = 1545601) B1545601
theorem B3109427 : Blo 405769 3109427 := bstep (se 1 (by rfl) ⟨2332070, by rfl⟩ : syracuseStep 3109427 = 4664141) B4664141
theorem B1700423 : Blo 405769 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B488111 : Blo 405769 488111 := bstep (se 1 (by rfl) ⟨366083, by rfl⟩ : syracuseStep 488111 = 732167) B732167
theorem B684767 : Blo 405769 684767 := bstep (se 1 (by rfl) ⟨513575, by rfl⟩ : syracuseStep 684767 = 1027151) B1027151
theorem B1372895 : Blo 405769 1372895 := bstep (se 1 (by rfl) ⟨1029671, by rfl⟩ : syracuseStep 1372895 = 2059343) B2059343
theorem B914255 : Blo 405769 914255 := bstep (se 1 (by rfl) ⟨685691, by rfl⟩ : syracuseStep 914255 = 1371383) B1371383
theorem B1733471 : Blo 405769 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B2061287 : Blo 405769 2061287 := bstep (se 1 (by rfl) ⟨1545965, by rfl⟩ : syracuseStep 2061287 = 3091931) B3091931
theorem B1307639 : Blo 405769 1307639 := bstep (se 1 (by rfl) ⟨980729, by rfl⟩ : syracuseStep 1307639 = 1961459) B1961459
theorem B914471 : Blo 405769 914471 := bstep (se 1 (by rfl) ⟨685853, by rfl⟩ : syracuseStep 914471 = 1371707) B1371707
theorem B685199 : Blo 405769 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B1373327 : Blo 405769 1373327 := bstep (se 1 (by rfl) ⟨1029995, by rfl⟩ : syracuseStep 1373327 = 2059991) B2059991
theorem B1995923 : Blo 405769 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B914651 : Blo 405769 914651 := bstep (se 1 (by rfl) ⟨685988, by rfl⟩ : syracuseStep 914651 = 1371977) B1371977
theorem B1733881 : Blo 405769 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B11728151 : Blo 405769 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B1307947 : Blo 405769 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B2061611 : Blo 405769 2061611 := bstep (se 1 (by rfl) ⟨1546208, by rfl⟩ : syracuseStep 2061611 = 3092417) B3092417
theorem B3306847 : Blo 405769 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B685435 : Blo 405769 685435 := bstep (se 1 (by rfl) ⟨514076, by rfl⟩ : syracuseStep 685435 = 1028153) B1028153
theorem B914849 : Blo 405769 914849 := bstep (se 2 (by rfl) ⟨343068, by rfl⟩ : syracuseStep 914849 = 686137) B686137
theorem B456655 : Blo 405769 456655 := bstep (se 1 (by rfl) ⟨342491, by rfl⟩ : syracuseStep 456655 = 684983) B684983
theorem B915407 : Blo 405769 915407 := bstep (se 1 (by rfl) ⟨686555, by rfl⟩ : syracuseStep 915407 = 1373111) B1373111
theorem B3110885 : Blo 405769 3110885 := bstep (se 4 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 3110885 = 583291) B583291
theorem B2062583 : Blo 405769 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B1374461 : Blo 405769 1374461 := bstep (se 3 (by rfl) ⟨257711, by rfl⟩ : syracuseStep 1374461 = 515423) B515423
theorem B915785 : Blo 405769 915785 := bstep (se 2 (by rfl) ⟨343419, by rfl⟩ : syracuseStep 915785 = 686839) B686839
theorem B457051 : Blo 405769 457051 := bstep (se 1 (by rfl) ⟨342788, by rfl⟩ : syracuseStep 457051 = 685577) B685577
theorem B915803 : Blo 405769 915803 := bstep (se 1 (by rfl) ⟨686852, by rfl⟩ : syracuseStep 915803 = 1373705) B1373705
theorem B457159 : Blo 405769 457159 := bstep (se 1 (by rfl) ⟨342869, by rfl⟩ : syracuseStep 457159 = 685739) B685739
theorem B2063069 : Blo 405769 2063069 := bstep (se 3 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 2063069 = 773651) B773651
theorem B1309459 : Blo 405769 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B457519 : Blo 405769 457519 := bstep (se 1 (by rfl) ⟨343139, by rfl⟩ : syracuseStep 457519 = 686279) B686279
theorem B686927 : Blo 405769 686927 := bstep (se 1 (by rfl) ⟨515195, by rfl⟩ : syracuseStep 686927 = 1030391) B1030391
theorem B457627 : Blo 405769 457627 := bstep (se 1 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 457627 = 686441) B686441
theorem B916379 : Blo 405769 916379 := bstep (se 1 (by rfl) ⟨687284, by rfl⟩ : syracuseStep 916379 = 1374569) B1374569
theorem B1375271 : Blo 405769 1375271 := bstep (se 1 (by rfl) ⟨1031453, by rfl⟩ : syracuseStep 1375271 = 2062907) B2062907
theorem B916577 : Blo 405769 916577 := bstep (se 2 (by rfl) ⟨343716, by rfl⟩ : syracuseStep 916577 = 687433) B687433
theorem B6945911 : Blo 405769 6945911 := bstep (se 1 (by rfl) ⟨5209433, by rfl⟩ : syracuseStep 6945911 = 10418867) B10418867
theorem B458023 : Blo 405769 458023 := bstep (se 1 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 458023 = 687035) B687035
theorem B916775 : Blo 405769 916775 := bstep (se 1 (by rfl) ⟨687581, by rfl⟩ : syracuseStep 916775 = 1375163) B1375163
theorem B1965379 : Blo 405769 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B458095 : Blo 405769 458095 := bstep (se 1 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 458095 = 687143) B687143
theorem B982459 : Blo 405769 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B1375703 : Blo 405769 1375703 := bstep (se 1 (by rfl) ⟨1031777, by rfl⟩ : syracuseStep 1375703 = 2063555) B2063555
theorem B458311 : Blo 405769 458311 := bstep (se 1 (by rfl) ⟨343733, by rfl⟩ : syracuseStep 458311 = 687467) B687467
theorem B917153 : Blo 405769 917153 := bstep (se 2 (by rfl) ⟨343932, by rfl⟩ : syracuseStep 917153 = 687865) B687865
theorem B687919 : Blo 405769 687919 := bstep (se 1 (by rfl) ⟨515939, by rfl⟩ : syracuseStep 687919 = 1031879) B1031879
theorem B2948993 : Blo 405769 2948993 := bstep (se 2 (by rfl) ⟨1105872, by rfl⟩ : syracuseStep 2948993 = 2211745) B2211745
theorem B688439 : Blo 405769 688439 := bstep (se 1 (by rfl) ⟨516329, by rfl⟩ : syracuseStep 688439 = 1032659) B1032659
theorem B3670447 : Blo 405769 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B1311175 : Blo 405769 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B3736115 : Blo 405769 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B3474049 : Blo 405769 3474049 := bstep (se 2 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 3474049 = 2605537) B2605537
theorem B918251 : Blo 405769 918251 := bstep (se 1 (by rfl) ⟨688688, by rfl⟩ : syracuseStep 918251 = 1377377) B1377377
theorem B21201841 : Blo 405769 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B5243879 : Blo 405769 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B2622455 : Blo 405769 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B689215 : Blo 405769 689215 := bstep (se 1 (by rfl) ⟨516911, by rfl⟩ : syracuseStep 689215 = 1033823) B1033823
theorem B2328061 : Blo 405769 2328061 := bstep (se 3 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 2328061 = 873023) B873023
theorem B689735 : Blo 405769 689735 := bstep (se 1 (by rfl) ⟨517301, by rfl⟩ : syracuseStep 689735 = 1034603) B1034603
theorem B919151 : Blo 405769 919151 := bstep (se 1 (by rfl) ⟨689363, by rfl⟩ : syracuseStep 919151 = 1378727) B1378727
theorem B460399 : Blo 405769 460399 := bstep (se 1 (by rfl) ⟨345299, by rfl⟩ : syracuseStep 460399 = 690599) B690599
theorem B919259 : Blo 405769 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B460507 : Blo 405769 460507 := bstep (se 1 (by rfl) ⟨345380, by rfl⟩ : syracuseStep 460507 = 690761) B690761
theorem B1378079 : Blo 405769 1378079 := bstep (se 1 (by rfl) ⟨1033559, by rfl⟩ : syracuseStep 1378079 = 2067119) B2067119
theorem B689951 : Blo 405769 689951 := bstep (se 1 (by rfl) ⟨517463, by rfl⟩ : syracuseStep 689951 = 1034927) B1034927
theorem B3770219 : Blo 405769 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B1542017 : Blo 405769 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B1378295 : Blo 405769 1378295 := bstep (se 1 (by rfl) ⟨1033721, by rfl⟩ : syracuseStep 1378295 = 2067443) B2067443
theorem B690167 : Blo 405769 690167 := bstep (se 1 (by rfl) ⟨517625, by rfl⟩ : syracuseStep 690167 = 1035251) B1035251
theorem B1968745 : Blo 405769 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B920375 : Blo 405769 920375 := bstep (se 1 (by rfl) ⟨690281, by rfl⟩ : syracuseStep 920375 = 1380563) B1380563
theorem B1379159 : Blo 405769 1379159 := bstep (se 1 (by rfl) ⟨1034369, by rfl⟩ : syracuseStep 1379159 = 2068739) B2068739
theorem B920555 : Blo 405769 920555 := bstep (se 1 (by rfl) ⟨690416, by rfl⟩ : syracuseStep 920555 = 1380833) B1380833
theorem B1379375 : Blo 405769 1379375 := bstep (se 1 (by rfl) ⟨1034531, by rfl⟩ : syracuseStep 1379375 = 2069063) B2069063
theorem B691247 : Blo 405769 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B691321 : Blo 405769 691321 := bstep (se 2 (by rfl) ⟨259245, by rfl⟩ : syracuseStep 691321 = 518491) B518491
theorem B2198771 : Blo 405769 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B5901619 : Blo 405769 5901619 := bstep (se 1 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 5901619 = 8852429) B8852429
theorem B1379753 : Blo 405769 1379753 := bstep (se 2 (by rfl) ⟨517407, by rfl⟩ : syracuseStep 1379753 = 1034815) B1034815
theorem B2330045 : Blo 405769 2330045 := bstep (se 3 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 2330045 = 873767) B873767
theorem B823079 : Blo 405769 823079 := bstep (se 1 (by rfl) ⟨617309, by rfl⟩ : syracuseStep 823079 = 1234619) B1234619
theorem B921383 : Blo 405769 921383 := bstep (se 1 (by rfl) ⟨691037, by rfl⟩ : syracuseStep 921383 = 1382075) B1382075
theorem B1380239 : Blo 405769 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B1380617 : Blo 405769 1380617 := bstep (se 2 (by rfl) ⟨517731, by rfl⟩ : syracuseStep 1380617 = 1035463) B1035463
theorem B3904001 : Blo 405769 3904001 := bstep (se 2 (by rfl) ⟨1464000, by rfl⟩ : syracuseStep 3904001 = 2928001) B2928001
theorem B2331251 : Blo 405769 2331251 := bstep (se 1 (by rfl) ⟨1748438, by rfl⟩ : syracuseStep 2331251 = 3496877) B3496877
theorem B1741931 : Blo 405769 1741931 := bstep (se 1 (by rfl) ⟨1306448, by rfl⟩ : syracuseStep 1741931 = 2612897) B2612897
theorem B9934073 : Blo 405769 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B2331935 : Blo 405769 2331935 := bstep (se 1 (by rfl) ⟨1748951, by rfl⟩ : syracuseStep 2331935 = 3497903) B3497903
theorem B1381751 : Blo 405769 1381751 := bstep (se 1 (by rfl) ⟨1036313, by rfl⟩ : syracuseStep 1381751 = 2072627) B2072627
theorem B11802419 : Blo 405769 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B4626233 : Blo 405769 4626233 := bstep (se 2 (by rfl) ⟨1734837, by rfl⟩ : syracuseStep 4626233 = 3469675) B3469675
theorem B3905617 : Blo 405769 3905617 := bstep (se 2 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 3905617 = 2929213) B2929213
theorem B2201755 : Blo 405769 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B2070683 : Blo 405769 2070683 := bstep (se 1 (by rfl) ⟨1553012, by rfl⟩ : syracuseStep 2070683 = 3106025) B3106025
theorem B1382561 : Blo 405769 1382561 := bstep (se 2 (by rfl) ⟨518460, by rfl⟩ : syracuseStep 1382561 = 1036921) B1036921
theorem B2234567 : Blo 405769 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1382831 : Blo 405769 1382831 := bstep (se 1 (by rfl) ⟨1037123, by rfl⟩ : syracuseStep 1382831 = 2074247) B2074247
theorem B1743707 : Blo 405769 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B1743929 : Blo 405769 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B3349991 : Blo 405769 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B6954659 : Blo 405769 6954659 := bstep (se 1 (by rfl) ⟨5215994, by rfl⟩ : syracuseStep 6954659 = 10431989) B10431989
theorem B5250851 : Blo 405769 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B2072951 : Blo 405769 2072951 := bstep (se 1 (by rfl) ⟨1554713, by rfl⟩ : syracuseStep 2072951 = 3109427) B3109427
theorem B1155647 : Blo 405769 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B1745945 : Blo 405769 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B1156285 : Blo 405769 1156285 := bstep (se 3 (by rfl) ⟨216803, by rfl⟩ : syracuseStep 1156285 = 433607) B433607
theorem B2073923 : Blo 405769 2073923 := bstep (se 1 (by rfl) ⟨1555442, by rfl⟩ : syracuseStep 2073923 = 3110885) B3110885
theorem B1157129 : Blo 405769 1157129 := bstep (se 2 (by rfl) ⟨433923, by rfl⟩ : syracuseStep 1157129 = 867847) B867847
theorem B4630607 : Blo 405769 4630607 := bstep (se 1 (by rfl) ⟨3472955, by rfl⟩ : syracuseStep 4630607 = 6945911) B6945911
theorem B1550461 : Blo 405769 1550461 := bstep (se 3 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 1550461 = 581423) B581423
theorem B2206727 : Blo 405769 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B11873665 : Blo 405769 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B1027961 : Blo 405769 1027961 := bstep (se 2 (by rfl) ⟨385485, by rfl⟩ : syracuseStep 1027961 = 770971) B770971
theorem B8859779 : Blo 405769 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B4731203 : Blo 405769 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B405887 : Blo 405769 405887 := bstep (se 1 (by rfl) ⟨304415, by rfl⟩ : syracuseStep 405887 = 608831) B608831
theorem B405967 : Blo 405769 405967 := bstep (se 1 (by rfl) ⟨304475, by rfl⟩ : syracuseStep 405967 = 608951) B608951
theorem B406119 : Blo 405769 406119 := bstep (se 1 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 406119 = 609179) B609179
theorem B406383 : Blo 405769 406383 := bstep (se 1 (by rfl) ⟨304787, by rfl⟩ : syracuseStep 406383 = 609575) B609575
theorem B406439 : Blo 405769 406439 := bstep (se 1 (by rfl) ⟨304829, by rfl⟩ : syracuseStep 406439 = 609659) B609659
theorem B406523 : Blo 405769 406523 := bstep (se 1 (by rfl) ⟨304892, by rfl⟩ : syracuseStep 406523 = 609785) B609785
theorem B406591 : Blo 405769 406591 := bstep (se 1 (by rfl) ⟨304943, by rfl⟩ : syracuseStep 406591 = 609887) B609887
theorem B406735 : Blo 405769 406735 := bstep (se 1 (by rfl) ⟨305051, by rfl⟩ : syracuseStep 406735 = 610103) B610103
theorem B406939 : Blo 405769 406939 := bstep (se 1 (by rfl) ⟨305204, by rfl⟩ : syracuseStep 406939 = 610409) B610409
theorem B2602439 : Blo 405769 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B4961735 : Blo 405769 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B1553863 : Blo 405769 1553863 := bstep (se 1 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 1553863 = 2330795) B2330795
theorem B8566361 : Blo 405769 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B407151 : Blo 405769 407151 := bstep (se 1 (by rfl) ⟨305363, by rfl⟩ : syracuseStep 407151 = 610727) B610727
theorem B407207 : Blo 405769 407207 := bstep (se 1 (by rfl) ⟨305405, by rfl⟩ : syracuseStep 407207 = 610811) B610811
theorem B1160887 : Blo 405769 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B407291 : Blo 405769 407291 := bstep (se 1 (by rfl) ⟨305468, by rfl⟩ : syracuseStep 407291 = 610937) B610937
theorem B407327 : Blo 405769 407327 := bstep (se 1 (by rfl) ⟨305495, by rfl⟩ : syracuseStep 407327 = 610991) B610991
theorem B3913535 : Blo 405769 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B407359 : Blo 405769 407359 := bstep (se 1 (by rfl) ⟨305519, by rfl⟩ : syracuseStep 407359 = 611039) B611039
theorem B407535 : Blo 405769 407535 := bstep (se 1 (by rfl) ⟨305651, by rfl⟩ : syracuseStep 407535 = 611303) B611303
theorem B407707 : Blo 405769 407707 := bstep (se 1 (by rfl) ⟨305780, by rfl⟩ : syracuseStep 407707 = 611561) B611561
theorem B407743 : Blo 405769 407743 := bstep (se 1 (by rfl) ⟨305807, by rfl⟩ : syracuseStep 407743 = 611615) B611615
theorem B1161479 : Blo 405769 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B1030441 : Blo 405769 1030441 := bstep (se 2 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 1030441 = 772831) B772831
theorem B407855 : Blo 405769 407855 := bstep (se 1 (by rfl) ⟨305891, by rfl⟩ : syracuseStep 407855 = 611783) B611783
theorem B1489225 : Blo 405769 1489225 := bstep (se 2 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 1489225 = 1116919) B1116919
theorem B2931059 : Blo 405769 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B3488129 : Blo 405769 3488129 := bstep (se 2 (by rfl) ⟨1308048, by rfl⟩ : syracuseStep 3488129 = 2616097) B2616097
theorem B9943505 : Blo 405769 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B408091 : Blo 405769 408091 := bstep (se 1 (by rfl) ⟨306068, by rfl⟩ : syracuseStep 408091 = 612137) B612137
theorem B408095 : Blo 405769 408095 := bstep (se 1 (by rfl) ⟨306071, by rfl⟩ : syracuseStep 408095 = 612143) B612143
theorem B408411 : Blo 405769 408411 := bstep (se 1 (by rfl) ⟨306308, by rfl⟩ : syracuseStep 408411 = 612617) B612617
theorem B1489823 : Blo 405769 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B408479 : Blo 405769 408479 := bstep (se 1 (by rfl) ⟨306359, by rfl⟩ : syracuseStep 408479 = 612719) B612719
theorem B408623 : Blo 405769 408623 := bstep (se 1 (by rfl) ⟨306467, by rfl⟩ : syracuseStep 408623 = 612935) B612935
theorem B408647 : Blo 405769 408647 := bstep (se 1 (by rfl) ⟨306485, by rfl⟩ : syracuseStep 408647 = 612971) B612971
theorem B408799 : Blo 405769 408799 := bstep (se 1 (by rfl) ⟨306599, by rfl⟩ : syracuseStep 408799 = 613199) B613199
theorem B1162505 : Blo 405769 1162505 := bstep (se 2 (by rfl) ⟨435939, by rfl⟩ : syracuseStep 1162505 = 871879) B871879
theorem B1326365 : Blo 405769 1326365 := bstep (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) B497387
theorem B736723 : Blo 405769 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B409063 : Blo 405769 409063 := bstep (se 1 (by rfl) ⟨306797, by rfl⟩ : syracuseStep 409063 = 613595) B613595
theorem B409179 : Blo 405769 409179 := bstep (se 1 (by rfl) ⟨306884, by rfl⟩ : syracuseStep 409179 = 613769) B613769
theorem B409415 : Blo 405769 409415 := bstep (se 1 (by rfl) ⟨307061, by rfl⟩ : syracuseStep 409415 = 614123) B614123
theorem B409567 : Blo 405769 409567 := bstep (se 1 (by rfl) ⟨307175, by rfl⟩ : syracuseStep 409567 = 614351) B614351
theorem B20299855 : Blo 405769 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B770401 : Blo 405769 770401 := bstep (se 2 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 770401 = 577801) B577801
theorem B21283337 : Blo 405769 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B16761613 : Blo 405769 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B869231 : Blo 405769 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B2606539 : Blo 405769 2606539 := bstep (se 1 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 2606539 = 3909809) B3909809
theorem B2311841 : Blo 405769 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B4409129 : Blo 405769 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B772087 : Blo 405769 772087 := bstep (se 1 (by rfl) ⟨579065, by rfl⟩ : syracuseStep 772087 = 1158131) B1158131
theorem B772391 : Blo 405769 772391 := bstep (se 1 (by rfl) ⟨579293, by rfl⟩ : syracuseStep 772391 = 1158587) B1158587
theorem B608795 : Blo 405769 608795 := bstep (se 1 (by rfl) ⟨456596, by rfl⟩ : syracuseStep 608795 = 913193) B913193
theorem B608873 : Blo 405769 608873 := bstep (se 2 (by rfl) ⟨228327, by rfl⟩ : syracuseStep 608873 = 456655) B456655
theorem B4639355 : Blo 405769 4639355 := bstep (se 1 (by rfl) ⟨3479516, by rfl⟩ : syracuseStep 4639355 = 6959033) B6959033
theorem B2837207 : Blo 405769 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B1133615 : Blo 405769 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B609401 : Blo 405769 609401 := bstep (se 2 (by rfl) ⟨228525, by rfl⟩ : syracuseStep 609401 = 457051) B457051
theorem B609503 : Blo 405769 609503 := bstep (se 1 (by rfl) ⟨457127, by rfl⟩ : syracuseStep 609503 = 914255) B914255
theorem B609545 : Blo 405769 609545 := bstep (se 2 (by rfl) ⟨228579, by rfl⟩ : syracuseStep 609545 = 457159) B457159
theorem B871759 : Blo 405769 871759 := bstep (se 1 (by rfl) ⟨653819, by rfl⟩ : syracuseStep 871759 = 1307639) B1307639
theorem B609647 : Blo 405769 609647 := bstep (se 1 (by rfl) ⟨457235, by rfl⟩ : syracuseStep 609647 = 914471) B914471
theorem B773545 : Blo 405769 773545 := bstep (se 2 (by rfl) ⟨290079, by rfl⟩ : syracuseStep 773545 = 580159) B580159
theorem B1330615 : Blo 405769 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B609767 : Blo 405769 609767 := bstep (se 1 (by rfl) ⟨457325, by rfl⟩ : syracuseStep 609767 = 914651) B914651
theorem B1035767 : Blo 405769 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B7818767 : Blo 405769 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B773705 : Blo 405769 773705 := bstep (se 2 (by rfl) ⟨290139, by rfl⟩ : syracuseStep 773705 = 580279) B580279
theorem B3296857 : Blo 405769 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B609899 : Blo 405769 609899 := bstep (se 1 (by rfl) ⟨457424, by rfl⟩ : syracuseStep 609899 = 914849) B914849
theorem B610025 : Blo 405769 610025 := bstep (se 2 (by rfl) ⟨228759, by rfl⟩ : syracuseStep 610025 = 457519) B457519
theorem B610169 : Blo 405769 610169 := bstep (se 2 (by rfl) ⟨228813, by rfl⟩ : syracuseStep 610169 = 457627) B457627
theorem B708473 : Blo 405769 708473 := bstep (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) B531355
theorem B610271 : Blo 405769 610271 := bstep (se 1 (by rfl) ⟨457703, by rfl⟩ : syracuseStep 610271 = 915407) B915407
theorem B610523 : Blo 405769 610523 := bstep (se 1 (by rfl) ⟨457892, by rfl⟩ : syracuseStep 610523 = 915785) B915785
theorem B610535 : Blo 405769 610535 := bstep (se 1 (by rfl) ⟨457901, by rfl⟩ : syracuseStep 610535 = 915803) B915803
theorem B610697 : Blo 405769 610697 := bstep (se 2 (by rfl) ⟨229011, by rfl⟩ : syracuseStep 610697 = 458023) B458023
theorem B2347429 : Blo 405769 2347429 := bstep (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) B440143
theorem B1036759 : Blo 405769 1036759 := bstep (se 1 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 1036759 = 1555139) B1555139
theorem B610793 : Blo 405769 610793 := bstep (se 2 (by rfl) ⟨229047, by rfl⟩ : syracuseStep 610793 = 458095) B458095
theorem B610919 : Blo 405769 610919 := bstep (se 1 (by rfl) ⟨458189, by rfl⟩ : syracuseStep 610919 = 916379) B916379
theorem B611051 : Blo 405769 611051 := bstep (se 1 (by rfl) ⟨458288, by rfl⟩ : syracuseStep 611051 = 916577) B916577
theorem B1037063 : Blo 405769 1037063 := bstep (se 1 (by rfl) ⟨777797, by rfl⟩ : syracuseStep 1037063 = 1555595) B1555595
theorem B611081 : Blo 405769 611081 := bstep (se 2 (by rfl) ⟨229155, by rfl⟩ : syracuseStep 611081 = 458311) B458311
theorem B611183 : Blo 405769 611183 := bstep (se 1 (by rfl) ⟨458387, by rfl⟩ : syracuseStep 611183 = 916775) B916775
theorem B775163 : Blo 405769 775163 := bstep (se 1 (by rfl) ⟨581372, by rfl⟩ : syracuseStep 775163 = 1162745) B1162745
theorem B611435 : Blo 405769 611435 := bstep (se 1 (by rfl) ⟨458576, by rfl⟩ : syracuseStep 611435 = 917153) B917153
theorem B611675 : Blo 405769 611675 := bstep (se 1 (by rfl) ⟨458756, by rfl⟩ : syracuseStep 611675 = 917513) B917513
theorem B775649 : Blo 405769 775649 := bstep (se 2 (by rfl) ⟨290868, by rfl⟩ : syracuseStep 775649 = 581737) B581737
theorem B611951 : Blo 405769 611951 := bstep (se 1 (by rfl) ⟨458963, by rfl⟩ : syracuseStep 611951 = 917927) B917927
theorem B612023 : Blo 405769 612023 := bstep (se 1 (by rfl) ⟨459017, by rfl⟩ : syracuseStep 612023 = 918035) B918035
theorem B612059 : Blo 405769 612059 := bstep (se 1 (by rfl) ⟨459044, by rfl⟩ : syracuseStep 612059 = 918089) B918089
theorem B612233 : Blo 405769 612233 := bstep (se 2 (by rfl) ⟨229587, by rfl⟩ : syracuseStep 612233 = 459175) B459175
theorem B2316215 : Blo 405769 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B612335 : Blo 405769 612335 := bstep (se 1 (by rfl) ⟨459251, by rfl⟩ : syracuseStep 612335 = 918503) B918503
theorem B612587 : Blo 405769 612587 := bstep (se 1 (by rfl) ⟨459440, by rfl⟩ : syracuseStep 612587 = 918881) B918881
theorem B612647 : Blo 405769 612647 := bstep (se 1 (by rfl) ⟨459485, by rfl⟩ : syracuseStep 612647 = 918971) B918971
theorem B874793 : Blo 405769 874793 := bstep (se 2 (by rfl) ⟨328047, by rfl⟩ : syracuseStep 874793 = 656095) B656095
theorem B612731 : Blo 405769 612731 := bstep (se 1 (by rfl) ⟨459548, by rfl⟩ : syracuseStep 612731 = 919097) B919097
theorem B1235375 : Blo 405769 1235375 := bstep (se 1 (by rfl) ⟨926531, by rfl⟩ : syracuseStep 1235375 = 1853063) B1853063
theorem B1104317 : Blo 405769 1104317 := bstep (se 3 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 1104317 = 414119) B414119
theorem B613001 : Blo 405769 613001 := bstep (se 2 (by rfl) ⟨229875, by rfl⟩ : syracuseStep 613001 = 459751) B459751
theorem B42326833 : Blo 405769 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B613175 : Blo 405769 613175 := bstep (se 1 (by rfl) ⟨459881, by rfl⟩ : syracuseStep 613175 = 919763) B919763
theorem B613211 : Blo 405769 613211 := bstep (se 1 (by rfl) ⟨459908, by rfl⟩ : syracuseStep 613211 = 919817) B919817
theorem B613355 : Blo 405769 613355 := bstep (se 1 (by rfl) ⟨460016, by rfl⟩ : syracuseStep 613355 = 920033) B920033
theorem B2055293 : Blo 405769 2055293 := bstep (se 3 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 2055293 = 770735) B770735
theorem B4775057 : Blo 405769 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B613559 : Blo 405769 613559 := bstep (se 1 (by rfl) ⟨460169, by rfl⟩ : syracuseStep 613559 = 920339) B920339
theorem B1465559 : Blo 405769 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B613799 : Blo 405769 613799 := bstep (se 1 (by rfl) ⟨460349, by rfl⟩ : syracuseStep 613799 = 920699) B920699
theorem B613883 : Blo 405769 613883 := bstep (se 1 (by rfl) ⟨460412, by rfl⟩ : syracuseStep 613883 = 920825) B920825
theorem B613979 : Blo 405769 613979 := bstep (se 1 (by rfl) ⟨460484, by rfl⟩ : syracuseStep 613979 = 920969) B920969
theorem B614063 : Blo 405769 614063 := bstep (se 1 (by rfl) ⟨460547, by rfl⟩ : syracuseStep 614063 = 921095) B921095
theorem B679657 : Blo 405769 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B614183 : Blo 405769 614183 := bstep (se 1 (by rfl) ⟨460637, by rfl⟩ : syracuseStep 614183 = 921275) B921275
theorem B3104567 : Blo 405769 3104567 := bstep (se 1 (by rfl) ⟨2328425, by rfl⟩ : syracuseStep 3104567 = 4656851) B4656851
theorem B614267 : Blo 405769 614267 := bstep (se 1 (by rfl) ⟨460700, by rfl⟩ : syracuseStep 614267 = 921401) B921401
theorem B2613383 : Blo 405769 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B3727619 : Blo 405769 3727619 := bstep (se 1 (by rfl) ⟨2795714, by rfl⟩ : syracuseStep 3727619 = 5591429) B5591429
theorem B2941265 : Blo 405769 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B1303103 : Blo 405769 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B5039003 : Blo 405769 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B549995 : Blo 405769 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B4646645 : Blo 405769 4646645 := bstep (se 5 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 4646645 = 435623) B435623
theorem B1370303 : Blo 405769 1370303 := bstep (se 1 (by rfl) ⟨1027727, by rfl⟩ : syracuseStep 1370303 = 2055455) B2055455
theorem B682219 : Blo 405769 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B3303737 : Blo 405769 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B2779643 : Blo 405769 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B1436161 : Blo 405769 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B53144099 : Blo 405769 53144099 := bstep (se 1 (by rfl) ⟨39858074, by rfl⟩ : syracuseStep 53144099 = 79716149) B79716149
theorem B3468035 : Blo 405769 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B167668697 : Blo 405769 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B3009869 : Blo 405769 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B1371923 : Blo 405769 1371923 := bstep (se 1 (by rfl) ⟨1028942, by rfl⟩ : syracuseStep 1371923 = 2057885) B2057885
theorem B2781067 : Blo 405769 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B2060477 : Blo 405769 2060477 := bstep (se 3 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 2060477 = 772679) B772679
theorem B2322755 : Blo 405769 2322755 := bstep (se 1 (by rfl) ⟨1742066, by rfl⟩ : syracuseStep 2322755 = 3484133) B3484133
theorem B5206517 : Blo 405769 5206517 := bstep (se 5 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 5206517 = 488111) B488111
theorem B913913 : Blo 405769 913913 := bstep (se 2 (by rfl) ⟨342717, by rfl⟩ : syracuseStep 913913 = 685435) B685435
theorem B914003 : Blo 405769 914003 := bstep (se 1 (by rfl) ⟨685502, by rfl⟩ : syracuseStep 914003 = 1371005) B1371005
theorem B1372787 : Blo 405769 1372787 := bstep (se 1 (by rfl) ⟨1029590, by rfl⟩ : syracuseStep 1372787 = 2059181) B2059181
theorem B914183 : Blo 405769 914183 := bstep (se 1 (by rfl) ⟨685637, by rfl⟩ : syracuseStep 914183 = 1371275) B1371275
theorem B684841 : Blo 405769 684841 := bstep (se 2 (by rfl) ⟨256815, by rfl⟩ : syracuseStep 684841 = 513631) B513631
theorem B1373057 : Blo 405769 1373057 := bstep (se 2 (by rfl) ⟨514896, by rfl⟩ : syracuseStep 1373057 = 1029793) B1029793
theorem B488443 : Blo 405769 488443 := bstep (se 1 (by rfl) ⟨366332, by rfl⟩ : syracuseStep 488443 = 732665) B732665
theorem B685111 : Blo 405769 685111 := bstep (se 1 (by rfl) ⟨513833, by rfl⟩ : syracuseStep 685111 = 1027667) B1027667
theorem B2618507 : Blo 405769 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B652871 : Blo 405769 652871 := bstep (se 1 (by rfl) ⟨489653, by rfl⟩ : syracuseStep 652871 = 979307) B979307
theorem B1373867 : Blo 405769 1373867 := bstep (se 1 (by rfl) ⟨1030400, by rfl⟩ : syracuseStep 1373867 = 2060801) B2060801
theorem B456511 : Blo 405769 456511 := bstep (se 1 (by rfl) ⟨342383, by rfl⟩ : syracuseStep 456511 = 684767) B684767
theorem B915263 : Blo 405769 915263 := bstep (se 1 (by rfl) ⟨686447, by rfl⟩ : syracuseStep 915263 = 1372895) B1372895
theorem B686063 : Blo 405769 686063 := bstep (se 1 (by rfl) ⟨514547, by rfl⟩ : syracuseStep 686063 = 1029095) B1029095
theorem B1374191 : Blo 405769 1374191 := bstep (se 1 (by rfl) ⟨1030643, by rfl⟩ : syracuseStep 1374191 = 2061287) B2061287
theorem B456799 : Blo 405769 456799 := bstep (se 1 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 456799 = 685199) B685199
theorem B915551 : Blo 405769 915551 := bstep (se 1 (by rfl) ⟨686663, by rfl⟩ : syracuseStep 915551 = 1373327) B1373327
theorem B1374407 : Blo 405769 1374407 := bstep (se 1 (by rfl) ⟨1030805, by rfl⟩ : syracuseStep 1374407 = 2061611) B2061611
theorem B686623 : Blo 405769 686623 := bstep (se 1 (by rfl) ⟨514967, by rfl⟩ : syracuseStep 686623 = 1029935) B1029935
theorem B2325145 : Blo 405769 2325145 := bstep (se 2 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 2325145 = 1743859) B1743859
theorem B1375055 : Blo 405769 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B916307 : Blo 405769 916307 := bstep (se 1 (by rfl) ⟨687230, by rfl⟩ : syracuseStep 916307 = 1374461) B1374461
theorem B687055 : Blo 405769 687055 := bstep (se 1 (by rfl) ⟨515291, by rfl⟩ : syracuseStep 687055 = 1030583) B1030583
theorem B2620505 : Blo 405769 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B621689 : Blo 405769 621689 := bstep (se 2 (by rfl) ⟨233133, by rfl⟩ : syracuseStep 621689 = 466267) B466267
theorem B1375379 : Blo 405769 1375379 := bstep (se 1 (by rfl) ⟨1031534, by rfl⟩ : syracuseStep 1375379 = 2063069) B2063069
theorem B457951 : Blo 405769 457951 := bstep (se 1 (by rfl) ⟨343463, by rfl⟩ : syracuseStep 457951 = 686927) B686927
theorem B1309945 : Blo 405769 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B916847 : Blo 405769 916847 := bstep (se 1 (by rfl) ⟨687635, by rfl⟩ : syracuseStep 916847 = 1375271) B1375271
theorem B1375649 : Blo 405769 1375649 := bstep (se 2 (by rfl) ⟨515868, by rfl⟩ : syracuseStep 1375649 = 1031737) B1031737
theorem B2063879 : Blo 405769 2063879 := bstep (se 1 (by rfl) ⟨1547909, by rfl⟩ : syracuseStep 2063879 = 3095819) B3095819
theorem B917135 : Blo 405769 917135 := bstep (se 1 (by rfl) ⟨687851, by rfl⟩ : syracuseStep 917135 = 1375703) B1375703
theorem B687791 : Blo 405769 687791 := bstep (se 1 (by rfl) ⟨515843, by rfl⟩ : syracuseStep 687791 = 1031687) B1031687
theorem B917225 : Blo 405769 917225 := bstep (se 2 (by rfl) ⟨343959, by rfl⟩ : syracuseStep 917225 = 687919) B687919
theorem B1867607 : Blo 405769 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B688027 : Blo 405769 688027 := bstep (se 1 (by rfl) ⟨516020, by rfl⟩ : syracuseStep 688027 = 1032041) B1032041
theorem B1965995 : Blo 405769 1965995 := bstep (se 1 (by rfl) ⟨1474496, by rfl⟩ : syracuseStep 1965995 = 2948993) B2948993
theorem B1376189 : Blo 405769 1376189 := bstep (se 3 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 1376189 = 516071) B516071
theorem B27066473 : Blo 405769 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B458959 : Blo 405769 458959 := bstep (se 1 (by rfl) ⟨344219, by rfl⟩ : syracuseStep 458959 = 688439) B688439
theorem B14188891 : Blo 405769 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B2490743 : Blo 405769 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B22348817 : Blo 405769 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B459823 : Blo 405769 459823 := bstep (se 1 (by rfl) ⟨344867, by rfl⟩ : syracuseStep 459823 = 689735) B689735
theorem B1541227 : Blo 405769 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B5866613 : Blo 405769 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B918719 : Blo 405769 918719 := bstep (se 1 (by rfl) ⟨689039, by rfl⟩ : syracuseStep 918719 = 1378079) B1378079
theorem B459967 : Blo 405769 459967 := bstep (se 1 (by rfl) ⟨344975, by rfl⟩ : syracuseStep 459967 = 689951) B689951
theorem B918863 : Blo 405769 918863 := bstep (se 1 (by rfl) ⟨689147, by rfl⟩ : syracuseStep 918863 = 1378295) B1378295
theorem B460111 : Blo 405769 460111 := bstep (se 1 (by rfl) ⟨345083, by rfl⟩ : syracuseStep 460111 = 690167) B690167
theorem B918953 : Blo 405769 918953 := bstep (se 2 (by rfl) ⟨344607, by rfl⟩ : syracuseStep 918953 = 689215) B689215
theorem B3081725 : Blo 405769 3081725 := bstep (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) B1155647
theorem B1541713 : Blo 405769 1541713 := bstep (se 2 (by rfl) ⟨578142, by rfl⟩ : syracuseStep 1541713 = 1156285) B1156285
theorem B919439 : Blo 405769 919439 := bstep (se 1 (by rfl) ⟨689579, by rfl⟩ : syracuseStep 919439 = 1379159) B1379159
theorem B3475385 : Blo 405769 3475385 := bstep (se 2 (by rfl) ⟨1303269, by rfl⟩ : syracuseStep 3475385 = 2606539) B2606539
theorem B755743 : Blo 405769 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B919583 : Blo 405769 919583 := bstep (se 1 (by rfl) ⟨689687, by rfl⟩ : syracuseStep 919583 = 1379375) B1379375
theorem B460831 : Blo 405769 460831 := bstep (se 1 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 460831 = 691247) B691247
theorem B919835 : Blo 405769 919835 := bstep (se 1 (by rfl) ⟨689876, by rfl⟩ : syracuseStep 919835 = 1379753) B1379753
theorem B690511 : Blo 405769 690511 := bstep (se 1 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 690511 = 1035767) B1035767
theorem B5212511 : Blo 405769 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B920159 : Blo 405769 920159 := bstep (se 1 (by rfl) ⟨690119, by rfl⟩ : syracuseStep 920159 = 1380239) B1380239
theorem B2067281 : Blo 405769 2067281 := bstep (se 2 (by rfl) ⟨775230, by rfl⟩ : syracuseStep 2067281 = 1550461) B1550461
theorem B920411 : Blo 405769 920411 := bstep (se 1 (by rfl) ⟨690308, by rfl⟩ : syracuseStep 920411 = 1380617) B1380617
theorem B691375 : Blo 405769 691375 := bstep (se 1 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 691375 = 1037063) B1037063
theorem B2624993 : Blo 405769 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B6622715 : Blo 405769 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B921167 : Blo 405769 921167 := bstep (se 1 (by rfl) ⟨690875, by rfl⟩ : syracuseStep 921167 = 1381751) B1381751
theorem B7868279 : Blo 405769 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B3084155 : Blo 405769 3084155 := bstep (se 1 (by rfl) ⟨2313116, by rfl⟩ : syracuseStep 3084155 = 4626233) B4626233
theorem B1544143 : Blo 405769 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B1380455 : Blo 405769 1380455 := bstep (se 1 (by rfl) ⟨1035341, by rfl⟩ : syracuseStep 1380455 = 2070683) B2070683
theorem B921707 : Blo 405769 921707 := bstep (se 1 (by rfl) ⟨691280, by rfl⟩ : syracuseStep 921707 = 1382561) B1382561
theorem B921761 : Blo 405769 921761 := bstep (se 2 (by rfl) ⟨345660, by rfl⟩ : syracuseStep 921761 = 691321) B691321
theorem B1740989 : Blo 405769 1740989 := bstep (se 3 (by rfl) ⟨326435, by rfl⟩ : syracuseStep 1740989 = 652871) B652871
theorem B823583 : Blo 405769 823583 := bstep (se 1 (by rfl) ⟨617687, by rfl⟩ : syracuseStep 823583 = 1235375) B1235375
theorem B921887 : Blo 405769 921887 := bstep (se 1 (by rfl) ⟨691415, by rfl⟩ : syracuseStep 921887 = 1382831) B1382831
theorem B7868825 : Blo 405769 7868825 := bstep (se 2 (by rfl) ⟨2950809, by rfl⟩ : syracuseStep 7868825 = 5901619) B5901619
theorem B15831553 : Blo 405769 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B1774153 : Blo 405769 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B3183371 : Blo 405769 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B4395809 : Blo 405769 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B2233327 : Blo 405769 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B3708089 : Blo 405769 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B2069711 : Blo 405769 2069711 := bstep (se 1 (by rfl) ⟨1552283, by rfl⟩ : syracuseStep 2069711 = 3104567) B3104567
theorem B1742255 : Blo 405769 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B1381967 : Blo 405769 1381967 := bstep (se 1 (by rfl) ⟨1036475, by rfl⟩ : syracuseStep 1381967 = 2072951) B2072951
theorem B1382345 : Blo 405769 1382345 := bstep (se 2 (by rfl) ⟨518379, by rfl⟩ : syracuseStep 1382345 = 1036759) B1036759
theorem B1382615 : Blo 405769 1382615 := bstep (se 1 (by rfl) ⟨1036961, by rfl⟩ : syracuseStep 1382615 = 2073923) B2073923
theorem B7412381 : Blo 405769 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B3087071 : Blo 405769 3087071 := bstep (se 1 (by rfl) ⟨2315303, by rfl⟩ : syracuseStep 3087071 = 4630607) B4630607
theorem B2202491 : Blo 405769 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B35429399 : Blo 405769 35429399 := bstep (se 1 (by rfl) ⟨26572049, by rfl⟩ : syracuseStep 35429399 = 53144099) B53144099
theorem B2071817 : Blo 405769 2071817 := bstep (se 2 (by rfl) ⟨776931, by rfl⟩ : syracuseStep 2071817 = 1553863) B1553863
theorem B111779131 : Blo 405769 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B2006579 : Blo 405769 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B1547849 : Blo 405769 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B5906519 : Blo 405769 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B1548503 : Blo 405769 1548503 := bstep (se 1 (by rfl) ⟨1161377, by rfl⟩ : syracuseStep 1548503 = 2322755) B2322755
theorem B3154135 : Blo 405769 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B1745671 : Blo 405769 1745671 := bstep (se 1 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 1745671 = 2618507) B2618507
theorem B5710907 : Blo 405769 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B56435777 : Blo 405769 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B6629003 : Blo 405769 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B1746593 : Blo 405769 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B993215 : Blo 405769 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B1747003 : Blo 405769 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1027201 : Blo 405769 1027201 := bstep (se 2 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 1027201 = 770401) B770401
theorem B4893929 : Blo 405769 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B1748233 : Blo 405769 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B1748303 : Blo 405769 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B4632065 : Blo 405769 4632065 := bstep (se 2 (by rfl) ⟨1737024, by rfl⟩ : syracuseStep 4632065 = 3474049) B3474049
theorem B1028011 : Blo 405769 1028011 := bstep (se 1 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 1028011 = 1542017) B1542017
theorem B405863 : Blo 405769 405863 := bstep (se 1 (by rfl) ⟨304397, by rfl⟩ : syracuseStep 405863 = 608795) B608795
theorem B405915 : Blo 405769 405915 := bstep (se 1 (by rfl) ⟨304436, by rfl⟩ : syracuseStep 405915 = 608873) B608873
theorem B3092903 : Blo 405769 3092903 := bstep (se 1 (by rfl) ⟨2319677, by rfl⟩ : syracuseStep 3092903 = 4639355) B4639355
theorem B406267 : Blo 405769 406267 := bstep (se 1 (by rfl) ⟨304700, by rfl⟩ : syracuseStep 406267 = 609401) B609401
theorem B406335 : Blo 405769 406335 := bstep (se 1 (by rfl) ⟨304751, by rfl⟩ : syracuseStep 406335 = 609503) B609503
theorem B406363 : Blo 405769 406363 := bstep (se 1 (by rfl) ⟨304772, by rfl⟩ : syracuseStep 406363 = 609545) B609545
theorem B406431 : Blo 405769 406431 := bstep (se 1 (by rfl) ⟨304823, by rfl⟩ : syracuseStep 406431 = 609647) B609647
theorem B1553363 : Blo 405769 1553363 := bstep (se 1 (by rfl) ⟨1165022, by rfl⟩ : syracuseStep 1553363 = 2330045) B2330045
theorem B406511 : Blo 405769 406511 := bstep (se 1 (by rfl) ⟨304883, by rfl⟩ : syracuseStep 406511 = 609767) B609767
theorem B406599 : Blo 405769 406599 := bstep (se 1 (by rfl) ⟨304949, by rfl⟩ : syracuseStep 406599 = 609899) B609899
theorem B406683 : Blo 405769 406683 := bstep (se 1 (by rfl) ⟨305012, by rfl⟩ : syracuseStep 406683 = 610025) B610025
theorem B406779 : Blo 405769 406779 := bstep (se 1 (by rfl) ⟨305084, by rfl⟩ : syracuseStep 406779 = 610169) B610169
theorem B406847 : Blo 405769 406847 := bstep (se 1 (by rfl) ⟨305135, by rfl⟩ : syracuseStep 406847 = 610271) B610271
theorem B1029449 : Blo 405769 1029449 := bstep (se 2 (by rfl) ⟨386043, by rfl⟩ : syracuseStep 1029449 = 772087) B772087
theorem B407015 : Blo 405769 407015 := bstep (se 1 (by rfl) ⟨305261, by rfl⟩ : syracuseStep 407015 = 610523) B610523
theorem B407023 : Blo 405769 407023 := bstep (se 1 (by rfl) ⟨305267, by rfl⟩ : syracuseStep 407023 = 610535) B610535
theorem B407131 : Blo 405769 407131 := bstep (se 1 (by rfl) ⟨305348, by rfl⟩ : syracuseStep 407131 = 610697) B610697
theorem B407195 : Blo 405769 407195 := bstep (se 1 (by rfl) ⟨305396, by rfl⟩ : syracuseStep 407195 = 610793) B610793
theorem B2602667 : Blo 405769 2602667 := bstep (se 1 (by rfl) ⟨1952000, by rfl⟩ : syracuseStep 2602667 = 3904001) B3904001
theorem B407279 : Blo 405769 407279 := bstep (se 1 (by rfl) ⟨305459, by rfl⟩ : syracuseStep 407279 = 610919) B610919
theorem B1554167 : Blo 405769 1554167 := bstep (se 1 (by rfl) ⟨1165625, by rfl⟩ : syracuseStep 1554167 = 2331251) B2331251
theorem B407367 : Blo 405769 407367 := bstep (se 1 (by rfl) ⟨305525, by rfl⟩ : syracuseStep 407367 = 611051) B611051
theorem B407387 : Blo 405769 407387 := bstep (se 1 (by rfl) ⟨305540, by rfl⟩ : syracuseStep 407387 = 611081) B611081
theorem B407455 : Blo 405769 407455 := bstep (se 1 (by rfl) ⟨305591, by rfl⟩ : syracuseStep 407455 = 611183) B611183
theorem B1914881 : Blo 405769 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B407623 : Blo 405769 407623 := bstep (se 1 (by rfl) ⟨305717, by rfl⟩ : syracuseStep 407623 = 611435) B611435
theorem B1161287 : Blo 405769 1161287 := bstep (se 1 (by rfl) ⟨870965, by rfl⟩ : syracuseStep 1161287 = 1741931) B1741931
theorem B1554623 : Blo 405769 1554623 := bstep (se 1 (by rfl) ⟨1165967, by rfl⟩ : syracuseStep 1554623 = 2331935) B2331935
theorem B407783 : Blo 405769 407783 := bstep (se 1 (by rfl) ⟨305837, by rfl⟩ : syracuseStep 407783 = 611675) B611675
theorem B407967 : Blo 405769 407967 := bstep (se 1 (by rfl) ⟨305975, by rfl⟩ : syracuseStep 407967 = 611951) B611951
theorem B408015 : Blo 405769 408015 := bstep (se 1 (by rfl) ⟨306011, by rfl⟩ : syracuseStep 408015 = 612023) B612023
theorem B408039 : Blo 405769 408039 := bstep (se 1 (by rfl) ⟨306029, by rfl⟩ : syracuseStep 408039 = 612059) B612059
theorem B408155 : Blo 405769 408155 := bstep (se 1 (by rfl) ⟨306116, by rfl⟩ : syracuseStep 408155 = 612233) B612233
theorem B408223 : Blo 405769 408223 := bstep (se 1 (by rfl) ⟨306167, by rfl⟩ : syracuseStep 408223 = 612335) B612335
theorem B408391 : Blo 405769 408391 := bstep (se 1 (by rfl) ⟨306293, by rfl⟩ : syracuseStep 408391 = 612587) B612587
theorem B408431 : Blo 405769 408431 := bstep (se 1 (by rfl) ⟨306323, by rfl⟩ : syracuseStep 408431 = 612647) B612647
theorem B408487 : Blo 405769 408487 := bstep (se 1 (by rfl) ⟨306365, by rfl⟩ : syracuseStep 408487 = 612731) B612731
theorem B736211 : Blo 405769 736211 := bstep (se 1 (by rfl) ⟨552158, by rfl⟩ : syracuseStep 736211 = 1104317) B1104317
theorem B408667 : Blo 405769 408667 := bstep (se 1 (by rfl) ⟨306500, by rfl⟩ : syracuseStep 408667 = 613001) B613001
theorem B1162345 : Blo 405769 1162345 := bstep (se 2 (by rfl) ⟨435879, by rfl⟩ : syracuseStep 1162345 = 871759) B871759
theorem B408783 : Blo 405769 408783 := bstep (se 1 (by rfl) ⟨306587, by rfl⟩ : syracuseStep 408783 = 613175) B613175
theorem B1031393 : Blo 405769 1031393 := bstep (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) B773545
theorem B1162471 : Blo 405769 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B408807 : Blo 405769 408807 := bstep (se 1 (by rfl) ⟨306605, by rfl⟩ : syracuseStep 408807 = 613211) B613211
theorem B408903 : Blo 405769 408903 := bstep (se 1 (by rfl) ⟨306677, by rfl⟩ : syracuseStep 408903 = 613355) B613355
theorem B1162619 : Blo 405769 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B409039 : Blo 405769 409039 := bstep (se 1 (by rfl) ⟨306779, by rfl⟩ : syracuseStep 409039 = 613559) B613559
theorem B409199 : Blo 405769 409199 := bstep (se 1 (by rfl) ⟨306899, by rfl⟩ : syracuseStep 409199 = 613799) B613799
theorem B409255 : Blo 405769 409255 := bstep (se 1 (by rfl) ⟨306941, by rfl⟩ : syracuseStep 409255 = 613883) B613883
theorem B409319 : Blo 405769 409319 := bstep (se 1 (by rfl) ⟨306989, by rfl⟩ : syracuseStep 409319 = 613979) B613979
theorem B4636439 : Blo 405769 4636439 := bstep (se 1 (by rfl) ⟨3477329, by rfl⟩ : syracuseStep 4636439 = 6954659) B6954659
theorem B409375 : Blo 405769 409375 := bstep (se 1 (by rfl) ⟨307031, by rfl⟩ : syracuseStep 409375 = 614063) B614063
theorem B409455 : Blo 405769 409455 := bstep (se 1 (by rfl) ⟨307091, by rfl⟩ : syracuseStep 409455 = 614183) B614183
theorem B409511 : Blo 405769 409511 := bstep (se 1 (by rfl) ⟨307133, by rfl⟩ : syracuseStep 409511 = 614267) B614267
theorem B868735 : Blo 405769 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B3129905 : Blo 405769 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B3359335 : Blo 405769 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B1163963 : Blo 405769 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B3097277 : Blo 405769 3097277 := bstep (se 3 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 3097277 = 1161479) B1161479
theorem B3097763 : Blo 405769 3097763 := bstep (se 1 (by rfl) ⟨2323322, by rfl⟩ : syracuseStep 3097763 = 4646645) B4646645
theorem B771419 : Blo 405769 771419 := bstep (se 1 (by rfl) ⟨578564, by rfl⟩ : syracuseStep 771419 = 1157129) B1157129
theorem B2312023 : Blo 405769 2312023 := bstep (se 1 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 2312023 = 3468035) B3468035
theorem B608681 : Blo 405769 608681 := bstep (se 2 (by rfl) ⟨228255, by rfl⟩ : syracuseStep 608681 = 456511) B456511
theorem B609065 : Blo 405769 609065 := bstep (se 2 (by rfl) ⟨228399, by rfl⟩ : syracuseStep 609065 = 456799) B456799
theorem B2935673 : Blo 405769 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B1657837 : Blo 405769 1657837 := bstep (se 3 (by rfl) ⟨310844, by rfl⟩ : syracuseStep 1657837 = 621689) B621689
theorem B609275 : Blo 405769 609275 := bstep (se 1 (by rfl) ⟨456956, by rfl⟩ : syracuseStep 609275 = 913913) B913913
theorem B609335 : Blo 405769 609335 := bstep (se 1 (by rfl) ⟨457001, by rfl⟩ : syracuseStep 609335 = 914003) B914003
theorem B1985633 : Blo 405769 1985633 := bstep (se 2 (by rfl) ⟨744612, by rfl⟩ : syracuseStep 1985633 = 1489225) B1489225
theorem B609455 : Blo 405769 609455 := bstep (se 1 (by rfl) ⟨457091, by rfl⟩ : syracuseStep 609455 = 914183) B914183
theorem B3100193 : Blo 405769 3100193 := bstep (se 2 (by rfl) ⟨1162572, by rfl⟩ : syracuseStep 3100193 = 2325145) B2325145
theorem B610175 : Blo 405769 610175 := bstep (se 1 (by rfl) ⟨457631, by rfl⟩ : syracuseStep 610175 = 915263) B915263
theorem B2609023 : Blo 405769 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B610367 : Blo 405769 610367 := bstep (se 1 (by rfl) ⟨457775, by rfl⟩ : syracuseStep 610367 = 915551) B915551
theorem B1954039 : Blo 405769 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B610601 : Blo 405769 610601 := bstep (se 2 (by rfl) ⟨228975, by rfl⟩ : syracuseStep 610601 = 457951) B457951
theorem B610871 : Blo 405769 610871 := bstep (se 1 (by rfl) ⟨458153, by rfl⟩ : syracuseStep 610871 = 916307) B916307
theorem B775003 : Blo 405769 775003 := bstep (se 1 (by rfl) ⟨581252, by rfl⟩ : syracuseStep 775003 = 1162505) B1162505
theorem B611231 : Blo 405769 611231 := bstep (se 1 (by rfl) ⟨458423, by rfl⟩ : syracuseStep 611231 = 916847) B916847
theorem B906209 : Blo 405769 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B1889261 : Blo 405769 1889261 := bstep (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) B708473
theorem B611423 : Blo 405769 611423 := bstep (se 1 (by rfl) ⟨458567, by rfl⟩ : syracuseStep 611423 = 917135) B917135
theorem B611483 : Blo 405769 611483 := bstep (se 1 (by rfl) ⟨458612, by rfl⟩ : syracuseStep 611483 = 917225) B917225
theorem B612167 : Blo 405769 612167 := bstep (se 1 (by rfl) ⟨459125, by rfl⟩ : syracuseStep 612167 = 918251) B918251
theorem B579487 : Blo 405769 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B3495919 : Blo 405769 3495919 := bstep (se 1 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 3495919 = 5243879) B5243879
theorem B612767 : Blo 405769 612767 := bstep (se 1 (by rfl) ⟨459575, by rfl⟩ : syracuseStep 612767 = 919151) B919151
theorem B612839 : Blo 405769 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B2939419 : Blo 405769 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B28269121 : Blo 405769 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B2513479 : Blo 405769 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B514927 : Blo 405769 514927 := bstep (se 1 (by rfl) ⟨386195, by rfl⟩ : syracuseStep 514927 = 772391) B772391
theorem B613583 : Blo 405769 613583 := bstep (se 1 (by rfl) ⟨460187, by rfl⟩ : syracuseStep 613583 = 920375) B920375
theorem B613703 : Blo 405769 613703 := bstep (se 1 (by rfl) ⟨460277, by rfl⟩ : syracuseStep 613703 = 920555) B920555
theorem B3104081 : Blo 405769 3104081 := bstep (se 2 (by rfl) ⟨1164030, by rfl⟩ : syracuseStep 3104081 = 2328061) B2328061
theorem B613865 : Blo 405769 613865 := bstep (se 2 (by rfl) ⟨230199, by rfl⟩ : syracuseStep 613865 = 460399) B460399
theorem B1465847 : Blo 405769 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B614009 : Blo 405769 614009 := bstep (se 2 (by rfl) ⟨230253, by rfl⟩ : syracuseStep 614009 = 460507) B460507
theorem B515803 : Blo 405769 515803 := bstep (se 1 (by rfl) ⟨386852, by rfl⟩ : syracuseStep 515803 = 773705) B773705
theorem B614255 : Blo 405769 614255 := bstep (se 1 (by rfl) ⟨460691, by rfl⟩ : syracuseStep 614255 = 921383) B921383
theorem B909625 : Blo 405769 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B516775 : Blo 405769 516775 := bstep (se 1 (by rfl) ⟨387581, by rfl⟩ : syracuseStep 516775 = 775163) B775163
theorem B517099 : Blo 405769 517099 := bstep (se 1 (by rfl) ⟨387824, by rfl⟩ : syracuseStep 517099 = 775649) B775649
theorem B583195 : Blo 405769 583195 := bstep (se 1 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 583195 = 874793) B874793
theorem B1370195 : Blo 405769 1370195 := bstep (se 1 (by rfl) ⟨1027646, by rfl⟩ : syracuseStep 1370195 = 2055293) B2055293
theorem B977039 : Blo 405769 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B3500567 : Blo 405769 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B2485079 : Blo 405769 2485079 := bstep (se 1 (by rfl) ⟨1863809, by rfl⟩ : syracuseStep 2485079 = 3727619) B3727619
theorem B1960843 : Blo 405769 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B5958845 : Blo 405769 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B913121 : Blo 405769 913121 := bstep (se 2 (by rfl) ⟨342420, by rfl⟩ : syracuseStep 913121 = 684841) B684841
theorem B651257 : Blo 405769 651257 := bstep (se 2 (by rfl) ⟨244221, by rfl⟩ : syracuseStep 651257 = 488443) B488443
theorem B913481 : Blo 405769 913481 := bstep (se 2 (by rfl) ⟨342555, by rfl⟩ : syracuseStep 913481 = 685111) B685111
theorem B913535 : Blo 405769 913535 := bstep (se 1 (by rfl) ⟨685151, by rfl⟩ : syracuseStep 913535 = 1370303) B1370303
theorem B7565885 : Blo 405769 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B1471151 : Blo 405769 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B914615 : Blo 405769 914615 := bstep (se 1 (by rfl) ⟨685961, by rfl⟩ : syracuseStep 914615 = 1371923) B1371923
theorem B685307 : Blo 405769 685307 := bstep (se 1 (by rfl) ⟨513980, by rfl⟩ : syracuseStep 685307 = 1027961) B1027961
theorem B5207489 : Blo 405769 5207489 := bstep (se 2 (by rfl) ⟨1952808, by rfl⟩ : syracuseStep 5207489 = 3905617) B3905617
theorem B1373651 : Blo 405769 1373651 := bstep (se 1 (by rfl) ⟨1030238, by rfl⟩ : syracuseStep 1373651 = 2060477) B2060477
theorem B3471011 : Blo 405769 3471011 := bstep (se 1 (by rfl) ⟨2603258, by rfl⟩ : syracuseStep 3471011 = 5206517) B5206517
theorem B1373921 : Blo 405769 1373921 := bstep (se 2 (by rfl) ⟨515220, by rfl⟩ : syracuseStep 1373921 = 1030441) B1030441
theorem B915191 : Blo 405769 915191 := bstep (se 1 (by rfl) ⟨686393, by rfl⟩ : syracuseStep 915191 = 1372787) B1372787
theorem B915371 : Blo 405769 915371 := bstep (se 1 (by rfl) ⟨686528, by rfl⟩ : syracuseStep 915371 = 1373057) B1373057
theorem B915497 : Blo 405769 915497 := bstep (se 2 (by rfl) ⟨343311, by rfl⟩ : syracuseStep 915497 = 686623) B686623
theorem B1734959 : Blo 405769 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B3307823 : Blo 405769 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B915911 : Blo 405769 915911 := bstep (se 1 (by rfl) ⟨686933, by rfl⟩ : syracuseStep 915911 = 1373867) B1373867
theorem B916073 : Blo 405769 916073 := bstep (se 2 (by rfl) ⟨343527, by rfl⟩ : syracuseStep 916073 = 687055) B687055
theorem B457375 : Blo 405769 457375 := bstep (se 1 (by rfl) ⟨343031, by rfl⟩ : syracuseStep 457375 = 686063) B686063
theorem B916127 : Blo 405769 916127 := bstep (se 1 (by rfl) ⟨687095, by rfl⟩ : syracuseStep 916127 = 1374191) B1374191
theorem B916271 : Blo 405769 916271 := bstep (se 1 (by rfl) ⟨687203, by rfl⟩ : syracuseStep 916271 = 1374407) B1374407
theorem B2325419 : Blo 405769 2325419 := bstep (se 1 (by rfl) ⟨1744064, by rfl⟩ : syracuseStep 2325419 = 3488129) B3488129
theorem B916703 : Blo 405769 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B982297 : Blo 405769 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B916919 : Blo 405769 916919 := bstep (se 1 (by rfl) ⟨687689, by rfl⟩ : syracuseStep 916919 = 1375379) B1375379
theorem B2194877 : Blo 405769 2194877 := bstep (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) B823079
theorem B884243 : Blo 405769 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B917099 : Blo 405769 917099 := bstep (se 1 (by rfl) ⟨687824, by rfl⟩ : syracuseStep 917099 = 1375649) B1375649
theorem B1375919 : Blo 405769 1375919 := bstep (se 1 (by rfl) ⟨1031939, by rfl⟩ : syracuseStep 1375919 = 2063879) B2063879
theorem B458527 : Blo 405769 458527 := bstep (se 1 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 458527 = 687791) B687791
theorem B917369 : Blo 405769 917369 := bstep (se 2 (by rfl) ⟨344013, by rfl⟩ : syracuseStep 917369 = 688027) B688027
theorem B1245071 : Blo 405769 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B1310663 : Blo 405769 1310663 := bstep (se 1 (by rfl) ⟨982997, by rfl⟩ : syracuseStep 1310663 = 1965995) B1965995
theorem B917459 : Blo 405769 917459 := bstep (se 1 (by rfl) ⟨688094, by rfl⟩ : syracuseStep 917459 = 1376189) B1376189
theorem B1212833 : Blo 405769 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B2064851 : Blo 405769 2064851 := bstep (se 1 (by rfl) ⟨1548638, by rfl⟩ : syracuseStep 2064851 = 3097277) B3097277
theorem B2065175 : Blo 405769 2065175 := bstep (se 1 (by rfl) ⟨1548881, by rfl⟩ : syracuseStep 2065175 = 3097763) B3097763
theorem B689033 : Blo 405769 689033 := bstep (se 2 (by rfl) ⟨258387, by rfl⟩ : syracuseStep 689033 = 516775) B516775
theorem B2327561 : Blo 405769 2327561 := bstep (se 2 (by rfl) ⟨872835, by rfl⟩ : syracuseStep 2327561 = 1745671) B1745671
theorem B689465 : Blo 405769 689465 := bstep (se 2 (by rfl) ⟨258549, by rfl⟩ : syracuseStep 689465 = 517099) B517099
theorem B3475007 : Blo 405769 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B1378187 : Blo 405769 1378187 := bstep (se 1 (by rfl) ⟨1033640, by rfl⟩ : syracuseStep 1378187 = 2067281) B2067281
theorem B2066795 : Blo 405769 2066795 := bstep (se 1 (by rfl) ⟨1550096, by rfl⟩ : syracuseStep 2066795 = 3100193) B3100193
theorem B3082697 : Blo 405769 3082697 := bstep (se 2 (by rfl) ⟨1156011, by rfl⟩ : syracuseStep 3082697 = 2312023) B2312023
theorem B5245519 : Blo 405769 5245519 := bstep (se 1 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 5245519 = 7868279) B7868279
theorem B920303 : Blo 405769 920303 := bstep (se 1 (by rfl) ⟨690227, by rfl⟩ : syracuseStep 920303 = 1380455) B1380455
theorem B2329337 : Blo 405769 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B5245883 : Blo 405769 5245883 := bstep (se 1 (by rfl) ⟨3934412, by rfl⟩ : syracuseStep 5245883 = 7868825) B7868825
theorem B920681 : Blo 405769 920681 := bstep (se 2 (by rfl) ⟨345255, by rfl⟩ : syracuseStep 920681 = 690511) B690511
theorem B1379807 : Blo 405769 1379807 := bstep (se 1 (by rfl) ⟨1034855, by rfl⟩ : syracuseStep 1379807 = 2069711) B2069711
theorem B921311 : Blo 405769 921311 := bstep (se 1 (by rfl) ⟨690983, by rfl⟩ : syracuseStep 921311 = 1381967) B1381967
theorem B921563 : Blo 405769 921563 := bstep (se 1 (by rfl) ⟨691172, by rfl⟩ : syracuseStep 921563 = 1382345) B1382345
theorem B921743 : Blo 405769 921743 := bstep (se 1 (by rfl) ⟨691307, by rfl⟩ : syracuseStep 921743 = 1382615) B1382615
theorem B921833 : Blo 405769 921833 := bstep (se 2 (by rfl) ⟨345687, by rfl⟩ : syracuseStep 921833 = 691375) B691375
theorem B2330977 : Blo 405769 2330977 := bstep (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) B1748233
theorem B1381211 : Blo 405769 1381211 := bstep (se 1 (by rfl) ⟨1035908, by rfl⟩ : syracuseStep 1381211 = 2071817) B2071817
theorem B2069387 : Blo 405769 2069387 := bstep (se 1 (by rfl) ⟨1552040, by rfl⟩ : syracuseStep 2069387 = 3104081) B3104081
theorem B3478697 : Blo 405769 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B3937679 : Blo 405769 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B21108737 : Blo 405769 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B3807271 : Blo 405769 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B37623851 : Blo 405769 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B2365537 : Blo 405769 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B662143 : Blo 405769 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B2333711 : Blo 405769 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B3972563 : Blo 405769 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B3088043 : Blo 405769 3088043 := bstep (se 1 (by rfl) ⟨2316032, by rfl⟩ : syracuseStep 3088043 = 4632065) B4632065
theorem B4661225 : Blo 405769 4661225 := bstep (se 2 (by rfl) ⟨1747959, by rfl⟩ : syracuseStep 4661225 = 3495919) B3495919
theorem B434171 : Blo 405769 434171 := bstep (se 1 (by rfl) ⟨325628, by rfl⟩ : syracuseStep 434171 = 651257) B651257
theorem B37692161 : Blo 405769 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B3351305 : Blo 405769 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B1549793 : Blo 405769 1549793 := bstep (se 2 (by rfl) ⟨581172, by rfl⟩ : syracuseStep 1549793 = 1162345) B1162345
theorem B1156639 : Blo 405769 1156639 := bstep (se 1 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 1156639 = 1734959) B1734959
theorem B2205215 : Blo 405769 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B1549961 : Blo 405769 1549961 := bstep (se 2 (by rfl) ⟨581235, by rfl⟩ : syracuseStep 1549961 = 1162471) B1162471
theorem B149038841 : Blo 405769 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B1550279 : Blo 405769 1550279 := bstep (se 1 (by rfl) ⟨1162709, by rfl⟩ : syracuseStep 1550279 = 2325419) B2325419
theorem B3090959 : Blo 405769 3090959 := bstep (se 1 (by rfl) ⟨2318219, by rfl⟩ : syracuseStep 3090959 = 4636439) B4636439
theorem B830047 : Blo 405769 830047 := bstep (se 1 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 830047 = 1245071) B1245071
theorem B4205513 : Blo 405769 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B18918521 : Blo 405769 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B1158313 : Blo 405769 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B3911075 : Blo 405769 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B405787 : Blo 405769 405787 := bstep (se 1 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 405787 = 608681) B608681
theorem B406043 : Blo 405769 406043 := bstep (se 1 (by rfl) ⟨304532, by rfl⟩ : syracuseStep 406043 = 609065) B609065
theorem B406183 : Blo 405769 406183 := bstep (se 1 (by rfl) ⟨304637, by rfl⟩ : syracuseStep 406183 = 609275) B609275
theorem B406223 : Blo 405769 406223 := bstep (se 1 (by rfl) ⟨304667, by rfl⟩ : syracuseStep 406223 = 609335) B609335
theorem B1323755 : Blo 405769 1323755 := bstep (se 1 (by rfl) ⟨992816, by rfl⟩ : syracuseStep 1323755 = 1985633) B1985633
theorem B406303 : Blo 405769 406303 := bstep (se 1 (by rfl) ⟨304727, by rfl⟩ : syracuseStep 406303 = 609455) B609455
theorem B1749995 : Blo 405769 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B406783 : Blo 405769 406783 := bstep (se 1 (by rfl) ⟨305087, by rfl⟩ : syracuseStep 406783 = 610175) B610175
theorem B406911 : Blo 405769 406911 := bstep (se 1 (by rfl) ⟨305183, by rfl⟩ : syracuseStep 406911 = 610367) B610367
theorem B1160659 : Blo 405769 1160659 := bstep (se 1 (by rfl) ⟨870494, by rfl⟩ : syracuseStep 1160659 = 1740989) B1740989
theorem B407067 : Blo 405769 407067 := bstep (se 1 (by rfl) ⟨305300, by rfl⟩ : syracuseStep 407067 = 610601) B610601
theorem B407247 : Blo 405769 407247 := bstep (se 1 (by rfl) ⟨305435, by rfl⟩ : syracuseStep 407247 = 610871) B610871
theorem B2930539 : Blo 405769 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B407487 : Blo 405769 407487 := bstep (se 1 (by rfl) ⟨305615, by rfl⟩ : syracuseStep 407487 = 611231) B611231
theorem B604139 : Blo 405769 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B1259507 : Blo 405769 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B407615 : Blo 405769 407615 := bstep (se 1 (by rfl) ⟨305711, by rfl⟩ : syracuseStep 407615 = 611423) B611423
theorem B407655 : Blo 405769 407655 := bstep (se 1 (by rfl) ⟨305741, by rfl⟩ : syracuseStep 407655 = 611483) B611483
theorem B2472059 : Blo 405769 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B1161503 : Blo 405769 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B408111 : Blo 405769 408111 := bstep (se 1 (by rfl) ⟨306083, by rfl⟩ : syracuseStep 408111 = 612167) B612167
theorem B2210449 : Blo 405769 2210449 := bstep (se 2 (by rfl) ⟨828918, by rfl⟩ : syracuseStep 2210449 = 1657837) B1657837
theorem B408511 : Blo 405769 408511 := bstep (se 1 (by rfl) ⟨306383, by rfl⟩ : syracuseStep 408511 = 612767) B612767
theorem B408559 : Blo 405769 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B409055 : Blo 405769 409055 := bstep (se 1 (by rfl) ⟨306791, by rfl⟩ : syracuseStep 409055 = 613583) B613583
theorem B409135 : Blo 405769 409135 := bstep (se 1 (by rfl) ⟨306851, by rfl⟩ : syracuseStep 409135 = 613703) B613703
theorem B409243 : Blo 405769 409243 := bstep (se 1 (by rfl) ⟨306932, by rfl⟩ : syracuseStep 409243 = 613865) B613865
theorem B1031899 : Blo 405769 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B409339 : Blo 405769 409339 := bstep (se 1 (by rfl) ⟨307004, by rfl⟩ : syracuseStep 409339 = 614009) B614009
theorem B409503 : Blo 405769 409503 := bstep (se 1 (by rfl) ⟨307127, by rfl⟩ : syracuseStep 409503 = 614255) B614255
theorem B1032335 : Blo 405769 1032335 := bstep (se 1 (by rfl) ⟨774251, by rfl⟩ : syracuseStep 1032335 = 1548503) B1548503
theorem B2605385 : Blo 405769 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B1164395 : Blo 405769 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B1033337 : Blo 405769 1033337 := bstep (se 2 (by rfl) ⟨387501, by rfl⟩ : syracuseStep 1033337 = 775003) B775003
theorem B1656719 : Blo 405769 1656719 := bstep (se 1 (by rfl) ⟨1242539, by rfl⟩ : syracuseStep 1656719 = 2485079) B2485079
theorem B3262619 : Blo 405769 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B1165535 : Blo 405769 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B608747 : Blo 405769 608747 := bstep (se 1 (by rfl) ⟨456560, by rfl⟩ : syracuseStep 608747 = 913121) B913121
theorem B772649 : Blo 405769 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B608987 : Blo 405769 608987 := bstep (se 1 (by rfl) ⟨456740, by rfl⟩ : syracuseStep 608987 = 913481) B913481
theorem B609023 : Blo 405769 609023 := bstep (se 1 (by rfl) ⟨456767, by rfl⟩ : syracuseStep 609023 = 913535) B913535
theorem B1035575 : Blo 405769 1035575 := bstep (se 1 (by rfl) ⟨776681, by rfl⟩ : syracuseStep 1035575 = 1553363) B1553363
theorem B3919225 : Blo 405769 3919225 := bstep (se 2 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 3919225 = 2939419) B2939419
theorem B609743 : Blo 405769 609743 := bstep (se 1 (by rfl) ⟨457307, by rfl⟩ : syracuseStep 609743 = 914615) B914615
theorem B609833 : Blo 405769 609833 := bstep (se 2 (by rfl) ⟨228687, by rfl⟩ : syracuseStep 609833 = 457375) B457375
theorem B2314007 : Blo 405769 2314007 := bstep (se 1 (by rfl) ⟨1735505, by rfl⟩ : syracuseStep 2314007 = 3471011) B3471011
theorem B5853005 : Blo 405769 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B610127 : Blo 405769 610127 := bstep (se 1 (by rfl) ⟨457595, by rfl⟩ : syracuseStep 610127 = 915191) B915191
theorem B1036111 : Blo 405769 1036111 := bstep (se 1 (by rfl) ⟨777083, by rfl⟩ : syracuseStep 1036111 = 1554167) B1554167
theorem B610247 : Blo 405769 610247 := bstep (se 1 (by rfl) ⟨457685, by rfl⟩ : syracuseStep 610247 = 915371) B915371
theorem B610331 : Blo 405769 610331 := bstep (se 1 (by rfl) ⟨457748, by rfl⟩ : syracuseStep 610331 = 915497) B915497
theorem B774191 : Blo 405769 774191 := bstep (se 1 (by rfl) ⟨580643, by rfl⟩ : syracuseStep 774191 = 1161287) B1161287
theorem B1036415 : Blo 405769 1036415 := bstep (se 1 (by rfl) ⟨777311, by rfl⟩ : syracuseStep 1036415 = 1554623) B1554623
theorem B610607 : Blo 405769 610607 := bstep (se 1 (by rfl) ⟨457955, by rfl⟩ : syracuseStep 610607 = 915911) B915911
theorem B610715 : Blo 405769 610715 := bstep (se 1 (by rfl) ⟨458036, by rfl⟩ : syracuseStep 610715 = 916073) B916073
theorem B610751 : Blo 405769 610751 := bstep (se 1 (by rfl) ⟨458063, by rfl⟩ : syracuseStep 610751 = 916127) B916127
theorem B610847 : Blo 405769 610847 := bstep (se 1 (by rfl) ⟨458135, by rfl⟩ : syracuseStep 610847 = 916271) B916271
theorem B611135 : Blo 405769 611135 := bstep (se 1 (by rfl) ⟨458351, by rfl⟩ : syracuseStep 611135 = 916703) B916703
theorem B775079 : Blo 405769 775079 := bstep (se 1 (by rfl) ⟨581309, by rfl⟩ : syracuseStep 775079 = 1162619) B1162619
theorem B611279 : Blo 405769 611279 := bstep (se 1 (by rfl) ⟨458459, by rfl⟩ : syracuseStep 611279 = 916919) B916919
theorem B611369 : Blo 405769 611369 := bstep (se 2 (by rfl) ⟨229263, by rfl⟩ : syracuseStep 611369 = 458527) B458527
theorem B611399 : Blo 405769 611399 := bstep (se 1 (by rfl) ⟨458549, by rfl⟩ : syracuseStep 611399 = 917099) B917099
theorem B611579 : Blo 405769 611579 := bstep (se 1 (by rfl) ⟨458684, by rfl⟩ : syracuseStep 611579 = 917369) B917369
theorem B873775 : Blo 405769 873775 := bstep (se 1 (by rfl) ⟨655331, by rfl⟩ : syracuseStep 873775 = 1310663) B1310663
theorem B611639 : Blo 405769 611639 := bstep (se 1 (by rfl) ⟨458729, by rfl⟩ : syracuseStep 611639 = 917459) B917459
theorem B18044315 : Blo 405769 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B1660495 : Blo 405769 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B611945 : Blo 405769 611945 := bstep (se 2 (by rfl) ⟨229479, by rfl⟩ : syracuseStep 611945 = 458959) B458959
theorem B2086603 : Blo 405769 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B775975 : Blo 405769 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B14899211 : Blo 405769 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B612479 : Blo 405769 612479 := bstep (se 1 (by rfl) ⟨459359, by rfl⟩ : syracuseStep 612479 = 918719) B918719
theorem B4479113 : Blo 405769 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B612575 : Blo 405769 612575 := bstep (se 1 (by rfl) ⟨459431, by rfl⟩ : syracuseStep 612575 = 918863) B918863
theorem B514279 : Blo 405769 514279 := bstep (se 1 (by rfl) ⟨385709, by rfl⟩ : syracuseStep 514279 = 771419) B771419
theorem B612635 : Blo 405769 612635 := bstep (se 1 (by rfl) ⟨459476, by rfl⟩ : syracuseStep 612635 = 918953) B918953
theorem B2054483 : Blo 405769 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B612959 : Blo 405769 612959 := bstep (se 1 (by rfl) ⟨459719, by rfl⟩ : syracuseStep 612959 = 919439) B919439
theorem B2316923 : Blo 405769 2316923 := bstep (se 1 (by rfl) ⟨1737692, by rfl⟩ : syracuseStep 2316923 = 3475385) B3475385
theorem B613055 : Blo 405769 613055 := bstep (se 1 (by rfl) ⟨459791, by rfl⟩ : syracuseStep 613055 = 919583) B919583
theorem B613097 : Blo 405769 613097 := bstep (se 2 (by rfl) ⟨229911, by rfl⟩ : syracuseStep 613097 = 459823) B459823
theorem B2054969 : Blo 405769 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B613223 : Blo 405769 613223 := bstep (se 1 (by rfl) ⟨459917, by rfl⟩ : syracuseStep 613223 = 919835) B919835
theorem B613289 : Blo 405769 613289 := bstep (se 2 (by rfl) ⟨229983, by rfl⟩ : syracuseStep 613289 = 459967) B459967
theorem B613439 : Blo 405769 613439 := bstep (se 1 (by rfl) ⟨460079, by rfl⟩ : syracuseStep 613439 = 920159) B920159
theorem B613481 : Blo 405769 613481 := bstep (se 2 (by rfl) ⟨230055, by rfl⟩ : syracuseStep 613481 = 460111) B460111
theorem B613607 : Blo 405769 613607 := bstep (se 1 (by rfl) ⟨460205, by rfl⟩ : syracuseStep 613607 = 920411) B920411
theorem B1957115 : Blo 405769 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B777593 : Blo 405769 777593 := bstep (se 2 (by rfl) ⟨291597, by rfl⟩ : syracuseStep 777593 = 583195) B583195
theorem B2055617 : Blo 405769 2055617 := bstep (se 2 (by rfl) ⟨770856, by rfl⟩ : syracuseStep 2055617 = 1541713) B1541713
theorem B4415143 : Blo 405769 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B614111 : Blo 405769 614111 := bstep (se 1 (by rfl) ⟨460583, by rfl⟩ : syracuseStep 614111 = 921167) B921167
theorem B2056103 : Blo 405769 2056103 := bstep (se 1 (by rfl) ⟨1542077, by rfl⟩ : syracuseStep 2056103 = 3084155) B3084155
theorem B1007657 : Blo 405769 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B614441 : Blo 405769 614441 := bstep (se 2 (by rfl) ⟨230415, by rfl⟩ : syracuseStep 614441 = 460831) B460831
theorem B614471 : Blo 405769 614471 := bstep (se 1 (by rfl) ⟨460853, by rfl⟩ : syracuseStep 614471 = 921707) B921707
theorem B614507 : Blo 405769 614507 := bstep (se 1 (by rfl) ⟨460880, by rfl⟩ : syracuseStep 614507 = 921761) B921761
theorem B549055 : Blo 405769 549055 := bstep (se 1 (by rfl) ⟨411791, by rfl⟩ : syracuseStep 549055 = 823583) B823583
theorem B614591 : Blo 405769 614591 := bstep (se 1 (by rfl) ⟨460943, by rfl⟩ : syracuseStep 614591 = 921887) B921887
theorem B2122247 : Blo 405769 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2614457 : Blo 405769 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B1369601 : Blo 405769 1369601 := bstep (se 2 (by rfl) ⟨513600, by rfl⟩ : syracuseStep 1369601 = 1027201) B1027201
theorem B4941587 : Blo 405769 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B2058047 : Blo 405769 2058047 := bstep (se 1 (by rfl) ⟨1543535, by rfl⟩ : syracuseStep 2058047 = 3087071) B3087071
theorem B1468327 : Blo 405769 1468327 := bstep (se 1 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 1468327 = 2202491) B2202491
theorem B23619599 : Blo 405769 23619599 := bstep (se 1 (by rfl) ⟨17714699, by rfl⟩ : syracuseStep 23619599 = 35429399) B35429399
theorem B977231 : Blo 405769 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B1337719 : Blo 405769 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B1370681 : Blo 405769 1370681 := bstep (se 2 (by rfl) ⟨514005, by rfl⟩ : syracuseStep 1370681 = 1028011) B1028011
theorem B2058857 : Blo 405769 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B5106349 : Blo 405769 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B4419335 : Blo 405769 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B2977769 : Blo 405769 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B913463 : Blo 405769 913463 := bstep (se 1 (by rfl) ⟨685097, by rfl⟩ : syracuseStep 913463 = 1370195) B1370195
theorem B651359 : Blo 405769 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B2061935 : Blo 405769 2061935 := bstep (se 1 (by rfl) ⟨1546451, by rfl⟩ : syracuseStep 2061935 = 3092903) B3092903
theorem B5043923 : Blo 405769 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B980767 : Blo 405769 980767 := bstep (se 1 (by rfl) ⟨735575, by rfl⟩ : syracuseStep 980767 = 1471151) B1471151
theorem B456871 : Blo 405769 456871 := bstep (se 1 (by rfl) ⟨342653, by rfl⟩ : syracuseStep 456871 = 685307) B685307
theorem B686299 : Blo 405769 686299 := bstep (se 1 (by rfl) ⟨514724, by rfl⟩ : syracuseStep 686299 = 1029449) B1029449
theorem B3471659 : Blo 405769 3471659 := bstep (se 1 (by rfl) ⟨2603744, by rfl⟩ : syracuseStep 3471659 = 5207489) B5207489
theorem B915767 : Blo 405769 915767 := bstep (se 1 (by rfl) ⟨686825, by rfl⟩ : syracuseStep 915767 = 1373651) B1373651
theorem B1735111 : Blo 405769 1735111 := bstep (se 1 (by rfl) ⟨1301333, by rfl⟩ : syracuseStep 1735111 = 2602667) B2602667
theorem B686569 : Blo 405769 686569 := bstep (se 2 (by rfl) ⟨257463, by rfl⟩ : syracuseStep 686569 = 514927) B514927
theorem B915947 : Blo 405769 915947 := bstep (se 1 (by rfl) ⟨686960, by rfl⟩ : syracuseStep 915947 = 1373921) B1373921
theorem B2357981 : Blo 405769 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B1309729 : Blo 405769 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B490807 : Blo 405769 490807 := bstep (se 1 (by rfl) ⟨368105, by rfl⟩ : syracuseStep 490807 = 736211) B736211
theorem B687595 : Blo 405769 687595 := bstep (se 1 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 687595 = 1031393) B1031393
theorem B687737 : Blo 405769 687737 := bstep (se 2 (by rfl) ⟨257901, by rfl⟩ : syracuseStep 687737 = 515803) B515803
theorem B917279 : Blo 405769 917279 := bstep (se 1 (by rfl) ⟨687959, by rfl⟩ : syracuseStep 917279 = 1375919) B1375919
theorem B688223 : Blo 405769 688223 := bstep (se 1 (by rfl) ⟨516167, by rfl⟩ : syracuseStep 688223 = 1032335) B1032335
theorem B1736923 : Blo 405769 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B1736957 : Blo 405769 1736957 := bstep (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) B651359
theorem B1376567 : Blo 405769 1376567 := bstep (se 1 (by rfl) ⟨1032425, by rfl⟩ : syracuseStep 1376567 = 2064851) B2064851
theorem B1376783 : Blo 405769 1376783 := bstep (se 1 (by rfl) ⟨1032587, by rfl⟩ : syracuseStep 1376783 = 2065175) B2065175
theorem B459355 : Blo 405769 459355 := bstep (se 1 (by rfl) ⟨344516, by rfl⟩ : syracuseStep 459355 = 689033) B689033
theorem B688891 : Blo 405769 688891 := bstep (se 1 (by rfl) ⟨516668, by rfl⟩ : syracuseStep 688891 = 1033337) B1033337
theorem B459643 : Blo 405769 459643 := bstep (se 1 (by rfl) ⟨344732, by rfl⟩ : syracuseStep 459643 = 689465) B689465
theorem B918791 : Blo 405769 918791 := bstep (se 1 (by rfl) ⟨689093, by rfl⟩ : syracuseStep 918791 = 1378187) B1378187
theorem B1377863 : Blo 405769 1377863 := bstep (se 1 (by rfl) ⟨1033397, by rfl⟩ : syracuseStep 1377863 = 2066795) B2066795
theorem B1542185 : Blo 405769 1542185 := bstep (se 2 (by rfl) ⟨578319, by rfl⟩ : syracuseStep 1542185 = 1156639) B1156639
theorem B690383 : Blo 405769 690383 := bstep (se 1 (by rfl) ⟨517787, by rfl⟩ : syracuseStep 690383 = 1035575) B1035575
theorem B919871 : Blo 405769 919871 := bstep (se 1 (by rfl) ⟨689903, by rfl⟩ : syracuseStep 919871 = 1379807) B1379807
theorem B1542671 : Blo 405769 1542671 := bstep (se 1 (by rfl) ⟨1157003, by rfl⟩ : syracuseStep 1542671 = 2314007) B2314007
theorem B3902003 : Blo 405769 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B690943 : Blo 405769 690943 := bstep (se 1 (by rfl) ⟨518207, by rfl⟩ : syracuseStep 690943 = 1036415) B1036415
theorem B920807 : Blo 405769 920807 := bstep (se 1 (by rfl) ⟨690605, by rfl⟩ : syracuseStep 920807 = 1381211) B1381211
theorem B1379591 : Blo 405769 1379591 := bstep (se 1 (by rfl) ⟨1034693, by rfl⟩ : syracuseStep 1379591 = 2069387) B2069387
theorem B2625119 : Blo 405769 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B12029543 : Blo 405769 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B9932807 : Blo 405769 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B2986075 : Blo 405769 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B1544417 : Blo 405769 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B1544615 : Blo 405769 1544615 := bstep (se 1 (by rfl) ⟨1158461, by rfl⟩ : syracuseStep 1544615 = 2316923) B2316923
theorem B13177565 : Blo 405769 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B1381481 : Blo 405769 1381481 := bstep (se 2 (by rfl) ⟨518055, by rfl⟩ : syracuseStep 1381481 = 1036111) B1036111
theorem B1611037 : Blo 405769 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B1414831 : Blo 405769 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1742971 : Blo 405769 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B99359227 : Blo 405769 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B1547545 : Blo 405769 1547545 := bstep (se 2 (by rfl) ⟨580329, by rfl⟩ : syracuseStep 1547545 = 1160659) B1160659
theorem B3907385 : Blo 405769 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B3154049 : Blo 405769 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B1746305 : Blo 405769 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B1648039 : Blo 405769 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B7940717 : Blo 405769 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B1157789 : Blo 405769 1157789 := bstep (se 3 (by rfl) ⟨217085, by rfl⟩ : syracuseStep 1157789 = 434171) B434171
theorem B732073 : Blo 405769 732073 := bstep (se 2 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 732073 = 549055) B549055
theorem B1551707 : Blo 405769 1551707 := bstep (se 1 (by rfl) ⟨1163780, by rfl⟩ : syracuseStep 1551707 = 2327561) B2327561
theorem B405831 : Blo 405769 405831 := bstep (se 1 (by rfl) ⟨304373, by rfl⟩ : syracuseStep 405831 = 608747) B608747
theorem B405991 : Blo 405769 405991 := bstep (se 1 (by rfl) ⟨304493, by rfl⟩ : syracuseStep 405991 = 608987) B608987
theorem B1552891 : Blo 405769 1552891 := bstep (se 1 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 1552891 = 2329337) B2329337
theorem B406015 : Blo 405769 406015 := bstep (se 1 (by rfl) ⟨304511, by rfl⟩ : syracuseStep 406015 = 609023) B609023
theorem B406495 : Blo 405769 406495 := bstep (se 1 (by rfl) ⟨304871, by rfl⟩ : syracuseStep 406495 = 609743) B609743
theorem B406555 : Blo 405769 406555 := bstep (se 1 (by rfl) ⟨304916, by rfl⟩ : syracuseStep 406555 = 609833) B609833
theorem B406751 : Blo 405769 406751 := bstep (se 1 (by rfl) ⟨305063, by rfl⟩ : syracuseStep 406751 = 610127) B610127
theorem B406831 : Blo 405769 406831 := bstep (se 1 (by rfl) ⟨305123, by rfl⟩ : syracuseStep 406831 = 610247) B610247
theorem B406887 : Blo 405769 406887 := bstep (se 1 (by rfl) ⟨305165, by rfl⟩ : syracuseStep 406887 = 610331) B610331
theorem B407071 : Blo 405769 407071 := bstep (se 1 (by rfl) ⟨305303, by rfl⟩ : syracuseStep 407071 = 610607) B610607
theorem B407143 : Blo 405769 407143 := bstep (se 1 (by rfl) ⟨305357, by rfl⟩ : syracuseStep 407143 = 610715) B610715
theorem B407167 : Blo 405769 407167 := bstep (se 1 (by rfl) ⟨305375, by rfl⟩ : syracuseStep 407167 = 610751) B610751
theorem B407231 : Blo 405769 407231 := bstep (se 1 (by rfl) ⟨305423, by rfl⟩ : syracuseStep 407231 = 610847) B610847
theorem B1783625 : Blo 405769 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B407423 : Blo 405769 407423 := bstep (se 1 (by rfl) ⟨305567, by rfl⟩ : syracuseStep 407423 = 611135) B611135
theorem B407519 : Blo 405769 407519 := bstep (se 1 (by rfl) ⟨305639, by rfl⟩ : syracuseStep 407519 = 611279) B611279
theorem B407579 : Blo 405769 407579 := bstep (se 1 (by rfl) ⟨305684, by rfl⟩ : syracuseStep 407579 = 611369) B611369
theorem B407599 : Blo 405769 407599 := bstep (se 1 (by rfl) ⟨305699, by rfl⟩ : syracuseStep 407599 = 611399) B611399
theorem B6994025 : Blo 405769 6994025 := bstep (se 2 (by rfl) ⟨2622759, by rfl⟩ : syracuseStep 6994025 = 5245519) B5245519
theorem B407719 : Blo 405769 407719 := bstep (se 1 (by rfl) ⟨305789, by rfl⟩ : syracuseStep 407719 = 611579) B611579
theorem B407759 : Blo 405769 407759 := bstep (se 1 (by rfl) ⟨305819, by rfl⟩ : syracuseStep 407759 = 611639) B611639
theorem B407963 : Blo 405769 407963 := bstep (se 1 (by rfl) ⟨305972, by rfl⟩ : syracuseStep 407963 = 611945) B611945
theorem B14072491 : Blo 405769 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B25082567 : Blo 405769 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B408319 : Blo 405769 408319 := bstep (se 1 (by rfl) ⟨306239, by rfl⟩ : syracuseStep 408319 = 612479) B612479
theorem B408383 : Blo 405769 408383 := bstep (se 1 (by rfl) ⟨306287, by rfl⟩ : syracuseStep 408383 = 612575) B612575
theorem B408423 : Blo 405769 408423 := bstep (se 1 (by rfl) ⟨306317, by rfl⟩ : syracuseStep 408423 = 612635) B612635
theorem B408639 : Blo 405769 408639 := bstep (se 1 (by rfl) ⟨306479, by rfl⟩ : syracuseStep 408639 = 612959) B612959
theorem B408703 : Blo 405769 408703 := bstep (se 1 (by rfl) ⟨306527, by rfl⟩ : syracuseStep 408703 = 613055) B613055
theorem B408731 : Blo 405769 408731 := bstep (se 1 (by rfl) ⟨306548, by rfl⟩ : syracuseStep 408731 = 613097) B613097
theorem B5225633 : Blo 405769 5225633 := bstep (se 2 (by rfl) ⟨1959612, by rfl⟩ : syracuseStep 5225633 = 3919225) B3919225
theorem B408815 : Blo 405769 408815 := bstep (se 1 (by rfl) ⟨306611, by rfl⟩ : syracuseStep 408815 = 613223) B613223
theorem B408859 : Blo 405769 408859 := bstep (se 1 (by rfl) ⟨306644, by rfl⟩ : syracuseStep 408859 = 613289) B613289
theorem B1555807 : Blo 405769 1555807 := bstep (se 1 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 1555807 = 2333711) B2333711
theorem B408959 : Blo 405769 408959 := bstep (se 1 (by rfl) ⟨306719, by rfl⟩ : syracuseStep 408959 = 613439) B613439
theorem B408987 : Blo 405769 408987 := bstep (se 1 (by rfl) ⟨306740, by rfl⟩ : syracuseStep 408987 = 613481) B613481
theorem B409071 : Blo 405769 409071 := bstep (se 1 (by rfl) ⟨306803, by rfl⟩ : syracuseStep 409071 = 613607) B613607
theorem B409407 : Blo 405769 409407 := bstep (se 1 (by rfl) ⟨307055, by rfl⟩ : syracuseStep 409407 = 614111) B614111
theorem B3358685 : Blo 405769 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B671771 : Blo 405769 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B409627 : Blo 405769 409627 := bstep (se 1 (by rfl) ⟨307220, by rfl⟩ : syracuseStep 409627 = 614441) B614441
theorem B409647 : Blo 405769 409647 := bstep (se 1 (by rfl) ⟨307235, by rfl⟩ : syracuseStep 409647 = 614471) B614471
theorem B409671 : Blo 405769 409671 := bstep (se 1 (by rfl) ⟨307253, by rfl⟩ : syracuseStep 409671 = 614507) B614507
theorem B409727 : Blo 405769 409727 := bstep (se 1 (by rfl) ⟨307295, by rfl⟩ : syracuseStep 409727 = 614591) B614591
theorem B8700317 : Blo 405769 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B1033195 : Blo 405769 1033195 := bstep (se 1 (by rfl) ⟨774896, by rfl⟩ : syracuseStep 1033195 = 1549793) B1549793
theorem B1033307 : Blo 405769 1033307 := bstep (se 1 (by rfl) ⟨774980, by rfl⟩ : syracuseStep 1033307 = 1549961) B1549961
theorem B1033519 : Blo 405769 1033519 := bstep (se 1 (by rfl) ⟨775139, by rfl⟩ : syracuseStep 1033519 = 1550279) B1550279
theorem B15746399 : Blo 405769 15746399 := bstep (se 1 (by rfl) ⟨11809799, by rfl⟩ : syracuseStep 15746399 = 23619599) B23619599
theorem B1165033 : Blo 405769 1165033 := bstep (se 2 (by rfl) ⟨436887, by rfl⟩ : syracuseStep 1165033 = 873775) B873775
theorem B2803675 : Blo 405769 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B2213993 : Blo 405769 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B2607383 : Blo 405769 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B1034633 : Blo 405769 1034633 := bstep (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) B775975
theorem B608975 : Blo 405769 608975 := bstep (se 1 (by rfl) ⟨456731, by rfl⟩ : syracuseStep 608975 = 913463) B913463
theorem B609161 : Blo 405769 609161 := bstep (se 2 (by rfl) ⟨228435, by rfl⟩ : syracuseStep 609161 = 456871) B456871
theorem B2313481 : Blo 405769 2313481 := bstep (se 2 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 2313481 = 1735111) B1735111
theorem B1166663 : Blo 405769 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B11128549 : Blo 405769 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B3362615 : Blo 405769 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B5230757 : Blo 405769 5230757 := bstep (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) B980767
theorem B774335 : Blo 405769 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B2314439 : Blo 405769 2314439 := bstep (se 1 (by rfl) ⟨1735829, by rfl⟩ : syracuseStep 2314439 = 3471659) B3471659
theorem B610511 : Blo 405769 610511 := bstep (se 1 (by rfl) ⟨457883, by rfl⟩ : syracuseStep 610511 = 915767) B915767
theorem B610631 : Blo 405769 610631 := bstep (se 1 (by rfl) ⟨457973, by rfl⟩ : syracuseStep 610631 = 915947) B915947
theorem B5886857 : Blo 405769 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B611519 : Blo 405769 611519 := bstep (se 1 (by rfl) ⟨458639, by rfl⟩ : syracuseStep 611519 = 917279) B917279
theorem B808555 : Blo 405769 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B2316671 : Blo 405769 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B1104479 : Blo 405769 1104479 := bstep (se 1 (by rfl) ⟨828359, by rfl⟩ : syracuseStep 1104479 = 1656719) B1656719
theorem B777023 : Blo 405769 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B2055131 : Blo 405769 2055131 := bstep (se 1 (by rfl) ⟨1541348, by rfl⟩ : syracuseStep 2055131 = 3082697) B3082697
theorem B515099 : Blo 405769 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B613535 : Blo 405769 613535 := bstep (se 1 (by rfl) ⟨460151, by rfl⟩ : syracuseStep 613535 = 920303) B920303
theorem B3497255 : Blo 405769 3497255 := bstep (se 1 (by rfl) ⟨2622941, by rfl⟩ : syracuseStep 3497255 = 5245883) B5245883
theorem B8936813 : Blo 405769 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B613787 : Blo 405769 613787 := bstep (se 1 (by rfl) ⟨460340, by rfl⟩ : syracuseStep 613787 = 920681) B920681
theorem B614207 : Blo 405769 614207 := bstep (se 1 (by rfl) ⟨460655, by rfl⟩ : syracuseStep 614207 = 921311) B921311
theorem B1957769 : Blo 405769 1957769 := bstep (se 2 (by rfl) ⟨734163, by rfl⟩ : syracuseStep 1957769 = 1468327) B1468327
theorem B614375 : Blo 405769 614375 := bstep (se 1 (by rfl) ⟨460781, by rfl⟩ : syracuseStep 614375 = 921563) B921563
theorem B516127 : Blo 405769 516127 := bstep (se 1 (by rfl) ⟨387095, by rfl⟩ : syracuseStep 516127 = 774191) B774191
theorem B614495 : Blo 405769 614495 := bstep (se 1 (by rfl) ⟨460871, by rfl⟩ : syracuseStep 614495 = 921743) B921743
theorem B614555 : Blo 405769 614555 := bstep (se 1 (by rfl) ⟨460916, by rfl⟩ : syracuseStep 614555 = 921833) B921833
theorem B3105053 : Blo 405769 3105053 := bstep (se 3 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 3105053 = 1164395) B1164395
theorem B516719 : Blo 405769 516719 := bstep (se 1 (by rfl) ⟨387539, by rfl⟩ : syracuseStep 516719 = 775079) B775079
theorem B2319131 : Blo 405769 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B1106729 : Blo 405769 1106729 := bstep (se 2 (by rfl) ⟨415023, by rfl⟩ : syracuseStep 1106729 = 830047) B830047
theorem B6808465 : Blo 405769 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B1369655 : Blo 405769 1369655 := bstep (se 1 (by rfl) ⟨1027241, by rfl⟩ : syracuseStep 1369655 = 2054483) B2054483
theorem B1369979 : Blo 405769 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B1304743 : Blo 405769 1304743 := bstep (se 1 (by rfl) ⟨978557, by rfl⟩ : syracuseStep 1304743 = 1957115) B1957115
theorem B518395 : Blo 405769 518395 := bstep (se 1 (by rfl) ⟨388796, by rfl⟩ : syracuseStep 518395 = 777593) B777593
theorem B1370411 : Blo 405769 1370411 := bstep (se 1 (by rfl) ⟨1027808, by rfl⟩ : syracuseStep 1370411 = 2055617) B2055617
theorem B2648375 : Blo 405769 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B2058695 : Blo 405769 2058695 := bstep (se 1 (by rfl) ⟨1544021, by rfl⟩ : syracuseStep 2058695 = 3088043) B3088043
theorem B1370735 : Blo 405769 1370735 := bstep (se 1 (by rfl) ⟨1028051, by rfl⟩ : syracuseStep 1370735 = 2056103) B2056103
theorem B3107483 : Blo 405769 3107483 := bstep (se 1 (by rfl) ⟨2330612, by rfl⟩ : syracuseStep 3107483 = 4661225) B4661225
theorem B3107969 : Blo 405769 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B25128107 : Blo 405769 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B913067 : Blo 405769 913067 := bstep (se 1 (by rfl) ⟨684800, by rfl⟩ : syracuseStep 913067 = 1369601) B1369601
theorem B1470143 : Blo 405769 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B1372031 : Blo 405769 1372031 := bstep (se 1 (by rfl) ⟨1029023, by rfl⟩ : syracuseStep 1372031 = 2058047) B2058047
theorem B651487 : Blo 405769 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B2060639 : Blo 405769 2060639 := bstep (se 1 (by rfl) ⟨1545479, by rfl⟩ : syracuseStep 2060639 = 3090959) B3090959
theorem B913787 : Blo 405769 913787 := bstep (se 1 (by rfl) ⟨685340, by rfl⟩ : syracuseStep 913787 = 1370681) B1370681
theorem B1372571 : Blo 405769 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B12612347 : Blo 405769 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B2946223 : Blo 405769 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B5076361 : Blo 405769 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B915065 : Blo 405769 915065 := bstep (se 2 (by rfl) ⟨343149, by rfl⟩ : syracuseStep 915065 = 686299) B686299
theorem B685705 : Blo 405769 685705 := bstep (se 2 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 685705 = 514279) B514279
theorem B882503 : Blo 405769 882503 := bstep (se 1 (by rfl) ⟨661877, by rfl⟩ : syracuseStep 882503 = 1323755) B1323755
theorem B915425 : Blo 405769 915425 := bstep (se 2 (by rfl) ⟨343284, by rfl⟩ : syracuseStep 915425 = 686569) B686569
theorem B882857 : Blo 405769 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B2947265 : Blo 405769 2947265 := bstep (se 2 (by rfl) ⟨1105224, by rfl⟩ : syracuseStep 2947265 = 2210449) B2210449
theorem B1374623 : Blo 405769 1374623 := bstep (se 1 (by rfl) ⟨1030967, by rfl⟩ : syracuseStep 1374623 = 2061935) B2061935
theorem B654409 : Blo 405769 654409 := bstep (se 2 (by rfl) ⟨245403, by rfl⟩ : syracuseStep 654409 = 490807) B490807
theorem B1571987 : Blo 405769 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B916793 : Blo 405769 916793 := bstep (se 2 (by rfl) ⟨343797, by rfl⟩ : syracuseStep 916793 = 687595) B687595
theorem B1375865 : Blo 405769 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B458491 : Blo 405769 458491 := bstep (se 1 (by rfl) ⟨343868, by rfl⟩ : syracuseStep 458491 = 687737) B687737
theorem B688169 : Blo 405769 688169 := bstep (se 2 (by rfl) ⟨258063, by rfl⟩ : syracuseStep 688169 = 516127) B516127
theorem B458815 : Blo 405769 458815 := bstep (se 1 (by rfl) ⟨344111, by rfl⟩ : syracuseStep 458815 = 688223) B688223
theorem B917711 : Blo 405769 917711 := bstep (se 1 (by rfl) ⟨688283, by rfl⟩ : syracuseStep 917711 = 1376567) B1376567
theorem B5800211 : Blo 405769 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B917855 : Blo 405769 917855 := bstep (se 1 (by rfl) ⟨688391, by rfl⟩ : syracuseStep 917855 = 1376783) B1376783
theorem B15925733 : Blo 405769 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B688871 : Blo 405769 688871 := bstep (se 1 (by rfl) ⟨516653, by rfl⟩ : syracuseStep 688871 = 1033307) B1033307
theorem B918521 : Blo 405769 918521 := bstep (se 2 (by rfl) ⟨344445, by rfl⟩ : syracuseStep 918521 = 688891) B688891
theorem B918575 : Blo 405769 918575 := bstep (se 1 (by rfl) ⟨688931, by rfl⟩ : syracuseStep 918575 = 1377863) B1377863
theorem B9077953 : Blo 405769 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B1377593 : Blo 405769 1377593 := bstep (se 2 (by rfl) ⟨516597, by rfl⟩ : syracuseStep 1377593 = 1033195) B1033195
theorem B1475995 : Blo 405769 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B460255 : Blo 405769 460255 := bstep (se 1 (by rfl) ⟨345191, by rfl⟩ : syracuseStep 460255 = 690383) B690383
theorem B1738255 : Blo 405769 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B689755 : Blo 405769 689755 := bstep (se 1 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 689755 = 1034633) B1034633
theorem B1377917 : Blo 405769 1377917 := bstep (se 3 (by rfl) ⟨258359, by rfl⟩ : syracuseStep 1377917 = 516719) B516719
theorem B1378025 : Blo 405769 1378025 := bstep (se 2 (by rfl) ⟨516759, by rfl⟩ : syracuseStep 1378025 = 1033519) B1033519
theorem B2197385 : Blo 405769 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B919727 : Blo 405769 919727 := bstep (se 1 (by rfl) ⟨689795, by rfl⟩ : syracuseStep 919727 = 1379591) B1379591
theorem B3738233 : Blo 405769 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B6621871 : Blo 405769 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B1542959 : Blo 405769 1542959 := bstep (se 1 (by rfl) ⟨1157219, by rfl⟩ : syracuseStep 1542959 = 2314439) B2314439
theorem B1739657 : Blo 405769 1739657 := bstep (se 2 (by rfl) ⟨652371, by rfl⟩ : syracuseStep 1739657 = 1304743) B1304743
theorem B691193 : Blo 405769 691193 := bstep (se 2 (by rfl) ⟨259197, by rfl⟩ : syracuseStep 691193 = 518395) B518395
theorem B8785043 : Blo 405769 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B920987 : Blo 405769 920987 := bstep (se 1 (by rfl) ⟨690740, by rfl⟩ : syracuseStep 920987 = 1381481) B1381481
theorem B921257 : Blo 405769 921257 := bstep (se 2 (by rfl) ⟨345471, by rfl⟩ : syracuseStep 921257 = 690943) B690943
theorem B1544447 : Blo 405769 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B3084641 : Blo 405769 3084641 := bstep (se 2 (by rfl) ⟨1156740, by rfl⟩ : syracuseStep 3084641 = 2313481) B2313481
theorem B4756333 : Blo 405769 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B2331503 : Blo 405769 2331503 := bstep (se 1 (by rfl) ⟨1748627, by rfl⟩ : syracuseStep 2331503 = 3497255) B3497255
theorem B2102699 : Blo 405769 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B2070035 : Blo 405769 2070035 := bstep (se 1 (by rfl) ⟨1552526, by rfl⟩ : syracuseStep 2070035 = 3105053) B3105053
theorem B1546087 : Blo 405769 1546087 := bstep (se 1 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 1546087 = 2319131) B2319131
theorem B2070521 : Blo 405769 2070521 := bstep (se 2 (by rfl) ⟨776445, by rfl⟩ : syracuseStep 2070521 = 1552891) B1552891
theorem B2071655 : Blo 405769 2071655 := bstep (se 1 (by rfl) ⟨1553741, by rfl⟩ : syracuseStep 2071655 = 3107483) B3107483
theorem B2071979 : Blo 405769 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B16752071 : Blo 405769 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B4662683 : Blo 405769 4662683 := bstep (se 1 (by rfl) ⟨3497012, by rfl⟩ : syracuseStep 4662683 = 6994025) B6994025
theorem B2074409 : Blo 405769 2074409 := bstep (se 2 (by rfl) ⟨777903, by rfl⟩ : syracuseStep 2074409 = 1555807) B1555807
theorem B16721711 : Blo 405769 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B3483755 : Blo 405769 3483755 := bstep (se 1 (by rfl) ⟨2612816, by rfl⟩ : syracuseStep 3483755 = 5225633) B5225633
theorem B2239123 : Blo 405769 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B1157971 : Blo 405769 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B10497599 : Blo 405769 10497599 := bstep (se 1 (by rfl) ⟨7873199, by rfl⟩ : syracuseStep 10497599 = 15746399) B15746399
theorem B1028123 : Blo 405769 1028123 := bstep (se 1 (by rfl) ⟨771092, by rfl⟩ : syracuseStep 1028123 = 1542185) B1542185
theorem B1028447 : Blo 405769 1028447 := bstep (se 1 (by rfl) ⟨771335, by rfl⟩ : syracuseStep 1028447 = 1542671) B1542671
theorem B2601335 : Blo 405769 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B405983 : Blo 405769 405983 := bstep (se 1 (by rfl) ⟨304487, by rfl⟩ : syracuseStep 405983 = 608975) B608975
theorem B406107 : Blo 405769 406107 := bstep (se 1 (by rfl) ⟨304580, by rfl⟩ : syracuseStep 406107 = 609161) B609161
theorem B143471573 : Blo 405769 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B1553377 : Blo 405769 1553377 := bstep (se 2 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 1553377 = 1165033) B1165033
theorem B1750079 : Blo 405769 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B3487171 : Blo 405769 3487171 := bstep (se 1 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 3487171 = 5230757) B5230757
theorem B407007 : Blo 405769 407007 := bstep (se 1 (by rfl) ⟨305255, by rfl⟩ : syracuseStep 407007 = 610511) B610511
theorem B1029611 : Blo 405769 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B407087 : Blo 405769 407087 := bstep (se 1 (by rfl) ⟨305315, by rfl⟩ : syracuseStep 407087 = 610631) B610631
theorem B1029743 : Blo 405769 1029743 := bstep (se 1 (by rfl) ⟨772307, by rfl⟩ : syracuseStep 1029743 = 1544615) B1544615
theorem B407679 : Blo 405769 407679 := bstep (se 1 (by rfl) ⟨305759, by rfl⟩ : syracuseStep 407679 = 611519) B611519
theorem B736319 : Blo 405769 736319 := bstep (se 1 (by rfl) ⟨552239, by rfl⟩ : syracuseStep 736319 = 1104479) B1104479
theorem B409023 : Blo 405769 409023 := bstep (se 1 (by rfl) ⟨306767, by rfl⟩ : syracuseStep 409023 = 613535) B613535
theorem B409191 : Blo 405769 409191 := bstep (se 1 (by rfl) ⟨306893, by rfl⟩ : syracuseStep 409191 = 613787) B613787
theorem B2604923 : Blo 405769 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B409471 : Blo 405769 409471 := bstep (se 1 (by rfl) ⟨307103, by rfl⟩ : syracuseStep 409471 = 614207) B614207
theorem B409583 : Blo 405769 409583 := bstep (se 1 (by rfl) ⟨307187, by rfl⟩ : syracuseStep 409583 = 614375) B614375
theorem B409663 : Blo 405769 409663 := bstep (se 1 (by rfl) ⟨307247, by rfl⟩ : syracuseStep 409663 = 614495) B614495
theorem B409703 : Blo 405769 409703 := bstep (se 1 (by rfl) ⟨307277, by rfl⟩ : syracuseStep 409703 = 614555) B614555
theorem B868649 : Blo 405769 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B737819 : Blo 405769 737819 := bstep (se 1 (by rfl) ⟨553364, by rfl⟩ : syracuseStep 737819 = 1106729) B1106729
theorem B1164203 : Blo 405769 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B2148049 : Blo 405769 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B5293811 : Blo 405769 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B771859 : Blo 405769 771859 := bstep (se 1 (by rfl) ⟨578894, by rfl⟩ : syracuseStep 771859 = 1157789) B1157789
theorem B6768481 : Blo 405769 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B1034471 : Blo 405769 1034471 := bstep (se 1 (by rfl) ⟨775853, by rfl⟩ : syracuseStep 1034471 = 1551707) B1551707
theorem B1886441 : Blo 405769 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B608711 : Blo 405769 608711 := bstep (se 1 (by rfl) ⟨456533, by rfl⟩ : syracuseStep 608711 = 913067) B913067
theorem B609191 : Blo 405769 609191 := bstep (se 1 (by rfl) ⟨456893, by rfl⟩ : syracuseStep 609191 = 913787) B913787
theorem B8408231 : Blo 405769 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B18763321 : Blo 405769 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B610043 : Blo 405769 610043 := bstep (se 1 (by rfl) ⟨457532, by rfl⟩ : syracuseStep 610043 = 915065) B915065
theorem B610283 : Blo 405769 610283 := bstep (se 1 (by rfl) ⟨457712, by rfl⟩ : syracuseStep 610283 = 915425) B915425
theorem B872545 : Blo 405769 872545 := bstep (se 2 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 872545 = 654409) B654409
theorem B611195 : Blo 405769 611195 := bstep (se 1 (by rfl) ⟨458396, by rfl⟩ : syracuseStep 611195 = 916793) B916793
theorem B611321 : Blo 405769 611321 := bstep (se 2 (by rfl) ⟨229245, by rfl⟩ : syracuseStep 611321 = 458491) B458491
theorem B1791389 : Blo 405769 1791389 := bstep (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) B671771
theorem B2315897 : Blo 405769 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B612473 : Blo 405769 612473 := bstep (se 2 (by rfl) ⟨229677, by rfl⟩ : syracuseStep 612473 = 459355) B459355
theorem B612527 : Blo 405769 612527 := bstep (se 1 (by rfl) ⟨459395, by rfl⟩ : syracuseStep 612527 = 918791) B918791
theorem B612857 : Blo 405769 612857 := bstep (se 2 (by rfl) ⟨229821, by rfl⟩ : syracuseStep 612857 = 459643) B459643
theorem B613247 : Blo 405769 613247 := bstep (se 1 (by rfl) ⟨459935, by rfl⟩ : syracuseStep 613247 = 919871) B919871
theorem B613871 : Blo 405769 613871 := bstep (se 1 (by rfl) ⟨460403, by rfl⟩ : syracuseStep 613871 = 920807) B920807
theorem B777775 : Blo 405769 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B8019695 : Blo 405769 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B529915877 : Blo 405769 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B516223 : Blo 405769 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B3924571 : Blo 405769 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B976097 : Blo 405769 976097 := bstep (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) B732073
theorem B518015 : Blo 405769 518015 := bstep (se 1 (by rfl) ⟨388511, by rfl⟩ : syracuseStep 518015 = 777023) B777023
theorem B1370087 : Blo 405769 1370087 := bstep (se 1 (by rfl) ⟨1027565, by rfl⟩ : syracuseStep 1370087 = 2055131) B2055131
theorem B5957875 : Blo 405769 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B14838065 : Blo 405769 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B1305179 : Blo 405769 1305179 := bstep (se 1 (by rfl) ⟨978884, by rfl⟩ : syracuseStep 1305179 = 1957769) B1957769
theorem B2354285 : Blo 405769 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B913103 : Blo 405769 913103 := bstep (se 1 (by rfl) ⟨684827, by rfl⟩ : syracuseStep 913103 = 1369655) B1369655
theorem B913319 : Blo 405769 913319 := bstep (se 1 (by rfl) ⟨684989, by rfl⟩ : syracuseStep 913319 = 1369979) B1369979
theorem B913607 : Blo 405769 913607 := bstep (se 1 (by rfl) ⟨685205, by rfl⟩ : syracuseStep 913607 = 1370411) B1370411
theorem B1765583 : Blo 405769 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B3928297 : Blo 405769 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B1372463 : Blo 405769 1372463 := bstep (se 1 (by rfl) ⟨1029347, by rfl⟩ : syracuseStep 1372463 = 2058695) B2058695
theorem B913823 : Blo 405769 913823 := bstep (se 1 (by rfl) ⟨685367, by rfl⟩ : syracuseStep 913823 = 1370735) B1370735
theorem B1078073 : Blo 405769 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B914273 : Blo 405769 914273 := bstep (se 2 (by rfl) ⟨342852, by rfl⟩ : syracuseStep 914273 = 685705) B685705
theorem B980095 : Blo 405769 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B914687 : Blo 405769 914687 := bstep (se 1 (by rfl) ⟨686015, by rfl⟩ : syracuseStep 914687 = 1372031) B1372031
theorem B1373597 : Blo 405769 1373597 := bstep (se 3 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 1373597 = 515099) B515099
theorem B2323961 : Blo 405769 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B1373759 : Blo 405769 1373759 := bstep (se 1 (by rfl) ⟨1030319, by rfl⟩ : syracuseStep 1373759 = 2060639) B2060639
theorem B915047 : Blo 405769 915047 := bstep (se 1 (by rfl) ⟨686285, by rfl⟩ : syracuseStep 915047 = 1372571) B1372571
theorem B588335 : Blo 405769 588335 := bstep (se 1 (by rfl) ⟨441251, by rfl⟩ : syracuseStep 588335 = 882503) B882503
theorem B1964843 : Blo 405769 1964843 := bstep (se 1 (by rfl) ⟨1473632, by rfl⟩ : syracuseStep 1964843 = 2947265) B2947265
theorem B916415 : Blo 405769 916415 := bstep (se 1 (by rfl) ⟨687311, by rfl⟩ : syracuseStep 916415 = 1374623) B1374623
theorem B2063393 : Blo 405769 2063393 := bstep (se 2 (by rfl) ⟨773772, by rfl⟩ : syracuseStep 2063393 = 1547545) B1547545
theorem B1047991 : Blo 405769 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B917243 : Blo 405769 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B458779 : Blo 405769 458779 := bstep (se 1 (by rfl) ⟨344084, by rfl⟩ : syracuseStep 458779 = 688169) B688169
theorem B688297 : Blo 405769 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B3866807 : Blo 405769 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B10617155 : Blo 405769 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B491879 : Blo 405769 491879 := bstep (se 1 (by rfl) ⟨368909, by rfl⟩ : syracuseStep 491879 = 737819) B737819
theorem B459247 : Blo 405769 459247 := bstep (se 1 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 459247 = 688871) B688871
theorem B918395 : Blo 405769 918395 := bstep (se 1 (by rfl) ⟨688796, by rfl⟩ : syracuseStep 918395 = 1377593) B1377593
theorem B918611 : Blo 405769 918611 := bstep (se 1 (by rfl) ⟨688958, by rfl⟩ : syracuseStep 918611 = 1377917) B1377917
theorem B918683 : Blo 405769 918683 := bstep (se 1 (by rfl) ⟨689012, by rfl⟩ : syracuseStep 918683 = 1378025) B1378025
theorem B689647 : Blo 405769 689647 := bstep (se 1 (by rfl) ⟨517235, by rfl⟩ : syracuseStep 689647 = 1034471) B1034471
theorem B2492155 : Blo 405769 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B1967993 : Blo 405769 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B460795 : Blo 405769 460795 := bstep (se 1 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 460795 = 691193) B691193
theorem B5605487 : Blo 405769 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B919673 : Blo 405769 919673 := bstep (se 2 (by rfl) ⟨344877, by rfl⟩ : syracuseStep 919673 = 689755) B689755
theorem B20122037 : Blo 405769 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B2985497 : Blo 405769 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B1380023 : Blo 405769 1380023 := bstep (se 1 (by rfl) ⟨1035017, by rfl⟩ : syracuseStep 1380023 = 2070035) B2070035
theorem B1543931 : Blo 405769 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B1543961 : Blo 405769 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B1380347 : Blo 405769 1380347 := bstep (se 1 (by rfl) ⟨1035260, by rfl⟩ : syracuseStep 1380347 = 2070521) B2070521
theorem B1381103 : Blo 405769 1381103 := bstep (se 1 (by rfl) ⟨1035827, by rfl⟩ : syracuseStep 1381103 = 2071655) B2071655
theorem B1381319 : Blo 405769 1381319 := bstep (se 1 (by rfl) ⟨1035989, by rfl⟩ : syracuseStep 1381319 = 2071979) B2071979
theorem B1381373 : Blo 405769 1381373 := bstep (se 3 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 1381373 = 518015) B518015
theorem B353277251 : Blo 405769 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B1382939 : Blo 405769 1382939 := bstep (se 1 (by rfl) ⟨1037204, by rfl⟩ : syracuseStep 1382939 = 2074409) B2074409
theorem B11147807 : Blo 405769 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B2071169 : Blo 405769 2071169 := bstep (se 2 (by rfl) ⟨776688, by rfl⟩ : syracuseStep 2071169 = 1553377) B1553377
theorem B1549307 : Blo 405769 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B12103937 : Blo 405769 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B405807 : Blo 405769 405807 := bstep (se 1 (by rfl) ⟨304355, by rfl⟩ : syracuseStep 405807 = 608711) B608711
theorem B1028639 : Blo 405769 1028639 := bstep (se 1 (by rfl) ⟨771479, by rfl⟩ : syracuseStep 1028639 = 1542959) B1542959
theorem B1159771 : Blo 405769 1159771 := bstep (se 1 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 1159771 = 1739657) B1739657
theorem B406127 : Blo 405769 406127 := bstep (se 1 (by rfl) ⟨304595, by rfl⟩ : syracuseStep 406127 = 609191) B609191
theorem B2864065 : Blo 405769 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1029145 : Blo 405769 1029145 := bstep (se 2 (by rfl) ⟨385929, by rfl⟩ : syracuseStep 1029145 = 771859) B771859
theorem B9024641 : Blo 405769 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B406695 : Blo 405769 406695 := bstep (se 1 (by rfl) ⟨305021, by rfl⟩ : syracuseStep 406695 = 610043) B610043
theorem B406855 : Blo 405769 406855 := bstep (se 1 (by rfl) ⟨305141, by rfl⟩ : syracuseStep 406855 = 610283) B610283
theorem B1029631 : Blo 405769 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B1554335 : Blo 405769 1554335 := bstep (se 1 (by rfl) ⟨1165751, by rfl⟩ : syracuseStep 1554335 = 2331503) B2331503
theorem B407463 : Blo 405769 407463 := bstep (se 1 (by rfl) ⟨305597, by rfl⟩ : syracuseStep 407463 = 611195) B611195
theorem B2602925 : Blo 405769 2602925 := bstep (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) B976097
theorem B407547 : Blo 405769 407547 := bstep (se 1 (by rfl) ⟨305660, by rfl⟩ : syracuseStep 407547 = 611321) B611321
theorem B8829161 : Blo 405769 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B1194259 : Blo 405769 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B408315 : Blo 405769 408315 := bstep (se 1 (by rfl) ⟨306236, by rfl⟩ : syracuseStep 408315 = 612473) B612473
theorem B408351 : Blo 405769 408351 := bstep (se 1 (by rfl) ⟨306263, by rfl⟩ : syracuseStep 408351 = 612527) B612527
theorem B408571 : Blo 405769 408571 := bstep (se 1 (by rfl) ⟨306428, by rfl⟩ : syracuseStep 408571 = 612857) B612857
theorem B408831 : Blo 405769 408831 := bstep (se 1 (by rfl) ⟨306623, by rfl⟩ : syracuseStep 408831 = 613247) B613247
theorem B25017761 : Blo 405769 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B409247 : Blo 405769 409247 := bstep (se 1 (by rfl) ⟨306935, by rfl⟩ : syracuseStep 409247 = 613871) B613871
theorem B1163393 : Blo 405769 1163393 := bstep (se 2 (by rfl) ⟨436272, by rfl⟩ : syracuseStep 1163393 = 872545) B872545
theorem B6341777 : Blo 405769 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B870119 : Blo 405769 870119 := bstep (se 1 (by rfl) ⟨652589, by rfl⟩ : syracuseStep 870119 = 1305179) B1305179
theorem B6998399 : Blo 405769 6998399 := bstep (se 1 (by rfl) ⟨5248799, by rfl⟩ : syracuseStep 6998399 = 10497599) B10497599
theorem B608735 : Blo 405769 608735 := bstep (se 1 (by rfl) ⟨456551, by rfl⟩ : syracuseStep 608735 = 913103) B913103
theorem B608879 : Blo 405769 608879 := bstep (se 1 (by rfl) ⟨456659, by rfl⟩ : syracuseStep 608879 = 913319) B913319
theorem B609071 : Blo 405769 609071 := bstep (se 1 (by rfl) ⟨456803, by rfl⟩ : syracuseStep 609071 = 913607) B913607
theorem B609215 : Blo 405769 609215 := bstep (se 1 (by rfl) ⟨456911, by rfl⟩ : syracuseStep 609215 = 913823) B913823
theorem B6278093 : Blo 405769 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B609515 : Blo 405769 609515 := bstep (se 1 (by rfl) ⟨457136, by rfl⟩ : syracuseStep 609515 = 914273) B914273
theorem B1166719 : Blo 405769 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B609791 : Blo 405769 609791 := bstep (se 1 (by rfl) ⟨457343, by rfl⟩ : syracuseStep 609791 = 914687) B914687
theorem B610031 : Blo 405769 610031 := bstep (se 1 (by rfl) ⟨457523, by rfl⟩ : syracuseStep 610031 = 915047) B915047
theorem B1397321 : Blo 405769 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B21385853 : Blo 405769 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B610943 : Blo 405769 610943 := bstep (se 1 (by rfl) ⟨458207, by rfl⟩ : syracuseStep 610943 = 916415) B916415
theorem B1037033 : Blo 405769 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B611495 : Blo 405769 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B611753 : Blo 405769 611753 := bstep (se 2 (by rfl) ⟨229407, by rfl⟩ : syracuseStep 611753 = 458815) B458815
theorem B611807 : Blo 405769 611807 := bstep (se 1 (by rfl) ⟨458855, by rfl⟩ : syracuseStep 611807 = 917711) B917711
theorem B611903 : Blo 405769 611903 := bstep (se 1 (by rfl) ⟨458927, by rfl⟩ : syracuseStep 611903 = 917855) B917855
theorem B776135 : Blo 405769 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B612347 : Blo 405769 612347 := bstep (se 1 (by rfl) ⟨459260, by rfl⟩ : syracuseStep 612347 = 918521) B918521
theorem B612383 : Blo 405769 612383 := bstep (se 1 (by rfl) ⟨459287, by rfl⟩ : syracuseStep 612383 = 918575) B918575
theorem B2316397 : Blo 405769 2316397 := bstep (se 3 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 2316397 = 868649) B868649
theorem B5232761 : Blo 405769 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B3529207 : Blo 405769 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B1464923 : Blo 405769 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B31775333 : Blo 405769 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B613151 : Blo 405769 613151 := bstep (se 1 (by rfl) ⟨459863, by rfl⟩ : syracuseStep 613151 = 919727) B919727
theorem B613673 : Blo 405769 613673 := bstep (se 2 (by rfl) ⟨230127, by rfl⟩ : syracuseStep 613673 = 460255) B460255
theorem B2317673 : Blo 405769 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B5856695 : Blo 405769 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B613991 : Blo 405769 613991 := bstep (se 1 (by rfl) ⟨460493, by rfl⟩ : syracuseStep 613991 = 920987) B920987
theorem B614171 : Blo 405769 614171 := bstep (se 1 (by rfl) ⟨460628, by rfl⟩ : syracuseStep 614171 = 921257) B921257
theorem B2056427 : Blo 405769 2056427 := bstep (se 1 (by rfl) ⟨1542320, by rfl⟩ : syracuseStep 2056427 = 3084641) B3084641
theorem B1401799 : Blo 405769 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B11168047 : Blo 405769 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B5237729 : Blo 405769 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B3108455 : Blo 405769 3108455 := bstep (se 1 (by rfl) ⟨2331341, by rfl⟩ : syracuseStep 3108455 = 4662683) B4662683
theorem B913391 : Blo 405769 913391 := bstep (se 1 (by rfl) ⟨685043, by rfl⟩ : syracuseStep 913391 = 1370087) B1370087
theorem B2322503 : Blo 405769 2322503 := bstep (se 1 (by rfl) ⟨1741877, by rfl⟩ : syracuseStep 2322503 = 3483755) B3483755
theorem B1568893 : Blo 405769 1568893 := bstep (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) B588335
theorem B1306793 : Blo 405769 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B9892043 : Blo 405769 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B4649561 : Blo 405769 4649561 := bstep (se 2 (by rfl) ⟨1743585, by rfl⟩ : syracuseStep 4649561 = 3487171) B3487171
theorem B2061449 : Blo 405769 2061449 := bstep (se 2 (by rfl) ⟨773043, by rfl⟩ : syracuseStep 2061449 = 1546087) B1546087
theorem B685415 : Blo 405769 685415 := bstep (se 1 (by rfl) ⟨514061, by rfl⟩ : syracuseStep 685415 = 1028123) B1028123
theorem B1177055 : Blo 405769 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B914975 : Blo 405769 914975 := bstep (se 1 (by rfl) ⟨686231, by rfl⟩ : syracuseStep 914975 = 1372463) B1372463
theorem B685631 : Blo 405769 685631 := bstep (se 1 (by rfl) ⟨514223, by rfl⟩ : syracuseStep 685631 = 1028447) B1028447
theorem B1734223 : Blo 405769 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B718715 : Blo 405769 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B95647715 : Blo 405769 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B915731 : Blo 405769 915731 := bstep (se 1 (by rfl) ⟨686798, by rfl⟩ : syracuseStep 915731 = 1373597) B1373597
theorem B686407 : Blo 405769 686407 := bstep (se 1 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 686407 = 1029611) B1029611
theorem B915839 : Blo 405769 915839 := bstep (se 1 (by rfl) ⟨686879, by rfl⟩ : syracuseStep 915839 = 1373759) B1373759
theorem B686495 : Blo 405769 686495 := bstep (se 1 (by rfl) ⟨514871, by rfl⟩ : syracuseStep 686495 = 1029743) B1029743
theorem B1309895 : Blo 405769 1309895 := bstep (se 1 (by rfl) ⟨982421, by rfl⟩ : syracuseStep 1309895 = 1964843) B1964843
theorem B1375595 : Blo 405769 1375595 := bstep (se 1 (by rfl) ⟨1031696, by rfl⟩ : syracuseStep 1375595 = 2063393) B2063393
theorem B490879 : Blo 405769 490879 := bstep (se 1 (by rfl) ⟨368159, by rfl⟩ : syracuseStep 490879 = 736319) B736319
theorem B1736615 : Blo 405769 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B7078103 : Blo 405769 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B917729 : Blo 405769 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B4227851 : Blo 405769 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B1311677 : Blo 405769 1311677 := bstep (se 3 (by rfl) ⟨245939, by rfl⟩ : syracuseStep 1311677 = 491879) B491879
theorem B1311995 : Blo 405769 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B1869065 : Blo 405769 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B3736991 : Blo 405769 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B919529 : Blo 405769 919529 := bstep (se 2 (by rfl) ⟨344823, by rfl⟩ : syracuseStep 919529 = 689647) B689647
theorem B920015 : Blo 405769 920015 := bstep (se 1 (by rfl) ⟨690011, by rfl⟩ : syracuseStep 920015 = 1380023) B1380023
theorem B920231 : Blo 405769 920231 := bstep (se 1 (by rfl) ⟨690173, by rfl⟩ : syracuseStep 920231 = 1380347) B1380347
theorem B14257235 : Blo 405769 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B691355 : Blo 405769 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B920735 : Blo 405769 920735 := bstep (se 1 (by rfl) ⟨690551, by rfl⟩ : syracuseStep 920735 = 1381103) B1381103
theorem B920879 : Blo 405769 920879 := bstep (se 1 (by rfl) ⟨690659, by rfl⟩ : syracuseStep 920879 = 1381319) B1381319
theorem B920915 : Blo 405769 920915 := bstep (se 1 (by rfl) ⟨690686, by rfl⟩ : syracuseStep 920915 = 1381373) B1381373
theorem B921959 : Blo 405769 921959 := bstep (se 1 (by rfl) ⟨691469, by rfl⟩ : syracuseStep 921959 = 1382939) B1382939
theorem B1380779 : Blo 405769 1380779 := bstep (se 1 (by rfl) ⟨1035584, by rfl⟩ : syracuseStep 1380779 = 2071169) B2071169
theorem B1545115 : Blo 405769 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B3904463 : Blo 405769 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B1546361 : Blo 405769 1546361 := bstep (se 2 (by rfl) ⟨579885, by rfl⟩ : syracuseStep 1546361 = 1159771) B1159771
theorem B3906461 : Blo 405769 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B2072303 : Blo 405769 2072303 := bstep (se 1 (by rfl) ⟨1554227, by rfl⟩ : syracuseStep 2072303 = 3108455) B3108455
theorem B1548335 : Blo 405769 1548335 := bstep (se 1 (by rfl) ⟨1161251, by rfl⟩ : syracuseStep 1548335 = 2322503) B2322503
theorem B6594695 : Blo 405769 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B3088529 : Blo 405769 3088529 := bstep (se 2 (by rfl) ⟨1158198, by rfl⟩ : syracuseStep 3088529 = 2316397) B2316397
theorem B8069291 : Blo 405769 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B1157743 : Blo 405769 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B3484781 : Blo 405769 3484781 := bstep (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) B1306793
theorem B4665599 : Blo 405769 4665599 := bstep (se 1 (by rfl) ⟨3499199, by rfl⟩ : syracuseStep 4665599 = 6998399) B6998399
theorem B13414691 : Blo 405769 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B405823 : Blo 405769 405823 := bstep (se 1 (by rfl) ⟨304367, by rfl⟩ : syracuseStep 405823 = 608735) B608735
theorem B405919 : Blo 405769 405919 := bstep (se 1 (by rfl) ⟨304439, by rfl⟩ : syracuseStep 405919 = 608879) B608879
theorem B406047 : Blo 405769 406047 := bstep (se 1 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 406047 = 609071) B609071
theorem B406143 : Blo 405769 406143 := bstep (se 1 (by rfl) ⟨304607, by rfl⟩ : syracuseStep 406143 = 609215) B609215
theorem B406343 : Blo 405769 406343 := bstep (se 1 (by rfl) ⟨304757, by rfl⟩ : syracuseStep 406343 = 609515) B609515
theorem B3322873 : Blo 405769 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B406527 : Blo 405769 406527 := bstep (se 1 (by rfl) ⟨304895, by rfl⟩ : syracuseStep 406527 = 609791) B609791
theorem B406687 : Blo 405769 406687 := bstep (se 1 (by rfl) ⟨305015, by rfl⟩ : syracuseStep 406687 = 610031) B610031
theorem B1029287 : Blo 405769 1029287 := bstep (se 1 (by rfl) ⟨771965, by rfl⟩ : syracuseStep 1029287 = 1543931) B1543931
theorem B1029307 : Blo 405769 1029307 := bstep (se 1 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 1029307 = 1543961) B1543961
theorem B931547 : Blo 405769 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B14890729 : Blo 405769 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B407295 : Blo 405769 407295 := bstep (se 1 (by rfl) ⟨305471, by rfl⟩ : syracuseStep 407295 = 610943) B610943
theorem B407663 : Blo 405769 407663 := bstep (se 1 (by rfl) ⟨305747, by rfl⟩ : syracuseStep 407663 = 611495) B611495
theorem B235518167 : Blo 405769 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B407835 : Blo 405769 407835 := bstep (se 1 (by rfl) ⟨305876, by rfl⟩ : syracuseStep 407835 = 611753) B611753
theorem B407871 : Blo 405769 407871 := bstep (se 1 (by rfl) ⟨305903, by rfl⟩ : syracuseStep 407871 = 611807) B611807
theorem B407935 : Blo 405769 407935 := bstep (se 1 (by rfl) ⟨305951, by rfl⟩ : syracuseStep 407935 = 611903) B611903
theorem B408231 : Blo 405769 408231 := bstep (se 1 (by rfl) ⟨306173, by rfl⟩ : syracuseStep 408231 = 612347) B612347
theorem B408255 : Blo 405769 408255 := bstep (se 1 (by rfl) ⟨306191, by rfl⟩ : syracuseStep 408255 = 612383) B612383
theorem B3488507 : Blo 405769 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B1555625 : Blo 405769 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B408767 : Blo 405769 408767 := bstep (se 1 (by rfl) ⟨306575, by rfl⟩ : syracuseStep 408767 = 613151) B613151
theorem B409115 : Blo 405769 409115 := bstep (se 1 (by rfl) ⟨306836, by rfl⟩ : syracuseStep 409115 = 613673) B613673
theorem B409327 : Blo 405769 409327 := bstep (se 1 (by rfl) ⟨306995, by rfl⟩ : syracuseStep 409327 = 613991) B613991
theorem B409447 : Blo 405769 409447 := bstep (se 1 (by rfl) ⟨307085, by rfl⟩ : syracuseStep 409447 = 614171) B614171
theorem B1032871 : Blo 405769 1032871 := bstep (se 1 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 1032871 = 1549307) B1549307
theorem B338936885 : Blo 405769 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B3818753 : Blo 405769 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B3491819 : Blo 405769 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B2312297 : Blo 405769 2312297 := bstep (se 2 (by rfl) ⟨867111, by rfl⟩ : syracuseStep 2312297 = 1734223) B1734223
theorem B608927 : Blo 405769 608927 := bstep (se 1 (by rfl) ⟨456695, by rfl⟩ : syracuseStep 608927 = 913391) B913391
theorem B1592345 : Blo 405769 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B3099707 : Blo 405769 3099707 := bstep (se 1 (by rfl) ⟨2324780, by rfl⟩ : syracuseStep 3099707 = 4649561) B4649561
theorem B4705609 : Blo 405769 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B6016427 : Blo 405769 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B609983 : Blo 405769 609983 := bstep (se 1 (by rfl) ⟨457487, by rfl⟩ : syracuseStep 609983 = 914975) B914975
theorem B479143 : Blo 405769 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B1036223 : Blo 405769 1036223 := bstep (se 1 (by rfl) ⟨777167, by rfl⟩ : syracuseStep 1036223 = 1554335) B1554335
theorem B5886107 : Blo 405769 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B610487 : Blo 405769 610487 := bstep (se 1 (by rfl) ⟨457865, by rfl⟩ : syracuseStep 610487 = 915731) B915731
theorem B610559 : Blo 405769 610559 := bstep (se 1 (by rfl) ⟨457919, by rfl⟩ : syracuseStep 610559 = 915839) B915839
theorem B873263 : Blo 405769 873263 := bstep (se 1 (by rfl) ⟨654947, by rfl⟩ : syracuseStep 873263 = 1309895) B1309895
theorem B611705 : Blo 405769 611705 := bstep (se 2 (by rfl) ⟨229389, by rfl⟩ : syracuseStep 611705 = 458779) B458779
theorem B775595 : Blo 405769 775595 := bstep (se 1 (by rfl) ⟨581696, by rfl⟩ : syracuseStep 775595 = 1163393) B1163393
theorem B2577871 : Blo 405769 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B612263 : Blo 405769 612263 := bstep (se 1 (by rfl) ⟨459197, by rfl⟩ : syracuseStep 612263 = 918395) B918395
theorem B612329 : Blo 405769 612329 := bstep (se 2 (by rfl) ⟨229623, by rfl⟩ : syracuseStep 612329 = 459247) B459247
theorem B612407 : Blo 405769 612407 := bstep (se 1 (by rfl) ⟨459305, by rfl⟩ : syracuseStep 612407 = 918611) B918611
theorem B612455 : Blo 405769 612455 := bstep (se 1 (by rfl) ⟨459341, by rfl⟩ : syracuseStep 612455 = 918683) B918683
theorem B580079 : Blo 405769 580079 := bstep (se 1 (by rfl) ⟨435059, by rfl⟩ : syracuseStep 580079 = 870119) B870119
theorem B613115 : Blo 405769 613115 := bstep (se 1 (by rfl) ⟨459836, by rfl⟩ : syracuseStep 613115 = 919673) B919673
theorem B4185395 : Blo 405769 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B1990331 : Blo 405769 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B614393 : Blo 405769 614393 := bstep (se 2 (by rfl) ⟨230397, by rfl⟩ : syracuseStep 614393 = 460795) B460795
theorem B517423 : Blo 405769 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B7431871 : Blo 405769 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B1370951 : Blo 405769 1370951 := bstep (se 1 (by rfl) ⟨1028213, by rfl⟩ : syracuseStep 1370951 = 2056427) B2056427
theorem B2091857 : Blo 405769 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B1372193 : Blo 405769 1372193 := bstep (se 2 (by rfl) ⟨514572, by rfl⟩ : syracuseStep 1372193 = 1029145) B1029145
theorem B2618021 : Blo 405769 2618021 := bstep (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) B490879
theorem B1372841 : Blo 405769 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B685759 : Blo 405769 685759 := bstep (se 1 (by rfl) ⟨514319, by rfl⟩ : syracuseStep 685759 = 1028639) B1028639
theorem B915209 : Blo 405769 915209 := bstep (se 2 (by rfl) ⟨343203, by rfl⟩ : syracuseStep 915209 = 686407) B686407
theorem B1374299 : Blo 405769 1374299 := bstep (se 1 (by rfl) ⟨1030724, by rfl⟩ : syracuseStep 1374299 = 2061449) B2061449
theorem B456943 : Blo 405769 456943 := bstep (se 1 (by rfl) ⟨342707, by rfl⟩ : syracuseStep 456943 = 685415) B685415
theorem B784703 : Blo 405769 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B457087 : Blo 405769 457087 := bstep (se 1 (by rfl) ⟨342815, by rfl⟩ : syracuseStep 457087 = 685631) B685631
theorem B1735283 : Blo 405769 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B63765143 : Blo 405769 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B457663 : Blo 405769 457663 := bstep (se 1 (by rfl) ⟨343247, by rfl⟩ : syracuseStep 457663 = 686495) B686495
theorem B917063 : Blo 405769 917063 := bstep (se 1 (by rfl) ⟨687797, by rfl⟩ : syracuseStep 917063 = 1375595) B1375595
theorem B16678507 : Blo 405769 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B4718735 : Blo 405769 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B2818567 : Blo 405769 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B1246043 : Blo 405769 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B1377161 : Blo 405769 1377161 := bstep (se 2 (by rfl) ⟨516435, by rfl⟩ : syracuseStep 1377161 = 1032871) B1032871
theorem B2491327 : Blo 405769 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B2327879 : Blo 405769 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B1541531 : Blo 405769 1541531 := bstep (se 1 (by rfl) ⟨1156148, by rfl⟩ : syracuseStep 1541531 = 2312297) B2312297
theorem B689897 : Blo 405769 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B2066471 : Blo 405769 2066471 := bstep (se 1 (by rfl) ⟨1549853, by rfl⟩ : syracuseStep 2066471 = 3099707) B3099707
theorem B9504823 : Blo 405769 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B460903 : Blo 405769 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B690815 : Blo 405769 690815 := bstep (se 1 (by rfl) ⟨518111, by rfl⟩ : syracuseStep 690815 = 1036223) B1036223
theorem B920519 : Blo 405769 920519 := bstep (se 1 (by rfl) ⟨690389, by rfl⟩ : syracuseStep 920519 = 1380779) B1380779
theorem B1543657 : Blo 405769 1543657 := bstep (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) B1157743
theorem B2068253 : Blo 405769 2068253 := bstep (se 3 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 2068253 = 775595) B775595
theorem B2790263 : Blo 405769 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B1381535 : Blo 405769 1381535 := bstep (se 1 (by rfl) ⟨1036151, by rfl⟩ : syracuseStep 1381535 = 2072303) B2072303
theorem B4396463 : Blo 405769 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B5379527 : Blo 405769 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B1546877 : Blo 405769 1546877 := bstep (se 3 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 1546877 = 580079) B580079
theorem B4430497 : Blo 405769 4430497 := bstep (se 2 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 4430497 = 3322873) B3322873
theorem B1745347 : Blo 405769 1745347 := bstep (se 1 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 1745347 = 2618021) B2618021
theorem B1156855 : Blo 405769 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B42510095 : Blo 405769 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B405951 : Blo 405769 405951 := bstep (se 1 (by rfl) ⟨304463, by rfl⟩ : syracuseStep 405951 = 608927) B608927
theorem B9909161 : Blo 405769 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B4010951 : Blo 405769 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B406655 : Blo 405769 406655 := bstep (se 1 (by rfl) ⟨304991, by rfl⟩ : syracuseStep 406655 = 609983) B609983
theorem B406991 : Blo 405769 406991 := bstep (se 1 (by rfl) ⟨305243, by rfl⟩ : syracuseStep 406991 = 610487) B610487
theorem B407039 : Blo 405769 407039 := bstep (se 1 (by rfl) ⟨305279, by rfl⟩ : syracuseStep 407039 = 610559) B610559
theorem B2602975 : Blo 405769 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B407803 : Blo 405769 407803 := bstep (se 1 (by rfl) ⟨305852, by rfl⟩ : syracuseStep 407803 = 611705) B611705
theorem B408175 : Blo 405769 408175 := bstep (se 1 (by rfl) ⟨306131, by rfl⟩ : syracuseStep 408175 = 612263) B612263
theorem B408219 : Blo 405769 408219 := bstep (se 1 (by rfl) ⟨306164, by rfl⟩ : syracuseStep 408219 = 612329) B612329
theorem B408271 : Blo 405769 408271 := bstep (se 1 (by rfl) ⟨306203, by rfl⟩ : syracuseStep 408271 = 612407) B612407
theorem B408303 : Blo 405769 408303 := bstep (se 1 (by rfl) ⟨306227, by rfl⟩ : syracuseStep 408303 = 612455) B612455
theorem B1030907 : Blo 405769 1030907 := bstep (se 1 (by rfl) ⟨773180, by rfl⟩ : syracuseStep 1030907 = 1546361) B1546361
theorem B6274145 : Blo 405769 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B408743 : Blo 405769 408743 := bstep (se 1 (by rfl) ⟨306557, by rfl⟩ : syracuseStep 408743 = 613115) B613115
theorem B2604307 : Blo 405769 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B1326887 : Blo 405769 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B638857 : Blo 405769 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B409595 : Blo 405769 409595 := bstep (se 1 (by rfl) ⟨307196, by rfl⟩ : syracuseStep 409595 = 614393) B614393
theorem B1032223 : Blo 405769 1032223 := bstep (se 1 (by rfl) ⟨774167, by rfl⟩ : syracuseStep 1032223 = 1548335) B1548335
theorem B4246253 : Blo 405769 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B609257 : Blo 405769 609257 := bstep (se 2 (by rfl) ⟨228471, by rfl⟩ : syracuseStep 609257 = 456943) B456943
theorem B609449 : Blo 405769 609449 := bstep (se 2 (by rfl) ⟨228543, by rfl⟩ : syracuseStep 609449 = 457087) B457087
theorem B610139 : Blo 405769 610139 := bstep (se 1 (by rfl) ⟨457604, by rfl⟩ : syracuseStep 610139 = 915209) B915209
theorem B610217 : Blo 405769 610217 := bstep (se 2 (by rfl) ⟨228831, by rfl⟩ : syracuseStep 610217 = 457663) B457663
theorem B157012111 : Blo 405769 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B1037083 : Blo 405769 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B22238009 : Blo 405769 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B611375 : Blo 405769 611375 := bstep (se 1 (by rfl) ⟨458531, by rfl⟩ : syracuseStep 611375 = 917063) B917063
theorem B611819 : Blo 405769 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B874451 : Blo 405769 874451 := bstep (se 1 (by rfl) ⟨655838, by rfl⟩ : syracuseStep 874451 = 1311677) B1311677
theorem B225957923 : Blo 405769 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B35772509 : Blo 405769 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B2545835 : Blo 405769 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B613019 : Blo 405769 613019 := bstep (se 1 (by rfl) ⟨459764, by rfl⟩ : syracuseStep 613019 = 919529) B919529
theorem B613343 : Blo 405769 613343 := bstep (se 1 (by rfl) ⟨460007, by rfl⟩ : syracuseStep 613343 = 920015) B920015
theorem B613487 : Blo 405769 613487 := bstep (se 1 (by rfl) ⟨460115, by rfl⟩ : syracuseStep 613487 = 920231) B920231
theorem B613823 : Blo 405769 613823 := bstep (se 1 (by rfl) ⟨460367, by rfl⟩ : syracuseStep 613823 = 920735) B920735
theorem B613919 : Blo 405769 613919 := bstep (se 1 (by rfl) ⟨460439, by rfl⟩ : syracuseStep 613919 = 920879) B920879
theorem B613943 : Blo 405769 613943 := bstep (se 1 (by rfl) ⟨460457, by rfl⟩ : syracuseStep 613943 = 920915) B920915
theorem B3924071 : Blo 405769 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B614639 : Blo 405769 614639 := bstep (se 1 (by rfl) ⟨460979, by rfl⟩ : syracuseStep 614639 = 921959) B921959
theorem B582175 : Blo 405769 582175 := bstep (se 1 (by rfl) ⟨436631, by rfl⟩ : syracuseStep 582175 = 873263) B873263
theorem B3498653 : Blo 405769 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B2484125 : Blo 405769 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B2059019 : Blo 405769 2059019 := bstep (se 1 (by rfl) ⟨1544264, by rfl⟩ : syracuseStep 2059019 = 3088529) B3088529
theorem B2060153 : Blo 405769 2060153 := bstep (se 2 (by rfl) ⟨772557, by rfl⟩ : syracuseStep 2060153 = 1545115) B1545115
theorem B1372409 : Blo 405769 1372409 := bstep (se 2 (by rfl) ⟨514653, by rfl⟩ : syracuseStep 1372409 = 1029307) B1029307
theorem B913967 : Blo 405769 913967 := bstep (se 1 (by rfl) ⟨685475, by rfl⟩ : syracuseStep 913967 = 1370951) B1370951
theorem B3437161 : Blo 405769 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B2323187 : Blo 405769 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B914345 : Blo 405769 914345 := bstep (se 2 (by rfl) ⟨342879, by rfl⟩ : syracuseStep 914345 = 685759) B685759
theorem B19854305 : Blo 405769 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B914795 : Blo 405769 914795 := bstep (se 1 (by rfl) ⟨686096, by rfl⟩ : syracuseStep 914795 = 1372193) B1372193
theorem B3110399 : Blo 405769 3110399 := bstep (se 1 (by rfl) ⟨2332799, by rfl⟩ : syracuseStep 3110399 = 4665599) B4665599
theorem B915227 : Blo 405769 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B686191 : Blo 405769 686191 := bstep (se 1 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 686191 = 1029287) B1029287
theorem B22313141 : Blo 405769 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B916199 : Blo 405769 916199 := bstep (se 1 (by rfl) ⟨687149, by rfl⟩ : syracuseStep 916199 = 1374299) B1374299
theorem B523135 : Blo 405769 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B2325671 : Blo 405769 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B1376297 : Blo 405769 1376297 := bstep (se 2 (by rfl) ⟨516111, by rfl⟩ : syracuseStep 1376297 = 1032223) B1032223
theorem B3145823 : Blo 405769 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B918107 : Blo 405769 918107 := bstep (se 1 (by rfl) ⟨688580, by rfl⟩ : syracuseStep 918107 = 1377161) B1377161
theorem B2327129 : Blo 405769 2327129 := bstep (se 2 (by rfl) ⟨872673, by rfl⟩ : syracuseStep 2327129 = 1745347) B1745347
theorem B459931 : Blo 405769 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B1377647 : Blo 405769 1377647 := bstep (se 1 (by rfl) ⟨1033235, by rfl⟩ : syracuseStep 1377647 = 2066471) B2066471
theorem B460543 : Blo 405769 460543 := bstep (se 1 (by rfl) ⟨345407, by rfl⟩ : syracuseStep 460543 = 690815) B690815
theorem B1542473 : Blo 405769 1542473 := bstep (se 2 (by rfl) ⟨578427, by rfl⟩ : syracuseStep 1542473 = 1156855) B1156855
theorem B1378835 : Blo 405769 1378835 := bstep (se 1 (by rfl) ⟨1034126, by rfl⟩ : syracuseStep 1378835 = 2068253) B2068253
theorem B921023 : Blo 405769 921023 := bstep (se 1 (by rfl) ⟨690767, by rfl⟩ : syracuseStep 921023 = 1381535) B1381535
theorem B150638615 : Blo 405769 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B2332435 : Blo 405769 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B6788893 : Blo 405769 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B1382777 : Blo 405769 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B1548791 : Blo 405769 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B5907329 : Blo 405769 5907329 := bstep (se 2 (by rfl) ⟨2215248, by rfl⟩ : syracuseStep 5907329 = 4430497) B4430497
theorem B2073599 : Blo 405769 2073599 := bstep (se 1 (by rfl) ⟨1555199, by rfl⟩ : syracuseStep 2073599 = 3110399) B3110399
theorem B697513 : Blo 405769 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B1550447 : Blo 405769 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B837397925 : Blo 405769 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B1551919 : Blo 405769 1551919 := bstep (se 1 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 1551919 = 2327879) B2327879
theorem B1027687 : Blo 405769 1027687 := bstep (se 1 (by rfl) ⟨770765, by rfl⟩ : syracuseStep 1027687 = 1541531) B1541531
theorem B3321769 : Blo 405769 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B2830835 : Blo 405769 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B406171 : Blo 405769 406171 := bstep (se 1 (by rfl) ⟨304628, by rfl⟩ : syracuseStep 406171 = 609257) B609257
theorem B406299 : Blo 405769 406299 := bstep (se 1 (by rfl) ⟨304724, by rfl⟩ : syracuseStep 406299 = 609449) B609449
theorem B3322781 : Blo 405769 3322781 := bstep (se 3 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 3322781 = 1246043) B1246043
theorem B406759 : Blo 405769 406759 := bstep (se 1 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 406759 = 610139) B610139
theorem B406811 : Blo 405769 406811 := bstep (se 1 (by rfl) ⟨305108, by rfl⟩ : syracuseStep 406811 = 610217) B610217
theorem B14825339 : Blo 405769 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B18331525 : Blo 405769 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B407583 : Blo 405769 407583 := bstep (se 1 (by rfl) ⟨305687, by rfl⟩ : syracuseStep 407583 = 611375) B611375
theorem B2930975 : Blo 405769 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B407879 : Blo 405769 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B1031251 : Blo 405769 1031251 := bstep (se 1 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 1031251 = 1546877) B1546877
theorem B408679 : Blo 405769 408679 := bstep (se 1 (by rfl) ⟨306509, by rfl⟩ : syracuseStep 408679 = 613019) B613019
theorem B408895 : Blo 405769 408895 := bstep (se 1 (by rfl) ⟨306671, by rfl⟩ : syracuseStep 408895 = 613343) B613343
theorem B408991 : Blo 405769 408991 := bstep (se 1 (by rfl) ⟨306743, by rfl⟩ : syracuseStep 408991 = 613487) B613487
theorem B409215 : Blo 405769 409215 := bstep (se 1 (by rfl) ⟨306911, by rfl⟩ : syracuseStep 409215 = 613823) B613823
theorem B409279 : Blo 405769 409279 := bstep (se 1 (by rfl) ⟨306959, by rfl⟩ : syracuseStep 409279 = 613919) B613919
theorem B409295 : Blo 405769 409295 := bstep (se 1 (by rfl) ⟨306971, by rfl⟩ : syracuseStep 409295 = 613943) B613943
theorem B409759 : Blo 405769 409759 := bstep (se 1 (by rfl) ⟨307319, by rfl⟩ : syracuseStep 409759 = 614639) B614639
theorem B1656083 : Blo 405769 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B609311 : Blo 405769 609311 := bstep (se 1 (by rfl) ⟨456983, by rfl⟩ : syracuseStep 609311 = 913967) B913967
theorem B609563 : Blo 405769 609563 := bstep (se 1 (by rfl) ⟨457172, by rfl⟩ : syracuseStep 609563 = 914345) B914345
theorem B6606107 : Blo 405769 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B2673967 : Blo 405769 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B609863 : Blo 405769 609863 := bstep (se 1 (by rfl) ⟨457397, by rfl⟩ : syracuseStep 609863 = 914795) B914795
theorem B610151 : Blo 405769 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B610799 : Blo 405769 610799 := bstep (se 1 (by rfl) ⟨458099, by rfl⟩ : syracuseStep 610799 = 916199) B916199
theorem B4182763 : Blo 405769 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B3758089 : Blo 405769 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B776233 : Blo 405769 776233 := bstep (se 2 (by rfl) ⟨291087, by rfl⟩ : syracuseStep 776233 = 582175) B582175
theorem B613679 : Blo 405769 613679 := bstep (se 1 (by rfl) ⟨460259, by rfl⟩ : syracuseStep 613679 = 920519) B920519
theorem B12673097 : Blo 405769 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B614537 : Blo 405769 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B1860175 : Blo 405769 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B14345405 : Blo 405769 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B582967 : Blo 405769 582967 := bstep (se 1 (by rfl) ⟨437225, by rfl⟩ : syracuseStep 582967 = 874451) B874451
theorem B23848339 : Blo 405769 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B2058209 : Blo 405769 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B2616047 : Blo 405769 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B28340063 : Blo 405769 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B1372679 : Blo 405769 1372679 := bstep (se 1 (by rfl) ⟨1029509, by rfl⟩ : syracuseStep 1372679 = 2059019) B2059019
theorem B1373435 : Blo 405769 1373435 := bstep (se 1 (by rfl) ⟨1030076, by rfl⟩ : syracuseStep 1373435 = 2060153) B2060153
theorem B3470633 : Blo 405769 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B914921 : Blo 405769 914921 := bstep (se 2 (by rfl) ⟨343095, by rfl⟩ : syracuseStep 914921 = 686191) B686191
theorem B914939 : Blo 405769 914939 := bstep (se 1 (by rfl) ⟨686204, by rfl⟩ : syracuseStep 914939 = 1372409) B1372409
theorem B13236203 : Blo 405769 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B14875427 : Blo 405769 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B3472409 : Blo 405769 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B687271 : Blo 405769 687271 := bstep (se 1 (by rfl) ⟨515453, by rfl⟩ : syracuseStep 687271 = 1030907) B1030907
theorem B851809 : Blo 405769 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B884591 : Blo 405769 884591 := bstep (se 1 (by rfl) ⟨663443, by rfl⟩ : syracuseStep 884591 = 1326887) B1326887
theorem B917531 : Blo 405769 917531 := bstep (se 1 (by rfl) ⟨688148, by rfl⟩ : syracuseStep 917531 = 1376297) B1376297
theorem B2097215 : Blo 405769 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B918431 : Blo 405769 918431 := bstep (se 1 (by rfl) ⟨688823, by rfl⟩ : syracuseStep 918431 = 1377647) B1377647
theorem B919223 : Blo 405769 919223 := bstep (se 1 (by rfl) ⟨689417, by rfl⟩ : syracuseStep 919223 = 1378835) B1378835
theorem B921851 : Blo 405769 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B2069225 : Blo 405769 2069225 := bstep (se 2 (by rfl) ⟨775959, by rfl⟩ : syracuseStep 2069225 = 1551919) B1551919
theorem B4429025 : Blo 405769 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B3938219 : Blo 405769 3938219 := bstep (se 1 (by rfl) ⟨2953664, by rfl⟩ : syracuseStep 3938219 = 5907329) B5907329
theorem B1382399 : Blo 405769 1382399 := bstep (se 1 (by rfl) ⟨1036799, by rfl⟩ : syracuseStep 1382399 = 2073599) B2073599
theorem B5577017 : Blo 405769 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1744031 : Blo 405769 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B9051857 : Blo 405769 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B8824135 : Blo 405769 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B1551419 : Blo 405769 1551419 := bstep (se 1 (by rfl) ⟨1163564, by rfl⟩ : syracuseStep 1551419 = 2327129) B2327129
theorem B7548893 : Blo 405769 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B1028315 : Blo 405769 1028315 := bstep (se 1 (by rfl) ⟨771236, by rfl⟩ : syracuseStep 1028315 = 1542473) B1542473
theorem B930017 : Blo 405769 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B31797785 : Blo 405769 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B406207 : Blo 405769 406207 := bstep (se 1 (by rfl) ⟨304655, by rfl⟩ : syracuseStep 406207 = 609311) B609311
theorem B406375 : Blo 405769 406375 := bstep (se 1 (by rfl) ⟨304781, by rfl⟩ : syracuseStep 406375 = 609563) B609563
theorem B4404071 : Blo 405769 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B406575 : Blo 405769 406575 := bstep (se 1 (by rfl) ⟨304931, by rfl⟩ : syracuseStep 406575 = 609863) B609863
theorem B406767 : Blo 405769 406767 := bstep (se 1 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 406767 = 610151) B610151
theorem B407199 : Blo 405769 407199 := bstep (se 1 (by rfl) ⟨305399, by rfl⟩ : syracuseStep 407199 = 610799) B610799
theorem B409119 : Blo 405769 409119 := bstep (se 1 (by rfl) ⟨306839, by rfl⟩ : syracuseStep 409119 = 613679) B613679
theorem B409691 : Blo 405769 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B1032527 : Blo 405769 1032527 := bstep (se 1 (by rfl) ⟨774395, by rfl⟩ : syracuseStep 1032527 = 1548791) B1548791
theorem B1033631 : Blo 405769 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B18893375 : Blo 405769 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B1034977 : Blo 405769 1034977 := bstep (se 2 (by rfl) ⟨388116, by rfl⟩ : syracuseStep 1034977 = 776233) B776233
theorem B2215187 : Blo 405769 2215187 := bstep (se 1 (by rfl) ⟨1661390, by rfl⟩ : syracuseStep 2215187 = 3322781) B3322781
theorem B2313755 : Blo 405769 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B609947 : Blo 405769 609947 := bstep (se 1 (by rfl) ⟨457460, by rfl⟩ : syracuseStep 609947 = 914921) B914921
theorem B609959 : Blo 405769 609959 := bstep (se 1 (by rfl) ⟨457469, by rfl⟩ : syracuseStep 609959 = 914939) B914939
theorem B9883559 : Blo 405769 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B1953983 : Blo 405769 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B9916951 : Blo 405769 9916951 := bstep (se 1 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 9916951 = 14875427) B14875427
theorem B2314939 : Blo 405769 2314939 := bstep (se 1 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 2314939 = 3472409) B3472409
theorem B1135745 : Blo 405769 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B612071 : Blo 405769 612071 := bstep (se 1 (by rfl) ⟨459053, by rfl⟩ : syracuseStep 612071 = 918107) B918107
theorem B2480233 : Blo 405769 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B613241 : Blo 405769 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B777289 : Blo 405769 777289 := bstep (se 2 (by rfl) ⟨291483, by rfl⟩ : syracuseStep 777289 = 582967) B582967
theorem B614015 : Blo 405769 614015 := bstep (se 1 (by rfl) ⟨460511, by rfl⟩ : syracuseStep 614015 = 921023) B921023
theorem B614057 : Blo 405769 614057 := bstep (se 2 (by rfl) ⟨230271, by rfl⟩ : syracuseStep 614057 = 460543) B460543
theorem B100425743 : Blo 405769 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B4416221 : Blo 405769 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B3565289 : Blo 405769 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B1370249 : Blo 405769 1370249 := bstep (se 2 (by rfl) ⟨513843, by rfl⟩ : syracuseStep 1370249 = 1027687) B1027687
theorem B8448731 : Blo 405769 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B9563603 : Blo 405769 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B1372139 : Blo 405769 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B558265283 : Blo 405769 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B3109913 : Blo 405769 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B24442033 : Blo 405769 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B5010785 : Blo 405769 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B915119 : Blo 405769 915119 := bstep (se 1 (by rfl) ⟨686339, by rfl⟩ : syracuseStep 915119 = 1372679) B1372679
theorem B915623 : Blo 405769 915623 := bstep (se 1 (by rfl) ⟨686717, by rfl⟩ : syracuseStep 915623 = 1373435) B1373435
theorem B1375001 : Blo 405769 1375001 := bstep (se 2 (by rfl) ⟨515625, by rfl⟩ : syracuseStep 1375001 = 1031251) B1031251
theorem B916361 : Blo 405769 916361 := bstep (se 2 (by rfl) ⟨343635, by rfl⟩ : syracuseStep 916361 = 687271) B687271
theorem B589727 : Blo 405769 589727 := bstep (se 1 (by rfl) ⟨442295, by rfl⟩ : syracuseStep 589727 = 884591) B884591
theorem B688351 : Blo 405769 688351 := bstep (se 1 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 688351 = 1032527) B1032527
theorem B689087 : Blo 405769 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B11765513 : Blo 405769 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B1476791 : Blo 405769 1476791 := bstep (se 1 (by rfl) ⟨1107593, by rfl⟩ : syracuseStep 1476791 = 2215187) B2215187
theorem B1542503 : Blo 405769 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B6589039 : Blo 405769 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B1379483 : Blo 405769 1379483 := bstep (se 1 (by rfl) ⟨1034612, by rfl⟩ : syracuseStep 1379483 = 2069225) B2069225
theorem B2952683 : Blo 405769 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B1379969 : Blo 405769 1379969 := bstep (se 2 (by rfl) ⟨517488, by rfl⟩ : syracuseStep 1379969 = 1034977) B1034977
theorem B2625479 : Blo 405769 2625479 := bstep (se 1 (by rfl) ⟨1969109, by rfl⟩ : syracuseStep 2625479 = 3938219) B3938219
theorem B921599 : Blo 405769 921599 := bstep (se 1 (by rfl) ⟨691199, by rfl⟩ : syracuseStep 921599 = 1382399) B1382399
theorem B6034571 : Blo 405769 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B66950495 : Blo 405769 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B3086585 : Blo 405769 3086585 := bstep (se 2 (by rfl) ⟨1157469, by rfl⟩ : syracuseStep 3086585 = 2314939) B2314939
theorem B2073275 : Blo 405769 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B25502941 : Blo 405769 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B12595583 : Blo 405769 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B11744189 : Blo 405769 11744189 := bstep (se 3 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 11744189 = 4404071) B4404071
theorem B406631 : Blo 405769 406631 := bstep (se 1 (by rfl) ⟨304973, by rfl⟩ : syracuseStep 406631 = 609947) B609947
theorem B406639 : Blo 405769 406639 := bstep (se 1 (by rfl) ⟨304979, by rfl⟩ : syracuseStep 406639 = 609959) B609959
theorem B408047 : Blo 405769 408047 := bstep (se 1 (by rfl) ⟨306035, by rfl⟩ : syracuseStep 408047 = 612071) B612071
theorem B408827 : Blo 405769 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B1162687 : Blo 405769 1162687 := bstep (se 1 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 1162687 = 1744031) B1744031
theorem B409343 : Blo 405769 409343 := bstep (se 1 (by rfl) ⟨307007, by rfl⟩ : syracuseStep 409343 = 614015) B614015
theorem B409371 : Blo 405769 409371 := bstep (se 1 (by rfl) ⟨307028, by rfl⟩ : syracuseStep 409371 = 614057) B614057
theorem B13222601 : Blo 405769 13222601 := bstep (se 2 (by rfl) ⟨4958475, by rfl⟩ : syracuseStep 13222601 = 9916951) B9916951
theorem B2376859 : Blo 405769 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B32589377 : Blo 405769 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B1034279 : Blo 405769 1034279 := bstep (se 1 (by rfl) ⟨775709, by rfl⟩ : syracuseStep 1034279 = 1551419) B1551419
theorem B5032595 : Blo 405769 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B610079 : Blo 405769 610079 := bstep (se 1 (by rfl) ⟨457559, by rfl⟩ : syracuseStep 610079 = 915119) B915119
theorem B1036385 : Blo 405769 1036385 := bstep (se 2 (by rfl) ⟨388644, by rfl⟩ : syracuseStep 1036385 = 777289) B777289
theorem B610415 : Blo 405769 610415 := bstep (se 1 (by rfl) ⟨457811, by rfl⟩ : syracuseStep 610415 = 915623) B915623
theorem B610907 : Blo 405769 610907 := bstep (se 1 (by rfl) ⟨458180, by rfl⟩ : syracuseStep 610907 = 916361) B916361
theorem B611687 : Blo 405769 611687 := bstep (se 1 (by rfl) ⟨458765, by rfl⟩ : syracuseStep 611687 = 917531) B917531
theorem B1398143 : Blo 405769 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B612287 : Blo 405769 612287 := bstep (se 1 (by rfl) ⟨459215, by rfl⟩ : syracuseStep 612287 = 918431) B918431
theorem B612815 : Blo 405769 612815 := bstep (se 1 (by rfl) ⟨459611, by rfl⟩ : syracuseStep 612815 = 919223) B919223
theorem B12114613 : Blo 405769 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B1302655 : Blo 405769 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B614567 : Blo 405769 614567 := bstep (se 1 (by rfl) ⟨460925, by rfl⟩ : syracuseStep 614567 = 921851) B921851
theorem B2944147 : Blo 405769 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B14872045 : Blo 405769 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B913499 : Blo 405769 913499 := bstep (se 1 (by rfl) ⟨685124, by rfl⟩ : syracuseStep 913499 = 1370249) B1370249
theorem B5632487 : Blo 405769 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B914759 : Blo 405769 914759 := bstep (se 1 (by rfl) ⟨686069, by rfl⟩ : syracuseStep 914759 = 1372139) B1372139
theorem B3306977 : Blo 405769 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B685543 : Blo 405769 685543 := bstep (se 1 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 685543 = 1028315) B1028315
theorem B620011 : Blo 405769 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B21198523 : Blo 405769 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B372176855 : Blo 405769 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B3340523 : Blo 405769 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B916667 : Blo 405769 916667 := bstep (se 1 (by rfl) ⟨687500, by rfl⟩ : syracuseStep 916667 = 1375001) B1375001
theorem B1572605 : Blo 405769 1572605 := bstep (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) B589727
theorem B1736873 : Blo 405769 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B917801 : Blo 405769 917801 := bstep (se 2 (by rfl) ⟨344175, by rfl⟩ : syracuseStep 917801 = 688351) B688351
theorem B8815067 : Blo 405769 8815067 := bstep (se 1 (by rfl) ⟨6611300, by rfl⟩ : syracuseStep 8815067 = 13222601) B13222601
theorem B459391 : Blo 405769 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B21726251 : Blo 405769 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B689519 : Blo 405769 689519 := bstep (se 1 (by rfl) ⟨517139, by rfl⟩ : syracuseStep 689519 = 1034279) B1034279
theorem B984527 : Blo 405769 984527 := bstep (se 1 (by rfl) ⟨738395, by rfl⟩ : syracuseStep 984527 = 1476791) B1476791
theorem B919655 : Blo 405769 919655 := bstep (se 1 (by rfl) ⟨689741, by rfl⟩ : syracuseStep 919655 = 1379483) B1379483
theorem B1968455 : Blo 405769 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B919979 : Blo 405769 919979 := bstep (se 1 (by rfl) ⟨689984, by rfl⟩ : syracuseStep 919979 = 1379969) B1379969
theorem B690923 : Blo 405769 690923 := bstep (se 1 (by rfl) ⟨518192, by rfl⟩ : syracuseStep 690923 = 1036385) B1036385
theorem B8785385 : Blo 405769 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B44633663 : Blo 405769 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B19829393 : Blo 405769 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B1382183 : Blo 405769 1382183 := bstep (se 1 (by rfl) ⟨1036637, by rfl⟩ : syracuseStep 1382183 = 2073275) B2073275
theorem B826681 : Blo 405769 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B8397055 : Blo 405769 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B2204651 : Blo 405769 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B1550249 : Blo 405769 1550249 := bstep (se 2 (by rfl) ⟨581343, by rfl⟩ : syracuseStep 1550249 = 1162687) B1162687
theorem B7843675 : Blo 405769 7843675 := bstep (se 1 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 7843675 = 11765513) B11765513
theorem B1028335 : Blo 405769 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B3355063 : Blo 405769 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B406719 : Blo 405769 406719 := bstep (se 1 (by rfl) ⟨305039, by rfl⟩ : syracuseStep 406719 = 610079) B610079
theorem B1750319 : Blo 405769 1750319 := bstep (se 1 (by rfl) ⟨1312739, by rfl⟩ : syracuseStep 1750319 = 2625479) B2625479
theorem B406943 : Blo 405769 406943 := bstep (se 1 (by rfl) ⟨305207, by rfl⟩ : syracuseStep 406943 = 610415) B610415
theorem B407271 : Blo 405769 407271 := bstep (se 1 (by rfl) ⟨305453, by rfl⟩ : syracuseStep 407271 = 610907) B610907
theorem B407791 : Blo 405769 407791 := bstep (se 1 (by rfl) ⟨305843, by rfl⟩ : syracuseStep 407791 = 611687) B611687
theorem B932095 : Blo 405769 932095 := bstep (se 1 (by rfl) ⟨699071, by rfl⟩ : syracuseStep 932095 = 1398143) B1398143
theorem B408191 : Blo 405769 408191 := bstep (se 1 (by rfl) ⟨306143, by rfl⟩ : syracuseStep 408191 = 612287) B612287
theorem B408543 : Blo 405769 408543 := bstep (se 1 (by rfl) ⟨306407, by rfl⟩ : syracuseStep 408543 = 612815) B612815
theorem B409711 : Blo 405769 409711 := bstep (se 1 (by rfl) ⟨307283, by rfl⟩ : syracuseStep 409711 = 614567) B614567
theorem B28264697 : Blo 405769 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B608999 : Blo 405769 608999 := bstep (se 1 (by rfl) ⟨456749, by rfl⟩ : syracuseStep 608999 = 913499) B913499
theorem B3754991 : Blo 405769 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B609839 : Blo 405769 609839 := bstep (se 1 (by rfl) ⟨457379, by rfl⟩ : syracuseStep 609839 = 914759) B914759
theorem B611111 : Blo 405769 611111 := bstep (se 1 (by rfl) ⟨458333, by rfl⟩ : syracuseStep 611111 = 916667) B916667
theorem B3169145 : Blo 405769 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B34003921 : Blo 405769 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B614399 : Blo 405769 614399 := bstep (se 1 (by rfl) ⟨460799, by rfl⟩ : syracuseStep 614399 = 921599) B921599
theorem B4023047 : Blo 405769 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B2057723 : Blo 405769 2057723 := bstep (se 1 (by rfl) ⟨1543292, by rfl⟩ : syracuseStep 2057723 = 3086585) B3086585
theorem B3925529 : Blo 405769 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B8908061 : Blo 405769 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B914057 : Blo 405769 914057 := bstep (se 2 (by rfl) ⟨342771, by rfl⟩ : syracuseStep 914057 = 685543) B685543
theorem B7829459 : Blo 405769 7829459 := bstep (se 1 (by rfl) ⟨5872094, by rfl⟩ : syracuseStep 7829459 = 11744189) B11744189
theorem B16152817 : Blo 405769 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B248117903 : Blo 405769 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B1048403 : Blo 405769 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B14484167 : Blo 405769 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B459679 : Blo 405769 459679 := bstep (se 1 (by rfl) ⟨344759, by rfl⟩ : syracuseStep 459679 = 689519) B689519
theorem B656351 : Blo 405769 656351 := bstep (se 1 (by rfl) ⟨492263, by rfl⟩ : syracuseStep 656351 = 984527) B984527
theorem B18843131 : Blo 405769 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B1312303 : Blo 405769 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B460615 : Blo 405769 460615 := bstep (se 1 (by rfl) ⟨345461, by rfl⟩ : syracuseStep 460615 = 690923) B690923
theorem B17893669 : Blo 405769 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B29755775 : Blo 405769 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B921455 : Blo 405769 921455 := bstep (se 1 (by rfl) ⟨691091, by rfl⟩ : syracuseStep 921455 = 1382183) B1382183
theorem B10458233 : Blo 405769 10458233 := bstep (se 2 (by rfl) ⟨3921837, by rfl⟩ : syracuseStep 10458233 = 7843675) B7843675
theorem B21537089 : Blo 405769 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B5219639 : Blo 405769 5219639 := bstep (se 1 (by rfl) ⟨3914729, by rfl⟩ : syracuseStep 5219639 = 7829459) B7829459
theorem B698935 : Blo 405769 698935 := bstep (se 1 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 698935 = 1048403) B1048403
theorem B1157915 : Blo 405769 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B5876711 : Blo 405769 5876711 := bstep (se 1 (by rfl) ⟨4407533, by rfl⟩ : syracuseStep 5876711 = 8815067) B8815067
theorem B405999 : Blo 405769 405999 := bstep (se 1 (by rfl) ⟨304499, by rfl⟩ : syracuseStep 405999 = 608999) B608999
theorem B2503327 : Blo 405769 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B10728125 : Blo 405769 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B406559 : Blo 405769 406559 := bstep (se 1 (by rfl) ⟨304919, by rfl⟩ : syracuseStep 406559 = 609839) B609839
theorem B13219595 : Blo 405769 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B407407 : Blo 405769 407407 := bstep (se 1 (by rfl) ⟨305555, by rfl⟩ : syracuseStep 407407 = 611111) B611111
theorem B2112763 : Blo 405769 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B409599 : Blo 405769 409599 := bstep (se 1 (by rfl) ⟨307199, by rfl⟩ : syracuseStep 409599 = 614399) B614399
theorem B1033499 : Blo 405769 1033499 := bstep (se 1 (by rfl) ⟨775124, by rfl⟩ : syracuseStep 1033499 = 1550249) B1550249
theorem B609371 : Blo 405769 609371 := bstep (se 1 (by rfl) ⟨457028, by rfl⟩ : syracuseStep 609371 = 914057) B914057
theorem B1166879 : Blo 405769 1166879 := bstep (se 1 (by rfl) ⟨875159, by rfl⟩ : syracuseStep 1166879 = 1750319) B1750319
theorem B45338561 : Blo 405769 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B1102241 : Blo 405769 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B611867 : Blo 405769 611867 := bstep (se 1 (by rfl) ⟨458900, by rfl⟩ : syracuseStep 611867 = 917801) B917801
theorem B11196073 : Blo 405769 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B612521 : Blo 405769 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B613103 : Blo 405769 613103 := bstep (se 1 (by rfl) ⟨459827, by rfl⟩ : syracuseStep 613103 = 919655) B919655
theorem B613319 : Blo 405769 613319 := bstep (se 1 (by rfl) ⟨459989, by rfl⟩ : syracuseStep 613319 = 919979) B919979
theorem B5856923 : Blo 405769 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B1371113 : Blo 405769 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B1469767 : Blo 405769 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B1371815 : Blo 405769 1371815 := bstep (se 1 (by rfl) ⟨1028861, by rfl⟩ : syracuseStep 1371815 = 2057723) B2057723
theorem B2617019 : Blo 405769 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B1242793 : Blo 405769 1242793 := bstep (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) B932095
theorem B23754829 : Blo 405769 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B165411935 : Blo 405769 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B688999 : Blo 405769 688999 := bstep (se 1 (by rfl) ⟨516749, by rfl⟩ : syracuseStep 688999 = 1033499) B1033499
theorem B23858225 : Blo 405769 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B3904615 : Blo 405769 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B14358059 : Blo 405769 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B3479759 : Blo 405769 3479759 := bstep (se 1 (by rfl) ⟨2609819, by rfl⟩ : syracuseStep 3479759 = 5219639) B5219639
theorem B1744679 : Blo 405769 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B7152083 : Blo 405769 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B6628229 : Blo 405769 6628229 := bstep (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) B1242793
theorem B110274623 : Blo 405769 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B437567 : Blo 405769 437567 := bstep (se 1 (by rfl) ⟨328175, by rfl⟩ : syracuseStep 437567 = 656351) B656351
theorem B12562087 : Blo 405769 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B19837183 : Blo 405769 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B406247 : Blo 405769 406247 := bstep (se 1 (by rfl) ⟨304685, by rfl⟩ : syracuseStep 406247 = 609371) B609371
theorem B1749737 : Blo 405769 1749737 := bstep (se 2 (by rfl) ⟨656151, by rfl⟩ : syracuseStep 1749737 = 1312303) B1312303
theorem B30225707 : Blo 405769 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B734827 : Blo 405769 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B931913 : Blo 405769 931913 := bstep (se 2 (by rfl) ⟨349467, by rfl⟩ : syracuseStep 931913 = 698935) B698935
theorem B407911 : Blo 405769 407911 := bstep (se 1 (by rfl) ⟨305933, by rfl⟩ : syracuseStep 407911 = 611867) B611867
theorem B408347 : Blo 405769 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B408735 : Blo 405769 408735 := bstep (se 1 (by rfl) ⟨306551, by rfl⟩ : syracuseStep 408735 = 613103) B613103
theorem B408879 : Blo 405769 408879 := bstep (se 1 (by rfl) ⟨306659, by rfl⟩ : syracuseStep 408879 = 613319) B613319
theorem B771943 : Blo 405769 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B3917807 : Blo 405769 3917807 := bstep (se 1 (by rfl) ⟨2938355, by rfl⟩ : syracuseStep 3917807 = 5876711) B5876711
theorem B14928097 : Blo 405769 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B31673105 : Blo 405769 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B9656111 : Blo 405769 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B612905 : Blo 405769 612905 := bstep (se 2 (by rfl) ⟨229839, by rfl⟩ : syracuseStep 612905 = 459679) B459679
theorem B777919 : Blo 405769 777919 := bstep (se 1 (by rfl) ⟨583439, by rfl⟩ : syracuseStep 777919 = 1166879) B1166879
theorem B614153 : Blo 405769 614153 := bstep (se 2 (by rfl) ⟨230307, by rfl⟩ : syracuseStep 614153 = 460615) B460615
theorem B614303 : Blo 405769 614303 := bstep (se 1 (by rfl) ⟨460727, by rfl⟩ : syracuseStep 614303 = 921455) B921455
theorem B6972155 : Blo 405769 6972155 := bstep (se 1 (by rfl) ⟨5229116, by rfl⟩ : syracuseStep 6972155 = 10458233) B10458233
theorem B1959689 : Blo 405769 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B3337769 : Blo 405769 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B914075 : Blo 405769 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B914543 : Blo 405769 914543 := bstep (se 1 (by rfl) ⟨685907, by rfl⟩ : syracuseStep 914543 = 1371815) B1371815
theorem B8813063 : Blo 405769 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B2817017 : Blo 405769 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B918665 : Blo 405769 918665 := bstep (se 2 (by rfl) ⟨344499, by rfl⟩ : syracuseStep 918665 = 688999) B688999
theorem B9572039 : Blo 405769 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B16749449 : Blo 405769 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B26449577 : Blo 405769 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B23501501 : Blo 405769 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B1878011 : Blo 405769 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B21115403 : Blo 405769 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B15905483 : Blo 405769 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B1029257 : Blo 405769 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B19904129 : Blo 405769 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B6437407 : Blo 405769 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B408603 : Blo 405769 408603 := bstep (se 1 (by rfl) ⟨306452, by rfl⟩ : syracuseStep 408603 = 612905) B612905
theorem B409435 : Blo 405769 409435 := bstep (se 1 (by rfl) ⟨307076, by rfl⟩ : syracuseStep 409435 = 614153) B614153
theorem B409535 : Blo 405769 409535 := bstep (se 1 (by rfl) ⟨307151, by rfl⟩ : syracuseStep 409535 = 614303) B614303
theorem B4768055 : Blo 405769 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B73516415 : Blo 405769 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B609383 : Blo 405769 609383 := bstep (se 1 (by rfl) ⟨457037, by rfl⟩ : syracuseStep 609383 = 914075) B914075
theorem B1166491 : Blo 405769 1166491 := bstep (se 1 (by rfl) ⟨874868, by rfl⟩ : syracuseStep 1166491 = 1749737) B1749737
theorem B609695 : Blo 405769 609695 := bstep (se 1 (by rfl) ⟨457271, by rfl⟩ : syracuseStep 609695 = 914543) B914543
theorem B1166845 : Blo 405769 1166845 := bstep (se 3 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 1166845 = 437567) B437567
theorem B1037225 : Blo 405769 1037225 := bstep (se 2 (by rfl) ⟨388959, by rfl⟩ : syracuseStep 1037225 = 777919) B777919
theorem B2611871 : Blo 405769 2611871 := bstep (se 1 (by rfl) ⟨1958903, by rfl⟩ : syracuseStep 2611871 = 3917807) B3917807
theorem B2319839 : Blo 405769 2319839 := bstep (se 1 (by rfl) ⟨1739879, by rfl⟩ : syracuseStep 2319839 = 3479759) B3479759
theorem B4648103 : Blo 405769 4648103 := bstep (se 1 (by rfl) ⟨3486077, by rfl⟩ : syracuseStep 4648103 = 6972155) B6972155
theorem B4418819 : Blo 405769 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B1306459 : Blo 405769 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B5206153 : Blo 405769 5206153 := bstep (se 2 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 5206153 = 3904615) B3904615
theorem B979769 : Blo 405769 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B2225179 : Blo 405769 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B20150471 : Blo 405769 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B621275 : Blo 405769 621275 := bstep (se 1 (by rfl) ⟨465956, by rfl⟩ : syracuseStep 621275 = 931913) B931913
theorem B4652477 : Blo 405769 4652477 := bstep (se 3 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 4652477 = 1744679) B1744679
theorem B3178703 : Blo 405769 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B691483 : Blo 405769 691483 := bstep (se 1 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 691483 = 1037225) B1037225
theorem B17633051 : Blo 405769 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B1741247 : Blo 405769 1741247 := bstep (se 1 (by rfl) ⟨1305935, by rfl⟩ : syracuseStep 1741247 = 2611871) B2611871
theorem B15667667 : Blo 405769 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B1546559 : Blo 405769 1546559 := bstep (se 1 (by rfl) ⟨1159919, by rfl⟩ : syracuseStep 1546559 = 2319839) B2319839
theorem B1252007 : Blo 405769 1252007 := bstep (se 1 (by rfl) ⟨939005, by rfl⟩ : syracuseStep 1252007 = 1878011) B1878011
theorem B406255 : Blo 405769 406255 := bstep (se 1 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 406255 = 609383) B609383
theorem B406463 : Blo 405769 406463 := bstep (se 1 (by rfl) ⟨304847, by rfl⟩ : syracuseStep 406463 = 609695) B609695
theorem B1555321 : Blo 405769 1555321 := bstep (se 2 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 1555321 = 1166491) B1166491
theorem B1555793 : Blo 405769 1555793 := bstep (se 2 (by rfl) ⟨583422, by rfl⟩ : syracuseStep 1555793 = 1166845) B1166845
theorem B2966905 : Blo 405769 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B1656733 : Blo 405769 1656733 := bstep (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) B621275
theorem B3098735 : Blo 405769 3098735 := bstep (se 1 (by rfl) ⟨2324051, by rfl⟩ : syracuseStep 3098735 = 4648103) B4648103
theorem B14076935 : Blo 405769 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B10603655 : Blo 405769 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B6967781 : Blo 405769 6967781 := bstep (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) B1306459
theorem B3101651 : Blo 405769 3101651 := bstep (se 1 (by rfl) ⟨2326238, by rfl⟩ : syracuseStep 3101651 = 4652477) B4652477
theorem B612443 : Blo 405769 612443 := bstep (se 1 (by rfl) ⟨459332, by rfl⟩ : syracuseStep 612443 = 918665) B918665
theorem B6381359 : Blo 405769 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B11166299 : Blo 405769 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B196043773 : Blo 405769 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B6941537 : Blo 405769 6941537 := bstep (se 2 (by rfl) ⟨2603076, by rfl⟩ : syracuseStep 6941537 = 5206153) B5206153
theorem B2945879 : Blo 405769 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B653179 : Blo 405769 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B8583209 : Blo 405769 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B686171 : Blo 405769 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B13269419 : Blo 405769 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B13433647 : Blo 405769 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B261391697 : Blo 405769 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B2065823 : Blo 405769 2065823 := bstep (se 1 (by rfl) ⟨1549367, by rfl⟩ : syracuseStep 2065823 = 3098735) B3098735
theorem B2067767 : Blo 405769 2067767 := bstep (se 1 (by rfl) ⟨1550825, by rfl⟩ : syracuseStep 2067767 = 3101651) B3101651
theorem B921977 : Blo 405769 921977 := bstep (se 2 (by rfl) ⟨345741, by rfl⟩ : syracuseStep 921977 = 691483) B691483
theorem B7444199 : Blo 405769 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B4627691 : Blo 405769 4627691 := bstep (se 1 (by rfl) ⟨3470768, by rfl⟩ : syracuseStep 4627691 = 6941537) B6941537
theorem B2073761 : Blo 405769 2073761 := bstep (se 2 (by rfl) ⟨777660, by rfl⟩ : syracuseStep 2073761 = 1555321) B1555321
theorem B9384623 : Blo 405769 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B2208977 : Blo 405769 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B1160831 : Blo 405769 1160831 := bstep (se 1 (by rfl) ⟨870623, by rfl⟩ : syracuseStep 1160831 = 1741247) B1741247
theorem B408295 : Blo 405769 408295 := bstep (se 1 (by rfl) ⟨306221, by rfl⟩ : syracuseStep 408295 = 612443) B612443
theorem B1031039 : Blo 405769 1031039 := bstep (se 1 (by rfl) ⟨773279, by rfl⟩ : syracuseStep 1031039 = 1546559) B1546559
theorem B834671 : Blo 405769 834671 := bstep (se 1 (by rfl) ⟨626003, by rfl⟩ : syracuseStep 834671 = 1252007) B1252007
theorem B870905 : Blo 405769 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B17911529 : Blo 405769 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B5722139 : Blo 405769 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B1037195 : Blo 405769 1037195 := bstep (se 1 (by rfl) ⟨777896, by rfl⟩ : syracuseStep 1037195 = 1555793) B1555793
theorem B2119135 : Blo 405769 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B3955873 : Blo 405769 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B7069103 : Blo 405769 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B11755367 : Blo 405769 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B10445111 : Blo 405769 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B4645187 : Blo 405769 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B4254239 : Blo 405769 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B1963919 : Blo 405769 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B457447 : Blo 405769 457447 := bstep (se 1 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 457447 = 686171) B686171
theorem B8846279 : Blo 405769 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B174261131 : Blo 405769 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B1377215 : Blo 405769 1377215 := bstep (se 1 (by rfl) ⟨1032911, by rfl⟩ : syracuseStep 1377215 = 2065823) B2065823
theorem B1378511 : Blo 405769 1378511 := bstep (se 1 (by rfl) ⟨1033883, by rfl⟩ : syracuseStep 1378511 = 2067767) B2067767
theorem B691463 : Blo 405769 691463 := bstep (se 1 (by rfl) ⟨518597, by rfl⟩ : syracuseStep 691463 = 1037195) B1037195
theorem B3085127 : Blo 405769 3085127 := bstep (se 1 (by rfl) ⟨2313845, by rfl⟩ : syracuseStep 3085127 = 4627691) B4627691
theorem B7836911 : Blo 405769 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B1382507 : Blo 405769 1382507 := bstep (se 1 (by rfl) ⟨1036880, by rfl⟩ : syracuseStep 1382507 = 2073761) B2073761
theorem B11344637 : Blo 405769 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B2825513 : Blo 405769 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B11941019 : Blo 405769 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B3814759 : Blo 405769 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B4962799 : Blo 405769 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B6963407 : Blo 405769 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B3096791 : Blo 405769 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B609929 : Blo 405769 609929 := bstep (se 2 (by rfl) ⟨228723, by rfl⟩ : syracuseStep 609929 = 457447) B457447
theorem B773887 : Blo 405769 773887 := bstep (se 1 (by rfl) ⟨580415, by rfl⟩ : syracuseStep 773887 = 1160831) B1160831
theorem B580603 : Blo 405769 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B614651 : Blo 405769 614651 := bstep (se 1 (by rfl) ⟨460988, by rfl⟩ : syracuseStep 614651 = 921977) B921977
theorem B4712735 : Blo 405769 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B6256415 : Blo 405769 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B1472651 : Blo 405769 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B1309279 : Blo 405769 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B5274497 : Blo 405769 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B687359 : Blo 405769 687359 := bstep (se 1 (by rfl) ⟨515519, by rfl⟩ : syracuseStep 687359 = 1031039) B1031039
theorem B5897519 : Blo 405769 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B556447 : Blo 405769 556447 := bstep (se 1 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 556447 = 834671) B834671
theorem B2064527 : Blo 405769 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B918143 : Blo 405769 918143 := bstep (se 1 (by rfl) ⟨688607, by rfl⟩ : syracuseStep 918143 = 1377215) B1377215
theorem B919007 : Blo 405769 919007 := bstep (se 1 (by rfl) ⟨689255, by rfl⟩ : syracuseStep 919007 = 1378511) B1378511
theorem B460975 : Blo 405769 460975 := bstep (se 1 (by rfl) ⟨345731, by rfl⟩ : syracuseStep 460975 = 691463) B691463
theorem B921671 : Blo 405769 921671 := bstep (se 1 (by rfl) ⟨691253, by rfl⟩ : syracuseStep 921671 = 1382507) B1382507
theorem B11870869 : Blo 405769 11870869 := bstep (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) B556447
theorem B1745705 : Blo 405769 1745705 := bstep (se 2 (by rfl) ⟨654639, by rfl⟩ : syracuseStep 1745705 = 1309279) B1309279
theorem B4170943 : Blo 405769 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B3516331 : Blo 405769 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B116174087 : Blo 405769 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B406619 : Blo 405769 406619 := bstep (se 1 (by rfl) ⟨304964, by rfl⟩ : syracuseStep 406619 = 609929) B609929
theorem B5224607 : Blo 405769 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B1883675 : Blo 405769 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B1031849 : Blo 405769 1031849 := bstep (se 2 (by rfl) ⟨386943, by rfl⟩ : syracuseStep 1031849 = 773887) B773887
theorem B409767 : Blo 405769 409767 := bstep (se 1 (by rfl) ⟨307325, by rfl⟩ : syracuseStep 409767 = 614651) B614651
theorem B774137 : Blo 405769 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B4642271 : Blo 405769 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B2056751 : Blo 405769 2056751 := bstep (se 1 (by rfl) ⟨1542563, by rfl⟩ : syracuseStep 2056751 = 3085127) B3085127
theorem B7563091 : Blo 405769 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B3141823 : Blo 405769 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B20345381 : Blo 405769 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B6617065 : Blo 405769 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B7960679 : Blo 405769 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B981767 : Blo 405769 981767 := bstep (se 1 (by rfl) ⟨736325, by rfl⟩ : syracuseStep 981767 = 1472651) B1472651
theorem B458239 : Blo 405769 458239 := bstep (se 1 (by rfl) ⟨343679, by rfl⟩ : syracuseStep 458239 = 687359) B687359
theorem B3931679 : Blo 405769 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B1376351 : Blo 405769 1376351 := bstep (se 1 (by rfl) ⟨1032263, by rfl⟩ : syracuseStep 1376351 = 2064527) B2064527
theorem B15827825 : Blo 405769 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B4688441 : Blo 405769 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B8822753 : Blo 405769 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B3483071 : Blo 405769 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B1255783 : Blo 405769 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B3094847 : Blo 405769 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B1163803 : Blo 405769 1163803 := bstep (se 1 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 1163803 = 1745705) B1745705
theorem B77449391 : Blo 405769 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B610985 : Blo 405769 610985 := bstep (se 2 (by rfl) ⟨229119, by rfl⟩ : syracuseStep 610985 = 458239) B458239
theorem B612095 : Blo 405769 612095 := bstep (se 1 (by rfl) ⟨459071, by rfl⟩ : syracuseStep 612095 = 918143) B918143
theorem B612671 : Blo 405769 612671 := bstep (se 1 (by rfl) ⟨459503, by rfl⟩ : syracuseStep 612671 = 919007) B919007
theorem B5561257 : Blo 405769 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B10084121 : Blo 405769 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B614447 : Blo 405769 614447 := bstep (se 1 (by rfl) ⟨460835, by rfl⟩ : syracuseStep 614447 = 921671) B921671
theorem B614633 : Blo 405769 614633 := bstep (se 2 (by rfl) ⟨230487, by rfl⟩ : syracuseStep 614633 = 460975) B460975
theorem B4189097 : Blo 405769 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B1371167 : Blo 405769 1371167 := bstep (se 1 (by rfl) ⟨1028375, by rfl⟩ : syracuseStep 1371167 = 2056751) B2056751
theorem B2618045 : Blo 405769 2618045 := bstep (se 3 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 2618045 = 981767) B981767
theorem B13563587 : Blo 405769 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B5307119 : Blo 405769 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B10484477 : Blo 405769 10484477 := bstep (se 3 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 10484477 = 3931679) B3931679
theorem B687899 : Blo 405769 687899 := bstep (se 1 (by rfl) ⟨515924, by rfl⟩ : syracuseStep 687899 = 1031849) B1031849
theorem B2064365 : Blo 405769 2064365 := bstep (se 3 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 2064365 = 774137) B774137
theorem B917567 : Blo 405769 917567 := bstep (se 1 (by rfl) ⟨688175, by rfl⟩ : syracuseStep 917567 = 1376351) B1376351
theorem B10551883 : Blo 405769 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B1674377 : Blo 405769 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B6722747 : Blo 405769 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B2792731 : Blo 405769 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B1745363 : Blo 405769 1745363 := bstep (se 1 (by rfl) ⟨1309022, by rfl⟩ : syracuseStep 1745363 = 2618045) B2618045
theorem B7415009 : Blo 405769 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B6989651 : Blo 405769 6989651 := bstep (se 1 (by rfl) ⟨5242238, by rfl⟩ : syracuseStep 6989651 = 10484477) B10484477
theorem B1551737 : Blo 405769 1551737 := bstep (se 2 (by rfl) ⟨581901, by rfl⟩ : syracuseStep 1551737 = 1163803) B1163803
theorem B3125627 : Blo 405769 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B407323 : Blo 405769 407323 := bstep (se 1 (by rfl) ⟨305492, by rfl⟩ : syracuseStep 407323 = 610985) B610985
theorem B408063 : Blo 405769 408063 := bstep (se 1 (by rfl) ⟨306047, by rfl⟩ : syracuseStep 408063 = 612095) B612095
theorem B408447 : Blo 405769 408447 := bstep (se 1 (by rfl) ⟨306335, by rfl⟩ : syracuseStep 408447 = 612671) B612671
theorem B5881835 : Blo 405769 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B409631 : Blo 405769 409631 := bstep (se 1 (by rfl) ⟨307223, by rfl⟩ : syracuseStep 409631 = 614447) B614447
theorem B409755 : Blo 405769 409755 := bstep (se 1 (by rfl) ⟨307316, by rfl⟩ : syracuseStep 409755 = 614633) B614633
theorem B51632927 : Blo 405769 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B2322047 : Blo 405769 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B914111 : Blo 405769 914111 := bstep (se 1 (by rfl) ⟨685583, by rfl⟩ : syracuseStep 914111 = 1371167) B1371167
theorem B9042391 : Blo 405769 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B2063231 : Blo 405769 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B3538079 : Blo 405769 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B458599 : Blo 405769 458599 := bstep (se 1 (by rfl) ⟨343949, by rfl⟩ : syracuseStep 458599 = 687899) B687899
theorem B1376243 : Blo 405769 1376243 := bstep (se 1 (by rfl) ⟨1032182, by rfl⟩ : syracuseStep 1376243 = 2064365) B2064365
theorem B1116251 : Blo 405769 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B4659767 : Blo 405769 4659767 := bstep (se 1 (by rfl) ⟨3494825, by rfl⟩ : syracuseStep 4659767 = 6989651) B6989651
theorem B1548031 : Blo 405769 1548031 := bstep (se 1 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 1548031 = 2322047) B2322047
theorem B14069177 : Blo 405769 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B34421951 : Blo 405769 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B1163575 : Blo 405769 1163575 := bstep (se 1 (by rfl) ⟨872681, by rfl⟩ : syracuseStep 1163575 = 1745363) B1745363
theorem B1034491 : Blo 405769 1034491 := bstep (se 1 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 1034491 = 1551737) B1551737
theorem B2083751 : Blo 405769 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B609407 : Blo 405769 609407 := bstep (se 1 (by rfl) ⟨457055, by rfl⟩ : syracuseStep 609407 = 914111) B914111
theorem B3723641 : Blo 405769 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B611465 : Blo 405769 611465 := bstep (se 2 (by rfl) ⟨229299, by rfl⟩ : syracuseStep 611465 = 458599) B458599
theorem B3921223 : Blo 405769 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B611711 : Blo 405769 611711 := bstep (se 1 (by rfl) ⟨458783, by rfl⟩ : syracuseStep 611711 = 917567) B917567
theorem B4481831 : Blo 405769 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B4943339 : Blo 405769 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B12056521 : Blo 405769 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B1375487 : Blo 405769 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B2358719 : Blo 405769 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B917495 : Blo 405769 917495 := bstep (se 1 (by rfl) ⟨688121, by rfl⟩ : syracuseStep 917495 = 1376243) B1376243
theorem B1379321 : Blo 405769 1379321 := bstep (se 2 (by rfl) ⟨517245, by rfl⟩ : syracuseStep 1379321 = 1034491) B1034491
theorem B2987887 : Blo 405769 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B9379451 : Blo 405769 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B22947967 : Blo 405769 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B1551433 : Blo 405769 1551433 := bstep (se 2 (by rfl) ⟨581787, by rfl⟩ : syracuseStep 1551433 = 1163575) B1163575
theorem B1389167 : Blo 405769 1389167 := bstep (se 1 (by rfl) ⟨1041875, by rfl⟩ : syracuseStep 1389167 = 2083751) B2083751
theorem B406271 : Blo 405769 406271 := bstep (se 1 (by rfl) ⟨304703, by rfl⟩ : syracuseStep 406271 = 609407) B609407
theorem B407643 : Blo 405769 407643 := bstep (se 1 (by rfl) ⟨305732, by rfl⟩ : syracuseStep 407643 = 611465) B611465
theorem B407807 : Blo 405769 407807 := bstep (se 1 (by rfl) ⟨305855, by rfl⟩ : syracuseStep 407807 = 611711) B611711
theorem B5228297 : Blo 405769 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B3295559 : Blo 405769 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B16075361 : Blo 405769 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B611663 : Blo 405769 611663 := bstep (se 1 (by rfl) ⟨458747, by rfl⟩ : syracuseStep 611663 = 917495) B917495
theorem B744167 : Blo 405769 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B2482427 : Blo 405769 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B3106511 : Blo 405769 3106511 := bstep (se 1 (by rfl) ⟨2329883, by rfl⟩ : syracuseStep 3106511 = 4659767) B4659767
theorem B916991 : Blo 405769 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B1572479 : Blo 405769 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B2064041 : Blo 405769 2064041 := bstep (se 2 (by rfl) ⟨774015, by rfl⟩ : syracuseStep 2064041 = 1548031) B1548031
theorem B122389157 : Blo 405769 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B2197039 : Blo 405769 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B10716907 : Blo 405769 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B919547 : Blo 405769 919547 := bstep (se 1 (by rfl) ⟨689660, by rfl⟩ : syracuseStep 919547 = 1379321) B1379321
theorem B2068577 : Blo 405769 2068577 := bstep (se 2 (by rfl) ⟨775716, by rfl⟩ : syracuseStep 2068577 = 1551433) B1551433
theorem B2071007 : Blo 405769 2071007 := bstep (se 1 (by rfl) ⟨1553255, by rfl⟩ : syracuseStep 2071007 = 3106511) B3106511
theorem B926111 : Blo 405769 926111 := bstep (se 1 (by rfl) ⟨694583, by rfl⟩ : syracuseStep 926111 = 1389167) B1389167
theorem B3485531 : Blo 405769 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B407775 : Blo 405769 407775 := bstep (se 1 (by rfl) ⟨305831, by rfl⟩ : syracuseStep 407775 = 611663) B611663
theorem B1654951 : Blo 405769 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B1984445 : Blo 405769 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B3983849 : Blo 405769 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B611327 : Blo 405769 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B6252967 : Blo 405769 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B1048319 : Blo 405769 1048319 := bstep (se 1 (by rfl) ⟨786239, by rfl⟩ : syracuseStep 1048319 = 1572479) B1572479
theorem B1376027 : Blo 405769 1376027 := bstep (se 1 (by rfl) ⟨1032020, by rfl⟩ : syracuseStep 1376027 = 2064041) B2064041
theorem B81592771 : Blo 405769 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B2655899 : Blo 405769 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B14289209 : Blo 405769 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B1379051 : Blo 405769 1379051 := bstep (se 1 (by rfl) ⟨1034288, by rfl⟩ : syracuseStep 1379051 = 2068577) B2068577
theorem B1380671 : Blo 405769 1380671 := bstep (se 1 (by rfl) ⟨1035503, by rfl⟩ : syracuseStep 1380671 = 2071007) B2071007
theorem B698879 : Blo 405769 698879 := bstep (se 1 (by rfl) ⟨524159, by rfl⟩ : syracuseStep 698879 = 1048319) B1048319
theorem B2206601 : Blo 405769 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B2469629 : Blo 405769 2469629 := bstep (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) B926111
theorem B1322963 : Blo 405769 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B2929385 : Blo 405769 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B8337289 : Blo 405769 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B407551 : Blo 405769 407551 := bstep (se 1 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 407551 = 611327) B611327
theorem B613031 : Blo 405769 613031 := bstep (se 1 (by rfl) ⟨459773, by rfl⟩ : syracuseStep 613031 = 919547) B919547
theorem B2323687 : Blo 405769 2323687 := bstep (se 1 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 2323687 = 3485531) B3485531
theorem B917351 : Blo 405769 917351 := bstep (se 1 (by rfl) ⟨688013, by rfl⟩ : syracuseStep 917351 = 1376027) B1376027
theorem B108790361 : Blo 405769 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B1770599 : Blo 405769 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B919367 : Blo 405769 919367 := bstep (se 1 (by rfl) ⟨689525, by rfl⟩ : syracuseStep 919367 = 1379051) B1379051
theorem B920447 : Blo 405769 920447 := bstep (se 1 (by rfl) ⟨690335, by rfl⟩ : syracuseStep 920447 = 1380671) B1380671
theorem B1646419 : Blo 405769 1646419 := bstep (se 1 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 1646419 = 2469629) B2469629
theorem B11116385 : Blo 405769 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B408687 : Blo 405769 408687 := bstep (se 1 (by rfl) ⟨306515, by rfl⟩ : syracuseStep 408687 = 613031) B613031
theorem B3098249 : Blo 405769 3098249 := bstep (se 2 (by rfl) ⟨1161843, by rfl⟩ : syracuseStep 3098249 = 2323687) B2323687
theorem B1952923 : Blo 405769 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B611567 : Blo 405769 611567 := bstep (se 1 (by rfl) ⟨458675, by rfl⟩ : syracuseStep 611567 = 917351) B917351
theorem B9526139 : Blo 405769 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B1863677 : Blo 405769 1863677 := bstep (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) B698879
theorem B1471067 : Blo 405769 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B881975 : Blo 405769 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B2065499 : Blo 405769 2065499 := bstep (se 1 (by rfl) ⟨1549124, by rfl⟩ : syracuseStep 2065499 = 3098249) B3098249
theorem B4721597 : Blo 405769 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B7410923 : Blo 405769 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B72526907 : Blo 405769 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B407711 : Blo 405769 407711 := bstep (se 1 (by rfl) ⟨305783, by rfl⟩ : syracuseStep 407711 = 611567) B611567
theorem B2603897 : Blo 405769 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B612911 : Blo 405769 612911 := bstep (se 1 (by rfl) ⟨459683, by rfl⟩ : syracuseStep 612911 = 919367) B919367
theorem B613631 : Blo 405769 613631 := bstep (se 1 (by rfl) ⟨460223, by rfl⟩ : syracuseStep 613631 = 920447) B920447
theorem B6350759 : Blo 405769 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B1242451 : Blo 405769 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B980711 : Blo 405769 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B587983 : Blo 405769 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B2195225 : Blo 405769 2195225 := bstep (se 2 (by rfl) ⟨823209, by rfl⟩ : syracuseStep 2195225 = 1646419) B1646419
theorem B1376999 : Blo 405769 1376999 := bstep (se 1 (by rfl) ⟨1032749, by rfl⟩ : syracuseStep 1376999 = 2065499) B2065499
theorem B3147731 : Blo 405769 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B6626405 : Blo 405769 6626405 := bstep (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) B1242451
theorem B67741429 : Blo 405769 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B408607 : Blo 405769 408607 := bstep (se 1 (by rfl) ⟨306455, by rfl⟩ : syracuseStep 408607 = 612911) B612911
theorem B409087 : Blo 405769 409087 := bstep (se 1 (by rfl) ⟨306815, by rfl⟩ : syracuseStep 409087 = 613631) B613631
theorem B48351271 : Blo 405769 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B1463483 : Blo 405769 1463483 := bstep (se 1 (by rfl) ⟨1097612, by rfl⟩ : syracuseStep 1463483 = 2195225) B2195225
theorem B4940615 : Blo 405769 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B783977 : Blo 405769 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B653807 : Blo 405769 653807 := bstep (se 1 (by rfl) ⟨490355, by rfl⟩ : syracuseStep 653807 = 980711) B980711
theorem B1735931 : Blo 405769 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B917999 : Blo 405769 917999 := bstep (se 1 (by rfl) ⟨688499, by rfl⟩ : syracuseStep 917999 = 1376999) B1376999
theorem B2098487 : Blo 405769 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B17670413 : Blo 405769 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B4629149 : Blo 405769 4629149 := bstep (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) B1735931
theorem B435871 : Blo 405769 435871 := bstep (se 1 (by rfl) ⟨326903, by rfl⟩ : syracuseStep 435871 = 653807) B653807
theorem B90321905 : Blo 405769 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B64468361 : Blo 405769 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B3293743 : Blo 405769 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B975655 : Blo 405769 975655 := bstep (se 1 (by rfl) ⟨731741, by rfl⟩ : syracuseStep 975655 = 1463483) B1463483
theorem B2090605 : Blo 405769 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B4391657 : Blo 405769 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B2787473 : Blo 405769 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B3086099 : Blo 405769 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B11780275 : Blo 405769 11780275 := bstep (se 1 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 11780275 = 17670413) B17670413
theorem B60214603 : Blo 405769 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B42978907 : Blo 405769 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B611999 : Blo 405769 611999 := bstep (se 1 (by rfl) ⟨458999, by rfl⟩ : syracuseStep 611999 = 917999) B917999
theorem B1300873 : Blo 405769 1300873 := bstep (se 2 (by rfl) ⟨487827, by rfl⟩ : syracuseStep 1300873 = 975655) B975655
theorem B5595965 : Blo 405769 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B2324645 : Blo 405769 2324645 := bstep (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) B435871
theorem B80286137 : Blo 405769 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B229220837 : Blo 405769 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B1549763 : Blo 405769 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B15707033 : Blo 405769 15707033 := bstep (se 2 (by rfl) ⟨5890137, by rfl⟩ : syracuseStep 15707033 = 11780275) B11780275
theorem B2927771 : Blo 405769 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B407999 : Blo 405769 407999 := bstep (se 1 (by rfl) ⟨305999, by rfl⟩ : syracuseStep 407999 = 611999) B611999
theorem B1858315 : Blo 405769 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B2057399 : Blo 405769 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B3730643 : Blo 405769 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B1734497 : Blo 405769 1734497 := bstep (se 2 (by rfl) ⟨650436, by rfl⟩ : syracuseStep 1734497 = 1300873) B1300873
theorem B1156331 : Blo 405769 1156331 := bstep (se 1 (by rfl) ⟨867248, by rfl⟩ : syracuseStep 1156331 = 1734497) B1734497
theorem B53524091 : Blo 405769 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B152813891 : Blo 405769 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B1033175 : Blo 405769 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B10471355 : Blo 405769 10471355 := bstep (se 1 (by rfl) ⟨7853516, by rfl⟩ : syracuseStep 10471355 = 15707033) B15707033
theorem B1951847 : Blo 405769 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B2477753 : Blo 405769 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B1371599 : Blo 405769 1371599 := bstep (se 1 (by rfl) ⟨1028699, by rfl⟩ : syracuseStep 1371599 = 2057399) B2057399
theorem B2487095 : Blo 405769 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B101875927 : Blo 405769 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B688783 : Blo 405769 688783 := bstep (se 1 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 688783 = 1033175) B1033175
theorem B6980903 : Blo 405769 6980903 := bstep (se 1 (by rfl) ⟨5235677, by rfl⟩ : syracuseStep 6980903 = 10471355) B10471355
theorem B1651835 : Blo 405769 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B770887 : Blo 405769 770887 := bstep (se 1 (by rfl) ⟨578165, by rfl⟩ : syracuseStep 770887 = 1156331) B1156331
theorem B1658063 : Blo 405769 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B1301231 : Blo 405769 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B914399 : Blo 405769 914399 := bstep (se 1 (by rfl) ⟨685799, by rfl⟩ : syracuseStep 914399 = 1371599) B1371599
theorem B35682727 : Blo 405769 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B918377 : Blo 405769 918377 := bstep (se 2 (by rfl) ⟨344391, by rfl⟩ : syracuseStep 918377 = 688783) B688783
theorem B4653935 : Blo 405769 4653935 := bstep (se 1 (by rfl) ⟨3490451, by rfl⟩ : syracuseStep 4653935 = 6980903) B6980903
theorem B135834569 : Blo 405769 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B1027849 : Blo 405769 1027849 := bstep (se 2 (by rfl) ⟨385443, by rfl⟩ : syracuseStep 1027849 = 770887) B770887
theorem B609599 : Blo 405769 609599 := bstep (se 1 (by rfl) ⟨457199, by rfl⟩ : syracuseStep 609599 = 914399) B914399
theorem B1101223 : Blo 405769 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B1105375 : Blo 405769 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B3469949 : Blo 405769 3469949 := bstep (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) B1301231
theorem B47576969 : Blo 405769 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B406399 : Blo 405769 406399 := bstep (se 1 (by rfl) ⟨304799, by rfl⟩ : syracuseStep 406399 = 609599) B609599
theorem B90556379 : Blo 405769 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B2313299 : Blo 405769 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B612251 : Blo 405769 612251 := bstep (se 1 (by rfl) ⟨459188, by rfl⟩ : syracuseStep 612251 = 918377) B918377
theorem B3102623 : Blo 405769 3102623 := bstep (se 1 (by rfl) ⟨2326967, by rfl⟩ : syracuseStep 3102623 = 4653935) B4653935
theorem B1468297 : Blo 405769 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B1370465 : Blo 405769 1370465 := bstep (se 2 (by rfl) ⟨513924, by rfl⟩ : syracuseStep 1370465 = 1027849) B1027849
theorem B31717979 : Blo 405769 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B1473833 : Blo 405769 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B1542199 : Blo 405769 1542199 := bstep (se 1 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 1542199 = 2313299) B2313299
theorem B2068415 : Blo 405769 2068415 := bstep (se 1 (by rfl) ⟨1551311, by rfl⟩ : syracuseStep 2068415 = 3102623) B3102623
theorem B21145319 : Blo 405769 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B60370919 : Blo 405769 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B408167 : Blo 405769 408167 := bstep (se 1 (by rfl) ⟨306125, by rfl⟩ : syracuseStep 408167 = 612251) B612251
theorem B913643 : Blo 405769 913643 := bstep (se 1 (by rfl) ⟨685232, by rfl⟩ : syracuseStep 913643 = 1370465) B1370465
theorem B3930221 : Blo 405769 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B7830917 : Blo 405769 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B1378943 : Blo 405769 1378943 := bstep (se 1 (by rfl) ⟨1034207, by rfl⟩ : syracuseStep 1378943 = 2068415) B2068415
theorem B14096879 : Blo 405769 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B40247279 : Blo 405769 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B5220611 : Blo 405769 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B609095 : Blo 405769 609095 := bstep (se 1 (by rfl) ⟨456821, by rfl⟩ : syracuseStep 609095 = 913643) B913643
theorem B2056265 : Blo 405769 2056265 := bstep (se 2 (by rfl) ⟨771099, by rfl⟩ : syracuseStep 2056265 = 1542199) B1542199
theorem B2620147 : Blo 405769 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B919295 : Blo 405769 919295 := bstep (se 1 (by rfl) ⟨689471, by rfl⟩ : syracuseStep 919295 = 1378943) B1378943
theorem B3480407 : Blo 405769 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B406063 : Blo 405769 406063 := bstep (se 1 (by rfl) ⟨304547, by rfl⟩ : syracuseStep 406063 = 609095) B609095
theorem B3493529 : Blo 405769 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B9397919 : Blo 405769 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B26831519 : Blo 405769 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B1370843 : Blo 405769 1370843 := bstep (se 1 (by rfl) ⟨1028132, by rfl⟩ : syracuseStep 1370843 = 2056265) B2056265
theorem B2329019 : Blo 405769 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B6265279 : Blo 405769 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B612863 : Blo 405769 612863 := bstep (se 1 (by rfl) ⟨459647, by rfl⟩ : syracuseStep 612863 = 919295) B919295
theorem B2320271 : Blo 405769 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B17887679 : Blo 405769 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B913895 : Blo 405769 913895 := bstep (se 1 (by rfl) ⟨685421, by rfl⟩ : syracuseStep 913895 = 1370843) B1370843
theorem B1546847 : Blo 405769 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B1552679 : Blo 405769 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B408575 : Blo 405769 408575 := bstep (se 1 (by rfl) ⟨306431, by rfl⟩ : syracuseStep 408575 = 612863) B612863
theorem B609263 : Blo 405769 609263 := bstep (se 1 (by rfl) ⟨456947, by rfl⟩ : syracuseStep 609263 = 913895) B913895
theorem B11925119 : Blo 405769 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B8353705 : Blo 405769 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B406175 : Blo 405769 406175 := bstep (se 1 (by rfl) ⟨304631, by rfl⟩ : syracuseStep 406175 = 609263) B609263
theorem B1031231 : Blo 405769 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B1035119 : Blo 405769 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B7950079 : Blo 405769 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B11138273 : Blo 405769 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B690079 : Blo 405769 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B10600105 : Blo 405769 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B7425515 : Blo 405769 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B687487 : Blo 405769 687487 := bstep (se 1 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 687487 = 1031231) B1031231
theorem B4950343 : Blo 405769 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B920105 : Blo 405769 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B14133473 : Blo 405769 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B916649 : Blo 405769 916649 := bstep (se 2 (by rfl) ⟨343743, by rfl⟩ : syracuseStep 916649 = 687487) B687487
theorem B6600457 : Blo 405769 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B9422315 : Blo 405769 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B611099 : Blo 405769 611099 := bstep (se 1 (by rfl) ⟨458324, by rfl⟩ : syracuseStep 611099 = 916649) B916649
theorem B613403 : Blo 405769 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B407399 : Blo 405769 407399 := bstep (se 1 (by rfl) ⟨305549, by rfl⟩ : syracuseStep 407399 = 611099) B611099
theorem B408935 : Blo 405769 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B8800609 : Blo 405769 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B6281543 : Blo 405769 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B11734145 : Blo 405769 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B4187695 : Blo 405769 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 405769 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B7822763 : Blo 405769 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B5215175 : Blo 405769 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B3722395 : Blo 405769 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B3476783 : Blo 405769 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B4963193 : Blo 405769 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B2317855 : Blo 405769 2317855 := bstep (se 1 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 2317855 = 3476783) B3476783
theorem B3308795 : Blo 405769 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B3090473 : Blo 405769 3090473 := bstep (se 2 (by rfl) ⟨1158927, by rfl⟩ : syracuseStep 3090473 = 2317855) B2317855
theorem B2205863 : Blo 405769 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B2060315 : Blo 405769 2060315 := bstep (se 1 (by rfl) ⟨1545236, by rfl⟩ : syracuseStep 2060315 = 3090473) B3090473
theorem B1470575 : Blo 405769 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B3921533 : Blo 405769 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B1373543 : Blo 405769 1373543 := bstep (se 1 (by rfl) ⟨1030157, by rfl⟩ : syracuseStep 1373543 = 2060315) B2060315
theorem B2614355 : Blo 405769 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B915695 : Blo 405769 915695 := bstep (se 1 (by rfl) ⟨686771, by rfl⟩ : syracuseStep 915695 = 1373543) B1373543
theorem B1742903 : Blo 405769 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B610463 : Blo 405769 610463 := bstep (se 1 (by rfl) ⟨457847, by rfl⟩ : syracuseStep 610463 = 915695) B915695
theorem B406975 : Blo 405769 406975 := bstep (se 1 (by rfl) ⟨305231, by rfl⟩ : syracuseStep 406975 = 610463) B610463
theorem B1161935 : Blo 405769 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903
theorem B774623 : Blo 405769 774623 := bstep (se 1 (by rfl) ⟨580967, by rfl⟩ : syracuseStep 774623 = 1161935) B1161935
theorem B2065661 : Blo 405769 2065661 := bstep (se 3 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 2065661 = 774623) B774623
theorem B1377107 : Blo 405769 1377107 := bstep (se 1 (by rfl) ⟨1032830, by rfl⟩ : syracuseStep 1377107 = 2065661) B2065661
theorem B918071 : Blo 405769 918071 := bstep (se 1 (by rfl) ⟨688553, by rfl⟩ : syracuseStep 918071 = 1377107) B1377107
theorem B612047 : Blo 405769 612047 := bstep (se 1 (by rfl) ⟨459035, by rfl⟩ : syracuseStep 612047 = 918071) B918071
theorem B408031 : Blo 405769 408031 := bstep (se 1 (by rfl) ⟨306023, by rfl⟩ : syracuseStep 408031 = 612047) B612047

theorem C0 (j : ℕ) (h1 : 101442 ≤ j) (h2 : j ≤ 102141) : Blo 405769 (4 * j + 3) := by
  interval_cases j
  · exact B405771
  · exact B405775
  · exact B405779
  · exact B405783
  · exact B405787
  · exact B405791
  · exact B405795
  · exact B405799
  · exact B405803
  · exact B405807
  · exact B405811
  · exact B405815
  · exact B405819
  · exact B405823
  · exact B405827
  · exact B405831
  · exact B405835
  · exact B405839
  · exact B405843
  · exact B405847
  · exact B405851
  · exact B405855
  · exact B405859
  · exact B405863
  · exact B405867
  · exact B405871
  · exact B405875
  · exact B405879
  · exact B405883
  · exact B405887
  · exact B405891
  · exact B405895
  · exact B405899
  · exact B405903
  · exact B405907
  · exact B405911
  · exact B405915
  · exact B405919
  · exact B405923
  · exact B405927
  · exact B405931
  · exact B405935
  · exact B405939
  · exact B405943
  · exact B405947
  · exact B405951
  · exact B405955
  · exact B405959
  · exact B405963
  · exact B405967
  · exact B405971
  · exact B405975
  · exact B405979
  · exact B405983
  · exact B405987
  · exact B405991
  · exact B405995
  · exact B405999
  · exact B406003
  · exact B406007
  · exact B406011
  · exact B406015
  · exact B406019
  · exact B406023
  · exact B406027
  · exact B406031
  · exact B406035
  · exact B406039
  · exact B406043
  · exact B406047
  · exact B406051
  · exact B406055
  · exact B406059
  · exact B406063
  · exact B406067
  · exact B406071
  · exact B406075
  · exact B406079
  · exact B406083
  · exact B406087
  · exact B406091
  · exact B406095
  · exact B406099
  · exact B406103
  · exact B406107
  · exact B406111
  · exact B406115
  · exact B406119
  · exact B406123
  · exact B406127
  · exact B406131
  · exact B406135
  · exact B406139
  · exact B406143
  · exact B406147
  · exact B406151
  · exact B406155
  · exact B406159
  · exact B406163
  · exact B406167
  · exact B406171
  · exact B406175
  · exact B406179
  · exact B406183
  · exact B406187
  · exact B406191
  · exact B406195
  · exact B406199
  · exact B406203
  · exact B406207
  · exact B406211
  · exact B406215
  · exact B406219
  · exact B406223
  · exact B406227
  · exact B406231
  · exact B406235
  · exact B406239
  · exact B406243
  · exact B406247
  · exact B406251
  · exact B406255
  · exact B406259
  · exact B406263
  · exact B406267
  · exact B406271
  · exact B406275
  · exact B406279
  · exact B406283
  · exact B406287
  · exact B406291
  · exact B406295
  · exact B406299
  · exact B406303
  · exact B406307
  · exact B406311
  · exact B406315
  · exact B406319
  · exact B406323
  · exact B406327
  · exact B406331
  · exact B406335
  · exact B406339
  · exact B406343
  · exact B406347
  · exact B406351
  · exact B406355
  · exact B406359
  · exact B406363
  · exact B406367
  · exact B406371
  · exact B406375
  · exact B406379
  · exact B406383
  · exact B406387
  · exact B406391
  · exact B406395
  · exact B406399
  · exact B406403
  · exact B406407
  · exact B406411
  · exact B406415
  · exact B406419
  · exact B406423
  · exact B406427
  · exact B406431
  · exact B406435
  · exact B406439
  · exact B406443
  · exact B406447
  · exact B406451
  · exact B406455
  · exact B406459
  · exact B406463
  · exact B406467
  · exact B406471
  · exact B406475
  · exact B406479
  · exact B406483
  · exact B406487
  · exact B406491
  · exact B406495
  · exact B406499
  · exact B406503
  · exact B406507
  · exact B406511
  · exact B406515
  · exact B406519
  · exact B406523
  · exact B406527
  · exact B406531
  · exact B406535
  · exact B406539
  · exact B406543
  · exact B406547
  · exact B406551
  · exact B406555
  · exact B406559
  · exact B406563
  · exact B406567
  · exact B406571
  · exact B406575
  · exact B406579
  · exact B406583
  · exact B406587
  · exact B406591
  · exact B406595
  · exact B406599
  · exact B406603
  · exact B406607
  · exact B406611
  · exact B406615
  · exact B406619
  · exact B406623
  · exact B406627
  · exact B406631
  · exact B406635
  · exact B406639
  · exact B406643
  · exact B406647
  · exact B406651
  · exact B406655
  · exact B406659
  · exact B406663
  · exact B406667
  · exact B406671
  · exact B406675
  · exact B406679
  · exact B406683
  · exact B406687
  · exact B406691
  · exact B406695
  · exact B406699
  · exact B406703
  · exact B406707
  · exact B406711
  · exact B406715
  · exact B406719
  · exact B406723
  · exact B406727
  · exact B406731
  · exact B406735
  · exact B406739
  · exact B406743
  · exact B406747
  · exact B406751
  · exact B406755
  · exact B406759
  · exact B406763
  · exact B406767
  · exact B406771
  · exact B406775
  · exact B406779
  · exact B406783
  · exact B406787
  · exact B406791
  · exact B406795
  · exact B406799
  · exact B406803
  · exact B406807
  · exact B406811
  · exact B406815
  · exact B406819
  · exact B406823
  · exact B406827
  · exact B406831
  · exact B406835
  · exact B406839
  · exact B406843
  · exact B406847
  · exact B406851
  · exact B406855
  · exact B406859
  · exact B406863
  · exact B406867
  · exact B406871
  · exact B406875
  · exact B406879
  · exact B406883
  · exact B406887
  · exact B406891
  · exact B406895
  · exact B406899
  · exact B406903
  · exact B406907
  · exact B406911
  · exact B406915
  · exact B406919
  · exact B406923
  · exact B406927
  · exact B406931
  · exact B406935
  · exact B406939
  · exact B406943
  · exact B406947
  · exact B406951
  · exact B406955
  · exact B406959
  · exact B406963
  · exact B406967
  · exact B406971
  · exact B406975
  · exact B406979
  · exact B406983
  · exact B406987
  · exact B406991
  · exact B406995
  · exact B406999
  · exact B407003
  · exact B407007
  · exact B407011
  · exact B407015
  · exact B407019
  · exact B407023
  · exact B407027
  · exact B407031
  · exact B407035
  · exact B407039
  · exact B407043
  · exact B407047
  · exact B407051
  · exact B407055
  · exact B407059
  · exact B407063
  · exact B407067
  · exact B407071
  · exact B407075
  · exact B407079
  · exact B407083
  · exact B407087
  · exact B407091
  · exact B407095
  · exact B407099
  · exact B407103
  · exact B407107
  · exact B407111
  · exact B407115
  · exact B407119
  · exact B407123
  · exact B407127
  · exact B407131
  · exact B407135
  · exact B407139
  · exact B407143
  · exact B407147
  · exact B407151
  · exact B407155
  · exact B407159
  · exact B407163
  · exact B407167
  · exact B407171
  · exact B407175
  · exact B407179
  · exact B407183
  · exact B407187
  · exact B407191
  · exact B407195
  · exact B407199
  · exact B407203
  · exact B407207
  · exact B407211
  · exact B407215
  · exact B407219
  · exact B407223
  · exact B407227
  · exact B407231
  · exact B407235
  · exact B407239
  · exact B407243
  · exact B407247
  · exact B407251
  · exact B407255
  · exact B407259
  · exact B407263
  · exact B407267
  · exact B407271
  · exact B407275
  · exact B407279
  · exact B407283
  · exact B407287
  · exact B407291
  · exact B407295
  · exact B407299
  · exact B407303
  · exact B407307
  · exact B407311
  · exact B407315
  · exact B407319
  · exact B407323
  · exact B407327
  · exact B407331
  · exact B407335
  · exact B407339
  · exact B407343
  · exact B407347
  · exact B407351
  · exact B407355
  · exact B407359
  · exact B407363
  · exact B407367
  · exact B407371
  · exact B407375
  · exact B407379
  · exact B407383
  · exact B407387
  · exact B407391
  · exact B407395
  · exact B407399
  · exact B407403
  · exact B407407
  · exact B407411
  · exact B407415
  · exact B407419
  · exact B407423
  · exact B407427
  · exact B407431
  · exact B407435
  · exact B407439
  · exact B407443
  · exact B407447
  · exact B407451
  · exact B407455
  · exact B407459
  · exact B407463
  · exact B407467
  · exact B407471
  · exact B407475
  · exact B407479
  · exact B407483
  · exact B407487
  · exact B407491
  · exact B407495
  · exact B407499
  · exact B407503
  · exact B407507
  · exact B407511
  · exact B407515
  · exact B407519
  · exact B407523
  · exact B407527
  · exact B407531
  · exact B407535
  · exact B407539
  · exact B407543
  · exact B407547
  · exact B407551
  · exact B407555
  · exact B407559
  · exact B407563
  · exact B407567
  · exact B407571
  · exact B407575
  · exact B407579
  · exact B407583
  · exact B407587
  · exact B407591
  · exact B407595
  · exact B407599
  · exact B407603
  · exact B407607
  · exact B407611
  · exact B407615
  · exact B407619
  · exact B407623
  · exact B407627
  · exact B407631
  · exact B407635
  · exact B407639
  · exact B407643
  · exact B407647
  · exact B407651
  · exact B407655
  · exact B407659
  · exact B407663
  · exact B407667
  · exact B407671
  · exact B407675
  · exact B407679
  · exact B407683
  · exact B407687
  · exact B407691
  · exact B407695
  · exact B407699
  · exact B407703
  · exact B407707
  · exact B407711
  · exact B407715
  · exact B407719
  · exact B407723
  · exact B407727
  · exact B407731
  · exact B407735
  · exact B407739
  · exact B407743
  · exact B407747
  · exact B407751
  · exact B407755
  · exact B407759
  · exact B407763
  · exact B407767
  · exact B407771
  · exact B407775
  · exact B407779
  · exact B407783
  · exact B407787
  · exact B407791
  · exact B407795
  · exact B407799
  · exact B407803
  · exact B407807
  · exact B407811
  · exact B407815
  · exact B407819
  · exact B407823
  · exact B407827
  · exact B407831
  · exact B407835
  · exact B407839
  · exact B407843
  · exact B407847
  · exact B407851
  · exact B407855
  · exact B407859
  · exact B407863
  · exact B407867
  · exact B407871
  · exact B407875
  · exact B407879
  · exact B407883
  · exact B407887
  · exact B407891
  · exact B407895
  · exact B407899
  · exact B407903
  · exact B407907
  · exact B407911
  · exact B407915
  · exact B407919
  · exact B407923
  · exact B407927
  · exact B407931
  · exact B407935
  · exact B407939
  · exact B407943
  · exact B407947
  · exact B407951
  · exact B407955
  · exact B407959
  · exact B407963
  · exact B407967
  · exact B407971
  · exact B407975
  · exact B407979
  · exact B407983
  · exact B407987
  · exact B407991
  · exact B407995
  · exact B407999
  · exact B408003
  · exact B408007
  · exact B408011
  · exact B408015
  · exact B408019
  · exact B408023
  · exact B408027
  · exact B408031
  · exact B408035
  · exact B408039
  · exact B408043
  · exact B408047
  · exact B408051
  · exact B408055
  · exact B408059
  · exact B408063
  · exact B408067
  · exact B408071
  · exact B408075
  · exact B408079
  · exact B408083
  · exact B408087
  · exact B408091
  · exact B408095
  · exact B408099
  · exact B408103
  · exact B408107
  · exact B408111
  · exact B408115
  · exact B408119
  · exact B408123
  · exact B408127
  · exact B408131
  · exact B408135
  · exact B408139
  · exact B408143
  · exact B408147
  · exact B408151
  · exact B408155
  · exact B408159
  · exact B408163
  · exact B408167
  · exact B408171
  · exact B408175
  · exact B408179
  · exact B408183
  · exact B408187
  · exact B408191
  · exact B408195
  · exact B408199
  · exact B408203
  · exact B408207
  · exact B408211
  · exact B408215
  · exact B408219
  · exact B408223
  · exact B408227
  · exact B408231
  · exact B408235
  · exact B408239
  · exact B408243
  · exact B408247
  · exact B408251
  · exact B408255
  · exact B408259
  · exact B408263
  · exact B408267
  · exact B408271
  · exact B408275
  · exact B408279
  · exact B408283
  · exact B408287
  · exact B408291
  · exact B408295
  · exact B408299
  · exact B408303
  · exact B408307
  · exact B408311
  · exact B408315
  · exact B408319
  · exact B408323
  · exact B408327
  · exact B408331
  · exact B408335
  · exact B408339
  · exact B408343
  · exact B408347
  · exact B408351
  · exact B408355
  · exact B408359
  · exact B408363
  · exact B408367
  · exact B408371
  · exact B408375
  · exact B408379
  · exact B408383
  · exact B408387
  · exact B408391
  · exact B408395
  · exact B408399
  · exact B408403
  · exact B408407
  · exact B408411
  · exact B408415
  · exact B408419
  · exact B408423
  · exact B408427
  · exact B408431
  · exact B408435
  · exact B408439
  · exact B408443
  · exact B408447
  · exact B408451
  · exact B408455
  · exact B408459
  · exact B408463
  · exact B408467
  · exact B408471
  · exact B408475
  · exact B408479
  · exact B408483
  · exact B408487
  · exact B408491
  · exact B408495
  · exact B408499
  · exact B408503
  · exact B408507
  · exact B408511
  · exact B408515
  · exact B408519
  · exact B408523
  · exact B408527
  · exact B408531
  · exact B408535
  · exact B408539
  · exact B408543
  · exact B408547
  · exact B408551
  · exact B408555
  · exact B408559
  · exact B408563
  · exact B408567

theorem C1 (j : ℕ) (h1 : 102142 ≤ j) (h2 : j ≤ 102441) : Blo 405769 (4 * j + 3) := by
  interval_cases j
  · exact B408571
  · exact B408575
  · exact B408579
  · exact B408583
  · exact B408587
  · exact B408591
  · exact B408595
  · exact B408599
  · exact B408603
  · exact B408607
  · exact B408611
  · exact B408615
  · exact B408619
  · exact B408623
  · exact B408627
  · exact B408631
  · exact B408635
  · exact B408639
  · exact B408643
  · exact B408647
  · exact B408651
  · exact B408655
  · exact B408659
  · exact B408663
  · exact B408667
  · exact B408671
  · exact B408675
  · exact B408679
  · exact B408683
  · exact B408687
  · exact B408691
  · exact B408695
  · exact B408699
  · exact B408703
  · exact B408707
  · exact B408711
  · exact B408715
  · exact B408719
  · exact B408723
  · exact B408727
  · exact B408731
  · exact B408735
  · exact B408739
  · exact B408743
  · exact B408747
  · exact B408751
  · exact B408755
  · exact B408759
  · exact B408763
  · exact B408767
  · exact B408771
  · exact B408775
  · exact B408779
  · exact B408783
  · exact B408787
  · exact B408791
  · exact B408795
  · exact B408799
  · exact B408803
  · exact B408807
  · exact B408811
  · exact B408815
  · exact B408819
  · exact B408823
  · exact B408827
  · exact B408831
  · exact B408835
  · exact B408839
  · exact B408843
  · exact B408847
  · exact B408851
  · exact B408855
  · exact B408859
  · exact B408863
  · exact B408867
  · exact B408871
  · exact B408875
  · exact B408879
  · exact B408883
  · exact B408887
  · exact B408891
  · exact B408895
  · exact B408899
  · exact B408903
  · exact B408907
  · exact B408911
  · exact B408915
  · exact B408919
  · exact B408923
  · exact B408927
  · exact B408931
  · exact B408935
  · exact B408939
  · exact B408943
  · exact B408947
  · exact B408951
  · exact B408955
  · exact B408959
  · exact B408963
  · exact B408967
  · exact B408971
  · exact B408975
  · exact B408979
  · exact B408983
  · exact B408987
  · exact B408991
  · exact B408995
  · exact B408999
  · exact B409003
  · exact B409007
  · exact B409011
  · exact B409015
  · exact B409019
  · exact B409023
  · exact B409027
  · exact B409031
  · exact B409035
  · exact B409039
  · exact B409043
  · exact B409047
  · exact B409051
  · exact B409055
  · exact B409059
  · exact B409063
  · exact B409067
  · exact B409071
  · exact B409075
  · exact B409079
  · exact B409083
  · exact B409087
  · exact B409091
  · exact B409095
  · exact B409099
  · exact B409103
  · exact B409107
  · exact B409111
  · exact B409115
  · exact B409119
  · exact B409123
  · exact B409127
  · exact B409131
  · exact B409135
  · exact B409139
  · exact B409143
  · exact B409147
  · exact B409151
  · exact B409155
  · exact B409159
  · exact B409163
  · exact B409167
  · exact B409171
  · exact B409175
  · exact B409179
  · exact B409183
  · exact B409187
  · exact B409191
  · exact B409195
  · exact B409199
  · exact B409203
  · exact B409207
  · exact B409211
  · exact B409215
  · exact B409219
  · exact B409223
  · exact B409227
  · exact B409231
  · exact B409235
  · exact B409239
  · exact B409243
  · exact B409247
  · exact B409251
  · exact B409255
  · exact B409259
  · exact B409263
  · exact B409267
  · exact B409271
  · exact B409275
  · exact B409279
  · exact B409283
  · exact B409287
  · exact B409291
  · exact B409295
  · exact B409299
  · exact B409303
  · exact B409307
  · exact B409311
  · exact B409315
  · exact B409319
  · exact B409323
  · exact B409327
  · exact B409331
  · exact B409335
  · exact B409339
  · exact B409343
  · exact B409347
  · exact B409351
  · exact B409355
  · exact B409359
  · exact B409363
  · exact B409367
  · exact B409371
  · exact B409375
  · exact B409379
  · exact B409383
  · exact B409387
  · exact B409391
  · exact B409395
  · exact B409399
  · exact B409403
  · exact B409407
  · exact B409411
  · exact B409415
  · exact B409419
  · exact B409423
  · exact B409427
  · exact B409431
  · exact B409435
  · exact B409439
  · exact B409443
  · exact B409447
  · exact B409451
  · exact B409455
  · exact B409459
  · exact B409463
  · exact B409467
  · exact B409471
  · exact B409475
  · exact B409479
  · exact B409483
  · exact B409487
  · exact B409491
  · exact B409495
  · exact B409499
  · exact B409503
  · exact B409507
  · exact B409511
  · exact B409515
  · exact B409519
  · exact B409523
  · exact B409527
  · exact B409531
  · exact B409535
  · exact B409539
  · exact B409543
  · exact B409547
  · exact B409551
  · exact B409555
  · exact B409559
  · exact B409563
  · exact B409567
  · exact B409571
  · exact B409575
  · exact B409579
  · exact B409583
  · exact B409587
  · exact B409591
  · exact B409595
  · exact B409599
  · exact B409603
  · exact B409607
  · exact B409611
  · exact B409615
  · exact B409619
  · exact B409623
  · exact B409627
  · exact B409631
  · exact B409635
  · exact B409639
  · exact B409643
  · exact B409647
  · exact B409651
  · exact B409655
  · exact B409659
  · exact B409663
  · exact B409667
  · exact B409671
  · exact B409675
  · exact B409679
  · exact B409683
  · exact B409687
  · exact B409691
  · exact B409695
  · exact B409699
  · exact B409703
  · exact B409707
  · exact B409711
  · exact B409715
  · exact B409719
  · exact B409723
  · exact B409727
  · exact B409731
  · exact B409735
  · exact B409739
  · exact B409743
  · exact B409747
  · exact B409751
  · exact B409755
  · exact B409759
  · exact B409763
  · exact B409767

theorem solution (m : ℕ) (hlo : 405769 ≤ m) (hhi : m ≤ 409769) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 101442 ≤ j := by omega
    have hj2 : j ≤ 102441 := by omega
    have hb : Blo 405769 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 102142 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
