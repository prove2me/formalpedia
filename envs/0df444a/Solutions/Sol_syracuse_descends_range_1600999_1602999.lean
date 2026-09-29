-- Prove2me | solution 1 for syracuse_descends_range_1600999_1602999
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:10:46.633722+00:00
-- url     : https://prove2.me/submissions/6e19c8fd-af3b-496c-a1e1-cbff1f60b14c

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


theorem B1826821 : Blo 1600999 1826821 := bbase (se 4 (by rfl) ⟨171264, by rfl⟩ : syracuseStep 1826821 = 342529) (by norm_num)
theorem B1802245 : Blo 1600999 1802245 := bbase (se 4 (by rfl) ⟨168960, by rfl⟩ : syracuseStep 1802245 = 337921) (by norm_num)
theorem B3604517 : Blo 1600999 3604517 := bbase (se 4 (by rfl) ⟨337923, by rfl⟩ : syracuseStep 3604517 = 675847) (by norm_num)
theorem B1802281 : Blo 1600999 1802281 := bbase (se 2 (by rfl) ⟨675855, by rfl⟩ : syracuseStep 1802281 = 1351711) (by norm_num)
theorem B4055093 : Blo 1600999 4055093 := bbase (se 5 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 4055093 = 380165) (by norm_num)
theorem B6840389 : Blo 1600999 6840389 := bbase (se 4 (by rfl) ⟨641286, by rfl⟩ : syracuseStep 6840389 = 1282573) (by norm_num)
theorem B1802317 : Blo 1600999 1802317 := bbase (se 3 (by rfl) ⟨337934, by rfl⟩ : syracuseStep 1802317 = 675869) (by norm_num)
theorem B3604589 : Blo 1600999 3604589 := bbase (se 3 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 3604589 = 1351721) (by norm_num)
theorem B2703469 : Blo 1600999 2703469 := bbase (se 3 (by rfl) ⟨506900, by rfl⟩ : syracuseStep 2703469 = 1013801) (by norm_num)
theorem B1802353 : Blo 1600999 1802353 := bbase (se 2 (by rfl) ⟨675882, by rfl⟩ : syracuseStep 1802353 = 1351765) (by norm_num)
theorem B1802389 : Blo 1600999 1802389 := bbase (se 6 (by rfl) ⟨42243, by rfl⟩ : syracuseStep 1802389 = 84487) (by norm_num)
theorem B3604661 : Blo 1600999 3604661 := bbase (se 5 (by rfl) ⟨168968, by rfl⟩ : syracuseStep 3604661 = 337937) (by norm_num)
theorem B1802425 : Blo 1600999 1802425 := bbase (se 2 (by rfl) ⟨675909, by rfl⟩ : syracuseStep 1802425 = 1351819) (by norm_num)
theorem B2703557 : Blo 1600999 2703557 := bbase (se 4 (by rfl) ⟨253458, by rfl⟩ : syracuseStep 2703557 = 506917) (by norm_num)
theorem B3039437 : Blo 1600999 3039437 := bbase (se 3 (by rfl) ⟨569894, by rfl⟩ : syracuseStep 3039437 = 1139789) (by norm_num)
theorem B6496469 : Blo 1600999 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B1802461 : Blo 1600999 1802461 := bbase (se 3 (by rfl) ⟨337961, by rfl⟩ : syracuseStep 1802461 = 675923) (by norm_num)
theorem B5406965 : Blo 1600999 5406965 := bbase (se 5 (by rfl) ⟨253451, by rfl⟩ : syracuseStep 5406965 = 506903) (by norm_num)
theorem B4055285 : Blo 1600999 4055285 := bbase (se 5 (by rfl) ⟨190091, by rfl⟩ : syracuseStep 4055285 = 380183) (by norm_num)
theorem B3604733 : Blo 1600999 3604733 := bbase (se 3 (by rfl) ⟨675887, by rfl⟩ : syracuseStep 3604733 = 1351775) (by norm_num)
theorem B1802497 : Blo 1600999 1802497 := bbase (se 2 (by rfl) ⟨675936, by rfl⟩ : syracuseStep 1802497 = 1351873) (by norm_num)
theorem B4112669 : Blo 1600999 4112669 := bbase (se 3 (by rfl) ⟨771125, by rfl⟩ : syracuseStep 4112669 = 1542251) (by norm_num)
theorem B1802533 : Blo 1600999 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B3604805 : Blo 1600999 3604805 := bbase (se 4 (by rfl) ⟨337950, by rfl⟩ : syracuseStep 3604805 = 675901) (by norm_num)
theorem B2703685 : Blo 1600999 2703685 := bbase (se 4 (by rfl) ⟨253470, by rfl⟩ : syracuseStep 2703685 = 506941) (by norm_num)
theorem B1802569 : Blo 1600999 1802569 := bbase (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) (by norm_num)
theorem B10551637 : Blo 1600999 10551637 := bbase (se 10 (by rfl) ⟨15456, by rfl⟩ : syracuseStep 10551637 = 30913) (by norm_num)
theorem B3039581 : Blo 1600999 3039581 := bbase (se 3 (by rfl) ⟨569921, by rfl⟩ : syracuseStep 3039581 = 1139843) (by norm_num)
theorem B1802605 : Blo 1600999 1802605 := bbase (se 3 (by rfl) ⟨337988, by rfl⟩ : syracuseStep 1802605 = 675977) (by norm_num)
theorem B15401333 : Blo 1600999 15401333 := bbase (se 5 (by rfl) ⟨721937, by rfl⟩ : syracuseStep 15401333 = 1443875) (by norm_num)
theorem B3604877 : Blo 1600999 3604877 := bbase (se 3 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 3604877 = 1351829) (by norm_num)
theorem B1802641 : Blo 1600999 1802641 := bbase (se 2 (by rfl) ⟨675990, by rfl⟩ : syracuseStep 1802641 = 1351981) (by norm_num)
theorem B2703773 : Blo 1600999 2703773 := bbase (se 3 (by rfl) ⟨506957, by rfl⟩ : syracuseStep 2703773 = 1013915) (by norm_num)
theorem B1802677 : Blo 1600999 1802677 := bbase (se 5 (by rfl) ⟨84500, by rfl⟩ : syracuseStep 1802677 = 169001) (by norm_num)
theorem B3604949 : Blo 1600999 3604949 := bbase (se 7 (by rfl) ⟨42245, by rfl⟩ : syracuseStep 3604949 = 84491) (by norm_num)
theorem B1802713 : Blo 1600999 1802713 := bbase (se 2 (by rfl) ⟨676017, by rfl⟩ : syracuseStep 1802713 = 1352035) (by norm_num)
theorem B14606837 : Blo 1600999 14606837 := bbase (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) (by norm_num)
theorem B1802749 : Blo 1600999 1802749 := bbase (se 3 (by rfl) ⟨338015, by rfl⟩ : syracuseStep 1802749 = 676031) (by norm_num)
theorem B3850757 : Blo 1600999 3850757 := bbase (se 4 (by rfl) ⟨361008, by rfl⟩ : syracuseStep 3850757 = 722017) (by norm_num)
theorem B3654173 : Blo 1600999 3654173 := bbase (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) (by norm_num)
theorem B3605021 : Blo 1600999 3605021 := bbase (se 3 (by rfl) ⟨675941, by rfl⟩ : syracuseStep 3605021 = 1351883) (by norm_num)
theorem B2703901 : Blo 1600999 2703901 := bbase (se 3 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 2703901 = 1013963) (by norm_num)
theorem B1802785 : Blo 1600999 1802785 := bbase (se 2 (by rfl) ⟨676044, by rfl⟩ : syracuseStep 1802785 = 1352089) (by norm_num)
theorem B1802821 : Blo 1600999 1802821 := bbase (se 4 (by rfl) ⟨169014, by rfl⟩ : syracuseStep 1802821 = 338029) (by norm_num)
theorem B1925705 : Blo 1600999 1925705 := bbase (se 2 (by rfl) ⟨722139, by rfl⟩ : syracuseStep 1925705 = 1444279) (by norm_num)
theorem B4055629 : Blo 1600999 4055629 := bbase (se 3 (by rfl) ⟨760430, by rfl⟩ : syracuseStep 4055629 = 1520861) (by norm_num)
theorem B3605093 : Blo 1600999 3605093 := bbase (se 4 (by rfl) ⟨337977, by rfl⟩ : syracuseStep 3605093 = 675955) (by norm_num)
theorem B1802857 : Blo 1600999 1802857 := bbase (se 2 (by rfl) ⟨676071, by rfl⟩ : syracuseStep 1802857 = 1352143) (by norm_num)
theorem B2703989 : Blo 1600999 2703989 := bbase (se 5 (by rfl) ⟨126749, by rfl⟩ : syracuseStep 2703989 = 253499) (by norm_num)
theorem B3039869 : Blo 1600999 3039869 := bbase (se 3 (by rfl) ⟨569975, by rfl⟩ : syracuseStep 3039869 = 1139951) (by norm_num)
theorem B1802893 : Blo 1600999 1802893 := bbase (se 3 (by rfl) ⟨338042, by rfl⟩ : syracuseStep 1802893 = 676085) (by norm_num)
theorem B5407397 : Blo 1600999 5407397 := bbase (se 4 (by rfl) ⟨506943, by rfl⟩ : syracuseStep 5407397 = 1013887) (by norm_num)
theorem B3605165 : Blo 1600999 3605165 := bbase (se 3 (by rfl) ⟨675968, by rfl⟩ : syracuseStep 3605165 = 1351937) (by norm_num)
theorem B1802929 : Blo 1600999 1802929 := bbase (se 2 (by rfl) ⟨676098, by rfl⟩ : syracuseStep 1802929 = 1352197) (by norm_num)
theorem B4055741 : Blo 1600999 4055741 := bbase (se 3 (by rfl) ⟨760451, by rfl⟩ : syracuseStep 4055741 = 1520903) (by norm_num)
theorem B3850949 : Blo 1600999 3850949 := bbase (se 4 (by rfl) ⟨361026, by rfl⟩ : syracuseStep 3850949 = 722053) (by norm_num)
theorem B1802965 : Blo 1600999 1802965 := bbase (se 7 (by rfl) ⟨21128, by rfl⟩ : syracuseStep 1802965 = 42257) (by norm_num)
theorem B3605237 : Blo 1600999 3605237 := bbase (se 5 (by rfl) ⟨168995, by rfl⟩ : syracuseStep 3605237 = 337991) (by norm_num)
theorem B2704117 : Blo 1600999 2704117 := bbase (se 5 (by rfl) ⟨126755, by rfl⟩ : syracuseStep 2704117 = 253511) (by norm_num)
theorem B1803001 : Blo 1600999 1803001 := bbase (se 2 (by rfl) ⟨676125, by rfl⟩ : syracuseStep 1803001 = 1352251) (by norm_num)
theorem B8110853 : Blo 1600999 8110853 := bbase (se 4 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 8110853 = 1520785) (by norm_num)
theorem B3040021 : Blo 1600999 3040021 := bbase (se 6 (by rfl) ⟨71250, by rfl⟩ : syracuseStep 3040021 = 142501) (by norm_num)
theorem B1803037 : Blo 1600999 1803037 := bbase (se 3 (by rfl) ⟨338069, by rfl⟩ : syracuseStep 1803037 = 676139) (by norm_num)
theorem B3605309 : Blo 1600999 3605309 := bbase (se 3 (by rfl) ⟨675995, by rfl⟩ : syracuseStep 3605309 = 1351991) (by norm_num)
theorem B1803073 : Blo 1600999 1803073 := bbase (se 2 (by rfl) ⟨676152, by rfl⟩ : syracuseStep 1803073 = 1352305) (by norm_num)
theorem B2704205 : Blo 1600999 2704205 := bbase (se 3 (by rfl) ⟨507038, by rfl⟩ : syracuseStep 2704205 = 1014077) (by norm_num)
theorem B3294029 : Blo 1600999 3294029 := bbase (se 3 (by rfl) ⟨617630, by rfl⟩ : syracuseStep 3294029 = 1235261) (by norm_num)
theorem B1803109 : Blo 1600999 1803109 := bbase (se 4 (by rfl) ⟨169041, by rfl⟩ : syracuseStep 1803109 = 338083) (by norm_num)
theorem B2311021 : Blo 1600999 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B4055933 : Blo 1600999 4055933 := bbase (se 3 (by rfl) ⟨760487, by rfl⟩ : syracuseStep 4055933 = 1520975) (by norm_num)
theorem B3605381 : Blo 1600999 3605381 := bbase (se 4 (by rfl) ⟨338004, by rfl⟩ : syracuseStep 3605381 = 676009) (by norm_num)
theorem B1803145 : Blo 1600999 1803145 := bbase (se 2 (by rfl) ⟨676179, by rfl⟩ : syracuseStep 1803145 = 1352359) (by norm_num)
theorem B12166037 : Blo 1600999 12166037 := bbase (se 6 (by rfl) ⟨285141, by rfl⟩ : syracuseStep 12166037 = 570283) (by norm_num)
theorem B1803181 : Blo 1600999 1803181 := bbase (se 3 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 1803181 = 676193) (by norm_num)
theorem B3605453 : Blo 1600999 3605453 := bbase (se 3 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 3605453 = 1352045) (by norm_num)
theorem B2704333 : Blo 1600999 2704333 := bbase (se 3 (by rfl) ⟨507062, by rfl⟩ : syracuseStep 2704333 = 1014125) (by norm_num)
theorem B1803217 : Blo 1600999 1803217 := bbase (se 2 (by rfl) ⟨676206, by rfl⟩ : syracuseStep 1803217 = 1352413) (by norm_num)
theorem B12329941 : Blo 1600999 12329941 := bbase (se 7 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 12329941 = 288983) (by norm_num)
theorem B1803253 : Blo 1600999 1803253 := bbase (se 5 (by rfl) ⟨84527, by rfl⟩ : syracuseStep 1803253 = 169055) (by norm_num)
theorem B3605525 : Blo 1600999 3605525 := bbase (se 6 (by rfl) ⟨84504, by rfl⟩ : syracuseStep 3605525 = 169009) (by norm_num)
theorem B1803289 : Blo 1600999 1803289 := bbase (se 2 (by rfl) ⟨676233, by rfl⟩ : syracuseStep 1803289 = 1352467) (by norm_num)
theorem B6841381 : Blo 1600999 6841381 := bbase (se 4 (by rfl) ⟨641379, by rfl⟩ : syracuseStep 6841381 = 1282759) (by norm_num)
theorem B2704421 : Blo 1600999 2704421 := bbase (se 4 (by rfl) ⟨253539, by rfl⟩ : syracuseStep 2704421 = 507079) (by norm_num)
theorem B1803325 : Blo 1600999 1803325 := bbase (se 3 (by rfl) ⟨338123, by rfl⟩ : syracuseStep 1803325 = 676247) (by norm_num)
theorem B3040325 : Blo 1600999 3040325 := bbase (se 4 (by rfl) ⟨285030, by rfl⟩ : syracuseStep 3040325 = 570061) (by norm_num)
theorem B5407829 : Blo 1600999 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B7701589 : Blo 1600999 7701589 := bbase (se 8 (by rfl) ⟨45126, by rfl⟩ : syracuseStep 7701589 = 90253) (by norm_num)
theorem B3605597 : Blo 1600999 3605597 := bbase (se 3 (by rfl) ⟨676049, by rfl⟩ : syracuseStep 3605597 = 1352099) (by norm_num)
theorem B1803361 : Blo 1600999 1803361 := bbase (se 2 (by rfl) ⟨676260, by rfl⟩ : syracuseStep 1803361 = 1352521) (by norm_num)
theorem B3605669 : Blo 1600999 3605669 := bbase (se 4 (by rfl) ⟨338031, by rfl⟩ : syracuseStep 3605669 = 676063) (by norm_num)
theorem B2704549 : Blo 1600999 2704549 := bbase (se 4 (by rfl) ⟨253551, by rfl⟩ : syracuseStep 2704549 = 507103) (by norm_num)
theorem B4564133 : Blo 1600999 4564133 := bbase (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) (by norm_num)
theorem B4056277 : Blo 1600999 4056277 := bbase (se 7 (by rfl) ⟨47534, by rfl⟩ : syracuseStep 4056277 = 95069) (by norm_num)
theorem B2401517 : Blo 1600999 2401517 := bbase (se 3 (by rfl) ⟨450284, by rfl⟩ : syracuseStep 2401517 = 900569) (by norm_num)
theorem B3605741 : Blo 1600999 3605741 := bbase (se 3 (by rfl) ⟨676076, by rfl⟩ : syracuseStep 3605741 = 1352153) (by norm_num)
theorem B9250037 : Blo 1600999 9250037 := bbase (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) (by norm_num)
theorem B2704637 : Blo 1600999 2704637 := bbase (se 3 (by rfl) ⟨507119, by rfl⟩ : syracuseStep 2704637 = 1014239) (by norm_num)
theorem B2401541 : Blo 1600999 2401541 := bbase (se 4 (by rfl) ⟨225144, by rfl⟩ : syracuseStep 2401541 = 450289) (by norm_num)
theorem B2401565 : Blo 1600999 2401565 := bbase (se 3 (by rfl) ⟨450293, by rfl⟩ : syracuseStep 2401565 = 900587) (by norm_num)
theorem B1951025 : Blo 1600999 1951025 := bbase (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) (by norm_num)
theorem B2401589 : Blo 1600999 2401589 := bbase (se 5 (by rfl) ⟨112574, by rfl⟩ : syracuseStep 2401589 = 225149) (by norm_num)
theorem B12158261 : Blo 1600999 12158261 := bbase (se 5 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 12158261 = 1139837) (by norm_num)
theorem B3605813 : Blo 1600999 3605813 := bbase (se 5 (by rfl) ⟨169022, by rfl⟩ : syracuseStep 3605813 = 338045) (by norm_num)
theorem B4056389 : Blo 1600999 4056389 := bbase (se 4 (by rfl) ⟨380286, by rfl⟩ : syracuseStep 4056389 = 760573) (by norm_num)
theorem B2401613 : Blo 1600999 2401613 := bbase (se 3 (by rfl) ⟨450302, by rfl⟩ : syracuseStep 2401613 = 900605) (by norm_num)
theorem B2401637 : Blo 1600999 2401637 := bbase (se 4 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 2401637 = 450307) (by norm_num)
theorem B2401661 : Blo 1600999 2401661 := bbase (se 3 (by rfl) ⟨450311, by rfl⟩ : syracuseStep 2401661 = 900623) (by norm_num)
theorem B3605885 : Blo 1600999 3605885 := bbase (se 3 (by rfl) ⟨676103, by rfl⟩ : syracuseStep 3605885 = 1352207) (by norm_num)
theorem B2704765 : Blo 1600999 2704765 := bbase (se 3 (by rfl) ⟨507143, by rfl⟩ : syracuseStep 2704765 = 1014287) (by norm_num)
theorem B2401685 : Blo 1600999 2401685 := bbase (se 6 (by rfl) ⟨56289, by rfl⟩ : syracuseStep 2401685 = 112579) (by norm_num)
theorem B2401709 : Blo 1600999 2401709 := bbase (se 3 (by rfl) ⟨450320, by rfl⟩ : syracuseStep 2401709 = 900641) (by norm_num)
theorem B2401733 : Blo 1600999 2401733 := bbase (se 4 (by rfl) ⟨225162, by rfl⟩ : syracuseStep 2401733 = 450325) (by norm_num)
theorem B3605957 : Blo 1600999 3605957 := bbase (se 4 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 3605957 = 676117) (by norm_num)
theorem B2885069 : Blo 1600999 2885069 := bbase (se 3 (by rfl) ⟨540950, by rfl⟩ : syracuseStep 2885069 = 1081901) (by norm_num)
theorem B11552213 : Blo 1600999 11552213 := bbase (se 7 (by rfl) ⟨135377, by rfl⟩ : syracuseStep 11552213 = 270755) (by norm_num)
theorem B2704853 : Blo 1600999 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B2401757 : Blo 1600999 2401757 := bbase (se 3 (by rfl) ⟨450329, by rfl⟩ : syracuseStep 2401757 = 900659) (by norm_num)
theorem B2401781 : Blo 1600999 2401781 := bbase (se 5 (by rfl) ⟨112583, by rfl⟩ : syracuseStep 2401781 = 225167) (by norm_num)
theorem B5408261 : Blo 1600999 5408261 := bbase (se 4 (by rfl) ⟨507024, by rfl⟩ : syracuseStep 5408261 = 1014049) (by norm_num)
theorem B4056581 : Blo 1600999 4056581 := bbase (se 4 (by rfl) ⟨380304, by rfl⟩ : syracuseStep 4056581 = 760609) (by norm_num)
theorem B2401805 : Blo 1600999 2401805 := bbase (se 3 (by rfl) ⟨450338, by rfl⟩ : syracuseStep 2401805 = 900677) (by norm_num)
theorem B3606029 : Blo 1600999 3606029 := bbase (se 3 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 3606029 = 1352261) (by norm_num)
theorem B6497813 : Blo 1600999 6497813 := bbase (se 6 (by rfl) ⟨152292, by rfl⟩ : syracuseStep 6497813 = 304585) (by norm_num)
theorem B2885149 : Blo 1600999 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B2401829 : Blo 1600999 2401829 := bbase (se 4 (by rfl) ⟨225171, by rfl⟩ : syracuseStep 2401829 = 450343) (by norm_num)
theorem B2565685 : Blo 1600999 2565685 := bbase (se 5 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 2565685 = 240533) (by norm_num)
theorem B2401853 : Blo 1600999 2401853 := bbase (se 3 (by rfl) ⟨450347, by rfl⟩ : syracuseStep 2401853 = 900695) (by norm_num)
theorem B2401877 : Blo 1600999 2401877 := bbase (se 8 (by rfl) ⟨14073, by rfl⟩ : syracuseStep 2401877 = 28147) (by norm_num)
theorem B3606101 : Blo 1600999 3606101 := bbase (se 8 (by rfl) ⟨21129, by rfl⟩ : syracuseStep 3606101 = 42259) (by norm_num)
theorem B2704981 : Blo 1600999 2704981 := bbase (se 8 (by rfl) ⟨15849, by rfl⟩ : syracuseStep 2704981 = 31699) (by norm_num)
theorem B2401901 : Blo 1600999 2401901 := bbase (se 3 (by rfl) ⟨450356, by rfl⟩ : syracuseStep 2401901 = 900713) (by norm_num)
theorem B2401925 : Blo 1600999 2401925 := bbase (se 4 (by rfl) ⟨225180, by rfl⟩ : syracuseStep 2401925 = 450361) (by norm_num)
theorem B5777029 : Blo 1600999 5777029 := bbase (se 4 (by rfl) ⟨541596, by rfl⟩ : syracuseStep 5777029 = 1083193) (by norm_num)
theorem B2401949 : Blo 1600999 2401949 := bbase (se 3 (by rfl) ⟨450365, by rfl⟩ : syracuseStep 2401949 = 900731) (by norm_num)
theorem B3606173 : Blo 1600999 3606173 := bbase (se 3 (by rfl) ⟨676157, by rfl⟩ : syracuseStep 3606173 = 1352315) (by norm_num)
theorem B2401973 : Blo 1600999 2401973 := bbase (se 5 (by rfl) ⟨112592, by rfl⟩ : syracuseStep 2401973 = 225185) (by norm_num)
theorem B2401997 : Blo 1600999 2401997 := bbase (se 3 (by rfl) ⟨450374, by rfl⟩ : syracuseStep 2401997 = 900749) (by norm_num)
theorem B2164429 : Blo 1600999 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B2402021 : Blo 1600999 2402021 := bbase (se 4 (by rfl) ⟨225189, by rfl⟩ : syracuseStep 2402021 = 450379) (by norm_num)
theorem B3606245 : Blo 1600999 3606245 := bbase (se 4 (by rfl) ⟨338085, by rfl⟩ : syracuseStep 3606245 = 676171) (by norm_num)
theorem B2402045 : Blo 1600999 2402045 := bbase (se 3 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 2402045 = 900767) (by norm_num)
theorem B2402069 : Blo 1600999 2402069 := bbase (se 6 (by rfl) ⟨56298, by rfl⟩ : syracuseStep 2402069 = 112597) (by norm_num)
theorem B2402093 : Blo 1600999 2402093 := bbase (se 3 (by rfl) ⟨450392, by rfl⟩ : syracuseStep 2402093 = 900785) (by norm_num)
theorem B3655469 : Blo 1600999 3655469 := bbase (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) (by norm_num)
theorem B3606317 : Blo 1600999 3606317 := bbase (se 3 (by rfl) ⟨676184, by rfl⟩ : syracuseStep 3606317 = 1352369) (by norm_num)
theorem B3041077 : Blo 1600999 3041077 := bbase (se 5 (by rfl) ⟨142550, by rfl⟩ : syracuseStep 3041077 = 285101) (by norm_num)
theorem B12994357 : Blo 1600999 12994357 := bbase (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) (by norm_num)
theorem B2402117 : Blo 1600999 2402117 := bbase (se 4 (by rfl) ⟨225198, by rfl⟩ : syracuseStep 2402117 = 450397) (by norm_num)
theorem B2402141 : Blo 1600999 2402141 := bbase (se 3 (by rfl) ⟨450401, by rfl⟩ : syracuseStep 2402141 = 900803) (by norm_num)
theorem B4056925 : Blo 1600999 4056925 := bbase (se 3 (by rfl) ⟨760673, by rfl⟩ : syracuseStep 4056925 = 1521347) (by norm_num)
theorem B2402165 : Blo 1600999 2402165 := bbase (se 5 (by rfl) ⟨112601, by rfl⟩ : syracuseStep 2402165 = 225203) (by norm_num)
theorem B3606389 : Blo 1600999 3606389 := bbase (se 5 (by rfl) ⟨169049, by rfl⟩ : syracuseStep 3606389 = 338099) (by norm_num)
theorem B2402189 : Blo 1600999 2402189 := bbase (se 3 (by rfl) ⟨450410, by rfl⟩ : syracuseStep 2402189 = 900821) (by norm_num)
theorem B2402213 : Blo 1600999 2402213 := bbase (se 4 (by rfl) ⟨225207, by rfl⟩ : syracuseStep 2402213 = 450415) (by norm_num)
theorem B5408693 : Blo 1600999 5408693 := bbase (se 5 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 5408693 = 507065) (by norm_num)
theorem B2402237 : Blo 1600999 2402237 := bbase (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) (by norm_num)
theorem B3606461 : Blo 1600999 3606461 := bbase (se 3 (by rfl) ⟨676211, by rfl⟩ : syracuseStep 3606461 = 1352423) (by norm_num)
theorem B6080453 : Blo 1600999 6080453 := bbase (se 4 (by rfl) ⟨570042, by rfl⟩ : syracuseStep 6080453 = 1140085) (by norm_num)
theorem B3041221 : Blo 1600999 3041221 := bbase (se 4 (by rfl) ⟨285114, by rfl⟩ : syracuseStep 3041221 = 570229) (by norm_num)
theorem B4057037 : Blo 1600999 4057037 := bbase (se 3 (by rfl) ⟨760694, by rfl⟩ : syracuseStep 4057037 = 1521389) (by norm_num)
theorem B2402261 : Blo 1600999 2402261 := bbase (se 7 (by rfl) ⟨28151, by rfl⟩ : syracuseStep 2402261 = 56303) (by norm_num)
theorem B2402285 : Blo 1600999 2402285 := bbase (se 3 (by rfl) ⟨450428, by rfl⟩ : syracuseStep 2402285 = 900857) (by norm_num)
theorem B2402309 : Blo 1600999 2402309 := bbase (se 4 (by rfl) ⟨225216, by rfl⟩ : syracuseStep 2402309 = 450433) (by norm_num)
theorem B3606533 : Blo 1600999 3606533 := bbase (se 4 (by rfl) ⟨338112, by rfl⟩ : syracuseStep 3606533 = 676225) (by norm_num)
theorem B8112149 : Blo 1600999 8112149 := bbase (se 6 (by rfl) ⟨190128, by rfl⟩ : syracuseStep 8112149 = 380257) (by norm_num)
theorem B2402333 : Blo 1600999 2402333 := bbase (se 3 (by rfl) ⟨450437, by rfl⟩ : syracuseStep 2402333 = 900875) (by norm_num)
theorem B2402357 : Blo 1600999 2402357 := bbase (se 5 (by rfl) ⟨112610, by rfl⟩ : syracuseStep 2402357 = 225221) (by norm_num)
theorem B2402381 : Blo 1600999 2402381 := bbase (se 3 (by rfl) ⟨450446, by rfl⟩ : syracuseStep 2402381 = 900893) (by norm_num)
theorem B1624141 : Blo 1600999 1624141 := bbase (se 3 (by rfl) ⟨304526, by rfl⟩ : syracuseStep 1624141 = 609053) (by norm_num)
theorem B3606605 : Blo 1600999 3606605 := bbase (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) (by norm_num)
theorem B23406677 : Blo 1600999 23406677 := bbase (se 8 (by rfl) ⟨137148, by rfl⟩ : syracuseStep 23406677 = 274297) (by norm_num)
theorem B2402405 : Blo 1600999 2402405 := bbase (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) (by norm_num)
theorem B3041381 : Blo 1600999 3041381 := bbase (se 4 (by rfl) ⟨285129, by rfl⟩ : syracuseStep 3041381 = 570259) (by norm_num)
theorem B9242741 : Blo 1600999 9242741 := bbase (se 5 (by rfl) ⟨433253, by rfl⟩ : syracuseStep 9242741 = 866507) (by norm_num)
theorem B2279549 : Blo 1600999 2279549 := bbase (se 3 (by rfl) ⟨427415, by rfl⟩ : syracuseStep 2279549 = 854831) (by norm_num)
theorem B2402429 : Blo 1600999 2402429 := bbase (se 3 (by rfl) ⟨450455, by rfl⟩ : syracuseStep 2402429 = 900911) (by norm_num)
theorem B4057229 : Blo 1600999 4057229 := bbase (se 3 (by rfl) ⟨760730, by rfl⟩ : syracuseStep 4057229 = 1521461) (by norm_num)
theorem B2435221 : Blo 1600999 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B2402453 : Blo 1600999 2402453 := bbase (se 6 (by rfl) ⟨56307, by rfl⟩ : syracuseStep 2402453 = 112615) (by norm_num)
theorem B3606677 : Blo 1600999 3606677 := bbase (se 6 (by rfl) ⟨84531, by rfl⟩ : syracuseStep 3606677 = 169063) (by norm_num)
theorem B2402477 : Blo 1600999 2402477 := bbase (se 3 (by rfl) ⟨450464, by rfl⟩ : syracuseStep 2402477 = 900929) (by norm_num)
theorem B2402501 : Blo 1600999 2402501 := bbase (se 4 (by rfl) ⟨225234, by rfl⟩ : syracuseStep 2402501 = 450469) (by norm_num)
theorem B2402525 : Blo 1600999 2402525 := bbase (se 3 (by rfl) ⟨450473, by rfl⟩ : syracuseStep 2402525 = 900947) (by norm_num)
theorem B3606749 : Blo 1600999 3606749 := bbase (se 3 (by rfl) ⟨676265, by rfl⟩ : syracuseStep 3606749 = 1352531) (by norm_num)
theorem B6080741 : Blo 1600999 6080741 := bbase (se 4 (by rfl) ⟨570069, by rfl⟩ : syracuseStep 6080741 = 1140139) (by norm_num)
theorem B2402549 : Blo 1600999 2402549 := bbase (se 5 (by rfl) ⟨112619, by rfl⟩ : syracuseStep 2402549 = 225239) (by norm_num)
theorem B3041525 : Blo 1600999 3041525 := bbase (se 5 (by rfl) ⟨142571, by rfl⟩ : syracuseStep 3041525 = 285143) (by norm_num)
theorem B4622597 : Blo 1600999 4622597 := bbase (se 4 (by rfl) ⟨433368, by rfl⟩ : syracuseStep 4622597 = 866737) (by norm_num)
theorem B2402573 : Blo 1600999 2402573 := bbase (se 3 (by rfl) ⟨450482, by rfl⟩ : syracuseStep 2402573 = 900965) (by norm_num)
theorem B13682965 : Blo 1600999 13682965 := bbase (se 6 (by rfl) ⟨320694, by rfl⟩ : syracuseStep 13682965 = 641389) (by norm_num)
theorem B2402597 : Blo 1600999 2402597 := bbase (se 4 (by rfl) ⟨225243, by rfl⟩ : syracuseStep 2402597 = 450487) (by norm_num)
theorem B2402621 : Blo 1600999 2402621 := bbase (se 3 (by rfl) ⟨450491, by rfl⟩ : syracuseStep 2402621 = 900983) (by norm_num)
theorem B4753733 : Blo 1600999 4753733 := bbase (se 4 (by rfl) ⟨445662, by rfl⟩ : syracuseStep 4753733 = 891325) (by norm_num)
theorem B2402645 : Blo 1600999 2402645 := bbase (se 10 (by rfl) ⟨3519, by rfl⟩ : syracuseStep 2402645 = 7039) (by norm_num)
theorem B5409125 : Blo 1600999 5409125 := bbase (se 4 (by rfl) ⟨507105, by rfl⟩ : syracuseStep 5409125 = 1014211) (by norm_num)
theorem B2402669 : Blo 1600999 2402669 := bbase (se 3 (by rfl) ⟨450500, by rfl⟩ : syracuseStep 2402669 = 901001) (by norm_num)
theorem B2402693 : Blo 1600999 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B1624457 : Blo 1600999 1624457 := bbase (se 2 (by rfl) ⟨609171, by rfl⟩ : syracuseStep 1624457 = 1218343) (by norm_num)
theorem B2402717 : Blo 1600999 2402717 := bbase (se 3 (by rfl) ⟨450509, by rfl⟩ : syracuseStep 2402717 = 901019) (by norm_num)
theorem B2402741 : Blo 1600999 2402741 := bbase (se 5 (by rfl) ⟨112628, by rfl⟩ : syracuseStep 2402741 = 225257) (by norm_num)
theorem B2402765 : Blo 1600999 2402765 := bbase (se 3 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 2402765 = 901037) (by norm_num)
theorem B2402789 : Blo 1600999 2402789 := bbase (se 4 (by rfl) ⟨225261, by rfl⟩ : syracuseStep 2402789 = 450523) (by norm_num)
theorem B4057573 : Blo 1600999 4057573 := bbase (se 4 (by rfl) ⟨380397, by rfl⟩ : syracuseStep 4057573 = 760795) (by norm_num)
theorem B2402813 : Blo 1600999 2402813 := bbase (se 3 (by rfl) ⟨450527, by rfl⟩ : syracuseStep 2402813 = 901055) (by norm_num)
theorem B2402837 : Blo 1600999 2402837 := bbase (se 6 (by rfl) ⟨56316, by rfl⟩ : syracuseStep 2402837 = 112633) (by norm_num)
theorem B3041813 : Blo 1600999 3041813 := bbase (se 6 (by rfl) ⟨71292, by rfl⟩ : syracuseStep 3041813 = 142585) (by norm_num)
theorem B2402861 : Blo 1600999 2402861 := bbase (se 3 (by rfl) ⟨450536, by rfl⟩ : syracuseStep 2402861 = 901073) (by norm_num)
theorem B5130805 : Blo 1600999 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B2402885 : Blo 1600999 2402885 := bbase (se 4 (by rfl) ⟨225270, by rfl⟩ : syracuseStep 2402885 = 450541) (by norm_num)
theorem B7309909 : Blo 1600999 7309909 := bbase (se 8 (by rfl) ⟨42831, by rfl⟩ : syracuseStep 7309909 = 85663) (by norm_num)
theorem B2402909 : Blo 1600999 2402909 := bbase (se 3 (by rfl) ⟨450545, by rfl⟩ : syracuseStep 2402909 = 901091) (by norm_num)
theorem B2402933 : Blo 1600999 2402933 := bbase (se 5 (by rfl) ⟨112637, by rfl⟩ : syracuseStep 2402933 = 225275) (by norm_num)
theorem B2402957 : Blo 1600999 2402957 := bbase (se 3 (by rfl) ⟨450554, by rfl⟩ : syracuseStep 2402957 = 901109) (by norm_num)
theorem B2402981 : Blo 1600999 2402981 := bbase (se 4 (by rfl) ⟨225279, by rfl⟩ : syracuseStep 2402981 = 450559) (by norm_num)
theorem B3041965 : Blo 1600999 3041965 := bbase (se 3 (by rfl) ⟨570368, by rfl⟩ : syracuseStep 3041965 = 1140737) (by norm_num)
theorem B2403005 : Blo 1600999 2403005 := bbase (se 3 (by rfl) ⟨450563, by rfl⟩ : syracuseStep 2403005 = 901127) (by norm_num)
theorem B2403029 : Blo 1600999 2403029 := bbase (se 7 (by rfl) ⟨28160, by rfl⟩ : syracuseStep 2403029 = 56321) (by norm_num)
theorem B2403053 : Blo 1600999 2403053 := bbase (se 3 (by rfl) ⟨450572, by rfl⟩ : syracuseStep 2403053 = 901145) (by norm_num)
theorem B2403077 : Blo 1600999 2403077 := bbase (se 4 (by rfl) ⟨225288, by rfl⟩ : syracuseStep 2403077 = 450577) (by norm_num)
theorem B5409557 : Blo 1600999 5409557 := bbase (se 6 (by rfl) ⟨126786, by rfl⟩ : syracuseStep 5409557 = 253573) (by norm_num)
theorem B2403101 : Blo 1600999 2403101 := bbase (se 3 (by rfl) ⟨450581, by rfl⟩ : syracuseStep 2403101 = 901163) (by norm_num)
theorem B2403125 : Blo 1600999 2403125 := bbase (se 5 (by rfl) ⟨112646, by rfl⟩ : syracuseStep 2403125 = 225293) (by norm_num)
theorem B2403149 : Blo 1600999 2403149 := bbase (se 3 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 2403149 = 901181) (by norm_num)
theorem B2403173 : Blo 1600999 2403173 := bbase (se 4 (by rfl) ⟨225297, by rfl⟩ : syracuseStep 2403173 = 450595) (by norm_num)
theorem B2403197 : Blo 1600999 2403197 := bbase (se 3 (by rfl) ⟨450599, by rfl⟩ : syracuseStep 2403197 = 901199) (by norm_num)
theorem B2886533 : Blo 1600999 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B2403221 : Blo 1600999 2403221 := bbase (se 6 (by rfl) ⟨56325, by rfl⟩ : syracuseStep 2403221 = 112651) (by norm_num)
theorem B2026397 : Blo 1600999 2026397 := bbase (se 3 (by rfl) ⟨379949, by rfl⟩ : syracuseStep 2026397 = 759899) (by norm_num)
theorem B2567069 : Blo 1600999 2567069 := bbase (se 3 (by rfl) ⟨481325, by rfl⟩ : syracuseStep 2567069 = 962651) (by norm_num)
theorem B7695269 : Blo 1600999 7695269 := bbase (se 4 (by rfl) ⟨721431, by rfl⟩ : syracuseStep 7695269 = 1442863) (by norm_num)
theorem B2403245 : Blo 1600999 2403245 := bbase (se 3 (by rfl) ⟨450608, by rfl⟩ : syracuseStep 2403245 = 901217) (by norm_num)
theorem B2403269 : Blo 1600999 2403269 := bbase (se 4 (by rfl) ⟨225306, by rfl⟩ : syracuseStep 2403269 = 450613) (by norm_num)
theorem B2026453 : Blo 1600999 2026453 := bbase (se 7 (by rfl) ⟨23747, by rfl⟩ : syracuseStep 2026453 = 47495) (by norm_num)
theorem B5483477 : Blo 1600999 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B2403293 : Blo 1600999 2403293 := bbase (se 3 (by rfl) ⟨450617, by rfl⟩ : syracuseStep 2403293 = 901235) (by norm_num)
theorem B3042269 : Blo 1600999 3042269 := bbase (se 3 (by rfl) ⟨570425, by rfl⟩ : syracuseStep 3042269 = 1140851) (by norm_num)
theorem B2403317 : Blo 1600999 2403317 := bbase (se 5 (by rfl) ⟨112655, by rfl⟩ : syracuseStep 2403317 = 225311) (by norm_num)
theorem B2403341 : Blo 1600999 2403341 := bbase (se 3 (by rfl) ⟨450626, by rfl⟩ : syracuseStep 2403341 = 901253) (by norm_num)
theorem B3124261 : Blo 1600999 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B2403365 : Blo 1600999 2403365 := bbase (se 4 (by rfl) ⟨225315, by rfl⟩ : syracuseStep 2403365 = 450631) (by norm_num)
theorem B2026549 : Blo 1600999 2026549 := bbase (se 5 (by rfl) ⟨94994, by rfl⟩ : syracuseStep 2026549 = 189989) (by norm_num)
theorem B2403389 : Blo 1600999 2403389 := bbase (se 3 (by rfl) ⟨450635, by rfl⟩ : syracuseStep 2403389 = 901271) (by norm_num)
theorem B2403413 : Blo 1600999 2403413 := bbase (se 8 (by rfl) ⟨14082, by rfl⟩ : syracuseStep 2403413 = 28165) (by norm_num)
theorem B2567261 : Blo 1600999 2567261 := bbase (se 3 (by rfl) ⟨481361, by rfl⟩ : syracuseStep 2567261 = 962723) (by norm_num)
theorem B2739301 : Blo 1600999 2739301 := bbase (se 4 (by rfl) ⟨256809, by rfl⟩ : syracuseStep 2739301 = 513619) (by norm_num)
theorem B2403437 : Blo 1600999 2403437 := bbase (se 3 (by rfl) ⟨450644, by rfl⟩ : syracuseStep 2403437 = 901289) (by norm_num)
theorem B3247229 : Blo 1600999 3247229 := bbase (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) (by norm_num)
theorem B2403461 : Blo 1600999 2403461 := bbase (se 4 (by rfl) ⟨225324, by rfl⟩ : syracuseStep 2403461 = 450649) (by norm_num)
theorem B2403485 : Blo 1600999 2403485 := bbase (se 3 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 2403485 = 901307) (by norm_num)
theorem B2403509 : Blo 1600999 2403509 := bbase (se 5 (by rfl) ⟨112664, by rfl⟩ : syracuseStep 2403509 = 225329) (by norm_num)
theorem B5409989 : Blo 1600999 5409989 := bbase (se 4 (by rfl) ⟨507186, by rfl⟩ : syracuseStep 5409989 = 1014373) (by norm_num)
theorem B2403533 : Blo 1600999 2403533 := bbase (se 3 (by rfl) ⟨450662, by rfl⟩ : syracuseStep 2403533 = 901325) (by norm_num)
theorem B18246869 : Blo 1600999 18246869 := bbase (se 7 (by rfl) ⟨213830, by rfl⟩ : syracuseStep 18246869 = 427661) (by norm_num)
theorem B2026721 : Blo 1600999 2026721 := bbase (se 2 (by rfl) ⟨760020, by rfl⟩ : syracuseStep 2026721 = 1520041) (by norm_num)
theorem B2403557 : Blo 1600999 2403557 := bbase (se 4 (by rfl) ⟨225333, by rfl⟩ : syracuseStep 2403557 = 450667) (by norm_num)
theorem B14806261 : Blo 1600999 14806261 := bbase (se 5 (by rfl) ⟨694043, by rfl⟩ : syracuseStep 14806261 = 1388087) (by norm_num)
theorem B2403581 : Blo 1600999 2403581 := bbase (se 3 (by rfl) ⟨450671, by rfl⟩ : syracuseStep 2403581 = 901343) (by norm_num)
theorem B2403605 : Blo 1600999 2403605 := bbase (se 6 (by rfl) ⟨56334, by rfl⟩ : syracuseStep 2403605 = 112669) (by norm_num)
theorem B2026777 : Blo 1600999 2026777 := bbase (se 2 (by rfl) ⟨760041, by rfl⟩ : syracuseStep 2026777 = 1520083) (by norm_num)
theorem B8113445 : Blo 1600999 8113445 := bbase (se 4 (by rfl) ⟨760635, by rfl⟩ : syracuseStep 8113445 = 1521271) (by norm_num)
theorem B2403629 : Blo 1600999 2403629 := bbase (se 3 (by rfl) ⟨450680, by rfl⟩ : syracuseStep 2403629 = 901361) (by norm_num)
theorem B2403653 : Blo 1600999 2403653 := bbase (se 4 (by rfl) ⟨225342, by rfl⟩ : syracuseStep 2403653 = 450685) (by norm_num)
theorem B2403677 : Blo 1600999 2403677 := bbase (se 3 (by rfl) ⟨450689, by rfl⟩ : syracuseStep 2403677 = 901379) (by norm_num)
theorem B2403701 : Blo 1600999 2403701 := bbase (se 5 (by rfl) ⟨112673, by rfl⟩ : syracuseStep 2403701 = 225347) (by norm_num)
theorem B2026873 : Blo 1600999 2026873 := bbase (se 2 (by rfl) ⟨760077, by rfl⟩ : syracuseStep 2026873 = 1520155) (by norm_num)
theorem B6081925 : Blo 1600999 6081925 := bbase (se 4 (by rfl) ⟨570180, by rfl⟩ : syracuseStep 6081925 = 1140361) (by norm_num)
theorem B2403725 : Blo 1600999 2403725 := bbase (se 3 (by rfl) ⟨450698, by rfl⟩ : syracuseStep 2403725 = 901397) (by norm_num)
theorem B2403749 : Blo 1600999 2403749 := bbase (se 4 (by rfl) ⟨225351, by rfl⟩ : syracuseStep 2403749 = 450703) (by norm_num)
theorem B2403773 : Blo 1600999 2403773 := bbase (se 3 (by rfl) ⟨450707, by rfl⟩ : syracuseStep 2403773 = 901415) (by norm_num)
theorem B3419597 : Blo 1600999 3419597 := bbase (se 3 (by rfl) ⟨641174, by rfl⟩ : syracuseStep 3419597 = 1282349) (by norm_num)
theorem B2403797 : Blo 1600999 2403797 := bbase (se 7 (by rfl) ⟨28169, by rfl⟩ : syracuseStep 2403797 = 56339) (by norm_num)
theorem B2436589 : Blo 1600999 2436589 := bbase (se 3 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 2436589 = 913721) (by norm_num)
theorem B2403821 : Blo 1600999 2403821 := bbase (se 3 (by rfl) ⟨450716, by rfl⟩ : syracuseStep 2403821 = 901433) (by norm_num)
theorem B2403845 : Blo 1600999 2403845 := bbase (se 4 (by rfl) ⟨225360, by rfl⟩ : syracuseStep 2403845 = 450721) (by norm_num)
theorem B2280973 : Blo 1600999 2280973 := bbase (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) (by norm_num)
theorem B2403869 : Blo 1600999 2403869 := bbase (se 3 (by rfl) ⟨450725, by rfl⟩ : syracuseStep 2403869 = 901451) (by norm_num)
theorem B2027045 : Blo 1600999 2027045 := bbase (se 4 (by rfl) ⟨190035, by rfl⟩ : syracuseStep 2027045 = 380071) (by norm_num)
theorem B2403893 : Blo 1600999 2403893 := bbase (se 5 (by rfl) ⟨112682, by rfl⟩ : syracuseStep 2403893 = 225365) (by norm_num)
theorem B2403917 : Blo 1600999 2403917 := bbase (se 3 (by rfl) ⟨450734, by rfl⟩ : syracuseStep 2403917 = 901469) (by norm_num)
theorem B58453589 : Blo 1600999 58453589 := bbase (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) (by norm_num)
theorem B2027101 : Blo 1600999 2027101 := bbase (se 3 (by rfl) ⟨380081, by rfl⟩ : syracuseStep 2027101 = 760163) (by norm_num)
theorem B2403941 : Blo 1600999 2403941 := bbase (se 4 (by rfl) ⟨225369, by rfl⟩ : syracuseStep 2403941 = 450739) (by norm_num)
theorem B2403965 : Blo 1600999 2403965 := bbase (se 3 (by rfl) ⟨450743, by rfl⟩ : syracuseStep 2403965 = 901487) (by norm_num)
theorem B2403989 : Blo 1600999 2403989 := bbase (se 6 (by rfl) ⟨56343, by rfl⟩ : syracuseStep 2403989 = 112687) (by norm_num)
theorem B2404013 : Blo 1600999 2404013 := bbase (se 3 (by rfl) ⟨450752, by rfl⟩ : syracuseStep 2404013 = 901505) (by norm_num)
theorem B6082229 : Blo 1600999 6082229 := bbase (se 5 (by rfl) ⟨285104, by rfl⟩ : syracuseStep 6082229 = 570209) (by norm_num)
theorem B2027197 : Blo 1600999 2027197 := bbase (se 3 (by rfl) ⟨380099, by rfl⟩ : syracuseStep 2027197 = 760199) (by norm_num)
theorem B8105669 : Blo 1600999 8105669 := bbase (se 4 (by rfl) ⟨759906, by rfl⟩ : syracuseStep 8105669 = 1519813) (by norm_num)
theorem B2404037 : Blo 1600999 2404037 := bbase (se 4 (by rfl) ⟨225378, by rfl⟩ : syracuseStep 2404037 = 450757) (by norm_num)
theorem B3043021 : Blo 1600999 3043021 := bbase (se 3 (by rfl) ⟨570566, by rfl⟩ : syracuseStep 3043021 = 1141133) (by norm_num)
theorem B8335061 : Blo 1600999 8335061 := bbase (se 7 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 8335061 = 195353) (by norm_num)
theorem B2404061 : Blo 1600999 2404061 := bbase (se 3 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 2404061 = 901523) (by norm_num)
theorem B2404085 : Blo 1600999 2404085 := bbase (se 5 (by rfl) ⟨112691, by rfl⟩ : syracuseStep 2404085 = 225383) (by norm_num)
theorem B3247877 : Blo 1600999 3247877 := bbase (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) (by norm_num)
theorem B2404109 : Blo 1600999 2404109 := bbase (se 3 (by rfl) ⟨450770, by rfl⟩ : syracuseStep 2404109 = 901541) (by norm_num)
theorem B20533013 : Blo 1600999 20533013 := bbase (se 6 (by rfl) ⟨481242, by rfl⟩ : syracuseStep 20533013 = 962485) (by norm_num)
theorem B2404133 : Blo 1600999 2404133 := bbase (se 4 (by rfl) ⟨225387, by rfl⟩ : syracuseStep 2404133 = 450775) (by norm_num)
theorem B2404157 : Blo 1600999 2404157 := bbase (se 3 (by rfl) ⟨450779, by rfl⟩ : syracuseStep 2404157 = 901559) (by norm_num)
theorem B2404181 : Blo 1600999 2404181 := bbase (se 9 (by rfl) ⟨7043, by rfl⟩ : syracuseStep 2404181 = 14087) (by norm_num)
theorem B3043165 : Blo 1600999 3043165 := bbase (se 3 (by rfl) ⟨570593, by rfl⟩ : syracuseStep 3043165 = 1141187) (by norm_num)
theorem B2027369 : Blo 1600999 2027369 := bbase (se 2 (by rfl) ⟨760263, by rfl⟩ : syracuseStep 2027369 = 1520527) (by norm_num)
theorem B2404205 : Blo 1600999 2404205 := bbase (se 3 (by rfl) ⟨450788, by rfl⟩ : syracuseStep 2404205 = 901577) (by norm_num)
theorem B2404229 : Blo 1600999 2404229 := bbase (se 4 (by rfl) ⟨225396, by rfl⟩ : syracuseStep 2404229 = 450793) (by norm_num)
theorem B2404253 : Blo 1600999 2404253 := bbase (se 3 (by rfl) ⟨450797, by rfl⟩ : syracuseStep 2404253 = 901595) (by norm_num)
theorem B2027425 : Blo 1600999 2027425 := bbase (se 2 (by rfl) ⟨760284, by rfl⟩ : syracuseStep 2027425 = 1520569) (by norm_num)
theorem B2404277 : Blo 1600999 2404277 := bbase (se 5 (by rfl) ⟨112700, by rfl⟩ : syracuseStep 2404277 = 225401) (by norm_num)
theorem B2404301 : Blo 1600999 2404301 := bbase (se 3 (by rfl) ⟨450806, by rfl⟩ : syracuseStep 2404301 = 901613) (by norm_num)
theorem B2404325 : Blo 1600999 2404325 := bbase (se 4 (by rfl) ⟨225405, by rfl⟩ : syracuseStep 2404325 = 450811) (by norm_num)
theorem B2404349 : Blo 1600999 2404349 := bbase (se 3 (by rfl) ⟨450815, by rfl⟩ : syracuseStep 2404349 = 901631) (by norm_num)
theorem B2027521 : Blo 1600999 2027521 := bbase (se 2 (by rfl) ⟨760320, by rfl⟩ : syracuseStep 2027521 = 1520641) (by norm_num)
theorem B2404373 : Blo 1600999 2404373 := bbase (se 6 (by rfl) ⟨56352, by rfl⟩ : syracuseStep 2404373 = 112705) (by norm_num)
theorem B2404397 : Blo 1600999 2404397 := bbase (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) (by norm_num)
theorem B2404421 : Blo 1600999 2404421 := bbase (se 4 (by rfl) ⟨225414, by rfl⟩ : syracuseStep 2404421 = 450829) (by norm_num)
theorem B2281565 : Blo 1600999 2281565 := bbase (se 3 (by rfl) ⟨427793, by rfl⟩ : syracuseStep 2281565 = 855587) (by norm_num)
theorem B2404445 : Blo 1600999 2404445 := bbase (se 3 (by rfl) ⟨450833, by rfl⟩ : syracuseStep 2404445 = 901667) (by norm_num)
theorem B1806445 : Blo 1600999 1806445 := bbase (se 3 (by rfl) ⟨338708, by rfl⟩ : syracuseStep 1806445 = 677417) (by norm_num)
theorem B2404469 : Blo 1600999 2404469 := bbase (se 5 (by rfl) ⟨112709, by rfl⟩ : syracuseStep 2404469 = 225419) (by norm_num)
theorem B4108421 : Blo 1600999 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B2404493 : Blo 1600999 2404493 := bbase (se 3 (by rfl) ⟨450842, by rfl⟩ : syracuseStep 2404493 = 901685) (by norm_num)
theorem B2027693 : Blo 1600999 2027693 := bbase (se 3 (by rfl) ⟨380192, by rfl⟩ : syracuseStep 2027693 = 760385) (by norm_num)
theorem B2281645 : Blo 1600999 2281645 := bbase (se 3 (by rfl) ⟨427808, by rfl⟩ : syracuseStep 2281645 = 855617) (by norm_num)
theorem B3338437 : Blo 1600999 3338437 := bbase (se 4 (by rfl) ⟨312978, by rfl⟩ : syracuseStep 3338437 = 625957) (by norm_num)
theorem B13684949 : Blo 1600999 13684949 := bbase (se 7 (by rfl) ⟨160370, by rfl⟩ : syracuseStep 13684949 = 320741) (by norm_num)
theorem B2027749 : Blo 1600999 2027749 := bbase (se 4 (by rfl) ⟨190101, by rfl⟩ : syracuseStep 2027749 = 380203) (by norm_num)
theorem B2281765 : Blo 1600999 2281765 := bbase (se 4 (by rfl) ⟨213915, by rfl⟩ : syracuseStep 2281765 = 427831) (by norm_num)
theorem B3420461 : Blo 1600999 3420461 := bbase (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) (by norm_num)
theorem B2027845 : Blo 1600999 2027845 := bbase (se 4 (by rfl) ⟨190110, by rfl⟩ : syracuseStep 2027845 = 380221) (by norm_num)
theorem B2281861 : Blo 1600999 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B3420605 : Blo 1600999 3420605 := bbase (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) (by norm_num)
theorem B2028017 : Blo 1600999 2028017 := bbase (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) (by norm_num)
theorem B4387349 : Blo 1600999 4387349 := bbase (se 6 (by rfl) ⟨102828, by rfl⟩ : syracuseStep 4387349 = 205657) (by norm_num)
theorem B2028073 : Blo 1600999 2028073 := bbase (se 2 (by rfl) ⟨760527, by rfl⟩ : syracuseStep 2028073 = 1521055) (by norm_num)
theorem B8114741 : Blo 1600999 8114741 := bbase (se 5 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 8114741 = 760757) (by norm_num)
theorem B4559429 : Blo 1600999 4559429 := bbase (se 4 (by rfl) ⟨427446, by rfl⟩ : syracuseStep 4559429 = 854893) (by norm_num)
theorem B13873781 : Blo 1600999 13873781 := bbase (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) (by norm_num)
theorem B2028169 : Blo 1600999 2028169 := bbase (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) (by norm_num)
theorem B16437941 : Blo 1600999 16437941 := bbase (se 5 (by rfl) ⟨770528, by rfl⟩ : syracuseStep 16437941 = 1541057) (by norm_num)
theorem B2028341 : Blo 1600999 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B3126125 : Blo 1600999 3126125 := bbase (se 3 (by rfl) ⟨586148, by rfl⟩ : syracuseStep 3126125 = 1172297) (by norm_num)
theorem B2028397 : Blo 1600999 2028397 := bbase (se 3 (by rfl) ⟨380324, by rfl⟩ : syracuseStep 2028397 = 760649) (by norm_num)
theorem B5403509 : Blo 1600999 5403509 := bbase (se 5 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 5403509 = 506579) (by norm_num)
theorem B2282357 : Blo 1600999 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B14062517 : Blo 1600999 14062517 := bbase (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) (by norm_num)
theorem B2028493 : Blo 1600999 2028493 := bbase (se 3 (by rfl) ⟨380342, by rfl⟩ : syracuseStep 2028493 = 760685) (by norm_num)
theorem B8106965 : Blo 1600999 8106965 := bbase (se 7 (by rfl) ⟨95003, by rfl⟩ : syracuseStep 8106965 = 190007) (by norm_num)
theorem B3847181 : Blo 1600999 3847181 := bbase (se 3 (by rfl) ⟨721346, by rfl⟩ : syracuseStep 3847181 = 1442693) (by norm_num)
theorem B2028665 : Blo 1600999 2028665 := bbase (se 2 (by rfl) ⟨760749, by rfl⟩ : syracuseStep 2028665 = 1521499) (by norm_num)
theorem B3421349 : Blo 1600999 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B2028721 : Blo 1600999 2028721 := bbase (se 2 (by rfl) ⟨760770, by rfl⟩ : syracuseStep 2028721 = 1521541) (by norm_num)
theorem B4560101 : Blo 1600999 4560101 := bbase (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) (by norm_num)
theorem B5403941 : Blo 1600999 5403941 := bbase (se 4 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 5403941 = 1013239) (by norm_num)
theorem B4330837 : Blo 1600999 4330837 := bbase (se 14 (by rfl) ⟨396, by rfl⟩ : syracuseStep 4330837 = 793) (by norm_num)
theorem B1734097 : Blo 1600999 1734097 := bbase (se 2 (by rfl) ⟨650286, by rfl⟩ : syracuseStep 1734097 = 1300573) (by norm_num)
theorem B8328677 : Blo 1600999 8328677 := bbase (se 4 (by rfl) ⟨780813, by rfl⟩ : syracuseStep 8328677 = 1561627) (by norm_num)
theorem B4871717 : Blo 1600999 4871717 := bbase (se 4 (by rfl) ⟨456723, by rfl⟩ : syracuseStep 4871717 = 913447) (by norm_num)
theorem B7698053 : Blo 1600999 7698053 := bbase (se 4 (by rfl) ⟨721692, by rfl⟩ : syracuseStep 7698053 = 1443385) (by norm_num)
theorem B4560533 : Blo 1600999 4560533 := bbase (se 6 (by rfl) ⟨106887, by rfl⟩ : syracuseStep 4560533 = 213775) (by norm_num)
theorem B4052693 : Blo 1600999 4052693 := bbase (se 7 (by rfl) ⟨47492, by rfl⟩ : syracuseStep 4052693 = 94985) (by norm_num)
theorem B5404373 : Blo 1600999 5404373 := bbase (se 7 (by rfl) ⟨63332, by rfl⟩ : syracuseStep 5404373 = 126665) (by norm_num)
theorem B17323733 : Blo 1600999 17323733 := bbase (se 7 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 17323733 = 406025) (by norm_num)
theorem B6084341 : Blo 1600999 6084341 := bbase (se 5 (by rfl) ⟨285203, by rfl⟩ : syracuseStep 6084341 = 570407) (by norm_num)
theorem B3381005 : Blo 1600999 3381005 := bbase (se 3 (by rfl) ⟨633938, by rfl⟩ : syracuseStep 3381005 = 1267877) (by norm_num)
theorem B8664853 : Blo 1600999 8664853 := bbase (se 6 (by rfl) ⟨203082, by rfl⟩ : syracuseStep 8664853 = 406165) (by norm_num)
theorem B3602285 : Blo 1600999 3602285 := bbase (se 3 (by rfl) ⟨675428, by rfl⟩ : syracuseStep 3602285 = 1350857) (by norm_num)
theorem B1709957 : Blo 1600999 1709957 := bbase (se 4 (by rfl) ⟨160308, by rfl⟩ : syracuseStep 1709957 = 320617) (by norm_num)
theorem B3422101 : Blo 1600999 3422101 := bbase (se 6 (by rfl) ⟨80205, by rfl⟩ : syracuseStep 3422101 = 160411) (by norm_num)
theorem B3602357 : Blo 1600999 3602357 := bbase (se 5 (by rfl) ⟨168860, by rfl⟩ : syracuseStep 3602357 = 337721) (by norm_num)
theorem B6846389 : Blo 1600999 6846389 := bbase (se 5 (by rfl) ⟨320924, by rfl⟩ : syracuseStep 6846389 = 641849) (by norm_num)
theorem B1710029 : Blo 1600999 1710029 := bbase (se 3 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 1710029 = 641261) (by norm_num)
theorem B3602429 : Blo 1600999 3602429 := bbase (se 3 (by rfl) ⟨675455, by rfl⟩ : syracuseStep 3602429 = 1350911) (by norm_num)
theorem B2193413 : Blo 1600999 2193413 := bbase (se 4 (by rfl) ⟨205632, by rfl⟩ : syracuseStep 2193413 = 411265) (by norm_num)
theorem B11548693 : Blo 1600999 11548693 := bbase (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) (by norm_num)
theorem B6084629 : Blo 1600999 6084629 := bbase (se 6 (by rfl) ⟨142608, by rfl⟩ : syracuseStep 6084629 = 285217) (by norm_num)
theorem B3422245 : Blo 1600999 3422245 := bbase (se 4 (by rfl) ⟨320835, by rfl⟩ : syracuseStep 3422245 = 641671) (by norm_num)
theorem B4053037 : Blo 1600999 4053037 := bbase (se 3 (by rfl) ⟨759944, by rfl⟩ : syracuseStep 4053037 = 1519889) (by norm_num)
theorem B3602501 : Blo 1600999 3602501 := bbase (se 4 (by rfl) ⟨337734, by rfl⟩ : syracuseStep 3602501 = 675469) (by norm_num)
theorem B49305685 : Blo 1600999 49305685 := bbase (se 8 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 49305685 = 577801) (by norm_num)
theorem B5404805 : Blo 1600999 5404805 := bbase (se 4 (by rfl) ⟨506700, by rfl⟩ : syracuseStep 5404805 = 1013401) (by norm_num)
theorem B1710217 : Blo 1600999 1710217 := bbase (se 2 (by rfl) ⟨641331, by rfl⟩ : syracuseStep 1710217 = 1282663) (by norm_num)
theorem B3602573 : Blo 1600999 3602573 := bbase (se 3 (by rfl) ⟨675482, by rfl⟩ : syracuseStep 3602573 = 1350965) (by norm_num)
theorem B4053149 : Blo 1600999 4053149 := bbase (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) (by norm_num)
theorem B3602645 : Blo 1600999 3602645 := bbase (se 7 (by rfl) ⟨42218, by rfl⟩ : syracuseStep 3602645 = 84437) (by norm_num)
theorem B6846677 : Blo 1600999 6846677 := bbase (se 7 (by rfl) ⟨80234, by rfl⟩ : syracuseStep 6846677 = 160469) (by norm_num)
theorem B8108261 : Blo 1600999 8108261 := bbase (se 4 (by rfl) ⟨760149, by rfl⟩ : syracuseStep 8108261 = 1520299) (by norm_num)
theorem B7305461 : Blo 1600999 7305461 := bbase (se 5 (by rfl) ⟨342443, by rfl⟩ : syracuseStep 7305461 = 684887) (by norm_num)
theorem B3602717 : Blo 1600999 3602717 := bbase (se 3 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 3602717 = 1351019) (by norm_num)
theorem B1710401 : Blo 1600999 1710401 := bbase (se 2 (by rfl) ⟨641400, by rfl⟩ : syracuseStep 1710401 = 1282801) (by norm_num)
theorem B140433749 : Blo 1600999 140433749 := bbase (se 10 (by rfl) ⟨205713, by rfl⟩ : syracuseStep 140433749 = 411427) (by norm_num)
theorem B4053341 : Blo 1600999 4053341 := bbase (se 3 (by rfl) ⟨760001, by rfl⟩ : syracuseStep 4053341 = 1520003) (by norm_num)
theorem B3602789 : Blo 1600999 3602789 := bbase (se 4 (by rfl) ⟨337761, by rfl⟩ : syracuseStep 3602789 = 675523) (by norm_num)
theorem B1923437 : Blo 1600999 1923437 := bbase (se 3 (by rfl) ⟨360644, by rfl⟩ : syracuseStep 1923437 = 721289) (by norm_num)
theorem B4561285 : Blo 1600999 4561285 := bbase (se 4 (by rfl) ⟨427620, by rfl⟩ : syracuseStep 4561285 = 855241) (by norm_num)
theorem B3422621 : Blo 1600999 3422621 := bbase (se 3 (by rfl) ⟨641741, by rfl⟩ : syracuseStep 3422621 = 1283483) (by norm_num)
theorem B2701741 : Blo 1600999 2701741 := bbase (se 3 (by rfl) ⟨506576, by rfl⟩ : syracuseStep 2701741 = 1013153) (by norm_num)
theorem B3602861 : Blo 1600999 3602861 := bbase (se 3 (by rfl) ⟨675536, by rfl⟩ : syracuseStep 3602861 = 1351073) (by norm_num)
theorem B8444341 : Blo 1600999 8444341 := bbase (se 5 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 8444341 = 791657) (by norm_num)
theorem B3291589 : Blo 1600999 3291589 := bbase (se 4 (by rfl) ⟨308586, by rfl⟩ : syracuseStep 3291589 = 617173) (by norm_num)
theorem B3602933 : Blo 1600999 3602933 := bbase (se 5 (by rfl) ⟨168887, by rfl⟩ : syracuseStep 3602933 = 337775) (by norm_num)
theorem B2701829 : Blo 1600999 2701829 := bbase (se 4 (by rfl) ⟨253296, by rfl⟩ : syracuseStep 2701829 = 506593) (by norm_num)
theorem B1923601 : Blo 1600999 1923601 := bbase (se 2 (by rfl) ⟨721350, by rfl⟩ : syracuseStep 1923601 = 1442701) (by norm_num)
theorem B1923629 : Blo 1600999 1923629 := bbase (se 3 (by rfl) ⟨360680, by rfl⟩ : syracuseStep 1923629 = 721361) (by norm_num)
theorem B16661045 : Blo 1600999 16661045 := bbase (se 5 (by rfl) ⟨780986, by rfl⟩ : syracuseStep 16661045 = 1561973) (by norm_num)
theorem B5405237 : Blo 1600999 5405237 := bbase (se 5 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 5405237 = 506741) (by norm_num)
theorem B3603005 : Blo 1600999 3603005 := bbase (se 3 (by rfl) ⟨675563, by rfl⟩ : syracuseStep 3603005 = 1351127) (by norm_num)
theorem B2701957 : Blo 1600999 2701957 := bbase (se 4 (by rfl) ⟨253308, by rfl⟩ : syracuseStep 2701957 = 506617) (by norm_num)
theorem B3603077 : Blo 1600999 3603077 := bbase (se 4 (by rfl) ⟨337788, by rfl⟩ : syracuseStep 3603077 = 675577) (by norm_num)
theorem B1923745 : Blo 1600999 1923745 := bbase (se 2 (by rfl) ⟨721404, by rfl⟩ : syracuseStep 1923745 = 1442809) (by norm_num)
theorem B4053685 : Blo 1600999 4053685 := bbase (se 5 (by rfl) ⟨190016, by rfl⟩ : syracuseStep 4053685 = 380033) (by norm_num)
theorem B3603149 : Blo 1600999 3603149 := bbase (se 3 (by rfl) ⟨675590, by rfl⟩ : syracuseStep 3603149 = 1351181) (by norm_num)
theorem B2702045 : Blo 1600999 2702045 := bbase (se 3 (by rfl) ⟨506633, by rfl⟩ : syracuseStep 2702045 = 1013267) (by norm_num)
theorem B1923841 : Blo 1600999 1923841 := bbase (se 2 (by rfl) ⟨721440, by rfl⟩ : syracuseStep 1923841 = 1442881) (by norm_num)
theorem B3422989 : Blo 1600999 3422989 := bbase (se 3 (by rfl) ⟨641810, by rfl⟩ : syracuseStep 3422989 = 1283621) (by norm_num)
theorem B3603221 : Blo 1600999 3603221 := bbase (se 6 (by rfl) ⟨84450, by rfl⟩ : syracuseStep 3603221 = 168901) (by norm_num)
theorem B4053797 : Blo 1600999 4053797 := bbase (se 4 (by rfl) ⟨380043, by rfl⟩ : syracuseStep 4053797 = 760087) (by norm_num)
theorem B2702173 : Blo 1600999 2702173 := bbase (se 3 (by rfl) ⟨506657, by rfl⟩ : syracuseStep 2702173 = 1013315) (by norm_num)
theorem B3603293 : Blo 1600999 3603293 := bbase (se 3 (by rfl) ⟨675617, by rfl⟩ : syracuseStep 3603293 = 1351235) (by norm_num)
theorem B9124757 : Blo 1600999 9124757 := bbase (se 6 (by rfl) ⟨213861, by rfl⟩ : syracuseStep 9124757 = 427723) (by norm_num)
theorem B4111253 : Blo 1600999 4111253 := bbase (se 6 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 4111253 = 192715) (by norm_num)
theorem B3603365 : Blo 1600999 3603365 := bbase (se 4 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 3603365 = 675631) (by norm_num)
theorem B1801129 : Blo 1600999 1801129 := bbase (se 2 (by rfl) ⟨675423, by rfl⟩ : syracuseStep 1801129 = 1350847) (by norm_num)
theorem B2702261 : Blo 1600999 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B1801165 : Blo 1600999 1801165 := bbase (se 3 (by rfl) ⟨337718, by rfl⟩ : syracuseStep 1801165 = 675437) (by norm_num)
theorem B10263509 : Blo 1600999 10263509 := bbase (se 7 (by rfl) ⟨120275, by rfl⟩ : syracuseStep 10263509 = 240551) (by norm_num)
theorem B4053989 : Blo 1600999 4053989 := bbase (se 4 (by rfl) ⟨380061, by rfl⟩ : syracuseStep 4053989 = 760123) (by norm_num)
theorem B5405669 : Blo 1600999 5405669 := bbase (se 4 (by rfl) ⟨506781, by rfl⟩ : syracuseStep 5405669 = 1013563) (by norm_num)
theorem B3603437 : Blo 1600999 3603437 := bbase (se 3 (by rfl) ⟨675644, by rfl⟩ : syracuseStep 3603437 = 1351289) (by norm_num)
theorem B1801201 : Blo 1600999 1801201 := bbase (se 2 (by rfl) ⟨675450, by rfl⟩ : syracuseStep 1801201 = 1350901) (by norm_num)
theorem B1801237 : Blo 1600999 1801237 := bbase (se 6 (by rfl) ⟨42216, by rfl⟩ : syracuseStep 1801237 = 84433) (by norm_num)
theorem B1711153 : Blo 1600999 1711153 := bbase (se 2 (by rfl) ⟨641682, by rfl⟩ : syracuseStep 1711153 = 1283365) (by norm_num)
theorem B2702389 : Blo 1600999 2702389 := bbase (se 5 (by rfl) ⟨126674, by rfl⟩ : syracuseStep 2702389 = 253349) (by norm_num)
theorem B3603509 : Blo 1600999 3603509 := bbase (se 5 (by rfl) ⟨168914, by rfl⟩ : syracuseStep 3603509 = 337829) (by norm_num)
theorem B1801273 : Blo 1600999 1801273 := bbase (se 2 (by rfl) ⟨675477, by rfl⟩ : syracuseStep 1801273 = 1350955) (by norm_num)
theorem B116939861 : Blo 1600999 116939861 := bbase (se 8 (by rfl) ⟨685194, by rfl⟩ : syracuseStep 116939861 = 1370389) (by norm_num)
theorem B1801309 : Blo 1600999 1801309 := bbase (se 3 (by rfl) ⟨337745, by rfl⟩ : syracuseStep 1801309 = 675491) (by norm_num)
theorem B1711225 : Blo 1600999 1711225 := bbase (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) (by norm_num)
theorem B3603581 : Blo 1600999 3603581 := bbase (se 3 (by rfl) ⟨675671, by rfl⟩ : syracuseStep 3603581 = 1351343) (by norm_num)
theorem B1801345 : Blo 1600999 1801345 := bbase (se 2 (by rfl) ⟨675504, by rfl⟩ : syracuseStep 1801345 = 1351009) (by norm_num)
theorem B2702477 : Blo 1600999 2702477 := bbase (se 3 (by rfl) ⟨506714, by rfl⟩ : syracuseStep 2702477 = 1013429) (by norm_num)
theorem B3849373 : Blo 1600999 3849373 := bbase (se 3 (by rfl) ⟨721757, by rfl⟩ : syracuseStep 3849373 = 1443515) (by norm_num)
theorem B1801381 : Blo 1600999 1801381 := bbase (se 4 (by rfl) ⟨168879, by rfl⟩ : syracuseStep 1801381 = 337759) (by norm_num)
theorem B5479589 : Blo 1600999 5479589 := bbase (se 4 (by rfl) ⟨513711, by rfl⟩ : syracuseStep 5479589 = 1027423) (by norm_num)
theorem B6085813 : Blo 1600999 6085813 := bbase (se 5 (by rfl) ⟨285272, by rfl⟩ : syracuseStep 6085813 = 570545) (by norm_num)
theorem B3603653 : Blo 1600999 3603653 := bbase (se 4 (by rfl) ⟨337842, by rfl⟩ : syracuseStep 3603653 = 675685) (by norm_num)
theorem B1801417 : Blo 1600999 1801417 := bbase (se 2 (by rfl) ⟨675531, by rfl⟩ : syracuseStep 1801417 = 1351063) (by norm_num)
theorem B1924321 : Blo 1600999 1924321 := bbase (se 2 (by rfl) ⟨721620, by rfl⟩ : syracuseStep 1924321 = 1443241) (by norm_num)
theorem B1801453 : Blo 1600999 1801453 := bbase (se 3 (by rfl) ⟨337772, by rfl⟩ : syracuseStep 1801453 = 675545) (by norm_num)
theorem B6495493 : Blo 1600999 6495493 := bbase (se 4 (by rfl) ⟨608952, by rfl⟩ : syracuseStep 6495493 = 1217905) (by norm_num)
theorem B2702605 : Blo 1600999 2702605 := bbase (se 3 (by rfl) ⟨506738, by rfl⟩ : syracuseStep 2702605 = 1013477) (by norm_num)
theorem B3603725 : Blo 1600999 3603725 := bbase (se 3 (by rfl) ⟨675698, by rfl⟩ : syracuseStep 3603725 = 1351397) (by norm_num)
theorem B1801489 : Blo 1600999 1801489 := bbase (se 2 (by rfl) ⟨675558, by rfl⟩ : syracuseStep 1801489 = 1351117) (by norm_num)
theorem B2055461 : Blo 1600999 2055461 := bbase (se 4 (by rfl) ⟨192699, by rfl⟩ : syracuseStep 2055461 = 385399) (by norm_num)
theorem B1711405 : Blo 1600999 1711405 := bbase (se 3 (by rfl) ⟨320888, by rfl⟩ : syracuseStep 1711405 = 641777) (by norm_num)
theorem B1801525 : Blo 1600999 1801525 := bbase (se 5 (by rfl) ⟨84446, by rfl⟩ : syracuseStep 1801525 = 168893) (by norm_num)
theorem B4054333 : Blo 1600999 4054333 := bbase (se 3 (by rfl) ⟨760187, by rfl⟩ : syracuseStep 4054333 = 1520375) (by norm_num)
theorem B6495557 : Blo 1600999 6495557 := bbase (se 4 (by rfl) ⟨608958, by rfl⟩ : syracuseStep 6495557 = 1217917) (by norm_num)
theorem B3603797 : Blo 1600999 3603797 := bbase (se 11 (by rfl) ⟨2639, by rfl⟩ : syracuseStep 3603797 = 5279) (by norm_num)
theorem B1801561 : Blo 1600999 1801561 := bbase (se 2 (by rfl) ⟨675585, by rfl⟩ : syracuseStep 1801561 = 1351171) (by norm_num)
theorem B2702693 : Blo 1600999 2702693 := bbase (se 4 (by rfl) ⟨253377, by rfl⟩ : syracuseStep 2702693 = 506755) (by norm_num)
theorem B1801597 : Blo 1600999 1801597 := bbase (se 3 (by rfl) ⟨337799, by rfl⟩ : syracuseStep 1801597 = 675599) (by norm_num)
theorem B5406101 : Blo 1600999 5406101 := bbase (se 6 (by rfl) ⟨126705, by rfl⟩ : syracuseStep 5406101 = 253411) (by norm_num)
theorem B3603869 : Blo 1600999 3603869 := bbase (se 3 (by rfl) ⟨675725, by rfl⟩ : syracuseStep 3603869 = 1351451) (by norm_num)
theorem B1801633 : Blo 1600999 1801633 := bbase (se 2 (by rfl) ⟨675612, by rfl⟩ : syracuseStep 1801633 = 1351225) (by norm_num)
theorem B4054445 : Blo 1600999 4054445 := bbase (se 3 (by rfl) ⟨760208, by rfl⟩ : syracuseStep 4054445 = 1520417) (by norm_num)
theorem B1801669 : Blo 1600999 1801669 := bbase (se 4 (by rfl) ⟨168906, by rfl⟩ : syracuseStep 1801669 = 337813) (by norm_num)
theorem B2702821 : Blo 1600999 2702821 := bbase (se 4 (by rfl) ⟨253389, by rfl⟩ : syracuseStep 2702821 = 506779) (by norm_num)
theorem B3603941 : Blo 1600999 3603941 := bbase (se 4 (by rfl) ⟨337869, by rfl⟩ : syracuseStep 3603941 = 675739) (by norm_num)
theorem B6086117 : Blo 1600999 6086117 := bbase (se 4 (by rfl) ⟨570573, by rfl⟩ : syracuseStep 6086117 = 1141147) (by norm_num)
theorem B1801705 : Blo 1600999 1801705 := bbase (se 2 (by rfl) ⟨675639, by rfl⟩ : syracuseStep 1801705 = 1351279) (by norm_num)
theorem B8109557 : Blo 1600999 8109557 := bbase (se 5 (by rfl) ⟨380135, by rfl⟩ : syracuseStep 8109557 = 760271) (by norm_num)
theorem B1801741 : Blo 1600999 1801741 := bbase (se 3 (by rfl) ⟨337826, by rfl⟩ : syracuseStep 1801741 = 675653) (by norm_num)
theorem B3604013 : Blo 1600999 3604013 := bbase (se 3 (by rfl) ⟨675752, by rfl⟩ : syracuseStep 3604013 = 1351505) (by norm_num)
theorem B1801777 : Blo 1600999 1801777 := bbase (se 2 (by rfl) ⟨675666, by rfl⟩ : syracuseStep 1801777 = 1351333) (by norm_num)
theorem B2702909 : Blo 1600999 2702909 := bbase (se 3 (by rfl) ⟨506795, by rfl⟩ : syracuseStep 2702909 = 1013591) (by norm_num)
theorem B1801813 : Blo 1600999 1801813 := bbase (se 8 (by rfl) ⟨10557, by rfl⟩ : syracuseStep 1801813 = 21115) (by norm_num)
theorem B20012629 : Blo 1600999 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B1826393 : Blo 1600999 1826393 := bbase (se 2 (by rfl) ⟨684897, by rfl⟩ : syracuseStep 1826393 = 1369795) (by norm_num)
theorem B4054637 : Blo 1600999 4054637 := bbase (se 3 (by rfl) ⟨760244, by rfl⟩ : syracuseStep 4054637 = 1520489) (by norm_num)
theorem B3604085 : Blo 1600999 3604085 := bbase (se 5 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 3604085 = 337883) (by norm_num)
theorem B1801849 : Blo 1600999 1801849 := bbase (se 2 (by rfl) ⟨675693, by rfl⟩ : syracuseStep 1801849 = 1351387) (by norm_num)
theorem B1801885 : Blo 1600999 1801885 := bbase (se 3 (by rfl) ⟨337853, by rfl⟩ : syracuseStep 1801885 = 675707) (by norm_num)
theorem B2703037 : Blo 1600999 2703037 := bbase (se 3 (by rfl) ⟨506819, by rfl⟩ : syracuseStep 2703037 = 1013639) (by norm_num)
theorem B3604157 : Blo 1600999 3604157 := bbase (se 3 (by rfl) ⟨675779, by rfl⟩ : syracuseStep 3604157 = 1351559) (by norm_num)
theorem B1801921 : Blo 1600999 1801921 := bbase (se 2 (by rfl) ⟨675720, by rfl⟩ : syracuseStep 1801921 = 1351441) (by norm_num)
theorem B1801957 : Blo 1600999 1801957 := bbase (se 4 (by rfl) ⟨168933, by rfl⟩ : syracuseStep 1801957 = 337867) (by norm_num)
theorem B3604229 : Blo 1600999 3604229 := bbase (se 4 (by rfl) ⟨337896, by rfl⟩ : syracuseStep 3604229 = 675793) (by norm_num)
theorem B1801993 : Blo 1600999 1801993 := bbase (se 2 (by rfl) ⟨675747, by rfl⟩ : syracuseStep 1801993 = 1351495) (by norm_num)
theorem B2703125 : Blo 1600999 2703125 := bbase (se 6 (by rfl) ⟨63354, by rfl⟩ : syracuseStep 2703125 = 126709) (by norm_num)
theorem B1802029 : Blo 1600999 1802029 := bbase (se 3 (by rfl) ⟨337880, by rfl⟩ : syracuseStep 1802029 = 675761) (by norm_num)
theorem B5406533 : Blo 1600999 5406533 := bbase (se 4 (by rfl) ⟨506862, by rfl⟩ : syracuseStep 5406533 = 1013725) (by norm_num)
theorem B4874053 : Blo 1600999 4874053 := bbase (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) (by norm_num)
theorem B3604301 : Blo 1600999 3604301 := bbase (se 3 (by rfl) ⟨675806, by rfl⟩ : syracuseStep 3604301 = 1351613) (by norm_num)
theorem B1802065 : Blo 1600999 1802065 := bbase (se 2 (by rfl) ⟨675774, by rfl⟩ : syracuseStep 1802065 = 1351549) (by norm_num)
theorem B1802101 : Blo 1600999 1802101 := bbase (se 5 (by rfl) ⟨84473, by rfl⟩ : syracuseStep 1802101 = 168947) (by norm_num)
theorem B2703253 : Blo 1600999 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B3604373 : Blo 1600999 3604373 := bbase (se 6 (by rfl) ⟨84477, by rfl⟩ : syracuseStep 3604373 = 168955) (by norm_num)
theorem B1802137 : Blo 1600999 1802137 := bbase (se 2 (by rfl) ⟨675801, by rfl⟩ : syracuseStep 1802137 = 1351603) (by norm_num)
theorem B1802173 : Blo 1600999 1802173 := bbase (se 3 (by rfl) ⟨337907, by rfl⟩ : syracuseStep 1802173 = 675815) (by norm_num)
theorem B4054981 : Blo 1600999 4054981 := bbase (se 4 (by rfl) ⟨380154, by rfl⟩ : syracuseStep 4054981 = 760309) (by norm_num)
theorem B3604445 : Blo 1600999 3604445 := bbase (se 3 (by rfl) ⟨675833, by rfl⟩ : syracuseStep 3604445 = 1351667) (by norm_num)
theorem B1802209 : Blo 1600999 1802209 := bbase (se 2 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 1802209 = 1351657) (by norm_num)
theorem B2703341 : Blo 1600999 2703341 := bbase (se 3 (by rfl) ⟨506876, by rfl⟩ : syracuseStep 2703341 = 1013753) (by norm_num)
theorem B2703361 : Blo 1600999 2703361 := bstep (se 2 (by rfl) ⟨1013760, by rfl⟩ : syracuseStep 2703361 = 2027521) B2027521
theorem B5849101 : Blo 1600999 5849101 := bstep (se 3 (by rfl) ⟨1096706, by rfl⟩ : syracuseStep 5849101 = 2193413) B2193413
theorem B2703395 : Blo 1600999 2703395 := bstep (se 1 (by rfl) ⟨2027546, by rfl⟩ : syracuseStep 2703395 = 4055093) B4055093
theorem B4562993 : Blo 1600999 4562993 := bstep (se 2 (by rfl) ⟨1711122, by rfl⟩ : syracuseStep 4562993 = 3422245) B3422245
theorem B65740913 : Blo 1600999 65740913 := bstep (se 2 (by rfl) ⟨24652842, by rfl⟩ : syracuseStep 65740913 = 49305685) B49305685
theorem B1802371 : Blo 1600999 1802371 := bstep (se 1 (by rfl) ⟨1351778, by rfl⟩ : syracuseStep 1802371 = 2703557) B2703557
theorem B3604625 : Blo 1600999 3604625 := bstep (se 2 (by rfl) ⟨1351734, by rfl⟩ : syracuseStep 3604625 = 2703469) B2703469
theorem B3604643 : Blo 1600999 3604643 := bstep (se 1 (by rfl) ⟨2703482, by rfl⟩ : syracuseStep 3604643 = 5406965) B5406965
theorem B2703523 : Blo 1600999 2703523 := bstep (se 1 (by rfl) ⟨2027642, by rfl⟩ : syracuseStep 2703523 = 4055285) B4055285
theorem B1802515 : Blo 1600999 1802515 := bstep (se 1 (by rfl) ⟨1351886, by rfl⟩ : syracuseStep 1802515 = 2703773) B2703773
theorem B2703665 : Blo 1600999 2703665 := bstep (se 2 (by rfl) ⟨1013874, by rfl⟩ : syracuseStep 2703665 = 2027749) B2027749
theorem B6078797 : Blo 1600999 6078797 := bstep (se 3 (by rfl) ⟨1139774, by rfl⟩ : syracuseStep 6078797 = 2279549) B2279549
theorem B2924899 : Blo 1600999 2924899 := bstep (se 1 (by rfl) ⟨2193674, by rfl⟩ : syracuseStep 2924899 = 4387349) B4387349
theorem B18243953 : Blo 1600999 18243953 := bstep (se 2 (by rfl) ⟨6841482, by rfl⟩ : syracuseStep 18243953 = 13682965) B13682965
theorem B3039619 : Blo 1600999 3039619 := bstep (se 1 (by rfl) ⟨2279714, by rfl⟩ : syracuseStep 3039619 = 4559429) B4559429
theorem B9249187 : Blo 1600999 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B1802659 : Blo 1600999 1802659 := bstep (se 1 (by rfl) ⟨1351994, by rfl⟩ : syracuseStep 1802659 = 2703989) B2703989
theorem B3604913 : Blo 1600999 3604913 := bstep (se 2 (by rfl) ⟨1351842, by rfl⟩ : syracuseStep 3604913 = 2703685) B2703685
theorem B2703793 : Blo 1600999 2703793 := bstep (se 2 (by rfl) ⟨1013922, by rfl⟩ : syracuseStep 2703793 = 2027845) B2027845
theorem B3604931 : Blo 1600999 3604931 := bstep (se 1 (by rfl) ⟨2703698, by rfl⟩ : syracuseStep 3604931 = 5407397) B5407397
theorem B38986181 : Blo 1600999 38986181 := bstep (se 4 (by rfl) ⟨3654954, by rfl⟩ : syracuseStep 38986181 = 7309909) B7309909
theorem B5407181 : Blo 1600999 5407181 := bstep (se 3 (by rfl) ⟨1013846, by rfl⟩ : syracuseStep 5407181 = 2027693) B2027693
theorem B2703827 : Blo 1600999 2703827 := bstep (se 1 (by rfl) ⟨2027870, by rfl⟩ : syracuseStep 2703827 = 4055741) B4055741
theorem B5407235 : Blo 1600999 5407235 := bstep (se 1 (by rfl) ⟨4055426, by rfl⟩ : syracuseStep 5407235 = 8110853) B8110853
theorem B1802803 : Blo 1600999 1802803 := bstep (se 1 (by rfl) ⟨1352102, by rfl⟩ : syracuseStep 1802803 = 2704205) B2704205
theorem B9634373 : Blo 1600999 9634373 := bstep (se 4 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 9634373 = 1806445) B1806445
theorem B2703955 : Blo 1600999 2703955 := bstep (se 1 (by rfl) ⟨2027966, by rfl⟩ : syracuseStep 2703955 = 4055933) B4055933
theorem B8110691 : Blo 1600999 8110691 := bstep (se 1 (by rfl) ⟨6083018, by rfl⟩ : syracuseStep 8110691 = 12166037) B12166037
theorem B9126533 : Blo 1600999 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B2564801 : Blo 1600999 2564801 := bstep (se 2 (by rfl) ⟨961800, by rfl⟩ : syracuseStep 2564801 = 1923601) B1923601
theorem B1802947 : Blo 1600999 1802947 := bstep (se 1 (by rfl) ⟨1352210, by rfl⟩ : syracuseStep 1802947 = 2704421) B2704421
theorem B3605201 : Blo 1600999 3605201 := bstep (se 2 (by rfl) ⟨1351950, by rfl⟩ : syracuseStep 3605201 = 2703901) B2703901
theorem B2704097 : Blo 1600999 2704097 := bstep (se 2 (by rfl) ⟨1014036, by rfl⟩ : syracuseStep 2704097 = 2028073) B2028073
theorem B3605219 : Blo 1600999 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B6841073 : Blo 1600999 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B5407505 : Blo 1600999 5407505 := bstep (se 2 (by rfl) ⟨2027814, by rfl⟩ : syracuseStep 5407505 = 4055629) B4055629
theorem B5202733 : Blo 1600999 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B3040067 : Blo 1600999 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B1803091 : Blo 1600999 1803091 := bstep (se 1 (by rfl) ⟨1352318, by rfl⟩ : syracuseStep 1803091 = 2704637) B2704637
theorem B2704225 : Blo 1600999 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B2564993 : Blo 1600999 2564993 := bstep (se 2 (by rfl) ⟨961872, by rfl⟩ : syracuseStep 2564993 = 1923745) B1923745
theorem B2704259 : Blo 1600999 2704259 := bstep (se 1 (by rfl) ⟨2028194, by rfl⟩ : syracuseStep 2704259 = 4056389) B4056389
theorem B4055953 : Blo 1600999 4055953 := bstep (se 2 (by rfl) ⟨1520982, by rfl⟩ : syracuseStep 4055953 = 3041965) B3041965
theorem B5129165 : Blo 1600999 5129165 := bstep (se 3 (by rfl) ⟨961718, by rfl⟩ : syracuseStep 5129165 = 1923437) B1923437
theorem B7701475 : Blo 1600999 7701475 := bstep (se 1 (by rfl) ⟨5776106, by rfl⟩ : syracuseStep 7701475 = 11552213) B11552213
theorem B1803235 : Blo 1600999 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B3605489 : Blo 1600999 3605489 := bstep (se 2 (by rfl) ⟨1352058, by rfl⟩ : syracuseStep 3605489 = 2704117) B2704117
theorem B2565121 : Blo 1600999 2565121 := bstep (se 2 (by rfl) ⟨961920, by rfl⟩ : syracuseStep 2565121 = 1923841) B1923841
theorem B3605507 : Blo 1600999 3605507 := bstep (se 1 (by rfl) ⟨2704130, by rfl⟩ : syracuseStep 3605507 = 5408261) B5408261
theorem B2704387 : Blo 1600999 2704387 := bstep (se 1 (by rfl) ⟨2028290, by rfl⟩ : syracuseStep 2704387 = 4056581) B4056581
theorem B4563985 : Blo 1600999 4563985 := bstep (se 2 (by rfl) ⟨1711494, by rfl⟩ : syracuseStep 4563985 = 3422989) B3422989
theorem B9126989 : Blo 1600999 9126989 := bstep (se 3 (by rfl) ⟨1711310, by rfl⟩ : syracuseStep 9126989 = 3422621) B3422621
theorem B3040355 : Blo 1600999 3040355 := bstep (se 1 (by rfl) ⟨2280266, by rfl⟩ : syracuseStep 3040355 = 4560533) B4560533
theorem B2704529 : Blo 1600999 2704529 := bstep (se 2 (by rfl) ⟨1014198, by rfl⟩ : syracuseStep 2704529 = 2028397) B2028397
theorem B4056227 : Blo 1600999 4056227 := bstep (se 1 (by rfl) ⟨3042170, by rfl⟩ : syracuseStep 4056227 = 6084341) B6084341
theorem B2254003 : Blo 1600999 2254003 := bstep (se 1 (by rfl) ⟨1690502, by rfl⟩ : syracuseStep 2254003 = 3381005) B3381005
theorem B7693517 : Blo 1600999 7693517 := bstep (se 3 (by rfl) ⟨1442534, by rfl⟩ : syracuseStep 7693517 = 2885069) B2885069
theorem B9118925 : Blo 1600999 9118925 := bstep (se 3 (by rfl) ⟨1709798, by rfl⟩ : syracuseStep 9118925 = 3419597) B3419597
theorem B2401505 : Blo 1600999 2401505 := bstep (se 2 (by rfl) ⟨900564, by rfl⟩ : syracuseStep 2401505 = 1801129) B1801129
theorem B2401523 : Blo 1600999 2401523 := bstep (se 1 (by rfl) ⟨1801142, by rfl⟩ : syracuseStep 2401523 = 3602285) B3602285
theorem B22209805 : Blo 1600999 22209805 := bstep (se 3 (by rfl) ⟨4164338, by rfl⟩ : syracuseStep 22209805 = 8328677) B8328677
theorem B2401553 : Blo 1600999 2401553 := bstep (se 2 (by rfl) ⟨900582, by rfl⟩ : syracuseStep 2401553 = 1801165) B1801165
theorem B3605777 : Blo 1600999 3605777 := bstep (se 2 (by rfl) ⟨1352166, by rfl⟩ : syracuseStep 3605777 = 2704333) B2704333
theorem B2704657 : Blo 1600999 2704657 := bstep (se 2 (by rfl) ⟨1014246, by rfl⟩ : syracuseStep 2704657 = 2028493) B2028493
theorem B2401571 : Blo 1600999 2401571 := bstep (se 1 (by rfl) ⟨1801178, by rfl⟩ : syracuseStep 2401571 = 3602357) B3602357
theorem B3605795 : Blo 1600999 3605795 := bstep (se 1 (by rfl) ⟨2704346, by rfl⟩ : syracuseStep 3605795 = 5408693) B5408693
theorem B4564259 : Blo 1600999 4564259 := bstep (se 1 (by rfl) ⟨3423194, by rfl⟩ : syracuseStep 4564259 = 6846389) B6846389
theorem B5408045 : Blo 1600999 5408045 := bstep (se 3 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 5408045 = 2028017) B2028017
theorem B2704691 : Blo 1600999 2704691 := bstep (se 1 (by rfl) ⟨2028518, by rfl⟩ : syracuseStep 2704691 = 4057037) B4057037
theorem B2401601 : Blo 1600999 2401601 := bstep (se 2 (by rfl) ⟨900600, by rfl⟩ : syracuseStep 2401601 = 1801201) B1801201
theorem B2401619 : Blo 1600999 2401619 := bstep (se 1 (by rfl) ⟨1801214, by rfl⟩ : syracuseStep 2401619 = 3602429) B3602429
theorem B5408099 : Blo 1600999 5408099 := bstep (se 1 (by rfl) ⟨4056074, by rfl⟩ : syracuseStep 5408099 = 8112149) B8112149
theorem B4056419 : Blo 1600999 4056419 := bstep (se 1 (by rfl) ⟨3042314, by rfl⟩ : syracuseStep 4056419 = 6084629) B6084629
theorem B2401649 : Blo 1600999 2401649 := bstep (se 2 (by rfl) ⟨900618, by rfl⟩ : syracuseStep 2401649 = 1801237) B1801237
theorem B2401667 : Blo 1600999 2401667 := bstep (se 1 (by rfl) ⟨1801250, by rfl⟩ : syracuseStep 2401667 = 3602501) B3602501
theorem B8111501 : Blo 1600999 8111501 := bstep (se 3 (by rfl) ⟨1520906, by rfl⟩ : syracuseStep 8111501 = 3041813) B3041813
theorem B2401697 : Blo 1600999 2401697 := bstep (se 2 (by rfl) ⟨900636, by rfl⟩ : syracuseStep 2401697 = 1801273) B1801273
theorem B6161827 : Blo 1600999 6161827 := bstep (se 1 (by rfl) ⟨4621370, by rfl⟩ : syracuseStep 6161827 = 9242741) B9242741
theorem B2401715 : Blo 1600999 2401715 := bstep (se 1 (by rfl) ⟨1801286, by rfl⟩ : syracuseStep 2401715 = 3602573) B3602573
theorem B2704819 : Blo 1600999 2704819 := bstep (se 1 (by rfl) ⟨2028614, by rfl⟩ : syracuseStep 2704819 = 4057229) B4057229
theorem B5129677 : Blo 1600999 5129677 := bstep (se 3 (by rfl) ⟨961814, by rfl⟩ : syracuseStep 5129677 = 1923629) B1923629
theorem B2401745 : Blo 1600999 2401745 := bstep (se 2 (by rfl) ⟨900654, by rfl⟩ : syracuseStep 2401745 = 1801309) B1801309
theorem B2401763 : Blo 1600999 2401763 := bstep (se 1 (by rfl) ⟨1801322, by rfl⟩ : syracuseStep 2401763 = 3602645) B3602645
theorem B4564451 : Blo 1600999 4564451 := bstep (se 1 (by rfl) ⟨3423338, by rfl⟩ : syracuseStep 4564451 = 6846677) B6846677
theorem B2401793 : Blo 1600999 2401793 := bstep (se 2 (by rfl) ⟨900672, by rfl⟩ : syracuseStep 2401793 = 1801345) B1801345
theorem B3081731 : Blo 1600999 3081731 := bstep (se 1 (by rfl) ⟨2311298, by rfl⟩ : syracuseStep 3081731 = 4622597) B4622597
theorem B2401811 : Blo 1600999 2401811 := bstep (se 1 (by rfl) ⟨1801358, by rfl⟩ : syracuseStep 2401811 = 3602717) B3602717
theorem B2401841 : Blo 1600999 2401841 := bstep (se 2 (by rfl) ⟨900690, by rfl⟩ : syracuseStep 2401841 = 1801381) B1801381
theorem B3606065 : Blo 1600999 3606065 := bstep (se 2 (by rfl) ⟨1352274, by rfl⟩ : syracuseStep 3606065 = 2704549) B2704549
theorem B2704961 : Blo 1600999 2704961 := bstep (se 2 (by rfl) ⟨1014360, by rfl⟩ : syracuseStep 2704961 = 2028721) B2028721
theorem B2401859 : Blo 1600999 2401859 := bstep (se 1 (by rfl) ⟨1801394, by rfl⟩ : syracuseStep 2401859 = 3602789) B3602789
theorem B3606083 : Blo 1600999 3606083 := bstep (se 1 (by rfl) ⟨2704562, by rfl⟩ : syracuseStep 3606083 = 5409125) B5409125
theorem B2401889 : Blo 1600999 2401889 := bstep (se 2 (by rfl) ⟨900708, by rfl⟩ : syracuseStep 2401889 = 1801417) B1801417
theorem B5408369 : Blo 1600999 5408369 := bstep (se 2 (by rfl) ⟨2028138, by rfl⟩ : syracuseStep 5408369 = 4056277) B4056277
theorem B2401907 : Blo 1600999 2401907 := bstep (se 1 (by rfl) ⟨1801430, by rfl⟩ : syracuseStep 2401907 = 3602861) B3602861
theorem B2565761 : Blo 1600999 2565761 := bstep (se 2 (by rfl) ⟨962160, by rfl⟩ : syracuseStep 2565761 = 1924321) B1924321
theorem B2401937 : Blo 1600999 2401937 := bstep (se 2 (by rfl) ⟨900726, by rfl⟩ : syracuseStep 2401937 = 1801453) B1801453
theorem B2401955 : Blo 1600999 2401955 := bstep (se 1 (by rfl) ⟨1801466, by rfl⟩ : syracuseStep 2401955 = 3602933) B3602933
theorem B8660657 : Blo 1600999 8660657 := bstep (se 2 (by rfl) ⟨3247746, by rfl⟩ : syracuseStep 8660657 = 6495493) B6495493
theorem B2401985 : Blo 1600999 2401985 := bstep (se 2 (by rfl) ⟨900744, by rfl⟩ : syracuseStep 2401985 = 1801489) B1801489
theorem B2402003 : Blo 1600999 2402003 := bstep (se 1 (by rfl) ⟨1801502, by rfl⟩ : syracuseStep 2402003 = 3603005) B3603005
theorem B2402033 : Blo 1600999 2402033 := bstep (se 2 (by rfl) ⟨900762, by rfl⟩ : syracuseStep 2402033 = 1801525) B1801525
theorem B2402051 : Blo 1600999 2402051 := bstep (se 1 (by rfl) ⟨1801538, by rfl⟩ : syracuseStep 2402051 = 3603077) B3603077
theorem B2402081 : Blo 1600999 2402081 := bstep (se 2 (by rfl) ⟨900780, by rfl⟩ : syracuseStep 2402081 = 1801561) B1801561
theorem B2402099 : Blo 1600999 2402099 := bstep (se 1 (by rfl) ⟨1801574, by rfl⟩ : syracuseStep 2402099 = 3603149) B3603149
theorem B2402129 : Blo 1600999 2402129 := bstep (se 2 (by rfl) ⟨900798, by rfl⟩ : syracuseStep 2402129 = 1801597) B1801597
theorem B3606353 : Blo 1600999 3606353 := bstep (se 2 (by rfl) ⟨1352382, by rfl⟩ : syracuseStep 3606353 = 2704765) B2704765
theorem B2402147 : Blo 1600999 2402147 := bstep (se 1 (by rfl) ⟨1801610, by rfl⟩ : syracuseStep 2402147 = 3603221) B3603221
theorem B3606371 : Blo 1600999 3606371 := bstep (se 1 (by rfl) ⟨2704778, by rfl⟩ : syracuseStep 3606371 = 5409557) B5409557
theorem B2402177 : Blo 1600999 2402177 := bstep (se 2 (by rfl) ⟨900816, by rfl⟩ : syracuseStep 2402177 = 1801633) B1801633
theorem B2402195 : Blo 1600999 2402195 := bstep (se 1 (by rfl) ⟨1801646, by rfl⟩ : syracuseStep 2402195 = 3603293) B3603293
theorem B2402225 : Blo 1600999 2402225 := bstep (se 2 (by rfl) ⟨900834, by rfl⟩ : syracuseStep 2402225 = 1801669) B1801669
theorem B2312129 : Blo 1600999 2312129 := bstep (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) B1734097
theorem B5130179 : Blo 1600999 5130179 := bstep (se 1 (by rfl) ⟨3847634, by rfl⟩ : syracuseStep 5130179 = 7695269) B7695269
theorem B2402243 : Blo 1600999 2402243 := bstep (se 1 (by rfl) ⟨1801682, by rfl⟩ : syracuseStep 2402243 = 3603365) B3603365
theorem B2402273 : Blo 1600999 2402273 := bstep (se 2 (by rfl) ⟨900852, by rfl⟩ : syracuseStep 2402273 = 1801705) B1801705
theorem B6842339 : Blo 1600999 6842339 := bstep (se 1 (by rfl) ⟨5131754, by rfl⟩ : syracuseStep 6842339 = 10263509) B10263509
theorem B3655651 : Blo 1600999 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B2402291 : Blo 1600999 2402291 := bstep (se 1 (by rfl) ⟨1801718, by rfl⟩ : syracuseStep 2402291 = 3603437) B3603437
theorem B8661005 : Blo 1600999 8661005 := bstep (se 3 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 8661005 = 3247877) B3247877
theorem B2402321 : Blo 1600999 2402321 := bstep (se 2 (by rfl) ⟨900870, by rfl⟩ : syracuseStep 2402321 = 1801741) B1801741
theorem B3041297 : Blo 1600999 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B2402339 : Blo 1600999 2402339 := bstep (se 1 (by rfl) ⟨1801754, by rfl⟩ : syracuseStep 2402339 = 3603509) B3603509
theorem B2402369 : Blo 1600999 2402369 := bstep (se 2 (by rfl) ⟨900888, by rfl⟩ : syracuseStep 2402369 = 1801777) B1801777
theorem B2402387 : Blo 1600999 2402387 := bstep (se 1 (by rfl) ⟨1801790, by rfl⟩ : syracuseStep 2402387 = 3603581) B3603581
theorem B2164819 : Blo 1600999 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B26683505 : Blo 1600999 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B2402417 : Blo 1600999 2402417 := bstep (se 2 (by rfl) ⟨900906, by rfl⟩ : syracuseStep 2402417 = 1801813) B1801813
theorem B3606641 : Blo 1600999 3606641 := bstep (se 2 (by rfl) ⟨1352490, by rfl⟩ : syracuseStep 3606641 = 2704981) B2704981
theorem B2402435 : Blo 1600999 2402435 := bstep (se 1 (by rfl) ⟨1801826, by rfl⟩ : syracuseStep 2402435 = 3603653) B3603653
theorem B3606659 : Blo 1600999 3606659 := bstep (se 1 (by rfl) ⟨2704994, by rfl⟩ : syracuseStep 3606659 = 5409989) B5409989
theorem B5408909 : Blo 1600999 5408909 := bstep (se 3 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 5408909 = 2028341) B2028341
theorem B2402465 : Blo 1600999 2402465 := bstep (se 2 (by rfl) ⟨900924, by rfl⟩ : syracuseStep 2402465 = 1801849) B1801849
theorem B7702705 : Blo 1600999 7702705 := bstep (se 2 (by rfl) ⟨2888514, by rfl⟩ : syracuseStep 7702705 = 5777029) B5777029
theorem B2402483 : Blo 1600999 2402483 := bstep (se 1 (by rfl) ⟨1801862, by rfl⟩ : syracuseStep 2402483 = 3603725) B3603725
theorem B5408963 : Blo 1600999 5408963 := bstep (se 1 (by rfl) ⟨4056722, by rfl⟩ : syracuseStep 5408963 = 8113445) B8113445
theorem B8784077 : Blo 1600999 8784077 := bstep (se 3 (by rfl) ⟨1647014, by rfl⟩ : syracuseStep 8784077 = 3294029) B3294029
theorem B2402513 : Blo 1600999 2402513 := bstep (se 2 (by rfl) ⟨900942, by rfl⟩ : syracuseStep 2402513 = 1801885) B1801885
theorem B2402531 : Blo 1600999 2402531 := bstep (se 1 (by rfl) ⟨1801898, by rfl⟩ : syracuseStep 2402531 = 3603797) B3603797
theorem B2402561 : Blo 1600999 2402561 := bstep (se 2 (by rfl) ⟨900960, by rfl⟩ : syracuseStep 2402561 = 1801921) B1801921
theorem B2885905 : Blo 1600999 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B4057361 : Blo 1600999 4057361 := bstep (se 2 (by rfl) ⟨1521510, by rfl⟩ : syracuseStep 4057361 = 3043021) B3043021
theorem B2402579 : Blo 1600999 2402579 := bstep (se 1 (by rfl) ⟨1801934, by rfl⟩ : syracuseStep 2402579 = 3603869) B3603869
theorem B2402609 : Blo 1600999 2402609 := bstep (se 2 (by rfl) ⟨900978, by rfl⟩ : syracuseStep 2402609 = 1801957) B1801957
theorem B2402627 : Blo 1600999 2402627 := bstep (se 1 (by rfl) ⟨1801970, by rfl⟩ : syracuseStep 2402627 = 3603941) B3603941
theorem B4057411 : Blo 1600999 4057411 := bstep (se 1 (by rfl) ⟨3043058, by rfl⟩ : syracuseStep 4057411 = 6086117) B6086117
theorem B2402657 : Blo 1600999 2402657 := bstep (se 2 (by rfl) ⟨900996, by rfl⟩ : syracuseStep 2402657 = 1801993) B1801993
theorem B11553137 : Blo 1600999 11553137 := bstep (se 2 (by rfl) ⟨4332426, by rfl⟩ : syracuseStep 11553137 = 8664853) B8664853
theorem B2402675 : Blo 1600999 2402675 := bstep (se 1 (by rfl) ⟨1802006, by rfl⟩ : syracuseStep 2402675 = 3604013) B3604013
theorem B2402705 : Blo 1600999 2402705 := bstep (se 2 (by rfl) ⟨901014, by rfl⟩ : syracuseStep 2402705 = 1802029) B1802029
theorem B2402723 : Blo 1600999 2402723 := bstep (se 1 (by rfl) ⟨1802042, by rfl⟩ : syracuseStep 2402723 = 3604085) B3604085
theorem B6498737 : Blo 1600999 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B2402753 : Blo 1600999 2402753 := bstep (se 2 (by rfl) ⟨901032, by rfl⟩ : syracuseStep 2402753 = 1802065) B1802065
theorem B5409233 : Blo 1600999 5409233 := bstep (se 2 (by rfl) ⟨2028462, by rfl⟩ : syracuseStep 5409233 = 4056925) B4056925
theorem B4057553 : Blo 1600999 4057553 := bstep (se 2 (by rfl) ⟨1521582, by rfl⟩ : syracuseStep 4057553 = 3043165) B3043165
theorem B2402771 : Blo 1600999 2402771 := bstep (se 1 (by rfl) ⟨1802078, by rfl⟩ : syracuseStep 2402771 = 3604157) B3604157
theorem B5556707 : Blo 1600999 5556707 := bstep (se 1 (by rfl) ⟨4167530, by rfl⟩ : syracuseStep 5556707 = 8335061) B8335061
theorem B2402801 : Blo 1600999 2402801 := bstep (se 2 (by rfl) ⟨901050, by rfl⟩ : syracuseStep 2402801 = 1802101) B1802101
theorem B2402819 : Blo 1600999 2402819 := bstep (se 1 (by rfl) ⟨1802114, by rfl⟩ : syracuseStep 2402819 = 3604229) B3604229
theorem B2402849 : Blo 1600999 2402849 := bstep (se 2 (by rfl) ⟨901068, by rfl⟩ : syracuseStep 2402849 = 1802137) B1802137
theorem B2402867 : Blo 1600999 2402867 := bstep (se 1 (by rfl) ⟨1802150, by rfl⟩ : syracuseStep 2402867 = 3604301) B3604301
theorem B2402897 : Blo 1600999 2402897 := bstep (se 2 (by rfl) ⟨901086, by rfl⟩ : syracuseStep 2402897 = 1802173) B1802173
theorem B2402915 : Blo 1600999 2402915 := bstep (se 1 (by rfl) ⟨1802186, by rfl⟩ : syracuseStep 2402915 = 3604373) B3604373
theorem B2402945 : Blo 1600999 2402945 := bstep (se 2 (by rfl) ⟨901104, by rfl⟩ : syracuseStep 2402945 = 1802209) B1802209
theorem B2402963 : Blo 1600999 2402963 := bstep (se 1 (by rfl) ⟨1802222, by rfl⟩ : syracuseStep 2402963 = 3604445) B3604445
theorem B2435761 : Blo 1600999 2435761 := bstep (se 2 (by rfl) ⟨913410, by rfl⟩ : syracuseStep 2435761 = 1826821) B1826821
theorem B2402993 : Blo 1600999 2402993 := bstep (se 2 (by rfl) ⟨901122, by rfl⟩ : syracuseStep 2402993 = 1802245) B1802245
theorem B2403011 : Blo 1600999 2403011 := bstep (se 1 (by rfl) ⟨1802258, by rfl⟩ : syracuseStep 2403011 = 3604517) B3604517
theorem B10259149 : Blo 1600999 10259149 := bstep (se 3 (by rfl) ⟨1923590, by rfl⟩ : syracuseStep 10259149 = 3847181) B3847181
theorem B2403041 : Blo 1600999 2403041 := bstep (se 2 (by rfl) ⟨901140, by rfl⟩ : syracuseStep 2403041 = 1802281) B1802281
theorem B2403059 : Blo 1600999 2403059 := bstep (se 1 (by rfl) ⟨1802294, by rfl⟩ : syracuseStep 2403059 = 3604589) B3604589
theorem B2738947 : Blo 1600999 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B2403089 : Blo 1600999 2403089 := bstep (se 2 (by rfl) ⟨901158, by rfl⟩ : syracuseStep 2403089 = 1802317) B1802317
theorem B2403107 : Blo 1600999 2403107 := bstep (se 1 (by rfl) ⟨1802330, by rfl⟩ : syracuseStep 2403107 = 3604661) B3604661
theorem B2026291 : Blo 1600999 2026291 := bstep (se 1 (by rfl) ⟨1519718, by rfl⟩ : syracuseStep 2026291 = 3039437) B3039437
theorem B2403137 : Blo 1600999 2403137 := bstep (se 2 (by rfl) ⟨901176, by rfl⟩ : syracuseStep 2403137 = 1802353) B1802353
theorem B2403155 : Blo 1600999 2403155 := bstep (se 1 (by rfl) ⟨1802366, by rfl⟩ : syracuseStep 2403155 = 3604733) B3604733
theorem B3246961 : Blo 1600999 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B2403185 : Blo 1600999 2403185 := bstep (se 2 (by rfl) ⟨901194, by rfl⟩ : syracuseStep 2403185 = 1802389) B1802389
theorem B2280307 : Blo 1600999 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B2403203 : Blo 1600999 2403203 := bstep (se 1 (by rfl) ⟨1802402, by rfl⟩ : syracuseStep 2403203 = 3604805) B3604805
theorem B3042193 : Blo 1600999 3042193 := bstep (se 2 (by rfl) ⟨1140822, by rfl⟩ : syracuseStep 3042193 = 2281645) B2281645
theorem B2026387 : Blo 1600999 2026387 := bstep (se 1 (by rfl) ⟨1519790, by rfl⟩ : syracuseStep 2026387 = 3039581) B3039581
theorem B2403233 : Blo 1600999 2403233 := bstep (se 2 (by rfl) ⟨901212, by rfl⟩ : syracuseStep 2403233 = 1802425) B1802425
theorem B10267555 : Blo 1600999 10267555 := bstep (se 1 (by rfl) ⟨7700666, by rfl⟩ : syracuseStep 10267555 = 15401333) B15401333
theorem B2403251 : Blo 1600999 2403251 := bstep (se 1 (by rfl) ⟨1802438, by rfl⟩ : syracuseStep 2403251 = 3604877) B3604877
theorem B2403281 : Blo 1600999 2403281 := bstep (se 2 (by rfl) ⟨901230, by rfl⟩ : syracuseStep 2403281 = 1802461) B1802461
theorem B2280403 : Blo 1600999 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B2403299 : Blo 1600999 2403299 := bstep (se 1 (by rfl) ⟨1802474, by rfl⟩ : syracuseStep 2403299 = 3604949) B3604949
theorem B5409773 : Blo 1600999 5409773 := bstep (se 3 (by rfl) ⟨1014332, by rfl⟩ : syracuseStep 5409773 = 2028665) B2028665
theorem B2403329 : Blo 1600999 2403329 := bstep (se 2 (by rfl) ⟨901248, by rfl⟩ : syracuseStep 2403329 = 1802497) B1802497
theorem B2567171 : Blo 1600999 2567171 := bstep (se 1 (by rfl) ⟨1925378, by rfl⟩ : syracuseStep 2567171 = 3850757) B3850757
theorem B2403347 : Blo 1600999 2403347 := bstep (se 1 (by rfl) ⟨1802510, by rfl⟩ : syracuseStep 2403347 = 3605021) B3605021
theorem B5409827 : Blo 1600999 5409827 := bstep (se 1 (by rfl) ⟨4057370, by rfl⟩ : syracuseStep 5409827 = 8114741) B8114741
theorem B2403377 : Blo 1600999 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B3042353 : Blo 1600999 3042353 := bstep (se 2 (by rfl) ⟨1140882, by rfl⟩ : syracuseStep 3042353 = 2281765) B2281765
theorem B21924917 : Blo 1600999 21924917 := bstep (se 5 (by rfl) ⟨1027730, by rfl⟩ : syracuseStep 21924917 = 2055461) B2055461
theorem B2403395 : Blo 1600999 2403395 := bstep (se 1 (by rfl) ⟨1802546, by rfl⟩ : syracuseStep 2403395 = 3605093) B3605093
theorem B8662085 : Blo 1600999 8662085 := bstep (se 4 (by rfl) ⟨812070, by rfl⟩ : syracuseStep 8662085 = 1624141) B1624141
theorem B2403425 : Blo 1600999 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B14068849 : Blo 1600999 14068849 := bstep (se 2 (by rfl) ⟨5275818, by rfl⟩ : syracuseStep 14068849 = 10551637) B10551637
theorem B2403443 : Blo 1600999 2403443 := bstep (se 1 (by rfl) ⟨1802582, by rfl⟩ : syracuseStep 2403443 = 3605165) B3605165
theorem B2567299 : Blo 1600999 2567299 := bstep (se 1 (by rfl) ⟨1925474, by rfl⟩ : syracuseStep 2567299 = 3850949) B3850949
theorem B2403473 : Blo 1600999 2403473 := bstep (se 2 (by rfl) ⟨901302, by rfl⟩ : syracuseStep 2403473 = 1802605) B1802605
theorem B2403491 : Blo 1600999 2403491 := bstep (se 1 (by rfl) ⟨1802618, by rfl⟩ : syracuseStep 2403491 = 3605237) B3605237
theorem B6081713 : Blo 1600999 6081713 := bstep (se 2 (by rfl) ⟨2280642, by rfl⟩ : syracuseStep 6081713 = 4561285) B4561285
theorem B2403521 : Blo 1600999 2403521 := bstep (se 2 (by rfl) ⟨901320, by rfl⟩ : syracuseStep 2403521 = 1802641) B1802641
theorem B14609605 : Blo 1600999 14609605 := bstep (se 4 (by rfl) ⟨1369650, by rfl⟩ : syracuseStep 14609605 = 2739301) B2739301
theorem B2403539 : Blo 1600999 2403539 := bstep (se 1 (by rfl) ⟨1802654, by rfl⟩ : syracuseStep 2403539 = 3605309) B3605309
theorem B11259121 : Blo 1600999 11259121 := bstep (se 2 (by rfl) ⟨4222170, by rfl⟩ : syracuseStep 11259121 = 8444341) B8444341
theorem B2403569 : Blo 1600999 2403569 := bstep (se 2 (by rfl) ⟨901338, by rfl⟩ : syracuseStep 2403569 = 1802677) B1802677
theorem B2403587 : Blo 1600999 2403587 := bstep (se 1 (by rfl) ⟨1802690, by rfl⟩ : syracuseStep 2403587 = 3605381) B3605381
theorem B2403617 : Blo 1600999 2403617 := bstep (se 2 (by rfl) ⟨901356, by rfl⟩ : syracuseStep 2403617 = 1802713) B1802713
theorem B9375011 : Blo 1600999 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B5410097 : Blo 1600999 5410097 := bstep (se 2 (by rfl) ⟨2028786, by rfl⟩ : syracuseStep 5410097 = 4057573) B4057573
theorem B2403635 : Blo 1600999 2403635 := bstep (se 1 (by rfl) ⟨1802726, by rfl⟩ : syracuseStep 2403635 = 3605453) B3605453
theorem B2403665 : Blo 1600999 2403665 := bstep (se 2 (by rfl) ⟨901374, by rfl⟩ : syracuseStep 2403665 = 1802749) B1802749
theorem B2403683 : Blo 1600999 2403683 := bstep (se 1 (by rfl) ⟨1802762, by rfl⟩ : syracuseStep 2403683 = 3605525) B3605525
theorem B2403713 : Blo 1600999 2403713 := bstep (se 2 (by rfl) ⟨901392, by rfl⟩ : syracuseStep 2403713 = 1802785) B1802785
theorem B2026883 : Blo 1600999 2026883 := bstep (se 1 (by rfl) ⟨1520162, by rfl⟩ : syracuseStep 2026883 = 3040325) B3040325
theorem B9121157 : Blo 1600999 9121157 := bstep (se 4 (by rfl) ⟨855108, by rfl⟩ : syracuseStep 9121157 = 1710217) B1710217
theorem B2403731 : Blo 1600999 2403731 := bstep (se 1 (by rfl) ⟨1802798, by rfl⟩ : syracuseStep 2403731 = 3605597) B3605597
theorem B2403761 : Blo 1600999 2403761 := bstep (se 2 (by rfl) ⟨901410, by rfl⟩ : syracuseStep 2403761 = 1802821) B1802821
theorem B2280899 : Blo 1600999 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B2403779 : Blo 1600999 2403779 := bstep (se 1 (by rfl) ⟨1802834, by rfl⟩ : syracuseStep 2403779 = 3605669) B3605669
theorem B3042755 : Blo 1600999 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B2403809 : Blo 1600999 2403809 := bstep (se 2 (by rfl) ⟨901428, by rfl⟩ : syracuseStep 2403809 = 1802857) B1802857
theorem B1601011 : Blo 1600999 1601011 := bstep (se 1 (by rfl) ⟨1200758, by rfl⟩ : syracuseStep 1601011 = 2401517) B2401517
theorem B2403827 : Blo 1600999 2403827 := bstep (se 1 (by rfl) ⟨1802870, by rfl⟩ : syracuseStep 2403827 = 3605741) B3605741
theorem B1601027 : Blo 1600999 1601027 := bstep (se 1 (by rfl) ⟨1200770, by rfl⟩ : syracuseStep 1601027 = 2401541) B2401541
theorem B17321485 : Blo 1600999 17321485 := bstep (se 3 (by rfl) ⟨3247778, by rfl⟩ : syracuseStep 17321485 = 6495557) B6495557
theorem B2403857 : Blo 1600999 2403857 := bstep (se 2 (by rfl) ⟨901446, by rfl⟩ : syracuseStep 2403857 = 1802893) B1802893
theorem B1601043 : Blo 1600999 1601043 := bstep (se 1 (by rfl) ⟨1200782, by rfl⟩ : syracuseStep 1601043 = 2401565) B2401565
theorem B1601059 : Blo 1600999 1601059 := bstep (se 1 (by rfl) ⟨1200794, by rfl⟩ : syracuseStep 1601059 = 2401589) B2401589
theorem B8105507 : Blo 1600999 8105507 := bstep (se 1 (by rfl) ⟨6079130, by rfl⟩ : syracuseStep 8105507 = 12158261) B12158261
theorem B2403875 : Blo 1600999 2403875 := bstep (se 1 (by rfl) ⟨1802906, by rfl⟩ : syracuseStep 2403875 = 3605813) B3605813
theorem B1601075 : Blo 1600999 1601075 := bstep (se 1 (by rfl) ⟨1200806, by rfl⟩ : syracuseStep 1601075 = 2401613) B2401613
theorem B2403905 : Blo 1600999 2403905 := bstep (se 2 (by rfl) ⟨901464, by rfl⟩ : syracuseStep 2403905 = 1802929) B1802929
theorem B1601091 : Blo 1600999 1601091 := bstep (se 1 (by rfl) ⟨1200818, by rfl⟩ : syracuseStep 1601091 = 2401637) B2401637
theorem B1601107 : Blo 1600999 1601107 := bstep (se 1 (by rfl) ⟨1200830, by rfl⟩ : syracuseStep 1601107 = 2401661) B2401661
theorem B2403923 : Blo 1600999 2403923 := bstep (se 1 (by rfl) ⟨1802942, by rfl⟩ : syracuseStep 2403923 = 3605885) B3605885
theorem B1601123 : Blo 1600999 1601123 := bstep (se 1 (by rfl) ⟨1200842, by rfl⟩ : syracuseStep 1601123 = 2401685) B2401685
theorem B2403953 : Blo 1600999 2403953 := bstep (se 2 (by rfl) ⟨901482, by rfl⟩ : syracuseStep 2403953 = 1802965) B1802965
theorem B1601139 : Blo 1600999 1601139 := bstep (se 1 (by rfl) ⟨1200854, by rfl⟩ : syracuseStep 1601139 = 2401709) B2401709
theorem B1601155 : Blo 1600999 1601155 := bstep (se 1 (by rfl) ⟨1200866, by rfl⟩ : syracuseStep 1601155 = 2401733) B2401733
theorem B2403971 : Blo 1600999 2403971 := bstep (se 1 (by rfl) ⟨1802978, by rfl⟩ : syracuseStep 2403971 = 3605957) B3605957
theorem B1601171 : Blo 1600999 1601171 := bstep (se 1 (by rfl) ⟨1200878, by rfl⟩ : syracuseStep 1601171 = 2401757) B2401757
theorem B2404001 : Blo 1600999 2404001 := bstep (se 2 (by rfl) ⟨901500, by rfl⟩ : syracuseStep 2404001 = 1803001) B1803001
theorem B1601187 : Blo 1600999 1601187 := bstep (se 1 (by rfl) ⟨1200890, by rfl⟩ : syracuseStep 1601187 = 2401781) B2401781
theorem B1601203 : Blo 1600999 1601203 := bstep (se 1 (by rfl) ⟨1200902, by rfl⟩ : syracuseStep 1601203 = 2401805) B2401805
theorem B2404019 : Blo 1600999 2404019 := bstep (se 1 (by rfl) ⟨1803014, by rfl⟩ : syracuseStep 2404019 = 3606029) B3606029
theorem B1601219 : Blo 1600999 1601219 := bstep (se 1 (by rfl) ⟨1200914, by rfl⟩ : syracuseStep 1601219 = 2401829) B2401829
theorem B3247811 : Blo 1600999 3247811 := bstep (se 1 (by rfl) ⟨2435858, by rfl⟩ : syracuseStep 3247811 = 4871717) B4871717
theorem B2404049 : Blo 1600999 2404049 := bstep (se 2 (by rfl) ⟨901518, by rfl⟩ : syracuseStep 2404049 = 1803037) B1803037
theorem B1601235 : Blo 1600999 1601235 := bstep (se 1 (by rfl) ⟨1200926, by rfl⟩ : syracuseStep 1601235 = 2401853) B2401853
theorem B1601251 : Blo 1600999 1601251 := bstep (se 1 (by rfl) ⟨1200938, by rfl⟩ : syracuseStep 1601251 = 2401877) B2401877
theorem B2404067 : Blo 1600999 2404067 := bstep (se 1 (by rfl) ⟨1803050, by rfl⟩ : syracuseStep 2404067 = 3606101) B3606101
theorem B1601267 : Blo 1600999 1601267 := bstep (se 1 (by rfl) ⟨1200950, by rfl⟩ : syracuseStep 1601267 = 2401901) B2401901
theorem B2404097 : Blo 1600999 2404097 := bstep (se 2 (by rfl) ⟨901536, by rfl⟩ : syracuseStep 2404097 = 1803073) B1803073
theorem B1601283 : Blo 1600999 1601283 := bstep (se 1 (by rfl) ⟨1200962, by rfl⟩ : syracuseStep 1601283 = 2401925) B2401925
theorem B5132035 : Blo 1600999 5132035 := bstep (se 1 (by rfl) ⟨3849026, by rfl⟩ : syracuseStep 5132035 = 7698053) B7698053
theorem B1601299 : Blo 1600999 1601299 := bstep (se 1 (by rfl) ⟨1200974, by rfl⟩ : syracuseStep 1601299 = 2401949) B2401949
theorem B2404115 : Blo 1600999 2404115 := bstep (se 1 (by rfl) ⟨1803086, by rfl⟩ : syracuseStep 2404115 = 3606173) B3606173
theorem B1601315 : Blo 1600999 1601315 := bstep (se 1 (by rfl) ⟨1200986, by rfl⟩ : syracuseStep 1601315 = 2401973) B2401973
theorem B2404145 : Blo 1600999 2404145 := bstep (se 2 (by rfl) ⟨901554, by rfl⟩ : syracuseStep 2404145 = 1803109) B1803109
theorem B1601331 : Blo 1600999 1601331 := bstep (se 1 (by rfl) ⟨1200998, by rfl⟩ : syracuseStep 1601331 = 2401997) B2401997
theorem B1601347 : Blo 1600999 1601347 := bstep (se 1 (by rfl) ⟨1201010, by rfl⟩ : syracuseStep 1601347 = 2402021) B2402021
theorem B2404163 : Blo 1600999 2404163 := bstep (se 1 (by rfl) ⟨1803122, by rfl⟩ : syracuseStep 2404163 = 3606245) B3606245
theorem B1601363 : Blo 1600999 1601363 := bstep (se 1 (by rfl) ⟨1201022, by rfl⟩ : syracuseStep 1601363 = 2402045) B2402045
theorem B2404193 : Blo 1600999 2404193 := bstep (se 2 (by rfl) ⟨901572, by rfl⟩ : syracuseStep 2404193 = 1803145) B1803145
theorem B1601379 : Blo 1600999 1601379 := bstep (se 1 (by rfl) ⟨1201034, by rfl⟩ : syracuseStep 1601379 = 2402069) B2402069
theorem B1601395 : Blo 1600999 1601395 := bstep (se 1 (by rfl) ⟨1201046, by rfl⟩ : syracuseStep 1601395 = 2402093) B2402093
theorem B2436979 : Blo 1600999 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B2404211 : Blo 1600999 2404211 := bstep (se 1 (by rfl) ⟨1803158, by rfl⟩ : syracuseStep 2404211 = 3606317) B3606317
theorem B1601411 : Blo 1600999 1601411 := bstep (se 1 (by rfl) ⟨1201058, by rfl⟩ : syracuseStep 1601411 = 2402117) B2402117
theorem B2404241 : Blo 1600999 2404241 := bstep (se 2 (by rfl) ⟨901590, by rfl⟩ : syracuseStep 2404241 = 1803181) B1803181
theorem B1601427 : Blo 1600999 1601427 := bstep (se 1 (by rfl) ⟨1201070, by rfl⟩ : syracuseStep 1601427 = 2402141) B2402141
theorem B1601443 : Blo 1600999 1601443 := bstep (se 1 (by rfl) ⟨1201082, by rfl⟩ : syracuseStep 1601443 = 2402165) B2402165
theorem B2404259 : Blo 1600999 2404259 := bstep (se 1 (by rfl) ⟨1803194, by rfl⟩ : syracuseStep 2404259 = 3606389) B3606389
theorem B1601459 : Blo 1600999 1601459 := bstep (se 1 (by rfl) ⟨1201094, by rfl⟩ : syracuseStep 1601459 = 2402189) B2402189
theorem B2404289 : Blo 1600999 2404289 := bstep (se 2 (by rfl) ⟨901608, by rfl⟩ : syracuseStep 2404289 = 1803217) B1803217
theorem B1601475 : Blo 1600999 1601475 := bstep (se 1 (by rfl) ⟨1201106, by rfl⟩ : syracuseStep 1601475 = 2402213) B2402213
theorem B1601491 : Blo 1600999 1601491 := bstep (se 1 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 1601491 = 2402237) B2402237
theorem B2404307 : Blo 1600999 2404307 := bstep (se 1 (by rfl) ⟨1803230, by rfl⟩ : syracuseStep 2404307 = 3606461) B3606461
theorem B1601507 : Blo 1600999 1601507 := bstep (se 1 (by rfl) ⟨1201130, by rfl⟩ : syracuseStep 1601507 = 2402261) B2402261
theorem B2404337 : Blo 1600999 2404337 := bstep (se 2 (by rfl) ⟨901626, by rfl⟩ : syracuseStep 2404337 = 1803253) B1803253
theorem B1601523 : Blo 1600999 1601523 := bstep (se 1 (by rfl) ⟨1201142, by rfl⟩ : syracuseStep 1601523 = 2402285) B2402285
theorem B1601539 : Blo 1600999 1601539 := bstep (se 1 (by rfl) ⟨1201154, by rfl⟩ : syracuseStep 1601539 = 2402309) B2402309
theorem B2404355 : Blo 1600999 2404355 := bstep (se 1 (by rfl) ⟨1803266, by rfl⟩ : syracuseStep 2404355 = 3606533) B3606533
theorem B1601555 : Blo 1600999 1601555 := bstep (se 1 (by rfl) ⟨1201166, by rfl⟩ : syracuseStep 1601555 = 2402333) B2402333
theorem B2404385 : Blo 1600999 2404385 := bstep (se 2 (by rfl) ⟨901644, by rfl⟩ : syracuseStep 2404385 = 1803289) B1803289
theorem B1601571 : Blo 1600999 1601571 := bstep (se 1 (by rfl) ⟨1201178, by rfl⟩ : syracuseStep 1601571 = 2402357) B2402357
theorem B9121841 : Blo 1600999 9121841 := bstep (se 2 (by rfl) ⟨3420690, by rfl⟩ : syracuseStep 9121841 = 6841381) B6841381
theorem B4165681 : Blo 1600999 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B1601587 : Blo 1600999 1601587 := bstep (se 1 (by rfl) ⟨1201190, by rfl⟩ : syracuseStep 1601587 = 2402381) B2402381
theorem B2404403 : Blo 1600999 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B2281537 : Blo 1600999 2281537 := bstep (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) B1711153
theorem B1601603 : Blo 1600999 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B2027587 : Blo 1600999 2027587 := bstep (se 1 (by rfl) ⟨1520690, by rfl⟩ : syracuseStep 2027587 = 3041381) B3041381
theorem B9744461 : Blo 1600999 9744461 := bstep (se 3 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 9744461 = 3654173) B3654173
theorem B2404433 : Blo 1600999 2404433 := bstep (se 2 (by rfl) ⟨901662, by rfl⟩ : syracuseStep 2404433 = 1803325) B1803325
theorem B1601619 : Blo 1600999 1601619 := bstep (se 1 (by rfl) ⟨1201214, by rfl⟩ : syracuseStep 1601619 = 2402429) B2402429
theorem B1601635 : Blo 1600999 1601635 := bstep (se 1 (by rfl) ⟨1201226, by rfl⟩ : syracuseStep 1601635 = 2402453) B2402453
theorem B2404451 : Blo 1600999 2404451 := bstep (se 1 (by rfl) ⟨1803338, by rfl⟩ : syracuseStep 2404451 = 3606677) B3606677
theorem B10268785 : Blo 1600999 10268785 := bstep (se 2 (by rfl) ⟨3850794, by rfl⟩ : syracuseStep 10268785 = 7701589) B7701589
theorem B1601651 : Blo 1600999 1601651 := bstep (se 1 (by rfl) ⟨1201238, by rfl⟩ : syracuseStep 1601651 = 2402477) B2402477
theorem B2404481 : Blo 1600999 2404481 := bstep (se 2 (by rfl) ⟨901680, by rfl⟩ : syracuseStep 2404481 = 1803361) B1803361
theorem B1601667 : Blo 1600999 1601667 := bstep (se 1 (by rfl) ⟨1201250, by rfl⟩ : syracuseStep 1601667 = 2402501) B2402501
theorem B1601683 : Blo 1600999 1601683 := bstep (se 1 (by rfl) ⟨1201262, by rfl⟩ : syracuseStep 1601683 = 2402525) B2402525
theorem B2404499 : Blo 1600999 2404499 := bstep (se 1 (by rfl) ⟨1803374, by rfl⟩ : syracuseStep 2404499 = 3606749) B3606749
theorem B4870307 : Blo 1600999 4870307 := bstep (se 1 (by rfl) ⟨3652730, by rfl⟩ : syracuseStep 4870307 = 7305461) B7305461
theorem B1601699 : Blo 1600999 1601699 := bstep (se 1 (by rfl) ⟨1201274, by rfl⟩ : syracuseStep 1601699 = 2402549) B2402549
theorem B2027683 : Blo 1600999 2027683 := bstep (se 1 (by rfl) ⟨1520762, by rfl⟩ : syracuseStep 2027683 = 3041525) B3041525
theorem B1601715 : Blo 1600999 1601715 := bstep (se 1 (by rfl) ⟨1201286, by rfl⟩ : syracuseStep 1601715 = 2402573) B2402573
theorem B1601731 : Blo 1600999 1601731 := bstep (se 1 (by rfl) ⟨1201298, by rfl⟩ : syracuseStep 1601731 = 2402597) B2402597
theorem B5132497 : Blo 1600999 5132497 := bstep (se 2 (by rfl) ⟨1924686, by rfl⟩ : syracuseStep 5132497 = 3849373) B3849373
theorem B1601747 : Blo 1600999 1601747 := bstep (se 1 (by rfl) ⟨1201310, by rfl⟩ : syracuseStep 1601747 = 2402621) B2402621
theorem B93622499 : Blo 1600999 93622499 := bstep (se 1 (by rfl) ⟨70216874, by rfl⟩ : syracuseStep 93622499 = 140433749) B140433749
theorem B1601763 : Blo 1600999 1601763 := bstep (se 1 (by rfl) ⟨1201322, by rfl⟩ : syracuseStep 1601763 = 2402645) B2402645
theorem B4870381 : Blo 1600999 4870381 := bstep (se 3 (by rfl) ⟨913196, by rfl⟩ : syracuseStep 4870381 = 1826393) B1826393
theorem B8114417 : Blo 1600999 8114417 := bstep (se 2 (by rfl) ⟨3042906, by rfl⟩ : syracuseStep 8114417 = 6085813) B6085813
theorem B1601779 : Blo 1600999 1601779 := bstep (se 1 (by rfl) ⟨1201334, by rfl⟩ : syracuseStep 1601779 = 2402669) B2402669
theorem B1601795 : Blo 1600999 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B1601811 : Blo 1600999 1601811 := bstep (se 1 (by rfl) ⟨1201358, by rfl⟩ : syracuseStep 1601811 = 2402717) B2402717
theorem B1601827 : Blo 1600999 1601827 := bstep (se 1 (by rfl) ⟨1201370, by rfl⟩ : syracuseStep 1601827 = 2402741) B2402741
theorem B1601843 : Blo 1600999 1601843 := bstep (se 1 (by rfl) ⟨1201382, by rfl⟩ : syracuseStep 1601843 = 2402765) B2402765
theorem B1601859 : Blo 1600999 1601859 := bstep (se 1 (by rfl) ⟨1201394, by rfl⟩ : syracuseStep 1601859 = 2402789) B2402789
theorem B8106317 : Blo 1600999 8106317 := bstep (se 3 (by rfl) ⟨1519934, by rfl⟩ : syracuseStep 8106317 = 3039869) B3039869
theorem B1601875 : Blo 1600999 1601875 := bstep (se 1 (by rfl) ⟨1201406, by rfl⟩ : syracuseStep 1601875 = 2402813) B2402813
theorem B1601891 : Blo 1600999 1601891 := bstep (se 1 (by rfl) ⟨1201418, by rfl⟩ : syracuseStep 1601891 = 2402837) B2402837
theorem B1601907 : Blo 1600999 1601907 := bstep (se 1 (by rfl) ⟨1201430, by rfl⟩ : syracuseStep 1601907 = 2402861) B2402861
theorem B1601923 : Blo 1600999 1601923 := bstep (se 1 (by rfl) ⟨1201442, by rfl⟩ : syracuseStep 1601923 = 2402885) B2402885
theorem B2281873 : Blo 1600999 2281873 := bstep (se 2 (by rfl) ⟨855702, by rfl⟩ : syracuseStep 2281873 = 1711405) B1711405
theorem B1601939 : Blo 1600999 1601939 := bstep (se 1 (by rfl) ⟨1201454, by rfl⟩ : syracuseStep 1601939 = 2402909) B2402909
theorem B1601955 : Blo 1600999 1601955 := bstep (se 1 (by rfl) ⟨1201466, by rfl⟩ : syracuseStep 1601955 = 2402933) B2402933
theorem B1601971 : Blo 1600999 1601971 := bstep (se 1 (by rfl) ⟨1201478, by rfl⟩ : syracuseStep 1601971 = 2402957) B2402957
theorem B1601987 : Blo 1600999 1601987 := bstep (se 1 (by rfl) ⟨1201490, by rfl⟩ : syracuseStep 1601987 = 2402981) B2402981
theorem B23097797 : Blo 1600999 23097797 := bstep (se 4 (by rfl) ⟨2165418, by rfl⟩ : syracuseStep 23097797 = 4330837) B4330837
theorem B1602003 : Blo 1600999 1602003 := bstep (se 1 (by rfl) ⟨1201502, by rfl⟩ : syracuseStep 1602003 = 2403005) B2403005
theorem B1602019 : Blo 1600999 1602019 := bstep (se 1 (by rfl) ⟨1201514, by rfl⟩ : syracuseStep 1602019 = 2403029) B2403029
theorem B1602035 : Blo 1600999 1602035 := bstep (se 1 (by rfl) ⟨1201526, by rfl⟩ : syracuseStep 1602035 = 2403053) B2403053
theorem B1602051 : Blo 1600999 1602051 := bstep (se 1 (by rfl) ⟨1201538, by rfl⟩ : syracuseStep 1602051 = 2403077) B2403077
theorem B1602067 : Blo 1600999 1602067 := bstep (se 1 (by rfl) ⟨1201550, by rfl⟩ : syracuseStep 1602067 = 2403101) B2403101
theorem B1602083 : Blo 1600999 1602083 := bstep (se 1 (by rfl) ⟨1201562, by rfl⟩ : syracuseStep 1602083 = 2403125) B2403125
theorem B1602099 : Blo 1600999 1602099 := bstep (se 1 (by rfl) ⟨1201574, by rfl⟩ : syracuseStep 1602099 = 2403149) B2403149
theorem B1602115 : Blo 1600999 1602115 := bstep (se 1 (by rfl) ⟨1201586, by rfl⟩ : syracuseStep 1602115 = 2403173) B2403173
theorem B12325445 : Blo 1600999 12325445 := bstep (se 4 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 12325445 = 2311021) B2311021
theorem B1602131 : Blo 1600999 1602131 := bstep (se 1 (by rfl) ⟨1201598, by rfl⟩ : syracuseStep 1602131 = 2403197) B2403197
theorem B1602147 : Blo 1600999 1602147 := bstep (se 1 (by rfl) ⟨1201610, by rfl⟩ : syracuseStep 1602147 = 2403221) B2403221
theorem B6083171 : Blo 1600999 6083171 := bstep (se 1 (by rfl) ⟨4562378, by rfl⟩ : syracuseStep 6083171 = 9124757) B9124757
theorem B2740835 : Blo 1600999 2740835 := bstep (se 1 (by rfl) ⟨2055626, by rfl⟩ : syracuseStep 2740835 = 4111253) B4111253
theorem B1602163 : Blo 1600999 1602163 := bstep (se 1 (by rfl) ⟨1201622, by rfl⟩ : syracuseStep 1602163 = 2403245) B2403245
theorem B1602179 : Blo 1600999 1602179 := bstep (se 1 (by rfl) ⟨1201634, by rfl⟩ : syracuseStep 1602179 = 2403269) B2403269
theorem B3248785 : Blo 1600999 3248785 := bstep (se 2 (by rfl) ⟨1218294, by rfl⟩ : syracuseStep 3248785 = 2436589) B2436589
theorem B1602195 : Blo 1600999 1602195 := bstep (se 1 (by rfl) ⟨1201646, by rfl⟩ : syracuseStep 1602195 = 2403293) B2403293
theorem B2028179 : Blo 1600999 2028179 := bstep (se 1 (by rfl) ⟨1521134, by rfl⟩ : syracuseStep 2028179 = 3042269) B3042269
theorem B1602211 : Blo 1600999 1602211 := bstep (se 1 (by rfl) ⟨1201658, by rfl⟩ : syracuseStep 1602211 = 2403317) B2403317
theorem B1602227 : Blo 1600999 1602227 := bstep (se 1 (by rfl) ⟨1201670, by rfl⟩ : syracuseStep 1602227 = 2403341) B2403341
theorem B1602243 : Blo 1600999 1602243 := bstep (se 1 (by rfl) ⟨1201682, by rfl⟩ : syracuseStep 1602243 = 2403365) B2403365
theorem B12169925 : Blo 1600999 12169925 := bstep (se 4 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 12169925 = 2281861) B2281861
theorem B3846865 : Blo 1600999 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1602259 : Blo 1600999 1602259 := bstep (se 1 (by rfl) ⟨1201694, by rfl⟩ : syracuseStep 1602259 = 2403389) B2403389
theorem B1602275 : Blo 1600999 1602275 := bstep (se 1 (by rfl) ⟨1201706, by rfl⟩ : syracuseStep 1602275 = 2403413) B2403413
theorem B77959907 : Blo 1600999 77959907 := bstep (se 1 (by rfl) ⟨58469930, by rfl⟩ : syracuseStep 77959907 = 116939861) B116939861
theorem B3420913 : Blo 1600999 3420913 := bstep (se 2 (by rfl) ⟨1282842, by rfl⟩ : syracuseStep 3420913 = 2565685) B2565685
theorem B1602291 : Blo 1600999 1602291 := bstep (se 1 (by rfl) ⟨1201718, by rfl⟩ : syracuseStep 1602291 = 2403437) B2403437
theorem B1602307 : Blo 1600999 1602307 := bstep (se 1 (by rfl) ⟨1201730, by rfl⟩ : syracuseStep 1602307 = 2403461) B2403461
theorem B1602323 : Blo 1600999 1602323 := bstep (se 1 (by rfl) ⟨1201742, by rfl⟩ : syracuseStep 1602323 = 2403485) B2403485
theorem B1602339 : Blo 1600999 1602339 := bstep (se 1 (by rfl) ⟨1201754, by rfl⟩ : syracuseStep 1602339 = 2403509) B2403509
theorem B1602355 : Blo 1600999 1602355 := bstep (se 1 (by rfl) ⟨1201766, by rfl⟩ : syracuseStep 1602355 = 2403533) B2403533
theorem B1602371 : Blo 1600999 1602371 := bstep (se 1 (by rfl) ⟨1201778, by rfl⟩ : syracuseStep 1602371 = 2403557) B2403557
theorem B1602387 : Blo 1600999 1602387 := bstep (se 1 (by rfl) ⟨1201790, by rfl⟩ : syracuseStep 1602387 = 2403581) B2403581
theorem B1602403 : Blo 1600999 1602403 := bstep (se 1 (by rfl) ⟨1201802, by rfl⟩ : syracuseStep 1602403 = 2403605) B2403605
theorem B1602419 : Blo 1600999 1602419 := bstep (se 1 (by rfl) ⟨1201814, by rfl⟩ : syracuseStep 1602419 = 2403629) B2403629
theorem B1602435 : Blo 1600999 1602435 := bstep (se 1 (by rfl) ⟨1201826, by rfl⟩ : syracuseStep 1602435 = 2403653) B2403653
theorem B1602451 : Blo 1600999 1602451 := bstep (se 1 (by rfl) ⟨1201838, by rfl⟩ : syracuseStep 1602451 = 2403677) B2403677
theorem B1602467 : Blo 1600999 1602467 := bstep (se 1 (by rfl) ⟨1201850, by rfl⟩ : syracuseStep 1602467 = 2403701) B2403701
theorem B1602483 : Blo 1600999 1602483 := bstep (se 1 (by rfl) ⟨1201862, by rfl⟩ : syracuseStep 1602483 = 2403725) B2403725
theorem B1602499 : Blo 1600999 1602499 := bstep (se 1 (by rfl) ⟨1201874, by rfl⟩ : syracuseStep 1602499 = 2403749) B2403749
theorem B8336333 : Blo 1600999 8336333 := bstep (se 3 (by rfl) ⟨1563062, by rfl⟩ : syracuseStep 8336333 = 3126125) B3126125
theorem B1602515 : Blo 1600999 1602515 := bstep (se 1 (by rfl) ⟨1201886, by rfl⟩ : syracuseStep 1602515 = 2403773) B2403773
theorem B1602531 : Blo 1600999 1602531 := bstep (se 1 (by rfl) ⟨1201898, by rfl⟩ : syracuseStep 1602531 = 2403797) B2403797
theorem B1602547 : Blo 1600999 1602547 := bstep (se 1 (by rfl) ⟨1201910, by rfl⟩ : syracuseStep 1602547 = 2403821) B2403821
theorem B1602563 : Blo 1600999 1602563 := bstep (se 1 (by rfl) ⟨1201922, by rfl⟩ : syracuseStep 1602563 = 2403845) B2403845
theorem B4559885 : Blo 1600999 4559885 := bstep (se 3 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 4559885 = 1709957) B1709957
theorem B1602579 : Blo 1600999 1602579 := bstep (se 1 (by rfl) ⟨1201934, by rfl⟩ : syracuseStep 1602579 = 2403869) B2403869
theorem B1602595 : Blo 1600999 1602595 := bstep (se 1 (by rfl) ⟨1201946, by rfl⟩ : syracuseStep 1602595 = 2403893) B2403893
theorem B1602611 : Blo 1600999 1602611 := bstep (se 1 (by rfl) ⟨1201958, by rfl⟩ : syracuseStep 1602611 = 2403917) B2403917
theorem B1602627 : Blo 1600999 1602627 := bstep (se 1 (by rfl) ⟨1201970, by rfl⟩ : syracuseStep 1602627 = 2403941) B2403941
theorem B5403725 : Blo 1600999 5403725 := bstep (se 3 (by rfl) ⟨1013198, by rfl⟩ : syracuseStep 5403725 = 2026397) B2026397
theorem B1602643 : Blo 1600999 1602643 := bstep (se 1 (by rfl) ⟨1201982, by rfl⟩ : syracuseStep 1602643 = 2403965) B2403965
theorem B1602659 : Blo 1600999 1602659 := bstep (se 1 (by rfl) ⟨1201994, by rfl⟩ : syracuseStep 1602659 = 2403989) B2403989
theorem B1602675 : Blo 1600999 1602675 := bstep (se 1 (by rfl) ⟨1202006, by rfl⟩ : syracuseStep 1602675 = 2404013) B2404013
theorem B5403779 : Blo 1600999 5403779 := bstep (se 1 (by rfl) ⟨4052834, by rfl⟩ : syracuseStep 5403779 = 8105669) B8105669
theorem B1602691 : Blo 1600999 1602691 := bstep (se 1 (by rfl) ⟨1202018, by rfl⟩ : syracuseStep 1602691 = 2404037) B2404037
theorem B1602707 : Blo 1600999 1602707 := bstep (se 1 (by rfl) ⟨1202030, by rfl⟩ : syracuseStep 1602707 = 2404061) B2404061
theorem B1602723 : Blo 1600999 1602723 := bstep (se 1 (by rfl) ⟨1202042, by rfl⟩ : syracuseStep 1602723 = 2404085) B2404085
theorem B1602739 : Blo 1600999 1602739 := bstep (se 1 (by rfl) ⟨1202054, by rfl⟩ : syracuseStep 1602739 = 2404109) B2404109
theorem B1602755 : Blo 1600999 1602755 := bstep (se 1 (by rfl) ⟨1202066, by rfl⟩ : syracuseStep 1602755 = 2404133) B2404133
theorem B4560077 : Blo 1600999 4560077 := bstep (se 3 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 4560077 = 1710029) B1710029
theorem B1602771 : Blo 1600999 1602771 := bstep (se 1 (by rfl) ⟨1202078, by rfl⟩ : syracuseStep 1602771 = 2404157) B2404157
theorem B1602787 : Blo 1600999 1602787 := bstep (se 1 (by rfl) ⟨1202090, by rfl⟩ : syracuseStep 1602787 = 2404181) B2404181
theorem B1602803 : Blo 1600999 1602803 := bstep (se 1 (by rfl) ⟨1202102, by rfl⟩ : syracuseStep 1602803 = 2404205) B2404205
theorem B1602819 : Blo 1600999 1602819 := bstep (se 1 (by rfl) ⟨1202114, by rfl⟩ : syracuseStep 1602819 = 2404229) B2404229
theorem B1602835 : Blo 1600999 1602835 := bstep (se 1 (by rfl) ⟨1202126, by rfl⟩ : syracuseStep 1602835 = 2404253) B2404253
theorem B1602851 : Blo 1600999 1602851 := bstep (se 1 (by rfl) ⟨1202138, by rfl⟩ : syracuseStep 1602851 = 2404277) B2404277
theorem B1602867 : Blo 1600999 1602867 := bstep (se 1 (by rfl) ⟨1202150, by rfl⟩ : syracuseStep 1602867 = 2404301) B2404301
theorem B1602883 : Blo 1600999 1602883 := bstep (se 1 (by rfl) ⟨1202162, by rfl⟩ : syracuseStep 1602883 = 2404325) B2404325
theorem B1602899 : Blo 1600999 1602899 := bstep (se 1 (by rfl) ⟨1202174, by rfl⟩ : syracuseStep 1602899 = 2404349) B2404349
theorem B1602915 : Blo 1600999 1602915 := bstep (se 1 (by rfl) ⟨1202186, by rfl⟩ : syracuseStep 1602915 = 2404373) B2404373
theorem B15398257 : Blo 1600999 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B1602931 : Blo 1600999 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B1602947 : Blo 1600999 1602947 := bstep (se 1 (by rfl) ⟨1202210, by rfl⟩ : syracuseStep 1602947 = 2404421) B2404421
theorem B5404049 : Blo 1600999 5404049 := bstep (se 2 (by rfl) ⟨2026518, by rfl⟩ : syracuseStep 5404049 = 4053037) B4053037
theorem B1602963 : Blo 1600999 1602963 := bstep (se 1 (by rfl) ⟨1202222, by rfl⟩ : syracuseStep 1602963 = 2404445) B2404445
theorem B1602979 : Blo 1600999 1602979 := bstep (se 1 (by rfl) ⟨1202234, by rfl⟩ : syracuseStep 1602979 = 2404469) B2404469
theorem B1602995 : Blo 1600999 1602995 := bstep (se 1 (by rfl) ⟨1202246, by rfl⟩ : syracuseStep 1602995 = 2404493) B2404493
theorem B9123299 : Blo 1600999 9123299 := bstep (se 1 (by rfl) ⟨6842474, by rfl⟩ : syracuseStep 9123299 = 13684949) B13684949
theorem B4330979 : Blo 1600999 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B18241037 : Blo 1600999 18241037 := bstep (se 3 (by rfl) ⟨3420194, by rfl⟩ : syracuseStep 18241037 = 6840389) B6840389
theorem B2741779 : Blo 1600999 2741779 := bstep (se 1 (by rfl) ⟨2056334, by rfl⟩ : syracuseStep 2741779 = 4112669) B4112669
theorem B6084173 : Blo 1600999 6084173 := bstep (se 3 (by rfl) ⟨1140782, by rfl⟩ : syracuseStep 6084173 = 2281565) B2281565
theorem B6846029 : Blo 1600999 6846029 := bstep (se 3 (by rfl) ⟨1283630, by rfl⟩ : syracuseStep 6846029 = 2567261) B2567261
theorem B9737891 : Blo 1600999 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B14612237 : Blo 1600999 14612237 := bstep (se 3 (by rfl) ⟨2739794, by rfl⟩ : syracuseStep 14612237 = 5479589) B5479589
theorem B10958627 : Blo 1600999 10958627 := bstep (se 1 (by rfl) ⟨8218970, by rfl⟩ : syracuseStep 10958627 = 16437941) B16437941
theorem B3602321 : Blo 1600999 3602321 := bstep (se 2 (by rfl) ⟨1350870, by rfl⟩ : syracuseStep 3602321 = 2701741) B2701741
theorem B3602339 : Blo 1600999 3602339 := bstep (se 1 (by rfl) ⟨2701754, by rfl⟩ : syracuseStep 3602339 = 5403509) B5403509
theorem B5404589 : Blo 1600999 5404589 := bstep (se 3 (by rfl) ⟨1013360, by rfl⟩ : syracuseStep 5404589 = 2026721) B2026721
theorem B4388785 : Blo 1600999 4388785 := bstep (se 2 (by rfl) ⟨1645794, by rfl⟩ : syracuseStep 4388785 = 3291589) B3291589
theorem B5404643 : Blo 1600999 5404643 := bstep (se 1 (by rfl) ⟨4053482, by rfl⟩ : syracuseStep 5404643 = 8106965) B8106965
theorem B50706485 : Blo 1600999 50706485 := bstep (se 5 (by rfl) ⟨2376866, by rfl⟩ : syracuseStep 50706485 = 4753733) B4753733
theorem B6166691 : Blo 1600999 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B4561069 : Blo 1600999 4561069 := bstep (se 3 (by rfl) ⟨855200, by rfl⟩ : syracuseStep 4561069 = 1710401) B1710401
theorem B3602609 : Blo 1600999 3602609 := bstep (se 2 (by rfl) ⟨1350978, by rfl⟩ : syracuseStep 3602609 = 2701957) B2701957
theorem B3602627 : Blo 1600999 3602627 := bstep (se 1 (by rfl) ⟨2701970, by rfl⟩ : syracuseStep 3602627 = 5403941) B5403941
theorem B5404913 : Blo 1600999 5404913 := bstep (se 2 (by rfl) ⟨2026842, by rfl⟩ : syracuseStep 5404913 = 4053685) B4053685
theorem B4331875 : Blo 1600999 4331875 := bstep (se 1 (by rfl) ⟨3248906, by rfl⟩ : syracuseStep 4331875 = 6497813) B6497813
theorem B4331885 : Blo 1600999 4331885 := bstep (se 3 (by rfl) ⟨812228, by rfl⟩ : syracuseStep 4331885 = 1624457) B1624457
theorem B4053361 : Blo 1600999 4053361 := bstep (se 2 (by rfl) ⟨1520010, by rfl⟩ : syracuseStep 4053361 = 3040021) B3040021
theorem B3602897 : Blo 1600999 3602897 := bstep (se 2 (by rfl) ⟨1351086, by rfl⟩ : syracuseStep 3602897 = 2702173) B2702173
theorem B2701795 : Blo 1600999 2701795 := bstep (se 1 (by rfl) ⟨2026346, by rfl⟩ : syracuseStep 2701795 = 4052693) B4052693
theorem B3602915 : Blo 1600999 3602915 := bstep (se 1 (by rfl) ⟨2702186, by rfl⟩ : syracuseStep 3602915 = 5404373) B5404373
theorem B11549155 : Blo 1600999 11549155 := bstep (se 1 (by rfl) ⟨8661866, by rfl⟩ : syracuseStep 11549155 = 17323733) B17323733
theorem B2701937 : Blo 1600999 2701937 := bstep (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) B2026453
theorem B16439921 : Blo 1600999 16439921 := bstep (se 2 (by rfl) ⟨6164970, by rfl⟩ : syracuseStep 16439921 = 12329941) B12329941
theorem B4053635 : Blo 1600999 4053635 := bstep (se 1 (by rfl) ⟨3040226, by rfl⟩ : syracuseStep 4053635 = 6080453) B6080453
theorem B15604451 : Blo 1600999 15604451 := bstep (se 1 (by rfl) ⟨11703338, by rfl⟩ : syracuseStep 15604451 = 23406677) B23406677
theorem B2702065 : Blo 1600999 2702065 := bstep (se 2 (by rfl) ⟨1013274, by rfl⟩ : syracuseStep 2702065 = 2026549) B2026549
theorem B3603185 : Blo 1600999 3603185 := bstep (se 2 (by rfl) ⟨1351194, by rfl⟩ : syracuseStep 3603185 = 2702389) B2702389
theorem B3603203 : Blo 1600999 3603203 := bstep (se 1 (by rfl) ⟨2702402, by rfl⟩ : syracuseStep 3603203 = 5404805) B5404805
theorem B5405453 : Blo 1600999 5405453 := bstep (se 3 (by rfl) ⟨1013522, by rfl⟩ : syracuseStep 5405453 = 2027045) B2027045
theorem B2702099 : Blo 1600999 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B71219989 : Blo 1600999 71219989 := bstep (se 6 (by rfl) ⟨1669218, by rfl⟩ : syracuseStep 71219989 = 3338437) B3338437
theorem B4053827 : Blo 1600999 4053827 := bstep (se 1 (by rfl) ⟨3040370, by rfl⟩ : syracuseStep 4053827 = 6080741) B6080741
theorem B5405507 : Blo 1600999 5405507 := bstep (se 1 (by rfl) ⟨4054130, by rfl⟩ : syracuseStep 5405507 = 8108261) B8108261
theorem B5135213 : Blo 1600999 5135213 := bstep (se 3 (by rfl) ⟨962852, by rfl⟩ : syracuseStep 5135213 = 1925705) B1925705
theorem B2702227 : Blo 1600999 2702227 := bstep (se 1 (by rfl) ⟨2026670, by rfl⟩ : syracuseStep 2702227 = 4053341) B4053341
theorem B19741681 : Blo 1600999 19741681 := bstep (se 2 (by rfl) ⟨7403130, by rfl⟩ : syracuseStep 19741681 = 14806261) B14806261
theorem B1801219 : Blo 1600999 1801219 := bstep (se 1 (by rfl) ⟨1350914, by rfl⟩ : syracuseStep 1801219 = 2701829) B2701829
theorem B3603473 : Blo 1600999 3603473 := bstep (se 2 (by rfl) ⟨1351302, by rfl⟩ : syracuseStep 3603473 = 2702605) B2702605
theorem B2702369 : Blo 1600999 2702369 := bstep (se 2 (by rfl) ⟨1013388, by rfl⟩ : syracuseStep 2702369 = 2026777) B2026777
theorem B11107363 : Blo 1600999 11107363 := bstep (se 1 (by rfl) ⟨8330522, by rfl⟩ : syracuseStep 11107363 = 16661045) B16661045
theorem B3603491 : Blo 1600999 3603491 := bstep (se 1 (by rfl) ⟨2702618, by rfl⟩ : syracuseStep 3603491 = 5405237) B5405237
theorem B5405777 : Blo 1600999 5405777 := bstep (se 2 (by rfl) ⟨2027166, by rfl⟩ : syracuseStep 5405777 = 4054333) B4054333
theorem B1801363 : Blo 1600999 1801363 := bstep (se 1 (by rfl) ⟨1351022, by rfl⟩ : syracuseStep 1801363 = 2702045) B2702045
theorem B2702497 : Blo 1600999 2702497 := bstep (se 2 (by rfl) ⟨1013436, by rfl⟩ : syracuseStep 2702497 = 2026873) B2026873
theorem B8109233 : Blo 1600999 8109233 := bstep (se 2 (by rfl) ⟨3040962, by rfl⟩ : syracuseStep 8109233 = 6081925) B6081925
theorem B2702531 : Blo 1600999 2702531 := bstep (se 1 (by rfl) ⟨2026898, by rfl⟩ : syracuseStep 2702531 = 4053797) B4053797
theorem B1924355 : Blo 1600999 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B1711379 : Blo 1600999 1711379 := bstep (se 1 (by rfl) ⟨1283534, by rfl⟩ : syracuseStep 1711379 = 2567069) B2567069
theorem B1801507 : Blo 1600999 1801507 := bstep (se 1 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 1801507 = 2702261) B2702261
theorem B3603761 : Blo 1600999 3603761 := bstep (se 2 (by rfl) ⟨1351410, by rfl⟩ : syracuseStep 3603761 = 2702821) B2702821
theorem B2702659 : Blo 1600999 2702659 := bstep (se 1 (by rfl) ⟨2026994, by rfl⟩ : syracuseStep 2702659 = 4053989) B4053989
theorem B3603779 : Blo 1600999 3603779 := bstep (se 1 (by rfl) ⟨2702834, by rfl⟩ : syracuseStep 3603779 = 5405669) B5405669
theorem B1801651 : Blo 1600999 1801651 := bstep (se 1 (by rfl) ⟨1351238, by rfl⟩ : syracuseStep 1801651 = 2702477) B2702477
theorem B2702801 : Blo 1600999 2702801 := bstep (se 2 (by rfl) ⟨1013550, by rfl⟩ : syracuseStep 2702801 = 2027101) B2027101
theorem B12164579 : Blo 1600999 12164579 := bstep (se 1 (by rfl) ⟨9123434, by rfl⟩ : syracuseStep 12164579 = 18246869) B18246869
theorem B1801795 : Blo 1600999 1801795 := bstep (se 1 (by rfl) ⟨1351346, by rfl⟩ : syracuseStep 1801795 = 2702693) B2702693
theorem B2702929 : Blo 1600999 2702929 := bstep (se 2 (by rfl) ⟨1013598, by rfl⟩ : syracuseStep 2702929 = 2027197) B2027197
theorem B3604049 : Blo 1600999 3604049 := bstep (se 2 (by rfl) ⟨1351518, by rfl⟩ : syracuseStep 3604049 = 2703037) B2703037
theorem B3604067 : Blo 1600999 3604067 := bstep (se 1 (by rfl) ⟨2703050, by rfl⟩ : syracuseStep 3604067 = 5406101) B5406101
theorem B5406317 : Blo 1600999 5406317 := bstep (se 3 (by rfl) ⟨1013684, by rfl⟩ : syracuseStep 5406317 = 2027369) B2027369
theorem B2702963 : Blo 1600999 2702963 := bstep (se 1 (by rfl) ⟨2027222, by rfl⟩ : syracuseStep 2702963 = 4054445) B4054445
theorem B6086285 : Blo 1600999 6086285 := bstep (se 3 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 6086285 = 2282357) B2282357
theorem B5406371 : Blo 1600999 5406371 := bstep (se 1 (by rfl) ⟨4054778, by rfl⟩ : syracuseStep 5406371 = 8109557) B8109557
theorem B1801939 : Blo 1600999 1801939 := bstep (se 1 (by rfl) ⟨1351454, by rfl⟩ : syracuseStep 1801939 = 2702909) B2702909
theorem B38969059 : Blo 1600999 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B4054769 : Blo 1600999 4054769 := bstep (se 2 (by rfl) ⟨1520538, by rfl⟩ : syracuseStep 4054769 = 3041077) B3041077
theorem B17325809 : Blo 1600999 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B2703091 : Blo 1600999 2703091 := bstep (se 1 (by rfl) ⟨2027318, by rfl⟩ : syracuseStep 2703091 = 4054637) B4054637
theorem B4054819 : Blo 1600999 4054819 := bstep (se 1 (by rfl) ⟨3041114, by rfl⟩ : syracuseStep 4054819 = 6082229) B6082229
theorem B1802083 : Blo 1600999 1802083 := bstep (se 1 (by rfl) ⟨1351562, by rfl⟩ : syracuseStep 1802083 = 2703125) B2703125
theorem B13688675 : Blo 1600999 13688675 := bstep (se 1 (by rfl) ⟨10266506, by rfl⟩ : syracuseStep 13688675 = 20533013) B20533013
theorem B3604337 : Blo 1600999 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B4562801 : Blo 1600999 4562801 := bstep (se 2 (by rfl) ⟨1711050, by rfl⟩ : syracuseStep 4562801 = 3422101) B3422101
theorem B2703233 : Blo 1600999 2703233 := bstep (se 2 (by rfl) ⟨1013712, by rfl⟩ : syracuseStep 2703233 = 2027425) B2027425
theorem B3604355 : Blo 1600999 3604355 := bstep (se 1 (by rfl) ⟨2703266, by rfl⟩ : syracuseStep 3604355 = 5406533) B5406533
theorem B4054961 : Blo 1600999 4054961 := bstep (se 2 (by rfl) ⟨1520610, by rfl⟩ : syracuseStep 4054961 = 3041221) B3041221
theorem B5406641 : Blo 1600999 5406641 := bstep (se 2 (by rfl) ⟨2027490, by rfl⟩ : syracuseStep 5406641 = 4054981) B4054981
theorem B1802227 : Blo 1600999 1802227 := bstep (se 1 (by rfl) ⟨1351670, by rfl⟩ : syracuseStep 1802227 = 2703341) B2703341
theorem B3604481 : Blo 1600999 3604481 := bstep (se 2 (by rfl) ⟨1351680, by rfl⟩ : syracuseStep 3604481 = 2703361) B2703361
theorem B7798801 : Blo 1600999 7798801 := bstep (se 2 (by rfl) ⟨2924550, by rfl⟩ : syracuseStep 7798801 = 5849101) B5849101
theorem B1802263 : Blo 1600999 1802263 := bstep (se 1 (by rfl) ⟨1351697, by rfl⟩ : syracuseStep 1802263 = 2703395) B2703395
theorem B6496307 : Blo 1600999 6496307 := bstep (se 1 (by rfl) ⟨4872230, by rfl⟩ : syracuseStep 6496307 = 9744461) B9744461
theorem B5554241 : Blo 1600999 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B43827275 : Blo 1600999 43827275 := bstep (se 1 (by rfl) ⟨32870456, by rfl⟩ : syracuseStep 43827275 = 65740913) B65740913
theorem B2703449 : Blo 1600999 2703449 := bstep (se 2 (by rfl) ⟨1013793, by rfl⟩ : syracuseStep 2703449 = 2027587) B2027587
theorem B62414999 : Blo 1600999 62414999 := bstep (se 1 (by rfl) ⟨46811249, by rfl⟩ : syracuseStep 62414999 = 93622499) B93622499
theorem B1802443 : Blo 1600999 1802443 := bstep (se 1 (by rfl) ⟨1351832, by rfl⟩ : syracuseStep 1802443 = 2703665) B2703665
theorem B3604697 : Blo 1600999 3604697 := bstep (se 2 (by rfl) ⟨1351761, by rfl⟩ : syracuseStep 3604697 = 2703523) B2703523
theorem B2703577 : Blo 1600999 2703577 := bstep (se 2 (by rfl) ⟨1013841, by rfl⟩ : syracuseStep 2703577 = 2027683) B2027683
theorem B3604787 : Blo 1600999 3604787 := bstep (se 1 (by rfl) ⟨2703590, by rfl⟩ : syracuseStep 3604787 = 5407181) B5407181
theorem B1802551 : Blo 1600999 1802551 := bstep (se 1 (by rfl) ⟨1351913, by rfl⟩ : syracuseStep 1802551 = 2703827) B2703827
theorem B3604823 : Blo 1600999 3604823 := bstep (se 1 (by rfl) ⟨2703617, by rfl⟩ : syracuseStep 3604823 = 5407235) B5407235
theorem B8216963 : Blo 1600999 8216963 := bstep (se 1 (by rfl) ⟨6162722, by rfl⟩ : syracuseStep 8216963 = 12325445) B12325445
theorem B6422915 : Blo 1600999 6422915 := bstep (se 1 (by rfl) ⟨4817186, by rfl⟩ : syracuseStep 6422915 = 9634373) B9634373
theorem B5407127 : Blo 1600999 5407127 := bstep (se 1 (by rfl) ⟨4055345, by rfl⟩ : syracuseStep 5407127 = 8110691) B8110691
theorem B4055447 : Blo 1600999 4055447 := bstep (se 1 (by rfl) ⟨3041585, by rfl⟩ : syracuseStep 4055447 = 6083171) B6083171
theorem B5775833 : Blo 1600999 5775833 := bstep (se 2 (by rfl) ⟨2165937, by rfl⟩ : syracuseStep 5775833 = 4331875) B4331875
theorem B1802731 : Blo 1600999 1802731 := bstep (se 1 (by rfl) ⟨1352048, by rfl⟩ : syracuseStep 1802731 = 2704097) B2704097
theorem B3605003 : Blo 1600999 3605003 := bstep (se 1 (by rfl) ⟨2703752, by rfl⟩ : syracuseStep 3605003 = 5407505) B5407505
theorem B3605057 : Blo 1600999 3605057 := bstep (se 2 (by rfl) ⟨1351896, by rfl⟩ : syracuseStep 3605057 = 2703793) B2703793
theorem B1802839 : Blo 1600999 1802839 := bstep (se 1 (by rfl) ⟨1352129, by rfl⟩ : syracuseStep 1802839 = 2704259) B2704259
theorem B3039923 : Blo 1600999 3039923 := bstep (se 1 (by rfl) ⟨2279942, by rfl⟩ : syracuseStep 3039923 = 4559885) B4559885
theorem B4563677 : Blo 1600999 4563677 := bstep (se 3 (by rfl) ⟨855689, by rfl⟩ : syracuseStep 4563677 = 1711379) B1711379
theorem B1803019 : Blo 1600999 1803019 := bstep (se 1 (by rfl) ⟨1352264, by rfl⟩ : syracuseStep 1803019 = 2704529) B2704529
theorem B2704151 : Blo 1600999 2704151 := bstep (se 1 (by rfl) ⟨2028113, by rfl⟩ : syracuseStep 2704151 = 4056227) B4056227
theorem B3605273 : Blo 1600999 3605273 := bstep (se 2 (by rfl) ⟨1351977, by rfl⟩ : syracuseStep 3605273 = 2703955) B2703955
theorem B5129011 : Blo 1600999 5129011 := bstep (se 1 (by rfl) ⟨3846758, by rfl⟩ : syracuseStep 5129011 = 7693517) B7693517
theorem B6079283 : Blo 1600999 6079283 := bstep (se 1 (by rfl) ⟨4559462, by rfl⟩ : syracuseStep 6079283 = 9118925) B9118925
theorem B3605363 : Blo 1600999 3605363 := bstep (se 1 (by rfl) ⟨2704022, by rfl⟩ : syracuseStep 3605363 = 5408045) B5408045
theorem B1803127 : Blo 1600999 1803127 := bstep (se 1 (by rfl) ⟨1352345, by rfl⟩ : syracuseStep 1803127 = 2704691) B2704691
theorem B3605399 : Blo 1600999 3605399 := bstep (se 1 (by rfl) ⟨2704049, by rfl⟩ : syracuseStep 3605399 = 5408099) B5408099
theorem B2704279 : Blo 1600999 2704279 := bstep (se 1 (by rfl) ⟨2028209, by rfl⟩ : syracuseStep 2704279 = 4056419) B4056419
theorem B5407667 : Blo 1600999 5407667 := bstep (se 1 (by rfl) ⟨4055750, by rfl⟩ : syracuseStep 5407667 = 8111501) B8111501
theorem B5129153 : Blo 1600999 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B11551693 : Blo 1600999 11551693 := bstep (se 3 (by rfl) ⟨2165942, by rfl⟩ : syracuseStep 11551693 = 4331885) B4331885
theorem B93627413 : Blo 1600999 93627413 := bstep (se 6 (by rfl) ⟨2194392, by rfl⟩ : syracuseStep 93627413 = 4388785) B4388785
theorem B1803307 : Blo 1600999 1803307 := bstep (se 1 (by rfl) ⟨1352480, by rfl⟩ : syracuseStep 1803307 = 2704961) B2704961
theorem B4056115 : Blo 1600999 4056115 := bstep (se 1 (by rfl) ⟨3042086, by rfl⟩ : syracuseStep 4056115 = 6084173) B6084173
theorem B4564019 : Blo 1600999 4564019 := bstep (se 1 (by rfl) ⟨3423014, by rfl⟩ : syracuseStep 4564019 = 6846029) B6846029
theorem B3605579 : Blo 1600999 3605579 := bstep (se 1 (by rfl) ⟨2704184, by rfl⟩ : syracuseStep 3605579 = 5408369) B5408369
theorem B3605633 : Blo 1600999 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B3040409 : Blo 1600999 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B9741491 : Blo 1600999 9741491 := bstep (se 1 (by rfl) ⟨7306118, by rfl⟩ : syracuseStep 9741491 = 14612237) B14612237
theorem B5407937 : Blo 1600999 5407937 := bstep (se 2 (by rfl) ⟨2027976, by rfl⟩ : syracuseStep 5407937 = 4055953) B4055953
theorem B4056257 : Blo 1600999 4056257 := bstep (se 2 (by rfl) ⟨1521096, by rfl⟩ : syracuseStep 4056257 = 3042193) B3042193
theorem B13690073 : Blo 1600999 13690073 := bstep (se 2 (by rfl) ⟨5133777, by rfl⟩ : syracuseStep 13690073 = 10267555) B10267555
theorem B2401547 : Blo 1600999 2401547 := bstep (se 1 (by rfl) ⟨1801160, by rfl⟩ : syracuseStep 2401547 = 3602321) B3602321
theorem B2401559 : Blo 1600999 2401559 := bstep (se 1 (by rfl) ⟨1801169, by rfl⟩ : syracuseStep 2401559 = 3602339) B3602339
theorem B26322241 : Blo 1600999 26322241 := bstep (se 2 (by rfl) ⟨9870840, by rfl⟩ : syracuseStep 26322241 = 19741681) B19741681
theorem B2401625 : Blo 1600999 2401625 := bstep (se 2 (by rfl) ⟨900609, by rfl⟩ : syracuseStep 2401625 = 1801219) B1801219
theorem B3605849 : Blo 1600999 3605849 := bstep (se 2 (by rfl) ⟨1352193, by rfl⟩ : syracuseStep 3605849 = 2704387) B2704387
theorem B8217949 : Blo 1600999 8217949 := bstep (se 3 (by rfl) ⟨1540865, by rfl⟩ : syracuseStep 8217949 = 3081731) B3081731
theorem B3605939 : Blo 1600999 3605939 := bstep (se 1 (by rfl) ⟨2704454, by rfl⟩ : syracuseStep 3605939 = 5408909) B5408909
theorem B2401739 : Blo 1600999 2401739 := bstep (se 1 (by rfl) ⟨1801304, by rfl⟩ : syracuseStep 2401739 = 3602609) B3602609
theorem B2401751 : Blo 1600999 2401751 := bstep (se 1 (by rfl) ⟨1801313, by rfl⟩ : syracuseStep 2401751 = 3602627) B3602627
theorem B3605975 : Blo 1600999 3605975 := bstep (se 1 (by rfl) ⟨2704481, by rfl⟩ : syracuseStep 3605975 = 5408963) B5408963
theorem B2704907 : Blo 1600999 2704907 := bstep (se 1 (by rfl) ⟨2028680, by rfl⟩ : syracuseStep 2704907 = 4057361) B4057361
theorem B2401817 : Blo 1600999 2401817 := bstep (se 2 (by rfl) ⟨900681, by rfl⟩ : syracuseStep 2401817 = 1801363) B1801363
theorem B7702091 : Blo 1600999 7702091 := bstep (se 1 (by rfl) ⟨5776568, by rfl⟩ : syracuseStep 7702091 = 11553137) B11553137
theorem B7308893 : Blo 1600999 7308893 := bstep (se 3 (by rfl) ⟨1370417, by rfl⟩ : syracuseStep 7308893 = 2740835) B2740835
theorem B2401931 : Blo 1600999 2401931 := bstep (se 1 (by rfl) ⟨1801448, by rfl⟩ : syracuseStep 2401931 = 3602897) B3602897
theorem B3606155 : Blo 1600999 3606155 := bstep (se 1 (by rfl) ⟨2704616, by rfl⟩ : syracuseStep 3606155 = 5409233) B5409233
theorem B2705035 : Blo 1600999 2705035 := bstep (se 1 (by rfl) ⟨2028776, by rfl⟩ : syracuseStep 2705035 = 4057553) B4057553
theorem B2401943 : Blo 1600999 2401943 := bstep (se 1 (by rfl) ⟨1801457, by rfl⟩ : syracuseStep 2401943 = 3602915) B3602915
theorem B3704471 : Blo 1600999 3704471 := bstep (se 1 (by rfl) ⟨2778353, by rfl⟩ : syracuseStep 3704471 = 5556707) B5556707
theorem B3606209 : Blo 1600999 3606209 := bstep (se 2 (by rfl) ⟨1352328, by rfl⟩ : syracuseStep 3606209 = 2704657) B2704657
theorem B2402009 : Blo 1600999 2402009 := bstep (se 2 (by rfl) ⟨900753, by rfl⟩ : syracuseStep 2402009 = 1801507) B1801507
theorem B5408477 : Blo 1600999 5408477 := bstep (se 3 (by rfl) ⟨1014089, by rfl⟩ : syracuseStep 5408477 = 2028179) B2028179
theorem B20531009 : Blo 1600999 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B2402123 : Blo 1600999 2402123 := bstep (se 1 (by rfl) ⟨1801592, by rfl⟩ : syracuseStep 2402123 = 3603185) B3603185
theorem B2402135 : Blo 1600999 2402135 := bstep (se 1 (by rfl) ⟨1801601, by rfl⟩ : syracuseStep 2402135 = 3603203) B3603203
theorem B15599461 : Blo 1600999 15599461 := bstep (se 4 (by rfl) ⟨1462449, by rfl⟩ : syracuseStep 15599461 = 2924899) B2924899
theorem B2402201 : Blo 1600999 2402201 := bstep (se 2 (by rfl) ⟨900825, by rfl⟩ : syracuseStep 2402201 = 1801651) B1801651
theorem B3606425 : Blo 1600999 3606425 := bstep (se 2 (by rfl) ⟨1352409, by rfl⟩ : syracuseStep 3606425 = 2704819) B2704819
theorem B3606515 : Blo 1600999 3606515 := bstep (se 1 (by rfl) ⟨2704886, by rfl⟩ : syracuseStep 3606515 = 5409773) B5409773
theorem B2402315 : Blo 1600999 2402315 := bstep (se 1 (by rfl) ⟨1801736, by rfl⟩ : syracuseStep 2402315 = 3603473) B3603473
theorem B23095313 : Blo 1600999 23095313 := bstep (se 2 (by rfl) ⟨8660742, by rfl⟩ : syracuseStep 23095313 = 17321485) B17321485
theorem B2402327 : Blo 1600999 2402327 := bstep (se 1 (by rfl) ⟨1801745, by rfl⟩ : syracuseStep 2402327 = 3603491) B3603491
theorem B3606551 : Blo 1600999 3606551 := bstep (se 1 (by rfl) ⟨2704913, by rfl⟩ : syracuseStep 3606551 = 5409827) B5409827
theorem B3655705 : Blo 1600999 3655705 := bstep (se 2 (by rfl) ⟨1370889, by rfl⟩ : syracuseStep 3655705 = 2741779) B2741779
theorem B14616611 : Blo 1600999 14616611 := bstep (se 1 (by rfl) ⟨10962458, by rfl⟩ : syracuseStep 14616611 = 21924917) B21924917
theorem B2402393 : Blo 1600999 2402393 := bstep (se 2 (by rfl) ⟨900897, by rfl⟩ : syracuseStep 2402393 = 1801795) B1801795
theorem B2402507 : Blo 1600999 2402507 := bstep (se 1 (by rfl) ⟨1801880, by rfl⟩ : syracuseStep 2402507 = 3603761) B3603761
theorem B3606731 : Blo 1600999 3606731 := bstep (se 1 (by rfl) ⟨2705048, by rfl⟩ : syracuseStep 3606731 = 5410097) B5410097
theorem B2402519 : Blo 1600999 2402519 := bstep (se 1 (by rfl) ⟨1801889, by rfl⟩ : syracuseStep 2402519 = 3603779) B3603779
theorem B6080771 : Blo 1600999 6080771 := bstep (se 1 (by rfl) ⟨4560578, by rfl⟩ : syracuseStep 6080771 = 9121157) B9121157
theorem B2402585 : Blo 1600999 2402585 := bstep (se 2 (by rfl) ⟨900969, by rfl⟩ : syracuseStep 2402585 = 1801939) B1801939
theorem B6842713 : Blo 1600999 6842713 := bstep (se 2 (by rfl) ⟨2566017, by rfl⟩ : syracuseStep 6842713 = 5132035) B5132035
theorem B2402699 : Blo 1600999 2402699 := bstep (se 1 (by rfl) ⟨1802024, by rfl⟩ : syracuseStep 2402699 = 3604049) B3604049
theorem B2402711 : Blo 1600999 2402711 := bstep (se 1 (by rfl) ⟨1802033, by rfl⟩ : syracuseStep 2402711 = 3604067) B3604067
theorem B4057523 : Blo 1600999 4057523 := bstep (se 1 (by rfl) ⟨3043142, by rfl⟩ : syracuseStep 4057523 = 6086285) B6086285
theorem B2165207 : Blo 1600999 2165207 := bstep (se 1 (by rfl) ⟨1623905, by rfl⟩ : syracuseStep 2165207 = 3247811) B3247811
theorem B2402777 : Blo 1600999 2402777 := bstep (se 2 (by rfl) ⟨901041, by rfl⟩ : syracuseStep 2402777 = 1802083) B1802083
theorem B2402891 : Blo 1600999 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B3041867 : Blo 1600999 3041867 := bstep (se 1 (by rfl) ⟨2281400, by rfl⟩ : syracuseStep 3041867 = 4562801) B4562801
theorem B2402903 : Blo 1600999 2402903 := bstep (se 1 (by rfl) ⟨1802177, by rfl⟩ : syracuseStep 2402903 = 3604355) B3604355
theorem B2402969 : Blo 1600999 2402969 := bstep (se 2 (by rfl) ⟨901113, by rfl⟩ : syracuseStep 2402969 = 1802227) B1802227
theorem B6081227 : Blo 1600999 6081227 := bstep (se 1 (by rfl) ⟨4560920, by rfl⟩ : syracuseStep 6081227 = 9121841) B9121841
theorem B3042049 : Blo 1600999 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B2403083 : Blo 1600999 2403083 := bstep (se 1 (by rfl) ⟨1802312, by rfl⟩ : syracuseStep 2403083 = 3604625) B3604625
theorem B2403095 : Blo 1600999 2403095 := bstep (se 1 (by rfl) ⟨1802321, by rfl⟩ : syracuseStep 2403095 = 3604643) B3604643
theorem B2886425 : Blo 1600999 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B12167981 : Blo 1600999 12167981 := bstep (se 3 (by rfl) ⟨2281496, by rfl⟩ : syracuseStep 12167981 = 4562993) B4562993
theorem B13691713 : Blo 1600999 13691713 := bstep (se 2 (by rfl) ⟨5134392, by rfl⟩ : syracuseStep 13691713 = 10268785) B10268785
theorem B5409611 : Blo 1600999 5409611 := bstep (se 1 (by rfl) ⟨4057208, by rfl⟩ : syracuseStep 5409611 = 8114417) B8114417
theorem B2403161 : Blo 1600999 2403161 := bstep (se 2 (by rfl) ⟨901185, by rfl⟩ : syracuseStep 2403161 = 1802371) B1802371
theorem B6081425 : Blo 1600999 6081425 := bstep (se 2 (by rfl) ⟨2280534, by rfl⟩ : syracuseStep 6081425 = 4561069) B4561069
theorem B6843329 : Blo 1600999 6843329 := bstep (se 2 (by rfl) ⟨2566248, by rfl⟩ : syracuseStep 6843329 = 5132497) B5132497
theorem B2403275 : Blo 1600999 2403275 := bstep (se 1 (by rfl) ⟨1802456, by rfl⟩ : syracuseStep 2403275 = 3604913) B3604913
theorem B2403287 : Blo 1600999 2403287 := bstep (se 1 (by rfl) ⟨1802465, by rfl⟩ : syracuseStep 2403287 = 3604931) B3604931
theorem B2403353 : Blo 1600999 2403353 := bstep (se 2 (by rfl) ⟨901257, by rfl⟩ : syracuseStep 2403353 = 1802515) B1802515
theorem B5409881 : Blo 1600999 5409881 := bstep (se 2 (by rfl) ⟨2028705, by rfl⟩ : syracuseStep 5409881 = 4057411) B4057411
theorem B12987485 : Blo 1600999 12987485 := bstep (se 3 (by rfl) ⟨2435153, by rfl⟩ : syracuseStep 12987485 = 4870307) B4870307
theorem B8113283 : Blo 1600999 8113283 := bstep (se 1 (by rfl) ⟨6084962, by rfl⟩ : syracuseStep 8113283 = 12169925) B12169925
theorem B2403467 : Blo 1600999 2403467 := bstep (se 1 (by rfl) ⟨1802600, by rfl⟩ : syracuseStep 2403467 = 3605201) B3605201
theorem B51973271 : Blo 1600999 51973271 := bstep (se 1 (by rfl) ⟨38979953, by rfl⟩ : syracuseStep 51973271 = 77959907) B77959907
theorem B2403479 : Blo 1600999 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B3042497 : Blo 1600999 3042497 := bstep (se 2 (by rfl) ⟨1140936, by rfl⟩ : syracuseStep 3042497 = 2281873) B2281873
theorem B12160205 : Blo 1600999 12160205 := bstep (se 3 (by rfl) ⟨2280038, by rfl⟩ : syracuseStep 12160205 = 4560077) B4560077
theorem B2026711 : Blo 1600999 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B12332249 : Blo 1600999 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B2403545 : Blo 1600999 2403545 := bstep (se 2 (by rfl) ⟨901329, by rfl⟩ : syracuseStep 2403545 = 1802659) B1802659
theorem B3419443 : Blo 1600999 3419443 := bstep (se 1 (by rfl) ⟨2564582, by rfl⟩ : syracuseStep 3419443 = 5129165) B5129165
theorem B5557555 : Blo 1600999 5557555 := bstep (se 1 (by rfl) ⟨4168166, by rfl⟩ : syracuseStep 5557555 = 8336333) B8336333
theorem B2403659 : Blo 1600999 2403659 := bstep (se 1 (by rfl) ⟨1802744, by rfl⟩ : syracuseStep 2403659 = 3605489) B3605489
theorem B2403671 : Blo 1600999 2403671 := bstep (se 1 (by rfl) ⟨1802753, by rfl⟩ : syracuseStep 2403671 = 3605507) B3605507
theorem B5131613 : Blo 1600999 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B2403737 : Blo 1600999 2403737 := bstep (se 2 (by rfl) ⟨901401, by rfl⟩ : syracuseStep 2403737 = 1802803) B1802803
theorem B1601003 : Blo 1600999 1601003 := bstep (se 1 (by rfl) ⟨1200752, by rfl⟩ : syracuseStep 1601003 = 2401505) B2401505
theorem B1601015 : Blo 1600999 1601015 := bstep (se 1 (by rfl) ⟨1200761, by rfl⟩ : syracuseStep 1601015 = 2401523) B2401523
theorem B1601035 : Blo 1600999 1601035 := bstep (se 1 (by rfl) ⟨1200776, by rfl⟩ : syracuseStep 1601035 = 2401553) B2401553
theorem B2403851 : Blo 1600999 2403851 := bstep (se 1 (by rfl) ⟨1802888, by rfl⟩ : syracuseStep 2403851 = 3605777) B3605777
theorem B1601047 : Blo 1600999 1601047 := bstep (se 1 (by rfl) ⟨1200785, by rfl⟩ : syracuseStep 1601047 = 2401571) B2401571
theorem B2403863 : Blo 1600999 2403863 := bstep (se 1 (by rfl) ⟨1802897, by rfl⟩ : syracuseStep 2403863 = 3605795) B3605795
theorem B3042839 : Blo 1600999 3042839 := bstep (se 1 (by rfl) ⟨2282129, by rfl⟩ : syracuseStep 3042839 = 4564259) B4564259
theorem B1601067 : Blo 1600999 1601067 := bstep (se 1 (by rfl) ⟨1200800, by rfl⟩ : syracuseStep 1601067 = 2401601) B2401601
theorem B1601079 : Blo 1600999 1601079 := bstep (se 1 (by rfl) ⟨1200809, by rfl⟩ : syracuseStep 1601079 = 2401619) B2401619
theorem B1601099 : Blo 1600999 1601099 := bstep (se 1 (by rfl) ⟨1200824, by rfl⟩ : syracuseStep 1601099 = 2401649) B2401649
theorem B1601111 : Blo 1600999 1601111 := bstep (se 1 (by rfl) ⟨1200833, by rfl⟩ : syracuseStep 1601111 = 2401667) B2401667
theorem B2403929 : Blo 1600999 2403929 := bstep (se 2 (by rfl) ⟨901473, by rfl⟩ : syracuseStep 2403929 = 1802947) B1802947
theorem B1601131 : Blo 1600999 1601131 := bstep (se 1 (by rfl) ⟨1200848, by rfl⟩ : syracuseStep 1601131 = 2401697) B2401697
theorem B1601143 : Blo 1600999 1601143 := bstep (se 1 (by rfl) ⟨1200857, by rfl⟩ : syracuseStep 1601143 = 2401715) B2401715
theorem B1601163 : Blo 1600999 1601163 := bstep (se 1 (by rfl) ⟨1200872, by rfl⟩ : syracuseStep 1601163 = 2401745) B2401745
theorem B1601175 : Blo 1600999 1601175 := bstep (se 1 (by rfl) ⟨1200881, by rfl⟩ : syracuseStep 1601175 = 2401763) B2401763
theorem B6082199 : Blo 1600999 6082199 := bstep (se 1 (by rfl) ⟨4561649, by rfl⟩ : syracuseStep 6082199 = 9123299) B9123299
theorem B2887319 : Blo 1600999 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B1601195 : Blo 1600999 1601195 := bstep (se 1 (by rfl) ⟨1200896, by rfl⟩ : syracuseStep 1601195 = 2401793) B2401793
theorem B12160691 : Blo 1600999 12160691 := bstep (se 1 (by rfl) ⟨9120518, by rfl⟩ : syracuseStep 12160691 = 18241037) B18241037
theorem B1601207 : Blo 1600999 1601207 := bstep (se 1 (by rfl) ⟨1200905, by rfl⟩ : syracuseStep 1601207 = 2401811) B2401811
theorem B1601227 : Blo 1600999 1601227 := bstep (se 1 (by rfl) ⟨1200920, by rfl⟩ : syracuseStep 1601227 = 2401841) B2401841
theorem B2404043 : Blo 1600999 2404043 := bstep (se 1 (by rfl) ⟨1803032, by rfl⟩ : syracuseStep 2404043 = 3606065) B3606065
theorem B1601239 : Blo 1600999 1601239 := bstep (se 1 (by rfl) ⟨1200929, by rfl⟩ : syracuseStep 1601239 = 2401859) B2401859
theorem B2404055 : Blo 1600999 2404055 := bstep (se 1 (by rfl) ⟨1803041, by rfl⟩ : syracuseStep 2404055 = 3606083) B3606083
theorem B1601259 : Blo 1600999 1601259 := bstep (se 1 (by rfl) ⟨1200944, by rfl⟩ : syracuseStep 1601259 = 2401889) B2401889
theorem B1601271 : Blo 1600999 1601271 := bstep (se 1 (by rfl) ⟨1200953, by rfl⟩ : syracuseStep 1601271 = 2401907) B2401907
theorem B1601291 : Blo 1600999 1601291 := bstep (se 1 (by rfl) ⟨1200968, by rfl⟩ : syracuseStep 1601291 = 2401937) B2401937
theorem B6491927 : Blo 1600999 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B1601303 : Blo 1600999 1601303 := bstep (se 1 (by rfl) ⟨1200977, by rfl⟩ : syracuseStep 1601303 = 2401955) B2401955
theorem B2404121 : Blo 1600999 2404121 := bstep (se 2 (by rfl) ⟨901545, by rfl⟩ : syracuseStep 2404121 = 1803091) B1803091
theorem B1601323 : Blo 1600999 1601323 := bstep (se 1 (by rfl) ⟨1200992, by rfl⟩ : syracuseStep 1601323 = 2401985) B2401985
theorem B1601335 : Blo 1600999 1601335 := bstep (se 1 (by rfl) ⟨1201001, by rfl⟩ : syracuseStep 1601335 = 2402003) B2402003
theorem B4329281 : Blo 1600999 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B1601355 : Blo 1600999 1601355 := bstep (se 1 (by rfl) ⟨1201016, by rfl⟩ : syracuseStep 1601355 = 2402033) B2402033
theorem B1601367 : Blo 1600999 1601367 := bstep (se 1 (by rfl) ⟨1201025, by rfl⟩ : syracuseStep 1601367 = 2402051) B2402051
theorem B6082397 : Blo 1600999 6082397 := bstep (se 3 (by rfl) ⟨1140449, by rfl⟩ : syracuseStep 6082397 = 2280899) B2280899
theorem B1601387 : Blo 1600999 1601387 := bstep (se 1 (by rfl) ⟨1201040, by rfl⟩ : syracuseStep 1601387 = 2402081) B2402081
theorem B1601399 : Blo 1600999 1601399 := bstep (se 1 (by rfl) ⟨1201049, by rfl⟩ : syracuseStep 1601399 = 2402099) B2402099
theorem B1601419 : Blo 1600999 1601419 := bstep (se 1 (by rfl) ⟨1201064, by rfl⟩ : syracuseStep 1601419 = 2402129) B2402129
theorem B2404235 : Blo 1600999 2404235 := bstep (se 1 (by rfl) ⟨1803176, by rfl⟩ : syracuseStep 2404235 = 3606353) B3606353
theorem B1601431 : Blo 1600999 1601431 := bstep (se 1 (by rfl) ⟨1201073, by rfl⟩ : syracuseStep 1601431 = 2402147) B2402147
theorem B2404247 : Blo 1600999 2404247 := bstep (se 1 (by rfl) ⟨1803185, by rfl⟩ : syracuseStep 2404247 = 3606371) B3606371
theorem B1601451 : Blo 1600999 1601451 := bstep (se 1 (by rfl) ⟨1201088, by rfl⟩ : syracuseStep 1601451 = 2402177) B2402177
theorem B1601463 : Blo 1600999 1601463 := bstep (se 1 (by rfl) ⟨1201097, by rfl⟩ : syracuseStep 1601463 = 2402195) B2402195
theorem B1601483 : Blo 1600999 1601483 := bstep (se 1 (by rfl) ⟨1201112, by rfl⟩ : syracuseStep 1601483 = 2402225) B2402225
theorem B3420119 : Blo 1600999 3420119 := bstep (se 1 (by rfl) ⟨2565089, by rfl⟩ : syracuseStep 3420119 = 5130179) B5130179
theorem B1601495 : Blo 1600999 1601495 := bstep (se 1 (by rfl) ⟨1201121, by rfl⟩ : syracuseStep 1601495 = 2402243) B2402243
theorem B10268633 : Blo 1600999 10268633 := bstep (se 2 (by rfl) ⟨3850737, by rfl⟩ : syracuseStep 10268633 = 7701475) B7701475
theorem B2404313 : Blo 1600999 2404313 := bstep (se 2 (by rfl) ⟨901617, by rfl⟩ : syracuseStep 2404313 = 1803235) B1803235
theorem B1601515 : Blo 1600999 1601515 := bstep (se 1 (by rfl) ⟨1201136, by rfl⟩ : syracuseStep 1601515 = 2402273) B2402273
theorem B1601527 : Blo 1600999 1601527 := bstep (se 1 (by rfl) ⟨1201145, by rfl⟩ : syracuseStep 1601527 = 2402291) B2402291
theorem B3420161 : Blo 1600999 3420161 := bstep (se 2 (by rfl) ⟨1282560, by rfl⟩ : syracuseStep 3420161 = 2565121) B2565121
theorem B1601547 : Blo 1600999 1601547 := bstep (se 1 (by rfl) ⟨1201160, by rfl⟩ : syracuseStep 1601547 = 2402321) B2402321
theorem B2027531 : Blo 1600999 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B1601559 : Blo 1600999 1601559 := bstep (se 1 (by rfl) ⟨1201169, by rfl⟩ : syracuseStep 1601559 = 2402339) B2402339
theorem B33804323 : Blo 1600999 33804323 := bstep (se 1 (by rfl) ⟨25353242, by rfl⟩ : syracuseStep 33804323 = 50706485) B50706485
theorem B1601579 : Blo 1600999 1601579 := bstep (se 1 (by rfl) ⟨1201184, by rfl⟩ : syracuseStep 1601579 = 2402369) B2402369
theorem B1601591 : Blo 1600999 1601591 := bstep (se 1 (by rfl) ⟨1201193, by rfl⟩ : syracuseStep 1601591 = 2402387) B2402387
theorem B118452293 : Blo 1600999 118452293 := bstep (se 4 (by rfl) ⟨11104902, by rfl⟩ : syracuseStep 118452293 = 22209805) B22209805
theorem B17789003 : Blo 1600999 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B1601611 : Blo 1600999 1601611 := bstep (se 1 (by rfl) ⟨1201208, by rfl⟩ : syracuseStep 1601611 = 2402417) B2402417
theorem B2404427 : Blo 1600999 2404427 := bstep (se 1 (by rfl) ⟨1803320, by rfl⟩ : syracuseStep 2404427 = 3606641) B3606641
theorem B1601623 : Blo 1600999 1601623 := bstep (se 1 (by rfl) ⟨1201217, by rfl⟩ : syracuseStep 1601623 = 2402435) B2402435
theorem B2404439 : Blo 1600999 2404439 := bstep (se 1 (by rfl) ⟨1803329, by rfl⟩ : syracuseStep 2404439 = 3606659) B3606659
theorem B1601643 : Blo 1600999 1601643 := bstep (se 1 (by rfl) ⟨1201232, by rfl⟩ : syracuseStep 1601643 = 2402465) B2402465
theorem B1601655 : Blo 1600999 1601655 := bstep (se 1 (by rfl) ⟨1201241, by rfl⟩ : syracuseStep 1601655 = 2402483) B2402483
theorem B1601675 : Blo 1600999 1601675 := bstep (se 1 (by rfl) ⟨1201256, by rfl⟩ : syracuseStep 1601675 = 2402513) B2402513
theorem B1601687 : Blo 1600999 1601687 := bstep (se 1 (by rfl) ⟨1201265, by rfl⟩ : syracuseStep 1601687 = 2402531) B2402531
theorem B1601707 : Blo 1600999 1601707 := bstep (se 1 (by rfl) ⟨1201280, by rfl⟩ : syracuseStep 1601707 = 2402561) B2402561
theorem B1601719 : Blo 1600999 1601719 := bstep (se 1 (by rfl) ⟨1201289, by rfl⟩ : syracuseStep 1601719 = 2402579) B2402579
theorem B1601739 : Blo 1600999 1601739 := bstep (se 1 (by rfl) ⟨1201304, by rfl⟩ : syracuseStep 1601739 = 2402609) B2402609
theorem B1601751 : Blo 1600999 1601751 := bstep (se 1 (by rfl) ⟨1201313, by rfl⟩ : syracuseStep 1601751 = 2402627) B2402627
theorem B1601771 : Blo 1600999 1601771 := bstep (se 1 (by rfl) ⟨1201328, by rfl⟩ : syracuseStep 1601771 = 2402657) B2402657
theorem B1601783 : Blo 1600999 1601783 := bstep (se 1 (by rfl) ⟨1201337, by rfl⟩ : syracuseStep 1601783 = 2402675) B2402675
theorem B1601803 : Blo 1600999 1601803 := bstep (se 1 (by rfl) ⟨1201352, by rfl⟩ : syracuseStep 1601803 = 2402705) B2402705
theorem B1601815 : Blo 1600999 1601815 := bstep (se 1 (by rfl) ⟨1201361, by rfl⟩ : syracuseStep 1601815 = 2402723) B2402723
theorem B1601835 : Blo 1600999 1601835 := bstep (se 1 (by rfl) ⟨1201376, by rfl⟩ : syracuseStep 1601835 = 2402753) B2402753
theorem B1601847 : Blo 1600999 1601847 := bstep (se 1 (by rfl) ⟨1201385, by rfl⟩ : syracuseStep 1601847 = 2402771) B2402771
theorem B15012161 : Blo 1600999 15012161 := bstep (se 2 (by rfl) ⟨5629560, by rfl⟩ : syracuseStep 15012161 = 11259121) B11259121
theorem B1601867 : Blo 1600999 1601867 := bstep (se 1 (by rfl) ⟨1201400, by rfl⟩ : syracuseStep 1601867 = 2402801) B2402801
theorem B1601879 : Blo 1600999 1601879 := bstep (se 1 (by rfl) ⟨1201409, by rfl⟩ : syracuseStep 1601879 = 2402819) B2402819
theorem B1601899 : Blo 1600999 1601899 := bstep (se 1 (by rfl) ⟨1201424, by rfl⟩ : syracuseStep 1601899 = 2402849) B2402849
theorem B1601911 : Blo 1600999 1601911 := bstep (se 1 (by rfl) ⟨1201433, by rfl⟩ : syracuseStep 1601911 = 2402867) B2402867
theorem B1601931 : Blo 1600999 1601931 := bstep (se 1 (by rfl) ⟨1201448, by rfl⟩ : syracuseStep 1601931 = 2402897) B2402897
theorem B1601943 : Blo 1600999 1601943 := bstep (se 1 (by rfl) ⟨1201457, by rfl⟩ : syracuseStep 1601943 = 2402915) B2402915
theorem B1601963 : Blo 1600999 1601963 := bstep (se 1 (by rfl) ⟨1201472, by rfl⟩ : syracuseStep 1601963 = 2402945) B2402945
theorem B1601975 : Blo 1600999 1601975 := bstep (se 1 (by rfl) ⟨1201481, by rfl⟩ : syracuseStep 1601975 = 2402963) B2402963
theorem B1601995 : Blo 1600999 1601995 := bstep (se 1 (by rfl) ⟨1201496, by rfl⟩ : syracuseStep 1601995 = 2402993) B2402993
theorem B1602007 : Blo 1600999 1602007 := bstep (se 1 (by rfl) ⟨1201505, by rfl⟩ : syracuseStep 1602007 = 2403011) B2403011
theorem B1602027 : Blo 1600999 1602027 := bstep (se 1 (by rfl) ⟨1201520, by rfl⟩ : syracuseStep 1602027 = 2403041) B2403041
theorem B1602039 : Blo 1600999 1602039 := bstep (se 1 (by rfl) ⟨1201529, by rfl⟩ : syracuseStep 1602039 = 2403059) B2403059
theorem B1602059 : Blo 1600999 1602059 := bstep (se 1 (by rfl) ⟨1201544, by rfl⟩ : syracuseStep 1602059 = 2403089) B2403089
theorem B1602071 : Blo 1600999 1602071 := bstep (se 1 (by rfl) ⟨1201553, by rfl⟩ : syracuseStep 1602071 = 2403107) B2403107
theorem B1602091 : Blo 1600999 1602091 := bstep (se 1 (by rfl) ⟨1201568, by rfl⟩ : syracuseStep 1602091 = 2403137) B2403137
theorem B1602103 : Blo 1600999 1602103 := bstep (se 1 (by rfl) ⟨1201577, by rfl⟩ : syracuseStep 1602103 = 2403155) B2403155
theorem B1602123 : Blo 1600999 1602123 := bstep (se 1 (by rfl) ⟨1201592, by rfl⟩ : syracuseStep 1602123 = 2403185) B2403185
theorem B1602135 : Blo 1600999 1602135 := bstep (se 1 (by rfl) ⟨1201601, by rfl⟩ : syracuseStep 1602135 = 2403203) B2403203
theorem B1602155 : Blo 1600999 1602155 := bstep (se 1 (by rfl) ⟨1201616, by rfl⟩ : syracuseStep 1602155 = 2403233) B2403233
theorem B1602167 : Blo 1600999 1602167 := bstep (se 1 (by rfl) ⟨1201625, by rfl⟩ : syracuseStep 1602167 = 2403251) B2403251
theorem B1602187 : Blo 1600999 1602187 := bstep (se 1 (by rfl) ⟨1201640, by rfl⟩ : syracuseStep 1602187 = 2403281) B2403281
theorem B1602199 : Blo 1600999 1602199 := bstep (se 1 (by rfl) ⟨1201649, by rfl⟩ : syracuseStep 1602199 = 2403299) B2403299
theorem B1602219 : Blo 1600999 1602219 := bstep (se 1 (by rfl) ⟨1201664, by rfl⟩ : syracuseStep 1602219 = 2403329) B2403329
theorem B1602231 : Blo 1600999 1602231 := bstep (se 1 (by rfl) ⟨1201673, by rfl⟩ : syracuseStep 1602231 = 2403347) B2403347
theorem B1602251 : Blo 1600999 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B2028235 : Blo 1600999 2028235 := bstep (se 1 (by rfl) ⟨1521176, by rfl⟩ : syracuseStep 2028235 = 3042353) B3042353
theorem B1602263 : Blo 1600999 1602263 := bstep (se 1 (by rfl) ⟨1201697, by rfl⟩ : syracuseStep 1602263 = 2403395) B2403395
theorem B1602283 : Blo 1600999 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1602295 : Blo 1600999 1602295 := bstep (se 1 (by rfl) ⟨1201721, by rfl⟩ : syracuseStep 1602295 = 2403443) B2403443
theorem B1602315 : Blo 1600999 1602315 := bstep (se 1 (by rfl) ⟨1201736, by rfl⟩ : syracuseStep 1602315 = 2403473) B2403473
theorem B1602327 : Blo 1600999 1602327 := bstep (se 1 (by rfl) ⟨1201745, by rfl⟩ : syracuseStep 1602327 = 2403491) B2403491
theorem B1602347 : Blo 1600999 1602347 := bstep (se 1 (by rfl) ⟨1201760, by rfl⟩ : syracuseStep 1602347 = 2403521) B2403521
theorem B93696821 : Blo 1600999 93696821 := bstep (se 5 (by rfl) ⟨4392038, by rfl⟩ : syracuseStep 93696821 = 8784077) B8784077
theorem B1602359 : Blo 1600999 1602359 := bstep (se 1 (by rfl) ⟨1201769, by rfl⟩ : syracuseStep 1602359 = 2403539) B2403539
theorem B1602379 : Blo 1600999 1602379 := bstep (se 1 (by rfl) ⟨1201784, by rfl⟩ : syracuseStep 1602379 = 2403569) B2403569
theorem B1602391 : Blo 1600999 1602391 := bstep (se 1 (by rfl) ⟨1201793, by rfl⟩ : syracuseStep 1602391 = 2403587) B2403587
theorem B1602411 : Blo 1600999 1602411 := bstep (se 1 (by rfl) ⟨1201808, by rfl⟩ : syracuseStep 1602411 = 2403617) B2403617
theorem B1602423 : Blo 1600999 1602423 := bstep (se 1 (by rfl) ⟨1201817, by rfl⟩ : syracuseStep 1602423 = 2403635) B2403635
theorem B1602443 : Blo 1600999 1602443 := bstep (se 1 (by rfl) ⟨1201832, by rfl⟩ : syracuseStep 1602443 = 2403665) B2403665
theorem B1602455 : Blo 1600999 1602455 := bstep (se 1 (by rfl) ⟨1201841, by rfl⟩ : syracuseStep 1602455 = 2403683) B2403683
theorem B1602475 : Blo 1600999 1602475 := bstep (se 1 (by rfl) ⟨1201856, by rfl⟩ : syracuseStep 1602475 = 2403713) B2403713
theorem B1602487 : Blo 1600999 1602487 := bstep (se 1 (by rfl) ⟨1201865, by rfl⟩ : syracuseStep 1602487 = 2403731) B2403731
theorem B1602507 : Blo 1600999 1602507 := bstep (se 1 (by rfl) ⟨1201880, by rfl⟩ : syracuseStep 1602507 = 2403761) B2403761
theorem B1602519 : Blo 1600999 1602519 := bstep (se 1 (by rfl) ⟨1201889, by rfl⟩ : syracuseStep 1602519 = 2403779) B2403779
theorem B2028503 : Blo 1600999 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B51958745 : Blo 1600999 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B1602539 : Blo 1600999 1602539 := bstep (se 1 (by rfl) ⟨1201904, by rfl⟩ : syracuseStep 1602539 = 2403809) B2403809
theorem B1602551 : Blo 1600999 1602551 := bstep (se 1 (by rfl) ⟨1201913, by rfl⟩ : syracuseStep 1602551 = 2403827) B2403827
theorem B1602571 : Blo 1600999 1602571 := bstep (se 1 (by rfl) ⟨1201928, by rfl⟩ : syracuseStep 1602571 = 2403857) B2403857
theorem B5403671 : Blo 1600999 5403671 := bstep (se 1 (by rfl) ⟨4052753, by rfl⟩ : syracuseStep 5403671 = 8105507) B8105507
theorem B1602583 : Blo 1600999 1602583 := bstep (se 1 (by rfl) ⟨1201937, by rfl⟩ : syracuseStep 1602583 = 2403875) B2403875
theorem B1602603 : Blo 1600999 1602603 := bstep (se 1 (by rfl) ⟨1201952, by rfl⟩ : syracuseStep 1602603 = 2403905) B2403905
theorem B1602615 : Blo 1600999 1602615 := bstep (se 1 (by rfl) ⟨1201961, by rfl⟩ : syracuseStep 1602615 = 2403923) B2403923
theorem B1602635 : Blo 1600999 1602635 := bstep (se 1 (by rfl) ⟨1201976, by rfl⟩ : syracuseStep 1602635 = 2403953) B2403953
theorem B1602647 : Blo 1600999 1602647 := bstep (se 1 (by rfl) ⟨1201985, by rfl⟩ : syracuseStep 1602647 = 2403971) B2403971
theorem B12162149 : Blo 1600999 12162149 := bstep (se 4 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 12162149 = 2280403) B2280403
theorem B1602667 : Blo 1600999 1602667 := bstep (se 1 (by rfl) ⟨1202000, by rfl⟩ : syracuseStep 1602667 = 2404001) B2404001
theorem B1602679 : Blo 1600999 1602679 := bstep (se 1 (by rfl) ⟨1202009, by rfl⟩ : syracuseStep 1602679 = 2404019) B2404019
theorem B1602699 : Blo 1600999 1602699 := bstep (se 1 (by rfl) ⟨1202024, by rfl⟩ : syracuseStep 1602699 = 2404049) B2404049
theorem B1602711 : Blo 1600999 1602711 := bstep (se 1 (by rfl) ⟨1202033, by rfl⟩ : syracuseStep 1602711 = 2404067) B2404067
theorem B3249305 : Blo 1600999 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B1602731 : Blo 1600999 1602731 := bstep (se 1 (by rfl) ⟨1202048, by rfl⟩ : syracuseStep 1602731 = 2404097) B2404097
theorem B6165677 : Blo 1600999 6165677 := bstep (se 3 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 6165677 = 2312129) B2312129
theorem B1602743 : Blo 1600999 1602743 := bstep (se 1 (by rfl) ⟨1202057, by rfl⟩ : syracuseStep 1602743 = 2404115) B2404115
theorem B1602763 : Blo 1600999 1602763 := bstep (se 1 (by rfl) ⟨1202072, by rfl⟩ : syracuseStep 1602763 = 2404145) B2404145
theorem B1602775 : Blo 1600999 1602775 := bstep (se 1 (by rfl) ⟨1202081, by rfl⟩ : syracuseStep 1602775 = 2404163) B2404163
theorem B1602795 : Blo 1600999 1602795 := bstep (se 1 (by rfl) ⟨1202096, by rfl⟩ : syracuseStep 1602795 = 2404193) B2404193
theorem B1602807 : Blo 1600999 1602807 := bstep (se 1 (by rfl) ⟨1202105, by rfl⟩ : syracuseStep 1602807 = 2404211) B2404211
theorem B1602827 : Blo 1600999 1602827 := bstep (se 1 (by rfl) ⟨1202120, by rfl⟩ : syracuseStep 1602827 = 2404241) B2404241
theorem B1602839 : Blo 1600999 1602839 := bstep (se 1 (by rfl) ⟨1202129, by rfl⟩ : syracuseStep 1602839 = 2404259) B2404259
theorem B1602859 : Blo 1600999 1602859 := bstep (se 1 (by rfl) ⟨1202144, by rfl⟩ : syracuseStep 1602859 = 2404289) B2404289
theorem B1602871 : Blo 1600999 1602871 := bstep (se 1 (by rfl) ⟨1202153, by rfl⟩ : syracuseStep 1602871 = 2404307) B2404307
theorem B1602891 : Blo 1600999 1602891 := bstep (se 1 (by rfl) ⟨1202168, by rfl⟩ : syracuseStep 1602891 = 2404337) B2404337
theorem B1602903 : Blo 1600999 1602903 := bstep (se 1 (by rfl) ⟨1202177, by rfl⟩ : syracuseStep 1602903 = 2404355) B2404355
theorem B6845789 : Blo 1600999 6845789 := bstep (se 3 (by rfl) ⟨1283585, by rfl⟩ : syracuseStep 6845789 = 2567171) B2567171
theorem B1602923 : Blo 1600999 1602923 := bstep (se 1 (by rfl) ⟨1202192, by rfl⟩ : syracuseStep 1602923 = 2404385) B2404385
theorem B1602935 : Blo 1600999 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B1602955 : Blo 1600999 1602955 := bstep (se 1 (by rfl) ⟨1202216, by rfl⟩ : syracuseStep 1602955 = 2404433) B2404433
theorem B1602967 : Blo 1600999 1602967 := bstep (se 1 (by rfl) ⟨1202225, by rfl⟩ : syracuseStep 1602967 = 2404451) B2404451
theorem B1602987 : Blo 1600999 1602987 := bstep (se 1 (by rfl) ⟨1202240, by rfl⟩ : syracuseStep 1602987 = 2404481) B2404481
theorem B1602999 : Blo 1600999 1602999 := bstep (se 1 (by rfl) ⟨1202249, by rfl⟩ : syracuseStep 1602999 = 2404499) B2404499
theorem B4052531 : Blo 1600999 4052531 := bstep (se 1 (by rfl) ⟨3039398, by rfl⟩ : syracuseStep 4052531 = 6078797) B6078797
theorem B5404211 : Blo 1600999 5404211 := bstep (se 1 (by rfl) ⟨4053158, by rfl⟩ : syracuseStep 5404211 = 8106317) B8106317
theorem B10270273 : Blo 1600999 10270273 := bstep (se 2 (by rfl) ⟨3851352, by rfl⟩ : syracuseStep 10270273 = 7702705) B7702705
theorem B12162635 : Blo 1600999 12162635 := bstep (se 1 (by rfl) ⟨9121976, by rfl⟩ : syracuseStep 12162635 = 18243953) B18243953
theorem B8107613 : Blo 1600999 8107613 := bstep (se 3 (by rfl) ⟨1520177, by rfl⟩ : syracuseStep 8107613 = 3040355) B3040355
theorem B15398531 : Blo 1600999 15398531 := bstep (se 1 (by rfl) ⟨11548898, by rfl⟩ : syracuseStep 15398531 = 23097797) B23097797
theorem B25990787 : Blo 1600999 25990787 := bstep (se 1 (by rfl) ⟨19493090, by rfl⟩ : syracuseStep 25990787 = 38986181) B38986181
theorem B6493841 : Blo 1600999 6493841 := bstep (se 2 (by rfl) ⟨2435190, by rfl⟩ : syracuseStep 6493841 = 4870381) B4870381
theorem B3847873 : Blo 1600999 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B6084355 : Blo 1600999 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B1709867 : Blo 1600999 1709867 := bstep (se 1 (by rfl) ⟨1282400, by rfl⟩ : syracuseStep 1709867 = 2564801) B2564801
theorem B5404481 : Blo 1600999 5404481 := bstep (se 2 (by rfl) ⟨2026680, by rfl⟩ : syracuseStep 5404481 = 4053361) B4053361
theorem B4560715 : Blo 1600999 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B4052825 : Blo 1600999 4052825 := bstep (se 2 (by rfl) ⟨1519809, by rfl⟩ : syracuseStep 4052825 = 3039619) B3039619
theorem B1709995 : Blo 1600999 1709995 := bstep (se 1 (by rfl) ⟨1282496, by rfl⟩ : syracuseStep 1709995 = 2564993) B2564993
theorem B3602393 : Blo 1600999 3602393 := bstep (se 2 (by rfl) ⟨1350897, by rfl⟩ : syracuseStep 3602393 = 2701795) B2701795
theorem B15398873 : Blo 1600999 15398873 := bstep (se 2 (by rfl) ⟨5774577, by rfl⟩ : syracuseStep 15398873 = 11549155) B11549155
theorem B3602483 : Blo 1600999 3602483 := bstep (se 1 (by rfl) ⟨2701862, by rfl⟩ : syracuseStep 3602483 = 5403725) B5403725
theorem B6084659 : Blo 1600999 6084659 := bstep (se 1 (by rfl) ⟨4563494, by rfl⟩ : syracuseStep 6084659 = 9126989) B9126989
theorem B3602519 : Blo 1600999 3602519 := bstep (se 1 (by rfl) ⟨2701889, by rfl⟩ : syracuseStep 3602519 = 5403779) B5403779
theorem B4331713 : Blo 1600999 4331713 := bstep (se 2 (by rfl) ⟨1624392, by rfl⟩ : syracuseStep 4331713 = 3248785) B3248785
theorem B12990725 : Blo 1600999 12990725 := bstep (se 4 (by rfl) ⟨1217880, by rfl⟩ : syracuseStep 12990725 = 2435761) B2435761
theorem B3602699 : Blo 1600999 3602699 := bstep (se 1 (by rfl) ⟨2702024, by rfl⟩ : syracuseStep 3602699 = 5404049) B5404049
theorem B13678865 : Blo 1600999 13678865 := bstep (se 2 (by rfl) ⟨5129574, by rfl⟩ : syracuseStep 13678865 = 10259149) B10259149
theorem B3602753 : Blo 1600999 3602753 := bstep (se 2 (by rfl) ⟨1351032, by rfl⟩ : syracuseStep 3602753 = 2702065) B2702065
theorem B4561217 : Blo 1600999 4561217 := bstep (se 2 (by rfl) ⟨1710456, by rfl⟩ : syracuseStep 4561217 = 3420913) B3420913
theorem B3651929 : Blo 1600999 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B5405021 : Blo 1600999 5405021 := bstep (se 3 (by rfl) ⟨1013441, by rfl⟩ : syracuseStep 5405021 = 2026883) B2026883
theorem B94959985 : Blo 1600999 94959985 := bstep (se 2 (by rfl) ⟨35609994, by rfl⟩ : syracuseStep 94959985 = 71219989) B71219989
theorem B6936977 : Blo 1600999 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B48085397 : Blo 1600999 48085397 := bstep (se 6 (by rfl) ⟨1127001, by rfl⟩ : syracuseStep 48085397 = 2254003) B2254003
theorem B2701721 : Blo 1600999 2701721 := bstep (se 2 (by rfl) ⟨1013145, by rfl⟩ : syracuseStep 2701721 = 2026291) B2026291
theorem B5773771 : Blo 1600999 5773771 := bstep (se 1 (by rfl) ⟨4330328, by rfl⟩ : syracuseStep 5773771 = 8660657) B8660657
theorem B7305751 : Blo 1600999 7305751 := bstep (se 1 (by rfl) ⟨5479313, by rfl⟩ : syracuseStep 7305751 = 10958627) B10958627
theorem B2701849 : Blo 1600999 2701849 := bstep (se 2 (by rfl) ⟨1013193, by rfl⟩ : syracuseStep 2701849 = 2026387) B2026387
theorem B3602969 : Blo 1600999 3602969 := bstep (se 2 (by rfl) ⟨1351113, by rfl⟩ : syracuseStep 3602969 = 2702227) B2702227
theorem B12171869 : Blo 1600999 12171869 := bstep (se 3 (by rfl) ⟨2282225, by rfl⟩ : syracuseStep 12171869 = 4564451) B4564451
theorem B3603059 : Blo 1600999 3603059 := bstep (se 1 (by rfl) ⟨2702294, by rfl⟩ : syracuseStep 3603059 = 5404589) B5404589
theorem B3603095 : Blo 1600999 3603095 := bstep (se 1 (by rfl) ⟨2702321, by rfl⟩ : syracuseStep 3603095 = 5404643) B5404643
theorem B4561559 : Blo 1600999 4561559 := bstep (se 1 (by rfl) ⟨3421169, by rfl⟩ : syracuseStep 4561559 = 6842339) B6842339
theorem B5774003 : Blo 1600999 5774003 := bstep (se 1 (by rfl) ⟨4330502, by rfl⟩ : syracuseStep 5774003 = 8661005) B8661005
theorem B27368117 : Blo 1600999 27368117 := bstep (se 5 (by rfl) ⟨1282880, by rfl⟩ : syracuseStep 27368117 = 2565761) B2565761
theorem B6085313 : Blo 1600999 6085313 := bstep (se 2 (by rfl) ⟨2281992, by rfl⟩ : syracuseStep 6085313 = 4563985) B4563985
theorem B14809817 : Blo 1600999 14809817 := bstep (se 2 (by rfl) ⟨5553681, by rfl⟩ : syracuseStep 14809817 = 11107363) B11107363
theorem B4111127 : Blo 1600999 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B18758465 : Blo 1600999 18758465 := bstep (se 2 (by rfl) ⟨7034424, by rfl⟩ : syracuseStep 18758465 = 14068849) B14068849
theorem B3603275 : Blo 1600999 3603275 := bstep (se 1 (by rfl) ⟨2702456, by rfl⟩ : syracuseStep 3603275 = 5404913) B5404913
theorem B3423065 : Blo 1600999 3423065 := bstep (se 2 (by rfl) ⟨1283649, by rfl⟩ : syracuseStep 3423065 = 2567299) B2567299
theorem B3603329 : Blo 1600999 3603329 := bstep (se 2 (by rfl) ⟨1351248, by rfl⟩ : syracuseStep 3603329 = 2702497) B2702497
theorem B19479473 : Blo 1600999 19479473 := bstep (se 2 (by rfl) ⟨7304802, by rfl⟩ : syracuseStep 19479473 = 14609605) B14609605
theorem B4332491 : Blo 1600999 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B1801291 : Blo 1600999 1801291 := bstep (se 1 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 1801291 = 2701937) B2701937
theorem B10959947 : Blo 1600999 10959947 := bstep (se 1 (by rfl) ⟨8219960, by rfl⟩ : syracuseStep 10959947 = 16439921) B16439921
theorem B2702423 : Blo 1600999 2702423 := bstep (se 1 (by rfl) ⟨2026817, by rfl⟩ : syracuseStep 2702423 = 4053635) B4053635
theorem B3603545 : Blo 1600999 3603545 := bstep (se 2 (by rfl) ⟨1351329, by rfl⟩ : syracuseStep 3603545 = 2702659) B2702659
theorem B10402967 : Blo 1600999 10402967 := bstep (se 1 (by rfl) ⟨7802225, by rfl⟩ : syracuseStep 10402967 = 15604451) B15604451
theorem B3603635 : Blo 1600999 3603635 := bstep (se 1 (by rfl) ⟨2702726, by rfl⟩ : syracuseStep 3603635 = 5405453) B5405453
theorem B1801399 : Blo 1600999 1801399 := bstep (se 1 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 1801399 = 2702099) B2702099
theorem B2702551 : Blo 1600999 2702551 := bstep (se 1 (by rfl) ⟨2026913, by rfl⟩ : syracuseStep 2702551 = 4053827) B4053827
theorem B3603671 : Blo 1600999 3603671 := bstep (se 1 (by rfl) ⟨2702753, by rfl⟩ : syracuseStep 3603671 = 5405507) B5405507
theorem B8215769 : Blo 1600999 8215769 := bstep (se 2 (by rfl) ⟨3080913, by rfl⟩ : syracuseStep 8215769 = 6161827) B6161827
theorem B3423475 : Blo 1600999 3423475 := bstep (se 1 (by rfl) ⟨2567606, by rfl⟩ : syracuseStep 3423475 = 5135213) B5135213
theorem B6839569 : Blo 1600999 6839569 := bstep (se 2 (by rfl) ⟨2564838, by rfl⟩ : syracuseStep 6839569 = 5129677) B5129677
theorem B1801579 : Blo 1600999 1801579 := bstep (se 1 (by rfl) ⟨1351184, by rfl⟩ : syracuseStep 1801579 = 2702369) B2702369
theorem B5774723 : Blo 1600999 5774723 := bstep (se 1 (by rfl) ⟨4331042, by rfl⟩ : syracuseStep 5774723 = 8662085) B8662085
theorem B3603851 : Blo 1600999 3603851 := bstep (se 1 (by rfl) ⟨2702888, by rfl⟩ : syracuseStep 3603851 = 5405777) B5405777
theorem B3603905 : Blo 1600999 3603905 := bstep (se 2 (by rfl) ⟨1351464, by rfl⟩ : syracuseStep 3603905 = 2702929) B2702929
theorem B4054475 : Blo 1600999 4054475 := bstep (se 1 (by rfl) ⟨3040856, by rfl⟩ : syracuseStep 4054475 = 6081713) B6081713
theorem B5406155 : Blo 1600999 5406155 := bstep (se 1 (by rfl) ⟨4054616, by rfl⟩ : syracuseStep 5406155 = 8109233) B8109233
theorem B1801687 : Blo 1600999 1801687 := bstep (se 1 (by rfl) ⟨1351265, by rfl⟩ : syracuseStep 1801687 = 2702531) B2702531
theorem B6250007 : Blo 1600999 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B1801867 : Blo 1600999 1801867 := bstep (se 1 (by rfl) ⟨1351400, by rfl⟩ : syracuseStep 1801867 = 2702801) B2702801
theorem B8109719 : Blo 1600999 8109719 := bstep (se 1 (by rfl) ⟨6082289, by rfl⟩ : syracuseStep 8109719 = 12164579) B12164579
theorem B3604121 : Blo 1600999 3604121 := bstep (se 2 (by rfl) ⟨1351545, by rfl⟩ : syracuseStep 3604121 = 2703091) B2703091
theorem B5406425 : Blo 1600999 5406425 := bstep (se 2 (by rfl) ⟨2027409, by rfl⟩ : syracuseStep 5406425 = 4054819) B4054819
theorem B3604211 : Blo 1600999 3604211 := bstep (se 1 (by rfl) ⟨2703158, by rfl⟩ : syracuseStep 3604211 = 5406317) B5406317
theorem B1801975 : Blo 1600999 1801975 := bstep (se 1 (by rfl) ⟨1351481, by rfl⟩ : syracuseStep 1801975 = 2702963) B2702963
theorem B3604247 : Blo 1600999 3604247 := bstep (se 1 (by rfl) ⟨2703185, by rfl⟩ : syracuseStep 3604247 = 5406371) B5406371
theorem B2703179 : Blo 1600999 2703179 := bstep (se 1 (by rfl) ⟨2027384, by rfl⟩ : syracuseStep 2703179 = 4054769) B4054769
theorem B11550539 : Blo 1600999 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B9125783 : Blo 1600999 9125783 := bstep (se 1 (by rfl) ⟨6844337, by rfl⟩ : syracuseStep 9125783 = 13688675) B13688675
theorem B1802155 : Blo 1600999 1802155 := bstep (se 1 (by rfl) ⟨1351616, by rfl⟩ : syracuseStep 1802155 = 2703233) B2703233
theorem B2703307 : Blo 1600999 2703307 := bstep (se 1 (by rfl) ⟨2027480, by rfl⟩ : syracuseStep 2703307 = 4054961) B4054961
theorem B3604427 : Blo 1600999 3604427 := bstep (se 1 (by rfl) ⟨2703320, by rfl⟩ : syracuseStep 3604427 = 5406641) B5406641
theorem B4874201 : Blo 1600999 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B22536215 : Blo 1600999 22536215 := bstep (se 1 (by rfl) ⟨16902161, by rfl⟩ : syracuseStep 22536215 = 33804323) B33804323
theorem B5406749 : Blo 1600999 5406749 := bstep (se 3 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 5406749 = 2027531) B2027531
theorem B4874273 : Blo 1600999 4874273 := bstep (se 2 (by rfl) ⟨1827852, by rfl⟩ : syracuseStep 4874273 = 3655705) B3655705
theorem B3702827 : Blo 1600999 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B1802299 : Blo 1600999 1802299 := bstep (se 1 (by rfl) ⟨1351724, by rfl⟩ : syracuseStep 1802299 = 2703449) B2703449
theorem B5775617 : Blo 1600999 5775617 := bstep (se 2 (by rfl) ⟨2165856, by rfl⟩ : syracuseStep 5775617 = 4331713) B4331713
theorem B3604751 : Blo 1600999 3604751 := bstep (se 1 (by rfl) ⟨2703563, by rfl⟩ : syracuseStep 3604751 = 5407127) B5407127
theorem B2703631 : Blo 1600999 2703631 := bstep (se 1 (by rfl) ⟨2027723, by rfl⟩ : syracuseStep 2703631 = 4055447) B4055447
theorem B3604769 : Blo 1600999 3604769 := bstep (se 2 (by rfl) ⟨1351788, by rfl⟩ : syracuseStep 3604769 = 2703577) B2703577
theorem B16441805 : Blo 1600999 16441805 := bstep (se 3 (by rfl) ⟨3082838, by rfl⟩ : syracuseStep 16441805 = 6165677) B6165677
theorem B1802767 : Blo 1600999 1802767 := bstep (se 1 (by rfl) ⟨1352075, by rfl⟩ : syracuseStep 1802767 = 2704151) B2704151
theorem B62464547 : Blo 1600999 62464547 := bstep (se 1 (by rfl) ⟨46848410, by rfl⟩ : syracuseStep 62464547 = 93696821) B93696821
theorem B3605111 : Blo 1600999 3605111 := bstep (se 1 (by rfl) ⟨2703833, by rfl⟩ : syracuseStep 3605111 = 5407667) B5407667
theorem B9741001 : Blo 1600999 9741001 := bstep (se 2 (by rfl) ⟨3652875, by rfl⟩ : syracuseStep 9741001 = 7305751) B7305751
theorem B3605291 : Blo 1600999 3605291 := bstep (se 1 (by rfl) ⟨2703968, by rfl⟩ : syracuseStep 3605291 = 5407937) B5407937
theorem B2704171 : Blo 1600999 2704171 := bstep (se 1 (by rfl) ⟨2028128, by rfl⟩ : syracuseStep 2704171 = 4056257) B4056257
theorem B9126715 : Blo 1600999 9126715 := bstep (se 1 (by rfl) ⟨6845036, by rfl⟩ : syracuseStep 9126715 = 13690073) B13690073
theorem B4563859 : Blo 1600999 4563859 := bstep (se 1 (by rfl) ⟨3422894, by rfl⟩ : syracuseStep 4563859 = 6845789) B6845789
theorem B2704313 : Blo 1600999 2704313 := bstep (se 2 (by rfl) ⟨1014117, by rfl⟩ : syracuseStep 2704313 = 2028235) B2028235
theorem B4056065 : Blo 1600999 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B1803271 : Blo 1600999 1803271 := bstep (se 1 (by rfl) ⟨1352453, by rfl⟩ : syracuseStep 1803271 = 2704907) B2704907
theorem B10265687 : Blo 1600999 10265687 := bstep (se 1 (by rfl) ⟨7699265, by rfl⟩ : syracuseStep 10265687 = 15398531) B15398531
theorem B17327191 : Blo 1600999 17327191 := bstep (se 1 (by rfl) ⟨12995393, by rfl⟩ : syracuseStep 17327191 = 25990787) B25990787
theorem B3605651 : Blo 1600999 3605651 := bstep (se 1 (by rfl) ⟨2704238, by rfl⟩ : syracuseStep 3605651 = 5408477) B5408477
theorem B3605705 : Blo 1600999 3605705 := bstep (se 2 (by rfl) ⟨1352139, by rfl⟩ : syracuseStep 3605705 = 2704279) B2704279
theorem B15402221 : Blo 1600999 15402221 := bstep (se 3 (by rfl) ⟨2887916, by rfl⟩ : syracuseStep 15402221 = 5775833) B5775833
theorem B15402257 : Blo 1600999 15402257 := bstep (se 2 (by rfl) ⟨5775846, by rfl⟩ : syracuseStep 15402257 = 11551693) B11551693
theorem B2401595 : Blo 1600999 2401595 := bstep (se 1 (by rfl) ⟨1801196, by rfl⟩ : syracuseStep 2401595 = 3602393) B3602393
theorem B10265915 : Blo 1600999 10265915 := bstep (se 1 (by rfl) ⟨7699436, by rfl⟩ : syracuseStep 10265915 = 15398873) B15398873
theorem B2401655 : Blo 1600999 2401655 := bstep (se 1 (by rfl) ⟨1801241, by rfl⟩ : syracuseStep 2401655 = 3602483) B3602483
theorem B4056439 : Blo 1600999 4056439 := bstep (se 1 (by rfl) ⟨3042329, by rfl⟩ : syracuseStep 4056439 = 6084659) B6084659
theorem B2401679 : Blo 1600999 2401679 := bstep (se 1 (by rfl) ⟨1801259, by rfl⟩ : syracuseStep 2401679 = 3602519) B3602519
theorem B5408153 : Blo 1600999 5408153 := bstep (se 2 (by rfl) ⟨2028057, by rfl⟩ : syracuseStep 5408153 = 4056115) B4056115
theorem B2401721 : Blo 1600999 2401721 := bstep (se 2 (by rfl) ⟨900645, by rfl⟩ : syracuseStep 2401721 = 1801291) B1801291
theorem B8660483 : Blo 1600999 8660483 := bstep (se 1 (by rfl) ⟨6495362, by rfl⟩ : syracuseStep 8660483 = 12990725) B12990725
theorem B2401799 : Blo 1600999 2401799 := bstep (se 1 (by rfl) ⟨1801349, by rfl⟩ : syracuseStep 2401799 = 3602699) B3602699
theorem B9119243 : Blo 1600999 9119243 := bstep (se 1 (by rfl) ⟨6839432, by rfl⟩ : syracuseStep 9119243 = 13678865) B13678865
theorem B2401835 : Blo 1600999 2401835 := bstep (se 1 (by rfl) ⟨1801376, by rfl⟩ : syracuseStep 2401835 = 3602753) B3602753
theorem B3040811 : Blo 1600999 3040811 := bstep (se 1 (by rfl) ⟨2280608, by rfl⟩ : syracuseStep 3040811 = 4561217) B4561217
theorem B2434619 : Blo 1600999 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B2401865 : Blo 1600999 2401865 := bstep (se 2 (by rfl) ⟨900699, by rfl⟩ : syracuseStep 2401865 = 1801399) B1801399
theorem B32056931 : Blo 1600999 32056931 := bstep (se 1 (by rfl) ⟨24042698, by rfl⟩ : syracuseStep 32056931 = 48085397) B48085397
theorem B29640293 : Blo 1600999 29640293 := bstep (se 4 (by rfl) ⟨2778777, by rfl⟩ : syracuseStep 29640293 = 5557555) B5557555
theorem B2705015 : Blo 1600999 2705015 := bstep (se 1 (by rfl) ⟨2028761, by rfl⟩ : syracuseStep 2705015 = 4057523) B4057523
theorem B2401979 : Blo 1600999 2401979 := bstep (se 1 (by rfl) ⟨1801484, by rfl⟩ : syracuseStep 2401979 = 3602969) B3602969
theorem B9119425 : Blo 1600999 9119425 := bstep (se 2 (by rfl) ⟨3419784, by rfl⟩ : syracuseStep 9119425 = 6839569) B6839569
theorem B2402039 : Blo 1600999 2402039 := bstep (se 1 (by rfl) ⟨1801529, by rfl⟩ : syracuseStep 2402039 = 3603059) B3603059
theorem B35096321 : Blo 1600999 35096321 := bstep (se 2 (by rfl) ⟨13161120, by rfl⟩ : syracuseStep 35096321 = 26322241) B26322241
theorem B2402063 : Blo 1600999 2402063 := bstep (se 1 (by rfl) ⟨1801547, by rfl⟩ : syracuseStep 2402063 = 3603095) B3603095
theorem B3041039 : Blo 1600999 3041039 := bstep (se 1 (by rfl) ⟨2280779, by rfl⟩ : syracuseStep 3041039 = 4561559) B4561559
theorem B18245411 : Blo 1600999 18245411 := bstep (se 1 (by rfl) ⟨13684058, by rfl⟩ : syracuseStep 18245411 = 27368117) B27368117
theorem B4056875 : Blo 1600999 4056875 := bstep (se 1 (by rfl) ⟨3042656, by rfl⟩ : syracuseStep 4056875 = 6085313) B6085313
theorem B2402105 : Blo 1600999 2402105 := bstep (se 2 (by rfl) ⟨900789, by rfl⟩ : syracuseStep 2402105 = 1801579) B1801579
theorem B8111987 : Blo 1600999 8111987 := bstep (se 1 (by rfl) ⟨6083990, by rfl⟩ : syracuseStep 8111987 = 12167981) B12167981
theorem B2402183 : Blo 1600999 2402183 := bstep (se 1 (by rfl) ⟨1801637, by rfl⟩ : syracuseStep 2402183 = 3603275) B3603275
theorem B3606407 : Blo 1600999 3606407 := bstep (se 1 (by rfl) ⟨2704805, by rfl⟩ : syracuseStep 3606407 = 5409611) B5409611
theorem B2402219 : Blo 1600999 2402219 := bstep (se 1 (by rfl) ⟨1801664, by rfl⟩ : syracuseStep 2402219 = 3603329) B3603329
theorem B2402249 : Blo 1600999 2402249 := bstep (se 2 (by rfl) ⟨900843, by rfl⟩ : syracuseStep 2402249 = 1801687) B1801687
theorem B12986315 : Blo 1600999 12986315 := bstep (se 1 (by rfl) ⟨9739736, by rfl⟩ : syracuseStep 12986315 = 19479473) B19479473
theorem B2402363 : Blo 1600999 2402363 := bstep (se 1 (by rfl) ⟨1801772, by rfl⟩ : syracuseStep 2402363 = 3603545) B3603545
theorem B3606587 : Blo 1600999 3606587 := bstep (se 1 (by rfl) ⟨2704940, by rfl⟩ : syracuseStep 3606587 = 5409881) B5409881
theorem B5408855 : Blo 1600999 5408855 := bstep (se 1 (by rfl) ⟨4056641, by rfl⟩ : syracuseStep 5408855 = 8113283) B8113283
theorem B2402423 : Blo 1600999 2402423 := bstep (se 1 (by rfl) ⟨1801817, by rfl⟩ : syracuseStep 2402423 = 3603635) B3603635
theorem B2402447 : Blo 1600999 2402447 := bstep (se 1 (by rfl) ⟨1801835, by rfl⟩ : syracuseStep 2402447 = 3603671) B3603671
theorem B2402489 : Blo 1600999 2402489 := bstep (se 2 (by rfl) ⟨900933, by rfl⟩ : syracuseStep 2402489 = 1801867) B1801867
theorem B3606713 : Blo 1600999 3606713 := bstep (se 2 (by rfl) ⟨1352517, by rfl⟩ : syracuseStep 3606713 = 2705035) B2705035
theorem B9128173 : Blo 1600999 9128173 := bstep (se 3 (by rfl) ⟨1711532, by rfl⟩ : syracuseStep 9128173 = 3423065) B3423065
theorem B5130497 : Blo 1600999 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B2402567 : Blo 1600999 2402567 := bstep (se 1 (by rfl) ⟨1801925, by rfl⟩ : syracuseStep 2402567 = 3603851) B3603851
theorem B2402603 : Blo 1600999 2402603 := bstep (se 1 (by rfl) ⟨1801952, by rfl⟩ : syracuseStep 2402603 = 3603905) B3603905
theorem B2402633 : Blo 1600999 2402633 := bstep (se 2 (by rfl) ⟨900987, by rfl⟩ : syracuseStep 2402633 = 1801975) B1801975
theorem B8112473 : Blo 1600999 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B6080953 : Blo 1600999 6080953 := bstep (se 2 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 6080953 = 4560715) B4560715
theorem B2402747 : Blo 1600999 2402747 := bstep (se 1 (by rfl) ⟨1802060, by rfl⟩ : syracuseStep 2402747 = 3604121) B3604121
theorem B2402807 : Blo 1600999 2402807 := bstep (se 1 (by rfl) ⟨1802105, by rfl⟩ : syracuseStep 2402807 = 3604211) B3604211
theorem B4327951 : Blo 1600999 4327951 := bstep (se 1 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 4327951 = 6491927) B6491927
theorem B2402831 : Blo 1600999 2402831 := bstep (se 1 (by rfl) ⟨1802123, by rfl⟩ : syracuseStep 2402831 = 3604247) B3604247
theorem B2886187 : Blo 1600999 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B2279993 : Blo 1600999 2279993 := bstep (se 2 (by rfl) ⟨854997, by rfl⟩ : syracuseStep 2279993 = 1709995) B1709995
theorem B2402873 : Blo 1600999 2402873 := bstep (se 2 (by rfl) ⟨901077, by rfl⟩ : syracuseStep 2402873 = 1802155) B1802155
theorem B5409341 : Blo 1600999 5409341 := bstep (se 3 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 5409341 = 2028503) B2028503
theorem B2402951 : Blo 1600999 2402951 := bstep (se 1 (by rfl) ⟨1802213, by rfl⟩ : syracuseStep 2402951 = 3604427) B3604427
theorem B2280079 : Blo 1600999 2280079 := bstep (se 1 (by rfl) ⟨1710059, by rfl⟩ : syracuseStep 2280079 = 3420119) B3420119
theorem B2280107 : Blo 1600999 2280107 := bstep (se 1 (by rfl) ⟨1710080, by rfl⟩ : syracuseStep 2280107 = 3420161) B3420161
theorem B2402987 : Blo 1600999 2402987 := bstep (se 1 (by rfl) ⟨1802240, by rfl⟩ : syracuseStep 2402987 = 3604481) B3604481
theorem B10398401 : Blo 1600999 10398401 := bstep (se 2 (by rfl) ⟨3899400, by rfl⟩ : syracuseStep 10398401 = 7798801) B7798801
theorem B2403017 : Blo 1600999 2403017 := bstep (se 2 (by rfl) ⟨901131, by rfl⟩ : syracuseStep 2403017 = 1802263) B1802263
theorem B41609999 : Blo 1600999 41609999 := bstep (se 1 (by rfl) ⟨31207499, by rfl⟩ : syracuseStep 41609999 = 62414999) B62414999
theorem B2403131 : Blo 1600999 2403131 := bstep (se 1 (by rfl) ⟨1802348, by rfl⟩ : syracuseStep 2403131 = 3604697) B3604697
theorem B2403191 : Blo 1600999 2403191 := bstep (se 1 (by rfl) ⟨1802393, by rfl⟩ : syracuseStep 2403191 = 3604787) B3604787
theorem B2403215 : Blo 1600999 2403215 := bstep (se 1 (by rfl) ⟨1802411, by rfl⟩ : syracuseStep 2403215 = 3604823) B3604823
theorem B2403257 : Blo 1600999 2403257 := bstep (se 2 (by rfl) ⟨901221, by rfl⟩ : syracuseStep 2403257 = 1802443) B1802443
theorem B2403335 : Blo 1600999 2403335 := bstep (se 1 (by rfl) ⟨1802501, by rfl⟩ : syracuseStep 2403335 = 3605003) B3605003
theorem B2403371 : Blo 1600999 2403371 := bstep (se 1 (by rfl) ⟨1802528, by rfl⟩ : syracuseStep 2403371 = 3605057) B3605057
theorem B2403401 : Blo 1600999 2403401 := bstep (se 2 (by rfl) ⟨901275, by rfl⟩ : syracuseStep 2403401 = 1802551) B1802551
theorem B2026615 : Blo 1600999 2026615 := bstep (se 1 (by rfl) ⟨1519961, by rfl⟩ : syracuseStep 2026615 = 3039923) B3039923
theorem B3042451 : Blo 1600999 3042451 := bstep (se 1 (by rfl) ⟨2281838, by rfl⟩ : syracuseStep 3042451 = 4563677) B4563677
theorem B2403515 : Blo 1600999 2403515 := bstep (se 1 (by rfl) ⟨1802636, by rfl⟩ : syracuseStep 2403515 = 3605273) B3605273
theorem B2403575 : Blo 1600999 2403575 := bstep (se 1 (by rfl) ⟨1802681, by rfl⟩ : syracuseStep 2403575 = 3605363) B3605363
theorem B2403599 : Blo 1600999 2403599 := bstep (se 1 (by rfl) ⟨1802699, by rfl⟩ : syracuseStep 2403599 = 3605399) B3605399
theorem B3419435 : Blo 1600999 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B2403641 : Blo 1600999 2403641 := bstep (se 2 (by rfl) ⟨901365, by rfl⟩ : syracuseStep 2403641 = 1802731) B1802731
theorem B34639163 : Blo 1600999 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B62418275 : Blo 1600999 62418275 := bstep (se 1 (by rfl) ⟨46813706, by rfl⟩ : syracuseStep 62418275 = 93627413) B93627413
theorem B3042679 : Blo 1600999 3042679 := bstep (se 1 (by rfl) ⟨2282009, by rfl⟩ : syracuseStep 3042679 = 4564019) B4564019
theorem B2403719 : Blo 1600999 2403719 := bstep (se 1 (by rfl) ⟨1802789, by rfl⟩ : syracuseStep 2403719 = 3605579) B3605579
theorem B2403755 : Blo 1600999 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B2026939 : Blo 1600999 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B2166203 : Blo 1600999 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B2403785 : Blo 1600999 2403785 := bstep (se 2 (by rfl) ⟨901419, by rfl⟩ : syracuseStep 2403785 = 1802839) B1802839
theorem B1601031 : Blo 1600999 1601031 := bstep (se 1 (by rfl) ⟨1200773, by rfl⟩ : syracuseStep 1601031 = 2401547) B2401547
theorem B1601039 : Blo 1600999 1601039 := bstep (se 1 (by rfl) ⟨1200779, by rfl⟩ : syracuseStep 1601039 = 2401559) B2401559
theorem B1601083 : Blo 1600999 1601083 := bstep (se 1 (by rfl) ⟨1200812, by rfl⟩ : syracuseStep 1601083 = 2401625) B2401625
theorem B2403899 : Blo 1600999 2403899 := bstep (se 1 (by rfl) ⟨1802924, by rfl⟩ : syracuseStep 2403899 = 3605849) B3605849
theorem B13684301 : Blo 1600999 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B2403959 : Blo 1600999 2403959 := bstep (se 1 (by rfl) ⟨1802969, by rfl⟩ : syracuseStep 2403959 = 3605939) B3605939
theorem B1601159 : Blo 1600999 1601159 := bstep (se 1 (by rfl) ⟨1200869, by rfl⟩ : syracuseStep 1601159 = 2401739) B2401739
theorem B1601167 : Blo 1600999 1601167 := bstep (se 1 (by rfl) ⟨1200875, by rfl⟩ : syracuseStep 1601167 = 2401751) B2401751
theorem B2403983 : Blo 1600999 2403983 := bstep (se 1 (by rfl) ⟨1802987, by rfl⟩ : syracuseStep 2403983 = 3605975) B3605975
theorem B2404025 : Blo 1600999 2404025 := bstep (se 2 (by rfl) ⟨901509, by rfl⟩ : syracuseStep 2404025 = 1803019) B1803019
theorem B1601211 : Blo 1600999 1601211 := bstep (se 1 (by rfl) ⟨1200908, by rfl⟩ : syracuseStep 1601211 = 2401817) B2401817
theorem B18255617 : Blo 1600999 18255617 := bstep (se 2 (by rfl) ⟨6845856, by rfl⟩ : syracuseStep 18255617 = 13691713) B13691713
theorem B1601287 : Blo 1600999 1601287 := bstep (se 1 (by rfl) ⟨1200965, by rfl⟩ : syracuseStep 1601287 = 2401931) B2401931
theorem B2404103 : Blo 1600999 2404103 := bstep (se 1 (by rfl) ⟨1803077, by rfl⟩ : syracuseStep 2404103 = 3606155) B3606155
theorem B4329227 : Blo 1600999 4329227 := bstep (se 1 (by rfl) ⟨3246920, by rfl⟩ : syracuseStep 4329227 = 6493841) B6493841
theorem B1601295 : Blo 1600999 1601295 := bstep (se 1 (by rfl) ⟨1200971, by rfl⟩ : syracuseStep 1601295 = 2401943) B2401943
theorem B2469647 : Blo 1600999 2469647 := bstep (se 1 (by rfl) ⟨1852235, by rfl⟩ : syracuseStep 2469647 = 3704471) B3704471
theorem B2404139 : Blo 1600999 2404139 := bstep (se 1 (by rfl) ⟨1803104, by rfl⟩ : syracuseStep 2404139 = 3606209) B3606209
theorem B1601339 : Blo 1600999 1601339 := bstep (se 1 (by rfl) ⟨1201004, by rfl⟩ : syracuseStep 1601339 = 2402009) B2402009
theorem B2404169 : Blo 1600999 2404169 := bstep (se 2 (by rfl) ⟨901563, by rfl⟩ : syracuseStep 2404169 = 1803127) B1803127
theorem B1601415 : Blo 1600999 1601415 := bstep (se 1 (by rfl) ⟨1201061, by rfl⟩ : syracuseStep 1601415 = 2402123) B2402123
theorem B1601423 : Blo 1600999 1601423 := bstep (se 1 (by rfl) ⟨1201067, by rfl⟩ : syracuseStep 1601423 = 2402135) B2402135
theorem B1601467 : Blo 1600999 1601467 := bstep (se 1 (by rfl) ⟨1201100, by rfl⟩ : syracuseStep 1601467 = 2402201) B2402201
theorem B2404283 : Blo 1600999 2404283 := bstep (se 1 (by rfl) ⟨1803212, by rfl⟩ : syracuseStep 2404283 = 3606425) B3606425
theorem B2404343 : Blo 1600999 2404343 := bstep (se 1 (by rfl) ⟨1803257, by rfl⟩ : syracuseStep 2404343 = 3606515) B3606515
theorem B1601543 : Blo 1600999 1601543 := bstep (se 1 (by rfl) ⟨1201157, by rfl⟩ : syracuseStep 1601543 = 2402315) B2402315
theorem B15396875 : Blo 1600999 15396875 := bstep (se 1 (by rfl) ⟨11547656, by rfl⟩ : syracuseStep 15396875 = 23095313) B23095313
theorem B1601551 : Blo 1600999 1601551 := bstep (se 1 (by rfl) ⟨1201163, by rfl⟩ : syracuseStep 1601551 = 2402327) B2402327
theorem B2404367 : Blo 1600999 2404367 := bstep (se 1 (by rfl) ⟨1803275, by rfl⟩ : syracuseStep 2404367 = 3606551) B3606551
theorem B9744407 : Blo 1600999 9744407 := bstep (se 1 (by rfl) ⟨7308305, by rfl⟩ : syracuseStep 9744407 = 14616611) B14616611
theorem B2404409 : Blo 1600999 2404409 := bstep (se 2 (by rfl) ⟨901653, by rfl⟩ : syracuseStep 2404409 = 1803307) B1803307
theorem B1601595 : Blo 1600999 1601595 := bstep (se 1 (by rfl) ⟨1201196, by rfl⟩ : syracuseStep 1601595 = 2402393) B2402393
theorem B1601671 : Blo 1600999 1601671 := bstep (se 1 (by rfl) ⟨1201253, by rfl⟩ : syracuseStep 1601671 = 2402507) B2402507
theorem B2404487 : Blo 1600999 2404487 := bstep (se 1 (by rfl) ⟨1803365, by rfl⟩ : syracuseStep 2404487 = 3606731) B3606731
theorem B1601679 : Blo 1600999 1601679 := bstep (se 1 (by rfl) ⟨1201259, by rfl⟩ : syracuseStep 1601679 = 2402519) B2402519
theorem B1601723 : Blo 1600999 1601723 := bstep (se 1 (by rfl) ⟨1201292, by rfl⟩ : syracuseStep 1601723 = 2402585) B2402585
theorem B1601799 : Blo 1600999 1601799 := bstep (se 1 (by rfl) ⟨1201349, by rfl⟩ : syracuseStep 1601799 = 2402699) B2402699
theorem B4624651 : Blo 1600999 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B1601807 : Blo 1600999 1601807 := bstep (se 1 (by rfl) ⟨1201355, by rfl⟩ : syracuseStep 1601807 = 2402711) B2402711
theorem B1601851 : Blo 1600999 1601851 := bstep (se 1 (by rfl) ⟨1201388, by rfl⟩ : syracuseStep 1601851 = 2402777) B2402777
theorem B1601927 : Blo 1600999 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B2027911 : Blo 1600999 2027911 := bstep (se 1 (by rfl) ⟨1520933, by rfl⟩ : syracuseStep 2027911 = 3041867) B3041867
theorem B1601935 : Blo 1600999 1601935 := bstep (se 1 (by rfl) ⟨1201451, by rfl⟩ : syracuseStep 1601935 = 2402903) B2402903
theorem B8114579 : Blo 1600999 8114579 := bstep (se 1 (by rfl) ⟨6085934, by rfl⟩ : syracuseStep 8114579 = 12171869) B12171869
theorem B4559257 : Blo 1600999 4559257 := bstep (se 2 (by rfl) ⟨1709721, by rfl⟩ : syracuseStep 4559257 = 3419443) B3419443
theorem B1601979 : Blo 1600999 1601979 := bstep (se 1 (by rfl) ⟨1201484, by rfl⟩ : syracuseStep 1601979 = 2402969) B2402969
theorem B10957265 : Blo 1600999 10957265 := bstep (se 2 (by rfl) ⟨4108974, by rfl⟩ : syracuseStep 10957265 = 8217949) B8217949
theorem B1602055 : Blo 1600999 1602055 := bstep (se 1 (by rfl) ⟨1201541, by rfl⟩ : syracuseStep 1602055 = 2403083) B2403083
theorem B1602063 : Blo 1600999 1602063 := bstep (se 1 (by rfl) ⟨1201547, by rfl⟩ : syracuseStep 1602063 = 2403095) B2403095
theorem B2740751 : Blo 1600999 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B12505643 : Blo 1600999 12505643 := bstep (se 1 (by rfl) ⟨9379232, by rfl⟩ : syracuseStep 12505643 = 18758465) B18758465
theorem B1602107 : Blo 1600999 1602107 := bstep (se 1 (by rfl) ⟨1201580, by rfl⟩ : syracuseStep 1602107 = 2403161) B2403161
theorem B1602183 : Blo 1600999 1602183 := bstep (se 1 (by rfl) ⟨1201637, by rfl⟩ : syracuseStep 1602183 = 2403275) B2403275
theorem B2888327 : Blo 1600999 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B1602191 : Blo 1600999 1602191 := bstep (se 1 (by rfl) ⟨1201643, by rfl⟩ : syracuseStep 1602191 = 2403287) B2403287
theorem B1602235 : Blo 1600999 1602235 := bstep (se 1 (by rfl) ⟨1201676, by rfl⟩ : syracuseStep 1602235 = 2403353) B2403353
theorem B13693697 : Blo 1600999 13693697 := bstep (se 2 (by rfl) ⟨5135136, by rfl⟩ : syracuseStep 13693697 = 10270273) B10270273
theorem B1602311 : Blo 1600999 1602311 := bstep (se 1 (by rfl) ⟨1201733, by rfl⟩ : syracuseStep 1602311 = 2403467) B2403467
theorem B6935311 : Blo 1600999 6935311 := bstep (se 1 (by rfl) ⟨5201483, by rfl⟩ : syracuseStep 6935311 = 10402967) B10402967
theorem B34648847 : Blo 1600999 34648847 := bstep (se 1 (by rfl) ⟨25986635, by rfl⟩ : syracuseStep 34648847 = 51973271) B51973271
theorem B1602319 : Blo 1600999 1602319 := bstep (se 1 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 1602319 = 2403479) B2403479
theorem B4559645 : Blo 1600999 4559645 := bstep (se 3 (by rfl) ⟨854933, by rfl⟩ : syracuseStep 4559645 = 1709867) B1709867
theorem B2028331 : Blo 1600999 2028331 := bstep (se 1 (by rfl) ⟨1521248, by rfl⟩ : syracuseStep 2028331 = 3042497) B3042497
theorem B8106803 : Blo 1600999 8106803 := bstep (se 1 (by rfl) ⟨6080102, by rfl⟩ : syracuseStep 8106803 = 12160205) B12160205
theorem B5477179 : Blo 1600999 5477179 := bstep (se 1 (by rfl) ⟨4107884, by rfl⟩ : syracuseStep 5477179 = 8215769) B8215769
theorem B8221499 : Blo 1600999 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B1602363 : Blo 1600999 1602363 := bstep (se 1 (by rfl) ⟨1201772, by rfl⟩ : syracuseStep 1602363 = 2403545) B2403545
theorem B1602439 : Blo 1600999 1602439 := bstep (se 1 (by rfl) ⟨1201829, by rfl⟩ : syracuseStep 1602439 = 2403659) B2403659
theorem B1602447 : Blo 1600999 1602447 := bstep (se 1 (by rfl) ⟨1201835, by rfl⟩ : syracuseStep 1602447 = 2403671) B2403671
theorem B1602491 : Blo 1600999 1602491 := bstep (se 1 (by rfl) ⟨1201868, by rfl⟩ : syracuseStep 1602491 = 2403737) B2403737
theorem B1602567 : Blo 1600999 1602567 := bstep (se 1 (by rfl) ⟨1201925, by rfl⟩ : syracuseStep 1602567 = 2403851) B2403851
theorem B4166671 : Blo 1600999 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B1602575 : Blo 1600999 1602575 := bstep (se 1 (by rfl) ⟨1201931, by rfl⟩ : syracuseStep 1602575 = 2403863) B2403863
theorem B2028559 : Blo 1600999 2028559 := bstep (se 1 (by rfl) ⟨1521419, by rfl⟩ : syracuseStep 2028559 = 3042839) B3042839
theorem B1602619 : Blo 1600999 1602619 := bstep (se 1 (by rfl) ⟨1201964, by rfl⟩ : syracuseStep 1602619 = 2403929) B2403929
theorem B8107127 : Blo 1600999 8107127 := bstep (se 1 (by rfl) ⟨6080345, by rfl⟩ : syracuseStep 8107127 = 12160691) B12160691
theorem B1602695 : Blo 1600999 1602695 := bstep (se 1 (by rfl) ⟨1202021, by rfl⟩ : syracuseStep 1602695 = 2404043) B2404043
theorem B1602703 : Blo 1600999 1602703 := bstep (se 1 (by rfl) ⟨1202027, by rfl⟩ : syracuseStep 1602703 = 2404055) B2404055
theorem B1602747 : Blo 1600999 1602747 := bstep (se 1 (by rfl) ⟨1202060, by rfl⟩ : syracuseStep 1602747 = 2404121) B2404121
theorem B1602823 : Blo 1600999 1602823 := bstep (se 1 (by rfl) ⟨1202117, by rfl⟩ : syracuseStep 1602823 = 2404235) B2404235
theorem B6083855 : Blo 1600999 6083855 := bstep (se 1 (by rfl) ⟨4562891, by rfl⟩ : syracuseStep 6083855 = 9125783) B9125783
theorem B1602831 : Blo 1600999 1602831 := bstep (se 1 (by rfl) ⟨1202123, by rfl⟩ : syracuseStep 1602831 = 2404247) B2404247
theorem B6845755 : Blo 1600999 6845755 := bstep (se 1 (by rfl) ⟨5134316, by rfl⟩ : syracuseStep 6845755 = 10268633) B10268633
theorem B3249467 : Blo 1600999 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B1602875 : Blo 1600999 1602875 := bstep (se 1 (by rfl) ⟨1202156, by rfl⟩ : syracuseStep 1602875 = 2404313) B2404313
theorem B4330871 : Blo 1600999 4330871 := bstep (se 1 (by rfl) ⟨3248153, by rfl⟩ : syracuseStep 4330871 = 6496307) B6496307
theorem B78968195 : Blo 1600999 78968195 := bstep (se 1 (by rfl) ⟨59226146, by rfl⟩ : syracuseStep 78968195 = 118452293) B118452293
theorem B11859335 : Blo 1600999 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B1602951 : Blo 1600999 1602951 := bstep (se 1 (by rfl) ⟨1202213, by rfl⟩ : syracuseStep 1602951 = 2404427) B2404427
theorem B1602959 : Blo 1600999 1602959 := bstep (se 1 (by rfl) ⟨1202219, by rfl⟩ : syracuseStep 1602959 = 2404439) B2404439
theorem B116872733 : Blo 1600999 116872733 := bstep (se 3 (by rfl) ⟨21913637, by rfl⟩ : syracuseStep 116872733 = 43827275) B43827275
theorem B10008107 : Blo 1600999 10008107 := bstep (se 1 (by rfl) ⟨7506080, by rfl⟩ : syracuseStep 10008107 = 15012161) B15012161
theorem B5477975 : Blo 1600999 5477975 := bstep (se 1 (by rfl) ⟨4108481, by rfl⟩ : syracuseStep 5477975 = 8216963) B8216963
theorem B4281943 : Blo 1600999 4281943 := bstep (se 1 (by rfl) ⟨3211457, by rfl⟩ : syracuseStep 4281943 = 6422915) B6422915
theorem B9123617 : Blo 1600999 9123617 := bstep (se 2 (by rfl) ⟨3421356, by rfl⟩ : syracuseStep 9123617 = 6842713) B6842713
theorem B126613313 : Blo 1600999 126613313 := bstep (se 2 (by rfl) ⟨47479992, by rfl⟩ : syracuseStep 126613313 = 94959985) B94959985
theorem B4052855 : Blo 1600999 4052855 := bstep (se 1 (by rfl) ⟨3039641, by rfl⟩ : syracuseStep 4052855 = 6079283) B6079283
theorem B7698361 : Blo 1600999 7698361 := bstep (se 2 (by rfl) ⟨2886885, by rfl⟩ : syracuseStep 7698361 = 5773771) B5773771
theorem B3602447 : Blo 1600999 3602447 := bstep (se 1 (by rfl) ⟨2701835, by rfl⟩ : syracuseStep 3602447 = 5403671) B5403671
theorem B3602465 : Blo 1600999 3602465 := bstep (se 2 (by rfl) ⟨1350924, by rfl⟩ : syracuseStep 3602465 = 2701849) B2701849
theorem B8108099 : Blo 1600999 8108099 := bstep (se 1 (by rfl) ⟨6081074, by rfl⟩ : syracuseStep 8108099 = 12162149) B12162149
theorem B6494327 : Blo 1600999 6494327 := bstep (se 1 (by rfl) ⟨4870745, by rfl⟩ : syracuseStep 6494327 = 9741491) B9741491
theorem B2701687 : Blo 1600999 2701687 := bstep (se 1 (by rfl) ⟨2026265, by rfl⟩ : syracuseStep 2701687 = 4052531) B4052531
theorem B3602807 : Blo 1600999 3602807 := bstep (se 1 (by rfl) ⟨2702105, by rfl⟩ : syracuseStep 3602807 = 5404211) B5404211
theorem B8108423 : Blo 1600999 8108423 := bstep (se 1 (by rfl) ⟨6081317, by rfl⟩ : syracuseStep 8108423 = 12162635) B12162635
theorem B5134727 : Blo 1600999 5134727 := bstep (se 1 (by rfl) ⟨3851045, by rfl⟩ : syracuseStep 5134727 = 7702091) B7702091
theorem B5405075 : Blo 1600999 5405075 := bstep (se 1 (by rfl) ⟨4053806, by rfl⟩ : syracuseStep 5405075 = 8107613) B8107613
theorem B4872595 : Blo 1600999 4872595 := bstep (se 1 (by rfl) ⟨3654446, by rfl⟩ : syracuseStep 4872595 = 7308893) B7308893
theorem B6838681 : Blo 1600999 6838681 := bstep (se 2 (by rfl) ⟨2564505, by rfl⟩ : syracuseStep 6838681 = 5129011) B5129011
theorem B3602987 : Blo 1600999 3602987 := bstep (se 1 (by rfl) ⟨2702240, by rfl⟩ : syracuseStep 3602987 = 5404481) B5404481
theorem B13687339 : Blo 1600999 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B2701883 : Blo 1600999 2701883 := bstep (se 1 (by rfl) ⟨2026412, by rfl⟩ : syracuseStep 2701883 = 4052825) B4052825
theorem B5773885 : Blo 1600999 5773885 := bstep (se 3 (by rfl) ⟨1082603, by rfl⟩ : syracuseStep 5773885 = 2165207) B2165207
theorem B18258533 : Blo 1600999 18258533 := bstep (se 4 (by rfl) ⟨1711737, by rfl⟩ : syracuseStep 18258533 = 3423475) B3423475
theorem B4053847 : Blo 1600999 4053847 := bstep (se 1 (by rfl) ⟨3040385, by rfl⟩ : syracuseStep 4053847 = 6080771) B6080771
theorem B3603347 : Blo 1600999 3603347 := bstep (se 1 (by rfl) ⟨2702510, by rfl⟩ : syracuseStep 3603347 = 5405021) B5405021
theorem B1801147 : Blo 1600999 1801147 := bstep (se 1 (by rfl) ⟨1350860, by rfl⟩ : syracuseStep 1801147 = 2701721) B2701721
theorem B2702281 : Blo 1600999 2702281 := bstep (se 2 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 2702281 = 2026711) B2026711
theorem B3603401 : Blo 1600999 3603401 := bstep (se 2 (by rfl) ⟨1351275, by rfl⟩ : syracuseStep 3603401 = 2702551) B2702551
theorem B3849335 : Blo 1600999 3849335 := bstep (se 1 (by rfl) ⟨2887001, by rfl⟩ : syracuseStep 3849335 = 5774003) B5774003
theorem B4054151 : Blo 1600999 4054151 := bstep (se 1 (by rfl) ⟨3040613, by rfl⟩ : syracuseStep 4054151 = 6081227) B6081227
theorem B1924283 : Blo 1600999 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B39492845 : Blo 1600999 39492845 := bstep (se 3 (by rfl) ⟨7404908, by rfl⟩ : syracuseStep 39492845 = 14809817) B14809817
theorem B4054283 : Blo 1600999 4054283 := bstep (se 1 (by rfl) ⟨3040712, by rfl⟩ : syracuseStep 4054283 = 6081425) B6081425
theorem B4562219 : Blo 1600999 4562219 := bstep (se 1 (by rfl) ⟨3421664, by rfl⟩ : syracuseStep 4562219 = 6843329) B6843329
theorem B7306631 : Blo 1600999 7306631 := bstep (se 1 (by rfl) ⟨5479973, by rfl⟩ : syracuseStep 7306631 = 10959947) B10959947
theorem B1801615 : Blo 1600999 1801615 := bstep (se 1 (by rfl) ⟨1351211, by rfl⟩ : syracuseStep 1801615 = 2702423) B2702423
theorem B8658323 : Blo 1600999 8658323 := bstep (se 1 (by rfl) ⟨6493742, by rfl⟩ : syracuseStep 8658323 = 12987485) B12987485
theorem B3849815 : Blo 1600999 3849815 := bstep (se 1 (by rfl) ⟨2887361, by rfl⟩ : syracuseStep 3849815 = 5774723) B5774723
theorem B2702983 : Blo 1600999 2702983 := bstep (se 1 (by rfl) ⟨2027237, by rfl⟩ : syracuseStep 2702983 = 4054475) B4054475
theorem B3604103 : Blo 1600999 3604103 := bstep (se 1 (by rfl) ⟨2703077, by rfl⟩ : syracuseStep 3604103 = 5406155) B5406155
theorem B4054799 : Blo 1600999 4054799 := bstep (se 1 (by rfl) ⟨3041099, by rfl⟩ : syracuseStep 4054799 = 6082199) B6082199
theorem B5406479 : Blo 1600999 5406479 := bstep (se 1 (by rfl) ⟨4054859, by rfl⟩ : syracuseStep 5406479 = 8109719) B8109719
theorem B1924879 : Blo 1600999 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B20799281 : Blo 1600999 20799281 := bstep (se 2 (by rfl) ⟨7799730, by rfl⟩ : syracuseStep 20799281 = 15599461) B15599461
theorem B3604283 : Blo 1600999 3604283 := bstep (se 1 (by rfl) ⟨2703212, by rfl⟩ : syracuseStep 3604283 = 5406425) B5406425
theorem B1802119 : Blo 1600999 1802119 := bstep (se 1 (by rfl) ⟨1351589, by rfl⟩ : syracuseStep 1802119 = 2703179) B2703179
theorem B7700359 : Blo 1600999 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B4054931 : Blo 1600999 4054931 := bstep (se 1 (by rfl) ⟨3041198, by rfl⟩ : syracuseStep 4054931 = 6082397) B6082397
theorem B3604409 : Blo 1600999 3604409 := bstep (se 2 (by rfl) ⟨1351653, by rfl⟩ : syracuseStep 3604409 = 2703307) B2703307
theorem B10264583 : Blo 1600999 10264583 := bstep (se 1 (by rfl) ⟨7698437, by rfl⟩ : syracuseStep 10264583 = 15396875) B15396875
theorem B6496271 : Blo 1600999 6496271 := bstep (se 1 (by rfl) ⟨4872203, by rfl⟩ : syracuseStep 6496271 = 9744407) B9744407
theorem B15024143 : Blo 1600999 15024143 := bstep (se 1 (by rfl) ⟨11268107, by rfl⟩ : syracuseStep 15024143 = 22536215) B22536215
theorem B3604499 : Blo 1600999 3604499 := bstep (se 1 (by rfl) ⟨2703374, by rfl⟩ : syracuseStep 3604499 = 5406749) B5406749
theorem B3850411 : Blo 1600999 3850411 := bstep (se 1 (by rfl) ⟨2887808, by rfl⟩ : syracuseStep 3850411 = 5775617) B5775617
theorem B10961203 : Blo 1600999 10961203 := bstep (se 1 (by rfl) ⟨8220902, by rfl⟩ : syracuseStep 10961203 = 16441805) B16441805
theorem B30794053 : Blo 1600999 30794053 := bstep (se 4 (by rfl) ⟨2886942, by rfl⟩ : syracuseStep 30794053 = 5773885) B5773885
theorem B3604841 : Blo 1600999 3604841 := bstep (se 2 (by rfl) ⟨1351815, by rfl⟩ : syracuseStep 3604841 = 2703631) B2703631
theorem B1925551 : Blo 1600999 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B2703881 : Blo 1600999 2703881 := bstep (se 2 (by rfl) ⟨1013955, by rfl⟩ : syracuseStep 2703881 = 2027911) B2027911
theorem B3039763 : Blo 1600999 3039763 := bstep (se 1 (by rfl) ⟨2279822, by rfl⟩ : syracuseStep 3039763 = 4559645) B4559645
theorem B6496793 : Blo 1600999 6496793 := bstep (se 2 (by rfl) ⟨2436297, by rfl⟩ : syracuseStep 6496793 = 4872595) B4872595
theorem B9118241 : Blo 1600999 9118241 := bstep (se 2 (by rfl) ⟨3419340, by rfl⟩ : syracuseStep 9118241 = 6838681) B6838681
theorem B6079009 : Blo 1600999 6079009 := bstep (se 2 (by rfl) ⟨2279628, by rfl⟩ : syracuseStep 6079009 = 4559257) B4559257
theorem B5480999 : Blo 1600999 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B1802875 : Blo 1600999 1802875 := bstep (se 1 (by rfl) ⟨1352156, by rfl⟩ : syracuseStep 1802875 = 2704313) B2704313
theorem B2704043 : Blo 1600999 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B13681325 : Blo 1600999 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B9118493 : Blo 1600999 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B4055903 : Blo 1600999 4055903 := bstep (se 1 (by rfl) ⟨3041927, by rfl⟩ : syracuseStep 4055903 = 6083855) B6083855
theorem B3040105 : Blo 1600999 3040105 := bstep (se 2 (by rfl) ⟨1140039, by rfl⟩ : syracuseStep 3040105 = 2280079) B2280079
theorem B7906223 : Blo 1600999 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B3605435 : Blo 1600999 3605435 := bstep (se 1 (by rfl) ⟨2704076, by rfl⟩ : syracuseStep 3605435 = 5408153) B5408153
theorem B6079495 : Blo 1600999 6079495 := bstep (se 1 (by rfl) ⟨4559621, by rfl⟩ : syracuseStep 6079495 = 9119243) B9119243
theorem B77915155 : Blo 1600999 77915155 := bstep (se 1 (by rfl) ⟨58436366, by rfl⟩ : syracuseStep 77915155 = 116872733) B116872733
theorem B1623079 : Blo 1600999 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B3605561 : Blo 1600999 3605561 := bstep (se 2 (by rfl) ⟨1352085, by rfl⟩ : syracuseStep 3605561 = 2704171) B2704171
theorem B2704441 : Blo 1600999 2704441 := bstep (se 2 (by rfl) ⟨1014165, by rfl⟩ : syracuseStep 2704441 = 2028331) B2028331
theorem B19760195 : Blo 1600999 19760195 := bstep (se 1 (by rfl) ⟨14820146, by rfl⟩ : syracuseStep 19760195 = 29640293) B29640293
theorem B1803343 : Blo 1600999 1803343 := bstep (se 1 (by rfl) ⟨1352507, by rfl⟩ : syracuseStep 1803343 = 2705015) B2705015
theorem B5776541 : Blo 1600999 5776541 := bstep (se 3 (by rfl) ⟨1083101, by rfl⟩ : syracuseStep 5776541 = 2166203) B2166203
theorem B23397547 : Blo 1600999 23397547 := bstep (se 1 (by rfl) ⟨17548160, by rfl⟩ : syracuseStep 23397547 = 35096321) B35096321
theorem B2704583 : Blo 1600999 2704583 := bstep (se 1 (by rfl) ⟨2028437, by rfl⟩ : syracuseStep 2704583 = 4056875) B4056875
theorem B2401529 : Blo 1600999 2401529 := bstep (se 2 (by rfl) ⟨900573, by rfl⟩ : syracuseStep 2401529 = 1801147) B1801147
theorem B5407991 : Blo 1600999 5407991 := bstep (se 1 (by rfl) ⟨4055993, by rfl⟩ : syracuseStep 5407991 = 8111987) B8111987
theorem B2401631 : Blo 1600999 2401631 := bstep (se 1 (by rfl) ⟨1801223, by rfl⟩ : syracuseStep 2401631 = 3602447) B3602447
theorem B5555561 : Blo 1600999 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B2704745 : Blo 1600999 2704745 := bstep (se 2 (by rfl) ⟨1014279, by rfl⟩ : syracuseStep 2704745 = 2028559) B2028559
theorem B2401643 : Blo 1600999 2401643 := bstep (se 1 (by rfl) ⟨1801232, by rfl⟩ : syracuseStep 2401643 = 3602465) B3602465
theorem B3605903 : Blo 1600999 3605903 := bstep (se 1 (by rfl) ⟨2704427, by rfl⟩ : syracuseStep 3605903 = 5408855) B5408855
theorem B23102921 : Blo 1600999 23102921 := bstep (se 2 (by rfl) ⟨8663595, by rfl⟩ : syracuseStep 23102921 = 17327191) B17327191
theorem B6079981 : Blo 1600999 6079981 := bstep (se 3 (by rfl) ⟨1139996, by rfl⟩ : syracuseStep 6079981 = 2279993) B2279993
theorem B4056601 : Blo 1600999 4056601 := bstep (se 2 (by rfl) ⟨1521225, by rfl⟩ : syracuseStep 4056601 = 3042451) B3042451
theorem B5408315 : Blo 1600999 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B10266173 : Blo 1600999 10266173 := bstep (se 3 (by rfl) ⟨1924907, by rfl⟩ : syracuseStep 10266173 = 3849815) B3849815
theorem B2401871 : Blo 1600999 2401871 := bstep (se 1 (by rfl) ⟨1801403, by rfl⟩ : syracuseStep 2401871 = 3602807) B3602807
theorem B85485149 : Blo 1600999 85485149 := bstep (se 3 (by rfl) ⟨16028465, by rfl⟩ : syracuseStep 85485149 = 32056931) B32056931
theorem B2401991 : Blo 1600999 2401991 := bstep (se 1 (by rfl) ⟨1801493, by rfl⟩ : syracuseStep 2401991 = 3602987) B3602987
theorem B3606227 : Blo 1600999 3606227 := bstep (se 1 (by rfl) ⟨2704670, by rfl⟩ : syracuseStep 3606227 = 5409341) B5409341
theorem B9127673 : Blo 1600999 9127673 := bstep (se 2 (by rfl) ⟨3422877, by rfl⟩ : syracuseStep 9127673 = 6845755) B6845755
theorem B6080285 : Blo 1600999 6080285 := bstep (se 3 (by rfl) ⟨1140053, by rfl⟩ : syracuseStep 6080285 = 2280107) B2280107
theorem B6932267 : Blo 1600999 6932267 := bstep (se 1 (by rfl) ⟨5199200, by rfl⟩ : syracuseStep 6932267 = 10398401) B10398401
theorem B5408585 : Blo 1600999 5408585 := bstep (se 2 (by rfl) ⟨2028219, by rfl⟩ : syracuseStep 5408585 = 4056439) B4056439
theorem B4056905 : Blo 1600999 4056905 := bstep (se 2 (by rfl) ⟨1521339, by rfl⟩ : syracuseStep 4056905 = 3042679) B3042679
theorem B27739999 : Blo 1600999 27739999 := bstep (se 1 (by rfl) ⟨20804999, by rfl⟩ : syracuseStep 27739999 = 41609999) B41609999
theorem B2402153 : Blo 1600999 2402153 := bstep (se 2 (by rfl) ⟨900807, by rfl⟩ : syracuseStep 2402153 = 1801615) B1801615
theorem B2402231 : Blo 1600999 2402231 := bstep (se 1 (by rfl) ⟨1801673, by rfl⟩ : syracuseStep 2402231 = 3603347) B3603347
theorem B2402267 : Blo 1600999 2402267 := bstep (se 1 (by rfl) ⟨1801700, by rfl⟩ : syracuseStep 2402267 = 3603401) B3603401
theorem B11544605 : Blo 1600999 11544605 := bstep (se 3 (by rfl) ⟨2164613, by rfl⟩ : syracuseStep 11544605 = 4329227) B4329227
theorem B2566223 : Blo 1600999 2566223 := bstep (se 1 (by rfl) ⟨1924667, by rfl⟩ : syracuseStep 2566223 = 3849335) B3849335
theorem B3041479 : Blo 1600999 3041479 := bstep (se 1 (by rfl) ⟨2281109, by rfl⟩ : syracuseStep 3041479 = 4562219) B4562219
theorem B12159233 : Blo 1600999 12159233 := bstep (se 2 (by rfl) ⟨4559712, by rfl⟩ : syracuseStep 12159233 = 9119425) B9119425
theorem B2566505 : Blo 1600999 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B2402735 : Blo 1600999 2402735 := bstep (se 1 (by rfl) ⟨1802051, by rfl⟩ : syracuseStep 2402735 = 3604103) B3604103
theorem B2402825 : Blo 1600999 2402825 := bstep (se 2 (by rfl) ⟨901059, by rfl⟩ : syracuseStep 2402825 = 1802119) B1802119
theorem B10267145 : Blo 1600999 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B2402855 : Blo 1600999 2402855 := bstep (se 1 (by rfl) ⟨1802141, by rfl⟩ : syracuseStep 2402855 = 3604283) B3604283
theorem B2402939 : Blo 1600999 2402939 := bstep (se 1 (by rfl) ⟨1802204, by rfl⟩ : syracuseStep 2402939 = 3604409) B3604409
theorem B2468551 : Blo 1600999 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B2403065 : Blo 1600999 2403065 := bstep (se 2 (by rfl) ⟨901149, by rfl⟩ : syracuseStep 2403065 = 1802299) B1802299
theorem B2403167 : Blo 1600999 2403167 := bstep (se 1 (by rfl) ⟨1802375, by rfl⟩ : syracuseStep 2403167 = 3604751) B3604751
theorem B2403179 : Blo 1600999 2403179 := bstep (se 1 (by rfl) ⟨1802384, by rfl⟩ : syracuseStep 2403179 = 3604769) B3604769
theorem B5409719 : Blo 1600999 5409719 := bstep (se 1 (by rfl) ⟨4057289, by rfl⟩ : syracuseStep 5409719 = 8114579) B8114579
theorem B2403407 : Blo 1600999 2403407 := bstep (se 1 (by rfl) ⟨1802555, by rfl⟩ : syracuseStep 2403407 = 3605111) B3605111
theorem B5131421 : Blo 1600999 5131421 := bstep (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) B1924283
theorem B9129131 : Blo 1600999 9129131 := bstep (se 1 (by rfl) ⟨6846848, by rfl⟩ : syracuseStep 9129131 = 13693697) B13693697
theorem B2403527 : Blo 1600999 2403527 := bstep (se 1 (by rfl) ⟨1802645, by rfl⟩ : syracuseStep 2403527 = 3605291) B3605291
theorem B5770601 : Blo 1600999 5770601 := bstep (se 2 (by rfl) ⟨2163975, by rfl⟩ : syracuseStep 5770601 = 4327951) B4327951
theorem B2403689 : Blo 1600999 2403689 := bstep (se 2 (by rfl) ⟨901383, by rfl⟩ : syracuseStep 2403689 = 1802767) B1802767
theorem B6843791 : Blo 1600999 6843791 := bstep (se 1 (by rfl) ⟨5132843, by rfl⟩ : syracuseStep 6843791 = 10265687) B10265687
theorem B2403767 : Blo 1600999 2403767 := bstep (se 1 (by rfl) ⟨1802825, by rfl⟩ : syracuseStep 2403767 = 3605651) B3605651
theorem B2403803 : Blo 1600999 2403803 := bstep (se 1 (by rfl) ⟨1802852, by rfl⟩ : syracuseStep 2403803 = 3605705) B3605705
theorem B10268147 : Blo 1600999 10268147 := bstep (se 1 (by rfl) ⟨7701110, by rfl⟩ : syracuseStep 10268147 = 15402221) B15402221
theorem B10268171 : Blo 1600999 10268171 := bstep (se 1 (by rfl) ⟨7701128, by rfl⟩ : syracuseStep 10268171 = 15402257) B15402257
theorem B1601063 : Blo 1600999 1601063 := bstep (se 1 (by rfl) ⟨1200797, by rfl⟩ : syracuseStep 1601063 = 2401595) B2401595
theorem B6843943 : Blo 1600999 6843943 := bstep (se 1 (by rfl) ⟨5132957, by rfl⟩ : syracuseStep 6843943 = 10265915) B10265915
theorem B2166311 : Blo 1600999 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B1601103 : Blo 1600999 1601103 := bstep (se 1 (by rfl) ⟨1200827, by rfl⟩ : syracuseStep 1601103 = 2401655) B2401655
theorem B2887247 : Blo 1600999 2887247 := bstep (se 1 (by rfl) ⟨2165435, by rfl⟩ : syracuseStep 2887247 = 4330871) B4330871
theorem B52645463 : Blo 1600999 52645463 := bstep (se 1 (by rfl) ⟨39484097, by rfl⟩ : syracuseStep 52645463 = 78968195) B78968195
theorem B1601119 : Blo 1600999 1601119 := bstep (se 1 (by rfl) ⟨1200839, by rfl⟩ : syracuseStep 1601119 = 2401679) B2401679
theorem B12988001 : Blo 1600999 12988001 := bstep (se 2 (by rfl) ⟨4870500, by rfl⟩ : syracuseStep 12988001 = 9741001) B9741001
theorem B1601147 : Blo 1600999 1601147 := bstep (se 1 (by rfl) ⟨1200860, by rfl⟩ : syracuseStep 1601147 = 2401721) B2401721
theorem B1601199 : Blo 1600999 1601199 := bstep (se 1 (by rfl) ⟨1200899, by rfl⟩ : syracuseStep 1601199 = 2401799) B2401799
theorem B1601223 : Blo 1600999 1601223 := bstep (se 1 (by rfl) ⟨1200917, by rfl⟩ : syracuseStep 1601223 = 2401835) B2401835
theorem B6672071 : Blo 1600999 6672071 := bstep (se 1 (by rfl) ⟨5004053, by rfl⟩ : syracuseStep 6672071 = 10008107) B10008107
theorem B2027207 : Blo 1600999 2027207 := bstep (se 1 (by rfl) ⟨1520405, by rfl⟩ : syracuseStep 2027207 = 3040811) B3040811
theorem B1601243 : Blo 1600999 1601243 := bstep (se 1 (by rfl) ⟨1200932, by rfl⟩ : syracuseStep 1601243 = 2401865) B2401865
theorem B7302905 : Blo 1600999 7302905 := bstep (se 2 (by rfl) ⟨2738589, by rfl⟩ : syracuseStep 7302905 = 5477179) B5477179
theorem B12168953 : Blo 1600999 12168953 := bstep (se 2 (by rfl) ⟨4563357, by rfl⟩ : syracuseStep 12168953 = 9126715) B9126715
theorem B1601319 : Blo 1600999 1601319 := bstep (se 1 (by rfl) ⟨1200989, by rfl⟩ : syracuseStep 1601319 = 2401979) B2401979
theorem B1601359 : Blo 1600999 1601359 := bstep (se 1 (by rfl) ⟨1201019, by rfl⟩ : syracuseStep 1601359 = 2402039) B2402039
theorem B1601375 : Blo 1600999 1601375 := bstep (se 1 (by rfl) ⟨1201031, by rfl⟩ : syracuseStep 1601375 = 2402063) B2402063
theorem B2027359 : Blo 1600999 2027359 := bstep (se 1 (by rfl) ⟨1520519, by rfl⟩ : syracuseStep 2027359 = 3041039) B3041039
theorem B6082411 : Blo 1600999 6082411 := bstep (se 1 (by rfl) ⟨4561808, by rfl⟩ : syracuseStep 6082411 = 9123617) B9123617
theorem B1601403 : Blo 1600999 1601403 := bstep (se 1 (by rfl) ⟨1201052, by rfl⟩ : syracuseStep 1601403 = 2402105) B2402105
theorem B1601455 : Blo 1600999 1601455 := bstep (se 1 (by rfl) ⟨1201091, by rfl⟩ : syracuseStep 1601455 = 2402183) B2402183
theorem B2404271 : Blo 1600999 2404271 := bstep (se 1 (by rfl) ⟨1803203, by rfl⟩ : syracuseStep 2404271 = 3606407) B3606407
theorem B1601479 : Blo 1600999 1601479 := bstep (se 1 (by rfl) ⟨1201109, by rfl⟩ : syracuseStep 1601479 = 2402219) B2402219
theorem B1601499 : Blo 1600999 1601499 := bstep (se 1 (by rfl) ⟨1201124, by rfl⟩ : syracuseStep 1601499 = 2402249) B2402249
theorem B2404361 : Blo 1600999 2404361 := bstep (se 2 (by rfl) ⟨901635, by rfl⟩ : syracuseStep 2404361 = 1803271) B1803271
theorem B1601575 : Blo 1600999 1601575 := bstep (se 1 (by rfl) ⟨1201181, by rfl⟩ : syracuseStep 1601575 = 2402363) B2402363
theorem B2404391 : Blo 1600999 2404391 := bstep (se 1 (by rfl) ⟨1803293, by rfl⟩ : syracuseStep 2404391 = 3606587) B3606587
theorem B1601615 : Blo 1600999 1601615 := bstep (se 1 (by rfl) ⟨1201211, by rfl⟩ : syracuseStep 1601615 = 2402423) B2402423
theorem B4329551 : Blo 1600999 4329551 := bstep (se 1 (by rfl) ⟨3247163, by rfl⟩ : syracuseStep 4329551 = 6494327) B6494327
theorem B1601631 : Blo 1600999 1601631 := bstep (se 1 (by rfl) ⟨1201223, by rfl⟩ : syracuseStep 1601631 = 2402447) B2402447
theorem B166572125 : Blo 1600999 166572125 := bstep (se 3 (by rfl) ⟨31232273, by rfl⟩ : syracuseStep 166572125 = 62464547) B62464547
theorem B1601659 : Blo 1600999 1601659 := bstep (se 1 (by rfl) ⟨1201244, by rfl⟩ : syracuseStep 1601659 = 2402489) B2402489
theorem B2404475 : Blo 1600999 2404475 := bstep (se 1 (by rfl) ⟨1803356, by rfl⟩ : syracuseStep 2404475 = 3606713) B3606713
theorem B1601711 : Blo 1600999 1601711 := bstep (se 1 (by rfl) ⟨1201283, by rfl⟩ : syracuseStep 1601711 = 2402567) B2402567
theorem B1601735 : Blo 1600999 1601735 := bstep (se 1 (by rfl) ⟨1201301, by rfl⟩ : syracuseStep 1601735 = 2402603) B2402603
theorem B1601755 : Blo 1600999 1601755 := bstep (se 1 (by rfl) ⟨1201316, by rfl⟩ : syracuseStep 1601755 = 2402633) B2402633
theorem B1601831 : Blo 1600999 1601831 := bstep (se 1 (by rfl) ⟨1201373, by rfl⟩ : syracuseStep 1601831 = 2402747) B2402747
theorem B1601871 : Blo 1600999 1601871 := bstep (se 1 (by rfl) ⟨1201403, by rfl⟩ : syracuseStep 1601871 = 2402807) B2402807
theorem B1601887 : Blo 1600999 1601887 := bstep (se 1 (by rfl) ⟨1201415, by rfl⟩ : syracuseStep 1601887 = 2402831) B2402831
theorem B1601915 : Blo 1600999 1601915 := bstep (se 1 (by rfl) ⟨1201436, by rfl⟩ : syracuseStep 1601915 = 2402873) B2402873
theorem B1601967 : Blo 1600999 1601967 := bstep (se 1 (by rfl) ⟨1201475, by rfl⟩ : syracuseStep 1601967 = 2402951) B2402951
theorem B1601991 : Blo 1600999 1601991 := bstep (se 1 (by rfl) ⟨1201493, by rfl⟩ : syracuseStep 1601991 = 2402987) B2402987
theorem B1602011 : Blo 1600999 1602011 := bstep (se 1 (by rfl) ⟨1201508, by rfl⟩ : syracuseStep 1602011 = 2403017) B2403017
theorem B1602087 : Blo 1600999 1602087 := bstep (se 1 (by rfl) ⟨1201565, by rfl⟩ : syracuseStep 1602087 = 2403131) B2403131
theorem B1602127 : Blo 1600999 1602127 := bstep (se 1 (by rfl) ⟨1201595, by rfl⟩ : syracuseStep 1602127 = 2403191) B2403191
theorem B1602143 : Blo 1600999 1602143 := bstep (se 1 (by rfl) ⟨1201607, by rfl⟩ : syracuseStep 1602143 = 2403215) B2403215
theorem B1602171 : Blo 1600999 1602171 := bstep (se 1 (by rfl) ⟨1201628, by rfl⟩ : syracuseStep 1602171 = 2403257) B2403257
theorem B1602223 : Blo 1600999 1602223 := bstep (se 1 (by rfl) ⟨1201667, by rfl⟩ : syracuseStep 1602223 = 2403335) B2403335
theorem B1602247 : Blo 1600999 1602247 := bstep (se 1 (by rfl) ⟨1201685, by rfl⟩ : syracuseStep 1602247 = 2403371) B2403371
theorem B1602267 : Blo 1600999 1602267 := bstep (se 1 (by rfl) ⟨1201700, by rfl⟩ : syracuseStep 1602267 = 2403401) B2403401
theorem B1602343 : Blo 1600999 1602343 := bstep (se 1 (by rfl) ⟨1201757, by rfl⟩ : syracuseStep 1602343 = 2403515) B2403515
theorem B55464749 : Blo 1600999 55464749 := bstep (se 3 (by rfl) ⟨10399640, by rfl⟩ : syracuseStep 55464749 = 20799281) B20799281
theorem B1602383 : Blo 1600999 1602383 := bstep (se 1 (by rfl) ⟨1201787, by rfl⟩ : syracuseStep 1602383 = 2403575) B2403575
theorem B1602399 : Blo 1600999 1602399 := bstep (se 1 (by rfl) ⟨1201799, by rfl⟩ : syracuseStep 1602399 = 2403599) B2403599
theorem B1602427 : Blo 1600999 1602427 := bstep (se 1 (by rfl) ⟨1201820, by rfl⟩ : syracuseStep 1602427 = 2403641) B2403641
theorem B41612183 : Blo 1600999 41612183 := bstep (se 1 (by rfl) ⟨31209137, by rfl⟩ : syracuseStep 41612183 = 62418275) B62418275
theorem B4871087 : Blo 1600999 4871087 := bstep (se 1 (by rfl) ⟨3653315, by rfl⟩ : syracuseStep 4871087 = 7306631) B7306631
theorem B1602479 : Blo 1600999 1602479 := bstep (se 1 (by rfl) ⟨1201859, by rfl⟩ : syracuseStep 1602479 = 2403719) B2403719
theorem B5772215 : Blo 1600999 5772215 := bstep (se 1 (by rfl) ⟨4329161, by rfl⟩ : syracuseStep 5772215 = 8658323) B8658323
theorem B1602503 : Blo 1600999 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B1602523 : Blo 1600999 1602523 := bstep (se 1 (by rfl) ⟨1201892, by rfl⟩ : syracuseStep 1602523 = 2403785) B2403785
theorem B1602599 : Blo 1600999 1602599 := bstep (se 1 (by rfl) ⟨1201949, by rfl⟩ : syracuseStep 1602599 = 2403899) B2403899
theorem B9122867 : Blo 1600999 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B1602639 : Blo 1600999 1602639 := bstep (se 1 (by rfl) ⟨1201979, by rfl⟩ : syracuseStep 1602639 = 2403959) B2403959
theorem B1602655 : Blo 1600999 1602655 := bstep (se 1 (by rfl) ⟨1201991, by rfl⟩ : syracuseStep 1602655 = 2403983) B2403983
theorem B1602683 : Blo 1600999 1602683 := bstep (se 1 (by rfl) ⟨1202012, by rfl⟩ : syracuseStep 1602683 = 2404025) B2404025
theorem B12170411 : Blo 1600999 12170411 := bstep (se 1 (by rfl) ⟨9127808, by rfl⟩ : syracuseStep 12170411 = 18255617) B18255617
theorem B1602735 : Blo 1600999 1602735 := bstep (se 1 (by rfl) ⟨1202051, by rfl⟩ : syracuseStep 1602735 = 2404103) B2404103
theorem B1602759 : Blo 1600999 1602759 := bstep (se 1 (by rfl) ⟨1202069, by rfl⟩ : syracuseStep 1602759 = 2404139) B2404139
theorem B1602779 : Blo 1600999 1602779 := bstep (se 1 (by rfl) ⟨1202084, by rfl⟩ : syracuseStep 1602779 = 2404169) B2404169
theorem B1602855 : Blo 1600999 1602855 := bstep (se 1 (by rfl) ⟨1202141, by rfl⟩ : syracuseStep 1602855 = 2404283) B2404283
theorem B1602895 : Blo 1600999 1602895 := bstep (se 1 (by rfl) ⟨1202171, by rfl⟩ : syracuseStep 1602895 = 2404343) B2404343
theorem B1602911 : Blo 1600999 1602911 := bstep (se 1 (by rfl) ⟨1202183, by rfl⟩ : syracuseStep 1602911 = 2404367) B2404367
theorem B3249515 : Blo 1600999 3249515 := bstep (se 1 (by rfl) ⟨2437136, by rfl⟩ : syracuseStep 3249515 = 4874273) B4874273
theorem B1602939 : Blo 1600999 1602939 := bstep (se 1 (by rfl) ⟨1202204, by rfl⟩ : syracuseStep 1602939 = 2404409) B2404409
theorem B1602991 : Blo 1600999 1602991 := bstep (se 1 (by rfl) ⟨1202243, by rfl⟩ : syracuseStep 1602991 = 2404487) B2404487
theorem B29234677 : Blo 1600999 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B7304843 : Blo 1600999 7304843 := bstep (se 1 (by rfl) ⟨5478632, by rfl⟩ : syracuseStep 7304843 = 10957265) B10957265
theorem B12170897 : Blo 1600999 12170897 := bstep (se 2 (by rfl) ⟨4564086, by rfl⟩ : syracuseStep 12170897 = 9128173) B9128173
theorem B6166201 : Blo 1600999 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B8337095 : Blo 1600999 8337095 := bstep (se 1 (by rfl) ⟨6252821, by rfl⟩ : syracuseStep 8337095 = 12505643) B12505643
theorem B3602249 : Blo 1600999 3602249 := bstep (se 2 (by rfl) ⟨1350843, by rfl⟩ : syracuseStep 3602249 = 2701687) B2701687
theorem B23099231 : Blo 1600999 23099231 := bstep (se 1 (by rfl) ⟨17324423, by rfl⟩ : syracuseStep 23099231 = 34648847) B34648847
theorem B5404535 : Blo 1600999 5404535 := bstep (se 1 (by rfl) ⟨4053401, by rfl⟩ : syracuseStep 5404535 = 8106803) B8106803
theorem B8107937 : Blo 1600999 8107937 := bstep (se 2 (by rfl) ⟨3040476, by rfl⟩ : syracuseStep 8107937 = 6080953) B6080953
theorem B3848249 : Blo 1600999 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B18249785 : Blo 1600999 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B5404751 : Blo 1600999 5404751 := bstep (se 1 (by rfl) ⟨4053563, by rfl⟩ : syracuseStep 5404751 = 8107127) B8107127
theorem B5773655 : Blo 1600999 5773655 := bstep (se 1 (by rfl) ⟨4330241, by rfl⟩ : syracuseStep 5773655 = 8660483) B8660483
theorem B9247081 : Blo 1600999 9247081 := bstep (se 2 (by rfl) ⟨3467655, by rfl⟩ : syracuseStep 9247081 = 6935311) B6935311
theorem B3651983 : Blo 1600999 3651983 := bstep (se 1 (by rfl) ⟨2738987, by rfl⟩ : syracuseStep 3651983 = 5477975) B5477975
theorem B5405129 : Blo 1600999 5405129 := bstep (se 2 (by rfl) ⟨2026923, by rfl⟩ : syracuseStep 5405129 = 4053847) B4053847
theorem B12163607 : Blo 1600999 12163607 := bstep (se 1 (by rfl) ⟨9122705, by rfl⟩ : syracuseStep 12163607 = 18245411) B18245411
theorem B6085145 : Blo 1600999 6085145 := bstep (se 2 (by rfl) ⟨2281929, by rfl⟩ : syracuseStep 6085145 = 4563859) B4563859
theorem B84408875 : Blo 1600999 84408875 := bstep (se 1 (by rfl) ⟨63306656, by rfl⟩ : syracuseStep 84408875 = 126613313) B126613313
theorem B2701903 : Blo 1600999 2701903 := bstep (se 1 (by rfl) ⟨2026427, by rfl⟩ : syracuseStep 2701903 = 4052855) B4052855
theorem B3603041 : Blo 1600999 3603041 := bstep (se 2 (by rfl) ⟨1351140, by rfl⟩ : syracuseStep 3603041 = 2702281) B2702281
theorem B8657543 : Blo 1600999 8657543 := bstep (se 1 (by rfl) ⟨6493157, by rfl⟩ : syracuseStep 8657543 = 12986315) B12986315
theorem B5405399 : Blo 1600999 5405399 := bstep (se 1 (by rfl) ⟨4054049, by rfl⟩ : syracuseStep 5405399 = 8108099) B8108099
theorem B2702153 : Blo 1600999 2702153 := bstep (se 2 (by rfl) ⟨1013307, by rfl⟩ : syracuseStep 2702153 = 2026615) B2026615
theorem B5405615 : Blo 1600999 5405615 := bstep (se 1 (by rfl) ⟨4054211, by rfl⟩ : syracuseStep 5405615 = 8108423) B8108423
theorem B3423151 : Blo 1600999 3423151 := bstep (se 1 (by rfl) ⟨2567363, by rfl⟩ : syracuseStep 3423151 = 5134727) B5134727
theorem B3603383 : Blo 1600999 3603383 := bstep (se 1 (by rfl) ⟨2702537, by rfl⟩ : syracuseStep 3603383 = 5405075) B5405075
theorem B1801255 : Blo 1600999 1801255 := bstep (se 1 (by rfl) ⟨1350941, by rfl⟩ : syracuseStep 1801255 = 2701883) B2701883
theorem B12172355 : Blo 1600999 12172355 := bstep (se 1 (by rfl) ⟨9129266, by rfl⟩ : syracuseStep 12172355 = 18258533) B18258533
theorem B2702585 : Blo 1600999 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B6585725 : Blo 1600999 6585725 := bstep (se 3 (by rfl) ⟨1234823, by rfl⟩ : syracuseStep 6585725 = 2469647) B2469647
theorem B2702767 : Blo 1600999 2702767 := bstep (se 1 (by rfl) ⟨2027075, by rfl⟩ : syracuseStep 2702767 = 4054151) B4054151
theorem B5709257 : Blo 1600999 5709257 := bstep (se 2 (by rfl) ⟨2140971, by rfl⟩ : syracuseStep 5709257 = 4281943) B4281943
theorem B26328563 : Blo 1600999 26328563 := bstep (se 1 (by rfl) ⟨19746422, by rfl⟩ : syracuseStep 26328563 = 39492845) B39492845
theorem B2702855 : Blo 1600999 2702855 := bstep (se 1 (by rfl) ⟨2027141, by rfl⟩ : syracuseStep 2702855 = 4054283) B4054283
theorem B3603977 : Blo 1600999 3603977 := bstep (se 2 (by rfl) ⟨1351491, by rfl⟩ : syracuseStep 3603977 = 2702983) B2702983
theorem B23092775 : Blo 1600999 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B2703199 : Blo 1600999 2703199 := bstep (se 1 (by rfl) ⟨2027399, by rfl⟩ : syracuseStep 2703199 = 4054799) B4054799
theorem B3604319 : Blo 1600999 3604319 := bstep (se 1 (by rfl) ⟨2703239, by rfl⟩ : syracuseStep 3604319 = 5406479) B5406479
theorem B10264481 : Blo 1600999 10264481 := bstep (se 2 (by rfl) ⟨3849180, by rfl⟩ : syracuseStep 10264481 = 7698361) B7698361
theorem B2703287 : Blo 1600999 2703287 := bstep (se 1 (by rfl) ⟨2027465, by rfl⟩ : syracuseStep 2703287 = 4054931) B4054931
theorem B4055305 : Blo 1600999 4055305 := bstep (se 2 (by rfl) ⟨1520739, by rfl⟩ : syracuseStep 4055305 = 3041479) B3041479
theorem B1802587 : Blo 1600999 1802587 := bstep (se 1 (by rfl) ⟨1351940, by rfl⟩ : syracuseStep 1802587 = 2703881) B2703881
theorem B6078827 : Blo 1600999 6078827 := bstep (se 1 (by rfl) ⟨4559120, by rfl⟩ : syracuseStep 6078827 = 9118241) B9118241
theorem B3653999 : Blo 1600999 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B14614937 : Blo 1600999 14614937 := bstep (se 2 (by rfl) ⟨5480601, by rfl⟩ : syracuseStep 14614937 = 10961203) B10961203
theorem B41058737 : Blo 1600999 41058737 := bstep (se 2 (by rfl) ⟨15397026, by rfl⟩ : syracuseStep 41058737 = 30794053) B30794053
theorem B1802695 : Blo 1600999 1802695 := bstep (se 1 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 1802695 = 2704043) B2704043
theorem B12329441 : Blo 1600999 12329441 := bstep (se 2 (by rfl) ⟨4623540, by rfl⟩ : syracuseStep 12329441 = 9247081) B9247081
theorem B6078995 : Blo 1600999 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B2703935 : Blo 1600999 2703935 := bstep (se 1 (by rfl) ⟨2027951, by rfl⟩ : syracuseStep 2703935 = 4055903) B4055903
theorem B13173463 : Blo 1600999 13173463 := bstep (se 1 (by rfl) ⟨9880097, by rfl⟩ : syracuseStep 13173463 = 19760195) B19760195
theorem B3851027 : Blo 1600999 3851027 := bstep (se 1 (by rfl) ⟨2888270, by rfl⟩ : syracuseStep 3851027 = 5776541) B5776541
theorem B1803055 : Blo 1600999 1803055 := bstep (se 1 (by rfl) ⟨1352291, by rfl⟩ : syracuseStep 1803055 = 2704583) B2704583
theorem B3605327 : Blo 1600999 3605327 := bstep (se 1 (by rfl) ⟨2703995, by rfl⟩ : syracuseStep 3605327 = 5407991) B5407991
theorem B1803163 : Blo 1600999 1803163 := bstep (se 1 (by rfl) ⟨1352372, by rfl⟩ : syracuseStep 1803163 = 2704745) B2704745
theorem B3605543 : Blo 1600999 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B4621511 : Blo 1600999 4621511 := bstep (se 1 (by rfl) ⟨3466133, by rfl⟩ : syracuseStep 4621511 = 6932267) B6932267
theorem B2401499 : Blo 1600999 2401499 := bstep (se 1 (by rfl) ⟨1801124, by rfl⟩ : syracuseStep 2401499 = 3602249) B3602249
theorem B3605723 : Blo 1600999 3605723 := bstep (se 1 (by rfl) ⟨2704292, by rfl⟩ : syracuseStep 3605723 = 5408585) B5408585
theorem B2704603 : Blo 1600999 2704603 := bstep (se 1 (by rfl) ⟨2028452, by rfl⟩ : syracuseStep 2704603 = 4056905) B4056905
theorem B4564201 : Blo 1600999 4564201 := bstep (se 2 (by rfl) ⟨1711575, by rfl⟩ : syracuseStep 4564201 = 3423151) B3423151
theorem B12166523 : Blo 1600999 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B2401673 : Blo 1600999 2401673 := bstep (se 2 (by rfl) ⟨900627, by rfl⟩ : syracuseStep 2401673 = 1801255) B1801255
theorem B2164105 : Blo 1600999 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B3605921 : Blo 1600999 3605921 := bstep (se 2 (by rfl) ⟨1352220, by rfl⟩ : syracuseStep 3605921 = 2704441) B2704441
theorem B5776829 : Blo 1600999 5776829 := bstep (se 3 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 5776829 = 2166311) B2166311
theorem B31196729 : Blo 1600999 31196729 := bstep (se 2 (by rfl) ⟨11698773, by rfl⟩ : syracuseStep 31196729 = 23397547) B23397547
theorem B2434655 : Blo 1600999 2434655 := bstep (se 1 (by rfl) ⟨1825991, by rfl⟩ : syracuseStep 2434655 = 3651983) B3651983
theorem B4056763 : Blo 1600999 4056763 := bstep (se 1 (by rfl) ⟨3042572, by rfl⟩ : syracuseStep 4056763 = 6085145) B6085145
theorem B56272583 : Blo 1600999 56272583 := bstep (se 1 (by rfl) ⟨42204437, by rfl⟩ : syracuseStep 56272583 = 84408875) B84408875
theorem B2402027 : Blo 1600999 2402027 := bstep (se 1 (by rfl) ⟨1801520, by rfl⟩ : syracuseStep 2402027 = 3603041) B3603041
theorem B2402255 : Blo 1600999 2402255 := bstep (se 1 (by rfl) ⟨1801691, by rfl⟩ : syracuseStep 2402255 = 3603383) B3603383
theorem B3606479 : Blo 1600999 3606479 := bstep (se 1 (by rfl) ⟨2704859, by rfl⟩ : syracuseStep 3606479 = 5409719) B5409719
theorem B38979569 : Blo 1600999 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B5408801 : Blo 1600999 5408801 := bstep (se 2 (by rfl) ⟨2028300, by rfl⟩ : syracuseStep 5408801 = 4056601) B4056601
theorem B2402651 : Blo 1600999 2402651 := bstep (se 1 (by rfl) ⟨1801988, by rfl⟩ : syracuseStep 2402651 = 3603977) B3603977
theorem B15395183 : Blo 1600999 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B35096975 : Blo 1600999 35096975 := bstep (se 1 (by rfl) ⟨26322731, by rfl⟩ : syracuseStep 35096975 = 52645463) B52645463
theorem B4868603 : Blo 1600999 4868603 := bstep (se 1 (by rfl) ⟨3651452, by rfl⟩ : syracuseStep 4868603 = 7302905) B7302905
theorem B8112635 : Blo 1600999 8112635 := bstep (se 1 (by rfl) ⟨6084476, by rfl⟩ : syracuseStep 8112635 = 12168953) B12168953
theorem B2402879 : Blo 1600999 2402879 := bstep (se 1 (by rfl) ⟨1802159, by rfl⟩ : syracuseStep 2402879 = 3604319) B3604319
theorem B6842987 : Blo 1600999 6842987 := bstep (se 1 (by rfl) ⟨5132240, by rfl⟩ : syracuseStep 6842987 = 10264481) B10264481
theorem B6843055 : Blo 1600999 6843055 := bstep (se 1 (by rfl) ⟨5132291, by rfl⟩ : syracuseStep 6843055 = 10264583) B10264583
theorem B2402999 : Blo 1600999 2402999 := bstep (se 1 (by rfl) ⟨1802249, by rfl⟩ : syracuseStep 2402999 = 3604499) B3604499
theorem B2886367 : Blo 1600999 2886367 := bstep (se 1 (by rfl) ⟨2164775, by rfl⟩ : syracuseStep 2886367 = 4329551) B4329551
theorem B2403227 : Blo 1600999 2403227 := bstep (se 1 (by rfl) ⟨1802420, by rfl⟩ : syracuseStep 2403227 = 3604841) B3604841
theorem B9120883 : Blo 1600999 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B27741455 : Blo 1600999 27741455 := bstep (se 1 (by rfl) ⟨20806091, by rfl⟩ : syracuseStep 27741455 = 41612183) B41612183
theorem B3247391 : Blo 1600999 3247391 := bstep (se 1 (by rfl) ⟨2435543, by rfl⟩ : syracuseStep 3247391 = 4871087) B4871087
theorem B2403623 : Blo 1600999 2403623 := bstep (se 1 (by rfl) ⟨1802717, by rfl⟩ : syracuseStep 2403623 = 3605435) B3605435
theorem B6081911 : Blo 1600999 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B2403707 : Blo 1600999 2403707 := bstep (se 1 (by rfl) ⟨1802780, by rfl⟩ : syracuseStep 2403707 = 3605561) B3605561
theorem B8105345 : Blo 1600999 8105345 := bstep (se 2 (by rfl) ⟨3039504, by rfl⟩ : syracuseStep 8105345 = 6079009) B6079009
theorem B8113607 : Blo 1600999 8113607 := bstep (se 1 (by rfl) ⟨6085205, by rfl⟩ : syracuseStep 8113607 = 12170411) B12170411
theorem B2403833 : Blo 1600999 2403833 := bstep (se 2 (by rfl) ⟨901437, by rfl⟩ : syracuseStep 2403833 = 1802875) B1802875
theorem B1601019 : Blo 1600999 1601019 := bstep (se 1 (by rfl) ⟨1200764, by rfl⟩ : syracuseStep 1601019 = 2401529) B2401529
theorem B1601087 : Blo 1600999 1601087 := bstep (se 1 (by rfl) ⟨1200815, by rfl⟩ : syracuseStep 1601087 = 2401631) B2401631
theorem B1601095 : Blo 1600999 1601095 := bstep (se 1 (by rfl) ⟨1200821, by rfl⟩ : syracuseStep 1601095 = 2401643) B2401643
theorem B2403935 : Blo 1600999 2403935 := bstep (se 1 (by rfl) ⟨1802951, by rfl⟩ : syracuseStep 2403935 = 3605903) B3605903
theorem B14814829 : Blo 1600999 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B6844013 : Blo 1600999 6844013 := bstep (se 3 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 6844013 = 2566505) B2566505
theorem B6844115 : Blo 1600999 6844115 := bstep (se 1 (by rfl) ⟨5133086, by rfl⟩ : syracuseStep 6844115 = 10266173) B10266173
theorem B1601247 : Blo 1600999 1601247 := bstep (se 1 (by rfl) ⟨1200935, by rfl⟩ : syracuseStep 1601247 = 2401871) B2401871
theorem B4869895 : Blo 1600999 4869895 := bstep (se 1 (by rfl) ⟨3652421, by rfl⟩ : syracuseStep 4869895 = 7304843) B7304843
theorem B8113931 : Blo 1600999 8113931 := bstep (se 1 (by rfl) ⟨6085448, by rfl⟩ : syracuseStep 8113931 = 12170897) B12170897
theorem B1601327 : Blo 1600999 1601327 := bstep (se 1 (by rfl) ⟨1200995, by rfl⟩ : syracuseStep 1601327 = 2401991) B2401991
theorem B5558063 : Blo 1600999 5558063 := bstep (se 1 (by rfl) ⟨4168547, by rfl⟩ : syracuseStep 5558063 = 8337095) B8337095
theorem B2404151 : Blo 1600999 2404151 := bstep (se 1 (by rfl) ⟨1803113, by rfl⟩ : syracuseStep 2404151 = 3606227) B3606227
theorem B61607789 : Blo 1600999 61607789 := bstep (se 3 (by rfl) ⟨11551460, by rfl⟩ : syracuseStep 61607789 = 23102921) B23102921
theorem B1601435 : Blo 1600999 1601435 := bstep (se 1 (by rfl) ⟨1201076, by rfl⟩ : syracuseStep 1601435 = 2402153) B2402153
theorem B1601487 : Blo 1600999 1601487 := bstep (se 1 (by rfl) ⟨1201115, by rfl⟩ : syracuseStep 1601487 = 2402231) B2402231
theorem B1601511 : Blo 1600999 1601511 := bstep (se 1 (by rfl) ⟨1201133, by rfl⟩ : syracuseStep 1601511 = 2402267) B2402267
theorem B8105993 : Blo 1600999 8105993 := bstep (se 2 (by rfl) ⟨3039747, by rfl⟩ : syracuseStep 8105993 = 6079495) B6079495
theorem B7696403 : Blo 1600999 7696403 := bstep (se 1 (by rfl) ⟨5772302, by rfl⟩ : syracuseStep 7696403 = 11544605) B11544605
theorem B103886873 : Blo 1600999 103886873 := bstep (se 2 (by rfl) ⟨38957577, by rfl⟩ : syracuseStep 103886873 = 77915155) B77915155
theorem B2404457 : Blo 1600999 2404457 := bstep (se 2 (by rfl) ⟨901671, by rfl⟩ : syracuseStep 2404457 = 1803343) B1803343
theorem B8106155 : Blo 1600999 8106155 := bstep (se 1 (by rfl) ⟨6079616, by rfl⟩ : syracuseStep 8106155 = 12159233) B12159233
theorem B1601823 : Blo 1600999 1601823 := bstep (se 1 (by rfl) ⟨1201367, by rfl⟩ : syracuseStep 1601823 = 2402735) B2402735
theorem B1601883 : Blo 1600999 1601883 := bstep (se 1 (by rfl) ⟨1201412, by rfl⟩ : syracuseStep 1601883 = 2402825) B2402825
theorem B6844763 : Blo 1600999 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B1601903 : Blo 1600999 1601903 := bstep (se 1 (by rfl) ⟨1201427, by rfl⟩ : syracuseStep 1601903 = 2402855) B2402855
theorem B1601959 : Blo 1600999 1601959 := bstep (se 1 (by rfl) ⟨1201469, by rfl⟩ : syracuseStep 1601959 = 2402939) B2402939
theorem B5771695 : Blo 1600999 5771695 := bstep (se 1 (by rfl) ⟨4328771, by rfl⟩ : syracuseStep 5771695 = 8657543) B8657543
theorem B1602043 : Blo 1600999 1602043 := bstep (se 1 (by rfl) ⟨1201532, by rfl⟩ : syracuseStep 1602043 = 2403065) B2403065
theorem B1602111 : Blo 1600999 1602111 := bstep (se 1 (by rfl) ⟨1201583, by rfl⟩ : syracuseStep 1602111 = 2403167) B2403167
theorem B1602119 : Blo 1600999 1602119 := bstep (se 1 (by rfl) ⟨1201589, by rfl⟩ : syracuseStep 1602119 = 2403179) B2403179
theorem B8106641 : Blo 1600999 8106641 := bstep (se 2 (by rfl) ⟨3039990, by rfl⟩ : syracuseStep 8106641 = 6079981) B6079981
theorem B8114903 : Blo 1600999 8114903 := bstep (se 1 (by rfl) ⟨6086177, by rfl⟩ : syracuseStep 8114903 = 12172355) B12172355
theorem B1602271 : Blo 1600999 1602271 := bstep (se 1 (by rfl) ⟨1201703, by rfl⟩ : syracuseStep 1602271 = 2403407) B2403407
theorem B3420947 : Blo 1600999 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B1602351 : Blo 1600999 1602351 := bstep (se 1 (by rfl) ⟨1201763, by rfl⟩ : syracuseStep 1602351 = 2403527) B2403527
theorem B3847067 : Blo 1600999 3847067 := bstep (se 1 (by rfl) ⟨2885300, by rfl⟩ : syracuseStep 3847067 = 5770601) B5770601
theorem B1602459 : Blo 1600999 1602459 := bstep (se 1 (by rfl) ⟨1201844, by rfl⟩ : syracuseStep 1602459 = 2403689) B2403689
theorem B8221601 : Blo 1600999 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B10269605 : Blo 1600999 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B1602511 : Blo 1600999 1602511 := bstep (se 1 (by rfl) ⟨1201883, by rfl⟩ : syracuseStep 1602511 = 2403767) B2403767
theorem B3806171 : Blo 1600999 3806171 := bstep (se 1 (by rfl) ⟨2854628, by rfl⟩ : syracuseStep 3806171 = 5709257) B5709257
theorem B1602535 : Blo 1600999 1602535 := bstep (se 1 (by rfl) ⟨1201901, by rfl⟩ : syracuseStep 1602535 = 2403803) B2403803
theorem B17552375 : Blo 1600999 17552375 := bstep (se 1 (by rfl) ⟨13164281, by rfl⟩ : syracuseStep 17552375 = 26328563) B26328563
theorem B6845431 : Blo 1600999 6845431 := bstep (se 1 (by rfl) ⟨5134073, by rfl⟩ : syracuseStep 6845431 = 10268147) B10268147
theorem B6845447 : Blo 1600999 6845447 := bstep (se 1 (by rfl) ⟨5134085, by rfl⟩ : syracuseStep 6845447 = 10268171) B10268171
theorem B21083261 : Blo 1600999 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B1602847 : Blo 1600999 1602847 := bstep (se 1 (by rfl) ⟨1202135, by rfl⟩ : syracuseStep 1602847 = 2404271) B2404271
theorem B1602907 : Blo 1600999 1602907 := bstep (se 1 (by rfl) ⟨1202180, by rfl⟩ : syracuseStep 1602907 = 2404361) B2404361
theorem B4330847 : Blo 1600999 4330847 := bstep (se 1 (by rfl) ⟨3248135, by rfl⟩ : syracuseStep 4330847 = 6496271) B6496271
theorem B10016095 : Blo 1600999 10016095 := bstep (se 1 (by rfl) ⟨7512071, by rfl⟩ : syracuseStep 10016095 = 15024143) B15024143
theorem B1602927 : Blo 1600999 1602927 := bstep (se 1 (by rfl) ⟨1202195, by rfl⟩ : syracuseStep 1602927 = 2404391) B2404391
theorem B111048083 : Blo 1600999 111048083 := bstep (se 1 (by rfl) ⟨83286062, by rfl⟩ : syracuseStep 111048083 = 166572125) B166572125
theorem B1602983 : Blo 1600999 1602983 := bstep (se 1 (by rfl) ⟨1202237, by rfl⟩ : syracuseStep 1602983 = 2404475) B2404475
theorem B10261997 : Blo 1600999 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B5133881 : Blo 1600999 5133881 := bstep (se 2 (by rfl) ⟨1925205, by rfl⟩ : syracuseStep 5133881 = 3850411) B3850411
theorem B4331195 : Blo 1600999 4331195 := bstep (se 1 (by rfl) ⟨3248396, by rfl⟩ : syracuseStep 4331195 = 6496793) B6496793
theorem B36976499 : Blo 1600999 36976499 := bstep (se 1 (by rfl) ⟨27732374, by rfl⟩ : syracuseStep 36976499 = 55464749) B55464749
theorem B3848143 : Blo 1600999 3848143 := bstep (se 1 (by rfl) ⟨2886107, by rfl⟩ : syracuseStep 3848143 = 5772215) B5772215
theorem B4053017 : Blo 1600999 4053017 := bstep (se 2 (by rfl) ⟨1519881, by rfl⟩ : syracuseStep 4053017 = 3039763) B3039763
theorem B3602537 : Blo 1600999 3602537 := bstep (se 2 (by rfl) ⟨1350951, by rfl⟩ : syracuseStep 3602537 = 2701903) B2701903
theorem B3291401 : Blo 1600999 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B8665373 : Blo 1600999 8665373 := bstep (se 3 (by rfl) ⟨1624757, by rfl⟩ : syracuseStep 8665373 = 3249515) B3249515
theorem B56990099 : Blo 1600999 56990099 := bstep (se 1 (by rfl) ⟨42742574, by rfl⟩ : syracuseStep 56990099 = 85485149) B85485149
theorem B4053473 : Blo 1600999 4053473 := bstep (se 2 (by rfl) ⟨1520052, by rfl⟩ : syracuseStep 4053473 = 3040105) B3040105
theorem B6085115 : Blo 1600999 6085115 := bstep (se 1 (by rfl) ⟨4563836, by rfl⟩ : syracuseStep 6085115 = 9127673) B9127673
theorem B4053523 : Blo 1600999 4053523 := bstep (se 1 (by rfl) ⟨3040142, by rfl⟩ : syracuseStep 4053523 = 6080285) B6080285
theorem B15399487 : Blo 1600999 15399487 := bstep (se 1 (by rfl) ⟨11549615, by rfl⟩ : syracuseStep 15399487 = 23099231) B23099231
theorem B3603023 : Blo 1600999 3603023 := bstep (se 1 (by rfl) ⟨2702267, by rfl⟩ : syracuseStep 3603023 = 5404535) B5404535
theorem B5405291 : Blo 1600999 5405291 := bstep (se 1 (by rfl) ⟨4053968, by rfl⟩ : syracuseStep 5405291 = 8107937) B8107937
theorem B3603167 : Blo 1600999 3603167 := bstep (se 1 (by rfl) ⟨2702375, by rfl⟩ : syracuseStep 3603167 = 5404751) B5404751
theorem B1710815 : Blo 1600999 1710815 := bstep (se 1 (by rfl) ⟨1283111, by rfl⟩ : syracuseStep 1710815 = 2566223) B2566223
theorem B3849103 : Blo 1600999 3849103 := bstep (se 1 (by rfl) ⟨2886827, by rfl⟩ : syracuseStep 3849103 = 5773655) B5773655
theorem B3603419 : Blo 1600999 3603419 := bstep (se 1 (by rfl) ⟨2702564, by rfl⟩ : syracuseStep 3603419 = 5405129) B5405129
theorem B8109071 : Blo 1600999 8109071 := bstep (se 1 (by rfl) ⟨6081803, by rfl⟩ : syracuseStep 8109071 = 12163607) B12163607
theorem B3603599 : Blo 1600999 3603599 := bstep (se 1 (by rfl) ⟨2702699, by rfl⟩ : syracuseStep 3603599 = 5405399) B5405399
theorem B5405885 : Blo 1600999 5405885 := bstep (se 3 (by rfl) ⟨1013603, by rfl⟩ : syracuseStep 5405885 = 2027207) B2027207
theorem B1801435 : Blo 1600999 1801435 := bstep (se 1 (by rfl) ⟨1351076, by rfl⟩ : syracuseStep 1801435 = 2702153) B2702153
theorem B3603689 : Blo 1600999 3603689 := bstep (se 2 (by rfl) ⟨1351383, by rfl⟩ : syracuseStep 3603689 = 2702767) B2702767
theorem B3603743 : Blo 1600999 3603743 := bstep (se 1 (by rfl) ⟨2702807, by rfl⟩ : syracuseStep 3603743 = 5405615) B5405615
theorem B9125257 : Blo 1600999 9125257 := bstep (se 2 (by rfl) ⟨3421971, by rfl⟩ : syracuseStep 9125257 = 6843943) B6843943
theorem B6086087 : Blo 1600999 6086087 := bstep (se 1 (by rfl) ⟨4564565, by rfl⟩ : syracuseStep 6086087 = 9129131) B9129131
theorem B1801723 : Blo 1600999 1801723 := bstep (se 1 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 1801723 = 2702585) B2702585
theorem B4390483 : Blo 1600999 4390483 := bstep (se 1 (by rfl) ⟨3292862, by rfl⟩ : syracuseStep 4390483 = 6585725) B6585725
theorem B4562527 : Blo 1600999 4562527 := bstep (se 1 (by rfl) ⟨3421895, by rfl⟩ : syracuseStep 4562527 = 6843791) B6843791
theorem B1801903 : Blo 1600999 1801903 := bstep (se 1 (by rfl) ⟨1351427, by rfl⟩ : syracuseStep 1801903 = 2702855) B2702855
theorem B1924831 : Blo 1600999 1924831 := bstep (se 1 (by rfl) ⟨1443623, by rfl⟩ : syracuseStep 1924831 = 2887247) B2887247
theorem B8658667 : Blo 1600999 8658667 := bstep (se 1 (by rfl) ⟨6494000, by rfl⟩ : syracuseStep 8658667 = 12988001) B12988001
theorem B36986665 : Blo 1600999 36986665 := bstep (se 2 (by rfl) ⟨13869999, by rfl⟩ : syracuseStep 36986665 = 27739999) B27739999
theorem B2703145 : Blo 1600999 2703145 := bstep (se 2 (by rfl) ⟨1013679, by rfl⟩ : syracuseStep 2703145 = 2027359) B2027359
theorem B3604265 : Blo 1600999 3604265 := bstep (se 2 (by rfl) ⟨1351599, by rfl⟩ : syracuseStep 3604265 = 2703199) B2703199
theorem B4448047 : Blo 1600999 4448047 := bstep (se 1 (by rfl) ⟨3336035, by rfl⟩ : syracuseStep 4448047 = 6672071) B6672071
theorem B8109881 : Blo 1600999 8109881 := bstep (se 2 (by rfl) ⟨3041205, by rfl⟩ : syracuseStep 8109881 = 6082411) B6082411
theorem B1802191 : Blo 1600999 1802191 := bstep (se 1 (by rfl) ⟨1351643, by rfl⟩ : syracuseStep 1802191 = 2703287) B2703287
theorem B56222029 : Blo 1600999 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B5407073 : Blo 1600999 5407073 := bstep (se 2 (by rfl) ⟨2027652, by rfl⟩ : syracuseStep 5407073 = 4055305) B4055305
theorem B1802623 : Blo 1600999 1802623 := bstep (se 1 (by rfl) ⟨1351967, by rfl⟩ : syracuseStep 1802623 = 2703935) B2703935
theorem B59286005 : Blo 1600999 59286005 := bstep (se 5 (by rfl) ⟨2779031, by rfl⟩ : syracuseStep 59286005 = 5558063) B5558063
theorem B2564711 : Blo 1600999 2564711 := bstep (se 1 (by rfl) ⟨1923533, by rfl⟩ : syracuseStep 2564711 = 3847067) B3847067
theorem B5481067 : Blo 1600999 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B4563631 : Blo 1600999 4563631 := bstep (se 1 (by rfl) ⟨3422723, by rfl⟩ : syracuseStep 4563631 = 6845447) B6845447
theorem B8659709 : Blo 1600999 8659709 := bstep (se 3 (by rfl) ⟨1623695, by rfl⟩ : syracuseStep 8659709 = 3247391) B3247391
theorem B3081007 : Blo 1600999 3081007 := bstep (se 1 (by rfl) ⟨2310755, by rfl⟩ : syracuseStep 3081007 = 4621511) B4621511
theorem B18252701 : Blo 1600999 18252701 := bstep (se 3 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 18252701 = 6844763) B6844763
theorem B8111015 : Blo 1600999 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B74032055 : Blo 1600999 74032055 := bstep (se 1 (by rfl) ⟨55524041, by rfl⟩ : syracuseStep 74032055 = 111048083) B111048083
theorem B17564617 : Blo 1600999 17564617 := bstep (se 2 (by rfl) ⟨6586731, by rfl⟩ : syracuseStep 17564617 = 13173463) B13173463
theorem B3851219 : Blo 1600999 3851219 := bstep (se 1 (by rfl) ⟨2888414, by rfl⟩ : syracuseStep 3851219 = 5776829) B5776829
theorem B6841331 : Blo 1600999 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B24650999 : Blo 1600999 24650999 := bstep (se 1 (by rfl) ⟨18488249, by rfl⟩ : syracuseStep 24650999 = 36976499) B36976499
theorem B9127241 : Blo 1600999 9127241 := bstep (se 2 (by rfl) ⟨3422715, by rfl⟩ : syracuseStep 9127241 = 6845431) B6845431
theorem B25986379 : Blo 1600999 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B3605867 : Blo 1600999 3605867 := bstep (se 1 (by rfl) ⟨2704400, by rfl⟩ : syracuseStep 3605867 = 5408801) B5408801
theorem B2401691 : Blo 1600999 2401691 := bstep (se 1 (by rfl) ⟨1801268, by rfl⟩ : syracuseStep 2401691 = 3602537) B3602537
theorem B5776915 : Blo 1600999 5776915 := bstep (se 1 (by rfl) ⟨4332686, by rfl⟩ : syracuseStep 5776915 = 8665373) B8665373
theorem B23397983 : Blo 1600999 23397983 := bstep (se 1 (by rfl) ⟨17548487, by rfl⟩ : syracuseStep 23397983 = 35096975) B35096975
theorem B2401913 : Blo 1600999 2401913 := bstep (se 2 (by rfl) ⟨900717, by rfl⟩ : syracuseStep 2401913 = 1801435) B1801435
theorem B3606137 : Blo 1600999 3606137 := bstep (se 2 (by rfl) ⟨1352301, by rfl⟩ : syracuseStep 3606137 = 2704603) B2704603
theorem B3245735 : Blo 1600999 3245735 := bstep (se 1 (by rfl) ⟨2434301, by rfl⟩ : syracuseStep 3245735 = 4868603) B4868603
theorem B5408423 : Blo 1600999 5408423 := bstep (se 1 (by rfl) ⟨4056317, by rfl⟩ : syracuseStep 5408423 = 8112635) B8112635
theorem B4056743 : Blo 1600999 4056743 := bstep (se 1 (by rfl) ⟨3042557, by rfl⟩ : syracuseStep 4056743 = 6085115) B6085115
theorem B2402015 : Blo 1600999 2402015 := bstep (se 1 (by rfl) ⟨1801511, by rfl⟩ : syracuseStep 2402015 = 3603023) B3603023
theorem B13354793 : Blo 1600999 13354793 := bstep (se 2 (by rfl) ⟨5008047, by rfl⟩ : syracuseStep 13354793 = 10016095) B10016095
theorem B2402111 : Blo 1600999 2402111 := bstep (se 1 (by rfl) ⟨1801583, by rfl⟩ : syracuseStep 2402111 = 3603167) B3603167
theorem B2885473 : Blo 1600999 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B12167009 : Blo 1600999 12167009 := bstep (se 2 (by rfl) ⟨4562628, by rfl⟩ : syracuseStep 12167009 = 9125257) B9125257
theorem B2402279 : Blo 1600999 2402279 := bstep (se 1 (by rfl) ⟨1801709, by rfl⟩ : syracuseStep 2402279 = 3603419) B3603419
theorem B2402297 : Blo 1600999 2402297 := bstep (se 2 (by rfl) ⟨900861, by rfl⟩ : syracuseStep 2402297 = 1801723) B1801723
theorem B2402399 : Blo 1600999 2402399 := bstep (se 1 (by rfl) ⟨1801799, by rfl⟩ : syracuseStep 2402399 = 3603599) B3603599
theorem B19753105 : Blo 1600999 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B2402459 : Blo 1600999 2402459 := bstep (se 1 (by rfl) ⟨1801844, by rfl⟩ : syracuseStep 2402459 = 3603689) B3603689
theorem B2402495 : Blo 1600999 2402495 := bstep (se 1 (by rfl) ⟨1801871, by rfl⟩ : syracuseStep 2402495 = 3603743) B3603743
theorem B2402537 : Blo 1600999 2402537 := bstep (se 2 (by rfl) ⟨900951, by rfl⟩ : syracuseStep 2402537 = 1801903) B1801903
theorem B5409017 : Blo 1600999 5409017 := bstep (se 2 (by rfl) ⟨2028381, by rfl⟩ : syracuseStep 5409017 = 4056763) B4056763
theorem B2566441 : Blo 1600999 2566441 := bstep (se 2 (by rfl) ⟨962415, by rfl⟩ : syracuseStep 2566441 = 1924831) B1924831
theorem B5409071 : Blo 1600999 5409071 := bstep (se 1 (by rfl) ⟨4056803, by rfl⟩ : syracuseStep 5409071 = 8113607) B8113607
theorem B4057391 : Blo 1600999 4057391 := bstep (se 1 (by rfl) ⟨3043043, by rfl⟩ : syracuseStep 4057391 = 6086087) B6086087
theorem B11544889 : Blo 1600999 11544889 := bstep (se 2 (by rfl) ⟨4329333, by rfl⟩ : syracuseStep 11544889 = 8658667) B8658667
theorem B5409287 : Blo 1600999 5409287 := bstep (se 1 (by rfl) ⟨4056965, by rfl⟩ : syracuseStep 5409287 = 8113931) B8113931
theorem B2402843 : Blo 1600999 2402843 := bstep (se 1 (by rfl) ⟨1802132, by rfl⟩ : syracuseStep 2402843 = 3604265) B3604265
theorem B5130857 : Blo 1600999 5130857 := bstep (se 2 (by rfl) ⟨1924071, by rfl⟩ : syracuseStep 5130857 = 3848143) B3848143
theorem B2402921 : Blo 1600999 2402921 := bstep (se 2 (by rfl) ⟨901095, by rfl⟩ : syracuseStep 2402921 = 1802191) B1802191
theorem B5130935 : Blo 1600999 5130935 := bstep (se 1 (by rfl) ⟨3848201, by rfl⟩ : syracuseStep 5130935 = 7696403) B7696403
theorem B69257915 : Blo 1600999 69257915 := bstep (se 1 (by rfl) ⟨51943436, by rfl⟩ : syracuseStep 69257915 = 103886873) B103886873
theorem B2435999 : Blo 1600999 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B9743291 : Blo 1600999 9743291 := bstep (se 1 (by rfl) ⟨7307468, by rfl⟩ : syracuseStep 9743291 = 14614937) B14614937
theorem B27372491 : Blo 1600999 27372491 := bstep (se 1 (by rfl) ⟨20529368, by rfl⟩ : syracuseStep 27372491 = 41058737) B41058737
theorem B8219627 : Blo 1600999 8219627 := bstep (se 1 (by rfl) ⟨6164720, by rfl⟩ : syracuseStep 8219627 = 12329441) B12329441
theorem B2403449 : Blo 1600999 2403449 := bstep (se 2 (by rfl) ⟨901293, by rfl⟩ : syracuseStep 2403449 = 1802587) B1802587
theorem B5409935 : Blo 1600999 5409935 := bstep (se 1 (by rfl) ⟨4057451, by rfl⟩ : syracuseStep 5409935 = 8114903) B8114903
theorem B2280631 : Blo 1600999 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B2567351 : Blo 1600999 2567351 := bstep (se 1 (by rfl) ⟨1925513, by rfl⟩ : syracuseStep 2567351 = 3851027) B3851027
theorem B2403551 : Blo 1600999 2403551 := bstep (se 1 (by rfl) ⟨1802663, by rfl⟩ : syracuseStep 2403551 = 3605327) B3605327
theorem B7695593 : Blo 1600999 7695593 := bstep (se 2 (by rfl) ⟨2885847, by rfl⟩ : syracuseStep 7695593 = 5771695) B5771695
theorem B2403593 : Blo 1600999 2403593 := bstep (se 2 (by rfl) ⟨901347, by rfl⟩ : syracuseStep 2403593 = 1802695) B1802695
theorem B11701583 : Blo 1600999 11701583 := bstep (se 1 (by rfl) ⟨8776187, by rfl⟩ : syracuseStep 11701583 = 17552375) B17552375
theorem B8777069 : Blo 1600999 8777069 := bstep (se 3 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 8777069 = 3291401) B3291401
theorem B2403695 : Blo 1600999 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B20532649 : Blo 1600999 20532649 := bstep (se 2 (by rfl) ⟨7699743, by rfl⟩ : syracuseStep 20532649 = 15399487) B15399487
theorem B1600999 : Blo 1600999 1600999 := bstep (se 1 (by rfl) ⟨1200749, by rfl⟩ : syracuseStep 1600999 = 2401499) B2401499
theorem B2403815 : Blo 1600999 2403815 := bstep (se 1 (by rfl) ⟨1802861, by rfl⟩ : syracuseStep 2403815 = 3605723) B3605723
theorem B1601115 : Blo 1600999 1601115 := bstep (se 1 (by rfl) ⟨1200836, by rfl⟩ : syracuseStep 1601115 = 2401673) B2401673
theorem B2403947 : Blo 1600999 2403947 := bstep (se 1 (by rfl) ⟨1802960, by rfl⟩ : syracuseStep 2403947 = 3605921) B3605921
theorem B151973597 : Blo 1600999 151973597 := bstep (se 3 (by rfl) ⟨28495049, by rfl⟩ : syracuseStep 151973597 = 56990099) B56990099
theorem B2404073 : Blo 1600999 2404073 := bstep (se 2 (by rfl) ⟨901527, by rfl⟩ : syracuseStep 2404073 = 1803055) B1803055
theorem B2887463 : Blo 1600999 2887463 := bstep (se 1 (by rfl) ⟨2165597, by rfl⟩ : syracuseStep 2887463 = 4331195) B4331195
theorem B1601351 : Blo 1600999 1601351 := bstep (se 1 (by rfl) ⟨1201013, by rfl⟩ : syracuseStep 1601351 = 2402027) B2402027
theorem B2404217 : Blo 1600999 2404217 := bstep (se 2 (by rfl) ⟨901581, by rfl⟩ : syracuseStep 2404217 = 1803163) B1803163
theorem B1601503 : Blo 1600999 1601503 := bstep (se 1 (by rfl) ⟨1201127, by rfl⟩ : syracuseStep 1601503 = 2402255) B2402255
theorem B2404319 : Blo 1600999 2404319 := bstep (se 1 (by rfl) ⟨1803239, by rfl⟩ : syracuseStep 2404319 = 3606479) B3606479
theorem B12161177 : Blo 1600999 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B1601767 : Blo 1600999 1601767 := bstep (se 1 (by rfl) ⟨1201325, by rfl⟩ : syracuseStep 1601767 = 2402651) B2402651
theorem B6492413 : Blo 1600999 6492413 := bstep (se 3 (by rfl) ⟨1217327, by rfl⟩ : syracuseStep 6492413 = 2434655) B2434655
theorem B1601919 : Blo 1600999 1601919 := bstep (se 1 (by rfl) ⟨1201439, by rfl⟩ : syracuseStep 1601919 = 2402879) B2402879
theorem B1601999 : Blo 1600999 1601999 := bstep (se 1 (by rfl) ⟨1201499, by rfl⟩ : syracuseStep 1601999 = 2402999) B2402999
theorem B1602151 : Blo 1600999 1602151 := bstep (se 1 (by rfl) ⟨1201613, by rfl⟩ : syracuseStep 1602151 = 2403227) B2403227
theorem B5853977 : Blo 1600999 5853977 := bstep (se 2 (by rfl) ⟨2195241, by rfl⟩ : syracuseStep 5853977 = 4390483) B4390483
theorem B6083369 : Blo 1600999 6083369 := bstep (se 2 (by rfl) ⟨2281263, by rfl⟩ : syracuseStep 6083369 = 4562527) B4562527
theorem B18494303 : Blo 1600999 18494303 := bstep (se 1 (by rfl) ⟨13870727, by rfl⟩ : syracuseStep 18494303 = 27741455) B27741455
theorem B1602415 : Blo 1600999 1602415 := bstep (se 1 (by rfl) ⟨1201811, by rfl⟩ : syracuseStep 1602415 = 2403623) B2403623
theorem B1602471 : Blo 1600999 1602471 := bstep (se 1 (by rfl) ⟨1201853, by rfl⟩ : syracuseStep 1602471 = 2403707) B2403707
theorem B5403563 : Blo 1600999 5403563 := bstep (se 1 (by rfl) ⟨4052672, by rfl⟩ : syracuseStep 5403563 = 8105345) B8105345
theorem B1602555 : Blo 1600999 1602555 := bstep (se 1 (by rfl) ⟨1201916, by rfl⟩ : syracuseStep 1602555 = 2403833) B2403833
theorem B6493193 : Blo 1600999 6493193 := bstep (se 2 (by rfl) ⟨2434947, by rfl⟩ : syracuseStep 6493193 = 4869895) B4869895
theorem B1602623 : Blo 1600999 1602623 := bstep (se 1 (by rfl) ⟨1201967, by rfl⟩ : syracuseStep 1602623 = 2403935) B2403935
theorem B1602767 : Blo 1600999 1602767 := bstep (se 1 (by rfl) ⟨1202075, by rfl⟩ : syracuseStep 1602767 = 2404151) B2404151
theorem B41071859 : Blo 1600999 41071859 := bstep (se 1 (by rfl) ⟨30803894, by rfl⟩ : syracuseStep 41071859 = 61607789) B61607789
theorem B5403995 : Blo 1600999 5403995 := bstep (se 1 (by rfl) ⟨4052996, by rfl⟩ : syracuseStep 5403995 = 8105993) B8105993
theorem B1602971 : Blo 1600999 1602971 := bstep (se 1 (by rfl) ⟨1202228, by rfl⟩ : syracuseStep 1602971 = 2404457) B2404457
theorem B5404103 : Blo 1600999 5404103 := bstep (se 1 (by rfl) ⟨4053077, by rfl⟩ : syracuseStep 5404103 = 8106155) B8106155
theorem B4052551 : Blo 1600999 4052551 := bstep (se 1 (by rfl) ⟨3039413, by rfl⟩ : syracuseStep 4052551 = 6078827) B6078827
theorem B4052663 : Blo 1600999 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B5404427 : Blo 1600999 5404427 := bstep (se 1 (by rfl) ⟨4053320, by rfl⟩ : syracuseStep 5404427 = 8106641) B8106641
theorem B2537447 : Blo 1600999 2537447 := bstep (se 1 (by rfl) ⟨1903085, by rfl⟩ : syracuseStep 2537447 = 3806171) B3806171
theorem B5404697 : Blo 1600999 5404697 := bstep (se 2 (by rfl) ⟨2026761, by rfl⟩ : syracuseStep 5404697 = 4053523) B4053523
theorem B9124073 : Blo 1600999 9124073 := bstep (se 2 (by rfl) ⟨3421527, by rfl⟩ : syracuseStep 9124073 = 6843055) B6843055
theorem B11548925 : Blo 1600999 11548925 := bstep (se 3 (by rfl) ⟨2165423, by rfl⟩ : syracuseStep 11548925 = 4330847) B4330847
theorem B3848489 : Blo 1600999 3848489 := bstep (se 2 (by rfl) ⟨1443183, by rfl⟩ : syracuseStep 3848489 = 2886367) B2886367
theorem B20797819 : Blo 1600999 20797819 := bstep (se 1 (by rfl) ⟨15598364, by rfl⟩ : syracuseStep 20797819 = 31196729) B31196729
theorem B3422587 : Blo 1600999 3422587 := bstep (se 1 (by rfl) ⟨2566940, by rfl⟩ : syracuseStep 3422587 = 5133881) B5133881
theorem B2702011 : Blo 1600999 2702011 := bstep (se 1 (by rfl) ⟨2026508, by rfl⟩ : syracuseStep 2702011 = 4053017) B4053017
theorem B10263455 : Blo 1600999 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B6085601 : Blo 1600999 6085601 := bstep (se 2 (by rfl) ⟨2282100, by rfl⟩ : syracuseStep 6085601 = 4564201) B4564201
theorem B2702315 : Blo 1600999 2702315 := bstep (se 1 (by rfl) ⟨2026736, by rfl⟩ : syracuseStep 2702315 = 4053473) B4053473
theorem B3603527 : Blo 1600999 3603527 := bstep (se 1 (by rfl) ⟨2702645, by rfl⟩ : syracuseStep 3603527 = 5405291) B5405291
theorem B4561991 : Blo 1600999 4561991 := bstep (se 1 (by rfl) ⟨3421493, by rfl⟩ : syracuseStep 4561991 = 6842987) B6842987
theorem B150060221 : Blo 1600999 150060221 := bstep (se 3 (by rfl) ⟨28136291, by rfl⟩ : syracuseStep 150060221 = 56272583) B56272583
theorem B4562173 : Blo 1600999 4562173 := bstep (se 3 (by rfl) ⟨855407, by rfl⟩ : syracuseStep 4562173 = 1710815) B1710815
theorem B5406047 : Blo 1600999 5406047 := bstep (se 1 (by rfl) ⟨4054535, by rfl⟩ : syracuseStep 5406047 = 8109071) B8109071
theorem B20528549 : Blo 1600999 20528549 := bstep (se 4 (by rfl) ⟨1924551, by rfl⟩ : syracuseStep 20528549 = 3849103) B3849103
theorem B3603923 : Blo 1600999 3603923 := bstep (se 1 (by rfl) ⟨2702942, by rfl⟩ : syracuseStep 3603923 = 5405885) B5405885
theorem B4054607 : Blo 1600999 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B49315553 : Blo 1600999 49315553 := bstep (se 2 (by rfl) ⟨18493332, by rfl⟩ : syracuseStep 49315553 = 36986665) B36986665
theorem B3604193 : Blo 1600999 3604193 := bstep (se 2 (by rfl) ⟨1351572, by rfl⟩ : syracuseStep 3604193 = 2703145) B2703145
theorem B5930729 : Blo 1600999 5930729 := bstep (se 2 (by rfl) ⟨2224023, by rfl⟩ : syracuseStep 5930729 = 4448047) B4448047
theorem B4562675 : Blo 1600999 4562675 := bstep (se 1 (by rfl) ⟨3422006, by rfl⟩ : syracuseStep 4562675 = 6844013) B6844013
theorem B27385613 : Blo 1600999 27385613 := bstep (se 3 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 27385613 = 10269605) B10269605
theorem B4562743 : Blo 1600999 4562743 := bstep (se 1 (by rfl) ⟨3422057, by rfl⟩ : syracuseStep 4562743 = 6844115) B6844115
theorem B5406587 : Blo 1600999 5406587 := bstep (se 1 (by rfl) ⟨4054940, by rfl⟩ : syracuseStep 5406587 = 8109881) B8109881
theorem B26337473 : Blo 1600999 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B3604715 : Blo 1600999 3604715 := bstep (se 1 (by rfl) ⟨2703536, by rfl⟩ : syracuseStep 3604715 = 5407073) B5407073
theorem B15393185 : Blo 1600999 15393185 := bstep (se 2 (by rfl) ⟨5772444, by rfl⟩ : syracuseStep 15393185 = 11544889) B11544889
theorem B4563449 : Blo 1600999 4563449 := bstep (se 2 (by rfl) ⟨1711293, by rfl⟩ : syracuseStep 4563449 = 3422587) B3422587
theorem B4055579 : Blo 1600999 4055579 := bstep (se 1 (by rfl) ⟨3041684, by rfl⟩ : syracuseStep 4055579 = 6083369) B6083369
theorem B5407343 : Blo 1600999 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B7308089 : Blo 1600999 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B16433999 : Blo 1600999 16433999 := bstep (se 1 (by rfl) ⟨12325499, by rfl⟩ : syracuseStep 16433999 = 24650999) B24650999
theorem B15598655 : Blo 1600999 15598655 := bstep (se 1 (by rfl) ⟨11698991, by rfl⟩ : syracuseStep 15598655 = 23397983) B23397983
theorem B2163823 : Blo 1600999 2163823 := bstep (se 1 (by rfl) ⟨1622867, by rfl⟩ : syracuseStep 2163823 = 3245735) B3245735
theorem B3605615 : Blo 1600999 3605615 := bstep (se 1 (by rfl) ⟨2704211, by rfl⟩ : syracuseStep 3605615 = 5408423) B5408423
theorem B2704495 : Blo 1600999 2704495 := bstep (se 1 (by rfl) ⟨2028371, by rfl⟩ : syracuseStep 2704495 = 4056743) B4056743
theorem B8111339 : Blo 1600999 8111339 := bstep (se 1 (by rfl) ⟨6083504, by rfl⟩ : syracuseStep 8111339 = 12167009) B12167009
theorem B3606011 : Blo 1600999 3606011 := bstep (se 1 (by rfl) ⟨2704508, by rfl⟩ : syracuseStep 3606011 = 5409017) B5409017
theorem B2565659 : Blo 1600999 2565659 := bstep (se 1 (by rfl) ⟨1924244, by rfl⟩ : syracuseStep 2565659 = 3848489) B3848489
theorem B3606047 : Blo 1600999 3606047 := bstep (se 1 (by rfl) ⟨2704535, by rfl⟩ : syracuseStep 3606047 = 5409071) B5409071
theorem B2704927 : Blo 1600999 2704927 := bstep (se 1 (by rfl) ⟨2028695, by rfl⟩ : syracuseStep 2704927 = 4057391) B4057391
theorem B3040841 : Blo 1600999 3040841 := bstep (se 2 (by rfl) ⟨1140315, by rfl⟩ : syracuseStep 3040841 = 2280631) B2280631
theorem B3606191 : Blo 1600999 3606191 := bstep (se 1 (by rfl) ⟨2704643, by rfl⟩ : syracuseStep 3606191 = 5409287) B5409287
theorem B46171943 : Blo 1600999 46171943 := bstep (se 1 (by rfl) ⟨34628957, by rfl⟩ : syracuseStep 46171943 = 69257915) B69257915
theorem B6842303 : Blo 1600999 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B4057067 : Blo 1600999 4057067 := bstep (se 1 (by rfl) ⟨3042800, by rfl⟩ : syracuseStep 4057067 = 6085601) B6085601
theorem B7702553 : Blo 1600999 7702553 := bstep (se 2 (by rfl) ⟨2888457, by rfl⟩ : syracuseStep 7702553 = 5776915) B5776915
theorem B2402351 : Blo 1600999 2402351 := bstep (se 1 (by rfl) ⟨1801763, by rfl⟩ : syracuseStep 2402351 = 3603527) B3603527
theorem B3041327 : Blo 1600999 3041327 := bstep (se 1 (by rfl) ⟨2280995, by rfl⟩ : syracuseStep 3041327 = 4561991) B4561991
theorem B3606623 : Blo 1600999 3606623 := bstep (se 1 (by rfl) ⟨2704967, by rfl⟩ : syracuseStep 3606623 = 5409935) B5409935
theorem B5130395 : Blo 1600999 5130395 := bstep (se 1 (by rfl) ⟨3847796, by rfl⟩ : syracuseStep 5130395 = 7695593) B7695593
theorem B7801055 : Blo 1600999 7801055 := bstep (se 1 (by rfl) ⟨5850791, by rfl⟩ : syracuseStep 7801055 = 11701583) B11701583
theorem B5851379 : Blo 1600999 5851379 := bstep (se 1 (by rfl) ⟨4388534, by rfl⟩ : syracuseStep 5851379 = 8777069) B8777069
theorem B49318141 : Blo 1600999 49318141 := bstep (se 3 (by rfl) ⟨9247151, by rfl⟩ : syracuseStep 49318141 = 18494303) B18494303
theorem B2402615 : Blo 1600999 2402615 := bstep (se 1 (by rfl) ⟨1801961, by rfl⟩ : syracuseStep 2402615 = 3603923) B3603923
theorem B32877035 : Blo 1600999 32877035 := bstep (se 1 (by rfl) ⟨24657776, by rfl⟩ : syracuseStep 32877035 = 49315553) B49315553
theorem B2402795 : Blo 1600999 2402795 := bstep (se 1 (by rfl) ⟨1802096, by rfl⟩ : syracuseStep 2402795 = 3604193) B3604193
theorem B3041783 : Blo 1600999 3041783 := bstep (se 1 (by rfl) ⟨2281337, by rfl⟩ : syracuseStep 3041783 = 4562675) B4562675
theorem B4328275 : Blo 1600999 4328275 := bstep (se 1 (by rfl) ⟨3246206, by rfl⟩ : syracuseStep 4328275 = 6492413) B6492413
theorem B2403497 : Blo 1600999 2403497 := bstep (se 2 (by rfl) ⟨901311, by rfl⟩ : syracuseStep 2403497 = 1802623) B1802623
theorem B3902651 : Blo 1600999 3902651 := bstep (se 1 (by rfl) ⟨2926988, by rfl⟩ : syracuseStep 3902651 = 5853977) B5853977
theorem B12168467 : Blo 1600999 12168467 := bstep (se 1 (by rfl) ⟨9126350, by rfl⟩ : syracuseStep 12168467 = 18252701) B18252701
theorem B2567479 : Blo 1600999 2567479 := bstep (se 1 (by rfl) ⟨1925609, by rfl⟩ : syracuseStep 2567479 = 3851219) B3851219
theorem B4328795 : Blo 1600999 4328795 := bstep (se 1 (by rfl) ⟨3246596, by rfl⟩ : syracuseStep 4328795 = 6493193) B6493193
theorem B27381239 : Blo 1600999 27381239 := bstep (se 1 (by rfl) ⟨20535929, by rfl⟩ : syracuseStep 27381239 = 41071859) B41071859
theorem B2403911 : Blo 1600999 2403911 := bstep (se 1 (by rfl) ⟨1802933, by rfl⟩ : syracuseStep 2403911 = 3605867) B3605867
theorem B1601127 : Blo 1600999 1601127 := bstep (se 1 (by rfl) ⟨1200845, by rfl⟩ : syracuseStep 1601127 = 2401691) B2401691
theorem B4108009 : Blo 1600999 4108009 := bstep (se 2 (by rfl) ⟨1540503, by rfl⟩ : syracuseStep 4108009 = 3081007) B3081007
theorem B1601275 : Blo 1600999 1601275 := bstep (se 1 (by rfl) ⟨1200956, by rfl⟩ : syracuseStep 1601275 = 2401913) B2401913
theorem B2404091 : Blo 1600999 2404091 := bstep (se 1 (by rfl) ⟨1803068, by rfl⟩ : syracuseStep 2404091 = 3606137) B3606137
theorem B1601343 : Blo 1600999 1601343 := bstep (se 1 (by rfl) ⟨1201007, by rfl⟩ : syracuseStep 1601343 = 2402015) B2402015
theorem B1601407 : Blo 1600999 1601407 := bstep (se 1 (by rfl) ⟨1201055, by rfl⟩ : syracuseStep 1601407 = 2402111) B2402111
theorem B1601519 : Blo 1600999 1601519 := bstep (se 1 (by rfl) ⟨1201139, by rfl⟩ : syracuseStep 1601519 = 2402279) B2402279
theorem B1601531 : Blo 1600999 1601531 := bstep (se 1 (by rfl) ⟨1201148, by rfl⟩ : syracuseStep 1601531 = 2402297) B2402297
theorem B1601599 : Blo 1600999 1601599 := bstep (se 1 (by rfl) ⟨1201199, by rfl⟩ : syracuseStep 1601599 = 2402399) B2402399
theorem B1601639 : Blo 1600999 1601639 := bstep (se 1 (by rfl) ⟨1201229, by rfl⟩ : syracuseStep 1601639 = 2402459) B2402459
theorem B1601663 : Blo 1600999 1601663 := bstep (se 1 (by rfl) ⟨1201247, by rfl⟩ : syracuseStep 1601663 = 2402495) B2402495
theorem B1601691 : Blo 1600999 1601691 := bstep (se 1 (by rfl) ⟨1201268, by rfl⟩ : syracuseStep 1601691 = 2402537) B2402537
theorem B6082715 : Blo 1600999 6082715 := bstep (se 1 (by rfl) ⟨4562036, by rfl⟩ : syracuseStep 6082715 = 9124073) B9124073
theorem B6082897 : Blo 1600999 6082897 := bstep (se 2 (by rfl) ⟨2281086, by rfl⟩ : syracuseStep 6082897 = 4562173) B4562173
theorem B1601895 : Blo 1600999 1601895 := bstep (se 1 (by rfl) ⟨1201421, by rfl⟩ : syracuseStep 1601895 = 2402843) B2402843
theorem B3420571 : Blo 1600999 3420571 := bstep (se 1 (by rfl) ⟨2565428, by rfl⟩ : syracuseStep 3420571 = 5130857) B5130857
theorem B1601947 : Blo 1600999 1601947 := bstep (se 1 (by rfl) ⟨1201460, by rfl⟩ : syracuseStep 1601947 = 2402921) B2402921
theorem B34648505 : Blo 1600999 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B3420623 : Blo 1600999 3420623 := bstep (se 1 (by rfl) ⟨2565467, by rfl⟩ : syracuseStep 3420623 = 5130935) B5130935
theorem B15389189 : Blo 1600999 15389189 := bstep (se 4 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 15389189 = 2885473) B2885473
theorem B405262925 : Blo 1600999 405262925 := bstep (se 3 (by rfl) ⟨75986798, by rfl⟩ : syracuseStep 405262925 = 151973597) B151973597
theorem B18248327 : Blo 1600999 18248327 := bstep (se 1 (by rfl) ⟨13686245, by rfl⟩ : syracuseStep 18248327 = 27372491) B27372491
theorem B1602299 : Blo 1600999 1602299 := bstep (se 1 (by rfl) ⟨1201724, by rfl⟩ : syracuseStep 1602299 = 2403449) B2403449
theorem B5403401 : Blo 1600999 5403401 := bstep (se 2 (by rfl) ⟨2026275, by rfl⟩ : syracuseStep 5403401 = 4052551) B4052551
theorem B1602367 : Blo 1600999 1602367 := bstep (se 1 (by rfl) ⟨1201775, by rfl⟩ : syracuseStep 1602367 = 2403551) B2403551
theorem B1602395 : Blo 1600999 1602395 := bstep (se 1 (by rfl) ⟨1201796, by rfl⟩ : syracuseStep 1602395 = 2403593) B2403593
theorem B1602463 : Blo 1600999 1602463 := bstep (se 1 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 1602463 = 2403695) B2403695
theorem B13685699 : Blo 1600999 13685699 := bstep (se 1 (by rfl) ⟨10264274, by rfl⟩ : syracuseStep 13685699 = 20528549) B20528549
theorem B1602543 : Blo 1600999 1602543 := bstep (se 1 (by rfl) ⟨1201907, by rfl⟩ : syracuseStep 1602543 = 2403815) B2403815
theorem B1602631 : Blo 1600999 1602631 := bstep (se 1 (by rfl) ⟨1201973, by rfl⟩ : syracuseStep 1602631 = 2403947) B2403947
theorem B6083657 : Blo 1600999 6083657 := bstep (se 2 (by rfl) ⟨2281371, by rfl⟩ : syracuseStep 6083657 = 4562743) B4562743
theorem B3953819 : Blo 1600999 3953819 := bstep (se 1 (by rfl) ⟨2965364, by rfl⟩ : syracuseStep 3953819 = 5930729) B5930729
theorem B1602715 : Blo 1600999 1602715 := bstep (se 1 (by rfl) ⟨1202036, by rfl⟩ : syracuseStep 1602715 = 2404073) B2404073
theorem B18257075 : Blo 1600999 18257075 := bstep (se 1 (by rfl) ⟨13692806, by rfl⟩ : syracuseStep 18257075 = 27385613) B27385613
theorem B1602811 : Blo 1600999 1602811 := bstep (se 1 (by rfl) ⟨1202108, by rfl⟩ : syracuseStep 1602811 = 2404217) B2404217
theorem B1602879 : Blo 1600999 1602879 := bstep (se 1 (by rfl) ⟨1202159, by rfl⟩ : syracuseStep 1602879 = 2404319) B2404319
theorem B8107451 : Blo 1600999 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B39524003 : Blo 1600999 39524003 := bstep (se 1 (by rfl) ⟨29643002, by rfl⟩ : syracuseStep 39524003 = 59286005) B59286005
theorem B3421921 : Blo 1600999 3421921 := bstep (se 2 (by rfl) ⟨1283220, by rfl⟩ : syracuseStep 3421921 = 2566441) B2566441
theorem B1709807 : Blo 1600999 1709807 := bstep (se 1 (by rfl) ⟨1282355, by rfl⟩ : syracuseStep 1709807 = 2564711) B2564711
theorem B5773139 : Blo 1600999 5773139 := bstep (se 1 (by rfl) ⟨4329854, by rfl⟩ : syracuseStep 5773139 = 8659709) B8659709
theorem B3602375 : Blo 1600999 3602375 := bstep (se 1 (by rfl) ⟨2701781, by rfl⟩ : syracuseStep 3602375 = 5403563) B5403563
theorem B49354703 : Blo 1600999 49354703 := bstep (se 1 (by rfl) ⟨37016027, by rfl⟩ : syracuseStep 49354703 = 74032055) B74032055
theorem B4560887 : Blo 1600999 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B6084827 : Blo 1600999 6084827 := bstep (se 1 (by rfl) ⟨4563620, by rfl⟩ : syracuseStep 6084827 = 9127241) B9127241
theorem B3602663 : Blo 1600999 3602663 := bstep (se 1 (by rfl) ⟨2701997, by rfl⟩ : syracuseStep 3602663 = 5403995) B5403995
theorem B6084841 : Blo 1600999 6084841 := bstep (se 2 (by rfl) ⟨2281815, by rfl⟩ : syracuseStep 6084841 = 4563631) B4563631
theorem B3602681 : Blo 1600999 3602681 := bstep (se 2 (by rfl) ⟨1351005, by rfl⟩ : syracuseStep 3602681 = 2702011) B2702011
theorem B3602735 : Blo 1600999 3602735 := bstep (se 1 (by rfl) ⟨2702051, by rfl⟩ : syracuseStep 3602735 = 5404103) B5404103
theorem B2701775 : Blo 1600999 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B3602951 : Blo 1600999 3602951 := bstep (se 1 (by rfl) ⟨2702213, by rfl⟩ : syracuseStep 3602951 = 5404427) B5404427
theorem B8903195 : Blo 1600999 8903195 := bstep (se 1 (by rfl) ⟨6677396, by rfl⟩ : syracuseStep 8903195 = 13354793) B13354793
theorem B23419489 : Blo 1600999 23419489 := bstep (se 2 (by rfl) ⟨8782308, by rfl⟩ : syracuseStep 23419489 = 17564617) B17564617
theorem B3603131 : Blo 1600999 3603131 := bstep (se 1 (by rfl) ⟨2702348, by rfl⟩ : syracuseStep 3603131 = 5404697) B5404697
theorem B7699283 : Blo 1600999 7699283 := bstep (se 1 (by rfl) ⟨5774462, by rfl⟩ : syracuseStep 7699283 = 11548925) B11548925
theorem B25983989 : Blo 1600999 25983989 := bstep (se 5 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 25983989 = 2435999) B2435999
theorem B299850821 : Blo 1600999 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B27376865 : Blo 1600999 27376865 := bstep (se 2 (by rfl) ⟨10266324, by rfl⟩ : syracuseStep 27376865 = 20532649) B20532649
theorem B6495527 : Blo 1600999 6495527 := bstep (se 1 (by rfl) ⟨4871645, by rfl⟩ : syracuseStep 6495527 = 9743291) B9743291
theorem B1801543 : Blo 1600999 1801543 := bstep (se 1 (by rfl) ⟨1351157, by rfl⟩ : syracuseStep 1801543 = 2702315) B2702315
theorem B5479751 : Blo 1600999 5479751 := bstep (se 1 (by rfl) ⟨4109813, by rfl⟩ : syracuseStep 5479751 = 8219627) B8219627
theorem B1711567 : Blo 1600999 1711567 := bstep (se 1 (by rfl) ⟨1283675, by rfl⟩ : syracuseStep 1711567 = 2567351) B2567351
theorem B100040147 : Blo 1600999 100040147 := bstep (se 1 (by rfl) ⟨75030110, by rfl⟩ : syracuseStep 100040147 = 150060221) B150060221
theorem B3604031 : Blo 1600999 3604031 := bstep (se 1 (by rfl) ⟨2703023, by rfl⟩ : syracuseStep 3604031 = 5406047) B5406047
theorem B2703071 : Blo 1600999 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B1924975 : Blo 1600999 1924975 := bstep (se 1 (by rfl) ⟨1443731, by rfl⟩ : syracuseStep 1924975 = 2887463) B2887463
theorem B443686805 : Blo 1600999 443686805 := bstep (se 6 (by rfl) ⟨10398909, by rfl⟩ : syracuseStep 443686805 = 20797819) B20797819
theorem B3604391 : Blo 1600999 3604391 := bstep (se 1 (by rfl) ⟨2703293, by rfl⟩ : syracuseStep 3604391 = 5406587) B5406587
theorem B6766525 : Blo 1600999 6766525 := bstep (se 3 (by rfl) ⟨1268723, by rfl⟩ : syracuseStep 6766525 = 2537447) B2537447
theorem B4055143 : Blo 1600999 4055143 := bstep (se 1 (by rfl) ⟨3041357, by rfl⟩ : syracuseStep 4055143 = 6082715) B6082715
theorem B8110205 : Blo 1600999 8110205 := bstep (se 3 (by rfl) ⟨1520663, by rfl⟩ : syracuseStep 8110205 = 3041327) B3041327
theorem B65757521 : Blo 1600999 65757521 := bstep (se 2 (by rfl) ⟨24659070, by rfl⟩ : syracuseStep 65757521 = 49318141) B49318141
theorem B2703719 : Blo 1600999 2703719 := bstep (se 1 (by rfl) ⟨2027789, by rfl⟩ : syracuseStep 2703719 = 4055579) B4055579
theorem B10543517 : Blo 1600999 10543517 := bstep (se 3 (by rfl) ⟨1976909, by rfl⟩ : syracuseStep 10543517 = 3953819) B3953819
theorem B3604895 : Blo 1600999 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B12165551 : Blo 1600999 12165551 := bstep (se 1 (by rfl) ⟨9124163, by rfl⟩ : syracuseStep 12165551 = 18248327) B18248327
theorem B8110529 : Blo 1600999 8110529 := bstep (se 2 (by rfl) ⟨3041448, by rfl⟩ : syracuseStep 8110529 = 6082897) B6082897
theorem B4055771 : Blo 1600999 4055771 := bstep (se 1 (by rfl) ⟨3041828, by rfl⟩ : syracuseStep 4055771 = 6083657) B6083657
theorem B5407559 : Blo 1600999 5407559 := bstep (se 1 (by rfl) ⟨4055669, by rfl⟩ : syracuseStep 5407559 = 8111339) B8111339
theorem B2401583 : Blo 1600999 2401583 := bstep (se 1 (by rfl) ⟨1801187, by rfl⟩ : syracuseStep 2401583 = 3602375) B3602375
theorem B2704711 : Blo 1600999 2704711 := bstep (se 1 (by rfl) ⟨2028533, by rfl⟩ : syracuseStep 2704711 = 4057067) B4057067
theorem B3040591 : Blo 1600999 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B4056551 : Blo 1600999 4056551 := bstep (se 1 (by rfl) ⟨3042413, by rfl⟩ : syracuseStep 4056551 = 6084827) B6084827
theorem B3605993 : Blo 1600999 3605993 := bstep (se 2 (by rfl) ⟨1352247, by rfl⟩ : syracuseStep 3605993 = 2704495) B2704495
theorem B2401775 : Blo 1600999 2401775 := bstep (se 1 (by rfl) ⟨1801331, by rfl⟩ : syracuseStep 2401775 = 3602663) B3602663
theorem B2401787 : Blo 1600999 2401787 := bstep (se 1 (by rfl) ⟨1801340, by rfl⟩ : syracuseStep 2401787 = 3602681) B3602681
theorem B2401823 : Blo 1600999 2401823 := bstep (se 1 (by rfl) ⟨1801367, by rfl⟩ : syracuseStep 2401823 = 3602735) B3602735
theorem B2401967 : Blo 1600999 2401967 := bstep (se 1 (by rfl) ⟨1801475, by rfl⟩ : syracuseStep 2401967 = 3602951) B3602951
theorem B2402057 : Blo 1600999 2402057 := bstep (se 2 (by rfl) ⟨900771, by rfl⟩ : syracuseStep 2402057 = 1801543) B1801543
theorem B2402087 : Blo 1600999 2402087 := bstep (se 1 (by rfl) ⟨1801565, by rfl⟩ : syracuseStep 2402087 = 3603131) B3603131
theorem B3606569 : Blo 1600999 3606569 := bstep (se 2 (by rfl) ⟨1352463, by rfl⟩ : syracuseStep 3606569 = 2704927) B2704927
theorem B8112311 : Blo 1600999 8112311 := bstep (se 1 (by rfl) ⟨6084233, by rfl⟩ : syracuseStep 8112311 = 12168467) B12168467
theorem B2885863 : Blo 1600999 2885863 := bstep (se 1 (by rfl) ⟨2164397, by rfl⟩ : syracuseStep 2885863 = 4328795) B4328795
theorem B66693431 : Blo 1600999 66693431 := bstep (se 1 (by rfl) ⟨50020073, by rfl⟩ : syracuseStep 66693431 = 100040147) B100040147
theorem B18254159 : Blo 1600999 18254159 := bstep (se 1 (by rfl) ⟨13690619, by rfl⟩ : syracuseStep 18254159 = 27381239) B27381239
theorem B2402687 : Blo 1600999 2402687 := bstep (se 1 (by rfl) ⟨1802015, by rfl⟩ : syracuseStep 2402687 = 3604031) B3604031
theorem B2566633 : Blo 1600999 2566633 := bstep (se 2 (by rfl) ⟨962487, by rfl⟩ : syracuseStep 2566633 = 1924975) B1924975
theorem B9022033 : Blo 1600999 9022033 := bstep (se 2 (by rfl) ⟨3383262, by rfl⟩ : syracuseStep 9022033 = 6766525) B6766525
theorem B295791203 : Blo 1600999 295791203 := bstep (se 1 (by rfl) ⟨221843402, by rfl⟩ : syracuseStep 295791203 = 443686805) B443686805
theorem B2402927 : Blo 1600999 2402927 := bstep (se 1 (by rfl) ⟨1802195, by rfl⟩ : syracuseStep 2402927 = 3604391) B3604391
theorem B17558315 : Blo 1600999 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B2403143 : Blo 1600999 2403143 := bstep (se 1 (by rfl) ⟨1802357, by rfl⟩ : syracuseStep 2403143 = 3604715) B3604715
theorem B2280415 : Blo 1600999 2280415 := bstep (se 1 (by rfl) ⟨1710311, by rfl⟩ : syracuseStep 2280415 = 3420623) B3420623
theorem B8113121 : Blo 1600999 8113121 := bstep (se 2 (by rfl) ⟨3042420, by rfl⟩ : syracuseStep 8113121 = 6084841) B6084841
theorem B3042299 : Blo 1600999 3042299 := bstep (se 1 (by rfl) ⟨2281724, by rfl⟩ : syracuseStep 3042299 = 4563449) B4563449
theorem B10259459 : Blo 1600999 10259459 := bstep (se 1 (by rfl) ⟨7694594, by rfl⟩ : syracuseStep 10259459 = 15389189) B15389189
theorem B270175283 : Blo 1600999 270175283 := bstep (se 1 (by rfl) ⟨202631462, by rfl⟩ : syracuseStep 270175283 = 405262925) B405262925
theorem B10955999 : Blo 1600999 10955999 := bstep (se 1 (by rfl) ⟨8216999, by rfl⟩ : syracuseStep 10955999 = 16433999) B16433999
theorem B10399103 : Blo 1600999 10399103 := bstep (se 1 (by rfl) ⟨7799327, by rfl⟩ : syracuseStep 10399103 = 15598655) B15598655
theorem B2403743 : Blo 1600999 2403743 := bstep (se 1 (by rfl) ⟨1802807, by rfl⟩ : syracuseStep 2403743 = 3605615) B3605615
theorem B2404007 : Blo 1600999 2404007 := bstep (se 1 (by rfl) ⟨1803005, by rfl⟩ : syracuseStep 2404007 = 3606011) B3606011
theorem B2404031 : Blo 1600999 2404031 := bstep (se 1 (by rfl) ⟨1803023, by rfl⟩ : syracuseStep 2404031 = 3606047) B3606047
theorem B5771033 : Blo 1600999 5771033 := bstep (se 2 (by rfl) ⟨2164137, by rfl⟩ : syracuseStep 5771033 = 4328275) B4328275
theorem B26349335 : Blo 1600999 26349335 := bstep (se 1 (by rfl) ⟨19762001, by rfl⟩ : syracuseStep 26349335 = 39524003) B39524003
theorem B2404127 : Blo 1600999 2404127 := bstep (se 1 (by rfl) ⟨1803095, by rfl⟩ : syracuseStep 2404127 = 3606191) B3606191
theorem B30781295 : Blo 1600999 30781295 := bstep (se 1 (by rfl) ⟨23085971, by rfl⟩ : syracuseStep 30781295 = 46171943) B46171943
theorem B32903135 : Blo 1600999 32903135 := bstep (se 1 (by rfl) ⟨24677351, by rfl⟩ : syracuseStep 32903135 = 49354703) B49354703
theorem B1601567 : Blo 1600999 1601567 := bstep (se 1 (by rfl) ⟨1201175, by rfl⟩ : syracuseStep 1601567 = 2402351) B2402351
theorem B2404415 : Blo 1600999 2404415 := bstep (se 1 (by rfl) ⟨1803311, by rfl⟩ : syracuseStep 2404415 = 3606623) B3606623
theorem B3420263 : Blo 1600999 3420263 := bstep (se 1 (by rfl) ⟨2565197, by rfl⟩ : syracuseStep 3420263 = 5130395) B5130395
theorem B1601743 : Blo 1600999 1601743 := bstep (se 1 (by rfl) ⟨1201307, by rfl⟩ : syracuseStep 1601743 = 2402615) B2402615
theorem B21918023 : Blo 1600999 21918023 := bstep (se 1 (by rfl) ⟨16438517, by rfl⟩ : syracuseStep 21918023 = 32877035) B32877035
theorem B1601863 : Blo 1600999 1601863 := bstep (se 1 (by rfl) ⟨1201397, by rfl⟩ : syracuseStep 1601863 = 2402795) B2402795
theorem B2027855 : Blo 1600999 2027855 := bstep (se 1 (by rfl) ⟨1520891, by rfl⟩ : syracuseStep 2027855 = 3041783) B3041783
theorem B5935463 : Blo 1600999 5935463 := bstep (se 1 (by rfl) ⟨4451597, by rfl⟩ : syracuseStep 5935463 = 8903195) B8903195
theorem B5132855 : Blo 1600999 5132855 := bstep (se 1 (by rfl) ⟨3849641, by rfl⟩ : syracuseStep 5132855 = 7699283) B7699283
theorem B2282089 : Blo 1600999 2282089 := bstep (se 2 (by rfl) ⟨855783, by rfl⟩ : syracuseStep 2282089 = 1711567) B1711567
theorem B41628277 : Blo 1600999 41628277 := bstep (se 5 (by rfl) ⟨1951325, by rfl⟩ : syracuseStep 41628277 = 3902651) B3902651
theorem B4559485 : Blo 1600999 4559485 := bstep (se 3 (by rfl) ⟨854903, by rfl⟩ : syracuseStep 4559485 = 1709807) B1709807
theorem B17322659 : Blo 1600999 17322659 := bstep (se 1 (by rfl) ⟨12991994, by rfl⟩ : syracuseStep 17322659 = 25983989) B25983989
theorem B1602331 : Blo 1600999 1602331 := bstep (se 1 (by rfl) ⟨1201748, by rfl⟩ : syracuseStep 1602331 = 2403497) B2403497
theorem B4330351 : Blo 1600999 4330351 := bstep (se 1 (by rfl) ⟨3247763, by rfl⟩ : syracuseStep 4330351 = 6495527) B6495527
theorem B5477345 : Blo 1600999 5477345 := bstep (se 2 (by rfl) ⟨2054004, by rfl⟩ : syracuseStep 5477345 = 4108009) B4108009
theorem B1602607 : Blo 1600999 1602607 := bstep (se 1 (by rfl) ⟨1201955, by rfl⟩ : syracuseStep 1602607 = 2403911) B2403911
theorem B1602727 : Blo 1600999 1602727 := bstep (se 1 (by rfl) ⟨1202045, by rfl⟩ : syracuseStep 1602727 = 2404091) B2404091
theorem B10262123 : Blo 1600999 10262123 := bstep (se 1 (by rfl) ⟨7696592, by rfl⟩ : syracuseStep 10262123 = 15393185) B15393185
theorem B23099003 : Blo 1600999 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B3602267 : Blo 1600999 3602267 := bstep (se 1 (by rfl) ⟨2701700, by rfl⟩ : syracuseStep 3602267 = 5403401) B5403401
theorem B4560761 : Blo 1600999 4560761 := bstep (se 2 (by rfl) ⟨1710285, by rfl⟩ : syracuseStep 4560761 = 3420571) B3420571
theorem B4872059 : Blo 1600999 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B11540389 : Blo 1600999 11540389 := bstep (se 4 (by rfl) ⟨1081911, by rfl⟩ : syracuseStep 11540389 = 2163823) B2163823
theorem B9123799 : Blo 1600999 9123799 := bstep (se 1 (by rfl) ⟨6842849, by rfl⟩ : syracuseStep 9123799 = 13685699) B13685699
theorem B15603677 : Blo 1600999 15603677 := bstep (se 3 (by rfl) ⟨2925689, by rfl⟩ : syracuseStep 15603677 = 5851379) B5851379
theorem B12171383 : Blo 1600999 12171383 := bstep (se 1 (by rfl) ⟨9128537, by rfl⟩ : syracuseStep 12171383 = 18257075) B18257075
theorem B31225985 : Blo 1600999 31225985 := bstep (se 2 (by rfl) ⟨11709744, by rfl⟩ : syracuseStep 31225985 = 23419489) B23419489
theorem B14612669 : Blo 1600999 14612669 := bstep (se 3 (by rfl) ⟨2739875, by rfl⟩ : syracuseStep 14612669 = 5479751) B5479751
theorem B5404967 : Blo 1600999 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B1710439 : Blo 1600999 1710439 := bstep (se 1 (by rfl) ⟨1282829, by rfl⟩ : syracuseStep 1710439 = 2565659) B2565659
theorem B3848759 : Blo 1600999 3848759 := bstep (se 1 (by rfl) ⟨2886569, by rfl⟩ : syracuseStep 3848759 = 5773139) B5773139
theorem B4561535 : Blo 1600999 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B5135035 : Blo 1600999 5135035 := bstep (se 1 (by rfl) ⟨3851276, by rfl⟩ : syracuseStep 5135035 = 7702553) B7702553
theorem B5200703 : Blo 1600999 5200703 := bstep (se 1 (by rfl) ⟨3900527, by rfl⟩ : syracuseStep 5200703 = 7801055) B7801055
theorem B8108909 : Blo 1600999 8108909 := bstep (se 3 (by rfl) ⟨1520420, by rfl⟩ : syracuseStep 8108909 = 3040841) B3040841
theorem B1801183 : Blo 1600999 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B3423305 : Blo 1600999 3423305 := bstep (se 2 (by rfl) ⟨1283739, by rfl⟩ : syracuseStep 3423305 = 2567479) B2567479
theorem B199900547 : Blo 1600999 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B18251243 : Blo 1600999 18251243 := bstep (se 1 (by rfl) ⟨13688432, by rfl⟩ : syracuseStep 18251243 = 27376865) B27376865
theorem B4562561 : Blo 1600999 4562561 := bstep (se 2 (by rfl) ⟨1710960, by rfl⟩ : syracuseStep 4562561 = 3421921) B3421921
theorem B1802047 : Blo 1600999 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B5406803 : Blo 1600999 5406803 := bstep (se 1 (by rfl) ⟨4055102, by rfl⟩ : syracuseStep 5406803 = 8110205) B8110205
theorem B5406857 : Blo 1600999 5406857 := bstep (se 2 (by rfl) ⟨2027571, by rfl⟩ : syracuseStep 5406857 = 4055143) B4055143
theorem B1802479 : Blo 1600999 1802479 := bstep (se 1 (by rfl) ⟨1351859, by rfl⟩ : syracuseStep 1802479 = 2703719) B2703719
theorem B3956975 : Blo 1600999 3956975 := bstep (se 1 (by rfl) ⟨2967731, by rfl⟩ : syracuseStep 3956975 = 5935463) B5935463
theorem B7029011 : Blo 1600999 7029011 := bstep (se 1 (by rfl) ⟨5271758, by rfl⟩ : syracuseStep 7029011 = 10543517) B10543517
theorem B8110367 : Blo 1600999 8110367 := bstep (se 1 (by rfl) ⟨6082775, by rfl⟩ : syracuseStep 8110367 = 12165551) B12165551
theorem B5407019 : Blo 1600999 5407019 := bstep (se 1 (by rfl) ⟨4055264, by rfl⟩ : syracuseStep 5407019 = 8110529) B8110529
theorem B2703847 : Blo 1600999 2703847 := bstep (se 1 (by rfl) ⟨2027885, by rfl⟩ : syracuseStep 2703847 = 4055771) B4055771
theorem B3605039 : Blo 1600999 3605039 := bstep (se 1 (by rfl) ⟨2703779, by rfl⟩ : syracuseStep 3605039 = 5407559) B5407559
theorem B6079313 : Blo 1600999 6079313 := bstep (se 2 (by rfl) ⟨2279742, by rfl⟩ : syracuseStep 6079313 = 4559485) B4559485
theorem B5407613 : Blo 1600999 5407613 := bstep (se 3 (by rfl) ⟨1013927, by rfl⟩ : syracuseStep 5407613 = 2027855) B2027855
theorem B2704367 : Blo 1600999 2704367 := bstep (se 1 (by rfl) ⟨2028275, by rfl⟩ : syracuseStep 2704367 = 4056551) B4056551
theorem B6841415 : Blo 1600999 6841415 := bstep (se 1 (by rfl) ⟨5131061, by rfl⟩ : syracuseStep 6841415 = 10262123) B10262123
theorem B2401511 : Blo 1600999 2401511 := bstep (se 1 (by rfl) ⟨1801133, by rfl⟩ : syracuseStep 2401511 = 3602267) B3602267
theorem B3040507 : Blo 1600999 3040507 := bstep (se 1 (by rfl) ⟨2280380, by rfl⟩ : syracuseStep 3040507 = 4560761) B4560761
theorem B2401577 : Blo 1600999 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B3040553 : Blo 1600999 3040553 := bstep (se 2 (by rfl) ⟨1140207, by rfl⟩ : syracuseStep 3040553 = 2280415) B2280415
theorem B20817323 : Blo 1600999 20817323 := bstep (se 1 (by rfl) ⟨15612992, by rfl⟩ : syracuseStep 20817323 = 31225985) B31225985
theorem B5408207 : Blo 1600999 5408207 := bstep (se 1 (by rfl) ⟨4056155, by rfl⟩ : syracuseStep 5408207 = 8112311) B8112311
theorem B9741779 : Blo 1600999 9741779 := bstep (se 1 (by rfl) ⟨7306334, by rfl⟩ : syracuseStep 9741779 = 14612669) B14612669
theorem B788776541 : Blo 1600999 788776541 := bstep (se 3 (by rfl) ⟨147895601, by rfl⟩ : syracuseStep 788776541 = 295791203) B295791203
theorem B2565839 : Blo 1600999 2565839 := bstep (se 1 (by rfl) ⟨1924379, by rfl⟩ : syracuseStep 2565839 = 3848759) B3848759
theorem B3606281 : Blo 1600999 3606281 := bstep (se 2 (by rfl) ⟨1352355, by rfl⟩ : syracuseStep 3606281 = 2704711) B2704711
theorem B3467135 : Blo 1600999 3467135 := bstep (se 1 (by rfl) ⟨2600351, by rfl⟩ : syracuseStep 3467135 = 5200703) B5200703
theorem B5408747 : Blo 1600999 5408747 := bstep (se 1 (by rfl) ⟨4056560, by rfl⟩ : syracuseStep 5408747 = 8113121) B8113121
theorem B6932735 : Blo 1600999 6932735 := bstep (se 1 (by rfl) ⟨5199551, by rfl⟩ : syracuseStep 6932735 = 10399103) B10399103
theorem B12167495 : Blo 1600999 12167495 := bstep (se 1 (by rfl) ⟨9125621, by rfl⟩ : syracuseStep 12167495 = 18251243) B18251243
theorem B2402729 : Blo 1600999 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B3041707 : Blo 1600999 3041707 := bstep (se 1 (by rfl) ⟨2281280, by rfl⟩ : syracuseStep 3041707 = 4562561) B4562561
theorem B17566223 : Blo 1600999 17566223 := bstep (se 1 (by rfl) ⟨13174667, by rfl⟩ : syracuseStep 17566223 = 26349335) B26349335
theorem B15387185 : Blo 1600999 15387185 := bstep (se 2 (by rfl) ⟨5770194, by rfl⟩ : syracuseStep 15387185 = 11540389) B11540389
theorem B8112797 : Blo 1600999 8112797 := bstep (se 3 (by rfl) ⟨1521149, by rfl⟩ : syracuseStep 8112797 = 3042299) B3042299
theorem B43838347 : Blo 1600999 43838347 := bstep (se 1 (by rfl) ⟨32878760, by rfl⟩ : syracuseStep 43838347 = 65757521) B65757521
theorem B9120701 : Blo 1600999 9120701 := bstep (se 3 (by rfl) ⟨1710131, by rfl⟩ : syracuseStep 9120701 = 3420263) B3420263
theorem B2403263 : Blo 1600999 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B29215997 : Blo 1600999 29215997 := bstep (se 3 (by rfl) ⟨5477999, by rfl⟩ : syracuseStep 29215997 = 10955999) B10955999
theorem B3042785 : Blo 1600999 3042785 := bstep (se 2 (by rfl) ⟨1141044, by rfl⟩ : syracuseStep 3042785 = 2282089) B2282089
theorem B55504369 : Blo 1600999 55504369 := bstep (se 2 (by rfl) ⟨20814138, by rfl⟩ : syracuseStep 55504369 = 41628277) B41628277
theorem B1601055 : Blo 1600999 1601055 := bstep (se 1 (by rfl) ⟨1200791, by rfl⟩ : syracuseStep 1601055 = 2401583) B2401583
theorem B2403995 : Blo 1600999 2403995 := bstep (se 1 (by rfl) ⟨1802996, by rfl⟩ : syracuseStep 2403995 = 3605993) B3605993
theorem B1601183 : Blo 1600999 1601183 := bstep (se 1 (by rfl) ⟨1200887, by rfl⟩ : syracuseStep 1601183 = 2401775) B2401775
theorem B1601191 : Blo 1600999 1601191 := bstep (se 1 (by rfl) ⟨1200893, by rfl⟩ : syracuseStep 1601191 = 2401787) B2401787
theorem B1601215 : Blo 1600999 1601215 := bstep (se 1 (by rfl) ⟨1200911, by rfl⟩ : syracuseStep 1601215 = 2401823) B2401823
theorem B1601311 : Blo 1600999 1601311 := bstep (se 1 (by rfl) ⟨1200983, by rfl⟩ : syracuseStep 1601311 = 2401967) B2401967
theorem B1601371 : Blo 1600999 1601371 := bstep (se 1 (by rfl) ⟨1201028, by rfl⟩ : syracuseStep 1601371 = 2402057) B2402057
theorem B1601391 : Blo 1600999 1601391 := bstep (se 1 (by rfl) ⟨1201043, by rfl⟩ : syracuseStep 1601391 = 2402087) B2402087
theorem B3248039 : Blo 1600999 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B2404379 : Blo 1600999 2404379 := bstep (se 1 (by rfl) ⟨1803284, by rfl⟩ : syracuseStep 2404379 = 3606569) B3606569
theorem B8114255 : Blo 1600999 8114255 := bstep (se 1 (by rfl) ⟨6085691, by rfl⟩ : syracuseStep 8114255 = 12171383) B12171383
theorem B44462287 : Blo 1600999 44462287 := bstep (se 1 (by rfl) ⟨33346715, by rfl⟩ : syracuseStep 44462287 = 66693431) B66693431
theorem B12169439 : Blo 1600999 12169439 := bstep (se 1 (by rfl) ⟨9127079, by rfl⟩ : syracuseStep 12169439 = 18254159) B18254159
theorem B1601791 : Blo 1600999 1601791 := bstep (se 1 (by rfl) ⟨1201343, by rfl⟩ : syracuseStep 1601791 = 2402687) B2402687
theorem B1601951 : Blo 1600999 1601951 := bstep (se 1 (by rfl) ⟨1201463, by rfl⟩ : syracuseStep 1601951 = 2402927) B2402927
theorem B9122341 : Blo 1600999 9122341 := bstep (se 4 (by rfl) ⟨855219, by rfl⟩ : syracuseStep 9122341 = 1710439) B1710439
theorem B1602095 : Blo 1600999 1602095 := bstep (se 1 (by rfl) ⟨1201571, by rfl⟩ : syracuseStep 1602095 = 2403143) B2403143
theorem B2282203 : Blo 1600999 2282203 := bstep (se 1 (by rfl) ⟨1711652, by rfl⟩ : syracuseStep 2282203 = 3423305) B3423305
theorem B1602495 : Blo 1600999 1602495 := bstep (se 1 (by rfl) ⟨1201871, by rfl⟩ : syracuseStep 1602495 = 2403743) B2403743
theorem B1602671 : Blo 1600999 1602671 := bstep (se 1 (by rfl) ⟨1202003, by rfl⟩ : syracuseStep 1602671 = 2404007) B2404007
theorem B1602687 : Blo 1600999 1602687 := bstep (se 1 (by rfl) ⟨1202015, by rfl⟩ : syracuseStep 1602687 = 2404031) B2404031
theorem B3847355 : Blo 1600999 3847355 := bstep (se 1 (by rfl) ⟨2885516, by rfl⟩ : syracuseStep 3847355 = 5771033) B5771033
theorem B1602751 : Blo 1600999 1602751 := bstep (se 1 (by rfl) ⟨1202063, by rfl⟩ : syracuseStep 1602751 = 2404127) B2404127
theorem B21935423 : Blo 1600999 21935423 := bstep (se 1 (by rfl) ⟨16451567, by rfl⟩ : syracuseStep 21935423 = 32903135) B32903135
theorem B1602943 : Blo 1600999 1602943 := bstep (se 1 (by rfl) ⟨1202207, by rfl⟩ : syracuseStep 1602943 = 2404415) B2404415
theorem B14612015 : Blo 1600999 14612015 := bstep (se 1 (by rfl) ⟨10959011, by rfl⟩ : syracuseStep 14612015 = 21918023) B21918023
theorem B3847817 : Blo 1600999 3847817 := bstep (se 2 (by rfl) ⟨1442931, by rfl⟩ : syracuseStep 3847817 = 2885863) B2885863
theorem B48117509 : Blo 1600999 48117509 := bstep (se 4 (by rfl) ⟨4511016, by rfl⟩ : syracuseStep 48117509 = 9022033) B9022033
theorem B11548439 : Blo 1600999 11548439 := bstep (se 1 (by rfl) ⟨8661329, by rfl⟩ : syracuseStep 11548439 = 17322659) B17322659
theorem B3422177 : Blo 1600999 3422177 := bstep (se 2 (by rfl) ⟨1283316, by rfl⟩ : syracuseStep 3422177 = 2566633) B2566633
theorem B3651563 : Blo 1600999 3651563 := bstep (se 1 (by rfl) ⟨2738672, by rfl⟩ : syracuseStep 3651563 = 5477345) B5477345
theorem B6846713 : Blo 1600999 6846713 := bstep (se 2 (by rfl) ⟨2567517, by rfl⟩ : syracuseStep 6846713 = 5135035) B5135035
theorem B15399335 : Blo 1600999 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B5773801 : Blo 1600999 5773801 := bstep (se 2 (by rfl) ⟨2165175, by rfl⟩ : syracuseStep 5773801 = 4330351) B4330351
theorem B10402451 : Blo 1600999 10402451 := bstep (se 1 (by rfl) ⟨7801838, by rfl⟩ : syracuseStep 10402451 = 15603677) B15603677
theorem B13687613 : Blo 1600999 13687613 := bstep (se 3 (by rfl) ⟨2566427, by rfl⟩ : syracuseStep 13687613 = 5132855) B5132855
theorem B3603311 : Blo 1600999 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B12164093 : Blo 1600999 12164093 := bstep (se 3 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 12164093 = 4561535) B4561535
theorem B4054121 : Blo 1600999 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B11705543 : Blo 1600999 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B5405939 : Blo 1600999 5405939 := bstep (se 1 (by rfl) ⟨4054454, by rfl⟩ : syracuseStep 5405939 = 8108909) B8108909
theorem B6839639 : Blo 1600999 6839639 := bstep (se 1 (by rfl) ⟨5129729, by rfl⟩ : syracuseStep 6839639 = 10259459) B10259459
theorem B180116855 : Blo 1600999 180116855 := bstep (se 1 (by rfl) ⟨135087641, by rfl⟩ : syracuseStep 180116855 = 270175283) B270175283
theorem B133267031 : Blo 1600999 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B20520863 : Blo 1600999 20520863 := bstep (se 1 (by rfl) ⟨15390647, by rfl⟩ : syracuseStep 20520863 = 30781295) B30781295
theorem B12165065 : Blo 1600999 12165065 := bstep (se 2 (by rfl) ⟨4561899, by rfl⟩ : syracuseStep 12165065 = 9123799) B9123799
theorem B3604535 : Blo 1600999 3604535 := bstep (se 1 (by rfl) ⟨2703401, by rfl⟩ : syracuseStep 3604535 = 5406803) B5406803
theorem B3604571 : Blo 1600999 3604571 := bstep (se 1 (by rfl) ⟨2703428, by rfl⟩ : syracuseStep 3604571 = 5406857) B5406857
theorem B2637983 : Blo 1600999 2637983 := bstep (se 1 (by rfl) ⟨1978487, by rfl⟩ : syracuseStep 2637983 = 3956975) B3956975
theorem B4686007 : Blo 1600999 4686007 := bstep (se 1 (by rfl) ⟨3514505, by rfl⟩ : syracuseStep 4686007 = 7029011) B7029011
theorem B5406911 : Blo 1600999 5406911 := bstep (se 1 (by rfl) ⟨4055183, by rfl⟩ : syracuseStep 5406911 = 8110367) B8110367
theorem B3604679 : Blo 1600999 3604679 := bstep (se 1 (by rfl) ⟨2703509, by rfl⟩ : syracuseStep 3604679 = 5407019) B5407019
theorem B4055609 : Blo 1600999 4055609 := bstep (se 2 (by rfl) ⟨1520853, by rfl⟩ : syracuseStep 4055609 = 3041707) B3041707
theorem B3605075 : Blo 1600999 3605075 := bstep (se 1 (by rfl) ⟨2703806, by rfl⟩ : syracuseStep 3605075 = 5407613) B5407613
theorem B3605129 : Blo 1600999 3605129 := bstep (se 2 (by rfl) ⟨1351923, by rfl⟩ : syracuseStep 3605129 = 2703847) B2703847
theorem B1802911 : Blo 1600999 1802911 := bstep (se 1 (by rfl) ⟨1352183, by rfl⟩ : syracuseStep 1802911 = 2704367) B2704367
theorem B2564903 : Blo 1600999 2564903 := bstep (se 1 (by rfl) ⟨1923677, by rfl⟩ : syracuseStep 2564903 = 3847355) B3847355
theorem B14623615 : Blo 1600999 14623615 := bstep (se 1 (by rfl) ⟨10967711, by rfl⟩ : syracuseStep 14623615 = 21935423) B21935423
theorem B13878215 : Blo 1600999 13878215 := bstep (se 1 (by rfl) ⟨10408661, by rfl⟩ : syracuseStep 13878215 = 20817323) B20817323
theorem B3605471 : Blo 1600999 3605471 := bstep (se 1 (by rfl) ⟨2704103, by rfl⟩ : syracuseStep 3605471 = 5408207) B5408207
theorem B9741343 : Blo 1600999 9741343 := bstep (se 1 (by rfl) ⟨7306007, by rfl⟩ : syracuseStep 9741343 = 14612015) B14612015
theorem B2565211 : Blo 1600999 2565211 := bstep (se 1 (by rfl) ⟨1923908, by rfl⟩ : syracuseStep 2565211 = 3847817) B3847817
theorem B58451129 : Blo 1600999 58451129 := bstep (se 2 (by rfl) ⟨21919173, by rfl⟩ : syracuseStep 58451129 = 43838347) B43838347
theorem B2311423 : Blo 1600999 2311423 := bstep (se 1 (by rfl) ⟨1733567, by rfl⟩ : syracuseStep 2311423 = 3467135) B3467135
theorem B2434375 : Blo 1600999 2434375 := bstep (se 1 (by rfl) ⟨1825781, by rfl⟩ : syracuseStep 2434375 = 3651563) B3651563
theorem B3605831 : Blo 1600999 3605831 := bstep (se 1 (by rfl) ⟨2704373, by rfl⟩ : syracuseStep 3605831 = 5408747) B5408747
theorem B4564475 : Blo 1600999 4564475 := bstep (se 1 (by rfl) ⟨3423356, by rfl⟩ : syracuseStep 4564475 = 6846713) B6846713
theorem B4621823 : Blo 1600999 4621823 := bstep (se 1 (by rfl) ⟨3466367, by rfl⟩ : syracuseStep 4621823 = 6932735) B6932735
theorem B8111663 : Blo 1600999 8111663 := bstep (se 1 (by rfl) ⟨6083747, by rfl⟩ : syracuseStep 8111663 = 12167495) B12167495
theorem B10266223 : Blo 1600999 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B5408531 : Blo 1600999 5408531 := bstep (se 1 (by rfl) ⟨4056398, by rfl⟩ : syracuseStep 5408531 = 8112797) B8112797
theorem B2402207 : Blo 1600999 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B6080467 : Blo 1600999 6080467 := bstep (se 1 (by rfl) ⟨4560350, by rfl⟩ : syracuseStep 6080467 = 9120701) B9120701
theorem B88844687 : Blo 1600999 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B8661437 : Blo 1600999 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B5409503 : Blo 1600999 5409503 := bstep (se 1 (by rfl) ⟨4057127, by rfl⟩ : syracuseStep 5409503 = 8114255) B8114255
theorem B8112959 : Blo 1600999 8112959 := bstep (se 1 (by rfl) ⟨6084719, by rfl⟩ : syracuseStep 8112959 = 12169439) B12169439
theorem B2403305 : Blo 1600999 2403305 := bstep (se 2 (by rfl) ⟨901239, by rfl⟩ : syracuseStep 2403305 = 1802479) B1802479
theorem B2403359 : Blo 1600999 2403359 := bstep (se 1 (by rfl) ⟨1802519, by rfl⟩ : syracuseStep 2403359 = 3605039) B3605039
theorem B1601007 : Blo 1600999 1601007 := bstep (se 1 (by rfl) ⟨1200755, by rfl⟩ : syracuseStep 1601007 = 2401511) B2401511
theorem B1601051 : Blo 1600999 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B2027035 : Blo 1600999 2027035 := bstep (se 1 (by rfl) ⟨1520276, by rfl⟩ : syracuseStep 2027035 = 3040553) B3040553
theorem B3042937 : Blo 1600999 3042937 := bstep (se 2 (by rfl) ⟨1141101, by rfl⟩ : syracuseStep 3042937 = 2282203) B2282203
theorem B2404187 : Blo 1600999 2404187 := bstep (se 1 (by rfl) ⟨1803140, by rfl⟩ : syracuseStep 2404187 = 3606281) B3606281
theorem B8114093 : Blo 1600999 8114093 := bstep (se 3 (by rfl) ⟨1521392, by rfl⟩ : syracuseStep 8114093 = 3042785) B3042785
theorem B2281451 : Blo 1600999 2281451 := bstep (se 1 (by rfl) ⟨1711088, by rfl⟩ : syracuseStep 2281451 = 3422177) B3422177
theorem B1601819 : Blo 1600999 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B6934967 : Blo 1600999 6934967 := bstep (se 1 (by rfl) ⟨5201225, by rfl⟩ : syracuseStep 6934967 = 10402451) B10402451
theorem B1602175 : Blo 1600999 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B7803695 : Blo 1600999 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B19477331 : Blo 1600999 19477331 := bstep (se 1 (by rfl) ⟨14607998, by rfl⟩ : syracuseStep 19477331 = 29215997) B29215997
theorem B4559759 : Blo 1600999 4559759 := bstep (se 1 (by rfl) ⟨3419819, by rfl⟩ : syracuseStep 4559759 = 6839639) B6839639
theorem B1602663 : Blo 1600999 1602663 := bstep (se 1 (by rfl) ⟨1201997, by rfl⟩ : syracuseStep 1602663 = 2403995) B2403995
theorem B1602919 : Blo 1600999 1602919 := bstep (se 1 (by rfl) ⟨1202189, by rfl⟩ : syracuseStep 1602919 = 2404379) B2404379
theorem B187373045 : Blo 1600999 187373045 := bstep (se 5 (by rfl) ⟨8783111, by rfl⟩ : syracuseStep 187373045 = 17566223) B17566223
theorem B4052875 : Blo 1600999 4052875 := bstep (se 1 (by rfl) ⟨3039656, by rfl⟩ : syracuseStep 4052875 = 6079313) B6079313
theorem B7698401 : Blo 1600999 7698401 := bstep (se 2 (by rfl) ⟨2886900, by rfl⟩ : syracuseStep 7698401 = 5773801) B5773801
theorem B4560943 : Blo 1600999 4560943 := bstep (se 1 (by rfl) ⟨3420707, by rfl⟩ : syracuseStep 4560943 = 6841415) B6841415
theorem B12163121 : Blo 1600999 12163121 := bstep (se 2 (by rfl) ⟨4561170, by rfl⟩ : syracuseStep 12163121 = 9122341) B9122341
theorem B6494519 : Blo 1600999 6494519 := bstep (se 1 (by rfl) ⟨4870889, by rfl⟩ : syracuseStep 6494519 = 9741779) B9741779
theorem B525851027 : Blo 1600999 525851027 := bstep (se 1 (by rfl) ⟨394388270, by rfl⟩ : syracuseStep 525851027 = 788776541) B788776541
theorem B237132197 : Blo 1600999 237132197 := bstep (se 4 (by rfl) ⟨22231143, by rfl⟩ : syracuseStep 237132197 = 44462287) B44462287
theorem B1710559 : Blo 1600999 1710559 := bstep (se 1 (by rfl) ⟨1282919, by rfl⟩ : syracuseStep 1710559 = 2565839) B2565839
theorem B32078339 : Blo 1600999 32078339 := bstep (se 1 (by rfl) ⟨24058754, by rfl⟩ : syracuseStep 32078339 = 48117509) B48117509
theorem B7698959 : Blo 1600999 7698959 := bstep (se 1 (by rfl) ⟨5774219, by rfl⟩ : syracuseStep 7698959 = 11548439) B11548439
theorem B41032493 : Blo 1600999 41032493 := bstep (se 3 (by rfl) ⟨7693592, by rfl⟩ : syracuseStep 41032493 = 15387185) B15387185
theorem B4054009 : Blo 1600999 4054009 := bstep (se 2 (by rfl) ⟨1520253, by rfl⟩ : syracuseStep 4054009 = 3040507) B3040507
theorem B9125075 : Blo 1600999 9125075 := bstep (se 1 (by rfl) ⟨6843806, by rfl⟩ : syracuseStep 9125075 = 13687613) B13687613
theorem B74005825 : Blo 1600999 74005825 := bstep (se 2 (by rfl) ⟨27752184, by rfl⟩ : syracuseStep 74005825 = 55504369) B55504369
theorem B8109395 : Blo 1600999 8109395 := bstep (se 1 (by rfl) ⟨6082046, by rfl⟩ : syracuseStep 8109395 = 12164093) B12164093
theorem B2702747 : Blo 1600999 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B3603959 : Blo 1600999 3603959 := bstep (se 1 (by rfl) ⟨2702969, by rfl⟩ : syracuseStep 3603959 = 5405939) B5405939
theorem B120077903 : Blo 1600999 120077903 := bstep (se 1 (by rfl) ⟨90058427, by rfl⟩ : syracuseStep 120077903 = 180116855) B180116855
theorem B13680575 : Blo 1600999 13680575 := bstep (se 1 (by rfl) ⟨10260431, by rfl⟩ : syracuseStep 13680575 = 20520863) B20520863
theorem B8110043 : Blo 1600999 8110043 := bstep (se 1 (by rfl) ⟨6082532, by rfl⟩ : syracuseStep 8110043 = 12165065) B12165065
theorem B3604607 : Blo 1600999 3604607 := bstep (se 1 (by rfl) ⟨2703455, by rfl⟩ : syracuseStep 3604607 = 5406911) B5406911
theorem B2703739 : Blo 1600999 2703739 := bstep (se 1 (by rfl) ⟨2027804, by rfl⟩ : syracuseStep 2703739 = 4055609) B4055609
theorem B5202463 : Blo 1600999 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B12984887 : Blo 1600999 12984887 := bstep (se 1 (by rfl) ⟨9738665, by rfl⟩ : syracuseStep 12984887 = 19477331) B19477331
theorem B3039839 : Blo 1600999 3039839 := bstep (se 1 (by rfl) ⟨2279879, by rfl⟩ : syracuseStep 3039839 = 4559759) B4559759
theorem B17318717 : Blo 1600999 17318717 := bstep (se 3 (by rfl) ⟨3247259, by rfl⟩ : syracuseStep 17318717 = 6494519) B6494519
theorem B3081215 : Blo 1600999 3081215 := bstep (se 1 (by rfl) ⟨2310911, by rfl⟩ : syracuseStep 3081215 = 4621823) B4621823
theorem B5407775 : Blo 1600999 5407775 := bstep (se 1 (by rfl) ⟨4055831, by rfl⟩ : syracuseStep 5407775 = 8111663) B8111663
theorem B19498153 : Blo 1600999 19498153 := bstep (se 2 (by rfl) ⟨7311807, by rfl⟩ : syracuseStep 19498153 = 14623615) B14623615
theorem B3605687 : Blo 1600999 3605687 := bstep (se 1 (by rfl) ⟨2704265, by rfl⟩ : syracuseStep 3605687 = 5408531) B5408531
theorem B59229791 : Blo 1600999 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B98674433 : Blo 1600999 98674433 := bstep (se 2 (by rfl) ⟨37002912, by rfl⟩ : syracuseStep 98674433 = 74005825) B74005825
theorem B3245833 : Blo 1600999 3245833 := bstep (se 2 (by rfl) ⟨1217187, by rfl⟩ : syracuseStep 3245833 = 2434375) B2434375
theorem B3606335 : Blo 1600999 3606335 := bstep (se 1 (by rfl) ⟨2704751, by rfl⟩ : syracuseStep 3606335 = 5409503) B5409503
theorem B27354995 : Blo 1600999 27354995 := bstep (se 1 (by rfl) ⟨20516246, by rfl⟩ : syracuseStep 27354995 = 41032493) B41032493
theorem B5408639 : Blo 1600999 5408639 := bstep (se 1 (by rfl) ⟨4056479, by rfl⟩ : syracuseStep 5408639 = 8112959) B8112959
theorem B4057249 : Blo 1600999 4057249 := bstep (se 2 (by rfl) ⟨1521468, by rfl⟩ : syracuseStep 4057249 = 3042937) B3042937
theorem B2402639 : Blo 1600999 2402639 := bstep (se 1 (by rfl) ⟨1801979, by rfl⟩ : syracuseStep 2402639 = 3603959) B3603959
theorem B5409395 : Blo 1600999 5409395 := bstep (se 1 (by rfl) ⟨4057046, by rfl⟩ : syracuseStep 5409395 = 8114093) B8114093
theorem B9120383 : Blo 1600999 9120383 := bstep (se 1 (by rfl) ⟨6840287, by rfl⟩ : syracuseStep 9120383 = 13680575) B13680575
theorem B2403023 : Blo 1600999 2403023 := bstep (se 1 (by rfl) ⟨1802267, by rfl⟩ : syracuseStep 2403023 = 3604535) B3604535
theorem B2403047 : Blo 1600999 2403047 := bstep (se 1 (by rfl) ⟨1802285, by rfl⟩ : syracuseStep 2403047 = 3604571) B3604571
theorem B6081257 : Blo 1600999 6081257 := bstep (se 2 (by rfl) ⟨2280471, by rfl⟩ : syracuseStep 6081257 = 4560943) B4560943
theorem B2403119 : Blo 1600999 2403119 := bstep (se 1 (by rfl) ⟨1802339, by rfl⟩ : syracuseStep 2403119 = 3604679) B3604679
theorem B4623311 : Blo 1600999 4623311 := bstep (se 1 (by rfl) ⟨3467483, by rfl⟩ : syracuseStep 4623311 = 6934967) B6934967
theorem B2403383 : Blo 1600999 2403383 := bstep (se 1 (by rfl) ⟨1802537, by rfl⟩ : syracuseStep 2403383 = 3605075) B3605075
theorem B2403419 : Blo 1600999 2403419 := bstep (se 1 (by rfl) ⟨1802564, by rfl⟩ : syracuseStep 2403419 = 3605129) B3605129
theorem B2280745 : Blo 1600999 2280745 := bstep (se 2 (by rfl) ⟨855279, by rfl⟩ : syracuseStep 2280745 = 1710559) B1710559
theorem B9252143 : Blo 1600999 9252143 := bstep (se 1 (by rfl) ⟨6939107, by rfl⟩ : syracuseStep 9252143 = 13878215) B13878215
theorem B2403647 : Blo 1600999 2403647 := bstep (se 1 (by rfl) ⟨1802735, by rfl⟩ : syracuseStep 2403647 = 3605471) B3605471
theorem B2403881 : Blo 1600999 2403881 := bstep (se 2 (by rfl) ⟨901455, by rfl⟩ : syracuseStep 2403881 = 1802911) B1802911
theorem B2403887 : Blo 1600999 2403887 := bstep (se 1 (by rfl) ⟨1802915, by rfl⟩ : syracuseStep 2403887 = 3605831) B3605831
theorem B3042983 : Blo 1600999 3042983 := bstep (se 1 (by rfl) ⟨2282237, by rfl⟩ : syracuseStep 3042983 = 4564475) B4564475
theorem B1601471 : Blo 1600999 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B5132267 : Blo 1600999 5132267 := bstep (se 1 (by rfl) ⟨3849200, by rfl⟩ : syracuseStep 5132267 = 7698401) B7698401
theorem B12988457 : Blo 1600999 12988457 := bstep (se 2 (by rfl) ⟨4870671, by rfl⟩ : syracuseStep 12988457 = 9741343) B9741343
theorem B3420281 : Blo 1600999 3420281 := bstep (se 2 (by rfl) ⟨1282605, by rfl⟩ : syracuseStep 3420281 = 2565211) B2565211
theorem B21385559 : Blo 1600999 21385559 := bstep (se 1 (by rfl) ⟨16039169, by rfl⟩ : syracuseStep 21385559 = 32078339) B32078339
theorem B5132639 : Blo 1600999 5132639 := bstep (se 1 (by rfl) ⟨3849479, by rfl⟩ : syracuseStep 5132639 = 7698959) B7698959
theorem B1602203 : Blo 1600999 1602203 := bstep (se 1 (by rfl) ⟨1201652, by rfl⟩ : syracuseStep 1602203 = 2403305) B2403305
theorem B1602239 : Blo 1600999 1602239 := bstep (se 1 (by rfl) ⟨1201679, by rfl⟩ : syracuseStep 1602239 = 2403359) B2403359
theorem B6083383 : Blo 1600999 6083383 := bstep (se 1 (by rfl) ⟨4562537, by rfl⟩ : syracuseStep 6083383 = 9125075) B9125075
theorem B5403833 : Blo 1600999 5403833 := bstep (se 2 (by rfl) ⟨2026437, by rfl⟩ : syracuseStep 5403833 = 4052875) B4052875
theorem B1602791 : Blo 1600999 1602791 := bstep (se 1 (by rfl) ⟨1202093, by rfl⟩ : syracuseStep 1602791 = 2404187) B2404187
theorem B8107289 : Blo 1600999 8107289 := bstep (se 2 (by rfl) ⟨3040233, by rfl⟩ : syracuseStep 8107289 = 6080467) B6080467
theorem B6083869 : Blo 1600999 6083869 := bstep (se 3 (by rfl) ⟨1140725, by rfl⟩ : syracuseStep 6083869 = 2281451) B2281451
theorem B1758655 : Blo 1600999 1758655 := bstep (se 1 (by rfl) ⟨1318991, by rfl⟩ : syracuseStep 1758655 = 2637983) B2637983
theorem B6248009 : Blo 1600999 6248009 := bstep (se 2 (by rfl) ⟨2343003, by rfl⟩ : syracuseStep 6248009 = 4686007) B4686007
theorem B38967419 : Blo 1600999 38967419 := bstep (se 1 (by rfl) ⟨29225564, by rfl⟩ : syracuseStep 38967419 = 58451129) B58451129
theorem B499661453 : Blo 1600999 499661453 := bstep (se 3 (by rfl) ⟨93686522, by rfl⟩ : syracuseStep 499661453 = 187373045) B187373045
theorem B5405345 : Blo 1600999 5405345 := bstep (se 2 (by rfl) ⟨2027004, by rfl⟩ : syracuseStep 5405345 = 4054009) B4054009
theorem B12327589 : Blo 1600999 12327589 := bstep (se 4 (by rfl) ⟨1155711, by rfl⟩ : syracuseStep 12327589 = 2311423) B2311423
theorem B8108747 : Blo 1600999 8108747 := bstep (se 1 (by rfl) ⟨6081560, by rfl⟩ : syracuseStep 8108747 = 12163121) B12163121
theorem B350567351 : Blo 1600999 350567351 := bstep (se 1 (by rfl) ⟨262925513, by rfl⟩ : syracuseStep 350567351 = 525851027) B525851027
theorem B158088131 : Blo 1600999 158088131 := bstep (se 1 (by rfl) ⟨118566098, by rfl⟩ : syracuseStep 158088131 = 237132197) B237132197
theorem B5774291 : Blo 1600999 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B2702713 : Blo 1600999 2702713 := bstep (se 2 (by rfl) ⟨1013517, by rfl⟩ : syracuseStep 2702713 = 2027035) B2027035
theorem B6839741 : Blo 1600999 6839741 := bstep (se 3 (by rfl) ⟨1282451, by rfl⟩ : syracuseStep 6839741 = 2564903) B2564903
theorem B13688297 : Blo 1600999 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B5406263 : Blo 1600999 5406263 := bstep (se 1 (by rfl) ⟨4054697, by rfl⟩ : syracuseStep 5406263 = 8109395) B8109395
theorem B1801831 : Blo 1600999 1801831 := bstep (se 1 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 1801831 = 2702747) B2702747
theorem B80051935 : Blo 1600999 80051935 := bstep (se 1 (by rfl) ⟨60038951, by rfl⟩ : syracuseStep 80051935 = 120077903) B120077903
theorem B5406695 : Blo 1600999 5406695 := bstep (se 1 (by rfl) ⟨4055021, by rfl⟩ : syracuseStep 5406695 = 8110043) B8110043
theorem B8658971 : Blo 1600999 8658971 := bstep (se 1 (by rfl) ⟨6494228, by rfl⟩ : syracuseStep 8658971 = 12988457) B12988457
theorem B3604985 : Blo 1600999 3604985 := bstep (se 2 (by rfl) ⟨1351869, by rfl⟩ : syracuseStep 3604985 = 2703739) B2703739
theorem B3605183 : Blo 1600999 3605183 := bstep (se 1 (by rfl) ⟨2703887, by rfl⟩ : syracuseStep 3605183 = 5407775) B5407775
theorem B39486527 : Blo 1600999 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B8111177 : Blo 1600999 8111177 := bstep (se 2 (by rfl) ⟨3041691, by rfl⟩ : syracuseStep 8111177 = 6083383) B6083383
theorem B65782955 : Blo 1600999 65782955 := bstep (se 1 (by rfl) ⟨49337216, by rfl⟩ : syracuseStep 65782955 = 98674433) B98674433
theorem B18236663 : Blo 1600999 18236663 := bstep (se 1 (by rfl) ⟨13677497, by rfl⟩ : syracuseStep 18236663 = 27354995) B27354995
theorem B3605759 : Blo 1600999 3605759 := bstep (se 1 (by rfl) ⟨2704319, by rfl⟩ : syracuseStep 3605759 = 5408639) B5408639
theorem B25978279 : Blo 1600999 25978279 := bstep (se 1 (by rfl) ⟨19483709, by rfl⟩ : syracuseStep 25978279 = 38967419) B38967419
theorem B8111825 : Blo 1600999 8111825 := bstep (se 2 (by rfl) ⟨3041934, by rfl⟩ : syracuseStep 8111825 = 6083869) B6083869
theorem B3040993 : Blo 1600999 3040993 := bstep (se 2 (by rfl) ⟨1140372, by rfl⟩ : syracuseStep 3040993 = 2280745) B2280745
theorem B3606263 : Blo 1600999 3606263 := bstep (se 1 (by rfl) ⟨2704697, by rfl⟩ : syracuseStep 3606263 = 5409395) B5409395
theorem B6080255 : Blo 1600999 6080255 := bstep (se 1 (by rfl) ⟨4560191, by rfl⟩ : syracuseStep 6080255 = 9120383) B9120383
theorem B233711567 : Blo 1600999 233711567 := bstep (se 1 (by rfl) ⟨175283675, by rfl⟩ : syracuseStep 233711567 = 350567351) B350567351
theorem B105392087 : Blo 1600999 105392087 := bstep (se 1 (by rfl) ⟨79044065, by rfl⟩ : syracuseStep 105392087 = 158088131) B158088131
theorem B3082207 : Blo 1600999 3082207 := bstep (se 1 (by rfl) ⟨2311655, by rfl⟩ : syracuseStep 3082207 = 4623311) B4623311
theorem B2402441 : Blo 1600999 2402441 := bstep (se 2 (by rfl) ⟨900915, by rfl⟩ : syracuseStep 2402441 = 1801831) B1801831
theorem B106735913 : Blo 1600999 106735913 := bstep (se 2 (by rfl) ⟨40025967, by rfl⟩ : syracuseStep 106735913 = 80051935) B80051935
theorem B4327777 : Blo 1600999 4327777 := bstep (se 2 (by rfl) ⟨1622916, by rfl⟩ : syracuseStep 4327777 = 3245833) B3245833
theorem B2280187 : Blo 1600999 2280187 := bstep (se 1 (by rfl) ⟨1710140, by rfl⟩ : syracuseStep 2280187 = 3420281) B3420281
theorem B2403071 : Blo 1600999 2403071 := bstep (se 1 (by rfl) ⟨1802303, by rfl⟩ : syracuseStep 2403071 = 3604607) B3604607
theorem B5409665 : Blo 1600999 5409665 := bstep (se 2 (by rfl) ⟨2028624, by rfl⟩ : syracuseStep 5409665 = 4057249) B4057249
theorem B2026559 : Blo 1600999 2026559 := bstep (se 1 (by rfl) ⟨1519919, by rfl⟩ : syracuseStep 2026559 = 3039839) B3039839
theorem B11545811 : Blo 1600999 11545811 := bstep (se 1 (by rfl) ⟨8659358, by rfl⟩ : syracuseStep 11545811 = 17318717) B17318717
theorem B2403791 : Blo 1600999 2403791 := bstep (se 1 (by rfl) ⟨1802843, by rfl⟩ : syracuseStep 2403791 = 3605687) B3605687
theorem B57028157 : Blo 1600999 57028157 := bstep (se 3 (by rfl) ⟨10692779, by rfl⟩ : syracuseStep 57028157 = 21385559) B21385559
theorem B4165339 : Blo 1600999 4165339 := bstep (se 1 (by rfl) ⟨3124004, by rfl⟩ : syracuseStep 4165339 = 6248009) B6248009
theorem B2404223 : Blo 1600999 2404223 := bstep (se 1 (by rfl) ⟨1803167, by rfl⟩ : syracuseStep 2404223 = 3606335) B3606335
theorem B1601759 : Blo 1600999 1601759 := bstep (se 1 (by rfl) ⟨1201319, by rfl⟩ : syracuseStep 1601759 = 2402639) B2402639
theorem B25997537 : Blo 1600999 25997537 := bstep (se 2 (by rfl) ⟨9749076, by rfl⟩ : syracuseStep 25997537 = 19498153) B19498153
theorem B333107635 : Blo 1600999 333107635 := bstep (se 1 (by rfl) ⟨249830726, by rfl⟩ : syracuseStep 333107635 = 499661453) B499661453
theorem B1602015 : Blo 1600999 1602015 := bstep (se 1 (by rfl) ⟨1201511, by rfl⟩ : syracuseStep 1602015 = 2403023) B2403023
theorem B1602031 : Blo 1600999 1602031 := bstep (se 1 (by rfl) ⟨1201523, by rfl⟩ : syracuseStep 1602031 = 2403047) B2403047
theorem B1602079 : Blo 1600999 1602079 := bstep (se 1 (by rfl) ⟨1201559, by rfl⟩ : syracuseStep 1602079 = 2403119) B2403119
theorem B1602255 : Blo 1600999 1602255 := bstep (se 1 (by rfl) ⟨1201691, by rfl⟩ : syracuseStep 1602255 = 2403383) B2403383
theorem B1602279 : Blo 1600999 1602279 := bstep (se 1 (by rfl) ⟨1201709, by rfl⟩ : syracuseStep 1602279 = 2403419) B2403419
theorem B1602431 : Blo 1600999 1602431 := bstep (se 1 (by rfl) ⟨1201823, by rfl⟩ : syracuseStep 1602431 = 2403647) B2403647
theorem B4559827 : Blo 1600999 4559827 := bstep (se 1 (by rfl) ⟨3419870, by rfl⟩ : syracuseStep 4559827 = 6839741) B6839741
theorem B1602587 : Blo 1600999 1602587 := bstep (se 1 (by rfl) ⟨1201940, by rfl⟩ : syracuseStep 1602587 = 2403881) B2403881
theorem B1602591 : Blo 1600999 1602591 := bstep (se 1 (by rfl) ⟨1201943, by rfl⟩ : syracuseStep 1602591 = 2403887) B2403887
theorem B2028655 : Blo 1600999 2028655 := bstep (se 1 (by rfl) ⟨1521491, by rfl⟩ : syracuseStep 2028655 = 3042983) B3042983
theorem B3421511 : Blo 1600999 3421511 := bstep (se 1 (by rfl) ⟨2566133, by rfl⟩ : syracuseStep 3421511 = 5132267) B5132267
theorem B3421759 : Blo 1600999 3421759 := bstep (se 1 (by rfl) ⟨2566319, by rfl⟩ : syracuseStep 3421759 = 5132639) B5132639
theorem B8656591 : Blo 1600999 8656591 := bstep (se 1 (by rfl) ⟨6492443, by rfl⟩ : syracuseStep 8656591 = 12984887) B12984887
theorem B2054143 : Blo 1600999 2054143 := bstep (se 1 (by rfl) ⟨1540607, by rfl⟩ : syracuseStep 2054143 = 3081215) B3081215
theorem B6936617 : Blo 1600999 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B3602555 : Blo 1600999 3602555 := bstep (se 1 (by rfl) ⟨2701916, by rfl⟩ : syracuseStep 3602555 = 5403833) B5403833
theorem B5404859 : Blo 1600999 5404859 := bstep (se 1 (by rfl) ⟨4053644, by rfl⟩ : syracuseStep 5404859 = 8107289) B8107289
theorem B65747141 : Blo 1600999 65747141 := bstep (se 4 (by rfl) ⟨6163794, by rfl⟩ : syracuseStep 65747141 = 12327589) B12327589
theorem B3603563 : Blo 1600999 3603563 := bstep (se 1 (by rfl) ⟨2702672, by rfl⟩ : syracuseStep 3603563 = 5405345) B5405345
theorem B5405831 : Blo 1600999 5405831 := bstep (se 1 (by rfl) ⟨4054373, by rfl⟩ : syracuseStep 5405831 = 8108747) B8108747
theorem B4054171 : Blo 1600999 4054171 := bstep (se 1 (by rfl) ⟨3040628, by rfl⟩ : syracuseStep 4054171 = 6081257) B6081257
theorem B3603617 : Blo 1600999 3603617 := bstep (se 2 (by rfl) ⟨1351356, by rfl⟩ : syracuseStep 3603617 = 2702713) B2702713
theorem B3849527 : Blo 1600999 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B6168095 : Blo 1600999 6168095 := bstep (se 1 (by rfl) ⟨4626071, by rfl⟩ : syracuseStep 6168095 = 9252143) B9252143
theorem B9125531 : Blo 1600999 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B9379493 : Blo 1600999 9379493 := bstep (se 4 (by rfl) ⟨879327, by rfl⟩ : syracuseStep 9379493 = 1758655) B1758655
theorem B3604175 : Blo 1600999 3604175 := bstep (se 1 (by rfl) ⟨2703131, by rfl⟩ : syracuseStep 3604175 = 5406263) B5406263
theorem B3604463 : Blo 1600999 3604463 := bstep (se 1 (by rfl) ⟨2703347, by rfl⟩ : syracuseStep 3604463 = 5406695) B5406695
theorem B18497645 : Blo 1600999 18497645 := bstep (se 3 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 18497645 = 6936617) B6936617
theorem B5407451 : Blo 1600999 5407451 := bstep (se 1 (by rfl) ⟨4055588, by rfl⟩ : syracuseStep 5407451 = 8111177) B8111177
theorem B12157775 : Blo 1600999 12157775 := bstep (se 1 (by rfl) ⟨9118331, by rfl⟩ : syracuseStep 12157775 = 18236663) B18236663
theorem B3040249 : Blo 1600999 3040249 := bstep (se 2 (by rfl) ⟨1140093, by rfl⟩ : syracuseStep 3040249 = 2280187) B2280187
theorem B5407883 : Blo 1600999 5407883 := bstep (se 1 (by rfl) ⟨4055912, by rfl⟩ : syracuseStep 5407883 = 8111825) B8111825
theorem B6079769 : Blo 1600999 6079769 := bstep (se 2 (by rfl) ⟨2279913, by rfl⟩ : syracuseStep 6079769 = 4559827) B4559827
theorem B2401703 : Blo 1600999 2401703 := bstep (se 1 (by rfl) ⟨1801277, by rfl⟩ : syracuseStep 2401703 = 3602555) B3602555
theorem B2704873 : Blo 1600999 2704873 := bstep (se 2 (by rfl) ⟨1014327, by rfl⟩ : syracuseStep 2704873 = 2028655) B2028655
theorem B71157275 : Blo 1600999 71157275 := bstep (se 1 (by rfl) ⟨53367956, by rfl⟩ : syracuseStep 71157275 = 106735913) B106735913
theorem B34637705 : Blo 1600999 34637705 := bstep (se 2 (by rfl) ⟨12989139, by rfl⟩ : syracuseStep 34637705 = 25978279) B25978279
theorem B3606443 : Blo 1600999 3606443 := bstep (se 1 (by rfl) ⟨2704832, by rfl⟩ : syracuseStep 3606443 = 5409665) B5409665
theorem B2402375 : Blo 1600999 2402375 := bstep (se 1 (by rfl) ⟨1801781, by rfl⟩ : syracuseStep 2402375 = 3603563) B3603563
theorem B2402411 : Blo 1600999 2402411 := bstep (se 1 (by rfl) ⟨1801808, by rfl⟩ : syracuseStep 2402411 = 3603617) B3603617
theorem B2566351 : Blo 1600999 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B6252995 : Blo 1600999 6252995 := bstep (se 1 (by rfl) ⟨4689746, by rfl⟩ : syracuseStep 6252995 = 9379493) B9379493
theorem B2402783 : Blo 1600999 2402783 := bstep (se 1 (by rfl) ⟨1802087, by rfl⟩ : syracuseStep 2402783 = 3604175) B3604175
theorem B2402975 : Blo 1600999 2402975 := bstep (se 1 (by rfl) ⟨1802231, by rfl⟩ : syracuseStep 2402975 = 3604463) B3604463
theorem B2738857 : Blo 1600999 2738857 := bstep (se 2 (by rfl) ⟨1027071, by rfl⟩ : syracuseStep 2738857 = 2054143) B2054143
theorem B2403323 : Blo 1600999 2403323 := bstep (se 1 (by rfl) ⟨1802492, by rfl⟩ : syracuseStep 2403323 = 3604985) B3604985
theorem B2403455 : Blo 1600999 2403455 := bstep (se 1 (by rfl) ⟨1802591, by rfl⟩ : syracuseStep 2403455 = 3605183) B3605183
theorem B5770369 : Blo 1600999 5770369 := bstep (se 2 (by rfl) ⟨2163888, by rfl⟩ : syracuseStep 5770369 = 4327777) B4327777
theorem B26324351 : Blo 1600999 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B43855303 : Blo 1600999 43855303 := bstep (se 1 (by rfl) ⟨32891477, by rfl⟩ : syracuseStep 43855303 = 65782955) B65782955
theorem B2403839 : Blo 1600999 2403839 := bstep (se 1 (by rfl) ⟨1802879, by rfl⟩ : syracuseStep 2403839 = 3605759) B3605759
theorem B2281007 : Blo 1600999 2281007 := bstep (se 1 (by rfl) ⟨1710755, by rfl⟩ : syracuseStep 2281007 = 3421511) B3421511
theorem B2404175 : Blo 1600999 2404175 := bstep (se 1 (by rfl) ⟨1803131, by rfl⟩ : syracuseStep 2404175 = 3606263) B3606263
theorem B155807711 : Blo 1600999 155807711 := bstep (se 1 (by rfl) ⟨116855783, by rfl⟩ : syracuseStep 155807711 = 233711567) B233711567
theorem B1601627 : Blo 1600999 1601627 := bstep (se 1 (by rfl) ⟨1201220, by rfl⟩ : syracuseStep 1601627 = 2402441) B2402441
theorem B43831427 : Blo 1600999 43831427 := bstep (se 1 (by rfl) ⟨32873570, by rfl⟩ : syracuseStep 43831427 = 65747141) B65747141
theorem B1602047 : Blo 1600999 1602047 := bstep (se 1 (by rfl) ⟨1201535, by rfl⟩ : syracuseStep 1602047 = 2403071) B2403071
theorem B7697207 : Blo 1600999 7697207 := bstep (se 1 (by rfl) ⟨5772905, by rfl⟩ : syracuseStep 7697207 = 11545811) B11545811
theorem B1602527 : Blo 1600999 1602527 := bstep (se 1 (by rfl) ⟨1201895, by rfl⟩ : syracuseStep 1602527 = 2403791) B2403791
theorem B6083687 : Blo 1600999 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B1602815 : Blo 1600999 1602815 := bstep (se 1 (by rfl) ⟨1202111, by rfl⟩ : syracuseStep 1602815 = 2404223) B2404223
theorem B4109609 : Blo 1600999 4109609 := bstep (se 2 (by rfl) ⟨1541103, by rfl⟩ : syracuseStep 4109609 = 3082207) B3082207
theorem B5772647 : Blo 1600999 5772647 := bstep (se 1 (by rfl) ⟨4329485, by rfl⟩ : syracuseStep 5772647 = 8658971) B8658971
theorem B17331691 : Blo 1600999 17331691 := bstep (se 1 (by rfl) ⟨12998768, by rfl⟩ : syracuseStep 17331691 = 25997537) B25997537
theorem B5404157 : Blo 1600999 5404157 := bstep (se 3 (by rfl) ⟨1013279, by rfl⟩ : syracuseStep 5404157 = 2026559) B2026559
theorem B444143513 : Blo 1600999 444143513 := bstep (se 2 (by rfl) ⟨166553817, by rfl⟩ : syracuseStep 444143513 = 333107635) B333107635
theorem B4053503 : Blo 1600999 4053503 := bstep (se 1 (by rfl) ⟨3040127, by rfl⟩ : syracuseStep 4053503 = 6080255) B6080255
theorem B70261391 : Blo 1600999 70261391 := bstep (se 1 (by rfl) ⟨52696043, by rfl⟩ : syracuseStep 70261391 = 105392087) B105392087
theorem B3603239 : Blo 1600999 3603239 := bstep (se 1 (by rfl) ⟨2702429, by rfl⟩ : syracuseStep 3603239 = 5404859) B5404859
theorem B5405561 : Blo 1600999 5405561 := bstep (se 2 (by rfl) ⟨2027085, by rfl⟩ : syracuseStep 5405561 = 4054171) B4054171
theorem B4562345 : Blo 1600999 4562345 := bstep (se 2 (by rfl) ⟨1710879, by rfl⟩ : syracuseStep 4562345 = 3421759) B3421759
theorem B3603887 : Blo 1600999 3603887 := bstep (se 1 (by rfl) ⟨2702915, by rfl⟩ : syracuseStep 3603887 = 5405831) B5405831
theorem B11542121 : Blo 1600999 11542121 := bstep (se 2 (by rfl) ⟨4328295, by rfl⟩ : syracuseStep 11542121 = 8656591) B8656591
theorem B5553785 : Blo 1600999 5553785 := bstep (se 2 (by rfl) ⟨2082669, by rfl⟩ : syracuseStep 5553785 = 4165339) B4165339
theorem B4054657 : Blo 1600999 4054657 := bstep (se 2 (by rfl) ⟨1520496, by rfl⟩ : syracuseStep 4054657 = 3040993) B3040993
theorem B4112063 : Blo 1600999 4112063 := bstep (se 1 (by rfl) ⟨3084047, by rfl⟩ : syracuseStep 4112063 = 6168095) B6168095
theorem B38018771 : Blo 1600999 38018771 := bstep (se 1 (by rfl) ⟨28514078, by rfl⟩ : syracuseStep 38018771 = 57028157) B57028157
theorem B116883805 : Blo 1600999 116883805 := bstep (se 3 (by rfl) ⟨21915713, by rfl⟩ : syracuseStep 116883805 = 43831427) B43831427
theorem B3604967 : Blo 1600999 3604967 := bstep (se 1 (by rfl) ⟨2703725, by rfl⟩ : syracuseStep 3604967 = 5407451) B5407451
theorem B4055791 : Blo 1600999 4055791 := bstep (se 1 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 4055791 = 6083687) B6083687
theorem B3605255 : Blo 1600999 3605255 := bstep (se 1 (by rfl) ⟨2703941, by rfl⟩ : syracuseStep 3605255 = 5407883) B5407883
theorem B15393725 : Blo 1600999 15393725 := bstep (se 3 (by rfl) ⟨2886323, by rfl⟩ : syracuseStep 15393725 = 5772647) B5772647
theorem B7693825 : Blo 1600999 7693825 := bstep (se 2 (by rfl) ⟨2885184, by rfl⟩ : syracuseStep 7693825 = 5770369) B5770369
theorem B2402159 : Blo 1600999 2402159 := bstep (se 1 (by rfl) ⟨1801619, by rfl⟩ : syracuseStep 2402159 = 3603239) B3603239
theorem B3606497 : Blo 1600999 3606497 := bstep (se 2 (by rfl) ⟨1352436, by rfl⟩ : syracuseStep 3606497 = 2704873) B2704873
theorem B17549567 : Blo 1600999 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B3041563 : Blo 1600999 3041563 := bstep (se 1 (by rfl) ⟨2281172, by rfl⟩ : syracuseStep 3041563 = 4562345) B4562345
theorem B2402591 : Blo 1600999 2402591 := bstep (se 1 (by rfl) ⟨1801943, by rfl⟩ : syracuseStep 2402591 = 3603887) B3603887
theorem B7694747 : Blo 1600999 7694747 := bstep (se 1 (by rfl) ⟨5771060, by rfl⟩ : syracuseStep 7694747 = 11542121) B11542121
theorem B12331763 : Blo 1600999 12331763 := bstep (se 1 (by rfl) ⟨9248822, by rfl⟩ : syracuseStep 12331763 = 18497645) B18497645
theorem B8105183 : Blo 1600999 8105183 := bstep (se 1 (by rfl) ⟨6078887, by rfl⟩ : syracuseStep 8105183 = 12157775) B12157775
theorem B2739739 : Blo 1600999 2739739 := bstep (se 1 (by rfl) ⟨2054804, by rfl⟩ : syracuseStep 2739739 = 4109609) B4109609
theorem B1601135 : Blo 1600999 1601135 := bstep (se 1 (by rfl) ⟨1200851, by rfl⟩ : syracuseStep 1601135 = 2401703) B2401703
theorem B16674653 : Blo 1600999 16674653 := bstep (se 3 (by rfl) ⟨3126497, by rfl⟩ : syracuseStep 16674653 = 6252995) B6252995
theorem B296095675 : Blo 1600999 296095675 := bstep (se 1 (by rfl) ⟨222071756, by rfl⟩ : syracuseStep 296095675 = 444143513) B444143513
theorem B2404295 : Blo 1600999 2404295 := bstep (se 1 (by rfl) ⟨1803221, by rfl⟩ : syracuseStep 2404295 = 3606443) B3606443
theorem B1601583 : Blo 1600999 1601583 := bstep (se 1 (by rfl) ⟨1201187, by rfl⟩ : syracuseStep 1601583 = 2402375) B2402375
theorem B1601607 : Blo 1600999 1601607 := bstep (se 1 (by rfl) ⟨1201205, by rfl⟩ : syracuseStep 1601607 = 2402411) B2402411
theorem B6082685 : Blo 1600999 6082685 := bstep (se 3 (by rfl) ⟨1140503, by rfl⟩ : syracuseStep 6082685 = 2281007) B2281007
theorem B1601855 : Blo 1600999 1601855 := bstep (se 1 (by rfl) ⟨1201391, by rfl⟩ : syracuseStep 1601855 = 2402783) B2402783
theorem B1601983 : Blo 1600999 1601983 := bstep (se 1 (by rfl) ⟨1201487, by rfl⟩ : syracuseStep 1601983 = 2402975) B2402975
theorem B1602215 : Blo 1600999 1602215 := bstep (se 1 (by rfl) ⟨1201661, by rfl⟩ : syracuseStep 1602215 = 2403323) B2403323
theorem B1602303 : Blo 1600999 1602303 := bstep (se 1 (by rfl) ⟨1201727, by rfl⟩ : syracuseStep 1602303 = 2403455) B2403455
theorem B20525885 : Blo 1600999 20525885 := bstep (se 3 (by rfl) ⟨3848603, by rfl⟩ : syracuseStep 20525885 = 7697207) B7697207
theorem B1602559 : Blo 1600999 1602559 := bstep (se 1 (by rfl) ⟨1201919, by rfl⟩ : syracuseStep 1602559 = 2403839) B2403839
theorem B2741375 : Blo 1600999 2741375 := bstep (se 1 (by rfl) ⟨2056031, by rfl⟩ : syracuseStep 2741375 = 4112063) B4112063
theorem B1602783 : Blo 1600999 1602783 := bstep (se 1 (by rfl) ⟨1202087, by rfl⟩ : syracuseStep 1602783 = 2404175) B2404175
theorem B103871807 : Blo 1600999 103871807 := bstep (se 1 (by rfl) ⟨77903855, by rfl⟩ : syracuseStep 103871807 = 155807711) B155807711
theorem B3421801 : Blo 1600999 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B4053179 : Blo 1600999 4053179 := bstep (se 1 (by rfl) ⟨3039884, by rfl⟩ : syracuseStep 4053179 = 6079769) B6079769
theorem B3651809 : Blo 1600999 3651809 := bstep (se 2 (by rfl) ⟨1369428, by rfl⟩ : syracuseStep 3651809 = 2738857) B2738857
theorem B3602771 : Blo 1600999 3602771 := bstep (se 1 (by rfl) ⟨2702078, by rfl⟩ : syracuseStep 3602771 = 5404157) B5404157
theorem B47438183 : Blo 1600999 47438183 := bstep (se 1 (by rfl) ⟨35578637, by rfl⟩ : syracuseStep 47438183 = 71157275) B71157275
theorem B23091803 : Blo 1600999 23091803 := bstep (se 1 (by rfl) ⟨17318852, by rfl⟩ : syracuseStep 23091803 = 34637705) B34637705
theorem B4053665 : Blo 1600999 4053665 := bstep (se 2 (by rfl) ⟨1520124, by rfl⟩ : syracuseStep 4053665 = 3040249) B3040249
theorem B2702335 : Blo 1600999 2702335 := bstep (se 1 (by rfl) ⟨2026751, by rfl⟩ : syracuseStep 2702335 = 4053503) B4053503
theorem B46840927 : Blo 1600999 46840927 := bstep (se 1 (by rfl) ⟨35130695, by rfl⟩ : syracuseStep 46840927 = 70261391) B70261391
theorem B3603707 : Blo 1600999 3603707 := bstep (se 1 (by rfl) ⟨2702780, by rfl⟩ : syracuseStep 3603707 = 5405561) B5405561
theorem B58473737 : Blo 1600999 58473737 := bstep (se 2 (by rfl) ⟨21927651, by rfl⟩ : syracuseStep 58473737 = 43855303) B43855303
theorem B23108921 : Blo 1600999 23108921 := bstep (se 2 (by rfl) ⟨8665845, by rfl⟩ : syracuseStep 23108921 = 17331691) B17331691
theorem B5406209 : Blo 1600999 5406209 := bstep (se 2 (by rfl) ⟨2027328, by rfl⟩ : syracuseStep 5406209 = 4054657) B4054657
theorem B3702523 : Blo 1600999 3702523 := bstep (se 1 (by rfl) ⟨2776892, by rfl⟩ : syracuseStep 3702523 = 5553785) B5553785
theorem B25345847 : Blo 1600999 25345847 := bstep (se 1 (by rfl) ⟨19009385, by rfl⟩ : syracuseStep 25345847 = 38018771) B38018771
theorem B4055123 : Blo 1600999 4055123 := bstep (se 1 (by rfl) ⟨3041342, by rfl⟩ : syracuseStep 4055123 = 6082685) B6082685
theorem B4055417 : Blo 1600999 4055417 := bstep (se 2 (by rfl) ⟨1520781, by rfl⟩ : syracuseStep 4055417 = 3041563) B3041563
theorem B155845073 : Blo 1600999 155845073 := bstep (se 2 (by rfl) ⟨58441902, by rfl⟩ : syracuseStep 155845073 = 116883805) B116883805
theorem B69247871 : Blo 1600999 69247871 := bstep (se 1 (by rfl) ⟨51935903, by rfl⟩ : syracuseStep 69247871 = 103871807) B103871807
theorem B126501821 : Blo 1600999 126501821 := bstep (se 3 (by rfl) ⟨23719091, by rfl⟩ : syracuseStep 126501821 = 47438183) B47438183
theorem B5407721 : Blo 1600999 5407721 := bstep (se 2 (by rfl) ⟨2027895, by rfl⟩ : syracuseStep 5407721 = 4055791) B4055791
theorem B11699711 : Blo 1600999 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B2401847 : Blo 1600999 2401847 := bstep (se 1 (by rfl) ⟨1801385, by rfl⟩ : syracuseStep 2401847 = 3602771) B3602771
theorem B5129831 : Blo 1600999 5129831 := bstep (se 1 (by rfl) ⟨3847373, by rfl⟩ : syracuseStep 5129831 = 7694747) B7694747
theorem B15394535 : Blo 1600999 15394535 := bstep (se 1 (by rfl) ⟨11545901, by rfl⟩ : syracuseStep 15394535 = 23091803) B23091803
theorem B10258433 : Blo 1600999 10258433 := bstep (se 2 (by rfl) ⟨3846912, by rfl⟩ : syracuseStep 10258433 = 7693825) B7693825
theorem B2402471 : Blo 1600999 2402471 := bstep (se 1 (by rfl) ⟨1801853, by rfl⟩ : syracuseStep 2402471 = 3603707) B3603707
theorem B2403311 : Blo 1600999 2403311 := bstep (se 1 (by rfl) ⟨1802483, by rfl⟩ : syracuseStep 2403311 = 3604967) B3604967
theorem B7310333 : Blo 1600999 7310333 := bstep (se 3 (by rfl) ⟨1370687, by rfl⟩ : syracuseStep 7310333 = 2741375) B2741375
theorem B2403503 : Blo 1600999 2403503 := bstep (se 1 (by rfl) ⟨1802627, by rfl⟩ : syracuseStep 2403503 = 3605255) B3605255
theorem B13683923 : Blo 1600999 13683923 := bstep (se 1 (by rfl) ⟨10262942, by rfl⟩ : syracuseStep 13683923 = 20525885) B20525885
theorem B1601439 : Blo 1600999 1601439 := bstep (se 1 (by rfl) ⟨1201079, by rfl⟩ : syracuseStep 1601439 = 2402159) B2402159
theorem B2404331 : Blo 1600999 2404331 := bstep (se 1 (by rfl) ⟨1803248, by rfl⟩ : syracuseStep 2404331 = 3606497) B3606497
theorem B1601727 : Blo 1600999 1601727 := bstep (se 1 (by rfl) ⟨1201295, by rfl⟩ : syracuseStep 1601727 = 2402591) B2402591
theorem B8221175 : Blo 1600999 8221175 := bstep (se 1 (by rfl) ⟨6165881, by rfl⟩ : syracuseStep 8221175 = 12331763) B12331763
theorem B5403455 : Blo 1600999 5403455 := bstep (se 1 (by rfl) ⟨4052591, by rfl⟩ : syracuseStep 5403455 = 8105183) B8105183
theorem B38982491 : Blo 1600999 38982491 := bstep (se 1 (by rfl) ⟨29236868, by rfl⟩ : syracuseStep 38982491 = 58473737) B58473737
theorem B15405947 : Blo 1600999 15405947 := bstep (se 1 (by rfl) ⟨11554460, by rfl⟩ : syracuseStep 15405947 = 23108921) B23108921
theorem B4936697 : Blo 1600999 4936697 := bstep (se 2 (by rfl) ⟨1851261, by rfl⟩ : syracuseStep 4936697 = 3702523) B3702523
theorem B16897231 : Blo 1600999 16897231 := bstep (se 1 (by rfl) ⟨12672923, by rfl⟩ : syracuseStep 16897231 = 25345847) B25345847
theorem B394794233 : Blo 1600999 394794233 := bstep (se 2 (by rfl) ⟨148047837, by rfl⟩ : syracuseStep 394794233 = 296095675) B296095675
theorem B1602863 : Blo 1600999 1602863 := bstep (se 1 (by rfl) ⟨1202147, by rfl⟩ : syracuseStep 1602863 = 2404295) B2404295
theorem B9738157 : Blo 1600999 9738157 := bstep (se 3 (by rfl) ⟨1825904, by rfl⟩ : syracuseStep 9738157 = 3651809) B3651809
theorem B10262483 : Blo 1600999 10262483 := bstep (se 1 (by rfl) ⟨7696862, by rfl⟩ : syracuseStep 10262483 = 15393725) B15393725
theorem B3603113 : Blo 1600999 3603113 := bstep (se 2 (by rfl) ⟨1351167, by rfl⟩ : syracuseStep 3603113 = 2702335) B2702335
theorem B2702119 : Blo 1600999 2702119 := bstep (se 1 (by rfl) ⟨2026589, by rfl⟩ : syracuseStep 2702119 = 4053179) B4053179
theorem B62454569 : Blo 1600999 62454569 := bstep (se 2 (by rfl) ⟨23420463, by rfl⟩ : syracuseStep 62454569 = 46840927) B46840927
theorem B2702443 : Blo 1600999 2702443 := bstep (se 1 (by rfl) ⟨2026832, by rfl⟩ : syracuseStep 2702443 = 4053665) B4053665
theorem B3652985 : Blo 1600999 3652985 := bstep (se 2 (by rfl) ⟨1369869, by rfl⟩ : syracuseStep 3652985 = 2739739) B2739739
theorem B4562401 : Blo 1600999 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B3604139 : Blo 1600999 3604139 := bstep (se 1 (by rfl) ⟨2703104, by rfl⟩ : syracuseStep 3604139 = 5406209) B5406209
theorem B11116435 : Blo 1600999 11116435 := bstep (se 1 (by rfl) ⟨8337326, by rfl⟩ : syracuseStep 11116435 = 16674653) B16674653
theorem B2703415 : Blo 1600999 2703415 := bstep (se 1 (by rfl) ⟨2027561, by rfl⟩ : syracuseStep 2703415 = 4055123) B4055123
theorem B2703611 : Blo 1600999 2703611 := bstep (se 1 (by rfl) ⟨2027708, by rfl⟩ : syracuseStep 2703611 = 4055417) B4055417
theorem B5480783 : Blo 1600999 5480783 := bstep (se 1 (by rfl) ⟨4110587, by rfl⟩ : syracuseStep 5480783 = 8221175) B8221175
theorem B3605147 : Blo 1600999 3605147 := bstep (se 1 (by rfl) ⟨2703860, by rfl⟩ : syracuseStep 3605147 = 5407721) B5407721
theorem B7799807 : Blo 1600999 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B6841655 : Blo 1600999 6841655 := bstep (se 1 (by rfl) ⟨5131241, by rfl⟩ : syracuseStep 6841655 = 10262483) B10262483
theorem B2402075 : Blo 1600999 2402075 := bstep (se 1 (by rfl) ⟨1801556, by rfl⟩ : syracuseStep 2402075 = 3603113) B3603113
theorem B166545517 : Blo 1600999 166545517 := bstep (se 3 (by rfl) ⟨31227284, by rfl⟩ : syracuseStep 166545517 = 62454569) B62454569
theorem B2435323 : Blo 1600999 2435323 := bstep (se 1 (by rfl) ⟨1826492, by rfl⟩ : syracuseStep 2435323 = 3652985) B3652985
theorem B2402759 : Blo 1600999 2402759 := bstep (se 1 (by rfl) ⟨1802069, by rfl⟩ : syracuseStep 2402759 = 3604139) B3604139
theorem B14821913 : Blo 1600999 14821913 := bstep (se 2 (by rfl) ⟨5558217, by rfl⟩ : syracuseStep 14821913 = 11116435) B11116435
theorem B25988327 : Blo 1600999 25988327 := bstep (se 1 (by rfl) ⟨19491245, by rfl⟩ : syracuseStep 25988327 = 38982491) B38982491
theorem B46165247 : Blo 1600999 46165247 := bstep (se 1 (by rfl) ⟨34623935, by rfl⟩ : syracuseStep 46165247 = 69247871) B69247871
theorem B263196155 : Blo 1600999 263196155 := bstep (se 1 (by rfl) ⟨197397116, by rfl⟩ : syracuseStep 263196155 = 394794233) B394794233
theorem B1601231 : Blo 1600999 1601231 := bstep (se 1 (by rfl) ⟨1200923, by rfl⟩ : syracuseStep 1601231 = 2401847) B2401847
theorem B1601647 : Blo 1600999 1601647 := bstep (se 1 (by rfl) ⟨1201235, by rfl⟩ : syracuseStep 1601647 = 2402471) B2402471
theorem B6083201 : Blo 1600999 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B1602207 : Blo 1600999 1602207 := bstep (se 1 (by rfl) ⟨1201655, by rfl⟩ : syracuseStep 1602207 = 2403311) B2403311
theorem B1602335 : Blo 1600999 1602335 := bstep (se 1 (by rfl) ⟨1201751, by rfl⟩ : syracuseStep 1602335 = 2403503) B2403503
theorem B9122615 : Blo 1600999 9122615 := bstep (se 1 (by rfl) ⟨6841961, by rfl⟩ : syracuseStep 9122615 = 13683923) B13683923
theorem B1602887 : Blo 1600999 1602887 := bstep (se 1 (by rfl) ⟨1202165, by rfl⟩ : syracuseStep 1602887 = 2404331) B2404331
theorem B103896715 : Blo 1600999 103896715 := bstep (se 1 (by rfl) ⟨77922536, by rfl⟩ : syracuseStep 103896715 = 155845073) B155845073
theorem B3602303 : Blo 1600999 3602303 := bstep (se 1 (by rfl) ⟨2701727, by rfl⟩ : syracuseStep 3602303 = 5403455) B5403455
theorem B10270631 : Blo 1600999 10270631 := bstep (se 1 (by rfl) ⟨7702973, by rfl⟩ : syracuseStep 10270631 = 15405947) B15405947
theorem B84334547 : Blo 1600999 84334547 := bstep (se 1 (by rfl) ⟨63250910, by rfl⟩ : syracuseStep 84334547 = 126501821) B126501821
theorem B3291131 : Blo 1600999 3291131 := bstep (se 1 (by rfl) ⟨2468348, by rfl⟩ : syracuseStep 3291131 = 4936697) B4936697
theorem B3602825 : Blo 1600999 3602825 := bstep (se 2 (by rfl) ⟨1351059, by rfl⟩ : syracuseStep 3602825 = 2702119) B2702119
theorem B90118565 : Blo 1600999 90118565 := bstep (se 4 (by rfl) ⟨8448615, by rfl⟩ : syracuseStep 90118565 = 16897231) B16897231
theorem B10263023 : Blo 1600999 10263023 := bstep (se 1 (by rfl) ⟨7697267, by rfl⟩ : syracuseStep 10263023 = 15394535) B15394535
theorem B6838955 : Blo 1600999 6838955 := bstep (se 1 (by rfl) ⟨5129216, by rfl⟩ : syracuseStep 6838955 = 10258433) B10258433
theorem B3603257 : Blo 1600999 3603257 := bstep (se 2 (by rfl) ⟨1351221, by rfl⟩ : syracuseStep 3603257 = 2702443) B2702443
theorem B13679549 : Blo 1600999 13679549 := bstep (se 3 (by rfl) ⟨2564915, by rfl⟩ : syracuseStep 13679549 = 5129831) B5129831
theorem B4873555 : Blo 1600999 4873555 := bstep (se 1 (by rfl) ⟨3655166, by rfl⟩ : syracuseStep 4873555 = 7310333) B7310333
theorem B12984209 : Blo 1600999 12984209 := bstep (se 2 (by rfl) ⟨4869078, by rfl⟩ : syracuseStep 12984209 = 9738157) B9738157
theorem B3604553 : Blo 1600999 3604553 := bstep (se 2 (by rfl) ⟨1351707, by rfl⟩ : syracuseStep 3604553 = 2703415) B2703415
theorem B222060689 : Blo 1600999 222060689 := bstep (se 2 (by rfl) ⟨83272758, by rfl⟩ : syracuseStep 222060689 = 166545517) B166545517
theorem B1802407 : Blo 1600999 1802407 := bstep (se 1 (by rfl) ⟨1351805, by rfl⟩ : syracuseStep 1802407 = 2703611) B2703611
theorem B3653855 : Blo 1600999 3653855 := bstep (se 1 (by rfl) ⟨2740391, by rfl⟩ : syracuseStep 3653855 = 5480783) B5480783
theorem B4055467 : Blo 1600999 4055467 := bstep (se 1 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 4055467 = 6083201) B6083201
theorem B2401535 : Blo 1600999 2401535 := bstep (se 1 (by rfl) ⟨1801151, by rfl⟩ : syracuseStep 2401535 = 3602303) B3602303
theorem B56223031 : Blo 1600999 56223031 := bstep (se 1 (by rfl) ⟨42167273, by rfl⟩ : syracuseStep 56223031 = 84334547) B84334547
theorem B2401883 : Blo 1600999 2401883 := bstep (se 1 (by rfl) ⟨1801412, by rfl⟩ : syracuseStep 2401883 = 3602825) B3602825
theorem B6842015 : Blo 1600999 6842015 := bstep (se 1 (by rfl) ⟨5131511, by rfl⟩ : syracuseStep 6842015 = 10263023) B10263023
theorem B9881275 : Blo 1600999 9881275 := bstep (se 1 (by rfl) ⟨7410956, by rfl⟩ : syracuseStep 9881275 = 14821913) B14821913
theorem B6498073 : Blo 1600999 6498073 := bstep (se 2 (by rfl) ⟨2436777, by rfl⟩ : syracuseStep 6498073 = 4873555) B4873555
theorem B2402171 : Blo 1600999 2402171 := bstep (se 1 (by rfl) ⟨1801628, by rfl⟩ : syracuseStep 2402171 = 3603257) B3603257
theorem B9119699 : Blo 1600999 9119699 := bstep (se 1 (by rfl) ⟨6839774, by rfl⟩ : syracuseStep 9119699 = 13679549) B13679549
theorem B138528953 : Blo 1600999 138528953 := bstep (se 2 (by rfl) ⟨51948357, by rfl⟩ : syracuseStep 138528953 = 103896715) B103896715
theorem B8776349 : Blo 1600999 8776349 := bstep (se 3 (by rfl) ⟨1645565, by rfl⟩ : syracuseStep 8776349 = 3291131) B3291131
theorem B3247097 : Blo 1600999 3247097 := bstep (se 2 (by rfl) ⟨1217661, by rfl⟩ : syracuseStep 3247097 = 2435323) B2435323
theorem B2403431 : Blo 1600999 2403431 := bstep (se 1 (by rfl) ⟨1802573, by rfl⟩ : syracuseStep 2403431 = 3605147) B3605147
theorem B6081743 : Blo 1600999 6081743 := bstep (se 1 (by rfl) ⟨4561307, by rfl⟩ : syracuseStep 6081743 = 9122615) B9122615
theorem B1601383 : Blo 1600999 1601383 := bstep (se 1 (by rfl) ⟨1201037, by rfl⟩ : syracuseStep 1601383 = 2402075) B2402075
theorem B1601839 : Blo 1600999 1601839 := bstep (se 1 (by rfl) ⟨1201379, by rfl⟩ : syracuseStep 1601839 = 2402759) B2402759
theorem B4559303 : Blo 1600999 4559303 := bstep (se 1 (by rfl) ⟨3419477, by rfl⟩ : syracuseStep 4559303 = 6838955) B6838955
theorem B8656139 : Blo 1600999 8656139 := bstep (se 1 (by rfl) ⟨6492104, by rfl⟩ : syracuseStep 8656139 = 12984209) B12984209
theorem B5199871 : Blo 1600999 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B4561103 : Blo 1600999 4561103 := bstep (se 1 (by rfl) ⟨3420827, by rfl⟩ : syracuseStep 4561103 = 6841655) B6841655
theorem B6847087 : Blo 1600999 6847087 := bstep (se 1 (by rfl) ⟨5135315, by rfl⟩ : syracuseStep 6847087 = 10270631) B10270631
theorem B60079043 : Blo 1600999 60079043 := bstep (se 1 (by rfl) ⟨45059282, by rfl⟩ : syracuseStep 60079043 = 90118565) B90118565
theorem B17325551 : Blo 1600999 17325551 := bstep (se 1 (by rfl) ⟨12994163, by rfl⟩ : syracuseStep 17325551 = 25988327) B25988327
theorem B30776831 : Blo 1600999 30776831 := bstep (se 1 (by rfl) ⟨23082623, by rfl⟩ : syracuseStep 30776831 = 46165247) B46165247
theorem B175464103 : Blo 1600999 175464103 := bstep (se 1 (by rfl) ⟨131598077, by rfl⟩ : syracuseStep 175464103 = 263196155) B263196155
theorem B3039535 : Blo 1600999 3039535 := bstep (se 1 (by rfl) ⟨2279651, by rfl⟩ : syracuseStep 3039535 = 4559303) B4559303
theorem B5407289 : Blo 1600999 5407289 := bstep (se 2 (by rfl) ⟨2027733, by rfl⟩ : syracuseStep 5407289 = 4055467) B4055467
theorem B6079799 : Blo 1600999 6079799 := bstep (se 1 (by rfl) ⟨4559849, by rfl⟩ : syracuseStep 6079799 = 9119699) B9119699
theorem B3040735 : Blo 1600999 3040735 := bstep (se 1 (by rfl) ⟨2280551, by rfl⟩ : syracuseStep 3040735 = 4561103) B4561103
theorem B5850899 : Blo 1600999 5850899 := bstep (se 1 (by rfl) ⟨4388174, by rfl⟩ : syracuseStep 5850899 = 8776349) B8776349
theorem B13175033 : Blo 1600999 13175033 := bstep (se 2 (by rfl) ⟨4940637, by rfl⟩ : syracuseStep 13175033 = 9881275) B9881275
theorem B6933161 : Blo 1600999 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B2403035 : Blo 1600999 2403035 := bstep (se 1 (by rfl) ⟨1802276, by rfl⟩ : syracuseStep 2403035 = 3604553) B3604553
theorem B148040459 : Blo 1600999 148040459 := bstep (se 1 (by rfl) ⟨111030344, by rfl⟩ : syracuseStep 148040459 = 222060689) B222060689
theorem B2435903 : Blo 1600999 2435903 := bstep (se 1 (by rfl) ⟨1826927, by rfl⟩ : syracuseStep 2435903 = 3653855) B3653855
theorem B2403209 : Blo 1600999 2403209 := bstep (se 2 (by rfl) ⟨901203, by rfl⟩ : syracuseStep 2403209 = 1802407) B1802407
theorem B9129449 : Blo 1600999 9129449 := bstep (se 2 (by rfl) ⟨3423543, by rfl⟩ : syracuseStep 9129449 = 6847087) B6847087
theorem B1601023 : Blo 1600999 1601023 := bstep (se 1 (by rfl) ⟨1200767, by rfl⟩ : syracuseStep 1601023 = 2401535) B2401535
theorem B5770759 : Blo 1600999 5770759 := bstep (se 1 (by rfl) ⟨4328069, by rfl⟩ : syracuseStep 5770759 = 8656139) B8656139
theorem B1601255 : Blo 1600999 1601255 := bstep (se 1 (by rfl) ⟨1200941, by rfl⟩ : syracuseStep 1601255 = 2401883) B2401883
theorem B1601447 : Blo 1600999 1601447 := bstep (se 1 (by rfl) ⟨1201085, by rfl⟩ : syracuseStep 1601447 = 2402171) B2402171
theorem B92352635 : Blo 1600999 92352635 := bstep (se 1 (by rfl) ⟨69264476, by rfl⟩ : syracuseStep 92352635 = 138528953) B138528953
theorem B1602287 : Blo 1600999 1602287 := bstep (se 1 (by rfl) ⟨1201715, by rfl⟩ : syracuseStep 1602287 = 2403431) B2403431
theorem B233952137 : Blo 1600999 233952137 := bstep (se 2 (by rfl) ⟨87732051, by rfl⟩ : syracuseStep 233952137 = 175464103) B175464103
theorem B20517887 : Blo 1600999 20517887 := bstep (se 1 (by rfl) ⟨15388415, by rfl⟩ : syracuseStep 20517887 = 30776831) B30776831
theorem B8664097 : Blo 1600999 8664097 := bstep (se 2 (by rfl) ⟨3249036, by rfl⟩ : syracuseStep 8664097 = 6498073) B6498073
theorem B4561343 : Blo 1600999 4561343 := bstep (se 1 (by rfl) ⟨3421007, by rfl⟩ : syracuseStep 4561343 = 6842015) B6842015
theorem B74964041 : Blo 1600999 74964041 := bstep (se 2 (by rfl) ⟨28111515, by rfl⟩ : syracuseStep 74964041 = 56223031) B56223031
theorem B4054495 : Blo 1600999 4054495 := bstep (se 1 (by rfl) ⟨3040871, by rfl⟩ : syracuseStep 4054495 = 6081743) B6081743
theorem B11550367 : Blo 1600999 11550367 := bstep (se 1 (by rfl) ⟨8662775, by rfl⟩ : syracuseStep 11550367 = 17325551) B17325551
theorem B160210781 : Blo 1600999 160210781 := bstep (se 3 (by rfl) ⟨30039521, by rfl⟩ : syracuseStep 160210781 = 60079043) B60079043
theorem B34635701 : Blo 1600999 34635701 := bstep (se 5 (by rfl) ⟨1623548, by rfl⟩ : syracuseStep 34635701 = 3247097) B3247097
theorem B3604859 : Blo 1600999 3604859 := bstep (se 1 (by rfl) ⟨2703644, by rfl⟩ : syracuseStep 3604859 = 5407289) B5407289
theorem B155968091 : Blo 1600999 155968091 := bstep (se 1 (by rfl) ⟨116976068, by rfl⟩ : syracuseStep 155968091 = 233952137) B233952137
theorem B3900599 : Blo 1600999 3900599 := bstep (se 1 (by rfl) ⟨2925449, by rfl⟩ : syracuseStep 3900599 = 5850899) B5850899
theorem B11552129 : Blo 1600999 11552129 := bstep (se 2 (by rfl) ⟨4332048, by rfl⟩ : syracuseStep 11552129 = 8664097) B8664097
theorem B3040895 : Blo 1600999 3040895 := bstep (se 1 (by rfl) ⟨2280671, by rfl⟩ : syracuseStep 3040895 = 4561343) B4561343
theorem B1623935 : Blo 1600999 1623935 := bstep (se 1 (by rfl) ⟨1217951, by rfl⟩ : syracuseStep 1623935 = 2435903) B2435903
theorem B7694345 : Blo 1600999 7694345 := bstep (se 2 (by rfl) ⟨2885379, by rfl⟩ : syracuseStep 7694345 = 5770759) B5770759
theorem B1602023 : Blo 1600999 1602023 := bstep (se 1 (by rfl) ⟨1201517, by rfl⟩ : syracuseStep 1602023 = 2403035) B2403035
theorem B98693639 : Blo 1600999 98693639 := bstep (se 1 (by rfl) ⟨74020229, by rfl⟩ : syracuseStep 98693639 = 148040459) B148040459
theorem B1602139 : Blo 1600999 1602139 := bstep (se 1 (by rfl) ⟨1201604, by rfl⟩ : syracuseStep 1602139 = 2403209) B2403209
theorem B49976027 : Blo 1600999 49976027 := bstep (se 1 (by rfl) ⟨37482020, by rfl⟩ : syracuseStep 49976027 = 74964041) B74964041
theorem B23090467 : Blo 1600999 23090467 := bstep (se 1 (by rfl) ⟨17317850, by rfl⟩ : syracuseStep 23090467 = 34635701) B34635701
theorem B61568423 : Blo 1600999 61568423 := bstep (se 1 (by rfl) ⟨46176317, by rfl⟩ : syracuseStep 61568423 = 92352635) B92352635
theorem B4052713 : Blo 1600999 4052713 := bstep (se 2 (by rfl) ⟨1519767, by rfl⟩ : syracuseStep 4052713 = 3039535) B3039535
theorem B35133421 : Blo 1600999 35133421 := bstep (se 3 (by rfl) ⟨6587516, by rfl⟩ : syracuseStep 35133421 = 13175033) B13175033
theorem B13678591 : Blo 1600999 13678591 := bstep (se 1 (by rfl) ⟨10258943, by rfl⟩ : syracuseStep 13678591 = 20517887) B20517887
theorem B4053199 : Blo 1600999 4053199 := bstep (se 1 (by rfl) ⟨3039899, by rfl⟩ : syracuseStep 4053199 = 6079799) B6079799
theorem B18488429 : Blo 1600999 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B4054313 : Blo 1600999 4054313 := bstep (se 2 (by rfl) ⟨1520367, by rfl⟩ : syracuseStep 4054313 = 3040735) B3040735
theorem B5405993 : Blo 1600999 5405993 := bstep (se 2 (by rfl) ⟨2027247, by rfl⟩ : syracuseStep 5405993 = 4054495) B4054495
theorem B15400489 : Blo 1600999 15400489 := bstep (se 2 (by rfl) ⟨5775183, by rfl⟩ : syracuseStep 15400489 = 11550367) B11550367
theorem B6086299 : Blo 1600999 6086299 := bstep (se 1 (by rfl) ⟨4564724, by rfl⟩ : syracuseStep 6086299 = 9129449) B9129449
theorem B106807187 : Blo 1600999 106807187 := bstep (se 1 (by rfl) ⟨80105390, by rfl⟩ : syracuseStep 106807187 = 160210781) B160210781
theorem B33317351 : Blo 1600999 33317351 := bstep (se 1 (by rfl) ⟨24988013, by rfl⟩ : syracuseStep 33317351 = 49976027) B49976027
theorem B7701419 : Blo 1600999 7701419 := bstep (se 1 (by rfl) ⟨5776064, by rfl⟩ : syracuseStep 7701419 = 11552129) B11552129
theorem B5129563 : Blo 1600999 5129563 := bstep (se 1 (by rfl) ⟨3847172, by rfl⟩ : syracuseStep 5129563 = 7694345) B7694345
theorem B30787289 : Blo 1600999 30787289 := bstep (se 2 (by rfl) ⟨11545233, by rfl⟩ : syracuseStep 30787289 = 23090467) B23090467
theorem B46844561 : Blo 1600999 46844561 := bstep (se 2 (by rfl) ⟨17566710, by rfl⟩ : syracuseStep 46844561 = 35133421) B35133421
theorem B18238121 : Blo 1600999 18238121 := bstep (se 2 (by rfl) ⟨6839295, by rfl⟩ : syracuseStep 18238121 = 13678591) B13678591
theorem B2403239 : Blo 1600999 2403239 := bstep (se 1 (by rfl) ⟨1802429, by rfl⟩ : syracuseStep 2403239 = 3604859) B3604859
theorem B2600399 : Blo 1600999 2600399 := bstep (se 1 (by rfl) ⟨1950299, by rfl⟩ : syracuseStep 2600399 = 3900599) B3900599
theorem B41045615 : Blo 1600999 41045615 := bstep (se 1 (by rfl) ⟨30784211, by rfl⟩ : syracuseStep 41045615 = 61568423) B61568423
theorem B2027263 : Blo 1600999 2027263 := bstep (se 1 (by rfl) ⟨1520447, by rfl⟩ : syracuseStep 2027263 = 3040895) B3040895
theorem B20533985 : Blo 1600999 20533985 := bstep (se 2 (by rfl) ⟨7700244, by rfl⟩ : syracuseStep 20533985 = 15400489) B15400489
theorem B12325619 : Blo 1600999 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B8115065 : Blo 1600999 8115065 := bstep (se 2 (by rfl) ⟨3043149, by rfl⟩ : syracuseStep 8115065 = 6086299) B6086299
theorem B5403617 : Blo 1600999 5403617 := bstep (se 2 (by rfl) ⟨2026356, by rfl⟩ : syracuseStep 5403617 = 4052713) B4052713
theorem B4330493 : Blo 1600999 4330493 := bstep (se 3 (by rfl) ⟨811967, by rfl⟩ : syracuseStep 4330493 = 1623935) B1623935
theorem B5404265 : Blo 1600999 5404265 := bstep (se 2 (by rfl) ⟨2026599, by rfl⟩ : syracuseStep 5404265 = 4053199) B4053199
theorem B65795759 : Blo 1600999 65795759 := bstep (se 1 (by rfl) ⟨49346819, by rfl⟩ : syracuseStep 65795759 = 98693639) B98693639
theorem B103978727 : Blo 1600999 103978727 := bstep (se 1 (by rfl) ⟨77984045, by rfl⟩ : syracuseStep 103978727 = 155968091) B155968091
theorem B2702875 : Blo 1600999 2702875 := bstep (se 1 (by rfl) ⟨2027156, by rfl⟩ : syracuseStep 2702875 = 4054313) B4054313
theorem B3603995 : Blo 1600999 3603995 := bstep (se 1 (by rfl) ⟨2702996, by rfl⟩ : syracuseStep 3603995 = 5405993) B5405993
theorem B71204791 : Blo 1600999 71204791 := bstep (se 1 (by rfl) ⟨53403593, by rfl⟩ : syracuseStep 71204791 = 106807187) B106807187
theorem B13689323 : Blo 1600999 13689323 := bstep (se 1 (by rfl) ⟨10266992, by rfl⟩ : syracuseStep 13689323 = 20533985) B20533985
theorem B31229707 : Blo 1600999 31229707 := bstep (se 1 (by rfl) ⟨23422280, by rfl⟩ : syracuseStep 31229707 = 46844561) B46844561
theorem B12158747 : Blo 1600999 12158747 := bstep (se 1 (by rfl) ⟨9119060, by rfl⟩ : syracuseStep 12158747 = 18238121) B18238121
theorem B32868317 : Blo 1600999 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B2402663 : Blo 1600999 2402663 := bstep (se 1 (by rfl) ⟨1801997, by rfl⟩ : syracuseStep 2402663 = 3603995) B3603995
theorem B27363743 : Blo 1600999 27363743 := bstep (se 1 (by rfl) ⟨20522807, by rfl⟩ : syracuseStep 27363743 = 41045615) B41045615
theorem B94939721 : Blo 1600999 94939721 := bstep (se 2 (by rfl) ⟨35602395, by rfl⟩ : syracuseStep 94939721 = 71204791) B71204791
theorem B22211567 : Blo 1600999 22211567 := bstep (se 1 (by rfl) ⟨16658675, by rfl⟩ : syracuseStep 22211567 = 33317351) B33317351
theorem B5410043 : Blo 1600999 5410043 := bstep (se 1 (by rfl) ⟨4057532, by rfl⟩ : syracuseStep 5410043 = 8115065) B8115065
theorem B2886995 : Blo 1600999 2886995 := bstep (se 1 (by rfl) ⟨2165246, by rfl⟩ : syracuseStep 2886995 = 4330493) B4330493
theorem B43863839 : Blo 1600999 43863839 := bstep (se 1 (by rfl) ⟨32897879, by rfl⟩ : syracuseStep 43863839 = 65795759) B65795759
theorem B20524859 : Blo 1600999 20524859 := bstep (se 1 (by rfl) ⟨15393644, by rfl⟩ : syracuseStep 20524859 = 30787289) B30787289
theorem B1602159 : Blo 1600999 1602159 := bstep (se 1 (by rfl) ⟨1201619, by rfl⟩ : syracuseStep 1602159 = 2403239) B2403239
theorem B1733599 : Blo 1600999 1733599 := bstep (se 1 (by rfl) ⟨1300199, by rfl⟩ : syracuseStep 1733599 = 2600399) B2600399
theorem B5134279 : Blo 1600999 5134279 := bstep (se 1 (by rfl) ⟨3850709, by rfl⟩ : syracuseStep 5134279 = 7701419) B7701419
theorem B3602411 : Blo 1600999 3602411 := bstep (se 1 (by rfl) ⟨2701808, by rfl⟩ : syracuseStep 3602411 = 5403617) B5403617
theorem B3602843 : Blo 1600999 3602843 := bstep (se 1 (by rfl) ⟨2702132, by rfl⟩ : syracuseStep 3602843 = 5404265) B5404265
theorem B69319151 : Blo 1600999 69319151 := bstep (se 1 (by rfl) ⟨51989363, by rfl⟩ : syracuseStep 69319151 = 103978727) B103978727
theorem B6839417 : Blo 1600999 6839417 := bstep (se 2 (by rfl) ⟨2564781, by rfl⟩ : syracuseStep 6839417 = 5129563) B5129563
theorem B3603833 : Blo 1600999 3603833 := bstep (se 2 (by rfl) ⟨1351437, by rfl⟩ : syracuseStep 3603833 = 2702875) B2702875
theorem B2703017 : Blo 1600999 2703017 := bstep (se 2 (by rfl) ⟨1013631, by rfl⟩ : syracuseStep 2703017 = 2027263) B2027263
theorem B9126215 : Blo 1600999 9126215 := bstep (se 1 (by rfl) ⟨6844661, by rfl⟩ : syracuseStep 9126215 = 13689323) B13689323
theorem B2311465 : Blo 1600999 2311465 := bstep (se 2 (by rfl) ⟨866799, by rfl⟩ : syracuseStep 2311465 = 1733599) B1733599
theorem B2401607 : Blo 1600999 2401607 := bstep (se 1 (by rfl) ⟨1801205, by rfl⟩ : syracuseStep 2401607 = 3602411) B3602411
theorem B2401895 : Blo 1600999 2401895 := bstep (se 1 (by rfl) ⟨1801421, by rfl⟩ : syracuseStep 2401895 = 3602843) B3602843
theorem B46212767 : Blo 1600999 46212767 := bstep (se 1 (by rfl) ⟨34659575, by rfl⟩ : syracuseStep 46212767 = 69319151) B69319151
theorem B63293147 : Blo 1600999 63293147 := bstep (se 1 (by rfl) ⟨47469860, by rfl⟩ : syracuseStep 63293147 = 94939721) B94939721
theorem B3606695 : Blo 1600999 3606695 := bstep (se 1 (by rfl) ⟨2705021, by rfl⟩ : syracuseStep 3606695 = 5410043) B5410043
theorem B2402555 : Blo 1600999 2402555 := bstep (se 1 (by rfl) ⟨1801916, by rfl⟩ : syracuseStep 2402555 = 3603833) B3603833
theorem B13683239 : Blo 1600999 13683239 := bstep (se 1 (by rfl) ⟨10262429, by rfl⟩ : syracuseStep 13683239 = 20524859) B20524859
theorem B8105831 : Blo 1600999 8105831 := bstep (se 1 (by rfl) ⟨6079373, by rfl⟩ : syracuseStep 8105831 = 12158747) B12158747
theorem B1601775 : Blo 1600999 1601775 := bstep (se 1 (by rfl) ⟨1201331, by rfl⟩ : syracuseStep 1601775 = 2402663) B2402663
theorem B14807711 : Blo 1600999 14807711 := bstep (se 1 (by rfl) ⟨11105783, by rfl⟩ : syracuseStep 14807711 = 22211567) B22211567
theorem B4559611 : Blo 1600999 4559611 := bstep (se 1 (by rfl) ⟨3419708, by rfl⟩ : syracuseStep 4559611 = 6839417) B6839417
theorem B29242559 : Blo 1600999 29242559 := bstep (se 1 (by rfl) ⟨21931919, by rfl⟩ : syracuseStep 29242559 = 43863839) B43863839
theorem B6845705 : Blo 1600999 6845705 := bstep (se 2 (by rfl) ⟨2567139, by rfl⟩ : syracuseStep 6845705 = 5134279) B5134279
theorem B21912211 : Blo 1600999 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B18242495 : Blo 1600999 18242495 := bstep (se 1 (by rfl) ⟨13681871, by rfl⟩ : syracuseStep 18242495 = 27363743) B27363743
theorem B1924663 : Blo 1600999 1924663 := bstep (se 1 (by rfl) ⟨1443497, by rfl⟩ : syracuseStep 1924663 = 2886995) B2886995
theorem B41639609 : Blo 1600999 41639609 := bstep (se 2 (by rfl) ⟨15614853, by rfl⟩ : syracuseStep 41639609 = 31229707) B31229707
theorem B1802011 : Blo 1600999 1802011 := bstep (se 1 (by rfl) ⟨1351508, by rfl⟩ : syracuseStep 1802011 = 2703017) B2703017
theorem B9871807 : Blo 1600999 9871807 := bstep (se 1 (by rfl) ⟨7403855, by rfl⟩ : syracuseStep 9871807 = 14807711) B14807711
theorem B4563803 : Blo 1600999 4563803 := bstep (se 1 (by rfl) ⟨3422852, by rfl⟩ : syracuseStep 4563803 = 6845705) B6845705
theorem B6079481 : Blo 1600999 6079481 := bstep (se 2 (by rfl) ⟨2279805, by rfl⟩ : syracuseStep 6079481 = 4559611) B4559611
theorem B3081953 : Blo 1600999 3081953 := bstep (se 2 (by rfl) ⟨1155732, by rfl⟩ : syracuseStep 3081953 = 2311465) B2311465
theorem B2566217 : Blo 1600999 2566217 := bstep (se 2 (by rfl) ⟨962331, by rfl⟩ : syracuseStep 2566217 = 1924663) B1924663
theorem B2402681 : Blo 1600999 2402681 := bstep (se 2 (by rfl) ⟨901005, by rfl⟩ : syracuseStep 2402681 = 1802011) B1802011
theorem B1601071 : Blo 1600999 1601071 := bstep (se 1 (by rfl) ⟨1200803, by rfl⟩ : syracuseStep 1601071 = 2401607) B2401607
theorem B1601263 : Blo 1600999 1601263 := bstep (se 1 (by rfl) ⟨1200947, by rfl⟩ : syracuseStep 1601263 = 2401895) B2401895
theorem B2404463 : Blo 1600999 2404463 := bstep (se 1 (by rfl) ⟨1803347, by rfl⟩ : syracuseStep 2404463 = 3606695) B3606695
theorem B1601703 : Blo 1600999 1601703 := bstep (se 1 (by rfl) ⟨1201277, by rfl⟩ : syracuseStep 1601703 = 2402555) B2402555
theorem B9122159 : Blo 1600999 9122159 := bstep (se 1 (by rfl) ⟨6841619, by rfl⟩ : syracuseStep 9122159 = 13683239) B13683239
theorem B111038957 : Blo 1600999 111038957 := bstep (se 3 (by rfl) ⟨20819804, by rfl⟩ : syracuseStep 111038957 = 41639609) B41639609
theorem B12161663 : Blo 1600999 12161663 := bstep (se 1 (by rfl) ⟨9121247, by rfl⟩ : syracuseStep 12161663 = 18242495) B18242495
theorem B5403887 : Blo 1600999 5403887 := bstep (se 1 (by rfl) ⟨4052915, by rfl⟩ : syracuseStep 5403887 = 8105831) B8105831
theorem B6084143 : Blo 1600999 6084143 := bstep (se 1 (by rfl) ⟨4563107, by rfl⟩ : syracuseStep 6084143 = 9126215) B9126215
theorem B116865125 : Blo 1600999 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B19495039 : Blo 1600999 19495039 := bstep (se 1 (by rfl) ⟨14621279, by rfl⟩ : syracuseStep 19495039 = 29242559) B29242559
theorem B30808511 : Blo 1600999 30808511 := bstep (se 1 (by rfl) ⟨23106383, by rfl⟩ : syracuseStep 30808511 = 46212767) B46212767
theorem B42195431 : Blo 1600999 42195431 := bstep (se 1 (by rfl) ⟨31646573, by rfl⟩ : syracuseStep 42195431 = 63293147) B63293147
theorem B25993385 : Blo 1600999 25993385 := bstep (se 2 (by rfl) ⟨9747519, by rfl⟩ : syracuseStep 25993385 = 19495039) B19495039
theorem B4056095 : Blo 1600999 4056095 := bstep (se 1 (by rfl) ⟨3042071, by rfl⟩ : syracuseStep 4056095 = 6084143) B6084143
theorem B20539007 : Blo 1600999 20539007 := bstep (se 1 (by rfl) ⟨15404255, by rfl⟩ : syracuseStep 20539007 = 30808511) B30808511
theorem B8218541 : Blo 1600999 8218541 := bstep (se 3 (by rfl) ⟨1540976, by rfl⟩ : syracuseStep 8218541 = 3081953) B3081953
theorem B6081439 : Blo 1600999 6081439 := bstep (se 1 (by rfl) ⟨4561079, by rfl⟩ : syracuseStep 6081439 = 9122159) B9122159
theorem B74025971 : Blo 1600999 74025971 := bstep (se 1 (by rfl) ⟨55519478, by rfl⟩ : syracuseStep 74025971 = 111038957) B111038957
theorem B3042535 : Blo 1600999 3042535 := bstep (se 1 (by rfl) ⟨2281901, by rfl⟩ : syracuseStep 3042535 = 4563803) B4563803
theorem B112521149 : Blo 1600999 112521149 := bstep (se 3 (by rfl) ⟨21097715, by rfl⟩ : syracuseStep 112521149 = 42195431) B42195431
theorem B77910083 : Blo 1600999 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B1601787 : Blo 1600999 1601787 := bstep (se 1 (by rfl) ⟨1201340, by rfl⟩ : syracuseStep 1601787 = 2402681) B2402681
theorem B1602975 : Blo 1600999 1602975 := bstep (se 1 (by rfl) ⟨1202231, by rfl⟩ : syracuseStep 1602975 = 2404463) B2404463
theorem B8107775 : Blo 1600999 8107775 := bstep (se 1 (by rfl) ⟨6080831, by rfl⟩ : syracuseStep 8107775 = 12161663) B12161663
theorem B13162409 : Blo 1600999 13162409 := bstep (se 2 (by rfl) ⟨4935903, by rfl⟩ : syracuseStep 13162409 = 9871807) B9871807
theorem B4052987 : Blo 1600999 4052987 := bstep (se 1 (by rfl) ⟨3039740, by rfl⟩ : syracuseStep 4052987 = 6079481) B6079481
theorem B3602591 : Blo 1600999 3602591 := bstep (se 1 (by rfl) ⟨2701943, by rfl⟩ : syracuseStep 3602591 = 5403887) B5403887
theorem B1710811 : Blo 1600999 1710811 := bstep (se 1 (by rfl) ⟨1283108, by rfl⟩ : syracuseStep 1710811 = 2566217) B2566217
theorem B2704063 : Blo 1600999 2704063 := bstep (se 1 (by rfl) ⟨2028047, by rfl⟩ : syracuseStep 2704063 = 4056095) B4056095
theorem B8774939 : Blo 1600999 8774939 := bstep (se 1 (by rfl) ⟨6581204, by rfl⟩ : syracuseStep 8774939 = 13162409) B13162409
theorem B2401727 : Blo 1600999 2401727 := bstep (se 1 (by rfl) ⟨1801295, by rfl⟩ : syracuseStep 2401727 = 3602591) B3602591
theorem B4056713 : Blo 1600999 4056713 := bstep (se 2 (by rfl) ⟨1521267, by rfl⟩ : syracuseStep 4056713 = 3042535) B3042535
theorem B49350647 : Blo 1600999 49350647 := bstep (se 1 (by rfl) ⟨37012985, by rfl⟩ : syracuseStep 49350647 = 74025971) B74025971
theorem B21916109 : Blo 1600999 21916109 := bstep (se 3 (by rfl) ⟨4109270, by rfl⟩ : syracuseStep 21916109 = 8218541) B8218541
theorem B51940055 : Blo 1600999 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B17328923 : Blo 1600999 17328923 := bstep (se 1 (by rfl) ⟨12996692, by rfl⟩ : syracuseStep 17328923 = 25993385) B25993385
theorem B13692671 : Blo 1600999 13692671 := bstep (se 1 (by rfl) ⟨10269503, by rfl⟩ : syracuseStep 13692671 = 20539007) B20539007
theorem B9124325 : Blo 1600999 9124325 := bstep (se 4 (by rfl) ⟨855405, by rfl⟩ : syracuseStep 9124325 = 1710811) B1710811
theorem B5405183 : Blo 1600999 5405183 := bstep (se 1 (by rfl) ⟨4053887, by rfl⟩ : syracuseStep 5405183 = 8107775) B8107775
theorem B8108585 : Blo 1600999 8108585 := bstep (se 2 (by rfl) ⟨3040719, by rfl⟩ : syracuseStep 8108585 = 6081439) B6081439
theorem B2701991 : Blo 1600999 2701991 := bstep (se 1 (by rfl) ⟨2026493, by rfl⟩ : syracuseStep 2701991 = 4052987) B4052987
theorem B75014099 : Blo 1600999 75014099 := bstep (se 1 (by rfl) ⟨56260574, by rfl⟩ : syracuseStep 75014099 = 112521149) B112521149
theorem B3605417 : Blo 1600999 3605417 := bstep (se 2 (by rfl) ⟨1352031, by rfl⟩ : syracuseStep 3605417 = 2704063) B2704063
theorem B2704475 : Blo 1600999 2704475 := bstep (se 1 (by rfl) ⟨2028356, by rfl⟩ : syracuseStep 2704475 = 4056713) B4056713
theorem B32900431 : Blo 1600999 32900431 := bstep (se 1 (by rfl) ⟨24675323, by rfl⟩ : syracuseStep 32900431 = 49350647) B49350647
theorem B11552615 : Blo 1600999 11552615 := bstep (se 1 (by rfl) ⟨8664461, by rfl⟩ : syracuseStep 11552615 = 17328923) B17328923
theorem B9128447 : Blo 1600999 9128447 := bstep (se 1 (by rfl) ⟨6846335, by rfl⟩ : syracuseStep 9128447 = 13692671) B13692671
theorem B23399837 : Blo 1600999 23399837 := bstep (se 3 (by rfl) ⟨4387469, by rfl⟩ : syracuseStep 23399837 = 8774939) B8774939
theorem B1601151 : Blo 1600999 1601151 := bstep (se 1 (by rfl) ⟨1200863, by rfl⟩ : syracuseStep 1601151 = 2401727) B2401727
theorem B14610739 : Blo 1600999 14610739 := bstep (se 1 (by rfl) ⟨10958054, by rfl⟩ : syracuseStep 14610739 = 21916109) B21916109
theorem B6082883 : Blo 1600999 6082883 := bstep (se 1 (by rfl) ⟨4562162, by rfl⟩ : syracuseStep 6082883 = 9124325) B9124325
theorem B50009399 : Blo 1600999 50009399 := bstep (se 1 (by rfl) ⟨37507049, by rfl⟩ : syracuseStep 50009399 = 75014099) B75014099
theorem B3603455 : Blo 1600999 3603455 := bstep (se 1 (by rfl) ⟨2702591, by rfl⟩ : syracuseStep 3603455 = 5405183) B5405183
theorem B5405723 : Blo 1600999 5405723 := bstep (se 1 (by rfl) ⟨4054292, by rfl⟩ : syracuseStep 5405723 = 8108585) B8108585
theorem B1801327 : Blo 1600999 1801327 := bstep (se 1 (by rfl) ⟨1350995, by rfl⟩ : syracuseStep 1801327 = 2701991) B2701991
theorem B34626703 : Blo 1600999 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B4055255 : Blo 1600999 4055255 := bstep (se 1 (by rfl) ⟨3041441, by rfl⟩ : syracuseStep 4055255 = 6082883) B6082883
theorem B19480985 : Blo 1600999 19480985 := bstep (se 2 (by rfl) ⟨7305369, by rfl⟩ : syracuseStep 19480985 = 14610739) B14610739
theorem B1802983 : Blo 1600999 1802983 := bstep (se 1 (by rfl) ⟨1352237, by rfl⟩ : syracuseStep 1802983 = 2704475) B2704475
theorem B7701743 : Blo 1600999 7701743 := bstep (se 1 (by rfl) ⟨5776307, by rfl⟩ : syracuseStep 7701743 = 11552615) B11552615
theorem B2401769 : Blo 1600999 2401769 := bstep (se 2 (by rfl) ⟨900663, by rfl⟩ : syracuseStep 2401769 = 1801327) B1801327
theorem B2402303 : Blo 1600999 2402303 := bstep (se 1 (by rfl) ⟨1801727, by rfl⟩ : syracuseStep 2402303 = 3603455) B3603455
theorem B15599891 : Blo 1600999 15599891 := bstep (se 1 (by rfl) ⟨11699918, by rfl⟩ : syracuseStep 15599891 = 23399837) B23399837
theorem B2403611 : Blo 1600999 2403611 := bstep (se 1 (by rfl) ⟨1802708, by rfl⟩ : syracuseStep 2403611 = 3605417) B3605417
theorem B33339599 : Blo 1600999 33339599 := bstep (se 1 (by rfl) ⟨25004699, by rfl⟩ : syracuseStep 33339599 = 50009399) B50009399
theorem B46168937 : Blo 1600999 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B6085631 : Blo 1600999 6085631 := bstep (se 1 (by rfl) ⟨4564223, by rfl⟩ : syracuseStep 6085631 = 9128447) B9128447
theorem B43867241 : Blo 1600999 43867241 := bstep (se 2 (by rfl) ⟨16450215, by rfl⟩ : syracuseStep 43867241 = 32900431) B32900431
theorem B3603815 : Blo 1600999 3603815 := bstep (se 1 (by rfl) ⟨2702861, by rfl⟩ : syracuseStep 3603815 = 5405723) B5405723
theorem B2703503 : Blo 1600999 2703503 := bstep (se 1 (by rfl) ⟨2027627, by rfl⟩ : syracuseStep 2703503 = 4055255) B4055255
theorem B20537981 : Blo 1600999 20537981 := bstep (se 3 (by rfl) ⟨3850871, by rfl⟩ : syracuseStep 20537981 = 7701743) B7701743
theorem B22226399 : Blo 1600999 22226399 := bstep (se 1 (by rfl) ⟨16669799, by rfl⟩ : syracuseStep 22226399 = 33339599) B33339599
theorem B30779291 : Blo 1600999 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B4057087 : Blo 1600999 4057087 := bstep (se 1 (by rfl) ⟨3042815, by rfl⟩ : syracuseStep 4057087 = 6085631) B6085631
theorem B2402543 : Blo 1600999 2402543 := bstep (se 1 (by rfl) ⟨1801907, by rfl⟩ : syracuseStep 2402543 = 3603815) B3603815
theorem B12987323 : Blo 1600999 12987323 := bstep (se 1 (by rfl) ⟨9740492, by rfl⟩ : syracuseStep 12987323 = 19480985) B19480985
theorem B2403977 : Blo 1600999 2403977 := bstep (se 2 (by rfl) ⟨901491, by rfl⟩ : syracuseStep 2403977 = 1802983) B1802983
theorem B1601179 : Blo 1600999 1601179 := bstep (se 1 (by rfl) ⟨1200884, by rfl⟩ : syracuseStep 1601179 = 2401769) B2401769
theorem B1601535 : Blo 1600999 1601535 := bstep (se 1 (by rfl) ⟨1201151, by rfl⟩ : syracuseStep 1601535 = 2402303) B2402303
theorem B10399927 : Blo 1600999 10399927 := bstep (se 1 (by rfl) ⟨7799945, by rfl⟩ : syracuseStep 10399927 = 15599891) B15599891
theorem B1602407 : Blo 1600999 1602407 := bstep (se 1 (by rfl) ⟨1201805, by rfl⟩ : syracuseStep 1602407 = 2403611) B2403611
theorem B29244827 : Blo 1600999 29244827 := bstep (se 1 (by rfl) ⟨21933620, by rfl⟩ : syracuseStep 29244827 = 43867241) B43867241
theorem B1802335 : Blo 1600999 1802335 := bstep (se 1 (by rfl) ⟨1351751, by rfl⟩ : syracuseStep 1802335 = 2703503) B2703503
theorem B5409449 : Blo 1600999 5409449 := bstep (se 2 (by rfl) ⟨2028543, by rfl⟩ : syracuseStep 5409449 = 4057087) B4057087
theorem B13691987 : Blo 1600999 13691987 := bstep (se 1 (by rfl) ⟨10268990, by rfl⟩ : syracuseStep 13691987 = 20537981) B20537981
theorem B1601695 : Blo 1600999 1601695 := bstep (se 1 (by rfl) ⟨1201271, by rfl⟩ : syracuseStep 1601695 = 2402543) B2402543
theorem B1602651 : Blo 1600999 1602651 := bstep (se 1 (by rfl) ⟨1201988, by rfl⟩ : syracuseStep 1602651 = 2403977) B2403977
theorem B13866569 : Blo 1600999 13866569 := bstep (se 2 (by rfl) ⟨5199963, by rfl⟩ : syracuseStep 13866569 = 10399927) B10399927
theorem B14817599 : Blo 1600999 14817599 := bstep (se 1 (by rfl) ⟨11113199, by rfl⟩ : syracuseStep 14817599 = 22226399) B22226399
theorem B20519527 : Blo 1600999 20519527 := bstep (se 1 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 20519527 = 30779291) B30779291
theorem B8658215 : Blo 1600999 8658215 := bstep (se 1 (by rfl) ⟨6493661, by rfl⟩ : syracuseStep 8658215 = 12987323) B12987323
theorem B19496551 : Blo 1600999 19496551 := bstep (se 1 (by rfl) ⟨14622413, by rfl⟩ : syracuseStep 19496551 = 29244827) B29244827
theorem B3606299 : Blo 1600999 3606299 := bstep (se 1 (by rfl) ⟨2704724, by rfl⟩ : syracuseStep 3606299 = 5409449) B5409449
theorem B9127991 : Blo 1600999 9127991 := bstep (se 1 (by rfl) ⟨6845993, by rfl⟩ : syracuseStep 9127991 = 13691987) B13691987
theorem B25995401 : Blo 1600999 25995401 := bstep (se 2 (by rfl) ⟨9748275, by rfl⟩ : syracuseStep 25995401 = 19496551) B19496551
theorem B2403113 : Blo 1600999 2403113 := bstep (se 2 (by rfl) ⟨901167, by rfl⟩ : syracuseStep 2403113 = 1802335) B1802335
theorem B9244379 : Blo 1600999 9244379 := bstep (se 1 (by rfl) ⟨6933284, by rfl⟩ : syracuseStep 9244379 = 13866569) B13866569
theorem B5772143 : Blo 1600999 5772143 := bstep (se 1 (by rfl) ⟨4329107, by rfl⟩ : syracuseStep 5772143 = 8658215) B8658215
theorem B27359369 : Blo 1600999 27359369 := bstep (se 2 (by rfl) ⟨10259763, by rfl⟩ : syracuseStep 27359369 = 20519527) B20519527
theorem B9878399 : Blo 1600999 9878399 := bstep (se 1 (by rfl) ⟨7408799, by rfl⟩ : syracuseStep 9878399 = 14817599) B14817599
theorem B24651677 : Blo 1600999 24651677 := bstep (se 3 (by rfl) ⟨4622189, by rfl⟩ : syracuseStep 24651677 = 9244379) B9244379
theorem B2404199 : Blo 1600999 2404199 := bstep (se 1 (by rfl) ⟨1803149, by rfl⟩ : syracuseStep 2404199 = 3606299) B3606299
theorem B18239579 : Blo 1600999 18239579 := bstep (se 1 (by rfl) ⟨13679684, by rfl⟩ : syracuseStep 18239579 = 27359369) B27359369
theorem B17330267 : Blo 1600999 17330267 := bstep (se 1 (by rfl) ⟨12997700, by rfl⟩ : syracuseStep 17330267 = 25995401) B25995401
theorem B1602075 : Blo 1600999 1602075 := bstep (se 1 (by rfl) ⟨1201556, by rfl⟩ : syracuseStep 1602075 = 2403113) B2403113
theorem B3848095 : Blo 1600999 3848095 := bstep (se 1 (by rfl) ⟨2886071, by rfl⟩ : syracuseStep 3848095 = 5772143) B5772143
theorem B6085327 : Blo 1600999 6085327 := bstep (se 1 (by rfl) ⟨4563995, by rfl⟩ : syracuseStep 6085327 = 9127991) B9127991
theorem B6585599 : Blo 1600999 6585599 := bstep (se 1 (by rfl) ⟨4939199, by rfl⟩ : syracuseStep 6585599 = 9878399) B9878399
theorem B16434451 : Blo 1600999 16434451 := bstep (se 1 (by rfl) ⟨12325838, by rfl⟩ : syracuseStep 16434451 = 24651677) B24651677
theorem B5130793 : Blo 1600999 5130793 := bstep (se 2 (by rfl) ⟨1924047, by rfl⟩ : syracuseStep 5130793 = 3848095) B3848095
theorem B12159719 : Blo 1600999 12159719 := bstep (se 1 (by rfl) ⟨9119789, by rfl⟩ : syracuseStep 12159719 = 18239579) B18239579
theorem B11553511 : Blo 1600999 11553511 := bstep (se 1 (by rfl) ⟨8665133, by rfl⟩ : syracuseStep 11553511 = 17330267) B17330267
theorem B8113769 : Blo 1600999 8113769 := bstep (se 2 (by rfl) ⟨3042663, by rfl⟩ : syracuseStep 8113769 = 6085327) B6085327
theorem B1602799 : Blo 1600999 1602799 := bstep (se 1 (by rfl) ⟨1202099, by rfl⟩ : syracuseStep 1602799 = 2404199) B2404199
theorem B4390399 : Blo 1600999 4390399 := bstep (se 1 (by rfl) ⟨3292799, by rfl⟩ : syracuseStep 4390399 = 6585599) B6585599
theorem B6841057 : Blo 1600999 6841057 := bstep (se 2 (by rfl) ⟨2565396, by rfl⟩ : syracuseStep 6841057 = 5130793) B5130793
theorem B5409179 : Blo 1600999 5409179 := bstep (se 1 (by rfl) ⟨4056884, by rfl⟩ : syracuseStep 5409179 = 8113769) B8113769
theorem B15404681 : Blo 1600999 15404681 := bstep (se 2 (by rfl) ⟨5776755, by rfl⟩ : syracuseStep 15404681 = 11553511) B11553511
theorem B8106479 : Blo 1600999 8106479 := bstep (se 1 (by rfl) ⟨6079859, by rfl⟩ : syracuseStep 8106479 = 12159719) B12159719
theorem B5853865 : Blo 1600999 5853865 := bstep (se 2 (by rfl) ⟨2195199, by rfl⟩ : syracuseStep 5853865 = 4390399) B4390399
theorem B21912601 : Blo 1600999 21912601 := bstep (se 2 (by rfl) ⟨8217225, by rfl⟩ : syracuseStep 21912601 = 16434451) B16434451
theorem B3606119 : Blo 1600999 3606119 := bstep (se 1 (by rfl) ⟨2704589, by rfl⟩ : syracuseStep 3606119 = 5409179) B5409179
theorem B9121409 : Blo 1600999 9121409 := bstep (se 2 (by rfl) ⟨3420528, by rfl⟩ : syracuseStep 9121409 = 6841057) B6841057
theorem B29216801 : Blo 1600999 29216801 := bstep (se 2 (by rfl) ⟨10956300, by rfl⟩ : syracuseStep 29216801 = 21912601) B21912601
theorem B10269787 : Blo 1600999 10269787 := bstep (se 1 (by rfl) ⟨7702340, by rfl⟩ : syracuseStep 10269787 = 15404681) B15404681
theorem B5404319 : Blo 1600999 5404319 := bstep (se 1 (by rfl) ⟨4053239, by rfl⟩ : syracuseStep 5404319 = 8106479) B8106479
theorem B7805153 : Blo 1600999 7805153 := bstep (se 2 (by rfl) ⟨2926932, by rfl⟩ : syracuseStep 7805153 = 5853865) B5853865
theorem B5203435 : Blo 1600999 5203435 := bstep (se 1 (by rfl) ⟨3902576, by rfl⟩ : syracuseStep 5203435 = 7805153) B7805153
theorem B6080939 : Blo 1600999 6080939 := bstep (se 1 (by rfl) ⟨4560704, by rfl⟩ : syracuseStep 6080939 = 9121409) B9121409
theorem B2404079 : Blo 1600999 2404079 := bstep (se 1 (by rfl) ⟨1803059, by rfl⟩ : syracuseStep 2404079 = 3606119) B3606119
theorem B13693049 : Blo 1600999 13693049 := bstep (se 2 (by rfl) ⟨5134893, by rfl⟩ : syracuseStep 13693049 = 10269787) B10269787
theorem B19477867 : Blo 1600999 19477867 := bstep (se 1 (by rfl) ⟨14608400, by rfl⟩ : syracuseStep 19477867 = 29216801) B29216801
theorem B3602879 : Blo 1600999 3602879 := bstep (se 1 (by rfl) ⟨2702159, by rfl⟩ : syracuseStep 3602879 = 5404319) B5404319
theorem B2401919 : Blo 1600999 2401919 := bstep (se 1 (by rfl) ⟨1801439, by rfl⟩ : syracuseStep 2401919 = 3602879) B3602879
theorem B25970489 : Blo 1600999 25970489 := bstep (se 2 (by rfl) ⟨9738933, by rfl⟩ : syracuseStep 25970489 = 19477867) B19477867
theorem B9128699 : Blo 1600999 9128699 := bstep (se 1 (by rfl) ⟨6846524, by rfl⟩ : syracuseStep 9128699 = 13693049) B13693049
theorem B1602719 : Blo 1600999 1602719 := bstep (se 1 (by rfl) ⟨1202039, by rfl⟩ : syracuseStep 1602719 = 2404079) B2404079
theorem B4053959 : Blo 1600999 4053959 := bstep (se 1 (by rfl) ⟨3040469, by rfl⟩ : syracuseStep 4053959 = 6080939) B6080939
theorem B6937913 : Blo 1600999 6937913 := bstep (se 2 (by rfl) ⟨2601717, by rfl⟩ : syracuseStep 6937913 = 5203435) B5203435
theorem B1601279 : Blo 1600999 1601279 := bstep (se 1 (by rfl) ⟨1200959, by rfl⟩ : syracuseStep 1601279 = 2401919) B2401919
theorem B17313659 : Blo 1600999 17313659 := bstep (se 1 (by rfl) ⟨12985244, by rfl⟩ : syracuseStep 17313659 = 25970489) B25970489
theorem B4625275 : Blo 1600999 4625275 := bstep (se 1 (by rfl) ⟨3468956, by rfl⟩ : syracuseStep 4625275 = 6937913) B6937913
theorem B6085799 : Blo 1600999 6085799 := bstep (se 1 (by rfl) ⟨4564349, by rfl⟩ : syracuseStep 6085799 = 9128699) B9128699
theorem B2702639 : Blo 1600999 2702639 := bstep (se 1 (by rfl) ⟨2026979, by rfl⟩ : syracuseStep 2702639 = 4053959) B4053959
theorem B4057199 : Blo 1600999 4057199 := bstep (se 1 (by rfl) ⟨3042899, by rfl⟩ : syracuseStep 4057199 = 6085799) B6085799
theorem B6167033 : Blo 1600999 6167033 := bstep (se 2 (by rfl) ⟨2312637, by rfl⟩ : syracuseStep 6167033 = 4625275) B4625275
theorem B1801759 : Blo 1600999 1801759 := bstep (se 1 (by rfl) ⟨1351319, by rfl⟩ : syracuseStep 1801759 = 2702639) B2702639
theorem B11542439 : Blo 1600999 11542439 := bstep (se 1 (by rfl) ⟨8656829, by rfl⟩ : syracuseStep 11542439 = 17313659) B17313659
theorem B2704799 : Blo 1600999 2704799 := bstep (se 1 (by rfl) ⟨2028599, by rfl⟩ : syracuseStep 2704799 = 4057199) B4057199
theorem B2402345 : Blo 1600999 2402345 := bstep (se 2 (by rfl) ⟨900879, by rfl⟩ : syracuseStep 2402345 = 1801759) B1801759
theorem B30779837 : Blo 1600999 30779837 := bstep (se 3 (by rfl) ⟨5771219, by rfl⟩ : syracuseStep 30779837 = 11542439) B11542439
theorem B4111355 : Blo 1600999 4111355 := bstep (se 1 (by rfl) ⟨3083516, by rfl⟩ : syracuseStep 4111355 = 6167033) B6167033
theorem B1803199 : Blo 1600999 1803199 := bstep (se 1 (by rfl) ⟨1352399, by rfl⟩ : syracuseStep 1803199 = 2704799) B2704799
theorem B10963613 : Blo 1600999 10963613 := bstep (se 3 (by rfl) ⟨2055677, by rfl⟩ : syracuseStep 10963613 = 4111355) B4111355
theorem B1601563 : Blo 1600999 1601563 := bstep (se 1 (by rfl) ⟨1201172, by rfl⟩ : syracuseStep 1601563 = 2402345) B2402345
theorem B20519891 : Blo 1600999 20519891 := bstep (se 1 (by rfl) ⟨15389918, by rfl⟩ : syracuseStep 20519891 = 30779837) B30779837
theorem B7309075 : Blo 1600999 7309075 := bstep (se 1 (by rfl) ⟨5481806, by rfl⟩ : syracuseStep 7309075 = 10963613) B10963613
theorem B2404265 : Blo 1600999 2404265 := bstep (se 2 (by rfl) ⟨901599, by rfl⟩ : syracuseStep 2404265 = 1803199) B1803199
theorem B13679927 : Blo 1600999 13679927 := bstep (se 1 (by rfl) ⟨10259945, by rfl⟩ : syracuseStep 13679927 = 20519891) B20519891
theorem B9119951 : Blo 1600999 9119951 := bstep (se 1 (by rfl) ⟨6839963, by rfl⟩ : syracuseStep 9119951 = 13679927) B13679927
theorem B9745433 : Blo 1600999 9745433 := bstep (se 2 (by rfl) ⟨3654537, by rfl⟩ : syracuseStep 9745433 = 7309075) B7309075
theorem B1602843 : Blo 1600999 1602843 := bstep (se 1 (by rfl) ⟨1202132, by rfl⟩ : syracuseStep 1602843 = 2404265) B2404265
theorem B6496955 : Blo 1600999 6496955 := bstep (se 1 (by rfl) ⟨4872716, by rfl⟩ : syracuseStep 6496955 = 9745433) B9745433
theorem B6079967 : Blo 1600999 6079967 := bstep (se 1 (by rfl) ⟨4559975, by rfl⟩ : syracuseStep 6079967 = 9119951) B9119951
theorem B4331303 : Blo 1600999 4331303 := bstep (se 1 (by rfl) ⟨3248477, by rfl⟩ : syracuseStep 4331303 = 6496955) B6496955
theorem B4053311 : Blo 1600999 4053311 := bstep (se 1 (by rfl) ⟨3039983, by rfl⟩ : syracuseStep 4053311 = 6079967) B6079967
theorem B2887535 : Blo 1600999 2887535 := bstep (se 1 (by rfl) ⟨2165651, by rfl⟩ : syracuseStep 2887535 = 4331303) B4331303
theorem B2702207 : Blo 1600999 2702207 := bstep (se 1 (by rfl) ⟨2026655, by rfl⟩ : syracuseStep 2702207 = 4053311) B4053311
theorem B1801471 : Blo 1600999 1801471 := bstep (se 1 (by rfl) ⟨1351103, by rfl⟩ : syracuseStep 1801471 = 2702207) B2702207
theorem B7700093 : Blo 1600999 7700093 := bstep (se 3 (by rfl) ⟨1443767, by rfl⟩ : syracuseStep 7700093 = 2887535) B2887535
theorem B2401961 : Blo 1600999 2401961 := bstep (se 2 (by rfl) ⟨900735, by rfl⟩ : syracuseStep 2401961 = 1801471) B1801471
theorem B5133395 : Blo 1600999 5133395 := bstep (se 1 (by rfl) ⟨3850046, by rfl⟩ : syracuseStep 5133395 = 7700093) B7700093
theorem B1601307 : Blo 1600999 1601307 := bstep (se 1 (by rfl) ⟨1200980, by rfl⟩ : syracuseStep 1601307 = 2401961) B2401961
theorem B3422263 : Blo 1600999 3422263 := bstep (se 1 (by rfl) ⟨2566697, by rfl⟩ : syracuseStep 3422263 = 5133395) B5133395
theorem B4563017 : Blo 1600999 4563017 := bstep (se 2 (by rfl) ⟨1711131, by rfl⟩ : syracuseStep 4563017 = 3422263) B3422263
theorem B3042011 : Blo 1600999 3042011 := bstep (se 1 (by rfl) ⟨2281508, by rfl⟩ : syracuseStep 3042011 = 4563017) B4563017
theorem B2028007 : Blo 1600999 2028007 := bstep (se 1 (by rfl) ⟨1521005, by rfl⟩ : syracuseStep 2028007 = 3042011) B3042011
theorem B2704009 : Blo 1600999 2704009 := bstep (se 2 (by rfl) ⟨1014003, by rfl⟩ : syracuseStep 2704009 = 2028007) B2028007
theorem B3605345 : Blo 1600999 3605345 := bstep (se 2 (by rfl) ⟨1352004, by rfl⟩ : syracuseStep 3605345 = 2704009) B2704009
theorem B2403563 : Blo 1600999 2403563 := bstep (se 1 (by rfl) ⟨1802672, by rfl⟩ : syracuseStep 2403563 = 3605345) B3605345
theorem B1602375 : Blo 1600999 1602375 := bstep (se 1 (by rfl) ⟨1201781, by rfl⟩ : syracuseStep 1602375 = 2403563) B2403563

theorem C0 (j : ℕ) (h1 : 400249 ≤ j) (h2 : j ≤ 400749) : Blo 1600999 (4 * j + 3) := by
  interval_cases j
  · exact B1600999
  · exact B1601003
  · exact B1601007
  · exact B1601011
  · exact B1601015
  · exact B1601019
  · exact B1601023
  · exact B1601027
  · exact B1601031
  · exact B1601035
  · exact B1601039
  · exact B1601043
  · exact B1601047
  · exact B1601051
  · exact B1601055
  · exact B1601059
  · exact B1601063
  · exact B1601067
  · exact B1601071
  · exact B1601075
  · exact B1601079
  · exact B1601083
  · exact B1601087
  · exact B1601091
  · exact B1601095
  · exact B1601099
  · exact B1601103
  · exact B1601107
  · exact B1601111
  · exact B1601115
  · exact B1601119
  · exact B1601123
  · exact B1601127
  · exact B1601131
  · exact B1601135
  · exact B1601139
  · exact B1601143
  · exact B1601147
  · exact B1601151
  · exact B1601155
  · exact B1601159
  · exact B1601163
  · exact B1601167
  · exact B1601171
  · exact B1601175
  · exact B1601179
  · exact B1601183
  · exact B1601187
  · exact B1601191
  · exact B1601195
  · exact B1601199
  · exact B1601203
  · exact B1601207
  · exact B1601211
  · exact B1601215
  · exact B1601219
  · exact B1601223
  · exact B1601227
  · exact B1601231
  · exact B1601235
  · exact B1601239
  · exact B1601243
  · exact B1601247
  · exact B1601251
  · exact B1601255
  · exact B1601259
  · exact B1601263
  · exact B1601267
  · exact B1601271
  · exact B1601275
  · exact B1601279
  · exact B1601283
  · exact B1601287
  · exact B1601291
  · exact B1601295
  · exact B1601299
  · exact B1601303
  · exact B1601307
  · exact B1601311
  · exact B1601315
  · exact B1601319
  · exact B1601323
  · exact B1601327
  · exact B1601331
  · exact B1601335
  · exact B1601339
  · exact B1601343
  · exact B1601347
  · exact B1601351
  · exact B1601355
  · exact B1601359
  · exact B1601363
  · exact B1601367
  · exact B1601371
  · exact B1601375
  · exact B1601379
  · exact B1601383
  · exact B1601387
  · exact B1601391
  · exact B1601395
  · exact B1601399
  · exact B1601403
  · exact B1601407
  · exact B1601411
  · exact B1601415
  · exact B1601419
  · exact B1601423
  · exact B1601427
  · exact B1601431
  · exact B1601435
  · exact B1601439
  · exact B1601443
  · exact B1601447
  · exact B1601451
  · exact B1601455
  · exact B1601459
  · exact B1601463
  · exact B1601467
  · exact B1601471
  · exact B1601475
  · exact B1601479
  · exact B1601483
  · exact B1601487
  · exact B1601491
  · exact B1601495
  · exact B1601499
  · exact B1601503
  · exact B1601507
  · exact B1601511
  · exact B1601515
  · exact B1601519
  · exact B1601523
  · exact B1601527
  · exact B1601531
  · exact B1601535
  · exact B1601539
  · exact B1601543
  · exact B1601547
  · exact B1601551
  · exact B1601555
  · exact B1601559
  · exact B1601563
  · exact B1601567
  · exact B1601571
  · exact B1601575
  · exact B1601579
  · exact B1601583
  · exact B1601587
  · exact B1601591
  · exact B1601595
  · exact B1601599
  · exact B1601603
  · exact B1601607
  · exact B1601611
  · exact B1601615
  · exact B1601619
  · exact B1601623
  · exact B1601627
  · exact B1601631
  · exact B1601635
  · exact B1601639
  · exact B1601643
  · exact B1601647
  · exact B1601651
  · exact B1601655
  · exact B1601659
  · exact B1601663
  · exact B1601667
  · exact B1601671
  · exact B1601675
  · exact B1601679
  · exact B1601683
  · exact B1601687
  · exact B1601691
  · exact B1601695
  · exact B1601699
  · exact B1601703
  · exact B1601707
  · exact B1601711
  · exact B1601715
  · exact B1601719
  · exact B1601723
  · exact B1601727
  · exact B1601731
  · exact B1601735
  · exact B1601739
  · exact B1601743
  · exact B1601747
  · exact B1601751
  · exact B1601755
  · exact B1601759
  · exact B1601763
  · exact B1601767
  · exact B1601771
  · exact B1601775
  · exact B1601779
  · exact B1601783
  · exact B1601787
  · exact B1601791
  · exact B1601795
  · exact B1601799
  · exact B1601803
  · exact B1601807
  · exact B1601811
  · exact B1601815
  · exact B1601819
  · exact B1601823
  · exact B1601827
  · exact B1601831
  · exact B1601835
  · exact B1601839
  · exact B1601843
  · exact B1601847
  · exact B1601851
  · exact B1601855
  · exact B1601859
  · exact B1601863
  · exact B1601867
  · exact B1601871
  · exact B1601875
  · exact B1601879
  · exact B1601883
  · exact B1601887
  · exact B1601891
  · exact B1601895
  · exact B1601899
  · exact B1601903
  · exact B1601907
  · exact B1601911
  · exact B1601915
  · exact B1601919
  · exact B1601923
  · exact B1601927
  · exact B1601931
  · exact B1601935
  · exact B1601939
  · exact B1601943
  · exact B1601947
  · exact B1601951
  · exact B1601955
  · exact B1601959
  · exact B1601963
  · exact B1601967
  · exact B1601971
  · exact B1601975
  · exact B1601979
  · exact B1601983
  · exact B1601987
  · exact B1601991
  · exact B1601995
  · exact B1601999
  · exact B1602003
  · exact B1602007
  · exact B1602011
  · exact B1602015
  · exact B1602019
  · exact B1602023
  · exact B1602027
  · exact B1602031
  · exact B1602035
  · exact B1602039
  · exact B1602043
  · exact B1602047
  · exact B1602051
  · exact B1602055
  · exact B1602059
  · exact B1602063
  · exact B1602067
  · exact B1602071
  · exact B1602075
  · exact B1602079
  · exact B1602083
  · exact B1602087
  · exact B1602091
  · exact B1602095
  · exact B1602099
  · exact B1602103
  · exact B1602107
  · exact B1602111
  · exact B1602115
  · exact B1602119
  · exact B1602123
  · exact B1602127
  · exact B1602131
  · exact B1602135
  · exact B1602139
  · exact B1602143
  · exact B1602147
  · exact B1602151
  · exact B1602155
  · exact B1602159
  · exact B1602163
  · exact B1602167
  · exact B1602171
  · exact B1602175
  · exact B1602179
  · exact B1602183
  · exact B1602187
  · exact B1602191
  · exact B1602195
  · exact B1602199
  · exact B1602203
  · exact B1602207
  · exact B1602211
  · exact B1602215
  · exact B1602219
  · exact B1602223
  · exact B1602227
  · exact B1602231
  · exact B1602235
  · exact B1602239
  · exact B1602243
  · exact B1602247
  · exact B1602251
  · exact B1602255
  · exact B1602259
  · exact B1602263
  · exact B1602267
  · exact B1602271
  · exact B1602275
  · exact B1602279
  · exact B1602283
  · exact B1602287
  · exact B1602291
  · exact B1602295
  · exact B1602299
  · exact B1602303
  · exact B1602307
  · exact B1602311
  · exact B1602315
  · exact B1602319
  · exact B1602323
  · exact B1602327
  · exact B1602331
  · exact B1602335
  · exact B1602339
  · exact B1602343
  · exact B1602347
  · exact B1602351
  · exact B1602355
  · exact B1602359
  · exact B1602363
  · exact B1602367
  · exact B1602371
  · exact B1602375
  · exact B1602379
  · exact B1602383
  · exact B1602387
  · exact B1602391
  · exact B1602395
  · exact B1602399
  · exact B1602403
  · exact B1602407
  · exact B1602411
  · exact B1602415
  · exact B1602419
  · exact B1602423
  · exact B1602427
  · exact B1602431
  · exact B1602435
  · exact B1602439
  · exact B1602443
  · exact B1602447
  · exact B1602451
  · exact B1602455
  · exact B1602459
  · exact B1602463
  · exact B1602467
  · exact B1602471
  · exact B1602475
  · exact B1602479
  · exact B1602483
  · exact B1602487
  · exact B1602491
  · exact B1602495
  · exact B1602499
  · exact B1602503
  · exact B1602507
  · exact B1602511
  · exact B1602515
  · exact B1602519
  · exact B1602523
  · exact B1602527
  · exact B1602531
  · exact B1602535
  · exact B1602539
  · exact B1602543
  · exact B1602547
  · exact B1602551
  · exact B1602555
  · exact B1602559
  · exact B1602563
  · exact B1602567
  · exact B1602571
  · exact B1602575
  · exact B1602579
  · exact B1602583
  · exact B1602587
  · exact B1602591
  · exact B1602595
  · exact B1602599
  · exact B1602603
  · exact B1602607
  · exact B1602611
  · exact B1602615
  · exact B1602619
  · exact B1602623
  · exact B1602627
  · exact B1602631
  · exact B1602635
  · exact B1602639
  · exact B1602643
  · exact B1602647
  · exact B1602651
  · exact B1602655
  · exact B1602659
  · exact B1602663
  · exact B1602667
  · exact B1602671
  · exact B1602675
  · exact B1602679
  · exact B1602683
  · exact B1602687
  · exact B1602691
  · exact B1602695
  · exact B1602699
  · exact B1602703
  · exact B1602707
  · exact B1602711
  · exact B1602715
  · exact B1602719
  · exact B1602723
  · exact B1602727
  · exact B1602731
  · exact B1602735
  · exact B1602739
  · exact B1602743
  · exact B1602747
  · exact B1602751
  · exact B1602755
  · exact B1602759
  · exact B1602763
  · exact B1602767
  · exact B1602771
  · exact B1602775
  · exact B1602779
  · exact B1602783
  · exact B1602787
  · exact B1602791
  · exact B1602795
  · exact B1602799
  · exact B1602803
  · exact B1602807
  · exact B1602811
  · exact B1602815
  · exact B1602819
  · exact B1602823
  · exact B1602827
  · exact B1602831
  · exact B1602835
  · exact B1602839
  · exact B1602843
  · exact B1602847
  · exact B1602851
  · exact B1602855
  · exact B1602859
  · exact B1602863
  · exact B1602867
  · exact B1602871
  · exact B1602875
  · exact B1602879
  · exact B1602883
  · exact B1602887
  · exact B1602891
  · exact B1602895
  · exact B1602899
  · exact B1602903
  · exact B1602907
  · exact B1602911
  · exact B1602915
  · exact B1602919
  · exact B1602923
  · exact B1602927
  · exact B1602931
  · exact B1602935
  · exact B1602939
  · exact B1602943
  · exact B1602947
  · exact B1602951
  · exact B1602955
  · exact B1602959
  · exact B1602963
  · exact B1602967
  · exact B1602971
  · exact B1602975
  · exact B1602979
  · exact B1602983
  · exact B1602987
  · exact B1602991
  · exact B1602995
  · exact B1602999

theorem solution (m : ℕ) (hlo : 1600999 ≤ m) (hhi : m ≤ 1602999) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 400249 ≤ j := by omega
    have hj2 : j ≤ 400749 := by omega
    have hb : Blo 1600999 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
