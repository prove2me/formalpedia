-- Prove2me | solution 1 for syracuse_descends_range_1784093_1786093
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:45:27.546517+00:00
-- url     : https://prove2.me/submissions/5f960ee3-61c2-43e5-a34a-26348e1fc293

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


theorem B2678789 : Blo 1784093 2678789 := bbase (se 4 (by rfl) ⟨251136, by rfl⟩ : syracuseStep 2678789 = 502273) (by norm_num)
theorem B2678813 : Blo 1784093 2678813 := bbase (se 3 (by rfl) ⟨502277, by rfl⟩ : syracuseStep 2678813 = 1004555) (by norm_num)
theorem B2678837 : Blo 1784093 2678837 := bbase (se 5 (by rfl) ⟨125570, by rfl⟩ : syracuseStep 2678837 = 251141) (by norm_num)
theorem B4071485 : Blo 1784093 4071485 := bbase (se 3 (by rfl) ⟨763403, by rfl⟩ : syracuseStep 4071485 = 1526807) (by norm_num)
theorem B2678861 : Blo 1784093 2678861 := bbase (se 3 (by rfl) ⟨502286, by rfl⟩ : syracuseStep 2678861 = 1004573) (by norm_num)
theorem B2007121 : Blo 1784093 2007121 := bbase (se 2 (by rfl) ⟨752670, by rfl⟩ : syracuseStep 2007121 = 1505341) (by norm_num)
theorem B2678885 : Blo 1784093 2678885 := bbase (se 4 (by rfl) ⟨251145, by rfl⟩ : syracuseStep 2678885 = 502291) (by norm_num)
theorem B2007157 : Blo 1784093 2007157 := bbase (se 5 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 2007157 = 188171) (by norm_num)
theorem B2678909 : Blo 1784093 2678909 := bbase (se 3 (by rfl) ⟨502295, by rfl⟩ : syracuseStep 2678909 = 1004591) (by norm_num)
theorem B2678933 : Blo 1784093 2678933 := bbase (se 6 (by rfl) ⟨62787, by rfl⟩ : syracuseStep 2678933 = 125575) (by norm_num)
theorem B2007193 : Blo 1784093 2007193 := bbase (se 2 (by rfl) ⟨752697, by rfl⟩ : syracuseStep 2007193 = 1505395) (by norm_num)
theorem B2678957 : Blo 1784093 2678957 := bbase (se 3 (by rfl) ⟨502304, by rfl⟩ : syracuseStep 2678957 = 1004609) (by norm_num)
theorem B13557941 : Blo 1784093 13557941 := bbase (se 5 (by rfl) ⟨635528, by rfl⟩ : syracuseStep 13557941 = 1271057) (by norm_num)
theorem B4014269 : Blo 1784093 4014269 := bbase (se 3 (by rfl) ⟨752675, by rfl⟩ : syracuseStep 4014269 = 1505351) (by norm_num)
theorem B2007229 : Blo 1784093 2007229 := bbase (se 3 (by rfl) ⟨376355, by rfl⟩ : syracuseStep 2007229 = 752711) (by norm_num)
theorem B2678981 : Blo 1784093 2678981 := bbase (se 4 (by rfl) ⟨251154, by rfl⟩ : syracuseStep 2678981 = 502309) (by norm_num)
theorem B2679005 : Blo 1784093 2679005 := bbase (se 3 (by rfl) ⟨502313, by rfl⟩ : syracuseStep 2679005 = 1004627) (by norm_num)
theorem B2007265 : Blo 1784093 2007265 := bbase (se 2 (by rfl) ⟨752724, by rfl⟩ : syracuseStep 2007265 = 1505449) (by norm_num)
theorem B2679029 : Blo 1784093 2679029 := bbase (se 5 (by rfl) ⟨125579, by rfl⟩ : syracuseStep 2679029 = 251159) (by norm_num)
theorem B4014341 : Blo 1784093 4014341 := bbase (se 4 (by rfl) ⟨376344, by rfl⟩ : syracuseStep 4014341 = 752689) (by norm_num)
theorem B2007301 : Blo 1784093 2007301 := bbase (se 4 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 2007301 = 376369) (by norm_num)
theorem B2679053 : Blo 1784093 2679053 := bbase (se 3 (by rfl) ⟨502322, by rfl⟩ : syracuseStep 2679053 = 1004645) (by norm_num)
theorem B2679077 : Blo 1784093 2679077 := bbase (se 4 (by rfl) ⟨251163, by rfl⟩ : syracuseStep 2679077 = 502327) (by norm_num)
theorem B2007337 : Blo 1784093 2007337 := bbase (se 2 (by rfl) ⟨752751, by rfl⟩ : syracuseStep 2007337 = 1505503) (by norm_num)
theorem B7627061 : Blo 1784093 7627061 := bbase (se 5 (by rfl) ⟨357518, by rfl⟩ : syracuseStep 7627061 = 715037) (by norm_num)
theorem B2679101 : Blo 1784093 2679101 := bbase (se 3 (by rfl) ⟨502331, by rfl⟩ : syracuseStep 2679101 = 1004663) (by norm_num)
theorem B4014413 : Blo 1784093 4014413 := bbase (se 3 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 4014413 = 1505405) (by norm_num)
theorem B2007373 : Blo 1784093 2007373 := bbase (se 3 (by rfl) ⟨376382, by rfl⟩ : syracuseStep 2007373 = 752765) (by norm_num)
theorem B2679125 : Blo 1784093 2679125 := bbase (se 10 (by rfl) ⟨3924, by rfl⟩ : syracuseStep 2679125 = 7849) (by norm_num)
theorem B2007409 : Blo 1784093 2007409 := bbase (se 2 (by rfl) ⟨752778, by rfl⟩ : syracuseStep 2007409 = 1505557) (by norm_num)
theorem B4014485 : Blo 1784093 4014485 := bbase (se 6 (by rfl) ⟨94089, by rfl⟩ : syracuseStep 4014485 = 188179) (by norm_num)
theorem B2007445 : Blo 1784093 2007445 := bbase (se 6 (by rfl) ⟨47049, by rfl⟩ : syracuseStep 2007445 = 94099) (by norm_num)
theorem B9036197 : Blo 1784093 9036197 := bbase (se 4 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 9036197 = 1694287) (by norm_num)
theorem B2007481 : Blo 1784093 2007481 := bbase (se 2 (by rfl) ⟨752805, by rfl⟩ : syracuseStep 2007481 = 1505611) (by norm_num)
theorem B4014557 : Blo 1784093 4014557 := bbase (se 3 (by rfl) ⟨752729, by rfl⟩ : syracuseStep 4014557 = 1505459) (by norm_num)
theorem B2007517 : Blo 1784093 2007517 := bbase (se 3 (by rfl) ⟨376409, by rfl⟩ : syracuseStep 2007517 = 752819) (by norm_num)
theorem B2007553 : Blo 1784093 2007553 := bbase (se 2 (by rfl) ⟨752832, by rfl⟩ : syracuseStep 2007553 = 1505665) (by norm_num)
theorem B4014629 : Blo 1784093 4014629 := bbase (se 4 (by rfl) ⟨376371, by rfl⟩ : syracuseStep 4014629 = 752743) (by norm_num)
theorem B2007589 : Blo 1784093 2007589 := bbase (se 4 (by rfl) ⟨188211, by rfl⟩ : syracuseStep 2007589 = 376423) (by norm_num)
theorem B6021701 : Blo 1784093 6021701 := bbase (se 4 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 6021701 = 1129069) (by norm_num)
theorem B2007625 : Blo 1784093 2007625 := bbase (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) (by norm_num)
theorem B13550165 : Blo 1784093 13550165 := bbase (se 8 (by rfl) ⟨79395, by rfl⟩ : syracuseStep 13550165 = 158791) (by norm_num)
theorem B4014701 : Blo 1784093 4014701 := bbase (se 3 (by rfl) ⟨752756, by rfl⟩ : syracuseStep 4014701 = 1505513) (by norm_num)
theorem B2007661 : Blo 1784093 2007661 := bbase (se 3 (by rfl) ⟨376436, by rfl⟩ : syracuseStep 2007661 = 752873) (by norm_num)
theorem B4072069 : Blo 1784093 4072069 := bbase (se 4 (by rfl) ⟨381756, by rfl⟩ : syracuseStep 4072069 = 763513) (by norm_num)
theorem B2007697 : Blo 1784093 2007697 := bbase (se 2 (by rfl) ⟨752886, by rfl⟩ : syracuseStep 2007697 = 1505773) (by norm_num)
theorem B4014773 : Blo 1784093 4014773 := bbase (se 5 (by rfl) ⟨188192, by rfl⟩ : syracuseStep 4014773 = 376385) (by norm_num)
theorem B6431413 : Blo 1784093 6431413 := bbase (se 5 (by rfl) ⟨301472, by rfl⟩ : syracuseStep 6431413 = 602945) (by norm_num)
theorem B2007733 : Blo 1784093 2007733 := bbase (se 5 (by rfl) ⟨94112, by rfl⟩ : syracuseStep 2007733 = 188225) (by norm_num)
theorem B2859725 : Blo 1784093 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B2007769 : Blo 1784093 2007769 := bbase (se 2 (by rfl) ⟨752913, by rfl⟩ : syracuseStep 2007769 = 1505827) (by norm_num)
theorem B2540269 : Blo 1784093 2540269 := bbase (se 3 (by rfl) ⟨476300, by rfl⟩ : syracuseStep 2540269 = 952601) (by norm_num)
theorem B4014845 : Blo 1784093 4014845 := bbase (se 3 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 4014845 = 1505567) (by norm_num)
theorem B2007805 : Blo 1784093 2007805 := bbase (se 3 (by rfl) ⟨376463, by rfl⟩ : syracuseStep 2007805 = 752927) (by norm_num)
theorem B2007841 : Blo 1784093 2007841 := bbase (se 2 (by rfl) ⟨752940, by rfl⟩ : syracuseStep 2007841 = 1505881) (by norm_num)
theorem B4014917 : Blo 1784093 4014917 := bbase (se 4 (by rfl) ⟨376398, by rfl⟩ : syracuseStep 4014917 = 752797) (by norm_num)
theorem B6431557 : Blo 1784093 6431557 := bbase (se 4 (by rfl) ⟨602958, by rfl⟩ : syracuseStep 6431557 = 1205917) (by norm_num)
theorem B2007877 : Blo 1784093 2007877 := bbase (se 4 (by rfl) ⟨188238, by rfl⟩ : syracuseStep 2007877 = 376477) (by norm_num)
theorem B2007913 : Blo 1784093 2007913 := bbase (se 2 (by rfl) ⟨752967, by rfl⟩ : syracuseStep 2007913 = 1505935) (by norm_num)
theorem B4014989 : Blo 1784093 4014989 := bbase (se 3 (by rfl) ⟨752810, by rfl⟩ : syracuseStep 4014989 = 1505621) (by norm_num)
theorem B2007949 : Blo 1784093 2007949 := bbase (se 3 (by rfl) ⟨376490, by rfl⟩ : syracuseStep 2007949 = 752981) (by norm_num)
theorem B17154965 : Blo 1784093 17154965 := bbase (se 6 (by rfl) ⟨402069, by rfl⟩ : syracuseStep 17154965 = 804139) (by norm_num)
theorem B2007985 : Blo 1784093 2007985 := bbase (se 2 (by rfl) ⟨752994, by rfl⟩ : syracuseStep 2007985 = 1505989) (by norm_num)
theorem B12862421 : Blo 1784093 12862421 := bbase (se 7 (by rfl) ⟨150731, by rfl⟩ : syracuseStep 12862421 = 301463) (by norm_num)
theorem B4015061 : Blo 1784093 4015061 := bbase (se 7 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 4015061 = 94103) (by norm_num)
theorem B2008021 : Blo 1784093 2008021 := bbase (se 7 (by rfl) ⟨23531, by rfl⟩ : syracuseStep 2008021 = 47063) (by norm_num)
theorem B6431717 : Blo 1784093 6431717 := bbase (se 4 (by rfl) ⟨602973, by rfl⟩ : syracuseStep 6431717 = 1205947) (by norm_num)
theorem B6022133 : Blo 1784093 6022133 := bbase (se 5 (by rfl) ⟨282287, by rfl⟩ : syracuseStep 6022133 = 564575) (by norm_num)
theorem B2008057 : Blo 1784093 2008057 := bbase (se 2 (by rfl) ⟨753021, by rfl⟩ : syracuseStep 2008057 = 1506043) (by norm_num)
theorem B4015133 : Blo 1784093 4015133 := bbase (se 3 (by rfl) ⟨752837, by rfl⟩ : syracuseStep 4015133 = 1505675) (by norm_num)
theorem B2008093 : Blo 1784093 2008093 := bbase (se 3 (by rfl) ⟨376517, by rfl⟩ : syracuseStep 2008093 = 753035) (by norm_num)
theorem B2008129 : Blo 1784093 2008129 := bbase (se 2 (by rfl) ⟨753048, by rfl⟩ : syracuseStep 2008129 = 1506097) (by norm_num)
theorem B4015205 : Blo 1784093 4015205 := bbase (se 4 (by rfl) ⟨376425, by rfl⟩ : syracuseStep 4015205 = 752851) (by norm_num)
theorem B6431845 : Blo 1784093 6431845 := bbase (se 4 (by rfl) ⟨602985, by rfl⟩ : syracuseStep 6431845 = 1205971) (by norm_num)
theorem B2008165 : Blo 1784093 2008165 := bbase (se 4 (by rfl) ⟨188265, by rfl⟩ : syracuseStep 2008165 = 376531) (by norm_num)
theorem B2008201 : Blo 1784093 2008201 := bbase (se 2 (by rfl) ⟨753075, by rfl⟩ : syracuseStep 2008201 = 1506151) (by norm_num)
theorem B2860181 : Blo 1784093 2860181 := bbase (se 6 (by rfl) ⟨67035, by rfl⟩ : syracuseStep 2860181 = 134071) (by norm_num)
theorem B4015277 : Blo 1784093 4015277 := bbase (se 3 (by rfl) ⟨752864, by rfl⟩ : syracuseStep 4015277 = 1505729) (by norm_num)
theorem B2008237 : Blo 1784093 2008237 := bbase (se 3 (by rfl) ⟨376544, by rfl⟩ : syracuseStep 2008237 = 753089) (by norm_num)
theorem B2008273 : Blo 1784093 2008273 := bbase (se 2 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 2008273 = 1506205) (by norm_num)
theorem B36660437 : Blo 1784093 36660437 := bbase (se 7 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 36660437 = 859229) (by norm_num)
theorem B4015349 : Blo 1784093 4015349 := bbase (se 5 (by rfl) ⟨188219, by rfl⟩ : syracuseStep 4015349 = 376439) (by norm_num)
theorem B2008309 : Blo 1784093 2008309 := bbase (se 5 (by rfl) ⟨94139, by rfl⟩ : syracuseStep 2008309 = 188279) (by norm_num)
theorem B2008345 : Blo 1784093 2008345 := bbase (se 2 (by rfl) ⟨753129, by rfl⟩ : syracuseStep 2008345 = 1506259) (by norm_num)
theorem B4015421 : Blo 1784093 4015421 := bbase (se 3 (by rfl) ⟨752891, by rfl⟩ : syracuseStep 4015421 = 1505783) (by norm_num)
theorem B2008381 : Blo 1784093 2008381 := bbase (se 3 (by rfl) ⟨376571, by rfl⟩ : syracuseStep 2008381 = 753143) (by norm_num)
theorem B2008417 : Blo 1784093 2008417 := bbase (se 2 (by rfl) ⟨753156, by rfl⟩ : syracuseStep 2008417 = 1506313) (by norm_num)
theorem B4015493 : Blo 1784093 4015493 := bbase (se 4 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 4015493 = 752905) (by norm_num)
theorem B2008453 : Blo 1784093 2008453 := bbase (se 4 (by rfl) ⟨188292, by rfl⟩ : syracuseStep 2008453 = 376585) (by norm_num)
theorem B6022565 : Blo 1784093 6022565 := bbase (se 4 (by rfl) ⟨564615, by rfl⟩ : syracuseStep 6022565 = 1129231) (by norm_num)
theorem B2008489 : Blo 1784093 2008489 := bbase (se 2 (by rfl) ⟨753183, by rfl⟩ : syracuseStep 2008489 = 1506367) (by norm_num)
theorem B4015565 : Blo 1784093 4015565 := bbase (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) (by norm_num)
theorem B2008525 : Blo 1784093 2008525 := bbase (se 3 (by rfl) ⟨376598, by rfl⟩ : syracuseStep 2008525 = 753197) (by norm_num)
theorem B3810797 : Blo 1784093 3810797 := bbase (se 3 (by rfl) ⟨714524, by rfl⟩ : syracuseStep 3810797 = 1429049) (by norm_num)
theorem B2008561 : Blo 1784093 2008561 := bbase (se 2 (by rfl) ⟨753210, by rfl⟩ : syracuseStep 2008561 = 1506421) (by norm_num)
theorem B2541061 : Blo 1784093 2541061 := bbase (se 4 (by rfl) ⟨238224, by rfl⟩ : syracuseStep 2541061 = 476449) (by norm_num)
theorem B4015637 : Blo 1784093 4015637 := bbase (se 6 (by rfl) ⟨94116, by rfl⟩ : syracuseStep 4015637 = 188233) (by norm_num)
theorem B2008597 : Blo 1784093 2008597 := bbase (se 6 (by rfl) ⟨47076, by rfl⟩ : syracuseStep 2008597 = 94153) (by norm_num)
theorem B2008633 : Blo 1784093 2008633 := bbase (se 2 (by rfl) ⟨753237, by rfl⟩ : syracuseStep 2008633 = 1506475) (by norm_num)
theorem B6776405 : Blo 1784093 6776405 := bbase (se 8 (by rfl) ⟨39705, by rfl⟩ : syracuseStep 6776405 = 79411) (by norm_num)
theorem B4015709 : Blo 1784093 4015709 := bbase (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) (by norm_num)
theorem B2008669 : Blo 1784093 2008669 := bbase (se 3 (by rfl) ⟨376625, by rfl⟩ : syracuseStep 2008669 = 753251) (by norm_num)
theorem B2008705 : Blo 1784093 2008705 := bbase (se 2 (by rfl) ⟨753264, by rfl⟩ : syracuseStep 2008705 = 1506529) (by norm_num)
theorem B4015781 : Blo 1784093 4015781 := bbase (se 4 (by rfl) ⟨376479, by rfl⟩ : syracuseStep 4015781 = 752959) (by norm_num)
theorem B2008741 : Blo 1784093 2008741 := bbase (se 4 (by rfl) ⟨188319, by rfl⟩ : syracuseStep 2008741 = 376639) (by norm_num)
theorem B9037493 : Blo 1784093 9037493 := bbase (se 5 (by rfl) ⟨423632, by rfl⟩ : syracuseStep 9037493 = 847265) (by norm_num)
theorem B2008777 : Blo 1784093 2008777 := bbase (se 2 (by rfl) ⟨753291, by rfl⟩ : syracuseStep 2008777 = 1506583) (by norm_num)
theorem B3811045 : Blo 1784093 3811045 := bbase (se 4 (by rfl) ⟨357285, by rfl⟩ : syracuseStep 3811045 = 714571) (by norm_num)
theorem B4015853 : Blo 1784093 4015853 := bbase (se 3 (by rfl) ⟨752972, by rfl⟩ : syracuseStep 4015853 = 1505945) (by norm_num)
theorem B2008813 : Blo 1784093 2008813 := bbase (se 3 (by rfl) ⟨376652, by rfl⟩ : syracuseStep 2008813 = 753305) (by norm_num)
theorem B2008849 : Blo 1784093 2008849 := bbase (se 2 (by rfl) ⟨753318, by rfl⟩ : syracuseStep 2008849 = 1506637) (by norm_num)
theorem B4073237 : Blo 1784093 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B4015925 : Blo 1784093 4015925 := bbase (se 5 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 4015925 = 376493) (by norm_num)
theorem B2008885 : Blo 1784093 2008885 := bbase (se 5 (by rfl) ⟨94166, by rfl⟩ : syracuseStep 2008885 = 188333) (by norm_num)
theorem B6022997 : Blo 1784093 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B2541397 : Blo 1784093 2541397 := bbase (se 9 (by rfl) ⟨7445, by rfl⟩ : syracuseStep 2541397 = 14891) (by norm_num)
theorem B2008921 : Blo 1784093 2008921 := bbase (se 2 (by rfl) ⟨753345, by rfl⟩ : syracuseStep 2008921 = 1506691) (by norm_num)
theorem B6776693 : Blo 1784093 6776693 := bbase (se 5 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 6776693 = 635315) (by norm_num)
theorem B4015997 : Blo 1784093 4015997 := bbase (se 3 (by rfl) ⟨752999, by rfl⟩ : syracuseStep 4015997 = 1505999) (by norm_num)
theorem B2008957 : Blo 1784093 2008957 := bbase (se 3 (by rfl) ⟨376679, by rfl⟩ : syracuseStep 2008957 = 753359) (by norm_num)
theorem B2008993 : Blo 1784093 2008993 := bbase (se 2 (by rfl) ⟨753372, by rfl⟩ : syracuseStep 2008993 = 1506745) (by norm_num)
theorem B4016069 : Blo 1784093 4016069 := bbase (se 4 (by rfl) ⟨376506, by rfl⟩ : syracuseStep 4016069 = 753013) (by norm_num)
theorem B2009029 : Blo 1784093 2009029 := bbase (se 4 (by rfl) ⟨188346, by rfl⟩ : syracuseStep 2009029 = 376693) (by norm_num)
theorem B2009065 : Blo 1784093 2009065 := bbase (se 2 (by rfl) ⟨753399, by rfl⟩ : syracuseStep 2009065 = 1506799) (by norm_num)
theorem B5720053 : Blo 1784093 5720053 := bbase (se 5 (by rfl) ⟨268127, by rfl⟩ : syracuseStep 5720053 = 536255) (by norm_num)
theorem B4016141 : Blo 1784093 4016141 := bbase (se 3 (by rfl) ⟨753026, by rfl⟩ : syracuseStep 4016141 = 1506053) (by norm_num)
theorem B2009101 : Blo 1784093 2009101 := bbase (se 3 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 2009101 = 753413) (by norm_num)
theorem B2541613 : Blo 1784093 2541613 := bbase (se 3 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 2541613 = 953105) (by norm_num)
theorem B2009137 : Blo 1784093 2009137 := bbase (se 2 (by rfl) ⟨753426, by rfl⟩ : syracuseStep 2009137 = 1506853) (by norm_num)
theorem B4016213 : Blo 1784093 4016213 := bbase (se 8 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 4016213 = 47065) (by norm_num)
theorem B2009173 : Blo 1784093 2009173 := bbase (se 8 (by rfl) ⟨11772, by rfl⟩ : syracuseStep 2009173 = 23545) (by norm_num)
theorem B7940213 : Blo 1784093 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B2009209 : Blo 1784093 2009209 := bbase (se 2 (by rfl) ⟨753453, by rfl⟩ : syracuseStep 2009209 = 1506907) (by norm_num)
theorem B5081221 : Blo 1784093 5081221 := bbase (se 4 (by rfl) ⟨476364, by rfl⟩ : syracuseStep 5081221 = 952729) (by norm_num)
theorem B4016285 : Blo 1784093 4016285 := bbase (se 3 (by rfl) ⟨753053, by rfl⟩ : syracuseStep 4016285 = 1506107) (by norm_num)
theorem B2009245 : Blo 1784093 2009245 := bbase (se 3 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 2009245 = 753467) (by norm_num)
theorem B4516013 : Blo 1784093 4516013 := bbase (se 3 (by rfl) ⟨846752, by rfl⟩ : syracuseStep 4516013 = 1693505) (by norm_num)
theorem B2009281 : Blo 1784093 2009281 := bbase (se 2 (by rfl) ⟨753480, by rfl⟩ : syracuseStep 2009281 = 1506961) (by norm_num)
theorem B3811549 : Blo 1784093 3811549 := bbase (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) (by norm_num)
theorem B4016357 : Blo 1784093 4016357 := bbase (se 4 (by rfl) ⟨376533, by rfl⟩ : syracuseStep 4016357 = 753067) (by norm_num)
theorem B2009317 : Blo 1784093 2009317 := bbase (se 4 (by rfl) ⟨188373, by rfl⟩ : syracuseStep 2009317 = 376747) (by norm_num)
theorem B6023429 : Blo 1784093 6023429 := bbase (se 4 (by rfl) ⟨564696, by rfl⟩ : syracuseStep 6023429 = 1129393) (by norm_num)
theorem B2009353 : Blo 1784093 2009353 := bbase (se 2 (by rfl) ⟨753507, by rfl⟩ : syracuseStep 2009353 = 1507015) (by norm_num)
theorem B4016429 : Blo 1784093 4016429 := bbase (se 3 (by rfl) ⟨753080, by rfl⟩ : syracuseStep 4016429 = 1506161) (by norm_num)
theorem B29804885 : Blo 1784093 29804885 := bbase (se 10 (by rfl) ⟨43659, by rfl⟩ : syracuseStep 29804885 = 87319) (by norm_num)
theorem B4581733 : Blo 1784093 4581733 := bbase (se 4 (by rfl) ⟨429537, by rfl⟩ : syracuseStep 4581733 = 859075) (by norm_num)
theorem B4016501 : Blo 1784093 4016501 := bbase (se 5 (by rfl) ⟨188273, by rfl⟩ : syracuseStep 4016501 = 376547) (by norm_num)
theorem B2541989 : Blo 1784093 2541989 := bbase (se 4 (by rfl) ⟨238311, by rfl⟩ : syracuseStep 2541989 = 476623) (by norm_num)
theorem B4016573 : Blo 1784093 4016573 := bbase (se 3 (by rfl) ⟨753107, by rfl⟩ : syracuseStep 4016573 = 1506215) (by norm_num)
theorem B4286965 : Blo 1784093 4286965 := bbase (se 5 (by rfl) ⟨200951, by rfl⟩ : syracuseStep 4286965 = 401903) (by norm_num)
theorem B4516357 : Blo 1784093 4516357 := bbase (se 4 (by rfl) ⟨423408, by rfl⟩ : syracuseStep 4516357 = 846817) (by norm_num)
theorem B4016645 : Blo 1784093 4016645 := bbase (se 4 (by rfl) ⟨376560, by rfl⟩ : syracuseStep 4016645 = 753121) (by norm_num)
theorem B4016717 : Blo 1784093 4016717 := bbase (se 3 (by rfl) ⟨753134, by rfl⟩ : syracuseStep 4016717 = 1506269) (by norm_num)
theorem B4516469 : Blo 1784093 4516469 := bbase (se 5 (by rfl) ⟨211709, by rfl⟩ : syracuseStep 4516469 = 423419) (by norm_num)
theorem B4016789 : Blo 1784093 4016789 := bbase (se 6 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 4016789 = 188287) (by norm_num)
theorem B7621285 : Blo 1784093 7621285 := bbase (se 4 (by rfl) ⟨714495, by rfl⟩ : syracuseStep 7621285 = 1428991) (by norm_num)
theorem B6023861 : Blo 1784093 6023861 := bbase (se 5 (by rfl) ⟨282368, by rfl⟩ : syracuseStep 6023861 = 564737) (by norm_num)
theorem B4016861 : Blo 1784093 4016861 := bbase (se 3 (by rfl) ⟨753161, by rfl⟩ : syracuseStep 4016861 = 1506323) (by norm_num)
theorem B2411293 : Blo 1784093 2411293 := bbase (se 3 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 2411293 = 904235) (by norm_num)
theorem B4016933 : Blo 1784093 4016933 := bbase (se 4 (by rfl) ⟨376587, by rfl⟩ : syracuseStep 4016933 = 753175) (by norm_num)
theorem B4516661 : Blo 1784093 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B5720885 : Blo 1784093 5720885 := bbase (se 5 (by rfl) ⟨268166, by rfl⟩ : syracuseStep 5720885 = 536333) (by norm_num)
theorem B4017005 : Blo 1784093 4017005 := bbase (se 3 (by rfl) ⟨753188, by rfl⟩ : syracuseStep 4017005 = 1506377) (by norm_num)
theorem B4017077 : Blo 1784093 4017077 := bbase (se 5 (by rfl) ⟨188300, by rfl⟩ : syracuseStep 4017077 = 376601) (by norm_num)
theorem B9038789 : Blo 1784093 9038789 := bbase (se 4 (by rfl) ⟨847386, by rfl⟩ : syracuseStep 9038789 = 1694773) (by norm_num)
theorem B4017149 : Blo 1784093 4017149 := bbase (se 3 (by rfl) ⟨753215, by rfl⟩ : syracuseStep 4017149 = 1506431) (by norm_num)
theorem B6777877 : Blo 1784093 6777877 := bbase (se 6 (by rfl) ⟨158856, by rfl⟩ : syracuseStep 6777877 = 317713) (by norm_num)
theorem B9161765 : Blo 1784093 9161765 := bbase (se 4 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 9161765 = 1717831) (by norm_num)
theorem B4017221 : Blo 1784093 4017221 := bbase (se 4 (by rfl) ⟨376614, by rfl⟩ : syracuseStep 4017221 = 753229) (by norm_num)
theorem B3812437 : Blo 1784093 3812437 := bbase (se 8 (by rfl) ⟨22338, by rfl⟩ : syracuseStep 3812437 = 44677) (by norm_num)
theorem B6024293 : Blo 1784093 6024293 := bbase (se 4 (by rfl) ⟨564777, by rfl⟩ : syracuseStep 6024293 = 1129555) (by norm_num)
theorem B1985657 : Blo 1784093 1985657 := bbase (se 2 (by rfl) ⟨744621, by rfl⟩ : syracuseStep 1985657 = 1489243) (by norm_num)
theorem B4517005 : Blo 1784093 4517005 := bbase (se 3 (by rfl) ⟨846938, by rfl⟩ : syracuseStep 4517005 = 1693877) (by norm_num)
theorem B4017293 : Blo 1784093 4017293 := bbase (se 3 (by rfl) ⟨753242, by rfl⟩ : syracuseStep 4017293 = 1506485) (by norm_num)
theorem B25734293 : Blo 1784093 25734293 := bbase (se 6 (by rfl) ⟨603147, by rfl⟩ : syracuseStep 25734293 = 1206295) (by norm_num)
theorem B2714797 : Blo 1784093 2714797 := bbase (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) (by norm_num)
theorem B4017365 : Blo 1784093 4017365 := bbase (se 7 (by rfl) ⟨47078, by rfl⟩ : syracuseStep 4017365 = 94157) (by norm_num)
theorem B4517117 : Blo 1784093 4517117 := bbase (se 3 (by rfl) ⟨846959, by rfl⟩ : syracuseStep 4517117 = 1693919) (by norm_num)
theorem B4017437 : Blo 1784093 4017437 := bbase (se 3 (by rfl) ⟨753269, by rfl⟩ : syracuseStep 4017437 = 1506539) (by norm_num)
theorem B11439413 : Blo 1784093 11439413 := bbase (se 5 (by rfl) ⟨536222, by rfl⟩ : syracuseStep 11439413 = 1072445) (by norm_num)
theorem B6778181 : Blo 1784093 6778181 := bbase (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) (by norm_num)
theorem B4017509 : Blo 1784093 4017509 := bbase (se 4 (by rfl) ⟨376641, by rfl⟩ : syracuseStep 4017509 = 753283) (by norm_num)
theorem B2174329 : Blo 1784093 2174329 := bbase (se 2 (by rfl) ⟨815373, by rfl⟩ : syracuseStep 2174329 = 1630747) (by norm_num)
theorem B4017581 : Blo 1784093 4017581 := bbase (se 3 (by rfl) ⟨753296, by rfl⟩ : syracuseStep 4017581 = 1506593) (by norm_num)
theorem B4517309 : Blo 1784093 4517309 := bbase (se 3 (by rfl) ⟨846995, by rfl⟩ : syracuseStep 4517309 = 1693991) (by norm_num)
theorem B4287973 : Blo 1784093 4287973 := bbase (se 4 (by rfl) ⟨401997, by rfl⟩ : syracuseStep 4287973 = 803995) (by norm_num)
theorem B3260413 : Blo 1784093 3260413 := bbase (se 3 (by rfl) ⟨611327, by rfl⟩ : syracuseStep 3260413 = 1222655) (by norm_num)
theorem B4017653 : Blo 1784093 4017653 := bbase (se 5 (by rfl) ⟨188327, by rfl⟩ : syracuseStep 4017653 = 376655) (by norm_num)
theorem B6024725 : Blo 1784093 6024725 := bbase (se 6 (by rfl) ⟨141204, by rfl⟩ : syracuseStep 6024725 = 282409) (by norm_num)
theorem B4017725 : Blo 1784093 4017725 := bbase (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) (by norm_num)
theorem B4288069 : Blo 1784093 4288069 := bbase (se 4 (by rfl) ⟨402006, by rfl⟩ : syracuseStep 4288069 = 804013) (by norm_num)
theorem B3812933 : Blo 1784093 3812933 := bbase (se 4 (by rfl) ⟨357462, by rfl⟩ : syracuseStep 3812933 = 714925) (by norm_num)
theorem B5082725 : Blo 1784093 5082725 := bbase (se 4 (by rfl) ⟨476505, by rfl⟩ : syracuseStep 5082725 = 953011) (by norm_num)
theorem B4017797 : Blo 1784093 4017797 := bbase (se 4 (by rfl) ⟨376668, by rfl⟩ : syracuseStep 4017797 = 753337) (by norm_num)
theorem B4017869 : Blo 1784093 4017869 := bbase (se 3 (by rfl) ⟨753350, by rfl⟩ : syracuseStep 4017869 = 1506701) (by norm_num)
theorem B3387109 : Blo 1784093 3387109 := bbase (se 4 (by rfl) ⟨317541, by rfl⟩ : syracuseStep 3387109 = 635083) (by norm_num)
theorem B4517653 : Blo 1784093 4517653 := bbase (se 6 (by rfl) ⟨105882, by rfl⟩ : syracuseStep 4517653 = 211765) (by norm_num)
theorem B4017941 : Blo 1784093 4017941 := bbase (se 6 (by rfl) ⟨94170, by rfl⟩ : syracuseStep 4017941 = 188341) (by norm_num)
theorem B3215173 : Blo 1784093 3215173 := bbase (se 4 (by rfl) ⟨301422, by rfl⟩ : syracuseStep 3215173 = 602845) (by norm_num)
theorem B4018013 : Blo 1784093 4018013 := bbase (se 3 (by rfl) ⟨753377, by rfl⟩ : syracuseStep 4018013 = 1506755) (by norm_num)
theorem B3387253 : Blo 1784093 3387253 := bbase (se 5 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 3387253 = 317555) (by norm_num)
theorem B4517765 : Blo 1784093 4517765 := bbase (se 4 (by rfl) ⟨423540, by rfl⟩ : syracuseStep 4517765 = 847081) (by norm_num)
theorem B2322317 : Blo 1784093 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B34312085 : Blo 1784093 34312085 := bbase (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) (by norm_num)
theorem B4018085 : Blo 1784093 4018085 := bbase (se 4 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 4018085 = 753391) (by norm_num)
theorem B6025157 : Blo 1784093 6025157 := bbase (se 4 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 6025157 = 1129717) (by norm_num)
theorem B9646037 : Blo 1784093 9646037 := bbase (se 7 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 9646037 = 226079) (by norm_num)
theorem B4018157 : Blo 1784093 4018157 := bbase (se 3 (by rfl) ⟨753404, by rfl⟩ : syracuseStep 4018157 = 1506809) (by norm_num)
theorem B3387413 : Blo 1784093 3387413 := bbase (se 6 (by rfl) ⟨79392, by rfl⟩ : syracuseStep 3387413 = 158785) (by norm_num)
theorem B4018229 : Blo 1784093 4018229 := bbase (se 5 (by rfl) ⟨188354, by rfl⟩ : syracuseStep 4018229 = 376709) (by norm_num)
theorem B4517957 : Blo 1784093 4517957 := bbase (se 4 (by rfl) ⟨423558, by rfl⟩ : syracuseStep 4517957 = 847117) (by norm_num)
theorem B4288589 : Blo 1784093 4288589 := bbase (se 3 (by rfl) ⟨804110, by rfl⟩ : syracuseStep 4288589 = 1608221) (by norm_num)
theorem B2289745 : Blo 1784093 2289745 := bbase (se 2 (by rfl) ⟨858654, by rfl⟩ : syracuseStep 2289745 = 1717309) (by norm_num)
theorem B4018301 : Blo 1784093 4018301 := bbase (se 3 (by rfl) ⟨753431, by rfl⟩ : syracuseStep 4018301 = 1506863) (by norm_num)
theorem B2412677 : Blo 1784093 2412677 := bbase (se 4 (by rfl) ⟨226188, by rfl⟩ : syracuseStep 2412677 = 452377) (by norm_num)
theorem B3010709 : Blo 1784093 3010709 := bbase (se 6 (by rfl) ⟨70563, by rfl⟩ : syracuseStep 3010709 = 141127) (by norm_num)
theorem B8138917 : Blo 1784093 8138917 := bbase (se 4 (by rfl) ⟨763023, by rfl⟩ : syracuseStep 8138917 = 1526047) (by norm_num)
theorem B3387557 : Blo 1784093 3387557 := bbase (se 4 (by rfl) ⟨317583, by rfl⟩ : syracuseStep 3387557 = 635167) (by norm_num)
theorem B3436717 : Blo 1784093 3436717 := bbase (se 3 (by rfl) ⟨644384, by rfl⟩ : syracuseStep 3436717 = 1288769) (by norm_num)
theorem B4018373 : Blo 1784093 4018373 := bbase (se 4 (by rfl) ⟨376722, by rfl⟩ : syracuseStep 4018373 = 753445) (by norm_num)
theorem B9040085 : Blo 1784093 9040085 := bbase (se 7 (by rfl) ⟨105938, by rfl⟩ : syracuseStep 9040085 = 211877) (by norm_num)
theorem B10162421 : Blo 1784093 10162421 := bbase (se 5 (by rfl) ⟨476363, by rfl⟩ : syracuseStep 10162421 = 952727) (by norm_num)
theorem B3617021 : Blo 1784093 3617021 := bbase (se 3 (by rfl) ⟨678191, by rfl⟩ : syracuseStep 3617021 = 1356383) (by norm_num)
theorem B4018445 : Blo 1784093 4018445 := bbase (se 3 (by rfl) ⟨753458, by rfl⟩ : syracuseStep 4018445 = 1506917) (by norm_num)
theorem B3010837 : Blo 1784093 3010837 := bbase (se 6 (by rfl) ⟨70566, by rfl⟩ : syracuseStep 3010837 = 141133) (by norm_num)
theorem B4018517 : Blo 1784093 4018517 := bbase (se 10 (by rfl) ⟨5886, by rfl⟩ : syracuseStep 4018517 = 11773) (by norm_num)
theorem B3010925 : Blo 1784093 3010925 := bbase (se 3 (by rfl) ⟨564548, by rfl⟩ : syracuseStep 3010925 = 1129097) (by norm_num)
theorem B10301813 : Blo 1784093 10301813 := bbase (se 5 (by rfl) ⟨482897, by rfl⟩ : syracuseStep 10301813 = 965795) (by norm_num)
theorem B6025589 : Blo 1784093 6025589 := bbase (se 5 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 6025589 = 564899) (by norm_num)
theorem B3215749 : Blo 1784093 3215749 := bbase (se 4 (by rfl) ⟨301476, by rfl⟩ : syracuseStep 3215749 = 602953) (by norm_num)
theorem B4518301 : Blo 1784093 4518301 := bbase (se 3 (by rfl) ⟨847181, by rfl⟩ : syracuseStep 4518301 = 1694363) (by norm_num)
theorem B4018589 : Blo 1784093 4018589 := bbase (se 3 (by rfl) ⟨753485, by rfl⟩ : syracuseStep 4018589 = 1506971) (by norm_num)
theorem B3813821 : Blo 1784093 3813821 := bbase (se 3 (by rfl) ⟨715091, by rfl⟩ : syracuseStep 3813821 = 1430183) (by norm_num)
theorem B3387845 : Blo 1784093 3387845 := bbase (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) (by norm_num)
theorem B4018661 : Blo 1784093 4018661 := bbase (se 4 (by rfl) ⟨376749, by rfl⟩ : syracuseStep 4018661 = 753499) (by norm_num)
theorem B3011053 : Blo 1784093 3011053 := bbase (se 3 (by rfl) ⟨564572, by rfl⟩ : syracuseStep 3011053 = 1129145) (by norm_num)
theorem B4518413 : Blo 1784093 4518413 := bbase (se 3 (by rfl) ⟨847202, by rfl⟩ : syracuseStep 4518413 = 1694405) (by norm_num)
theorem B10850869 : Blo 1784093 10850869 := bbase (se 5 (by rfl) ⟨508634, by rfl⟩ : syracuseStep 10850869 = 1017269) (by norm_num)
theorem B3813941 : Blo 1784093 3813941 := bbase (se 5 (by rfl) ⟨178778, by rfl⟩ : syracuseStep 3813941 = 357557) (by norm_num)
theorem B3011141 : Blo 1784093 3011141 := bbase (se 4 (by rfl) ⟨282294, by rfl⟩ : syracuseStep 3011141 = 564589) (by norm_num)
theorem B65172053 : Blo 1784093 65172053 := bbase (se 8 (by rfl) ⟨381867, by rfl⟩ : syracuseStep 65172053 = 763735) (by norm_num)
theorem B3387997 : Blo 1784093 3387997 := bbase (se 3 (by rfl) ⟨635249, by rfl⟩ : syracuseStep 3387997 = 1270499) (by norm_num)
theorem B4289117 : Blo 1784093 4289117 := bbase (se 3 (by rfl) ⟨804209, by rfl⟩ : syracuseStep 4289117 = 1608419) (by norm_num)
theorem B9032309 : Blo 1784093 9032309 := bbase (se 5 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 9032309 = 846779) (by norm_num)
theorem B3011269 : Blo 1784093 3011269 := bbase (se 4 (by rfl) ⟨282306, by rfl⟩ : syracuseStep 3011269 = 564613) (by norm_num)
theorem B4518605 : Blo 1784093 4518605 := bbase (se 3 (by rfl) ⟨847238, by rfl⟩ : syracuseStep 4518605 = 1694477) (by norm_num)
theorem B2413261 : Blo 1784093 2413261 := bbase (se 3 (by rfl) ⟨452486, by rfl⟩ : syracuseStep 2413261 = 904973) (by norm_num)
theorem B1905373 : Blo 1784093 1905373 := bbase (se 3 (by rfl) ⟨357257, by rfl⟩ : syracuseStep 1905373 = 714515) (by norm_num)
theorem B21721877 : Blo 1784093 21721877 := bbase (se 6 (by rfl) ⟨509106, by rfl⟩ : syracuseStep 21721877 = 1018213) (by norm_num)
theorem B3011357 : Blo 1784093 3011357 := bbase (se 3 (by rfl) ⟨564629, by rfl⟩ : syracuseStep 3011357 = 1129259) (by norm_num)
theorem B6026021 : Blo 1784093 6026021 := bbase (se 4 (by rfl) ⟨564939, by rfl⟩ : syracuseStep 6026021 = 1129879) (by norm_num)
theorem B8581925 : Blo 1784093 8581925 := bbase (se 4 (by rfl) ⟨804555, by rfl⟩ : syracuseStep 8581925 = 1609111) (by norm_num)
theorem B9646901 : Blo 1784093 9646901 := bbase (se 5 (by rfl) ⟨452198, by rfl⟩ : syracuseStep 9646901 = 904397) (by norm_num)
theorem B4289357 : Blo 1784093 4289357 := bbase (se 3 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 4289357 = 1608509) (by norm_num)
theorem B2036605 : Blo 1784093 2036605 := bbase (se 3 (by rfl) ⟨381863, by rfl⟩ : syracuseStep 2036605 = 763727) (by norm_num)
theorem B8582021 : Blo 1784093 8582021 := bbase (se 4 (by rfl) ⟨804564, by rfl⟩ : syracuseStep 8582021 = 1609129) (by norm_num)
theorem B3388301 : Blo 1784093 3388301 := bbase (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) (by norm_num)
theorem B3216269 : Blo 1784093 3216269 := bbase (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) (by norm_num)
theorem B7238549 : Blo 1784093 7238549 := bbase (se 6 (by rfl) ⟨169653, by rfl⟩ : syracuseStep 7238549 = 339307) (by norm_num)
theorem B3011485 : Blo 1784093 3011485 := bbase (se 3 (by rfl) ⟨564653, by rfl⟩ : syracuseStep 3011485 = 1129307) (by norm_num)
theorem B9286613 : Blo 1784093 9286613 := bbase (se 7 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 9286613 = 217655) (by norm_num)
theorem B3011573 : Blo 1784093 3011573 := bbase (se 5 (by rfl) ⟨141167, by rfl⟩ : syracuseStep 3011573 = 282335) (by norm_num)
theorem B4518949 : Blo 1784093 4518949 := bbase (se 4 (by rfl) ⟨423651, by rfl⟩ : syracuseStep 4518949 = 847303) (by norm_num)
theorem B3011701 : Blo 1784093 3011701 := bbase (se 5 (by rfl) ⟨141173, by rfl⟩ : syracuseStep 3011701 = 282347) (by norm_num)
theorem B2258057 : Blo 1784093 2258057 := bbase (se 2 (by rfl) ⟨846771, by rfl⟩ : syracuseStep 2258057 = 1693543) (by norm_num)
theorem B3093653 : Blo 1784093 3093653 := bbase (se 6 (by rfl) ⟨72507, by rfl⟩ : syracuseStep 3093653 = 145015) (by norm_num)
theorem B4519061 : Blo 1784093 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B1905817 : Blo 1784093 1905817 := bbase (se 2 (by rfl) ⟨714681, by rfl⟩ : syracuseStep 1905817 = 1429363) (by norm_num)
theorem B5084309 : Blo 1784093 5084309 := bbase (se 6 (by rfl) ⟨119163, by rfl⟩ : syracuseStep 5084309 = 238327) (by norm_num)
theorem B3814573 : Blo 1784093 3814573 := bbase (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) (by norm_num)
theorem B2258113 : Blo 1784093 2258113 := bbase (se 2 (by rfl) ⟨846792, by rfl⟩ : syracuseStep 2258113 = 1693585) (by norm_num)
theorem B3011789 : Blo 1784093 3011789 := bbase (se 3 (by rfl) ⟨564710, by rfl⟩ : syracuseStep 3011789 = 1129421) (by norm_num)
theorem B1905877 : Blo 1784093 1905877 := bbase (se 7 (by rfl) ⟨22334, by rfl⟩ : syracuseStep 1905877 = 44669) (by norm_num)
theorem B6026453 : Blo 1784093 6026453 := bbase (se 7 (by rfl) ⟨70622, by rfl⟩ : syracuseStep 6026453 = 141245) (by norm_num)
theorem B3216629 : Blo 1784093 3216629 := bbase (se 5 (by rfl) ⟨150779, by rfl⟩ : syracuseStep 3216629 = 301559) (by norm_num)
theorem B6190357 : Blo 1784093 6190357 := bbase (se 6 (by rfl) ⟨145086, by rfl⟩ : syracuseStep 6190357 = 290173) (by norm_num)
theorem B2258209 : Blo 1784093 2258209 := bbase (se 2 (by rfl) ⟨846828, by rfl⟩ : syracuseStep 2258209 = 1693657) (by norm_num)
theorem B8140085 : Blo 1784093 8140085 := bbase (se 5 (by rfl) ⟨381566, by rfl⟩ : syracuseStep 8140085 = 763133) (by norm_num)
theorem B3011917 : Blo 1784093 3011917 := bbase (se 3 (by rfl) ⟨564734, by rfl⟩ : syracuseStep 3011917 = 1129469) (by norm_num)
theorem B4519253 : Blo 1784093 4519253 := bbase (se 13 (by rfl) ⟨827, by rfl⟩ : syracuseStep 4519253 = 1655) (by norm_num)
theorem B6780293 : Blo 1784093 6780293 := bbase (se 4 (by rfl) ⟨635652, by rfl⟩ : syracuseStep 6780293 = 1271305) (by norm_num)
theorem B3216781 : Blo 1784093 3216781 := bbase (se 3 (by rfl) ⟨603146, by rfl⟩ : syracuseStep 3216781 = 1206293) (by norm_num)
theorem B3012005 : Blo 1784093 3012005 := bbase (se 4 (by rfl) ⟨282375, by rfl⟩ : syracuseStep 3012005 = 564751) (by norm_num)
theorem B2676149 : Blo 1784093 2676149 := bbase (se 5 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 2676149 = 250889) (by norm_num)
theorem B2676173 : Blo 1784093 2676173 := bbase (se 3 (by rfl) ⟨501782, by rfl⟩ : syracuseStep 2676173 = 1003565) (by norm_num)
theorem B2258381 : Blo 1784093 2258381 := bbase (se 3 (by rfl) ⟨423446, by rfl⟩ : syracuseStep 2258381 = 846893) (by norm_num)
theorem B2676197 : Blo 1784093 2676197 := bbase (se 4 (by rfl) ⟨250893, by rfl⟩ : syracuseStep 2676197 = 501787) (by norm_num)
theorem B9041381 : Blo 1784093 9041381 := bbase (se 4 (by rfl) ⟨847629, by rfl⟩ : syracuseStep 9041381 = 1695259) (by norm_num)
theorem B2676221 : Blo 1784093 2676221 := bbase (se 3 (by rfl) ⟨501791, by rfl⟩ : syracuseStep 2676221 = 1003583) (by norm_num)
theorem B2258437 : Blo 1784093 2258437 := bbase (se 4 (by rfl) ⟨211728, by rfl⟩ : syracuseStep 2258437 = 423457) (by norm_num)
theorem B1906193 : Blo 1784093 1906193 := bbase (se 2 (by rfl) ⟨714822, by rfl⟩ : syracuseStep 1906193 = 1429645) (by norm_num)
theorem B2676245 : Blo 1784093 2676245 := bbase (se 6 (by rfl) ⟨62724, by rfl⟩ : syracuseStep 2676245 = 125449) (by norm_num)
theorem B3012133 : Blo 1784093 3012133 := bbase (se 4 (by rfl) ⟨282387, by rfl⟩ : syracuseStep 3012133 = 564775) (by norm_num)
theorem B2676269 : Blo 1784093 2676269 := bbase (se 3 (by rfl) ⟨501800, by rfl⟩ : syracuseStep 2676269 = 1003601) (by norm_num)
theorem B2676293 : Blo 1784093 2676293 := bbase (se 4 (by rfl) ⟨250902, by rfl⟩ : syracuseStep 2676293 = 501805) (by norm_num)
theorem B7624277 : Blo 1784093 7624277 := bbase (se 8 (by rfl) ⟨44673, by rfl⟩ : syracuseStep 7624277 = 89347) (by norm_num)
theorem B2676317 : Blo 1784093 2676317 := bbase (se 3 (by rfl) ⟨501809, by rfl⟩ : syracuseStep 2676317 = 1003619) (by norm_num)
theorem B2258533 : Blo 1784093 2258533 := bbase (se 4 (by rfl) ⟨211737, by rfl⟩ : syracuseStep 2258533 = 423475) (by norm_num)
theorem B2676341 : Blo 1784093 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B3012221 : Blo 1784093 3012221 := bbase (se 3 (by rfl) ⟨564791, by rfl⟩ : syracuseStep 3012221 = 1129583) (by norm_num)
theorem B3389053 : Blo 1784093 3389053 := bbase (se 3 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 3389053 = 1270895) (by norm_num)
theorem B6026885 : Blo 1784093 6026885 := bbase (se 4 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 6026885 = 1130041) (by norm_num)
theorem B2676365 : Blo 1784093 2676365 := bbase (se 3 (by rfl) ⟨501818, by rfl⟩ : syracuseStep 2676365 = 1003637) (by norm_num)
theorem B2676389 : Blo 1784093 2676389 := bbase (se 4 (by rfl) ⟨250911, by rfl⟩ : syracuseStep 2676389 = 501823) (by norm_num)
theorem B6780581 : Blo 1784093 6780581 := bbase (se 4 (by rfl) ⟨635679, by rfl⟩ : syracuseStep 6780581 = 1271359) (by norm_num)
theorem B4519597 : Blo 1784093 4519597 := bbase (se 3 (by rfl) ⟨847424, by rfl⟩ : syracuseStep 4519597 = 1694849) (by norm_num)
theorem B2676413 : Blo 1784093 2676413 := bbase (se 3 (by rfl) ⟨501827, by rfl⟩ : syracuseStep 2676413 = 1003655) (by norm_num)
theorem B2676437 : Blo 1784093 2676437 := bbase (se 7 (by rfl) ⟨31364, by rfl⟩ : syracuseStep 2676437 = 62729) (by norm_num)
theorem B2676461 : Blo 1784093 2676461 := bbase (se 3 (by rfl) ⟨501836, by rfl⟩ : syracuseStep 2676461 = 1003673) (by norm_num)
theorem B3012349 : Blo 1784093 3012349 := bbase (se 3 (by rfl) ⟨564815, by rfl⟩ : syracuseStep 3012349 = 1129631) (by norm_num)
theorem B2676485 : Blo 1784093 2676485 := bbase (se 4 (by rfl) ⟨250920, by rfl⟩ : syracuseStep 2676485 = 501841) (by norm_num)
theorem B3389197 : Blo 1784093 3389197 := bbase (se 3 (by rfl) ⟨635474, by rfl⟩ : syracuseStep 3389197 = 1270949) (by norm_num)
theorem B2258705 : Blo 1784093 2258705 := bbase (se 2 (by rfl) ⟨847014, by rfl⟩ : syracuseStep 2258705 = 1694029) (by norm_num)
theorem B2676509 : Blo 1784093 2676509 := bbase (se 3 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 2676509 = 1003691) (by norm_num)
theorem B4519709 : Blo 1784093 4519709 := bbase (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) (by norm_num)
theorem B2676533 : Blo 1784093 2676533 := bbase (se 5 (by rfl) ⟨125462, by rfl⟩ : syracuseStep 2676533 = 250925) (by norm_num)
theorem B5084981 : Blo 1784093 5084981 := bbase (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) (by norm_num)
theorem B2258761 : Blo 1784093 2258761 := bbase (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) (by norm_num)
theorem B2676557 : Blo 1784093 2676557 := bbase (se 3 (by rfl) ⟨501854, by rfl⟩ : syracuseStep 2676557 = 1003709) (by norm_num)
theorem B3012437 : Blo 1784093 3012437 := bbase (se 9 (by rfl) ⟨8825, by rfl⟩ : syracuseStep 3012437 = 17651) (by norm_num)
theorem B2676581 : Blo 1784093 2676581 := bbase (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) (by norm_num)
theorem B2676605 : Blo 1784093 2676605 := bbase (se 3 (by rfl) ⟨501863, by rfl⟩ : syracuseStep 2676605 = 1003727) (by norm_num)
theorem B9033605 : Blo 1784093 9033605 := bbase (se 4 (by rfl) ⟨846900, by rfl⟩ : syracuseStep 9033605 = 1693801) (by norm_num)
theorem B2676629 : Blo 1784093 2676629 := bbase (se 6 (by rfl) ⟨62733, by rfl⟩ : syracuseStep 2676629 = 125467) (by norm_num)
theorem B3094429 : Blo 1784093 3094429 := bbase (se 3 (by rfl) ⟨580205, by rfl⟩ : syracuseStep 3094429 = 1160411) (by norm_num)
theorem B2258857 : Blo 1784093 2258857 := bbase (se 2 (by rfl) ⟨847071, by rfl⟩ : syracuseStep 2258857 = 1694143) (by norm_num)
theorem B2676653 : Blo 1784093 2676653 := bbase (se 3 (by rfl) ⟨501872, by rfl⟩ : syracuseStep 2676653 = 1003745) (by norm_num)
theorem B3389357 : Blo 1784093 3389357 := bbase (se 3 (by rfl) ⟨635504, by rfl⟩ : syracuseStep 3389357 = 1271009) (by norm_num)
theorem B2676677 : Blo 1784093 2676677 := bbase (se 4 (by rfl) ⟨250938, by rfl⟩ : syracuseStep 2676677 = 501877) (by norm_num)
theorem B1906637 : Blo 1784093 1906637 := bbase (se 3 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 1906637 = 714989) (by norm_num)
theorem B3012565 : Blo 1784093 3012565 := bbase (se 7 (by rfl) ⟨35303, by rfl⟩ : syracuseStep 3012565 = 70607) (by norm_num)
theorem B2676701 : Blo 1784093 2676701 := bbase (se 3 (by rfl) ⟨501881, by rfl⟩ : syracuseStep 2676701 = 1003763) (by norm_num)
theorem B4519901 : Blo 1784093 4519901 := bbase (se 3 (by rfl) ⟨847481, by rfl⟩ : syracuseStep 4519901 = 1694963) (by norm_num)
theorem B2676725 : Blo 1784093 2676725 := bbase (se 5 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 2676725 = 250943) (by norm_num)
theorem B1906697 : Blo 1784093 1906697 := bbase (se 2 (by rfl) ⟨715011, by rfl⟩ : syracuseStep 1906697 = 1430023) (by norm_num)
theorem B2676749 : Blo 1784093 2676749 := bbase (se 3 (by rfl) ⟨501890, by rfl⟩ : syracuseStep 2676749 = 1003781) (by norm_num)
theorem B2676773 : Blo 1784093 2676773 := bbase (se 4 (by rfl) ⟨250947, by rfl⟩ : syracuseStep 2676773 = 501895) (by norm_num)
theorem B3012653 : Blo 1784093 3012653 := bbase (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) (by norm_num)
theorem B6027317 : Blo 1784093 6027317 := bbase (se 5 (by rfl) ⟨282530, by rfl⟩ : syracuseStep 6027317 = 565061) (by norm_num)
theorem B2676797 : Blo 1784093 2676797 := bbase (se 3 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 2676797 = 1003799) (by norm_num)
theorem B3389501 : Blo 1784093 3389501 := bbase (se 3 (by rfl) ⟨635531, by rfl⟩ : syracuseStep 3389501 = 1271063) (by norm_num)
theorem B2676821 : Blo 1784093 2676821 := bbase (se 8 (by rfl) ⟨15684, by rfl⟩ : syracuseStep 2676821 = 31369) (by norm_num)
theorem B2259029 : Blo 1784093 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B2676845 : Blo 1784093 2676845 := bbase (se 3 (by rfl) ⟨501908, by rfl⟩ : syracuseStep 2676845 = 1003817) (by norm_num)
theorem B2676869 : Blo 1784093 2676869 := bbase (se 4 (by rfl) ⟨250956, by rfl⟩ : syracuseStep 2676869 = 501913) (by norm_num)
theorem B2119817 : Blo 1784093 2119817 := bbase (se 2 (by rfl) ⟨794931, by rfl⟩ : syracuseStep 2119817 = 1589863) (by norm_num)
theorem B2259085 : Blo 1784093 2259085 := bbase (se 3 (by rfl) ⟨423578, by rfl⟩ : syracuseStep 2259085 = 847157) (by norm_num)
theorem B1906825 : Blo 1784093 1906825 := bbase (se 2 (by rfl) ⟨715059, by rfl⟩ : syracuseStep 1906825 = 1430119) (by norm_num)
theorem B2144405 : Blo 1784093 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B2676893 : Blo 1784093 2676893 := bbase (se 3 (by rfl) ⟨501917, by rfl⟩ : syracuseStep 2676893 = 1003835) (by norm_num)
theorem B3012781 : Blo 1784093 3012781 := bbase (se 3 (by rfl) ⟨564896, by rfl⟩ : syracuseStep 3012781 = 1129793) (by norm_num)
theorem B2676917 : Blo 1784093 2676917 := bbase (se 5 (by rfl) ⟨125480, by rfl⟩ : syracuseStep 2676917 = 250961) (by norm_num)
theorem B2676941 : Blo 1784093 2676941 := bbase (se 3 (by rfl) ⟨501926, by rfl⟩ : syracuseStep 2676941 = 1003853) (by norm_num)
theorem B2676965 : Blo 1784093 2676965 := bbase (se 4 (by rfl) ⟨250965, by rfl⟩ : syracuseStep 2676965 = 501931) (by norm_num)
theorem B5085413 : Blo 1784093 5085413 := bbase (se 4 (by rfl) ⟨476757, by rfl⟩ : syracuseStep 5085413 = 953515) (by norm_num)
theorem B2259181 : Blo 1784093 2259181 := bbase (se 3 (by rfl) ⟨423596, by rfl⟩ : syracuseStep 2259181 = 847193) (by norm_num)
theorem B2676989 : Blo 1784093 2676989 := bbase (se 3 (by rfl) ⟨501935, by rfl⟩ : syracuseStep 2676989 = 1003871) (by norm_num)
theorem B3012869 : Blo 1784093 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B6109445 : Blo 1784093 6109445 := bbase (se 4 (by rfl) ⟨572760, by rfl⟩ : syracuseStep 6109445 = 1145521) (by norm_num)
theorem B2677013 : Blo 1784093 2677013 := bbase (se 6 (by rfl) ⟨62742, by rfl⟩ : syracuseStep 2677013 = 125485) (by norm_num)
theorem B9156901 : Blo 1784093 9156901 := bbase (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) (by norm_num)
theorem B2677037 : Blo 1784093 2677037 := bbase (se 3 (by rfl) ⟨501944, by rfl⟩ : syracuseStep 2677037 = 1003889) (by norm_num)
theorem B4520245 : Blo 1784093 4520245 := bbase (se 5 (by rfl) ⟨211886, by rfl⟩ : syracuseStep 4520245 = 423773) (by norm_num)
theorem B2677061 : Blo 1784093 2677061 := bbase (se 4 (by rfl) ⟨250974, by rfl⟩ : syracuseStep 2677061 = 501949) (by norm_num)
theorem B2677085 : Blo 1784093 2677085 := bbase (se 3 (by rfl) ⟨501953, by rfl⟩ : syracuseStep 2677085 = 1003907) (by norm_num)
theorem B3389789 : Blo 1784093 3389789 := bbase (se 3 (by rfl) ⟨635585, by rfl⟩ : syracuseStep 3389789 = 1271171) (by norm_num)
theorem B2677109 : Blo 1784093 2677109 := bbase (se 5 (by rfl) ⟨125489, by rfl⟩ : syracuseStep 2677109 = 250979) (by norm_num)
theorem B3012997 : Blo 1784093 3012997 := bbase (se 4 (by rfl) ⟨282468, by rfl⟩ : syracuseStep 3012997 = 564937) (by norm_num)
theorem B2677133 : Blo 1784093 2677133 := bbase (se 3 (by rfl) ⟨501962, by rfl⟩ : syracuseStep 2677133 = 1003925) (by norm_num)
theorem B5151125 : Blo 1784093 5151125 := bbase (se 6 (by rfl) ⟨120729, by rfl⟩ : syracuseStep 5151125 = 241459) (by norm_num)
theorem B10164629 : Blo 1784093 10164629 := bbase (se 6 (by rfl) ⟨238233, by rfl⟩ : syracuseStep 10164629 = 476467) (by norm_num)
theorem B2259353 : Blo 1784093 2259353 := bbase (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) (by norm_num)
theorem B2677157 : Blo 1784093 2677157 := bbase (se 4 (by rfl) ⟨250983, by rfl⟩ : syracuseStep 2677157 = 501967) (by norm_num)
theorem B4520357 : Blo 1784093 4520357 := bbase (se 4 (by rfl) ⟨423783, by rfl⟩ : syracuseStep 4520357 = 847567) (by norm_num)
theorem B2677181 : Blo 1784093 2677181 := bbase (se 3 (by rfl) ⟨501971, by rfl⟩ : syracuseStep 2677181 = 1003943) (by norm_num)
theorem B2144713 : Blo 1784093 2144713 := bbase (se 2 (by rfl) ⟨804267, by rfl⟩ : syracuseStep 2144713 = 1608535) (by norm_num)
theorem B2259409 : Blo 1784093 2259409 := bbase (se 2 (by rfl) ⟨847278, by rfl⟩ : syracuseStep 2259409 = 1694557) (by norm_num)
theorem B2677205 : Blo 1784093 2677205 := bbase (se 7 (by rfl) ⟨31373, by rfl⟩ : syracuseStep 2677205 = 62747) (by norm_num)
theorem B3217877 : Blo 1784093 3217877 := bbase (se 7 (by rfl) ⟨37709, by rfl⟩ : syracuseStep 3217877 = 75419) (by norm_num)
theorem B3013085 : Blo 1784093 3013085 := bbase (se 3 (by rfl) ⟨564953, by rfl⟩ : syracuseStep 3013085 = 1129907) (by norm_num)
theorem B6027749 : Blo 1784093 6027749 := bbase (se 4 (by rfl) ⟨565101, by rfl⟩ : syracuseStep 6027749 = 1130203) (by norm_num)
theorem B2677229 : Blo 1784093 2677229 := bbase (se 3 (by rfl) ⟨501980, by rfl⟩ : syracuseStep 2677229 = 1003961) (by norm_num)
theorem B3389941 : Blo 1784093 3389941 := bbase (se 5 (by rfl) ⟨158903, by rfl⟩ : syracuseStep 3389941 = 317807) (by norm_num)
theorem B4291069 : Blo 1784093 4291069 := bbase (se 3 (by rfl) ⟨804575, by rfl⟩ : syracuseStep 4291069 = 1609151) (by norm_num)
theorem B2677253 : Blo 1784093 2677253 := bbase (se 4 (by rfl) ⟨250992, by rfl⟩ : syracuseStep 2677253 = 501985) (by norm_num)
theorem B2677277 : Blo 1784093 2677277 := bbase (se 3 (by rfl) ⟨501989, by rfl⟩ : syracuseStep 2677277 = 1003979) (by norm_num)
theorem B2144813 : Blo 1784093 2144813 := bbase (se 3 (by rfl) ⟨402152, by rfl⟩ : syracuseStep 2144813 = 804305) (by norm_num)
theorem B2259505 : Blo 1784093 2259505 := bbase (se 2 (by rfl) ⟨847314, by rfl⟩ : syracuseStep 2259505 = 1694629) (by norm_num)
theorem B2677301 : Blo 1784093 2677301 := bbase (se 5 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 2677301 = 250997) (by norm_num)
theorem B7625285 : Blo 1784093 7625285 := bbase (se 4 (by rfl) ⟨714870, by rfl⟩ : syracuseStep 7625285 = 1429741) (by norm_num)
theorem B1907269 : Blo 1784093 1907269 := bbase (se 4 (by rfl) ⟨178806, by rfl⟩ : syracuseStep 1907269 = 357613) (by norm_num)
theorem B2677325 : Blo 1784093 2677325 := bbase (se 3 (by rfl) ⟨501998, by rfl⟩ : syracuseStep 2677325 = 1003997) (by norm_num)
theorem B26434133 : Blo 1784093 26434133 := bbase (se 8 (by rfl) ⟨154887, by rfl⟩ : syracuseStep 26434133 = 309775) (by norm_num)
theorem B3013213 : Blo 1784093 3013213 := bbase (se 3 (by rfl) ⟨564977, by rfl⟩ : syracuseStep 3013213 = 1129955) (by norm_num)
theorem B2677349 : Blo 1784093 2677349 := bbase (se 4 (by rfl) ⟨251001, by rfl⟩ : syracuseStep 2677349 = 502003) (by norm_num)
theorem B4520549 : Blo 1784093 4520549 := bbase (se 4 (by rfl) ⟨423801, by rfl⟩ : syracuseStep 4520549 = 847603) (by norm_num)
theorem B2677373 : Blo 1784093 2677373 := bbase (se 3 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 2677373 = 1004015) (by norm_num)
theorem B8575637 : Blo 1784093 8575637 := bbase (se 6 (by rfl) ⟨200991, by rfl⟩ : syracuseStep 8575637 = 401983) (by norm_num)
theorem B2677397 : Blo 1784093 2677397 := bbase (se 6 (by rfl) ⟨62751, by rfl⟩ : syracuseStep 2677397 = 125503) (by norm_num)
theorem B3054229 : Blo 1784093 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B2677421 : Blo 1784093 2677421 := bbase (se 3 (by rfl) ⟨502016, by rfl⟩ : syracuseStep 2677421 = 1004033) (by norm_num)
theorem B3013301 : Blo 1784093 3013301 := bbase (se 5 (by rfl) ⟨141248, by rfl⟩ : syracuseStep 3013301 = 282497) (by norm_num)
theorem B2677445 : Blo 1784093 2677445 := bbase (se 4 (by rfl) ⟨251010, by rfl⟩ : syracuseStep 2677445 = 502021) (by norm_num)
theorem B2677469 : Blo 1784093 2677469 := bbase (se 3 (by rfl) ⟨502025, by rfl⟩ : syracuseStep 2677469 = 1004051) (by norm_num)
theorem B2259677 : Blo 1784093 2259677 := bbase (se 3 (by rfl) ⟨423689, by rfl⟩ : syracuseStep 2259677 = 847379) (by norm_num)
theorem B2677493 : Blo 1784093 2677493 := bbase (se 5 (by rfl) ⟨125507, by rfl⟩ : syracuseStep 2677493 = 251015) (by norm_num)
theorem B2677517 : Blo 1784093 2677517 := bbase (se 3 (by rfl) ⟨502034, by rfl⟩ : syracuseStep 2677517 = 1004069) (by norm_num)
theorem B2259733 : Blo 1784093 2259733 := bbase (se 6 (by rfl) ⟨52962, by rfl⟩ : syracuseStep 2259733 = 105925) (by norm_num)
theorem B2677541 : Blo 1784093 2677541 := bbase (se 4 (by rfl) ⟨251019, by rfl⟩ : syracuseStep 2677541 = 502039) (by norm_num)
theorem B3390245 : Blo 1784093 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B3013429 : Blo 1784093 3013429 := bbase (se 5 (by rfl) ⟨141254, by rfl⟩ : syracuseStep 3013429 = 282509) (by norm_num)
theorem B2677565 : Blo 1784093 2677565 := bbase (se 3 (by rfl) ⟨502043, by rfl⟩ : syracuseStep 2677565 = 1004087) (by norm_num)
theorem B2677589 : Blo 1784093 2677589 := bbase (se 9 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 2677589 = 15689) (by norm_num)
theorem B2677613 : Blo 1784093 2677613 := bbase (se 3 (by rfl) ⟨502052, by rfl⟩ : syracuseStep 2677613 = 1004105) (by norm_num)
theorem B2259829 : Blo 1784093 2259829 := bbase (se 5 (by rfl) ⟨105929, by rfl⟩ : syracuseStep 2259829 = 211859) (by norm_num)
theorem B11598709 : Blo 1784093 11598709 := bbase (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) (by norm_num)
theorem B2202493 : Blo 1784093 2202493 := bbase (se 3 (by rfl) ⟨412967, by rfl⟩ : syracuseStep 2202493 = 825935) (by norm_num)
theorem B2677637 : Blo 1784093 2677637 := bbase (se 4 (by rfl) ⟨251028, by rfl⟩ : syracuseStep 2677637 = 502057) (by norm_num)
theorem B1809289 : Blo 1784093 1809289 := bbase (se 2 (by rfl) ⟨678483, by rfl⟩ : syracuseStep 1809289 = 1356967) (by norm_num)
theorem B3013517 : Blo 1784093 3013517 := bbase (se 3 (by rfl) ⟨565034, by rfl⟩ : syracuseStep 3013517 = 1130069) (by norm_num)
theorem B2677661 : Blo 1784093 2677661 := bbase (se 3 (by rfl) ⟨502061, by rfl⟩ : syracuseStep 2677661 = 1004123) (by norm_num)
theorem B2677685 : Blo 1784093 2677685 := bbase (se 5 (by rfl) ⟨125516, by rfl⟩ : syracuseStep 2677685 = 251033) (by norm_num)
theorem B4520893 : Blo 1784093 4520893 := bbase (se 3 (by rfl) ⟨847667, by rfl⟩ : syracuseStep 4520893 = 1695335) (by norm_num)
theorem B2145217 : Blo 1784093 2145217 := bbase (se 2 (by rfl) ⟨804456, by rfl⟩ : syracuseStep 2145217 = 1608913) (by norm_num)
theorem B2677709 : Blo 1784093 2677709 := bbase (se 3 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 2677709 = 1004141) (by norm_num)
theorem B5086165 : Blo 1784093 5086165 := bbase (se 7 (by rfl) ⟨59603, by rfl⟩ : syracuseStep 5086165 = 119207) (by norm_num)
theorem B2677733 : Blo 1784093 2677733 := bbase (se 4 (by rfl) ⟨251037, by rfl⟩ : syracuseStep 2677733 = 502075) (by norm_num)
theorem B2677757 : Blo 1784093 2677757 := bbase (se 3 (by rfl) ⟨502079, by rfl⟩ : syracuseStep 2677757 = 1004159) (by norm_num)
theorem B3013645 : Blo 1784093 3013645 := bbase (se 3 (by rfl) ⟨565058, by rfl⟩ : syracuseStep 3013645 = 1130117) (by norm_num)
theorem B28949525 : Blo 1784093 28949525 := bbase (se 6 (by rfl) ⟨678504, by rfl⟩ : syracuseStep 28949525 = 1357009) (by norm_num)
theorem B2677781 : Blo 1784093 2677781 := bbase (se 6 (by rfl) ⟨62760, by rfl⟩ : syracuseStep 2677781 = 125521) (by norm_num)
theorem B2260001 : Blo 1784093 2260001 := bbase (se 2 (by rfl) ⟨847500, by rfl⟩ : syracuseStep 2260001 = 1695001) (by norm_num)
theorem B2677805 : Blo 1784093 2677805 := bbase (se 3 (by rfl) ⟨502088, by rfl⟩ : syracuseStep 2677805 = 1004177) (by norm_num)
theorem B4521005 : Blo 1784093 4521005 := bbase (se 3 (by rfl) ⟨847688, by rfl⟩ : syracuseStep 4521005 = 1695377) (by norm_num)
theorem B2677829 : Blo 1784093 2677829 := bbase (se 4 (by rfl) ⟨251046, by rfl⟩ : syracuseStep 2677829 = 502093) (by norm_num)
theorem B2260057 : Blo 1784093 2260057 := bbase (se 2 (by rfl) ⟨847521, by rfl⟩ : syracuseStep 2260057 = 1695043) (by norm_num)
theorem B2677853 : Blo 1784093 2677853 := bbase (se 3 (by rfl) ⟨502097, by rfl⟩ : syracuseStep 2677853 = 1004195) (by norm_num)
theorem B3013733 : Blo 1784093 3013733 := bbase (se 4 (by rfl) ⟨282537, by rfl⟩ : syracuseStep 3013733 = 565075) (by norm_num)
theorem B2677877 : Blo 1784093 2677877 := bbase (se 5 (by rfl) ⟨125525, by rfl⟩ : syracuseStep 2677877 = 251051) (by norm_num)
theorem B2677901 : Blo 1784093 2677901 := bbase (se 3 (by rfl) ⟨502106, by rfl⟩ : syracuseStep 2677901 = 1004213) (by norm_num)
theorem B9034901 : Blo 1784093 9034901 := bbase (se 6 (by rfl) ⟨211755, by rfl⟩ : syracuseStep 9034901 = 423511) (by norm_num)
theorem B2677925 : Blo 1784093 2677925 := bbase (se 4 (by rfl) ⟨251055, by rfl⟩ : syracuseStep 2677925 = 502111) (by norm_num)
theorem B2260153 : Blo 1784093 2260153 := bbase (se 2 (by rfl) ⟨847557, by rfl⟩ : syracuseStep 2260153 = 1695115) (by norm_num)
theorem B2677949 : Blo 1784093 2677949 := bbase (se 3 (by rfl) ⟨502115, by rfl⟩ : syracuseStep 2677949 = 1004231) (by norm_num)
theorem B1809605 : Blo 1784093 1809605 := bbase (se 4 (by rfl) ⟨169650, by rfl⟩ : syracuseStep 1809605 = 339301) (by norm_num)
theorem B2677973 : Blo 1784093 2677973 := bbase (se 7 (by rfl) ⟨31382, by rfl⟩ : syracuseStep 2677973 = 62765) (by norm_num)
theorem B6773989 : Blo 1784093 6773989 := bbase (se 4 (by rfl) ⟨635061, by rfl⟩ : syracuseStep 6773989 = 1270123) (by norm_num)
theorem B2858213 : Blo 1784093 2858213 := bbase (se 4 (by rfl) ⟨267957, by rfl⟩ : syracuseStep 2858213 = 535915) (by norm_num)
theorem B3013861 : Blo 1784093 3013861 := bbase (se 4 (by rfl) ⟨282549, by rfl⟩ : syracuseStep 3013861 = 565099) (by norm_num)
theorem B2677997 : Blo 1784093 2677997 := bbase (se 3 (by rfl) ⟨502124, by rfl⟩ : syracuseStep 2677997 = 1004249) (by norm_num)
theorem B6872309 : Blo 1784093 6872309 := bbase (se 5 (by rfl) ⟨322139, by rfl⟩ : syracuseStep 6872309 = 644279) (by norm_num)
theorem B2678021 : Blo 1784093 2678021 := bbase (se 4 (by rfl) ⟨251064, by rfl⟩ : syracuseStep 2678021 = 502129) (by norm_num)
theorem B2678045 : Blo 1784093 2678045 := bbase (se 3 (by rfl) ⟨502133, by rfl⟩ : syracuseStep 2678045 = 1004267) (by norm_num)
theorem B2678069 : Blo 1784093 2678069 := bbase (se 5 (by rfl) ⟨125534, by rfl⟩ : syracuseStep 2678069 = 251069) (by norm_num)
theorem B3013949 : Blo 1784093 3013949 := bbase (se 3 (by rfl) ⟨565115, by rfl⟩ : syracuseStep 3013949 = 1130231) (by norm_num)
theorem B2145601 : Blo 1784093 2145601 := bbase (se 2 (by rfl) ⟨804600, by rfl⟩ : syracuseStep 2145601 = 1609201) (by norm_num)
theorem B2678093 : Blo 1784093 2678093 := bbase (se 3 (by rfl) ⟨502142, by rfl⟩ : syracuseStep 2678093 = 1004285) (by norm_num)
theorem B2678117 : Blo 1784093 2678117 := bbase (se 4 (by rfl) ⟨251073, by rfl⟩ : syracuseStep 2678117 = 502147) (by norm_num)
theorem B2260325 : Blo 1784093 2260325 := bbase (se 4 (by rfl) ⟨211905, by rfl⟩ : syracuseStep 2260325 = 423811) (by norm_num)
theorem B2678141 : Blo 1784093 2678141 := bbase (se 3 (by rfl) ⟨502151, by rfl⟩ : syracuseStep 2678141 = 1004303) (by norm_num)
theorem B11435413 : Blo 1784093 11435413 := bbase (se 6 (by rfl) ⟨268017, by rfl⟩ : syracuseStep 11435413 = 536035) (by norm_num)
theorem B2678165 : Blo 1784093 2678165 := bbase (se 6 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 2678165 = 125539) (by norm_num)
theorem B2260381 : Blo 1784093 2260381 := bbase (se 3 (by rfl) ⟨423821, by rfl⟩ : syracuseStep 2260381 = 847643) (by norm_num)
theorem B2678189 : Blo 1784093 2678189 := bbase (se 3 (by rfl) ⟨502160, by rfl⟩ : syracuseStep 2678189 = 1004321) (by norm_num)
theorem B2678213 : Blo 1784093 2678213 := bbase (se 4 (by rfl) ⟨251082, by rfl⟩ : syracuseStep 2678213 = 502165) (by norm_num)
theorem B15244757 : Blo 1784093 15244757 := bbase (se 7 (by rfl) ⟨178649, by rfl⟩ : syracuseStep 15244757 = 357299) (by norm_num)
theorem B65158613 : Blo 1784093 65158613 := bbase (se 7 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 65158613 = 1527155) (by norm_num)
theorem B2678237 : Blo 1784093 2678237 := bbase (se 3 (by rfl) ⟨502169, by rfl⟩ : syracuseStep 2678237 = 1004339) (by norm_num)
theorem B2678261 : Blo 1784093 2678261 := bbase (se 5 (by rfl) ⟨125543, by rfl⟩ : syracuseStep 2678261 = 251087) (by norm_num)
theorem B2260477 : Blo 1784093 2260477 := bbase (se 3 (by rfl) ⟨423839, by rfl⟩ : syracuseStep 2260477 = 847679) (by norm_num)
theorem B2678285 : Blo 1784093 2678285 := bbase (se 3 (by rfl) ⟨502178, by rfl⟩ : syracuseStep 2678285 = 1004357) (by norm_num)
theorem B6774293 : Blo 1784093 6774293 := bbase (se 6 (by rfl) ⟨158772, by rfl⟩ : syracuseStep 6774293 = 317545) (by norm_num)
theorem B1834525 : Blo 1784093 1834525 := bbase (se 3 (by rfl) ⟨343973, by rfl⟩ : syracuseStep 1834525 = 687947) (by norm_num)
theorem B3055133 : Blo 1784093 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B2678309 : Blo 1784093 2678309 := bbase (se 4 (by rfl) ⟨251091, by rfl⟩ : syracuseStep 2678309 = 502183) (by norm_num)
theorem B2678333 : Blo 1784093 2678333 := bbase (se 3 (by rfl) ⟨502187, by rfl⟩ : syracuseStep 2678333 = 1004375) (by norm_num)
theorem B2678357 : Blo 1784093 2678357 := bbase (se 8 (by rfl) ⟨15693, by rfl⟩ : syracuseStep 2678357 = 31387) (by norm_num)
theorem B2678381 : Blo 1784093 2678381 := bbase (se 3 (by rfl) ⟨502196, by rfl⟩ : syracuseStep 2678381 = 1004393) (by norm_num)
theorem B6872693 : Blo 1784093 6872693 := bbase (se 5 (by rfl) ⟨322157, by rfl⟩ : syracuseStep 6872693 = 644315) (by norm_num)
theorem B2678405 : Blo 1784093 2678405 := bbase (se 4 (by rfl) ⟨251100, by rfl⟩ : syracuseStep 2678405 = 502201) (by norm_num)
theorem B2678429 : Blo 1784093 2678429 := bbase (se 3 (by rfl) ⟨502205, by rfl⟩ : syracuseStep 2678429 = 1004411) (by norm_num)
theorem B2678453 : Blo 1784093 2678453 := bbase (se 5 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 2678453 = 251105) (by norm_num)
theorem B11599541 : Blo 1784093 11599541 := bbase (se 5 (by rfl) ⟨543728, by rfl⟩ : syracuseStep 11599541 = 1087457) (by norm_num)
theorem B2678477 : Blo 1784093 2678477 := bbase (se 3 (by rfl) ⟨502214, by rfl⟩ : syracuseStep 2678477 = 1004429) (by norm_num)
theorem B2678501 : Blo 1784093 2678501 := bbase (se 4 (by rfl) ⟨251109, by rfl⟩ : syracuseStep 2678501 = 502219) (by norm_num)
theorem B2678525 : Blo 1784093 2678525 := bbase (se 3 (by rfl) ⟨502223, by rfl⟩ : syracuseStep 2678525 = 1004447) (by norm_num)
theorem B2678549 : Blo 1784093 2678549 := bbase (se 6 (by rfl) ⟨62778, by rfl⟩ : syracuseStep 2678549 = 125557) (by norm_num)
theorem B4644637 : Blo 1784093 4644637 := bbase (se 3 (by rfl) ⟨870869, by rfl⟩ : syracuseStep 4644637 = 1741739) (by norm_num)
theorem B2678573 : Blo 1784093 2678573 := bbase (se 3 (by rfl) ⟨502232, by rfl⟩ : syracuseStep 2678573 = 1004465) (by norm_num)
theorem B2678597 : Blo 1784093 2678597 := bbase (se 4 (by rfl) ⟨251118, by rfl⟩ : syracuseStep 2678597 = 502237) (by norm_num)
theorem B2678621 : Blo 1784093 2678621 := bbase (se 3 (by rfl) ⟨502241, by rfl⟩ : syracuseStep 2678621 = 1004483) (by norm_num)
theorem B5717861 : Blo 1784093 5717861 := bbase (se 4 (by rfl) ⟨536049, by rfl⟩ : syracuseStep 5717861 = 1072099) (by norm_num)
theorem B5431141 : Blo 1784093 5431141 := bbase (se 4 (by rfl) ⟨509169, by rfl⟩ : syracuseStep 5431141 = 1018339) (by norm_num)
theorem B2678645 : Blo 1784093 2678645 := bbase (se 5 (by rfl) ⟨125561, by rfl⟩ : syracuseStep 2678645 = 251123) (by norm_num)
theorem B2678669 : Blo 1784093 2678669 := bbase (se 3 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 2678669 = 1004501) (by norm_num)
theorem B2678693 : Blo 1784093 2678693 := bbase (se 4 (by rfl) ⟨251127, by rfl⟩ : syracuseStep 2678693 = 502255) (by norm_num)
theorem B2678717 : Blo 1784093 2678717 := bbase (se 3 (by rfl) ⟨502259, by rfl⟩ : syracuseStep 2678717 = 1004519) (by norm_num)
theorem B2678741 : Blo 1784093 2678741 := bbase (se 7 (by rfl) ⟨31391, by rfl⟩ : syracuseStep 2678741 = 62783) (by norm_num)
theorem B2678765 : Blo 1784093 2678765 := bbase (se 3 (by rfl) ⟨502268, by rfl⟩ : syracuseStep 2678765 = 1004537) (by norm_num)
theorem B10878965 : Blo 1784093 10878965 := bbase (se 5 (by rfl) ⟨509951, by rfl⟩ : syracuseStep 10878965 = 1019903) (by norm_num)
theorem B1785859 : Blo 1784093 1785859 := bstep (se 1 (by rfl) ⟨1339394, by rfl⟩ : syracuseStep 1785859 = 2678789) B2678789
theorem B2678801 : Blo 1784093 2678801 := bstep (se 2 (by rfl) ⟨1004550, by rfl⟩ : syracuseStep 2678801 = 2009101) B2009101
theorem B1785875 : Blo 1784093 1785875 := bstep (se 1 (by rfl) ⟨1339406, by rfl⟩ : syracuseStep 1785875 = 2678813) B2678813
theorem B2678819 : Blo 1784093 2678819 := bstep (se 1 (by rfl) ⟨2009114, by rfl⟩ : syracuseStep 2678819 = 4018229) B4018229
theorem B1785891 : Blo 1784093 1785891 := bstep (se 1 (by rfl) ⟨1339418, by rfl⟩ : syracuseStep 1785891 = 2678837) B2678837
theorem B2859059 : Blo 1784093 2859059 := bstep (se 1 (by rfl) ⟨2144294, by rfl⟩ : syracuseStep 2859059 = 4288589) B4288589
theorem B1785907 : Blo 1784093 1785907 := bstep (se 1 (by rfl) ⟨1339430, by rfl⟩ : syracuseStep 1785907 = 2678861) B2678861
theorem B2678849 : Blo 1784093 2678849 := bstep (se 2 (by rfl) ⟨1004568, by rfl⟩ : syracuseStep 2678849 = 2009137) B2009137
theorem B1785923 : Blo 1784093 1785923 := bstep (se 1 (by rfl) ⟨1339442, by rfl⟩ : syracuseStep 1785923 = 2678885) B2678885
theorem B2678867 : Blo 1784093 2678867 := bstep (se 1 (by rfl) ⟨2009150, by rfl⟩ : syracuseStep 2678867 = 4018301) B4018301
theorem B1785939 : Blo 1784093 1785939 := bstep (se 1 (by rfl) ⟨1339454, by rfl⟩ : syracuseStep 1785939 = 2678909) B2678909
theorem B2007139 : Blo 1784093 2007139 := bstep (se 1 (by rfl) ⟨1505354, by rfl⟩ : syracuseStep 2007139 = 3010709) B3010709
theorem B1785955 : Blo 1784093 1785955 := bstep (se 1 (by rfl) ⟨1339466, by rfl⟩ : syracuseStep 1785955 = 2678933) B2678933
theorem B2678897 : Blo 1784093 2678897 := bstep (se 2 (by rfl) ⟨1004586, by rfl⟩ : syracuseStep 2678897 = 2009173) B2009173
theorem B1785971 : Blo 1784093 1785971 := bstep (se 1 (by rfl) ⟨1339478, by rfl⟩ : syracuseStep 1785971 = 2678957) B2678957
theorem B2678915 : Blo 1784093 2678915 := bstep (se 1 (by rfl) ⟨2009186, by rfl⟩ : syracuseStep 2678915 = 4018373) B4018373
theorem B1785987 : Blo 1784093 1785987 := bstep (se 1 (by rfl) ⟨1339490, by rfl⟩ : syracuseStep 1785987 = 2678981) B2678981
theorem B1786003 : Blo 1784093 1786003 := bstep (se 1 (by rfl) ⟨1339502, by rfl⟩ : syracuseStep 1786003 = 2679005) B2679005
theorem B2678945 : Blo 1784093 2678945 := bstep (se 2 (by rfl) ⟨1004604, by rfl⟩ : syracuseStep 2678945 = 2009209) B2009209
theorem B6774947 : Blo 1784093 6774947 := bstep (se 1 (by rfl) ⟨5081210, by rfl⟩ : syracuseStep 6774947 = 10162421) B10162421
theorem B1786019 : Blo 1784093 1786019 := bstep (se 1 (by rfl) ⟨1339514, by rfl⟩ : syracuseStep 1786019 = 2679029) B2679029
theorem B6774961 : Blo 1784093 6774961 := bstep (se 2 (by rfl) ⟨2540610, by rfl⟩ : syracuseStep 6774961 = 5081221) B5081221
theorem B2678963 : Blo 1784093 2678963 := bstep (se 1 (by rfl) ⟨2009222, by rfl⟩ : syracuseStep 2678963 = 4018445) B4018445
theorem B1786035 : Blo 1784093 1786035 := bstep (se 1 (by rfl) ⟨1339526, by rfl⟩ : syracuseStep 1786035 = 2679053) B2679053
theorem B1786051 : Blo 1784093 1786051 := bstep (se 1 (by rfl) ⟨1339538, by rfl⟩ : syracuseStep 1786051 = 2679077) B2679077
theorem B2678993 : Blo 1784093 2678993 := bstep (se 2 (by rfl) ⟨1004622, by rfl⟩ : syracuseStep 2678993 = 2009245) B2009245
theorem B1786067 : Blo 1784093 1786067 := bstep (se 1 (by rfl) ⟨1339550, by rfl⟩ : syracuseStep 1786067 = 2679101) B2679101
theorem B2679011 : Blo 1784093 2679011 := bstep (se 1 (by rfl) ⟨2009258, by rfl⟩ : syracuseStep 2679011 = 4018517) B4018517
theorem B1786083 : Blo 1784093 1786083 := bstep (se 1 (by rfl) ⟨1339562, by rfl⟩ : syracuseStep 1786083 = 2679125) B2679125
theorem B2007283 : Blo 1784093 2007283 := bstep (se 1 (by rfl) ⟨1505462, by rfl⟩ : syracuseStep 2007283 = 3010925) B3010925
theorem B2679041 : Blo 1784093 2679041 := bstep (se 2 (by rfl) ⟨1004640, by rfl⟩ : syracuseStep 2679041 = 2009281) B2009281
theorem B2679059 : Blo 1784093 2679059 := bstep (se 1 (by rfl) ⟨2009294, by rfl⟩ : syracuseStep 2679059 = 4018589) B4018589
theorem B2679089 : Blo 1784093 2679089 := bstep (se 2 (by rfl) ⟨1004658, by rfl⟩ : syracuseStep 2679089 = 2009317) B2009317
theorem B2679107 : Blo 1784093 2679107 := bstep (se 1 (by rfl) ⟨2009330, by rfl⟩ : syracuseStep 2679107 = 4018661) B4018661
theorem B2679137 : Blo 1784093 2679137 := bstep (se 2 (by rfl) ⟨1004676, by rfl⟩ : syracuseStep 2679137 = 2009353) B2009353
theorem B6021485 : Blo 1784093 6021485 := bstep (se 3 (by rfl) ⟨1129028, by rfl⟩ : syracuseStep 6021485 = 2258057) B2258057
theorem B4014449 : Blo 1784093 4014449 := bstep (se 2 (by rfl) ⟨1505418, by rfl⟩ : syracuseStep 4014449 = 3010837) B3010837
theorem B4014467 : Blo 1784093 4014467 := bstep (se 1 (by rfl) ⟨3010850, by rfl⟩ : syracuseStep 4014467 = 6021701) B6021701
theorem B2007427 : Blo 1784093 2007427 := bstep (se 1 (by rfl) ⟨1505570, by rfl⟩ : syracuseStep 2007427 = 3011141) B3011141
theorem B8249741 : Blo 1784093 8249741 := bstep (se 3 (by rfl) ⟨1546826, by rfl⟩ : syracuseStep 8249741 = 3093653) B3093653
theorem B5718413 : Blo 1784093 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B6021539 : Blo 1784093 6021539 := bstep (se 1 (by rfl) ⟨4516154, by rfl⟩ : syracuseStep 6021539 = 9032309) B9032309
theorem B4825613 : Blo 1784093 4825613 := bstep (se 3 (by rfl) ⟨904802, by rfl⟩ : syracuseStep 4825613 = 1809605) B1809605
theorem B2007571 : Blo 1784093 2007571 := bstep (se 1 (by rfl) ⟨1505678, by rfl⟩ : syracuseStep 2007571 = 3011357) B3011357
theorem B6431267 : Blo 1784093 6431267 := bstep (se 1 (by rfl) ⟨4823450, by rfl⟩ : syracuseStep 6431267 = 9646901) B9646901
theorem B2859571 : Blo 1784093 2859571 := bstep (se 1 (by rfl) ⟨2144678, by rfl⟩ : syracuseStep 2859571 = 4289357) B4289357
theorem B2859617 : Blo 1784093 2859617 := bstep (se 2 (by rfl) ⟨1072356, by rfl⟩ : syracuseStep 2859617 = 2144713) B2144713
theorem B11436643 : Blo 1784093 11436643 := bstep (se 1 (by rfl) ⟨8577482, by rfl⟩ : syracuseStep 11436643 = 17154965) B17154965
theorem B4825699 : Blo 1784093 4825699 := bstep (se 1 (by rfl) ⟨3619274, by rfl⟩ : syracuseStep 4825699 = 7238549) B7238549
theorem B8577677 : Blo 1784093 8577677 := bstep (se 3 (by rfl) ⟨1608314, by rfl⟩ : syracuseStep 8577677 = 3216629) B3216629
theorem B4014737 : Blo 1784093 4014737 := bstep (se 2 (by rfl) ⟨1505526, by rfl⟩ : syracuseStep 4014737 = 3011053) B3011053
theorem B4014755 : Blo 1784093 4014755 := bstep (se 1 (by rfl) ⟨3011066, by rfl⟩ : syracuseStep 4014755 = 6022133) B6022133
theorem B2007715 : Blo 1784093 2007715 := bstep (se 1 (by rfl) ⟨1505786, by rfl⟩ : syracuseStep 2007715 = 3011573) B3011573
theorem B6021809 : Blo 1784093 6021809 := bstep (se 2 (by rfl) ⟨2258178, by rfl⟩ : syracuseStep 6021809 = 4516357) B4516357
theorem B14467825 : Blo 1784093 14467825 := bstep (se 2 (by rfl) ⟨5425434, by rfl⟩ : syracuseStep 14467825 = 10850869) B10850869
theorem B2007859 : Blo 1784093 2007859 := bstep (se 1 (by rfl) ⟨1505894, by rfl⟩ : syracuseStep 2007859 = 3011789) B3011789
theorem B4015025 : Blo 1784093 4015025 := bstep (se 2 (by rfl) ⟨1505634, by rfl⟩ : syracuseStep 4015025 = 3011269) B3011269
theorem B4015043 : Blo 1784093 4015043 := bstep (se 1 (by rfl) ⟨3011282, by rfl⟩ : syracuseStep 4015043 = 6022565) B6022565
theorem B2008003 : Blo 1784093 2008003 := bstep (se 1 (by rfl) ⟨1506002, by rfl⟩ : syracuseStep 2008003 = 3012005) B3012005
theorem B2540497 : Blo 1784093 2540497 := bstep (se 2 (by rfl) ⟨952686, by rfl⟩ : syracuseStep 2540497 = 1905373) B1905373
theorem B2540531 : Blo 1784093 2540531 := bstep (se 1 (by rfl) ⟨1905398, by rfl⟩ : syracuseStep 2540531 = 3810797) B3810797
theorem B2008147 : Blo 1784093 2008147 := bstep (se 1 (by rfl) ⟨1506110, by rfl⟩ : syracuseStep 2008147 = 3012221) B3012221
theorem B6022349 : Blo 1784093 6022349 := bstep (se 3 (by rfl) ⟨1129190, by rfl⟩ : syracuseStep 6022349 = 2258381) B2258381
theorem B4015313 : Blo 1784093 4015313 := bstep (se 2 (by rfl) ⟨1505742, by rfl⟩ : syracuseStep 4015313 = 3011485) B3011485
theorem B4015331 : Blo 1784093 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B2008291 : Blo 1784093 2008291 := bstep (se 1 (by rfl) ⟨1506218, by rfl⟩ : syracuseStep 2008291 = 3012437) B3012437
theorem B2860289 : Blo 1784093 2860289 := bstep (se 2 (by rfl) ⟨1072608, by rfl⟩ : syracuseStep 2860289 = 2145217) B2145217
theorem B6022403 : Blo 1784093 6022403 := bstep (se 1 (by rfl) ⟨4516802, by rfl⟩ : syracuseStep 6022403 = 9033605) B9033605
theorem B9037169 : Blo 1784093 9037169 := bstep (se 2 (by rfl) ⟨3388938, by rfl⟩ : syracuseStep 9037169 = 6777877) B6777877
theorem B2008435 : Blo 1784093 2008435 := bstep (se 1 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 2008435 = 3012653) B3012653
theorem B5293475 : Blo 1784093 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B5719501 : Blo 1784093 5719501 := bstep (se 3 (by rfl) ⟨1072406, by rfl⟩ : syracuseStep 5719501 = 2144813) B2144813
theorem B4015601 : Blo 1784093 4015601 := bstep (se 2 (by rfl) ⟨1505850, by rfl⟩ : syracuseStep 4015601 = 3011701) B3011701
theorem B4015619 : Blo 1784093 4015619 := bstep (se 1 (by rfl) ⟨3011714, by rfl⟩ : syracuseStep 4015619 = 6023429) B6023429
theorem B2008579 : Blo 1784093 2008579 := bstep (se 1 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 2008579 = 3012869) B3012869
theorem B6022673 : Blo 1784093 6022673 := bstep (se 2 (by rfl) ⟨2258502, by rfl⟩ : syracuseStep 6022673 = 4517005) B4517005
theorem B2541089 : Blo 1784093 2541089 := bstep (se 2 (by rfl) ⟨952908, by rfl⟩ : syracuseStep 2541089 = 1905817) B1905817
theorem B11437645 : Blo 1784093 11437645 := bstep (se 3 (by rfl) ⟨2144558, by rfl⟩ : syracuseStep 11437645 = 4289117) B4289117
theorem B3434083 : Blo 1784093 3434083 := bstep (se 1 (by rfl) ⟨2575562, by rfl⟩ : syracuseStep 3434083 = 5151125) B5151125
theorem B6776419 : Blo 1784093 6776419 := bstep (se 1 (by rfl) ⟨5082314, by rfl⟩ : syracuseStep 6776419 = 10164629) B10164629
theorem B2541169 : Blo 1784093 2541169 := bstep (se 2 (by rfl) ⟨952938, by rfl⟩ : syracuseStep 2541169 = 1905877) B1905877
theorem B18327181 : Blo 1784093 18327181 := bstep (se 3 (by rfl) ⟨3436346, by rfl⟩ : syracuseStep 18327181 = 6872693) B6872693
theorem B2008723 : Blo 1784093 2008723 := bstep (se 1 (by rfl) ⟨1506542, by rfl⟩ : syracuseStep 2008723 = 3013085) B3013085
theorem B17622755 : Blo 1784093 17622755 := bstep (se 1 (by rfl) ⟨13217066, by rfl⟩ : syracuseStep 17622755 = 26434133) B26434133
theorem B2860801 : Blo 1784093 2860801 := bstep (se 2 (by rfl) ⟨1072800, by rfl⟩ : syracuseStep 2860801 = 2145601) B2145601
theorem B4015889 : Blo 1784093 4015889 := bstep (se 2 (by rfl) ⟨1505958, by rfl⟩ : syracuseStep 4015889 = 3011917) B3011917
theorem B4015907 : Blo 1784093 4015907 := bstep (se 1 (by rfl) ⟨3011930, by rfl⟩ : syracuseStep 4015907 = 6023861) B6023861
theorem B2008867 : Blo 1784093 2008867 := bstep (se 1 (by rfl) ⟨1506650, by rfl⟩ : syracuseStep 2008867 = 3013301) B3013301
theorem B15247217 : Blo 1784093 15247217 := bstep (se 2 (by rfl) ⟨5717706, by rfl⟩ : syracuseStep 15247217 = 11435413) B11435413
theorem B2009011 : Blo 1784093 2009011 := bstep (se 1 (by rfl) ⟨1506758, by rfl⟩ : syracuseStep 2009011 = 3013517) B3013517
theorem B6023213 : Blo 1784093 6023213 := bstep (se 3 (by rfl) ⟨1129352, by rfl⟩ : syracuseStep 6023213 = 2258705) B2258705
theorem B4016177 : Blo 1784093 4016177 := bstep (se 2 (by rfl) ⟨1506066, by rfl⟩ : syracuseStep 4016177 = 3012133) B3012133
theorem B4016195 : Blo 1784093 4016195 := bstep (se 1 (by rfl) ⟨3012146, by rfl⟩ : syracuseStep 4016195 = 6024293) B6024293
theorem B2009155 : Blo 1784093 2009155 := bstep (se 1 (by rfl) ⟨1506866, by rfl⟩ : syracuseStep 2009155 = 3013733) B3013733
theorem B6023267 : Blo 1784093 6023267 := bstep (se 1 (by rfl) ⟨4517450, by rfl⟩ : syracuseStep 6023267 = 9034901) B9034901
theorem B17156195 : Blo 1784093 17156195 := bstep (se 1 (by rfl) ⟨12867146, by rfl⟩ : syracuseStep 17156195 = 25734293) B25734293
theorem B4581539 : Blo 1784093 4581539 := bstep (se 1 (by rfl) ⟨3436154, by rfl⟩ : syracuseStep 4581539 = 6872309) B6872309
theorem B2009299 : Blo 1784093 2009299 := bstep (se 1 (by rfl) ⟨1506974, by rfl⟩ : syracuseStep 2009299 = 3013949) B3013949
theorem B4516145 : Blo 1784093 4516145 := bstep (se 2 (by rfl) ⟨1693554, by rfl⟩ : syracuseStep 4516145 = 3387109) B3387109
theorem B5081393 : Blo 1784093 5081393 := bstep (se 2 (by rfl) ⟨1905522, by rfl⟩ : syracuseStep 5081393 = 3811045) B3811045
theorem B4016465 : Blo 1784093 4016465 := bstep (se 2 (by rfl) ⟨1506174, by rfl⟩ : syracuseStep 4016465 = 3012349) B3012349
theorem B4516195 : Blo 1784093 4516195 := bstep (se 1 (by rfl) ⟨3387146, by rfl⟩ : syracuseStep 4516195 = 6774293) B6774293
theorem B4016483 : Blo 1784093 4016483 := bstep (se 1 (by rfl) ⟨3012362, by rfl⟩ : syracuseStep 4016483 = 6024725) B6024725
theorem B6023537 : Blo 1784093 6023537 := bstep (se 2 (by rfl) ⟨2258826, by rfl⟩ : syracuseStep 6023537 = 4517653) B4517653
theorem B2541955 : Blo 1784093 2541955 := bstep (se 1 (by rfl) ⟨1906466, by rfl⟩ : syracuseStep 2541955 = 3812933) B3812933
theorem B4286897 : Blo 1784093 4286897 := bstep (se 2 (by rfl) ⟨1607586, by rfl⟩ : syracuseStep 4286897 = 3215173) B3215173
theorem B4516337 : Blo 1784093 4516337 := bstep (se 2 (by rfl) ⟨1693626, by rfl⟩ : syracuseStep 4516337 = 3387253) B3387253
theorem B3811907 : Blo 1784093 3811907 := bstep (se 1 (by rfl) ⟨2858930, by rfl⟩ : syracuseStep 3811907 = 5717861) B5717861
theorem B22874723 : Blo 1784093 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B4016753 : Blo 1784093 4016753 := bstep (se 2 (by rfl) ⟨1506282, by rfl⟩ : syracuseStep 4016753 = 3012565) B3012565
theorem B4016771 : Blo 1784093 4016771 := bstep (se 1 (by rfl) ⟨3012578, by rfl⟩ : syracuseStep 4016771 = 6025157) B6025157
theorem B7252643 : Blo 1784093 7252643 := bstep (se 1 (by rfl) ⟨5439482, by rfl⟩ : syracuseStep 7252643 = 10878965) B10878965
theorem B2714323 : Blo 1784093 2714323 := bstep (se 1 (by rfl) ⟨2035742, by rfl⟩ : syracuseStep 2714323 = 4071485) B4071485
theorem B9038627 : Blo 1784093 9038627 := bstep (se 1 (by rfl) ⟨6778970, by rfl⟩ : syracuseStep 9038627 = 13557941) B13557941
theorem B2542433 : Blo 1784093 2542433 := bstep (se 2 (by rfl) ⟨953412, by rfl⟩ : syracuseStep 2542433 = 1906825) B1906825
theorem B6024077 : Blo 1784093 6024077 := bstep (se 3 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 6024077 = 2259029) B2259029
theorem B4017041 : Blo 1784093 4017041 := bstep (se 2 (by rfl) ⟨1506390, by rfl⟩ : syracuseStep 4017041 = 3012781) B3012781
theorem B4582289 : Blo 1784093 4582289 := bstep (se 2 (by rfl) ⟨1718358, by rfl⟩ : syracuseStep 4582289 = 3436717) B3436717
theorem B6867875 : Blo 1784093 6867875 := bstep (se 1 (by rfl) ⟨5150906, by rfl⟩ : syracuseStep 6867875 = 10301813) B10301813
theorem B4017059 : Blo 1784093 4017059 := bstep (se 1 (by rfl) ⟨3012794, by rfl⟩ : syracuseStep 4017059 = 6025589) B6025589
theorem B6024131 : Blo 1784093 6024131 := bstep (se 1 (by rfl) ⟨4518098, by rfl⟩ : syracuseStep 6024131 = 9036197) B9036197
theorem B5082065 : Blo 1784093 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B2542547 : Blo 1784093 2542547 := bstep (se 1 (by rfl) ⟨1906910, by rfl⟩ : syracuseStep 2542547 = 3813821) B3813821
theorem B6433805 : Blo 1784093 6433805 := bstep (se 3 (by rfl) ⟨1206338, by rfl⟩ : syracuseStep 6433805 = 2412677) B2412677
theorem B2542627 : Blo 1784093 2542627 := bstep (se 1 (by rfl) ⟨1906970, by rfl⟩ : syracuseStep 2542627 = 3813941) B3813941
theorem B12209201 : Blo 1784093 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B4287665 : Blo 1784093 4287665 := bstep (se 2 (by rfl) ⟨1607874, by rfl⟩ : syracuseStep 4287665 = 3215749) B3215749
theorem B4017329 : Blo 1784093 4017329 := bstep (se 2 (by rfl) ⟨1506498, by rfl⟩ : syracuseStep 4017329 = 3012997) B3012997
theorem B4017347 : Blo 1784093 4017347 := bstep (se 1 (by rfl) ⟨3013010, by rfl⟩ : syracuseStep 4017347 = 6026021) B6026021
theorem B5721283 : Blo 1784093 5721283 := bstep (se 1 (by rfl) ⟨4290962, by rfl⟩ : syracuseStep 5721283 = 8581925) B8581925
theorem B6024401 : Blo 1784093 6024401 := bstep (se 2 (by rfl) ⟨2259150, by rfl⟩ : syracuseStep 6024401 = 4518301) B4518301
theorem B5721347 : Blo 1784093 5721347 := bstep (se 1 (by rfl) ⟨4291010, by rfl⟩ : syracuseStep 5721347 = 8582021) B8582021
theorem B7621901 : Blo 1784093 7621901 := bstep (se 3 (by rfl) ⟨1429106, by rfl⟩ : syracuseStep 7621901 = 2858213) B2858213
theorem B4287811 : Blo 1784093 4287811 := bstep (se 1 (by rfl) ⟨3215858, by rfl⟩ : syracuseStep 4287811 = 6431717) B6431717
theorem B9645389 : Blo 1784093 9645389 := bstep (se 3 (by rfl) ⟨1808510, by rfl⟩ : syracuseStep 9645389 = 3617021) B3617021
theorem B5721425 : Blo 1784093 5721425 := bstep (se 2 (by rfl) ⟨2145534, by rfl⟩ : syracuseStep 5721425 = 4291069) B4291069
theorem B16289221 : Blo 1784093 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B4517329 : Blo 1784093 4517329 := bstep (se 2 (by rfl) ⟨1693998, by rfl⟩ : syracuseStep 4517329 = 3387997) B3387997
theorem B4017617 : Blo 1784093 4017617 := bstep (se 2 (by rfl) ⟨1506606, by rfl⟩ : syracuseStep 4017617 = 3013213) B3013213
theorem B4017635 : Blo 1784093 4017635 := bstep (se 1 (by rfl) ⟨3013226, by rfl⟩ : syracuseStep 4017635 = 6026453) B6026453
theorem B24440291 : Blo 1784093 24440291 := bstep (se 1 (by rfl) ⟨18330218, by rfl⟩ : syracuseStep 24440291 = 36660437) B36660437
theorem B5426723 : Blo 1784093 5426723 := bstep (se 1 (by rfl) ⟨4070042, by rfl⟩ : syracuseStep 5426723 = 8140085) B8140085
theorem B10161713 : Blo 1784093 10161713 := bstep (se 2 (by rfl) ⟨3810642, by rfl⟩ : syracuseStep 10161713 = 7621285) B7621285
theorem B9039437 : Blo 1784093 9039437 := bstep (se 3 (by rfl) ⟨1694894, by rfl⟩ : syracuseStep 9039437 = 3389789) B3389789
theorem B3387025 : Blo 1784093 3387025 := bstep (se 2 (by rfl) ⟨1270134, by rfl⟩ : syracuseStep 3387025 = 2540269) B2540269
theorem B3215057 : Blo 1784093 3215057 := bstep (se 2 (by rfl) ⟨1205646, by rfl⟩ : syracuseStep 3215057 = 2411293) B2411293
theorem B4517603 : Blo 1784093 4517603 := bstep (se 1 (by rfl) ⟨3388202, by rfl⟩ : syracuseStep 4517603 = 6776405) B6776405
theorem B5082851 : Blo 1784093 5082851 := bstep (se 1 (by rfl) ⟨3812138, by rfl⟩ : syracuseStep 5082851 = 7624277) B7624277
theorem B6024941 : Blo 1784093 6024941 := bstep (se 3 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 6024941 = 2259353) B2259353
theorem B4017905 : Blo 1784093 4017905 := bstep (se 2 (by rfl) ⟨1506714, by rfl⟩ : syracuseStep 4017905 = 3013429) B3013429
theorem B4017923 : Blo 1784093 4017923 := bstep (se 1 (by rfl) ⟨3013442, by rfl⟩ : syracuseStep 4017923 = 6026885) B6026885
theorem B6778637 : Blo 1784093 6778637 := bstep (se 3 (by rfl) ⟨1270994, by rfl⟩ : syracuseStep 6778637 = 2541989) B2541989
theorem B6024995 : Blo 1784093 6024995 := bstep (se 1 (by rfl) ⟨4518746, by rfl⟩ : syracuseStep 6024995 = 9037493) B9037493
theorem B2936657 : Blo 1784093 2936657 := bstep (se 2 (by rfl) ⟨1101246, by rfl⟩ : syracuseStep 2936657 = 2202493) B2202493
theorem B2715473 : Blo 1784093 2715473 := bstep (se 2 (by rfl) ⟨1018302, by rfl⟩ : syracuseStep 2715473 = 2036605) B2036605
theorem B2412385 : Blo 1784093 2412385 := bstep (se 2 (by rfl) ⟨904644, by rfl⟩ : syracuseStep 2412385 = 1809289) B1809289
theorem B2715491 : Blo 1784093 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B4517795 : Blo 1784093 4517795 := bstep (se 1 (by rfl) ⟨3388346, by rfl⟩ : syracuseStep 4517795 = 6776693) B6776693
theorem B21180341 : Blo 1784093 21180341 := bstep (se 5 (by rfl) ⟨992828, by rfl⟩ : syracuseStep 21180341 = 1985657) B1985657
theorem B4018193 : Blo 1784093 4018193 := bstep (se 2 (by rfl) ⟨1506822, by rfl⟩ : syracuseStep 4018193 = 3013645) B3013645
theorem B4018211 : Blo 1784093 4018211 := bstep (se 1 (by rfl) ⟨3013658, by rfl⟩ : syracuseStep 4018211 = 6027317) B6027317
theorem B5083181 : Blo 1784093 5083181 := bstep (se 3 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 5083181 = 1906193) B1906193
theorem B6025265 : Blo 1784093 6025265 := bstep (se 2 (by rfl) ⟨2259474, by rfl⟩ : syracuseStep 6025265 = 4518949) B4518949
theorem B5083249 : Blo 1784093 5083249 := bstep (se 2 (by rfl) ⟨1906218, by rfl⟩ : syracuseStep 5083249 = 3812437) B3812437
theorem B3010675 : Blo 1784093 3010675 := bstep (se 1 (by rfl) ⟨2258006, by rfl⟩ : syracuseStep 3010675 = 4516013) B4516013
theorem B19869923 : Blo 1784093 19869923 := bstep (se 1 (by rfl) ⟨14902442, by rfl⟩ : syracuseStep 19869923 = 29804885) B29804885
theorem B3010817 : Blo 1784093 3010817 := bstep (se 2 (by rfl) ⟨1129056, by rfl⟩ : syracuseStep 3010817 = 2258113) B2258113
theorem B9031985 : Blo 1784093 9031985 := bstep (se 2 (by rfl) ⟨3386994, by rfl⟩ : syracuseStep 9031985 = 6773989) B6773989
theorem B4018481 : Blo 1784093 4018481 := bstep (se 2 (by rfl) ⟨1506930, by rfl⟩ : syracuseStep 4018481 = 3013861) B3013861
theorem B4018499 : Blo 1784093 4018499 := bstep (se 1 (by rfl) ⟨3013874, by rfl⟩ : syracuseStep 4018499 = 6027749) B6027749
theorem B8253809 : Blo 1784093 8253809 := bstep (se 2 (by rfl) ⟨3095178, by rfl⟩ : syracuseStep 8253809 = 6190357) B6190357
theorem B3010945 : Blo 1784093 3010945 := bstep (se 2 (by rfl) ⟨1129104, by rfl⟩ : syracuseStep 3010945 = 2258209) B2258209
theorem B5083523 : Blo 1784093 5083523 := bstep (se 1 (by rfl) ⟨3812642, by rfl⟩ : syracuseStep 5083523 = 7625285) B7625285
theorem B22868365 : Blo 1784093 22868365 := bstep (se 3 (by rfl) ⟨4287818, by rfl⟩ : syracuseStep 22868365 = 8575637) B8575637
theorem B3010979 : Blo 1784093 3010979 := bstep (se 1 (by rfl) ⟨2258234, by rfl⟩ : syracuseStep 3010979 = 4516469) B4516469
theorem B4289041 : Blo 1784093 4289041 := bstep (se 2 (by rfl) ⟨1608390, by rfl⟩ : syracuseStep 4289041 = 3216781) B3216781
theorem B3011107 : Blo 1784093 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B3813923 : Blo 1784093 3813923 := bstep (se 1 (by rfl) ⟨2860442, by rfl⟩ : syracuseStep 3813923 = 5720885) B5720885
theorem B6025805 : Blo 1784093 6025805 := bstep (se 3 (by rfl) ⟨1129838, by rfl⟩ : syracuseStep 6025805 = 2259677) B2259677
theorem B6025859 : Blo 1784093 6025859 := bstep (se 1 (by rfl) ⟨4519394, by rfl⟩ : syracuseStep 6025859 = 9038789) B9038789
theorem B11596421 : Blo 1784093 11596421 := bstep (se 4 (by rfl) ⟨1087164, by rfl⟩ : syracuseStep 11596421 = 2174329) B2174329
theorem B3011249 : Blo 1784093 3011249 := bstep (se 2 (by rfl) ⟨1129218, by rfl⟩ : syracuseStep 3011249 = 2258437) B2258437
theorem B3388081 : Blo 1784093 3388081 := bstep (se 2 (by rfl) ⟨1270530, by rfl⟩ : syracuseStep 3388081 = 2541061) B2541061
theorem B6107843 : Blo 1784093 6107843 := bstep (se 1 (by rfl) ⟨4580882, by rfl⟩ : syracuseStep 6107843 = 9161765) B9161765
theorem B2446033 : Blo 1784093 2446033 := bstep (se 2 (by rfl) ⟨917262, by rfl⟩ : syracuseStep 2446033 = 1834525) B1834525
theorem B3011377 : Blo 1784093 3011377 := bstep (se 2 (by rfl) ⟨1129266, by rfl⟩ : syracuseStep 3011377 = 2258533) B2258533
theorem B4518737 : Blo 1784093 4518737 := bstep (se 2 (by rfl) ⟨1694526, by rfl⟩ : syracuseStep 4518737 = 3389053) B3389053
theorem B3011411 : Blo 1784093 3011411 := bstep (se 1 (by rfl) ⟨2258558, by rfl⟩ : syracuseStep 3011411 = 4517117) B4517117
theorem B4518787 : Blo 1784093 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B6026129 : Blo 1784093 6026129 := bstep (se 2 (by rfl) ⟨2259798, by rfl⟩ : syracuseStep 6026129 = 4519597) B4519597
theorem B3011539 : Blo 1784093 3011539 := bstep (se 1 (by rfl) ⟨2258654, by rfl⟩ : syracuseStep 3011539 = 4517309) B4517309
theorem B10163171 : Blo 1784093 10163171 := bstep (se 1 (by rfl) ⟨7622378, by rfl⟩ : syracuseStep 10163171 = 15244757) B15244757
theorem B43439075 : Blo 1784093 43439075 := bstep (se 1 (by rfl) ⟨32579306, by rfl⟩ : syracuseStep 43439075 = 65158613) B65158613
theorem B4518929 : Blo 1784093 4518929 := bstep (se 2 (by rfl) ⟨1694598, by rfl⟩ : syracuseStep 4518929 = 3389197) B3389197
theorem B2036755 : Blo 1784093 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B3388483 : Blo 1784093 3388483 := bstep (se 1 (by rfl) ⟨2541362, by rfl⟩ : syracuseStep 3388483 = 5082725) B5082725
theorem B3011681 : Blo 1784093 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B3388529 : Blo 1784093 3388529 := bstep (se 2 (by rfl) ⟨1270698, by rfl⟩ : syracuseStep 3388529 = 2541397) B2541397
theorem B5084365 : Blo 1784093 5084365 := bstep (se 3 (by rfl) ⟨953318, by rfl⟩ : syracuseStep 5084365 = 1906637) B1906637
theorem B4125905 : Blo 1784093 4125905 := bstep (se 2 (by rfl) ⟨1547214, by rfl⟩ : syracuseStep 4125905 = 3094429) B3094429
theorem B3011809 : Blo 1784093 3011809 := bstep (se 2 (by rfl) ⟨1129428, by rfl⟩ : syracuseStep 3011809 = 2258857) B2258857
theorem B3011843 : Blo 1784093 3011843 := bstep (se 1 (by rfl) ⟨2258882, by rfl⟩ : syracuseStep 3011843 = 4517765) B4517765
theorem B4347217 : Blo 1784093 4347217 := bstep (se 2 (by rfl) ⟨1630206, by rfl⟩ : syracuseStep 4347217 = 3260413) B3260413
theorem B2258275 : Blo 1784093 2258275 := bstep (se 1 (by rfl) ⟨1693706, by rfl⟩ : syracuseStep 2258275 = 3387413) B3387413
theorem B5084525 : Blo 1784093 5084525 := bstep (se 3 (by rfl) ⟨953348, by rfl⟩ : syracuseStep 5084525 = 1906697) B1906697
theorem B3011971 : Blo 1784093 3011971 := bstep (se 1 (by rfl) ⟨2258978, by rfl⟩ : syracuseStep 3011971 = 4517957) B4517957
theorem B3388817 : Blo 1784093 3388817 := bstep (se 2 (by rfl) ⟨1270806, by rfl⟩ : syracuseStep 3388817 = 2541613) B2541613
theorem B6026669 : Blo 1784093 6026669 := bstep (se 3 (by rfl) ⟨1130000, by rfl⟩ : syracuseStep 6026669 = 2260001) B2260001
theorem B2676161 : Blo 1784093 2676161 := bstep (se 2 (by rfl) ⟨1003560, by rfl⟩ : syracuseStep 2676161 = 2007121) B2007121
theorem B3052993 : Blo 1784093 3052993 := bstep (se 2 (by rfl) ⟨1144872, by rfl⟩ : syracuseStep 3052993 = 2289745) B2289745
theorem B2258371 : Blo 1784093 2258371 := bstep (se 1 (by rfl) ⟨1693778, by rfl⟩ : syracuseStep 2258371 = 3387557) B3387557
theorem B2676179 : Blo 1784093 2676179 := bstep (se 1 (by rfl) ⟨2007134, by rfl⟩ : syracuseStep 2676179 = 4014269) B4014269
theorem B6026723 : Blo 1784093 6026723 := bstep (se 1 (by rfl) ⟨4520042, by rfl⟩ : syracuseStep 6026723 = 9040085) B9040085
theorem B2676209 : Blo 1784093 2676209 := bstep (se 2 (by rfl) ⟨1003578, by rfl⟩ : syracuseStep 2676209 = 2007157) B2007157
theorem B2676227 : Blo 1784093 2676227 := bstep (se 1 (by rfl) ⟨2007170, by rfl⟩ : syracuseStep 2676227 = 4014341) B4014341
theorem B3012113 : Blo 1784093 3012113 := bstep (se 2 (by rfl) ⟨1129542, by rfl⟩ : syracuseStep 3012113 = 2259085) B2259085
theorem B2676257 : Blo 1784093 2676257 := bstep (se 2 (by rfl) ⟨1003596, by rfl⟩ : syracuseStep 2676257 = 2007193) B2007193
theorem B5084707 : Blo 1784093 5084707 := bstep (se 1 (by rfl) ⟨3813530, by rfl⟩ : syracuseStep 5084707 = 7627061) B7627061
theorem B10851889 : Blo 1784093 10851889 := bstep (se 2 (by rfl) ⟨4069458, by rfl⟩ : syracuseStep 10851889 = 8138917) B8138917
theorem B2676275 : Blo 1784093 2676275 := bstep (se 1 (by rfl) ⟨2007206, by rfl⟩ : syracuseStep 2676275 = 4014413) B4014413
theorem B2676305 : Blo 1784093 2676305 := bstep (se 2 (by rfl) ⟨1003614, by rfl⟩ : syracuseStep 2676305 = 2007229) B2007229
theorem B2676323 : Blo 1784093 2676323 := bstep (se 1 (by rfl) ⟨2007242, by rfl⟩ : syracuseStep 2676323 = 4014485) B4014485
theorem B2676353 : Blo 1784093 2676353 := bstep (se 2 (by rfl) ⟨1003632, by rfl⟩ : syracuseStep 2676353 = 2007265) B2007265
theorem B3012241 : Blo 1784093 3012241 := bstep (se 2 (by rfl) ⟨1129590, by rfl⟩ : syracuseStep 3012241 = 2259181) B2259181
theorem B2676371 : Blo 1784093 2676371 := bstep (se 1 (by rfl) ⟨2007278, by rfl⟩ : syracuseStep 2676371 = 4014557) B4014557
theorem B2676401 : Blo 1784093 2676401 := bstep (se 2 (by rfl) ⟨1003650, by rfl⟩ : syracuseStep 2676401 = 2007301) B2007301
theorem B3012275 : Blo 1784093 3012275 := bstep (se 1 (by rfl) ⟨2259206, by rfl⟩ : syracuseStep 3012275 = 4518413) B4518413
theorem B2676419 : Blo 1784093 2676419 := bstep (se 1 (by rfl) ⟨2007314, by rfl⟩ : syracuseStep 2676419 = 4014629) B4014629
theorem B22869701 : Blo 1784093 22869701 := bstep (se 4 (by rfl) ⟨2144034, by rfl⟩ : syracuseStep 22869701 = 4288069) B4288069
theorem B10172101 : Blo 1784093 10172101 := bstep (se 4 (by rfl) ⟨953634, by rfl⟩ : syracuseStep 10172101 = 1907269) B1907269
theorem B2676449 : Blo 1784093 2676449 := bstep (se 2 (by rfl) ⟨1003668, by rfl⟩ : syracuseStep 2676449 = 2007337) B2007337
theorem B9033443 : Blo 1784093 9033443 := bstep (se 1 (by rfl) ⟨6775082, by rfl⟩ : syracuseStep 9033443 = 13550165) B13550165
theorem B43448035 : Blo 1784093 43448035 := bstep (se 1 (by rfl) ⟨32586026, by rfl⟩ : syracuseStep 43448035 = 65172053) B65172053
theorem B6026993 : Blo 1784093 6026993 := bstep (se 2 (by rfl) ⟨2260122, by rfl⟩ : syracuseStep 6026993 = 4520245) B4520245
theorem B2676467 : Blo 1784093 2676467 := bstep (se 1 (by rfl) ⟨2007350, by rfl⟩ : syracuseStep 2676467 = 4014701) B4014701
theorem B2676497 : Blo 1784093 2676497 := bstep (se 2 (by rfl) ⟨1003686, by rfl⟩ : syracuseStep 2676497 = 2007373) B2007373
theorem B2676515 : Blo 1784093 2676515 := bstep (se 1 (by rfl) ⟨2007386, by rfl⟩ : syracuseStep 2676515 = 4014773) B4014773
theorem B6108977 : Blo 1784093 6108977 := bstep (se 2 (by rfl) ⟨2290866, by rfl⟩ : syracuseStep 6108977 = 4581733) B4581733
theorem B3012403 : Blo 1784093 3012403 := bstep (se 1 (by rfl) ⟨2259302, by rfl⟩ : syracuseStep 3012403 = 4518605) B4518605
theorem B2676545 : Blo 1784093 2676545 := bstep (se 2 (by rfl) ⟨1003704, by rfl⟩ : syracuseStep 2676545 = 2007409) B2007409
theorem B2676563 : Blo 1784093 2676563 := bstep (se 1 (by rfl) ⟨2007422, by rfl⟩ : syracuseStep 2676563 = 4014845) B4014845
theorem B14481251 : Blo 1784093 14481251 := bstep (se 1 (by rfl) ⟨10860938, by rfl⟩ : syracuseStep 14481251 = 21721877) B21721877
theorem B2676593 : Blo 1784093 2676593 := bstep (se 2 (by rfl) ⟨1003722, by rfl⟩ : syracuseStep 2676593 = 2007445) B2007445
theorem B2676611 : Blo 1784093 2676611 := bstep (se 1 (by rfl) ⟨2007458, by rfl⟩ : syracuseStep 2676611 = 4014917) B4014917
theorem B2676641 : Blo 1784093 2676641 := bstep (se 2 (by rfl) ⟨1003740, by rfl⟩ : syracuseStep 2676641 = 2007481) B2007481
theorem B2676659 : Blo 1784093 2676659 := bstep (se 1 (by rfl) ⟨2007494, by rfl⟩ : syracuseStep 2676659 = 4014989) B4014989
theorem B2258867 : Blo 1784093 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B2144179 : Blo 1784093 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B3012545 : Blo 1784093 3012545 := bstep (se 2 (by rfl) ⟨1129704, by rfl⟩ : syracuseStep 3012545 = 2259409) B2259409
theorem B2676689 : Blo 1784093 2676689 := bstep (se 2 (by rfl) ⟨1003758, by rfl⟩ : syracuseStep 2676689 = 2007517) B2007517
theorem B8574947 : Blo 1784093 8574947 := bstep (se 1 (by rfl) ⟨6431210, by rfl⟩ : syracuseStep 8574947 = 12862421) B12862421
theorem B2676707 : Blo 1784093 2676707 := bstep (se 1 (by rfl) ⟨2007530, by rfl⟩ : syracuseStep 2676707 = 4015061) B4015061
theorem B6191075 : Blo 1784093 6191075 := bstep (se 1 (by rfl) ⟨4643306, by rfl⟩ : syracuseStep 6191075 = 9286613) B9286613
theorem B5715953 : Blo 1784093 5715953 := bstep (se 2 (by rfl) ⟨2143482, by rfl⟩ : syracuseStep 5715953 = 4286965) B4286965
theorem B4519921 : Blo 1784093 4519921 := bstep (se 2 (by rfl) ⟨1694970, by rfl⟩ : syracuseStep 4519921 = 3389941) B3389941
theorem B2676737 : Blo 1784093 2676737 := bstep (se 2 (by rfl) ⟨1003776, by rfl⟩ : syracuseStep 2676737 = 2007553) B2007553
theorem B16291853 : Blo 1784093 16291853 := bstep (se 3 (by rfl) ⟨3054722, by rfl⟩ : syracuseStep 16291853 = 6109445) B6109445
theorem B2676755 : Blo 1784093 2676755 := bstep (se 1 (by rfl) ⟨2007566, by rfl⟩ : syracuseStep 2676755 = 4015133) B4015133
theorem B2676785 : Blo 1784093 2676785 := bstep (se 2 (by rfl) ⟨1003794, by rfl⟩ : syracuseStep 2676785 = 2007589) B2007589
theorem B3012673 : Blo 1784093 3012673 := bstep (se 2 (by rfl) ⟨1129752, by rfl⟩ : syracuseStep 3012673 = 2259505) B2259505
theorem B2676803 : Blo 1784093 2676803 := bstep (se 1 (by rfl) ⟨2007602, by rfl⟩ : syracuseStep 2676803 = 4015205) B4015205
theorem B2676833 : Blo 1784093 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B3012707 : Blo 1784093 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B3389539 : Blo 1784093 3389539 := bstep (se 1 (by rfl) ⟨2542154, by rfl⟩ : syracuseStep 3389539 = 5084309) B5084309
theorem B1906787 : Blo 1784093 1906787 := bstep (se 1 (by rfl) ⟨1430090, by rfl⟩ : syracuseStep 1906787 = 2860181) B2860181
theorem B2676851 : Blo 1784093 2676851 := bstep (se 1 (by rfl) ⟨2007638, by rfl⟩ : syracuseStep 2676851 = 4015277) B4015277
theorem B2676881 : Blo 1784093 2676881 := bstep (se 2 (by rfl) ⟨1003830, by rfl⟩ : syracuseStep 2676881 = 2007661) B2007661
theorem B2676899 : Blo 1784093 2676899 := bstep (se 1 (by rfl) ⟨2007674, by rfl⟩ : syracuseStep 2676899 = 4015349) B4015349
theorem B5429425 : Blo 1784093 5429425 := bstep (se 2 (by rfl) ⟨2036034, by rfl⟩ : syracuseStep 5429425 = 4072069) B4072069
theorem B2676929 : Blo 1784093 2676929 := bstep (se 2 (by rfl) ⟨1003848, by rfl⟩ : syracuseStep 2676929 = 2007697) B2007697
theorem B2676947 : Blo 1784093 2676947 := bstep (se 1 (by rfl) ⟨2007710, by rfl⟩ : syracuseStep 2676947 = 4015421) B4015421
theorem B3012835 : Blo 1784093 3012835 := bstep (se 1 (by rfl) ⟨2259626, by rfl⟩ : syracuseStep 3012835 = 4519253) B4519253
theorem B8575217 : Blo 1784093 8575217 := bstep (se 2 (by rfl) ⟨3215706, by rfl⟩ : syracuseStep 8575217 = 6431413) B6431413
theorem B2676977 : Blo 1784093 2676977 := bstep (se 2 (by rfl) ⟨1003866, by rfl⟩ : syracuseStep 2676977 = 2007733) B2007733
theorem B2676995 : Blo 1784093 2676995 := bstep (se 1 (by rfl) ⟨2007746, by rfl⟩ : syracuseStep 2676995 = 4015493) B4015493
theorem B4520195 : Blo 1784093 4520195 := bstep (se 1 (by rfl) ⟨3390146, by rfl⟩ : syracuseStep 4520195 = 6780293) B6780293
theorem B6027533 : Blo 1784093 6027533 := bstep (se 3 (by rfl) ⟨1130162, by rfl⟩ : syracuseStep 6027533 = 2260325) B2260325
theorem B3217681 : Blo 1784093 3217681 := bstep (se 2 (by rfl) ⟨1206630, by rfl⟩ : syracuseStep 3217681 = 2413261) B2413261
theorem B2677025 : Blo 1784093 2677025 := bstep (se 2 (by rfl) ⟨1003884, by rfl⟩ : syracuseStep 2677025 = 2007769) B2007769
theorem B1784099 : Blo 1784093 1784099 := bstep (se 1 (by rfl) ⟨1338074, by rfl⟩ : syracuseStep 1784099 = 2676149) B2676149
theorem B1784115 : Blo 1784093 1784115 := bstep (se 1 (by rfl) ⟨1338086, by rfl⟩ : syracuseStep 1784115 = 2676173) B2676173
theorem B2677043 : Blo 1784093 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B1784131 : Blo 1784093 1784131 := bstep (se 1 (by rfl) ⟨1338098, by rfl⟩ : syracuseStep 1784131 = 2676197) B2676197
theorem B6027587 : Blo 1784093 6027587 := bstep (se 1 (by rfl) ⟨4520690, by rfl⟩ : syracuseStep 6027587 = 9041381) B9041381
theorem B2677073 : Blo 1784093 2677073 := bstep (se 2 (by rfl) ⟨1003902, by rfl⟩ : syracuseStep 2677073 = 2007805) B2007805
theorem B1784147 : Blo 1784093 1784147 := bstep (se 1 (by rfl) ⟨1338110, by rfl⟩ : syracuseStep 1784147 = 2676221) B2676221
theorem B1784163 : Blo 1784093 1784163 := bstep (se 1 (by rfl) ⟨1338122, by rfl⟩ : syracuseStep 1784163 = 2676245) B2676245
theorem B2677091 : Blo 1784093 2677091 := bstep (se 1 (by rfl) ⟨2007818, by rfl⟩ : syracuseStep 2677091 = 4015637) B4015637
theorem B3012977 : Blo 1784093 3012977 := bstep (se 2 (by rfl) ⟨1129866, by rfl⟩ : syracuseStep 3012977 = 2259733) B2259733
theorem B1784179 : Blo 1784093 1784179 := bstep (se 1 (by rfl) ⟨1338134, by rfl⟩ : syracuseStep 1784179 = 2676269) B2676269
theorem B2677121 : Blo 1784093 2677121 := bstep (se 2 (by rfl) ⟨1003920, by rfl⟩ : syracuseStep 2677121 = 2007841) B2007841
theorem B1784195 : Blo 1784093 1784195 := bstep (se 1 (by rfl) ⟨1338146, by rfl⟩ : syracuseStep 1784195 = 2676293) B2676293
theorem B1784211 : Blo 1784093 1784211 := bstep (se 1 (by rfl) ⟨1338158, by rfl⟩ : syracuseStep 1784211 = 2676317) B2676317
theorem B2677139 : Blo 1784093 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B1784227 : Blo 1784093 1784227 := bstep (se 1 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 1784227 = 2676341) B2676341
theorem B8575409 : Blo 1784093 8575409 := bstep (se 2 (by rfl) ⟨3215778, by rfl⟩ : syracuseStep 8575409 = 6431557) B6431557
theorem B2677169 : Blo 1784093 2677169 := bstep (se 2 (by rfl) ⟨1003938, by rfl⟩ : syracuseStep 2677169 = 2007877) B2007877
theorem B1784243 : Blo 1784093 1784243 := bstep (se 1 (by rfl) ⟨1338182, by rfl⟩ : syracuseStep 1784243 = 2676365) B2676365
theorem B1784259 : Blo 1784093 1784259 := bstep (se 1 (by rfl) ⟨1338194, by rfl⟩ : syracuseStep 1784259 = 2676389) B2676389
theorem B2677187 : Blo 1784093 2677187 := bstep (se 1 (by rfl) ⟨2007890, by rfl⟩ : syracuseStep 2677187 = 4015781) B4015781
theorem B4520387 : Blo 1784093 4520387 := bstep (se 1 (by rfl) ⟨3390290, by rfl⟩ : syracuseStep 4520387 = 6780581) B6780581
theorem B1784275 : Blo 1784093 1784275 := bstep (se 1 (by rfl) ⟨1338206, by rfl⟩ : syracuseStep 1784275 = 2676413) B2676413
theorem B2677217 : Blo 1784093 2677217 := bstep (se 2 (by rfl) ⟨1003956, by rfl⟩ : syracuseStep 2677217 = 2007913) B2007913
theorem B1784291 : Blo 1784093 1784291 := bstep (se 1 (by rfl) ⟨1338218, by rfl⟩ : syracuseStep 1784291 = 2676437) B2676437
theorem B3013105 : Blo 1784093 3013105 := bstep (se 2 (by rfl) ⟨1129914, by rfl⟩ : syracuseStep 3013105 = 2259829) B2259829
theorem B15464945 : Blo 1784093 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B1784307 : Blo 1784093 1784307 := bstep (se 1 (by rfl) ⟨1338230, by rfl⟩ : syracuseStep 1784307 = 2676461) B2676461
theorem B2677235 : Blo 1784093 2677235 := bstep (se 1 (by rfl) ⟨2007926, by rfl⟩ : syracuseStep 2677235 = 4015853) B4015853
theorem B1784323 : Blo 1784093 1784323 := bstep (se 1 (by rfl) ⟨1338242, by rfl⟩ : syracuseStep 1784323 = 2676485) B2676485
theorem B9034253 : Blo 1784093 9034253 := bstep (se 3 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 9034253 = 3387845) B3387845
theorem B2677265 : Blo 1784093 2677265 := bstep (se 2 (by rfl) ⟨1003974, by rfl⟩ : syracuseStep 2677265 = 2007949) B2007949
theorem B1784339 : Blo 1784093 1784339 := bstep (se 1 (by rfl) ⟨1338254, by rfl⟩ : syracuseStep 1784339 = 2676509) B2676509
theorem B3013139 : Blo 1784093 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B1784355 : Blo 1784093 1784355 := bstep (se 1 (by rfl) ⟨1338266, by rfl⟩ : syracuseStep 1784355 = 2676533) B2676533
theorem B2677283 : Blo 1784093 2677283 := bstep (se 1 (by rfl) ⟨2007962, by rfl⟩ : syracuseStep 2677283 = 4015925) B4015925
theorem B3389987 : Blo 1784093 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B1784371 : Blo 1784093 1784371 := bstep (se 1 (by rfl) ⟨1338278, by rfl⟩ : syracuseStep 1784371 = 2676557) B2676557
theorem B2677313 : Blo 1784093 2677313 := bstep (se 2 (by rfl) ⟨1003992, by rfl⟩ : syracuseStep 2677313 = 2007985) B2007985
theorem B1784387 : Blo 1784093 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B6027857 : Blo 1784093 6027857 := bstep (se 2 (by rfl) ⟨2260446, by rfl⟩ : syracuseStep 6027857 = 4520893) B4520893
theorem B1784403 : Blo 1784093 1784403 := bstep (se 1 (by rfl) ⟨1338302, by rfl⟩ : syracuseStep 1784403 = 2676605) B2676605
theorem B2677331 : Blo 1784093 2677331 := bstep (se 1 (by rfl) ⟨2007998, by rfl⟩ : syracuseStep 2677331 = 4015997) B4015997
theorem B1784419 : Blo 1784093 1784419 := bstep (se 1 (by rfl) ⟨1338314, by rfl⟩ : syracuseStep 1784419 = 2676629) B2676629
theorem B2677361 : Blo 1784093 2677361 := bstep (se 2 (by rfl) ⟨1004010, by rfl⟩ : syracuseStep 2677361 = 2008021) B2008021
theorem B6781553 : Blo 1784093 6781553 := bstep (se 2 (by rfl) ⟨2543082, by rfl⟩ : syracuseStep 6781553 = 5086165) B5086165
theorem B1784435 : Blo 1784093 1784435 := bstep (se 1 (by rfl) ⟨1338326, by rfl⟩ : syracuseStep 1784435 = 2676653) B2676653
theorem B2259571 : Blo 1784093 2259571 := bstep (se 1 (by rfl) ⟨1694678, by rfl⟩ : syracuseStep 2259571 = 3389357) B3389357
theorem B1784451 : Blo 1784093 1784451 := bstep (se 1 (by rfl) ⟨1338338, by rfl⟩ : syracuseStep 1784451 = 2676677) B2676677
theorem B2677379 : Blo 1784093 2677379 := bstep (se 1 (by rfl) ⟨2008034, by rfl⟩ : syracuseStep 2677379 = 4016069) B4016069
theorem B1784467 : Blo 1784093 1784467 := bstep (se 1 (by rfl) ⟨1338350, by rfl⟩ : syracuseStep 1784467 = 2676701) B2676701
theorem B3013267 : Blo 1784093 3013267 := bstep (se 1 (by rfl) ⟨2259950, by rfl⟩ : syracuseStep 3013267 = 4519901) B4519901
theorem B2677409 : Blo 1784093 2677409 := bstep (se 2 (by rfl) ⟨1004028, by rfl⟩ : syracuseStep 2677409 = 2008057) B2008057
theorem B1784483 : Blo 1784093 1784483 := bstep (se 1 (by rfl) ⟨1338362, by rfl⟩ : syracuseStep 1784483 = 2676725) B2676725
theorem B1784499 : Blo 1784093 1784499 := bstep (se 1 (by rfl) ⟨1338374, by rfl⟩ : syracuseStep 1784499 = 2676749) B2676749
theorem B2677427 : Blo 1784093 2677427 := bstep (se 1 (by rfl) ⟨2008070, by rfl⟩ : syracuseStep 2677427 = 4016141) B4016141
theorem B1784515 : Blo 1784093 1784515 := bstep (se 1 (by rfl) ⟨1338386, by rfl⟩ : syracuseStep 1784515 = 2676773) B2676773
theorem B1784531 : Blo 1784093 1784531 := bstep (se 1 (by rfl) ⟨1338398, by rfl⟩ : syracuseStep 1784531 = 2676797) B2676797
theorem B2677457 : Blo 1784093 2677457 := bstep (se 2 (by rfl) ⟨1004046, by rfl⟩ : syracuseStep 2677457 = 2008093) B2008093
theorem B2259667 : Blo 1784093 2259667 := bstep (se 1 (by rfl) ⟨1694750, by rfl⟩ : syracuseStep 2259667 = 3389501) B3389501
theorem B1784547 : Blo 1784093 1784547 := bstep (se 1 (by rfl) ⟨1338410, by rfl⟩ : syracuseStep 1784547 = 2676821) B2676821
theorem B2677475 : Blo 1784093 2677475 := bstep (se 1 (by rfl) ⟨2008106, by rfl⟩ : syracuseStep 2677475 = 4016213) B4016213
theorem B1784563 : Blo 1784093 1784563 := bstep (se 1 (by rfl) ⟨1338422, by rfl⟩ : syracuseStep 1784563 = 2676845) B2676845
theorem B2677505 : Blo 1784093 2677505 := bstep (se 2 (by rfl) ⟨1004064, by rfl⟩ : syracuseStep 2677505 = 2008129) B2008129
theorem B1784579 : Blo 1784093 1784579 := bstep (se 1 (by rfl) ⟨1338434, by rfl⟩ : syracuseStep 1784579 = 2676869) B2676869
theorem B1784595 : Blo 1784093 1784595 := bstep (se 1 (by rfl) ⟨1338446, by rfl⟩ : syracuseStep 1784595 = 2676893) B2676893
theorem B2677523 : Blo 1784093 2677523 := bstep (se 1 (by rfl) ⟨2008142, by rfl⟩ : syracuseStep 2677523 = 4016285) B4016285
theorem B3013409 : Blo 1784093 3013409 := bstep (se 2 (by rfl) ⟨1130028, by rfl⟩ : syracuseStep 3013409 = 2260057) B2260057
theorem B1784611 : Blo 1784093 1784611 := bstep (se 1 (by rfl) ⟨1338458, by rfl⟩ : syracuseStep 1784611 = 2676917) B2676917
theorem B8575793 : Blo 1784093 8575793 := bstep (se 2 (by rfl) ⟨3215922, by rfl⟩ : syracuseStep 8575793 = 6431845) B6431845
theorem B2677553 : Blo 1784093 2677553 := bstep (se 2 (by rfl) ⟨1004082, by rfl⟩ : syracuseStep 2677553 = 2008165) B2008165
theorem B1784627 : Blo 1784093 1784627 := bstep (se 1 (by rfl) ⟨1338470, by rfl⟩ : syracuseStep 1784627 = 2676941) B2676941
theorem B1784643 : Blo 1784093 1784643 := bstep (se 1 (by rfl) ⟨1338482, by rfl⟩ : syracuseStep 1784643 = 2676965) B2676965
theorem B2677571 : Blo 1784093 2677571 := bstep (se 1 (by rfl) ⟨2008178, by rfl⟩ : syracuseStep 2677571 = 4016357) B4016357
theorem B3390275 : Blo 1784093 3390275 := bstep (se 1 (by rfl) ⟨2542706, by rfl⟩ : syracuseStep 3390275 = 5085413) B5085413
theorem B24771397 : Blo 1784093 24771397 := bstep (se 4 (by rfl) ⟨2322318, by rfl⟩ : syracuseStep 24771397 = 4644637) B4644637
theorem B1784659 : Blo 1784093 1784659 := bstep (se 1 (by rfl) ⟨1338494, by rfl⟩ : syracuseStep 1784659 = 2676989) B2676989
theorem B361782101 : Blo 1784093 361782101 := bstep (se 9 (by rfl) ⟨1059908, by rfl⟩ : syracuseStep 361782101 = 2119817) B2119817
theorem B2677601 : Blo 1784093 2677601 := bstep (se 2 (by rfl) ⟨1004100, by rfl⟩ : syracuseStep 2677601 = 2008201) B2008201
theorem B1784675 : Blo 1784093 1784675 := bstep (se 1 (by rfl) ⟨1338506, by rfl⟩ : syracuseStep 1784675 = 2677013) B2677013
theorem B1784691 : Blo 1784093 1784691 := bstep (se 1 (by rfl) ⟨1338518, by rfl⟩ : syracuseStep 1784691 = 2677037) B2677037
theorem B2677619 : Blo 1784093 2677619 := bstep (se 1 (by rfl) ⟨2008214, by rfl⟩ : syracuseStep 2677619 = 4016429) B4016429
theorem B1784707 : Blo 1784093 1784707 := bstep (se 1 (by rfl) ⟨1338530, by rfl⟩ : syracuseStep 1784707 = 2677061) B2677061
theorem B2677649 : Blo 1784093 2677649 := bstep (se 2 (by rfl) ⟨1004118, by rfl⟩ : syracuseStep 2677649 = 2008237) B2008237
theorem B3619729 : Blo 1784093 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B1784723 : Blo 1784093 1784723 := bstep (se 1 (by rfl) ⟨1338542, by rfl⟩ : syracuseStep 1784723 = 2677085) B2677085
theorem B5086097 : Blo 1784093 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B3013537 : Blo 1784093 3013537 := bstep (se 2 (by rfl) ⟨1130076, by rfl⟩ : syracuseStep 3013537 = 2260153) B2260153
theorem B1784739 : Blo 1784093 1784739 := bstep (se 1 (by rfl) ⟨1338554, by rfl⟩ : syracuseStep 1784739 = 2677109) B2677109
theorem B2677667 : Blo 1784093 2677667 := bstep (se 1 (by rfl) ⟨2008250, by rfl⟩ : syracuseStep 2677667 = 4016501) B4016501
theorem B1784755 : Blo 1784093 1784755 := bstep (se 1 (by rfl) ⟨1338566, by rfl⟩ : syracuseStep 1784755 = 2677133) B2677133
theorem B2677697 : Blo 1784093 2677697 := bstep (se 2 (by rfl) ⟨1004136, by rfl⟩ : syracuseStep 2677697 = 2008273) B2008273
theorem B1784771 : Blo 1784093 1784771 := bstep (se 1 (by rfl) ⟨1338578, by rfl⟩ : syracuseStep 1784771 = 2677157) B2677157
theorem B3013571 : Blo 1784093 3013571 := bstep (se 1 (by rfl) ⟨2260178, by rfl⟩ : syracuseStep 3013571 = 4520357) B4520357
theorem B1784787 : Blo 1784093 1784787 := bstep (se 1 (by rfl) ⟨1338590, by rfl⟩ : syracuseStep 1784787 = 2677181) B2677181
theorem B2677715 : Blo 1784093 2677715 := bstep (se 1 (by rfl) ⟨2008286, by rfl⟩ : syracuseStep 2677715 = 4016573) B4016573
theorem B1784803 : Blo 1784093 1784803 := bstep (se 1 (by rfl) ⟨1338602, by rfl⟩ : syracuseStep 1784803 = 2677205) B2677205
theorem B2145251 : Blo 1784093 2145251 := bstep (se 1 (by rfl) ⟨1608938, by rfl⟩ : syracuseStep 2145251 = 3217877) B3217877
theorem B2677745 : Blo 1784093 2677745 := bstep (se 2 (by rfl) ⟨1004154, by rfl⟩ : syracuseStep 2677745 = 2008309) B2008309
theorem B1784819 : Blo 1784093 1784819 := bstep (se 1 (by rfl) ⟨1338614, by rfl⟩ : syracuseStep 1784819 = 2677229) B2677229
theorem B1784835 : Blo 1784093 1784835 := bstep (se 1 (by rfl) ⟨1338626, by rfl⟩ : syracuseStep 1784835 = 2677253) B2677253
theorem B2677763 : Blo 1784093 2677763 := bstep (se 1 (by rfl) ⟨2008322, by rfl⟩ : syracuseStep 2677763 = 4016645) B4016645
theorem B1784851 : Blo 1784093 1784851 := bstep (se 1 (by rfl) ⟨1338638, by rfl⟩ : syracuseStep 1784851 = 2677277) B2677277
theorem B2677793 : Blo 1784093 2677793 := bstep (se 2 (by rfl) ⟨1004172, by rfl⟩ : syracuseStep 2677793 = 2008345) B2008345
theorem B1784867 : Blo 1784093 1784867 := bstep (se 1 (by rfl) ⟨1338650, by rfl⟩ : syracuseStep 1784867 = 2677301) B2677301
theorem B1784883 : Blo 1784093 1784883 := bstep (se 1 (by rfl) ⟨1338662, by rfl⟩ : syracuseStep 1784883 = 2677325) B2677325
theorem B2677811 : Blo 1784093 2677811 := bstep (se 1 (by rfl) ⟨2008358, by rfl⟩ : syracuseStep 2677811 = 4016717) B4016717
theorem B1784899 : Blo 1784093 1784899 := bstep (se 1 (by rfl) ⟨1338674, by rfl⟩ : syracuseStep 1784899 = 2677349) B2677349
theorem B3013699 : Blo 1784093 3013699 := bstep (se 1 (by rfl) ⟨2260274, by rfl⟩ : syracuseStep 3013699 = 4520549) B4520549
theorem B2677841 : Blo 1784093 2677841 := bstep (se 2 (by rfl) ⟨1004190, by rfl⟩ : syracuseStep 2677841 = 2008381) B2008381
theorem B1784915 : Blo 1784093 1784915 := bstep (se 1 (by rfl) ⟨1338686, by rfl⟩ : syracuseStep 1784915 = 2677373) B2677373
theorem B1784931 : Blo 1784093 1784931 := bstep (se 1 (by rfl) ⟨1338698, by rfl⟩ : syracuseStep 1784931 = 2677397) B2677397
theorem B2677859 : Blo 1784093 2677859 := bstep (se 1 (by rfl) ⟨2008394, by rfl⟩ : syracuseStep 2677859 = 4016789) B4016789
theorem B1784947 : Blo 1784093 1784947 := bstep (se 1 (by rfl) ⟨1338710, by rfl⟩ : syracuseStep 1784947 = 2677421) B2677421
theorem B2677889 : Blo 1784093 2677889 := bstep (se 2 (by rfl) ⟨1004208, by rfl⟩ : syracuseStep 2677889 = 2008417) B2008417
theorem B1784963 : Blo 1784093 1784963 := bstep (se 1 (by rfl) ⟨1338722, by rfl⟩ : syracuseStep 1784963 = 2677445) B2677445
theorem B1784979 : Blo 1784093 1784979 := bstep (se 1 (by rfl) ⟨1338734, by rfl⟩ : syracuseStep 1784979 = 2677469) B2677469
theorem B2677907 : Blo 1784093 2677907 := bstep (se 1 (by rfl) ⟨2008430, by rfl⟩ : syracuseStep 2677907 = 4016861) B4016861
theorem B1784995 : Blo 1784093 1784995 := bstep (se 1 (by rfl) ⟨1338746, by rfl⟩ : syracuseStep 1784995 = 2677493) B2677493
theorem B2677937 : Blo 1784093 2677937 := bstep (se 2 (by rfl) ⟨1004226, by rfl⟩ : syracuseStep 2677937 = 2008453) B2008453
theorem B1785011 : Blo 1784093 1785011 := bstep (se 1 (by rfl) ⟨1338758, by rfl⟩ : syracuseStep 1785011 = 2677517) B2677517
theorem B1785027 : Blo 1784093 1785027 := bstep (se 1 (by rfl) ⟨1338770, by rfl⟩ : syracuseStep 1785027 = 2677541) B2677541
theorem B2677955 : Blo 1784093 2677955 := bstep (se 1 (by rfl) ⟨2008466, by rfl⟩ : syracuseStep 2677955 = 4016933) B4016933
theorem B2260163 : Blo 1784093 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B7625933 : Blo 1784093 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B3013841 : Blo 1784093 3013841 := bstep (se 2 (by rfl) ⟨1130190, by rfl⟩ : syracuseStep 3013841 = 2260381) B2260381
theorem B1785043 : Blo 1784093 1785043 := bstep (se 1 (by rfl) ⟨1338782, by rfl⟩ : syracuseStep 1785043 = 2677565) B2677565
theorem B2677985 : Blo 1784093 2677985 := bstep (se 2 (by rfl) ⟨1004244, by rfl⟩ : syracuseStep 2677985 = 2008489) B2008489
theorem B1785059 : Blo 1784093 1785059 := bstep (se 1 (by rfl) ⟨1338794, by rfl⟩ : syracuseStep 1785059 = 2677589) B2677589
theorem B1785075 : Blo 1784093 1785075 := bstep (se 1 (by rfl) ⟨1338806, by rfl⟩ : syracuseStep 1785075 = 2677613) B2677613
theorem B2678003 : Blo 1784093 2678003 := bstep (se 1 (by rfl) ⟨2008502, by rfl⟩ : syracuseStep 2678003 = 4017005) B4017005
theorem B1785091 : Blo 1784093 1785091 := bstep (se 1 (by rfl) ⟨1338818, by rfl⟩ : syracuseStep 1785091 = 2677637) B2677637
theorem B1785107 : Blo 1784093 1785107 := bstep (se 1 (by rfl) ⟨1338830, by rfl⟩ : syracuseStep 1785107 = 2677661) B2677661
theorem B2678033 : Blo 1784093 2678033 := bstep (se 2 (by rfl) ⟨1004262, by rfl⟩ : syracuseStep 2678033 = 2008525) B2008525
theorem B1785123 : Blo 1784093 1785123 := bstep (se 1 (by rfl) ⟨1338842, by rfl⟩ : syracuseStep 1785123 = 2677685) B2677685
theorem B2678051 : Blo 1784093 2678051 := bstep (se 1 (by rfl) ⟨2008538, by rfl⟩ : syracuseStep 2678051 = 4017077) B4017077
theorem B5717297 : Blo 1784093 5717297 := bstep (se 2 (by rfl) ⟨2143986, by rfl⟩ : syracuseStep 5717297 = 4287973) B4287973
theorem B1785139 : Blo 1784093 1785139 := bstep (se 1 (by rfl) ⟨1338854, by rfl⟩ : syracuseStep 1785139 = 2677709) B2677709
theorem B2678081 : Blo 1784093 2678081 := bstep (se 2 (by rfl) ⟨1004280, by rfl⟩ : syracuseStep 2678081 = 2008561) B2008561
theorem B1785155 : Blo 1784093 1785155 := bstep (se 1 (by rfl) ⟨1338866, by rfl⟩ : syracuseStep 1785155 = 2677733) B2677733
theorem B3013969 : Blo 1784093 3013969 := bstep (se 2 (by rfl) ⟨1130238, by rfl⟩ : syracuseStep 3013969 = 2260477) B2260477
theorem B1785171 : Blo 1784093 1785171 := bstep (se 1 (by rfl) ⟨1338878, by rfl⟩ : syracuseStep 1785171 = 2677757) B2677757
theorem B2678099 : Blo 1784093 2678099 := bstep (se 1 (by rfl) ⟨2008574, by rfl⟩ : syracuseStep 2678099 = 4017149) B4017149
theorem B19299683 : Blo 1784093 19299683 := bstep (se 1 (by rfl) ⟨14474762, by rfl⟩ : syracuseStep 19299683 = 28949525) B28949525
theorem B1785187 : Blo 1784093 1785187 := bstep (se 1 (by rfl) ⟨1338890, by rfl⟩ : syracuseStep 1785187 = 2677781) B2677781
theorem B2678129 : Blo 1784093 2678129 := bstep (se 2 (by rfl) ⟨1004298, by rfl⟩ : syracuseStep 2678129 = 2008597) B2008597
theorem B1785203 : Blo 1784093 1785203 := bstep (se 1 (by rfl) ⟨1338902, by rfl⟩ : syracuseStep 1785203 = 2677805) B2677805
theorem B3014003 : Blo 1784093 3014003 := bstep (se 1 (by rfl) ⟨2260502, by rfl⟩ : syracuseStep 3014003 = 4521005) B4521005
theorem B1785219 : Blo 1784093 1785219 := bstep (se 1 (by rfl) ⟨1338914, by rfl⟩ : syracuseStep 1785219 = 2677829) B2677829
theorem B2678147 : Blo 1784093 2678147 := bstep (se 1 (by rfl) ⟨2008610, by rfl⟩ : syracuseStep 2678147 = 4017221) B4017221
theorem B1785235 : Blo 1784093 1785235 := bstep (se 1 (by rfl) ⟨1338926, by rfl⟩ : syracuseStep 1785235 = 2677853) B2677853
theorem B2678177 : Blo 1784093 2678177 := bstep (se 2 (by rfl) ⟨1004316, by rfl⟩ : syracuseStep 2678177 = 2008633) B2008633
theorem B1785251 : Blo 1784093 1785251 := bstep (se 1 (by rfl) ⟨1338938, by rfl⟩ : syracuseStep 1785251 = 2677877) B2677877
theorem B1785267 : Blo 1784093 1785267 := bstep (se 1 (by rfl) ⟨1338950, by rfl⟩ : syracuseStep 1785267 = 2677901) B2677901
theorem B2678195 : Blo 1784093 2678195 := bstep (se 1 (by rfl) ⟨2008646, by rfl⟩ : syracuseStep 2678195 = 4017293) B4017293
theorem B1785283 : Blo 1784093 1785283 := bstep (se 1 (by rfl) ⟨1338962, by rfl⟩ : syracuseStep 1785283 = 2677925) B2677925
theorem B2678225 : Blo 1784093 2678225 := bstep (se 2 (by rfl) ⟨1004334, by rfl⟩ : syracuseStep 2678225 = 2008669) B2008669
theorem B1785299 : Blo 1784093 1785299 := bstep (se 1 (by rfl) ⟨1338974, by rfl⟩ : syracuseStep 1785299 = 2677949) B2677949
theorem B1785315 : Blo 1784093 1785315 := bstep (se 1 (by rfl) ⟨1338986, by rfl⟩ : syracuseStep 1785315 = 2677973) B2677973
theorem B2678243 : Blo 1784093 2678243 := bstep (se 1 (by rfl) ⟨2008682, by rfl⟩ : syracuseStep 2678243 = 4017365) B4017365
theorem B1785331 : Blo 1784093 1785331 := bstep (se 1 (by rfl) ⟨1338998, by rfl⟩ : syracuseStep 1785331 = 2677997) B2677997
theorem B2678273 : Blo 1784093 2678273 := bstep (se 2 (by rfl) ⟨1004352, by rfl⟩ : syracuseStep 2678273 = 2008705) B2008705
theorem B1785347 : Blo 1784093 1785347 := bstep (se 1 (by rfl) ⟨1339010, by rfl⟩ : syracuseStep 1785347 = 2678021) B2678021
theorem B1785363 : Blo 1784093 1785363 := bstep (se 1 (by rfl) ⟨1339022, by rfl⟩ : syracuseStep 1785363 = 2678045) B2678045
theorem B2678291 : Blo 1784093 2678291 := bstep (se 1 (by rfl) ⟨2008718, by rfl⟩ : syracuseStep 2678291 = 4017437) B4017437
theorem B1785379 : Blo 1784093 1785379 := bstep (se 1 (by rfl) ⟨1339034, by rfl⟩ : syracuseStep 1785379 = 2678069) B2678069
theorem B7626275 : Blo 1784093 7626275 := bstep (se 1 (by rfl) ⟨5719706, by rfl⟩ : syracuseStep 7626275 = 11439413) B11439413
theorem B2678321 : Blo 1784093 2678321 := bstep (se 2 (by rfl) ⟨1004370, by rfl⟩ : syracuseStep 2678321 = 2008741) B2008741
theorem B1785395 : Blo 1784093 1785395 := bstep (se 1 (by rfl) ⟨1339046, by rfl⟩ : syracuseStep 1785395 = 2678093) B2678093
theorem B1785411 : Blo 1784093 1785411 := bstep (se 1 (by rfl) ⟨1339058, by rfl⟩ : syracuseStep 1785411 = 2678117) B2678117
theorem B2678339 : Blo 1784093 2678339 := bstep (se 1 (by rfl) ⟨2008754, by rfl⟩ : syracuseStep 2678339 = 4017509) B4017509
theorem B1785427 : Blo 1784093 1785427 := bstep (se 1 (by rfl) ⟨1339070, by rfl⟩ : syracuseStep 1785427 = 2678141) B2678141
theorem B2678369 : Blo 1784093 2678369 := bstep (se 2 (by rfl) ⟨1004388, by rfl⟩ : syracuseStep 2678369 = 2008777) B2008777
theorem B1785443 : Blo 1784093 1785443 := bstep (se 1 (by rfl) ⟨1339082, by rfl⟩ : syracuseStep 1785443 = 2678165) B2678165
theorem B1785459 : Blo 1784093 1785459 := bstep (se 1 (by rfl) ⟨1339094, by rfl⟩ : syracuseStep 1785459 = 2678189) B2678189
theorem B2678387 : Blo 1784093 2678387 := bstep (se 1 (by rfl) ⟨2008790, by rfl⟩ : syracuseStep 2678387 = 4017581) B4017581
theorem B1785475 : Blo 1784093 1785475 := bstep (se 1 (by rfl) ⟨1339106, by rfl⟩ : syracuseStep 1785475 = 2678213) B2678213
theorem B2678417 : Blo 1784093 2678417 := bstep (se 2 (by rfl) ⟨1004406, by rfl⟩ : syracuseStep 2678417 = 2008813) B2008813
theorem B1785491 : Blo 1784093 1785491 := bstep (se 1 (by rfl) ⟨1339118, by rfl⟩ : syracuseStep 1785491 = 2678237) B2678237
theorem B1785507 : Blo 1784093 1785507 := bstep (se 1 (by rfl) ⟨1339130, by rfl⟩ : syracuseStep 1785507 = 2678261) B2678261
theorem B2678435 : Blo 1784093 2678435 := bstep (se 1 (by rfl) ⟨2008826, by rfl⟩ : syracuseStep 2678435 = 4017653) B4017653
theorem B1785523 : Blo 1784093 1785523 := bstep (se 1 (by rfl) ⟨1339142, by rfl⟩ : syracuseStep 1785523 = 2678285) B2678285
theorem B1785539 : Blo 1784093 1785539 := bstep (se 1 (by rfl) ⟨1339154, by rfl⟩ : syracuseStep 1785539 = 2678309) B2678309
theorem B2678465 : Blo 1784093 2678465 := bstep (se 2 (by rfl) ⟨1004424, by rfl⟩ : syracuseStep 2678465 = 2008849) B2008849
theorem B6192845 : Blo 1784093 6192845 := bstep (se 3 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 6192845 = 2322317) B2322317
theorem B1785555 : Blo 1784093 1785555 := bstep (se 1 (by rfl) ⟨1339166, by rfl⟩ : syracuseStep 1785555 = 2678333) B2678333
theorem B2678483 : Blo 1784093 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B1785571 : Blo 1784093 1785571 := bstep (se 1 (by rfl) ⟨1339178, by rfl⟩ : syracuseStep 1785571 = 2678357) B2678357
theorem B2678513 : Blo 1784093 2678513 := bstep (se 2 (by rfl) ⟨1004442, by rfl⟩ : syracuseStep 2678513 = 2008885) B2008885
theorem B1785587 : Blo 1784093 1785587 := bstep (se 1 (by rfl) ⟨1339190, by rfl⟩ : syracuseStep 1785587 = 2678381) B2678381
theorem B1785603 : Blo 1784093 1785603 := bstep (se 1 (by rfl) ⟨1339202, by rfl⟩ : syracuseStep 1785603 = 2678405) B2678405
theorem B2678531 : Blo 1784093 2678531 := bstep (se 1 (by rfl) ⟨2008898, by rfl⟩ : syracuseStep 2678531 = 4017797) B4017797
theorem B1785619 : Blo 1784093 1785619 := bstep (se 1 (by rfl) ⟨1339214, by rfl⟩ : syracuseStep 1785619 = 2678429) B2678429
theorem B2678561 : Blo 1784093 2678561 := bstep (se 2 (by rfl) ⟨1004460, by rfl⟩ : syracuseStep 2678561 = 2008921) B2008921
theorem B1785635 : Blo 1784093 1785635 := bstep (se 1 (by rfl) ⟨1339226, by rfl⟩ : syracuseStep 1785635 = 2678453) B2678453
theorem B7733027 : Blo 1784093 7733027 := bstep (se 1 (by rfl) ⟨5799770, by rfl⟩ : syracuseStep 7733027 = 11599541) B11599541
theorem B1785651 : Blo 1784093 1785651 := bstep (se 1 (by rfl) ⟨1339238, by rfl⟩ : syracuseStep 1785651 = 2678477) B2678477
theorem B2678579 : Blo 1784093 2678579 := bstep (se 1 (by rfl) ⟨2008934, by rfl⟩ : syracuseStep 2678579 = 4017869) B4017869
theorem B7241521 : Blo 1784093 7241521 := bstep (se 2 (by rfl) ⟨2715570, by rfl⟩ : syracuseStep 7241521 = 5431141) B5431141
theorem B1785667 : Blo 1784093 1785667 := bstep (se 1 (by rfl) ⟨1339250, by rfl⟩ : syracuseStep 1785667 = 2678501) B2678501
theorem B2678609 : Blo 1784093 2678609 := bstep (se 2 (by rfl) ⟨1004478, by rfl⟩ : syracuseStep 2678609 = 2008957) B2008957
theorem B1785683 : Blo 1784093 1785683 := bstep (se 1 (by rfl) ⟨1339262, by rfl⟩ : syracuseStep 1785683 = 2678525) B2678525
theorem B1785699 : Blo 1784093 1785699 := bstep (se 1 (by rfl) ⟨1339274, by rfl⟩ : syracuseStep 1785699 = 2678549) B2678549
theorem B2678627 : Blo 1784093 2678627 := bstep (se 1 (by rfl) ⟨2008970, by rfl⟩ : syracuseStep 2678627 = 4017941) B4017941
theorem B1785715 : Blo 1784093 1785715 := bstep (se 1 (by rfl) ⟨1339286, by rfl⟩ : syracuseStep 1785715 = 2678573) B2678573
theorem B2678657 : Blo 1784093 2678657 := bstep (se 2 (by rfl) ⟨1004496, by rfl⟩ : syracuseStep 2678657 = 2008993) B2008993
theorem B1785731 : Blo 1784093 1785731 := bstep (se 1 (by rfl) ⟨1339298, by rfl⟩ : syracuseStep 1785731 = 2678597) B2678597
theorem B1785747 : Blo 1784093 1785747 := bstep (se 1 (by rfl) ⟨1339310, by rfl⟩ : syracuseStep 1785747 = 2678621) B2678621
theorem B2678675 : Blo 1784093 2678675 := bstep (se 1 (by rfl) ⟨2009006, by rfl⟩ : syracuseStep 2678675 = 4018013) B4018013
theorem B1785763 : Blo 1784093 1785763 := bstep (se 1 (by rfl) ⟨1339322, by rfl⟩ : syracuseStep 1785763 = 2678645) B2678645
theorem B2678705 : Blo 1784093 2678705 := bstep (se 2 (by rfl) ⟨1004514, by rfl⟩ : syracuseStep 2678705 = 2009029) B2009029
theorem B1785779 : Blo 1784093 1785779 := bstep (se 1 (by rfl) ⟨1339334, by rfl⟩ : syracuseStep 1785779 = 2678669) B2678669
theorem B1785795 : Blo 1784093 1785795 := bstep (se 1 (by rfl) ⟨1339346, by rfl⟩ : syracuseStep 1785795 = 2678693) B2678693
theorem B2678723 : Blo 1784093 2678723 := bstep (se 1 (by rfl) ⟨2009042, by rfl⟩ : syracuseStep 2678723 = 4018085) B4018085
theorem B1785811 : Blo 1784093 1785811 := bstep (se 1 (by rfl) ⟨1339358, by rfl⟩ : syracuseStep 1785811 = 2678717) B2678717
theorem B2678753 : Blo 1784093 2678753 := bstep (se 2 (by rfl) ⟨1004532, by rfl⟩ : syracuseStep 2678753 = 2009065) B2009065
theorem B6430691 : Blo 1784093 6430691 := bstep (se 1 (by rfl) ⟨4823018, by rfl⟩ : syracuseStep 6430691 = 9646037) B9646037
theorem B1785827 : Blo 1784093 1785827 := bstep (se 1 (by rfl) ⟨1339370, by rfl⟩ : syracuseStep 1785827 = 2678741) B2678741
theorem B7626737 : Blo 1784093 7626737 := bstep (se 2 (by rfl) ⟨2860026, by rfl⟩ : syracuseStep 7626737 = 5720053) B5720053
theorem B1785843 : Blo 1784093 1785843 := bstep (se 1 (by rfl) ⟨1339382, by rfl⟩ : syracuseStep 1785843 = 2678765) B2678765
theorem B2678771 : Blo 1784093 2678771 := bstep (se 1 (by rfl) ⟨2009078, by rfl⟩ : syracuseStep 2678771 = 4018157) B4018157
theorem B2678795 : Blo 1784093 2678795 := bstep (se 1 (by rfl) ⟨2009096, by rfl⟩ : syracuseStep 2678795 = 4018193) B4018193
theorem B1785867 : Blo 1784093 1785867 := bstep (se 1 (by rfl) ⟨1339400, by rfl⟩ : syracuseStep 1785867 = 2678801) B2678801
theorem B2678807 : Blo 1784093 2678807 := bstep (se 1 (by rfl) ⟨2009105, by rfl⟩ : syracuseStep 2678807 = 4018211) B4018211
theorem B1785879 : Blo 1784093 1785879 := bstep (se 1 (by rfl) ⟨1339409, by rfl⟩ : syracuseStep 1785879 = 2678819) B2678819
theorem B1785899 : Blo 1784093 1785899 := bstep (se 1 (by rfl) ⟨1339424, by rfl⟩ : syracuseStep 1785899 = 2678849) B2678849
theorem B1785911 : Blo 1784093 1785911 := bstep (se 1 (by rfl) ⟨1339433, by rfl⟩ : syracuseStep 1785911 = 2678867) B2678867
theorem B1785931 : Blo 1784093 1785931 := bstep (se 1 (by rfl) ⟨1339448, by rfl⟩ : syracuseStep 1785931 = 2678897) B2678897
theorem B1785943 : Blo 1784093 1785943 := bstep (se 1 (by rfl) ⟨1339457, by rfl⟩ : syracuseStep 1785943 = 2678915) B2678915
theorem B2678873 : Blo 1784093 2678873 := bstep (se 2 (by rfl) ⟨1004577, by rfl⟩ : syracuseStep 2678873 = 2009155) B2009155
theorem B10862693 : Blo 1784093 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B1785963 : Blo 1784093 1785963 := bstep (se 1 (by rfl) ⟨1339472, by rfl⟩ : syracuseStep 1785963 = 2678945) B2678945
theorem B1785975 : Blo 1784093 1785975 := bstep (se 1 (by rfl) ⟨1339481, by rfl⟩ : syracuseStep 1785975 = 2678963) B2678963
theorem B1785995 : Blo 1784093 1785995 := bstep (se 1 (by rfl) ⟨1339496, by rfl⟩ : syracuseStep 1785995 = 2678993) B2678993
theorem B13246615 : Blo 1784093 13246615 := bstep (se 1 (by rfl) ⟨9934961, by rfl⟩ : syracuseStep 13246615 = 19869923) B19869923
theorem B1786007 : Blo 1784093 1786007 := bstep (se 1 (by rfl) ⟨1339505, by rfl⟩ : syracuseStep 1786007 = 2679011) B2679011
theorem B4014233 : Blo 1784093 4014233 := bstep (se 2 (by rfl) ⟨1505337, by rfl⟩ : syracuseStep 4014233 = 3010675) B3010675
theorem B2007211 : Blo 1784093 2007211 := bstep (se 1 (by rfl) ⟨1505408, by rfl⟩ : syracuseStep 2007211 = 3010817) B3010817
theorem B1786027 : Blo 1784093 1786027 := bstep (se 1 (by rfl) ⟨1339520, by rfl⟩ : syracuseStep 1786027 = 2679041) B2679041
theorem B1786039 : Blo 1784093 1786039 := bstep (se 1 (by rfl) ⟨1339529, by rfl⟩ : syracuseStep 1786039 = 2679059) B2679059
theorem B6021323 : Blo 1784093 6021323 := bstep (se 1 (by rfl) ⟨4515992, by rfl⟩ : syracuseStep 6021323 = 9031985) B9031985
theorem B2678987 : Blo 1784093 2678987 := bstep (se 1 (by rfl) ⟨2009240, by rfl⟩ : syracuseStep 2678987 = 4018481) B4018481
theorem B1786059 : Blo 1784093 1786059 := bstep (se 1 (by rfl) ⟨1339544, by rfl⟩ : syracuseStep 1786059 = 2679089) B2679089
theorem B2678999 : Blo 1784093 2678999 := bstep (se 1 (by rfl) ⟨2009249, by rfl⟩ : syracuseStep 2678999 = 4018499) B4018499
theorem B1786071 : Blo 1784093 1786071 := bstep (se 1 (by rfl) ⟨1339553, by rfl⟩ : syracuseStep 1786071 = 2679107) B2679107
theorem B1786091 : Blo 1784093 1786091 := bstep (se 1 (by rfl) ⟨1339568, by rfl⟩ : syracuseStep 1786091 = 2679137) B2679137
theorem B4014323 : Blo 1784093 4014323 := bstep (se 1 (by rfl) ⟨3010742, by rfl⟩ : syracuseStep 4014323 = 6021485) B6021485
theorem B4014359 : Blo 1784093 4014359 := bstep (se 1 (by rfl) ⟨3010769, by rfl⟩ : syracuseStep 4014359 = 6021539) B6021539
theorem B2007319 : Blo 1784093 2007319 := bstep (se 1 (by rfl) ⟨1505489, by rfl⟩ : syracuseStep 2007319 = 3010979) B3010979
theorem B2679065 : Blo 1784093 2679065 := bstep (se 2 (by rfl) ⟨1004649, by rfl⟩ : syracuseStep 2679065 = 2009299) B2009299
theorem B5718451 : Blo 1784093 5718451 := bstep (se 1 (by rfl) ⟨4288838, by rfl⟩ : syracuseStep 5718451 = 8577677) B8577677
theorem B4014539 : Blo 1784093 4014539 := bstep (se 1 (by rfl) ⟨3010904, by rfl⟩ : syracuseStep 4014539 = 6021809) B6021809
theorem B2007499 : Blo 1784093 2007499 := bstep (se 1 (by rfl) ⟨1505624, by rfl⟩ : syracuseStep 2007499 = 3011249) B3011249
theorem B6021593 : Blo 1784093 6021593 := bstep (se 2 (by rfl) ⟨2258097, by rfl⟩ : syracuseStep 6021593 = 4516195) B4516195
theorem B4014593 : Blo 1784093 4014593 := bstep (se 2 (by rfl) ⟨1505472, by rfl⟩ : syracuseStep 4014593 = 3010945) B3010945
theorem B30491153 : Blo 1784093 30491153 := bstep (se 2 (by rfl) ⟨11434182, by rfl⟩ : syracuseStep 30491153 = 22868365) B22868365
theorem B2007607 : Blo 1784093 2007607 := bstep (se 1 (by rfl) ⟨1505705, by rfl⟩ : syracuseStep 2007607 = 3011411) B3011411
theorem B6775447 : Blo 1784093 6775447 := bstep (se 1 (by rfl) ⟨5081585, by rfl⟩ : syracuseStep 6775447 = 10163171) B10163171
theorem B28959383 : Blo 1784093 28959383 := bstep (se 1 (by rfl) ⟨21719537, by rfl⟩ : syracuseStep 28959383 = 43439075) B43439075
theorem B5718721 : Blo 1784093 5718721 := bstep (se 2 (by rfl) ⟨2144520, by rfl⟩ : syracuseStep 5718721 = 4289041) B4289041
theorem B4014809 : Blo 1784093 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B2007787 : Blo 1784093 2007787 := bstep (se 1 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 2007787 = 3011681) B3011681
theorem B4014899 : Blo 1784093 4014899 := bstep (se 1 (by rfl) ⟨3011174, by rfl⟩ : syracuseStep 4014899 = 6022349) B6022349
theorem B4014935 : Blo 1784093 4014935 := bstep (se 1 (by rfl) ⟨3011201, by rfl⟩ : syracuseStep 4014935 = 6022403) B6022403
theorem B2007895 : Blo 1784093 2007895 := bstep (se 1 (by rfl) ⟨1505921, by rfl⟩ : syracuseStep 2007895 = 3011843) B3011843
theorem B3261377 : Blo 1784093 3261377 := bstep (se 2 (by rfl) ⟨1223016, by rfl⟩ : syracuseStep 3261377 = 2446033) B2446033
theorem B4015115 : Blo 1784093 4015115 := bstep (se 1 (by rfl) ⟨3011336, by rfl⟩ : syracuseStep 4015115 = 6022673) B6022673
theorem B2008075 : Blo 1784093 2008075 := bstep (se 1 (by rfl) ⟨1506056, by rfl⟩ : syracuseStep 2008075 = 3012113) B3012113
theorem B9036845 : Blo 1784093 9036845 := bstep (se 3 (by rfl) ⟨1694408, by rfl⟩ : syracuseStep 9036845 = 3388817) B3388817
theorem B4015169 : Blo 1784093 4015169 := bstep (se 2 (by rfl) ⟨1505688, by rfl⟩ : syracuseStep 4015169 = 3011377) B3011377
theorem B2008183 : Blo 1784093 2008183 := bstep (se 1 (by rfl) ⟨1506137, by rfl⟩ : syracuseStep 2008183 = 3012275) B3012275
theorem B15246467 : Blo 1784093 15246467 := bstep (se 1 (by rfl) ⟨11434850, by rfl⟩ : syracuseStep 15246467 = 22869701) B22869701
theorem B6022295 : Blo 1784093 6022295 := bstep (se 1 (by rfl) ⟨4516721, by rfl⟩ : syracuseStep 6022295 = 9033443) B9033443
theorem B11748503 : Blo 1784093 11748503 := bstep (se 1 (by rfl) ⟨8811377, by rfl⟩ : syracuseStep 11748503 = 17622755) B17622755
theorem B4826305 : Blo 1784093 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B4015385 : Blo 1784093 4015385 := bstep (se 2 (by rfl) ⟨1505769, by rfl⟩ : syracuseStep 4015385 = 3011539) B3011539
theorem B2008363 : Blo 1784093 2008363 := bstep (se 1 (by rfl) ⟨1506272, by rfl⟩ : syracuseStep 2008363 = 3012545) B3012545
theorem B3810635 : Blo 1784093 3810635 := bstep (se 1 (by rfl) ⟨2857976, by rfl⟩ : syracuseStep 3810635 = 5715953) B5715953
theorem B4015475 : Blo 1784093 4015475 := bstep (se 1 (by rfl) ⟨3011606, by rfl⟩ : syracuseStep 4015475 = 6023213) B6023213
theorem B4015511 : Blo 1784093 4015511 := bstep (se 1 (by rfl) ⟨3011633, by rfl⟩ : syracuseStep 4015511 = 6023267) B6023267
theorem B11437463 : Blo 1784093 11437463 := bstep (se 1 (by rfl) ⟨8578097, by rfl⟩ : syracuseStep 11437463 = 17156195) B17156195
theorem B2008471 : Blo 1784093 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B6776237 : Blo 1784093 6776237 := bstep (se 3 (by rfl) ⟨1270544, by rfl⟩ : syracuseStep 6776237 = 2541089) B2541089
theorem B4015691 : Blo 1784093 4015691 := bstep (se 1 (by rfl) ⟨3011768, by rfl⟩ : syracuseStep 4015691 = 6023537) B6023537
theorem B2008651 : Blo 1784093 2008651 := bstep (se 1 (by rfl) ⟨1506488, by rfl⟩ : syracuseStep 2008651 = 3012977) B3012977
theorem B7628377 : Blo 1784093 7628377 := bstep (se 2 (by rfl) ⟨2860641, by rfl⟩ : syracuseStep 7628377 = 5721283) B5721283
theorem B4015745 : Blo 1784093 4015745 := bstep (se 2 (by rfl) ⟨1505904, by rfl⟩ : syracuseStep 4015745 = 3011809) B3011809
theorem B6022835 : Blo 1784093 6022835 := bstep (se 1 (by rfl) ⟨4517126, by rfl⟩ : syracuseStep 6022835 = 9034253) B9034253
theorem B2008759 : Blo 1784093 2008759 := bstep (se 1 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 2008759 = 3013139) B3013139
theorem B4835095 : Blo 1784093 4835095 := bstep (se 1 (by rfl) ⟨3626321, by rfl⟩ : syracuseStep 4835095 = 7252643) B7252643
theorem B4015961 : Blo 1784093 4015961 := bstep (se 2 (by rfl) ⟨1505985, by rfl⟩ : syracuseStep 4015961 = 3011971) B3011971
theorem B16287581 : Blo 1784093 16287581 := bstep (se 3 (by rfl) ⟨3053921, by rfl⟩ : syracuseStep 16287581 = 6107843) B6107843
theorem B2008939 : Blo 1784093 2008939 := bstep (se 1 (by rfl) ⟨1506704, by rfl⟩ : syracuseStep 2008939 = 3013409) B3013409
theorem B21718961 : Blo 1784093 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B4016051 : Blo 1784093 4016051 := bstep (se 1 (by rfl) ⟨3012038, by rfl⟩ : syracuseStep 4016051 = 6024077) B6024077
theorem B6023105 : Blo 1784093 6023105 := bstep (se 2 (by rfl) ⟨2258664, by rfl⟩ : syracuseStep 6023105 = 4517329) B4517329
theorem B4016087 : Blo 1784093 4016087 := bstep (se 1 (by rfl) ⟨3012065, by rfl⟩ : syracuseStep 4016087 = 6024131) B6024131
theorem B2009047 : Blo 1784093 2009047 := bstep (se 1 (by rfl) ⟨1506785, by rfl⟩ : syracuseStep 2009047 = 3013571) B3013571
theorem B14469185 : Blo 1784093 14469185 := bstep (se 2 (by rfl) ⟨5425944, by rfl⟩ : syracuseStep 14469185 = 10851889) B10851889
theorem B20621405 : Blo 1784093 20621405 := bstep (se 3 (by rfl) ⟨3866513, by rfl⟩ : syracuseStep 20621405 = 7733027) B7733027
theorem B4016267 : Blo 1784093 4016267 := bstep (se 1 (by rfl) ⟨3012200, by rfl⟩ : syracuseStep 4016267 = 6024401) B6024401
theorem B2009227 : Blo 1784093 2009227 := bstep (se 1 (by rfl) ⟨1506920, by rfl⟩ : syracuseStep 2009227 = 3013841) B3013841
theorem B5081267 : Blo 1784093 5081267 := bstep (se 1 (by rfl) ⟨3810950, by rfl⟩ : syracuseStep 5081267 = 7621901) B7621901
theorem B4516033 : Blo 1784093 4516033 := bstep (se 2 (by rfl) ⟨1693512, by rfl⟩ : syracuseStep 4516033 = 3387025) B3387025
theorem B4016321 : Blo 1784093 4016321 := bstep (se 2 (by rfl) ⟨1506120, by rfl⟩ : syracuseStep 4016321 = 3012241) B3012241
theorem B3811531 : Blo 1784093 3811531 := bstep (se 1 (by rfl) ⟨2858648, by rfl⟩ : syracuseStep 3811531 = 5717297) B5717297
theorem B2009335 : Blo 1784093 2009335 := bstep (se 1 (by rfl) ⟨1507001, by rfl⟩ : syracuseStep 2009335 = 3014003) B3014003
theorem B4016537 : Blo 1784093 4016537 := bstep (se 2 (by rfl) ⟨1506201, by rfl⟩ : syracuseStep 4016537 = 3012403) B3012403
theorem B6023645 : Blo 1784093 6023645 := bstep (se 3 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 6023645 = 2258867) B2258867
theorem B4016627 : Blo 1784093 4016627 := bstep (se 1 (by rfl) ⟨3012470, by rfl⟩ : syracuseStep 4016627 = 6024941) B6024941
theorem B4016663 : Blo 1784093 4016663 := bstep (se 1 (by rfl) ⟨3012497, by rfl⟩ : syracuseStep 4016663 = 6024995) B6024995
theorem B17148509 : Blo 1784093 17148509 := bstep (se 3 (by rfl) ⟨3215345, by rfl⟩ : syracuseStep 17148509 = 6430691) B6430691
theorem B5720669 : Blo 1784093 5720669 := bstep (se 3 (by rfl) ⟨1072625, by rfl⟩ : syracuseStep 5720669 = 2145251) B2145251
theorem B4016843 : Blo 1784093 4016843 := bstep (se 1 (by rfl) ⟨3012632, by rfl⟩ : syracuseStep 4016843 = 6025265) B6025265
theorem B4016897 : Blo 1784093 4016897 := bstep (se 2 (by rfl) ⟨1506336, by rfl⟩ : syracuseStep 4016897 = 3012673) B3012673
theorem B4516631 : Blo 1784093 4516631 := bstep (se 1 (by rfl) ⟨3387473, by rfl⟩ : syracuseStep 4516631 = 6774947) B6774947
theorem B6777665 : Blo 1784093 6777665 := bstep (se 2 (by rfl) ⟨2541624, by rfl⟩ : syracuseStep 6777665 = 5083249) B5083249
theorem B5499827 : Blo 1784093 5499827 := bstep (se 1 (by rfl) ⟨4124870, by rfl⟩ : syracuseStep 5499827 = 8249741) B8249741
theorem B3812275 : Blo 1784093 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B4017113 : Blo 1784093 4017113 := bstep (se 2 (by rfl) ⟨1506417, by rfl⟩ : syracuseStep 4017113 = 3012835) B3012835
theorem B4287511 : Blo 1784093 4287511 := bstep (se 1 (by rfl) ⟨3215633, by rfl⟩ : syracuseStep 4287511 = 6431267) B6431267
theorem B4017203 : Blo 1784093 4017203 := bstep (se 1 (by rfl) ⟨3012902, by rfl⟩ : syracuseStep 4017203 = 6025805) B6025805
theorem B4017239 : Blo 1784093 4017239 := bstep (se 1 (by rfl) ⟨3012929, by rfl⟩ : syracuseStep 4017239 = 6025859) B6025859
theorem B4017419 : Blo 1784093 4017419 := bstep (se 1 (by rfl) ⟨3013064, by rfl⟩ : syracuseStep 4017419 = 6026129) B6026129
theorem B4017473 : Blo 1784093 4017473 := bstep (se 2 (by rfl) ⟨1506552, by rfl⟩ : syracuseStep 4017473 = 3013105) B3013105
theorem B3812761 : Blo 1784093 3812761 := bstep (se 2 (by rfl) ⟨1429785, by rfl⟩ : syracuseStep 3812761 = 2859571) B2859571
theorem B15248857 : Blo 1784093 15248857 := bstep (se 2 (by rfl) ⟨5718321, by rfl⟩ : syracuseStep 15248857 = 11436643) B11436643
theorem B4017689 : Blo 1784093 4017689 := bstep (se 2 (by rfl) ⟨1506633, by rfl⟩ : syracuseStep 4017689 = 3013267) B3013267
theorem B4517441 : Blo 1784093 4517441 := bstep (se 2 (by rfl) ⟨1694040, by rfl⟩ : syracuseStep 4517441 = 3388081) B3388081
theorem B6024779 : Blo 1784093 6024779 := bstep (se 1 (by rfl) ⟨4518584, by rfl⟩ : syracuseStep 6024779 = 9037169) B9037169
theorem B4017779 : Blo 1784093 4017779 := bstep (se 1 (by rfl) ⟨3013334, by rfl⟩ : syracuseStep 4017779 = 6026669) B6026669
theorem B4017815 : Blo 1784093 4017815 := bstep (se 1 (by rfl) ⟨3013361, by rfl⟩ : syracuseStep 4017815 = 6026723) B6026723
theorem B4017995 : Blo 1784093 4017995 := bstep (se 1 (by rfl) ⟨3013496, by rfl⟩ : syracuseStep 4017995 = 6026993) B6026993
theorem B6025049 : Blo 1784093 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B4018049 : Blo 1784093 4018049 := bstep (se 2 (by rfl) ⟨1506768, by rfl⟩ : syracuseStep 4018049 = 3013537) B3013537
theorem B9654167 : Blo 1784093 9654167 := bstep (se 1 (by rfl) ⟨7240625, by rfl⟩ : syracuseStep 9654167 = 14481251) B14481251
theorem B3387329 : Blo 1784093 3387329 := bstep (se 2 (by rfl) ⟨1270248, by rfl⟩ : syracuseStep 3387329 = 2540497) B2540497
theorem B15257605 : Blo 1784093 15257605 := bstep (se 4 (by rfl) ⟨1430400, by rfl⟩ : syracuseStep 15257605 = 2860801) B2860801
theorem B4517977 : Blo 1784093 4517977 := bstep (se 2 (by rfl) ⟨1694241, by rfl⟩ : syracuseStep 4517977 = 3388483) B3388483
theorem B4018265 : Blo 1784093 4018265 := bstep (se 2 (by rfl) ⟨1506849, by rfl⟩ : syracuseStep 4018265 = 3013699) B3013699
theorem B14471261 : Blo 1784093 14471261 := bstep (se 3 (by rfl) ⟨2713361, by rfl⟩ : syracuseStep 14471261 = 5426723) B5426723
theorem B10170461 : Blo 1784093 10170461 := bstep (se 3 (by rfl) ⟨1906961, by rfl⟩ : syracuseStep 10170461 = 3813923) B3813923
theorem B4018355 : Blo 1784093 4018355 := bstep (se 1 (by rfl) ⟨3013766, by rfl⟩ : syracuseStep 4018355 = 6027533) B6027533
theorem B3010763 : Blo 1784093 3010763 := bstep (se 1 (by rfl) ⟨2258072, by rfl⟩ : syracuseStep 3010763 = 4516145) B4516145
theorem B3387595 : Blo 1784093 3387595 := bstep (se 1 (by rfl) ⟨2540696, by rfl⟩ : syracuseStep 3387595 = 5081393) B5081393
theorem B4018391 : Blo 1784093 4018391 := bstep (se 1 (by rfl) ⟨3013793, by rfl⟩ : syracuseStep 4018391 = 6027587) B6027587
theorem B6779153 : Blo 1784093 6779153 := bstep (se 2 (by rfl) ⟨2542182, by rfl⟩ : syracuseStep 6779153 = 5084365) B5084365
theorem B3010891 : Blo 1784093 3010891 := bstep (se 1 (by rfl) ⟨2258168, by rfl⟩ : syracuseStep 3010891 = 4516337) B4516337
theorem B10309963 : Blo 1784093 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B4018571 : Blo 1784093 4018571 := bstep (se 1 (by rfl) ⟨3013928, by rfl⟩ : syracuseStep 4018571 = 6027857) B6027857
theorem B15249815 : Blo 1784093 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B5796289 : Blo 1784093 5796289 := bstep (se 2 (by rfl) ⟨2173608, by rfl⟩ : syracuseStep 5796289 = 4347217) B4347217
theorem B4018625 : Blo 1784093 4018625 := bstep (se 2 (by rfl) ⟨1506984, by rfl⟩ : syracuseStep 4018625 = 3013969) B3013969
theorem B3011033 : Blo 1784093 3011033 := bstep (se 2 (by rfl) ⟨1129137, by rfl⟩ : syracuseStep 3011033 = 2258275) B2258275
theorem B12866053 : Blo 1784093 12866053 := bstep (se 4 (by rfl) ⟨1206192, by rfl⟩ : syracuseStep 12866053 = 2412385) B2412385
theorem B6025751 : Blo 1784093 6025751 := bstep (se 1 (by rfl) ⟨4519313, by rfl⟩ : syracuseStep 6025751 = 9038627) B9038627
theorem B8573485 : Blo 1784093 8573485 := bstep (se 3 (by rfl) ⟨1607528, by rfl⟩ : syracuseStep 8573485 = 3215057) B3215057
theorem B3011161 : Blo 1784093 3011161 := bstep (se 2 (by rfl) ⟨1129185, by rfl⟩ : syracuseStep 3011161 = 2258371) B2258371
theorem B3388043 : Blo 1784093 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B4289203 : Blo 1784093 4289203 := bstep (se 1 (by rfl) ⟨3216902, by rfl⟩ : syracuseStep 4289203 = 6433805) B6433805
theorem B8139467 : Blo 1784093 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B6779609 : Blo 1784093 6779609 := bstep (se 2 (by rfl) ⟨2542353, by rfl⟩ : syracuseStep 6779609 = 5084707) B5084707
theorem B15250193 : Blo 1784093 15250193 := bstep (se 2 (by rfl) ⟨5718822, by rfl⟩ : syracuseStep 15250193 = 11437645) B11437645
theorem B16290605 : Blo 1784093 16290605 := bstep (se 3 (by rfl) ⟨3054488, by rfl⟩ : syracuseStep 16290605 = 6108977) B6108977
theorem B5083955 : Blo 1784093 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B3388225 : Blo 1784093 3388225 := bstep (se 2 (by rfl) ⟨1270584, by rfl⟩ : syracuseStep 3388225 = 2541169) B2541169
theorem B3814231 : Blo 1784093 3814231 := bstep (se 1 (by rfl) ⟨2860673, by rfl⟩ : syracuseStep 3814231 = 5721347) B5721347
theorem B9040733 : Blo 1784093 9040733 := bstep (se 3 (by rfl) ⟨1695137, by rfl⟩ : syracuseStep 9040733 = 3390275) B3390275
theorem B3814283 : Blo 1784093 3814283 := bstep (se 1 (by rfl) ⟨2860712, by rfl⟩ : syracuseStep 3814283 = 5721425) B5721425
theorem B12866455 : Blo 1784093 12866455 := bstep (se 1 (by rfl) ⟨9649841, by rfl⟩ : syracuseStep 12866455 = 19299683) B19299683
theorem B6779821 : Blo 1784093 6779821 := bstep (se 3 (by rfl) ⟨1271216, by rfl⟩ : syracuseStep 6779821 = 2542433) B2542433
theorem B13562801 : Blo 1784093 13562801 := bstep (se 2 (by rfl) ⟨5086050, by rfl⟩ : syracuseStep 13562801 = 10172101) B10172101
theorem B57930713 : Blo 1784093 57930713 := bstep (se 2 (by rfl) ⟨21724017, by rfl⟩ : syracuseStep 57930713 = 43448035) B43448035
theorem B5084183 : Blo 1784093 5084183 := bstep (se 1 (by rfl) ⟨3813137, by rfl⟩ : syracuseStep 5084183 = 7626275) B7626275
theorem B12219437 : Blo 1784093 12219437 := bstep (se 3 (by rfl) ⟨2291144, by rfl⟩ : syracuseStep 12219437 = 4582289) B4582289
theorem B6026291 : Blo 1784093 6026291 := bstep (se 1 (by rfl) ⟨4519718, by rfl⟩ : syracuseStep 6026291 = 9039437) B9039437
theorem B9655361 : Blo 1784093 9655361 := bstep (se 2 (by rfl) ⟨3620760, by rfl⟩ : syracuseStep 9655361 = 7241521) B7241521
theorem B18314333 : Blo 1784093 18314333 := bstep (se 3 (by rfl) ⟨3433937, by rfl⟩ : syracuseStep 18314333 = 6867875) B6867875
theorem B3011735 : Blo 1784093 3011735 := bstep (se 1 (by rfl) ⟨2258801, by rfl⟩ : syracuseStep 3011735 = 4517603) B4517603
theorem B3388567 : Blo 1784093 3388567 := bstep (se 1 (by rfl) ⟨2541425, by rfl⟩ : syracuseStep 3388567 = 5082851) B5082851
theorem B4519091 : Blo 1784093 4519091 := bstep (se 1 (by rfl) ⟨3389318, by rfl⟩ : syracuseStep 4519091 = 6778637) B6778637
theorem B6780125 : Blo 1784093 6780125 := bstep (se 3 (by rfl) ⟨1271273, by rfl⟩ : syracuseStep 6780125 = 2542547) B2542547
theorem B3011863 : Blo 1784093 3011863 := bstep (se 1 (by rfl) ⟨2258897, by rfl⟩ : syracuseStep 3011863 = 4517795) B4517795
theorem B14120227 : Blo 1784093 14120227 := bstep (se 1 (by rfl) ⟨10590170, by rfl⟩ : syracuseStep 14120227 = 21180341) B21180341
theorem B6026561 : Blo 1784093 6026561 := bstep (se 2 (by rfl) ⟨2259960, by rfl⟩ : syracuseStep 6026561 = 4519921) B4519921
theorem B5084491 : Blo 1784093 5084491 := bstep (se 1 (by rfl) ⟨3813368, by rfl⟩ : syracuseStep 5084491 = 7626737) B7626737
theorem B3388787 : Blo 1784093 3388787 := bstep (se 1 (by rfl) ⟨2541590, by rfl⟩ : syracuseStep 3388787 = 5083181) B5083181
theorem B1906039 : Blo 1784093 1906039 := bstep (se 1 (by rfl) ⟨1429529, by rfl⟩ : syracuseStep 1906039 = 2859059) B2859059
theorem B2676185 : Blo 1784093 2676185 := bstep (se 2 (by rfl) ⟨1003569, by rfl⟩ : syracuseStep 2676185 = 2007139) B2007139
theorem B4519385 : Blo 1784093 4519385 := bstep (se 2 (by rfl) ⟨1694769, by rfl⟩ : syracuseStep 4519385 = 3389539) B3389539
theorem B9033281 : Blo 1784093 9033281 := bstep (se 2 (by rfl) ⟨3387480, by rfl⟩ : syracuseStep 9033281 = 6774961) B6774961
theorem B7239233 : Blo 1784093 7239233 := bstep (se 2 (by rfl) ⟨2714712, by rfl⟩ : syracuseStep 7239233 = 5429425) B5429425
theorem B2676299 : Blo 1784093 2676299 := bstep (se 1 (by rfl) ⟨2007224, by rfl⟩ : syracuseStep 2676299 = 4014449) B4014449
theorem B5502539 : Blo 1784093 5502539 := bstep (se 1 (by rfl) ⟨4126904, by rfl⟩ : syracuseStep 5502539 = 8253809) B8253809
theorem B2676311 : Blo 1784093 2676311 := bstep (se 1 (by rfl) ⟨2007233, by rfl⟩ : syracuseStep 2676311 = 4014467) B4014467
theorem B3389015 : Blo 1784093 3389015 := bstep (se 1 (by rfl) ⟨2541761, by rfl⟩ : syracuseStep 3389015 = 5083523) B5083523
theorem B5084765 : Blo 1784093 5084765 := bstep (se 3 (by rfl) ⟨953393, by rfl⟩ : syracuseStep 5084765 = 1906787) B1906787
theorem B2676377 : Blo 1784093 2676377 := bstep (se 2 (by rfl) ⟨1003641, by rfl⟩ : syracuseStep 2676377 = 2007283) B2007283
theorem B4290241 : Blo 1784093 4290241 := bstep (se 2 (by rfl) ⟨1608840, by rfl⟩ : syracuseStep 4290241 = 3217681) B3217681
theorem B1906411 : Blo 1784093 1906411 := bstep (se 1 (by rfl) ⟨1429808, by rfl⟩ : syracuseStep 1906411 = 2859617) B2859617
theorem B7730947 : Blo 1784093 7730947 := bstep (se 1 (by rfl) ⟨5798210, by rfl⟩ : syracuseStep 7730947 = 11596421) B11596421
theorem B2676491 : Blo 1784093 2676491 := bstep (se 1 (by rfl) ⟨2007368, by rfl⟩ : syracuseStep 2676491 = 4014737) B4014737
theorem B2676503 : Blo 1784093 2676503 := bstep (se 1 (by rfl) ⟨2007377, by rfl⟩ : syracuseStep 2676503 = 4014755) B4014755
theorem B11433773 : Blo 1784093 11433773 := bstep (se 3 (by rfl) ⟨2143832, by rfl⟩ : syracuseStep 11433773 = 4287665) B4287665
theorem B2676569 : Blo 1784093 2676569 := bstep (se 2 (by rfl) ⟨1003713, by rfl⟩ : syracuseStep 2676569 = 2007427) B2007427
theorem B3389273 : Blo 1784093 3389273 := bstep (se 2 (by rfl) ⟨1270977, by rfl⟩ : syracuseStep 3389273 = 2541955) B2541955
theorem B6027101 : Blo 1784093 6027101 := bstep (se 3 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 6027101 = 2260163) B2260163
theorem B18315109 : Blo 1784093 18315109 := bstep (se 4 (by rfl) ⟨1717041, by rfl⟩ : syracuseStep 18315109 = 3434083) B3434083
theorem B25737061 : Blo 1784093 25737061 := bstep (se 4 (by rfl) ⟨2412849, by rfl⟩ : syracuseStep 25737061 = 4825699) B4825699
theorem B3012491 : Blo 1784093 3012491 := bstep (se 1 (by rfl) ⟨2259368, by rfl⟩ : syracuseStep 3012491 = 4518737) B4518737
theorem B2676683 : Blo 1784093 2676683 := bstep (se 1 (by rfl) ⟨2007512, by rfl⟩ : syracuseStep 2676683 = 4015025) B4015025
theorem B2676695 : Blo 1784093 2676695 := bstep (se 1 (by rfl) ⟨2007521, by rfl⟩ : syracuseStep 2676695 = 4015043) B4015043
theorem B3012619 : Blo 1784093 3012619 := bstep (se 1 (by rfl) ⟨2259464, by rfl⟩ : syracuseStep 3012619 = 4518929) B4518929
theorem B2676761 : Blo 1784093 2676761 := bstep (se 2 (by rfl) ⟨1003785, by rfl⟩ : syracuseStep 2676761 = 2007571) B2007571
theorem B2259019 : Blo 1784093 2259019 := bstep (se 1 (by rfl) ⟨1694264, by rfl⟩ : syracuseStep 2259019 = 3388529) B3388529
theorem B2676875 : Blo 1784093 2676875 := bstep (se 1 (by rfl) ⟨2007656, by rfl⟩ : syracuseStep 2676875 = 4015313) B4015313
theorem B2750603 : Blo 1784093 2750603 := bstep (se 1 (by rfl) ⟨2062952, by rfl⟩ : syracuseStep 2750603 = 4125905) B4125905
theorem B2676887 : Blo 1784093 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B3012761 : Blo 1784093 3012761 := bstep (se 2 (by rfl) ⟨1129785, by rfl⟩ : syracuseStep 3012761 = 2259571) B2259571
theorem B1906859 : Blo 1784093 1906859 := bstep (se 1 (by rfl) ⟨1430144, by rfl⟩ : syracuseStep 1906859 = 2860289) B2860289
theorem B2676953 : Blo 1784093 2676953 := bstep (se 2 (by rfl) ⟨1003857, by rfl⟩ : syracuseStep 2676953 = 2007715) B2007715
theorem B3389683 : Blo 1784093 3389683 := bstep (se 1 (by rfl) ⟨2542262, by rfl⟩ : syracuseStep 3389683 = 5084525) B5084525
theorem B3528983 : Blo 1784093 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B3619097 : Blo 1784093 3619097 := bstep (se 2 (by rfl) ⟨1357161, by rfl⟩ : syracuseStep 3619097 = 2714323) B2714323
theorem B3012889 : Blo 1784093 3012889 := bstep (se 2 (by rfl) ⟨1129833, by rfl⟩ : syracuseStep 3012889 = 2259667) B2259667
theorem B1784107 : Blo 1784093 1784107 := bstep (se 1 (by rfl) ⟨1338080, by rfl⟩ : syracuseStep 1784107 = 2676161) B2676161
theorem B1784119 : Blo 1784093 1784119 := bstep (se 1 (by rfl) ⟨1338089, by rfl⟩ : syracuseStep 1784119 = 2676179) B2676179
theorem B19290433 : Blo 1784093 19290433 := bstep (se 2 (by rfl) ⟨7233912, by rfl⟩ : syracuseStep 19290433 = 14467825) B14467825
theorem B1784139 : Blo 1784093 1784139 := bstep (se 1 (by rfl) ⟨1338104, by rfl⟩ : syracuseStep 1784139 = 2676209) B2676209
theorem B2677067 : Blo 1784093 2677067 := bstep (se 1 (by rfl) ⟨2007800, by rfl⟩ : syracuseStep 2677067 = 4015601) B4015601
theorem B1784151 : Blo 1784093 1784151 := bstep (se 1 (by rfl) ⟨1338113, by rfl⟩ : syracuseStep 1784151 = 2676227) B2676227
theorem B2677079 : Blo 1784093 2677079 := bstep (se 1 (by rfl) ⟨2007809, by rfl⟩ : syracuseStep 2677079 = 4015619) B4015619
theorem B1784171 : Blo 1784093 1784171 := bstep (se 1 (by rfl) ⟨1338128, by rfl⟩ : syracuseStep 1784171 = 2676257) B2676257
theorem B1784183 : Blo 1784093 1784183 := bstep (se 1 (by rfl) ⟨1338137, by rfl⟩ : syracuseStep 1784183 = 2676275) B2676275
theorem B1784203 : Blo 1784093 1784203 := bstep (se 1 (by rfl) ⟨1338152, by rfl⟩ : syracuseStep 1784203 = 2676305) B2676305
theorem B1784215 : Blo 1784093 1784215 := bstep (se 1 (by rfl) ⟨1338161, by rfl⟩ : syracuseStep 1784215 = 2676323) B2676323
theorem B2677145 : Blo 1784093 2677145 := bstep (se 2 (by rfl) ⟨1003929, by rfl⟩ : syracuseStep 2677145 = 2007859) B2007859
theorem B1784235 : Blo 1784093 1784235 := bstep (se 1 (by rfl) ⟨1338176, by rfl⟩ : syracuseStep 1784235 = 2676353) B2676353
theorem B33028529 : Blo 1784093 33028529 := bstep (se 2 (by rfl) ⟨12385698, by rfl⟩ : syracuseStep 33028529 = 24771397) B24771397
theorem B1784247 : Blo 1784093 1784247 := bstep (se 1 (by rfl) ⟨1338185, by rfl⟩ : syracuseStep 1784247 = 2676371) B2676371
theorem B1784267 : Blo 1784093 1784267 := bstep (se 1 (by rfl) ⟨1338200, by rfl⟩ : syracuseStep 1784267 = 2676401) B2676401
theorem B1784279 : Blo 1784093 1784279 := bstep (se 1 (by rfl) ⟨1338209, by rfl⟩ : syracuseStep 1784279 = 2676419) B2676419
theorem B1784299 : Blo 1784093 1784299 := bstep (se 1 (by rfl) ⟨1338224, by rfl⟩ : syracuseStep 1784299 = 2676449) B2676449
theorem B1784311 : Blo 1784093 1784311 := bstep (se 1 (by rfl) ⟨1338233, by rfl⟩ : syracuseStep 1784311 = 2676467) B2676467
theorem B1784331 : Blo 1784093 1784331 := bstep (se 1 (by rfl) ⟨1338248, by rfl⟩ : syracuseStep 1784331 = 2676497) B2676497
theorem B2677259 : Blo 1784093 2677259 := bstep (se 1 (by rfl) ⟨2007944, by rfl⟩ : syracuseStep 2677259 = 4015889) B4015889
theorem B1784343 : Blo 1784093 1784343 := bstep (se 1 (by rfl) ⟨1338257, by rfl⟩ : syracuseStep 1784343 = 2676515) B2676515
theorem B2677271 : Blo 1784093 2677271 := bstep (se 1 (by rfl) ⟨2007953, by rfl⟩ : syracuseStep 2677271 = 4015907) B4015907
theorem B1784363 : Blo 1784093 1784363 := bstep (se 1 (by rfl) ⟨1338272, by rfl⟩ : syracuseStep 1784363 = 2676545) B2676545
theorem B1784375 : Blo 1784093 1784375 := bstep (se 1 (by rfl) ⟨1338281, by rfl⟩ : syracuseStep 1784375 = 2676563) B2676563
theorem B1784395 : Blo 1784093 1784395 := bstep (se 1 (by rfl) ⟨1338296, by rfl⟩ : syracuseStep 1784395 = 2676593) B2676593
theorem B10164811 : Blo 1784093 10164811 := bstep (se 1 (by rfl) ⟨7623608, by rfl⟩ : syracuseStep 10164811 = 15247217) B15247217
theorem B1784407 : Blo 1784093 1784407 := bstep (se 1 (by rfl) ⟨1338305, by rfl⟩ : syracuseStep 1784407 = 2676611) B2676611
theorem B2677337 : Blo 1784093 2677337 := bstep (se 2 (by rfl) ⟨1004001, by rfl⟩ : syracuseStep 2677337 = 2008003) B2008003
theorem B1784427 : Blo 1784093 1784427 := bstep (se 1 (by rfl) ⟨1338320, by rfl⟩ : syracuseStep 1784427 = 2676641) B2676641
theorem B1784439 : Blo 1784093 1784439 := bstep (se 1 (by rfl) ⟨1338329, by rfl⟩ : syracuseStep 1784439 = 2676659) B2676659
theorem B1784459 : Blo 1784093 1784459 := bstep (se 1 (by rfl) ⟨1338344, by rfl⟩ : syracuseStep 1784459 = 2676689) B2676689
theorem B5716631 : Blo 1784093 5716631 := bstep (se 1 (by rfl) ⟨4287473, by rfl⟩ : syracuseStep 5716631 = 8574947) B8574947
theorem B1784471 : Blo 1784093 1784471 := bstep (se 1 (by rfl) ⟨1338353, by rfl⟩ : syracuseStep 1784471 = 2676707) B2676707
theorem B4127383 : Blo 1784093 4127383 := bstep (se 1 (by rfl) ⟨3095537, by rfl⟩ : syracuseStep 4127383 = 6191075) B6191075
theorem B1784491 : Blo 1784093 1784491 := bstep (se 1 (by rfl) ⟨1338368, by rfl⟩ : syracuseStep 1784491 = 2676737) B2676737
theorem B10861235 : Blo 1784093 10861235 := bstep (se 1 (by rfl) ⟨8145926, by rfl⟩ : syracuseStep 10861235 = 16291853) B16291853
theorem B1784503 : Blo 1784093 1784503 := bstep (se 1 (by rfl) ⟨1338377, by rfl⟩ : syracuseStep 1784503 = 2676755) B2676755
theorem B1784523 : Blo 1784093 1784523 := bstep (se 1 (by rfl) ⟨1338392, by rfl⟩ : syracuseStep 1784523 = 2676785) B2676785
theorem B2677451 : Blo 1784093 2677451 := bstep (se 1 (by rfl) ⟨2008088, by rfl⟩ : syracuseStep 2677451 = 4016177) B4016177
theorem B12868301 : Blo 1784093 12868301 := bstep (se 3 (by rfl) ⟨2412806, by rfl⟩ : syracuseStep 12868301 = 4825613) B4825613
theorem B1784535 : Blo 1784093 1784535 := bstep (se 1 (by rfl) ⟨1338401, by rfl⟩ : syracuseStep 1784535 = 2676803) B2676803
theorem B2677463 : Blo 1784093 2677463 := bstep (se 1 (by rfl) ⟨2008097, by rfl⟩ : syracuseStep 2677463 = 4016195) B4016195
theorem B3390169 : Blo 1784093 3390169 := bstep (se 2 (by rfl) ⟨1271313, by rfl⟩ : syracuseStep 3390169 = 2542627) B2542627
theorem B1784555 : Blo 1784093 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B1784567 : Blo 1784093 1784567 := bstep (se 1 (by rfl) ⟨1338425, by rfl⟩ : syracuseStep 1784567 = 2676851) B2676851
theorem B1784587 : Blo 1784093 1784587 := bstep (se 1 (by rfl) ⟨1338440, by rfl⟩ : syracuseStep 1784587 = 2676881) B2676881
theorem B1784599 : Blo 1784093 1784599 := bstep (se 1 (by rfl) ⟨1338449, by rfl⟩ : syracuseStep 1784599 = 2676899) B2676899
theorem B3054359 : Blo 1784093 3054359 := bstep (se 1 (by rfl) ⟨2290769, by rfl⟩ : syracuseStep 3054359 = 4581539) B4581539
theorem B2677529 : Blo 1784093 2677529 := bstep (se 2 (by rfl) ⟨1004073, by rfl⟩ : syracuseStep 2677529 = 2008147) B2008147
theorem B1784619 : Blo 1784093 1784619 := bstep (se 1 (by rfl) ⟨1338464, by rfl⟩ : syracuseStep 1784619 = 2676929) B2676929
theorem B1784631 : Blo 1784093 1784631 := bstep (se 1 (by rfl) ⟨1338473, by rfl⟩ : syracuseStep 1784631 = 2676947) B2676947
theorem B5716811 : Blo 1784093 5716811 := bstep (se 1 (by rfl) ⟨4287608, by rfl⟩ : syracuseStep 5716811 = 8575217) B8575217
theorem B1784651 : Blo 1784093 1784651 := bstep (se 1 (by rfl) ⟨1338488, by rfl⟩ : syracuseStep 1784651 = 2676977) B2676977
theorem B1784663 : Blo 1784093 1784663 := bstep (se 1 (by rfl) ⟨1338497, by rfl⟩ : syracuseStep 1784663 = 2676995) B2676995
theorem B3013463 : Blo 1784093 3013463 := bstep (se 1 (by rfl) ⟨2260097, by rfl⟩ : syracuseStep 3013463 = 4520195) B4520195
theorem B10165085 : Blo 1784093 10165085 := bstep (se 3 (by rfl) ⟨1905953, by rfl⟩ : syracuseStep 10165085 = 3811907) B3811907
theorem B1784683 : Blo 1784093 1784683 := bstep (se 1 (by rfl) ⟨1338512, by rfl⟩ : syracuseStep 1784683 = 2677025) B2677025
theorem B1784695 : Blo 1784093 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B1784715 : Blo 1784093 1784715 := bstep (se 1 (by rfl) ⟨1338536, by rfl⟩ : syracuseStep 1784715 = 2677073) B2677073
theorem B2677643 : Blo 1784093 2677643 := bstep (se 1 (by rfl) ⟨2008232, by rfl⟩ : syracuseStep 2677643 = 4016465) B4016465
theorem B1784727 : Blo 1784093 1784727 := bstep (se 1 (by rfl) ⟨1338545, by rfl⟩ : syracuseStep 1784727 = 2677091) B2677091
theorem B2677655 : Blo 1784093 2677655 := bstep (se 1 (by rfl) ⟨2008241, by rfl⟩ : syracuseStep 2677655 = 4016483) B4016483
theorem B1784747 : Blo 1784093 1784747 := bstep (se 1 (by rfl) ⟨1338560, by rfl⟩ : syracuseStep 1784747 = 2677121) B2677121
theorem B1784759 : Blo 1784093 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B2857931 : Blo 1784093 2857931 := bstep (se 1 (by rfl) ⟨2143448, by rfl⟩ : syracuseStep 2857931 = 4286897) B4286897
theorem B5716939 : Blo 1784093 5716939 := bstep (se 1 (by rfl) ⟨4287704, by rfl⟩ : syracuseStep 5716939 = 8575409) B8575409
theorem B1784779 : Blo 1784093 1784779 := bstep (se 1 (by rfl) ⟨1338584, by rfl⟩ : syracuseStep 1784779 = 2677169) B2677169
theorem B1784791 : Blo 1784093 1784791 := bstep (se 1 (by rfl) ⟨1338593, by rfl⟩ : syracuseStep 1784791 = 2677187) B2677187
theorem B2677721 : Blo 1784093 2677721 := bstep (se 2 (by rfl) ⟨1004145, by rfl⟩ : syracuseStep 2677721 = 2008291) B2008291
theorem B3013591 : Blo 1784093 3013591 := bstep (se 1 (by rfl) ⟨2260193, by rfl⟩ : syracuseStep 3013591 = 4520387) B4520387
theorem B1784811 : Blo 1784093 1784811 := bstep (se 1 (by rfl) ⟨1338608, by rfl⟩ : syracuseStep 1784811 = 2677217) B2677217
theorem B1784823 : Blo 1784093 1784823 := bstep (se 1 (by rfl) ⟨1338617, by rfl⟩ : syracuseStep 1784823 = 2677235) B2677235
theorem B1784843 : Blo 1784093 1784843 := bstep (se 1 (by rfl) ⟨1338632, by rfl⟩ : syracuseStep 1784843 = 2677265) B2677265
theorem B1784855 : Blo 1784093 1784855 := bstep (se 1 (by rfl) ⟨1338641, by rfl⟩ : syracuseStep 1784855 = 2677283) B2677283
theorem B2259991 : Blo 1784093 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B1784875 : Blo 1784093 1784875 := bstep (se 1 (by rfl) ⟨1338656, by rfl⟩ : syracuseStep 1784875 = 2677313) B2677313
theorem B1784887 : Blo 1784093 1784887 := bstep (se 1 (by rfl) ⟨1338665, by rfl⟩ : syracuseStep 1784887 = 2677331) B2677331
theorem B1784907 : Blo 1784093 1784907 := bstep (se 1 (by rfl) ⟨1338680, by rfl⟩ : syracuseStep 1784907 = 2677361) B2677361
theorem B2677835 : Blo 1784093 2677835 := bstep (se 1 (by rfl) ⟨2008376, by rfl⟩ : syracuseStep 2677835 = 4016753) B4016753
theorem B4521035 : Blo 1784093 4521035 := bstep (se 1 (by rfl) ⟨3390776, by rfl⟩ : syracuseStep 4521035 = 6781553) B6781553
theorem B1784919 : Blo 1784093 1784919 := bstep (se 1 (by rfl) ⟨1338689, by rfl⟩ : syracuseStep 1784919 = 2677379) B2677379
theorem B2677847 : Blo 1784093 2677847 := bstep (se 1 (by rfl) ⟨2008385, by rfl⟩ : syracuseStep 2677847 = 4016771) B4016771
theorem B5717081 : Blo 1784093 5717081 := bstep (se 2 (by rfl) ⟨2143905, by rfl⟩ : syracuseStep 5717081 = 4287811) B4287811
theorem B1784939 : Blo 1784093 1784939 := bstep (se 1 (by rfl) ⟨1338704, by rfl⟩ : syracuseStep 1784939 = 2677409) B2677409
theorem B1784951 : Blo 1784093 1784951 := bstep (se 1 (by rfl) ⟨1338713, by rfl⟩ : syracuseStep 1784951 = 2677427) B2677427
theorem B1784971 : Blo 1784093 1784971 := bstep (se 1 (by rfl) ⟨1338728, by rfl⟩ : syracuseStep 1784971 = 2677457) B2677457
theorem B1784983 : Blo 1784093 1784983 := bstep (se 1 (by rfl) ⟨1338737, by rfl⟩ : syracuseStep 1784983 = 2677475) B2677475
theorem B2677913 : Blo 1784093 2677913 := bstep (se 2 (by rfl) ⟨1004217, by rfl⟩ : syracuseStep 2677913 = 2008435) B2008435
theorem B1785003 : Blo 1784093 1785003 := bstep (se 1 (by rfl) ⟨1338752, by rfl⟩ : syracuseStep 1785003 = 2677505) B2677505
theorem B1785015 : Blo 1784093 1785015 := bstep (se 1 (by rfl) ⟨1338761, by rfl⟩ : syracuseStep 1785015 = 2677523) B2677523
theorem B5717195 : Blo 1784093 5717195 := bstep (se 1 (by rfl) ⟨4287896, by rfl⟩ : syracuseStep 5717195 = 8575793) B8575793
theorem B1785035 : Blo 1784093 1785035 := bstep (se 1 (by rfl) ⟨1338776, by rfl⟩ : syracuseStep 1785035 = 2677553) B2677553
theorem B1785047 : Blo 1784093 1785047 := bstep (se 1 (by rfl) ⟨1338785, by rfl⟩ : syracuseStep 1785047 = 2677571) B2677571
theorem B241188067 : Blo 1784093 241188067 := bstep (se 1 (by rfl) ⟨180891050, by rfl⟩ : syracuseStep 241188067 = 361782101) B361782101
theorem B1785067 : Blo 1784093 1785067 := bstep (se 1 (by rfl) ⟨1338800, by rfl⟩ : syracuseStep 1785067 = 2677601) B2677601
theorem B1785079 : Blo 1784093 1785079 := bstep (se 1 (by rfl) ⟨1338809, by rfl⟩ : syracuseStep 1785079 = 2677619) B2677619
theorem B4070657 : Blo 1784093 4070657 := bstep (se 2 (by rfl) ⟨1526496, by rfl⟩ : syracuseStep 4070657 = 3052993) B3052993
theorem B1785099 : Blo 1784093 1785099 := bstep (se 1 (by rfl) ⟨1338824, by rfl⟩ : syracuseStep 1785099 = 2677649) B2677649
theorem B2678027 : Blo 1784093 2678027 := bstep (se 1 (by rfl) ⟨2008520, by rfl⟩ : syracuseStep 2678027 = 4017041) B4017041
theorem B3390731 : Blo 1784093 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B7626001 : Blo 1784093 7626001 := bstep (se 2 (by rfl) ⟨2859750, by rfl⟩ : syracuseStep 7626001 = 5719501) B5719501
theorem B1785111 : Blo 1784093 1785111 := bstep (se 1 (by rfl) ⟨1338833, by rfl⟩ : syracuseStep 1785111 = 2677667) B2677667
theorem B2678039 : Blo 1784093 2678039 := bstep (se 1 (by rfl) ⟨2008529, by rfl⟩ : syracuseStep 2678039 = 4017059) B4017059
theorem B1785131 : Blo 1784093 1785131 := bstep (se 1 (by rfl) ⟨1338848, by rfl⟩ : syracuseStep 1785131 = 2677697) B2677697
theorem B1785143 : Blo 1784093 1785143 := bstep (se 1 (by rfl) ⟨1338857, by rfl⟩ : syracuseStep 1785143 = 2677715) B2677715
theorem B1785163 : Blo 1784093 1785163 := bstep (se 1 (by rfl) ⟨1338872, by rfl⟩ : syracuseStep 1785163 = 2677745) B2677745
theorem B1785175 : Blo 1784093 1785175 := bstep (se 1 (by rfl) ⟨1338881, by rfl⟩ : syracuseStep 1785175 = 2677763) B2677763
theorem B2678105 : Blo 1784093 2678105 := bstep (se 2 (by rfl) ⟨1004289, by rfl⟩ : syracuseStep 2678105 = 2008579) B2008579
theorem B1785195 : Blo 1784093 1785195 := bstep (se 1 (by rfl) ⟨1338896, by rfl⟩ : syracuseStep 1785195 = 2677793) B2677793
theorem B1785207 : Blo 1784093 1785207 := bstep (se 1 (by rfl) ⟨1338905, by rfl⟩ : syracuseStep 1785207 = 2677811) B2677811
theorem B1785227 : Blo 1784093 1785227 := bstep (se 1 (by rfl) ⟨1338920, by rfl⟩ : syracuseStep 1785227 = 2677841) B2677841
theorem B1785239 : Blo 1784093 1785239 := bstep (se 1 (by rfl) ⟨1338929, by rfl⟩ : syracuseStep 1785239 = 2677859) B2677859
theorem B1785259 : Blo 1784093 1785259 := bstep (se 1 (by rfl) ⟨1338944, by rfl⟩ : syracuseStep 1785259 = 2677889) B2677889
theorem B1785271 : Blo 1784093 1785271 := bstep (se 1 (by rfl) ⟨1338953, by rfl⟩ : syracuseStep 1785271 = 2677907) B2677907
theorem B1785291 : Blo 1784093 1785291 := bstep (se 1 (by rfl) ⟨1338968, by rfl⟩ : syracuseStep 1785291 = 2677937) B2677937
theorem B2678219 : Blo 1784093 2678219 := bstep (se 1 (by rfl) ⟨2008664, by rfl⟩ : syracuseStep 2678219 = 4017329) B4017329
theorem B1785303 : Blo 1784093 1785303 := bstep (se 1 (by rfl) ⟨1338977, by rfl⟩ : syracuseStep 1785303 = 2677955) B2677955
theorem B2678231 : Blo 1784093 2678231 := bstep (se 1 (by rfl) ⟨2008673, by rfl⟩ : syracuseStep 2678231 = 4017347) B4017347
theorem B9035225 : Blo 1784093 9035225 := bstep (se 2 (by rfl) ⟨3388209, by rfl⟩ : syracuseStep 9035225 = 6776419) B6776419
theorem B1785323 : Blo 1784093 1785323 := bstep (se 1 (by rfl) ⟨1338992, by rfl⟩ : syracuseStep 1785323 = 2677985) B2677985
theorem B1785335 : Blo 1784093 1785335 := bstep (se 1 (by rfl) ⟨1339001, by rfl⟩ : syracuseStep 1785335 = 2678003) B2678003
theorem B1785355 : Blo 1784093 1785355 := bstep (se 1 (by rfl) ⟨1339016, by rfl⟩ : syracuseStep 1785355 = 2678033) B2678033
theorem B24436241 : Blo 1784093 24436241 := bstep (se 2 (by rfl) ⟨9163590, by rfl⟩ : syracuseStep 24436241 = 18327181) B18327181
theorem B1785367 : Blo 1784093 1785367 := bstep (se 1 (by rfl) ⟨1339025, by rfl⟩ : syracuseStep 1785367 = 2678051) B2678051
theorem B2678297 : Blo 1784093 2678297 := bstep (se 2 (by rfl) ⟨1004361, by rfl⟩ : syracuseStep 2678297 = 2008723) B2008723
theorem B1785387 : Blo 1784093 1785387 := bstep (se 1 (by rfl) ⟨1339040, by rfl⟩ : syracuseStep 1785387 = 2678081) B2678081
theorem B6430259 : Blo 1784093 6430259 := bstep (se 1 (by rfl) ⟨4822694, by rfl⟩ : syracuseStep 6430259 = 9645389) B9645389
theorem B1785399 : Blo 1784093 1785399 := bstep (se 1 (by rfl) ⟨1339049, by rfl⟩ : syracuseStep 1785399 = 2678099) B2678099
theorem B1785419 : Blo 1784093 1785419 := bstep (se 1 (by rfl) ⟨1339064, by rfl⟩ : syracuseStep 1785419 = 2678129) B2678129
theorem B1785431 : Blo 1784093 1785431 := bstep (se 1 (by rfl) ⟨1339073, by rfl⟩ : syracuseStep 1785431 = 2678147) B2678147
theorem B7241309 : Blo 1784093 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B1785451 : Blo 1784093 1785451 := bstep (se 1 (by rfl) ⟨1339088, by rfl⟩ : syracuseStep 1785451 = 2678177) B2678177
theorem B1785463 : Blo 1784093 1785463 := bstep (se 1 (by rfl) ⟨1339097, by rfl⟩ : syracuseStep 1785463 = 2678195) B2678195
theorem B1785483 : Blo 1784093 1785483 := bstep (se 1 (by rfl) ⟨1339112, by rfl⟩ : syracuseStep 1785483 = 2678225) B2678225
theorem B2678411 : Blo 1784093 2678411 := bstep (se 1 (by rfl) ⟨2008808, by rfl⟩ : syracuseStep 2678411 = 4017617) B4017617
theorem B1785495 : Blo 1784093 1785495 := bstep (se 1 (by rfl) ⟨1339121, by rfl⟩ : syracuseStep 1785495 = 2678243) B2678243
theorem B2678423 : Blo 1784093 2678423 := bstep (se 1 (by rfl) ⟨2008817, by rfl⟩ : syracuseStep 2678423 = 4017635) B4017635
theorem B16293527 : Blo 1784093 16293527 := bstep (se 1 (by rfl) ⟨12220145, by rfl⟩ : syracuseStep 16293527 = 24440291) B24440291
theorem B1785515 : Blo 1784093 1785515 := bstep (se 1 (by rfl) ⟨1339136, by rfl⟩ : syracuseStep 1785515 = 2678273) B2678273
theorem B1785527 : Blo 1784093 1785527 := bstep (se 1 (by rfl) ⟨1339145, by rfl⟩ : syracuseStep 1785527 = 2678291) B2678291
theorem B6774475 : Blo 1784093 6774475 := bstep (se 1 (by rfl) ⟨5080856, by rfl⟩ : syracuseStep 6774475 = 10161713) B10161713
theorem B1785547 : Blo 1784093 1785547 := bstep (se 1 (by rfl) ⟨1339160, by rfl⟩ : syracuseStep 1785547 = 2678321) B2678321
theorem B1785559 : Blo 1784093 1785559 := bstep (se 1 (by rfl) ⟨1339169, by rfl⟩ : syracuseStep 1785559 = 2678339) B2678339
theorem B2678489 : Blo 1784093 2678489 := bstep (se 2 (by rfl) ⟨1004433, by rfl⟩ : syracuseStep 2678489 = 2008867) B2008867
theorem B1785579 : Blo 1784093 1785579 := bstep (se 1 (by rfl) ⟨1339184, by rfl⟩ : syracuseStep 1785579 = 2678369) B2678369
theorem B1785591 : Blo 1784093 1785591 := bstep (se 1 (by rfl) ⟨1339193, by rfl⟩ : syracuseStep 1785591 = 2678387) B2678387
theorem B1785611 : Blo 1784093 1785611 := bstep (se 1 (by rfl) ⟨1339208, by rfl⟩ : syracuseStep 1785611 = 2678417) B2678417
theorem B1785623 : Blo 1784093 1785623 := bstep (se 1 (by rfl) ⟨1339217, by rfl⟩ : syracuseStep 1785623 = 2678435) B2678435
theorem B1785643 : Blo 1784093 1785643 := bstep (se 1 (by rfl) ⟨1339232, by rfl⟩ : syracuseStep 1785643 = 2678465) B2678465
theorem B4128563 : Blo 1784093 4128563 := bstep (se 1 (by rfl) ⟨3096422, by rfl⟩ : syracuseStep 4128563 = 6192845) B6192845
theorem B1785655 : Blo 1784093 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B1785675 : Blo 1784093 1785675 := bstep (se 1 (by rfl) ⟨1339256, by rfl⟩ : syracuseStep 1785675 = 2678513) B2678513
theorem B2678603 : Blo 1784093 2678603 := bstep (se 1 (by rfl) ⟨2008952, by rfl⟩ : syracuseStep 2678603 = 4017905) B4017905
theorem B1785687 : Blo 1784093 1785687 := bstep (se 1 (by rfl) ⟨1339265, by rfl⟩ : syracuseStep 1785687 = 2678531) B2678531
theorem B2678615 : Blo 1784093 2678615 := bstep (se 1 (by rfl) ⟨2008961, by rfl⟩ : syracuseStep 2678615 = 4017923) B4017923
theorem B1785707 : Blo 1784093 1785707 := bstep (se 1 (by rfl) ⟨1339280, by rfl⟩ : syracuseStep 1785707 = 2678561) B2678561
theorem B1785719 : Blo 1784093 1785719 := bstep (se 1 (by rfl) ⟨1339289, by rfl⟩ : syracuseStep 1785719 = 2678579) B2678579
theorem B1957771 : Blo 1784093 1957771 := bstep (se 1 (by rfl) ⟨1468328, by rfl⟩ : syracuseStep 1957771 = 2936657) B2936657
theorem B1785739 : Blo 1784093 1785739 := bstep (se 1 (by rfl) ⟨1339304, by rfl⟩ : syracuseStep 1785739 = 2678609) B2678609
theorem B1810315 : Blo 1784093 1810315 := bstep (se 1 (by rfl) ⟨1357736, by rfl⟩ : syracuseStep 1810315 = 2715473) B2715473
theorem B1785751 : Blo 1784093 1785751 := bstep (se 1 (by rfl) ⟨1339313, by rfl⟩ : syracuseStep 1785751 = 2678627) B2678627
theorem B2858905 : Blo 1784093 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B2678681 : Blo 1784093 2678681 := bstep (se 2 (by rfl) ⟨1004505, by rfl⟩ : syracuseStep 2678681 = 2009011) B2009011
theorem B1785771 : Blo 1784093 1785771 := bstep (se 1 (by rfl) ⟨1339328, by rfl⟩ : syracuseStep 1785771 = 2678657) B2678657
theorem B1785783 : Blo 1784093 1785783 := bstep (se 1 (by rfl) ⟨1339337, by rfl⟩ : syracuseStep 1785783 = 2678675) B2678675
theorem B1785803 : Blo 1784093 1785803 := bstep (se 1 (by rfl) ⟨1339352, by rfl⟩ : syracuseStep 1785803 = 2678705) B2678705
theorem B1785815 : Blo 1784093 1785815 := bstep (se 1 (by rfl) ⟨1339361, by rfl⟩ : syracuseStep 1785815 = 2678723) B2678723
theorem B6774749 : Blo 1784093 6774749 := bstep (se 3 (by rfl) ⟨1270265, by rfl⟩ : syracuseStep 6774749 = 2540531) B2540531
theorem B1785835 : Blo 1784093 1785835 := bstep (se 1 (by rfl) ⟨1339376, by rfl⟩ : syracuseStep 1785835 = 2678753) B2678753
theorem B1785847 : Blo 1784093 1785847 := bstep (se 1 (by rfl) ⟨1339385, by rfl⟩ : syracuseStep 1785847 = 2678771) B2678771
theorem B1785863 : Blo 1784093 1785863 := bstep (se 1 (by rfl) ⟨1339397, by rfl⟩ : syracuseStep 1785863 = 2678795) B2678795
theorem B1785871 : Blo 1784093 1785871 := bstep (se 1 (by rfl) ⟨1339403, by rfl⟩ : syracuseStep 1785871 = 2678807) B2678807
theorem B2678843 : Blo 1784093 2678843 := bstep (se 1 (by rfl) ⟨2009132, by rfl⟩ : syracuseStep 2678843 = 4018265) B4018265
theorem B1785915 : Blo 1784093 1785915 := bstep (se 1 (by rfl) ⟨1339436, by rfl⟩ : syracuseStep 1785915 = 2678873) B2678873
theorem B7241795 : Blo 1784093 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B2678903 : Blo 1784093 2678903 := bstep (se 1 (by rfl) ⟨2009177, by rfl⟩ : syracuseStep 2678903 = 4018355) B4018355
theorem B4014215 : Blo 1784093 4014215 := bstep (se 1 (by rfl) ⟨3010661, by rfl⟩ : syracuseStep 4014215 = 6021323) B6021323
theorem B2007175 : Blo 1784093 2007175 := bstep (se 1 (by rfl) ⟨1505381, by rfl⟩ : syracuseStep 2007175 = 3010763) B3010763
theorem B1785991 : Blo 1784093 1785991 := bstep (se 1 (by rfl) ⟨1339493, by rfl⟩ : syracuseStep 1785991 = 2678987) B2678987
theorem B2678927 : Blo 1784093 2678927 := bstep (se 1 (by rfl) ⟨2009195, by rfl⟩ : syracuseStep 2678927 = 4018391) B4018391
theorem B1785999 : Blo 1784093 1785999 := bstep (se 1 (by rfl) ⟨1339499, by rfl⟩ : syracuseStep 1785999 = 2678999) B2678999
theorem B2678969 : Blo 1784093 2678969 := bstep (se 2 (by rfl) ⟨1004613, by rfl⟩ : syracuseStep 2678969 = 2009227) B2009227
theorem B1786043 : Blo 1784093 1786043 := bstep (se 1 (by rfl) ⟨1339532, by rfl⟩ : syracuseStep 1786043 = 2679065) B2679065
theorem B17662153 : Blo 1784093 17662153 := bstep (se 2 (by rfl) ⟨6623307, by rfl⟩ : syracuseStep 17662153 = 13246615) B13246615
theorem B6021377 : Blo 1784093 6021377 := bstep (se 2 (by rfl) ⟨2258016, by rfl⟩ : syracuseStep 6021377 = 4516033) B4516033
theorem B2679047 : Blo 1784093 2679047 := bstep (se 1 (by rfl) ⟨2009285, by rfl⟩ : syracuseStep 2679047 = 4018571) B4018571
theorem B10166543 : Blo 1784093 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B2679083 : Blo 1784093 2679083 := bstep (se 1 (by rfl) ⟨2009312, by rfl⟩ : syracuseStep 2679083 = 4018625) B4018625
theorem B4014395 : Blo 1784093 4014395 := bstep (se 1 (by rfl) ⟨3010796, by rfl⟩ : syracuseStep 4014395 = 6021593) B6021593
theorem B2007355 : Blo 1784093 2007355 := bstep (se 1 (by rfl) ⟨1505516, by rfl⟩ : syracuseStep 2007355 = 3011033) B3011033
theorem B2679113 : Blo 1784093 2679113 := bstep (se 2 (by rfl) ⟨1004667, by rfl⟩ : syracuseStep 2679113 = 2009335) B2009335
theorem B4014521 : Blo 1784093 4014521 := bstep (se 2 (by rfl) ⟨1505445, by rfl⟩ : syracuseStep 4014521 = 3010891) B3010891
theorem B13746617 : Blo 1784093 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B10166795 : Blo 1784093 10166795 := bstep (se 1 (by rfl) ⟨7625096, by rfl⟩ : syracuseStep 10166795 = 15250193) B15250193
theorem B17154737 : Blo 1784093 17154737 := bstep (se 2 (by rfl) ⟨6433026, by rfl⟩ : syracuseStep 17154737 = 12866053) B12866053
theorem B4014863 : Blo 1784093 4014863 := bstep (se 1 (by rfl) ⟨3011147, by rfl⟩ : syracuseStep 4014863 = 6022295) B6022295
theorem B2007823 : Blo 1784093 2007823 := bstep (se 1 (by rfl) ⟨1505867, by rfl⟩ : syracuseStep 2007823 = 3011735) B3011735
theorem B4014881 : Blo 1784093 4014881 := bstep (se 2 (by rfl) ⟨1505580, by rfl⟩ : syracuseStep 4014881 = 3011161) B3011161
theorem B2540423 : Blo 1784093 2540423 := bstep (se 1 (by rfl) ⟨1905317, by rfl⟩ : syracuseStep 2540423 = 3810635) B3810635
theorem B5718937 : Blo 1784093 5718937 := bstep (se 2 (by rfl) ⟨2144601, by rfl⟩ : syracuseStep 5718937 = 4289203) B4289203
theorem B6022187 : Blo 1784093 6022187 := bstep (se 1 (by rfl) ⟨4516640, by rfl⟩ : syracuseStep 6022187 = 9033281) B9033281
theorem B4826155 : Blo 1784093 4826155 := bstep (se 1 (by rfl) ⟨3619616, by rfl⟩ : syracuseStep 4826155 = 7239233) B7239233
theorem B30499901 : Blo 1784093 30499901 := bstep (se 3 (by rfl) ⟨5718731, by rfl⟩ : syracuseStep 30499901 = 11437463) B11437463
theorem B4015223 : Blo 1784093 4015223 := bstep (se 1 (by rfl) ⟨3011417, by rfl⟩ : syracuseStep 4015223 = 6022835) B6022835
theorem B17155273 : Blo 1784093 17155273 := bstep (se 2 (by rfl) ⟨6433227, by rfl⟩ : syracuseStep 17155273 = 12866455) B12866455
theorem B2008327 : Blo 1784093 2008327 := bstep (se 1 (by rfl) ⟨1506245, by rfl⟩ : syracuseStep 2008327 = 3012491) B3012491
theorem B4015403 : Blo 1784093 4015403 := bstep (se 1 (by rfl) ⟨3011552, by rfl⟩ : syracuseStep 4015403 = 6023105) B6023105
theorem B41231717 : Blo 1784093 41231717 := bstep (se 4 (by rfl) ⟨3865473, by rfl⟩ : syracuseStep 41231717 = 7730947) B7730947
theorem B13747603 : Blo 1784093 13747603 := bstep (se 1 (by rfl) ⟨10310702, by rfl⟩ : syracuseStep 13747603 = 20621405) B20621405
theorem B2008507 : Blo 1784093 2008507 := bstep (se 1 (by rfl) ⟨1506380, by rfl⟩ : syracuseStep 2008507 = 3012761) B3012761
theorem B2352655 : Blo 1784093 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B14673437 : Blo 1784093 14673437 := bstep (se 3 (by rfl) ⟨2751269, by rfl⟩ : syracuseStep 14673437 = 5502539) B5502539
theorem B4015763 : Blo 1784093 4015763 := bstep (se 1 (by rfl) ⟨3011822, by rfl⟩ : syracuseStep 4015763 = 6023645) B6023645
theorem B10168001 : Blo 1784093 10168001 := bstep (se 2 (by rfl) ⟨3813000, by rfl⟩ : syracuseStep 10168001 = 7626001) B7626001
theorem B4015817 : Blo 1784093 4015817 := bstep (se 2 (by rfl) ⟨1505931, by rfl⟩ : syracuseStep 4015817 = 3011863) B3011863
theorem B3811087 : Blo 1784093 3811087 := bstep (se 1 (by rfl) ⟨2858315, by rfl⟩ : syracuseStep 3811087 = 5716631) B5716631
theorem B8578867 : Blo 1784093 8578867 := bstep (se 1 (by rfl) ⟨6434150, by rfl⟩ : syracuseStep 8578867 = 12868301) B12868301
theorem B2541385 : Blo 1784093 2541385 := bstep (se 2 (by rfl) ⟨953019, by rfl⟩ : syracuseStep 2541385 = 1906039) B1906039
theorem B3811207 : Blo 1784093 3811207 := bstep (se 1 (by rfl) ⟨2858405, by rfl⟩ : syracuseStep 3811207 = 5716811) B5716811
theorem B2008975 : Blo 1784093 2008975 := bstep (se 1 (by rfl) ⟨1506731, by rfl⟩ : syracuseStep 2008975 = 3013463) B3013463
theorem B6776723 : Blo 1784093 6776723 := bstep (se 1 (by rfl) ⟨5082542, by rfl⟩ : syracuseStep 6776723 = 10165085) B10165085
theorem B3811387 : Blo 1784093 3811387 := bstep (se 1 (by rfl) ⟨2858540, by rfl⟩ : syracuseStep 3811387 = 5717081) B5717081
theorem B8144957 : Blo 1784093 8144957 := bstep (se 3 (by rfl) ⟨1527179, by rfl⟩ : syracuseStep 8144957 = 3054359) B3054359
theorem B20334725 : Blo 1784093 20334725 := bstep (se 4 (by rfl) ⟨1906380, by rfl⟩ : syracuseStep 20334725 = 3812761) B3812761
theorem B3811463 : Blo 1784093 3811463 := bstep (se 1 (by rfl) ⟨2858597, by rfl⟩ : syracuseStep 3811463 = 5717195) B5717195
theorem B2713771 : Blo 1784093 2713771 := bstep (se 1 (by rfl) ⟨2035328, by rfl⟩ : syracuseStep 2713771 = 4070657) B4070657
theorem B5720321 : Blo 1784093 5720321 := bstep (se 2 (by rfl) ⟨2145120, by rfl⟩ : syracuseStep 5720321 = 4290241) B4290241
theorem B2541881 : Blo 1784093 2541881 := bstep (se 2 (by rfl) ⟨953205, by rfl⟩ : syracuseStep 2541881 = 1906411) B1906411
theorem B6023483 : Blo 1784093 6023483 := bstep (se 1 (by rfl) ⟨4517612, by rfl⟩ : syracuseStep 6023483 = 9035225) B9035225
theorem B4286839 : Blo 1784093 4286839 := bstep (se 1 (by rfl) ⟨3215129, by rfl⟩ : syracuseStep 4286839 = 6430259) B6430259
theorem B4016519 : Blo 1784093 4016519 := bstep (se 1 (by rfl) ⟨3012389, by rfl⟩ : syracuseStep 4016519 = 6024779) B6024779
theorem B4827539 : Blo 1784093 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B3811873 : Blo 1784093 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B4016699 : Blo 1784093 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B4516499 : Blo 1784093 4516499 := bstep (se 1 (by rfl) ⟨3387374, by rfl⟩ : syracuseStep 4516499 = 6774749) B6774749
theorem B20343473 : Blo 1784093 20343473 := bstep (se 2 (by rfl) ⟨7628802, by rfl⟩ : syracuseStep 20343473 = 15257605) B15257605
theorem B4016825 : Blo 1784093 4016825 := bstep (se 2 (by rfl) ⟨1506309, by rfl⟩ : syracuseStep 4016825 = 3012619) B3012619
theorem B6023969 : Blo 1784093 6023969 := bstep (se 2 (by rfl) ⟨2258988, by rfl⟩ : syracuseStep 6023969 = 4517977) B4517977
theorem B22866725 : Blo 1784093 22866725 := bstep (se 4 (by rfl) ⟨2143755, by rfl⟩ : syracuseStep 22866725 = 4287511) B4287511
theorem B4516793 : Blo 1784093 4516793 := bstep (se 2 (by rfl) ⟨1693797, by rfl⟩ : syracuseStep 4516793 = 3387595) B3387595
theorem B5082041 : Blo 1784093 5082041 := bstep (se 2 (by rfl) ⟨1905765, by rfl⟩ : syracuseStep 5082041 = 3811531) B3811531
theorem B20327435 : Blo 1784093 20327435 := bstep (se 1 (by rfl) ⟨15245576, by rfl⟩ : syracuseStep 20327435 = 30491153) B30491153
theorem B4017167 : Blo 1784093 4017167 := bstep (se 1 (by rfl) ⟨3012875, by rfl⟩ : syracuseStep 4017167 = 6025751) B6025751
theorem B7334941 : Blo 1784093 7334941 := bstep (se 3 (by rfl) ⟨1375301, by rfl⟩ : syracuseStep 7334941 = 2750603) B2750603
theorem B4017185 : Blo 1784093 4017185 := bstep (se 2 (by rfl) ⟨1506444, by rfl⟩ : syracuseStep 4017185 = 3012889) B3012889
theorem B31329341 : Blo 1784093 31329341 := bstep (se 3 (by rfl) ⟨5874251, by rfl⟩ : syracuseStep 31329341 = 11748503) B11748503
theorem B7728385 : Blo 1784093 7728385 := bstep (se 2 (by rfl) ⟨2898144, by rfl⟩ : syracuseStep 7728385 = 5796289) B5796289
theorem B2542855 : Blo 1784093 2542855 := bstep (se 1 (by rfl) ⟨1907141, by rfl⟩ : syracuseStep 2542855 = 3814283) B3814283
theorem B2174251 : Blo 1784093 2174251 := bstep (se 1 (by rfl) ⟨1630688, by rfl⟩ : syracuseStep 2174251 = 3261377) B3261377
theorem B38620475 : Blo 1784093 38620475 := bstep (se 1 (by rfl) ⟨28965356, by rfl⟩ : syracuseStep 38620475 = 57930713) B57930713
theorem B6024563 : Blo 1784093 6024563 := bstep (se 1 (by rfl) ⟨4518422, by rfl⟩ : syracuseStep 6024563 = 9036845) B9036845
theorem B8146291 : Blo 1784093 8146291 := bstep (se 1 (by rfl) ⟨6109718, by rfl⟩ : syracuseStep 8146291 = 12219437) B12219437
theorem B4017527 : Blo 1784093 4017527 := bstep (se 1 (by rfl) ⟨3013145, by rfl⟩ : syracuseStep 4017527 = 6026291) B6026291
theorem B11431313 : Blo 1784093 11431313 := bstep (se 2 (by rfl) ⟨4286742, by rfl⟩ : syracuseStep 11431313 = 8573485) B8573485
theorem B12209555 : Blo 1784093 12209555 := bstep (se 1 (by rfl) ⟨9157166, by rfl⟩ : syracuseStep 12209555 = 18314333) B18314333
theorem B13553081 : Blo 1784093 13553081 := bstep (se 2 (by rfl) ⟨5082405, by rfl⟩ : syracuseStep 13553081 = 10164811) B10164811
theorem B4017707 : Blo 1784093 4017707 := bstep (se 1 (by rfl) ⟨3013280, by rfl⟩ : syracuseStep 4017707 = 6026561) B6026561
theorem B4517491 : Blo 1784093 4517491 := bstep (se 1 (by rfl) ⟨3388118, by rfl⟩ : syracuseStep 4517491 = 6776237) B6776237
theorem B4517633 : Blo 1784093 4517633 := bstep (se 2 (by rfl) ⟨1694112, by rfl⟩ : syracuseStep 4517633 = 3388225) B3388225
theorem B7622515 : Blo 1784093 7622515 := bstep (se 1 (by rfl) ⟨5716886, by rfl⟩ : syracuseStep 7622515 = 11433773) B11433773
theorem B9039761 : Blo 1784093 9039761 := bstep (se 2 (by rfl) ⟨3389910, by rfl⟩ : syracuseStep 9039761 = 6779821) B6779821
theorem B10858387 : Blo 1784093 10858387 := bstep (se 1 (by rfl) ⟨8143790, by rfl⟩ : syracuseStep 10858387 = 16287581) B16287581
theorem B4018067 : Blo 1784093 4018067 := bstep (se 1 (by rfl) ⟨3013550, by rfl⟩ : syracuseStep 4018067 = 6027101) B6027101
theorem B5083033 : Blo 1784093 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B7622585 : Blo 1784093 7622585 := bstep (se 2 (by rfl) ⟨2858469, by rfl⟩ : syracuseStep 7622585 = 5716939) B5716939
theorem B4018121 : Blo 1784093 4018121 := bstep (se 2 (by rfl) ⟨1506795, by rfl⟩ : syracuseStep 4018121 = 3013591) B3013591
theorem B14479307 : Blo 1784093 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B9646123 : Blo 1784093 9646123 := bstep (se 1 (by rfl) ⟨7234592, by rfl⟩ : syracuseStep 9646123 = 14469185) B14469185
theorem B3387511 : Blo 1784093 3387511 := bstep (se 1 (by rfl) ⟨2540633, by rfl⟩ : syracuseStep 3387511 = 5081267) B5081267
theorem B2412731 : Blo 1784093 2412731 := bstep (se 1 (by rfl) ⟨1809548, by rfl⟩ : syracuseStep 2412731 = 3619097) B3619097
theorem B4518089 : Blo 1784093 4518089 := bstep (se 2 (by rfl) ⟨1694283, by rfl⟩ : syracuseStep 4518089 = 3388567) B3388567
theorem B6435073 : Blo 1784093 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B11432339 : Blo 1784093 11432339 := bstep (se 1 (by rfl) ⟨8574254, by rfl⟩ : syracuseStep 11432339 = 17148509) B17148509
theorem B3813779 : Blo 1784093 3813779 := bstep (se 1 (by rfl) ⟨2860334, by rfl⟩ : syracuseStep 3813779 = 5720669) B5720669
theorem B6779321 : Blo 1784093 6779321 := bstep (se 2 (by rfl) ⟨2542245, by rfl⟩ : syracuseStep 6779321 = 5084491) B5084491
theorem B3011087 : Blo 1784093 3011087 := bstep (se 1 (by rfl) ⟨2258315, by rfl⟩ : syracuseStep 3011087 = 4516631) B4516631
theorem B21705245 : Blo 1784093 21705245 := bstep (se 3 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 21705245 = 8139467) B8139467
theorem B4518443 : Blo 1784093 4518443 := bstep (se 1 (by rfl) ⟨3388832, by rfl⟩ : syracuseStep 4518443 = 6777665) B6777665
theorem B3666551 : Blo 1784093 3666551 := bstep (se 1 (by rfl) ⟨2749913, by rfl⟩ : syracuseStep 3666551 = 5499827) B5499827
theorem B1905287 : Blo 1784093 1905287 := bstep (se 1 (by rfl) ⟨1428965, by rfl⟩ : syracuseStep 1905287 = 2857931) B2857931
theorem B10441445 : Blo 1784093 10441445 := bstep (se 4 (by rfl) ⟨978885, by rfl⟩ : syracuseStep 10441445 = 1957771) B1957771
theorem B9655013 : Blo 1784093 9655013 := bstep (se 4 (by rfl) ⟨905157, by rfl⟩ : syracuseStep 9655013 = 1810315) B1810315
theorem B10171169 : Blo 1784093 10171169 := bstep (se 2 (by rfl) ⟨3814188, by rfl⟩ : syracuseStep 10171169 = 7628377) B7628377
theorem B9032633 : Blo 1784093 9032633 := bstep (se 2 (by rfl) ⟨3387237, by rfl⟩ : syracuseStep 9032633 = 6774475) B6774475
theorem B16290827 : Blo 1784093 16290827 := bstep (se 1 (by rfl) ⟨12218120, by rfl⟩ : syracuseStep 16290827 = 24436241) B24436241
theorem B3011627 : Blo 1784093 3011627 := bstep (se 1 (by rfl) ⟨2258720, by rfl⟩ : syracuseStep 3011627 = 4517441) B4517441
theorem B6436111 : Blo 1784093 6436111 := bstep (se 1 (by rfl) ⟨4827083, by rfl⟩ : syracuseStep 6436111 = 9654167) B9654167
theorem B2258219 : Blo 1784093 2258219 := bstep (se 1 (by rfl) ⟨1693664, by rfl⟩ : syracuseStep 2258219 = 3387329) B3387329
theorem B9647507 : Blo 1784093 9647507 := bstep (se 1 (by rfl) ⟨7235630, by rfl⟩ : syracuseStep 9647507 = 14471261) B14471261
theorem B6780307 : Blo 1784093 6780307 := bstep (se 1 (by rfl) ⟨5085230, by rfl⟩ : syracuseStep 6780307 = 10170461) B10170461
theorem B3012025 : Blo 1784093 3012025 := bstep (se 2 (by rfl) ⟨1129509, by rfl⟩ : syracuseStep 3012025 = 2259019) B2259019
theorem B2676155 : Blo 1784093 2676155 := bstep (se 1 (by rfl) ⟨2007116, by rfl⟩ : syracuseStep 2676155 = 4014233) B4014233
theorem B2676215 : Blo 1784093 2676215 := bstep (se 1 (by rfl) ⟨2007161, by rfl⟩ : syracuseStep 2676215 = 4014323) B4014323
theorem B4519435 : Blo 1784093 4519435 := bstep (se 1 (by rfl) ⟨3389576, by rfl⟩ : syracuseStep 4519435 = 6779153) B6779153
theorem B2676239 : Blo 1784093 2676239 := bstep (se 1 (by rfl) ⟨2007179, by rfl⟩ : syracuseStep 2676239 = 4014359) B4014359
theorem B2676281 : Blo 1784093 2676281 := bstep (se 2 (by rfl) ⟨1003605, by rfl⟩ : syracuseStep 2676281 = 2007211) B2007211
theorem B2676359 : Blo 1784093 2676359 := bstep (se 1 (by rfl) ⟨2007269, by rfl⟩ : syracuseStep 2676359 = 4014539) B4014539
theorem B4519577 : Blo 1784093 4519577 := bstep (se 2 (by rfl) ⟨1694841, by rfl⟩ : syracuseStep 4519577 = 3389683) B3389683
theorem B2676395 : Blo 1784093 2676395 := bstep (se 1 (by rfl) ⟨2007296, by rfl⟩ : syracuseStep 2676395 = 4014593) B4014593
theorem B2676425 : Blo 1784093 2676425 := bstep (se 2 (by rfl) ⟨1003659, by rfl⟩ : syracuseStep 2676425 = 2007319) B2007319
theorem B25720577 : Blo 1784093 25720577 := bstep (se 2 (by rfl) ⟨9645216, by rfl⟩ : syracuseStep 25720577 = 19290433) B19290433
theorem B2258695 : Blo 1784093 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B5084957 : Blo 1784093 5084957 := bstep (se 3 (by rfl) ⟨953429, by rfl⟩ : syracuseStep 5084957 = 1906859) B1906859
theorem B2676539 : Blo 1784093 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B4519739 : Blo 1784093 4519739 := bstep (se 1 (by rfl) ⟨3389804, by rfl⟩ : syracuseStep 4519739 = 6779609) B6779609
theorem B10860403 : Blo 1784093 10860403 := bstep (se 1 (by rfl) ⟨8145302, by rfl⟩ : syracuseStep 10860403 = 16290605) B16290605
theorem B2676599 : Blo 1784093 2676599 := bstep (se 1 (by rfl) ⟨2007449, by rfl⟩ : syracuseStep 2676599 = 4014899) B4014899
theorem B3389303 : Blo 1784093 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B2676623 : Blo 1784093 2676623 := bstep (se 1 (by rfl) ⟨2007467, by rfl⟩ : syracuseStep 2676623 = 4014935) B4014935
theorem B6027155 : Blo 1784093 6027155 := bstep (se 1 (by rfl) ⟨4520366, by rfl⟩ : syracuseStep 6027155 = 9040733) B9040733
theorem B7624601 : Blo 1784093 7624601 := bstep (se 2 (by rfl) ⟨2859225, by rfl⟩ : syracuseStep 7624601 = 5718451) B5718451
theorem B2676665 : Blo 1784093 2676665 := bstep (se 2 (by rfl) ⟨1003749, by rfl⟩ : syracuseStep 2676665 = 2007499) B2007499
theorem B9041867 : Blo 1784093 9041867 := bstep (se 1 (by rfl) ⟨6781400, by rfl⟩ : syracuseStep 9041867 = 13562801) B13562801
theorem B2676743 : Blo 1784093 2676743 := bstep (se 1 (by rfl) ⟨2007557, by rfl⟩ : syracuseStep 2676743 = 4015115) B4015115
theorem B3389455 : Blo 1784093 3389455 := bstep (se 1 (by rfl) ⟨2542091, by rfl⟩ : syracuseStep 3389455 = 5084183) B5084183
theorem B2676779 : Blo 1784093 2676779 := bstep (se 1 (by rfl) ⟨2007584, by rfl⟩ : syracuseStep 2676779 = 4015169) B4015169
theorem B6436907 : Blo 1784093 6436907 := bstep (se 1 (by rfl) ⟨4827680, by rfl⟩ : syracuseStep 6436907 = 9655361) B9655361
theorem B2676809 : Blo 1784093 2676809 := bstep (se 2 (by rfl) ⟨1003803, by rfl⟩ : syracuseStep 2676809 = 2007607) B2007607
theorem B10164311 : Blo 1784093 10164311 := bstep (se 1 (by rfl) ⟨7623233, by rfl⟩ : syracuseStep 10164311 = 15246467) B15246467
theorem B3012727 : Blo 1784093 3012727 := bstep (se 1 (by rfl) ⟨2259545, by rfl⟩ : syracuseStep 3012727 = 4519091) B4519091
theorem B4520083 : Blo 1784093 4520083 := bstep (se 1 (by rfl) ⟨3390062, by rfl⟩ : syracuseStep 4520083 = 6780125) B6780125
theorem B2676923 : Blo 1784093 2676923 := bstep (se 1 (by rfl) ⟨2007692, by rfl⟩ : syracuseStep 2676923 = 4015385) B4015385
theorem B9033929 : Blo 1784093 9033929 := bstep (se 2 (by rfl) ⟨3387723, by rfl⟩ : syracuseStep 9033929 = 6775447) B6775447
theorem B5503177 : Blo 1784093 5503177 := bstep (se 2 (by rfl) ⟨2063691, by rfl⟩ : syracuseStep 5503177 = 4127383) B4127383
theorem B2676983 : Blo 1784093 2676983 := bstep (se 1 (by rfl) ⟨2007737, by rfl⟩ : syracuseStep 2676983 = 4015475) B4015475
theorem B2259191 : Blo 1784093 2259191 := bstep (se 1 (by rfl) ⟨1694393, by rfl⟩ : syracuseStep 2259191 = 3388787) B3388787
theorem B7624961 : Blo 1784093 7624961 := bstep (se 2 (by rfl) ⟨2859360, by rfl⟩ : syracuseStep 7624961 = 5718721) B5718721
theorem B2677007 : Blo 1784093 2677007 := bstep (se 1 (by rfl) ⟨2007755, by rfl⟩ : syracuseStep 2677007 = 4015511) B4015511
theorem B4520225 : Blo 1784093 4520225 := bstep (se 2 (by rfl) ⟨1695084, by rfl⟩ : syracuseStep 4520225 = 3390169) B3390169
theorem B2677049 : Blo 1784093 2677049 := bstep (se 2 (by rfl) ⟨1003893, by rfl⟩ : syracuseStep 2677049 = 2007787) B2007787
theorem B1784123 : Blo 1784093 1784123 := bstep (se 1 (by rfl) ⟨1338092, by rfl⟩ : syracuseStep 1784123 = 2676185) B2676185
theorem B3012923 : Blo 1784093 3012923 := bstep (se 1 (by rfl) ⟨2259692, by rfl⟩ : syracuseStep 3012923 = 4519385) B4519385
theorem B1784199 : Blo 1784093 1784199 := bstep (se 1 (by rfl) ⟨1338149, by rfl⟩ : syracuseStep 1784199 = 2676299) B2676299
theorem B2677127 : Blo 1784093 2677127 := bstep (se 1 (by rfl) ⟨2007845, by rfl⟩ : syracuseStep 2677127 = 4015691) B4015691
theorem B1784207 : Blo 1784093 1784207 := bstep (se 1 (by rfl) ⟨1338155, by rfl⟩ : syracuseStep 1784207 = 2676311) B2676311
theorem B2259343 : Blo 1784093 2259343 := bstep (se 1 (by rfl) ⟨1694507, by rfl⟩ : syracuseStep 2259343 = 3389015) B3389015
theorem B3389843 : Blo 1784093 3389843 := bstep (se 1 (by rfl) ⟨2542382, by rfl⟩ : syracuseStep 3389843 = 5084765) B5084765
theorem B2677163 : Blo 1784093 2677163 := bstep (se 1 (by rfl) ⟨2007872, by rfl⟩ : syracuseStep 2677163 = 4015745) B4015745
theorem B1784251 : Blo 1784093 1784251 := bstep (se 1 (by rfl) ⟨1338188, by rfl⟩ : syracuseStep 1784251 = 2676377) B2676377
theorem B2677193 : Blo 1784093 2677193 := bstep (se 2 (by rfl) ⟨1003947, by rfl⟩ : syracuseStep 2677193 = 2007895) B2007895
theorem B5085641 : Blo 1784093 5085641 := bstep (se 2 (by rfl) ⟨1907115, by rfl⟩ : syracuseStep 5085641 = 3814231) B3814231
theorem B1784327 : Blo 1784093 1784327 := bstep (se 1 (by rfl) ⟨1338245, by rfl⟩ : syracuseStep 1784327 = 2676491) B2676491
theorem B1784335 : Blo 1784093 1784335 := bstep (se 1 (by rfl) ⟨1338251, by rfl⟩ : syracuseStep 1784335 = 2676503) B2676503
theorem B1784379 : Blo 1784093 1784379 := bstep (se 1 (by rfl) ⟨1338284, by rfl⟩ : syracuseStep 1784379 = 2676569) B2676569
theorem B2677307 : Blo 1784093 2677307 := bstep (se 1 (by rfl) ⟨2007980, by rfl⟩ : syracuseStep 2677307 = 4015961) B4015961
theorem B2259515 : Blo 1784093 2259515 := bstep (se 1 (by rfl) ⟨1694636, by rfl⟩ : syracuseStep 2259515 = 3389273) B3389273
theorem B2677367 : Blo 1784093 2677367 := bstep (se 1 (by rfl) ⟨2008025, by rfl⟩ : syracuseStep 2677367 = 4016051) B4016051
theorem B1784455 : Blo 1784093 1784455 := bstep (se 1 (by rfl) ⟨1338341, by rfl⟩ : syracuseStep 1784455 = 2676683) B2676683
theorem B1784463 : Blo 1784093 1784463 := bstep (se 1 (by rfl) ⟨1338347, by rfl⟩ : syracuseStep 1784463 = 2676695) B2676695
theorem B2677391 : Blo 1784093 2677391 := bstep (se 1 (by rfl) ⟨2008043, by rfl⟩ : syracuseStep 2677391 = 4016087) B4016087
theorem B2677433 : Blo 1784093 2677433 := bstep (se 2 (by rfl) ⟨1004037, by rfl⟩ : syracuseStep 2677433 = 2008075) B2008075
theorem B1784507 : Blo 1784093 1784507 := bstep (se 1 (by rfl) ⟨1338380, by rfl⟩ : syracuseStep 1784507 = 2676761) B2676761
theorem B3013321 : Blo 1784093 3013321 := bstep (se 2 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 3013321 = 2259991) B2259991
theorem B1784583 : Blo 1784093 1784583 := bstep (se 1 (by rfl) ⟨1338437, by rfl⟩ : syracuseStep 1784583 = 2676875) B2676875
theorem B2677511 : Blo 1784093 2677511 := bstep (se 1 (by rfl) ⟨2008133, by rfl⟩ : syracuseStep 2677511 = 4016267) B4016267
theorem B1784591 : Blo 1784093 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B25787173 : Blo 1784093 25787173 := bstep (se 4 (by rfl) ⟨2417547, by rfl⟩ : syracuseStep 25787173 = 4835095) B4835095
theorem B2677547 : Blo 1784093 2677547 := bstep (se 1 (by rfl) ⟨2008160, by rfl⟩ : syracuseStep 2677547 = 4016321) B4016321
theorem B1784635 : Blo 1784093 1784635 := bstep (se 1 (by rfl) ⟨1338476, by rfl⟩ : syracuseStep 1784635 = 2676953) B2676953
theorem B2677577 : Blo 1784093 2677577 := bstep (se 2 (by rfl) ⟨1004091, by rfl⟩ : syracuseStep 2677577 = 2008183) B2008183
theorem B75307877 : Blo 1784093 75307877 := bstep (se 4 (by rfl) ⟨7060113, by rfl⟩ : syracuseStep 75307877 = 14120227) B14120227
theorem B1784711 : Blo 1784093 1784711 := bstep (se 1 (by rfl) ⟨1338533, by rfl⟩ : syracuseStep 1784711 = 2677067) B2677067
theorem B1784719 : Blo 1784093 1784719 := bstep (se 1 (by rfl) ⟨1338539, by rfl⟩ : syracuseStep 1784719 = 2677079) B2677079
theorem B1784763 : Blo 1784093 1784763 := bstep (se 1 (by rfl) ⟨1338572, by rfl⟩ : syracuseStep 1784763 = 2677145) B2677145
theorem B2677691 : Blo 1784093 2677691 := bstep (se 1 (by rfl) ⟨2008268, by rfl⟩ : syracuseStep 2677691 = 4016537) B4016537
theorem B321584089 : Blo 1784093 321584089 := bstep (se 2 (by rfl) ⟨120594033, by rfl⟩ : syracuseStep 321584089 = 241188067) B241188067
theorem B2677751 : Blo 1784093 2677751 := bstep (se 1 (by rfl) ⟨2008313, by rfl⟩ : syracuseStep 2677751 = 4016627) B4016627
theorem B1784839 : Blo 1784093 1784839 := bstep (se 1 (by rfl) ⟨1338629, by rfl⟩ : syracuseStep 1784839 = 2677259) B2677259
theorem B1784847 : Blo 1784093 1784847 := bstep (se 1 (by rfl) ⟨1338635, by rfl⟩ : syracuseStep 1784847 = 2677271) B2677271
theorem B2677775 : Blo 1784093 2677775 := bstep (se 1 (by rfl) ⟨2008331, by rfl⟩ : syracuseStep 2677775 = 4016663) B4016663
theorem B2677817 : Blo 1784093 2677817 := bstep (se 2 (by rfl) ⟨1004181, by rfl⟩ : syracuseStep 2677817 = 2008363) B2008363
theorem B1784891 : Blo 1784093 1784891 := bstep (se 1 (by rfl) ⟨1338668, by rfl⟩ : syracuseStep 1784891 = 2677337) B2677337
theorem B77225021 : Blo 1784093 77225021 := bstep (se 3 (by rfl) ⟨14479691, by rfl⟩ : syracuseStep 77225021 = 28959383) B28959383
theorem B7240823 : Blo 1784093 7240823 := bstep (se 1 (by rfl) ⟨5430617, by rfl⟩ : syracuseStep 7240823 = 10861235) B10861235
theorem B1784967 : Blo 1784093 1784967 := bstep (se 1 (by rfl) ⟨1338725, by rfl⟩ : syracuseStep 1784967 = 2677451) B2677451
theorem B2677895 : Blo 1784093 2677895 := bstep (se 1 (by rfl) ⟨2008421, by rfl⟩ : syracuseStep 2677895 = 4016843) B4016843
theorem B1784975 : Blo 1784093 1784975 := bstep (se 1 (by rfl) ⟨1338731, by rfl⟩ : syracuseStep 1784975 = 2677463) B2677463
theorem B2677931 : Blo 1784093 2677931 := bstep (se 1 (by rfl) ⟨2008448, by rfl⟩ : syracuseStep 2677931 = 4016897) B4016897
theorem B352304309 : Blo 1784093 352304309 := bstep (se 5 (by rfl) ⟨16514264, by rfl⟩ : syracuseStep 352304309 = 33028529) B33028529
theorem B1785019 : Blo 1784093 1785019 := bstep (se 1 (by rfl) ⟨1338764, by rfl⟩ : syracuseStep 1785019 = 2677529) B2677529
theorem B2677961 : Blo 1784093 2677961 := bstep (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) B2008471
theorem B1785095 : Blo 1784093 1785095 := bstep (se 1 (by rfl) ⟨1338821, by rfl⟩ : syracuseStep 1785095 = 2677643) B2677643
theorem B1785103 : Blo 1784093 1785103 := bstep (se 1 (by rfl) ⟨1338827, by rfl⟩ : syracuseStep 1785103 = 2677655) B2677655
theorem B20331809 : Blo 1784093 20331809 := bstep (se 2 (by rfl) ⟨7624428, by rfl⟩ : syracuseStep 20331809 = 15248857) B15248857
theorem B1785147 : Blo 1784093 1785147 := bstep (se 1 (by rfl) ⟨1338860, by rfl⟩ : syracuseStep 1785147 = 2677721) B2677721
theorem B2678075 : Blo 1784093 2678075 := bstep (se 1 (by rfl) ⟨2008556, by rfl⟩ : syracuseStep 2678075 = 4017113) B4017113
theorem B2678135 : Blo 1784093 2678135 := bstep (se 1 (by rfl) ⟨2008601, by rfl⟩ : syracuseStep 2678135 = 4017203) B4017203
theorem B1785223 : Blo 1784093 1785223 := bstep (se 1 (by rfl) ⟨1338917, by rfl⟩ : syracuseStep 1785223 = 2677835) B2677835
theorem B3014023 : Blo 1784093 3014023 := bstep (se 1 (by rfl) ⟨2260517, by rfl⟩ : syracuseStep 3014023 = 4521035) B4521035
theorem B1785231 : Blo 1784093 1785231 := bstep (se 1 (by rfl) ⟨1338923, by rfl⟩ : syracuseStep 1785231 = 2677847) B2677847
theorem B2678159 : Blo 1784093 2678159 := bstep (se 1 (by rfl) ⟨2008619, by rfl⟩ : syracuseStep 2678159 = 4017239) B4017239
theorem B2678201 : Blo 1784093 2678201 := bstep (se 2 (by rfl) ⟨1004325, by rfl⟩ : syracuseStep 2678201 = 2008651) B2008651
theorem B1785275 : Blo 1784093 1785275 := bstep (se 1 (by rfl) ⟨1338956, by rfl⟩ : syracuseStep 1785275 = 2677913) B2677913
theorem B1785351 : Blo 1784093 1785351 := bstep (se 1 (by rfl) ⟨1339013, by rfl⟩ : syracuseStep 1785351 = 2678027) B2678027
theorem B2678279 : Blo 1784093 2678279 := bstep (se 1 (by rfl) ⟨2008709, by rfl⟩ : syracuseStep 2678279 = 4017419) B4017419
theorem B2260487 : Blo 1784093 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B1785359 : Blo 1784093 1785359 := bstep (se 1 (by rfl) ⟨1339019, by rfl⟩ : syracuseStep 1785359 = 2678039) B2678039
theorem B2678315 : Blo 1784093 2678315 := bstep (se 1 (by rfl) ⟨2008736, by rfl⟩ : syracuseStep 2678315 = 4017473) B4017473
theorem B1785403 : Blo 1784093 1785403 := bstep (se 1 (by rfl) ⟨1339052, by rfl⟩ : syracuseStep 1785403 = 2678105) B2678105
theorem B2678345 : Blo 1784093 2678345 := bstep (se 2 (by rfl) ⟨1004379, by rfl⟩ : syracuseStep 2678345 = 2008759) B2008759
theorem B1785479 : Blo 1784093 1785479 := bstep (se 1 (by rfl) ⟨1339109, by rfl⟩ : syracuseStep 1785479 = 2678219) B2678219
theorem B1785487 : Blo 1784093 1785487 := bstep (se 1 (by rfl) ⟨1339115, by rfl⟩ : syracuseStep 1785487 = 2678231) B2678231
theorem B1785531 : Blo 1784093 1785531 := bstep (se 1 (by rfl) ⟨1339148, by rfl⟩ : syracuseStep 1785531 = 2678297) B2678297
theorem B2678459 : Blo 1784093 2678459 := bstep (se 1 (by rfl) ⟨2008844, by rfl⟩ : syracuseStep 2678459 = 4017689) B4017689
theorem B2678519 : Blo 1784093 2678519 := bstep (se 1 (by rfl) ⟨2008889, by rfl⟩ : syracuseStep 2678519 = 4017779) B4017779
theorem B1785607 : Blo 1784093 1785607 := bstep (se 1 (by rfl) ⟨1339205, by rfl⟩ : syracuseStep 1785607 = 2678411) B2678411
theorem B1785615 : Blo 1784093 1785615 := bstep (se 1 (by rfl) ⟨1339211, by rfl⟩ : syracuseStep 1785615 = 2678423) B2678423
theorem B2678543 : Blo 1784093 2678543 := bstep (se 1 (by rfl) ⟨2008907, by rfl⟩ : syracuseStep 2678543 = 4017815) B4017815
theorem B10862351 : Blo 1784093 10862351 := bstep (se 1 (by rfl) ⟨8146763, by rfl⟩ : syracuseStep 10862351 = 16293527) B16293527
theorem B24420145 : Blo 1784093 24420145 := bstep (se 2 (by rfl) ⟨9157554, by rfl⟩ : syracuseStep 24420145 = 18315109) B18315109
theorem B34316081 : Blo 1784093 34316081 := bstep (se 2 (by rfl) ⟨12868530, by rfl⟩ : syracuseStep 34316081 = 25737061) B25737061
theorem B2678585 : Blo 1784093 2678585 := bstep (se 2 (by rfl) ⟨1004469, by rfl⟩ : syracuseStep 2678585 = 2008939) B2008939
theorem B1785659 : Blo 1784093 1785659 := bstep (se 1 (by rfl) ⟨1339244, by rfl⟩ : syracuseStep 1785659 = 2678489) B2678489
theorem B2752375 : Blo 1784093 2752375 := bstep (se 1 (by rfl) ⟨2064281, by rfl⟩ : syracuseStep 2752375 = 4128563) B4128563
theorem B1785735 : Blo 1784093 1785735 := bstep (se 1 (by rfl) ⟨1339301, by rfl⟩ : syracuseStep 1785735 = 2678603) B2678603
theorem B2678663 : Blo 1784093 2678663 := bstep (se 1 (by rfl) ⟨2008997, by rfl⟩ : syracuseStep 2678663 = 4017995) B4017995
theorem B1785743 : Blo 1784093 1785743 := bstep (se 1 (by rfl) ⟨1339307, by rfl⟩ : syracuseStep 1785743 = 2678615) B2678615
theorem B2678699 : Blo 1784093 2678699 := bstep (se 1 (by rfl) ⟨2009024, by rfl⟩ : syracuseStep 2678699 = 4018049) B4018049
theorem B1785787 : Blo 1784093 1785787 := bstep (se 1 (by rfl) ⟨1339340, by rfl⟩ : syracuseStep 1785787 = 2678681) B2678681
theorem B2678729 : Blo 1784093 2678729 := bstep (se 2 (by rfl) ⟨1004523, by rfl⟩ : syracuseStep 2678729 = 2009047) B2009047
theorem B1785895 : Blo 1784093 1785895 := bstep (se 1 (by rfl) ⟨1339421, by rfl⟩ : syracuseStep 1785895 = 2678843) B2678843
theorem B12861497 : Blo 1784093 12861497 := bstep (se 2 (by rfl) ⟨4823061, by rfl⟩ : syracuseStep 12861497 = 9646123) B9646123
theorem B1785935 : Blo 1784093 1785935 := bstep (se 1 (by rfl) ⟨1339451, by rfl⟩ : syracuseStep 1785935 = 2678903) B2678903
theorem B1785951 : Blo 1784093 1785951 := bstep (se 1 (by rfl) ⟨1339463, by rfl⟩ : syracuseStep 1785951 = 2678927) B2678927
theorem B1785979 : Blo 1784093 1785979 := bstep (se 1 (by rfl) ⟨1339484, by rfl⟩ : syracuseStep 1785979 = 2678969) B2678969
theorem B4014251 : Blo 1784093 4014251 := bstep (se 1 (by rfl) ⟨3010688, by rfl⟩ : syracuseStep 4014251 = 6021377) B6021377
theorem B1786031 : Blo 1784093 1786031 := bstep (se 1 (by rfl) ⟨1339523, by rfl⟩ : syracuseStep 1786031 = 2679047) B2679047
theorem B1786055 : Blo 1784093 1786055 := bstep (se 1 (by rfl) ⟨1339541, by rfl⟩ : syracuseStep 1786055 = 2679083) B2679083
theorem B1786075 : Blo 1784093 1786075 := bstep (se 1 (by rfl) ⟨1339556, by rfl⟩ : syracuseStep 1786075 = 2679113) B2679113
theorem B2007391 : Blo 1784093 2007391 := bstep (se 1 (by rfl) ⟨1505543, by rfl⟩ : syracuseStep 2007391 = 3011087) B3011087
theorem B11436491 : Blo 1784093 11436491 := bstep (se 1 (by rfl) ⟨8577368, by rfl⟩ : syracuseStep 11436491 = 17154737) B17154737
theorem B6021755 : Blo 1784093 6021755 := bstep (se 1 (by rfl) ⟨4516316, by rfl⟩ : syracuseStep 6021755 = 9032633) B9032633
theorem B15254189 : Blo 1784093 15254189 := bstep (se 3 (by rfl) ⟨2860160, by rfl⟩ : syracuseStep 15254189 = 5720321) B5720321
theorem B4014791 : Blo 1784093 4014791 := bstep (se 1 (by rfl) ⟨3011093, by rfl⟩ : syracuseStep 4014791 = 6022187) B6022187
theorem B2007751 : Blo 1784093 2007751 := bstep (se 1 (by rfl) ⟨1505813, by rfl⟩ : syracuseStep 2007751 = 3011627) B3011627
theorem B20333267 : Blo 1784093 20333267 := bstep (se 1 (by rfl) ⟨15249950, by rfl⟩ : syracuseStep 20333267 = 30499901) B30499901
theorem B6021917 : Blo 1784093 6021917 := bstep (se 3 (by rfl) ⟨1129109, by rfl⟩ : syracuseStep 6021917 = 2258219) B2258219
theorem B6431671 : Blo 1784093 6431671 := bstep (se 1 (by rfl) ⟨4823753, by rfl⟩ : syracuseStep 6431671 = 9647507) B9647507
theorem B9782291 : Blo 1784093 9782291 := bstep (se 1 (by rfl) ⟨7336718, by rfl⟩ : syracuseStep 9782291 = 14673437) B14673437
theorem B34382897 : Blo 1784093 34382897 := bstep (se 2 (by rfl) ⟨12893586, by rfl⟩ : syracuseStep 34382897 = 25787173) B25787173
theorem B17147051 : Blo 1784093 17147051 := bstep (se 1 (by rfl) ⟨12860288, by rfl⟩ : syracuseStep 17147051 = 25720577) B25720577
theorem B428778785 : Blo 1784093 428778785 := bstep (se 2 (by rfl) ⟨160792044, by rfl⟩ : syracuseStep 428778785 = 321584089) B321584089
theorem B6776207 : Blo 1784093 6776207 := bstep (se 1 (by rfl) ⟨5082155, by rfl⟩ : syracuseStep 6776207 = 10164311) B10164311
theorem B2540975 : Blo 1784093 2540975 := bstep (se 1 (by rfl) ⟨1905731, by rfl⟩ : syracuseStep 2540975 = 3811463) B3811463
theorem B6022619 : Blo 1784093 6022619 := bstep (se 1 (by rfl) ⟨4516964, by rfl⟩ : syracuseStep 6022619 = 9033929) B9033929
theorem B4015655 : Blo 1784093 4015655 := bstep (se 1 (by rfl) ⟨3011741, by rfl⟩ : syracuseStep 4015655 = 6023483) B6023483
theorem B2008615 : Blo 1784093 2008615 := bstep (se 1 (by rfl) ⟨1506461, by rfl⟩ : syracuseStep 2008615 = 3012923) B3012923
theorem B22873697 : Blo 1784093 22873697 := bstep (se 2 (by rfl) ⟨8577636, by rfl⟩ : syracuseStep 22873697 = 17155273) B17155273
theorem B4015979 : Blo 1784093 4015979 := bstep (se 1 (by rfl) ⟨3011984, by rfl⟩ : syracuseStep 4015979 = 6023969) B6023969
theorem B4016033 : Blo 1784093 4016033 := bstep (se 2 (by rfl) ⟨1506012, by rfl⟩ : syracuseStep 4016033 = 3012025) B3012025
theorem B13551623 : Blo 1784093 13551623 := bstep (se 1 (by rfl) ⟨10163717, by rfl⟩ : syracuseStep 13551623 = 20327435) B20327435
theorem B13559885 : Blo 1784093 13559885 := bstep (se 3 (by rfl) ⟨2542478, by rfl⟩ : syracuseStep 13559885 = 5084957) B5084957
theorem B4827215 : Blo 1784093 4827215 := bstep (se 1 (by rfl) ⟨3620411, by rfl⟩ : syracuseStep 4827215 = 7240823) B7240823
theorem B6023321 : Blo 1784093 6023321 := bstep (se 2 (by rfl) ⟨2258745, by rfl⟩ : syracuseStep 6023321 = 4517491) B4517491
theorem B4016375 : Blo 1784093 4016375 := bstep (se 1 (by rfl) ⟨3012281, by rfl⟩ : syracuseStep 4016375 = 6024563) B6024563
theorem B7620875 : Blo 1784093 7620875 := bstep (se 1 (by rfl) ⟨5715656, by rfl⟩ : syracuseStep 7620875 = 11431313) B11431313
theorem B9038141 : Blo 1784093 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B5081449 : Blo 1784093 5081449 := bstep (se 2 (by rfl) ⟨1905543, by rfl⟩ : syracuseStep 5081449 = 3811087) B3811087
theorem B11438489 : Blo 1784093 11438489 := bstep (se 2 (by rfl) ⟨4289433, by rfl⟩ : syracuseStep 11438489 = 8578867) B8578867
theorem B13552109 : Blo 1784093 13552109 := bstep (se 3 (by rfl) ⟨2541020, by rfl⟩ : syracuseStep 13552109 = 5082041) B5082041
theorem B5081609 : Blo 1784093 5081609 := bstep (se 2 (by rfl) ⟨1905603, by rfl⟩ : syracuseStep 5081609 = 3811207) B3811207
theorem B14477849 : Blo 1784093 14477849 := bstep (se 2 (by rfl) ⟨5429193, by rfl⟩ : syracuseStep 14477849 = 10858387) B10858387
theorem B6777377 : Blo 1784093 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B5081723 : Blo 1784093 5081723 := bstep (se 1 (by rfl) ⟨3811292, by rfl⟩ : syracuseStep 5081723 = 7622585) B7622585
theorem B9652871 : Blo 1784093 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B4827863 : Blo 1784093 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B5081849 : Blo 1784093 5081849 := bstep (se 2 (by rfl) ⟨1905693, by rfl⟩ : syracuseStep 5081849 = 3811387) B3811387
theorem B4516681 : Blo 1784093 4516681 := bstep (se 2 (by rfl) ⟨1693755, by rfl⟩ : syracuseStep 4516681 = 3387511) B3387511
theorem B4016969 : Blo 1784093 4016969 := bstep (se 2 (by rfl) ⟨1506363, by rfl⟩ : syracuseStep 4016969 = 3012727) B3012727
theorem B6777695 : Blo 1784093 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B7621559 : Blo 1784093 7621559 := bstep (se 1 (by rfl) ⟨5716169, by rfl⟩ : syracuseStep 7621559 = 11432339) B11432339
theorem B2542519 : Blo 1784093 2542519 := bstep (se 1 (by rfl) ⟨1906889, by rfl⟩ : syracuseStep 2542519 = 3813779) B3813779
theorem B8580097 : Blo 1784093 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B6777863 : Blo 1784093 6777863 := bstep (se 1 (by rfl) ⟨5083397, by rfl⟩ : syracuseStep 6777863 = 10166795) B10166795
theorem B14470163 : Blo 1784093 14470163 := bstep (se 1 (by rfl) ⟨10852622, by rfl⟩ : syracuseStep 14470163 = 21705245) B21705245
theorem B6433949 : Blo 1784093 6433949 := bstep (se 3 (by rfl) ⟨1206365, by rfl⟩ : syracuseStep 6433949 = 2412731) B2412731
theorem B6024509 : Blo 1784093 6024509 := bstep (se 3 (by rfl) ⟨1129595, by rfl⟩ : syracuseStep 6024509 = 2259191) B2259191
theorem B5082497 : Blo 1784093 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B6778349 : Blo 1784093 6778349 := bstep (se 3 (by rfl) ⟨1270940, by rfl⟩ : syracuseStep 6778349 = 2541881) B2541881
theorem B27487811 : Blo 1784093 27487811 := bstep (se 1 (by rfl) ⟨20615858, by rfl⟩ : syracuseStep 27487811 = 41231717) B41231717
theorem B4017761 : Blo 1784093 4017761 := bstep (se 2 (by rfl) ⟨1506660, by rfl⟩ : syracuseStep 4017761 = 3013321) B3013321
theorem B6778667 : Blo 1784093 6778667 := bstep (se 1 (by rfl) ⟨5084000, by rfl⟩ : syracuseStep 6778667 = 10168001) B10168001
theorem B4517815 : Blo 1784093 4517815 := bstep (se 1 (by rfl) ⟨3388361, by rfl⟩ : syracuseStep 4517815 = 6776723) B6776723
theorem B4018103 : Blo 1784093 4018103 := bstep (se 1 (by rfl) ⟨3013577, by rfl⟩ : syracuseStep 4018103 = 6027155) B6027155
theorem B5083067 : Blo 1784093 5083067 := bstep (se 1 (by rfl) ⟨3812300, by rfl⟩ : syracuseStep 5083067 = 7624601) B7624601
theorem B6434873 : Blo 1784093 6434873 := bstep (se 2 (by rfl) ⟨2413077, by rfl⟩ : syracuseStep 6434873 = 4826155) B4826155
theorem B6025373 : Blo 1784093 6025373 := bstep (se 3 (by rfl) ⟨1129757, by rfl⟩ : syracuseStep 6025373 = 2259515) B2259515
theorem B5083307 : Blo 1784093 5083307 := bstep (se 1 (by rfl) ⟨3812480, by rfl⟩ : syracuseStep 5083307 = 7624961) B7624961
theorem B9777469 : Blo 1784093 9777469 := bstep (se 3 (by rfl) ⟨1833275, by rfl⟩ : syracuseStep 9777469 = 3666551) B3666551
theorem B8581481 : Blo 1784093 8581481 := bstep (se 2 (by rfl) ⟨3218055, by rfl⟩ : syracuseStep 8581481 = 6436111) B6436111
theorem B13554053 : Blo 1784093 13554053 := bstep (se 4 (by rfl) ⟨1270692, by rfl⟩ : syracuseStep 13554053 = 2541385) B2541385
theorem B3010999 : Blo 1784093 3010999 := bstep (se 1 (by rfl) ⟨2258249, by rfl⟩ : syracuseStep 3010999 = 4516499) B4516499
theorem B13562315 : Blo 1784093 13562315 := bstep (se 1 (by rfl) ⟨10171736, by rfl⟩ : syracuseStep 13562315 = 20343473) B20343473
theorem B4018697 : Blo 1784093 4018697 := bstep (se 2 (by rfl) ⟨1507011, by rfl⟩ : syracuseStep 4018697 = 3014023) B3014023
theorem B9040409 : Blo 1784093 9040409 := bstep (se 2 (by rfl) ⟨3390153, by rfl⟩ : syracuseStep 9040409 = 6780307) B6780307
theorem B18330137 : Blo 1784093 18330137 := bstep (se 2 (by rfl) ⟨6873801, by rfl⟩ : syracuseStep 18330137 = 13747603) B13747603
theorem B50205251 : Blo 1784093 50205251 := bstep (se 1 (by rfl) ⟨37653938, by rfl⟩ : syracuseStep 50205251 = 75307877) B75307877
theorem B3011195 : Blo 1784093 3011195 := bstep (se 1 (by rfl) ⟨2258396, by rfl⟩ : syracuseStep 3011195 = 4516793) B4516793
theorem B6025913 : Blo 1784093 6025913 := bstep (se 2 (by rfl) ⟨2259717, by rfl⟩ : syracuseStep 6025913 = 4519435) B4519435
theorem B20886227 : Blo 1784093 20886227 := bstep (se 1 (by rfl) ⟨15664670, by rfl⟩ : syracuseStep 20886227 = 31329341) B31329341
theorem B51483347 : Blo 1784093 51483347 := bstep (se 1 (by rfl) ⟨38612510, by rfl⟩ : syracuseStep 51483347 = 77225021) B77225021
theorem B234869539 : Blo 1784093 234869539 := bstep (se 1 (by rfl) ⟨176152154, by rfl⟩ : syracuseStep 234869539 = 352304309) B352304309
theorem B13554539 : Blo 1784093 13554539 := bstep (se 1 (by rfl) ⟨10165904, by rfl⟩ : syracuseStep 13554539 = 20331809) B20331809
theorem B8139703 : Blo 1784093 8139703 := bstep (se 1 (by rfl) ⟨6104777, by rfl⟩ : syracuseStep 8139703 = 12209555) B12209555
theorem B3011593 : Blo 1784093 3011593 := bstep (se 2 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 3011593 = 2258695) B2258695
theorem B32560193 : Blo 1784093 32560193 := bstep (se 2 (by rfl) ⟨12210072, by rfl⟩ : syracuseStep 32560193 = 24420145) B24420145
theorem B10163353 : Blo 1784093 10163353 := bstep (se 2 (by rfl) ⟨3811257, by rfl⟩ : syracuseStep 10163353 = 7622515) B7622515
theorem B14480537 : Blo 1784093 14480537 := bstep (se 2 (by rfl) ⟨5430201, by rfl⟩ : syracuseStep 14480537 = 10860403) B10860403
theorem B3011755 : Blo 1784093 3011755 := bstep (se 1 (by rfl) ⟨2258816, by rfl⟩ : syracuseStep 3011755 = 4517633) B4517633
theorem B22877387 : Blo 1784093 22877387 := bstep (se 1 (by rfl) ⟨17158040, by rfl⟩ : syracuseStep 22877387 = 34316081) B34316081
theorem B6026507 : Blo 1784093 6026507 := bstep (se 1 (by rfl) ⟨4519880, by rfl⟩ : syracuseStep 6026507 = 9039761) B9039761
theorem B4519273 : Blo 1784093 4519273 := bstep (se 2 (by rfl) ⟨1694727, by rfl⟩ : syracuseStep 4519273 = 3389455) B3389455
theorem B12547493 : Blo 1784093 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B2676143 : Blo 1784093 2676143 := bstep (se 1 (by rfl) ⟨2007107, by rfl⟩ : syracuseStep 2676143 = 4014215) B4014215
theorem B3012059 : Blo 1784093 3012059 := bstep (se 1 (by rfl) ⟨2259044, by rfl⟩ : syracuseStep 3012059 = 4518089) B4518089
theorem B2676233 : Blo 1784093 2676233 := bstep (se 2 (by rfl) ⟨1003587, by rfl⟩ : syracuseStep 2676233 = 2007175) B2007175
theorem B6026777 : Blo 1784093 6026777 := bstep (se 2 (by rfl) ⟨2260041, by rfl⟩ : syracuseStep 6026777 = 4520083) B4520083
theorem B2676263 : Blo 1784093 2676263 := bstep (se 1 (by rfl) ⟨2007197, by rfl⟩ : syracuseStep 2676263 = 4014395) B4014395
theorem B3618361 : Blo 1784093 3618361 := bstep (se 2 (by rfl) ⟨1356885, by rfl⟩ : syracuseStep 3618361 = 2713771) B2713771
theorem B23549537 : Blo 1784093 23549537 := bstep (se 2 (by rfl) ⟨8831076, by rfl⟩ : syracuseStep 23549537 = 17662153) B17662153
theorem B2676347 : Blo 1784093 2676347 := bstep (se 1 (by rfl) ⟨2007260, by rfl⟩ : syracuseStep 2676347 = 4014521) B4014521
theorem B4519547 : Blo 1784093 4519547 := bstep (se 1 (by rfl) ⟨3389660, by rfl⟩ : syracuseStep 4519547 = 6779321) B6779321
theorem B9164411 : Blo 1784093 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B3012295 : Blo 1784093 3012295 := bstep (se 1 (by rfl) ⟨2259221, by rfl⟩ : syracuseStep 3012295 = 4518443) B4518443
theorem B2676473 : Blo 1784093 2676473 := bstep (se 2 (by rfl) ⟨1003677, by rfl⟩ : syracuseStep 2676473 = 2007355) B2007355
theorem B6436675 : Blo 1784093 6436675 := bstep (se 1 (by rfl) ⟨4827506, by rfl⟩ : syracuseStep 6436675 = 9655013) B9655013
theorem B5715785 : Blo 1784093 5715785 := bstep (se 2 (by rfl) ⟨2143419, by rfl⟩ : syracuseStep 5715785 = 4286839) B4286839
theorem B2676575 : Blo 1784093 2676575 := bstep (se 1 (by rfl) ⟨2007431, by rfl⟩ : syracuseStep 2676575 = 4014863) B4014863
theorem B3012457 : Blo 1784093 3012457 := bstep (se 2 (by rfl) ⟨1129671, by rfl⟩ : syracuseStep 3012457 = 2259343) B2259343
theorem B2676587 : Blo 1784093 2676587 := bstep (se 1 (by rfl) ⟨2007440, by rfl⟩ : syracuseStep 2676587 = 4014881) B4014881
theorem B6780779 : Blo 1784093 6780779 := bstep (se 1 (by rfl) ⟨5085584, by rfl⟩ : syracuseStep 6780779 = 10171169) B10171169
theorem B10860551 : Blo 1784093 10860551 := bstep (se 1 (by rfl) ⟨8145413, by rfl⟩ : syracuseStep 10860551 = 16290827) B16290827
theorem B2676815 : Blo 1784093 2676815 := bstep (se 1 (by rfl) ⟨2007611, by rfl⟩ : syracuseStep 2676815 = 4015223) B4015223
theorem B2676935 : Blo 1784093 2676935 := bstep (se 1 (by rfl) ⟨2007701, by rfl⟩ : syracuseStep 2676935 = 4015403) B4015403
theorem B1784103 : Blo 1784093 1784103 := bstep (se 1 (by rfl) ⟨1338077, by rfl⟩ : syracuseStep 1784103 = 2676155) B2676155
theorem B1784143 : Blo 1784093 1784143 := bstep (se 1 (by rfl) ⟨1338107, by rfl⟩ : syracuseStep 1784143 = 2676215) B2676215
theorem B1784159 : Blo 1784093 1784159 := bstep (se 1 (by rfl) ⟨1338119, by rfl⟩ : syracuseStep 1784159 = 2676239) B2676239
theorem B2677097 : Blo 1784093 2677097 := bstep (se 2 (by rfl) ⟨1003911, by rfl⟩ : syracuseStep 2677097 = 2007823) B2007823
theorem B1784187 : Blo 1784093 1784187 := bstep (se 1 (by rfl) ⟨1338140, by rfl⟩ : syracuseStep 1784187 = 2676281) B2676281
theorem B29350277 : Blo 1784093 29350277 := bstep (se 4 (by rfl) ⟨2751588, by rfl⟩ : syracuseStep 29350277 = 5503177) B5503177
theorem B1784239 : Blo 1784093 1784239 := bstep (se 1 (by rfl) ⟨1338179, by rfl⟩ : syracuseStep 1784239 = 2676359) B2676359
theorem B2677175 : Blo 1784093 2677175 := bstep (se 1 (by rfl) ⟨2007881, by rfl⟩ : syracuseStep 2677175 = 4015763) B4015763
theorem B3013051 : Blo 1784093 3013051 := bstep (se 1 (by rfl) ⟨2259788, by rfl⟩ : syracuseStep 3013051 = 4519577) B4519577
theorem B1784263 : Blo 1784093 1784263 := bstep (se 1 (by rfl) ⟨1338197, by rfl⟩ : syracuseStep 1784263 = 2676395) B2676395
theorem B1784283 : Blo 1784093 1784283 := bstep (se 1 (by rfl) ⟨1338212, by rfl⟩ : syracuseStep 1784283 = 2676425) B2676425
theorem B2677211 : Blo 1784093 2677211 := bstep (se 1 (by rfl) ⟨2007908, by rfl⟩ : syracuseStep 2677211 = 4015817) B4015817
theorem B7625249 : Blo 1784093 7625249 := bstep (se 2 (by rfl) ⟨2859468, by rfl⟩ : syracuseStep 7625249 = 5718937) B5718937
theorem B1784359 : Blo 1784093 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B3013159 : Blo 1784093 3013159 := bstep (se 1 (by rfl) ⟨2259869, by rfl⟩ : syracuseStep 3013159 = 4519739) B4519739
theorem B1784399 : Blo 1784093 1784399 := bstep (se 1 (by rfl) ⟨1338299, by rfl⟩ : syracuseStep 1784399 = 2676599) B2676599
theorem B1784415 : Blo 1784093 1784415 := bstep (se 1 (by rfl) ⟨1338311, by rfl⟩ : syracuseStep 1784415 = 2676623) B2676623
theorem B1784443 : Blo 1784093 1784443 := bstep (se 1 (by rfl) ⟨1338332, by rfl⟩ : syracuseStep 1784443 = 2676665) B2676665
theorem B6027911 : Blo 1784093 6027911 := bstep (se 1 (by rfl) ⟨4520933, by rfl⟩ : syracuseStep 6027911 = 9041867) B9041867
theorem B1784495 : Blo 1784093 1784495 := bstep (se 1 (by rfl) ⟨1338371, by rfl⟩ : syracuseStep 1784495 = 2676743) B2676743
theorem B6027965 : Blo 1784093 6027965 := bstep (se 3 (by rfl) ⟨1130243, by rfl⟩ : syracuseStep 6027965 = 2260487) B2260487
theorem B1784519 : Blo 1784093 1784519 := bstep (se 1 (by rfl) ⟨1338389, by rfl⟩ : syracuseStep 1784519 = 2676779) B2676779
theorem B4291271 : Blo 1784093 4291271 := bstep (se 1 (by rfl) ⟨3218453, by rfl⟩ : syracuseStep 4291271 = 6436907) B6436907
theorem B9779921 : Blo 1784093 9779921 := bstep (se 2 (by rfl) ⟨3667470, by rfl⟩ : syracuseStep 9779921 = 7334941) B7334941
theorem B5429971 : Blo 1784093 5429971 := bstep (se 1 (by rfl) ⟨4072478, by rfl⟩ : syracuseStep 5429971 = 8144957) B8144957
theorem B1784539 : Blo 1784093 1784539 := bstep (se 1 (by rfl) ⟨1338404, by rfl⟩ : syracuseStep 1784539 = 2676809) B2676809
theorem B20323061 : Blo 1784093 20323061 := bstep (se 5 (by rfl) ⟨952643, by rfl⟩ : syracuseStep 20323061 = 1905287) B1905287
theorem B13556483 : Blo 1784093 13556483 := bstep (se 1 (by rfl) ⟨10167362, by rfl⟩ : syracuseStep 13556483 = 20334725) B20334725
theorem B1784615 : Blo 1784093 1784615 := bstep (se 1 (by rfl) ⟨1338461, by rfl⟩ : syracuseStep 1784615 = 2676923) B2676923
theorem B1784655 : Blo 1784093 1784655 := bstep (se 1 (by rfl) ⟨1338491, by rfl⟩ : syracuseStep 1784655 = 2676983) B2676983
theorem B1784671 : Blo 1784093 1784671 := bstep (se 1 (by rfl) ⟨1338503, by rfl⟩ : syracuseStep 1784671 = 2677007) B2677007
theorem B3013483 : Blo 1784093 3013483 := bstep (se 1 (by rfl) ⟨2260112, by rfl⟩ : syracuseStep 3013483 = 4520225) B4520225
theorem B1784699 : Blo 1784093 1784699 := bstep (se 1 (by rfl) ⟨1338524, by rfl⟩ : syracuseStep 1784699 = 2677049) B2677049
theorem B1784751 : Blo 1784093 1784751 := bstep (se 1 (by rfl) ⟨1338563, by rfl⟩ : syracuseStep 1784751 = 2677127) B2677127
theorem B2677679 : Blo 1784093 2677679 := bstep (se 1 (by rfl) ⟨2008259, by rfl⟩ : syracuseStep 2677679 = 4016519) B4016519
theorem B2259895 : Blo 1784093 2259895 := bstep (se 1 (by rfl) ⟨1694921, by rfl⟩ : syracuseStep 2259895 = 3389843) B3389843
theorem B3218359 : Blo 1784093 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B1784775 : Blo 1784093 1784775 := bstep (se 1 (by rfl) ⟨1338581, by rfl⟩ : syracuseStep 1784775 = 2677163) B2677163
theorem B1784795 : Blo 1784093 1784795 := bstep (se 1 (by rfl) ⟨1338596, by rfl⟩ : syracuseStep 1784795 = 2677193) B2677193
theorem B3390427 : Blo 1784093 3390427 := bstep (se 1 (by rfl) ⟨2542820, by rfl⟩ : syracuseStep 3390427 = 5085641) B5085641
theorem B10304513 : Blo 1784093 10304513 := bstep (se 2 (by rfl) ⟨3864192, by rfl⟩ : syracuseStep 10304513 = 7728385) B7728385
theorem B2677769 : Blo 1784093 2677769 := bstep (se 2 (by rfl) ⟨1004163, by rfl⟩ : syracuseStep 2677769 = 2008327) B2008327
theorem B3390473 : Blo 1784093 3390473 := bstep (se 2 (by rfl) ⟨1271427, by rfl⟩ : syracuseStep 3390473 = 2542855) B2542855
theorem B1784871 : Blo 1784093 1784871 := bstep (se 1 (by rfl) ⟨1338653, by rfl⟩ : syracuseStep 1784871 = 2677307) B2677307
theorem B2677799 : Blo 1784093 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B2899001 : Blo 1784093 2899001 := bstep (se 2 (by rfl) ⟨1087125, by rfl⟩ : syracuseStep 2899001 = 2174251) B2174251
theorem B1784911 : Blo 1784093 1784911 := bstep (se 1 (by rfl) ⟨1338683, by rfl⟩ : syracuseStep 1784911 = 2677367) B2677367
theorem B1784927 : Blo 1784093 1784927 := bstep (se 1 (by rfl) ⟨1338695, by rfl⟩ : syracuseStep 1784927 = 2677391) B2677391
theorem B1784955 : Blo 1784093 1784955 := bstep (se 1 (by rfl) ⟨1338716, by rfl⟩ : syracuseStep 1784955 = 2677433) B2677433
theorem B2677883 : Blo 1784093 2677883 := bstep (se 1 (by rfl) ⟨2008412, by rfl⟩ : syracuseStep 2677883 = 4016825) B4016825
theorem B10861721 : Blo 1784093 10861721 := bstep (se 2 (by rfl) ⟨4073145, by rfl⟩ : syracuseStep 10861721 = 8146291) B8146291
theorem B1785007 : Blo 1784093 1785007 := bstep (se 1 (by rfl) ⟨1338755, by rfl⟩ : syracuseStep 1785007 = 2677511) B2677511
theorem B15244483 : Blo 1784093 15244483 := bstep (se 1 (by rfl) ⟨11433362, by rfl⟩ : syracuseStep 15244483 = 22866725) B22866725
theorem B1785031 : Blo 1784093 1785031 := bstep (se 1 (by rfl) ⟨1338773, by rfl⟩ : syracuseStep 1785031 = 2677547) B2677547
theorem B1785051 : Blo 1784093 1785051 := bstep (se 1 (by rfl) ⟨1338788, by rfl⟩ : syracuseStep 1785051 = 2677577) B2677577
theorem B2678009 : Blo 1784093 2678009 := bstep (se 2 (by rfl) ⟨1004253, by rfl⟩ : syracuseStep 2678009 = 2008507) B2008507
theorem B27843853 : Blo 1784093 27843853 := bstep (se 3 (by rfl) ⟨5220722, by rfl⟩ : syracuseStep 27843853 = 10441445) B10441445
theorem B1785127 : Blo 1784093 1785127 := bstep (se 1 (by rfl) ⟨1338845, by rfl⟩ : syracuseStep 1785127 = 2677691) B2677691
theorem B1785167 : Blo 1784093 1785167 := bstep (se 1 (by rfl) ⟨1338875, by rfl⟩ : syracuseStep 1785167 = 2677751) B2677751
theorem B1785183 : Blo 1784093 1785183 := bstep (se 1 (by rfl) ⟨1338887, by rfl⟩ : syracuseStep 1785183 = 2677775) B2677775
theorem B2678111 : Blo 1784093 2678111 := bstep (se 1 (by rfl) ⟨2008583, by rfl⟩ : syracuseStep 2678111 = 4017167) B4017167
theorem B2678123 : Blo 1784093 2678123 := bstep (se 1 (by rfl) ⟨2008592, by rfl⟩ : syracuseStep 2678123 = 4017185) B4017185
theorem B1785211 : Blo 1784093 1785211 := bstep (se 1 (by rfl) ⟨1338908, by rfl⟩ : syracuseStep 1785211 = 2677817) B2677817
theorem B1785263 : Blo 1784093 1785263 := bstep (se 1 (by rfl) ⟨1338947, by rfl⟩ : syracuseStep 1785263 = 2677895) B2677895
theorem B1785287 : Blo 1784093 1785287 := bstep (se 1 (by rfl) ⟨1338965, by rfl⟩ : syracuseStep 1785287 = 2677931) B2677931
theorem B1785307 : Blo 1784093 1785307 := bstep (se 1 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 1785307 = 2677961) B2677961
theorem B1785383 : Blo 1784093 1785383 := bstep (se 1 (by rfl) ⟨1339037, by rfl⟩ : syracuseStep 1785383 = 2678075) B2678075
theorem B25746983 : Blo 1784093 25746983 := bstep (se 1 (by rfl) ⟨19310237, by rfl⟩ : syracuseStep 25746983 = 38620475) B38620475
theorem B1785423 : Blo 1784093 1785423 := bstep (se 1 (by rfl) ⟨1339067, by rfl⟩ : syracuseStep 1785423 = 2678135) B2678135
theorem B2678351 : Blo 1784093 2678351 := bstep (se 1 (by rfl) ⟨2008763, by rfl⟩ : syracuseStep 2678351 = 4017527) B4017527
theorem B1785439 : Blo 1784093 1785439 := bstep (se 1 (by rfl) ⟨1339079, by rfl⟩ : syracuseStep 1785439 = 2678159) B2678159
theorem B9035387 : Blo 1784093 9035387 := bstep (se 1 (by rfl) ⟨6776540, by rfl⟩ : syracuseStep 9035387 = 13553081) B13553081
theorem B1785467 : Blo 1784093 1785467 := bstep (se 1 (by rfl) ⟨1339100, by rfl⟩ : syracuseStep 1785467 = 2678201) B2678201
theorem B1785519 : Blo 1784093 1785519 := bstep (se 1 (by rfl) ⟨1339139, by rfl⟩ : syracuseStep 1785519 = 2678279) B2678279
theorem B6774461 : Blo 1784093 6774461 := bstep (se 3 (by rfl) ⟨1270211, by rfl⟩ : syracuseStep 6774461 = 2540423) B2540423
theorem B1785543 : Blo 1784093 1785543 := bstep (se 1 (by rfl) ⟨1339157, by rfl⟩ : syracuseStep 1785543 = 2678315) B2678315
theorem B2678471 : Blo 1784093 2678471 := bstep (se 1 (by rfl) ⟨2008853, by rfl⟩ : syracuseStep 2678471 = 4017707) B4017707
theorem B1785563 : Blo 1784093 1785563 := bstep (se 1 (by rfl) ⟨1339172, by rfl⟩ : syracuseStep 1785563 = 2678345) B2678345
theorem B1785639 : Blo 1784093 1785639 := bstep (se 1 (by rfl) ⟨1339229, by rfl⟩ : syracuseStep 1785639 = 2678459) B2678459
theorem B3669833 : Blo 1784093 3669833 := bstep (se 2 (by rfl) ⟨1376187, by rfl⟩ : syracuseStep 3669833 = 2752375) B2752375
theorem B1785679 : Blo 1784093 1785679 := bstep (se 1 (by rfl) ⟨1339259, by rfl⟩ : syracuseStep 1785679 = 2678519) B2678519
theorem B1785695 : Blo 1784093 1785695 := bstep (se 1 (by rfl) ⟨1339271, by rfl⟩ : syracuseStep 1785695 = 2678543) B2678543
theorem B7241567 : Blo 1784093 7241567 := bstep (se 1 (by rfl) ⟨5431175, by rfl⟩ : syracuseStep 7241567 = 10862351) B10862351
theorem B2678633 : Blo 1784093 2678633 := bstep (se 2 (by rfl) ⟨1004487, by rfl⟩ : syracuseStep 2678633 = 2008975) B2008975
theorem B1785723 : Blo 1784093 1785723 := bstep (se 1 (by rfl) ⟨1339292, by rfl⟩ : syracuseStep 1785723 = 2678585) B2678585
theorem B1785775 : Blo 1784093 1785775 := bstep (se 1 (by rfl) ⟨1339331, by rfl⟩ : syracuseStep 1785775 = 2678663) B2678663
theorem B2678711 : Blo 1784093 2678711 := bstep (se 1 (by rfl) ⟨2009033, by rfl⟩ : syracuseStep 2678711 = 4018067) B4018067
theorem B1785799 : Blo 1784093 1785799 := bstep (se 1 (by rfl) ⟨1339349, by rfl⟩ : syracuseStep 1785799 = 2678699) B2678699
theorem B1785819 : Blo 1784093 1785819 := bstep (se 1 (by rfl) ⟨1339364, by rfl⟩ : syracuseStep 1785819 = 2678729) B2678729
theorem B2678747 : Blo 1784093 2678747 := bstep (se 1 (by rfl) ⟨2009060, by rfl⟩ : syracuseStep 2678747 = 4018121) B4018121
theorem B9036035 : Blo 1784093 9036035 := bstep (se 1 (by rfl) ⟨6777026, by rfl⟩ : syracuseStep 9036035 = 13554053) B13554053
theorem B2679131 : Blo 1784093 2679131 := bstep (se 1 (by rfl) ⟨2009348, by rfl⟩ : syracuseStep 2679131 = 4018697) B4018697
theorem B4014503 : Blo 1784093 4014503 := bstep (se 1 (by rfl) ⟨3010877, by rfl⟩ : syracuseStep 4014503 = 6021755) B6021755
theorem B2007463 : Blo 1784093 2007463 := bstep (se 1 (by rfl) ⟨1505597, by rfl⟩ : syracuseStep 2007463 = 3011195) B3011195
theorem B6775265 : Blo 1784093 6775265 := bstep (se 2 (by rfl) ⟨2540724, by rfl⟩ : syracuseStep 6775265 = 5081449) B5081449
theorem B4014611 : Blo 1784093 4014611 := bstep (se 1 (by rfl) ⟨3010958, by rfl⟩ : syracuseStep 4014611 = 6021917) B6021917
theorem B9036359 : Blo 1784093 9036359 := bstep (se 1 (by rfl) ⟨6777269, by rfl⟩ : syracuseStep 9036359 = 13554539) B13554539
theorem B4014665 : Blo 1784093 4014665 := bstep (se 2 (by rfl) ⟨1505499, by rfl⟩ : syracuseStep 4014665 = 3010999) B3010999
theorem B6521527 : Blo 1784093 6521527 := bstep (se 1 (by rfl) ⟨4891145, by rfl⟩ : syracuseStep 6521527 = 9782291) B9782291
theorem B22921931 : Blo 1784093 22921931 := bstep (se 1 (by rfl) ⟨17191448, by rfl⟩ : syracuseStep 22921931 = 34382897) B34382897
theorem B285852523 : Blo 1784093 285852523 := bstep (se 1 (by rfl) ⟨214389392, by rfl⟩ : syracuseStep 285852523 = 428778785) B428778785
theorem B8364995 : Blo 1784093 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B4015079 : Blo 1784093 4015079 := bstep (se 1 (by rfl) ⟨3011309, by rfl⟩ : syracuseStep 4015079 = 6022619) B6022619
theorem B2008039 : Blo 1784093 2008039 := bstep (se 1 (by rfl) ⟨1506029, by rfl⟩ : syracuseStep 2008039 = 3012059) B3012059
theorem B6022241 : Blo 1784093 6022241 := bstep (se 2 (by rfl) ⟨2258340, by rfl⟩ : syracuseStep 6022241 = 4516681) B4516681
theorem B6775933 : Blo 1784093 6775933 := bstep (se 3 (by rfl) ⟨1270487, by rfl⟩ : syracuseStep 6775933 = 2540975) B2540975
theorem B4015457 : Blo 1784093 4015457 := bstep (se 2 (by rfl) ⟨1505796, by rfl⟩ : syracuseStep 4015457 = 3011593) B3011593
theorem B4015547 : Blo 1784093 4015547 := bstep (se 1 (by rfl) ⟨3011660, by rfl⟩ : syracuseStep 4015547 = 6023321) B6023321
theorem B5080583 : Blo 1784093 5080583 := bstep (se 1 (by rfl) ⟨3810437, by rfl⟩ : syracuseStep 5080583 = 7620875) B7620875
theorem B13551137 : Blo 1784093 13551137 := bstep (se 2 (by rfl) ⟨5081676, by rfl⟩ : syracuseStep 13551137 = 10163353) B10163353
theorem B4015673 : Blo 1784093 4015673 := bstep (se 2 (by rfl) ⟨1505877, by rfl⟩ : syracuseStep 4015673 = 3011755) B3011755
theorem B20325977 : Blo 1784093 20325977 := bstep (se 2 (by rfl) ⟨7622241, by rfl⟩ : syracuseStep 20325977 = 15244483) B15244483
theorem B9651899 : Blo 1784093 9651899 := bstep (se 1 (by rfl) ⟨7238924, by rfl⟩ : syracuseStep 9651899 = 14477849) B14477849
theorem B25740989 : Blo 1784093 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B2860847 : Blo 1784093 2860847 := bstep (se 1 (by rfl) ⟨2145635, by rfl⟩ : syracuseStep 2860847 = 4291271) B4291271
theorem B9037655 : Blo 1784093 9037655 := bstep (se 1 (by rfl) ⟨6778241, by rfl⟩ : syracuseStep 9037655 = 13556483) B13556483
theorem B5081039 : Blo 1784093 5081039 := bstep (se 1 (by rfl) ⟨3810779, by rfl⟩ : syracuseStep 5081039 = 7621559) B7621559
theorem B4016339 : Blo 1784093 4016339 := bstep (se 1 (by rfl) ⟨3012254, by rfl⟩ : syracuseStep 4016339 = 6024509) B6024509
theorem B19310845 : Blo 1784093 19310845 := bstep (se 3 (by rfl) ⟨3620783, by rfl⟩ : syracuseStep 19310845 = 7241567) B7241567
theorem B4016393 : Blo 1784093 4016393 := bstep (se 2 (by rfl) ⟨1506147, by rfl⟩ : syracuseStep 4016393 = 3012295) B3012295
theorem B17164655 : Blo 1784093 17164655 := bstep (se 1 (by rfl) ⟨12873491, by rfl⟩ : syracuseStep 17164655 = 25746983) B25746983
theorem B6023591 : Blo 1784093 6023591 := bstep (se 1 (by rfl) ⟨4517693, by rfl⟩ : syracuseStep 6023591 = 9035387) B9035387
theorem B4516307 : Blo 1784093 4516307 := bstep (se 1 (by rfl) ⟨3387230, by rfl⟩ : syracuseStep 4516307 = 6774461) B6774461
theorem B4016609 : Blo 1784093 4016609 := bstep (se 2 (by rfl) ⟨1506228, by rfl⟩ : syracuseStep 4016609 = 3012457) B3012457
theorem B6023753 : Blo 1784093 6023753 := bstep (se 2 (by rfl) ⟨2258907, by rfl⟩ : syracuseStep 6023753 = 4517815) B4517815
theorem B4016915 : Blo 1784093 4016915 := bstep (se 1 (by rfl) ⟨3012686, by rfl⟩ : syracuseStep 4016915 = 6025373) B6025373
theorem B4520519 : Blo 1784093 4520519 := bstep (se 1 (by rfl) ⟨3390389, by rfl⟩ : syracuseStep 4520519 = 6780779) B6780779
theorem B5720987 : Blo 1784093 5720987 := bstep (se 1 (by rfl) ⟨4290740, by rfl⟩ : syracuseStep 5720987 = 8581481) B8581481
theorem B17157197 : Blo 1784093 17157197 := bstep (se 3 (by rfl) ⟨3216974, by rfl⟩ : syracuseStep 17157197 = 6433949) B6433949
theorem B13036625 : Blo 1784093 13036625 := bstep (se 2 (by rfl) ⟨4888734, by rfl⟩ : syracuseStep 13036625 = 9777469) B9777469
theorem B10169459 : Blo 1784093 10169459 := bstep (se 1 (by rfl) ⟨7627094, by rfl⟩ : syracuseStep 10169459 = 15254189) B15254189
theorem B4017275 : Blo 1784093 4017275 := bstep (se 1 (by rfl) ⟨3012956, by rfl⟩ : syracuseStep 4017275 = 6025913) B6025913
theorem B4017401 : Blo 1784093 4017401 := bstep (se 2 (by rfl) ⟨1506525, by rfl⟩ : syracuseStep 4017401 = 3013051) B3013051
theorem B4017545 : Blo 1784093 4017545 := bstep (se 2 (by rfl) ⟨1506579, by rfl⟩ : syracuseStep 4017545 = 3013159) B3013159
theorem B11431367 : Blo 1784093 11431367 := bstep (se 1 (by rfl) ⟨8573525, by rfl⟩ : syracuseStep 11431367 = 17147051) B17147051
theorem B4017671 : Blo 1784093 4017671 := bstep (se 1 (by rfl) ⟨3013253, by rfl⟩ : syracuseStep 4017671 = 6026507) B6026507
theorem B4517471 : Blo 1784093 4517471 := bstep (se 1 (by rfl) ⟨3388103, by rfl⟩ : syracuseStep 4517471 = 6776207) B6776207
theorem B4017851 : Blo 1784093 4017851 := bstep (se 1 (by rfl) ⟨3013388, by rfl⟩ : syracuseStep 4017851 = 6026777) B6026777
theorem B313159385 : Blo 1784093 313159385 := bstep (se 2 (by rfl) ⟨117434769, by rfl⟩ : syracuseStep 313159385 = 234869539) B234869539
theorem B15699691 : Blo 1784093 15699691 := bstep (se 1 (by rfl) ⟨11774768, by rfl⟩ : syracuseStep 15699691 = 23549537) B23549537
theorem B15249131 : Blo 1784093 15249131 := bstep (se 1 (by rfl) ⟨11436848, by rfl⟩ : syracuseStep 15249131 = 22873697) B22873697
theorem B4017977 : Blo 1784093 4017977 := bstep (se 2 (by rfl) ⟨1506741, by rfl⟩ : syracuseStep 4017977 = 3013483) B3013483
theorem B11440129 : Blo 1784093 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B9039923 : Blo 1784093 9039923 := bstep (se 1 (by rfl) ⟨6779942, by rfl⟩ : syracuseStep 9039923 = 13559885) B13559885
theorem B6025427 : Blo 1784093 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B19566851 : Blo 1784093 19566851 := bstep (se 1 (by rfl) ⟨14675138, by rfl⟩ : syracuseStep 19566851 = 29350277) B29350277
theorem B3387739 : Blo 1784093 3387739 := bstep (se 1 (by rfl) ⟨2540804, by rfl⟩ : syracuseStep 3387739 = 5081609) B5081609
theorem B4518251 : Blo 1784093 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B5083499 : Blo 1784093 5083499 := bstep (se 1 (by rfl) ⟨3812624, by rfl⟩ : syracuseStep 5083499 = 7625249) B7625249
theorem B3387815 : Blo 1784093 3387815 := bstep (se 1 (by rfl) ⟨2540861, by rfl⟩ : syracuseStep 3387815 = 5081723) B5081723
theorem B4018607 : Blo 1784093 4018607 := bstep (se 1 (by rfl) ⟨3013955, by rfl⟩ : syracuseStep 4018607 = 6027911) B6027911
theorem B4018643 : Blo 1784093 4018643 := bstep (se 1 (by rfl) ⟨3013982, by rfl⟩ : syracuseStep 4018643 = 6027965) B6027965
theorem B6025697 : Blo 1784093 6025697 := bstep (se 2 (by rfl) ⟨2259636, by rfl⟩ : syracuseStep 6025697 = 4519273) B4519273
theorem B3387899 : Blo 1784093 3387899 := bstep (se 1 (by rfl) ⟨2540924, by rfl⟩ : syracuseStep 3387899 = 5081849) B5081849
theorem B12874301 : Blo 1784093 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B4518463 : Blo 1784093 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B6869675 : Blo 1784093 6869675 := bstep (se 1 (by rfl) ⟨5152256, by rfl⟩ : syracuseStep 6869675 = 10304513) B10304513
theorem B4518575 : Blo 1784093 4518575 := bstep (se 1 (by rfl) ⟨3388931, by rfl⟩ : syracuseStep 4518575 = 6777863) B6777863
theorem B9646775 : Blo 1784093 9646775 := bstep (se 1 (by rfl) ⟨7235081, by rfl⟩ : syracuseStep 9646775 = 14470163) B14470163
theorem B15242093 : Blo 1784093 15242093 := bstep (se 3 (by rfl) ⟨2857892, by rfl⟩ : syracuseStep 15242093 = 5715785) B5715785
theorem B3388331 : Blo 1784093 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B4518899 : Blo 1784093 4518899 := bstep (se 1 (by rfl) ⟨3389174, by rfl⟩ : syracuseStep 4518899 = 6778349) B6778349
theorem B8582233 : Blo 1784093 8582233 := bstep (se 2 (by rfl) ⟨3218337, by rfl⟩ : syracuseStep 8582233 = 6436675) B6436675
theorem B4519111 : Blo 1784093 4519111 := bstep (se 1 (by rfl) ⟨3389333, by rfl⟩ : syracuseStep 4519111 = 6778667) B6778667
theorem B2446555 : Blo 1784093 2446555 := bstep (se 1 (by rfl) ⟨1834916, by rfl⟩ : syracuseStep 2446555 = 3669833) B3669833
theorem B3388711 : Blo 1784093 3388711 := bstep (se 1 (by rfl) ⟨2541533, by rfl⟩ : syracuseStep 3388711 = 5083067) B5083067
theorem B8574331 : Blo 1784093 8574331 := bstep (se 1 (by rfl) ⟨6430748, by rfl⟩ : syracuseStep 8574331 = 12861497) B12861497
theorem B4289915 : Blo 1784093 4289915 := bstep (se 1 (by rfl) ⟨3217436, by rfl⟩ : syracuseStep 4289915 = 6434873) B6434873
theorem B2676167 : Blo 1784093 2676167 := bstep (se 1 (by rfl) ⟨2007125, by rfl⟩ : syracuseStep 2676167 = 4014251) B4014251
theorem B3388871 : Blo 1784093 3388871 := bstep (se 1 (by rfl) ⟨2541653, by rfl⟩ : syracuseStep 3388871 = 5083307) B5083307
theorem B7730669 : Blo 1784093 7730669 := bstep (se 3 (by rfl) ⟨1449500, by rfl⟩ : syracuseStep 7730669 = 2899001) B2899001
theorem B7624327 : Blo 1784093 7624327 := bstep (se 1 (by rfl) ⟨5718245, by rfl⟩ : syracuseStep 7624327 = 11436491) B11436491
theorem B9041543 : Blo 1784093 9041543 := bstep (se 1 (by rfl) ⟨6781157, by rfl⟩ : syracuseStep 9041543 = 13562315) B13562315
theorem B6026939 : Blo 1784093 6026939 := bstep (se 1 (by rfl) ⟨4520204, by rfl⟩ : syracuseStep 6026939 = 9040409) B9040409
theorem B12220091 : Blo 1784093 12220091 := bstep (se 1 (by rfl) ⟨9165068, by rfl⟩ : syracuseStep 12220091 = 18330137) B18330137
theorem B33470167 : Blo 1784093 33470167 := bstep (se 1 (by rfl) ⟨25102625, by rfl⟩ : syracuseStep 33470167 = 50205251) B50205251
theorem B38614765 : Blo 1784093 38614765 := bstep (se 3 (by rfl) ⟨7240268, by rfl⟩ : syracuseStep 38614765 = 14480537) B14480537
theorem B2676521 : Blo 1784093 2676521 := bstep (se 2 (by rfl) ⟨1003695, by rfl⟩ : syracuseStep 2676521 = 2007391) B2007391
theorem B2676527 : Blo 1784093 2676527 := bstep (se 1 (by rfl) ⟨2007395, by rfl⟩ : syracuseStep 2676527 = 4014791) B4014791
theorem B13924151 : Blo 1784093 13924151 := bstep (se 1 (by rfl) ⟨10443113, by rfl⟩ : syracuseStep 13924151 = 20886227) B20886227
theorem B13555511 : Blo 1784093 13555511 := bstep (se 1 (by rfl) ⟨10166633, by rfl⟩ : syracuseStep 13555511 = 20333267) B20333267
theorem B34322231 : Blo 1784093 34322231 := bstep (se 1 (by rfl) ⟨25741673, by rfl⟩ : syracuseStep 34322231 = 51483347) B51483347
theorem B21706795 : Blo 1784093 21706795 := bstep (se 1 (by rfl) ⟨16280096, by rfl⟩ : syracuseStep 21706795 = 32560193) B32560193
theorem B15251591 : Blo 1784093 15251591 := bstep (se 1 (by rfl) ⟨11438693, by rfl⟩ : syracuseStep 15251591 = 22877387) B22877387
theorem B2677001 : Blo 1784093 2677001 := bstep (se 2 (by rfl) ⟨1003875, by rfl⟩ : syracuseStep 2677001 = 2007751) B2007751
theorem B7239961 : Blo 1784093 7239961 := bstep (se 2 (by rfl) ⟨2714985, by rfl⟩ : syracuseStep 7239961 = 5429971) B5429971
theorem B1784095 : Blo 1784093 1784095 := bstep (se 1 (by rfl) ⟨1338071, by rfl⟩ : syracuseStep 1784095 = 2676143) B2676143
theorem B1784155 : Blo 1784093 1784155 := bstep (se 1 (by rfl) ⟨1338116, by rfl⟩ : syracuseStep 1784155 = 2676233) B2676233
theorem B1784175 : Blo 1784093 1784175 := bstep (se 1 (by rfl) ⟨1338131, by rfl⟩ : syracuseStep 1784175 = 2676263) B2676263
theorem B2677103 : Blo 1784093 2677103 := bstep (se 1 (by rfl) ⟨2007827, by rfl⟩ : syracuseStep 2677103 = 4015655) B4015655
theorem B1784231 : Blo 1784093 1784231 := bstep (se 1 (by rfl) ⟨1338173, by rfl⟩ : syracuseStep 1784231 = 2676347) B2676347
theorem B3013031 : Blo 1784093 3013031 := bstep (se 1 (by rfl) ⟨2259773, by rfl⟩ : syracuseStep 3013031 = 4519547) B4519547
theorem B6109607 : Blo 1784093 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1784315 : Blo 1784093 1784315 := bstep (se 1 (by rfl) ⟨1338236, by rfl⟩ : syracuseStep 1784315 = 2676473) B2676473
theorem B1784383 : Blo 1784093 1784383 := bstep (se 1 (by rfl) ⟨1338287, by rfl⟩ : syracuseStep 1784383 = 2676575) B2676575
theorem B1784391 : Blo 1784093 1784391 := bstep (se 1 (by rfl) ⟨1338293, by rfl⟩ : syracuseStep 1784391 = 2676587) B2676587
theorem B2677319 : Blo 1784093 2677319 := bstep (se 1 (by rfl) ⟨2007989, by rfl⟩ : syracuseStep 2677319 = 4015979) B4015979
theorem B10852937 : Blo 1784093 10852937 := bstep (se 2 (by rfl) ⟨4069851, by rfl⟩ : syracuseStep 10852937 = 8139703) B8139703
theorem B8575561 : Blo 1784093 8575561 := bstep (se 2 (by rfl) ⟨3215835, by rfl⟩ : syracuseStep 8575561 = 6431671) B6431671
theorem B3013193 : Blo 1784093 3013193 := bstep (se 2 (by rfl) ⟨1129947, by rfl⟩ : syracuseStep 3013193 = 2259895) B2259895
theorem B3390025 : Blo 1784093 3390025 := bstep (se 2 (by rfl) ⟨1271259, by rfl⟩ : syracuseStep 3390025 = 2542519) B2542519
theorem B4291145 : Blo 1784093 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B2677355 : Blo 1784093 2677355 := bstep (se 1 (by rfl) ⟨2008016, by rfl⟩ : syracuseStep 2677355 = 4016033) B4016033
theorem B4520569 : Blo 1784093 4520569 := bstep (se 2 (by rfl) ⟨1695213, by rfl⟩ : syracuseStep 4520569 = 3390427) B3390427
theorem B9034415 : Blo 1784093 9034415 := bstep (se 1 (by rfl) ⟨6775811, by rfl⟩ : syracuseStep 9034415 = 13551623) B13551623
theorem B7240367 : Blo 1784093 7240367 := bstep (se 1 (by rfl) ⟨5430275, by rfl⟩ : syracuseStep 7240367 = 10860551) B10860551
theorem B1784543 : Blo 1784093 1784543 := bstep (se 1 (by rfl) ⟨1338407, by rfl⟩ : syracuseStep 1784543 = 2676815) B2676815
theorem B3218143 : Blo 1784093 3218143 := bstep (se 1 (by rfl) ⟨2413607, by rfl⟩ : syracuseStep 3218143 = 4827215) B4827215
theorem B1784623 : Blo 1784093 1784623 := bstep (se 1 (by rfl) ⟨1338467, by rfl⟩ : syracuseStep 1784623 = 2676935) B2676935
theorem B2677583 : Blo 1784093 2677583 := bstep (se 1 (by rfl) ⟨2008187, by rfl⟩ : syracuseStep 2677583 = 4016375) B4016375
theorem B1784731 : Blo 1784093 1784731 := bstep (se 1 (by rfl) ⟨1338548, by rfl⟩ : syracuseStep 1784731 = 2677097) B2677097
theorem B7625659 : Blo 1784093 7625659 := bstep (se 1 (by rfl) ⟨5719244, by rfl⟩ : syracuseStep 7625659 = 11438489) B11438489
theorem B1784783 : Blo 1784093 1784783 := bstep (se 1 (by rfl) ⟨1338587, by rfl⟩ : syracuseStep 1784783 = 2677175) B2677175
theorem B1784807 : Blo 1784093 1784807 := bstep (se 1 (by rfl) ⟨1338605, by rfl⟩ : syracuseStep 1784807 = 2677211) B2677211
theorem B9034739 : Blo 1784093 9034739 := bstep (se 1 (by rfl) ⟨6776054, by rfl⟩ : syracuseStep 9034739 = 13552109) B13552109
theorem B37125137 : Blo 1784093 37125137 := bstep (se 2 (by rfl) ⟨13921926, by rfl⟩ : syracuseStep 37125137 = 27843853) B27843853
theorem B6519947 : Blo 1784093 6519947 := bstep (se 1 (by rfl) ⟨4889960, by rfl⟩ : syracuseStep 6519947 = 9779921) B9779921
theorem B13548707 : Blo 1784093 13548707 := bstep (se 1 (by rfl) ⟨10161530, by rfl⟩ : syracuseStep 13548707 = 20323061) B20323061
theorem B2677979 : Blo 1784093 2677979 := bstep (se 1 (by rfl) ⟨2008484, by rfl⟩ : syracuseStep 2677979 = 4016969) B4016969
theorem B1785119 : Blo 1784093 1785119 := bstep (se 1 (by rfl) ⟨1338839, by rfl⟩ : syracuseStep 1785119 = 2677679) B2677679
theorem B1785179 : Blo 1784093 1785179 := bstep (se 1 (by rfl) ⟨1338884, by rfl⟩ : syracuseStep 1785179 = 2677769) B2677769
theorem B2260315 : Blo 1784093 2260315 := bstep (se 1 (by rfl) ⟨1695236, by rfl⟩ : syracuseStep 2260315 = 3390473) B3390473
theorem B1785199 : Blo 1784093 1785199 := bstep (se 1 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 1785199 = 2677799) B2677799
theorem B2678153 : Blo 1784093 2678153 := bstep (se 2 (by rfl) ⟨1004307, by rfl⟩ : syracuseStep 2678153 = 2008615) B2008615
theorem B4824481 : Blo 1784093 4824481 := bstep (se 2 (by rfl) ⟨1809180, by rfl⟩ : syracuseStep 4824481 = 3618361) B3618361
theorem B1785255 : Blo 1784093 1785255 := bstep (se 1 (by rfl) ⟨1338941, by rfl⟩ : syracuseStep 1785255 = 2677883) B2677883
theorem B7241147 : Blo 1784093 7241147 := bstep (se 1 (by rfl) ⟨5430860, by rfl⟩ : syracuseStep 7241147 = 10861721) B10861721
theorem B1785339 : Blo 1784093 1785339 := bstep (se 1 (by rfl) ⟨1339004, by rfl⟩ : syracuseStep 1785339 = 2678009) B2678009
theorem B1785407 : Blo 1784093 1785407 := bstep (se 1 (by rfl) ⟨1339055, by rfl⟩ : syracuseStep 1785407 = 2678111) B2678111
theorem B1785415 : Blo 1784093 1785415 := bstep (se 1 (by rfl) ⟨1339061, by rfl⟩ : syracuseStep 1785415 = 2678123) B2678123
theorem B18325207 : Blo 1784093 18325207 := bstep (se 1 (by rfl) ⟨13743905, by rfl⟩ : syracuseStep 18325207 = 27487811) B27487811
theorem B1785567 : Blo 1784093 1785567 := bstep (se 1 (by rfl) ⟨1339175, by rfl⟩ : syracuseStep 1785567 = 2678351) B2678351
theorem B2678507 : Blo 1784093 2678507 := bstep (se 1 (by rfl) ⟨2008880, by rfl⟩ : syracuseStep 2678507 = 4017761) B4017761
theorem B1785647 : Blo 1784093 1785647 := bstep (se 1 (by rfl) ⟨1339235, by rfl⟩ : syracuseStep 1785647 = 2678471) B2678471
theorem B1785755 : Blo 1784093 1785755 := bstep (se 1 (by rfl) ⟨1339316, by rfl⟩ : syracuseStep 1785755 = 2678633) B2678633
theorem B1785807 : Blo 1784093 1785807 := bstep (se 1 (by rfl) ⟨1339355, by rfl⟩ : syracuseStep 1785807 = 2678711) B2678711
theorem B2678735 : Blo 1784093 2678735 := bstep (se 1 (by rfl) ⟨2009051, by rfl⟩ : syracuseStep 2678735 = 4018103) B4018103
theorem B1785831 : Blo 1784093 1785831 := bstep (se 1 (by rfl) ⟨1339373, by rfl⟩ : syracuseStep 1785831 = 2678747) B2678747
theorem B15253505 : Blo 1784093 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B99000365 : Blo 1784093 99000365 := bstep (se 3 (by rfl) ⟨18562568, by rfl⟩ : syracuseStep 99000365 = 37125137) B37125137
theorem B28942393 : Blo 1784093 28942393 := bstep (se 2 (by rfl) ⟨10853397, by rfl⟩ : syracuseStep 28942393 = 21706795) B21706795
theorem B1786087 : Blo 1784093 1786087 := bstep (se 1 (by rfl) ⟨1339565, by rfl⟩ : syracuseStep 1786087 = 2679131) B2679131
theorem B2679071 : Blo 1784093 2679071 := bstep (se 1 (by rfl) ⟨2009303, by rfl⟩ : syracuseStep 2679071 = 4018607) B4018607
theorem B2679095 : Blo 1784093 2679095 := bstep (se 1 (by rfl) ⟨2009321, by rfl⟩ : syracuseStep 2679095 = 4018643) B4018643
theorem B25747793 : Blo 1784093 25747793 := bstep (se 2 (by rfl) ⟨9655422, by rfl⟩ : syracuseStep 25747793 = 19310845) B19310845
theorem B4579783 : Blo 1784093 4579783 := bstep (se 1 (by rfl) ⟨3434837, by rfl⟩ : syracuseStep 4579783 = 6869675) B6869675
theorem B6431183 : Blo 1784093 6431183 := bstep (se 1 (by rfl) ⟨4823387, by rfl⟩ : syracuseStep 6431183 = 9646775) B9646775
theorem B4014827 : Blo 1784093 4014827 := bstep (se 1 (by rfl) ⟨3011120, by rfl⟩ : syracuseStep 4014827 = 6022241) B6022241
theorem B2859943 : Blo 1784093 2859943 := bstep (se 1 (by rfl) ⟨2144957, by rfl⟩ : syracuseStep 2859943 = 4289915) B4289915
theorem B5153779 : Blo 1784093 5153779 := bstep (se 1 (by rfl) ⟨3865334, by rfl⟩ : syracuseStep 5153779 = 7730669) B7730669
theorem B13550651 : Blo 1784093 13550651 := bstep (se 1 (by rfl) ⟨10162988, by rfl⟩ : syracuseStep 13550651 = 20325977) B20325977
theorem B9282767 : Blo 1784093 9282767 := bstep (se 1 (by rfl) ⟨6962075, by rfl⟩ : syracuseStep 9282767 = 13924151) B13924151
theorem B9037007 : Blo 1784093 9037007 := bstep (se 1 (by rfl) ⟨6777755, by rfl⟩ : syracuseStep 9037007 = 13555511) B13555511
theorem B22881487 : Blo 1784093 22881487 := bstep (se 1 (by rfl) ⟨17161115, by rfl⟩ : syracuseStep 22881487 = 34322231) B34322231
theorem B10167545 : Blo 1784093 10167545 := bstep (se 2 (by rfl) ⟨3812829, by rfl⟩ : syracuseStep 10167545 = 7625659) B7625659
theorem B10167727 : Blo 1784093 10167727 := bstep (se 1 (by rfl) ⟨7625795, by rfl⟩ : syracuseStep 10167727 = 15251591) B15251591
theorem B4015727 : Blo 1784093 4015727 := bstep (se 1 (by rfl) ⟨3011795, by rfl⟩ : syracuseStep 4015727 = 6023591) B6023591
theorem B2008687 : Blo 1784093 2008687 := bstep (se 1 (by rfl) ⟨1506515, by rfl⟩ : syracuseStep 2008687 = 3013031) B3013031
theorem B3262073 : Blo 1784093 3262073 := bstep (se 2 (by rfl) ⟨1223277, by rfl⟩ : syracuseStep 3262073 = 2446555) B2446555
theorem B7235291 : Blo 1784093 7235291 := bstep (se 1 (by rfl) ⟨5426468, by rfl⟩ : syracuseStep 7235291 = 10852937) B10852937
theorem B4015835 : Blo 1784093 4015835 := bstep (se 1 (by rfl) ⟨3011876, by rfl⟩ : syracuseStep 4015835 = 6023753) B6023753
theorem B2008795 : Blo 1784093 2008795 := bstep (se 1 (by rfl) ⟨1506596, by rfl⟩ : syracuseStep 2008795 = 3013193) B3013193
theorem B2860763 : Blo 1784093 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B6022943 : Blo 1784093 6022943 := bstep (se 1 (by rfl) ⟨4517207, by rfl⟩ : syracuseStep 6022943 = 9034415) B9034415
theorem B4826911 : Blo 1784093 4826911 := bstep (se 1 (by rfl) ⟨3620183, by rfl⟩ : syracuseStep 4826911 = 7240367) B7240367
theorem B6432641 : Blo 1784093 6432641 := bstep (se 2 (by rfl) ⟨2412240, by rfl⟩ : syracuseStep 6432641 = 4824481) B4824481
theorem B6023159 : Blo 1784093 6023159 := bstep (se 1 (by rfl) ⟨4517369, by rfl⟩ : syracuseStep 6023159 = 9034739) B9034739
theorem B11438131 : Blo 1784093 11438131 := bstep (se 1 (by rfl) ⟨8578598, by rfl⟩ : syracuseStep 11438131 = 17157197) B17157197
theorem B4827431 : Blo 1784093 4827431 := bstep (se 1 (by rfl) ⟨3620573, by rfl⟩ : syracuseStep 4827431 = 7241147) B7241147
theorem B7620911 : Blo 1784093 7620911 := bstep (se 1 (by rfl) ⟨5715683, by rfl⟩ : syracuseStep 7620911 = 11431367) B11431367
theorem B20932921 : Blo 1784093 20932921 := bstep (se 2 (by rfl) ⟨7849845, by rfl⟩ : syracuseStep 20932921 = 15699691) B15699691
theorem B15255965 : Blo 1784093 15255965 := bstep (se 3 (by rfl) ⟨2860493, by rfl⟩ : syracuseStep 15255965 = 5720987) B5720987
theorem B4016951 : Blo 1784093 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B6024023 : Blo 1784093 6024023 := bstep (se 1 (by rfl) ⟨4518017, by rfl⟩ : syracuseStep 6024023 = 9036035) B9036035
theorem B4516843 : Blo 1784093 4516843 := bstep (se 1 (by rfl) ⟨3387632, by rfl⟩ : syracuseStep 4516843 = 6775265) B6775265
theorem B4017131 : Blo 1784093 4017131 := bstep (se 1 (by rfl) ⟨3012848, by rfl⟩ : syracuseStep 4017131 = 6025697) B6025697
theorem B17386525 : Blo 1784093 17386525 := bstep (se 3 (by rfl) ⟨3259973, by rfl⟩ : syracuseStep 17386525 = 6519947) B6519947
theorem B6024239 : Blo 1784093 6024239 := bstep (se 1 (by rfl) ⟨4518179, by rfl⟩ : syracuseStep 6024239 = 9036359) B9036359
theorem B4516985 : Blo 1784093 4516985 := bstep (se 2 (by rfl) ⟨1693869, by rfl⟩ : syracuseStep 4516985 = 3387739) B3387739
theorem B15281287 : Blo 1784093 15281287 := bstep (se 1 (by rfl) ⟨11460965, by rfl⟩ : syracuseStep 15281287 = 22921931) B22921931
theorem B10161395 : Blo 1784093 10161395 := bstep (se 1 (by rfl) ⟨7621046, by rfl⟩ : syracuseStep 10161395 = 15242093) B15242093
theorem B52178269 : Blo 1784093 52178269 := bstep (se 3 (by rfl) ⟨9783425, by rfl⟩ : syracuseStep 52178269 = 19566851) B19566851
theorem B6024617 : Blo 1784093 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B8695369 : Blo 1784093 8695369 := bstep (se 2 (by rfl) ⟨3260763, by rfl⟩ : syracuseStep 8695369 = 6521527) B6521527
theorem B6434599 : Blo 1784093 6434599 := bstep (se 1 (by rfl) ⟨4825949, by rfl⟩ : syracuseStep 6434599 = 9651899) B9651899
theorem B4017959 : Blo 1784093 4017959 := bstep (se 1 (by rfl) ⟨3013469, by rfl⟩ : syracuseStep 4017959 = 6026939) B6026939
theorem B8146727 : Blo 1784093 8146727 := bstep (se 1 (by rfl) ⟨6110045, by rfl⟩ : syracuseStep 8146727 = 12220091) B12220091
theorem B381136697 : Blo 1784093 381136697 := bstep (se 2 (by rfl) ⟨142926261, by rfl⟩ : syracuseStep 381136697 = 285852523) B285852523
theorem B6025103 : Blo 1784093 6025103 := bstep (se 1 (by rfl) ⟨4518827, by rfl⟩ : syracuseStep 6025103 = 9037655) B9037655
theorem B3387359 : Blo 1784093 3387359 := bstep (se 1 (by rfl) ⟨2540519, by rfl⟩ : syracuseStep 3387359 = 5081039) B5081039
theorem B38613125 : Blo 1784093 38613125 := bstep (se 4 (by rfl) ⟨3619980, by rfl⟩ : syracuseStep 38613125 = 7239961) B7239961
theorem B6025481 : Blo 1784093 6025481 := bstep (se 2 (by rfl) ⟨2259555, by rfl⟩ : syracuseStep 6025481 = 4519111) B4519111
theorem B3010871 : Blo 1784093 3010871 := bstep (se 1 (by rfl) ⟨2258153, by rfl⟩ : syracuseStep 3010871 = 4516307) B4516307
theorem B4518281 : Blo 1784093 4518281 := bstep (se 2 (by rfl) ⟨1694355, by rfl⟩ : syracuseStep 4518281 = 3388711) B3388711
theorem B11432441 : Blo 1784093 11432441 := bstep (se 2 (by rfl) ⟨4287165, by rfl⟩ : syracuseStep 11432441 = 8574331) B8574331
theorem B6779639 : Blo 1784093 6779639 := bstep (se 1 (by rfl) ⟨5084729, by rfl⟩ : syracuseStep 6779639 = 10169459) B10169459
theorem B9032471 : Blo 1784093 9032471 := bstep (se 1 (by rfl) ⟨6774353, by rfl⟩ : syracuseStep 9032471 = 13548707) B13548707
theorem B44626889 : Blo 1784093 44626889 := bstep (se 2 (by rfl) ⟨16735083, by rfl⟩ : syracuseStep 44626889 = 33470167) B33470167
theorem B24433609 : Blo 1784093 24433609 := bstep (se 2 (by rfl) ⟨9162603, by rfl⟩ : syracuseStep 24433609 = 18325207) B18325207
theorem B3011647 : Blo 1784093 3011647 := bstep (se 1 (by rfl) ⟨2258735, by rfl⟩ : syracuseStep 3011647 = 4517471) B4517471
theorem B6026615 : Blo 1784093 6026615 := bstep (se 1 (by rfl) ⟨4519961, by rfl⟩ : syracuseStep 6026615 = 9039923) B9039923
theorem B3012167 : Blo 1784093 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B2676335 : Blo 1784093 2676335 := bstep (se 1 (by rfl) ⟨2007251, by rfl⟩ : syracuseStep 2676335 = 4014503) B4014503
theorem B2258543 : Blo 1784093 2258543 := bstep (se 1 (by rfl) ⟨1693907, by rfl⟩ : syracuseStep 2258543 = 3387815) B3387815
theorem B2258599 : Blo 1784093 2258599 := bstep (se 1 (by rfl) ⟨1693949, by rfl⟩ : syracuseStep 2258599 = 3387899) B3387899
theorem B2676407 : Blo 1784093 2676407 := bstep (se 1 (by rfl) ⟨2007305, by rfl⟩ : syracuseStep 2676407 = 4014611) B4014611
theorem B8582867 : Blo 1784093 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B2676443 : Blo 1784093 2676443 := bstep (se 1 (by rfl) ⟨2007332, by rfl⟩ : syracuseStep 2676443 = 4014665) B4014665
theorem B3012383 : Blo 1784093 3012383 := bstep (se 1 (by rfl) ⟨2259287, by rfl⟩ : syracuseStep 3012383 = 4518575) B4518575
theorem B2676617 : Blo 1784093 2676617 := bstep (se 2 (by rfl) ⟨1003731, by rfl⟩ : syracuseStep 2676617 = 2007463) B2007463
theorem B5576663 : Blo 1784093 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B2676719 : Blo 1784093 2676719 := bstep (se 1 (by rfl) ⟨2007539, by rfl⟩ : syracuseStep 2676719 = 4015079) B4015079
theorem B3012599 : Blo 1784093 3012599 := bstep (se 1 (by rfl) ⟨2259449, by rfl⟩ : syracuseStep 3012599 = 4518899) B4518899
theorem B11434081 : Blo 1784093 11434081 := bstep (se 2 (by rfl) ⟨4287780, by rfl⟩ : syracuseStep 11434081 = 8575561) B8575561
theorem B4520033 : Blo 1784093 4520033 := bstep (se 2 (by rfl) ⟨1695012, by rfl⟩ : syracuseStep 4520033 = 3390025) B3390025
theorem B6027425 : Blo 1784093 6027425 := bstep (se 2 (by rfl) ⟨2260284, by rfl⟩ : syracuseStep 6027425 = 4520569) B4520569
theorem B2676971 : Blo 1784093 2676971 := bstep (se 1 (by rfl) ⟨2007728, by rfl⟩ : syracuseStep 2676971 = 4015457) B4015457
theorem B13555997 : Blo 1784093 13555997 := bstep (se 3 (by rfl) ⟨2541749, by rfl⟩ : syracuseStep 13555997 = 5083499) B5083499
theorem B2677031 : Blo 1784093 2677031 := bstep (se 1 (by rfl) ⟨2007773, by rfl⟩ : syracuseStep 2677031 = 4015547) B4015547
theorem B4290857 : Blo 1784093 4290857 := bstep (se 2 (by rfl) ⟨1609071, by rfl⟩ : syracuseStep 4290857 = 3218143) B3218143
theorem B1784111 : Blo 1784093 1784111 := bstep (se 1 (by rfl) ⟨1338083, by rfl⟩ : syracuseStep 1784111 = 2676167) B2676167
theorem B2259247 : Blo 1784093 2259247 := bstep (se 1 (by rfl) ⟨1694435, by rfl⟩ : syracuseStep 2259247 = 3388871) B3388871
theorem B9034091 : Blo 1784093 9034091 := bstep (se 1 (by rfl) ⟨6775568, by rfl⟩ : syracuseStep 9034091 = 13551137) B13551137
theorem B2677115 : Blo 1784093 2677115 := bstep (se 1 (by rfl) ⟨2007836, by rfl⟩ : syracuseStep 2677115 = 4015673) B4015673
theorem B6027695 : Blo 1784093 6027695 := bstep (se 1 (by rfl) ⟨4520771, by rfl⟩ : syracuseStep 6027695 = 9041543) B9041543
theorem B16292285 : Blo 1784093 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B17160659 : Blo 1784093 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B1784347 : Blo 1784093 1784347 := bstep (se 1 (by rfl) ⟨1338260, by rfl⟩ : syracuseStep 1784347 = 2676521) B2676521
theorem B1784351 : Blo 1784093 1784351 := bstep (se 1 (by rfl) ⟨1338263, by rfl⟩ : syracuseStep 1784351 = 2676527) B2676527
theorem B1907231 : Blo 1784093 1907231 := bstep (se 1 (by rfl) ⟨1430423, by rfl⟩ : syracuseStep 1907231 = 2860847) B2860847
theorem B2677385 : Blo 1784093 2677385 := bstep (se 2 (by rfl) ⟨1004019, by rfl⟩ : syracuseStep 2677385 = 2008039) B2008039
theorem B13548221 : Blo 1784093 13548221 := bstep (se 3 (by rfl) ⟨2540291, by rfl⟩ : syracuseStep 13548221 = 5080583) B5080583
theorem B11442977 : Blo 1784093 11442977 := bstep (se 2 (by rfl) ⟨4291116, by rfl⟩ : syracuseStep 11442977 = 8582233) B8582233
theorem B2677559 : Blo 1784093 2677559 := bstep (se 1 (by rfl) ⟨2008169, by rfl⟩ : syracuseStep 2677559 = 4016339) B4016339
theorem B9034577 : Blo 1784093 9034577 := bstep (se 2 (by rfl) ⟨3387966, by rfl⟩ : syracuseStep 9034577 = 6775933) B6775933
theorem B1784667 : Blo 1784093 1784667 := bstep (se 1 (by rfl) ⟨1338500, by rfl⟩ : syracuseStep 1784667 = 2677001) B2677001
theorem B2677595 : Blo 1784093 2677595 := bstep (se 1 (by rfl) ⟨2008196, by rfl⟩ : syracuseStep 2677595 = 4016393) B4016393
theorem B1784735 : Blo 1784093 1784735 := bstep (se 1 (by rfl) ⟨1338551, by rfl⟩ : syracuseStep 1784735 = 2677103) B2677103
theorem B11443103 : Blo 1784093 11443103 := bstep (se 1 (by rfl) ⟨8582327, by rfl⟩ : syracuseStep 11443103 = 17164655) B17164655
theorem B2677739 : Blo 1784093 2677739 := bstep (se 1 (by rfl) ⟨2008304, by rfl⟩ : syracuseStep 2677739 = 4016609) B4016609
theorem B1784879 : Blo 1784093 1784879 := bstep (se 1 (by rfl) ⟨1338659, by rfl⟩ : syracuseStep 1784879 = 2677319) B2677319
theorem B3013679 : Blo 1784093 3013679 := bstep (se 1 (by rfl) ⟨2260259, by rfl⟩ : syracuseStep 3013679 = 4520519) B4520519
theorem B1784903 : Blo 1784093 1784903 := bstep (se 1 (by rfl) ⟨1338677, by rfl⟩ : syracuseStep 1784903 = 2677355) B2677355
theorem B3013753 : Blo 1784093 3013753 := bstep (se 2 (by rfl) ⟨1130157, by rfl⟩ : syracuseStep 3013753 = 2260315) B2260315
theorem B2677943 : Blo 1784093 2677943 := bstep (se 1 (by rfl) ⟨2008457, by rfl⟩ : syracuseStep 2677943 = 4016915) B4016915
theorem B1785055 : Blo 1784093 1785055 := bstep (se 1 (by rfl) ⟨1338791, by rfl⟩ : syracuseStep 1785055 = 2677583) B2677583
theorem B8691083 : Blo 1784093 8691083 := bstep (se 1 (by rfl) ⟨6518312, by rfl⟩ : syracuseStep 8691083 = 13036625) B13036625
theorem B2678183 : Blo 1784093 2678183 := bstep (se 1 (by rfl) ⟨2008637, by rfl⟩ : syracuseStep 2678183 = 4017275) B4017275
theorem B1785319 : Blo 1784093 1785319 := bstep (se 1 (by rfl) ⟨1338989, by rfl⟩ : syracuseStep 1785319 = 2677979) B2677979
theorem B2678267 : Blo 1784093 2678267 := bstep (se 1 (by rfl) ⟨2008700, by rfl⟩ : syracuseStep 2678267 = 4017401) B4017401
theorem B10165769 : Blo 1784093 10165769 := bstep (se 2 (by rfl) ⟨3812163, by rfl⟩ : syracuseStep 10165769 = 7624327) B7624327
theorem B1785435 : Blo 1784093 1785435 := bstep (se 1 (by rfl) ⟨1339076, by rfl⟩ : syracuseStep 1785435 = 2678153) B2678153
theorem B2678363 : Blo 1784093 2678363 := bstep (se 1 (by rfl) ⟨2008772, by rfl⟩ : syracuseStep 2678363 = 4017545) B4017545
theorem B51486353 : Blo 1784093 51486353 := bstep (se 2 (by rfl) ⟨19307382, by rfl⟩ : syracuseStep 51486353 = 38614765) B38614765
theorem B2678447 : Blo 1784093 2678447 := bstep (se 1 (by rfl) ⟨2008835, by rfl⟩ : syracuseStep 2678447 = 4017671) B4017671
theorem B9035549 : Blo 1784093 9035549 := bstep (se 3 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 9035549 = 3388331) B3388331
theorem B2678567 : Blo 1784093 2678567 := bstep (se 1 (by rfl) ⟨2008925, by rfl⟩ : syracuseStep 2678567 = 4017851) B4017851
theorem B208772923 : Blo 1784093 208772923 := bstep (se 1 (by rfl) ⟨156579692, by rfl⟩ : syracuseStep 208772923 = 313159385) B313159385
theorem B10166087 : Blo 1784093 10166087 := bstep (se 1 (by rfl) ⟨7624565, by rfl⟩ : syracuseStep 10166087 = 15249131) B15249131
theorem B1785671 : Blo 1784093 1785671 := bstep (se 1 (by rfl) ⟨1339253, by rfl⟩ : syracuseStep 1785671 = 2678507) B2678507
theorem B2678651 : Blo 1784093 2678651 := bstep (se 1 (by rfl) ⟨2008988, by rfl⟩ : syracuseStep 2678651 = 4017977) B4017977
theorem B1785823 : Blo 1784093 1785823 := bstep (se 1 (by rfl) ⟨1339367, by rfl⟩ : syracuseStep 1785823 = 2678735) B2678735
theorem B15245441 : Blo 1784093 15245441 := bstep (se 2 (by rfl) ⟨5717040, by rfl⟩ : syracuseStep 15245441 = 11434081) B11434081
theorem B1786047 : Blo 1784093 1786047 := bstep (se 1 (by rfl) ⟨1339535, by rfl⟩ : syracuseStep 1786047 = 2679071) B2679071
theorem B2007247 : Blo 1784093 2007247 := bstep (se 1 (by rfl) ⟨1505435, by rfl⟩ : syracuseStep 2007247 = 3010871) B3010871
theorem B1786063 : Blo 1784093 1786063 := bstep (se 1 (by rfl) ⟨1339547, by rfl⟩ : syracuseStep 1786063 = 2679095) B2679095
theorem B46375301 : Blo 1784093 46375301 := bstep (se 4 (by rfl) ⟨4347684, by rfl⟩ : syracuseStep 46375301 = 8695369) B8695369
theorem B27910561 : Blo 1784093 27910561 := bstep (se 2 (by rfl) ⟨10466460, by rfl⟩ : syracuseStep 27910561 = 20932921) B20932921
theorem B6021647 : Blo 1784093 6021647 := bstep (se 1 (by rfl) ⟨4516235, by rfl⟩ : syracuseStep 6021647 = 9032471) B9032471
theorem B2008111 : Blo 1784093 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B4015295 : Blo 1784093 4015295 := bstep (se 1 (by rfl) ⟨3011471, by rfl⟩ : syracuseStep 4015295 = 6022943) B6022943
theorem B2008255 : Blo 1784093 2008255 := bstep (se 1 (by rfl) ⟨1506191, by rfl⟩ : syracuseStep 2008255 = 3012383) B3012383
theorem B6022457 : Blo 1784093 6022457 := bstep (se 2 (by rfl) ⟨2258421, by rfl⟩ : syracuseStep 6022457 = 4516843) B4516843
theorem B4015439 : Blo 1784093 4015439 := bstep (se 1 (by rfl) ⟨3011579, by rfl⟩ : syracuseStep 4015439 = 6023159) B6023159
theorem B2008399 : Blo 1784093 2008399 := bstep (se 1 (by rfl) ⟨1506299, by rfl⟩ : syracuseStep 2008399 = 3012599) B3012599
theorem B4015529 : Blo 1784093 4015529 := bstep (se 2 (by rfl) ⟨1505823, by rfl⟩ : syracuseStep 4015529 = 3011647) B3011647
theorem B9037331 : Blo 1784093 9037331 := bstep (se 1 (by rfl) ⟨6777998, by rfl⟩ : syracuseStep 9037331 = 13555997) B13555997
theorem B2860571 : Blo 1784093 2860571 := bstep (se 1 (by rfl) ⟨2145428, by rfl⟩ : syracuseStep 2860571 = 4290857) B4290857
theorem B5080607 : Blo 1784093 5080607 := bstep (se 1 (by rfl) ⟨3810455, by rfl⟩ : syracuseStep 5080607 = 7620911) B7620911
theorem B6022727 : Blo 1784093 6022727 := bstep (se 1 (by rfl) ⟨4517045, by rfl⟩ : syracuseStep 6022727 = 9034091) B9034091
theorem B30508649 : Blo 1784093 30508649 := bstep (se 2 (by rfl) ⟨11440743, by rfl⟩ : syracuseStep 30508649 = 22881487) B22881487
theorem B6022781 : Blo 1784093 6022781 := bstep (se 3 (by rfl) ⟨1129271, by rfl⟩ : syracuseStep 6022781 = 2258543) B2258543
theorem B7628651 : Blo 1784093 7628651 := bstep (se 1 (by rfl) ⟨5721488, by rfl⟩ : syracuseStep 7628651 = 11442977) B11442977
theorem B6023051 : Blo 1784093 6023051 := bstep (se 1 (by rfl) ⟨4517288, by rfl⟩ : syracuseStep 6023051 = 9034577) B9034577
theorem B4016015 : Blo 1784093 4016015 := bstep (se 1 (by rfl) ⟨3012011, by rfl⟩ : syracuseStep 4016015 = 6024023) B6024023
theorem B19294109 : Blo 1784093 19294109 := bstep (se 3 (by rfl) ⟨3617645, by rfl⟩ : syracuseStep 19294109 = 7235291) B7235291
theorem B7628701 : Blo 1784093 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B7628735 : Blo 1784093 7628735 := bstep (se 1 (by rfl) ⟨5721551, by rfl⟩ : syracuseStep 7628735 = 11443103) B11443103
theorem B4016159 : Blo 1784093 4016159 := bstep (se 1 (by rfl) ⟨3012119, by rfl⟩ : syracuseStep 4016159 = 6024239) B6024239
theorem B2009119 : Blo 1784093 2009119 := bstep (se 1 (by rfl) ⟨1506839, by rfl⟩ : syracuseStep 2009119 = 3013679) B3013679
theorem B5794055 : Blo 1784093 5794055 := bstep (se 1 (by rfl) ⟨4345541, by rfl⟩ : syracuseStep 5794055 = 8691083) B8691083
theorem B4016411 : Blo 1784093 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B6777179 : Blo 1784093 6777179 := bstep (se 1 (by rfl) ⟨5082884, by rfl⟩ : syracuseStep 6777179 = 10165769) B10165769
theorem B8579465 : Blo 1784093 8579465 := bstep (se 2 (by rfl) ⟨3217299, by rfl⟩ : syracuseStep 8579465 = 6434599) B6434599
theorem B6023699 : Blo 1784093 6023699 := bstep (se 1 (by rfl) ⟨4517774, by rfl⟩ : syracuseStep 6023699 = 9035549) B9035549
theorem B6777391 : Blo 1784093 6777391 := bstep (se 1 (by rfl) ⟨5083043, by rfl⟩ : syracuseStep 6777391 = 10166087) B10166087
theorem B4016735 : Blo 1784093 4016735 := bstep (se 1 (by rfl) ⟨3012551, by rfl⟩ : syracuseStep 4016735 = 6025103) B6025103
theorem B10169003 : Blo 1784093 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B25742083 : Blo 1784093 25742083 := bstep (se 1 (by rfl) ⟨19306562, by rfl⟩ : syracuseStep 25742083 = 38613125) B38613125
theorem B4016987 : Blo 1784093 4016987 := bstep (se 1 (by rfl) ⟨3012740, by rfl⟩ : syracuseStep 4016987 = 6025481) B6025481
theorem B17165195 : Blo 1784093 17165195 := bstep (se 1 (by rfl) ⟨12873896, by rfl⟩ : syracuseStep 17165195 = 25747793) B25747793
theorem B4287455 : Blo 1784093 4287455 := bstep (se 1 (by rfl) ⟨3215591, by rfl⟩ : syracuseStep 4287455 = 6431183) B6431183
theorem B7621627 : Blo 1784093 7621627 := bstep (se 1 (by rfl) ⟨5716220, by rfl⟩ : syracuseStep 7621627 = 11432441) B11432441
theorem B6024671 : Blo 1784093 6024671 := bstep (se 1 (by rfl) ⟨4518503, by rfl⟩ : syracuseStep 6024671 = 9037007) B9037007
theorem B6778363 : Blo 1784093 6778363 := bstep (se 1 (by rfl) ⟨5083772, by rfl⟩ : syracuseStep 6778363 = 10167545) B10167545
theorem B4017743 : Blo 1784093 4017743 := bstep (se 1 (by rfl) ⟨3013307, by rfl⟩ : syracuseStep 4017743 = 6026615) B6026615
theorem B5721911 : Blo 1784093 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B3813257 : Blo 1784093 3813257 := bstep (se 2 (by rfl) ⟨1429971, by rfl⟩ : syracuseStep 3813257 = 2859943) B2859943
theorem B4288427 : Blo 1784093 4288427 := bstep (se 1 (by rfl) ⟨3216320, by rfl⟩ : syracuseStep 4288427 = 6432641) B6432641
theorem B4018283 : Blo 1784093 4018283 := bstep (se 1 (by rfl) ⟨3013712, by rfl⟩ : syracuseStep 4018283 = 6027425) B6027425
theorem B97702037 : Blo 1784093 97702037 := bstep (se 6 (by rfl) ⟨2289891, by rfl⟩ : syracuseStep 97702037 = 4579783) B4579783
theorem B4018337 : Blo 1784093 4018337 := bstep (se 2 (by rfl) ⟨1506876, by rfl⟩ : syracuseStep 4018337 = 3013753) B3013753
theorem B10170643 : Blo 1784093 10170643 := bstep (se 1 (by rfl) ⟨7627982, by rfl⟩ : syracuseStep 10170643 = 15255965) B15255965
theorem B4018463 : Blo 1784093 4018463 := bstep (se 1 (by rfl) ⟨3013847, by rfl⟩ : syracuseStep 4018463 = 6027695) B6027695
theorem B11440439 : Blo 1784093 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B69571025 : Blo 1784093 69571025 := bstep (se 2 (by rfl) ⟨26089134, by rfl⟩ : syracuseStep 69571025 = 52178269) B52178269
theorem B9032147 : Blo 1784093 9032147 := bstep (se 1 (by rfl) ⟨6774110, by rfl⟩ : syracuseStep 9032147 = 13548221) B13548221
theorem B3011323 : Blo 1784093 3011323 := bstep (se 1 (by rfl) ⟨2258492, by rfl⟩ : syracuseStep 3011323 = 4516985) B4516985
theorem B3011465 : Blo 1784093 3011465 := bstep (se 2 (by rfl) ⟨1129299, by rfl⟩ : syracuseStep 3011465 = 2258599) B2258599
theorem B6435881 : Blo 1784093 6435881 := bstep (se 2 (by rfl) ⟨2413455, by rfl⟩ : syracuseStep 6435881 = 4826911) B4826911
theorem B9032957 : Blo 1784093 9032957 := bstep (se 3 (by rfl) ⟨1693679, by rfl⟩ : syracuseStep 9032957 = 3387359) B3387359
theorem B15250841 : Blo 1784093 15250841 := bstep (se 2 (by rfl) ⟨5719065, by rfl⟩ : syracuseStep 15250841 = 11438131) B11438131
theorem B38589857 : Blo 1784093 38589857 := bstep (se 2 (by rfl) ⟨14471196, by rfl⟩ : syracuseStep 38589857 = 28942393) B28942393
theorem B264000973 : Blo 1784093 264000973 := bstep (se 3 (by rfl) ⟨49500182, by rfl⟩ : syracuseStep 264000973 = 99000365) B99000365
theorem B3012187 : Blo 1784093 3012187 := bstep (se 1 (by rfl) ⟨2259140, by rfl⟩ : syracuseStep 3012187 = 4518281) B4518281
theorem B3012329 : Blo 1784093 3012329 := bstep (se 2 (by rfl) ⟨1129623, by rfl⟩ : syracuseStep 3012329 = 2259247) B2259247
theorem B2676551 : Blo 1784093 2676551 := bstep (se 1 (by rfl) ⟨2007413, by rfl⟩ : syracuseStep 2676551 = 4014827) B4014827
theorem B4519759 : Blo 1784093 4519759 := bstep (se 1 (by rfl) ⟨3389819, by rfl⟩ : syracuseStep 4519759 = 6779639) B6779639
theorem B81500197 : Blo 1784093 81500197 := bstep (se 4 (by rfl) ⟨7640643, by rfl⟩ : syracuseStep 81500197 = 15281287) B15281287
theorem B9033767 : Blo 1784093 9033767 := bstep (se 1 (by rfl) ⟨6775325, by rfl⟩ : syracuseStep 9033767 = 13550651) B13550651
theorem B1784223 : Blo 1784093 1784223 := bstep (se 1 (by rfl) ⟨1338167, by rfl⟩ : syracuseStep 1784223 = 2676335) B2676335
theorem B2677151 : Blo 1784093 2677151 := bstep (se 1 (by rfl) ⟨2007863, by rfl⟩ : syracuseStep 2677151 = 4015727) B4015727
theorem B1784271 : Blo 1784093 1784271 := bstep (se 1 (by rfl) ⟨1338203, by rfl⟩ : syracuseStep 1784271 = 2676407) B2676407
theorem B1784295 : Blo 1784093 1784295 := bstep (se 1 (by rfl) ⟨1338221, by rfl⟩ : syracuseStep 1784295 = 2676443) B2676443
theorem B2677223 : Blo 1784093 2677223 := bstep (se 1 (by rfl) ⟨2007917, by rfl⟩ : syracuseStep 2677223 = 4015835) B4015835
theorem B1784411 : Blo 1784093 1784411 := bstep (se 1 (by rfl) ⟨1338308, by rfl⟩ : syracuseStep 1784411 = 2676617) B2676617
theorem B32578145 : Blo 1784093 32578145 := bstep (se 2 (by rfl) ⟨12216804, by rfl⟩ : syracuseStep 32578145 = 24433609) B24433609
theorem B3717775 : Blo 1784093 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B6871705 : Blo 1784093 6871705 := bstep (se 2 (by rfl) ⟨2576889, by rfl⟩ : syracuseStep 6871705 = 5153779) B5153779
theorem B1784479 : Blo 1784093 1784479 := bstep (se 1 (by rfl) ⟨1338359, by rfl⟩ : syracuseStep 1784479 = 2676719) B2676719
theorem B23182033 : Blo 1784093 23182033 := bstep (se 2 (by rfl) ⟨8693262, by rfl⟩ : syracuseStep 23182033 = 17386525) B17386525
theorem B3013355 : Blo 1784093 3013355 := bstep (se 1 (by rfl) ⟨2260016, by rfl⟩ : syracuseStep 3013355 = 4520033) B4520033
theorem B5085949 : Blo 1784093 5085949 := bstep (se 3 (by rfl) ⟨953615, by rfl⟩ : syracuseStep 5085949 = 1907231) B1907231
theorem B1784647 : Blo 1784093 1784647 := bstep (se 1 (by rfl) ⟨1338485, by rfl⟩ : syracuseStep 1784647 = 2676971) B2676971
theorem B1784687 : Blo 1784093 1784687 := bstep (se 1 (by rfl) ⟨1338515, by rfl⟩ : syracuseStep 1784687 = 2677031) B2677031
theorem B3218287 : Blo 1784093 3218287 := bstep (se 1 (by rfl) ⟨2413715, by rfl⟩ : syracuseStep 3218287 = 4827431) B4827431
theorem B1784743 : Blo 1784093 1784743 := bstep (se 1 (by rfl) ⟨1338557, by rfl⟩ : syracuseStep 1784743 = 2677115) B2677115
theorem B10861523 : Blo 1784093 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B8698861 : Blo 1784093 8698861 := bstep (se 3 (by rfl) ⟨1631036, by rfl⟩ : syracuseStep 8698861 = 3262073) B3262073
theorem B1784923 : Blo 1784093 1784923 := bstep (se 1 (by rfl) ⟨1338692, by rfl⟩ : syracuseStep 1784923 = 2677385) B2677385
theorem B1785039 : Blo 1784093 1785039 := bstep (se 1 (by rfl) ⟨1338779, by rfl⟩ : syracuseStep 1785039 = 2677559) B2677559
theorem B2677967 : Blo 1784093 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B1785063 : Blo 1784093 1785063 := bstep (se 1 (by rfl) ⟨1338797, by rfl⟩ : syracuseStep 1785063 = 2677595) B2677595
theorem B13556969 : Blo 1784093 13556969 := bstep (se 2 (by rfl) ⟨5083863, by rfl⟩ : syracuseStep 13556969 = 10167727) B10167727
theorem B1785159 : Blo 1784093 1785159 := bstep (se 1 (by rfl) ⟨1338869, by rfl⟩ : syracuseStep 1785159 = 2677739) B2677739
theorem B2678087 : Blo 1784093 2678087 := bstep (se 1 (by rfl) ⟨2008565, by rfl⟩ : syracuseStep 2678087 = 4017131) B4017131
theorem B1785295 : Blo 1784093 1785295 := bstep (se 1 (by rfl) ⟨1338971, by rfl⟩ : syracuseStep 1785295 = 2677943) B2677943
theorem B2678249 : Blo 1784093 2678249 := bstep (se 2 (by rfl) ⟨1004343, by rfl⟩ : syracuseStep 2678249 = 2008687) B2008687
theorem B99016181 : Blo 1784093 99016181 := bstep (se 5 (by rfl) ⟨4641383, by rfl⟩ : syracuseStep 99016181 = 9282767) B9282767
theorem B6774263 : Blo 1784093 6774263 := bstep (se 1 (by rfl) ⟨5080697, by rfl⟩ : syracuseStep 6774263 = 10161395) B10161395
theorem B1785455 : Blo 1784093 1785455 := bstep (se 1 (by rfl) ⟨1339091, by rfl⟩ : syracuseStep 1785455 = 2678183) B2678183
theorem B2678393 : Blo 1784093 2678393 := bstep (se 2 (by rfl) ⟨1004397, by rfl⟩ : syracuseStep 2678393 = 2008795) B2008795
theorem B1785511 : Blo 1784093 1785511 := bstep (se 1 (by rfl) ⟨1339133, by rfl⟩ : syracuseStep 1785511 = 2678267) B2678267
theorem B1785575 : Blo 1784093 1785575 := bstep (se 1 (by rfl) ⟨1339181, by rfl⟩ : syracuseStep 1785575 = 2678363) B2678363
theorem B278363897 : Blo 1784093 278363897 := bstep (se 2 (by rfl) ⟨104386461, by rfl⟩ : syracuseStep 278363897 = 208772923) B208772923
theorem B34324235 : Blo 1784093 34324235 := bstep (se 1 (by rfl) ⟨25743176, by rfl⟩ : syracuseStep 34324235 = 51486353) B51486353
theorem B1785631 : Blo 1784093 1785631 := bstep (se 1 (by rfl) ⟨1339223, by rfl⟩ : syracuseStep 1785631 = 2678447) B2678447
theorem B119005037 : Blo 1784093 119005037 := bstep (se 3 (by rfl) ⟨22313444, by rfl⟩ : syracuseStep 119005037 = 44626889) B44626889
theorem B1785711 : Blo 1784093 1785711 := bstep (se 1 (by rfl) ⟨1339283, by rfl⟩ : syracuseStep 1785711 = 2678567) B2678567
theorem B2678639 : Blo 1784093 2678639 := bstep (se 1 (by rfl) ⟨2008979, by rfl⟩ : syracuseStep 2678639 = 4017959) B4017959
theorem B5431151 : Blo 1784093 5431151 := bstep (se 1 (by rfl) ⟨4073363, by rfl⟩ : syracuseStep 5431151 = 8146727) B8146727
theorem B254091131 : Blo 1784093 254091131 := bstep (se 1 (by rfl) ⟨190568348, by rfl⟩ : syracuseStep 254091131 = 381136697) B381136697
theorem B1785767 : Blo 1784093 1785767 := bstep (se 1 (by rfl) ⟨1339325, by rfl⟩ : syracuseStep 1785767 = 2678651) B2678651
theorem B2678825 : Blo 1784093 2678825 := bstep (se 2 (by rfl) ⟨1004559, by rfl⟩ : syracuseStep 2678825 = 2009119) B2009119
theorem B108666929 : Blo 1784093 108666929 := bstep (se 2 (by rfl) ⟨40750098, by rfl⟩ : syracuseStep 108666929 = 81500197) B81500197
theorem B2678855 : Blo 1784093 2678855 := bstep (se 1 (by rfl) ⟨2009141, by rfl⟩ : syracuseStep 2678855 = 4018283) B4018283
theorem B65134691 : Blo 1784093 65134691 := bstep (se 1 (by rfl) ⟨48851018, by rfl⟩ : syracuseStep 65134691 = 97702037) B97702037
theorem B2678891 : Blo 1784093 2678891 := bstep (se 1 (by rfl) ⟨2009168, by rfl⟩ : syracuseStep 2678891 = 4018337) B4018337
theorem B2678975 : Blo 1784093 2678975 := bstep (se 1 (by rfl) ⟨2009231, by rfl⟩ : syracuseStep 2678975 = 4018463) B4018463
theorem B7626959 : Blo 1784093 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B6021431 : Blo 1784093 6021431 := bstep (se 1 (by rfl) ⟨4516073, by rfl⟩ : syracuseStep 6021431 = 9032147) B9032147
theorem B4014431 : Blo 1784093 4014431 := bstep (se 1 (by rfl) ⟨3010823, by rfl⟩ : syracuseStep 4014431 = 6021647) B6021647
theorem B2007643 : Blo 1784093 2007643 := bstep (se 1 (by rfl) ⟨1505732, by rfl⟩ : syracuseStep 2007643 = 3011465) B3011465
theorem B9036521 : Blo 1784093 9036521 := bstep (se 2 (by rfl) ⟨3388695, by rfl⟩ : syracuseStep 9036521 = 6777391) B6777391
theorem B6021971 : Blo 1784093 6021971 := bstep (se 1 (by rfl) ⟨4516478, by rfl⟩ : syracuseStep 6021971 = 9032957) B9032957
theorem B4957033 : Blo 1784093 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B4014971 : Blo 1784093 4014971 := bstep (se 1 (by rfl) ⟨3011228, by rfl⟩ : syracuseStep 4014971 = 6022457) B6022457
theorem B10167227 : Blo 1784093 10167227 := bstep (se 1 (by rfl) ⟨7625420, by rfl⟩ : syracuseStep 10167227 = 15250841) B15250841
theorem B30909377 : Blo 1784093 30909377 := bstep (se 2 (by rfl) ⟨11591016, by rfl⟩ : syracuseStep 30909377 = 23182033) B23182033
theorem B4015097 : Blo 1784093 4015097 := bstep (se 2 (by rfl) ⟨1505661, by rfl⟩ : syracuseStep 4015097 = 3011323) B3011323
theorem B123667469 : Blo 1784093 123667469 := bstep (se 3 (by rfl) ⟨23187650, by rfl⟩ : syracuseStep 123667469 = 46375301) B46375301
theorem B4015151 : Blo 1784093 4015151 := bstep (se 1 (by rfl) ⟨3011363, by rfl⟩ : syracuseStep 4015151 = 6022727) B6022727
theorem B4015187 : Blo 1784093 4015187 := bstep (se 1 (by rfl) ⟨3011390, by rfl⟩ : syracuseStep 4015187 = 6022781) B6022781
theorem B2008219 : Blo 1784093 2008219 := bstep (se 1 (by rfl) ⟨1506164, by rfl⟩ : syracuseStep 2008219 = 3012329) B3012329
theorem B4015367 : Blo 1784093 4015367 := bstep (se 1 (by rfl) ⟨3011525, by rfl⟩ : syracuseStep 4015367 = 6023051) B6023051
theorem B12862739 : Blo 1784093 12862739 := bstep (se 1 (by rfl) ⟨9647054, by rfl⟩ : syracuseStep 12862739 = 19294109) B19294109
theorem B6022511 : Blo 1784093 6022511 := bstep (se 1 (by rfl) ⟨4516883, by rfl⟩ : syracuseStep 6022511 = 9033767) B9033767
theorem B5719643 : Blo 1784093 5719643 := bstep (se 1 (by rfl) ⟨4289732, by rfl⟩ : syracuseStep 5719643 = 8579465) B8579465
theorem B4015799 : Blo 1784093 4015799 := bstep (se 1 (by rfl) ⟨3011849, by rfl⟩ : syracuseStep 4015799 = 6023699) B6023699
theorem B21718763 : Blo 1784093 21718763 := bstep (se 1 (by rfl) ⟨16289072, by rfl⟩ : syracuseStep 21718763 = 32578145) B32578145
theorem B2008903 : Blo 1784093 2008903 := bstep (se 1 (by rfl) ⟨1506677, by rfl⟩ : syracuseStep 2008903 = 3013355) B3013355
theorem B9037817 : Blo 1784093 9037817 := bstep (se 2 (by rfl) ⟨3389181, by rfl⟩ : syracuseStep 9037817 = 6778363) B6778363
theorem B4016249 : Blo 1784093 4016249 := bstep (se 2 (by rfl) ⟨1506093, by rfl⟩ : syracuseStep 4016249 = 3012187) B3012187
theorem B9037979 : Blo 1784093 9037979 := bstep (se 1 (by rfl) ⟨6778484, by rfl⟩ : syracuseStep 9037979 = 13556969) B13556969
theorem B4016447 : Blo 1784093 4016447 := bstep (se 1 (by rfl) ⟨3012335, by rfl⟩ : syracuseStep 4016447 = 6024671) B6024671
theorem B4516175 : Blo 1784093 4516175 := bstep (se 1 (by rfl) ⟨3387131, by rfl⟩ : syracuseStep 4516175 = 6774263) B6774263
theorem B10168685 : Blo 1784093 10168685 := bstep (se 3 (by rfl) ⟨1906628, by rfl⟩ : syracuseStep 10168685 = 3813257) B3813257
theorem B185575931 : Blo 1784093 185575931 := bstep (se 1 (by rfl) ⟨139181948, by rfl⟩ : syracuseStep 185575931 = 278363897) B278363897
theorem B22882823 : Blo 1784093 22882823 := bstep (se 1 (by rfl) ⟨17162117, by rfl⟩ : syracuseStep 22882823 = 34324235) B34324235
theorem B13560857 : Blo 1784093 13560857 := bstep (se 2 (by rfl) ⟨5085321, by rfl⟩ : syracuseStep 13560857 = 10170643) B10170643
theorem B25726571 : Blo 1784093 25726571 := bstep (se 1 (by rfl) ⟨19294928, by rfl⟩ : syracuseStep 25726571 = 38589857) B38589857
theorem B6024887 : Blo 1784093 6024887 := bstep (se 1 (by rfl) ⟨4518665, by rfl⟩ : syracuseStep 6024887 = 9037331) B9037331
theorem B3387071 : Blo 1784093 3387071 := bstep (se 1 (by rfl) ⟨2540303, by rfl⟩ : syracuseStep 3387071 = 5080607) B5080607
theorem B10162169 : Blo 1784093 10162169 := bstep (se 2 (by rfl) ⟨3810813, by rfl⟩ : syracuseStep 10162169 = 7621627) B7621627
theorem B5085767 : Blo 1784093 5085767 := bstep (se 1 (by rfl) ⟨3814325, by rfl⟩ : syracuseStep 5085767 = 7628651) B7628651
theorem B3862703 : Blo 1784093 3862703 := bstep (se 1 (by rfl) ⟨2897027, by rfl⟩ : syracuseStep 3862703 = 5794055) B5794055
theorem B4518119 : Blo 1784093 4518119 := bstep (se 1 (by rfl) ⟨3388589, by rfl⟩ : syracuseStep 4518119 = 6777179) B6777179
theorem B6779335 : Blo 1784093 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B6026345 : Blo 1784093 6026345 := bstep (se 2 (by rfl) ⟨2259879, by rfl⟩ : syracuseStep 6026345 = 4519759) B4519759
theorem B3814607 : Blo 1784093 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B10171601 : Blo 1784093 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B79336691 : Blo 1784093 79336691 := bstep (se 1 (by rfl) ⟨59502518, by rfl⟩ : syracuseStep 79336691 = 119005037) B119005037
theorem B10163627 : Blo 1784093 10163627 := bstep (se 1 (by rfl) ⟨7622720, by rfl⟩ : syracuseStep 10163627 = 15245441) B15245441
theorem B2676329 : Blo 1784093 2676329 := bstep (se 2 (by rfl) ⟨1003623, by rfl⟩ : syracuseStep 2676329 = 2007247) B2007247
theorem B46380683 : Blo 1784093 46380683 := bstep (se 1 (by rfl) ⟨34785512, by rfl⟩ : syracuseStep 46380683 = 69571025) B69571025
theorem B37214081 : Blo 1784093 37214081 := bstep (se 2 (by rfl) ⟨13955280, by rfl⟩ : syracuseStep 37214081 = 27910561) B27910561
theorem B4290587 : Blo 1784093 4290587 := bstep (se 1 (by rfl) ⟨3217940, by rfl⟩ : syracuseStep 4290587 = 6435881) B6435881
theorem B2676863 : Blo 1784093 2676863 := bstep (se 1 (by rfl) ⟨2007647, by rfl⟩ : syracuseStep 2676863 = 4015295) B4015295
theorem B36649093 : Blo 1784093 36649093 := bstep (se 4 (by rfl) ⟨3435852, by rfl⟩ : syracuseStep 36649093 = 6871705) B6871705
theorem B2676959 : Blo 1784093 2676959 := bstep (se 1 (by rfl) ⟨2007719, by rfl⟩ : syracuseStep 2676959 = 4015439) B4015439
theorem B2677019 : Blo 1784093 2677019 := bstep (se 1 (by rfl) ⟨2007764, by rfl⟩ : syracuseStep 2677019 = 4015529) B4015529
theorem B6781265 : Blo 1784093 6781265 := bstep (se 2 (by rfl) ⟨2542974, by rfl⟩ : syracuseStep 6781265 = 5085949) B5085949
theorem B34322777 : Blo 1784093 34322777 := bstep (se 2 (by rfl) ⟨12871041, by rfl⟩ : syracuseStep 34322777 = 25742083) B25742083
theorem B1907047 : Blo 1784093 1907047 := bstep (se 1 (by rfl) ⟨1430285, by rfl⟩ : syracuseStep 1907047 = 2860571) B2860571
theorem B20339099 : Blo 1784093 20339099 := bstep (se 1 (by rfl) ⟨15254324, by rfl⟩ : syracuseStep 20339099 = 30508649) B30508649
theorem B4291049 : Blo 1784093 4291049 := bstep (se 2 (by rfl) ⟨1609143, by rfl⟩ : syracuseStep 4291049 = 3218287) B3218287
theorem B1784367 : Blo 1784093 1784367 := bstep (se 1 (by rfl) ⟨1338275, by rfl⟩ : syracuseStep 1784367 = 2676551) B2676551
theorem B2677343 : Blo 1784093 2677343 := bstep (se 1 (by rfl) ⟨2008007, by rfl⟩ : syracuseStep 2677343 = 4016015) B4016015
theorem B5085823 : Blo 1784093 5085823 := bstep (se 1 (by rfl) ⟨3814367, by rfl⟩ : syracuseStep 5085823 = 7628735) B7628735
theorem B11598481 : Blo 1784093 11598481 := bstep (se 2 (by rfl) ⟨4349430, by rfl⟩ : syracuseStep 11598481 = 8698861) B8698861
theorem B2677439 : Blo 1784093 2677439 := bstep (se 1 (by rfl) ⟨2008079, by rfl⟩ : syracuseStep 2677439 = 4016159) B4016159
theorem B2677481 : Blo 1784093 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B2677607 : Blo 1784093 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B2677673 : Blo 1784093 2677673 := bstep (se 2 (by rfl) ⟨1004127, by rfl⟩ : syracuseStep 2677673 = 2008255) B2008255
theorem B1784767 : Blo 1784093 1784767 := bstep (se 1 (by rfl) ⟨1338575, by rfl⟩ : syracuseStep 1784767 = 2677151) B2677151
theorem B1784815 : Blo 1784093 1784815 := bstep (se 1 (by rfl) ⟨1338611, by rfl⟩ : syracuseStep 1784815 = 2677223) B2677223
theorem B2677823 : Blo 1784093 2677823 := bstep (se 1 (by rfl) ⟨2008367, by rfl⟩ : syracuseStep 2677823 = 4016735) B4016735
theorem B2677865 : Blo 1784093 2677865 := bstep (se 2 (by rfl) ⟨1004199, by rfl⟩ : syracuseStep 2677865 = 2008399) B2008399
theorem B2677991 : Blo 1784093 2677991 := bstep (se 1 (by rfl) ⟨2008493, by rfl⟩ : syracuseStep 2677991 = 4016987) B4016987
theorem B11443463 : Blo 1784093 11443463 := bstep (se 1 (by rfl) ⟨8582597, by rfl⟩ : syracuseStep 11443463 = 17165195) B17165195
theorem B352001297 : Blo 1784093 352001297 := bstep (se 2 (by rfl) ⟨132000486, by rfl⟩ : syracuseStep 352001297 = 264000973) B264000973
theorem B7241015 : Blo 1784093 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B2858303 : Blo 1784093 2858303 := bstep (se 1 (by rfl) ⟨2143727, by rfl⟩ : syracuseStep 2858303 = 4287455) B4287455
theorem B1785311 : Blo 1784093 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B1785391 : Blo 1784093 1785391 := bstep (se 1 (by rfl) ⟨1339043, by rfl⟩ : syracuseStep 1785391 = 2678087) B2678087
theorem B1785499 : Blo 1784093 1785499 := bstep (se 1 (by rfl) ⟨1339124, by rfl⟩ : syracuseStep 1785499 = 2678249) B2678249
theorem B66010787 : Blo 1784093 66010787 := bstep (se 1 (by rfl) ⟨49508090, by rfl⟩ : syracuseStep 66010787 = 99016181) B99016181
theorem B2678495 : Blo 1784093 2678495 := bstep (se 1 (by rfl) ⟨2008871, by rfl⟩ : syracuseStep 2678495 = 4017743) B4017743
theorem B1785595 : Blo 1784093 1785595 := bstep (se 1 (by rfl) ⟨1339196, by rfl⟩ : syracuseStep 1785595 = 2678393) B2678393
theorem B1785759 : Blo 1784093 1785759 := bstep (se 1 (by rfl) ⟨1339319, by rfl⟩ : syracuseStep 1785759 = 2678639) B2678639
theorem B3620767 : Blo 1784093 3620767 := bstep (se 1 (by rfl) ⟨2715575, by rfl⟩ : syracuseStep 3620767 = 5431151) B5431151
theorem B169394087 : Blo 1784093 169394087 := bstep (se 1 (by rfl) ⟨127045565, by rfl⟩ : syracuseStep 169394087 = 254091131) B254091131
theorem B2858951 : Blo 1784093 2858951 := bstep (se 1 (by rfl) ⟨2144213, by rfl⟩ : syracuseStep 2858951 = 4288427) B4288427
theorem B1785883 : Blo 1784093 1785883 := bstep (se 1 (by rfl) ⟨1339412, by rfl⟩ : syracuseStep 1785883 = 2678825) B2678825
theorem B1785903 : Blo 1784093 1785903 := bstep (se 1 (by rfl) ⟨1339427, by rfl⟩ : syracuseStep 1785903 = 2678855) B2678855
theorem B1785927 : Blo 1784093 1785927 := bstep (se 1 (by rfl) ⟨1339445, by rfl⟩ : syracuseStep 1785927 = 2678891) B2678891
theorem B1785983 : Blo 1784093 1785983 := bstep (se 1 (by rfl) ⟨1339487, by rfl⟩ : syracuseStep 1785983 = 2678975) B2678975
theorem B48865457 : Blo 1784093 48865457 := bstep (se 2 (by rfl) ⟨18324546, by rfl⟩ : syracuseStep 48865457 = 36649093) B36649093
theorem B4014287 : Blo 1784093 4014287 := bstep (se 1 (by rfl) ⟨3010715, by rfl⟩ : syracuseStep 4014287 = 6021431) B6021431
theorem B4014647 : Blo 1784093 4014647 := bstep (se 1 (by rfl) ⟨3010985, by rfl⟩ : syracuseStep 4014647 = 6021971) B6021971
theorem B82444979 : Blo 1784093 82444979 := bstep (se 1 (by rfl) ⟨61833734, by rfl⟩ : syracuseStep 82444979 = 123667469) B123667469
theorem B61858565 : Blo 1784093 61858565 := bstep (se 4 (by rfl) ⟨5799240, by rfl⟩ : syracuseStep 61858565 = 11598481) B11598481
theorem B19309373 : Blo 1784093 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B4015007 : Blo 1784093 4015007 := bstep (se 1 (by rfl) ⟨3011255, by rfl⟩ : syracuseStep 4015007 = 6022511) B6022511
theorem B6775751 : Blo 1784093 6775751 := bstep (se 1 (by rfl) ⟨5081813, by rfl⟩ : syracuseStep 6775751 = 10163627) B10163627
theorem B2860391 : Blo 1784093 2860391 := bstep (se 1 (by rfl) ⟨2145293, by rfl⟩ : syracuseStep 2860391 = 4290587) B4290587
theorem B22881851 : Blo 1784093 22881851 := bstep (se 1 (by rfl) ⟨17161388, by rfl⟩ : syracuseStep 22881851 = 34322777) B34322777
theorem B13559399 : Blo 1784093 13559399 := bstep (se 1 (by rfl) ⟨10169549, by rfl⟩ : syracuseStep 13559399 = 20339099) B20339099
theorem B2860699 : Blo 1784093 2860699 := bstep (se 1 (by rfl) ⟨2145524, by rfl⟩ : syracuseStep 2860699 = 4291049) B4291049
theorem B123717287 : Blo 1784093 123717287 := bstep (se 1 (by rfl) ⟨92787965, by rfl⟩ : syracuseStep 123717287 = 185575931) B185575931
theorem B15255215 : Blo 1784093 15255215 := bstep (se 1 (by rfl) ⟨11441411, by rfl⟩ : syracuseStep 15255215 = 22882823) B22882823
theorem B7628975 : Blo 1784093 7628975 := bstep (se 1 (by rfl) ⟨5721731, by rfl⟩ : syracuseStep 7628975 = 11443463) B11443463
theorem B4016591 : Blo 1784093 4016591 := bstep (se 1 (by rfl) ⟨3012443, by rfl⟩ : syracuseStep 4016591 = 6024887) B6024887
theorem B4827689 : Blo 1784093 4827689 := bstep (se 2 (by rfl) ⟨1810383, by rfl⟩ : syracuseStep 4827689 = 3620767) B3620767
theorem B112929391 : Blo 1784093 112929391 := bstep (se 1 (by rfl) ⟨84697043, by rfl⟩ : syracuseStep 112929391 = 169394087) B169394087
theorem B72444619 : Blo 1784093 72444619 := bstep (se 1 (by rfl) ⟨54333464, by rfl⟩ : syracuseStep 72444619 = 108666929) B108666929
theorem B2575135 : Blo 1784093 2575135 := bstep (se 1 (by rfl) ⟨1931351, by rfl⟩ : syracuseStep 2575135 = 3862703) B3862703
theorem B6024347 : Blo 1784093 6024347 := bstep (se 1 (by rfl) ⟨4518260, by rfl⟩ : syracuseStep 6024347 = 9036521) B9036521
theorem B9039113 : Blo 1784093 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B6778151 : Blo 1784093 6778151 := bstep (se 1 (by rfl) ⟨5083613, by rfl⟩ : syracuseStep 6778151 = 10167227) B10167227
theorem B20606251 : Blo 1784093 20606251 := bstep (se 1 (by rfl) ⟨15454688, by rfl⟩ : syracuseStep 20606251 = 30909377) B30909377
theorem B4017563 : Blo 1784093 4017563 := bstep (se 1 (by rfl) ⟨3013172, by rfl⟩ : syracuseStep 4017563 = 6026345) B6026345
theorem B2543071 : Blo 1784093 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B52891127 : Blo 1784093 52891127 := bstep (se 1 (by rfl) ⟨39668345, by rfl⟩ : syracuseStep 52891127 = 79336691) B79336691
theorem B3813095 : Blo 1784093 3813095 := bstep (se 1 (by rfl) ⟨2859821, by rfl⟩ : syracuseStep 3813095 = 5719643) B5719643
theorem B14479175 : Blo 1784093 14479175 := bstep (se 1 (by rfl) ⟨10859381, by rfl⟩ : syracuseStep 14479175 = 21718763) B21718763
theorem B24809387 : Blo 1784093 24809387 := bstep (se 1 (by rfl) ⟨18607040, by rfl⟩ : syracuseStep 24809387 = 37214081) B37214081
theorem B6025211 : Blo 1784093 6025211 := bstep (se 1 (by rfl) ⟨4518908, by rfl⟩ : syracuseStep 6025211 = 9037817) B9037817
theorem B6025319 : Blo 1784093 6025319 := bstep (se 1 (by rfl) ⟨4518989, by rfl⟩ : syracuseStep 6025319 = 9037979) B9037979
theorem B3010783 : Blo 1784093 3010783 := bstep (se 1 (by rfl) ⟨2258087, by rfl⟩ : syracuseStep 3010783 = 4516175) B4516175
theorem B6779123 : Blo 1784093 6779123 := bstep (se 1 (by rfl) ⟨5084342, by rfl⟩ : syracuseStep 6779123 = 10168685) B10168685
theorem B10170917 : Blo 1784093 10170917 := bstep (se 4 (by rfl) ⟨953523, by rfl⟩ : syracuseStep 10170917 = 1907047) B1907047
theorem B9040571 : Blo 1784093 9040571 := bstep (se 1 (by rfl) ⟨6780428, by rfl⟩ : syracuseStep 9040571 = 13560857) B13560857
theorem B1905535 : Blo 1784093 1905535 := bstep (se 1 (by rfl) ⟨1429151, by rfl⟩ : syracuseStep 1905535 = 2858303) B2858303
theorem B17151047 : Blo 1784093 17151047 := bstep (se 1 (by rfl) ⟨12863285, by rfl⟩ : syracuseStep 17151047 = 25726571) B25726571
theorem B2258047 : Blo 1784093 2258047 := bstep (se 1 (by rfl) ⟨1693535, by rfl⟩ : syracuseStep 2258047 = 3387071) B3387071
theorem B1905967 : Blo 1784093 1905967 := bstep (se 1 (by rfl) ⟨1429475, by rfl⟩ : syracuseStep 1905967 = 2858951) B2858951
theorem B43423127 : Blo 1784093 43423127 := bstep (se 1 (by rfl) ⟨32567345, by rfl⟩ : syracuseStep 43423127 = 65134691) B65134691
theorem B5084639 : Blo 1784093 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B3012079 : Blo 1784093 3012079 := bstep (se 1 (by rfl) ⟨2259059, by rfl⟩ : syracuseStep 3012079 = 4518119) B4518119
theorem B2676287 : Blo 1784093 2676287 := bstep (se 1 (by rfl) ⟨2007215, by rfl⟩ : syracuseStep 2676287 = 4014431) B4014431
theorem B2676647 : Blo 1784093 2676647 := bstep (se 1 (by rfl) ⟨2007485, by rfl⟩ : syracuseStep 2676647 = 4014971) B4014971
theorem B2676731 : Blo 1784093 2676731 := bstep (se 1 (by rfl) ⟨2007548, by rfl⟩ : syracuseStep 2676731 = 4015097) B4015097
theorem B2676767 : Blo 1784093 2676767 := bstep (se 1 (by rfl) ⟨2007575, by rfl⟩ : syracuseStep 2676767 = 4015151) B4015151
theorem B2676791 : Blo 1784093 2676791 := bstep (se 1 (by rfl) ⟨2007593, by rfl⟩ : syracuseStep 2676791 = 4015187) B4015187
theorem B2676857 : Blo 1784093 2676857 := bstep (se 2 (by rfl) ⟨1003821, by rfl⟩ : syracuseStep 2676857 = 2007643) B2007643
theorem B6781067 : Blo 1784093 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B6781097 : Blo 1784093 6781097 := bstep (se 2 (by rfl) ⟨2542911, by rfl⟩ : syracuseStep 6781097 = 5085823) B5085823
theorem B2676911 : Blo 1784093 2676911 := bstep (se 1 (by rfl) ⟨2007683, by rfl⟩ : syracuseStep 2676911 = 4015367) B4015367
theorem B8575159 : Blo 1784093 8575159 := bstep (se 1 (by rfl) ⟨6431369, by rfl⟩ : syracuseStep 8575159 = 12862739) B12862739
theorem B1784219 : Blo 1784093 1784219 := bstep (se 1 (by rfl) ⟨1338164, by rfl⟩ : syracuseStep 1784219 = 2676329) B2676329
theorem B2677199 : Blo 1784093 2677199 := bstep (se 1 (by rfl) ⟨2007899, by rfl⟩ : syracuseStep 2677199 = 4015799) B4015799
theorem B6609377 : Blo 1784093 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B2677499 : Blo 1784093 2677499 := bstep (se 1 (by rfl) ⟨2008124, by rfl⟩ : syracuseStep 2677499 = 4016249) B4016249
theorem B1784575 : Blo 1784093 1784575 := bstep (se 1 (by rfl) ⟨1338431, by rfl⟩ : syracuseStep 1784575 = 2676863) B2676863
theorem B1784639 : Blo 1784093 1784639 := bstep (se 1 (by rfl) ⟨1338479, by rfl⟩ : syracuseStep 1784639 = 2676959) B2676959
theorem B1784679 : Blo 1784093 1784679 := bstep (se 1 (by rfl) ⟨1338509, by rfl⟩ : syracuseStep 1784679 = 2677019) B2677019
theorem B2677625 : Blo 1784093 2677625 := bstep (se 2 (by rfl) ⟨1004109, by rfl⟩ : syracuseStep 2677625 = 2008219) B2008219
theorem B2677631 : Blo 1784093 2677631 := bstep (se 1 (by rfl) ⟨2008223, by rfl⟩ : syracuseStep 2677631 = 4016447) B4016447
theorem B4520843 : Blo 1784093 4520843 := bstep (se 1 (by rfl) ⟨3390632, by rfl⟩ : syracuseStep 4520843 = 6781265) B6781265
theorem B123681821 : Blo 1784093 123681821 := bstep (se 3 (by rfl) ⟨23190341, by rfl⟩ : syracuseStep 123681821 = 46380683) B46380683
theorem B3390511 : Blo 1784093 3390511 := bstep (se 1 (by rfl) ⟨2542883, by rfl⟩ : syracuseStep 3390511 = 5085767) B5085767
theorem B1784895 : Blo 1784093 1784895 := bstep (se 1 (by rfl) ⟨1338671, by rfl⟩ : syracuseStep 1784895 = 2677343) B2677343
theorem B1784959 : Blo 1784093 1784959 := bstep (se 1 (by rfl) ⟨1338719, by rfl⟩ : syracuseStep 1784959 = 2677439) B2677439
theorem B1784987 : Blo 1784093 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B1785071 : Blo 1784093 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B1785115 : Blo 1784093 1785115 := bstep (se 1 (by rfl) ⟨1338836, by rfl⟩ : syracuseStep 1785115 = 2677673) B2677673
theorem B1785215 : Blo 1784093 1785215 := bstep (se 1 (by rfl) ⟨1338911, by rfl⟩ : syracuseStep 1785215 = 2677823) B2677823
theorem B1785243 : Blo 1784093 1785243 := bstep (se 1 (by rfl) ⟨1338932, by rfl⟩ : syracuseStep 1785243 = 2677865) B2677865
theorem B1785327 : Blo 1784093 1785327 := bstep (se 1 (by rfl) ⟨1338995, by rfl⟩ : syracuseStep 1785327 = 2677991) B2677991
theorem B234667531 : Blo 1784093 234667531 := bstep (se 1 (by rfl) ⟨176000648, by rfl⟩ : syracuseStep 234667531 = 352001297) B352001297
theorem B2678537 : Blo 1784093 2678537 := bstep (se 2 (by rfl) ⟨1004451, by rfl⟩ : syracuseStep 2678537 = 2008903) B2008903
theorem B44007191 : Blo 1784093 44007191 := bstep (se 1 (by rfl) ⟨33005393, by rfl⟩ : syracuseStep 44007191 = 66010787) B66010787
theorem B1785663 : Blo 1784093 1785663 := bstep (se 1 (by rfl) ⟨1339247, by rfl⟩ : syracuseStep 1785663 = 2678495) B2678495
theorem B6774779 : Blo 1784093 6774779 := bstep (se 1 (by rfl) ⟨5081084, by rfl⟩ : syracuseStep 6774779 = 10162169) B10162169
theorem B329818189 : Blo 1784093 329818189 := bstep (se 3 (by rfl) ⟨61840910, by rfl⟩ : syracuseStep 329818189 = 123681821) B123681821
theorem B4014377 : Blo 1784093 4014377 := bstep (se 2 (by rfl) ⟨1505391, by rfl⟩ : syracuseStep 4014377 = 3010783) B3010783
theorem B41239043 : Blo 1784093 41239043 := bstep (se 1 (by rfl) ⟨30929282, by rfl⟩ : syracuseStep 41239043 = 61858565) B61858565
theorem B96592825 : Blo 1784093 96592825 := bstep (se 2 (by rfl) ⟨36222309, by rfl⟩ : syracuseStep 96592825 = 72444619) B72444619
theorem B7627709 : Blo 1784093 7627709 := bstep (se 3 (by rfl) ⟨1430195, by rfl⟩ : syracuseStep 7627709 = 2860391) B2860391
theorem B15254567 : Blo 1784093 15254567 := bstep (se 1 (by rfl) ⟨11440925, by rfl⟩ : syracuseStep 15254567 = 22881851) B22881851
theorem B3433513 : Blo 1784093 3433513 := bstep (se 2 (by rfl) ⟨1287567, by rfl⟩ : syracuseStep 3433513 = 2575135) B2575135
theorem B82478191 : Blo 1784093 82478191 := bstep (se 1 (by rfl) ⟨61858643, by rfl⟩ : syracuseStep 82478191 = 123717287) B123717287
theorem B2541289 : Blo 1784093 2541289 := bstep (se 2 (by rfl) ⟨952983, by rfl⟩ : syracuseStep 2541289 = 1905967) B1905967
theorem B10168253 : Blo 1784093 10168253 := bstep (se 3 (by rfl) ⟨1906547, by rfl⟩ : syracuseStep 10168253 = 3813095) B3813095
theorem B4016105 : Blo 1784093 4016105 := bstep (se 2 (by rfl) ⟨1506039, by rfl⟩ : syracuseStep 4016105 = 3012079) B3012079
theorem B4016231 : Blo 1784093 4016231 := bstep (se 1 (by rfl) ⟨3012173, by rfl⟩ : syracuseStep 4016231 = 6024347) B6024347
theorem B35260751 : Blo 1784093 35260751 := bstep (se 1 (by rfl) ⟨26445563, by rfl⟩ : syracuseStep 35260751 = 52891127) B52891127
theorem B29338127 : Blo 1784093 29338127 := bstep (se 1 (by rfl) ⟨22003595, by rfl⟩ : syracuseStep 29338127 = 44007191) B44007191
theorem B9652783 : Blo 1784093 9652783 := bstep (se 1 (by rfl) ⟨7239587, by rfl⟩ : syracuseStep 9652783 = 14479175) B14479175
theorem B4516519 : Blo 1784093 4516519 := bstep (se 1 (by rfl) ⟨3387389, by rfl⟩ : syracuseStep 4516519 = 6774779) B6774779
theorem B4016807 : Blo 1784093 4016807 := bstep (se 1 (by rfl) ⟨3012605, by rfl⟩ : syracuseStep 4016807 = 6025211) B6025211
theorem B4016879 : Blo 1784093 4016879 := bstep (se 1 (by rfl) ⟨3012659, by rfl⟩ : syracuseStep 4016879 = 6025319) B6025319
theorem B54963319 : Blo 1784093 54963319 := bstep (se 1 (by rfl) ⟨41222489, by rfl⟩ : syracuseStep 54963319 = 82444979) B82444979
theorem B12872915 : Blo 1784093 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B4517167 : Blo 1784093 4517167 := bstep (se 1 (by rfl) ⟨3387875, by rfl⟩ : syracuseStep 4517167 = 6775751) B6775751
theorem B150572521 : Blo 1784093 150572521 := bstep (se 2 (by rfl) ⟨56464695, by rfl⟩ : syracuseStep 150572521 = 112929391) B112929391
theorem B9039599 : Blo 1784093 9039599 := bstep (se 1 (by rfl) ⟨6779699, by rfl⟩ : syracuseStep 9039599 = 13559399) B13559399
theorem B10170143 : Blo 1784093 10170143 := bstep (se 1 (by rfl) ⟨7627607, by rfl⟩ : syracuseStep 10170143 = 15255215) B15255215
theorem B3010729 : Blo 1784093 3010729 := bstep (se 2 (by rfl) ⟨1129023, by rfl⟩ : syracuseStep 3010729 = 2258047) B2258047
theorem B10162853 : Blo 1784093 10162853 := bstep (se 4 (by rfl) ⟨952767, by rfl⟩ : syracuseStep 10162853 = 1905535) B1905535
theorem B312890041 : Blo 1784093 312890041 := bstep (se 2 (by rfl) ⟨117333765, by rfl⟩ : syracuseStep 312890041 = 234667531) B234667531
theorem B6026075 : Blo 1784093 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B4518767 : Blo 1784093 4518767 := bstep (se 1 (by rfl) ⟨3389075, by rfl⟩ : syracuseStep 4518767 = 6778151) B6778151
theorem B3814265 : Blo 1784093 3814265 := bstep (se 2 (by rfl) ⟨1430349, by rfl⟩ : syracuseStep 3814265 = 2860699) B2860699
theorem B5085983 : Blo 1784093 5085983 := bstep (se 1 (by rfl) ⟨3814487, by rfl⟩ : syracuseStep 5085983 = 7628975) B7628975
theorem B2676191 : Blo 1784093 2676191 := bstep (se 1 (by rfl) ⟨2007143, by rfl⟩ : syracuseStep 2676191 = 4014287) B4014287
theorem B4519415 : Blo 1784093 4519415 := bstep (se 1 (by rfl) ⟨3389561, by rfl⟩ : syracuseStep 4519415 = 6779123) B6779123
theorem B11433545 : Blo 1784093 11433545 := bstep (se 2 (by rfl) ⟨4287579, by rfl⟩ : syracuseStep 11433545 = 8575159) B8575159
theorem B6780611 : Blo 1784093 6780611 := bstep (se 1 (by rfl) ⟨5085458, by rfl⟩ : syracuseStep 6780611 = 10170917) B10170917
theorem B2676431 : Blo 1784093 2676431 := bstep (se 1 (by rfl) ⟨2007323, by rfl⟩ : syracuseStep 2676431 = 4014647) B4014647
theorem B6027047 : Blo 1784093 6027047 := bstep (se 1 (by rfl) ⟨4520285, by rfl⟩ : syracuseStep 6027047 = 9040571) B9040571
theorem B130307885 : Blo 1784093 130307885 := bstep (se 3 (by rfl) ⟨24432728, by rfl⟩ : syracuseStep 130307885 = 48865457) B48865457
theorem B2676671 : Blo 1784093 2676671 := bstep (se 1 (by rfl) ⟨2007503, by rfl⟩ : syracuseStep 2676671 = 4015007) B4015007
theorem B11434031 : Blo 1784093 11434031 := bstep (se 1 (by rfl) ⟨8575523, by rfl⟩ : syracuseStep 11434031 = 17151047) B17151047
theorem B28948751 : Blo 1784093 28948751 := bstep (se 1 (by rfl) ⟨21711563, by rfl⟩ : syracuseStep 28948751 = 43423127) B43423127
theorem B3389759 : Blo 1784093 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B1784191 : Blo 1784093 1784191 := bstep (se 1 (by rfl) ⟨1338143, by rfl⟩ : syracuseStep 1784191 = 2676287) B2676287
theorem B1784431 : Blo 1784093 1784431 := bstep (se 1 (by rfl) ⟨1338323, by rfl⟩ : syracuseStep 1784431 = 2676647) B2676647
theorem B1784487 : Blo 1784093 1784487 := bstep (se 1 (by rfl) ⟨1338365, by rfl⟩ : syracuseStep 1784487 = 2676731) B2676731
theorem B1784511 : Blo 1784093 1784511 := bstep (se 1 (by rfl) ⟨1338383, by rfl⟩ : syracuseStep 1784511 = 2676767) B2676767
theorem B1784527 : Blo 1784093 1784527 := bstep (se 1 (by rfl) ⟨1338395, by rfl⟩ : syracuseStep 1784527 = 2676791) B2676791
theorem B4520681 : Blo 1784093 4520681 := bstep (se 2 (by rfl) ⟨1695255, by rfl⟩ : syracuseStep 4520681 = 3390511) B3390511
theorem B1784571 : Blo 1784093 1784571 := bstep (se 1 (by rfl) ⟨1338428, by rfl⟩ : syracuseStep 1784571 = 2676857) B2676857
theorem B4520711 : Blo 1784093 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B4520731 : Blo 1784093 4520731 := bstep (se 1 (by rfl) ⟨3390548, by rfl⟩ : syracuseStep 4520731 = 6781097) B6781097
theorem B1784607 : Blo 1784093 1784607 := bstep (se 1 (by rfl) ⟨1338455, by rfl⟩ : syracuseStep 1784607 = 2676911) B2676911
theorem B1784799 : Blo 1784093 1784799 := bstep (se 1 (by rfl) ⟨1338599, by rfl⟩ : syracuseStep 1784799 = 2677199) B2677199
theorem B2677727 : Blo 1784093 2677727 := bstep (se 1 (by rfl) ⟨2008295, by rfl⟩ : syracuseStep 2677727 = 4016591) B4016591
theorem B4406251 : Blo 1784093 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B3218459 : Blo 1784093 3218459 := bstep (se 1 (by rfl) ⟨2413844, by rfl⟩ : syracuseStep 3218459 = 4827689) B4827689
theorem B27475001 : Blo 1784093 27475001 := bstep (se 2 (by rfl) ⟨10303125, by rfl⟩ : syracuseStep 27475001 = 20606251) B20606251
theorem B1784999 : Blo 1784093 1784999 := bstep (se 1 (by rfl) ⟨1338749, by rfl⟩ : syracuseStep 1784999 = 2677499) B2677499
theorem B1785083 : Blo 1784093 1785083 := bstep (se 1 (by rfl) ⟨1338812, by rfl⟩ : syracuseStep 1785083 = 2677625) B2677625
theorem B1785087 : Blo 1784093 1785087 := bstep (se 1 (by rfl) ⟨1338815, by rfl⟩ : syracuseStep 1785087 = 2677631) B2677631
theorem B3013895 : Blo 1784093 3013895 := bstep (se 1 (by rfl) ⟨2260421, by rfl⟩ : syracuseStep 3013895 = 4520843) B4520843
theorem B3390761 : Blo 1784093 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B2678375 : Blo 1784093 2678375 := bstep (se 1 (by rfl) ⟨2008781, by rfl⟩ : syracuseStep 2678375 = 4017563) B4017563
theorem B66158365 : Blo 1784093 66158365 := bstep (se 3 (by rfl) ⟨12404693, by rfl⟩ : syracuseStep 66158365 = 24809387) B24809387
theorem B1785691 : Blo 1784093 1785691 := bstep (se 1 (by rfl) ⟨1339268, by rfl⟩ : syracuseStep 1785691 = 2678537) B2678537
theorem B4014305 : Blo 1784093 4014305 := bstep (se 2 (by rfl) ⟨1505364, by rfl⟩ : syracuseStep 4014305 = 3010729) B3010729
theorem B27492695 : Blo 1784093 27492695 := bstep (se 1 (by rfl) ⟨20619521, by rfl⟩ : syracuseStep 27492695 = 41239043) B41239043
theorem B6775235 : Blo 1784093 6775235 := bstep (se 1 (by rfl) ⟨5081426, by rfl⟩ : syracuseStep 6775235 = 10162853) B10162853
theorem B12870377 : Blo 1784093 12870377 := bstep (se 2 (by rfl) ⟨4826391, by rfl⟩ : syracuseStep 12870377 = 9652783) B9652783
theorem B6022025 : Blo 1784093 6022025 := bstep (se 2 (by rfl) ⟨2258259, by rfl⟩ : syracuseStep 6022025 = 4516519) B4516519
theorem B417186721 : Blo 1784093 417186721 := bstep (se 2 (by rfl) ⟨156445020, by rfl⟩ : syracuseStep 417186721 = 312890041) B312890041
theorem B5875001 : Blo 1784093 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B109970921 : Blo 1784093 109970921 := bstep (se 2 (by rfl) ⟨41239095, by rfl⟩ : syracuseStep 109970921 = 82478191) B82478191
theorem B6022889 : Blo 1784093 6022889 := bstep (se 2 (by rfl) ⟨2258583, by rfl⟩ : syracuseStep 6022889 = 4517167) B4517167
theorem B2009263 : Blo 1784093 2009263 := bstep (se 1 (by rfl) ⟨1506947, by rfl⟩ : syracuseStep 2009263 = 3013895) B3013895
theorem B439757585 : Blo 1784093 439757585 := bstep (se 2 (by rfl) ⟨164909094, by rfl⟩ : syracuseStep 439757585 = 329818189) B329818189
theorem B4017383 : Blo 1784093 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B2542843 : Blo 1784093 2542843 := bstep (se 1 (by rfl) ⟨1907132, by rfl⟩ : syracuseStep 2542843 = 3814265) B3814265
theorem B10169711 : Blo 1784093 10169711 := bstep (se 1 (by rfl) ⟨7627283, by rfl⟩ : syracuseStep 10169711 = 15254567) B15254567
theorem B7622363 : Blo 1784093 7622363 := bstep (se 1 (by rfl) ⟨5716772, by rfl⟩ : syracuseStep 7622363 = 11433545) B11433545
theorem B4018031 : Blo 1784093 4018031 := bstep (se 1 (by rfl) ⟨3013523, by rfl⟩ : syracuseStep 4018031 = 6027047) B6027047
theorem B86871923 : Blo 1784093 86871923 := bstep (se 1 (by rfl) ⟨65153942, by rfl⟩ : syracuseStep 86871923 = 130307885) B130307885
theorem B128790433 : Blo 1784093 128790433 := bstep (se 2 (by rfl) ⟨48296412, by rfl⟩ : syracuseStep 128790433 = 96592825) B96592825
theorem B6778835 : Blo 1784093 6778835 := bstep (se 1 (by rfl) ⟨5084126, by rfl⟩ : syracuseStep 6778835 = 10168253) B10168253
theorem B7622687 : Blo 1784093 7622687 := bstep (se 1 (by rfl) ⟨5717015, by rfl⟩ : syracuseStep 7622687 = 11434031) B11434031
theorem B23507167 : Blo 1784093 23507167 := bstep (se 1 (by rfl) ⟨17630375, by rfl⟩ : syracuseStep 23507167 = 35260751) B35260751
theorem B19558751 : Blo 1784093 19558751 := bstep (se 1 (by rfl) ⟨14669063, by rfl⟩ : syracuseStep 19558751 = 29338127) B29338127
theorem B8581943 : Blo 1784093 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B3388385 : Blo 1784093 3388385 := bstep (se 2 (by rfl) ⟨1270644, by rfl⟩ : syracuseStep 3388385 = 2541289) B2541289
theorem B6026399 : Blo 1784093 6026399 := bstep (se 1 (by rfl) ⟨4519799, by rfl⟩ : syracuseStep 6026399 = 9039599) B9039599
theorem B6780095 : Blo 1784093 6780095 := bstep (se 1 (by rfl) ⟨5085071, by rfl⟩ : syracuseStep 6780095 = 10170143) B10170143
theorem B2676251 : Blo 1784093 2676251 := bstep (se 1 (by rfl) ⟨2007188, by rfl⟩ : syracuseStep 2676251 = 4014377) B4014377
theorem B34330229 : Blo 1784093 34330229 := bstep (se 5 (by rfl) ⟨1609229, by rfl⟩ : syracuseStep 34330229 = 3218459) B3218459
theorem B3012511 : Blo 1784093 3012511 := bstep (se 1 (by rfl) ⟨2259383, by rfl⟩ : syracuseStep 3012511 = 4518767) B4518767
theorem B9042029 : Blo 1784093 9042029 := bstep (se 3 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 9042029 = 3390761) B3390761
theorem B1784127 : Blo 1784093 1784127 := bstep (se 1 (by rfl) ⟨1338095, by rfl⟩ : syracuseStep 1784127 = 2676191) B2676191
theorem B3012943 : Blo 1784093 3012943 := bstep (se 1 (by rfl) ⟨2259707, by rfl⟩ : syracuseStep 3012943 = 4519415) B4519415
theorem B6027641 : Blo 1784093 6027641 := bstep (se 2 (by rfl) ⟨2260365, by rfl⟩ : syracuseStep 6027641 = 4520731) B4520731
theorem B4520407 : Blo 1784093 4520407 := bstep (se 1 (by rfl) ⟨3390305, by rfl⟩ : syracuseStep 4520407 = 6780611) B6780611
theorem B1784287 : Blo 1784093 1784287 := bstep (se 1 (by rfl) ⟨1338215, by rfl⟩ : syracuseStep 1784287 = 2676431) B2676431
theorem B1784447 : Blo 1784093 1784447 := bstep (se 1 (by rfl) ⟨1338335, by rfl⟩ : syracuseStep 1784447 = 2676671) B2676671
theorem B2677403 : Blo 1784093 2677403 := bstep (se 1 (by rfl) ⟨2008052, by rfl⟩ : syracuseStep 2677403 = 4016105) B4016105
theorem B4578017 : Blo 1784093 4578017 := bstep (se 2 (by rfl) ⟨1716756, by rfl⟩ : syracuseStep 4578017 = 3433513) B3433513
theorem B2677487 : Blo 1784093 2677487 := bstep (se 1 (by rfl) ⟨2008115, by rfl⟩ : syracuseStep 2677487 = 4016231) B4016231
theorem B73284425 : Blo 1784093 73284425 := bstep (se 2 (by rfl) ⟨27481659, by rfl⟩ : syracuseStep 73284425 = 54963319) B54963319
theorem B19299167 : Blo 1784093 19299167 := bstep (se 1 (by rfl) ⟨14474375, by rfl⟩ : syracuseStep 19299167 = 28948751) B28948751
theorem B2259839 : Blo 1784093 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B2677871 : Blo 1784093 2677871 := bstep (se 1 (by rfl) ⟨2008403, by rfl⟩ : syracuseStep 2677871 = 4016807) B4016807
theorem B3013787 : Blo 1784093 3013787 := bstep (se 1 (by rfl) ⟨2260340, by rfl⟩ : syracuseStep 3013787 = 4520681) B4520681
theorem B2677919 : Blo 1784093 2677919 := bstep (se 1 (by rfl) ⟨2008439, by rfl⟩ : syracuseStep 2677919 = 4016879) B4016879
theorem B3013807 : Blo 1784093 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B3390655 : Blo 1784093 3390655 := bstep (se 1 (by rfl) ⟨2542991, by rfl⟩ : syracuseStep 3390655 = 5085983) B5085983
theorem B1785151 : Blo 1784093 1785151 := bstep (se 1 (by rfl) ⟨1338863, by rfl⟩ : syracuseStep 1785151 = 2677727) B2677727
theorem B18316667 : Blo 1784093 18316667 := bstep (se 1 (by rfl) ⟨13737500, by rfl⟩ : syracuseStep 18316667 = 27475001) B27475001
theorem B88211153 : Blo 1784093 88211153 := bstep (se 2 (by rfl) ⟨33079182, by rfl⟩ : syracuseStep 88211153 = 66158365) B66158365
theorem B1785583 : Blo 1784093 1785583 := bstep (se 1 (by rfl) ⟨1339187, by rfl⟩ : syracuseStep 1785583 = 2678375) B2678375
theorem B20340557 : Blo 1784093 20340557 := bstep (se 3 (by rfl) ⟨3813854, by rfl⟩ : syracuseStep 20340557 = 7627709) B7627709
theorem B803053445 : Blo 1784093 803053445 := bstep (se 4 (by rfl) ⟨75286260, by rfl⟩ : syracuseStep 803053445 = 150572521) B150572521
theorem B2679017 : Blo 1784093 2679017 := bstep (se 2 (by rfl) ⟨1004631, by rfl⟩ : syracuseStep 2679017 = 2009263) B2009263
theorem B31342889 : Blo 1784093 31342889 := bstep (se 2 (by rfl) ⟨11753583, by rfl⟩ : syracuseStep 31342889 = 23507167) B23507167
theorem B4014683 : Blo 1784093 4014683 := bstep (se 1 (by rfl) ⟨3011012, by rfl⟩ : syracuseStep 4014683 = 6022025) B6022025
theorem B3916667 : Blo 1784093 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B4015259 : Blo 1784093 4015259 := bstep (se 1 (by rfl) ⟨3011444, by rfl⟩ : syracuseStep 4015259 = 6022889) B6022889
theorem B12208045 : Blo 1784093 12208045 := bstep (se 3 (by rfl) ⟨2289008, by rfl⟩ : syracuseStep 12208045 = 4578017) B4578017
theorem B2009191 : Blo 1784093 2009191 := bstep (se 1 (by rfl) ⟨1506893, by rfl⟩ : syracuseStep 2009191 = 3013787) B3013787
theorem B5081575 : Blo 1784093 5081575 := bstep (se 1 (by rfl) ⟨3811181, by rfl⟩ : syracuseStep 5081575 = 7622363) B7622363
theorem B4016681 : Blo 1784093 4016681 := bstep (se 2 (by rfl) ⟨1506255, by rfl⟩ : syracuseStep 4016681 = 3012511) B3012511
theorem B13560371 : Blo 1784093 13560371 := bstep (se 1 (by rfl) ⟨10170278, by rfl⟩ : syracuseStep 13560371 = 20340557) B20340557
theorem B5081791 : Blo 1784093 5081791 := bstep (se 1 (by rfl) ⟨3811343, by rfl⟩ : syracuseStep 5081791 = 7622687) B7622687
theorem B18328463 : Blo 1784093 18328463 := bstep (se 1 (by rfl) ⟨13746347, by rfl⟩ : syracuseStep 18328463 = 27492695) B27492695
theorem B4516823 : Blo 1784093 4516823 := bstep (se 1 (by rfl) ⟨3387617, by rfl⟩ : syracuseStep 4516823 = 6775235) B6775235
theorem B4017257 : Blo 1784093 4017257 := bstep (se 2 (by rfl) ⟨1506471, by rfl⟩ : syracuseStep 4017257 = 3012943) B3012943
theorem B8580251 : Blo 1784093 8580251 := bstep (se 1 (by rfl) ⟨6435188, by rfl⟩ : syracuseStep 8580251 = 12870377) B12870377
theorem B5721295 : Blo 1784093 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B4017599 : Blo 1784093 4017599 := bstep (se 1 (by rfl) ⟨3013199, by rfl⟩ : syracuseStep 4017599 = 6026399) B6026399
theorem B73313947 : Blo 1784093 73313947 := bstep (se 1 (by rfl) ⟨54985460, by rfl⟩ : syracuseStep 73313947 = 109970921) B109970921
theorem B556248961 : Blo 1784093 556248961 := bstep (se 2 (by rfl) ⟨208593360, by rfl⟩ : syracuseStep 556248961 = 417186721) B417186721
theorem B13561829 : Blo 1784093 13561829 := bstep (se 4 (by rfl) ⟨1271421, by rfl⟩ : syracuseStep 13561829 = 2542843) B2542843
theorem B4018409 : Blo 1784093 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B4018427 : Blo 1784093 4018427 := bstep (se 1 (by rfl) ⟨3013820, by rfl⟩ : syracuseStep 4018427 = 6027641) B6027641
theorem B293171723 : Blo 1784093 293171723 := bstep (se 1 (by rfl) ⟨219878792, by rfl⟩ : syracuseStep 293171723 = 439757585) B439757585
theorem B235229741 : Blo 1784093 235229741 := bstep (se 3 (by rfl) ⟨44105576, by rfl⟩ : syracuseStep 235229741 = 88211153) B88211153
theorem B12866111 : Blo 1784093 12866111 := bstep (se 1 (by rfl) ⟨9649583, by rfl⟩ : syracuseStep 12866111 = 19299167) B19299167
theorem B6779807 : Blo 1784093 6779807 := bstep (se 1 (by rfl) ⟨5084855, by rfl⟩ : syracuseStep 6779807 = 10169711) B10169711
theorem B12211111 : Blo 1784093 12211111 := bstep (se 1 (by rfl) ⟨9158333, by rfl⟩ : syracuseStep 12211111 = 18316667) B18316667
theorem B6026237 : Blo 1784093 6026237 := bstep (se 3 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 6026237 = 2259839) B2259839
theorem B2141475853 : Blo 1784093 2141475853 := bstep (se 3 (by rfl) ⟨401526722, by rfl⟩ : syracuseStep 2141475853 = 803053445) B803053445
theorem B57914615 : Blo 1784093 57914615 := bstep (se 1 (by rfl) ⟨43435961, by rfl⟩ : syracuseStep 57914615 = 86871923) B86871923
theorem B4519223 : Blo 1784093 4519223 := bstep (se 1 (by rfl) ⟨3389417, by rfl⟩ : syracuseStep 4519223 = 6778835) B6778835
theorem B2676203 : Blo 1784093 2676203 := bstep (se 1 (by rfl) ⟨2007152, by rfl⟩ : syracuseStep 2676203 = 4014305) B4014305
theorem B6027209 : Blo 1784093 6027209 := bstep (se 2 (by rfl) ⟨2260203, by rfl⟩ : syracuseStep 6027209 = 4520407) B4520407
theorem B2258923 : Blo 1784093 2258923 := bstep (se 1 (by rfl) ⟨1694192, by rfl⟩ : syracuseStep 2258923 = 3388385) B3388385
theorem B4520063 : Blo 1784093 4520063 := bstep (se 1 (by rfl) ⟨3390047, by rfl⟩ : syracuseStep 4520063 = 6780095) B6780095
theorem B52156669 : Blo 1784093 52156669 := bstep (se 3 (by rfl) ⟨9779375, by rfl⟩ : syracuseStep 52156669 = 19558751) B19558751
theorem B1784167 : Blo 1784093 1784167 := bstep (se 1 (by rfl) ⟨1338125, by rfl⟩ : syracuseStep 1784167 = 2676251) B2676251
theorem B22886819 : Blo 1784093 22886819 := bstep (se 1 (by rfl) ⟨17165114, by rfl⟩ : syracuseStep 22886819 = 34330229) B34330229
theorem B6028019 : Blo 1784093 6028019 := bstep (se 1 (by rfl) ⟨4521014, by rfl⟩ : syracuseStep 6028019 = 9042029) B9042029
theorem B4520873 : Blo 1784093 4520873 := bstep (se 2 (by rfl) ⟨1695327, by rfl⟩ : syracuseStep 4520873 = 3390655) B3390655
theorem B1784935 : Blo 1784093 1784935 := bstep (se 1 (by rfl) ⟨1338701, by rfl⟩ : syracuseStep 1784935 = 2677403) B2677403
theorem B1784991 : Blo 1784093 1784991 := bstep (se 1 (by rfl) ⟨1338743, by rfl⟩ : syracuseStep 1784991 = 2677487) B2677487
theorem B48856283 : Blo 1784093 48856283 := bstep (se 1 (by rfl) ⟨36642212, by rfl⟩ : syracuseStep 48856283 = 73284425) B73284425
theorem B1785247 : Blo 1784093 1785247 := bstep (se 1 (by rfl) ⟨1338935, by rfl⟩ : syracuseStep 1785247 = 2677871) B2677871
theorem B1785279 : Blo 1784093 1785279 := bstep (se 1 (by rfl) ⟨1338959, by rfl⟩ : syracuseStep 1785279 = 2677919) B2677919
theorem B2678255 : Blo 1784093 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B171720577 : Blo 1784093 171720577 := bstep (se 2 (by rfl) ⟨64395216, by rfl⟩ : syracuseStep 171720577 = 128790433) B128790433
theorem B2678687 : Blo 1784093 2678687 := bstep (se 1 (by rfl) ⟨2009015, by rfl⟩ : syracuseStep 2678687 = 4018031) B4018031
theorem B2678921 : Blo 1784093 2678921 := bstep (se 2 (by rfl) ⟨1004595, by rfl⟩ : syracuseStep 2678921 = 2009191) B2009191
theorem B2678939 : Blo 1784093 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B1786011 : Blo 1784093 1786011 := bstep (se 1 (by rfl) ⟨1339508, by rfl⟩ : syracuseStep 1786011 = 2679017) B2679017
theorem B2678951 : Blo 1784093 2678951 := bstep (se 1 (by rfl) ⟨2009213, by rfl⟩ : syracuseStep 2678951 = 4018427) B4018427
theorem B69542225 : Blo 1784093 69542225 := bstep (se 2 (by rfl) ⟨26078334, by rfl⟩ : syracuseStep 69542225 = 52156669) B52156669
theorem B156819827 : Blo 1784093 156819827 := bstep (se 1 (by rfl) ⟨117614870, by rfl⟩ : syracuseStep 156819827 = 235229741) B235229741
theorem B8577407 : Blo 1784093 8577407 := bstep (se 1 (by rfl) ⟨6433055, by rfl⟩ : syracuseStep 8577407 = 12866111) B12866111
theorem B6775433 : Blo 1784093 6775433 := bstep (se 2 (by rfl) ⟨2540787, by rfl⟩ : syracuseStep 6775433 = 5081575) B5081575
theorem B38609743 : Blo 1784093 38609743 := bstep (se 1 (by rfl) ⟨28957307, by rfl⟩ : syracuseStep 38609743 = 57914615) B57914615
theorem B6775721 : Blo 1784093 6775721 := bstep (se 2 (by rfl) ⟨2540895, by rfl⟩ : syracuseStep 6775721 = 5081791) B5081791
theorem B7628393 : Blo 1784093 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B5720167 : Blo 1784093 5720167 := bstep (se 1 (by rfl) ⟨4290125, by rfl⟩ : syracuseStep 5720167 = 8580251) B8580251
theorem B741665281 : Blo 1784093 741665281 := bstep (se 2 (by rfl) ⟨278124480, by rfl⟩ : syracuseStep 741665281 = 556248961) B556248961
theorem B228960769 : Blo 1784093 228960769 := bstep (se 2 (by rfl) ⟨85860288, by rfl⟩ : syracuseStep 228960769 = 171720577) B171720577
theorem B195447815 : Blo 1784093 195447815 := bstep (se 1 (by rfl) ⟨146585861, by rfl⟩ : syracuseStep 195447815 = 293171723) B293171723
theorem B4017491 : Blo 1784093 4017491 := bstep (se 1 (by rfl) ⟨3013118, by rfl⟩ : syracuseStep 4017491 = 6026237) B6026237
theorem B16281481 : Blo 1784093 16281481 := bstep (se 2 (by rfl) ⟨6105555, by rfl⟩ : syracuseStep 16281481 = 12211111) B12211111
theorem B4018139 : Blo 1784093 4018139 := bstep (se 1 (by rfl) ⟨3013604, by rfl⟩ : syracuseStep 4018139 = 6027209) B6027209
theorem B2855301137 : Blo 1784093 2855301137 := bstep (se 2 (by rfl) ⟨1070737926, by rfl⟩ : syracuseStep 2855301137 = 2141475853) B2141475853
theorem B15257879 : Blo 1784093 15257879 := bstep (se 1 (by rfl) ⟨11443409, by rfl⟩ : syracuseStep 15257879 = 22886819) B22886819
theorem B9040247 : Blo 1784093 9040247 := bstep (se 1 (by rfl) ⟨6780185, by rfl⟩ : syracuseStep 9040247 = 13560371) B13560371
theorem B4018679 : Blo 1784093 4018679 := bstep (se 1 (by rfl) ⟨3014009, by rfl⟩ : syracuseStep 4018679 = 6028019) B6028019
theorem B12218975 : Blo 1784093 12218975 := bstep (se 1 (by rfl) ⟨9164231, by rfl⟩ : syracuseStep 12218975 = 18328463) B18328463
theorem B3011215 : Blo 1784093 3011215 := bstep (se 1 (by rfl) ⟨2258411, by rfl⟩ : syracuseStep 3011215 = 4516823) B4516823
theorem B97751929 : Blo 1784093 97751929 := bstep (se 2 (by rfl) ⟨36656973, by rfl⟩ : syracuseStep 97751929 = 73313947) B73313947
theorem B3011897 : Blo 1784093 3011897 := bstep (se 2 (by rfl) ⟨1129461, by rfl⟩ : syracuseStep 3011897 = 2258923) B2258923
theorem B9041219 : Blo 1784093 9041219 := bstep (se 1 (by rfl) ⟨6780914, by rfl⟩ : syracuseStep 9041219 = 13561829) B13561829
theorem B20895259 : Blo 1784093 20895259 := bstep (se 1 (by rfl) ⟨15671444, by rfl⟩ : syracuseStep 20895259 = 31342889) B31342889
theorem B2676455 : Blo 1784093 2676455 := bstep (se 1 (by rfl) ⟨2007341, by rfl⟩ : syracuseStep 2676455 = 4014683) B4014683
theorem B2611111 : Blo 1784093 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B4519871 : Blo 1784093 4519871 := bstep (se 1 (by rfl) ⟨3389903, by rfl⟩ : syracuseStep 4519871 = 6779807) B6779807
theorem B2676839 : Blo 1784093 2676839 := bstep (se 1 (by rfl) ⟨2007629, by rfl⟩ : syracuseStep 2676839 = 4015259) B4015259
theorem B3012815 : Blo 1784093 3012815 := bstep (se 1 (by rfl) ⟨2259611, by rfl⟩ : syracuseStep 3012815 = 4519223) B4519223
theorem B1784135 : Blo 1784093 1784135 := bstep (se 1 (by rfl) ⟨1338101, by rfl⟩ : syracuseStep 1784135 = 2676203) B2676203
theorem B3013375 : Blo 1784093 3013375 := bstep (se 1 (by rfl) ⟨2260031, by rfl⟩ : syracuseStep 3013375 = 4520063) B4520063
theorem B2677787 : Blo 1784093 2677787 := bstep (se 1 (by rfl) ⟨2008340, by rfl⟩ : syracuseStep 2677787 = 4016681) B4016681
theorem B3013915 : Blo 1784093 3013915 := bstep (se 1 (by rfl) ⟨2260436, by rfl⟩ : syracuseStep 3013915 = 4520873) B4520873
theorem B2678171 : Blo 1784093 2678171 := bstep (se 1 (by rfl) ⟨2008628, by rfl⟩ : syracuseStep 2678171 = 4017257) B4017257
theorem B32570855 : Blo 1784093 32570855 := bstep (se 1 (by rfl) ⟨24428141, by rfl⟩ : syracuseStep 32570855 = 48856283) B48856283
theorem B2678399 : Blo 1784093 2678399 := bstep (se 1 (by rfl) ⟨2008799, by rfl⟩ : syracuseStep 2678399 = 4017599) B4017599
theorem B1785503 : Blo 1784093 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B16277393 : Blo 1784093 16277393 := bstep (se 2 (by rfl) ⟨6104022, by rfl⟩ : syracuseStep 16277393 = 12208045) B12208045
theorem B1785791 : Blo 1784093 1785791 := bstep (se 1 (by rfl) ⟨1339343, by rfl⟩ : syracuseStep 1785791 = 2678687) B2678687
theorem B1903534091 : Blo 1784093 1903534091 := bstep (se 1 (by rfl) ⟨1427650568, by rfl⟩ : syracuseStep 1903534091 = 2855301137) B2855301137
theorem B1785947 : Blo 1784093 1785947 := bstep (se 1 (by rfl) ⟨1339460, by rfl⟩ : syracuseStep 1785947 = 2678921) B2678921
theorem B1785959 : Blo 1784093 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B1785967 : Blo 1784093 1785967 := bstep (se 1 (by rfl) ⟨1339475, by rfl⟩ : syracuseStep 1785967 = 2678951) B2678951
theorem B7626889 : Blo 1784093 7626889 := bstep (se 2 (by rfl) ⟨2860083, by rfl⟩ : syracuseStep 7626889 = 5720167) B5720167
theorem B104546551 : Blo 1784093 104546551 := bstep (se 1 (by rfl) ⟨78409913, by rfl⟩ : syracuseStep 104546551 = 156819827) B156819827
theorem B5718271 : Blo 1784093 5718271 := bstep (se 1 (by rfl) ⟨4288703, by rfl⟩ : syracuseStep 5718271 = 8577407) B8577407
theorem B2679119 : Blo 1784093 2679119 := bstep (se 1 (by rfl) ⟨2009339, by rfl⟩ : syracuseStep 2679119 = 4018679) B4018679
theorem B4014953 : Blo 1784093 4014953 := bstep (se 2 (by rfl) ⟨1505607, by rfl⟩ : syracuseStep 4014953 = 3011215) B3011215
theorem B2007931 : Blo 1784093 2007931 := bstep (se 1 (by rfl) ⟨1505948, by rfl⟩ : syracuseStep 2007931 = 3011897) B3011897
theorem B51479657 : Blo 1784093 51479657 := bstep (se 2 (by rfl) ⟨19304871, by rfl⟩ : syracuseStep 51479657 = 38609743) B38609743
theorem B130335905 : Blo 1784093 130335905 := bstep (se 2 (by rfl) ⟨48875964, by rfl⟩ : syracuseStep 130335905 = 97751929) B97751929
theorem B2008543 : Blo 1784093 2008543 := bstep (se 1 (by rfl) ⟨1506407, by rfl⟩ : syracuseStep 2008543 = 3012815) B3012815
theorem B46361483 : Blo 1784093 46361483 := bstep (se 1 (by rfl) ⟨34771112, by rfl⟩ : syracuseStep 46361483 = 69542225) B69542225
theorem B8145983 : Blo 1784093 8145983 := bstep (se 1 (by rfl) ⟨6109487, by rfl⟩ : syracuseStep 8145983 = 12218975) B12218975
theorem B4516955 : Blo 1784093 4516955 := bstep (se 1 (by rfl) ⟨3387716, by rfl⟩ : syracuseStep 4516955 = 6775433) B6775433
theorem B4517147 : Blo 1784093 4517147 := bstep (se 1 (by rfl) ⟨3387860, by rfl⟩ : syracuseStep 4517147 = 6775721) B6775721
theorem B4017833 : Blo 1784093 4017833 := bstep (se 2 (by rfl) ⟨1506687, by rfl⟩ : syracuseStep 4017833 = 3013375) B3013375
theorem B4018553 : Blo 1784093 4018553 := bstep (se 2 (by rfl) ⟨1506957, by rfl⟩ : syracuseStep 4018553 = 3013915) B3013915
theorem B130298543 : Blo 1784093 130298543 := bstep (se 1 (by rfl) ⟨97723907, by rfl⟩ : syracuseStep 130298543 = 195447815) B195447815
theorem B21713903 : Blo 1784093 21713903 := bstep (se 1 (by rfl) ⟨16285427, by rfl⟩ : syracuseStep 21713903 = 32570855) B32570855
theorem B43406381 : Blo 1784093 43406381 := bstep (se 3 (by rfl) ⟨8138696, by rfl⟩ : syracuseStep 43406381 = 16277393) B16277393
theorem B10171919 : Blo 1784093 10171919 := bstep (se 1 (by rfl) ⟨7628939, by rfl⟩ : syracuseStep 10171919 = 15257879) B15257879
theorem B6026831 : Blo 1784093 6026831 := bstep (se 1 (by rfl) ⟨4520123, by rfl⟩ : syracuseStep 6026831 = 9040247) B9040247
theorem B988887041 : Blo 1784093 988887041 := bstep (se 2 (by rfl) ⟨370832640, by rfl⟩ : syracuseStep 988887041 = 741665281) B741665281
theorem B305281025 : Blo 1784093 305281025 := bstep (se 2 (by rfl) ⟨114480384, by rfl⟩ : syracuseStep 305281025 = 228960769) B228960769
theorem B6027479 : Blo 1784093 6027479 := bstep (se 1 (by rfl) ⟨4520609, by rfl⟩ : syracuseStep 6027479 = 9041219) B9041219
theorem B5085595 : Blo 1784093 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B1784303 : Blo 1784093 1784303 := bstep (se 1 (by rfl) ⟨1338227, by rfl⟩ : syracuseStep 1784303 = 2676455) B2676455
theorem B3013247 : Blo 1784093 3013247 := bstep (se 1 (by rfl) ⟨2259935, by rfl⟩ : syracuseStep 3013247 = 4519871) B4519871
theorem B1784559 : Blo 1784093 1784559 := bstep (se 1 (by rfl) ⟨1338419, by rfl⟩ : syracuseStep 1784559 = 2676839) B2676839
theorem B1785191 : Blo 1784093 1785191 := bstep (se 1 (by rfl) ⟨1338893, by rfl⟩ : syracuseStep 1785191 = 2677787) B2677787
theorem B27860345 : Blo 1784093 27860345 := bstep (se 2 (by rfl) ⟨10447629, by rfl⟩ : syracuseStep 27860345 = 20895259) B20895259
theorem B2678327 : Blo 1784093 2678327 := bstep (se 1 (by rfl) ⟨2008745, by rfl⟩ : syracuseStep 2678327 = 4017491) B4017491
theorem B1785447 : Blo 1784093 1785447 := bstep (se 1 (by rfl) ⟨1339085, by rfl⟩ : syracuseStep 1785447 = 2678171) B2678171
theorem B1785599 : Blo 1784093 1785599 := bstep (se 1 (by rfl) ⟨1339199, by rfl⟩ : syracuseStep 1785599 = 2678399) B2678399
theorem B21708641 : Blo 1784093 21708641 := bstep (se 2 (by rfl) ⟨8140740, by rfl⟩ : syracuseStep 21708641 = 16281481) B16281481
theorem B3481481 : Blo 1784093 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B2678759 : Blo 1784093 2678759 := bstep (se 1 (by rfl) ⟨2009069, by rfl⟩ : syracuseStep 2678759 = 4018139) B4018139
theorem B1269022727 : Blo 1784093 1269022727 := bstep (se 1 (by rfl) ⟨951767045, by rfl⟩ : syracuseStep 1269022727 = 1903534091) B1903534091
theorem B1786079 : Blo 1784093 1786079 := bstep (se 1 (by rfl) ⟨1339559, by rfl⟩ : syracuseStep 1786079 = 2679119) B2679119
theorem B2679035 : Blo 1784093 2679035 := bstep (se 1 (by rfl) ⟨2009276, by rfl⟩ : syracuseStep 2679035 = 4018553) B4018553
theorem B139395401 : Blo 1784093 139395401 := bstep (se 2 (by rfl) ⟨52273275, by rfl⟩ : syracuseStep 139395401 = 104546551) B104546551
theorem B347562413 : Blo 1784093 347562413 := bstep (se 3 (by rfl) ⟨65167952, by rfl⟩ : syracuseStep 347562413 = 130335905) B130335905
theorem B14475935 : Blo 1784093 14475935 := bstep (se 1 (by rfl) ⟨10856951, by rfl⟩ : syracuseStep 14475935 = 21713903) B21713903
theorem B2008831 : Blo 1784093 2008831 := bstep (se 1 (by rfl) ⟨1506623, by rfl⟩ : syracuseStep 2008831 = 3013247) B3013247
theorem B18573563 : Blo 1784093 18573563 := bstep (se 1 (by rfl) ⟨13930172, by rfl⟩ : syracuseStep 18573563 = 27860345) B27860345
theorem B9283949 : Blo 1784093 9283949 := bstep (se 3 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 9283949 = 3481481) B3481481
theorem B10169185 : Blo 1784093 10169185 := bstep (se 2 (by rfl) ⟨3813444, by rfl⟩ : syracuseStep 10169185 = 7626889) B7626889
theorem B28937587 : Blo 1784093 28937587 := bstep (se 1 (by rfl) ⟨21703190, by rfl⟩ : syracuseStep 28937587 = 43406381) B43406381
theorem B34319771 : Blo 1784093 34319771 := bstep (se 1 (by rfl) ⟨25739828, by rfl⟩ : syracuseStep 34319771 = 51479657) B51479657
theorem B4017887 : Blo 1784093 4017887 := bstep (se 1 (by rfl) ⟨3013415, by rfl⟩ : syracuseStep 4017887 = 6026831) B6026831
theorem B4018319 : Blo 1784093 4018319 := bstep (se 1 (by rfl) ⟨3013739, by rfl⟩ : syracuseStep 4018319 = 6027479) B6027479
theorem B3011303 : Blo 1784093 3011303 := bstep (se 1 (by rfl) ⟨2258477, by rfl⟩ : syracuseStep 3011303 = 4516955) B4516955
theorem B3011431 : Blo 1784093 3011431 := bstep (se 1 (by rfl) ⟨2258573, by rfl⟩ : syracuseStep 3011431 = 4517147) B4517147
theorem B14472427 : Blo 1784093 14472427 := bstep (se 1 (by rfl) ⟨10854320, by rfl⟩ : syracuseStep 14472427 = 21708641) B21708641
theorem B7624361 : Blo 1784093 7624361 := bstep (se 2 (by rfl) ⟨2859135, by rfl⟩ : syracuseStep 7624361 = 5718271) B5718271
theorem B86865695 : Blo 1784093 86865695 := bstep (se 1 (by rfl) ⟨65149271, by rfl⟩ : syracuseStep 86865695 = 130298543) B130298543
theorem B6780793 : Blo 1784093 6780793 := bstep (se 2 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 6780793 = 5085595) B5085595
theorem B2676635 : Blo 1784093 2676635 := bstep (se 1 (by rfl) ⟨2007476, by rfl⟩ : syracuseStep 2676635 = 4014953) B4014953
theorem B6781279 : Blo 1784093 6781279 := bstep (se 1 (by rfl) ⟨5085959, by rfl⟩ : syracuseStep 6781279 = 10171919) B10171919
theorem B2677241 : Blo 1784093 2677241 := bstep (se 2 (by rfl) ⟨1003965, by rfl⟩ : syracuseStep 2677241 = 2007931) B2007931
theorem B659258027 : Blo 1784093 659258027 := bstep (se 1 (by rfl) ⟨494443520, by rfl⟩ : syracuseStep 659258027 = 988887041) B988887041
theorem B203520683 : Blo 1784093 203520683 := bstep (se 1 (by rfl) ⟨152640512, by rfl⟩ : syracuseStep 203520683 = 305281025) B305281025
theorem B30907655 : Blo 1784093 30907655 := bstep (se 1 (by rfl) ⟨23180741, by rfl⟩ : syracuseStep 30907655 = 46361483) B46361483
theorem B2678057 : Blo 1784093 2678057 := bstep (se 2 (by rfl) ⟨1004271, by rfl⟩ : syracuseStep 2678057 = 2008543) B2008543
theorem B5430655 : Blo 1784093 5430655 := bstep (se 1 (by rfl) ⟨4072991, by rfl⟩ : syracuseStep 5430655 = 8145983) B8145983
theorem B1785551 : Blo 1784093 1785551 := bstep (se 1 (by rfl) ⟨1339163, by rfl⟩ : syracuseStep 1785551 = 2678327) B2678327
theorem B2678555 : Blo 1784093 2678555 := bstep (se 1 (by rfl) ⟨2008916, by rfl⟩ : syracuseStep 2678555 = 4017833) B4017833
theorem B1785839 : Blo 1784093 1785839 := bstep (se 1 (by rfl) ⟨1339379, by rfl⟩ : syracuseStep 1785839 = 2678759) B2678759
theorem B2678879 : Blo 1784093 2678879 := bstep (se 1 (by rfl) ⟨2009159, by rfl⟩ : syracuseStep 2678879 = 4018319) B4018319
theorem B1786023 : Blo 1784093 1786023 := bstep (se 1 (by rfl) ⟨1339517, by rfl⟩ : syracuseStep 1786023 = 2679035) B2679035
theorem B92930267 : Blo 1784093 92930267 := bstep (se 1 (by rfl) ⟨69697700, by rfl⟩ : syracuseStep 92930267 = 139395401) B139395401
theorem B9650623 : Blo 1784093 9650623 := bstep (se 1 (by rfl) ⟨7237967, by rfl⟩ : syracuseStep 9650623 = 14475935) B14475935
theorem B2007535 : Blo 1784093 2007535 := bstep (se 1 (by rfl) ⟨1505651, by rfl⟩ : syracuseStep 2007535 = 3011303) B3011303
theorem B13558913 : Blo 1784093 13558913 := bstep (se 2 (by rfl) ⟨5084592, by rfl⟩ : syracuseStep 13558913 = 10169185) B10169185
theorem B4015241 : Blo 1784093 4015241 := bstep (se 2 (by rfl) ⟨1505715, by rfl⟩ : syracuseStep 4015241 = 3011431) B3011431
theorem B57910463 : Blo 1784093 57910463 := bstep (se 1 (by rfl) ⟨43432847, by rfl⟩ : syracuseStep 57910463 = 86865695) B86865695
theorem B20605103 : Blo 1784093 20605103 := bstep (se 1 (by rfl) ⟨15453827, by rfl⟩ : syracuseStep 20605103 = 30907655) B30907655
theorem B846015151 : Blo 1784093 846015151 := bstep (se 1 (by rfl) ⟨634511363, by rfl⟩ : syracuseStep 846015151 = 1269022727) B1269022727
theorem B5082907 : Blo 1784093 5082907 := bstep (se 1 (by rfl) ⟨3812180, by rfl⟩ : syracuseStep 5082907 = 7624361) B7624361
theorem B12382375 : Blo 1784093 12382375 := bstep (se 1 (by rfl) ⟨9286781, by rfl⟩ : syracuseStep 12382375 = 18573563) B18573563
theorem B6189299 : Blo 1784093 6189299 := bstep (se 1 (by rfl) ⟨4641974, by rfl⟩ : syracuseStep 6189299 = 9283949) B9283949
theorem B19296569 : Blo 1784093 19296569 := bstep (se 2 (by rfl) ⟨7236213, by rfl⟩ : syracuseStep 19296569 = 14472427) B14472427
theorem B439505351 : Blo 1784093 439505351 := bstep (se 1 (by rfl) ⟨329629013, by rfl⟩ : syracuseStep 439505351 = 659258027) B659258027
theorem B135680455 : Blo 1784093 135680455 := bstep (se 1 (by rfl) ⟨101760341, by rfl⟩ : syracuseStep 135680455 = 203520683) B203520683
theorem B9041057 : Blo 1784093 9041057 := bstep (se 2 (by rfl) ⟨3390396, by rfl⟩ : syracuseStep 9041057 = 6780793) B6780793
theorem B231708275 : Blo 1784093 231708275 := bstep (se 1 (by rfl) ⟨173781206, by rfl⟩ : syracuseStep 231708275 = 347562413) B347562413
theorem B9041705 : Blo 1784093 9041705 := bstep (se 2 (by rfl) ⟨3390639, by rfl⟩ : syracuseStep 9041705 = 6781279) B6781279
theorem B1784423 : Blo 1784093 1784423 := bstep (se 1 (by rfl) ⟨1338317, by rfl⟩ : syracuseStep 1784423 = 2676635) B2676635
theorem B1784827 : Blo 1784093 1784827 := bstep (se 1 (by rfl) ⟨1338620, by rfl⟩ : syracuseStep 1784827 = 2677241) B2677241
theorem B38583449 : Blo 1784093 38583449 := bstep (se 2 (by rfl) ⟨14468793, by rfl⟩ : syracuseStep 38583449 = 28937587) B28937587
theorem B7240873 : Blo 1784093 7240873 := bstep (se 2 (by rfl) ⟨2715327, by rfl⟩ : syracuseStep 7240873 = 5430655) B5430655
theorem B1785371 : Blo 1784093 1785371 := bstep (se 1 (by rfl) ⟨1339028, by rfl⟩ : syracuseStep 1785371 = 2678057) B2678057
theorem B22879847 : Blo 1784093 22879847 := bstep (se 1 (by rfl) ⟨17159885, by rfl⟩ : syracuseStep 22879847 = 34319771) B34319771
theorem B2678441 : Blo 1784093 2678441 := bstep (se 2 (by rfl) ⟨1004415, by rfl⟩ : syracuseStep 2678441 = 2008831) B2008831
theorem B2678591 : Blo 1784093 2678591 := bstep (se 1 (by rfl) ⟨2008943, by rfl⟩ : syracuseStep 2678591 = 4017887) B4017887
theorem B1785703 : Blo 1784093 1785703 := bstep (se 1 (by rfl) ⟨1339277, by rfl⟩ : syracuseStep 1785703 = 2678555) B2678555
theorem B1785919 : Blo 1784093 1785919 := bstep (se 1 (by rfl) ⟨1339439, by rfl⟩ : syracuseStep 1785919 = 2678879) B2678879
theorem B293003567 : Blo 1784093 293003567 := bstep (se 1 (by rfl) ⟨219752675, by rfl⟩ : syracuseStep 293003567 = 439505351) B439505351
theorem B6777209 : Blo 1784093 6777209 := bstep (se 2 (by rfl) ⟨2541453, by rfl⟩ : syracuseStep 6777209 = 5082907) B5082907
theorem B12864379 : Blo 1784093 12864379 := bstep (se 1 (by rfl) ⟨9648284, by rfl⟩ : syracuseStep 12864379 = 19296569) B19296569
theorem B16509833 : Blo 1784093 16509833 := bstep (se 2 (by rfl) ⟨6191187, by rfl⟩ : syracuseStep 16509833 = 12382375) B12382375
theorem B180907273 : Blo 1784093 180907273 := bstep (se 2 (by rfl) ⟨67840227, by rfl⟩ : syracuseStep 180907273 = 135680455) B135680455
theorem B9039275 : Blo 1784093 9039275 := bstep (se 1 (by rfl) ⟨6779456, by rfl⟩ : syracuseStep 9039275 = 13558913) B13558913
theorem B154472183 : Blo 1784093 154472183 := bstep (se 1 (by rfl) ⟨115854137, by rfl⟩ : syracuseStep 154472183 = 231708275) B231708275
theorem B9654497 : Blo 1784093 9654497 := bstep (se 2 (by rfl) ⟨3620436, by rfl⟩ : syracuseStep 9654497 = 7240873) B7240873
theorem B61953511 : Blo 1784093 61953511 := bstep (se 1 (by rfl) ⟨46465133, by rfl⟩ : syracuseStep 61953511 = 92930267) B92930267
theorem B4126199 : Blo 1784093 4126199 := bstep (se 1 (by rfl) ⟨3094649, by rfl⟩ : syracuseStep 4126199 = 6189299) B6189299
theorem B12867497 : Blo 1784093 12867497 := bstep (se 2 (by rfl) ⟨4825311, by rfl⟩ : syracuseStep 12867497 = 9650623) B9650623
theorem B2676713 : Blo 1784093 2676713 := bstep (se 2 (by rfl) ⟨1003767, by rfl⟩ : syracuseStep 2676713 = 2007535) B2007535
theorem B2676827 : Blo 1784093 2676827 := bstep (se 1 (by rfl) ⟨2007620, by rfl⟩ : syracuseStep 2676827 = 4015241) B4015241
theorem B6027371 : Blo 1784093 6027371 := bstep (se 1 (by rfl) ⟨4520528, by rfl⟩ : syracuseStep 6027371 = 9041057) B9041057
theorem B38606975 : Blo 1784093 38606975 := bstep (se 1 (by rfl) ⟨28955231, by rfl⟩ : syracuseStep 38606975 = 57910463) B57910463
theorem B1128020201 : Blo 1784093 1128020201 := bstep (se 2 (by rfl) ⟨423007575, by rfl⟩ : syracuseStep 1128020201 = 846015151) B846015151
theorem B6027803 : Blo 1784093 6027803 := bstep (se 1 (by rfl) ⟨4520852, by rfl⟩ : syracuseStep 6027803 = 9041705) B9041705
theorem B13736735 : Blo 1784093 13736735 := bstep (se 1 (by rfl) ⟨10302551, by rfl⟩ : syracuseStep 13736735 = 20605103) B20605103
theorem B25722299 : Blo 1784093 25722299 := bstep (se 1 (by rfl) ⟨19291724, by rfl⟩ : syracuseStep 25722299 = 38583449) B38583449
theorem B15253231 : Blo 1784093 15253231 := bstep (se 1 (by rfl) ⟨11439923, by rfl⟩ : syracuseStep 15253231 = 22879847) B22879847
theorem B1785627 : Blo 1784093 1785627 := bstep (se 1 (by rfl) ⟨1339220, by rfl⟩ : syracuseStep 1785627 = 2678441) B2678441
theorem B1785727 : Blo 1784093 1785727 := bstep (se 1 (by rfl) ⟨1339295, by rfl⟩ : syracuseStep 1785727 = 2678591) B2678591
theorem B8578331 : Blo 1784093 8578331 := bstep (se 1 (by rfl) ⟨6433748, by rfl⟩ : syracuseStep 8578331 = 12867497) B12867497
theorem B17148199 : Blo 1784093 17148199 := bstep (se 1 (by rfl) ⟨12861149, by rfl⟩ : syracuseStep 17148199 = 25722299) B25722299
theorem B4018247 : Blo 1784093 4018247 := bstep (se 1 (by rfl) ⟨3013685, by rfl⟩ : syracuseStep 4018247 = 6027371) B6027371
theorem B752013467 : Blo 1784093 752013467 := bstep (se 1 (by rfl) ⟨564010100, by rfl⟩ : syracuseStep 752013467 = 1128020201) B1128020201
theorem B4518139 : Blo 1784093 4518139 := bstep (se 1 (by rfl) ⟨3388604, by rfl⟩ : syracuseStep 4518139 = 6777209) B6777209
theorem B241209697 : Blo 1784093 241209697 := bstep (se 2 (by rfl) ⟨90453636, by rfl⟩ : syracuseStep 241209697 = 180907273) B180907273
theorem B4018535 : Blo 1784093 4018535 := bstep (se 1 (by rfl) ⟨3013901, by rfl⟩ : syracuseStep 4018535 = 6027803) B6027803
theorem B11006555 : Blo 1784093 11006555 := bstep (se 1 (by rfl) ⟨8254916, by rfl⟩ : syracuseStep 11006555 = 16509833) B16509833
theorem B82604681 : Blo 1784093 82604681 := bstep (se 2 (by rfl) ⟨30976755, by rfl⟩ : syracuseStep 82604681 = 61953511) B61953511
theorem B6026183 : Blo 1784093 6026183 := bstep (se 1 (by rfl) ⟨4519637, by rfl⟩ : syracuseStep 6026183 = 9039275) B9039275
theorem B20337641 : Blo 1784093 20337641 := bstep (se 2 (by rfl) ⟨7626615, by rfl⟩ : syracuseStep 20337641 = 15253231) B15253231
theorem B44012789 : Blo 1784093 44012789 := bstep (se 5 (by rfl) ⟨2063099, by rfl⟩ : syracuseStep 44012789 = 4126199) B4126199
theorem B6436331 : Blo 1784093 6436331 := bstep (se 1 (by rfl) ⟨4827248, by rfl⟩ : syracuseStep 6436331 = 9654497) B9654497
theorem B195335711 : Blo 1784093 195335711 := bstep (se 1 (by rfl) ⟨146501783, by rfl⟩ : syracuseStep 195335711 = 293003567) B293003567
theorem B17152505 : Blo 1784093 17152505 := bstep (se 2 (by rfl) ⟨6432189, by rfl⟩ : syracuseStep 17152505 = 12864379) B12864379
theorem B1784475 : Blo 1784093 1784475 := bstep (se 1 (by rfl) ⟨1338356, by rfl⟩ : syracuseStep 1784475 = 2676713) B2676713
theorem B1784551 : Blo 1784093 1784551 := bstep (se 1 (by rfl) ⟨1338413, by rfl⟩ : syracuseStep 1784551 = 2676827) B2676827
theorem B25737983 : Blo 1784093 25737983 := bstep (se 1 (by rfl) ⟨19303487, by rfl⟩ : syracuseStep 25737983 = 38606975) B38606975
theorem B9157823 : Blo 1784093 9157823 := bstep (se 1 (by rfl) ⟨6868367, by rfl⟩ : syracuseStep 9157823 = 13736735) B13736735
theorem B102981455 : Blo 1784093 102981455 := bstep (se 1 (by rfl) ⟨77236091, by rfl⟩ : syracuseStep 102981455 = 154472183) B154472183
theorem B2678831 : Blo 1784093 2678831 := bstep (se 1 (by rfl) ⟨2009123, by rfl⟩ : syracuseStep 2678831 = 4018247) B4018247
theorem B501342311 : Blo 1784093 501342311 := bstep (se 1 (by rfl) ⟨376006733, by rfl⟩ : syracuseStep 501342311 = 752013467) B752013467
theorem B2679023 : Blo 1784093 2679023 := bstep (se 1 (by rfl) ⟨2009267, by rfl⟩ : syracuseStep 2679023 = 4018535) B4018535
theorem B22864265 : Blo 1784093 22864265 := bstep (se 2 (by rfl) ⟨8574099, by rfl⟩ : syracuseStep 22864265 = 17148199) B17148199
theorem B13558427 : Blo 1784093 13558427 := bstep (se 1 (by rfl) ⟨10168820, by rfl⟩ : syracuseStep 13558427 = 20337641) B20337641
theorem B5718887 : Blo 1784093 5718887 := bstep (se 1 (by rfl) ⟨4289165, by rfl⟩ : syracuseStep 5718887 = 8578331) B8578331
theorem B6105215 : Blo 1784093 6105215 := bstep (se 1 (by rfl) ⟨4578911, by rfl⟩ : syracuseStep 6105215 = 9157823) B9157823
theorem B6024185 : Blo 1784093 6024185 := bstep (se 2 (by rfl) ⟨2259069, by rfl⟩ : syracuseStep 6024185 = 4518139) B4518139
theorem B55069787 : Blo 1784093 55069787 := bstep (se 1 (by rfl) ⟨41302340, by rfl⟩ : syracuseStep 55069787 = 82604681) B82604681
theorem B321612929 : Blo 1784093 321612929 := bstep (se 2 (by rfl) ⟨120604848, by rfl⟩ : syracuseStep 321612929 = 241209697) B241209697
theorem B4017455 : Blo 1784093 4017455 := bstep (se 1 (by rfl) ⟨3013091, by rfl⟩ : syracuseStep 4017455 = 6026183) B6026183
theorem B117403253 : Blo 1784093 117403253 := bstep (se 5 (by rfl) ⟨5503277, by rfl⟩ : syracuseStep 117403253 = 11006555) B11006555
theorem B130223807 : Blo 1784093 130223807 := bstep (se 1 (by rfl) ⟨97667855, by rfl⟩ : syracuseStep 130223807 = 195335711) B195335711
theorem B17158655 : Blo 1784093 17158655 := bstep (se 1 (by rfl) ⟨12868991, by rfl⟩ : syracuseStep 17158655 = 25737983) B25737983
theorem B68654303 : Blo 1784093 68654303 := bstep (se 1 (by rfl) ⟨51490727, by rfl⟩ : syracuseStep 68654303 = 102981455) B102981455
theorem B29341859 : Blo 1784093 29341859 := bstep (se 1 (by rfl) ⟨22006394, by rfl⟩ : syracuseStep 29341859 = 44012789) B44012789
theorem B4290887 : Blo 1784093 4290887 := bstep (se 1 (by rfl) ⟨3218165, by rfl⟩ : syracuseStep 4290887 = 6436331) B6436331
theorem B11435003 : Blo 1784093 11435003 := bstep (se 1 (by rfl) ⟨8576252, by rfl⟩ : syracuseStep 11435003 = 17152505) B17152505
theorem B1785887 : Blo 1784093 1785887 := bstep (se 1 (by rfl) ⟨1339415, by rfl⟩ : syracuseStep 1785887 = 2678831) B2678831
theorem B1786015 : Blo 1784093 1786015 := bstep (se 1 (by rfl) ⟨1339511, by rfl⟩ : syracuseStep 1786015 = 2679023) B2679023
theorem B45769535 : Blo 1784093 45769535 := bstep (se 1 (by rfl) ⟨34327151, by rfl⟩ : syracuseStep 45769535 = 68654303) B68654303
theorem B2860591 : Blo 1784093 2860591 := bstep (se 1 (by rfl) ⟨2145443, by rfl⟩ : syracuseStep 2860591 = 4290887) B4290887
theorem B4016123 : Blo 1784093 4016123 := bstep (se 1 (by rfl) ⟨3012092, by rfl⟩ : syracuseStep 4016123 = 6024185) B6024185
theorem B78268835 : Blo 1784093 78268835 := bstep (se 1 (by rfl) ⟨58701626, by rfl⟩ : syracuseStep 78268835 = 117403253) B117403253
theorem B334228207 : Blo 1784093 334228207 := bstep (se 1 (by rfl) ⟨250671155, by rfl⟩ : syracuseStep 334228207 = 501342311) B501342311
theorem B78244957 : Blo 1784093 78244957 := bstep (se 3 (by rfl) ⟨14670929, by rfl⟩ : syracuseStep 78244957 = 29341859) B29341859
theorem B9038951 : Blo 1784093 9038951 := bstep (se 1 (by rfl) ⟨6779213, by rfl⟩ : syracuseStep 9038951 = 13558427) B13558427
theorem B3812591 : Blo 1784093 3812591 := bstep (se 1 (by rfl) ⟨2859443, by rfl⟩ : syracuseStep 3812591 = 5718887) B5718887
theorem B45756413 : Blo 1784093 45756413 := bstep (se 3 (by rfl) ⟨8579327, by rfl⟩ : syracuseStep 45756413 = 17158655) B17158655
theorem B7623335 : Blo 1784093 7623335 := bstep (se 1 (by rfl) ⟨5717501, by rfl⟩ : syracuseStep 7623335 = 11435003) B11435003
theorem B36713191 : Blo 1784093 36713191 := bstep (se 1 (by rfl) ⟨27534893, by rfl⟩ : syracuseStep 36713191 = 55069787) B55069787
theorem B86815871 : Blo 1784093 86815871 := bstep (se 1 (by rfl) ⟨65111903, by rfl⟩ : syracuseStep 86815871 = 130223807) B130223807
theorem B15242843 : Blo 1784093 15242843 := bstep (se 1 (by rfl) ⟨11432132, by rfl⟩ : syracuseStep 15242843 = 22864265) B22864265
theorem B4070143 : Blo 1784093 4070143 := bstep (se 1 (by rfl) ⟨3052607, by rfl⟩ : syracuseStep 4070143 = 6105215) B6105215
theorem B214408619 : Blo 1784093 214408619 := bstep (se 1 (by rfl) ⟨160806464, by rfl⟩ : syracuseStep 214408619 = 321612929) B321612929
theorem B2678303 : Blo 1784093 2678303 := bstep (se 1 (by rfl) ⟨2008727, by rfl⟩ : syracuseStep 2678303 = 4017455) B4017455
theorem B57877247 : Blo 1784093 57877247 := bstep (se 1 (by rfl) ⟨43407935, by rfl⟩ : syracuseStep 57877247 = 86815871) B86815871
theorem B445637609 : Blo 1784093 445637609 := bstep (se 2 (by rfl) ⟨167114103, by rfl⟩ : syracuseStep 445637609 = 334228207) B334228207
theorem B2541727 : Blo 1784093 2541727 := bstep (se 1 (by rfl) ⟨1906295, by rfl⟩ : syracuseStep 2541727 = 3812591) B3812591
theorem B48950921 : Blo 1784093 48950921 := bstep (se 2 (by rfl) ⟨18356595, by rfl⟩ : syracuseStep 48950921 = 36713191) B36713191
theorem B5426857 : Blo 1784093 5426857 := bstep (se 2 (by rfl) ⟨2035071, by rfl⟩ : syracuseStep 5426857 = 4070143) B4070143
theorem B10161895 : Blo 1784093 10161895 := bstep (se 1 (by rfl) ⟨7621421, by rfl⟩ : syracuseStep 10161895 = 15242843) B15242843
theorem B52179223 : Blo 1784093 52179223 := bstep (se 1 (by rfl) ⟨39134417, by rfl⟩ : syracuseStep 52179223 = 78268835) B78268835
theorem B20328893 : Blo 1784093 20328893 := bstep (se 3 (by rfl) ⟨3811667, by rfl⟩ : syracuseStep 20328893 = 7623335) B7623335
theorem B3814121 : Blo 1784093 3814121 := bstep (se 2 (by rfl) ⟨1430295, by rfl⟩ : syracuseStep 3814121 = 2860591) B2860591
theorem B6025967 : Blo 1784093 6025967 := bstep (se 1 (by rfl) ⟨4519475, by rfl⟩ : syracuseStep 6025967 = 9038951) B9038951
theorem B142939079 : Blo 1784093 142939079 := bstep (se 1 (by rfl) ⟨107204309, by rfl⟩ : syracuseStep 142939079 = 214408619) B214408619
theorem B30504275 : Blo 1784093 30504275 := bstep (se 1 (by rfl) ⟨22878206, by rfl⟩ : syracuseStep 30504275 = 45756413) B45756413
theorem B417306437 : Blo 1784093 417306437 := bstep (se 4 (by rfl) ⟨39122478, by rfl⟩ : syracuseStep 417306437 = 78244957) B78244957
theorem B30513023 : Blo 1784093 30513023 := bstep (se 1 (by rfl) ⟨22884767, by rfl⟩ : syracuseStep 30513023 = 45769535) B45769535
theorem B2677415 : Blo 1784093 2677415 := bstep (se 1 (by rfl) ⟨2008061, by rfl⟩ : syracuseStep 2677415 = 4016123) B4016123
theorem B1785535 : Blo 1784093 1785535 := bstep (se 1 (by rfl) ⟨1339151, by rfl⟩ : syracuseStep 1785535 = 2678303) B2678303
theorem B38584831 : Blo 1784093 38584831 := bstep (se 1 (by rfl) ⟨28938623, by rfl⟩ : syracuseStep 38584831 = 57877247) B57877247
theorem B297091739 : Blo 1784093 297091739 := bstep (se 1 (by rfl) ⟨222818804, by rfl⟩ : syracuseStep 297091739 = 445637609) B445637609
theorem B28943237 : Blo 1784093 28943237 := bstep (se 4 (by rfl) ⟨2713428, by rfl⟩ : syracuseStep 28943237 = 5426857) B5426857
theorem B20342015 : Blo 1784093 20342015 := bstep (se 1 (by rfl) ⟨15256511, by rfl⟩ : syracuseStep 20342015 = 30513023) B30513023
theorem B13552595 : Blo 1784093 13552595 := bstep (se 1 (by rfl) ⟨10164446, by rfl⟩ : syracuseStep 13552595 = 20328893) B20328893
theorem B2542747 : Blo 1784093 2542747 := bstep (se 1 (by rfl) ⟨1907060, by rfl⟩ : syracuseStep 2542747 = 3814121) B3814121
theorem B4017311 : Blo 1784093 4017311 := bstep (se 1 (by rfl) ⟨3012983, by rfl⟩ : syracuseStep 4017311 = 6025967) B6025967
theorem B95292719 : Blo 1784093 95292719 := bstep (se 1 (by rfl) ⟨71469539, by rfl⟩ : syracuseStep 95292719 = 142939079) B142939079
theorem B20336183 : Blo 1784093 20336183 := bstep (se 1 (by rfl) ⟨15252137, by rfl⟩ : syracuseStep 20336183 = 30504275) B30504275
theorem B278204291 : Blo 1784093 278204291 := bstep (se 1 (by rfl) ⟨208653218, by rfl⟩ : syracuseStep 278204291 = 417306437) B417306437
theorem B32633947 : Blo 1784093 32633947 := bstep (se 1 (by rfl) ⟨24475460, by rfl⟩ : syracuseStep 32633947 = 48950921) B48950921
theorem B3388969 : Blo 1784093 3388969 := bstep (se 2 (by rfl) ⟨1270863, by rfl⟩ : syracuseStep 3388969 = 2541727) B2541727
theorem B69572297 : Blo 1784093 69572297 := bstep (se 2 (by rfl) ⟨26089611, by rfl⟩ : syracuseStep 69572297 = 52179223) B52179223
theorem B1784943 : Blo 1784093 1784943 := bstep (se 1 (by rfl) ⟨1338707, by rfl⟩ : syracuseStep 1784943 = 2677415) B2677415
theorem B13549193 : Blo 1784093 13549193 := bstep (se 2 (by rfl) ⟨5080947, by rfl⟩ : syracuseStep 13549193 = 10161895) B10161895
theorem B174047717 : Blo 1784093 174047717 := bstep (se 4 (by rfl) ⟨16316973, by rfl⟩ : syracuseStep 174047717 = 32633947) B32633947
theorem B51446441 : Blo 1784093 51446441 := bstep (se 2 (by rfl) ⟨19292415, by rfl⟩ : syracuseStep 51446441 = 38584831) B38584831
theorem B185469527 : Blo 1784093 185469527 := bstep (se 1 (by rfl) ⟨139102145, by rfl⟩ : syracuseStep 185469527 = 278204291) B278204291
theorem B19295491 : Blo 1784093 19295491 := bstep (se 1 (by rfl) ⟨14471618, by rfl⟩ : syracuseStep 19295491 = 28943237) B28943237
theorem B13561343 : Blo 1784093 13561343 := bstep (se 1 (by rfl) ⟨10171007, by rfl⟩ : syracuseStep 13561343 = 20342015) B20342015
theorem B792244637 : Blo 1784093 792244637 := bstep (se 3 (by rfl) ⟨148545869, by rfl⟩ : syracuseStep 792244637 = 297091739) B297091739
theorem B4518625 : Blo 1784093 4518625 := bstep (se 2 (by rfl) ⟨1694484, by rfl⟩ : syracuseStep 4518625 = 3388969) B3388969
theorem B9032795 : Blo 1784093 9032795 := bstep (se 1 (by rfl) ⟨6774596, by rfl⟩ : syracuseStep 9032795 = 13549193) B13549193
theorem B46381531 : Blo 1784093 46381531 := bstep (se 1 (by rfl) ⟨34786148, by rfl⟩ : syracuseStep 46381531 = 69572297) B69572297
theorem B3390329 : Blo 1784093 3390329 := bstep (se 2 (by rfl) ⟨1271373, by rfl⟩ : syracuseStep 3390329 = 2542747) B2542747
theorem B9035063 : Blo 1784093 9035063 := bstep (se 1 (by rfl) ⟨6776297, by rfl⟩ : syracuseStep 9035063 = 13552595) B13552595
theorem B2678207 : Blo 1784093 2678207 := bstep (se 1 (by rfl) ⟨2008655, by rfl⟩ : syracuseStep 2678207 = 4017311) B4017311
theorem B63528479 : Blo 1784093 63528479 := bstep (se 1 (by rfl) ⟨47646359, by rfl⟩ : syracuseStep 63528479 = 95292719) B95292719
theorem B13557455 : Blo 1784093 13557455 := bstep (se 1 (by rfl) ⟨10168091, by rfl⟩ : syracuseStep 13557455 = 20336183) B20336183
theorem B528163091 : Blo 1784093 528163091 := bstep (se 1 (by rfl) ⟨396122318, by rfl⟩ : syracuseStep 528163091 = 792244637) B792244637
theorem B61842041 : Blo 1784093 61842041 := bstep (se 2 (by rfl) ⟨23190765, by rfl⟩ : syracuseStep 61842041 = 46381531) B46381531
theorem B6021863 : Blo 1784093 6021863 := bstep (se 1 (by rfl) ⟨4516397, by rfl⟩ : syracuseStep 6021863 = 9032795) B9032795
theorem B464127245 : Blo 1784093 464127245 := bstep (se 3 (by rfl) ⟨87023858, by rfl⟩ : syracuseStep 464127245 = 174047717) B174047717
theorem B6023375 : Blo 1784093 6023375 := bstep (se 1 (by rfl) ⟨4517531, by rfl⟩ : syracuseStep 6023375 = 9035063) B9035063
theorem B9038303 : Blo 1784093 9038303 := bstep (se 1 (by rfl) ⟨6778727, by rfl⟩ : syracuseStep 9038303 = 13557455) B13557455
theorem B6024833 : Blo 1784093 6024833 := bstep (se 2 (by rfl) ⟨2259312, by rfl⟩ : syracuseStep 6024833 = 4518625) B4518625
theorem B25727321 : Blo 1784093 25727321 := bstep (se 2 (by rfl) ⟨9647745, by rfl⟩ : syracuseStep 25727321 = 19295491) B19295491
theorem B123646351 : Blo 1784093 123646351 := bstep (se 1 (by rfl) ⟨92734763, by rfl⟩ : syracuseStep 123646351 = 185469527) B185469527
theorem B9040895 : Blo 1784093 9040895 := bstep (se 1 (by rfl) ⟨6780671, by rfl⟩ : syracuseStep 9040895 = 13561343) B13561343
theorem B34297627 : Blo 1784093 34297627 := bstep (se 1 (by rfl) ⟨25723220, by rfl⟩ : syracuseStep 34297627 = 51446441) B51446441
theorem B2260219 : Blo 1784093 2260219 := bstep (se 1 (by rfl) ⟨1695164, by rfl⟩ : syracuseStep 2260219 = 3390329) B3390329
theorem B1785471 : Blo 1784093 1785471 := bstep (se 1 (by rfl) ⟨1339103, by rfl⟩ : syracuseStep 1785471 = 2678207) B2678207
theorem B42352319 : Blo 1784093 42352319 := bstep (se 1 (by rfl) ⟨31764239, by rfl⟩ : syracuseStep 42352319 = 63528479) B63528479
theorem B352108727 : Blo 1784093 352108727 := bstep (se 1 (by rfl) ⟨264081545, by rfl⟩ : syracuseStep 352108727 = 528163091) B528163091
theorem B4014575 : Blo 1784093 4014575 := bstep (se 1 (by rfl) ⟨3010931, by rfl⟩ : syracuseStep 4014575 = 6021863) B6021863
theorem B4015583 : Blo 1784093 4015583 := bstep (se 1 (by rfl) ⟨3011687, by rfl⟩ : syracuseStep 4015583 = 6023375) B6023375
theorem B45730169 : Blo 1784093 45730169 := bstep (se 2 (by rfl) ⟨17148813, by rfl⟩ : syracuseStep 45730169 = 34297627) B34297627
theorem B4016555 : Blo 1784093 4016555 := bstep (se 1 (by rfl) ⟨3012416, by rfl⟩ : syracuseStep 4016555 = 6024833) B6024833
theorem B6025535 : Blo 1784093 6025535 := bstep (se 1 (by rfl) ⟨4519151, by rfl⟩ : syracuseStep 6025535 = 9038303) B9038303
theorem B112939517 : Blo 1784093 112939517 := bstep (se 3 (by rfl) ⟨21176159, by rfl⟩ : syracuseStep 112939517 = 42352319) B42352319
theorem B17151547 : Blo 1784093 17151547 := bstep (se 1 (by rfl) ⟨12863660, by rfl⟩ : syracuseStep 17151547 = 25727321) B25727321
theorem B41228027 : Blo 1784093 41228027 := bstep (se 1 (by rfl) ⟨30921020, by rfl⟩ : syracuseStep 41228027 = 61842041) B61842041
theorem B164861801 : Blo 1784093 164861801 := bstep (se 2 (by rfl) ⟨61823175, by rfl⟩ : syracuseStep 164861801 = 123646351) B123646351
theorem B6027263 : Blo 1784093 6027263 := bstep (se 1 (by rfl) ⟨4520447, by rfl⟩ : syracuseStep 6027263 = 9040895) B9040895
theorem B309418163 : Blo 1784093 309418163 := bstep (se 1 (by rfl) ⟨232063622, by rfl⟩ : syracuseStep 309418163 = 464127245) B464127245
theorem B3013625 : Blo 1784093 3013625 := bstep (se 2 (by rfl) ⟨1130109, by rfl⟩ : syracuseStep 3013625 = 2260219) B2260219
theorem B75293011 : Blo 1784093 75293011 := bstep (se 1 (by rfl) ⟨56469758, by rfl⟩ : syracuseStep 75293011 = 112939517) B112939517
theorem B27485351 : Blo 1784093 27485351 := bstep (se 1 (by rfl) ⟨20614013, by rfl⟩ : syracuseStep 27485351 = 41228027) B41228027
theorem B2009083 : Blo 1784093 2009083 := bstep (se 1 (by rfl) ⟨1506812, by rfl⟩ : syracuseStep 2009083 = 3013625) B3013625
theorem B4017023 : Blo 1784093 4017023 := bstep (se 1 (by rfl) ⟨3012767, by rfl⟩ : syracuseStep 4017023 = 6025535) B6025535
theorem B109907867 : Blo 1784093 109907867 := bstep (se 1 (by rfl) ⟨82430900, by rfl⟩ : syracuseStep 109907867 = 164861801) B164861801
theorem B4018175 : Blo 1784093 4018175 := bstep (se 1 (by rfl) ⟨3013631, by rfl⟩ : syracuseStep 4018175 = 6027263) B6027263
theorem B206278775 : Blo 1784093 206278775 := bstep (se 1 (by rfl) ⟨154709081, by rfl⟩ : syracuseStep 206278775 = 309418163) B309418163
theorem B30486779 : Blo 1784093 30486779 := bstep (se 1 (by rfl) ⟨22865084, by rfl⟩ : syracuseStep 30486779 = 45730169) B45730169
theorem B22868729 : Blo 1784093 22868729 := bstep (se 2 (by rfl) ⟨8575773, by rfl⟩ : syracuseStep 22868729 = 17151547) B17151547
theorem B234739151 : Blo 1784093 234739151 := bstep (se 1 (by rfl) ⟨176054363, by rfl⟩ : syracuseStep 234739151 = 352108727) B352108727
theorem B2676383 : Blo 1784093 2676383 := bstep (se 1 (by rfl) ⟨2007287, by rfl⟩ : syracuseStep 2676383 = 4014575) B4014575
theorem B2677055 : Blo 1784093 2677055 := bstep (se 1 (by rfl) ⟨2007791, by rfl⟩ : syracuseStep 2677055 = 4015583) B4015583
theorem B2677703 : Blo 1784093 2677703 := bstep (se 1 (by rfl) ⟨2008277, by rfl⟩ : syracuseStep 2677703 = 4016555) B4016555
theorem B137519183 : Blo 1784093 137519183 := bstep (se 1 (by rfl) ⟨103139387, by rfl⟩ : syracuseStep 137519183 = 206278775) B206278775
theorem B20324519 : Blo 1784093 20324519 := bstep (se 1 (by rfl) ⟨15243389, by rfl⟩ : syracuseStep 20324519 = 30486779) B30486779
theorem B15245819 : Blo 1784093 15245819 := bstep (se 1 (by rfl) ⟨11434364, by rfl⟩ : syracuseStep 15245819 = 22868729) B22868729
theorem B156492767 : Blo 1784093 156492767 := bstep (se 1 (by rfl) ⟨117369575, by rfl⟩ : syracuseStep 156492767 = 234739151) B234739151
theorem B2678783 : Blo 1784093 2678783 := bstep (se 1 (by rfl) ⟨2009087, by rfl⟩ : syracuseStep 2678783 = 4018175) B4018175
theorem B73271911 : Blo 1784093 73271911 := bstep (se 1 (by rfl) ⟨54953933, by rfl⟩ : syracuseStep 73271911 = 109907867) B109907867
theorem B100390681 : Blo 1784093 100390681 := bstep (se 2 (by rfl) ⟨37646505, by rfl⟩ : syracuseStep 100390681 = 75293011) B75293011
theorem B18323567 : Blo 1784093 18323567 := bstep (se 1 (by rfl) ⟨13742675, by rfl⟩ : syracuseStep 18323567 = 27485351) B27485351
theorem B1784255 : Blo 1784093 1784255 := bstep (se 1 (by rfl) ⟨1338191, by rfl⟩ : syracuseStep 1784255 = 2676383) B2676383
theorem B1784703 : Blo 1784093 1784703 := bstep (se 1 (by rfl) ⟨1338527, by rfl⟩ : syracuseStep 1784703 = 2677055) B2677055
theorem B2678015 : Blo 1784093 2678015 := bstep (se 1 (by rfl) ⟨2008511, by rfl⟩ : syracuseStep 2678015 = 4017023) B4017023
theorem B1785135 : Blo 1784093 1785135 := bstep (se 1 (by rfl) ⟨1338851, by rfl⟩ : syracuseStep 1785135 = 2677703) B2677703
theorem B2678777 : Blo 1784093 2678777 := bstep (se 2 (by rfl) ⟨1004541, by rfl⟩ : syracuseStep 2678777 = 2009083) B2009083
theorem B13549679 : Blo 1784093 13549679 := bstep (se 1 (by rfl) ⟨10162259, by rfl⟩ : syracuseStep 13549679 = 20324519) B20324519
theorem B12215711 : Blo 1784093 12215711 := bstep (se 1 (by rfl) ⟨9161783, by rfl⟩ : syracuseStep 12215711 = 18323567) B18323567
theorem B91679455 : Blo 1784093 91679455 := bstep (se 1 (by rfl) ⟨68759591, by rfl⟩ : syracuseStep 91679455 = 137519183) B137519183
theorem B133854241 : Blo 1784093 133854241 := bstep (se 2 (by rfl) ⟨50195340, by rfl⟩ : syracuseStep 133854241 = 100390681) B100390681
theorem B417314045 : Blo 1784093 417314045 := bstep (se 3 (by rfl) ⟨78246383, by rfl⟩ : syracuseStep 417314045 = 156492767) B156492767
theorem B10163879 : Blo 1784093 10163879 := bstep (se 1 (by rfl) ⟨7622909, by rfl⟩ : syracuseStep 10163879 = 15245819) B15245819
theorem B97695881 : Blo 1784093 97695881 := bstep (se 2 (by rfl) ⟨36635955, by rfl⟩ : syracuseStep 97695881 = 73271911) B73271911
theorem B1785851 : Blo 1784093 1785851 := bstep (se 1 (by rfl) ⟨1339388, by rfl⟩ : syracuseStep 1785851 = 2678777) B2678777
theorem B1785343 : Blo 1784093 1785343 := bstep (se 1 (by rfl) ⟨1339007, by rfl⟩ : syracuseStep 1785343 = 2678015) B2678015
theorem B1785855 : Blo 1784093 1785855 := bstep (se 1 (by rfl) ⟨1339391, by rfl⟩ : syracuseStep 1785855 = 2678783) B2678783
theorem B278209363 : Blo 1784093 278209363 := bstep (se 1 (by rfl) ⟨208657022, by rfl⟩ : syracuseStep 278209363 = 417314045) B417314045
theorem B6775919 : Blo 1784093 6775919 := bstep (se 1 (by rfl) ⟨5081939, by rfl⟩ : syracuseStep 6775919 = 10163879) B10163879
theorem B178472321 : Blo 1784093 178472321 := bstep (se 2 (by rfl) ⟨66927120, by rfl⟩ : syracuseStep 178472321 = 133854241) B133854241
theorem B32575229 : Blo 1784093 32575229 := bstep (se 3 (by rfl) ⟨6107855, by rfl⟩ : syracuseStep 32575229 = 12215711) B12215711
theorem B65130587 : Blo 1784093 65130587 := bstep (se 1 (by rfl) ⟨48847940, by rfl⟩ : syracuseStep 65130587 = 97695881) B97695881
theorem B9033119 : Blo 1784093 9033119 := bstep (se 1 (by rfl) ⟨6774839, by rfl⟩ : syracuseStep 9033119 = 13549679) B13549679
theorem B122239273 : Blo 1784093 122239273 := bstep (se 2 (by rfl) ⟨45839727, by rfl⟩ : syracuseStep 122239273 = 91679455) B91679455
theorem B118981547 : Blo 1784093 118981547 := bstep (se 1 (by rfl) ⟨89236160, by rfl⟩ : syracuseStep 118981547 = 178472321) B178472321
theorem B6022079 : Blo 1784093 6022079 := bstep (se 1 (by rfl) ⟨4516559, by rfl⟩ : syracuseStep 6022079 = 9033119) B9033119
theorem B43420391 : Blo 1784093 43420391 := bstep (se 1 (by rfl) ⟨32565293, by rfl⟩ : syracuseStep 43420391 = 65130587) B65130587
theorem B4517279 : Blo 1784093 4517279 := bstep (se 1 (by rfl) ⟨3387959, by rfl⟩ : syracuseStep 4517279 = 6775919) B6775919
theorem B370945817 : Blo 1784093 370945817 := bstep (se 2 (by rfl) ⟨139104681, by rfl⟩ : syracuseStep 370945817 = 278209363) B278209363
theorem B162985697 : Blo 1784093 162985697 := bstep (se 2 (by rfl) ⟨61119636, by rfl⟩ : syracuseStep 162985697 = 122239273) B122239273
theorem B21716819 : Blo 1784093 21716819 := bstep (se 1 (by rfl) ⟨16287614, by rfl⟩ : syracuseStep 21716819 = 32575229) B32575229
theorem B4014719 : Blo 1784093 4014719 := bstep (se 1 (by rfl) ⟨3011039, by rfl⟩ : syracuseStep 4014719 = 6022079) B6022079
theorem B14477879 : Blo 1784093 14477879 := bstep (se 1 (by rfl) ⟨10858409, by rfl⟩ : syracuseStep 14477879 = 21716819) B21716819
theorem B28946927 : Blo 1784093 28946927 := bstep (se 1 (by rfl) ⟨21710195, by rfl⟩ : syracuseStep 28946927 = 43420391) B43420391
theorem B3011519 : Blo 1784093 3011519 := bstep (se 1 (by rfl) ⟨2258639, by rfl⟩ : syracuseStep 3011519 = 4517279) B4517279
theorem B247297211 : Blo 1784093 247297211 := bstep (se 1 (by rfl) ⟨185472908, by rfl⟩ : syracuseStep 247297211 = 370945817) B370945817
theorem B79321031 : Blo 1784093 79321031 := bstep (se 1 (by rfl) ⟨59490773, by rfl⟩ : syracuseStep 79321031 = 118981547) B118981547
theorem B108657131 : Blo 1784093 108657131 := bstep (se 1 (by rfl) ⟨81492848, by rfl⟩ : syracuseStep 108657131 = 162985697) B162985697
theorem B2007679 : Blo 1784093 2007679 := bstep (se 1 (by rfl) ⟨1505759, by rfl⟩ : syracuseStep 2007679 = 3011519) B3011519
theorem B164864807 : Blo 1784093 164864807 := bstep (se 1 (by rfl) ⟨123648605, by rfl⟩ : syracuseStep 164864807 = 247297211) B247297211
theorem B289752349 : Blo 1784093 289752349 := bstep (se 3 (by rfl) ⟨54328565, by rfl⟩ : syracuseStep 289752349 = 108657131) B108657131
theorem B52880687 : Blo 1784093 52880687 := bstep (se 1 (by rfl) ⟨39660515, by rfl⟩ : syracuseStep 52880687 = 79321031) B79321031
theorem B9651919 : Blo 1784093 9651919 := bstep (se 1 (by rfl) ⟨7238939, by rfl⟩ : syracuseStep 9651919 = 14477879) B14477879
theorem B2676479 : Blo 1784093 2676479 := bstep (se 1 (by rfl) ⟨2007359, by rfl⟩ : syracuseStep 2676479 = 4014719) B4014719
theorem B77191805 : Blo 1784093 77191805 := bstep (se 3 (by rfl) ⟨14473463, by rfl⟩ : syracuseStep 77191805 = 28946927) B28946927
theorem B386336465 : Blo 1784093 386336465 := bstep (se 2 (by rfl) ⟨144876174, by rfl⟩ : syracuseStep 386336465 = 289752349) B289752349
theorem B35253791 : Blo 1784093 35253791 := bstep (se 1 (by rfl) ⟨26440343, by rfl⟩ : syracuseStep 35253791 = 52880687) B52880687
theorem B109909871 : Blo 1784093 109909871 := bstep (se 1 (by rfl) ⟨82432403, by rfl⟩ : syracuseStep 109909871 = 164864807) B164864807
theorem B2676905 : Blo 1784093 2676905 := bstep (se 2 (by rfl) ⟨1003839, by rfl⟩ : syracuseStep 2676905 = 2007679) B2007679
theorem B1784319 : Blo 1784093 1784319 := bstep (se 1 (by rfl) ⟨1338239, by rfl⟩ : syracuseStep 1784319 = 2676479) B2676479
theorem B51461203 : Blo 1784093 51461203 := bstep (se 1 (by rfl) ⟨38595902, by rfl⟩ : syracuseStep 51461203 = 77191805) B77191805
theorem B12869225 : Blo 1784093 12869225 := bstep (se 2 (by rfl) ⟨4825959, by rfl⟩ : syracuseStep 12869225 = 9651919) B9651919
theorem B257557643 : Blo 1784093 257557643 := bstep (se 1 (by rfl) ⟨193168232, by rfl⟩ : syracuseStep 257557643 = 386336465) B386336465
theorem B8579483 : Blo 1784093 8579483 := bstep (se 1 (by rfl) ⟨6434612, by rfl⟩ : syracuseStep 8579483 = 12869225) B12869225
theorem B73273247 : Blo 1784093 73273247 := bstep (se 1 (by rfl) ⟨54954935, by rfl⟩ : syracuseStep 73273247 = 109909871) B109909871
theorem B68614937 : Blo 1784093 68614937 := bstep (se 2 (by rfl) ⟨25730601, by rfl⟩ : syracuseStep 68614937 = 51461203) B51461203
theorem B1784603 : Blo 1784093 1784603 := bstep (se 1 (by rfl) ⟨1338452, by rfl⟩ : syracuseStep 1784603 = 2676905) B2676905
theorem B23502527 : Blo 1784093 23502527 := bstep (se 1 (by rfl) ⟨17626895, by rfl⟩ : syracuseStep 23502527 = 35253791) B35253791
theorem B171705095 : Blo 1784093 171705095 := bstep (se 1 (by rfl) ⟨128778821, by rfl⟩ : syracuseStep 171705095 = 257557643) B257557643
theorem B5719655 : Blo 1784093 5719655 := bstep (se 1 (by rfl) ⟨4289741, by rfl⟩ : syracuseStep 5719655 = 8579483) B8579483
theorem B15668351 : Blo 1784093 15668351 := bstep (se 1 (by rfl) ⟨11751263, by rfl⟩ : syracuseStep 15668351 = 23502527) B23502527
theorem B45743291 : Blo 1784093 45743291 := bstep (se 1 (by rfl) ⟨34307468, by rfl⟩ : syracuseStep 45743291 = 68614937) B68614937
theorem B48848831 : Blo 1784093 48848831 := bstep (se 1 (by rfl) ⟨36636623, by rfl⟩ : syracuseStep 48848831 = 73273247) B73273247
theorem B10445567 : Blo 1784093 10445567 := bstep (se 1 (by rfl) ⟨7834175, by rfl⟩ : syracuseStep 10445567 = 15668351) B15668351
theorem B32565887 : Blo 1784093 32565887 := bstep (se 1 (by rfl) ⟨24424415, by rfl⟩ : syracuseStep 32565887 = 48848831) B48848831
theorem B114470063 : Blo 1784093 114470063 := bstep (se 1 (by rfl) ⟨85852547, by rfl⟩ : syracuseStep 114470063 = 171705095) B171705095
theorem B3813103 : Blo 1784093 3813103 := bstep (se 1 (by rfl) ⟨2859827, by rfl⟩ : syracuseStep 3813103 = 5719655) B5719655
theorem B30495527 : Blo 1784093 30495527 := bstep (se 1 (by rfl) ⟨22871645, by rfl⟩ : syracuseStep 30495527 = 45743291) B45743291
theorem B21710591 : Blo 1784093 21710591 := bstep (se 1 (by rfl) ⟨16282943, by rfl⟩ : syracuseStep 21710591 = 32565887) B32565887
theorem B76313375 : Blo 1784093 76313375 := bstep (se 1 (by rfl) ⟨57235031, by rfl⟩ : syracuseStep 76313375 = 114470063) B114470063
theorem B5084137 : Blo 1784093 5084137 := bstep (se 2 (by rfl) ⟨1906551, by rfl⟩ : syracuseStep 5084137 = 3813103) B3813103
theorem B20330351 : Blo 1784093 20330351 := bstep (se 1 (by rfl) ⟨15247763, by rfl⟩ : syracuseStep 20330351 = 30495527) B30495527
theorem B111419381 : Blo 1784093 111419381 := bstep (se 5 (by rfl) ⟨5222783, by rfl⟩ : syracuseStep 111419381 = 10445567) B10445567
theorem B74279587 : Blo 1784093 74279587 := bstep (se 1 (by rfl) ⟨55709690, by rfl⟩ : syracuseStep 74279587 = 111419381) B111419381
theorem B50875583 : Blo 1784093 50875583 := bstep (se 1 (by rfl) ⟨38156687, by rfl⟩ : syracuseStep 50875583 = 76313375) B76313375
theorem B13553567 : Blo 1784093 13553567 := bstep (se 1 (by rfl) ⟨10165175, by rfl⟩ : syracuseStep 13553567 = 20330351) B20330351
theorem B6778849 : Blo 1784093 6778849 := bstep (se 2 (by rfl) ⟨2542068, by rfl⟩ : syracuseStep 6778849 = 5084137) B5084137
theorem B14473727 : Blo 1784093 14473727 := bstep (se 1 (by rfl) ⟨10855295, by rfl⟩ : syracuseStep 14473727 = 21710591) B21710591
theorem B542672885 : Blo 1784093 542672885 := bstep (se 5 (by rfl) ⟨25437791, by rfl⟩ : syracuseStep 542672885 = 50875583) B50875583
theorem B9038465 : Blo 1784093 9038465 := bstep (se 2 (by rfl) ⟨3389424, by rfl⟩ : syracuseStep 9038465 = 6778849) B6778849
theorem B99039449 : Blo 1784093 99039449 := bstep (se 2 (by rfl) ⟨37139793, by rfl⟩ : syracuseStep 99039449 = 74279587) B74279587
theorem B9649151 : Blo 1784093 9649151 := bstep (se 1 (by rfl) ⟨7236863, by rfl⟩ : syracuseStep 9649151 = 14473727) B14473727
theorem B9035711 : Blo 1784093 9035711 := bstep (se 1 (by rfl) ⟨6776783, by rfl⟩ : syracuseStep 9035711 = 13553567) B13553567
theorem B6432767 : Blo 1784093 6432767 := bstep (se 1 (by rfl) ⟨4824575, by rfl⟩ : syracuseStep 6432767 = 9649151) B9649151
theorem B6023807 : Blo 1784093 6023807 := bstep (se 1 (by rfl) ⟨4517855, by rfl⟩ : syracuseStep 6023807 = 9035711) B9035711
theorem B264105197 : Blo 1784093 264105197 := bstep (se 3 (by rfl) ⟨49519724, by rfl⟩ : syracuseStep 264105197 = 99039449) B99039449
theorem B6025643 : Blo 1784093 6025643 := bstep (se 1 (by rfl) ⟨4519232, by rfl⟩ : syracuseStep 6025643 = 9038465) B9038465
theorem B361781923 : Blo 1784093 361781923 := bstep (se 1 (by rfl) ⟨271336442, by rfl⟩ : syracuseStep 361781923 = 542672885) B542672885
theorem B4015871 : Blo 1784093 4015871 := bstep (se 1 (by rfl) ⟨3011903, by rfl⟩ : syracuseStep 4015871 = 6023807) B6023807
theorem B4017095 : Blo 1784093 4017095 := bstep (se 1 (by rfl) ⟨3012821, by rfl⟩ : syracuseStep 4017095 = 6025643) B6025643
theorem B4288511 : Blo 1784093 4288511 := bstep (se 1 (by rfl) ⟨3216383, by rfl⟩ : syracuseStep 4288511 = 6432767) B6432767
theorem B482375897 : Blo 1784093 482375897 := bstep (se 2 (by rfl) ⟨180890961, by rfl⟩ : syracuseStep 482375897 = 361781923) B361781923
theorem B176070131 : Blo 1784093 176070131 := bstep (se 1 (by rfl) ⟨132052598, by rfl⟩ : syracuseStep 176070131 = 264105197) B264105197
theorem B117380087 : Blo 1784093 117380087 := bstep (se 1 (by rfl) ⟨88035065, by rfl⟩ : syracuseStep 117380087 = 176070131) B176070131
theorem B2677247 : Blo 1784093 2677247 := bstep (se 1 (by rfl) ⟨2007935, by rfl⟩ : syracuseStep 2677247 = 4015871) B4015871
theorem B321583931 : Blo 1784093 321583931 := bstep (se 1 (by rfl) ⟨241187948, by rfl⟩ : syracuseStep 321583931 = 482375897) B482375897
theorem B2678063 : Blo 1784093 2678063 := bstep (se 1 (by rfl) ⟨2008547, by rfl⟩ : syracuseStep 2678063 = 4017095) B4017095
theorem B11436029 : Blo 1784093 11436029 := bstep (se 3 (by rfl) ⟨2144255, by rfl⟩ : syracuseStep 11436029 = 4288511) B4288511
theorem B78253391 : Blo 1784093 78253391 := bstep (se 1 (by rfl) ⟨58690043, by rfl⟩ : syracuseStep 78253391 = 117380087) B117380087
theorem B214389287 : Blo 1784093 214389287 := bstep (se 1 (by rfl) ⟨160791965, by rfl⟩ : syracuseStep 214389287 = 321583931) B321583931
theorem B7624019 : Blo 1784093 7624019 := bstep (se 1 (by rfl) ⟨5718014, by rfl⟩ : syracuseStep 7624019 = 11436029) B11436029
theorem B1784831 : Blo 1784093 1784831 := bstep (se 1 (by rfl) ⟨1338623, by rfl⟩ : syracuseStep 1784831 = 2677247) B2677247
theorem B1785375 : Blo 1784093 1785375 := bstep (se 1 (by rfl) ⟨1339031, by rfl⟩ : syracuseStep 1785375 = 2678063) B2678063
theorem B142926191 : Blo 1784093 142926191 := bstep (se 1 (by rfl) ⟨107194643, by rfl⟩ : syracuseStep 142926191 = 214389287) B214389287
theorem B208675709 : Blo 1784093 208675709 := bstep (se 3 (by rfl) ⟨39126695, by rfl⟩ : syracuseStep 208675709 = 78253391) B78253391
theorem B5082679 : Blo 1784093 5082679 := bstep (se 1 (by rfl) ⟨3812009, by rfl⟩ : syracuseStep 5082679 = 7624019) B7624019
theorem B139117139 : Blo 1784093 139117139 := bstep (se 1 (by rfl) ⟨104337854, by rfl⟩ : syracuseStep 139117139 = 208675709) B208675709
theorem B6776905 : Blo 1784093 6776905 := bstep (se 2 (by rfl) ⟨2541339, by rfl⟩ : syracuseStep 6776905 = 5082679) B5082679
theorem B95284127 : Blo 1784093 95284127 := bstep (se 1 (by rfl) ⟨71463095, by rfl⟩ : syracuseStep 95284127 = 142926191) B142926191
theorem B9035873 : Blo 1784093 9035873 := bstep (se 2 (by rfl) ⟨3388452, by rfl⟩ : syracuseStep 9035873 = 6776905) B6776905
theorem B92744759 : Blo 1784093 92744759 := bstep (se 1 (by rfl) ⟨69558569, by rfl⟩ : syracuseStep 92744759 = 139117139) B139117139
theorem B254091005 : Blo 1784093 254091005 := bstep (se 3 (by rfl) ⟨47642063, by rfl⟩ : syracuseStep 254091005 = 95284127) B95284127
theorem B6023915 : Blo 1784093 6023915 := bstep (se 1 (by rfl) ⟨4517936, by rfl⟩ : syracuseStep 6023915 = 9035873) B9035873
theorem B61829839 : Blo 1784093 61829839 := bstep (se 1 (by rfl) ⟨46372379, by rfl⟩ : syracuseStep 61829839 = 92744759) B92744759
theorem B169394003 : Blo 1784093 169394003 := bstep (se 1 (by rfl) ⟨127045502, by rfl⟩ : syracuseStep 169394003 = 254091005) B254091005
theorem B4015943 : Blo 1784093 4015943 := bstep (se 1 (by rfl) ⟨3011957, by rfl⟩ : syracuseStep 4015943 = 6023915) B6023915
theorem B112929335 : Blo 1784093 112929335 := bstep (se 1 (by rfl) ⟨84697001, by rfl⟩ : syracuseStep 112929335 = 169394003) B169394003
theorem B82439785 : Blo 1784093 82439785 := bstep (se 2 (by rfl) ⟨30914919, by rfl⟩ : syracuseStep 82439785 = 61829839) B61829839
theorem B75286223 : Blo 1784093 75286223 := bstep (se 1 (by rfl) ⟨56464667, by rfl⟩ : syracuseStep 75286223 = 112929335) B112929335
theorem B2677295 : Blo 1784093 2677295 := bstep (se 1 (by rfl) ⟨2007971, by rfl⟩ : syracuseStep 2677295 = 4015943) B4015943
theorem B109919713 : Blo 1784093 109919713 := bstep (se 2 (by rfl) ⟨41219892, by rfl⟩ : syracuseStep 109919713 = 82439785) B82439785
theorem B146559617 : Blo 1784093 146559617 := bstep (se 2 (by rfl) ⟨54959856, by rfl⟩ : syracuseStep 146559617 = 109919713) B109919713
theorem B50190815 : Blo 1784093 50190815 := bstep (se 1 (by rfl) ⟨37643111, by rfl⟩ : syracuseStep 50190815 = 75286223) B75286223
theorem B1784863 : Blo 1784093 1784863 := bstep (se 1 (by rfl) ⟨1338647, by rfl⟩ : syracuseStep 1784863 = 2677295) B2677295
theorem B97706411 : Blo 1784093 97706411 := bstep (se 1 (by rfl) ⟨73279808, by rfl⟩ : syracuseStep 97706411 = 146559617) B146559617
theorem B33460543 : Blo 1784093 33460543 := bstep (se 1 (by rfl) ⟨25095407, by rfl⟩ : syracuseStep 33460543 = 50190815) B50190815
theorem B178456229 : Blo 1784093 178456229 := bstep (se 4 (by rfl) ⟨16730271, by rfl⟩ : syracuseStep 178456229 = 33460543) B33460543
theorem B65137607 : Blo 1784093 65137607 := bstep (se 1 (by rfl) ⟨48853205, by rfl⟩ : syracuseStep 65137607 = 97706411) B97706411
theorem B118970819 : Blo 1784093 118970819 := bstep (se 1 (by rfl) ⟨89228114, by rfl⟩ : syracuseStep 118970819 = 178456229) B178456229
theorem B43425071 : Blo 1784093 43425071 := bstep (se 1 (by rfl) ⟨32568803, by rfl⟩ : syracuseStep 43425071 = 65137607) B65137607
theorem B79313879 : Blo 1784093 79313879 := bstep (se 1 (by rfl) ⟨59485409, by rfl⟩ : syracuseStep 79313879 = 118970819) B118970819
theorem B28950047 : Blo 1784093 28950047 := bstep (se 1 (by rfl) ⟨21712535, by rfl⟩ : syracuseStep 28950047 = 43425071) B43425071
theorem B52875919 : Blo 1784093 52875919 := bstep (se 1 (by rfl) ⟨39656939, by rfl⟩ : syracuseStep 52875919 = 79313879) B79313879
theorem B19300031 : Blo 1784093 19300031 := bstep (se 1 (by rfl) ⟨14475023, by rfl⟩ : syracuseStep 19300031 = 28950047) B28950047
theorem B70501225 : Blo 1784093 70501225 := bstep (se 2 (by rfl) ⟨26437959, by rfl⟩ : syracuseStep 70501225 = 52875919) B52875919
theorem B12866687 : Blo 1784093 12866687 := bstep (se 1 (by rfl) ⟨9650015, by rfl⟩ : syracuseStep 12866687 = 19300031) B19300031
theorem B8577791 : Blo 1784093 8577791 := bstep (se 1 (by rfl) ⟨6433343, by rfl⟩ : syracuseStep 8577791 = 12866687) B12866687
theorem B94001633 : Blo 1784093 94001633 := bstep (se 2 (by rfl) ⟨35250612, by rfl⟩ : syracuseStep 94001633 = 70501225) B70501225
theorem B5718527 : Blo 1784093 5718527 := bstep (se 1 (by rfl) ⟨4288895, by rfl⟩ : syracuseStep 5718527 = 8577791) B8577791
theorem B62667755 : Blo 1784093 62667755 := bstep (se 1 (by rfl) ⟨47000816, by rfl⟩ : syracuseStep 62667755 = 94001633) B94001633
theorem B3812351 : Blo 1784093 3812351 := bstep (se 1 (by rfl) ⟨2859263, by rfl⟩ : syracuseStep 3812351 = 5718527) B5718527
theorem B41778503 : Blo 1784093 41778503 := bstep (se 1 (by rfl) ⟨31333877, by rfl⟩ : syracuseStep 41778503 = 62667755) B62667755
theorem B10166269 : Blo 1784093 10166269 := bstep (se 3 (by rfl) ⟨1906175, by rfl⟩ : syracuseStep 10166269 = 3812351) B3812351
theorem B27852335 : Blo 1784093 27852335 := bstep (se 1 (by rfl) ⟨20889251, by rfl⟩ : syracuseStep 27852335 = 41778503) B41778503
theorem B18568223 : Blo 1784093 18568223 := bstep (se 1 (by rfl) ⟨13926167, by rfl⟩ : syracuseStep 18568223 = 27852335) B27852335
theorem B13555025 : Blo 1784093 13555025 := bstep (se 2 (by rfl) ⟨5083134, by rfl⟩ : syracuseStep 13555025 = 10166269) B10166269
theorem B12378815 : Blo 1784093 12378815 := bstep (se 1 (by rfl) ⟨9284111, by rfl⟩ : syracuseStep 12378815 = 18568223) B18568223
theorem B9036683 : Blo 1784093 9036683 := bstep (se 1 (by rfl) ⟨6777512, by rfl⟩ : syracuseStep 9036683 = 13555025) B13555025
theorem B8252543 : Blo 1784093 8252543 := bstep (se 1 (by rfl) ⟨6189407, by rfl⟩ : syracuseStep 8252543 = 12378815) B12378815
theorem B6024455 : Blo 1784093 6024455 := bstep (se 1 (by rfl) ⟨4518341, by rfl⟩ : syracuseStep 6024455 = 9036683) B9036683
theorem B4016303 : Blo 1784093 4016303 := bstep (se 1 (by rfl) ⟨3012227, by rfl⟩ : syracuseStep 4016303 = 6024455) B6024455
theorem B5501695 : Blo 1784093 5501695 := bstep (se 1 (by rfl) ⟨4126271, by rfl⟩ : syracuseStep 5501695 = 8252543) B8252543
theorem B7335593 : Blo 1784093 7335593 := bstep (se 2 (by rfl) ⟨2750847, by rfl⟩ : syracuseStep 7335593 = 5501695) B5501695
theorem B2677535 : Blo 1784093 2677535 := bstep (se 1 (by rfl) ⟨2008151, by rfl⟩ : syracuseStep 2677535 = 4016303) B4016303
theorem B1785023 : Blo 1784093 1785023 := bstep (se 1 (by rfl) ⟨1338767, by rfl⟩ : syracuseStep 1785023 = 2677535) B2677535
theorem B4890395 : Blo 1784093 4890395 := bstep (se 1 (by rfl) ⟨3667796, by rfl⟩ : syracuseStep 4890395 = 7335593) B7335593
theorem B3260263 : Blo 1784093 3260263 := bstep (se 1 (by rfl) ⟨2445197, by rfl⟩ : syracuseStep 3260263 = 4890395) B4890395
theorem B4347017 : Blo 1784093 4347017 := bstep (se 2 (by rfl) ⟨1630131, by rfl⟩ : syracuseStep 4347017 = 3260263) B3260263
theorem B2898011 : Blo 1784093 2898011 := bstep (se 1 (by rfl) ⟨2173508, by rfl⟩ : syracuseStep 2898011 = 4347017) B4347017
theorem B1932007 : Blo 1784093 1932007 := bstep (se 1 (by rfl) ⟨1449005, by rfl⟩ : syracuseStep 1932007 = 2898011) B2898011
theorem B2576009 : Blo 1784093 2576009 := bstep (se 2 (by rfl) ⟨966003, by rfl⟩ : syracuseStep 2576009 = 1932007) B1932007
theorem B6869357 : Blo 1784093 6869357 := bstep (se 3 (by rfl) ⟨1288004, by rfl⟩ : syracuseStep 6869357 = 2576009) B2576009
theorem B4579571 : Blo 1784093 4579571 := bstep (se 1 (by rfl) ⟨3434678, by rfl⟩ : syracuseStep 4579571 = 6869357) B6869357
theorem B3053047 : Blo 1784093 3053047 := bstep (se 1 (by rfl) ⟨2289785, by rfl⟩ : syracuseStep 3053047 = 4579571) B4579571
theorem B4070729 : Blo 1784093 4070729 := bstep (se 2 (by rfl) ⟨1526523, by rfl⟩ : syracuseStep 4070729 = 3053047) B3053047
theorem B2713819 : Blo 1784093 2713819 := bstep (se 1 (by rfl) ⟨2035364, by rfl⟩ : syracuseStep 2713819 = 4070729) B4070729
theorem B3618425 : Blo 1784093 3618425 := bstep (se 2 (by rfl) ⟨1356909, by rfl⟩ : syracuseStep 3618425 = 2713819) B2713819
theorem B2412283 : Blo 1784093 2412283 := bstep (se 1 (by rfl) ⟨1809212, by rfl⟩ : syracuseStep 2412283 = 3618425) B3618425
theorem B3216377 : Blo 1784093 3216377 := bstep (se 2 (by rfl) ⟨1206141, by rfl⟩ : syracuseStep 3216377 = 2412283) B2412283
theorem B2144251 : Blo 1784093 2144251 := bstep (se 1 (by rfl) ⟨1608188, by rfl⟩ : syracuseStep 2144251 = 3216377) B3216377
theorem B11436005 : Blo 1784093 11436005 := bstep (se 4 (by rfl) ⟨1072125, by rfl⟩ : syracuseStep 11436005 = 2144251) B2144251
theorem B7624003 : Blo 1784093 7624003 := bstep (se 1 (by rfl) ⟨5718002, by rfl⟩ : syracuseStep 7624003 = 11436005) B11436005
theorem B10165337 : Blo 1784093 10165337 := bstep (se 2 (by rfl) ⟨3812001, by rfl⟩ : syracuseStep 10165337 = 7624003) B7624003
theorem B6776891 : Blo 1784093 6776891 := bstep (se 1 (by rfl) ⟨5082668, by rfl⟩ : syracuseStep 6776891 = 10165337) B10165337
theorem B4517927 : Blo 1784093 4517927 := bstep (se 1 (by rfl) ⟨3388445, by rfl⟩ : syracuseStep 4517927 = 6776891) B6776891
theorem B3011951 : Blo 1784093 3011951 := bstep (se 1 (by rfl) ⟨2258963, by rfl⟩ : syracuseStep 3011951 = 4517927) B4517927
theorem B2007967 : Blo 1784093 2007967 := bstep (se 1 (by rfl) ⟨1505975, by rfl⟩ : syracuseStep 2007967 = 3011951) B3011951
theorem B2677289 : Blo 1784093 2677289 := bstep (se 2 (by rfl) ⟨1003983, by rfl⟩ : syracuseStep 2677289 = 2007967) B2007967
theorem B1784859 : Blo 1784093 1784859 := bstep (se 1 (by rfl) ⟨1338644, by rfl⟩ : syracuseStep 1784859 = 2677289) B2677289

theorem C0 (j : ℕ) (h1 : 446023 ≤ j) (h2 : j ≤ 446522) : Blo 1784093 (4 * j + 3) := by
  interval_cases j
  · exact B1784095
  · exact B1784099
  · exact B1784103
  · exact B1784107
  · exact B1784111
  · exact B1784115
  · exact B1784119
  · exact B1784123
  · exact B1784127
  · exact B1784131
  · exact B1784135
  · exact B1784139
  · exact B1784143
  · exact B1784147
  · exact B1784151
  · exact B1784155
  · exact B1784159
  · exact B1784163
  · exact B1784167
  · exact B1784171
  · exact B1784175
  · exact B1784179
  · exact B1784183
  · exact B1784187
  · exact B1784191
  · exact B1784195
  · exact B1784199
  · exact B1784203
  · exact B1784207
  · exact B1784211
  · exact B1784215
  · exact B1784219
  · exact B1784223
  · exact B1784227
  · exact B1784231
  · exact B1784235
  · exact B1784239
  · exact B1784243
  · exact B1784247
  · exact B1784251
  · exact B1784255
  · exact B1784259
  · exact B1784263
  · exact B1784267
  · exact B1784271
  · exact B1784275
  · exact B1784279
  · exact B1784283
  · exact B1784287
  · exact B1784291
  · exact B1784295
  · exact B1784299
  · exact B1784303
  · exact B1784307
  · exact B1784311
  · exact B1784315
  · exact B1784319
  · exact B1784323
  · exact B1784327
  · exact B1784331
  · exact B1784335
  · exact B1784339
  · exact B1784343
  · exact B1784347
  · exact B1784351
  · exact B1784355
  · exact B1784359
  · exact B1784363
  · exact B1784367
  · exact B1784371
  · exact B1784375
  · exact B1784379
  · exact B1784383
  · exact B1784387
  · exact B1784391
  · exact B1784395
  · exact B1784399
  · exact B1784403
  · exact B1784407
  · exact B1784411
  · exact B1784415
  · exact B1784419
  · exact B1784423
  · exact B1784427
  · exact B1784431
  · exact B1784435
  · exact B1784439
  · exact B1784443
  · exact B1784447
  · exact B1784451
  · exact B1784455
  · exact B1784459
  · exact B1784463
  · exact B1784467
  · exact B1784471
  · exact B1784475
  · exact B1784479
  · exact B1784483
  · exact B1784487
  · exact B1784491
  · exact B1784495
  · exact B1784499
  · exact B1784503
  · exact B1784507
  · exact B1784511
  · exact B1784515
  · exact B1784519
  · exact B1784523
  · exact B1784527
  · exact B1784531
  · exact B1784535
  · exact B1784539
  · exact B1784543
  · exact B1784547
  · exact B1784551
  · exact B1784555
  · exact B1784559
  · exact B1784563
  · exact B1784567
  · exact B1784571
  · exact B1784575
  · exact B1784579
  · exact B1784583
  · exact B1784587
  · exact B1784591
  · exact B1784595
  · exact B1784599
  · exact B1784603
  · exact B1784607
  · exact B1784611
  · exact B1784615
  · exact B1784619
  · exact B1784623
  · exact B1784627
  · exact B1784631
  · exact B1784635
  · exact B1784639
  · exact B1784643
  · exact B1784647
  · exact B1784651
  · exact B1784655
  · exact B1784659
  · exact B1784663
  · exact B1784667
  · exact B1784671
  · exact B1784675
  · exact B1784679
  · exact B1784683
  · exact B1784687
  · exact B1784691
  · exact B1784695
  · exact B1784699
  · exact B1784703
  · exact B1784707
  · exact B1784711
  · exact B1784715
  · exact B1784719
  · exact B1784723
  · exact B1784727
  · exact B1784731
  · exact B1784735
  · exact B1784739
  · exact B1784743
  · exact B1784747
  · exact B1784751
  · exact B1784755
  · exact B1784759
  · exact B1784763
  · exact B1784767
  · exact B1784771
  · exact B1784775
  · exact B1784779
  · exact B1784783
  · exact B1784787
  · exact B1784791
  · exact B1784795
  · exact B1784799
  · exact B1784803
  · exact B1784807
  · exact B1784811
  · exact B1784815
  · exact B1784819
  · exact B1784823
  · exact B1784827
  · exact B1784831
  · exact B1784835
  · exact B1784839
  · exact B1784843
  · exact B1784847
  · exact B1784851
  · exact B1784855
  · exact B1784859
  · exact B1784863
  · exact B1784867
  · exact B1784871
  · exact B1784875
  · exact B1784879
  · exact B1784883
  · exact B1784887
  · exact B1784891
  · exact B1784895
  · exact B1784899
  · exact B1784903
  · exact B1784907
  · exact B1784911
  · exact B1784915
  · exact B1784919
  · exact B1784923
  · exact B1784927
  · exact B1784931
  · exact B1784935
  · exact B1784939
  · exact B1784943
  · exact B1784947
  · exact B1784951
  · exact B1784955
  · exact B1784959
  · exact B1784963
  · exact B1784967
  · exact B1784971
  · exact B1784975
  · exact B1784979
  · exact B1784983
  · exact B1784987
  · exact B1784991
  · exact B1784995
  · exact B1784999
  · exact B1785003
  · exact B1785007
  · exact B1785011
  · exact B1785015
  · exact B1785019
  · exact B1785023
  · exact B1785027
  · exact B1785031
  · exact B1785035
  · exact B1785039
  · exact B1785043
  · exact B1785047
  · exact B1785051
  · exact B1785055
  · exact B1785059
  · exact B1785063
  · exact B1785067
  · exact B1785071
  · exact B1785075
  · exact B1785079
  · exact B1785083
  · exact B1785087
  · exact B1785091
  · exact B1785095
  · exact B1785099
  · exact B1785103
  · exact B1785107
  · exact B1785111
  · exact B1785115
  · exact B1785119
  · exact B1785123
  · exact B1785127
  · exact B1785131
  · exact B1785135
  · exact B1785139
  · exact B1785143
  · exact B1785147
  · exact B1785151
  · exact B1785155
  · exact B1785159
  · exact B1785163
  · exact B1785167
  · exact B1785171
  · exact B1785175
  · exact B1785179
  · exact B1785183
  · exact B1785187
  · exact B1785191
  · exact B1785195
  · exact B1785199
  · exact B1785203
  · exact B1785207
  · exact B1785211
  · exact B1785215
  · exact B1785219
  · exact B1785223
  · exact B1785227
  · exact B1785231
  · exact B1785235
  · exact B1785239
  · exact B1785243
  · exact B1785247
  · exact B1785251
  · exact B1785255
  · exact B1785259
  · exact B1785263
  · exact B1785267
  · exact B1785271
  · exact B1785275
  · exact B1785279
  · exact B1785283
  · exact B1785287
  · exact B1785291
  · exact B1785295
  · exact B1785299
  · exact B1785303
  · exact B1785307
  · exact B1785311
  · exact B1785315
  · exact B1785319
  · exact B1785323
  · exact B1785327
  · exact B1785331
  · exact B1785335
  · exact B1785339
  · exact B1785343
  · exact B1785347
  · exact B1785351
  · exact B1785355
  · exact B1785359
  · exact B1785363
  · exact B1785367
  · exact B1785371
  · exact B1785375
  · exact B1785379
  · exact B1785383
  · exact B1785387
  · exact B1785391
  · exact B1785395
  · exact B1785399
  · exact B1785403
  · exact B1785407
  · exact B1785411
  · exact B1785415
  · exact B1785419
  · exact B1785423
  · exact B1785427
  · exact B1785431
  · exact B1785435
  · exact B1785439
  · exact B1785443
  · exact B1785447
  · exact B1785451
  · exact B1785455
  · exact B1785459
  · exact B1785463
  · exact B1785467
  · exact B1785471
  · exact B1785475
  · exact B1785479
  · exact B1785483
  · exact B1785487
  · exact B1785491
  · exact B1785495
  · exact B1785499
  · exact B1785503
  · exact B1785507
  · exact B1785511
  · exact B1785515
  · exact B1785519
  · exact B1785523
  · exact B1785527
  · exact B1785531
  · exact B1785535
  · exact B1785539
  · exact B1785543
  · exact B1785547
  · exact B1785551
  · exact B1785555
  · exact B1785559
  · exact B1785563
  · exact B1785567
  · exact B1785571
  · exact B1785575
  · exact B1785579
  · exact B1785583
  · exact B1785587
  · exact B1785591
  · exact B1785595
  · exact B1785599
  · exact B1785603
  · exact B1785607
  · exact B1785611
  · exact B1785615
  · exact B1785619
  · exact B1785623
  · exact B1785627
  · exact B1785631
  · exact B1785635
  · exact B1785639
  · exact B1785643
  · exact B1785647
  · exact B1785651
  · exact B1785655
  · exact B1785659
  · exact B1785663
  · exact B1785667
  · exact B1785671
  · exact B1785675
  · exact B1785679
  · exact B1785683
  · exact B1785687
  · exact B1785691
  · exact B1785695
  · exact B1785699
  · exact B1785703
  · exact B1785707
  · exact B1785711
  · exact B1785715
  · exact B1785719
  · exact B1785723
  · exact B1785727
  · exact B1785731
  · exact B1785735
  · exact B1785739
  · exact B1785743
  · exact B1785747
  · exact B1785751
  · exact B1785755
  · exact B1785759
  · exact B1785763
  · exact B1785767
  · exact B1785771
  · exact B1785775
  · exact B1785779
  · exact B1785783
  · exact B1785787
  · exact B1785791
  · exact B1785795
  · exact B1785799
  · exact B1785803
  · exact B1785807
  · exact B1785811
  · exact B1785815
  · exact B1785819
  · exact B1785823
  · exact B1785827
  · exact B1785831
  · exact B1785835
  · exact B1785839
  · exact B1785843
  · exact B1785847
  · exact B1785851
  · exact B1785855
  · exact B1785859
  · exact B1785863
  · exact B1785867
  · exact B1785871
  · exact B1785875
  · exact B1785879
  · exact B1785883
  · exact B1785887
  · exact B1785891
  · exact B1785895
  · exact B1785899
  · exact B1785903
  · exact B1785907
  · exact B1785911
  · exact B1785915
  · exact B1785919
  · exact B1785923
  · exact B1785927
  · exact B1785931
  · exact B1785935
  · exact B1785939
  · exact B1785943
  · exact B1785947
  · exact B1785951
  · exact B1785955
  · exact B1785959
  · exact B1785963
  · exact B1785967
  · exact B1785971
  · exact B1785975
  · exact B1785979
  · exact B1785983
  · exact B1785987
  · exact B1785991
  · exact B1785995
  · exact B1785999
  · exact B1786003
  · exact B1786007
  · exact B1786011
  · exact B1786015
  · exact B1786019
  · exact B1786023
  · exact B1786027
  · exact B1786031
  · exact B1786035
  · exact B1786039
  · exact B1786043
  · exact B1786047
  · exact B1786051
  · exact B1786055
  · exact B1786059
  · exact B1786063
  · exact B1786067
  · exact B1786071
  · exact B1786075
  · exact B1786079
  · exact B1786083
  · exact B1786087
  · exact B1786091

theorem solution (m : ℕ) (hlo : 1784093 ≤ m) (hhi : m ≤ 1786093) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 446023 ≤ j := by omega
    have hj2 : j ≤ 446522 := by omega
    have hb : Blo 1784093 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
