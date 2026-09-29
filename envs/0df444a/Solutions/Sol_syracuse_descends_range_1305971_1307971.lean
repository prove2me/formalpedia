-- Prove2me | solution 1 for syracuse_descends_range_1305971_1307971
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:29.153511+00:00
-- url     : https://prove2.me/submissions/c87b5de1-fd6f-4e12-9f3f-26051a7692e3

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


theorem B6619157 : Blo 1305971 6619157 := bbase (se 6 (by rfl) ⟨155136, by rfl⟩ : syracuseStep 6619157 = 310273) (by norm_num)
theorem B5586965 : Blo 1305971 5586965 := bbase (se 6 (by rfl) ⟨130944, by rfl⟩ : syracuseStep 5586965 = 261889) (by norm_num)
theorem B2940965 : Blo 1305971 2940965 := bbase (se 4 (by rfl) ⟨275715, by rfl⟩ : syracuseStep 2940965 = 551431) (by norm_num)
theorem B1654825 : Blo 1305971 1654825 := bbase (se 2 (by rfl) ⟨620559, by rfl⟩ : syracuseStep 1654825 = 1241119) (by norm_num)
theorem B1859645 : Blo 1305971 1859645 := bbase (se 3 (by rfl) ⟨348683, by rfl⟩ : syracuseStep 1859645 = 697367) (by norm_num)
theorem B1491029 : Blo 1305971 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B2941037 : Blo 1305971 2941037 := bbase (se 3 (by rfl) ⟨551444, by rfl⟩ : syracuseStep 2941037 = 1102889) (by norm_num)
theorem B1654921 : Blo 1305971 1654921 := bbase (se 2 (by rfl) ⟨620595, by rfl⟩ : syracuseStep 1654921 = 1241191) (by norm_num)
theorem B5578901 : Blo 1305971 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B2941109 : Blo 1305971 2941109 := bbase (se 5 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 2941109 = 275729) (by norm_num)
theorem B2203861 : Blo 1305971 2203861 := bbase (se 7 (by rfl) ⟨25826, by rfl⟩ : syracuseStep 2203861 = 51653) (by norm_num)
theorem B3309781 : Blo 1305971 3309781 := bbase (se 7 (by rfl) ⟨38786, by rfl⟩ : syracuseStep 3309781 = 77573) (by norm_num)
theorem B2482397 : Blo 1305971 2482397 := bbase (se 3 (by rfl) ⟨465449, by rfl⟩ : syracuseStep 2482397 = 930899) (by norm_num)
theorem B4964597 : Blo 1305971 4964597 := bbase (se 5 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 4964597 = 465431) (by norm_num)
theorem B2941181 : Blo 1305971 2941181 := bbase (se 3 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 2941181 = 1102943) (by norm_num)
theorem B2203949 : Blo 1305971 2203949 := bbase (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) (by norm_num)
theorem B1655093 : Blo 1305971 1655093 := bbase (se 5 (by rfl) ⟨77582, by rfl⟩ : syracuseStep 1655093 = 155165) (by norm_num)
theorem B2941253 : Blo 1305971 2941253 := bbase (se 4 (by rfl) ⟨275742, by rfl⟩ : syracuseStep 2941253 = 551485) (by norm_num)
theorem B3309893 : Blo 1305971 3309893 := bbase (se 4 (by rfl) ⟨310302, by rfl⟩ : syracuseStep 3309893 = 620605) (by norm_num)
theorem B1655149 : Blo 1305971 1655149 := bbase (se 3 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 1655149 = 620681) (by norm_num)
theorem B4710773 : Blo 1305971 4710773 := bbase (se 5 (by rfl) ⟨220817, by rfl⟩ : syracuseStep 4710773 = 441635) (by norm_num)
theorem B2941325 : Blo 1305971 2941325 := bbase (se 3 (by rfl) ⟨551498, by rfl⟩ : syracuseStep 2941325 = 1102997) (by norm_num)
theorem B2204077 : Blo 1305971 2204077 := bbase (se 3 (by rfl) ⟨413264, by rfl⟩ : syracuseStep 2204077 = 826529) (by norm_num)
theorem B4407749 : Blo 1305971 4407749 := bbase (se 4 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 4407749 = 826453) (by norm_num)
theorem B3719621 : Blo 1305971 3719621 := bbase (se 4 (by rfl) ⟨348714, by rfl⟩ : syracuseStep 3719621 = 697429) (by norm_num)
theorem B1655245 : Blo 1305971 1655245 := bbase (se 3 (by rfl) ⟨310358, by rfl⟩ : syracuseStep 1655245 = 620717) (by norm_num)
theorem B2941397 : Blo 1305971 2941397 := bbase (se 7 (by rfl) ⟨34469, by rfl⟩ : syracuseStep 2941397 = 68939) (by norm_num)
theorem B2204165 : Blo 1305971 2204165 := bbase (se 4 (by rfl) ⟨206640, by rfl⟩ : syracuseStep 2204165 = 413281) (by norm_num)
theorem B3310085 : Blo 1305971 3310085 := bbase (se 4 (by rfl) ⟨310320, by rfl⟩ : syracuseStep 3310085 = 620641) (by norm_num)
theorem B4964885 : Blo 1305971 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B2941469 : Blo 1305971 2941469 := bbase (se 3 (by rfl) ⟨551525, by rfl⟩ : syracuseStep 2941469 = 1103051) (by norm_num)
theorem B2122309 : Blo 1305971 2122309 := bbase (se 4 (by rfl) ⟨198966, by rfl⟩ : syracuseStep 2122309 = 397933) (by norm_num)
theorem B2941541 : Blo 1305971 2941541 := bbase (se 4 (by rfl) ⟨275769, by rfl⟩ : syracuseStep 2941541 = 551539) (by norm_num)
theorem B2204293 : Blo 1305971 2204293 := bbase (se 4 (by rfl) ⟨206652, by rfl⟩ : syracuseStep 2204293 = 413305) (by norm_num)
theorem B8938133 : Blo 1305971 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B2941613 : Blo 1305971 2941613 := bbase (se 3 (by rfl) ⟨551552, by rfl⟩ : syracuseStep 2941613 = 1103105) (by norm_num)
theorem B2204381 : Blo 1305971 2204381 := bbase (se 3 (by rfl) ⟨413321, by rfl⟩ : syracuseStep 2204381 = 826643) (by norm_num)
theorem B3023581 : Blo 1305971 3023581 := bbase (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) (by norm_num)
theorem B3138277 : Blo 1305971 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B2941685 : Blo 1305971 2941685 := bbase (se 5 (by rfl) ⟨137891, by rfl⟩ : syracuseStep 2941685 = 275783) (by norm_num)
theorem B2941757 : Blo 1305971 2941757 := bbase (se 3 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 2941757 = 1103159) (by norm_num)
theorem B2204509 : Blo 1305971 2204509 := bbase (se 3 (by rfl) ⟨413345, by rfl⟩ : syracuseStep 2204509 = 826691) (by norm_num)
theorem B3310429 : Blo 1305971 3310429 := bbase (se 3 (by rfl) ⟨620705, by rfl⟩ : syracuseStep 3310429 = 1241411) (by norm_num)
theorem B4408181 : Blo 1305971 4408181 := bbase (se 5 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 4408181 = 413267) (by norm_num)
theorem B2941829 : Blo 1305971 2941829 := bbase (se 4 (by rfl) ⟨275796, by rfl⟩ : syracuseStep 2941829 = 551593) (by norm_num)
theorem B2204597 : Blo 1305971 2204597 := bbase (se 5 (by rfl) ⟨103340, by rfl⟩ : syracuseStep 2204597 = 206681) (by norm_num)
theorem B2941901 : Blo 1305971 2941901 := bbase (se 3 (by rfl) ⟨551606, by rfl⟩ : syracuseStep 2941901 = 1103213) (by norm_num)
theorem B3310541 : Blo 1305971 3310541 := bbase (se 3 (by rfl) ⟨620726, by rfl⟩ : syracuseStep 3310541 = 1241453) (by norm_num)
theorem B2941973 : Blo 1305971 2941973 := bbase (se 6 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 2941973 = 137905) (by norm_num)
theorem B1958957 : Blo 1305971 1958957 := bbase (se 3 (by rfl) ⟨367304, by rfl⟩ : syracuseStep 1958957 = 734609) (by norm_num)
theorem B2204725 : Blo 1305971 2204725 := bbase (se 5 (by rfl) ⟨103346, by rfl⟩ : syracuseStep 2204725 = 206693) (by norm_num)
theorem B1958981 : Blo 1305971 1958981 := bbase (se 4 (by rfl) ⟨183654, by rfl⟩ : syracuseStep 1958981 = 367309) (by norm_num)
theorem B1959005 : Blo 1305971 1959005 := bbase (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) (by norm_num)
theorem B2942045 : Blo 1305971 2942045 := bbase (se 3 (by rfl) ⟨551633, by rfl⟩ : syracuseStep 2942045 = 1103267) (by norm_num)
theorem B3720293 : Blo 1305971 3720293 := bbase (se 4 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 3720293 = 697555) (by norm_num)
theorem B1959029 : Blo 1305971 1959029 := bbase (se 5 (by rfl) ⟨91829, by rfl⟩ : syracuseStep 1959029 = 183659) (by norm_num)
theorem B1959053 : Blo 1305971 1959053 := bbase (se 3 (by rfl) ⟨367322, by rfl⟩ : syracuseStep 1959053 = 734645) (by norm_num)
theorem B2204813 : Blo 1305971 2204813 := bbase (se 3 (by rfl) ⟨413402, by rfl⟩ : syracuseStep 2204813 = 826805) (by norm_num)
theorem B3310733 : Blo 1305971 3310733 := bbase (se 3 (by rfl) ⟨620762, by rfl⟩ : syracuseStep 3310733 = 1241525) (by norm_num)
theorem B1959077 : Blo 1305971 1959077 := bbase (se 4 (by rfl) ⟨183663, by rfl⟩ : syracuseStep 1959077 = 367327) (by norm_num)
theorem B2942117 : Blo 1305971 2942117 := bbase (se 4 (by rfl) ⟨275823, by rfl⟩ : syracuseStep 2942117 = 551647) (by norm_num)
theorem B6710453 : Blo 1305971 6710453 := bbase (se 5 (by rfl) ⟨314552, by rfl⟩ : syracuseStep 6710453 = 629105) (by norm_num)
theorem B1959101 : Blo 1305971 1959101 := bbase (se 3 (by rfl) ⟨367331, by rfl⟩ : syracuseStep 1959101 = 734663) (by norm_num)
theorem B1959125 : Blo 1305971 1959125 := bbase (se 7 (by rfl) ⟨22958, by rfl⟩ : syracuseStep 1959125 = 45917) (by norm_num)
theorem B16753877 : Blo 1305971 16753877 := bbase (se 7 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 16753877 = 392669) (by norm_num)
theorem B1959149 : Blo 1305971 1959149 := bbase (se 3 (by rfl) ⟨367340, by rfl⟩ : syracuseStep 1959149 = 734681) (by norm_num)
theorem B1885421 : Blo 1305971 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B2942189 : Blo 1305971 2942189 := bbase (se 3 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 2942189 = 1103321) (by norm_num)
theorem B6276341 : Blo 1305971 6276341 := bbase (se 5 (by rfl) ⟨294203, by rfl⟩ : syracuseStep 6276341 = 588407) (by norm_num)
theorem B1959173 : Blo 1305971 1959173 := bbase (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) (by norm_num)
theorem B2204941 : Blo 1305971 2204941 := bbase (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) (by norm_num)
theorem B1959197 : Blo 1305971 1959197 := bbase (se 3 (by rfl) ⟨367349, by rfl⟩ : syracuseStep 1959197 = 734699) (by norm_num)
theorem B4408613 : Blo 1305971 4408613 := bbase (se 4 (by rfl) ⟨413307, by rfl⟩ : syracuseStep 4408613 = 826615) (by norm_num)
theorem B6620453 : Blo 1305971 6620453 := bbase (se 4 (by rfl) ⟨620667, by rfl⟩ : syracuseStep 6620453 = 1241335) (by norm_num)
theorem B1959221 : Blo 1305971 1959221 := bbase (se 5 (by rfl) ⟨91838, by rfl⟩ : syracuseStep 1959221 = 183677) (by norm_num)
theorem B2942261 : Blo 1305971 2942261 := bbase (se 5 (by rfl) ⟨137918, by rfl⟩ : syracuseStep 2942261 = 275837) (by norm_num)
theorem B1959245 : Blo 1305971 1959245 := bbase (se 3 (by rfl) ⟨367358, by rfl⟩ : syracuseStep 1959245 = 734717) (by norm_num)
theorem B1959269 : Blo 1305971 1959269 := bbase (se 4 (by rfl) ⟨183681, by rfl⟩ : syracuseStep 1959269 = 367363) (by norm_num)
theorem B2205029 : Blo 1305971 2205029 := bbase (se 4 (by rfl) ⟨206721, by rfl⟩ : syracuseStep 2205029 = 413443) (by norm_num)
theorem B1959293 : Blo 1305971 1959293 := bbase (se 3 (by rfl) ⟨367367, by rfl⟩ : syracuseStep 1959293 = 734735) (by norm_num)
theorem B2942333 : Blo 1305971 2942333 := bbase (se 3 (by rfl) ⟨551687, by rfl⟩ : syracuseStep 2942333 = 1103375) (by norm_num)
theorem B1959317 : Blo 1305971 1959317 := bbase (se 6 (by rfl) ⟨45921, by rfl⟩ : syracuseStep 1959317 = 91843) (by norm_num)
theorem B16983445 : Blo 1305971 16983445 := bbase (se 6 (by rfl) ⟨398049, by rfl⟩ : syracuseStep 16983445 = 796099) (by norm_num)
theorem B1959341 : Blo 1305971 1959341 := bbase (se 3 (by rfl) ⟨367376, by rfl⟩ : syracuseStep 1959341 = 734753) (by norm_num)
theorem B6038981 : Blo 1305971 6038981 := bbase (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) (by norm_num)
theorem B1959365 : Blo 1305971 1959365 := bbase (se 4 (by rfl) ⟨183690, by rfl⟩ : syracuseStep 1959365 = 367381) (by norm_num)
theorem B2942405 : Blo 1305971 2942405 := bbase (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) (by norm_num)
theorem B1861069 : Blo 1305971 1861069 := bbase (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) (by norm_num)
theorem B1959389 : Blo 1305971 1959389 := bbase (se 3 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 1959389 = 734771) (by norm_num)
theorem B2205157 : Blo 1305971 2205157 := bbase (se 4 (by rfl) ⟨206733, by rfl⟩ : syracuseStep 2205157 = 413467) (by norm_num)
theorem B5965285 : Blo 1305971 5965285 := bbase (se 4 (by rfl) ⟨559245, by rfl⟩ : syracuseStep 5965285 = 1118491) (by norm_num)
theorem B1959413 : Blo 1305971 1959413 := bbase (se 5 (by rfl) ⟨91847, by rfl⟩ : syracuseStep 1959413 = 183695) (by norm_num)
theorem B1959437 : Blo 1305971 1959437 := bbase (se 3 (by rfl) ⟨367394, by rfl⟩ : syracuseStep 1959437 = 734789) (by norm_num)
theorem B2942477 : Blo 1305971 2942477 := bbase (se 3 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 2942477 = 1103429) (by norm_num)
theorem B3720725 : Blo 1305971 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B1959461 : Blo 1305971 1959461 := bbase (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) (by norm_num)
theorem B1959485 : Blo 1305971 1959485 := bbase (se 3 (by rfl) ⟨367403, by rfl⟩ : syracuseStep 1959485 = 734807) (by norm_num)
theorem B2205245 : Blo 1305971 2205245 := bbase (se 3 (by rfl) ⟨413483, by rfl⟩ : syracuseStep 2205245 = 826967) (by norm_num)
theorem B1959509 : Blo 1305971 1959509 := bbase (se 8 (by rfl) ⟨11481, by rfl⟩ : syracuseStep 1959509 = 22963) (by norm_num)
theorem B2942549 : Blo 1305971 2942549 := bbase (se 8 (by rfl) ⟨17241, by rfl⟩ : syracuseStep 2942549 = 34483) (by norm_num)
theorem B1959533 : Blo 1305971 1959533 := bbase (se 3 (by rfl) ⟨367412, by rfl⟩ : syracuseStep 1959533 = 734825) (by norm_num)
theorem B1959557 : Blo 1305971 1959557 := bbase (se 4 (by rfl) ⟨183708, by rfl⟩ : syracuseStep 1959557 = 367417) (by norm_num)
theorem B1959581 : Blo 1305971 1959581 := bbase (se 3 (by rfl) ⟨367421, by rfl⟩ : syracuseStep 1959581 = 734843) (by norm_num)
theorem B3139229 : Blo 1305971 3139229 := bbase (se 3 (by rfl) ⟨588605, by rfl⟩ : syracuseStep 3139229 = 1177211) (by norm_num)
theorem B2942621 : Blo 1305971 2942621 := bbase (se 3 (by rfl) ⟨551741, by rfl⟩ : syracuseStep 2942621 = 1103483) (by norm_num)
theorem B1959605 : Blo 1305971 1959605 := bbase (se 5 (by rfl) ⟨91856, by rfl⟩ : syracuseStep 1959605 = 183713) (by norm_num)
theorem B8373941 : Blo 1305971 8373941 := bbase (se 5 (by rfl) ⟨392528, by rfl⟩ : syracuseStep 8373941 = 785057) (by norm_num)
theorem B4966069 : Blo 1305971 4966069 := bbase (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) (by norm_num)
theorem B2205373 : Blo 1305971 2205373 := bbase (se 3 (by rfl) ⟨413507, by rfl⟩ : syracuseStep 2205373 = 827015) (by norm_num)
theorem B6612677 : Blo 1305971 6612677 := bbase (se 4 (by rfl) ⟨619938, by rfl⟩ : syracuseStep 6612677 = 1239877) (by norm_num)
theorem B1959629 : Blo 1305971 1959629 := bbase (se 3 (by rfl) ⟨367430, by rfl⟩ : syracuseStep 1959629 = 734861) (by norm_num)
theorem B4409045 : Blo 1305971 4409045 := bbase (se 7 (by rfl) ⟨51668, by rfl⟩ : syracuseStep 4409045 = 103337) (by norm_num)
theorem B3139285 : Blo 1305971 3139285 := bbase (se 7 (by rfl) ⟨36788, by rfl⟩ : syracuseStep 3139285 = 73577) (by norm_num)
theorem B1959653 : Blo 1305971 1959653 := bbase (se 4 (by rfl) ⟨183717, by rfl⟩ : syracuseStep 1959653 = 367435) (by norm_num)
theorem B2942693 : Blo 1305971 2942693 := bbase (se 4 (by rfl) ⟨275877, by rfl⟩ : syracuseStep 2942693 = 551755) (by norm_num)
theorem B1959677 : Blo 1305971 1959677 := bbase (se 3 (by rfl) ⟨367439, by rfl⟩ : syracuseStep 1959677 = 734879) (by norm_num)
theorem B1959701 : Blo 1305971 1959701 := bbase (se 6 (by rfl) ⟨45930, by rfl⟩ : syracuseStep 1959701 = 91861) (by norm_num)
theorem B2205461 : Blo 1305971 2205461 := bbase (se 6 (by rfl) ⟨51690, by rfl⟩ : syracuseStep 2205461 = 103381) (by norm_num)
theorem B1959725 : Blo 1305971 1959725 := bbase (se 3 (by rfl) ⟨367448, by rfl⟩ : syracuseStep 1959725 = 734897) (by norm_num)
theorem B2942765 : Blo 1305971 2942765 := bbase (se 3 (by rfl) ⟨551768, by rfl⟩ : syracuseStep 2942765 = 1103537) (by norm_num)
theorem B1959749 : Blo 1305971 1959749 := bbase (se 4 (by rfl) ⟨183726, by rfl⟩ : syracuseStep 1959749 = 367453) (by norm_num)
theorem B1959773 : Blo 1305971 1959773 := bbase (se 3 (by rfl) ⟨367457, by rfl⟩ : syracuseStep 1959773 = 734915) (by norm_num)
theorem B1959797 : Blo 1305971 1959797 := bbase (se 5 (by rfl) ⟨91865, by rfl⟩ : syracuseStep 1959797 = 183731) (by norm_num)
theorem B2942837 : Blo 1305971 2942837 := bbase (se 5 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 2942837 = 275891) (by norm_num)
theorem B5580677 : Blo 1305971 5580677 := bbase (se 4 (by rfl) ⟨523188, by rfl⟩ : syracuseStep 5580677 = 1046377) (by norm_num)
theorem B1959821 : Blo 1305971 1959821 := bbase (se 3 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 1959821 = 734933) (by norm_num)
theorem B3532693 : Blo 1305971 3532693 := bbase (se 6 (by rfl) ⟨82797, by rfl⟩ : syracuseStep 3532693 = 165595) (by norm_num)
theorem B2205589 : Blo 1305971 2205589 := bbase (se 6 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 2205589 = 103387) (by norm_num)
theorem B1959845 : Blo 1305971 1959845 := bbase (se 4 (by rfl) ⟨183735, by rfl⟩ : syracuseStep 1959845 = 367471) (by norm_num)
theorem B1959869 : Blo 1305971 1959869 := bbase (se 3 (by rfl) ⟨367475, by rfl⟩ : syracuseStep 1959869 = 734951) (by norm_num)
theorem B2942909 : Blo 1305971 2942909 := bbase (se 3 (by rfl) ⟨551795, by rfl⟩ : syracuseStep 2942909 = 1103591) (by norm_num)
theorem B14125013 : Blo 1305971 14125013 := bbase (se 7 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 14125013 = 331055) (by norm_num)
theorem B1959893 : Blo 1305971 1959893 := bbase (se 7 (by rfl) ⟨22967, by rfl⟩ : syracuseStep 1959893 = 45935) (by norm_num)
theorem B1394653 : Blo 1305971 1394653 := bbase (se 3 (by rfl) ⟨261497, by rfl⟩ : syracuseStep 1394653 = 522995) (by norm_num)
theorem B1959917 : Blo 1305971 1959917 := bbase (se 3 (by rfl) ⟨367484, by rfl⟩ : syracuseStep 1959917 = 734969) (by norm_num)
theorem B2205677 : Blo 1305971 2205677 := bbase (se 3 (by rfl) ⟨413564, by rfl⟩ : syracuseStep 2205677 = 827129) (by norm_num)
theorem B4777973 : Blo 1305971 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B1959941 : Blo 1305971 1959941 := bbase (se 4 (by rfl) ⟨183744, by rfl⟩ : syracuseStep 1959941 = 367489) (by norm_num)
theorem B1959965 : Blo 1305971 1959965 := bbase (se 3 (by rfl) ⟨367493, by rfl⟩ : syracuseStep 1959965 = 734987) (by norm_num)
theorem B1861661 : Blo 1305971 1861661 := bbase (se 3 (by rfl) ⟨349061, by rfl⟩ : syracuseStep 1861661 = 698123) (by norm_num)
theorem B1959989 : Blo 1305971 1959989 := bbase (se 5 (by rfl) ⟨91874, by rfl⟩ : syracuseStep 1959989 = 183749) (by norm_num)
theorem B1960013 : Blo 1305971 1960013 := bbase (se 3 (by rfl) ⟨367502, by rfl⟩ : syracuseStep 1960013 = 735005) (by norm_num)
theorem B3139661 : Blo 1305971 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B1960037 : Blo 1305971 1960037 := bbase (se 4 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 1960037 = 367507) (by norm_num)
theorem B2205805 : Blo 1305971 2205805 := bbase (se 3 (by rfl) ⟨413588, by rfl⟩ : syracuseStep 2205805 = 827177) (by norm_num)
theorem B1861741 : Blo 1305971 1861741 := bbase (se 3 (by rfl) ⟨349076, by rfl⟩ : syracuseStep 1861741 = 698153) (by norm_num)
theorem B2648189 : Blo 1305971 2648189 := bbase (se 3 (by rfl) ⟨496535, by rfl⟩ : syracuseStep 2648189 = 993071) (by norm_num)
theorem B1960061 : Blo 1305971 1960061 := bbase (se 3 (by rfl) ⟨367511, by rfl⟩ : syracuseStep 1960061 = 735023) (by norm_num)
theorem B4409477 : Blo 1305971 4409477 := bbase (se 4 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 4409477 = 826777) (by norm_num)
theorem B1960085 : Blo 1305971 1960085 := bbase (se 6 (by rfl) ⟨45939, by rfl⟩ : syracuseStep 1960085 = 91879) (by norm_num)
theorem B1960109 : Blo 1305971 1960109 := bbase (se 3 (by rfl) ⟨367520, by rfl⟩ : syracuseStep 1960109 = 735041) (by norm_num)
theorem B1960133 : Blo 1305971 1960133 := bbase (se 4 (by rfl) ⟨183762, by rfl⟩ : syracuseStep 1960133 = 367525) (by norm_num)
theorem B2205893 : Blo 1305971 2205893 := bbase (se 4 (by rfl) ⟨206802, by rfl⟩ : syracuseStep 2205893 = 413605) (by norm_num)
theorem B1960157 : Blo 1305971 1960157 := bbase (se 3 (by rfl) ⟨367529, by rfl⟩ : syracuseStep 1960157 = 735059) (by norm_num)
theorem B1861861 : Blo 1305971 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B1960181 : Blo 1305971 1960181 := bbase (se 5 (by rfl) ⟨91883, by rfl⟩ : syracuseStep 1960181 = 183767) (by norm_num)
theorem B3721477 : Blo 1305971 3721477 := bbase (se 4 (by rfl) ⟨348888, by rfl⟩ : syracuseStep 3721477 = 697777) (by norm_num)
theorem B1960205 : Blo 1305971 1960205 := bbase (se 3 (by rfl) ⟨367538, by rfl⟩ : syracuseStep 1960205 = 735077) (by norm_num)
theorem B6703397 : Blo 1305971 6703397 := bbase (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) (by norm_num)
theorem B1960229 : Blo 1305971 1960229 := bbase (se 4 (by rfl) ⟨183771, by rfl⟩ : syracuseStep 1960229 = 367543) (by norm_num)
theorem B3139901 : Blo 1305971 3139901 := bbase (se 3 (by rfl) ⟨588731, by rfl⟩ : syracuseStep 3139901 = 1177463) (by norm_num)
theorem B1960253 : Blo 1305971 1960253 := bbase (se 3 (by rfl) ⟨367547, by rfl⟩ : syracuseStep 1960253 = 735095) (by norm_num)
theorem B2206021 : Blo 1305971 2206021 := bbase (se 4 (by rfl) ⟨206814, by rfl⟩ : syracuseStep 2206021 = 413629) (by norm_num)
theorem B1861957 : Blo 1305971 1861957 := bbase (se 4 (by rfl) ⟨174558, by rfl⟩ : syracuseStep 1861957 = 349117) (by norm_num)
theorem B1395029 : Blo 1305971 1395029 := bbase (se 10 (by rfl) ⟨2043, by rfl⟩ : syracuseStep 1395029 = 4087) (by norm_num)
theorem B1960277 : Blo 1305971 1960277 := bbase (se 10 (by rfl) ⟨2871, by rfl⟩ : syracuseStep 1960277 = 5743) (by norm_num)
theorem B1960301 : Blo 1305971 1960301 := bbase (se 3 (by rfl) ⟨367556, by rfl⟩ : syracuseStep 1960301 = 735113) (by norm_num)
theorem B9185653 : Blo 1305971 9185653 := bbase (se 5 (by rfl) ⟨430577, by rfl⟩ : syracuseStep 9185653 = 861155) (by norm_num)
theorem B2353541 : Blo 1305971 2353541 := bbase (se 4 (by rfl) ⟨220644, by rfl⟩ : syracuseStep 2353541 = 441289) (by norm_num)
theorem B1960325 : Blo 1305971 1960325 := bbase (se 4 (by rfl) ⟨183780, by rfl⟩ : syracuseStep 1960325 = 367561) (by norm_num)
theorem B1395101 : Blo 1305971 1395101 := bbase (se 3 (by rfl) ⟨261581, by rfl⟩ : syracuseStep 1395101 = 523163) (by norm_num)
theorem B1960349 : Blo 1305971 1960349 := bbase (se 3 (by rfl) ⟨367565, by rfl⟩ : syracuseStep 1960349 = 735131) (by norm_num)
theorem B2206109 : Blo 1305971 2206109 := bbase (se 3 (by rfl) ⟨413645, by rfl⟩ : syracuseStep 2206109 = 827291) (by norm_num)
theorem B1960373 : Blo 1305971 1960373 := bbase (se 5 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 1960373 = 183785) (by norm_num)
theorem B1960397 : Blo 1305971 1960397 := bbase (se 3 (by rfl) ⟨367574, by rfl⟩ : syracuseStep 1960397 = 735149) (by norm_num)
theorem B1960421 : Blo 1305971 1960421 := bbase (se 4 (by rfl) ⟨183789, by rfl⟩ : syracuseStep 1960421 = 367579) (by norm_num)
theorem B1960445 : Blo 1305971 1960445 := bbase (se 3 (by rfl) ⟨367583, by rfl⟩ : syracuseStep 1960445 = 735167) (by norm_num)
theorem B1960469 : Blo 1305971 1960469 := bbase (se 6 (by rfl) ⟨45948, by rfl⟩ : syracuseStep 1960469 = 91897) (by norm_num)
theorem B2206237 : Blo 1305971 2206237 := bbase (se 3 (by rfl) ⟨413669, by rfl⟩ : syracuseStep 2206237 = 827339) (by norm_num)
theorem B1960493 : Blo 1305971 1960493 := bbase (se 3 (by rfl) ⟨367592, by rfl⟩ : syracuseStep 1960493 = 735185) (by norm_num)
theorem B4409909 : Blo 1305971 4409909 := bbase (se 5 (by rfl) ⟨206714, by rfl⟩ : syracuseStep 4409909 = 413429) (by norm_num)
theorem B1960517 : Blo 1305971 1960517 := bbase (se 4 (by rfl) ⟨183798, by rfl⟩ : syracuseStep 1960517 = 367597) (by norm_num)
theorem B3353165 : Blo 1305971 3353165 := bbase (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) (by norm_num)
theorem B1395289 : Blo 1305971 1395289 := bbase (se 2 (by rfl) ⟨523233, by rfl⟩ : syracuseStep 1395289 = 1046467) (by norm_num)
theorem B1960541 : Blo 1305971 1960541 := bbase (se 3 (by rfl) ⟨367601, by rfl⟩ : syracuseStep 1960541 = 735203) (by norm_num)
theorem B1960565 : Blo 1305971 1960565 := bbase (se 5 (by rfl) ⟨91901, by rfl⟩ : syracuseStep 1960565 = 183803) (by norm_num)
theorem B2206325 : Blo 1305971 2206325 := bbase (se 5 (by rfl) ⟨103421, by rfl⟩ : syracuseStep 2206325 = 206843) (by norm_num)
theorem B1960589 : Blo 1305971 1960589 := bbase (se 3 (by rfl) ⟨367610, by rfl⟩ : syracuseStep 1960589 = 735221) (by norm_num)
theorem B1960613 : Blo 1305971 1960613 := bbase (se 4 (by rfl) ⟨183807, by rfl⟩ : syracuseStep 1960613 = 367615) (by norm_num)
theorem B1960637 : Blo 1305971 1960637 := bbase (se 3 (by rfl) ⟨367619, by rfl⟩ : syracuseStep 1960637 = 735239) (by norm_num)
theorem B14887637 : Blo 1305971 14887637 := bbase (se 7 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 14887637 = 348929) (by norm_num)
theorem B1960661 : Blo 1305971 1960661 := bbase (se 7 (by rfl) ⟨22976, by rfl⟩ : syracuseStep 1960661 = 45953) (by norm_num)
theorem B1960685 : Blo 1305971 1960685 := bbase (se 3 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 1960685 = 735257) (by norm_num)
theorem B3533557 : Blo 1305971 3533557 := bbase (se 5 (by rfl) ⟨165635, by rfl⟩ : syracuseStep 3533557 = 331271) (by norm_num)
theorem B2206453 : Blo 1305971 2206453 := bbase (se 5 (by rfl) ⟨103427, by rfl⟩ : syracuseStep 2206453 = 206855) (by norm_num)
theorem B1960709 : Blo 1305971 1960709 := bbase (se 4 (by rfl) ⟨183816, by rfl⟩ : syracuseStep 1960709 = 367633) (by norm_num)
theorem B1395473 : Blo 1305971 1395473 := bbase (se 2 (by rfl) ⟨523302, by rfl⟩ : syracuseStep 1395473 = 1046605) (by norm_num)
theorem B1960733 : Blo 1305971 1960733 := bbase (se 3 (by rfl) ⟨367637, by rfl⟩ : syracuseStep 1960733 = 735275) (by norm_num)
theorem B1960757 : Blo 1305971 1960757 := bbase (se 5 (by rfl) ⟨91910, by rfl⟩ : syracuseStep 1960757 = 183821) (by norm_num)
theorem B1469245 : Blo 1305971 1469245 := bbase (se 3 (by rfl) ⟨275483, by rfl⟩ : syracuseStep 1469245 = 550967) (by norm_num)
theorem B1960781 : Blo 1305971 1960781 := bbase (se 3 (by rfl) ⟨367646, by rfl⟩ : syracuseStep 1960781 = 735293) (by norm_num)
theorem B2206541 : Blo 1305971 2206541 := bbase (se 3 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 2206541 = 827453) (by norm_num)
theorem B4246357 : Blo 1305971 4246357 := bbase (se 9 (by rfl) ⟨12440, by rfl⟩ : syracuseStep 4246357 = 24881) (by norm_num)
theorem B1469281 : Blo 1305971 1469281 := bbase (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) (by norm_num)
theorem B5581669 : Blo 1305971 5581669 := bbase (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) (by norm_num)
theorem B1960805 : Blo 1305971 1960805 := bbase (se 4 (by rfl) ⟨183825, by rfl⟩ : syracuseStep 1960805 = 367651) (by norm_num)
theorem B1960829 : Blo 1305971 1960829 := bbase (se 3 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 1960829 = 735311) (by norm_num)
theorem B1469317 : Blo 1305971 1469317 := bbase (se 4 (by rfl) ⟨137748, by rfl⟩ : syracuseStep 1469317 = 275497) (by norm_num)
theorem B2722709 : Blo 1305971 2722709 := bbase (se 6 (by rfl) ⟨63813, by rfl⟩ : syracuseStep 2722709 = 127627) (by norm_num)
theorem B1960853 : Blo 1305971 1960853 := bbase (se 6 (by rfl) ⟨45957, by rfl⟩ : syracuseStep 1960853 = 91915) (by norm_num)
theorem B1469353 : Blo 1305971 1469353 := bbase (se 2 (by rfl) ⟨551007, by rfl⟩ : syracuseStep 1469353 = 1102015) (by norm_num)
theorem B1960877 : Blo 1305971 1960877 := bbase (se 3 (by rfl) ⟨367664, by rfl⟩ : syracuseStep 1960877 = 735329) (by norm_num)
theorem B1960901 : Blo 1305971 1960901 := bbase (se 4 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 1960901 = 367669) (by norm_num)
theorem B1469389 : Blo 1305971 1469389 := bbase (se 3 (by rfl) ⟨275510, by rfl⟩ : syracuseStep 1469389 = 551021) (by norm_num)
theorem B2206669 : Blo 1305971 2206669 := bbase (se 3 (by rfl) ⟨413750, by rfl⟩ : syracuseStep 2206669 = 827501) (by norm_num)
theorem B6613973 : Blo 1305971 6613973 := bbase (se 7 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 6613973 = 155015) (by norm_num)
theorem B1960925 : Blo 1305971 1960925 := bbase (se 3 (by rfl) ⟨367673, by rfl⟩ : syracuseStep 1960925 = 735347) (by norm_num)
theorem B4410341 : Blo 1305971 4410341 := bbase (se 4 (by rfl) ⟨413469, by rfl⟩ : syracuseStep 4410341 = 826939) (by norm_num)
theorem B1469425 : Blo 1305971 1469425 := bbase (se 2 (by rfl) ⟨551034, by rfl⟩ : syracuseStep 1469425 = 1102069) (by norm_num)
theorem B1960949 : Blo 1305971 1960949 := bbase (se 5 (by rfl) ⟨91919, by rfl⟩ : syracuseStep 1960949 = 183839) (by norm_num)
theorem B1960973 : Blo 1305971 1960973 := bbase (se 3 (by rfl) ⟨367682, by rfl⟩ : syracuseStep 1960973 = 735365) (by norm_num)
theorem B1469461 : Blo 1305971 1469461 := bbase (se 6 (by rfl) ⟨34440, by rfl⟩ : syracuseStep 1469461 = 68881) (by norm_num)
theorem B1592345 : Blo 1305971 1592345 := bbase (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) (by norm_num)
theorem B1960997 : Blo 1305971 1960997 := bbase (se 4 (by rfl) ⟨183843, by rfl⟩ : syracuseStep 1960997 = 367687) (by norm_num)
theorem B2206757 : Blo 1305971 2206757 := bbase (se 4 (by rfl) ⟨206883, by rfl⟩ : syracuseStep 2206757 = 413767) (by norm_num)
theorem B2386997 : Blo 1305971 2386997 := bbase (se 5 (by rfl) ⟨111890, by rfl⟩ : syracuseStep 2386997 = 223781) (by norm_num)
theorem B1469497 : Blo 1305971 1469497 := bbase (se 2 (by rfl) ⟨551061, by rfl⟩ : syracuseStep 1469497 = 1102123) (by norm_num)
theorem B1961021 : Blo 1305971 1961021 := bbase (se 3 (by rfl) ⟨367691, by rfl⟩ : syracuseStep 1961021 = 735383) (by norm_num)
theorem B1961045 : Blo 1305971 1961045 := bbase (se 8 (by rfl) ⟨11490, by rfl⟩ : syracuseStep 1961045 = 22981) (by norm_num)
theorem B1469533 : Blo 1305971 1469533 := bbase (se 3 (by rfl) ⟨275537, by rfl⟩ : syracuseStep 1469533 = 551075) (by norm_num)
theorem B2354285 : Blo 1305971 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B1961069 : Blo 1305971 1961069 := bbase (se 3 (by rfl) ⟨367700, by rfl⟩ : syracuseStep 1961069 = 735401) (by norm_num)
theorem B1469569 : Blo 1305971 1469569 := bbase (se 2 (by rfl) ⟨551088, by rfl⟩ : syracuseStep 1469569 = 1102177) (by norm_num)
theorem B1961093 : Blo 1305971 1961093 := bbase (se 4 (by rfl) ⟨183852, by rfl⟩ : syracuseStep 1961093 = 367705) (by norm_num)
theorem B1961117 : Blo 1305971 1961117 := bbase (se 3 (by rfl) ⟨367709, by rfl⟩ : syracuseStep 1961117 = 735419) (by norm_num)
theorem B1469605 : Blo 1305971 1469605 := bbase (se 4 (by rfl) ⟨137775, by rfl⟩ : syracuseStep 1469605 = 275551) (by norm_num)
theorem B2206885 : Blo 1305971 2206885 := bbase (se 4 (by rfl) ⟨206895, by rfl⟩ : syracuseStep 2206885 = 413791) (by norm_num)
theorem B1592497 : Blo 1305971 1592497 := bbase (se 2 (by rfl) ⟨597186, by rfl⟩ : syracuseStep 1592497 = 1194373) (by norm_num)
theorem B1961141 : Blo 1305971 1961141 := bbase (se 5 (by rfl) ⟨91928, by rfl⟩ : syracuseStep 1961141 = 183857) (by norm_num)
theorem B1469641 : Blo 1305971 1469641 := bbase (se 2 (by rfl) ⟨551115, by rfl⟩ : syracuseStep 1469641 = 1102231) (by norm_num)
theorem B1961165 : Blo 1305971 1961165 := bbase (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) (by norm_num)
theorem B1961189 : Blo 1305971 1961189 := bbase (se 4 (by rfl) ⟨183861, by rfl⟩ : syracuseStep 1961189 = 367723) (by norm_num)
theorem B1469677 : Blo 1305971 1469677 := bbase (se 3 (by rfl) ⟨275564, by rfl⟩ : syracuseStep 1469677 = 551129) (by norm_num)
theorem B1961213 : Blo 1305971 1961213 := bbase (se 3 (by rfl) ⟨367727, by rfl⟩ : syracuseStep 1961213 = 735455) (by norm_num)
theorem B2206973 : Blo 1305971 2206973 := bbase (se 3 (by rfl) ⟨413807, by rfl⟩ : syracuseStep 2206973 = 827615) (by norm_num)
theorem B1469713 : Blo 1305971 1469713 := bbase (se 2 (by rfl) ⟨551142, by rfl⟩ : syracuseStep 1469713 = 1102285) (by norm_num)
theorem B1961237 : Blo 1305971 1961237 := bbase (se 6 (by rfl) ⟨45966, by rfl⟩ : syracuseStep 1961237 = 91933) (by norm_num)
theorem B1961261 : Blo 1305971 1961261 := bbase (se 3 (by rfl) ⟨367736, by rfl⟩ : syracuseStep 1961261 = 735473) (by norm_num)
theorem B1469749 : Blo 1305971 1469749 := bbase (se 5 (by rfl) ⟨68894, by rfl⟩ : syracuseStep 1469749 = 137789) (by norm_num)
theorem B1961285 : Blo 1305971 1961285 := bbase (se 4 (by rfl) ⟨183870, by rfl⟩ : syracuseStep 1961285 = 367741) (by norm_num)
theorem B1469785 : Blo 1305971 1469785 := bbase (se 2 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 1469785 = 1102339) (by norm_num)
theorem B1961309 : Blo 1305971 1961309 := bbase (se 3 (by rfl) ⟨367745, by rfl⟩ : syracuseStep 1961309 = 735491) (by norm_num)
theorem B1961333 : Blo 1305971 1961333 := bbase (se 5 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 1961333 = 183875) (by norm_num)
theorem B1469821 : Blo 1305971 1469821 := bbase (se 3 (by rfl) ⟨275591, by rfl⟩ : syracuseStep 1469821 = 551183) (by norm_num)
theorem B2207101 : Blo 1305971 2207101 := bbase (se 3 (by rfl) ⟨413831, by rfl⟩ : syracuseStep 2207101 = 827663) (by norm_num)
theorem B1961357 : Blo 1305971 1961357 := bbase (se 3 (by rfl) ⟨367754, by rfl⟩ : syracuseStep 1961357 = 735509) (by norm_num)
theorem B4410773 : Blo 1305971 4410773 := bbase (se 6 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 4410773 = 206755) (by norm_num)
theorem B1469857 : Blo 1305971 1469857 := bbase (se 2 (by rfl) ⟨551196, by rfl⟩ : syracuseStep 1469857 = 1102393) (by norm_num)
theorem B1961381 : Blo 1305971 1961381 := bbase (se 4 (by rfl) ⟨183879, by rfl⟩ : syracuseStep 1961381 = 367759) (by norm_num)
theorem B1961405 : Blo 1305971 1961405 := bbase (se 3 (by rfl) ⟨367763, by rfl⟩ : syracuseStep 1961405 = 735527) (by norm_num)
theorem B1469893 : Blo 1305971 1469893 := bbase (se 4 (by rfl) ⟨137802, by rfl⟩ : syracuseStep 1469893 = 275605) (by norm_num)
theorem B1961429 : Blo 1305971 1961429 := bbase (se 7 (by rfl) ⟨22985, by rfl⟩ : syracuseStep 1961429 = 45971) (by norm_num)
theorem B2207189 : Blo 1305971 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B1469929 : Blo 1305971 1469929 := bbase (se 2 (by rfl) ⟨551223, by rfl⟩ : syracuseStep 1469929 = 1102447) (by norm_num)
theorem B1961453 : Blo 1305971 1961453 := bbase (se 3 (by rfl) ⟨367772, by rfl⟩ : syracuseStep 1961453 = 735545) (by norm_num)
theorem B1396225 : Blo 1305971 1396225 := bbase (se 2 (by rfl) ⟨523584, by rfl⟩ : syracuseStep 1396225 = 1047169) (by norm_num)
theorem B1961477 : Blo 1305971 1961477 := bbase (se 4 (by rfl) ⟨183888, by rfl⟩ : syracuseStep 1961477 = 367777) (by norm_num)
theorem B1469965 : Blo 1305971 1469965 := bbase (se 3 (by rfl) ⟨275618, by rfl⟩ : syracuseStep 1469965 = 551237) (by norm_num)
theorem B1961501 : Blo 1305971 1961501 := bbase (se 3 (by rfl) ⟨367781, by rfl⟩ : syracuseStep 1961501 = 735563) (by norm_num)
theorem B1470001 : Blo 1305971 1470001 := bbase (se 2 (by rfl) ⟨551250, by rfl⟩ : syracuseStep 1470001 = 1102501) (by norm_num)
theorem B1961525 : Blo 1305971 1961525 := bbase (se 5 (by rfl) ⟨91946, by rfl⟩ : syracuseStep 1961525 = 183893) (by norm_num)
theorem B1396297 : Blo 1305971 1396297 := bbase (se 2 (by rfl) ⟨523611, by rfl⟩ : syracuseStep 1396297 = 1047223) (by norm_num)
theorem B1961549 : Blo 1305971 1961549 := bbase (se 3 (by rfl) ⟨367790, by rfl⟩ : syracuseStep 1961549 = 735581) (by norm_num)
theorem B1470037 : Blo 1305971 1470037 := bbase (se 8 (by rfl) ⟨8613, by rfl⟩ : syracuseStep 1470037 = 17227) (by norm_num)
theorem B1961573 : Blo 1305971 1961573 := bbase (se 4 (by rfl) ⟨183897, by rfl⟩ : syracuseStep 1961573 = 367795) (by norm_num)
theorem B1470073 : Blo 1305971 1470073 := bbase (se 2 (by rfl) ⟨551277, by rfl⟩ : syracuseStep 1470073 = 1102555) (by norm_num)
theorem B1961597 : Blo 1305971 1961597 := bbase (se 3 (by rfl) ⟨367799, by rfl⟩ : syracuseStep 1961597 = 735599) (by norm_num)
theorem B1961621 : Blo 1305971 1961621 := bbase (se 6 (by rfl) ⟨45975, by rfl⟩ : syracuseStep 1961621 = 91951) (by norm_num)
theorem B1470109 : Blo 1305971 1470109 := bbase (se 3 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 1470109 = 551291) (by norm_num)
theorem B1961645 : Blo 1305971 1961645 := bbase (se 3 (by rfl) ⟨367808, by rfl⟩ : syracuseStep 1961645 = 735617) (by norm_num)
theorem B1470145 : Blo 1305971 1470145 := bbase (se 2 (by rfl) ⟨551304, by rfl⟩ : syracuseStep 1470145 = 1102609) (by norm_num)
theorem B1961669 : Blo 1305971 1961669 := bbase (se 4 (by rfl) ⟨183906, by rfl⟩ : syracuseStep 1961669 = 367813) (by norm_num)
theorem B1961693 : Blo 1305971 1961693 := bbase (se 3 (by rfl) ⟨367817, by rfl⟩ : syracuseStep 1961693 = 735635) (by norm_num)
theorem B1470181 : Blo 1305971 1470181 := bbase (se 4 (by rfl) ⟨137829, by rfl⟩ : syracuseStep 1470181 = 275659) (by norm_num)
theorem B1961717 : Blo 1305971 1961717 := bbase (se 5 (by rfl) ⟨91955, by rfl⟩ : syracuseStep 1961717 = 183911) (by norm_num)
theorem B1396477 : Blo 1305971 1396477 := bbase (se 3 (by rfl) ⟨261839, by rfl⟩ : syracuseStep 1396477 = 523679) (by norm_num)
theorem B1470217 : Blo 1305971 1470217 := bbase (se 2 (by rfl) ⟨551331, by rfl⟩ : syracuseStep 1470217 = 1102663) (by norm_num)
theorem B1961741 : Blo 1305971 1961741 := bbase (se 3 (by rfl) ⟨367826, by rfl⟩ : syracuseStep 1961741 = 735653) (by norm_num)
theorem B1961765 : Blo 1305971 1961765 := bbase (se 4 (by rfl) ⟨183915, by rfl⟩ : syracuseStep 1961765 = 367831) (by norm_num)
theorem B1470253 : Blo 1305971 1470253 := bbase (se 3 (by rfl) ⟨275672, by rfl⟩ : syracuseStep 1470253 = 551345) (by norm_num)
theorem B1961789 : Blo 1305971 1961789 := bbase (se 3 (by rfl) ⟨367835, by rfl⟩ : syracuseStep 1961789 = 735671) (by norm_num)
theorem B4411205 : Blo 1305971 4411205 := bbase (se 4 (by rfl) ⟨413550, by rfl⟩ : syracuseStep 4411205 = 827101) (by norm_num)
theorem B1470289 : Blo 1305971 1470289 := bbase (se 2 (by rfl) ⟨551358, by rfl⟩ : syracuseStep 1470289 = 1102717) (by norm_num)
theorem B1961813 : Blo 1305971 1961813 := bbase (se 9 (by rfl) ⟨5747, by rfl⟩ : syracuseStep 1961813 = 11495) (by norm_num)
theorem B1961837 : Blo 1305971 1961837 := bbase (se 3 (by rfl) ⟨367844, by rfl⟩ : syracuseStep 1961837 = 735689) (by norm_num)
theorem B1470325 : Blo 1305971 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B2789245 : Blo 1305971 2789245 := bbase (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) (by norm_num)
theorem B1961861 : Blo 1305971 1961861 := bbase (se 4 (by rfl) ⟨183924, by rfl⟩ : syracuseStep 1961861 = 367849) (by norm_num)
theorem B1470361 : Blo 1305971 1470361 := bbase (se 2 (by rfl) ⟨551385, by rfl⟩ : syracuseStep 1470361 = 1102771) (by norm_num)
theorem B1961885 : Blo 1305971 1961885 := bbase (se 3 (by rfl) ⟨367853, by rfl⟩ : syracuseStep 1961885 = 735707) (by norm_num)
theorem B3772325 : Blo 1305971 3772325 := bbase (se 4 (by rfl) ⟨353655, by rfl⟩ : syracuseStep 3772325 = 707311) (by norm_num)
theorem B1961909 : Blo 1305971 1961909 := bbase (se 5 (by rfl) ⟨91964, by rfl⟩ : syracuseStep 1961909 = 183929) (by norm_num)
theorem B1470397 : Blo 1305971 1470397 := bbase (se 3 (by rfl) ⟨275699, by rfl⟩ : syracuseStep 1470397 = 551399) (by norm_num)
theorem B1961933 : Blo 1305971 1961933 := bbase (se 3 (by rfl) ⟨367862, by rfl⟩ : syracuseStep 1961933 = 735725) (by norm_num)
theorem B1470433 : Blo 1305971 1470433 := bbase (se 2 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 1470433 = 1102825) (by norm_num)
theorem B1961957 : Blo 1305971 1961957 := bbase (se 4 (by rfl) ⟨183933, by rfl⟩ : syracuseStep 1961957 = 367867) (by norm_num)
theorem B1470469 : Blo 1305971 1470469 := bbase (se 4 (by rfl) ⟨137856, by rfl⟩ : syracuseStep 1470469 = 275713) (by norm_num)
theorem B2830349 : Blo 1305971 2830349 := bbase (se 3 (by rfl) ⟨530690, by rfl⟩ : syracuseStep 2830349 = 1061381) (by norm_num)
theorem B1470505 : Blo 1305971 1470505 := bbase (se 2 (by rfl) ⟨551439, by rfl⟩ : syracuseStep 1470505 = 1102879) (by norm_num)
theorem B6205493 : Blo 1305971 6205493 := bbase (se 5 (by rfl) ⟨290882, by rfl⟩ : syracuseStep 6205493 = 581765) (by norm_num)
theorem B1470541 : Blo 1305971 1470541 := bbase (se 3 (by rfl) ⟨275726, by rfl⟩ : syracuseStep 1470541 = 551453) (by norm_num)
theorem B1470577 : Blo 1305971 1470577 := bbase (se 2 (by rfl) ⟨551466, by rfl⟩ : syracuseStep 1470577 = 1102933) (by norm_num)
theorem B1470613 : Blo 1305971 1470613 := bbase (se 6 (by rfl) ⟨34467, by rfl⟩ : syracuseStep 1470613 = 68935) (by norm_num)
theorem B1470649 : Blo 1305971 1470649 := bbase (se 2 (by rfl) ⟨551493, by rfl⟩ : syracuseStep 1470649 = 1102987) (by norm_num)
theorem B1568989 : Blo 1305971 1568989 := bbase (se 3 (by rfl) ⟨294185, by rfl⟩ : syracuseStep 1568989 = 588371) (by norm_num)
theorem B1470685 : Blo 1305971 1470685 := bbase (se 3 (by rfl) ⟨275753, by rfl⟩ : syracuseStep 1470685 = 551507) (by norm_num)
theorem B6615269 : Blo 1305971 6615269 := bbase (se 4 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 6615269 = 1240363) (by norm_num)
theorem B2093293 : Blo 1305971 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B4411637 : Blo 1305971 4411637 := bbase (se 5 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 4411637 = 413591) (by norm_num)
theorem B1470721 : Blo 1305971 1470721 := bbase (se 2 (by rfl) ⟨551520, by rfl⟩ : syracuseStep 1470721 = 1103041) (by norm_num)
theorem B1470757 : Blo 1305971 1470757 := bbase (se 4 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 1470757 = 275767) (by norm_num)
theorem B3535157 : Blo 1305971 3535157 := bbase (se 5 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 3535157 = 331421) (by norm_num)
theorem B1470793 : Blo 1305971 1470793 := bbase (se 2 (by rfl) ⟨551547, by rfl⟩ : syracuseStep 1470793 = 1103095) (by norm_num)
theorem B2789741 : Blo 1305971 2789741 := bbase (se 3 (by rfl) ⟨523076, by rfl⟩ : syracuseStep 2789741 = 1046153) (by norm_num)
theorem B1765741 : Blo 1305971 1765741 := bbase (se 3 (by rfl) ⟨331076, by rfl⟩ : syracuseStep 1765741 = 662153) (by norm_num)
theorem B1470829 : Blo 1305971 1470829 := bbase (se 3 (by rfl) ⟨275780, by rfl⟩ : syracuseStep 1470829 = 551561) (by norm_num)
theorem B2355589 : Blo 1305971 2355589 := bbase (se 4 (by rfl) ⟨220836, by rfl⟩ : syracuseStep 2355589 = 441673) (by norm_num)
theorem B1470865 : Blo 1305971 1470865 := bbase (se 2 (by rfl) ⟨551574, by rfl⟩ : syracuseStep 1470865 = 1103149) (by norm_num)
theorem B3305893 : Blo 1305971 3305893 := bbase (se 4 (by rfl) ⟨309927, by rfl⟩ : syracuseStep 3305893 = 619855) (by norm_num)
theorem B1765805 : Blo 1305971 1765805 := bbase (se 3 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 1765805 = 662177) (by norm_num)
theorem B1470901 : Blo 1305971 1470901 := bbase (se 5 (by rfl) ⟨68948, by rfl⟩ : syracuseStep 1470901 = 137897) (by norm_num)
theorem B4960709 : Blo 1305971 4960709 := bbase (se 4 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 4960709 = 930133) (by norm_num)
theorem B9818581 : Blo 1305971 9818581 := bbase (se 7 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 9818581 = 230123) (by norm_num)
theorem B1470937 : Blo 1305971 1470937 := bbase (se 2 (by rfl) ⟨551601, by rfl⟩ : syracuseStep 1470937 = 1103203) (by norm_num)
theorem B1470973 : Blo 1305971 1470973 := bbase (se 3 (by rfl) ⟨275807, by rfl⟩ : syracuseStep 1470973 = 551615) (by norm_num)
theorem B3306005 : Blo 1305971 3306005 := bbase (se 6 (by rfl) ⟨77484, by rfl⟩ : syracuseStep 3306005 = 154969) (by norm_num)
theorem B11932181 : Blo 1305971 11932181 := bbase (se 6 (by rfl) ⟨279660, by rfl⟩ : syracuseStep 11932181 = 559321) (by norm_num)
theorem B1471009 : Blo 1305971 1471009 := bbase (se 2 (by rfl) ⟨551628, by rfl⟩ : syracuseStep 1471009 = 1103257) (by norm_num)
theorem B1471045 : Blo 1305971 1471045 := bbase (se 4 (by rfl) ⟨137910, by rfl⟩ : syracuseStep 1471045 = 275821) (by norm_num)
theorem B12554837 : Blo 1305971 12554837 := bbase (se 8 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 12554837 = 147127) (by norm_num)
theorem B1765973 : Blo 1305971 1765973 := bbase (se 8 (by rfl) ⟨10347, by rfl⟩ : syracuseStep 1765973 = 20695) (by norm_num)
theorem B13414997 : Blo 1305971 13414997 := bbase (se 8 (by rfl) ⟨78603, by rfl⟩ : syracuseStep 13414997 = 157207) (by norm_num)
theorem B1471081 : Blo 1305971 1471081 := bbase (se 2 (by rfl) ⟨551655, by rfl⟩ : syracuseStep 1471081 = 1103311) (by norm_num)
theorem B1471117 : Blo 1305971 1471117 := bbase (se 3 (by rfl) ⟨275834, by rfl⟩ : syracuseStep 1471117 = 551669) (by norm_num)
theorem B4412069 : Blo 1305971 4412069 := bbase (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) (by norm_num)
theorem B1471153 : Blo 1305971 1471153 := bbase (se 2 (by rfl) ⟨551682, by rfl⟩ : syracuseStep 1471153 = 1103365) (by norm_num)
theorem B3306197 : Blo 1305971 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B1471189 : Blo 1305971 1471189 := bbase (se 7 (by rfl) ⟨17240, by rfl⟩ : syracuseStep 1471189 = 34481) (by norm_num)
theorem B4960997 : Blo 1305971 4960997 := bbase (se 4 (by rfl) ⟨465093, by rfl⟩ : syracuseStep 4960997 = 930187) (by norm_num)
theorem B1471225 : Blo 1305971 1471225 := bbase (se 2 (by rfl) ⟨551709, by rfl⟩ : syracuseStep 1471225 = 1103419) (by norm_num)
theorem B1471261 : Blo 1305971 1471261 := bbase (se 3 (by rfl) ⟨275861, by rfl⟩ : syracuseStep 1471261 = 551723) (by norm_num)
theorem B1471297 : Blo 1305971 1471297 := bbase (se 2 (by rfl) ⟨551736, by rfl⟩ : syracuseStep 1471297 = 1103473) (by norm_num)
theorem B1413973 : Blo 1305971 1413973 := bbase (se 9 (by rfl) ⟨4142, by rfl⟩ : syracuseStep 1413973 = 8285) (by norm_num)
theorem B1471333 : Blo 1305971 1471333 := bbase (se 4 (by rfl) ⟨137937, by rfl⟩ : syracuseStep 1471333 = 275875) (by norm_num)
theorem B1471369 : Blo 1305971 1471369 := bbase (se 2 (by rfl) ⟨551763, by rfl⟩ : syracuseStep 1471369 = 1103527) (by norm_num)
theorem B1471405 : Blo 1305971 1471405 := bbase (se 3 (by rfl) ⟨275888, by rfl⟩ : syracuseStep 1471405 = 551777) (by norm_num)
theorem B1323965 : Blo 1305971 1323965 := bbase (se 3 (by rfl) ⟨248243, by rfl⟩ : syracuseStep 1323965 = 496487) (by norm_num)
theorem B1471441 : Blo 1305971 1471441 := bbase (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) (by norm_num)
theorem B3724325 : Blo 1305971 3724325 := bbase (se 4 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 3724325 = 698311) (by norm_num)
theorem B3306541 : Blo 1305971 3306541 := bbase (se 3 (by rfl) ⟨619976, by rfl⟩ : syracuseStep 3306541 = 1239953) (by norm_num)
theorem B2651189 : Blo 1305971 2651189 := bbase (se 5 (by rfl) ⟨124274, by rfl⟩ : syracuseStep 2651189 = 248549) (by norm_num)
theorem B4412501 : Blo 1305971 4412501 := bbase (se 8 (by rfl) ⟨25854, by rfl⟩ : syracuseStep 4412501 = 51709) (by norm_num)
theorem B2356309 : Blo 1305971 2356309 := bbase (se 8 (by rfl) ⟨13806, by rfl⟩ : syracuseStep 2356309 = 27613) (by norm_num)
theorem B3306653 : Blo 1305971 3306653 := bbase (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) (by norm_num)
theorem B1324225 : Blo 1305971 1324225 := bbase (se 2 (by rfl) ⟨496584, by rfl⟩ : syracuseStep 1324225 = 993169) (by norm_num)
theorem B1569989 : Blo 1305971 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B2790605 : Blo 1305971 2790605 := bbase (se 3 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 2790605 = 1046477) (by norm_num)
theorem B1570061 : Blo 1305971 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B2479405 : Blo 1305971 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B3306845 : Blo 1305971 3306845 := bbase (se 3 (by rfl) ⟨620033, by rfl⟩ : syracuseStep 3306845 = 1240067) (by norm_num)
theorem B2790749 : Blo 1305971 2790749 := bbase (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) (by norm_num)
theorem B2479565 : Blo 1305971 2479565 := bbase (se 3 (by rfl) ⟨464918, by rfl⟩ : syracuseStep 2479565 = 929837) (by norm_num)
theorem B6616565 : Blo 1305971 6616565 := bbase (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) (by norm_num)
theorem B4412933 : Blo 1305971 4412933 := bbase (se 4 (by rfl) ⟨413712, by rfl⟩ : syracuseStep 4412933 = 827425) (by norm_num)
theorem B4707877 : Blo 1305971 4707877 := bbase (se 4 (by rfl) ⟨441363, by rfl⟩ : syracuseStep 4707877 = 882727) (by norm_num)
theorem B1570369 : Blo 1305971 1570369 := bbase (se 2 (by rfl) ⟨588888, by rfl⟩ : syracuseStep 1570369 = 1177777) (by norm_num)
theorem B2938445 : Blo 1305971 2938445 := bbase (se 3 (by rfl) ⟨550958, by rfl⟩ : syracuseStep 2938445 = 1101917) (by norm_num)
theorem B2094677 : Blo 1305971 2094677 := bbase (se 8 (by rfl) ⟨12273, by rfl⟩ : syracuseStep 2094677 = 24547) (by norm_num)
theorem B2479709 : Blo 1305971 2479709 := bbase (se 3 (by rfl) ⟨464945, by rfl⟩ : syracuseStep 2479709 = 929891) (by norm_num)
theorem B2938517 : Blo 1305971 2938517 := bbase (se 6 (by rfl) ⟨68871, by rfl⟩ : syracuseStep 2938517 = 137743) (by norm_num)
theorem B26834581 : Blo 1305971 26834581 := bbase (se 6 (by rfl) ⟨628935, by rfl⟩ : syracuseStep 26834581 = 1257871) (by norm_num)
theorem B3307189 : Blo 1305971 3307189 := bbase (se 5 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 3307189 = 310049) (by norm_num)
theorem B2938589 : Blo 1305971 2938589 := bbase (se 3 (by rfl) ⟨550985, by rfl⟩ : syracuseStep 2938589 = 1101971) (by norm_num)
theorem B1570537 : Blo 1305971 1570537 := bbase (se 2 (by rfl) ⟨588951, by rfl⟩ : syracuseStep 1570537 = 1177903) (by norm_num)
theorem B10065653 : Blo 1305971 10065653 := bbase (se 5 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 10065653 = 943655) (by norm_num)
theorem B2094869 : Blo 1305971 2094869 := bbase (se 6 (by rfl) ⟨49098, by rfl⟩ : syracuseStep 2094869 = 98197) (by norm_num)
theorem B1570585 : Blo 1305971 1570585 := bbase (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) (by norm_num)
theorem B2938661 : Blo 1305971 2938661 := bbase (se 4 (by rfl) ⟨275499, by rfl⟩ : syracuseStep 2938661 = 550999) (by norm_num)
theorem B3307301 : Blo 1305971 3307301 := bbase (se 4 (by rfl) ⟨310059, by rfl⟩ : syracuseStep 3307301 = 620119) (by norm_num)
theorem B1988405 : Blo 1305971 1988405 := bbase (se 5 (by rfl) ⟨93206, by rfl⟩ : syracuseStep 1988405 = 186413) (by norm_num)
theorem B1324873 : Blo 1305971 1324873 := bbase (se 2 (by rfl) ⟨496827, by rfl⟩ : syracuseStep 1324873 = 993655) (by norm_num)
theorem B2938733 : Blo 1305971 2938733 := bbase (se 3 (by rfl) ⟨551012, by rfl⟩ : syracuseStep 2938733 = 1102025) (by norm_num)
theorem B1570681 : Blo 1305971 1570681 := bbase (se 2 (by rfl) ⟨589005, by rfl⟩ : syracuseStep 1570681 = 1178011) (by norm_num)
theorem B2479997 : Blo 1305971 2479997 := bbase (se 3 (by rfl) ⟨464999, by rfl⟩ : syracuseStep 2479997 = 929999) (by norm_num)
theorem B1988477 : Blo 1305971 1988477 := bbase (se 3 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 1988477 = 745679) (by norm_num)
theorem B4962181 : Blo 1305971 4962181 := bbase (se 4 (by rfl) ⟨465204, by rfl⟩ : syracuseStep 4962181 = 930409) (by norm_num)
theorem B11163541 : Blo 1305971 11163541 := bbase (se 6 (by rfl) ⟨261645, by rfl⟩ : syracuseStep 11163541 = 523291) (by norm_num)
theorem B9926549 : Blo 1305971 9926549 := bbase (se 6 (by rfl) ⟨232653, by rfl⟩ : syracuseStep 9926549 = 465307) (by norm_num)
theorem B2938805 : Blo 1305971 2938805 := bbase (se 5 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 2938805 = 275513) (by norm_num)
theorem B4413365 : Blo 1305971 4413365 := bbase (se 5 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 4413365 = 413753) (by norm_num)
theorem B3307493 : Blo 1305971 3307493 := bbase (se 4 (by rfl) ⟨310077, by rfl⟩ : syracuseStep 3307493 = 620155) (by norm_num)
theorem B2938877 : Blo 1305971 2938877 := bbase (se 3 (by rfl) ⟨551039, by rfl⟩ : syracuseStep 2938877 = 1102079) (by norm_num)
theorem B2480149 : Blo 1305971 2480149 := bbase (se 6 (by rfl) ⟨58128, by rfl⟩ : syracuseStep 2480149 = 116257) (by norm_num)
theorem B2938949 : Blo 1305971 2938949 := bbase (se 4 (by rfl) ⟨275526, by rfl⟩ : syracuseStep 2938949 = 551053) (by norm_num)
theorem B2791493 : Blo 1305971 2791493 := bbase (se 4 (by rfl) ⟨261702, by rfl⟩ : syracuseStep 2791493 = 523405) (by norm_num)
theorem B7944277 : Blo 1305971 7944277 := bbase (se 8 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 7944277 = 93097) (by norm_num)
theorem B4028549 : Blo 1305971 4028549 := bbase (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) (by norm_num)
theorem B2939021 : Blo 1305971 2939021 := bbase (se 3 (by rfl) ⟨551066, by rfl⟩ : syracuseStep 2939021 = 1102133) (by norm_num)
theorem B1652881 : Blo 1305971 1652881 := bbase (se 2 (by rfl) ⟨619830, by rfl⟩ : syracuseStep 1652881 = 1239661) (by norm_num)
theorem B4962485 : Blo 1305971 4962485 := bbase (se 5 (by rfl) ⟨232616, by rfl⟩ : syracuseStep 4962485 = 465233) (by norm_num)
theorem B2939093 : Blo 1305971 2939093 := bbase (se 7 (by rfl) ⟨34442, by rfl⟩ : syracuseStep 2939093 = 68885) (by norm_num)
theorem B1652977 : Blo 1305971 1652977 := bbase (se 2 (by rfl) ⟨619866, by rfl⟩ : syracuseStep 1652977 = 1239733) (by norm_num)
theorem B2939165 : Blo 1305971 2939165 := bbase (se 3 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 2939165 = 1102187) (by norm_num)
theorem B9918773 : Blo 1305971 9918773 := bbase (se 5 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 9918773 = 929885) (by norm_num)
theorem B3307837 : Blo 1305971 3307837 := bbase (se 3 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 3307837 = 1240439) (by norm_num)
theorem B2480453 : Blo 1305971 2480453 := bbase (se 4 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 2480453 = 465085) (by norm_num)
theorem B2980181 : Blo 1305971 2980181 := bbase (se 10 (by rfl) ⟨4365, by rfl⟩ : syracuseStep 2980181 = 8731) (by norm_num)
theorem B2939237 : Blo 1305971 2939237 := bbase (se 4 (by rfl) ⟨275553, by rfl⟩ : syracuseStep 2939237 = 551107) (by norm_num)
theorem B4413797 : Blo 1305971 4413797 := bbase (se 4 (by rfl) ⟨413793, by rfl⟩ : syracuseStep 4413797 = 827587) (by norm_num)
theorem B9419125 : Blo 1305971 9419125 := bbase (se 5 (by rfl) ⟨441521, by rfl⟩ : syracuseStep 9419125 = 883043) (by norm_num)
theorem B1653149 : Blo 1305971 1653149 := bbase (se 3 (by rfl) ⟨309965, by rfl⟩ : syracuseStep 1653149 = 619931) (by norm_num)
theorem B2939309 : Blo 1305971 2939309 := bbase (se 3 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 2939309 = 1102241) (by norm_num)
theorem B3307949 : Blo 1305971 3307949 := bbase (se 3 (by rfl) ⟨620240, by rfl⟩ : syracuseStep 3307949 = 1240481) (by norm_num)
theorem B1571257 : Blo 1305971 1571257 := bbase (se 2 (by rfl) ⟨589221, by rfl⟩ : syracuseStep 1571257 = 1178443) (by norm_num)
theorem B1653205 : Blo 1305971 1653205 := bbase (se 7 (by rfl) ⟨19373, by rfl⟩ : syracuseStep 1653205 = 38747) (by norm_num)
theorem B2939381 : Blo 1305971 2939381 := bbase (se 5 (by rfl) ⟨137783, by rfl⟩ : syracuseStep 2939381 = 275567) (by norm_num)
theorem B1653301 : Blo 1305971 1653301 := bbase (se 5 (by rfl) ⟨77498, by rfl⟩ : syracuseStep 1653301 = 154997) (by norm_num)
theorem B2939453 : Blo 1305971 2939453 := bbase (se 3 (by rfl) ⟨551147, by rfl⟩ : syracuseStep 2939453 = 1102295) (by norm_num)
theorem B1342045 : Blo 1305971 1342045 := bbase (se 3 (by rfl) ⟨251633, by rfl⟩ : syracuseStep 1342045 = 503267) (by norm_num)
theorem B3308141 : Blo 1305971 3308141 := bbase (se 3 (by rfl) ⟨620276, by rfl⟩ : syracuseStep 3308141 = 1240553) (by norm_num)
theorem B2939525 : Blo 1305971 2939525 := bbase (se 4 (by rfl) ⟨275580, by rfl⟩ : syracuseStep 2939525 = 551161) (by norm_num)
theorem B7445141 : Blo 1305971 7445141 := bbase (se 6 (by rfl) ⟨174495, by rfl⟩ : syracuseStep 7445141 = 348991) (by norm_num)
theorem B3676837 : Blo 1305971 3676837 := bbase (se 4 (by rfl) ⟨344703, by rfl⟩ : syracuseStep 3676837 = 689407) (by norm_num)
theorem B2939597 : Blo 1305971 2939597 := bbase (se 3 (by rfl) ⟨551174, by rfl⟩ : syracuseStep 2939597 = 1102349) (by norm_num)
theorem B1325777 : Blo 1305971 1325777 := bbase (se 2 (by rfl) ⟨497166, by rfl⟩ : syracuseStep 1325777 = 994333) (by norm_num)
theorem B1653473 : Blo 1305971 1653473 := bbase (se 2 (by rfl) ⟨620052, by rfl⟩ : syracuseStep 1653473 = 1240105) (by norm_num)
theorem B4242149 : Blo 1305971 4242149 := bbase (se 4 (by rfl) ⟨397701, by rfl⟩ : syracuseStep 4242149 = 795403) (by norm_num)
theorem B6617861 : Blo 1305971 6617861 := bbase (se 4 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 6617861 = 1240849) (by norm_num)
theorem B2939669 : Blo 1305971 2939669 := bbase (se 6 (by rfl) ⟨68898, by rfl⟩ : syracuseStep 2939669 = 137797) (by norm_num)
theorem B4414229 : Blo 1305971 4414229 := bbase (se 6 (by rfl) ⟨103458, by rfl⟩ : syracuseStep 4414229 = 206917) (by norm_num)
theorem B1653529 : Blo 1305971 1653529 := bbase (se 2 (by rfl) ⟨620073, by rfl⟩ : syracuseStep 1653529 = 1240147) (by norm_num)
theorem B2792245 : Blo 1305971 2792245 := bbase (se 5 (by rfl) ⟨130886, by rfl⟩ : syracuseStep 2792245 = 261773) (by norm_num)
theorem B2939741 : Blo 1305971 2939741 := bbase (se 3 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 2939741 = 1102403) (by norm_num)
theorem B1653625 : Blo 1305971 1653625 := bbase (se 2 (by rfl) ⟨620109, by rfl⟩ : syracuseStep 1653625 = 1240219) (by norm_num)
theorem B2939813 : Blo 1305971 2939813 := bbase (se 4 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 2939813 = 551215) (by norm_num)
theorem B3308485 : Blo 1305971 3308485 := bbase (se 4 (by rfl) ⟨310170, by rfl⟩ : syracuseStep 3308485 = 620341) (by norm_num)
theorem B5659589 : Blo 1305971 5659589 := bbase (se 4 (by rfl) ⟨530586, by rfl⟩ : syracuseStep 5659589 = 1061173) (by norm_num)
theorem B2792389 : Blo 1305971 2792389 := bbase (se 4 (by rfl) ⟨261786, by rfl⟩ : syracuseStep 2792389 = 523573) (by norm_num)
theorem B4709333 : Blo 1305971 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B20126677 : Blo 1305971 20126677 := bbase (se 7 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 20126677 = 471719) (by norm_num)
theorem B2939885 : Blo 1305971 2939885 := bbase (se 3 (by rfl) ⟨551228, by rfl⟩ : syracuseStep 2939885 = 1102457) (by norm_num)
theorem B1653797 : Blo 1305971 1653797 := bbase (se 4 (by rfl) ⟨155043, by rfl⟩ : syracuseStep 1653797 = 310087) (by norm_num)
theorem B2939957 : Blo 1305971 2939957 := bbase (se 5 (by rfl) ⟨137810, by rfl⟩ : syracuseStep 2939957 = 275621) (by norm_num)
theorem B2481205 : Blo 1305971 2481205 := bbase (se 5 (by rfl) ⟨116306, by rfl⟩ : syracuseStep 2481205 = 232613) (by norm_num)
theorem B3308597 : Blo 1305971 3308597 := bbase (se 5 (by rfl) ⟨155090, by rfl⟩ : syracuseStep 3308597 = 310181) (by norm_num)
theorem B1653853 : Blo 1305971 1653853 := bbase (se 3 (by rfl) ⟨310097, by rfl⟩ : syracuseStep 1653853 = 620195) (by norm_num)
theorem B2940029 : Blo 1305971 2940029 := bbase (se 3 (by rfl) ⟨551255, by rfl⟩ : syracuseStep 2940029 = 1102511) (by norm_num)
theorem B1653949 : Blo 1305971 1653949 := bbase (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) (by norm_num)
theorem B2940101 : Blo 1305971 2940101 := bbase (se 4 (by rfl) ⟨275634, by rfl⟩ : syracuseStep 2940101 = 551269) (by norm_num)
theorem B2481349 : Blo 1305971 2481349 := bbase (se 4 (by rfl) ⟨232626, by rfl⟩ : syracuseStep 2481349 = 465253) (by norm_num)
theorem B5962949 : Blo 1305971 5962949 := bbase (se 4 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 5962949 = 1118053) (by norm_num)
theorem B3308789 : Blo 1305971 3308789 := bbase (se 5 (by rfl) ⟨155099, by rfl⟩ : syracuseStep 3308789 = 310199) (by norm_num)
theorem B2940173 : Blo 1305971 2940173 := bbase (se 3 (by rfl) ⟨551282, by rfl⟩ : syracuseStep 2940173 = 1102565) (by norm_num)
theorem B2792765 : Blo 1305971 2792765 := bbase (se 3 (by rfl) ⟨523643, by rfl⟩ : syracuseStep 2792765 = 1047287) (by norm_num)
theorem B2686285 : Blo 1305971 2686285 := bbase (se 3 (by rfl) ⟨503678, by rfl⟩ : syracuseStep 2686285 = 1007357) (by norm_num)
theorem B2940245 : Blo 1305971 2940245 := bbase (se 11 (by rfl) ⟨2153, by rfl⟩ : syracuseStep 2940245 = 4307) (by norm_num)
theorem B2481509 : Blo 1305971 2481509 := bbase (se 4 (by rfl) ⟨232641, by rfl⟩ : syracuseStep 2481509 = 465283) (by norm_num)
theorem B1490281 : Blo 1305971 1490281 := bbase (se 2 (by rfl) ⟨558855, by rfl⟩ : syracuseStep 1490281 = 1117711) (by norm_num)
theorem B1654121 : Blo 1305971 1654121 := bbase (se 2 (by rfl) ⟨620295, by rfl⟩ : syracuseStep 1654121 = 1240591) (by norm_num)
theorem B4709765 : Blo 1305971 4709765 := bbase (se 4 (by rfl) ⟨441540, by rfl⟩ : syracuseStep 4709765 = 883081) (by norm_num)
theorem B3022229 : Blo 1305971 3022229 := bbase (se 6 (by rfl) ⟨70833, by rfl⟩ : syracuseStep 3022229 = 141667) (by norm_num)
theorem B2940317 : Blo 1305971 2940317 := bbase (se 3 (by rfl) ⟨551309, by rfl⟩ : syracuseStep 2940317 = 1102619) (by norm_num)
theorem B1654177 : Blo 1305971 1654177 := bbase (se 2 (by rfl) ⟨620316, by rfl⟩ : syracuseStep 1654177 = 1240633) (by norm_num)
theorem B2940389 : Blo 1305971 2940389 := bbase (se 4 (by rfl) ⟨275661, by rfl⟩ : syracuseStep 2940389 = 551323) (by norm_num)
theorem B2481653 : Blo 1305971 2481653 := bbase (se 5 (by rfl) ⟨116327, by rfl⟩ : syracuseStep 2481653 = 232655) (by norm_num)
theorem B4472309 : Blo 1305971 4472309 := bbase (se 5 (by rfl) ⟨209639, by rfl⟩ : syracuseStep 4472309 = 419279) (by norm_num)
theorem B1654273 : Blo 1305971 1654273 := bbase (se 2 (by rfl) ⟨620352, by rfl⟩ : syracuseStep 1654273 = 1240705) (by norm_num)
theorem B2940461 : Blo 1305971 2940461 := bbase (se 3 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 2940461 = 1102673) (by norm_num)
theorem B7945781 : Blo 1305971 7945781 := bbase (se 5 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 7945781 = 744917) (by norm_num)
theorem B3309133 : Blo 1305971 3309133 := bbase (se 3 (by rfl) ⟨620462, by rfl⟩ : syracuseStep 3309133 = 1240925) (by norm_num)
theorem B2940533 : Blo 1305971 2940533 := bbase (se 5 (by rfl) ⟨137837, by rfl⟩ : syracuseStep 2940533 = 275675) (by norm_num)
theorem B6282917 : Blo 1305971 6282917 := bbase (se 4 (by rfl) ⟨589023, by rfl⟩ : syracuseStep 6282917 = 1178047) (by norm_num)
theorem B1654445 : Blo 1305971 1654445 := bbase (se 3 (by rfl) ⟨310208, by rfl⟩ : syracuseStep 1654445 = 620417) (by norm_num)
theorem B2793133 : Blo 1305971 2793133 := bbase (se 3 (by rfl) ⟨523712, by rfl⟩ : syracuseStep 2793133 = 1047425) (by norm_num)
theorem B2940605 : Blo 1305971 2940605 := bbase (se 3 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 2940605 = 1102727) (by norm_num)
theorem B3309245 : Blo 1305971 3309245 := bbase (se 3 (by rfl) ⟨620483, by rfl⟩ : syracuseStep 3309245 = 1240967) (by norm_num)
theorem B1490629 : Blo 1305971 1490629 := bbase (se 4 (by rfl) ⟨139746, by rfl⟩ : syracuseStep 1490629 = 279493) (by norm_num)
theorem B1654501 : Blo 1305971 1654501 := bbase (se 4 (by rfl) ⟨155109, by rfl⟩ : syracuseStep 1654501 = 310219) (by norm_num)
theorem B5586677 : Blo 1305971 5586677 := bbase (se 5 (by rfl) ⟨261875, by rfl⟩ : syracuseStep 5586677 = 523751) (by norm_num)
theorem B2940677 : Blo 1305971 2940677 := bbase (se 4 (by rfl) ⟨275688, by rfl⟩ : syracuseStep 2940677 = 551377) (by norm_num)
theorem B2481941 : Blo 1305971 2481941 := bbase (se 6 (by rfl) ⟨58170, by rfl⟩ : syracuseStep 2481941 = 116341) (by norm_num)
theorem B1654597 : Blo 1305971 1654597 := bbase (se 4 (by rfl) ⟨155118, by rfl⟩ : syracuseStep 1654597 = 310237) (by norm_num)
theorem B2940749 : Blo 1305971 2940749 := bbase (se 3 (by rfl) ⟨551390, by rfl⟩ : syracuseStep 2940749 = 1102781) (by norm_num)
theorem B11165525 : Blo 1305971 11165525 := bbase (se 9 (by rfl) ⟨32711, by rfl⟩ : syracuseStep 11165525 = 65423) (by norm_num)
theorem B2236285 : Blo 1305971 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B3309437 : Blo 1305971 3309437 := bbase (se 3 (by rfl) ⟨620519, by rfl⟩ : syracuseStep 3309437 = 1241039) (by norm_num)
theorem B2940821 : Blo 1305971 2940821 := bbase (se 6 (by rfl) ⟨68925, by rfl⟩ : syracuseStep 2940821 = 137851) (by norm_num)
theorem B4186021 : Blo 1305971 4186021 := bbase (se 4 (by rfl) ⟨392439, by rfl⟩ : syracuseStep 4186021 = 784879) (by norm_num)
theorem B2482093 : Blo 1305971 2482093 := bbase (se 3 (by rfl) ⟨465392, by rfl⟩ : syracuseStep 2482093 = 930785) (by norm_num)
theorem B2940893 : Blo 1305971 2940893 := bbase (se 3 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 2940893 = 1102835) (by norm_num)
theorem B1654769 : Blo 1305971 1654769 := bbase (se 2 (by rfl) ⟨620538, by rfl⟩ : syracuseStep 1654769 = 1241077) (by norm_num)
theorem B4136995 : Blo 1305971 4136995 := bstep (se 1 (by rfl) ⟨3102746, by rfl⟩ : syracuseStep 4136995 = 6205493) B6205493
theorem B4964429 : Blo 1305971 4964429 := bstep (se 3 (by rfl) ⟨930830, by rfl⟩ : syracuseStep 4964429 = 1861661) B1861661
theorem B3719267 : Blo 1305971 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B10592369 : Blo 1305971 10592369 := bstep (se 2 (by rfl) ⟨3972138, by rfl⟩ : syracuseStep 10592369 = 7944277) B7944277
theorem B7069837 : Blo 1305971 7069837 := bstep (se 3 (by rfl) ⟨1325594, by rfl⟩ : syracuseStep 7069837 = 2651189) B2651189
theorem B2941073 : Blo 1305971 2941073 := bstep (se 2 (by rfl) ⟨1102902, by rfl⟩ : syracuseStep 2941073 = 2205805) B2205805
theorem B2482321 : Blo 1305971 2482321 := bstep (se 2 (by rfl) ⟨930870, by rfl⟩ : syracuseStep 2482321 = 1861741) B1861741
theorem B1654931 : Blo 1305971 1654931 := bstep (se 1 (by rfl) ⟨1241198, by rfl⟩ : syracuseStep 1654931 = 2482397) B2482397
theorem B2941091 : Blo 1305971 2941091 := bstep (se 1 (by rfl) ⟨2205818, by rfl⟩ : syracuseStep 2941091 = 4411637) B4411637
theorem B3309731 : Blo 1305971 3309731 := bstep (se 1 (by rfl) ⟨2482298, by rfl⟩ : syracuseStep 3309731 = 4964597) B4964597
theorem B2203841 : Blo 1305971 2203841 := bstep (se 2 (by rfl) ⟨826440, by rfl⟩ : syracuseStep 2203841 = 1652881) B1652881
theorem B8372429 : Blo 1305971 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B2482481 : Blo 1305971 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B2203969 : Blo 1305971 2203969 := bstep (se 2 (by rfl) ⟨826488, by rfl⟩ : syracuseStep 2203969 = 1652977) B1652977
theorem B2204003 : Blo 1305971 2204003 := bstep (se 1 (by rfl) ⟨1653002, by rfl⟩ : syracuseStep 2204003 = 3306005) B3306005
theorem B3309923 : Blo 1305971 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B7954787 : Blo 1305971 7954787 := bstep (se 1 (by rfl) ⟨5966090, by rfl⟩ : syracuseStep 7954787 = 11932181) B11932181
theorem B7446917 : Blo 1305971 7446917 := bstep (se 4 (by rfl) ⟨698148, by rfl⟩ : syracuseStep 7446917 = 1396297) B1396297
theorem B2941361 : Blo 1305971 2941361 := bstep (se 2 (by rfl) ⟨1103010, by rfl⟩ : syracuseStep 2941361 = 2206021) B2206021
theorem B2941379 : Blo 1305971 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B12566981 : Blo 1305971 12566981 := bstep (se 4 (by rfl) ⟨1178154, by rfl⟩ : syracuseStep 12566981 = 2356309) B2356309
theorem B2204131 : Blo 1305971 2204131 := bstep (se 1 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 2204131 = 3306197) B3306197
theorem B12247537 : Blo 1305971 12247537 := bstep (se 2 (by rfl) ⟨4592826, by rfl⟩ : syracuseStep 12247537 = 9185653) B9185653
theorem B12558833 : Blo 1305971 12558833 := bstep (se 2 (by rfl) ⟨4709562, by rfl⟩ : syracuseStep 12558833 = 9419125) B9419125
theorem B4186637 : Blo 1305971 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B4407857 : Blo 1305971 4407857 := bstep (se 2 (by rfl) ⟨1652946, by rfl⟩ : syracuseStep 4407857 = 3305893) B3305893
theorem B84754997 : Blo 1305971 84754997 := bstep (se 5 (by rfl) ⟨3972890, by rfl⟩ : syracuseStep 84754997 = 7945781) B7945781
theorem B2204273 : Blo 1305971 2204273 := bstep (se 2 (by rfl) ⟨826602, by rfl⟩ : syracuseStep 2204273 = 1653205) B1653205
theorem B13091441 : Blo 1305971 13091441 := bstep (se 2 (by rfl) ⟨4909290, by rfl⟩ : syracuseStep 13091441 = 9818581) B9818581
theorem B2482883 : Blo 1305971 2482883 := bstep (se 1 (by rfl) ⟨1862162, by rfl⟩ : syracuseStep 2482883 = 3724325) B3724325
theorem B4186829 : Blo 1305971 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B2941649 : Blo 1305971 2941649 := bstep (se 2 (by rfl) ⟨1103118, by rfl⟩ : syracuseStep 2941649 = 2206237) B2206237
theorem B2941667 : Blo 1305971 2941667 := bstep (se 1 (by rfl) ⟨2206250, by rfl⟩ : syracuseStep 2941667 = 4412501) B4412501
theorem B2204401 : Blo 1305971 2204401 := bstep (se 2 (by rfl) ⟨826650, by rfl⟩ : syracuseStep 2204401 = 1653301) B1653301
theorem B2204435 : Blo 1305971 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B4473635 : Blo 1305971 4473635 := bstep (se 1 (by rfl) ⟨3355226, by rfl⟩ : syracuseStep 4473635 = 6710453) B6710453
theorem B1860403 : Blo 1305971 1860403 := bstep (se 1 (by rfl) ⟨1395302, by rfl⟩ : syracuseStep 1860403 = 2790605) B2790605
theorem B7447373 : Blo 1305971 7447373 := bstep (se 3 (by rfl) ⟨1396382, by rfl⟩ : syracuseStep 7447373 = 2792765) B2792765
theorem B3720077 : Blo 1305971 3720077 := bstep (se 3 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 3720077 = 1395029) B1395029
theorem B2204563 : Blo 1305971 2204563 := bstep (se 1 (by rfl) ⟨1653422, by rfl⟩ : syracuseStep 2204563 = 3306845) B3306845
theorem B1860499 : Blo 1305971 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B7439309 : Blo 1305971 7439309 := bstep (se 3 (by rfl) ⟨1394870, by rfl⟩ : syracuseStep 7439309 = 2789741) B2789741
theorem B4031441 : Blo 1305971 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B4711409 : Blo 1305971 4711409 := bstep (se 2 (by rfl) ⟨1766778, by rfl⟩ : syracuseStep 4711409 = 3533557) B3533557
theorem B2941937 : Blo 1305971 2941937 := bstep (se 2 (by rfl) ⟨1103226, by rfl⟩ : syracuseStep 2941937 = 2206453) B2206453
theorem B2941955 : Blo 1305971 2941955 := bstep (se 1 (by rfl) ⟨2206466, by rfl⟩ : syracuseStep 2941955 = 4412933) B4412933
theorem B12559373 : Blo 1305971 12559373 := bstep (se 3 (by rfl) ⟨2354882, by rfl⟩ : syracuseStep 12559373 = 4709765) B4709765
theorem B2204705 : Blo 1305971 2204705 := bstep (se 2 (by rfl) ⟨826764, by rfl⟩ : syracuseStep 2204705 = 1653529) B1653529
theorem B1958963 : Blo 1305971 1958963 := bstep (se 1 (by rfl) ⟨1469222, by rfl⟩ : syracuseStep 1958963 = 2938445) B2938445
theorem B4408397 : Blo 1305971 4408397 := bstep (se 3 (by rfl) ⟨826574, by rfl⟩ : syracuseStep 4408397 = 1653149) B1653149
theorem B3720269 : Blo 1305971 3720269 := bstep (se 3 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 3720269 = 1395101) B1395101
theorem B1958993 : Blo 1305971 1958993 := bstep (se 2 (by rfl) ⟨734622, by rfl⟩ : syracuseStep 1958993 = 1469245) B1469245
theorem B1959011 : Blo 1305971 1959011 := bstep (se 1 (by rfl) ⟨1469258, by rfl⟩ : syracuseStep 1959011 = 2938517) B2938517
theorem B1885297 : Blo 1305971 1885297 := bstep (se 2 (by rfl) ⟨706986, by rfl⟩ : syracuseStep 1885297 = 1413973) B1413973
theorem B5661809 : Blo 1305971 5661809 := bstep (se 2 (by rfl) ⟨2123178, by rfl⟩ : syracuseStep 5661809 = 4246357) B4246357
theorem B1959041 : Blo 1305971 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B4408451 : Blo 1305971 4408451 := bstep (se 1 (by rfl) ⟨3306338, by rfl⟩ : syracuseStep 4408451 = 6612677) B6612677
theorem B1959059 : Blo 1305971 1959059 := bstep (se 1 (by rfl) ⟨1469294, by rfl⟩ : syracuseStep 1959059 = 2938589) B2938589
theorem B2204833 : Blo 1305971 2204833 := bstep (se 2 (by rfl) ⟨826812, by rfl⟩ : syracuseStep 2204833 = 1653625) B1653625
theorem B6710435 : Blo 1305971 6710435 := bstep (se 1 (by rfl) ⟨5032826, by rfl⟩ : syracuseStep 6710435 = 10065653) B10065653
theorem B1959089 : Blo 1305971 1959089 := bstep (se 2 (by rfl) ⟨734658, by rfl⟩ : syracuseStep 1959089 = 1469317) B1469317
theorem B1959107 : Blo 1305971 1959107 := bstep (se 1 (by rfl) ⟨1469330, by rfl⟩ : syracuseStep 1959107 = 2938661) B2938661
theorem B2204867 : Blo 1305971 2204867 := bstep (se 1 (by rfl) ⟨1653650, by rfl⟩ : syracuseStep 2204867 = 3307301) B3307301
theorem B1959137 : Blo 1305971 1959137 := bstep (se 2 (by rfl) ⟨734676, by rfl⟩ : syracuseStep 1959137 = 1469353) B1469353
theorem B1959155 : Blo 1305971 1959155 := bstep (se 1 (by rfl) ⟨1469366, by rfl⟩ : syracuseStep 1959155 = 2938733) B2938733
theorem B1959185 : Blo 1305971 1959185 := bstep (se 2 (by rfl) ⟨734694, by rfl⟩ : syracuseStep 1959185 = 1469389) B1469389
theorem B2942225 : Blo 1305971 2942225 := bstep (se 2 (by rfl) ⟨1103334, by rfl⟩ : syracuseStep 2942225 = 2206669) B2206669
theorem B1959203 : Blo 1305971 1959203 := bstep (se 1 (by rfl) ⟨1469402, by rfl⟩ : syracuseStep 1959203 = 2938805) B2938805
theorem B2942243 : Blo 1305971 2942243 := bstep (se 1 (by rfl) ⟨2206682, by rfl⟩ : syracuseStep 2942243 = 4413365) B4413365
theorem B1959233 : Blo 1305971 1959233 := bstep (se 2 (by rfl) ⟨734712, by rfl⟩ : syracuseStep 1959233 = 1469425) B1469425
theorem B2204995 : Blo 1305971 2204995 := bstep (se 1 (by rfl) ⟨1653746, by rfl⟩ : syracuseStep 2204995 = 3307493) B3307493
theorem B1959251 : Blo 1305971 1959251 := bstep (se 1 (by rfl) ⟨1469438, by rfl⟩ : syracuseStep 1959251 = 2938877) B2938877
theorem B1959281 : Blo 1305971 1959281 := bstep (se 2 (by rfl) ⟨734730, by rfl⟩ : syracuseStep 1959281 = 1469461) B1469461
theorem B1959299 : Blo 1305971 1959299 := bstep (se 1 (by rfl) ⟨1469474, by rfl⟩ : syracuseStep 1959299 = 2938949) B2938949
theorem B1860995 : Blo 1305971 1860995 := bstep (se 1 (by rfl) ⟨1395746, by rfl⟩ : syracuseStep 1860995 = 2791493) B2791493
theorem B4408721 : Blo 1305971 4408721 := bstep (se 2 (by rfl) ⟨1653270, by rfl⟩ : syracuseStep 4408721 = 3306541) B3306541
theorem B1959329 : Blo 1305971 1959329 := bstep (se 2 (by rfl) ⟨734748, by rfl⟩ : syracuseStep 1959329 = 1469497) B1469497
theorem B1959347 : Blo 1305971 1959347 := bstep (se 1 (by rfl) ⟨1469510, by rfl⟩ : syracuseStep 1959347 = 2939021) B2939021
theorem B1959377 : Blo 1305971 1959377 := bstep (se 2 (by rfl) ⟨734766, by rfl⟩ : syracuseStep 1959377 = 1469533) B1469533
theorem B2205137 : Blo 1305971 2205137 := bstep (se 2 (by rfl) ⟨826926, by rfl⟩ : syracuseStep 2205137 = 1653853) B1653853
theorem B1959395 : Blo 1305971 1959395 := bstep (se 1 (by rfl) ⟨1469546, by rfl⟩ : syracuseStep 1959395 = 2939093) B2939093
theorem B1959425 : Blo 1305971 1959425 := bstep (se 2 (by rfl) ⟨734784, by rfl⟩ : syracuseStep 1959425 = 1469569) B1469569
theorem B1959443 : Blo 1305971 1959443 := bstep (se 1 (by rfl) ⟨1469582, by rfl⟩ : syracuseStep 1959443 = 2939165) B2939165
theorem B6612515 : Blo 1305971 6612515 := bstep (se 1 (by rfl) ⟨4959386, by rfl⟩ : syracuseStep 6612515 = 9918773) B9918773
theorem B1959473 : Blo 1305971 1959473 := bstep (se 2 (by rfl) ⟨734802, by rfl⟩ : syracuseStep 1959473 = 1469605) B1469605
theorem B2942513 : Blo 1305971 2942513 := bstep (se 2 (by rfl) ⟨1103442, by rfl⟩ : syracuseStep 2942513 = 2206885) B2206885
theorem B1959491 : Blo 1305971 1959491 := bstep (se 1 (by rfl) ⟨1469618, by rfl⟩ : syracuseStep 1959491 = 2939237) B2939237
theorem B2123329 : Blo 1305971 2123329 := bstep (se 2 (by rfl) ⟨796248, by rfl⟩ : syracuseStep 2123329 = 1592497) B1592497
theorem B2942531 : Blo 1305971 2942531 := bstep (se 1 (by rfl) ⟨2206898, by rfl⟩ : syracuseStep 2942531 = 4413797) B4413797
theorem B2205265 : Blo 1305971 2205265 := bstep (se 2 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 2205265 = 1653949) B1653949
theorem B1959521 : Blo 1305971 1959521 := bstep (se 2 (by rfl) ⟨734820, by rfl⟩ : syracuseStep 1959521 = 1469641) B1469641
theorem B1959539 : Blo 1305971 1959539 := bstep (se 1 (by rfl) ⟨1469654, by rfl⟩ : syracuseStep 1959539 = 2939309) B2939309
theorem B2205299 : Blo 1305971 2205299 := bstep (se 1 (by rfl) ⟨1653974, by rfl⟩ : syracuseStep 2205299 = 3307949) B3307949
theorem B1959569 : Blo 1305971 1959569 := bstep (se 2 (by rfl) ⟨734838, by rfl⟩ : syracuseStep 1959569 = 1469677) B1469677
theorem B1959587 : Blo 1305971 1959587 := bstep (se 1 (by rfl) ⟨1469690, by rfl⟩ : syracuseStep 1959587 = 2939381) B2939381
theorem B1959617 : Blo 1305971 1959617 := bstep (se 2 (by rfl) ⟨734856, by rfl⟩ : syracuseStep 1959617 = 1469713) B1469713
theorem B9930437 : Blo 1305971 9930437 := bstep (se 4 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 9930437 = 1861957) B1861957
theorem B1959635 : Blo 1305971 1959635 := bstep (se 1 (by rfl) ⟨1469726, by rfl⟩ : syracuseStep 1959635 = 2939453) B2939453
theorem B1959665 : Blo 1305971 1959665 := bstep (se 2 (by rfl) ⟨734874, by rfl⟩ : syracuseStep 1959665 = 1469749) B1469749
theorem B2205427 : Blo 1305971 2205427 := bstep (se 1 (by rfl) ⟨1654070, by rfl⟩ : syracuseStep 2205427 = 3308141) B3308141
theorem B1959683 : Blo 1305971 1959683 := bstep (se 1 (by rfl) ⟨1469762, by rfl⟩ : syracuseStep 1959683 = 2939525) B2939525
theorem B3581713 : Blo 1305971 3581713 := bstep (se 2 (by rfl) ⟨1343142, by rfl⟩ : syracuseStep 3581713 = 2686285) B2686285
theorem B1959713 : Blo 1305971 1959713 := bstep (se 2 (by rfl) ⟨734892, by rfl⟩ : syracuseStep 1959713 = 1469785) B1469785
theorem B1959731 : Blo 1305971 1959731 := bstep (se 1 (by rfl) ⟨1469798, by rfl⟩ : syracuseStep 1959731 = 2939597) B2939597
theorem B2828099 : Blo 1305971 2828099 := bstep (se 1 (by rfl) ⟨2121074, by rfl⟩ : syracuseStep 2828099 = 4242149) B4242149
theorem B1959761 : Blo 1305971 1959761 := bstep (se 2 (by rfl) ⟨734910, by rfl⟩ : syracuseStep 1959761 = 1469821) B1469821
theorem B2942801 : Blo 1305971 2942801 := bstep (se 2 (by rfl) ⟨1103550, by rfl⟩ : syracuseStep 2942801 = 2207101) B2207101
theorem B1959779 : Blo 1305971 1959779 := bstep (se 1 (by rfl) ⟨1469834, by rfl⟩ : syracuseStep 1959779 = 2939669) B2939669
theorem B2942819 : Blo 1305971 2942819 := bstep (se 1 (by rfl) ⟨2207114, by rfl⟩ : syracuseStep 2942819 = 4414229) B4414229
theorem B22644593 : Blo 1305971 22644593 := bstep (se 2 (by rfl) ⟨8491722, by rfl⟩ : syracuseStep 22644593 = 16983445) B16983445
theorem B1959809 : Blo 1305971 1959809 := bstep (se 2 (by rfl) ⟨734928, by rfl⟩ : syracuseStep 1959809 = 1469857) B1469857
theorem B2205569 : Blo 1305971 2205569 := bstep (se 2 (by rfl) ⟨827088, by rfl⟩ : syracuseStep 2205569 = 1654177) B1654177
theorem B1959827 : Blo 1305971 1959827 := bstep (se 1 (by rfl) ⟨1469870, by rfl⟩ : syracuseStep 1959827 = 2939741) B2939741
theorem B4409261 : Blo 1305971 4409261 := bstep (se 3 (by rfl) ⟨826736, by rfl⟩ : syracuseStep 4409261 = 1653473) B1653473
theorem B1959857 : Blo 1305971 1959857 := bstep (se 2 (by rfl) ⟨734946, by rfl⟩ : syracuseStep 1959857 = 1469893) B1469893
theorem B1959875 : Blo 1305971 1959875 := bstep (se 1 (by rfl) ⟨1469906, by rfl⟩ : syracuseStep 1959875 = 2939813) B2939813
theorem B1959905 : Blo 1305971 1959905 := bstep (se 2 (by rfl) ⟨734964, by rfl⟩ : syracuseStep 1959905 = 1469929) B1469929
theorem B4409315 : Blo 1305971 4409315 := bstep (se 1 (by rfl) ⟨3306986, by rfl⟩ : syracuseStep 4409315 = 6613973) B6613973
theorem B3139555 : Blo 1305971 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B1959923 : Blo 1305971 1959923 := bstep (se 1 (by rfl) ⟨1469942, by rfl⟩ : syracuseStep 1959923 = 2939885) B2939885
theorem B2205697 : Blo 1305971 2205697 := bstep (se 2 (by rfl) ⟨827136, by rfl⟩ : syracuseStep 2205697 = 1654273) B1654273
theorem B1861633 : Blo 1305971 1861633 := bstep (se 2 (by rfl) ⟨698112, by rfl⟩ : syracuseStep 1861633 = 1396225) B1396225
theorem B1959953 : Blo 1305971 1959953 := bstep (se 2 (by rfl) ⟨734982, by rfl⟩ : syracuseStep 1959953 = 1469965) B1469965
theorem B1959971 : Blo 1305971 1959971 := bstep (se 1 (by rfl) ⟨1469978, by rfl⟩ : syracuseStep 1959971 = 2939957) B2939957
theorem B1591331 : Blo 1305971 1591331 := bstep (se 1 (by rfl) ⟨1193498, by rfl⟩ : syracuseStep 1591331 = 2386997) B2386997
theorem B2205731 : Blo 1305971 2205731 := bstep (se 1 (by rfl) ⟨1654298, by rfl⟩ : syracuseStep 2205731 = 3308597) B3308597
theorem B3721261 : Blo 1305971 3721261 := bstep (se 3 (by rfl) ⟨697736, by rfl⟩ : syracuseStep 3721261 = 1395473) B1395473
theorem B6277169 : Blo 1305971 6277169 := bstep (se 2 (by rfl) ⟨2353938, by rfl⟩ : syracuseStep 6277169 = 4707877) B4707877
theorem B1960001 : Blo 1305971 1960001 := bstep (se 2 (by rfl) ⟨735000, by rfl⟩ : syracuseStep 1960001 = 1470001) B1470001
theorem B1960019 : Blo 1305971 1960019 := bstep (se 1 (by rfl) ⟨1470014, by rfl⟩ : syracuseStep 1960019 = 2940029) B2940029
theorem B1960049 : Blo 1305971 1960049 := bstep (se 2 (by rfl) ⟨735018, by rfl⟩ : syracuseStep 1960049 = 1470037) B1470037
theorem B1960067 : Blo 1305971 1960067 := bstep (se 1 (by rfl) ⟨1470050, by rfl⟩ : syracuseStep 1960067 = 2940101) B2940101
theorem B3975299 : Blo 1305971 3975299 := bstep (se 1 (by rfl) ⟨2981474, by rfl⟩ : syracuseStep 3975299 = 5962949) B5962949
theorem B1960097 : Blo 1305971 1960097 := bstep (se 2 (by rfl) ⟨735036, by rfl⟩ : syracuseStep 1960097 = 1470073) B1470073
theorem B2205859 : Blo 1305971 2205859 := bstep (se 1 (by rfl) ⟨1654394, by rfl⟩ : syracuseStep 2205859 = 3308789) B3308789
theorem B1960115 : Blo 1305971 1960115 := bstep (se 1 (by rfl) ⟨1470086, by rfl⟩ : syracuseStep 1960115 = 2940173) B2940173
theorem B14141621 : Blo 1305971 14141621 := bstep (se 5 (by rfl) ⟨662888, by rfl⟩ : syracuseStep 14141621 = 1325777) B1325777
theorem B1960145 : Blo 1305971 1960145 := bstep (se 2 (by rfl) ⟨735054, by rfl⟩ : syracuseStep 1960145 = 1470109) B1470109
theorem B1960163 : Blo 1305971 1960163 := bstep (se 1 (by rfl) ⟨1470122, by rfl⟩ : syracuseStep 1960163 = 2940245) B2940245
theorem B4409585 : Blo 1305971 4409585 := bstep (se 2 (by rfl) ⟨1653594, by rfl⟩ : syracuseStep 4409585 = 3307189) B3307189
theorem B6621425 : Blo 1305971 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1960193 : Blo 1305971 1960193 := bstep (se 2 (by rfl) ⟨735072, by rfl⟩ : syracuseStep 1960193 = 1470145) B1470145
theorem B1960211 : Blo 1305971 1960211 := bstep (se 1 (by rfl) ⟨1470158, by rfl⟩ : syracuseStep 1960211 = 2940317) B2940317
theorem B1960241 : Blo 1305971 1960241 := bstep (se 2 (by rfl) ⟨735090, by rfl⟩ : syracuseStep 1960241 = 1470181) B1470181
theorem B2206001 : Blo 1305971 2206001 := bstep (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) B1654501
theorem B1960259 : Blo 1305971 1960259 := bstep (se 1 (by rfl) ⟨1470194, by rfl⟩ : syracuseStep 1960259 = 2940389) B2940389
theorem B6613325 : Blo 1305971 6613325 := bstep (se 3 (by rfl) ⟨1239998, by rfl⟩ : syracuseStep 6613325 = 2479997) B2479997
theorem B1861969 : Blo 1305971 1861969 := bstep (se 2 (by rfl) ⟨698238, by rfl⟩ : syracuseStep 1861969 = 1396477) B1396477
theorem B1960289 : Blo 1305971 1960289 := bstep (se 2 (by rfl) ⟨735108, by rfl⟩ : syracuseStep 1960289 = 1470217) B1470217
theorem B1960307 : Blo 1305971 1960307 := bstep (se 1 (by rfl) ⟨1470230, by rfl⟩ : syracuseStep 1960307 = 2940461) B2940461
theorem B1960337 : Blo 1305971 1960337 := bstep (se 2 (by rfl) ⟨735126, by rfl⟩ : syracuseStep 1960337 = 1470253) B1470253
theorem B1960355 : Blo 1305971 1960355 := bstep (se 1 (by rfl) ⟨1470266, by rfl⟩ : syracuseStep 1960355 = 2940533) B2940533
theorem B2206129 : Blo 1305971 2206129 := bstep (se 2 (by rfl) ⟨827298, by rfl⟩ : syracuseStep 2206129 = 1654597) B1654597
theorem B1960385 : Blo 1305971 1960385 := bstep (se 2 (by rfl) ⟨735144, by rfl⟩ : syracuseStep 1960385 = 1470289) B1470289
theorem B4188611 : Blo 1305971 4188611 := bstep (se 1 (by rfl) ⟨3141458, by rfl⟩ : syracuseStep 4188611 = 6282917) B6282917
theorem B1960403 : Blo 1305971 1960403 := bstep (se 1 (by rfl) ⟨1470302, by rfl⟩ : syracuseStep 1960403 = 2940605) B2940605
theorem B2206163 : Blo 1305971 2206163 := bstep (se 1 (by rfl) ⟨1654622, by rfl⟩ : syracuseStep 2206163 = 3309245) B3309245
theorem B1960433 : Blo 1305971 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B1960451 : Blo 1305971 1960451 := bstep (se 1 (by rfl) ⟨1470338, by rfl⟩ : syracuseStep 1960451 = 2940677) B2940677
theorem B15092237 : Blo 1305971 15092237 := bstep (se 3 (by rfl) ⟨2829794, by rfl⟩ : syracuseStep 15092237 = 5659589) B5659589
theorem B1960481 : Blo 1305971 1960481 := bstep (se 2 (by rfl) ⟨735180, by rfl⟩ : syracuseStep 1960481 = 1470361) B1470361
theorem B5581361 : Blo 1305971 5581361 := bstep (se 2 (by rfl) ⟨2093010, by rfl⟩ : syracuseStep 5581361 = 4186021) B4186021
theorem B1960499 : Blo 1305971 1960499 := bstep (se 1 (by rfl) ⟨1470374, by rfl⟩ : syracuseStep 1960499 = 2940749) B2940749
theorem B1960529 : Blo 1305971 1960529 := bstep (se 2 (by rfl) ⟨735198, by rfl⟩ : syracuseStep 1960529 = 1470397) B1470397
theorem B2206291 : Blo 1305971 2206291 := bstep (se 1 (by rfl) ⟨1654718, by rfl⟩ : syracuseStep 2206291 = 3309437) B3309437
theorem B1960547 : Blo 1305971 1960547 := bstep (se 1 (by rfl) ⟨1470410, by rfl⟩ : syracuseStep 1960547 = 2940821) B2940821
theorem B1960577 : Blo 1305971 1960577 := bstep (se 2 (by rfl) ⟨735216, by rfl⟩ : syracuseStep 1960577 = 1470433) B1470433
theorem B1960595 : Blo 1305971 1960595 := bstep (se 1 (by rfl) ⟨1470446, by rfl⟩ : syracuseStep 1960595 = 2940893) B2940893
theorem B1960625 : Blo 1305971 1960625 := bstep (se 2 (by rfl) ⟨735234, by rfl⟩ : syracuseStep 1960625 = 1470469) B1470469
theorem B1886899 : Blo 1305971 1886899 := bstep (se 1 (by rfl) ⟨1415174, by rfl⟩ : syracuseStep 1886899 = 2830349) B2830349
theorem B1960643 : Blo 1305971 1960643 := bstep (se 1 (by rfl) ⟨1470482, by rfl⟩ : syracuseStep 1960643 = 2940965) B2940965
theorem B1960673 : Blo 1305971 1960673 := bstep (se 2 (by rfl) ⟨735252, by rfl⟩ : syracuseStep 1960673 = 1470505) B1470505
theorem B2206433 : Blo 1305971 2206433 := bstep (se 2 (by rfl) ⟨827412, by rfl⟩ : syracuseStep 2206433 = 1654825) B1654825
theorem B4246253 : Blo 1305971 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B1960691 : Blo 1305971 1960691 := bstep (se 1 (by rfl) ⟨1470518, by rfl⟩ : syracuseStep 1960691 = 2941037) B2941037
theorem B4410125 : Blo 1305971 4410125 := bstep (se 3 (by rfl) ⟨826898, by rfl⟩ : syracuseStep 4410125 = 1653797) B1653797
theorem B1960721 : Blo 1305971 1960721 := bstep (se 2 (by rfl) ⟨735270, by rfl⟩ : syracuseStep 1960721 = 1470541) B1470541
theorem B1960739 : Blo 1305971 1960739 := bstep (se 1 (by rfl) ⟨1470554, by rfl⟩ : syracuseStep 1960739 = 2941109) B2941109
theorem B1960769 : Blo 1305971 1960769 := bstep (se 2 (by rfl) ⟨735288, by rfl⟩ : syracuseStep 1960769 = 1470577) B1470577
theorem B4410179 : Blo 1305971 4410179 := bstep (se 1 (by rfl) ⟨3307634, by rfl⟩ : syracuseStep 4410179 = 6615269) B6615269
theorem B4959053 : Blo 1305971 4959053 := bstep (se 3 (by rfl) ⟨929822, by rfl⟩ : syracuseStep 4959053 = 1859645) B1859645
theorem B1960787 : Blo 1305971 1960787 := bstep (se 1 (by rfl) ⟨1470590, by rfl⟩ : syracuseStep 1960787 = 2941181) B2941181
theorem B2206561 : Blo 1305971 2206561 := bstep (se 2 (by rfl) ⟨827460, by rfl⟩ : syracuseStep 2206561 = 1654921) B1654921
theorem B1960817 : Blo 1305971 1960817 := bstep (se 2 (by rfl) ⟨735306, by rfl⟩ : syracuseStep 1960817 = 1470613) B1470613
theorem B1469299 : Blo 1305971 1469299 := bstep (se 1 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 1469299 = 2203949) B2203949
theorem B1960835 : Blo 1305971 1960835 := bstep (se 1 (by rfl) ⟨1470626, by rfl⟩ : syracuseStep 1960835 = 2941253) B2941253
theorem B2206595 : Blo 1305971 2206595 := bstep (se 1 (by rfl) ⟨1654946, by rfl⟩ : syracuseStep 2206595 = 3309893) B3309893
theorem B1960865 : Blo 1305971 1960865 := bstep (se 2 (by rfl) ⟨735324, by rfl⟩ : syracuseStep 1960865 = 1470649) B1470649
theorem B3140515 : Blo 1305971 3140515 := bstep (se 1 (by rfl) ⟨2355386, by rfl⟩ : syracuseStep 3140515 = 4710773) B4710773
theorem B1960883 : Blo 1305971 1960883 := bstep (se 1 (by rfl) ⟨1470662, by rfl⟩ : syracuseStep 1960883 = 2941325) B2941325
theorem B6278093 : Blo 1305971 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B1960913 : Blo 1305971 1960913 := bstep (se 2 (by rfl) ⟨735342, by rfl⟩ : syracuseStep 1960913 = 1470685) B1470685
theorem B1960931 : Blo 1305971 1960931 := bstep (se 1 (by rfl) ⟨1470698, by rfl⟩ : syracuseStep 1960931 = 2941397) B2941397
theorem B1960961 : Blo 1305971 1960961 := bstep (se 2 (by rfl) ⟨735360, by rfl⟩ : syracuseStep 1960961 = 1470721) B1470721
theorem B1469443 : Blo 1305971 1469443 := bstep (se 1 (by rfl) ⟨1102082, by rfl⟩ : syracuseStep 1469443 = 2204165) B2204165
theorem B2206723 : Blo 1305971 2206723 := bstep (se 1 (by rfl) ⟨1655042, by rfl⟩ : syracuseStep 2206723 = 3310085) B3310085
theorem B10742797 : Blo 1305971 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B1960979 : Blo 1305971 1960979 := bstep (se 1 (by rfl) ⟨1470734, by rfl⟩ : syracuseStep 1960979 = 2941469) B2941469
theorem B1961009 : Blo 1305971 1961009 := bstep (se 2 (by rfl) ⟨735378, by rfl⟩ : syracuseStep 1961009 = 1470757) B1470757
theorem B1961027 : Blo 1305971 1961027 := bstep (se 1 (by rfl) ⟨1470770, by rfl⟩ : syracuseStep 1961027 = 2941541) B2941541
theorem B4410449 : Blo 1305971 4410449 := bstep (se 2 (by rfl) ⟨1653918, by rfl⟩ : syracuseStep 4410449 = 3307837) B3307837
theorem B1961057 : Blo 1305971 1961057 := bstep (se 2 (by rfl) ⟨735396, by rfl⟩ : syracuseStep 1961057 = 1470793) B1470793
theorem B5958755 : Blo 1305971 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B1961075 : Blo 1305971 1961075 := bstep (se 1 (by rfl) ⟨1470806, by rfl⟩ : syracuseStep 1961075 = 2941613) B2941613
theorem B7441541 : Blo 1305971 7441541 := bstep (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) B1395289
theorem B2354321 : Blo 1305971 2354321 := bstep (se 2 (by rfl) ⟨882870, by rfl⟩ : syracuseStep 2354321 = 1765741) B1765741
theorem B1961105 : Blo 1305971 1961105 := bstep (se 2 (by rfl) ⟨735414, by rfl⟩ : syracuseStep 1961105 = 1470829) B1470829
theorem B1469587 : Blo 1305971 1469587 := bstep (se 1 (by rfl) ⟨1102190, by rfl⟩ : syracuseStep 1469587 = 2204381) B2204381
theorem B2206865 : Blo 1305971 2206865 := bstep (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) B1655149
theorem B1961123 : Blo 1305971 1961123 := bstep (se 1 (by rfl) ⟨1470842, by rfl⟩ : syracuseStep 1961123 = 2941685) B2941685
theorem B3140785 : Blo 1305971 3140785 := bstep (se 2 (by rfl) ⟨1177794, by rfl⟩ : syracuseStep 3140785 = 2355589) B2355589
theorem B1961153 : Blo 1305971 1961153 := bstep (se 2 (by rfl) ⟨735432, by rfl⟩ : syracuseStep 1961153 = 1470865) B1470865
theorem B1961171 : Blo 1305971 1961171 := bstep (se 1 (by rfl) ⟨1470878, by rfl⟩ : syracuseStep 1961171 = 2941757) B2941757
theorem B1961201 : Blo 1305971 1961201 := bstep (se 2 (by rfl) ⟨735450, by rfl⟩ : syracuseStep 1961201 = 1470901) B1470901
theorem B1961219 : Blo 1305971 1961219 := bstep (se 1 (by rfl) ⟨1470914, by rfl⟩ : syracuseStep 1961219 = 2941829) B2941829
theorem B2206993 : Blo 1305971 2206993 := bstep (se 2 (by rfl) ⟨827622, by rfl⟩ : syracuseStep 2206993 = 1655245) B1655245
theorem B1961249 : Blo 1305971 1961249 := bstep (se 2 (by rfl) ⟨735468, by rfl⟩ : syracuseStep 1961249 = 1470937) B1470937
theorem B1469731 : Blo 1305971 1469731 := bstep (se 1 (by rfl) ⟨1102298, by rfl⟩ : syracuseStep 1469731 = 2204597) B2204597
theorem B1961267 : Blo 1305971 1961267 := bstep (se 1 (by rfl) ⟨1470950, by rfl⟩ : syracuseStep 1961267 = 2941901) B2941901
theorem B2207027 : Blo 1305971 2207027 := bstep (se 1 (by rfl) ⟨1655270, by rfl⟩ : syracuseStep 2207027 = 3310541) B3310541
theorem B1961297 : Blo 1305971 1961297 := bstep (se 2 (by rfl) ⟨735486, by rfl⟩ : syracuseStep 1961297 = 1470973) B1470973
theorem B1961315 : Blo 1305971 1961315 := bstep (se 1 (by rfl) ⟨1470986, by rfl⟩ : syracuseStep 1961315 = 2941973) B2941973
theorem B1305971 : Blo 1305971 1305971 := bstep (se 1 (by rfl) ⟨979478, by rfl⟩ : syracuseStep 1305971 = 1958957) B1958957
theorem B1961345 : Blo 1305971 1961345 := bstep (se 2 (by rfl) ⟨735504, by rfl⟩ : syracuseStep 1961345 = 1471009) B1471009
theorem B1305987 : Blo 1305971 1305987 := bstep (se 1 (by rfl) ⟨979490, by rfl⟩ : syracuseStep 1305987 = 1958981) B1958981
theorem B1306003 : Blo 1305971 1306003 := bstep (se 1 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 1306003 = 1959005) B1959005
theorem B1961363 : Blo 1305971 1961363 := bstep (se 1 (by rfl) ⟨1471022, by rfl⟩ : syracuseStep 1961363 = 2942045) B2942045
theorem B1306019 : Blo 1305971 1306019 := bstep (se 1 (by rfl) ⟨979514, by rfl⟩ : syracuseStep 1306019 = 1959029) B1959029
theorem B2829745 : Blo 1305971 2829745 := bstep (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) B2122309
theorem B1961393 : Blo 1305971 1961393 := bstep (se 2 (by rfl) ⟨735522, by rfl⟩ : syracuseStep 1961393 = 1471045) B1471045
theorem B1306035 : Blo 1305971 1306035 := bstep (se 1 (by rfl) ⟨979526, by rfl⟩ : syracuseStep 1306035 = 1959053) B1959053
theorem B1469875 : Blo 1305971 1469875 := bstep (se 1 (by rfl) ⟨1102406, by rfl⟩ : syracuseStep 1469875 = 2204813) B2204813
theorem B2207155 : Blo 1305971 2207155 := bstep (se 1 (by rfl) ⟨1655366, by rfl⟩ : syracuseStep 2207155 = 3310733) B3310733
theorem B1306051 : Blo 1305971 1306051 := bstep (se 1 (by rfl) ⟨979538, by rfl⟩ : syracuseStep 1306051 = 1959077) B1959077
theorem B1961411 : Blo 1305971 1961411 := bstep (se 1 (by rfl) ⟨1471058, by rfl⟩ : syracuseStep 1961411 = 2942117) B2942117
theorem B1789393 : Blo 1305971 1789393 := bstep (se 2 (by rfl) ⟨671022, by rfl⟩ : syracuseStep 1789393 = 1342045) B1342045
theorem B1306067 : Blo 1305971 1306067 := bstep (se 1 (by rfl) ⟨979550, by rfl⟩ : syracuseStep 1306067 = 1959101) B1959101
theorem B1306083 : Blo 1305971 1306083 := bstep (se 1 (by rfl) ⟨979562, by rfl⟩ : syracuseStep 1306083 = 1959125) B1959125
theorem B11169251 : Blo 1305971 11169251 := bstep (se 1 (by rfl) ⟨8376938, by rfl⟩ : syracuseStep 11169251 = 16753877) B16753877
theorem B1961441 : Blo 1305971 1961441 := bstep (se 2 (by rfl) ⟨735540, by rfl⟩ : syracuseStep 1961441 = 1471081) B1471081
theorem B1306099 : Blo 1305971 1306099 := bstep (se 1 (by rfl) ⟨979574, by rfl⟩ : syracuseStep 1306099 = 1959149) B1959149
theorem B1961459 : Blo 1305971 1961459 := bstep (se 1 (by rfl) ⟨1471094, by rfl⟩ : syracuseStep 1961459 = 2942189) B2942189
theorem B1306115 : Blo 1305971 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B1961489 : Blo 1305971 1961489 := bstep (se 2 (by rfl) ⟨735558, by rfl⟩ : syracuseStep 1961489 = 1471117) B1471117
theorem B1306131 : Blo 1305971 1306131 := bstep (se 1 (by rfl) ⟨979598, by rfl⟩ : syracuseStep 1306131 = 1959197) B1959197
theorem B1306147 : Blo 1305971 1306147 := bstep (se 1 (by rfl) ⟨979610, by rfl⟩ : syracuseStep 1306147 = 1959221) B1959221
theorem B1961507 : Blo 1305971 1961507 := bstep (se 1 (by rfl) ⟨1471130, by rfl⟩ : syracuseStep 1961507 = 2942261) B2942261
theorem B4902449 : Blo 1305971 4902449 := bstep (se 2 (by rfl) ⟨1838418, by rfl⟩ : syracuseStep 4902449 = 3676837) B3676837
theorem B1306163 : Blo 1305971 1306163 := bstep (se 1 (by rfl) ⟨979622, by rfl⟩ : syracuseStep 1306163 = 1959245) B1959245
theorem B15904309 : Blo 1305971 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B1961537 : Blo 1305971 1961537 := bstep (se 2 (by rfl) ⟨735576, by rfl⟩ : syracuseStep 1961537 = 1471153) B1471153
theorem B1306179 : Blo 1305971 1306179 := bstep (se 1 (by rfl) ⟨979634, by rfl⟩ : syracuseStep 1306179 = 1959269) B1959269
theorem B1470019 : Blo 1305971 1470019 := bstep (se 1 (by rfl) ⟨1102514, by rfl⟩ : syracuseStep 1470019 = 2205029) B2205029
theorem B1306195 : Blo 1305971 1306195 := bstep (se 1 (by rfl) ⟨979646, by rfl⟩ : syracuseStep 1306195 = 1959293) B1959293
theorem B1961555 : Blo 1305971 1961555 := bstep (se 1 (by rfl) ⟨1471166, by rfl⟩ : syracuseStep 1961555 = 2942333) B2942333
theorem B1306211 : Blo 1305971 1306211 := bstep (se 1 (by rfl) ⟨979658, by rfl⟩ : syracuseStep 1306211 = 1959317) B1959317
theorem B4410989 : Blo 1305971 4410989 := bstep (se 3 (by rfl) ⟨827060, by rfl⟩ : syracuseStep 4410989 = 1654121) B1654121
theorem B1961585 : Blo 1305971 1961585 := bstep (se 2 (by rfl) ⟨735594, by rfl⟩ : syracuseStep 1961585 = 1471189) B1471189
theorem B1306227 : Blo 1305971 1306227 := bstep (se 1 (by rfl) ⟨979670, by rfl⟩ : syracuseStep 1306227 = 1959341) B1959341
theorem B4025987 : Blo 1305971 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B1306243 : Blo 1305971 1306243 := bstep (se 1 (by rfl) ⟨979682, by rfl⟩ : syracuseStep 1306243 = 1959365) B1959365
theorem B1961603 : Blo 1305971 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B1306259 : Blo 1305971 1306259 := bstep (se 1 (by rfl) ⟨979694, by rfl⟩ : syracuseStep 1306259 = 1959389) B1959389
theorem B1961633 : Blo 1305971 1961633 := bstep (se 2 (by rfl) ⟨735612, by rfl⟩ : syracuseStep 1961633 = 1471225) B1471225
theorem B1306275 : Blo 1305971 1306275 := bstep (se 1 (by rfl) ⟨979706, by rfl⟩ : syracuseStep 1306275 = 1959413) B1959413
theorem B4411043 : Blo 1305971 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B1306291 : Blo 1305971 1306291 := bstep (se 1 (by rfl) ⟨979718, by rfl⟩ : syracuseStep 1306291 = 1959437) B1959437
theorem B1961651 : Blo 1305971 1961651 := bstep (se 1 (by rfl) ⟨1471238, by rfl⟩ : syracuseStep 1961651 = 2942477) B2942477
theorem B1306307 : Blo 1305971 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B1961681 : Blo 1305971 1961681 := bstep (se 2 (by rfl) ⟨735630, by rfl⟩ : syracuseStep 1961681 = 1471261) B1471261
theorem B1306323 : Blo 1305971 1306323 := bstep (se 1 (by rfl) ⟨979742, by rfl⟩ : syracuseStep 1306323 = 1959485) B1959485
theorem B1470163 : Blo 1305971 1470163 := bstep (se 1 (by rfl) ⟨1102622, by rfl⟩ : syracuseStep 1470163 = 2205245) B2205245
theorem B1306339 : Blo 1305971 1306339 := bstep (se 1 (by rfl) ⟨979754, by rfl⟩ : syracuseStep 1306339 = 1959509) B1959509
theorem B1396451 : Blo 1305971 1396451 := bstep (se 1 (by rfl) ⟨1047338, by rfl⟩ : syracuseStep 1396451 = 2094677) B2094677
theorem B1961699 : Blo 1305971 1961699 := bstep (se 1 (by rfl) ⟨1471274, by rfl⟩ : syracuseStep 1961699 = 2942549) B2942549
theorem B3722993 : Blo 1305971 3722993 := bstep (se 2 (by rfl) ⟨1396122, by rfl⟩ : syracuseStep 3722993 = 2792245) B2792245
theorem B1306355 : Blo 1305971 1306355 := bstep (se 1 (by rfl) ⟨979766, by rfl⟩ : syracuseStep 1306355 = 1959533) B1959533
theorem B1961729 : Blo 1305971 1961729 := bstep (se 2 (by rfl) ⟨735648, by rfl⟩ : syracuseStep 1961729 = 1471297) B1471297
theorem B1306371 : Blo 1305971 1306371 := bstep (se 1 (by rfl) ⟨979778, by rfl⟩ : syracuseStep 1306371 = 1959557) B1959557
theorem B1306387 : Blo 1305971 1306387 := bstep (se 1 (by rfl) ⟨979790, by rfl⟩ : syracuseStep 1306387 = 1959581) B1959581
theorem B2092819 : Blo 1305971 2092819 := bstep (se 1 (by rfl) ⟨1569614, by rfl⟩ : syracuseStep 2092819 = 3139229) B3139229
theorem B1961747 : Blo 1305971 1961747 := bstep (se 1 (by rfl) ⟨1471310, by rfl⟩ : syracuseStep 1961747 = 2942621) B2942621
theorem B1306403 : Blo 1305971 1306403 := bstep (se 1 (by rfl) ⟨979802, by rfl⟩ : syracuseStep 1306403 = 1959605) B1959605
theorem B5582627 : Blo 1305971 5582627 := bstep (se 1 (by rfl) ⟨4186970, by rfl⟩ : syracuseStep 5582627 = 8373941) B8373941
theorem B7442225 : Blo 1305971 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B1961777 : Blo 1305971 1961777 := bstep (se 2 (by rfl) ⟨735666, by rfl⟩ : syracuseStep 1961777 = 1471333) B1471333
theorem B1306419 : Blo 1305971 1306419 := bstep (se 1 (by rfl) ⟨979814, by rfl⟩ : syracuseStep 1306419 = 1959629) B1959629
theorem B1306435 : Blo 1305971 1306435 := bstep (se 1 (by rfl) ⟨979826, by rfl⟩ : syracuseStep 1306435 = 1959653) B1959653
theorem B1961795 : Blo 1305971 1961795 := bstep (se 1 (by rfl) ⟨1471346, by rfl⟩ : syracuseStep 1961795 = 2942693) B2942693
theorem B8367941 : Blo 1305971 8367941 := bstep (se 4 (by rfl) ⟨784494, by rfl⟩ : syracuseStep 8367941 = 1568989) B1568989
theorem B1306451 : Blo 1305971 1306451 := bstep (se 1 (by rfl) ⟨979838, by rfl⟩ : syracuseStep 1306451 = 1959677) B1959677
theorem B1961825 : Blo 1305971 1961825 := bstep (se 2 (by rfl) ⟨735684, by rfl⟩ : syracuseStep 1961825 = 1471369) B1471369
theorem B1306467 : Blo 1305971 1306467 := bstep (se 1 (by rfl) ⟨979850, by rfl⟩ : syracuseStep 1306467 = 1959701) B1959701
theorem B1470307 : Blo 1305971 1470307 := bstep (se 1 (by rfl) ⟨1102730, by rfl⟩ : syracuseStep 1470307 = 2205461) B2205461
theorem B1306483 : Blo 1305971 1306483 := bstep (se 1 (by rfl) ⟨979862, by rfl⟩ : syracuseStep 1306483 = 1959725) B1959725
theorem B1961843 : Blo 1305971 1961843 := bstep (se 1 (by rfl) ⟨1471382, by rfl⟩ : syracuseStep 1961843 = 2942765) B2942765
theorem B1306499 : Blo 1305971 1306499 := bstep (se 1 (by rfl) ⟨979874, by rfl⟩ : syracuseStep 1306499 = 1959749) B1959749
theorem B1961873 : Blo 1305971 1961873 := bstep (se 2 (by rfl) ⟨735702, by rfl⟩ : syracuseStep 1961873 = 1471405) B1471405
theorem B1306515 : Blo 1305971 1306515 := bstep (se 1 (by rfl) ⟨979886, by rfl⟩ : syracuseStep 1306515 = 1959773) B1959773
theorem B1306531 : Blo 1305971 1306531 := bstep (se 1 (by rfl) ⟨979898, by rfl⟩ : syracuseStep 1306531 = 1959797) B1959797
theorem B1961891 : Blo 1305971 1961891 := bstep (se 1 (by rfl) ⟨1471418, by rfl⟩ : syracuseStep 1961891 = 2942837) B2942837
theorem B4411313 : Blo 1305971 4411313 := bstep (se 2 (by rfl) ⟨1654242, by rfl⟩ : syracuseStep 4411313 = 3308485) B3308485
theorem B3723185 : Blo 1305971 3723185 := bstep (se 2 (by rfl) ⟨1396194, by rfl⟩ : syracuseStep 3723185 = 2792389) B2792389
theorem B1306547 : Blo 1305971 1306547 := bstep (se 1 (by rfl) ⟨979910, by rfl⟩ : syracuseStep 1306547 = 1959821) B1959821
theorem B1961921 : Blo 1305971 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B1306563 : Blo 1305971 1306563 := bstep (se 1 (by rfl) ⟨979922, by rfl⟩ : syracuseStep 1306563 = 1959845) B1959845
theorem B1306579 : Blo 1305971 1306579 := bstep (se 1 (by rfl) ⟨979934, by rfl⟩ : syracuseStep 1306579 = 1959869) B1959869
theorem B1961939 : Blo 1305971 1961939 := bstep (se 1 (by rfl) ⟨1471454, by rfl⟩ : syracuseStep 1961939 = 2942909) B2942909
theorem B9416675 : Blo 1305971 9416675 := bstep (se 1 (by rfl) ⟨7062506, by rfl⟩ : syracuseStep 9416675 = 14125013) B14125013
theorem B1306595 : Blo 1305971 1306595 := bstep (se 1 (by rfl) ⟨979946, by rfl⟩ : syracuseStep 1306595 = 1959893) B1959893
theorem B1306611 : Blo 1305971 1306611 := bstep (se 1 (by rfl) ⟨979958, by rfl⟩ : syracuseStep 1306611 = 1959917) B1959917
theorem B1470451 : Blo 1305971 1470451 := bstep (se 1 (by rfl) ⟨1102838, by rfl⟩ : syracuseStep 1470451 = 2205677) B2205677
theorem B1306627 : Blo 1305971 1306627 := bstep (se 1 (by rfl) ⟨979970, by rfl⟩ : syracuseStep 1306627 = 1959941) B1959941
theorem B1306643 : Blo 1305971 1306643 := bstep (se 1 (by rfl) ⟨979982, by rfl⟩ : syracuseStep 1306643 = 1959965) B1959965
theorem B1306659 : Blo 1305971 1306659 := bstep (se 1 (by rfl) ⟨979994, by rfl⟩ : syracuseStep 1306659 = 1959989) B1959989
theorem B1306675 : Blo 1305971 1306675 := bstep (se 1 (by rfl) ⟨980006, by rfl⟩ : syracuseStep 1306675 = 1960013) B1960013
theorem B25104437 : Blo 1305971 25104437 := bstep (se 5 (by rfl) ⟨1176770, by rfl⟩ : syracuseStep 25104437 = 2353541) B2353541
theorem B1306691 : Blo 1305971 1306691 := bstep (se 1 (by rfl) ⟨980018, by rfl⟩ : syracuseStep 1306691 = 1960037) B1960037
theorem B1765459 : Blo 1305971 1765459 := bstep (se 1 (by rfl) ⟨1324094, by rfl⟩ : syracuseStep 1765459 = 2648189) B2648189
theorem B1306707 : Blo 1305971 1306707 := bstep (se 1 (by rfl) ⟨980030, by rfl⟩ : syracuseStep 1306707 = 1960061) B1960061
theorem B1306723 : Blo 1305971 1306723 := bstep (se 1 (by rfl) ⟨980042, by rfl⟩ : syracuseStep 1306723 = 1960085) B1960085
theorem B1306739 : Blo 1305971 1306739 := bstep (se 1 (by rfl) ⟨980054, by rfl⟩ : syracuseStep 1306739 = 1960109) B1960109
theorem B1306755 : Blo 1305971 1306755 := bstep (se 1 (by rfl) ⟨980066, by rfl⟩ : syracuseStep 1306755 = 1960133) B1960133
theorem B1470595 : Blo 1305971 1470595 := bstep (se 1 (by rfl) ⟨1102946, by rfl⟩ : syracuseStep 1470595 = 2205893) B2205893
theorem B1306771 : Blo 1305971 1306771 := bstep (se 1 (by rfl) ⟨980078, by rfl⟩ : syracuseStep 1306771 = 1960157) B1960157
theorem B1306787 : Blo 1305971 1306787 := bstep (se 1 (by rfl) ⟨980090, by rfl⟩ : syracuseStep 1306787 = 1960181) B1960181
theorem B1306803 : Blo 1305971 1306803 := bstep (se 1 (by rfl) ⟨980102, by rfl⟩ : syracuseStep 1306803 = 1960205) B1960205
theorem B4468931 : Blo 1305971 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1306819 : Blo 1305971 1306819 := bstep (se 1 (by rfl) ⟨980114, by rfl⟩ : syracuseStep 1306819 = 1960229) B1960229
theorem B2093267 : Blo 1305971 2093267 := bstep (se 1 (by rfl) ⟨1569950, by rfl⟩ : syracuseStep 2093267 = 3139901) B3139901
theorem B1306835 : Blo 1305971 1306835 := bstep (se 1 (by rfl) ⟨980126, by rfl⟩ : syracuseStep 1306835 = 1960253) B1960253
theorem B1986787 : Blo 1305971 1986787 := bstep (se 1 (by rfl) ⟨1490090, by rfl⟩ : syracuseStep 1986787 = 2980181) B2980181
theorem B1306851 : Blo 1305971 1306851 := bstep (se 1 (by rfl) ⟨980138, by rfl⟩ : syracuseStep 1306851 = 1960277) B1960277
theorem B1306867 : Blo 1305971 1306867 := bstep (se 1 (by rfl) ⟨980150, by rfl⟩ : syracuseStep 1306867 = 1960301) B1960301
theorem B1765633 : Blo 1305971 1765633 := bstep (se 2 (by rfl) ⟨662112, by rfl⟩ : syracuseStep 1765633 = 1324225) B1324225
theorem B1306883 : Blo 1305971 1306883 := bstep (se 1 (by rfl) ⟨980162, by rfl⟩ : syracuseStep 1306883 = 1960325) B1960325
theorem B1306899 : Blo 1305971 1306899 := bstep (se 1 (by rfl) ⟨980174, by rfl⟩ : syracuseStep 1306899 = 1960349) B1960349
theorem B1470739 : Blo 1305971 1470739 := bstep (se 1 (by rfl) ⟨1103054, by rfl⟩ : syracuseStep 1470739 = 2206109) B2206109
theorem B1306915 : Blo 1305971 1306915 := bstep (se 1 (by rfl) ⟨980186, by rfl⟩ : syracuseStep 1306915 = 1960373) B1960373
theorem B1306931 : Blo 1305971 1306931 := bstep (se 1 (by rfl) ⟨980198, by rfl⟩ : syracuseStep 1306931 = 1960397) B1960397
theorem B1306947 : Blo 1305971 1306947 := bstep (se 1 (by rfl) ⟨980210, by rfl⟩ : syracuseStep 1306947 = 1960421) B1960421
theorem B1306963 : Blo 1305971 1306963 := bstep (se 1 (by rfl) ⟨980222, by rfl⟩ : syracuseStep 1306963 = 1960445) B1960445
theorem B1306979 : Blo 1305971 1306979 := bstep (se 1 (by rfl) ⟨980234, by rfl⟩ : syracuseStep 1306979 = 1960469) B1960469
theorem B1306995 : Blo 1305971 1306995 := bstep (se 1 (by rfl) ⟨980246, by rfl⟩ : syracuseStep 1306995 = 1960493) B1960493
theorem B1307011 : Blo 1305971 1307011 := bstep (se 1 (by rfl) ⟨980258, by rfl⟩ : syracuseStep 1307011 = 1960517) B1960517
theorem B3305873 : Blo 1305971 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B1307027 : Blo 1305971 1307027 := bstep (se 1 (by rfl) ⟨980270, by rfl⟩ : syracuseStep 1307027 = 1960541) B1960541
theorem B1307043 : Blo 1305971 1307043 := bstep (se 1 (by rfl) ⟨980282, by rfl⟩ : syracuseStep 1307043 = 1960565) B1960565
theorem B1470883 : Blo 1305971 1470883 := bstep (se 1 (by rfl) ⟨1103162, by rfl⟩ : syracuseStep 1470883 = 2206325) B2206325
theorem B1307059 : Blo 1305971 1307059 := bstep (se 1 (by rfl) ⟨980294, by rfl⟩ : syracuseStep 1307059 = 1960589) B1960589
theorem B1307075 : Blo 1305971 1307075 := bstep (se 1 (by rfl) ⟨980306, by rfl⟩ : syracuseStep 1307075 = 1960613) B1960613
theorem B4411853 : Blo 1305971 4411853 := bstep (se 3 (by rfl) ⟨827222, by rfl⟩ : syracuseStep 4411853 = 1654445) B1654445
theorem B1307091 : Blo 1305971 1307091 := bstep (se 1 (by rfl) ⟨980318, by rfl⟩ : syracuseStep 1307091 = 1960637) B1960637
theorem B9925091 : Blo 1305971 9925091 := bstep (se 1 (by rfl) ⟨7443818, by rfl⟩ : syracuseStep 9925091 = 14887637) B14887637
theorem B1307107 : Blo 1305971 1307107 := bstep (se 1 (by rfl) ⟨980330, by rfl⟩ : syracuseStep 1307107 = 1960661) B1960661
theorem B1307123 : Blo 1305971 1307123 := bstep (se 1 (by rfl) ⟨980342, by rfl⟩ : syracuseStep 1307123 = 1960685) B1960685
theorem B1307139 : Blo 1305971 1307139 := bstep (se 1 (by rfl) ⟨980354, by rfl⟩ : syracuseStep 1307139 = 1960709) B1960709
theorem B4411907 : Blo 1305971 4411907 := bstep (se 1 (by rfl) ⟨3308930, by rfl⟩ : syracuseStep 4411907 = 6617861) B6617861
theorem B1307155 : Blo 1305971 1307155 := bstep (se 1 (by rfl) ⟨980366, by rfl⟩ : syracuseStep 1307155 = 1960733) B1960733
theorem B1307171 : Blo 1305971 1307171 := bstep (se 1 (by rfl) ⟨980378, by rfl⟩ : syracuseStep 1307171 = 1960757) B1960757
theorem B1307187 : Blo 1305971 1307187 := bstep (se 1 (by rfl) ⟨980390, by rfl⟩ : syracuseStep 1307187 = 1960781) B1960781
theorem B1471027 : Blo 1305971 1471027 := bstep (se 1 (by rfl) ⟨1103270, by rfl⟩ : syracuseStep 1471027 = 2206541) B2206541
theorem B1307203 : Blo 1305971 1307203 := bstep (se 1 (by rfl) ⟨980402, by rfl⟩ : syracuseStep 1307203 = 1960805) B1960805
theorem B1307219 : Blo 1305971 1307219 := bstep (se 1 (by rfl) ⟨980414, by rfl⟩ : syracuseStep 1307219 = 1960829) B1960829
theorem B1815139 : Blo 1305971 1815139 := bstep (se 1 (by rfl) ⟨1361354, by rfl⟩ : syracuseStep 1815139 = 2722709) B2722709
theorem B1307235 : Blo 1305971 1307235 := bstep (se 1 (by rfl) ⟨980426, by rfl⟩ : syracuseStep 1307235 = 1960853) B1960853
theorem B1307251 : Blo 1305971 1307251 := bstep (se 1 (by rfl) ⟨980438, by rfl⟩ : syracuseStep 1307251 = 1960877) B1960877
theorem B1307267 : Blo 1305971 1307267 := bstep (se 1 (by rfl) ⟨980450, by rfl⟩ : syracuseStep 1307267 = 1960901) B1960901
theorem B1307283 : Blo 1305971 1307283 := bstep (se 1 (by rfl) ⟨980462, by rfl⟩ : syracuseStep 1307283 = 1960925) B1960925
theorem B1307299 : Blo 1305971 1307299 := bstep (se 1 (by rfl) ⟨980474, by rfl⟩ : syracuseStep 1307299 = 1960949) B1960949
theorem B1307315 : Blo 1305971 1307315 := bstep (se 1 (by rfl) ⟨980486, by rfl⟩ : syracuseStep 1307315 = 1960973) B1960973
theorem B1307331 : Blo 1305971 1307331 := bstep (se 1 (by rfl) ⟨980498, by rfl⟩ : syracuseStep 1307331 = 1960997) B1960997
theorem B1471171 : Blo 1305971 1471171 := bstep (se 1 (by rfl) ⟨1103378, by rfl⟩ : syracuseStep 1471171 = 2206757) B2206757
theorem B1307347 : Blo 1305971 1307347 := bstep (se 1 (by rfl) ⟨980510, by rfl⟩ : syracuseStep 1307347 = 1961021) B1961021
theorem B1307363 : Blo 1305971 1307363 := bstep (se 1 (by rfl) ⟨980522, by rfl⟩ : syracuseStep 1307363 = 1961045) B1961045
theorem B1307379 : Blo 1305971 1307379 := bstep (se 1 (by rfl) ⟨980534, by rfl⟩ : syracuseStep 1307379 = 1961069) B1961069
theorem B2093825 : Blo 1305971 2093825 := bstep (se 2 (by rfl) ⟨785184, by rfl⟩ : syracuseStep 2093825 = 1570369) B1570369
theorem B1307395 : Blo 1305971 1307395 := bstep (se 1 (by rfl) ⟨980546, by rfl⟩ : syracuseStep 1307395 = 1961093) B1961093
theorem B4412177 : Blo 1305971 4412177 := bstep (se 2 (by rfl) ⟨1654566, by rfl⟩ : syracuseStep 4412177 = 3309133) B3309133
theorem B1307411 : Blo 1305971 1307411 := bstep (se 1 (by rfl) ⟨980558, by rfl⟩ : syracuseStep 1307411 = 1961117) B1961117
theorem B1307427 : Blo 1305971 1307427 := bstep (se 1 (by rfl) ⟨980570, by rfl⟩ : syracuseStep 1307427 = 1961141) B1961141
theorem B1307443 : Blo 1305971 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1307459 : Blo 1305971 1307459 := bstep (se 1 (by rfl) ⟨980594, by rfl⟩ : syracuseStep 1307459 = 1961189) B1961189
theorem B1307475 : Blo 1305971 1307475 := bstep (se 1 (by rfl) ⟨980606, by rfl⟩ : syracuseStep 1307475 = 1961213) B1961213
theorem B1471315 : Blo 1305971 1471315 := bstep (se 1 (by rfl) ⟨1103486, by rfl⟩ : syracuseStep 1471315 = 2206973) B2206973
theorem B1307491 : Blo 1305971 1307491 := bstep (se 1 (by rfl) ⟨980618, by rfl⟩ : syracuseStep 1307491 = 1961237) B1961237
theorem B35779441 : Blo 1305971 35779441 := bstep (se 2 (by rfl) ⟨13417290, by rfl⟩ : syracuseStep 35779441 = 26834581) B26834581
theorem B1307507 : Blo 1305971 1307507 := bstep (se 1 (by rfl) ⟨980630, by rfl⟩ : syracuseStep 1307507 = 1961261) B1961261
theorem B1307523 : Blo 1305971 1307523 := bstep (se 1 (by rfl) ⟨980642, by rfl⟩ : syracuseStep 1307523 = 1961285) B1961285
theorem B3724177 : Blo 1305971 3724177 := bstep (se 2 (by rfl) ⟨1396566, by rfl⟩ : syracuseStep 3724177 = 2793133) B2793133
theorem B1307539 : Blo 1305971 1307539 := bstep (se 1 (by rfl) ⟨980654, by rfl⟩ : syracuseStep 1307539 = 1961309) B1961309
theorem B1307555 : Blo 1305971 1307555 := bstep (se 1 (by rfl) ⟨980666, by rfl⟩ : syracuseStep 1307555 = 1961333) B1961333
theorem B1987505 : Blo 1305971 1987505 := bstep (se 2 (by rfl) ⟨745314, by rfl⟩ : syracuseStep 1987505 = 1490629) B1490629
theorem B1307571 : Blo 1305971 1307571 := bstep (se 1 (by rfl) ⟨980678, by rfl⟩ : syracuseStep 1307571 = 1961357) B1961357
theorem B1307587 : Blo 1305971 1307587 := bstep (se 1 (by rfl) ⟨980690, by rfl⟩ : syracuseStep 1307587 = 1961381) B1961381
theorem B1307603 : Blo 1305971 1307603 := bstep (se 1 (by rfl) ⟨980702, by rfl⟩ : syracuseStep 1307603 = 1961405) B1961405
theorem B2094049 : Blo 1305971 2094049 := bstep (se 2 (by rfl) ⟨785268, by rfl⟩ : syracuseStep 2094049 = 1570537) B1570537
theorem B1307619 : Blo 1305971 1307619 := bstep (se 1 (by rfl) ⟨980714, by rfl⟩ : syracuseStep 1307619 = 1961429) B1961429
theorem B1471459 : Blo 1305971 1471459 := bstep (se 1 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 1471459 = 2207189) B2207189
theorem B1307635 : Blo 1305971 1307635 := bstep (se 1 (by rfl) ⟨980726, by rfl⟩ : syracuseStep 1307635 = 1961453) B1961453
theorem B1307651 : Blo 1305971 1307651 := bstep (se 1 (by rfl) ⟨980738, by rfl⟩ : syracuseStep 1307651 = 1961477) B1961477
theorem B14881805 : Blo 1305971 14881805 := bstep (se 3 (by rfl) ⟨2790338, by rfl⟩ : syracuseStep 14881805 = 5580677) B5580677
theorem B1307667 : Blo 1305971 1307667 := bstep (se 1 (by rfl) ⟨980750, by rfl⟩ : syracuseStep 1307667 = 1961501) B1961501
theorem B2094113 : Blo 1305971 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B1307683 : Blo 1305971 1307683 := bstep (se 1 (by rfl) ⟨980762, by rfl⟩ : syracuseStep 1307683 = 1961525) B1961525
theorem B1307699 : Blo 1305971 1307699 := bstep (se 1 (by rfl) ⟨980774, by rfl⟩ : syracuseStep 1307699 = 1961549) B1961549
theorem B1307715 : Blo 1305971 1307715 := bstep (se 1 (by rfl) ⟨980786, by rfl⟩ : syracuseStep 1307715 = 1961573) B1961573
theorem B1307731 : Blo 1305971 1307731 := bstep (se 1 (by rfl) ⟨980798, by rfl⟩ : syracuseStep 1307731 = 1961597) B1961597
theorem B1766497 : Blo 1305971 1766497 := bstep (se 2 (by rfl) ⟨662436, by rfl⟩ : syracuseStep 1766497 = 1324873) B1324873
theorem B1307747 : Blo 1305971 1307747 := bstep (se 1 (by rfl) ⟨980810, by rfl⟩ : syracuseStep 1307747 = 1961621) B1961621
theorem B1307763 : Blo 1305971 1307763 := bstep (se 1 (by rfl) ⟨980822, by rfl⟩ : syracuseStep 1307763 = 1961645) B1961645
theorem B1307779 : Blo 1305971 1307779 := bstep (se 1 (by rfl) ⟨980834, by rfl⟩ : syracuseStep 1307779 = 1961669) B1961669
theorem B1307795 : Blo 1305971 1307795 := bstep (se 1 (by rfl) ⟨980846, by rfl⟩ : syracuseStep 1307795 = 1961693) B1961693
theorem B2094241 : Blo 1305971 2094241 := bstep (se 2 (by rfl) ⟨785340, by rfl⟩ : syracuseStep 2094241 = 1570681) B1570681
theorem B1307811 : Blo 1305971 1307811 := bstep (se 1 (by rfl) ⟨980858, by rfl⟩ : syracuseStep 1307811 = 1961717) B1961717
theorem B3724451 : Blo 1305971 3724451 := bstep (se 1 (by rfl) ⟨2793338, by rfl⟩ : syracuseStep 3724451 = 5586677) B5586677
theorem B6616241 : Blo 1305971 6616241 := bstep (se 2 (by rfl) ⟨2481090, by rfl⟩ : syracuseStep 6616241 = 4962181) B4962181
theorem B1307827 : Blo 1305971 1307827 := bstep (se 1 (by rfl) ⟨980870, by rfl⟩ : syracuseStep 1307827 = 1961741) B1961741
theorem B1307843 : Blo 1305971 1307843 := bstep (se 1 (by rfl) ⟨980882, by rfl⟩ : syracuseStep 1307843 = 1961765) B1961765
theorem B1307859 : Blo 1305971 1307859 := bstep (se 1 (by rfl) ⟨980894, by rfl⟩ : syracuseStep 1307859 = 1961789) B1961789
theorem B7443683 : Blo 1305971 7443683 := bstep (se 1 (by rfl) ⟨5582762, by rfl⟩ : syracuseStep 7443683 = 11165525) B11165525
theorem B1307875 : Blo 1305971 1307875 := bstep (se 1 (by rfl) ⟨980906, by rfl⟩ : syracuseStep 1307875 = 1961813) B1961813
theorem B1307891 : Blo 1305971 1307891 := bstep (se 1 (by rfl) ⟨980918, by rfl⟩ : syracuseStep 1307891 = 1961837) B1961837
theorem B1307907 : Blo 1305971 1307907 := bstep (se 1 (by rfl) ⟨980930, by rfl⟩ : syracuseStep 1307907 = 1961861) B1961861
theorem B1307923 : Blo 1305971 1307923 := bstep (se 1 (by rfl) ⟨980942, by rfl⟩ : syracuseStep 1307923 = 1961885) B1961885
theorem B1307939 : Blo 1305971 1307939 := bstep (se 1 (by rfl) ⟨980954, by rfl⟩ : syracuseStep 1307939 = 1961909) B1961909
theorem B4412717 : Blo 1305971 4412717 := bstep (se 3 (by rfl) ⟨827384, by rfl⟩ : syracuseStep 4412717 = 1654769) B1654769
theorem B1307955 : Blo 1305971 1307955 := bstep (se 1 (by rfl) ⟨980966, by rfl⟩ : syracuseStep 1307955 = 1961933) B1961933
theorem B1307971 : Blo 1305971 1307971 := bstep (se 1 (by rfl) ⟨980978, by rfl⟩ : syracuseStep 1307971 = 1961957) B1961957
theorem B4412771 : Blo 1305971 4412771 := bstep (se 1 (by rfl) ⟨3309578, by rfl⟩ : syracuseStep 4412771 = 6619157) B6619157
theorem B3724643 : Blo 1305971 3724643 := bstep (se 1 (by rfl) ⟨2793482, by rfl⟩ : syracuseStep 3724643 = 5586965) B5586965
theorem B3306865 : Blo 1305971 3306865 := bstep (se 2 (by rfl) ⟨1240074, by rfl⟩ : syracuseStep 3306865 = 2480149) B2480149
theorem B2356771 : Blo 1305971 2356771 := bstep (se 1 (by rfl) ⟨1767578, by rfl⟩ : syracuseStep 2356771 = 3535157) B3535157
theorem B2938481 : Blo 1305971 2938481 := bstep (se 2 (by rfl) ⟨1101930, by rfl⟩ : syracuseStep 2938481 = 2203861) B2203861
theorem B4413041 : Blo 1305971 4413041 := bstep (se 2 (by rfl) ⟨1654890, by rfl⟩ : syracuseStep 4413041 = 3309781) B3309781
theorem B2938499 : Blo 1305971 2938499 := bstep (se 1 (by rfl) ⟨2203874, by rfl⟩ : syracuseStep 2938499 = 4407749) B4407749
theorem B2479747 : Blo 1305971 2479747 := bstep (se 1 (by rfl) ⟨1859810, by rfl⟩ : syracuseStep 2479747 = 3719621) B3719621
theorem B3307139 : Blo 1305971 3307139 := bstep (se 1 (by rfl) ⟨2480354, by rfl⟩ : syracuseStep 3307139 = 4960709) B4960709
theorem B2791057 : Blo 1305971 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B4961969 : Blo 1305971 4961969 := bstep (se 2 (by rfl) ⟨1860738, by rfl⟩ : syracuseStep 4961969 = 3721477) B3721477
theorem B8369891 : Blo 1305971 8369891 := bstep (se 1 (by rfl) ⟨6277418, by rfl⟩ : syracuseStep 8369891 = 12554837) B12554837
theorem B8943331 : Blo 1305971 8943331 := bstep (se 1 (by rfl) ⟨6707498, by rfl⟩ : syracuseStep 8943331 = 13414997) B13414997
theorem B3307331 : Blo 1305971 3307331 := bstep (se 1 (by rfl) ⟨2480498, by rfl⟩ : syracuseStep 3307331 = 4960997) B4960997
theorem B2938769 : Blo 1305971 2938769 := bstep (se 2 (by rfl) ⟨1102038, by rfl⟩ : syracuseStep 2938769 = 2204077) B2204077
theorem B2938787 : Blo 1305971 2938787 := bstep (se 1 (by rfl) ⟨2204090, by rfl⟩ : syracuseStep 2938787 = 4408181) B4408181
theorem B5027789 : Blo 1305971 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B2480195 : Blo 1305971 2480195 := bstep (se 1 (by rfl) ⟨1860146, by rfl⟩ : syracuseStep 2480195 = 3720293) B3720293
theorem B4413581 : Blo 1305971 4413581 := bstep (se 3 (by rfl) ⟨827546, by rfl⟩ : syracuseStep 4413581 = 1655093) B1655093
theorem B4184227 : Blo 1305971 4184227 := bstep (se 1 (by rfl) ⟨3138170, by rfl⟩ : syracuseStep 4184227 = 6276341) B6276341
theorem B2939057 : Blo 1305971 2939057 := bstep (se 2 (by rfl) ⟨1102146, by rfl⟩ : syracuseStep 2939057 = 2204293) B2204293
theorem B2939075 : Blo 1305971 2939075 := bstep (se 1 (by rfl) ⟨2204306, by rfl⟩ : syracuseStep 2939075 = 4408613) B4408613
theorem B4413635 : Blo 1305971 4413635 := bstep (se 1 (by rfl) ⟨3310226, by rfl⟩ : syracuseStep 4413635 = 6620453) B6620453
theorem B4184369 : Blo 1305971 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B1653043 : Blo 1305971 1653043 := bstep (se 1 (by rfl) ⟨1239782, by rfl⟩ : syracuseStep 1653043 = 2479565) B2479565
theorem B2480483 : Blo 1305971 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B8059277 : Blo 1305971 8059277 := bstep (se 3 (by rfl) ⟨1511114, by rfl⟩ : syracuseStep 8059277 = 3022229) B3022229
theorem B1653139 : Blo 1305971 1653139 := bstep (se 1 (by rfl) ⟨1239854, by rfl⟩ : syracuseStep 1653139 = 2479709) B2479709
theorem B4708813 : Blo 1305971 4708813 := bstep (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) B1765805
theorem B2939345 : Blo 1305971 2939345 := bstep (se 2 (by rfl) ⟨1102254, by rfl⟩ : syracuseStep 2939345 = 2204509) B2204509
theorem B4413905 : Blo 1305971 4413905 := bstep (se 2 (by rfl) ⟨1655214, by rfl⟩ : syracuseStep 4413905 = 3310429) B3310429
theorem B2939363 : Blo 1305971 2939363 := bstep (se 1 (by rfl) ⟨2204522, by rfl⟩ : syracuseStep 2939363 = 4409045) B4409045
theorem B1325603 : Blo 1305971 1325603 := bstep (se 1 (by rfl) ⟨994202, by rfl⟩ : syracuseStep 1325603 = 1988405) B1988405
theorem B1325651 : Blo 1305971 1325651 := bstep (se 1 (by rfl) ⟨994238, by rfl⟩ : syracuseStep 1325651 = 1988477) B1988477
theorem B6617699 : Blo 1305971 6617699 := bstep (se 1 (by rfl) ⟨4963274, by rfl⟩ : syracuseStep 6617699 = 9926549) B9926549
theorem B26835569 : Blo 1305971 26835569 := bstep (se 2 (by rfl) ⟨10063338, by rfl⟩ : syracuseStep 26835569 = 20126677) B20126677
theorem B3185315 : Blo 1305971 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B2939633 : Blo 1305971 2939633 := bstep (se 2 (by rfl) ⟨1102362, by rfl⟩ : syracuseStep 2939633 = 2204725) B2204725
theorem B3308273 : Blo 1305971 3308273 := bstep (se 2 (by rfl) ⟨1240602, by rfl⟩ : syracuseStep 3308273 = 2481205) B2481205
theorem B2939651 : Blo 1305971 2939651 := bstep (se 1 (by rfl) ⟨2204738, by rfl⟩ : syracuseStep 2939651 = 4409477) B4409477
theorem B3308323 : Blo 1305971 3308323 := bstep (se 1 (by rfl) ⟨2481242, by rfl⟩ : syracuseStep 3308323 = 4962485) B4962485
theorem B1653635 : Blo 1305971 1653635 := bstep (se 1 (by rfl) ⟨1240226, by rfl⟩ : syracuseStep 1653635 = 2480453) B2480453
theorem B4709261 : Blo 1305971 4709261 := bstep (se 3 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 4709261 = 1765973) B1765973
theorem B3308465 : Blo 1305971 3308465 := bstep (se 2 (by rfl) ⟨1240674, by rfl⟩ : syracuseStep 3308465 = 2481349) B2481349
theorem B2939921 : Blo 1305971 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B2939939 : Blo 1305971 2939939 := bstep (se 1 (by rfl) ⟨2204954, by rfl⟩ : syracuseStep 2939939 = 4409909) B4409909
theorem B2235443 : Blo 1305971 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B4963427 : Blo 1305971 4963427 := bstep (se 1 (by rfl) ⟨3722570, by rfl⟩ : syracuseStep 4963427 = 7445141) B7445141
theorem B2481425 : Blo 1305971 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B2940209 : Blo 1305971 2940209 := bstep (se 2 (by rfl) ⟨1102578, by rfl⟩ : syracuseStep 2940209 = 2205157) B2205157
theorem B7953713 : Blo 1305971 7953713 := bstep (se 2 (by rfl) ⟨2982642, by rfl⟩ : syracuseStep 7953713 = 5965285) B5965285
theorem B2940227 : Blo 1305971 2940227 := bstep (se 1 (by rfl) ⟨2205170, by rfl⟩ : syracuseStep 2940227 = 4410341) B4410341
theorem B14875973 : Blo 1305971 14875973 := bstep (se 4 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 14875973 = 2789245) B2789245
theorem B6618509 : Blo 1305971 6618509 := bstep (se 3 (by rfl) ⟨1240970, by rfl⟩ : syracuseStep 6618509 = 2481941) B2481941
theorem B5586317 : Blo 1305971 5586317 := bstep (se 3 (by rfl) ⟨1047434, by rfl⟩ : syracuseStep 5586317 = 2094869) B2094869
theorem B31792661 : Blo 1305971 31792661 := bstep (se 6 (by rfl) ⟨745140, by rfl⟩ : syracuseStep 31792661 = 1490281) B1490281
theorem B1654339 : Blo 1305971 1654339 := bstep (se 1 (by rfl) ⟨1240754, by rfl⟩ : syracuseStep 1654339 = 2481509) B2481509
theorem B2940497 : Blo 1305971 2940497 := bstep (se 2 (by rfl) ⟨1102686, by rfl⟩ : syracuseStep 2940497 = 2205373) B2205373
theorem B2940515 : Blo 1305971 2940515 := bstep (se 1 (by rfl) ⟨2205386, by rfl⟩ : syracuseStep 2940515 = 4410773) B4410773
theorem B4185713 : Blo 1305971 4185713 := bstep (se 2 (by rfl) ⟨1569642, by rfl⟩ : syracuseStep 4185713 = 3139285) B3139285
theorem B8380037 : Blo 1305971 8380037 := bstep (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) B1571257
theorem B1654435 : Blo 1305971 1654435 := bstep (se 1 (by rfl) ⟨1240826, by rfl⟩ : syracuseStep 1654435 = 2481653) B2481653
theorem B2981539 : Blo 1305971 2981539 := bstep (se 1 (by rfl) ⟨2236154, by rfl⟩ : syracuseStep 2981539 = 4472309) B4472309
theorem B3530573 : Blo 1305971 3530573 := bstep (se 3 (by rfl) ⟨661982, by rfl⟩ : syracuseStep 3530573 = 1323965) B1323965
theorem B2981713 : Blo 1305971 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B14884721 : Blo 1305971 14884721 := bstep (se 2 (by rfl) ⟨5581770, by rfl⟩ : syracuseStep 14884721 = 11163541) B11163541
theorem B4710257 : Blo 1305971 4710257 := bstep (se 2 (by rfl) ⟨1766346, by rfl⟩ : syracuseStep 4710257 = 3532693) B3532693
theorem B2940785 : Blo 1305971 2940785 := bstep (se 2 (by rfl) ⟨1102794, by rfl⟩ : syracuseStep 2940785 = 2205589) B2205589
theorem B2940803 : Blo 1305971 2940803 := bstep (se 1 (by rfl) ⟨2205602, by rfl⟩ : syracuseStep 2940803 = 4411205) B4411205
theorem B3309457 : Blo 1305971 3309457 := bstep (se 2 (by rfl) ⟨1241046, by rfl⟩ : syracuseStep 3309457 = 2482093) B2482093
theorem B2514883 : Blo 1305971 2514883 := bstep (se 1 (by rfl) ⟨1886162, by rfl⟩ : syracuseStep 2514883 = 3772325) B3772325
theorem B1859537 : Blo 1305971 1859537 := bstep (se 2 (by rfl) ⟨697326, by rfl⟩ : syracuseStep 1859537 = 1394653) B1394653
theorem B2940929 : Blo 1305971 2940929 := bstep (se 2 (by rfl) ⟨1102848, by rfl⟩ : syracuseStep 2940929 = 2205697) B2205697
theorem B2482177 : Blo 1305971 2482177 := bstep (se 2 (by rfl) ⟨930816, by rfl⟩ : syracuseStep 2482177 = 1861633) B1861633
theorem B16736291 : Blo 1305971 16736291 := bstep (se 1 (by rfl) ⟨12552218, by rfl⟩ : syracuseStep 16736291 = 25104437) B25104437
theorem B3309619 : Blo 1305971 3309619 := bstep (se 1 (by rfl) ⟨2482214, by rfl⟩ : syracuseStep 3309619 = 4964429) B4964429
theorem B7061579 : Blo 1305971 7061579 := bstep (se 1 (by rfl) ⟨5296184, by rfl⟩ : syracuseStep 7061579 = 10592369) B10592369
theorem B4243549 : Blo 1305971 4243549 := bstep (se 3 (by rfl) ⟨795665, by rfl⟩ : syracuseStep 4243549 = 1591331) B1591331
theorem B3309761 : Blo 1305971 3309761 := bstep (se 2 (by rfl) ⟨1241160, by rfl⟩ : syracuseStep 3309761 = 2482321) B2482321
theorem B1654987 : Blo 1305971 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B9920717 : Blo 1305971 9920717 := bstep (se 3 (by rfl) ⟨1860134, by rfl⟩ : syracuseStep 9920717 = 3720269) B3720269
theorem B5578969 : Blo 1305971 5578969 := bstep (se 2 (by rfl) ⟨2092113, by rfl⟩ : syracuseStep 5578969 = 4184227) B4184227
theorem B2941145 : Blo 1305971 2941145 := bstep (se 2 (by rfl) ⟨1102929, by rfl⟩ : syracuseStep 2941145 = 2205859) B2205859
theorem B4964611 : Blo 1305971 4964611 := bstep (se 1 (by rfl) ⟨3723458, by rfl⟩ : syracuseStep 4964611 = 7446917) B7446917
theorem B2203915 : Blo 1305971 2203915 := bstep (se 1 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 2203915 = 3305873) B3305873
theorem B2941235 : Blo 1305971 2941235 := bstep (se 1 (by rfl) ⟨2205926, by rfl⟩ : syracuseStep 2941235 = 4411853) B4411853
theorem B8372555 : Blo 1305971 8372555 := bstep (se 1 (by rfl) ⟨6279416, by rfl⟩ : syracuseStep 8372555 = 12558833) B12558833
theorem B2941271 : Blo 1305971 2941271 := bstep (se 1 (by rfl) ⟨2205953, by rfl⟩ : syracuseStep 2941271 = 4411907) B4411907
theorem B2204057 : Blo 1305971 2204057 := bstep (se 2 (by rfl) ⟨826521, by rfl⟩ : syracuseStep 2204057 = 1653043) B1653043
theorem B2482625 : Blo 1305971 2482625 := bstep (se 2 (by rfl) ⟨930984, by rfl⟩ : syracuseStep 2482625 = 1861969) B1861969
theorem B1655255 : Blo 1305971 1655255 := bstep (se 1 (by rfl) ⟨1241441, by rfl⟩ : syracuseStep 1655255 = 2482883) B2482883
theorem B2941451 : Blo 1305971 2941451 := bstep (se 1 (by rfl) ⟨2206088, by rfl⟩ : syracuseStep 2941451 = 4412177) B4412177
theorem B2204185 : Blo 1305971 2204185 := bstep (se 2 (by rfl) ⟨826569, by rfl⟩ : syracuseStep 2204185 = 1653139) B1653139
theorem B4964915 : Blo 1305971 4964915 := bstep (se 1 (by rfl) ⟨3723686, by rfl⟩ : syracuseStep 4964915 = 7447373) B7447373
theorem B2941505 : Blo 1305971 2941505 := bstep (se 2 (by rfl) ⟨1103064, by rfl⟩ : syracuseStep 2941505 = 2206129) B2206129
theorem B2687627 : Blo 1305971 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B9921203 : Blo 1305971 9921203 := bstep (se 1 (by rfl) ⟨7440902, by rfl⟩ : syracuseStep 9921203 = 14881805) B14881805
theorem B8372915 : Blo 1305971 8372915 := bstep (se 1 (by rfl) ⟨6279686, by rfl⟩ : syracuseStep 8372915 = 12559373) B12559373
theorem B4473623 : Blo 1305971 4473623 := bstep (se 1 (by rfl) ⟨3355217, by rfl⟩ : syracuseStep 4473623 = 6710435) B6710435
theorem B2482967 : Blo 1305971 2482967 := bstep (se 1 (by rfl) ⟨1862225, by rfl⟩ : syracuseStep 2482967 = 3724451) B3724451
theorem B2941721 : Blo 1305971 2941721 := bstep (se 2 (by rfl) ⟨1103145, by rfl⟩ : syracuseStep 2941721 = 2206291) B2206291
theorem B15901541 : Blo 1305971 15901541 := bstep (se 4 (by rfl) ⟨1490769, by rfl⟩ : syracuseStep 15901541 = 2981539) B2981539
theorem B2941811 : Blo 1305971 2941811 := bstep (se 1 (by rfl) ⟨2206358, by rfl⟩ : syracuseStep 2941811 = 4412717) B4412717
theorem B14140277 : Blo 1305971 14140277 := bstep (se 5 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 14140277 = 1325651) B1325651
theorem B2941847 : Blo 1305971 2941847 := bstep (se 1 (by rfl) ⟨2206385, by rfl⟩ : syracuseStep 2941847 = 4412771) B4412771
theorem B2515865 : Blo 1305971 2515865 := bstep (se 2 (by rfl) ⟨943449, by rfl⟩ : syracuseStep 2515865 = 1886899) B1886899
theorem B4408343 : Blo 1305971 4408343 := bstep (se 1 (by rfl) ⟨3306257, by rfl⟩ : syracuseStep 4408343 = 6612515) B6612515
theorem B1958987 : Blo 1305971 1958987 := bstep (se 1 (by rfl) ⟨1469240, by rfl⟩ : syracuseStep 1958987 = 2938481) B2938481
theorem B2942027 : Blo 1305971 2942027 := bstep (se 1 (by rfl) ⟨2206520, by rfl⟩ : syracuseStep 2942027 = 4413041) B4413041
theorem B1958999 : Blo 1305971 1958999 := bstep (se 1 (by rfl) ⟨1469249, by rfl⟩ : syracuseStep 1958999 = 2938499) B2938499
theorem B2204759 : Blo 1305971 2204759 := bstep (se 1 (by rfl) ⟨1653569, by rfl⟩ : syracuseStep 2204759 = 3307139) B3307139
theorem B2942081 : Blo 1305971 2942081 := bstep (se 2 (by rfl) ⟨1103280, by rfl⟩ : syracuseStep 2942081 = 2206561) B2206561
theorem B6620291 : Blo 1305971 6620291 := bstep (se 1 (by rfl) ⟨4965218, by rfl⟩ : syracuseStep 6620291 = 9930437) B9930437
theorem B5579927 : Blo 1305971 5579927 := bstep (se 1 (by rfl) ⟨4184945, by rfl⟩ : syracuseStep 5579927 = 8369891) B8369891
theorem B1959065 : Blo 1305971 1959065 := bstep (se 2 (by rfl) ⟨734649, by rfl⟩ : syracuseStep 1959065 = 1469299) B1469299
theorem B4965569 : Blo 1305971 4965569 := bstep (se 2 (by rfl) ⟨1862088, by rfl⟩ : syracuseStep 4965569 = 3724177) B3724177
theorem B1885399 : Blo 1305971 1885399 := bstep (se 1 (by rfl) ⟨1414049, by rfl⟩ : syracuseStep 1885399 = 2828099) B2828099
theorem B2204887 : Blo 1305971 2204887 := bstep (se 1 (by rfl) ⟨1653665, by rfl⟩ : syracuseStep 2204887 = 3307331) B3307331
theorem B1959179 : Blo 1305971 1959179 := bstep (se 1 (by rfl) ⟨1469384, by rfl⟩ : syracuseStep 1959179 = 2938769) B2938769
theorem B1959191 : Blo 1305971 1959191 := bstep (se 1 (by rfl) ⟨1469393, by rfl⟩ : syracuseStep 1959191 = 2938787) B2938787
theorem B1959257 : Blo 1305971 1959257 := bstep (se 2 (by rfl) ⟨734721, by rfl⟩ : syracuseStep 1959257 = 1469443) B1469443
theorem B2942297 : Blo 1305971 2942297 := bstep (se 2 (by rfl) ⟨1103361, by rfl⟩ : syracuseStep 2942297 = 2206723) B2206723
theorem B2942387 : Blo 1305971 2942387 := bstep (se 1 (by rfl) ⟨2206790, by rfl⟩ : syracuseStep 2942387 = 4413581) B4413581
theorem B1959371 : Blo 1305971 1959371 := bstep (se 1 (by rfl) ⟨1469528, by rfl⟩ : syracuseStep 1959371 = 2939057) B2939057
theorem B1959383 : Blo 1305971 1959383 := bstep (se 1 (by rfl) ⟨1469537, by rfl⟩ : syracuseStep 1959383 = 2939075) B2939075
theorem B2942423 : Blo 1305971 2942423 := bstep (se 1 (by rfl) ⟨2206817, by rfl⟩ : syracuseStep 2942423 = 4413635) B4413635
theorem B1959449 : Blo 1305971 1959449 := bstep (se 2 (by rfl) ⟨734793, by rfl⟩ : syracuseStep 1959449 = 1469587) B1469587
theorem B4408883 : Blo 1305971 4408883 := bstep (se 1 (by rfl) ⟨3306662, by rfl⟩ : syracuseStep 4408883 = 6613325) B6613325
theorem B4187713 : Blo 1305971 4187713 := bstep (se 2 (by rfl) ⟨1570392, by rfl⟩ : syracuseStep 4187713 = 3140785) B3140785
theorem B1959563 : Blo 1305971 1959563 := bstep (se 1 (by rfl) ⟨1469672, by rfl⟩ : syracuseStep 1959563 = 2939345) B2939345
theorem B2942603 : Blo 1305971 2942603 := bstep (se 1 (by rfl) ⟨2206952, by rfl⟩ : syracuseStep 2942603 = 4413905) B4413905
theorem B1959575 : Blo 1305971 1959575 := bstep (se 1 (by rfl) ⟨1469681, by rfl⟩ : syracuseStep 1959575 = 2939363) B2939363
theorem B10061491 : Blo 1305971 10061491 := bstep (se 1 (by rfl) ⟨7546118, by rfl⟩ : syracuseStep 10061491 = 15092237) B15092237
theorem B2942657 : Blo 1305971 2942657 := bstep (se 2 (by rfl) ⟨1103496, by rfl⟩ : syracuseStep 2942657 = 2206993) B2206993
theorem B3720907 : Blo 1305971 3720907 := bstep (se 1 (by rfl) ⟨2790680, by rfl⟩ : syracuseStep 3720907 = 5581361) B5581361
theorem B1959641 : Blo 1305971 1959641 := bstep (se 2 (by rfl) ⟨734865, by rfl⟩ : syracuseStep 1959641 = 1469731) B1469731
theorem B2123543 : Blo 1305971 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B4409153 : Blo 1305971 4409153 := bstep (se 2 (by rfl) ⟨1653432, by rfl⟩ : syracuseStep 4409153 = 3306865) B3306865
theorem B1959755 : Blo 1305971 1959755 := bstep (se 1 (by rfl) ⟨1469816, by rfl⟩ : syracuseStep 1959755 = 2939633) B2939633
theorem B2205515 : Blo 1305971 2205515 := bstep (se 1 (by rfl) ⟨1654136, by rfl⟩ : syracuseStep 2205515 = 3308273) B3308273
theorem B1959767 : Blo 1305971 1959767 := bstep (se 1 (by rfl) ⟨1469825, by rfl⟩ : syracuseStep 1959767 = 2939651) B2939651
theorem B1959833 : Blo 1305971 1959833 := bstep (se 2 (by rfl) ⟨734937, by rfl⟩ : syracuseStep 1959833 = 1469875) B1469875
theorem B2942873 : Blo 1305971 2942873 := bstep (se 2 (by rfl) ⟨1103577, by rfl⟩ : syracuseStep 2942873 = 2207155) B2207155
theorem B3139507 : Blo 1305971 3139507 := bstep (se 1 (by rfl) ⟨2354630, by rfl⟩ : syracuseStep 3139507 = 4709261) B4709261
theorem B2385857 : Blo 1305971 2385857 := bstep (se 2 (by rfl) ⟨894696, by rfl⟩ : syracuseStep 2385857 = 1789393) B1789393
theorem B2205643 : Blo 1305971 2205643 := bstep (se 1 (by rfl) ⟨1654232, by rfl⟩ : syracuseStep 2205643 = 3308465) B3308465
theorem B1959947 : Blo 1305971 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B1959959 : Blo 1305971 1959959 := bstep (se 1 (by rfl) ⟨1469969, by rfl⟩ : syracuseStep 1959959 = 2939939) B2939939
theorem B1960025 : Blo 1305971 1960025 := bstep (se 2 (by rfl) ⟨735009, by rfl⟩ : syracuseStep 1960025 = 1470019) B1470019
theorem B2205785 : Blo 1305971 2205785 := bstep (se 2 (by rfl) ⟨827169, by rfl⟩ : syracuseStep 2205785 = 1654339) B1654339
theorem B11929693 : Blo 1305971 11929693 := bstep (se 3 (by rfl) ⟨2236817, by rfl⟩ : syracuseStep 11929693 = 4473635) B4473635
theorem B9922661 : Blo 1305971 9922661 := bstep (se 4 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 9922661 = 1860499) B1860499
theorem B3721409 : Blo 1305971 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B1960139 : Blo 1305971 1960139 := bstep (se 1 (by rfl) ⟨1470104, by rfl⟩ : syracuseStep 1960139 = 2940209) B2940209
theorem B5302475 : Blo 1305971 5302475 := bstep (se 1 (by rfl) ⟨3976856, by rfl⟩ : syracuseStep 5302475 = 7953713) B7953713
theorem B1960151 : Blo 1305971 1960151 := bstep (se 1 (by rfl) ⟨1470113, by rfl⟩ : syracuseStep 1960151 = 2940227) B2940227
theorem B2205913 : Blo 1305971 2205913 := bstep (se 2 (by rfl) ⟨827217, by rfl⟩ : syracuseStep 2205913 = 1654435) B1654435
theorem B1960217 : Blo 1305971 1960217 := bstep (se 2 (by rfl) ⟨735081, by rfl⟩ : syracuseStep 1960217 = 1470163) B1470163
theorem B4409693 : Blo 1305971 4409693 := bstep (se 3 (by rfl) ⟨826817, by rfl⟩ : syracuseStep 4409693 = 1653635) B1653635
theorem B21195107 : Blo 1305971 21195107 := bstep (se 1 (by rfl) ⟨15896330, by rfl⟩ : syracuseStep 21195107 = 31792661) B31792661
theorem B1960331 : Blo 1305971 1960331 := bstep (se 1 (by rfl) ⟨1470248, by rfl⟩ : syracuseStep 1960331 = 2940497) B2940497
theorem B1960343 : Blo 1305971 1960343 := bstep (se 1 (by rfl) ⟨1470257, by rfl⟩ : syracuseStep 1960343 = 2940515) B2940515
theorem B3975617 : Blo 1305971 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B1960409 : Blo 1305971 1960409 := bstep (se 2 (by rfl) ⟨735153, by rfl⟩ : syracuseStep 1960409 = 1470307) B1470307
theorem B3721751 : Blo 1305971 3721751 := bstep (se 1 (by rfl) ⟨2791313, by rfl⟩ : syracuseStep 3721751 = 5582627) B5582627
theorem B4958765 : Blo 1305971 4958765 := bstep (se 3 (by rfl) ⟨929768, by rfl⟩ : syracuseStep 4958765 = 1859537) B1859537
theorem B2353715 : Blo 1305971 2353715 := bstep (se 1 (by rfl) ⟨1765286, by rfl⟩ : syracuseStep 2353715 = 3530573) B3530573
theorem B9923147 : Blo 1305971 9923147 := bstep (se 1 (by rfl) ⟨7442360, by rfl⟩ : syracuseStep 9923147 = 14884721) B14884721
theorem B3140171 : Blo 1305971 3140171 := bstep (se 1 (by rfl) ⟨2355128, by rfl⟩ : syracuseStep 3140171 = 4710257) B4710257
theorem B1960523 : Blo 1305971 1960523 := bstep (se 1 (by rfl) ⟨1470392, by rfl⟩ : syracuseStep 1960523 = 2940785) B2940785
theorem B1960535 : Blo 1305971 1960535 := bstep (se 1 (by rfl) ⟨1470401, by rfl⟩ : syracuseStep 1960535 = 2940803) B2940803
theorem B3353177 : Blo 1305971 3353177 := bstep (se 2 (by rfl) ⟨1257441, by rfl⟩ : syracuseStep 3353177 = 2514883) B2514883
theorem B25111133 : Blo 1305971 25111133 := bstep (se 3 (by rfl) ⟨4708337, by rfl⟩ : syracuseStep 25111133 = 9416675) B9416675
theorem B1960601 : Blo 1305971 1960601 := bstep (se 2 (by rfl) ⟨735225, by rfl⟩ : syracuseStep 1960601 = 1470451) B1470451
theorem B5515993 : Blo 1305971 5515993 := bstep (se 2 (by rfl) ⟨2068497, by rfl⟩ : syracuseStep 5515993 = 4136995) B4136995
theorem B1960715 : Blo 1305971 1960715 := bstep (se 1 (by rfl) ⟨1470536, by rfl⟩ : syracuseStep 1960715 = 2941073) B2941073
theorem B1960727 : Blo 1305971 1960727 := bstep (se 1 (by rfl) ⟨1470545, by rfl⟩ : syracuseStep 1960727 = 2941091) B2941091
theorem B2206487 : Blo 1305971 2206487 := bstep (se 1 (by rfl) ⟨1654865, by rfl⟩ : syracuseStep 2206487 = 3309731) B3309731
theorem B2353945 : Blo 1305971 2353945 := bstep (se 2 (by rfl) ⟨882729, by rfl⟩ : syracuseStep 2353945 = 1765459) B1765459
theorem B1469227 : Blo 1305971 1469227 := bstep (se 1 (by rfl) ⟨1101920, by rfl⟩ : syracuseStep 1469227 = 2203841) B2203841
theorem B5581619 : Blo 1305971 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B1395511 : Blo 1305971 1395511 := bstep (se 1 (by rfl) ⟨1046633, by rfl⟩ : syracuseStep 1395511 = 2093267) B2093267
theorem B1960793 : Blo 1305971 1960793 := bstep (se 2 (by rfl) ⟨735297, by rfl⟩ : syracuseStep 1960793 = 1470595) B1470595
theorem B1469335 : Blo 1305971 1469335 := bstep (se 1 (by rfl) ⟨1102001, by rfl⟩ : syracuseStep 1469335 = 2204003) B2204003
theorem B2206615 : Blo 1305971 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B5303191 : Blo 1305971 5303191 := bstep (se 1 (by rfl) ⟨3977393, by rfl⟩ : syracuseStep 5303191 = 7954787) B7954787
theorem B1960907 : Blo 1305971 1960907 := bstep (se 1 (by rfl) ⟨1470680, by rfl⟩ : syracuseStep 1960907 = 2941361) B2941361
theorem B1960919 : Blo 1305971 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B2354177 : Blo 1305971 2354177 := bstep (se 2 (by rfl) ⟨882816, by rfl⟩ : syracuseStep 2354177 = 1765633) B1765633
theorem B1960985 : Blo 1305971 1960985 := bstep (se 2 (by rfl) ⟨735369, by rfl⟩ : syracuseStep 1960985 = 1470739) B1470739
theorem B56503331 : Blo 1305971 56503331 := bstep (se 1 (by rfl) ⟨42377498, by rfl⟩ : syracuseStep 56503331 = 84754997) B84754997
theorem B1469515 : Blo 1305971 1469515 := bstep (se 1 (by rfl) ⟨1102136, by rfl⟩ : syracuseStep 1469515 = 2204273) B2204273
theorem B1961099 : Blo 1305971 1961099 := bstep (se 1 (by rfl) ⟨1470824, by rfl⟩ : syracuseStep 1961099 = 2941649) B2941649
theorem B1961111 : Blo 1305971 1961111 := bstep (se 1 (by rfl) ⟨1470833, by rfl⟩ : syracuseStep 1961111 = 2941667) B2941667
theorem B1395883 : Blo 1305971 1395883 := bstep (se 1 (by rfl) ⟨1046912, by rfl⟩ : syracuseStep 1395883 = 2093825) B2093825
theorem B52292789 : Blo 1305971 52292789 := bstep (se 5 (by rfl) ⟨2451224, by rfl⟩ : syracuseStep 52292789 = 4902449) B4902449
theorem B1469623 : Blo 1305971 1469623 := bstep (se 1 (by rfl) ⟨1102217, by rfl⟩ : syracuseStep 1469623 = 2204435) B2204435
theorem B1961177 : Blo 1305971 1961177 := bstep (se 2 (by rfl) ⟨735441, by rfl⟩ : syracuseStep 1961177 = 1470883) B1470883
theorem B6278417 : Blo 1305971 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B4959539 : Blo 1305971 4959539 := bstep (se 1 (by rfl) ⟨3719654, by rfl⟩ : syracuseStep 4959539 = 7439309) B7439309
theorem B16330049 : Blo 1305971 16330049 := bstep (se 2 (by rfl) ⟨6123768, by rfl⟩ : syracuseStep 16330049 = 12247537) B12247537
theorem B3140939 : Blo 1305971 3140939 := bstep (se 1 (by rfl) ⟨2355704, by rfl⟩ : syracuseStep 3140939 = 4711409) B4711409
theorem B1961291 : Blo 1305971 1961291 := bstep (se 1 (by rfl) ⟨1470968, by rfl⟩ : syracuseStep 1961291 = 2941937) B2941937
theorem B1961303 : Blo 1305971 1961303 := bstep (se 1 (by rfl) ⟨1470977, by rfl⟩ : syracuseStep 1961303 = 2941955) B2941955
theorem B1469803 : Blo 1305971 1469803 := bstep (se 1 (by rfl) ⟨1102352, by rfl⟩ : syracuseStep 1469803 = 2204705) B2204705
theorem B1305975 : Blo 1305971 1305975 := bstep (se 1 (by rfl) ⟨979481, by rfl⟩ : syracuseStep 1305975 = 1958963) B1958963
theorem B1305995 : Blo 1305971 1305995 := bstep (se 1 (by rfl) ⟨979496, by rfl⟩ : syracuseStep 1305995 = 1958993) B1958993
theorem B1306007 : Blo 1305971 1306007 := bstep (se 1 (by rfl) ⟨979505, by rfl⟩ : syracuseStep 1306007 = 1959011) B1959011
theorem B1961369 : Blo 1305971 1961369 := bstep (se 2 (by rfl) ⟨735513, by rfl⟩ : syracuseStep 1961369 = 1471027) B1471027
theorem B1306027 : Blo 1305971 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B1306039 : Blo 1305971 1306039 := bstep (se 1 (by rfl) ⟨979529, by rfl⟩ : syracuseStep 1306039 = 1959059) B1959059
theorem B1306059 : Blo 1305971 1306059 := bstep (se 1 (by rfl) ⟨979544, by rfl⟩ : syracuseStep 1306059 = 1959089) B1959089
theorem B4410827 : Blo 1305971 4410827 := bstep (se 1 (by rfl) ⟨3308120, by rfl⟩ : syracuseStep 4410827 = 6616241) B6616241
theorem B1306071 : Blo 1305971 1306071 := bstep (se 1 (by rfl) ⟨979553, by rfl⟩ : syracuseStep 1306071 = 1959107) B1959107
theorem B1469911 : Blo 1305971 1469911 := bstep (se 1 (by rfl) ⟨1102433, by rfl⟩ : syracuseStep 1469911 = 2204867) B2204867
theorem B2420185 : Blo 1305971 2420185 := bstep (se 2 (by rfl) ⟨907569, by rfl⟩ : syracuseStep 2420185 = 1815139) B1815139
theorem B1306091 : Blo 1305971 1306091 := bstep (se 1 (by rfl) ⟨979568, by rfl⟩ : syracuseStep 1306091 = 1959137) B1959137
theorem B1306103 : Blo 1305971 1306103 := bstep (se 1 (by rfl) ⟨979577, by rfl⟩ : syracuseStep 1306103 = 1959155) B1959155
theorem B1306123 : Blo 1305971 1306123 := bstep (se 1 (by rfl) ⟨979592, by rfl⟩ : syracuseStep 1306123 = 1959185) B1959185
theorem B1961483 : Blo 1305971 1961483 := bstep (se 1 (by rfl) ⟨1471112, by rfl⟩ : syracuseStep 1961483 = 2942225) B2942225
theorem B1306135 : Blo 1305971 1306135 := bstep (se 1 (by rfl) ⟨979601, by rfl⟩ : syracuseStep 1306135 = 1959203) B1959203
theorem B1961495 : Blo 1305971 1961495 := bstep (se 1 (by rfl) ⟨1471121, by rfl⟩ : syracuseStep 1961495 = 2942243) B2942243
theorem B1306155 : Blo 1305971 1306155 := bstep (se 1 (by rfl) ⟨979616, by rfl⟩ : syracuseStep 1306155 = 1959233) B1959233
theorem B1306167 : Blo 1305971 1306167 := bstep (se 1 (by rfl) ⟨979625, by rfl⟩ : syracuseStep 1306167 = 1959251) B1959251
theorem B1306187 : Blo 1305971 1306187 := bstep (se 1 (by rfl) ⟨979640, by rfl⟩ : syracuseStep 1306187 = 1959281) B1959281
theorem B1306199 : Blo 1305971 1306199 := bstep (se 1 (by rfl) ⟨979649, by rfl⟩ : syracuseStep 1306199 = 1959299) B1959299
theorem B1961561 : Blo 1305971 1961561 := bstep (se 2 (by rfl) ⟨735585, by rfl⟩ : syracuseStep 1961561 = 1471171) B1471171
theorem B6614621 : Blo 1305971 6614621 := bstep (se 3 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 6614621 = 2480483) B2480483
theorem B9932381 : Blo 1305971 9932381 := bstep (se 3 (by rfl) ⟨1862321, by rfl⟩ : syracuseStep 9932381 = 3724643) B3724643
theorem B1306219 : Blo 1305971 1306219 := bstep (se 1 (by rfl) ⟨979664, by rfl⟩ : syracuseStep 1306219 = 1959329) B1959329
theorem B1306231 : Blo 1305971 1306231 := bstep (se 1 (by rfl) ⟨979673, by rfl⟩ : syracuseStep 1306231 = 1959347) B1959347
theorem B1306251 : Blo 1305971 1306251 := bstep (se 1 (by rfl) ⟨979688, by rfl⟩ : syracuseStep 1306251 = 1959377) B1959377
theorem B1470091 : Blo 1305971 1470091 := bstep (se 1 (by rfl) ⟨1102568, by rfl⟩ : syracuseStep 1470091 = 2205137) B2205137
theorem B1306263 : Blo 1305971 1306263 := bstep (se 1 (by rfl) ⟨979697, by rfl⟩ : syracuseStep 1306263 = 1959395) B1959395
theorem B1306283 : Blo 1305971 1306283 := bstep (se 1 (by rfl) ⟨979712, by rfl⟩ : syracuseStep 1306283 = 1959425) B1959425
theorem B1306295 : Blo 1305971 1306295 := bstep (se 1 (by rfl) ⟨979721, by rfl⟩ : syracuseStep 1306295 = 1959443) B1959443
theorem B1306315 : Blo 1305971 1306315 := bstep (se 1 (by rfl) ⟨979736, by rfl⟩ : syracuseStep 1306315 = 1959473) B1959473
theorem B1961675 : Blo 1305971 1961675 := bstep (se 1 (by rfl) ⟨1471256, by rfl⟩ : syracuseStep 1961675 = 2942513) B2942513
theorem B1306327 : Blo 1305971 1306327 := bstep (se 1 (by rfl) ⟨979745, by rfl⟩ : syracuseStep 1306327 = 1959491) B1959491
theorem B1961687 : Blo 1305971 1961687 := bstep (se 1 (by rfl) ⟨1471265, by rfl⟩ : syracuseStep 1961687 = 2942531) B2942531
theorem B4411097 : Blo 1305971 4411097 := bstep (se 2 (by rfl) ⟨1654161, by rfl⟩ : syracuseStep 4411097 = 3308323) B3308323
theorem B1306347 : Blo 1305971 1306347 := bstep (se 1 (by rfl) ⟨979760, by rfl⟩ : syracuseStep 1306347 = 1959521) B1959521
theorem B1306359 : Blo 1305971 1306359 := bstep (se 1 (by rfl) ⟨979769, by rfl⟩ : syracuseStep 1306359 = 1959539) B1959539
theorem B1470199 : Blo 1305971 1470199 := bstep (se 1 (by rfl) ⟨1102649, by rfl⟩ : syracuseStep 1470199 = 2205299) B2205299
theorem B1306379 : Blo 1305971 1306379 := bstep (se 1 (by rfl) ⟨979784, by rfl⟩ : syracuseStep 1306379 = 1959569) B1959569
theorem B1306391 : Blo 1305971 1306391 := bstep (se 1 (by rfl) ⟨979793, by rfl⟩ : syracuseStep 1306391 = 1959587) B1959587
theorem B1961753 : Blo 1305971 1961753 := bstep (se 2 (by rfl) ⟨735657, by rfl⟩ : syracuseStep 1961753 = 1471315) B1471315
theorem B1306411 : Blo 1305971 1306411 := bstep (se 1 (by rfl) ⟨979808, by rfl⟩ : syracuseStep 1306411 = 1959617) B1959617
theorem B1306423 : Blo 1305971 1306423 := bstep (se 1 (by rfl) ⟨979817, by rfl⟩ : syracuseStep 1306423 = 1959635) B1959635
theorem B47705921 : Blo 1305971 47705921 := bstep (se 2 (by rfl) ⟨17889720, by rfl⟩ : syracuseStep 47705921 = 35779441) B35779441
theorem B1306443 : Blo 1305971 1306443 := bstep (se 1 (by rfl) ⟨979832, by rfl⟩ : syracuseStep 1306443 = 1959665) B1959665
theorem B1306455 : Blo 1305971 1306455 := bstep (se 1 (by rfl) ⟨979841, by rfl⟩ : syracuseStep 1306455 = 1959683) B1959683
theorem B10596197 : Blo 1305971 10596197 := bstep (se 4 (by rfl) ⟨993393, by rfl⟩ : syracuseStep 10596197 = 1986787) B1986787
theorem B1306475 : Blo 1305971 1306475 := bstep (se 1 (by rfl) ⟨979856, by rfl⟩ : syracuseStep 1306475 = 1959713) B1959713
theorem B1306487 : Blo 1305971 1306487 := bstep (se 1 (by rfl) ⟨979865, by rfl⟩ : syracuseStep 1306487 = 1959731) B1959731
theorem B1306507 : Blo 1305971 1306507 := bstep (se 1 (by rfl) ⟨979880, by rfl⟩ : syracuseStep 1306507 = 1959761) B1959761
theorem B1961867 : Blo 1305971 1961867 := bstep (se 1 (by rfl) ⟨1471400, by rfl⟩ : syracuseStep 1961867 = 2942801) B2942801
theorem B1306519 : Blo 1305971 1306519 := bstep (se 1 (by rfl) ⟨979889, by rfl⟩ : syracuseStep 1306519 = 1959779) B1959779
theorem B1961879 : Blo 1305971 1961879 := bstep (se 1 (by rfl) ⟨1471409, by rfl⟩ : syracuseStep 1961879 = 2942819) B2942819
theorem B1306539 : Blo 1305971 1306539 := bstep (se 1 (by rfl) ⟨979904, by rfl⟩ : syracuseStep 1306539 = 1959809) B1959809
theorem B1470379 : Blo 1305971 1470379 := bstep (se 1 (by rfl) ⟨1102784, by rfl⟩ : syracuseStep 1470379 = 2205569) B2205569
theorem B1306551 : Blo 1305971 1306551 := bstep (se 1 (by rfl) ⟨979913, by rfl⟩ : syracuseStep 1306551 = 1959827) B1959827
theorem B1306571 : Blo 1305971 1306571 := bstep (se 1 (by rfl) ⟨979928, by rfl⟩ : syracuseStep 1306571 = 1959857) B1959857
theorem B1306583 : Blo 1305971 1306583 := bstep (se 1 (by rfl) ⟨979937, by rfl⟩ : syracuseStep 1306583 = 1959875) B1959875
theorem B1961945 : Blo 1305971 1961945 := bstep (se 2 (by rfl) ⟨735729, by rfl⟩ : syracuseStep 1961945 = 1471459) B1471459
theorem B1306603 : Blo 1305971 1306603 := bstep (se 1 (by rfl) ⟨979952, by rfl⟩ : syracuseStep 1306603 = 1959905) B1959905
theorem B1306615 : Blo 1305971 1306615 := bstep (se 1 (by rfl) ⟨979961, by rfl⟩ : syracuseStep 1306615 = 1959923) B1959923
theorem B1306635 : Blo 1305971 1306635 := bstep (se 1 (by rfl) ⟨979976, by rfl⟩ : syracuseStep 1306635 = 1959953) B1959953
theorem B14323729 : Blo 1305971 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B1306647 : Blo 1305971 1306647 := bstep (se 1 (by rfl) ⟨979985, by rfl⟩ : syracuseStep 1306647 = 1959971) B1959971
theorem B1470487 : Blo 1305971 1470487 := bstep (se 1 (by rfl) ⟨1102865, by rfl⟩ : syracuseStep 1470487 = 2205731) B2205731
theorem B1306667 : Blo 1305971 1306667 := bstep (se 1 (by rfl) ⟨980000, by rfl⟩ : syracuseStep 1306667 = 1960001) B1960001
theorem B1306679 : Blo 1305971 1306679 := bstep (se 1 (by rfl) ⟨980009, by rfl⟩ : syracuseStep 1306679 = 1960019) B1960019
theorem B1306699 : Blo 1305971 1306699 := bstep (se 1 (by rfl) ⟨980024, by rfl⟩ : syracuseStep 1306699 = 1960049) B1960049
theorem B1306711 : Blo 1305971 1306711 := bstep (se 1 (by rfl) ⟨980033, by rfl⟩ : syracuseStep 1306711 = 1960067) B1960067
theorem B2650199 : Blo 1305971 2650199 := bstep (se 1 (by rfl) ⟨1987649, by rfl⟩ : syracuseStep 2650199 = 3975299) B3975299
theorem B3534941 : Blo 1305971 3534941 := bstep (se 3 (by rfl) ⟨662801, by rfl⟩ : syracuseStep 3534941 = 1325603) B1325603
theorem B1306731 : Blo 1305971 1306731 := bstep (se 1 (by rfl) ⟨980048, by rfl⟩ : syracuseStep 1306731 = 1960097) B1960097
theorem B1306743 : Blo 1305971 1306743 := bstep (se 1 (by rfl) ⟨980057, by rfl⟩ : syracuseStep 1306743 = 1960115) B1960115
theorem B2355329 : Blo 1305971 2355329 := bstep (se 2 (by rfl) ⟨883248, by rfl⟩ : syracuseStep 2355329 = 1766497) B1766497
theorem B1306763 : Blo 1305971 1306763 := bstep (se 1 (by rfl) ⟨980072, by rfl⟩ : syracuseStep 1306763 = 1960145) B1960145
theorem B1306775 : Blo 1305971 1306775 := bstep (se 1 (by rfl) ⟨980081, by rfl⟩ : syracuseStep 1306775 = 1960163) B1960163
theorem B1306795 : Blo 1305971 1306795 := bstep (se 1 (by rfl) ⟨980096, by rfl⟩ : syracuseStep 1306795 = 1960193) B1960193
theorem B1306807 : Blo 1305971 1306807 := bstep (se 1 (by rfl) ⟨980105, by rfl⟩ : syracuseStep 1306807 = 1960211) B1960211
theorem B2789579 : Blo 1305971 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B1306827 : Blo 1305971 1306827 := bstep (se 1 (by rfl) ⟨980120, by rfl⟩ : syracuseStep 1306827 = 1960241) B1960241
theorem B1470667 : Blo 1305971 1470667 := bstep (se 1 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 1470667 = 2206001) B2206001
theorem B1306839 : Blo 1305971 1306839 := bstep (se 1 (by rfl) ⟨980129, by rfl⟩ : syracuseStep 1306839 = 1960259) B1960259
theorem B1306859 : Blo 1305971 1306859 := bstep (se 1 (by rfl) ⟨980144, by rfl⟩ : syracuseStep 1306859 = 1960289) B1960289
theorem B1306871 : Blo 1305971 1306871 := bstep (se 1 (by rfl) ⟨980153, by rfl⟩ : syracuseStep 1306871 = 1960307) B1960307
theorem B1306891 : Blo 1305971 1306891 := bstep (se 1 (by rfl) ⟨980168, by rfl⟩ : syracuseStep 1306891 = 1960337) B1960337
theorem B1306903 : Blo 1305971 1306903 := bstep (se 1 (by rfl) ⟨980177, by rfl⟩ : syracuseStep 1306903 = 1960355) B1960355
theorem B1306923 : Blo 1305971 1306923 := bstep (se 1 (by rfl) ⟨980192, by rfl⟩ : syracuseStep 1306923 = 1960385) B1960385
theorem B11161901 : Blo 1305971 11161901 := bstep (se 3 (by rfl) ⟨2092856, by rfl⟩ : syracuseStep 11161901 = 4185713) B4185713
theorem B34910509 : Blo 1305971 34910509 := bstep (se 3 (by rfl) ⟨6545720, by rfl⟩ : syracuseStep 34910509 = 13091441) B13091441
theorem B1306935 : Blo 1305971 1306935 := bstep (se 1 (by rfl) ⟨980201, by rfl⟩ : syracuseStep 1306935 = 1960403) B1960403
theorem B1470775 : Blo 1305971 1470775 := bstep (se 1 (by rfl) ⟨1103081, by rfl⟩ : syracuseStep 1470775 = 2206163) B2206163
theorem B1306955 : Blo 1305971 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B1306967 : Blo 1305971 1306967 := bstep (se 1 (by rfl) ⟨980225, by rfl⟩ : syracuseStep 1306967 = 1960451) B1960451
theorem B1306987 : Blo 1305971 1306987 := bstep (se 1 (by rfl) ⟨980240, by rfl⟩ : syracuseStep 1306987 = 1960481) B1960481
theorem B1306999 : Blo 1305971 1306999 := bstep (se 1 (by rfl) ⟨980249, by rfl⟩ : syracuseStep 1306999 = 1960499) B1960499
theorem B1307019 : Blo 1305971 1307019 := bstep (se 1 (by rfl) ⟨980264, by rfl⟩ : syracuseStep 1307019 = 1960529) B1960529
theorem B1307031 : Blo 1305971 1307031 := bstep (se 1 (by rfl) ⟨980273, by rfl⟩ : syracuseStep 1307031 = 1960547) B1960547
theorem B4411799 : Blo 1305971 4411799 := bstep (se 1 (by rfl) ⟨3308849, by rfl⟩ : syracuseStep 4411799 = 6617699) B6617699
theorem B1307051 : Blo 1305971 1307051 := bstep (se 1 (by rfl) ⟨980288, by rfl⟩ : syracuseStep 1307051 = 1960577) B1960577
theorem B1307063 : Blo 1305971 1307063 := bstep (se 1 (by rfl) ⟨980297, by rfl⟩ : syracuseStep 1307063 = 1960595) B1960595
theorem B1307083 : Blo 1305971 1307083 := bstep (se 1 (by rfl) ⟨980312, by rfl⟩ : syracuseStep 1307083 = 1960625) B1960625
theorem B1307095 : Blo 1305971 1307095 := bstep (se 1 (by rfl) ⟨980321, by rfl⟩ : syracuseStep 1307095 = 1960643) B1960643
theorem B1307115 : Blo 1305971 1307115 := bstep (se 1 (by rfl) ⟨980336, by rfl⟩ : syracuseStep 1307115 = 1960673) B1960673
theorem B1470955 : Blo 1305971 1470955 := bstep (se 1 (by rfl) ⟨1103216, by rfl⟩ : syracuseStep 1470955 = 2206433) B2206433
theorem B2830835 : Blo 1305971 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B1307127 : Blo 1305971 1307127 := bstep (se 1 (by rfl) ⟨980345, by rfl⟩ : syracuseStep 1307127 = 1960691) B1960691
theorem B1307147 : Blo 1305971 1307147 := bstep (se 1 (by rfl) ⟨980360, by rfl⟩ : syracuseStep 1307147 = 1960721) B1960721
theorem B1307159 : Blo 1305971 1307159 := bstep (se 1 (by rfl) ⟨980369, by rfl⟩ : syracuseStep 1307159 = 1960739) B1960739
theorem B1307179 : Blo 1305971 1307179 := bstep (se 1 (by rfl) ⟨980384, by rfl⟩ : syracuseStep 1307179 = 1960769) B1960769
theorem B3306035 : Blo 1305971 3306035 := bstep (se 1 (by rfl) ⟨2479526, by rfl⟩ : syracuseStep 3306035 = 4959053) B4959053
theorem B1307191 : Blo 1305971 1307191 := bstep (se 1 (by rfl) ⟨980393, by rfl⟩ : syracuseStep 1307191 = 1960787) B1960787
theorem B3772993 : Blo 1305971 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B1307211 : Blo 1305971 1307211 := bstep (se 1 (by rfl) ⟨980408, by rfl⟩ : syracuseStep 1307211 = 1960817) B1960817
theorem B1307223 : Blo 1305971 1307223 := bstep (se 1 (by rfl) ⟨980417, by rfl⟩ : syracuseStep 1307223 = 1960835) B1960835
theorem B1471063 : Blo 1305971 1471063 := bstep (se 1 (by rfl) ⟨1103297, by rfl⟩ : syracuseStep 1471063 = 2206595) B2206595
theorem B3723869 : Blo 1305971 3723869 := bstep (se 3 (by rfl) ⟨698225, by rfl⟩ : syracuseStep 3723869 = 1396451) B1396451
theorem B1307243 : Blo 1305971 1307243 := bstep (se 1 (by rfl) ⟨980432, by rfl⟩ : syracuseStep 1307243 = 1960865) B1960865
theorem B1307255 : Blo 1305971 1307255 := bstep (se 1 (by rfl) ⟨980441, by rfl⟩ : syracuseStep 1307255 = 1960883) B1960883
theorem B1307275 : Blo 1305971 1307275 := bstep (se 1 (by rfl) ⟨980456, by rfl⟩ : syracuseStep 1307275 = 1960913) B1960913
theorem B1307287 : Blo 1305971 1307287 := bstep (se 1 (by rfl) ⟨980465, by rfl⟩ : syracuseStep 1307287 = 1960931) B1960931
theorem B1307307 : Blo 1305971 1307307 := bstep (se 1 (by rfl) ⟨980480, by rfl⟩ : syracuseStep 1307307 = 1960961) B1960961
theorem B1307319 : Blo 1305971 1307319 := bstep (se 1 (by rfl) ⟨980489, by rfl⟩ : syracuseStep 1307319 = 1960979) B1960979
theorem B1307339 : Blo 1305971 1307339 := bstep (se 1 (by rfl) ⟨980504, by rfl⟩ : syracuseStep 1307339 = 1961009) B1961009
theorem B1307351 : Blo 1305971 1307351 := bstep (se 1 (by rfl) ⟨980513, by rfl⟩ : syracuseStep 1307351 = 1961027) B1961027
theorem B3142361 : Blo 1305971 3142361 := bstep (se 2 (by rfl) ⟨1178385, by rfl⟩ : syracuseStep 3142361 = 2356771) B2356771
theorem B1307371 : Blo 1305971 1307371 := bstep (se 1 (by rfl) ⟨980528, by rfl⟩ : syracuseStep 1307371 = 1961057) B1961057
theorem B21205745 : Blo 1305971 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B1307383 : Blo 1305971 1307383 := bstep (se 1 (by rfl) ⟨980537, by rfl⟩ : syracuseStep 1307383 = 1961075) B1961075
theorem B4961027 : Blo 1305971 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B2831105 : Blo 1305971 2831105 := bstep (se 2 (by rfl) ⟨1061664, by rfl⟩ : syracuseStep 2831105 = 2123329) B2123329
theorem B1569547 : Blo 1305971 1569547 := bstep (se 1 (by rfl) ⟨1177160, by rfl⟩ : syracuseStep 1569547 = 2354321) B2354321
theorem B1307403 : Blo 1305971 1307403 := bstep (se 1 (by rfl) ⟨980552, by rfl⟩ : syracuseStep 1307403 = 1961105) B1961105
theorem B1471243 : Blo 1305971 1471243 := bstep (se 1 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 1471243 = 2206865) B2206865
theorem B1307415 : Blo 1305971 1307415 := bstep (se 1 (by rfl) ⟨980561, by rfl⟩ : syracuseStep 1307415 = 1961123) B1961123
theorem B1307435 : Blo 1305971 1307435 := bstep (se 1 (by rfl) ⟨980576, by rfl⟩ : syracuseStep 1307435 = 1961153) B1961153
theorem B1307447 : Blo 1305971 1307447 := bstep (se 1 (by rfl) ⟨980585, by rfl⟩ : syracuseStep 1307447 = 1961171) B1961171
theorem B1307467 : Blo 1305971 1307467 := bstep (se 1 (by rfl) ⟨980600, by rfl⟩ : syracuseStep 1307467 = 1961201) B1961201
theorem B1307479 : Blo 1305971 1307479 := bstep (se 1 (by rfl) ⟨980609, by rfl⟩ : syracuseStep 1307479 = 1961219) B1961219
theorem B3306329 : Blo 1305971 3306329 := bstep (se 2 (by rfl) ⟨1239873, by rfl⟩ : syracuseStep 3306329 = 2479747) B2479747
theorem B16749413 : Blo 1305971 16749413 := bstep (se 4 (by rfl) ⟨1570257, by rfl⟩ : syracuseStep 16749413 = 3140515) B3140515
theorem B1307499 : Blo 1305971 1307499 := bstep (se 1 (by rfl) ⟨980624, by rfl⟩ : syracuseStep 1307499 = 1961249) B1961249
theorem B1307511 : Blo 1305971 1307511 := bstep (se 1 (by rfl) ⟨980633, by rfl⟩ : syracuseStep 1307511 = 1961267) B1961267
theorem B1471351 : Blo 1305971 1471351 := bstep (se 1 (by rfl) ⟨1103513, by rfl⟩ : syracuseStep 1471351 = 2207027) B2207027
theorem B9917315 : Blo 1305971 9917315 := bstep (se 1 (by rfl) ⟨7437986, by rfl⟩ : syracuseStep 9917315 = 14875973) B14875973
theorem B1307531 : Blo 1305971 1307531 := bstep (se 1 (by rfl) ⟨980648, by rfl⟩ : syracuseStep 1307531 = 1961297) B1961297
theorem B1307543 : Blo 1305971 1307543 := bstep (se 1 (by rfl) ⟨980657, by rfl⟩ : syracuseStep 1307543 = 1961315) B1961315
theorem B1307563 : Blo 1305971 1307563 := bstep (se 1 (by rfl) ⟨980672, by rfl⟩ : syracuseStep 1307563 = 1961345) B1961345
theorem B4412339 : Blo 1305971 4412339 := bstep (se 1 (by rfl) ⟨3309254, by rfl⟩ : syracuseStep 4412339 = 6618509) B6618509
theorem B3724211 : Blo 1305971 3724211 := bstep (se 1 (by rfl) ⟨2793158, by rfl⟩ : syracuseStep 3724211 = 5586317) B5586317
theorem B1307575 : Blo 1305971 1307575 := bstep (se 1 (by rfl) ⟨980681, by rfl⟩ : syracuseStep 1307575 = 1961363) B1961363
theorem B1307595 : Blo 1305971 1307595 := bstep (se 1 (by rfl) ⟨980696, by rfl⟩ : syracuseStep 1307595 = 1961393) B1961393
theorem B1307607 : Blo 1305971 1307607 := bstep (se 1 (by rfl) ⟨980705, by rfl⟩ : syracuseStep 1307607 = 1961411) B1961411
theorem B11924441 : Blo 1305971 11924441 := bstep (se 2 (by rfl) ⟨4471665, by rfl⟩ : syracuseStep 11924441 = 8943331) B8943331
theorem B1307627 : Blo 1305971 1307627 := bstep (se 1 (by rfl) ⟨980720, by rfl⟩ : syracuseStep 1307627 = 1961441) B1961441
theorem B1307639 : Blo 1305971 1307639 := bstep (se 1 (by rfl) ⟨980729, by rfl⟩ : syracuseStep 1307639 = 1961459) B1961459
theorem B1307659 : Blo 1305971 1307659 := bstep (se 1 (by rfl) ⟨980744, by rfl⟩ : syracuseStep 1307659 = 1961489) B1961489
theorem B1307671 : Blo 1305971 1307671 := bstep (se 1 (by rfl) ⟨980753, by rfl⟩ : syracuseStep 1307671 = 1961507) B1961507
theorem B2790425 : Blo 1305971 2790425 := bstep (se 2 (by rfl) ⟨1046409, by rfl⟩ : syracuseStep 2790425 = 2092819) B2092819
theorem B1307691 : Blo 1305971 1307691 := bstep (se 1 (by rfl) ⟨980768, by rfl⟩ : syracuseStep 1307691 = 1961537) B1961537
theorem B1307703 : Blo 1305971 1307703 := bstep (se 1 (by rfl) ⟨980777, by rfl⟩ : syracuseStep 1307703 = 1961555) B1961555
theorem B1307723 : Blo 1305971 1307723 := bstep (se 1 (by rfl) ⟨980792, by rfl⟩ : syracuseStep 1307723 = 1961585) B1961585
theorem B2683991 : Blo 1305971 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B1307735 : Blo 1305971 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B1307755 : Blo 1305971 1307755 := bstep (se 1 (by rfl) ⟨980816, by rfl⟩ : syracuseStep 1307755 = 1961633) B1961633
theorem B1307767 : Blo 1305971 1307767 := bstep (se 1 (by rfl) ⟨980825, by rfl⟩ : syracuseStep 1307767 = 1961651) B1961651
theorem B1307787 : Blo 1305971 1307787 := bstep (se 1 (by rfl) ⟨980840, by rfl⟩ : syracuseStep 1307787 = 1961681) B1961681
theorem B1307799 : Blo 1305971 1307799 := bstep (se 1 (by rfl) ⟨980849, by rfl⟩ : syracuseStep 1307799 = 1961699) B1961699
theorem B1307819 : Blo 1305971 1307819 := bstep (se 1 (by rfl) ⟨980864, by rfl⟩ : syracuseStep 1307819 = 1961729) B1961729
theorem B1307831 : Blo 1305971 1307831 := bstep (se 1 (by rfl) ⟨980873, by rfl⟩ : syracuseStep 1307831 = 1961747) B1961747
theorem B4412609 : Blo 1305971 4412609 := bstep (se 2 (by rfl) ⟨1654728, by rfl⟩ : syracuseStep 4412609 = 3309457) B3309457
theorem B4961483 : Blo 1305971 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B1307851 : Blo 1305971 1307851 := bstep (se 1 (by rfl) ⟨980888, by rfl⟩ : syracuseStep 1307851 = 1961777) B1961777
theorem B13407437 : Blo 1305971 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1307863 : Blo 1305971 1307863 := bstep (se 1 (by rfl) ⟨980897, by rfl⟩ : syracuseStep 1307863 = 1961795) B1961795
theorem B1307883 : Blo 1305971 1307883 := bstep (se 1 (by rfl) ⟨980912, by rfl⟩ : syracuseStep 1307883 = 1961825) B1961825
theorem B1307895 : Blo 1305971 1307895 := bstep (se 1 (by rfl) ⟨980921, by rfl⟩ : syracuseStep 1307895 = 1961843) B1961843
theorem B1307915 : Blo 1305971 1307915 := bstep (se 1 (by rfl) ⟨980936, by rfl⟩ : syracuseStep 1307915 = 1961873) B1961873
theorem B1307927 : Blo 1305971 1307927 := bstep (se 1 (by rfl) ⟨980945, by rfl⟩ : syracuseStep 1307927 = 1961891) B1961891
theorem B1307947 : Blo 1305971 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B1307959 : Blo 1305971 1307959 := bstep (se 1 (by rfl) ⟨980969, by rfl⟩ : syracuseStep 1307959 = 1961939) B1961939
theorem B4961681 : Blo 1305971 4961681 := bstep (se 2 (by rfl) ⟨1860630, by rfl⟩ : syracuseStep 4961681 = 3721261) B3721261
theorem B2479511 : Blo 1305971 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B5584301 : Blo 1305971 5584301 := bstep (se 3 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 5584301 = 2094113) B2094113
theorem B2979287 : Blo 1305971 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B9426449 : Blo 1305971 9426449 := bstep (se 2 (by rfl) ⟨3534918, by rfl⟩ : syracuseStep 9426449 = 7069837) B7069837
theorem B8377987 : Blo 1305971 8377987 := bstep (se 1 (by rfl) ⟨6283490, by rfl⟩ : syracuseStep 8377987 = 12566981) B12566981
theorem B6616727 : Blo 1305971 6616727 := bstep (se 1 (by rfl) ⟨4962545, by rfl⟩ : syracuseStep 6616727 = 9925091) B9925091
theorem B2791091 : Blo 1305971 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B2938571 : Blo 1305971 2938571 := bstep (se 1 (by rfl) ⟨2203928, by rfl⟩ : syracuseStep 2938571 = 4407857) B4407857
theorem B4413149 : Blo 1305971 4413149 := bstep (se 3 (by rfl) ⟨827465, by rfl⟩ : syracuseStep 4413149 = 1654931) B1654931
theorem B2938625 : Blo 1305971 2938625 := bstep (se 2 (by rfl) ⟨1101984, by rfl⟩ : syracuseStep 2938625 = 2203969) B2203969
theorem B23844725 : Blo 1305971 23844725 := bstep (se 5 (by rfl) ⟨1117721, by rfl⟩ : syracuseStep 23844725 = 2235443) B2235443
theorem B2480051 : Blo 1305971 2480051 := bstep (se 1 (by rfl) ⟨1860038, by rfl⟩ : syracuseStep 2480051 = 3720077) B3720077
theorem B1325003 : Blo 1305971 1325003 := bstep (se 1 (by rfl) ⟨993752, by rfl⟩ : syracuseStep 1325003 = 1987505) B1987505
theorem B2938841 : Blo 1305971 2938841 := bstep (se 2 (by rfl) ⟨1102065, by rfl⟩ : syracuseStep 2938841 = 2204131) B2204131
theorem B2938931 : Blo 1305971 2938931 := bstep (se 1 (by rfl) ⟨2204198, by rfl⟩ : syracuseStep 2938931 = 4408397) B4408397
theorem B3774539 : Blo 1305971 3774539 := bstep (se 1 (by rfl) ⟨2830904, by rfl⟩ : syracuseStep 3774539 = 5661809) B5661809
theorem B2938967 : Blo 1305971 2938967 := bstep (se 1 (by rfl) ⟨2204225, by rfl⟩ : syracuseStep 2938967 = 4408451) B4408451
theorem B4962455 : Blo 1305971 4962455 := bstep (se 1 (by rfl) ⟨3721841, by rfl⟩ : syracuseStep 4962455 = 7443683) B7443683
theorem B2939147 : Blo 1305971 2939147 := bstep (se 1 (by rfl) ⟨2204360, by rfl⟩ : syracuseStep 2939147 = 4408721) B4408721
theorem B2939201 : Blo 1305971 2939201 := bstep (se 2 (by rfl) ⟨1102200, by rfl⟩ : syracuseStep 2939201 = 2204401) B2204401
theorem B4962653 : Blo 1305971 4962653 := bstep (se 3 (by rfl) ⟨930497, by rfl⟩ : syracuseStep 4962653 = 1860995) B1860995
theorem B2480537 : Blo 1305971 2480537 := bstep (se 2 (by rfl) ⟨930201, by rfl⟩ : syracuseStep 2480537 = 1860403) B1860403
theorem B3307979 : Blo 1305971 3307979 := bstep (se 1 (by rfl) ⟨2480984, by rfl⟩ : syracuseStep 3307979 = 4961969) B4961969
theorem B2939417 : Blo 1305971 2939417 := bstep (se 2 (by rfl) ⟨1102281, by rfl⟩ : syracuseStep 2939417 = 2204563) B2204563
theorem B15096395 : Blo 1305971 15096395 := bstep (se 1 (by rfl) ⟨11322296, by rfl⟩ : syracuseStep 15096395 = 22644593) B22644593
theorem B2939507 : Blo 1305971 2939507 := bstep (se 1 (by rfl) ⟨2204630, by rfl⟩ : syracuseStep 2939507 = 4409261) B4409261
theorem B2792065 : Blo 1305971 2792065 := bstep (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) B2094049
theorem B2939543 : Blo 1305971 2939543 := bstep (se 1 (by rfl) ⟨2204657, by rfl⟩ : syracuseStep 2939543 = 4409315) B4409315
theorem B4184779 : Blo 1305971 4184779 := bstep (se 1 (by rfl) ⟨3138584, by rfl⟩ : syracuseStep 4184779 = 6277169) B6277169
theorem B1653463 : Blo 1305971 1653463 := bstep (se 1 (by rfl) ⟨1240097, by rfl⟩ : syracuseStep 1653463 = 2480195) B2480195
theorem B9427747 : Blo 1305971 9427747 := bstep (se 1 (by rfl) ⟨7070810, by rfl⟩ : syracuseStep 9427747 = 14141621) B14141621
theorem B2513729 : Blo 1305971 2513729 := bstep (se 2 (by rfl) ⟨942648, by rfl⟩ : syracuseStep 2513729 = 1885297) B1885297
theorem B2939723 : Blo 1305971 2939723 := bstep (se 1 (by rfl) ⟨2204792, by rfl⟩ : syracuseStep 2939723 = 4409585) B4409585
theorem B4414283 : Blo 1305971 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B2939777 : Blo 1305971 2939777 := bstep (se 2 (by rfl) ⟨1102416, by rfl⟩ : syracuseStep 2939777 = 2204833) B2204833
theorem B2792321 : Blo 1305971 2792321 := bstep (se 2 (by rfl) ⟨1047120, by rfl⟩ : syracuseStep 2792321 = 2094241) B2094241
theorem B5372851 : Blo 1305971 5372851 := bstep (se 1 (by rfl) ⟨4029638, by rfl⟩ : syracuseStep 5372851 = 8059277) B8059277
theorem B2792407 : Blo 1305971 2792407 := bstep (se 1 (by rfl) ⟨2094305, by rfl⟩ : syracuseStep 2792407 = 4188611) B4188611
theorem B22346765 : Blo 1305971 22346765 := bstep (se 3 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 22346765 = 8380037) B8380037
theorem B17890379 : Blo 1305971 17890379 := bstep (se 1 (by rfl) ⟨13417784, by rfl⟩ : syracuseStep 17890379 = 26835569) B26835569
theorem B2939993 : Blo 1305971 2939993 := bstep (se 2 (by rfl) ⟨1102497, by rfl⟩ : syracuseStep 2939993 = 2204995) B2204995
theorem B2940083 : Blo 1305971 2940083 := bstep (se 1 (by rfl) ⟨2205062, by rfl⟩ : syracuseStep 2940083 = 4410125) B4410125
theorem B11164877 : Blo 1305971 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B2940119 : Blo 1305971 2940119 := bstep (se 1 (by rfl) ⟨2205089, by rfl⟩ : syracuseStep 2940119 = 4410179) B4410179
theorem B4185395 : Blo 1305971 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B2940299 : Blo 1305971 2940299 := bstep (se 1 (by rfl) ⟨2205224, by rfl⟩ : syracuseStep 2940299 = 4410449) B4410449
theorem B3972503 : Blo 1305971 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B3308951 : Blo 1305971 3308951 := bstep (se 1 (by rfl) ⟨2481713, by rfl⟩ : syracuseStep 3308951 = 4963427) B4963427
theorem B2940353 : Blo 1305971 2940353 := bstep (se 2 (by rfl) ⟨1102632, by rfl⟩ : syracuseStep 2940353 = 2205265) B2205265
theorem B1654283 : Blo 1305971 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B7446167 : Blo 1305971 7446167 := bstep (se 1 (by rfl) ⟨5584625, by rfl⟩ : syracuseStep 7446167 = 11169251) B11169251
theorem B2940569 : Blo 1305971 2940569 := bstep (se 2 (by rfl) ⟨1102713, by rfl⟩ : syracuseStep 2940569 = 2205427) B2205427
theorem B4775617 : Blo 1305971 4775617 := bstep (se 2 (by rfl) ⟨1790856, by rfl⟩ : syracuseStep 4775617 = 3581713) B3581713
theorem B2940659 : Blo 1305971 2940659 := bstep (se 1 (by rfl) ⟨2205494, by rfl⟩ : syracuseStep 2940659 = 4410989) B4410989
theorem B2940695 : Blo 1305971 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B9928493 : Blo 1305971 9928493 := bstep (se 3 (by rfl) ⟨1861592, by rfl⟩ : syracuseStep 9928493 = 3723185) B3723185
theorem B2481995 : Blo 1305971 2481995 := bstep (se 1 (by rfl) ⟨1861496, by rfl⟩ : syracuseStep 2481995 = 3722993) B3722993
theorem B5578627 : Blo 1305971 5578627 := bstep (se 1 (by rfl) ⟨4183970, by rfl⟩ : syracuseStep 5578627 = 8367941) B8367941
theorem B2940875 : Blo 1305971 2940875 := bstep (se 1 (by rfl) ⟨2205656, by rfl⟩ : syracuseStep 2940875 = 4411313) B4411313
theorem B4186073 : Blo 1305971 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B3309569 : Blo 1305971 3309569 := bstep (se 2 (by rfl) ⟨1241088, by rfl⟩ : syracuseStep 3309569 = 2482177) B2482177
theorem B11157527 : Blo 1305971 11157527 := bstep (se 1 (by rfl) ⟨8368145, by rfl⟩ : syracuseStep 11157527 = 16736291) B16736291
theorem B2941199 : Blo 1305971 2941199 := bstep (se 1 (by rfl) ⟨2205899, by rfl⟩ : syracuseStep 2941199 = 4411799) B4411799
theorem B7438625 : Blo 1305971 7438625 := bstep (se 2 (by rfl) ⟨2789484, by rfl⟩ : syracuseStep 7438625 = 5578969) B5578969
theorem B2941217 : Blo 1305971 2941217 := bstep (se 2 (by rfl) ⟨1102956, by rfl⟩ : syracuseStep 2941217 = 2205913) B2205913
theorem B1655083 : Blo 1305971 1655083 := bstep (se 1 (by rfl) ⟨1241312, by rfl⟩ : syracuseStep 1655083 = 2482625) B2482625
theorem B6619481 : Blo 1305971 6619481 := bstep (se 2 (by rfl) ⟨2482305, by rfl⟩ : syracuseStep 6619481 = 4964611) B4964611
theorem B2204023 : Blo 1305971 2204023 := bstep (se 1 (by rfl) ⟨1653017, by rfl⟩ : syracuseStep 2204023 = 3306035) B3306035
theorem B3309943 : Blo 1305971 3309943 := bstep (se 1 (by rfl) ⟨2482457, by rfl⟩ : syracuseStep 3309943 = 4964915) B4964915
theorem B46547345 : Blo 1305971 46547345 := bstep (se 2 (by rfl) ⟨17455254, by rfl⟩ : syracuseStep 46547345 = 34910509) B34910509
theorem B2482579 : Blo 1305971 2482579 := bstep (se 1 (by rfl) ⟨1861934, by rfl⟩ : syracuseStep 2482579 = 3723869) B3723869
theorem B2982415 : Blo 1305971 2982415 := bstep (se 1 (by rfl) ⟨2236811, by rfl⟩ : syracuseStep 2982415 = 4473623) B4473623
theorem B1655311 : Blo 1305971 1655311 := bstep (se 1 (by rfl) ⟨1241483, by rfl⟩ : syracuseStep 1655311 = 2482967) B2482967
theorem B7438877 : Blo 1305971 7438877 := bstep (se 3 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 7438877 = 2789579) B2789579
theorem B2204219 : Blo 1305971 2204219 := bstep (se 1 (by rfl) ⟨1653164, by rfl⟩ : syracuseStep 2204219 = 3306329) B3306329
theorem B11166275 : Blo 1305971 11166275 := bstep (se 1 (by rfl) ⟨8374706, by rfl⟩ : syracuseStep 11166275 = 16749413) B16749413
theorem B10601027 : Blo 1305971 10601027 := bstep (se 1 (by rfl) ⟨7950770, by rfl⟩ : syracuseStep 10601027 = 15901541) B15901541
theorem B6611543 : Blo 1305971 6611543 := bstep (se 1 (by rfl) ⟨4958657, by rfl⟩ : syracuseStep 6611543 = 9917315) B9917315
theorem B2941559 : Blo 1305971 2941559 := bstep (se 1 (by rfl) ⟨2206169, by rfl⟩ : syracuseStep 2941559 = 4412339) B4412339
theorem B2482807 : Blo 1305971 2482807 := bstep (se 1 (by rfl) ⟨1862105, by rfl⟩ : syracuseStep 2482807 = 3724211) B3724211
theorem B1860283 : Blo 1305971 1860283 := bstep (se 1 (by rfl) ⟨1395212, by rfl⟩ : syracuseStep 1860283 = 2790425) B2790425
theorem B5030657 : Blo 1305971 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B3719951 : Blo 1305971 3719951 := bstep (se 1 (by rfl) ⟨2789963, by rfl⟩ : syracuseStep 3719951 = 5579927) B5579927
theorem B2941739 : Blo 1305971 2941739 := bstep (se 1 (by rfl) ⟨2206304, by rfl⟩ : syracuseStep 2941739 = 4412609) B4412609
theorem B3310379 : Blo 1305971 3310379 := bstep (se 1 (by rfl) ⟨2482784, by rfl⟩ : syracuseStep 3310379 = 4965569) B4965569
theorem B8938291 : Blo 1305971 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B5579705 : Blo 1305971 5579705 := bstep (se 2 (by rfl) ⟨2092389, by rfl⟩ : syracuseStep 5579705 = 4184779) B4184779
theorem B2204617 : Blo 1305971 2204617 := bstep (se 2 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 2204617 = 1653463) B1653463
theorem B25469957 : Blo 1305971 25469957 := bstep (se 4 (by rfl) ⟨2387808, by rfl⟩ : syracuseStep 25469957 = 4775617) B4775617
theorem B6284299 : Blo 1305971 6284299 := bstep (se 1 (by rfl) ⟨4713224, by rfl⟩ : syracuseStep 6284299 = 9426449) B9426449
theorem B3138593 : Blo 1305971 3138593 := bstep (se 2 (by rfl) ⟨1176972, by rfl⟩ : syracuseStep 3138593 = 2353945) B2353945
theorem B1958969 : Blo 1305971 1958969 := bstep (se 2 (by rfl) ⟨734613, by rfl⟩ : syracuseStep 1958969 = 1469227) B1469227
theorem B6612029 : Blo 1305971 6612029 := bstep (se 3 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 6612029 = 2479511) B2479511
theorem B10593341 : Blo 1305971 10593341 := bstep (se 3 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 10593341 = 3972503) B3972503
theorem B1860727 : Blo 1305971 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B1959047 : Blo 1305971 1959047 := bstep (se 1 (by rfl) ⟨1469285, by rfl⟩ : syracuseStep 1959047 = 2938571) B2938571
theorem B2942099 : Blo 1305971 2942099 := bstep (se 1 (by rfl) ⟨2206574, by rfl⟩ : syracuseStep 2942099 = 4413149) B4413149
theorem B1959083 : Blo 1305971 1959083 := bstep (se 1 (by rfl) ⟨1469312, by rfl⟩ : syracuseStep 1959083 = 2938625) B2938625
theorem B1959113 : Blo 1305971 1959113 := bstep (se 2 (by rfl) ⟨734667, by rfl⟩ : syracuseStep 1959113 = 1469335) B1469335
theorem B2942153 : Blo 1305971 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B7070921 : Blo 1305971 7070921 := bstep (se 2 (by rfl) ⟨2651595, by rfl⟩ : syracuseStep 7070921 = 5303191) B5303191
theorem B1959227 : Blo 1305971 1959227 := bstep (se 1 (by rfl) ⟨1469420, by rfl⟩ : syracuseStep 1959227 = 2938841) B2938841
theorem B1959287 : Blo 1305971 1959287 := bstep (se 1 (by rfl) ⟨1469465, by rfl⟩ : syracuseStep 1959287 = 2938931) B2938931
theorem B2516359 : Blo 1305971 2516359 := bstep (se 1 (by rfl) ⟨1887269, by rfl⟩ : syracuseStep 2516359 = 3774539) B3774539
theorem B1959311 : Blo 1305971 1959311 := bstep (se 1 (by rfl) ⟨1469483, by rfl⟩ : syracuseStep 1959311 = 2938967) B2938967
theorem B1959353 : Blo 1305971 1959353 := bstep (se 2 (by rfl) ⟨734757, by rfl⟩ : syracuseStep 1959353 = 1469515) B1469515
theorem B1959431 : Blo 1305971 1959431 := bstep (se 1 (by rfl) ⟨1469573, by rfl⟩ : syracuseStep 1959431 = 2939147) B2939147
theorem B1959467 : Blo 1305971 1959467 := bstep (se 1 (by rfl) ⟨1469600, by rfl⟩ : syracuseStep 1959467 = 2939201) B2939201
theorem B1959497 : Blo 1305971 1959497 := bstep (se 2 (by rfl) ⟨734811, by rfl⟩ : syracuseStep 1959497 = 1469623) B1469623
theorem B2205319 : Blo 1305971 2205319 := bstep (se 1 (by rfl) ⟨1653989, by rfl⟩ : syracuseStep 2205319 = 3307979) B3307979
theorem B1959611 : Blo 1305971 1959611 := bstep (se 1 (by rfl) ⟨1469708, by rfl⟩ : syracuseStep 1959611 = 2939417) B2939417
theorem B1959671 : Blo 1305971 1959671 := bstep (se 1 (by rfl) ⟨1469753, by rfl⟩ : syracuseStep 1959671 = 2939507) B2939507
theorem B1959695 : Blo 1305971 1959695 := bstep (se 1 (by rfl) ⟨1469771, by rfl⟩ : syracuseStep 1959695 = 2939543) B2939543
theorem B1959737 : Blo 1305971 1959737 := bstep (se 2 (by rfl) ⟨734901, by rfl⟩ : syracuseStep 1959737 = 1469803) B1469803
theorem B3721079 : Blo 1305971 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B1959815 : Blo 1305971 1959815 := bstep (se 1 (by rfl) ⟨1469861, by rfl⟩ : syracuseStep 1959815 = 2939723) B2939723
theorem B2942855 : Blo 1305971 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B1959851 : Blo 1305971 1959851 := bstep (se 1 (by rfl) ⟨1469888, by rfl⟩ : syracuseStep 1959851 = 2939777) B2939777
theorem B1861547 : Blo 1305971 1861547 := bstep (se 1 (by rfl) ⟨1396160, by rfl⟩ : syracuseStep 1861547 = 2792321) B2792321
theorem B1959881 : Blo 1305971 1959881 := bstep (se 2 (by rfl) ⟨734955, by rfl⟩ : syracuseStep 1959881 = 1469911) B1469911
theorem B37668887 : Blo 1305971 37668887 := bstep (se 1 (by rfl) ⟨28251665, by rfl⟩ : syracuseStep 37668887 = 56503331) B56503331
theorem B1959995 : Blo 1305971 1959995 := bstep (se 1 (by rfl) ⟨1469996, by rfl⟩ : syracuseStep 1959995 = 2939993) B2939993
theorem B5662781 : Blo 1305971 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B1960055 : Blo 1305971 1960055 := bstep (se 1 (by rfl) ⟨1470041, by rfl⟩ : syracuseStep 1960055 = 2940083) B2940083
theorem B1960079 : Blo 1305971 1960079 := bstep (se 1 (by rfl) ⟨1470059, by rfl⟩ : syracuseStep 1960079 = 2940119) B2940119
theorem B1960121 : Blo 1305971 1960121 := bstep (se 2 (by rfl) ⟨735045, by rfl⟩ : syracuseStep 1960121 = 1470091) B1470091
theorem B1960199 : Blo 1305971 1960199 := bstep (se 1 (by rfl) ⟨1470149, by rfl⟩ : syracuseStep 1960199 = 2940299) B2940299
theorem B2205967 : Blo 1305971 2205967 := bstep (se 1 (by rfl) ⟨1654475, by rfl⟩ : syracuseStep 2205967 = 3308951) B3308951
theorem B1960235 : Blo 1305971 1960235 := bstep (se 1 (by rfl) ⟨1470176, by rfl⟩ : syracuseStep 1960235 = 2940353) B2940353
theorem B1960265 : Blo 1305971 1960265 := bstep (se 2 (by rfl) ⟨735099, by rfl⟩ : syracuseStep 1960265 = 1470199) B1470199
theorem B4409747 : Blo 1305971 4409747 := bstep (se 1 (by rfl) ⟨3307310, by rfl⟩ : syracuseStep 4409747 = 6614621) B6614621
theorem B6621587 : Blo 1305971 6621587 := bstep (se 1 (by rfl) ⟨4966190, by rfl⟩ : syracuseStep 6621587 = 9932381) B9932381
theorem B1960379 : Blo 1305971 1960379 := bstep (se 1 (by rfl) ⟨1470284, by rfl⟩ : syracuseStep 1960379 = 2940569) B2940569
theorem B1960439 : Blo 1305971 1960439 := bstep (se 1 (by rfl) ⟨1470329, by rfl⟩ : syracuseStep 1960439 = 2940659) B2940659
theorem B1960463 : Blo 1305971 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B3533341 : Blo 1305971 3533341 := bstep (se 3 (by rfl) ⟨662501, by rfl⟩ : syracuseStep 3533341 = 1325003) B1325003
theorem B31803947 : Blo 1305971 31803947 := bstep (se 1 (by rfl) ⟨23852960, by rfl⟩ : syracuseStep 31803947 = 47705921) B47705921
theorem B1960505 : Blo 1305971 1960505 := bstep (se 2 (by rfl) ⟨735189, by rfl⟩ : syracuseStep 1960505 = 1470379) B1470379
theorem B7064131 : Blo 1305971 7064131 := bstep (se 1 (by rfl) ⟨5298098, by rfl⟩ : syracuseStep 7064131 = 10596197) B10596197
theorem B1960583 : Blo 1305971 1960583 := bstep (se 1 (by rfl) ⟨1470437, by rfl⟩ : syracuseStep 1960583 = 2940875) B2940875
theorem B1960619 : Blo 1305971 1960619 := bstep (se 1 (by rfl) ⟨1470464, by rfl⟩ : syracuseStep 1960619 = 2940929) B2940929
theorem B19098305 : Blo 1305971 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B1960649 : Blo 1305971 1960649 := bstep (se 2 (by rfl) ⟨735243, by rfl⟩ : syracuseStep 1960649 = 1470487) B1470487
theorem B2206507 : Blo 1305971 2206507 := bstep (se 1 (by rfl) ⟨1654880, by rfl⟩ : syracuseStep 2206507 = 3309761) B3309761
theorem B6613811 : Blo 1305971 6613811 := bstep (se 1 (by rfl) ⟨4960358, by rfl⟩ : syracuseStep 6613811 = 9920717) B9920717
theorem B1960763 : Blo 1305971 1960763 := bstep (se 1 (by rfl) ⟨1470572, by rfl⟩ : syracuseStep 1960763 = 2941145) B2941145
theorem B7441267 : Blo 1305971 7441267 := bstep (se 1 (by rfl) ⟨5580950, by rfl⟩ : syracuseStep 7441267 = 11161901) B11161901
theorem B1960823 : Blo 1305971 1960823 := bstep (se 1 (by rfl) ⟨1470617, by rfl⟩ : syracuseStep 1960823 = 2941235) B2941235
theorem B5581703 : Blo 1305971 5581703 := bstep (se 1 (by rfl) ⟨4186277, by rfl⟩ : syracuseStep 5581703 = 8372555) B8372555
theorem B1960847 : Blo 1305971 1960847 := bstep (se 1 (by rfl) ⟨1470635, by rfl⟩ : syracuseStep 1960847 = 2941271) B2941271
theorem B1960889 : Blo 1305971 1960889 := bstep (se 2 (by rfl) ⟨735333, by rfl⟩ : syracuseStep 1960889 = 1470667) B1470667
theorem B2206649 : Blo 1305971 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B1469371 : Blo 1305971 1469371 := bstep (se 1 (by rfl) ⟨1102028, by rfl⟩ : syracuseStep 1469371 = 2204057) B2204057
theorem B1960967 : Blo 1305971 1960967 := bstep (se 1 (by rfl) ⟨1470725, by rfl⟩ : syracuseStep 1960967 = 2941451) B2941451
theorem B1961003 : Blo 1305971 1961003 := bstep (se 1 (by rfl) ⟨1470752, by rfl⟩ : syracuseStep 1961003 = 2941505) B2941505
theorem B1961033 : Blo 1305971 1961033 := bstep (se 2 (by rfl) ⟨735387, by rfl⟩ : syracuseStep 1961033 = 1470775) B1470775
theorem B6614135 : Blo 1305971 6614135 := bstep (se 1 (by rfl) ⟨4960601, by rfl⟩ : syracuseStep 6614135 = 9921203) B9921203
theorem B5581943 : Blo 1305971 5581943 := bstep (se 1 (by rfl) ⟨4186457, by rfl⟩ : syracuseStep 5581943 = 8372915) B8372915
theorem B1887403 : Blo 1305971 1887403 := bstep (se 1 (by rfl) ⟨1415552, by rfl⟩ : syracuseStep 1887403 = 2831105) B2831105
theorem B1961147 : Blo 1305971 1961147 := bstep (se 1 (by rfl) ⟨1470860, by rfl⟩ : syracuseStep 1961147 = 2941721) B2941721
theorem B1961207 : Blo 1305971 1961207 := bstep (se 1 (by rfl) ⟨1470905, by rfl⟩ : syracuseStep 1961207 = 2941811) B2941811
theorem B1961231 : Blo 1305971 1961231 := bstep (se 1 (by rfl) ⟨1470923, by rfl⟩ : syracuseStep 1961231 = 2941847) B2941847
theorem B1961273 : Blo 1305971 1961273 := bstep (se 2 (by rfl) ⟨735477, by rfl⟩ : syracuseStep 1961273 = 1470955) B1470955
theorem B7949627 : Blo 1305971 7949627 := bstep (se 1 (by rfl) ⟨5962220, by rfl⟩ : syracuseStep 7949627 = 11924441) B11924441
theorem B1305991 : Blo 1305971 1305991 := bstep (se 1 (by rfl) ⟨979493, by rfl⟩ : syracuseStep 1305991 = 1958987) B1958987
theorem B1961351 : Blo 1305971 1961351 := bstep (se 1 (by rfl) ⟨1471013, by rfl⟩ : syracuseStep 1961351 = 2942027) B2942027
theorem B1305999 : Blo 1305971 1305999 := bstep (se 1 (by rfl) ⟨979499, by rfl⟩ : syracuseStep 1305999 = 1958999) B1958999
theorem B1789327 : Blo 1305971 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B1469839 : Blo 1305971 1469839 := bstep (se 1 (by rfl) ⟨1102379, by rfl⟩ : syracuseStep 1469839 = 2204759) B2204759
theorem B1961387 : Blo 1305971 1961387 := bstep (se 1 (by rfl) ⟨1471040, by rfl⟩ : syracuseStep 1961387 = 2942081) B2942081
theorem B1306043 : Blo 1305971 1306043 := bstep (se 1 (by rfl) ⟨979532, by rfl⟩ : syracuseStep 1306043 = 1959065) B1959065
theorem B1961417 : Blo 1305971 1961417 := bstep (se 2 (by rfl) ⟨735531, by rfl⟩ : syracuseStep 1961417 = 1471063) B1471063
theorem B3722753 : Blo 1305971 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B1306119 : Blo 1305971 1306119 := bstep (se 1 (by rfl) ⟨979589, by rfl⟩ : syracuseStep 1306119 = 1959179) B1959179
theorem B1306127 : Blo 1305971 1306127 := bstep (se 1 (by rfl) ⟨979595, by rfl⟩ : syracuseStep 1306127 = 1959191) B1959191
theorem B1306171 : Blo 1305971 1306171 := bstep (se 1 (by rfl) ⟨979628, by rfl⟩ : syracuseStep 1306171 = 1959257) B1959257
theorem B1961531 : Blo 1305971 1961531 := bstep (se 1 (by rfl) ⟨1471148, by rfl⟩ : syracuseStep 1961531 = 2942297) B2942297
theorem B3722867 : Blo 1305971 3722867 := bstep (se 1 (by rfl) ⟨2792150, by rfl⟩ : syracuseStep 3722867 = 5584301) B5584301
theorem B1961591 : Blo 1305971 1961591 := bstep (se 1 (by rfl) ⟨1471193, by rfl⟩ : syracuseStep 1961591 = 2942387) B2942387
theorem B1306247 : Blo 1305971 1306247 := bstep (se 1 (by rfl) ⟨979685, by rfl⟩ : syracuseStep 1306247 = 1959371) B1959371
theorem B1306255 : Blo 1305971 1306255 := bstep (se 1 (by rfl) ⟨979691, by rfl⟩ : syracuseStep 1306255 = 1959383) B1959383
theorem B1986191 : Blo 1305971 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B1961615 : Blo 1305971 1961615 := bstep (se 1 (by rfl) ⟨1471211, by rfl⟩ : syracuseStep 1961615 = 2942423) B2942423
theorem B2092729 : Blo 1305971 2092729 := bstep (se 2 (by rfl) ⟨784773, by rfl⟩ : syracuseStep 2092729 = 1569547) B1569547
theorem B1961657 : Blo 1305971 1961657 := bstep (se 2 (by rfl) ⟨735621, by rfl⟩ : syracuseStep 1961657 = 1471243) B1471243
theorem B1306299 : Blo 1305971 1306299 := bstep (se 1 (by rfl) ⟨979724, by rfl⟩ : syracuseStep 1306299 = 1959449) B1959449
theorem B12570329 : Blo 1305971 12570329 := bstep (se 2 (by rfl) ⟨4713873, by rfl⟩ : syracuseStep 12570329 = 9427747) B9427747
theorem B1306375 : Blo 1305971 1306375 := bstep (se 1 (by rfl) ⟨979781, by rfl⟩ : syracuseStep 1306375 = 1959563) B1959563
theorem B1961735 : Blo 1305971 1961735 := bstep (se 1 (by rfl) ⟨1471301, by rfl⟩ : syracuseStep 1961735 = 2942603) B2942603
theorem B1306383 : Blo 1305971 1306383 := bstep (se 1 (by rfl) ⟨979787, by rfl⟩ : syracuseStep 1306383 = 1959575) B1959575
theorem B4411151 : Blo 1305971 4411151 := bstep (se 1 (by rfl) ⟨3308363, by rfl⟩ : syracuseStep 4411151 = 6616727) B6616727
theorem B10055461 : Blo 1305971 10055461 := bstep (se 4 (by rfl) ⟨942699, by rfl⟩ : syracuseStep 10055461 = 1885399) B1885399
theorem B1961771 : Blo 1305971 1961771 := bstep (se 1 (by rfl) ⟨1471328, by rfl⟩ : syracuseStep 1961771 = 2942657) B2942657
theorem B1306427 : Blo 1305971 1306427 := bstep (se 1 (by rfl) ⟨979820, by rfl⟩ : syracuseStep 1306427 = 1959641) B1959641
theorem B1961801 : Blo 1305971 1961801 := bstep (se 2 (by rfl) ⟨735675, by rfl⟩ : syracuseStep 1961801 = 1471351) B1471351
theorem B1306503 : Blo 1305971 1306503 := bstep (se 1 (by rfl) ⟨979877, by rfl⟩ : syracuseStep 1306503 = 1959755) B1959755
theorem B1470343 : Blo 1305971 1470343 := bstep (se 1 (by rfl) ⟨1102757, by rfl⟩ : syracuseStep 1470343 = 2205515) B2205515
theorem B1306511 : Blo 1305971 1306511 := bstep (se 1 (by rfl) ⟨979883, by rfl⟩ : syracuseStep 1306511 = 1959767) B1959767
theorem B7163801 : Blo 1305971 7163801 := bstep (se 2 (by rfl) ⟨2686425, by rfl⟩ : syracuseStep 7163801 = 5372851) B5372851
theorem B15896483 : Blo 1305971 15896483 := bstep (se 1 (by rfl) ⟨11922362, by rfl⟩ : syracuseStep 15896483 = 23844725) B23844725
theorem B1306555 : Blo 1305971 1306555 := bstep (se 1 (by rfl) ⟨979916, by rfl⟩ : syracuseStep 1306555 = 1959833) B1959833
theorem B1961915 : Blo 1305971 1961915 := bstep (se 1 (by rfl) ⟨1471436, by rfl⟩ : syracuseStep 1961915 = 2942873) B2942873
theorem B3723209 : Blo 1305971 3723209 := bstep (se 2 (by rfl) ⟨1396203, by rfl⟩ : syracuseStep 3723209 = 2792407) B2792407
theorem B7548893 : Blo 1305971 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B1306631 : Blo 1305971 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B1306639 : Blo 1305971 1306639 := bstep (se 1 (by rfl) ⟨979979, by rfl⟩ : syracuseStep 1306639 = 1959959) B1959959
theorem B4411421 : Blo 1305971 4411421 := bstep (se 3 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 4411421 = 1654283) B1654283
theorem B1306683 : Blo 1305971 1306683 := bstep (se 1 (by rfl) ⟨980012, by rfl⟩ : syracuseStep 1306683 = 1960025) B1960025
theorem B1470523 : Blo 1305971 1470523 := bstep (se 1 (by rfl) ⟨1102892, by rfl⟩ : syracuseStep 1470523 = 2205785) B2205785
theorem B6615107 : Blo 1305971 6615107 := bstep (se 1 (by rfl) ⟨4961330, by rfl⟩ : syracuseStep 6615107 = 9922661) B9922661
theorem B1306759 : Blo 1305971 1306759 := bstep (se 1 (by rfl) ⟨980069, by rfl⟩ : syracuseStep 1306759 = 1960139) B1960139
theorem B3534983 : Blo 1305971 3534983 := bstep (se 1 (by rfl) ⟨2651237, by rfl⟩ : syracuseStep 3534983 = 5302475) B5302475
theorem B1306767 : Blo 1305971 1306767 := bstep (se 1 (by rfl) ⟨980075, by rfl⟩ : syracuseStep 1306767 = 1960151) B1960151
theorem B1306811 : Blo 1305971 1306811 := bstep (se 1 (by rfl) ⟨980108, by rfl⟩ : syracuseStep 1306811 = 1960217) B1960217
theorem B1306887 : Blo 1305971 1306887 := bstep (se 1 (by rfl) ⟨980165, by rfl⟩ : syracuseStep 1306887 = 1960331) B1960331
theorem B1306895 : Blo 1305971 1306895 := bstep (se 1 (by rfl) ⟨980171, by rfl⟩ : syracuseStep 1306895 = 1960343) B1960343
theorem B7442725 : Blo 1305971 7442725 := bstep (se 4 (by rfl) ⟨697755, by rfl⟩ : syracuseStep 7442725 = 1395511) B1395511
theorem B2650411 : Blo 1305971 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B1306939 : Blo 1305971 1306939 := bstep (se 1 (by rfl) ⟨980204, by rfl⟩ : syracuseStep 1306939 = 1960409) B1960409
theorem B3305843 : Blo 1305971 3305843 := bstep (se 1 (by rfl) ⟨2479382, by rfl⟩ : syracuseStep 3305843 = 4958765) B4958765
theorem B1569143 : Blo 1305971 1569143 := bstep (se 1 (by rfl) ⟨1176857, by rfl⟩ : syracuseStep 1569143 = 2353715) B2353715
theorem B6615431 : Blo 1305971 6615431 := bstep (se 1 (by rfl) ⟨4961573, by rfl⟩ : syracuseStep 6615431 = 9923147) B9923147
theorem B2093447 : Blo 1305971 2093447 := bstep (se 1 (by rfl) ⟨1570085, by rfl⟩ : syracuseStep 2093447 = 3140171) B3140171
theorem B1307015 : Blo 1305971 1307015 := bstep (se 1 (by rfl) ⟨980261, by rfl⟩ : syracuseStep 1307015 = 1960523) B1960523
theorem B10064263 : Blo 1305971 10064263 := bstep (se 1 (by rfl) ⟨7548197, by rfl⟩ : syracuseStep 10064263 = 15096395) B15096395
theorem B1307023 : Blo 1305971 1307023 := bstep (se 1 (by rfl) ⟨980267, by rfl⟩ : syracuseStep 1307023 = 1960535) B1960535
theorem B16740755 : Blo 1305971 16740755 := bstep (se 1 (by rfl) ⟨12555566, by rfl⟩ : syracuseStep 16740755 = 25111133) B25111133
theorem B1307067 : Blo 1305971 1307067 := bstep (se 1 (by rfl) ⟨980300, by rfl⟩ : syracuseStep 1307067 = 1960601) B1960601
theorem B1307143 : Blo 1305971 1307143 := bstep (se 1 (by rfl) ⟨980357, by rfl⟩ : syracuseStep 1307143 = 1960715) B1960715
theorem B1307151 : Blo 1305971 1307151 := bstep (se 1 (by rfl) ⟨980363, by rfl⟩ : syracuseStep 1307151 = 1960727) B1960727
theorem B1470991 : Blo 1305971 1470991 := bstep (se 1 (by rfl) ⟨1103243, by rfl⟩ : syracuseStep 1470991 = 2206487) B2206487
theorem B1675819 : Blo 1305971 1675819 := bstep (se 1 (by rfl) ⟨1256864, by rfl⟩ : syracuseStep 1675819 = 2513729) B2513729
theorem B1307195 : Blo 1305971 1307195 := bstep (se 1 (by rfl) ⟨980396, by rfl⟩ : syracuseStep 1307195 = 1960793) B1960793
theorem B1307271 : Blo 1305971 1307271 := bstep (se 1 (by rfl) ⟨980453, by rfl⟩ : syracuseStep 1307271 = 1960907) B1960907
theorem B1307279 : Blo 1305971 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B1569451 : Blo 1305971 1569451 := bstep (se 1 (by rfl) ⟨1177088, by rfl⟩ : syracuseStep 1569451 = 2354177) B2354177
theorem B14897843 : Blo 1305971 14897843 := bstep (se 1 (by rfl) ⟨11173382, by rfl⟩ : syracuseStep 14897843 = 22346765) B22346765
theorem B1307323 : Blo 1305971 1307323 := bstep (se 1 (by rfl) ⟨980492, by rfl⟩ : syracuseStep 1307323 = 1960985) B1960985
theorem B5583617 : Blo 1305971 5583617 := bstep (se 2 (by rfl) ⟨2093856, by rfl⟩ : syracuseStep 5583617 = 4187713) B4187713
theorem B1307399 : Blo 1305971 1307399 := bstep (se 1 (by rfl) ⟨980549, by rfl⟩ : syracuseStep 1307399 = 1961099) B1961099
theorem B1307407 : Blo 1305971 1307407 := bstep (se 1 (by rfl) ⟨980555, by rfl⟩ : syracuseStep 1307407 = 1961111) B1961111
theorem B34861859 : Blo 1305971 34861859 := bstep (se 1 (by rfl) ⟨26146394, by rfl⟩ : syracuseStep 34861859 = 52292789) B52292789
theorem B7443251 : Blo 1305971 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B1307451 : Blo 1305971 1307451 := bstep (se 1 (by rfl) ⟨980588, by rfl⟩ : syracuseStep 1307451 = 1961177) B1961177
theorem B11170649 : Blo 1305971 11170649 := bstep (se 2 (by rfl) ⟨4188993, by rfl⟩ : syracuseStep 11170649 = 8377987) B8377987
theorem B3306359 : Blo 1305971 3306359 := bstep (se 1 (by rfl) ⟨2479769, by rfl⟩ : syracuseStep 3306359 = 4959539) B4959539
theorem B2790263 : Blo 1305971 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B2093959 : Blo 1305971 2093959 := bstep (se 1 (by rfl) ⟨1570469, by rfl⟩ : syracuseStep 2093959 = 3140939) B3140939
theorem B1307527 : Blo 1305971 1307527 := bstep (se 1 (by rfl) ⟨980645, by rfl⟩ : syracuseStep 1307527 = 1961291) B1961291
theorem B1307535 : Blo 1305971 1307535 := bstep (se 1 (by rfl) ⟨980651, by rfl⟩ : syracuseStep 1307535 = 1961303) B1961303
theorem B13415321 : Blo 1305971 13415321 := bstep (se 2 (by rfl) ⟨5030745, by rfl⟩ : syracuseStep 13415321 = 10061491) B10061491
theorem B4961209 : Blo 1305971 4961209 := bstep (se 2 (by rfl) ⟨1860453, by rfl⟩ : syracuseStep 4961209 = 3720907) B3720907
theorem B1307579 : Blo 1305971 1307579 := bstep (se 1 (by rfl) ⟨980684, by rfl⟩ : syracuseStep 1307579 = 1961369) B1961369
theorem B1307655 : Blo 1305971 1307655 := bstep (se 1 (by rfl) ⟨980741, by rfl⟩ : syracuseStep 1307655 = 1961483) B1961483
theorem B1307663 : Blo 1305971 1307663 := bstep (se 1 (by rfl) ⟨980747, by rfl⟩ : syracuseStep 1307663 = 1961495) B1961495
theorem B1307707 : Blo 1305971 1307707 := bstep (se 1 (by rfl) ⟨980780, by rfl⟩ : syracuseStep 1307707 = 1961561) B1961561
theorem B1307783 : Blo 1305971 1307783 := bstep (se 1 (by rfl) ⟨980837, by rfl⟩ : syracuseStep 1307783 = 1961675) B1961675
theorem B1307791 : Blo 1305971 1307791 := bstep (se 1 (by rfl) ⟨980843, by rfl⟩ : syracuseStep 1307791 = 1961687) B1961687
theorem B6362285 : Blo 1305971 6362285 := bstep (se 3 (by rfl) ⟨1192928, by rfl⟩ : syracuseStep 6362285 = 2385857) B2385857
theorem B1307835 : Blo 1305971 1307835 := bstep (se 1 (by rfl) ⟨980876, by rfl⟩ : syracuseStep 1307835 = 1961753) B1961753
theorem B1307911 : Blo 1305971 1307911 := bstep (se 1 (by rfl) ⟨980933, by rfl⟩ : syracuseStep 1307911 = 1961867) B1961867
theorem B1307919 : Blo 1305971 1307919 := bstep (se 1 (by rfl) ⟨980939, by rfl⟩ : syracuseStep 1307919 = 1961879) B1961879
theorem B2790715 : Blo 1305971 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B1307963 : Blo 1305971 1307963 := bstep (se 1 (by rfl) ⟨980972, by rfl⟩ : syracuseStep 1307963 = 1961945) B1961945
theorem B4707719 : Blo 1305971 4707719 := bstep (se 1 (by rfl) ⟨3530789, by rfl⟩ : syracuseStep 4707719 = 7061579) B7061579
theorem B2356627 : Blo 1305971 2356627 := bstep (se 1 (by rfl) ⟨1767470, by rfl⟩ : syracuseStep 2356627 = 3534941) B3534941
theorem B4412825 : Blo 1305971 4412825 := bstep (se 2 (by rfl) ⟨1654809, by rfl⟩ : syracuseStep 4412825 = 3309619) B3309619
theorem B5658065 : Blo 1305971 5658065 := bstep (se 2 (by rfl) ⟨2121774, by rfl⟩ : syracuseStep 5658065 = 4243549) B4243549
theorem B15906257 : Blo 1305971 15906257 := bstep (se 2 (by rfl) ⟨5964846, by rfl⟩ : syracuseStep 15906257 = 11929693) B11929693
theorem B7067197 : Blo 1305971 7067197 := bstep (se 3 (by rfl) ⟨1325099, by rfl⟩ : syracuseStep 7067197 = 2650199) B2650199
theorem B6280877 : Blo 1305971 6280877 := bstep (se 3 (by rfl) ⟨1177664, by rfl⟩ : syracuseStep 6280877 = 2355329) B2355329
theorem B2938553 : Blo 1305971 2938553 := bstep (se 2 (by rfl) ⟨1101957, by rfl⟩ : syracuseStep 2938553 = 2203915) B2203915
theorem B2094907 : Blo 1305971 2094907 := bstep (se 1 (by rfl) ⟨1571180, by rfl⟩ : syracuseStep 2094907 = 3142361) B3142361
theorem B14137163 : Blo 1305971 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B3307351 : Blo 1305971 3307351 := bstep (se 1 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 3307351 = 4961027) B4961027
theorem B9426851 : Blo 1305971 9426851 := bstep (se 1 (by rfl) ⟨7070138, by rfl⟩ : syracuseStep 9426851 = 14140277) B14140277
theorem B2938895 : Blo 1305971 2938895 := bstep (se 1 (by rfl) ⟨2204171, by rfl⟩ : syracuseStep 2938895 = 4408343) B4408343
theorem B2938913 : Blo 1305971 2938913 := bstep (se 2 (by rfl) ⟨1102092, by rfl⟩ : syracuseStep 2938913 = 2204185) B2204185
theorem B4413527 : Blo 1305971 4413527 := bstep (se 1 (by rfl) ⟨3310145, by rfl⟩ : syracuseStep 4413527 = 6620291) B6620291
theorem B3307655 : Blo 1305971 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B7444709 : Blo 1305971 7444709 := bstep (se 4 (by rfl) ⟨697941, by rfl⟩ : syracuseStep 7444709 = 1395883) B1395883
theorem B3307787 : Blo 1305971 3307787 := bstep (se 1 (by rfl) ⟨2480840, by rfl⟩ : syracuseStep 3307787 = 4961681) B4961681
theorem B7354657 : Blo 1305971 7354657 := bstep (se 2 (by rfl) ⟨2757996, by rfl⟩ : syracuseStep 7354657 = 5515993) B5515993
theorem B2939255 : Blo 1305971 2939255 := bstep (se 1 (by rfl) ⟨2204441, by rfl⟩ : syracuseStep 2939255 = 4408883) B4408883
theorem B2939435 : Blo 1305971 2939435 := bstep (se 1 (by rfl) ⟨2204576, by rfl⟩ : syracuseStep 2939435 = 4409153) B4409153
theorem B4414013 : Blo 1305971 4414013 := bstep (se 3 (by rfl) ⟨827627, by rfl⟩ : syracuseStep 4414013 = 1655255) B1655255
theorem B1653367 : Blo 1305971 1653367 := bstep (se 1 (by rfl) ⟨1240025, by rfl⟩ : syracuseStep 1653367 = 2480051) B2480051
theorem B3308303 : Blo 1305971 3308303 := bstep (se 1 (by rfl) ⟨2481227, by rfl⟩ : syracuseStep 3308303 = 4962455) B4962455
theorem B2480939 : Blo 1305971 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B2939795 : Blo 1305971 2939795 := bstep (se 1 (by rfl) ⟨2204846, by rfl⟩ : syracuseStep 2939795 = 4409693) B4409693
theorem B3308435 : Blo 1305971 3308435 := bstep (se 1 (by rfl) ⟨2481326, by rfl⟩ : syracuseStep 3308435 = 4962653) B4962653
theorem B14130071 : Blo 1305971 14130071 := bstep (se 1 (by rfl) ⟨10597553, by rfl⟩ : syracuseStep 14130071 = 21195107) B21195107
theorem B26835893 : Blo 1305971 26835893 := bstep (se 5 (by rfl) ⟨1257932, by rfl⟩ : syracuseStep 26835893 = 2515865) B2515865
theorem B1653691 : Blo 1305971 1653691 := bstep (se 1 (by rfl) ⟨1240268, by rfl⟩ : syracuseStep 1653691 = 2480537) B2480537
theorem B2939849 : Blo 1305971 2939849 := bstep (se 2 (by rfl) ⟨1102443, by rfl⟩ : syracuseStep 2939849 = 2204887) B2204887
theorem B2481167 : Blo 1305971 2481167 := bstep (se 1 (by rfl) ⟨1860875, by rfl⟩ : syracuseStep 2481167 = 3721751) B3721751
theorem B7167005 : Blo 1305971 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B2235451 : Blo 1305971 2235451 := bstep (se 1 (by rfl) ⟨1676588, by rfl⟩ : syracuseStep 2235451 = 3353177) B3353177
theorem B3226913 : Blo 1305971 3226913 := bstep (se 2 (by rfl) ⟨1210092, by rfl⟩ : syracuseStep 3226913 = 2420185) B2420185
theorem B11926919 : Blo 1305971 11926919 := bstep (se 1 (by rfl) ⟨8945189, by rfl⟩ : syracuseStep 11926919 = 17890379) B17890379
theorem B4185611 : Blo 1305971 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B10886699 : Blo 1305971 10886699 := bstep (se 1 (by rfl) ⟨8165024, by rfl⟩ : syracuseStep 10886699 = 16330049) B16330049
theorem B2940551 : Blo 1305971 2940551 := bstep (se 1 (by rfl) ⟨2205413, by rfl⟩ : syracuseStep 2940551 = 4410827) B4410827
theorem B4964111 : Blo 1305971 4964111 := bstep (se 1 (by rfl) ⟨3723083, by rfl⟩ : syracuseStep 4964111 = 7446167) B7446167
theorem B2940731 : Blo 1305971 2940731 := bstep (se 1 (by rfl) ⟨2205548, by rfl⟩ : syracuseStep 2940731 = 4411097) B4411097
theorem B7438169 : Blo 1305971 7438169 := bstep (se 2 (by rfl) ⟨2789313, by rfl⟩ : syracuseStep 7438169 = 5578627) B5578627
theorem B6618995 : Blo 1305971 6618995 := bstep (se 1 (by rfl) ⟨4964246, by rfl⟩ : syracuseStep 6618995 = 9928493) B9928493
theorem B1654663 : Blo 1305971 1654663 := bstep (se 1 (by rfl) ⟨1240997, by rfl⟩ : syracuseStep 1654663 = 2481995) B2481995
theorem B4186009 : Blo 1305971 4186009 := bstep (se 2 (by rfl) ⟨1569753, by rfl⟩ : syracuseStep 4186009 = 3139507) B3139507
theorem B2940857 : Blo 1305971 2940857 := bstep (se 2 (by rfl) ⟨1102821, by rfl⟩ : syracuseStep 2940857 = 2205643) B2205643
theorem B7438351 : Blo 1305971 7438351 := bstep (se 1 (by rfl) ⟨5578763, by rfl⟩ : syracuseStep 7438351 = 11157527) B11157527
theorem B2940947 : Blo 1305971 2940947 := bstep (se 1 (by rfl) ⟨2205710, by rfl⟩ : syracuseStep 2940947 = 4411421) B4411421
theorem B8937701 : Blo 1305971 8937701 := bstep (se 4 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 8937701 = 1675819) B1675819
theorem B2203895 : Blo 1305971 2203895 := bstep (se 1 (by rfl) ⟨1652921, by rfl⟩ : syracuseStep 2203895 = 3305843) B3305843
theorem B2941289 : Blo 1305971 2941289 := bstep (se 2 (by rfl) ⟨1102983, by rfl⟩ : syracuseStep 2941289 = 2205967) B2205967
theorem B4407695 : Blo 1305971 4407695 := bstep (se 1 (by rfl) ⟨3305771, by rfl⟩ : syracuseStep 4407695 = 6611543) B6611543
theorem B16966093 : Blo 1305971 16966093 := bstep (se 3 (by rfl) ⟨3181142, by rfl⟩ : syracuseStep 16966093 = 6362285) B6362285
theorem B13419017 : Blo 1305971 13419017 := bstep (se 2 (by rfl) ⟨5032131, by rfl⟩ : syracuseStep 13419017 = 10064263) B10064263
theorem B23241239 : Blo 1305971 23241239 := bstep (se 1 (by rfl) ⟨17430929, by rfl⟩ : syracuseStep 23241239 = 34861859) B34861859
theorem B3310105 : Blo 1305971 3310105 := bstep (se 2 (by rfl) ⟨1241289, by rfl⟩ : syracuseStep 3310105 = 2482579) B2482579
theorem B7447099 : Blo 1305971 7447099 := bstep (se 1 (by rfl) ⟨5585324, by rfl⟩ : syracuseStep 7447099 = 11170649) B11170649
theorem B2204239 : Blo 1305971 2204239 := bstep (se 1 (by rfl) ⟨1653179, by rfl⟩ : syracuseStep 2204239 = 3306359) B3306359
theorem B1860175 : Blo 1305971 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B3719803 : Blo 1305971 3719803 := bstep (se 1 (by rfl) ⟨2789852, by rfl⟩ : syracuseStep 3719803 = 5579705) B5579705
theorem B4711121 : Blo 1305971 4711121 := bstep (se 2 (by rfl) ⟨1766670, by rfl⟩ : syracuseStep 4711121 = 3533341) B3533341
theorem B4408019 : Blo 1305971 4408019 := bstep (se 1 (by rfl) ⟨3306014, by rfl⟩ : syracuseStep 4408019 = 6612029) B6612029
theorem B7062227 : Blo 1305971 7062227 := bstep (se 1 (by rfl) ⟨5296670, by rfl⟩ : syracuseStep 7062227 = 10593341) B10593341
theorem B2204489 : Blo 1305971 2204489 := bstep (se 2 (by rfl) ⟨826683, by rfl⟩ : syracuseStep 2204489 = 1653367) B1653367
theorem B3310409 : Blo 1305971 3310409 := bstep (se 2 (by rfl) ⟨1241403, by rfl⟩ : syracuseStep 3310409 = 2482807) B2482807
theorem B3138479 : Blo 1305971 3138479 := bstep (se 1 (by rfl) ⟨2353859, by rfl⟩ : syracuseStep 3138479 = 4707719) B4707719
theorem B2941883 : Blo 1305971 2941883 := bstep (se 1 (by rfl) ⟨2206412, by rfl⟩ : syracuseStep 2941883 = 4412825) B4412825
theorem B124126253 : Blo 1305971 124126253 := bstep (se 3 (by rfl) ⟨23273672, by rfl⟩ : syracuseStep 124126253 = 46547345) B46547345
theorem B2942009 : Blo 1305971 2942009 := bstep (se 2 (by rfl) ⟨1103253, by rfl⟩ : syracuseStep 2942009 = 2206507) B2206507
theorem B4187251 : Blo 1305971 4187251 := bstep (se 1 (by rfl) ⟨3140438, by rfl⟩ : syracuseStep 4187251 = 6280877) B6280877
theorem B1959035 : Blo 1305971 1959035 := bstep (se 1 (by rfl) ⟨1469276, by rfl⟩ : syracuseStep 1959035 = 2938553) B2938553
theorem B9921689 : Blo 1305971 9921689 := bstep (se 2 (by rfl) ⟨3720633, by rfl⟩ : syracuseStep 9921689 = 7441267) B7441267
theorem B1959161 : Blo 1305971 1959161 := bstep (se 2 (by rfl) ⟨734685, by rfl⟩ : syracuseStep 1959161 = 1469371) B1469371
theorem B2204921 : Blo 1305971 2204921 := bstep (se 2 (by rfl) ⟨826845, by rfl⟩ : syracuseStep 2204921 = 1653691) B1653691
theorem B6284567 : Blo 1305971 6284567 := bstep (se 1 (by rfl) ⟨4713425, by rfl⟩ : syracuseStep 6284567 = 9426851) B9426851
theorem B1959263 : Blo 1305971 1959263 := bstep (se 1 (by rfl) ⟨1469447, by rfl⟩ : syracuseStep 1959263 = 2938895) B2938895
theorem B1959275 : Blo 1305971 1959275 := bstep (se 1 (by rfl) ⟨1469456, by rfl⟩ : syracuseStep 1959275 = 2938913) B2938913
theorem B2942351 : Blo 1305971 2942351 := bstep (se 1 (by rfl) ⟨2206763, by rfl⟩ : syracuseStep 2942351 = 4413527) B4413527
theorem B2205103 : Blo 1305971 2205103 := bstep (se 1 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 2205103 = 3307655) B3307655
theorem B39224837 : Blo 1305971 39224837 := bstep (se 4 (by rfl) ⟨3677328, by rfl⟩ : syracuseStep 39224837 = 7354657) B7354657
theorem B2205191 : Blo 1305971 2205191 := bstep (se 1 (by rfl) ⟨1653893, by rfl⟩ : syracuseStep 2205191 = 3307787) B3307787
theorem B2516537 : Blo 1305971 2516537 := bstep (se 2 (by rfl) ⟨943701, by rfl⟩ : syracuseStep 2516537 = 1887403) B1887403
theorem B1959503 : Blo 1305971 1959503 := bstep (se 1 (by rfl) ⟨1469627, by rfl⟩ : syracuseStep 1959503 = 2939255) B2939255
theorem B1959623 : Blo 1305971 1959623 := bstep (se 1 (by rfl) ⟨1469717, by rfl⟩ : syracuseStep 1959623 = 2939435) B2939435
theorem B21202631 : Blo 1305971 21202631 := bstep (se 1 (by rfl) ⟨15901973, by rfl⟩ : syracuseStep 21202631 = 31803947) B31803947
theorem B2942675 : Blo 1305971 2942675 := bstep (se 1 (by rfl) ⟨2207006, by rfl⟩ : syracuseStep 2942675 = 4414013) B4414013
theorem B3720953 : Blo 1305971 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B12732203 : Blo 1305971 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B2205535 : Blo 1305971 2205535 := bstep (se 1 (by rfl) ⟨1654151, by rfl⟩ : syracuseStep 2205535 = 3308303) B3308303
theorem B2385769 : Blo 1305971 2385769 := bstep (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) B1789327
theorem B1959785 : Blo 1305971 1959785 := bstep (se 2 (by rfl) ⟨734919, by rfl⟩ : syracuseStep 1959785 = 1469839) B1469839
theorem B4409207 : Blo 1305971 4409207 := bstep (se 1 (by rfl) ⟨3306905, by rfl⟩ : syracuseStep 4409207 = 6613811) B6613811
theorem B3721135 : Blo 1305971 3721135 := bstep (se 1 (by rfl) ⟨2790851, by rfl⟩ : syracuseStep 3721135 = 5581703) B5581703
theorem B1959863 : Blo 1305971 1959863 := bstep (se 1 (by rfl) ⟨1469897, by rfl⟩ : syracuseStep 1959863 = 2939795) B2939795
theorem B2205623 : Blo 1305971 2205623 := bstep (se 1 (by rfl) ⟨1654217, by rfl⟩ : syracuseStep 2205623 = 3308435) B3308435
theorem B1959899 : Blo 1305971 1959899 := bstep (se 1 (by rfl) ⟨1469924, by rfl⟩ : syracuseStep 1959899 = 2939849) B2939849
theorem B4778003 : Blo 1305971 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B4409423 : Blo 1305971 4409423 := bstep (se 1 (by rfl) ⟨3307067, by rfl⟩ : syracuseStep 4409423 = 6614135) B6614135
theorem B3721295 : Blo 1305971 3721295 := bstep (se 1 (by rfl) ⟨2790971, by rfl⟩ : syracuseStep 3721295 = 5581943) B5581943
theorem B9422929 : Blo 1305971 9422929 := bstep (se 2 (by rfl) ⟨3533598, by rfl⟩ : syracuseStep 9422929 = 7067197) B7067197
theorem B1960367 : Blo 1305971 1960367 := bstep (se 1 (by rfl) ⟨1470275, by rfl⟩ : syracuseStep 1960367 = 2940551) B2940551
theorem B4409801 : Blo 1305971 4409801 := bstep (se 2 (by rfl) ⟨1653675, by rfl⟩ : syracuseStep 4409801 = 3307351) B3307351
theorem B1960457 : Blo 1305971 1960457 := bstep (se 2 (by rfl) ⟨735171, by rfl⟩ : syracuseStep 1960457 = 1470343) B1470343
theorem B2206217 : Blo 1305971 2206217 := bstep (se 2 (by rfl) ⟨827331, by rfl⟩ : syracuseStep 2206217 = 1654663) B1654663
theorem B5581345 : Blo 1305971 5581345 := bstep (se 2 (by rfl) ⟨2093004, by rfl⟩ : syracuseStep 5581345 = 4186009) B4186009
theorem B1960487 : Blo 1305971 1960487 := bstep (se 1 (by rfl) ⟨1470365, by rfl⟩ : syracuseStep 1960487 = 2940731) B2940731
theorem B4958779 : Blo 1305971 4958779 := bstep (se 1 (by rfl) ⟨3719084, by rfl⟩ : syracuseStep 4958779 = 7438169) B7438169
theorem B1960571 : Blo 1305971 1960571 := bstep (se 1 (by rfl) ⟨1470428, by rfl⟩ : syracuseStep 1960571 = 2940857) B2940857
theorem B5032595 : Blo 1305971 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B2206379 : Blo 1305971 2206379 := bstep (se 1 (by rfl) ⟨1654784, by rfl⟩ : syracuseStep 2206379 = 3309569) B3309569
theorem B4410071 : Blo 1305971 4410071 := bstep (se 1 (by rfl) ⟨3307553, by rfl⟩ : syracuseStep 4410071 = 6615107) B6615107
theorem B1960697 : Blo 1305971 1960697 := bstep (se 2 (by rfl) ⟨735261, by rfl⟩ : syracuseStep 1960697 = 1470523) B1470523
theorem B1960799 : Blo 1305971 1960799 := bstep (se 1 (by rfl) ⟨1470599, by rfl⟩ : syracuseStep 1960799 = 2941199) B2941199
theorem B4959083 : Blo 1305971 4959083 := bstep (se 1 (by rfl) ⟨3719312, by rfl⟩ : syracuseStep 4959083 = 7438625) B7438625
theorem B1960811 : Blo 1305971 1960811 := bstep (se 1 (by rfl) ⟨1470608, by rfl⟩ : syracuseStep 1960811 = 2941217) B2941217
theorem B4410287 : Blo 1305971 4410287 := bstep (se 1 (by rfl) ⟨3307715, by rfl⟩ : syracuseStep 4410287 = 6615431) B6615431
theorem B1395631 : Blo 1305971 1395631 := bstep (se 1 (by rfl) ⟨1046723, by rfl⟩ : syracuseStep 1395631 = 2093447) B2093447
theorem B11160503 : Blo 1305971 11160503 := bstep (se 1 (by rfl) ⟨8370377, by rfl⟩ : syracuseStep 11160503 = 16740755) B16740755
theorem B4959251 : Blo 1305971 4959251 := bstep (se 1 (by rfl) ⟨3719438, by rfl⟩ : syracuseStep 4959251 = 7438877) B7438877
theorem B1469479 : Blo 1305971 1469479 := bstep (se 1 (by rfl) ⟨1102109, by rfl⟩ : syracuseStep 1469479 = 2204219) B2204219
theorem B9923633 : Blo 1305971 9923633 := bstep (se 2 (by rfl) ⟨3721362, by rfl⟩ : syracuseStep 9923633 = 7442725) B7442725
theorem B3533881 : Blo 1305971 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B2206777 : Blo 1305971 2206777 := bstep (se 2 (by rfl) ⟨827541, by rfl⟩ : syracuseStep 2206777 = 1655083) B1655083
theorem B1961039 : Blo 1305971 1961039 := bstep (se 1 (by rfl) ⟨1470779, by rfl⟩ : syracuseStep 1961039 = 2941559) B2941559
theorem B9931895 : Blo 1305971 9931895 := bstep (se 1 (by rfl) ⟨7448921, by rfl⟩ : syracuseStep 9931895 = 14897843) B14897843
theorem B3353771 : Blo 1305971 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B3722411 : Blo 1305971 3722411 := bstep (se 1 (by rfl) ⟨2791808, by rfl⟩ : syracuseStep 3722411 = 5583617) B5583617
theorem B1961159 : Blo 1305971 1961159 := bstep (se 1 (by rfl) ⟨1470869, by rfl⟩ : syracuseStep 1961159 = 2941739) B2941739
theorem B2206919 : Blo 1305971 2206919 := bstep (se 1 (by rfl) ⟨1655189, by rfl⟩ : syracuseStep 2206919 = 3310379) B3310379
theorem B1961321 : Blo 1305971 1961321 := bstep (se 2 (by rfl) ⟨735495, by rfl⟩ : syracuseStep 1961321 = 1470991) B1470991
theorem B3976553 : Blo 1305971 3976553 := bstep (se 2 (by rfl) ⟨1491207, by rfl⟩ : syracuseStep 3976553 = 2982415) B2982415
theorem B2207081 : Blo 1305971 2207081 := bstep (se 2 (by rfl) ⟨827655, by rfl⟩ : syracuseStep 2207081 = 1655311) B1655311
theorem B1305979 : Blo 1305971 1305979 := bstep (se 1 (by rfl) ⟨979484, by rfl⟩ : syracuseStep 1305979 = 1958969) B1958969
theorem B1306031 : Blo 1305971 1306031 := bstep (se 1 (by rfl) ⟨979523, by rfl⟩ : syracuseStep 1306031 = 1959047) B1959047
theorem B1961399 : Blo 1305971 1961399 := bstep (se 1 (by rfl) ⟨1471049, by rfl⟩ : syracuseStep 1961399 = 2942099) B2942099
theorem B1306055 : Blo 1305971 1306055 := bstep (se 1 (by rfl) ⟨979541, by rfl⟩ : syracuseStep 1306055 = 1959083) B1959083
theorem B1306075 : Blo 1305971 1306075 := bstep (se 1 (by rfl) ⟨979556, by rfl⟩ : syracuseStep 1306075 = 1959113) B1959113
theorem B1961435 : Blo 1305971 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B4713947 : Blo 1305971 4713947 := bstep (se 1 (by rfl) ⟨3535460, by rfl⟩ : syracuseStep 4713947 = 7070921) B7070921
theorem B1306151 : Blo 1305971 1306151 := bstep (se 1 (by rfl) ⟨979613, by rfl⟩ : syracuseStep 1306151 = 1959227) B1959227
theorem B2092601 : Blo 1305971 2092601 := bstep (se 2 (by rfl) ⟨784725, by rfl⟩ : syracuseStep 2092601 = 1569451) B1569451
theorem B1306191 : Blo 1305971 1306191 := bstep (se 1 (by rfl) ⟨979643, by rfl⟩ : syracuseStep 1306191 = 1959287) B1959287
theorem B1306207 : Blo 1305971 1306207 := bstep (se 1 (by rfl) ⟨979655, by rfl⟩ : syracuseStep 1306207 = 1959311) B1959311
theorem B1306235 : Blo 1305971 1306235 := bstep (se 1 (by rfl) ⟨979676, by rfl⟩ : syracuseStep 1306235 = 1959353) B1959353
theorem B3772043 : Blo 1305971 3772043 := bstep (se 1 (by rfl) ⟨2829032, by rfl⟩ : syracuseStep 3772043 = 5658065) B5658065
theorem B10604171 : Blo 1305971 10604171 := bstep (se 1 (by rfl) ⟨7953128, by rfl⟩ : syracuseStep 10604171 = 15906257) B15906257
theorem B1306287 : Blo 1305971 1306287 := bstep (se 1 (by rfl) ⟨979715, by rfl⟩ : syracuseStep 1306287 = 1959431) B1959431
theorem B1306311 : Blo 1305971 1306311 := bstep (se 1 (by rfl) ⟨979733, by rfl⟩ : syracuseStep 1306311 = 1959467) B1959467
theorem B1306331 : Blo 1305971 1306331 := bstep (se 1 (by rfl) ⟨979748, by rfl⟩ : syracuseStep 1306331 = 1959497) B1959497
theorem B1306407 : Blo 1305971 1306407 := bstep (se 1 (by rfl) ⟨979805, by rfl⟩ : syracuseStep 1306407 = 1959611) B1959611
theorem B1306447 : Blo 1305971 1306447 := bstep (se 1 (by rfl) ⟨979835, by rfl⟩ : syracuseStep 1306447 = 1959671) B1959671
theorem B1306463 : Blo 1305971 1306463 := bstep (se 1 (by rfl) ⟨979847, by rfl⟩ : syracuseStep 1306463 = 1959695) B1959695
theorem B1306491 : Blo 1305971 1306491 := bstep (se 1 (by rfl) ⟨979868, by rfl⟩ : syracuseStep 1306491 = 1959737) B1959737
theorem B9424775 : Blo 1305971 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B6614945 : Blo 1305971 6614945 := bstep (se 2 (by rfl) ⟨2480604, by rfl⟩ : syracuseStep 6614945 = 4961209) B4961209
theorem B1306543 : Blo 1305971 1306543 := bstep (se 1 (by rfl) ⟨979907, by rfl⟩ : syracuseStep 1306543 = 1959815) B1959815
theorem B1961903 : Blo 1305971 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B1306567 : Blo 1305971 1306567 := bstep (se 1 (by rfl) ⟨979925, by rfl⟩ : syracuseStep 1306567 = 1959851) B1959851
theorem B1306587 : Blo 1305971 1306587 := bstep (se 1 (by rfl) ⟨979940, by rfl⟩ : syracuseStep 1306587 = 1959881) B1959881
theorem B25112591 : Blo 1305971 25112591 := bstep (se 1 (by rfl) ⟨18834443, by rfl⟩ : syracuseStep 25112591 = 37668887) B37668887
theorem B1306663 : Blo 1305971 1306663 := bstep (se 1 (by rfl) ⟨979997, by rfl⟩ : syracuseStep 1306663 = 1959995) B1959995
theorem B1306703 : Blo 1305971 1306703 := bstep (se 1 (by rfl) ⟨980027, by rfl⟩ : syracuseStep 1306703 = 1960055) B1960055
theorem B1306719 : Blo 1305971 1306719 := bstep (se 1 (by rfl) ⟨980039, by rfl⟩ : syracuseStep 1306719 = 1960079) B1960079
theorem B1306747 : Blo 1305971 1306747 := bstep (se 1 (by rfl) ⟨980060, by rfl⟩ : syracuseStep 1306747 = 1960121) B1960121
theorem B1306799 : Blo 1305971 1306799 := bstep (se 1 (by rfl) ⟨980099, by rfl⟩ : syracuseStep 1306799 = 1960199) B1960199
theorem B1306823 : Blo 1305971 1306823 := bstep (se 1 (by rfl) ⟨980117, by rfl⟩ : syracuseStep 1306823 = 1960235) B1960235
theorem B1306843 : Blo 1305971 1306843 := bstep (se 1 (by rfl) ⟨980132, by rfl⟩ : syracuseStep 1306843 = 1960265) B1960265
theorem B1306919 : Blo 1305971 1306919 := bstep (se 1 (by rfl) ⟨980189, by rfl⟩ : syracuseStep 1306919 = 1960379) B1960379
theorem B1306959 : Blo 1305971 1306959 := bstep (se 1 (by rfl) ⟨980219, by rfl⟩ : syracuseStep 1306959 = 1960439) B1960439
theorem B1306975 : Blo 1305971 1306975 := bstep (se 1 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 1306975 = 1960463) B1960463
theorem B1307003 : Blo 1305971 1307003 := bstep (se 1 (by rfl) ⟨980252, by rfl⟩ : syracuseStep 1307003 = 1960505) B1960505
theorem B1307055 : Blo 1305971 1307055 := bstep (se 1 (by rfl) ⟨980291, by rfl⟩ : syracuseStep 1307055 = 1960583) B1960583
theorem B1307079 : Blo 1305971 1307079 := bstep (se 1 (by rfl) ⟨980309, by rfl⟩ : syracuseStep 1307079 = 1960619) B1960619
theorem B1307099 : Blo 1305971 1307099 := bstep (se 1 (by rfl) ⟨980324, by rfl⟩ : syracuseStep 1307099 = 1960649) B1960649
theorem B3355145 : Blo 1305971 3355145 := bstep (se 2 (by rfl) ⟨1258179, by rfl⟩ : syracuseStep 3355145 = 2516359) B2516359
theorem B3142169 : Blo 1305971 3142169 := bstep (se 2 (by rfl) ⟨1178313, by rfl⟩ : syracuseStep 3142169 = 2356627) B2356627
theorem B1307175 : Blo 1305971 1307175 := bstep (se 1 (by rfl) ⟨980381, by rfl⟩ : syracuseStep 1307175 = 1960763) B1960763
theorem B1307215 : Blo 1305971 1307215 := bstep (se 1 (by rfl) ⟨980411, by rfl⟩ : syracuseStep 1307215 = 1960823) B1960823
theorem B1307231 : Blo 1305971 1307231 := bstep (se 1 (by rfl) ⟨980423, by rfl⟩ : syracuseStep 1307231 = 1960847) B1960847
theorem B1307259 : Blo 1305971 1307259 := bstep (se 1 (by rfl) ⟨980444, by rfl⟩ : syracuseStep 1307259 = 1960889) B1960889
theorem B1471099 : Blo 1305971 1471099 := bstep (se 1 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 1471099 = 2206649) B2206649
theorem B1307311 : Blo 1305971 1307311 := bstep (se 1 (by rfl) ⟨980483, by rfl⟩ : syracuseStep 1307311 = 1960967) B1960967
theorem B1307335 : Blo 1305971 1307335 := bstep (se 1 (by rfl) ⟨980501, by rfl⟩ : syracuseStep 1307335 = 1961003) B1961003
theorem B1307355 : Blo 1305971 1307355 := bstep (se 1 (by rfl) ⟨980516, by rfl⟩ : syracuseStep 1307355 = 1961033) B1961033
theorem B1307431 : Blo 1305971 1307431 := bstep (se 1 (by rfl) ⟨980573, by rfl⟩ : syracuseStep 1307431 = 1961147) B1961147
theorem B1307471 : Blo 1305971 1307471 := bstep (se 1 (by rfl) ⟨980603, by rfl⟩ : syracuseStep 1307471 = 1961207) B1961207
theorem B1307487 : Blo 1305971 1307487 := bstep (se 1 (by rfl) ⟨980615, by rfl⟩ : syracuseStep 1307487 = 1961231) B1961231
theorem B1307515 : Blo 1305971 1307515 := bstep (se 1 (by rfl) ⟨980636, by rfl⟩ : syracuseStep 1307515 = 1961273) B1961273
theorem B2790305 : Blo 1305971 2790305 := bstep (se 2 (by rfl) ⟨1046364, by rfl⟩ : syracuseStep 2790305 = 2092729) B2092729
theorem B7951279 : Blo 1305971 7951279 := bstep (se 1 (by rfl) ⟨5963459, by rfl⟩ : syracuseStep 7951279 = 11926919) B11926919
theorem B1307567 : Blo 1305971 1307567 := bstep (se 1 (by rfl) ⟨980675, by rfl⟩ : syracuseStep 1307567 = 1961351) B1961351
theorem B1307591 : Blo 1305971 1307591 := bstep (se 1 (by rfl) ⟨980693, by rfl⟩ : syracuseStep 1307591 = 1961387) B1961387
theorem B1307611 : Blo 1305971 1307611 := bstep (se 1 (by rfl) ⟨980708, by rfl⟩ : syracuseStep 1307611 = 1961417) B1961417
theorem B2790407 : Blo 1305971 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B1307687 : Blo 1305971 1307687 := bstep (se 1 (by rfl) ⟨980765, by rfl⟩ : syracuseStep 1307687 = 1961531) B1961531
theorem B13407281 : Blo 1305971 13407281 := bstep (se 2 (by rfl) ⟨5027730, by rfl⟩ : syracuseStep 13407281 = 10055461) B10055461
theorem B1307727 : Blo 1305971 1307727 := bstep (se 1 (by rfl) ⟨980795, by rfl⟩ : syracuseStep 1307727 = 1961591) B1961591
theorem B1324127 : Blo 1305971 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B1307743 : Blo 1305971 1307743 := bstep (se 1 (by rfl) ⟨980807, by rfl⟩ : syracuseStep 1307743 = 1961615) B1961615
theorem B1307771 : Blo 1305971 1307771 := bstep (se 1 (by rfl) ⟨980828, by rfl⟩ : syracuseStep 1307771 = 1961657) B1961657
theorem B1307823 : Blo 1305971 1307823 := bstep (se 1 (by rfl) ⟨980867, by rfl⟩ : syracuseStep 1307823 = 1961735) B1961735
theorem B1307847 : Blo 1305971 1307847 := bstep (se 1 (by rfl) ⟨980885, by rfl⟩ : syracuseStep 1307847 = 1961771) B1961771
theorem B1307867 : Blo 1305971 1307867 := bstep (se 1 (by rfl) ⟨980900, by rfl⟩ : syracuseStep 1307867 = 1961801) B1961801
theorem B4412663 : Blo 1305971 4412663 := bstep (se 1 (by rfl) ⟨3309497, by rfl⟩ : syracuseStep 4412663 = 6618995) B6618995
theorem B10597655 : Blo 1305971 10597655 := bstep (se 1 (by rfl) ⟨7948241, by rfl⟩ : syracuseStep 10597655 = 15896483) B15896483
theorem B1307943 : Blo 1305971 1307943 := bstep (se 1 (by rfl) ⟨980957, by rfl⟩ : syracuseStep 1307943 = 1961915) B1961915
theorem B8369581 : Blo 1305971 8369581 := bstep (se 3 (by rfl) ⟨1569296, by rfl⟩ : syracuseStep 8369581 = 3138593) B3138593
theorem B2356655 : Blo 1305971 2356655 := bstep (se 1 (by rfl) ⟨1767491, by rfl⟩ : syracuseStep 2356655 = 3534983) B3534983
theorem B4412987 : Blo 1305971 4412987 := bstep (se 1 (by rfl) ⟨3309740, by rfl⟩ : syracuseStep 4412987 = 6619481) B6619481
theorem B34420405 : Blo 1305971 34420405 := bstep (se 5 (by rfl) ⟨1613456, by rfl⟩ : syracuseStep 34420405 = 3226913) B3226913
theorem B7444183 : Blo 1305971 7444183 := bstep (se 1 (by rfl) ⟨5583137, by rfl⟩ : syracuseStep 7444183 = 11166275) B11166275
theorem B7067351 : Blo 1305971 7067351 := bstep (se 1 (by rfl) ⟨5300513, by rfl⟩ : syracuseStep 7067351 = 10601027) B10601027
theorem B2938697 : Blo 1305971 2938697 := bstep (se 2 (by rfl) ⟨1102011, by rfl⟩ : syracuseStep 2938697 = 2204023) B2204023
theorem B4413257 : Blo 1305971 4413257 := bstep (se 2 (by rfl) ⟨1654971, by rfl⟩ : syracuseStep 4413257 = 3309943) B3309943
theorem B2479967 : Blo 1305971 2479967 := bstep (se 1 (by rfl) ⟨1859975, by rfl⟩ : syracuseStep 2479967 = 3719951) B3719951
theorem B4962167 : Blo 1305971 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B8943547 : Blo 1305971 8943547 := bstep (se 1 (by rfl) ⟨6707660, by rfl⟩ : syracuseStep 8943547 = 13415321) B13415321
theorem B16979971 : Blo 1305971 16979971 := bstep (se 1 (by rfl) ⟨12734978, by rfl⟩ : syracuseStep 16979971 = 25469957) B25469957
theorem B9418841 : Blo 1305971 9418841 := bstep (se 2 (by rfl) ⟨3532065, by rfl⟩ : syracuseStep 9418841 = 7064131) B7064131
theorem B2480377 : Blo 1305971 2480377 := bstep (se 2 (by rfl) ⟨930141, by rfl⟩ : syracuseStep 2480377 = 1860283) B1860283
theorem B4184381 : Blo 1305971 4184381 := bstep (se 3 (by rfl) ⟨784571, by rfl⟩ : syracuseStep 4184381 = 1569143) B1569143
theorem B11917721 : Blo 1305971 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B2791945 : Blo 1305971 2791945 := bstep (se 2 (by rfl) ⟨1046979, by rfl⟩ : syracuseStep 2791945 = 2093959) B2093959
theorem B2480719 : Blo 1305971 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B2939489 : Blo 1305971 2939489 := bstep (se 2 (by rfl) ⟨1102308, by rfl⟩ : syracuseStep 2939489 = 2204617) B2204617
theorem B8379065 : Blo 1305971 8379065 := bstep (se 2 (by rfl) ⟨3142149, by rfl⟩ : syracuseStep 8379065 = 6284299) B6284299
theorem B3775187 : Blo 1305971 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B2980601 : Blo 1305971 2980601 := bstep (se 2 (by rfl) ⟨1117725, by rfl⟩ : syracuseStep 2980601 = 2235451) B2235451
theorem B4963139 : Blo 1305971 4963139 := bstep (se 1 (by rfl) ⟨3722354, by rfl⟩ : syracuseStep 4963139 = 7444709) B7444709
theorem B2480969 : Blo 1305971 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B2939831 : Blo 1305971 2939831 := bstep (se 1 (by rfl) ⟨2204873, by rfl⟩ : syracuseStep 2939831 = 4409747) B4409747
theorem B4414391 : Blo 1305971 4414391 := bstep (se 1 (by rfl) ⟨3310793, by rfl⟩ : syracuseStep 4414391 = 6621587) B6621587
theorem B1653959 : Blo 1305971 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B9420047 : Blo 1305971 9420047 := bstep (se 1 (by rfl) ⟨7065035, by rfl⟩ : syracuseStep 9420047 = 14130071) B14130071
theorem B17890595 : Blo 1305971 17890595 := bstep (se 1 (by rfl) ⟨13417946, by rfl⟩ : syracuseStep 17890595 = 26835893) B26835893
theorem B1654111 : Blo 1305971 1654111 := bstep (se 1 (by rfl) ⟨1240583, by rfl⟩ : syracuseStep 1654111 = 2481167) B2481167
theorem B2940425 : Blo 1305971 2940425 := bstep (se 2 (by rfl) ⟨1102659, by rfl⟩ : syracuseStep 2940425 = 2205319) B2205319
theorem B5299751 : Blo 1305971 5299751 := bstep (se 1 (by rfl) ⟨3974813, by rfl⟩ : syracuseStep 5299751 = 7949627) B7949627
theorem B2481835 : Blo 1305971 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B7257799 : Blo 1305971 7257799 := bstep (se 1 (by rfl) ⟨5443349, by rfl⟩ : syracuseStep 7257799 = 10886699) B10886699
theorem B2481911 : Blo 1305971 2481911 := bstep (se 1 (by rfl) ⟨1861433, by rfl⟩ : syracuseStep 2481911 = 3722867) B3722867
theorem B2793209 : Blo 1305971 2793209 := bstep (se 2 (by rfl) ⟨1047453, by rfl⟩ : syracuseStep 2793209 = 2094907) B2094907
theorem B4964125 : Blo 1305971 4964125 := bstep (se 3 (by rfl) ⟨930773, by rfl⟩ : syracuseStep 4964125 = 1861547) B1861547
theorem B8380219 : Blo 1305971 8380219 := bstep (se 1 (by rfl) ⟨6285164, by rfl⟩ : syracuseStep 8380219 = 12570329) B12570329
theorem B2940767 : Blo 1305971 2940767 := bstep (se 1 (by rfl) ⟨2205575, by rfl⟩ : syracuseStep 2940767 = 4411151) B4411151
theorem B3309407 : Blo 1305971 3309407 := bstep (se 1 (by rfl) ⟨2482055, by rfl⟩ : syracuseStep 3309407 = 4964111) B4964111
theorem B4775867 : Blo 1305971 4775867 := bstep (se 1 (by rfl) ⟨3581900, by rfl⟩ : syracuseStep 4775867 = 7163801) B7163801
theorem B2482139 : Blo 1305971 2482139 := bstep (se 1 (by rfl) ⟨1861604, by rfl⟩ : syracuseStep 2482139 = 3723209) B3723209
theorem B3531005 : Blo 1305971 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B8946011 : Blo 1305971 8946011 := bstep (se 1 (by rfl) ⟨6709508, by rfl⟩ : syracuseStep 8946011 = 13419017) B13419017
theorem B2236763 : Blo 1305971 2236763 := bstep (se 1 (by rfl) ⟨1677572, by rfl⟩ : syracuseStep 2236763 = 3355145) B3355145
theorem B1860203 : Blo 1305971 1860203 := bstep (se 1 (by rfl) ⟨1395152, by rfl⟩ : syracuseStep 1860203 = 2790305) B2790305
theorem B8938187 : Blo 1305971 8938187 := bstep (se 1 (by rfl) ⟨6703640, by rfl⟩ : syracuseStep 8938187 = 13407281) B13407281
theorem B6611705 : Blo 1305971 6611705 := bstep (se 2 (by rfl) ⟨2479389, by rfl⟩ : syracuseStep 6611705 = 4958779) B4958779
theorem B9929465 : Blo 1305971 9929465 := bstep (se 2 (by rfl) ⟨3723549, by rfl⟩ : syracuseStep 9929465 = 7447099) B7447099
theorem B2941775 : Blo 1305971 2941775 := bstep (se 1 (by rfl) ⟨2206331, by rfl⟩ : syracuseStep 2941775 = 4412663) B4412663
theorem B26149891 : Blo 1305971 26149891 := bstep (se 1 (by rfl) ⟨19612418, by rfl⟩ : syracuseStep 26149891 = 39224837) B39224837
theorem B2941991 : Blo 1305971 2941991 := bstep (se 1 (by rfl) ⟨2206493, by rfl⟩ : syracuseStep 2941991 = 4412987) B4412987
theorem B6284413 : Blo 1305971 6284413 := bstep (se 3 (by rfl) ⟨1178327, by rfl⟩ : syracuseStep 6284413 = 2356655) B2356655
theorem B1959131 : Blo 1305971 1959131 := bstep (se 1 (by rfl) ⟨1469348, by rfl⟩ : syracuseStep 1959131 = 2938697) B2938697
theorem B2942171 : Blo 1305971 2942171 := bstep (se 1 (by rfl) ⟨2206628, by rfl⟩ : syracuseStep 2942171 = 4413257) B4413257
theorem B1860841 : Blo 1305971 1860841 := bstep (se 2 (by rfl) ⟨697815, by rfl⟩ : syracuseStep 1860841 = 1395631) B1395631
theorem B10601705 : Blo 1305971 10601705 := bstep (se 2 (by rfl) ⟨3975639, by rfl⟩ : syracuseStep 10601705 = 7951279) B7951279
theorem B1959305 : Blo 1305971 1959305 := bstep (se 2 (by rfl) ⟨734739, by rfl⟩ : syracuseStep 1959305 = 1469479) B1469479
theorem B4711841 : Blo 1305971 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B2942369 : Blo 1305971 2942369 := bstep (se 2 (by rfl) ⟨1103388, by rfl⟩ : syracuseStep 2942369 = 2206777) B2206777
theorem B1959659 : Blo 1305971 1959659 := bstep (se 1 (by rfl) ⟨1469744, by rfl⟩ : syracuseStep 1959659 = 2939489) B2939489
theorem B2205481 : Blo 1305971 2205481 := bstep (se 2 (by rfl) ⟨827055, by rfl⟩ : syracuseStep 2205481 = 1654111) B1654111
theorem B11159441 : Blo 1305971 11159441 := bstep (se 2 (by rfl) ⟨4184790, by rfl⟩ : syracuseStep 11159441 = 8369581) B8369581
theorem B7440335 : Blo 1305971 7440335 := bstep (se 1 (by rfl) ⟨5580251, by rfl⟩ : syracuseStep 7440335 = 11160503) B11160503
theorem B1959887 : Blo 1305971 1959887 := bstep (se 1 (by rfl) ⟨1469915, by rfl⟩ : syracuseStep 1959887 = 2939831) B2939831
theorem B2942927 : Blo 1305971 2942927 := bstep (se 1 (by rfl) ⟨2207195, by rfl⟩ : syracuseStep 2942927 = 4414391) B4414391
theorem B7448557 : Blo 1305971 7448557 := bstep (se 3 (by rfl) ⟨1396604, by rfl⟩ : syracuseStep 7448557 = 2793209) B2793209
theorem B6621263 : Blo 1305971 6621263 := bstep (se 1 (by rfl) ⟨4965947, by rfl⟩ : syracuseStep 6621263 = 9931895) B9931895
theorem B45893873 : Blo 1305971 45893873 := bstep (se 2 (by rfl) ⟨17210202, by rfl⟩ : syracuseStep 45893873 = 34420405) B34420405
theorem B9677065 : Blo 1305971 9677065 := bstep (se 2 (by rfl) ⟨3628899, by rfl⟩ : syracuseStep 9677065 = 7257799) B7257799
theorem B1960283 : Blo 1305971 1960283 := bstep (se 1 (by rfl) ⟨1470212, by rfl⟩ : syracuseStep 1960283 = 2940425) B2940425
theorem B3533167 : Blo 1305971 3533167 := bstep (se 1 (by rfl) ⟨2649875, by rfl⟩ : syracuseStep 3533167 = 5299751) B5299751
theorem B1395067 : Blo 1305971 1395067 := bstep (se 1 (by rfl) ⟨1046300, by rfl⟩ : syracuseStep 1395067 = 2092601) B2092601
theorem B3181025 : Blo 1305971 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B1960511 : Blo 1305971 1960511 := bstep (se 1 (by rfl) ⟨1470383, by rfl⟩ : syracuseStep 1960511 = 2940767) B2940767
theorem B2206271 : Blo 1305971 2206271 := bstep (se 1 (by rfl) ⟨1654703, by rfl⟩ : syracuseStep 2206271 = 3309407) B3309407
theorem B4409963 : Blo 1305971 4409963 := bstep (se 1 (by rfl) ⟨3307472, by rfl⟩ : syracuseStep 4409963 = 6614945) B6614945
theorem B1960631 : Blo 1305971 1960631 := bstep (se 1 (by rfl) ⟨1470473, by rfl⟩ : syracuseStep 1960631 = 2940947) B2940947
theorem B7441085 : Blo 1305971 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B5958467 : Blo 1305971 5958467 := bstep (se 1 (by rfl) ⟨4468850, by rfl⟩ : syracuseStep 5958467 = 8937701) B8937701
theorem B1469263 : Blo 1305971 1469263 := bstep (se 1 (by rfl) ⟨1101947, by rfl⟩ : syracuseStep 1469263 = 2203895) B2203895
theorem B1960859 : Blo 1305971 1960859 := bstep (se 1 (by rfl) ⟨1470644, by rfl⟩ : syracuseStep 1960859 = 2941289) B2941289
theorem B15494159 : Blo 1305971 15494159 := bstep (se 1 (by rfl) ⟨11620619, by rfl⟩ : syracuseStep 15494159 = 23241239) B23241239
theorem B3140747 : Blo 1305971 3140747 := bstep (se 1 (by rfl) ⟨2355560, by rfl⟩ : syracuseStep 3140747 = 4711121) B4711121
theorem B4410557 : Blo 1305971 4410557 := bstep (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) B1653959
theorem B1469659 : Blo 1305971 1469659 := bstep (se 1 (by rfl) ⟨1102244, by rfl⟩ : syracuseStep 1469659 = 2204489) B2204489
theorem B2206939 : Blo 1305971 2206939 := bstep (se 1 (by rfl) ⟨1655204, by rfl⟩ : syracuseStep 2206939 = 3310409) B3310409
theorem B22621457 : Blo 1305971 22621457 := bstep (se 2 (by rfl) ⟨8483046, by rfl⟩ : syracuseStep 22621457 = 16966093) B16966093
theorem B2092319 : Blo 1305971 2092319 := bstep (se 1 (by rfl) ⟨1569239, by rfl⟩ : syracuseStep 2092319 = 3138479) B3138479
theorem B1961255 : Blo 1305971 1961255 := bstep (se 1 (by rfl) ⟨1470941, by rfl⟩ : syracuseStep 1961255 = 2941883) B2941883
theorem B3722593 : Blo 1305971 3722593 := bstep (se 2 (by rfl) ⟨1395972, by rfl⟩ : syracuseStep 3722593 = 2791945) B2791945
theorem B82750835 : Blo 1305971 82750835 := bstep (se 1 (by rfl) ⟨62063126, by rfl⟩ : syracuseStep 82750835 = 124126253) B124126253
theorem B1961339 : Blo 1305971 1961339 := bstep (se 1 (by rfl) ⟨1471004, by rfl⟩ : syracuseStep 1961339 = 2942009) B2942009
theorem B7441793 : Blo 1305971 7441793 := bstep (se 2 (by rfl) ⟨2790672, by rfl⟩ : syracuseStep 7441793 = 5581345) B5581345
theorem B1306023 : Blo 1305971 1306023 := bstep (se 1 (by rfl) ⟨979517, by rfl⟩ : syracuseStep 1306023 = 1959035) B1959035
theorem B6614459 : Blo 1305971 6614459 := bstep (se 1 (by rfl) ⟨4960844, by rfl⟩ : syracuseStep 6614459 = 9921689) B9921689
theorem B4959737 : Blo 1305971 4959737 := bstep (se 2 (by rfl) ⟨1859901, by rfl⟩ : syracuseStep 4959737 = 3719803) B3719803
theorem B1961465 : Blo 1305971 1961465 := bstep (se 2 (by rfl) ⟨735549, by rfl⟩ : syracuseStep 1961465 = 1471099) B1471099
theorem B1306107 : Blo 1305971 1306107 := bstep (se 1 (by rfl) ⟨979580, by rfl⟩ : syracuseStep 1306107 = 1959161) B1959161
theorem B1469947 : Blo 1305971 1469947 := bstep (se 1 (by rfl) ⟨1102460, by rfl⟩ : syracuseStep 1469947 = 2204921) B2204921
theorem B1306175 : Blo 1305971 1306175 := bstep (se 1 (by rfl) ⟨979631, by rfl⟩ : syracuseStep 1306175 = 1959263) B1959263
theorem B1306183 : Blo 1305971 1306183 := bstep (se 1 (by rfl) ⟨979637, by rfl⟩ : syracuseStep 1306183 = 1959275) B1959275
theorem B1961567 : Blo 1305971 1961567 := bstep (se 1 (by rfl) ⟨1471175, by rfl⟩ : syracuseStep 1961567 = 2942351) B2942351
theorem B10604141 : Blo 1305971 10604141 := bstep (se 3 (by rfl) ⟨1988276, by rfl⟩ : syracuseStep 10604141 = 3976553) B3976553
theorem B1470127 : Blo 1305971 1470127 := bstep (se 1 (by rfl) ⟨1102595, by rfl⟩ : syracuseStep 1470127 = 2205191) B2205191
theorem B1306335 : Blo 1305971 1306335 := bstep (se 1 (by rfl) ⟨979751, by rfl⟩ : syracuseStep 1306335 = 1959503) B1959503
theorem B1306415 : Blo 1305971 1306415 := bstep (se 1 (by rfl) ⟨979811, by rfl⟩ : syracuseStep 1306415 = 1959623) B1959623
theorem B14135087 : Blo 1305971 14135087 := bstep (se 1 (by rfl) ⟨10601315, by rfl⟩ : syracuseStep 14135087 = 21202631) B21202631
theorem B1961783 : Blo 1305971 1961783 := bstep (se 1 (by rfl) ⟨1471337, by rfl⟩ : syracuseStep 1961783 = 2942675) B2942675
theorem B1306523 : Blo 1305971 1306523 := bstep (se 1 (by rfl) ⟨979892, by rfl⟩ : syracuseStep 1306523 = 1959785) B1959785
theorem B1306575 : Blo 1305971 1306575 := bstep (se 1 (by rfl) ⟨979931, by rfl⟩ : syracuseStep 1306575 = 1959863) B1959863
theorem B1470415 : Blo 1305971 1470415 := bstep (se 1 (by rfl) ⟨1102811, by rfl⟩ : syracuseStep 1470415 = 2205623) B2205623
theorem B1306599 : Blo 1305971 1306599 := bstep (se 1 (by rfl) ⟨979949, by rfl⟩ : syracuseStep 1306599 = 1959899) B1959899
theorem B6279227 : Blo 1305971 6279227 := bstep (se 1 (by rfl) ⟨4709420, by rfl⟩ : syracuseStep 6279227 = 9418841) B9418841
theorem B5583001 : Blo 1305971 5583001 := bstep (se 2 (by rfl) ⟨2093625, by rfl⟩ : syracuseStep 5583001 = 4187251) B4187251
theorem B2789587 : Blo 1305971 2789587 := bstep (se 1 (by rfl) ⟨2092190, by rfl⟩ : syracuseStep 2789587 = 4184381) B4184381
theorem B1306911 : Blo 1305971 1306911 := bstep (se 1 (by rfl) ⟨980183, by rfl⟩ : syracuseStep 1306911 = 1960367) B1960367
theorem B1306971 : Blo 1305971 1306971 := bstep (se 1 (by rfl) ⟨980228, by rfl⟩ : syracuseStep 1306971 = 1960457) B1960457
theorem B1470811 : Blo 1305971 1470811 := bstep (se 1 (by rfl) ⟨1103108, by rfl⟩ : syracuseStep 1470811 = 2206217) B2206217
theorem B1306991 : Blo 1305971 1306991 := bstep (se 1 (by rfl) ⟨980243, by rfl⟩ : syracuseStep 1306991 = 1960487) B1960487
theorem B1307047 : Blo 1305971 1307047 := bstep (se 1 (by rfl) ⟨980285, by rfl⟩ : syracuseStep 1307047 = 1960571) B1960571
theorem B3355063 : Blo 1305971 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B1470919 : Blo 1305971 1470919 := bstep (se 1 (by rfl) ⟨1103189, by rfl⟩ : syracuseStep 1470919 = 2206379) B2206379
theorem B1987067 : Blo 1305971 1987067 := bstep (se 1 (by rfl) ⟨1490300, by rfl⟩ : syracuseStep 1987067 = 2980601) B2980601
theorem B1307131 : Blo 1305971 1307131 := bstep (se 1 (by rfl) ⟨980348, by rfl⟩ : syracuseStep 1307131 = 1960697) B1960697
theorem B18846269 : Blo 1305971 18846269 := bstep (se 3 (by rfl) ⟨3533675, by rfl⟩ : syracuseStep 18846269 = 7067351) B7067351
theorem B1307199 : Blo 1305971 1307199 := bstep (se 1 (by rfl) ⟨980399, by rfl⟩ : syracuseStep 1307199 = 1960799) B1960799
theorem B3306055 : Blo 1305971 3306055 := bstep (se 1 (by rfl) ⟨2479541, by rfl⟩ : syracuseStep 3306055 = 4959083) B4959083
theorem B1307207 : Blo 1305971 1307207 := bstep (se 1 (by rfl) ⟨980405, by rfl⟩ : syracuseStep 1307207 = 1960811) B1960811
theorem B3306167 : Blo 1305971 3306167 := bstep (se 1 (by rfl) ⟨2479625, by rfl⟩ : syracuseStep 3306167 = 4959251) B4959251
theorem B6615755 : Blo 1305971 6615755 := bstep (se 1 (by rfl) ⟨4961816, by rfl⟩ : syracuseStep 6615755 = 9923633) B9923633
theorem B1307359 : Blo 1305971 1307359 := bstep (se 1 (by rfl) ⟨980519, by rfl⟩ : syracuseStep 1307359 = 1961039) B1961039
theorem B33952541 : Blo 1305971 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B1307439 : Blo 1305971 1307439 := bstep (se 1 (by rfl) ⟨980579, by rfl⟩ : syracuseStep 1307439 = 1961159) B1961159
theorem B1471279 : Blo 1305971 1471279 := bstep (se 1 (by rfl) ⟨1103459, by rfl⟩ : syracuseStep 1471279 = 2206919) B2206919
theorem B6280031 : Blo 1305971 6280031 := bstep (se 1 (by rfl) ⟨4710023, by rfl⟩ : syracuseStep 6280031 = 9420047) B9420047
theorem B6615917 : Blo 1305971 6615917 := bstep (se 3 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 6615917 = 2480969) B2480969
theorem B1307547 : Blo 1305971 1307547 := bstep (se 1 (by rfl) ⟨980660, by rfl⟩ : syracuseStep 1307547 = 1961321) B1961321
theorem B1471387 : Blo 1305971 1471387 := bstep (se 1 (by rfl) ⟨1103540, by rfl⟩ : syracuseStep 1471387 = 2207081) B2207081
theorem B9925577 : Blo 1305971 9925577 := bstep (se 2 (by rfl) ⟨3722091, by rfl⟩ : syracuseStep 9925577 = 7444183) B7444183
theorem B1307599 : Blo 1305971 1307599 := bstep (se 1 (by rfl) ⟨980699, by rfl⟩ : syracuseStep 1307599 = 1961399) B1961399
theorem B1307623 : Blo 1305971 1307623 := bstep (se 1 (by rfl) ⟨980717, by rfl⟩ : syracuseStep 1307623 = 1961435) B1961435
theorem B3142631 : Blo 1305971 3142631 := bstep (se 1 (by rfl) ⟨2356973, by rfl⟩ : syracuseStep 3142631 = 4713947) B4713947
theorem B4961513 : Blo 1305971 4961513 := bstep (se 2 (by rfl) ⟨1860567, by rfl⟩ : syracuseStep 4961513 = 3721135) B3721135
theorem B11924729 : Blo 1305971 11924729 := bstep (se 2 (by rfl) ⟨4471773, by rfl⟩ : syracuseStep 11924729 = 8943547) B8943547
theorem B1307935 : Blo 1305971 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B3183911 : Blo 1305971 3183911 := bstep (se 1 (by rfl) ⟨2387933, by rfl⟩ : syracuseStep 3183911 = 4775867) B4775867
theorem B22639961 : Blo 1305971 22639961 := bstep (se 2 (by rfl) ⟨8489985, by rfl⟩ : syracuseStep 22639961 = 16979971) B16979971
theorem B16741727 : Blo 1305971 16741727 := bstep (se 1 (by rfl) ⟨12556295, by rfl⟩ : syracuseStep 16741727 = 25112591) B25112591
theorem B9917801 : Blo 1305971 9917801 := bstep (se 2 (by rfl) ⟨3719175, by rfl⟩ : syracuseStep 9917801 = 7438351) B7438351
theorem B12563905 : Blo 1305971 12563905 := bstep (se 2 (by rfl) ⟨4711464, by rfl⟩ : syracuseStep 12563905 = 9422929) B9422929
theorem B2938463 : Blo 1305971 2938463 := bstep (se 1 (by rfl) ⟨2203847, by rfl⟩ : syracuseStep 2938463 = 4407695) B4407695
theorem B3307169 : Blo 1305971 3307169 := bstep (se 2 (by rfl) ⟨1240188, by rfl⟩ : syracuseStep 3307169 = 2480377) B2480377
theorem B2094779 : Blo 1305971 2094779 := bstep (se 1 (by rfl) ⟨1571084, by rfl⟩ : syracuseStep 2094779 = 3142169) B3142169
theorem B2938679 : Blo 1305971 2938679 := bstep (se 1 (by rfl) ⟨2204009, by rfl⟩ : syracuseStep 2938679 = 4408019) B4408019
theorem B4708151 : Blo 1305971 4708151 := bstep (se 1 (by rfl) ⟨3531113, by rfl⟩ : syracuseStep 4708151 = 7062227) B7062227
theorem B4413473 : Blo 1305971 4413473 := bstep (se 2 (by rfl) ⟨1655052, by rfl⟩ : syracuseStep 4413473 = 3310105) B3310105
theorem B28260413 : Blo 1305971 28260413 := bstep (se 3 (by rfl) ⟨5298827, by rfl⟩ : syracuseStep 28260413 = 10597655) B10597655
theorem B16758845 : Blo 1305971 16758845 := bstep (se 3 (by rfl) ⟨3142283, by rfl⟩ : syracuseStep 16758845 = 6284567) B6284567
theorem B2938985 : Blo 1305971 2938985 := bstep (se 2 (by rfl) ⟨1102119, by rfl⟩ : syracuseStep 2938985 = 2204239) B2204239
theorem B2480233 : Blo 1305971 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B3307625 : Blo 1305971 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B1677691 : Blo 1305971 1677691 := bstep (se 1 (by rfl) ⟨1258268, by rfl⟩ : syracuseStep 1677691 = 2516537) B2516537
theorem B2480635 : Blo 1305971 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B1653311 : Blo 1305971 1653311 := bstep (se 1 (by rfl) ⟨1239983, by rfl⟩ : syracuseStep 1653311 = 2479967) B2479967
theorem B2939471 : Blo 1305971 2939471 := bstep (se 1 (by rfl) ⟨2204603, by rfl⟩ : syracuseStep 2939471 = 4409207) B4409207
theorem B3308111 : Blo 1305971 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B3185335 : Blo 1305971 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B2939615 : Blo 1305971 2939615 := bstep (se 1 (by rfl) ⟨2204711, by rfl⟩ : syracuseStep 2939615 = 4409423) B4409423
theorem B2480863 : Blo 1305971 2480863 := bstep (se 1 (by rfl) ⟨1860647, by rfl⟩ : syracuseStep 2480863 = 3721295) B3721295
theorem B7945147 : Blo 1305971 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B2939867 : Blo 1305971 2939867 := bstep (se 1 (by rfl) ⟨2204900, by rfl⟩ : syracuseStep 2939867 = 4409801) B4409801
theorem B5586043 : Blo 1305971 5586043 := bstep (se 1 (by rfl) ⟨4189532, by rfl⟩ : syracuseStep 5586043 = 8379065) B8379065
theorem B2940047 : Blo 1305971 2940047 := bstep (se 1 (by rfl) ⟨2205035, by rfl⟩ : syracuseStep 2940047 = 4410071) B4410071
theorem B3308759 : Blo 1305971 3308759 := bstep (se 1 (by rfl) ⟨2481569, by rfl⟩ : syracuseStep 3308759 = 4963139) B4963139
theorem B10067165 : Blo 1305971 10067165 := bstep (se 3 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 10067165 = 3775187) B3775187
theorem B2940137 : Blo 1305971 2940137 := bstep (se 2 (by rfl) ⟨1102551, by rfl⟩ : syracuseStep 2940137 = 2205103) B2205103
theorem B2940191 : Blo 1305971 2940191 := bstep (se 1 (by rfl) ⟨2205143, by rfl⟩ : syracuseStep 2940191 = 4410287) B4410287
theorem B2235847 : Blo 1305971 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B2481607 : Blo 1305971 2481607 := bstep (se 1 (by rfl) ⟨1861205, by rfl⟩ : syracuseStep 2481607 = 3722411) B3722411
theorem B11927063 : Blo 1305971 11927063 := bstep (se 1 (by rfl) ⟨8945297, by rfl⟩ : syracuseStep 11927063 = 17890595) B17890595
theorem B3309113 : Blo 1305971 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B6618833 : Blo 1305971 6618833 := bstep (se 2 (by rfl) ⟨2482062, by rfl⟩ : syracuseStep 6618833 = 4964125) B4964125
theorem B11173625 : Blo 1305971 11173625 := bstep (se 2 (by rfl) ⟨4190109, by rfl⟩ : syracuseStep 11173625 = 8380219) B8380219
theorem B2514695 : Blo 1305971 2514695 := bstep (se 1 (by rfl) ⟨1886021, by rfl⟩ : syracuseStep 2514695 = 3772043) B3772043
theorem B7069447 : Blo 1305971 7069447 := bstep (se 1 (by rfl) ⟨5302085, by rfl⟩ : syracuseStep 7069447 = 10604171) B10604171
theorem B2940713 : Blo 1305971 2940713 := bstep (se 2 (by rfl) ⟨1102767, by rfl⟩ : syracuseStep 2940713 = 2205535) B2205535
theorem B1654607 : Blo 1305971 1654607 := bstep (se 1 (by rfl) ⟨1240955, by rfl⟩ : syracuseStep 1654607 = 2481911) B2481911
theorem B6283183 : Blo 1305971 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B1654759 : Blo 1305971 1654759 := bstep (se 1 (by rfl) ⟨1241069, by rfl⟩ : syracuseStep 1654759 = 2482139) B2482139
theorem B4186151 : Blo 1305971 4186151 := bstep (se 1 (by rfl) ⟨3139613, by rfl⟩ : syracuseStep 4186151 = 6279227) B6279227
theorem B1491175 : Blo 1305971 1491175 := bstep (se 1 (by rfl) ⟨1118381, by rfl⟩ : syracuseStep 1491175 = 2236763) B2236763
theorem B3719449 : Blo 1305971 3719449 := bstep (se 2 (by rfl) ⟨1394793, by rfl⟩ : syracuseStep 3719449 = 2789587) B2789587
theorem B12902753 : Blo 1305971 12902753 := bstep (se 2 (by rfl) ⟨4838532, by rfl⟩ : syracuseStep 12902753 = 9677065) B9677065
theorem B2204111 : Blo 1305971 2204111 := bstep (se 1 (by rfl) ⟨1653083, by rfl⟩ : syracuseStep 2204111 = 3306167) B3306167
theorem B4710889 : Blo 1305971 4710889 := bstep (se 2 (by rfl) ⟨1766583, by rfl⟩ : syracuseStep 4710889 = 3533167) B3533167
theorem B1860089 : Blo 1305971 1860089 := bstep (se 2 (by rfl) ⟨697533, by rfl⟩ : syracuseStep 1860089 = 1395067) B1395067
theorem B4407803 : Blo 1305971 4407803 := bstep (se 1 (by rfl) ⟨3305852, by rfl⟩ : syracuseStep 4407803 = 6611705) B6611705
theorem B6619643 : Blo 1305971 6619643 := bstep (se 1 (by rfl) ⟨4964732, by rfl⟩ : syracuseStep 6619643 = 9929465) B9929465
theorem B28271213 : Blo 1305971 28271213 := bstep (se 3 (by rfl) ⟨5300852, by rfl⟩ : syracuseStep 28271213 = 10601705) B10601705
theorem B4408073 : Blo 1305971 4408073 := bstep (se 2 (by rfl) ⟨1653027, by rfl⟩ : syracuseStep 4408073 = 3306055) B3306055
theorem B2122607 : Blo 1305971 2122607 := bstep (se 1 (by rfl) ⟨1591955, by rfl⟩ : syracuseStep 2122607 = 3183911) B3183911
theorem B6611867 : Blo 1305971 6611867 := bstep (se 1 (by rfl) ⟨4958900, by rfl⟩ : syracuseStep 6611867 = 9917801) B9917801
theorem B23856029 : Blo 1305971 23856029 := bstep (se 3 (by rfl) ⟨4473005, by rfl⟩ : syracuseStep 23856029 = 8946011) B8946011
theorem B220668893 : Blo 1305971 220668893 := bstep (se 3 (by rfl) ⟨41375417, by rfl⟩ : syracuseStep 220668893 = 82750835) B82750835
theorem B1958975 : Blo 1305971 1958975 := bstep (se 1 (by rfl) ⟨1469231, by rfl⟩ : syracuseStep 1958975 = 2938463) B2938463
theorem B1959017 : Blo 1305971 1959017 := bstep (se 2 (by rfl) ⟨734631, by rfl⟩ : syracuseStep 1959017 = 1469263) B1469263
theorem B2204779 : Blo 1305971 2204779 := bstep (se 1 (by rfl) ⟨1653584, by rfl⟩ : syracuseStep 2204779 = 3307169) B3307169
theorem B1959119 : Blo 1305971 1959119 := bstep (se 1 (by rfl) ⟨1469339, by rfl⟩ : syracuseStep 1959119 = 2938679) B2938679
theorem B3138767 : Blo 1305971 3138767 := bstep (se 1 (by rfl) ⟨2354075, by rfl⟩ : syracuseStep 3138767 = 4708151) B4708151
theorem B7439627 : Blo 1305971 7439627 := bstep (se 1 (by rfl) ⟨5579720, by rfl⟩ : syracuseStep 7439627 = 11159441) B11159441
theorem B34866521 : Blo 1305971 34866521 := bstep (se 2 (by rfl) ⟨13074945, by rfl⟩ : syracuseStep 34866521 = 26149891) B26149891
theorem B2942315 : Blo 1305971 2942315 := bstep (se 1 (by rfl) ⟨2206736, by rfl⟩ : syracuseStep 2942315 = 4413473) B4413473
theorem B1959323 : Blo 1305971 1959323 := bstep (se 1 (by rfl) ⟨1469492, by rfl⟩ : syracuseStep 1959323 = 2938985) B2938985
theorem B2205083 : Blo 1305971 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B7448057 : Blo 1305971 7448057 := bstep (se 2 (by rfl) ⟨2793021, by rfl⟩ : syracuseStep 7448057 = 5586043) B5586043
theorem B4408829 : Blo 1305971 4408829 := bstep (se 3 (by rfl) ⟨826655, by rfl⟩ : syracuseStep 4408829 = 1653311) B1653311
theorem B1959545 : Blo 1305971 1959545 := bstep (se 2 (by rfl) ⟨734829, by rfl⟩ : syracuseStep 1959545 = 1469659) B1469659
theorem B2942585 : Blo 1305971 2942585 := bstep (se 2 (by rfl) ⟨1103469, by rfl⟩ : syracuseStep 2942585 = 2206939) B2206939
theorem B1959647 : Blo 1305971 1959647 := bstep (se 1 (by rfl) ⟨1469735, by rfl⟩ : syracuseStep 1959647 = 2939471) B2939471
theorem B2205407 : Blo 1305971 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B1959743 : Blo 1305971 1959743 := bstep (se 1 (by rfl) ⟨1469807, by rfl⟩ : syracuseStep 1959743 = 2939615) B2939615
theorem B8947685 : Blo 1305971 8947685 := bstep (se 4 (by rfl) ⟨838845, by rfl⟩ : syracuseStep 8947685 = 1677691) B1677691
theorem B1959911 : Blo 1305971 1959911 := bstep (se 1 (by rfl) ⟨1469933, by rfl⟩ : syracuseStep 1959911 = 2939867) B2939867
theorem B1959929 : Blo 1305971 1959929 := bstep (se 2 (by rfl) ⟨734973, by rfl⟩ : syracuseStep 1959929 = 1469947) B1469947
theorem B90540109 : Blo 1305971 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B1960031 : Blo 1305971 1960031 := bstep (se 1 (by rfl) ⟨1470023, by rfl⟩ : syracuseStep 1960031 = 2940047) B2940047
theorem B2205839 : Blo 1305971 2205839 := bstep (se 1 (by rfl) ⟨1654379, by rfl⟩ : syracuseStep 2205839 = 3308759) B3308759
theorem B6711443 : Blo 1305971 6711443 := bstep (se 1 (by rfl) ⟨5033582, by rfl⟩ : syracuseStep 6711443 = 10067165) B10067165
theorem B1960091 : Blo 1305971 1960091 := bstep (se 1 (by rfl) ⟨1470068, by rfl⟩ : syracuseStep 1960091 = 2940137) B2940137
theorem B1394879 : Blo 1305971 1394879 := bstep (se 1 (by rfl) ⟨1046159, by rfl⟩ : syracuseStep 1394879 = 2092319) B2092319
theorem B1960127 : Blo 1305971 1960127 := bstep (se 1 (by rfl) ⟨1470095, by rfl⟩ : syracuseStep 1960127 = 2940191) B2940191
theorem B1960169 : Blo 1305971 1960169 := bstep (se 2 (by rfl) ⟨735063, by rfl⟩ : syracuseStep 1960169 = 1470127) B1470127
theorem B16746749 : Blo 1305971 16746749 := bstep (se 3 (by rfl) ⟨3140015, by rfl⟩ : syracuseStep 16746749 = 6280031) B6280031
theorem B4409639 : Blo 1305971 4409639 := bstep (se 1 (by rfl) ⟨3307229, by rfl⟩ : syracuseStep 4409639 = 6614459) B6614459
theorem B17893669 : Blo 1305971 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B2206075 : Blo 1305971 2206075 := bstep (se 1 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 2206075 = 3309113) B3309113
theorem B7449083 : Blo 1305971 7449083 := bstep (se 1 (by rfl) ⟨5586812, by rfl⟩ : syracuseStep 7449083 = 11173625) B11173625
theorem B1960475 : Blo 1305971 1960475 := bstep (se 1 (by rfl) ⟨1470356, by rfl⟩ : syracuseStep 1960475 = 2940713) B2940713
theorem B9423391 : Blo 1305971 9423391 := bstep (se 1 (by rfl) ⟨7067543, by rfl⟩ : syracuseStep 9423391 = 14135087) B14135087
theorem B1960553 : Blo 1305971 1960553 := bstep (se 2 (by rfl) ⟨735207, by rfl⟩ : syracuseStep 1960553 = 1470415) B1470415
theorem B2206345 : Blo 1305971 2206345 := bstep (se 2 (by rfl) ⟨827379, by rfl⟩ : syracuseStep 2206345 = 1654759) B1654759
theorem B9931409 : Blo 1305971 9931409 := bstep (se 2 (by rfl) ⟨3724278, by rfl⟩ : syracuseStep 9931409 = 7448557) B7448557
theorem B26823413 : Blo 1305971 26823413 := bstep (se 5 (by rfl) ⟨1257347, by rfl⟩ : syracuseStep 26823413 = 2514695) B2514695
theorem B2354003 : Blo 1305971 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B1961081 : Blo 1305971 1961081 := bstep (se 2 (by rfl) ⟨735405, by rfl⟩ : syracuseStep 1961081 = 1470811) B1470811
theorem B5958791 : Blo 1305971 5958791 := bstep (se 1 (by rfl) ⟨4469093, by rfl⟩ : syracuseStep 5958791 = 8938187) B8938187
theorem B4410503 : Blo 1305971 4410503 := bstep (se 1 (by rfl) ⟨3307877, by rfl⟩ : syracuseStep 4410503 = 6615755) B6615755
theorem B1961183 : Blo 1305971 1961183 := bstep (se 1 (by rfl) ⟨1470887, by rfl⟩ : syracuseStep 1961183 = 2941775) B2941775
theorem B4410611 : Blo 1305971 4410611 := bstep (se 1 (by rfl) ⟨3307958, by rfl⟩ : syracuseStep 4410611 = 6615917) B6615917
theorem B1961225 : Blo 1305971 1961225 := bstep (se 2 (by rfl) ⟨735459, by rfl⟩ : syracuseStep 1961225 = 1470919) B1470919
theorem B1961327 : Blo 1305971 1961327 := bstep (se 1 (by rfl) ⟨1470995, by rfl⟩ : syracuseStep 1961327 = 2941991) B2941991
theorem B1306087 : Blo 1305971 1306087 := bstep (se 1 (by rfl) ⟨979565, by rfl⟩ : syracuseStep 1306087 = 1959131) B1959131
theorem B1961447 : Blo 1305971 1961447 := bstep (se 1 (by rfl) ⟨1471085, by rfl⟩ : syracuseStep 1961447 = 2942171) B2942171
theorem B7949819 : Blo 1305971 7949819 := bstep (se 1 (by rfl) ⟨5962364, by rfl⟩ : syracuseStep 7949819 = 11924729) B11924729
theorem B15093307 : Blo 1305971 15093307 := bstep (se 1 (by rfl) ⟨11319980, by rfl⟩ : syracuseStep 15093307 = 22639961) B22639961
theorem B11161151 : Blo 1305971 11161151 := bstep (se 1 (by rfl) ⟨8370863, by rfl⟩ : syracuseStep 11161151 = 16741727) B16741727
theorem B4247113 : Blo 1305971 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B1306203 : Blo 1305971 1306203 := bstep (se 1 (by rfl) ⟨979652, by rfl⟩ : syracuseStep 1306203 = 1959305) B1959305
theorem B3141227 : Blo 1305971 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B1961579 : Blo 1305971 1961579 := bstep (se 1 (by rfl) ⟨1471184, by rfl⟩ : syracuseStep 1961579 = 2942369) B2942369
theorem B1961705 : Blo 1305971 1961705 := bstep (se 2 (by rfl) ⟨735639, by rfl⟩ : syracuseStep 1961705 = 1471279) B1471279
theorem B1306439 : Blo 1305971 1306439 := bstep (se 1 (by rfl) ⟨979829, by rfl⟩ : syracuseStep 1306439 = 1959659) B1959659
theorem B1961849 : Blo 1305971 1961849 := bstep (se 2 (by rfl) ⟨735693, by rfl⟩ : syracuseStep 1961849 = 1471387) B1471387
theorem B8482733 : Blo 1305971 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B4960223 : Blo 1305971 4960223 := bstep (se 1 (by rfl) ⟨3720167, by rfl⟩ : syracuseStep 4960223 = 7440335) B7440335
theorem B1306591 : Blo 1305971 1306591 := bstep (se 1 (by rfl) ⟨979943, by rfl⟩ : syracuseStep 1306591 = 1959887) B1959887
theorem B1961951 : Blo 1305971 1961951 := bstep (se 1 (by rfl) ⟨1471463, by rfl⟩ : syracuseStep 1961951 = 2942927) B2942927
theorem B1306855 : Blo 1305971 1306855 := bstep (se 1 (by rfl) ⟨980141, by rfl⟩ : syracuseStep 1306855 = 1960283) B1960283
theorem B4960541 : Blo 1305971 4960541 := bstep (se 3 (by rfl) ⟨930101, by rfl⟩ : syracuseStep 4960541 = 1860203) B1860203
theorem B1307007 : Blo 1305971 1307007 := bstep (se 1 (by rfl) ⟨980255, by rfl⟩ : syracuseStep 1307007 = 1960511) B1960511
theorem B1470847 : Blo 1305971 1470847 := bstep (se 1 (by rfl) ⟨1103135, by rfl⟩ : syracuseStep 1470847 = 2206271) B2206271
theorem B1307087 : Blo 1305971 1307087 := bstep (se 1 (by rfl) ⟨980315, by rfl⟩ : syracuseStep 1307087 = 1960631) B1960631
theorem B4960723 : Blo 1305971 4960723 := bstep (se 1 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 4960723 = 7441085) B7441085
theorem B1307239 : Blo 1305971 1307239 := bstep (se 1 (by rfl) ⟨980429, by rfl⟩ : syracuseStep 1307239 = 1960859) B1960859
theorem B2093831 : Blo 1305971 2093831 := bstep (se 1 (by rfl) ⟨1570373, by rfl⟩ : syracuseStep 2093831 = 3140747) B3140747
theorem B1307503 : Blo 1305971 1307503 := bstep (se 1 (by rfl) ⟨980627, by rfl⟩ : syracuseStep 1307503 = 1961255) B1961255
theorem B4412285 : Blo 1305971 4412285 := bstep (se 3 (by rfl) ⟨827303, by rfl⟩ : syracuseStep 4412285 = 1654607) B1654607
theorem B1307559 : Blo 1305971 1307559 := bstep (se 1 (by rfl) ⟨980669, by rfl⟩ : syracuseStep 1307559 = 1961339) B1961339
theorem B4961195 : Blo 1305971 4961195 := bstep (se 1 (by rfl) ⟨3720896, by rfl⟩ : syracuseStep 4961195 = 7441793) B7441793
theorem B42374117 : Blo 1305971 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B3306491 : Blo 1305971 3306491 := bstep (se 1 (by rfl) ⟨2479868, by rfl⟩ : syracuseStep 3306491 = 4959737) B4959737
theorem B1307643 : Blo 1305971 1307643 := bstep (se 1 (by rfl) ⟨980732, by rfl⟩ : syracuseStep 1307643 = 1961465) B1961465
theorem B9425929 : Blo 1305971 9425929 := bstep (se 2 (by rfl) ⟨3534723, by rfl⟩ : syracuseStep 9425929 = 7069447) B7069447
theorem B7951375 : Blo 1305971 7951375 := bstep (se 1 (by rfl) ⟨5963531, by rfl⟩ : syracuseStep 7951375 = 11927063) B11927063
theorem B1307711 : Blo 1305971 1307711 := bstep (se 1 (by rfl) ⟨980783, by rfl⟩ : syracuseStep 1307711 = 1961567) B1961567
theorem B4412555 : Blo 1305971 4412555 := bstep (se 1 (by rfl) ⟨3309416, by rfl⟩ : syracuseStep 4412555 = 6618833) B6618833
theorem B1307855 : Blo 1305971 1307855 := bstep (se 1 (by rfl) ⟨980891, by rfl⟩ : syracuseStep 1307855 = 1961783) B1961783
theorem B8377577 : Blo 1305971 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B3306977 : Blo 1305971 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B7444001 : Blo 1305971 7444001 := bstep (se 2 (by rfl) ⟨2791500, by rfl⟩ : syracuseStep 7444001 = 5583001) B5583001
theorem B1324711 : Blo 1305971 1324711 := bstep (se 1 (by rfl) ⟨993533, by rfl⟩ : syracuseStep 1324711 = 1987067) B1987067
theorem B12564179 : Blo 1305971 12564179 := bstep (se 1 (by rfl) ⟨9423134, by rfl⟩ : syracuseStep 12564179 = 18846269) B18846269
theorem B6617051 : Blo 1305971 6617051 := bstep (se 1 (by rfl) ⟨4962788, by rfl⟩ : syracuseStep 6617051 = 9925577) B9925577
theorem B2095087 : Blo 1305971 2095087 := bstep (se 1 (by rfl) ⟨1571315, by rfl⟩ : syracuseStep 2095087 = 3142631) B3142631
theorem B3307513 : Blo 1305971 3307513 := bstep (se 2 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 3307513 = 2480635) B2480635
theorem B60323885 : Blo 1305971 60323885 := bstep (se 3 (by rfl) ⟨11310728, by rfl⟩ : syracuseStep 60323885 = 22621457) B22621457
theorem B3307675 : Blo 1305971 3307675 := bstep (se 1 (by rfl) ⟨2480756, by rfl⟩ : syracuseStep 3307675 = 4961513) B4961513
theorem B3307817 : Blo 1305971 3307817 := bstep (se 2 (by rfl) ⟨1240431, by rfl⟩ : syracuseStep 3307817 = 2480863) B2480863
theorem B18840275 : Blo 1305971 18840275 := bstep (se 1 (by rfl) ⟨14130206, by rfl⟩ : syracuseStep 18840275 = 28260413) B28260413
theorem B11172563 : Blo 1305971 11172563 := bstep (se 1 (by rfl) ⟨8379422, by rfl⟩ : syracuseStep 11172563 = 16758845) B16758845
theorem B4414175 : Blo 1305971 4414175 := bstep (se 1 (by rfl) ⟨3310631, by rfl⟩ : syracuseStep 4414175 = 6621263) B6621263
theorem B30595915 : Blo 1305971 30595915 := bstep (se 1 (by rfl) ⟨22946936, by rfl⟩ : syracuseStep 30595915 = 45893873) B45893873
theorem B8379217 : Blo 1305971 8379217 := bstep (se 2 (by rfl) ⟨3142206, by rfl⟩ : syracuseStep 8379217 = 6284413) B6284413
theorem B2481121 : Blo 1305971 2481121 := bstep (se 2 (by rfl) ⟨930420, by rfl⟩ : syracuseStep 2481121 = 1860841) B1860841
theorem B2939975 : Blo 1305971 2939975 := bstep (se 1 (by rfl) ⟨2204981, by rfl⟩ : syracuseStep 2939975 = 4409963) B4409963
theorem B4963457 : Blo 1305971 4963457 := bstep (se 2 (by rfl) ⟨1861296, by rfl⟩ : syracuseStep 4963457 = 3722593) B3722593
theorem B5586077 : Blo 1305971 5586077 := bstep (se 3 (by rfl) ⟨1047389, by rfl⟩ : syracuseStep 5586077 = 2094779) B2094779
theorem B3972311 : Blo 1305971 3972311 := bstep (se 1 (by rfl) ⟨2979233, by rfl⟩ : syracuseStep 3972311 = 5958467) B5958467
theorem B16751873 : Blo 1305971 16751873 := bstep (se 2 (by rfl) ⟨6281952, by rfl⟩ : syracuseStep 16751873 = 12563905) B12563905
theorem B2981129 : Blo 1305971 2981129 := bstep (se 2 (by rfl) ⟨1117923, by rfl⟩ : syracuseStep 2981129 = 2235847) B2235847
theorem B3308809 : Blo 1305971 3308809 := bstep (se 2 (by rfl) ⟨1240803, by rfl⟩ : syracuseStep 3308809 = 2481607) B2481607
theorem B10329439 : Blo 1305971 10329439 := bstep (se 1 (by rfl) ⟨7747079, by rfl⟩ : syracuseStep 10329439 = 15494159) B15494159
theorem B2940371 : Blo 1305971 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B2940641 : Blo 1305971 2940641 := bstep (se 2 (by rfl) ⟨1102740, by rfl⟩ : syracuseStep 2940641 = 2205481) B2205481
theorem B7069427 : Blo 1305971 7069427 := bstep (se 1 (by rfl) ⟨5302070, by rfl⟩ : syracuseStep 7069427 = 10604141) B10604141
theorem B8601835 : Blo 1305971 8601835 := bstep (se 1 (by rfl) ⟨6451376, by rfl⟩ : syracuseStep 8601835 = 12902753) B12902753
theorem B2941433 : Blo 1305971 2941433 := bstep (se 2 (by rfl) ⟨1103037, by rfl⟩ : syracuseStep 2941433 = 2206075) B2206075
theorem B3719677 : Blo 1305971 3719677 := bstep (se 3 (by rfl) ⟨697439, by rfl⟩ : syracuseStep 3719677 = 1394879) B1394879
theorem B2941523 : Blo 1305971 2941523 := bstep (se 1 (by rfl) ⟨2206142, by rfl⟩ : syracuseStep 2941523 = 4412285) B4412285
theorem B4407911 : Blo 1305971 4407911 := bstep (se 1 (by rfl) ⟨3305933, by rfl⟩ : syracuseStep 4407911 = 6611867) B6611867
theorem B147112595 : Blo 1305971 147112595 := bstep (se 1 (by rfl) ⟨110334446, by rfl⟩ : syracuseStep 147112595 = 220668893) B220668893
theorem B2204327 : Blo 1305971 2204327 := bstep (se 1 (by rfl) ⟨1653245, by rfl⟩ : syracuseStep 2204327 = 3306491) B3306491
theorem B2941703 : Blo 1305971 2941703 := bstep (se 1 (by rfl) ⟨2206277, by rfl⟩ : syracuseStep 2941703 = 4412555) B4412555
theorem B2941793 : Blo 1305971 2941793 := bstep (se 2 (by rfl) ⟨1103172, by rfl⟩ : syracuseStep 2941793 = 2206345) B2206345
theorem B2204651 : Blo 1305971 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B4965371 : Blo 1305971 4965371 := bstep (se 1 (by rfl) ⟨3724028, by rfl⟩ : syracuseStep 4965371 = 7448057) B7448057
theorem B5965123 : Blo 1305971 5965123 := bstep (se 1 (by rfl) ⟨4473842, by rfl⟩ : syracuseStep 5965123 = 8947685) B8947685
theorem B12567905 : Blo 1305971 12567905 := bstep (se 2 (by rfl) ⟨4712964, by rfl⟩ : syracuseStep 12567905 = 9425929) B9425929
theorem B40215923 : Blo 1305971 40215923 := bstep (se 1 (by rfl) ⟨30161942, by rfl⟩ : syracuseStep 40215923 = 60323885) B60323885
theorem B4474295 : Blo 1305971 4474295 := bstep (se 1 (by rfl) ⟨3355721, by rfl⟩ : syracuseStep 4474295 = 6711443) B6711443
theorem B2205211 : Blo 1305971 2205211 := bstep (se 1 (by rfl) ⟨1653908, by rfl⟩ : syracuseStep 2205211 = 3307817) B3307817
theorem B4966055 : Blo 1305971 4966055 := bstep (se 1 (by rfl) ⟨3724541, by rfl⟩ : syracuseStep 4966055 = 7449083) B7449083
theorem B6620939 : Blo 1305971 6620939 := bstep (se 1 (by rfl) ⟨4965704, by rfl⟩ : syracuseStep 6620939 = 9931409) B9931409
theorem B13772585 : Blo 1305971 13772585 := bstep (se 2 (by rfl) ⟨5164719, by rfl⟩ : syracuseStep 13772585 = 10329439) B10329439
theorem B12560183 : Blo 1305971 12560183 := bstep (se 1 (by rfl) ⟨9420137, by rfl⟩ : syracuseStep 12560183 = 18840275) B18840275
theorem B7448375 : Blo 1305971 7448375 := bstep (se 1 (by rfl) ⟨5586281, by rfl⟩ : syracuseStep 7448375 = 11172563) B11172563
theorem B2942783 : Blo 1305971 2942783 := bstep (se 1 (by rfl) ⟨2207087, by rfl⟩ : syracuseStep 2942783 = 4414175) B4414175
theorem B1959983 : Blo 1305971 1959983 := bstep (se 1 (by rfl) ⟨1469987, by rfl⟩ : syracuseStep 1959983 = 2939975) B2939975
theorem B5662817 : Blo 1305971 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B2648207 : Blo 1305971 2648207 := bstep (se 1 (by rfl) ⟨1986155, by rfl⟩ : syracuseStep 2648207 = 3972311) B3972311
theorem B11167915 : Blo 1305971 11167915 := bstep (se 1 (by rfl) ⟨8375936, by rfl⟩ : syracuseStep 11167915 = 16751873) B16751873
theorem B1960247 : Blo 1305971 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B7440767 : Blo 1305971 7440767 := bstep (se 1 (by rfl) ⟨5580575, by rfl⟩ : syracuseStep 7440767 = 11161151) B11161151
theorem B1960427 : Blo 1305971 1960427 := bstep (se 1 (by rfl) ⟨1470320, by rfl⟩ : syracuseStep 1960427 = 2940641) B2940641
theorem B4712951 : Blo 1305971 4712951 := bstep (se 1 (by rfl) ⟨3534713, by rfl⟩ : syracuseStep 4712951 = 7069427) B7069427
theorem B5655155 : Blo 1305971 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B4410017 : Blo 1305971 4410017 := bstep (se 2 (by rfl) ⟨1653756, by rfl⟩ : syracuseStep 4410017 = 3307513) B3307513
theorem B120720145 : Blo 1305971 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B4410233 : Blo 1305971 4410233 := bstep (se 2 (by rfl) ⟨1653837, by rfl⟩ : syracuseStep 4410233 = 3307675) B3307675
theorem B1469407 : Blo 1305971 1469407 := bstep (se 1 (by rfl) ⟨1102055, by rfl⟩ : syracuseStep 1469407 = 2204111) B2204111
theorem B4959265 : Blo 1305971 4959265 := bstep (se 2 (by rfl) ⟨1859724, by rfl⟩ : syracuseStep 4959265 = 3719449) B3719449
theorem B23858225 : Blo 1305971 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B1961129 : Blo 1305971 1961129 := bstep (se 2 (by rfl) ⟨735423, by rfl⟩ : syracuseStep 1961129 = 1470847) B1470847
theorem B1395887 : Blo 1305971 1395887 := bstep (se 1 (by rfl) ⟨1046915, by rfl⟩ : syracuseStep 1395887 = 2093831) B2093831
theorem B15904019 : Blo 1305971 15904019 := bstep (se 1 (by rfl) ⟨11928014, by rfl⟩ : syracuseStep 15904019 = 23856029) B23856029
theorem B6614297 : Blo 1305971 6614297 := bstep (se 2 (by rfl) ⟨2480361, by rfl⟩ : syracuseStep 6614297 = 4960723) B4960723
theorem B28249411 : Blo 1305971 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B7949677 : Blo 1305971 7949677 := bstep (se 3 (by rfl) ⟨1490564, by rfl⟩ : syracuseStep 7949677 = 2981129) B2981129
theorem B1305983 : Blo 1305971 1305983 := bstep (se 1 (by rfl) ⟨979487, by rfl⟩ : syracuseStep 1305983 = 1958975) B1958975
theorem B1306011 : Blo 1305971 1306011 := bstep (se 1 (by rfl) ⟨979508, by rfl⟩ : syracuseStep 1306011 = 1959017) B1959017
theorem B1306079 : Blo 1305971 1306079 := bstep (se 1 (by rfl) ⟨979559, by rfl⟩ : syracuseStep 1306079 = 1959119) B1959119
theorem B2092511 : Blo 1305971 2092511 := bstep (se 1 (by rfl) ⟨1569383, by rfl⟩ : syracuseStep 2092511 = 3138767) B3138767
theorem B4959751 : Blo 1305971 4959751 := bstep (se 1 (by rfl) ⟨3719813, by rfl⟩ : syracuseStep 4959751 = 7439627) B7439627
theorem B23244347 : Blo 1305971 23244347 := bstep (se 1 (by rfl) ⟨17433260, by rfl⟩ : syracuseStep 23244347 = 34866521) B34866521
theorem B1961543 : Blo 1305971 1961543 := bstep (se 1 (by rfl) ⟨1471157, by rfl⟩ : syracuseStep 1961543 = 2942315) B2942315
theorem B1306215 : Blo 1305971 1306215 := bstep (se 1 (by rfl) ⟨979661, by rfl⟩ : syracuseStep 1306215 = 1959323) B1959323
theorem B1470055 : Blo 1305971 1470055 := bstep (se 1 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 1470055 = 2205083) B2205083
theorem B1306363 : Blo 1305971 1306363 := bstep (se 1 (by rfl) ⟨979772, by rfl⟩ : syracuseStep 1306363 = 1959545) B1959545
theorem B1961723 : Blo 1305971 1961723 := bstep (se 1 (by rfl) ⟨1471292, by rfl⟩ : syracuseStep 1961723 = 2942585) B2942585
theorem B8376119 : Blo 1305971 8376119 := bstep (se 1 (by rfl) ⟨6282089, by rfl⟩ : syracuseStep 8376119 = 12564179) B12564179
theorem B1306431 : Blo 1305971 1306431 := bstep (se 1 (by rfl) ⟨979823, by rfl⟩ : syracuseStep 1306431 = 1959647) B1959647
theorem B1470271 : Blo 1305971 1470271 := bstep (se 1 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 1470271 = 2205407) B2205407
theorem B1306495 : Blo 1305971 1306495 := bstep (se 1 (by rfl) ⟨979871, by rfl⟩ : syracuseStep 1306495 = 1959743) B1959743
theorem B4411367 : Blo 1305971 4411367 := bstep (se 1 (by rfl) ⟨3308525, by rfl⟩ : syracuseStep 4411367 = 6617051) B6617051
theorem B4960237 : Blo 1305971 4960237 := bstep (se 3 (by rfl) ⟨930044, by rfl⟩ : syracuseStep 4960237 = 1860089) B1860089
theorem B1306607 : Blo 1305971 1306607 := bstep (se 1 (by rfl) ⟨979955, by rfl⟩ : syracuseStep 1306607 = 1959911) B1959911
theorem B1306619 : Blo 1305971 1306619 := bstep (se 1 (by rfl) ⟨979964, by rfl⟩ : syracuseStep 1306619 = 1959929) B1959929
theorem B1306687 : Blo 1305971 1306687 := bstep (se 1 (by rfl) ⟨980015, by rfl⟩ : syracuseStep 1306687 = 1960031) B1960031
theorem B1470559 : Blo 1305971 1470559 := bstep (se 1 (by rfl) ⟨1102919, by rfl⟩ : syracuseStep 1470559 = 2205839) B2205839
theorem B1306727 : Blo 1305971 1306727 := bstep (se 1 (by rfl) ⟨980045, by rfl⟩ : syracuseStep 1306727 = 1960091) B1960091
theorem B1306751 : Blo 1305971 1306751 := bstep (se 1 (by rfl) ⟨980063, by rfl⟩ : syracuseStep 1306751 = 1960127) B1960127
theorem B1306779 : Blo 1305971 1306779 := bstep (se 1 (by rfl) ⟨980084, by rfl⟩ : syracuseStep 1306779 = 1960169) B1960169
theorem B8376605 : Blo 1305971 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B4411745 : Blo 1305971 4411745 := bstep (se 2 (by rfl) ⟨1654404, by rfl⟩ : syracuseStep 4411745 = 3308809) B3308809
theorem B1306983 : Blo 1305971 1306983 := bstep (se 1 (by rfl) ⟨980237, by rfl⟩ : syracuseStep 1306983 = 1960475) B1960475
theorem B1307035 : Blo 1305971 1307035 := bstep (se 1 (by rfl) ⟨980276, by rfl⟩ : syracuseStep 1307035 = 1960553) B1960553
theorem B1569335 : Blo 1305971 1569335 := bstep (se 1 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 1569335 = 2354003) B2354003
theorem B71529101 : Blo 1305971 71529101 := bstep (se 3 (by rfl) ⟨13411706, by rfl⟩ : syracuseStep 71529101 = 26823413) B26823413
theorem B20124409 : Blo 1305971 20124409 := bstep (se 2 (by rfl) ⟨7546653, by rfl⟩ : syracuseStep 20124409 = 15093307) B15093307
theorem B1307387 : Blo 1305971 1307387 := bstep (se 1 (by rfl) ⟨980540, by rfl⟩ : syracuseStep 1307387 = 1961081) B1961081
theorem B3724051 : Blo 1305971 3724051 := bstep (se 1 (by rfl) ⟨2793038, by rfl⟩ : syracuseStep 3724051 = 5586077) B5586077
theorem B1307455 : Blo 1305971 1307455 := bstep (se 1 (by rfl) ⟨980591, by rfl⟩ : syracuseStep 1307455 = 1961183) B1961183
theorem B1307483 : Blo 1305971 1307483 := bstep (se 1 (by rfl) ⟨980612, by rfl⟩ : syracuseStep 1307483 = 1961225) B1961225
theorem B1766281 : Blo 1305971 1766281 := bstep (se 2 (by rfl) ⟨662355, by rfl⟩ : syracuseStep 1766281 = 1324711) B1324711
theorem B1307551 : Blo 1305971 1307551 := bstep (se 1 (by rfl) ⟨980663, by rfl⟩ : syracuseStep 1307551 = 1961327) B1961327
theorem B1307631 : Blo 1305971 1307631 := bstep (se 1 (by rfl) ⟨980723, by rfl⟩ : syracuseStep 1307631 = 1961447) B1961447
theorem B1307719 : Blo 1305971 1307719 := bstep (se 1 (by rfl) ⟨980789, by rfl⟩ : syracuseStep 1307719 = 1961579) B1961579
theorem B1307803 : Blo 1305971 1307803 := bstep (se 1 (by rfl) ⟨980852, by rfl⟩ : syracuseStep 1307803 = 1961705) B1961705
theorem B1307899 : Blo 1305971 1307899 := bstep (se 1 (by rfl) ⟨980924, by rfl⟩ : syracuseStep 1307899 = 1961849) B1961849
theorem B3306815 : Blo 1305971 3306815 := bstep (se 1 (by rfl) ⟨2480111, by rfl⟩ : syracuseStep 3306815 = 4960223) B4960223
theorem B1307967 : Blo 1305971 1307967 := bstep (se 1 (by rfl) ⟨980975, by rfl⟩ : syracuseStep 1307967 = 1961951) B1961951
theorem B2790767 : Blo 1305971 2790767 := bstep (se 1 (by rfl) ⟨2093075, by rfl⟩ : syracuseStep 2790767 = 4186151) B4186151
theorem B42407333 : Blo 1305971 42407333 := bstep (se 4 (by rfl) ⟨3975687, by rfl⟩ : syracuseStep 42407333 = 7951375) B7951375
theorem B3307027 : Blo 1305971 3307027 := bstep (se 1 (by rfl) ⟨2480270, by rfl⟩ : syracuseStep 3307027 = 4960541) B4960541
theorem B1988233 : Blo 1305971 1988233 := bstep (se 2 (by rfl) ⟨745587, by rfl⟩ : syracuseStep 1988233 = 1491175) B1491175
theorem B2938535 : Blo 1305971 2938535 := bstep (se 1 (by rfl) ⟨2203901, by rfl⟩ : syracuseStep 2938535 = 4407803) B4407803
theorem B4413095 : Blo 1305971 4413095 := bstep (se 1 (by rfl) ⟨3309821, by rfl⟩ : syracuseStep 4413095 = 6619643) B6619643
theorem B18847475 : Blo 1305971 18847475 := bstep (se 1 (by rfl) ⟨14135606, by rfl⟩ : syracuseStep 18847475 = 28271213) B28271213
theorem B2938715 : Blo 1305971 2938715 := bstep (se 1 (by rfl) ⟨2204036, by rfl⟩ : syracuseStep 2938715 = 4408073) B4408073
theorem B1415071 : Blo 1305971 1415071 := bstep (se 1 (by rfl) ⟨1061303, by rfl⟩ : syracuseStep 1415071 = 2122607) B2122607
theorem B3307463 : Blo 1305971 3307463 := bstep (se 1 (by rfl) ⟨2480597, by rfl⟩ : syracuseStep 3307463 = 4961195) B4961195
theorem B6281185 : Blo 1305971 6281185 := bstep (se 2 (by rfl) ⟨2355444, by rfl⟩ : syracuseStep 6281185 = 4710889) B4710889
theorem B12564521 : Blo 1305971 12564521 := bstep (se 2 (by rfl) ⟨4711695, by rfl⟩ : syracuseStep 12564521 = 9423391) B9423391
theorem B5585051 : Blo 1305971 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B2939219 : Blo 1305971 2939219 := bstep (se 1 (by rfl) ⟨2204414, by rfl⟩ : syracuseStep 2939219 = 4408829) B4408829
theorem B4962667 : Blo 1305971 4962667 := bstep (se 1 (by rfl) ⟨3722000, by rfl⟩ : syracuseStep 4962667 = 7444001) B7444001
theorem B40794553 : Blo 1305971 40794553 := bstep (se 2 (by rfl) ⟨15297957, by rfl⟩ : syracuseStep 40794553 = 30595915) B30595915
theorem B11172289 : Blo 1305971 11172289 := bstep (se 2 (by rfl) ⟨4189608, by rfl⟩ : syracuseStep 11172289 = 8379217) B8379217
theorem B3308161 : Blo 1305971 3308161 := bstep (se 2 (by rfl) ⟨1240560, by rfl⟩ : syracuseStep 3308161 = 2481121) B2481121
theorem B2939705 : Blo 1305971 2939705 := bstep (se 2 (by rfl) ⟨1102389, by rfl⟩ : syracuseStep 2939705 = 2204779) B2204779
theorem B11164499 : Blo 1305971 11164499 := bstep (se 1 (by rfl) ⟨8373374, by rfl⟩ : syracuseStep 11164499 = 16746749) B16746749
theorem B2939759 : Blo 1305971 2939759 := bstep (se 1 (by rfl) ⟨2204819, by rfl⟩ : syracuseStep 2939759 = 4409639) B4409639
theorem B3308971 : Blo 1305971 3308971 := bstep (se 1 (by rfl) ⟨2481728, by rfl⟩ : syracuseStep 3308971 = 4963457) B4963457
theorem B3972527 : Blo 1305971 3972527 := bstep (se 1 (by rfl) ⟨2979395, by rfl⟩ : syracuseStep 3972527 = 5958791) B5958791
theorem B2940335 : Blo 1305971 2940335 := bstep (se 1 (by rfl) ⟨2205251, by rfl⟩ : syracuseStep 2940335 = 4410503) B4410503
theorem B2940407 : Blo 1305971 2940407 := bstep (se 1 (by rfl) ⟨2205305, by rfl⟩ : syracuseStep 2940407 = 4410611) B4410611
theorem B5299879 : Blo 1305971 5299879 := bstep (se 1 (by rfl) ⟨3974909, by rfl⟩ : syracuseStep 5299879 = 7949819) B7949819
theorem B2793449 : Blo 1305971 2793449 := bstep (se 2 (by rfl) ⟨1047543, by rfl⟩ : syracuseStep 2793449 = 2095087) B2095087
theorem B2941163 : Blo 1305971 2941163 := bstep (se 1 (by rfl) ⟨2205872, by rfl⟩ : syracuseStep 2941163 = 4411745) B4411745
theorem B11469113 : Blo 1305971 11469113 := bstep (se 2 (by rfl) ⟨4300917, by rfl⟩ : syracuseStep 11469113 = 8601835) B8601835
theorem B14893469 : Blo 1305971 14893469 := bstep (se 3 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 14893469 = 5585051) B5585051
theorem B47686067 : Blo 1305971 47686067 := bstep (se 1 (by rfl) ⟨35764550, by rfl⟩ : syracuseStep 47686067 = 71529101) B71529101
theorem B98075063 : Blo 1305971 98075063 := bstep (se 1 (by rfl) ⟨73556297, by rfl⟩ : syracuseStep 98075063 = 147112595) B147112595
theorem B3310247 : Blo 1305971 3310247 := bstep (se 1 (by rfl) ⟨2482685, by rfl⟩ : syracuseStep 3310247 = 4965371) B4965371
theorem B2204543 : Blo 1305971 2204543 := bstep (se 1 (by rfl) ⟨1653407, by rfl⟩ : syracuseStep 2204543 = 3306815) B3306815
theorem B1860511 : Blo 1305971 1860511 := bstep (se 1 (by rfl) ⟨1395383, by rfl⟩ : syracuseStep 1860511 = 2790767) B2790767
theorem B28271555 : Blo 1305971 28271555 := bstep (se 1 (by rfl) ⟨21203666, by rfl⟩ : syracuseStep 28271555 = 42407333) B42407333
theorem B2982863 : Blo 1305971 2982863 := bstep (se 1 (by rfl) ⟨2237147, by rfl⟩ : syracuseStep 2982863 = 4474295) B4474295
theorem B4965401 : Blo 1305971 4965401 := bstep (se 2 (by rfl) ⟨1862025, by rfl⟩ : syracuseStep 4965401 = 3724051) B3724051
theorem B1959023 : Blo 1305971 1959023 := bstep (se 1 (by rfl) ⟨1469267, by rfl⟩ : syracuseStep 1959023 = 2938535) B2938535
theorem B2942063 : Blo 1305971 2942063 := bstep (se 1 (by rfl) ⟨2206547, by rfl⟩ : syracuseStep 2942063 = 4413095) B4413095
theorem B3310703 : Blo 1305971 3310703 := bstep (se 1 (by rfl) ⟨2483027, by rfl⟩ : syracuseStep 3310703 = 4966055) B4966055
theorem B8373455 : Blo 1305971 8373455 := bstep (se 1 (by rfl) ⟨6280091, by rfl⟩ : syracuseStep 8373455 = 12560183) B12560183
theorem B4965583 : Blo 1305971 4965583 := bstep (se 1 (by rfl) ⟨3724187, by rfl⟩ : syracuseStep 4965583 = 7448375) B7448375
theorem B1959143 : Blo 1305971 1959143 := bstep (se 1 (by rfl) ⟨1469357, by rfl⟩ : syracuseStep 1959143 = 2938715) B2938715
theorem B5580029 : Blo 1305971 5580029 := bstep (se 3 (by rfl) ⟨1046255, by rfl⟩ : syracuseStep 5580029 = 2092511) B2092511
theorem B1959209 : Blo 1305971 1959209 := bstep (se 2 (by rfl) ⟨734703, by rfl⟩ : syracuseStep 1959209 = 1469407) B1469407
theorem B2204975 : Blo 1305971 2204975 := bstep (se 1 (by rfl) ⟨1653731, by rfl⟩ : syracuseStep 2204975 = 3307463) B3307463
theorem B12567869 : Blo 1305971 12567869 := bstep (se 3 (by rfl) ⟨2356475, by rfl⟩ : syracuseStep 12567869 = 4712951) B4712951
theorem B6612353 : Blo 1305971 6612353 := bstep (se 2 (by rfl) ⟨2479632, by rfl⟩ : syracuseStep 6612353 = 4959265) B4959265
theorem B1959479 : Blo 1305971 1959479 := bstep (se 1 (by rfl) ⟨1469609, by rfl⟩ : syracuseStep 1959479 = 2939219) B2939219
theorem B1959803 : Blo 1305971 1959803 := bstep (se 1 (by rfl) ⟨1469852, by rfl⟩ : syracuseStep 1959803 = 2939705) B2939705
theorem B1959839 : Blo 1305971 1959839 := bstep (se 1 (by rfl) ⟨1469879, by rfl⟩ : syracuseStep 1959839 = 2939759) B2939759
theorem B6613001 : Blo 1305971 6613001 := bstep (se 2 (by rfl) ⟨2479875, by rfl⟩ : syracuseStep 6613001 = 4959751) B4959751
theorem B4409369 : Blo 1305971 4409369 := bstep (se 2 (by rfl) ⟨1653513, by rfl⟩ : syracuseStep 4409369 = 3307027) B3307027
theorem B1960073 : Blo 1305971 1960073 := bstep (se 2 (by rfl) ⟨735027, by rfl⟩ : syracuseStep 1960073 = 1470055) B1470055
theorem B10602679 : Blo 1305971 10602679 := bstep (se 1 (by rfl) ⟨7952009, by rfl⟩ : syracuseStep 10602679 = 15904019) B15904019
theorem B4409531 : Blo 1305971 4409531 := bstep (se 1 (by rfl) ⟨3307148, by rfl⟩ : syracuseStep 4409531 = 6614297) B6614297
theorem B2648351 : Blo 1305971 2648351 := bstep (se 1 (by rfl) ⟨1986263, by rfl⟩ : syracuseStep 2648351 = 3972527) B3972527
theorem B1960223 : Blo 1305971 1960223 := bstep (se 1 (by rfl) ⟨1470167, by rfl⟩ : syracuseStep 1960223 = 2940335) B2940335
theorem B1960271 : Blo 1305971 1960271 := bstep (se 1 (by rfl) ⟨1470203, by rfl⟩ : syracuseStep 1960271 = 2940407) B2940407
theorem B1960361 : Blo 1305971 1960361 := bstep (se 2 (by rfl) ⟨735135, by rfl⟩ : syracuseStep 1960361 = 1470271) B1470271
theorem B1886761 : Blo 1305971 1886761 := bstep (se 2 (by rfl) ⟨707535, by rfl⟩ : syracuseStep 1886761 = 1415071) B1415071
theorem B8374913 : Blo 1305971 8374913 := bstep (se 2 (by rfl) ⟨3140592, by rfl⟩ : syracuseStep 8374913 = 6281185) B6281185
theorem B6613649 : Blo 1305971 6613649 := bstep (se 2 (by rfl) ⟨2480118, by rfl⟩ : syracuseStep 6613649 = 4960237) B4960237
theorem B1862299 : Blo 1305971 1862299 := bstep (se 1 (by rfl) ⟨1396724, by rfl⟩ : syracuseStep 1862299 = 2793449) B2793449
theorem B1960745 : Blo 1305971 1960745 := bstep (se 2 (by rfl) ⟨735279, by rfl⟩ : syracuseStep 1960745 = 1470559) B1470559
theorem B1960955 : Blo 1305971 1960955 := bstep (se 1 (by rfl) ⟨1470716, by rfl⟩ : syracuseStep 1960955 = 2941433) B2941433
theorem B1961015 : Blo 1305971 1961015 := bstep (se 1 (by rfl) ⟨1470761, by rfl⟩ : syracuseStep 1961015 = 2941523) B2941523
theorem B1469551 : Blo 1305971 1469551 := bstep (se 1 (by rfl) ⟨1102163, by rfl⟩ : syracuseStep 1469551 = 2204327) B2204327
theorem B3722365 : Blo 1305971 3722365 := bstep (se 3 (by rfl) ⟨697943, by rfl⟩ : syracuseStep 3722365 = 1395887) B1395887
theorem B1961135 : Blo 1305971 1961135 := bstep (se 1 (by rfl) ⟨1470851, by rfl⟩ : syracuseStep 1961135 = 2941703) B2941703
theorem B1961195 : Blo 1305971 1961195 := bstep (se 1 (by rfl) ⟨1470896, by rfl⟩ : syracuseStep 1961195 = 2941793) B2941793
theorem B14896385 : Blo 1305971 14896385 := bstep (se 2 (by rfl) ⟨5586144, by rfl⟩ : syracuseStep 14896385 = 11172289) B11172289
theorem B1469767 : Blo 1305971 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B4959569 : Blo 1305971 4959569 := bstep (se 2 (by rfl) ⟨1859838, by rfl⟩ : syracuseStep 4959569 = 3719677) B3719677
theorem B10603909 : Blo 1305971 10603909 := bstep (se 4 (by rfl) ⟨994116, by rfl⟩ : syracuseStep 10603909 = 1988233) B1988233
theorem B4410881 : Blo 1305971 4410881 := bstep (se 2 (by rfl) ⟨1654080, by rfl⟩ : syracuseStep 4410881 = 3308161) B3308161
theorem B26832545 : Blo 1305971 26832545 := bstep (se 2 (by rfl) ⟨10062204, by rfl⟩ : syracuseStep 26832545 = 20124409) B20124409
theorem B160960193 : Blo 1305971 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B2355041 : Blo 1305971 2355041 := bstep (se 2 (by rfl) ⟨883140, by rfl⟩ : syracuseStep 2355041 = 1766281) B1766281
theorem B1961855 : Blo 1305971 1961855 := bstep (se 1 (by rfl) ⟨1471391, by rfl⟩ : syracuseStep 1961855 = 2942783) B2942783
theorem B8376347 : Blo 1305971 8376347 := bstep (se 1 (by rfl) ⟨6282260, by rfl⟩ : syracuseStep 8376347 = 12564521) B12564521
theorem B1306655 : Blo 1305971 1306655 := bstep (se 1 (by rfl) ⟨979991, by rfl⟩ : syracuseStep 1306655 = 1959983) B1959983
theorem B1765471 : Blo 1305971 1765471 := bstep (se 1 (by rfl) ⟨1324103, by rfl⟩ : syracuseStep 1765471 = 2648207) B2648207
theorem B61984925 : Blo 1305971 61984925 := bstep (se 3 (by rfl) ⟨11622173, by rfl⟩ : syracuseStep 61984925 = 23244347) B23244347
theorem B1306831 : Blo 1305971 1306831 := bstep (se 1 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 1306831 = 1960247) B1960247
theorem B4960511 : Blo 1305971 4960511 := bstep (se 1 (by rfl) ⟨3720383, by rfl⟩ : syracuseStep 4960511 = 7440767) B7440767
theorem B1306951 : Blo 1305971 1306951 := bstep (se 1 (by rfl) ⟨980213, by rfl⟩ : syracuseStep 1306951 = 1960427) B1960427
theorem B7442999 : Blo 1305971 7442999 := bstep (se 1 (by rfl) ⟨5582249, by rfl⟩ : syracuseStep 7442999 = 11164499) B11164499
theorem B4411961 : Blo 1305971 4411961 := bstep (se 2 (by rfl) ⟨1654485, by rfl⟩ : syracuseStep 4411961 = 3308971) B3308971
theorem B15905483 : Blo 1305971 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B1307419 : Blo 1305971 1307419 := bstep (se 1 (by rfl) ⟨980564, by rfl⟩ : syracuseStep 1307419 = 1961129) B1961129
theorem B7066505 : Blo 1305971 7066505 := bstep (se 2 (by rfl) ⟨2649939, by rfl⟩ : syracuseStep 7066505 = 5299879) B5299879
theorem B1307695 : Blo 1305971 1307695 := bstep (se 1 (by rfl) ⟨980771, by rfl⟩ : syracuseStep 1307695 = 1961543) B1961543
theorem B1307815 : Blo 1305971 1307815 := bstep (se 1 (by rfl) ⟨980861, by rfl⟩ : syracuseStep 1307815 = 1961723) B1961723
theorem B5584079 : Blo 1305971 5584079 := bstep (se 1 (by rfl) ⟨4188059, by rfl⟩ : syracuseStep 5584079 = 8376119) B8376119
theorem B5584403 : Blo 1305971 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B14890553 : Blo 1305971 14890553 := bstep (se 2 (by rfl) ⟨5583957, by rfl⟩ : syracuseStep 14890553 = 11167915) B11167915
theorem B2938607 : Blo 1305971 2938607 := bstep (se 1 (by rfl) ⟨2203955, by rfl⟩ : syracuseStep 2938607 = 4407911) B4407911
theorem B6616889 : Blo 1305971 6616889 := bstep (se 2 (by rfl) ⟨2481333, by rfl⟩ : syracuseStep 6616889 = 4962667) B4962667
theorem B54392737 : Blo 1305971 54392737 := bstep (se 2 (by rfl) ⟨20397276, by rfl⟩ : syracuseStep 54392737 = 40794553) B40794553
theorem B8378603 : Blo 1305971 8378603 := bstep (se 1 (by rfl) ⟨6283952, by rfl⟩ : syracuseStep 8378603 = 12567905) B12567905
theorem B26810615 : Blo 1305971 26810615 := bstep (se 1 (by rfl) ⟨20107961, by rfl⟩ : syracuseStep 26810615 = 40215923) B40215923
theorem B12564983 : Blo 1305971 12564983 := bstep (se 1 (by rfl) ⟨9423737, by rfl⟩ : syracuseStep 12564983 = 18847475) B18847475
theorem B4413959 : Blo 1305971 4413959 := bstep (se 1 (by rfl) ⟨3310469, by rfl⟩ : syracuseStep 4413959 = 6620939) B6620939
theorem B9181723 : Blo 1305971 9181723 := bstep (se 1 (by rfl) ⟨6886292, by rfl⟩ : syracuseStep 9181723 = 13772585) B13772585
theorem B3775211 : Blo 1305971 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B4184893 : Blo 1305971 4184893 := bstep (se 3 (by rfl) ⟨784667, by rfl⟩ : syracuseStep 4184893 = 1569335) B1569335
theorem B15080413 : Blo 1305971 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B37665881 : Blo 1305971 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B7953497 : Blo 1305971 7953497 := bstep (se 2 (by rfl) ⟨2982561, by rfl⟩ : syracuseStep 7953497 = 5965123) B5965123
theorem B2940011 : Blo 1305971 2940011 := bstep (se 1 (by rfl) ⟨2205008, by rfl⟩ : syracuseStep 2940011 = 4410017) B4410017
theorem B10599569 : Blo 1305971 10599569 := bstep (se 2 (by rfl) ⟨3974838, by rfl⟩ : syracuseStep 10599569 = 7949677) B7949677
theorem B2940155 : Blo 1305971 2940155 := bstep (se 1 (by rfl) ⟨2205116, by rfl⟩ : syracuseStep 2940155 = 4410233) B4410233
theorem B2940281 : Blo 1305971 2940281 := bstep (se 2 (by rfl) ⟨1102605, by rfl⟩ : syracuseStep 2940281 = 2205211) B2205211
theorem B2940911 : Blo 1305971 2940911 := bstep (se 1 (by rfl) ⟨2205683, by rfl⟩ : syracuseStep 2940911 = 4411367) B4411367
theorem B9928979 : Blo 1305971 9928979 := bstep (se 1 (by rfl) ⟨7446734, by rfl⟩ : syracuseStep 9928979 = 14893469) B14893469
theorem B2941307 : Blo 1305971 2941307 := bstep (se 1 (by rfl) ⟨2205980, by rfl⟩ : syracuseStep 2941307 = 4411961) B4411961
theorem B4711003 : Blo 1305971 4711003 := bstep (se 1 (by rfl) ⟨3533252, by rfl⟩ : syracuseStep 4711003 = 7066505) B7066505
theorem B3310267 : Blo 1305971 3310267 := bstep (se 1 (by rfl) ⟨2482700, by rfl⟩ : syracuseStep 3310267 = 4965401) B4965401
theorem B2515681 : Blo 1305971 2515681 := bstep (se 2 (by rfl) ⟨943380, by rfl⟩ : syracuseStep 2515681 = 1886761) B1886761
theorem B3720019 : Blo 1305971 3720019 := bstep (se 1 (by rfl) ⟨2790014, by rfl⟩ : syracuseStep 3720019 = 5580029) B5580029
theorem B2483065 : Blo 1305971 2483065 := bstep (se 2 (by rfl) ⟨931149, by rfl⟩ : syracuseStep 2483065 = 1862299) B1862299
theorem B4408235 : Blo 1305971 4408235 := bstep (se 1 (by rfl) ⟨3306176, by rfl⟩ : syracuseStep 4408235 = 6612353) B6612353
theorem B5579857 : Blo 1305971 5579857 := bstep (se 2 (by rfl) ⟨2092446, by rfl⟩ : syracuseStep 5579857 = 4184893) B4184893
theorem B1959071 : Blo 1305971 1959071 := bstep (se 1 (by rfl) ⟨1469303, by rfl⟩ : syracuseStep 1959071 = 2938607) B2938607
theorem B4408667 : Blo 1305971 4408667 := bstep (se 1 (by rfl) ⟨3306500, by rfl⟩ : syracuseStep 4408667 = 6613001) B6613001
theorem B1959401 : Blo 1305971 1959401 := bstep (se 2 (by rfl) ⟨734775, by rfl⟩ : syracuseStep 1959401 = 1469551) B1469551
theorem B6620777 : Blo 1305971 6620777 := bstep (se 2 (by rfl) ⟨2482791, by rfl⟩ : syracuseStep 6620777 = 4965583) B4965583
theorem B2942639 : Blo 1305971 2942639 := bstep (se 1 (by rfl) ⟨2206979, by rfl⟩ : syracuseStep 2942639 = 4413959) B4413959
theorem B1959689 : Blo 1305971 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B4409099 : Blo 1305971 4409099 := bstep (se 1 (by rfl) ⟨3306824, by rfl⟩ : syracuseStep 4409099 = 6613649) B6613649
theorem B2516807 : Blo 1305971 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B25110587 : Blo 1305971 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B5302331 : Blo 1305971 5302331 := bstep (se 1 (by rfl) ⟨3976748, by rfl⟩ : syracuseStep 5302331 = 7953497) B7953497
theorem B1960007 : Blo 1305971 1960007 := bstep (se 1 (by rfl) ⟨1470005, by rfl⟩ : syracuseStep 1960007 = 2940011) B2940011
theorem B1960103 : Blo 1305971 1960103 := bstep (se 1 (by rfl) ⟨1470077, by rfl⟩ : syracuseStep 1960103 = 2940155) B2940155
theorem B9930923 : Blo 1305971 9930923 := bstep (se 1 (by rfl) ⟨7448192, by rfl⟩ : syracuseStep 9930923 = 14896385) B14896385
theorem B1960187 : Blo 1305971 1960187 := bstep (se 1 (by rfl) ⟨1470140, by rfl⟩ : syracuseStep 1960187 = 2940281) B2940281
theorem B1960607 : Blo 1305971 1960607 := bstep (se 1 (by rfl) ⟨1470455, by rfl⟩ : syracuseStep 1960607 = 2940911) B2940911
theorem B41323283 : Blo 1305971 41323283 := bstep (se 1 (by rfl) ⟨30992462, by rfl⟩ : syracuseStep 41323283 = 61984925) B61984925
theorem B2353961 : Blo 1305971 2353961 := bstep (se 2 (by rfl) ⟨882735, by rfl⟩ : syracuseStep 2353961 = 1765471) B1765471
theorem B1960775 : Blo 1305971 1960775 := bstep (se 1 (by rfl) ⟨1470581, by rfl⟩ : syracuseStep 1960775 = 2941163) B2941163
theorem B7646075 : Blo 1305971 7646075 := bstep (se 1 (by rfl) ⟨5734556, by rfl⟩ : syracuseStep 7646075 = 11469113) B11469113
theorem B2206831 : Blo 1305971 2206831 := bstep (se 1 (by rfl) ⟨1655123, by rfl⟩ : syracuseStep 2206831 = 3310247) B3310247
theorem B10603655 : Blo 1305971 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B1469695 : Blo 1305971 1469695 := bstep (se 1 (by rfl) ⟨1102271, by rfl⟩ : syracuseStep 1469695 = 2204543) B2204543
theorem B12242297 : Blo 1305971 12242297 := bstep (se 2 (by rfl) ⟨4590861, by rfl⟩ : syracuseStep 12242297 = 9181723) B9181723
theorem B1306015 : Blo 1305971 1306015 := bstep (se 1 (by rfl) ⟨979511, by rfl⟩ : syracuseStep 1306015 = 1959023) B1959023
theorem B1961375 : Blo 1305971 1961375 := bstep (se 1 (by rfl) ⟨1471031, by rfl⟩ : syracuseStep 1961375 = 2942063) B2942063
theorem B2207135 : Blo 1305971 2207135 := bstep (se 1 (by rfl) ⟨1655351, by rfl⟩ : syracuseStep 2207135 = 3310703) B3310703
theorem B5582303 : Blo 1305971 5582303 := bstep (se 1 (by rfl) ⟨4186727, by rfl⟩ : syracuseStep 5582303 = 8373455) B8373455
theorem B3722719 : Blo 1305971 3722719 := bstep (se 1 (by rfl) ⟨2792039, by rfl⟩ : syracuseStep 3722719 = 5584079) B5584079
theorem B1306095 : Blo 1305971 1306095 := bstep (se 1 (by rfl) ⟨979571, by rfl⟩ : syracuseStep 1306095 = 1959143) B1959143
theorem B1306139 : Blo 1305971 1306139 := bstep (se 1 (by rfl) ⟨979604, by rfl⟩ : syracuseStep 1306139 = 1959209) B1959209
theorem B1469983 : Blo 1305971 1469983 := bstep (se 1 (by rfl) ⟨1102487, by rfl⟩ : syracuseStep 1469983 = 2204975) B2204975
theorem B3722935 : Blo 1305971 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B1306319 : Blo 1305971 1306319 := bstep (se 1 (by rfl) ⟨979739, by rfl⟩ : syracuseStep 1306319 = 1959479) B1959479
theorem B261533501 : Blo 1305971 261533501 := bstep (se 3 (by rfl) ⟨49037531, by rfl⟩ : syracuseStep 261533501 = 98075063) B98075063
theorem B4411259 : Blo 1305971 4411259 := bstep (se 1 (by rfl) ⟨3308444, by rfl⟩ : syracuseStep 4411259 = 6616889) B6616889
theorem B1306535 : Blo 1305971 1306535 := bstep (se 1 (by rfl) ⟨979901, by rfl⟩ : syracuseStep 1306535 = 1959803) B1959803
theorem B1306559 : Blo 1305971 1306559 := bstep (se 1 (by rfl) ⟨979919, by rfl⟩ : syracuseStep 1306559 = 1959839) B1959839
theorem B20107217 : Blo 1305971 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B1306715 : Blo 1305971 1306715 := bstep (se 1 (by rfl) ⟨980036, by rfl⟩ : syracuseStep 1306715 = 1960073) B1960073
theorem B1765567 : Blo 1305971 1765567 := bstep (se 1 (by rfl) ⟨1324175, by rfl⟩ : syracuseStep 1765567 = 2648351) B2648351
theorem B1306815 : Blo 1305971 1306815 := bstep (se 1 (by rfl) ⟨980111, by rfl⟩ : syracuseStep 1306815 = 1960223) B1960223
theorem B1306847 : Blo 1305971 1306847 := bstep (se 1 (by rfl) ⟨980135, by rfl⟩ : syracuseStep 1306847 = 1960271) B1960271
theorem B1306907 : Blo 1305971 1306907 := bstep (se 1 (by rfl) ⟨980180, by rfl⟩ : syracuseStep 1306907 = 1960361) B1960361
theorem B8376655 : Blo 1305971 8376655 := bstep (se 1 (by rfl) ⟨6282491, by rfl⟩ : syracuseStep 8376655 = 12564983) B12564983
theorem B5583275 : Blo 1305971 5583275 := bstep (se 1 (by rfl) ⟨4187456, by rfl⟩ : syracuseStep 5583275 = 8374913) B8374913
theorem B1307163 : Blo 1305971 1307163 := bstep (se 1 (by rfl) ⟨980372, by rfl⟩ : syracuseStep 1307163 = 1960745) B1960745
theorem B1307303 : Blo 1305971 1307303 := bstep (se 1 (by rfl) ⟨980477, by rfl⟩ : syracuseStep 1307303 = 1960955) B1960955
theorem B1307343 : Blo 1305971 1307343 := bstep (se 1 (by rfl) ⟨980507, by rfl⟩ : syracuseStep 1307343 = 1961015) B1961015
theorem B7066379 : Blo 1305971 7066379 := bstep (se 1 (by rfl) ⟨5299784, by rfl⟩ : syracuseStep 7066379 = 10599569) B10599569
theorem B1307423 : Blo 1305971 1307423 := bstep (se 1 (by rfl) ⟨980567, by rfl⟩ : syracuseStep 1307423 = 1961135) B1961135
theorem B1307463 : Blo 1305971 1307463 := bstep (se 1 (by rfl) ⟨980597, by rfl⟩ : syracuseStep 1307463 = 1961195) B1961195
theorem B3306379 : Blo 1305971 3306379 := bstep (se 1 (by rfl) ⟨2479784, by rfl⟩ : syracuseStep 3306379 = 4959569) B4959569
theorem B17888363 : Blo 1305971 17888363 := bstep (se 1 (by rfl) ⟨13416272, by rfl⟩ : syracuseStep 17888363 = 26832545) B26832545
theorem B1570027 : Blo 1305971 1570027 := bstep (se 1 (by rfl) ⟨1177520, by rfl⟩ : syracuseStep 1570027 = 2355041) B2355041
theorem B1307903 : Blo 1305971 1307903 := bstep (se 1 (by rfl) ⟨980927, by rfl⟩ : syracuseStep 1307903 = 1961855) B1961855
theorem B5584231 : Blo 1305971 5584231 := bstep (se 1 (by rfl) ⟨4188173, by rfl⟩ : syracuseStep 5584231 = 8376347) B8376347
theorem B3307007 : Blo 1305971 3307007 := bstep (se 1 (by rfl) ⟨2480255, by rfl⟩ : syracuseStep 3307007 = 4960511) B4960511
theorem B14136905 : Blo 1305971 14136905 := bstep (se 2 (by rfl) ⟨5301339, by rfl⟩ : syracuseStep 14136905 = 10602679) B10602679
theorem B31790711 : Blo 1305971 31790711 := bstep (se 1 (by rfl) ⟨23843033, by rfl⟩ : syracuseStep 31790711 = 47686067) B47686067
theorem B4961999 : Blo 1305971 4961999 := bstep (se 1 (by rfl) ⟨3721499, by rfl⟩ : syracuseStep 4961999 = 7442999) B7442999
theorem B18847703 : Blo 1305971 18847703 := bstep (se 1 (by rfl) ⟨14135777, by rfl⟩ : syracuseStep 18847703 = 28271555) B28271555
theorem B8378579 : Blo 1305971 8378579 := bstep (se 1 (by rfl) ⟨6283934, by rfl⟩ : syracuseStep 8378579 = 12567869) B12567869
theorem B9927035 : Blo 1305971 9927035 := bstep (se 1 (by rfl) ⟨7445276, by rfl⟩ : syracuseStep 9927035 = 14890553) B14890553
theorem B2480681 : Blo 1305971 2480681 := bstep (se 2 (by rfl) ⟨930255, by rfl⟩ : syracuseStep 2480681 = 1860511) B1860511
theorem B2939579 : Blo 1305971 2939579 := bstep (se 1 (by rfl) ⟨2204684, by rfl⟩ : syracuseStep 2939579 = 4409369) B4409369
theorem B2939687 : Blo 1305971 2939687 := bstep (se 1 (by rfl) ⟨2204765, by rfl⟩ : syracuseStep 2939687 = 4409531) B4409531
theorem B5585735 : Blo 1305971 5585735 := bstep (se 1 (by rfl) ⟨4189301, by rfl⟩ : syracuseStep 5585735 = 8378603) B8378603
theorem B17873743 : Blo 1305971 17873743 := bstep (se 1 (by rfl) ⟨13405307, by rfl⟩ : syracuseStep 17873743 = 26810615) B26810615
theorem B4963153 : Blo 1305971 4963153 := bstep (se 2 (by rfl) ⟨1861182, by rfl⟩ : syracuseStep 4963153 = 3722365) B3722365
theorem B14138545 : Blo 1305971 14138545 := bstep (se 2 (by rfl) ⟨5301954, by rfl⟩ : syracuseStep 14138545 = 10603909) B10603909
theorem B2940587 : Blo 1305971 2940587 := bstep (se 1 (by rfl) ⟨2205440, by rfl⟩ : syracuseStep 2940587 = 4410881) B4410881
theorem B107306795 : Blo 1305971 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B7954301 : Blo 1305971 7954301 := bstep (se 3 (by rfl) ⟨1491431, by rfl⟩ : syracuseStep 7954301 = 2982863) B2982863
theorem B72523649 : Blo 1305971 72523649 := bstep (se 2 (by rfl) ⟨27196368, by rfl⟩ : syracuseStep 72523649 = 54392737) B54392737
theorem B6619319 : Blo 1305971 6619319 := bstep (se 1 (by rfl) ⟨4964489, by rfl⟩ : syracuseStep 6619319 = 9928979) B9928979
theorem B25125349 : Blo 1305971 25125349 := bstep (se 4 (by rfl) ⟨2355501, by rfl⟩ : syracuseStep 25125349 = 4711003) B4711003
theorem B4710919 : Blo 1305971 4710919 := bstep (se 1 (by rfl) ⟨3533189, by rfl⟩ : syracuseStep 4710919 = 7066379) B7066379
theorem B32646125 : Blo 1305971 32646125 := bstep (se 3 (by rfl) ⟨6121148, by rfl⟩ : syracuseStep 32646125 = 12242297) B12242297
theorem B2204671 : Blo 1305971 2204671 := bstep (se 1 (by rfl) ⟨1653503, by rfl⟩ : syracuseStep 2204671 = 3307007) B3307007
theorem B21193807 : Blo 1305971 21193807 := bstep (se 1 (by rfl) ⟨15895355, by rfl⟩ : syracuseStep 21193807 = 31790711) B31790711
theorem B23831657 : Blo 1305971 23831657 := bstep (se 2 (by rfl) ⟨8936871, by rfl⟩ : syracuseStep 23831657 = 17873743) B17873743
theorem B3310753 : Blo 1305971 3310753 := bstep (se 2 (by rfl) ⟨1241532, by rfl⟩ : syracuseStep 3310753 = 2483065) B2483065
theorem B4408505 : Blo 1305971 4408505 := bstep (se 2 (by rfl) ⟨1653189, by rfl⟩ : syracuseStep 4408505 = 3306379) B3306379
theorem B7439809 : Blo 1305971 7439809 := bstep (se 2 (by rfl) ⟨2789928, by rfl⟩ : syracuseStep 7439809 = 5579857) B5579857
theorem B6620615 : Blo 1305971 6620615 := bstep (se 1 (by rfl) ⟨4965461, by rfl⟩ : syracuseStep 6620615 = 9930923) B9930923
theorem B2942441 : Blo 1305971 2942441 := bstep (se 2 (by rfl) ⟨1103415, by rfl⟩ : syracuseStep 2942441 = 2206831) B2206831
theorem B18851393 : Blo 1305971 18851393 := bstep (se 2 (by rfl) ⟨7069272, by rfl⟩ : syracuseStep 18851393 = 14138545) B14138545
theorem B1959593 : Blo 1305971 1959593 := bstep (se 2 (by rfl) ⟨734847, by rfl⟩ : syracuseStep 1959593 = 1469695) B1469695
theorem B1959719 : Blo 1305971 1959719 := bstep (se 1 (by rfl) ⟨1469789, by rfl⟩ : syracuseStep 1959719 = 2939579) B2939579
theorem B1959791 : Blo 1305971 1959791 := bstep (se 1 (by rfl) ⟨1469843, by rfl⟩ : syracuseStep 1959791 = 2939687) B2939687
theorem B5097383 : Blo 1305971 5097383 := bstep (se 1 (by rfl) ⟨3823037, by rfl⟩ : syracuseStep 5097383 = 7646075) B7646075
theorem B1959977 : Blo 1305971 1959977 := bstep (se 2 (by rfl) ⟨734991, by rfl⟩ : syracuseStep 1959977 = 1469983) B1469983
theorem B3721535 : Blo 1305971 3721535 := bstep (se 1 (by rfl) ⟨2791151, by rfl⟩ : syracuseStep 3721535 = 5582303) B5582303
theorem B1960391 : Blo 1305971 1960391 := bstep (se 1 (by rfl) ⟨1470293, by rfl⟩ : syracuseStep 1960391 = 2940587) B2940587
theorem B5302867 : Blo 1305971 5302867 := bstep (se 1 (by rfl) ⟨3977150, by rfl⟩ : syracuseStep 5302867 = 7954301) B7954301
theorem B13404811 : Blo 1305971 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B1960871 : Blo 1305971 1960871 := bstep (se 1 (by rfl) ⟨1470653, by rfl⟩ : syracuseStep 1960871 = 2941307) B2941307
theorem B3722183 : Blo 1305971 3722183 := bstep (se 1 (by rfl) ⟨2791637, by rfl⟩ : syracuseStep 3722183 = 5583275) B5583275
theorem B11168873 : Blo 1305971 11168873 := bstep (se 2 (by rfl) ⟨4188327, by rfl⟩ : syracuseStep 11168873 = 8376655) B8376655
theorem B1306047 : Blo 1305971 1306047 := bstep (se 1 (by rfl) ⟨979535, by rfl⟩ : syracuseStep 1306047 = 1959071) B1959071
theorem B1306267 : Blo 1305971 1306267 := bstep (se 1 (by rfl) ⟨979700, by rfl⟩ : syracuseStep 1306267 = 1959401) B1959401
theorem B9416357 : Blo 1305971 9416357 := bstep (se 4 (by rfl) ⟨882783, by rfl⟩ : syracuseStep 9416357 = 1765567) B1765567
theorem B9424603 : Blo 1305971 9424603 := bstep (se 1 (by rfl) ⟨7068452, by rfl⟩ : syracuseStep 9424603 = 14136905) B14136905
theorem B4960025 : Blo 1305971 4960025 := bstep (se 2 (by rfl) ⟨1860009, by rfl⟩ : syracuseStep 4960025 = 3720019) B3720019
theorem B1961759 : Blo 1305971 1961759 := bstep (se 1 (by rfl) ⟨1471319, by rfl⟩ : syracuseStep 1961759 = 2942639) B2942639
theorem B1306459 : Blo 1305971 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B16740391 : Blo 1305971 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B3534887 : Blo 1305971 3534887 := bstep (se 1 (by rfl) ⟨2651165, by rfl⟩ : syracuseStep 3534887 = 5302331) B5302331
theorem B1306671 : Blo 1305971 1306671 := bstep (se 1 (by rfl) ⟨980003, by rfl⟩ : syracuseStep 1306671 = 1960007) B1960007
theorem B1306735 : Blo 1305971 1306735 := bstep (se 1 (by rfl) ⟨980051, by rfl⟩ : syracuseStep 1306735 = 1960103) B1960103
theorem B1306791 : Blo 1305971 1306791 := bstep (se 1 (by rfl) ⟨980093, by rfl⟩ : syracuseStep 1306791 = 1960187) B1960187
theorem B2093369 : Blo 1305971 2093369 := bstep (se 2 (by rfl) ⟨785013, by rfl⟩ : syracuseStep 2093369 = 1570027) B1570027
theorem B1307071 : Blo 1305971 1307071 := bstep (se 1 (by rfl) ⟨980303, by rfl⟩ : syracuseStep 1307071 = 1960607) B1960607
theorem B1569307 : Blo 1305971 1569307 := bstep (se 1 (by rfl) ⟨1176980, by rfl⟩ : syracuseStep 1569307 = 2353961) B2353961
theorem B1307183 : Blo 1305971 1307183 := bstep (se 1 (by rfl) ⟨980387, by rfl⟩ : syracuseStep 1307183 = 1960775) B1960775
theorem B3723823 : Blo 1305971 3723823 := bstep (se 1 (by rfl) ⟨2792867, by rfl⟩ : syracuseStep 3723823 = 5585735) B5585735
theorem B1307583 : Blo 1305971 1307583 := bstep (se 1 (by rfl) ⟨980687, by rfl⟩ : syracuseStep 1307583 = 1961375) B1961375
theorem B1471423 : Blo 1305971 1471423 := bstep (se 1 (by rfl) ⟨1103567, by rfl⟩ : syracuseStep 1471423 = 2207135) B2207135
theorem B71537863 : Blo 1305971 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B174355667 : Blo 1305971 174355667 := bstep (se 1 (by rfl) ⟨130766750, by rfl⟩ : syracuseStep 174355667 = 261533501) B261533501
theorem B2938823 : Blo 1305971 2938823 := bstep (se 1 (by rfl) ⟨2204117, by rfl⟩ : syracuseStep 2938823 = 4408235) B4408235
theorem B11925575 : Blo 1305971 11925575 := bstep (se 1 (by rfl) ⟨8944181, by rfl⟩ : syracuseStep 11925575 = 17888363) B17888363
theorem B2939111 : Blo 1305971 2939111 := bstep (se 1 (by rfl) ⟨2204333, by rfl⟩ : syracuseStep 2939111 = 4408667) B4408667
theorem B4413689 : Blo 1305971 4413689 := bstep (se 2 (by rfl) ⟨1655133, by rfl⟩ : syracuseStep 4413689 = 3310267) B3310267
theorem B4413851 : Blo 1305971 4413851 := bstep (se 1 (by rfl) ⟨3310388, by rfl⟩ : syracuseStep 4413851 = 6620777) B6620777
theorem B6617537 : Blo 1305971 6617537 := bstep (se 2 (by rfl) ⟨2481576, by rfl⟩ : syracuseStep 6617537 = 4963153) B4963153
theorem B3307999 : Blo 1305971 3307999 := bstep (se 1 (by rfl) ⟨2480999, by rfl⟩ : syracuseStep 3307999 = 4961999) B4961999
theorem B13416965 : Blo 1305971 13416965 := bstep (se 4 (by rfl) ⟨1257840, by rfl⟩ : syracuseStep 13416965 = 2515681) B2515681
theorem B2939399 : Blo 1305971 2939399 := bstep (se 1 (by rfl) ⟨2204549, by rfl⟩ : syracuseStep 2939399 = 4409099) B4409099
theorem B1677871 : Blo 1305971 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B12565135 : Blo 1305971 12565135 := bstep (se 1 (by rfl) ⟨9423851, by rfl⟩ : syracuseStep 12565135 = 18847703) B18847703
theorem B5585719 : Blo 1305971 5585719 := bstep (se 1 (by rfl) ⟨4189289, by rfl⟩ : syracuseStep 5585719 = 8378579) B8378579
theorem B6618023 : Blo 1305971 6618023 := bstep (se 1 (by rfl) ⟨4963517, by rfl⟩ : syracuseStep 6618023 = 9927035) B9927035
theorem B1653787 : Blo 1305971 1653787 := bstep (se 1 (by rfl) ⟨1240340, by rfl⟩ : syracuseStep 1653787 = 2480681) B2480681
theorem B7445641 : Blo 1305971 7445641 := bstep (se 2 (by rfl) ⟨2792115, by rfl⟩ : syracuseStep 7445641 = 5584231) B5584231
theorem B27548855 : Blo 1305971 27548855 := bstep (se 1 (by rfl) ⟨20661641, by rfl⟩ : syracuseStep 27548855 = 41323283) B41323283
theorem B4963625 : Blo 1305971 4963625 := bstep (se 2 (by rfl) ⟨1861359, by rfl⟩ : syracuseStep 4963625 = 3722719) B3722719
theorem B7069103 : Blo 1305971 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B4963913 : Blo 1305971 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B2940839 : Blo 1305971 2940839 := bstep (se 1 (by rfl) ⟨2205629, by rfl⟩ : syracuseStep 2940839 = 4411259) B4411259
theorem B48349099 : Blo 1305971 48349099 := bstep (se 1 (by rfl) ⟨36261824, by rfl⟩ : syracuseStep 48349099 = 72523649) B72523649
theorem B4965097 : Blo 1305971 4965097 := bstep (se 2 (by rfl) ⟨1861911, by rfl⟩ : syracuseStep 4965097 = 3723823) B3723823
theorem B2237161 : Blo 1305971 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B7070489 : Blo 1305971 7070489 := bstep (se 2 (by rfl) ⟨2651433, by rfl⟩ : syracuseStep 7070489 = 5302867) B5302867
theorem B116237111 : Blo 1305971 116237111 := bstep (se 1 (by rfl) ⟨87177833, by rfl⟩ : syracuseStep 116237111 = 174355667) B174355667
theorem B16753513 : Blo 1305971 16753513 := bstep (se 2 (by rfl) ⟨6282567, by rfl⟩ : syracuseStep 16753513 = 12565135) B12565135
theorem B7447625 : Blo 1305971 7447625 := bstep (se 2 (by rfl) ⟨2792859, by rfl⟩ : syracuseStep 7447625 = 5585719) B5585719
theorem B1959215 : Blo 1305971 1959215 := bstep (se 1 (by rfl) ⟨1469411, by rfl⟩ : syracuseStep 1959215 = 2938823) B2938823
theorem B2205049 : Blo 1305971 2205049 := bstep (se 2 (by rfl) ⟨826893, by rfl⟩ : syracuseStep 2205049 = 1653787) B1653787
theorem B1959407 : Blo 1305971 1959407 := bstep (se 1 (by rfl) ⟨1469555, by rfl⟩ : syracuseStep 1959407 = 2939111) B2939111
theorem B2942459 : Blo 1305971 2942459 := bstep (se 1 (by rfl) ⟨2206844, by rfl⟩ : syracuseStep 2942459 = 4413689) B4413689
theorem B2942567 : Blo 1305971 2942567 := bstep (se 1 (by rfl) ⟨2206925, by rfl⟩ : syracuseStep 2942567 = 4413851) B4413851
theorem B1959599 : Blo 1305971 1959599 := bstep (se 1 (by rfl) ⟨1469699, by rfl⟩ : syracuseStep 1959599 = 2939399) B2939399
theorem B4712735 : Blo 1305971 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B6277571 : Blo 1305971 6277571 := bstep (se 1 (by rfl) ⟨4708178, by rfl⟩ : syracuseStep 6277571 = 9416357) B9416357
theorem B64465465 : Blo 1305971 64465465 := bstep (se 2 (by rfl) ⟨24174549, by rfl⟩ : syracuseStep 64465465 = 48349099) B48349099
theorem B1960559 : Blo 1305971 1960559 := bstep (se 1 (by rfl) ⟨1470419, by rfl⟩ : syracuseStep 1960559 = 2940839) B2940839
theorem B4410665 : Blo 1305971 4410665 := bstep (se 2 (by rfl) ⟨1653999, by rfl⟩ : syracuseStep 4410665 = 3307999) B3307999
theorem B33500465 : Blo 1305971 33500465 := bstep (se 2 (by rfl) ⟨12562674, by rfl⟩ : syracuseStep 33500465 = 25125349) B25125349
theorem B2092409 : Blo 1305971 2092409 := bstep (se 2 (by rfl) ⟨784653, by rfl⟩ : syracuseStep 2092409 = 1569307) B1569307
theorem B15887771 : Blo 1305971 15887771 := bstep (se 1 (by rfl) ⟨11915828, by rfl⟩ : syracuseStep 15887771 = 23831657) B23831657
theorem B1961627 : Blo 1305971 1961627 := bstep (se 1 (by rfl) ⟨1471220, by rfl⟩ : syracuseStep 1961627 = 2942441) B2942441
theorem B1306395 : Blo 1305971 1306395 := bstep (se 1 (by rfl) ⟨979796, by rfl⟩ : syracuseStep 1306395 = 1959593) B1959593
theorem B1306479 : Blo 1305971 1306479 := bstep (se 1 (by rfl) ⟨979859, by rfl⟩ : syracuseStep 1306479 = 1959719) B1959719
theorem B1306527 : Blo 1305971 1306527 := bstep (se 1 (by rfl) ⟨979895, by rfl⟩ : syracuseStep 1306527 = 1959791) B1959791
theorem B1961897 : Blo 1305971 1961897 := bstep (se 2 (by rfl) ⟨735711, by rfl⟩ : syracuseStep 1961897 = 1471423) B1471423
theorem B1306651 : Blo 1305971 1306651 := bstep (se 1 (by rfl) ⟨979988, by rfl⟩ : syracuseStep 1306651 = 1959977) B1959977
theorem B7950383 : Blo 1305971 7950383 := bstep (se 1 (by rfl) ⟨5962787, by rfl⟩ : syracuseStep 7950383 = 11925575) B11925575
theorem B28258409 : Blo 1305971 28258409 := bstep (se 2 (by rfl) ⟨10596903, by rfl⟩ : syracuseStep 28258409 = 21193807) B21193807
theorem B50270381 : Blo 1305971 50270381 := bstep (se 3 (by rfl) ⟨9425696, by rfl⟩ : syracuseStep 50270381 = 18851393) B18851393
theorem B95383817 : Blo 1305971 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B4411691 : Blo 1305971 4411691 := bstep (se 1 (by rfl) ⟨3308768, by rfl⟩ : syracuseStep 4411691 = 6617537) B6617537
theorem B1306927 : Blo 1305971 1306927 := bstep (se 1 (by rfl) ⟨980195, by rfl⟩ : syracuseStep 1306927 = 1960391) B1960391
theorem B1307247 : Blo 1305971 1307247 := bstep (se 1 (by rfl) ⟨980435, by rfl⟩ : syracuseStep 1307247 = 1960871) B1960871
theorem B4412015 : Blo 1305971 4412015 := bstep (se 1 (by rfl) ⟨3309011, by rfl⟩ : syracuseStep 4412015 = 6618023) B6618023
theorem B3306683 : Blo 1305971 3306683 := bstep (se 1 (by rfl) ⟨2480012, by rfl⟩ : syracuseStep 3306683 = 4960025) B4960025
theorem B1307839 : Blo 1305971 1307839 := bstep (se 1 (by rfl) ⟨980879, by rfl⟩ : syracuseStep 1307839 = 1961759) B1961759
theorem B22320521 : Blo 1305971 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B9426365 : Blo 1305971 9426365 := bstep (se 3 (by rfl) ⟨1767443, by rfl⟩ : syracuseStep 9426365 = 3534887) B3534887
theorem B4412879 : Blo 1305971 4412879 := bstep (se 1 (by rfl) ⟨3309659, by rfl⟩ : syracuseStep 4412879 = 6619319) B6619319
theorem B22329269 : Blo 1305971 22329269 := bstep (se 5 (by rfl) ⟨1046684, by rfl⟩ : syracuseStep 22329269 = 2093369) B2093369
theorem B6281225 : Blo 1305971 6281225 := bstep (se 2 (by rfl) ⟨2355459, by rfl⟩ : syracuseStep 6281225 = 4710919) B4710919
theorem B2939003 : Blo 1305971 2939003 := bstep (se 1 (by rfl) ⟨2204252, by rfl⟩ : syracuseStep 2939003 = 4408505) B4408505
theorem B17873081 : Blo 1305971 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B4413743 : Blo 1305971 4413743 := bstep (se 1 (by rfl) ⟨3310307, by rfl⟩ : syracuseStep 4413743 = 6620615) B6620615
theorem B3398255 : Blo 1305971 3398255 := bstep (se 1 (by rfl) ⟨2548691, by rfl⟩ : syracuseStep 3398255 = 5097383) B5097383
theorem B2939561 : Blo 1305971 2939561 := bstep (se 2 (by rfl) ⟨1102335, by rfl⟩ : syracuseStep 2939561 = 2204671) B2204671
theorem B9927521 : Blo 1305971 9927521 := bstep (se 2 (by rfl) ⟨3722820, by rfl⟩ : syracuseStep 9927521 = 7445641) B7445641
theorem B2481023 : Blo 1305971 2481023 := bstep (se 1 (by rfl) ⟨1860767, by rfl⟩ : syracuseStep 2481023 = 3721535) B3721535
theorem B4414337 : Blo 1305971 4414337 := bstep (se 2 (by rfl) ⟨1655376, by rfl⟩ : syracuseStep 4414337 = 3310753) B3310753
theorem B8944643 : Blo 1305971 8944643 := bstep (se 1 (by rfl) ⟨6708482, by rfl⟩ : syracuseStep 8944643 = 13416965) B13416965
theorem B9919745 : Blo 1305971 9919745 := bstep (se 2 (by rfl) ⟨3719904, by rfl⟩ : syracuseStep 9919745 = 7439809) B7439809
theorem B2481455 : Blo 1305971 2481455 := bstep (se 1 (by rfl) ⟨1861091, by rfl⟩ : syracuseStep 2481455 = 3722183) B3722183
theorem B7445915 : Blo 1305971 7445915 := bstep (se 1 (by rfl) ⟨5584436, by rfl⟩ : syracuseStep 7445915 = 11168873) B11168873
theorem B18365903 : Blo 1305971 18365903 := bstep (se 1 (by rfl) ⟨13774427, by rfl⟩ : syracuseStep 18365903 = 27548855) B27548855
theorem B3309083 : Blo 1305971 3309083 := bstep (se 1 (by rfl) ⟨2481812, by rfl⟩ : syracuseStep 3309083 = 4963625) B4963625
theorem B12566137 : Blo 1305971 12566137 := bstep (se 2 (by rfl) ⟨4712301, by rfl⟩ : syracuseStep 12566137 = 9424603) B9424603
theorem B3309275 : Blo 1305971 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B87056333 : Blo 1305971 87056333 := bstep (se 3 (by rfl) ⟨16323062, by rfl⟩ : syracuseStep 87056333 = 32646125) B32646125
theorem B5300255 : Blo 1305971 5300255 := bstep (se 1 (by rfl) ⟨3975191, by rfl⟩ : syracuseStep 5300255 = 7950383) B7950383
theorem B33513587 : Blo 1305971 33513587 := bstep (se 1 (by rfl) ⟨25135190, by rfl⟩ : syracuseStep 33513587 = 50270381) B50270381
theorem B2941127 : Blo 1305971 2941127 := bstep (se 1 (by rfl) ⟨2205845, by rfl⟩ : syracuseStep 2941127 = 4411691) B4411691
theorem B2941343 : Blo 1305971 2941343 := bstep (se 1 (by rfl) ⟨2206007, by rfl⟩ : syracuseStep 2941343 = 4412015) B4412015
theorem B4965083 : Blo 1305971 4965083 := bstep (se 1 (by rfl) ⟨3723812, by rfl⟩ : syracuseStep 4965083 = 7447625) B7447625
theorem B2204455 : Blo 1305971 2204455 := bstep (se 1 (by rfl) ⟨1653341, by rfl⟩ : syracuseStep 2204455 = 3306683) B3306683
theorem B6284243 : Blo 1305971 6284243 := bstep (se 1 (by rfl) ⟨4713182, by rfl⟩ : syracuseStep 6284243 = 9426365) B9426365
theorem B2941919 : Blo 1305971 2941919 := bstep (se 1 (by rfl) ⟨2206439, by rfl⟩ : syracuseStep 2941919 = 4412879) B4412879
theorem B6620129 : Blo 1305971 6620129 := bstep (se 2 (by rfl) ⟨2482548, by rfl⟩ : syracuseStep 6620129 = 4965097) B4965097
theorem B2982881 : Blo 1305971 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B14886179 : Blo 1305971 14886179 := bstep (se 1 (by rfl) ⟨11164634, by rfl⟩ : syracuseStep 14886179 = 22329269) B22329269
theorem B4187483 : Blo 1305971 4187483 := bstep (se 1 (by rfl) ⟨3140612, by rfl⟩ : syracuseStep 4187483 = 6281225) B6281225
theorem B1959335 : Blo 1305971 1959335 := bstep (se 1 (by rfl) ⟨1469501, by rfl⟩ : syracuseStep 1959335 = 2939003) B2939003
theorem B2942495 : Blo 1305971 2942495 := bstep (se 1 (by rfl) ⟨2206871, by rfl⟩ : syracuseStep 2942495 = 4413743) B4413743
theorem B1959707 : Blo 1305971 1959707 := bstep (se 1 (by rfl) ⟨1469780, by rfl⟩ : syracuseStep 1959707 = 2939561) B2939561
theorem B2942891 : Blo 1305971 2942891 := bstep (se 1 (by rfl) ⟨2207168, by rfl⟩ : syracuseStep 2942891 = 4414337) B4414337
theorem B144992213 : Blo 1305971 144992213 := bstep (se 7 (by rfl) ⟨1699127, by rfl⟩ : syracuseStep 144992213 = 3398255) B3398255
theorem B16754849 : Blo 1305971 16754849 := bstep (se 2 (by rfl) ⟨6283068, by rfl⟩ : syracuseStep 16754849 = 12566137) B12566137
theorem B6613163 : Blo 1305971 6613163 := bstep (se 1 (by rfl) ⟨4959872, by rfl⟩ : syracuseStep 6613163 = 9919745) B9919745
theorem B22333643 : Blo 1305971 22333643 := bstep (se 1 (by rfl) ⟨16750232, by rfl⟩ : syracuseStep 22333643 = 33500465) B33500465
theorem B1394939 : Blo 1305971 1394939 := bstep (se 1 (by rfl) ⟨1046204, by rfl⟩ : syracuseStep 1394939 = 2092409) B2092409
theorem B2206055 : Blo 1305971 2206055 := bstep (se 1 (by rfl) ⟨1654541, by rfl⟩ : syracuseStep 2206055 = 3309083) B3309083
theorem B2206183 : Blo 1305971 2206183 := bstep (se 1 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 2206183 = 3309275) B3309275
theorem B63589211 : Blo 1305971 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B4713659 : Blo 1305971 4713659 := bstep (se 1 (by rfl) ⟨3535244, by rfl⟩ : syracuseStep 4713659 = 7070489) B7070489
theorem B85953953 : Blo 1305971 85953953 := bstep (se 2 (by rfl) ⟨32232732, by rfl⟩ : syracuseStep 85953953 = 64465465) B64465465
theorem B1306143 : Blo 1305971 1306143 := bstep (se 1 (by rfl) ⟨979607, by rfl⟩ : syracuseStep 1306143 = 1959215) B1959215
theorem B14880347 : Blo 1305971 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B1306271 : Blo 1305971 1306271 := bstep (se 1 (by rfl) ⟨979703, by rfl⟩ : syracuseStep 1306271 = 1959407) B1959407
theorem B1961639 : Blo 1305971 1961639 := bstep (se 1 (by rfl) ⟨1471229, by rfl⟩ : syracuseStep 1961639 = 2942459) B2942459
theorem B1961711 : Blo 1305971 1961711 := bstep (se 1 (by rfl) ⟨1471283, by rfl⟩ : syracuseStep 1961711 = 2942567) B2942567
theorem B1306399 : Blo 1305971 1306399 := bstep (se 1 (by rfl) ⟨979799, by rfl⟩ : syracuseStep 1306399 = 1959599) B1959599
theorem B11915387 : Blo 1305971 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B3141823 : Blo 1305971 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B1307039 : Blo 1305971 1307039 := bstep (se 1 (by rfl) ⟨980279, by rfl⟩ : syracuseStep 1307039 = 1960559) B1960559
theorem B309965629 : Blo 1305971 309965629 := bstep (se 3 (by rfl) ⟨58118555, by rfl⟩ : syracuseStep 309965629 = 116237111) B116237111
theorem B12243935 : Blo 1305971 12243935 := bstep (se 1 (by rfl) ⟨9182951, by rfl⟩ : syracuseStep 12243935 = 18365903) B18365903
theorem B1307751 : Blo 1305971 1307751 := bstep (se 1 (by rfl) ⟨980813, by rfl⟩ : syracuseStep 1307751 = 1961627) B1961627
theorem B1307931 : Blo 1305971 1307931 := bstep (se 1 (by rfl) ⟨980948, by rfl⟩ : syracuseStep 1307931 = 1961897) B1961897
theorem B58037555 : Blo 1305971 58037555 := bstep (se 1 (by rfl) ⟨43528166, by rfl⟩ : syracuseStep 58037555 = 87056333) B87056333
theorem B18838939 : Blo 1305971 18838939 := bstep (se 1 (by rfl) ⟨14129204, by rfl⟩ : syracuseStep 18838939 = 28258409) B28258409
theorem B6617213 : Blo 1305971 6617213 := bstep (se 3 (by rfl) ⟨1240727, by rfl⟩ : syracuseStep 6617213 = 2481455) B2481455
theorem B22338017 : Blo 1305971 22338017 := bstep (se 2 (by rfl) ⟨8376756, by rfl⟩ : syracuseStep 22338017 = 16753513) B16753513
theorem B4185047 : Blo 1305971 4185047 := bstep (se 1 (by rfl) ⟨3138785, by rfl⟩ : syracuseStep 4185047 = 6277571) B6277571
theorem B2940065 : Blo 1305971 2940065 := bstep (se 2 (by rfl) ⟨1102524, by rfl⟩ : syracuseStep 2940065 = 2205049) B2205049
theorem B6618347 : Blo 1305971 6618347 := bstep (se 1 (by rfl) ⟨4963760, by rfl⟩ : syracuseStep 6618347 = 9927521) B9927521
theorem B1654015 : Blo 1305971 1654015 := bstep (se 1 (by rfl) ⟨1240511, by rfl⟩ : syracuseStep 1654015 = 2481023) B2481023
theorem B5963095 : Blo 1305971 5963095 := bstep (se 1 (by rfl) ⟨4472321, by rfl⟩ : syracuseStep 5963095 = 8944643) B8944643
theorem B2940443 : Blo 1305971 2940443 := bstep (se 1 (by rfl) ⟨2205332, by rfl⟩ : syracuseStep 2940443 = 4410665) B4410665
theorem B10591847 : Blo 1305971 10591847 := bstep (se 1 (by rfl) ⟨7943885, by rfl⟩ : syracuseStep 10591847 = 15887771) B15887771
theorem B4963943 : Blo 1305971 4963943 := bstep (se 1 (by rfl) ⟨3722957, by rfl⟩ : syracuseStep 4963943 = 7445915) B7445915
theorem B3310055 : Blo 1305971 3310055 := bstep (se 1 (by rfl) ⟨2482541, by rfl⟩ : syracuseStep 3310055 = 4965083) B4965083
theorem B2941577 : Blo 1305971 2941577 := bstep (se 2 (by rfl) ⟨1103091, by rfl⟩ : syracuseStep 2941577 = 2206183) B2206183
theorem B3719837 : Blo 1305971 3719837 := bstep (se 3 (by rfl) ⟨697469, by rfl⟩ : syracuseStep 3719837 = 1394939) B1394939
theorem B38691703 : Blo 1305971 38691703 := bstep (se 1 (by rfl) ⟨29018777, by rfl⟩ : syracuseStep 38691703 = 58037555) B58037555
theorem B413287505 : Blo 1305971 413287505 := bstep (se 2 (by rfl) ⟨154982814, by rfl⟩ : syracuseStep 413287505 = 309965629) B309965629
theorem B4408775 : Blo 1305971 4408775 := bstep (se 1 (by rfl) ⟨3306581, by rfl⟩ : syracuseStep 4408775 = 6613163) B6613163
theorem B2205353 : Blo 1305971 2205353 := bstep (se 2 (by rfl) ⟨827007, by rfl⟩ : syracuseStep 2205353 = 1654015) B1654015
theorem B25118585 : Blo 1305971 25118585 := bstep (se 2 (by rfl) ⟨9419469, by rfl⟩ : syracuseStep 25118585 = 18838939) B18838939
theorem B1960043 : Blo 1305971 1960043 := bstep (se 1 (by rfl) ⟨1470032, by rfl⟩ : syracuseStep 1960043 = 2940065) B2940065
theorem B1960295 : Blo 1305971 1960295 := bstep (se 1 (by rfl) ⟨1470221, by rfl⟩ : syracuseStep 1960295 = 2940443) B2940443
theorem B11160125 : Blo 1305971 11160125 := bstep (se 3 (by rfl) ⟨2092523, by rfl⟩ : syracuseStep 11160125 = 4185047) B4185047
theorem B22342391 : Blo 1305971 22342391 := bstep (se 1 (by rfl) ⟨16756793, by rfl⟩ : syracuseStep 22342391 = 33513587) B33513587
theorem B14134013 : Blo 1305971 14134013 := bstep (se 3 (by rfl) ⟨2650127, by rfl⟩ : syracuseStep 14134013 = 5300255) B5300255
theorem B1960751 : Blo 1305971 1960751 := bstep (se 1 (by rfl) ⟨1470563, by rfl⟩ : syracuseStep 1960751 = 2941127) B2941127
theorem B4189097 : Blo 1305971 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B1960895 : Blo 1305971 1960895 := bstep (se 1 (by rfl) ⟨1470671, by rfl⟩ : syracuseStep 1960895 = 2941343) B2941343
theorem B4189495 : Blo 1305971 4189495 := bstep (se 1 (by rfl) ⟨3142121, by rfl⟩ : syracuseStep 4189495 = 6284243) B6284243
theorem B8162623 : Blo 1305971 8162623 := bstep (se 1 (by rfl) ⟨6121967, by rfl⟩ : syracuseStep 8162623 = 12243935) B12243935
theorem B1961279 : Blo 1305971 1961279 := bstep (se 1 (by rfl) ⟨1470959, by rfl⟩ : syracuseStep 1961279 = 2941919) B2941919
theorem B9924119 : Blo 1305971 9924119 := bstep (se 1 (by rfl) ⟨7443089, by rfl⟩ : syracuseStep 9924119 = 14886179) B14886179
theorem B1306223 : Blo 1305971 1306223 := bstep (se 1 (by rfl) ⟨979667, by rfl⟩ : syracuseStep 1306223 = 1959335) B1959335
theorem B1961663 : Blo 1305971 1961663 := bstep (se 1 (by rfl) ⟨1471247, by rfl⟩ : syracuseStep 1961663 = 2942495) B2942495
theorem B1306471 : Blo 1305971 1306471 := bstep (se 1 (by rfl) ⟨979853, by rfl⟩ : syracuseStep 1306471 = 1959707) B1959707
theorem B1961927 : Blo 1305971 1961927 := bstep (se 1 (by rfl) ⟨1471445, by rfl⟩ : syracuseStep 1961927 = 2942891) B2942891
theorem B96661475 : Blo 1305971 96661475 := bstep (se 1 (by rfl) ⟨72496106, by rfl⟩ : syracuseStep 96661475 = 144992213) B144992213
theorem B4411475 : Blo 1305971 4411475 := bstep (se 1 (by rfl) ⟨3308606, by rfl⟩ : syracuseStep 4411475 = 6617213) B6617213
theorem B11169899 : Blo 1305971 11169899 := bstep (se 1 (by rfl) ⟨8377424, by rfl⟩ : syracuseStep 11169899 = 16754849) B16754849
theorem B14889095 : Blo 1305971 14889095 := bstep (se 1 (by rfl) ⟨11166821, by rfl⟩ : syracuseStep 14889095 = 22333643) B22333643
theorem B1470703 : Blo 1305971 1470703 := bstep (se 1 (by rfl) ⟨1103027, by rfl⟩ : syracuseStep 1470703 = 2206055) B2206055
theorem B7950793 : Blo 1305971 7950793 := bstep (se 2 (by rfl) ⟨2981547, by rfl⟩ : syracuseStep 7950793 = 5963095) B5963095
theorem B3142439 : Blo 1305971 3142439 := bstep (se 1 (by rfl) ⟨2356829, by rfl⟩ : syracuseStep 3142439 = 4713659) B4713659
theorem B4412231 : Blo 1305971 4412231 := bstep (se 1 (by rfl) ⟨3309173, by rfl⟩ : syracuseStep 4412231 = 6618347) B6618347
theorem B1307759 : Blo 1305971 1307759 := bstep (se 1 (by rfl) ⟨980819, by rfl⟩ : syracuseStep 1307759 = 1961639) B1961639
theorem B1307807 : Blo 1305971 1307807 := bstep (se 1 (by rfl) ⟨980855, by rfl⟩ : syracuseStep 1307807 = 1961711) B1961711
theorem B7943591 : Blo 1305971 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B4413419 : Blo 1305971 4413419 := bstep (se 1 (by rfl) ⟨3310064, by rfl⟩ : syracuseStep 4413419 = 6620129) B6620129
theorem B1988587 : Blo 1305971 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B2791655 : Blo 1305971 2791655 := bstep (se 1 (by rfl) ⟨2093741, by rfl⟩ : syracuseStep 2791655 = 4187483) B4187483
theorem B2939273 : Blo 1305971 2939273 := bstep (se 2 (by rfl) ⟨1102227, by rfl⟩ : syracuseStep 2939273 = 2204455) B2204455
theorem B14892011 : Blo 1305971 14892011 := bstep (se 1 (by rfl) ⟨11169008, by rfl⟩ : syracuseStep 14892011 = 22338017) B22338017
theorem B42392807 : Blo 1305971 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B57302635 : Blo 1305971 57302635 := bstep (se 1 (by rfl) ⟨42976976, by rfl⟩ : syracuseStep 57302635 = 85953953) B85953953
theorem B9920231 : Blo 1305971 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B7061231 : Blo 1305971 7061231 := bstep (se 1 (by rfl) ⟨5295923, by rfl⟩ : syracuseStep 7061231 = 10591847) B10591847
theorem B3309295 : Blo 1305971 3309295 := bstep (se 1 (by rfl) ⟨2481971, by rfl⟩ : syracuseStep 3309295 = 4963943) B4963943
theorem B2940983 : Blo 1305971 2940983 := bstep (se 1 (by rfl) ⟨2205737, by rfl⟩ : syracuseStep 2940983 = 4411475) B4411475
theorem B7446599 : Blo 1305971 7446599 := bstep (se 1 (by rfl) ⟨5584949, by rfl⟩ : syracuseStep 7446599 = 11169899) B11169899
theorem B2941487 : Blo 1305971 2941487 := bstep (se 1 (by rfl) ⟨2206115, by rfl⟩ : syracuseStep 2941487 = 4412231) B4412231
theorem B10601057 : Blo 1305971 10601057 := bstep (se 2 (by rfl) ⟨3975396, by rfl⟩ : syracuseStep 10601057 = 7950793) B7950793
theorem B16745723 : Blo 1305971 16745723 := bstep (se 1 (by rfl) ⟨12559292, by rfl⟩ : syracuseStep 16745723 = 25118585) B25118585
theorem B2942279 : Blo 1305971 2942279 := bstep (se 1 (by rfl) ⟨2206709, by rfl⟩ : syracuseStep 2942279 = 4413419) B4413419
theorem B1861103 : Blo 1305971 1861103 := bstep (se 1 (by rfl) ⟨1395827, by rfl⟩ : syracuseStep 1861103 = 2791655) B2791655
theorem B1959515 : Blo 1305971 1959515 := bstep (se 1 (by rfl) ⟨1469636, by rfl⟩ : syracuseStep 1959515 = 2939273) B2939273
theorem B7440083 : Blo 1305971 7440083 := bstep (se 1 (by rfl) ⟨5580062, by rfl⟩ : syracuseStep 7440083 = 11160125) B11160125
theorem B14894927 : Blo 1305971 14894927 := bstep (se 1 (by rfl) ⟨11171195, by rfl⟩ : syracuseStep 14894927 = 22342391) B22342391
theorem B9422675 : Blo 1305971 9422675 := bstep (se 1 (by rfl) ⟨7067006, by rfl⟩ : syracuseStep 9422675 = 14134013) B14134013
theorem B6613487 : Blo 1305971 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B64440983 : Blo 1305971 64440983 := bstep (se 1 (by rfl) ⟨48330737, by rfl⟩ : syracuseStep 64440983 = 96661475) B96661475
theorem B1960937 : Blo 1305971 1960937 := bstep (se 2 (by rfl) ⟨735351, by rfl⟩ : syracuseStep 1960937 = 1470703) B1470703
theorem B2206703 : Blo 1305971 2206703 := bstep (se 1 (by rfl) ⟨1655027, by rfl⟩ : syracuseStep 2206703 = 3310055) B3310055
theorem B1961051 : Blo 1305971 1961051 := bstep (se 1 (by rfl) ⟨1470788, by rfl⟩ : syracuseStep 1961051 = 2941577) B2941577
theorem B275525003 : Blo 1305971 275525003 := bstep (se 1 (by rfl) ⟨206643752, by rfl⟩ : syracuseStep 275525003 = 413287505) B413287505
theorem B5295727 : Blo 1305971 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B1470235 : Blo 1305971 1470235 := bstep (se 1 (by rfl) ⟨1102676, by rfl⟩ : syracuseStep 1470235 = 2205353) B2205353
theorem B51588937 : Blo 1305971 51588937 := bstep (se 2 (by rfl) ⟨19345851, by rfl⟩ : syracuseStep 51588937 = 38691703) B38691703
theorem B1306695 : Blo 1305971 1306695 := bstep (se 1 (by rfl) ⟨980021, by rfl⟩ : syracuseStep 1306695 = 1960043) B1960043
theorem B1306863 : Blo 1305971 1306863 := bstep (se 1 (by rfl) ⟨980147, by rfl⟩ : syracuseStep 1306863 = 1960295) B1960295
theorem B10883497 : Blo 1305971 10883497 := bstep (se 2 (by rfl) ⟨4081311, by rfl⟩ : syracuseStep 10883497 = 8162623) B8162623
theorem B1307167 : Blo 1305971 1307167 := bstep (se 1 (by rfl) ⟨980375, by rfl⟩ : syracuseStep 1307167 = 1960751) B1960751
theorem B1307263 : Blo 1305971 1307263 := bstep (se 1 (by rfl) ⟨980447, by rfl⟩ : syracuseStep 1307263 = 1960895) B1960895
theorem B76403513 : Blo 1305971 76403513 := bstep (se 2 (by rfl) ⟨28651317, by rfl⟩ : syracuseStep 76403513 = 57302635) B57302635
theorem B1307519 : Blo 1305971 1307519 := bstep (se 1 (by rfl) ⟨980639, by rfl⟩ : syracuseStep 1307519 = 1961279) B1961279
theorem B4412393 : Blo 1305971 4412393 := bstep (se 2 (by rfl) ⟨1654647, by rfl⟩ : syracuseStep 4412393 = 3309295) B3309295
theorem B6616079 : Blo 1305971 6616079 := bstep (se 1 (by rfl) ⟨4962059, by rfl⟩ : syracuseStep 6616079 = 9924119) B9924119
theorem B1307775 : Blo 1305971 1307775 := bstep (se 1 (by rfl) ⟨980831, by rfl⟩ : syracuseStep 1307775 = 1961663) B1961663
theorem B4707487 : Blo 1305971 4707487 := bstep (se 1 (by rfl) ⟨3530615, by rfl⟩ : syracuseStep 4707487 = 7061231) B7061231
theorem B1307951 : Blo 1305971 1307951 := bstep (se 1 (by rfl) ⟨980963, by rfl⟩ : syracuseStep 1307951 = 1961927) B1961927
theorem B2651449 : Blo 1305971 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B9926063 : Blo 1305971 9926063 := bstep (se 1 (by rfl) ⟨7444547, by rfl⟩ : syracuseStep 9926063 = 14889095) B14889095
theorem B2479891 : Blo 1305971 2479891 := bstep (se 1 (by rfl) ⟨1859918, by rfl⟩ : syracuseStep 2479891 = 3719837) B3719837
theorem B2094959 : Blo 1305971 2094959 := bstep (se 1 (by rfl) ⟨1571219, by rfl⟩ : syracuseStep 2094959 = 3142439) B3142439
theorem B2939183 : Blo 1305971 2939183 := bstep (se 1 (by rfl) ⟨2204387, by rfl⟩ : syracuseStep 2939183 = 4408775) B4408775
theorem B5585993 : Blo 1305971 5585993 := bstep (se 2 (by rfl) ⟨2094747, by rfl⟩ : syracuseStep 5585993 = 4189495) B4189495
theorem B2792731 : Blo 1305971 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B9928007 : Blo 1305971 9928007 := bstep (se 1 (by rfl) ⟨7446005, by rfl⟩ : syracuseStep 9928007 = 14892011) B14892011
theorem B28261871 : Blo 1305971 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B4964399 : Blo 1305971 4964399 := bstep (se 1 (by rfl) ⟨3723299, by rfl⟩ : syracuseStep 4964399 = 7446599) B7446599
theorem B2941595 : Blo 1305971 2941595 := bstep (se 1 (by rfl) ⟨2206196, by rfl⟩ : syracuseStep 2941595 = 4412393) B4412393
theorem B9929951 : Blo 1305971 9929951 := bstep (se 1 (by rfl) ⟨7447463, by rfl⟩ : syracuseStep 9929951 = 14894927) B14894927
theorem B1959455 : Blo 1305971 1959455 := bstep (se 1 (by rfl) ⟨1469591, by rfl⟩ : syracuseStep 1959455 = 2939183) B2939183
theorem B6276649 : Blo 1305971 6276649 := bstep (se 2 (by rfl) ⟨2353743, by rfl⟩ : syracuseStep 6276649 = 4707487) B4707487
theorem B4408991 : Blo 1305971 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B42960655 : Blo 1305971 42960655 := bstep (se 1 (by rfl) ⟨32220491, by rfl⟩ : syracuseStep 42960655 = 64440983) B64440983
theorem B183683335 : Blo 1305971 183683335 := bstep (se 1 (by rfl) ⟨137762501, by rfl⟩ : syracuseStep 183683335 = 275525003) B275525003
theorem B1960313 : Blo 1305971 1960313 := bstep (se 2 (by rfl) ⟨735117, by rfl⟩ : syracuseStep 1960313 = 1470235) B1470235
theorem B1960655 : Blo 1305971 1960655 := bstep (se 1 (by rfl) ⟨1470491, by rfl⟩ : syracuseStep 1960655 = 2940983) B2940983
theorem B1960991 : Blo 1305971 1960991 := bstep (se 1 (by rfl) ⟨1470743, by rfl⟩ : syracuseStep 1960991 = 2941487) B2941487
theorem B14511329 : Blo 1305971 14511329 := bstep (se 2 (by rfl) ⟨5441748, by rfl⟩ : syracuseStep 14511329 = 10883497) B10883497
theorem B4410719 : Blo 1305971 4410719 := bstep (se 1 (by rfl) ⟨3308039, by rfl⟩ : syracuseStep 4410719 = 6616079) B6616079
theorem B1961519 : Blo 1305971 1961519 := bstep (se 1 (by rfl) ⟨1471139, by rfl⟩ : syracuseStep 1961519 = 2942279) B2942279
theorem B1306343 : Blo 1305971 1306343 := bstep (se 1 (by rfl) ⟨979757, by rfl⟩ : syracuseStep 1306343 = 1959515) B1959515
theorem B4960055 : Blo 1305971 4960055 := bstep (se 1 (by rfl) ⟨3720041, by rfl⟩ : syracuseStep 4960055 = 7440083) B7440083
theorem B1396639 : Blo 1305971 1396639 := bstep (se 1 (by rfl) ⟨1047479, by rfl⟩ : syracuseStep 1396639 = 2094959) B2094959
theorem B3723641 : Blo 1305971 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B3535265 : Blo 1305971 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B1307291 : Blo 1305971 1307291 := bstep (se 1 (by rfl) ⟨980468, by rfl⟩ : syracuseStep 1307291 = 1960937) B1960937
theorem B1471135 : Blo 1305971 1471135 := bstep (se 1 (by rfl) ⟨1103351, by rfl⟩ : syracuseStep 1471135 = 2206703) B2206703
theorem B3723995 : Blo 1305971 3723995 := bstep (se 1 (by rfl) ⟨2792996, by rfl⟩ : syracuseStep 3723995 = 5585993) B5585993
theorem B1307367 : Blo 1305971 1307367 := bstep (se 1 (by rfl) ⟨980525, by rfl⟩ : syracuseStep 1307367 = 1961051) B1961051
theorem B3306521 : Blo 1305971 3306521 := bstep (se 2 (by rfl) ⟨1239945, by rfl⟩ : syracuseStep 3306521 = 2479891) B2479891
theorem B68785249 : Blo 1305971 68785249 := bstep (se 2 (by rfl) ⟨25794468, by rfl⟩ : syracuseStep 68785249 = 51588937) B51588937
theorem B7067371 : Blo 1305971 7067371 := bstep (se 1 (by rfl) ⟨5300528, by rfl⟩ : syracuseStep 7067371 = 10601057) B10601057
theorem B50935675 : Blo 1305971 50935675 := bstep (se 1 (by rfl) ⟨38201756, by rfl⟩ : syracuseStep 50935675 = 76403513) B76403513
theorem B11163815 : Blo 1305971 11163815 := bstep (se 1 (by rfl) ⟨8372861, by rfl⟩ : syracuseStep 11163815 = 16745723) B16745723
theorem B6617375 : Blo 1305971 6617375 := bstep (se 1 (by rfl) ⟨4963031, by rfl⟩ : syracuseStep 6617375 = 9926063) B9926063
theorem B6281783 : Blo 1305971 6281783 := bstep (se 1 (by rfl) ⟨4711337, by rfl⟩ : syracuseStep 6281783 = 9422675) B9422675
theorem B4962941 : Blo 1305971 4962941 := bstep (se 3 (by rfl) ⟨930551, by rfl⟩ : syracuseStep 4962941 = 1861103) B1861103
theorem B7060969 : Blo 1305971 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B6618671 : Blo 1305971 6618671 := bstep (se 1 (by rfl) ⟨4964003, by rfl⟩ : syracuseStep 6618671 = 9928007) B9928007
theorem B18841247 : Blo 1305971 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B3309599 : Blo 1305971 3309599 := bstep (se 1 (by rfl) ⟨2482199, by rfl⟩ : syracuseStep 3309599 = 4964399) B4964399
theorem B2482427 : Blo 1305971 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B2482663 : Blo 1305971 2482663 := bstep (se 1 (by rfl) ⟨1861997, by rfl⟩ : syracuseStep 2482663 = 3723995) B3723995
theorem B2204347 : Blo 1305971 2204347 := bstep (se 1 (by rfl) ⟨1653260, by rfl⟩ : syracuseStep 2204347 = 3306521) B3306521
theorem B6619967 : Blo 1305971 6619967 := bstep (se 1 (by rfl) ⟨4964975, by rfl⟩ : syracuseStep 6619967 = 9929951) B9929951
theorem B229123493 : Blo 1305971 229123493 := bstep (se 4 (by rfl) ⟨21480327, by rfl⟩ : syracuseStep 229123493 = 42960655) B42960655
theorem B4187855 : Blo 1305971 4187855 := bstep (se 1 (by rfl) ⟨3140891, by rfl⟩ : syracuseStep 4187855 = 6281783) B6281783
theorem B9414625 : Blo 1305971 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B9423161 : Blo 1305971 9423161 := bstep (se 2 (by rfl) ⟨3533685, by rfl⟩ : syracuseStep 9423161 = 7067371) B7067371
theorem B12560831 : Blo 1305971 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B67914233 : Blo 1305971 67914233 := bstep (se 2 (by rfl) ⟨25467837, by rfl⟩ : syracuseStep 67914233 = 50935675) B50935675
theorem B1862185 : Blo 1305971 1862185 := bstep (se 2 (by rfl) ⟨698319, by rfl⟩ : syracuseStep 1862185 = 1396639) B1396639
theorem B244911113 : Blo 1305971 244911113 := bstep (se 2 (by rfl) ⟨91841667, by rfl⟩ : syracuseStep 244911113 = 183683335) B183683335
theorem B1961063 : Blo 1305971 1961063 := bstep (se 1 (by rfl) ⟨1470797, by rfl⟩ : syracuseStep 1961063 = 2941595) B2941595
theorem B1961513 : Blo 1305971 1961513 := bstep (se 2 (by rfl) ⟨735567, by rfl⟩ : syracuseStep 1961513 = 1471135) B1471135
theorem B1306303 : Blo 1305971 1306303 := bstep (se 1 (by rfl) ⟨979727, by rfl⟩ : syracuseStep 1306303 = 1959455) B1959455
theorem B7442543 : Blo 1305971 7442543 := bstep (se 1 (by rfl) ⟨5581907, by rfl⟩ : syracuseStep 7442543 = 11163815) B11163815
theorem B91713665 : Blo 1305971 91713665 := bstep (se 2 (by rfl) ⟨34392624, by rfl⟩ : syracuseStep 91713665 = 68785249) B68785249
theorem B4411583 : Blo 1305971 4411583 := bstep (se 1 (by rfl) ⟨3308687, by rfl⟩ : syracuseStep 4411583 = 6617375) B6617375
theorem B1306875 : Blo 1305971 1306875 := bstep (se 1 (by rfl) ⟨980156, by rfl⟩ : syracuseStep 1306875 = 1960313) B1960313
theorem B1307103 : Blo 1305971 1307103 := bstep (se 1 (by rfl) ⟨980327, by rfl⟩ : syracuseStep 1307103 = 1960655) B1960655
theorem B1307327 : Blo 1305971 1307327 := bstep (se 1 (by rfl) ⟨980495, by rfl⟩ : syracuseStep 1307327 = 1960991) B1960991
theorem B8368865 : Blo 1305971 8368865 := bstep (se 2 (by rfl) ⟨3138324, by rfl⟩ : syracuseStep 8368865 = 6276649) B6276649
theorem B4412447 : Blo 1305971 4412447 := bstep (se 1 (by rfl) ⟨3309335, by rfl⟩ : syracuseStep 4412447 = 6618671) B6618671
theorem B1307679 : Blo 1305971 1307679 := bstep (se 1 (by rfl) ⟨980759, by rfl⟩ : syracuseStep 1307679 = 1961519) B1961519
theorem B3306703 : Blo 1305971 3306703 := bstep (se 1 (by rfl) ⟨2480027, by rfl⟩ : syracuseStep 3306703 = 4960055) B4960055
theorem B9427373 : Blo 1305971 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B2939327 : Blo 1305971 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B3308627 : Blo 1305971 3308627 := bstep (se 1 (by rfl) ⟨2481470, by rfl⟩ : syracuseStep 3308627 = 4962941) B4962941
theorem B9674219 : Blo 1305971 9674219 := bstep (se 1 (by rfl) ⟨7255664, by rfl⟩ : syracuseStep 9674219 = 14511329) B14511329
theorem B2940479 : Blo 1305971 2940479 := bstep (se 1 (by rfl) ⟨2205359, by rfl⟩ : syracuseStep 2940479 = 4410719) B4410719
theorem B2941055 : Blo 1305971 2941055 := bstep (se 1 (by rfl) ⟨2205791, by rfl⟩ : syracuseStep 2941055 = 4411583) B4411583
theorem B5579243 : Blo 1305971 5579243 := bstep (se 1 (by rfl) ⟨4184432, by rfl⟩ : syracuseStep 5579243 = 8368865) B8368865
theorem B3310217 : Blo 1305971 3310217 := bstep (se 2 (by rfl) ⟨1241331, by rfl⟩ : syracuseStep 3310217 = 2482663) B2482663
theorem B6619805 : Blo 1305971 6619805 := bstep (se 3 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 6619805 = 2482427) B2482427
theorem B2941631 : Blo 1305971 2941631 := bstep (se 1 (by rfl) ⟨2206223, by rfl⟩ : syracuseStep 2941631 = 4412447) B4412447
theorem B2482913 : Blo 1305971 2482913 := bstep (se 2 (by rfl) ⟨931092, by rfl⟩ : syracuseStep 2482913 = 1862185) B1862185
theorem B152748995 : Blo 1305971 152748995 := bstep (se 1 (by rfl) ⟨114561746, by rfl⟩ : syracuseStep 152748995 = 229123493) B229123493
theorem B4408937 : Blo 1305971 4408937 := bstep (se 2 (by rfl) ⟨1653351, by rfl⟩ : syracuseStep 4408937 = 3306703) B3306703
theorem B6284915 : Blo 1305971 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B1959551 : Blo 1305971 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B8373887 : Blo 1305971 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B2205751 : Blo 1305971 2205751 := bstep (se 1 (by rfl) ⟨1654313, by rfl⟩ : syracuseStep 2205751 = 3308627) B3308627
theorem B6449479 : Blo 1305971 6449479 := bstep (se 1 (by rfl) ⟨4837109, by rfl⟩ : syracuseStep 6449479 = 9674219) B9674219
theorem B1960319 : Blo 1305971 1960319 := bstep (se 1 (by rfl) ⟨1470239, by rfl⟩ : syracuseStep 1960319 = 2940479) B2940479
theorem B12552833 : Blo 1305971 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B2206399 : Blo 1305971 2206399 := bstep (se 1 (by rfl) ⟨1654799, by rfl⟩ : syracuseStep 2206399 = 3309599) B3309599
theorem B1307375 : Blo 1305971 1307375 := bstep (se 1 (by rfl) ⟨980531, by rfl⟩ : syracuseStep 1307375 = 1961063) B1961063
theorem B1307675 : Blo 1305971 1307675 := bstep (se 1 (by rfl) ⟨980756, by rfl⟩ : syracuseStep 1307675 = 1961513) B1961513
theorem B4961695 : Blo 1305971 4961695 := bstep (se 1 (by rfl) ⟨3721271, by rfl⟩ : syracuseStep 4961695 = 7442543) B7442543
theorem B244569773 : Blo 1305971 244569773 := bstep (se 3 (by rfl) ⟨45856832, by rfl⟩ : syracuseStep 244569773 = 91713665) B91713665
theorem B4413311 : Blo 1305971 4413311 := bstep (se 1 (by rfl) ⟨3309983, by rfl⟩ : syracuseStep 4413311 = 6619967) B6619967
theorem B2939129 : Blo 1305971 2939129 := bstep (se 2 (by rfl) ⟨1102173, by rfl⟩ : syracuseStep 2939129 = 2204347) B2204347
theorem B2791903 : Blo 1305971 2791903 := bstep (se 1 (by rfl) ⟨2093927, by rfl⟩ : syracuseStep 2791903 = 4187855) B4187855
theorem B6282107 : Blo 1305971 6282107 := bstep (se 1 (by rfl) ⟨4711580, by rfl⟩ : syracuseStep 6282107 = 9423161) B9423161
theorem B45276155 : Blo 1305971 45276155 := bstep (se 1 (by rfl) ⟨33957116, by rfl⟩ : syracuseStep 45276155 = 67914233) B67914233
theorem B163274075 : Blo 1305971 163274075 := bstep (se 1 (by rfl) ⟨122455556, by rfl⟩ : syracuseStep 163274075 = 244911113) B244911113
theorem B2941001 : Blo 1305971 2941001 := bstep (se 2 (by rfl) ⟨1102875, by rfl⟩ : syracuseStep 2941001 = 2205751) B2205751
theorem B3719495 : Blo 1305971 3719495 := bstep (se 1 (by rfl) ⟨2789621, by rfl⟩ : syracuseStep 3719495 = 5579243) B5579243
theorem B2941865 : Blo 1305971 2941865 := bstep (se 2 (by rfl) ⟨1103199, by rfl⟩ : syracuseStep 2941865 = 2206399) B2206399
theorem B163046515 : Blo 1305971 163046515 := bstep (se 1 (by rfl) ⟨122284886, by rfl⟩ : syracuseStep 163046515 = 244569773) B244569773
theorem B2942207 : Blo 1305971 2942207 := bstep (se 1 (by rfl) ⟨2206655, by rfl⟩ : syracuseStep 2942207 = 4413311) B4413311
theorem B1959419 : Blo 1305971 1959419 := bstep (se 1 (by rfl) ⟨1469564, by rfl⟩ : syracuseStep 1959419 = 2939129) B2939129
theorem B33474221 : Blo 1305971 33474221 := bstep (se 3 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 33474221 = 12552833) B12552833
theorem B4188071 : Blo 1305971 4188071 := bstep (se 1 (by rfl) ⟨3141053, by rfl⟩ : syracuseStep 4188071 = 6282107) B6282107
theorem B6621101 : Blo 1305971 6621101 := bstep (se 3 (by rfl) ⟨1241456, by rfl⟩ : syracuseStep 6621101 = 2482913) B2482913
theorem B108849383 : Blo 1305971 108849383 := bstep (se 1 (by rfl) ⟨81637037, by rfl⟩ : syracuseStep 108849383 = 163274075) B163274075
theorem B1960703 : Blo 1305971 1960703 := bstep (se 1 (by rfl) ⟨1470527, by rfl⟩ : syracuseStep 1960703 = 2941055) B2941055
theorem B2206811 : Blo 1305971 2206811 := bstep (se 1 (by rfl) ⟨1655108, by rfl⟩ : syracuseStep 2206811 = 3310217) B3310217
theorem B1961087 : Blo 1305971 1961087 := bstep (se 1 (by rfl) ⟨1470815, by rfl⟩ : syracuseStep 1961087 = 2941631) B2941631
theorem B3722537 : Blo 1305971 3722537 := bstep (se 2 (by rfl) ⟨1395951, by rfl⟩ : syracuseStep 3722537 = 2791903) B2791903
theorem B4189943 : Blo 1305971 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B1306367 : Blo 1305971 1306367 := bstep (se 1 (by rfl) ⟨979775, by rfl⟩ : syracuseStep 1306367 = 1959551) B1959551
theorem B5582591 : Blo 1305971 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B137588885 : Blo 1305971 137588885 := bstep (se 6 (by rfl) ⟨3224739, by rfl⟩ : syracuseStep 137588885 = 6449479) B6449479
theorem B1306879 : Blo 1305971 1306879 := bstep (se 1 (by rfl) ⟨980159, by rfl⟩ : syracuseStep 1306879 = 1960319) B1960319
theorem B6615593 : Blo 1305971 6615593 := bstep (se 2 (by rfl) ⟨2480847, by rfl⟩ : syracuseStep 6615593 = 4961695) B4961695
theorem B30184103 : Blo 1305971 30184103 := bstep (se 1 (by rfl) ⟨22638077, by rfl⟩ : syracuseStep 30184103 = 45276155) B45276155
theorem B4413203 : Blo 1305971 4413203 := bstep (se 1 (by rfl) ⟨3309902, by rfl⟩ : syracuseStep 4413203 = 6619805) B6619805
theorem B2939291 : Blo 1305971 2939291 := bstep (se 1 (by rfl) ⟨2204468, by rfl⟩ : syracuseStep 2939291 = 4408937) B4408937
theorem B407330653 : Blo 1305971 407330653 := bstep (se 3 (by rfl) ⟨76374497, by rfl⟩ : syracuseStep 407330653 = 152748995) B152748995
theorem B91725923 : Blo 1305971 91725923 := bstep (se 1 (by rfl) ⟨68794442, by rfl⟩ : syracuseStep 91725923 = 137588885) B137588885
theorem B22316147 : Blo 1305971 22316147 := bstep (se 1 (by rfl) ⟨16737110, by rfl⟩ : syracuseStep 22316147 = 33474221) B33474221
theorem B2942135 : Blo 1305971 2942135 := bstep (se 1 (by rfl) ⟨2206601, by rfl⟩ : syracuseStep 2942135 = 4413203) B4413203
theorem B72566255 : Blo 1305971 72566255 := bstep (se 1 (by rfl) ⟨54424691, by rfl⟩ : syracuseStep 72566255 = 108849383) B108849383
theorem B1959527 : Blo 1305971 1959527 := bstep (se 1 (by rfl) ⟨1469645, by rfl⟩ : syracuseStep 1959527 = 2939291) B2939291
theorem B11168189 : Blo 1305971 11168189 := bstep (se 3 (by rfl) ⟨2094035, by rfl⟩ : syracuseStep 11168189 = 4188071) B4188071
theorem B543107537 : Blo 1305971 543107537 := bstep (se 2 (by rfl) ⟨203665326, by rfl⟩ : syracuseStep 543107537 = 407330653) B407330653
theorem B3721727 : Blo 1305971 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B1960667 : Blo 1305971 1960667 := bstep (se 1 (by rfl) ⟨1470500, by rfl⟩ : syracuseStep 1960667 = 2941001) B2941001
theorem B4410395 : Blo 1305971 4410395 := bstep (se 1 (by rfl) ⟨3307796, by rfl⟩ : syracuseStep 4410395 = 6615593) B6615593
theorem B1961243 : Blo 1305971 1961243 := bstep (se 1 (by rfl) ⟨1470932, by rfl⟩ : syracuseStep 1961243 = 2941865) B2941865
theorem B1961471 : Blo 1305971 1961471 := bstep (se 1 (by rfl) ⟨1471103, by rfl⟩ : syracuseStep 1961471 = 2942207) B2942207
theorem B1306279 : Blo 1305971 1306279 := bstep (se 1 (by rfl) ⟨979709, by rfl⟩ : syracuseStep 1306279 = 1959419) B1959419
theorem B217395353 : Blo 1305971 217395353 := bstep (se 2 (by rfl) ⟨81523257, by rfl⟩ : syracuseStep 217395353 = 163046515) B163046515
theorem B80490941 : Blo 1305971 80490941 := bstep (se 3 (by rfl) ⟨15092051, by rfl⟩ : syracuseStep 80490941 = 30184103) B30184103
theorem B1307135 : Blo 1305971 1307135 := bstep (se 1 (by rfl) ⟨980351, by rfl⟩ : syracuseStep 1307135 = 1960703) B1960703
theorem B1471207 : Blo 1305971 1471207 := bstep (se 1 (by rfl) ⟨1103405, by rfl⟩ : syracuseStep 1471207 = 2206811) B2206811
theorem B1307391 : Blo 1305971 1307391 := bstep (se 1 (by rfl) ⟨980543, by rfl⟩ : syracuseStep 1307391 = 1961087) B1961087
theorem B2479663 : Blo 1305971 2479663 := bstep (se 1 (by rfl) ⟨1859747, by rfl⟩ : syracuseStep 2479663 = 3719495) B3719495
theorem B4414067 : Blo 1305971 4414067 := bstep (se 1 (by rfl) ⟨3310550, by rfl⟩ : syracuseStep 4414067 = 6621101) B6621101
theorem B2481691 : Blo 1305971 2481691 := bstep (se 1 (by rfl) ⟨1861268, by rfl⟩ : syracuseStep 2481691 = 3722537) B3722537
theorem B2793295 : Blo 1305971 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B14877431 : Blo 1305971 14877431 := bstep (se 1 (by rfl) ⟨11158073, by rfl⟩ : syracuseStep 14877431 = 22316147) B22316147
theorem B362071691 : Blo 1305971 362071691 := bstep (se 1 (by rfl) ⟨271553768, by rfl⟩ : syracuseStep 362071691 = 543107537) B543107537
theorem B2942711 : Blo 1305971 2942711 := bstep (se 1 (by rfl) ⟨2207033, by rfl⟩ : syracuseStep 2942711 = 4414067) B4414067
theorem B53660627 : Blo 1305971 53660627 := bstep (se 1 (by rfl) ⟨40245470, by rfl⟩ : syracuseStep 53660627 = 80490941) B80490941
theorem B1961423 : Blo 1305971 1961423 := bstep (se 1 (by rfl) ⟨1471067, by rfl⟩ : syracuseStep 1961423 = 2942135) B2942135
theorem B1961609 : Blo 1305971 1961609 := bstep (se 2 (by rfl) ⟨735603, by rfl⟩ : syracuseStep 1961609 = 1471207) B1471207
theorem B48377503 : Blo 1305971 48377503 := bstep (se 1 (by rfl) ⟨36283127, by rfl⟩ : syracuseStep 48377503 = 72566255) B72566255
theorem B1306351 : Blo 1305971 1306351 := bstep (se 1 (by rfl) ⟨979763, by rfl⟩ : syracuseStep 1306351 = 1959527) B1959527
theorem B9924605 : Blo 1305971 9924605 := bstep (se 3 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 9924605 = 3721727) B3721727
theorem B1307111 : Blo 1305971 1307111 := bstep (se 1 (by rfl) ⟨980333, by rfl⟩ : syracuseStep 1307111 = 1960667) B1960667
theorem B3306217 : Blo 1305971 3306217 := bstep (se 2 (by rfl) ⟨1239831, by rfl⟩ : syracuseStep 3306217 = 2479663) B2479663
theorem B1307495 : Blo 1305971 1307495 := bstep (se 1 (by rfl) ⟨980621, by rfl⟩ : syracuseStep 1307495 = 1961243) B1961243
theorem B1307647 : Blo 1305971 1307647 := bstep (se 1 (by rfl) ⟨980735, by rfl⟩ : syracuseStep 1307647 = 1961471) B1961471
theorem B3724393 : Blo 1305971 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B144930235 : Blo 1305971 144930235 := bstep (se 1 (by rfl) ⟨108697676, by rfl⟩ : syracuseStep 144930235 = 217395353) B217395353
theorem B244602461 : Blo 1305971 244602461 := bstep (se 3 (by rfl) ⟨45862961, by rfl⟩ : syracuseStep 244602461 = 91725923) B91725923
theorem B7445459 : Blo 1305971 7445459 := bstep (se 1 (by rfl) ⟨5584094, by rfl⟩ : syracuseStep 7445459 = 11168189) B11168189
theorem B2940263 : Blo 1305971 2940263 := bstep (se 1 (by rfl) ⟨2205197, by rfl⟩ : syracuseStep 2940263 = 4410395) B4410395
theorem B3308921 : Blo 1305971 3308921 := bstep (se 2 (by rfl) ⟨1240845, by rfl⟩ : syracuseStep 3308921 = 2481691) B2481691
theorem B4408289 : Blo 1305971 4408289 := bstep (se 2 (by rfl) ⟨1653108, by rfl⟩ : syracuseStep 4408289 = 3306217) B3306217
theorem B4965857 : Blo 1305971 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B652273229 : Blo 1305971 652273229 := bstep (se 3 (by rfl) ⟨122301230, by rfl⟩ : syracuseStep 652273229 = 244602461) B244602461
theorem B1960175 : Blo 1305971 1960175 := bstep (se 1 (by rfl) ⟨1470131, by rfl⟩ : syracuseStep 1960175 = 2940263) B2940263
theorem B2205947 : Blo 1305971 2205947 := bstep (se 1 (by rfl) ⟨1654460, by rfl⟩ : syracuseStep 2205947 = 3308921) B3308921
theorem B241381127 : Blo 1305971 241381127 := bstep (se 1 (by rfl) ⟨181035845, by rfl⟩ : syracuseStep 241381127 = 362071691) B362071691
theorem B1961807 : Blo 1305971 1961807 := bstep (se 1 (by rfl) ⟨1471355, by rfl⟩ : syracuseStep 1961807 = 2942711) B2942711
theorem B1307615 : Blo 1305971 1307615 := bstep (se 1 (by rfl) ⟨980711, by rfl⟩ : syracuseStep 1307615 = 1961423) B1961423
theorem B1307739 : Blo 1305971 1307739 := bstep (se 1 (by rfl) ⟨980804, by rfl⟩ : syracuseStep 1307739 = 1961609) B1961609
theorem B6616403 : Blo 1305971 6616403 := bstep (se 1 (by rfl) ⟨4962302, by rfl⟩ : syracuseStep 6616403 = 9924605) B9924605
theorem B9918287 : Blo 1305971 9918287 := bstep (se 1 (by rfl) ⟨7438715, by rfl⟩ : syracuseStep 9918287 = 14877431) B14877431
theorem B193240313 : Blo 1305971 193240313 := bstep (se 2 (by rfl) ⟨72465117, by rfl⟩ : syracuseStep 193240313 = 144930235) B144930235
theorem B35773751 : Blo 1305971 35773751 := bstep (se 1 (by rfl) ⟨26830313, by rfl⟩ : syracuseStep 35773751 = 53660627) B53660627
theorem B4963639 : Blo 1305971 4963639 := bstep (se 1 (by rfl) ⟨3722729, by rfl⟩ : syracuseStep 4963639 = 7445459) B7445459
theorem B64503337 : Blo 1305971 64503337 := bstep (se 2 (by rfl) ⟨24188751, by rfl⟩ : syracuseStep 64503337 = 48377503) B48377503
theorem B3310571 : Blo 1305971 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B434848819 : Blo 1305971 434848819 := bstep (se 1 (by rfl) ⟨326136614, by rfl⟩ : syracuseStep 434848819 = 652273229) B652273229
theorem B6612191 : Blo 1305971 6612191 := bstep (se 1 (by rfl) ⟨4959143, by rfl⟩ : syracuseStep 6612191 = 9918287) B9918287
theorem B23849167 : Blo 1305971 23849167 := bstep (se 1 (by rfl) ⟨17886875, by rfl⟩ : syracuseStep 23849167 = 35773751) B35773751
theorem B4410935 : Blo 1305971 4410935 := bstep (se 1 (by rfl) ⟨3308201, by rfl⟩ : syracuseStep 4410935 = 6616403) B6616403
theorem B1306783 : Blo 1305971 1306783 := bstep (se 1 (by rfl) ⟨980087, by rfl⟩ : syracuseStep 1306783 = 1960175) B1960175
theorem B1470631 : Blo 1305971 1470631 := bstep (se 1 (by rfl) ⟨1102973, by rfl⟩ : syracuseStep 1470631 = 2205947) B2205947
theorem B86004449 : Blo 1305971 86004449 := bstep (se 2 (by rfl) ⟨32251668, by rfl⟩ : syracuseStep 86004449 = 64503337) B64503337
theorem B160920751 : Blo 1305971 160920751 := bstep (se 1 (by rfl) ⟨120690563, by rfl⟩ : syracuseStep 160920751 = 241381127) B241381127
theorem B1307871 : Blo 1305971 1307871 := bstep (se 1 (by rfl) ⟨980903, by rfl⟩ : syracuseStep 1307871 = 1961807) B1961807
theorem B2938859 : Blo 1305971 2938859 := bstep (se 1 (by rfl) ⟨2204144, by rfl⟩ : syracuseStep 2938859 = 4408289) B4408289
theorem B6618185 : Blo 1305971 6618185 := bstep (se 2 (by rfl) ⟨2481819, by rfl⟩ : syracuseStep 6618185 = 4963639) B4963639
theorem B128826875 : Blo 1305971 128826875 := bstep (se 1 (by rfl) ⟨96620156, by rfl⟩ : syracuseStep 128826875 = 193240313) B193240313
theorem B57336299 : Blo 1305971 57336299 := bstep (se 1 (by rfl) ⟨43002224, by rfl⟩ : syracuseStep 57336299 = 86004449) B86004449
theorem B4408127 : Blo 1305971 4408127 := bstep (se 1 (by rfl) ⟨3306095, by rfl⟩ : syracuseStep 4408127 = 6612191) B6612191
theorem B1959239 : Blo 1305971 1959239 := bstep (se 1 (by rfl) ⟨1469429, by rfl⟩ : syracuseStep 1959239 = 2938859) B2938859
theorem B579798425 : Blo 1305971 579798425 := bstep (se 2 (by rfl) ⟨217424409, by rfl⟩ : syracuseStep 579798425 = 434848819) B434848819
theorem B1960841 : Blo 1305971 1960841 := bstep (se 2 (by rfl) ⟨735315, by rfl⟩ : syracuseStep 1960841 = 1470631) B1470631
theorem B2207047 : Blo 1305971 2207047 := bstep (se 1 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 2207047 = 3310571) B3310571
theorem B214561001 : Blo 1305971 214561001 := bstep (se 2 (by rfl) ⟨80460375, by rfl⟩ : syracuseStep 214561001 = 160920751) B160920751
theorem B4412123 : Blo 1305971 4412123 := bstep (se 1 (by rfl) ⟨3309092, by rfl⟩ : syracuseStep 4412123 = 6618185) B6618185
theorem B31798889 : Blo 1305971 31798889 := bstep (se 2 (by rfl) ⟨11924583, by rfl⟩ : syracuseStep 31798889 = 23849167) B23849167
theorem B85884583 : Blo 1305971 85884583 := bstep (se 1 (by rfl) ⟨64413437, by rfl⟩ : syracuseStep 85884583 = 128826875) B128826875
theorem B2940623 : Blo 1305971 2940623 := bstep (se 1 (by rfl) ⟨2205467, by rfl⟩ : syracuseStep 2940623 = 4410935) B4410935
theorem B143040667 : Blo 1305971 143040667 := bstep (se 1 (by rfl) ⟨107280500, by rfl⟩ : syracuseStep 143040667 = 214561001) B214561001
theorem B38224199 : Blo 1305971 38224199 := bstep (se 1 (by rfl) ⟨28668149, by rfl⟩ : syracuseStep 38224199 = 57336299) B57336299
theorem B2941415 : Blo 1305971 2941415 := bstep (se 1 (by rfl) ⟨2206061, by rfl⟩ : syracuseStep 2941415 = 4412123) B4412123
theorem B386532283 : Blo 1305971 386532283 := bstep (se 1 (by rfl) ⟨289899212, by rfl⟩ : syracuseStep 386532283 = 579798425) B579798425
theorem B2942729 : Blo 1305971 2942729 := bstep (se 2 (by rfl) ⟨1103523, by rfl⟩ : syracuseStep 2942729 = 2207047) B2207047
theorem B1960415 : Blo 1305971 1960415 := bstep (se 1 (by rfl) ⟨1470311, by rfl⟩ : syracuseStep 1960415 = 2940623) B2940623
theorem B1306159 : Blo 1305971 1306159 := bstep (se 1 (by rfl) ⟨979619, by rfl⟩ : syracuseStep 1306159 = 1959239) B1959239
theorem B1307227 : Blo 1305971 1307227 := bstep (se 1 (by rfl) ⟨980420, by rfl⟩ : syracuseStep 1307227 = 1960841) B1960841
theorem B114512777 : Blo 1305971 114512777 := bstep (se 2 (by rfl) ⟨42942291, by rfl⟩ : syracuseStep 114512777 = 85884583) B85884583
theorem B2938751 : Blo 1305971 2938751 := bstep (se 1 (by rfl) ⟨2204063, by rfl⟩ : syracuseStep 2938751 = 4408127) B4408127
theorem B21199259 : Blo 1305971 21199259 := bstep (se 1 (by rfl) ⟨15899444, by rfl⟩ : syracuseStep 21199259 = 31798889) B31798889
theorem B76341851 : Blo 1305971 76341851 := bstep (se 1 (by rfl) ⟨57256388, by rfl⟩ : syracuseStep 76341851 = 114512777) B114512777
theorem B515376377 : Blo 1305971 515376377 := bstep (se 2 (by rfl) ⟨193266141, by rfl⟩ : syracuseStep 515376377 = 386532283) B386532283
theorem B1959167 : Blo 1305971 1959167 := bstep (se 1 (by rfl) ⟨1469375, by rfl⟩ : syracuseStep 1959167 = 2938751) B2938751
theorem B14132839 : Blo 1305971 14132839 := bstep (se 1 (by rfl) ⟨10599629, by rfl⟩ : syracuseStep 14132839 = 21199259) B21199259
theorem B190720889 : Blo 1305971 190720889 := bstep (se 2 (by rfl) ⟨71520333, by rfl⟩ : syracuseStep 190720889 = 143040667) B143040667
theorem B1960943 : Blo 1305971 1960943 := bstep (se 1 (by rfl) ⟨1470707, by rfl⟩ : syracuseStep 1960943 = 2941415) B2941415
theorem B1961819 : Blo 1305971 1961819 := bstep (se 1 (by rfl) ⟨1471364, by rfl⟩ : syracuseStep 1961819 = 2942729) B2942729
theorem B1306943 : Blo 1305971 1306943 := bstep (se 1 (by rfl) ⟨980207, by rfl⟩ : syracuseStep 1306943 = 1960415) B1960415
theorem B25482799 : Blo 1305971 25482799 := bstep (se 1 (by rfl) ⟨19112099, by rfl⟩ : syracuseStep 25482799 = 38224199) B38224199
theorem B18843785 : Blo 1305971 18843785 := bstep (se 2 (by rfl) ⟨7066419, by rfl⟩ : syracuseStep 18843785 = 14132839) B14132839
theorem B343584251 : Blo 1305971 343584251 := bstep (se 1 (by rfl) ⟨257688188, by rfl⟩ : syracuseStep 343584251 = 515376377) B515376377
theorem B1306111 : Blo 1305971 1306111 := bstep (se 1 (by rfl) ⟨979583, by rfl⟩ : syracuseStep 1306111 = 1959167) B1959167
theorem B1307295 : Blo 1305971 1307295 := bstep (se 1 (by rfl) ⟨980471, by rfl⟩ : syracuseStep 1307295 = 1960943) B1960943
theorem B33977065 : Blo 1305971 33977065 := bstep (se 2 (by rfl) ⟨12741399, by rfl⟩ : syracuseStep 33977065 = 25482799) B25482799
theorem B1307879 : Blo 1305971 1307879 := bstep (se 1 (by rfl) ⟨980909, by rfl⟩ : syracuseStep 1307879 = 1961819) B1961819
theorem B50894567 : Blo 1305971 50894567 := bstep (se 1 (by rfl) ⟨38170925, by rfl⟩ : syracuseStep 50894567 = 76341851) B76341851
theorem B127147259 : Blo 1305971 127147259 := bstep (se 1 (by rfl) ⟨95360444, by rfl⟩ : syracuseStep 127147259 = 190720889) B190720889
theorem B45302753 : Blo 1305971 45302753 := bstep (se 2 (by rfl) ⟨16988532, by rfl⟩ : syracuseStep 45302753 = 33977065) B33977065
theorem B84764839 : Blo 1305971 84764839 := bstep (se 1 (by rfl) ⟨63573629, by rfl⟩ : syracuseStep 84764839 = 127147259) B127147259
theorem B12562523 : Blo 1305971 12562523 := bstep (se 1 (by rfl) ⟨9421892, by rfl⟩ : syracuseStep 12562523 = 18843785) B18843785
theorem B33929711 : Blo 1305971 33929711 := bstep (se 1 (by rfl) ⟨25447283, by rfl⟩ : syracuseStep 33929711 = 50894567) B50894567
theorem B229056167 : Blo 1305971 229056167 := bstep (se 1 (by rfl) ⟨171792125, by rfl⟩ : syracuseStep 229056167 = 343584251) B343584251
theorem B22619807 : Blo 1305971 22619807 := bstep (se 1 (by rfl) ⟨16964855, by rfl⟩ : syracuseStep 22619807 = 33929711) B33929711
theorem B8375015 : Blo 1305971 8375015 := bstep (se 1 (by rfl) ⟨6281261, by rfl⟩ : syracuseStep 8375015 = 12562523) B12562523
theorem B113019785 : Blo 1305971 113019785 := bstep (se 2 (by rfl) ⟨42382419, by rfl⟩ : syracuseStep 113019785 = 84764839) B84764839
theorem B152704111 : Blo 1305971 152704111 := bstep (se 1 (by rfl) ⟨114528083, by rfl⟩ : syracuseStep 152704111 = 229056167) B229056167
theorem B30201835 : Blo 1305971 30201835 := bstep (se 1 (by rfl) ⟨22651376, by rfl⟩ : syracuseStep 30201835 = 45302753) B45302753
theorem B203605481 : Blo 1305971 203605481 := bstep (se 2 (by rfl) ⟨76352055, by rfl⟩ : syracuseStep 203605481 = 152704111) B152704111
theorem B5583343 : Blo 1305971 5583343 := bstep (se 1 (by rfl) ⟨4187507, by rfl⟩ : syracuseStep 5583343 = 8375015) B8375015
theorem B75346523 : Blo 1305971 75346523 := bstep (se 1 (by rfl) ⟨56509892, by rfl⟩ : syracuseStep 75346523 = 113019785) B113019785
theorem B40269113 : Blo 1305971 40269113 := bstep (se 2 (by rfl) ⟨15100917, by rfl⟩ : syracuseStep 40269113 = 30201835) B30201835
theorem B15079871 : Blo 1305971 15079871 := bstep (se 1 (by rfl) ⟨11309903, by rfl⟩ : syracuseStep 15079871 = 22619807) B22619807
theorem B26846075 : Blo 1305971 26846075 := bstep (se 1 (by rfl) ⟨20134556, by rfl⟩ : syracuseStep 26846075 = 40269113) B40269113
theorem B10053247 : Blo 1305971 10053247 := bstep (se 1 (by rfl) ⟨7539935, by rfl⟩ : syracuseStep 10053247 = 15079871) B15079871
theorem B135736987 : Blo 1305971 135736987 := bstep (se 1 (by rfl) ⟨101802740, by rfl⟩ : syracuseStep 135736987 = 203605481) B203605481
theorem B50231015 : Blo 1305971 50231015 := bstep (se 1 (by rfl) ⟨37673261, by rfl⟩ : syracuseStep 50231015 = 75346523) B75346523
theorem B7444457 : Blo 1305971 7444457 := bstep (se 2 (by rfl) ⟨2791671, by rfl⟩ : syracuseStep 7444457 = 5583343) B5583343
theorem B13404329 : Blo 1305971 13404329 := bstep (se 2 (by rfl) ⟨5026623, by rfl⟩ : syracuseStep 13404329 = 10053247) B10053247
theorem B180982649 : Blo 1305971 180982649 := bstep (se 2 (by rfl) ⟨67868493, by rfl⟩ : syracuseStep 180982649 = 135736987) B135736987
theorem B17897383 : Blo 1305971 17897383 := bstep (se 1 (by rfl) ⟨13423037, by rfl⟩ : syracuseStep 17897383 = 26846075) B26846075
theorem B33487343 : Blo 1305971 33487343 := bstep (se 1 (by rfl) ⟨25115507, by rfl⟩ : syracuseStep 33487343 = 50231015) B50231015
theorem B4962971 : Blo 1305971 4962971 := bstep (se 1 (by rfl) ⟨3722228, by rfl⟩ : syracuseStep 4962971 = 7444457) B7444457
theorem B22324895 : Blo 1305971 22324895 := bstep (se 1 (by rfl) ⟨16743671, by rfl⟩ : syracuseStep 22324895 = 33487343) B33487343
theorem B120655099 : Blo 1305971 120655099 := bstep (se 1 (by rfl) ⟨90491324, by rfl⟩ : syracuseStep 120655099 = 180982649) B180982649
theorem B8936219 : Blo 1305971 8936219 := bstep (se 1 (by rfl) ⟨6702164, by rfl⟩ : syracuseStep 8936219 = 13404329) B13404329
theorem B3308647 : Blo 1305971 3308647 := bstep (se 1 (by rfl) ⟨2481485, by rfl⟩ : syracuseStep 3308647 = 4962971) B4962971
theorem B23863177 : Blo 1305971 23863177 := bstep (se 2 (by rfl) ⟨8948691, by rfl⟩ : syracuseStep 23863177 = 17897383) B17897383
theorem B5957479 : Blo 1305971 5957479 := bstep (se 1 (by rfl) ⟨4468109, by rfl⟩ : syracuseStep 5957479 = 8936219) B8936219
theorem B4411529 : Blo 1305971 4411529 := bstep (se 2 (by rfl) ⟨1654323, by rfl⟩ : syracuseStep 4411529 = 3308647) B3308647
theorem B14883263 : Blo 1305971 14883263 := bstep (se 1 (by rfl) ⟨11162447, by rfl⟩ : syracuseStep 14883263 = 22324895) B22324895
theorem B160873465 : Blo 1305971 160873465 := bstep (se 2 (by rfl) ⟨60327549, by rfl⟩ : syracuseStep 160873465 = 120655099) B120655099
theorem B127270277 : Blo 1305971 127270277 := bstep (se 4 (by rfl) ⟨11931588, by rfl⟩ : syracuseStep 127270277 = 23863177) B23863177
theorem B2941019 : Blo 1305971 2941019 := bstep (se 1 (by rfl) ⟨2205764, by rfl⟩ : syracuseStep 2941019 = 4411529) B4411529
theorem B9922175 : Blo 1305971 9922175 := bstep (se 1 (by rfl) ⟨7441631, by rfl⟩ : syracuseStep 9922175 = 14883263) B14883263
theorem B84846851 : Blo 1305971 84846851 := bstep (se 1 (by rfl) ⟨63635138, by rfl⟩ : syracuseStep 84846851 = 127270277) B127270277
theorem B7943305 : Blo 1305971 7943305 := bstep (se 2 (by rfl) ⟨2978739, by rfl⟩ : syracuseStep 7943305 = 5957479) B5957479
theorem B214497953 : Blo 1305971 214497953 := bstep (se 2 (by rfl) ⟨80436732, by rfl⟩ : syracuseStep 214497953 = 160873465) B160873465
theorem B1960679 : Blo 1305971 1960679 := bstep (se 1 (by rfl) ⟨1470509, by rfl⟩ : syracuseStep 1960679 = 2941019) B2941019
theorem B6614783 : Blo 1305971 6614783 := bstep (se 1 (by rfl) ⟨4961087, by rfl⟩ : syracuseStep 6614783 = 9922175) B9922175
theorem B56564567 : Blo 1305971 56564567 := bstep (se 1 (by rfl) ⟨42423425, by rfl⟩ : syracuseStep 56564567 = 84846851) B84846851
theorem B10591073 : Blo 1305971 10591073 := bstep (se 2 (by rfl) ⟨3971652, by rfl⟩ : syracuseStep 10591073 = 7943305) B7943305
theorem B142998635 : Blo 1305971 142998635 := bstep (se 1 (by rfl) ⟨107248976, by rfl⟩ : syracuseStep 142998635 = 214497953) B214497953
theorem B37709711 : Blo 1305971 37709711 := bstep (se 1 (by rfl) ⟨28282283, by rfl⟩ : syracuseStep 37709711 = 56564567) B56564567
theorem B95332423 : Blo 1305971 95332423 := bstep (se 1 (by rfl) ⟨71499317, by rfl⟩ : syracuseStep 95332423 = 142998635) B142998635
theorem B4409855 : Blo 1305971 4409855 := bstep (se 1 (by rfl) ⟨3307391, by rfl⟩ : syracuseStep 4409855 = 6614783) B6614783
theorem B1307119 : Blo 1305971 1307119 := bstep (se 1 (by rfl) ⟨980339, by rfl⟩ : syracuseStep 1307119 = 1960679) B1960679
theorem B7060715 : Blo 1305971 7060715 := bstep (se 1 (by rfl) ⟨5295536, by rfl⟩ : syracuseStep 7060715 = 10591073) B10591073
theorem B127109897 : Blo 1305971 127109897 := bstep (se 2 (by rfl) ⟨47666211, by rfl⟩ : syracuseStep 127109897 = 95332423) B95332423
theorem B4707143 : Blo 1305971 4707143 := bstep (se 1 (by rfl) ⟨3530357, by rfl⟩ : syracuseStep 4707143 = 7060715) B7060715
theorem B25139807 : Blo 1305971 25139807 := bstep (se 1 (by rfl) ⟨18854855, by rfl⟩ : syracuseStep 25139807 = 37709711) B37709711
theorem B2939903 : Blo 1305971 2939903 := bstep (se 1 (by rfl) ⟨2204927, by rfl⟩ : syracuseStep 2939903 = 4409855) B4409855
theorem B3138095 : Blo 1305971 3138095 := bstep (se 1 (by rfl) ⟨2353571, by rfl⟩ : syracuseStep 3138095 = 4707143) B4707143
theorem B84739931 : Blo 1305971 84739931 := bstep (se 1 (by rfl) ⟨63554948, by rfl⟩ : syracuseStep 84739931 = 127109897) B127109897
theorem B1959935 : Blo 1305971 1959935 := bstep (se 1 (by rfl) ⟨1469951, by rfl⟩ : syracuseStep 1959935 = 2939903) B2939903
theorem B16759871 : Blo 1305971 16759871 := bstep (se 1 (by rfl) ⟨12569903, by rfl⟩ : syracuseStep 16759871 = 25139807) B25139807
theorem B56493287 : Blo 1305971 56493287 := bstep (se 1 (by rfl) ⟨42369965, by rfl⟩ : syracuseStep 56493287 = 84739931) B84739931
theorem B2092063 : Blo 1305971 2092063 := bstep (se 1 (by rfl) ⟨1569047, by rfl⟩ : syracuseStep 2092063 = 3138095) B3138095
theorem B1306623 : Blo 1305971 1306623 := bstep (se 1 (by rfl) ⟨979967, by rfl⟩ : syracuseStep 1306623 = 1959935) B1959935
theorem B11173247 : Blo 1305971 11173247 := bstep (se 1 (by rfl) ⟨8379935, by rfl⟩ : syracuseStep 11173247 = 16759871) B16759871
theorem B7448831 : Blo 1305971 7448831 := bstep (se 1 (by rfl) ⟨5586623, by rfl⟩ : syracuseStep 7448831 = 11173247) B11173247
theorem B37662191 : Blo 1305971 37662191 := bstep (se 1 (by rfl) ⟨28246643, by rfl⟩ : syracuseStep 37662191 = 56493287) B56493287
theorem B2789417 : Blo 1305971 2789417 := bstep (se 2 (by rfl) ⟨1046031, by rfl⟩ : syracuseStep 2789417 = 2092063) B2092063
theorem B1859611 : Blo 1305971 1859611 := bstep (se 1 (by rfl) ⟨1394708, by rfl⟩ : syracuseStep 1859611 = 2789417) B2789417
theorem B4965887 : Blo 1305971 4965887 := bstep (se 1 (by rfl) ⟨3724415, by rfl⟩ : syracuseStep 4965887 = 7448831) B7448831
theorem B25108127 : Blo 1305971 25108127 := bstep (se 1 (by rfl) ⟨18831095, by rfl⟩ : syracuseStep 25108127 = 37662191) B37662191
theorem B3310591 : Blo 1305971 3310591 := bstep (se 1 (by rfl) ⟨2482943, by rfl⟩ : syracuseStep 3310591 = 4965887) B4965887
theorem B16738751 : Blo 1305971 16738751 := bstep (se 1 (by rfl) ⟨12554063, by rfl⟩ : syracuseStep 16738751 = 25108127) B25108127
theorem B2479481 : Blo 1305971 2479481 := bstep (se 2 (by rfl) ⟨929805, by rfl⟩ : syracuseStep 2479481 = 1859611) B1859611
theorem B11159167 : Blo 1305971 11159167 := bstep (se 1 (by rfl) ⟨8369375, by rfl⟩ : syracuseStep 11159167 = 16738751) B16738751
theorem B1652987 : Blo 1305971 1652987 := bstep (se 1 (by rfl) ⟨1239740, by rfl⟩ : syracuseStep 1652987 = 2479481) B2479481
theorem B4414121 : Blo 1305971 4414121 := bstep (se 2 (by rfl) ⟨1655295, by rfl⟩ : syracuseStep 4414121 = 3310591) B3310591
theorem B4407965 : Blo 1305971 4407965 := bstep (se 3 (by rfl) ⟨826493, by rfl⟩ : syracuseStep 4407965 = 1652987) B1652987
theorem B2942747 : Blo 1305971 2942747 := bstep (se 1 (by rfl) ⟨2207060, by rfl⟩ : syracuseStep 2942747 = 4414121) B4414121
theorem B14878889 : Blo 1305971 14878889 := bstep (se 2 (by rfl) ⟨5579583, by rfl⟩ : syracuseStep 14878889 = 11159167) B11159167
theorem B1961831 : Blo 1305971 1961831 := bstep (se 1 (by rfl) ⟨1471373, by rfl⟩ : syracuseStep 1961831 = 2942747) B2942747
theorem B2938643 : Blo 1305971 2938643 := bstep (se 1 (by rfl) ⟨2203982, by rfl⟩ : syracuseStep 2938643 = 4407965) B4407965
theorem B9919259 : Blo 1305971 9919259 := bstep (se 1 (by rfl) ⟨7439444, by rfl⟩ : syracuseStep 9919259 = 14878889) B14878889
theorem B1959095 : Blo 1305971 1959095 := bstep (se 1 (by rfl) ⟨1469321, by rfl⟩ : syracuseStep 1959095 = 2938643) B2938643
theorem B6612839 : Blo 1305971 6612839 := bstep (se 1 (by rfl) ⟨4959629, by rfl⟩ : syracuseStep 6612839 = 9919259) B9919259
theorem B1307887 : Blo 1305971 1307887 := bstep (se 1 (by rfl) ⟨980915, by rfl⟩ : syracuseStep 1307887 = 1961831) B1961831
theorem B4408559 : Blo 1305971 4408559 := bstep (se 1 (by rfl) ⟨3306419, by rfl⟩ : syracuseStep 4408559 = 6612839) B6612839
theorem B1306063 : Blo 1305971 1306063 := bstep (se 1 (by rfl) ⟨979547, by rfl⟩ : syracuseStep 1306063 = 1959095) B1959095
theorem B2939039 : Blo 1305971 2939039 := bstep (se 1 (by rfl) ⟨2204279, by rfl⟩ : syracuseStep 2939039 = 4408559) B4408559
theorem B1959359 : Blo 1305971 1959359 := bstep (se 1 (by rfl) ⟨1469519, by rfl⟩ : syracuseStep 1959359 = 2939039) B2939039
theorem B1306239 : Blo 1305971 1306239 := bstep (se 1 (by rfl) ⟨979679, by rfl⟩ : syracuseStep 1306239 = 1959359) B1959359

theorem C0 (j : ℕ) (h1 : 326492 ≤ j) (h2 : j ≤ 326992) : Blo 1305971 (4 * j + 3) := by
  interval_cases j
  · exact B1305971
  · exact B1305975
  · exact B1305979
  · exact B1305983
  · exact B1305987
  · exact B1305991
  · exact B1305995
  · exact B1305999
  · exact B1306003
  · exact B1306007
  · exact B1306011
  · exact B1306015
  · exact B1306019
  · exact B1306023
  · exact B1306027
  · exact B1306031
  · exact B1306035
  · exact B1306039
  · exact B1306043
  · exact B1306047
  · exact B1306051
  · exact B1306055
  · exact B1306059
  · exact B1306063
  · exact B1306067
  · exact B1306071
  · exact B1306075
  · exact B1306079
  · exact B1306083
  · exact B1306087
  · exact B1306091
  · exact B1306095
  · exact B1306099
  · exact B1306103
  · exact B1306107
  · exact B1306111
  · exact B1306115
  · exact B1306119
  · exact B1306123
  · exact B1306127
  · exact B1306131
  · exact B1306135
  · exact B1306139
  · exact B1306143
  · exact B1306147
  · exact B1306151
  · exact B1306155
  · exact B1306159
  · exact B1306163
  · exact B1306167
  · exact B1306171
  · exact B1306175
  · exact B1306179
  · exact B1306183
  · exact B1306187
  · exact B1306191
  · exact B1306195
  · exact B1306199
  · exact B1306203
  · exact B1306207
  · exact B1306211
  · exact B1306215
  · exact B1306219
  · exact B1306223
  · exact B1306227
  · exact B1306231
  · exact B1306235
  · exact B1306239
  · exact B1306243
  · exact B1306247
  · exact B1306251
  · exact B1306255
  · exact B1306259
  · exact B1306263
  · exact B1306267
  · exact B1306271
  · exact B1306275
  · exact B1306279
  · exact B1306283
  · exact B1306287
  · exact B1306291
  · exact B1306295
  · exact B1306299
  · exact B1306303
  · exact B1306307
  · exact B1306311
  · exact B1306315
  · exact B1306319
  · exact B1306323
  · exact B1306327
  · exact B1306331
  · exact B1306335
  · exact B1306339
  · exact B1306343
  · exact B1306347
  · exact B1306351
  · exact B1306355
  · exact B1306359
  · exact B1306363
  · exact B1306367
  · exact B1306371
  · exact B1306375
  · exact B1306379
  · exact B1306383
  · exact B1306387
  · exact B1306391
  · exact B1306395
  · exact B1306399
  · exact B1306403
  · exact B1306407
  · exact B1306411
  · exact B1306415
  · exact B1306419
  · exact B1306423
  · exact B1306427
  · exact B1306431
  · exact B1306435
  · exact B1306439
  · exact B1306443
  · exact B1306447
  · exact B1306451
  · exact B1306455
  · exact B1306459
  · exact B1306463
  · exact B1306467
  · exact B1306471
  · exact B1306475
  · exact B1306479
  · exact B1306483
  · exact B1306487
  · exact B1306491
  · exact B1306495
  · exact B1306499
  · exact B1306503
  · exact B1306507
  · exact B1306511
  · exact B1306515
  · exact B1306519
  · exact B1306523
  · exact B1306527
  · exact B1306531
  · exact B1306535
  · exact B1306539
  · exact B1306543
  · exact B1306547
  · exact B1306551
  · exact B1306555
  · exact B1306559
  · exact B1306563
  · exact B1306567
  · exact B1306571
  · exact B1306575
  · exact B1306579
  · exact B1306583
  · exact B1306587
  · exact B1306591
  · exact B1306595
  · exact B1306599
  · exact B1306603
  · exact B1306607
  · exact B1306611
  · exact B1306615
  · exact B1306619
  · exact B1306623
  · exact B1306627
  · exact B1306631
  · exact B1306635
  · exact B1306639
  · exact B1306643
  · exact B1306647
  · exact B1306651
  · exact B1306655
  · exact B1306659
  · exact B1306663
  · exact B1306667
  · exact B1306671
  · exact B1306675
  · exact B1306679
  · exact B1306683
  · exact B1306687
  · exact B1306691
  · exact B1306695
  · exact B1306699
  · exact B1306703
  · exact B1306707
  · exact B1306711
  · exact B1306715
  · exact B1306719
  · exact B1306723
  · exact B1306727
  · exact B1306731
  · exact B1306735
  · exact B1306739
  · exact B1306743
  · exact B1306747
  · exact B1306751
  · exact B1306755
  · exact B1306759
  · exact B1306763
  · exact B1306767
  · exact B1306771
  · exact B1306775
  · exact B1306779
  · exact B1306783
  · exact B1306787
  · exact B1306791
  · exact B1306795
  · exact B1306799
  · exact B1306803
  · exact B1306807
  · exact B1306811
  · exact B1306815
  · exact B1306819
  · exact B1306823
  · exact B1306827
  · exact B1306831
  · exact B1306835
  · exact B1306839
  · exact B1306843
  · exact B1306847
  · exact B1306851
  · exact B1306855
  · exact B1306859
  · exact B1306863
  · exact B1306867
  · exact B1306871
  · exact B1306875
  · exact B1306879
  · exact B1306883
  · exact B1306887
  · exact B1306891
  · exact B1306895
  · exact B1306899
  · exact B1306903
  · exact B1306907
  · exact B1306911
  · exact B1306915
  · exact B1306919
  · exact B1306923
  · exact B1306927
  · exact B1306931
  · exact B1306935
  · exact B1306939
  · exact B1306943
  · exact B1306947
  · exact B1306951
  · exact B1306955
  · exact B1306959
  · exact B1306963
  · exact B1306967
  · exact B1306971
  · exact B1306975
  · exact B1306979
  · exact B1306983
  · exact B1306987
  · exact B1306991
  · exact B1306995
  · exact B1306999
  · exact B1307003
  · exact B1307007
  · exact B1307011
  · exact B1307015
  · exact B1307019
  · exact B1307023
  · exact B1307027
  · exact B1307031
  · exact B1307035
  · exact B1307039
  · exact B1307043
  · exact B1307047
  · exact B1307051
  · exact B1307055
  · exact B1307059
  · exact B1307063
  · exact B1307067
  · exact B1307071
  · exact B1307075
  · exact B1307079
  · exact B1307083
  · exact B1307087
  · exact B1307091
  · exact B1307095
  · exact B1307099
  · exact B1307103
  · exact B1307107
  · exact B1307111
  · exact B1307115
  · exact B1307119
  · exact B1307123
  · exact B1307127
  · exact B1307131
  · exact B1307135
  · exact B1307139
  · exact B1307143
  · exact B1307147
  · exact B1307151
  · exact B1307155
  · exact B1307159
  · exact B1307163
  · exact B1307167
  · exact B1307171
  · exact B1307175
  · exact B1307179
  · exact B1307183
  · exact B1307187
  · exact B1307191
  · exact B1307195
  · exact B1307199
  · exact B1307203
  · exact B1307207
  · exact B1307211
  · exact B1307215
  · exact B1307219
  · exact B1307223
  · exact B1307227
  · exact B1307231
  · exact B1307235
  · exact B1307239
  · exact B1307243
  · exact B1307247
  · exact B1307251
  · exact B1307255
  · exact B1307259
  · exact B1307263
  · exact B1307267
  · exact B1307271
  · exact B1307275
  · exact B1307279
  · exact B1307283
  · exact B1307287
  · exact B1307291
  · exact B1307295
  · exact B1307299
  · exact B1307303
  · exact B1307307
  · exact B1307311
  · exact B1307315
  · exact B1307319
  · exact B1307323
  · exact B1307327
  · exact B1307331
  · exact B1307335
  · exact B1307339
  · exact B1307343
  · exact B1307347
  · exact B1307351
  · exact B1307355
  · exact B1307359
  · exact B1307363
  · exact B1307367
  · exact B1307371
  · exact B1307375
  · exact B1307379
  · exact B1307383
  · exact B1307387
  · exact B1307391
  · exact B1307395
  · exact B1307399
  · exact B1307403
  · exact B1307407
  · exact B1307411
  · exact B1307415
  · exact B1307419
  · exact B1307423
  · exact B1307427
  · exact B1307431
  · exact B1307435
  · exact B1307439
  · exact B1307443
  · exact B1307447
  · exact B1307451
  · exact B1307455
  · exact B1307459
  · exact B1307463
  · exact B1307467
  · exact B1307471
  · exact B1307475
  · exact B1307479
  · exact B1307483
  · exact B1307487
  · exact B1307491
  · exact B1307495
  · exact B1307499
  · exact B1307503
  · exact B1307507
  · exact B1307511
  · exact B1307515
  · exact B1307519
  · exact B1307523
  · exact B1307527
  · exact B1307531
  · exact B1307535
  · exact B1307539
  · exact B1307543
  · exact B1307547
  · exact B1307551
  · exact B1307555
  · exact B1307559
  · exact B1307563
  · exact B1307567
  · exact B1307571
  · exact B1307575
  · exact B1307579
  · exact B1307583
  · exact B1307587
  · exact B1307591
  · exact B1307595
  · exact B1307599
  · exact B1307603
  · exact B1307607
  · exact B1307611
  · exact B1307615
  · exact B1307619
  · exact B1307623
  · exact B1307627
  · exact B1307631
  · exact B1307635
  · exact B1307639
  · exact B1307643
  · exact B1307647
  · exact B1307651
  · exact B1307655
  · exact B1307659
  · exact B1307663
  · exact B1307667
  · exact B1307671
  · exact B1307675
  · exact B1307679
  · exact B1307683
  · exact B1307687
  · exact B1307691
  · exact B1307695
  · exact B1307699
  · exact B1307703
  · exact B1307707
  · exact B1307711
  · exact B1307715
  · exact B1307719
  · exact B1307723
  · exact B1307727
  · exact B1307731
  · exact B1307735
  · exact B1307739
  · exact B1307743
  · exact B1307747
  · exact B1307751
  · exact B1307755
  · exact B1307759
  · exact B1307763
  · exact B1307767
  · exact B1307771
  · exact B1307775
  · exact B1307779
  · exact B1307783
  · exact B1307787
  · exact B1307791
  · exact B1307795
  · exact B1307799
  · exact B1307803
  · exact B1307807
  · exact B1307811
  · exact B1307815
  · exact B1307819
  · exact B1307823
  · exact B1307827
  · exact B1307831
  · exact B1307835
  · exact B1307839
  · exact B1307843
  · exact B1307847
  · exact B1307851
  · exact B1307855
  · exact B1307859
  · exact B1307863
  · exact B1307867
  · exact B1307871
  · exact B1307875
  · exact B1307879
  · exact B1307883
  · exact B1307887
  · exact B1307891
  · exact B1307895
  · exact B1307899
  · exact B1307903
  · exact B1307907
  · exact B1307911
  · exact B1307915
  · exact B1307919
  · exact B1307923
  · exact B1307927
  · exact B1307931
  · exact B1307935
  · exact B1307939
  · exact B1307943
  · exact B1307947
  · exact B1307951
  · exact B1307955
  · exact B1307959
  · exact B1307963
  · exact B1307967
  · exact B1307971

theorem solution (m : ℕ) (hlo : 1305971 ≤ m) (hhi : m ≤ 1307971) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 326492 ≤ j := by omega
    have hj2 : j ≤ 326992 := by omega
    have hb : Blo 1305971 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
