-- Prove2me | solution 1 for syracuse_descends_range_908576_912576
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:50.556554+00:00
-- url     : https://prove2.me/submissions/a19a2f82-8ab4-4120-928a-31ff278b1b34

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


theorem B7110773 : Blo 908576 7110773 := bbase (se 5 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 7110773 = 666635) (by norm_num)
theorem B1638605 : Blo 908576 1638605 := bbase (se 3 (by rfl) ⟨307238, by rfl⟩ : syracuseStep 1638605 = 614477) (by norm_num)
theorem B2588885 : Blo 908576 2588885 := bbase (se 7 (by rfl) ⟨30338, by rfl⟩ : syracuseStep 2588885 = 60677) (by norm_num)
theorem B2916661 : Blo 908576 2916661 := bbase (se 5 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 2916661 = 273437) (by norm_num)
theorem B1638893 : Blo 908576 1638893 := bbase (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) (by norm_num)
theorem B2589317 : Blo 908576 2589317 := bbase (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) (by norm_num)
theorem B5833397 : Blo 908576 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B2917109 : Blo 908576 2917109 := bbase (se 5 (by rfl) ⟨136739, by rfl⟩ : syracuseStep 2917109 = 273479) (by norm_num)
theorem B2458565 : Blo 908576 2458565 := bbase (se 4 (by rfl) ⟨230490, by rfl⟩ : syracuseStep 2458565 = 460981) (by norm_num)
theorem B6554645 : Blo 908576 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B2590069 : Blo 908576 2590069 := bbase (se 5 (by rfl) ⟨121409, by rfl⟩ : syracuseStep 2590069 = 242819) (by norm_num)
theorem B3278245 : Blo 908576 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B3507781 : Blo 908576 3507781 := bbase (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) (by norm_num)
theorem B1640045 : Blo 908576 1640045 := bbase (se 3 (by rfl) ⟨307508, by rfl⟩ : syracuseStep 1640045 = 615017) (by norm_num)
theorem B1640125 : Blo 908576 1640125 := bbase (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) (by norm_num)
theorem B985105 : Blo 908576 985105 := bbase (se 2 (by rfl) ⟨369414, by rfl⟩ : syracuseStep 985105 = 738829) (by norm_num)
theorem B3278981 : Blo 908576 3278981 := bbase (se 4 (by rfl) ⟨307404, by rfl⟩ : syracuseStep 3278981 = 614809) (by norm_num)
theorem B9832661 : Blo 908576 9832661 := bbase (se 7 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 9832661 = 230453) (by norm_num)
theorem B4262213 : Blo 908576 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B2623861 : Blo 908576 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B985645 : Blo 908576 985645 := bbase (se 3 (by rfl) ⟨184808, by rfl⟩ : syracuseStep 985645 = 369617) (by norm_num)
theorem B1641205 : Blo 908576 1641205 := bbase (se 5 (by rfl) ⟨76931, by rfl⟩ : syracuseStep 1641205 = 153863) (by norm_num)
theorem B1641293 : Blo 908576 1641293 := bbase (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) (by norm_num)
theorem B986041 : Blo 908576 986041 := bbase (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) (by norm_num)
theorem B2919365 : Blo 908576 2919365 := bbase (se 4 (by rfl) ⟨273690, by rfl⟩ : syracuseStep 2919365 = 547381) (by norm_num)
theorem B1149977 : Blo 908576 1149977 := bbase (se 2 (by rfl) ⟨431241, by rfl⟩ : syracuseStep 1149977 = 862483) (by norm_num)
theorem B1150033 : Blo 908576 1150033 := bbase (se 2 (by rfl) ⟨431262, by rfl⟩ : syracuseStep 1150033 = 862525) (by norm_num)
theorem B5049461 : Blo 908576 5049461 := bbase (se 5 (by rfl) ⟨236693, by rfl⟩ : syracuseStep 5049461 = 473387) (by norm_num)
theorem B6917237 : Blo 908576 6917237 := bbase (se 5 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 6917237 = 648491) (by norm_num)
theorem B1150129 : Blo 908576 1150129 := bbase (se 2 (by rfl) ⟨431298, by rfl⟩ : syracuseStep 1150129 = 862597) (by norm_num)
theorem B1182937 : Blo 908576 1182937 := bbase (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) (by norm_num)
theorem B1051969 : Blo 908576 1051969 := bbase (se 2 (by rfl) ⟨394488, by rfl⟩ : syracuseStep 1051969 = 788977) (by norm_num)
theorem B1641797 : Blo 908576 1641797 := bbase (se 4 (by rfl) ⟨153918, by rfl⟩ : syracuseStep 1641797 = 307837) (by norm_num)
theorem B1150301 : Blo 908576 1150301 := bbase (se 3 (by rfl) ⟨215681, by rfl⟩ : syracuseStep 1150301 = 431363) (by norm_num)
theorem B1969525 : Blo 908576 1969525 := bbase (se 5 (by rfl) ⟨92321, by rfl⟩ : syracuseStep 1969525 = 184643) (by norm_num)
theorem B1150357 : Blo 908576 1150357 := bbase (se 6 (by rfl) ⟨26961, by rfl⟩ : syracuseStep 1150357 = 53923) (by norm_num)
theorem B920989 : Blo 908576 920989 := bbase (se 3 (by rfl) ⟨172685, by rfl⟩ : syracuseStep 920989 = 345371) (by norm_num)
theorem B7376341 : Blo 908576 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B1150453 : Blo 908576 1150453 := bbase (se 5 (by rfl) ⟨53927, by rfl⟩ : syracuseStep 1150453 = 107855) (by norm_num)
theorem B2428453 : Blo 908576 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B1150625 : Blo 908576 1150625 := bbase (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) (by norm_num)
theorem B1150681 : Blo 908576 1150681 := bbase (se 2 (by rfl) ⟨431505, by rfl⟩ : syracuseStep 1150681 = 863011) (by norm_num)
theorem B1150777 : Blo 908576 1150777 := bbase (se 2 (by rfl) ⟨431541, by rfl⟩ : syracuseStep 1150777 = 863083) (by norm_num)
theorem B986941 : Blo 908576 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B1150949 : Blo 908576 1150949 := bbase (se 4 (by rfl) ⟨107901, by rfl⟩ : syracuseStep 1150949 = 215803) (by norm_num)
theorem B2101277 : Blo 908576 2101277 := bbase (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) (by norm_num)
theorem B1151005 : Blo 908576 1151005 := bbase (se 3 (by rfl) ⟨215813, by rfl⟩ : syracuseStep 1151005 = 431627) (by norm_num)
theorem B2101349 : Blo 908576 2101349 := bbase (se 4 (by rfl) ⟨197001, by rfl⟩ : syracuseStep 2101349 = 394003) (by norm_num)
theorem B1151101 : Blo 908576 1151101 := bbase (se 3 (by rfl) ⟨215831, by rfl⟩ : syracuseStep 1151101 = 431663) (by norm_num)
theorem B2592917 : Blo 908576 2592917 := bbase (se 6 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 2592917 = 121543) (by norm_num)
theorem B1151273 : Blo 908576 1151273 := bbase (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) (by norm_num)
theorem B1151329 : Blo 908576 1151329 := bbase (se 2 (by rfl) ⟨431748, by rfl⟩ : syracuseStep 1151329 = 863497) (by norm_num)
theorem B987533 : Blo 908576 987533 := bbase (se 3 (by rfl) ⟨185162, by rfl⟩ : syracuseStep 987533 = 370325) (by norm_num)
theorem B1151425 : Blo 908576 1151425 := bbase (se 2 (by rfl) ⟨431784, by rfl⟩ : syracuseStep 1151425 = 863569) (by norm_num)
theorem B1151597 : Blo 908576 1151597 := bbase (se 3 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 1151597 = 431849) (by norm_num)
theorem B922237 : Blo 908576 922237 := bbase (se 3 (by rfl) ⟨172919, by rfl⟩ : syracuseStep 922237 = 345839) (by norm_num)
theorem B1249933 : Blo 908576 1249933 := bbase (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) (by norm_num)
theorem B1151653 : Blo 908576 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B3117797 : Blo 908576 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1151749 : Blo 908576 1151749 := bbase (se 4 (by rfl) ⟨107976, by rfl⟩ : syracuseStep 1151749 = 215953) (by norm_num)
theorem B5182325 : Blo 908576 5182325 := bbase (se 5 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 5182325 = 485843) (by norm_num)
theorem B1151921 : Blo 908576 1151921 := bbase (se 2 (by rfl) ⟨431970, by rfl⟩ : syracuseStep 1151921 = 863941) (by norm_num)
theorem B1151977 : Blo 908576 1151977 := bbase (se 2 (by rfl) ⟨431991, by rfl⟩ : syracuseStep 1151977 = 863983) (by norm_num)
theorem B1152073 : Blo 908576 1152073 := bbase (se 2 (by rfl) ⟨432027, by rfl⟩ : syracuseStep 1152073 = 864055) (by norm_num)
theorem B1053865 : Blo 908576 1053865 := bbase (se 2 (by rfl) ⟨395199, by rfl⟩ : syracuseStep 1053865 = 790399) (by norm_num)
theorem B1152245 : Blo 908576 1152245 := bbase (se 5 (by rfl) ⟨54011, by rfl⟩ : syracuseStep 1152245 = 108023) (by norm_num)
theorem B1152301 : Blo 908576 1152301 := bbase (se 3 (by rfl) ⟨216056, by rfl⟩ : syracuseStep 1152301 = 432113) (by norm_num)
theorem B2594101 : Blo 908576 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B1152397 : Blo 908576 1152397 := bbase (se 3 (by rfl) ⟨216074, by rfl⟩ : syracuseStep 1152397 = 432149) (by norm_num)
theorem B923081 : Blo 908576 923081 := bbase (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) (by norm_num)
theorem B2594261 : Blo 908576 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B1643989 : Blo 908576 1643989 := bbase (se 7 (by rfl) ⟨19265, by rfl⟩ : syracuseStep 1643989 = 38531) (by norm_num)
theorem B1152569 : Blo 908576 1152569 := bbase (se 2 (by rfl) ⟨432213, by rfl⟩ : syracuseStep 1152569 = 864427) (by norm_num)
theorem B1152625 : Blo 908576 1152625 := bbase (se 2 (by rfl) ⟨432234, by rfl⟩ : syracuseStep 1152625 = 864469) (by norm_num)
theorem B1644197 : Blo 908576 1644197 := bbase (se 4 (by rfl) ⟨154143, by rfl⟩ : syracuseStep 1644197 = 308287) (by norm_num)
theorem B2594501 : Blo 908576 2594501 := bbase (se 4 (by rfl) ⟨243234, by rfl⟩ : syracuseStep 2594501 = 486469) (by norm_num)
theorem B1152721 : Blo 908576 1152721 := bbase (se 2 (by rfl) ⟨432270, by rfl⟩ : syracuseStep 1152721 = 864541) (by norm_num)
theorem B1152893 : Blo 908576 1152893 := bbase (se 3 (by rfl) ⟨216167, by rfl⟩ : syracuseStep 1152893 = 432335) (by norm_num)
theorem B2594693 : Blo 908576 2594693 := bbase (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) (by norm_num)
theorem B1152949 : Blo 908576 1152949 := bbase (se 5 (by rfl) ⟨54044, by rfl⟩ : syracuseStep 1152949 = 108089) (by norm_num)
theorem B2299853 : Blo 908576 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B2463701 : Blo 908576 2463701 := bbase (se 7 (by rfl) ⟨28871, by rfl⟩ : syracuseStep 2463701 = 57743) (by norm_num)
theorem B923609 : Blo 908576 923609 := bbase (se 2 (by rfl) ⟨346353, by rfl⟩ : syracuseStep 923609 = 692707) (by norm_num)
theorem B2463733 : Blo 908576 2463733 := bbase (se 5 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 2463733 = 230975) (by norm_num)
theorem B1153045 : Blo 908576 1153045 := bbase (se 6 (by rfl) ⟨27024, by rfl⟩ : syracuseStep 1153045 = 54049) (by norm_num)
theorem B2463797 : Blo 908576 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B6559861 : Blo 908576 6559861 := bbase (se 5 (by rfl) ⟨307493, by rfl⟩ : syracuseStep 6559861 = 614987) (by norm_num)
theorem B1153217 : Blo 908576 1153217 := bbase (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) (by norm_num)
theorem B1022161 : Blo 908576 1022161 := bbase (se 2 (by rfl) ⟨383310, by rfl⟩ : syracuseStep 1022161 = 766621) (by norm_num)
theorem B1022197 : Blo 908576 1022197 := bbase (se 5 (by rfl) ⟨47915, by rfl⟩ : syracuseStep 1022197 = 95831) (by norm_num)
theorem B1153273 : Blo 908576 1153273 := bbase (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) (by norm_num)
theorem B1022233 : Blo 908576 1022233 := bbase (se 2 (by rfl) ⟨383337, by rfl⟩ : syracuseStep 1022233 = 766675) (by norm_num)
theorem B2300197 : Blo 908576 2300197 := bbase (se 4 (by rfl) ⟨215643, by rfl⟩ : syracuseStep 2300197 = 431287) (by norm_num)
theorem B1022269 : Blo 908576 1022269 := bbase (se 3 (by rfl) ⟨191675, by rfl⟩ : syracuseStep 1022269 = 383351) (by norm_num)
theorem B17733973 : Blo 908576 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B1153369 : Blo 908576 1153369 := bbase (se 2 (by rfl) ⟨432513, by rfl⟩ : syracuseStep 1153369 = 865027) (by norm_num)
theorem B1022305 : Blo 908576 1022305 := bbase (se 2 (by rfl) ⟨383364, by rfl⟩ : syracuseStep 1022305 = 766729) (by norm_num)
theorem B1382773 : Blo 908576 1382773 := bbase (se 5 (by rfl) ⟨64817, by rfl⟩ : syracuseStep 1382773 = 129635) (by norm_num)
theorem B1022341 : Blo 908576 1022341 := bbase (se 4 (by rfl) ⟨95844, by rfl⟩ : syracuseStep 1022341 = 191689) (by norm_num)
theorem B2300309 : Blo 908576 2300309 := bbase (se 6 (by rfl) ⟨53913, by rfl⟩ : syracuseStep 2300309 = 107827) (by norm_num)
theorem B1022377 : Blo 908576 1022377 := bbase (se 2 (by rfl) ⟨383391, by rfl⟩ : syracuseStep 1022377 = 766783) (by norm_num)
theorem B1022413 : Blo 908576 1022413 := bbase (se 3 (by rfl) ⟨191702, by rfl⟩ : syracuseStep 1022413 = 383405) (by norm_num)
theorem B1022449 : Blo 908576 1022449 := bbase (se 2 (by rfl) ⟨383418, by rfl⟩ : syracuseStep 1022449 = 766837) (by norm_num)
theorem B1153541 : Blo 908576 1153541 := bbase (se 4 (by rfl) ⟨108144, by rfl⟩ : syracuseStep 1153541 = 216289) (by norm_num)
theorem B1022485 : Blo 908576 1022485 := bbase (se 6 (by rfl) ⟨23964, by rfl⟩ : syracuseStep 1022485 = 47929) (by norm_num)
theorem B1022521 : Blo 908576 1022521 := bbase (se 2 (by rfl) ⟨383445, by rfl⟩ : syracuseStep 1022521 = 766891) (by norm_num)
theorem B1153597 : Blo 908576 1153597 := bbase (se 3 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 1153597 = 432599) (by norm_num)
theorem B2300501 : Blo 908576 2300501 := bbase (se 8 (by rfl) ⟨13479, by rfl⟩ : syracuseStep 2300501 = 26959) (by norm_num)
theorem B1022557 : Blo 908576 1022557 := bbase (se 3 (by rfl) ⟨191729, by rfl⟩ : syracuseStep 1022557 = 383459) (by norm_num)
theorem B1022593 : Blo 908576 1022593 := bbase (se 2 (by rfl) ⟨383472, by rfl⟩ : syracuseStep 1022593 = 766945) (by norm_num)
theorem B1153693 : Blo 908576 1153693 := bbase (se 3 (by rfl) ⟨216317, by rfl⟩ : syracuseStep 1153693 = 432635) (by norm_num)
theorem B1022629 : Blo 908576 1022629 := bbase (se 4 (by rfl) ⟨95871, by rfl⟩ : syracuseStep 1022629 = 191743) (by norm_num)
theorem B1022665 : Blo 908576 1022665 := bbase (se 2 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 1022665 = 766999) (by norm_num)
theorem B1022701 : Blo 908576 1022701 := bbase (se 3 (by rfl) ⟨191756, by rfl⟩ : syracuseStep 1022701 = 383513) (by norm_num)
theorem B1022737 : Blo 908576 1022737 := bbase (se 2 (by rfl) ⟨383526, by rfl⟩ : syracuseStep 1022737 = 767053) (by norm_num)
theorem B2923285 : Blo 908576 2923285 := bbase (se 6 (by rfl) ⟨68514, by rfl⟩ : syracuseStep 2923285 = 137029) (by norm_num)
theorem B1022773 : Blo 908576 1022773 := bbase (se 5 (by rfl) ⟨47942, by rfl⟩ : syracuseStep 1022773 = 95885) (by norm_num)
theorem B1153865 : Blo 908576 1153865 := bbase (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) (by norm_num)
theorem B1022809 : Blo 908576 1022809 := bbase (se 2 (by rfl) ⟨383553, by rfl⟩ : syracuseStep 1022809 = 767107) (by norm_num)
theorem B2595685 : Blo 908576 2595685 := bbase (se 4 (by rfl) ⟨243345, by rfl⟩ : syracuseStep 2595685 = 486691) (by norm_num)
theorem B1481573 : Blo 908576 1481573 := bbase (se 4 (by rfl) ⟨138897, by rfl⟩ : syracuseStep 1481573 = 277795) (by norm_num)
theorem B1022845 : Blo 908576 1022845 := bbase (se 3 (by rfl) ⟨191783, by rfl⟩ : syracuseStep 1022845 = 383567) (by norm_num)
theorem B1153921 : Blo 908576 1153921 := bbase (se 2 (by rfl) ⟨432720, by rfl⟩ : syracuseStep 1153921 = 865441) (by norm_num)
theorem B1022881 : Blo 908576 1022881 := bbase (se 2 (by rfl) ⟨383580, by rfl⟩ : syracuseStep 1022881 = 767161) (by norm_num)
theorem B2300845 : Blo 908576 2300845 := bbase (se 3 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 2300845 = 862817) (by norm_num)
theorem B1022917 : Blo 908576 1022917 := bbase (se 4 (by rfl) ⟨95898, by rfl⟩ : syracuseStep 1022917 = 191797) (by norm_num)
theorem B1154017 : Blo 908576 1154017 := bbase (se 2 (by rfl) ⟨432756, by rfl⟩ : syracuseStep 1154017 = 865513) (by norm_num)
theorem B1022953 : Blo 908576 1022953 := bbase (se 2 (by rfl) ⟨383607, by rfl⟩ : syracuseStep 1022953 = 767215) (by norm_num)
theorem B1022989 : Blo 908576 1022989 := bbase (se 3 (by rfl) ⟨191810, by rfl⟩ : syracuseStep 1022989 = 383621) (by norm_num)
theorem B2923541 : Blo 908576 2923541 := bbase (se 6 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 2923541 = 137041) (by norm_num)
theorem B2300957 : Blo 908576 2300957 := bbase (se 3 (by rfl) ⟨431429, by rfl⟩ : syracuseStep 2300957 = 862859) (by norm_num)
theorem B1023025 : Blo 908576 1023025 := bbase (se 2 (by rfl) ⟨383634, by rfl⟩ : syracuseStep 1023025 = 767269) (by norm_num)
theorem B1023061 : Blo 908576 1023061 := bbase (se 8 (by rfl) ⟨5994, by rfl⟩ : syracuseStep 1023061 = 11989) (by norm_num)
theorem B1023097 : Blo 908576 1023097 := bbase (se 2 (by rfl) ⟨383661, by rfl⟩ : syracuseStep 1023097 = 767323) (by norm_num)
theorem B1154189 : Blo 908576 1154189 := bbase (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) (by norm_num)
theorem B10362005 : Blo 908576 10362005 := bbase (se 6 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 10362005 = 485719) (by norm_num)
theorem B1023133 : Blo 908576 1023133 := bbase (se 3 (by rfl) ⟨191837, by rfl⟩ : syracuseStep 1023133 = 383675) (by norm_num)
theorem B1023169 : Blo 908576 1023169 := bbase (se 2 (by rfl) ⟨383688, by rfl⟩ : syracuseStep 1023169 = 767377) (by norm_num)
theorem B1154245 : Blo 908576 1154245 := bbase (se 4 (by rfl) ⟨108210, by rfl⟩ : syracuseStep 1154245 = 216421) (by norm_num)
theorem B2301149 : Blo 908576 2301149 := bbase (se 3 (by rfl) ⟨431465, by rfl⟩ : syracuseStep 2301149 = 862931) (by norm_num)
theorem B1023205 : Blo 908576 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B1023241 : Blo 908576 1023241 := bbase (se 2 (by rfl) ⟨383715, by rfl⟩ : syracuseStep 1023241 = 767431) (by norm_num)
theorem B1154341 : Blo 908576 1154341 := bbase (se 4 (by rfl) ⟨108219, by rfl⟩ : syracuseStep 1154341 = 216439) (by norm_num)
theorem B1023277 : Blo 908576 1023277 := bbase (se 3 (by rfl) ⟨191864, by rfl⟩ : syracuseStep 1023277 = 383729) (by norm_num)
theorem B1023313 : Blo 908576 1023313 := bbase (se 2 (by rfl) ⟨383742, by rfl⟩ : syracuseStep 1023313 = 767485) (by norm_num)
theorem B1023349 : Blo 908576 1023349 := bbase (se 5 (by rfl) ⟨47969, by rfl⟩ : syracuseStep 1023349 = 95939) (by norm_num)
theorem B1940861 : Blo 908576 1940861 := bbase (se 3 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 1940861 = 727823) (by norm_num)
theorem B1023385 : Blo 908576 1023385 := bbase (se 2 (by rfl) ⟨383769, by rfl⟩ : syracuseStep 1023385 = 767539) (by norm_num)
theorem B1023421 : Blo 908576 1023421 := bbase (se 3 (by rfl) ⟨191891, by rfl⟩ : syracuseStep 1023421 = 383783) (by norm_num)
theorem B1154513 : Blo 908576 1154513 := bbase (se 2 (by rfl) ⟨432942, by rfl⟩ : syracuseStep 1154513 = 865885) (by norm_num)
theorem B1023457 : Blo 908576 1023457 := bbase (se 2 (by rfl) ⟨383796, by rfl⟩ : syracuseStep 1023457 = 767593) (by norm_num)
theorem B1023493 : Blo 908576 1023493 := bbase (se 4 (by rfl) ⟨95952, by rfl⟩ : syracuseStep 1023493 = 191905) (by norm_num)
theorem B1383941 : Blo 908576 1383941 := bbase (se 4 (by rfl) ⟨129744, by rfl⟩ : syracuseStep 1383941 = 259489) (by norm_num)
theorem B1154569 : Blo 908576 1154569 := bbase (se 2 (by rfl) ⟨432963, by rfl⟩ : syracuseStep 1154569 = 865927) (by norm_num)
theorem B3939877 : Blo 908576 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B1023529 : Blo 908576 1023529 := bbase (se 2 (by rfl) ⟨383823, by rfl⟩ : syracuseStep 1023529 = 767647) (by norm_num)
theorem B2301493 : Blo 908576 2301493 := bbase (se 5 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 2301493 = 215765) (by norm_num)
theorem B1023565 : Blo 908576 1023565 := bbase (se 3 (by rfl) ⟨191918, by rfl⟩ : syracuseStep 1023565 = 383837) (by norm_num)
theorem B1154665 : Blo 908576 1154665 := bbase (se 2 (by rfl) ⟨432999, by rfl⟩ : syracuseStep 1154665 = 865999) (by norm_num)
theorem B1023601 : Blo 908576 1023601 := bbase (se 2 (by rfl) ⟨383850, by rfl⟩ : syracuseStep 1023601 = 767701) (by norm_num)
theorem B1023637 : Blo 908576 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B2301605 : Blo 908576 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B1023673 : Blo 908576 1023673 := bbase (se 2 (by rfl) ⟨383877, by rfl⟩ : syracuseStep 1023673 = 767755) (by norm_num)
theorem B1023709 : Blo 908576 1023709 := bbase (se 3 (by rfl) ⟨191945, by rfl⟩ : syracuseStep 1023709 = 383891) (by norm_num)
theorem B1023745 : Blo 908576 1023745 := bbase (se 2 (by rfl) ⟨383904, by rfl⟩ : syracuseStep 1023745 = 767809) (by norm_num)
theorem B1154837 : Blo 908576 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B1023781 : Blo 908576 1023781 := bbase (se 4 (by rfl) ⟨95979, by rfl⟩ : syracuseStep 1023781 = 191959) (by norm_num)
theorem B1023817 : Blo 908576 1023817 := bbase (se 2 (by rfl) ⟨383931, by rfl⟩ : syracuseStep 1023817 = 767863) (by norm_num)
theorem B1154893 : Blo 908576 1154893 := bbase (se 3 (by rfl) ⟨216542, by rfl⟩ : syracuseStep 1154893 = 433085) (by norm_num)
theorem B2301797 : Blo 908576 2301797 := bbase (se 4 (by rfl) ⟨215793, by rfl⟩ : syracuseStep 2301797 = 431587) (by norm_num)
theorem B1023853 : Blo 908576 1023853 := bbase (se 3 (by rfl) ⟨191972, by rfl⟩ : syracuseStep 1023853 = 383945) (by norm_num)
theorem B1023889 : Blo 908576 1023889 := bbase (se 2 (by rfl) ⟨383958, by rfl⟩ : syracuseStep 1023889 = 767917) (by norm_num)
theorem B1023925 : Blo 908576 1023925 := bbase (se 5 (by rfl) ⟨47996, by rfl⟩ : syracuseStep 1023925 = 95993) (by norm_num)
theorem B2596789 : Blo 908576 2596789 := bbase (se 5 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 2596789 = 243449) (by norm_num)
theorem B1023961 : Blo 908576 1023961 := bbase (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) (by norm_num)
theorem B1023997 : Blo 908576 1023997 := bbase (se 3 (by rfl) ⟨191999, by rfl⟩ : syracuseStep 1023997 = 383999) (by norm_num)
theorem B1024033 : Blo 908576 1024033 := bbase (se 2 (by rfl) ⟨384012, by rfl⟩ : syracuseStep 1024033 = 768025) (by norm_num)
theorem B1024069 : Blo 908576 1024069 := bbase (se 4 (by rfl) ⟨96006, by rfl⟩ : syracuseStep 1024069 = 192013) (by norm_num)
theorem B1024105 : Blo 908576 1024105 := bbase (se 2 (by rfl) ⟨384039, by rfl⟩ : syracuseStep 1024105 = 768079) (by norm_num)
theorem B1024141 : Blo 908576 1024141 := bbase (se 3 (by rfl) ⟨192026, by rfl⟩ : syracuseStep 1024141 = 384053) (by norm_num)
theorem B1024177 : Blo 908576 1024177 := bbase (se 2 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 1024177 = 768133) (by norm_num)
theorem B2302141 : Blo 908576 2302141 := bbase (se 3 (by rfl) ⟨431651, by rfl⟩ : syracuseStep 2302141 = 863303) (by norm_num)
theorem B1024213 : Blo 908576 1024213 := bbase (se 7 (by rfl) ⟨12002, by rfl⟩ : syracuseStep 1024213 = 24005) (by norm_num)
theorem B1941749 : Blo 908576 1941749 := bbase (se 5 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 1941749 = 182039) (by norm_num)
theorem B1024249 : Blo 908576 1024249 := bbase (se 2 (by rfl) ⟨384093, by rfl⟩ : syracuseStep 1024249 = 768187) (by norm_num)
theorem B1024285 : Blo 908576 1024285 := bbase (se 3 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 1024285 = 384107) (by norm_num)
theorem B2302253 : Blo 908576 2302253 := bbase (se 3 (by rfl) ⟨431672, by rfl⟩ : syracuseStep 2302253 = 863345) (by norm_num)
theorem B1024321 : Blo 908576 1024321 := bbase (se 2 (by rfl) ⟨384120, by rfl⟩ : syracuseStep 1024321 = 768241) (by norm_num)
theorem B1024357 : Blo 908576 1024357 := bbase (se 4 (by rfl) ⟨96033, by rfl⟩ : syracuseStep 1024357 = 192067) (by norm_num)
theorem B1941869 : Blo 908576 1941869 := bbase (se 3 (by rfl) ⟨364100, by rfl⟩ : syracuseStep 1941869 = 728201) (by norm_num)
theorem B1024393 : Blo 908576 1024393 := bbase (se 2 (by rfl) ⟨384147, by rfl⟩ : syracuseStep 1024393 = 768295) (by norm_num)
theorem B1024429 : Blo 908576 1024429 := bbase (se 3 (by rfl) ⟨192080, by rfl⟩ : syracuseStep 1024429 = 384161) (by norm_num)
theorem B1024465 : Blo 908576 1024465 := bbase (se 2 (by rfl) ⟨384174, by rfl⟩ : syracuseStep 1024465 = 768349) (by norm_num)
theorem B2302445 : Blo 908576 2302445 := bbase (se 3 (by rfl) ⟨431708, by rfl⟩ : syracuseStep 2302445 = 863417) (by norm_num)
theorem B1024501 : Blo 908576 1024501 := bbase (se 5 (by rfl) ⟨48023, by rfl⟩ : syracuseStep 1024501 = 96047) (by norm_num)
theorem B1024537 : Blo 908576 1024537 := bbase (se 2 (by rfl) ⟨384201, by rfl⟩ : syracuseStep 1024537 = 768403) (by norm_num)
theorem B1024573 : Blo 908576 1024573 := bbase (se 3 (by rfl) ⟨192107, by rfl⟩ : syracuseStep 1024573 = 384215) (by norm_num)
theorem B15540821 : Blo 908576 15540821 := bbase (se 8 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 15540821 = 182119) (by norm_num)
theorem B1024609 : Blo 908576 1024609 := bbase (se 2 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 1024609 = 768457) (by norm_num)
theorem B1024645 : Blo 908576 1024645 := bbase (se 4 (by rfl) ⟨96060, by rfl⟩ : syracuseStep 1024645 = 192121) (by norm_num)
theorem B1024681 : Blo 908576 1024681 := bbase (se 2 (by rfl) ⟨384255, by rfl⟩ : syracuseStep 1024681 = 768511) (by norm_num)
theorem B1024717 : Blo 908576 1024717 := bbase (se 3 (by rfl) ⟨192134, by rfl⟩ : syracuseStep 1024717 = 384269) (by norm_num)
theorem B1843949 : Blo 908576 1843949 := bbase (se 3 (by rfl) ⟨345740, by rfl⟩ : syracuseStep 1843949 = 691481) (by norm_num)
theorem B1024753 : Blo 908576 1024753 := bbase (se 2 (by rfl) ⟨384282, by rfl⟩ : syracuseStep 1024753 = 768565) (by norm_num)
theorem B1024789 : Blo 908576 1024789 := bbase (se 6 (by rfl) ⟨24018, by rfl⟩ : syracuseStep 1024789 = 48037) (by norm_num)
theorem B1024825 : Blo 908576 1024825 := bbase (se 2 (by rfl) ⟨384309, by rfl⟩ : syracuseStep 1024825 = 768619) (by norm_num)
theorem B2302789 : Blo 908576 2302789 := bbase (se 4 (by rfl) ⟨215886, by rfl⟩ : syracuseStep 2302789 = 431773) (by norm_num)
theorem B1024861 : Blo 908576 1024861 := bbase (se 3 (by rfl) ⟨192161, by rfl⟩ : syracuseStep 1024861 = 384323) (by norm_num)
theorem B1024897 : Blo 908576 1024897 := bbase (se 2 (by rfl) ⟨384336, by rfl⟩ : syracuseStep 1024897 = 768673) (by norm_num)
theorem B1024933 : Blo 908576 1024933 := bbase (se 4 (by rfl) ⟨96087, by rfl⟩ : syracuseStep 1024933 = 192175) (by norm_num)
theorem B2302901 : Blo 908576 2302901 := bbase (se 5 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 2302901 = 215897) (by norm_num)
theorem B1024969 : Blo 908576 1024969 := bbase (se 2 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 1024969 = 768727) (by norm_num)
theorem B1942501 : Blo 908576 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B1025005 : Blo 908576 1025005 := bbase (se 3 (by rfl) ⟨192188, by rfl⟩ : syracuseStep 1025005 = 384377) (by norm_num)
theorem B1025041 : Blo 908576 1025041 := bbase (se 2 (by rfl) ⟨384390, by rfl⟩ : syracuseStep 1025041 = 768781) (by norm_num)
theorem B1025077 : Blo 908576 1025077 := bbase (se 5 (by rfl) ⟨48050, by rfl⟩ : syracuseStep 1025077 = 96101) (by norm_num)
theorem B1025113 : Blo 908576 1025113 := bbase (se 2 (by rfl) ⟨384417, by rfl⟩ : syracuseStep 1025113 = 768835) (by norm_num)
theorem B2303093 : Blo 908576 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B6661237 : Blo 908576 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B1025149 : Blo 908576 1025149 := bbase (se 3 (by rfl) ⟨192215, by rfl⟩ : syracuseStep 1025149 = 384431) (by norm_num)
theorem B1025185 : Blo 908576 1025185 := bbase (se 2 (by rfl) ⟨384444, by rfl⟩ : syracuseStep 1025185 = 768889) (by norm_num)
theorem B3450053 : Blo 908576 3450053 := bbase (se 4 (by rfl) ⟨323442, by rfl⟩ : syracuseStep 3450053 = 646885) (by norm_num)
theorem B1025221 : Blo 908576 1025221 := bbase (se 4 (by rfl) ⟨96114, by rfl⟩ : syracuseStep 1025221 = 192229) (by norm_num)
theorem B1025257 : Blo 908576 1025257 := bbase (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) (by norm_num)
theorem B3286277 : Blo 908576 3286277 := bbase (se 4 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 3286277 = 616177) (by norm_num)
theorem B1025293 : Blo 908576 1025293 := bbase (se 3 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 1025293 = 384485) (by norm_num)
theorem B1025329 : Blo 908576 1025329 := bbase (se 2 (by rfl) ⟨384498, by rfl⟩ : syracuseStep 1025329 = 768997) (by norm_num)
theorem B1025365 : Blo 908576 1025365 := bbase (se 12 (by rfl) ⟨375, by rfl⟩ : syracuseStep 1025365 = 751) (by norm_num)
theorem B1025401 : Blo 908576 1025401 := bbase (se 2 (by rfl) ⟨384525, by rfl⟩ : syracuseStep 1025401 = 769051) (by norm_num)
theorem B2598293 : Blo 908576 2598293 := bbase (se 6 (by rfl) ⟨60897, by rfl⟩ : syracuseStep 2598293 = 121795) (by norm_num)
theorem B1025437 : Blo 908576 1025437 := bbase (se 3 (by rfl) ⟨192269, by rfl⟩ : syracuseStep 1025437 = 384539) (by norm_num)
theorem B1025473 : Blo 908576 1025473 := bbase (se 2 (by rfl) ⟨384552, by rfl⟩ : syracuseStep 1025473 = 769105) (by norm_num)
theorem B2303437 : Blo 908576 2303437 := bbase (se 3 (by rfl) ⟨431894, by rfl⟩ : syracuseStep 2303437 = 863789) (by norm_num)
theorem B1025509 : Blo 908576 1025509 := bbase (se 4 (by rfl) ⟨96141, by rfl⟩ : syracuseStep 1025509 = 192283) (by norm_num)
theorem B1025545 : Blo 908576 1025545 := bbase (se 2 (by rfl) ⟨384579, by rfl⟩ : syracuseStep 1025545 = 769159) (by norm_num)
theorem B1025581 : Blo 908576 1025581 := bbase (se 3 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 1025581 = 384593) (by norm_num)
theorem B2303549 : Blo 908576 2303549 := bbase (se 3 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 2303549 = 863831) (by norm_num)
theorem B1025617 : Blo 908576 1025617 := bbase (se 2 (by rfl) ⟨384606, by rfl⟩ : syracuseStep 1025617 = 769213) (by norm_num)
theorem B1025653 : Blo 908576 1025653 := bbase (se 5 (by rfl) ⟨48077, by rfl⟩ : syracuseStep 1025653 = 96155) (by norm_num)
theorem B1025689 : Blo 908576 1025689 := bbase (se 2 (by rfl) ⟨384633, by rfl⟩ : syracuseStep 1025689 = 769267) (by norm_num)
theorem B1025725 : Blo 908576 1025725 := bbase (se 3 (by rfl) ⟨192323, by rfl⟩ : syracuseStep 1025725 = 384647) (by norm_num)
theorem B1025761 : Blo 908576 1025761 := bbase (se 2 (by rfl) ⟨384660, by rfl⟩ : syracuseStep 1025761 = 769321) (by norm_num)
theorem B2303741 : Blo 908576 2303741 := bbase (se 3 (by rfl) ⟨431951, by rfl⟩ : syracuseStep 2303741 = 863903) (by norm_num)
theorem B1025797 : Blo 908576 1025797 := bbase (se 4 (by rfl) ⟨96168, by rfl⟩ : syracuseStep 1025797 = 192337) (by norm_num)
theorem B1025833 : Blo 908576 1025833 := bbase (se 2 (by rfl) ⟨384687, by rfl⟩ : syracuseStep 1025833 = 769375) (by norm_num)
theorem B1025869 : Blo 908576 1025869 := bbase (se 3 (by rfl) ⟨192350, by rfl⟩ : syracuseStep 1025869 = 384701) (by norm_num)
theorem B1386325 : Blo 908576 1386325 := bbase (se 9 (by rfl) ⟨4061, by rfl⟩ : syracuseStep 1386325 = 8123) (by norm_num)
theorem B1943389 : Blo 908576 1943389 := bbase (se 3 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 1943389 = 728771) (by norm_num)
theorem B1025905 : Blo 908576 1025905 := bbase (se 2 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 1025905 = 769429) (by norm_num)
theorem B1025941 : Blo 908576 1025941 := bbase (se 6 (by rfl) ⟨24045, by rfl⟩ : syracuseStep 1025941 = 48091) (by norm_num)
theorem B1025977 : Blo 908576 1025977 := bbase (se 2 (by rfl) ⟨384741, by rfl⟩ : syracuseStep 1025977 = 769483) (by norm_num)
theorem B1943509 : Blo 908576 1943509 := bbase (se 7 (by rfl) ⟨22775, by rfl⟩ : syracuseStep 1943509 = 45551) (by norm_num)
theorem B1026013 : Blo 908576 1026013 := bbase (se 3 (by rfl) ⟨192377, by rfl⟩ : syracuseStep 1026013 = 384755) (by norm_num)
theorem B1091561 : Blo 908576 1091561 := bbase (se 2 (by rfl) ⟨409335, by rfl⟩ : syracuseStep 1091561 = 818671) (by norm_num)
theorem B1026049 : Blo 908576 1026049 := bbase (se 2 (by rfl) ⟨384768, by rfl⟩ : syracuseStep 1026049 = 769537) (by norm_num)
theorem B1026085 : Blo 908576 1026085 := bbase (se 4 (by rfl) ⟨96195, by rfl⟩ : syracuseStep 1026085 = 192391) (by norm_num)
theorem B1026121 : Blo 908576 1026121 := bbase (se 2 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 1026121 = 769591) (by norm_num)
theorem B2304085 : Blo 908576 2304085 := bbase (se 8 (by rfl) ⟨13500, by rfl⟩ : syracuseStep 2304085 = 27001) (by norm_num)
theorem B1026157 : Blo 908576 1026157 := bbase (se 3 (by rfl) ⟨192404, by rfl⟩ : syracuseStep 1026157 = 384809) (by norm_num)
theorem B1026193 : Blo 908576 1026193 := bbase (se 2 (by rfl) ⟨384822, by rfl⟩ : syracuseStep 1026193 = 769645) (by norm_num)
theorem B1026229 : Blo 908576 1026229 := bbase (se 5 (by rfl) ⟨48104, by rfl⟩ : syracuseStep 1026229 = 96209) (by norm_num)
theorem B2304197 : Blo 908576 2304197 := bbase (se 4 (by rfl) ⟨216018, by rfl⟩ : syracuseStep 2304197 = 432037) (by norm_num)
theorem B1943765 : Blo 908576 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B1026265 : Blo 908576 1026265 := bbase (se 2 (by rfl) ⟨384849, by rfl⟩ : syracuseStep 1026265 = 769699) (by norm_num)
theorem B1026301 : Blo 908576 1026301 := bbase (se 3 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 1026301 = 384863) (by norm_num)
theorem B1026337 : Blo 908576 1026337 := bbase (se 2 (by rfl) ⟨384876, by rfl⟩ : syracuseStep 1026337 = 769753) (by norm_num)
theorem B1026373 : Blo 908576 1026373 := bbase (se 4 (by rfl) ⟨96222, by rfl⟩ : syracuseStep 1026373 = 192445) (by norm_num)
theorem B1091917 : Blo 908576 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B1026409 : Blo 908576 1026409 := bbase (se 2 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 1026409 = 769807) (by norm_num)
theorem B2304389 : Blo 908576 2304389 := bbase (se 4 (by rfl) ⟨216036, by rfl⟩ : syracuseStep 2304389 = 432073) (by norm_num)
theorem B1026445 : Blo 908576 1026445 := bbase (se 3 (by rfl) ⟨192458, by rfl⟩ : syracuseStep 1026445 = 384917) (by norm_num)
theorem B2632085 : Blo 908576 2632085 := bbase (se 6 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 2632085 = 123379) (by norm_num)
theorem B1845661 : Blo 908576 1845661 := bbase (se 3 (by rfl) ⟨346061, by rfl⟩ : syracuseStep 1845661 = 692123) (by norm_num)
theorem B1026481 : Blo 908576 1026481 := bbase (se 2 (by rfl) ⟨384930, by rfl⟩ : syracuseStep 1026481 = 769861) (by norm_num)
theorem B1026517 : Blo 908576 1026517 := bbase (se 7 (by rfl) ⟨12029, by rfl⟩ : syracuseStep 1026517 = 24059) (by norm_num)
theorem B1026553 : Blo 908576 1026553 := bbase (se 2 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 1026553 = 769915) (by norm_num)
theorem B1026589 : Blo 908576 1026589 := bbase (se 3 (by rfl) ⟨192485, by rfl⟩ : syracuseStep 1026589 = 384971) (by norm_num)
theorem B1026625 : Blo 908576 1026625 := bbase (se 2 (by rfl) ⟨384984, by rfl⟩ : syracuseStep 1026625 = 769969) (by norm_num)
theorem B2108005 : Blo 908576 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B5843573 : Blo 908576 5843573 := bbase (se 5 (by rfl) ⟨273917, by rfl⟩ : syracuseStep 5843573 = 547835) (by norm_num)
theorem B1092253 : Blo 908576 1092253 := bbase (se 3 (by rfl) ⟨204797, by rfl⟩ : syracuseStep 1092253 = 409595) (by norm_num)
theorem B6925013 : Blo 908576 6925013 := bbase (se 7 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 6925013 = 162305) (by norm_num)
theorem B2304733 : Blo 908576 2304733 := bbase (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) (by norm_num)
theorem B17705749 : Blo 908576 17705749 := bbase (se 6 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 17705749 = 829957) (by norm_num)
theorem B2304845 : Blo 908576 2304845 := bbase (se 3 (by rfl) ⟨432158, by rfl⟩ : syracuseStep 2304845 = 864317) (by norm_num)
theorem B2305037 : Blo 908576 2305037 := bbase (se 3 (by rfl) ⟨432194, by rfl⟩ : syracuseStep 2305037 = 864389) (by norm_num)
theorem B1944653 : Blo 908576 1944653 := bbase (se 3 (by rfl) ⟨364622, by rfl⟩ : syracuseStep 1944653 = 729245) (by norm_num)
theorem B2337965 : Blo 908576 2337965 := bbase (se 3 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 2337965 = 876737) (by norm_num)
theorem B2632949 : Blo 908576 2632949 := bbase (se 5 (by rfl) ⟨123419, by rfl⟩ : syracuseStep 2632949 = 246839) (by norm_num)
theorem B3452165 : Blo 908576 3452165 := bbase (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) (by norm_num)
theorem B1944893 : Blo 908576 1944893 := bbase (se 3 (by rfl) ⟨364667, by rfl⟩ : syracuseStep 1944893 = 729335) (by norm_num)
theorem B6663509 : Blo 908576 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B2305381 : Blo 908576 2305381 := bbase (se 4 (by rfl) ⟨216129, by rfl⟩ : syracuseStep 2305381 = 432259) (by norm_num)
theorem B4369781 : Blo 908576 4369781 := bbase (se 5 (by rfl) ⟨204833, by rfl⟩ : syracuseStep 4369781 = 409667) (by norm_num)
theorem B2305493 : Blo 908576 2305493 := bbase (se 7 (by rfl) ⟨27017, by rfl⟩ : syracuseStep 2305493 = 54035) (by norm_num)
theorem B1125865 : Blo 908576 1125865 := bbase (se 2 (by rfl) ⟨422199, by rfl⟩ : syracuseStep 1125865 = 844399) (by norm_num)
theorem B1093133 : Blo 908576 1093133 := bbase (se 3 (by rfl) ⟨204962, by rfl⟩ : syracuseStep 1093133 = 409925) (by norm_num)
theorem B3452453 : Blo 908576 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B2305685 : Blo 908576 2305685 := bbase (se 6 (by rfl) ⟨54039, by rfl⟩ : syracuseStep 2305685 = 108079) (by norm_num)
theorem B1846973 : Blo 908576 1846973 := bbase (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) (by norm_num)
theorem B1683149 : Blo 908576 1683149 := bbase (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) (by norm_num)
theorem B1945397 : Blo 908576 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B1945405 : Blo 908576 1945405 := bbase (se 3 (by rfl) ⟨364763, by rfl⟩ : syracuseStep 1945405 = 729527) (by norm_num)
theorem B1093441 : Blo 908576 1093441 := bbase (se 2 (by rfl) ⟨410040, by rfl⟩ : syracuseStep 1093441 = 820081) (by norm_num)
theorem B3321701 : Blo 908576 3321701 := bbase (se 4 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 3321701 = 622819) (by norm_num)
theorem B4665221 : Blo 908576 4665221 := bbase (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) (by norm_num)
theorem B2764693 : Blo 908576 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B2306029 : Blo 908576 2306029 := bbase (se 3 (by rfl) ⟨432380, by rfl⟩ : syracuseStep 2306029 = 864761) (by norm_num)
theorem B2306141 : Blo 908576 2306141 := bbase (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) (by norm_num)
theorem B4599989 : Blo 908576 4599989 := bbase (se 5 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 4599989 = 431249) (by norm_num)
theorem B1093825 : Blo 908576 1093825 := bbase (se 2 (by rfl) ⟨410184, by rfl⟩ : syracuseStep 1093825 = 820369) (by norm_num)
theorem B1093829 : Blo 908576 1093829 := bbase (se 4 (by rfl) ⟨102546, by rfl⟩ : syracuseStep 1093829 = 205093) (by norm_num)
theorem B2306333 : Blo 908576 2306333 := bbase (se 3 (by rfl) ⟨432437, by rfl⟩ : syracuseStep 2306333 = 864875) (by norm_num)
theorem B2044349 : Blo 908576 2044349 := bbase (se 3 (by rfl) ⟨383315, by rfl⟩ : syracuseStep 2044349 = 766631) (by norm_num)
theorem B2044421 : Blo 908576 2044421 := bbase (se 4 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 2044421 = 383329) (by norm_num)
theorem B2044493 : Blo 908576 2044493 := bbase (se 3 (by rfl) ⟨383342, by rfl⟩ : syracuseStep 2044493 = 766685) (by norm_num)
theorem B1094233 : Blo 908576 1094233 := bbase (se 2 (by rfl) ⟨410337, by rfl⟩ : syracuseStep 1094233 = 820675) (by norm_num)
theorem B2306677 : Blo 908576 2306677 := bbase (se 5 (by rfl) ⟨108125, by rfl⟩ : syracuseStep 2306677 = 216251) (by norm_num)
theorem B2044565 : Blo 908576 2044565 := bbase (se 6 (by rfl) ⟨47919, by rfl⟩ : syracuseStep 2044565 = 95839) (by norm_num)
theorem B3453637 : Blo 908576 3453637 := bbase (se 4 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 3453637 = 647557) (by norm_num)
theorem B2044637 : Blo 908576 2044637 := bbase (se 3 (by rfl) ⟨383369, by rfl⟩ : syracuseStep 2044637 = 766739) (by norm_num)
theorem B2306789 : Blo 908576 2306789 := bbase (se 4 (by rfl) ⟨216261, by rfl⟩ : syracuseStep 2306789 = 432523) (by norm_num)
theorem B5190389 : Blo 908576 5190389 := bbase (se 5 (by rfl) ⟨243299, by rfl⟩ : syracuseStep 5190389 = 486599) (by norm_num)
theorem B4371205 : Blo 908576 4371205 := bbase (se 4 (by rfl) ⟨409800, by rfl⟩ : syracuseStep 4371205 = 819601) (by norm_num)
theorem B2044709 : Blo 908576 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B2274149 : Blo 908576 2274149 := bbase (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) (by norm_num)
theorem B2044781 : Blo 908576 2044781 := bbase (se 3 (by rfl) ⟨383396, by rfl⟩ : syracuseStep 2044781 = 766793) (by norm_num)
theorem B2306981 : Blo 908576 2306981 := bbase (se 4 (by rfl) ⟨216279, by rfl⟩ : syracuseStep 2306981 = 432559) (by norm_num)
theorem B1946533 : Blo 908576 1946533 := bbase (se 4 (by rfl) ⟨182487, by rfl⟩ : syracuseStep 1946533 = 364975) (by norm_num)
theorem B2044853 : Blo 908576 2044853 := bbase (se 5 (by rfl) ⟨95852, by rfl⟩ : syracuseStep 2044853 = 191705) (by norm_num)
theorem B2077661 : Blo 908576 2077661 := bbase (se 3 (by rfl) ⟨389561, by rfl⟩ : syracuseStep 2077661 = 779123) (by norm_num)
theorem B3453941 : Blo 908576 3453941 := bbase (se 5 (by rfl) ⟨161903, by rfl⟩ : syracuseStep 3453941 = 323807) (by norm_num)
theorem B2044925 : Blo 908576 2044925 := bbase (se 3 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 2044925 = 766847) (by norm_num)
theorem B2044997 : Blo 908576 2044997 := bbase (se 4 (by rfl) ⟨191718, by rfl⟩ : syracuseStep 2044997 = 383437) (by norm_num)
theorem B1750133 : Blo 908576 1750133 := bbase (se 5 (by rfl) ⟨82037, by rfl⟩ : syracuseStep 1750133 = 164075) (by norm_num)
theorem B2045069 : Blo 908576 2045069 := bbase (se 3 (by rfl) ⟨383450, by rfl⟩ : syracuseStep 2045069 = 766901) (by norm_num)
theorem B2045141 : Blo 908576 2045141 := bbase (se 7 (by rfl) ⟨23966, by rfl⟩ : syracuseStep 2045141 = 47933) (by norm_num)
theorem B2307325 : Blo 908576 2307325 := bbase (se 3 (by rfl) ⟨432623, by rfl⟩ : syracuseStep 2307325 = 865247) (by norm_num)
theorem B2045213 : Blo 908576 2045213 := bbase (se 3 (by rfl) ⟨383477, by rfl⟩ : syracuseStep 2045213 = 766955) (by norm_num)
theorem B1946909 : Blo 908576 1946909 := bbase (se 3 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 1946909 = 730091) (by norm_num)
theorem B2045285 : Blo 908576 2045285 := bbase (se 4 (by rfl) ⟨191745, by rfl⟩ : syracuseStep 2045285 = 383491) (by norm_num)
theorem B2307437 : Blo 908576 2307437 := bbase (se 3 (by rfl) ⟨432644, by rfl⟩ : syracuseStep 2307437 = 865289) (by norm_num)
theorem B1455517 : Blo 908576 1455517 := bbase (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) (by norm_num)
theorem B2045357 : Blo 908576 2045357 := bbase (se 3 (by rfl) ⟨383504, by rfl⟩ : syracuseStep 2045357 = 767009) (by norm_num)
theorem B4601285 : Blo 908576 4601285 := bbase (se 4 (by rfl) ⟨431370, by rfl⟩ : syracuseStep 4601285 = 862741) (by norm_num)
theorem B2340317 : Blo 908576 2340317 := bbase (se 3 (by rfl) ⟨438809, by rfl⟩ : syracuseStep 2340317 = 877619) (by norm_num)
theorem B2045429 : Blo 908576 2045429 := bbase (se 5 (by rfl) ⟨95879, by rfl⟩ : syracuseStep 2045429 = 191759) (by norm_num)
theorem B2307629 : Blo 908576 2307629 := bbase (se 3 (by rfl) ⟨432680, by rfl⟩ : syracuseStep 2307629 = 865361) (by norm_num)
theorem B2045501 : Blo 908576 2045501 := bbase (se 3 (by rfl) ⟨383531, by rfl⟩ : syracuseStep 2045501 = 767063) (by norm_num)
theorem B2045573 : Blo 908576 2045573 := bbase (se 4 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 2045573 = 383545) (by norm_num)
theorem B2045645 : Blo 908576 2045645 := bbase (se 3 (by rfl) ⟨383558, by rfl⟩ : syracuseStep 2045645 = 767117) (by norm_num)
theorem B2045717 : Blo 908576 2045717 := bbase (se 6 (by rfl) ⟨47946, by rfl⟩ : syracuseStep 2045717 = 95893) (by norm_num)
theorem B2045789 : Blo 908576 2045789 := bbase (se 3 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 2045789 = 767171) (by norm_num)
theorem B2307973 : Blo 908576 2307973 := bbase (se 4 (by rfl) ⟨216372, by rfl⟩ : syracuseStep 2307973 = 432745) (by norm_num)
theorem B5191573 : Blo 908576 5191573 := bbase (se 6 (by rfl) ⟨121677, by rfl⟩ : syracuseStep 5191573 = 243355) (by norm_num)
theorem B2045861 : Blo 908576 2045861 := bbase (se 4 (by rfl) ⟨191799, by rfl⟩ : syracuseStep 2045861 = 383599) (by norm_num)
theorem B1095617 : Blo 908576 1095617 := bbase (se 2 (by rfl) ⟨410856, by rfl⟩ : syracuseStep 1095617 = 821713) (by norm_num)
theorem B2045933 : Blo 908576 2045933 := bbase (se 3 (by rfl) ⟨383612, by rfl⟩ : syracuseStep 2045933 = 767225) (by norm_num)
theorem B2308085 : Blo 908576 2308085 := bbase (se 5 (by rfl) ⟨108191, by rfl⟩ : syracuseStep 2308085 = 216383) (by norm_num)
theorem B2046005 : Blo 908576 2046005 := bbase (se 5 (by rfl) ⟨95906, by rfl⟩ : syracuseStep 2046005 = 191813) (by norm_num)
theorem B2046077 : Blo 908576 2046077 := bbase (se 3 (by rfl) ⟨383639, by rfl⟩ : syracuseStep 2046077 = 767279) (by norm_num)
theorem B3881141 : Blo 908576 3881141 := bbase (se 5 (by rfl) ⟨181928, by rfl⟩ : syracuseStep 3881141 = 363857) (by norm_num)
theorem B2308277 : Blo 908576 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B2046149 : Blo 908576 2046149 := bbase (se 4 (by rfl) ⟨191826, by rfl⟩ : syracuseStep 2046149 = 383653) (by norm_num)
theorem B1095877 : Blo 908576 1095877 := bbase (se 4 (by rfl) ⟨102738, by rfl⟩ : syracuseStep 1095877 = 205477) (by norm_num)
theorem B1095925 : Blo 908576 1095925 := bbase (se 5 (by rfl) ⟨51371, by rfl⟩ : syracuseStep 1095925 = 102743) (by norm_num)
theorem B2046221 : Blo 908576 2046221 := bbase (se 3 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 2046221 = 767333) (by norm_num)
theorem B2046293 : Blo 908576 2046293 := bbase (se 10 (by rfl) ⟨2997, by rfl⟩ : syracuseStep 2046293 = 5995) (by norm_num)
theorem B1456517 : Blo 908576 1456517 := bbase (se 4 (by rfl) ⟨136548, by rfl⟩ : syracuseStep 1456517 = 273097) (by norm_num)
theorem B2046365 : Blo 908576 2046365 := bbase (se 3 (by rfl) ⟨383693, by rfl⟩ : syracuseStep 2046365 = 767387) (by norm_num)
theorem B2046437 : Blo 908576 2046437 := bbase (se 4 (by rfl) ⟨191853, by rfl⟩ : syracuseStep 2046437 = 383707) (by norm_num)
theorem B1849853 : Blo 908576 1849853 := bbase (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) (by norm_num)
theorem B1456645 : Blo 908576 1456645 := bbase (se 4 (by rfl) ⟨136560, by rfl⟩ : syracuseStep 1456645 = 273121) (by norm_num)
theorem B2308621 : Blo 908576 2308621 := bbase (se 3 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 2308621 = 865733) (by norm_num)
theorem B2046509 : Blo 908576 2046509 := bbase (se 3 (by rfl) ⟨383720, by rfl⟩ : syracuseStep 2046509 = 767441) (by norm_num)
theorem B1456709 : Blo 908576 1456709 := bbase (se 4 (by rfl) ⟨136566, by rfl⟩ : syracuseStep 1456709 = 273133) (by norm_num)
theorem B2046581 : Blo 908576 2046581 := bbase (se 5 (by rfl) ⟨95933, by rfl⟩ : syracuseStep 2046581 = 191867) (by norm_num)
theorem B2308733 : Blo 908576 2308733 := bbase (se 3 (by rfl) ⟨432887, by rfl⟩ : syracuseStep 2308733 = 865775) (by norm_num)
theorem B2046653 : Blo 908576 2046653 := bbase (se 3 (by rfl) ⟨383747, by rfl⟩ : syracuseStep 2046653 = 767495) (by norm_num)
theorem B4602581 : Blo 908576 4602581 := bbase (se 7 (by rfl) ⟨53936, by rfl⟩ : syracuseStep 4602581 = 107873) (by norm_num)
theorem B2046725 : Blo 908576 2046725 := bbase (se 4 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 2046725 = 383761) (by norm_num)
theorem B2308925 : Blo 908576 2308925 := bbase (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) (by norm_num)
theorem B2046797 : Blo 908576 2046797 := bbase (se 3 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 2046797 = 767549) (by norm_num)
theorem B1948549 : Blo 908576 1948549 := bbase (se 4 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 1948549 = 365353) (by norm_num)
theorem B2046869 : Blo 908576 2046869 := bbase (se 6 (by rfl) ⟨47973, by rfl⟩ : syracuseStep 2046869 = 95947) (by norm_num)
theorem B2046941 : Blo 908576 2046941 := bbase (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) (by norm_num)
theorem B2047013 : Blo 908576 2047013 := bbase (se 4 (by rfl) ⟨191907, by rfl⟩ : syracuseStep 2047013 = 383815) (by norm_num)
theorem B3456053 : Blo 908576 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B2047085 : Blo 908576 2047085 := bbase (se 3 (by rfl) ⟨383828, by rfl⟩ : syracuseStep 2047085 = 767657) (by norm_num)
theorem B2309269 : Blo 908576 2309269 := bbase (se 6 (by rfl) ⟨54123, by rfl⟩ : syracuseStep 2309269 = 108247) (by norm_num)
theorem B2047157 : Blo 908576 2047157 := bbase (se 5 (by rfl) ⟨95960, by rfl⟩ : syracuseStep 2047157 = 191921) (by norm_num)
theorem B2047229 : Blo 908576 2047229 := bbase (se 3 (by rfl) ⟨383855, by rfl⟩ : syracuseStep 2047229 = 767711) (by norm_num)
theorem B2309381 : Blo 908576 2309381 := bbase (se 4 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 2309381 = 433009) (by norm_num)
theorem B2047301 : Blo 908576 2047301 := bbase (se 4 (by rfl) ⟨191934, by rfl⟩ : syracuseStep 2047301 = 383869) (by norm_num)
theorem B3456341 : Blo 908576 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B5913973 : Blo 908576 5913973 := bbase (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) (by norm_num)
theorem B2047373 : Blo 908576 2047373 := bbase (se 3 (by rfl) ⟨383882, by rfl⟩ : syracuseStep 2047373 = 767765) (by norm_num)
theorem B2080181 : Blo 908576 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B2309573 : Blo 908576 2309573 := bbase (se 4 (by rfl) ⟨216522, by rfl⟩ : syracuseStep 2309573 = 433045) (by norm_num)
theorem B2047445 : Blo 908576 2047445 := bbase (se 7 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 2047445 = 47987) (by norm_num)
theorem B2047517 : Blo 908576 2047517 := bbase (se 3 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 2047517 = 767819) (by norm_num)
theorem B2047589 : Blo 908576 2047589 := bbase (se 4 (by rfl) ⟨191961, by rfl⟩ : syracuseStep 2047589 = 383923) (by norm_num)
theorem B1293941 : Blo 908576 1293941 := bbase (se 5 (by rfl) ⟨60653, by rfl⟩ : syracuseStep 1293941 = 121307) (by norm_num)
theorem B2047661 : Blo 908576 2047661 := bbase (se 3 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 2047661 = 767873) (by norm_num)
theorem B1752781 : Blo 908576 1752781 := bbase (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) (by norm_num)
theorem B31571669 : Blo 908576 31571669 := bbase (se 7 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 31571669 = 739961) (by norm_num)
theorem B2047733 : Blo 908576 2047733 := bbase (se 5 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 2047733 = 191975) (by norm_num)
theorem B2309917 : Blo 908576 2309917 := bbase (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) (by norm_num)
theorem B2047805 : Blo 908576 2047805 := bbase (se 3 (by rfl) ⟨383963, by rfl⟩ : syracuseStep 2047805 = 767927) (by norm_num)
theorem B5193557 : Blo 908576 5193557 := bbase (se 9 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 5193557 = 30431) (by norm_num)
theorem B1458029 : Blo 908576 1458029 := bbase (se 3 (by rfl) ⟨273380, by rfl⟩ : syracuseStep 1458029 = 546761) (by norm_num)
theorem B2047877 : Blo 908576 2047877 := bbase (se 4 (by rfl) ⟨191988, by rfl⟩ : syracuseStep 2047877 = 383977) (by norm_num)
theorem B3882917 : Blo 908576 3882917 := bbase (se 4 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 3882917 = 728047) (by norm_num)
theorem B4440005 : Blo 908576 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B2047949 : Blo 908576 2047949 := bbase (se 3 (by rfl) ⟨383990, by rfl⟩ : syracuseStep 2047949 = 767981) (by norm_num)
theorem B4603877 : Blo 908576 4603877 := bbase (se 4 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 4603877 = 863227) (by norm_num)
theorem B1458157 : Blo 908576 1458157 := bbase (se 3 (by rfl) ⟨273404, by rfl⟩ : syracuseStep 1458157 = 546809) (by norm_num)
theorem B2048021 : Blo 908576 2048021 := bbase (se 6 (by rfl) ⟨48000, by rfl⟩ : syracuseStep 2048021 = 96001) (by norm_num)
theorem B2080837 : Blo 908576 2080837 := bbase (se 4 (by rfl) ⟨195078, by rfl⟩ : syracuseStep 2080837 = 390157) (by norm_num)
theorem B3686485 : Blo 908576 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B22134869 : Blo 908576 22134869 := bbase (se 8 (by rfl) ⟨129696, by rfl⟩ : syracuseStep 22134869 = 259393) (by norm_num)
theorem B2048093 : Blo 908576 2048093 := bbase (se 3 (by rfl) ⟨384017, by rfl⟩ : syracuseStep 2048093 = 768035) (by norm_num)
theorem B2048165 : Blo 908576 2048165 := bbase (se 4 (by rfl) ⟨192015, by rfl⟩ : syracuseStep 2048165 = 384031) (by norm_num)
theorem B1425613 : Blo 908576 1425613 := bbase (se 3 (by rfl) ⟨267302, by rfl⟩ : syracuseStep 1425613 = 534605) (by norm_num)
theorem B2048237 : Blo 908576 2048237 := bbase (se 3 (by rfl) ⟨384044, by rfl⟩ : syracuseStep 2048237 = 768089) (by norm_num)
theorem B2048309 : Blo 908576 2048309 := bbase (se 5 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 2048309 = 192029) (by norm_num)
theorem B2048381 : Blo 908576 2048381 := bbase (se 3 (by rfl) ⟨384071, by rfl⟩ : syracuseStep 2048381 = 768143) (by norm_num)
theorem B2048453 : Blo 908576 2048453 := bbase (se 4 (by rfl) ⟨192042, by rfl⟩ : syracuseStep 2048453 = 384085) (by norm_num)
theorem B1229261 : Blo 908576 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B2769365 : Blo 908576 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B3457525 : Blo 908576 3457525 := bbase (se 5 (by rfl) ⟨162071, by rfl⟩ : syracuseStep 3457525 = 324143) (by norm_num)
theorem B2048525 : Blo 908576 2048525 := bbase (se 3 (by rfl) ⟨384098, by rfl⟩ : syracuseStep 2048525 = 768197) (by norm_num)
theorem B6242837 : Blo 908576 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B2048597 : Blo 908576 2048597 := bbase (se 8 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 2048597 = 24007) (by norm_num)
theorem B2048669 : Blo 908576 2048669 := bbase (se 3 (by rfl) ⟨384125, by rfl⟩ : syracuseStep 2048669 = 768251) (by norm_num)
theorem B2048741 : Blo 908576 2048741 := bbase (se 4 (by rfl) ⟨192069, by rfl⟩ : syracuseStep 2048741 = 384139) (by norm_num)
theorem B1458965 : Blo 908576 1458965 := bbase (se 6 (by rfl) ⟨34194, by rfl⟩ : syracuseStep 1458965 = 68389) (by norm_num)
theorem B3457829 : Blo 908576 3457829 := bbase (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) (by norm_num)
theorem B2048813 : Blo 908576 2048813 := bbase (se 3 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 2048813 = 768305) (by norm_num)
theorem B2048885 : Blo 908576 2048885 := bbase (se 5 (by rfl) ⟨96041, by rfl⟩ : syracuseStep 2048885 = 192083) (by norm_num)
theorem B2048957 : Blo 908576 2048957 := bbase (se 3 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 2048957 = 768359) (by norm_num)
theorem B1295365 : Blo 908576 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B2049029 : Blo 908576 2049029 := bbase (se 4 (by rfl) ⟨192096, by rfl⟩ : syracuseStep 2049029 = 384193) (by norm_num)
theorem B1229861 : Blo 908576 1229861 := bbase (se 4 (by rfl) ⟨115299, by rfl⟩ : syracuseStep 1229861 = 230599) (by norm_num)
theorem B1459253 : Blo 908576 1459253 := bbase (se 5 (by rfl) ⟨68402, by rfl⟩ : syracuseStep 1459253 = 136805) (by norm_num)
theorem B2049101 : Blo 908576 2049101 := bbase (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) (by norm_num)
theorem B1229909 : Blo 908576 1229909 := bbase (se 8 (by rfl) ⟨7206, by rfl⟩ : syracuseStep 1229909 = 14413) (by norm_num)
theorem B2049173 : Blo 908576 2049173 := bbase (se 6 (by rfl) ⟨48027, by rfl⟩ : syracuseStep 2049173 = 96055) (by norm_num)
theorem B2049245 : Blo 908576 2049245 := bbase (se 3 (by rfl) ⟨384233, by rfl⟩ : syracuseStep 2049245 = 768467) (by norm_num)
theorem B4605173 : Blo 908576 4605173 := bbase (se 5 (by rfl) ⟨215867, by rfl⟩ : syracuseStep 4605173 = 431735) (by norm_num)
theorem B2049317 : Blo 908576 2049317 := bbase (se 4 (by rfl) ⟨192123, by rfl⟩ : syracuseStep 2049317 = 384247) (by norm_num)
theorem B2049389 : Blo 908576 2049389 := bbase (se 3 (by rfl) ⟨384260, by rfl⟩ : syracuseStep 2049389 = 768521) (by norm_num)
theorem B2049461 : Blo 908576 2049461 := bbase (se 5 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 2049461 = 192137) (by norm_num)
theorem B1459669 : Blo 908576 1459669 := bbase (se 7 (by rfl) ⟨17105, by rfl⟩ : syracuseStep 1459669 = 34211) (by norm_num)
theorem B2049533 : Blo 908576 2049533 := bbase (se 3 (by rfl) ⟨384287, by rfl⟩ : syracuseStep 2049533 = 768575) (by norm_num)
theorem B2049605 : Blo 908576 2049605 := bbase (se 4 (by rfl) ⟨192150, by rfl⟩ : syracuseStep 2049605 = 384301) (by norm_num)
theorem B1295957 : Blo 908576 1295957 := bbase (se 8 (by rfl) ⟨7593, by rfl⟩ : syracuseStep 1295957 = 15187) (by norm_num)
theorem B2049677 : Blo 908576 2049677 := bbase (se 3 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 2049677 = 768629) (by norm_num)
theorem B1296037 : Blo 908576 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B2049749 : Blo 908576 2049749 := bbase (se 7 (by rfl) ⟨24020, by rfl⟩ : syracuseStep 2049749 = 48041) (by norm_num)
theorem B1296157 : Blo 908576 1296157 := bbase (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) (by norm_num)
theorem B2049821 : Blo 908576 2049821 := bbase (se 3 (by rfl) ⟨384341, by rfl⟩ : syracuseStep 2049821 = 768683) (by norm_num)
theorem B2049893 : Blo 908576 2049893 := bbase (se 4 (by rfl) ⟨192177, by rfl⟩ : syracuseStep 2049893 = 384355) (by norm_num)
theorem B1296253 : Blo 908576 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B2049965 : Blo 908576 2049965 := bbase (se 3 (by rfl) ⟨384368, by rfl⟩ : syracuseStep 2049965 = 768737) (by norm_num)
theorem B2050037 : Blo 908576 2050037 := bbase (se 5 (by rfl) ⟨96095, by rfl⟩ : syracuseStep 2050037 = 192191) (by norm_num)
theorem B5195765 : Blo 908576 5195765 := bbase (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) (by norm_num)
theorem B2050109 : Blo 908576 2050109 := bbase (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) (by norm_num)
theorem B1755245 : Blo 908576 1755245 := bbase (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) (by norm_num)
theorem B2050181 : Blo 908576 2050181 := bbase (se 4 (by rfl) ⟨192204, by rfl⟩ : syracuseStep 2050181 = 384409) (by norm_num)
theorem B2050253 : Blo 908576 2050253 := bbase (se 3 (by rfl) ⟨384422, by rfl⟩ : syracuseStep 2050253 = 768845) (by norm_num)
theorem B2050325 : Blo 908576 2050325 := bbase (se 6 (by rfl) ⟨48054, by rfl⟩ : syracuseStep 2050325 = 96109) (by norm_num)
theorem B1755445 : Blo 908576 1755445 := bbase (se 5 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 1755445 = 164573) (by norm_num)
theorem B2050397 : Blo 908576 2050397 := bbase (se 3 (by rfl) ⟨384449, by rfl⟩ : syracuseStep 2050397 = 768899) (by norm_num)
theorem B1296749 : Blo 908576 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B1460605 : Blo 908576 1460605 := bbase (se 3 (by rfl) ⟨273863, by rfl⟩ : syracuseStep 1460605 = 547727) (by norm_num)
theorem B2050469 : Blo 908576 2050469 := bbase (se 4 (by rfl) ⟨192231, by rfl⟩ : syracuseStep 2050469 = 384463) (by norm_num)
theorem B2050541 : Blo 908576 2050541 := bbase (se 3 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 2050541 = 768953) (by norm_num)
theorem B4606469 : Blo 908576 4606469 := bbase (se 4 (by rfl) ⟨431856, by rfl⟩ : syracuseStep 4606469 = 863713) (by norm_num)
theorem B2050613 : Blo 908576 2050613 := bbase (se 5 (by rfl) ⟨96122, by rfl⟩ : syracuseStep 2050613 = 192245) (by norm_num)
theorem B2050685 : Blo 908576 2050685 := bbase (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) (by norm_num)
theorem B2050757 : Blo 908576 2050757 := bbase (se 4 (by rfl) ⟨192258, by rfl⟩ : syracuseStep 2050757 = 384517) (by norm_num)
theorem B7785173 : Blo 908576 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B2050829 : Blo 908576 2050829 := bbase (se 3 (by rfl) ⟨384530, by rfl⟩ : syracuseStep 2050829 = 769061) (by norm_num)
theorem B2050901 : Blo 908576 2050901 := bbase (se 9 (by rfl) ⟨6008, by rfl⟩ : syracuseStep 2050901 = 12017) (by norm_num)
theorem B3459941 : Blo 908576 3459941 := bbase (se 4 (by rfl) ⟨324369, by rfl⟩ : syracuseStep 3459941 = 648739) (by norm_num)
theorem B1297301 : Blo 908576 1297301 := bbase (se 6 (by rfl) ⟨30405, by rfl⟩ : syracuseStep 1297301 = 60811) (by norm_num)
theorem B2050973 : Blo 908576 2050973 := bbase (se 3 (by rfl) ⟨384557, by rfl⟩ : syracuseStep 2050973 = 769115) (by norm_num)
theorem B4377509 : Blo 908576 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B1362869 : Blo 908576 1362869 := bbase (se 5 (by rfl) ⟨63884, by rfl⟩ : syracuseStep 1362869 = 127769) (by norm_num)
theorem B3066821 : Blo 908576 3066821 := bbase (se 4 (by rfl) ⟨287514, by rfl⟩ : syracuseStep 3066821 = 575029) (by norm_num)
theorem B1362893 : Blo 908576 1362893 := bbase (se 3 (by rfl) ⟨255542, by rfl⟩ : syracuseStep 1362893 = 511085) (by norm_num)
theorem B1362917 : Blo 908576 1362917 := bbase (se 4 (by rfl) ⟨127773, by rfl⟩ : syracuseStep 1362917 = 255547) (by norm_num)
theorem B2051045 : Blo 908576 2051045 := bbase (se 4 (by rfl) ⟨192285, by rfl⟩ : syracuseStep 2051045 = 384571) (by norm_num)
theorem B1362941 : Blo 908576 1362941 := bbase (se 3 (by rfl) ⟨255551, by rfl⟩ : syracuseStep 1362941 = 511103) (by norm_num)
theorem B1362965 : Blo 908576 1362965 := bbase (se 6 (by rfl) ⟨31944, by rfl⟩ : syracuseStep 1362965 = 63889) (by norm_num)
theorem B1362989 : Blo 908576 1362989 := bbase (se 3 (by rfl) ⟨255560, by rfl⟩ : syracuseStep 1362989 = 511121) (by norm_num)
theorem B2051117 : Blo 908576 2051117 := bbase (se 3 (by rfl) ⟨384584, by rfl⟩ : syracuseStep 2051117 = 769169) (by norm_num)
theorem B1363013 : Blo 908576 1363013 := bbase (se 4 (by rfl) ⟨127782, by rfl⟩ : syracuseStep 1363013 = 255565) (by norm_num)
theorem B1363037 : Blo 908576 1363037 := bbase (se 3 (by rfl) ⟨255569, by rfl⟩ : syracuseStep 1363037 = 511139) (by norm_num)
theorem B1363061 : Blo 908576 1363061 := bbase (se 5 (by rfl) ⟨63893, by rfl⟩ : syracuseStep 1363061 = 127787) (by norm_num)
theorem B2051189 : Blo 908576 2051189 := bbase (se 5 (by rfl) ⟨96149, by rfl⟩ : syracuseStep 2051189 = 192299) (by norm_num)
theorem B1559669 : Blo 908576 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B1264765 : Blo 908576 1264765 := bbase (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) (by norm_num)
theorem B3460229 : Blo 908576 3460229 := bbase (se 4 (by rfl) ⟨324396, by rfl⟩ : syracuseStep 3460229 = 648793) (by norm_num)
theorem B1363085 : Blo 908576 1363085 := bbase (se 3 (by rfl) ⟨255578, by rfl⟩ : syracuseStep 1363085 = 511157) (by norm_num)
theorem B1363109 : Blo 908576 1363109 := bbase (se 4 (by rfl) ⟨127791, by rfl⟩ : syracuseStep 1363109 = 255583) (by norm_num)
theorem B1363133 : Blo 908576 1363133 := bbase (se 3 (by rfl) ⟨255587, by rfl⟩ : syracuseStep 1363133 = 511175) (by norm_num)
theorem B2051261 : Blo 908576 2051261 := bbase (se 3 (by rfl) ⟨384611, by rfl⟩ : syracuseStep 2051261 = 769223) (by norm_num)
theorem B1363157 : Blo 908576 1363157 := bbase (se 7 (by rfl) ⟨15974, by rfl⟩ : syracuseStep 1363157 = 31949) (by norm_num)
theorem B1363181 : Blo 908576 1363181 := bbase (se 3 (by rfl) ⟨255596, by rfl⟩ : syracuseStep 1363181 = 511193) (by norm_num)
theorem B1363205 : Blo 908576 1363205 := bbase (se 4 (by rfl) ⟨127800, by rfl⟩ : syracuseStep 1363205 = 255601) (by norm_num)
theorem B2051333 : Blo 908576 2051333 := bbase (se 4 (by rfl) ⟨192312, by rfl⟩ : syracuseStep 2051333 = 384625) (by norm_num)
theorem B1363229 : Blo 908576 1363229 := bbase (se 3 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 1363229 = 511211) (by norm_num)
theorem B1363253 : Blo 908576 1363253 := bbase (se 5 (by rfl) ⟨63902, by rfl⟩ : syracuseStep 1363253 = 127805) (by norm_num)
theorem B5918005 : Blo 908576 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B1363277 : Blo 908576 1363277 := bbase (se 3 (by rfl) ⟨255614, by rfl⟩ : syracuseStep 1363277 = 511229) (by norm_num)
theorem B2051405 : Blo 908576 2051405 := bbase (se 3 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 2051405 = 769277) (by norm_num)
theorem B1363301 : Blo 908576 1363301 := bbase (se 4 (by rfl) ⟨127809, by rfl⟩ : syracuseStep 1363301 = 255619) (by norm_num)
theorem B3067253 : Blo 908576 3067253 := bbase (se 5 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 3067253 = 287555) (by norm_num)
theorem B1363325 : Blo 908576 1363325 := bbase (se 3 (by rfl) ⟨255623, by rfl⟩ : syracuseStep 1363325 = 511247) (by norm_num)
theorem B1363349 : Blo 908576 1363349 := bbase (se 6 (by rfl) ⟨31953, by rfl⟩ : syracuseStep 1363349 = 63907) (by norm_num)
theorem B2051477 : Blo 908576 2051477 := bbase (se 6 (by rfl) ⟨48081, by rfl⟩ : syracuseStep 2051477 = 96163) (by norm_num)
theorem B1363373 : Blo 908576 1363373 := bbase (se 3 (by rfl) ⟨255632, by rfl⟩ : syracuseStep 1363373 = 511265) (by norm_num)
theorem B1363397 : Blo 908576 1363397 := bbase (se 4 (by rfl) ⟨127818, by rfl⟩ : syracuseStep 1363397 = 255637) (by norm_num)
theorem B1363421 : Blo 908576 1363421 := bbase (se 3 (by rfl) ⟨255641, by rfl⟩ : syracuseStep 1363421 = 511283) (by norm_num)
theorem B2051549 : Blo 908576 2051549 := bbase (se 3 (by rfl) ⟨384665, by rfl⟩ : syracuseStep 2051549 = 769331) (by norm_num)
theorem B1363445 : Blo 908576 1363445 := bbase (se 5 (by rfl) ⟨63911, by rfl⟩ : syracuseStep 1363445 = 127823) (by norm_num)
theorem B1363469 : Blo 908576 1363469 := bbase (se 3 (by rfl) ⟨255650, by rfl⟩ : syracuseStep 1363469 = 511301) (by norm_num)
theorem B1363493 : Blo 908576 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B2051621 : Blo 908576 2051621 := bbase (se 4 (by rfl) ⟨192339, by rfl⟩ : syracuseStep 2051621 = 384679) (by norm_num)
theorem B1363517 : Blo 908576 1363517 := bbase (se 3 (by rfl) ⟨255659, by rfl⟩ : syracuseStep 1363517 = 511319) (by norm_num)
theorem B1363541 : Blo 908576 1363541 := bbase (se 8 (by rfl) ⟨7989, by rfl⟩ : syracuseStep 1363541 = 15979) (by norm_num)
theorem B1363565 : Blo 908576 1363565 := bbase (se 3 (by rfl) ⟨255668, by rfl⟩ : syracuseStep 1363565 = 511337) (by norm_num)
theorem B2051693 : Blo 908576 2051693 := bbase (se 3 (by rfl) ⟨384692, by rfl⟩ : syracuseStep 2051693 = 769385) (by norm_num)
theorem B4673141 : Blo 908576 4673141 := bbase (se 5 (by rfl) ⟨219053, by rfl⟩ : syracuseStep 4673141 = 438107) (by norm_num)
theorem B1363589 : Blo 908576 1363589 := bbase (se 4 (by rfl) ⟨127836, by rfl⟩ : syracuseStep 1363589 = 255673) (by norm_num)
theorem B1298053 : Blo 908576 1298053 := bbase (se 4 (by rfl) ⟨121692, by rfl⟩ : syracuseStep 1298053 = 243385) (by norm_num)
theorem B1363613 : Blo 908576 1363613 := bbase (se 3 (by rfl) ⟨255677, by rfl⟩ : syracuseStep 1363613 = 511355) (by norm_num)
theorem B1363637 : Blo 908576 1363637 := bbase (se 5 (by rfl) ⟨63920, by rfl⟩ : syracuseStep 1363637 = 127841) (by norm_num)
theorem B2051765 : Blo 908576 2051765 := bbase (se 5 (by rfl) ⟨96176, by rfl⟩ : syracuseStep 2051765 = 192353) (by norm_num)
theorem B1363661 : Blo 908576 1363661 := bbase (se 3 (by rfl) ⟨255686, by rfl⟩ : syracuseStep 1363661 = 511373) (by norm_num)
theorem B1363685 : Blo 908576 1363685 := bbase (se 4 (by rfl) ⟨127845, by rfl⟩ : syracuseStep 1363685 = 255691) (by norm_num)
theorem B1363709 : Blo 908576 1363709 := bbase (se 3 (by rfl) ⟨255695, by rfl⟩ : syracuseStep 1363709 = 511391) (by norm_num)
theorem B2051837 : Blo 908576 2051837 := bbase (se 3 (by rfl) ⟨384719, by rfl⟩ : syracuseStep 2051837 = 769439) (by norm_num)
theorem B1363733 : Blo 908576 1363733 := bbase (se 6 (by rfl) ⟨31962, by rfl⟩ : syracuseStep 1363733 = 63925) (by norm_num)
theorem B4607765 : Blo 908576 4607765 := bbase (se 6 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 4607765 = 215989) (by norm_num)
theorem B3067685 : Blo 908576 3067685 := bbase (se 4 (by rfl) ⟨287595, by rfl⟩ : syracuseStep 3067685 = 575191) (by norm_num)
theorem B1232677 : Blo 908576 1232677 := bbase (se 4 (by rfl) ⟨115563, by rfl⟩ : syracuseStep 1232677 = 231127) (by norm_num)
theorem B1363757 : Blo 908576 1363757 := bbase (se 3 (by rfl) ⟨255704, by rfl⟩ : syracuseStep 1363757 = 511409) (by norm_num)
theorem B1363781 : Blo 908576 1363781 := bbase (se 4 (by rfl) ⟨127854, by rfl⟩ : syracuseStep 1363781 = 255709) (by norm_num)
theorem B2051909 : Blo 908576 2051909 := bbase (se 4 (by rfl) ⟨192366, by rfl⟩ : syracuseStep 2051909 = 384733) (by norm_num)
theorem B1363805 : Blo 908576 1363805 := bbase (se 3 (by rfl) ⟨255713, by rfl⟩ : syracuseStep 1363805 = 511427) (by norm_num)
theorem B970601 : Blo 908576 970601 := bbase (se 2 (by rfl) ⟨363975, by rfl⟩ : syracuseStep 970601 = 727951) (by norm_num)
theorem B1363829 : Blo 908576 1363829 := bbase (se 5 (by rfl) ⟨63929, by rfl⟩ : syracuseStep 1363829 = 127859) (by norm_num)
theorem B1363853 : Blo 908576 1363853 := bbase (se 3 (by rfl) ⟨255722, by rfl⟩ : syracuseStep 1363853 = 511445) (by norm_num)
theorem B2051981 : Blo 908576 2051981 := bbase (se 3 (by rfl) ⟨384746, by rfl⟩ : syracuseStep 2051981 = 769493) (by norm_num)
theorem B970661 : Blo 908576 970661 := bbase (se 4 (by rfl) ⟨90999, by rfl⟩ : syracuseStep 970661 = 181999) (by norm_num)
theorem B1363877 : Blo 908576 1363877 := bbase (se 4 (by rfl) ⟨127863, by rfl⟩ : syracuseStep 1363877 = 255727) (by norm_num)
theorem B6901685 : Blo 908576 6901685 := bbase (se 5 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 6901685 = 647033) (by norm_num)
theorem B1363901 : Blo 908576 1363901 := bbase (se 3 (by rfl) ⟨255731, by rfl⟩ : syracuseStep 1363901 = 511463) (by norm_num)
theorem B1363925 : Blo 908576 1363925 := bbase (se 7 (by rfl) ⟨15983, by rfl⟩ : syracuseStep 1363925 = 31967) (by norm_num)
theorem B2052053 : Blo 908576 2052053 := bbase (se 7 (by rfl) ⟨24047, by rfl⟩ : syracuseStep 2052053 = 48095) (by norm_num)
theorem B1363949 : Blo 908576 1363949 := bbase (se 3 (by rfl) ⟨255740, by rfl⟩ : syracuseStep 1363949 = 511481) (by norm_num)
theorem B1363973 : Blo 908576 1363973 := bbase (se 4 (by rfl) ⟨127872, by rfl⟩ : syracuseStep 1363973 = 255745) (by norm_num)
theorem B1363997 : Blo 908576 1363997 := bbase (se 3 (by rfl) ⟨255749, by rfl⟩ : syracuseStep 1363997 = 511499) (by norm_num)
theorem B2052125 : Blo 908576 2052125 := bbase (se 3 (by rfl) ⟨384773, by rfl⟩ : syracuseStep 2052125 = 769547) (by norm_num)
theorem B970789 : Blo 908576 970789 := bbase (se 4 (by rfl) ⟨91011, by rfl⟩ : syracuseStep 970789 = 182023) (by norm_num)
theorem B1364021 : Blo 908576 1364021 := bbase (se 5 (by rfl) ⟨63938, by rfl⟩ : syracuseStep 1364021 = 127877) (by norm_num)
theorem B1036349 : Blo 908576 1036349 := bbase (se 3 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 1036349 = 388631) (by norm_num)
theorem B1364045 : Blo 908576 1364045 := bbase (se 3 (by rfl) ⟨255758, by rfl⟩ : syracuseStep 1364045 = 511517) (by norm_num)
theorem B3887189 : Blo 908576 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B1364069 : Blo 908576 1364069 := bbase (se 4 (by rfl) ⟨127881, by rfl⟩ : syracuseStep 1364069 = 255763) (by norm_num)
theorem B2052197 : Blo 908576 2052197 := bbase (se 4 (by rfl) ⟨192393, by rfl⟩ : syracuseStep 2052197 = 384787) (by norm_num)
theorem B1036405 : Blo 908576 1036405 := bbase (se 5 (by rfl) ⟨48581, by rfl⟩ : syracuseStep 1036405 = 97163) (by norm_num)
theorem B1364093 : Blo 908576 1364093 := bbase (se 3 (by rfl) ⟨255767, by rfl⟩ : syracuseStep 1364093 = 511535) (by norm_num)
theorem B1364117 : Blo 908576 1364117 := bbase (se 6 (by rfl) ⟨31971, by rfl⟩ : syracuseStep 1364117 = 63943) (by norm_num)
theorem B1364141 : Blo 908576 1364141 := bbase (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) (by norm_num)
theorem B2052269 : Blo 908576 2052269 := bbase (se 3 (by rfl) ⟨384800, by rfl⟩ : syracuseStep 2052269 = 769601) (by norm_num)
theorem B1364165 : Blo 908576 1364165 := bbase (se 4 (by rfl) ⟨127890, by rfl⟩ : syracuseStep 1364165 = 255781) (by norm_num)
theorem B3068117 : Blo 908576 3068117 := bbase (se 7 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 3068117 = 71909) (by norm_num)
theorem B1364189 : Blo 908576 1364189 := bbase (se 3 (by rfl) ⟨255785, by rfl⟩ : syracuseStep 1364189 = 511571) (by norm_num)
theorem B4378853 : Blo 908576 4378853 := bbase (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) (by norm_num)
theorem B1364213 : Blo 908576 1364213 := bbase (se 5 (by rfl) ⟨63947, by rfl⟩ : syracuseStep 1364213 = 127895) (by norm_num)
theorem B2052341 : Blo 908576 2052341 := bbase (se 5 (by rfl) ⟨96203, by rfl⟩ : syracuseStep 2052341 = 192407) (by norm_num)
theorem B1364237 : Blo 908576 1364237 := bbase (se 3 (by rfl) ⟨255794, by rfl⟩ : syracuseStep 1364237 = 511589) (by norm_num)
theorem B1364261 : Blo 908576 1364261 := bbase (se 4 (by rfl) ⟨127899, by rfl⟩ : syracuseStep 1364261 = 255799) (by norm_num)
theorem B3461413 : Blo 908576 3461413 := bbase (se 4 (by rfl) ⟨324507, by rfl⟩ : syracuseStep 3461413 = 649015) (by norm_num)
theorem B1364285 : Blo 908576 1364285 := bbase (se 3 (by rfl) ⟨255803, by rfl⟩ : syracuseStep 1364285 = 511607) (by norm_num)
theorem B2052413 : Blo 908576 2052413 := bbase (se 3 (by rfl) ⟨384827, by rfl⟩ : syracuseStep 2052413 = 769655) (by norm_num)
theorem B1364309 : Blo 908576 1364309 := bbase (se 10 (by rfl) ⟨1998, by rfl⟩ : syracuseStep 1364309 = 3997) (by norm_num)
theorem B1364333 : Blo 908576 1364333 := bbase (se 3 (by rfl) ⟨255812, by rfl⟩ : syracuseStep 1364333 = 511625) (by norm_num)
theorem B1364357 : Blo 908576 1364357 := bbase (se 4 (by rfl) ⟨127908, by rfl⟩ : syracuseStep 1364357 = 255817) (by norm_num)
theorem B2052485 : Blo 908576 2052485 := bbase (se 4 (by rfl) ⟨192420, by rfl⟩ : syracuseStep 2052485 = 384841) (by norm_num)
theorem B1364381 : Blo 908576 1364381 := bbase (se 3 (by rfl) ⟨255821, by rfl⟩ : syracuseStep 1364381 = 511643) (by norm_num)
theorem B1298845 : Blo 908576 1298845 := bbase (se 3 (by rfl) ⟨243533, by rfl⟩ : syracuseStep 1298845 = 487067) (by norm_num)
theorem B1364405 : Blo 908576 1364405 := bbase (se 5 (by rfl) ⟨63956, by rfl⟩ : syracuseStep 1364405 = 127913) (by norm_num)
theorem B1364429 : Blo 908576 1364429 := bbase (se 3 (by rfl) ⟨255830, by rfl⟩ : syracuseStep 1364429 = 511661) (by norm_num)
theorem B2052557 : Blo 908576 2052557 := bbase (se 3 (by rfl) ⟨384854, by rfl⟩ : syracuseStep 2052557 = 769709) (by norm_num)
theorem B971233 : Blo 908576 971233 := bbase (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) (by norm_num)
theorem B1364453 : Blo 908576 1364453 := bbase (se 4 (by rfl) ⟨127917, by rfl⟩ : syracuseStep 1364453 = 255835) (by norm_num)
theorem B1364477 : Blo 908576 1364477 := bbase (se 3 (by rfl) ⟨255839, by rfl⟩ : syracuseStep 1364477 = 511679) (by norm_num)
theorem B1364501 : Blo 908576 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B2052629 : Blo 908576 2052629 := bbase (se 6 (by rfl) ⟨48108, by rfl⟩ : syracuseStep 2052629 = 96217) (by norm_num)
theorem B1364525 : Blo 908576 1364525 := bbase (se 3 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 1364525 = 511697) (by norm_num)
theorem B1724989 : Blo 908576 1724989 := bbase (se 3 (by rfl) ⟨323435, by rfl⟩ : syracuseStep 1724989 = 646871) (by norm_num)
theorem B1364549 : Blo 908576 1364549 := bbase (se 4 (by rfl) ⟨127926, by rfl⟩ : syracuseStep 1364549 = 255853) (by norm_num)
theorem B3461717 : Blo 908576 3461717 := bbase (se 8 (by rfl) ⟨20283, by rfl⟩ : syracuseStep 3461717 = 40567) (by norm_num)
theorem B971353 : Blo 908576 971353 := bbase (se 2 (by rfl) ⟨364257, by rfl⟩ : syracuseStep 971353 = 728515) (by norm_num)
theorem B1364573 : Blo 908576 1364573 := bbase (se 3 (by rfl) ⟨255857, by rfl⟩ : syracuseStep 1364573 = 511715) (by norm_num)
theorem B2052701 : Blo 908576 2052701 := bbase (se 3 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 2052701 = 769763) (by norm_num)
theorem B1364597 : Blo 908576 1364597 := bbase (se 5 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 1364597 = 127931) (by norm_num)
theorem B3068549 : Blo 908576 3068549 := bbase (se 4 (by rfl) ⟨287676, by rfl⟩ : syracuseStep 3068549 = 575353) (by norm_num)
theorem B1364621 : Blo 908576 1364621 := bbase (se 3 (by rfl) ⟨255866, by rfl⟩ : syracuseStep 1364621 = 511733) (by norm_num)
theorem B1364645 : Blo 908576 1364645 := bbase (se 4 (by rfl) ⟨127935, by rfl⟩ : syracuseStep 1364645 = 255871) (by norm_num)
theorem B2052773 : Blo 908576 2052773 := bbase (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) (by norm_num)
theorem B1364669 : Blo 908576 1364669 := bbase (se 3 (by rfl) ⟨255875, by rfl⟩ : syracuseStep 1364669 = 511751) (by norm_num)
theorem B1725133 : Blo 908576 1725133 := bbase (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) (by norm_num)
theorem B1364693 : Blo 908576 1364693 := bbase (se 7 (by rfl) ⟨15992, by rfl⟩ : syracuseStep 1364693 = 31985) (by norm_num)
theorem B1364717 : Blo 908576 1364717 := bbase (se 3 (by rfl) ⟨255884, by rfl⟩ : syracuseStep 1364717 = 511769) (by norm_num)
theorem B2052845 : Blo 908576 2052845 := bbase (se 3 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 2052845 = 769817) (by norm_num)
theorem B1299181 : Blo 908576 1299181 := bbase (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) (by norm_num)
theorem B1364741 : Blo 908576 1364741 := bbase (se 4 (by rfl) ⟨127944, by rfl⟩ : syracuseStep 1364741 = 255889) (by norm_num)
theorem B1364765 : Blo 908576 1364765 := bbase (se 3 (by rfl) ⟨255893, by rfl⟩ : syracuseStep 1364765 = 511787) (by norm_num)
theorem B1364789 : Blo 908576 1364789 := bbase (se 5 (by rfl) ⟨63974, by rfl⟩ : syracuseStep 1364789 = 127949) (by norm_num)
theorem B2052917 : Blo 908576 2052917 := bbase (se 5 (by rfl) ⟨96230, by rfl⟩ : syracuseStep 2052917 = 192461) (by norm_num)
theorem B1037125 : Blo 908576 1037125 := bbase (se 4 (by rfl) ⟨97230, by rfl⟩ : syracuseStep 1037125 = 194461) (by norm_num)
theorem B1364813 : Blo 908576 1364813 := bbase (se 3 (by rfl) ⟨255902, by rfl⟩ : syracuseStep 1364813 = 511805) (by norm_num)
theorem B971605 : Blo 908576 971605 := bbase (se 9 (by rfl) ⟨2846, by rfl⟩ : syracuseStep 971605 = 5693) (by norm_num)
theorem B971609 : Blo 908576 971609 := bbase (se 2 (by rfl) ⟨364353, by rfl⟩ : syracuseStep 971609 = 728707) (by norm_num)
theorem B1364837 : Blo 908576 1364837 := bbase (se 4 (by rfl) ⟨127953, by rfl⟩ : syracuseStep 1364837 = 255907) (by norm_num)
theorem B1725293 : Blo 908576 1725293 := bbase (se 3 (by rfl) ⟨323492, by rfl⟩ : syracuseStep 1725293 = 646985) (by norm_num)
theorem B1364861 : Blo 908576 1364861 := bbase (se 3 (by rfl) ⟨255911, by rfl⟩ : syracuseStep 1364861 = 511823) (by norm_num)
theorem B2052989 : Blo 908576 2052989 := bbase (se 3 (by rfl) ⟨384935, by rfl⟩ : syracuseStep 2052989 = 769871) (by norm_num)
theorem B1364885 : Blo 908576 1364885 := bbase (se 6 (by rfl) ⟨31989, by rfl⟩ : syracuseStep 1364885 = 63979) (by norm_num)
theorem B1364909 : Blo 908576 1364909 := bbase (se 3 (by rfl) ⟨255920, by rfl⟩ : syracuseStep 1364909 = 511841) (by norm_num)
theorem B1364933 : Blo 908576 1364933 := bbase (se 4 (by rfl) ⟨127962, by rfl⟩ : syracuseStep 1364933 = 255925) (by norm_num)
theorem B2053061 : Blo 908576 2053061 := bbase (se 4 (by rfl) ⟨192474, by rfl⟩ : syracuseStep 2053061 = 384949) (by norm_num)
theorem B1364957 : Blo 908576 1364957 := bbase (se 3 (by rfl) ⟨255929, by rfl⟩ : syracuseStep 1364957 = 511859) (by norm_num)
theorem B1168357 : Blo 908576 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B1364981 : Blo 908576 1364981 := bbase (se 5 (by rfl) ⟨63983, by rfl⟩ : syracuseStep 1364981 = 127967) (by norm_num)
theorem B1725437 : Blo 908576 1725437 := bbase (se 3 (by rfl) ⟨323519, by rfl⟩ : syracuseStep 1725437 = 647039) (by norm_num)
theorem B1365005 : Blo 908576 1365005 := bbase (se 3 (by rfl) ⟨255938, by rfl⟩ : syracuseStep 1365005 = 511877) (by norm_num)
theorem B2053133 : Blo 908576 2053133 := bbase (se 3 (by rfl) ⟨384962, by rfl⟩ : syracuseStep 2053133 = 769925) (by norm_num)
theorem B1365029 : Blo 908576 1365029 := bbase (se 4 (by rfl) ⟨127971, by rfl⟩ : syracuseStep 1365029 = 255943) (by norm_num)
theorem B4609061 : Blo 908576 4609061 := bbase (se 4 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 4609061 = 864199) (by norm_num)
theorem B3068981 : Blo 908576 3068981 := bbase (se 5 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 3068981 = 287717) (by norm_num)
theorem B1365053 : Blo 908576 1365053 := bbase (se 3 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 1365053 = 511895) (by norm_num)
theorem B1365077 : Blo 908576 1365077 := bbase (se 8 (by rfl) ⟨7998, by rfl⟩ : syracuseStep 1365077 = 15997) (by norm_num)
theorem B2053205 : Blo 908576 2053205 := bbase (se 8 (by rfl) ⟨12030, by rfl⟩ : syracuseStep 2053205 = 24061) (by norm_num)
theorem B1365101 : Blo 908576 1365101 := bbase (se 3 (by rfl) ⟨255956, by rfl⟩ : syracuseStep 1365101 = 511913) (by norm_num)
theorem B1365125 : Blo 908576 1365125 := bbase (se 4 (by rfl) ⟨127980, by rfl⟩ : syracuseStep 1365125 = 255961) (by norm_num)
theorem B1365149 : Blo 908576 1365149 := bbase (se 3 (by rfl) ⟨255965, by rfl⟩ : syracuseStep 1365149 = 511931) (by norm_num)
theorem B2053277 : Blo 908576 2053277 := bbase (se 3 (by rfl) ⟨384989, by rfl⟩ : syracuseStep 2053277 = 769979) (by norm_num)
theorem B1660085 : Blo 908576 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B1365173 : Blo 908576 1365173 := bbase (se 5 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 1365173 = 127985) (by norm_num)
theorem B1365197 : Blo 908576 1365197 := bbase (se 3 (by rfl) ⟨255974, by rfl⟩ : syracuseStep 1365197 = 511949) (by norm_num)
theorem B2184421 : Blo 908576 2184421 := bbase (se 4 (by rfl) ⟨204789, by rfl⟩ : syracuseStep 2184421 = 409579) (by norm_num)
theorem B1365221 : Blo 908576 1365221 := bbase (se 4 (by rfl) ⟨127989, by rfl⟩ : syracuseStep 1365221 = 255979) (by norm_num)
theorem B1365245 : Blo 908576 1365245 := bbase (se 3 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 1365245 = 511967) (by norm_num)
theorem B1365269 : Blo 908576 1365269 := bbase (se 6 (by rfl) ⟨31998, by rfl⟩ : syracuseStep 1365269 = 63997) (by norm_num)
theorem B1725725 : Blo 908576 1725725 := bbase (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) (by norm_num)
theorem B1365293 : Blo 908576 1365293 := bbase (se 3 (by rfl) ⟨255992, by rfl⟩ : syracuseStep 1365293 = 511985) (by norm_num)
theorem B1365317 : Blo 908576 1365317 := bbase (se 4 (by rfl) ⟨127998, by rfl⟩ : syracuseStep 1365317 = 255997) (by norm_num)
theorem B1365341 : Blo 908576 1365341 := bbase (se 3 (by rfl) ⟨256001, by rfl⟩ : syracuseStep 1365341 = 512003) (by norm_num)
theorem B1365365 : Blo 908576 1365365 := bbase (se 5 (by rfl) ⟨64001, by rfl⟩ : syracuseStep 1365365 = 128003) (by norm_num)
theorem B1365389 : Blo 908576 1365389 := bbase (se 3 (by rfl) ⟨256010, by rfl⟩ : syracuseStep 1365389 = 512021) (by norm_num)
theorem B972173 : Blo 908576 972173 := bbase (se 3 (by rfl) ⟨182282, by rfl⟩ : syracuseStep 972173 = 364565) (by norm_num)
theorem B1365413 : Blo 908576 1365413 := bbase (se 4 (by rfl) ⟨128007, by rfl⟩ : syracuseStep 1365413 = 256015) (by norm_num)
theorem B1725877 : Blo 908576 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B1365437 : Blo 908576 1365437 := bbase (se 3 (by rfl) ⟨256019, by rfl⟩ : syracuseStep 1365437 = 512039) (by norm_num)
theorem B1168849 : Blo 908576 1168849 := bbase (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) (by norm_num)
theorem B1365461 : Blo 908576 1365461 := bbase (se 7 (by rfl) ⟨16001, by rfl⟩ : syracuseStep 1365461 = 32003) (by norm_num)
theorem B3069413 : Blo 908576 3069413 := bbase (se 4 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 3069413 = 575515) (by norm_num)
theorem B1365485 : Blo 908576 1365485 := bbase (se 3 (by rfl) ⟨256028, by rfl⟩ : syracuseStep 1365485 = 512057) (by norm_num)
theorem B1365509 : Blo 908576 1365509 := bbase (se 4 (by rfl) ⟨128016, by rfl⟩ : syracuseStep 1365509 = 256033) (by norm_num)
theorem B1365533 : Blo 908576 1365533 := bbase (se 3 (by rfl) ⟨256037, by rfl⟩ : syracuseStep 1365533 = 512075) (by norm_num)
theorem B1365557 : Blo 908576 1365557 := bbase (se 5 (by rfl) ⟨64010, by rfl⟩ : syracuseStep 1365557 = 128021) (by norm_num)
theorem B972361 : Blo 908576 972361 := bbase (se 2 (by rfl) ⟨364635, by rfl⟩ : syracuseStep 972361 = 729271) (by norm_num)
theorem B1365581 : Blo 908576 1365581 := bbase (se 3 (by rfl) ⟨256046, by rfl⟩ : syracuseStep 1365581 = 512093) (by norm_num)
theorem B1365605 : Blo 908576 1365605 := bbase (se 4 (by rfl) ⟨128025, by rfl⟩ : syracuseStep 1365605 = 256051) (by norm_num)
theorem B4380277 : Blo 908576 4380277 := bbase (se 5 (by rfl) ⟨205325, by rfl⟩ : syracuseStep 4380277 = 410651) (by norm_num)
theorem B7788149 : Blo 908576 7788149 := bbase (se 5 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 7788149 = 730139) (by norm_num)
theorem B1365629 : Blo 908576 1365629 := bbase (se 3 (by rfl) ⟨256055, by rfl⟩ : syracuseStep 1365629 = 512111) (by norm_num)
theorem B1365653 : Blo 908576 1365653 := bbase (se 6 (by rfl) ⟨32007, by rfl⟩ : syracuseStep 1365653 = 64015) (by norm_num)
theorem B1365677 : Blo 908576 1365677 := bbase (se 3 (by rfl) ⟨256064, by rfl⟩ : syracuseStep 1365677 = 512129) (by norm_num)
theorem B1365701 : Blo 908576 1365701 := bbase (se 4 (by rfl) ⟨128034, by rfl⟩ : syracuseStep 1365701 = 256069) (by norm_num)
theorem B1365725 : Blo 908576 1365725 := bbase (se 3 (by rfl) ⟨256073, by rfl⟩ : syracuseStep 1365725 = 512147) (by norm_num)
theorem B1726181 : Blo 908576 1726181 := bbase (se 4 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 1726181 = 323659) (by norm_num)
theorem B1365749 : Blo 908576 1365749 := bbase (se 5 (by rfl) ⟨64019, by rfl⟩ : syracuseStep 1365749 = 128039) (by norm_num)
theorem B1365773 : Blo 908576 1365773 := bbase (se 3 (by rfl) ⟨256082, by rfl⟩ : syracuseStep 1365773 = 512165) (by norm_num)
theorem B1038101 : Blo 908576 1038101 := bbase (se 6 (by rfl) ⟨24330, by rfl⟩ : syracuseStep 1038101 = 48661) (by norm_num)
theorem B1365797 : Blo 908576 1365797 := bbase (se 4 (by rfl) ⟨128043, by rfl⟩ : syracuseStep 1365797 = 256087) (by norm_num)
theorem B1365821 : Blo 908576 1365821 := bbase (se 3 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 1365821 = 512183) (by norm_num)
theorem B3888965 : Blo 908576 3888965 := bbase (se 4 (by rfl) ⟨364590, by rfl⟩ : syracuseStep 3888965 = 729181) (by norm_num)
theorem B1365845 : Blo 908576 1365845 := bbase (se 9 (by rfl) ⟨4001, by rfl⟩ : syracuseStep 1365845 = 8003) (by norm_num)
theorem B1365869 : Blo 908576 1365869 := bbase (se 3 (by rfl) ⟨256100, by rfl⟩ : syracuseStep 1365869 = 512201) (by norm_num)
theorem B1365893 : Blo 908576 1365893 := bbase (se 4 (by rfl) ⟨128052, by rfl⟩ : syracuseStep 1365893 = 256105) (by norm_num)
theorem B3069845 : Blo 908576 3069845 := bbase (se 6 (by rfl) ⟨71949, by rfl⟩ : syracuseStep 3069845 = 143899) (by norm_num)
theorem B1365917 : Blo 908576 1365917 := bbase (se 3 (by rfl) ⟨256109, by rfl⟩ : syracuseStep 1365917 = 512219) (by norm_num)
theorem B1365941 : Blo 908576 1365941 := bbase (se 5 (by rfl) ⟨64028, by rfl⟩ : syracuseStep 1365941 = 128057) (by norm_num)
theorem B1365965 : Blo 908576 1365965 := bbase (se 3 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 1365965 = 512237) (by norm_num)
theorem B2807765 : Blo 908576 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B1365989 : Blo 908576 1365989 := bbase (se 4 (by rfl) ⟨128061, by rfl⟩ : syracuseStep 1365989 = 256123) (by norm_num)
theorem B1366013 : Blo 908576 1366013 := bbase (se 3 (by rfl) ⟨256127, by rfl⟩ : syracuseStep 1366013 = 512255) (by norm_num)
theorem B1366037 : Blo 908576 1366037 := bbase (se 6 (by rfl) ⟨32016, by rfl⟩ : syracuseStep 1366037 = 64033) (by norm_num)
theorem B1366061 : Blo 908576 1366061 := bbase (se 3 (by rfl) ⟨256136, by rfl⟩ : syracuseStep 1366061 = 512273) (by norm_num)
theorem B3889205 : Blo 908576 3889205 := bbase (se 5 (by rfl) ⟨182306, by rfl⟩ : syracuseStep 3889205 = 364613) (by norm_num)
theorem B1366085 : Blo 908576 1366085 := bbase (se 4 (by rfl) ⟨128070, by rfl⟩ : syracuseStep 1366085 = 256141) (by norm_num)
theorem B1169485 : Blo 908576 1169485 := bbase (se 3 (by rfl) ⟨219278, by rfl⟩ : syracuseStep 1169485 = 438557) (by norm_num)
theorem B1038425 : Blo 908576 1038425 := bbase (se 2 (by rfl) ⟨389409, by rfl⟩ : syracuseStep 1038425 = 778819) (by norm_num)
theorem B1366109 : Blo 908576 1366109 := bbase (se 3 (by rfl) ⟨256145, by rfl⟩ : syracuseStep 1366109 = 512291) (by norm_num)
theorem B1366133 : Blo 908576 1366133 := bbase (se 5 (by rfl) ⟨64037, by rfl⟩ : syracuseStep 1366133 = 128075) (by norm_num)
theorem B1366157 : Blo 908576 1366157 := bbase (se 3 (by rfl) ⟨256154, by rfl⟩ : syracuseStep 1366157 = 512309) (by norm_num)
theorem B1366181 : Blo 908576 1366181 := bbase (se 4 (by rfl) ⟨128079, by rfl⟩ : syracuseStep 1366181 = 256159) (by norm_num)
theorem B1366205 : Blo 908576 1366205 := bbase (se 3 (by rfl) ⟨256163, by rfl⟩ : syracuseStep 1366205 = 512327) (by norm_num)
theorem B1366229 : Blo 908576 1366229 := bbase (se 7 (by rfl) ⟨16010, by rfl⟩ : syracuseStep 1366229 = 32021) (by norm_num)
theorem B1366253 : Blo 908576 1366253 := bbase (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) (by norm_num)
theorem B1366277 : Blo 908576 1366277 := bbase (se 4 (by rfl) ⟨128088, by rfl⟩ : syracuseStep 1366277 = 256177) (by norm_num)
theorem B1366301 : Blo 908576 1366301 := bbase (se 3 (by rfl) ⟨256181, by rfl⟩ : syracuseStep 1366301 = 512363) (by norm_num)
theorem B4610357 : Blo 908576 4610357 := bbase (se 5 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 4610357 = 432221) (by norm_num)
theorem B1366325 : Blo 908576 1366325 := bbase (se 5 (by rfl) ⟨64046, by rfl⟩ : syracuseStep 1366325 = 128093) (by norm_num)
theorem B1038649 : Blo 908576 1038649 := bbase (se 2 (by rfl) ⟨389493, by rfl⟩ : syracuseStep 1038649 = 778987) (by norm_num)
theorem B3070277 : Blo 908576 3070277 := bbase (se 4 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 3070277 = 575677) (by norm_num)
theorem B1366349 : Blo 908576 1366349 := bbase (se 3 (by rfl) ⟨256190, by rfl⟩ : syracuseStep 1366349 = 512381) (by norm_num)
theorem B1366373 : Blo 908576 1366373 := bbase (se 4 (by rfl) ⟨128097, by rfl⟩ : syracuseStep 1366373 = 256195) (by norm_num)
theorem B1366397 : Blo 908576 1366397 := bbase (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) (by norm_num)
theorem B973181 : Blo 908576 973181 := bbase (se 3 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 973181 = 364943) (by norm_num)
theorem B1366421 : Blo 908576 1366421 := bbase (se 6 (by rfl) ⟨32025, by rfl⟩ : syracuseStep 1366421 = 64051) (by norm_num)
theorem B2251157 : Blo 908576 2251157 := bbase (se 6 (by rfl) ⟨52761, by rfl⟩ : syracuseStep 2251157 = 105523) (by norm_num)
theorem B1366445 : Blo 908576 1366445 := bbase (se 3 (by rfl) ⟨256208, by rfl⟩ : syracuseStep 1366445 = 512417) (by norm_num)
theorem B1366469 : Blo 908576 1366469 := bbase (se 4 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 1366469 = 256213) (by norm_num)
theorem B1726933 : Blo 908576 1726933 := bbase (se 7 (by rfl) ⟨20237, by rfl⟩ : syracuseStep 1726933 = 40475) (by norm_num)
theorem B1366493 : Blo 908576 1366493 := bbase (se 3 (by rfl) ⟨256217, by rfl⟩ : syracuseStep 1366493 = 512435) (by norm_num)
theorem B1366517 : Blo 908576 1366517 := bbase (se 5 (by rfl) ⟨64055, by rfl⟩ : syracuseStep 1366517 = 128111) (by norm_num)
theorem B1366541 : Blo 908576 1366541 := bbase (se 3 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 1366541 = 512453) (by norm_num)
theorem B1366565 : Blo 908576 1366565 := bbase (se 4 (by rfl) ⟨128115, by rfl⟩ : syracuseStep 1366565 = 256231) (by norm_num)
theorem B1366589 : Blo 908576 1366589 := bbase (se 3 (by rfl) ⟨256235, by rfl⟩ : syracuseStep 1366589 = 512471) (by norm_num)
theorem B2185805 : Blo 908576 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B2185813 : Blo 908576 2185813 := bbase (se 8 (by rfl) ⟨12807, by rfl⟩ : syracuseStep 2185813 = 25615) (by norm_num)
theorem B1366613 : Blo 908576 1366613 := bbase (se 8 (by rfl) ⟨8007, by rfl⟩ : syracuseStep 1366613 = 16015) (by norm_num)
theorem B1727077 : Blo 908576 1727077 := bbase (se 4 (by rfl) ⟨161913, by rfl⟩ : syracuseStep 1727077 = 323827) (by norm_num)
theorem B1366637 : Blo 908576 1366637 := bbase (se 3 (by rfl) ⟨256244, by rfl⟩ : syracuseStep 1366637 = 512489) (by norm_num)
theorem B1366661 : Blo 908576 1366661 := bbase (se 4 (by rfl) ⟨128124, by rfl⟩ : syracuseStep 1366661 = 256249) (by norm_num)
theorem B3463829 : Blo 908576 3463829 := bbase (se 6 (by rfl) ⟨81183, by rfl⟩ : syracuseStep 3463829 = 162367) (by norm_num)
theorem B1366685 : Blo 908576 1366685 := bbase (se 3 (by rfl) ⟨256253, by rfl⟩ : syracuseStep 1366685 = 512507) (by norm_num)
theorem B1039009 : Blo 908576 1039009 := bbase (se 2 (by rfl) ⟨389628, by rfl⟩ : syracuseStep 1039009 = 779257) (by norm_num)
theorem B1366709 : Blo 908576 1366709 := bbase (se 5 (by rfl) ⟨64064, by rfl⟩ : syracuseStep 1366709 = 128129) (by norm_num)
theorem B1366733 : Blo 908576 1366733 := bbase (se 3 (by rfl) ⟨256262, by rfl⟩ : syracuseStep 1366733 = 512525) (by norm_num)
theorem B1366757 : Blo 908576 1366757 := bbase (se 4 (by rfl) ⟨128133, by rfl⟩ : syracuseStep 1366757 = 256267) (by norm_num)
theorem B3070709 : Blo 908576 3070709 := bbase (se 5 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 3070709 = 287879) (by norm_num)
theorem B1366781 : Blo 908576 1366781 := bbase (se 3 (by rfl) ⟨256271, by rfl⟩ : syracuseStep 1366781 = 512543) (by norm_num)
theorem B1727237 : Blo 908576 1727237 := bbase (se 4 (by rfl) ⟨161928, by rfl⟩ : syracuseStep 1727237 = 323857) (by norm_num)
theorem B1366805 : Blo 908576 1366805 := bbase (se 6 (by rfl) ⟨32034, by rfl⟩ : syracuseStep 1366805 = 64069) (by norm_num)
theorem B1366829 : Blo 908576 1366829 := bbase (se 3 (by rfl) ⟨256280, by rfl⟩ : syracuseStep 1366829 = 512561) (by norm_num)
theorem B973625 : Blo 908576 973625 := bbase (se 2 (by rfl) ⟨365109, by rfl⟩ : syracuseStep 973625 = 730219) (by norm_num)
theorem B1366853 : Blo 908576 1366853 := bbase (se 4 (by rfl) ⟨128142, by rfl⟩ : syracuseStep 1366853 = 256285) (by norm_num)
theorem B1170245 : Blo 908576 1170245 := bbase (se 4 (by rfl) ⟨109710, by rfl⟩ : syracuseStep 1170245 = 219421) (by norm_num)
theorem B1366877 : Blo 908576 1366877 := bbase (se 3 (by rfl) ⟨256289, by rfl⟩ : syracuseStep 1366877 = 512579) (by norm_num)
theorem B1366901 : Blo 908576 1366901 := bbase (se 5 (by rfl) ⟨64073, by rfl⟩ : syracuseStep 1366901 = 128147) (by norm_num)
theorem B1366925 : Blo 908576 1366925 := bbase (se 3 (by rfl) ⟨256298, by rfl⟩ : syracuseStep 1366925 = 512597) (by norm_num)
theorem B1727381 : Blo 908576 1727381 := bbase (se 6 (by rfl) ⟨40485, by rfl⟩ : syracuseStep 1727381 = 80971) (by norm_num)
theorem B1366949 : Blo 908576 1366949 := bbase (se 4 (by rfl) ⟨128151, by rfl⟩ : syracuseStep 1366949 = 256303) (by norm_num)
theorem B3464117 : Blo 908576 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B1366973 : Blo 908576 1366973 := bbase (se 3 (by rfl) ⟨256307, by rfl⟩ : syracuseStep 1366973 = 512615) (by norm_num)
theorem B1366997 : Blo 908576 1366997 := bbase (se 7 (by rfl) ⟨16019, by rfl⟩ : syracuseStep 1366997 = 32039) (by norm_num)
theorem B1367021 : Blo 908576 1367021 := bbase (se 3 (by rfl) ⟨256316, by rfl⟩ : syracuseStep 1367021 = 512633) (by norm_num)
theorem B1367045 : Blo 908576 1367045 := bbase (se 4 (by rfl) ⟨128160, by rfl⟩ : syracuseStep 1367045 = 256321) (by norm_num)
theorem B1367069 : Blo 908576 1367069 := bbase (se 3 (by rfl) ⟨256325, by rfl⟩ : syracuseStep 1367069 = 512651) (by norm_num)
theorem B973873 : Blo 908576 973873 := bbase (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) (by norm_num)
theorem B1367093 : Blo 908576 1367093 := bbase (se 5 (by rfl) ⟨64082, by rfl⟩ : syracuseStep 1367093 = 128165) (by norm_num)
theorem B1367117 : Blo 908576 1367117 := bbase (se 3 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 1367117 = 512669) (by norm_num)
theorem B1367141 : Blo 908576 1367141 := bbase (se 4 (by rfl) ⟨128169, by rfl⟩ : syracuseStep 1367141 = 256339) (by norm_num)
theorem B1367165 : Blo 908576 1367165 := bbase (se 3 (by rfl) ⟨256343, by rfl⟩ : syracuseStep 1367165 = 512687) (by norm_num)
theorem B1367189 : Blo 908576 1367189 := bbase (se 6 (by rfl) ⟨32043, by rfl⟩ : syracuseStep 1367189 = 64087) (by norm_num)
theorem B3071141 : Blo 908576 3071141 := bbase (se 4 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 3071141 = 575839) (by norm_num)
theorem B1367213 : Blo 908576 1367213 := bbase (se 3 (by rfl) ⟨256352, by rfl⟩ : syracuseStep 1367213 = 512705) (by norm_num)
theorem B1727669 : Blo 908576 1727669 := bbase (se 5 (by rfl) ⟨80984, by rfl⟩ : syracuseStep 1727669 = 161969) (by norm_num)
theorem B1367237 : Blo 908576 1367237 := bbase (se 4 (by rfl) ⟨128178, by rfl⟩ : syracuseStep 1367237 = 256357) (by norm_num)
theorem B1367261 : Blo 908576 1367261 := bbase (se 3 (by rfl) ⟨256361, by rfl⟩ : syracuseStep 1367261 = 512723) (by norm_num)
theorem B1367285 : Blo 908576 1367285 := bbase (se 5 (by rfl) ⟨64091, by rfl⟩ : syracuseStep 1367285 = 128183) (by norm_num)
theorem B1367309 : Blo 908576 1367309 := bbase (se 3 (by rfl) ⟨256370, by rfl⟩ : syracuseStep 1367309 = 512741) (by norm_num)
theorem B1367333 : Blo 908576 1367333 := bbase (se 4 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 1367333 = 256375) (by norm_num)
theorem B1367357 : Blo 908576 1367357 := bbase (se 3 (by rfl) ⟨256379, by rfl⟩ : syracuseStep 1367357 = 512759) (by norm_num)
theorem B1727821 : Blo 908576 1727821 := bbase (se 3 (by rfl) ⟨323966, by rfl⟩ : syracuseStep 1727821 = 647933) (by norm_num)
theorem B14736725 : Blo 908576 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B1367381 : Blo 908576 1367381 := bbase (se 11 (by rfl) ⟨1001, by rfl⟩ : syracuseStep 1367381 = 2003) (by norm_num)
theorem B1367405 : Blo 908576 1367405 := bbase (se 3 (by rfl) ⟨256388, by rfl⟩ : syracuseStep 1367405 = 512777) (by norm_num)
theorem B1367429 : Blo 908576 1367429 := bbase (se 4 (by rfl) ⟨128196, by rfl⟩ : syracuseStep 1367429 = 256393) (by norm_num)
theorem B1367453 : Blo 908576 1367453 := bbase (se 3 (by rfl) ⟨256397, by rfl⟩ : syracuseStep 1367453 = 512795) (by norm_num)
theorem B1367477 : Blo 908576 1367477 := bbase (se 5 (by rfl) ⟨64100, by rfl⟩ : syracuseStep 1367477 = 128201) (by norm_num)
theorem B1367501 : Blo 908576 1367501 := bbase (se 3 (by rfl) ⟨256406, by rfl⟩ : syracuseStep 1367501 = 512813) (by norm_num)
theorem B974305 : Blo 908576 974305 := bbase (se 2 (by rfl) ⟨365364, by rfl⟩ : syracuseStep 974305 = 730729) (by norm_num)
theorem B1367525 : Blo 908576 1367525 := bbase (se 4 (by rfl) ⟨128205, by rfl⟩ : syracuseStep 1367525 = 256411) (by norm_num)
theorem B1367549 : Blo 908576 1367549 := bbase (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) (by norm_num)
theorem B1367573 : Blo 908576 1367573 := bbase (se 6 (by rfl) ⟨32052, by rfl⟩ : syracuseStep 1367573 = 64105) (by norm_num)
theorem B974377 : Blo 908576 974377 := bbase (se 2 (by rfl) ⟨365391, by rfl⟩ : syracuseStep 974377 = 730783) (by norm_num)
theorem B1367597 : Blo 908576 1367597 := bbase (se 3 (by rfl) ⟨256424, by rfl⟩ : syracuseStep 1367597 = 512849) (by norm_num)
theorem B2186813 : Blo 908576 2186813 := bbase (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) (by norm_num)
theorem B4611653 : Blo 908576 4611653 := bbase (se 4 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 4611653 = 864685) (by norm_num)
theorem B1367621 : Blo 908576 1367621 := bbase (se 4 (by rfl) ⟨128214, by rfl⟩ : syracuseStep 1367621 = 256429) (by norm_num)
theorem B3071573 : Blo 908576 3071573 := bbase (se 8 (by rfl) ⟨17997, by rfl⟩ : syracuseStep 3071573 = 35995) (by norm_num)
theorem B1367645 : Blo 908576 1367645 := bbase (se 3 (by rfl) ⟨256433, by rfl⟩ : syracuseStep 1367645 = 512867) (by norm_num)
theorem B1367669 : Blo 908576 1367669 := bbase (se 5 (by rfl) ⟨64109, by rfl⟩ : syracuseStep 1367669 = 128219) (by norm_num)
theorem B1728125 : Blo 908576 1728125 := bbase (se 3 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 1728125 = 648047) (by norm_num)
theorem B1367693 : Blo 908576 1367693 := bbase (se 3 (by rfl) ⟨256442, by rfl⟩ : syracuseStep 1367693 = 512885) (by norm_num)
theorem B1367717 : Blo 908576 1367717 := bbase (se 4 (by rfl) ⟨128223, by rfl⟩ : syracuseStep 1367717 = 256447) (by norm_num)
theorem B1040045 : Blo 908576 1040045 := bbase (se 3 (by rfl) ⟨195008, by rfl⟩ : syracuseStep 1040045 = 390017) (by norm_num)
theorem B1367741 : Blo 908576 1367741 := bbase (se 3 (by rfl) ⟨256451, by rfl⟩ : syracuseStep 1367741 = 512903) (by norm_num)
theorem B1367765 : Blo 908576 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B1367789 : Blo 908576 1367789 := bbase (se 3 (by rfl) ⟨256460, by rfl⟩ : syracuseStep 1367789 = 512921) (by norm_num)
theorem B1367813 : Blo 908576 1367813 := bbase (se 4 (by rfl) ⟨128232, by rfl⟩ : syracuseStep 1367813 = 256465) (by norm_num)
theorem B1367837 : Blo 908576 1367837 := bbase (se 3 (by rfl) ⟨256469, by rfl⟩ : syracuseStep 1367837 = 512939) (by norm_num)
theorem B1367861 : Blo 908576 1367861 := bbase (se 5 (by rfl) ⟨64118, by rfl⟩ : syracuseStep 1367861 = 128237) (by norm_num)
theorem B1662781 : Blo 908576 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B1367885 : Blo 908576 1367885 := bbase (se 3 (by rfl) ⟨256478, by rfl⟩ : syracuseStep 1367885 = 512957) (by norm_num)
theorem B1367909 : Blo 908576 1367909 := bbase (se 4 (by rfl) ⟨128241, by rfl⟩ : syracuseStep 1367909 = 256483) (by norm_num)
theorem B1367933 : Blo 908576 1367933 := bbase (se 3 (by rfl) ⟨256487, by rfl⟩ : syracuseStep 1367933 = 512975) (by norm_num)
theorem B1367957 : Blo 908576 1367957 := bbase (se 6 (by rfl) ⟨32061, by rfl⟩ : syracuseStep 1367957 = 64123) (by norm_num)
theorem B1367981 : Blo 908576 1367981 := bbase (se 3 (by rfl) ⟨256496, by rfl⟩ : syracuseStep 1367981 = 512993) (by norm_num)
theorem B3694517 : Blo 908576 3694517 := bbase (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) (by norm_num)
theorem B1368005 : Blo 908576 1368005 := bbase (se 4 (by rfl) ⟨128250, by rfl⟩ : syracuseStep 1368005 = 256501) (by norm_num)
theorem B1368029 : Blo 908576 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B1368053 : Blo 908576 1368053 := bbase (se 5 (by rfl) ⟨64127, by rfl⟩ : syracuseStep 1368053 = 128255) (by norm_num)
theorem B3072005 : Blo 908576 3072005 := bbase (se 4 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 3072005 = 576001) (by norm_num)
theorem B1368077 : Blo 908576 1368077 := bbase (se 3 (by rfl) ⟨256514, by rfl⟩ : syracuseStep 1368077 = 513029) (by norm_num)
theorem B1368101 : Blo 908576 1368101 := bbase (se 4 (by rfl) ⟨128259, by rfl⟩ : syracuseStep 1368101 = 256519) (by norm_num)
theorem B1368125 : Blo 908576 1368125 := bbase (se 3 (by rfl) ⟨256523, by rfl⟩ : syracuseStep 1368125 = 513047) (by norm_num)
theorem B1368149 : Blo 908576 1368149 := bbase (se 8 (by rfl) ⟨8016, by rfl⟩ : syracuseStep 1368149 = 16033) (by norm_num)
theorem B1368173 : Blo 908576 1368173 := bbase (se 3 (by rfl) ⟨256532, by rfl⟩ : syracuseStep 1368173 = 513065) (by norm_num)
theorem B1368197 : Blo 908576 1368197 := bbase (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) (by norm_num)
theorem B1368221 : Blo 908576 1368221 := bbase (se 3 (by rfl) ⟨256541, by rfl⟩ : syracuseStep 1368221 = 513083) (by norm_num)
theorem B1368245 : Blo 908576 1368245 := bbase (se 5 (by rfl) ⟨64136, by rfl⟩ : syracuseStep 1368245 = 128273) (by norm_num)
theorem B1368269 : Blo 908576 1368269 := bbase (se 3 (by rfl) ⟨256550, by rfl⟩ : syracuseStep 1368269 = 513101) (by norm_num)
theorem B1368293 : Blo 908576 1368293 := bbase (se 4 (by rfl) ⟨128277, by rfl⟩ : syracuseStep 1368293 = 256555) (by norm_num)
theorem B1138933 : Blo 908576 1138933 := bbase (se 5 (by rfl) ⟨53387, by rfl⟩ : syracuseStep 1138933 = 106775) (by norm_num)
theorem B1040629 : Blo 908576 1040629 := bbase (se 5 (by rfl) ⟨48779, by rfl⟩ : syracuseStep 1040629 = 97559) (by norm_num)
theorem B1368317 : Blo 908576 1368317 := bbase (se 3 (by rfl) ⟨256559, by rfl⟩ : syracuseStep 1368317 = 513119) (by norm_num)
theorem B1368341 : Blo 908576 1368341 := bbase (se 6 (by rfl) ⟨32070, by rfl⟩ : syracuseStep 1368341 = 64141) (by norm_num)
theorem B3891493 : Blo 908576 3891493 := bbase (se 4 (by rfl) ⟨364827, by rfl⟩ : syracuseStep 3891493 = 729655) (by norm_num)
theorem B1368365 : Blo 908576 1368365 := bbase (se 3 (by rfl) ⟨256568, by rfl⟩ : syracuseStep 1368365 = 513137) (by norm_num)
theorem B2187581 : Blo 908576 2187581 := bbase (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) (by norm_num)
theorem B1663301 : Blo 908576 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B1368389 : Blo 908576 1368389 := bbase (se 4 (by rfl) ⟨128286, by rfl⟩ : syracuseStep 1368389 = 256573) (by norm_num)
theorem B1368413 : Blo 908576 1368413 := bbase (se 3 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 1368413 = 513155) (by norm_num)
theorem B1728877 : Blo 908576 1728877 := bbase (se 3 (by rfl) ⟨324164, by rfl⟩ : syracuseStep 1728877 = 648329) (by norm_num)
theorem B1368437 : Blo 908576 1368437 := bbase (se 5 (by rfl) ⟨64145, by rfl⟩ : syracuseStep 1368437 = 128291) (by norm_num)
theorem B1368461 : Blo 908576 1368461 := bbase (se 3 (by rfl) ⟨256586, by rfl⟩ : syracuseStep 1368461 = 513173) (by norm_num)
theorem B1368485 : Blo 908576 1368485 := bbase (se 4 (by rfl) ⟨128295, by rfl⟩ : syracuseStep 1368485 = 256591) (by norm_num)
theorem B3072437 : Blo 908576 3072437 := bbase (se 5 (by rfl) ⟨144020, by rfl⟩ : syracuseStep 3072437 = 288041) (by norm_num)
theorem B1368509 : Blo 908576 1368509 := bbase (se 3 (by rfl) ⟨256595, by rfl⟩ : syracuseStep 1368509 = 513191) (by norm_num)
theorem B1368533 : Blo 908576 1368533 := bbase (se 7 (by rfl) ⟨16037, by rfl⟩ : syracuseStep 1368533 = 32075) (by norm_num)
theorem B1368557 : Blo 908576 1368557 := bbase (se 3 (by rfl) ⟨256604, by rfl⟩ : syracuseStep 1368557 = 513209) (by norm_num)
theorem B1729021 : Blo 908576 1729021 := bbase (se 3 (by rfl) ⟨324191, by rfl⟩ : syracuseStep 1729021 = 648383) (by norm_num)
theorem B1368581 : Blo 908576 1368581 := bbase (se 4 (by rfl) ⟨128304, by rfl⟩ : syracuseStep 1368581 = 256609) (by norm_num)
theorem B1368605 : Blo 908576 1368605 := bbase (se 3 (by rfl) ⟨256613, by rfl⟩ : syracuseStep 1368605 = 513227) (by norm_num)
theorem B1368629 : Blo 908576 1368629 := bbase (se 5 (by rfl) ⟨64154, by rfl⟩ : syracuseStep 1368629 = 128309) (by norm_num)
theorem B1368653 : Blo 908576 1368653 := bbase (se 3 (by rfl) ⟨256622, by rfl⟩ : syracuseStep 1368653 = 513245) (by norm_num)
theorem B1368677 : Blo 908576 1368677 := bbase (se 4 (by rfl) ⟨128313, by rfl⟩ : syracuseStep 1368677 = 256627) (by norm_num)
theorem B1368701 : Blo 908576 1368701 := bbase (se 3 (by rfl) ⟨256631, by rfl⟩ : syracuseStep 1368701 = 513263) (by norm_num)
theorem B1368725 : Blo 908576 1368725 := bbase (se 6 (by rfl) ⟨32079, by rfl⟩ : syracuseStep 1368725 = 64159) (by norm_num)
theorem B1729181 : Blo 908576 1729181 := bbase (se 3 (by rfl) ⟨324221, by rfl⟩ : syracuseStep 1729181 = 648443) (by norm_num)
theorem B1401517 : Blo 908576 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B1368749 : Blo 908576 1368749 := bbase (se 3 (by rfl) ⟨256640, by rfl⟩ : syracuseStep 1368749 = 513281) (by norm_num)
theorem B1368773 : Blo 908576 1368773 := bbase (se 4 (by rfl) ⟨128322, by rfl⟩ : syracuseStep 1368773 = 256645) (by norm_num)
theorem B1368797 : Blo 908576 1368797 := bbase (se 3 (by rfl) ⟨256649, by rfl⟩ : syracuseStep 1368797 = 513299) (by norm_num)
theorem B1368821 : Blo 908576 1368821 := bbase (se 5 (by rfl) ⟨64163, by rfl⟩ : syracuseStep 1368821 = 128327) (by norm_num)
theorem B1368845 : Blo 908576 1368845 := bbase (se 3 (by rfl) ⟨256658, by rfl⟩ : syracuseStep 1368845 = 513317) (by norm_num)
theorem B3498773 : Blo 908576 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B1729325 : Blo 908576 1729325 := bbase (se 3 (by rfl) ⟨324248, by rfl⟩ : syracuseStep 1729325 = 648497) (by norm_num)
theorem B4612949 : Blo 908576 4612949 := bbase (se 9 (by rfl) ⟨13514, by rfl⟩ : syracuseStep 4612949 = 27029) (by norm_num)
theorem B3072869 : Blo 908576 3072869 := bbase (se 4 (by rfl) ⟨288081, by rfl⟩ : syracuseStep 3072869 = 576163) (by norm_num)
theorem B2221085 : Blo 908576 2221085 := bbase (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) (by norm_num)
theorem B1729613 : Blo 908576 1729613 := bbase (se 3 (by rfl) ⟨324302, by rfl⟩ : syracuseStep 1729613 = 648605) (by norm_num)
theorem B8316053 : Blo 908576 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B1729765 : Blo 908576 1729765 := bbase (se 4 (by rfl) ⟨162165, by rfl⟩ : syracuseStep 1729765 = 324331) (by norm_num)
theorem B3073301 : Blo 908576 3073301 := bbase (se 6 (by rfl) ⟨72030, by rfl⟩ : syracuseStep 3073301 = 144061) (by norm_num)
theorem B1402181 : Blo 908576 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1533269 : Blo 908576 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B1533397 : Blo 908576 1533397 := bbase (se 7 (by rfl) ⟨17969, by rfl⟩ : syracuseStep 1533397 = 35939) (by norm_num)
theorem B1730069 : Blo 908576 1730069 := bbase (se 6 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 1730069 = 81097) (by norm_num)
theorem B1533485 : Blo 908576 1533485 := bbase (se 3 (by rfl) ⟨287528, by rfl⟩ : syracuseStep 1533485 = 575057) (by norm_num)
theorem B1533613 : Blo 908576 1533613 := bbase (se 3 (by rfl) ⟨287552, by rfl⟩ : syracuseStep 1533613 = 575105) (by norm_num)
theorem B3073733 : Blo 908576 3073733 := bbase (se 4 (by rfl) ⟨288162, by rfl⟩ : syracuseStep 3073733 = 576325) (by norm_num)
theorem B3892981 : Blo 908576 3892981 := bbase (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) (by norm_num)
theorem B1533701 : Blo 908576 1533701 := bbase (se 4 (by rfl) ⟨143784, by rfl⟩ : syracuseStep 1533701 = 287569) (by norm_num)
theorem B3892997 : Blo 908576 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B1533829 : Blo 908576 1533829 := bbase (se 4 (by rfl) ⟨143796, by rfl⟩ : syracuseStep 1533829 = 287593) (by norm_num)
theorem B1533917 : Blo 908576 1533917 := bbase (se 3 (by rfl) ⟨287609, by rfl⟩ : syracuseStep 1533917 = 575219) (by norm_num)
theorem B2189389 : Blo 908576 2189389 := bbase (se 3 (by rfl) ⟨410510, by rfl⟩ : syracuseStep 2189389 = 821021) (by norm_num)
theorem B1534045 : Blo 908576 1534045 := bbase (se 3 (by rfl) ⟨287633, by rfl⟩ : syracuseStep 1534045 = 575267) (by norm_num)
theorem B4614245 : Blo 908576 4614245 := bbase (se 4 (by rfl) ⟨432585, by rfl⟩ : syracuseStep 4614245 = 865171) (by norm_num)
theorem B3074165 : Blo 908576 3074165 := bbase (se 5 (by rfl) ⟨144101, by rfl⟩ : syracuseStep 3074165 = 288203) (by norm_num)
theorem B1534133 : Blo 908576 1534133 := bbase (se 5 (by rfl) ⟨71912, by rfl⟩ : syracuseStep 1534133 = 143825) (by norm_num)
theorem B1730821 : Blo 908576 1730821 := bbase (se 4 (by rfl) ⟨162264, by rfl⟩ : syracuseStep 1730821 = 324529) (by norm_num)
theorem B1665293 : Blo 908576 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B1534261 : Blo 908576 1534261 := bbase (se 5 (by rfl) ⟨71918, by rfl⟩ : syracuseStep 1534261 = 143837) (by norm_num)
theorem B4385141 : Blo 908576 4385141 := bbase (se 5 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 4385141 = 411107) (by norm_num)
theorem B1534349 : Blo 908576 1534349 := bbase (se 3 (by rfl) ⟨287690, by rfl⟩ : syracuseStep 1534349 = 575381) (by norm_num)
theorem B1730965 : Blo 908576 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B1534477 : Blo 908576 1534477 := bbase (se 3 (by rfl) ⟨287714, by rfl⟩ : syracuseStep 1534477 = 575429) (by norm_num)
theorem B3074597 : Blo 908576 3074597 := bbase (se 4 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 3074597 = 576487) (by norm_num)
theorem B1731125 : Blo 908576 1731125 := bbase (se 5 (by rfl) ⟨81146, by rfl⟩ : syracuseStep 1731125 = 162293) (by norm_num)
theorem B2189909 : Blo 908576 2189909 := bbase (se 8 (by rfl) ⟨12831, by rfl⟩ : syracuseStep 2189909 = 25663) (by norm_num)
theorem B1534565 : Blo 908576 1534565 := bbase (se 4 (by rfl) ⟨143865, by rfl⟩ : syracuseStep 1534565 = 287731) (by norm_num)
theorem B1731269 : Blo 908576 1731269 := bbase (se 4 (by rfl) ⟨162306, by rfl⟩ : syracuseStep 1731269 = 324613) (by norm_num)
theorem B1534693 : Blo 908576 1534693 := bbase (se 4 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 1534693 = 287755) (by norm_num)
theorem B1534781 : Blo 908576 1534781 := bbase (se 3 (by rfl) ⟨287771, by rfl⟩ : syracuseStep 1534781 = 575543) (by norm_num)
theorem B1534909 : Blo 908576 1534909 := bbase (se 3 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 1534909 = 575591) (by norm_num)
theorem B3075029 : Blo 908576 3075029 := bbase (se 7 (by rfl) ⟨36035, by rfl⟩ : syracuseStep 3075029 = 72071) (by norm_num)
theorem B2190293 : Blo 908576 2190293 := bbase (se 7 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 2190293 = 51335) (by norm_num)
theorem B1731557 : Blo 908576 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B2190341 : Blo 908576 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B2190349 : Blo 908576 2190349 := bbase (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) (by norm_num)
theorem B1534997 : Blo 908576 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B8744021 : Blo 908576 8744021 := bbase (se 8 (by rfl) ⟨51234, by rfl⟩ : syracuseStep 8744021 = 102469) (by norm_num)
theorem B1731709 : Blo 908576 1731709 := bbase (se 3 (by rfl) ⟨324695, by rfl⟩ : syracuseStep 1731709 = 649391) (by norm_num)
theorem B1535125 : Blo 908576 1535125 := bbase (se 6 (by rfl) ⟨35979, by rfl⟩ : syracuseStep 1535125 = 71959) (by norm_num)
theorem B1535213 : Blo 908576 1535213 := bbase (se 3 (by rfl) ⟨287852, by rfl⟩ : syracuseStep 1535213 = 575705) (by norm_num)
theorem B1535341 : Blo 908576 1535341 := bbase (se 3 (by rfl) ⟨287876, by rfl⟩ : syracuseStep 1535341 = 575753) (by norm_num)
theorem B4615541 : Blo 908576 4615541 := bbase (se 5 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 4615541 = 432707) (by norm_num)
theorem B1109377 : Blo 908576 1109377 := bbase (se 2 (by rfl) ⟨416016, by rfl⟩ : syracuseStep 1109377 = 832033) (by norm_num)
theorem B3075461 : Blo 908576 3075461 := bbase (se 4 (by rfl) ⟨288324, by rfl⟩ : syracuseStep 3075461 = 576649) (by norm_num)
theorem B1732013 : Blo 908576 1732013 := bbase (se 3 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 1732013 = 649505) (by norm_num)
theorem B1535429 : Blo 908576 1535429 := bbase (se 4 (by rfl) ⟨143946, by rfl⟩ : syracuseStep 1535429 = 287893) (by norm_num)
theorem B6909461 : Blo 908576 6909461 := bbase (se 6 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 6909461 = 323881) (by norm_num)
theorem B1535557 : Blo 908576 1535557 := bbase (se 4 (by rfl) ⟨143958, by rfl⟩ : syracuseStep 1535557 = 287917) (by norm_num)
theorem B1535645 : Blo 908576 1535645 := bbase (se 3 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 1535645 = 575867) (by norm_num)
theorem B1666813 : Blo 908576 1666813 := bbase (se 3 (by rfl) ⟨312527, by rfl⟩ : syracuseStep 1666813 = 625055) (by norm_num)
theorem B1535773 : Blo 908576 1535773 := bbase (se 3 (by rfl) ⟨287957, by rfl⟩ : syracuseStep 1535773 = 575915) (by norm_num)
theorem B3075893 : Blo 908576 3075893 := bbase (se 5 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 3075893 = 288365) (by norm_num)
theorem B1535861 : Blo 908576 1535861 := bbase (se 5 (by rfl) ⟨71993, by rfl⟩ : syracuseStep 1535861 = 143987) (by norm_num)
theorem B2912213 : Blo 908576 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B3895253 : Blo 908576 3895253 := bbase (se 7 (by rfl) ⟨45647, by rfl⟩ : syracuseStep 3895253 = 91295) (by norm_num)
theorem B1535989 : Blo 908576 1535989 := bbase (se 5 (by rfl) ⟨71999, by rfl⟩ : syracuseStep 1535989 = 143999) (by norm_num)
theorem B2191349 : Blo 908576 2191349 := bbase (se 5 (by rfl) ⟨102719, by rfl⟩ : syracuseStep 2191349 = 205439) (by norm_num)
theorem B1536077 : Blo 908576 1536077 := bbase (se 3 (by rfl) ⟨288014, by rfl⟩ : syracuseStep 1536077 = 576029) (by norm_num)
theorem B2191541 : Blo 908576 2191541 := bbase (se 5 (by rfl) ⟨102728, by rfl⟩ : syracuseStep 2191541 = 205457) (by norm_num)
theorem B1536205 : Blo 908576 1536205 := bbase (se 3 (by rfl) ⟨288038, by rfl⟩ : syracuseStep 1536205 = 576077) (by norm_num)
theorem B3076325 : Blo 908576 3076325 := bbase (se 4 (by rfl) ⟨288405, by rfl⟩ : syracuseStep 3076325 = 576811) (by norm_num)
theorem B1536293 : Blo 908576 1536293 := bbase (se 4 (by rfl) ⟨144027, by rfl⟩ : syracuseStep 1536293 = 288055) (by norm_num)
theorem B1536421 : Blo 908576 1536421 := bbase (se 4 (by rfl) ⟨144039, by rfl⟩ : syracuseStep 1536421 = 288079) (by norm_num)
theorem B1536509 : Blo 908576 1536509 := bbase (se 3 (by rfl) ⟨288095, by rfl⟩ : syracuseStep 1536509 = 576191) (by norm_num)
theorem B1536637 : Blo 908576 1536637 := bbase (se 3 (by rfl) ⟨288119, by rfl⟩ : syracuseStep 1536637 = 576239) (by norm_num)
theorem B4616837 : Blo 908576 4616837 := bbase (se 4 (by rfl) ⟨432828, by rfl⟩ : syracuseStep 4616837 = 865657) (by norm_num)
theorem B3076757 : Blo 908576 3076757 := bbase (se 6 (by rfl) ⟨72111, by rfl⟩ : syracuseStep 3076757 = 144223) (by norm_num)
theorem B1536725 : Blo 908576 1536725 := bbase (se 7 (by rfl) ⟨18008, by rfl⟩ : syracuseStep 1536725 = 36017) (by norm_num)
theorem B1110781 : Blo 908576 1110781 := bbase (se 3 (by rfl) ⟨208271, by rfl⟩ : syracuseStep 1110781 = 416543) (by norm_num)
theorem B1536853 : Blo 908576 1536853 := bbase (se 9 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 1536853 = 9005) (by norm_num)
theorem B16610197 : Blo 908576 16610197 := bbase (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) (by norm_num)
theorem B1536941 : Blo 908576 1536941 := bbase (se 3 (by rfl) ⟨288176, by rfl⟩ : syracuseStep 1536941 = 576353) (by norm_num)
theorem B2913317 : Blo 908576 2913317 := bbase (se 4 (by rfl) ⟨273123, by rfl⟩ : syracuseStep 2913317 = 546247) (by norm_num)
theorem B1537069 : Blo 908576 1537069 := bbase (se 3 (by rfl) ⟨288200, by rfl⟩ : syracuseStep 1537069 = 576401) (by norm_num)
theorem B3077189 : Blo 908576 3077189 := bbase (se 4 (by rfl) ⟨288486, by rfl⟩ : syracuseStep 3077189 = 576973) (by norm_num)
theorem B5534837 : Blo 908576 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B1537157 : Blo 908576 1537157 := bbase (se 4 (by rfl) ⟨144108, by rfl⟩ : syracuseStep 1537157 = 288217) (by norm_num)
theorem B1537285 : Blo 908576 1537285 := bbase (se 4 (by rfl) ⟨144120, by rfl⟩ : syracuseStep 1537285 = 288241) (by norm_num)
theorem B1537373 : Blo 908576 1537373 := bbase (se 3 (by rfl) ⟨288257, by rfl⟩ : syracuseStep 1537373 = 576515) (by norm_num)
theorem B1537501 : Blo 908576 1537501 := bbase (se 3 (by rfl) ⟨288281, by rfl⟩ : syracuseStep 1537501 = 576563) (by norm_num)
theorem B3077621 : Blo 908576 3077621 := bbase (se 5 (by rfl) ⟨144263, by rfl⟩ : syracuseStep 3077621 = 288527) (by norm_num)
theorem B1537589 : Blo 908576 1537589 := bbase (se 5 (by rfl) ⟨72074, by rfl⟩ : syracuseStep 1537589 = 144149) (by norm_num)
theorem B1537717 : Blo 908576 1537717 := bbase (se 5 (by rfl) ⟨72080, by rfl⟩ : syracuseStep 1537717 = 144161) (by norm_num)
theorem B1603309 : Blo 908576 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B1537805 : Blo 908576 1537805 := bbase (se 3 (by rfl) ⟨288338, by rfl⟩ : syracuseStep 1537805 = 576677) (by norm_num)
theorem B1537933 : Blo 908576 1537933 := bbase (se 3 (by rfl) ⟨288362, by rfl⟩ : syracuseStep 1537933 = 576725) (by norm_num)
theorem B4618133 : Blo 908576 4618133 := bbase (se 6 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 4618133 = 216475) (by norm_num)
theorem B3078053 : Blo 908576 3078053 := bbase (se 4 (by rfl) ⟨288567, by rfl⟩ : syracuseStep 3078053 = 577135) (by norm_num)
theorem B948137 : Blo 908576 948137 := bbase (se 2 (by rfl) ⟨355551, by rfl⟩ : syracuseStep 948137 = 711103) (by norm_num)
theorem B1538021 : Blo 908576 1538021 := bbase (se 4 (by rfl) ⟨144189, by rfl⟩ : syracuseStep 1538021 = 288379) (by norm_num)
theorem B4913237 : Blo 908576 4913237 := bbase (se 8 (by rfl) ⟨28788, by rfl⟩ : syracuseStep 4913237 = 57577) (by norm_num)
theorem B1538149 : Blo 908576 1538149 := bbase (se 4 (by rfl) ⟨144201, by rfl⟩ : syracuseStep 1538149 = 288403) (by norm_num)
theorem B1538237 : Blo 908576 1538237 := bbase (se 3 (by rfl) ⟨288419, by rfl⟩ : syracuseStep 1538237 = 576839) (by norm_num)
theorem B3275029 : Blo 908576 3275029 := bbase (se 6 (by rfl) ⟨76758, by rfl⟩ : syracuseStep 3275029 = 153517) (by norm_num)
theorem B1538365 : Blo 908576 1538365 := bbase (se 3 (by rfl) ⟨288443, by rfl⟩ : syracuseStep 1538365 = 576887) (by norm_num)
theorem B3078485 : Blo 908576 3078485 := bbase (se 10 (by rfl) ⟨4509, by rfl⟩ : syracuseStep 3078485 = 9019) (by norm_num)
theorem B1538453 : Blo 908576 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B1538581 : Blo 908576 1538581 := bbase (se 6 (by rfl) ⟨36060, by rfl⟩ : syracuseStep 1538581 = 72121) (by norm_num)
theorem B1538669 : Blo 908576 1538669 := bbase (se 3 (by rfl) ⟨288500, by rfl⟩ : syracuseStep 1538669 = 577001) (by norm_num)
theorem B948893 : Blo 908576 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B1538797 : Blo 908576 1538797 := bbase (se 3 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 1538797 = 577049) (by norm_num)
theorem B4913909 : Blo 908576 4913909 := bbase (se 5 (by rfl) ⟨230339, by rfl⟩ : syracuseStep 4913909 = 460679) (by norm_num)
theorem B3078917 : Blo 908576 3078917 := bbase (se 4 (by rfl) ⟨288648, by rfl⟩ : syracuseStep 3078917 = 577297) (by norm_num)
theorem B1538885 : Blo 908576 1538885 := bbase (se 4 (by rfl) ⟨144270, by rfl⟩ : syracuseStep 1538885 = 288541) (by norm_num)
theorem B2915237 : Blo 908576 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B4914101 : Blo 908576 4914101 := bbase (se 5 (by rfl) ⟨230348, by rfl⟩ : syracuseStep 4914101 = 460697) (by norm_num)
theorem B1539013 : Blo 908576 1539013 := bbase (se 4 (by rfl) ⟨144282, by rfl⟩ : syracuseStep 1539013 = 288565) (by norm_num)
theorem B1539101 : Blo 908576 1539101 := bbase (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) (by norm_num)
theorem B1637509 : Blo 908576 1637509 := bbase (se 4 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 1637509 = 307033) (by norm_num)
theorem B1539229 : Blo 908576 1539229 := bbase (se 3 (by rfl) ⟨288605, by rfl⟩ : syracuseStep 1539229 = 577211) (by norm_num)
theorem B4619429 : Blo 908576 4619429 := bbase (se 4 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 4619429 = 866143) (by norm_num)
theorem B3079349 : Blo 908576 3079349 := bbase (se 5 (by rfl) ⟨144344, by rfl⟩ : syracuseStep 3079349 = 288689) (by norm_num)
theorem B1539317 : Blo 908576 1539317 := bbase (se 5 (by rfl) ⟨72155, by rfl⟩ : syracuseStep 1539317 = 144311) (by norm_num)
theorem B1539445 : Blo 908576 1539445 := bbase (se 5 (by rfl) ⟨72161, by rfl⟩ : syracuseStep 1539445 = 144323) (by norm_num)
theorem B1539533 : Blo 908576 1539533 := bbase (se 3 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 1539533 = 577325) (by norm_num)
theorem B2588213 : Blo 908576 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B1539661 : Blo 908576 1539661 := bbase (se 3 (by rfl) ⟨288686, by rfl⟩ : syracuseStep 1539661 = 577373) (by norm_num)
theorem B3079781 : Blo 908576 3079781 := bbase (se 4 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 3079781 = 577459) (by norm_num)
theorem B1539749 : Blo 908576 1539749 := bbase (se 4 (by rfl) ⟨144351, by rfl⟩ : syracuseStep 1539749 = 288703) (by norm_num)
theorem B1539877 : Blo 908576 1539877 := bbase (se 4 (by rfl) ⟨144363, by rfl⟩ : syracuseStep 1539877 = 288727) (by norm_num)
theorem B1539965 : Blo 908576 1539965 := bbase (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) (by norm_num)
theorem B4915313 : Blo 908576 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B1900817 : Blo 908576 1900817 := bstep (se 2 (by rfl) ⟨712806, by rfl⟩ : syracuseStep 1900817 = 1425613) B1425613
theorem B1639043 : Blo 908576 1639043 := bstep (se 1 (by rfl) ⟨1229282, by rfl⟩ : syracuseStep 1639043 = 2458565) B2458565
theorem B5833549 : Blo 908576 5833549 := bstep (se 3 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 5833549 = 2187581) B2187581
theorem B1868689 : Blo 908576 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B11076533 : Blo 908576 11076533 := bstep (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) B1038425
theorem B3278029 : Blo 908576 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B2590001 : Blo 908576 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B16647565 : Blo 908576 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B6555107 : Blo 908576 6555107 := bstep (se 1 (by rfl) ⟨4916330, by rfl⟩ : syracuseStep 6555107 = 9832661) B9832661
theorem B8881649 : Blo 908576 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B2918339 : Blo 908576 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B11667509 : Blo 908576 11667509 := bstep (se 5 (by rfl) ⟨546914, by rfl⟩ : syracuseStep 11667509 = 1093829) B1093829
theorem B2590957 : Blo 908576 2590957 := bstep (se 3 (by rfl) ⟨485804, by rfl⟩ : syracuseStep 2590957 = 971609) B971609
theorem B3115427 : Blo 908576 3115427 := bstep (se 1 (by rfl) ⟨2336570, by rfl⟩ : syracuseStep 3115427 = 4673141) B4673141
theorem B2591185 : Blo 908576 2591185 := bstep (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) B1943389
theorem B5179909 : Blo 908576 5179909 := bstep (se 4 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 5179909 = 971233) B971233
theorem B5540429 : Blo 908576 5540429 := bstep (se 3 (by rfl) ⟨1038830, by rfl⟩ : syracuseStep 5540429 = 2077661) B2077661
theorem B2591345 : Blo 908576 2591345 := bstep (se 2 (by rfl) ⟨971754, by rfl⟩ : syracuseStep 2591345 = 1943509) B1943509
theorem B2591459 : Blo 908576 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B3279629 : Blo 908576 3279629 := bstep (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) B1229861
theorem B2919185 : Blo 908576 2919185 := bstep (se 2 (by rfl) ⟨1094694, by rfl⟩ : syracuseStep 2919185 = 2189389) B2189389
theorem B2919235 : Blo 908576 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B2460881 : Blo 908576 2460881 := bstep (se 2 (by rfl) ⟨922830, by rfl⟩ : syracuseStep 2460881 = 1845661) B1845661
theorem B1150195 : Blo 908576 1150195 := bstep (se 1 (by rfl) ⟨862646, by rfl⟩ : syracuseStep 1150195 = 1725293) B1725293
theorem B1150291 : Blo 908576 1150291 := bstep (se 1 (by rfl) ⟨862718, by rfl⟩ : syracuseStep 1150291 = 1725437) B1725437
theorem B1314193 : Blo 908576 1314193 := bstep (se 2 (by rfl) ⟨492822, by rfl⟩ : syracuseStep 1314193 = 985645) B985645
theorem B2592461 : Blo 908576 2592461 := bstep (se 3 (by rfl) ⟨486086, by rfl⟩ : syracuseStep 2592461 = 972173) B972173
theorem B1150787 : Blo 908576 1150787 := bstep (se 1 (by rfl) ⟨863090, by rfl⟩ : syracuseStep 1150787 = 1726181) B1726181
theorem B2461549 : Blo 908576 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B2592643 : Blo 908576 2592643 := bstep (se 1 (by rfl) ⟨1944482, by rfl⟩ : syracuseStep 2592643 = 3888965) B3888965
theorem B1314721 : Blo 908576 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B8753093 : Blo 908576 8753093 := bstep (se 4 (by rfl) ⟨820602, by rfl⟩ : syracuseStep 8753093 = 1641205) B1641205
theorem B1871843 : Blo 908576 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B2920465 : Blo 908576 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B2592803 : Blo 908576 2592803 := bstep (se 1 (by rfl) ⟨1944602, by rfl⟩ : syracuseStep 2592803 = 3889205) B3889205
theorem B1577249 : Blo 908576 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B5181893 : Blo 908576 5181893 := bstep (se 4 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 5181893 = 971605) B971605
theorem B2626033 : Blo 908576 2626033 := bstep (se 2 (by rfl) ⟨984762, by rfl⟩ : syracuseStep 2626033 = 1969525) B1969525
theorem B1479169 : Blo 908576 1479169 := bstep (se 2 (by rfl) ⟨554688, by rfl⟩ : syracuseStep 1479169 = 1109377) B1109377
theorem B1151491 : Blo 908576 1151491 := bstep (se 1 (by rfl) ⟨863618, by rfl⟩ : syracuseStep 1151491 = 1727237) B1727237
theorem B987715 : Blo 908576 987715 := bstep (se 1 (by rfl) ⟨740786, by rfl⟩ : syracuseStep 987715 = 1481573) B1481573
theorem B1151587 : Blo 908576 1151587 := bstep (se 1 (by rfl) ⟨863690, by rfl⟩ : syracuseStep 1151587 = 1727381) B1727381
theorem B9835121 : Blo 908576 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B922627 : Blo 908576 922627 := bstep (se 1 (by rfl) ⟨691970, by rfl⟩ : syracuseStep 922627 = 1383941) B1383941
theorem B6919181 : Blo 908576 6919181 := bstep (se 3 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 6919181 = 2594693) B2594693
theorem B2593873 : Blo 908576 2593873 := bstep (se 2 (by rfl) ⟨972702, by rfl⟩ : syracuseStep 2593873 = 1945405) B1945405
theorem B1315921 : Blo 908576 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B1152083 : Blo 908576 1152083 := bstep (se 1 (by rfl) ⟨864062, by rfl⟩ : syracuseStep 1152083 = 1728125) B1728125
theorem B2528365 : Blo 908576 2528365 := bstep (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) B948137
theorem B2921645 : Blo 908576 2921645 := bstep (se 3 (by rfl) ⟨547808, by rfl⟩ : syracuseStep 2921645 = 1095617) B1095617
theorem B2462957 : Blo 908576 2462957 := bstep (se 3 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 2462957 = 923609) B923609
theorem B2463011 : Blo 908576 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B1381873 : Blo 908576 1381873 := bstep (se 2 (by rfl) ⟨518202, by rfl⟩ : syracuseStep 1381873 = 1036405) B1036405
theorem B10360547 : Blo 908576 10360547 := bstep (se 1 (by rfl) ⟨7770410, by rfl⟩ : syracuseStep 10360547 = 15540821) B15540821
theorem B1152787 : Blo 908576 1152787 := bstep (se 1 (by rfl) ⟨864590, by rfl⟩ : syracuseStep 1152787 = 1729181) B1729181
theorem B1152883 : Blo 908576 1152883 := bstep (se 1 (by rfl) ⟨864662, by rfl⟩ : syracuseStep 1152883 = 1729325) B1729325
theorem B1480723 : Blo 908576 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B2299985 : Blo 908576 2299985 := bstep (se 2 (by rfl) ⟨862494, by rfl⟩ : syracuseStep 2299985 = 1724989) B1724989
theorem B5544035 : Blo 908576 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B2300035 : Blo 908576 2300035 := bstep (se 1 (by rfl) ⟨1725026, by rfl⟩ : syracuseStep 2300035 = 3450053) B3450053
theorem B1022179 : Blo 908576 1022179 := bstep (se 1 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 1022179 = 1533269) B1533269
theorem B2300177 : Blo 908576 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B2595149 : Blo 908576 2595149 := bstep (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) B973181
theorem B1481041 : Blo 908576 1481041 := bstep (se 2 (by rfl) ⟨555390, by rfl⟩ : syracuseStep 1481041 = 1110781) B1110781
theorem B1153379 : Blo 908576 1153379 := bstep (se 1 (by rfl) ⟨865034, by rfl⟩ : syracuseStep 1153379 = 1730069) B1730069
theorem B1022323 : Blo 908576 1022323 := bstep (se 1 (by rfl) ⟨766742, by rfl⟩ : syracuseStep 1022323 = 1533485) B1533485
theorem B6003085 : Blo 908576 6003085 := bstep (se 3 (by rfl) ⟨1125578, by rfl⟩ : syracuseStep 6003085 = 2251157) B2251157
theorem B1022467 : Blo 908576 1022467 := bstep (se 1 (by rfl) ⟨766850, by rfl⟩ : syracuseStep 1022467 = 1533701) B1533701
theorem B2595331 : Blo 908576 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B2595377 : Blo 908576 2595377 := bstep (se 2 (by rfl) ⟨973266, by rfl⟩ : syracuseStep 2595377 = 1946533) B1946533
theorem B1022611 : Blo 908576 1022611 := bstep (se 1 (by rfl) ⟨766958, by rfl⟩ : syracuseStep 1022611 = 1533917) B1533917
theorem B1022755 : Blo 908576 1022755 := bstep (se 1 (by rfl) ⟨767066, by rfl⟩ : syracuseStep 1022755 = 1534133) B1534133
theorem B2923427 : Blo 908576 2923427 := bstep (se 1 (by rfl) ⟨2192570, by rfl⟩ : syracuseStep 2923427 = 4385141) B4385141
theorem B1022899 : Blo 908576 1022899 := bstep (se 1 (by rfl) ⟨767174, by rfl⟩ : syracuseStep 1022899 = 1534349) B1534349
theorem B31562693 : Blo 908576 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B1154083 : Blo 908576 1154083 := bstep (se 1 (by rfl) ⟨865562, by rfl⟩ : syracuseStep 1154083 = 1731125) B1731125
theorem B1023043 : Blo 908576 1023043 := bstep (se 1 (by rfl) ⟨767282, by rfl⟩ : syracuseStep 1023043 = 1534565) B1534565
theorem B2530381 : Blo 908576 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B1154179 : Blo 908576 1154179 := bstep (se 1 (by rfl) ⟨865634, by rfl⟩ : syracuseStep 1154179 = 1731269) B1731269
theorem B1940689 : Blo 908576 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B1023187 : Blo 908576 1023187 := bstep (se 1 (by rfl) ⟨767390, by rfl⟩ : syracuseStep 1023187 = 1534781) B1534781
theorem B2301169 : Blo 908576 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B1023331 : Blo 908576 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B5840369 : Blo 908576 5840369 := bstep (se 2 (by rfl) ⟨2190138, by rfl⟩ : syracuseStep 5840369 = 4380277) B4380277
theorem B1023475 : Blo 908576 1023475 := bstep (se 1 (by rfl) ⟨767606, by rfl⟩ : syracuseStep 1023475 = 1535213) B1535213
theorem B2301443 : Blo 908576 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B3120653 : Blo 908576 3120653 := bstep (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) B1170245
theorem B1154675 : Blo 908576 1154675 := bstep (se 1 (by rfl) ⟨866006, by rfl⟩ : syracuseStep 1154675 = 1732013) B1732013
theorem B1023619 : Blo 908576 1023619 := bstep (se 1 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 1023619 = 1535429) B1535429
theorem B2137745 : Blo 908576 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B2301635 : Blo 908576 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B6233861 : Blo 908576 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B7773965 : Blo 908576 7773965 := bstep (se 3 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 7773965 = 2915237) B2915237
theorem B1023763 : Blo 908576 1023763 := bstep (se 1 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 1023763 = 1535645) B1535645
theorem B6922097 : Blo 908576 6922097 := bstep (se 2 (by rfl) ⟨2595786, by rfl⟩ : syracuseStep 6922097 = 5191573) B5191573
theorem B1023907 : Blo 908576 1023907 := bstep (se 1 (by rfl) ⟨767930, by rfl⟩ : syracuseStep 1023907 = 1535861) B1535861
theorem B2596835 : Blo 908576 2596835 := bstep (se 1 (by rfl) ⟨1947626, by rfl⟩ : syracuseStep 2596835 = 3895253) B3895253
theorem B3284977 : Blo 908576 3284977 := bstep (se 2 (by rfl) ⟨1231866, by rfl⟩ : syracuseStep 3284977 = 2463733) B2463733
theorem B5840909 : Blo 908576 5840909 := bstep (se 3 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 5840909 = 2190341) B2190341
theorem B1024051 : Blo 908576 1024051 := bstep (se 1 (by rfl) ⟨768038, by rfl⟩ : syracuseStep 1024051 = 1536077) B1536077
theorem B1024195 : Blo 908576 1024195 := bstep (se 1 (by rfl) ⟨768146, by rfl⟩ : syracuseStep 1024195 = 1536293) B1536293
theorem B5185741 : Blo 908576 5185741 := bstep (se 3 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 5185741 = 1944653) B1944653
theorem B1024339 : Blo 908576 1024339 := bstep (se 1 (by rfl) ⟨768254, by rfl⟩ : syracuseStep 1024339 = 1536509) B1536509
theorem B4366705 : Blo 908576 4366705 := bstep (se 2 (by rfl) ⟨1637514, by rfl⟩ : syracuseStep 4366705 = 3275029) B3275029
theorem B1384865 : Blo 908576 1384865 := bstep (se 2 (by rfl) ⟨519324, by rfl⟩ : syracuseStep 1384865 = 1038649) B1038649
theorem B1024483 : Blo 908576 1024483 := bstep (se 1 (by rfl) ⟨768362, by rfl⟩ : syracuseStep 1024483 = 1536725) B1536725
theorem B1843697 : Blo 908576 1843697 := bstep (se 2 (by rfl) ⟨691386, by rfl⟩ : syracuseStep 1843697 = 1382773) B1382773
theorem B1516099 : Blo 908576 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B2302577 : Blo 908576 2302577 := bstep (se 2 (by rfl) ⟨863466, by rfl⟩ : syracuseStep 2302577 = 1726933) B1726933
theorem B1024627 : Blo 908576 1024627 := bstep (se 1 (by rfl) ⟨768470, by rfl⟩ : syracuseStep 1024627 = 1536941) B1536941
theorem B2302627 : Blo 908576 2302627 := bstep (se 1 (by rfl) ⟨1726970, by rfl⟩ : syracuseStep 2302627 = 3453941) B3453941
theorem B1942193 : Blo 908576 1942193 := bstep (se 2 (by rfl) ⟨728322, by rfl⟩ : syracuseStep 1942193 = 1456645) B1456645
theorem B1942211 : Blo 908576 1942211 := bstep (se 1 (by rfl) ⟨1456658, by rfl⟩ : syracuseStep 1942211 = 2913317) B2913317
theorem B1024771 : Blo 908576 1024771 := bstep (se 1 (by rfl) ⟨768578, by rfl⟩ : syracuseStep 1024771 = 1537157) B1537157
theorem B2302769 : Blo 908576 2302769 := bstep (se 2 (by rfl) ⟨863538, by rfl⟩ : syracuseStep 2302769 = 1727077) B1727077
theorem B1385345 : Blo 908576 1385345 := bstep (se 2 (by rfl) ⟨519504, by rfl⟩ : syracuseStep 1385345 = 1039009) B1039009
theorem B1024915 : Blo 908576 1024915 := bstep (se 1 (by rfl) ⟨768686, by rfl⟩ : syracuseStep 1024915 = 1537373) B1537373
theorem B1025059 : Blo 908576 1025059 := bstep (se 1 (by rfl) ⟨768794, by rfl⟩ : syracuseStep 1025059 = 1537589) B1537589
theorem B5547149 : Blo 908576 5547149 := bstep (se 3 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 5547149 = 2080181) B2080181
theorem B2598065 : Blo 908576 2598065 := bstep (se 2 (by rfl) ⟨974274, by rfl⟩ : syracuseStep 2598065 = 1948549) B1948549
theorem B1025203 : Blo 908576 1025203 := bstep (se 1 (by rfl) ⟨768902, by rfl⟩ : syracuseStep 1025203 = 1537805) B1537805
theorem B1025347 : Blo 908576 1025347 := bstep (se 1 (by rfl) ⟨769010, by rfl⟩ : syracuseStep 1025347 = 1538021) B1538021
theorem B1025491 : Blo 908576 1025491 := bstep (se 1 (by rfl) ⟨769118, by rfl⟩ : syracuseStep 1025491 = 1538237) B1538237
theorem B1025635 : Blo 908576 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B3450509 : Blo 908576 3450509 := bstep (se 3 (by rfl) ⟨646970, by rfl⟩ : syracuseStep 3450509 = 1293941) B1293941
theorem B1025779 : Blo 908576 1025779 := bstep (se 1 (by rfl) ⟨769334, by rfl⟩ : syracuseStep 1025779 = 1538669) B1538669
theorem B2303761 : Blo 908576 2303761 := bstep (se 2 (by rfl) ⟨863910, by rfl⟩ : syracuseStep 2303761 = 1727821) B1727821
theorem B4925261 : Blo 908576 4925261 := bstep (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) B1846973
theorem B1025923 : Blo 908576 1025923 := bstep (se 1 (by rfl) ⟨769442, by rfl⟩ : syracuseStep 1025923 = 1538885) B1538885
theorem B1026067 : Blo 908576 1026067 := bstep (se 1 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 1026067 = 1539101) B1539101
theorem B2304035 : Blo 908576 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B5253169 : Blo 908576 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B5187725 : Blo 908576 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B1026211 : Blo 908576 1026211 := bstep (se 1 (by rfl) ⟨769658, by rfl⟩ : syracuseStep 1026211 = 1539317) B1539317
theorem B2304227 : Blo 908576 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B2337041 : Blo 908576 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B1026355 : Blo 908576 1026355 := bstep (se 1 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 1026355 = 1539533) B1539533
theorem B1026499 : Blo 908576 1026499 := bstep (se 1 (by rfl) ⟨769874, by rfl⟩ : syracuseStep 1026499 = 1539749) B1539749
theorem B21047779 : Blo 908576 21047779 := bstep (se 1 (by rfl) ⟨15785834, by rfl⟩ : syracuseStep 21047779 = 31571669) B31571669
theorem B1026643 : Blo 908576 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B2960003 : Blo 908576 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B1944209 : Blo 908576 1944209 := bstep (se 2 (by rfl) ⟨729078, by rfl⟩ : syracuseStep 1944209 = 1458157) B1458157
theorem B14756579 : Blo 908576 14756579 := bstep (se 1 (by rfl) ⟨11067434, by rfl⟩ : syracuseStep 14756579 = 22134869) B22134869
theorem B5253893 : Blo 908576 5253893 := bstep (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) B985105
theorem B1092403 : Blo 908576 1092403 := bstep (se 1 (by rfl) ⟨819302, by rfl⟩ : syracuseStep 1092403 = 1638605) B1638605
theorem B1846243 : Blo 908576 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B1387505 : Blo 908576 1387505 := bstep (se 2 (by rfl) ⟨520314, by rfl⟩ : syracuseStep 1387505 = 1040629) B1040629
theorem B1092595 : Blo 908576 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B5188657 : Blo 908576 5188657 := bstep (se 2 (by rfl) ⟨1945746, by rfl⟩ : syracuseStep 5188657 = 3891493) B3891493
theorem B6237253 : Blo 908576 6237253 := bstep (se 4 (by rfl) ⟨584742, by rfl⟩ : syracuseStep 6237253 = 1169485) B1169485
theorem B5844109 : Blo 908576 5844109 := bstep (se 3 (by rfl) ⟨1095770, by rfl⟩ : syracuseStep 5844109 = 2191541) B2191541
theorem B2305169 : Blo 908576 2305169 := bstep (se 2 (by rfl) ⟨864438, by rfl⟩ : syracuseStep 2305169 = 1728877) B1728877
theorem B1944739 : Blo 908576 1944739 := bstep (se 1 (by rfl) ⟨1458554, by rfl⟩ : syracuseStep 1944739 = 2917109) B2917109
theorem B2305219 : Blo 908576 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B11054389 : Blo 908576 11054389 := bstep (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) B1036349
theorem B2305361 : Blo 908576 2305361 := bstep (se 2 (by rfl) ⟨864510, by rfl⟩ : syracuseStep 2305361 = 1729021) B1729021
theorem B4369763 : Blo 908576 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B4435469 : Blo 908576 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B13119029 : Blo 908576 13119029 := bstep (se 5 (by rfl) ⟨614954, by rfl⟩ : syracuseStep 13119029 = 1229909) B1229909
theorem B6074309 : Blo 908576 6074309 := bstep (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) B1138933
theorem B2306353 : Blo 908576 2306353 := bstep (se 2 (by rfl) ⟨864882, by rfl⟩ : syracuseStep 2306353 = 1729765) B1729765
theorem B5190115 : Blo 908576 5190115 := bstep (se 1 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 5190115 = 7785173) B7785173
theorem B3453425 : Blo 908576 3453425 := bstep (se 2 (by rfl) ⟨1295034, by rfl⟩ : syracuseStep 3453425 = 2590069) B2590069
theorem B4370993 : Blo 908576 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B1094195 : Blo 908576 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B2306627 : Blo 908576 2306627 := bstep (se 1 (by rfl) ⟨1729970, by rfl⟩ : syracuseStep 2306627 = 3459941) B3459941
theorem B2044529 : Blo 908576 2044529 := bstep (se 2 (by rfl) ⟨766698, by rfl⟩ : syracuseStep 2044529 = 1533397) B1533397
theorem B1946225 : Blo 908576 1946225 := bstep (se 2 (by rfl) ⟨729834, by rfl⟩ : syracuseStep 1946225 = 1459669) B1459669
theorem B2044547 : Blo 908576 2044547 := bstep (se 1 (by rfl) ⟨1533410, by rfl⟩ : syracuseStep 2044547 = 3066821) B3066821
theorem B1946243 : Blo 908576 1946243 := bstep (se 1 (by rfl) ⟨1459682, by rfl⟩ : syracuseStep 1946243 = 2919365) B2919365
theorem B2306819 : Blo 908576 2306819 := bstep (se 1 (by rfl) ⟨1730114, by rfl⟩ : syracuseStep 2306819 = 3460229) B3460229
theorem B44970773 : Blo 908576 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B1094531 : Blo 908576 1094531 := bstep (se 1 (by rfl) ⟨820898, by rfl⟩ : syracuseStep 1094531 = 1641797) B1641797
theorem B2044817 : Blo 908576 2044817 := bstep (se 2 (by rfl) ⟨766806, by rfl⟩ : syracuseStep 2044817 = 1533613) B1533613
theorem B2044835 : Blo 908576 2044835 := bstep (se 1 (by rfl) ⟨1533626, by rfl⟩ : syracuseStep 2044835 = 3067253) B3067253
theorem B5190641 : Blo 908576 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B1848433 : Blo 908576 1848433 := bstep (se 2 (by rfl) ⟨693162, by rfl⟩ : syracuseStep 1848433 = 1386325) B1386325
theorem B2045105 : Blo 908576 2045105 := bstep (se 2 (by rfl) ⟨766914, by rfl⟩ : syracuseStep 2045105 = 1533829) B1533829
theorem B2045123 : Blo 908576 2045123 := bstep (se 1 (by rfl) ⟨1533842, by rfl⟩ : syracuseStep 2045123 = 3067685) B3067685
theorem B19674389 : Blo 908576 19674389 := bstep (se 6 (by rfl) ⟨461118, by rfl⟩ : syracuseStep 19674389 = 922237) B922237
theorem B4601123 : Blo 908576 4601123 := bstep (se 1 (by rfl) ⟨3450842, by rfl⟩ : syracuseStep 4601123 = 6901685) B6901685
theorem B2045393 : Blo 908576 2045393 := bstep (se 2 (by rfl) ⟨767022, by rfl⟩ : syracuseStep 2045393 = 1534045) B1534045
theorem B2045411 : Blo 908576 2045411 := bstep (se 1 (by rfl) ⟨1534058, by rfl⟩ : syracuseStep 2045411 = 3068117) B3068117
theorem B4667021 : Blo 908576 4667021 := bstep (se 3 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 4667021 = 1750133) B1750133
theorem B2307761 : Blo 908576 2307761 := bstep (se 2 (by rfl) ⟨865410, by rfl⟩ : syracuseStep 2307761 = 1730821) B1730821
theorem B2307811 : Blo 908576 2307811 := bstep (se 1 (by rfl) ⟨1730858, by rfl⟩ : syracuseStep 2307811 = 3461717) B3461717
theorem B2045681 : Blo 908576 2045681 := bstep (se 2 (by rfl) ⟨767130, by rfl⟩ : syracuseStep 2045681 = 1534261) B1534261
theorem B2340593 : Blo 908576 2340593 := bstep (se 2 (by rfl) ⟨877722, by rfl⟩ : syracuseStep 2340593 = 1755445) B1755445
theorem B2045699 : Blo 908576 2045699 := bstep (se 1 (by rfl) ⟨1534274, by rfl⟩ : syracuseStep 2045699 = 3068549) B3068549
theorem B1455889 : Blo 908576 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B2078531 : Blo 908576 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1947473 : Blo 908576 1947473 := bstep (se 2 (by rfl) ⟨730302, by rfl⟩ : syracuseStep 1947473 = 1460605) B1460605
theorem B2307953 : Blo 908576 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B3454883 : Blo 908576 3454883 := bstep (se 1 (by rfl) ⟨2591162, by rfl⟩ : syracuseStep 3454883 = 5182325) B5182325
theorem B2045969 : Blo 908576 2045969 := bstep (se 2 (by rfl) ⟨767238, by rfl⟩ : syracuseStep 2045969 = 1534477) B1534477
theorem B2045987 : Blo 908576 2045987 := bstep (se 1 (by rfl) ⟨1534490, by rfl⟩ : syracuseStep 2045987 = 3068981) B3068981
theorem B14956597 : Blo 908576 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B4601933 : Blo 908576 4601933 := bstep (se 3 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 4601933 = 1725725) B1725725
theorem B1456337 : Blo 908576 1456337 := bstep (se 2 (by rfl) ⟨546126, by rfl⟩ : syracuseStep 1456337 = 1092253) B1092253
theorem B2046257 : Blo 908576 2046257 := bstep (se 2 (by rfl) ⟨767346, by rfl⟩ : syracuseStep 2046257 = 1534693) B1534693
theorem B2046275 : Blo 908576 2046275 := bstep (se 1 (by rfl) ⟨1534706, by rfl⟩ : syracuseStep 2046275 = 3069413) B3069413
theorem B23607665 : Blo 908576 23607665 := bstep (se 2 (by rfl) ⟨8852874, by rfl⟩ : syracuseStep 23607665 = 17705749) B17705749
theorem B5192099 : Blo 908576 5192099 := bstep (se 1 (by rfl) ⟨3894074, by rfl⟩ : syracuseStep 5192099 = 7788149) B7788149
theorem B2046545 : Blo 908576 2046545 := bstep (se 2 (by rfl) ⟨767454, by rfl⟩ : syracuseStep 2046545 = 1534909) B1534909
theorem B2046563 : Blo 908576 2046563 := bstep (se 1 (by rfl) ⟨1534922, by rfl⟩ : syracuseStep 2046563 = 3069845) B3069845
theorem B10533685 : Blo 908576 10533685 := bstep (se 5 (by rfl) ⟨493766, by rfl⟩ : syracuseStep 10533685 = 987533) B987533
theorem B1686353 : Blo 908576 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B2308945 : Blo 908576 2308945 := bstep (se 2 (by rfl) ⟨865854, by rfl⟩ : syracuseStep 2308945 = 1731709) B1731709
theorem B2046833 : Blo 908576 2046833 := bstep (se 2 (by rfl) ⟨767562, by rfl⟩ : syracuseStep 2046833 = 1535125) B1535125
theorem B2046851 : Blo 908576 2046851 := bstep (se 1 (by rfl) ⟨1535138, by rfl⟩ : syracuseStep 2046851 = 3070277) B3070277
theorem B3455885 : Blo 908576 3455885 := bstep (se 3 (by rfl) ⟨647978, by rfl⟩ : syracuseStep 3455885 = 1295957) B1295957
theorem B4373453 : Blo 908576 4373453 := bstep (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) B1640045
theorem B1457203 : Blo 908576 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B2309219 : Blo 908576 2309219 := bstep (se 1 (by rfl) ⟨1731914, by rfl⟩ : syracuseStep 2309219 = 3463829) B3463829
theorem B2047121 : Blo 908576 2047121 := bstep (se 2 (by rfl) ⟨767670, by rfl⟩ : syracuseStep 2047121 = 1535341) B1535341
theorem B2047139 : Blo 908576 2047139 := bstep (se 1 (by rfl) ⟨1535354, by rfl⟩ : syracuseStep 2047139 = 3070709) B3070709
theorem B2309411 : Blo 908576 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B1949027 : Blo 908576 1949027 := bstep (se 1 (by rfl) ⟨1461770, by rfl⟩ : syracuseStep 1949027 = 2923541) B2923541
theorem B2768269 : Blo 908576 2768269 := bstep (se 3 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 2768269 = 1038101) B1038101
theorem B2047409 : Blo 908576 2047409 := bstep (se 2 (by rfl) ⟨767778, by rfl⟩ : syracuseStep 2047409 = 1535557) B1535557
theorem B2047427 : Blo 908576 2047427 := bstep (se 1 (by rfl) ⟨1535570, by rfl⟩ : syracuseStep 2047427 = 3071141) B3071141
theorem B1293907 : Blo 908576 1293907 := bstep (se 1 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 1293907 = 1940861) B1940861
theorem B2047697 : Blo 908576 2047697 := bstep (se 2 (by rfl) ⟨767886, by rfl⟩ : syracuseStep 2047697 = 1535773) B1535773
theorem B1457875 : Blo 908576 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B2047715 : Blo 908576 2047715 := bstep (se 1 (by rfl) ⟨1535786, by rfl⟩ : syracuseStep 2047715 = 3071573) B3071573
theorem B1457921 : Blo 908576 1457921 := bstep (se 2 (by rfl) ⟨546720, by rfl⟩ : syracuseStep 1457921 = 1093441) B1093441
theorem B3686257 : Blo 908576 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B6569869 : Blo 908576 6569869 := bstep (se 3 (by rfl) ⟨1231850, by rfl⟩ : syracuseStep 6569869 = 2463701) B2463701
theorem B2047985 : Blo 908576 2047985 := bstep (se 2 (by rfl) ⟨767994, by rfl⟩ : syracuseStep 2047985 = 1535989) B1535989
theorem B2048003 : Blo 908576 2048003 := bstep (se 1 (by rfl) ⟨1536002, by rfl⟩ : syracuseStep 2048003 = 3072005) B3072005
theorem B1294385 : Blo 908576 1294385 := bstep (se 2 (by rfl) ⟨485394, by rfl⟩ : syracuseStep 1294385 = 970789) B970789
theorem B6570125 : Blo 908576 6570125 := bstep (se 3 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 6570125 = 2463797) B2463797
theorem B1294499 : Blo 908576 1294499 := bstep (se 1 (by rfl) ⟨970874, by rfl⟩ : syracuseStep 1294499 = 1941749) B1941749
theorem B1294579 : Blo 908576 1294579 := bstep (se 1 (by rfl) ⟨970934, by rfl⟩ : syracuseStep 1294579 = 1941869) B1941869
theorem B1458433 : Blo 908576 1458433 := bstep (se 2 (by rfl) ⟨546912, by rfl⟩ : syracuseStep 1458433 = 1093825) B1093825
theorem B5193989 : Blo 908576 5193989 := bstep (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) B973873
theorem B2048273 : Blo 908576 2048273 := bstep (se 2 (by rfl) ⟨768102, by rfl⟩ : syracuseStep 2048273 = 1536205) B1536205
theorem B2048291 : Blo 908576 2048291 := bstep (se 1 (by rfl) ⟨1536218, by rfl⟩ : syracuseStep 2048291 = 3072437) B3072437
theorem B1229299 : Blo 908576 1229299 := bstep (se 1 (by rfl) ⟨921974, by rfl⟩ : syracuseStep 1229299 = 1843949) B1843949
theorem B2048561 : Blo 908576 2048561 := bstep (se 2 (by rfl) ⟨768210, by rfl⟩ : syracuseStep 2048561 = 1536421) B1536421
theorem B2048579 : Blo 908576 2048579 := bstep (se 1 (by rfl) ⟨1536434, by rfl⟩ : syracuseStep 2048579 = 3072869) B3072869
theorem B4440781 : Blo 908576 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B1295137 : Blo 908576 1295137 := bstep (se 2 (by rfl) ⟨485676, by rfl⟩ : syracuseStep 1295137 = 971353) B971353
theorem B1458977 : Blo 908576 1458977 := bstep (se 2 (by rfl) ⟨547116, by rfl⟩ : syracuseStep 1458977 = 1094233) B1094233
theorem B2048849 : Blo 908576 2048849 := bstep (se 2 (by rfl) ⟨768318, by rfl⟩ : syracuseStep 2048849 = 1536637) B1536637
theorem B2048867 : Blo 908576 2048867 := bstep (se 1 (by rfl) ⟨1536650, by rfl⟩ : syracuseStep 2048867 = 3073301) B3073301
theorem B4604849 : Blo 908576 4604849 := bstep (se 2 (by rfl) ⟨1726818, by rfl⟩ : syracuseStep 4604849 = 3453637) B3453637
theorem B3457997 : Blo 908576 3457997 := bstep (se 3 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 3457997 = 1296749) B1296749
theorem B2049137 : Blo 908576 2049137 := bstep (se 2 (by rfl) ⟨768426, by rfl⟩ : syracuseStep 2049137 = 1536853) B1536853
theorem B2049155 : Blo 908576 2049155 := bstep (se 1 (by rfl) ⟨1536866, by rfl⟩ : syracuseStep 2049155 = 3073733) B3073733
theorem B1557809 : Blo 908576 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B2049425 : Blo 908576 2049425 := bstep (se 2 (by rfl) ⟨768534, by rfl⟩ : syracuseStep 2049425 = 1537069) B1537069
theorem B2049443 : Blo 908576 2049443 := bstep (se 1 (by rfl) ⟨1537082, by rfl⟩ : syracuseStep 2049443 = 3074165) B3074165
theorem B1295843 : Blo 908576 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B3884557 : Blo 908576 3884557 := bstep (se 3 (by rfl) ⟨728354, by rfl⟩ : syracuseStep 3884557 = 1456709) B1456709
theorem B1754723 : Blo 908576 1754723 := bstep (se 1 (by rfl) ⟨1316042, by rfl⟩ : syracuseStep 1754723 = 2632085) B2632085
theorem B2049713 : Blo 908576 2049713 := bstep (se 2 (by rfl) ⟨768642, by rfl⟩ : syracuseStep 2049713 = 1537285) B1537285
theorem B2049731 : Blo 908576 2049731 := bstep (se 1 (by rfl) ⟨1537298, by rfl⟩ : syracuseStep 2049731 = 3074597) B3074597
theorem B1459939 : Blo 908576 1459939 := bstep (se 1 (by rfl) ⟨1094954, by rfl⟩ : syracuseStep 1459939 = 2189909) B2189909
theorem B3458801 : Blo 908576 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B2050001 : Blo 908576 2050001 := bstep (se 2 (by rfl) ⟨768750, by rfl⟩ : syracuseStep 2050001 = 1537501) B1537501
theorem B2050019 : Blo 908576 2050019 := bstep (se 1 (by rfl) ⟨1537514, by rfl⟩ : syracuseStep 2050019 = 3075029) B3075029
theorem B1460195 : Blo 908576 1460195 := bstep (se 1 (by rfl) ⟨1095146, by rfl⟩ : syracuseStep 1460195 = 2190293) B2190293
theorem B1296481 : Blo 908576 1296481 := bstep (se 2 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 1296481 = 972361) B972361
theorem B1558643 : Blo 908576 1558643 := bstep (se 1 (by rfl) ⟨1168982, by rfl⟩ : syracuseStep 1558643 = 2337965) B2337965
theorem B1755299 : Blo 908576 1755299 := bstep (se 1 (by rfl) ⟨1316474, by rfl⟩ : syracuseStep 1755299 = 2632949) B2632949
theorem B1296595 : Blo 908576 1296595 := bstep (se 1 (by rfl) ⟨972446, by rfl⟩ : syracuseStep 1296595 = 1944893) B1944893
theorem B4442339 : Blo 908576 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B2050289 : Blo 908576 2050289 := bstep (se 2 (by rfl) ⟨768858, by rfl⟩ : syracuseStep 2050289 = 1537717) B1537717
theorem B2050307 : Blo 908576 2050307 := bstep (se 1 (by rfl) ⟨1537730, by rfl⟩ : syracuseStep 2050307 = 3075461) B3075461
theorem B4606307 : Blo 908576 4606307 := bstep (se 1 (by rfl) ⟨3454730, by rfl⟩ : syracuseStep 4606307 = 6909461) B6909461
theorem B3459469 : Blo 908576 3459469 := bstep (se 3 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 3459469 = 1297301) B1297301
theorem B2050577 : Blo 908576 2050577 := bstep (se 2 (by rfl) ⟨768966, by rfl⟩ : syracuseStep 2050577 = 1537933) B1537933
theorem B2050595 : Blo 908576 2050595 := bstep (se 1 (by rfl) ⟨1537946, by rfl⟩ : syracuseStep 2050595 = 3075893) B3075893
theorem B2214467 : Blo 908576 2214467 := bstep (se 1 (by rfl) ⟨1660850, by rfl⟩ : syracuseStep 2214467 = 3321701) B3321701
theorem B1460899 : Blo 908576 1460899 := bstep (se 1 (by rfl) ⟨1095674, by rfl⟩ : syracuseStep 1460899 = 2191349) B2191349
theorem B3066605 : Blo 908576 3066605 := bstep (se 3 (by rfl) ⟨574988, by rfl⟩ : syracuseStep 3066605 = 1149977) B1149977
theorem B3066659 : Blo 908576 3066659 := bstep (se 1 (by rfl) ⟨2299994, by rfl⟩ : syracuseStep 3066659 = 4599989) B4599989
theorem B2050865 : Blo 908576 2050865 := bstep (se 2 (by rfl) ⟨769074, by rfl⟩ : syracuseStep 2050865 = 1538149) B1538149
theorem B2050883 : Blo 908576 2050883 := bstep (se 1 (by rfl) ⟨1538162, by rfl⟩ : syracuseStep 2050883 = 3076325) B3076325
theorem B1461169 : Blo 908576 1461169 := bstep (se 2 (by rfl) ⟨547938, by rfl⟩ : syracuseStep 1461169 = 1095877) B1095877
theorem B1362881 : Blo 908576 1362881 := bstep (se 2 (by rfl) ⟨511080, by rfl⟩ : syracuseStep 1362881 = 1022161) B1022161
theorem B1362899 : Blo 908576 1362899 := bstep (se 1 (by rfl) ⟨1022174, by rfl⟩ : syracuseStep 1362899 = 2044349) B2044349
theorem B1362929 : Blo 908576 1362929 := bstep (se 2 (by rfl) ⟨511098, by rfl⟩ : syracuseStep 1362929 = 1022197) B1022197
theorem B1461233 : Blo 908576 1461233 := bstep (se 2 (by rfl) ⟨547962, by rfl⟩ : syracuseStep 1461233 = 1095925) B1095925
theorem B1362947 : Blo 908576 1362947 := bstep (se 1 (by rfl) ⟨1022210, by rfl⟩ : syracuseStep 1362947 = 2044421) B2044421
theorem B1362977 : Blo 908576 1362977 := bstep (se 2 (by rfl) ⟨511116, by rfl⟩ : syracuseStep 1362977 = 1022233) B1022233
theorem B3066929 : Blo 908576 3066929 := bstep (se 2 (by rfl) ⟨1150098, by rfl⟩ : syracuseStep 3066929 = 2300197) B2300197
theorem B1362995 : Blo 908576 1362995 := bstep (se 1 (by rfl) ⟨1022246, by rfl⟩ : syracuseStep 1362995 = 2044493) B2044493
theorem B1363025 : Blo 908576 1363025 := bstep (se 2 (by rfl) ⟨511134, by rfl⟩ : syracuseStep 1363025 = 1022269) B1022269
theorem B2051153 : Blo 908576 2051153 := bstep (se 2 (by rfl) ⟨769182, by rfl⟩ : syracuseStep 2051153 = 1538365) B1538365
theorem B1363043 : Blo 908576 1363043 := bstep (se 1 (by rfl) ⟨1022282, by rfl⟩ : syracuseStep 1363043 = 2044565) B2044565
theorem B2051171 : Blo 908576 2051171 := bstep (se 1 (by rfl) ⟨1538378, by rfl⟩ : syracuseStep 2051171 = 3076757) B3076757
theorem B23645297 : Blo 908576 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B1363073 : Blo 908576 1363073 := bstep (se 2 (by rfl) ⟨511152, by rfl⟩ : syracuseStep 1363073 = 1022305) B1022305
theorem B4607117 : Blo 908576 4607117 := bstep (se 3 (by rfl) ⟨863834, by rfl⟩ : syracuseStep 4607117 = 1727669) B1727669
theorem B1363091 : Blo 908576 1363091 := bstep (se 1 (by rfl) ⟨1022318, by rfl⟩ : syracuseStep 1363091 = 2044637) B2044637
theorem B3460259 : Blo 908576 3460259 := bstep (se 1 (by rfl) ⟨2595194, by rfl⟩ : syracuseStep 3460259 = 5190389) B5190389
theorem B1363121 : Blo 908576 1363121 := bstep (se 2 (by rfl) ⟨511170, by rfl⟩ : syracuseStep 1363121 = 1022341) B1022341
theorem B1363139 : Blo 908576 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B1363169 : Blo 908576 1363169 := bstep (se 2 (by rfl) ⟨511188, by rfl⟩ : syracuseStep 1363169 = 1022377) B1022377
theorem B1363187 : Blo 908576 1363187 := bstep (se 1 (by rfl) ⟨1022390, by rfl⟩ : syracuseStep 1363187 = 2044781) B2044781
theorem B1363217 : Blo 908576 1363217 := bstep (se 2 (by rfl) ⟨511206, by rfl⟩ : syracuseStep 1363217 = 1022413) B1022413
theorem B1363235 : Blo 908576 1363235 := bstep (se 1 (by rfl) ⟨1022426, by rfl⟩ : syracuseStep 1363235 = 2044853) B2044853
theorem B1363265 : Blo 908576 1363265 := bstep (se 2 (by rfl) ⟨511224, by rfl⟩ : syracuseStep 1363265 = 1022449) B1022449
theorem B1363283 : Blo 908576 1363283 := bstep (se 1 (by rfl) ⟨1022462, by rfl⟩ : syracuseStep 1363283 = 2044925) B2044925
theorem B1363313 : Blo 908576 1363313 := bstep (se 2 (by rfl) ⟨511242, by rfl⟩ : syracuseStep 1363313 = 1022485) B1022485
theorem B2051441 : Blo 908576 2051441 := bstep (se 2 (by rfl) ⟨769290, by rfl⟩ : syracuseStep 2051441 = 1538581) B1538581
theorem B1363331 : Blo 908576 1363331 := bstep (se 1 (by rfl) ⟨1022498, by rfl⟩ : syracuseStep 1363331 = 2044997) B2044997
theorem B2051459 : Blo 908576 2051459 := bstep (se 1 (by rfl) ⟨1538594, by rfl⟩ : syracuseStep 2051459 = 3077189) B3077189
theorem B1363361 : Blo 908576 1363361 := bstep (se 2 (by rfl) ⟨511260, by rfl⟩ : syracuseStep 1363361 = 1022521) B1022521
theorem B3689891 : Blo 908576 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B1363379 : Blo 908576 1363379 := bstep (se 1 (by rfl) ⟨1022534, by rfl⟩ : syracuseStep 1363379 = 2045069) B2045069
theorem B1363409 : Blo 908576 1363409 := bstep (se 2 (by rfl) ⟨511278, by rfl⟩ : syracuseStep 1363409 = 1022557) B1022557
theorem B1363427 : Blo 908576 1363427 := bstep (se 1 (by rfl) ⟨1022570, by rfl⟩ : syracuseStep 1363427 = 2045141) B2045141
theorem B1363457 : Blo 908576 1363457 := bstep (se 2 (by rfl) ⟨511296, by rfl⟩ : syracuseStep 1363457 = 1022593) B1022593
theorem B1363475 : Blo 908576 1363475 := bstep (se 1 (by rfl) ⟨1022606, by rfl⟩ : syracuseStep 1363475 = 2045213) B2045213
theorem B1297939 : Blo 908576 1297939 := bstep (se 1 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 1297939 = 1946909) B1946909
theorem B1363505 : Blo 908576 1363505 := bstep (se 2 (by rfl) ⟨511314, by rfl⟩ : syracuseStep 1363505 = 1022629) B1022629
theorem B1363523 : Blo 908576 1363523 := bstep (se 1 (by rfl) ⟨1022642, by rfl⟩ : syracuseStep 1363523 = 2045285) B2045285
theorem B3067469 : Blo 908576 3067469 := bstep (se 3 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 3067469 = 1150301) B1150301
theorem B1363553 : Blo 908576 1363553 := bstep (se 2 (by rfl) ⟨511332, by rfl⟩ : syracuseStep 1363553 = 1022665) B1022665
theorem B1363571 : Blo 908576 1363571 := bstep (se 1 (by rfl) ⟨1022678, by rfl⟩ : syracuseStep 1363571 = 2045357) B2045357
theorem B3067523 : Blo 908576 3067523 := bstep (se 1 (by rfl) ⟨2300642, by rfl⟩ : syracuseStep 3067523 = 4601285) B4601285
theorem B1363601 : Blo 908576 1363601 := bstep (se 2 (by rfl) ⟨511350, by rfl⟩ : syracuseStep 1363601 = 1022701) B1022701
theorem B2051729 : Blo 908576 2051729 := bstep (se 2 (by rfl) ⟨769398, by rfl⟩ : syracuseStep 2051729 = 1538797) B1538797
theorem B1560211 : Blo 908576 1560211 := bstep (se 1 (by rfl) ⟨1170158, by rfl⟩ : syracuseStep 1560211 = 2340317) B2340317
theorem B1363619 : Blo 908576 1363619 := bstep (se 1 (by rfl) ⟨1022714, by rfl⟩ : syracuseStep 1363619 = 2045429) B2045429
theorem B2051747 : Blo 908576 2051747 := bstep (se 1 (by rfl) ⟨1538810, by rfl⟩ : syracuseStep 2051747 = 3077621) B3077621
theorem B1363649 : Blo 908576 1363649 := bstep (se 2 (by rfl) ⟨511368, by rfl⟩ : syracuseStep 1363649 = 1022737) B1022737
theorem B1363667 : Blo 908576 1363667 := bstep (se 1 (by rfl) ⟨1022750, by rfl⟩ : syracuseStep 1363667 = 2045501) B2045501
theorem B1363697 : Blo 908576 1363697 := bstep (se 2 (by rfl) ⟨511386, by rfl⟩ : syracuseStep 1363697 = 1022773) B1022773
theorem B1363715 : Blo 908576 1363715 := bstep (se 1 (by rfl) ⟨1022786, by rfl⟩ : syracuseStep 1363715 = 2045573) B2045573
theorem B1363745 : Blo 908576 1363745 := bstep (se 2 (by rfl) ⟨511404, by rfl⟩ : syracuseStep 1363745 = 1022809) B1022809
theorem B3460913 : Blo 908576 3460913 := bstep (se 2 (by rfl) ⟨1297842, by rfl⟩ : syracuseStep 3460913 = 2595685) B2595685
theorem B1363763 : Blo 908576 1363763 := bstep (se 1 (by rfl) ⟨1022822, by rfl⟩ : syracuseStep 1363763 = 2045645) B2045645
theorem B1363793 : Blo 908576 1363793 := bstep (se 2 (by rfl) ⟨511422, by rfl⟩ : syracuseStep 1363793 = 1022845) B1022845
theorem B1363811 : Blo 908576 1363811 := bstep (se 1 (by rfl) ⟨1022858, by rfl⟩ : syracuseStep 1363811 = 2045717) B2045717
theorem B1363841 : Blo 908576 1363841 := bstep (se 2 (by rfl) ⟨511440, by rfl⟩ : syracuseStep 1363841 = 1022881) B1022881
theorem B3067793 : Blo 908576 3067793 := bstep (se 2 (by rfl) ⟨1150422, by rfl⟩ : syracuseStep 3067793 = 2300845) B2300845
theorem B1363859 : Blo 908576 1363859 := bstep (se 1 (by rfl) ⟨1022894, by rfl⟩ : syracuseStep 1363859 = 2045789) B2045789
theorem B1363889 : Blo 908576 1363889 := bstep (se 2 (by rfl) ⟨511458, by rfl⟩ : syracuseStep 1363889 = 1022917) B1022917
theorem B2052017 : Blo 908576 2052017 := bstep (se 2 (by rfl) ⟨769506, by rfl⟩ : syracuseStep 2052017 = 1539013) B1539013
theorem B1363907 : Blo 908576 1363907 := bstep (se 1 (by rfl) ⟨1022930, by rfl⟩ : syracuseStep 1363907 = 2045861) B2045861
theorem B2052035 : Blo 908576 2052035 := bstep (se 1 (by rfl) ⟨1539026, by rfl⟩ : syracuseStep 2052035 = 3078053) B3078053
theorem B1363937 : Blo 908576 1363937 := bstep (se 2 (by rfl) ⟨511476, by rfl⟩ : syracuseStep 1363937 = 1022953) B1022953
theorem B1363955 : Blo 908576 1363955 := bstep (se 1 (by rfl) ⟨1022966, by rfl⟩ : syracuseStep 1363955 = 2045933) B2045933
theorem B1363985 : Blo 908576 1363985 := bstep (se 2 (by rfl) ⟨511494, by rfl⟩ : syracuseStep 1363985 = 1022989) B1022989
theorem B1364003 : Blo 908576 1364003 := bstep (se 1 (by rfl) ⟨1023002, by rfl⟩ : syracuseStep 1364003 = 2046005) B2046005
theorem B1364033 : Blo 908576 1364033 := bstep (se 2 (by rfl) ⟨511512, by rfl⟩ : syracuseStep 1364033 = 1023025) B1023025
theorem B1364051 : Blo 908576 1364051 := bstep (se 1 (by rfl) ⟨1023038, by rfl⟩ : syracuseStep 1364051 = 2046077) B2046077
theorem B1364081 : Blo 908576 1364081 := bstep (se 2 (by rfl) ⟨511530, by rfl⟩ : syracuseStep 1364081 = 1023061) B1023061
theorem B1364099 : Blo 908576 1364099 := bstep (se 1 (by rfl) ⟨1023074, by rfl⟩ : syracuseStep 1364099 = 2046149) B2046149
theorem B1364129 : Blo 908576 1364129 := bstep (se 2 (by rfl) ⟨511548, by rfl⟩ : syracuseStep 1364129 = 1023097) B1023097
theorem B2183345 : Blo 908576 2183345 := bstep (se 2 (by rfl) ⟨818754, by rfl⟩ : syracuseStep 2183345 = 1637509) B1637509
theorem B1364147 : Blo 908576 1364147 := bstep (se 1 (by rfl) ⟨1023110, by rfl⟩ : syracuseStep 1364147 = 2046221) B2046221
theorem B6574277 : Blo 908576 6574277 := bstep (se 4 (by rfl) ⟨616338, by rfl⟩ : syracuseStep 6574277 = 1232677) B1232677
theorem B1364177 : Blo 908576 1364177 := bstep (se 2 (by rfl) ⟨511566, by rfl⟩ : syracuseStep 1364177 = 1023133) B1023133
theorem B2052305 : Blo 908576 2052305 := bstep (se 2 (by rfl) ⟨769614, by rfl⟩ : syracuseStep 2052305 = 1539229) B1539229
theorem B1364195 : Blo 908576 1364195 := bstep (se 1 (by rfl) ⟨1023146, by rfl⟩ : syracuseStep 1364195 = 2046293) B2046293
theorem B2052323 : Blo 908576 2052323 := bstep (se 1 (by rfl) ⟨1539242, by rfl⟩ : syracuseStep 2052323 = 3078485) B3078485
theorem B1364225 : Blo 908576 1364225 := bstep (se 2 (by rfl) ⟨511584, by rfl⟩ : syracuseStep 1364225 = 1023169) B1023169
theorem B971011 : Blo 908576 971011 := bstep (se 1 (by rfl) ⟨728258, by rfl⟩ : syracuseStep 971011 = 1456517) B1456517
theorem B1364243 : Blo 908576 1364243 := bstep (se 1 (by rfl) ⟨1023182, by rfl⟩ : syracuseStep 1364243 = 2046365) B2046365
theorem B1364273 : Blo 908576 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B1364291 : Blo 908576 1364291 := bstep (se 1 (by rfl) ⟨1023218, by rfl⟩ : syracuseStep 1364291 = 2046437) B2046437
theorem B1233235 : Blo 908576 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B1364321 : Blo 908576 1364321 := bstep (se 2 (by rfl) ⟨511620, by rfl⟩ : syracuseStep 1364321 = 1023241) B1023241
theorem B1364339 : Blo 908576 1364339 := bstep (se 1 (by rfl) ⟨1023254, by rfl⟩ : syracuseStep 1364339 = 2046509) B2046509
theorem B1364369 : Blo 908576 1364369 := bstep (se 2 (by rfl) ⟨511638, by rfl⟩ : syracuseStep 1364369 = 1023277) B1023277
theorem B1364387 : Blo 908576 1364387 := bstep (se 1 (by rfl) ⟨1023290, by rfl⟩ : syracuseStep 1364387 = 2046581) B2046581
theorem B3068333 : Blo 908576 3068333 := bstep (se 3 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 3068333 = 1150625) B1150625
theorem B1364417 : Blo 908576 1364417 := bstep (se 2 (by rfl) ⟨511656, by rfl⟩ : syracuseStep 1364417 = 1023313) B1023313
theorem B2773453 : Blo 908576 2773453 := bstep (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) B1040045
theorem B1364435 : Blo 908576 1364435 := bstep (se 1 (by rfl) ⟨1023326, by rfl⟩ : syracuseStep 1364435 = 2046653) B2046653
theorem B3068387 : Blo 908576 3068387 := bstep (se 1 (by rfl) ⟨2301290, by rfl⟩ : syracuseStep 3068387 = 4602581) B4602581
theorem B1364465 : Blo 908576 1364465 := bstep (se 2 (by rfl) ⟨511674, by rfl⟩ : syracuseStep 1364465 = 1023349) B1023349
theorem B7885297 : Blo 908576 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B2052593 : Blo 908576 2052593 := bstep (se 2 (by rfl) ⟨769722, by rfl⟩ : syracuseStep 2052593 = 1539445) B1539445
theorem B1364483 : Blo 908576 1364483 := bstep (se 1 (by rfl) ⟨1023362, by rfl⟩ : syracuseStep 1364483 = 2046725) B2046725
theorem B2052611 : Blo 908576 2052611 := bstep (se 1 (by rfl) ⟨1539458, by rfl⟩ : syracuseStep 2052611 = 3078917) B3078917
theorem B1364513 : Blo 908576 1364513 := bstep (se 2 (by rfl) ⟨511692, by rfl⟩ : syracuseStep 1364513 = 1023385) B1023385
theorem B1364531 : Blo 908576 1364531 := bstep (se 1 (by rfl) ⟨1023398, by rfl⟩ : syracuseStep 1364531 = 2046797) B2046797
theorem B1364561 : Blo 908576 1364561 := bstep (se 2 (by rfl) ⟨511710, by rfl⟩ : syracuseStep 1364561 = 1023421) B1023421
theorem B1364579 : Blo 908576 1364579 := bstep (se 1 (by rfl) ⟨1023434, by rfl⟩ : syracuseStep 1364579 = 2046869) B2046869
theorem B1364609 : Blo 908576 1364609 := bstep (se 2 (by rfl) ⟨511728, by rfl⟩ : syracuseStep 1364609 = 1023457) B1023457
theorem B1299073 : Blo 908576 1299073 := bstep (se 2 (by rfl) ⟨487152, by rfl⟩ : syracuseStep 1299073 = 974305) B974305
theorem B1364627 : Blo 908576 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B1364657 : Blo 908576 1364657 := bstep (se 2 (by rfl) ⟨511746, by rfl⟩ : syracuseStep 1364657 = 1023493) B1023493
theorem B1364675 : Blo 908576 1364675 := bstep (se 1 (by rfl) ⟨1023506, by rfl⟩ : syracuseStep 1364675 = 2047013) B2047013
theorem B1364705 : Blo 908576 1364705 := bstep (se 2 (by rfl) ⟨511764, by rfl⟩ : syracuseStep 1364705 = 1023529) B1023529
theorem B1299169 : Blo 908576 1299169 := bstep (se 2 (by rfl) ⟨487188, by rfl⟩ : syracuseStep 1299169 = 974377) B974377
theorem B3068657 : Blo 908576 3068657 := bstep (se 2 (by rfl) ⟨1150746, by rfl⟩ : syracuseStep 3068657 = 2301493) B2301493
theorem B1364723 : Blo 908576 1364723 := bstep (se 1 (by rfl) ⟨1023542, by rfl⟩ : syracuseStep 1364723 = 2047085) B2047085
theorem B1364753 : Blo 908576 1364753 := bstep (se 2 (by rfl) ⟨511782, by rfl⟩ : syracuseStep 1364753 = 1023565) B1023565
theorem B2052881 : Blo 908576 2052881 := bstep (se 2 (by rfl) ⟨769830, by rfl⟩ : syracuseStep 2052881 = 1539661) B1539661
theorem B1364771 : Blo 908576 1364771 := bstep (se 1 (by rfl) ⟨1023578, by rfl⟩ : syracuseStep 1364771 = 2047157) B2047157
theorem B2052899 : Blo 908576 2052899 := bstep (se 1 (by rfl) ⟨1539674, by rfl⟩ : syracuseStep 2052899 = 3079349) B3079349
theorem B1364801 : Blo 908576 1364801 := bstep (se 2 (by rfl) ⟨511800, by rfl⟩ : syracuseStep 1364801 = 1023601) B1023601
theorem B1364819 : Blo 908576 1364819 := bstep (se 1 (by rfl) ⟨1023614, by rfl⟩ : syracuseStep 1364819 = 2047229) B2047229
theorem B1364849 : Blo 908576 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B1364867 : Blo 908576 1364867 := bstep (se 1 (by rfl) ⟨1023650, by rfl⟩ : syracuseStep 1364867 = 2047301) B2047301
theorem B1364897 : Blo 908576 1364897 := bstep (se 2 (by rfl) ⟨511836, by rfl⟩ : syracuseStep 1364897 = 1023673) B1023673
theorem B1364915 : Blo 908576 1364915 := bstep (se 1 (by rfl) ⟨1023686, by rfl⟩ : syracuseStep 1364915 = 2047373) B2047373
theorem B1364945 : Blo 908576 1364945 := bstep (se 2 (by rfl) ⟨511854, by rfl⟩ : syracuseStep 1364945 = 1023709) B1023709
theorem B1364963 : Blo 908576 1364963 := bstep (se 1 (by rfl) ⟨1023722, by rfl⟩ : syracuseStep 1364963 = 2047445) B2047445
theorem B1364993 : Blo 908576 1364993 := bstep (se 2 (by rfl) ⟨511872, by rfl⟩ : syracuseStep 1364993 = 1023745) B1023745
theorem B1365011 : Blo 908576 1365011 := bstep (se 1 (by rfl) ⟨1023758, by rfl⟩ : syracuseStep 1365011 = 2047517) B2047517
theorem B1725475 : Blo 908576 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B1365041 : Blo 908576 1365041 := bstep (se 2 (by rfl) ⟨511890, by rfl⟩ : syracuseStep 1365041 = 1023781) B1023781
theorem B2053169 : Blo 908576 2053169 := bstep (se 2 (by rfl) ⟨769938, by rfl⟩ : syracuseStep 2053169 = 1539877) B1539877
theorem B1365059 : Blo 908576 1365059 := bstep (se 1 (by rfl) ⟨1023794, by rfl⟩ : syracuseStep 1365059 = 2047589) B2047589
theorem B2053187 : Blo 908576 2053187 := bstep (se 1 (by rfl) ⟨1539890, by rfl⟩ : syracuseStep 2053187 = 3079781) B3079781
theorem B2217041 : Blo 908576 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B1365089 : Blo 908576 1365089 := bstep (se 2 (by rfl) ⟨511908, by rfl⟩ : syracuseStep 1365089 = 1023817) B1023817
theorem B1365107 : Blo 908576 1365107 := bstep (se 1 (by rfl) ⟨1023830, by rfl⟩ : syracuseStep 1365107 = 2047661) B2047661
theorem B1365137 : Blo 908576 1365137 := bstep (se 2 (by rfl) ⟨511926, by rfl⟩ : syracuseStep 1365137 = 1023853) B1023853
theorem B1365155 : Blo 908576 1365155 := bstep (se 1 (by rfl) ⟨1023866, by rfl⟩ : syracuseStep 1365155 = 2047733) B2047733
theorem B1365185 : Blo 908576 1365185 := bstep (se 2 (by rfl) ⟨511944, by rfl⟩ : syracuseStep 1365185 = 1023889) B1023889
theorem B1365203 : Blo 908576 1365203 := bstep (se 1 (by rfl) ⟨1023902, by rfl⟩ : syracuseStep 1365203 = 2047805) B2047805
theorem B3462371 : Blo 908576 3462371 := bstep (se 1 (by rfl) ⟨2596778, by rfl⟩ : syracuseStep 3462371 = 5193557) B5193557
theorem B1365233 : Blo 908576 1365233 := bstep (se 2 (by rfl) ⟨511962, by rfl⟩ : syracuseStep 1365233 = 1023925) B1023925
theorem B3462385 : Blo 908576 3462385 := bstep (se 2 (by rfl) ⟨1298394, by rfl⟩ : syracuseStep 3462385 = 2596789) B2596789
theorem B972019 : Blo 908576 972019 := bstep (se 1 (by rfl) ⟨729014, by rfl⟩ : syracuseStep 972019 = 1458029) B1458029
theorem B1365251 : Blo 908576 1365251 := bstep (se 1 (by rfl) ⟨1023938, by rfl⟩ : syracuseStep 1365251 = 2047877) B2047877
theorem B3069197 : Blo 908576 3069197 := bstep (se 3 (by rfl) ⟨575474, by rfl⟩ : syracuseStep 3069197 = 1150949) B1150949
theorem B1365281 : Blo 908576 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B1365299 : Blo 908576 1365299 := bstep (se 1 (by rfl) ⟨1023974, by rfl⟩ : syracuseStep 1365299 = 2047949) B2047949
theorem B3069251 : Blo 908576 3069251 := bstep (se 1 (by rfl) ⟨2301938, by rfl⟩ : syracuseStep 3069251 = 4603877) B4603877
theorem B1365329 : Blo 908576 1365329 := bstep (se 2 (by rfl) ⟨511998, by rfl⟩ : syracuseStep 1365329 = 1023997) B1023997
theorem B1365347 : Blo 908576 1365347 := bstep (se 1 (by rfl) ⟨1024010, by rfl⟩ : syracuseStep 1365347 = 2048021) B2048021
theorem B1365377 : Blo 908576 1365377 := bstep (se 2 (by rfl) ⟨512016, by rfl⟩ : syracuseStep 1365377 = 1024033) B1024033
theorem B1365395 : Blo 908576 1365395 := bstep (se 1 (by rfl) ⟨1024046, by rfl⟩ : syracuseStep 1365395 = 2048093) B2048093
theorem B4740515 : Blo 908576 4740515 := bstep (se 1 (by rfl) ⟨3555386, by rfl⟩ : syracuseStep 4740515 = 7110773) B7110773
theorem B1365425 : Blo 908576 1365425 := bstep (se 2 (by rfl) ⟨512034, by rfl⟩ : syracuseStep 1365425 = 1024069) B1024069
theorem B2774449 : Blo 908576 2774449 := bstep (se 2 (by rfl) ⟨1040418, by rfl⟩ : syracuseStep 2774449 = 2080837) B2080837
theorem B1365443 : Blo 908576 1365443 := bstep (se 1 (by rfl) ⟨1024082, by rfl⟩ : syracuseStep 1365443 = 2048165) B2048165
theorem B1365473 : Blo 908576 1365473 := bstep (se 2 (by rfl) ⟨512052, by rfl⟩ : syracuseStep 1365473 = 1024105) B1024105
theorem B1725923 : Blo 908576 1725923 := bstep (se 1 (by rfl) ⟨1294442, by rfl⟩ : syracuseStep 1725923 = 2588885) B2588885
theorem B1365491 : Blo 908576 1365491 := bstep (se 1 (by rfl) ⟨1024118, by rfl⟩ : syracuseStep 1365491 = 2048237) B2048237
theorem B1365521 : Blo 908576 1365521 := bstep (se 2 (by rfl) ⟨512070, by rfl⟩ : syracuseStep 1365521 = 1024141) B1024141
theorem B1365539 : Blo 908576 1365539 := bstep (se 1 (by rfl) ⟨1024154, by rfl⟩ : syracuseStep 1365539 = 2048309) B2048309
theorem B1365569 : Blo 908576 1365569 := bstep (se 2 (by rfl) ⟨512088, by rfl⟩ : syracuseStep 1365569 = 1024177) B1024177
theorem B3069521 : Blo 908576 3069521 := bstep (se 2 (by rfl) ⟨1151070, by rfl⟩ : syracuseStep 3069521 = 2302141) B2302141
theorem B1365587 : Blo 908576 1365587 := bstep (se 1 (by rfl) ⟨1024190, by rfl⟩ : syracuseStep 1365587 = 2048381) B2048381
theorem B1365617 : Blo 908576 1365617 := bstep (se 2 (by rfl) ⟨512106, by rfl⟩ : syracuseStep 1365617 = 1024213) B1024213
theorem B1365635 : Blo 908576 1365635 := bstep (se 1 (by rfl) ⟨1024226, by rfl⟩ : syracuseStep 1365635 = 2048453) B2048453
theorem B1365665 : Blo 908576 1365665 := bstep (se 2 (by rfl) ⟨512124, by rfl⟩ : syracuseStep 1365665 = 1024249) B1024249
theorem B1365683 : Blo 908576 1365683 := bstep (se 1 (by rfl) ⟨1024262, by rfl⟩ : syracuseStep 1365683 = 2048525) B2048525
theorem B1365713 : Blo 908576 1365713 := bstep (se 2 (by rfl) ⟨512142, by rfl⟩ : syracuseStep 1365713 = 1024285) B1024285
theorem B1365731 : Blo 908576 1365731 := bstep (se 1 (by rfl) ⟨1024298, by rfl⟩ : syracuseStep 1365731 = 2048597) B2048597
theorem B3888881 : Blo 908576 3888881 := bstep (se 2 (by rfl) ⟨1458330, by rfl⟩ : syracuseStep 3888881 = 2916661) B2916661
theorem B1365761 : Blo 908576 1365761 := bstep (se 2 (by rfl) ⟨512160, by rfl⟩ : syracuseStep 1365761 = 1024321) B1024321
theorem B1726211 : Blo 908576 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B1365779 : Blo 908576 1365779 := bstep (se 1 (by rfl) ⟨1024334, by rfl⟩ : syracuseStep 1365779 = 2048669) B2048669
theorem B3888931 : Blo 908576 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B1365809 : Blo 908576 1365809 := bstep (se 2 (by rfl) ⟨512178, by rfl⟩ : syracuseStep 1365809 = 1024357) B1024357
theorem B1365827 : Blo 908576 1365827 := bstep (se 1 (by rfl) ⟨1024370, by rfl⟩ : syracuseStep 1365827 = 2048741) B2048741
theorem B1365857 : Blo 908576 1365857 := bstep (se 2 (by rfl) ⟨512196, by rfl⟩ : syracuseStep 1365857 = 1024393) B1024393
theorem B972643 : Blo 908576 972643 := bstep (se 1 (by rfl) ⟨729482, by rfl⟩ : syracuseStep 972643 = 1458965) B1458965
theorem B1365875 : Blo 908576 1365875 := bstep (se 1 (by rfl) ⟨1024406, by rfl⟩ : syracuseStep 1365875 = 2048813) B2048813
theorem B1365905 : Blo 908576 1365905 := bstep (se 2 (by rfl) ⟨512214, by rfl⟩ : syracuseStep 1365905 = 1024429) B1024429
theorem B1365923 : Blo 908576 1365923 := bstep (se 1 (by rfl) ⟨1024442, by rfl⟩ : syracuseStep 1365923 = 2048885) B2048885
theorem B1365953 : Blo 908576 1365953 := bstep (se 2 (by rfl) ⟨512232, by rfl⟩ : syracuseStep 1365953 = 1024465) B1024465
theorem B1365971 : Blo 908576 1365971 := bstep (se 1 (by rfl) ⟨1024478, by rfl⟩ : syracuseStep 1365971 = 2048957) B2048957
theorem B4610033 : Blo 908576 4610033 := bstep (se 2 (by rfl) ⟨1728762, by rfl⟩ : syracuseStep 4610033 = 3457525) B3457525
theorem B1366001 : Blo 908576 1366001 := bstep (se 2 (by rfl) ⟨512250, by rfl⟩ : syracuseStep 1366001 = 1024501) B1024501
theorem B1366019 : Blo 908576 1366019 := bstep (se 1 (by rfl) ⟨1024514, by rfl⟩ : syracuseStep 1366019 = 2049029) B2049029
theorem B1366049 : Blo 908576 1366049 := bstep (se 2 (by rfl) ⟨512268, by rfl⟩ : syracuseStep 1366049 = 1024537) B1024537
theorem B1366067 : Blo 908576 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B1366097 : Blo 908576 1366097 := bstep (se 2 (by rfl) ⟨512286, by rfl⟩ : syracuseStep 1366097 = 1024573) B1024573
theorem B1366115 : Blo 908576 1366115 := bstep (se 1 (by rfl) ⟨1024586, by rfl⟩ : syracuseStep 1366115 = 2049173) B2049173
theorem B3070061 : Blo 908576 3070061 := bstep (se 3 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 3070061 = 1151273) B1151273
theorem B1366145 : Blo 908576 1366145 := bstep (se 2 (by rfl) ⟨512304, by rfl⟩ : syracuseStep 1366145 = 1024609) B1024609
theorem B1366163 : Blo 908576 1366163 := bstep (se 1 (by rfl) ⟨1024622, by rfl⟩ : syracuseStep 1366163 = 2049245) B2049245
theorem B3070115 : Blo 908576 3070115 := bstep (se 1 (by rfl) ⟨2302586, by rfl⟩ : syracuseStep 3070115 = 4605173) B4605173
theorem B1366193 : Blo 908576 1366193 := bstep (se 2 (by rfl) ⟨512322, by rfl⟩ : syracuseStep 1366193 = 1024645) B1024645
theorem B1366211 : Blo 908576 1366211 := bstep (se 1 (by rfl) ⟨1024658, by rfl⟩ : syracuseStep 1366211 = 2049317) B2049317
theorem B1366241 : Blo 908576 1366241 := bstep (se 2 (by rfl) ⟨512340, by rfl⟩ : syracuseStep 1366241 = 1024681) B1024681
theorem B1366259 : Blo 908576 1366259 := bstep (se 1 (by rfl) ⟨1024694, by rfl⟩ : syracuseStep 1366259 = 2049389) B2049389
theorem B1366289 : Blo 908576 1366289 := bstep (se 2 (by rfl) ⟨512358, by rfl⟩ : syracuseStep 1366289 = 1024717) B1024717
theorem B1366307 : Blo 908576 1366307 := bstep (se 1 (by rfl) ⟨1024730, by rfl⟩ : syracuseStep 1366307 = 2049461) B2049461
theorem B1366337 : Blo 908576 1366337 := bstep (se 2 (by rfl) ⟨512376, by rfl⟩ : syracuseStep 1366337 = 1024753) B1024753
theorem B1366355 : Blo 908576 1366355 := bstep (se 1 (by rfl) ⟨1024766, by rfl⟩ : syracuseStep 1366355 = 2049533) B2049533
theorem B1366385 : Blo 908576 1366385 := bstep (se 2 (by rfl) ⟨512394, by rfl⟩ : syracuseStep 1366385 = 1024789) B1024789
theorem B1366403 : Blo 908576 1366403 := bstep (se 1 (by rfl) ⟨1024802, by rfl⟩ : syracuseStep 1366403 = 2049605) B2049605
theorem B1366433 : Blo 908576 1366433 := bstep (se 2 (by rfl) ⟨512412, by rfl⟩ : syracuseStep 1366433 = 1024825) B1024825
theorem B3070385 : Blo 908576 3070385 := bstep (se 2 (by rfl) ⟨1151394, by rfl⟩ : syracuseStep 3070385 = 2302789) B2302789
theorem B1366451 : Blo 908576 1366451 := bstep (se 1 (by rfl) ⟨1024838, by rfl⟩ : syracuseStep 1366451 = 2049677) B2049677
theorem B1366481 : Blo 908576 1366481 := bstep (se 2 (by rfl) ⟨512430, by rfl⟩ : syracuseStep 1366481 = 1024861) B1024861
theorem B1366499 : Blo 908576 1366499 := bstep (se 1 (by rfl) ⟨1024874, by rfl⟩ : syracuseStep 1366499 = 2049749) B2049749
theorem B1366529 : Blo 908576 1366529 := bstep (se 2 (by rfl) ⟨512448, by rfl⟩ : syracuseStep 1366529 = 1024897) B1024897
theorem B1366547 : Blo 908576 1366547 := bstep (se 1 (by rfl) ⟨1024910, by rfl⟩ : syracuseStep 1366547 = 2049821) B2049821
theorem B1366577 : Blo 908576 1366577 := bstep (se 2 (by rfl) ⟨512466, by rfl⟩ : syracuseStep 1366577 = 1024933) B1024933
theorem B1366595 : Blo 908576 1366595 := bstep (se 1 (by rfl) ⟨1024946, by rfl⟩ : syracuseStep 1366595 = 2049893) B2049893
theorem B1366625 : Blo 908576 1366625 := bstep (se 2 (by rfl) ⟨512484, by rfl⟩ : syracuseStep 1366625 = 1024969) B1024969
theorem B1366643 : Blo 908576 1366643 := bstep (se 1 (by rfl) ⟨1024982, by rfl⟩ : syracuseStep 1366643 = 2049965) B2049965
theorem B1366673 : Blo 908576 1366673 := bstep (se 2 (by rfl) ⟨512502, by rfl⟩ : syracuseStep 1366673 = 1025005) B1025005
theorem B1366691 : Blo 908576 1366691 := bstep (se 1 (by rfl) ⟨1025018, by rfl⟩ : syracuseStep 1366691 = 2050037) B2050037
theorem B3463843 : Blo 908576 3463843 := bstep (se 1 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 3463843 = 5195765) B5195765
theorem B1727153 : Blo 908576 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B1366721 : Blo 908576 1366721 := bstep (se 2 (by rfl) ⟨512520, by rfl⟩ : syracuseStep 1366721 = 1025041) B1025041
theorem B1366739 : Blo 908576 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B1366769 : Blo 908576 1366769 := bstep (se 2 (by rfl) ⟨512538, by rfl⟩ : syracuseStep 1366769 = 1025077) B1025077
theorem B1170163 : Blo 908576 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B2185987 : Blo 908576 2185987 := bstep (se 1 (by rfl) ⟨1639490, by rfl⟩ : syracuseStep 2185987 = 3278981) B3278981
theorem B1366787 : Blo 908576 1366787 := bstep (se 1 (by rfl) ⟨1025090, by rfl⟩ : syracuseStep 1366787 = 2050181) B2050181
theorem B1366817 : Blo 908576 1366817 := bstep (se 2 (by rfl) ⟨512556, by rfl⟩ : syracuseStep 1366817 = 1025113) B1025113
theorem B1366835 : Blo 908576 1366835 := bstep (se 1 (by rfl) ⟨1025126, by rfl⟩ : syracuseStep 1366835 = 2050253) B2050253
theorem B1366865 : Blo 908576 1366865 := bstep (se 2 (by rfl) ⟨512574, by rfl⟩ : syracuseStep 1366865 = 1025149) B1025149
theorem B1366883 : Blo 908576 1366883 := bstep (se 1 (by rfl) ⟨1025162, by rfl⟩ : syracuseStep 1366883 = 2050325) B2050325
theorem B1366913 : Blo 908576 1366913 := bstep (se 2 (by rfl) ⟨512592, by rfl⟩ : syracuseStep 1366913 = 1025185) B1025185
theorem B2841475 : Blo 908576 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B1366931 : Blo 908576 1366931 := bstep (se 1 (by rfl) ⟨1025198, by rfl⟩ : syracuseStep 1366931 = 2050397) B2050397
theorem B1366961 : Blo 908576 1366961 := bstep (se 2 (by rfl) ⟨512610, by rfl⟩ : syracuseStep 1366961 = 1025221) B1025221
theorem B1366979 : Blo 908576 1366979 := bstep (se 1 (by rfl) ⟨1025234, by rfl⟩ : syracuseStep 1366979 = 2050469) B2050469
theorem B3070925 : Blo 908576 3070925 := bstep (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) B1151597
theorem B1367009 : Blo 908576 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B1367027 : Blo 908576 1367027 := bstep (se 1 (by rfl) ⟨1025270, by rfl⟩ : syracuseStep 1367027 = 2050541) B2050541
theorem B3070979 : Blo 908576 3070979 := bstep (se 1 (by rfl) ⟨2303234, by rfl⟩ : syracuseStep 3070979 = 4606469) B4606469
theorem B1367057 : Blo 908576 1367057 := bstep (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) B1025293
theorem B1367075 : Blo 908576 1367075 := bstep (se 1 (by rfl) ⟨1025306, by rfl⟩ : syracuseStep 1367075 = 2050613) B2050613
theorem B1367105 : Blo 908576 1367105 := bstep (se 2 (by rfl) ⟨512664, by rfl⟩ : syracuseStep 1367105 = 1025329) B1025329
theorem B1367123 : Blo 908576 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B1367153 : Blo 908576 1367153 := bstep (se 2 (by rfl) ⟨512682, by rfl⟩ : syracuseStep 1367153 = 1025365) B1025365
theorem B1367171 : Blo 908576 1367171 := bstep (se 1 (by rfl) ⟨1025378, by rfl⟩ : syracuseStep 1367171 = 2050757) B2050757
theorem B1367201 : Blo 908576 1367201 := bstep (se 2 (by rfl) ⟨512700, by rfl⟩ : syracuseStep 1367201 = 1025401) B1025401
theorem B1367219 : Blo 908576 1367219 := bstep (se 1 (by rfl) ⟨1025414, by rfl⟩ : syracuseStep 1367219 = 2050829) B2050829
theorem B1367249 : Blo 908576 1367249 := bstep (se 2 (by rfl) ⟨512718, by rfl⟩ : syracuseStep 1367249 = 1025437) B1025437
theorem B1367267 : Blo 908576 1367267 := bstep (se 1 (by rfl) ⟨1025450, by rfl⟩ : syracuseStep 1367267 = 2050901) B2050901
theorem B1367297 : Blo 908576 1367297 := bstep (se 2 (by rfl) ⟨512736, by rfl⟩ : syracuseStep 1367297 = 1025473) B1025473
theorem B3071249 : Blo 908576 3071249 := bstep (se 2 (by rfl) ⟨1151718, by rfl⟩ : syracuseStep 3071249 = 2303437) B2303437
theorem B1367315 : Blo 908576 1367315 := bstep (se 1 (by rfl) ⟨1025486, by rfl⟩ : syracuseStep 1367315 = 2050973) B2050973
theorem B908579 : Blo 908576 908579 := bstep (se 1 (by rfl) ⟨681434, by rfl⟩ : syracuseStep 908579 = 1362869) B1362869
theorem B1367345 : Blo 908576 1367345 := bstep (se 2 (by rfl) ⟨512754, by rfl⟩ : syracuseStep 1367345 = 1025509) B1025509
theorem B908595 : Blo 908576 908595 := bstep (se 1 (by rfl) ⟨681446, by rfl⟩ : syracuseStep 908595 = 1362893) B1362893
theorem B1367363 : Blo 908576 1367363 := bstep (se 1 (by rfl) ⟨1025522, by rfl⟩ : syracuseStep 1367363 = 2051045) B2051045
theorem B908611 : Blo 908576 908611 := bstep (se 1 (by rfl) ⟨681458, by rfl⟩ : syracuseStep 908611 = 1362917) B1362917
theorem B908627 : Blo 908576 908627 := bstep (se 1 (by rfl) ⟨681470, by rfl⟩ : syracuseStep 908627 = 1362941) B1362941
theorem B1367393 : Blo 908576 1367393 := bstep (se 2 (by rfl) ⟨512772, by rfl⟩ : syracuseStep 1367393 = 1025545) B1025545
theorem B908643 : Blo 908576 908643 := bstep (se 1 (by rfl) ⟨681482, by rfl⟩ : syracuseStep 908643 = 1362965) B1362965
theorem B908659 : Blo 908576 908659 := bstep (se 1 (by rfl) ⟨681494, by rfl⟩ : syracuseStep 908659 = 1362989) B1362989
theorem B1367411 : Blo 908576 1367411 := bstep (se 1 (by rfl) ⟨1025558, by rfl⟩ : syracuseStep 1367411 = 2051117) B2051117
theorem B908675 : Blo 908576 908675 := bstep (se 1 (by rfl) ⟨681506, by rfl⟩ : syracuseStep 908675 = 1363013) B1363013
theorem B9330061 : Blo 908576 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B1367441 : Blo 908576 1367441 := bstep (se 2 (by rfl) ⟨512790, by rfl⟩ : syracuseStep 1367441 = 1025581) B1025581
theorem B908691 : Blo 908576 908691 := bstep (se 1 (by rfl) ⟨681518, by rfl⟩ : syracuseStep 908691 = 1363037) B1363037
theorem B908707 : Blo 908576 908707 := bstep (se 1 (by rfl) ⟨681530, by rfl⟩ : syracuseStep 908707 = 1363061) B1363061
theorem B3366307 : Blo 908576 3366307 := bstep (se 1 (by rfl) ⟨2524730, by rfl⟩ : syracuseStep 3366307 = 5049461) B5049461
theorem B4611491 : Blo 908576 4611491 := bstep (se 1 (by rfl) ⟨3458618, by rfl⟩ : syracuseStep 4611491 = 6917237) B6917237
theorem B1367459 : Blo 908576 1367459 := bstep (se 1 (by rfl) ⟨1025594, by rfl⟩ : syracuseStep 1367459 = 2051189) B2051189
theorem B4677041 : Blo 908576 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B908723 : Blo 908576 908723 := bstep (se 1 (by rfl) ⟨681542, by rfl⟩ : syracuseStep 908723 = 1363085) B1363085
theorem B1367489 : Blo 908576 1367489 := bstep (se 2 (by rfl) ⟨512808, by rfl⟩ : syracuseStep 1367489 = 1025617) B1025617
theorem B908739 : Blo 908576 908739 := bstep (se 1 (by rfl) ⟨681554, by rfl⟩ : syracuseStep 908739 = 1363109) B1363109
theorem B908755 : Blo 908576 908755 := bstep (se 1 (by rfl) ⟨681566, by rfl⟩ : syracuseStep 908755 = 1363133) B1363133
theorem B1367507 : Blo 908576 1367507 := bstep (se 1 (by rfl) ⟨1025630, by rfl⟩ : syracuseStep 1367507 = 2051261) B2051261
theorem B908771 : Blo 908576 908771 := bstep (se 1 (by rfl) ⟨681578, by rfl⟩ : syracuseStep 908771 = 1363157) B1363157
theorem B1367537 : Blo 908576 1367537 := bstep (se 2 (by rfl) ⟨512826, by rfl⟩ : syracuseStep 1367537 = 1025653) B1025653
theorem B908787 : Blo 908576 908787 := bstep (se 1 (by rfl) ⟨681590, by rfl⟩ : syracuseStep 908787 = 1363181) B1363181
theorem B908803 : Blo 908576 908803 := bstep (se 1 (by rfl) ⟨681602, by rfl⟩ : syracuseStep 908803 = 1363205) B1363205
theorem B1367555 : Blo 908576 1367555 := bstep (se 1 (by rfl) ⟨1025666, by rfl⟩ : syracuseStep 1367555 = 2051333) B2051333
theorem B908819 : Blo 908576 908819 := bstep (se 1 (by rfl) ⟨681614, by rfl⟩ : syracuseStep 908819 = 1363229) B1363229
theorem B1367585 : Blo 908576 1367585 := bstep (se 2 (by rfl) ⟨512844, by rfl⟩ : syracuseStep 1367585 = 1025689) B1025689
theorem B908835 : Blo 908576 908835 := bstep (se 1 (by rfl) ⟨681626, by rfl⟩ : syracuseStep 908835 = 1363253) B1363253
theorem B1728049 : Blo 908576 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B908851 : Blo 908576 908851 := bstep (se 1 (by rfl) ⟨681638, by rfl⟩ : syracuseStep 908851 = 1363277) B1363277
theorem B1367603 : Blo 908576 1367603 := bstep (se 1 (by rfl) ⟨1025702, by rfl⟩ : syracuseStep 1367603 = 2051405) B2051405
theorem B908867 : Blo 908576 908867 := bstep (se 1 (by rfl) ⟨681650, by rfl⟩ : syracuseStep 908867 = 1363301) B1363301
theorem B2186833 : Blo 908576 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B1367633 : Blo 908576 1367633 := bstep (se 2 (by rfl) ⟨512862, by rfl⟩ : syracuseStep 1367633 = 1025725) B1025725
theorem B908883 : Blo 908576 908883 := bstep (se 1 (by rfl) ⟨681662, by rfl⟩ : syracuseStep 908883 = 1363325) B1363325
theorem B908899 : Blo 908576 908899 := bstep (se 1 (by rfl) ⟨681674, by rfl⟩ : syracuseStep 908899 = 1363349) B1363349
theorem B1367651 : Blo 908576 1367651 := bstep (se 1 (by rfl) ⟨1025738, by rfl⟩ : syracuseStep 1367651 = 2051477) B2051477
theorem B908915 : Blo 908576 908915 := bstep (se 1 (by rfl) ⟨681686, by rfl⟩ : syracuseStep 908915 = 1363373) B1363373
theorem B1367681 : Blo 908576 1367681 := bstep (se 2 (by rfl) ⟨512880, by rfl⟩ : syracuseStep 1367681 = 1025761) B1025761
theorem B908931 : Blo 908576 908931 := bstep (se 1 (by rfl) ⟨681698, by rfl⟩ : syracuseStep 908931 = 1363397) B1363397
theorem B908947 : Blo 908576 908947 := bstep (se 1 (by rfl) ⟨681710, by rfl⟩ : syracuseStep 908947 = 1363421) B1363421
theorem B1367699 : Blo 908576 1367699 := bstep (se 1 (by rfl) ⟨1025774, by rfl⟩ : syracuseStep 1367699 = 2051549) B2051549
theorem B908963 : Blo 908576 908963 := bstep (se 1 (by rfl) ⟨681722, by rfl⟩ : syracuseStep 908963 = 1363445) B1363445
theorem B1367729 : Blo 908576 1367729 := bstep (se 2 (by rfl) ⟨512898, by rfl⟩ : syracuseStep 1367729 = 1025797) B1025797
theorem B908979 : Blo 908576 908979 := bstep (se 1 (by rfl) ⟨681734, by rfl⟩ : syracuseStep 908979 = 1363469) B1363469
theorem B908995 : Blo 908576 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B1367747 : Blo 908576 1367747 := bstep (se 1 (by rfl) ⟨1025810, by rfl⟩ : syracuseStep 1367747 = 2051621) B2051621
theorem B1728209 : Blo 908576 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B909011 : Blo 908576 909011 := bstep (se 1 (by rfl) ⟨681758, by rfl⟩ : syracuseStep 909011 = 1363517) B1363517
theorem B1367777 : Blo 908576 1367777 := bstep (se 2 (by rfl) ⟨512916, by rfl⟩ : syracuseStep 1367777 = 1025833) B1025833
theorem B909027 : Blo 908576 909027 := bstep (se 1 (by rfl) ⟨681770, by rfl⟩ : syracuseStep 909027 = 1363541) B1363541
theorem B909043 : Blo 908576 909043 := bstep (se 1 (by rfl) ⟨681782, by rfl⟩ : syracuseStep 909043 = 1363565) B1363565
theorem B1367795 : Blo 908576 1367795 := bstep (se 1 (by rfl) ⟨1025846, by rfl⟩ : syracuseStep 1367795 = 2051693) B2051693
theorem B909059 : Blo 908576 909059 := bstep (se 1 (by rfl) ⟨681794, by rfl⟩ : syracuseStep 909059 = 1363589) B1363589
theorem B1367825 : Blo 908576 1367825 := bstep (se 2 (by rfl) ⟨512934, by rfl⟩ : syracuseStep 1367825 = 1025869) B1025869
theorem B909075 : Blo 908576 909075 := bstep (se 1 (by rfl) ⟨681806, by rfl⟩ : syracuseStep 909075 = 1363613) B1363613
theorem B909091 : Blo 908576 909091 := bstep (se 1 (by rfl) ⟨681818, by rfl⟩ : syracuseStep 909091 = 1363637) B1363637
theorem B1367843 : Blo 908576 1367843 := bstep (se 1 (by rfl) ⟨1025882, by rfl⟩ : syracuseStep 1367843 = 2051765) B2051765
theorem B3071789 : Blo 908576 3071789 := bstep (se 3 (by rfl) ⟨575960, by rfl⟩ : syracuseStep 3071789 = 1151921) B1151921
theorem B909107 : Blo 908576 909107 := bstep (se 1 (by rfl) ⟨681830, by rfl⟩ : syracuseStep 909107 = 1363661) B1363661
theorem B1367873 : Blo 908576 1367873 := bstep (se 2 (by rfl) ⟨512952, by rfl⟩ : syracuseStep 1367873 = 1025905) B1025905
theorem B909123 : Blo 908576 909123 := bstep (se 1 (by rfl) ⟨681842, by rfl⟩ : syracuseStep 909123 = 1363685) B1363685
theorem B909139 : Blo 908576 909139 := bstep (se 1 (by rfl) ⟨681854, by rfl⟩ : syracuseStep 909139 = 1363709) B1363709
theorem B1367891 : Blo 908576 1367891 := bstep (se 1 (by rfl) ⟨1025918, by rfl⟩ : syracuseStep 1367891 = 2051837) B2051837
theorem B909155 : Blo 908576 909155 := bstep (se 1 (by rfl) ⟨681866, by rfl⟩ : syracuseStep 909155 = 1363733) B1363733
theorem B3071843 : Blo 908576 3071843 := bstep (se 1 (by rfl) ⟨2303882, by rfl⟩ : syracuseStep 3071843 = 4607765) B4607765
theorem B1367921 : Blo 908576 1367921 := bstep (se 2 (by rfl) ⟨512970, by rfl⟩ : syracuseStep 1367921 = 1025941) B1025941
theorem B909171 : Blo 908576 909171 := bstep (se 1 (by rfl) ⟨681878, by rfl⟩ : syracuseStep 909171 = 1363757) B1363757
theorem B909187 : Blo 908576 909187 := bstep (se 1 (by rfl) ⟨681890, by rfl⟩ : syracuseStep 909187 = 1363781) B1363781
theorem B1367939 : Blo 908576 1367939 := bstep (se 1 (by rfl) ⟨1025954, by rfl⟩ : syracuseStep 1367939 = 2051909) B2051909
theorem B909203 : Blo 908576 909203 := bstep (se 1 (by rfl) ⟨681902, by rfl⟩ : syracuseStep 909203 = 1363805) B1363805
theorem B1367969 : Blo 908576 1367969 := bstep (se 2 (by rfl) ⟨512988, by rfl⟩ : syracuseStep 1367969 = 1025977) B1025977
theorem B909219 : Blo 908576 909219 := bstep (se 1 (by rfl) ⟨681914, by rfl⟩ : syracuseStep 909219 = 1363829) B1363829
theorem B909235 : Blo 908576 909235 := bstep (se 1 (by rfl) ⟨681926, by rfl⟩ : syracuseStep 909235 = 1363853) B1363853
theorem B1367987 : Blo 908576 1367987 := bstep (se 1 (by rfl) ⟨1025990, by rfl⟩ : syracuseStep 1367987 = 2051981) B2051981
theorem B909251 : Blo 908576 909251 := bstep (se 1 (by rfl) ⟨681938, by rfl⟩ : syracuseStep 909251 = 1363877) B1363877
theorem B1368017 : Blo 908576 1368017 := bstep (se 2 (by rfl) ⟨513006, by rfl⟩ : syracuseStep 1368017 = 1026013) B1026013
theorem B909267 : Blo 908576 909267 := bstep (se 1 (by rfl) ⟨681950, by rfl⟩ : syracuseStep 909267 = 1363901) B1363901
theorem B909283 : Blo 908576 909283 := bstep (se 1 (by rfl) ⟨681962, by rfl⟩ : syracuseStep 909283 = 1363925) B1363925
theorem B1368035 : Blo 908576 1368035 := bstep (se 1 (by rfl) ⟨1026026, by rfl⟩ : syracuseStep 1368035 = 2052053) B2052053
theorem B909299 : Blo 908576 909299 := bstep (se 1 (by rfl) ⟨681974, by rfl⟩ : syracuseStep 909299 = 1363949) B1363949
theorem B1368065 : Blo 908576 1368065 := bstep (se 2 (by rfl) ⟨513024, by rfl⟩ : syracuseStep 1368065 = 1026049) B1026049
theorem B909315 : Blo 908576 909315 := bstep (se 1 (by rfl) ⟨681986, by rfl⟩ : syracuseStep 909315 = 1363973) B1363973
theorem B1400851 : Blo 908576 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B909331 : Blo 908576 909331 := bstep (se 1 (by rfl) ⟨681998, by rfl⟩ : syracuseStep 909331 = 1363997) B1363997
theorem B1368083 : Blo 908576 1368083 := bstep (se 1 (by rfl) ⟨1026062, by rfl⟩ : syracuseStep 1368083 = 2052125) B2052125
theorem B909347 : Blo 908576 909347 := bstep (se 1 (by rfl) ⟨682010, by rfl⟩ : syracuseStep 909347 = 1364021) B1364021
theorem B1368113 : Blo 908576 1368113 := bstep (se 2 (by rfl) ⟨513042, by rfl⟩ : syracuseStep 1368113 = 1026085) B1026085
theorem B909363 : Blo 908576 909363 := bstep (se 1 (by rfl) ⟨682022, by rfl⟩ : syracuseStep 909363 = 1364045) B1364045
theorem B1400899 : Blo 908576 1400899 := bstep (se 1 (by rfl) ⟨1050674, by rfl⟩ : syracuseStep 1400899 = 2101349) B2101349
theorem B909379 : Blo 908576 909379 := bstep (se 1 (by rfl) ⟨682034, by rfl⟩ : syracuseStep 909379 = 1364069) B1364069
theorem B1368131 : Blo 908576 1368131 := bstep (se 1 (by rfl) ⟨1026098, by rfl⟩ : syracuseStep 1368131 = 2052197) B2052197
theorem B909395 : Blo 908576 909395 := bstep (se 1 (by rfl) ⟨682046, by rfl⟩ : syracuseStep 909395 = 1364093) B1364093
theorem B1368161 : Blo 908576 1368161 := bstep (se 2 (by rfl) ⟨513060, by rfl⟩ : syracuseStep 1368161 = 1026121) B1026121
theorem B909411 : Blo 908576 909411 := bstep (se 1 (by rfl) ⟨682058, by rfl⟩ : syracuseStep 909411 = 1364117) B1364117
theorem B1728611 : Blo 908576 1728611 := bstep (se 1 (by rfl) ⟨1296458, by rfl⟩ : syracuseStep 1728611 = 2592917) B2592917
theorem B3072113 : Blo 908576 3072113 := bstep (se 2 (by rfl) ⟨1152042, by rfl⟩ : syracuseStep 3072113 = 2304085) B2304085
theorem B909427 : Blo 908576 909427 := bstep (se 1 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 909427 = 1364141) B1364141
theorem B1368179 : Blo 908576 1368179 := bstep (se 1 (by rfl) ⟨1026134, by rfl⟩ : syracuseStep 1368179 = 2052269) B2052269
theorem B909443 : Blo 908576 909443 := bstep (se 1 (by rfl) ⟨682082, by rfl⟩ : syracuseStep 909443 = 1364165) B1364165
theorem B3891341 : Blo 908576 3891341 := bstep (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) B1459253
theorem B1368209 : Blo 908576 1368209 := bstep (se 2 (by rfl) ⟨513078, by rfl⟩ : syracuseStep 1368209 = 1026157) B1026157
theorem B909459 : Blo 908576 909459 := bstep (se 1 (by rfl) ⟨682094, by rfl⟩ : syracuseStep 909459 = 1364189) B1364189
theorem B909475 : Blo 908576 909475 := bstep (se 1 (by rfl) ⟨682106, by rfl⟩ : syracuseStep 909475 = 1364213) B1364213
theorem B1368227 : Blo 908576 1368227 := bstep (se 1 (by rfl) ⟨1026170, by rfl⟩ : syracuseStep 1368227 = 2052341) B2052341
theorem B909491 : Blo 908576 909491 := bstep (se 1 (by rfl) ⟨682118, by rfl⟩ : syracuseStep 909491 = 1364237) B1364237
theorem B1368257 : Blo 908576 1368257 := bstep (se 2 (by rfl) ⟨513096, by rfl⟩ : syracuseStep 1368257 = 1026193) B1026193
theorem B909507 : Blo 908576 909507 := bstep (se 1 (by rfl) ⟨682130, by rfl⟩ : syracuseStep 909507 = 1364261) B1364261
theorem B4612301 : Blo 908576 4612301 := bstep (se 3 (by rfl) ⟨864806, by rfl⟩ : syracuseStep 4612301 = 1729613) B1729613
theorem B909523 : Blo 908576 909523 := bstep (se 1 (by rfl) ⟨682142, by rfl⟩ : syracuseStep 909523 = 1364285) B1364285
theorem B1368275 : Blo 908576 1368275 := bstep (se 1 (by rfl) ⟨1026206, by rfl⟩ : syracuseStep 1368275 = 2052413) B2052413
theorem B909539 : Blo 908576 909539 := bstep (se 1 (by rfl) ⟨682154, by rfl⟩ : syracuseStep 909539 = 1364309) B1364309
theorem B1368305 : Blo 908576 1368305 := bstep (se 2 (by rfl) ⟨513114, by rfl⟩ : syracuseStep 1368305 = 1026229) B1026229
theorem B909555 : Blo 908576 909555 := bstep (se 1 (by rfl) ⟨682166, by rfl⟩ : syracuseStep 909555 = 1364333) B1364333
theorem B909571 : Blo 908576 909571 := bstep (se 1 (by rfl) ⟨682178, by rfl⟩ : syracuseStep 909571 = 1364357) B1364357
theorem B1368323 : Blo 908576 1368323 := bstep (se 1 (by rfl) ⟨1026242, by rfl⟩ : syracuseStep 1368323 = 2052485) B2052485
theorem B909587 : Blo 908576 909587 := bstep (se 1 (by rfl) ⟨682190, by rfl⟩ : syracuseStep 909587 = 1364381) B1364381
theorem B26665237 : Blo 908576 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B1368353 : Blo 908576 1368353 := bstep (se 2 (by rfl) ⟨513132, by rfl⟩ : syracuseStep 1368353 = 1026265) B1026265
theorem B909603 : Blo 908576 909603 := bstep (se 1 (by rfl) ⟨682202, by rfl⟩ : syracuseStep 909603 = 1364405) B1364405
theorem B909619 : Blo 908576 909619 := bstep (se 1 (by rfl) ⟨682214, by rfl⟩ : syracuseStep 909619 = 1364429) B1364429
theorem B1368371 : Blo 908576 1368371 := bstep (se 1 (by rfl) ⟨1026278, by rfl⟩ : syracuseStep 1368371 = 2052557) B2052557
theorem B909635 : Blo 908576 909635 := bstep (se 1 (by rfl) ⟨682226, by rfl⟩ : syracuseStep 909635 = 1364453) B1364453
theorem B1368401 : Blo 908576 1368401 := bstep (se 2 (by rfl) ⟨513150, by rfl⟩ : syracuseStep 1368401 = 1026301) B1026301
theorem B909651 : Blo 908576 909651 := bstep (se 1 (by rfl) ⟨682238, by rfl⟩ : syracuseStep 909651 = 1364477) B1364477
theorem B909667 : Blo 908576 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B1368419 : Blo 908576 1368419 := bstep (se 1 (by rfl) ⟨1026314, by rfl⟩ : syracuseStep 1368419 = 2052629) B2052629
theorem B909683 : Blo 908576 909683 := bstep (se 1 (by rfl) ⟨682262, by rfl⟩ : syracuseStep 909683 = 1364525) B1364525
theorem B1368449 : Blo 908576 1368449 := bstep (se 2 (by rfl) ⟨513168, by rfl⟩ : syracuseStep 1368449 = 1026337) B1026337
theorem B909699 : Blo 908576 909699 := bstep (se 1 (by rfl) ⟨682274, by rfl⟩ : syracuseStep 909699 = 1364549) B1364549
theorem B909715 : Blo 908576 909715 := bstep (se 1 (by rfl) ⟨682286, by rfl⟩ : syracuseStep 909715 = 1364573) B1364573
theorem B1368467 : Blo 908576 1368467 := bstep (se 1 (by rfl) ⟨1026350, by rfl⟩ : syracuseStep 1368467 = 2052701) B2052701
theorem B909731 : Blo 908576 909731 := bstep (se 1 (by rfl) ⟨682298, by rfl⟩ : syracuseStep 909731 = 1364597) B1364597
theorem B1368497 : Blo 908576 1368497 := bstep (se 2 (by rfl) ⟨513186, by rfl⟩ : syracuseStep 1368497 = 1026373) B1026373
theorem B909747 : Blo 908576 909747 := bstep (se 1 (by rfl) ⟨682310, by rfl⟩ : syracuseStep 909747 = 1364621) B1364621
theorem B909763 : Blo 908576 909763 := bstep (se 1 (by rfl) ⟨682322, by rfl⟩ : syracuseStep 909763 = 1364645) B1364645
theorem B1368515 : Blo 908576 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B909779 : Blo 908576 909779 := bstep (se 1 (by rfl) ⟨682334, by rfl⟩ : syracuseStep 909779 = 1364669) B1364669
theorem B1368545 : Blo 908576 1368545 := bstep (se 2 (by rfl) ⟨513204, by rfl⟩ : syracuseStep 1368545 = 1026409) B1026409
theorem B909795 : Blo 908576 909795 := bstep (se 1 (by rfl) ⟨682346, by rfl⟩ : syracuseStep 909795 = 1364693) B1364693
theorem B3498481 : Blo 908576 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B909811 : Blo 908576 909811 := bstep (se 1 (by rfl) ⟨682358, by rfl⟩ : syracuseStep 909811 = 1364717) B1364717
theorem B1368563 : Blo 908576 1368563 := bstep (se 1 (by rfl) ⟨1026422, by rfl⟩ : syracuseStep 1368563 = 2052845) B2052845
theorem B909827 : Blo 908576 909827 := bstep (se 1 (by rfl) ⟨682370, by rfl⟩ : syracuseStep 909827 = 1364741) B1364741
theorem B1368593 : Blo 908576 1368593 := bstep (se 2 (by rfl) ⟨513222, by rfl⟩ : syracuseStep 1368593 = 1026445) B1026445
theorem B909843 : Blo 908576 909843 := bstep (se 1 (by rfl) ⟨682382, by rfl⟩ : syracuseStep 909843 = 1364765) B1364765
theorem B909859 : Blo 908576 909859 := bstep (se 1 (by rfl) ⟨682394, by rfl⟩ : syracuseStep 909859 = 1364789) B1364789
theorem B1368611 : Blo 908576 1368611 := bstep (se 1 (by rfl) ⟨1026458, by rfl⟩ : syracuseStep 1368611 = 2052917) B2052917
theorem B909875 : Blo 908576 909875 := bstep (se 1 (by rfl) ⟨682406, by rfl⟩ : syracuseStep 909875 = 1364813) B1364813
theorem B1368641 : Blo 908576 1368641 := bstep (se 2 (by rfl) ⟨513240, by rfl⟩ : syracuseStep 1368641 = 1026481) B1026481
theorem B909891 : Blo 908576 909891 := bstep (se 1 (by rfl) ⟨682418, by rfl⟩ : syracuseStep 909891 = 1364837) B1364837
theorem B909907 : Blo 908576 909907 := bstep (se 1 (by rfl) ⟨682430, by rfl⟩ : syracuseStep 909907 = 1364861) B1364861
theorem B1368659 : Blo 908576 1368659 := bstep (se 1 (by rfl) ⟨1026494, by rfl⟩ : syracuseStep 1368659 = 2052989) B2052989
theorem B909923 : Blo 908576 909923 := bstep (se 1 (by rfl) ⟨682442, by rfl⟩ : syracuseStep 909923 = 1364885) B1364885
theorem B1368689 : Blo 908576 1368689 := bstep (se 2 (by rfl) ⟨513258, by rfl⟩ : syracuseStep 1368689 = 1026517) B1026517
theorem B909939 : Blo 908576 909939 := bstep (se 1 (by rfl) ⟨682454, by rfl⟩ : syracuseStep 909939 = 1364909) B1364909
theorem B909955 : Blo 908576 909955 := bstep (se 1 (by rfl) ⟨682466, by rfl⟩ : syracuseStep 909955 = 1364933) B1364933
theorem B1368707 : Blo 908576 1368707 := bstep (se 1 (by rfl) ⟨1026530, by rfl⟩ : syracuseStep 1368707 = 2053061) B2053061
theorem B3072653 : Blo 908576 3072653 := bstep (se 3 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 3072653 = 1152245) B1152245
theorem B909971 : Blo 908576 909971 := bstep (se 1 (by rfl) ⟨682478, by rfl⟩ : syracuseStep 909971 = 1364957) B1364957
theorem B1368737 : Blo 908576 1368737 := bstep (se 2 (by rfl) ⟨513276, by rfl⟩ : syracuseStep 1368737 = 1026553) B1026553
theorem B909987 : Blo 908576 909987 := bstep (se 1 (by rfl) ⟨682490, by rfl⟩ : syracuseStep 909987 = 1364981) B1364981
theorem B910003 : Blo 908576 910003 := bstep (se 1 (by rfl) ⟨682502, by rfl⟩ : syracuseStep 910003 = 1365005) B1365005
theorem B1368755 : Blo 908576 1368755 := bstep (se 1 (by rfl) ⟨1026566, by rfl⟩ : syracuseStep 1368755 = 2053133) B2053133
theorem B910019 : Blo 908576 910019 := bstep (se 1 (by rfl) ⟨682514, by rfl⟩ : syracuseStep 910019 = 1365029) B1365029
theorem B3072707 : Blo 908576 3072707 := bstep (se 1 (by rfl) ⟨2304530, by rfl⟩ : syracuseStep 3072707 = 4609061) B4609061
theorem B1368785 : Blo 908576 1368785 := bstep (se 2 (by rfl) ⟨513294, by rfl⟩ : syracuseStep 1368785 = 1026589) B1026589
theorem B910035 : Blo 908576 910035 := bstep (se 1 (by rfl) ⟨682526, by rfl⟩ : syracuseStep 910035 = 1365053) B1365053
theorem B910051 : Blo 908576 910051 := bstep (se 1 (by rfl) ⟨682538, by rfl⟩ : syracuseStep 910051 = 1365077) B1365077
theorem B1368803 : Blo 908576 1368803 := bstep (se 1 (by rfl) ⟨1026602, by rfl⟩ : syracuseStep 1368803 = 2053205) B2053205
theorem B910067 : Blo 908576 910067 := bstep (se 1 (by rfl) ⟨682550, by rfl⟩ : syracuseStep 910067 = 1365101) B1365101
theorem B1368833 : Blo 908576 1368833 := bstep (se 2 (by rfl) ⟨513312, by rfl⟩ : syracuseStep 1368833 = 1026625) B1026625
theorem B910083 : Blo 908576 910083 := bstep (se 1 (by rfl) ⟨682562, by rfl⟩ : syracuseStep 910083 = 1365125) B1365125
theorem B910099 : Blo 908576 910099 := bstep (se 1 (by rfl) ⟨682574, by rfl⟩ : syracuseStep 910099 = 1365149) B1365149
theorem B1368851 : Blo 908576 1368851 := bstep (se 1 (by rfl) ⟨1026638, by rfl⟩ : syracuseStep 1368851 = 2053277) B2053277
theorem B1106723 : Blo 908576 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B910115 : Blo 908576 910115 := bstep (se 1 (by rfl) ⟨682586, by rfl⟩ : syracuseStep 910115 = 1365173) B1365173
theorem B910131 : Blo 908576 910131 := bstep (se 1 (by rfl) ⟨682598, by rfl⟩ : syracuseStep 910131 = 1365197) B1365197
theorem B910147 : Blo 908576 910147 := bstep (se 1 (by rfl) ⟨682610, by rfl⟩ : syracuseStep 910147 = 1365221) B1365221
theorem B910163 : Blo 908576 910163 := bstep (se 1 (by rfl) ⟨682622, by rfl⟩ : syracuseStep 910163 = 1365245) B1365245
theorem B910179 : Blo 908576 910179 := bstep (se 1 (by rfl) ⟨682634, by rfl⟩ : syracuseStep 910179 = 1365269) B1365269
theorem B910195 : Blo 908576 910195 := bstep (se 1 (by rfl) ⟨682646, by rfl⟩ : syracuseStep 910195 = 1365293) B1365293
theorem B910211 : Blo 908576 910211 := bstep (se 1 (by rfl) ⟨682658, by rfl⟩ : syracuseStep 910211 = 1365317) B1365317
theorem B910227 : Blo 908576 910227 := bstep (se 1 (by rfl) ⟨682670, by rfl⟩ : syracuseStep 910227 = 1365341) B1365341
theorem B910243 : Blo 908576 910243 := bstep (se 1 (by rfl) ⟨682682, by rfl⟩ : syracuseStep 910243 = 1365365) B1365365
theorem B910259 : Blo 908576 910259 := bstep (se 1 (by rfl) ⟨682694, by rfl⟩ : syracuseStep 910259 = 1365389) B1365389
theorem B910275 : Blo 908576 910275 := bstep (se 1 (by rfl) ⟨682706, by rfl⟩ : syracuseStep 910275 = 1365413) B1365413
theorem B3072977 : Blo 908576 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B910291 : Blo 908576 910291 := bstep (se 1 (by rfl) ⟨682718, by rfl⟩ : syracuseStep 910291 = 1365437) B1365437
theorem B910307 : Blo 908576 910307 := bstep (se 1 (by rfl) ⟨682730, by rfl⟩ : syracuseStep 910307 = 1365461) B1365461
theorem B1729507 : Blo 908576 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B910323 : Blo 908576 910323 := bstep (se 1 (by rfl) ⟨682742, by rfl⟩ : syracuseStep 910323 = 1365485) B1365485
theorem B910339 : Blo 908576 910339 := bstep (se 1 (by rfl) ⟨682754, by rfl⟩ : syracuseStep 910339 = 1365509) B1365509
theorem B910355 : Blo 908576 910355 := bstep (se 1 (by rfl) ⟨682766, by rfl⟩ : syracuseStep 910355 = 1365533) B1365533
theorem B910371 : Blo 908576 910371 := bstep (se 1 (by rfl) ⟨682778, by rfl⟩ : syracuseStep 910371 = 1365557) B1365557
theorem B910387 : Blo 908576 910387 := bstep (se 1 (by rfl) ⟨682790, by rfl⟩ : syracuseStep 910387 = 1365581) B1365581
theorem B910403 : Blo 908576 910403 := bstep (se 1 (by rfl) ⟨682802, by rfl⟩ : syracuseStep 910403 = 1365605) B1365605
theorem B910419 : Blo 908576 910419 := bstep (se 1 (by rfl) ⟨682814, by rfl⟩ : syracuseStep 910419 = 1365629) B1365629
theorem B910435 : Blo 908576 910435 := bstep (se 1 (by rfl) ⟨682826, by rfl⟩ : syracuseStep 910435 = 1365653) B1365653
theorem B910451 : Blo 908576 910451 := bstep (se 1 (by rfl) ⟨682838, by rfl⟩ : syracuseStep 910451 = 1365677) B1365677
theorem B910467 : Blo 908576 910467 := bstep (se 1 (by rfl) ⟨682850, by rfl⟩ : syracuseStep 910467 = 1365701) B1365701
theorem B1729667 : Blo 908576 1729667 := bstep (se 1 (by rfl) ⟨1297250, by rfl⟩ : syracuseStep 1729667 = 2594501) B2594501
theorem B910483 : Blo 908576 910483 := bstep (se 1 (by rfl) ⟨682862, by rfl⟩ : syracuseStep 910483 = 1365725) B1365725
theorem B910499 : Blo 908576 910499 := bstep (se 1 (by rfl) ⟨682874, by rfl⟩ : syracuseStep 910499 = 1365749) B1365749
theorem B910515 : Blo 908576 910515 := bstep (se 1 (by rfl) ⟨682886, by rfl⟩ : syracuseStep 910515 = 1365773) B1365773
theorem B910531 : Blo 908576 910531 := bstep (se 1 (by rfl) ⟨682898, by rfl⟩ : syracuseStep 910531 = 1365797) B1365797
theorem B910547 : Blo 908576 910547 := bstep (se 1 (by rfl) ⟨682910, by rfl⟩ : syracuseStep 910547 = 1365821) B1365821
theorem B910563 : Blo 908576 910563 := bstep (se 1 (by rfl) ⟨682922, by rfl⟩ : syracuseStep 910563 = 1365845) B1365845
theorem B910579 : Blo 908576 910579 := bstep (se 1 (by rfl) ⟨682934, by rfl⟩ : syracuseStep 910579 = 1365869) B1365869
theorem B910595 : Blo 908576 910595 := bstep (se 1 (by rfl) ⟨682946, by rfl⟩ : syracuseStep 910595 = 1365893) B1365893
theorem B910611 : Blo 908576 910611 := bstep (se 1 (by rfl) ⟨682958, by rfl⟩ : syracuseStep 910611 = 1365917) B1365917
theorem B910627 : Blo 908576 910627 := bstep (se 1 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 910627 = 1365941) B1365941
theorem B1533235 : Blo 908576 1533235 := bstep (se 1 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 1533235 = 2299853) B2299853
theorem B910643 : Blo 908576 910643 := bstep (se 1 (by rfl) ⟨682982, by rfl⟩ : syracuseStep 910643 = 1365965) B1365965
theorem B910659 : Blo 908576 910659 := bstep (se 1 (by rfl) ⟨682994, by rfl⟩ : syracuseStep 910659 = 1365989) B1365989
theorem B910675 : Blo 908576 910675 := bstep (se 1 (by rfl) ⟨683006, by rfl⟩ : syracuseStep 910675 = 1366013) B1366013
theorem B910691 : Blo 908576 910691 := bstep (se 1 (by rfl) ⟨683018, by rfl⟩ : syracuseStep 910691 = 1366037) B1366037
theorem B910707 : Blo 908576 910707 := bstep (se 1 (by rfl) ⟨683030, by rfl⟩ : syracuseStep 910707 = 1366061) B1366061
theorem B910723 : Blo 908576 910723 := bstep (se 1 (by rfl) ⟨683042, by rfl⟩ : syracuseStep 910723 = 1366085) B1366085
theorem B910739 : Blo 908576 910739 := bstep (se 1 (by rfl) ⟨683054, by rfl⟩ : syracuseStep 910739 = 1366109) B1366109
theorem B910755 : Blo 908576 910755 := bstep (se 1 (by rfl) ⟨683066, by rfl⟩ : syracuseStep 910755 = 1366133) B1366133
theorem B910771 : Blo 908576 910771 := bstep (se 1 (by rfl) ⟨683078, by rfl⟩ : syracuseStep 910771 = 1366157) B1366157
theorem B1533377 : Blo 908576 1533377 := bstep (se 2 (by rfl) ⟨575016, by rfl⟩ : syracuseStep 1533377 = 1150033) B1150033
theorem B910787 : Blo 908576 910787 := bstep (se 1 (by rfl) ⟨683090, by rfl⟩ : syracuseStep 910787 = 1366181) B1366181
theorem B910803 : Blo 908576 910803 := bstep (se 1 (by rfl) ⟨683102, by rfl⟩ : syracuseStep 910803 = 1366205) B1366205
theorem B910819 : Blo 908576 910819 := bstep (se 1 (by rfl) ⟨683114, by rfl⟩ : syracuseStep 910819 = 1366229) B1366229
theorem B3073517 : Blo 908576 3073517 := bstep (se 3 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 3073517 = 1152569) B1152569
theorem B910835 : Blo 908576 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B910851 : Blo 908576 910851 := bstep (se 1 (by rfl) ⟨683138, by rfl⟩ : syracuseStep 910851 = 1366277) B1366277
theorem B910867 : Blo 908576 910867 := bstep (se 1 (by rfl) ⟨683150, by rfl⟩ : syracuseStep 910867 = 1366301) B1366301
theorem B3073571 : Blo 908576 3073571 := bstep (se 1 (by rfl) ⟨2305178, by rfl⟩ : syracuseStep 3073571 = 4610357) B4610357
theorem B910883 : Blo 908576 910883 := bstep (se 1 (by rfl) ⟨683162, by rfl⟩ : syracuseStep 910883 = 1366325) B1366325
theorem B910899 : Blo 908576 910899 := bstep (se 1 (by rfl) ⟨683174, by rfl⟩ : syracuseStep 910899 = 1366349) B1366349
theorem B1533505 : Blo 908576 1533505 := bstep (se 2 (by rfl) ⟨575064, by rfl⟩ : syracuseStep 1533505 = 1150129) B1150129
theorem B910915 : Blo 908576 910915 := bstep (se 1 (by rfl) ⟨683186, by rfl⟩ : syracuseStep 910915 = 1366373) B1366373
theorem B910931 : Blo 908576 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B1533539 : Blo 908576 1533539 := bstep (se 1 (by rfl) ⟨1150154, by rfl⟩ : syracuseStep 1533539 = 2300309) B2300309
theorem B910947 : Blo 908576 910947 := bstep (se 1 (by rfl) ⟨683210, by rfl⟩ : syracuseStep 910947 = 1366421) B1366421
theorem B910963 : Blo 908576 910963 := bstep (se 1 (by rfl) ⟨683222, by rfl⟩ : syracuseStep 910963 = 1366445) B1366445
theorem B910979 : Blo 908576 910979 := bstep (se 1 (by rfl) ⟨683234, by rfl⟩ : syracuseStep 910979 = 1366469) B1366469
theorem B910995 : Blo 908576 910995 := bstep (se 1 (by rfl) ⟨683246, by rfl⟩ : syracuseStep 910995 = 1366493) B1366493
theorem B911011 : Blo 908576 911011 := bstep (se 1 (by rfl) ⟨683258, by rfl⟩ : syracuseStep 911011 = 1366517) B1366517
theorem B911027 : Blo 908576 911027 := bstep (se 1 (by rfl) ⟨683270, by rfl⟩ : syracuseStep 911027 = 1366541) B1366541
theorem B911043 : Blo 908576 911043 := bstep (se 1 (by rfl) ⟨683282, by rfl⟩ : syracuseStep 911043 = 1366565) B1366565
theorem B5531333 : Blo 908576 5531333 := bstep (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) B1037125
theorem B911059 : Blo 908576 911059 := bstep (se 1 (by rfl) ⟨683294, by rfl⟩ : syracuseStep 911059 = 1366589) B1366589
theorem B1533667 : Blo 908576 1533667 := bstep (se 1 (by rfl) ⟨1150250, by rfl⟩ : syracuseStep 1533667 = 2300501) B2300501
theorem B911075 : Blo 908576 911075 := bstep (se 1 (by rfl) ⟨683306, by rfl⟩ : syracuseStep 911075 = 1366613) B1366613
theorem B911091 : Blo 908576 911091 := bstep (se 1 (by rfl) ⟨683318, by rfl⟩ : syracuseStep 911091 = 1366637) B1366637
theorem B1402625 : Blo 908576 1402625 := bstep (se 2 (by rfl) ⟨525984, by rfl⟩ : syracuseStep 1402625 = 1051969) B1051969
theorem B911107 : Blo 908576 911107 := bstep (se 1 (by rfl) ⟨683330, by rfl⟩ : syracuseStep 911107 = 1366661) B1366661
theorem B4384525 : Blo 908576 4384525 := bstep (se 3 (by rfl) ⟨822098, by rfl⟩ : syracuseStep 4384525 = 1644197) B1644197
theorem B911123 : Blo 908576 911123 := bstep (se 1 (by rfl) ⟨683342, by rfl⟩ : syracuseStep 911123 = 1366685) B1366685
theorem B911139 : Blo 908576 911139 := bstep (se 1 (by rfl) ⟨683354, by rfl⟩ : syracuseStep 911139 = 1366709) B1366709
theorem B3073841 : Blo 908576 3073841 := bstep (se 2 (by rfl) ⟨1152690, by rfl⟩ : syracuseStep 3073841 = 2305381) B2305381
theorem B911155 : Blo 908576 911155 := bstep (se 1 (by rfl) ⟨683366, by rfl⟩ : syracuseStep 911155 = 1366733) B1366733
theorem B911171 : Blo 908576 911171 := bstep (se 1 (by rfl) ⟨683378, by rfl⟩ : syracuseStep 911171 = 1366757) B1366757
theorem B911187 : Blo 908576 911187 := bstep (se 1 (by rfl) ⟨683390, by rfl⟩ : syracuseStep 911187 = 1366781) B1366781
theorem B911203 : Blo 908576 911203 := bstep (se 1 (by rfl) ⟨683402, by rfl⟩ : syracuseStep 911203 = 1366805) B1366805
theorem B1533809 : Blo 908576 1533809 := bstep (se 2 (by rfl) ⟨575178, by rfl⟩ : syracuseStep 1533809 = 1150357) B1150357
theorem B911219 : Blo 908576 911219 := bstep (se 1 (by rfl) ⟨683414, by rfl⟩ : syracuseStep 911219 = 1366829) B1366829
theorem B911235 : Blo 908576 911235 := bstep (se 1 (by rfl) ⟨683426, by rfl⟩ : syracuseStep 911235 = 1366853) B1366853
theorem B911251 : Blo 908576 911251 := bstep (se 1 (by rfl) ⟨683438, by rfl⟩ : syracuseStep 911251 = 1366877) B1366877
theorem B911267 : Blo 908576 911267 := bstep (se 1 (by rfl) ⟨683450, by rfl⟩ : syracuseStep 911267 = 1366901) B1366901
theorem B911283 : Blo 908576 911283 := bstep (se 1 (by rfl) ⟨683462, by rfl⟩ : syracuseStep 911283 = 1366925) B1366925
theorem B911299 : Blo 908576 911299 := bstep (se 1 (by rfl) ⟨683474, by rfl⟩ : syracuseStep 911299 = 1366949) B1366949
theorem B911315 : Blo 908576 911315 := bstep (se 1 (by rfl) ⟨683486, by rfl⟩ : syracuseStep 911315 = 1366973) B1366973
theorem B911331 : Blo 908576 911331 := bstep (se 1 (by rfl) ⟨683498, by rfl⟩ : syracuseStep 911331 = 1366997) B1366997
theorem B1533937 : Blo 908576 1533937 := bstep (se 2 (by rfl) ⟨575226, by rfl⟩ : syracuseStep 1533937 = 1150453) B1150453
theorem B911347 : Blo 908576 911347 := bstep (se 1 (by rfl) ⟨683510, by rfl⟩ : syracuseStep 911347 = 1367021) B1367021
theorem B911363 : Blo 908576 911363 := bstep (se 1 (by rfl) ⟨683522, by rfl⟩ : syracuseStep 911363 = 1367045) B1367045
theorem B1533971 : Blo 908576 1533971 := bstep (se 1 (by rfl) ⟨1150478, by rfl⟩ : syracuseStep 1533971 = 2300957) B2300957
theorem B911379 : Blo 908576 911379 := bstep (se 1 (by rfl) ⟨683534, by rfl⟩ : syracuseStep 911379 = 1367069) B1367069
theorem B911395 : Blo 908576 911395 := bstep (se 1 (by rfl) ⟨683546, by rfl⟩ : syracuseStep 911395 = 1367093) B1367093
theorem B3237937 : Blo 908576 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B911411 : Blo 908576 911411 := bstep (se 1 (by rfl) ⟨683558, by rfl⟩ : syracuseStep 911411 = 1367117) B1367117
theorem B911427 : Blo 908576 911427 := bstep (se 1 (by rfl) ⟨683570, by rfl⟩ : syracuseStep 911427 = 1367141) B1367141
theorem B911443 : Blo 908576 911443 := bstep (se 1 (by rfl) ⟨683582, by rfl⟩ : syracuseStep 911443 = 1367165) B1367165
theorem B6908003 : Blo 908576 6908003 := bstep (se 1 (by rfl) ⟨5181002, by rfl⟩ : syracuseStep 6908003 = 10362005) B10362005
theorem B911459 : Blo 908576 911459 := bstep (se 1 (by rfl) ⟨683594, by rfl⟩ : syracuseStep 911459 = 1367189) B1367189
theorem B911475 : Blo 908576 911475 := bstep (se 1 (by rfl) ⟨683606, by rfl⟩ : syracuseStep 911475 = 1367213) B1367213
theorem B911491 : Blo 908576 911491 := bstep (se 1 (by rfl) ⟨683618, by rfl⟩ : syracuseStep 911491 = 1367237) B1367237
theorem B1534099 : Blo 908576 1534099 := bstep (se 1 (by rfl) ⟨1150574, by rfl⟩ : syracuseStep 1534099 = 2301149) B2301149
theorem B911507 : Blo 908576 911507 := bstep (se 1 (by rfl) ⟨683630, by rfl⟩ : syracuseStep 911507 = 1367261) B1367261
theorem B911523 : Blo 908576 911523 := bstep (se 1 (by rfl) ⟨683642, by rfl⟩ : syracuseStep 911523 = 1367285) B1367285
theorem B1730737 : Blo 908576 1730737 := bstep (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) B1298053
theorem B911539 : Blo 908576 911539 := bstep (se 1 (by rfl) ⟨683654, by rfl⟩ : syracuseStep 911539 = 1367309) B1367309
theorem B911555 : Blo 908576 911555 := bstep (se 1 (by rfl) ⟨683666, by rfl⟩ : syracuseStep 911555 = 1367333) B1367333
theorem B911571 : Blo 908576 911571 := bstep (se 1 (by rfl) ⟨683678, by rfl⟩ : syracuseStep 911571 = 1367357) B1367357
theorem B9824483 : Blo 908576 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B911587 : Blo 908576 911587 := bstep (se 1 (by rfl) ⟨683690, by rfl⟩ : syracuseStep 911587 = 1367381) B1367381
theorem B911603 : Blo 908576 911603 := bstep (se 1 (by rfl) ⟨683702, by rfl⟩ : syracuseStep 911603 = 1367405) B1367405
theorem B911619 : Blo 908576 911619 := bstep (se 1 (by rfl) ⟨683714, by rfl⟩ : syracuseStep 911619 = 1367429) B1367429
theorem B911635 : Blo 908576 911635 := bstep (se 1 (by rfl) ⟨683726, by rfl⟩ : syracuseStep 911635 = 1367453) B1367453
theorem B1534241 : Blo 908576 1534241 := bstep (se 2 (by rfl) ⟨575340, by rfl⟩ : syracuseStep 1534241 = 1150681) B1150681
theorem B911651 : Blo 908576 911651 := bstep (se 1 (by rfl) ⟨683738, by rfl⟩ : syracuseStep 911651 = 1367477) B1367477
theorem B911667 : Blo 908576 911667 := bstep (se 1 (by rfl) ⟨683750, by rfl⟩ : syracuseStep 911667 = 1367501) B1367501
theorem B911683 : Blo 908576 911683 := bstep (se 1 (by rfl) ⟨683762, by rfl⟩ : syracuseStep 911683 = 1367525) B1367525
theorem B3074381 : Blo 908576 3074381 := bstep (se 3 (by rfl) ⟨576446, by rfl⟩ : syracuseStep 3074381 = 1152893) B1152893
theorem B2222417 : Blo 908576 2222417 := bstep (se 2 (by rfl) ⟨833406, by rfl⟩ : syracuseStep 2222417 = 1666813) B1666813
theorem B911699 : Blo 908576 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B911715 : Blo 908576 911715 := bstep (se 1 (by rfl) ⟨683786, by rfl⟩ : syracuseStep 911715 = 1367573) B1367573
theorem B911731 : Blo 908576 911731 := bstep (se 1 (by rfl) ⟨683798, by rfl⟩ : syracuseStep 911731 = 1367597) B1367597
theorem B3074435 : Blo 908576 3074435 := bstep (se 1 (by rfl) ⟨2305826, by rfl⟩ : syracuseStep 3074435 = 4611653) B4611653
theorem B911747 : Blo 908576 911747 := bstep (se 1 (by rfl) ⟨683810, by rfl⟩ : syracuseStep 911747 = 1367621) B1367621
theorem B911763 : Blo 908576 911763 := bstep (se 1 (by rfl) ⟨683822, by rfl⟩ : syracuseStep 911763 = 1367645) B1367645
theorem B1534369 : Blo 908576 1534369 := bstep (se 2 (by rfl) ⟨575388, by rfl⟩ : syracuseStep 1534369 = 1150777) B1150777
theorem B911779 : Blo 908576 911779 := bstep (se 1 (by rfl) ⟨683834, by rfl⟩ : syracuseStep 911779 = 1367669) B1367669
theorem B911795 : Blo 908576 911795 := bstep (se 1 (by rfl) ⟨683846, by rfl⟩ : syracuseStep 911795 = 1367693) B1367693
theorem B1534403 : Blo 908576 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B911811 : Blo 908576 911811 := bstep (se 1 (by rfl) ⟨683858, by rfl⟩ : syracuseStep 911811 = 1367717) B1367717
theorem B911827 : Blo 908576 911827 := bstep (se 1 (by rfl) ⟨683870, by rfl⟩ : syracuseStep 911827 = 1367741) B1367741
theorem B911843 : Blo 908576 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B911859 : Blo 908576 911859 := bstep (se 1 (by rfl) ⟨683894, by rfl⟩ : syracuseStep 911859 = 1367789) B1367789
theorem B911875 : Blo 908576 911875 := bstep (se 1 (by rfl) ⟨683906, by rfl⟩ : syracuseStep 911875 = 1367813) B1367813
theorem B911891 : Blo 908576 911891 := bstep (se 1 (by rfl) ⟨683918, by rfl⟩ : syracuseStep 911891 = 1367837) B1367837
theorem B911907 : Blo 908576 911907 := bstep (se 1 (by rfl) ⟨683930, by rfl⟩ : syracuseStep 911907 = 1367861) B1367861
theorem B911923 : Blo 908576 911923 := bstep (se 1 (by rfl) ⟨683942, by rfl⟩ : syracuseStep 911923 = 1367885) B1367885
theorem B1534531 : Blo 908576 1534531 := bstep (se 1 (by rfl) ⟨1150898, by rfl⟩ : syracuseStep 1534531 = 2301797) B2301797
theorem B911939 : Blo 908576 911939 := bstep (se 1 (by rfl) ⟨683954, by rfl⟩ : syracuseStep 911939 = 1367909) B1367909
theorem B911955 : Blo 908576 911955 := bstep (se 1 (by rfl) ⟨683966, by rfl⟩ : syracuseStep 911955 = 1367933) B1367933
theorem B911971 : Blo 908576 911971 := bstep (se 1 (by rfl) ⟨683978, by rfl⟩ : syracuseStep 911971 = 1367957) B1367957
theorem B2910829 : Blo 908576 2910829 := bstep (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) B1091561
theorem B911987 : Blo 908576 911987 := bstep (se 1 (by rfl) ⟨683990, by rfl⟩ : syracuseStep 911987 = 1367981) B1367981
theorem B912003 : Blo 908576 912003 := bstep (se 1 (by rfl) ⟨684002, by rfl⟩ : syracuseStep 912003 = 1368005) B1368005
theorem B3074705 : Blo 908576 3074705 := bstep (se 2 (by rfl) ⟨1153014, by rfl⟩ : syracuseStep 3074705 = 2306029) B2306029
theorem B912019 : Blo 908576 912019 := bstep (se 1 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 912019 = 1368029) B1368029
theorem B912035 : Blo 908576 912035 := bstep (se 1 (by rfl) ⟨684026, by rfl⟩ : syracuseStep 912035 = 1368053) B1368053
theorem B912051 : Blo 908576 912051 := bstep (se 1 (by rfl) ⟨684038, by rfl⟩ : syracuseStep 912051 = 1368077) B1368077
theorem B912067 : Blo 908576 912067 := bstep (se 1 (by rfl) ⟨684050, by rfl⟩ : syracuseStep 912067 = 1368101) B1368101
theorem B1534673 : Blo 908576 1534673 := bstep (se 2 (by rfl) ⟨575502, by rfl⟩ : syracuseStep 1534673 = 1151005) B1151005
theorem B912083 : Blo 908576 912083 := bstep (se 1 (by rfl) ⟨684062, by rfl⟩ : syracuseStep 912083 = 1368125) B1368125
theorem B912099 : Blo 908576 912099 := bstep (se 1 (by rfl) ⟨684074, by rfl⟩ : syracuseStep 912099 = 1368149) B1368149
theorem B912115 : Blo 908576 912115 := bstep (se 1 (by rfl) ⟨684086, by rfl⟩ : syracuseStep 912115 = 1368173) B1368173
theorem B912131 : Blo 908576 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B912147 : Blo 908576 912147 := bstep (se 1 (by rfl) ⟨684110, by rfl⟩ : syracuseStep 912147 = 1368221) B1368221
theorem B912163 : Blo 908576 912163 := bstep (se 1 (by rfl) ⟨684122, by rfl⟩ : syracuseStep 912163 = 1368245) B1368245
theorem B912179 : Blo 908576 912179 := bstep (se 1 (by rfl) ⟨684134, by rfl⟩ : syracuseStep 912179 = 1368269) B1368269
theorem B912195 : Blo 908576 912195 := bstep (se 1 (by rfl) ⟨684146, by rfl⟩ : syracuseStep 912195 = 1368293) B1368293
theorem B1534801 : Blo 908576 1534801 := bstep (se 2 (by rfl) ⟨575550, by rfl⟩ : syracuseStep 1534801 = 1151101) B1151101
theorem B912211 : Blo 908576 912211 := bstep (se 1 (by rfl) ⟨684158, by rfl⟩ : syracuseStep 912211 = 1368317) B1368317
theorem B912227 : Blo 908576 912227 := bstep (se 1 (by rfl) ⟨684170, by rfl⟩ : syracuseStep 912227 = 1368341) B1368341
theorem B1534835 : Blo 908576 1534835 := bstep (se 1 (by rfl) ⟨1151126, by rfl⟩ : syracuseStep 1534835 = 2302253) B2302253
theorem B912243 : Blo 908576 912243 := bstep (se 1 (by rfl) ⟨684182, by rfl⟩ : syracuseStep 912243 = 1368365) B1368365
theorem B912259 : Blo 908576 912259 := bstep (se 1 (by rfl) ⟨684194, by rfl⟩ : syracuseStep 912259 = 1368389) B1368389
theorem B912275 : Blo 908576 912275 := bstep (se 1 (by rfl) ⟨684206, by rfl⟩ : syracuseStep 912275 = 1368413) B1368413
theorem B912291 : Blo 908576 912291 := bstep (se 1 (by rfl) ⟨684218, by rfl⟩ : syracuseStep 912291 = 1368437) B1368437
theorem B912307 : Blo 908576 912307 := bstep (se 1 (by rfl) ⟨684230, by rfl⟩ : syracuseStep 912307 = 1368461) B1368461
theorem B912323 : Blo 908576 912323 := bstep (se 1 (by rfl) ⟨684242, by rfl⟩ : syracuseStep 912323 = 1368485) B1368485
theorem B912339 : Blo 908576 912339 := bstep (se 1 (by rfl) ⟨684254, by rfl⟩ : syracuseStep 912339 = 1368509) B1368509
theorem B912355 : Blo 908576 912355 := bstep (se 1 (by rfl) ⟨684266, by rfl⟩ : syracuseStep 912355 = 1368533) B1368533
theorem B1534963 : Blo 908576 1534963 := bstep (se 1 (by rfl) ⟨1151222, by rfl⟩ : syracuseStep 1534963 = 2302445) B2302445
theorem B912371 : Blo 908576 912371 := bstep (se 1 (by rfl) ⟨684278, by rfl⟩ : syracuseStep 912371 = 1368557) B1368557
theorem B912387 : Blo 908576 912387 := bstep (se 1 (by rfl) ⟨684290, by rfl⟩ : syracuseStep 912387 = 1368581) B1368581
theorem B912403 : Blo 908576 912403 := bstep (se 1 (by rfl) ⟨684302, by rfl⟩ : syracuseStep 912403 = 1368605) B1368605
theorem B912419 : Blo 908576 912419 := bstep (se 1 (by rfl) ⟨684314, by rfl⟩ : syracuseStep 912419 = 1368629) B1368629
theorem B4615217 : Blo 908576 4615217 := bstep (se 2 (by rfl) ⟨1730706, by rfl⟩ : syracuseStep 4615217 = 3461413) B3461413
theorem B912435 : Blo 908576 912435 := bstep (se 1 (by rfl) ⟨684326, by rfl⟩ : syracuseStep 912435 = 1368653) B1368653
theorem B912451 : Blo 908576 912451 := bstep (se 1 (by rfl) ⟨684338, by rfl⟩ : syracuseStep 912451 = 1368677) B1368677
theorem B912467 : Blo 908576 912467 := bstep (se 1 (by rfl) ⟨684350, by rfl⟩ : syracuseStep 912467 = 1368701) B1368701
theorem B912483 : Blo 908576 912483 := bstep (se 1 (by rfl) ⟨684362, by rfl⟩ : syracuseStep 912483 = 1368725) B1368725
theorem B912499 : Blo 908576 912499 := bstep (se 1 (by rfl) ⟨684374, by rfl⟩ : syracuseStep 912499 = 1368749) B1368749
theorem B1535105 : Blo 908576 1535105 := bstep (se 2 (by rfl) ⟨575664, by rfl⟩ : syracuseStep 1535105 = 1151329) B1151329
theorem B912515 : Blo 908576 912515 := bstep (se 1 (by rfl) ⟨684386, by rfl⟩ : syracuseStep 912515 = 1368773) B1368773
theorem B912531 : Blo 908576 912531 := bstep (se 1 (by rfl) ⟨684398, by rfl⟩ : syracuseStep 912531 = 1368797) B1368797
theorem B912547 : Blo 908576 912547 := bstep (se 1 (by rfl) ⟨684410, by rfl⟩ : syracuseStep 912547 = 1368821) B1368821
theorem B3075245 : Blo 908576 3075245 := bstep (se 3 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 3075245 = 1153217) B1153217
theorem B912563 : Blo 908576 912563 := bstep (se 1 (by rfl) ⟨684422, by rfl⟩ : syracuseStep 912563 = 1368845) B1368845
theorem B1731793 : Blo 908576 1731793 := bstep (se 2 (by rfl) ⟨649422, by rfl⟩ : syracuseStep 1731793 = 1298845) B1298845
theorem B3075299 : Blo 908576 3075299 := bstep (se 1 (by rfl) ⟨2306474, by rfl⟩ : syracuseStep 3075299 = 4612949) B4612949
theorem B1535233 : Blo 908576 1535233 := bstep (se 2 (by rfl) ⟨575712, by rfl⟩ : syracuseStep 1535233 = 1151425) B1151425
theorem B1535267 : Blo 908576 1535267 := bstep (se 1 (by rfl) ⟨1151450, by rfl⟩ : syracuseStep 1535267 = 2302901) B2302901
theorem B1535395 : Blo 908576 1535395 := bstep (se 1 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 1535395 = 2303093) B2303093
theorem B3075569 : Blo 908576 3075569 := bstep (se 2 (by rfl) ⟨1153338, by rfl⟩ : syracuseStep 3075569 = 2306677) B2306677
theorem B2190851 : Blo 908576 2190851 := bstep (se 1 (by rfl) ⟨1643138, by rfl⟩ : syracuseStep 2190851 = 3286277) B3286277
theorem B1535537 : Blo 908576 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B1732195 : Blo 908576 1732195 := bstep (se 1 (by rfl) ⟨1299146, by rfl⟩ : syracuseStep 1732195 = 2598293) B2598293
theorem B1732241 : Blo 908576 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B5828273 : Blo 908576 5828273 := bstep (se 2 (by rfl) ⟨2185602, by rfl⟩ : syracuseStep 5828273 = 4371205) B4371205
theorem B1535665 : Blo 908576 1535665 := bstep (se 2 (by rfl) ⟨575874, by rfl⟩ : syracuseStep 1535665 = 1151749) B1151749
theorem B1535699 : Blo 908576 1535699 := bstep (se 1 (by rfl) ⟨1151774, by rfl⟩ : syracuseStep 1535699 = 2303549) B2303549
theorem B1535827 : Blo 908576 1535827 := bstep (se 1 (by rfl) ⟨1151870, by rfl⟩ : syracuseStep 1535827 = 2303741) B2303741
theorem B22146929 : Blo 908576 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B1535969 : Blo 908576 1535969 := bstep (se 2 (by rfl) ⟨575988, by rfl⟩ : syracuseStep 1535969 = 1151977) B1151977
theorem B3076109 : Blo 908576 3076109 := bstep (se 3 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 3076109 = 1153541) B1153541
theorem B3076163 : Blo 908576 3076163 := bstep (se 1 (by rfl) ⟨2307122, by rfl⟩ : syracuseStep 3076163 = 4614245) B4614245
theorem B1536097 : Blo 908576 1536097 := bstep (se 2 (by rfl) ⟨576036, by rfl⟩ : syracuseStep 1536097 = 1152073) B1152073
theorem B1536131 : Blo 908576 1536131 := bstep (se 1 (by rfl) ⟨1152098, by rfl⟩ : syracuseStep 1536131 = 2304197) B2304197
theorem B1405153 : Blo 908576 1405153 := bstep (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) B1053865
theorem B1536259 : Blo 908576 1536259 := bstep (se 1 (by rfl) ⟨1152194, by rfl⟩ : syracuseStep 1536259 = 2304389) B2304389
theorem B2912561 : Blo 908576 2912561 := bstep (se 2 (by rfl) ⟨1092210, by rfl⟩ : syracuseStep 2912561 = 2184421) B2184421
theorem B3076433 : Blo 908576 3076433 := bstep (se 2 (by rfl) ⟨1153662, by rfl⟩ : syracuseStep 3076433 = 2307325) B2307325
theorem B1536401 : Blo 908576 1536401 := bstep (se 2 (by rfl) ⟨576150, by rfl⟩ : syracuseStep 1536401 = 1152301) B1152301
theorem B3895715 : Blo 908576 3895715 := bstep (se 1 (by rfl) ⟨2921786, by rfl⟩ : syracuseStep 3895715 = 5843573) B5843573
theorem B4616675 : Blo 908576 4616675 := bstep (se 1 (by rfl) ⟨3462506, by rfl⟩ : syracuseStep 4616675 = 6925013) B6925013
theorem B1536529 : Blo 908576 1536529 := bstep (se 2 (by rfl) ⟨576198, by rfl⟩ : syracuseStep 1536529 = 1152397) B1152397
theorem B1536563 : Blo 908576 1536563 := bstep (se 1 (by rfl) ⟨1152422, by rfl⟩ : syracuseStep 1536563 = 2304845) B2304845
theorem B2191985 : Blo 908576 2191985 := bstep (se 2 (by rfl) ⟨821994, by rfl⟩ : syracuseStep 2191985 = 1643989) B1643989
theorem B1536691 : Blo 908576 1536691 := bstep (se 1 (by rfl) ⟨1152518, by rfl⟩ : syracuseStep 1536691 = 2305037) B2305037
theorem B5829347 : Blo 908576 5829347 := bstep (se 1 (by rfl) ⟨4372010, by rfl⟩ : syracuseStep 5829347 = 8744021) B8744021
theorem B17953589 : Blo 908576 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B1536833 : Blo 908576 1536833 := bstep (se 2 (by rfl) ⟨576312, by rfl⟩ : syracuseStep 1536833 = 1152625) B1152625
theorem B4911941 : Blo 908576 4911941 := bstep (se 4 (by rfl) ⟨460494, by rfl⟩ : syracuseStep 4911941 = 920989) B920989
theorem B3076973 : Blo 908576 3076973 := bstep (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) B1153865
theorem B2913187 : Blo 908576 2913187 := bstep (se 1 (by rfl) ⟨2184890, by rfl⟩ : syracuseStep 2913187 = 4369781) B4369781
theorem B3077027 : Blo 908576 3077027 := bstep (se 1 (by rfl) ⟨2307770, by rfl⟩ : syracuseStep 3077027 = 4615541) B4615541
theorem B1536961 : Blo 908576 1536961 := bstep (se 2 (by rfl) ⟨576360, by rfl⟩ : syracuseStep 1536961 = 1152721) B1152721
theorem B1536995 : Blo 908576 1536995 := bstep (se 1 (by rfl) ⟨1152746, by rfl⟩ : syracuseStep 1536995 = 2305493) B2305493
theorem B1537123 : Blo 908576 1537123 := bstep (se 1 (by rfl) ⟨1152842, by rfl⟩ : syracuseStep 1537123 = 2305685) B2305685
theorem B3077297 : Blo 908576 3077297 := bstep (se 2 (by rfl) ⟨1153986, by rfl⟩ : syracuseStep 3077297 = 2307973) B2307973
theorem B1537265 : Blo 908576 1537265 := bstep (se 2 (by rfl) ⟨576474, by rfl⟩ : syracuseStep 1537265 = 1152949) B1152949
theorem B3110147 : Blo 908576 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B4617485 : Blo 908576 4617485 := bstep (se 3 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 4617485 = 1731557) B1731557
theorem B1537393 : Blo 908576 1537393 := bstep (se 2 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 1537393 = 1153045) B1153045
theorem B1537427 : Blo 908576 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B8746481 : Blo 908576 8746481 := bstep (se 2 (by rfl) ⟨3279930, by rfl⟩ : syracuseStep 8746481 = 6559861) B6559861
theorem B1537555 : Blo 908576 1537555 := bstep (se 1 (by rfl) ⟨1153166, by rfl⟩ : syracuseStep 1537555 = 2306333) B2306333
theorem B4159117 : Blo 908576 4159117 := bstep (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) B1559669
theorem B1537697 : Blo 908576 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B3077837 : Blo 908576 3077837 := bstep (se 3 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 3077837 = 1154189) B1154189
theorem B3077891 : Blo 908576 3077891 := bstep (se 1 (by rfl) ⟨2308418, by rfl⟩ : syracuseStep 3077891 = 4616837) B4616837
theorem B1537825 : Blo 908576 1537825 := bstep (se 2 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 1537825 = 1153369) B1153369
theorem B1537859 : Blo 908576 1537859 := bstep (se 1 (by rfl) ⟨1153394, by rfl⟩ : syracuseStep 1537859 = 2306789) B2306789
theorem B10385333 : Blo 908576 10385333 := bstep (se 5 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 10385333 = 973625) B973625
theorem B1537987 : Blo 908576 1537987 := bstep (se 1 (by rfl) ⟨1153490, by rfl⟩ : syracuseStep 1537987 = 2306981) B2306981
theorem B3078161 : Blo 908576 3078161 := bstep (se 2 (by rfl) ⟨1154310, by rfl⟩ : syracuseStep 3078161 = 2308621) B2308621
theorem B1538129 : Blo 908576 1538129 := bstep (se 2 (by rfl) ⟨576798, by rfl⟩ : syracuseStep 1538129 = 1153597) B1153597
theorem B96073813 : Blo 908576 96073813 := bstep (se 8 (by rfl) ⟨562932, by rfl⟩ : syracuseStep 96073813 = 1125865) B1125865
theorem B2914417 : Blo 908576 2914417 := bstep (se 2 (by rfl) ⟨1092906, by rfl⟩ : syracuseStep 2914417 = 2185813) B2185813
theorem B1538257 : Blo 908576 1538257 := bstep (se 2 (by rfl) ⟨576846, by rfl⟩ : syracuseStep 1538257 = 1153693) B1153693
theorem B1538291 : Blo 908576 1538291 := bstep (se 1 (by rfl) ⟨1153718, by rfl⟩ : syracuseStep 1538291 = 2307437) B2307437
theorem B3897713 : Blo 908576 3897713 := bstep (se 2 (by rfl) ⟨1461642, by rfl⟩ : syracuseStep 3897713 = 2923285) B2923285
theorem B1538419 : Blo 908576 1538419 := bstep (se 1 (by rfl) ⟨1153814, by rfl⟩ : syracuseStep 1538419 = 2307629) B2307629
theorem B1538561 : Blo 908576 1538561 := bstep (se 2 (by rfl) ⟨576960, by rfl⟩ : syracuseStep 1538561 = 1153921) B1153921
theorem B3078701 : Blo 908576 3078701 := bstep (se 3 (by rfl) ⟨577256, by rfl⟩ : syracuseStep 3078701 = 1154513) B1154513
theorem B3078755 : Blo 908576 3078755 := bstep (se 1 (by rfl) ⟨2309066, by rfl⟩ : syracuseStep 3078755 = 4618133) B4618133
theorem B1538689 : Blo 908576 1538689 := bstep (se 2 (by rfl) ⟨577008, by rfl⟩ : syracuseStep 1538689 = 1154017) B1154017
theorem B1538723 : Blo 908576 1538723 := bstep (se 1 (by rfl) ⟨1154042, by rfl⟩ : syracuseStep 1538723 = 2308085) B2308085
theorem B2915021 : Blo 908576 2915021 := bstep (se 3 (by rfl) ⟨546566, by rfl⟩ : syracuseStep 2915021 = 1093133) B1093133
theorem B3275491 : Blo 908576 3275491 := bstep (se 1 (by rfl) ⟨2456618, by rfl⟩ : syracuseStep 3275491 = 4913237) B4913237
theorem B2587427 : Blo 908576 2587427 := bstep (se 1 (by rfl) ⟨1940570, by rfl⟩ : syracuseStep 2587427 = 3881141) B3881141
theorem B1538851 : Blo 908576 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B3079025 : Blo 908576 3079025 := bstep (se 2 (by rfl) ⟨1154634, by rfl⟩ : syracuseStep 3079025 = 2309269) B2309269
theorem B1538993 : Blo 908576 1538993 := bstep (se 2 (by rfl) ⟨577122, by rfl⟩ : syracuseStep 1538993 = 1154245) B1154245
theorem B1539121 : Blo 908576 1539121 := bstep (se 2 (by rfl) ⟨577170, by rfl⟩ : syracuseStep 1539121 = 1154341) B1154341
theorem B1539155 : Blo 908576 1539155 := bstep (se 1 (by rfl) ⟨1154366, by rfl⟩ : syracuseStep 1539155 = 2308733) B2308733
theorem B3275939 : Blo 908576 3275939 := bstep (se 1 (by rfl) ⟨2456954, by rfl⟩ : syracuseStep 3275939 = 4913909) B4913909
theorem B1539283 : Blo 908576 1539283 := bstep (se 1 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 1539283 = 2308925) B2308925
theorem B3276067 : Blo 908576 3276067 := bstep (se 1 (by rfl) ⟨2457050, by rfl⟩ : syracuseStep 3276067 = 4914101) B4914101
theorem B6913349 : Blo 908576 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B1539425 : Blo 908576 1539425 := bstep (se 2 (by rfl) ⟨577284, by rfl⟩ : syracuseStep 1539425 = 1154569) B1154569
theorem B3079565 : Blo 908576 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B3079619 : Blo 908576 3079619 := bstep (se 1 (by rfl) ⟨2309714, by rfl⟩ : syracuseStep 3079619 = 4619429) B4619429
theorem B1539553 : Blo 908576 1539553 := bstep (se 2 (by rfl) ⟨577332, by rfl⟩ : syracuseStep 1539553 = 1154665) B1154665
theorem B1539587 : Blo 908576 1539587 := bstep (se 1 (by rfl) ⟨1154690, by rfl⟩ : syracuseStep 1539587 = 2309381) B2309381
theorem B2588269 : Blo 908576 2588269 := bstep (se 3 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 2588269 = 970601) B970601
theorem B1539715 : Blo 908576 1539715 := bstep (se 1 (by rfl) ⟨1154786, by rfl⟩ : syracuseStep 1539715 = 2309573) B2309573
theorem B3079889 : Blo 908576 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B2588429 : Blo 908576 2588429 := bstep (se 3 (by rfl) ⟨485330, by rfl⟩ : syracuseStep 2588429 = 970661) B970661
theorem B1539857 : Blo 908576 1539857 := bstep (se 2 (by rfl) ⟨577446, by rfl⟩ : syracuseStep 1539857 = 1154893) B1154893
theorem B7765901 : Blo 908576 7765901 := bstep (se 3 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 7765901 = 2912213) B2912213
theorem B2588611 : Blo 908576 2588611 := bstep (se 1 (by rfl) ⟨1941458, by rfl⟩ : syracuseStep 2588611 = 3882917) B3882917
theorem B1867801 : Blo 908576 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B3276875 : Blo 908576 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B1867865 : Blo 908576 1867865 := bstep (se 2 (by rfl) ⟨700449, by rfl⟩ : syracuseStep 1867865 = 1400899) B1400899
theorem B7897189 : Blo 908576 7897189 := bstep (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) B1480723
theorem B17268997 : Blo 908576 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B6914321 : Blo 908576 6914321 := bstep (se 2 (by rfl) ⟨2592870, by rfl⟩ : syracuseStep 6914321 = 5185741) B5185741
theorem B35553649 : Blo 908576 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B5178725 : Blo 908576 5178725 := bstep (se 4 (by rfl) ⟨485505, by rfl⟩ : syracuseStep 5178725 = 971011) B971011
theorem B2917853 : Blo 908576 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B1476311 : Blo 908576 1476311 := bstep (se 1 (by rfl) ⟨1107233, by rfl⟩ : syracuseStep 1476311 = 2214467) B2214467
theorem B5179409 : Blo 908576 5179409 := bstep (se 2 (by rfl) ⟨1942278, by rfl⟩ : syracuseStep 5179409 = 3884557) B3884557
theorem B15763531 : Blo 908576 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B2951261 : Blo 908576 2951261 := bstep (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) B1106723
theorem B1640587 : Blo 908576 1640587 := bstep (se 1 (by rfl) ⟨1230440, by rfl⟩ : syracuseStep 1640587 = 2460881) B2460881
theorem B2459927 : Blo 908576 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B2918749 : Blo 908576 2918749 := bstep (se 3 (by rfl) ⟨547265, by rfl⟩ : syracuseStep 2918749 = 1094531) B1094531
theorem B6556261 : Blo 908576 6556261 := bstep (se 4 (by rfl) ⟨614649, by rfl⟩ : syracuseStep 6556261 = 1229299) B1229299
theorem B5835395 : Blo 908576 5835395 := bstep (se 1 (by rfl) ⟨4376546, by rfl⟩ : syracuseStep 5835395 = 8753093) B8753093
theorem B1051499 : Blo 908576 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B6556747 : Blo 908576 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B1478027 : Blo 908576 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B1641971 : Blo 908576 1641971 := bstep (se 1 (by rfl) ⟨1231478, by rfl⟩ : syracuseStep 1641971 = 2462957) B2462957
theorem B1642007 : Blo 908576 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B1150615 : Blo 908576 1150615 := bstep (se 1 (by rfl) ⟨862961, by rfl⟩ : syracuseStep 1150615 = 1725923) B1725923
theorem B2592587 : Blo 908576 2592587 := bstep (se 1 (by rfl) ⟨1944440, by rfl⟩ : syracuseStep 2592587 = 3888881) B3888881
theorem B2461657 : Blo 908576 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B6918209 : Blo 908576 6918209 := bstep (se 2 (by rfl) ⟨2594328, by rfl⟩ : syracuseStep 6918209 = 5188657) B5188657
theorem B2592985 : Blo 908576 2592985 := bstep (se 2 (by rfl) ⟨972369, by rfl⟩ : syracuseStep 2592985 = 1944739) B1944739
theorem B1151435 : Blo 908576 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B14750221 : Blo 908576 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B21041795 : Blo 908576 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B9966341 : Blo 908576 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B3118027 : Blo 908576 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B1152139 : Blo 908576 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B3282065 : Blo 908576 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B5182643 : Blo 908576 5182643 := bstep (se 1 (by rfl) ⟨3886982, by rfl⟩ : syracuseStep 5182643 = 7773965) B7773965
theorem B1152407 : Blo 908576 1152407 := bstep (se 1 (by rfl) ⟨864305, by rfl⟩ : syracuseStep 1152407 = 1728611) B1728611
theorem B2594227 : Blo 908576 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B923243 : Blo 908576 923243 := bstep (se 1 (by rfl) ⟨692432, by rfl⟩ : syracuseStep 923243 = 1384865) B1384865
theorem B33265349 : Blo 908576 33265349 := bstep (se 4 (by rfl) ⟨3118626, by rfl⟩ : syracuseStep 33265349 = 6237253) B6237253
theorem B1644313 : Blo 908576 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B6920153 : Blo 908576 6920153 := bstep (se 2 (by rfl) ⟨2595057, by rfl⟩ : syracuseStep 6920153 = 5190115) B5190115
theorem B1972225 : Blo 908576 1972225 := bstep (se 2 (by rfl) ⟨739584, by rfl⟩ : syracuseStep 1972225 = 1479169) B1479169
theorem B1153111 : Blo 908576 1153111 := bstep (se 1 (by rfl) ⟨864833, by rfl⟩ : syracuseStep 1153111 = 1729667) B1729667
theorem B1316953 : Blo 908576 1316953 := bstep (se 2 (by rfl) ⟨493857, by rfl⟩ : syracuseStep 1316953 = 987715) B987715
theorem B1022251 : Blo 908576 1022251 := bstep (se 1 (by rfl) ⟨766688, by rfl⟩ : syracuseStep 1022251 = 1533377) B1533377
theorem B1022359 : Blo 908576 1022359 := bstep (se 1 (by rfl) ⟨766769, by rfl⟩ : syracuseStep 1022359 = 1533539) B1533539
theorem B2300339 : Blo 908576 2300339 := bstep (se 1 (by rfl) ⟨1725254, by rfl⟩ : syracuseStep 2300339 = 3450509) B3450509
theorem B3283507 : Blo 908576 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B1022539 : Blo 908576 1022539 := bstep (se 1 (by rfl) ⟨766904, by rfl⟩ : syracuseStep 1022539 = 1533809) B1533809
theorem B5184101 : Blo 908576 5184101 := bstep (se 4 (by rfl) ⟨486009, by rfl⟩ : syracuseStep 5184101 = 972019) B972019
theorem B1022647 : Blo 908576 1022647 := bstep (se 1 (by rfl) ⟨766985, by rfl⟩ : syracuseStep 1022647 = 1533971) B1533971
theorem B2300633 : Blo 908576 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B2464577 : Blo 908576 2464577 := bstep (se 2 (by rfl) ⟨924216, by rfl⟩ : syracuseStep 2464577 = 1848433) B1848433
theorem B1022827 : Blo 908576 1022827 := bstep (se 1 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 1022827 = 1534241) B1534241
theorem B1022935 : Blo 908576 1022935 := bstep (se 1 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 1022935 = 1534403) B1534403
theorem B5184557 : Blo 908576 5184557 := bstep (se 3 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 5184557 = 1944209) B1944209
theorem B1973335 : Blo 908576 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B1023115 : Blo 908576 1023115 := bstep (se 1 (by rfl) ⟨767336, by rfl⟩ : syracuseStep 1023115 = 1534673) B1534673
theorem B9837719 : Blo 908576 9837719 := bstep (se 1 (by rfl) ⟨7378289, by rfl⟩ : syracuseStep 9837719 = 14756579) B14756579
theorem B1023223 : Blo 908576 1023223 := bstep (se 1 (by rfl) ⟨767417, by rfl⟩ : syracuseStep 1023223 = 1534835) B1534835
theorem B1842497 : Blo 908576 1842497 := bstep (se 2 (by rfl) ⟨690936, by rfl⟩ : syracuseStep 1842497 = 1381873) B1381873
theorem B925003 : Blo 908576 925003 := bstep (se 1 (by rfl) ⟨693752, by rfl⟩ : syracuseStep 925003 = 1387505) B1387505
theorem B1023403 : Blo 908576 1023403 := bstep (se 1 (by rfl) ⟨767552, by rfl⟩ : syracuseStep 1023403 = 1535105) B1535105
theorem B1023511 : Blo 908576 1023511 := bstep (se 1 (by rfl) ⟨767633, by rfl⟩ : syracuseStep 1023511 = 1535267) B1535267
theorem B4496941 : Blo 908576 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B2956979 : Blo 908576 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B1941185 : Blo 908576 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B1023691 : Blo 908576 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B5185241 : Blo 908576 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B1154827 : Blo 908576 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B1023799 : Blo 908576 1023799 := bstep (se 1 (by rfl) ⟨767849, by rfl⟩ : syracuseStep 1023799 = 1535699) B1535699
theorem B1023979 : Blo 908576 1023979 := bstep (se 1 (by rfl) ⟨767984, by rfl⟩ : syracuseStep 1023979 = 1535969) B1535969
theorem B1024087 : Blo 908576 1024087 := bstep (se 1 (by rfl) ⟨768065, by rfl⟩ : syracuseStep 1024087 = 1536131) B1536131
theorem B128098417 : Blo 908576 128098417 := bstep (se 2 (by rfl) ⟨48036906, by rfl⟩ : syracuseStep 128098417 = 96073813) B96073813
theorem B1941707 : Blo 908576 1941707 := bstep (se 1 (by rfl) ⟨1456280, by rfl⟩ : syracuseStep 1941707 = 2912561) B2912561
theorem B1024267 : Blo 908576 1024267 := bstep (se 1 (by rfl) ⟨768200, by rfl⟩ : syracuseStep 1024267 = 1536401) B1536401
theorem B2597143 : Blo 908576 2597143 := bstep (se 1 (by rfl) ⟨1947857, by rfl⟩ : syracuseStep 2597143 = 3895715) B3895715
theorem B2302283 : Blo 908576 2302283 := bstep (se 1 (by rfl) ⟨1726712, by rfl⟩ : syracuseStep 2302283 = 3453425) B3453425
theorem B1024375 : Blo 908576 1024375 := bstep (se 1 (by rfl) ⟨768281, by rfl⟩ : syracuseStep 1024375 = 1536563) B1536563
theorem B1974721 : Blo 908576 1974721 := bstep (se 2 (by rfl) ⟨740520, by rfl⟩ : syracuseStep 1974721 = 1481041) B1481041
theorem B8004113 : Blo 908576 8004113 := bstep (se 2 (by rfl) ⟨3001542, by rfl⟩ : syracuseStep 8004113 = 6003085) B6003085
theorem B11969059 : Blo 908576 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B1024555 : Blo 908576 1024555 := bstep (se 1 (by rfl) ⟨768416, by rfl⟩ : syracuseStep 1024555 = 1536833) B1536833
theorem B1024663 : Blo 908576 1024663 := bstep (se 1 (by rfl) ⟨768497, by rfl⟩ : syracuseStep 1024663 = 1536995) B1536995
theorem B1024843 : Blo 908576 1024843 := bstep (se 1 (by rfl) ⟨768632, by rfl⟩ : syracuseStep 1024843 = 1537265) B1537265
theorem B2073431 : Blo 908576 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B13116259 : Blo 908576 13116259 := bstep (se 1 (by rfl) ⟨9837194, by rfl⟩ : syracuseStep 13116259 = 19674389) B19674389
theorem B1024951 : Blo 908576 1024951 := bstep (se 1 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 1024951 = 1537427) B1537427
theorem B4367321 : Blo 908576 4367321 := bstep (se 2 (by rfl) ⟨1637745, by rfl⟩ : syracuseStep 4367321 = 3275491) B3275491
theorem B1025131 : Blo 908576 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B1025239 : Blo 908576 1025239 := bstep (se 1 (by rfl) ⟨768929, by rfl⟩ : syracuseStep 1025239 = 1537859) B1537859
theorem B1385687 : Blo 908576 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B2303255 : Blo 908576 2303255 := bstep (se 1 (by rfl) ⟨1727441, by rfl⟩ : syracuseStep 2303255 = 3454883) B3454883
theorem B6923555 : Blo 908576 6923555 := bstep (se 1 (by rfl) ⟨5192666, by rfl⟩ : syracuseStep 6923555 = 10385333) B10385333
theorem B1025419 : Blo 908576 1025419 := bstep (se 1 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 1025419 = 1538129) B1538129
theorem B1942937 : Blo 908576 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B1025527 : Blo 908576 1025527 := bstep (se 1 (by rfl) ⟨769145, by rfl⟩ : syracuseStep 1025527 = 1538291) B1538291
theorem B15738443 : Blo 908576 15738443 := bstep (se 1 (by rfl) ⟨11803832, by rfl⟩ : syracuseStep 15738443 = 23607665) B23607665
theorem B2598475 : Blo 908576 2598475 := bstep (se 1 (by rfl) ⟨1948856, by rfl⟩ : syracuseStep 2598475 = 3897713) B3897713
theorem B1025707 : Blo 908576 1025707 := bstep (se 1 (by rfl) ⟨769280, by rfl⟩ : syracuseStep 1025707 = 1538561) B1538561
theorem B4368089 : Blo 908576 4368089 := bstep (se 2 (by rfl) ⟨1638033, by rfl⟩ : syracuseStep 4368089 = 3276067) B3276067
theorem B1025815 : Blo 908576 1025815 := bstep (se 1 (by rfl) ⟨769361, by rfl⟩ : syracuseStep 1025815 = 1538723) B1538723
theorem B1943347 : Blo 908576 1943347 := bstep (se 1 (by rfl) ⟨1457510, by rfl⟩ : syracuseStep 1943347 = 2915021) B2915021
theorem B2303923 : Blo 908576 2303923 := bstep (se 1 (by rfl) ⟨1727942, by rfl⟩ : syracuseStep 2303923 = 3455885) B3455885
theorem B1025995 : Blo 908576 1025995 := bstep (se 1 (by rfl) ⟨769496, by rfl⟩ : syracuseStep 1025995 = 1538993) B1538993
theorem B1026103 : Blo 908576 1026103 := bstep (se 1 (by rfl) ⟨769577, by rfl⟩ : syracuseStep 1026103 = 1539155) B1539155
theorem B2304065 : Blo 908576 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B3451025 : Blo 908576 3451025 := bstep (se 2 (by rfl) ⟨1294134, by rfl⟩ : syracuseStep 3451025 = 2588269) B2588269
theorem B1026283 : Blo 908576 1026283 := bstep (se 1 (by rfl) ⟨769712, by rfl⟩ : syracuseStep 1026283 = 1539425) B1539425
theorem B1943833 : Blo 908576 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B1026391 : Blo 908576 1026391 := bstep (se 1 (by rfl) ⟨769793, by rfl⟩ : syracuseStep 1026391 = 1539587) B1539587
theorem B1026571 : Blo 908576 1026571 := bstep (se 1 (by rfl) ⟨769928, by rfl⟩ : syracuseStep 1026571 = 1539857) B1539857
theorem B16198157 : Blo 908576 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B8759825 : Blo 908576 8759825 := bstep (se 2 (by rfl) ⟨3284934, by rfl⟩ : syracuseStep 8759825 = 6569869) B6569869
theorem B3451481 : Blo 908576 3451481 := bstep (se 2 (by rfl) ⟨1294305, by rfl⟩ : syracuseStep 3451481 = 2588611) B2588611
theorem B4991581 : Blo 908576 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B15575813 : Blo 908576 15575813 := bstep (se 4 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 15575813 = 2920465) B2920465
theorem B3451693 : Blo 908576 3451693 := bstep (se 3 (by rfl) ⟨647192, by rfl⟩ : syracuseStep 3451693 = 1294385) B1294385
theorem B1944577 : Blo 908576 1944577 := bstep (se 2 (by rfl) ⟨729216, by rfl⟩ : syracuseStep 1944577 = 1458433) B1458433
theorem B1092695 : Blo 908576 1092695 := bstep (se 1 (by rfl) ⟨819521, by rfl⟩ : syracuseStep 1092695 = 1639043) B1639043
theorem B3451997 : Blo 908576 3451997 := bstep (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) B1294499
theorem B7384355 : Blo 908576 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B2305331 : Blo 908576 2305331 := bstep (se 1 (by rfl) ⟨1728998, by rfl⟩ : syracuseStep 2305331 = 3457997) B3457997
theorem B4664641 : Blo 908576 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B4370071 : Blo 908576 4370071 := bstep (se 1 (by rfl) ⟨3277553, by rfl⟩ : syracuseStep 4370071 = 6555107) B6555107
theorem B7778065 : Blo 908576 7778065 := bstep (se 2 (by rfl) ⟨2916774, by rfl⟩ : syracuseStep 7778065 = 5833549) B5833549
theorem B2305867 : Blo 908576 2305867 := bstep (se 1 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 2305867 = 3458801) B3458801
theorem B1945559 : Blo 908576 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B2306009 : Blo 908576 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B7778339 : Blo 908576 7778339 := bstep (se 1 (by rfl) ⟨5833754, by rfl⟩ : syracuseStep 7778339 = 11667509) B11667509
theorem B2961559 : Blo 908576 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B4370705 : Blo 908576 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B5189933 : Blo 908576 5189933 := bstep (se 3 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 5189933 = 1946225) B1946225
theorem B2044313 : Blo 908576 2044313 := bstep (se 2 (by rfl) ⟨766617, by rfl⟩ : syracuseStep 2044313 = 1533235) B1533235
theorem B2044403 : Blo 908576 2044403 := bstep (se 1 (by rfl) ⟨1533302, by rfl⟩ : syracuseStep 2044403 = 3066605) B3066605
theorem B1946123 : Blo 908576 1946123 := bstep (se 1 (by rfl) ⟨1459592, by rfl⟩ : syracuseStep 1946123 = 2919185) B2919185
theorem B22196753 : Blo 908576 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B2044439 : Blo 908576 2044439 := bstep (se 1 (by rfl) ⟨1533329, by rfl⟩ : syracuseStep 2044439 = 3066659) B3066659
theorem B2044619 : Blo 908576 2044619 := bstep (se 1 (by rfl) ⟨1533464, by rfl⟩ : syracuseStep 2044619 = 3066929) B3066929
theorem B2044673 : Blo 908576 2044673 := bstep (se 2 (by rfl) ⟨766752, by rfl⟩ : syracuseStep 2044673 = 1533505) B1533505
theorem B2306839 : Blo 908576 2306839 := bstep (se 1 (by rfl) ⟨1730129, by rfl⟩ : syracuseStep 2306839 = 3460259) B3460259
theorem B2044889 : Blo 908576 2044889 := bstep (se 2 (by rfl) ⟨766833, by rfl⟩ : syracuseStep 2044889 = 1533667) B1533667
theorem B1946585 : Blo 908576 1946585 := bstep (se 2 (by rfl) ⟨729969, by rfl⟩ : syracuseStep 1946585 = 1459939) B1459939
theorem B5846033 : Blo 908576 5846033 := bstep (se 2 (by rfl) ⟨2192262, by rfl⟩ : syracuseStep 5846033 = 4384525) B4384525
theorem B2044979 : Blo 908576 2044979 := bstep (se 1 (by rfl) ⟨1533734, by rfl⟩ : syracuseStep 2044979 = 3067469) B3067469
theorem B2045015 : Blo 908576 2045015 := bstep (se 1 (by rfl) ⟨1533761, by rfl⟩ : syracuseStep 2045015 = 3067523) B3067523
theorem B2307275 : Blo 908576 2307275 := bstep (se 1 (by rfl) ⟨1730456, by rfl⟩ : syracuseStep 2307275 = 3460913) B3460913
theorem B2045195 : Blo 908576 2045195 := bstep (se 1 (by rfl) ⟨1533896, by rfl⟩ : syracuseStep 2045195 = 3067793) B3067793
theorem B2045249 : Blo 908576 2045249 := bstep (se 2 (by rfl) ⟨766968, by rfl⟩ : syracuseStep 2045249 = 1533937) B1533937
theorem B1455563 : Blo 908576 1455563 := bstep (se 1 (by rfl) ⟨1091672, by rfl⟩ : syracuseStep 1455563 = 2183345) B2183345
theorem B2045465 : Blo 908576 2045465 := bstep (se 2 (by rfl) ⟨767049, by rfl⟩ : syracuseStep 2045465 = 1534099) B1534099
theorem B2307649 : Blo 908576 2307649 := bstep (se 2 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 2307649 = 1730737) B1730737
theorem B2045555 : Blo 908576 2045555 := bstep (se 1 (by rfl) ⟨1534166, by rfl⟩ : syracuseStep 2045555 = 3068333) B3068333
theorem B3454595 : Blo 908576 3454595 := bstep (se 1 (by rfl) ⟨2590946, by rfl⟩ : syracuseStep 3454595 = 5181893) B5181893
theorem B3454609 : Blo 908576 3454609 := bstep (se 2 (by rfl) ⟨1295478, by rfl⟩ : syracuseStep 3454609 = 2590957) B2590957
theorem B2045591 : Blo 908576 2045591 := bstep (se 1 (by rfl) ⟨1534193, by rfl⟩ : syracuseStep 2045591 = 3068387) B3068387
theorem B2045771 : Blo 908576 2045771 := bstep (se 1 (by rfl) ⟨1534328, by rfl⟩ : syracuseStep 2045771 = 3068657) B3068657
theorem B2045825 : Blo 908576 2045825 := bstep (se 2 (by rfl) ⟨767184, by rfl⟩ : syracuseStep 2045825 = 1534369) B1534369
theorem B3454913 : Blo 908576 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B28063705 : Blo 908576 28063705 := bstep (se 2 (by rfl) ⟨10523889, by rfl⟩ : syracuseStep 28063705 = 21047779) B21047779
theorem B2046041 : Blo 908576 2046041 := bstep (se 2 (by rfl) ⟨767265, by rfl⟩ : syracuseStep 2046041 = 1534531) B1534531
theorem B1947763 : Blo 908576 1947763 := bstep (se 1 (by rfl) ⟨1460822, by rfl⟩ : syracuseStep 1947763 = 2921645) B2921645
theorem B3881105 : Blo 908576 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B2308247 : Blo 908576 2308247 := bstep (se 1 (by rfl) ⟨1731185, by rfl⟩ : syracuseStep 2308247 = 3462371) B3462371
theorem B2046131 : Blo 908576 2046131 := bstep (se 1 (by rfl) ⟨1534598, by rfl⟩ : syracuseStep 2046131 = 3069197) B3069197
theorem B2046167 : Blo 908576 2046167 := bstep (se 1 (by rfl) ⟨1534625, by rfl⟩ : syracuseStep 2046167 = 3069251) B3069251
theorem B3160343 : Blo 908576 3160343 := bstep (se 1 (by rfl) ⟨2370257, by rfl⟩ : syracuseStep 3160343 = 4740515) B4740515
theorem B2046347 : Blo 908576 2046347 := bstep (se 1 (by rfl) ⟨1534760, by rfl⟩ : syracuseStep 2046347 = 3069521) B3069521
theorem B1456537 : Blo 908576 1456537 := bstep (se 2 (by rfl) ⟨546201, by rfl⟩ : syracuseStep 1456537 = 1092403) B1092403
theorem B2046401 : Blo 908576 2046401 := bstep (se 2 (by rfl) ⟨767400, by rfl⟩ : syracuseStep 2046401 = 1534801) B1534801
theorem B6928901 : Blo 908576 6928901 := bstep (se 4 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 6928901 = 1299169) B1299169
theorem B1948225 : Blo 908576 1948225 := bstep (se 2 (by rfl) ⟨730584, by rfl⟩ : syracuseStep 1948225 = 1461169) B1461169
theorem B3455581 : Blo 908576 3455581 := bstep (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) B1295843
theorem B1456793 : Blo 908576 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B2046617 : Blo 908576 2046617 := bstep (se 2 (by rfl) ⟨767481, by rfl⟩ : syracuseStep 2046617 = 1534963) B1534963
theorem B2046707 : Blo 908576 2046707 := bstep (se 1 (by rfl) ⟨1535030, by rfl⟩ : syracuseStep 2046707 = 3070061) B3070061
theorem B2046743 : Blo 908576 2046743 := bstep (se 1 (by rfl) ⟨1535057, by rfl⟩ : syracuseStep 2046743 = 3070115) B3070115
theorem B2309057 : Blo 908576 2309057 := bstep (se 2 (by rfl) ⟨865896, by rfl⟩ : syracuseStep 2309057 = 1731793) B1731793
theorem B2046923 : Blo 908576 2046923 := bstep (se 1 (by rfl) ⟨1535192, by rfl⟩ : syracuseStep 2046923 = 3070385) B3070385
theorem B2046977 : Blo 908576 2046977 := bstep (se 2 (by rfl) ⟨767616, by rfl⟩ : syracuseStep 2046977 = 1535233) B1535233
theorem B1752257 : Blo 908576 1752257 := bstep (se 2 (by rfl) ⟨657096, by rfl⟩ : syracuseStep 1752257 = 1314193) B1314193
theorem B2047193 : Blo 908576 2047193 := bstep (se 2 (by rfl) ⟨767697, by rfl⟩ : syracuseStep 2047193 = 1535395) B1535395
theorem B1948951 : Blo 908576 1948951 := bstep (se 1 (by rfl) ⟨1461713, by rfl⟩ : syracuseStep 1948951 = 2923427) B2923427
theorem B2047283 : Blo 908576 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B2047319 : Blo 908576 2047319 := bstep (se 1 (by rfl) ⟨1535489, by rfl⟩ : syracuseStep 2047319 = 3070979) B3070979
theorem B4603229 : Blo 908576 4603229 := bstep (se 3 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 4603229 = 1726211) B1726211
theorem B2309593 : Blo 908576 2309593 := bstep (se 2 (by rfl) ⟨866097, by rfl⟩ : syracuseStep 2309593 = 1732195) B1732195
theorem B2047499 : Blo 908576 2047499 := bstep (se 1 (by rfl) ⟨1535624, by rfl⟩ : syracuseStep 2047499 = 3071249) B3071249
theorem B2047553 : Blo 908576 2047553 := bstep (se 2 (by rfl) ⟨767832, by rfl⟩ : syracuseStep 2047553 = 1535665) B1535665
theorem B1425163 : Blo 908576 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B2047769 : Blo 908576 2047769 := bstep (se 2 (by rfl) ⟨767913, by rfl⟩ : syracuseStep 2047769 = 1535827) B1535827
theorem B3456857 : Blo 908576 3456857 := bstep (se 2 (by rfl) ⟨1296321, by rfl⟩ : syracuseStep 3456857 = 2592643) B2592643
theorem B2047859 : Blo 908576 2047859 := bstep (se 1 (by rfl) ⟨1535894, by rfl⟩ : syracuseStep 2047859 = 3071789) B3071789
theorem B1752961 : Blo 908576 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B2047895 : Blo 908576 2047895 := bstep (se 1 (by rfl) ⟨1535921, by rfl⟩ : syracuseStep 2047895 = 3071843) B3071843
theorem B2048075 : Blo 908576 2048075 := bstep (se 1 (by rfl) ⟨1536056, by rfl⟩ : syracuseStep 2048075 = 3072113) B3072113
theorem B2048129 : Blo 908576 2048129 := bstep (se 2 (by rfl) ⟨768048, by rfl⟩ : syracuseStep 2048129 = 1536097) B1536097
theorem B1229131 : Blo 908576 1229131 := bstep (se 1 (by rfl) ⟨921848, by rfl⟩ : syracuseStep 1229131 = 1843697) B1843697
theorem B2048345 : Blo 908576 2048345 := bstep (se 2 (by rfl) ⟨768129, by rfl⟩ : syracuseStep 2048345 = 1536259) B1536259
theorem B2048435 : Blo 908576 2048435 := bstep (se 1 (by rfl) ⟨1536326, by rfl⟩ : syracuseStep 2048435 = 3072653) B3072653
theorem B1294795 : Blo 908576 1294795 := bstep (se 1 (by rfl) ⟨971096, by rfl⟩ : syracuseStep 1294795 = 1942193) B1942193
theorem B1294807 : Blo 908576 1294807 := bstep (se 1 (by rfl) ⟨971105, by rfl⟩ : syracuseStep 1294807 = 1942211) B1942211
theorem B2048471 : Blo 908576 2048471 := bstep (se 1 (by rfl) ⟨1536353, by rfl⟩ : syracuseStep 2048471 = 3072707) B3072707
theorem B3883565 : Blo 908576 3883565 := bstep (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) B1456337
theorem B2048651 : Blo 908576 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B2048705 : Blo 908576 2048705 := bstep (se 2 (by rfl) ⟨768264, by rfl⟩ : syracuseStep 2048705 = 1536529) B1536529
theorem B2048921 : Blo 908576 2048921 := bstep (se 2 (by rfl) ⟨768345, by rfl⟩ : syracuseStep 2048921 = 1536691) B1536691
theorem B2049011 : Blo 908576 2049011 := bstep (se 1 (by rfl) ⟨1536758, by rfl⟩ : syracuseStep 2049011 = 3073517) B3073517
theorem B2049047 : Blo 908576 2049047 := bstep (se 1 (by rfl) ⟨1536785, by rfl⟩ : syracuseStep 2049047 = 3073571) B3073571
theorem B8307805 : Blo 908576 8307805 := bstep (se 3 (by rfl) ⟨1557713, by rfl⟩ : syracuseStep 8307805 = 3115427) B3115427
theorem B935083 : Blo 908576 935083 := bstep (se 1 (by rfl) ⟨701312, by rfl⟩ : syracuseStep 935083 = 1402625) B1402625
theorem B2049227 : Blo 908576 2049227 := bstep (se 1 (by rfl) ⟨1536920, by rfl⟩ : syracuseStep 2049227 = 3073841) B3073841
theorem B3884249 : Blo 908576 3884249 := bstep (se 2 (by rfl) ⟨1456593, by rfl⟩ : syracuseStep 3884249 = 2913187) B2913187
theorem B2049281 : Blo 908576 2049281 := bstep (se 2 (by rfl) ⟨768480, by rfl⟩ : syracuseStep 2049281 = 1536961) B1536961
theorem B1230169 : Blo 908576 1230169 := bstep (se 2 (by rfl) ⟨461313, by rfl⟩ : syracuseStep 1230169 = 922627) B922627
theorem B4605335 : Blo 908576 4605335 := bstep (se 1 (by rfl) ⟨3454001, by rfl⟩ : syracuseStep 4605335 = 6908003) B6908003
theorem B3458483 : Blo 908576 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B3458497 : Blo 908576 3458497 := bstep (se 2 (by rfl) ⟨1296936, by rfl⟩ : syracuseStep 3458497 = 2593873) B2593873
theorem B1754561 : Blo 908576 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B2049497 : Blo 908576 2049497 := bstep (se 2 (by rfl) ⟨768561, by rfl⟩ : syracuseStep 2049497 = 1537123) B1537123
theorem B1558027 : Blo 908576 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B2049587 : Blo 908576 2049587 := bstep (se 1 (by rfl) ⟨1537190, by rfl⟩ : syracuseStep 2049587 = 3074381) B3074381
theorem B2049623 : Blo 908576 2049623 := bstep (se 1 (by rfl) ⟨1537217, by rfl⟩ : syracuseStep 2049623 = 3074435) B3074435
theorem B2049803 : Blo 908576 2049803 := bstep (se 1 (by rfl) ⟨1537352, by rfl⟩ : syracuseStep 2049803 = 3074705) B3074705
theorem B2049857 : Blo 908576 2049857 := bstep (se 2 (by rfl) ⟨768696, by rfl⟩ : syracuseStep 2049857 = 1537393) B1537393
theorem B2050073 : Blo 908576 2050073 := bstep (se 2 (by rfl) ⟨768777, by rfl⟩ : syracuseStep 2050073 = 1537555) B1537555
theorem B2050163 : Blo 908576 2050163 := bstep (se 1 (by rfl) ⟨1537622, by rfl⟩ : syracuseStep 2050163 = 3075245) B3075245
theorem B2050199 : Blo 908576 2050199 := bstep (se 1 (by rfl) ⟨1537649, by rfl⟩ : syracuseStep 2050199 = 3075299) B3075299
theorem B2050379 : Blo 908576 2050379 := bstep (se 1 (by rfl) ⟨1537784, by rfl⟩ : syracuseStep 2050379 = 3075569) B3075569
theorem B1460567 : Blo 908576 1460567 := bstep (se 1 (by rfl) ⟨1095425, by rfl⟩ : syracuseStep 1460567 = 2190851) B2190851
theorem B2050433 : Blo 908576 2050433 := bstep (se 2 (by rfl) ⟨768912, by rfl⟩ : syracuseStep 2050433 = 1537825) B1537825
theorem B3885515 : Blo 908576 3885515 := bstep (se 1 (by rfl) ⟨2914136, by rfl⟩ : syracuseStep 3885515 = 5828273) B5828273
theorem B1296857 : Blo 908576 1296857 := bstep (se 2 (by rfl) ⟨486321, by rfl⟩ : syracuseStep 1296857 = 972643) B972643
theorem B14764619 : Blo 908576 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B2050649 : Blo 908576 2050649 := bstep (se 2 (by rfl) ⟨768993, by rfl⟩ : syracuseStep 2050649 = 1537987) B1537987
theorem B2050739 : Blo 908576 2050739 := bstep (se 1 (by rfl) ⟨1538054, by rfl⟩ : syracuseStep 2050739 = 3076109) B3076109
theorem B2050775 : Blo 908576 2050775 := bstep (se 1 (by rfl) ⟨1538081, by rfl⟩ : syracuseStep 2050775 = 3076163) B3076163
theorem B19942129 : Blo 908576 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B3885889 : Blo 908576 3885889 := bstep (se 2 (by rfl) ⟨1457208, by rfl⟩ : syracuseStep 3885889 = 2914417) B2914417
theorem B3066713 : Blo 908576 3066713 := bstep (se 2 (by rfl) ⟨1150017, by rfl⟩ : syracuseStep 3066713 = 2300035) B2300035
theorem B2050955 : Blo 908576 2050955 := bstep (se 1 (by rfl) ⟨1538216, by rfl⟩ : syracuseStep 2050955 = 3076433) B3076433
theorem B2051009 : Blo 908576 2051009 := bstep (se 2 (by rfl) ⟨769128, by rfl⟩ : syracuseStep 2051009 = 1538257) B1538257
theorem B1362905 : Blo 908576 1362905 := bstep (se 2 (by rfl) ⟨511089, by rfl⟩ : syracuseStep 1362905 = 1022179) B1022179
theorem B1363019 : Blo 908576 1363019 := bstep (se 1 (by rfl) ⟨1022264, by rfl⟩ : syracuseStep 1363019 = 2044529) B2044529
theorem B1461323 : Blo 908576 1461323 := bstep (se 1 (by rfl) ⟨1095992, by rfl⟩ : syracuseStep 1461323 = 2191985) B2191985
theorem B1363031 : Blo 908576 1363031 := bstep (se 1 (by rfl) ⟨1022273, by rfl⟩ : syracuseStep 1363031 = 2044547) B2044547
theorem B1297495 : Blo 908576 1297495 := bstep (se 1 (by rfl) ⟨973121, by rfl⟩ : syracuseStep 1297495 = 1946243) B1946243
theorem B3886231 : Blo 908576 3886231 := bstep (se 1 (by rfl) ⟨2914673, by rfl⟩ : syracuseStep 3886231 = 5829347) B5829347
theorem B1363097 : Blo 908576 1363097 := bstep (se 2 (by rfl) ⟨511161, by rfl⟩ : syracuseStep 1363097 = 1022323) B1022323
theorem B2051225 : Blo 908576 2051225 := bstep (se 2 (by rfl) ⟨769209, by rfl⟩ : syracuseStep 2051225 = 1538419) B1538419
theorem B2051315 : Blo 908576 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B1363211 : Blo 908576 1363211 := bstep (se 1 (by rfl) ⟨1022408, by rfl⟩ : syracuseStep 1363211 = 2044817) B2044817
theorem B1363223 : Blo 908576 1363223 := bstep (se 1 (by rfl) ⟨1022417, by rfl⟩ : syracuseStep 1363223 = 2044835) B2044835
theorem B2051351 : Blo 908576 2051351 := bstep (se 1 (by rfl) ⟨1538513, by rfl⟩ : syracuseStep 2051351 = 3077027) B3077027
theorem B3460427 : Blo 908576 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B1363289 : Blo 908576 1363289 := bstep (se 2 (by rfl) ⟨511233, by rfl⟩ : syracuseStep 1363289 = 1022467) B1022467
theorem B3460441 : Blo 908576 3460441 := bstep (se 2 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 3460441 = 2595331) B2595331
theorem B1363403 : Blo 908576 1363403 := bstep (se 1 (by rfl) ⟨1022552, by rfl⟩ : syracuseStep 1363403 = 2045105) B2045105
theorem B2051531 : Blo 908576 2051531 := bstep (se 1 (by rfl) ⟨1538648, by rfl⟩ : syracuseStep 2051531 = 3077297) B3077297
theorem B1363415 : Blo 908576 1363415 := bstep (se 1 (by rfl) ⟨1022561, by rfl⟩ : syracuseStep 1363415 = 2045123) B2045123
theorem B2051585 : Blo 908576 2051585 := bstep (se 2 (by rfl) ⟨769344, by rfl⟩ : syracuseStep 2051585 = 1538689) B1538689
theorem B3067415 : Blo 908576 3067415 := bstep (se 1 (by rfl) ⟨2300561, by rfl⟩ : syracuseStep 3067415 = 4601123) B4601123
theorem B1363481 : Blo 908576 1363481 := bstep (se 2 (by rfl) ⟨511305, by rfl⟩ : syracuseStep 1363481 = 1022611) B1022611
theorem B5197405 : Blo 908576 5197405 := bstep (se 3 (by rfl) ⟨974513, by rfl⟩ : syracuseStep 5197405 = 1949027) B1949027
theorem B1363595 : Blo 908576 1363595 := bstep (se 1 (by rfl) ⟨1022696, by rfl⟩ : syracuseStep 1363595 = 2045393) B2045393
theorem B1363607 : Blo 908576 1363607 := bstep (se 1 (by rfl) ⟨1022705, by rfl⟩ : syracuseStep 1363607 = 2045411) B2045411
theorem B1560217 : Blo 908576 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B1363673 : Blo 908576 1363673 := bstep (se 2 (by rfl) ⟨511377, by rfl⟩ : syracuseStep 1363673 = 1022755) B1022755
theorem B2051801 : Blo 908576 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B14044913 : Blo 908576 14044913 := bstep (se 2 (by rfl) ⟨5266842, by rfl⟩ : syracuseStep 14044913 = 10533685) B10533685
theorem B2051891 : Blo 908576 2051891 := bstep (se 1 (by rfl) ⟨1538918, by rfl⟩ : syracuseStep 2051891 = 3077837) B3077837
theorem B1363787 : Blo 908576 1363787 := bstep (se 1 (by rfl) ⟨1022840, by rfl⟩ : syracuseStep 1363787 = 2045681) B2045681
theorem B1560395 : Blo 908576 1560395 := bstep (se 1 (by rfl) ⟨1170296, by rfl⟩ : syracuseStep 1560395 = 2340593) B2340593
theorem B1363799 : Blo 908576 1363799 := bstep (se 1 (by rfl) ⟨1022849, by rfl⟩ : syracuseStep 1363799 = 2045699) B2045699
theorem B2051927 : Blo 908576 2051927 := bstep (se 1 (by rfl) ⟨1538945, by rfl⟩ : syracuseStep 2051927 = 3077891) B3077891
theorem B3788633 : Blo 908576 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B1298315 : Blo 908576 1298315 := bstep (se 1 (by rfl) ⟨973736, by rfl⟩ : syracuseStep 1298315 = 1947473) B1947473
theorem B1363865 : Blo 908576 1363865 := bstep (se 2 (by rfl) ⟨511449, by rfl⟩ : syracuseStep 1363865 = 1022899) B1022899
theorem B1363979 : Blo 908576 1363979 := bstep (se 1 (by rfl) ⟨1022984, by rfl⟩ : syracuseStep 1363979 = 2045969) B2045969
theorem B2052107 : Blo 908576 2052107 := bstep (se 1 (by rfl) ⟨1539080, by rfl⟩ : syracuseStep 2052107 = 3078161) B3078161
theorem B1363991 : Blo 908576 1363991 := bstep (se 1 (by rfl) ⟨1022993, by rfl⟩ : syracuseStep 1363991 = 2045987) B2045987
theorem B3067955 : Blo 908576 3067955 := bstep (se 1 (by rfl) ⟨2300966, by rfl⟩ : syracuseStep 3067955 = 4601933) B4601933
theorem B2052161 : Blo 908576 2052161 := bstep (se 2 (by rfl) ⟨769560, by rfl⟩ : syracuseStep 2052161 = 1539121) B1539121
theorem B1364057 : Blo 908576 1364057 := bstep (se 2 (by rfl) ⟨511521, by rfl⟩ : syracuseStep 1364057 = 1023043) B1023043
theorem B1364171 : Blo 908576 1364171 := bstep (se 1 (by rfl) ⟨1023128, by rfl⟩ : syracuseStep 1364171 = 2046257) B2046257
theorem B1364183 : Blo 908576 1364183 := bstep (se 1 (by rfl) ⟨1023137, by rfl⟩ : syracuseStep 1364183 = 2046275) B2046275
theorem B3461399 : Blo 908576 3461399 := bstep (se 1 (by rfl) ⟨2596049, by rfl⟩ : syracuseStep 3461399 = 5192099) B5192099
theorem B1364249 : Blo 908576 1364249 := bstep (se 2 (by rfl) ⟨511593, by rfl⟩ : syracuseStep 1364249 = 1023187) B1023187
theorem B2052377 : Blo 908576 2052377 := bstep (se 2 (by rfl) ⟨769641, by rfl⟩ : syracuseStep 2052377 = 1539283) B1539283
theorem B3068225 : Blo 908576 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B2052467 : Blo 908576 2052467 := bstep (se 1 (by rfl) ⟨1539350, by rfl⟩ : syracuseStep 2052467 = 3078701) B3078701
theorem B1364363 : Blo 908576 1364363 := bstep (se 1 (by rfl) ⟨1023272, by rfl⟩ : syracuseStep 1364363 = 2046545) B2046545
theorem B1364375 : Blo 908576 1364375 := bstep (se 1 (by rfl) ⟨1023281, by rfl⟩ : syracuseStep 1364375 = 2046563) B2046563
theorem B2052503 : Blo 908576 2052503 := bstep (se 1 (by rfl) ⟨1539377, by rfl⟩ : syracuseStep 2052503 = 3078755) B3078755
theorem B1364441 : Blo 908576 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B12440081 : Blo 908576 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B3691025 : Blo 908576 3691025 := bstep (se 2 (by rfl) ⟨1384134, by rfl⟩ : syracuseStep 3691025 = 2768269) B2768269
theorem B1724951 : Blo 908576 1724951 := bstep (se 1 (by rfl) ⟨1293713, by rfl⟩ : syracuseStep 1724951 = 2587427) B2587427
theorem B1364555 : Blo 908576 1364555 := bstep (se 1 (by rfl) ⟨1023416, by rfl⟩ : syracuseStep 1364555 = 2046833) B2046833
theorem B2052683 : Blo 908576 2052683 := bstep (se 1 (by rfl) ⟨1539512, by rfl⟩ : syracuseStep 2052683 = 3079025) B3079025
theorem B1364567 : Blo 908576 1364567 := bstep (se 1 (by rfl) ⟨1023425, by rfl⟩ : syracuseStep 1364567 = 2046851) B2046851
theorem B2052737 : Blo 908576 2052737 := bstep (se 2 (by rfl) ⟨769776, by rfl⟩ : syracuseStep 2052737 = 1539553) B1539553
theorem B1364633 : Blo 908576 1364633 := bstep (se 2 (by rfl) ⟨511737, by rfl⟩ : syracuseStep 1364633 = 1023475) B1023475
theorem B1364747 : Blo 908576 1364747 := bstep (se 1 (by rfl) ⟨1023560, by rfl⟩ : syracuseStep 1364747 = 2047121) B2047121
theorem B2183959 : Blo 908576 2183959 := bstep (se 1 (by rfl) ⟨1637969, by rfl⟩ : syracuseStep 2183959 = 3275939) B3275939
theorem B1364759 : Blo 908576 1364759 := bstep (se 1 (by rfl) ⟨1023569, by rfl⟩ : syracuseStep 1364759 = 2047139) B2047139
theorem B1725209 : Blo 908576 1725209 := bstep (se 2 (by rfl) ⟨646953, by rfl⟩ : syracuseStep 1725209 = 1293907) B1293907
theorem B1364825 : Blo 908576 1364825 := bstep (se 2 (by rfl) ⟨511809, by rfl⟩ : syracuseStep 1364825 = 1023619) B1023619
theorem B2052953 : Blo 908576 2052953 := bstep (se 2 (by rfl) ⟨769857, by rfl⟩ : syracuseStep 2052953 = 1539715) B1539715
theorem B3068765 : Blo 908576 3068765 := bstep (se 3 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 3068765 = 1150787) B1150787
theorem B4608899 : Blo 908576 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B2053043 : Blo 908576 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B1364939 : Blo 908576 1364939 := bstep (se 1 (by rfl) ⟨1023704, by rfl⟩ : syracuseStep 1364939 = 2047409) B2047409
theorem B1364951 : Blo 908576 1364951 := bstep (se 1 (by rfl) ⟨1023713, by rfl⟩ : syracuseStep 1364951 = 2047427) B2047427
theorem B2053079 : Blo 908576 2053079 := bstep (se 1 (by rfl) ⟨1539809, by rfl⟩ : syracuseStep 2053079 = 3079619) B3079619
theorem B1365017 : Blo 908576 1365017 := bstep (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) B1023763
theorem B1365131 : Blo 908576 1365131 := bstep (se 1 (by rfl) ⟨1023848, by rfl⟩ : syracuseStep 1365131 = 2047697) B2047697
theorem B2053259 : Blo 908576 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B1365143 : Blo 908576 1365143 := bstep (se 1 (by rfl) ⟨1023857, by rfl⟩ : syracuseStep 1365143 = 2047715) B2047715
theorem B971947 : Blo 908576 971947 := bstep (se 1 (by rfl) ⟨728960, by rfl⟩ : syracuseStep 971947 = 1457921) B1457921
theorem B1725619 : Blo 908576 1725619 := bstep (se 1 (by rfl) ⟨1294214, by rfl⟩ : syracuseStep 1725619 = 2588429) B2588429
theorem B1365209 : Blo 908576 1365209 := bstep (se 2 (by rfl) ⟨511953, by rfl⟩ : syracuseStep 1365209 = 1023907) B1023907
theorem B4379969 : Blo 908576 4379969 := bstep (se 2 (by rfl) ⟨1642488, by rfl⟩ : syracuseStep 4379969 = 3284977) B3284977
theorem B1365323 : Blo 908576 1365323 := bstep (se 1 (by rfl) ⟨1023992, by rfl⟩ : syracuseStep 1365323 = 2047985) B2047985
theorem B1365335 : Blo 908576 1365335 := bstep (se 1 (by rfl) ⟨1024001, by rfl⟩ : syracuseStep 1365335 = 2048003) B2048003
theorem B1365401 : Blo 908576 1365401 := bstep (se 2 (by rfl) ⟨512025, by rfl⟩ : syracuseStep 1365401 = 1024051) B1024051
theorem B4380083 : Blo 908576 4380083 := bstep (se 1 (by rfl) ⟨3285062, by rfl⟩ : syracuseStep 4380083 = 6570125) B6570125
theorem B3462659 : Blo 908576 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B1365515 : Blo 908576 1365515 := bstep (se 1 (by rfl) ⟨1024136, by rfl⟩ : syracuseStep 1365515 = 2048273) B2048273
theorem B1267211 : Blo 908576 1267211 := bstep (se 1 (by rfl) ⟨950408, by rfl⟩ : syracuseStep 1267211 = 1900817) B1900817
theorem B1365527 : Blo 908576 1365527 := bstep (se 1 (by rfl) ⟨1024145, by rfl⟩ : syracuseStep 1365527 = 2048291) B2048291
theorem B1365593 : Blo 908576 1365593 := bstep (se 2 (by rfl) ⟨512097, by rfl⟩ : syracuseStep 1365593 = 1024195) B1024195
theorem B1726105 : Blo 908576 1726105 := bstep (se 2 (by rfl) ⟨647289, by rfl⟩ : syracuseStep 1726105 = 1294579) B1294579
theorem B1365707 : Blo 908576 1365707 := bstep (se 1 (by rfl) ⟨1024280, by rfl⟩ : syracuseStep 1365707 = 2048561) B2048561
theorem B1365719 : Blo 908576 1365719 := bstep (se 1 (by rfl) ⟨1024289, by rfl⟩ : syracuseStep 1365719 = 2048579) B2048579
theorem B1365785 : Blo 908576 1365785 := bstep (se 2 (by rfl) ⟨512169, by rfl⟩ : syracuseStep 1365785 = 1024339) B1024339
theorem B5822273 : Blo 908576 5822273 := bstep (se 2 (by rfl) ⟨2183352, by rfl⟩ : syracuseStep 5822273 = 4366705) B4366705
theorem B1365899 : Blo 908576 1365899 := bstep (se 1 (by rfl) ⟨1024424, by rfl⟩ : syracuseStep 1365899 = 2048849) B2048849
theorem B1365911 : Blo 908576 1365911 := bstep (se 1 (by rfl) ⟨1024433, by rfl⟩ : syracuseStep 1365911 = 2048867) B2048867
theorem B3069899 : Blo 908576 3069899 := bstep (se 1 (by rfl) ⟨2302424, by rfl⟩ : syracuseStep 3069899 = 4604849) B4604849
theorem B1365977 : Blo 908576 1365977 := bstep (se 2 (by rfl) ⟨512241, by rfl⟩ : syracuseStep 1365977 = 1024483) B1024483
theorem B1366091 : Blo 908576 1366091 := bstep (se 1 (by rfl) ⟨1024568, by rfl⟩ : syracuseStep 1366091 = 2049137) B2049137
theorem B1366103 : Blo 908576 1366103 := bstep (se 1 (by rfl) ⟨1024577, by rfl⟩ : syracuseStep 1366103 = 2049155) B2049155
theorem B2021465 : Blo 908576 2021465 := bstep (se 2 (by rfl) ⟨758049, by rfl⟩ : syracuseStep 2021465 = 1516099) B1516099
theorem B1366169 : Blo 908576 1366169 := bstep (se 2 (by rfl) ⟨512313, by rfl⟩ : syracuseStep 1366169 = 1024627) B1024627
theorem B1726667 : Blo 908576 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B1038539 : Blo 908576 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B3070169 : Blo 908576 3070169 := bstep (se 2 (by rfl) ⟨1151313, by rfl⟩ : syracuseStep 3070169 = 2302627) B2302627
theorem B1366283 : Blo 908576 1366283 := bstep (se 1 (by rfl) ⟨1024712, by rfl⟩ : syracuseStep 1366283 = 2049425) B2049425
theorem B5921041 : Blo 908576 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B1366295 : Blo 908576 1366295 := bstep (se 1 (by rfl) ⟨1024721, by rfl⟩ : syracuseStep 1366295 = 2049443) B2049443
theorem B5921099 : Blo 908576 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B1366361 : Blo 908576 1366361 := bstep (se 2 (by rfl) ⟨512385, by rfl⟩ : syracuseStep 1366361 = 1024771) B1024771
theorem B1726849 : Blo 908576 1726849 := bstep (se 2 (by rfl) ⟨647568, by rfl⟩ : syracuseStep 1726849 = 1295137) B1295137
theorem B1169815 : Blo 908576 1169815 := bstep (se 1 (by rfl) ⟨877361, by rfl⟩ : syracuseStep 1169815 = 1754723) B1754723
theorem B1366475 : Blo 908576 1366475 := bstep (se 1 (by rfl) ⟨1024856, by rfl⟩ : syracuseStep 1366475 = 2049713) B2049713
theorem B1366487 : Blo 908576 1366487 := bstep (se 1 (by rfl) ⟨1024865, by rfl⟩ : syracuseStep 1366487 = 2049731) B2049731
theorem B7494149 : Blo 908576 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B1366553 : Blo 908576 1366553 := bstep (se 2 (by rfl) ⟨512457, by rfl⟩ : syracuseStep 1366553 = 1024915) B1024915
theorem B1366667 : Blo 908576 1366667 := bstep (se 1 (by rfl) ⟨1025000, by rfl⟩ : syracuseStep 1366667 = 2050001) B2050001
theorem B1366679 : Blo 908576 1366679 := bstep (se 1 (by rfl) ⟨1025009, by rfl⟩ : syracuseStep 1366679 = 2050019) B2050019
theorem B973463 : Blo 908576 973463 := bstep (se 1 (by rfl) ⟨730097, by rfl⟩ : syracuseStep 973463 = 1460195) B1460195
theorem B1366745 : Blo 908576 1366745 := bstep (se 2 (by rfl) ⟨512529, by rfl⟩ : syracuseStep 1366745 = 1025059) B1025059
theorem B1170199 : Blo 908576 1170199 := bstep (se 1 (by rfl) ⟨877649, by rfl⟩ : syracuseStep 1170199 = 1755299) B1755299
theorem B1366859 : Blo 908576 1366859 := bstep (se 1 (by rfl) ⟨1025144, by rfl⟩ : syracuseStep 1366859 = 2050289) B2050289
theorem B1366871 : Blo 908576 1366871 := bstep (se 1 (by rfl) ⟨1025153, by rfl⟩ : syracuseStep 1366871 = 2050307) B2050307
theorem B3070871 : Blo 908576 3070871 := bstep (se 1 (by rfl) ⟨2303153, by rfl⟩ : syracuseStep 3070871 = 4606307) B4606307
theorem B1366937 : Blo 908576 1366937 := bstep (se 2 (by rfl) ⟨512601, by rfl⟩ : syracuseStep 1366937 = 1025203) B1025203
theorem B1367051 : Blo 908576 1367051 := bstep (se 1 (by rfl) ⟨1025288, by rfl⟩ : syracuseStep 1367051 = 2050577) B2050577
theorem B1367063 : Blo 908576 1367063 := bstep (se 1 (by rfl) ⟨1025297, by rfl⟩ : syracuseStep 1367063 = 2050595) B2050595
theorem B3693619 : Blo 908576 3693619 := bstep (se 1 (by rfl) ⟨2770214, by rfl⟩ : syracuseStep 3693619 = 5540429) B5540429
theorem B1727563 : Blo 908576 1727563 := bstep (se 1 (by rfl) ⟨1295672, by rfl⟩ : syracuseStep 1727563 = 2591345) B2591345
theorem B1367129 : Blo 908576 1367129 := bstep (se 2 (by rfl) ⟨512673, by rfl⟩ : syracuseStep 1367129 = 1025347) B1025347
theorem B1727639 : Blo 908576 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B1367243 : Blo 908576 1367243 := bstep (se 1 (by rfl) ⟨1025432, by rfl⟩ : syracuseStep 1367243 = 2050865) B2050865
theorem B1367255 : Blo 908576 1367255 := bstep (se 1 (by rfl) ⟨1025441, by rfl⟩ : syracuseStep 1367255 = 2050883) B2050883
theorem B1367321 : Blo 908576 1367321 := bstep (se 2 (by rfl) ⟨512745, by rfl⟩ : syracuseStep 1367321 = 1025491) B1025491
theorem B908587 : Blo 908576 908587 := bstep (se 1 (by rfl) ⟨681440, by rfl⟩ : syracuseStep 908587 = 1362881) B1362881
theorem B908599 : Blo 908576 908599 := bstep (se 1 (by rfl) ⟨681449, by rfl⟩ : syracuseStep 908599 = 1362899) B1362899
theorem B908619 : Blo 908576 908619 := bstep (se 1 (by rfl) ⟨681464, by rfl⟩ : syracuseStep 908619 = 1362929) B1362929
theorem B974155 : Blo 908576 974155 := bstep (se 1 (by rfl) ⟨730616, by rfl⟩ : syracuseStep 974155 = 1461233) B1461233
theorem B908631 : Blo 908576 908631 := bstep (se 1 (by rfl) ⟨681473, by rfl⟩ : syracuseStep 908631 = 1362947) B1362947
theorem B908651 : Blo 908576 908651 := bstep (se 1 (by rfl) ⟨681488, by rfl⟩ : syracuseStep 908651 = 1362977) B1362977
theorem B908663 : Blo 908576 908663 := bstep (se 1 (by rfl) ⟨681497, by rfl⟩ : syracuseStep 908663 = 1362995) B1362995
theorem B908683 : Blo 908576 908683 := bstep (se 1 (by rfl) ⟨681512, by rfl⟩ : syracuseStep 908683 = 1363025) B1363025
theorem B1367435 : Blo 908576 1367435 := bstep (se 1 (by rfl) ⟨1025576, by rfl⟩ : syracuseStep 1367435 = 2051153) B2051153
theorem B119922061 : Blo 908576 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B908695 : Blo 908576 908695 := bstep (se 1 (by rfl) ⟨681521, by rfl⟩ : syracuseStep 908695 = 1363043) B1363043
theorem B1367447 : Blo 908576 1367447 := bstep (se 1 (by rfl) ⟨1025585, by rfl⟩ : syracuseStep 1367447 = 2051171) B2051171
theorem B908715 : Blo 908576 908715 := bstep (se 1 (by rfl) ⟨681536, by rfl⟩ : syracuseStep 908715 = 1363073) B1363073
theorem B3890605 : Blo 908576 3890605 := bstep (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) B1458977
theorem B3071411 : Blo 908576 3071411 := bstep (se 1 (by rfl) ⟨2303558, by rfl⟩ : syracuseStep 3071411 = 4607117) B4607117
theorem B908727 : Blo 908576 908727 := bstep (se 1 (by rfl) ⟨681545, by rfl⟩ : syracuseStep 908727 = 1363091) B1363091
theorem B908747 : Blo 908576 908747 := bstep (se 1 (by rfl) ⟨681560, by rfl⟩ : syracuseStep 908747 = 1363121) B1363121
theorem B908759 : Blo 908576 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B1367513 : Blo 908576 1367513 := bstep (se 2 (by rfl) ⟨512817, by rfl⟩ : syracuseStep 1367513 = 1025635) B1025635
theorem B908779 : Blo 908576 908779 := bstep (se 1 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 908779 = 1363169) B1363169
theorem B908791 : Blo 908576 908791 := bstep (se 1 (by rfl) ⟨681593, by rfl⟩ : syracuseStep 908791 = 1363187) B1363187
theorem B908811 : Blo 908576 908811 := bstep (se 1 (by rfl) ⟨681608, by rfl⟩ : syracuseStep 908811 = 1363217) B1363217
theorem B908823 : Blo 908576 908823 := bstep (se 1 (by rfl) ⟨681617, by rfl⟩ : syracuseStep 908823 = 1363235) B1363235
theorem B908843 : Blo 908576 908843 := bstep (se 1 (by rfl) ⟨681632, by rfl⟩ : syracuseStep 908843 = 1363265) B1363265
theorem B908855 : Blo 908576 908855 := bstep (se 1 (by rfl) ⟨681641, by rfl⟩ : syracuseStep 908855 = 1363283) B1363283
theorem B908875 : Blo 908576 908875 := bstep (se 1 (by rfl) ⟨681656, by rfl⟩ : syracuseStep 908875 = 1363313) B1363313
theorem B1367627 : Blo 908576 1367627 := bstep (se 1 (by rfl) ⟨1025720, by rfl⟩ : syracuseStep 1367627 = 2051441) B2051441
theorem B908887 : Blo 908576 908887 := bstep (se 1 (by rfl) ⟨681665, by rfl⟩ : syracuseStep 908887 = 1363331) B1363331
theorem B1367639 : Blo 908576 1367639 := bstep (se 1 (by rfl) ⟨1025729, by rfl⟩ : syracuseStep 1367639 = 2051459) B2051459
theorem B908907 : Blo 908576 908907 := bstep (se 1 (by rfl) ⟨681680, by rfl⟩ : syracuseStep 908907 = 1363361) B1363361
theorem B908919 : Blo 908576 908919 := bstep (se 1 (by rfl) ⟨681689, by rfl⟩ : syracuseStep 908919 = 1363379) B1363379
theorem B908939 : Blo 908576 908939 := bstep (se 1 (by rfl) ⟨681704, by rfl⟩ : syracuseStep 908939 = 1363409) B1363409
theorem B908951 : Blo 908576 908951 := bstep (se 1 (by rfl) ⟨681713, by rfl⟩ : syracuseStep 908951 = 1363427) B1363427
theorem B1367705 : Blo 908576 1367705 := bstep (se 2 (by rfl) ⟨512889, by rfl⟩ : syracuseStep 1367705 = 1025779) B1025779
theorem B908971 : Blo 908576 908971 := bstep (se 1 (by rfl) ⟨681728, by rfl⟩ : syracuseStep 908971 = 1363457) B1363457
theorem B3694253 : Blo 908576 3694253 := bstep (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) B1385345
theorem B908983 : Blo 908576 908983 := bstep (se 1 (by rfl) ⟨681737, by rfl⟩ : syracuseStep 908983 = 1363475) B1363475
theorem B3071681 : Blo 908576 3071681 := bstep (se 2 (by rfl) ⟨1151880, by rfl⟩ : syracuseStep 3071681 = 2303761) B2303761
theorem B909003 : Blo 908576 909003 := bstep (se 1 (by rfl) ⟨681752, by rfl⟩ : syracuseStep 909003 = 1363505) B1363505
theorem B909015 : Blo 908576 909015 := bstep (se 1 (by rfl) ⟨681761, by rfl⟩ : syracuseStep 909015 = 1363523) B1363523
theorem B909035 : Blo 908576 909035 := bstep (se 1 (by rfl) ⟨681776, by rfl⟩ : syracuseStep 909035 = 1363553) B1363553
theorem B909047 : Blo 908576 909047 := bstep (se 1 (by rfl) ⟨681785, by rfl⟩ : syracuseStep 909047 = 1363571) B1363571
theorem B909067 : Blo 908576 909067 := bstep (se 1 (by rfl) ⟨681800, by rfl⟩ : syracuseStep 909067 = 1363601) B1363601
theorem B1367819 : Blo 908576 1367819 := bstep (se 1 (by rfl) ⟨1025864, by rfl⟩ : syracuseStep 1367819 = 2051729) B2051729
theorem B909079 : Blo 908576 909079 := bstep (se 1 (by rfl) ⟨681809, by rfl⟩ : syracuseStep 909079 = 1363619) B1363619
theorem B1367831 : Blo 908576 1367831 := bstep (se 1 (by rfl) ⟨1025873, by rfl⟩ : syracuseStep 1367831 = 2051747) B2051747
theorem B909099 : Blo 908576 909099 := bstep (se 1 (by rfl) ⟨681824, by rfl⟩ : syracuseStep 909099 = 1363649) B1363649
theorem B1728307 : Blo 908576 1728307 := bstep (se 1 (by rfl) ⟨1296230, by rfl⟩ : syracuseStep 1728307 = 2592461) B2592461
theorem B909111 : Blo 908576 909111 := bstep (se 1 (by rfl) ⟨681833, by rfl⟩ : syracuseStep 909111 = 1363667) B1363667
theorem B909131 : Blo 908576 909131 := bstep (se 1 (by rfl) ⟨681848, by rfl⟩ : syracuseStep 909131 = 1363697) B1363697
theorem B909143 : Blo 908576 909143 := bstep (se 1 (by rfl) ⟨681857, by rfl⟩ : syracuseStep 909143 = 1363715) B1363715
theorem B1367897 : Blo 908576 1367897 := bstep (se 2 (by rfl) ⟨512961, by rfl⟩ : syracuseStep 1367897 = 1025923) B1025923
theorem B909163 : Blo 908576 909163 := bstep (se 1 (by rfl) ⟨681872, by rfl⟩ : syracuseStep 909163 = 1363745) B1363745
theorem B909175 : Blo 908576 909175 := bstep (se 1 (by rfl) ⟨681881, by rfl⟩ : syracuseStep 909175 = 1363763) B1363763
theorem B909195 : Blo 908576 909195 := bstep (se 1 (by rfl) ⟨681896, by rfl⟩ : syracuseStep 909195 = 1363793) B1363793
theorem B909207 : Blo 908576 909207 := bstep (se 1 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 909207 = 1363811) B1363811
theorem B909227 : Blo 908576 909227 := bstep (se 1 (by rfl) ⟨681920, by rfl⟩ : syracuseStep 909227 = 1363841) B1363841
theorem B909239 : Blo 908576 909239 := bstep (se 1 (by rfl) ⟨681929, by rfl⟩ : syracuseStep 909239 = 1363859) B1363859
theorem B909259 : Blo 908576 909259 := bstep (se 1 (by rfl) ⟨681944, by rfl⟩ : syracuseStep 909259 = 1363889) B1363889
theorem B1368011 : Blo 908576 1368011 := bstep (se 1 (by rfl) ⟨1026008, by rfl⟩ : syracuseStep 1368011 = 2052017) B2052017
theorem B909271 : Blo 908576 909271 := bstep (se 1 (by rfl) ⟨681953, by rfl⟩ : syracuseStep 909271 = 1363907) B1363907
theorem B1368023 : Blo 908576 1368023 := bstep (se 1 (by rfl) ⟨1026017, by rfl⟩ : syracuseStep 1368023 = 2052035) B2052035
theorem B909291 : Blo 908576 909291 := bstep (se 1 (by rfl) ⟨681968, by rfl⟩ : syracuseStep 909291 = 1363937) B1363937
theorem B909303 : Blo 908576 909303 := bstep (se 1 (by rfl) ⟨681977, by rfl⟩ : syracuseStep 909303 = 1363955) B1363955
theorem B909323 : Blo 908576 909323 := bstep (se 1 (by rfl) ⟨681992, by rfl⟩ : syracuseStep 909323 = 1363985) B1363985
theorem B909335 : Blo 908576 909335 := bstep (se 1 (by rfl) ⟨682001, by rfl⟩ : syracuseStep 909335 = 1364003) B1364003
theorem B1728535 : Blo 908576 1728535 := bstep (se 1 (by rfl) ⟨1296401, by rfl⟩ : syracuseStep 1728535 = 2592803) B2592803
theorem B1368089 : Blo 908576 1368089 := bstep (se 2 (by rfl) ⟨513033, by rfl⟩ : syracuseStep 1368089 = 1026067) B1026067
theorem B909355 : Blo 908576 909355 := bstep (se 1 (by rfl) ⟨682016, by rfl⟩ : syracuseStep 909355 = 1364033) B1364033
theorem B909367 : Blo 908576 909367 := bstep (se 1 (by rfl) ⟨682025, by rfl⟩ : syracuseStep 909367 = 1364051) B1364051
theorem B7004225 : Blo 908576 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B909387 : Blo 908576 909387 := bstep (se 1 (by rfl) ⟨682040, by rfl⟩ : syracuseStep 909387 = 1364081) B1364081
theorem B909399 : Blo 908576 909399 := bstep (se 1 (by rfl) ⟨682049, by rfl⟩ : syracuseStep 909399 = 1364099) B1364099
theorem B909419 : Blo 908576 909419 := bstep (se 1 (by rfl) ⟨682064, by rfl⟩ : syracuseStep 909419 = 1364129) B1364129
theorem B909431 : Blo 908576 909431 := bstep (se 1 (by rfl) ⟨682073, by rfl⟩ : syracuseStep 909431 = 1364147) B1364147
theorem B1728641 : Blo 908576 1728641 := bstep (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) B1296481
theorem B4382851 : Blo 908576 4382851 := bstep (se 1 (by rfl) ⟨3287138, by rfl⟩ : syracuseStep 4382851 = 6574277) B6574277
theorem B909451 : Blo 908576 909451 := bstep (se 1 (by rfl) ⟨682088, by rfl⟩ : syracuseStep 909451 = 1364177) B1364177
theorem B1368203 : Blo 908576 1368203 := bstep (se 1 (by rfl) ⟨1026152, by rfl⟩ : syracuseStep 1368203 = 2052305) B2052305
theorem B909463 : Blo 908576 909463 := bstep (se 1 (by rfl) ⟨682097, by rfl⟩ : syracuseStep 909463 = 1364195) B1364195
theorem B1368215 : Blo 908576 1368215 := bstep (se 1 (by rfl) ⟨1026161, by rfl⟩ : syracuseStep 1368215 = 2052323) B2052323
theorem B909483 : Blo 908576 909483 := bstep (se 1 (by rfl) ⟨682112, by rfl⟩ : syracuseStep 909483 = 1364225) B1364225
theorem B909495 : Blo 908576 909495 := bstep (se 1 (by rfl) ⟨682121, by rfl⟩ : syracuseStep 909495 = 1364243) B1364243
theorem B909515 : Blo 908576 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B909527 : Blo 908576 909527 := bstep (se 1 (by rfl) ⟨682145, by rfl⟩ : syracuseStep 909527 = 1364291) B1364291
theorem B1368281 : Blo 908576 1368281 := bstep (se 2 (by rfl) ⟨513105, by rfl⟩ : syracuseStep 1368281 = 1026211) B1026211
theorem B3072221 : Blo 908576 3072221 := bstep (se 3 (by rfl) ⟨576041, by rfl⟩ : syracuseStep 3072221 = 1152083) B1152083
theorem B909547 : Blo 908576 909547 := bstep (se 1 (by rfl) ⟨682160, by rfl⟩ : syracuseStep 909547 = 1364321) B1364321
theorem B909559 : Blo 908576 909559 := bstep (se 1 (by rfl) ⟨682169, by rfl⟩ : syracuseStep 909559 = 1364339) B1364339
theorem B909579 : Blo 908576 909579 := bstep (se 1 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 909579 = 1364369) B1364369
theorem B909591 : Blo 908576 909591 := bstep (se 1 (by rfl) ⟨682193, by rfl⟩ : syracuseStep 909591 = 1364387) B1364387
theorem B1728793 : Blo 908576 1728793 := bstep (se 2 (by rfl) ⟨648297, by rfl⟩ : syracuseStep 1728793 = 1296595) B1296595
theorem B909611 : Blo 908576 909611 := bstep (se 1 (by rfl) ⟨682208, by rfl⟩ : syracuseStep 909611 = 1364417) B1364417
theorem B909623 : Blo 908576 909623 := bstep (se 1 (by rfl) ⟨682217, by rfl⟩ : syracuseStep 909623 = 1364435) B1364435
theorem B909643 : Blo 908576 909643 := bstep (se 1 (by rfl) ⟨682232, by rfl⟩ : syracuseStep 909643 = 1364465) B1364465
theorem B1368395 : Blo 908576 1368395 := bstep (se 1 (by rfl) ⟨1026296, by rfl⟩ : syracuseStep 1368395 = 2052593) B2052593
theorem B909655 : Blo 908576 909655 := bstep (se 1 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 909655 = 1364483) B1364483
theorem B1368407 : Blo 908576 1368407 := bstep (se 1 (by rfl) ⟨1026305, by rfl⟩ : syracuseStep 1368407 = 2052611) B2052611
theorem B909675 : Blo 908576 909675 := bstep (se 1 (by rfl) ⟨682256, by rfl⟩ : syracuseStep 909675 = 1364513) B1364513
theorem B909687 : Blo 908576 909687 := bstep (se 1 (by rfl) ⟨682265, by rfl⟩ : syracuseStep 909687 = 1364531) B1364531
theorem B909707 : Blo 908576 909707 := bstep (se 1 (by rfl) ⟨682280, by rfl⟩ : syracuseStep 909707 = 1364561) B1364561
theorem B909719 : Blo 908576 909719 := bstep (se 1 (by rfl) ⟨682289, by rfl⟩ : syracuseStep 909719 = 1364579) B1364579
theorem B1368473 : Blo 908576 1368473 := bstep (se 2 (by rfl) ⟨513177, by rfl⟩ : syracuseStep 1368473 = 1026355) B1026355
theorem B909739 : Blo 908576 909739 := bstep (se 1 (by rfl) ⟨682304, by rfl⟩ : syracuseStep 909739 = 1364609) B1364609
theorem B909751 : Blo 908576 909751 := bstep (se 1 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 909751 = 1364627) B1364627
theorem B909771 : Blo 908576 909771 := bstep (se 1 (by rfl) ⟨682328, by rfl⟩ : syracuseStep 909771 = 1364657) B1364657
theorem B909783 : Blo 908576 909783 := bstep (se 1 (by rfl) ⟨682337, by rfl⟩ : syracuseStep 909783 = 1364675) B1364675
theorem B909803 : Blo 908576 909803 := bstep (se 1 (by rfl) ⟨682352, by rfl⟩ : syracuseStep 909803 = 1364705) B1364705
theorem B909815 : Blo 908576 909815 := bstep (se 1 (by rfl) ⟨682361, by rfl⟩ : syracuseStep 909815 = 1364723) B1364723
theorem B909835 : Blo 908576 909835 := bstep (se 1 (by rfl) ⟨682376, by rfl⟩ : syracuseStep 909835 = 1364753) B1364753
theorem B1368587 : Blo 908576 1368587 := bstep (se 1 (by rfl) ⟨1026440, by rfl⟩ : syracuseStep 1368587 = 2052881) B2052881
theorem B4612625 : Blo 908576 4612625 := bstep (se 2 (by rfl) ⟨1729734, by rfl⟩ : syracuseStep 4612625 = 3459469) B3459469
theorem B909847 : Blo 908576 909847 := bstep (se 1 (by rfl) ⟨682385, by rfl⟩ : syracuseStep 909847 = 1364771) B1364771
theorem B1368599 : Blo 908576 1368599 := bstep (se 1 (by rfl) ⟨1026449, by rfl⟩ : syracuseStep 1368599 = 2052899) B2052899
theorem B909867 : Blo 908576 909867 := bstep (se 1 (by rfl) ⟨682400, by rfl⟩ : syracuseStep 909867 = 1364801) B1364801
theorem B909879 : Blo 908576 909879 := bstep (se 1 (by rfl) ⟨682409, by rfl⟩ : syracuseStep 909879 = 1364819) B1364819
theorem B909899 : Blo 908576 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B909911 : Blo 908576 909911 := bstep (se 1 (by rfl) ⟨682433, by rfl⟩ : syracuseStep 909911 = 1364867) B1364867
theorem B1368665 : Blo 908576 1368665 := bstep (se 2 (by rfl) ⟨513249, by rfl⟩ : syracuseStep 1368665 = 1026499) B1026499
theorem B909931 : Blo 908576 909931 := bstep (se 1 (by rfl) ⟨682448, by rfl⟩ : syracuseStep 909931 = 1364897) B1364897
theorem B909943 : Blo 908576 909943 := bstep (se 1 (by rfl) ⟨682457, by rfl⟩ : syracuseStep 909943 = 1364915) B1364915
theorem B909963 : Blo 908576 909963 := bstep (se 1 (by rfl) ⟨682472, by rfl⟩ : syracuseStep 909963 = 1364945) B1364945
theorem B909975 : Blo 908576 909975 := bstep (se 1 (by rfl) ⟨682481, by rfl⟩ : syracuseStep 909975 = 1364963) B1364963
theorem B909995 : Blo 908576 909995 := bstep (se 1 (by rfl) ⟨682496, by rfl⟩ : syracuseStep 909995 = 1364993) B1364993
theorem B6906545 : Blo 908576 6906545 := bstep (se 2 (by rfl) ⟨2589954, by rfl⟩ : syracuseStep 6906545 = 5179909) B5179909
theorem B4612787 : Blo 908576 4612787 := bstep (se 1 (by rfl) ⟨3459590, by rfl⟩ : syracuseStep 4612787 = 6919181) B6919181
theorem B910007 : Blo 908576 910007 := bstep (se 1 (by rfl) ⟨682505, by rfl⟩ : syracuseStep 910007 = 1365011) B1365011
theorem B910027 : Blo 908576 910027 := bstep (se 1 (by rfl) ⟨682520, by rfl⟩ : syracuseStep 910027 = 1365041) B1365041
theorem B1368779 : Blo 908576 1368779 := bstep (se 1 (by rfl) ⟨1026584, by rfl⟩ : syracuseStep 1368779 = 2053169) B2053169
theorem B910039 : Blo 908576 910039 := bstep (se 1 (by rfl) ⟨682529, by rfl⟩ : syracuseStep 910039 = 1365059) B1365059
theorem B1368791 : Blo 908576 1368791 := bstep (se 1 (by rfl) ⟨1026593, by rfl⟩ : syracuseStep 1368791 = 2053187) B2053187
theorem B910059 : Blo 908576 910059 := bstep (se 1 (by rfl) ⟨682544, by rfl⟩ : syracuseStep 910059 = 1365089) B1365089
theorem B910071 : Blo 908576 910071 := bstep (se 1 (by rfl) ⟨682553, by rfl⟩ : syracuseStep 910071 = 1365107) B1365107
theorem B910091 : Blo 908576 910091 := bstep (se 1 (by rfl) ⟨682568, by rfl⟩ : syracuseStep 910091 = 1365137) B1365137
theorem B910103 : Blo 908576 910103 := bstep (se 1 (by rfl) ⟨682577, by rfl⟩ : syracuseStep 910103 = 1365155) B1365155
theorem B1368857 : Blo 908576 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B910123 : Blo 908576 910123 := bstep (se 1 (by rfl) ⟨682592, by rfl⟩ : syracuseStep 910123 = 1365185) B1365185
theorem B910135 : Blo 908576 910135 := bstep (se 1 (by rfl) ⟨682601, by rfl⟩ : syracuseStep 910135 = 1365203) B1365203
theorem B910155 : Blo 908576 910155 := bstep (se 1 (by rfl) ⟨682616, by rfl⟩ : syracuseStep 910155 = 1365233) B1365233
theorem B910167 : Blo 908576 910167 := bstep (se 1 (by rfl) ⟨682625, by rfl⟩ : syracuseStep 910167 = 1365251) B1365251
theorem B7791461 : Blo 908576 7791461 := bstep (se 4 (by rfl) ⟨730449, by rfl⟩ : syracuseStep 7791461 = 1460899) B1460899
theorem B910187 : Blo 908576 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B910199 : Blo 908576 910199 := bstep (se 1 (by rfl) ⟨682649, by rfl⟩ : syracuseStep 910199 = 1365299) B1365299
theorem B910219 : Blo 908576 910219 := bstep (se 1 (by rfl) ⟨682664, by rfl⟩ : syracuseStep 910219 = 1365329) B1365329
theorem B910231 : Blo 908576 910231 := bstep (se 1 (by rfl) ⟨682673, by rfl⟩ : syracuseStep 910231 = 1365347) B1365347
theorem B910251 : Blo 908576 910251 := bstep (se 1 (by rfl) ⟨682688, by rfl⟩ : syracuseStep 910251 = 1365377) B1365377
theorem B910263 : Blo 908576 910263 := bstep (se 1 (by rfl) ⟨682697, by rfl⟩ : syracuseStep 910263 = 1365395) B1365395
theorem B910283 : Blo 908576 910283 := bstep (se 1 (by rfl) ⟨682712, by rfl⟩ : syracuseStep 910283 = 1365425) B1365425
theorem B910295 : Blo 908576 910295 := bstep (se 1 (by rfl) ⟨682721, by rfl⟩ : syracuseStep 910295 = 1365443) B1365443
theorem B910315 : Blo 908576 910315 := bstep (se 1 (by rfl) ⟨682736, by rfl⟩ : syracuseStep 910315 = 1365473) B1365473
theorem B910327 : Blo 908576 910327 := bstep (se 1 (by rfl) ⟨682745, by rfl⟩ : syracuseStep 910327 = 1365491) B1365491
theorem B910347 : Blo 908576 910347 := bstep (se 1 (by rfl) ⟨682760, by rfl⟩ : syracuseStep 910347 = 1365521) B1365521
theorem B910359 : Blo 908576 910359 := bstep (se 1 (by rfl) ⟨682769, by rfl⟩ : syracuseStep 910359 = 1365539) B1365539
theorem B910379 : Blo 908576 910379 := bstep (se 1 (by rfl) ⟨682784, by rfl⟩ : syracuseStep 910379 = 1365569) B1365569
theorem B910391 : Blo 908576 910391 := bstep (se 1 (by rfl) ⟨682793, by rfl⟩ : syracuseStep 910391 = 1365587) B1365587
theorem B910411 : Blo 908576 910411 := bstep (se 1 (by rfl) ⟨682808, by rfl⟩ : syracuseStep 910411 = 1365617) B1365617
theorem B910423 : Blo 908576 910423 := bstep (se 1 (by rfl) ⟨682817, by rfl⟩ : syracuseStep 910423 = 1365635) B1365635
theorem B3892313 : Blo 908576 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B910443 : Blo 908576 910443 := bstep (se 1 (by rfl) ⟨682832, by rfl⟩ : syracuseStep 910443 = 1365665) B1365665
theorem B910455 : Blo 908576 910455 := bstep (se 1 (by rfl) ⟨682841, by rfl⟩ : syracuseStep 910455 = 1365683) B1365683
theorem B910475 : Blo 908576 910475 := bstep (se 1 (by rfl) ⟨682856, by rfl⟩ : syracuseStep 910475 = 1365713) B1365713
theorem B6907031 : Blo 908576 6907031 := bstep (se 1 (by rfl) ⟨5180273, by rfl⟩ : syracuseStep 6907031 = 10360547) B10360547
theorem B910487 : Blo 908576 910487 := bstep (se 1 (by rfl) ⟨682865, by rfl⟩ : syracuseStep 910487 = 1365731) B1365731
theorem B910507 : Blo 908576 910507 := bstep (se 1 (by rfl) ⟨682880, by rfl⟩ : syracuseStep 910507 = 1365761) B1365761
theorem B910519 : Blo 908576 910519 := bstep (se 1 (by rfl) ⟨682889, by rfl⟩ : syracuseStep 910519 = 1365779) B1365779
theorem B910539 : Blo 908576 910539 := bstep (se 1 (by rfl) ⟨682904, by rfl⟩ : syracuseStep 910539 = 1365809) B1365809
theorem B910551 : Blo 908576 910551 := bstep (se 1 (by rfl) ⟨682913, by rfl⟩ : syracuseStep 910551 = 1365827) B1365827
theorem B910571 : Blo 908576 910571 := bstep (se 1 (by rfl) ⟨682928, by rfl⟩ : syracuseStep 910571 = 1365857) B1365857
theorem B910583 : Blo 908576 910583 := bstep (se 1 (by rfl) ⟨682937, by rfl⟩ : syracuseStep 910583 = 1365875) B1365875
theorem B910603 : Blo 908576 910603 := bstep (se 1 (by rfl) ⟨682952, by rfl⟩ : syracuseStep 910603 = 1365905) B1365905
theorem B910615 : Blo 908576 910615 := bstep (se 1 (by rfl) ⟨682961, by rfl⟩ : syracuseStep 910615 = 1365923) B1365923
theorem B910635 : Blo 908576 910635 := bstep (se 1 (by rfl) ⟨682976, by rfl⟩ : syracuseStep 910635 = 1365953) B1365953
theorem B910647 : Blo 908576 910647 := bstep (se 1 (by rfl) ⟨682985, by rfl⟩ : syracuseStep 910647 = 1365971) B1365971
theorem B3073355 : Blo 908576 3073355 := bstep (se 1 (by rfl) ⟨2305016, by rfl⟩ : syracuseStep 3073355 = 4610033) B4610033
theorem B910667 : Blo 908576 910667 := bstep (se 1 (by rfl) ⟨683000, by rfl⟩ : syracuseStep 910667 = 1366001) B1366001
theorem B910679 : Blo 908576 910679 := bstep (se 1 (by rfl) ⟨683009, by rfl⟩ : syracuseStep 910679 = 1366019) B1366019
theorem B910699 : Blo 908576 910699 := bstep (se 1 (by rfl) ⟨683024, by rfl⟩ : syracuseStep 910699 = 1366049) B1366049
theorem B910711 : Blo 908576 910711 := bstep (se 1 (by rfl) ⟨683033, by rfl⟩ : syracuseStep 910711 = 1366067) B1366067
theorem B1533323 : Blo 908576 1533323 := bstep (se 1 (by rfl) ⟨1149992, by rfl⟩ : syracuseStep 1533323 = 2299985) B2299985
theorem B910731 : Blo 908576 910731 := bstep (se 1 (by rfl) ⟨683048, by rfl⟩ : syracuseStep 910731 = 1366097) B1366097
theorem B910743 : Blo 908576 910743 := bstep (se 1 (by rfl) ⟨683057, by rfl⟩ : syracuseStep 910743 = 1366115) B1366115
theorem B3696023 : Blo 908576 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B910763 : Blo 908576 910763 := bstep (se 1 (by rfl) ⟨683072, by rfl⟩ : syracuseStep 910763 = 1366145) B1366145
theorem B910775 : Blo 908576 910775 := bstep (se 1 (by rfl) ⟨683081, by rfl⟩ : syracuseStep 910775 = 1366163) B1366163
theorem B910795 : Blo 908576 910795 := bstep (se 1 (by rfl) ⟨683096, by rfl⟩ : syracuseStep 910795 = 1366193) B1366193
theorem B910807 : Blo 908576 910807 := bstep (se 1 (by rfl) ⟨683105, by rfl⟩ : syracuseStep 910807 = 1366211) B1366211
theorem B910827 : Blo 908576 910827 := bstep (se 1 (by rfl) ⟨683120, by rfl⟩ : syracuseStep 910827 = 1366241) B1366241
theorem B910839 : Blo 908576 910839 := bstep (se 1 (by rfl) ⟨683129, by rfl⟩ : syracuseStep 910839 = 1366259) B1366259
theorem B1533451 : Blo 908576 1533451 := bstep (se 1 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 1533451 = 2300177) B2300177
theorem B910859 : Blo 908576 910859 := bstep (se 1 (by rfl) ⟨683144, by rfl⟩ : syracuseStep 910859 = 1366289) B1366289
theorem B7792145 : Blo 908576 7792145 := bstep (se 2 (by rfl) ⟨2922054, by rfl⟩ : syracuseStep 7792145 = 5844109) B5844109
theorem B910871 : Blo 908576 910871 := bstep (se 1 (by rfl) ⟨683153, by rfl⟩ : syracuseStep 910871 = 1366307) B1366307
theorem B910891 : Blo 908576 910891 := bstep (se 1 (by rfl) ⟨683168, by rfl⟩ : syracuseStep 910891 = 1366337) B1366337
theorem B1730099 : Blo 908576 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B910903 : Blo 908576 910903 := bstep (se 1 (by rfl) ⟨683177, by rfl⟩ : syracuseStep 910903 = 1366355) B1366355
theorem B910923 : Blo 908576 910923 := bstep (se 1 (by rfl) ⟨683192, by rfl⟩ : syracuseStep 910923 = 1366385) B1366385
theorem B910935 : Blo 908576 910935 := bstep (se 1 (by rfl) ⟨683201, by rfl⟩ : syracuseStep 910935 = 1366403) B1366403
theorem B3073625 : Blo 908576 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B910955 : Blo 908576 910955 := bstep (se 1 (by rfl) ⟨683216, by rfl⟩ : syracuseStep 910955 = 1366433) B1366433
theorem B910967 : Blo 908576 910967 := bstep (se 1 (by rfl) ⟨683225, by rfl⟩ : syracuseStep 910967 = 1366451) B1366451
theorem B910987 : Blo 908576 910987 := bstep (se 1 (by rfl) ⟨683240, by rfl⟩ : syracuseStep 910987 = 1366481) B1366481
theorem B910999 : Blo 908576 910999 := bstep (se 1 (by rfl) ⟨683249, by rfl⟩ : syracuseStep 910999 = 1366499) B1366499
theorem B1533593 : Blo 908576 1533593 := bstep (se 2 (by rfl) ⟨575097, by rfl⟩ : syracuseStep 1533593 = 1150195) B1150195
theorem B911019 : Blo 908576 911019 := bstep (se 1 (by rfl) ⟨683264, by rfl⟩ : syracuseStep 911019 = 1366529) B1366529
theorem B911031 : Blo 908576 911031 := bstep (se 1 (by rfl) ⟨683273, by rfl⟩ : syracuseStep 911031 = 1366547) B1366547
theorem B911051 : Blo 908576 911051 := bstep (se 1 (by rfl) ⟨683288, by rfl⟩ : syracuseStep 911051 = 1366577) B1366577
theorem B1730251 : Blo 908576 1730251 := bstep (se 1 (by rfl) ⟨1297688, by rfl⟩ : syracuseStep 1730251 = 2595377) B2595377
theorem B911063 : Blo 908576 911063 := bstep (se 1 (by rfl) ⟨683297, by rfl⟩ : syracuseStep 911063 = 1366595) B1366595
theorem B911083 : Blo 908576 911083 := bstep (se 1 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 911083 = 1366625) B1366625
theorem B14739185 : Blo 908576 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B911095 : Blo 908576 911095 := bstep (se 1 (by rfl) ⟨683321, by rfl⟩ : syracuseStep 911095 = 1366643) B1366643
theorem B911115 : Blo 908576 911115 := bstep (se 1 (by rfl) ⟨683336, by rfl⟩ : syracuseStep 911115 = 1366673) B1366673
theorem B911127 : Blo 908576 911127 := bstep (se 1 (by rfl) ⟨683345, by rfl⟩ : syracuseStep 911127 = 1366691) B1366691
theorem B1533721 : Blo 908576 1533721 := bstep (se 2 (by rfl) ⟨575145, by rfl⟩ : syracuseStep 1533721 = 1150291) B1150291
theorem B911147 : Blo 908576 911147 := bstep (se 1 (by rfl) ⟨683360, by rfl⟩ : syracuseStep 911147 = 1366721) B1366721
theorem B911159 : Blo 908576 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B911179 : Blo 908576 911179 := bstep (se 1 (by rfl) ⟨683384, by rfl⟩ : syracuseStep 911179 = 1366769) B1366769
theorem B911191 : Blo 908576 911191 := bstep (se 1 (by rfl) ⟨683393, by rfl⟩ : syracuseStep 911191 = 1366787) B1366787
theorem B911211 : Blo 908576 911211 := bstep (se 1 (by rfl) ⟨683408, by rfl⟩ : syracuseStep 911211 = 1366817) B1366817
theorem B911223 : Blo 908576 911223 := bstep (se 1 (by rfl) ⟨683417, by rfl⟩ : syracuseStep 911223 = 1366835) B1366835
theorem B911243 : Blo 908576 911243 := bstep (se 1 (by rfl) ⟨683432, by rfl⟩ : syracuseStep 911243 = 1366865) B1366865
theorem B911255 : Blo 908576 911255 := bstep (se 1 (by rfl) ⟨683441, by rfl⟩ : syracuseStep 911255 = 1366883) B1366883
theorem B911275 : Blo 908576 911275 := bstep (se 1 (by rfl) ⟨683456, by rfl⟩ : syracuseStep 911275 = 1366913) B1366913
theorem B911287 : Blo 908576 911287 := bstep (se 1 (by rfl) ⟨683465, by rfl⟩ : syracuseStep 911287 = 1366931) B1366931
theorem B911307 : Blo 908576 911307 := bstep (se 1 (by rfl) ⟨683480, by rfl⟩ : syracuseStep 911307 = 1366961) B1366961
theorem B911319 : Blo 908576 911319 := bstep (se 1 (by rfl) ⟨683489, by rfl⟩ : syracuseStep 911319 = 1366979) B1366979
theorem B911339 : Blo 908576 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B911351 : Blo 908576 911351 := bstep (se 1 (by rfl) ⟨683513, by rfl⟩ : syracuseStep 911351 = 1367027) B1367027
theorem B911371 : Blo 908576 911371 := bstep (se 1 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 911371 = 1367057) B1367057
theorem B911383 : Blo 908576 911383 := bstep (se 1 (by rfl) ⟨683537, by rfl⟩ : syracuseStep 911383 = 1367075) B1367075
theorem B1730585 : Blo 908576 1730585 := bstep (se 2 (by rfl) ⟨648969, by rfl⟩ : syracuseStep 1730585 = 1297939) B1297939
theorem B911403 : Blo 908576 911403 := bstep (se 1 (by rfl) ⟨683552, by rfl⟩ : syracuseStep 911403 = 1367105) B1367105
theorem B911415 : Blo 908576 911415 := bstep (se 1 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 911415 = 1367123) B1367123
theorem B911435 : Blo 908576 911435 := bstep (se 1 (by rfl) ⟨683576, by rfl⟩ : syracuseStep 911435 = 1367153) B1367153
theorem B911447 : Blo 908576 911447 := bstep (se 1 (by rfl) ⟨683585, by rfl⟩ : syracuseStep 911447 = 1367171) B1367171
theorem B911467 : Blo 908576 911467 := bstep (se 1 (by rfl) ⟨683600, by rfl⟩ : syracuseStep 911467 = 1367201) B1367201
theorem B911479 : Blo 908576 911479 := bstep (se 1 (by rfl) ⟨683609, by rfl⟩ : syracuseStep 911479 = 1367219) B1367219
theorem B911499 : Blo 908576 911499 := bstep (se 1 (by rfl) ⟨683624, by rfl⟩ : syracuseStep 911499 = 1367249) B1367249
theorem B911511 : Blo 908576 911511 := bstep (se 1 (by rfl) ⟨683633, by rfl⟩ : syracuseStep 911511 = 1367267) B1367267
theorem B911531 : Blo 908576 911531 := bstep (se 1 (by rfl) ⟨683648, by rfl⟩ : syracuseStep 911531 = 1367297) B1367297
theorem B911543 : Blo 908576 911543 := bstep (se 1 (by rfl) ⟨683657, by rfl⟩ : syracuseStep 911543 = 1367315) B1367315
theorem B911563 : Blo 908576 911563 := bstep (se 1 (by rfl) ⟨683672, by rfl⟩ : syracuseStep 911563 = 1367345) B1367345
theorem B911575 : Blo 908576 911575 := bstep (se 1 (by rfl) ⟨683681, by rfl⟩ : syracuseStep 911575 = 1367363) B1367363
theorem B911595 : Blo 908576 911595 := bstep (se 1 (by rfl) ⟨683696, by rfl⟩ : syracuseStep 911595 = 1367393) B1367393
theorem B911607 : Blo 908576 911607 := bstep (se 1 (by rfl) ⟨683705, by rfl⟩ : syracuseStep 911607 = 1367411) B1367411
theorem B911627 : Blo 908576 911627 := bstep (se 1 (by rfl) ⟨683720, by rfl⟩ : syracuseStep 911627 = 1367441) B1367441
theorem B3074327 : Blo 908576 3074327 := bstep (se 1 (by rfl) ⟨2305745, by rfl⟩ : syracuseStep 3074327 = 4611491) B4611491
theorem B911639 : Blo 908576 911639 := bstep (se 1 (by rfl) ⟨683729, by rfl⟩ : syracuseStep 911639 = 1367459) B1367459
theorem B911659 : Blo 908576 911659 := bstep (se 1 (by rfl) ⟨683744, by rfl⟩ : syracuseStep 911659 = 1367489) B1367489
theorem B911671 : Blo 908576 911671 := bstep (se 1 (by rfl) ⟨683753, by rfl⟩ : syracuseStep 911671 = 1367507) B1367507
theorem B3893579 : Blo 908576 3893579 := bstep (se 1 (by rfl) ⟨2920184, by rfl⟩ : syracuseStep 3893579 = 5840369) B5840369
theorem B911691 : Blo 908576 911691 := bstep (se 1 (by rfl) ⟨683768, by rfl⟩ : syracuseStep 911691 = 1367537) B1367537
theorem B1534295 : Blo 908576 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B911703 : Blo 908576 911703 := bstep (se 1 (by rfl) ⟨683777, by rfl⟩ : syracuseStep 911703 = 1367555) B1367555
theorem B911723 : Blo 908576 911723 := bstep (se 1 (by rfl) ⟨683792, by rfl⟩ : syracuseStep 911723 = 1367585) B1367585
theorem B911735 : Blo 908576 911735 := bstep (se 1 (by rfl) ⟨683801, by rfl⟩ : syracuseStep 911735 = 1367603) B1367603
theorem B911755 : Blo 908576 911755 := bstep (se 1 (by rfl) ⟨683816, by rfl⟩ : syracuseStep 911755 = 1367633) B1367633
theorem B911767 : Blo 908576 911767 := bstep (se 1 (by rfl) ⟨683825, by rfl⟩ : syracuseStep 911767 = 1367651) B1367651
theorem B911787 : Blo 908576 911787 := bstep (se 1 (by rfl) ⟨683840, by rfl⟩ : syracuseStep 911787 = 1367681) B1367681
theorem B911799 : Blo 908576 911799 := bstep (se 1 (by rfl) ⟨683849, by rfl⟩ : syracuseStep 911799 = 1367699) B1367699
theorem B911819 : Blo 908576 911819 := bstep (se 1 (by rfl) ⟨683864, by rfl⟩ : syracuseStep 911819 = 1367729) B1367729
theorem B1534423 : Blo 908576 1534423 := bstep (se 1 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 1534423 = 2301635) B2301635
theorem B911831 : Blo 908576 911831 := bstep (se 1 (by rfl) ⟨683873, by rfl⟩ : syracuseStep 911831 = 1367747) B1367747
theorem B911851 : Blo 908576 911851 := bstep (se 1 (by rfl) ⟨683888, by rfl⟩ : syracuseStep 911851 = 1367777) B1367777
theorem B911863 : Blo 908576 911863 := bstep (se 1 (by rfl) ⟨683897, by rfl⟩ : syracuseStep 911863 = 1367795) B1367795
theorem B4155907 : Blo 908576 4155907 := bstep (se 1 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 4155907 = 6233861) B6233861
theorem B911883 : Blo 908576 911883 := bstep (se 1 (by rfl) ⟨683912, by rfl⟩ : syracuseStep 911883 = 1367825) B1367825
theorem B911895 : Blo 908576 911895 := bstep (se 1 (by rfl) ⟨683921, by rfl⟩ : syracuseStep 911895 = 1367843) B1367843
theorem B911915 : Blo 908576 911915 := bstep (se 1 (by rfl) ⟨683936, by rfl⟩ : syracuseStep 911915 = 1367873) B1367873
theorem B911927 : Blo 908576 911927 := bstep (se 1 (by rfl) ⟨683945, by rfl⟩ : syracuseStep 911927 = 1367891) B1367891
theorem B4614731 : Blo 908576 4614731 := bstep (se 1 (by rfl) ⟨3461048, by rfl⟩ : syracuseStep 4614731 = 6922097) B6922097
theorem B911947 : Blo 908576 911947 := bstep (se 1 (by rfl) ⟨683960, by rfl⟩ : syracuseStep 911947 = 1367921) B1367921
theorem B911959 : Blo 908576 911959 := bstep (se 1 (by rfl) ⟨683969, by rfl⟩ : syracuseStep 911959 = 1367939) B1367939
theorem B911979 : Blo 908576 911979 := bstep (se 1 (by rfl) ⟨683984, by rfl⟩ : syracuseStep 911979 = 1367969) B1367969
theorem B911991 : Blo 908576 911991 := bstep (se 1 (by rfl) ⟨683993, by rfl⟩ : syracuseStep 911991 = 1367987) B1367987
theorem B912011 : Blo 908576 912011 := bstep (se 1 (by rfl) ⟨684008, by rfl⟩ : syracuseStep 912011 = 1368017) B1368017
theorem B1731223 : Blo 908576 1731223 := bstep (se 1 (by rfl) ⟨1298417, by rfl⟩ : syracuseStep 1731223 = 2596835) B2596835
theorem B912023 : Blo 908576 912023 := bstep (se 1 (by rfl) ⟨684017, by rfl⟩ : syracuseStep 912023 = 1368035) B1368035
theorem B912043 : Blo 908576 912043 := bstep (se 1 (by rfl) ⟨684032, by rfl⟩ : syracuseStep 912043 = 1368065) B1368065
theorem B3893939 : Blo 908576 3893939 := bstep (se 1 (by rfl) ⟨2920454, by rfl⟩ : syracuseStep 3893939 = 5840909) B5840909
theorem B912055 : Blo 908576 912055 := bstep (se 1 (by rfl) ⟨684041, by rfl⟩ : syracuseStep 912055 = 1368083) B1368083
theorem B912075 : Blo 908576 912075 := bstep (se 1 (by rfl) ⟨684056, by rfl⟩ : syracuseStep 912075 = 1368113) B1368113
theorem B912087 : Blo 908576 912087 := bstep (se 1 (by rfl) ⟨684065, by rfl⟩ : syracuseStep 912087 = 1368131) B1368131
theorem B912107 : Blo 908576 912107 := bstep (se 1 (by rfl) ⟨684080, by rfl⟩ : syracuseStep 912107 = 1368161) B1368161
theorem B912119 : Blo 908576 912119 := bstep (se 1 (by rfl) ⟨684089, by rfl⟩ : syracuseStep 912119 = 1368179) B1368179
theorem B912139 : Blo 908576 912139 := bstep (se 1 (by rfl) ⟨684104, by rfl⟩ : syracuseStep 912139 = 1368209) B1368209
theorem B912151 : Blo 908576 912151 := bstep (se 1 (by rfl) ⟨684113, by rfl⟩ : syracuseStep 912151 = 1368227) B1368227
theorem B912171 : Blo 908576 912171 := bstep (se 1 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 912171 = 1368257) B1368257
theorem B3074867 : Blo 908576 3074867 := bstep (se 1 (by rfl) ⟨2306150, by rfl⟩ : syracuseStep 3074867 = 4612301) B4612301
theorem B912183 : Blo 908576 912183 := bstep (se 1 (by rfl) ⟨684137, by rfl⟩ : syracuseStep 912183 = 1368275) B1368275
theorem B912203 : Blo 908576 912203 := bstep (se 1 (by rfl) ⟨684152, by rfl⟩ : syracuseStep 912203 = 1368305) B1368305
theorem B912215 : Blo 908576 912215 := bstep (se 1 (by rfl) ⟨684161, by rfl⟩ : syracuseStep 912215 = 1368323) B1368323
theorem B912235 : Blo 908576 912235 := bstep (se 1 (by rfl) ⟨684176, by rfl⟩ : syracuseStep 912235 = 1368353) B1368353
theorem B912247 : Blo 908576 912247 := bstep (se 1 (by rfl) ⟨684185, by rfl⟩ : syracuseStep 912247 = 1368371) B1368371
theorem B912267 : Blo 908576 912267 := bstep (se 1 (by rfl) ⟨684200, by rfl⟩ : syracuseStep 912267 = 1368401) B1368401
theorem B912279 : Blo 908576 912279 := bstep (se 1 (by rfl) ⟨684209, by rfl⟩ : syracuseStep 912279 = 1368419) B1368419
theorem B912299 : Blo 908576 912299 := bstep (se 1 (by rfl) ⟨684224, by rfl⟩ : syracuseStep 912299 = 1368449) B1368449
theorem B912311 : Blo 908576 912311 := bstep (se 1 (by rfl) ⟨684233, by rfl⟩ : syracuseStep 912311 = 1368467) B1368467
theorem B912331 : Blo 908576 912331 := bstep (se 1 (by rfl) ⟨684248, by rfl⟩ : syracuseStep 912331 = 1368497) B1368497
theorem B912343 : Blo 908576 912343 := bstep (se 1 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 912343 = 1368515) B1368515
theorem B4156381 : Blo 908576 4156381 := bstep (se 3 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 4156381 = 1558643) B1558643
theorem B912363 : Blo 908576 912363 := bstep (se 1 (by rfl) ⟨684272, by rfl⟩ : syracuseStep 912363 = 1368545) B1368545
theorem B912375 : Blo 908576 912375 := bstep (se 1 (by rfl) ⟨684281, by rfl⟩ : syracuseStep 912375 = 1368563) B1368563
theorem B912395 : Blo 908576 912395 := bstep (se 1 (by rfl) ⟨684296, by rfl⟩ : syracuseStep 912395 = 1368593) B1368593
theorem B912407 : Blo 908576 912407 := bstep (se 1 (by rfl) ⟨684305, by rfl⟩ : syracuseStep 912407 = 1368611) B1368611
theorem B912427 : Blo 908576 912427 := bstep (se 1 (by rfl) ⟨684320, by rfl⟩ : syracuseStep 912427 = 1368641) B1368641
theorem B912439 : Blo 908576 912439 := bstep (se 1 (by rfl) ⟨684329, by rfl⟩ : syracuseStep 912439 = 1368659) B1368659
theorem B3075137 : Blo 908576 3075137 := bstep (se 2 (by rfl) ⟨1153176, by rfl⟩ : syracuseStep 3075137 = 2306353) B2306353
theorem B1535051 : Blo 908576 1535051 := bstep (se 1 (by rfl) ⟨1151288, by rfl⟩ : syracuseStep 1535051 = 2302577) B2302577
theorem B912459 : Blo 908576 912459 := bstep (se 1 (by rfl) ⟨684344, by rfl⟩ : syracuseStep 912459 = 1368689) B1368689
theorem B912471 : Blo 908576 912471 := bstep (se 1 (by rfl) ⟨684353, by rfl⟩ : syracuseStep 912471 = 1368707) B1368707
theorem B912491 : Blo 908576 912491 := bstep (se 1 (by rfl) ⟨684368, by rfl⟩ : syracuseStep 912491 = 1368737) B1368737
theorem B912503 : Blo 908576 912503 := bstep (se 1 (by rfl) ⟨684377, by rfl⟩ : syracuseStep 912503 = 1368755) B1368755
theorem B912523 : Blo 908576 912523 := bstep (se 1 (by rfl) ⟨684392, by rfl⟩ : syracuseStep 912523 = 1368785) B1368785
theorem B912535 : Blo 908576 912535 := bstep (se 1 (by rfl) ⟨684401, by rfl⟩ : syracuseStep 912535 = 1368803) B1368803
theorem B912555 : Blo 908576 912555 := bstep (se 1 (by rfl) ⟨684416, by rfl⟩ : syracuseStep 912555 = 1368833) B1368833
theorem B912567 : Blo 908576 912567 := bstep (se 1 (by rfl) ⟨684425, by rfl⟩ : syracuseStep 912567 = 1368851) B1368851
theorem B1535179 : Blo 908576 1535179 := bstep (se 1 (by rfl) ⟨1151384, by rfl⟩ : syracuseStep 1535179 = 2302769) B2302769
theorem B3697937 : Blo 908576 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B3501377 : Blo 908576 3501377 := bstep (se 2 (by rfl) ⟨1313016, by rfl⟩ : syracuseStep 3501377 = 2626033) B2626033
theorem B10513729 : Blo 908576 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B1535321 : Blo 908576 1535321 := bstep (se 2 (by rfl) ⟨575745, by rfl⟩ : syracuseStep 1535321 = 1151491) B1151491
theorem B3698099 : Blo 908576 3698099 := bstep (se 1 (by rfl) ⟨2773574, by rfl⟩ : syracuseStep 3698099 = 5547149) B5547149
theorem B1732043 : Blo 908576 1732043 := bstep (se 1 (by rfl) ⟨1299032, by rfl⟩ : syracuseStep 1732043 = 2598065) B2598065
theorem B1535449 : Blo 908576 1535449 := bstep (se 2 (by rfl) ⟨575793, by rfl⟩ : syracuseStep 1535449 = 1151587) B1151587
theorem B1732097 : Blo 908576 1732097 := bstep (se 2 (by rfl) ⟨649536, by rfl⟩ : syracuseStep 1732097 = 1299073) B1299073
theorem B5926445 : Blo 908576 5926445 := bstep (se 3 (by rfl) ⟨1111208, by rfl⟩ : syracuseStep 5926445 = 2222417) B2222417
theorem B3075677 : Blo 908576 3075677 := bstep (se 3 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 3075677 = 1153379) B1153379
theorem B10350341 : Blo 908576 10350341 := bstep (se 4 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 10350341 = 1940689) B1940689
theorem B1536023 : Blo 908576 1536023 := bstep (se 1 (by rfl) ⟨1152017, by rfl⟩ : syracuseStep 1536023 = 2304035) B2304035
theorem B3371153 : Blo 908576 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B6549655 : Blo 908576 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B1536151 : Blo 908576 1536151 := bstep (se 1 (by rfl) ⟨1152113, by rfl⟩ : syracuseStep 1536151 = 2304227) B2304227
theorem B4616513 : Blo 908576 4616513 := bstep (se 2 (by rfl) ⟨1731192, by rfl⟩ : syracuseStep 4616513 = 3462385) B3462385
theorem B3502595 : Blo 908576 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B3699265 : Blo 908576 3699265 := bstep (se 2 (by rfl) ⟨1387224, by rfl⟩ : syracuseStep 3699265 = 2774449) B2774449
theorem B3076811 : Blo 908576 3076811 := bstep (se 1 (by rfl) ⟨2307608, by rfl⟩ : syracuseStep 3076811 = 4615217) B4615217
theorem B8745677 : Blo 908576 8745677 := bstep (se 3 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 8745677 = 3279629) B3279629
theorem B1536779 : Blo 908576 1536779 := bstep (se 1 (by rfl) ⟨1152584, by rfl⟩ : syracuseStep 1536779 = 2305169) B2305169
theorem B1536907 : Blo 908576 1536907 := bstep (se 1 (by rfl) ⟨1152680, by rfl⟩ : syracuseStep 1536907 = 2305361) B2305361
theorem B2913175 : Blo 908576 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B3077081 : Blo 908576 3077081 := bstep (se 2 (by rfl) ⟨1153905, by rfl⟩ : syracuseStep 3077081 = 2307811) B2307811
theorem B1537049 : Blo 908576 1537049 := bstep (se 2 (by rfl) ⟨576393, by rfl⟩ : syracuseStep 1537049 = 1152787) B1152787
theorem B8746019 : Blo 908576 8746019 := bstep (se 1 (by rfl) ⟨6559514, by rfl⟩ : syracuseStep 8746019 = 13119029) B13119029
theorem B1537177 : Blo 908576 1537177 := bstep (se 2 (by rfl) ⟨576441, by rfl⟩ : syracuseStep 1537177 = 1152883) B1152883
theorem B11662541 : Blo 908576 11662541 := bstep (se 3 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 11662541 = 4373453) B4373453
theorem B3077783 : Blo 908576 3077783 := bstep (se 1 (by rfl) ⟨2308337, by rfl⟩ : syracuseStep 3077783 = 4616675) B4616675
theorem B2913995 : Blo 908576 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B1537751 : Blo 908576 1537751 := bstep (se 1 (by rfl) ⟨1153313, by rfl⟩ : syracuseStep 1537751 = 2306627) B2306627
theorem B1537879 : Blo 908576 1537879 := bstep (se 1 (by rfl) ⟨1153409, by rfl⟩ : syracuseStep 1537879 = 2306819) B2306819
theorem B3274627 : Blo 908576 3274627 := bstep (se 1 (by rfl) ⟨2455970, by rfl⟩ : syracuseStep 3274627 = 4911941) B4911941
theorem B22181957 : Blo 908576 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B8321125 : Blo 908576 8321125 := bstep (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) B1560211
theorem B3078323 : Blo 908576 3078323 := bstep (se 1 (by rfl) ⟨2308742, by rfl⟩ : syracuseStep 3078323 = 4617485) B4617485
theorem B4618457 : Blo 908576 4618457 := bstep (se 2 (by rfl) ⟨1731921, by rfl⟩ : syracuseStep 4618457 = 3463843) B3463843
theorem B5830987 : Blo 908576 5830987 := bstep (se 1 (by rfl) ⟨4373240, by rfl⟩ : syracuseStep 5830987 = 8746481) B8746481
theorem B2914649 : Blo 908576 2914649 := bstep (se 2 (by rfl) ⟨1092993, by rfl⟩ : syracuseStep 2914649 = 2185987) B2185987
theorem B3111347 : Blo 908576 3111347 := bstep (se 1 (by rfl) ⟨2333510, by rfl⟩ : syracuseStep 3111347 = 4667021) B4667021
theorem B3078593 : Blo 908576 3078593 := bstep (se 2 (by rfl) ⟨1154472, by rfl⟩ : syracuseStep 3078593 = 2308945) B2308945
theorem B1538507 : Blo 908576 1538507 := bstep (se 1 (by rfl) ⟨1153880, by rfl⟩ : syracuseStep 1538507 = 2307761) B2307761
theorem B1538635 : Blo 908576 1538635 := bstep (se 1 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 1538635 = 2307953) B2307953
theorem B8321741 : Blo 908576 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B1538777 : Blo 908576 1538777 := bstep (se 2 (by rfl) ⟨577041, by rfl⟩ : syracuseStep 1538777 = 1154083) B1154083
theorem B3373841 : Blo 908576 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B1538905 : Blo 908576 1538905 := bstep (se 2 (by rfl) ⟨577089, by rfl⟩ : syracuseStep 1538905 = 1154179) B1154179
theorem B3079133 : Blo 908576 3079133 := bstep (se 3 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 3079133 = 1154675) B1154675
theorem B4488409 : Blo 908576 4488409 := bstep (se 2 (by rfl) ⟨1683153, by rfl⟩ : syracuseStep 4488409 = 3366307) B3366307
theorem B1539479 : Blo 908576 1539479 := bstep (se 1 (by rfl) ⟨1154609, by rfl⟩ : syracuseStep 1539479 = 2309219) B2309219
theorem B2915777 : Blo 908576 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B1539607 : Blo 908576 1539607 := bstep (se 1 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 1539607 = 2309411) B2309411
theorem B4915009 : Blo 908576 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B5177267 : Blo 908576 5177267 := bstep (se 1 (by rfl) ⟨3882950, by rfl⟩ : syracuseStep 5177267 = 7765901) B7765901
theorem B2490401 : Blo 908576 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B4980973 : Blo 908576 4980973 := bstep (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) B1867865
theorem B1638841 : Blo 908576 1638841 := bstep (se 2 (by rfl) ⟨614565, by rfl⟩ : syracuseStep 1638841 = 1229131) B1229131
theorem B15958745 : Blo 908576 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B2589499 : Blo 908576 2589499 := bstep (se 1 (by rfl) ⟨1942124, by rfl⟩ : syracuseStep 2589499 = 3884249) B3884249
theorem B1967507 : Blo 908576 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B10356173 : Blo 908576 10356173 := bstep (se 3 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 10356173 = 3883565) B3883565
theorem B11077073 : Blo 908576 11077073 := bstep (se 2 (by rfl) ⟨4153902, by rfl⟩ : syracuseStep 11077073 = 8307805) B8307805
theorem B2590343 : Blo 908576 2590343 := bstep (se 1 (by rfl) ⟨1942757, by rfl⟩ : syracuseStep 2590343 = 3885515) B3885515
theorem B1640225 : Blo 908576 1640225 := bstep (se 2 (by rfl) ⟨615084, by rfl⟩ : syracuseStep 1640225 = 1230169) B1230169
theorem B2591129 : Blo 908576 2591129 := bstep (se 2 (by rfl) ⟨971673, by rfl⟩ : syracuseStep 2591129 = 1943347) B1943347
theorem B2525755 : Blo 908576 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B8293387 : Blo 908576 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B2460683 : Blo 908576 2460683 := bstep (se 1 (by rfl) ⟨1845512, by rfl⟩ : syracuseStep 2460683 = 3691025) B3691025
theorem B1149967 : Blo 908576 1149967 := bstep (se 1 (by rfl) ⟨862475, by rfl⟩ : syracuseStep 1149967 = 1724951) B1724951
theorem B2591777 : Blo 908576 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B14027863 : Blo 908576 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B1150139 : Blo 908576 1150139 := bstep (se 1 (by rfl) ⟨862604, by rfl⟩ : syracuseStep 1150139 = 1725209) B1725209
theorem B5541209 : Blo 908576 5541209 := bstep (se 2 (by rfl) ⟨2077953, by rfl⟩ : syracuseStep 5541209 = 4155907) B4155907
theorem B6655441 : Blo 908576 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B2919979 : Blo 908576 2919979 := bstep (se 1 (by rfl) ⟨2189984, by rfl⟩ : syracuseStep 2919979 = 4379969) B4379969
theorem B2920055 : Blo 908576 2920055 := bstep (se 1 (by rfl) ⟨2190041, by rfl⟩ : syracuseStep 2920055 = 4380083) B4380083
theorem B5181185 : Blo 908576 5181185 := bstep (se 2 (by rfl) ⟨1942944, by rfl⟩ : syracuseStep 5181185 = 3885889) B3885889
theorem B5541841 : Blo 908576 5541841 := bstep (se 2 (by rfl) ⟨2078190, by rfl⟩ : syracuseStep 5541841 = 4156381) B4156381
theorem B2592769 : Blo 908576 2592769 := bstep (se 2 (by rfl) ⟨972288, by rfl⟩ : syracuseStep 2592769 = 1944577) B1944577
theorem B3379229 : Blo 908576 3379229 := bstep (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) B1267211
theorem B1347643 : Blo 908576 1347643 := bstep (se 1 (by rfl) ⟨1010732, by rfl⟩ : syracuseStep 1347643 = 2021465) B2021465
theorem B1151111 : Blo 908576 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B5181641 : Blo 908576 5181641 := bstep (se 2 (by rfl) ⟨1943115, by rfl⟩ : syracuseStep 5181641 = 3886231) B3886231
theorem B7770653 : Blo 908576 7770653 := bstep (se 3 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 7770653 = 2913995) B2913995
theorem B1643051 : Blo 908576 1643051 := bstep (se 1 (by rfl) ⟨1232288, by rfl⟩ : syracuseStep 1643051 = 2464577) B2464577
theorem B6558479 : Blo 908576 6558479 := bstep (se 1 (by rfl) ⟨4918859, by rfl⟩ : syracuseStep 6558479 = 9837719) B9837719
theorem B1151759 : Blo 908576 1151759 := bstep (se 1 (by rfl) ⟨863819, by rfl⟩ : syracuseStep 1151759 = 1727639) B1727639
theorem B1971319 : Blo 908576 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B3282209 : Blo 908576 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B19699301 : Blo 908576 19699301 := bstep (se 4 (by rfl) ⟨1846809, by rfl⟩ : syracuseStep 19699301 = 3693619) B3693619
theorem B1382287 : Blo 908576 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B19666961 : Blo 908576 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B6559805 : Blo 908576 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B4987109 : Blo 908576 4987109 := bstep (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) B935083
theorem B1022215 : Blo 908576 1022215 := bstep (se 1 (by rfl) ⟨766661, by rfl⟩ : syracuseStep 1022215 = 1533323) B1533323
theorem B2464015 : Blo 908576 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B10492295 : Blo 908576 10492295 := bstep (se 1 (by rfl) ⟨7869221, by rfl⟩ : syracuseStep 10492295 = 15738443) B15738443
theorem B1022395 : Blo 908576 1022395 := bstep (se 1 (by rfl) ⟨766796, by rfl⟩ : syracuseStep 1022395 = 1533593) B1533593
theorem B2300683 : Blo 908576 2300683 := bstep (se 1 (by rfl) ⟨1725512, by rfl⟩ : syracuseStep 2300683 = 3451025) B3451025
theorem B2595719 : Blo 908576 2595719 := bstep (se 1 (by rfl) ⟨1946789, by rfl⟩ : syracuseStep 2595719 = 3893579) B3893579
theorem B1022863 : Blo 908576 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B2300825 : Blo 908576 2300825 := bstep (se 2 (by rfl) ⟨862809, by rfl⟩ : syracuseStep 2300825 = 1725619) B1725619
theorem B5839883 : Blo 908576 5839883 := bstep (se 1 (by rfl) ⟨4379912, by rfl⟩ : syracuseStep 5839883 = 8759825) B8759825
theorem B2300987 : Blo 908576 2300987 := bstep (se 1 (by rfl) ⟨1725740, by rfl⟩ : syracuseStep 2300987 = 3451481) B3451481
theorem B2595901 : Blo 908576 2595901 := bstep (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) B973463
theorem B2595959 : Blo 908576 2595959 := bstep (se 1 (by rfl) ⟨1946969, by rfl⟩ : syracuseStep 2595959 = 3893939) B3893939
theorem B1023367 : Blo 908576 1023367 := bstep (se 1 (by rfl) ⟨767525, by rfl⟩ : syracuseStep 1023367 = 1535051) B1535051
theorem B2301331 : Blo 908576 2301331 := bstep (se 1 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 2301331 = 3451997) B3451997
theorem B2465291 : Blo 908576 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B4922903 : Blo 908576 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B2301473 : Blo 908576 2301473 := bstep (se 2 (by rfl) ⟨863052, by rfl⟩ : syracuseStep 2301473 = 1726105) B1726105
theorem B2334251 : Blo 908576 2334251 := bstep (se 1 (by rfl) ⟨1750688, by rfl⟩ : syracuseStep 2334251 = 3501377) B3501377
theorem B1023547 : Blo 908576 1023547 := bstep (se 1 (by rfl) ⟨767660, by rfl⟩ : syracuseStep 1023547 = 1535321) B1535321
theorem B2465399 : Blo 908576 2465399 := bstep (se 1 (by rfl) ⟨1849049, by rfl⟩ : syracuseStep 2465399 = 3698099) B3698099
theorem B1154731 : Blo 908576 1154731 := bstep (se 1 (by rfl) ⟨866048, by rfl⟩ : syracuseStep 1154731 = 1732097) B1732097
theorem B4366169 : Blo 908576 4366169 := bstep (se 2 (by rfl) ⟨1637313, by rfl⟩ : syracuseStep 4366169 = 3274627) B3274627
theorem B2629633 : Blo 908576 2629633 := bstep (se 2 (by rfl) ⟨986112, by rfl⟩ : syracuseStep 2629633 = 1972225) B1972225
theorem B1024015 : Blo 908576 1024015 := bstep (se 1 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 1024015 = 1536023) B1536023
theorem B5185559 : Blo 908576 5185559 := bstep (se 1 (by rfl) ⟨3889169, by rfl⟩ : syracuseStep 5185559 = 7778339) B7778339
theorem B2597017 : Blo 908576 2597017 := bstep (se 2 (by rfl) ⟨973881, by rfl⟩ : syracuseStep 2597017 = 1947763) B1947763
theorem B2335063 : Blo 908576 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B7774649 : Blo 908576 7774649 := bstep (se 2 (by rfl) ⟨2915493, by rfl⟩ : syracuseStep 7774649 = 5830987) B5830987
theorem B2302465 : Blo 908576 2302465 := bstep (se 2 (by rfl) ⟨863424, by rfl⟩ : syracuseStep 2302465 = 1726849) B1726849
theorem B1024519 : Blo 908576 1024519 := bstep (se 1 (by rfl) ⟨768389, by rfl⟩ : syracuseStep 1024519 = 1536779) B1536779
theorem B1942049 : Blo 908576 1942049 := bstep (se 2 (by rfl) ⟨728268, by rfl⟩ : syracuseStep 1942049 = 1456537) B1456537
theorem B1024699 : Blo 908576 1024699 := bstep (se 1 (by rfl) ⟨768524, by rfl⟩ : syracuseStep 1024699 = 1537049) B1537049
theorem B2597633 : Blo 908576 2597633 := bstep (se 2 (by rfl) ⟨974112, by rfl⟩ : syracuseStep 2597633 = 1948225) B1948225
theorem B7775027 : Blo 908576 7775027 := bstep (se 1 (by rfl) ⟨5831270, by rfl⟩ : syracuseStep 7775027 = 11662541) B11662541
theorem B3941405 : Blo 908576 3941405 := bstep (se 3 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 3941405 = 1478027) B1478027
theorem B2303063 : Blo 908576 2303063 := bstep (se 1 (by rfl) ⟨1727297, by rfl⟩ : syracuseStep 2303063 = 3454595) B3454595
theorem B1025167 : Blo 908576 1025167 := bstep (se 1 (by rfl) ⟨768875, by rfl⟩ : syracuseStep 1025167 = 1537751) B1537751
theorem B2303275 : Blo 908576 2303275 := bstep (se 1 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 2303275 = 3454913) B3454913
theorem B14787971 : Blo 908576 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B2303417 : Blo 908576 2303417 := bstep (se 2 (by rfl) ⟨863781, by rfl⟩ : syracuseStep 2303417 = 1727563) B1727563
theorem B2631113 : Blo 908576 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B2106895 : Blo 908576 2106895 := bstep (se 1 (by rfl) ⟨1580171, by rfl⟩ : syracuseStep 2106895 = 3160343) B3160343
theorem B1943099 : Blo 908576 1943099 := bstep (se 1 (by rfl) ⟨1457324, by rfl⟩ : syracuseStep 1943099 = 2914649) B2914649
theorem B2074231 : Blo 908576 2074231 := bstep (se 1 (by rfl) ⟨1555673, by rfl⟩ : syracuseStep 2074231 = 3111347) B3111347
theorem B1025671 : Blo 908576 1025671 := bstep (se 1 (by rfl) ⟨769253, by rfl⟩ : syracuseStep 1025671 = 1538507) B1538507
theorem B2598601 : Blo 908576 2598601 := bstep (se 2 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 2598601 = 1948951) B1948951
theorem B5547827 : Blo 908576 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B1025851 : Blo 908576 1025851 := bstep (se 1 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 1025851 = 1538777) B1538777
theorem B5187473 : Blo 908576 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B1026319 : Blo 908576 1026319 := bstep (se 1 (by rfl) ⟨769739, by rfl⟩ : syracuseStep 1026319 = 1539479) B1539479
theorem B1943851 : Blo 908576 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B2304409 : Blo 908576 2304409 := bstep (se 2 (by rfl) ⟨864153, by rfl⟩ : syracuseStep 2304409 = 1728307) B1728307
theorem B2337281 : Blo 908576 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B2304571 : Blo 908576 2304571 := bstep (se 1 (by rfl) ⟨1728428, by rfl⟩ : syracuseStep 2304571 = 3456857) B3456857
theorem B5188157 : Blo 908576 5188157 := bstep (se 3 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 5188157 = 1945559) B1945559
theorem B3451511 : Blo 908576 3451511 := bstep (se 1 (by rfl) ⟨2588633, by rfl⟩ : syracuseStep 3451511 = 5177267) B5177267
theorem B2304713 : Blo 908576 2304713 := bstep (se 2 (by rfl) ⟨864267, by rfl⟩ : syracuseStep 2304713 = 1728535) B1728535
theorem B10529585 : Blo 908576 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B170797889 : Blo 908576 170797889 := bstep (se 2 (by rfl) ⟨64049208, by rfl⟩ : syracuseStep 170797889 = 128098417) B128098417
theorem B5843801 : Blo 908576 5843801 := bstep (se 2 (by rfl) ⟨2191425, by rfl⟩ : syracuseStep 5843801 = 4382851) B4382851
theorem B2305057 : Blo 908576 2305057 := bstep (se 2 (by rfl) ⟨864396, by rfl⟩ : syracuseStep 2305057 = 1728793) B1728793
theorem B8989741 : Blo 908576 8989741 := bstep (se 3 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 8989741 = 3371153) B3371153
theorem B2632961 : Blo 908576 2632961 := bstep (se 2 (by rfl) ⟨987360, by rfl⟩ : syracuseStep 2632961 = 1974721) B1974721
theorem B3452483 : Blo 908576 3452483 := bstep (se 1 (by rfl) ⟨2589362, by rfl⟩ : syracuseStep 3452483 = 5178725) B5178725
theorem B2305655 : Blo 908576 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B1945235 : Blo 908576 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B3452939 : Blo 908576 3452939 := bstep (se 1 (by rfl) ⟨2589704, by rfl⟩ : syracuseStep 3452939 = 5179409) B5179409
theorem B9843079 : Blo 908576 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B2044475 : Blo 908576 2044475 := bstep (se 1 (by rfl) ⟨1533356, by rfl⟩ : syracuseStep 2044475 = 3066713) B3066713
theorem B2044601 : Blo 908576 2044601 := bstep (se 2 (by rfl) ⟨766725, by rfl⟩ : syracuseStep 2044601 = 1533451) B1533451
theorem B2077369 : Blo 908576 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B2306951 : Blo 908576 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B2307001 : Blo 908576 2307001 := bstep (se 2 (by rfl) ⟨865125, by rfl⟩ : syracuseStep 2307001 = 1730251) B1730251
theorem B1094647 : Blo 908576 1094647 := bstep (se 1 (by rfl) ⟨820985, by rfl⟩ : syracuseStep 1094647 = 1641971) B1641971
theorem B2044943 : Blo 908576 2044943 := bstep (se 1 (by rfl) ⟨1533707, by rfl⟩ : syracuseStep 2044943 = 3067415) B3067415
theorem B1094671 : Blo 908576 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B2044961 : Blo 908576 2044961 := bstep (se 2 (by rfl) ⟨766860, by rfl⟩ : syracuseStep 2044961 = 1533721) B1533721
theorem B2045303 : Blo 908576 2045303 := bstep (se 1 (by rfl) ⟨1533977, by rfl⟩ : syracuseStep 2045303 = 3067955) B3067955
theorem B21018041 : Blo 908576 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B2307599 : Blo 908576 2307599 := bstep (se 1 (by rfl) ⟨1730699, by rfl⟩ : syracuseStep 2307599 = 3461399) B3461399
theorem B2045483 : Blo 908576 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B2045843 : Blo 908576 2045843 := bstep (se 1 (by rfl) ⟨1534382, by rfl⟩ : syracuseStep 2045843 = 3068765) B3068765
theorem B2045897 : Blo 908576 2045897 := bstep (se 2 (by rfl) ⟨767211, by rfl⟩ : syracuseStep 2045897 = 1534423) B1534423
theorem B3455095 : Blo 908576 3455095 := bstep (se 1 (by rfl) ⟨2591321, by rfl⟩ : syracuseStep 3455095 = 5182643) B5182643
theorem B2308297 : Blo 908576 2308297 := bstep (se 2 (by rfl) ⟨865611, by rfl⟩ : syracuseStep 2308297 = 1731223) B1731223
theorem B26589505 : Blo 908576 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B2308439 : Blo 908576 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B4602257 : Blo 908576 4602257 := bstep (se 2 (by rfl) ⟨1725846, by rfl⟩ : syracuseStep 4602257 = 3451693) B3451693
theorem B3881515 : Blo 908576 3881515 := bstep (se 1 (by rfl) ⟨2911136, by rfl⟩ : syracuseStep 3881515 = 5822273) B5822273
theorem B2046599 : Blo 908576 2046599 := bstep (se 1 (by rfl) ⟨1534949, by rfl⟩ : syracuseStep 2046599 = 3069899) B3069899
theorem B2046779 : Blo 908576 2046779 := bstep (se 1 (by rfl) ⟨1535084, by rfl⟩ : syracuseStep 2046779 = 3070169) B3070169
theorem B3947399 : Blo 908576 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B2046905 : Blo 908576 2046905 := bstep (se 2 (by rfl) ⟨767589, by rfl⟩ : syracuseStep 2046905 = 1535179) B1535179
theorem B4996099 : Blo 908576 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B3456067 : Blo 908576 3456067 := bstep (se 1 (by rfl) ⟨2592050, by rfl⟩ : syracuseStep 3456067 = 5184101) B5184101
theorem B2047247 : Blo 908576 2047247 := bstep (se 1 (by rfl) ⟨1535435, by rfl⟩ : syracuseStep 2047247 = 3070871) B3070871
theorem B2047265 : Blo 908576 2047265 := bstep (se 2 (by rfl) ⟨767724, by rfl⟩ : syracuseStep 2047265 = 1535449) B1535449
theorem B3456371 : Blo 908576 3456371 := bstep (se 1 (by rfl) ⟨2592278, by rfl⟩ : syracuseStep 3456371 = 5184557) B5184557
theorem B6929873 : Blo 908576 6929873 := bstep (se 2 (by rfl) ⟨2598702, by rfl⟩ : syracuseStep 6929873 = 5197405) B5197405
theorem B2080289 : Blo 908576 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B1228331 : Blo 908576 1228331 := bstep (se 1 (by rfl) ⟨921248, by rfl⟩ : syracuseStep 1228331 = 1842497) B1842497
theorem B2047607 : Blo 908576 2047607 := bstep (se 1 (by rfl) ⟨1535705, by rfl⟩ : syracuseStep 2047607 = 3071411) B3071411
theorem B10370753 : Blo 908576 10370753 := bstep (se 2 (by rfl) ⟨3889032, by rfl⟩ : syracuseStep 10370753 = 7778065) B7778065
theorem B2047787 : Blo 908576 2047787 := bstep (se 1 (by rfl) ⟨1535840, by rfl⟩ : syracuseStep 2047787 = 3071681) B3071681
theorem B3456827 : Blo 908576 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B4669483 : Blo 908576 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B1294471 : Blo 908576 1294471 := bstep (se 1 (by rfl) ⟨970853, by rfl⟩ : syracuseStep 1294471 = 1941707) B1941707
theorem B2048147 : Blo 908576 2048147 := bstep (se 1 (by rfl) ⟨1536110, by rfl⟩ : syracuseStep 2048147 = 3072221) B3072221
theorem B8732873 : Blo 908576 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B2048201 : Blo 908576 2048201 := bstep (se 2 (by rfl) ⟨768075, by rfl⟩ : syracuseStep 2048201 = 1536151) B1536151
theorem B3948745 : Blo 908576 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B3457313 : Blo 908576 3457313 := bstep (se 2 (by rfl) ⟨1296492, by rfl⟩ : syracuseStep 3457313 = 2592985) B2592985
theorem B4604363 : Blo 908576 4604363 := bstep (se 1 (by rfl) ⟨3453272, by rfl⟩ : syracuseStep 4604363 = 6906545) B6906545
theorem B2769437 : Blo 908576 2769437 := bstep (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) B1038539
theorem B5194307 : Blo 908576 5194307 := bstep (se 1 (by rfl) ⟨3895730, by rfl⟩ : syracuseStep 5194307 = 7791461) B7791461
theorem B4932353 : Blo 908576 4932353 := bstep (se 2 (by rfl) ⟨1849632, by rfl⟩ : syracuseStep 4932353 = 3699265) B3699265
theorem B4604687 : Blo 908576 4604687 := bstep (se 1 (by rfl) ⟨3453515, by rfl⟩ : syracuseStep 4604687 = 6907031) B6907031
theorem B2048903 : Blo 908576 2048903 := bstep (se 1 (by rfl) ⟨1536677, by rfl⟩ : syracuseStep 2048903 = 3073355) B3073355
theorem B1295291 : Blo 908576 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B5194763 : Blo 908576 5194763 := bstep (se 1 (by rfl) ⟨3896072, by rfl⟩ : syracuseStep 5194763 = 7792145) B7792145
theorem B2049083 : Blo 908576 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B9847925 : Blo 908576 9847925 := bstep (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) B923243
theorem B2049209 : Blo 908576 2049209 := bstep (se 2 (by rfl) ⟨768453, by rfl⟩ : syracuseStep 2049209 = 1536907) B1536907
theorem B3884233 : Blo 908576 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B3458285 : Blo 908576 3458285 := bstep (se 3 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 3458285 = 1296857) B1296857
theorem B2049551 : Blo 908576 2049551 := bstep (se 1 (by rfl) ⟨1537163, by rfl⟩ : syracuseStep 2049551 = 3074327) B3074327
theorem B2049569 : Blo 908576 2049569 := bstep (se 2 (by rfl) ⟨768588, by rfl⟩ : syracuseStep 2049569 = 1537177) B1537177
theorem B1295929 : Blo 908576 1295929 := bstep (se 2 (by rfl) ⟨485973, by rfl⟩ : syracuseStep 1295929 = 971947) B971947
theorem B10798771 : Blo 908576 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B4933349 : Blo 908576 4933349 := bstep (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) B925003
theorem B39405365 : Blo 908576 39405365 := bstep (se 5 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 39405365 = 3694253) B3694253
theorem B2049911 : Blo 908576 2049911 := bstep (se 1 (by rfl) ⟨1537433, by rfl⟩ : syracuseStep 2049911 = 3074867) B3074867
theorem B3458969 : Blo 908576 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B2050091 : Blo 908576 2050091 := bstep (se 1 (by rfl) ⟨1537568, by rfl⟩ : syracuseStep 2050091 = 3075137) B3075137
theorem B4606145 : Blo 908576 4606145 := bstep (se 2 (by rfl) ⟨1727304, by rfl⟩ : syracuseStep 4606145 = 3454609) B3454609
theorem B15747317 : Blo 908576 15747317 := bstep (se 5 (by rfl) ⟨738155, by rfl⟩ : syracuseStep 15747317 = 1476311) B1476311
theorem B2803997 : Blo 908576 2803997 := bstep (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) B1051499
theorem B3950963 : Blo 908576 3950963 := bstep (se 1 (by rfl) ⟨2963222, by rfl⟩ : syracuseStep 3950963 = 5926445) B5926445
theorem B2050451 : Blo 908576 2050451 := bstep (se 1 (by rfl) ⟨1537838, by rfl⟩ : syracuseStep 2050451 = 3075677) B3075677
theorem B2050505 : Blo 908576 2050505 := bstep (se 2 (by rfl) ⟨768939, by rfl⟩ : syracuseStep 2050505 = 1537879) B1537879
theorem B6900227 : Blo 908576 6900227 := bstep (se 1 (by rfl) ⟨5175170, by rfl⟩ : syracuseStep 6900227 = 10350341) B10350341
theorem B1755937 : Blo 908576 1755937 := bstep (se 2 (by rfl) ⟨658476, by rfl⟩ : syracuseStep 1755937 = 1316953) B1316953
theorem B11094833 : Blo 908576 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B3459955 : Blo 908576 3459955 := bstep (se 1 (by rfl) ⟨2594966, by rfl⟩ : syracuseStep 3459955 = 5189933) B5189933
theorem B1362875 : Blo 908576 1362875 := bstep (se 1 (by rfl) ⟨1022156, by rfl⟩ : syracuseStep 1362875 = 2044313) B2044313
theorem B1362935 : Blo 908576 1362935 := bstep (se 1 (by rfl) ⟨1022201, by rfl⟩ : syracuseStep 1362935 = 2044403) B2044403
theorem B1297415 : Blo 908576 1297415 := bstep (se 1 (by rfl) ⟨973061, by rfl⟩ : syracuseStep 1297415 = 1946123) B1946123
theorem B14797835 : Blo 908576 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B1362959 : Blo 908576 1362959 := bstep (se 1 (by rfl) ⟨1022219, by rfl⟩ : syracuseStep 1362959 = 2044439) B2044439
theorem B1363001 : Blo 908576 1363001 := bstep (se 2 (by rfl) ⟨511125, by rfl⟩ : syracuseStep 1363001 = 1022251) B1022251
theorem B1363079 : Blo 908576 1363079 := bstep (se 1 (by rfl) ⟨1022309, by rfl⟩ : syracuseStep 1363079 = 2044619) B2044619
theorem B2051207 : Blo 908576 2051207 := bstep (se 1 (by rfl) ⟨1538405, by rfl⟩ : syracuseStep 2051207 = 3076811) B3076811
theorem B1363115 : Blo 908576 1363115 := bstep (se 1 (by rfl) ⟨1022336, by rfl⟩ : syracuseStep 1363115 = 2044673) B2044673
theorem B4672685 : Blo 908576 4672685 := bstep (se 3 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 4672685 = 1752257) B1752257
theorem B1363145 : Blo 908576 1363145 := bstep (se 2 (by rfl) ⟨511179, by rfl⟩ : syracuseStep 1363145 = 1022359) B1022359
theorem B1559753 : Blo 908576 1559753 := bstep (se 2 (by rfl) ⟨584907, by rfl⟩ : syracuseStep 1559753 = 1169815) B1169815
theorem B1363259 : Blo 908576 1363259 := bstep (se 1 (by rfl) ⟨1022444, by rfl⟩ : syracuseStep 1363259 = 2044889) B2044889
theorem B1297723 : Blo 908576 1297723 := bstep (se 1 (by rfl) ⟨973292, by rfl⟩ : syracuseStep 1297723 = 1946585) B1946585
theorem B2051387 : Blo 908576 2051387 := bstep (se 1 (by rfl) ⟨1538540, by rfl⟩ : syracuseStep 2051387 = 3077081) B3077081
theorem B1363319 : Blo 908576 1363319 := bstep (se 1 (by rfl) ⟨1022489, by rfl⟩ : syracuseStep 1363319 = 2044979) B2044979
theorem B1363343 : Blo 908576 1363343 := bstep (se 1 (by rfl) ⟨1022507, by rfl⟩ : syracuseStep 1363343 = 2045015) B2045015
theorem B4378009 : Blo 908576 4378009 := bstep (se 2 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 4378009 = 3283507) B3283507
theorem B1363385 : Blo 908576 1363385 := bstep (se 2 (by rfl) ⟨511269, by rfl⟩ : syracuseStep 1363385 = 1022539) B1022539
theorem B2051513 : Blo 908576 2051513 := bstep (se 2 (by rfl) ⟨769317, by rfl⟩ : syracuseStep 2051513 = 1538635) B1538635
theorem B4607441 : Blo 908576 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B1363463 : Blo 908576 1363463 := bstep (se 1 (by rfl) ⟨1022597, by rfl⟩ : syracuseStep 1363463 = 2045195) B2045195
theorem B1363499 : Blo 908576 1363499 := bstep (se 1 (by rfl) ⟨1022624, by rfl⟩ : syracuseStep 1363499 = 2045249) B2045249
theorem B1363529 : Blo 908576 1363529 := bstep (se 2 (by rfl) ⟨511323, by rfl⟩ : syracuseStep 1363529 = 1022647) B1022647
theorem B970375 : Blo 908576 970375 := bstep (se 1 (by rfl) ⟨727781, by rfl⟩ : syracuseStep 970375 = 1455563) B1455563
theorem B1363643 : Blo 908576 1363643 := bstep (se 1 (by rfl) ⟨1022732, by rfl⟩ : syracuseStep 1363643 = 2045465) B2045465
theorem B1560265 : Blo 908576 1560265 := bstep (se 2 (by rfl) ⟨585099, by rfl⟩ : syracuseStep 1560265 = 1170199) B1170199
theorem B1363703 : Blo 908576 1363703 := bstep (se 1 (by rfl) ⟨1022777, by rfl⟩ : syracuseStep 1363703 = 2045555) B2045555
theorem B1363727 : Blo 908576 1363727 := bstep (se 1 (by rfl) ⟨1022795, by rfl⟩ : syracuseStep 1363727 = 2045591) B2045591
theorem B2051855 : Blo 908576 2051855 := bstep (se 1 (by rfl) ⟨1538891, by rfl⟩ : syracuseStep 2051855 = 3077783) B3077783
theorem B2051873 : Blo 908576 2051873 := bstep (se 2 (by rfl) ⟨769452, by rfl⟩ : syracuseStep 2051873 = 1538905) B1538905
theorem B1363769 : Blo 908576 1363769 := bstep (se 2 (by rfl) ⟨511413, by rfl⟩ : syracuseStep 1363769 = 1022827) B1022827
theorem B1363847 : Blo 908576 1363847 := bstep (se 1 (by rfl) ⟨1022885, by rfl⟩ : syracuseStep 1363847 = 2045771) B2045771
theorem B1363883 : Blo 908576 1363883 := bstep (se 1 (by rfl) ⟨1022912, by rfl⟩ : syracuseStep 1363883 = 2045825) B2045825
theorem B1363913 : Blo 908576 1363913 := bstep (se 2 (by rfl) ⟨511467, by rfl⟩ : syracuseStep 1363913 = 1022935) B1022935
theorem B1364027 : Blo 908576 1364027 := bstep (se 1 (by rfl) ⟨1023020, by rfl⟩ : syracuseStep 1364027 = 2046041) B2046041
theorem B1364087 : Blo 908576 1364087 := bstep (se 1 (by rfl) ⟨1023065, by rfl⟩ : syracuseStep 1364087 = 2046131) B2046131
theorem B2052215 : Blo 908576 2052215 := bstep (se 1 (by rfl) ⟨1539161, by rfl⟩ : syracuseStep 2052215 = 3078323) B3078323
theorem B1364111 : Blo 908576 1364111 := bstep (se 1 (by rfl) ⟨1023083, by rfl⟩ : syracuseStep 1364111 = 2046167) B2046167
theorem B1364153 : Blo 908576 1364153 := bstep (se 2 (by rfl) ⟨511557, by rfl⟩ : syracuseStep 1364153 = 1023115) B1023115
theorem B1364231 : Blo 908576 1364231 := bstep (se 1 (by rfl) ⟨1023173, by rfl⟩ : syracuseStep 1364231 = 2046347) B2046347
theorem B5984545 : Blo 908576 5984545 := bstep (se 2 (by rfl) ⟨2244204, by rfl⟩ : syracuseStep 5984545 = 4488409) B4488409
theorem B1364267 : Blo 908576 1364267 := bstep (se 1 (by rfl) ⟨1023200, by rfl⟩ : syracuseStep 1364267 = 2046401) B2046401
theorem B2052395 : Blo 908576 2052395 := bstep (se 1 (by rfl) ⟨1539296, by rfl⟩ : syracuseStep 2052395 = 3078593) B3078593
theorem B1364297 : Blo 908576 1364297 := bstep (se 2 (by rfl) ⟨511611, by rfl⟩ : syracuseStep 1364297 = 1023223) B1023223
theorem B1298873 : Blo 908576 1298873 := bstep (se 2 (by rfl) ⟨487077, by rfl⟩ : syracuseStep 1298873 = 974155) B974155
theorem B971195 : Blo 908576 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B1364411 : Blo 908576 1364411 := bstep (se 1 (by rfl) ⟨1023308, by rfl⟩ : syracuseStep 1364411 = 2046617) B2046617
theorem B1364471 : Blo 908576 1364471 := bstep (se 1 (by rfl) ⟨1023353, by rfl⟩ : syracuseStep 1364471 = 2046707) B2046707
theorem B2249227 : Blo 908576 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1364495 : Blo 908576 1364495 := bstep (se 1 (by rfl) ⟨1023371, by rfl⟩ : syracuseStep 1364495 = 2046743) B2046743
theorem B159896081 : Blo 908576 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B1364537 : Blo 908576 1364537 := bstep (se 2 (by rfl) ⟨511701, by rfl⟩ : syracuseStep 1364537 = 1023403) B1023403
theorem B1364615 : Blo 908576 1364615 := bstep (se 1 (by rfl) ⟨1023461, by rfl⟩ : syracuseStep 1364615 = 2046923) B2046923
theorem B2052755 : Blo 908576 2052755 := bstep (se 1 (by rfl) ⟨1539566, by rfl⟩ : syracuseStep 2052755 = 3079133) B3079133
theorem B1364651 : Blo 908576 1364651 := bstep (se 1 (by rfl) ⟨1023488, by rfl⟩ : syracuseStep 1364651 = 2046977) B2046977
theorem B1364681 : Blo 908576 1364681 := bstep (se 2 (by rfl) ⟨511755, by rfl⟩ : syracuseStep 1364681 = 1023511) B1023511
theorem B2052809 : Blo 908576 2052809 := bstep (se 2 (by rfl) ⟨769803, by rfl⟩ : syracuseStep 2052809 = 1539607) B1539607
theorem B1364795 : Blo 908576 1364795 := bstep (se 1 (by rfl) ⟨1023596, by rfl⟩ : syracuseStep 1364795 = 2047193) B2047193
theorem B1364855 : Blo 908576 1364855 := bstep (se 1 (by rfl) ⟨1023641, by rfl⟩ : syracuseStep 1364855 = 2047283) B2047283
theorem B1364879 : Blo 908576 1364879 := bstep (se 1 (by rfl) ⟨1023659, by rfl⟩ : syracuseStep 1364879 = 2047319) B2047319
theorem B3068819 : Blo 908576 3068819 := bstep (se 1 (by rfl) ⟨2301614, by rfl⟩ : syracuseStep 3068819 = 4603229) B4603229
theorem B1364921 : Blo 908576 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B1364999 : Blo 908576 1364999 := bstep (se 1 (by rfl) ⟨1023749, by rfl⟩ : syracuseStep 1364999 = 2047499) B2047499
theorem B3462173 : Blo 908576 3462173 := bstep (se 3 (by rfl) ⟨649157, by rfl⟩ : syracuseStep 3462173 = 1298315) B1298315
theorem B1365035 : Blo 908576 1365035 := bstep (se 1 (by rfl) ⟨1023776, by rfl⟩ : syracuseStep 1365035 = 2047553) B2047553
theorem B1365065 : Blo 908576 1365065 := bstep (se 2 (by rfl) ⟨511899, by rfl⟩ : syracuseStep 1365065 = 1023799) B1023799
theorem B1365179 : Blo 908576 1365179 := bstep (se 1 (by rfl) ⟨1023884, by rfl⟩ : syracuseStep 1365179 = 2047769) B2047769
theorem B1365239 : Blo 908576 1365239 := bstep (se 1 (by rfl) ⟨1023929, by rfl⟩ : syracuseStep 1365239 = 2047859) B2047859
theorem B1365263 : Blo 908576 1365263 := bstep (se 1 (by rfl) ⟨1023947, by rfl⟩ : syracuseStep 1365263 = 2047895) B2047895
theorem B1365305 : Blo 908576 1365305 := bstep (se 2 (by rfl) ⟨511989, by rfl⟩ : syracuseStep 1365305 = 1023979) B1023979
theorem B2184583 : Blo 908576 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B1365383 : Blo 908576 1365383 := bstep (se 1 (by rfl) ⟨1024037, by rfl⟩ : syracuseStep 1365383 = 2048075) B2048075
theorem B1365419 : Blo 908576 1365419 := bstep (se 1 (by rfl) ⟨1024064, by rfl⟩ : syracuseStep 1365419 = 2048129) B2048129
theorem B1365449 : Blo 908576 1365449 := bstep (se 2 (by rfl) ⟨512043, by rfl⟩ : syracuseStep 1365449 = 1024087) B1024087
theorem B4609547 : Blo 908576 4609547 := bstep (se 1 (by rfl) ⟨3457160, by rfl⟩ : syracuseStep 4609547 = 6914321) B6914321
theorem B1365563 : Blo 908576 1365563 := bstep (se 1 (by rfl) ⟨1024172, by rfl⟩ : syracuseStep 1365563 = 2048345) B2048345
theorem B1365623 : Blo 908576 1365623 := bstep (se 1 (by rfl) ⟨1024217, by rfl⟩ : syracuseStep 1365623 = 2048435) B2048435
theorem B1365647 : Blo 908576 1365647 := bstep (se 1 (by rfl) ⟨1024235, by rfl⟩ : syracuseStep 1365647 = 2048471) B2048471
theorem B4609709 : Blo 908576 4609709 := bstep (se 3 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 4609709 = 1728641) B1728641
theorem B23025329 : Blo 908576 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B1365689 : Blo 908576 1365689 := bstep (se 2 (by rfl) ⟨512133, by rfl⟩ : syracuseStep 1365689 = 1024267) B1024267
theorem B3462857 : Blo 908576 3462857 := bstep (se 2 (by rfl) ⟨1298571, by rfl⟩ : syracuseStep 3462857 = 2597143) B2597143
theorem B1365767 : Blo 908576 1365767 := bstep (se 1 (by rfl) ⟨1024325, by rfl⟩ : syracuseStep 1365767 = 2048651) B2048651
theorem B1365803 : Blo 908576 1365803 := bstep (se 1 (by rfl) ⟨1024352, by rfl⟩ : syracuseStep 1365803 = 2048705) B2048705
theorem B47404865 : Blo 908576 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B1365833 : Blo 908576 1365833 := bstep (se 2 (by rfl) ⟨512187, by rfl⟩ : syracuseStep 1365833 = 1024375) B1024375
theorem B1365947 : Blo 908576 1365947 := bstep (se 1 (by rfl) ⟨1024460, by rfl⟩ : syracuseStep 1365947 = 2048921) B2048921
theorem B1726409 : Blo 908576 1726409 := bstep (se 2 (by rfl) ⟨647403, by rfl⟩ : syracuseStep 1726409 = 1294807) B1294807
theorem B1366007 : Blo 908576 1366007 := bstep (se 1 (by rfl) ⟨1024505, by rfl⟩ : syracuseStep 1366007 = 2049011) B2049011
theorem B1366031 : Blo 908576 1366031 := bstep (se 1 (by rfl) ⟨1024523, by rfl⟩ : syracuseStep 1366031 = 2049047) B2049047
theorem B1366073 : Blo 908576 1366073 := bstep (se 2 (by rfl) ⟨512277, by rfl⟩ : syracuseStep 1366073 = 1024555) B1024555
theorem B1366151 : Blo 908576 1366151 := bstep (se 1 (by rfl) ⟨1024613, by rfl⟩ : syracuseStep 1366151 = 2049227) B2049227
theorem B1366187 : Blo 908576 1366187 := bstep (se 1 (by rfl) ⟨1024640, by rfl⟩ : syracuseStep 1366187 = 2049281) B2049281
theorem B1366217 : Blo 908576 1366217 := bstep (se 2 (by rfl) ⟨512331, by rfl⟩ : syracuseStep 1366217 = 1024663) B1024663
theorem B11655413 : Blo 908576 11655413 := bstep (se 5 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 11655413 = 1092695) B1092695
theorem B3070223 : Blo 908576 3070223 := bstep (se 1 (by rfl) ⟨2302667, by rfl⟩ : syracuseStep 3070223 = 4605335) B4605335
theorem B1366331 : Blo 908576 1366331 := bstep (se 1 (by rfl) ⟨1024748, by rfl⟩ : syracuseStep 1366331 = 2049497) B2049497
theorem B1366391 : Blo 908576 1366391 := bstep (se 1 (by rfl) ⟨1024793, by rfl⟩ : syracuseStep 1366391 = 2049587) B2049587
theorem B1366415 : Blo 908576 1366415 := bstep (se 1 (by rfl) ⟨1024811, by rfl⟩ : syracuseStep 1366415 = 2049623) B2049623
theorem B1366457 : Blo 908576 1366457 := bstep (se 2 (by rfl) ⟨512421, by rfl⟩ : syracuseStep 1366457 = 1024843) B1024843
theorem B17488345 : Blo 908576 17488345 := bstep (se 2 (by rfl) ⟨6558129, by rfl⟩ : syracuseStep 17488345 = 13116259) B13116259
theorem B1366535 : Blo 908576 1366535 := bstep (se 1 (by rfl) ⟨1024901, by rfl⟩ : syracuseStep 1366535 = 2049803) B2049803
theorem B3070493 : Blo 908576 3070493 := bstep (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) B1151435
theorem B1366571 : Blo 908576 1366571 := bstep (se 1 (by rfl) ⟨1024928, by rfl⟩ : syracuseStep 1366571 = 2049857) B2049857
theorem B1366601 : Blo 908576 1366601 := bstep (se 2 (by rfl) ⟨512475, by rfl⟩ : syracuseStep 1366601 = 1024951) B1024951
theorem B1366715 : Blo 908576 1366715 := bstep (se 1 (by rfl) ⟨1025036, by rfl⟩ : syracuseStep 1366715 = 2050073) B2050073
theorem B1366775 : Blo 908576 1366775 := bstep (se 1 (by rfl) ⟨1025081, by rfl⟩ : syracuseStep 1366775 = 2050163) B2050163
theorem B1366799 : Blo 908576 1366799 := bstep (se 1 (by rfl) ⟨1025099, by rfl⟩ : syracuseStep 1366799 = 2050199) B2050199
theorem B1366841 : Blo 908576 1366841 := bstep (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) B1025131
theorem B1366919 : Blo 908576 1366919 := bstep (se 1 (by rfl) ⟨1025189, by rfl⟩ : syracuseStep 1366919 = 2050379) B2050379
theorem B973711 : Blo 908576 973711 := bstep (se 1 (by rfl) ⟨730283, by rfl⟩ : syracuseStep 973711 = 1460567) B1460567
theorem B1366955 : Blo 908576 1366955 := bstep (se 1 (by rfl) ⟨1025216, by rfl⟩ : syracuseStep 1366955 = 2050433) B2050433
theorem B1366985 : Blo 908576 1366985 := bstep (se 2 (by rfl) ⟨512619, by rfl⟩ : syracuseStep 1366985 = 1025239) B1025239
theorem B1367099 : Blo 908576 1367099 := bstep (se 1 (by rfl) ⟨1025324, by rfl⟩ : syracuseStep 1367099 = 2050649) B2050649
theorem B3890263 : Blo 908576 3890263 := bstep (se 1 (by rfl) ⟨2917697, by rfl⟩ : syracuseStep 3890263 = 5835395) B5835395
theorem B1367159 : Blo 908576 1367159 := bstep (se 1 (by rfl) ⟨1025369, by rfl⟩ : syracuseStep 1367159 = 2050739) B2050739
theorem B1367183 : Blo 908576 1367183 := bstep (se 1 (by rfl) ⟨1025387, by rfl⟩ : syracuseStep 1367183 = 2050775) B2050775
theorem B1367225 : Blo 908576 1367225 := bstep (se 2 (by rfl) ⟨512709, by rfl⟩ : syracuseStep 1367225 = 1025419) B1025419
theorem B4611329 : Blo 908576 4611329 := bstep (se 2 (by rfl) ⟨1729248, by rfl⟩ : syracuseStep 4611329 = 3458497) B3458497
theorem B1367303 : Blo 908576 1367303 := bstep (se 1 (by rfl) ⟨1025477, by rfl⟩ : syracuseStep 1367303 = 2050955) B2050955
theorem B1367339 : Blo 908576 1367339 := bstep (se 1 (by rfl) ⟨1025504, by rfl⟩ : syracuseStep 1367339 = 2051009) B2051009
theorem B908603 : Blo 908576 908603 := bstep (se 1 (by rfl) ⟨681452, by rfl⟩ : syracuseStep 908603 = 1362905) B1362905
theorem B1367369 : Blo 908576 1367369 := bstep (se 2 (by rfl) ⟨512763, by rfl⟩ : syracuseStep 1367369 = 1025527) B1025527
theorem B908679 : Blo 908576 908679 := bstep (se 1 (by rfl) ⟨681509, by rfl⟩ : syracuseStep 908679 = 1363019) B1363019
theorem B974215 : Blo 908576 974215 := bstep (se 1 (by rfl) ⟨730661, by rfl⟩ : syracuseStep 974215 = 1461323) B1461323
theorem B908687 : Blo 908576 908687 := bstep (se 1 (by rfl) ⟨681515, by rfl⟩ : syracuseStep 908687 = 1363031) B1363031
theorem B3464633 : Blo 908576 3464633 := bstep (se 2 (by rfl) ⟨1299237, by rfl⟩ : syracuseStep 3464633 = 2598475) B2598475
theorem B908731 : Blo 908576 908731 := bstep (se 1 (by rfl) ⟨681548, by rfl⟩ : syracuseStep 908731 = 1363097) B1363097
theorem B1367483 : Blo 908576 1367483 := bstep (se 1 (by rfl) ⟨1025612, by rfl⟩ : syracuseStep 1367483 = 2051225) B2051225
theorem B1367543 : Blo 908576 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B908807 : Blo 908576 908807 := bstep (se 1 (by rfl) ⟨681605, by rfl⟩ : syracuseStep 908807 = 1363211) B1363211
theorem B908815 : Blo 908576 908815 := bstep (se 1 (by rfl) ⟨681611, by rfl⟩ : syracuseStep 908815 = 1363223) B1363223
theorem B1367567 : Blo 908576 1367567 := bstep (se 1 (by rfl) ⟨1025675, by rfl⟩ : syracuseStep 1367567 = 2051351) B2051351
theorem B1367609 : Blo 908576 1367609 := bstep (se 2 (by rfl) ⟨512853, by rfl⟩ : syracuseStep 1367609 = 1025707) B1025707
theorem B908859 : Blo 908576 908859 := bstep (se 1 (by rfl) ⟨681644, by rfl⟩ : syracuseStep 908859 = 1363289) B1363289
theorem B908935 : Blo 908576 908935 := bstep (se 1 (by rfl) ⟨681701, by rfl⟩ : syracuseStep 908935 = 1363403) B1363403
theorem B1367687 : Blo 908576 1367687 := bstep (se 1 (by rfl) ⟨1025765, by rfl⟩ : syracuseStep 1367687 = 2051531) B2051531
theorem B908943 : Blo 908576 908943 := bstep (se 1 (by rfl) ⟨681707, by rfl⟩ : syracuseStep 908943 = 1363415) B1363415
theorem B1367723 : Blo 908576 1367723 := bstep (se 1 (by rfl) ⟨1025792, by rfl⟩ : syracuseStep 1367723 = 2051585) B2051585
theorem B908987 : Blo 908576 908987 := bstep (se 1 (by rfl) ⟨681740, by rfl⟩ : syracuseStep 908987 = 1363481) B1363481
theorem B1367753 : Blo 908576 1367753 := bstep (se 2 (by rfl) ⟨512907, by rfl⟩ : syracuseStep 1367753 = 1025815) B1025815
theorem B6905573 : Blo 908576 6905573 := bstep (se 4 (by rfl) ⟨647397, by rfl⟩ : syracuseStep 6905573 = 1294795) B1294795
theorem B909063 : Blo 908576 909063 := bstep (se 1 (by rfl) ⟨681797, by rfl⟩ : syracuseStep 909063 = 1363595) B1363595
theorem B909071 : Blo 908576 909071 := bstep (se 1 (by rfl) ⟨681803, by rfl⟩ : syracuseStep 909071 = 1363607) B1363607
theorem B909115 : Blo 908576 909115 := bstep (se 1 (by rfl) ⟨681836, by rfl⟩ : syracuseStep 909115 = 1363673) B1363673
theorem B1367867 : Blo 908576 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B9363275 : Blo 908576 9363275 := bstep (se 1 (by rfl) ⟨7022456, by rfl⟩ : syracuseStep 9363275 = 14044913) B14044913
theorem B1367927 : Blo 908576 1367927 := bstep (se 1 (by rfl) ⟨1025945, by rfl⟩ : syracuseStep 1367927 = 2051891) B2051891
theorem B909191 : Blo 908576 909191 := bstep (se 1 (by rfl) ⟨681893, by rfl⟩ : syracuseStep 909191 = 1363787) B1363787
theorem B1728391 : Blo 908576 1728391 := bstep (se 1 (by rfl) ⟨1296293, by rfl⟩ : syracuseStep 1728391 = 2592587) B2592587
theorem B909199 : Blo 908576 909199 := bstep (se 1 (by rfl) ⟨681899, by rfl⟩ : syracuseStep 909199 = 1363799) B1363799
theorem B1367951 : Blo 908576 1367951 := bstep (se 1 (by rfl) ⟨1025963, by rfl⟩ : syracuseStep 1367951 = 2051927) B2051927
theorem B3071897 : Blo 908576 3071897 := bstep (se 2 (by rfl) ⟨1151961, by rfl⟩ : syracuseStep 3071897 = 2303923) B2303923
theorem B1367993 : Blo 908576 1367993 := bstep (se 2 (by rfl) ⟨512997, by rfl⟩ : syracuseStep 1367993 = 1025995) B1025995
theorem B909243 : Blo 908576 909243 := bstep (se 1 (by rfl) ⟨681932, by rfl⟩ : syracuseStep 909243 = 1363865) B1363865
theorem B909319 : Blo 908576 909319 := bstep (se 1 (by rfl) ⟨681989, by rfl⟩ : syracuseStep 909319 = 1363979) B1363979
theorem B1368071 : Blo 908576 1368071 := bstep (se 1 (by rfl) ⟨1026053, by rfl⟩ : syracuseStep 1368071 = 2052107) B2052107
theorem B909327 : Blo 908576 909327 := bstep (se 1 (by rfl) ⟨681995, by rfl⟩ : syracuseStep 909327 = 1363991) B1363991
theorem B4612139 : Blo 908576 4612139 := bstep (se 1 (by rfl) ⟨3459104, by rfl⟩ : syracuseStep 4612139 = 6918209) B6918209
theorem B1368107 : Blo 908576 1368107 := bstep (se 1 (by rfl) ⟨1026080, by rfl⟩ : syracuseStep 1368107 = 2052161) B2052161
theorem B909371 : Blo 908576 909371 := bstep (se 1 (by rfl) ⟨682028, by rfl⟩ : syracuseStep 909371 = 1364057) B1364057
theorem B1368137 : Blo 908576 1368137 := bstep (se 2 (by rfl) ⟨513051, by rfl⟩ : syracuseStep 1368137 = 1026103) B1026103
theorem B909447 : Blo 908576 909447 := bstep (se 1 (by rfl) ⟨682085, by rfl⟩ : syracuseStep 909447 = 1364171) B1364171
theorem B909455 : Blo 908576 909455 := bstep (se 1 (by rfl) ⟨682091, by rfl⟩ : syracuseStep 909455 = 1364183) B1364183
theorem B2187449 : Blo 908576 2187449 := bstep (se 2 (by rfl) ⟨820293, by rfl⟩ : syracuseStep 2187449 = 1640587) B1640587
theorem B909499 : Blo 908576 909499 := bstep (se 1 (by rfl) ⟨682124, by rfl⟩ : syracuseStep 909499 = 1364249) B1364249
theorem B1368251 : Blo 908576 1368251 := bstep (se 1 (by rfl) ⟨1026188, by rfl⟩ : syracuseStep 1368251 = 2052377) B2052377
theorem B10379501 : Blo 908576 10379501 := bstep (se 3 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 10379501 = 3892313) B3892313
theorem B1368311 : Blo 908576 1368311 := bstep (se 1 (by rfl) ⟨1026233, by rfl⟩ : syracuseStep 1368311 = 2052467) B2052467
theorem B909575 : Blo 908576 909575 := bstep (se 1 (by rfl) ⟨682181, by rfl⟩ : syracuseStep 909575 = 1364363) B1364363
theorem B909583 : Blo 908576 909583 := bstep (se 1 (by rfl) ⟨682187, by rfl⟩ : syracuseStep 909583 = 1364375) B1364375
theorem B1368335 : Blo 908576 1368335 := bstep (se 1 (by rfl) ⟨1026251, by rfl⟩ : syracuseStep 1368335 = 2052503) B2052503
theorem B1368377 : Blo 908576 1368377 := bstep (se 2 (by rfl) ⟨513141, by rfl⟩ : syracuseStep 1368377 = 1026283) B1026283
theorem B909627 : Blo 908576 909627 := bstep (se 1 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 909627 = 1364441) B1364441
theorem B909703 : Blo 908576 909703 := bstep (se 1 (by rfl) ⟨682277, by rfl⟩ : syracuseStep 909703 = 1364555) B1364555
theorem B1368455 : Blo 908576 1368455 := bstep (se 1 (by rfl) ⟨1026341, by rfl⟩ : syracuseStep 1368455 = 2052683) B2052683
theorem B909711 : Blo 908576 909711 := bstep (se 1 (by rfl) ⟨682283, by rfl⟩ : syracuseStep 909711 = 1364567) B1364567
theorem B1368491 : Blo 908576 1368491 := bstep (se 1 (by rfl) ⟨1026368, by rfl⟩ : syracuseStep 1368491 = 2052737) B2052737
theorem B909755 : Blo 908576 909755 := bstep (se 1 (by rfl) ⟨682316, by rfl⟩ : syracuseStep 909755 = 1364633) B1364633
theorem B1368521 : Blo 908576 1368521 := bstep (se 2 (by rfl) ⟨513195, by rfl⟩ : syracuseStep 1368521 = 1026391) B1026391
theorem B3891665 : Blo 908576 3891665 := bstep (se 2 (by rfl) ⟨1459374, by rfl⟩ : syracuseStep 3891665 = 2918749) B2918749
theorem B6644227 : Blo 908576 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B909831 : Blo 908576 909831 := bstep (se 1 (by rfl) ⟨682373, by rfl⟩ : syracuseStep 909831 = 1364747) B1364747
theorem B909839 : Blo 908576 909839 := bstep (se 1 (by rfl) ⟨682379, by rfl⟩ : syracuseStep 909839 = 1364759) B1364759
theorem B909883 : Blo 908576 909883 := bstep (se 1 (by rfl) ⟨682412, by rfl⟩ : syracuseStep 909883 = 1364825) B1364825
theorem B1368635 : Blo 908576 1368635 := bstep (se 1 (by rfl) ⟨1026476, by rfl⟩ : syracuseStep 1368635 = 2052953) B2052953
theorem B3695165 : Blo 908576 3695165 := bstep (se 3 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 3695165 = 1385687) B1385687
theorem B3072599 : Blo 908576 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B1368695 : Blo 908576 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B909959 : Blo 908576 909959 := bstep (se 1 (by rfl) ⟨682469, by rfl⟩ : syracuseStep 909959 = 1364939) B1364939
theorem B909967 : Blo 908576 909967 := bstep (se 1 (by rfl) ⟨682475, by rfl⟩ : syracuseStep 909967 = 1364951) B1364951
theorem B1368719 : Blo 908576 1368719 := bstep (se 1 (by rfl) ⟨1026539, by rfl⟩ : syracuseStep 1368719 = 2053079) B2053079
theorem B1368761 : Blo 908576 1368761 := bstep (se 2 (by rfl) ⟨513285, by rfl⟩ : syracuseStep 1368761 = 1026571) B1026571
theorem B910011 : Blo 908576 910011 := bstep (se 1 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 910011 = 1365017) B1365017
theorem B910087 : Blo 908576 910087 := bstep (se 1 (by rfl) ⟨682565, by rfl⟩ : syracuseStep 910087 = 1365131) B1365131
theorem B1368839 : Blo 908576 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B2188043 : Blo 908576 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B910095 : Blo 908576 910095 := bstep (se 1 (by rfl) ⟨682571, by rfl⟩ : syracuseStep 910095 = 1365143) B1365143
theorem B8741681 : Blo 908576 8741681 := bstep (se 2 (by rfl) ⟨3278130, by rfl⟩ : syracuseStep 8741681 = 6556261) B6556261
theorem B910139 : Blo 908576 910139 := bstep (se 1 (by rfl) ⟨682604, by rfl⟩ : syracuseStep 910139 = 1365209) B1365209
theorem B910215 : Blo 908576 910215 := bstep (se 1 (by rfl) ⟨682661, by rfl⟩ : syracuseStep 910215 = 1365323) B1365323
theorem B910223 : Blo 908576 910223 := bstep (se 1 (by rfl) ⟨682667, by rfl⟩ : syracuseStep 910223 = 1365335) B1365335
theorem B910267 : Blo 908576 910267 := bstep (se 1 (by rfl) ⟨682700, by rfl⟩ : syracuseStep 910267 = 1365401) B1365401
theorem B910343 : Blo 908576 910343 := bstep (se 1 (by rfl) ⟨682757, by rfl⟩ : syracuseStep 910343 = 1365515) B1365515
theorem B910351 : Blo 908576 910351 := bstep (se 1 (by rfl) ⟨682763, by rfl⟩ : syracuseStep 910351 = 1365527) B1365527
theorem B910395 : Blo 908576 910395 := bstep (se 1 (by rfl) ⟨682796, by rfl⟩ : syracuseStep 910395 = 1365593) B1365593
theorem B3073085 : Blo 908576 3073085 := bstep (se 3 (by rfl) ⟨576203, by rfl⟩ : syracuseStep 3073085 = 1152407) B1152407
theorem B22176899 : Blo 908576 22176899 := bstep (se 1 (by rfl) ⟨16632674, by rfl⟩ : syracuseStep 22176899 = 33265349) B33265349
theorem B910471 : Blo 908576 910471 := bstep (se 1 (by rfl) ⟨682853, by rfl⟩ : syracuseStep 910471 = 1365707) B1365707
theorem B910479 : Blo 908576 910479 := bstep (se 1 (by rfl) ⟨682859, by rfl⟩ : syracuseStep 910479 = 1365719) B1365719
theorem B4678829 : Blo 908576 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B910523 : Blo 908576 910523 := bstep (se 1 (by rfl) ⟨682892, by rfl⟩ : syracuseStep 910523 = 1365785) B1365785
theorem B910599 : Blo 908576 910599 := bstep (se 1 (by rfl) ⟨682949, by rfl⟩ : syracuseStep 910599 = 1365899) B1365899
theorem B910607 : Blo 908576 910607 := bstep (se 1 (by rfl) ⟨682955, by rfl⟩ : syracuseStep 910607 = 1365911) B1365911
theorem B910651 : Blo 908576 910651 := bstep (se 1 (by rfl) ⟨682988, by rfl⟩ : syracuseStep 910651 = 1365977) B1365977
theorem B4613435 : Blo 908576 4613435 := bstep (se 1 (by rfl) ⟨3460076, by rfl⟩ : syracuseStep 4613435 = 6920153) B6920153
theorem B910727 : Blo 908576 910727 := bstep (se 1 (by rfl) ⟨683045, by rfl⟩ : syracuseStep 910727 = 1366091) B1366091
theorem B910735 : Blo 908576 910735 := bstep (se 1 (by rfl) ⟨683051, by rfl⟩ : syracuseStep 910735 = 1366103) B1366103
theorem B8742329 : Blo 908576 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B910779 : Blo 908576 910779 := bstep (se 1 (by rfl) ⟨683084, by rfl⟩ : syracuseStep 910779 = 1366169) B1366169
theorem B1729993 : Blo 908576 1729993 := bstep (se 2 (by rfl) ⟨648747, by rfl⟩ : syracuseStep 1729993 = 1297495) B1297495
theorem B4613597 : Blo 908576 4613597 := bstep (se 3 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 4613597 = 1730099) B1730099
theorem B910855 : Blo 908576 910855 := bstep (se 1 (by rfl) ⟨683141, by rfl⟩ : syracuseStep 910855 = 1366283) B1366283
theorem B910863 : Blo 908576 910863 := bstep (se 1 (by rfl) ⟨683147, by rfl⟩ : syracuseStep 910863 = 1366295) B1366295
theorem B910907 : Blo 908576 910907 := bstep (se 1 (by rfl) ⟨683180, by rfl⟩ : syracuseStep 910907 = 1366361) B1366361
theorem B1533559 : Blo 908576 1533559 := bstep (se 1 (by rfl) ⟨1150169, by rfl⟩ : syracuseStep 1533559 = 2300339) B2300339
theorem B910983 : Blo 908576 910983 := bstep (se 1 (by rfl) ⟨683237, by rfl⟩ : syracuseStep 910983 = 1366475) B1366475
theorem B910991 : Blo 908576 910991 := bstep (se 1 (by rfl) ⟨683243, by rfl⟩ : syracuseStep 910991 = 1366487) B1366487
theorem B911035 : Blo 908576 911035 := bstep (se 1 (by rfl) ⟨683276, by rfl⟩ : syracuseStep 911035 = 1366553) B1366553
theorem B6219521 : Blo 908576 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B14018305 : Blo 908576 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B911111 : Blo 908576 911111 := bstep (se 1 (by rfl) ⟨683333, by rfl⟩ : syracuseStep 911111 = 1366667) B1366667
theorem B911119 : Blo 908576 911119 := bstep (se 1 (by rfl) ⟨683339, by rfl⟩ : syracuseStep 911119 = 1366679) B1366679
theorem B4613921 : Blo 908576 4613921 := bstep (se 2 (by rfl) ⟨1730220, by rfl⟩ : syracuseStep 4613921 = 3460441) B3460441
theorem B1533755 : Blo 908576 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B911163 : Blo 908576 911163 := bstep (se 1 (by rfl) ⟨683372, by rfl⟩ : syracuseStep 911163 = 1366745) B1366745
theorem B911239 : Blo 908576 911239 := bstep (se 1 (by rfl) ⟨683429, by rfl⟩ : syracuseStep 911239 = 1366859) B1366859
theorem B911247 : Blo 908576 911247 := bstep (se 1 (by rfl) ⟨683435, by rfl⟩ : syracuseStep 911247 = 1366871) B1366871
theorem B911291 : Blo 908576 911291 := bstep (se 1 (by rfl) ⟨683468, by rfl⟩ : syracuseStep 911291 = 1366937) B1366937
theorem B911367 : Blo 908576 911367 := bstep (se 1 (by rfl) ⟨683525, by rfl⟩ : syracuseStep 911367 = 1367051) B1367051
theorem B911375 : Blo 908576 911375 := bstep (se 1 (by rfl) ⟨683531, by rfl⟩ : syracuseStep 911375 = 1367063) B1367063
theorem B911419 : Blo 908576 911419 := bstep (se 1 (by rfl) ⟨683564, by rfl⟩ : syracuseStep 911419 = 1367129) B1367129
theorem B911495 : Blo 908576 911495 := bstep (se 1 (by rfl) ⟨683621, by rfl⟩ : syracuseStep 911495 = 1367243) B1367243
theorem B911503 : Blo 908576 911503 := bstep (se 1 (by rfl) ⟨683627, by rfl⟩ : syracuseStep 911503 = 1367255) B1367255
theorem B911547 : Blo 908576 911547 := bstep (se 1 (by rfl) ⟨683660, by rfl⟩ : syracuseStep 911547 = 1367321) B1367321
theorem B1534153 : Blo 908576 1534153 := bstep (se 2 (by rfl) ⟨575307, by rfl⟩ : syracuseStep 1534153 = 1150615) B1150615
theorem B5826761 : Blo 908576 5826761 := bstep (se 2 (by rfl) ⟨2185035, by rfl⟩ : syracuseStep 5826761 = 4370071) B4370071
theorem B911623 : Blo 908576 911623 := bstep (se 1 (by rfl) ⟨683717, by rfl⟩ : syracuseStep 911623 = 1367435) B1367435
theorem B911631 : Blo 908576 911631 := bstep (se 1 (by rfl) ⟨683723, by rfl⟩ : syracuseStep 911631 = 1367447) B1367447
theorem B911675 : Blo 908576 911675 := bstep (se 1 (by rfl) ⟨683756, by rfl⟩ : syracuseStep 911675 = 1367513) B1367513
theorem B911751 : Blo 908576 911751 := bstep (se 1 (by rfl) ⟨683813, by rfl⟩ : syracuseStep 911751 = 1367627) B1367627
theorem B911759 : Blo 908576 911759 := bstep (se 1 (by rfl) ⟨683819, by rfl⟩ : syracuseStep 911759 = 1367639) B1367639
theorem B3074489 : Blo 908576 3074489 := bstep (se 2 (by rfl) ⟨1152933, by rfl⟩ : syracuseStep 3074489 = 2305867) B2305867
theorem B911803 : Blo 908576 911803 := bstep (se 1 (by rfl) ⟨683852, by rfl⟩ : syracuseStep 911803 = 1367705) B1367705
theorem B911879 : Blo 908576 911879 := bstep (se 1 (by rfl) ⟨683909, by rfl⟩ : syracuseStep 911879 = 1367819) B1367819
theorem B911887 : Blo 908576 911887 := bstep (se 1 (by rfl) ⟨683915, by rfl⟩ : syracuseStep 911887 = 1367831) B1367831
theorem B911931 : Blo 908576 911931 := bstep (se 1 (by rfl) ⟨683948, by rfl⟩ : syracuseStep 911931 = 1367897) B1367897
theorem B912007 : Blo 908576 912007 := bstep (se 1 (by rfl) ⟨684005, by rfl⟩ : syracuseStep 912007 = 1368011) B1368011
theorem B912015 : Blo 908576 912015 := bstep (se 1 (by rfl) ⟨684011, by rfl⟩ : syracuseStep 912015 = 1368023) B1368023
theorem B912059 : Blo 908576 912059 := bstep (se 1 (by rfl) ⟨684044, by rfl⟩ : syracuseStep 912059 = 1368089) B1368089
theorem B4614893 : Blo 908576 4614893 := bstep (se 3 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 4614893 = 1730585) B1730585
theorem B912135 : Blo 908576 912135 := bstep (se 1 (by rfl) ⟨684101, by rfl⟩ : syracuseStep 912135 = 1368203) B1368203
theorem B912143 : Blo 908576 912143 := bstep (se 1 (by rfl) ⟨684107, by rfl⟩ : syracuseStep 912143 = 1368215) B1368215
theorem B912187 : Blo 908576 912187 := bstep (se 1 (by rfl) ⟨684140, by rfl⟩ : syracuseStep 912187 = 1368281) B1368281
theorem B1534855 : Blo 908576 1534855 := bstep (se 1 (by rfl) ⟨1151141, by rfl⟩ : syracuseStep 1534855 = 2302283) B2302283
theorem B912263 : Blo 908576 912263 := bstep (se 1 (by rfl) ⟨684197, by rfl⟩ : syracuseStep 912263 = 1368395) B1368395
theorem B912271 : Blo 908576 912271 := bstep (se 1 (by rfl) ⟨684203, by rfl⟩ : syracuseStep 912271 = 1368407) B1368407
theorem B912315 : Blo 908576 912315 := bstep (se 1 (by rfl) ⟨684236, by rfl⟩ : syracuseStep 912315 = 1368473) B1368473
theorem B912391 : Blo 908576 912391 := bstep (se 1 (by rfl) ⟨684293, by rfl⟩ : syracuseStep 912391 = 1368587) B1368587
theorem B3075083 : Blo 908576 3075083 := bstep (se 1 (by rfl) ⟨2306312, by rfl⟩ : syracuseStep 3075083 = 4612625) B4612625
theorem B5336075 : Blo 908576 5336075 := bstep (se 1 (by rfl) ⟨4002056, by rfl⟩ : syracuseStep 5336075 = 8004113) B8004113
theorem B912399 : Blo 908576 912399 := bstep (se 1 (by rfl) ⟨684299, by rfl⟩ : syracuseStep 912399 = 1368599) B1368599
theorem B912443 : Blo 908576 912443 := bstep (se 1 (by rfl) ⟨684332, by rfl⟩ : syracuseStep 912443 = 1368665) B1368665
theorem B3075191 : Blo 908576 3075191 := bstep (se 1 (by rfl) ⟨2306393, by rfl⟩ : syracuseStep 3075191 = 4612787) B4612787
theorem B912519 : Blo 908576 912519 := bstep (se 1 (by rfl) ⟨684389, by rfl⟩ : syracuseStep 912519 = 1368779) B1368779
theorem B912527 : Blo 908576 912527 := bstep (se 1 (by rfl) ⟨684395, by rfl⟩ : syracuseStep 912527 = 1368791) B1368791
theorem B912571 : Blo 908576 912571 := bstep (se 1 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 912571 = 1368857) B1368857
theorem B2911547 : Blo 908576 2911547 := bstep (se 1 (by rfl) ⟨2183660, by rfl⟩ : syracuseStep 2911547 = 4367321) B4367321
theorem B1535503 : Blo 908576 1535503 := bstep (se 1 (by rfl) ⟨1151627, by rfl⟩ : syracuseStep 1535503 = 2303255) B2303255
theorem B4615703 : Blo 908576 4615703 := bstep (se 1 (by rfl) ⟨3461777, by rfl⟩ : syracuseStep 4615703 = 6923555) B6923555
theorem B2911945 : Blo 908576 2911945 := bstep (se 2 (by rfl) ⟨1091979, by rfl⟩ : syracuseStep 2911945 = 2183959) B2183959
theorem B3075785 : Blo 908576 3075785 := bstep (se 2 (by rfl) ⟨1153419, by rfl⟩ : syracuseStep 3075785 = 2306839) B2306839
theorem B2912059 : Blo 908576 2912059 := bstep (se 1 (by rfl) ⟨2184044, by rfl⟩ : syracuseStep 2912059 = 4368089) B4368089
theorem B9826123 : Blo 908576 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B4157369 : Blo 908576 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B1536043 : Blo 908576 1536043 := bstep (se 1 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 1536043 = 2304065) B2304065
theorem B1536185 : Blo 908576 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B3076487 : Blo 908576 3076487 := bstep (se 1 (by rfl) ⟨2307365, by rfl⟩ : syracuseStep 3076487 = 4614731) B4614731
theorem B10383875 : Blo 908576 10383875 := bstep (se 1 (by rfl) ⟨7787906, by rfl⟩ : syracuseStep 10383875 = 15575813) B15575813
theorem B3076865 : Blo 908576 3076865 := bstep (se 2 (by rfl) ⟨1153824, by rfl⟩ : syracuseStep 3076865 = 2307649) B2307649
theorem B1536887 : Blo 908576 1536887 := bstep (se 1 (by rfl) ⟨1152665, by rfl⟩ : syracuseStep 1536887 = 2305331) B2305331
theorem B2192417 : Blo 908576 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B37418273 : Blo 908576 37418273 := bstep (se 2 (by rfl) ⟨14031852, by rfl⟩ : syracuseStep 37418273 = 28063705) B28063705
theorem B1537339 : Blo 908576 1537339 := bstep (se 1 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 1537339 = 2306009) B2306009
theorem B1537481 : Blo 908576 1537481 := bstep (se 2 (by rfl) ⟨576555, by rfl⟩ : syracuseStep 1537481 = 1153111) B1153111
theorem B2913803 : Blo 908576 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B3077675 : Blo 908576 3077675 := bstep (se 1 (by rfl) ⟨2308256, by rfl⟩ : syracuseStep 3077675 = 4616513) B4616513
theorem B23983685 : Blo 908576 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B7894721 : Blo 908576 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B5830451 : Blo 908576 5830451 := bstep (se 1 (by rfl) ⟨4372838, by rfl⟩ : syracuseStep 5830451 = 8745677) B8745677
theorem B3897355 : Blo 908576 3897355 := bstep (se 1 (by rfl) ⟨2923016, by rfl⟩ : syracuseStep 3897355 = 5846033) B5846033
theorem B5830679 : Blo 908576 5830679 := bstep (se 1 (by rfl) ⟨4373009, by rfl⟩ : syracuseStep 5830679 = 8746019) B8746019
theorem B1538183 : Blo 908576 1538183 := bstep (se 1 (by rfl) ⟨1153637, by rfl⟩ : syracuseStep 1538183 = 2307275) B2307275
theorem B4618781 : Blo 908576 4618781 := bstep (se 3 (by rfl) ⟨866021, by rfl⟩ : syracuseStep 4618781 = 1732043) B1732043
theorem B2587403 : Blo 908576 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B1538831 : Blo 908576 1538831 := bstep (se 1 (by rfl) ⟨1154123, by rfl⟩ : syracuseStep 1538831 = 2308247) B2308247
theorem B3078971 : Blo 908576 3078971 := bstep (se 1 (by rfl) ⟨2309228, by rfl⟩ : syracuseStep 3078971 = 4618457) B4618457
theorem B4619267 : Blo 908576 4619267 := bstep (se 1 (by rfl) ⟨3464450, by rfl⟩ : syracuseStep 4619267 = 6928901) B6928901
theorem B26213381 : Blo 908576 26213381 := bstep (se 4 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 26213381 = 4915009) B4915009
theorem B5176493 : Blo 908576 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B3079457 : Blo 908576 3079457 := bstep (se 2 (by rfl) ⟨1154796, by rfl⟩ : syracuseStep 3079457 = 2309593) B2309593
theorem B1539371 : Blo 908576 1539371 := bstep (se 1 (by rfl) ⟨1154528, by rfl⟩ : syracuseStep 1539371 = 2309057) B2309057
theorem B4161053 : Blo 908576 4161053 := bstep (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) B1560395
theorem B1900217 : Blo 908576 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B1539769 : Blo 908576 1539769 := bstep (se 2 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 1539769 = 1154827) B1154827
theorem B3506177 : Blo 908576 3506177 := bstep (se 2 (by rfl) ⟨1314816, by rfl⟩ : syracuseStep 3506177 = 2629633) B2629633
theorem B6225977 : Blo 908576 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B3113417 : Blo 908576 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B1311671 : Blo 908576 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B2589853 : Blo 908576 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B1869331 : Blo 908576 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B5178977 : Blo 908576 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B1640455 : Blo 908576 1640455 := bstep (se 1 (by rfl) ⟨1230341, by rfl⟩ : syracuseStep 1640455 = 2460683) B2460683
theorem B9865223 : Blo 908576 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B11995877 : Blo 908576 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B106597387 : Blo 908576 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B5180435 : Blo 908576 5180435 := bstep (se 1 (by rfl) ⟨3885326, by rfl⟩ : syracuseStep 5180435 = 7770653) B7770653
theorem B2591801 : Blo 908576 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B11079301 : Blo 908576 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B1150939 : Blo 908576 1150939 := bstep (se 1 (by rfl) ⟨863204, by rfl⟩ : syracuseStep 1150939 = 1726409) B1726409
theorem B13111307 : Blo 908576 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B7770275 : Blo 908576 7770275 := bstep (se 1 (by rfl) ⟨5827706, by rfl⟩ : syracuseStep 7770275 = 11655413) B11655413
theorem B5837345 : Blo 908576 5837345 := bstep (se 2 (by rfl) ⟨2189004, by rfl⟩ : syracuseStep 5837345 = 4378009) B4378009
theorem B1643527 : Blo 908576 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B1643599 : Blo 908576 1643599 := bstep (se 1 (by rfl) ⟨1232699, by rfl⟩ : syracuseStep 1643599 = 2465399) B2465399
theorem B26645861 : Blo 908576 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B6919667 : Blo 908576 6919667 := bstep (se 1 (by rfl) ⟨5189750, by rfl⟩ : syracuseStep 6919667 = 10379501) B10379501
theorem B5183099 : Blo 908576 5183099 := bstep (se 1 (by rfl) ⟨3887324, by rfl⟩ : syracuseStep 5183099 = 7774649) B7774649
theorem B2594443 : Blo 908576 2594443 := bstep (se 1 (by rfl) ⟨1945832, by rfl⟩ : syracuseStep 2594443 = 3891665) B3891665
theorem B2463443 : Blo 908576 2463443 := bstep (se 1 (by rfl) ⟨1847582, by rfl⟩ : syracuseStep 2463443 = 3695165) B3695165
theorem B5183351 : Blo 908576 5183351 := bstep (se 1 (by rfl) ⟨3887513, by rfl⟩ : syracuseStep 5183351 = 7775027) B7775027
theorem B2627603 : Blo 908576 2627603 := bstep (se 1 (by rfl) ⟨1970702, by rfl⟩ : syracuseStep 2627603 = 3941405) B3941405
theorem B14784599 : Blo 908576 14784599 := bstep (se 1 (by rfl) ⟨11088449, by rfl⟩ : syracuseStep 14784599 = 22176899) B22176899
theorem B3119219 : Blo 908576 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1022503 : Blo 908576 1022503 := bstep (se 1 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 1022503 = 1533755) B1533755
theorem B2628425 : Blo 908576 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B2301007 : Blo 908576 2301007 := bstep (se 1 (by rfl) ⟨1725755, by rfl⟩ : syracuseStep 2301007 = 3451511) B3451511
theorem B7019723 : Blo 908576 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B1941031 : Blo 908576 1941031 := bstep (se 1 (by rfl) ⟨1455773, by rfl⟩ : syracuseStep 1941031 = 2911547) B2911547
theorem B2301655 : Blo 908576 2301655 := bstep (se 1 (by rfl) ⟨1726241, by rfl⟩ : syracuseStep 2301655 = 3452483) B3452483
theorem B1843049 : Blo 908576 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B2301959 : Blo 908576 2301959 := bstep (se 1 (by rfl) ⟨1726469, by rfl⟩ : syracuseStep 2301959 = 3452939) B3452939
theorem B14229533 : Blo 908576 14229533 := bstep (se 3 (by rfl) ⟨2668037, by rfl⟩ : syracuseStep 14229533 = 5336075) B5336075
theorem B1024123 : Blo 908576 1024123 := bstep (se 1 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 1024123 = 1536185) B1536185
theorem B6922583 : Blo 908576 6922583 := bstep (se 1 (by rfl) ⟨5191937, by rfl⟩ : syracuseStep 6922583 = 10383875) B10383875
theorem B3285353 : Blo 908576 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B12460493 : Blo 908576 12460493 := bstep (se 3 (by rfl) ⟨2336342, by rfl⟩ : syracuseStep 12460493 = 4672685) B4672685
theorem B1024591 : Blo 908576 1024591 := bstep (se 1 (by rfl) ⟨768443, by rfl⟩ : syracuseStep 1024591 = 1536887) B1536887
theorem B24945515 : Blo 908576 24945515 := bstep (se 1 (by rfl) ⟨18709136, by rfl⟩ : syracuseStep 24945515 = 37418273) B37418273
theorem B1024987 : Blo 908576 1024987 := bstep (se 1 (by rfl) ⟨768740, by rfl⟩ : syracuseStep 1024987 = 1537481) B1537481
theorem B1942535 : Blo 908576 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B5547437 : Blo 908576 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B1025455 : Blo 908576 1025455 := bstep (se 1 (by rfl) ⟨769091, by rfl⟩ : syracuseStep 1025455 = 1538183) B1538183
theorem B5187017 : Blo 908576 5187017 := bstep (se 2 (by rfl) ⟨1945131, by rfl⟩ : syracuseStep 5187017 = 3890263) B3890263
theorem B1025887 : Blo 908576 1025887 := bstep (se 1 (by rfl) ⟨769415, by rfl⟩ : syracuseStep 1025887 = 1538831) B1538831
theorem B2631599 : Blo 908576 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B17475587 : Blo 908576 17475587 := bstep (se 1 (by rfl) ⟨13106690, by rfl⟩ : syracuseStep 17475587 = 26213381) B26213381
theorem B3450995 : Blo 908576 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B1026247 : Blo 908576 1026247 := bstep (se 1 (by rfl) ⟨769685, by rfl⟩ : syracuseStep 1026247 = 1539371) B1539371
theorem B2304247 : Blo 908576 2304247 := bstep (se 1 (by rfl) ⟨1728185, by rfl⟩ : syracuseStep 2304247 = 3456371) B3456371
theorem B2304521 : Blo 908576 2304521 := bstep (se 2 (by rfl) ⟨864195, by rfl⟩ : syracuseStep 2304521 = 1728391) B1728391
theorem B2304551 : Blo 908576 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B2304875 : Blo 908576 2304875 := bstep (se 1 (by rfl) ⟨1728656, by rfl⟩ : syracuseStep 2304875 = 3457313) B3457313
theorem B7187429 : Blo 908576 7187429 := bstep (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) B1347643
theorem B3288235 : Blo 908576 3288235 := bstep (se 1 (by rfl) ⟨2466176, by rfl⟩ : syracuseStep 3288235 = 4932353) B4932353
theorem B8858969 : Blo 908576 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B6565283 : Blo 908576 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B2305523 : Blo 908576 2305523 := bstep (se 1 (by rfl) ⟨1729142, by rfl⟩ : syracuseStep 2305523 = 3458285) B3458285
theorem B7384715 : Blo 908576 7384715 := bstep (se 1 (by rfl) ⟨5538536, by rfl⟩ : syracuseStep 7384715 = 11077073) B11077073
theorem B3452665 : Blo 908576 3452665 := bstep (se 2 (by rfl) ⟨1294749, by rfl⟩ : syracuseStep 3452665 = 2589499) B2589499
theorem B3288899 : Blo 908576 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B1093483 : Blo 908576 1093483 := bstep (se 1 (by rfl) ⟨820112, by rfl⟩ : syracuseStep 1093483 = 1640225) B1640225
theorem B2305979 : Blo 908576 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B7385165 : Blo 908576 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B10498211 : Blo 908576 10498211 := bstep (se 1 (by rfl) ⟨7873658, by rfl⟩ : syracuseStep 10498211 = 15747317) B15747317
theorem B2633975 : Blo 908576 2633975 := bstep (se 1 (by rfl) ⟨1975481, by rfl⟩ : syracuseStep 2633975 = 3950963) B3950963
theorem B4600151 : Blo 908576 4600151 := bstep (se 1 (by rfl) ⟨3450113, by rfl⟩ : syracuseStep 4600151 = 6900227) B6900227
theorem B2306657 : Blo 908576 2306657 := bstep (se 2 (by rfl) ⟨864996, by rfl⟩ : syracuseStep 2306657 = 1729993) B1729993
theorem B2044745 : Blo 908576 2044745 := bstep (se 2 (by rfl) ⟨766779, by rfl⟩ : syracuseStep 2044745 = 1533559) B1533559
theorem B14398361 : Blo 908576 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B18691073 : Blo 908576 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B3454109 : Blo 908576 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B3454123 : Blo 908576 3454123 := bstep (se 1 (by rfl) ⟨2590592, by rfl⟩ : syracuseStep 3454123 = 5181185) B5181185
theorem B3454427 : Blo 908576 3454427 := bstep (se 1 (by rfl) ⟨2590820, by rfl⟩ : syracuseStep 3454427 = 5181641) B5181641
theorem B2045537 : Blo 908576 2045537 := bstep (se 2 (by rfl) ⟨767076, by rfl⟩ : syracuseStep 2045537 = 1534153) B1534153
theorem B1095367 : Blo 908576 1095367 := bstep (se 1 (by rfl) ⟨821525, by rfl⟩ : syracuseStep 1095367 = 1643051) B1643051
theorem B4372319 : Blo 908576 4372319 := bstep (se 1 (by rfl) ⟨3279239, by rfl⟩ : syracuseStep 4372319 = 6558479) B6558479
theorem B2045879 : Blo 908576 2045879 := bstep (se 1 (by rfl) ⟨1534409, by rfl⟩ : syracuseStep 2045879 = 3068819) B3068819
theorem B2308115 : Blo 908576 2308115 := bstep (se 1 (by rfl) ⟨1731086, by rfl⟩ : syracuseStep 2308115 = 3462173) B3462173
theorem B15350219 : Blo 908576 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B2308571 : Blo 908576 2308571 := bstep (se 1 (by rfl) ⟨1731428, by rfl⟩ : syracuseStep 2308571 = 3462857) B3462857
theorem B2046473 : Blo 908576 2046473 := bstep (se 2 (by rfl) ⟨767427, by rfl⟩ : syracuseStep 2046473 = 1534855) B1534855
theorem B11057849 : Blo 908576 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B4373203 : Blo 908576 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B3324739 : Blo 908576 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B2046815 : Blo 908576 2046815 := bstep (se 1 (by rfl) ⟨1535111, by rfl⟩ : syracuseStep 2046815 = 3070223) B3070223
theorem B2046995 : Blo 908576 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B2047337 : Blo 908576 2047337 := bstep (se 2 (by rfl) ⟨767751, by rfl⟩ : syracuseStep 2047337 = 1535503) B1535503
theorem B1293833 : Blo 908576 1293833 := bstep (se 2 (by rfl) ⟨485187, by rfl⟩ : syracuseStep 1293833 = 970375) B970375
theorem B3882593 : Blo 908576 3882593 := bstep (se 2 (by rfl) ⟨1455972, by rfl⟩ : syracuseStep 3882593 = 2911945) B2911945
theorem B2309755 : Blo 908576 2309755 := bstep (se 1 (by rfl) ⟨1732316, by rfl⟩ : syracuseStep 2309755 = 3464633) B3464633
theorem B1556167 : Blo 908576 1556167 := bstep (se 1 (by rfl) ⟨1167125, by rfl⟩ : syracuseStep 1556167 = 2334251) B2334251
theorem B3882745 : Blo 908576 3882745 := bstep (se 2 (by rfl) ⟨1456029, by rfl⟩ : syracuseStep 3882745 = 2912059) B2912059
theorem B4603715 : Blo 908576 4603715 := bstep (se 1 (by rfl) ⟨3452786, by rfl⟩ : syracuseStep 4603715 = 6905573) B6905573
theorem B6242183 : Blo 908576 6242183 := bstep (se 1 (by rfl) ⟨4681637, by rfl⟩ : syracuseStep 6242183 = 9363275) B9363275
theorem B2047931 : Blo 908576 2047931 := bstep (se 1 (by rfl) ⟨1535948, by rfl⟩ : syracuseStep 2047931 = 3071897) B3071897
theorem B3457025 : Blo 908576 3457025 := bstep (se 2 (by rfl) ⟨1296384, by rfl⟩ : syracuseStep 3457025 = 2592769) B2592769
theorem B3457039 : Blo 908576 3457039 := bstep (se 1 (by rfl) ⟨2592779, by rfl⟩ : syracuseStep 3457039 = 5185559) B5185559
theorem B2048057 : Blo 908576 2048057 := bstep (se 2 (by rfl) ⟨768021, by rfl⟩ : syracuseStep 2048057 = 1536043) B1536043
theorem B1458299 : Blo 908576 1458299 := bstep (se 1 (by rfl) ⟨1093724, by rfl⟩ : syracuseStep 1458299 = 2187449) B2187449
theorem B1294699 : Blo 908576 1294699 := bstep (se 1 (by rfl) ⟨971024, by rfl⟩ : syracuseStep 1294699 = 1942049) B1942049
theorem B7979393 : Blo 908576 7979393 := bstep (se 2 (by rfl) ⟨2992272, by rfl⟩ : syracuseStep 7979393 = 5984545) B5984545
theorem B2048399 : Blo 908576 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B1458695 : Blo 908576 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B13124105 : Blo 908576 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B2048723 : Blo 908576 2048723 := bstep (se 1 (by rfl) ⟨1536542, by rfl⟩ : syracuseStep 2048723 = 3073085) B3073085
theorem B1754075 : Blo 908576 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B1295399 : Blo 908576 1295399 := bstep (se 1 (by rfl) ⟨971549, by rfl⟩ : syracuseStep 1295399 = 1943099) B1943099
theorem B4146347 : Blo 908576 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B3458315 : Blo 908576 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B1459529 : Blo 908576 1459529 := bstep (se 2 (by rfl) ⟨547323, by rfl⟩ : syracuseStep 1459529 = 1094647) B1094647
theorem B1459561 : Blo 908576 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B3884507 : Blo 908576 3884507 := bstep (se 1 (by rfl) ⟨2913380, by rfl⟩ : syracuseStep 3884507 = 5826761) B5826761
theorem B2049659 : Blo 908576 2049659 := bstep (se 1 (by rfl) ⟨1537244, by rfl⟩ : syracuseStep 2049659 = 3074489) B3074489
theorem B1558187 : Blo 908576 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B3458771 : Blo 908576 3458771 := bstep (se 1 (by rfl) ⟨2594078, by rfl⟩ : syracuseStep 3458771 = 5188157) B5188157
theorem B2049785 : Blo 908576 2049785 := bstep (se 2 (by rfl) ⟨768669, by rfl⟩ : syracuseStep 2049785 = 1537339) B1537339
theorem B2050055 : Blo 908576 2050055 := bstep (se 1 (by rfl) ⟨1537541, by rfl⟩ : syracuseStep 2050055 = 3075083) B3075083
theorem B6899741 : Blo 908576 6899741 := bstep (se 3 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 6899741 = 2587403) B2587403
theorem B2050127 : Blo 908576 2050127 := bstep (se 1 (by rfl) ⟨1537595, by rfl⟩ : syracuseStep 2050127 = 3075191) B3075191
theorem B1755307 : Blo 908576 1755307 := bstep (se 1 (by rfl) ⟨1316480, by rfl⟩ : syracuseStep 1755307 = 2632961) B2632961
theorem B1296823 : Blo 908576 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B2050523 : Blo 908576 2050523 := bstep (se 1 (by rfl) ⟨1537892, by rfl⟩ : syracuseStep 2050523 = 3075785) B3075785
theorem B2771579 : Blo 908576 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B5196473 : Blo 908576 5196473 := bstep (se 2 (by rfl) ⟨1948677, by rfl⟩ : syracuseStep 5196473 = 3897355) B3897355
theorem B3459773 : Blo 908576 3459773 := bstep (se 3 (by rfl) ⟨648707, by rfl⟩ : syracuseStep 3459773 = 1297415) B1297415
theorem B4606793 : Blo 908576 4606793 := bstep (se 2 (by rfl) ⟨1727547, by rfl⟩ : syracuseStep 4606793 = 3455095) B3455095
theorem B2050991 : Blo 908576 2050991 := bstep (se 1 (by rfl) ⟨1538243, by rfl⟩ : syracuseStep 2050991 = 3076487) B3076487
theorem B1362953 : Blo 908576 1362953 := bstep (se 2 (by rfl) ⟨511107, by rfl⟩ : syracuseStep 1362953 = 1022215) B1022215
theorem B1362983 : Blo 908576 1362983 := bstep (se 1 (by rfl) ⟨1022237, by rfl⟩ : syracuseStep 1362983 = 2044475) B2044475
theorem B1363067 : Blo 908576 1363067 := bstep (se 1 (by rfl) ⟨1022300, by rfl⟩ : syracuseStep 1363067 = 2044601) B2044601
theorem B3067037 : Blo 908576 3067037 := bstep (se 3 (by rfl) ⟨575069, by rfl⟩ : syracuseStep 3067037 = 1150139) B1150139
theorem B2051243 : Blo 908576 2051243 := bstep (se 1 (by rfl) ⟨1538432, by rfl⟩ : syracuseStep 2051243 = 3076865) B3076865
theorem B1363193 : Blo 908576 1363193 := bstep (se 2 (by rfl) ⟨511197, by rfl⟩ : syracuseStep 1363193 = 1022395) B1022395
theorem B23317793 : Blo 908576 23317793 := bstep (se 2 (by rfl) ⟨8744172, by rfl⟩ : syracuseStep 23317793 = 17488345) B17488345
theorem B11062565 : Blo 908576 11062565 := bstep (se 4 (by rfl) ⟨1037115, by rfl⟩ : syracuseStep 11062565 = 2074231) B2074231
theorem B1363295 : Blo 908576 1363295 := bstep (se 1 (by rfl) ⟨1022471, by rfl⟩ : syracuseStep 1363295 = 2044943) B2044943
theorem B1363307 : Blo 908576 1363307 := bstep (se 1 (by rfl) ⟨1022480, by rfl⟩ : syracuseStep 1363307 = 2044961) B2044961
theorem B1461611 : Blo 908576 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B1363535 : Blo 908576 1363535 := bstep (se 1 (by rfl) ⟨1022651, by rfl⟩ : syracuseStep 1363535 = 2045303) B2045303
theorem B14012027 : Blo 908576 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B3067577 : Blo 908576 3067577 := bstep (se 2 (by rfl) ⟨1150341, by rfl⟩ : syracuseStep 3067577 = 2300683) B2300683
theorem B1363655 : Blo 908576 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B2051783 : Blo 908576 2051783 := bstep (se 1 (by rfl) ⟨1538837, by rfl⟩ : syracuseStep 2051783 = 3077675) B3077675
theorem B5263147 : Blo 908576 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B1363817 : Blo 908576 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B1298281 : Blo 908576 1298281 := bstep (se 2 (by rfl) ⟨486855, by rfl⟩ : syracuseStep 1298281 = 973711) B973711
theorem B3886967 : Blo 908576 3886967 := bstep (se 1 (by rfl) ⟨2915225, by rfl⟩ : syracuseStep 3886967 = 5830451) B5830451
theorem B1363895 : Blo 908576 1363895 := bstep (se 1 (by rfl) ⟨1022921, by rfl⟩ : syracuseStep 1363895 = 2045843) B2045843
theorem B1363931 : Blo 908576 1363931 := bstep (se 1 (by rfl) ⟨1022948, by rfl⟩ : syracuseStep 1363931 = 2045897) B2045897
theorem B3887119 : Blo 908576 3887119 := bstep (se 1 (by rfl) ⟨2915339, by rfl⟩ : syracuseStep 3887119 = 5830679) B5830679
theorem B13127741 : Blo 908576 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B3461201 : Blo 908576 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B4608089 : Blo 908576 4608089 := bstep (se 2 (by rfl) ⟨1728033, by rfl⟩ : syracuseStep 4608089 = 3456067) B3456067
theorem B3068171 : Blo 908576 3068171 := bstep (se 1 (by rfl) ⟨2301128, by rfl⟩ : syracuseStep 3068171 = 4602257) B4602257
theorem B7786813 : Blo 908576 7786813 := bstep (se 3 (by rfl) ⟨1460027, by rfl⟩ : syracuseStep 7786813 = 2920055) B2920055
theorem B1364399 : Blo 908576 1364399 := bstep (se 1 (by rfl) ⟨1023299, by rfl⟩ : syracuseStep 1364399 = 2046599) B2046599
theorem B5067245 : Blo 908576 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B1364489 : Blo 908576 1364489 := bstep (se 2 (by rfl) ⟨511683, by rfl⟩ : syracuseStep 1364489 = 1023367) B1023367
theorem B1298953 : Blo 908576 1298953 := bstep (se 2 (by rfl) ⟨487107, by rfl⟩ : syracuseStep 1298953 = 974215) B974215
theorem B3068441 : Blo 908576 3068441 := bstep (se 2 (by rfl) ⟨1150665, by rfl⟩ : syracuseStep 3068441 = 2301331) B2301331
theorem B1364519 : Blo 908576 1364519 := bstep (se 1 (by rfl) ⟨1023389, by rfl⟩ : syracuseStep 1364519 = 2046779) B2046779
theorem B2052647 : Blo 908576 2052647 := bstep (se 1 (by rfl) ⟨1539485, by rfl⟩ : syracuseStep 2052647 = 3078971) B3078971
theorem B1364603 : Blo 908576 1364603 := bstep (se 1 (by rfl) ⟨1023452, by rfl⟩ : syracuseStep 1364603 = 2046905) B2046905
theorem B1364729 : Blo 908576 1364729 := bstep (se 2 (by rfl) ⟨511773, by rfl⟩ : syracuseStep 1364729 = 1023547) B1023547
theorem B1364831 : Blo 908576 1364831 := bstep (se 1 (by rfl) ⟨1023623, by rfl⟩ : syracuseStep 1364831 = 2047247) B2047247
theorem B1364843 : Blo 908576 1364843 := bstep (se 1 (by rfl) ⟨1023632, by rfl⟩ : syracuseStep 1364843 = 2047265) B2047265
theorem B2052971 : Blo 908576 2052971 := bstep (se 1 (by rfl) ⟨1539728, by rfl⟩ : syracuseStep 2052971 = 3079457) B3079457
theorem B2053025 : Blo 908576 2053025 := bstep (se 2 (by rfl) ⟨769884, by rfl⟩ : syracuseStep 2053025 = 1539769) B1539769
theorem B2774035 : Blo 908576 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B1365071 : Blo 908576 1365071 := bstep (se 1 (by rfl) ⟨1023803, by rfl⟩ : syracuseStep 1365071 = 2047607) B2047607
theorem B1365191 : Blo 908576 1365191 := bstep (se 1 (by rfl) ⟨1023893, by rfl⟩ : syracuseStep 1365191 = 2047787) B2047787
theorem B1365353 : Blo 908576 1365353 := bstep (se 2 (by rfl) ⟨512007, by rfl⟩ : syracuseStep 1365353 = 1024015) B1024015
theorem B1660267 : Blo 908576 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B1365431 : Blo 908576 1365431 := bstep (se 1 (by rfl) ⟨1024073, by rfl⟩ : syracuseStep 1365431 = 2048147) B2048147
theorem B5821915 : Blo 908576 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B1365467 : Blo 908576 1365467 := bstep (se 1 (by rfl) ⟨1024100, by rfl⟩ : syracuseStep 1365467 = 2048201) B2048201
theorem B1725961 : Blo 908576 1725961 := bstep (se 2 (by rfl) ⟨647235, by rfl⟩ : syracuseStep 1725961 = 1294471) B1294471
theorem B3462689 : Blo 908576 3462689 := bstep (se 2 (by rfl) ⟨1298508, by rfl⟩ : syracuseStep 3462689 = 2597017) B2597017
theorem B5264993 : Blo 908576 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B3069575 : Blo 908576 3069575 := bstep (se 1 (by rfl) ⟨2302181, by rfl⟩ : syracuseStep 3069575 = 4604363) B4604363
theorem B6641297 : Blo 908576 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B3069629 : Blo 908576 3069629 := bstep (se 3 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 3069629 = 1151111) B1151111
theorem B3462871 : Blo 908576 3462871 := bstep (se 1 (by rfl) ⟨2597153, by rfl⟩ : syracuseStep 3462871 = 5194307) B5194307
theorem B10639163 : Blo 908576 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B3069791 : Blo 908576 3069791 := bstep (se 1 (by rfl) ⟨2302343, by rfl⟩ : syracuseStep 3069791 = 4604687) B4604687
theorem B2185121 : Blo 908576 2185121 := bstep (se 2 (by rfl) ⟨819420, by rfl⟩ : syracuseStep 2185121 = 1638841) B1638841
theorem B1365935 : Blo 908576 1365935 := bstep (se 1 (by rfl) ⟨1024451, by rfl⟩ : syracuseStep 1365935 = 2048903) B2048903
theorem B3069953 : Blo 908576 3069953 := bstep (se 2 (by rfl) ⟨1151232, by rfl⟩ : syracuseStep 3069953 = 2302465) B2302465
theorem B3463175 : Blo 908576 3463175 := bstep (se 1 (by rfl) ⟨2597381, by rfl⟩ : syracuseStep 3463175 = 5194763) B5194763
theorem B1366025 : Blo 908576 1366025 := bstep (se 2 (by rfl) ⟨512259, by rfl⟩ : syracuseStep 1366025 = 1024519) B1024519
theorem B1366055 : Blo 908576 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B1366139 : Blo 908576 1366139 := bstep (se 1 (by rfl) ⟨1024604, by rfl⟩ : syracuseStep 1366139 = 2049209) B2049209
theorem B1366265 : Blo 908576 1366265 := bstep (se 2 (by rfl) ⟨512349, by rfl⟩ : syracuseStep 1366265 = 1024699) B1024699
theorem B6904115 : Blo 908576 6904115 := bstep (se 1 (by rfl) ⟨5178086, by rfl⟩ : syracuseStep 6904115 = 10356173) B10356173
theorem B1366367 : Blo 908576 1366367 := bstep (se 1 (by rfl) ⟨1024775, by rfl⟩ : syracuseStep 1366367 = 2049551) B2049551
theorem B1366379 : Blo 908576 1366379 := bstep (se 1 (by rfl) ⟨1024784, by rfl⟩ : syracuseStep 1366379 = 2049569) B2049569
theorem B1726895 : Blo 908576 1726895 := bstep (se 1 (by rfl) ⟨1295171, by rfl⟩ : syracuseStep 1726895 = 2590343) B2590343
theorem B3463661 : Blo 908576 3463661 := bstep (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) B1298873
theorem B26270243 : Blo 908576 26270243 := bstep (se 1 (by rfl) ⟨19702682, by rfl⟩ : syracuseStep 26270243 = 39405365) B39405365
theorem B1366607 : Blo 908576 1366607 := bstep (se 1 (by rfl) ⟨1024955, by rfl⟩ : syracuseStep 1366607 = 2049911) B2049911
theorem B1366727 : Blo 908576 1366727 := bstep (se 1 (by rfl) ⟨1025045, by rfl⟩ : syracuseStep 1366727 = 2050091) B2050091
theorem B3070763 : Blo 908576 3070763 := bstep (se 1 (by rfl) ⟨2303072, by rfl⟩ : syracuseStep 3070763 = 4606145) B4606145
theorem B1366889 : Blo 908576 1366889 := bstep (se 2 (by rfl) ⟨512583, by rfl⟩ : syracuseStep 1366889 = 1025167) B1025167
theorem B1366967 : Blo 908576 1366967 := bstep (se 1 (by rfl) ⟨1025225, by rfl⟩ : syracuseStep 1366967 = 2050451) B2050451
theorem B1727419 : Blo 908576 1727419 := bstep (se 1 (by rfl) ⟨1295564, by rfl⟩ : syracuseStep 1727419 = 2591129) B2591129
theorem B1367003 : Blo 908576 1367003 := bstep (se 1 (by rfl) ⟨1025252, by rfl⟩ : syracuseStep 1367003 = 2050505) B2050505
theorem B3071033 : Blo 908576 3071033 := bstep (se 2 (by rfl) ⟨1151637, by rfl⟩ : syracuseStep 3071033 = 2303275) B2303275
theorem B7396555 : Blo 908576 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B908583 : Blo 908576 908583 := bstep (se 1 (by rfl) ⟨681437, by rfl⟩ : syracuseStep 908583 = 1362875) B1362875
theorem B908623 : Blo 908576 908623 := bstep (se 1 (by rfl) ⟨681467, by rfl⟩ : syracuseStep 908623 = 1362935) B1362935
theorem B908639 : Blo 908576 908639 := bstep (se 1 (by rfl) ⟨681479, by rfl⟩ : syracuseStep 908639 = 1362959) B1362959
theorem B2809193 : Blo 908576 2809193 := bstep (se 2 (by rfl) ⟨1053447, by rfl⟩ : syracuseStep 2809193 = 2106895) B2106895
theorem B908667 : Blo 908576 908667 := bstep (se 1 (by rfl) ⟨681500, by rfl⟩ : syracuseStep 908667 = 1363001) B1363001
theorem B3071357 : Blo 908576 3071357 := bstep (se 3 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 3071357 = 1151759) B1151759
theorem B1727905 : Blo 908576 1727905 := bstep (se 2 (by rfl) ⟨647964, by rfl⟩ : syracuseStep 1727905 = 1295929) B1295929
theorem B908719 : Blo 908576 908719 := bstep (se 1 (by rfl) ⟨681539, by rfl⟩ : syracuseStep 908719 = 1363079) B1363079
theorem B1367471 : Blo 908576 1367471 := bstep (se 1 (by rfl) ⟨1025603, by rfl⟩ : syracuseStep 1367471 = 2051207) B2051207
theorem B908743 : Blo 908576 908743 := bstep (se 1 (by rfl) ⟨681557, by rfl⟩ : syracuseStep 908743 = 1363115) B1363115
theorem B908763 : Blo 908576 908763 := bstep (se 1 (by rfl) ⟨681572, by rfl⟩ : syracuseStep 908763 = 1363145) B1363145
theorem B1039835 : Blo 908576 1039835 := bstep (se 1 (by rfl) ⟨779876, by rfl⟩ : syracuseStep 1039835 = 1559753) B1559753
theorem B1367561 : Blo 908576 1367561 := bstep (se 2 (by rfl) ⟨512835, by rfl⟩ : syracuseStep 1367561 = 1025671) B1025671
theorem B1367591 : Blo 908576 1367591 := bstep (se 1 (by rfl) ⟨1025693, by rfl⟩ : syracuseStep 1367591 = 2051387) B2051387
theorem B908839 : Blo 908576 908839 := bstep (se 1 (by rfl) ⟨681629, by rfl⟩ : syracuseStep 908839 = 1363259) B1363259
theorem B3694139 : Blo 908576 3694139 := bstep (se 1 (by rfl) ⟨2770604, by rfl⟩ : syracuseStep 3694139 = 5541209) B5541209
theorem B908879 : Blo 908576 908879 := bstep (se 1 (by rfl) ⟨681659, by rfl⟩ : syracuseStep 908879 = 1363319) B1363319
theorem B908895 : Blo 908576 908895 := bstep (se 1 (by rfl) ⟨681671, by rfl⟩ : syracuseStep 908895 = 1363343) B1363343
theorem B3464801 : Blo 908576 3464801 := bstep (se 2 (by rfl) ⟨1299300, by rfl⟩ : syracuseStep 3464801 = 2598601) B2598601
theorem B908923 : Blo 908576 908923 := bstep (se 1 (by rfl) ⟨681692, by rfl⟩ : syracuseStep 908923 = 1363385) B1363385
theorem B1367675 : Blo 908576 1367675 := bstep (se 1 (by rfl) ⟨1025756, by rfl⟩ : syracuseStep 1367675 = 2051513) B2051513
theorem B3071627 : Blo 908576 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B908975 : Blo 908576 908975 := bstep (se 1 (by rfl) ⟨681731, by rfl⟩ : syracuseStep 908975 = 1363463) B1363463
theorem B908999 : Blo 908576 908999 := bstep (se 1 (by rfl) ⟨681749, by rfl⟩ : syracuseStep 908999 = 1363499) B1363499
theorem B909019 : Blo 908576 909019 := bstep (se 1 (by rfl) ⟨681764, by rfl⟩ : syracuseStep 909019 = 1363529) B1363529
theorem B1367801 : Blo 908576 1367801 := bstep (se 2 (by rfl) ⟨512925, by rfl⟩ : syracuseStep 1367801 = 1025851) B1025851
theorem B909095 : Blo 908576 909095 := bstep (se 1 (by rfl) ⟨681821, by rfl⟩ : syracuseStep 909095 = 1363643) B1363643
theorem B909135 : Blo 908576 909135 := bstep (se 1 (by rfl) ⟨681851, by rfl⟩ : syracuseStep 909135 = 1363703) B1363703
theorem B909151 : Blo 908576 909151 := bstep (se 1 (by rfl) ⟨681863, by rfl⟩ : syracuseStep 909151 = 1363727) B1363727
theorem B1367903 : Blo 908576 1367903 := bstep (se 1 (by rfl) ⟨1025927, by rfl⟩ : syracuseStep 1367903 = 2051855) B2051855
theorem B1367915 : Blo 908576 1367915 := bstep (se 1 (by rfl) ⟨1025936, by rfl⟩ : syracuseStep 1367915 = 2051873) B2051873
theorem B909179 : Blo 908576 909179 := bstep (se 1 (by rfl) ⟨681884, by rfl⟩ : syracuseStep 909179 = 1363769) B1363769
theorem B909231 : Blo 908576 909231 := bstep (se 1 (by rfl) ⟨681923, by rfl⟩ : syracuseStep 909231 = 1363847) B1363847
theorem B909255 : Blo 908576 909255 := bstep (se 1 (by rfl) ⟨681941, by rfl⟩ : syracuseStep 909255 = 1363883) B1363883
theorem B909275 : Blo 908576 909275 := bstep (se 1 (by rfl) ⟨681956, by rfl⟩ : syracuseStep 909275 = 1363913) B1363913
theorem B2252819 : Blo 908576 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B909351 : Blo 908576 909351 := bstep (se 1 (by rfl) ⟨682013, by rfl⟩ : syracuseStep 909351 = 1364027) B1364027
theorem B909391 : Blo 908576 909391 := bstep (se 1 (by rfl) ⟨682043, by rfl⟩ : syracuseStep 909391 = 1364087) B1364087
theorem B1368143 : Blo 908576 1368143 := bstep (se 1 (by rfl) ⟨1026107, by rfl⟩ : syracuseStep 1368143 = 2052215) B2052215
theorem B909407 : Blo 908576 909407 := bstep (se 1 (by rfl) ⟨682055, by rfl⟩ : syracuseStep 909407 = 1364111) B1364111
theorem B909435 : Blo 908576 909435 := bstep (se 1 (by rfl) ⟨682076, by rfl⟩ : syracuseStep 909435 = 1364153) B1364153
theorem B909487 : Blo 908576 909487 := bstep (se 1 (by rfl) ⟨682115, by rfl⟩ : syracuseStep 909487 = 1364231) B1364231
theorem B909511 : Blo 908576 909511 := bstep (se 1 (by rfl) ⟨682133, by rfl⟩ : syracuseStep 909511 = 1364267) B1364267
theorem B1368263 : Blo 908576 1368263 := bstep (se 1 (by rfl) ⟨1026197, by rfl⟩ : syracuseStep 1368263 = 2052395) B2052395
theorem B909531 : Blo 908576 909531 := bstep (se 1 (by rfl) ⟨682148, by rfl⟩ : syracuseStep 909531 = 1364297) B1364297
theorem B909607 : Blo 908576 909607 := bstep (se 1 (by rfl) ⟨682205, by rfl⟩ : syracuseStep 909607 = 1364411) B1364411
theorem B909647 : Blo 908576 909647 := bstep (se 1 (by rfl) ⟨682235, by rfl⟩ : syracuseStep 909647 = 1364471) B1364471
theorem B909663 : Blo 908576 909663 := bstep (se 1 (by rfl) ⟨682247, by rfl⟩ : syracuseStep 909663 = 1364495) B1364495
theorem B1368425 : Blo 908576 1368425 := bstep (se 2 (by rfl) ⟨513159, by rfl⟩ : syracuseStep 1368425 = 1026319) B1026319
theorem B909691 : Blo 908576 909691 := bstep (se 1 (by rfl) ⟨682268, by rfl⟩ : syracuseStep 909691 = 1364537) B1364537
theorem B909743 : Blo 908576 909743 := bstep (se 1 (by rfl) ⟨682307, by rfl⟩ : syracuseStep 909743 = 1364615) B1364615
theorem B1368503 : Blo 908576 1368503 := bstep (se 1 (by rfl) ⟨1026377, by rfl⟩ : syracuseStep 1368503 = 2052755) B2052755
theorem B909767 : Blo 908576 909767 := bstep (se 1 (by rfl) ⟨682325, by rfl⟩ : syracuseStep 909767 = 1364651) B1364651
theorem B909787 : Blo 908576 909787 := bstep (se 1 (by rfl) ⟨682340, by rfl⟩ : syracuseStep 909787 = 1364681) B1364681
theorem B1368539 : Blo 908576 1368539 := bstep (se 1 (by rfl) ⟨1026404, by rfl⟩ : syracuseStep 1368539 = 2052809) B2052809
theorem B3072545 : Blo 908576 3072545 := bstep (se 2 (by rfl) ⟨1152204, by rfl⟩ : syracuseStep 3072545 = 2304409) B2304409
theorem B909863 : Blo 908576 909863 := bstep (se 1 (by rfl) ⟨682397, by rfl⟩ : syracuseStep 909863 = 1364795) B1364795
theorem B909903 : Blo 908576 909903 := bstep (se 1 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 909903 = 1364855) B1364855
theorem B909919 : Blo 908576 909919 := bstep (se 1 (by rfl) ⟨682439, by rfl⟩ : syracuseStep 909919 = 1364879) B1364879
theorem B909947 : Blo 908576 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B909999 : Blo 908576 909999 := bstep (se 1 (by rfl) ⟨682499, by rfl⟩ : syracuseStep 909999 = 1364999) B1364999
theorem B910023 : Blo 908576 910023 := bstep (se 1 (by rfl) ⟨682517, by rfl⟩ : syracuseStep 910023 = 1365035) B1365035
theorem B910043 : Blo 908576 910043 := bstep (se 1 (by rfl) ⟨682532, by rfl⟩ : syracuseStep 910043 = 1365065) B1365065
theorem B3367673 : Blo 908576 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B3072761 : Blo 908576 3072761 := bstep (se 2 (by rfl) ⟨1152285, by rfl⟩ : syracuseStep 3072761 = 2304571) B2304571
theorem B910119 : Blo 908576 910119 := bstep (se 1 (by rfl) ⟨682589, by rfl⟩ : syracuseStep 910119 = 1365179) B1365179
theorem B910159 : Blo 908576 910159 := bstep (se 1 (by rfl) ⟨682619, by rfl⟩ : syracuseStep 910159 = 1365239) B1365239
theorem B910175 : Blo 908576 910175 := bstep (se 1 (by rfl) ⟨682631, by rfl⟩ : syracuseStep 910175 = 1365263) B1365263
theorem B2188139 : Blo 908576 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B910203 : Blo 908576 910203 := bstep (se 1 (by rfl) ⟨682652, by rfl⟩ : syracuseStep 910203 = 1365305) B1365305
theorem B910255 : Blo 908576 910255 := bstep (se 1 (by rfl) ⟨682691, by rfl⟩ : syracuseStep 910255 = 1365383) B1365383
theorem B910279 : Blo 908576 910279 := bstep (se 1 (by rfl) ⟨682709, by rfl⟩ : syracuseStep 910279 = 1365419) B1365419
theorem B910299 : Blo 908576 910299 := bstep (se 1 (by rfl) ⟨682724, by rfl⟩ : syracuseStep 910299 = 1365449) B1365449
theorem B3073031 : Blo 908576 3073031 := bstep (se 1 (by rfl) ⟨2304773, by rfl⟩ : syracuseStep 3073031 = 4609547) B4609547
theorem B910375 : Blo 908576 910375 := bstep (se 1 (by rfl) ⟨682781, by rfl⟩ : syracuseStep 910375 = 1365563) B1365563
theorem B13132867 : Blo 908576 13132867 := bstep (se 1 (by rfl) ⟨9849650, by rfl⟩ : syracuseStep 13132867 = 19699301) B19699301
theorem B910415 : Blo 908576 910415 := bstep (se 1 (by rfl) ⟨682811, by rfl⟩ : syracuseStep 910415 = 1365623) B1365623
theorem B910431 : Blo 908576 910431 := bstep (se 1 (by rfl) ⟨682823, by rfl⟩ : syracuseStep 910431 = 1365647) B1365647
theorem B3073139 : Blo 908576 3073139 := bstep (se 1 (by rfl) ⟨2304854, by rfl⟩ : syracuseStep 3073139 = 4609709) B4609709
theorem B910459 : Blo 908576 910459 := bstep (se 1 (by rfl) ⟨682844, by rfl⟩ : syracuseStep 910459 = 1365689) B1365689
theorem B4613273 : Blo 908576 4613273 := bstep (se 2 (by rfl) ⟨1729977, by rfl⟩ : syracuseStep 4613273 = 3459955) B3459955
theorem B910511 : Blo 908576 910511 := bstep (se 1 (by rfl) ⟨682883, by rfl⟩ : syracuseStep 910511 = 1365767) B1365767
theorem B910535 : Blo 908576 910535 := bstep (se 1 (by rfl) ⟨682901, by rfl⟩ : syracuseStep 910535 = 1365803) B1365803
theorem B910555 : Blo 908576 910555 := bstep (se 1 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 910555 = 1365833) B1365833
theorem B910631 : Blo 908576 910631 := bstep (se 1 (by rfl) ⟨682973, by rfl⟩ : syracuseStep 910631 = 1365947) B1365947
theorem B910671 : Blo 908576 910671 := bstep (se 1 (by rfl) ⟨683003, by rfl⟩ : syracuseStep 910671 = 1366007) B1366007
theorem B910687 : Blo 908576 910687 := bstep (se 1 (by rfl) ⟨683015, by rfl⟩ : syracuseStep 910687 = 1366031) B1366031
theorem B1533289 : Blo 908576 1533289 := bstep (se 2 (by rfl) ⟨574983, by rfl⟩ : syracuseStep 1533289 = 1149967) B1149967
theorem B910715 : Blo 908576 910715 := bstep (se 1 (by rfl) ⟨683036, by rfl⟩ : syracuseStep 910715 = 1366073) B1366073
theorem B3073409 : Blo 908576 3073409 := bstep (se 2 (by rfl) ⟨1152528, by rfl⟩ : syracuseStep 3073409 = 2305057) B2305057
theorem B11986321 : Blo 908576 11986321 := bstep (se 2 (by rfl) ⟨4494870, by rfl⟩ : syracuseStep 11986321 = 8989741) B8989741
theorem B910767 : Blo 908576 910767 := bstep (se 1 (by rfl) ⟨683075, by rfl⟩ : syracuseStep 910767 = 1366151) B1366151
theorem B910791 : Blo 908576 910791 := bstep (se 1 (by rfl) ⟨683093, by rfl⟩ : syracuseStep 910791 = 1366187) B1366187
theorem B18703817 : Blo 908576 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B910811 : Blo 908576 910811 := bstep (se 1 (by rfl) ⟨683108, by rfl⟩ : syracuseStep 910811 = 1366217) B1366217
theorem B9364997 : Blo 908576 9364997 := bstep (se 4 (by rfl) ⟨877968, by rfl⟩ : syracuseStep 9364997 = 1755937) B1755937
theorem B910887 : Blo 908576 910887 := bstep (se 1 (by rfl) ⟨683165, by rfl⟩ : syracuseStep 910887 = 1366331) B1366331
theorem B910927 : Blo 908576 910927 := bstep (se 1 (by rfl) ⟨683195, by rfl⟩ : syracuseStep 910927 = 1366391) B1366391
theorem B910943 : Blo 908576 910943 := bstep (se 1 (by rfl) ⟨683207, by rfl⟩ : syracuseStep 910943 = 1366415) B1366415
theorem B910971 : Blo 908576 910971 := bstep (se 1 (by rfl) ⟨683228, by rfl⟩ : syracuseStep 910971 = 1366457) B1366457
theorem B911023 : Blo 908576 911023 := bstep (se 1 (by rfl) ⟨683267, by rfl⟩ : syracuseStep 911023 = 1366535) B1366535
theorem B911047 : Blo 908576 911047 := bstep (se 1 (by rfl) ⟨683285, by rfl⟩ : syracuseStep 911047 = 1366571) B1366571
theorem B911067 : Blo 908576 911067 := bstep (se 1 (by rfl) ⟨683300, by rfl⟩ : syracuseStep 911067 = 1366601) B1366601
theorem B1730297 : Blo 908576 1730297 := bstep (se 2 (by rfl) ⟨648861, by rfl⟩ : syracuseStep 1730297 = 1297723) B1297723
theorem B911143 : Blo 908576 911143 := bstep (se 1 (by rfl) ⟨683357, by rfl⟩ : syracuseStep 911143 = 1366715) B1366715
theorem B911183 : Blo 908576 911183 := bstep (se 1 (by rfl) ⟨683387, by rfl⟩ : syracuseStep 911183 = 1366775) B1366775
theorem B911199 : Blo 908576 911199 := bstep (se 1 (by rfl) ⟨683399, by rfl⟩ : syracuseStep 911199 = 1366799) B1366799
theorem B911227 : Blo 908576 911227 := bstep (se 1 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 911227 = 1366841) B1366841
theorem B911279 : Blo 908576 911279 := bstep (se 1 (by rfl) ⟨683459, by rfl⟩ : syracuseStep 911279 = 1366919) B1366919
theorem B1730479 : Blo 908576 1730479 := bstep (se 1 (by rfl) ⟨1297859, by rfl⟩ : syracuseStep 1730479 = 2595719) B2595719
theorem B1533883 : Blo 908576 1533883 := bstep (se 1 (by rfl) ⟨1150412, by rfl⟩ : syracuseStep 1533883 = 2300825) B2300825
theorem B8873921 : Blo 908576 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B911303 : Blo 908576 911303 := bstep (se 1 (by rfl) ⟨683477, by rfl⟩ : syracuseStep 911303 = 1366955) B1366955
theorem B911323 : Blo 908576 911323 := bstep (se 1 (by rfl) ⟨683492, by rfl⟩ : syracuseStep 911323 = 1366985) B1366985
theorem B3893255 : Blo 908576 3893255 := bstep (se 1 (by rfl) ⟨2919941, by rfl⟩ : syracuseStep 3893255 = 5839883) B5839883
theorem B1533991 : Blo 908576 1533991 := bstep (se 1 (by rfl) ⟨1150493, by rfl⟩ : syracuseStep 1533991 = 2300987) B2300987
theorem B911399 : Blo 908576 911399 := bstep (se 1 (by rfl) ⟨683549, by rfl⟩ : syracuseStep 911399 = 1367099) B1367099
theorem B3893305 : Blo 908576 3893305 := bstep (se 2 (by rfl) ⟨1459989, by rfl⟩ : syracuseStep 3893305 = 2919979) B2919979
theorem B911439 : Blo 908576 911439 := bstep (se 1 (by rfl) ⟨683579, by rfl⟩ : syracuseStep 911439 = 1367159) B1367159
theorem B1730639 : Blo 908576 1730639 := bstep (se 1 (by rfl) ⟨1297979, by rfl⟩ : syracuseStep 1730639 = 2595959) B2595959
theorem B911455 : Blo 908576 911455 := bstep (se 1 (by rfl) ⟨683591, by rfl⟩ : syracuseStep 911455 = 1367183) B1367183
theorem B911483 : Blo 908576 911483 := bstep (se 1 (by rfl) ⟨683612, by rfl⟩ : syracuseStep 911483 = 1367225) B1367225
theorem B3074219 : Blo 908576 3074219 := bstep (se 1 (by rfl) ⟨2305664, by rfl⟩ : syracuseStep 3074219 = 4611329) B4611329
theorem B126412973 : Blo 908576 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B911535 : Blo 908576 911535 := bstep (se 1 (by rfl) ⟨683651, by rfl⟩ : syracuseStep 911535 = 1367303) B1367303
theorem B911559 : Blo 908576 911559 := bstep (se 1 (by rfl) ⟨683669, by rfl⟩ : syracuseStep 911559 = 1367339) B1367339
theorem B911579 : Blo 908576 911579 := bstep (se 1 (by rfl) ⟨683684, by rfl⟩ : syracuseStep 911579 = 1367369) B1367369
theorem B911655 : Blo 908576 911655 := bstep (se 1 (by rfl) ⟨683741, by rfl⟩ : syracuseStep 911655 = 1367483) B1367483
theorem B911695 : Blo 908576 911695 := bstep (se 1 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 911695 = 1367543) B1367543
theorem B911711 : Blo 908576 911711 := bstep (se 1 (by rfl) ⟨683783, by rfl⟩ : syracuseStep 911711 = 1367567) B1367567
theorem B1534315 : Blo 908576 1534315 := bstep (se 1 (by rfl) ⟨1150736, by rfl⟩ : syracuseStep 1534315 = 2301473) B2301473
theorem B911739 : Blo 908576 911739 := bstep (se 1 (by rfl) ⟨683804, by rfl⟩ : syracuseStep 911739 = 1367609) B1367609
theorem B911791 : Blo 908576 911791 := bstep (se 1 (by rfl) ⟨683843, by rfl⟩ : syracuseStep 911791 = 1367687) B1367687
theorem B13101497 : Blo 908576 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B911815 : Blo 908576 911815 := bstep (se 1 (by rfl) ⟨683861, by rfl⟩ : syracuseStep 911815 = 1367723) B1367723
theorem B911835 : Blo 908576 911835 := bstep (se 1 (by rfl) ⟨683876, by rfl⟩ : syracuseStep 911835 = 1367753) B1367753
theorem B911911 : Blo 908576 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B2910779 : Blo 908576 2910779 := bstep (se 1 (by rfl) ⟨2183084, by rfl⟩ : syracuseStep 2910779 = 4366169) B4366169
theorem B911951 : Blo 908576 911951 := bstep (se 1 (by rfl) ⟨683963, by rfl⟩ : syracuseStep 911951 = 1367927) B1367927
theorem B911967 : Blo 908576 911967 := bstep (se 1 (by rfl) ⟨683975, by rfl⟩ : syracuseStep 911967 = 1367951) B1367951
theorem B911995 : Blo 908576 911995 := bstep (se 1 (by rfl) ⟨683996, by rfl⟩ : syracuseStep 911995 = 1367993) B1367993
theorem B912047 : Blo 908576 912047 := bstep (se 1 (by rfl) ⟨684035, by rfl⟩ : syracuseStep 912047 = 1368071) B1368071
theorem B3074759 : Blo 908576 3074759 := bstep (se 1 (by rfl) ⟨2306069, by rfl⟩ : syracuseStep 3074759 = 4612139) B4612139
theorem B912071 : Blo 908576 912071 := bstep (se 1 (by rfl) ⟨684053, by rfl⟩ : syracuseStep 912071 = 1368107) B1368107
theorem B912091 : Blo 908576 912091 := bstep (se 1 (by rfl) ⟨684068, by rfl⟩ : syracuseStep 912091 = 1368137) B1368137
theorem B912167 : Blo 908576 912167 := bstep (se 1 (by rfl) ⟨684125, by rfl⟩ : syracuseStep 912167 = 1368251) B1368251
theorem B912207 : Blo 908576 912207 := bstep (se 1 (by rfl) ⟨684155, by rfl⟩ : syracuseStep 912207 = 1368311) B1368311
theorem B912223 : Blo 908576 912223 := bstep (se 1 (by rfl) ⟨684167, by rfl⟩ : syracuseStep 912223 = 1368335) B1368335
theorem B912251 : Blo 908576 912251 := bstep (se 1 (by rfl) ⟨684188, by rfl⟩ : syracuseStep 912251 = 1368377) B1368377
theorem B912303 : Blo 908576 912303 := bstep (se 1 (by rfl) ⟨684227, by rfl⟩ : syracuseStep 912303 = 1368455) B1368455
theorem B912327 : Blo 908576 912327 := bstep (se 1 (by rfl) ⟨684245, by rfl⟩ : syracuseStep 912327 = 1368491) B1368491
theorem B912347 : Blo 908576 912347 := bstep (se 1 (by rfl) ⟨684260, by rfl⟩ : syracuseStep 912347 = 1368521) B1368521
theorem B912423 : Blo 908576 912423 := bstep (se 1 (by rfl) ⟨684317, by rfl⟩ : syracuseStep 912423 = 1368635) B1368635
theorem B912463 : Blo 908576 912463 := bstep (se 1 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 912463 = 1368695) B1368695
theorem B912479 : Blo 908576 912479 := bstep (se 1 (by rfl) ⟨684359, by rfl⟩ : syracuseStep 912479 = 1368719) B1368719
theorem B912507 : Blo 908576 912507 := bstep (se 1 (by rfl) ⟨684380, by rfl⟩ : syracuseStep 912507 = 1368761) B1368761
theorem B1731755 : Blo 908576 1731755 := bstep (se 1 (by rfl) ⟨1298816, by rfl⟩ : syracuseStep 1731755 = 2597633) B2597633
theorem B912559 : Blo 908576 912559 := bstep (se 1 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 912559 = 1368839) B1368839
theorem B5827787 : Blo 908576 5827787 := bstep (se 1 (by rfl) ⟨4370840, by rfl⟩ : syracuseStep 5827787 = 8741681) B8741681
theorem B1535375 : Blo 908576 1535375 := bstep (se 1 (by rfl) ⟨1151531, by rfl⟩ : syracuseStep 1535375 = 2303063) B2303063
theorem B3075623 : Blo 908576 3075623 := bstep (se 1 (by rfl) ⟨2306717, by rfl⟩ : syracuseStep 3075623 = 4613435) B4613435
theorem B9858647 : Blo 908576 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B5828219 : Blo 908576 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B1535611 : Blo 908576 1535611 := bstep (se 1 (by rfl) ⟨1151708, by rfl⟩ : syracuseStep 1535611 = 2303417) B2303417
theorem B3075731 : Blo 908576 3075731 := bstep (se 1 (by rfl) ⟨2306798, by rfl⟩ : syracuseStep 3075731 = 4613597) B4613597
theorem B27979453 : Blo 908576 27979453 := bstep (se 3 (by rfl) ⟨5246147, by rfl⟩ : syracuseStep 27979453 = 10492295) B10492295
theorem B3075947 : Blo 908576 3075947 := bstep (se 1 (by rfl) ⟨2306960, by rfl⟩ : syracuseStep 3075947 = 4613921) B4613921
theorem B3698551 : Blo 908576 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B3076001 : Blo 908576 3076001 := bstep (se 2 (by rfl) ⟨1153500, by rfl⟩ : syracuseStep 3076001 = 2307001) B2307001
theorem B1536475 : Blo 908576 1536475 := bstep (se 1 (by rfl) ⟨1152356, by rfl⟩ : syracuseStep 1536475 = 2304713) B2304713
theorem B3076595 : Blo 908576 3076595 := bstep (se 1 (by rfl) ⟨2307446, by rfl⟩ : syracuseStep 3076595 = 4614893) B4614893
theorem B2912777 : Blo 908576 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B113865259 : Blo 908576 113865259 := bstep (se 1 (by rfl) ⟨85398944, by rfl⟩ : syracuseStep 113865259 = 170797889) B170797889
theorem B3895867 : Blo 908576 3895867 := bstep (se 1 (by rfl) ⟨2921900, by rfl⟩ : syracuseStep 3895867 = 5843801) B5843801
theorem B3077135 : Blo 908576 3077135 := bstep (se 1 (by rfl) ⟨2307851, by rfl⟩ : syracuseStep 3077135 = 4615703) B4615703
theorem B1537103 : Blo 908576 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B6911405 : Blo 908576 6911405 := bstep (se 3 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 6911405 = 2591777) B2591777
theorem B3077729 : Blo 908576 3077729 := bstep (se 2 (by rfl) ⟨1154148, by rfl⟩ : syracuseStep 3077729 = 2308297) B2308297
theorem B35452673 : Blo 908576 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B1537967 : Blo 908576 1537967 := bstep (se 1 (by rfl) ⟨1153475, by rfl⟩ : syracuseStep 1537967 = 2306951) B2306951
theorem B5175353 : Blo 908576 5175353 := bstep (se 2 (by rfl) ⟨1940757, by rfl⟩ : syracuseStep 5175353 = 3881515) B3881515
theorem B1538399 : Blo 908576 1538399 := bstep (se 1 (by rfl) ⟨1153799, by rfl⟩ : syracuseStep 1538399 = 2307599) B2307599
theorem B15989123 : Blo 908576 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B8321413 : Blo 908576 8321413 := bstep (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) B1560265
theorem B3275549 : Blo 908576 3275549 := bstep (se 3 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 3275549 = 1228331) B1228331
theorem B1538959 : Blo 908576 1538959 := bstep (se 1 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 1538959 = 2308439) B2308439
theorem B3079187 : Blo 908576 3079187 := bstep (se 1 (by rfl) ⟨2309390, by rfl⟩ : syracuseStep 3079187 = 4618781) B4618781
theorem B3079511 : Blo 908576 3079511 := bstep (se 1 (by rfl) ⟨2309633, by rfl⟩ : syracuseStep 3079511 = 4619267) B4619267
theorem B1539641 : Blo 908576 1539641 := bstep (se 2 (by rfl) ⟨577365, by rfl⟩ : syracuseStep 1539641 = 1154731) B1154731
theorem B4619915 : Blo 908576 4619915 := bstep (se 1 (by rfl) ⟨3464936, by rfl⟩ : syracuseStep 4619915 = 6929873) B6929873
theorem B29556485 : Blo 908576 29556485 := bstep (se 4 (by rfl) ⟨2770920, by rfl⟩ : syracuseStep 29556485 = 5541841) B5541841
theorem B6913835 : Blo 908576 6913835 := bstep (se 1 (by rfl) ⟨5185376, by rfl⟩ : syracuseStep 6913835 = 10370753) B10370753
theorem B37945421 : Blo 908576 37945421 := bstep (se 3 (by rfl) ⟨7114766, by rfl⟩ : syracuseStep 37945421 = 14229533) B14229533
theorem B34996373 : Blo 908576 34996373 := bstep (se 6 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 34996373 = 1640455) B1640455
theorem B8749403 : Blo 908576 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B2589671 : Blo 908576 2589671 := bstep (se 1 (by rfl) ⟨1942253, by rfl⟩ : syracuseStep 2589671 = 3884507) B3884507
theorem B33227981 : Blo 908576 33227981 := bstep (se 3 (by rfl) ⟨6230246, by rfl⟩ : syracuseStep 33227981 = 12460493) B12460493
theorem B7997251 : Blo 908576 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B2492441 : Blo 908576 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B7375043 : Blo 908576 7375043 := bstep (se 1 (by rfl) ⟨5531282, by rfl⟩ : syracuseStep 7375043 = 11062565) B11062565
theorem B5835037 : Blo 908576 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B9341351 : Blo 908576 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B2591311 : Blo 908576 2591311 := bstep (se 1 (by rfl) ⟨1943483, by rfl⟩ : syracuseStep 2591311 = 3886967) B3886967
theorem B8751827 : Blo 908576 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B5180183 : Blo 908576 5180183 := bstep (se 1 (by rfl) ⟨3885137, by rfl⟩ : syracuseStep 5180183 = 7770275) B7770275
theorem B17763907 : Blo 908576 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B3509995 : Blo 908576 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B4427531 : Blo 908576 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B1642295 : Blo 908576 1642295 := bstep (se 1 (by rfl) ⟨1231721, by rfl⟩ : syracuseStep 1642295 = 2463443) B2463443
theorem B1151263 : Blo 908576 1151263 := bstep (se 1 (by rfl) ⟨863447, by rfl⟩ : syracuseStep 1151263 = 1726895) B1726895
theorem B2462759 : Blo 908576 2462759 := bstep (se 1 (by rfl) ⟨1847069, by rfl⟩ : syracuseStep 2462759 = 3694139) B3694139
theorem B7017529 : Blo 908576 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B23663789 : Blo 908576 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B5182825 : Blo 908576 5182825 := bstep (se 2 (by rfl) ⟨1943559, by rfl⟩ : syracuseStep 5182825 = 3887119) B3887119
theorem B151820345 : Blo 908576 151820345 := bstep (se 2 (by rfl) ⟨56932629, by rfl⟩ : syracuseStep 151820345 = 113865259) B113865259
theorem B42637661 : Blo 908576 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B1153531 : Blo 908576 1153531 := bstep (se 1 (by rfl) ⟨865148, by rfl⟩ : syracuseStep 1153531 = 1730297) B1730297
theorem B2595503 : Blo 908576 2595503 := bstep (se 1 (by rfl) ⟨1946627, by rfl⟩ : syracuseStep 2595503 = 3893255) B3893255
theorem B1153759 : Blo 908576 1153759 := bstep (se 1 (by rfl) ⟨865319, by rfl⟩ : syracuseStep 1153759 = 1730639) B1730639
theorem B2300663 : Blo 908576 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B1940519 : Blo 908576 1940519 := bstep (se 1 (by rfl) ⟨1455389, by rfl⟩ : syracuseStep 1940519 = 2910779) B2910779
theorem B4791619 : Blo 908576 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B2301281 : Blo 908576 2301281 := bstep (se 2 (by rfl) ⟨862980, by rfl⟩ : syracuseStep 2301281 = 1725961) B1725961
theorem B1154503 : Blo 908576 1154503 := bstep (se 1 (by rfl) ⟨865877, by rfl⟩ : syracuseStep 1154503 = 1731755) B1731755
theorem B5905979 : Blo 908576 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B1023583 : Blo 908576 1023583 := bstep (se 1 (by rfl) ⟨767687, by rfl⟩ : syracuseStep 1023583 = 1535375) B1535375
theorem B4923143 : Blo 908576 4923143 := bstep (se 1 (by rfl) ⟨3692357, by rfl⟩ : syracuseStep 4923143 = 7384715) B7384715
theorem B4923443 : Blo 908576 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B1941851 : Blo 908576 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B12460715 : Blo 908576 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B1024735 : Blo 908576 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B2302739 : Blo 908576 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B2302951 : Blo 908576 2302951 := bstep (se 1 (by rfl) ⟨1727213, by rfl⟩ : syracuseStep 2302951 = 3454427) B3454427
theorem B4432985 : Blo 908576 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B23635115 : Blo 908576 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B2303225 : Blo 908576 2303225 := bstep (se 2 (by rfl) ⟨863709, by rfl⟩ : syracuseStep 2303225 = 1727419) B1727419
theorem B1025311 : Blo 908576 1025311 := bstep (se 1 (by rfl) ⟨768983, by rfl⟩ : syracuseStep 1025311 = 1537967) B1537967
theorem B3450221 : Blo 908576 3450221 := bstep (se 3 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 3450221 = 1293833) B1293833
theorem B3450235 : Blo 908576 3450235 := bstep (se 1 (by rfl) ⟨2587676, by rfl⟩ : syracuseStep 3450235 = 5175353) B5175353
theorem B1025599 : Blo 908576 1025599 := bstep (se 1 (by rfl) ⟨769199, by rfl⟩ : syracuseStep 1025599 = 1538399) B1538399
theorem B10233479 : Blo 908576 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B2303873 : Blo 908576 2303873 := bstep (se 2 (by rfl) ⟨863952, by rfl⟩ : syracuseStep 2303873 = 1727905) B1727905
theorem B2074889 : Blo 908576 2074889 := bstep (se 2 (by rfl) ⟨778083, by rfl⟩ : syracuseStep 2074889 = 1556167) B1556167
theorem B1026427 : Blo 908576 1026427 := bstep (se 1 (by rfl) ⟨769820, by rfl⟩ : syracuseStep 1026427 = 1539641) B1539641
theorem B19704323 : Blo 908576 19704323 := bstep (se 1 (by rfl) ⟨14778242, by rfl⟩ : syracuseStep 19704323 = 29556485) B29556485
theorem B2304683 : Blo 908576 2304683 := bstep (se 1 (by rfl) ⟨1728512, by rfl⟩ : syracuseStep 2304683 = 3457025) B3457025
theorem B9349805 : Blo 908576 9349805 := bstep (se 3 (by rfl) ⟨1753088, by rfl⟩ : syracuseStep 9349805 = 3506177) B3506177
theorem B6007517 : Blo 908576 6007517 := bstep (se 3 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 6007517 = 2252819) B2252819
theorem B5319595 : Blo 908576 5319595 := bstep (se 1 (by rfl) ⟨3989696, by rfl⟩ : syracuseStep 5319595 = 7979393) B7979393
theorem B2305543 : Blo 908576 2305543 := bstep (se 1 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 2305543 = 3458315) B3458315
theorem B3452651 : Blo 908576 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B2305847 : Blo 908576 2305847 := bstep (se 1 (by rfl) ⟨1729385, by rfl⟩ : syracuseStep 2305847 = 3458771) B3458771
theorem B8302445 : Blo 908576 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B13512653 : Blo 908576 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B4599827 : Blo 908576 4599827 := bstep (se 1 (by rfl) ⟨3449870, by rfl⟩ : syracuseStep 4599827 = 6899741) B6899741
theorem B17510489 : Blo 908576 17510489 := bstep (se 2 (by rfl) ⟨6566433, by rfl⟩ : syracuseStep 17510489 = 13132867) B13132867
theorem B3453137 : Blo 908576 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B1847719 : Blo 908576 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B2306515 : Blo 908576 2306515 := bstep (se 1 (by rfl) ⟨1729886, by rfl⟩ : syracuseStep 2306515 = 3459773) B3459773
theorem B2044385 : Blo 908576 2044385 := bstep (se 2 (by rfl) ⟨766644, by rfl⟩ : syracuseStep 2044385 = 1533289) B1533289
theorem B1946081 : Blo 908576 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B3453623 : Blo 908576 3453623 := bstep (se 1 (by rfl) ⟨2590217, by rfl⟩ : syracuseStep 3453623 = 5180435) B5180435
theorem B2044691 : Blo 908576 2044691 := bstep (se 1 (by rfl) ⟨1533518, by rfl⟩ : syracuseStep 2044691 = 3067037) B3067037
theorem B15545195 : Blo 908576 15545195 := bstep (se 1 (by rfl) ⟨11658896, by rfl⟩ : syracuseStep 15545195 = 23317793) B23317793
theorem B2045051 : Blo 908576 2045051 := bstep (se 1 (by rfl) ⟨1533788, by rfl⟩ : syracuseStep 2045051 = 3067577) B3067577
theorem B2307305 : Blo 908576 2307305 := bstep (se 2 (by rfl) ⟨865239, by rfl⟩ : syracuseStep 2307305 = 1730479) B1730479
theorem B2045177 : Blo 908576 2045177 := bstep (se 2 (by rfl) ⟨766941, by rfl⟩ : syracuseStep 2045177 = 1533883) B1533883
theorem B2045321 : Blo 908576 2045321 := bstep (se 2 (by rfl) ⟨766995, by rfl⟩ : syracuseStep 2045321 = 1533991) B1533991
theorem B2307467 : Blo 908576 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B5191073 : Blo 908576 5191073 := bstep (se 2 (by rfl) ⟨1946652, by rfl⟩ : syracuseStep 5191073 = 3893305) B3893305
theorem B3454397 : Blo 908576 3454397 := bstep (se 3 (by rfl) ⟨647699, by rfl⟩ : syracuseStep 3454397 = 1295399) B1295399
theorem B2045447 : Blo 908576 2045447 := bstep (se 1 (by rfl) ⟨1534085, by rfl⟩ : syracuseStep 2045447 = 3068171) B3068171
theorem B2340409 : Blo 908576 2340409 := bstep (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) B1755307
theorem B2045627 : Blo 908576 2045627 := bstep (se 1 (by rfl) ⟨1534220, by rfl⟩ : syracuseStep 2045627 = 3068441) B3068441
theorem B11056925 : Blo 908576 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B2045753 : Blo 908576 2045753 := bstep (se 2 (by rfl) ⟨767157, by rfl⟩ : syracuseStep 2045753 = 1534315) B1534315
theorem B2308459 : Blo 908576 2308459 := bstep (se 1 (by rfl) ⟨1731344, by rfl⟩ : syracuseStep 2308459 = 3462689) B3462689
theorem B3455399 : Blo 908576 3455399 := bstep (se 1 (by rfl) ⟨2591549, by rfl⟩ : syracuseStep 3455399 = 5183099) B5183099
theorem B2046383 : Blo 908576 2046383 := bstep (se 1 (by rfl) ⟨1534787, by rfl⟩ : syracuseStep 2046383 = 3069575) B3069575
theorem B29964725 : Blo 908576 29964725 := bstep (se 5 (by rfl) ⟨1404596, by rfl⟩ : syracuseStep 29964725 = 2809193) B2809193
theorem B2046419 : Blo 908576 2046419 := bstep (se 1 (by rfl) ⟨1534814, by rfl⟩ : syracuseStep 2046419 = 3069629) B3069629
theorem B7092775 : Blo 908576 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B2046527 : Blo 908576 2046527 := bstep (se 1 (by rfl) ⟨1534895, by rfl⟩ : syracuseStep 2046527 = 3069791) B3069791
theorem B3455567 : Blo 908576 3455567 := bstep (se 1 (by rfl) ⟨2591675, by rfl⟩ : syracuseStep 3455567 = 5183351) B5183351
theorem B1456747 : Blo 908576 1456747 := bstep (se 1 (by rfl) ⟨1092560, by rfl⟩ : syracuseStep 1456747 = 2185121) B2185121
theorem B2046635 : Blo 908576 2046635 := bstep (se 1 (by rfl) ⟨1534976, by rfl⟩ : syracuseStep 2046635 = 3069953) B3069953
theorem B2308783 : Blo 908576 2308783 := bstep (se 1 (by rfl) ⟨1731587, by rfl⟩ : syracuseStep 2308783 = 3463175) B3463175
theorem B1751735 : Blo 908576 1751735 := bstep (se 1 (by rfl) ⟨1313801, by rfl⟩ : syracuseStep 1751735 = 2627603) B2627603
theorem B2079479 : Blo 908576 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B4602743 : Blo 908576 4602743 := bstep (se 1 (by rfl) ⟨3452057, by rfl⟩ : syracuseStep 4602743 = 6904115) B6904115
theorem B2309107 : Blo 908576 2309107 := bstep (se 1 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 2309107 = 3463661) B3463661
theorem B17513495 : Blo 908576 17513495 := bstep (se 1 (by rfl) ⟨13135121, by rfl⟩ : syracuseStep 17513495 = 26270243) B26270243
theorem B2047175 : Blo 908576 2047175 := bstep (se 1 (by rfl) ⟨1535381, by rfl⟩ : syracuseStep 2047175 = 3070763) B3070763
theorem B1752283 : Blo 908576 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B2047355 : Blo 908576 2047355 := bstep (se 1 (by rfl) ⟨1535516, by rfl⟩ : syracuseStep 2047355 = 3071033) B3071033
theorem B2047481 : Blo 908576 2047481 := bstep (se 2 (by rfl) ⟨767805, by rfl⟩ : syracuseStep 2047481 = 1535611) B1535611
theorem B37305937 : Blo 908576 37305937 := bstep (se 2 (by rfl) ⟨13989726, by rfl⟩ : syracuseStep 37305937 = 27979453) B27979453
theorem B2047571 : Blo 908576 2047571 := bstep (se 1 (by rfl) ⟨1535678, by rfl⟩ : syracuseStep 2047571 = 3071357) B3071357
theorem B4603553 : Blo 908576 4603553 := bstep (se 2 (by rfl) ⟨1726332, by rfl⟩ : syracuseStep 4603553 = 3452665) B3452665
theorem B2309867 : Blo 908576 2309867 := bstep (se 1 (by rfl) ⟨1732400, by rfl⟩ : syracuseStep 2309867 = 3464801) B3464801
theorem B2047751 : Blo 908576 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B4931401 : Blo 908576 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B1228699 : Blo 908576 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B2048363 : Blo 908576 2048363 := bstep (se 1 (by rfl) ⟨1536272, by rfl⟩ : syracuseStep 2048363 = 3072545) B3072545
theorem B2245115 : Blo 908576 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B2048507 : Blo 908576 2048507 := bstep (se 1 (by rfl) ⟨1536380, by rfl⟩ : syracuseStep 2048507 = 3072761) B3072761
theorem B16630343 : Blo 908576 16630343 := bstep (se 1 (by rfl) ⟨12472757, by rfl⟩ : syracuseStep 16630343 = 24945515) B24945515
theorem B2048633 : Blo 908576 2048633 := bstep (se 2 (by rfl) ⟨768237, by rfl⟩ : syracuseStep 2048633 = 1536475) B1536475
theorem B1295023 : Blo 908576 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B2048687 : Blo 908576 2048687 := bstep (se 1 (by rfl) ⟨1536515, by rfl⟩ : syracuseStep 2048687 = 3073031) B3073031
theorem B2048759 : Blo 908576 2048759 := bstep (se 1 (by rfl) ⟨1536569, by rfl⟩ : syracuseStep 2048759 = 3073139) B3073139
theorem B5194489 : Blo 908576 5194489 := bstep (se 2 (by rfl) ⟨1947933, by rfl⟩ : syracuseStep 5194489 = 3895867) B3895867
theorem B2048939 : Blo 908576 2048939 := bstep (se 1 (by rfl) ⟨1536704, by rfl⟩ : syracuseStep 2048939 = 3073409) B3073409
theorem B12469211 : Blo 908576 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B3458011 : Blo 908576 3458011 := bstep (se 1 (by rfl) ⟨2593508, by rfl⟩ : syracuseStep 3458011 = 5187017) B5187017
theorem B6243331 : Blo 908576 6243331 := bstep (se 1 (by rfl) ⟨4682498, by rfl⟩ : syracuseStep 6243331 = 9364997) B9364997
theorem B1754399 : Blo 908576 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B11650391 : Blo 908576 11650391 := bstep (se 1 (by rfl) ⟨8737793, by rfl⟩ : syracuseStep 11650391 = 17475587) B17475587
theorem B2049479 : Blo 908576 2049479 := bstep (se 1 (by rfl) ⟨1537109, by rfl⟩ : syracuseStep 2049479 = 3074219) B3074219
theorem B4605497 : Blo 908576 4605497 := bstep (se 2 (by rfl) ⟨1727061, by rfl⟩ : syracuseStep 4605497 = 3454123) B3454123
theorem B8734331 : Blo 908576 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B2049839 : Blo 908576 2049839 := bstep (se 1 (by rfl) ⟨1537379, by rfl⟩ : syracuseStep 2049839 = 3074759) B3074759
theorem B2213689 : Blo 908576 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B3885191 : Blo 908576 3885191 := bstep (se 1 (by rfl) ⟨2913893, by rfl⟩ : syracuseStep 3885191 = 5827787) B5827787
theorem B3459257 : Blo 908576 3459257 := bstep (se 2 (by rfl) ⟨1297221, by rfl⟩ : syracuseStep 3459257 = 2594443) B2594443
theorem B1460489 : Blo 908576 1460489 := bstep (se 2 (by rfl) ⟨547683, by rfl⟩ : syracuseStep 1460489 = 1095367) B1095367
theorem B4376855 : Blo 908576 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B2050415 : Blo 908576 2050415 := bstep (se 1 (by rfl) ⟨1537811, by rfl⟩ : syracuseStep 2050415 = 3075623) B3075623
theorem B6572431 : Blo 908576 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B3885479 : Blo 908576 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B2050487 : Blo 908576 2050487 := bstep (se 1 (by rfl) ⟨1537865, by rfl⟩ : syracuseStep 2050487 = 3075731) B3075731
theorem B2050631 : Blo 908576 2050631 := bstep (se 1 (by rfl) ⟨1537973, by rfl⟩ : syracuseStep 2050631 = 3075947) B3075947
theorem B2050667 : Blo 908576 2050667 := bstep (se 1 (by rfl) ⟨1538000, by rfl⟩ : syracuseStep 2050667 = 3076001) B3076001
theorem B6998807 : Blo 908576 6998807 := bstep (se 1 (by rfl) ⟨5249105, by rfl⟩ : syracuseStep 6998807 = 10498211) B10498211
theorem B1755983 : Blo 908576 1755983 := bstep (se 1 (by rfl) ⟨1316987, by rfl⟩ : syracuseStep 1755983 = 2633975) B2633975
theorem B3066767 : Blo 908576 3066767 := bstep (se 1 (by rfl) ⟨2300075, by rfl⟩ : syracuseStep 3066767 = 4600151) B4600151
theorem B2051063 : Blo 908576 2051063 := bstep (se 1 (by rfl) ⟨1538297, by rfl⟩ : syracuseStep 2051063 = 3076595) B3076595
theorem B11095217 : Blo 908576 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B1363163 : Blo 908576 1363163 := bstep (se 1 (by rfl) ⟨1022372, by rfl⟩ : syracuseStep 1363163 = 2044745) B2044745
theorem B2051423 : Blo 908576 2051423 := bstep (se 1 (by rfl) ⟨1538567, by rfl⟩ : syracuseStep 2051423 = 3077135) B3077135
theorem B1363337 : Blo 908576 1363337 := bstep (se 2 (by rfl) ⟨511251, by rfl⟩ : syracuseStep 1363337 = 1022503) B1022503
theorem B4607603 : Blo 908576 4607603 := bstep (se 1 (by rfl) ⟨3455702, by rfl⟩ : syracuseStep 4607603 = 6911405) B6911405
theorem B1363691 : Blo 908576 1363691 := bstep (se 1 (by rfl) ⟨1022768, by rfl⟩ : syracuseStep 1363691 = 2045537) B2045537
theorem B2051819 : Blo 908576 2051819 := bstep (se 1 (by rfl) ⟨1538864, by rfl⟩ : syracuseStep 2051819 = 3077729) B3077729
theorem B2051945 : Blo 908576 2051945 := bstep (se 2 (by rfl) ⟨769479, by rfl⟩ : syracuseStep 2051945 = 1538959) B1538959
theorem B2772893 : Blo 908576 2772893 := bstep (se 3 (by rfl) ⟨519917, by rfl⟩ : syracuseStep 2772893 = 1039835) B1039835
theorem B1363919 : Blo 908576 1363919 := bstep (se 1 (by rfl) ⟨1022939, by rfl⟩ : syracuseStep 1363919 = 2045879) B2045879
theorem B3068009 : Blo 908576 3068009 := bstep (se 2 (by rfl) ⟨1150503, by rfl⟩ : syracuseStep 3068009 = 2301007) B2301007
theorem B1364315 : Blo 908576 1364315 := bstep (se 1 (by rfl) ⟨1023236, by rfl⟩ : syracuseStep 1364315 = 2046473) B2046473
theorem B2183699 : Blo 908576 2183699 := bstep (se 1 (by rfl) ⟨1637774, by rfl⟩ : syracuseStep 2183699 = 3275549) B3275549
theorem B1364543 : Blo 908576 1364543 := bstep (se 1 (by rfl) ⟨1023407, by rfl⟩ : syracuseStep 1364543 = 2046815) B2046815
theorem B1364663 : Blo 908576 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B2052791 : Blo 908576 2052791 := bstep (se 1 (by rfl) ⟨1539593, by rfl⟩ : syracuseStep 2052791 = 3079187) B3079187
theorem B2053007 : Blo 908576 2053007 := bstep (se 1 (by rfl) ⟨1539755, by rfl⟩ : syracuseStep 2053007 = 3079511) B3079511
theorem B1364891 : Blo 908576 1364891 := bstep (se 1 (by rfl) ⟨1023668, by rfl⟩ : syracuseStep 1364891 = 2047337) B2047337
theorem B3068873 : Blo 908576 3068873 := bstep (se 2 (by rfl) ⟨1150827, by rfl⟩ : syracuseStep 3068873 = 2301655) B2301655
theorem B4609223 : Blo 908576 4609223 := bstep (se 1 (by rfl) ⟨3456917, by rfl⟩ : syracuseStep 4609223 = 6913835) B6913835
theorem B3069143 : Blo 908576 3069143 := bstep (se 1 (by rfl) ⟨2301857, by rfl⟩ : syracuseStep 3069143 = 4603715) B4603715
theorem B1365287 : Blo 908576 1365287 := bstep (se 1 (by rfl) ⟨1023965, by rfl⟩ : syracuseStep 1365287 = 2047931) B2047931
theorem B4609385 : Blo 908576 4609385 := bstep (se 2 (by rfl) ⟨1728519, by rfl⟩ : syracuseStep 4609385 = 3457039) B3457039
theorem B4150651 : Blo 908576 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B1365371 : Blo 908576 1365371 := bstep (se 1 (by rfl) ⟨1024028, by rfl⟩ : syracuseStep 1365371 = 2048057) B2048057
theorem B972199 : Blo 908576 972199 := bstep (se 1 (by rfl) ⟨729149, by rfl⟩ : syracuseStep 972199 = 1458299) B1458299
theorem B1365497 : Blo 908576 1365497 := bstep (se 2 (by rfl) ⟨512061, by rfl⟩ : syracuseStep 1365497 = 1024123) B1024123
theorem B1365599 : Blo 908576 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B1365815 : Blo 908576 1365815 := bstep (se 1 (by rfl) ⟨1024361, by rfl⟩ : syracuseStep 1365815 = 2048723) B2048723
theorem B1726265 : Blo 908576 1726265 := bstep (se 2 (by rfl) ⟨647349, by rfl⟩ : syracuseStep 1726265 = 1294699) B1294699
theorem B1169383 : Blo 908576 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B1366121 : Blo 908576 1366121 := bstep (se 2 (by rfl) ⟨512295, by rfl⟩ : syracuseStep 1366121 = 1024591) B1024591
theorem B973019 : Blo 908576 973019 := bstep (se 1 (by rfl) ⟨729764, by rfl⟩ : syracuseStep 973019 = 1459529) B1459529
theorem B1366439 : Blo 908576 1366439 := bstep (se 1 (by rfl) ⟨1024829, by rfl⟩ : syracuseStep 1366439 = 2049659) B2049659
theorem B1038791 : Blo 908576 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B1366523 : Blo 908576 1366523 := bstep (se 1 (by rfl) ⟨1024892, by rfl⟩ : syracuseStep 1366523 = 2049785) B2049785
theorem B1366649 : Blo 908576 1366649 := bstep (se 2 (by rfl) ⟨512493, by rfl⟩ : syracuseStep 1366649 = 1024987) B1024987
theorem B1366703 : Blo 908576 1366703 := bstep (se 1 (by rfl) ⟨1025027, by rfl⟩ : syracuseStep 1366703 = 2050055) B2050055
theorem B6576815 : Blo 908576 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B3889853 : Blo 908576 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B1366751 : Blo 908576 1366751 := bstep (se 1 (by rfl) ⟨1025063, by rfl⟩ : syracuseStep 1366751 = 2050127) B2050127
theorem B1367015 : Blo 908576 1367015 := bstep (se 1 (by rfl) ⟨1025261, by rfl⟩ : syracuseStep 1367015 = 2050523) B2050523
theorem B3464315 : Blo 908576 3464315 := bstep (se 1 (by rfl) ⟨2598236, by rfl⟩ : syracuseStep 3464315 = 5196473) B5196473
theorem B15981761 : Blo 908576 15981761 := bstep (se 2 (by rfl) ⟨5993160, by rfl⟩ : syracuseStep 15981761 = 11986321) B11986321
theorem B3071195 : Blo 908576 3071195 := bstep (se 1 (by rfl) ⟨2303396, by rfl⟩ : syracuseStep 3071195 = 4606793) B4606793
theorem B1367273 : Blo 908576 1367273 := bstep (se 2 (by rfl) ⟨512727, by rfl⟩ : syracuseStep 1367273 = 1025455) B1025455
theorem B1367327 : Blo 908576 1367327 := bstep (se 1 (by rfl) ⟨1025495, by rfl⟩ : syracuseStep 1367327 = 2050991) B2050991
theorem B908635 : Blo 908576 908635 := bstep (se 1 (by rfl) ⟨681476, by rfl⟩ : syracuseStep 908635 = 1362953) B1362953
theorem B908655 : Blo 908576 908655 := bstep (se 1 (by rfl) ⟨681491, by rfl⟩ : syracuseStep 908655 = 1362983) B1362983
theorem B1727867 : Blo 908576 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B908711 : Blo 908576 908711 := bstep (se 1 (by rfl) ⟨681533, by rfl⟩ : syracuseStep 908711 = 1363067) B1363067
theorem B1367495 : Blo 908576 1367495 := bstep (se 1 (by rfl) ⟨1025621, by rfl⟩ : syracuseStep 1367495 = 2051243) B2051243
theorem B908795 : Blo 908576 908795 := bstep (se 1 (by rfl) ⟨681596, by rfl⟩ : syracuseStep 908795 = 1363193) B1363193
theorem B908863 : Blo 908576 908863 := bstep (se 1 (by rfl) ⟨681647, by rfl⟩ : syracuseStep 908863 = 1363295) B1363295
theorem B908871 : Blo 908576 908871 := bstep (se 1 (by rfl) ⟨681653, by rfl⟩ : syracuseStep 908871 = 1363307) B1363307
theorem B909023 : Blo 908576 909023 := bstep (se 1 (by rfl) ⟨681767, by rfl⟩ : syracuseStep 909023 = 1363535) B1363535
theorem B1367849 : Blo 908576 1367849 := bstep (se 2 (by rfl) ⟨512943, by rfl⟩ : syracuseStep 1367849 = 1025887) B1025887
theorem B909103 : Blo 908576 909103 := bstep (se 1 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 909103 = 1363655) B1363655
theorem B1367855 : Blo 908576 1367855 := bstep (se 1 (by rfl) ⟨1025891, by rfl⟩ : syracuseStep 1367855 = 2051783) B2051783
theorem B3497789 : Blo 908576 3497789 := bstep (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) B1311671
theorem B909211 : Blo 908576 909211 := bstep (se 1 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 909211 = 1363817) B1363817
theorem B909263 : Blo 908576 909263 := bstep (se 1 (by rfl) ⟨681947, by rfl⟩ : syracuseStep 909263 = 1363895) B1363895
theorem B909287 : Blo 908576 909287 := bstep (se 1 (by rfl) ⟨681965, by rfl⟩ : syracuseStep 909287 = 1363931) B1363931
theorem B8740871 : Blo 908576 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B3072059 : Blo 908576 3072059 := bstep (se 1 (by rfl) ⟨2304044, by rfl⟩ : syracuseStep 3072059 = 4608089) B4608089
theorem B1368329 : Blo 908576 1368329 := bstep (se 2 (by rfl) ⟨513123, by rfl⟩ : syracuseStep 1368329 = 1026247) B1026247
theorem B909599 : Blo 908576 909599 := bstep (se 1 (by rfl) ⟨682199, by rfl⟩ : syracuseStep 909599 = 1364399) B1364399
theorem B3072329 : Blo 908576 3072329 := bstep (se 2 (by rfl) ⟨1152123, by rfl⟩ : syracuseStep 3072329 = 2304247) B2304247
theorem B909659 : Blo 908576 909659 := bstep (se 1 (by rfl) ⟨682244, by rfl⟩ : syracuseStep 909659 = 1364489) B1364489
theorem B3891563 : Blo 908576 3891563 := bstep (se 1 (by rfl) ⟨2918672, by rfl⟩ : syracuseStep 3891563 = 5837345) B5837345
theorem B909679 : Blo 908576 909679 := bstep (se 1 (by rfl) ⟨682259, by rfl⟩ : syracuseStep 909679 = 1364519) B1364519
theorem B1368431 : Blo 908576 1368431 := bstep (se 1 (by rfl) ⟨1026323, by rfl⟩ : syracuseStep 1368431 = 2052647) B2052647
theorem B909735 : Blo 908576 909735 := bstep (se 1 (by rfl) ⟨682301, by rfl⟩ : syracuseStep 909735 = 1364603) B1364603
theorem B909819 : Blo 908576 909819 := bstep (se 1 (by rfl) ⟨682364, by rfl⟩ : syracuseStep 909819 = 1364729) B1364729
theorem B909887 : Blo 908576 909887 := bstep (se 1 (by rfl) ⟨682415, by rfl⟩ : syracuseStep 909887 = 1364831) B1364831
theorem B909895 : Blo 908576 909895 := bstep (se 1 (by rfl) ⟨682421, by rfl⟩ : syracuseStep 909895 = 1364843) B1364843
theorem B1368647 : Blo 908576 1368647 := bstep (se 1 (by rfl) ⟨1026485, by rfl⟩ : syracuseStep 1368647 = 2052971) B2052971
theorem B1729097 : Blo 908576 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B1368683 : Blo 908576 1368683 := bstep (se 1 (by rfl) ⟨1026512, by rfl⟩ : syracuseStep 1368683 = 2053025) B2053025
theorem B910047 : Blo 908576 910047 := bstep (se 1 (by rfl) ⟨682535, by rfl⟩ : syracuseStep 910047 = 1365071) B1365071
theorem B910127 : Blo 908576 910127 := bstep (se 1 (by rfl) ⟨682595, by rfl⟩ : syracuseStep 910127 = 1365191) B1365191
theorem B910235 : Blo 908576 910235 := bstep (se 1 (by rfl) ⟨682676, by rfl⟩ : syracuseStep 910235 = 1365353) B1365353
theorem B910287 : Blo 908576 910287 := bstep (se 1 (by rfl) ⟨682715, by rfl⟩ : syracuseStep 910287 = 1365431) B1365431
theorem B910311 : Blo 908576 910311 := bstep (se 1 (by rfl) ⟨682733, by rfl⟩ : syracuseStep 910311 = 1365467) B1365467
theorem B4613111 : Blo 908576 4613111 := bstep (se 1 (by rfl) ⟨3459833, by rfl⟩ : syracuseStep 4613111 = 6919667) B6919667
theorem B910623 : Blo 908576 910623 := bstep (se 1 (by rfl) ⟨682967, by rfl⟩ : syracuseStep 910623 = 1365935) B1365935
theorem B910683 : Blo 908576 910683 := bstep (se 1 (by rfl) ⟨683012, by rfl⟩ : syracuseStep 910683 = 1366025) B1366025
theorem B910703 : Blo 908576 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B9856399 : Blo 908576 9856399 := bstep (se 1 (by rfl) ⟨7392299, by rfl⟩ : syracuseStep 9856399 = 14784599) B14784599
theorem B910759 : Blo 908576 910759 := bstep (se 1 (by rfl) ⟨683069, by rfl⟩ : syracuseStep 910759 = 1366139) B1366139
theorem B910843 : Blo 908576 910843 := bstep (se 1 (by rfl) ⟨683132, by rfl⟩ : syracuseStep 910843 = 1366265) B1366265
theorem B4384313 : Blo 908576 4384313 := bstep (se 2 (by rfl) ⟨1644117, by rfl⟩ : syracuseStep 4384313 = 3288235) B3288235
theorem B910911 : Blo 908576 910911 := bstep (se 1 (by rfl) ⟨683183, by rfl⟩ : syracuseStep 910911 = 1366367) B1366367
theorem B910919 : Blo 908576 910919 := bstep (se 1 (by rfl) ⟨683189, by rfl⟩ : syracuseStep 910919 = 1366379) B1366379
theorem B911071 : Blo 908576 911071 := bstep (se 1 (by rfl) ⟨683303, by rfl⟩ : syracuseStep 911071 = 1366607) B1366607
theorem B911151 : Blo 908576 911151 := bstep (se 1 (by rfl) ⟨683363, by rfl⟩ : syracuseStep 911151 = 1366727) B1366727
theorem B911259 : Blo 908576 911259 := bstep (se 1 (by rfl) ⟨683444, by rfl⟩ : syracuseStep 911259 = 1366889) B1366889
theorem B911311 : Blo 908576 911311 := bstep (se 1 (by rfl) ⟨683483, by rfl⟩ : syracuseStep 911311 = 1366967) B1366967
theorem B911335 : Blo 908576 911335 := bstep (se 1 (by rfl) ⟨683501, by rfl⟩ : syracuseStep 911335 = 1367003) B1367003
theorem B4679815 : Blo 908576 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B14772401 : Blo 908576 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B911647 : Blo 908576 911647 := bstep (se 1 (by rfl) ⟨683735, by rfl⟩ : syracuseStep 911647 = 1367471) B1367471
theorem B911707 : Blo 908576 911707 := bstep (se 1 (by rfl) ⟨683780, by rfl⟩ : syracuseStep 911707 = 1367561) B1367561
theorem B911727 : Blo 908576 911727 := bstep (se 1 (by rfl) ⟨683795, by rfl⟩ : syracuseStep 911727 = 1367591) B1367591
theorem B911783 : Blo 908576 911783 := bstep (se 1 (by rfl) ⟨683837, by rfl⟩ : syracuseStep 911783 = 1367675) B1367675
theorem B1731041 : Blo 908576 1731041 := bstep (se 2 (by rfl) ⟨649140, by rfl⟩ : syracuseStep 1731041 = 1298281) B1298281
theorem B911867 : Blo 908576 911867 := bstep (se 1 (by rfl) ⟨683900, by rfl⟩ : syracuseStep 911867 = 1367801) B1367801
theorem B911935 : Blo 908576 911935 := bstep (se 1 (by rfl) ⟨683951, by rfl⟩ : syracuseStep 911935 = 1367903) B1367903
theorem B911943 : Blo 908576 911943 := bstep (se 1 (by rfl) ⟨683957, by rfl⟩ : syracuseStep 911943 = 1367915) B1367915
theorem B1534585 : Blo 908576 1534585 := bstep (se 2 (by rfl) ⟨575469, by rfl⟩ : syracuseStep 1534585 = 1150939) B1150939
theorem B1534639 : Blo 908576 1534639 := bstep (se 1 (by rfl) ⟨1150979, by rfl⟩ : syracuseStep 1534639 = 2301959) B2301959
theorem B912095 : Blo 908576 912095 := bstep (se 1 (by rfl) ⟨684071, by rfl⟩ : syracuseStep 912095 = 1368143) B1368143
theorem B568519397 : Blo 908576 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B912175 : Blo 908576 912175 := bstep (se 1 (by rfl) ⟨684131, by rfl⟩ : syracuseStep 912175 = 1368263) B1368263
theorem B4615055 : Blo 908576 4615055 := bstep (se 1 (by rfl) ⟨3461291, by rfl⟩ : syracuseStep 4615055 = 6922583) B6922583
theorem B2190235 : Blo 908576 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B912283 : Blo 908576 912283 := bstep (se 1 (by rfl) ⟨684212, by rfl⟩ : syracuseStep 912283 = 1368425) B1368425
theorem B912335 : Blo 908576 912335 := bstep (se 1 (by rfl) ⟨684251, by rfl⟩ : syracuseStep 912335 = 1368503) B1368503
theorem B912359 : Blo 908576 912359 := bstep (se 1 (by rfl) ⟨684269, by rfl⟩ : syracuseStep 912359 = 1368539) B1368539
theorem B10382417 : Blo 908576 10382417 := bstep (se 2 (by rfl) ⟨3893406, by rfl⟩ : syracuseStep 10382417 = 7786813) B7786813
theorem B1731937 : Blo 908576 1731937 := bstep (se 2 (by rfl) ⟨649476, by rfl⟩ : syracuseStep 1731937 = 1298953) B1298953
theorem B3075515 : Blo 908576 3075515 := bstep (se 1 (by rfl) ⟨2306636, by rfl⟩ : syracuseStep 3075515 = 4613273) B4613273
theorem B3698291 : Blo 908576 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B2191369 : Blo 908576 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B3698713 : Blo 908576 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B2191465 : Blo 908576 2191465 := bstep (se 2 (by rfl) ⟨821799, by rfl⟩ : syracuseStep 2191465 = 1643599) B1643599
theorem B84275315 : Blo 908576 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B1536347 : Blo 908576 1536347 := bstep (se 1 (by rfl) ⟨1152260, by rfl⟩ : syracuseStep 1536347 = 2304521) B2304521
theorem B1536367 : Blo 908576 1536367 := bstep (se 1 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 1536367 = 2304551) B2304551
theorem B1536583 : Blo 908576 1536583 := bstep (se 1 (by rfl) ⟨1152437, by rfl⟩ : syracuseStep 1536583 = 2304875) B2304875
theorem B7762553 : Blo 908576 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B4617161 : Blo 908576 4617161 := bstep (se 2 (by rfl) ⟨1731435, by rfl⟩ : syracuseStep 4617161 = 3462871) B3462871
theorem B1537015 : Blo 908576 1537015 := bstep (se 1 (by rfl) ⟨1152761, by rfl⟩ : syracuseStep 1537015 = 2305523) B2305523
theorem B2192599 : Blo 908576 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B1537319 : Blo 908576 1537319 := bstep (se 1 (by rfl) ⟨1152989, by rfl⟩ : syracuseStep 1537319 = 2305979) B2305979
theorem B1537771 : Blo 908576 1537771 := bstep (se 1 (by rfl) ⟨1153328, by rfl⟩ : syracuseStep 1537771 = 2306657) B2306657
theorem B9598907 : Blo 908576 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B5830937 : Blo 908576 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B3897629 : Blo 908576 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B2914879 : Blo 908576 2914879 := bstep (se 1 (by rfl) ⟨2186159, by rfl⟩ : syracuseStep 2914879 = 4372319) B4372319
theorem B1538743 : Blo 908576 1538743 := bstep (se 1 (by rfl) ⟨1154057, by rfl⟩ : syracuseStep 1538743 = 2308115) B2308115
theorem B9862073 : Blo 908576 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B1539047 : Blo 908576 1539047 := bstep (se 1 (by rfl) ⟨1154285, by rfl⟩ : syracuseStep 1539047 = 2308571) B2308571
theorem B7371899 : Blo 908576 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B5831909 : Blo 908576 5831909 := bstep (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) B1093483
theorem B2588041 : Blo 908576 2588041 := bstep (se 2 (by rfl) ⟨970515, by rfl⟩ : syracuseStep 2588041 = 1941031) B1941031
theorem B3079673 : Blo 908576 3079673 := bstep (se 2 (by rfl) ⟨1154877, by rfl⟩ : syracuseStep 3079673 = 2309755) B2309755
theorem B5176993 : Blo 908576 5176993 := bstep (se 2 (by rfl) ⟨1941372, by rfl⟩ : syracuseStep 5176993 = 3882745) B3882745
theorem B2588395 : Blo 908576 2588395 := bstep (se 1 (by rfl) ⟨1941296, by rfl⟩ : syracuseStep 2588395 = 3882593) B3882593
theorem B3079943 : Blo 908576 3079943 := bstep (se 1 (by rfl) ⟨2309957, by rfl⟩ : syracuseStep 3079943 = 4619915) B4619915
theorem B4161455 : Blo 908576 4161455 := bstep (se 1 (by rfl) ⟨3121091, by rfl⟩ : syracuseStep 4161455 = 6242183) B6242183
theorem B25296947 : Blo 908576 25296947 := bstep (se 1 (by rfl) ⟨18972710, by rfl⟩ : syracuseStep 25296947 = 37945421) B37945421
theorem B23330915 : Blo 908576 23330915 := bstep (se 1 (by rfl) ⟨17498186, by rfl⟩ : syracuseStep 23330915 = 34996373) B34996373
theorem B5832935 : Blo 908576 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B22151987 : Blo 908576 22151987 := bstep (se 1 (by rfl) ⟨16613990, by rfl⟩ : syracuseStep 22151987 = 33227981) B33227981
theorem B7766927 : Blo 908576 7766927 := bstep (se 1 (by rfl) ⟨5825195, by rfl⟩ : syracuseStep 7766927 = 11650391) B11650391
theorem B5178269 : Blo 908576 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B8324441 : Blo 908576 8324441 := bstep (se 2 (by rfl) ⟨3121665, by rfl⟩ : syracuseStep 8324441 = 6243331) B6243331
theorem B2590127 : Blo 908576 2590127 := bstep (se 1 (by rfl) ⟨1942595, by rfl⟩ : syracuseStep 2590127 = 3885191) B3885191
theorem B4916695 : Blo 908576 4916695 := bstep (se 1 (by rfl) ⟨3687521, by rfl⟩ : syracuseStep 4916695 = 7375043) B7375043
theorem B2917903 : Blo 908576 2917903 := bstep (se 1 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 2917903 = 4376855) B4376855
theorem B2590319 : Blo 908576 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B6227567 : Blo 908576 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B5834551 : Blo 908576 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B13141865 : Blo 908576 13141865 := bstep (se 2 (by rfl) ⟨4928199, by rfl⟩ : syracuseStep 13141865 = 9856399) B9856399
theorem B2951585 : Blo 908576 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B2951687 : Blo 908576 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B7769317 : Blo 908576 7769317 := bstep (se 4 (by rfl) ⟨728373, by rfl⟩ : syracuseStep 7769317 = 1456747) B1456747
theorem B1641839 : Blo 908576 1641839 := bstep (se 1 (by rfl) ⟨1231379, by rfl⟩ : syracuseStep 1641839 = 2462759) B2462759
theorem B2920313 : Blo 908576 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B1150843 : Blo 908576 1150843 := bstep (se 1 (by rfl) ⟨863132, by rfl⟩ : syracuseStep 1150843 = 1726265) B1726265
theorem B2593235 : Blo 908576 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B10654507 : Blo 908576 10654507 := bstep (se 1 (by rfl) ⟨7990880, by rfl⟩ : syracuseStep 10654507 = 15981761) B15981761
theorem B1151911 : Blo 908576 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B3937319 : Blo 908576 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B3282095 : Blo 908576 3282095 := bstep (se 1 (by rfl) ⟨2461571, by rfl⟩ : syracuseStep 3282095 = 4923143) B4923143
theorem B2921825 : Blo 908576 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B3282295 : Blo 908576 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B2921953 : Blo 908576 2921953 := bstep (se 2 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 2921953 = 2191465) B2191465
theorem B2594375 : Blo 908576 2594375 := bstep (se 1 (by rfl) ⟨1945781, by rfl⟩ : syracuseStep 2594375 = 3891563) B3891563
theorem B1152731 : Blo 908576 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B2463625 : Blo 908576 2463625 := bstep (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) B1847719
theorem B2594717 : Blo 908576 2594717 := bstep (se 3 (by rfl) ⟨486509, by rfl⟩ : syracuseStep 2594717 = 973019) B973019
theorem B2955323 : Blo 908576 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B2300147 : Blo 908576 2300147 := bstep (se 1 (by rfl) ⟨1725110, by rfl⟩ : syracuseStep 2300147 = 3450221) B3450221
theorem B2922875 : Blo 908576 2922875 := bstep (se 1 (by rfl) ⟨2192156, by rfl⟩ : syracuseStep 2922875 = 4384313) B4384313
theorem B6822319 : Blo 908576 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1383259 : Blo 908576 1383259 := bstep (se 1 (by rfl) ⟨1037444, by rfl⟩ : syracuseStep 1383259 = 2074889) B2074889
theorem B2923465 : Blo 908576 2923465 := bstep (se 2 (by rfl) ⟨1096299, by rfl⟩ : syracuseStep 2923465 = 2192599) B2192599
theorem B1154027 : Blo 908576 1154027 := bstep (se 1 (by rfl) ⟨865520, by rfl⟩ : syracuseStep 1154027 = 1731041) B1731041
theorem B6233203 : Blo 908576 6233203 := bstep (se 1 (by rfl) ⟨4674902, by rfl⟩ : syracuseStep 6233203 = 9349805) B9349805
theorem B4005011 : Blo 908576 4005011 := bstep (se 1 (by rfl) ⟨3003758, by rfl⟩ : syracuseStep 4005011 = 6007517) B6007517
theorem B6921611 : Blo 908576 6921611 := bstep (se 1 (by rfl) ⟨5191208, by rfl⟩ : syracuseStep 6921611 = 10382417) B10382417
theorem B3120545 : Blo 908576 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B2465527 : Blo 908576 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B2301767 : Blo 908576 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B11673659 : Blo 908576 11673659 := bstep (se 1 (by rfl) ⟨8755244, by rfl⟩ : syracuseStep 11673659 = 17510489) B17510489
theorem B2302091 : Blo 908576 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B1024231 : Blo 908576 1024231 := bstep (se 1 (by rfl) ⟨768173, by rfl⟩ : syracuseStep 1024231 = 1536347) B1536347
theorem B2302415 : Blo 908576 2302415 := bstep (se 1 (by rfl) ⟨1726811, by rfl⟩ : syracuseStep 2302415 = 3453623) B3453623
theorem B10363463 : Blo 908576 10363463 := bstep (se 1 (by rfl) ⟨7772597, by rfl⟩ : syracuseStep 10363463 = 15545195) B15545195
theorem B1024879 : Blo 908576 1024879 := bstep (se 1 (by rfl) ⟨768659, by rfl⟩ : syracuseStep 1024879 = 1537319) B1537319
theorem B2302931 : Blo 908576 2302931 := bstep (se 1 (by rfl) ⟨1727198, by rfl⟩ : syracuseStep 2302931 = 3454397) B3454397
theorem B6399271 : Blo 908576 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B2598419 : Blo 908576 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B2303599 : Blo 908576 2303599 := bstep (se 1 (by rfl) ⟨1727699, by rfl⟩ : syracuseStep 2303599 = 3455399) B3455399
theorem B2336377 : Blo 908576 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B2303711 : Blo 908576 2303711 := bstep (se 1 (by rfl) ⟨1727783, by rfl⟩ : syracuseStep 2303711 = 3455567) B3455567
theorem B1386319 : Blo 908576 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B3450721 : Blo 908576 3450721 := bstep (se 2 (by rfl) ⟨1294020, by rfl⟩ : syracuseStep 3450721 = 2588041) B2588041
theorem B1026031 : Blo 908576 1026031 := bstep (se 1 (by rfl) ⟨769523, by rfl⟩ : syracuseStep 1026031 = 1539047) B1539047
theorem B11675663 : Blo 908576 11675663 := bstep (se 1 (by rfl) ⟨8756747, by rfl⟩ : syracuseStep 11675663 = 17513495) B17513495
theorem B3451193 : Blo 908576 3451193 := bstep (se 2 (by rfl) ⟨1294197, by rfl⟩ : syracuseStep 3451193 = 2588395) B2588395
theorem B11086895 : Blo 908576 11086895 := bstep (se 1 (by rfl) ⟨8315171, by rfl⟩ : syracuseStep 11086895 = 16630343) B16630343
theorem B6925985 : Blo 908576 6925985 := bstep (se 2 (by rfl) ⟨2597244, by rfl⟩ : syracuseStep 6925985 = 5194489) B5194489
theorem B2306171 : Blo 908576 2306171 := bstep (se 1 (by rfl) ⟨1729628, by rfl⟩ : syracuseStep 2306171 = 3459257) B3459257
theorem B4600313 : Blo 908576 4600313 := bstep (se 2 (by rfl) ⟨1725117, by rfl⟩ : syracuseStep 4600313 = 3450235) B3450235
theorem B4665871 : Blo 908576 4665871 := bstep (se 1 (by rfl) ⟨3499403, by rfl⟩ : syracuseStep 4665871 = 6998807) B6998807
theorem B3453455 : Blo 908576 3453455 := bstep (se 1 (by rfl) ⟨2590091, by rfl⟩ : syracuseStep 3453455 = 5180183) B5180183
theorem B2044511 : Blo 908576 2044511 := bstep (se 1 (by rfl) ⟨1533383, by rfl⟩ : syracuseStep 2044511 = 3066767) B3066767
theorem B10663001 : Blo 908576 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B1848595 : Blo 908576 1848595 := bstep (se 1 (by rfl) ⟨1386446, by rfl⟩ : syracuseStep 1848595 = 2772893) B2772893
theorem B2045339 : Blo 908576 2045339 := bstep (se 1 (by rfl) ⟨1534004, by rfl⟩ : syracuseStep 2045339 = 3068009) B3068009
theorem B6239753 : Blo 908576 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B7780049 : Blo 908576 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B8763241 : Blo 908576 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B2045915 : Blo 908576 2045915 := bstep (se 1 (by rfl) ⟨1534436, by rfl⟩ : syracuseStep 2045915 = 3068873) B3068873
theorem B3455081 : Blo 908576 3455081 := bstep (se 2 (by rfl) ⟨1295655, by rfl⟩ : syracuseStep 3455081 = 2591311) B2591311
theorem B15775859 : Blo 908576 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B2046095 : Blo 908576 2046095 := bstep (se 1 (by rfl) ⟨1534571, by rfl⟩ : syracuseStep 2046095 = 3069143) B3069143
theorem B2046113 : Blo 908576 2046113 := bstep (se 2 (by rfl) ⟨767292, by rfl⟩ : syracuseStep 2046113 = 1534585) B1534585
theorem B2046185 : Blo 908576 2046185 := bstep (se 2 (by rfl) ⟨767319, by rfl⟩ : syracuseStep 2046185 = 1534639) B1534639
theorem B7092793 : Blo 908576 7092793 := bstep (se 2 (by rfl) ⟨2659797, by rfl⟩ : syracuseStep 7092793 = 5319595) B5319595
theorem B28425107 : Blo 908576 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B2309249 : Blo 908576 2309249 := bstep (se 2 (by rfl) ⟨865968, by rfl⟩ : syracuseStep 2309249 = 1731937) B1731937
theorem B1293679 : Blo 908576 1293679 := bstep (se 1 (by rfl) ⟨970259, by rfl⟩ : syracuseStep 1293679 = 1940519) B1940519
theorem B2309543 : Blo 908576 2309543 := bstep (se 1 (by rfl) ⟨1732157, by rfl⟩ : syracuseStep 2309543 = 3464315) B3464315
theorem B2047463 : Blo 908576 2047463 := bstep (se 1 (by rfl) ⟨1535597, by rfl⟩ : syracuseStep 2047463 = 3071195) B3071195
theorem B4931617 : Blo 908576 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B2048039 : Blo 908576 2048039 := bstep (se 1 (by rfl) ⟨1536029, by rfl⟩ : syracuseStep 2048039 = 3072059) B3072059
theorem B2048219 : Blo 908576 2048219 := bstep (se 1 (by rfl) ⟨1536164, by rfl⟩ : syracuseStep 2048219 = 3072329) B3072329
theorem B8307143 : Blo 908576 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B2048489 : Blo 908576 2048489 := bstep (se 2 (by rfl) ⟨768183, by rfl⟩ : syracuseStep 2048489 = 1536367) B1536367
theorem B2048777 : Blo 908576 2048777 := bstep (se 2 (by rfl) ⟨768291, by rfl⟩ : syracuseStep 2048777 = 1536583) B1536583
theorem B2770109 : Blo 908576 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B2049353 : Blo 908576 2049353 := bstep (se 2 (by rfl) ⟨768507, by rfl⟩ : syracuseStep 2049353 = 1537015) B1537015
theorem B9356705 : Blo 908576 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B9848267 : Blo 908576 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B379012931 : Blo 908576 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B1296265 : Blo 908576 1296265 := bstep (se 2 (by rfl) ⟨486099, by rfl⟩ : syracuseStep 1296265 = 972199) B972199
theorem B2050343 : Blo 908576 2050343 := bstep (se 1 (by rfl) ⟨1537757, by rfl⟩ : syracuseStep 2050343 = 3075515) B3075515
theorem B2050361 : Blo 908576 2050361 := bstep (se 2 (by rfl) ⟨768885, by rfl⟩ : syracuseStep 2050361 = 1537771) B1537771
theorem B1559177 : Blo 908576 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B3066551 : Blo 908576 3066551 := bstep (se 1 (by rfl) ⟨2299913, by rfl⟩ : syracuseStep 3066551 = 4599827) B4599827
theorem B56183543 : Blo 908576 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B1362923 : Blo 908576 1362923 := bstep (se 1 (by rfl) ⟨1022192, by rfl⟩ : syracuseStep 1362923 = 2044385) B2044385
theorem B1297387 : Blo 908576 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B1363127 : Blo 908576 1363127 := bstep (se 1 (by rfl) ⟨1022345, by rfl⟩ : syracuseStep 1363127 = 2044691) B2044691
theorem B9457033 : Blo 908576 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B1363367 : Blo 908576 1363367 := bstep (se 1 (by rfl) ⟨1022525, by rfl⟩ : syracuseStep 1363367 = 2045051) B2045051
theorem B3886505 : Blo 908576 3886505 := bstep (se 2 (by rfl) ⟨1457439, by rfl⟩ : syracuseStep 3886505 = 2914879) B2914879
theorem B1363451 : Blo 908576 1363451 := bstep (se 1 (by rfl) ⟨1022588, by rfl⟩ : syracuseStep 1363451 = 2045177) B2045177
theorem B2051657 : Blo 908576 2051657 := bstep (se 2 (by rfl) ⟨769371, by rfl⟩ : syracuseStep 2051657 = 1538743) B1538743
theorem B1363547 : Blo 908576 1363547 := bstep (se 1 (by rfl) ⟨1022660, by rfl⟩ : syracuseStep 1363547 = 2045321) B2045321
theorem B3460715 : Blo 908576 3460715 := bstep (se 1 (by rfl) ⟨2595536, by rfl⟩ : syracuseStep 3460715 = 5191073) B5191073
theorem B1363631 : Blo 908576 1363631 := bstep (se 1 (by rfl) ⟨1022723, by rfl⟩ : syracuseStep 1363631 = 2045447) B2045447
theorem B1363751 : Blo 908576 1363751 := bstep (se 1 (by rfl) ⟨1022813, by rfl⟩ : syracuseStep 1363751 = 2045627) B2045627
theorem B1363835 : Blo 908576 1363835 := bstep (se 1 (by rfl) ⟨1022876, by rfl⟩ : syracuseStep 1363835 = 2045753) B2045753
theorem B3887291 : Blo 908576 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B1364255 : Blo 908576 1364255 := bstep (se 1 (by rfl) ⟨1023191, by rfl⟩ : syracuseStep 1364255 = 2046383) B2046383
theorem B19976483 : Blo 908576 19976483 := bstep (se 1 (by rfl) ⟨14982362, by rfl⟩ : syracuseStep 19976483 = 29964725) B29964725
theorem B1364279 : Blo 908576 1364279 := bstep (se 1 (by rfl) ⟨1023209, by rfl⟩ : syracuseStep 1364279 = 2046419) B2046419
theorem B1364351 : Blo 908576 1364351 := bstep (se 1 (by rfl) ⟨1023263, by rfl⟩ : syracuseStep 1364351 = 2046527) B2046527
theorem B1364423 : Blo 908576 1364423 := bstep (se 1 (by rfl) ⟨1023317, by rfl⟩ : syracuseStep 1364423 = 2046635) B2046635
theorem B1167823 : Blo 908576 1167823 := bstep (se 1 (by rfl) ⟨875867, by rfl⟩ : syracuseStep 1167823 = 1751735) B1751735
theorem B3068495 : Blo 908576 3068495 := bstep (se 1 (by rfl) ⟨2301371, by rfl⟩ : syracuseStep 3068495 = 4602743) B4602743
theorem B6574715 : Blo 908576 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B1364777 : Blo 908576 1364777 := bstep (se 2 (by rfl) ⟨511791, by rfl⟩ : syracuseStep 1364777 = 1023583) B1023583
theorem B1364783 : Blo 908576 1364783 := bstep (se 1 (by rfl) ⟨1023587, by rfl⟩ : syracuseStep 1364783 = 2047175) B2047175
theorem B4379453 : Blo 908576 4379453 := bstep (se 3 (by rfl) ⟨821147, by rfl⟩ : syracuseStep 4379453 = 1642295) B1642295
theorem B3887939 : Blo 908576 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B9327437 : Blo 908576 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B6902657 : Blo 908576 6902657 := bstep (se 2 (by rfl) ⟨2588496, by rfl⟩ : syracuseStep 6902657 = 5176993) B5176993
theorem B1364903 : Blo 908576 1364903 := bstep (se 1 (by rfl) ⟨1023677, by rfl⟩ : syracuseStep 1364903 = 2047355) B2047355
theorem B1364987 : Blo 908576 1364987 := bstep (se 1 (by rfl) ⟨1023740, by rfl⟩ : syracuseStep 1364987 = 2047481) B2047481
theorem B2053115 : Blo 908576 2053115 := bstep (se 1 (by rfl) ⟨1539836, by rfl⟩ : syracuseStep 2053115 = 3079673) B3079673
theorem B1365047 : Blo 908576 1365047 := bstep (se 1 (by rfl) ⟨1023785, by rfl⟩ : syracuseStep 1365047 = 2047571) B2047571
theorem B6575201 : Blo 908576 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B3069035 : Blo 908576 3069035 := bstep (se 1 (by rfl) ⟨2301776, by rfl⟩ : syracuseStep 3069035 = 4603553) B4603553
theorem B1365167 : Blo 908576 1365167 := bstep (se 1 (by rfl) ⟨1023875, by rfl⟩ : syracuseStep 1365167 = 2047751) B2047751
theorem B2053295 : Blo 908576 2053295 := bstep (se 1 (by rfl) ⟨1539971, by rfl⟩ : syracuseStep 2053295 = 3079943) B3079943
theorem B2774303 : Blo 908576 2774303 := bstep (se 1 (by rfl) ⟨2080727, by rfl⟩ : syracuseStep 2774303 = 4161455) B4161455
theorem B1365575 : Blo 908576 1365575 := bstep (se 1 (by rfl) ⟨1024181, by rfl⟩ : syracuseStep 1365575 = 2048363) B2048363
theorem B1365671 : Blo 908576 1365671 := bstep (se 1 (by rfl) ⟨1024253, by rfl⟩ : syracuseStep 1365671 = 2048507) B2048507
theorem B1365755 : Blo 908576 1365755 := bstep (se 1 (by rfl) ⟨1024316, by rfl⟩ : syracuseStep 1365755 = 2048633) B2048633
theorem B1365791 : Blo 908576 1365791 := bstep (se 1 (by rfl) ⟨1024343, by rfl⟩ : syracuseStep 1365791 = 2048687) B2048687
theorem B1365839 : Blo 908576 1365839 := bstep (se 1 (by rfl) ⟨1024379, by rfl⟩ : syracuseStep 1365839 = 2048759) B2048759
theorem B1365959 : Blo 908576 1365959 := bstep (se 1 (by rfl) ⟨1024469, by rfl⟩ : syracuseStep 1365959 = 2048939) B2048939
theorem B8312807 : Blo 908576 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B1726447 : Blo 908576 1726447 := bstep (se 1 (by rfl) ⟨1294835, by rfl⟩ : syracuseStep 1726447 = 2589671) B2589671
theorem B1726697 : Blo 908576 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B1366313 : Blo 908576 1366313 := bstep (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) B1024735
theorem B1366319 : Blo 908576 1366319 := bstep (se 1 (by rfl) ⟨1024739, by rfl⟩ : syracuseStep 1366319 = 2049479) B2049479
theorem B3070331 : Blo 908576 3070331 := bstep (se 1 (by rfl) ⟨2302748, by rfl⟩ : syracuseStep 3070331 = 4605497) B4605497
theorem B1366559 : Blo 908576 1366559 := bstep (se 1 (by rfl) ⟨1024919, by rfl⟩ : syracuseStep 1366559 = 2049839) B2049839
theorem B4610681 : Blo 908576 4610681 := bstep (se 2 (by rfl) ⟨1729005, by rfl⟩ : syracuseStep 4610681 = 3458011) B3458011
theorem B3070601 : Blo 908576 3070601 := bstep (se 2 (by rfl) ⟨1151475, by rfl⟩ : syracuseStep 3070601 = 2302951) B2302951
theorem B5986973 : Blo 908576 5986973 := bstep (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) B2245115
theorem B1661627 : Blo 908576 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B5823197 : Blo 908576 5823197 := bstep (se 3 (by rfl) ⟨1091849, by rfl⟩ : syracuseStep 5823197 = 2183699) B2183699
theorem B1366943 : Blo 908576 1366943 := bstep (se 1 (by rfl) ⟨1025207, by rfl⟩ : syracuseStep 1366943 = 2050415) B2050415
theorem B1366991 : Blo 908576 1366991 := bstep (se 1 (by rfl) ⟨1025243, by rfl⟩ : syracuseStep 1366991 = 2050487) B2050487
theorem B1367081 : Blo 908576 1367081 := bstep (se 2 (by rfl) ⟨512655, by rfl⟩ : syracuseStep 1367081 = 1025311) B1025311
theorem B1367087 : Blo 908576 1367087 := bstep (se 1 (by rfl) ⟨1025315, by rfl⟩ : syracuseStep 1367087 = 2050631) B2050631
theorem B1367111 : Blo 908576 1367111 := bstep (se 1 (by rfl) ⟨1025333, by rfl⟩ : syracuseStep 1367111 = 2050667) B2050667
theorem B1170655 : Blo 908576 1170655 := bstep (se 1 (by rfl) ⟨877991, by rfl⟩ : syracuseStep 1170655 = 1755983) B1755983
theorem B1367375 : Blo 908576 1367375 := bstep (se 1 (by rfl) ⟨1025531, by rfl⟩ : syracuseStep 1367375 = 2051063) B2051063
theorem B1367465 : Blo 908576 1367465 := bstep (se 2 (by rfl) ⟨512799, by rfl⟩ : syracuseStep 1367465 = 1025599) B1025599
theorem B7396811 : Blo 908576 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B908775 : Blo 908576 908775 := bstep (se 1 (by rfl) ⟨681581, by rfl⟩ : syracuseStep 908775 = 1363163) B1363163
theorem B1367615 : Blo 908576 1367615 := bstep (se 1 (by rfl) ⟨1025711, by rfl⟩ : syracuseStep 1367615 = 2051423) B2051423
theorem B908891 : Blo 908576 908891 := bstep (se 1 (by rfl) ⟨681668, by rfl⟩ : syracuseStep 908891 = 1363337) B1363337
theorem B3071735 : Blo 908576 3071735 := bstep (se 1 (by rfl) ⟨2303801, by rfl⟩ : syracuseStep 3071735 = 4607603) B4607603
theorem B909127 : Blo 908576 909127 := bstep (se 1 (by rfl) ⟨681845, by rfl⟩ : syracuseStep 909127 = 1363691) B1363691
theorem B1367879 : Blo 908576 1367879 := bstep (se 1 (by rfl) ⟨1025909, by rfl⟩ : syracuseStep 1367879 = 2051819) B2051819
theorem B1367963 : Blo 908576 1367963 := bstep (se 1 (by rfl) ⟨1025972, by rfl⟩ : syracuseStep 1367963 = 2051945) B2051945
theorem B909279 : Blo 908576 909279 := bstep (se 1 (by rfl) ⟨681959, by rfl⟩ : syracuseStep 909279 = 1363919) B1363919
theorem B909543 : Blo 908576 909543 := bstep (se 1 (by rfl) ⟨682157, by rfl⟩ : syracuseStep 909543 = 1364315) B1364315
theorem B909695 : Blo 908576 909695 := bstep (se 1 (by rfl) ⟨682271, by rfl⟩ : syracuseStep 909695 = 1364543) B1364543
theorem B909775 : Blo 908576 909775 := bstep (se 1 (by rfl) ⟨682331, by rfl⟩ : syracuseStep 909775 = 1364663) B1364663
theorem B1368527 : Blo 908576 1368527 := bstep (se 1 (by rfl) ⟨1026395, by rfl⟩ : syracuseStep 1368527 = 2052791) B2052791
theorem B1368569 : Blo 908576 1368569 := bstep (se 2 (by rfl) ⟨513213, by rfl⟩ : syracuseStep 1368569 = 1026427) B1026427
theorem B1368671 : Blo 908576 1368671 := bstep (se 1 (by rfl) ⟨1026503, by rfl⟩ : syracuseStep 1368671 = 2053007) B2053007
theorem B909927 : Blo 908576 909927 := bstep (se 1 (by rfl) ⟨682445, by rfl⟩ : syracuseStep 909927 = 1364891) B1364891
theorem B4678397 : Blo 908576 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B3072815 : Blo 908576 3072815 := bstep (se 1 (by rfl) ⟨2304611, by rfl⟩ : syracuseStep 3072815 = 4609223) B4609223
theorem B910191 : Blo 908576 910191 := bstep (se 1 (by rfl) ⟨682643, by rfl⟩ : syracuseStep 910191 = 1365287) B1365287
theorem B3072923 : Blo 908576 3072923 := bstep (se 1 (by rfl) ⟨2304692, by rfl⟩ : syracuseStep 3072923 = 4609385) B4609385
theorem B910247 : Blo 908576 910247 := bstep (se 1 (by rfl) ⟨682685, by rfl⟩ : syracuseStep 910247 = 1365371) B1365371
theorem B910331 : Blo 908576 910331 := bstep (se 1 (by rfl) ⟨682748, by rfl⟩ : syracuseStep 910331 = 1365497) B1365497
theorem B910399 : Blo 908576 910399 := bstep (se 1 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 910399 = 1365599) B1365599
theorem B910543 : Blo 908576 910543 := bstep (se 1 (by rfl) ⟨682907, by rfl⟩ : syracuseStep 910543 = 1365815) B1365815
theorem B101213563 : Blo 908576 101213563 := bstep (se 1 (by rfl) ⟨75910172, by rfl⟩ : syracuseStep 101213563 = 151820345) B151820345
theorem B910747 : Blo 908576 910747 := bstep (se 1 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 910747 = 1366121) B1366121
theorem B910959 : Blo 908576 910959 := bstep (se 1 (by rfl) ⟨683219, by rfl⟩ : syracuseStep 910959 = 1366439) B1366439
theorem B23291549 : Blo 908576 23291549 := bstep (se 3 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 23291549 = 8734331) B8734331
theorem B911015 : Blo 908576 911015 := bstep (se 1 (by rfl) ⟨683261, by rfl⟩ : syracuseStep 911015 = 1366523) B1366523
theorem B911099 : Blo 908576 911099 := bstep (se 1 (by rfl) ⟨683324, by rfl⟩ : syracuseStep 911099 = 1366649) B1366649
theorem B911135 : Blo 908576 911135 := bstep (se 1 (by rfl) ⟨683351, by rfl⟩ : syracuseStep 911135 = 1366703) B1366703
theorem B1730335 : Blo 908576 1730335 := bstep (se 1 (by rfl) ⟨1297751, by rfl⟩ : syracuseStep 1730335 = 2595503) B2595503
theorem B4384543 : Blo 908576 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B911167 : Blo 908576 911167 := bstep (se 1 (by rfl) ⟨683375, by rfl⟩ : syracuseStep 911167 = 1366751) B1366751
theorem B1533775 : Blo 908576 1533775 := bstep (se 1 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 1533775 = 2300663) B2300663
theorem B911343 : Blo 908576 911343 := bstep (se 1 (by rfl) ⟨683507, by rfl⟩ : syracuseStep 911343 = 1367015) B1367015
theorem B3074057 : Blo 908576 3074057 := bstep (se 2 (by rfl) ⟨1152771, by rfl⟩ : syracuseStep 3074057 = 2305543) B2305543
theorem B29485133 : Blo 908576 29485133 := bstep (se 3 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 29485133 = 11056925) B11056925
theorem B23685209 : Blo 908576 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B911515 : Blo 908576 911515 := bstep (se 1 (by rfl) ⟨683636, by rfl⟩ : syracuseStep 911515 = 1367273) B1367273
theorem B911551 : Blo 908576 911551 := bstep (se 1 (by rfl) ⟨683663, by rfl⟩ : syracuseStep 911551 = 1367327) B1367327
theorem B1534187 : Blo 908576 1534187 := bstep (se 1 (by rfl) ⟨1150640, by rfl⟩ : syracuseStep 1534187 = 2301281) B2301281
theorem B911663 : Blo 908576 911663 := bstep (se 1 (by rfl) ⟨683747, by rfl⟩ : syracuseStep 911663 = 1367495) B1367495
theorem B4679993 : Blo 908576 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B911899 : Blo 908576 911899 := bstep (se 1 (by rfl) ⟨683924, by rfl⟩ : syracuseStep 911899 = 1367849) B1367849
theorem B911903 : Blo 908576 911903 := bstep (se 1 (by rfl) ⟨683927, by rfl⟩ : syracuseStep 911903 = 1367855) B1367855
theorem B5827247 : Blo 908576 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B912219 : Blo 908576 912219 := bstep (se 1 (by rfl) ⟨684164, by rfl⟩ : syracuseStep 912219 = 1368329) B1368329
theorem B912287 : Blo 908576 912287 := bstep (se 1 (by rfl) ⟨684215, by rfl⟩ : syracuseStep 912287 = 1368431) B1368431
theorem B1535017 : Blo 908576 1535017 := bstep (se 2 (by rfl) ⟨575631, by rfl⟩ : syracuseStep 1535017 = 1151263) B1151263
theorem B912431 : Blo 908576 912431 := bstep (se 1 (by rfl) ⟨684323, by rfl⟩ : syracuseStep 912431 = 1368647) B1368647
theorem B912455 : Blo 908576 912455 := bstep (se 1 (by rfl) ⟨684341, by rfl⟩ : syracuseStep 912455 = 1368683) B1368683
theorem B1535159 : Blo 908576 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B3075353 : Blo 908576 3075353 := bstep (se 2 (by rfl) ⟨1153257, by rfl⟩ : syracuseStep 3075353 = 2306515) B2306515
theorem B3075407 : Blo 908576 3075407 := bstep (se 1 (by rfl) ⟨2306555, by rfl⟩ : syracuseStep 3075407 = 4613111) B4613111
theorem B3894637 : Blo 908576 3894637 := bstep (se 3 (by rfl) ⟨730244, by rfl⟩ : syracuseStep 3894637 = 1460489) B1460489
theorem B15756743 : Blo 908576 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B1535483 : Blo 908576 1535483 := bstep (se 1 (by rfl) ⟨1151612, by rfl⟩ : syracuseStep 1535483 = 2303225) B2303225
theorem B1535915 : Blo 908576 1535915 := bstep (se 1 (by rfl) ⟨1151936, by rfl⟩ : syracuseStep 1535915 = 2303873) B2303873
theorem B13136215 : Blo 908576 13136215 := bstep (se 1 (by rfl) ⟨9852161, by rfl⟩ : syracuseStep 13136215 = 19704323) B19704323
theorem B25555301 : Blo 908576 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B1536455 : Blo 908576 1536455 := bstep (se 1 (by rfl) ⟨1152341, by rfl⟩ : syracuseStep 1536455 = 2304683) B2304683
theorem B6910433 : Blo 908576 6910433 := bstep (se 2 (by rfl) ⟨2591412, by rfl⟩ : syracuseStep 6910433 = 5182825) B5182825
theorem B5534201 : Blo 908576 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B3076703 : Blo 908576 3076703 := bstep (se 1 (by rfl) ⟨2307527, by rfl⟩ : syracuseStep 3076703 = 4615055) B4615055
theorem B1537231 : Blo 908576 1537231 := bstep (se 1 (by rfl) ⟨1152923, by rfl⟩ : syracuseStep 1537231 = 2305847) B2305847
theorem B5534963 : Blo 908576 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B9008435 : Blo 908576 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B5175035 : Blo 908576 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B3077945 : Blo 908576 3077945 := bstep (se 2 (by rfl) ⟨1154229, by rfl⟩ : syracuseStep 3077945 = 2308459) B2308459
theorem B3078107 : Blo 908576 3078107 := bstep (se 1 (by rfl) ⟨2308580, by rfl⟩ : syracuseStep 3078107 = 4617161) B4617161
theorem B1538041 : Blo 908576 1538041 := bstep (se 2 (by rfl) ⟨576765, by rfl⟩ : syracuseStep 1538041 = 1153531) B1153531
theorem B1538203 : Blo 908576 1538203 := bstep (se 1 (by rfl) ⟨1153652, by rfl⟩ : syracuseStep 1538203 = 2307305) B2307305
theorem B3078377 : Blo 908576 3078377 := bstep (se 2 (by rfl) ⟨1154391, by rfl⟩ : syracuseStep 3078377 = 2308783) B2308783
theorem B1538311 : Blo 908576 1538311 := bstep (se 1 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 1538311 = 2307467) B2307467
theorem B1538345 : Blo 908576 1538345 := bstep (se 2 (by rfl) ⟨576879, by rfl⟩ : syracuseStep 1538345 = 1153759) B1153759
theorem B3078809 : Blo 908576 3078809 := bstep (se 2 (by rfl) ⟨1154553, by rfl⟩ : syracuseStep 3078809 = 2309107) B2309107
theorem B1539337 : Blo 908576 1539337 := bstep (se 2 (by rfl) ⟨577251, by rfl⟩ : syracuseStep 1539337 = 1154503) B1154503
theorem B4914599 : Blo 908576 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B49741249 : Blo 908576 49741249 := bstep (se 2 (by rfl) ⟨18652968, by rfl⟩ : syracuseStep 49741249 = 37305937) B37305937
theorem B1539911 : Blo 908576 1539911 := bstep (se 1 (by rfl) ⟨1154933, by rfl⟩ : syracuseStep 1539911 = 2309867) B2309867
theorem B1638265 : Blo 908576 1638265 := bstep (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) B1228699
theorem B5538095 : Blo 908576 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B5177951 : Blo 908576 5177951 := bstep (se 1 (by rfl) ⟨3883463, by rfl⟩ : syracuseStep 5177951 = 7766927) B7766927
theorem B252675287 : Blo 908576 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B6915293 : Blo 908576 6915293 := bstep (se 3 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 6915293 = 2593235) B2593235
theorem B1967723 : Blo 908576 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B37455695 : Blo 908576 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B6555593 : Blo 908576 6555593 := bstep (se 2 (by rfl) ⟨2458347, by rfl⟩ : syracuseStep 6555593 = 4916695) B4916695
theorem B3115169 : Blo 908576 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B2591003 : Blo 908576 2591003 := bstep (se 1 (by rfl) ⟨1943252, by rfl⟩ : syracuseStep 2591003 = 3886505) B3886505
theorem B6228389 : Blo 908576 6228389 := bstep (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) B1167823
theorem B2591527 : Blo 908576 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B2919635 : Blo 908576 2919635 := bstep (se 1 (by rfl) ⟨2189726, by rfl⟩ : syracuseStep 2919635 = 4379453) B4379453
theorem B2624879 : Blo 908576 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B5541871 : Blo 908576 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B56824037 : Blo 908576 56824037 := bstep (se 4 (by rfl) ⟨5327253, by rfl⟩ : syracuseStep 56824037 = 10654507) B10654507
theorem B10359089 : Blo 908576 10359089 := bstep (se 2 (by rfl) ⟨3884658, by rfl⟩ : syracuseStep 10359089 = 7769317) B7769317
theorem B3118931 : Blo 908576 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B7871165 : Blo 908576 7871165 := bstep (se 3 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 7871165 = 2951687) B2951687
theorem B1022791 : Blo 908576 1022791 := bstep (se 1 (by rfl) ⟨767093, by rfl⟩ : syracuseStep 1022791 = 1534187) B1534187
theorem B2300795 : Blo 908576 2300795 := bstep (se 1 (by rfl) ⟨1725596, by rfl⟩ : syracuseStep 2300795 = 3451193) B3451193
theorem B3119995 : Blo 908576 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B2464793 : Blo 908576 2464793 := bstep (se 2 (by rfl) ⟨924297, by rfl⟩ : syracuseStep 2464793 = 1848595) B1848595
theorem B15965261 : Blo 908576 15965261 := bstep (se 3 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 15965261 = 5986973) B5986973
theorem B1023439 : Blo 908576 1023439 := bstep (se 1 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 1023439 = 1535159) B1535159
theorem B1023655 : Blo 908576 1023655 := bstep (se 1 (by rfl) ⟨767741, by rfl⟩ : syracuseStep 1023655 = 1535483) B1535483
theorem B3284833 : Blo 908576 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B1023943 : Blo 908576 1023943 := bstep (se 1 (by rfl) ⟨767957, by rfl⟩ : syracuseStep 1023943 = 1535915) B1535915
theorem B2301929 : Blo 908576 2301929 := bstep (se 2 (by rfl) ⟨863223, by rfl⟩ : syracuseStep 2301929 = 1726447) B1726447
theorem B1024303 : Blo 908576 1024303 := bstep (se 1 (by rfl) ⟨768227, by rfl⟩ : syracuseStep 1024303 = 1536455) B1536455
theorem B2302303 : Blo 908576 2302303 := bstep (se 1 (by rfl) ⟨1726727, by rfl⟩ : syracuseStep 2302303 = 3453455) B3453455
theorem B6005623 : Blo 908576 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B1844345 : Blo 908576 1844345 := bstep (se 2 (by rfl) ⟨691629, by rfl⟩ : syracuseStep 1844345 = 1383259) B1383259
theorem B5186699 : Blo 908576 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B3450023 : Blo 908576 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B2303387 : Blo 908576 2303387 := bstep (se 1 (by rfl) ⟨1727540, by rfl⟩ : syracuseStep 2303387 = 3455081) B3455081
theorem B1025563 : Blo 908576 1025563 := bstep (se 1 (by rfl) ⟨769172, by rfl⟩ : syracuseStep 1025563 = 1538345) B1538345
theorem B18950071 : Blo 908576 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B3287369 : Blo 908576 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B1026607 : Blo 908576 1026607 := bstep (se 1 (by rfl) ⟨769955, by rfl⟩ : syracuseStep 1026607 = 1539911) B1539911
theorem B3452179 : Blo 908576 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B1846739 : Blo 908576 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B5549627 : Blo 908576 5549627 := bstep (se 1 (by rfl) ⟨4162220, by rfl⟩ : syracuseStep 5549627 = 8324441) B8324441
theorem B6237803 : Blo 908576 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B6565511 : Blo 908576 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B8761243 : Blo 908576 8761243 := bstep (se 1 (by rfl) ⟨6570932, by rfl⟩ : syracuseStep 8761243 = 13141865) B13141865
theorem B14757869 : Blo 908576 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B8532361 : Blo 908576 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B2044367 : Blo 908576 2044367 := bstep (se 1 (by rfl) ⟨1533275, by rfl⟩ : syracuseStep 2044367 = 3066551) B3066551
theorem B134951417 : Blo 908576 134951417 := bstep (se 2 (by rfl) ⟨50606781, by rfl⟩ : syracuseStep 134951417 = 101213563) B101213563
theorem B10367837 : Blo 908576 10367837 := bstep (se 3 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 10367837 = 3887939) B3887939
theorem B2307113 : Blo 908576 2307113 := bstep (se 2 (by rfl) ⟨865167, by rfl⟩ : syracuseStep 2307113 = 1730335) B1730335
theorem B5846057 : Blo 908576 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B2307143 : Blo 908576 2307143 := bstep (se 1 (by rfl) ⟨1730357, by rfl⟩ : syracuseStep 2307143 = 3460715) B3460715
theorem B7779401 : Blo 908576 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B2045033 : Blo 908576 2045033 := bstep (se 2 (by rfl) ⟨766887, by rfl⟩ : syracuseStep 2045033 = 1533775) B1533775
theorem B1848425 : Blo 908576 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B4600961 : Blo 908576 4600961 := bstep (se 2 (by rfl) ⟨1725360, by rfl⟩ : syracuseStep 4600961 = 3450721) B3450721
theorem B1946875 : Blo 908576 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B13317655 : Blo 908576 13317655 := bstep (se 1 (by rfl) ⟨9988241, by rfl⟩ : syracuseStep 13317655 = 19976483) B19976483
theorem B2045663 : Blo 908576 2045663 := bstep (se 1 (by rfl) ⟨1534247, by rfl⟩ : syracuseStep 2045663 = 3068495) B3068495
theorem B4601771 : Blo 908576 4601771 := bstep (se 1 (by rfl) ⟨3451328, by rfl⟩ : syracuseStep 4601771 = 6902657) B6902657
theorem B2046023 : Blo 908576 2046023 := bstep (se 1 (by rfl) ⟨1534517, by rfl⟩ : syracuseStep 2046023 = 3069035) B3069035
theorem B1849535 : Blo 908576 1849535 := bstep (se 1 (by rfl) ⟨1387151, by rfl⟩ : syracuseStep 1849535 = 2774303) B2774303
theorem B1947883 : Blo 908576 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B17512949 : Blo 908576 17512949 := bstep (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) B1641839
theorem B2046689 : Blo 908576 2046689 := bstep (se 2 (by rfl) ⟨767508, by rfl⟩ : syracuseStep 2046689 = 1535017) B1535017
theorem B2046887 : Blo 908576 2046887 := bstep (se 1 (by rfl) ⟨1535165, by rfl⟩ : syracuseStep 2046887 = 3070331) B3070331
theorem B1948583 : Blo 908576 1948583 := bstep (se 1 (by rfl) ⟨1461437, by rfl⟩ : syracuseStep 1948583 = 2922875) B2922875
theorem B2047067 : Blo 908576 2047067 := bstep (se 1 (by rfl) ⟨1535300, by rfl⟩ : syracuseStep 2047067 = 3070601) B3070601
theorem B5192849 : Blo 908576 5192849 := bstep (se 2 (by rfl) ⟨1947318, by rfl⟩ : syracuseStep 5192849 = 3894637) B3894637
theorem B3882131 : Blo 908576 3882131 := bstep (se 1 (by rfl) ⟨2911598, by rfl⟩ : syracuseStep 3882131 = 5823197) B5823197
theorem B2670007 : Blo 908576 2670007 := bstep (se 1 (by rfl) ⟨2002505, by rfl⟩ : syracuseStep 2670007 = 4005011) B4005011
theorem B4931207 : Blo 908576 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B2047823 : Blo 908576 2047823 := bstep (se 1 (by rfl) ⟨1535867, by rfl⟩ : syracuseStep 2047823 = 3071735) B3071735
theorem B7782439 : Blo 908576 7782439 := bstep (se 1 (by rfl) ⟨5836829, by rfl⟩ : syracuseStep 7782439 = 11673659) B11673659
theorem B7880861 : Blo 908576 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B17514953 : Blo 908576 17514953 := bstep (se 2 (by rfl) ⟨6568107, by rfl⟩ : syracuseStep 17514953 = 13136215) B13136215
theorem B2048543 : Blo 908576 2048543 := bstep (se 1 (by rfl) ⟨1536407, by rfl⟩ : syracuseStep 2048543 = 3072815) B3072815
theorem B2048615 : Blo 908576 2048615 := bstep (se 1 (by rfl) ⟨1536461, by rfl⟩ : syracuseStep 2048615 = 3072923) B3072923
theorem B4604525 : Blo 908576 4604525 := bstep (se 3 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 4604525 = 1726697) B1726697
theorem B6243493 : Blo 908576 6243493 := bstep (se 4 (by rfl) ⟨585327, by rfl⟩ : syracuseStep 6243493 = 1170655) B1170655
theorem B2049371 : Blo 908576 2049371 := bstep (se 1 (by rfl) ⟨1537028, by rfl⟩ : syracuseStep 2049371 = 3074057) B3074057
theorem B7783775 : Blo 908576 7783775 := bstep (se 1 (by rfl) ⟨5837831, by rfl⟩ : syracuseStep 7783775 = 11675663) B11675663
theorem B2049641 : Blo 908576 2049641 := bstep (se 2 (by rfl) ⟨768615, by rfl⟩ : syracuseStep 2049641 = 1537231) B1537231
theorem B3884831 : Blo 908576 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B4376393 : Blo 908576 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B7391263 : Blo 908576 7391263 := bstep (se 1 (by rfl) ⟨5543447, by rfl⟩ : syracuseStep 7391263 = 11086895) B11086895
theorem B2050235 : Blo 908576 2050235 := bstep (se 1 (by rfl) ⟨1537676, by rfl⟩ : syracuseStep 2050235 = 3075353) B3075353
theorem B2050271 : Blo 908576 2050271 := bstep (se 1 (by rfl) ⟨1537703, by rfl⟩ : syracuseStep 2050271 = 3075407) B3075407
theorem B10504495 : Blo 908576 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B11684321 : Blo 908576 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B2050721 : Blo 908576 2050721 := bstep (se 2 (by rfl) ⟨769020, by rfl⟩ : syracuseStep 2050721 = 1538041) B1538041
theorem B2050937 : Blo 908576 2050937 := bstep (se 2 (by rfl) ⟨769101, by rfl⟩ : syracuseStep 2050937 = 1538203) B1538203
theorem B4606955 : Blo 908576 4606955 := bstep (se 1 (by rfl) ⟨3455216, by rfl⟩ : syracuseStep 4606955 = 6910433) B6910433
theorem B3066875 : Blo 908576 3066875 := bstep (se 1 (by rfl) ⟨2300156, by rfl⟩ : syracuseStep 3066875 = 4600313) B4600313
theorem B2051081 : Blo 908576 2051081 := bstep (se 2 (by rfl) ⟨769155, by rfl⟩ : syracuseStep 2051081 = 1538311) B1538311
theorem B1363007 : Blo 908576 1363007 := bstep (se 1 (by rfl) ⟨1022255, by rfl⟩ : syracuseStep 1363007 = 2044511) B2044511
theorem B2051135 : Blo 908576 2051135 := bstep (se 1 (by rfl) ⟨1538351, by rfl⟩ : syracuseStep 2051135 = 3076703) B3076703
theorem B9096425 : Blo 908576 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B9457057 : Blo 908576 9457057 := bstep (se 2 (by rfl) ⟨3546396, by rfl⟩ : syracuseStep 9457057 = 7092793) B7092793
theorem B3689975 : Blo 908576 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B1363559 : Blo 908576 1363559 := bstep (se 1 (by rfl) ⟨1022669, by rfl⟩ : syracuseStep 1363559 = 2045339) B2045339
theorem B2051963 : Blo 908576 2051963 := bstep (se 1 (by rfl) ⟨1538972, by rfl⟩ : syracuseStep 2051963 = 3077945) B3077945
theorem B1363943 : Blo 908576 1363943 := bstep (se 1 (by rfl) ⟨1022957, by rfl⟩ : syracuseStep 1363943 = 2045915) B2045915
theorem B2052071 : Blo 908576 2052071 := bstep (se 1 (by rfl) ⟨1539053, by rfl⟩ : syracuseStep 2052071 = 3078107) B3078107
theorem B1364063 : Blo 908576 1364063 := bstep (se 1 (by rfl) ⟨1023047, by rfl⟩ : syracuseStep 1364063 = 2046095) B2046095
theorem B1364075 : Blo 908576 1364075 := bstep (se 1 (by rfl) ⟨1023056, by rfl⟩ : syracuseStep 1364075 = 2046113) B2046113
theorem B8310937 : Blo 908576 8310937 := bstep (se 2 (by rfl) ⟨3116601, by rfl⟩ : syracuseStep 8310937 = 6233203) B6233203
theorem B1364123 : Blo 908576 1364123 := bstep (se 1 (by rfl) ⟨1023092, by rfl⟩ : syracuseStep 1364123 = 2046185) B2046185
theorem B2052251 : Blo 908576 2052251 := bstep (se 1 (by rfl) ⟨1539188, by rfl⟩ : syracuseStep 2052251 = 3078377) B3078377
theorem B2052449 : Blo 908576 2052449 := bstep (se 2 (by rfl) ⟨769668, by rfl⟩ : syracuseStep 2052449 = 1539337) B1539337
theorem B2052539 : Blo 908576 2052539 := bstep (se 1 (by rfl) ⟨1539404, by rfl⟩ : syracuseStep 2052539 = 3078809) B3078809
theorem B1724905 : Blo 908576 1724905 := bstep (se 2 (by rfl) ⟨646839, by rfl⟩ : syracuseStep 1724905 = 1293679) B1293679
theorem B1364975 : Blo 908576 1364975 := bstep (se 1 (by rfl) ⟨1023731, by rfl⟩ : syracuseStep 1364975 = 2047463) B2047463
theorem B2184353 : Blo 908576 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B1365359 : Blo 908576 1365359 := bstep (se 1 (by rfl) ⟨1024019, by rfl⟩ : syracuseStep 1365359 = 2048039) B2048039
theorem B16864631 : Blo 908576 16864631 := bstep (se 1 (by rfl) ⟨12648473, by rfl⟩ : syracuseStep 16864631 = 25296947) B25296947
theorem B6575489 : Blo 908576 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B15553943 : Blo 908576 15553943 := bstep (se 1 (by rfl) ⟨11665457, by rfl⟩ : syracuseStep 15553943 = 23330915) B23330915
theorem B1365479 : Blo 908576 1365479 := bstep (se 1 (by rfl) ⟨1024109, by rfl⟩ : syracuseStep 1365479 = 2048219) B2048219
theorem B3888623 : Blo 908576 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B1365641 : Blo 908576 1365641 := bstep (se 2 (by rfl) ⟨512115, by rfl⟩ : syracuseStep 1365641 = 1024231) B1024231
theorem B1365659 : Blo 908576 1365659 := bstep (se 1 (by rfl) ⟨1024244, by rfl⟩ : syracuseStep 1365659 = 2048489) B2048489
theorem B1365851 : Blo 908576 1365851 := bstep (se 1 (by rfl) ⟨1024388, by rfl⟩ : syracuseStep 1365851 = 2048777) B2048777
theorem B14767991 : Blo 908576 14767991 := bstep (se 1 (by rfl) ⟨11075993, by rfl⟩ : syracuseStep 14767991 = 22151987) B22151987
theorem B1366235 : Blo 908576 1366235 := bstep (se 1 (by rfl) ⟨1024676, by rfl⟩ : syracuseStep 1366235 = 2049353) B2049353
theorem B1726751 : Blo 908576 1726751 := bstep (se 1 (by rfl) ⟨1295063, by rfl⟩ : syracuseStep 1726751 = 2590127) B2590127
theorem B4151711 : Blo 908576 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B1366505 : Blo 908576 1366505 := bstep (se 2 (by rfl) ⟨512439, by rfl⟩ : syracuseStep 1366505 = 1024879) B1024879
theorem B1366895 : Blo 908576 1366895 := bstep (se 1 (by rfl) ⟨1025171, by rfl⟩ : syracuseStep 1366895 = 2050343) B2050343
theorem B1366907 : Blo 908576 1366907 := bstep (se 1 (by rfl) ⟨1025180, by rfl⟩ : syracuseStep 1366907 = 2050361) B2050361
theorem B1039451 : Blo 908576 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B908615 : Blo 908576 908615 := bstep (se 1 (by rfl) ⟨681461, by rfl⟩ : syracuseStep 908615 = 1362923) B1362923
theorem B3890537 : Blo 908576 3890537 := bstep (se 2 (by rfl) ⟨1458951, by rfl⟩ : syracuseStep 3890537 = 2917903) B2917903
theorem B908751 : Blo 908576 908751 := bstep (se 1 (by rfl) ⟨681563, by rfl⟩ : syracuseStep 908751 = 1363127) B1363127
theorem B3071465 : Blo 908576 3071465 := bstep (se 2 (by rfl) ⟨1151799, by rfl⟩ : syracuseStep 3071465 = 2303599) B2303599
theorem B908911 : Blo 908576 908911 := bstep (se 1 (by rfl) ⟨681683, by rfl⟩ : syracuseStep 908911 = 1363367) B1363367
theorem B908967 : Blo 908576 908967 := bstep (se 1 (by rfl) ⟨681725, by rfl⟩ : syracuseStep 908967 = 1363451) B1363451
theorem B1367771 : Blo 908576 1367771 := bstep (se 1 (by rfl) ⟨1025828, by rfl⟩ : syracuseStep 1367771 = 2051657) B2051657
theorem B909031 : Blo 908576 909031 := bstep (se 1 (by rfl) ⟨681773, by rfl⟩ : syracuseStep 909031 = 1363547) B1363547
theorem B909087 : Blo 908576 909087 := bstep (se 1 (by rfl) ⟨681815, by rfl⟩ : syracuseStep 909087 = 1363631) B1363631
theorem B1728353 : Blo 908576 1728353 := bstep (se 2 (by rfl) ⟨648132, by rfl⟩ : syracuseStep 1728353 = 1296265) B1296265
theorem B909167 : Blo 908576 909167 := bstep (se 1 (by rfl) ⟨681875, by rfl⟩ : syracuseStep 909167 = 1363751) B1363751
theorem B909223 : Blo 908576 909223 := bstep (se 1 (by rfl) ⟨681917, by rfl⟩ : syracuseStep 909223 = 1363835) B1363835
theorem B1368041 : Blo 908576 1368041 := bstep (se 2 (by rfl) ⟨513015, by rfl⟩ : syracuseStep 1368041 = 1026031) B1026031
theorem B909503 : Blo 908576 909503 := bstep (se 1 (by rfl) ⟨682127, by rfl⟩ : syracuseStep 909503 = 1364255) B1364255
theorem B909519 : Blo 908576 909519 := bstep (se 1 (by rfl) ⟨682139, by rfl⟩ : syracuseStep 909519 = 1364279) B1364279
theorem B909567 : Blo 908576 909567 := bstep (se 1 (by rfl) ⟨682175, by rfl⟩ : syracuseStep 909567 = 1364351) B1364351
theorem B909615 : Blo 908576 909615 := bstep (se 1 (by rfl) ⟨682211, by rfl⟩ : syracuseStep 909615 = 1364423) B1364423
theorem B4383143 : Blo 908576 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B909851 : Blo 908576 909851 := bstep (se 1 (by rfl) ⟨682388, by rfl⟩ : syracuseStep 909851 = 1364777) B1364777
theorem B909855 : Blo 908576 909855 := bstep (se 1 (by rfl) ⟨682391, by rfl⟩ : syracuseStep 909855 = 1364783) B1364783
theorem B6218291 : Blo 908576 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B909935 : Blo 908576 909935 := bstep (se 1 (by rfl) ⟨682451, by rfl⟩ : syracuseStep 909935 = 1364903) B1364903
theorem B909991 : Blo 908576 909991 := bstep (se 1 (by rfl) ⟨682493, by rfl⟩ : syracuseStep 909991 = 1364987) B1364987
theorem B1368743 : Blo 908576 1368743 := bstep (se 1 (by rfl) ⟨1026557, by rfl⟩ : syracuseStep 1368743 = 2053115) B2053115
theorem B910031 : Blo 908576 910031 := bstep (se 1 (by rfl) ⟨682523, by rfl⟩ : syracuseStep 910031 = 1365047) B1365047
theorem B4383467 : Blo 908576 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B910111 : Blo 908576 910111 := bstep (se 1 (by rfl) ⟨682583, by rfl⟩ : syracuseStep 910111 = 1365167) B1365167
theorem B2188063 : Blo 908576 2188063 := bstep (se 1 (by rfl) ⟨1641047, by rfl⟩ : syracuseStep 2188063 = 3282095) B3282095
theorem B1368863 : Blo 908576 1368863 := bstep (se 1 (by rfl) ⟨1026647, by rfl⟩ : syracuseStep 1368863 = 2053295) B2053295
theorem B910383 : Blo 908576 910383 := bstep (se 1 (by rfl) ⟨682787, by rfl⟩ : syracuseStep 910383 = 1365575) B1365575
theorem B1729583 : Blo 908576 1729583 := bstep (se 1 (by rfl) ⟨1297187, by rfl⟩ : syracuseStep 1729583 = 2594375) B2594375
theorem B910447 : Blo 908576 910447 := bstep (se 1 (by rfl) ⟨682835, by rfl⟩ : syracuseStep 910447 = 1365671) B1365671
theorem B910503 : Blo 908576 910503 := bstep (se 1 (by rfl) ⟨682877, by rfl⟩ : syracuseStep 910503 = 1365755) B1365755
theorem B910527 : Blo 908576 910527 := bstep (se 1 (by rfl) ⟨682895, by rfl⟩ : syracuseStep 910527 = 1365791) B1365791
theorem B910559 : Blo 908576 910559 := bstep (se 1 (by rfl) ⟨682919, by rfl⟩ : syracuseStep 910559 = 1365839) B1365839
theorem B1729811 : Blo 908576 1729811 := bstep (se 1 (by rfl) ⟨1297358, by rfl⟩ : syracuseStep 1729811 = 2594717) B2594717
theorem B910639 : Blo 908576 910639 := bstep (se 1 (by rfl) ⟨682979, by rfl⟩ : syracuseStep 910639 = 1365959) B1365959
theorem B1729849 : Blo 908576 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B1533431 : Blo 908576 1533431 := bstep (se 1 (by rfl) ⟨1150073, by rfl⟩ : syracuseStep 1533431 = 2300147) B2300147
theorem B910875 : Blo 908576 910875 := bstep (se 1 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 910875 = 1366313) B1366313
theorem B910879 : Blo 908576 910879 := bstep (se 1 (by rfl) ⟨683159, by rfl⟩ : syracuseStep 910879 = 1366319) B1366319
theorem B6907517 : Blo 908576 6907517 := bstep (se 3 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 6907517 = 2590319) B2590319
theorem B911039 : Blo 908576 911039 := bstep (se 1 (by rfl) ⟨683279, by rfl⟩ : syracuseStep 911039 = 1366559) B1366559
theorem B3073787 : Blo 908576 3073787 := bstep (se 1 (by rfl) ⟨2305340, by rfl⟩ : syracuseStep 3073787 = 4610681) B4610681
theorem B1107751 : Blo 908576 1107751 := bstep (se 1 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 1107751 = 1661627) B1661627
theorem B12609377 : Blo 908576 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B3073949 : Blo 908576 3073949 := bstep (se 3 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 3073949 = 1152731) B1152731
theorem B911295 : Blo 908576 911295 := bstep (se 1 (by rfl) ⟨683471, by rfl⟩ : syracuseStep 911295 = 1366943) B1366943
theorem B911327 : Blo 908576 911327 := bstep (se 1 (by rfl) ⟨683495, by rfl⟩ : syracuseStep 911327 = 1366991) B1366991
theorem B911387 : Blo 908576 911387 := bstep (se 1 (by rfl) ⟨683540, by rfl⟩ : syracuseStep 911387 = 1367081) B1367081
theorem B911391 : Blo 908576 911391 := bstep (se 1 (by rfl) ⟨683543, by rfl⟩ : syracuseStep 911391 = 1367087) B1367087
theorem B911407 : Blo 908576 911407 := bstep (se 1 (by rfl) ⟨683555, by rfl⟩ : syracuseStep 911407 = 1367111) B1367111
theorem B911583 : Blo 908576 911583 := bstep (se 1 (by rfl) ⟨683687, by rfl⟩ : syracuseStep 911583 = 1367375) B1367375
theorem B4614407 : Blo 908576 4614407 := bstep (se 1 (by rfl) ⟨3460805, by rfl⟩ : syracuseStep 4614407 = 6921611) B6921611
theorem B911643 : Blo 908576 911643 := bstep (se 1 (by rfl) ⟨683732, by rfl⟩ : syracuseStep 911643 = 1367465) B1367465
theorem B911743 : Blo 908576 911743 := bstep (se 1 (by rfl) ⟨683807, by rfl⟩ : syracuseStep 911743 = 1367615) B1367615
theorem B1534457 : Blo 908576 1534457 := bstep (se 2 (by rfl) ⟨575421, by rfl⟩ : syracuseStep 1534457 = 1150843) B1150843
theorem B1534511 : Blo 908576 1534511 := bstep (se 1 (by rfl) ⟨1150883, by rfl⟩ : syracuseStep 1534511 = 2301767) B2301767
theorem B911919 : Blo 908576 911919 := bstep (se 1 (by rfl) ⟨683939, by rfl⟩ : syracuseStep 911919 = 1367879) B1367879
theorem B911975 : Blo 908576 911975 := bstep (se 1 (by rfl) ⟨683981, by rfl⟩ : syracuseStep 911975 = 1367963) B1367963
theorem B1534727 : Blo 908576 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B1534943 : Blo 908576 1534943 := bstep (se 1 (by rfl) ⟨1151207, by rfl⟩ : syracuseStep 1534943 = 2302415) B2302415
theorem B912351 : Blo 908576 912351 := bstep (se 1 (by rfl) ⟨684263, by rfl⟩ : syracuseStep 912351 = 1368527) B1368527
theorem B912379 : Blo 908576 912379 := bstep (se 1 (by rfl) ⟨684284, by rfl⟩ : syracuseStep 912379 = 1368569) B1368569
theorem B6908975 : Blo 908576 6908975 := bstep (se 1 (by rfl) ⟨5181731, by rfl⟩ : syracuseStep 6908975 = 10363463) B10363463
theorem B912447 : Blo 908576 912447 := bstep (se 1 (by rfl) ⟨684335, by rfl⟩ : syracuseStep 912447 = 1368671) B1368671
theorem B1535287 : Blo 908576 1535287 := bstep (se 1 (by rfl) ⟨1151465, by rfl⟩ : syracuseStep 1535287 = 2302931) B2302931
theorem B6221161 : Blo 908576 6221161 := bstep (se 2 (by rfl) ⟨2332935, by rfl⟩ : syracuseStep 6221161 = 4665871) B4665871
theorem B1732279 : Blo 908576 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B15527699 : Blo 908576 15527699 := bstep (se 1 (by rfl) ⟨11645774, by rfl⟩ : syracuseStep 15527699 = 23291549) B23291549
theorem B1535807 : Blo 908576 1535807 := bstep (se 1 (by rfl) ⟨1151855, by rfl⟩ : syracuseStep 1535807 = 2303711) B2303711
theorem B1535881 : Blo 908576 1535881 := bstep (se 2 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 1535881 = 1151911) B1151911
theorem B19656755 : Blo 908576 19656755 := bstep (se 1 (by rfl) ⟨14742566, by rfl⟩ : syracuseStep 19656755 = 29485133) B29485133
theorem B15790139 : Blo 908576 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B3895937 : Blo 908576 3895937 := bstep (se 2 (by rfl) ⟨1460976, by rfl⟩ : syracuseStep 3895937 = 2921953) B2921953
theorem B4617323 : Blo 908576 4617323 := bstep (se 1 (by rfl) ⟨3462992, by rfl⟩ : syracuseStep 4617323 = 6925985) B6925985
theorem B3077405 : Blo 908576 3077405 := bstep (se 3 (by rfl) ⟨577013, by rfl⟩ : syracuseStep 3077405 = 1154027) B1154027
theorem B1537447 : Blo 908576 1537447 := bstep (se 1 (by rfl) ⟨1153085, by rfl⟩ : syracuseStep 1537447 = 2306171) B2306171
theorem B17036867 : Blo 908576 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B7108667 : Blo 908576 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B4159835 : Blo 908576 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B8321453 : Blo 908576 8321453 := bstep (se 3 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 8321453 = 3120545) B3120545
theorem B13105597 : Blo 908576 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B3897953 : Blo 908576 3897953 := bstep (se 2 (by rfl) ⟨1461732, by rfl⟩ : syracuseStep 3897953 = 2923465) B2923465
theorem B10517239 : Blo 908576 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B66321665 : Blo 908576 66321665 := bstep (se 2 (by rfl) ⟨24870624, by rfl⟩ : syracuseStep 66321665 = 49741249) B49741249
theorem B1539499 : Blo 908576 1539499 := bstep (se 1 (by rfl) ⟨1154624, by rfl⟩ : syracuseStep 1539499 = 2309249) B2309249
theorem B1539695 : Blo 908576 1539695 := bstep (se 1 (by rfl) ⟨1154771, by rfl⟩ : syracuseStep 1539695 = 2309543) B2309543
theorem B2917417 : Blo 908576 2917417 := bstep (se 2 (by rfl) ⟨1094031, by rfl⟩ : syracuseStep 2917417 = 2188063) B2188063
theorem B1311815 : Blo 908576 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B2589887 : Blo 908576 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B2917595 : Blo 908576 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B24970463 : Blo 908576 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B8324657 : Blo 908576 8324657 := bstep (se 2 (by rfl) ⟨3121746, by rfl⟩ : syracuseStep 8324657 = 6243493) B6243493
theorem B6064283 : Blo 908576 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B2459983 : Blo 908576 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B1477001 : Blo 908576 1477001 := bstep (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) B1107751
theorem B25266761 : Blo 908576 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B37882691 : Blo 908576 37882691 := bstep (se 1 (by rfl) ⟨28412018, by rfl⟩ : syracuseStep 37882691 = 56824037) B56824037
theorem B11243087 : Blo 908576 11243087 := bstep (se 1 (by rfl) ⟨8432315, by rfl⟩ : syracuseStep 11243087 = 16864631) B16864631
theorem B2592415 : Blo 908576 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B1151167 : Blo 908576 1151167 := bstep (se 1 (by rfl) ⟨863375, by rfl⟩ : syracuseStep 1151167 = 1726751) B1726751
theorem B5247443 : Blo 908576 5247443 := bstep (se 1 (by rfl) ⟨3935582, by rfl⟩ : syracuseStep 5247443 = 7871165) B7871165
theorem B8294881 : Blo 908576 8294881 := bstep (se 2 (by rfl) ⟨3110580, by rfl⟩ : syracuseStep 8294881 = 6221161) B6221161
theorem B1643195 : Blo 908576 1643195 := bstep (se 1 (by rfl) ⟨1232396, by rfl⟩ : syracuseStep 1643195 = 2464793) B2464793
theorem B2593691 : Blo 908576 2593691 := bstep (se 1 (by rfl) ⟨1945268, by rfl⟩ : syracuseStep 2593691 = 3890537) B3890537
theorem B1152235 : Blo 908576 1152235 := bstep (se 1 (by rfl) ⟨864176, by rfl⟩ : syracuseStep 1152235 = 1728353) B1728353
theorem B11081249 : Blo 908576 11081249 := bstep (se 2 (by rfl) ⟨4155468, by rfl⟩ : syracuseStep 11081249 = 8310937) B8310937
theorem B2922095 : Blo 908576 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B2922311 : Blo 908576 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B2299873 : Blo 908576 2299873 := bstep (se 2 (by rfl) ⟨862452, by rfl⟩ : syracuseStep 2299873 = 1724905) B1724905
theorem B1153055 : Blo 908576 1153055 := bstep (se 1 (by rfl) ⟨864791, by rfl⟩ : syracuseStep 1153055 = 1729583) B1729583
theorem B2300015 : Blo 908576 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B1153207 : Blo 908576 1153207 := bstep (se 1 (by rfl) ⟨864905, by rfl⟩ : syracuseStep 1153207 = 1729811) B1729811
theorem B1022287 : Blo 908576 1022287 := bstep (se 1 (by rfl) ⟨766715, by rfl⟩ : syracuseStep 1022287 = 1533431) B1533431
theorem B2595833 : Blo 908576 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B1022971 : Blo 908576 1022971 := bstep (se 1 (by rfl) ⟨767228, by rfl⟩ : syracuseStep 1022971 = 1534457) B1534457
theorem B1023007 : Blo 908576 1023007 := bstep (se 1 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 1023007 = 1534511) B1534511
theorem B1023151 : Blo 908576 1023151 := bstep (se 1 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 1023151 = 1534727) B1534727
theorem B1023295 : Blo 908576 1023295 := bstep (se 1 (by rfl) ⟨767471, by rfl⟩ : syracuseStep 1023295 = 1534943) B1534943
theorem B1023871 : Blo 908576 1023871 := bstep (se 1 (by rfl) ⟨767903, by rfl⟩ : syracuseStep 1023871 = 1535807) B1535807
theorem B9838579 : Blo 908576 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B10526759 : Blo 908576 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B2597177 : Blo 908576 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B2597291 : Blo 908576 2597291 := bstep (se 1 (by rfl) ⟨1947968, by rfl⟩ : syracuseStep 2597291 = 3895937) B3895937
theorem B17474129 : Blo 908576 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B5186267 : Blo 908576 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B4924637 : Blo 908576 4924637 := bstep (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) B1846739
theorem B5547635 : Blo 908576 5547635 := bstep (se 1 (by rfl) ⟨4160726, by rfl⟩ : syracuseStep 5547635 = 8321453) B8321453
theorem B11675299 : Blo 908576 11675299 := bstep (se 1 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 11675299 = 17512949) B17512949
theorem B2598635 : Blo 908576 2598635 := bstep (se 1 (by rfl) ⟨1948976, by rfl⟩ : syracuseStep 2598635 = 3897953) B3897953
theorem B44214443 : Blo 908576 44214443 := bstep (se 1 (by rfl) ⟨33160832, by rfl⟩ : syracuseStep 44214443 = 66321665) B66321665
theorem B1026463 : Blo 908576 1026463 := bstep (se 1 (by rfl) ⟨769847, by rfl⟩ : syracuseStep 1026463 = 1539695) B1539695
theorem B3287471 : Blo 908576 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B5253907 : Blo 908576 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B11676635 : Blo 908576 11676635 := bstep (se 1 (by rfl) ⟨8757476, by rfl⟩ : syracuseStep 11676635 = 17514953) B17514953
theorem B3451967 : Blo 908576 3451967 := bstep (se 1 (by rfl) ⟨2588975, by rfl⟩ : syracuseStep 3451967 = 5177951) B5177951
theorem B5189183 : Blo 908576 5189183 := bstep (se 1 (by rfl) ⟨3891887, by rfl⟩ : syracuseStep 5189183 = 7783775) B7783775
theorem B8007497 : Blo 908576 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B2076779 : Blo 908576 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B2306465 : Blo 908576 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B2044583 : Blo 908576 2044583 := bstep (se 1 (by rfl) ⟨1533437, by rfl⟩ : syracuseStep 2044583 = 3066875) B3066875
theorem B1946423 : Blo 908576 1946423 := bstep (se 1 (by rfl) ⟨1459817, by rfl⟩ : syracuseStep 1946423 = 2919635) B2919635
theorem B1749919 : Blo 908576 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B4929133 : Blo 908576 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B14005993 : Blo 908576 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1456235 : Blo 908576 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B10369295 : Blo 908576 10369295 := bstep (se 1 (by rfl) ⟨7776971, by rfl⟩ : syracuseStep 10369295 = 15553943) B15553943
theorem B3455369 : Blo 908576 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B2079287 : Blo 908576 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B9845327 : Blo 908576 9845327 := bstep (se 1 (by rfl) ⟨7383995, by rfl⟩ : syracuseStep 9845327 = 14767991) B14767991
theorem B2767807 : Blo 908576 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B4602905 : Blo 908576 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B2047049 : Blo 908576 2047049 := bstep (se 2 (by rfl) ⟨767643, by rfl⟩ : syracuseStep 2047049 = 1535287) B1535287
theorem B2309705 : Blo 908576 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B2047643 : Blo 908576 2047643 := bstep (se 1 (by rfl) ⟨1535732, by rfl⟩ : syracuseStep 2047643 = 3071465) B3071465
theorem B2047841 : Blo 908576 2047841 := bstep (se 2 (by rfl) ⟨767940, by rfl⟩ : syracuseStep 2047841 = 1535881) B1535881
theorem B17481581 : Blo 908576 17481581 := bstep (se 3 (by rfl) ⟨3277796, by rfl⟩ : syracuseStep 17481581 = 6555593) B6555593
theorem B11681657 : Blo 908576 11681657 := bstep (se 2 (by rfl) ⟨4380621, by rfl⟩ : syracuseStep 11681657 = 8761243) B8761243
theorem B7389161 : Blo 908576 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B4145527 : Blo 908576 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B1229563 : Blo 908576 1229563 := bstep (se 1 (by rfl) ⟨922172, by rfl⟩ : syracuseStep 1229563 = 1844345) B1844345
theorem B3457799 : Blo 908576 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B4605011 : Blo 908576 4605011 := bstep (se 1 (by rfl) ⟨3453758, by rfl⟩ : syracuseStep 4605011 = 6907517) B6907517
theorem B2049191 : Blo 908576 2049191 := bstep (se 1 (by rfl) ⟨1536893, by rfl⟩ : syracuseStep 2049191 = 3073787) B3073787
theorem B8406251 : Blo 908576 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B2049299 : Blo 908576 2049299 := bstep (se 1 (by rfl) ⟨1536974, by rfl⟩ : syracuseStep 2049299 = 3073949) B3073949
theorem B2049929 : Blo 908576 2049929 := bstep (se 2 (by rfl) ⟨768723, by rfl⟩ : syracuseStep 2049929 = 1537447) B1537447
theorem B4605983 : Blo 908576 4605983 := bstep (se 1 (by rfl) ⟨3454487, by rfl⟩ : syracuseStep 4605983 = 6908975) B6908975
theorem B4377007 : Blo 908576 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B5196221 : Blo 908576 5196221 := bstep (se 3 (by rfl) ⟨974291, by rfl⟩ : syracuseStep 5196221 = 1948583) B1948583
theorem B2771869 : Blo 908576 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B1362911 : Blo 908576 1362911 := bstep (se 1 (by rfl) ⟨1022183, by rfl⟩ : syracuseStep 1362911 = 2044367) B2044367
theorem B89967611 : Blo 908576 89967611 := bstep (se 1 (by rfl) ⟨67475708, by rfl⟩ : syracuseStep 89967611 = 134951417) B134951417
theorem B1363355 : Blo 908576 1363355 := bstep (se 1 (by rfl) ⟨1022516, by rfl⟩ : syracuseStep 1363355 = 2045033) B2045033
theorem B3067307 : Blo 908576 3067307 := bstep (se 1 (by rfl) ⟨2300480, by rfl⟩ : syracuseStep 3067307 = 4600961) B4600961
theorem B2051603 : Blo 908576 2051603 := bstep (se 1 (by rfl) ⟨1538702, by rfl⟩ : syracuseStep 2051603 = 3077405) B3077405
theorem B11357911 : Blo 908576 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B1363721 : Blo 908576 1363721 := bstep (se 2 (by rfl) ⟨511395, by rfl⟩ : syracuseStep 1363721 = 1022791) B1022791
theorem B1363775 : Blo 908576 1363775 := bstep (se 1 (by rfl) ⟨1022831, by rfl⟩ : syracuseStep 1363775 = 2045663) B2045663
theorem B3067847 : Blo 908576 3067847 := bstep (se 1 (by rfl) ⟨2300885, by rfl⟩ : syracuseStep 3067847 = 4601771) B4601771
theorem B4739111 : Blo 908576 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B1364015 : Blo 908576 1364015 := bstep (se 1 (by rfl) ⟨1023011, by rfl⟩ : syracuseStep 1364015 = 2046023) B2046023
theorem B1233023 : Blo 908576 1233023 := bstep (se 1 (by rfl) ⟨924767, by rfl⟩ : syracuseStep 1233023 = 1849535) B1849535
theorem B2773223 : Blo 908576 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B1364459 : Blo 908576 1364459 := bstep (se 1 (by rfl) ⟨1023344, by rfl⟩ : syracuseStep 1364459 = 2046689) B2046689
theorem B2052665 : Blo 908576 2052665 := bstep (se 2 (by rfl) ⟨769749, by rfl⟩ : syracuseStep 2052665 = 1539499) B1539499
theorem B3560009 : Blo 908576 3560009 := bstep (se 2 (by rfl) ⟨1335003, by rfl⟩ : syracuseStep 3560009 = 2670007) B2670007
theorem B1364585 : Blo 908576 1364585 := bstep (se 2 (by rfl) ⟨511719, by rfl⟩ : syracuseStep 1364585 = 1023439) B1023439
theorem B1364591 : Blo 908576 1364591 := bstep (se 1 (by rfl) ⟨1023443, by rfl⟩ : syracuseStep 1364591 = 2046887) B2046887
theorem B1364711 : Blo 908576 1364711 := bstep (se 1 (by rfl) ⟨1023533, by rfl⟩ : syracuseStep 1364711 = 2047067) B2047067
theorem B3461899 : Blo 908576 3461899 := bstep (se 1 (by rfl) ⟨2596424, by rfl⟩ : syracuseStep 3461899 = 5192849) B5192849
theorem B1364873 : Blo 908576 1364873 := bstep (se 2 (by rfl) ⟨511827, by rfl⟩ : syracuseStep 1364873 = 1023655) B1023655
theorem B4379777 : Blo 908576 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B1365215 : Blo 908576 1365215 := bstep (se 1 (by rfl) ⟨1023911, by rfl⟩ : syracuseStep 1365215 = 2047823) B2047823
theorem B1365257 : Blo 908576 1365257 := bstep (se 2 (by rfl) ⟨511971, by rfl⟩ : syracuseStep 1365257 = 1023943) B1023943
theorem B10376585 : Blo 908576 10376585 := bstep (se 2 (by rfl) ⟨3891219, by rfl⟩ : syracuseStep 10376585 = 7782439) B7782439
theorem B3692063 : Blo 908576 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B1365695 : Blo 908576 1365695 := bstep (se 1 (by rfl) ⟨1024271, by rfl⟩ : syracuseStep 1365695 = 2048543) B2048543
theorem B1365737 : Blo 908576 1365737 := bstep (se 2 (by rfl) ⟨512151, by rfl⟩ : syracuseStep 1365737 = 1024303) B1024303
theorem B1365743 : Blo 908576 1365743 := bstep (se 1 (by rfl) ⟨1024307, by rfl⟩ : syracuseStep 1365743 = 2048615) B2048615
theorem B3069683 : Blo 908576 3069683 := bstep (se 1 (by rfl) ⟨2302262, by rfl⟩ : syracuseStep 3069683 = 4604525) B4604525
theorem B3069737 : Blo 908576 3069737 := bstep (se 2 (by rfl) ⟨1151151, by rfl⟩ : syracuseStep 3069737 = 2302303) B2302303
theorem B168450191 : Blo 908576 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B4610195 : Blo 908576 4610195 := bstep (se 1 (by rfl) ⟨3457646, by rfl⟩ : syracuseStep 4610195 = 6915293) B6915293
theorem B1366247 : Blo 908576 1366247 := bstep (se 1 (by rfl) ⟨1024685, by rfl⟩ : syracuseStep 1366247 = 2049371) B2049371
theorem B1366427 : Blo 908576 1366427 := bstep (se 1 (by rfl) ⟨1024820, by rfl⟩ : syracuseStep 1366427 = 2049641) B2049641
theorem B1366823 : Blo 908576 1366823 := bstep (se 1 (by rfl) ⟨1025117, by rfl⟩ : syracuseStep 1366823 = 2050235) B2050235
theorem B1366847 : Blo 908576 1366847 := bstep (se 1 (by rfl) ⟨1025135, by rfl⟩ : syracuseStep 1366847 = 2050271) B2050271
theorem B1727335 : Blo 908576 1727335 := bstep (se 1 (by rfl) ⟨1295501, by rfl⟩ : syracuseStep 1727335 = 2591003) B2591003
theorem B4152259 : Blo 908576 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B7789547 : Blo 908576 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B1367147 : Blo 908576 1367147 := bstep (se 1 (by rfl) ⟨1025360, by rfl⟩ : syracuseStep 1367147 = 2050721) B2050721
theorem B1367291 : Blo 908576 1367291 := bstep (se 1 (by rfl) ⟨1025468, by rfl⟩ : syracuseStep 1367291 = 2050937) B2050937
theorem B3071303 : Blo 908576 3071303 := bstep (se 1 (by rfl) ⟨2303477, by rfl⟩ : syracuseStep 3071303 = 4606955) B4606955
theorem B1367387 : Blo 908576 1367387 := bstep (se 1 (by rfl) ⟨1025540, by rfl⟩ : syracuseStep 1367387 = 2051081) B2051081
theorem B1367417 : Blo 908576 1367417 := bstep (se 2 (by rfl) ⟨512781, by rfl⟩ : syracuseStep 1367417 = 1025563) B1025563
theorem B908671 : Blo 908576 908671 := bstep (se 1 (by rfl) ⟨681503, by rfl⟩ : syracuseStep 908671 = 1363007) B1363007
theorem B1367423 : Blo 908576 1367423 := bstep (se 1 (by rfl) ⟨1025567, by rfl⟩ : syracuseStep 1367423 = 2051135) B2051135
theorem B45505925 : Blo 908576 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B909039 : Blo 908576 909039 := bstep (se 1 (by rfl) ⟨681779, by rfl⟩ : syracuseStep 909039 = 1363559) B1363559
theorem B1367975 : Blo 908576 1367975 := bstep (se 1 (by rfl) ⟨1025981, by rfl⟩ : syracuseStep 1367975 = 2051963) B2051963
theorem B909295 : Blo 908576 909295 := bstep (se 1 (by rfl) ⟨681971, by rfl⟩ : syracuseStep 909295 = 1363943) B1363943
theorem B1368047 : Blo 908576 1368047 := bstep (se 1 (by rfl) ⟨1026035, by rfl⟩ : syracuseStep 1368047 = 2052071) B2052071
theorem B9855017 : Blo 908576 9855017 := bstep (se 2 (by rfl) ⟨3695631, by rfl⟩ : syracuseStep 9855017 = 7391263) B7391263
theorem B909375 : Blo 908576 909375 := bstep (se 1 (by rfl) ⟨682031, by rfl⟩ : syracuseStep 909375 = 1364063) B1364063
theorem B909383 : Blo 908576 909383 := bstep (se 1 (by rfl) ⟨682037, by rfl⟩ : syracuseStep 909383 = 1364075) B1364075
theorem B909415 : Blo 908576 909415 := bstep (se 1 (by rfl) ⟨682061, by rfl⟩ : syracuseStep 909415 = 1364123) B1364123
theorem B1368167 : Blo 908576 1368167 := bstep (se 1 (by rfl) ⟨1026125, by rfl⟩ : syracuseStep 1368167 = 2052251) B2052251
theorem B6906059 : Blo 908576 6906059 := bstep (se 1 (by rfl) ⟨5179544, by rfl⟩ : syracuseStep 6906059 = 10359089) B10359089
theorem B1368299 : Blo 908576 1368299 := bstep (se 1 (by rfl) ⟨1026224, by rfl⟩ : syracuseStep 1368299 = 2052449) B2052449
theorem B1368359 : Blo 908576 1368359 := bstep (se 1 (by rfl) ⟨1026269, by rfl⟩ : syracuseStep 1368359 = 2052539) B2052539
theorem B909983 : Blo 908576 909983 := bstep (se 1 (by rfl) ⟨682487, by rfl⟩ : syracuseStep 909983 = 1364975) B1364975
theorem B1368809 : Blo 908576 1368809 := bstep (se 2 (by rfl) ⟨513303, by rfl⟩ : syracuseStep 1368809 = 1026607) B1026607
theorem B910239 : Blo 908576 910239 := bstep (se 1 (by rfl) ⟨682679, by rfl⟩ : syracuseStep 910239 = 1365359) B1365359
theorem B4383659 : Blo 908576 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B910319 : Blo 908576 910319 := bstep (se 1 (by rfl) ⟨682739, by rfl⟩ : syracuseStep 910319 = 1365479) B1365479
theorem B910427 : Blo 908576 910427 := bstep (se 1 (by rfl) ⟨682820, by rfl⟩ : syracuseStep 910427 = 1365641) B1365641
theorem B910439 : Blo 908576 910439 := bstep (se 1 (by rfl) ⟨682829, by rfl⟩ : syracuseStep 910439 = 1365659) B1365659
theorem B910567 : Blo 908576 910567 := bstep (se 1 (by rfl) ⟨682925, by rfl⟩ : syracuseStep 910567 = 1365851) B1365851
theorem B910823 : Blo 908576 910823 := bstep (se 1 (by rfl) ⟨683117, by rfl⟩ : syracuseStep 910823 = 1366235) B1366235
theorem B911003 : Blo 908576 911003 := bstep (se 1 (by rfl) ⟨683252, by rfl⟩ : syracuseStep 911003 = 1366505) B1366505
theorem B12609409 : Blo 908576 12609409 := bstep (se 2 (by rfl) ⟨4728528, by rfl⟩ : syracuseStep 12609409 = 9457057) B9457057
theorem B911263 : Blo 908576 911263 := bstep (se 1 (by rfl) ⟨683447, by rfl⟩ : syracuseStep 911263 = 1366895) B1366895
theorem B1533863 : Blo 908576 1533863 := bstep (se 1 (by rfl) ⟨1150397, by rfl⟩ : syracuseStep 1533863 = 2300795) B2300795
theorem B911271 : Blo 908576 911271 := bstep (se 1 (by rfl) ⟨683453, by rfl⟩ : syracuseStep 911271 = 1366907) B1366907
theorem B10643507 : Blo 908576 10643507 := bstep (se 1 (by rfl) ⟨7982630, by rfl⟩ : syracuseStep 10643507 = 15965261) B15965261
theorem B911847 : Blo 908576 911847 := bstep (se 1 (by rfl) ⟨683885, by rfl⟩ : syracuseStep 911847 = 1367771) B1367771
theorem B1534619 : Blo 908576 1534619 := bstep (se 1 (by rfl) ⟨1150964, by rfl⟩ : syracuseStep 1534619 = 2301929) B2301929
theorem B912027 : Blo 908576 912027 := bstep (se 1 (by rfl) ⟨684020, by rfl⟩ : syracuseStep 912027 = 1368041) B1368041
theorem B912495 : Blo 908576 912495 := bstep (se 1 (by rfl) ⟨684371, by rfl⟩ : syracuseStep 912495 = 1368743) B1368743
theorem B912575 : Blo 908576 912575 := bstep (se 1 (by rfl) ⟨684431, by rfl⟩ : syracuseStep 912575 = 1368863) B1368863
theorem B1535591 : Blo 908576 1535591 := bstep (se 1 (by rfl) ⟨1151693, by rfl⟩ : syracuseStep 1535591 = 2303387) B2303387
theorem B3076271 : Blo 908576 3076271 := bstep (se 1 (by rfl) ⟨2307203, by rfl⟩ : syracuseStep 3076271 = 4614407) B4614407
theorem B2191579 : Blo 908576 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B17756873 : Blo 908576 17756873 := bstep (se 2 (by rfl) ⟨6658827, by rfl⟩ : syracuseStep 17756873 = 13317655) B13317655
theorem B3699751 : Blo 908576 3699751 := bstep (se 1 (by rfl) ⟨2774813, by rfl⟩ : syracuseStep 3699751 = 5549627) B5549627
theorem B4158535 : Blo 908576 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B10351799 : Blo 908576 10351799 := bstep (se 1 (by rfl) ⟨7763849, by rfl⟩ : syracuseStep 10351799 = 15527699) B15527699
theorem B13104503 : Blo 908576 13104503 := bstep (se 1 (by rfl) ⟨9828377, by rfl⟩ : syracuseStep 13104503 = 19656755) B19656755
theorem B6911891 : Blo 908576 6911891 := bstep (se 1 (by rfl) ⟨5183918, by rfl⟩ : syracuseStep 6911891 = 10367837) B10367837
theorem B1538075 : Blo 908576 1538075 := bstep (se 1 (by rfl) ⟨1153556, by rfl⟩ : syracuseStep 1538075 = 2307113) B2307113
theorem B3897371 : Blo 908576 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B1538095 : Blo 908576 1538095 := bstep (se 1 (by rfl) ⟨1153571, by rfl⟩ : syracuseStep 1538095 = 2307143) B2307143
theorem B3078215 : Blo 908576 3078215 := bstep (se 1 (by rfl) ⟨2308661, by rfl⟩ : syracuseStep 3078215 = 4617323) B4617323
theorem B14022985 : Blo 908576 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B4159993 : Blo 908576 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B2588087 : Blo 908576 2588087 := bstep (se 1 (by rfl) ⟨1941065, by rfl⟩ : syracuseStep 2588087 = 3882131) B3882131
theorem B5538077 : Blo 908576 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B16646975 : Blo 908576 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B5604167 : Blo 908576 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B16844507 : Blo 908576 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B15567065 : Blo 908576 15567065 := bstep (se 2 (by rfl) ⟨5837649, by rfl⟩ : syracuseStep 15567065 = 11675299) B11675299
theorem B16812545 : Blo 908576 16812545 := bstep (se 2 (by rfl) ⟨6304704, by rfl⟩ : syracuseStep 16812545 = 12609409) B12609409
theorem B3279977 : Blo 908576 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B2919851 : Blo 908576 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B6917723 : Blo 908576 6917723 := bstep (se 1 (by rfl) ⟨5188292, by rfl⟩ : syracuseStep 6917723 = 10376585) B10376585
theorem B2461375 : Blo 908576 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B6557669 : Blo 908576 6557669 := bstep (se 4 (by rfl) ⟨614781, by rfl⟩ : syracuseStep 6557669 = 1229563) B1229563
theorem B112300127 : Blo 908576 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B15143881 : Blo 908576 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B7017839 : Blo 908576 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B3283091 : Blo 908576 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B3938669 : Blo 908576 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B2333225 : Blo 908576 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B1022575 : Blo 908576 1022575 := bstep (se 1 (by rfl) ⟨766931, by rfl⟩ : syracuseStep 1022575 = 1533863) B1533863
theorem B5544713 : Blo 908576 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B26254205 : Blo 908576 26254205 := bstep (se 3 (by rfl) ⟨4922663, by rfl⟩ : syracuseStep 26254205 = 9845327) B9845327
theorem B1023079 : Blo 908576 1023079 := bstep (se 1 (by rfl) ⟨767309, by rfl⟩ : syracuseStep 1023079 = 1534619) B1534619
theorem B2301311 : Blo 908576 2301311 := bstep (se 1 (by rfl) ⟨1725983, by rfl⟩ : syracuseStep 2301311 = 3451967) B3451967
theorem B1023727 : Blo 908576 1023727 := bstep (se 1 (by rfl) ⟨767795, by rfl⟩ : syracuseStep 1023727 = 1535591) B1535591
theorem B11837915 : Blo 908576 11837915 := bstep (se 1 (by rfl) ⟨8878436, by rfl⟩ : syracuseStep 11837915 = 17756873) B17756873
theorem B5546657 : Blo 908576 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B2303113 : Blo 908576 2303113 := bstep (se 2 (by rfl) ⟨863667, by rfl⟩ : syracuseStep 2303113 = 1727335) B1727335
theorem B1025383 : Blo 908576 1025383 := bstep (se 1 (by rfl) ⟨769037, by rfl⟩ : syracuseStep 1025383 = 1538075) B1538075
theorem B2598247 : Blo 908576 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B2303579 : Blo 908576 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B1386191 : Blo 908576 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B13118105 : Blo 908576 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B4926107 : Blo 908576 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B3288061 : Blo 908576 3288061 := bstep (se 3 (by rfl) ⟨616511, by rfl⟩ : syracuseStep 3288061 = 1233023) B1233023
theorem B2305199 : Blo 908576 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B1945063 : Blo 908576 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B5549771 : Blo 908576 5549771 := bstep (se 1 (by rfl) ⟨4162328, by rfl⟩ : syracuseStep 5549771 = 8324657) B8324657
theorem B4042855 : Blo 908576 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B59978407 : Blo 908576 59978407 := bstep (se 1 (by rfl) ⟨44983805, by rfl⟩ : syracuseStep 59978407 = 89967611) B89967611
theorem B23344037 : Blo 908576 23344037 := bstep (se 4 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 23344037 = 4377007) B4377007
theorem B2044871 : Blo 908576 2044871 := bstep (se 1 (by rfl) ⟨1533653, by rfl⟩ : syracuseStep 2044871 = 3067307) B3067307
theorem B2045231 : Blo 908576 2045231 := bstep (se 1 (by rfl) ⟨1533923, by rfl⟩ : syracuseStep 2045231 = 3067847) B3067847
theorem B3159407 : Blo 908576 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1848815 : Blo 908576 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B1095463 : Blo 908576 1095463 := bstep (se 1 (by rfl) ⟨821597, by rfl⟩ : syracuseStep 1095463 = 1643195) B1643195
theorem B7387499 : Blo 908576 7387499 := bstep (se 1 (by rfl) ⟨5540624, by rfl⟩ : syracuseStep 7387499 = 11081249) B11081249
theorem B1948063 : Blo 908576 1948063 := bstep (se 1 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 1948063 = 2922095) B2922095
theorem B2046455 : Blo 908576 2046455 := bstep (se 1 (by rfl) ⟨1534841, by rfl⟩ : syracuseStep 2046455 = 3069683) B3069683
theorem B2046491 : Blo 908576 2046491 := bstep (se 1 (by rfl) ⟨1534868, by rfl⟩ : syracuseStep 2046491 = 3069737) B3069737
theorem B1948207 : Blo 908576 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B5193031 : Blo 908576 5193031 := bstep (se 1 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 5193031 = 7789547) B7789547
theorem B3456553 : Blo 908576 3456553 := bstep (se 2 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 3456553 = 2592415) B2592415
theorem B2047535 : Blo 908576 2047535 := bstep (se 1 (by rfl) ⟨1535651, by rfl⟩ : syracuseStep 2047535 = 3071303) B3071303
theorem B6570011 : Blo 908576 6570011 := bstep (se 1 (by rfl) ⟨4927508, by rfl⟩ : syracuseStep 6570011 = 9855017) B9855017
theorem B4604039 : Blo 908576 4604039 := bstep (se 1 (by rfl) ⟨3453029, by rfl⟩ : syracuseStep 4604039 = 6906059) B6906059
theorem B11649419 : Blo 908576 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B3457511 : Blo 908576 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B11059841 : Blo 908576 11059841 := bstep (se 2 (by rfl) ⟨4147440, by rfl⟩ : syracuseStep 11059841 = 8294881) B8294881
theorem B8766589 : Blo 908576 8766589 := bstep (se 3 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 8766589 = 3287471) B3287471
theorem B7095671 : Blo 908576 7095671 := bstep (se 1 (by rfl) ⟨5321753, by rfl⟩ : syracuseStep 7095671 = 10643507) B10643507
theorem B4933001 : Blo 908576 4933001 := bstep (se 2 (by rfl) ⟨1849875, by rfl⟩ : syracuseStep 4933001 = 3699751) B3699751
theorem B29476295 : Blo 908576 29476295 := bstep (se 1 (by rfl) ⟨22107221, by rfl⟩ : syracuseStep 29476295 = 44214443) B44214443
theorem B7784423 : Blo 908576 7784423 := bstep (se 1 (by rfl) ⟨5838317, by rfl⟩ : syracuseStep 7784423 = 11676635) B11676635
theorem B6572177 : Blo 908576 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B3459455 : Blo 908576 3459455 := bstep (se 1 (by rfl) ⟨2594591, by rfl⟩ : syracuseStep 3459455 = 5189183) B5189183
theorem B3066497 : Blo 908576 3066497 := bstep (se 2 (by rfl) ⟨1149936, by rfl⟩ : syracuseStep 3066497 = 2299873) B2299873
theorem B2050793 : Blo 908576 2050793 := bstep (se 2 (by rfl) ⟨769047, by rfl⟩ : syracuseStep 2050793 = 1538095) B1538095
theorem B2050847 : Blo 908576 2050847 := bstep (se 1 (by rfl) ⟨1538135, by rfl⟩ : syracuseStep 2050847 = 3076271) B3076271
theorem B18697313 : Blo 908576 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B1363049 : Blo 908576 1363049 := bstep (se 2 (by rfl) ⟨511143, by rfl⟩ : syracuseStep 1363049 = 1022287) B1022287
theorem B1363055 : Blo 908576 1363055 := bstep (se 1 (by rfl) ⟨1022291, by rfl⟩ : syracuseStep 1363055 = 2044583) B2044583
theorem B1297615 : Blo 908576 1297615 := bstep (se 1 (by rfl) ⟨973211, by rfl⟩ : syracuseStep 1297615 = 1946423) B1946423
theorem B6901199 : Blo 908576 6901199 := bstep (se 1 (by rfl) ⟨5175899, by rfl⟩ : syracuseStep 6901199 = 10351799) B10351799
theorem B8736335 : Blo 908576 8736335 := bstep (se 1 (by rfl) ⟨6552251, by rfl⟩ : syracuseStep 8736335 = 13104503) B13104503
theorem B3690409 : Blo 908576 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B4607927 : Blo 908576 4607927 := bstep (se 1 (by rfl) ⟨3455945, by rfl⟩ : syracuseStep 4607927 = 6911891) B6911891
theorem B1363961 : Blo 908576 1363961 := bstep (se 2 (by rfl) ⟨511485, by rfl⟩ : syracuseStep 1363961 = 1022971) B1022971
theorem B1364009 : Blo 908576 1364009 := bstep (se 2 (by rfl) ⟨511503, by rfl⟩ : syracuseStep 1364009 = 1023007) B1023007
theorem B2052143 : Blo 908576 2052143 := bstep (se 1 (by rfl) ⟨1539107, by rfl⟩ : syracuseStep 2052143 = 3078215) B3078215
theorem B970823 : Blo 908576 970823 := bstep (se 1 (by rfl) ⟨728117, by rfl⟩ : syracuseStep 970823 = 1456235) B1456235
theorem B1364201 : Blo 908576 1364201 := bstep (se 2 (by rfl) ⟨511575, by rfl⟩ : syracuseStep 1364201 = 1023151) B1023151
theorem B1364393 : Blo 908576 1364393 := bstep (se 2 (by rfl) ⟨511647, by rfl⟩ : syracuseStep 1364393 = 1023295) B1023295
theorem B3068603 : Blo 908576 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B1364699 : Blo 908576 1364699 := bstep (se 1 (by rfl) ⟨1023524, by rfl⟩ : syracuseStep 1364699 = 2047049) B2047049
theorem B1725391 : Blo 908576 1725391 := bstep (se 1 (by rfl) ⟨1294043, by rfl⟩ : syracuseStep 1725391 = 2588087) B2588087
theorem B1365095 : Blo 908576 1365095 := bstep (se 1 (by rfl) ⟨1023821, by rfl⟩ : syracuseStep 1365095 = 2047643) B2047643
theorem B1365161 : Blo 908576 1365161 := bstep (se 2 (by rfl) ⟨511935, by rfl⟩ : syracuseStep 1365161 = 1023871) B1023871
theorem B1365227 : Blo 908576 1365227 := bstep (se 1 (by rfl) ⟨1023920, by rfl⟩ : syracuseStep 1365227 = 2047841) B2047841
theorem B11654387 : Blo 908576 11654387 := bstep (se 1 (by rfl) ⟨8740790, by rfl⟩ : syracuseStep 11654387 = 17481581) B17481581
theorem B7787771 : Blo 908576 7787771 := bstep (se 1 (by rfl) ⟨5840828, by rfl⟩ : syracuseStep 7787771 = 11681657) B11681657
theorem B5527369 : Blo 908576 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B3070007 : Blo 908576 3070007 := bstep (se 1 (by rfl) ⟨2302505, by rfl⟩ : syracuseStep 3070007 = 4605011) B4605011
theorem B1366127 : Blo 908576 1366127 := bstep (se 1 (by rfl) ⟨1024595, by rfl⟩ : syracuseStep 1366127 = 2049191) B2049191
theorem B1726591 : Blo 908576 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B1366199 : Blo 908576 1366199 := bstep (se 1 (by rfl) ⟨1024649, by rfl⟩ : syracuseStep 1366199 = 2049299) B2049299
theorem B11688421 : Blo 908576 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B1366619 : Blo 908576 1366619 := bstep (se 1 (by rfl) ⟨1024964, by rfl⟩ : syracuseStep 1366619 = 2049929) B2049929
theorem B3070655 : Blo 908576 3070655 := bstep (se 1 (by rfl) ⟨2302991, by rfl⟩ : syracuseStep 3070655 = 4605983) B4605983
theorem B3889889 : Blo 908576 3889889 := bstep (se 2 (by rfl) ⟨1458708, by rfl⟩ : syracuseStep 3889889 = 2917417) B2917417
theorem B9493357 : Blo 908576 9493357 := bstep (se 3 (by rfl) ⟨1780004, by rfl⟩ : syracuseStep 9493357 = 3560009) B3560009
theorem B3464147 : Blo 908576 3464147 := bstep (se 1 (by rfl) ⟨2598110, by rfl⟩ : syracuseStep 3464147 = 5196221) B5196221
theorem B25255127 : Blo 908576 25255127 := bstep (se 1 (by rfl) ⟨18941345, by rfl⟩ : syracuseStep 25255127 = 37882691) B37882691
theorem B908607 : Blo 908576 908607 := bstep (se 1 (by rfl) ⟨681455, by rfl⟩ : syracuseStep 908607 = 1362911) B1362911
theorem B908903 : Blo 908576 908903 := bstep (se 1 (by rfl) ⟨681677, by rfl⟩ : syracuseStep 908903 = 1363355) B1363355
theorem B1367735 : Blo 908576 1367735 := bstep (se 1 (by rfl) ⟨1025801, by rfl⟩ : syracuseStep 1367735 = 2051603) B2051603
theorem B7495391 : Blo 908576 7495391 := bstep (se 1 (by rfl) ⟨5621543, by rfl⟩ : syracuseStep 7495391 = 11243087) B11243087
theorem B11689757 : Blo 908576 11689757 := bstep (se 3 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 11689757 = 4383659) B4383659
theorem B909147 : Blo 908576 909147 := bstep (se 1 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 909147 = 1363721) B1363721
theorem B909183 : Blo 908576 909183 := bstep (se 1 (by rfl) ⟨681887, by rfl⟩ : syracuseStep 909183 = 1363775) B1363775
theorem B909343 : Blo 908576 909343 := bstep (se 1 (by rfl) ⟨682007, by rfl⟩ : syracuseStep 909343 = 1364015) B1364015
theorem B3498173 : Blo 908576 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B3498295 : Blo 908576 3498295 := bstep (se 1 (by rfl) ⟨2623721, by rfl⟩ : syracuseStep 3498295 = 5247443) B5247443
theorem B909639 : Blo 908576 909639 := bstep (se 1 (by rfl) ⟨682229, by rfl⟩ : syracuseStep 909639 = 1364459) B1364459
theorem B1368443 : Blo 908576 1368443 := bstep (se 1 (by rfl) ⟨1026332, by rfl⟩ : syracuseStep 1368443 = 2052665) B2052665
theorem B909723 : Blo 908576 909723 := bstep (se 1 (by rfl) ⟨682292, by rfl⟩ : syracuseStep 909723 = 1364585) B1364585
theorem B909727 : Blo 908576 909727 := bstep (se 1 (by rfl) ⟨682295, by rfl⟩ : syracuseStep 909727 = 1364591) B1364591
theorem B909807 : Blo 908576 909807 := bstep (se 1 (by rfl) ⟨682355, by rfl⟩ : syracuseStep 909807 = 1364711) B1364711
theorem B1368617 : Blo 908576 1368617 := bstep (se 2 (by rfl) ⟨513231, by rfl⟩ : syracuseStep 1368617 = 1026463) B1026463
theorem B909915 : Blo 908576 909915 := bstep (se 1 (by rfl) ⟨682436, by rfl⟩ : syracuseStep 909915 = 1364873) B1364873
theorem B1729127 : Blo 908576 1729127 := bstep (se 1 (by rfl) ⟨1296845, by rfl⟩ : syracuseStep 1729127 = 2593691) B2593691
theorem B910143 : Blo 908576 910143 := bstep (se 1 (by rfl) ⟨682607, by rfl⟩ : syracuseStep 910143 = 1365215) B1365215
theorem B910171 : Blo 908576 910171 := bstep (se 1 (by rfl) ⟨682628, by rfl⟩ : syracuseStep 910171 = 1365257) B1365257
theorem B7005209 : Blo 908576 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B910463 : Blo 908576 910463 := bstep (se 1 (by rfl) ⟨682847, by rfl⟩ : syracuseStep 910463 = 1365695) B1365695
theorem B910491 : Blo 908576 910491 := bstep (se 1 (by rfl) ⟨682868, by rfl⟩ : syracuseStep 910491 = 1365737) B1365737
theorem B910495 : Blo 908576 910495 := bstep (se 1 (by rfl) ⟨682871, by rfl⟩ : syracuseStep 910495 = 1365743) B1365743
theorem B3695825 : Blo 908576 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B1533343 : Blo 908576 1533343 := bstep (se 1 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 1533343 = 2300015) B2300015
theorem B3073463 : Blo 908576 3073463 := bstep (se 1 (by rfl) ⟨2305097, by rfl⟩ : syracuseStep 3073463 = 4610195) B4610195
theorem B910831 : Blo 908576 910831 := bstep (se 1 (by rfl) ⟨683123, by rfl⟩ : syracuseStep 910831 = 1366247) B1366247
theorem B910951 : Blo 908576 910951 := bstep (se 1 (by rfl) ⟨683213, by rfl⟩ : syracuseStep 910951 = 1366427) B1366427
theorem B911215 : Blo 908576 911215 := bstep (se 1 (by rfl) ⟨683411, by rfl⟩ : syracuseStep 911215 = 1366823) B1366823
theorem B911231 : Blo 908576 911231 := bstep (se 1 (by rfl) ⟨683423, by rfl⟩ : syracuseStep 911231 = 1366847) B1366847
theorem B1730555 : Blo 908576 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B911431 : Blo 908576 911431 := bstep (se 1 (by rfl) ⟨683573, by rfl⟩ : syracuseStep 911431 = 1367147) B1367147
theorem B911527 : Blo 908576 911527 := bstep (se 1 (by rfl) ⟨683645, by rfl⟩ : syracuseStep 911527 = 1367291) B1367291
theorem B911591 : Blo 908576 911591 := bstep (se 1 (by rfl) ⟨683693, by rfl⟩ : syracuseStep 911591 = 1367387) B1367387
theorem B911611 : Blo 908576 911611 := bstep (se 1 (by rfl) ⟨683708, by rfl⟩ : syracuseStep 911611 = 1367417) B1367417
theorem B911615 : Blo 908576 911615 := bstep (se 1 (by rfl) ⟨683711, by rfl⟩ : syracuseStep 911615 = 1367423) B1367423
theorem B30337283 : Blo 908576 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B911983 : Blo 908576 911983 := bstep (se 1 (by rfl) ⟨683987, by rfl⟩ : syracuseStep 911983 = 1367975) B1367975
theorem B912031 : Blo 908576 912031 := bstep (se 1 (by rfl) ⟨684023, by rfl⟩ : syracuseStep 912031 = 1368047) B1368047
theorem B912111 : Blo 908576 912111 := bstep (se 1 (by rfl) ⟨684083, by rfl⟩ : syracuseStep 912111 = 1368167) B1368167
theorem B3074813 : Blo 908576 3074813 := bstep (se 3 (by rfl) ⟨576527, by rfl⟩ : syracuseStep 3074813 = 1153055) B1153055
theorem B912199 : Blo 908576 912199 := bstep (se 1 (by rfl) ⟨684149, by rfl⟩ : syracuseStep 912199 = 1368299) B1368299
theorem B912239 : Blo 908576 912239 := bstep (se 1 (by rfl) ⟨684179, by rfl⟩ : syracuseStep 912239 = 1368359) B1368359
theorem B1731451 : Blo 908576 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B1534889 : Blo 908576 1534889 := bstep (se 2 (by rfl) ⟨575583, by rfl⟩ : syracuseStep 1534889 = 1151167) B1151167
theorem B1731527 : Blo 908576 1731527 := bstep (se 1 (by rfl) ⟨1298645, by rfl⟩ : syracuseStep 1731527 = 2597291) B2597291
theorem B912539 : Blo 908576 912539 := bstep (se 1 (by rfl) ⟨684404, by rfl⟩ : syracuseStep 912539 = 1368809) B1368809
theorem B4615865 : Blo 908576 4615865 := bstep (se 2 (by rfl) ⟨1730949, by rfl⟩ : syracuseStep 4615865 = 3461899) B3461899
theorem B3698423 : Blo 908576 3698423 := bstep (se 1 (by rfl) ⟨2773817, by rfl⟩ : syracuseStep 3698423 = 5547635) B5547635
theorem B1732423 : Blo 908576 1732423 := bstep (se 1 (by rfl) ⟨1299317, by rfl⟩ : syracuseStep 1732423 = 2598635) B2598635
theorem B1536313 : Blo 908576 1536313 := bstep (se 2 (by rfl) ⟨576117, by rfl⟩ : syracuseStep 1536313 = 1152235) B1152235
theorem B18674657 : Blo 908576 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B5338331 : Blo 908576 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B1537609 : Blo 908576 1537609 := bstep (se 2 (by rfl) ⟨576603, by rfl⟩ : syracuseStep 1537609 = 1153207) B1153207
theorem B1537643 : Blo 908576 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B5536345 : Blo 908576 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B6912863 : Blo 908576 6912863 := bstep (se 1 (by rfl) ⟨5184647, by rfl⟩ : syracuseStep 6912863 = 10369295) B10369295
theorem B1539803 : Blo 908576 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B2588861 : Blo 908576 2588861 := bstep (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) B970823
theorem B7766279 : Blo 908576 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B7373227 : Blo 908576 7373227 := bstep (se 1 (by rfl) ⟨5529920, by rfl⟩ : syracuseStep 7373227 = 11059841) B11059841
theorem B3736111 : Blo 908576 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B18680557 : Blo 908576 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B7769591 : Blo 908576 7769591 := bstep (se 1 (by rfl) ⟨5827193, by rfl⟩ : syracuseStep 7769591 = 11654387) B11654387
theorem B2625779 : Blo 908576 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B2593259 : Blo 908576 2593259 := bstep (se 1 (by rfl) ⟨1944944, by rfl⟩ : syracuseStep 2593259 = 3889889) B3889889
theorem B17502803 : Blo 908576 17502803 := bstep (se 1 (by rfl) ⟨13127102, by rfl⟩ : syracuseStep 17502803 = 26254205) B26254205
theorem B3281833 : Blo 908576 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B4920545 : Blo 908576 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B2332115 : Blo 908576 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B20191841 : Blo 908576 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B2300521 : Blo 908576 2300521 := bstep (se 2 (by rfl) ⟨862695, by rfl⟩ : syracuseStep 2300521 = 1725391) B1725391
theorem B1153703 : Blo 908576 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B20224855 : Blo 908576 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B3284071 : Blo 908576 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B1023259 : Blo 908576 1023259 := bstep (se 1 (by rfl) ⟨767444, by rfl⟩ : syracuseStep 1023259 = 1534889) B1534889
theorem B1154351 : Blo 908576 1154351 := bstep (se 1 (by rfl) ⟨865763, by rfl⟩ : syracuseStep 1154351 = 1731527) B1731527
theorem B2465615 : Blo 908576 2465615 := bstep (se 1 (by rfl) ⟨1849211, by rfl⟩ : syracuseStep 2465615 = 3698423) B3698423
theorem B2302121 : Blo 908576 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B2597417 : Blo 908576 2597417 := bstep (se 2 (by rfl) ⟨974031, by rfl⟩ : syracuseStep 2597417 = 1948063) B1948063
theorem B2597609 : Blo 908576 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B7381793 : Blo 908576 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B2106271 : Blo 908576 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B1025095 : Blo 908576 1025095 := bstep (se 1 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 1025095 = 1537643) B1537643
theorem B12657809 : Blo 908576 12657809 := bstep (se 2 (by rfl) ⟨4746678, by rfl⟩ : syracuseStep 12657809 = 9493357) B9493357
theorem B5842469 : Blo 908576 5842469 := bstep (se 4 (by rfl) ⟨547731, by rfl⟩ : syracuseStep 5842469 = 1095463) B1095463
theorem B4924999 : Blo 908576 4924999 := bstep (se 1 (by rfl) ⟨3693749, by rfl⟩ : syracuseStep 4924999 = 7387499) B7387499
theorem B6924041 : Blo 908576 6924041 := bstep (se 2 (by rfl) ⟨2596515, by rfl⟩ : syracuseStep 6924041 = 5193031) B5193031
theorem B1026535 : Blo 908576 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B2305007 : Blo 908576 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B4664393 : Blo 908576 4664393 := bstep (se 2 (by rfl) ⟨1749147, by rfl⟩ : syracuseStep 4664393 = 3498295) B3498295
theorem B4730447 : Blo 908576 4730447 := bstep (se 1 (by rfl) ⟨3547835, by rfl⟩ : syracuseStep 4730447 = 7095671) B7095671
theorem B5189615 : Blo 908576 5189615 := bstep (se 1 (by rfl) ⟨3892211, by rfl⟩ : syracuseStep 5189615 = 7784423) B7784423
theorem B2306303 : Blo 908576 2306303 := bstep (se 1 (by rfl) ⟨1729727, by rfl⟩ : syracuseStep 2306303 = 3459455) B3459455
theorem B2044331 : Blo 908576 2044331 := bstep (se 1 (by rfl) ⟨1533248, by rfl⟩ : syracuseStep 2044331 = 3066497) B3066497
theorem B14791085 : Blo 908576 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B2044457 : Blo 908576 2044457 := bstep (se 2 (by rfl) ⟨766671, by rfl⟩ : syracuseStep 2044457 = 1533343) B1533343
theorem B12464875 : Blo 908576 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B1946567 : Blo 908576 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B4600799 : Blo 908576 4600799 := bstep (se 1 (by rfl) ⟨3450599, by rfl⟩ : syracuseStep 4600799 = 6901199) B6901199
theorem B4371779 : Blo 908576 4371779 := bstep (se 1 (by rfl) ⟨3278834, by rfl⟩ : syracuseStep 4371779 = 6557669) B6557669
theorem B2045735 : Blo 908576 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B5191847 : Blo 908576 5191847 := bstep (se 1 (by rfl) ⟨3893885, by rfl⟩ : syracuseStep 5191847 = 7787771) B7787771
theorem B13154669 : Blo 908576 13154669 := bstep (se 3 (by rfl) ⟨2466500, by rfl⟩ : syracuseStep 13154669 = 4933001) B4933001
theorem B2308601 : Blo 908576 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B2046671 : Blo 908576 2046671 := bstep (se 1 (by rfl) ⟨1535003, by rfl⟩ : syracuseStep 2046671 = 3070007) B3070007
theorem B2047103 : Blo 908576 2047103 := bstep (se 1 (by rfl) ⟨1535327, by rfl⟩ : syracuseStep 2047103 = 3070655) B3070655
theorem B2309431 : Blo 908576 2309431 := bstep (se 1 (by rfl) ⟨1732073, by rfl⟩ : syracuseStep 2309431 = 3464147) B3464147
theorem B2309897 : Blo 908576 2309897 := bstep (se 2 (by rfl) ⟨866211, by rfl⟩ : syracuseStep 2309897 = 1732423) B1732423
theorem B4996927 : Blo 908576 4996927 := bstep (se 1 (by rfl) ⟨3747695, by rfl⟩ : syracuseStep 4996927 = 7495391) B7495391
theorem B5390473 : Blo 908576 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B2048417 : Blo 908576 2048417 := bstep (se 2 (by rfl) ⟨768156, by rfl⟩ : syracuseStep 2048417 = 1536313) B1536313
theorem B79971209 : Blo 908576 79971209 := bstep (se 2 (by rfl) ⟨29989203, by rfl⟩ : syracuseStep 79971209 = 59978407) B59978407
theorem B2048975 : Blo 908576 2048975 := bstep (se 1 (by rfl) ⟨1536731, by rfl⟩ : syracuseStep 2048975 = 3073463) B3073463
theorem B2049875 : Blo 908576 2049875 := bstep (se 1 (by rfl) ⟨1537406, by rfl⟩ : syracuseStep 2049875 = 3074813) B3074813
theorem B2050145 : Blo 908576 2050145 := bstep (se 2 (by rfl) ⟨768804, by rfl⟩ : syracuseStep 2050145 = 1537609) B1537609
theorem B10373669 : Blo 908576 10373669 := bstep (se 4 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 10373669 = 1945063) B1945063
theorem B1363247 : Blo 908576 1363247 := bstep (se 1 (by rfl) ⟨1022435, by rfl⟩ : syracuseStep 1363247 = 2044871) B2044871
theorem B15584561 : Blo 908576 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B3558887 : Blo 908576 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B1363433 : Blo 908576 1363433 := bstep (se 2 (by rfl) ⟨511287, by rfl⟩ : syracuseStep 1363433 = 1022575) B1022575
theorem B1363487 : Blo 908576 1363487 := bstep (se 1 (by rfl) ⟨1022615, by rfl⟩ : syracuseStep 1363487 = 2045231) B2045231
theorem B1232543 : Blo 908576 1232543 := bstep (se 1 (by rfl) ⟨924407, by rfl⟩ : syracuseStep 1232543 = 1848815) B1848815
theorem B1364105 : Blo 908576 1364105 := bstep (se 2 (by rfl) ⟨511539, by rfl⟩ : syracuseStep 1364105 = 1023079) B1023079
theorem B1364303 : Blo 908576 1364303 := bstep (se 1 (by rfl) ⟨1023227, by rfl⟩ : syracuseStep 1364303 = 2046455) B2046455
theorem B1364327 : Blo 908576 1364327 := bstep (se 1 (by rfl) ⟨1023245, by rfl⟩ : syracuseStep 1364327 = 2046491) B2046491
theorem B4608575 : Blo 908576 4608575 := bstep (se 1 (by rfl) ⟨3456431, by rfl⟩ : syracuseStep 4608575 = 6912863) B6912863
theorem B4608737 : Blo 908576 4608737 := bstep (se 2 (by rfl) ⟨1728276, by rfl⟩ : syracuseStep 4608737 = 3456553) B3456553
theorem B1364969 : Blo 908576 1364969 := bstep (se 2 (by rfl) ⟨511863, by rfl⟩ : syracuseStep 1364969 = 1023727) B1023727
theorem B1365023 : Blo 908576 1365023 := bstep (se 1 (by rfl) ⟨1023767, by rfl⟩ : syracuseStep 1365023 = 2047535) B2047535
theorem B4380007 : Blo 908576 4380007 := bstep (se 1 (by rfl) ⟨3285005, by rfl⟩ : syracuseStep 4380007 = 6570011) B6570011
theorem B3069359 : Blo 908576 3069359 := bstep (se 1 (by rfl) ⟨2302019, by rfl⟩ : syracuseStep 3069359 = 4604039) B4604039
theorem B3692051 : Blo 908576 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B11097983 : Blo 908576 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B19650863 : Blo 908576 19650863 := bstep (se 1 (by rfl) ⟨14738147, by rfl⟩ : syracuseStep 19650863 = 29476295) B29476295
theorem B11229671 : Blo 908576 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B4381451 : Blo 908576 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B10378043 : Blo 908576 10378043 := bstep (se 1 (by rfl) ⟨7783532, by rfl⟩ : syracuseStep 10378043 = 15567065) B15567065
theorem B11688785 : Blo 908576 11688785 := bstep (se 2 (by rfl) ⟨4383294, by rfl⟩ : syracuseStep 11688785 = 8766589) B8766589
theorem B3070817 : Blo 908576 3070817 := bstep (se 2 (by rfl) ⟨1151556, by rfl⟩ : syracuseStep 3070817 = 2303113) B2303113
theorem B4611005 : Blo 908576 4611005 := bstep (se 3 (by rfl) ⟨864563, by rfl⟩ : syracuseStep 4611005 = 1729127) B1729127
theorem B1367177 : Blo 908576 1367177 := bstep (se 2 (by rfl) ⟨512691, by rfl⟩ : syracuseStep 1367177 = 1025383) B1025383
theorem B3464329 : Blo 908576 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B1367195 : Blo 908576 1367195 := bstep (se 1 (by rfl) ⟨1025396, by rfl⟩ : syracuseStep 1367195 = 2050793) B2050793
theorem B1367231 : Blo 908576 1367231 := bstep (se 1 (by rfl) ⟨1025423, by rfl⟩ : syracuseStep 1367231 = 2050847) B2050847
theorem B908699 : Blo 908576 908699 := bstep (se 1 (by rfl) ⟨681524, by rfl⟩ : syracuseStep 908699 = 1363049) B1363049
theorem B2186651 : Blo 908576 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B908703 : Blo 908576 908703 := bstep (se 1 (by rfl) ⟨681527, by rfl⟩ : syracuseStep 908703 = 1363055) B1363055
theorem B5824223 : Blo 908576 5824223 := bstep (se 1 (by rfl) ⟨4368167, by rfl⟩ : syracuseStep 5824223 = 8736335) B8736335
theorem B4611815 : Blo 908576 4611815 := bstep (se 1 (by rfl) ⟨3458861, by rfl⟩ : syracuseStep 4611815 = 6917723) B6917723
theorem B3071951 : Blo 908576 3071951 := bstep (se 1 (by rfl) ⟨2303963, by rfl⟩ : syracuseStep 3071951 = 4607927) B4607927
theorem B909307 : Blo 908576 909307 := bstep (se 1 (by rfl) ⟨681980, by rfl⟩ : syracuseStep 909307 = 1363961) B1363961
theorem B909339 : Blo 908576 909339 := bstep (se 1 (by rfl) ⟨682004, by rfl⟩ : syracuseStep 909339 = 1364009) B1364009
theorem B1368095 : Blo 908576 1368095 := bstep (se 1 (by rfl) ⟨1026071, by rfl⟩ : syracuseStep 1368095 = 2052143) B2052143
theorem B74866751 : Blo 908576 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B909467 : Blo 908576 909467 := bstep (se 1 (by rfl) ⟨682100, by rfl⟩ : syracuseStep 909467 = 1364201) B1364201
theorem B909595 : Blo 908576 909595 := bstep (se 1 (by rfl) ⟨682196, by rfl⟩ : syracuseStep 909595 = 1364393) B1364393
theorem B909799 : Blo 908576 909799 := bstep (se 1 (by rfl) ⟨682349, by rfl⟩ : syracuseStep 909799 = 1364699) B1364699
theorem B9855533 : Blo 908576 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B910063 : Blo 908576 910063 := bstep (se 1 (by rfl) ⟨682547, by rfl⟩ : syracuseStep 910063 = 1365095) B1365095
theorem B910107 : Blo 908576 910107 := bstep (se 1 (by rfl) ⟨682580, by rfl⟩ : syracuseStep 910107 = 1365161) B1365161
theorem B910151 : Blo 908576 910151 := bstep (se 1 (by rfl) ⟨682613, by rfl⟩ : syracuseStep 910151 = 1365227) B1365227
theorem B4678559 : Blo 908576 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B4384081 : Blo 908576 4384081 := bstep (se 2 (by rfl) ⟨1644030, by rfl⟩ : syracuseStep 4384081 = 3288061) B3288061
theorem B910751 : Blo 908576 910751 := bstep (se 1 (by rfl) ⟨683063, by rfl⟩ : syracuseStep 910751 = 1366127) B1366127
theorem B2188727 : Blo 908576 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B910799 : Blo 908576 910799 := bstep (se 1 (by rfl) ⟨683099, by rfl⟩ : syracuseStep 910799 = 1366199) B1366199
theorem B1730153 : Blo 908576 1730153 := bstep (se 2 (by rfl) ⟨648807, by rfl⟩ : syracuseStep 1730153 = 1297615) B1297615
theorem B911079 : Blo 908576 911079 := bstep (se 1 (by rfl) ⟨683309, by rfl⟩ : syracuseStep 911079 = 1366619) B1366619
theorem B3696475 : Blo 908576 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B3696509 : Blo 908576 3696509 := bstep (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) B1386191
theorem B16836751 : Blo 908576 16836751 := bstep (se 1 (by rfl) ⟨12627563, by rfl⟩ : syracuseStep 16836751 = 25255127) B25255127
theorem B1534207 : Blo 908576 1534207 := bstep (se 1 (by rfl) ⟨1150655, by rfl⟩ : syracuseStep 1534207 = 2301311) B2301311
theorem B911823 : Blo 908576 911823 := bstep (se 1 (by rfl) ⟨683867, by rfl⟩ : syracuseStep 911823 = 1367735) B1367735
theorem B7793171 : Blo 908576 7793171 := bstep (se 1 (by rfl) ⟨5844878, by rfl⟩ : syracuseStep 7793171 = 11689757) B11689757
theorem B179333813 : Blo 908576 179333813 := bstep (se 5 (by rfl) ⟨8406272, by rfl⟩ : syracuseStep 179333813 = 16812545) B16812545
theorem B912295 : Blo 908576 912295 := bstep (se 1 (by rfl) ⟨684221, by rfl⟩ : syracuseStep 912295 = 1368443) B1368443
theorem B7891943 : Blo 908576 7891943 := bstep (se 1 (by rfl) ⟨5918957, by rfl⟩ : syracuseStep 7891943 = 11837915) B11837915
theorem B912411 : Blo 908576 912411 := bstep (se 1 (by rfl) ⟨684308, by rfl⟩ : syracuseStep 912411 = 1368617) B1368617
theorem B1535719 : Blo 908576 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B6221933 : Blo 908576 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B8745403 : Blo 908576 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B1536799 : Blo 908576 1536799 := bstep (se 1 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 1536799 = 2305199) B2305199
theorem B7369825 : Blo 908576 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B3077243 : Blo 908576 3077243 := bstep (se 1 (by rfl) ⟨2307932, by rfl⟩ : syracuseStep 3077243 = 4615865) B4615865
theorem B3699847 : Blo 908576 3699847 := bstep (se 1 (by rfl) ⟨2774885, by rfl⟩ : syracuseStep 3699847 = 5549771) B5549771
theorem B15562691 : Blo 908576 15562691 := bstep (se 1 (by rfl) ⟨11672018, by rfl⟩ : syracuseStep 15562691 = 23344037) B23344037
theorem B12449771 : Blo 908576 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B5177519 : Blo 908576 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B9830969 : Blo 908576 9830969 := bstep (se 2 (by rfl) ⟨3686613, by rfl⟩ : syracuseStep 9830969 = 7373227) B7373227
theorem B53314139 : Blo 908576 53314139 := bstep (se 1 (by rfl) ⟨39985604, by rfl⟩ : syracuseStep 53314139 = 79971209) B79971209
theorem B4981481 : Blo 908576 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B26281421 : Blo 908576 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B6915779 : Blo 908576 6915779 := bstep (se 1 (by rfl) ⟨5186834, by rfl⟩ : syracuseStep 6915779 = 10373669) B10373669
theorem B10389707 : Blo 908576 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B5179727 : Blo 908576 5179727 := bstep (se 1 (by rfl) ⟨3884795, by rfl⟩ : syracuseStep 5179727 = 7769591) B7769591
theorem B22449001 : Blo 908576 22449001 := bstep (se 2 (by rfl) ⟨8418375, by rfl⟩ : syracuseStep 22449001 = 16836751) B16836751
theorem B11668535 : Blo 908576 11668535 := bstep (se 1 (by rfl) ⟨8751401, by rfl⟩ : syracuseStep 11668535 = 17502803) B17502803
theorem B24907409 : Blo 908576 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B2461367 : Blo 908576 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B2920967 : Blo 908576 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B6918695 : Blo 908576 6918695 := bstep (se 1 (by rfl) ⟨5189021, by rfl⟩ : syracuseStep 6918695 = 10378043) B10378043
theorem B29594621 : Blo 908576 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B1643743 : Blo 908576 1643743 := bstep (se 1 (by rfl) ⟨1232807, by rfl⟩ : syracuseStep 1643743 = 2465615) B2465615
theorem B49911167 : Blo 908576 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B4921195 : Blo 908576 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B3119039 : Blo 908576 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B19732517 : Blo 908576 19732517 := bstep (se 4 (by rfl) ⟨1849923, by rfl⟩ : syracuseStep 19732517 = 3699847) B3699847
theorem B16619833 : Blo 908576 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B1153435 : Blo 908576 1153435 := bstep (se 1 (by rfl) ⟨865076, by rfl⟩ : syracuseStep 1153435 = 1730153) B1730153
theorem B2464339 : Blo 908576 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B5840009 : Blo 908576 5840009 := bstep (se 2 (by rfl) ⟨2190003, by rfl⟩ : syracuseStep 5840009 = 4380007) B4380007
theorem B21045181 : Blo 908576 21045181 := bstep (se 3 (by rfl) ⟨3945971, by rfl⟩ : syracuseStep 21045181 = 7891943) B7891943
theorem B8299847 : Blo 908576 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B3286781 : Blo 908576 3286781 := bstep (se 3 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 3286781 = 1232543) B1232543
theorem B6662569 : Blo 908576 6662569 := bstep (se 2 (by rfl) ⟨2498463, by rfl⟩ : syracuseStep 6662569 = 4996927) B4996927
theorem B7187297 : Blo 908576 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B5845441 : Blo 908576 5845441 := bstep (se 2 (by rfl) ⟨2192040, by rfl⟩ : syracuseStep 5845441 = 4384081) B4384081
theorem B6926957 : Blo 908576 6926957 := bstep (se 3 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 6926957 = 2597609) B2597609
theorem B6566665 : Blo 908576 6566665 := bstep (se 2 (by rfl) ⟨2462499, by rfl⟩ : syracuseStep 6566665 = 4924999) B4924999
theorem B2372591 : Blo 908576 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B4928633 : Blo 908576 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B1750519 : Blo 908576 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B2045609 : Blo 908576 2045609 := bstep (se 2 (by rfl) ⟨767103, by rfl⟩ : syracuseStep 2045609 = 1534207) B1534207
theorem B13121453 : Blo 908576 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B2046239 : Blo 908576 2046239 := bstep (se 1 (by rfl) ⟨1534679, by rfl⟩ : syracuseStep 2046239 = 3069359) B3069359
theorem B1554743 : Blo 908576 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B7486447 : Blo 908576 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B2047211 : Blo 908576 2047211 := bstep (se 1 (by rfl) ⟨1535408, by rfl⟩ : syracuseStep 2047211 = 3070817) B3070817
theorem B1457767 : Blo 908576 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B2047625 : Blo 908576 2047625 := bstep (se 2 (by rfl) ⟨767859, by rfl⟩ : syracuseStep 2047625 = 1535719) B1535719
theorem B3882815 : Blo 908576 3882815 := bstep (se 1 (by rfl) ⟨2912111, by rfl⟩ : syracuseStep 3882815 = 5824223) B5824223
theorem B2047967 : Blo 908576 2047967 := bstep (se 1 (by rfl) ⟨1535975, by rfl⟩ : syracuseStep 2047967 = 3071951) B3071951
theorem B17515045 : Blo 908576 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B8438539 : Blo 908576 8438539 := bstep (se 1 (by rfl) ⟨6328904, by rfl⟩ : syracuseStep 8438539 = 12657809) B12657809
theorem B1459151 : Blo 908576 1459151 := bstep (se 1 (by rfl) ⟨1094363, by rfl⟩ : syracuseStep 1459151 = 2188727) B2188727
theorem B2049065 : Blo 908576 2049065 := bstep (se 2 (by rfl) ⟨768399, by rfl⟩ : syracuseStep 2049065 = 1536799) B1536799
theorem B4375777 : Blo 908576 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B5195447 : Blo 908576 5195447 := bstep (se 1 (by rfl) ⟨3896585, by rfl⟩ : syracuseStep 5195447 = 7793171) B7793171
theorem B119555875 : Blo 908576 119555875 := bstep (se 1 (by rfl) ⟨89666906, by rfl⟩ : syracuseStep 119555875 = 179333813) B179333813
theorem B3459743 : Blo 908576 3459743 := bstep (se 1 (by rfl) ⟨2594807, by rfl⟩ : syracuseStep 3459743 = 5189615) B5189615
theorem B4147955 : Blo 908576 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B1362887 : Blo 908576 1362887 := bstep (se 1 (by rfl) ⟨1022165, by rfl⟩ : syracuseStep 1362887 = 2044331) B2044331
theorem B1362971 : Blo 908576 1362971 := bstep (se 1 (by rfl) ⟨1022228, by rfl⟩ : syracuseStep 1362971 = 2044457) B2044457
theorem B1297711 : Blo 908576 1297711 := bstep (se 1 (by rfl) ⟨973283, by rfl⟩ : syracuseStep 1297711 = 1946567) B1946567
theorem B3067199 : Blo 908576 3067199 := bstep (se 1 (by rfl) ⟨2300399, by rfl⟩ : syracuseStep 3067199 = 4600799) B4600799
theorem B2051495 : Blo 908576 2051495 := bstep (se 1 (by rfl) ⟨1538621, by rfl⟩ : syracuseStep 2051495 = 3077243) B3077243
theorem B3067361 : Blo 908576 3067361 := bstep (se 2 (by rfl) ⟨1150260, by rfl⟩ : syracuseStep 3067361 = 2300521) B2300521
theorem B1363823 : Blo 908576 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B10375127 : Blo 908576 10375127 := bstep (se 1 (by rfl) ⟨7781345, by rfl⟩ : syracuseStep 10375127 = 15562691) B15562691
theorem B3461231 : Blo 908576 3461231 := bstep (se 1 (by rfl) ⟨2595923, by rfl⟩ : syracuseStep 3461231 = 5191847) B5191847
theorem B8769779 : Blo 908576 8769779 := bstep (se 1 (by rfl) ⟨6577334, by rfl⟩ : syracuseStep 8769779 = 13154669) B13154669
theorem B1364345 : Blo 908576 1364345 := bstep (se 2 (by rfl) ⟨511629, by rfl⟩ : syracuseStep 1364345 = 1023259) B1023259
theorem B1364447 : Blo 908576 1364447 := bstep (se 1 (by rfl) ⟨1023335, by rfl⟩ : syracuseStep 1364447 = 2046671) B2046671
theorem B1364735 : Blo 908576 1364735 := bstep (se 1 (by rfl) ⟨1023551, by rfl⟩ : syracuseStep 1364735 = 2047103) B2047103
theorem B1365611 : Blo 908576 1365611 := bstep (se 1 (by rfl) ⟨1024208, by rfl⟩ : syracuseStep 1365611 = 2048417) B2048417
theorem B6903629 : Blo 908576 6903629 := bstep (se 3 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 6903629 = 2588861) B2588861
theorem B1365983 : Blo 908576 1365983 := bstep (se 1 (by rfl) ⟨1024487, by rfl⟩ : syracuseStep 1365983 = 2048975) B2048975
theorem B2808361 : Blo 908576 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B1366583 : Blo 908576 1366583 := bstep (se 1 (by rfl) ⟨1024937, by rfl⟩ : syracuseStep 1366583 = 2049875) B2049875
theorem B1366763 : Blo 908576 1366763 := bstep (se 1 (by rfl) ⟨1025072, by rfl⟩ : syracuseStep 1366763 = 2050145) B2050145
theorem B1366793 : Blo 908576 1366793 := bstep (se 2 (by rfl) ⟨512547, by rfl⟩ : syracuseStep 1366793 = 1025095) B1025095
theorem B908831 : Blo 908576 908831 := bstep (se 1 (by rfl) ⟨681623, by rfl⟩ : syracuseStep 908831 = 1363247) B1363247
theorem B908955 : Blo 908576 908955 := bstep (se 1 (by rfl) ⟨681716, by rfl⟩ : syracuseStep 908955 = 1363433) B1363433
theorem B908991 : Blo 908576 908991 := bstep (se 1 (by rfl) ⟨681743, by rfl⟩ : syracuseStep 908991 = 1363487) B1363487
theorem B909403 : Blo 908576 909403 := bstep (se 1 (by rfl) ⟨682052, by rfl⟩ : syracuseStep 909403 = 1364105) B1364105
theorem B909535 : Blo 908576 909535 := bstep (se 1 (by rfl) ⟨682151, by rfl⟩ : syracuseStep 909535 = 1364303) B1364303
theorem B909551 : Blo 908576 909551 := bstep (se 1 (by rfl) ⟨682163, by rfl⟩ : syracuseStep 909551 = 1364327) B1364327
theorem B1728839 : Blo 908576 1728839 := bstep (se 1 (by rfl) ⟨1296629, by rfl⟩ : syracuseStep 1728839 = 2593259) B2593259
theorem B3072383 : Blo 908576 3072383 := bstep (se 1 (by rfl) ⟨2304287, by rfl⟩ : syracuseStep 3072383 = 4608575) B4608575
theorem B3072491 : Blo 908576 3072491 := bstep (se 1 (by rfl) ⟨2304368, by rfl⟩ : syracuseStep 3072491 = 4608737) B4608737
theorem B1368713 : Blo 908576 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B909979 : Blo 908576 909979 := bstep (se 1 (by rfl) ⟨682484, by rfl⟩ : syracuseStep 909979 = 1364969) B1364969
theorem B910015 : Blo 908576 910015 := bstep (se 1 (by rfl) ⟨682511, by rfl⟩ : syracuseStep 910015 = 1365023) B1365023
theorem B11658077 : Blo 908576 11658077 := bstep (se 3 (by rfl) ⟨2185889, by rfl⟩ : syracuseStep 11658077 = 4371779) B4371779
theorem B13100575 : Blo 908576 13100575 := bstep (se 1 (by rfl) ⟨9825431, by rfl⟩ : syracuseStep 13100575 = 19650863) B19650863
theorem B13461227 : Blo 908576 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B107865893 : Blo 908576 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B7792523 : Blo 908576 7792523 := bstep (se 1 (by rfl) ⟨5844392, by rfl⟩ : syracuseStep 7792523 = 11688785) B11688785
theorem B3074003 : Blo 908576 3074003 := bstep (se 1 (by rfl) ⟨2305502, by rfl⟩ : syracuseStep 3074003 = 4611005) B4611005
theorem B911451 : Blo 908576 911451 := bstep (se 1 (by rfl) ⟨683588, by rfl⟩ : syracuseStep 911451 = 1367177) B1367177
theorem B911463 : Blo 908576 911463 := bstep (se 1 (by rfl) ⟨683597, by rfl⟩ : syracuseStep 911463 = 1367195) B1367195
theorem B911487 : Blo 908576 911487 := bstep (se 1 (by rfl) ⟨683615, by rfl⟩ : syracuseStep 911487 = 1367231) B1367231
theorem B3074543 : Blo 908576 3074543 := bstep (se 1 (by rfl) ⟨2305907, by rfl⟩ : syracuseStep 3074543 = 4611815) B4611815
theorem B912063 : Blo 908576 912063 := bstep (se 1 (by rfl) ⟨684047, by rfl⟩ : syracuseStep 912063 = 1368095) B1368095
theorem B1534747 : Blo 908576 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B1731611 : Blo 908576 1731611 := bstep (se 1 (by rfl) ⟨1298708, by rfl⟩ : syracuseStep 1731611 = 2597417) B2597417
theorem B11660537 : Blo 908576 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B3894979 : Blo 908576 3894979 := bstep (se 1 (by rfl) ⟨2921234, by rfl⟩ : syracuseStep 3894979 = 5842469) B5842469
theorem B4616027 : Blo 908576 4616027 := bstep (se 1 (by rfl) ⟨3462020, by rfl⟩ : syracuseStep 4616027 = 6924041) B6924041
theorem B9826433 : Blo 908576 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B3076541 : Blo 908576 3076541 := bstep (se 3 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 3076541 = 1153703) B1153703
theorem B1536671 : Blo 908576 1536671 := bstep (se 1 (by rfl) ⟨1152503, by rfl⟩ : syracuseStep 1536671 = 2305007) B2305007
theorem B3109595 : Blo 908576 3109595 := bstep (se 1 (by rfl) ⟨2332196, by rfl⟩ : syracuseStep 3109595 = 4664393) B4664393
theorem B1537535 : Blo 908576 1537535 := bstep (se 1 (by rfl) ⟨1153151, by rfl⟩ : syracuseStep 1537535 = 2306303) B2306303
theorem B9860723 : Blo 908576 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B3078269 : Blo 908576 3078269 := bstep (se 3 (by rfl) ⟨577175, by rfl⟩ : syracuseStep 3078269 = 1154351) B1154351
theorem B4619105 : Blo 908576 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B12614525 : Blo 908576 12614525 := bstep (se 3 (by rfl) ⟨2365223, by rfl⟩ : syracuseStep 12614525 = 4730447) B4730447
theorem B1539067 : Blo 908576 1539067 := bstep (se 1 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 1539067 = 2308601) B2308601
theorem B3079241 : Blo 908576 3079241 := bstep (se 2 (by rfl) ⟨1154715, by rfl⟩ : syracuseStep 3079241 = 2309431) B2309431
theorem B1539931 : Blo 908576 1539931 := bstep (se 1 (by rfl) ⟨1154948, by rfl⟩ : syracuseStep 1539931 = 2309897) B2309897
theorem B6553979 : Blo 908576 6553979 := bstep (se 1 (by rfl) ⟨4915484, by rfl⟩ : syracuseStep 6553979 = 9830969) B9830969
theorem B5834369 : Blo 908576 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B17467433 : Blo 908576 17467433 := bstep (se 2 (by rfl) ⟨6550287, by rfl⟩ : syracuseStep 17467433 = 13100575) B13100575
theorem B1640911 : Blo 908576 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B6916751 : Blo 908576 6916751 := bstep (se 1 (by rfl) ⟨5187563, by rfl⟩ : syracuseStep 6916751 = 10375127) B10375127
theorem B8883425 : Blo 908576 8883425 := bstep (se 2 (by rfl) ⟨3331284, by rfl⟩ : syracuseStep 8883425 = 6662569) B6662569
theorem B19729747 : Blo 908576 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B1152559 : Blo 908576 1152559 := bstep (se 1 (by rfl) ⟨864419, by rfl⟩ : syracuseStep 1152559 = 1728839) B1728839
theorem B7772051 : Blo 908576 7772051 := bstep (se 1 (by rfl) ⟨5829038, by rfl⟩ : syracuseStep 7772051 = 11658077) B11658077
theorem B8755553 : Blo 908576 8755553 := bstep (se 2 (by rfl) ⟨3283332, by rfl⟩ : syracuseStep 8755553 = 6566665) B6566665
theorem B6921125 : Blo 908576 6921125 := bstep (se 4 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 6921125 = 1297711) B1297711
theorem B2334025 : Blo 908576 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B1154407 : Blo 908576 1154407 := bstep (se 1 (by rfl) ⟨865805, by rfl⟩ : syracuseStep 1154407 = 1731611) B1731611
theorem B7773691 : Blo 908576 7773691 := bstep (se 1 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 7773691 = 11660537) B11660537
theorem B33169013 : Blo 908576 33169013 := bstep (se 5 (by rfl) ⟨1554797, by rfl⟩ : syracuseStep 33169013 = 3109595) B3109595
theorem B6561593 : Blo 908576 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B22159777 : Blo 908576 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B1024447 : Blo 908576 1024447 := bstep (se 1 (by rfl) ⟨768335, by rfl⟩ : syracuseStep 1024447 = 1536671) B1536671
theorem B1581727 : Blo 908576 1581727 := bstep (se 1 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 1581727 = 2372591) B2372591
theorem B3744481 : Blo 908576 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B3285755 : Blo 908576 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B3285785 : Blo 908576 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B1025023 : Blo 908576 1025023 := bstep (se 1 (by rfl) ⟨768767, by rfl⟩ : syracuseStep 1025023 = 1537535) B1537535
theorem B1943689 : Blo 908576 1943689 := bstep (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) B1457767
theorem B28060241 : Blo 908576 28060241 := bstep (se 2 (by rfl) ⟨10522590, by rfl⟩ : syracuseStep 28060241 = 21045181) B21045181
theorem B3451679 : Blo 908576 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B11251385 : Blo 908576 11251385 := bstep (se 2 (by rfl) ⟨4219269, by rfl⟩ : syracuseStep 11251385 = 8438539) B8438539
theorem B6926471 : Blo 908576 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B3453151 : Blo 908576 3453151 := bstep (se 1 (by rfl) ⟨2589863, by rfl⟩ : syracuseStep 3453151 = 5179727) B5179727
theorem B2306495 : Blo 908576 2306495 := bstep (se 1 (by rfl) ⟨1729871, by rfl⟩ : syracuseStep 2306495 = 3459743) B3459743
theorem B2765303 : Blo 908576 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B7779023 : Blo 908576 7779023 := bstep (se 1 (by rfl) ⟨5834267, by rfl⟩ : syracuseStep 7779023 = 11668535) B11668535
theorem B2044799 : Blo 908576 2044799 := bstep (se 1 (by rfl) ⟨1533599, by rfl⟩ : syracuseStep 2044799 = 3067199) B3067199
theorem B2044907 : Blo 908576 2044907 := bstep (se 1 (by rfl) ⟨1533680, by rfl⟩ : syracuseStep 2044907 = 3067361) B3067361
theorem B2307487 : Blo 908576 2307487 := bstep (se 1 (by rfl) ⟨1730615, by rfl⟩ : syracuseStep 2307487 = 3461231) B3461231
theorem B5846519 : Blo 908576 5846519 := bstep (se 1 (by rfl) ⟨4384889, by rfl⟩ : syracuseStep 5846519 = 8769779) B8769779
theorem B1947311 : Blo 908576 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B33274111 : Blo 908576 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B2046329 : Blo 908576 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B29932001 : Blo 908576 29932001 := bstep (se 2 (by rfl) ⟨11224500, by rfl⟩ : syracuseStep 29932001 = 22449001) B22449001
theorem B4602419 : Blo 908576 4602419 := bstep (se 1 (by rfl) ⟨3451814, by rfl⟩ : syracuseStep 4602419 = 6903629) B6903629
theorem B2079359 : Blo 908576 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B13155011 : Blo 908576 13155011 := bstep (se 1 (by rfl) ⟨9866258, by rfl⟩ : syracuseStep 13155011 = 19732517) B19732517
theorem B5193305 : Blo 908576 5193305 := bstep (se 2 (by rfl) ⟨1947489, by rfl⟩ : syracuseStep 5193305 = 3894979) B3894979
theorem B2048255 : Blo 908576 2048255 := bstep (se 1 (by rfl) ⟨1536191, by rfl⟩ : syracuseStep 2048255 = 3072383) B3072383
theorem B2048327 : Blo 908576 2048327 := bstep (se 1 (by rfl) ⟨1536245, by rfl⟩ : syracuseStep 2048327 = 3072491) B3072491
theorem B71910595 : Blo 908576 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B5195015 : Blo 908576 5195015 := bstep (se 1 (by rfl) ⟨3896261, by rfl⟩ : syracuseStep 5195015 = 7792523) B7792523
theorem B2049335 : Blo 908576 2049335 := bstep (se 1 (by rfl) ⟨1537001, by rfl⟩ : syracuseStep 2049335 = 3074003) B3074003
theorem B2049695 : Blo 908576 2049695 := bstep (se 1 (by rfl) ⟨1537271, by rfl⟩ : syracuseStep 2049695 = 3074543) B3074543
theorem B53135797 : Blo 908576 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B2051027 : Blo 908576 2051027 := bstep (se 1 (by rfl) ⟨1538270, by rfl⟩ : syracuseStep 2051027 = 3076541) B3076541
theorem B76664501 : Blo 908576 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B6573815 : Blo 908576 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B1363739 : Blo 908576 1363739 := bstep (se 1 (by rfl) ⟨1022804, by rfl⟩ : syracuseStep 1363739 = 2045609) B2045609
theorem B9981929 : Blo 908576 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B2052089 : Blo 908576 2052089 := bstep (se 2 (by rfl) ⟨769533, by rfl⟩ : syracuseStep 2052089 = 1539067) B1539067
theorem B2052179 : Blo 908576 2052179 := bstep (se 1 (by rfl) ⟨1539134, by rfl⟩ : syracuseStep 2052179 = 3078269) B3078269
theorem B1364159 : Blo 908576 1364159 := bstep (se 1 (by rfl) ⟨1023119, by rfl⟩ : syracuseStep 1364159 = 2046239) B2046239
theorem B1036495 : Blo 908576 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B8409683 : Blo 908576 8409683 := bstep (se 1 (by rfl) ⟨6307262, by rfl⟩ : syracuseStep 8409683 = 12614525) B12614525
theorem B2052827 : Blo 908576 2052827 := bstep (se 1 (by rfl) ⟨1539620, by rfl⟩ : syracuseStep 2052827 = 3079241) B3079241
theorem B1364807 : Blo 908576 1364807 := bstep (se 1 (by rfl) ⟨1023605, by rfl⟩ : syracuseStep 1364807 = 2047211) B2047211
theorem B1365083 : Blo 908576 1365083 := bstep (se 1 (by rfl) ⟨1023812, by rfl⟩ : syracuseStep 1365083 = 2047625) B2047625
theorem B2053241 : Blo 908576 2053241 := bstep (se 2 (by rfl) ⟨769965, by rfl⟩ : syracuseStep 2053241 = 1539931) B1539931
theorem B1365311 : Blo 908576 1365311 := bstep (se 1 (by rfl) ⟨1023983, by rfl⟩ : syracuseStep 1365311 = 2047967) B2047967
theorem B35542759 : Blo 908576 35542759 := bstep (se 1 (by rfl) ⟨26657069, by rfl⟩ : syracuseStep 35542759 = 53314139) B53314139
theorem B972767 : Blo 908576 972767 := bstep (se 1 (by rfl) ⟨729575, by rfl⟩ : syracuseStep 972767 = 1459151) B1459151
theorem B1366043 : Blo 908576 1366043 := bstep (se 1 (by rfl) ⟨1024532, by rfl⟩ : syracuseStep 1366043 = 2049065) B2049065
theorem B17520947 : Blo 908576 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B3463631 : Blo 908576 3463631 := bstep (se 1 (by rfl) ⟨2597723, by rfl⟩ : syracuseStep 3463631 = 5195447) B5195447
theorem B4610519 : Blo 908576 4610519 := bstep (se 1 (by rfl) ⟨3457889, by rfl⟩ : syracuseStep 4610519 = 6915779) B6915779
theorem B908591 : Blo 908576 908591 := bstep (se 1 (by rfl) ⟨681443, by rfl⟩ : syracuseStep 908591 = 1362887) B1362887
theorem B908647 : Blo 908576 908647 := bstep (se 1 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 908647 = 1362971) B1362971
theorem B1367663 : Blo 908576 1367663 := bstep (se 1 (by rfl) ⟨1025747, by rfl⟩ : syracuseStep 1367663 = 2051495) B2051495
theorem B159407833 : Blo 908576 159407833 := bstep (se 2 (by rfl) ⟨59777937, by rfl⟩ : syracuseStep 159407833 = 119555875) B119555875
theorem B16604939 : Blo 908576 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B909215 : Blo 908576 909215 := bstep (se 1 (by rfl) ⟨681911, by rfl⟩ : syracuseStep 909215 = 1363823) B1363823
theorem B93413573 : Blo 908576 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B909563 : Blo 908576 909563 := bstep (se 1 (by rfl) ⟨682172, by rfl⟩ : syracuseStep 909563 = 1364345) B1364345
theorem B909631 : Blo 908576 909631 := bstep (se 1 (by rfl) ⟨682223, by rfl⟩ : syracuseStep 909631 = 1364447) B1364447
theorem B4612463 : Blo 908576 4612463 := bstep (se 1 (by rfl) ⟨3459347, by rfl⟩ : syracuseStep 4612463 = 6918695) B6918695
theorem B909823 : Blo 908576 909823 := bstep (se 1 (by rfl) ⟨682367, by rfl⟩ : syracuseStep 909823 = 1364735) B1364735
theorem B910407 : Blo 908576 910407 := bstep (se 1 (by rfl) ⟨682805, by rfl⟩ : syracuseStep 910407 = 1365611) B1365611
theorem B910655 : Blo 908576 910655 := bstep (se 1 (by rfl) ⟨682991, by rfl⟩ : syracuseStep 910655 = 1365983) B1365983
theorem B911055 : Blo 908576 911055 := bstep (se 1 (by rfl) ⟨683291, by rfl⟩ : syracuseStep 911055 = 1366583) B1366583
theorem B911175 : Blo 908576 911175 := bstep (se 1 (by rfl) ⟨683381, by rfl⟩ : syracuseStep 911175 = 1366763) B1366763
theorem B911195 : Blo 908576 911195 := bstep (se 1 (by rfl) ⟨683396, by rfl⟩ : syracuseStep 911195 = 1366793) B1366793
theorem B3893339 : Blo 908576 3893339 := bstep (se 1 (by rfl) ⟨2920004, by rfl⟩ : syracuseStep 3893339 = 5840009) B5840009
theorem B912475 : Blo 908576 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B7793921 : Blo 908576 7793921 := bstep (se 2 (by rfl) ⟨2922720, by rfl⟩ : syracuseStep 7793921 = 5845441) B5845441
theorem B5533231 : Blo 908576 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B8974151 : Blo 908576 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B2191187 : Blo 908576 2191187 := bstep (se 1 (by rfl) ⟨1643390, by rfl⟩ : syracuseStep 2191187 = 3286781) B3286781
theorem B2191657 : Blo 908576 2191657 := bstep (se 2 (by rfl) ⟨821871, by rfl⟩ : syracuseStep 2191657 = 1643743) B1643743
theorem B3077351 : Blo 908576 3077351 := bstep (se 1 (by rfl) ⟨2308013, by rfl⟩ : syracuseStep 3077351 = 4616027) B4616027
theorem B6550955 : Blo 908576 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B4617971 : Blo 908576 4617971 := bstep (se 1 (by rfl) ⟨3463478, by rfl⟩ : syracuseStep 4617971 = 6926957) B6926957
theorem B1537913 : Blo 908576 1537913 := bstep (se 2 (by rfl) ⟨576717, by rfl⟩ : syracuseStep 1537913 = 1153435) B1153435
theorem B8747635 : Blo 908576 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B3079403 : Blo 908576 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B2588543 : Blo 908576 2588543 := bstep (se 1 (by rfl) ⟨1941407, by rfl⟩ : syracuseStep 2588543 = 3882815) B3882815
theorem B6654619 : Blo 908576 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B2591585 : Blo 908576 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B5606455 : Blo 908576 5606455 := bstep (se 1 (by rfl) ⟨4204841, by rfl⟩ : syracuseStep 5606455 = 8409683) B8409683
theorem B70847729 : Blo 908576 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B5181367 : Blo 908576 5181367 := bstep (se 1 (by rfl) ⟨3886025, by rfl⟩ : syracuseStep 5181367 = 7772051) B7772051
theorem B5837035 : Blo 908576 5837035 := bstep (se 1 (by rfl) ⟨4377776, by rfl⟩ : syracuseStep 5837035 = 8755553) B8755553
theorem B7377641 : Blo 908576 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B2594045 : Blo 908576 2594045 := bstep (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) B972767
theorem B2922209 : Blo 908576 2922209 := bstep (se 2 (by rfl) ⟨1095828, by rfl⟩ : syracuseStep 2922209 = 2191657) B2191657
theorem B383523173 : Blo 908576 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B2595559 : Blo 908576 2595559 := bstep (se 1 (by rfl) ⟨1946669, by rfl⟩ : syracuseStep 2595559 = 3893339) B3893339
theorem B2301119 : Blo 908576 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B47390345 : Blo 908576 47390345 := bstep (se 2 (by rfl) ⟨17771379, by rfl⟩ : syracuseStep 47390345 = 35542759) B35542759
theorem B1843535 : Blo 908576 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B5186015 : Blo 908576 5186015 := bstep (se 1 (by rfl) ⟨3889511, by rfl⟩ : syracuseStep 5186015 = 7779023) B7779023
theorem B4367303 : Blo 908576 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B1025275 : Blo 908576 1025275 := bstep (se 1 (by rfl) ⟨768956, by rfl⟩ : syracuseStep 1025275 = 1537913) B1537913
theorem B1386239 : Blo 908576 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B10364921 : Blo 908576 10364921 := bstep (se 2 (by rfl) ⟨3886845, by rfl⟩ : syracuseStep 10364921 = 7773691) B7773691
theorem B212543777 : Blo 908576 212543777 := bstep (se 2 (by rfl) ⟨79703916, by rfl⟩ : syracuseStep 212543777 = 159407833) B159407833
theorem B4369319 : Blo 908576 4369319 := bstep (se 1 (by rfl) ⟨3276989, by rfl⟩ : syracuseStep 4369319 = 6553979) B6553979
theorem B2108969 : Blo 908576 2108969 := bstep (se 2 (by rfl) ⟨790863, by rfl⟩ : syracuseStep 2108969 = 1581727) B1581727
theorem B4992641 : Blo 908576 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B11644955 : Blo 908576 11644955 := bstep (se 1 (by rfl) ⟨8733716, by rfl⟩ : syracuseStep 11644955 = 17467433) B17467433
theorem B8762093 : Blo 908576 8762093 := bstep (se 3 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 8762093 = 3285785) B3285785
theorem B11680631 : Blo 908576 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B2309087 : Blo 908576 2309087 := bstep (se 1 (by rfl) ⟨1731815, by rfl⟩ : syracuseStep 2309087 = 3463631) B3463631
theorem B4374395 : Blo 908576 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B62275715 : Blo 908576 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B4604201 : Blo 908576 4604201 := bstep (se 2 (by rfl) ⟨1726575, by rfl⟩ : syracuseStep 4604201 = 3453151) B3453151
theorem B74827309 : Blo 908576 74827309 := bstep (se 3 (by rfl) ⟨14030120, by rfl⟩ : syracuseStep 74827309 = 28060241) B28060241
theorem B5195947 : Blo 908576 5195947 := bstep (se 1 (by rfl) ⟨3896960, by rfl⟩ : syracuseStep 5195947 = 7793921) B7793921
theorem B5982767 : Blo 908576 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B1460791 : Blo 908576 1460791 := bstep (se 1 (by rfl) ⟨1095593, by rfl⟩ : syracuseStep 1460791 = 2191187) B2191187
theorem B1363199 : Blo 908576 1363199 := bstep (se 1 (by rfl) ⟨1022399, by rfl⟩ : syracuseStep 1363199 = 2044799) B2044799
theorem B1363271 : Blo 908576 1363271 := bstep (se 1 (by rfl) ⟨1022453, by rfl⟩ : syracuseStep 1363271 = 2044907) B2044907
theorem B2051567 : Blo 908576 2051567 := bstep (se 1 (by rfl) ⟨1538675, by rfl⟩ : syracuseStep 2051567 = 3077351) B3077351
theorem B1298207 : Blo 908576 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B1364219 : Blo 908576 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B3068279 : Blo 908576 3068279 := bstep (se 1 (by rfl) ⟨2301209, by rfl⟩ : syracuseStep 3068279 = 4602419) B4602419
theorem B8770007 : Blo 908576 8770007 := bstep (se 1 (by rfl) ⟨6577505, by rfl⟩ : syracuseStep 8770007 = 13155011) B13155011
theorem B2052935 : Blo 908576 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B3462203 : Blo 908576 3462203 := bstep (se 1 (by rfl) ⟨2596652, by rfl⟩ : syracuseStep 3462203 = 5193305) B5193305
theorem B1725695 : Blo 908576 1725695 := bstep (se 1 (by rfl) ⟨1294271, by rfl⟩ : syracuseStep 1725695 = 2588543) B2588543
theorem B1365503 : Blo 908576 1365503 := bstep (se 1 (by rfl) ⟨1024127, by rfl⟩ : syracuseStep 1365503 = 2048255) B2048255
theorem B1365551 : Blo 908576 1365551 := bstep (se 1 (by rfl) ⟨1024163, by rfl⟩ : syracuseStep 1365551 = 2048327) B2048327
theorem B29546369 : Blo 908576 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B1365929 : Blo 908576 1365929 := bstep (se 2 (by rfl) ⟨512223, by rfl⟩ : syracuseStep 1365929 = 1024447) B1024447
theorem B3463343 : Blo 908576 3463343 := bstep (se 1 (by rfl) ⟨2597507, by rfl⟩ : syracuseStep 3463343 = 5195015) B5195015
theorem B1366223 : Blo 908576 1366223 := bstep (se 1 (by rfl) ⟨1024667, by rfl⟩ : syracuseStep 1366223 = 2049335) B2049335
theorem B5527973 : Blo 908576 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B1366463 : Blo 908576 1366463 := bstep (se 1 (by rfl) ⟨1024847, by rfl⟩ : syracuseStep 1366463 = 2049695) B2049695
theorem B1366697 : Blo 908576 1366697 := bstep (se 2 (by rfl) ⟨512511, by rfl⟩ : syracuseStep 1366697 = 1025023) B1025023
theorem B4611167 : Blo 908576 4611167 := bstep (se 1 (by rfl) ⟨3458375, by rfl⟩ : syracuseStep 4611167 = 6916751) B6916751
theorem B1367351 : Blo 908576 1367351 := bstep (se 1 (by rfl) ⟨1025513, by rfl⟩ : syracuseStep 1367351 = 2051027) B2051027
theorem B5922283 : Blo 908576 5922283 := bstep (se 1 (by rfl) ⟨4441712, by rfl⟩ : syracuseStep 5922283 = 8883425) B8883425
theorem B51109667 : Blo 908576 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B4382543 : Blo 908576 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B909159 : Blo 908576 909159 := bstep (se 1 (by rfl) ⟨681869, by rfl⟩ : syracuseStep 909159 = 1363739) B1363739
theorem B1368059 : Blo 908576 1368059 := bstep (se 1 (by rfl) ⟨1026044, by rfl⟩ : syracuseStep 1368059 = 2052089) B2052089
theorem B1368119 : Blo 908576 1368119 := bstep (se 1 (by rfl) ⟨1026089, by rfl⟩ : syracuseStep 1368119 = 2052179) B2052179
theorem B909439 : Blo 908576 909439 := bstep (se 1 (by rfl) ⟨682079, by rfl⟩ : syracuseStep 909439 = 1364159) B1364159
theorem B1368551 : Blo 908576 1368551 := bstep (se 1 (by rfl) ⟨1026413, by rfl⟩ : syracuseStep 1368551 = 2052827) B2052827
theorem B909871 : Blo 908576 909871 := bstep (se 1 (by rfl) ⟨682403, by rfl⟩ : syracuseStep 909871 = 1364807) B1364807
theorem B2187881 : Blo 908576 2187881 := bstep (se 2 (by rfl) ⟨820455, by rfl⟩ : syracuseStep 2187881 = 1640911) B1640911
theorem B910055 : Blo 908576 910055 := bstep (se 1 (by rfl) ⟨682541, by rfl⟩ : syracuseStep 910055 = 1365083) B1365083
theorem B1368827 : Blo 908576 1368827 := bstep (se 1 (by rfl) ⟨1026620, by rfl⟩ : syracuseStep 1368827 = 2053241) B2053241
theorem B910207 : Blo 908576 910207 := bstep (se 1 (by rfl) ⟨682655, by rfl⟩ : syracuseStep 910207 = 1365311) B1365311
theorem B910695 : Blo 908576 910695 := bstep (se 1 (by rfl) ⟨683021, by rfl⟩ : syracuseStep 910695 = 1366043) B1366043
theorem B3073679 : Blo 908576 3073679 := bstep (se 1 (by rfl) ⟨2305259, by rfl⟩ : syracuseStep 3073679 = 4610519) B4610519
theorem B15558317 : Blo 908576 15558317 := bstep (se 3 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 15558317 = 5834369) B5834369
theorem B26306329 : Blo 908576 26306329 := bstep (se 2 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 26306329 = 19729747) B19729747
theorem B4614083 : Blo 908576 4614083 := bstep (se 1 (by rfl) ⟨3460562, by rfl⟩ : syracuseStep 4614083 = 6921125) B6921125
theorem B911775 : Blo 908576 911775 := bstep (se 1 (by rfl) ⟨683831, by rfl⟩ : syracuseStep 911775 = 1367663) B1367663
theorem B22112675 : Blo 908576 22112675 := bstep (se 1 (by rfl) ⟨16584506, by rfl⟩ : syracuseStep 22112675 = 33169013) B33169013
theorem B11069959 : Blo 908576 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B3074975 : Blo 908576 3074975 := bstep (se 1 (by rfl) ⟨2306231, by rfl⟩ : syracuseStep 3074975 = 4612463) B4612463
theorem B2190503 : Blo 908576 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B3076649 : Blo 908576 3076649 := bstep (se 2 (by rfl) ⟨1153743, by rfl⟩ : syracuseStep 3076649 = 2307487) B2307487
theorem B1536745 : Blo 908576 1536745 := bstep (se 2 (by rfl) ⟨576279, by rfl⟩ : syracuseStep 1536745 = 1152559) B1152559
theorem B7500923 : Blo 908576 7500923 := bstep (se 1 (by rfl) ⟨5625692, by rfl⟩ : syracuseStep 7500923 = 11251385) B11251385
theorem B4617647 : Blo 908576 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B1537663 : Blo 908576 1537663 := bstep (se 1 (by rfl) ⟨1153247, by rfl⟩ : syracuseStep 1537663 = 2306495) B2306495
theorem B44365481 : Blo 908576 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B11663513 : Blo 908576 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B3897679 : Blo 908576 3897679 := bstep (se 1 (by rfl) ⟨2923259, by rfl⟩ : syracuseStep 3897679 = 5846519) B5846519
theorem B3078647 : Blo 908576 3078647 := bstep (se 1 (by rfl) ⟨2308985, by rfl⟩ : syracuseStep 3078647 = 4617971) B4617971
theorem B19954667 : Blo 908576 19954667 := bstep (se 1 (by rfl) ⟨14966000, by rfl⟩ : syracuseStep 19954667 = 29932001) B29932001
theorem B3112033 : Blo 908576 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B1539209 : Blo 908576 1539209 := bstep (se 2 (by rfl) ⟨577203, by rfl⟩ : syracuseStep 1539209 = 1154407) B1154407
theorem B41517143 : Blo 908576 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B4918427 : Blo 908576 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B35491301 : Blo 908576 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B1150463 : Blo 908576 1150463 := bstep (se 1 (by rfl) ⟨862847, by rfl⟩ : syracuseStep 1150463 = 1725695) B1725695
theorem B19697579 : Blo 908576 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B7475273 : Blo 908576 7475273 := bstep (se 2 (by rfl) ⟨2803227, by rfl⟩ : syracuseStep 7475273 = 5606455) B5606455
theorem B31593563 : Blo 908576 31593563 := bstep (se 1 (by rfl) ⟨23695172, by rfl⟩ : syracuseStep 31593563 = 47390345) B47390345
theorem B141695851 : Blo 908576 141695851 := bstep (se 1 (by rfl) ⟨106271888, by rfl⟩ : syracuseStep 141695851 = 212543777) B212543777
theorem B14786549 : Blo 908576 14786549 := bstep (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) B1386239
theorem B5841341 : Blo 908576 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B5841395 : Blo 908576 5841395 := bstep (se 1 (by rfl) ⟨4381046, by rfl⟩ : syracuseStep 5841395 = 8762093) B8762093
theorem B7775675 : Blo 908576 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B1026139 : Blo 908576 1026139 := bstep (se 1 (by rfl) ⟨769604, by rfl⟩ : syracuseStep 1026139 = 1539209) B1539209
theorem B47231819 : Blo 908576 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B35075105 : Blo 908576 35075105 := bstep (se 2 (by rfl) ⟨13153164, by rfl⟩ : syracuseStep 35075105 = 26306329) B26306329
theorem B6927929 : Blo 908576 6927929 := bstep (se 2 (by rfl) ⟨2597973, by rfl⟩ : syracuseStep 6927929 = 5195947) B5195947
theorem B2045519 : Blo 908576 2045519 := bstep (se 1 (by rfl) ⟨1534139, by rfl⟩ : syracuseStep 2045519 = 3068279) B3068279
theorem B5846671 : Blo 908576 5846671 := bstep (se 1 (by rfl) ⟨4385003, by rfl⟩ : syracuseStep 5846671 = 8770007) B8770007
theorem B14759945 : Blo 908576 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B2308135 : Blo 908576 2308135 := bstep (se 1 (by rfl) ⟨1731101, by rfl⟩ : syracuseStep 2308135 = 3462203) B3462203
theorem B1947721 : Blo 908576 1947721 := bstep (se 2 (by rfl) ⟨730395, by rfl⟩ : syracuseStep 1947721 = 1460791) B1460791
theorem B1948139 : Blo 908576 1948139 := bstep (se 1 (by rfl) ⟨1461104, by rfl⟩ : syracuseStep 1948139 = 2922209) B2922209
theorem B2308895 : Blo 908576 2308895 := bstep (se 1 (by rfl) ⟨1731671, by rfl⟩ : syracuseStep 2308895 = 3463343) B3463343
theorem B1229023 : Blo 908576 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B7782713 : Blo 908576 7782713 := bstep (se 2 (by rfl) ⟨2918517, by rfl⟩ : syracuseStep 7782713 = 5837035) B5837035
theorem B3457343 : Blo 908576 3457343 := bstep (se 1 (by rfl) ⟨2593007, by rfl⟩ : syracuseStep 3457343 = 5186015) B5186015
theorem B1458587 : Blo 908576 1458587 := bstep (se 1 (by rfl) ⟨1093940, by rfl⟩ : syracuseStep 1458587 = 2187881) B2187881
theorem B2048993 : Blo 908576 2048993 := bstep (se 2 (by rfl) ⟨768372, by rfl⟩ : syracuseStep 2048993 = 1536745) B1536745
theorem B2049119 : Blo 908576 2049119 := bstep (se 1 (by rfl) ⟨1536839, by rfl⟩ : syracuseStep 2049119 = 3073679) B3073679
theorem B10372211 : Blo 908576 10372211 := bstep (se 1 (by rfl) ⟨7779158, by rfl⟩ : syracuseStep 10372211 = 15558317) B15558317
theorem B2049983 : Blo 908576 2049983 := bstep (se 1 (by rfl) ⟨1537487, by rfl⟩ : syracuseStep 2049983 = 3074975) B3074975
theorem B2050217 : Blo 908576 2050217 := bstep (se 2 (by rfl) ⟨768831, by rfl⟩ : syracuseStep 2050217 = 1537663) B1537663
theorem B3328427 : Blo 908576 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B2051099 : Blo 908576 2051099 := bstep (se 1 (by rfl) ⟨1538324, by rfl⟩ : syracuseStep 2051099 = 3076649) B3076649
theorem B5196905 : Blo 908576 5196905 := bstep (se 2 (by rfl) ⟨1948839, by rfl⟩ : syracuseStep 5196905 = 3897679) B3897679
theorem B5000615 : Blo 908576 5000615 := bstep (se 1 (by rfl) ⟨3750461, by rfl⟩ : syracuseStep 5000615 = 7500923) B7500923
theorem B3460745 : Blo 908576 3460745 := bstep (se 2 (by rfl) ⟨1297779, by rfl⟩ : syracuseStep 3460745 = 2595559) B2595559
theorem B29576987 : Blo 908576 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B4149377 : Blo 908576 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B2052431 : Blo 908576 2052431 := bstep (se 1 (by rfl) ⟨1539323, by rfl⟩ : syracuseStep 2052431 = 3078647) B3078647
theorem B7787087 : Blo 908576 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B3461885 : Blo 908576 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B11686781 : Blo 908576 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B3069467 : Blo 908576 3069467 := bstep (se 1 (by rfl) ⟨2302100, by rfl⟩ : syracuseStep 3069467 = 4604201) B4604201
theorem B1367033 : Blo 908576 1367033 := bstep (se 2 (by rfl) ⟨512637, by rfl⟩ : syracuseStep 1367033 = 1025275) B1025275
theorem B3988511 : Blo 908576 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B1727723 : Blo 908576 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B99769745 : Blo 908576 99769745 := bstep (se 2 (by rfl) ⟨37413654, by rfl⟩ : syracuseStep 99769745 = 74827309) B74827309
theorem B908799 : Blo 908576 908799 := bstep (se 1 (by rfl) ⟨681599, by rfl⟩ : syracuseStep 908799 = 1363199) B1363199
theorem B908847 : Blo 908576 908847 := bstep (se 1 (by rfl) ⟨681635, by rfl⟩ : syracuseStep 908847 = 1363271) B1363271
theorem B1367711 : Blo 908576 1367711 := bstep (se 1 (by rfl) ⟨1025783, by rfl⟩ : syracuseStep 1367711 = 2051567) B2051567
theorem B909479 : Blo 908576 909479 := bstep (se 1 (by rfl) ⟨682109, by rfl⟩ : syracuseStep 909479 = 1364219) B1364219
theorem B1368623 : Blo 908576 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B1729363 : Blo 908576 1729363 := bstep (se 1 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 1729363 = 2594045) B2594045
theorem B910335 : Blo 908576 910335 := bstep (se 1 (by rfl) ⟨682751, by rfl⟩ : syracuseStep 910335 = 1365503) B1365503
theorem B910367 : Blo 908576 910367 := bstep (se 1 (by rfl) ⟨682775, by rfl⟩ : syracuseStep 910367 = 1365551) B1365551
theorem B910619 : Blo 908576 910619 := bstep (se 1 (by rfl) ⟨682964, by rfl⟩ : syracuseStep 910619 = 1365929) B1365929
theorem B910815 : Blo 908576 910815 := bstep (se 1 (by rfl) ⟨683111, by rfl⟩ : syracuseStep 910815 = 1366223) B1366223
theorem B255682115 : Blo 908576 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B910975 : Blo 908576 910975 := bstep (se 1 (by rfl) ⟨683231, by rfl⟩ : syracuseStep 910975 = 1366463) B1366463
theorem B911131 : Blo 908576 911131 := bstep (se 1 (by rfl) ⟨683348, by rfl⟩ : syracuseStep 911131 = 1366697) B1366697
theorem B3074111 : Blo 908576 3074111 := bstep (se 1 (by rfl) ⟨2305583, by rfl⟩ : syracuseStep 3074111 = 4611167) B4611167
theorem B1534079 : Blo 908576 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B911567 : Blo 908576 911567 := bstep (se 1 (by rfl) ⟨683675, by rfl⟩ : syracuseStep 911567 = 1367351) B1367351
theorem B34073111 : Blo 908576 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B6908489 : Blo 908576 6908489 := bstep (se 2 (by rfl) ⟨2590683, by rfl⟩ : syracuseStep 6908489 = 5181367) B5181367
theorem B912039 : Blo 908576 912039 := bstep (se 1 (by rfl) ⟨684029, by rfl⟩ : syracuseStep 912039 = 1368059) B1368059
theorem B912079 : Blo 908576 912079 := bstep (se 1 (by rfl) ⟨684059, by rfl⟩ : syracuseStep 912079 = 1368119) B1368119
theorem B912367 : Blo 908576 912367 := bstep (se 1 (by rfl) ⟨684275, by rfl⟩ : syracuseStep 912367 = 1368551) B1368551
theorem B912551 : Blo 908576 912551 := bstep (se 1 (by rfl) ⟨684413, by rfl⟩ : syracuseStep 912551 = 1368827) B1368827
theorem B2911535 : Blo 908576 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B14741261 : Blo 908576 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B3076055 : Blo 908576 3076055 := bstep (se 1 (by rfl) ⟨2307041, by rfl⟩ : syracuseStep 3076055 = 4614083) B4614083
theorem B6909947 : Blo 908576 6909947 := bstep (se 1 (by rfl) ⟨5182460, by rfl⟩ : syracuseStep 6909947 = 10364921) B10364921
theorem B14741783 : Blo 908576 14741783 := bstep (se 1 (by rfl) ⟨11056337, by rfl⟩ : syracuseStep 14741783 = 22112675) B22112675
theorem B2912879 : Blo 908576 2912879 := bstep (se 1 (by rfl) ⟨2184659, by rfl⟩ : syracuseStep 2912879 = 4369319) B4369319
theorem B1405979 : Blo 908576 1405979 := bstep (se 1 (by rfl) ⟨1054484, by rfl⟩ : syracuseStep 1405979 = 2108969) B2108969
theorem B7763303 : Blo 908576 7763303 := bstep (se 1 (by rfl) ⟨5822477, by rfl⟩ : syracuseStep 7763303 = 11644955) B11644955
theorem B3078431 : Blo 908576 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B7896377 : Blo 908576 7896377 := bstep (se 2 (by rfl) ⟨2961141, by rfl⟩ : syracuseStep 7896377 = 5922283) B5922283
theorem B1539391 : Blo 908576 1539391 := bstep (se 1 (by rfl) ⟨1154543, by rfl⟩ : syracuseStep 1539391 = 2309087) B2309087
theorem B13303111 : Blo 908576 13303111 := bstep (se 1 (by rfl) ⟨9977333, by rfl⟩ : syracuseStep 13303111 = 19954667) B19954667
theorem B2916263 : Blo 908576 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B6914807 : Blo 908576 6914807 := bstep (se 1 (by rfl) ⟨5186105, by rfl⟩ : syracuseStep 6914807 = 10372211) B10372211
theorem B6554789 : Blo 908576 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B7767677 : Blo 908576 7767677 := bstep (se 3 (by rfl) ⟨1456439, by rfl⟩ : syracuseStep 7767677 = 2912879) B2912879
theorem B3278951 : Blo 908576 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B23660867 : Blo 908576 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B4983515 : Blo 908576 4983515 := bstep (se 1 (by rfl) ⟨3737636, by rfl⟩ : syracuseStep 4983515 = 7475273) B7475273
theorem B2659007 : Blo 908576 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B1151815 : Blo 908576 1151815 := bstep (se 1 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 1151815 = 1727723) B1727723
theorem B5183783 : Blo 908576 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B1022719 : Blo 908576 1022719 := bstep (se 1 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 1022719 = 1534079) B1534079
theorem B22715407 : Blo 908576 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B1941023 : Blo 908576 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B2596961 : Blo 908576 2596961 := bstep (se 2 (by rfl) ⟨973860, by rfl⟩ : syracuseStep 2596961 = 1947721) B1947721
theorem B9839963 : Blo 908576 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B17737481 : Blo 908576 17737481 := bstep (se 2 (by rfl) ⟨6651555, by rfl⟩ : syracuseStep 17737481 = 13303111) B13303111
theorem B1944175 : Blo 908576 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B5188475 : Blo 908576 5188475 := bstep (se 1 (by rfl) ⟨3891356, by rfl⟩ : syracuseStep 5188475 = 7782713) B7782713
theorem B2304895 : Blo 908576 2304895 := bstep (se 1 (by rfl) ⟨1728671, by rfl⟩ : syracuseStep 2304895 = 3457343) B3457343
theorem B2305817 : Blo 908576 2305817 := bstep (se 2 (by rfl) ⟨864681, by rfl⟩ : syracuseStep 2305817 = 1729363) B1729363
theorem B2307163 : Blo 908576 2307163 := bstep (se 1 (by rfl) ⟨1730372, by rfl⟩ : syracuseStep 2307163 = 3460745) B3460745
theorem B2766251 : Blo 908576 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B5191391 : Blo 908576 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B2307923 : Blo 908576 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B2046311 : Blo 908576 2046311 := bstep (se 1 (by rfl) ⟨1534733, by rfl⟩ : syracuseStep 2046311 = 3069467) B3069467
theorem B2049407 : Blo 908576 2049407 := bstep (se 1 (by rfl) ⟨1537055, by rfl⟩ : syracuseStep 2049407 = 3074111) B3074111
theorem B4605659 : Blo 908576 4605659 := bstep (se 1 (by rfl) ⟨3454244, by rfl⟩ : syracuseStep 4605659 = 6908489) B6908489
theorem B2050703 : Blo 908576 2050703 := bstep (se 1 (by rfl) ⟨1538027, by rfl⟩ : syracuseStep 2050703 = 3076055) B3076055
theorem B4606631 : Blo 908576 4606631 := bstep (se 1 (by rfl) ⟨3454973, by rfl⟩ : syracuseStep 4606631 = 6909947) B6909947
theorem B937319 : Blo 908576 937319 := bstep (se 1 (by rfl) ⟨702989, by rfl⟩ : syracuseStep 937319 = 1405979) B1405979
theorem B23383403 : Blo 908576 23383403 := bstep (se 1 (by rfl) ⟨17537552, by rfl⟩ : syracuseStep 23383403 = 35075105) B35075105
theorem B21057005 : Blo 908576 21057005 := bstep (se 3 (by rfl) ⟨3948188, by rfl⟩ : syracuseStep 21057005 = 7896377) B7896377
theorem B1363679 : Blo 908576 1363679 := bstep (se 1 (by rfl) ⟨1022759, by rfl⟩ : syracuseStep 1363679 = 2045519) B2045519
theorem B188927801 : Blo 908576 188927801 := bstep (se 2 (by rfl) ⟨70847925, by rfl⟩ : syracuseStep 188927801 = 141695851) B141695851
theorem B3067901 : Blo 908576 3067901 := bstep (se 3 (by rfl) ⟨575231, by rfl⟩ : syracuseStep 3067901 = 1150463) B1150463
theorem B2052287 : Blo 908576 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B1298759 : Blo 908576 1298759 := bstep (se 1 (by rfl) ⟨974069, by rfl⟩ : syracuseStep 1298759 = 1948139) B1948139
theorem B2052521 : Blo 908576 2052521 := bstep (se 2 (by rfl) ⟨769695, by rfl⟩ : syracuseStep 2052521 = 1539391) B1539391
theorem B27678095 : Blo 908576 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B1365995 : Blo 908576 1365995 := bstep (se 1 (by rfl) ⟨1024496, by rfl⟩ : syracuseStep 1365995 = 2048993) B2048993
theorem B1366079 : Blo 908576 1366079 := bstep (se 1 (by rfl) ⟨1024559, by rfl⟩ : syracuseStep 1366079 = 2049119) B2049119
theorem B3889565 : Blo 908576 3889565 := bstep (se 3 (by rfl) ⟨729293, by rfl⟩ : syracuseStep 3889565 = 1458587) B1458587
theorem B1366655 : Blo 908576 1366655 := bstep (se 1 (by rfl) ⟨1024991, by rfl⟩ : syracuseStep 1366655 = 2049983) B2049983
theorem B1366811 : Blo 908576 1366811 := bstep (se 1 (by rfl) ⟨1025108, by rfl⟩ : syracuseStep 1366811 = 2050217) B2050217
theorem B2218951 : Blo 908576 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1367399 : Blo 908576 1367399 := bstep (se 1 (by rfl) ⟨1025549, by rfl⟩ : syracuseStep 1367399 = 2051099) B2051099
theorem B3464603 : Blo 908576 3464603 := bstep (se 1 (by rfl) ⟨2598452, by rfl⟩ : syracuseStep 3464603 = 5196905) B5196905
theorem B3333743 : Blo 908576 3333743 := bstep (se 1 (by rfl) ⟨2500307, by rfl⟩ : syracuseStep 3333743 = 5000615) B5000615
theorem B19717991 : Blo 908576 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B13131719 : Blo 908576 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B1368185 : Blo 908576 1368185 := bstep (se 2 (by rfl) ⟨513069, by rfl⟩ : syracuseStep 1368185 = 1026139) B1026139
theorem B1368287 : Blo 908576 1368287 := bstep (se 1 (by rfl) ⟨1026215, by rfl⟩ : syracuseStep 1368287 = 2052431) B2052431
theorem B7791187 : Blo 908576 7791187 := bstep (se 1 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 7791187 = 11686781) B11686781
theorem B21062375 : Blo 908576 21062375 := bstep (se 1 (by rfl) ⟨15796781, by rfl⟩ : syracuseStep 21062375 = 31593563) B31593563
theorem B911355 : Blo 908576 911355 := bstep (se 1 (by rfl) ⟨683516, by rfl⟩ : syracuseStep 911355 = 1367033) B1367033
theorem B66513163 : Blo 908576 66513163 := bstep (se 1 (by rfl) ⟨49884872, by rfl⟩ : syracuseStep 66513163 = 99769745) B99769745
theorem B911807 : Blo 908576 911807 := bstep (se 1 (by rfl) ⟨683855, by rfl⟩ : syracuseStep 911807 = 1367711) B1367711
theorem B9857699 : Blo 908576 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B3894227 : Blo 908576 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B3894263 : Blo 908576 3894263 := bstep (se 1 (by rfl) ⟨2920697, by rfl⟩ : syracuseStep 3894263 = 5841395) B5841395
theorem B912415 : Blo 908576 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B170454743 : Blo 908576 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B7795561 : Blo 908576 7795561 := bstep (se 2 (by rfl) ⟨2923335, by rfl⟩ : syracuseStep 7795561 = 5846671) B5846671
theorem B9827507 : Blo 908576 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B3077513 : Blo 908576 3077513 := bstep (se 2 (by rfl) ⟨1154067, by rfl⟩ : syracuseStep 3077513 = 2308135) B2308135
theorem B9827855 : Blo 908576 9827855 := bstep (se 1 (by rfl) ⟨7370891, by rfl⟩ : syracuseStep 9827855 = 14741783) B14741783
theorem B31487879 : Blo 908576 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B5175535 : Blo 908576 5175535 := bstep (se 1 (by rfl) ⟨3881651, by rfl⟩ : syracuseStep 5175535 = 7763303) B7763303
theorem B4618619 : Blo 908576 4618619 := bstep (se 1 (by rfl) ⟨3463964, by rfl⟩ : syracuseStep 4618619 = 6927929) B6927929
theorem B1539263 : Blo 908576 1539263 := bstep (se 1 (by rfl) ⟨1154447, by rfl⟩ : syracuseStep 1539263 = 2308895) B2308895
theorem B10388249 : Blo 908576 10388249 := bstep (se 2 (by rfl) ⟨3895593, by rfl⟩ : syracuseStep 10388249 = 7791187) B7791187
theorem B5178451 : Blo 908576 5178451 := bstep (se 1 (by rfl) ⟨3883838, by rfl⟩ : syracuseStep 5178451 = 7767677) B7767677
theorem B1772671 : Blo 908576 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B2592233 : Blo 908576 2592233 := bstep (se 2 (by rfl) ⟨972087, by rfl⟩ : syracuseStep 2592233 = 1944175) B1944175
theorem B18452063 : Blo 908576 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B7376669 : Blo 908576 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B2593043 : Blo 908576 2593043 := bstep (se 1 (by rfl) ⟨1944782, by rfl⟩ : syracuseStep 2593043 = 3889565) B3889565
theorem B13145327 : Blo 908576 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B8754479 : Blo 908576 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B6559975 : Blo 908576 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B10394081 : Blo 908576 10394081 := bstep (se 2 (by rfl) ⟨3897780, by rfl⟩ : syracuseStep 10394081 = 7795561) B7795561
theorem B2596151 : Blo 908576 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B2596175 : Blo 908576 2596175 := bstep (se 1 (by rfl) ⟨1947131, by rfl⟩ : syracuseStep 2596175 = 3894263) B3894263
theorem B2499517 : Blo 908576 2499517 := bstep (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) B937319
theorem B2958601 : Blo 908576 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B30287209 : Blo 908576 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B1026175 : Blo 908576 1026175 := bstep (se 1 (by rfl) ⟨769631, by rfl⟩ : syracuseStep 1026175 = 1539263) B1539263
theorem B4369859 : Blo 908576 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B3322343 : Blo 908576 3322343 := bstep (se 1 (by rfl) ⟨2491757, by rfl⟩ : syracuseStep 3322343 = 4983515) B4983515
theorem B14038003 : Blo 908576 14038003 := bstep (se 1 (by rfl) ⟨10528502, by rfl⟩ : syracuseStep 14038003 = 21057005) B21057005
theorem B2045267 : Blo 908576 2045267 := bstep (se 1 (by rfl) ⟨1533950, by rfl⟩ : syracuseStep 2045267 = 3067901) B3067901
theorem B88684217 : Blo 908576 88684217 := bstep (se 2 (by rfl) ⟨33256581, by rfl⟩ : syracuseStep 88684217 = 66513163) B66513163
theorem B3455855 : Blo 908576 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B2309735 : Blo 908576 2309735 := bstep (se 1 (by rfl) ⟨1732301, by rfl⟩ : syracuseStep 2309735 = 3464603) B3464603
theorem B83967677 : Blo 908576 83967677 := bstep (se 3 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 83967677 = 31487879) B31487879
theorem B14041583 : Blo 908576 14041583 := bstep (se 1 (by rfl) ⟨10531187, by rfl⟩ : syracuseStep 14041583 = 21062375) B21062375
theorem B63095645 : Blo 908576 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B6571799 : Blo 908576 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B3458983 : Blo 908576 3458983 := bstep (se 1 (by rfl) ⟨2594237, by rfl⟩ : syracuseStep 3458983 = 5188475) B5188475
theorem B6900713 : Blo 908576 6900713 := bstep (se 2 (by rfl) ⟨2587767, by rfl⟩ : syracuseStep 6900713 = 5175535) B5175535
theorem B2051675 : Blo 908576 2051675 := bstep (se 1 (by rfl) ⟨1538756, by rfl⟩ : syracuseStep 2051675 = 3077513) B3077513
theorem B1363625 : Blo 908576 1363625 := bstep (se 2 (by rfl) ⟨511359, by rfl⟩ : syracuseStep 1363625 = 1022719) B1022719
theorem B3460927 : Blo 908576 3460927 := bstep (se 1 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 3460927 = 5191391) B5191391
theorem B1364207 : Blo 908576 1364207 := bstep (se 1 (by rfl) ⟨1023155, by rfl⟩ : syracuseStep 1364207 = 2046311) B2046311
theorem B4609871 : Blo 908576 4609871 := bstep (se 1 (by rfl) ⟨3457403, by rfl⟩ : syracuseStep 4609871 = 6914807) B6914807
theorem B3463357 : Blo 908576 3463357 := bstep (se 3 (by rfl) ⟨649379, by rfl⟩ : syracuseStep 3463357 = 1298759) B1298759
theorem B1366271 : Blo 908576 1366271 := bstep (se 1 (by rfl) ⟨1024703, by rfl⟩ : syracuseStep 1366271 = 2049407) B2049407
theorem B3070439 : Blo 908576 3070439 := bstep (se 1 (by rfl) ⟨2302829, by rfl⟩ : syracuseStep 3070439 = 4605659) B4605659
theorem B2185967 : Blo 908576 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B1367135 : Blo 908576 1367135 := bstep (se 1 (by rfl) ⟨1025351, by rfl⟩ : syracuseStep 1367135 = 2050703) B2050703
theorem B3071087 : Blo 908576 3071087 := bstep (se 1 (by rfl) ⟨2303315, by rfl⟩ : syracuseStep 3071087 = 4606631) B4606631
theorem B15588935 : Blo 908576 15588935 := bstep (se 1 (by rfl) ⟨11691701, by rfl⟩ : syracuseStep 15588935 = 23383403) B23383403
theorem B909119 : Blo 908576 909119 := bstep (se 1 (by rfl) ⟨681839, by rfl⟩ : syracuseStep 909119 = 1363679) B1363679
theorem B125951867 : Blo 908576 125951867 := bstep (se 1 (by rfl) ⟨94463900, by rfl⟩ : syracuseStep 125951867 = 188927801) B188927801
theorem B1368191 : Blo 908576 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B1368347 : Blo 908576 1368347 := bstep (se 1 (by rfl) ⟨1026260, by rfl⟩ : syracuseStep 1368347 = 2052521) B2052521
theorem B26206685 : Blo 908576 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B3073193 : Blo 908576 3073193 := bstep (se 2 (by rfl) ⟨1152447, by rfl⟩ : syracuseStep 3073193 = 2304895) B2304895
theorem B910663 : Blo 908576 910663 := bstep (se 1 (by rfl) ⟨682997, by rfl⟩ : syracuseStep 910663 = 1365995) B1365995
theorem B910719 : Blo 908576 910719 := bstep (se 1 (by rfl) ⟨683039, by rfl⟩ : syracuseStep 910719 = 1366079) B1366079
theorem B911103 : Blo 908576 911103 := bstep (se 1 (by rfl) ⟨683327, by rfl⟩ : syracuseStep 911103 = 1366655) B1366655
theorem B911207 : Blo 908576 911207 := bstep (se 1 (by rfl) ⟨683405, by rfl⟩ : syracuseStep 911207 = 1366811) B1366811
theorem B911599 : Blo 908576 911599 := bstep (se 1 (by rfl) ⟨683699, by rfl⟩ : syracuseStep 911599 = 1367399) B1367399
theorem B2222495 : Blo 908576 2222495 := bstep (se 1 (by rfl) ⟨1666871, by rfl⟩ : syracuseStep 2222495 = 3333743) B3333743
theorem B1731307 : Blo 908576 1731307 := bstep (se 1 (by rfl) ⟨1298480, by rfl⟩ : syracuseStep 1731307 = 2596961) B2596961
theorem B912123 : Blo 908576 912123 := bstep (se 1 (by rfl) ⟨684092, by rfl⟩ : syracuseStep 912123 = 1368185) B1368185
theorem B912191 : Blo 908576 912191 := bstep (se 1 (by rfl) ⟨684143, by rfl⟩ : syracuseStep 912191 = 1368287) B1368287
theorem B1535753 : Blo 908576 1535753 := bstep (se 2 (by rfl) ⟨575907, by rfl⟩ : syracuseStep 1535753 = 1151815) B1151815
theorem B11824987 : Blo 908576 11824987 := bstep (se 1 (by rfl) ⟨8868740, by rfl⟩ : syracuseStep 11824987 = 17737481) B17737481
theorem B3076217 : Blo 908576 3076217 := bstep (se 2 (by rfl) ⟨1153581, by rfl⟩ : syracuseStep 3076217 = 2307163) B2307163
theorem B113636495 : Blo 908576 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B1537211 : Blo 908576 1537211 := bstep (se 1 (by rfl) ⟨1152908, by rfl⟩ : syracuseStep 1537211 = 2305817) B2305817
theorem B6551903 : Blo 908576 6551903 := bstep (se 1 (by rfl) ⟨4913927, by rfl⟩ : syracuseStep 6551903 = 9827855) B9827855
theorem B1538615 : Blo 908576 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B5176061 : Blo 908576 5176061 := bstep (se 3 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 5176061 = 1941023) B1941023
theorem B3079079 : Blo 908576 3079079 := bstep (se 1 (by rfl) ⟨2309309, by rfl⟩ : syracuseStep 3079079 = 4618619) B4618619
theorem B4917779 : Blo 908576 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B5836319 : Blo 908576 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B2363561 : Blo 908576 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B10392623 : Blo 908576 10392623 := bstep (se 1 (by rfl) ⟨7794467, by rfl⟩ : syracuseStep 10392623 = 15588935) B15588935
theorem B15766649 : Blo 908576 15766649 := bstep (se 2 (by rfl) ⟨5912493, by rfl⟩ : syracuseStep 15766649 = 11824987) B11824987
theorem B17471123 : Blo 908576 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B18717337 : Blo 908576 18717337 := bstep (se 2 (by rfl) ⟨7019001, by rfl⟩ : syracuseStep 18717337 = 14038003) B14038003
theorem B1481663 : Blo 908576 1481663 := bstep (se 1 (by rfl) ⟨1111247, by rfl⟩ : syracuseStep 1481663 = 2222495) B2222495
theorem B1023835 : Blo 908576 1023835 := bstep (se 1 (by rfl) ⟨767876, by rfl⟩ : syracuseStep 1023835 = 1535753) B1535753
theorem B1024807 : Blo 908576 1024807 := bstep (se 1 (by rfl) ⟨768605, by rfl⟩ : syracuseStep 1024807 = 1537211) B1537211
theorem B6923069 : Blo 908576 6923069 := bstep (se 3 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 6923069 = 2596151) B2596151
theorem B59122811 : Blo 908576 59122811 := bstep (se 1 (by rfl) ⟨44342108, by rfl⟩ : syracuseStep 59122811 = 88684217) B88684217
theorem B4367935 : Blo 908576 4367935 := bstep (se 1 (by rfl) ⟨3275951, by rfl⟩ : syracuseStep 4367935 = 6551903) B6551903
theorem B1025743 : Blo 908576 1025743 := bstep (se 1 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 1025743 = 1538615) B1538615
theorem B3450707 : Blo 908576 3450707 := bstep (se 1 (by rfl) ⟨2588030, by rfl⟩ : syracuseStep 3450707 = 5176061) B5176061
theorem B2303903 : Blo 908576 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B55978451 : Blo 908576 55978451 := bstep (se 1 (by rfl) ⟨41983838, by rfl⟩ : syracuseStep 55978451 = 83967677) B83967677
theorem B6925499 : Blo 908576 6925499 := bstep (se 1 (by rfl) ⟨5194124, by rfl⟩ : syracuseStep 6925499 = 10388249) B10388249
theorem B8859581 : Blo 908576 8859581 := bstep (se 3 (by rfl) ⟨1661171, by rfl⟩ : syracuseStep 8859581 = 3322343) B3322343
theorem B3944801 : Blo 908576 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B40382945 : Blo 908576 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B4600475 : Blo 908576 4600475 := bstep (se 1 (by rfl) ⟨3450356, by rfl⟩ : syracuseStep 4600475 = 6900713) B6900713
theorem B12301375 : Blo 908576 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B8763551 : Blo 908576 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B2308409 : Blo 908576 2308409 := bstep (se 2 (by rfl) ⟨865653, by rfl⟩ : syracuseStep 2308409 = 1731307) B1731307
theorem B6929387 : Blo 908576 6929387 := bstep (se 1 (by rfl) ⟨5197040, by rfl⟩ : syracuseStep 6929387 = 10394081) B10394081
theorem B2046959 : Blo 908576 2046959 := bstep (se 1 (by rfl) ⟨1535219, by rfl⟩ : syracuseStep 2046959 = 3070439) B3070439
theorem B2047391 : Blo 908576 2047391 := bstep (se 1 (by rfl) ⟨1535543, by rfl⟩ : syracuseStep 2047391 = 3071087) B3071087
theorem B83967911 : Blo 908576 83967911 := bstep (se 1 (by rfl) ⟨62975933, by rfl⟩ : syracuseStep 83967911 = 125951867) B125951867
theorem B2048795 : Blo 908576 2048795 := bstep (se 1 (by rfl) ⟨1536596, by rfl⟩ : syracuseStep 2048795 = 3073193) B3073193
theorem B2050811 : Blo 908576 2050811 := bstep (se 1 (by rfl) ⟨1538108, by rfl⟩ : syracuseStep 2050811 = 3076217) B3076217
theorem B1363511 : Blo 908576 1363511 := bstep (se 1 (by rfl) ⟨1022633, by rfl⟩ : syracuseStep 1363511 = 2045267) B2045267
theorem B2052719 : Blo 908576 2052719 := bstep (se 1 (by rfl) ⟨1539539, by rfl⟩ : syracuseStep 2052719 = 3079079) B3079079
theorem B9361055 : Blo 908576 9361055 := bstep (se 1 (by rfl) ⟨7020791, by rfl⟩ : syracuseStep 9361055 = 14041583) B14041583
theorem B4381199 : Blo 908576 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B6904601 : Blo 908576 6904601 := bstep (se 2 (by rfl) ⟨2589225, by rfl⟩ : syracuseStep 6904601 = 5178451) B5178451
theorem B168255053 : Blo 908576 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B1728155 : Blo 908576 1728155 := bstep (se 1 (by rfl) ⟨1296116, by rfl⟩ : syracuseStep 1728155 = 2592233) B2592233
theorem B1367783 : Blo 908576 1367783 := bstep (se 1 (by rfl) ⟨1025837, by rfl⟩ : syracuseStep 1367783 = 2051675) B2051675
theorem B909083 : Blo 908576 909083 := bstep (se 1 (by rfl) ⟨681812, by rfl⟩ : syracuseStep 909083 = 1363625) B1363625
theorem B4611977 : Blo 908576 4611977 := bstep (se 2 (by rfl) ⟨1729491, by rfl⟩ : syracuseStep 4611977 = 3458983) B3458983
theorem B909471 : Blo 908576 909471 := bstep (se 1 (by rfl) ⟨682103, by rfl⟩ : syracuseStep 909471 = 1364207) B1364207
theorem B1368233 : Blo 908576 1368233 := bstep (se 2 (by rfl) ⟨513087, by rfl⟩ : syracuseStep 1368233 = 1026175) B1026175
theorem B1728695 : Blo 908576 1728695 := bstep (se 1 (by rfl) ⟨1296521, by rfl⟩ : syracuseStep 1728695 = 2593043) B2593043
theorem B3073247 : Blo 908576 3073247 := bstep (se 1 (by rfl) ⟨2304935, by rfl⟩ : syracuseStep 3073247 = 4609871) B4609871
theorem B910847 : Blo 908576 910847 := bstep (se 1 (by rfl) ⟨683135, by rfl⟩ : syracuseStep 910847 = 1366271) B1366271
theorem B911423 : Blo 908576 911423 := bstep (se 1 (by rfl) ⟨683567, by rfl⟩ : syracuseStep 911423 = 1367135) B1367135
theorem B1730783 : Blo 908576 1730783 := bstep (se 1 (by rfl) ⟨1298087, by rfl⟩ : syracuseStep 1730783 = 2596175) B2596175
theorem B13330757 : Blo 908576 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B4614569 : Blo 908576 4614569 := bstep (se 2 (by rfl) ⟨1730463, by rfl⟩ : syracuseStep 4614569 = 3460927) B3460927
theorem B912127 : Blo 908576 912127 := bstep (se 1 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 912127 = 1368191) B1368191
theorem B912231 : Blo 908576 912231 := bstep (se 1 (by rfl) ⟨684173, by rfl⟩ : syracuseStep 912231 = 1368347) B1368347
theorem B5829245 : Blo 908576 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B2913239 : Blo 908576 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B4617809 : Blo 908576 4617809 := bstep (se 2 (by rfl) ⟨1731678, by rfl⟩ : syracuseStep 4617809 = 3463357) B3463357
theorem B8746633 : Blo 908576 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B75757663 : Blo 908576 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B1539823 : Blo 908576 1539823 := bstep (se 1 (by rfl) ⟨1154867, by rfl⟩ : syracuseStep 1539823 = 2309735) B2309735
theorem B10519469 : Blo 908576 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B3278519 : Blo 908576 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B1575707 : Blo 908576 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B2920799 : Blo 908576 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B112170035 : Blo 908576 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B1152463 : Blo 908576 1152463 := bstep (se 1 (by rfl) ⟨864347, by rfl⟩ : syracuseStep 1152463 = 1728695) B1728695
theorem B2300471 : Blo 908576 2300471 := bstep (se 1 (by rfl) ⟨1725353, by rfl⟩ : syracuseStep 2300471 = 3450707) B3450707
theorem B1153855 : Blo 908576 1153855 := bstep (se 1 (by rfl) ⟨865391, by rfl⟩ : syracuseStep 1153855 = 1730783) B1730783
theorem B8887171 : Blo 908576 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B5906387 : Blo 908576 5906387 := bstep (se 1 (by rfl) ⟨4429790, by rfl⟩ : syracuseStep 5906387 = 8859581) B8859581
theorem B1942159 : Blo 908576 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B5842367 : Blo 908576 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B55978607 : Blo 908576 55978607 := bstep (se 1 (by rfl) ⟨41983955, by rfl⟩ : syracuseStep 55978607 = 83967911) B83967911
theorem B404040869 : Blo 908576 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B6928415 : Blo 908576 6928415 := bstep (se 1 (by rfl) ⟨5196311, by rfl⟩ : syracuseStep 6928415 = 10392623) B10392623
theorem B99825797 : Blo 908576 99825797 := bstep (se 4 (by rfl) ⟨9358668, by rfl⟩ : syracuseStep 99825797 = 18717337) B18717337
theorem B11647415 : Blo 908576 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B4603067 : Blo 908576 4603067 := bstep (se 1 (by rfl) ⟨3452300, by rfl⟩ : syracuseStep 4603067 = 6904601) B6904601
theorem B2048831 : Blo 908576 2048831 := bstep (se 1 (by rfl) ⟨1536623, by rfl⟩ : syracuseStep 2048831 = 3073247) B3073247
theorem B16401833 : Blo 908576 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B3951101 : Blo 908576 3951101 := bstep (se 3 (by rfl) ⟨740831, by rfl⟩ : syracuseStep 3951101 = 1481663) B1481663
theorem B26921963 : Blo 908576 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B3886163 : Blo 908576 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B3066983 : Blo 908576 3066983 := bstep (se 1 (by rfl) ⟨2300237, by rfl⟩ : syracuseStep 3066983 = 4600475) B4600475
theorem B4608413 : Blo 908576 4608413 := bstep (se 3 (by rfl) ⟨864077, by rfl⟩ : syracuseStep 4608413 = 1728155) B1728155
theorem B1364639 : Blo 908576 1364639 := bstep (se 1 (by rfl) ⟨1023479, by rfl⟩ : syracuseStep 1364639 = 2046959) B2046959
theorem B1364927 : Blo 908576 1364927 := bstep (se 1 (by rfl) ⟨1023695, by rfl⟩ : syracuseStep 1364927 = 2047391) B2047391
theorem B2053097 : Blo 908576 2053097 := bstep (se 2 (by rfl) ⟨769911, by rfl⟩ : syracuseStep 2053097 = 1539823) B1539823
theorem B1365113 : Blo 908576 1365113 := bstep (se 2 (by rfl) ⟨511917, by rfl⟩ : syracuseStep 1365113 = 1023835) B1023835
theorem B1365863 : Blo 908576 1365863 := bstep (se 1 (by rfl) ⟨1024397, by rfl⟩ : syracuseStep 1365863 = 2048795) B2048795
theorem B1366409 : Blo 908576 1366409 := bstep (se 2 (by rfl) ⟨512403, by rfl⟩ : syracuseStep 1366409 = 1024807) B1024807
theorem B1367207 : Blo 908576 1367207 := bstep (se 1 (by rfl) ⟨1025405, by rfl⟩ : syracuseStep 1367207 = 2050811) B2050811
theorem B5823913 : Blo 908576 5823913 := bstep (se 2 (by rfl) ⟨2183967, by rfl⟩ : syracuseStep 5823913 = 4367935) B4367935
theorem B1367657 : Blo 908576 1367657 := bstep (se 2 (by rfl) ⟨512871, by rfl⟩ : syracuseStep 1367657 = 1025743) B1025743
theorem B3890879 : Blo 908576 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B909007 : Blo 908576 909007 := bstep (se 1 (by rfl) ⟨681755, by rfl⟩ : syracuseStep 909007 = 1363511) B1363511
theorem B1368479 : Blo 908576 1368479 := bstep (se 1 (by rfl) ⟨1026359, by rfl⟩ : syracuseStep 1368479 = 2052719) B2052719
theorem B10511099 : Blo 908576 10511099 := bstep (se 1 (by rfl) ⟨7883324, by rfl⟩ : syracuseStep 10511099 = 15766649) B15766649
theorem B24962813 : Blo 908576 24962813 := bstep (se 3 (by rfl) ⟨4680527, by rfl⟩ : syracuseStep 24962813 = 9361055) B9361055
theorem B911855 : Blo 908576 911855 := bstep (se 1 (by rfl) ⟨683891, by rfl⟩ : syracuseStep 911855 = 1367783) B1367783
theorem B3074651 : Blo 908576 3074651 := bstep (se 1 (by rfl) ⟨2305988, by rfl⟩ : syracuseStep 3074651 = 4611977) B4611977
theorem B912155 : Blo 908576 912155 := bstep (se 1 (by rfl) ⟨684116, by rfl⟩ : syracuseStep 912155 = 1368233) B1368233
theorem B4615379 : Blo 908576 4615379 := bstep (se 1 (by rfl) ⟨3461534, by rfl⟩ : syracuseStep 4615379 = 6923069) B6923069
theorem B39415207 : Blo 908576 39415207 := bstep (se 1 (by rfl) ⟨29561405, by rfl⟩ : syracuseStep 39415207 = 59122811) B59122811
theorem B1535935 : Blo 908576 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B3076379 : Blo 908576 3076379 := bstep (se 1 (by rfl) ⟨2307284, by rfl⟩ : syracuseStep 3076379 = 4614569) B4614569
theorem B37318967 : Blo 908576 37318967 := bstep (se 1 (by rfl) ⟨27989225, by rfl⟩ : syracuseStep 37318967 = 55978451) B55978451
theorem B4616999 : Blo 908576 4616999 := bstep (se 1 (by rfl) ⟨3462749, by rfl⟩ : syracuseStep 4616999 = 6925499) B6925499
theorem B11662177 : Blo 908576 11662177 := bstep (se 2 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 11662177 = 8746633) B8746633
theorem B3078539 : Blo 908576 3078539 := bstep (se 1 (by rfl) ⟨2308904, by rfl⟩ : syracuseStep 3078539 = 4617809) B4617809
theorem B1538939 : Blo 908576 1538939 := bstep (se 1 (by rfl) ⟨1154204, by rfl⟩ : syracuseStep 1538939 = 2308409) B2308409
theorem B4619591 : Blo 908576 4619591 := bstep (se 1 (by rfl) ⟨3464693, by rfl⟩ : syracuseStep 4619591 = 6929387) B6929387
theorem B7012979 : Blo 908576 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B2589545 : Blo 908576 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B2590775 : Blo 908576 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B74780023 : Blo 908576 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B174952885 : Blo 908576 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B2593919 : Blo 908576 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B3937591 : Blo 908576 3937591 := bstep (se 1 (by rfl) ⟨2953193, by rfl⟩ : syracuseStep 3937591 = 5906387) B5906387
theorem B4201885 : Blo 908576 4201885 := bstep (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) B1575707
theorem B269360579 : Blo 908576 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B24879311 : Blo 908576 24879311 := bstep (se 1 (by rfl) ⟨18659483, by rfl⟩ : syracuseStep 24879311 = 37318967) B37318967
theorem B1025959 : Blo 908576 1025959 := bstep (se 1 (by rfl) ⟨769469, by rfl⟩ : syracuseStep 1025959 = 1538939) B1538939
theorem B2634067 : Blo 908576 2634067 := bstep (se 1 (by rfl) ⟨1975550, by rfl⟩ : syracuseStep 2634067 = 3951101) B3951101
theorem B2044655 : Blo 908576 2044655 := bstep (se 1 (by rfl) ⟨1533491, by rfl⟩ : syracuseStep 2044655 = 3066983) B3066983
theorem B2047913 : Blo 908576 2047913 := bstep (se 2 (by rfl) ⟨767967, by rfl⟩ : syracuseStep 2047913 = 1535935) B1535935
theorem B15549569 : Blo 908576 15549569 := bstep (se 2 (by rfl) ⟨5831088, by rfl⟩ : syracuseStep 15549569 = 11662177) B11662177
theorem B2049767 : Blo 908576 2049767 := bstep (se 1 (by rfl) ⟨1537325, by rfl⟩ : syracuseStep 2049767 = 3074651) B3074651
theorem B2050919 : Blo 908576 2050919 := bstep (se 1 (by rfl) ⟨1538189, by rfl⟩ : syracuseStep 2050919 = 3076379) B3076379
theorem B11849561 : Blo 908576 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B2052359 : Blo 908576 2052359 := bstep (se 1 (by rfl) ⟨1539269, by rfl⟩ : syracuseStep 2052359 = 3078539) B3078539
theorem B3068711 : Blo 908576 3068711 := bstep (se 1 (by rfl) ⟨2301533, by rfl⟩ : syracuseStep 3068711 = 4603067) B4603067
theorem B1365887 : Blo 908576 1365887 := bstep (se 1 (by rfl) ⟨1024415, by rfl⟩ : syracuseStep 1365887 = 2048831) B2048831
theorem B7788797 : Blo 908576 7788797 := bstep (se 3 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 7788797 = 2920799) B2920799
theorem B2185679 : Blo 908576 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B17947975 : Blo 908576 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B3072275 : Blo 908576 3072275 := bstep (se 1 (by rfl) ⟨2304206, by rfl⟩ : syracuseStep 3072275 = 4608413) B4608413
theorem B909759 : Blo 908576 909759 := bstep (se 1 (by rfl) ⟨682319, by rfl⟩ : syracuseStep 909759 = 1364639) B1364639
theorem B909951 : Blo 908576 909951 := bstep (se 1 (by rfl) ⟨682463, by rfl⟩ : syracuseStep 909951 = 1364927) B1364927
theorem B1368731 : Blo 908576 1368731 := bstep (se 1 (by rfl) ⟨1026548, by rfl⟩ : syracuseStep 1368731 = 2053097) B2053097
theorem B910075 : Blo 908576 910075 := bstep (se 1 (by rfl) ⟨682556, by rfl⟩ : syracuseStep 910075 = 1365113) B1365113
theorem B910575 : Blo 908576 910575 := bstep (se 1 (by rfl) ⟨682931, by rfl⟩ : syracuseStep 910575 = 1365863) B1365863
theorem B910939 : Blo 908576 910939 := bstep (se 1 (by rfl) ⟨683204, by rfl⟩ : syracuseStep 910939 = 1366409) B1366409
theorem B1533647 : Blo 908576 1533647 := bstep (se 1 (by rfl) ⟨1150235, by rfl⟩ : syracuseStep 1533647 = 2300471) B2300471
theorem B52553609 : Blo 908576 52553609 := bstep (se 2 (by rfl) ⟨19707603, by rfl⟩ : syracuseStep 52553609 = 39415207) B39415207
theorem B911471 : Blo 908576 911471 := bstep (se 1 (by rfl) ⟨683603, by rfl⟩ : syracuseStep 911471 = 1367207) B1367207
theorem B911771 : Blo 908576 911771 := bstep (se 1 (by rfl) ⟨683828, by rfl⟩ : syracuseStep 911771 = 1367657) B1367657
theorem B912319 : Blo 908576 912319 := bstep (se 1 (by rfl) ⟨684239, by rfl⟩ : syracuseStep 912319 = 1368479) B1368479
theorem B7007399 : Blo 908576 7007399 := bstep (se 1 (by rfl) ⟨5255549, by rfl⟩ : syracuseStep 7007399 = 10511099) B10511099
theorem B3894911 : Blo 908576 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B16641875 : Blo 908576 16641875 := bstep (se 1 (by rfl) ⟨12481406, by rfl⟩ : syracuseStep 16641875 = 24962813) B24962813
theorem B37319071 : Blo 908576 37319071 := bstep (se 1 (by rfl) ⟨27989303, by rfl⟩ : syracuseStep 37319071 = 55978607) B55978607
theorem B1536617 : Blo 908576 1536617 := bstep (se 2 (by rfl) ⟨576231, by rfl⟩ : syracuseStep 1536617 = 1152463) B1152463
theorem B3076919 : Blo 908576 3076919 := bstep (se 1 (by rfl) ⟨2307689, by rfl⟩ : syracuseStep 3076919 = 4615379) B4615379
theorem B3077999 : Blo 908576 3077999 := bstep (se 1 (by rfl) ⟨2308499, by rfl⟩ : syracuseStep 3077999 = 4616999) B4616999
theorem B1538473 : Blo 908576 1538473 := bstep (se 2 (by rfl) ⟨576927, by rfl⟩ : syracuseStep 1538473 = 1153855) B1153855
theorem B4618943 : Blo 908576 4618943 := bstep (se 1 (by rfl) ⟨3464207, by rfl⟩ : syracuseStep 4618943 = 6928415) B6928415
theorem B66550531 : Blo 908576 66550531 := bstep (se 1 (by rfl) ⟨49912898, by rfl⟩ : syracuseStep 66550531 = 99825797) B99825797
theorem B7764943 : Blo 908576 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B7765217 : Blo 908576 7765217 := bstep (se 2 (by rfl) ⟨2911956, by rfl⟩ : syracuseStep 7765217 = 5823913) B5823913
theorem B3079727 : Blo 908576 3079727 := bstep (se 1 (by rfl) ⟨2309795, by rfl⟩ : syracuseStep 3079727 = 4619591) B4619591
theorem B7899707 : Blo 908576 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B16586207 : Blo 908576 16586207 := bstep (se 1 (by rfl) ⟨12439655, by rfl⟩ : syracuseStep 16586207 = 24879311) B24879311
theorem B3512089 : Blo 908576 3512089 := bstep (se 2 (by rfl) ⟨1317033, by rfl⟩ : syracuseStep 3512089 = 2634067) B2634067
theorem B1022431 : Blo 908576 1022431 := bstep (se 1 (by rfl) ⟨766823, by rfl⟩ : syracuseStep 1022431 = 1533647) B1533647
theorem B35035739 : Blo 908576 35035739 := bstep (se 1 (by rfl) ⟨26276804, by rfl⟩ : syracuseStep 35035739 = 52553609) B52553609
theorem B2596607 : Blo 908576 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B1024411 : Blo 908576 1024411 := bstep (se 1 (by rfl) ⟨768308, by rfl⟩ : syracuseStep 1024411 = 1536617) B1536617
theorem B23930633 : Blo 908576 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B10366379 : Blo 908576 10366379 := bstep (se 1 (by rfl) ⟨7774784, by rfl⟩ : syracuseStep 10366379 = 15549569) B15549569
theorem B2045807 : Blo 908576 2045807 := bstep (se 1 (by rfl) ⟨1534355, by rfl⟩ : syracuseStep 2045807 = 3068711) B3068711
theorem B5192531 : Blo 908576 5192531 := bstep (se 1 (by rfl) ⟨3894398, by rfl⟩ : syracuseStep 5192531 = 7788797) B7788797
theorem B1457119 : Blo 908576 1457119 := bstep (se 1 (by rfl) ⟨1092839, by rfl⟩ : syracuseStep 1457119 = 2185679) B2185679
theorem B2048183 : Blo 908576 2048183 := bstep (se 1 (by rfl) ⟨1536137, by rfl⟩ : syracuseStep 2048183 = 3072275) B3072275
theorem B49758761 : Blo 908576 49758761 := bstep (se 2 (by rfl) ⟨18659535, by rfl⟩ : syracuseStep 49758761 = 37319071) B37319071
theorem B4671599 : Blo 908576 4671599 := bstep (se 1 (by rfl) ⟨3503699, by rfl⟩ : syracuseStep 4671599 = 7007399) B7007399
theorem B11094583 : Blo 908576 11094583 := bstep (se 1 (by rfl) ⟨8320937, by rfl⟩ : syracuseStep 11094583 = 16641875) B16641875
theorem B1363103 : Blo 908576 1363103 := bstep (se 1 (by rfl) ⟨1022327, by rfl⟩ : syracuseStep 1363103 = 2044655) B2044655
theorem B2051279 : Blo 908576 2051279 := bstep (se 1 (by rfl) ⟨1538459, by rfl⟩ : syracuseStep 2051279 = 3076919) B3076919
theorem B2051297 : Blo 908576 2051297 := bstep (se 2 (by rfl) ⟨769236, by rfl⟩ : syracuseStep 2051297 = 1538473) B1538473
theorem B718294877 : Blo 908576 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B2051999 : Blo 908576 2051999 := bstep (se 1 (by rfl) ⟨1538999, by rfl⟩ : syracuseStep 2051999 = 3077999) B3077999
theorem B2053151 : Blo 908576 2053151 := bstep (se 1 (by rfl) ⟨1539863, by rfl⟩ : syracuseStep 2053151 = 3079727) B3079727
theorem B1365275 : Blo 908576 1365275 := bstep (se 1 (by rfl) ⟨1023956, by rfl⟩ : syracuseStep 1365275 = 2047913) B2047913
theorem B4675319 : Blo 908576 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B1726363 : Blo 908576 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1366511 : Blo 908576 1366511 := bstep (se 1 (by rfl) ⟨1024883, by rfl⟩ : syracuseStep 1366511 = 2049767) B2049767
theorem B1727183 : Blo 908576 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B1367279 : Blo 908576 1367279 := bstep (se 1 (by rfl) ⟨1025459, by rfl⟩ : syracuseStep 1367279 = 2050919) B2050919
theorem B1367945 : Blo 908576 1367945 := bstep (se 2 (by rfl) ⟨512979, by rfl⟩ : syracuseStep 1367945 = 1025959) B1025959
theorem B1368239 : Blo 908576 1368239 := bstep (se 1 (by rfl) ⟨1026179, by rfl⟩ : syracuseStep 1368239 = 2052359) B2052359
theorem B1729279 : Blo 908576 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B910591 : Blo 908576 910591 := bstep (se 1 (by rfl) ⟨682943, by rfl⟩ : syracuseStep 910591 = 1365887) B1365887
theorem B99706697 : Blo 908576 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B912487 : Blo 908576 912487 := bstep (se 1 (by rfl) ⟨684365, by rfl⟩ : syracuseStep 912487 = 1368731) B1368731
theorem B233270513 : Blo 908576 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B21000485 : Blo 908576 21000485 := bstep (se 4 (by rfl) ⟨1968795, by rfl⟩ : syracuseStep 21000485 = 3937591) B3937591
theorem B22410053 : Blo 908576 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B88734041 : Blo 908576 88734041 := bstep (se 2 (by rfl) ⟨33275265, by rfl⟩ : syracuseStep 88734041 = 66550531) B66550531
theorem B10353257 : Blo 908576 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B3079295 : Blo 908576 3079295 := bstep (se 1 (by rfl) ⟨2309471, by rfl⟩ : syracuseStep 3079295 = 4618943) B4618943
theorem B5176811 : Blo 908576 5176811 := bstep (se 1 (by rfl) ⟨3882608, by rfl⟩ : syracuseStep 5176811 = 7765217) B7765217
theorem B56001293 : Blo 908576 56001293 := bstep (se 3 (by rfl) ⟨10500242, by rfl⟩ : syracuseStep 56001293 = 21000485) B21000485
theorem B3116879 : Blo 908576 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B7771301 : Blo 908576 7771301 := bstep (se 4 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 7771301 = 1457119) B1457119
theorem B12457597 : Blo 908576 12457597 := bstep (se 3 (by rfl) ⟨2335799, by rfl⟩ : syracuseStep 12457597 = 4671599) B4671599
theorem B2301817 : Blo 908576 2301817 := bstep (se 2 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 2301817 = 1726363) B1726363
theorem B59156027 : Blo 908576 59156027 := bstep (se 1 (by rfl) ⟨44367020, by rfl⟩ : syracuseStep 59156027 = 88734041) B88734041
theorem B3451207 : Blo 908576 3451207 := bstep (se 1 (by rfl) ⟨2588405, by rfl⟩ : syracuseStep 3451207 = 5176811) B5176811
theorem B33172507 : Blo 908576 33172507 := bstep (se 1 (by rfl) ⟨24879380, by rfl⟩ : syracuseStep 33172507 = 49758761) B49758761
theorem B2305705 : Blo 908576 2305705 := bstep (se 2 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 2305705 = 1729279) B1729279
theorem B14792777 : Blo 908576 14792777 := bstep (se 2 (by rfl) ⟨5547291, by rfl⟩ : syracuseStep 14792777 = 11094583) B11094583
theorem B11057471 : Blo 908576 11057471 := bstep (se 1 (by rfl) ⟨8293103, by rfl⟩ : syracuseStep 11057471 = 16586207) B16586207
theorem B66471131 : Blo 908576 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B4605821 : Blo 908576 4605821 := bstep (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) B1727183
theorem B1363241 : Blo 908576 1363241 := bstep (se 2 (by rfl) ⟨511215, by rfl⟩ : syracuseStep 1363241 = 1022431) B1022431
theorem B1363871 : Blo 908576 1363871 := bstep (se 1 (by rfl) ⟨1022903, by rfl⟩ : syracuseStep 1363871 = 2045807) B2045807
theorem B6902171 : Blo 908576 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B3461687 : Blo 908576 3461687 := bstep (se 1 (by rfl) ⟨2596265, by rfl⟩ : syracuseStep 3461687 = 5192531) B5192531
theorem B2052863 : Blo 908576 2052863 := bstep (se 1 (by rfl) ⟨1539647, by rfl⟩ : syracuseStep 2052863 = 3079295) B3079295
theorem B1365455 : Blo 908576 1365455 := bstep (se 1 (by rfl) ⟨1024091, by rfl⟩ : syracuseStep 1365455 = 2048183) B2048183
theorem B1365881 : Blo 908576 1365881 := bstep (se 2 (by rfl) ⟨512205, by rfl⟩ : syracuseStep 1365881 = 1024411) B1024411
theorem B5266471 : Blo 908576 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B908735 : Blo 908576 908735 := bstep (se 1 (by rfl) ⟨681551, by rfl⟩ : syracuseStep 908735 = 1363103) B1363103
theorem B1367519 : Blo 908576 1367519 := bstep (se 1 (by rfl) ⟨1025639, by rfl⟩ : syracuseStep 1367519 = 2051279) B2051279
theorem B1367531 : Blo 908576 1367531 := bstep (se 1 (by rfl) ⟨1025648, by rfl⟩ : syracuseStep 1367531 = 2051297) B2051297
theorem B478863251 : Blo 908576 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B1367999 : Blo 908576 1367999 := bstep (se 1 (by rfl) ⟨1025999, by rfl⟩ : syracuseStep 1367999 = 2051999) B2051999
theorem B1368767 : Blo 908576 1368767 := bstep (se 1 (by rfl) ⟨1026575, by rfl⟩ : syracuseStep 1368767 = 2053151) B2053151
theorem B910183 : Blo 908576 910183 := bstep (se 1 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 910183 = 1365275) B1365275
theorem B911007 : Blo 908576 911007 := bstep (se 1 (by rfl) ⟨683255, by rfl⟩ : syracuseStep 911007 = 1366511) B1366511
theorem B23357159 : Blo 908576 23357159 := bstep (se 1 (by rfl) ⟨17517869, by rfl⟩ : syracuseStep 23357159 = 35035739) B35035739
theorem B911519 : Blo 908576 911519 := bstep (se 1 (by rfl) ⟨683639, by rfl⟩ : syracuseStep 911519 = 1367279) B1367279
theorem B1731071 : Blo 908576 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B911963 : Blo 908576 911963 := bstep (se 1 (by rfl) ⟨683972, by rfl⟩ : syracuseStep 911963 = 1367945) B1367945
theorem B912159 : Blo 908576 912159 := bstep (se 1 (by rfl) ⟨684119, by rfl⟩ : syracuseStep 912159 = 1368239) B1368239
theorem B15953755 : Blo 908576 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B155513675 : Blo 908576 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B6910919 : Blo 908576 6910919 := bstep (se 1 (by rfl) ⟨5183189, by rfl⟩ : syracuseStep 6910919 = 10366379) B10366379
theorem B4682785 : Blo 908576 4682785 := bstep (se 2 (by rfl) ⟨1756044, by rfl⟩ : syracuseStep 4682785 = 3512089) B3512089
theorem B14940035 : Blo 908576 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B5180867 : Blo 908576 5180867 := bstep (se 1 (by rfl) ⟨3885650, by rfl⟩ : syracuseStep 5180867 = 7771301) B7771301
theorem B21271673 : Blo 908576 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B15571439 : Blo 908576 15571439 := bstep (se 1 (by rfl) ⟨11678579, by rfl⟩ : syracuseStep 15571439 = 23357159) B23357159
theorem B7021961 : Blo 908576 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B37334195 : Blo 908576 37334195 := bstep (se 1 (by rfl) ⟨28000646, by rfl⟩ : syracuseStep 37334195 = 56001293) B56001293
theorem B44314087 : Blo 908576 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B2077919 : Blo 908576 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B4601447 : Blo 908576 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B2307791 : Blo 908576 2307791 := bstep (se 1 (by rfl) ⟨1730843, by rfl⟩ : syracuseStep 2307791 = 3461687) B3461687
theorem B4601609 : Blo 908576 4601609 := bstep (se 2 (by rfl) ⟨1725603, by rfl⟩ : syracuseStep 4601609 = 3451207) B3451207
theorem B319242167 : Blo 908576 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B39437351 : Blo 908576 39437351 := bstep (se 1 (by rfl) ⟨29578013, by rfl⟩ : syracuseStep 39437351 = 59156027) B59156027
theorem B6243713 : Blo 908576 6243713 := bstep (se 2 (by rfl) ⟨2341392, by rfl⟩ : syracuseStep 6243713 = 4682785) B4682785
theorem B4607279 : Blo 908576 4607279 := bstep (se 1 (by rfl) ⟨3455459, by rfl⟩ : syracuseStep 4607279 = 6910919) B6910919
theorem B3069089 : Blo 908576 3069089 := bstep (se 2 (by rfl) ⟨1150908, by rfl⟩ : syracuseStep 3069089 = 2301817) B2301817
theorem B3070547 : Blo 908576 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B908827 : Blo 908576 908827 := bstep (se 1 (by rfl) ⟨681620, by rfl⟩ : syracuseStep 908827 = 1363241) B1363241
theorem B909247 : Blo 908576 909247 := bstep (se 1 (by rfl) ⟨681935, by rfl⟩ : syracuseStep 909247 = 1363871) B1363871
theorem B1368575 : Blo 908576 1368575 := bstep (se 1 (by rfl) ⟨1026431, by rfl⟩ : syracuseStep 1368575 = 2052863) B2052863
theorem B910303 : Blo 908576 910303 := bstep (se 1 (by rfl) ⟨682727, by rfl⟩ : syracuseStep 910303 = 1365455) B1365455
theorem B910587 : Blo 908576 910587 := bstep (se 1 (by rfl) ⟨682940, by rfl⟩ : syracuseStep 910587 = 1365881) B1365881
theorem B44230009 : Blo 908576 44230009 := bstep (se 2 (by rfl) ⟨16586253, by rfl⟩ : syracuseStep 44230009 = 33172507) B33172507
theorem B3074273 : Blo 908576 3074273 := bstep (se 2 (by rfl) ⟨1152852, by rfl⟩ : syracuseStep 3074273 = 2305705) B2305705
theorem B911679 : Blo 908576 911679 := bstep (se 1 (by rfl) ⟨683759, by rfl⟩ : syracuseStep 911679 = 1367519) B1367519
theorem B911687 : Blo 908576 911687 := bstep (se 1 (by rfl) ⟨683765, by rfl⟩ : syracuseStep 911687 = 1367531) B1367531
theorem B911999 : Blo 908576 911999 := bstep (se 1 (by rfl) ⟨683999, by rfl⟩ : syracuseStep 911999 = 1367999) B1367999
theorem B912511 : Blo 908576 912511 := bstep (se 1 (by rfl) ⟨684383, by rfl⟩ : syracuseStep 912511 = 1368767) B1368767
theorem B4616189 : Blo 908576 4616189 := bstep (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) B1731071
theorem B16610129 : Blo 908576 16610129 := bstep (se 2 (by rfl) ⟨6228798, by rfl⟩ : syracuseStep 16610129 = 12457597) B12457597
theorem B103675783 : Blo 908576 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B9960023 : Blo 908576 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B9861851 : Blo 908576 9861851 := bstep (se 1 (by rfl) ⟨7396388, by rfl⟩ : syracuseStep 9861851 = 14792777) B14792777
theorem B7371647 : Blo 908576 7371647 := bstep (se 1 (by rfl) ⟨5528735, by rfl⟩ : syracuseStep 7371647 = 11057471) B11057471
theorem B4162475 : Blo 908576 4162475 := bstep (se 1 (by rfl) ⟨3121856, by rfl⟩ : syracuseStep 4162475 = 6243713) B6243713
theorem B56724461 : Blo 908576 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B59085449 : Blo 908576 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B1385279 : Blo 908576 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B26291567 : Blo 908576 26291567 := bstep (se 1 (by rfl) ⟨19718675, by rfl⟩ : syracuseStep 26291567 = 39437351) B39437351
theorem B3453911 : Blo 908576 3453911 := bstep (se 1 (by rfl) ⟨2590433, by rfl⟩ : syracuseStep 3453911 = 5180867) B5180867
theorem B2046059 : Blo 908576 2046059 := bstep (se 1 (by rfl) ⟨1534544, by rfl⟩ : syracuseStep 2046059 = 3069089) B3069089
theorem B2047031 : Blo 908576 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B2049515 : Blo 908576 2049515 := bstep (se 1 (by rfl) ⟨1537136, by rfl⟩ : syracuseStep 2049515 = 3074273) B3074273
theorem B24889463 : Blo 908576 24889463 := bstep (se 1 (by rfl) ⟨18667097, by rfl⟩ : syracuseStep 24889463 = 37334195) B37334195
theorem B138234377 : Blo 908576 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B3067631 : Blo 908576 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B3067739 : Blo 908576 3067739 := bstep (se 1 (by rfl) ⟨2300804, by rfl⟩ : syracuseStep 3067739 = 4601609) B4601609
theorem B6640015 : Blo 908576 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B6574567 : Blo 908576 6574567 := bstep (se 1 (by rfl) ⟨4930925, by rfl⟩ : syracuseStep 6574567 = 9861851) B9861851
theorem B58973345 : Blo 908576 58973345 := bstep (se 2 (by rfl) ⟨22115004, by rfl⟩ : syracuseStep 58973345 = 44230009) B44230009
theorem B3071519 : Blo 908576 3071519 := bstep (se 1 (by rfl) ⟨2303639, by rfl⟩ : syracuseStep 3071519 = 4607279) B4607279
theorem B10380959 : Blo 908576 10380959 := bstep (se 1 (by rfl) ⟨7785719, by rfl⟩ : syracuseStep 10380959 = 15571439) B15571439
theorem B912383 : Blo 908576 912383 := bstep (se 1 (by rfl) ⟨684287, by rfl⟩ : syracuseStep 912383 = 1368575) B1368575
theorem B4681307 : Blo 908576 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B3077459 : Blo 908576 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B11073419 : Blo 908576 11073419 := bstep (se 1 (by rfl) ⟨8305064, by rfl⟩ : syracuseStep 11073419 = 16610129) B16610129
theorem B1538527 : Blo 908576 1538527 := bstep (se 1 (by rfl) ⟨1153895, by rfl⟩ : syracuseStep 1538527 = 2307791) B2307791
theorem B4914431 : Blo 908576 4914431 := bstep (se 1 (by rfl) ⟨3685823, by rfl⟩ : syracuseStep 4914431 = 7371647) B7371647
theorem B212828111 : Blo 908576 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B37816307 : Blo 908576 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B39390299 : Blo 908576 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B8853353 : Blo 908576 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B923519 : Blo 908576 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B6920639 : Blo 908576 6920639 := bstep (se 1 (by rfl) ⟨5190479, by rfl⟩ : syracuseStep 6920639 = 10380959) B10380959
theorem B3120871 : Blo 908576 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B2302607 : Blo 908576 2302607 := bstep (se 1 (by rfl) ⟨1726955, by rfl⟩ : syracuseStep 2302607 = 3453911) B3453911
theorem B7382279 : Blo 908576 7382279 := bstep (se 1 (by rfl) ⟨5536709, by rfl⟩ : syracuseStep 7382279 = 11073419) B11073419
theorem B16592975 : Blo 908576 16592975 := bstep (se 1 (by rfl) ⟨12444731, by rfl⟩ : syracuseStep 16592975 = 24889463) B24889463
theorem B92156251 : Blo 908576 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B2045087 : Blo 908576 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B2045159 : Blo 908576 2045159 := bstep (se 1 (by rfl) ⟨1533869, by rfl⟩ : syracuseStep 2045159 = 3067739) B3067739
theorem B2047679 : Blo 908576 2047679 := bstep (se 1 (by rfl) ⟨1535759, by rfl⟩ : syracuseStep 2047679 = 3071519) B3071519
theorem B8766089 : Blo 908576 8766089 := bstep (se 2 (by rfl) ⟨3287283, by rfl⟩ : syracuseStep 8766089 = 6574567) B6574567
theorem B2051369 : Blo 908576 2051369 := bstep (se 2 (by rfl) ⟨769263, by rfl⟩ : syracuseStep 2051369 = 1538527) B1538527
theorem B2051639 : Blo 908576 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B1364039 : Blo 908576 1364039 := bstep (se 1 (by rfl) ⟨1023029, by rfl⟩ : syracuseStep 1364039 = 2046059) B2046059
theorem B1364687 : Blo 908576 1364687 := bstep (se 1 (by rfl) ⟨1023515, by rfl⟩ : syracuseStep 1364687 = 2047031) B2047031
theorem B2774983 : Blo 908576 2774983 := bstep (se 1 (by rfl) ⟨2081237, by rfl⟩ : syracuseStep 2774983 = 4162475) B4162475
theorem B1366343 : Blo 908576 1366343 := bstep (se 1 (by rfl) ⟨1024757, by rfl⟩ : syracuseStep 1366343 = 2049515) B2049515
theorem B39315563 : Blo 908576 39315563 := bstep (se 1 (by rfl) ⟨29486672, by rfl⟩ : syracuseStep 39315563 = 58973345) B58973345
theorem B17527711 : Blo 908576 17527711 := bstep (se 1 (by rfl) ⟨13145783, by rfl⟩ : syracuseStep 17527711 = 26291567) B26291567
theorem B3276287 : Blo 908576 3276287 := bstep (se 1 (by rfl) ⟨2457215, by rfl⟩ : syracuseStep 3276287 = 4914431) B4914431
theorem B141885407 : Blo 908576 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B5902235 : Blo 908576 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B2462717 : Blo 908576 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B23370281 : Blo 908576 23370281 := bstep (se 2 (by rfl) ⟨8763855, by rfl⟩ : syracuseStep 23370281 = 17527711) B17527711
theorem B5844059 : Blo 908576 5844059 := bstep (se 1 (by rfl) ⟨4383044, by rfl⟩ : syracuseStep 5844059 = 8766089) B8766089
theorem B25210871 : Blo 908576 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B26260199 : Blo 908576 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B11061983 : Blo 908576 11061983 := bstep (se 1 (by rfl) ⟨8296487, by rfl⟩ : syracuseStep 11061983 = 16592975) B16592975
theorem B1363391 : Blo 908576 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B1363439 : Blo 908576 1363439 := bstep (se 1 (by rfl) ⟨1022579, by rfl⟩ : syracuseStep 1363439 = 2045159) B2045159
theorem B2184191 : Blo 908576 2184191 := bstep (se 1 (by rfl) ⟨1638143, by rfl⟩ : syracuseStep 2184191 = 3276287) B3276287
theorem B1365119 : Blo 908576 1365119 := bstep (se 1 (by rfl) ⟨1023839, by rfl⟩ : syracuseStep 1365119 = 2047679) B2047679
theorem B94590271 : Blo 908576 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B1367579 : Blo 908576 1367579 := bstep (se 1 (by rfl) ⟨1025684, by rfl⟩ : syracuseStep 1367579 = 2051369) B2051369
theorem B1367759 : Blo 908576 1367759 := bstep (se 1 (by rfl) ⟨1025819, by rfl⟩ : syracuseStep 1367759 = 2051639) B2051639
theorem B909359 : Blo 908576 909359 := bstep (se 1 (by rfl) ⟨682019, by rfl⟩ : syracuseStep 909359 = 1364039) B1364039
theorem B909791 : Blo 908576 909791 := bstep (se 1 (by rfl) ⟨682343, by rfl⟩ : syracuseStep 909791 = 1364687) B1364687
theorem B19686077 : Blo 908576 19686077 := bstep (se 3 (by rfl) ⟨3691139, by rfl⟩ : syracuseStep 19686077 = 7382279) B7382279
theorem B910895 : Blo 908576 910895 := bstep (se 1 (by rfl) ⟨683171, by rfl⟩ : syracuseStep 910895 = 1366343) B1366343
theorem B4613759 : Blo 908576 4613759 := bstep (se 1 (by rfl) ⟨3460319, by rfl⟩ : syracuseStep 4613759 = 6920639) B6920639
theorem B1535071 : Blo 908576 1535071 := bstep (se 1 (by rfl) ⟨1151303, by rfl⟩ : syracuseStep 1535071 = 2302607) B2302607
theorem B122875001 : Blo 908576 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B26210375 : Blo 908576 26210375 := bstep (se 1 (by rfl) ⟨19657781, by rfl⟩ : syracuseStep 26210375 = 39315563) B39315563
theorem B3699977 : Blo 908576 3699977 := bstep (se 2 (by rfl) ⟨1387491, by rfl⟩ : syracuseStep 3699977 = 2774983) B2774983
theorem B4161161 : Blo 908576 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B7374655 : Blo 908576 7374655 := bstep (se 1 (by rfl) ⟨5530991, by rfl⟩ : syracuseStep 7374655 = 11061983) B11061983
theorem B3934823 : Blo 908576 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B1641811 : Blo 908576 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B9866605 : Blo 908576 9866605 := bstep (se 3 (by rfl) ⟨1849988, by rfl⟩ : syracuseStep 9866605 = 3699977) B3699977
theorem B17473583 : Blo 908576 17473583 := bstep (se 1 (by rfl) ⟨13105187, by rfl⟩ : syracuseStep 17473583 = 26210375) B26210375
theorem B17506799 : Blo 908576 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B1456127 : Blo 908576 1456127 := bstep (se 1 (by rfl) ⟨1092095, by rfl⟩ : syracuseStep 1456127 = 2184191) B2184191
theorem B2046761 : Blo 908576 2046761 := bstep (se 2 (by rfl) ⟨767535, by rfl⟩ : syracuseStep 2046761 = 1535071) B1535071
theorem B15580187 : Blo 908576 15580187 := bstep (se 1 (by rfl) ⟨11685140, by rfl⟩ : syracuseStep 15580187 = 23370281) B23370281
theorem B13124051 : Blo 908576 13124051 := bstep (se 1 (by rfl) ⟨9843038, by rfl⟩ : syracuseStep 13124051 = 19686077) B19686077
theorem B2774107 : Blo 908576 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B908927 : Blo 908576 908927 := bstep (se 1 (by rfl) ⟨681695, by rfl⟩ : syracuseStep 908927 = 1363391) B1363391
theorem B908959 : Blo 908576 908959 := bstep (se 1 (by rfl) ⟨681719, by rfl⟩ : syracuseStep 908959 = 1363439) B1363439
theorem B910079 : Blo 908576 910079 := bstep (se 1 (by rfl) ⟨682559, by rfl⟩ : syracuseStep 910079 = 1365119) B1365119
theorem B911719 : Blo 908576 911719 := bstep (se 1 (by rfl) ⟨683789, by rfl⟩ : syracuseStep 911719 = 1367579) B1367579
theorem B911839 : Blo 908576 911839 := bstep (se 1 (by rfl) ⟨683879, by rfl⟩ : syracuseStep 911839 = 1367759) B1367759
theorem B3075839 : Blo 908576 3075839 := bstep (se 1 (by rfl) ⟨2306879, by rfl⟩ : syracuseStep 3075839 = 4613759) B4613759
theorem B126120361 : Blo 908576 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B3896039 : Blo 908576 3896039 := bstep (se 1 (by rfl) ⟨2922029, by rfl⟩ : syracuseStep 3896039 = 5844059) B5844059
theorem B81916667 : Blo 908576 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B16807247 : Blo 908576 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B8749367 : Blo 908576 8749367 := bstep (se 1 (by rfl) ⟨6562025, by rfl⟩ : syracuseStep 8749367 = 13124051) B13124051
theorem B9832873 : Blo 908576 9832873 := bstep (se 2 (by rfl) ⟨3687327, by rfl⟩ : syracuseStep 9832873 = 7374655) B7374655
theorem B11671199 : Blo 908576 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B10492861 : Blo 908576 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B2597359 : Blo 908576 2597359 := bstep (se 1 (by rfl) ⟨1948019, by rfl⟩ : syracuseStep 2597359 = 3896039) B3896039
theorem B13155473 : Blo 908576 13155473 := bstep (se 2 (by rfl) ⟨4933302, by rfl⟩ : syracuseStep 13155473 = 9866605) B9866605
theorem B11649055 : Blo 908576 11649055 := bstep (se 1 (by rfl) ⟨8736791, by rfl⟩ : syracuseStep 11649055 = 17473583) B17473583
theorem B14795237 : Blo 908576 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B2050559 : Blo 908576 2050559 := bstep (se 1 (by rfl) ⟨1537919, by rfl⟩ : syracuseStep 2050559 = 3075839) B3075839
theorem B54611111 : Blo 908576 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B970751 : Blo 908576 970751 := bstep (se 1 (by rfl) ⟨728063, by rfl⟩ : syracuseStep 970751 = 1456127) B1456127
theorem B1364507 : Blo 908576 1364507 := bstep (se 1 (by rfl) ⟨1023380, by rfl⟩ : syracuseStep 1364507 = 2046761) B2046761
theorem B2189081 : Blo 908576 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B168160481 : Blo 908576 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B11204831 : Blo 908576 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B10386791 : Blo 908576 10386791 := bstep (se 1 (by rfl) ⟨7790093, by rfl⟩ : syracuseStep 10386791 = 15580187) B15580187
theorem B15532073 : Blo 908576 15532073 := bstep (se 2 (by rfl) ⟨5824527, by rfl⟩ : syracuseStep 15532073 = 11649055) B11649055
theorem B5832911 : Blo 908576 5832911 := bstep (se 1 (by rfl) ⟨4374683, by rfl⟩ : syracuseStep 5832911 = 8749367) B8749367
theorem B9863491 : Blo 908576 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B36407407 : Blo 908576 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B13110497 : Blo 908576 13110497 := bstep (se 2 (by rfl) ⟨4916436, by rfl⟩ : syracuseStep 13110497 = 9832873) B9832873
theorem B112106987 : Blo 908576 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B6924527 : Blo 908576 6924527 := bstep (se 1 (by rfl) ⟨5193395, by rfl⟩ : syracuseStep 6924527 = 10386791) B10386791
theorem B7780799 : Blo 908576 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B1459387 : Blo 908576 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B8770315 : Blo 908576 8770315 := bstep (se 1 (by rfl) ⟨6577736, by rfl⟩ : syracuseStep 8770315 = 13155473) B13155473
theorem B3463145 : Blo 908576 3463145 := bstep (se 2 (by rfl) ⟨1298679, by rfl⟩ : syracuseStep 3463145 = 2597359) B2597359
theorem B1367039 : Blo 908576 1367039 := bstep (se 1 (by rfl) ⟨1025279, by rfl⟩ : syracuseStep 1367039 = 2050559) B2050559
theorem B909671 : Blo 908576 909671 := bstep (se 1 (by rfl) ⟨682253, by rfl⟩ : syracuseStep 909671 = 1364507) B1364507
theorem B13990481 : Blo 908576 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B7469887 : Blo 908576 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B2588669 : Blo 908576 2588669 := bstep (se 3 (by rfl) ⟨485375, by rfl⟩ : syracuseStep 2588669 = 970751) B970751
theorem B10354715 : Blo 908576 10354715 := bstep (se 1 (by rfl) ⟨7766036, by rfl⟩ : syracuseStep 10354715 = 15532073) B15532073
theorem B5187199 : Blo 908576 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B13151321 : Blo 908576 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B48543209 : Blo 908576 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B2308763 : Blo 908576 2308763 := bstep (se 1 (by rfl) ⟨1731572, by rfl⟩ : syracuseStep 2308763 = 3463145) B3463145
theorem B7783397 : Blo 908576 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B9326987 : Blo 908576 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B1725779 : Blo 908576 1725779 := bstep (se 1 (by rfl) ⟨1294334, by rfl⟩ : syracuseStep 1725779 = 2588669) B2588669
theorem B3888607 : Blo 908576 3888607 := bstep (se 1 (by rfl) ⟨2916455, by rfl⟩ : syracuseStep 3888607 = 5832911) B5832911
theorem B8740331 : Blo 908576 8740331 := bstep (se 1 (by rfl) ⟨6555248, by rfl⟩ : syracuseStep 8740331 = 13110497) B13110497
theorem B911359 : Blo 908576 911359 := bstep (se 1 (by rfl) ⟨683519, by rfl⟩ : syracuseStep 911359 = 1367039) B1367039
theorem B74737991 : Blo 908576 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B11693753 : Blo 908576 11693753 := bstep (se 2 (by rfl) ⟨4385157, by rfl⟩ : syracuseStep 11693753 = 8770315) B8770315
theorem B4616351 : Blo 908576 4616351 := bstep (se 1 (by rfl) ⟨3462263, by rfl⟩ : syracuseStep 4616351 = 6924527) B6924527
theorem B9959849 : Blo 908576 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B6916265 : Blo 908576 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B1150519 : Blo 908576 1150519 := bstep (se 1 (by rfl) ⟨862889, by rfl⟩ : syracuseStep 1150519 = 1725779) B1725779
theorem B5184809 : Blo 908576 5184809 := bstep (se 2 (by rfl) ⟨1944303, by rfl⟩ : syracuseStep 5184809 = 3888607) B3888607
theorem B5188931 : Blo 908576 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B49825327 : Blo 908576 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B8767547 : Blo 908576 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B32362139 : Blo 908576 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B6639899 : Blo 908576 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B6903143 : Blo 908576 6903143 := bstep (se 1 (by rfl) ⟨5177357, by rfl⟩ : syracuseStep 6903143 = 10354715) B10354715
theorem B6217991 : Blo 908576 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B5826887 : Blo 908576 5826887 := bstep (se 1 (by rfl) ⟨4370165, by rfl⟩ : syracuseStep 5826887 = 8740331) B8740331
theorem B7795835 : Blo 908576 7795835 := bstep (se 1 (by rfl) ⟨5846876, by rfl⟩ : syracuseStep 7795835 = 11693753) B11693753
theorem B3077567 : Blo 908576 3077567 := bstep (se 1 (by rfl) ⟨2308175, by rfl⟩ : syracuseStep 3077567 = 4616351) B4616351
theorem B1539175 : Blo 908576 1539175 := bstep (se 1 (by rfl) ⟨1154381, by rfl⟩ : syracuseStep 1539175 = 2308763) B2308763
theorem B17706397 : Blo 908576 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B5845031 : Blo 908576 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B66433769 : Blo 908576 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B21574759 : Blo 908576 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B4602095 : Blo 908576 4602095 := bstep (se 1 (by rfl) ⟨3451571, by rfl⟩ : syracuseStep 4602095 = 6903143) B6903143
theorem B3456539 : Blo 908576 3456539 := bstep (se 1 (by rfl) ⟨2592404, by rfl⟩ : syracuseStep 3456539 = 5184809) B5184809
theorem B4145327 : Blo 908576 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B3884591 : Blo 908576 3884591 := bstep (se 1 (by rfl) ⟨2913443, by rfl⟩ : syracuseStep 3884591 = 5826887) B5826887
theorem B3459287 : Blo 908576 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B5197223 : Blo 908576 5197223 := bstep (se 1 (by rfl) ⟨3897917, by rfl⟩ : syracuseStep 5197223 = 7795835) B7795835
theorem B2051711 : Blo 908576 2051711 := bstep (se 1 (by rfl) ⟨1538783, by rfl⟩ : syracuseStep 2051711 = 3077567) B3077567
theorem B2052233 : Blo 908576 2052233 := bstep (se 2 (by rfl) ⟨769587, by rfl⟩ : syracuseStep 2052233 = 1539175) B1539175
theorem B4610843 : Blo 908576 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B1534025 : Blo 908576 1534025 := bstep (se 2 (by rfl) ⟨575259, by rfl⟩ : syracuseStep 1534025 = 1150519) B1150519
theorem B2589727 : Blo 908576 2589727 := bstep (se 1 (by rfl) ⟨1942295, by rfl⟩ : syracuseStep 2589727 = 3884591) B3884591
theorem B1022683 : Blo 908576 1022683 := bstep (se 1 (by rfl) ⟨767012, by rfl⟩ : syracuseStep 1022683 = 1534025) B1534025
theorem B2304359 : Blo 908576 2304359 := bstep (se 1 (by rfl) ⟨1728269, by rfl⟩ : syracuseStep 2304359 = 3456539) B3456539
theorem B2763551 : Blo 908576 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B2306191 : Blo 908576 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B23608529 : Blo 908576 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B44289179 : Blo 908576 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B3068063 : Blo 908576 3068063 := bstep (se 1 (by rfl) ⟨2301047, by rfl⟩ : syracuseStep 3068063 = 4602095) B4602095
theorem B3464815 : Blo 908576 3464815 := bstep (se 1 (by rfl) ⟨2598611, by rfl⟩ : syracuseStep 3464815 = 5197223) B5197223
theorem B1367807 : Blo 908576 1367807 := bstep (se 1 (by rfl) ⟨1025855, by rfl⟩ : syracuseStep 1367807 = 2051711) B2051711
theorem B1368155 : Blo 908576 1368155 := bstep (se 1 (by rfl) ⟨1026116, by rfl⟩ : syracuseStep 1368155 = 2052233) B2052233
theorem B3073895 : Blo 908576 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B28766345 : Blo 908576 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B3896687 : Blo 908576 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B76710253 : Blo 908576 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B29526119 : Blo 908576 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B10391165 : Blo 908576 10391165 := bstep (se 3 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 10391165 = 3896687) B3896687
theorem B1842367 : Blo 908576 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B15739019 : Blo 908576 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B3452969 : Blo 908576 3452969 := bstep (se 2 (by rfl) ⟨1294863, by rfl⟩ : syracuseStep 3452969 = 2589727) B2589727
theorem B2045375 : Blo 908576 2045375 := bstep (se 1 (by rfl) ⟨1534031, by rfl⟩ : syracuseStep 2045375 = 3068063) B3068063
theorem B2049263 : Blo 908576 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B1363577 : Blo 908576 1363577 := bstep (se 2 (by rfl) ⟨511341, by rfl⟩ : syracuseStep 1363577 = 1022683) B1022683
theorem B911871 : Blo 908576 911871 := bstep (se 1 (by rfl) ⟨683903, by rfl⟩ : syracuseStep 911871 = 1367807) B1367807
theorem B912103 : Blo 908576 912103 := bstep (se 1 (by rfl) ⟨684077, by rfl⟩ : syracuseStep 912103 = 1368155) B1368155
theorem B3074921 : Blo 908576 3074921 := bstep (se 2 (by rfl) ⟨1153095, by rfl⟩ : syracuseStep 3074921 = 2306191) B2306191
theorem B1536239 : Blo 908576 1536239 := bstep (se 1 (by rfl) ⟨1152179, by rfl⟩ : syracuseStep 1536239 = 2304359) B2304359
theorem B4619753 : Blo 908576 4619753 := bstep (se 2 (by rfl) ⟨1732407, by rfl⟩ : syracuseStep 4619753 = 3464815) B3464815
theorem B10492679 : Blo 908576 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B2301979 : Blo 908576 2301979 := bstep (se 1 (by rfl) ⟨1726484, by rfl⟩ : syracuseStep 2301979 = 3452969) B3452969
theorem B1024159 : Blo 908576 1024159 := bstep (se 1 (by rfl) ⟨768119, by rfl⟩ : syracuseStep 1024159 = 1536239) B1536239
theorem B102280337 : Blo 908576 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B6927443 : Blo 908576 6927443 := bstep (se 1 (by rfl) ⟨5195582, by rfl⟩ : syracuseStep 6927443 = 10391165) B10391165
theorem B2049947 : Blo 908576 2049947 := bstep (se 1 (by rfl) ⟨1537460, by rfl⟩ : syracuseStep 2049947 = 3074921) B3074921
theorem B1363583 : Blo 908576 1363583 := bstep (se 1 (by rfl) ⟨1022687, by rfl⟩ : syracuseStep 1363583 = 2045375) B2045375
theorem B1366175 : Blo 908576 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B19684079 : Blo 908576 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B909051 : Blo 908576 909051 := bstep (se 1 (by rfl) ⟨681788, by rfl⟩ : syracuseStep 909051 = 1363577) B1363577
theorem B2456489 : Blo 908576 2456489 := bstep (se 2 (by rfl) ⟨921183, by rfl⟩ : syracuseStep 2456489 = 1842367) B1842367
theorem B3079835 : Blo 908576 3079835 := bstep (se 1 (by rfl) ⟨2309876, by rfl⟩ : syracuseStep 3079835 = 4619753) B4619753
theorem B13122719 : Blo 908576 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B6995119 : Blo 908576 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B2053223 : Blo 908576 2053223 := bstep (se 1 (by rfl) ⟨1539917, by rfl⟩ : syracuseStep 2053223 = 3079835) B3079835
theorem B3069305 : Blo 908576 3069305 := bstep (se 2 (by rfl) ⟨1150989, by rfl⟩ : syracuseStep 3069305 = 2301979) B2301979
theorem B1365545 : Blo 908576 1365545 := bstep (se 2 (by rfl) ⟨512079, by rfl⟩ : syracuseStep 1365545 = 1024159) B1024159
theorem B1366631 : Blo 908576 1366631 := bstep (se 1 (by rfl) ⟨1024973, by rfl⟩ : syracuseStep 1366631 = 2049947) B2049947
theorem B909055 : Blo 908576 909055 := bstep (se 1 (by rfl) ⟨681791, by rfl⟩ : syracuseStep 909055 = 1363583) B1363583
theorem B910783 : Blo 908576 910783 := bstep (se 1 (by rfl) ⟨683087, by rfl⟩ : syracuseStep 910783 = 1366175) B1366175
theorem B68186891 : Blo 908576 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B4618295 : Blo 908576 4618295 := bstep (se 1 (by rfl) ⟨3463721, by rfl⟩ : syracuseStep 4618295 = 6927443) B6927443
theorem B1637659 : Blo 908576 1637659 := bstep (se 1 (by rfl) ⟨1228244, by rfl⟩ : syracuseStep 1637659 = 2456489) B2456489
theorem B181831709 : Blo 908576 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B2046203 : Blo 908576 2046203 := bstep (se 1 (by rfl) ⟨1534652, by rfl⟩ : syracuseStep 2046203 = 3069305) B3069305
theorem B9326825 : Blo 908576 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B2183545 : Blo 908576 2183545 := bstep (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) B1637659
theorem B1368815 : Blo 908576 1368815 := bstep (se 1 (by rfl) ⟨1026611, by rfl⟩ : syracuseStep 1368815 = 2053223) B2053223
theorem B910363 : Blo 908576 910363 := bstep (se 1 (by rfl) ⟨682772, by rfl⟩ : syracuseStep 910363 = 1365545) B1365545
theorem B911087 : Blo 908576 911087 := bstep (se 1 (by rfl) ⟨683315, by rfl⟩ : syracuseStep 911087 = 1366631) B1366631
theorem B3078863 : Blo 908576 3078863 := bstep (se 1 (by rfl) ⟨2309147, by rfl⟩ : syracuseStep 3078863 = 4618295) B4618295
theorem B8748479 : Blo 908576 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B121221139 : Blo 908576 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B1364135 : Blo 908576 1364135 := bstep (se 1 (by rfl) ⟨1023101, by rfl⟩ : syracuseStep 1364135 = 2046203) B2046203
theorem B2052575 : Blo 908576 2052575 := bstep (se 1 (by rfl) ⟨1539431, by rfl⟩ : syracuseStep 2052575 = 3078863) B3078863
theorem B6217883 : Blo 908576 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B912543 : Blo 908576 912543 := bstep (se 1 (by rfl) ⟨684407, by rfl⟩ : syracuseStep 912543 = 1368815) B1368815
theorem B2911393 : Blo 908576 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B5832319 : Blo 908576 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B7776425 : Blo 908576 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B3881857 : Blo 908576 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B161628185 : Blo 908576 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B4145255 : Blo 908576 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B909423 : Blo 908576 909423 := bstep (se 1 (by rfl) ⟨682067, by rfl⟩ : syracuseStep 909423 = 1364135) B1364135
theorem B1368383 : Blo 908576 1368383 := bstep (se 1 (by rfl) ⟨1026287, by rfl⟩ : syracuseStep 1368383 = 2052575) B2052575
theorem B5184283 : Blo 908576 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B107752123 : Blo 908576 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B2763503 : Blo 908576 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B912255 : Blo 908576 912255 := bstep (se 1 (by rfl) ⟨684191, by rfl⟩ : syracuseStep 912255 = 1368383) B1368383
theorem B5175809 : Blo 908576 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B1842335 : Blo 908576 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B3450539 : Blo 908576 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B143669497 : Blo 908576 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B6912377 : Blo 908576 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B2300359 : Blo 908576 2300359 := bstep (se 1 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 2300359 = 3450539) B3450539
theorem B1228223 : Blo 908576 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B4608251 : Blo 908576 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B191559329 : Blo 908576 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B127706219 : Blo 908576 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B3067145 : Blo 908576 3067145 := bstep (se 2 (by rfl) ⟨1150179, by rfl⟩ : syracuseStep 3067145 = 2300359) B2300359
theorem B3072167 : Blo 908576 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B3275261 : Blo 908576 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B85137479 : Blo 908576 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B2044763 : Blo 908576 2044763 := bstep (se 1 (by rfl) ⟨1533572, by rfl⟩ : syracuseStep 2044763 = 3067145) B3067145
theorem B2048111 : Blo 908576 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B2183507 : Blo 908576 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B56758319 : Blo 908576 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B1455671 : Blo 908576 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B1363175 : Blo 908576 1363175 := bstep (se 1 (by rfl) ⟨1022381, by rfl⟩ : syracuseStep 1363175 = 2044763) B2044763
theorem B1365407 : Blo 908576 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111
theorem B3881789 : Blo 908576 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B908783 : Blo 908576 908783 := bstep (se 1 (by rfl) ⟨681587, by rfl⟩ : syracuseStep 908783 = 1363175) B1363175
theorem B37838879 : Blo 908576 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B910271 : Blo 908576 910271 := bstep (se 1 (by rfl) ⟨682703, by rfl⟩ : syracuseStep 910271 = 1365407) B1365407
theorem B25225919 : Blo 908576 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B2587859 : Blo 908576 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B16817279 : Blo 908576 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B1725239 : Blo 908576 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B4600637 : Blo 908576 4600637 := bstep (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) B1725239
theorem B44846077 : Blo 908576 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B3067091 : Blo 908576 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B59794769 : Blo 908576 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B2044727 : Blo 908576 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B39863179 : Blo 908576 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B53150905 : Blo 908576 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B1363151 : Blo 908576 1363151 := bstep (se 1 (by rfl) ⟨1022363, by rfl⟩ : syracuseStep 1363151 = 2044727) B2044727
theorem B70867873 : Blo 908576 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B908767 : Blo 908576 908767 := bstep (se 1 (by rfl) ⟨681575, by rfl⟩ : syracuseStep 908767 = 1363151) B1363151
theorem B94490497 : Blo 908576 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 908576 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 908576 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 908576 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 908576 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 908576 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 908576 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 908576 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B117979901 : Blo 908576 117979901 := bstep (se 3 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 117979901 = 44242463) B44242463
theorem B78653267 : Blo 908576 78653267 := bstep (se 1 (by rfl) ⟨58989950, by rfl⟩ : syracuseStep 78653267 = 117979901) B117979901
theorem B52435511 : Blo 908576 52435511 := bstep (se 1 (by rfl) ⟨39326633, by rfl⟩ : syracuseStep 52435511 = 78653267) B78653267
theorem B34957007 : Blo 908576 34957007 := bstep (se 1 (by rfl) ⟨26217755, by rfl⟩ : syracuseStep 34957007 = 52435511) B52435511
theorem B23304671 : Blo 908576 23304671 := bstep (se 1 (by rfl) ⟨17478503, by rfl⟩ : syracuseStep 23304671 = 34957007) B34957007
theorem B15536447 : Blo 908576 15536447 := bstep (se 1 (by rfl) ⟨11652335, by rfl⟩ : syracuseStep 15536447 = 23304671) B23304671
theorem B10357631 : Blo 908576 10357631 := bstep (se 1 (by rfl) ⟨7768223, by rfl⟩ : syracuseStep 10357631 = 15536447) B15536447
theorem B6905087 : Blo 908576 6905087 := bstep (se 1 (by rfl) ⟨5178815, by rfl⟩ : syracuseStep 6905087 = 10357631) B10357631
theorem B4603391 : Blo 908576 4603391 := bstep (se 1 (by rfl) ⟨3452543, by rfl⟩ : syracuseStep 4603391 = 6905087) B6905087
theorem B3068927 : Blo 908576 3068927 := bstep (se 1 (by rfl) ⟨2301695, by rfl⟩ : syracuseStep 3068927 = 4603391) B4603391
theorem B2045951 : Blo 908576 2045951 := bstep (se 1 (by rfl) ⟨1534463, by rfl⟩ : syracuseStep 2045951 = 3068927) B3068927
theorem B1363967 : Blo 908576 1363967 := bstep (se 1 (by rfl) ⟨1022975, by rfl⟩ : syracuseStep 1363967 = 2045951) B2045951
theorem B909311 : Blo 908576 909311 := bstep (se 1 (by rfl) ⟨681983, by rfl⟩ : syracuseStep 909311 = 1363967) B1363967

theorem C0 (j : ℕ) (h1 : 227144 ≤ j) (h2 : j ≤ 227843) : Blo 908576 (4 * j + 3) := by
  interval_cases j
  · exact B908579
  · exact B908583
  · exact B908587
  · exact B908591
  · exact B908595
  · exact B908599
  · exact B908603
  · exact B908607
  · exact B908611
  · exact B908615
  · exact B908619
  · exact B908623
  · exact B908627
  · exact B908631
  · exact B908635
  · exact B908639
  · exact B908643
  · exact B908647
  · exact B908651
  · exact B908655
  · exact B908659
  · exact B908663
  · exact B908667
  · exact B908671
  · exact B908675
  · exact B908679
  · exact B908683
  · exact B908687
  · exact B908691
  · exact B908695
  · exact B908699
  · exact B908703
  · exact B908707
  · exact B908711
  · exact B908715
  · exact B908719
  · exact B908723
  · exact B908727
  · exact B908731
  · exact B908735
  · exact B908739
  · exact B908743
  · exact B908747
  · exact B908751
  · exact B908755
  · exact B908759
  · exact B908763
  · exact B908767
  · exact B908771
  · exact B908775
  · exact B908779
  · exact B908783
  · exact B908787
  · exact B908791
  · exact B908795
  · exact B908799
  · exact B908803
  · exact B908807
  · exact B908811
  · exact B908815
  · exact B908819
  · exact B908823
  · exact B908827
  · exact B908831
  · exact B908835
  · exact B908839
  · exact B908843
  · exact B908847
  · exact B908851
  · exact B908855
  · exact B908859
  · exact B908863
  · exact B908867
  · exact B908871
  · exact B908875
  · exact B908879
  · exact B908883
  · exact B908887
  · exact B908891
  · exact B908895
  · exact B908899
  · exact B908903
  · exact B908907
  · exact B908911
  · exact B908915
  · exact B908919
  · exact B908923
  · exact B908927
  · exact B908931
  · exact B908935
  · exact B908939
  · exact B908943
  · exact B908947
  · exact B908951
  · exact B908955
  · exact B908959
  · exact B908963
  · exact B908967
  · exact B908971
  · exact B908975
  · exact B908979
  · exact B908983
  · exact B908987
  · exact B908991
  · exact B908995
  · exact B908999
  · exact B909003
  · exact B909007
  · exact B909011
  · exact B909015
  · exact B909019
  · exact B909023
  · exact B909027
  · exact B909031
  · exact B909035
  · exact B909039
  · exact B909043
  · exact B909047
  · exact B909051
  · exact B909055
  · exact B909059
  · exact B909063
  · exact B909067
  · exact B909071
  · exact B909075
  · exact B909079
  · exact B909083
  · exact B909087
  · exact B909091
  · exact B909095
  · exact B909099
  · exact B909103
  · exact B909107
  · exact B909111
  · exact B909115
  · exact B909119
  · exact B909123
  · exact B909127
  · exact B909131
  · exact B909135
  · exact B909139
  · exact B909143
  · exact B909147
  · exact B909151
  · exact B909155
  · exact B909159
  · exact B909163
  · exact B909167
  · exact B909171
  · exact B909175
  · exact B909179
  · exact B909183
  · exact B909187
  · exact B909191
  · exact B909195
  · exact B909199
  · exact B909203
  · exact B909207
  · exact B909211
  · exact B909215
  · exact B909219
  · exact B909223
  · exact B909227
  · exact B909231
  · exact B909235
  · exact B909239
  · exact B909243
  · exact B909247
  · exact B909251
  · exact B909255
  · exact B909259
  · exact B909263
  · exact B909267
  · exact B909271
  · exact B909275
  · exact B909279
  · exact B909283
  · exact B909287
  · exact B909291
  · exact B909295
  · exact B909299
  · exact B909303
  · exact B909307
  · exact B909311
  · exact B909315
  · exact B909319
  · exact B909323
  · exact B909327
  · exact B909331
  · exact B909335
  · exact B909339
  · exact B909343
  · exact B909347
  · exact B909351
  · exact B909355
  · exact B909359
  · exact B909363
  · exact B909367
  · exact B909371
  · exact B909375
  · exact B909379
  · exact B909383
  · exact B909387
  · exact B909391
  · exact B909395
  · exact B909399
  · exact B909403
  · exact B909407
  · exact B909411
  · exact B909415
  · exact B909419
  · exact B909423
  · exact B909427
  · exact B909431
  · exact B909435
  · exact B909439
  · exact B909443
  · exact B909447
  · exact B909451
  · exact B909455
  · exact B909459
  · exact B909463
  · exact B909467
  · exact B909471
  · exact B909475
  · exact B909479
  · exact B909483
  · exact B909487
  · exact B909491
  · exact B909495
  · exact B909499
  · exact B909503
  · exact B909507
  · exact B909511
  · exact B909515
  · exact B909519
  · exact B909523
  · exact B909527
  · exact B909531
  · exact B909535
  · exact B909539
  · exact B909543
  · exact B909547
  · exact B909551
  · exact B909555
  · exact B909559
  · exact B909563
  · exact B909567
  · exact B909571
  · exact B909575
  · exact B909579
  · exact B909583
  · exact B909587
  · exact B909591
  · exact B909595
  · exact B909599
  · exact B909603
  · exact B909607
  · exact B909611
  · exact B909615
  · exact B909619
  · exact B909623
  · exact B909627
  · exact B909631
  · exact B909635
  · exact B909639
  · exact B909643
  · exact B909647
  · exact B909651
  · exact B909655
  · exact B909659
  · exact B909663
  · exact B909667
  · exact B909671
  · exact B909675
  · exact B909679
  · exact B909683
  · exact B909687
  · exact B909691
  · exact B909695
  · exact B909699
  · exact B909703
  · exact B909707
  · exact B909711
  · exact B909715
  · exact B909719
  · exact B909723
  · exact B909727
  · exact B909731
  · exact B909735
  · exact B909739
  · exact B909743
  · exact B909747
  · exact B909751
  · exact B909755
  · exact B909759
  · exact B909763
  · exact B909767
  · exact B909771
  · exact B909775
  · exact B909779
  · exact B909783
  · exact B909787
  · exact B909791
  · exact B909795
  · exact B909799
  · exact B909803
  · exact B909807
  · exact B909811
  · exact B909815
  · exact B909819
  · exact B909823
  · exact B909827
  · exact B909831
  · exact B909835
  · exact B909839
  · exact B909843
  · exact B909847
  · exact B909851
  · exact B909855
  · exact B909859
  · exact B909863
  · exact B909867
  · exact B909871
  · exact B909875
  · exact B909879
  · exact B909883
  · exact B909887
  · exact B909891
  · exact B909895
  · exact B909899
  · exact B909903
  · exact B909907
  · exact B909911
  · exact B909915
  · exact B909919
  · exact B909923
  · exact B909927
  · exact B909931
  · exact B909935
  · exact B909939
  · exact B909943
  · exact B909947
  · exact B909951
  · exact B909955
  · exact B909959
  · exact B909963
  · exact B909967
  · exact B909971
  · exact B909975
  · exact B909979
  · exact B909983
  · exact B909987
  · exact B909991
  · exact B909995
  · exact B909999
  · exact B910003
  · exact B910007
  · exact B910011
  · exact B910015
  · exact B910019
  · exact B910023
  · exact B910027
  · exact B910031
  · exact B910035
  · exact B910039
  · exact B910043
  · exact B910047
  · exact B910051
  · exact B910055
  · exact B910059
  · exact B910063
  · exact B910067
  · exact B910071
  · exact B910075
  · exact B910079
  · exact B910083
  · exact B910087
  · exact B910091
  · exact B910095
  · exact B910099
  · exact B910103
  · exact B910107
  · exact B910111
  · exact B910115
  · exact B910119
  · exact B910123
  · exact B910127
  · exact B910131
  · exact B910135
  · exact B910139
  · exact B910143
  · exact B910147
  · exact B910151
  · exact B910155
  · exact B910159
  · exact B910163
  · exact B910167
  · exact B910171
  · exact B910175
  · exact B910179
  · exact B910183
  · exact B910187
  · exact B910191
  · exact B910195
  · exact B910199
  · exact B910203
  · exact B910207
  · exact B910211
  · exact B910215
  · exact B910219
  · exact B910223
  · exact B910227
  · exact B910231
  · exact B910235
  · exact B910239
  · exact B910243
  · exact B910247
  · exact B910251
  · exact B910255
  · exact B910259
  · exact B910263
  · exact B910267
  · exact B910271
  · exact B910275
  · exact B910279
  · exact B910283
  · exact B910287
  · exact B910291
  · exact B910295
  · exact B910299
  · exact B910303
  · exact B910307
  · exact B910311
  · exact B910315
  · exact B910319
  · exact B910323
  · exact B910327
  · exact B910331
  · exact B910335
  · exact B910339
  · exact B910343
  · exact B910347
  · exact B910351
  · exact B910355
  · exact B910359
  · exact B910363
  · exact B910367
  · exact B910371
  · exact B910375
  · exact B910379
  · exact B910383
  · exact B910387
  · exact B910391
  · exact B910395
  · exact B910399
  · exact B910403
  · exact B910407
  · exact B910411
  · exact B910415
  · exact B910419
  · exact B910423
  · exact B910427
  · exact B910431
  · exact B910435
  · exact B910439
  · exact B910443
  · exact B910447
  · exact B910451
  · exact B910455
  · exact B910459
  · exact B910463
  · exact B910467
  · exact B910471
  · exact B910475
  · exact B910479
  · exact B910483
  · exact B910487
  · exact B910491
  · exact B910495
  · exact B910499
  · exact B910503
  · exact B910507
  · exact B910511
  · exact B910515
  · exact B910519
  · exact B910523
  · exact B910527
  · exact B910531
  · exact B910535
  · exact B910539
  · exact B910543
  · exact B910547
  · exact B910551
  · exact B910555
  · exact B910559
  · exact B910563
  · exact B910567
  · exact B910571
  · exact B910575
  · exact B910579
  · exact B910583
  · exact B910587
  · exact B910591
  · exact B910595
  · exact B910599
  · exact B910603
  · exact B910607
  · exact B910611
  · exact B910615
  · exact B910619
  · exact B910623
  · exact B910627
  · exact B910631
  · exact B910635
  · exact B910639
  · exact B910643
  · exact B910647
  · exact B910651
  · exact B910655
  · exact B910659
  · exact B910663
  · exact B910667
  · exact B910671
  · exact B910675
  · exact B910679
  · exact B910683
  · exact B910687
  · exact B910691
  · exact B910695
  · exact B910699
  · exact B910703
  · exact B910707
  · exact B910711
  · exact B910715
  · exact B910719
  · exact B910723
  · exact B910727
  · exact B910731
  · exact B910735
  · exact B910739
  · exact B910743
  · exact B910747
  · exact B910751
  · exact B910755
  · exact B910759
  · exact B910763
  · exact B910767
  · exact B910771
  · exact B910775
  · exact B910779
  · exact B910783
  · exact B910787
  · exact B910791
  · exact B910795
  · exact B910799
  · exact B910803
  · exact B910807
  · exact B910811
  · exact B910815
  · exact B910819
  · exact B910823
  · exact B910827
  · exact B910831
  · exact B910835
  · exact B910839
  · exact B910843
  · exact B910847
  · exact B910851
  · exact B910855
  · exact B910859
  · exact B910863
  · exact B910867
  · exact B910871
  · exact B910875
  · exact B910879
  · exact B910883
  · exact B910887
  · exact B910891
  · exact B910895
  · exact B910899
  · exact B910903
  · exact B910907
  · exact B910911
  · exact B910915
  · exact B910919
  · exact B910923
  · exact B910927
  · exact B910931
  · exact B910935
  · exact B910939
  · exact B910943
  · exact B910947
  · exact B910951
  · exact B910955
  · exact B910959
  · exact B910963
  · exact B910967
  · exact B910971
  · exact B910975
  · exact B910979
  · exact B910983
  · exact B910987
  · exact B910991
  · exact B910995
  · exact B910999
  · exact B911003
  · exact B911007
  · exact B911011
  · exact B911015
  · exact B911019
  · exact B911023
  · exact B911027
  · exact B911031
  · exact B911035
  · exact B911039
  · exact B911043
  · exact B911047
  · exact B911051
  · exact B911055
  · exact B911059
  · exact B911063
  · exact B911067
  · exact B911071
  · exact B911075
  · exact B911079
  · exact B911083
  · exact B911087
  · exact B911091
  · exact B911095
  · exact B911099
  · exact B911103
  · exact B911107
  · exact B911111
  · exact B911115
  · exact B911119
  · exact B911123
  · exact B911127
  · exact B911131
  · exact B911135
  · exact B911139
  · exact B911143
  · exact B911147
  · exact B911151
  · exact B911155
  · exact B911159
  · exact B911163
  · exact B911167
  · exact B911171
  · exact B911175
  · exact B911179
  · exact B911183
  · exact B911187
  · exact B911191
  · exact B911195
  · exact B911199
  · exact B911203
  · exact B911207
  · exact B911211
  · exact B911215
  · exact B911219
  · exact B911223
  · exact B911227
  · exact B911231
  · exact B911235
  · exact B911239
  · exact B911243
  · exact B911247
  · exact B911251
  · exact B911255
  · exact B911259
  · exact B911263
  · exact B911267
  · exact B911271
  · exact B911275
  · exact B911279
  · exact B911283
  · exact B911287
  · exact B911291
  · exact B911295
  · exact B911299
  · exact B911303
  · exact B911307
  · exact B911311
  · exact B911315
  · exact B911319
  · exact B911323
  · exact B911327
  · exact B911331
  · exact B911335
  · exact B911339
  · exact B911343
  · exact B911347
  · exact B911351
  · exact B911355
  · exact B911359
  · exact B911363
  · exact B911367
  · exact B911371
  · exact B911375

theorem C1 (j : ℕ) (h1 : 227844 ≤ j) (h2 : j ≤ 228143) : Blo 908576 (4 * j + 3) := by
  interval_cases j
  · exact B911379
  · exact B911383
  · exact B911387
  · exact B911391
  · exact B911395
  · exact B911399
  · exact B911403
  · exact B911407
  · exact B911411
  · exact B911415
  · exact B911419
  · exact B911423
  · exact B911427
  · exact B911431
  · exact B911435
  · exact B911439
  · exact B911443
  · exact B911447
  · exact B911451
  · exact B911455
  · exact B911459
  · exact B911463
  · exact B911467
  · exact B911471
  · exact B911475
  · exact B911479
  · exact B911483
  · exact B911487
  · exact B911491
  · exact B911495
  · exact B911499
  · exact B911503
  · exact B911507
  · exact B911511
  · exact B911515
  · exact B911519
  · exact B911523
  · exact B911527
  · exact B911531
  · exact B911535
  · exact B911539
  · exact B911543
  · exact B911547
  · exact B911551
  · exact B911555
  · exact B911559
  · exact B911563
  · exact B911567
  · exact B911571
  · exact B911575
  · exact B911579
  · exact B911583
  · exact B911587
  · exact B911591
  · exact B911595
  · exact B911599
  · exact B911603
  · exact B911607
  · exact B911611
  · exact B911615
  · exact B911619
  · exact B911623
  · exact B911627
  · exact B911631
  · exact B911635
  · exact B911639
  · exact B911643
  · exact B911647
  · exact B911651
  · exact B911655
  · exact B911659
  · exact B911663
  · exact B911667
  · exact B911671
  · exact B911675
  · exact B911679
  · exact B911683
  · exact B911687
  · exact B911691
  · exact B911695
  · exact B911699
  · exact B911703
  · exact B911707
  · exact B911711
  · exact B911715
  · exact B911719
  · exact B911723
  · exact B911727
  · exact B911731
  · exact B911735
  · exact B911739
  · exact B911743
  · exact B911747
  · exact B911751
  · exact B911755
  · exact B911759
  · exact B911763
  · exact B911767
  · exact B911771
  · exact B911775
  · exact B911779
  · exact B911783
  · exact B911787
  · exact B911791
  · exact B911795
  · exact B911799
  · exact B911803
  · exact B911807
  · exact B911811
  · exact B911815
  · exact B911819
  · exact B911823
  · exact B911827
  · exact B911831
  · exact B911835
  · exact B911839
  · exact B911843
  · exact B911847
  · exact B911851
  · exact B911855
  · exact B911859
  · exact B911863
  · exact B911867
  · exact B911871
  · exact B911875
  · exact B911879
  · exact B911883
  · exact B911887
  · exact B911891
  · exact B911895
  · exact B911899
  · exact B911903
  · exact B911907
  · exact B911911
  · exact B911915
  · exact B911919
  · exact B911923
  · exact B911927
  · exact B911931
  · exact B911935
  · exact B911939
  · exact B911943
  · exact B911947
  · exact B911951
  · exact B911955
  · exact B911959
  · exact B911963
  · exact B911967
  · exact B911971
  · exact B911975
  · exact B911979
  · exact B911983
  · exact B911987
  · exact B911991
  · exact B911995
  · exact B911999
  · exact B912003
  · exact B912007
  · exact B912011
  · exact B912015
  · exact B912019
  · exact B912023
  · exact B912027
  · exact B912031
  · exact B912035
  · exact B912039
  · exact B912043
  · exact B912047
  · exact B912051
  · exact B912055
  · exact B912059
  · exact B912063
  · exact B912067
  · exact B912071
  · exact B912075
  · exact B912079
  · exact B912083
  · exact B912087
  · exact B912091
  · exact B912095
  · exact B912099
  · exact B912103
  · exact B912107
  · exact B912111
  · exact B912115
  · exact B912119
  · exact B912123
  · exact B912127
  · exact B912131
  · exact B912135
  · exact B912139
  · exact B912143
  · exact B912147
  · exact B912151
  · exact B912155
  · exact B912159
  · exact B912163
  · exact B912167
  · exact B912171
  · exact B912175
  · exact B912179
  · exact B912183
  · exact B912187
  · exact B912191
  · exact B912195
  · exact B912199
  · exact B912203
  · exact B912207
  · exact B912211
  · exact B912215
  · exact B912219
  · exact B912223
  · exact B912227
  · exact B912231
  · exact B912235
  · exact B912239
  · exact B912243
  · exact B912247
  · exact B912251
  · exact B912255
  · exact B912259
  · exact B912263
  · exact B912267
  · exact B912271
  · exact B912275
  · exact B912279
  · exact B912283
  · exact B912287
  · exact B912291
  · exact B912295
  · exact B912299
  · exact B912303
  · exact B912307
  · exact B912311
  · exact B912315
  · exact B912319
  · exact B912323
  · exact B912327
  · exact B912331
  · exact B912335
  · exact B912339
  · exact B912343
  · exact B912347
  · exact B912351
  · exact B912355
  · exact B912359
  · exact B912363
  · exact B912367
  · exact B912371
  · exact B912375
  · exact B912379
  · exact B912383
  · exact B912387
  · exact B912391
  · exact B912395
  · exact B912399
  · exact B912403
  · exact B912407
  · exact B912411
  · exact B912415
  · exact B912419
  · exact B912423
  · exact B912427
  · exact B912431
  · exact B912435
  · exact B912439
  · exact B912443
  · exact B912447
  · exact B912451
  · exact B912455
  · exact B912459
  · exact B912463
  · exact B912467
  · exact B912471
  · exact B912475
  · exact B912479
  · exact B912483
  · exact B912487
  · exact B912491
  · exact B912495
  · exact B912499
  · exact B912503
  · exact B912507
  · exact B912511
  · exact B912515
  · exact B912519
  · exact B912523
  · exact B912527
  · exact B912531
  · exact B912535
  · exact B912539
  · exact B912543
  · exact B912547
  · exact B912551
  · exact B912555
  · exact B912559
  · exact B912563
  · exact B912567
  · exact B912571
  · exact B912575

theorem solution (m : ℕ) (hlo : 908576 ≤ m) (hhi : m ≤ 912576) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 227144 ≤ j := by omega
    have hj2 : j ≤ 228143 := by omega
    have hb : Blo 908576 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 227844 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
