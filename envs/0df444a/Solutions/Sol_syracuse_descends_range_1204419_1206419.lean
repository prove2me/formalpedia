-- Prove2me | solution 1 for syracuse_descends_range_1204419_1206419
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:46.134231+00:00
-- url     : https://prove2.me/submissions/0b534fdd-cd83-4f0d-b249-0fb8e438407d

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


theorem B2711573 : Blo 1204419 2711573 := bbase (se 6 (by rfl) ⟨63552, by rfl⟩ : syracuseStep 2711573 = 127105) (by norm_num)
theorem B2572357 : Blo 1204419 2572357 := bbase (se 4 (by rfl) ⟨241158, by rfl⟩ : syracuseStep 2572357 = 482317) (by norm_num)
theorem B2711645 : Blo 1204419 2711645 := bbase (se 3 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 2711645 = 1016867) (by norm_num)
theorem B1286281 : Blo 1204419 1286281 := bbase (se 2 (by rfl) ⟨482355, by rfl⟩ : syracuseStep 1286281 = 964711) (by norm_num)
theorem B2711717 : Blo 1204419 2711717 := bbase (se 4 (by rfl) ⟨254223, by rfl⟩ : syracuseStep 2711717 = 508447) (by norm_num)
theorem B1392833 : Blo 1204419 1392833 := bbase (se 2 (by rfl) ⟨522312, by rfl⟩ : syracuseStep 1392833 = 1044625) (by norm_num)
theorem B1630405 : Blo 1204419 1630405 := bbase (se 4 (by rfl) ⟨152850, by rfl⟩ : syracuseStep 1630405 = 305701) (by norm_num)
theorem B4071653 : Blo 1204419 4071653 := bbase (se 4 (by rfl) ⟨381717, by rfl⟩ : syracuseStep 4071653 = 763435) (by norm_num)
theorem B2711789 : Blo 1204419 2711789 := bbase (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) (by norm_num)
theorem B2171141 : Blo 1204419 2171141 := bbase (se 4 (by rfl) ⟨203544, by rfl⟩ : syracuseStep 2171141 = 407089) (by norm_num)
theorem B3432725 : Blo 1204419 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B2711861 : Blo 1204419 2711861 := bbase (se 5 (by rfl) ⟨127118, by rfl⟩ : syracuseStep 2711861 = 254237) (by norm_num)
theorem B6103349 : Blo 1204419 6103349 := bbase (se 5 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 6103349 = 572189) (by norm_num)
theorem B4579685 : Blo 1204419 4579685 := bbase (se 4 (by rfl) ⟨429345, by rfl⟩ : syracuseStep 4579685 = 858691) (by norm_num)
theorem B2711933 : Blo 1204419 2711933 := bbase (se 3 (by rfl) ⟨508487, by rfl⟩ : syracuseStep 2711933 = 1016975) (by norm_num)
theorem B1286533 : Blo 1204419 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B1286537 : Blo 1204419 1286537 := bbase (se 2 (by rfl) ⟨482451, by rfl⟩ : syracuseStep 1286537 = 964903) (by norm_num)
theorem B2712005 : Blo 1204419 2712005 := bbase (se 4 (by rfl) ⟨254250, by rfl⟩ : syracuseStep 2712005 = 508501) (by norm_num)
theorem B2712077 : Blo 1204419 2712077 := bbase (se 3 (by rfl) ⟨508514, by rfl⟩ : syracuseStep 2712077 = 1017029) (by norm_num)
theorem B1221157 : Blo 1204419 1221157 := bbase (se 4 (by rfl) ⟨114483, by rfl⟩ : syracuseStep 1221157 = 228967) (by norm_num)
theorem B2712149 : Blo 1204419 2712149 := bbase (se 8 (by rfl) ⟨15891, by rfl⟩ : syracuseStep 2712149 = 31783) (by norm_num)
theorem B1524349 : Blo 1204419 1524349 := bbase (se 3 (by rfl) ⟨285815, by rfl⟩ : syracuseStep 1524349 = 571631) (by norm_num)
theorem B4579973 : Blo 1204419 4579973 := bbase (se 4 (by rfl) ⟨429372, by rfl⟩ : syracuseStep 4579973 = 858745) (by norm_num)
theorem B2712221 : Blo 1204419 2712221 := bbase (se 3 (by rfl) ⟨508541, by rfl⟩ : syracuseStep 2712221 = 1017083) (by norm_num)
theorem B2712293 : Blo 1204419 2712293 := bbase (se 4 (by rfl) ⟨254277, by rfl⟩ : syracuseStep 2712293 = 508555) (by norm_num)
theorem B1524521 : Blo 1204419 1524521 := bbase (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) (by norm_num)
theorem B2712365 : Blo 1204419 2712365 := bbase (se 3 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 2712365 = 1017137) (by norm_num)
theorem B7824181 : Blo 1204419 7824181 := bbase (se 5 (by rfl) ⟨366758, by rfl⟩ : syracuseStep 7824181 = 733517) (by norm_num)
theorem B1524577 : Blo 1204419 1524577 := bbase (se 2 (by rfl) ⟨571716, by rfl⟩ : syracuseStep 1524577 = 1143433) (by norm_num)
theorem B1467253 : Blo 1204419 1467253 := bbase (se 5 (by rfl) ⟨68777, by rfl⟩ : syracuseStep 1467253 = 137555) (by norm_num)
theorem B2712437 : Blo 1204419 2712437 := bbase (se 5 (by rfl) ⟨127145, by rfl⟩ : syracuseStep 2712437 = 254291) (by norm_num)
theorem B2032573 : Blo 1204419 2032573 := bbase (se 3 (by rfl) ⟨381107, by rfl⟩ : syracuseStep 2032573 = 762215) (by norm_num)
theorem B2573245 : Blo 1204419 2573245 := bbase (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) (by norm_num)
theorem B1287101 : Blo 1204419 1287101 := bbase (se 3 (by rfl) ⟨241331, by rfl⟩ : syracuseStep 1287101 = 482663) (by norm_num)
theorem B1524673 : Blo 1204419 1524673 := bbase (se 2 (by rfl) ⟨571752, by rfl⟩ : syracuseStep 1524673 = 1143505) (by norm_num)
theorem B2712509 : Blo 1204419 2712509 := bbase (se 3 (by rfl) ⟨508595, by rfl⟩ : syracuseStep 2712509 = 1017191) (by norm_num)
theorem B2712581 : Blo 1204419 2712581 := bbase (se 4 (by rfl) ⟨254304, by rfl⟩ : syracuseStep 2712581 = 508609) (by norm_num)
theorem B2032661 : Blo 1204419 2032661 := bbase (se 6 (by rfl) ⟨47640, by rfl⟩ : syracuseStep 2032661 = 95281) (by norm_num)
theorem B2573365 : Blo 1204419 2573365 := bbase (se 5 (by rfl) ⟨120626, by rfl⟩ : syracuseStep 2573365 = 241253) (by norm_num)
theorem B2712653 : Blo 1204419 2712653 := bbase (se 3 (by rfl) ⟨508622, by rfl⟩ : syracuseStep 2712653 = 1017245) (by norm_num)
theorem B1524845 : Blo 1204419 1524845 := bbase (se 3 (by rfl) ⟨285908, by rfl⟩ : syracuseStep 1524845 = 571817) (by norm_num)
theorem B1287289 : Blo 1204419 1287289 := bbase (se 2 (by rfl) ⟨482733, by rfl⟩ : syracuseStep 1287289 = 965467) (by norm_num)
theorem B2032789 : Blo 1204419 2032789 := bbase (se 6 (by rfl) ⟨47643, by rfl⟩ : syracuseStep 2032789 = 95287) (by norm_num)
theorem B2712725 : Blo 1204419 2712725 := bbase (se 6 (by rfl) ⟨63579, by rfl⟩ : syracuseStep 2712725 = 127159) (by norm_num)
theorem B1524901 : Blo 1204419 1524901 := bbase (se 4 (by rfl) ⟨142959, by rfl⟩ : syracuseStep 1524901 = 285919) (by norm_num)
theorem B2286805 : Blo 1204419 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B2712797 : Blo 1204419 2712797 := bbase (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) (by norm_num)
theorem B2032877 : Blo 1204419 2032877 := bbase (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) (by norm_num)
theorem B1524997 : Blo 1204419 1524997 := bbase (se 4 (by rfl) ⟨142968, by rfl⟩ : syracuseStep 1524997 = 285937) (by norm_num)
theorem B2712869 : Blo 1204419 2712869 := bbase (se 4 (by rfl) ⟨254331, by rfl⟩ : syracuseStep 2712869 = 508663) (by norm_num)
theorem B3048749 : Blo 1204419 3048749 := bbase (se 3 (by rfl) ⟨571640, by rfl⟩ : syracuseStep 3048749 = 1143281) (by norm_num)
theorem B2573621 : Blo 1204419 2573621 := bbase (se 5 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 2573621 = 241277) (by norm_num)
theorem B20579669 : Blo 1204419 20579669 := bbase (se 12 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 20579669 = 15073) (by norm_num)
theorem B2286949 : Blo 1204419 2286949 := bbase (se 4 (by rfl) ⟨214401, by rfl⟩ : syracuseStep 2286949 = 428803) (by norm_num)
theorem B2033005 : Blo 1204419 2033005 := bbase (se 3 (by rfl) ⟨381188, by rfl⟩ : syracuseStep 2033005 = 762377) (by norm_num)
theorem B2712941 : Blo 1204419 2712941 := bbase (se 3 (by rfl) ⟨508676, by rfl⟩ : syracuseStep 2712941 = 1017353) (by norm_num)
theorem B1222025 : Blo 1204419 1222025 := bbase (se 2 (by rfl) ⟨458259, by rfl⟩ : syracuseStep 1222025 = 916519) (by norm_num)
theorem B1222057 : Blo 1204419 1222057 := bbase (se 2 (by rfl) ⟨458271, by rfl⟩ : syracuseStep 1222057 = 916543) (by norm_num)
theorem B1525169 : Blo 1204419 1525169 := bbase (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) (by norm_num)
theorem B2713013 : Blo 1204419 2713013 := bbase (se 5 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 2713013 = 254345) (by norm_num)
theorem B3433909 : Blo 1204419 3433909 := bbase (se 5 (by rfl) ⟨160964, by rfl⟩ : syracuseStep 3433909 = 321929) (by norm_num)
theorem B2033093 : Blo 1204419 2033093 := bbase (se 4 (by rfl) ⟨190602, by rfl⟩ : syracuseStep 2033093 = 381205) (by norm_num)
theorem B1525225 : Blo 1204419 1525225 := bbase (se 2 (by rfl) ⟨571959, by rfl⟩ : syracuseStep 1525225 = 1143919) (by norm_num)
theorem B3048941 : Blo 1204419 3048941 := bbase (se 3 (by rfl) ⟨571676, by rfl⟩ : syracuseStep 3048941 = 1143353) (by norm_num)
theorem B2713085 : Blo 1204419 2713085 := bbase (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) (by norm_num)
theorem B2287109 : Blo 1204419 2287109 := bbase (se 4 (by rfl) ⟨214416, by rfl⟩ : syracuseStep 2287109 = 428833) (by norm_num)
theorem B3860021 : Blo 1204419 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B2033221 : Blo 1204419 2033221 := bbase (se 4 (by rfl) ⟨190614, by rfl⟩ : syracuseStep 2033221 = 381229) (by norm_num)
theorem B2713157 : Blo 1204419 2713157 := bbase (se 4 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 2713157 = 508717) (by norm_num)
theorem B6104645 : Blo 1204419 6104645 := bbase (se 4 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 6104645 = 1144621) (by norm_num)
theorem B1525321 : Blo 1204419 1525321 := bbase (se 2 (by rfl) ⟨571995, by rfl⟩ : syracuseStep 1525321 = 1143991) (by norm_num)
theorem B2475605 : Blo 1204419 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B3434069 : Blo 1204419 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B2713229 : Blo 1204419 2713229 := bbase (se 3 (by rfl) ⟨508730, by rfl⟩ : syracuseStep 2713229 = 1017461) (by norm_num)
theorem B2287253 : Blo 1204419 2287253 := bbase (se 6 (by rfl) ⟨53607, by rfl⟩ : syracuseStep 2287253 = 107215) (by norm_num)
theorem B2033309 : Blo 1204419 2033309 := bbase (se 3 (by rfl) ⟨381245, by rfl⟩ : syracuseStep 2033309 = 762491) (by norm_num)
theorem B2713301 : Blo 1204419 2713301 := bbase (se 7 (by rfl) ⟨31796, by rfl⟩ : syracuseStep 2713301 = 63593) (by norm_num)
theorem B1222373 : Blo 1204419 1222373 := bbase (se 4 (by rfl) ⟨114597, by rfl⟩ : syracuseStep 1222373 = 229195) (by norm_num)
theorem B1525493 : Blo 1204419 1525493 := bbase (se 5 (by rfl) ⟨71507, by rfl⟩ : syracuseStep 1525493 = 143015) (by norm_num)
theorem B2033437 : Blo 1204419 2033437 := bbase (se 3 (by rfl) ⟨381269, by rfl⟩ : syracuseStep 2033437 = 762539) (by norm_num)
theorem B2713373 : Blo 1204419 2713373 := bbase (se 3 (by rfl) ⟨508757, by rfl⟩ : syracuseStep 2713373 = 1017515) (by norm_num)
theorem B1525549 : Blo 1204419 1525549 := bbase (se 3 (by rfl) ⟨286040, by rfl⟩ : syracuseStep 1525549 = 572081) (by norm_num)
theorem B3049285 : Blo 1204419 3049285 := bbase (se 4 (by rfl) ⟨285870, by rfl⟩ : syracuseStep 3049285 = 571741) (by norm_num)
theorem B3434309 : Blo 1204419 3434309 := bbase (se 4 (by rfl) ⟨321966, by rfl⟩ : syracuseStep 3434309 = 643933) (by norm_num)
theorem B2713445 : Blo 1204419 2713445 := bbase (se 4 (by rfl) ⟨254385, by rfl⟩ : syracuseStep 2713445 = 508771) (by norm_num)
theorem B2033525 : Blo 1204419 2033525 := bbase (se 5 (by rfl) ⟨95321, by rfl⟩ : syracuseStep 2033525 = 190643) (by norm_num)
theorem B1525645 : Blo 1204419 1525645 := bbase (se 3 (by rfl) ⟨286058, by rfl⟩ : syracuseStep 1525645 = 572117) (by norm_num)
theorem B4065173 : Blo 1204419 4065173 := bbase (se 6 (by rfl) ⟨95277, by rfl⟩ : syracuseStep 4065173 = 190555) (by norm_num)
theorem B2713517 : Blo 1204419 2713517 := bbase (se 3 (by rfl) ⟨508784, by rfl⟩ : syracuseStep 2713517 = 1017569) (by norm_num)
theorem B1288109 : Blo 1204419 1288109 := bbase (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) (by norm_num)
theorem B3049397 : Blo 1204419 3049397 := bbase (se 5 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 3049397 = 285881) (by norm_num)
theorem B2287541 : Blo 1204419 2287541 := bbase (se 5 (by rfl) ⟨107228, by rfl⟩ : syracuseStep 2287541 = 214457) (by norm_num)
theorem B7325653 : Blo 1204419 7325653 := bbase (se 7 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 7325653 = 171695) (by norm_num)
theorem B2934749 : Blo 1204419 2934749 := bbase (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) (by norm_num)
theorem B2033653 : Blo 1204419 2033653 := bbase (se 5 (by rfl) ⟨95327, by rfl⟩ : syracuseStep 2033653 = 190655) (by norm_num)
theorem B2713589 : Blo 1204419 2713589 := bbase (se 5 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 2713589 = 254399) (by norm_num)
theorem B3434501 : Blo 1204419 3434501 := bbase (se 4 (by rfl) ⟨321984, by rfl⟩ : syracuseStep 3434501 = 643969) (by norm_num)
theorem B1525817 : Blo 1204419 1525817 := bbase (se 2 (by rfl) ⟨572181, by rfl⟩ : syracuseStep 1525817 = 1144363) (by norm_num)
theorem B2713661 : Blo 1204419 2713661 := bbase (se 3 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 2713661 = 1017623) (by norm_num)
theorem B2287693 : Blo 1204419 2287693 := bbase (se 3 (by rfl) ⟨428942, by rfl⟩ : syracuseStep 2287693 = 857885) (by norm_num)
theorem B2033741 : Blo 1204419 2033741 := bbase (se 3 (by rfl) ⟨381326, by rfl⟩ : syracuseStep 2033741 = 762653) (by norm_num)
theorem B1525873 : Blo 1204419 1525873 := bbase (se 2 (by rfl) ⟨572202, by rfl⟩ : syracuseStep 1525873 = 1144405) (by norm_num)
theorem B3049589 : Blo 1204419 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B2713733 : Blo 1204419 2713733 := bbase (se 4 (by rfl) ⟨254412, by rfl⟩ : syracuseStep 2713733 = 508825) (by norm_num)
theorem B1304749 : Blo 1204419 1304749 := bbase (se 3 (by rfl) ⟨244640, by rfl⟩ : syracuseStep 1304749 = 489281) (by norm_num)
theorem B2574509 : Blo 1204419 2574509 := bbase (se 3 (by rfl) ⟨482720, by rfl⟩ : syracuseStep 2574509 = 965441) (by norm_num)
theorem B4573381 : Blo 1204419 4573381 := bbase (se 4 (by rfl) ⟨428754, by rfl⟩ : syracuseStep 4573381 = 857509) (by norm_num)
theorem B2033869 : Blo 1204419 2033869 := bbase (se 3 (by rfl) ⟨381350, by rfl⟩ : syracuseStep 2033869 = 762701) (by norm_num)
theorem B2713805 : Blo 1204419 2713805 := bbase (se 3 (by rfl) ⟨508838, by rfl⟩ : syracuseStep 2713805 = 1017677) (by norm_num)
theorem B1525969 : Blo 1204419 1525969 := bbase (se 2 (by rfl) ⟨572238, by rfl⟩ : syracuseStep 1525969 = 1144477) (by norm_num)
theorem B5146901 : Blo 1204419 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B2713877 : Blo 1204419 2713877 := bbase (se 6 (by rfl) ⟨63606, by rfl⟩ : syracuseStep 2713877 = 127213) (by norm_num)
theorem B2033957 : Blo 1204419 2033957 := bbase (se 4 (by rfl) ⟨190683, by rfl⟩ : syracuseStep 2033957 = 381367) (by norm_num)
theorem B4065605 : Blo 1204419 4065605 := bbase (se 4 (by rfl) ⟨381150, by rfl⟩ : syracuseStep 4065605 = 762301) (by norm_num)
theorem B2713949 : Blo 1204419 2713949 := bbase (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) (by norm_num)
theorem B2287997 : Blo 1204419 2287997 := bbase (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) (by norm_num)
theorem B1526141 : Blo 1204419 1526141 := bbase (se 3 (by rfl) ⟨286151, by rfl⟩ : syracuseStep 1526141 = 572303) (by norm_num)
theorem B2574749 : Blo 1204419 2574749 := bbase (se 3 (by rfl) ⟨482765, by rfl⟩ : syracuseStep 2574749 = 965531) (by norm_num)
theorem B2034085 : Blo 1204419 2034085 := bbase (se 4 (by rfl) ⟨190695, by rfl⟩ : syracuseStep 2034085 = 381391) (by norm_num)
theorem B2714021 : Blo 1204419 2714021 := bbase (se 4 (by rfl) ⟨254439, by rfl⟩ : syracuseStep 2714021 = 508879) (by norm_num)
theorem B1526197 : Blo 1204419 1526197 := bbase (se 5 (by rfl) ⟨71540, by rfl⟩ : syracuseStep 1526197 = 143081) (by norm_num)
theorem B2443709 : Blo 1204419 2443709 := bbase (se 3 (by rfl) ⟨458195, by rfl⟩ : syracuseStep 2443709 = 916391) (by norm_num)
theorem B3049933 : Blo 1204419 3049933 := bbase (se 3 (by rfl) ⟨571862, by rfl⟩ : syracuseStep 3049933 = 1143725) (by norm_num)
theorem B2714093 : Blo 1204419 2714093 := bbase (se 3 (by rfl) ⟨508892, by rfl⟩ : syracuseStep 2714093 = 1017785) (by norm_num)
theorem B4573685 : Blo 1204419 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B2091509 : Blo 1204419 2091509 := bbase (se 5 (by rfl) ⟨98039, by rfl⟩ : syracuseStep 2091509 = 196079) (by norm_num)
theorem B2034173 : Blo 1204419 2034173 := bbase (se 3 (by rfl) ⟨381407, by rfl⟩ : syracuseStep 2034173 = 762815) (by norm_num)
theorem B1526293 : Blo 1204419 1526293 := bbase (se 6 (by rfl) ⟨35772, by rfl⟩ : syracuseStep 1526293 = 71545) (by norm_num)
theorem B2714165 : Blo 1204419 2714165 := bbase (se 5 (by rfl) ⟨127226, by rfl⟩ : syracuseStep 2714165 = 254453) (by norm_num)
theorem B3050045 : Blo 1204419 3050045 := bbase (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) (by norm_num)
theorem B12364373 : Blo 1204419 12364373 := bbase (se 8 (by rfl) ⟨72447, by rfl⟩ : syracuseStep 12364373 = 144895) (by norm_num)
theorem B2034301 : Blo 1204419 2034301 := bbase (se 3 (by rfl) ⟨381431, by rfl⟩ : syracuseStep 2034301 = 762863) (by norm_num)
theorem B2714237 : Blo 1204419 2714237 := bbase (se 3 (by rfl) ⟨508919, by rfl⟩ : syracuseStep 2714237 = 1017839) (by norm_num)
theorem B1526465 : Blo 1204419 1526465 := bbase (se 2 (by rfl) ⟨572424, by rfl⟩ : syracuseStep 1526465 = 1144849) (by norm_num)
theorem B2714309 : Blo 1204419 2714309 := bbase (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) (by norm_num)
theorem B2034389 : Blo 1204419 2034389 := bbase (se 7 (by rfl) ⟨23840, by rfl⟩ : syracuseStep 2034389 = 47681) (by norm_num)
theorem B4066037 : Blo 1204419 4066037 := bbase (se 5 (by rfl) ⟨190595, by rfl⟩ : syracuseStep 4066037 = 381191) (by norm_num)
theorem B1526521 : Blo 1204419 1526521 := bbase (se 2 (by rfl) ⟨572445, by rfl⟩ : syracuseStep 1526521 = 1144891) (by norm_num)
theorem B3050237 : Blo 1204419 3050237 := bbase (se 3 (by rfl) ⟨571919, by rfl⟩ : syracuseStep 3050237 = 1143839) (by norm_num)
theorem B2714381 : Blo 1204419 2714381 := bbase (se 3 (by rfl) ⟨508946, by rfl⟩ : syracuseStep 2714381 = 1017893) (by norm_num)
theorem B2034517 : Blo 1204419 2034517 := bbase (se 9 (by rfl) ⟨5960, by rfl⟩ : syracuseStep 2034517 = 11921) (by norm_num)
theorem B6105941 : Blo 1204419 6105941 := bbase (se 9 (by rfl) ⟨17888, by rfl⟩ : syracuseStep 6105941 = 35777) (by norm_num)
theorem B1526617 : Blo 1204419 1526617 := bbase (se 2 (by rfl) ⟨572481, by rfl⟩ : syracuseStep 1526617 = 1144963) (by norm_num)
theorem B2575253 : Blo 1204419 2575253 := bbase (se 6 (by rfl) ⟨60357, by rfl⟩ : syracuseStep 2575253 = 120715) (by norm_num)
theorem B2575261 : Blo 1204419 2575261 := bbase (se 3 (by rfl) ⟨482861, by rfl⟩ : syracuseStep 2575261 = 965723) (by norm_num)
theorem B2034605 : Blo 1204419 2034605 := bbase (se 3 (by rfl) ⟨381488, by rfl⟩ : syracuseStep 2034605 = 762977) (by norm_num)
theorem B3861445 : Blo 1204419 3861445 := bbase (se 4 (by rfl) ⟨362010, by rfl⟩ : syracuseStep 3861445 = 724021) (by norm_num)
theorem B1526789 : Blo 1204419 1526789 := bbase (se 4 (by rfl) ⟨143136, by rfl⟩ : syracuseStep 1526789 = 286273) (by norm_num)
theorem B2034733 : Blo 1204419 2034733 := bbase (se 3 (by rfl) ⟨381512, by rfl⟩ : syracuseStep 2034733 = 763025) (by norm_num)
theorem B1526845 : Blo 1204419 1526845 := bbase (se 3 (by rfl) ⟨286283, by rfl⟩ : syracuseStep 1526845 = 572567) (by norm_num)
theorem B1715269 : Blo 1204419 1715269 := bbase (se 4 (by rfl) ⟨160806, by rfl⟩ : syracuseStep 1715269 = 321613) (by norm_num)
theorem B3050581 : Blo 1204419 3050581 := bbase (se 8 (by rfl) ⟨17874, by rfl⟩ : syracuseStep 3050581 = 35749) (by norm_num)
theorem B2288749 : Blo 1204419 2288749 := bbase (se 3 (by rfl) ⟨429140, by rfl⟩ : syracuseStep 2288749 = 858281) (by norm_num)
theorem B2034821 : Blo 1204419 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B4066469 : Blo 1204419 4066469 := bbase (se 4 (by rfl) ⟨381231, by rfl⟩ : syracuseStep 4066469 = 762463) (by norm_num)
theorem B2935997 : Blo 1204419 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B3050693 : Blo 1204419 3050693 := bbase (se 4 (by rfl) ⟨286002, by rfl⟩ : syracuseStep 3050693 = 572005) (by norm_num)
theorem B4885717 : Blo 1204419 4885717 := bbase (se 7 (by rfl) ⟨57254, by rfl⟩ : syracuseStep 4885717 = 114509) (by norm_num)
theorem B1354981 : Blo 1204419 1354981 := bbase (se 4 (by rfl) ⟨127029, by rfl⟩ : syracuseStep 1354981 = 254059) (by norm_num)
theorem B6098165 : Blo 1204419 6098165 := bbase (se 5 (by rfl) ⟨285851, by rfl⟩ : syracuseStep 6098165 = 571703) (by norm_num)
theorem B2288893 : Blo 1204419 2288893 := bbase (se 3 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 2288893 = 858335) (by norm_num)
theorem B2034949 : Blo 1204419 2034949 := bbase (se 4 (by rfl) ⟨190776, by rfl⟩ : syracuseStep 2034949 = 381553) (by norm_num)
theorem B1355017 : Blo 1204419 1355017 := bbase (se 2 (by rfl) ⟨508131, by rfl⟩ : syracuseStep 1355017 = 1016263) (by norm_num)
theorem B3665173 : Blo 1204419 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B1355053 : Blo 1204419 1355053 := bbase (se 3 (by rfl) ⟨254072, by rfl⟩ : syracuseStep 1355053 = 508145) (by norm_num)
theorem B1355089 : Blo 1204419 1355089 := bbase (se 2 (by rfl) ⟨508158, by rfl⟩ : syracuseStep 1355089 = 1016317) (by norm_num)
theorem B3345749 : Blo 1204419 3345749 := bbase (se 11 (by rfl) ⟨2450, by rfl⟩ : syracuseStep 3345749 = 4901) (by norm_num)
theorem B2035037 : Blo 1204419 2035037 := bbase (se 3 (by rfl) ⟨381569, by rfl⟩ : syracuseStep 2035037 = 763139) (by norm_num)
theorem B1355125 : Blo 1204419 1355125 := bbase (se 5 (by rfl) ⟨63521, by rfl⟩ : syracuseStep 1355125 = 127043) (by norm_num)
theorem B3050885 : Blo 1204419 3050885 := bbase (se 4 (by rfl) ⟨286020, by rfl⟩ : syracuseStep 3050885 = 572041) (by norm_num)
theorem B3861893 : Blo 1204419 3861893 := bbase (se 4 (by rfl) ⟨362052, by rfl⟩ : syracuseStep 3861893 = 724105) (by norm_num)
theorem B1355161 : Blo 1204419 1355161 := bbase (se 2 (by rfl) ⟨508185, by rfl⟩ : syracuseStep 1355161 = 1016371) (by norm_num)
theorem B2289053 : Blo 1204419 2289053 := bbase (se 3 (by rfl) ⟨429197, by rfl⟩ : syracuseStep 2289053 = 858395) (by norm_num)
theorem B1355197 : Blo 1204419 1355197 := bbase (se 3 (by rfl) ⟨254099, by rfl⟩ : syracuseStep 1355197 = 508199) (by norm_num)
theorem B2035165 : Blo 1204419 2035165 := bbase (se 3 (by rfl) ⟨381593, by rfl⟩ : syracuseStep 2035165 = 763187) (by norm_num)
theorem B1355233 : Blo 1204419 1355233 := bbase (se 2 (by rfl) ⟨508212, by rfl⟩ : syracuseStep 1355233 = 1016425) (by norm_num)
theorem B1355269 : Blo 1204419 1355269 := bbase (se 4 (by rfl) ⟨127056, by rfl⟩ : syracuseStep 1355269 = 254113) (by norm_num)
theorem B1355305 : Blo 1204419 1355305 := bbase (se 2 (by rfl) ⟨508239, by rfl⟩ : syracuseStep 1355305 = 1016479) (by norm_num)
theorem B2289197 : Blo 1204419 2289197 := bbase (se 3 (by rfl) ⟨429224, by rfl⟩ : syracuseStep 2289197 = 858449) (by norm_num)
theorem B2035253 : Blo 1204419 2035253 := bbase (se 5 (by rfl) ⟨95402, by rfl⟩ : syracuseStep 2035253 = 190805) (by norm_num)
theorem B2895421 : Blo 1204419 2895421 := bbase (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) (by norm_num)
theorem B1355341 : Blo 1204419 1355341 := bbase (se 3 (by rfl) ⟨254126, by rfl⟩ : syracuseStep 1355341 = 508253) (by norm_num)
theorem B4066901 : Blo 1204419 4066901 := bbase (se 8 (by rfl) ⟨23829, by rfl⟩ : syracuseStep 4066901 = 47659) (by norm_num)
theorem B1355377 : Blo 1204419 1355377 := bbase (se 2 (by rfl) ⟨508266, by rfl⟩ : syracuseStep 1355377 = 1016533) (by norm_num)
theorem B1412725 : Blo 1204419 1412725 := bbase (se 5 (by rfl) ⟨66221, by rfl⟩ : syracuseStep 1412725 = 132443) (by norm_num)
theorem B1355413 : Blo 1204419 1355413 := bbase (se 6 (by rfl) ⟨31767, by rfl⟩ : syracuseStep 1355413 = 63535) (by norm_num)
theorem B1715861 : Blo 1204419 1715861 := bbase (se 6 (by rfl) ⟨40215, by rfl⟩ : syracuseStep 1715861 = 80431) (by norm_num)
theorem B2608805 : Blo 1204419 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B2035381 : Blo 1204419 2035381 := bbase (se 5 (by rfl) ⟨95408, by rfl⟩ : syracuseStep 2035381 = 190817) (by norm_num)
theorem B1355449 : Blo 1204419 1355449 := bbase (se 2 (by rfl) ⟨508293, by rfl⟩ : syracuseStep 1355449 = 1016587) (by norm_num)
theorem B1355485 : Blo 1204419 1355485 := bbase (se 3 (by rfl) ⟨254153, by rfl⟩ : syracuseStep 1355485 = 508307) (by norm_num)
theorem B3051229 : Blo 1204419 3051229 := bbase (se 3 (by rfl) ⟨572105, by rfl⟩ : syracuseStep 3051229 = 1144211) (by norm_num)
theorem B1715941 : Blo 1204419 1715941 := bbase (se 4 (by rfl) ⟨160869, by rfl⟩ : syracuseStep 1715941 = 321739) (by norm_num)
theorem B1355521 : Blo 1204419 1355521 := bbase (se 2 (by rfl) ⟨508320, by rfl⟩ : syracuseStep 1355521 = 1016641) (by norm_num)
theorem B2035469 : Blo 1204419 2035469 := bbase (se 3 (by rfl) ⟨381650, by rfl⟩ : syracuseStep 2035469 = 763301) (by norm_num)
theorem B1355557 : Blo 1204419 1355557 := bbase (se 4 (by rfl) ⟨127083, by rfl⟩ : syracuseStep 1355557 = 254167) (by norm_num)
theorem B1355593 : Blo 1204419 1355593 := bbase (se 2 (by rfl) ⟨508347, by rfl⟩ : syracuseStep 1355593 = 1016695) (by norm_num)
theorem B3051341 : Blo 1204419 3051341 := bbase (se 3 (by rfl) ⟨572126, by rfl⟩ : syracuseStep 3051341 = 1144253) (by norm_num)
theorem B2289485 : Blo 1204419 2289485 := bbase (se 3 (by rfl) ⟨429278, by rfl⟩ : syracuseStep 2289485 = 858557) (by norm_num)
theorem B1740629 : Blo 1204419 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1716061 : Blo 1204419 1716061 := bbase (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) (by norm_num)
theorem B1355629 : Blo 1204419 1355629 := bbase (se 3 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 1355629 = 508361) (by norm_num)
theorem B11587445 : Blo 1204419 11587445 := bbase (se 5 (by rfl) ⟨543161, by rfl⟩ : syracuseStep 11587445 = 1086323) (by norm_num)
theorem B2035597 : Blo 1204419 2035597 := bbase (se 3 (by rfl) ⟨381674, by rfl⟩ : syracuseStep 2035597 = 763349) (by norm_num)
theorem B1355665 : Blo 1204419 1355665 := bbase (se 2 (by rfl) ⟨508374, by rfl⟩ : syracuseStep 1355665 = 1016749) (by norm_num)
theorem B1355701 : Blo 1204419 1355701 := bbase (se 5 (by rfl) ⟨63548, by rfl⟩ : syracuseStep 1355701 = 127097) (by norm_num)
theorem B1716157 : Blo 1204419 1716157 := bbase (se 3 (by rfl) ⟨321779, by rfl⟩ : syracuseStep 1716157 = 643559) (by norm_num)
theorem B1355737 : Blo 1204419 1355737 := bbase (se 2 (by rfl) ⟨508401, by rfl⟩ : syracuseStep 1355737 = 1016803) (by norm_num)
theorem B2289637 : Blo 1204419 2289637 := bbase (se 4 (by rfl) ⟨214653, by rfl⟩ : syracuseStep 2289637 = 429307) (by norm_num)
theorem B2035685 : Blo 1204419 2035685 := bbase (se 4 (by rfl) ⟨190845, by rfl⟩ : syracuseStep 2035685 = 381691) (by norm_num)
theorem B1355773 : Blo 1204419 1355773 := bbase (se 3 (by rfl) ⟨254207, by rfl⟩ : syracuseStep 1355773 = 508415) (by norm_num)
theorem B4067333 : Blo 1204419 4067333 := bbase (se 4 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 4067333 = 762625) (by norm_num)
theorem B5148677 : Blo 1204419 5148677 := bbase (se 4 (by rfl) ⟨482688, by rfl⟩ : syracuseStep 5148677 = 965377) (by norm_num)
theorem B2576389 : Blo 1204419 2576389 := bbase (se 4 (by rfl) ⟨241536, by rfl⟩ : syracuseStep 2576389 = 483073) (by norm_num)
theorem B3051533 : Blo 1204419 3051533 := bbase (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) (by norm_num)
theorem B2748437 : Blo 1204419 2748437 := bbase (se 6 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 2748437 = 128833) (by norm_num)
theorem B1355809 : Blo 1204419 1355809 := bbase (se 2 (by rfl) ⟨508428, by rfl⟩ : syracuseStep 1355809 = 1016857) (by norm_num)
theorem B1355845 : Blo 1204419 1355845 := bbase (se 4 (by rfl) ⟨127110, by rfl⟩ : syracuseStep 1355845 = 254221) (by norm_num)
theorem B6107237 : Blo 1204419 6107237 := bbase (se 4 (by rfl) ⟨572553, by rfl⟩ : syracuseStep 6107237 = 1145107) (by norm_num)
theorem B2035813 : Blo 1204419 2035813 := bbase (se 4 (by rfl) ⟨190857, by rfl⟩ : syracuseStep 2035813 = 381715) (by norm_num)
theorem B1355881 : Blo 1204419 1355881 := bbase (se 2 (by rfl) ⟨508455, by rfl⟩ : syracuseStep 1355881 = 1016911) (by norm_num)
theorem B4345973 : Blo 1204419 4345973 := bbase (se 5 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 4345973 = 407435) (by norm_num)
theorem B1355917 : Blo 1204419 1355917 := bbase (se 3 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 1355917 = 508469) (by norm_num)
theorem B2896037 : Blo 1204419 2896037 := bbase (se 4 (by rfl) ⟨271503, by rfl⟩ : syracuseStep 2896037 = 543007) (by norm_num)
theorem B1355953 : Blo 1204419 1355953 := bbase (se 2 (by rfl) ⟨508482, by rfl⟩ : syracuseStep 1355953 = 1016965) (by norm_num)
theorem B1355989 : Blo 1204419 1355989 := bbase (se 7 (by rfl) ⟨15890, by rfl⟩ : syracuseStep 1355989 = 31781) (by norm_num)
theorem B14110933 : Blo 1204419 14110933 := bbase (se 7 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 14110933 = 330725) (by norm_num)
theorem B5148917 : Blo 1204419 5148917 := bbase (se 5 (by rfl) ⟨241355, by rfl⟩ : syracuseStep 5148917 = 482711) (by norm_num)
theorem B1356025 : Blo 1204419 1356025 := bbase (se 2 (by rfl) ⟨508509, by rfl⟩ : syracuseStep 1356025 = 1017019) (by norm_num)
theorem B2289941 : Blo 1204419 2289941 := bbase (se 6 (by rfl) ⟨53670, by rfl⟩ : syracuseStep 2289941 = 107341) (by norm_num)
theorem B1356061 : Blo 1204419 1356061 := bbase (se 3 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 1356061 = 508523) (by norm_num)
theorem B1806629 : Blo 1204419 1806629 := bbase (se 4 (by rfl) ⟨169371, by rfl⟩ : syracuseStep 1806629 = 338743) (by norm_num)
theorem B1806653 : Blo 1204419 1806653 := bbase (se 3 (by rfl) ⟨338747, by rfl⟩ : syracuseStep 1806653 = 677495) (by norm_num)
theorem B1356097 : Blo 1204419 1356097 := bbase (se 2 (by rfl) ⟨508536, by rfl⟩ : syracuseStep 1356097 = 1017073) (by norm_num)
theorem B3092813 : Blo 1204419 3092813 := bbase (se 3 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 3092813 = 1159805) (by norm_num)
theorem B1806677 : Blo 1204419 1806677 := bbase (se 10 (by rfl) ⟨2646, by rfl⟩ : syracuseStep 1806677 = 5293) (by norm_num)
theorem B1356133 : Blo 1204419 1356133 := bbase (se 4 (by rfl) ⟨127137, by rfl⟩ : syracuseStep 1356133 = 254275) (by norm_num)
theorem B3051877 : Blo 1204419 3051877 := bbase (se 4 (by rfl) ⟨286113, by rfl⟩ : syracuseStep 3051877 = 572227) (by norm_num)
theorem B1806701 : Blo 1204419 1806701 := bbase (se 3 (by rfl) ⟨338756, by rfl⟩ : syracuseStep 1806701 = 677513) (by norm_num)
theorem B1806725 : Blo 1204419 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B1356169 : Blo 1204419 1356169 := bbase (se 2 (by rfl) ⟨508563, by rfl⟩ : syracuseStep 1356169 = 1017127) (by norm_num)
theorem B1806749 : Blo 1204419 1806749 := bbase (se 3 (by rfl) ⟨338765, by rfl⟩ : syracuseStep 1806749 = 677531) (by norm_num)
theorem B1356205 : Blo 1204419 1356205 := bbase (se 3 (by rfl) ⟨254288, by rfl⟩ : syracuseStep 1356205 = 508577) (by norm_num)
theorem B1716653 : Blo 1204419 1716653 := bbase (se 3 (by rfl) ⟨321872, by rfl⟩ : syracuseStep 1716653 = 643745) (by norm_num)
theorem B1806773 : Blo 1204419 1806773 := bbase (se 5 (by rfl) ⟨84692, by rfl⟩ : syracuseStep 1806773 = 169385) (by norm_num)
theorem B4067765 : Blo 1204419 4067765 := bbase (se 5 (by rfl) ⟨190676, by rfl⟩ : syracuseStep 4067765 = 381353) (by norm_num)
theorem B1806797 : Blo 1204419 1806797 := bbase (se 3 (by rfl) ⟨338774, by rfl⟩ : syracuseStep 1806797 = 677549) (by norm_num)
theorem B1356241 : Blo 1204419 1356241 := bbase (se 2 (by rfl) ⟨508590, by rfl⟩ : syracuseStep 1356241 = 1017181) (by norm_num)
theorem B3051989 : Blo 1204419 3051989 := bbase (se 7 (by rfl) ⟨35765, by rfl⟩ : syracuseStep 3051989 = 71531) (by norm_num)
theorem B1806821 : Blo 1204419 1806821 := bbase (se 4 (by rfl) ⟨169389, by rfl⟩ : syracuseStep 1806821 = 338779) (by norm_num)
theorem B1356277 : Blo 1204419 1356277 := bbase (se 5 (by rfl) ⟨63575, by rfl⟩ : syracuseStep 1356277 = 127151) (by norm_num)
theorem B1806845 : Blo 1204419 1806845 := bbase (se 3 (by rfl) ⟨338783, by rfl⟩ : syracuseStep 1806845 = 677567) (by norm_num)
theorem B2200069 : Blo 1204419 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B6099461 : Blo 1204419 6099461 := bbase (se 4 (by rfl) ⟨571824, by rfl⟩ : syracuseStep 6099461 = 1143649) (by norm_num)
theorem B1806869 : Blo 1204419 1806869 := bbase (se 6 (by rfl) ⟨42348, by rfl⟩ : syracuseStep 1806869 = 84697) (by norm_num)
theorem B9777685 : Blo 1204419 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B4346389 : Blo 1204419 4346389 := bbase (se 6 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 4346389 = 203737) (by norm_num)
theorem B1356313 : Blo 1204419 1356313 := bbase (se 2 (by rfl) ⟨508617, by rfl⟩ : syracuseStep 1356313 = 1017235) (by norm_num)
theorem B1806893 : Blo 1204419 1806893 := bbase (se 3 (by rfl) ⟨338792, by rfl⟩ : syracuseStep 1806893 = 677585) (by norm_num)
theorem B4575797 : Blo 1204419 4575797 := bbase (se 5 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 4575797 = 428981) (by norm_num)
theorem B1356349 : Blo 1204419 1356349 := bbase (se 3 (by rfl) ⟨254315, by rfl⟩ : syracuseStep 1356349 = 508631) (by norm_num)
theorem B1806917 : Blo 1204419 1806917 := bbase (se 4 (by rfl) ⟨169398, by rfl⟩ : syracuseStep 1806917 = 338797) (by norm_num)
theorem B2609741 : Blo 1204419 2609741 := bbase (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) (by norm_num)
theorem B2896469 : Blo 1204419 2896469 := bbase (se 8 (by rfl) ⟨16971, by rfl⟩ : syracuseStep 2896469 = 33943) (by norm_num)
theorem B1806941 : Blo 1204419 1806941 := bbase (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) (by norm_num)
theorem B1356385 : Blo 1204419 1356385 := bbase (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) (by norm_num)
theorem B1806965 : Blo 1204419 1806965 := bbase (se 5 (by rfl) ⟨84701, by rfl⟩ : syracuseStep 1806965 = 169403) (by norm_num)
theorem B1323649 : Blo 1204419 1323649 := bbase (se 2 (by rfl) ⟨496368, by rfl⟩ : syracuseStep 1323649 = 992737) (by norm_num)
theorem B1356421 : Blo 1204419 1356421 := bbase (se 4 (by rfl) ⟨127164, by rfl⟩ : syracuseStep 1356421 = 254329) (by norm_num)
theorem B1806989 : Blo 1204419 1806989 := bbase (se 3 (by rfl) ⟨338810, by rfl⟩ : syracuseStep 1806989 = 677621) (by norm_num)
theorem B3052181 : Blo 1204419 3052181 := bbase (se 6 (by rfl) ⟨71535, by rfl⟩ : syracuseStep 3052181 = 143071) (by norm_num)
theorem B1807013 : Blo 1204419 1807013 := bbase (se 4 (by rfl) ⟨169407, by rfl⟩ : syracuseStep 1807013 = 338815) (by norm_num)
theorem B1356457 : Blo 1204419 1356457 := bbase (se 2 (by rfl) ⟨508671, by rfl⟩ : syracuseStep 1356457 = 1017343) (by norm_num)
theorem B1807037 : Blo 1204419 1807037 := bbase (se 3 (by rfl) ⟨338819, by rfl⟩ : syracuseStep 1807037 = 677639) (by norm_num)
theorem B1356493 : Blo 1204419 1356493 := bbase (se 3 (by rfl) ⟨254342, by rfl⟩ : syracuseStep 1356493 = 508685) (by norm_num)
theorem B1807061 : Blo 1204419 1807061 := bbase (se 7 (by rfl) ⟨21176, by rfl⟩ : syracuseStep 1807061 = 42353) (by norm_num)
theorem B1807085 : Blo 1204419 1807085 := bbase (se 3 (by rfl) ⟨338828, by rfl⟩ : syracuseStep 1807085 = 677657) (by norm_num)
theorem B1356529 : Blo 1204419 1356529 := bbase (se 2 (by rfl) ⟨508698, by rfl⟩ : syracuseStep 1356529 = 1017397) (by norm_num)
theorem B1807109 : Blo 1204419 1807109 := bbase (se 4 (by rfl) ⟨169416, by rfl⟩ : syracuseStep 1807109 = 338833) (by norm_num)
theorem B1356565 : Blo 1204419 1356565 := bbase (se 6 (by rfl) ⟨31794, by rfl⟩ : syracuseStep 1356565 = 63589) (by norm_num)
theorem B5796629 : Blo 1204419 5796629 := bbase (se 6 (by rfl) ⟨135858, by rfl⟩ : syracuseStep 5796629 = 271717) (by norm_num)
theorem B1807133 : Blo 1204419 1807133 := bbase (se 3 (by rfl) ⟨338837, by rfl⟩ : syracuseStep 1807133 = 677675) (by norm_num)
theorem B1807157 : Blo 1204419 1807157 := bbase (se 5 (by rfl) ⟨84710, by rfl⟩ : syracuseStep 1807157 = 169421) (by norm_num)
theorem B1356601 : Blo 1204419 1356601 := bbase (se 2 (by rfl) ⟨508725, by rfl⟩ : syracuseStep 1356601 = 1017451) (by norm_num)
theorem B1807181 : Blo 1204419 1807181 := bbase (se 3 (by rfl) ⟨338846, by rfl⟩ : syracuseStep 1807181 = 677693) (by norm_num)
theorem B4576085 : Blo 1204419 4576085 := bbase (se 9 (by rfl) ⟨13406, by rfl⟩ : syracuseStep 4576085 = 26813) (by norm_num)
theorem B1356637 : Blo 1204419 1356637 := bbase (se 3 (by rfl) ⟨254369, by rfl⟩ : syracuseStep 1356637 = 508739) (by norm_num)
theorem B1807205 : Blo 1204419 1807205 := bbase (se 4 (by rfl) ⟨169425, by rfl⟩ : syracuseStep 1807205 = 338851) (by norm_num)
theorem B4068197 : Blo 1204419 4068197 := bbase (se 4 (by rfl) ⟨381393, by rfl⟩ : syracuseStep 4068197 = 762787) (by norm_num)
theorem B1807229 : Blo 1204419 1807229 := bbase (se 3 (by rfl) ⟨338855, by rfl⟩ : syracuseStep 1807229 = 677711) (by norm_num)
theorem B1356673 : Blo 1204419 1356673 := bbase (se 2 (by rfl) ⟨508752, by rfl⟩ : syracuseStep 1356673 = 1017505) (by norm_num)
theorem B1807253 : Blo 1204419 1807253 := bbase (se 6 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 1807253 = 84715) (by norm_num)
theorem B1356709 : Blo 1204419 1356709 := bbase (se 4 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 1356709 = 254383) (by norm_num)
theorem B1807277 : Blo 1204419 1807277 := bbase (se 3 (by rfl) ⟨338864, by rfl⟩ : syracuseStep 1807277 = 677729) (by norm_num)
theorem B1807301 : Blo 1204419 1807301 := bbase (se 4 (by rfl) ⟨169434, by rfl⟩ : syracuseStep 1807301 = 338869) (by norm_num)
theorem B1356745 : Blo 1204419 1356745 := bbase (se 2 (by rfl) ⟨508779, by rfl⟩ : syracuseStep 1356745 = 1017559) (by norm_num)
theorem B1717205 : Blo 1204419 1717205 := bbase (se 7 (by rfl) ⟨20123, by rfl⟩ : syracuseStep 1717205 = 40247) (by norm_num)
theorem B1807325 : Blo 1204419 1807325 := bbase (se 3 (by rfl) ⟨338873, by rfl⟩ : syracuseStep 1807325 = 677747) (by norm_num)
theorem B3052525 : Blo 1204419 3052525 := bbase (se 3 (by rfl) ⟨572348, by rfl⟩ : syracuseStep 3052525 = 1144697) (by norm_num)
theorem B1356781 : Blo 1204419 1356781 := bbase (se 3 (by rfl) ⟨254396, by rfl⟩ : syracuseStep 1356781 = 508793) (by norm_num)
theorem B1807349 : Blo 1204419 1807349 := bbase (se 5 (by rfl) ⟨84719, by rfl⟩ : syracuseStep 1807349 = 169439) (by norm_num)
theorem B6870005 : Blo 1204419 6870005 := bbase (se 5 (by rfl) ⟨322031, by rfl⟩ : syracuseStep 6870005 = 644063) (by norm_num)
theorem B1807373 : Blo 1204419 1807373 := bbase (se 3 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 1807373 = 677765) (by norm_num)
theorem B1356817 : Blo 1204419 1356817 := bbase (se 2 (by rfl) ⟨508806, by rfl⟩ : syracuseStep 1356817 = 1017613) (by norm_num)
theorem B1807397 : Blo 1204419 1807397 := bbase (se 4 (by rfl) ⟨169443, by rfl⟩ : syracuseStep 1807397 = 338887) (by norm_num)
theorem B1356853 : Blo 1204419 1356853 := bbase (se 5 (by rfl) ⟨63602, by rfl⟩ : syracuseStep 1356853 = 127205) (by norm_num)
theorem B1807421 : Blo 1204419 1807421 := bbase (se 3 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 1807421 = 677783) (by norm_num)
theorem B2864189 : Blo 1204419 2864189 := bbase (se 3 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 2864189 = 1074071) (by norm_num)
theorem B1446989 : Blo 1204419 1446989 := bbase (se 3 (by rfl) ⟨271310, by rfl⟩ : syracuseStep 1446989 = 542621) (by norm_num)
theorem B1545301 : Blo 1204419 1545301 := bbase (se 8 (by rfl) ⟨9054, by rfl⟩ : syracuseStep 1545301 = 18109) (by norm_num)
theorem B1807445 : Blo 1204419 1807445 := bbase (se 8 (by rfl) ⟨10590, by rfl⟩ : syracuseStep 1807445 = 21181) (by norm_num)
theorem B1356889 : Blo 1204419 1356889 := bbase (se 2 (by rfl) ⟨508833, by rfl⟩ : syracuseStep 1356889 = 1017667) (by norm_num)
theorem B3052637 : Blo 1204419 3052637 := bbase (se 3 (by rfl) ⟨572369, by rfl⟩ : syracuseStep 3052637 = 1144739) (by norm_num)
theorem B1545313 : Blo 1204419 1545313 := bbase (se 2 (by rfl) ⟨579492, by rfl⟩ : syracuseStep 1545313 = 1158985) (by norm_num)
theorem B1807469 : Blo 1204419 1807469 := bbase (se 3 (by rfl) ⟨338900, by rfl⟩ : syracuseStep 1807469 = 677801) (by norm_num)
theorem B6861941 : Blo 1204419 6861941 := bbase (se 5 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 6861941 = 643307) (by norm_num)
theorem B1356925 : Blo 1204419 1356925 := bbase (se 3 (by rfl) ⟨254423, by rfl⟩ : syracuseStep 1356925 = 508847) (by norm_num)
theorem B1807493 : Blo 1204419 1807493 := bbase (se 4 (by rfl) ⟨169452, by rfl⟩ : syracuseStep 1807493 = 338905) (by norm_num)
theorem B1807517 : Blo 1204419 1807517 := bbase (se 3 (by rfl) ⟨338909, by rfl⟩ : syracuseStep 1807517 = 677819) (by norm_num)
theorem B1356961 : Blo 1204419 1356961 := bbase (se 2 (by rfl) ⟨508860, by rfl⟩ : syracuseStep 1356961 = 1017721) (by norm_num)
theorem B1807541 : Blo 1204419 1807541 := bbase (se 5 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 1807541 = 169457) (by norm_num)
theorem B1930421 : Blo 1204419 1930421 := bbase (se 5 (by rfl) ⟨90488, by rfl⟩ : syracuseStep 1930421 = 180977) (by norm_num)
theorem B1356997 : Blo 1204419 1356997 := bbase (se 4 (by rfl) ⟨127218, by rfl⟩ : syracuseStep 1356997 = 254437) (by norm_num)
theorem B1545421 : Blo 1204419 1545421 := bbase (se 3 (by rfl) ⟨289766, by rfl⟩ : syracuseStep 1545421 = 579533) (by norm_num)
theorem B1807565 : Blo 1204419 1807565 := bbase (se 3 (by rfl) ⟨338918, by rfl⟩ : syracuseStep 1807565 = 677837) (by norm_num)
theorem B1807589 : Blo 1204419 1807589 := bbase (se 4 (by rfl) ⟨169461, by rfl⟩ : syracuseStep 1807589 = 338923) (by norm_num)
theorem B1357033 : Blo 1204419 1357033 := bbase (se 2 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 1357033 = 1017775) (by norm_num)
theorem B1807613 : Blo 1204419 1807613 := bbase (se 3 (by rfl) ⟨338927, by rfl⟩ : syracuseStep 1807613 = 677855) (by norm_num)
theorem B1357069 : Blo 1204419 1357069 := bbase (se 3 (by rfl) ⟨254450, by rfl⟩ : syracuseStep 1357069 = 508901) (by norm_num)
theorem B1807637 : Blo 1204419 1807637 := bbase (se 6 (by rfl) ⟨42366, by rfl⟩ : syracuseStep 1807637 = 84733) (by norm_num)
theorem B4068629 : Blo 1204419 4068629 := bbase (se 6 (by rfl) ⟨95358, by rfl⟩ : syracuseStep 4068629 = 190717) (by norm_num)
theorem B3052829 : Blo 1204419 3052829 := bbase (se 3 (by rfl) ⟨572405, by rfl⟩ : syracuseStep 3052829 = 1144811) (by norm_num)
theorem B1807661 : Blo 1204419 1807661 := bbase (se 3 (by rfl) ⟨338936, by rfl⟩ : syracuseStep 1807661 = 677873) (by norm_num)
theorem B1357105 : Blo 1204419 1357105 := bbase (se 2 (by rfl) ⟨508914, by rfl⟩ : syracuseStep 1357105 = 1017829) (by norm_num)
theorem B1930549 : Blo 1204419 1930549 := bbase (se 5 (by rfl) ⟨90494, by rfl⟩ : syracuseStep 1930549 = 180989) (by norm_num)
theorem B1807685 : Blo 1204419 1807685 := bbase (se 4 (by rfl) ⟨169470, by rfl⟩ : syracuseStep 1807685 = 338941) (by norm_num)
theorem B32986453 : Blo 1204419 32986453 := bbase (se 17 (by rfl) ⟨377, by rfl⟩ : syracuseStep 32986453 = 755) (by norm_num)
theorem B1357141 : Blo 1204419 1357141 := bbase (se 13 (by rfl) ⟨248, by rfl⟩ : syracuseStep 1357141 = 497) (by norm_num)
theorem B1807709 : Blo 1204419 1807709 := bbase (se 3 (by rfl) ⟨338945, by rfl⟩ : syracuseStep 1807709 = 677891) (by norm_num)
theorem B1807733 : Blo 1204419 1807733 := bbase (se 5 (by rfl) ⟨84737, by rfl⟩ : syracuseStep 1807733 = 169475) (by norm_num)
theorem B1357177 : Blo 1204419 1357177 := bbase (se 2 (by rfl) ⟨508941, by rfl⟩ : syracuseStep 1357177 = 1017883) (by norm_num)
theorem B1807757 : Blo 1204419 1807757 := bbase (se 3 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 1807757 = 677909) (by norm_num)
theorem B10990997 : Blo 1204419 10990997 := bbase (se 6 (by rfl) ⟨257601, by rfl⟩ : syracuseStep 10990997 = 515203) (by norm_num)
theorem B1357213 : Blo 1204419 1357213 := bbase (se 3 (by rfl) ⟨254477, by rfl⟩ : syracuseStep 1357213 = 508955) (by norm_num)
theorem B1807781 : Blo 1204419 1807781 := bbase (se 4 (by rfl) ⟨169479, by rfl⟩ : syracuseStep 1807781 = 338959) (by norm_num)
theorem B1807805 : Blo 1204419 1807805 := bbase (se 3 (by rfl) ⟨338963, by rfl⟩ : syracuseStep 1807805 = 677927) (by norm_num)
theorem B1807829 : Blo 1204419 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B1807853 : Blo 1204419 1807853 := bbase (se 3 (by rfl) ⟨338972, by rfl⟩ : syracuseStep 1807853 = 677945) (by norm_num)
theorem B3429877 : Blo 1204419 3429877 := bbase (se 5 (by rfl) ⟨160775, by rfl⟩ : syracuseStep 3429877 = 321551) (by norm_num)
theorem B1807877 : Blo 1204419 1807877 := bbase (se 4 (by rfl) ⟨169488, by rfl⟩ : syracuseStep 1807877 = 338977) (by norm_num)
theorem B1807901 : Blo 1204419 1807901 := bbase (se 3 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 1807901 = 677963) (by norm_num)
theorem B1807925 : Blo 1204419 1807925 := bbase (se 5 (by rfl) ⟨84746, by rfl⟩ : syracuseStep 1807925 = 169493) (by norm_num)
theorem B4126277 : Blo 1204419 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B1807949 : Blo 1204419 1807949 := bbase (se 3 (by rfl) ⟨338990, by rfl⟩ : syracuseStep 1807949 = 677981) (by norm_num)
theorem B3864149 : Blo 1204419 3864149 := bbase (se 8 (by rfl) ⟨22641, by rfl⟩ : syracuseStep 3864149 = 45283) (by norm_num)
theorem B1807973 : Blo 1204419 1807973 := bbase (se 4 (by rfl) ⟨169497, by rfl⟩ : syracuseStep 1807973 = 338995) (by norm_num)
theorem B1652341 : Blo 1204419 1652341 := bbase (se 5 (by rfl) ⟨77453, by rfl⟩ : syracuseStep 1652341 = 154907) (by norm_num)
theorem B3053173 : Blo 1204419 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B1807997 : Blo 1204419 1807997 := bbase (se 3 (by rfl) ⟨338999, by rfl⟩ : syracuseStep 1807997 = 677999) (by norm_num)
theorem B1808021 : Blo 1204419 1808021 := bbase (se 6 (by rfl) ⟨42375, by rfl⟩ : syracuseStep 1808021 = 84751) (by norm_num)
theorem B1808045 : Blo 1204419 1808045 := bbase (se 3 (by rfl) ⟨339008, by rfl⟩ : syracuseStep 1808045 = 678017) (by norm_num)
theorem B1808069 : Blo 1204419 1808069 := bbase (se 4 (by rfl) ⟨169506, by rfl⟩ : syracuseStep 1808069 = 339013) (by norm_num)
theorem B4069061 : Blo 1204419 4069061 := bbase (se 4 (by rfl) ⟨381474, by rfl⟩ : syracuseStep 4069061 = 762949) (by norm_num)
theorem B1808093 : Blo 1204419 1808093 := bbase (se 3 (by rfl) ⟨339017, by rfl⟩ : syracuseStep 1808093 = 678035) (by norm_num)
theorem B3053285 : Blo 1204419 3053285 := bbase (se 4 (by rfl) ⟨286245, by rfl⟩ : syracuseStep 3053285 = 572491) (by norm_num)
theorem B1808117 : Blo 1204419 1808117 := bbase (se 5 (by rfl) ⟨84755, by rfl⟩ : syracuseStep 1808117 = 169511) (by norm_num)
theorem B4888325 : Blo 1204419 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B2750213 : Blo 1204419 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B2897669 : Blo 1204419 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B1808141 : Blo 1204419 1808141 := bbase (se 3 (by rfl) ⟨339026, by rfl⟩ : syracuseStep 1808141 = 678053) (by norm_num)
theorem B6100757 : Blo 1204419 6100757 := bbase (se 6 (by rfl) ⟨142986, by rfl⟩ : syracuseStep 6100757 = 285973) (by norm_num)
theorem B1808165 : Blo 1204419 1808165 := bbase (se 4 (by rfl) ⟨169515, by rfl⟩ : syracuseStep 1808165 = 339031) (by norm_num)
theorem B1808189 : Blo 1204419 1808189 := bbase (se 3 (by rfl) ⟨339035, by rfl⟩ : syracuseStep 1808189 = 678071) (by norm_num)
theorem B2201413 : Blo 1204419 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B1808213 : Blo 1204419 1808213 := bbase (se 9 (by rfl) ⟨5297, by rfl⟩ : syracuseStep 1808213 = 10595) (by norm_num)
theorem B1447777 : Blo 1204419 1447777 := bbase (se 2 (by rfl) ⟨542916, by rfl⟩ : syracuseStep 1447777 = 1085833) (by norm_num)
theorem B1808237 : Blo 1204419 1808237 := bbase (se 3 (by rfl) ⟨339044, by rfl⟩ : syracuseStep 1808237 = 678089) (by norm_num)
theorem B1808261 : Blo 1204419 1808261 := bbase (se 4 (by rfl) ⟨169524, by rfl⟩ : syracuseStep 1808261 = 339049) (by norm_num)
theorem B2381717 : Blo 1204419 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B5502869 : Blo 1204419 5502869 := bbase (se 6 (by rfl) ⟨128973, by rfl⟩ : syracuseStep 5502869 = 257947) (by norm_num)
theorem B1808285 : Blo 1204419 1808285 := bbase (se 3 (by rfl) ⟨339053, by rfl⟩ : syracuseStep 1808285 = 678107) (by norm_num)
theorem B3053477 : Blo 1204419 3053477 := bbase (se 4 (by rfl) ⟨286263, by rfl⟩ : syracuseStep 3053477 = 572527) (by norm_num)
theorem B1808309 : Blo 1204419 1808309 := bbase (se 5 (by rfl) ⟨84764, by rfl⟩ : syracuseStep 1808309 = 169529) (by norm_num)
theorem B1628101 : Blo 1204419 1628101 := bbase (se 4 (by rfl) ⟨152634, by rfl⟩ : syracuseStep 1628101 = 305269) (by norm_num)
theorem B1808333 : Blo 1204419 1808333 := bbase (se 3 (by rfl) ⟨339062, by rfl⟩ : syracuseStep 1808333 = 678125) (by norm_num)
theorem B7722965 : Blo 1204419 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B1808357 : Blo 1204419 1808357 := bbase (se 4 (by rfl) ⟨169533, by rfl⟩ : syracuseStep 1808357 = 339067) (by norm_num)
theorem B4577269 : Blo 1204419 4577269 := bbase (se 5 (by rfl) ⟨214559, by rfl⟩ : syracuseStep 4577269 = 429119) (by norm_num)
theorem B1808381 : Blo 1204419 1808381 := bbase (se 3 (by rfl) ⟨339071, by rfl⟩ : syracuseStep 1808381 = 678143) (by norm_num)
theorem B1808405 : Blo 1204419 1808405 := bbase (se 6 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 1808405 = 84769) (by norm_num)
theorem B1808429 : Blo 1204419 1808429 := bbase (se 3 (by rfl) ⟨339080, by rfl⟩ : syracuseStep 1808429 = 678161) (by norm_num)
theorem B1808453 : Blo 1204419 1808453 := bbase (se 4 (by rfl) ⟨169542, by rfl⟩ : syracuseStep 1808453 = 339085) (by norm_num)
theorem B1808477 : Blo 1204419 1808477 := bbase (se 3 (by rfl) ⟨339089, by rfl⟩ : syracuseStep 1808477 = 678179) (by norm_num)
theorem B1931357 : Blo 1204419 1931357 := bbase (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) (by norm_num)
theorem B1808501 : Blo 1204419 1808501 := bbase (se 5 (by rfl) ⟨84773, by rfl⟩ : syracuseStep 1808501 = 169547) (by norm_num)
theorem B4069493 : Blo 1204419 4069493 := bbase (se 5 (by rfl) ⟨190757, by rfl⟩ : syracuseStep 4069493 = 381515) (by norm_num)
theorem B9156725 : Blo 1204419 9156725 := bbase (se 5 (by rfl) ⟨429221, by rfl⟩ : syracuseStep 9156725 = 858443) (by norm_num)
theorem B1808525 : Blo 1204419 1808525 := bbase (se 3 (by rfl) ⟨339098, by rfl⟩ : syracuseStep 1808525 = 678197) (by norm_num)
theorem B1808549 : Blo 1204419 1808549 := bbase (se 4 (by rfl) ⟨169551, by rfl⟩ : syracuseStep 1808549 = 339103) (by norm_num)
theorem B1808573 : Blo 1204419 1808573 := bbase (se 3 (by rfl) ⟨339107, by rfl⟩ : syracuseStep 1808573 = 678215) (by norm_num)
theorem B1808597 : Blo 1204419 1808597 := bbase (se 7 (by rfl) ⟨21194, by rfl⟩ : syracuseStep 1808597 = 42389) (by norm_num)
theorem B24762581 : Blo 1204419 24762581 := bbase (se 7 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 24762581 = 580373) (by norm_num)
theorem B1808621 : Blo 1204419 1808621 := bbase (se 3 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 1808621 = 678233) (by norm_num)
theorem B3258613 : Blo 1204419 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B6183173 : Blo 1204419 6183173 := bbase (se 4 (by rfl) ⟨579672, by rfl⟩ : syracuseStep 6183173 = 1159345) (by norm_num)
theorem B1808645 : Blo 1204419 1808645 := bbase (se 4 (by rfl) ⟨169560, by rfl⟩ : syracuseStep 1808645 = 339121) (by norm_num)
theorem B1808669 : Blo 1204419 1808669 := bbase (se 3 (by rfl) ⟨339125, by rfl⟩ : syracuseStep 1808669 = 678251) (by norm_num)
theorem B4577573 : Blo 1204419 4577573 := bbase (se 4 (by rfl) ⟨429147, by rfl⟩ : syracuseStep 4577573 = 858295) (by norm_num)
theorem B1808693 : Blo 1204419 1808693 := bbase (se 5 (by rfl) ⟨84782, by rfl⟩ : syracuseStep 1808693 = 169565) (by norm_num)
theorem B1833293 : Blo 1204419 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B1808717 : Blo 1204419 1808717 := bbase (se 3 (by rfl) ⟨339134, by rfl⟩ : syracuseStep 1808717 = 678269) (by norm_num)
theorem B23181653 : Blo 1204419 23181653 := bbase (se 10 (by rfl) ⟨33957, by rfl⟩ : syracuseStep 23181653 = 67915) (by norm_num)
theorem B1808741 : Blo 1204419 1808741 := bbase (se 4 (by rfl) ⟨169569, by rfl⟩ : syracuseStep 1808741 = 339139) (by norm_num)
theorem B1808765 : Blo 1204419 1808765 := bbase (se 3 (by rfl) ⟨339143, by rfl⟩ : syracuseStep 1808765 = 678287) (by norm_num)
theorem B1931645 : Blo 1204419 1931645 := bbase (se 3 (by rfl) ⟨362183, by rfl⟩ : syracuseStep 1931645 = 724367) (by norm_num)
theorem B1808789 : Blo 1204419 1808789 := bbase (se 6 (by rfl) ⟨42393, by rfl⟩ : syracuseStep 1808789 = 84787) (by norm_num)
theorem B1808813 : Blo 1204419 1808813 := bbase (se 3 (by rfl) ⟨339152, by rfl⟩ : syracuseStep 1808813 = 678305) (by norm_num)
theorem B10041781 : Blo 1204419 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B1808837 : Blo 1204419 1808837 := bbase (se 4 (by rfl) ⟨169578, by rfl⟩ : syracuseStep 1808837 = 339157) (by norm_num)
theorem B1808861 : Blo 1204419 1808861 := bbase (se 3 (by rfl) ⟨339161, by rfl⟩ : syracuseStep 1808861 = 678323) (by norm_num)
theorem B2709989 : Blo 1204419 2709989 := bbase (se 4 (by rfl) ⟨254061, by rfl⟩ : syracuseStep 2709989 = 508123) (by norm_num)
theorem B5151205 : Blo 1204419 5151205 := bbase (se 4 (by rfl) ⟨482925, by rfl⟩ : syracuseStep 5151205 = 965851) (by norm_num)
theorem B1808885 : Blo 1204419 1808885 := bbase (se 5 (by rfl) ⟨84791, by rfl⟩ : syracuseStep 1808885 = 169583) (by norm_num)
theorem B1808909 : Blo 1204419 1808909 := bbase (se 3 (by rfl) ⟨339170, by rfl⟩ : syracuseStep 1808909 = 678341) (by norm_num)
theorem B9148949 : Blo 1204419 9148949 := bbase (se 6 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 9148949 = 428857) (by norm_num)
theorem B4069925 : Blo 1204419 4069925 := bbase (se 4 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 4069925 = 763111) (by norm_num)
theorem B1808933 : Blo 1204419 1808933 := bbase (se 4 (by rfl) ⟨169587, by rfl⟩ : syracuseStep 1808933 = 339175) (by norm_num)
theorem B1448489 : Blo 1204419 1448489 := bbase (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) (by norm_num)
theorem B2710061 : Blo 1204419 2710061 := bbase (se 3 (by rfl) ⟨508136, by rfl⟩ : syracuseStep 2710061 = 1016273) (by norm_num)
theorem B1628717 : Blo 1204419 1628717 := bbase (se 3 (by rfl) ⟨305384, by rfl⟩ : syracuseStep 1628717 = 610769) (by norm_num)
theorem B1374769 : Blo 1204419 1374769 := bbase (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) (by norm_num)
theorem B1808957 : Blo 1204419 1808957 := bbase (se 3 (by rfl) ⟨339179, by rfl⟩ : syracuseStep 1808957 = 678359) (by norm_num)
theorem B1808981 : Blo 1204419 1808981 := bbase (se 8 (by rfl) ⟨10599, by rfl⟩ : syracuseStep 1808981 = 21199) (by norm_num)
theorem B1809005 : Blo 1204419 1809005 := bbase (se 3 (by rfl) ⟨339188, by rfl⟩ : syracuseStep 1809005 = 678377) (by norm_num)
theorem B2710133 : Blo 1204419 2710133 := bbase (se 5 (by rfl) ⟨127037, by rfl⟩ : syracuseStep 2710133 = 254075) (by norm_num)
theorem B1809029 : Blo 1204419 1809029 := bbase (se 4 (by rfl) ⟨169596, by rfl⟩ : syracuseStep 1809029 = 339193) (by norm_num)
theorem B1809053 : Blo 1204419 1809053 := bbase (se 3 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 1809053 = 678395) (by norm_num)
theorem B1809077 : Blo 1204419 1809077 := bbase (se 5 (by rfl) ⟨84800, by rfl⟩ : syracuseStep 1809077 = 169601) (by norm_num)
theorem B2710205 : Blo 1204419 2710205 := bbase (se 3 (by rfl) ⟨508163, by rfl⟩ : syracuseStep 2710205 = 1016327) (by norm_num)
theorem B1809101 : Blo 1204419 1809101 := bbase (se 3 (by rfl) ⟨339206, by rfl⟩ : syracuseStep 1809101 = 678413) (by norm_num)
theorem B1809125 : Blo 1204419 1809125 := bbase (se 4 (by rfl) ⟨169605, by rfl⟩ : syracuseStep 1809125 = 339211) (by norm_num)
theorem B1809149 : Blo 1204419 1809149 := bbase (se 3 (by rfl) ⟨339215, by rfl⟩ : syracuseStep 1809149 = 678431) (by norm_num)
theorem B2710277 : Blo 1204419 2710277 := bbase (se 4 (by rfl) ⟨254088, by rfl⟩ : syracuseStep 2710277 = 508177) (by norm_num)
theorem B1809173 : Blo 1204419 1809173 := bbase (se 6 (by rfl) ⟨42402, by rfl⟩ : syracuseStep 1809173 = 84805) (by norm_num)
theorem B1932061 : Blo 1204419 1932061 := bbase (se 3 (by rfl) ⟨362261, by rfl⟩ : syracuseStep 1932061 = 724523) (by norm_num)
theorem B1809197 : Blo 1204419 1809197 := bbase (se 3 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 1809197 = 678449) (by norm_num)
theorem B1809221 : Blo 1204419 1809221 := bbase (se 4 (by rfl) ⟨169614, by rfl⟩ : syracuseStep 1809221 = 339229) (by norm_num)
theorem B2710349 : Blo 1204419 2710349 := bbase (se 3 (by rfl) ⟨508190, by rfl⟩ : syracuseStep 2710349 = 1016381) (by norm_num)
theorem B1809245 : Blo 1204419 1809245 := bbase (se 3 (by rfl) ⟨339233, by rfl⟩ : syracuseStep 1809245 = 678467) (by norm_num)
theorem B1809269 : Blo 1204419 1809269 := bbase (se 5 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 1809269 = 169619) (by norm_num)
theorem B1448825 : Blo 1204419 1448825 := bbase (se 2 (by rfl) ⟨543309, by rfl⟩ : syracuseStep 1448825 = 1086619) (by norm_num)
theorem B1809293 : Blo 1204419 1809293 := bbase (se 3 (by rfl) ⟨339242, by rfl⟩ : syracuseStep 1809293 = 678485) (by norm_num)
theorem B2710421 : Blo 1204419 2710421 := bbase (se 6 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 2710421 = 127051) (by norm_num)
theorem B1833877 : Blo 1204419 1833877 := bbase (se 6 (by rfl) ⟨42981, by rfl⟩ : syracuseStep 1833877 = 85963) (by norm_num)
theorem B1375133 : Blo 1204419 1375133 := bbase (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) (by norm_num)
theorem B5790629 : Blo 1204419 5790629 := bbase (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) (by norm_num)
theorem B1809317 : Blo 1204419 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B1809341 : Blo 1204419 1809341 := bbase (se 3 (by rfl) ⟨339251, by rfl⟩ : syracuseStep 1809341 = 678503) (by norm_num)
theorem B4070357 : Blo 1204419 4070357 := bbase (se 7 (by rfl) ⟨47699, by rfl⟩ : syracuseStep 4070357 = 95399) (by norm_num)
theorem B1809365 : Blo 1204419 1809365 := bbase (se 7 (by rfl) ⟨21203, by rfl⟩ : syracuseStep 1809365 = 42407) (by norm_num)
theorem B2710493 : Blo 1204419 2710493 := bbase (se 3 (by rfl) ⟨508217, by rfl⟩ : syracuseStep 2710493 = 1016435) (by norm_num)
theorem B1448941 : Blo 1204419 1448941 := bbase (se 3 (by rfl) ⟨271676, by rfl⟩ : syracuseStep 1448941 = 543353) (by norm_num)
theorem B1809389 : Blo 1204419 1809389 := bbase (se 3 (by rfl) ⟨339260, by rfl⟩ : syracuseStep 1809389 = 678521) (by norm_num)
theorem B1448965 : Blo 1204419 1448965 := bbase (se 4 (by rfl) ⟨135840, by rfl⟩ : syracuseStep 1448965 = 271681) (by norm_num)
theorem B1809413 : Blo 1204419 1809413 := bbase (se 4 (by rfl) ⟨169632, by rfl⟩ : syracuseStep 1809413 = 339265) (by norm_num)
theorem B1809437 : Blo 1204419 1809437 := bbase (se 3 (by rfl) ⟨339269, by rfl⟩ : syracuseStep 1809437 = 678539) (by norm_num)
theorem B2710565 : Blo 1204419 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B6102053 : Blo 1204419 6102053 := bbase (se 4 (by rfl) ⟨572067, by rfl⟩ : syracuseStep 6102053 = 1144135) (by norm_num)
theorem B5495861 : Blo 1204419 5495861 := bbase (se 5 (by rfl) ⟨257618, by rfl⟩ : syracuseStep 5495861 = 515237) (by norm_num)
theorem B1809461 : Blo 1204419 1809461 := bbase (se 5 (by rfl) ⟨84818, by rfl⟩ : syracuseStep 1809461 = 169637) (by norm_num)
theorem B1809485 : Blo 1204419 1809485 := bbase (se 3 (by rfl) ⟨339278, by rfl⟩ : syracuseStep 1809485 = 678557) (by norm_num)
theorem B10304597 : Blo 1204419 10304597 := bbase (se 8 (by rfl) ⟨60378, by rfl⟩ : syracuseStep 10304597 = 120757) (by norm_num)
theorem B1809509 : Blo 1204419 1809509 := bbase (se 4 (by rfl) ⟨169641, by rfl⟩ : syracuseStep 1809509 = 339283) (by norm_num)
theorem B2710637 : Blo 1204419 2710637 := bbase (se 3 (by rfl) ⟨508244, by rfl⟩ : syracuseStep 2710637 = 1016489) (by norm_num)
theorem B1809533 : Blo 1204419 1809533 := bbase (se 3 (by rfl) ⟨339287, by rfl⟩ : syracuseStep 1809533 = 678575) (by norm_num)
theorem B1809557 : Blo 1204419 1809557 := bbase (se 6 (by rfl) ⟨42411, by rfl⟩ : syracuseStep 1809557 = 84823) (by norm_num)
theorem B1809581 : Blo 1204419 1809581 := bbase (se 3 (by rfl) ⟨339296, by rfl⟩ : syracuseStep 1809581 = 678593) (by norm_num)
theorem B2710709 : Blo 1204419 2710709 := bbase (se 5 (by rfl) ⟨127064, by rfl⟩ : syracuseStep 2710709 = 254129) (by norm_num)
theorem B1809605 : Blo 1204419 1809605 := bbase (se 4 (by rfl) ⟨169650, by rfl⟩ : syracuseStep 1809605 = 339301) (by norm_num)
theorem B1809629 : Blo 1204419 1809629 := bbase (se 3 (by rfl) ⟨339305, by rfl⟩ : syracuseStep 1809629 = 678611) (by norm_num)
theorem B2710781 : Blo 1204419 2710781 := bbase (se 3 (by rfl) ⟨508271, by rfl⟩ : syracuseStep 2710781 = 1016543) (by norm_num)
theorem B2710853 : Blo 1204419 2710853 := bbase (se 4 (by rfl) ⟨254142, by rfl⟩ : syracuseStep 2710853 = 508285) (by norm_num)
theorem B4070789 : Blo 1204419 4070789 := bbase (se 4 (by rfl) ⟨381636, by rfl⟩ : syracuseStep 4070789 = 763273) (by norm_num)
theorem B2710925 : Blo 1204419 2710925 := bbase (se 3 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 2710925 = 1016597) (by norm_num)
theorem B1375645 : Blo 1204419 1375645 := bbase (se 3 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 1375645 = 515867) (by norm_num)
theorem B2710997 : Blo 1204419 2710997 := bbase (se 7 (by rfl) ⟨31769, by rfl⟩ : syracuseStep 2710997 = 63539) (by norm_num)
theorem B2711069 : Blo 1204419 2711069 := bbase (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) (by norm_num)
theorem B5496373 : Blo 1204419 5496373 := bbase (se 5 (by rfl) ⟨257642, by rfl⟩ : syracuseStep 5496373 = 515285) (by norm_num)
theorem B2711141 : Blo 1204419 2711141 := bbase (se 4 (by rfl) ⟨254169, by rfl⟩ : syracuseStep 2711141 = 508339) (by norm_num)
theorem B13721237 : Blo 1204419 13721237 := bbase (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) (by norm_num)
theorem B2711213 : Blo 1204419 2711213 := bbase (se 3 (by rfl) ⟨508352, by rfl⟩ : syracuseStep 2711213 = 1016705) (by norm_num)
theorem B2711285 : Blo 1204419 2711285 := bbase (se 5 (by rfl) ⟨127091, by rfl⟩ : syracuseStep 2711285 = 254183) (by norm_num)
theorem B6610709 : Blo 1204419 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B4071221 : Blo 1204419 4071221 := bbase (se 5 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 4071221 = 381677) (by norm_num)
theorem B2711357 : Blo 1204419 2711357 := bbase (se 3 (by rfl) ⟨508379, by rfl⟩ : syracuseStep 2711357 = 1016759) (by norm_num)
theorem B46333781 : Blo 1204419 46333781 := bbase (se 9 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 46333781 = 271487) (by norm_num)
theorem B2711429 : Blo 1204419 2711429 := bbase (se 4 (by rfl) ⟨254196, by rfl⟩ : syracuseStep 2711429 = 508393) (by norm_num)
theorem B5152693 : Blo 1204419 5152693 := bbase (se 5 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 5152693 = 483065) (by norm_num)
theorem B5152709 : Blo 1204419 5152709 := bbase (se 4 (by rfl) ⟨483066, by rfl⟩ : syracuseStep 5152709 = 966133) (by norm_num)
theorem B2711501 : Blo 1204419 2711501 := bbase (se 3 (by rfl) ⟨508406, by rfl⟩ : syracuseStep 2711501 = 1016813) (by norm_num)
theorem B37085141 : Blo 1204419 37085141 := bbase (se 7 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 37085141 = 869183) (by norm_num)
theorem B2711555 : Blo 1204419 2711555 := bstep (se 1 (by rfl) ⟨2033666, by rfl⟩ : syracuseStep 2711555 = 4067333) B4067333
theorem B3432451 : Blo 1204419 3432451 := bstep (se 1 (by rfl) ⟨2574338, by rfl⟩ : syracuseStep 3432451 = 5148677) B5148677
theorem B9158669 : Blo 1204419 9158669 := bstep (se 3 (by rfl) ⟨1717250, by rfl⟩ : syracuseStep 9158669 = 3434501) B3434501
theorem B4071437 : Blo 1204419 4071437 := bstep (se 3 (by rfl) ⟨763394, by rfl⟩ : syracuseStep 4071437 = 1526789) B1526789
theorem B4071491 : Blo 1204419 4071491 := bstep (se 1 (by rfl) ⟨3053618, by rfl⟩ : syracuseStep 4071491 = 6107237) B6107237
theorem B14655629 : Blo 1204419 14655629 := bstep (se 3 (by rfl) ⟨2747930, by rfl⟩ : syracuseStep 14655629 = 5495861) B5495861
theorem B3432611 : Blo 1204419 3432611 := bstep (se 1 (by rfl) ⟨2574458, by rfl⟩ : syracuseStep 3432611 = 5148917) B5148917
theorem B1204419 : Blo 1204419 1204419 := bstep (se 1 (by rfl) ⟨903314, by rfl⟩ : syracuseStep 1204419 = 1806629) B1806629
theorem B1204435 : Blo 1204419 1204435 := bstep (se 1 (by rfl) ⟨903326, by rfl⟩ : syracuseStep 1204435 = 1806653) B1806653
theorem B1204451 : Blo 1204419 1204451 := bstep (se 1 (by rfl) ⟨903338, by rfl⟩ : syracuseStep 1204451 = 1806677) B1806677
theorem B1204467 : Blo 1204419 1204467 := bstep (se 1 (by rfl) ⟨903350, by rfl⟩ : syracuseStep 1204467 = 1806701) B1806701
theorem B1204483 : Blo 1204419 1204483 := bstep (se 1 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 1204483 = 1806725) B1806725
theorem B2711825 : Blo 1204419 2711825 := bstep (se 2 (by rfl) ⟨1016934, by rfl⟩ : syracuseStep 2711825 = 2033869) B2033869
theorem B1204499 : Blo 1204419 1204499 := bstep (se 1 (by rfl) ⟨903374, by rfl⟩ : syracuseStep 1204499 = 1806749) B1806749
theorem B1204515 : Blo 1204419 1204515 := bstep (se 1 (by rfl) ⟨903386, by rfl⟩ : syracuseStep 1204515 = 1806773) B1806773
theorem B2711843 : Blo 1204419 2711843 := bstep (se 1 (by rfl) ⟨2033882, by rfl⟩ : syracuseStep 2711843 = 4067765) B4067765
theorem B1204531 : Blo 1204419 1204531 := bstep (se 1 (by rfl) ⟨903398, by rfl⟩ : syracuseStep 1204531 = 1806797) B1806797
theorem B1204547 : Blo 1204419 1204547 := bstep (se 1 (by rfl) ⟨903410, by rfl⟩ : syracuseStep 1204547 = 1806821) B1806821
theorem B1204563 : Blo 1204419 1204563 := bstep (se 1 (by rfl) ⟨903422, by rfl⟩ : syracuseStep 1204563 = 1806845) B1806845
theorem B1204579 : Blo 1204419 1204579 := bstep (se 1 (by rfl) ⟨903434, by rfl⟩ : syracuseStep 1204579 = 1806869) B1806869
theorem B1204595 : Blo 1204419 1204595 := bstep (se 1 (by rfl) ⟨903446, by rfl⟩ : syracuseStep 1204595 = 1806893) B1806893
theorem B1204611 : Blo 1204419 1204611 := bstep (se 1 (by rfl) ⟨903458, by rfl⟩ : syracuseStep 1204611 = 1806917) B1806917
theorem B1204627 : Blo 1204419 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B1204643 : Blo 1204419 1204643 := bstep (se 1 (by rfl) ⟨903482, by rfl⟩ : syracuseStep 1204643 = 1806965) B1806965
theorem B1204659 : Blo 1204419 1204659 := bstep (se 1 (by rfl) ⟨903494, by rfl⟩ : syracuseStep 1204659 = 1806989) B1806989
theorem B1204675 : Blo 1204419 1204675 := bstep (se 1 (by rfl) ⟨903506, by rfl⟩ : syracuseStep 1204675 = 1807013) B1807013
theorem B6865357 : Blo 1204419 6865357 := bstep (se 3 (by rfl) ⟨1287254, by rfl⟩ : syracuseStep 6865357 = 2574509) B2574509
theorem B1204691 : Blo 1204419 1204691 := bstep (se 1 (by rfl) ⟨903518, by rfl⟩ : syracuseStep 1204691 = 1807037) B1807037
theorem B1204707 : Blo 1204419 1204707 := bstep (se 1 (by rfl) ⟨903530, by rfl⟩ : syracuseStep 1204707 = 1807061) B1807061
theorem B1204723 : Blo 1204419 1204723 := bstep (se 1 (by rfl) ⟨903542, by rfl⟩ : syracuseStep 1204723 = 1807085) B1807085
theorem B1204739 : Blo 1204419 1204739 := bstep (se 1 (by rfl) ⟨903554, by rfl⟩ : syracuseStep 1204739 = 1807109) B1807109
theorem B1204755 : Blo 1204419 1204755 := bstep (se 1 (by rfl) ⟨903566, by rfl⟩ : syracuseStep 1204755 = 1807133) B1807133
theorem B1204771 : Blo 1204419 1204771 := bstep (se 1 (by rfl) ⟨903578, by rfl⟩ : syracuseStep 1204771 = 1807157) B1807157
theorem B2712113 : Blo 1204419 2712113 := bstep (se 2 (by rfl) ⟨1017042, by rfl⟩ : syracuseStep 2712113 = 2034085) B2034085
theorem B1204787 : Blo 1204419 1204787 := bstep (se 1 (by rfl) ⟨903590, by rfl⟩ : syracuseStep 1204787 = 1807181) B1807181
theorem B1204803 : Blo 1204419 1204803 := bstep (se 1 (by rfl) ⟨903602, by rfl⟩ : syracuseStep 1204803 = 1807205) B1807205
theorem B2712131 : Blo 1204419 2712131 := bstep (se 1 (by rfl) ⟨2034098, by rfl⟩ : syracuseStep 2712131 = 4068197) B4068197
theorem B1204819 : Blo 1204419 1204819 := bstep (se 1 (by rfl) ⟨903614, by rfl⟩ : syracuseStep 1204819 = 1807229) B1807229
theorem B1204835 : Blo 1204419 1204835 := bstep (se 1 (by rfl) ⟨903626, by rfl⟩ : syracuseStep 1204835 = 1807253) B1807253
theorem B1204851 : Blo 1204419 1204851 := bstep (se 1 (by rfl) ⟨903638, by rfl⟩ : syracuseStep 1204851 = 1807277) B1807277
theorem B1204867 : Blo 1204419 1204867 := bstep (se 1 (by rfl) ⟨903650, by rfl⟩ : syracuseStep 1204867 = 1807301) B1807301
theorem B1204883 : Blo 1204419 1204883 := bstep (se 1 (by rfl) ⟨903662, by rfl⟩ : syracuseStep 1204883 = 1807325) B1807325
theorem B1204899 : Blo 1204419 1204899 := bstep (se 1 (by rfl) ⟨903674, by rfl⟩ : syracuseStep 1204899 = 1807349) B1807349
theorem B4580003 : Blo 1204419 4580003 := bstep (se 1 (by rfl) ⟨3435002, by rfl⟩ : syracuseStep 4580003 = 6870005) B6870005
theorem B2933425 : Blo 1204419 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B1204915 : Blo 1204419 1204915 := bstep (se 1 (by rfl) ⟨903686, by rfl⟩ : syracuseStep 1204915 = 1807373) B1807373
theorem B1204931 : Blo 1204419 1204931 := bstep (se 1 (by rfl) ⟨903698, by rfl⟩ : syracuseStep 1204931 = 1807397) B1807397
theorem B1204947 : Blo 1204419 1204947 := bstep (se 1 (by rfl) ⟨903710, by rfl⟩ : syracuseStep 1204947 = 1807421) B1807421
theorem B1909459 : Blo 1204419 1909459 := bstep (se 1 (by rfl) ⟨1432094, by rfl⟩ : syracuseStep 1909459 = 2864189) B2864189
theorem B1204963 : Blo 1204419 1204963 := bstep (se 1 (by rfl) ⟨903722, by rfl⟩ : syracuseStep 1204963 = 1807445) B1807445
theorem B1204979 : Blo 1204419 1204979 := bstep (se 1 (by rfl) ⟨903734, by rfl⟩ : syracuseStep 1204979 = 1807469) B1807469
theorem B1204995 : Blo 1204419 1204995 := bstep (se 1 (by rfl) ⟨903746, by rfl⟩ : syracuseStep 1204995 = 1807493) B1807493
theorem B1205011 : Blo 1204419 1205011 := bstep (se 1 (by rfl) ⟨903758, by rfl⟩ : syracuseStep 1205011 = 1807517) B1807517
theorem B1205027 : Blo 1204419 1205027 := bstep (se 1 (by rfl) ⟨903770, by rfl⟩ : syracuseStep 1205027 = 1807541) B1807541
theorem B1286947 : Blo 1204419 1286947 := bstep (se 1 (by rfl) ⟨965210, by rfl⟩ : syracuseStep 1286947 = 1930421) B1930421
theorem B1205043 : Blo 1204419 1205043 := bstep (se 1 (by rfl) ⟨903782, by rfl⟩ : syracuseStep 1205043 = 1807565) B1807565
theorem B15434549 : Blo 1204419 15434549 := bstep (se 5 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 15434549 = 1446989) B1446989
theorem B1205059 : Blo 1204419 1205059 := bstep (se 1 (by rfl) ⟨903794, by rfl⟩ : syracuseStep 1205059 = 1807589) B1807589
theorem B2032465 : Blo 1204419 2032465 := bstep (se 2 (by rfl) ⟨762174, by rfl⟩ : syracuseStep 2032465 = 1524349) B1524349
theorem B2712401 : Blo 1204419 2712401 := bstep (se 2 (by rfl) ⟨1017150, by rfl⟩ : syracuseStep 2712401 = 2034301) B2034301
theorem B1205075 : Blo 1204419 1205075 := bstep (se 1 (by rfl) ⟨903806, by rfl⟩ : syracuseStep 1205075 = 1807613) B1807613
theorem B1205091 : Blo 1204419 1205091 := bstep (se 1 (by rfl) ⟨903818, by rfl⟩ : syracuseStep 1205091 = 1807637) B1807637
theorem B2712419 : Blo 1204419 2712419 := bstep (se 1 (by rfl) ⟨2034314, by rfl⟩ : syracuseStep 2712419 = 4068629) B4068629
theorem B2032499 : Blo 1204419 2032499 := bstep (se 1 (by rfl) ⟨1524374, by rfl⟩ : syracuseStep 2032499 = 3048749) B3048749
theorem B1205107 : Blo 1204419 1205107 := bstep (se 1 (by rfl) ⟨903830, by rfl⟩ : syracuseStep 1205107 = 1807661) B1807661
theorem B1205123 : Blo 1204419 1205123 := bstep (se 1 (by rfl) ⟨903842, by rfl⟩ : syracuseStep 1205123 = 1807685) B1807685
theorem B1205139 : Blo 1204419 1205139 := bstep (se 1 (by rfl) ⟨903854, by rfl⟩ : syracuseStep 1205139 = 1807709) B1807709
theorem B1205155 : Blo 1204419 1205155 := bstep (se 1 (by rfl) ⟨903866, by rfl⟩ : syracuseStep 1205155 = 1807733) B1807733
theorem B1205171 : Blo 1204419 1205171 := bstep (se 1 (by rfl) ⟨903878, by rfl⟩ : syracuseStep 1205171 = 1807757) B1807757
theorem B1205187 : Blo 1204419 1205187 := bstep (se 1 (by rfl) ⟨903890, by rfl⟩ : syracuseStep 1205187 = 1807781) B1807781
theorem B1205203 : Blo 1204419 1205203 := bstep (se 1 (by rfl) ⟨903902, by rfl⟩ : syracuseStep 1205203 = 1807805) B1807805
theorem B1205219 : Blo 1204419 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B2032627 : Blo 1204419 2032627 := bstep (se 1 (by rfl) ⟨1524470, by rfl⟩ : syracuseStep 2032627 = 3048941) B3048941
theorem B1205235 : Blo 1204419 1205235 := bstep (se 1 (by rfl) ⟨903926, by rfl⟩ : syracuseStep 1205235 = 1807853) B1807853
theorem B1524739 : Blo 1204419 1524739 := bstep (se 1 (by rfl) ⟨1143554, by rfl⟩ : syracuseStep 1524739 = 2287109) B2287109
theorem B1205251 : Blo 1204419 1205251 := bstep (se 1 (by rfl) ⟨903938, by rfl⟩ : syracuseStep 1205251 = 1807877) B1807877
theorem B1205267 : Blo 1204419 1205267 := bstep (se 1 (by rfl) ⟨903950, by rfl⟩ : syracuseStep 1205267 = 1807901) B1807901
theorem B1205283 : Blo 1204419 1205283 := bstep (se 1 (by rfl) ⟨903962, by rfl⟩ : syracuseStep 1205283 = 1807925) B1807925
theorem B1205299 : Blo 1204419 1205299 := bstep (se 1 (by rfl) ⟨903974, by rfl⟩ : syracuseStep 1205299 = 1807949) B1807949
theorem B1205315 : Blo 1204419 1205315 := bstep (se 1 (by rfl) ⟨903986, by rfl⟩ : syracuseStep 1205315 = 1807973) B1807973
theorem B1205331 : Blo 1204419 1205331 := bstep (se 1 (by rfl) ⟨903998, by rfl⟩ : syracuseStep 1205331 = 1807997) B1807997
theorem B1524835 : Blo 1204419 1524835 := bstep (se 1 (by rfl) ⟨1143626, by rfl⟩ : syracuseStep 1524835 = 2287253) B2287253
theorem B1205347 : Blo 1204419 1205347 := bstep (se 1 (by rfl) ⟨904010, by rfl⟩ : syracuseStep 1205347 = 1808021) B1808021
theorem B2712689 : Blo 1204419 2712689 := bstep (se 2 (by rfl) ⟨1017258, by rfl⟩ : syracuseStep 2712689 = 2034517) B2034517
theorem B1205363 : Blo 1204419 1205363 := bstep (se 1 (by rfl) ⟨904022, by rfl⟩ : syracuseStep 1205363 = 1808045) B1808045
theorem B2032769 : Blo 1204419 2032769 := bstep (se 2 (by rfl) ⟨762288, by rfl⟩ : syracuseStep 2032769 = 1524577) B1524577
theorem B1205379 : Blo 1204419 1205379 := bstep (se 1 (by rfl) ⟨904034, by rfl⟩ : syracuseStep 1205379 = 1808069) B1808069
theorem B2712707 : Blo 1204419 2712707 := bstep (se 1 (by rfl) ⟨2034530, by rfl⟩ : syracuseStep 2712707 = 4069061) B4069061
theorem B1205395 : Blo 1204419 1205395 := bstep (se 1 (by rfl) ⟨904046, by rfl⟩ : syracuseStep 1205395 = 1808093) B1808093
theorem B1205411 : Blo 1204419 1205411 := bstep (se 1 (by rfl) ⟨904058, by rfl⟩ : syracuseStep 1205411 = 1808117) B1808117
theorem B1205427 : Blo 1204419 1205427 := bstep (se 1 (by rfl) ⟨904070, by rfl⟩ : syracuseStep 1205427 = 1808141) B1808141
theorem B1205443 : Blo 1204419 1205443 := bstep (se 1 (by rfl) ⟨904082, by rfl⟩ : syracuseStep 1205443 = 1808165) B1808165
theorem B3433681 : Blo 1204419 3433681 := bstep (se 2 (by rfl) ⟨1287630, by rfl⟩ : syracuseStep 3433681 = 2575261) B2575261
theorem B1205459 : Blo 1204419 1205459 := bstep (se 1 (by rfl) ⟨904094, by rfl⟩ : syracuseStep 1205459 = 1808189) B1808189
theorem B1205475 : Blo 1204419 1205475 := bstep (se 1 (by rfl) ⟨904106, by rfl⟩ : syracuseStep 1205475 = 1808213) B1808213
theorem B1205491 : Blo 1204419 1205491 := bstep (se 1 (by rfl) ⟨904118, by rfl⟩ : syracuseStep 1205491 = 1808237) B1808237
theorem B2032897 : Blo 1204419 2032897 := bstep (se 2 (by rfl) ⟨762336, by rfl⟩ : syracuseStep 2032897 = 1524673) B1524673
theorem B1205507 : Blo 1204419 1205507 := bstep (se 1 (by rfl) ⟨904130, by rfl⟩ : syracuseStep 1205507 = 1808261) B1808261
theorem B1205523 : Blo 1204419 1205523 := bstep (se 1 (by rfl) ⟨904142, by rfl⟩ : syracuseStep 1205523 = 1808285) B1808285
theorem B2032931 : Blo 1204419 2032931 := bstep (se 1 (by rfl) ⟨1524698, by rfl⟩ : syracuseStep 2032931 = 3049397) B3049397
theorem B1205539 : Blo 1204419 1205539 := bstep (se 1 (by rfl) ⟨904154, by rfl⟩ : syracuseStep 1205539 = 1808309) B1808309
theorem B1205555 : Blo 1204419 1205555 := bstep (se 1 (by rfl) ⟨904166, by rfl⟩ : syracuseStep 1205555 = 1808333) B1808333
theorem B1205571 : Blo 1204419 1205571 := bstep (se 1 (by rfl) ⟨904178, by rfl⟩ : syracuseStep 1205571 = 1808357) B1808357
theorem B1205587 : Blo 1204419 1205587 := bstep (se 1 (by rfl) ⟨904190, by rfl⟩ : syracuseStep 1205587 = 1808381) B1808381
theorem B1205603 : Blo 1204419 1205603 := bstep (se 1 (by rfl) ⟨904202, by rfl⟩ : syracuseStep 1205603 = 1808405) B1808405
theorem B1205619 : Blo 1204419 1205619 := bstep (se 1 (by rfl) ⟨904214, by rfl⟩ : syracuseStep 1205619 = 1808429) B1808429
theorem B1205635 : Blo 1204419 1205635 := bstep (se 1 (by rfl) ⟨904226, by rfl⟩ : syracuseStep 1205635 = 1808453) B1808453
theorem B2712977 : Blo 1204419 2712977 := bstep (se 2 (by rfl) ⟨1017366, by rfl⟩ : syracuseStep 2712977 = 2034733) B2034733
theorem B1205651 : Blo 1204419 1205651 := bstep (se 1 (by rfl) ⟨904238, by rfl⟩ : syracuseStep 1205651 = 1808477) B1808477
theorem B1287571 : Blo 1204419 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B2033059 : Blo 1204419 2033059 := bstep (se 1 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 2033059 = 3049589) B3049589
theorem B1205667 : Blo 1204419 1205667 := bstep (se 1 (by rfl) ⟨904250, by rfl⟩ : syracuseStep 1205667 = 1808501) B1808501
theorem B2712995 : Blo 1204419 2712995 := bstep (se 1 (by rfl) ⟨2034746, by rfl⟩ : syracuseStep 2712995 = 4069493) B4069493
theorem B6104483 : Blo 1204419 6104483 := bstep (se 1 (by rfl) ⟨4578362, by rfl⟩ : syracuseStep 6104483 = 9156725) B9156725
theorem B2287025 : Blo 1204419 2287025 := bstep (se 2 (by rfl) ⟨857634, by rfl⟩ : syracuseStep 2287025 = 1715269) B1715269
theorem B1205683 : Blo 1204419 1205683 := bstep (se 1 (by rfl) ⟨904262, by rfl⟩ : syracuseStep 1205683 = 1808525) B1808525
theorem B1205699 : Blo 1204419 1205699 := bstep (se 1 (by rfl) ⟨904274, by rfl⟩ : syracuseStep 1205699 = 1808549) B1808549
theorem B1205715 : Blo 1204419 1205715 := bstep (se 1 (by rfl) ⟨904286, by rfl⟩ : syracuseStep 1205715 = 1808573) B1808573
theorem B1205731 : Blo 1204419 1205731 := bstep (se 1 (by rfl) ⟨904298, by rfl⟩ : syracuseStep 1205731 = 1808597) B1808597
theorem B16508387 : Blo 1204419 16508387 := bstep (se 1 (by rfl) ⟨12381290, by rfl⟩ : syracuseStep 16508387 = 24762581) B24762581
theorem B1205747 : Blo 1204419 1205747 := bstep (se 1 (by rfl) ⟨904310, by rfl⟩ : syracuseStep 1205747 = 1808621) B1808621
theorem B1205763 : Blo 1204419 1205763 := bstep (se 1 (by rfl) ⟨904322, by rfl⟩ : syracuseStep 1205763 = 1808645) B1808645
theorem B1205779 : Blo 1204419 1205779 := bstep (se 1 (by rfl) ⟨904334, by rfl⟩ : syracuseStep 1205779 = 1808669) B1808669
theorem B1205795 : Blo 1204419 1205795 := bstep (se 1 (by rfl) ⟨904346, by rfl⟩ : syracuseStep 1205795 = 1808693) B1808693
theorem B2033201 : Blo 1204419 2033201 := bstep (se 2 (by rfl) ⟨762450, by rfl⟩ : syracuseStep 2033201 = 1524901) B1524901
theorem B1205811 : Blo 1204419 1205811 := bstep (se 1 (by rfl) ⟨904358, by rfl⟩ : syracuseStep 1205811 = 1808717) B1808717
theorem B1205827 : Blo 1204419 1205827 := bstep (se 1 (by rfl) ⟨904370, by rfl⟩ : syracuseStep 1205827 = 1808741) B1808741
theorem B1525331 : Blo 1204419 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B1205843 : Blo 1204419 1205843 := bstep (se 1 (by rfl) ⟨904382, by rfl⟩ : syracuseStep 1205843 = 1808765) B1808765
theorem B1205859 : Blo 1204419 1205859 := bstep (se 1 (by rfl) ⟨904394, by rfl⟩ : syracuseStep 1205859 = 1808789) B1808789
theorem B3049073 : Blo 1204419 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B6514289 : Blo 1204419 6514289 := bstep (se 2 (by rfl) ⟨2442858, by rfl⟩ : syracuseStep 6514289 = 4885717) B4885717
theorem B1205875 : Blo 1204419 1205875 := bstep (se 1 (by rfl) ⟨904406, by rfl⟩ : syracuseStep 1205875 = 1808813) B1808813
theorem B1205891 : Blo 1204419 1205891 := bstep (se 1 (by rfl) ⟨904418, by rfl⟩ : syracuseStep 1205891 = 1808837) B1808837
theorem B1205907 : Blo 1204419 1205907 := bstep (se 1 (by rfl) ⟨904430, by rfl⟩ : syracuseStep 1205907 = 1808861) B1808861
theorem B3049123 : Blo 1204419 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B1205923 : Blo 1204419 1205923 := bstep (se 1 (by rfl) ⟨904442, by rfl⟩ : syracuseStep 1205923 = 1808885) B1808885
theorem B1394339 : Blo 1204419 1394339 := bstep (se 1 (by rfl) ⟨1045754, by rfl⟩ : syracuseStep 1394339 = 2091509) B2091509
theorem B2033329 : Blo 1204419 2033329 := bstep (se 2 (by rfl) ⟨762498, by rfl⟩ : syracuseStep 2033329 = 1524997) B1524997
theorem B2713265 : Blo 1204419 2713265 := bstep (se 2 (by rfl) ⟨1017474, by rfl⟩ : syracuseStep 2713265 = 2034949) B2034949
theorem B1205939 : Blo 1204419 1205939 := bstep (se 1 (by rfl) ⟨904454, by rfl⟩ : syracuseStep 1205939 = 1808909) B1808909
theorem B2713283 : Blo 1204419 2713283 := bstep (se 1 (by rfl) ⟨2034962, by rfl⟩ : syracuseStep 2713283 = 4069925) B4069925
theorem B1205955 : Blo 1204419 1205955 := bstep (se 1 (by rfl) ⟨904466, by rfl⟩ : syracuseStep 1205955 = 1808933) B1808933
theorem B2033363 : Blo 1204419 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B1205971 : Blo 1204419 1205971 := bstep (se 1 (by rfl) ⟨904478, by rfl⟩ : syracuseStep 1205971 = 1808957) B1808957
theorem B1205987 : Blo 1204419 1205987 := bstep (se 1 (by rfl) ⟨904490, by rfl⟩ : syracuseStep 1205987 = 1808981) B1808981
theorem B2574065 : Blo 1204419 2574065 := bstep (se 2 (by rfl) ⟨965274, by rfl⟩ : syracuseStep 2574065 = 1930549) B1930549
theorem B1206003 : Blo 1204419 1206003 := bstep (se 1 (by rfl) ⟨904502, by rfl⟩ : syracuseStep 1206003 = 1809005) B1809005
theorem B1206019 : Blo 1204419 1206019 := bstep (se 1 (by rfl) ⟨904514, by rfl⟩ : syracuseStep 1206019 = 1809029) B1809029
theorem B6956813 : Blo 1204419 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B1206035 : Blo 1204419 1206035 := bstep (se 1 (by rfl) ⟨904526, by rfl⟩ : syracuseStep 1206035 = 1809053) B1809053
theorem B1206051 : Blo 1204419 1206051 := bstep (se 1 (by rfl) ⟨904538, by rfl⟩ : syracuseStep 1206051 = 1809077) B1809077
theorem B3049265 : Blo 1204419 3049265 := bstep (se 2 (by rfl) ⟨1143474, by rfl⟩ : syracuseStep 3049265 = 2286949) B2286949
theorem B1206067 : Blo 1204419 1206067 := bstep (se 1 (by rfl) ⟨904550, by rfl⟩ : syracuseStep 1206067 = 1809101) B1809101
theorem B1206083 : Blo 1204419 1206083 := bstep (se 1 (by rfl) ⟨904562, by rfl⟩ : syracuseStep 1206083 = 1809125) B1809125
theorem B2033491 : Blo 1204419 2033491 := bstep (se 1 (by rfl) ⟨1525118, by rfl⟩ : syracuseStep 2033491 = 3050237) B3050237
theorem B1206099 : Blo 1204419 1206099 := bstep (se 1 (by rfl) ⟨904574, by rfl⟩ : syracuseStep 1206099 = 1809149) B1809149
theorem B1206115 : Blo 1204419 1206115 := bstep (se 1 (by rfl) ⟨904586, by rfl⟩ : syracuseStep 1206115 = 1809173) B1809173
theorem B1206131 : Blo 1204419 1206131 := bstep (se 1 (by rfl) ⟨904598, by rfl⟩ : syracuseStep 1206131 = 1809197) B1809197
theorem B1206147 : Blo 1204419 1206147 := bstep (se 1 (by rfl) ⟨904610, by rfl⟩ : syracuseStep 1206147 = 1809221) B1809221
theorem B1206163 : Blo 1204419 1206163 := bstep (se 1 (by rfl) ⟨904622, by rfl⟩ : syracuseStep 1206163 = 1809245) B1809245
theorem B1206179 : Blo 1204419 1206179 := bstep (se 1 (by rfl) ⟨904634, by rfl⟩ : syracuseStep 1206179 = 1809269) B1809269
theorem B1206195 : Blo 1204419 1206195 := bstep (se 1 (by rfl) ⟨904646, by rfl⟩ : syracuseStep 1206195 = 1809293) B1809293
theorem B1206211 : Blo 1204419 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B2713553 : Blo 1204419 2713553 := bstep (se 2 (by rfl) ⟨1017582, by rfl⟩ : syracuseStep 2713553 = 2035165) B2035165
theorem B1206227 : Blo 1204419 1206227 := bstep (se 1 (by rfl) ⟨904670, by rfl⟩ : syracuseStep 1206227 = 1809341) B1809341
theorem B2033633 : Blo 1204419 2033633 := bstep (se 2 (by rfl) ⟨762612, by rfl⟩ : syracuseStep 2033633 = 1525225) B1525225
theorem B2713571 : Blo 1204419 2713571 := bstep (se 1 (by rfl) ⟨2035178, by rfl⟩ : syracuseStep 2713571 = 4070357) B4070357
theorem B1206243 : Blo 1204419 1206243 := bstep (se 1 (by rfl) ⟨904682, by rfl⟩ : syracuseStep 1206243 = 1809365) B1809365
theorem B4573169 : Blo 1204419 4573169 := bstep (se 2 (by rfl) ⟨1714938, by rfl⟩ : syracuseStep 4573169 = 3429877) B3429877
theorem B1206259 : Blo 1204419 1206259 := bstep (se 1 (by rfl) ⟨904694, by rfl⟩ : syracuseStep 1206259 = 1809389) B1809389
theorem B1206275 : Blo 1204419 1206275 := bstep (se 1 (by rfl) ⟨904706, by rfl⟩ : syracuseStep 1206275 = 1809413) B1809413
theorem B7333901 : Blo 1204419 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B1206291 : Blo 1204419 1206291 := bstep (se 1 (by rfl) ⟨904718, by rfl⟩ : syracuseStep 1206291 = 1809437) B1809437
theorem B1206307 : Blo 1204419 1206307 := bstep (se 1 (by rfl) ⟨904730, by rfl⟩ : syracuseStep 1206307 = 1809461) B1809461
theorem B1206323 : Blo 1204419 1206323 := bstep (se 1 (by rfl) ⟨904742, by rfl⟩ : syracuseStep 1206323 = 1809485) B1809485
theorem B1206339 : Blo 1204419 1206339 := bstep (se 1 (by rfl) ⟨904754, by rfl⟩ : syracuseStep 1206339 = 1809509) B1809509
theorem B3860561 : Blo 1204419 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B1206355 : Blo 1204419 1206355 := bstep (se 1 (by rfl) ⟨904766, by rfl⟩ : syracuseStep 1206355 = 1809533) B1809533
theorem B2033761 : Blo 1204419 2033761 := bstep (se 2 (by rfl) ⟨762660, by rfl⟩ : syracuseStep 2033761 = 1525321) B1525321
theorem B1206371 : Blo 1204419 1206371 := bstep (se 1 (by rfl) ⟨904778, by rfl⟩ : syracuseStep 1206371 = 1809557) B1809557
theorem B4065389 : Blo 1204419 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B1206387 : Blo 1204419 1206387 := bstep (se 1 (by rfl) ⟨904790, by rfl⟩ : syracuseStep 1206387 = 1809581) B1809581
theorem B2033795 : Blo 1204419 2033795 := bstep (se 1 (by rfl) ⟨1525346, by rfl⟩ : syracuseStep 2033795 = 3050693) B3050693
theorem B1206403 : Blo 1204419 1206403 := bstep (se 1 (by rfl) ⟨904802, by rfl⟩ : syracuseStep 1206403 = 1809605) B1809605
theorem B1206419 : Blo 1204419 1206419 := bstep (se 1 (by rfl) ⟨904814, by rfl⟩ : syracuseStep 1206419 = 1809629) B1809629
theorem B4065443 : Blo 1204419 4065443 := bstep (se 1 (by rfl) ⟨3049082, by rfl⟩ : syracuseStep 4065443 = 6098165) B6098165
theorem B6105293 : Blo 1204419 6105293 := bstep (se 3 (by rfl) ⟨1144742, by rfl⟩ : syracuseStep 6105293 = 2289485) B2289485
theorem B2230499 : Blo 1204419 2230499 := bstep (se 1 (by rfl) ⟨1672874, by rfl⟩ : syracuseStep 2230499 = 3345749) B3345749
theorem B2713841 : Blo 1204419 2713841 := bstep (se 2 (by rfl) ⟨1017690, by rfl⟩ : syracuseStep 2713841 = 2035381) B2035381
theorem B2033923 : Blo 1204419 2033923 := bstep (se 1 (by rfl) ⟨1525442, by rfl⟩ : syracuseStep 2033923 = 3050885) B3050885
theorem B2574595 : Blo 1204419 2574595 := bstep (se 1 (by rfl) ⟨1930946, by rfl⟩ : syracuseStep 2574595 = 3861893) B3861893
theorem B2713859 : Blo 1204419 2713859 := bstep (se 1 (by rfl) ⟨2035394, by rfl⟩ : syracuseStep 2713859 = 4070789) B4070789
theorem B1526035 : Blo 1204419 1526035 := bstep (se 1 (by rfl) ⟨1144526, by rfl⟩ : syracuseStep 1526035 = 2289053) B2289053
theorem B2287921 : Blo 1204419 2287921 := bstep (se 2 (by rfl) ⟨857970, by rfl⟩ : syracuseStep 2287921 = 1715941) B1715941
theorem B9152837 : Blo 1204419 9152837 := bstep (se 4 (by rfl) ⟨858078, by rfl⟩ : syracuseStep 9152837 = 1716157) B1716157
theorem B1526131 : Blo 1204419 1526131 := bstep (se 1 (by rfl) ⟨1144598, by rfl⟩ : syracuseStep 1526131 = 2289197) B2289197
theorem B6867341 : Blo 1204419 6867341 := bstep (se 3 (by rfl) ⟨1287626, by rfl⟩ : syracuseStep 6867341 = 2575253) B2575253
theorem B2034065 : Blo 1204419 2034065 := bstep (se 2 (by rfl) ⟨762774, by rfl⟩ : syracuseStep 2034065 = 1525549) B1525549
theorem B4065713 : Blo 1204419 4065713 := bstep (se 2 (by rfl) ⟨1524642, by rfl⟩ : syracuseStep 4065713 = 3049285) B3049285
theorem B2935217 : Blo 1204419 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B3434957 : Blo 1204419 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B2288081 : Blo 1204419 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B2034193 : Blo 1204419 2034193 := bstep (se 2 (by rfl) ⟨762822, by rfl⟩ : syracuseStep 2034193 = 1525645) B1525645
theorem B2714129 : Blo 1204419 2714129 := bstep (se 2 (by rfl) ⟨1017798, by rfl⟩ : syracuseStep 2714129 = 2035597) B2035597
theorem B2714147 : Blo 1204419 2714147 := bstep (se 1 (by rfl) ⟨2035610, by rfl⟩ : syracuseStep 2714147 = 4071221) B4071221
theorem B2034227 : Blo 1204419 2034227 := bstep (se 1 (by rfl) ⟨1525670, by rfl⟩ : syracuseStep 2034227 = 3051341) B3051341
theorem B7825997 : Blo 1204419 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B9767537 : Blo 1204419 9767537 := bstep (se 2 (by rfl) ⟨3662826, by rfl⟩ : syracuseStep 9767537 = 7325653) B7325653
theorem B3435139 : Blo 1204419 3435139 := bstep (se 1 (by rfl) ⟨2576354, by rfl⟩ : syracuseStep 3435139 = 5152709) B5152709
theorem B3435185 : Blo 1204419 3435185 := bstep (se 2 (by rfl) ⟨1288194, by rfl⟩ : syracuseStep 3435185 = 2576389) B2576389
theorem B2034355 : Blo 1204419 2034355 := bstep (se 1 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 2034355 = 3051533) B3051533
theorem B3050257 : Blo 1204419 3050257 := bstep (se 2 (by rfl) ⟨1143846, by rfl⟩ : syracuseStep 3050257 = 2287693) B2287693
theorem B2714417 : Blo 1204419 2714417 := bstep (se 2 (by rfl) ⟨1017906, by rfl⟩ : syracuseStep 2714417 = 2035813) B2035813
theorem B2034497 : Blo 1204419 2034497 := bstep (se 2 (by rfl) ⟨762936, by rfl⟩ : syracuseStep 2034497 = 1525873) B1525873
theorem B2714435 : Blo 1204419 2714435 := bstep (se 1 (by rfl) ⟨2035826, by rfl⟩ : syracuseStep 2714435 = 4071653) B4071653
theorem B1715041 : Blo 1204419 1715041 := bstep (se 2 (by rfl) ⟨643140, by rfl⟩ : syracuseStep 1715041 = 1286281) B1286281
theorem B2288483 : Blo 1204419 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B1526627 : Blo 1204419 1526627 := bstep (se 1 (by rfl) ⟨1144970, by rfl⟩ : syracuseStep 1526627 = 2289941) B2289941
theorem B1739665 : Blo 1204419 1739665 := bstep (se 2 (by rfl) ⟨652374, by rfl⟩ : syracuseStep 1739665 = 1304749) B1304749
theorem B6097841 : Blo 1204419 6097841 := bstep (se 2 (by rfl) ⟨2286690, by rfl⟩ : syracuseStep 6097841 = 4573381) B4573381
theorem B2173873 : Blo 1204419 2173873 := bstep (se 2 (by rfl) ⟨815202, by rfl⟩ : syracuseStep 2173873 = 1630405) B1630405
theorem B2034625 : Blo 1204419 2034625 := bstep (se 2 (by rfl) ⟨762984, by rfl⟩ : syracuseStep 2034625 = 1525969) B1525969
theorem B4066253 : Blo 1204419 4066253 := bstep (se 3 (by rfl) ⟨762422, by rfl⟩ : syracuseStep 4066253 = 1524845) B1524845
theorem B2034659 : Blo 1204419 2034659 := bstep (se 1 (by rfl) ⟨1525994, by rfl⟩ : syracuseStep 2034659 = 3051989) B3051989
theorem B4066307 : Blo 1204419 4066307 := bstep (se 1 (by rfl) ⟨3049730, by rfl⟩ : syracuseStep 4066307 = 6099461) B6099461
theorem B3050531 : Blo 1204419 3050531 := bstep (se 1 (by rfl) ⟨2287898, by rfl⟩ : syracuseStep 3050531 = 4575797) B4575797
theorem B1739827 : Blo 1204419 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B2034787 : Blo 1204419 2034787 := bstep (se 1 (by rfl) ⟨1526090, by rfl⟩ : syracuseStep 2034787 = 3052181) B3052181
theorem B3714221 : Blo 1204419 3714221 := bstep (se 3 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 3714221 = 1392833) B1392833
theorem B3050723 : Blo 1204419 3050723 := bstep (se 1 (by rfl) ⟨2288042, by rfl⟩ : syracuseStep 3050723 = 4576085) B4576085
theorem B13389041 : Blo 1204419 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B2034929 : Blo 1204419 2034929 := bstep (se 2 (by rfl) ⟨763098, by rfl⟩ : syracuseStep 2034929 = 1526197) B1526197
theorem B4066577 : Blo 1204419 4066577 := bstep (se 2 (by rfl) ⟨1524966, by rfl⟩ : syracuseStep 4066577 = 3049933) B3049933
theorem B6868273 : Blo 1204419 6868273 := bstep (se 2 (by rfl) ⟨2575602, by rfl⟩ : syracuseStep 6868273 = 5151205) B5151205
theorem B1355107 : Blo 1204419 1355107 := bstep (se 1 (by rfl) ⟨1016330, by rfl⟩ : syracuseStep 1355107 = 2032661) B2032661
theorem B13036913 : Blo 1204419 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B2035057 : Blo 1204419 2035057 := bstep (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) B1526293
theorem B5795185 : Blo 1204419 5795185 := bstep (se 2 (by rfl) ⟨2173194, by rfl⟩ : syracuseStep 5795185 = 4346389) B4346389
theorem B2035091 : Blo 1204419 2035091 := bstep (se 1 (by rfl) ⟨1526318, by rfl⟩ : syracuseStep 2035091 = 3052637) B3052637
theorem B4574627 : Blo 1204419 4574627 := bstep (se 1 (by rfl) ⟨3430970, by rfl⟩ : syracuseStep 4574627 = 6861941) B6861941
theorem B1355251 : Blo 1204419 1355251 := bstep (se 1 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 1355251 = 2032877) B2032877
theorem B1764865 : Blo 1204419 1764865 := bstep (se 2 (by rfl) ⟨661824, by rfl⟩ : syracuseStep 1764865 = 1323649) B1323649
theorem B2035219 : Blo 1204419 2035219 := bstep (se 1 (by rfl) ⟨1526414, by rfl⟩ : syracuseStep 2035219 = 3052829) B3052829
theorem B1715747 : Blo 1204419 1715747 := bstep (se 1 (by rfl) ⟨1286810, by rfl⟩ : syracuseStep 1715747 = 2573621) B2573621
theorem B7327331 : Blo 1204419 7327331 := bstep (se 1 (by rfl) ⟨5495498, by rfl⟩ : syracuseStep 7327331 = 10990997) B10990997
theorem B1355395 : Blo 1204419 1355395 := bstep (se 1 (by rfl) ⟨1016546, by rfl⟩ : syracuseStep 1355395 = 2033093) B2033093
theorem B2035361 : Blo 1204419 2035361 := bstep (se 2 (by rfl) ⟨763260, by rfl⟩ : syracuseStep 2035361 = 1526521) B1526521
theorem B2576081 : Blo 1204419 2576081 := bstep (se 2 (by rfl) ⟨966030, by rfl⟩ : syracuseStep 2576081 = 1932061) B1932061
theorem B1650403 : Blo 1204419 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B2289379 : Blo 1204419 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B2576099 : Blo 1204419 2576099 := bstep (se 1 (by rfl) ⟨1932074, by rfl⟩ : syracuseStep 2576099 = 3864149) B3864149
theorem B10432241 : Blo 1204419 10432241 := bstep (se 2 (by rfl) ⟨3912090, by rfl⟩ : syracuseStep 10432241 = 7824181) B7824181
theorem B1355539 : Blo 1204419 1355539 := bstep (se 1 (by rfl) ⟨1016654, by rfl⟩ : syracuseStep 1355539 = 2033309) B2033309
theorem B2035489 : Blo 1204419 2035489 := bstep (se 2 (by rfl) ⟨763308, by rfl⟩ : syracuseStep 2035489 = 1526617) B1526617
theorem B4067117 : Blo 1204419 4067117 := bstep (se 3 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 4067117 = 1525169) B1525169
theorem B2035523 : Blo 1204419 2035523 := bstep (se 1 (by rfl) ⟨1526642, by rfl⟩ : syracuseStep 2035523 = 3053285) B3053285
theorem B4067171 : Blo 1204419 4067171 := bstep (se 1 (by rfl) ⟨3050378, by rfl⟩ : syracuseStep 4067171 = 6100757) B6100757
theorem B2445169 : Blo 1204419 2445169 := bstep (se 2 (by rfl) ⟨916938, by rfl⟩ : syracuseStep 2445169 = 1833877) B1833877
theorem B2289539 : Blo 1204419 2289539 := bstep (se 1 (by rfl) ⟨1717154, by rfl⟩ : syracuseStep 2289539 = 3434309) B3434309
theorem B1355683 : Blo 1204419 1355683 := bstep (se 1 (by rfl) ⟨1016762, by rfl⟩ : syracuseStep 1355683 = 2033525) B2033525
theorem B5148593 : Blo 1204419 5148593 := bstep (se 2 (by rfl) ⟨1930722, by rfl⟩ : syracuseStep 5148593 = 3861445) B3861445
theorem B2035651 : Blo 1204419 2035651 := bstep (se 1 (by rfl) ⟨1526738, by rfl⟩ : syracuseStep 2035651 = 3053477) B3053477
theorem B17379269 : Blo 1204419 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B5148643 : Blo 1204419 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B1355827 : Blo 1204419 1355827 := bstep (se 1 (by rfl) ⟨1016870, by rfl⟩ : syracuseStep 1355827 = 2033741) B2033741
theorem B2035793 : Blo 1204419 2035793 := bstep (se 2 (by rfl) ⟨763422, by rfl⟩ : syracuseStep 2035793 = 1526845) B1526845
theorem B3862637 : Blo 1204419 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B2060401 : Blo 1204419 2060401 := bstep (se 2 (by rfl) ⟨772650, by rfl⟩ : syracuseStep 2060401 = 1545301) B1545301
theorem B4067441 : Blo 1204419 4067441 := bstep (se 2 (by rfl) ⟨1525290, by rfl⟩ : syracuseStep 4067441 = 3050581) B3050581
theorem B2060417 : Blo 1204419 2060417 := bstep (se 2 (by rfl) ⟨772656, by rfl⟩ : syracuseStep 2060417 = 1545313) B1545313
theorem B10293389 : Blo 1204419 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B3051665 : Blo 1204419 3051665 := bstep (se 2 (by rfl) ⟨1144374, by rfl⟩ : syracuseStep 3051665 = 2288749) B2288749
theorem B1716385 : Blo 1204419 1716385 := bstep (se 2 (by rfl) ⟨643644, by rfl⟩ : syracuseStep 1716385 = 1287289) B1287289
theorem B1355971 : Blo 1204419 1355971 := bstep (se 1 (by rfl) ⟨1016978, by rfl⟩ : syracuseStep 1355971 = 2033957) B2033957
theorem B3051715 : Blo 1204419 3051715 := bstep (se 1 (by rfl) ⟨2288786, by rfl⟩ : syracuseStep 3051715 = 4577573) B4577573
theorem B15454435 : Blo 1204419 15454435 := bstep (se 1 (by rfl) ⟨11590826, by rfl⟩ : syracuseStep 15454435 = 23181653) B23181653
theorem B2060561 : Blo 1204419 2060561 := bstep (se 2 (by rfl) ⟨772710, by rfl⟩ : syracuseStep 2060561 = 1545421) B1545421
theorem B1716499 : Blo 1204419 1716499 := bstep (se 1 (by rfl) ⟨1287374, by rfl⟩ : syracuseStep 1716499 = 2574749) B2574749
theorem B1806641 : Blo 1204419 1806641 := bstep (se 2 (by rfl) ⟨677490, by rfl⟩ : syracuseStep 1806641 = 1354981) B1354981
theorem B1806659 : Blo 1204419 1806659 := bstep (se 1 (by rfl) ⟨1354994, by rfl⟩ : syracuseStep 1806659 = 2709989) B2709989
theorem B3051857 : Blo 1204419 3051857 := bstep (se 2 (by rfl) ⟨1144446, by rfl⟩ : syracuseStep 3051857 = 2288893) B2288893
theorem B1356115 : Blo 1204419 1356115 := bstep (se 1 (by rfl) ⟨1017086, by rfl⟩ : syracuseStep 1356115 = 2034173) B2034173
theorem B1806689 : Blo 1204419 1806689 := bstep (se 2 (by rfl) ⟨677508, by rfl⟩ : syracuseStep 1806689 = 1355017) B1355017
theorem B6099299 : Blo 1204419 6099299 := bstep (se 1 (by rfl) ⟨4574474, by rfl⟩ : syracuseStep 6099299 = 9148949) B9148949
theorem B4886897 : Blo 1204419 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B1806707 : Blo 1204419 1806707 := bstep (se 1 (by rfl) ⟨1355030, by rfl⟩ : syracuseStep 1806707 = 2710061) B2710061
theorem B4575629 : Blo 1204419 4575629 := bstep (se 3 (by rfl) ⟨857930, by rfl⟩ : syracuseStep 4575629 = 1715861) B1715861
theorem B1806737 : Blo 1204419 1806737 := bstep (se 2 (by rfl) ⟨677526, by rfl⟩ : syracuseStep 1806737 = 1355053) B1355053
theorem B1806755 : Blo 1204419 1806755 := bstep (se 1 (by rfl) ⟨1355066, by rfl⟩ : syracuseStep 1806755 = 2710133) B2710133
theorem B1806785 : Blo 1204419 1806785 := bstep (se 2 (by rfl) ⟨677544, by rfl⟩ : syracuseStep 1806785 = 1355089) B1355089
theorem B1806803 : Blo 1204419 1806803 := bstep (se 1 (by rfl) ⟨1355102, by rfl⟩ : syracuseStep 1806803 = 2710205) B2710205
theorem B1356259 : Blo 1204419 1356259 := bstep (se 1 (by rfl) ⟨1017194, by rfl⟩ : syracuseStep 1356259 = 2034389) B2034389
theorem B1806833 : Blo 1204419 1806833 := bstep (se 2 (by rfl) ⟨677562, by rfl⟩ : syracuseStep 1806833 = 1355125) B1355125
theorem B1806851 : Blo 1204419 1806851 := bstep (se 1 (by rfl) ⟨1355138, by rfl⟩ : syracuseStep 1806851 = 2710277) B2710277
theorem B7721477 : Blo 1204419 7721477 := bstep (se 4 (by rfl) ⟨723888, by rfl⟩ : syracuseStep 7721477 = 1447777) B1447777
theorem B1806881 : Blo 1204419 1806881 := bstep (se 2 (by rfl) ⟨677580, by rfl⟩ : syracuseStep 1806881 = 1355161) B1355161
theorem B1806899 : Blo 1204419 1806899 := bstep (se 1 (by rfl) ⟨1355174, by rfl⟩ : syracuseStep 1806899 = 2710349) B2710349
theorem B1806929 : Blo 1204419 1806929 := bstep (se 2 (by rfl) ⟨677598, by rfl⟩ : syracuseStep 1806929 = 1355197) B1355197
theorem B1806947 : Blo 1204419 1806947 := bstep (se 1 (by rfl) ⟨1355210, by rfl⟩ : syracuseStep 1806947 = 2710421) B2710421
theorem B1356403 : Blo 1204419 1356403 := bstep (se 1 (by rfl) ⟨1017302, by rfl⟩ : syracuseStep 1356403 = 2034605) B2034605
theorem B1806977 : Blo 1204419 1806977 := bstep (se 2 (by rfl) ⟨677616, by rfl⟩ : syracuseStep 1806977 = 1355233) B1355233
theorem B4067981 : Blo 1204419 4067981 := bstep (se 3 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 4067981 = 1525493) B1525493
theorem B1806995 : Blo 1204419 1806995 := bstep (se 1 (by rfl) ⟨1355246, by rfl⟩ : syracuseStep 1806995 = 2710493) B2710493
theorem B1807025 : Blo 1204419 1807025 := bstep (se 2 (by rfl) ⟨677634, by rfl⟩ : syracuseStep 1807025 = 1355269) B1355269
theorem B1807043 : Blo 1204419 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B4068035 : Blo 1204419 4068035 := bstep (se 1 (by rfl) ⟨3051026, by rfl⟩ : syracuseStep 4068035 = 6102053) B6102053
theorem B6861509 : Blo 1204419 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B1807073 : Blo 1204419 1807073 := bstep (se 2 (by rfl) ⟨677652, by rfl⟩ : syracuseStep 1807073 = 1355305) B1355305
theorem B6869731 : Blo 1204419 6869731 := bstep (se 1 (by rfl) ⟨5152298, by rfl⟩ : syracuseStep 6869731 = 10304597) B10304597
theorem B7328497 : Blo 1204419 7328497 := bstep (se 2 (by rfl) ⟨2748186, by rfl⟩ : syracuseStep 7328497 = 5496373) B5496373
theorem B1807091 : Blo 1204419 1807091 := bstep (se 1 (by rfl) ⟨1355318, by rfl⟩ : syracuseStep 1807091 = 2710637) B2710637
theorem B1356547 : Blo 1204419 1356547 := bstep (se 1 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 1356547 = 2034821) B2034821
theorem B1807121 : Blo 1204419 1807121 := bstep (se 2 (by rfl) ⟨677670, by rfl⟩ : syracuseStep 1807121 = 1355341) B1355341
theorem B1807139 : Blo 1204419 1807139 := bstep (se 1 (by rfl) ⟨1355354, by rfl⟩ : syracuseStep 1807139 = 2710709) B2710709
theorem B1807169 : Blo 1204419 1807169 := bstep (se 2 (by rfl) ⟨677688, by rfl⟩ : syracuseStep 1807169 = 1355377) B1355377
theorem B1807187 : Blo 1204419 1807187 := bstep (se 1 (by rfl) ⟨1355390, by rfl⟩ : syracuseStep 1807187 = 2710781) B2710781
theorem B1807217 : Blo 1204419 1807217 := bstep (se 2 (by rfl) ⟨677706, by rfl⟩ : syracuseStep 1807217 = 1355413) B1355413
theorem B1807235 : Blo 1204419 1807235 := bstep (se 1 (by rfl) ⟨1355426, by rfl⟩ : syracuseStep 1807235 = 2710853) B2710853
theorem B6517637 : Blo 1204419 6517637 := bstep (se 4 (by rfl) ⟨611028, by rfl⟩ : syracuseStep 6517637 = 1222057) B1222057
theorem B4641677 : Blo 1204419 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1356691 : Blo 1204419 1356691 := bstep (se 1 (by rfl) ⟨1017518, by rfl⟩ : syracuseStep 1356691 = 2035037) B2035037
theorem B1807265 : Blo 1204419 1807265 := bstep (se 2 (by rfl) ⟨677724, by rfl⟩ : syracuseStep 1807265 = 1355449) B1355449
theorem B1807283 : Blo 1204419 1807283 := bstep (se 1 (by rfl) ⟨1355462, by rfl⟩ : syracuseStep 1807283 = 2710925) B2710925
theorem B1807313 : Blo 1204419 1807313 := bstep (se 2 (by rfl) ⟨677742, by rfl⟩ : syracuseStep 1807313 = 1355485) B1355485
theorem B4068305 : Blo 1204419 4068305 := bstep (se 2 (by rfl) ⟨1525614, by rfl⟩ : syracuseStep 4068305 = 3051229) B3051229
theorem B1807331 : Blo 1204419 1807331 := bstep (se 1 (by rfl) ⟨1355498, by rfl⟩ : syracuseStep 1807331 = 2710997) B2710997
theorem B3863533 : Blo 1204419 3863533 := bstep (se 3 (by rfl) ⟨724412, by rfl⟩ : syracuseStep 3863533 = 1448825) B1448825
theorem B1807361 : Blo 1204419 1807361 := bstep (se 2 (by rfl) ⟨677760, by rfl⟩ : syracuseStep 1807361 = 1355521) B1355521
theorem B1807379 : Blo 1204419 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B1356835 : Blo 1204419 1356835 := bstep (se 1 (by rfl) ⟨1017626, by rfl⟩ : syracuseStep 1356835 = 2035253) B2035253
theorem B1807409 : Blo 1204419 1807409 := bstep (se 2 (by rfl) ⟨677778, by rfl⟩ : syracuseStep 1807409 = 1355557) B1355557
theorem B1807427 : Blo 1204419 1807427 := bstep (se 1 (by rfl) ⟨1355570, by rfl⟩ : syracuseStep 1807427 = 2711141) B2711141
theorem B3667021 : Blo 1204419 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B1807457 : Blo 1204419 1807457 := bstep (se 2 (by rfl) ⟨677796, by rfl⟩ : syracuseStep 1807457 = 1355593) B1355593
theorem B9147491 : Blo 1204419 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B1807475 : Blo 1204419 1807475 := bstep (se 1 (by rfl) ⟨1355606, by rfl⟩ : syracuseStep 1807475 = 2711213) B2711213
theorem B6100109 : Blo 1204419 6100109 := bstep (se 3 (by rfl) ⟨1143770, by rfl⟩ : syracuseStep 6100109 = 2287541) B2287541
theorem B1807505 : Blo 1204419 1807505 := bstep (se 2 (by rfl) ⟨677814, by rfl⟩ : syracuseStep 1807505 = 1355629) B1355629
theorem B1807523 : Blo 1204419 1807523 := bstep (se 1 (by rfl) ⟨1355642, by rfl⟩ : syracuseStep 1807523 = 2711285) B2711285
theorem B1356979 : Blo 1204419 1356979 := bstep (se 1 (by rfl) ⟨1017734, by rfl⟩ : syracuseStep 1356979 = 2035469) B2035469
theorem B1807553 : Blo 1204419 1807553 := bstep (se 2 (by rfl) ⟨677832, by rfl⟩ : syracuseStep 1807553 = 1355665) B1355665
theorem B1807571 : Blo 1204419 1807571 := bstep (se 1 (by rfl) ⟨1355678, by rfl⟩ : syracuseStep 1807571 = 2711357) B2711357
theorem B30889187 : Blo 1204419 30889187 := bstep (se 1 (by rfl) ⟨23166890, by rfl⟩ : syracuseStep 30889187 = 46333781) B46333781
theorem B1807601 : Blo 1204419 1807601 := bstep (se 2 (by rfl) ⟨677850, by rfl⟩ : syracuseStep 1807601 = 1355701) B1355701
theorem B6870257 : Blo 1204419 6870257 := bstep (se 2 (by rfl) ⟨2576346, by rfl⟩ : syracuseStep 6870257 = 5152693) B5152693
theorem B1807619 : Blo 1204419 1807619 := bstep (se 1 (by rfl) ⟨1355714, by rfl⟩ : syracuseStep 1807619 = 2711429) B2711429
theorem B1807649 : Blo 1204419 1807649 := bstep (se 2 (by rfl) ⟨677868, by rfl⟩ : syracuseStep 1807649 = 1355737) B1355737
theorem B3052849 : Blo 1204419 3052849 := bstep (se 2 (by rfl) ⟨1144818, by rfl⟩ : syracuseStep 3052849 = 2289637) B2289637
theorem B1807667 : Blo 1204419 1807667 := bstep (se 1 (by rfl) ⟨1355750, by rfl⟩ : syracuseStep 1807667 = 2711501) B2711501
theorem B1357123 : Blo 1204419 1357123 := bstep (se 1 (by rfl) ⟨1017842, by rfl⟩ : syracuseStep 1357123 = 2035685) B2035685
theorem B1807697 : Blo 1204419 1807697 := bstep (se 2 (by rfl) ⟨677886, by rfl⟩ : syracuseStep 1807697 = 1355773) B1355773
theorem B1832291 : Blo 1204419 1832291 := bstep (se 1 (by rfl) ⟨1374218, by rfl⟩ : syracuseStep 1832291 = 2748437) B2748437
theorem B1807715 : Blo 1204419 1807715 := bstep (se 1 (by rfl) ⟨1355786, by rfl⟩ : syracuseStep 1807715 = 2711573) B2711573
theorem B1807745 : Blo 1204419 1807745 := bstep (se 2 (by rfl) ⟨677904, by rfl⟩ : syracuseStep 1807745 = 1355809) B1355809
theorem B1807763 : Blo 1204419 1807763 := bstep (se 1 (by rfl) ⟨1355822, by rfl⟩ : syracuseStep 1807763 = 2711645) B2711645
theorem B2897315 : Blo 1204419 2897315 := bstep (se 1 (by rfl) ⟨2172986, by rfl⟩ : syracuseStep 2897315 = 4345973) B4345973
theorem B3429809 : Blo 1204419 3429809 := bstep (se 2 (by rfl) ⟨1286178, by rfl⟩ : syracuseStep 3429809 = 2572357) B2572357
theorem B1807793 : Blo 1204419 1807793 := bstep (se 2 (by rfl) ⟨677922, by rfl⟩ : syracuseStep 1807793 = 1355845) B1355845
theorem B1807811 : Blo 1204419 1807811 := bstep (se 1 (by rfl) ⟨1355858, by rfl⟩ : syracuseStep 1807811 = 2711717) B2711717
theorem B1930691 : Blo 1204419 1930691 := bstep (se 1 (by rfl) ⟨1448018, by rfl⟩ : syracuseStep 1930691 = 2896037) B2896037
theorem B1807841 : Blo 1204419 1807841 := bstep (se 2 (by rfl) ⟨677940, by rfl⟩ : syracuseStep 1807841 = 1355881) B1355881
theorem B4068845 : Blo 1204419 4068845 := bstep (se 3 (by rfl) ⟨762908, by rfl⟩ : syracuseStep 4068845 = 1525817) B1525817
theorem B1807859 : Blo 1204419 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B1447427 : Blo 1204419 1447427 := bstep (se 1 (by rfl) ⟨1085570, by rfl⟩ : syracuseStep 1447427 = 2171141) B2171141
theorem B1807889 : Blo 1204419 1807889 := bstep (se 2 (by rfl) ⟨677958, by rfl⟩ : syracuseStep 1807889 = 1355917) B1355917
theorem B1807907 : Blo 1204419 1807907 := bstep (se 1 (by rfl) ⟨1355930, by rfl⟩ : syracuseStep 1807907 = 2711861) B2711861
theorem B4068899 : Blo 1204419 4068899 := bstep (se 1 (by rfl) ⟨3051674, by rfl⟩ : syracuseStep 4068899 = 6103349) B6103349
theorem B2061875 : Blo 1204419 2061875 := bstep (se 1 (by rfl) ⟨1546406, by rfl⟩ : syracuseStep 2061875 = 3092813) B3092813
theorem B1807937 : Blo 1204419 1807937 := bstep (se 2 (by rfl) ⟨677976, by rfl⟩ : syracuseStep 1807937 = 1355953) B1355953
theorem B3053123 : Blo 1204419 3053123 := bstep (se 1 (by rfl) ⟨2289842, by rfl⟩ : syracuseStep 3053123 = 4579685) B4579685
theorem B1807955 : Blo 1204419 1807955 := bstep (se 1 (by rfl) ⟨1355966, by rfl⟩ : syracuseStep 1807955 = 2711933) B2711933
theorem B1807985 : Blo 1204419 1807985 := bstep (se 2 (by rfl) ⟨677994, by rfl⟩ : syracuseStep 1807985 = 1355989) B1355989
theorem B18814577 : Blo 1204419 18814577 := bstep (se 2 (by rfl) ⟨7055466, by rfl⟩ : syracuseStep 18814577 = 14110933) B14110933
theorem B1808003 : Blo 1204419 1808003 := bstep (se 1 (by rfl) ⟨1356002, by rfl⟩ : syracuseStep 1808003 = 2712005) B2712005
theorem B1808033 : Blo 1204419 1808033 := bstep (se 2 (by rfl) ⟨678012, by rfl⟩ : syracuseStep 1808033 = 1356025) B1356025
theorem B1808051 : Blo 1204419 1808051 := bstep (se 1 (by rfl) ⟨1356038, by rfl⟩ : syracuseStep 1808051 = 2712077) B2712077
theorem B1808081 : Blo 1204419 1808081 := bstep (se 2 (by rfl) ⟨678030, by rfl⟩ : syracuseStep 1808081 = 1356061) B1356061
theorem B1808099 : Blo 1204419 1808099 := bstep (se 1 (by rfl) ⟨1356074, by rfl⟩ : syracuseStep 1808099 = 2712149) B2712149
theorem B1930979 : Blo 1204419 1930979 := bstep (se 1 (by rfl) ⟨1448234, by rfl⟩ : syracuseStep 1930979 = 2896469) B2896469
theorem B1808129 : Blo 1204419 1808129 := bstep (se 2 (by rfl) ⟨678048, by rfl⟩ : syracuseStep 1808129 = 1356097) B1356097
theorem B3053315 : Blo 1204419 3053315 := bstep (se 1 (by rfl) ⟨2289986, by rfl⟩ : syracuseStep 3053315 = 4579973) B4579973
theorem B1808147 : Blo 1204419 1808147 := bstep (se 1 (by rfl) ⟨1356110, by rfl⟩ : syracuseStep 1808147 = 2712221) B2712221
theorem B1808177 : Blo 1204419 1808177 := bstep (se 2 (by rfl) ⟨678066, by rfl⟩ : syracuseStep 1808177 = 1356133) B1356133
theorem B4069169 : Blo 1204419 4069169 := bstep (se 2 (by rfl) ⟨1525938, by rfl⟩ : syracuseStep 4069169 = 3051877) B3051877
theorem B17372981 : Blo 1204419 17372981 := bstep (se 5 (by rfl) ⟨814358, by rfl⟩ : syracuseStep 17372981 = 1628717) B1628717
theorem B1808195 : Blo 1204419 1808195 := bstep (se 1 (by rfl) ⟨1356146, by rfl⟩ : syracuseStep 1808195 = 2712293) B2712293
theorem B1808225 : Blo 1204419 1808225 := bstep (se 2 (by rfl) ⟨678084, by rfl⟩ : syracuseStep 1808225 = 1356169) B1356169
theorem B3864419 : Blo 1204419 3864419 := bstep (se 1 (by rfl) ⟨2898314, by rfl⟩ : syracuseStep 3864419 = 5796629) B5796629
theorem B1808243 : Blo 1204419 1808243 := bstep (se 1 (by rfl) ⟨1356182, by rfl⟩ : syracuseStep 1808243 = 2712365) B2712365
theorem B1808273 : Blo 1204419 1808273 := bstep (se 2 (by rfl) ⟨678102, by rfl⟩ : syracuseStep 1808273 = 1356205) B1356205
theorem B1808291 : Blo 1204419 1808291 := bstep (se 1 (by rfl) ⟨1356218, by rfl⟩ : syracuseStep 1808291 = 2712437) B2712437
theorem B1808321 : Blo 1204419 1808321 := bstep (se 2 (by rfl) ⟨678120, by rfl⟩ : syracuseStep 1808321 = 1356241) B1356241
theorem B1808339 : Blo 1204419 1808339 := bstep (se 1 (by rfl) ⟨1356254, by rfl⟩ : syracuseStep 1808339 = 2712509) B2712509
theorem B1808369 : Blo 1204419 1808369 := bstep (se 2 (by rfl) ⟨678138, by rfl⟩ : syracuseStep 1808369 = 1356277) B1356277
theorem B1808387 : Blo 1204419 1808387 := bstep (se 1 (by rfl) ⟨1356290, by rfl⟩ : syracuseStep 1808387 = 2712581) B2712581
theorem B16488461 : Blo 1204419 16488461 := bstep (se 3 (by rfl) ⟨3091586, by rfl⟩ : syracuseStep 16488461 = 6183173) B6183173
theorem B1808417 : Blo 1204419 1808417 := bstep (se 2 (by rfl) ⟨678156, by rfl⟩ : syracuseStep 1808417 = 1356313) B1356313
theorem B1628209 : Blo 1204419 1628209 := bstep (se 2 (by rfl) ⟨610578, by rfl⟩ : syracuseStep 1628209 = 1221157) B1221157
theorem B1808435 : Blo 1204419 1808435 := bstep (se 1 (by rfl) ⟨1356326, by rfl⟩ : syracuseStep 1808435 = 2712653) B2712653
theorem B1833025 : Blo 1204419 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B1808465 : Blo 1204419 1808465 := bstep (se 2 (by rfl) ⟨678174, by rfl⟩ : syracuseStep 1808465 = 1356349) B1356349
theorem B1808483 : Blo 1204419 1808483 := bstep (se 1 (by rfl) ⟨1356362, by rfl⟩ : syracuseStep 1808483 = 2712725) B2712725
theorem B1808513 : Blo 1204419 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B1808531 : Blo 1204419 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B1808561 : Blo 1204419 1808561 := bstep (se 2 (by rfl) ⟨678210, by rfl⟩ : syracuseStep 1808561 = 1356421) B1356421
theorem B1808579 : Blo 1204419 1808579 := bstep (se 1 (by rfl) ⟨1356434, by rfl⟩ : syracuseStep 1808579 = 2712869) B2712869
theorem B4888781 : Blo 1204419 4888781 := bstep (se 3 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 4888781 = 1833293) B1833293
theorem B1808609 : Blo 1204419 1808609 := bstep (se 2 (by rfl) ⟨678228, by rfl⟩ : syracuseStep 1808609 = 1356457) B1356457
theorem B13719779 : Blo 1204419 13719779 := bstep (se 1 (by rfl) ⟨10289834, by rfl⟩ : syracuseStep 13719779 = 20579669) B20579669
theorem B1808627 : Blo 1204419 1808627 := bstep (se 1 (by rfl) ⟨1356470, by rfl⟩ : syracuseStep 1808627 = 2712941) B2712941
theorem B1808657 : Blo 1204419 1808657 := bstep (se 2 (by rfl) ⟨678246, by rfl⟩ : syracuseStep 1808657 = 1356493) B1356493
theorem B1808675 : Blo 1204419 1808675 := bstep (se 1 (by rfl) ⟨1356506, by rfl⟩ : syracuseStep 1808675 = 2713013) B2713013
theorem B1808705 : Blo 1204419 1808705 := bstep (se 2 (by rfl) ⟨678264, by rfl⟩ : syracuseStep 1808705 = 1356529) B1356529
theorem B4069709 : Blo 1204419 4069709 := bstep (se 3 (by rfl) ⟨763070, by rfl⟩ : syracuseStep 4069709 = 1526141) B1526141
theorem B5151053 : Blo 1204419 5151053 := bstep (se 3 (by rfl) ⟨965822, by rfl⟩ : syracuseStep 5151053 = 1931645) B1931645
theorem B1808723 : Blo 1204419 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B3430765 : Blo 1204419 3430765 := bstep (se 3 (by rfl) ⟨643268, by rfl⟩ : syracuseStep 3430765 = 1286537) B1286537
theorem B3258733 : Blo 1204419 3258733 := bstep (se 3 (by rfl) ⟨611012, by rfl⟩ : syracuseStep 3258733 = 1222025) B1222025
theorem B1808753 : Blo 1204419 1808753 := bstep (se 2 (by rfl) ⟨678282, by rfl⟩ : syracuseStep 1808753 = 1356565) B1356565
theorem B1808771 : Blo 1204419 1808771 := bstep (se 1 (by rfl) ⟨1356578, by rfl⟩ : syracuseStep 1808771 = 2713157) B2713157
theorem B4069763 : Blo 1204419 4069763 := bstep (se 1 (by rfl) ⟨3052322, by rfl⟩ : syracuseStep 4069763 = 6104645) B6104645
theorem B2750851 : Blo 1204419 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B1808801 : Blo 1204419 1808801 := bstep (se 2 (by rfl) ⟨678300, by rfl⟩ : syracuseStep 1808801 = 1356601) B1356601
theorem B1808819 : Blo 1204419 1808819 := bstep (se 1 (by rfl) ⟨1356614, by rfl⟩ : syracuseStep 1808819 = 2713229) B2713229
theorem B4577741 : Blo 1204419 4577741 := bstep (se 3 (by rfl) ⟨858326, by rfl⟩ : syracuseStep 4577741 = 1716653) B1716653
theorem B1808849 : Blo 1204419 1808849 := bstep (se 2 (by rfl) ⟨678318, by rfl⟩ : syracuseStep 1808849 = 1356637) B1356637
theorem B1808867 : Blo 1204419 1808867 := bstep (se 1 (by rfl) ⟨1356650, by rfl⟩ : syracuseStep 1808867 = 2713301) B2713301
theorem B1956337 : Blo 1204419 1956337 := bstep (se 2 (by rfl) ⟨733626, by rfl⟩ : syracuseStep 1956337 = 1467253) B1467253
theorem B1808897 : Blo 1204419 1808897 := bstep (se 2 (by rfl) ⟨678336, by rfl⟩ : syracuseStep 1808897 = 1356673) B1356673
theorem B3258883 : Blo 1204419 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B1931779 : Blo 1204419 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B1808915 : Blo 1204419 1808915 := bstep (se 1 (by rfl) ⟨1356686, by rfl⟩ : syracuseStep 1808915 = 2713373) B2713373
theorem B1808945 : Blo 1204419 1808945 := bstep (se 2 (by rfl) ⟨678354, by rfl⟩ : syracuseStep 1808945 = 1356709) B1356709
theorem B1808963 : Blo 1204419 1808963 := bstep (se 1 (by rfl) ⟨1356722, by rfl⟩ : syracuseStep 1808963 = 2713445) B2713445
theorem B2710097 : Blo 1204419 2710097 := bstep (se 2 (by rfl) ⟨1016286, by rfl⟩ : syracuseStep 2710097 = 2032573) B2032573
theorem B3430993 : Blo 1204419 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B1808993 : Blo 1204419 1808993 := bstep (se 2 (by rfl) ⟨678372, by rfl⟩ : syracuseStep 1808993 = 1356745) B1356745
theorem B2710115 : Blo 1204419 2710115 := bstep (se 1 (by rfl) ⟨2032586, by rfl⟩ : syracuseStep 2710115 = 4065173) B4065173
theorem B1587811 : Blo 1204419 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B3668579 : Blo 1204419 3668579 := bstep (se 1 (by rfl) ⟨2751434, by rfl⟩ : syracuseStep 3668579 = 5502869) B5502869
theorem B1809011 : Blo 1204419 1809011 := bstep (se 1 (by rfl) ⟨1356758, by rfl⟩ : syracuseStep 1809011 = 2713517) B2713517
theorem B4070033 : Blo 1204419 4070033 := bstep (se 2 (by rfl) ⟨1526262, by rfl⟩ : syracuseStep 4070033 = 3052525) B3052525
theorem B1809041 : Blo 1204419 1809041 := bstep (se 2 (by rfl) ⟨678390, by rfl⟩ : syracuseStep 1809041 = 1356781) B1356781
theorem B1931921 : Blo 1204419 1931921 := bstep (se 2 (by rfl) ⟨724470, by rfl⟩ : syracuseStep 1931921 = 1448941) B1448941
theorem B1809059 : Blo 1204419 1809059 := bstep (se 1 (by rfl) ⟨1356794, by rfl⟩ : syracuseStep 1809059 = 2713589) B2713589
theorem B1931953 : Blo 1204419 1931953 := bstep (se 2 (by rfl) ⟨724482, by rfl⟩ : syracuseStep 1931953 = 1448965) B1448965
theorem B1809089 : Blo 1204419 1809089 := bstep (se 2 (by rfl) ⟨678408, by rfl⟩ : syracuseStep 1809089 = 1356817) B1356817
theorem B1809107 : Blo 1204419 1809107 := bstep (se 1 (by rfl) ⟨1356830, by rfl⟩ : syracuseStep 1809107 = 2713661) B2713661
theorem B3431153 : Blo 1204419 3431153 := bstep (se 2 (by rfl) ⟨1286682, by rfl⟩ : syracuseStep 3431153 = 2573365) B2573365
theorem B1809137 : Blo 1204419 1809137 := bstep (se 2 (by rfl) ⟨678426, by rfl⟩ : syracuseStep 1809137 = 1356853) B1356853
theorem B1809155 : Blo 1204419 1809155 := bstep (se 1 (by rfl) ⟨1356866, by rfl⟩ : syracuseStep 1809155 = 2713733) B2713733
theorem B1809185 : Blo 1204419 1809185 := bstep (se 2 (by rfl) ⟨678444, by rfl⟩ : syracuseStep 1809185 = 1356889) B1356889
theorem B1809203 : Blo 1204419 1809203 := bstep (se 1 (by rfl) ⟨1356902, by rfl⟩ : syracuseStep 1809203 = 2713805) B2713805
theorem B1809233 : Blo 1204419 1809233 := bstep (se 2 (by rfl) ⟨678462, by rfl⟩ : syracuseStep 1809233 = 1356925) B1356925
theorem B3431267 : Blo 1204419 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B1809251 : Blo 1204419 1809251 := bstep (se 1 (by rfl) ⟨1356938, by rfl⟩ : syracuseStep 1809251 = 2713877) B2713877
theorem B2710385 : Blo 1204419 2710385 := bstep (se 2 (by rfl) ⟨1016394, by rfl⟩ : syracuseStep 2710385 = 2032789) B2032789
theorem B1809281 : Blo 1204419 1809281 := bstep (se 2 (by rfl) ⟨678480, by rfl⟩ : syracuseStep 1809281 = 1356961) B1356961
theorem B2710403 : Blo 1204419 2710403 := bstep (se 1 (by rfl) ⟨2032802, by rfl⟩ : syracuseStep 2710403 = 4065605) B4065605
theorem B32971661 : Blo 1204419 32971661 := bstep (se 3 (by rfl) ⟨6182186, by rfl⟩ : syracuseStep 32971661 = 12364373) B12364373
theorem B1809299 : Blo 1204419 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B1809329 : Blo 1204419 1809329 := bstep (se 2 (by rfl) ⟨678498, by rfl⟩ : syracuseStep 1809329 = 1356997) B1356997
theorem B1809347 : Blo 1204419 1809347 := bstep (se 1 (by rfl) ⟨1357010, by rfl⟩ : syracuseStep 1809347 = 2714021) B2714021
theorem B1629139 : Blo 1204419 1629139 := bstep (se 1 (by rfl) ⟨1221854, by rfl⟩ : syracuseStep 1629139 = 2443709) B2443709
theorem B1809377 : Blo 1204419 1809377 := bstep (se 2 (by rfl) ⟨678516, by rfl⟩ : syracuseStep 1809377 = 1357033) B1357033
theorem B1809395 : Blo 1204419 1809395 := bstep (se 1 (by rfl) ⟨1357046, by rfl⟩ : syracuseStep 1809395 = 2714093) B2714093
theorem B1809425 : Blo 1204419 1809425 := bstep (se 2 (by rfl) ⟨678534, by rfl⟩ : syracuseStep 1809425 = 1357069) B1357069
theorem B1809443 : Blo 1204419 1809443 := bstep (se 1 (by rfl) ⟨1357082, by rfl⟩ : syracuseStep 1809443 = 2714165) B2714165
theorem B1809473 : Blo 1204419 1809473 := bstep (se 2 (by rfl) ⟨678552, by rfl⟩ : syracuseStep 1809473 = 1357105) B1357105
theorem B1809491 : Blo 1204419 1809491 := bstep (se 1 (by rfl) ⟨1357118, by rfl⟩ : syracuseStep 1809491 = 2714237) B2714237
theorem B43981937 : Blo 1204419 43981937 := bstep (se 2 (by rfl) ⟨16493226, by rfl⟩ : syracuseStep 43981937 = 32986453) B32986453
theorem B1809521 : Blo 1204419 1809521 := bstep (se 2 (by rfl) ⟨678570, by rfl⟩ : syracuseStep 1809521 = 1357141) B1357141
theorem B1809539 : Blo 1204419 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B2710673 : Blo 1204419 2710673 := bstep (se 2 (by rfl) ⟨1016502, by rfl⟩ : syracuseStep 2710673 = 2033005) B2033005
theorem B1809569 : Blo 1204419 1809569 := bstep (se 2 (by rfl) ⟨678588, by rfl⟩ : syracuseStep 1809569 = 1357177) B1357177
theorem B2710691 : Blo 1204419 2710691 := bstep (se 1 (by rfl) ⟨2033018, by rfl⟩ : syracuseStep 2710691 = 4066037) B4066037
theorem B4070573 : Blo 1204419 4070573 := bstep (se 3 (by rfl) ⟨763232, by rfl⟩ : syracuseStep 4070573 = 1526465) B1526465
theorem B1809587 : Blo 1204419 1809587 := bstep (se 1 (by rfl) ⟨1357190, by rfl⟩ : syracuseStep 1809587 = 2714381) B2714381
theorem B1834193 : Blo 1204419 1834193 := bstep (se 2 (by rfl) ⟨687822, by rfl⟩ : syracuseStep 1834193 = 1375645) B1375645
theorem B1809617 : Blo 1204419 1809617 := bstep (se 2 (by rfl) ⟨678606, by rfl⟩ : syracuseStep 1809617 = 1357213) B1357213
theorem B4070627 : Blo 1204419 4070627 := bstep (se 1 (by rfl) ⟨3052970, by rfl⟩ : syracuseStep 4070627 = 6105941) B6105941
theorem B4578545 : Blo 1204419 4578545 := bstep (se 2 (by rfl) ⟨1716954, by rfl⟩ : syracuseStep 4578545 = 3433909) B3433909
theorem B3259661 : Blo 1204419 3259661 := bstep (se 3 (by rfl) ⟨611186, by rfl⟩ : syracuseStep 3259661 = 1222373) B1222373
theorem B2710961 : Blo 1204419 2710961 := bstep (se 2 (by rfl) ⟨1016610, by rfl⟩ : syracuseStep 2710961 = 2033221) B2033221
theorem B2710979 : Blo 1204419 2710979 := bstep (se 1 (by rfl) ⟨2033234, by rfl⟩ : syracuseStep 2710979 = 4066469) B4066469
theorem B1957331 : Blo 1204419 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B1883633 : Blo 1204419 1883633 := bstep (se 2 (by rfl) ⟨706362, by rfl⟩ : syracuseStep 1883633 = 1412725) B1412725
theorem B4070897 : Blo 1204419 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B2711249 : Blo 1204419 2711249 := bstep (se 2 (by rfl) ⟨1016718, by rfl⟩ : syracuseStep 2711249 = 2033437) B2033437
theorem B2711267 : Blo 1204419 2711267 := bstep (se 1 (by rfl) ⟨2033450, by rfl⟩ : syracuseStep 2711267 = 4066901) B4066901
theorem B15441677 : Blo 1204419 15441677 := bstep (se 3 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 15441677 = 5790629) B5790629
theorem B35249941 : Blo 1204419 35249941 := bstep (se 6 (by rfl) ⟨826170, by rfl⟩ : syracuseStep 35249941 = 1652341) B1652341
theorem B3432269 : Blo 1204419 3432269 := bstep (se 3 (by rfl) ⟨643550, by rfl⟩ : syracuseStep 3432269 = 1287101) B1287101
theorem B4407139 : Blo 1204419 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B4579213 : Blo 1204419 4579213 := bstep (se 3 (by rfl) ⟨858602, by rfl⟩ : syracuseStep 4579213 = 1717205) B1717205
theorem B7724963 : Blo 1204419 7724963 := bstep (se 1 (by rfl) ⟨5793722, by rfl⟩ : syracuseStep 7724963 = 11587445) B11587445
theorem B2170801 : Blo 1204419 2170801 := bstep (se 2 (by rfl) ⟨814050, by rfl⟩ : syracuseStep 2170801 = 1628101) B1628101
theorem B24723427 : Blo 1204419 24723427 := bstep (se 1 (by rfl) ⟨18542570, by rfl⟩ : syracuseStep 24723427 = 37085141) B37085141
theorem B2711537 : Blo 1204419 2711537 := bstep (se 2 (by rfl) ⟨1016826, by rfl⟩ : syracuseStep 2711537 = 2033653) B2033653
theorem B6103025 : Blo 1204419 6103025 := bstep (se 2 (by rfl) ⟨2288634, by rfl⟩ : syracuseStep 6103025 = 4577269) B4577269
theorem B2170945 : Blo 1204419 2170945 := bstep (se 2 (by rfl) ⟨814104, by rfl⟩ : syracuseStep 2170945 = 1628209) B1628209
theorem B2711627 : Blo 1204419 2711627 := bstep (se 1 (by rfl) ⟨2033720, by rfl⟩ : syracuseStep 2711627 = 4067441) B4067441
theorem B2711681 : Blo 1204419 2711681 := bstep (se 2 (by rfl) ⟨1016880, by rfl⟩ : syracuseStep 2711681 = 2033761) B2033761
theorem B1204427 : Blo 1204419 1204427 := bstep (se 1 (by rfl) ⟨903320, by rfl⟩ : syracuseStep 1204427 = 1806641) B1806641
theorem B1204439 : Blo 1204419 1204439 := bstep (se 1 (by rfl) ⟨903329, by rfl⟩ : syracuseStep 1204439 = 1806659) B1806659
theorem B1204459 : Blo 1204419 1204459 := bstep (se 1 (by rfl) ⟨903344, by rfl⟩ : syracuseStep 1204459 = 1806689) B1806689
theorem B1204471 : Blo 1204419 1204471 := bstep (se 1 (by rfl) ⟨903353, by rfl⟩ : syracuseStep 1204471 = 1806707) B1806707
theorem B1204491 : Blo 1204419 1204491 := bstep (se 1 (by rfl) ⟨903368, by rfl⟩ : syracuseStep 1204491 = 1806737) B1806737
theorem B1204503 : Blo 1204419 1204503 := bstep (se 1 (by rfl) ⟨903377, by rfl⟩ : syracuseStep 1204503 = 1806755) B1806755
theorem B1204523 : Blo 1204419 1204523 := bstep (se 1 (by rfl) ⟨903392, by rfl⟩ : syracuseStep 1204523 = 1806785) B1806785
theorem B1204535 : Blo 1204419 1204535 := bstep (se 1 (by rfl) ⟨903401, by rfl⟩ : syracuseStep 1204535 = 1806803) B1806803
theorem B1204555 : Blo 1204419 1204555 := bstep (se 1 (by rfl) ⟨903416, by rfl⟩ : syracuseStep 1204555 = 1806833) B1806833
theorem B1204567 : Blo 1204419 1204567 := bstep (se 1 (by rfl) ⟨903425, by rfl⟩ : syracuseStep 1204567 = 1806851) B1806851
theorem B2711897 : Blo 1204419 2711897 := bstep (se 2 (by rfl) ⟨1016961, by rfl⟩ : syracuseStep 2711897 = 2033923) B2033923
theorem B3432793 : Blo 1204419 3432793 := bstep (se 2 (by rfl) ⟨1287297, by rfl⟩ : syracuseStep 3432793 = 2574595) B2574595
theorem B1204587 : Blo 1204419 1204587 := bstep (se 1 (by rfl) ⟨903440, by rfl⟩ : syracuseStep 1204587 = 1806881) B1806881
theorem B1204599 : Blo 1204419 1204599 := bstep (se 1 (by rfl) ⟨903449, by rfl⟩ : syracuseStep 1204599 = 1806899) B1806899
theorem B1204619 : Blo 1204419 1204619 := bstep (se 1 (by rfl) ⟨903464, by rfl⟩ : syracuseStep 1204619 = 1806929) B1806929
theorem B1204631 : Blo 1204419 1204631 := bstep (se 1 (by rfl) ⟨903473, by rfl⟩ : syracuseStep 1204631 = 1806947) B1806947
theorem B1204651 : Blo 1204419 1204651 := bstep (se 1 (by rfl) ⟨903488, by rfl⟩ : syracuseStep 1204651 = 1806977) B1806977
theorem B2711987 : Blo 1204419 2711987 := bstep (se 1 (by rfl) ⟨2033990, by rfl⟩ : syracuseStep 2711987 = 4067981) B4067981
theorem B1204663 : Blo 1204419 1204663 := bstep (se 1 (by rfl) ⟨903497, by rfl⟩ : syracuseStep 1204663 = 1806995) B1806995
theorem B1204683 : Blo 1204419 1204683 := bstep (se 1 (by rfl) ⟨903512, by rfl⟩ : syracuseStep 1204683 = 1807025) B1807025
theorem B9904589 : Blo 1204419 9904589 := bstep (se 3 (by rfl) ⟨1857110, by rfl⟩ : syracuseStep 9904589 = 3714221) B3714221
theorem B1204695 : Blo 1204419 1204695 := bstep (se 1 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 1204695 = 1807043) B1807043
theorem B2712023 : Blo 1204419 2712023 := bstep (se 1 (by rfl) ⟨2034017, by rfl⟩ : syracuseStep 2712023 = 4068035) B4068035
theorem B1204715 : Blo 1204419 1204715 := bstep (se 1 (by rfl) ⟨903536, by rfl⟩ : syracuseStep 1204715 = 1807073) B1807073
theorem B1204727 : Blo 1204419 1204727 := bstep (se 1 (by rfl) ⟨903545, by rfl⟩ : syracuseStep 1204727 = 1807091) B1807091
theorem B1204747 : Blo 1204419 1204747 := bstep (se 1 (by rfl) ⟨903560, by rfl⟩ : syracuseStep 1204747 = 1807121) B1807121
theorem B1204759 : Blo 1204419 1204759 := bstep (se 1 (by rfl) ⟨903569, by rfl⟩ : syracuseStep 1204759 = 1807139) B1807139
theorem B10289699 : Blo 1204419 10289699 := bstep (se 1 (by rfl) ⟨7717274, by rfl⟩ : syracuseStep 10289699 = 15434549) B15434549
theorem B1204779 : Blo 1204419 1204779 := bstep (se 1 (by rfl) ⟨903584, by rfl⟩ : syracuseStep 1204779 = 1807169) B1807169
theorem B1204791 : Blo 1204419 1204791 := bstep (se 1 (by rfl) ⟨903593, by rfl⟩ : syracuseStep 1204791 = 1807187) B1807187
theorem B1204811 : Blo 1204419 1204811 := bstep (se 1 (by rfl) ⟨903608, by rfl⟩ : syracuseStep 1204811 = 1807217) B1807217
theorem B1204823 : Blo 1204419 1204823 := bstep (se 1 (by rfl) ⟨903617, by rfl⟩ : syracuseStep 1204823 = 1807235) B1807235
theorem B1204843 : Blo 1204419 1204843 := bstep (se 1 (by rfl) ⟨903632, by rfl⟩ : syracuseStep 1204843 = 1807265) B1807265
theorem B1204855 : Blo 1204419 1204855 := bstep (se 1 (by rfl) ⟨903641, by rfl⟩ : syracuseStep 1204855 = 1807283) B1807283
theorem B1204875 : Blo 1204419 1204875 := bstep (se 1 (by rfl) ⟨903656, by rfl⟩ : syracuseStep 1204875 = 1807313) B1807313
theorem B2712203 : Blo 1204419 2712203 := bstep (se 1 (by rfl) ⟨2034152, by rfl⟩ : syracuseStep 2712203 = 4068305) B4068305
theorem B1204887 : Blo 1204419 1204887 := bstep (se 1 (by rfl) ⟨903665, by rfl⟩ : syracuseStep 1204887 = 1807331) B1807331
theorem B1204907 : Blo 1204419 1204907 := bstep (se 1 (by rfl) ⟨903680, by rfl⟩ : syracuseStep 1204907 = 1807361) B1807361
theorem B1204919 : Blo 1204419 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B2712257 : Blo 1204419 2712257 := bstep (se 2 (by rfl) ⟨1017096, by rfl⟩ : syracuseStep 2712257 = 2034193) B2034193
theorem B1204939 : Blo 1204419 1204939 := bstep (se 1 (by rfl) ⟨903704, by rfl⟩ : syracuseStep 1204939 = 1807409) B1807409
theorem B8692429 : Blo 1204419 8692429 := bstep (se 3 (by rfl) ⟨1629830, by rfl⟩ : syracuseStep 8692429 = 3259661) B3259661
theorem B1204951 : Blo 1204419 1204951 := bstep (se 1 (by rfl) ⟨903713, by rfl⟩ : syracuseStep 1204951 = 1807427) B1807427
theorem B1204971 : Blo 1204419 1204971 := bstep (se 1 (by rfl) ⟨903728, by rfl⟩ : syracuseStep 1204971 = 1807457) B1807457
theorem B1204983 : Blo 1204419 1204983 := bstep (se 1 (by rfl) ⟨903737, by rfl⟩ : syracuseStep 1204983 = 1807475) B1807475
theorem B1205003 : Blo 1204419 1205003 := bstep (se 1 (by rfl) ⟨903752, by rfl⟩ : syracuseStep 1205003 = 1807505) B1807505
theorem B1205015 : Blo 1204419 1205015 := bstep (se 1 (by rfl) ⟨903761, by rfl⟩ : syracuseStep 1205015 = 1807523) B1807523
theorem B1205035 : Blo 1204419 1205035 := bstep (se 1 (by rfl) ⟨903776, by rfl⟩ : syracuseStep 1205035 = 1807553) B1807553
theorem B1205047 : Blo 1204419 1205047 := bstep (se 1 (by rfl) ⟨903785, by rfl⟩ : syracuseStep 1205047 = 1807571) B1807571
theorem B1205067 : Blo 1204419 1205067 := bstep (se 1 (by rfl) ⟨903800, by rfl⟩ : syracuseStep 1205067 = 1807601) B1807601
theorem B4580171 : Blo 1204419 4580171 := bstep (se 1 (by rfl) ⟨3435128, by rfl⟩ : syracuseStep 4580171 = 6870257) B6870257
theorem B1205079 : Blo 1204419 1205079 := bstep (se 1 (by rfl) ⟨903809, by rfl⟩ : syracuseStep 1205079 = 1807619) B1807619
theorem B4580185 : Blo 1204419 4580185 := bstep (se 2 (by rfl) ⟨1717569, by rfl⟩ : syracuseStep 4580185 = 3435139) B3435139
theorem B1205099 : Blo 1204419 1205099 := bstep (se 1 (by rfl) ⟨903824, by rfl⟩ : syracuseStep 1205099 = 1807649) B1807649
theorem B1205111 : Blo 1204419 1205111 := bstep (se 1 (by rfl) ⟨903833, by rfl⟩ : syracuseStep 1205111 = 1807667) B1807667
theorem B1205131 : Blo 1204419 1205131 := bstep (se 1 (by rfl) ⟨903848, by rfl⟩ : syracuseStep 1205131 = 1807697) B1807697
theorem B1221527 : Blo 1204419 1221527 := bstep (se 1 (by rfl) ⟨916145, by rfl⟩ : syracuseStep 1221527 = 1832291) B1832291
theorem B1205143 : Blo 1204419 1205143 := bstep (se 1 (by rfl) ⟨903857, by rfl⟩ : syracuseStep 1205143 = 1807715) B1807715
theorem B2712473 : Blo 1204419 2712473 := bstep (se 2 (by rfl) ⟨1017177, by rfl⟩ : syracuseStep 2712473 = 2034355) B2034355
theorem B1205163 : Blo 1204419 1205163 := bstep (se 1 (by rfl) ⟨903872, by rfl⟩ : syracuseStep 1205163 = 1807745) B1807745
theorem B1205175 : Blo 1204419 1205175 := bstep (se 1 (by rfl) ⟨903881, by rfl⟩ : syracuseStep 1205175 = 1807763) B1807763
theorem B2286539 : Blo 1204419 2286539 := bstep (se 1 (by rfl) ⟨1714904, by rfl⟩ : syracuseStep 2286539 = 3429809) B3429809
theorem B1524683 : Blo 1204419 1524683 := bstep (se 1 (by rfl) ⟨1143512, by rfl⟩ : syracuseStep 1524683 = 2287025) B2287025
theorem B1205195 : Blo 1204419 1205195 := bstep (se 1 (by rfl) ⟨903896, by rfl⟩ : syracuseStep 1205195 = 1807793) B1807793
theorem B1205207 : Blo 1204419 1205207 := bstep (se 1 (by rfl) ⟨903905, by rfl⟩ : syracuseStep 1205207 = 1807811) B1807811
theorem B1287127 : Blo 1204419 1287127 := bstep (se 1 (by rfl) ⟨965345, by rfl⟩ : syracuseStep 1287127 = 1930691) B1930691
theorem B9159641 : Blo 1204419 9159641 := bstep (se 2 (by rfl) ⟨3434865, by rfl⟩ : syracuseStep 9159641 = 6869731) B6869731
theorem B1205227 : Blo 1204419 1205227 := bstep (se 1 (by rfl) ⟨903920, by rfl⟩ : syracuseStep 1205227 = 1807841) B1807841
theorem B2712563 : Blo 1204419 2712563 := bstep (se 1 (by rfl) ⟨2034422, by rfl⟩ : syracuseStep 2712563 = 4068845) B4068845
theorem B1205239 : Blo 1204419 1205239 := bstep (se 1 (by rfl) ⟨903929, by rfl⟩ : syracuseStep 1205239 = 1807859) B1807859
theorem B1205259 : Blo 1204419 1205259 := bstep (se 1 (by rfl) ⟨903944, by rfl⟩ : syracuseStep 1205259 = 1807889) B1807889
theorem B1205271 : Blo 1204419 1205271 := bstep (se 1 (by rfl) ⟨903953, by rfl⟩ : syracuseStep 1205271 = 1807907) B1807907
theorem B2712599 : Blo 1204419 2712599 := bstep (se 1 (by rfl) ⟨2034449, by rfl⟩ : syracuseStep 2712599 = 4068899) B4068899
theorem B1205291 : Blo 1204419 1205291 := bstep (se 1 (by rfl) ⟨903968, by rfl⟩ : syracuseStep 1205291 = 1807937) B1807937
theorem B1205303 : Blo 1204419 1205303 := bstep (se 1 (by rfl) ⟨903977, by rfl⟩ : syracuseStep 1205303 = 1807955) B1807955
theorem B2032715 : Blo 1204419 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B4342859 : Blo 1204419 4342859 := bstep (se 1 (by rfl) ⟨3257144, by rfl⟩ : syracuseStep 4342859 = 6514289) B6514289
theorem B1205323 : Blo 1204419 1205323 := bstep (se 1 (by rfl) ⟨903992, by rfl⟩ : syracuseStep 1205323 = 1807985) B1807985
theorem B1205335 : Blo 1204419 1205335 := bstep (se 1 (by rfl) ⟨904001, by rfl⟩ : syracuseStep 1205335 = 1808003) B1808003
theorem B10183781 : Blo 1204419 10183781 := bstep (se 4 (by rfl) ⟨954729, by rfl⟩ : syracuseStep 10183781 = 1909459) B1909459
theorem B1205355 : Blo 1204419 1205355 := bstep (se 1 (by rfl) ⟨904016, by rfl⟩ : syracuseStep 1205355 = 1808033) B1808033
theorem B1205367 : Blo 1204419 1205367 := bstep (se 1 (by rfl) ⟨904025, by rfl⟩ : syracuseStep 1205367 = 1808051) B1808051
theorem B2286721 : Blo 1204419 2286721 := bstep (se 2 (by rfl) ⟨857520, by rfl⟩ : syracuseStep 2286721 = 1715041) B1715041
theorem B1205387 : Blo 1204419 1205387 := bstep (se 1 (by rfl) ⟨904040, by rfl⟩ : syracuseStep 1205387 = 1808081) B1808081
theorem B1205399 : Blo 1204419 1205399 := bstep (se 1 (by rfl) ⟨904049, by rfl⟩ : syracuseStep 1205399 = 1808099) B1808099
theorem B1205419 : Blo 1204419 1205419 := bstep (se 1 (by rfl) ⟨904064, by rfl⟩ : syracuseStep 1205419 = 1808129) B1808129
theorem B1205431 : Blo 1204419 1205431 := bstep (se 1 (by rfl) ⟨904073, by rfl⟩ : syracuseStep 1205431 = 1808147) B1808147
theorem B2319553 : Blo 1204419 2319553 := bstep (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) B1739665
theorem B2032843 : Blo 1204419 2032843 := bstep (se 1 (by rfl) ⟨1524632, by rfl⟩ : syracuseStep 2032843 = 3049265) B3049265
theorem B1205451 : Blo 1204419 1205451 := bstep (se 1 (by rfl) ⟨904088, by rfl⟩ : syracuseStep 1205451 = 1808177) B1808177
theorem B2712779 : Blo 1204419 2712779 := bstep (se 1 (by rfl) ⟨2034584, by rfl⟩ : syracuseStep 2712779 = 4069169) B4069169
theorem B1205463 : Blo 1204419 1205463 := bstep (se 1 (by rfl) ⟨904097, by rfl⟩ : syracuseStep 1205463 = 1808195) B1808195
theorem B5219549 : Blo 1204419 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B1205483 : Blo 1204419 1205483 := bstep (se 1 (by rfl) ⟨904112, by rfl⟩ : syracuseStep 1205483 = 1808225) B1808225
theorem B1205495 : Blo 1204419 1205495 := bstep (se 1 (by rfl) ⟨904121, by rfl⟩ : syracuseStep 1205495 = 1808243) B1808243
theorem B2712833 : Blo 1204419 2712833 := bstep (se 2 (by rfl) ⟨1017312, by rfl⟩ : syracuseStep 2712833 = 2034625) B2034625
theorem B1205515 : Blo 1204419 1205515 := bstep (se 1 (by rfl) ⟨904136, by rfl⟩ : syracuseStep 1205515 = 1808273) B1808273
theorem B1205527 : Blo 1204419 1205527 := bstep (se 1 (by rfl) ⟨904145, by rfl⟩ : syracuseStep 1205527 = 1808291) B1808291
theorem B2172185 : Blo 1204419 2172185 := bstep (se 2 (by rfl) ⟨814569, by rfl⟩ : syracuseStep 2172185 = 1629139) B1629139
theorem B1205547 : Blo 1204419 1205547 := bstep (se 1 (by rfl) ⟨904160, by rfl⟩ : syracuseStep 1205547 = 1808321) B1808321
theorem B1205559 : Blo 1204419 1205559 := bstep (se 1 (by rfl) ⟨904169, by rfl⟩ : syracuseStep 1205559 = 1808339) B1808339
theorem B3048779 : Blo 1204419 3048779 := bstep (se 1 (by rfl) ⟨2286584, by rfl⟩ : syracuseStep 3048779 = 4573169) B4573169
theorem B1205579 : Blo 1204419 1205579 := bstep (se 1 (by rfl) ⟨904184, by rfl⟩ : syracuseStep 1205579 = 1808369) B1808369
theorem B1205591 : Blo 1204419 1205591 := bstep (se 1 (by rfl) ⟨904193, by rfl⟩ : syracuseStep 1205591 = 1808387) B1808387
theorem B2032985 : Blo 1204419 2032985 := bstep (se 2 (by rfl) ⟨762369, by rfl⟩ : syracuseStep 2032985 = 1524739) B1524739
theorem B3859805 : Blo 1204419 3859805 := bstep (se 3 (by rfl) ⟨723713, by rfl⟩ : syracuseStep 3859805 = 1447427) B1447427
theorem B1205611 : Blo 1204419 1205611 := bstep (se 1 (by rfl) ⟨904208, by rfl⟩ : syracuseStep 1205611 = 1808417) B1808417
theorem B1205623 : Blo 1204419 1205623 := bstep (se 1 (by rfl) ⟨904217, by rfl⟩ : syracuseStep 1205623 = 1808435) B1808435
theorem B2573707 : Blo 1204419 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B1205643 : Blo 1204419 1205643 := bstep (se 1 (by rfl) ⟨904232, by rfl⟩ : syracuseStep 1205643 = 1808465) B1808465
theorem B1205655 : Blo 1204419 1205655 := bstep (se 1 (by rfl) ⟨904241, by rfl⟩ : syracuseStep 1205655 = 1808483) B1808483
theorem B2319769 : Blo 1204419 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B1205675 : Blo 1204419 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B1205687 : Blo 1204419 1205687 := bstep (se 1 (by rfl) ⟨904265, by rfl⟩ : syracuseStep 1205687 = 1808531) B1808531
theorem B1205707 : Blo 1204419 1205707 := bstep (se 1 (by rfl) ⟨904280, by rfl⟩ : syracuseStep 1205707 = 1808561) B1808561
theorem B1205719 : Blo 1204419 1205719 := bstep (se 1 (by rfl) ⟨904289, by rfl⟩ : syracuseStep 1205719 = 1808579) B1808579
theorem B2033113 : Blo 1204419 2033113 := bstep (se 2 (by rfl) ⟨762417, by rfl⟩ : syracuseStep 2033113 = 1524835) B1524835
theorem B2713049 : Blo 1204419 2713049 := bstep (se 2 (by rfl) ⟨1017393, by rfl⟩ : syracuseStep 2713049 = 2034787) B2034787
theorem B1205739 : Blo 1204419 1205739 := bstep (se 1 (by rfl) ⟨904304, by rfl⟩ : syracuseStep 1205739 = 1808609) B1808609
theorem B1205751 : Blo 1204419 1205751 := bstep (se 1 (by rfl) ⟨904313, by rfl⟩ : syracuseStep 1205751 = 1808627) B1808627
theorem B1205771 : Blo 1204419 1205771 := bstep (se 1 (by rfl) ⟨904328, by rfl⟩ : syracuseStep 1205771 = 1808657) B1808657
theorem B1205783 : Blo 1204419 1205783 := bstep (se 1 (by rfl) ⟨904337, by rfl⟩ : syracuseStep 1205783 = 1808675) B1808675
theorem B1205803 : Blo 1204419 1205803 := bstep (se 1 (by rfl) ⟨904352, by rfl⟩ : syracuseStep 1205803 = 1808705) B1808705
theorem B2713139 : Blo 1204419 2713139 := bstep (se 1 (by rfl) ⟨2034854, by rfl⟩ : syracuseStep 2713139 = 4069709) B4069709
theorem B3434035 : Blo 1204419 3434035 := bstep (se 1 (by rfl) ⟨2575526, by rfl⟩ : syracuseStep 3434035 = 5151053) B5151053
theorem B1205815 : Blo 1204419 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B1205835 : Blo 1204419 1205835 := bstep (se 1 (by rfl) ⟨904376, by rfl⟩ : syracuseStep 1205835 = 1808753) B1808753
theorem B1205847 : Blo 1204419 1205847 := bstep (se 1 (by rfl) ⟨904385, by rfl⟩ : syracuseStep 1205847 = 1808771) B1808771
theorem B2713175 : Blo 1204419 2713175 := bstep (se 1 (by rfl) ⟨2034881, by rfl⟩ : syracuseStep 2713175 = 4069763) B4069763
theorem B1205867 : Blo 1204419 1205867 := bstep (se 1 (by rfl) ⟨904400, by rfl⟩ : syracuseStep 1205867 = 1808801) B1808801
theorem B1205879 : Blo 1204419 1205879 := bstep (se 1 (by rfl) ⟨904409, by rfl⟩ : syracuseStep 1205879 = 1808819) B1808819
theorem B1525387 : Blo 1204419 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B1205899 : Blo 1204419 1205899 := bstep (se 1 (by rfl) ⟨904424, by rfl⟩ : syracuseStep 1205899 = 1808849) B1808849
theorem B1205911 : Blo 1204419 1205911 := bstep (se 1 (by rfl) ⟨904433, by rfl⟩ : syracuseStep 1205911 = 1808867) B1808867
theorem B1205931 : Blo 1204419 1205931 := bstep (se 1 (by rfl) ⟨904448, by rfl⟩ : syracuseStep 1205931 = 1808897) B1808897
theorem B1205943 : Blo 1204419 1205943 := bstep (se 1 (by rfl) ⟨904457, by rfl⟩ : syracuseStep 1205943 = 1808915) B1808915
theorem B1205963 : Blo 1204419 1205963 := bstep (se 1 (by rfl) ⟨904472, by rfl⟩ : syracuseStep 1205963 = 1808945) B1808945
theorem B1205975 : Blo 1204419 1205975 := bstep (se 1 (by rfl) ⟨904481, by rfl⟩ : syracuseStep 1205975 = 1808963) B1808963
theorem B1205995 : Blo 1204419 1205995 := bstep (se 1 (by rfl) ⟨904496, by rfl⟩ : syracuseStep 1205995 = 1808993) B1808993
theorem B1206007 : Blo 1204419 1206007 := bstep (se 1 (by rfl) ⟨904505, by rfl⟩ : syracuseStep 1206007 = 1809011) B1809011
theorem B2713355 : Blo 1204419 2713355 := bstep (se 1 (by rfl) ⟨2035016, by rfl⟩ : syracuseStep 2713355 = 4070033) B4070033
theorem B1206027 : Blo 1204419 1206027 := bstep (se 1 (by rfl) ⟨904520, by rfl⟩ : syracuseStep 1206027 = 1809041) B1809041
theorem B1287947 : Blo 1204419 1287947 := bstep (se 1 (by rfl) ⟨965960, by rfl⟩ : syracuseStep 1287947 = 1931921) B1931921
theorem B1206039 : Blo 1204419 1206039 := bstep (se 1 (by rfl) ⟨904529, by rfl⟩ : syracuseStep 1206039 = 1809059) B1809059
theorem B1206059 : Blo 1204419 1206059 := bstep (se 1 (by rfl) ⟨904544, by rfl⟩ : syracuseStep 1206059 = 1809089) B1809089
theorem B1206071 : Blo 1204419 1206071 := bstep (se 1 (by rfl) ⟨904553, by rfl⟩ : syracuseStep 1206071 = 1809107) B1809107
theorem B2713409 : Blo 1204419 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B7726913 : Blo 1204419 7726913 := bstep (se 2 (by rfl) ⟨2897592, by rfl⟩ : syracuseStep 7726913 = 5795185) B5795185
theorem B2287435 : Blo 1204419 2287435 := bstep (se 1 (by rfl) ⟨1715576, by rfl⟩ : syracuseStep 2287435 = 3431153) B3431153
theorem B1206091 : Blo 1204419 1206091 := bstep (se 1 (by rfl) ⟨904568, by rfl⟩ : syracuseStep 1206091 = 1809137) B1809137
theorem B1206103 : Blo 1204419 1206103 := bstep (se 1 (by rfl) ⟨904577, by rfl⟩ : syracuseStep 1206103 = 1809155) B1809155
theorem B1206123 : Blo 1204419 1206123 := bstep (se 1 (by rfl) ⟨904592, by rfl⟩ : syracuseStep 1206123 = 1809185) B1809185
theorem B1206135 : Blo 1204419 1206135 := bstep (se 1 (by rfl) ⟨904601, by rfl⟩ : syracuseStep 1206135 = 1809203) B1809203
theorem B1206155 : Blo 1204419 1206155 := bstep (se 1 (by rfl) ⟨904616, by rfl⟩ : syracuseStep 1206155 = 1809233) B1809233
theorem B2287511 : Blo 1204419 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B1525655 : Blo 1204419 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B1206167 : Blo 1204419 1206167 := bstep (se 1 (by rfl) ⟨904625, by rfl⟩ : syracuseStep 1206167 = 1809251) B1809251
theorem B1206187 : Blo 1204419 1206187 := bstep (se 1 (by rfl) ⟨904640, by rfl⟩ : syracuseStep 1206187 = 1809281) B1809281
theorem B21981107 : Blo 1204419 21981107 := bstep (se 1 (by rfl) ⟨16485830, by rfl⟩ : syracuseStep 21981107 = 32971661) B32971661
theorem B1206199 : Blo 1204419 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B4065227 : Blo 1204419 4065227 := bstep (se 1 (by rfl) ⟨3048920, by rfl⟩ : syracuseStep 4065227 = 6097841) B6097841
theorem B1206219 : Blo 1204419 1206219 := bstep (se 1 (by rfl) ⟨904664, by rfl⟩ : syracuseStep 1206219 = 1809329) B1809329
theorem B1206231 : Blo 1204419 1206231 := bstep (se 1 (by rfl) ⟨904673, by rfl⟩ : syracuseStep 1206231 = 1809347) B1809347
theorem B1206251 : Blo 1204419 1206251 := bstep (se 1 (by rfl) ⟨904688, by rfl⟩ : syracuseStep 1206251 = 1809377) B1809377
theorem B1206263 : Blo 1204419 1206263 := bstep (se 1 (by rfl) ⟨904697, by rfl⟩ : syracuseStep 1206263 = 1809395) B1809395
theorem B2353153 : Blo 1204419 2353153 := bstep (se 2 (by rfl) ⟨882432, by rfl⟩ : syracuseStep 2353153 = 1764865) B1764865
theorem B1206283 : Blo 1204419 1206283 := bstep (se 1 (by rfl) ⟨904712, by rfl⟩ : syracuseStep 1206283 = 1809425) B1809425
theorem B2033687 : Blo 1204419 2033687 := bstep (se 1 (by rfl) ⟨1525265, by rfl⟩ : syracuseStep 2033687 = 3050531) B3050531
theorem B1206295 : Blo 1204419 1206295 := bstep (se 1 (by rfl) ⟨904721, by rfl⟩ : syracuseStep 1206295 = 1809443) B1809443
theorem B2713625 : Blo 1204419 2713625 := bstep (se 2 (by rfl) ⟨1017609, by rfl⟩ : syracuseStep 2713625 = 2035219) B2035219
theorem B1206315 : Blo 1204419 1206315 := bstep (se 1 (by rfl) ⟨904736, by rfl⟩ : syracuseStep 1206315 = 1809473) B1809473
theorem B1206327 : Blo 1204419 1206327 := bstep (se 1 (by rfl) ⟨904745, by rfl⟩ : syracuseStep 1206327 = 1809491) B1809491
theorem B29321291 : Blo 1204419 29321291 := bstep (se 1 (by rfl) ⟨21990968, by rfl⟩ : syracuseStep 29321291 = 43981937) B43981937
theorem B1206347 : Blo 1204419 1206347 := bstep (se 1 (by rfl) ⟨904760, by rfl⟩ : syracuseStep 1206347 = 1809521) B1809521
theorem B1206359 : Blo 1204419 1206359 := bstep (se 1 (by rfl) ⟨904769, by rfl⟩ : syracuseStep 1206359 = 1809539) B1809539
theorem B1206379 : Blo 1204419 1206379 := bstep (se 1 (by rfl) ⟨904784, by rfl⟩ : syracuseStep 1206379 = 1809569) B1809569
theorem B2713715 : Blo 1204419 2713715 := bstep (se 1 (by rfl) ⟨2035286, by rfl⟩ : syracuseStep 2713715 = 4070573) B4070573
theorem B1206391 : Blo 1204419 1206391 := bstep (se 1 (by rfl) ⟨904793, by rfl⟩ : syracuseStep 1206391 = 1809587) B1809587
theorem B1222795 : Blo 1204419 1222795 := bstep (se 1 (by rfl) ⟨917096, by rfl⟩ : syracuseStep 1222795 = 1834193) B1834193
theorem B1206411 : Blo 1204419 1206411 := bstep (se 1 (by rfl) ⟨904808, by rfl⟩ : syracuseStep 1206411 = 1809617) B1809617
theorem B2033815 : Blo 1204419 2033815 := bstep (se 1 (by rfl) ⟨1525361, by rfl⟩ : syracuseStep 2033815 = 3050723) B3050723
theorem B2713751 : Blo 1204419 2713751 := bstep (se 1 (by rfl) ⟨2035313, by rfl⟩ : syracuseStep 2713751 = 4070627) B4070627
theorem B4065497 : Blo 1204419 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B3049751 : Blo 1204419 3049751 := bstep (se 1 (by rfl) ⟨2287313, by rfl⟩ : syracuseStep 3049751 = 4574627) B4574627
theorem B2713931 : Blo 1204419 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B46999921 : Blo 1204419 46999921 := bstep (se 2 (by rfl) ⟨17624970, by rfl⟩ : syracuseStep 46999921 = 35249941) B35249941
theorem B2713985 : Blo 1204419 2713985 := bstep (se 2 (by rfl) ⟨1017744, by rfl⟩ : syracuseStep 2713985 = 2035489) B2035489
theorem B4884887 : Blo 1204419 4884887 := bstep (se 1 (by rfl) ⟨3663665, by rfl⟩ : syracuseStep 4884887 = 7327331) B7327331
theorem B5876185 : Blo 1204419 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B6105617 : Blo 1204419 6105617 := bstep (se 2 (by rfl) ⟨2289606, by rfl⟩ : syracuseStep 6105617 = 4579213) B4579213
theorem B2288179 : Blo 1204419 2288179 := bstep (se 1 (by rfl) ⟨1716134, by rfl⟩ : syracuseStep 2288179 = 3432269) B3432269
theorem B2894401 : Blo 1204419 2894401 := bstep (se 2 (by rfl) ⟨1085400, by rfl⟩ : syracuseStep 2894401 = 2170801) B2170801
theorem B1526359 : Blo 1204419 1526359 := bstep (se 1 (by rfl) ⟨1144769, by rfl⟩ : syracuseStep 1526359 = 2289539) B2289539
theorem B2714201 : Blo 1204419 2714201 := bstep (se 2 (by rfl) ⟨1017825, by rfl⟩ : syracuseStep 2714201 = 2035651) B2035651
theorem B11586179 : Blo 1204419 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B6105779 : Blo 1204419 6105779 := bstep (se 1 (by rfl) ⟨4579334, by rfl⟩ : syracuseStep 6105779 = 9158669) B9158669
theorem B2714291 : Blo 1204419 2714291 := bstep (se 1 (by rfl) ⟨2035718, by rfl⟩ : syracuseStep 2714291 = 4071437) B4071437
theorem B2714327 : Blo 1204419 2714327 := bstep (se 1 (by rfl) ⟨2035745, by rfl⟩ : syracuseStep 2714327 = 4071491) B4071491
theorem B2575091 : Blo 1204419 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B2444033 : Blo 1204419 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B2034443 : Blo 1204419 2034443 := bstep (se 1 (by rfl) ⟨1525832, by rfl⟩ : syracuseStep 2034443 = 3051665) B3051665
theorem B2288407 : Blo 1204419 2288407 := bstep (se 1 (by rfl) ⟨1716305, by rfl⟩ : syracuseStep 2288407 = 3432611) B3432611
theorem B2747201 : Blo 1204419 2747201 := bstep (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) B2060401
theorem B2288513 : Blo 1204419 2288513 := bstep (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) B1716385
theorem B2034571 : Blo 1204419 2034571 := bstep (se 1 (by rfl) ⟨1525928, by rfl⟩ : syracuseStep 2034571 = 3051857) B3051857
theorem B4066199 : Blo 1204419 4066199 := bstep (se 1 (by rfl) ⟨3049649, by rfl⟩ : syracuseStep 4066199 = 6099299) B6099299
theorem B3050419 : Blo 1204419 3050419 := bstep (se 1 (by rfl) ⟨2287814, by rfl⟩ : syracuseStep 3050419 = 4575629) B4575629
theorem B20605913 : Blo 1204419 20605913 := bstep (se 2 (by rfl) ⟨7727217, by rfl⟩ : syracuseStep 20605913 = 15454435) B15454435
theorem B5147651 : Blo 1204419 5147651 := bstep (se 1 (by rfl) ⟨3860738, by rfl⟩ : syracuseStep 5147651 = 7721477) B7721477
theorem B2288665 : Blo 1204419 2288665 := bstep (se 2 (by rfl) ⟨858249, by rfl⟩ : syracuseStep 2288665 = 1716499) B1716499
theorem B2034713 : Blo 1204419 2034713 := bstep (se 2 (by rfl) ⟨763017, by rfl⟩ : syracuseStep 2034713 = 1526035) B1526035
theorem B3050561 : Blo 1204419 3050561 := bstep (se 2 (by rfl) ⟨1143960, by rfl⟩ : syracuseStep 3050561 = 2287921) B2287921
theorem B19557445 : Blo 1204419 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B4574339 : Blo 1204419 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B4574353 : Blo 1204419 4574353 := bstep (se 2 (by rfl) ⟨1715382, by rfl⟩ : syracuseStep 4574353 = 3430765) B3430765
theorem B4344977 : Blo 1204419 4344977 := bstep (se 2 (by rfl) ⟨1629366, by rfl⟩ : syracuseStep 4344977 = 3258733) B3258733
theorem B2034841 : Blo 1204419 2034841 := bstep (se 2 (by rfl) ⟨763065, by rfl⟩ : syracuseStep 2034841 = 1526131) B1526131
theorem B1354999 : Blo 1204419 1354999 := bstep (se 1 (by rfl) ⟨1016249, by rfl⟩ : syracuseStep 1354999 = 2032499) B2032499
theorem B4345091 : Blo 1204419 4345091 := bstep (se 1 (by rfl) ⟨3258818, by rfl⟩ : syracuseStep 4345091 = 6517637) B6517637
theorem B9153809 : Blo 1204419 9153809 := bstep (se 2 (by rfl) ⟨3432678, by rfl⟩ : syracuseStep 9153809 = 6865357) B6865357
theorem B4345177 : Blo 1204419 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B6098327 : Blo 1204419 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B1355179 : Blo 1204419 1355179 := bstep (se 1 (by rfl) ⟨1016384, by rfl⟩ : syracuseStep 1355179 = 2032769) B2032769
theorem B4066739 : Blo 1204419 4066739 := bstep (se 1 (by rfl) ⟨3050054, by rfl⟩ : syracuseStep 4066739 = 6100109) B6100109
theorem B4574657 : Blo 1204419 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B2117081 : Blo 1204419 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B1355287 : Blo 1204419 1355287 := bstep (se 1 (by rfl) ⟨1016465, by rfl⟩ : syracuseStep 1355287 = 2032931) B2032931
theorem B2575937 : Blo 1204419 2575937 := bstep (se 2 (by rfl) ⟨965976, by rfl⟩ : syracuseStep 2575937 = 1931953) B1931953
theorem B4067009 : Blo 1204419 4067009 := bstep (se 2 (by rfl) ⟨1525128, by rfl⟩ : syracuseStep 4067009 = 3050257) B3050257
theorem B1355467 : Blo 1204419 1355467 := bstep (se 1 (by rfl) ⟨1016600, by rfl⟩ : syracuseStep 1355467 = 2033201) B2033201
theorem B2035415 : Blo 1204419 2035415 := bstep (se 1 (by rfl) ⟨1526561, by rfl⟩ : syracuseStep 2035415 = 3053123) B3053123
theorem B1355575 : Blo 1204419 1355575 := bstep (se 1 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 1355575 = 2033363) B2033363
theorem B2035543 : Blo 1204419 2035543 := bstep (se 1 (by rfl) ⟨1526657, by rfl⟩ : syracuseStep 2035543 = 3053315) B3053315
theorem B2576279 : Blo 1204419 2576279 := bstep (se 1 (by rfl) ⟨1932209, by rfl⟩ : syracuseStep 2576279 = 3864419) B3864419
theorem B1355755 : Blo 1204419 1355755 := bstep (se 1 (by rfl) ⟨1016816, by rfl⟩ : syracuseStep 1355755 = 2033633) B2033633
theorem B1355863 : Blo 1204419 1355863 := bstep (se 1 (by rfl) ⟨1016897, by rfl⟩ : syracuseStep 1355863 = 2033795) B2033795
theorem B4575325 : Blo 1204419 4575325 := bstep (se 3 (by rfl) ⟨857873, by rfl⟩ : syracuseStep 4575325 = 1715747) B1715747
theorem B9146519 : Blo 1204419 9146519 := bstep (se 1 (by rfl) ⟨6859889, by rfl⟩ : syracuseStep 9146519 = 13719779) B13719779
theorem B1486999 : Blo 1204419 1486999 := bstep (se 1 (by rfl) ⟨1115249, by rfl⟩ : syracuseStep 1486999 = 2230499) B2230499
theorem B4067549 : Blo 1204419 4067549 := bstep (se 3 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 4067549 = 1525331) B1525331
theorem B1356043 : Blo 1204419 1356043 := bstep (se 1 (by rfl) ⟨1017032, by rfl⟩ : syracuseStep 1356043 = 2034065) B2034065
theorem B50172205 : Blo 1204419 50172205 := bstep (se 3 (by rfl) ⟨9407288, by rfl⟩ : syracuseStep 50172205 = 18814577) B18814577
theorem B3051827 : Blo 1204419 3051827 := bstep (se 1 (by rfl) ⟨2288870, by rfl⟩ : syracuseStep 3051827 = 4577741) B4577741
theorem B2289971 : Blo 1204419 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B1356151 : Blo 1204419 1356151 := bstep (se 1 (by rfl) ⟨1017113, by rfl⟩ : syracuseStep 1356151 = 2034227) B2034227
theorem B1806731 : Blo 1204419 1806731 := bstep (se 1 (by rfl) ⟨1355048, by rfl⟩ : syracuseStep 1806731 = 2710097) B2710097
theorem B1806743 : Blo 1204419 1806743 := bstep (se 1 (by rfl) ⟨1355057, by rfl⟩ : syracuseStep 1806743 = 2710115) B2710115
theorem B2445719 : Blo 1204419 2445719 := bstep (se 1 (by rfl) ⟨1834289, by rfl⟩ : syracuseStep 2445719 = 3668579) B3668579
theorem B2290123 : Blo 1204419 2290123 := bstep (se 1 (by rfl) ⟨1717592, by rfl⟩ : syracuseStep 2290123 = 3435185) B3435185
theorem B1806809 : Blo 1204419 1806809 := bstep (se 2 (by rfl) ⟨677553, by rfl⟩ : syracuseStep 1806809 = 1355107) B1355107
theorem B1716761 : Blo 1204419 1716761 := bstep (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) B1287571
theorem B1356331 : Blo 1204419 1356331 := bstep (se 1 (by rfl) ⟨1017248, by rfl⟩ : syracuseStep 1356331 = 2034497) B2034497
theorem B6869549 : Blo 1204419 6869549 := bstep (se 3 (by rfl) ⟨1288040, by rfl⟩ : syracuseStep 6869549 = 2576081) B2576081
theorem B1806923 : Blo 1204419 1806923 := bstep (se 1 (by rfl) ⟨1355192, by rfl⟩ : syracuseStep 1806923 = 2710385) B2710385
theorem B1806935 : Blo 1204419 1806935 := bstep (se 1 (by rfl) ⟨1355201, by rfl⟩ : syracuseStep 1806935 = 2710403) B2710403
theorem B5149277 : Blo 1204419 5149277 := bstep (se 3 (by rfl) ⟨965489, by rfl⟩ : syracuseStep 5149277 = 1930979) B1930979
theorem B1356439 : Blo 1204419 1356439 := bstep (se 1 (by rfl) ⟨1017329, by rfl⟩ : syracuseStep 1356439 = 2034659) B2034659
theorem B1807001 : Blo 1204419 1807001 := bstep (se 2 (by rfl) ⟨677625, by rfl⟩ : syracuseStep 1807001 = 1355251) B1355251
theorem B18551501 : Blo 1204419 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B1807115 : Blo 1204419 1807115 := bstep (se 1 (by rfl) ⟨1355336, by rfl⟩ : syracuseStep 1807115 = 2710673) B2710673
theorem B1807127 : Blo 1204419 1807127 := bstep (se 1 (by rfl) ⟨1355345, by rfl⟩ : syracuseStep 1807127 = 2710691) B2710691
theorem B8926027 : Blo 1204419 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B3052363 : Blo 1204419 3052363 := bstep (se 1 (by rfl) ⟨2289272, by rfl⟩ : syracuseStep 3052363 = 4578545) B4578545
theorem B1356619 : Blo 1204419 1356619 := bstep (se 1 (by rfl) ⟨1017464, by rfl⟩ : syracuseStep 1356619 = 2034929) B2034929
theorem B1807193 : Blo 1204419 1807193 := bstep (se 2 (by rfl) ⟨677697, by rfl⟩ : syracuseStep 1807193 = 1355395) B1355395
theorem B1356727 : Blo 1204419 1356727 := bstep (se 1 (by rfl) ⟨1017545, by rfl⟩ : syracuseStep 1356727 = 2035091) B2035091
theorem B1807307 : Blo 1204419 1807307 := bstep (se 1 (by rfl) ⟨1355480, by rfl⟩ : syracuseStep 1807307 = 2710961) B2710961
theorem B1807319 : Blo 1204419 1807319 := bstep (se 1 (by rfl) ⟨1355489, by rfl⟩ : syracuseStep 1807319 = 2710979) B2710979
theorem B2200537 : Blo 1204419 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B3052505 : Blo 1204419 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B41735189 : Blo 1204419 41735189 := bstep (se 6 (by rfl) ⟨978168, by rfl⟩ : syracuseStep 41735189 = 1956337) B1956337
theorem B1807385 : Blo 1204419 1807385 := bstep (se 2 (by rfl) ⟨677769, by rfl⟩ : syracuseStep 1807385 = 1355539) B1355539
theorem B1356907 : Blo 1204419 1356907 := bstep (se 1 (by rfl) ⟨1017680, by rfl⟩ : syracuseStep 1356907 = 2035361) B2035361
theorem B1807499 : Blo 1204419 1807499 := bstep (se 1 (by rfl) ⟨1355624, by rfl⟩ : syracuseStep 1807499 = 2711249) B2711249
theorem B1807511 : Blo 1204419 1807511 := bstep (se 1 (by rfl) ⟨1355633, by rfl⟩ : syracuseStep 1807511 = 2711267) B2711267
theorem B1717399 : Blo 1204419 1717399 := bstep (se 1 (by rfl) ⟨1288049, by rfl⟩ : syracuseStep 1717399 = 2576099) B2576099
theorem B10294451 : Blo 1204419 10294451 := bstep (se 1 (by rfl) ⟨7720838, by rfl⟩ : syracuseStep 10294451 = 15441677) B15441677
theorem B20092085 : Blo 1204419 20092085 := bstep (se 5 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 20092085 = 1883633) B1883633
theorem B1357015 : Blo 1204419 1357015 := bstep (se 1 (by rfl) ⟨1017761, by rfl⟩ : syracuseStep 1357015 = 2035523) B2035523
theorem B1807577 : Blo 1204419 1807577 := bstep (se 2 (by rfl) ⟨677841, by rfl⟩ : syracuseStep 1807577 = 1355683) B1355683
theorem B5149975 : Blo 1204419 5149975 := bstep (se 1 (by rfl) ⟨3862481, by rfl⟩ : syracuseStep 5149975 = 7724963) B7724963
theorem B1807691 : Blo 1204419 1807691 := bstep (se 1 (by rfl) ⟨1355768, by rfl⟩ : syracuseStep 1807691 = 2711537) B2711537
theorem B4068683 : Blo 1204419 4068683 := bstep (se 1 (by rfl) ⟨3051512, by rfl⟩ : syracuseStep 4068683 = 6103025) B6103025
theorem B1807703 : Blo 1204419 1807703 := bstep (se 1 (by rfl) ⟨1355777, by rfl⟩ : syracuseStep 1807703 = 2711555) B2711555
theorem B4576601 : Blo 1204419 4576601 := bstep (se 2 (by rfl) ⟨1716225, by rfl⟩ : syracuseStep 4576601 = 3432451) B3432451
theorem B10302821 : Blo 1204419 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B1357195 : Blo 1204419 1357195 := bstep (se 1 (by rfl) ⟨1017896, by rfl⟩ : syracuseStep 1357195 = 2035793) B2035793
theorem B1807769 : Blo 1204419 1807769 := bstep (se 2 (by rfl) ⟨677913, by rfl⟩ : syracuseStep 1807769 = 1355827) B1355827
theorem B1373611 : Blo 1204419 1373611 := bstep (se 1 (by rfl) ⟨1030208, by rfl⟩ : syracuseStep 1373611 = 2060417) B2060417
theorem B9770419 : Blo 1204419 9770419 := bstep (se 1 (by rfl) ⟨7327814, by rfl⟩ : syracuseStep 9770419 = 14655629) B14655629
theorem B6862259 : Blo 1204419 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B1373707 : Blo 1204419 1373707 := bstep (se 1 (by rfl) ⟨1030280, by rfl⟩ : syracuseStep 1373707 = 2060561) B2060561
theorem B1807883 : Blo 1204419 1807883 := bstep (se 1 (by rfl) ⟨1355912, by rfl⟩ : syracuseStep 1807883 = 2711825) B2711825
theorem B1807895 : Blo 1204419 1807895 := bstep (se 1 (by rfl) ⟨1355921, by rfl⟩ : syracuseStep 1807895 = 2711843) B2711843
theorem B1807961 : Blo 1204419 1807961 := bstep (se 2 (by rfl) ⟨677985, by rfl⟩ : syracuseStep 1807961 = 1355971) B1355971
theorem B4068953 : Blo 1204419 4068953 := bstep (se 2 (by rfl) ⟨1525857, by rfl⟩ : syracuseStep 4068953 = 3051715) B3051715
theorem B1808075 : Blo 1204419 1808075 := bstep (se 1 (by rfl) ⟨1356056, by rfl⟩ : syracuseStep 1808075 = 2712113) B2712113
theorem B1808087 : Blo 1204419 1808087 := bstep (se 1 (by rfl) ⟨1356065, by rfl⟩ : syracuseStep 1808087 = 2712131) B2712131
theorem B3053335 : Blo 1204419 3053335 := bstep (se 1 (by rfl) ⟨2290001, by rfl⟩ : syracuseStep 3053335 = 4580003) B4580003
theorem B1808153 : Blo 1204419 1808153 := bstep (se 2 (by rfl) ⟨678057, by rfl⟩ : syracuseStep 1808153 = 1356115) B1356115
theorem B3667801 : Blo 1204419 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B1808267 : Blo 1204419 1808267 := bstep (se 1 (by rfl) ⟨1356200, by rfl⟩ : syracuseStep 1808267 = 2712401) B2712401
theorem B1808279 : Blo 1204419 1808279 := bstep (se 1 (by rfl) ⟨1356209, by rfl⟩ : syracuseStep 1808279 = 2712419) B2712419
theorem B3094451 : Blo 1204419 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1808345 : Blo 1204419 1808345 := bstep (se 2 (by rfl) ⟨678129, by rfl⟩ : syracuseStep 1808345 = 1356259) B1356259
theorem B1808459 : Blo 1204419 1808459 := bstep (se 1 (by rfl) ⟨1356344, by rfl⟩ : syracuseStep 1808459 = 2712689) B2712689
theorem B1808471 : Blo 1204419 1808471 := bstep (se 1 (by rfl) ⟨1356353, by rfl⟩ : syracuseStep 1808471 = 2712707) B2712707
theorem B20592791 : Blo 1204419 20592791 := bstep (se 1 (by rfl) ⟨15444593, by rfl⟩ : syracuseStep 20592791 = 30889187) B30889187
theorem B1808537 : Blo 1204419 1808537 := bstep (se 2 (by rfl) ⟨678201, by rfl⟩ : syracuseStep 1808537 = 1356403) B1356403
theorem B15644933 : Blo 1204419 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B1808651 : Blo 1204419 1808651 := bstep (se 1 (by rfl) ⟨1356488, by rfl⟩ : syracuseStep 1808651 = 2712977) B2712977
theorem B1808663 : Blo 1204419 1808663 := bstep (se 1 (by rfl) ⟨1356497, by rfl⟩ : syracuseStep 1808663 = 2712995) B2712995
theorem B4069655 : Blo 1204419 4069655 := bstep (se 1 (by rfl) ⟨3052241, by rfl⟩ : syracuseStep 4069655 = 6104483) B6104483
theorem B1931543 : Blo 1204419 1931543 := bstep (se 1 (by rfl) ⟨1448657, by rfl⟩ : syracuseStep 1931543 = 2897315) B2897315
theorem B13031725 : Blo 1204419 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B9771329 : Blo 1204419 9771329 := bstep (se 2 (by rfl) ⟨3664248, by rfl⟩ : syracuseStep 9771329 = 7328497) B7328497
theorem B1808729 : Blo 1204419 1808729 := bstep (se 2 (by rfl) ⟨678273, by rfl⟩ : syracuseStep 1808729 = 1356547) B1356547
theorem B1374583 : Blo 1204419 1374583 := bstep (se 1 (by rfl) ⟨1030937, by rfl⟩ : syracuseStep 1374583 = 2061875) B2061875
theorem B2709953 : Blo 1204419 2709953 := bstep (se 2 (by rfl) ⟨1016232, by rfl⟩ : syracuseStep 2709953 = 2032465) B2032465
theorem B1808843 : Blo 1204419 1808843 := bstep (se 1 (by rfl) ⟨1356632, by rfl⟩ : syracuseStep 1808843 = 2713265) B2713265
theorem B1808855 : Blo 1204419 1808855 := bstep (se 1 (by rfl) ⟨1356641, by rfl⟩ : syracuseStep 1808855 = 2713283) B2713283
theorem B1808921 : Blo 1204419 1808921 := bstep (se 2 (by rfl) ⟨678345, by rfl⟩ : syracuseStep 1808921 = 1356691) B1356691
theorem B11581987 : Blo 1204419 11581987 := bstep (se 1 (by rfl) ⟨8686490, by rfl⟩ : syracuseStep 11581987 = 17372981) B17372981
theorem B2898497 : Blo 1204419 2898497 := bstep (se 2 (by rfl) ⟨1086936, by rfl⟩ : syracuseStep 2898497 = 2173873) B2173873
theorem B44022365 : Blo 1204419 44022365 := bstep (se 3 (by rfl) ⟨8254193, by rfl⟩ : syracuseStep 44022365 = 16508387) B16508387
theorem B1809035 : Blo 1204419 1809035 := bstep (se 1 (by rfl) ⟨1356776, by rfl⟩ : syracuseStep 1809035 = 2713553) B2713553
theorem B5151377 : Blo 1204419 5151377 := bstep (se 2 (by rfl) ⟨1931766, by rfl⟩ : syracuseStep 5151377 = 3863533) B3863533
theorem B1809047 : Blo 1204419 1809047 := bstep (se 1 (by rfl) ⟨1356785, by rfl⟩ : syracuseStep 1809047 = 2713571) B2713571
theorem B2710169 : Blo 1204419 2710169 := bstep (se 2 (by rfl) ⟨1016313, by rfl⟩ : syracuseStep 2710169 = 2032627) B2032627
theorem B10992307 : Blo 1204419 10992307 := bstep (se 1 (by rfl) ⟨8244230, by rfl⟩ : syracuseStep 10992307 = 16488461) B16488461
theorem B4889267 : Blo 1204419 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B1809113 : Blo 1204419 1809113 := bstep (se 2 (by rfl) ⟨678417, by rfl⟩ : syracuseStep 1809113 = 1356835) B1356835
theorem B2710259 : Blo 1204419 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B2710295 : Blo 1204419 2710295 := bstep (se 1 (by rfl) ⟨2032721, by rfl⟩ : syracuseStep 2710295 = 4065443) B4065443
theorem B3259187 : Blo 1204419 3259187 := bstep (se 1 (by rfl) ⟨2444390, by rfl⟩ : syracuseStep 3259187 = 4888781) B4888781
theorem B4070195 : Blo 1204419 4070195 := bstep (se 1 (by rfl) ⟨3052646, by rfl⟩ : syracuseStep 4070195 = 6105293) B6105293
theorem B1809227 : Blo 1204419 1809227 := bstep (se 1 (by rfl) ⟨1356920, by rfl⟩ : syracuseStep 1809227 = 2713841) B2713841
theorem B1809239 : Blo 1204419 1809239 := bstep (se 1 (by rfl) ⟨1356929, by rfl⟩ : syracuseStep 1809239 = 2713859) B2713859
theorem B6863717 : Blo 1204419 6863717 := bstep (se 4 (by rfl) ⟨643473, by rfl⟩ : syracuseStep 6863717 = 1286947) B1286947
theorem B6101891 : Blo 1204419 6101891 := bstep (se 1 (by rfl) ⟨4576418, by rfl⟩ : syracuseStep 6101891 = 9152837) B9152837
theorem B1809305 : Blo 1204419 1809305 := bstep (se 2 (by rfl) ⟨678489, by rfl⟩ : syracuseStep 1809305 = 1356979) B1356979
theorem B4578227 : Blo 1204419 4578227 := bstep (se 1 (by rfl) ⟨3433670, by rfl⟩ : syracuseStep 4578227 = 6867341) B6867341
theorem B4578241 : Blo 1204419 4578241 := bstep (se 2 (by rfl) ⟨1716840, by rfl⟩ : syracuseStep 4578241 = 3433681) B3433681
theorem B2710475 : Blo 1204419 2710475 := bstep (se 1 (by rfl) ⟨2032856, by rfl⟩ : syracuseStep 2710475 = 4065713) B4065713
theorem B1956811 : Blo 1204419 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B2710529 : Blo 1204419 2710529 := bstep (se 2 (by rfl) ⟨1016448, by rfl⟩ : syracuseStep 2710529 = 2032897) B2032897
theorem B1809419 : Blo 1204419 1809419 := bstep (se 1 (by rfl) ⟨1357064, by rfl⟩ : syracuseStep 1809419 = 2714129) B2714129
theorem B1809431 : Blo 1204419 1809431 := bstep (se 1 (by rfl) ⟨1357073, by rfl⟩ : syracuseStep 1809431 = 2714147) B2714147
theorem B5217331 : Blo 1204419 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B9157697 : Blo 1204419 9157697 := bstep (se 2 (by rfl) ⟨3434136, by rfl⟩ : syracuseStep 9157697 = 6868273) B6868273
theorem B4070465 : Blo 1204419 4070465 := bstep (se 2 (by rfl) ⟨1526424, by rfl⟩ : syracuseStep 4070465 = 3052849) B3052849
theorem B6511691 : Blo 1204419 6511691 := bstep (se 1 (by rfl) ⟨4883768, by rfl⟩ : syracuseStep 6511691 = 9767537) B9767537
theorem B1809497 : Blo 1204419 1809497 := bstep (se 2 (by rfl) ⟨678561, by rfl⟩ : syracuseStep 1809497 = 1357123) B1357123
theorem B3718237 : Blo 1204419 3718237 := bstep (se 3 (by rfl) ⟨697169, by rfl⟩ : syracuseStep 3718237 = 1394339) B1394339
theorem B1809611 : Blo 1204419 1809611 := bstep (se 1 (by rfl) ⟨1357208, by rfl⟩ : syracuseStep 1809611 = 2714417) B2714417
theorem B1809623 : Blo 1204419 1809623 := bstep (se 1 (by rfl) ⟨1357217, by rfl⟩ : syracuseStep 1809623 = 2714435) B2714435
theorem B2710745 : Blo 1204419 2710745 := bstep (se 2 (by rfl) ⟨1016529, by rfl⟩ : syracuseStep 2710745 = 2033059) B2033059
theorem B6864173 : Blo 1204419 6864173 := bstep (se 3 (by rfl) ⟨1287032, by rfl⟩ : syracuseStep 6864173 = 2574065) B2574065
theorem B2710835 : Blo 1204419 2710835 := bstep (se 1 (by rfl) ⟨2033126, by rfl⟩ : syracuseStep 2710835 = 4066253) B4066253
theorem B2710871 : Blo 1204419 2710871 := bstep (se 1 (by rfl) ⟨2033153, by rfl⟩ : syracuseStep 2710871 = 4066307) B4066307
theorem B2711051 : Blo 1204419 2711051 := bstep (se 1 (by rfl) ⟨2033288, by rfl⟩ : syracuseStep 2711051 = 4066577) B4066577
theorem B2711105 : Blo 1204419 2711105 := bstep (se 2 (by rfl) ⟨1016664, by rfl⟩ : syracuseStep 2711105 = 2033329) B2033329
theorem B8691275 : Blo 1204419 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B4071005 : Blo 1204419 4071005 := bstep (se 3 (by rfl) ⟨763313, by rfl⟩ : syracuseStep 4071005 = 1526627) B1526627
theorem B2711321 : Blo 1204419 2711321 := bstep (se 2 (by rfl) ⟨1016745, by rfl⟩ : syracuseStep 2711321 = 2033491) B2033491
theorem B3260225 : Blo 1204419 3260225 := bstep (se 2 (by rfl) ⟨1222584, by rfl⟩ : syracuseStep 3260225 = 2445169) B2445169
theorem B6954827 : Blo 1204419 6954827 := bstep (se 1 (by rfl) ⟨5216120, by rfl⟩ : syracuseStep 6954827 = 10432241) B10432241
theorem B2711411 : Blo 1204419 2711411 := bstep (se 1 (by rfl) ⟨2033558, by rfl⟩ : syracuseStep 2711411 = 4067117) B4067117
theorem B2711447 : Blo 1204419 2711447 := bstep (se 1 (by rfl) ⟨2033585, by rfl⟩ : syracuseStep 2711447 = 4067171) B4067171
theorem B3432395 : Blo 1204419 3432395 := bstep (se 1 (by rfl) ⟨2574296, by rfl⟩ : syracuseStep 3432395 = 5148593) B5148593
theorem B32964569 : Blo 1204419 32964569 := bstep (se 2 (by rfl) ⟨12361713, by rfl⟩ : syracuseStep 32964569 = 24723427) B24723427
theorem B6864857 : Blo 1204419 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B3137537 : Blo 1204419 3137537 := bstep (se 2 (by rfl) ⟨1176576, by rfl⟩ : syracuseStep 3137537 = 2353153) B2353153
theorem B2711699 : Blo 1204419 2711699 := bstep (se 1 (by rfl) ⟨2033774, by rfl⟩ : syracuseStep 2711699 = 4067549) B4067549
theorem B1982665 : Blo 1204419 1982665 := bstep (se 2 (by rfl) ⟨743499, by rfl⟩ : syracuseStep 1982665 = 1486999) B1486999
theorem B2711753 : Blo 1204419 2711753 := bstep (se 2 (by rfl) ⟨1016907, by rfl⟩ : syracuseStep 2711753 = 2033815) B2033815
theorem B1204487 : Blo 1204419 1204487 := bstep (se 1 (by rfl) ⟨903365, by rfl⟩ : syracuseStep 1204487 = 1806731) B1806731
theorem B1204495 : Blo 1204419 1204495 := bstep (se 1 (by rfl) ⟨903371, by rfl⟩ : syracuseStep 1204495 = 1806743) B1806743
theorem B6603059 : Blo 1204419 6603059 := bstep (se 1 (by rfl) ⟨4952294, by rfl⟩ : syracuseStep 6603059 = 9904589) B9904589
theorem B1204539 : Blo 1204419 1204539 := bstep (se 1 (by rfl) ⟨903404, by rfl⟩ : syracuseStep 1204539 = 1806809) B1806809
theorem B4579699 : Blo 1204419 4579699 := bstep (se 1 (by rfl) ⟨3434774, by rfl⟩ : syracuseStep 4579699 = 6869549) B6869549
theorem B1204615 : Blo 1204419 1204615 := bstep (se 1 (by rfl) ⟨903461, by rfl⟩ : syracuseStep 1204615 = 1806923) B1806923
theorem B1204623 : Blo 1204419 1204623 := bstep (se 1 (by rfl) ⟨903467, by rfl⟩ : syracuseStep 1204623 = 1806935) B1806935
theorem B17375633 : Blo 1204419 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B66896273 : Blo 1204419 66896273 := bstep (se 2 (by rfl) ⟨25086102, by rfl⟩ : syracuseStep 66896273 = 50172205) B50172205
theorem B3432851 : Blo 1204419 3432851 := bstep (se 1 (by rfl) ⟨2574638, by rfl⟩ : syracuseStep 3432851 = 5149277) B5149277
theorem B1204667 : Blo 1204419 1204667 := bstep (se 1 (by rfl) ⟨903500, by rfl⟩ : syracuseStep 1204667 = 1807001) B1807001
theorem B1204743 : Blo 1204419 1204743 := bstep (se 1 (by rfl) ⟨903557, by rfl⟩ : syracuseStep 1204743 = 1807115) B1807115
theorem B1204751 : Blo 1204419 1204751 := bstep (se 1 (by rfl) ⟨903563, by rfl⟩ : syracuseStep 1204751 = 1807127) B1807127
theorem B1204795 : Blo 1204419 1204795 := bstep (se 1 (by rfl) ⟨903596, by rfl⟩ : syracuseStep 1204795 = 1807193) B1807193
theorem B1524359 : Blo 1204419 1524359 := bstep (se 1 (by rfl) ⟨1143269, by rfl⟩ : syracuseStep 1524359 = 2286539) B2286539
theorem B1204871 : Blo 1204419 1204871 := bstep (se 1 (by rfl) ⟨903653, by rfl⟩ : syracuseStep 1204871 = 1807307) B1807307
theorem B1204879 : Blo 1204419 1204879 := bstep (se 1 (by rfl) ⟨903659, by rfl⟩ : syracuseStep 1204879 = 1807319) B1807319
theorem B29303477 : Blo 1204419 29303477 := bstep (se 5 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 29303477 = 2747201) B2747201
theorem B1204923 : Blo 1204419 1204923 := bstep (se 1 (by rfl) ⟨903692, by rfl⟩ : syracuseStep 1204923 = 1807385) B1807385
theorem B15442649 : Blo 1204419 15442649 := bstep (se 2 (by rfl) ⟨5790993, by rfl⟩ : syracuseStep 15442649 = 11581987) B11581987
theorem B6521573 : Blo 1204419 6521573 := bstep (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) B1222795
theorem B3859201 : Blo 1204419 3859201 := bstep (se 2 (by rfl) ⟨1447200, by rfl⟩ : syracuseStep 3859201 = 2894401) B2894401
theorem B1204999 : Blo 1204419 1204999 := bstep (se 1 (by rfl) ⟨903749, by rfl⟩ : syracuseStep 1204999 = 1807499) B1807499
theorem B1205007 : Blo 1204419 1205007 := bstep (se 1 (by rfl) ⟨903755, by rfl⟩ : syracuseStep 1205007 = 1807511) B1807511
theorem B13394723 : Blo 1204419 13394723 := bstep (se 1 (by rfl) ⟨10046042, by rfl⟩ : syracuseStep 13394723 = 20092085) B20092085
theorem B1205051 : Blo 1204419 1205051 := bstep (se 1 (by rfl) ⟨903788, by rfl⟩ : syracuseStep 1205051 = 1807577) B1807577
theorem B2032519 : Blo 1204419 2032519 := bstep (se 1 (by rfl) ⟨1524389, by rfl⟩ : syracuseStep 2032519 = 3048779) B3048779
theorem B1205127 : Blo 1204419 1205127 := bstep (se 1 (by rfl) ⟨903845, by rfl⟩ : syracuseStep 1205127 = 1807691) B1807691
theorem B2712455 : Blo 1204419 2712455 := bstep (se 1 (by rfl) ⟨2034341, by rfl⟩ : syracuseStep 2712455 = 4068683) B4068683
theorem B1205135 : Blo 1204419 1205135 := bstep (se 1 (by rfl) ⟨903851, by rfl⟩ : syracuseStep 1205135 = 1807703) B1807703
theorem B2573203 : Blo 1204419 2573203 := bstep (se 1 (by rfl) ⟨1929902, by rfl⟩ : syracuseStep 2573203 = 3859805) B3859805
theorem B14656409 : Blo 1204419 14656409 := bstep (se 2 (by rfl) ⟨5496153, by rfl⟩ : syracuseStep 14656409 = 10992307) B10992307
theorem B1205179 : Blo 1204419 1205179 := bstep (se 1 (by rfl) ⟨903884, by rfl⟩ : syracuseStep 1205179 = 1807769) B1807769
theorem B1205255 : Blo 1204419 1205255 := bstep (se 1 (by rfl) ⟨903941, by rfl⟩ : syracuseStep 1205255 = 1807883) B1807883
theorem B1205263 : Blo 1204419 1205263 := bstep (se 1 (by rfl) ⟨903947, by rfl⟩ : syracuseStep 1205263 = 1807895) B1807895
theorem B1205307 : Blo 1204419 1205307 := bstep (se 1 (by rfl) ⟨903980, by rfl⟩ : syracuseStep 1205307 = 1807961) B1807961
theorem B2712635 : Blo 1204419 2712635 := bstep (se 1 (by rfl) ⟨2034476, by rfl⟩ : syracuseStep 2712635 = 4068953) B4068953
theorem B13026365 : Blo 1204419 13026365 := bstep (se 3 (by rfl) ⟨2442443, by rfl⟩ : syracuseStep 13026365 = 4884887) B4884887
theorem B6521917 : Blo 1204419 6521917 := bstep (se 3 (by rfl) ⟨1222859, by rfl⟩ : syracuseStep 6521917 = 2445719) B2445719
theorem B1205383 : Blo 1204419 1205383 := bstep (se 1 (by rfl) ⟨904037, by rfl⟩ : syracuseStep 1205383 = 1808075) B1808075
theorem B1205391 : Blo 1204419 1205391 := bstep (se 1 (by rfl) ⟨904043, by rfl⟩ : syracuseStep 1205391 = 1808087) B1808087
theorem B2712761 : Blo 1204419 2712761 := bstep (se 2 (by rfl) ⟨1017285, by rfl⟩ : syracuseStep 2712761 = 2034571) B2034571
theorem B1205435 : Blo 1204419 1205435 := bstep (se 1 (by rfl) ⟨904076, by rfl⟩ : syracuseStep 1205435 = 1808153) B1808153
theorem B6104321 : Blo 1204419 6104321 := bstep (se 2 (by rfl) ⟨2289120, by rfl⟩ : syracuseStep 6104321 = 4578241) B4578241
theorem B1205511 : Blo 1204419 1205511 := bstep (se 1 (by rfl) ⟨904133, by rfl⟩ : syracuseStep 1205511 = 1808267) B1808267
theorem B1525007 : Blo 1204419 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B1205519 : Blo 1204419 1205519 := bstep (se 1 (by rfl) ⟨904139, by rfl⟩ : syracuseStep 1205519 = 1808279) B1808279
theorem B2934049 : Blo 1204419 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B1205563 : Blo 1204419 1205563 := bstep (se 1 (by rfl) ⟨904172, by rfl⟩ : syracuseStep 1205563 = 1808345) B1808345
theorem B19547527 : Blo 1204419 19547527 := bstep (se 1 (by rfl) ⟨14660645, by rfl⟩ : syracuseStep 19547527 = 29321291) B29321291
theorem B1205639 : Blo 1204419 1205639 := bstep (se 1 (by rfl) ⟨904229, by rfl⟩ : syracuseStep 1205639 = 1808459) B1808459
theorem B1205647 : Blo 1204419 1205647 := bstep (se 1 (by rfl) ⟨904235, by rfl⟩ : syracuseStep 1205647 = 1808471) B1808471
theorem B6956441 : Blo 1204419 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B26076593 : Blo 1204419 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B1205691 : Blo 1204419 1205691 := bstep (se 1 (by rfl) ⟨904268, by rfl⟩ : syracuseStep 1205691 = 1808537) B1808537
theorem B4957649 : Blo 1204419 4957649 := bstep (se 2 (by rfl) ⟨1859118, by rfl⟩ : syracuseStep 4957649 = 3718237) B3718237
theorem B3048961 : Blo 1204419 3048961 := bstep (se 2 (by rfl) ⟨1143360, by rfl⟩ : syracuseStep 3048961 = 2286721) B2286721
theorem B10429955 : Blo 1204419 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B1205767 : Blo 1204419 1205767 := bstep (se 1 (by rfl) ⟨904325, by rfl⟩ : syracuseStep 1205767 = 1808651) B1808651
theorem B2033167 : Blo 1204419 2033167 := bstep (se 1 (by rfl) ⟨1524875, by rfl⟩ : syracuseStep 2033167 = 3049751) B3049751
theorem B1205775 : Blo 1204419 1205775 := bstep (se 1 (by rfl) ⟨904331, by rfl⟩ : syracuseStep 1205775 = 1808663) B1808663
theorem B2713103 : Blo 1204419 2713103 := bstep (se 1 (by rfl) ⟨2034827, by rfl⟩ : syracuseStep 2713103 = 4069655) B4069655
theorem B1287695 : Blo 1204419 1287695 := bstep (se 1 (by rfl) ⟨965771, by rfl⟩ : syracuseStep 1287695 = 1931543) B1931543
theorem B2713121 : Blo 1204419 2713121 := bstep (se 2 (by rfl) ⟨1017420, by rfl⟩ : syracuseStep 2713121 = 2034841) B2034841
theorem B6514219 : Blo 1204419 6514219 := bstep (se 1 (by rfl) ⟨4885664, by rfl⟩ : syracuseStep 6514219 = 9771329) B9771329
theorem B1205819 : Blo 1204419 1205819 := bstep (se 1 (by rfl) ⟨904364, by rfl⟩ : syracuseStep 1205819 = 1808729) B1808729
theorem B1205895 : Blo 1204419 1205895 := bstep (se 1 (by rfl) ⟨904421, by rfl⟩ : syracuseStep 1205895 = 1808843) B1808843
theorem B1205903 : Blo 1204419 1205903 := bstep (se 1 (by rfl) ⟨904427, by rfl⟩ : syracuseStep 1205903 = 1808855) B1808855
theorem B1205947 : Blo 1204419 1205947 := bstep (se 1 (by rfl) ⟨904460, by rfl⟩ : syracuseStep 1205947 = 1808921) B1808921
theorem B6866633 : Blo 1204419 6866633 := bstep (se 2 (by rfl) ⟨2574987, by rfl⟩ : syracuseStep 6866633 = 5149975) B5149975
theorem B47605477 : Blo 1204419 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B1206023 : Blo 1204419 1206023 := bstep (se 1 (by rfl) ⟨904517, by rfl⟩ : syracuseStep 1206023 = 1809035) B1809035
theorem B3434251 : Blo 1204419 3434251 := bstep (se 1 (by rfl) ⟨2575688, by rfl⟩ : syracuseStep 3434251 = 5151377) B5151377
theorem B1206031 : Blo 1204419 1206031 := bstep (se 1 (by rfl) ⟨904523, by rfl⟩ : syracuseStep 1206031 = 1809047) B1809047
theorem B5793569 : Blo 1204419 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B1206075 : Blo 1204419 1206075 := bstep (se 1 (by rfl) ⟨904556, by rfl⟩ : syracuseStep 1206075 = 1809113) B1809113
theorem B2172791 : Blo 1204419 2172791 := bstep (se 1 (by rfl) ⟨1629593, by rfl⟩ : syracuseStep 2172791 = 3259187) B3259187
theorem B2713463 : Blo 1204419 2713463 := bstep (se 1 (by rfl) ⟨2035097, by rfl⟩ : syracuseStep 2713463 = 4070195) B4070195
theorem B1206151 : Blo 1204419 1206151 := bstep (se 1 (by rfl) ⟨904613, by rfl⟩ : syracuseStep 1206151 = 1809227) B1809227
theorem B1206159 : Blo 1204419 1206159 := bstep (se 1 (by rfl) ⟨904619, by rfl⟩ : syracuseStep 1206159 = 1809239) B1809239
theorem B13027225 : Blo 1204419 13027225 := bstep (se 2 (by rfl) ⟨4885209, by rfl⟩ : syracuseStep 13027225 = 9770419) B9770419
theorem B1206203 : Blo 1204419 1206203 := bstep (se 1 (by rfl) ⟨904652, by rfl⟩ : syracuseStep 1206203 = 1809305) B1809305
theorem B1206279 : Blo 1204419 1206279 := bstep (se 1 (by rfl) ⟨904709, by rfl⟩ : syracuseStep 1206279 = 1809419) B1809419
theorem B1206287 : Blo 1204419 1206287 := bstep (se 1 (by rfl) ⟨904715, by rfl⟩ : syracuseStep 1206287 = 1809431) B1809431
theorem B3434525 : Blo 1204419 3434525 := bstep (se 3 (by rfl) ⟨643973, by rfl⟩ : syracuseStep 3434525 = 1287947) B1287947
theorem B2033707 : Blo 1204419 2033707 := bstep (se 1 (by rfl) ⟨1525280, by rfl⟩ : syracuseStep 2033707 = 3050561) B3050561
theorem B6105131 : Blo 1204419 6105131 := bstep (se 1 (by rfl) ⟨4578848, by rfl⟩ : syracuseStep 6105131 = 9157697) B9157697
theorem B2713643 : Blo 1204419 2713643 := bstep (se 1 (by rfl) ⟨2035232, by rfl⟩ : syracuseStep 2713643 = 4070465) B4070465
theorem B1206331 : Blo 1204419 1206331 := bstep (se 1 (by rfl) ⟨904748, by rfl⟩ : syracuseStep 1206331 = 1809497) B1809497
theorem B3049559 : Blo 1204419 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B1206407 : Blo 1204419 1206407 := bstep (se 1 (by rfl) ⟨904805, by rfl⟩ : syracuseStep 1206407 = 1809611) B1809611
theorem B1206415 : Blo 1204419 1206415 := bstep (se 1 (by rfl) ⟨904811, by rfl⟩ : syracuseStep 1206415 = 1809623) B1809623
theorem B2033849 : Blo 1204419 2033849 := bstep (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) B1525387
theorem B4065551 : Blo 1204419 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B3049771 : Blo 1204419 3049771 := bstep (se 1 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 3049771 = 4574657) B4574657
theorem B1411387 : Blo 1204419 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B5794183 : Blo 1204419 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B2714003 : Blo 1204419 2714003 := bstep (se 1 (by rfl) ⟨2035502, by rfl⟩ : syracuseStep 2714003 = 4071005) B4071005
theorem B3049913 : Blo 1204419 3049913 := bstep (se 2 (by rfl) ⟨1143717, by rfl⟩ : syracuseStep 3049913 = 2287435) B2287435
theorem B2714057 : Blo 1204419 2714057 := bstep (se 2 (by rfl) ⟨1017771, by rfl⟩ : syracuseStep 2714057 = 2035543) B2035543
theorem B4065821 : Blo 1204419 4065821 := bstep (se 3 (by rfl) ⟨762341, by rfl⟩ : syracuseStep 4065821 = 1524683) B1524683
theorem B2173483 : Blo 1204419 2173483 := bstep (se 1 (by rfl) ⟨1630112, by rfl⟩ : syracuseStep 2173483 = 3260225) B3260225
theorem B2288263 : Blo 1204419 2288263 := bstep (se 1 (by rfl) ⟨1716197, by rfl⟩ : syracuseStep 2288263 = 3432395) B3432395
theorem B6097679 : Blo 1204419 6097679 := bstep (se 1 (by rfl) ⟨4573259, by rfl⟩ : syracuseStep 6097679 = 9146519) B9146519
theorem B2034551 : Blo 1204419 2034551 := bstep (se 1 (by rfl) ⟨1525913, by rfl⟩ : syracuseStep 2034551 = 3051827) B3051827
theorem B11578373 : Blo 1204419 11578373 := bstep (se 4 (by rfl) ⟨1085472, by rfl⟩ : syracuseStep 11578373 = 2170945) B2170945
theorem B6859799 : Blo 1204419 6859799 := bstep (se 1 (by rfl) ⟨5144849, by rfl⟩ : syracuseStep 6859799 = 10289699) B10289699
theorem B7834913 : Blo 1204419 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B2035003 : Blo 1204419 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B6106427 : Blo 1204419 6106427 := bstep (se 1 (by rfl) ⟨4579820, by rfl⟩ : syracuseStep 6106427 = 9159641) B9159641
theorem B27823459 : Blo 1204419 27823459 := bstep (se 1 (by rfl) ⟨20867594, by rfl⟩ : syracuseStep 27823459 = 41735189) B41735189
theorem B1355143 : Blo 1204419 1355143 := bstep (se 1 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 1355143 = 2032715) B2032715
theorem B2895239 : Blo 1204419 2895239 := bstep (se 1 (by rfl) ⟨2171429, by rfl⟩ : syracuseStep 2895239 = 4342859) B4342859
theorem B3050905 : Blo 1204419 3050905 := bstep (se 2 (by rfl) ⟨1144089, by rfl⟩ : syracuseStep 3050905 = 2288179) B2288179
theorem B2035145 : Blo 1204419 2035145 := bstep (se 2 (by rfl) ⟨763179, by rfl⟩ : syracuseStep 2035145 = 1526359) B1526359
theorem B6106589 : Blo 1204419 6106589 := bstep (se 3 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 6106589 = 2289971) B2289971
theorem B1355323 : Blo 1204419 1355323 := bstep (se 1 (by rfl) ⟨1016492, by rfl⟩ : syracuseStep 1355323 = 2032985) B2032985
theorem B3051067 : Blo 1204419 3051067 := bstep (se 1 (by rfl) ⟨2288300, by rfl⟩ : syracuseStep 3051067 = 4576601) B4576601
theorem B6868547 : Blo 1204419 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B4574839 : Blo 1204419 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B3051209 : Blo 1204419 3051209 := bstep (se 2 (by rfl) ⟨1144203, by rfl⟩ : syracuseStep 3051209 = 2288407) B2288407
theorem B6106913 : Blo 1204419 6106913 := bstep (se 2 (by rfl) ⟨2290092, by rfl⟩ : syracuseStep 6106913 = 4580185) B4580185
theorem B4067225 : Blo 1204419 4067225 := bstep (se 2 (by rfl) ⟨1525209, by rfl⟩ : syracuseStep 4067225 = 3050419) B3050419
theorem B2609081 : Blo 1204419 2609081 := bstep (se 2 (by rfl) ⟨978405, by rfl⟩ : syracuseStep 2609081 = 1956811) B1956811
theorem B1716169 : Blo 1204419 1716169 := bstep (se 2 (by rfl) ⟨643563, by rfl⟩ : syracuseStep 1716169 = 1287127) B1287127
theorem B1355791 : Blo 1204419 1355791 := bstep (se 1 (by rfl) ⟨1016843, by rfl⟩ : syracuseStep 1355791 = 2033687) B2033687
theorem B3051553 : Blo 1204419 3051553 := bstep (se 2 (by rfl) ⟨1144332, by rfl⟩ : syracuseStep 3051553 = 2288665) B2288665
theorem B6099137 : Blo 1204419 6099137 := bstep (se 2 (by rfl) ⟨2287176, by rfl⟩ : syracuseStep 6099137 = 4574353) B4574353
theorem B2289865 : Blo 1204419 2289865 := bstep (se 2 (by rfl) ⟨858699, by rfl⟩ : syracuseStep 2289865 = 1717399) B1717399
theorem B3092737 : Blo 1204419 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B1806635 : Blo 1204419 1806635 := bstep (se 1 (by rfl) ⟨1354976, by rfl⟩ : syracuseStep 1806635 = 2709953) B2709953
theorem B1806665 : Blo 1204419 1806665 := bstep (se 2 (by rfl) ⟨677499, by rfl⟩ : syracuseStep 1806665 = 1354999) B1354999
theorem B29348243 : Blo 1204419 29348243 := bstep (se 1 (by rfl) ⟨22011182, by rfl⟩ : syracuseStep 29348243 = 44022365) B44022365
theorem B1806779 : Blo 1204419 1806779 := bstep (se 1 (by rfl) ⟨1355084, by rfl⟩ : syracuseStep 1806779 = 2710169) B2710169
theorem B1806839 : Blo 1204419 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B1716727 : Blo 1204419 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B1356295 : Blo 1204419 1356295 := bstep (se 1 (by rfl) ⟨1017221, by rfl⟩ : syracuseStep 1356295 = 2034443) B2034443
theorem B1806863 : Blo 1204419 1806863 := bstep (se 1 (by rfl) ⟨1355147, by rfl⟩ : syracuseStep 1806863 = 2710295) B2710295
theorem B3093025 : Blo 1204419 3093025 := bstep (se 2 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 3093025 = 2319769) B2319769
theorem B1831481 : Blo 1204419 1831481 := bstep (se 2 (by rfl) ⟨686805, by rfl⟩ : syracuseStep 1831481 = 1373611) B1373611
theorem B1806905 : Blo 1204419 1806905 := bstep (se 2 (by rfl) ⟨677589, by rfl⟩ : syracuseStep 1806905 = 1355179) B1355179
theorem B4575811 : Blo 1204419 4575811 := bstep (se 1 (by rfl) ⟨3431858, by rfl⟩ : syracuseStep 4575811 = 6863717) B6863717
theorem B4067927 : Blo 1204419 4067927 := bstep (se 1 (by rfl) ⟨3050945, by rfl⟩ : syracuseStep 4067927 = 6101891) B6101891
theorem B3052151 : Blo 1204419 3052151 := bstep (se 1 (by rfl) ⟨2289113, by rfl⟩ : syracuseStep 3052151 = 4578227) B4578227
theorem B1806983 : Blo 1204419 1806983 := bstep (se 1 (by rfl) ⟨1355237, by rfl⟩ : syracuseStep 1806983 = 2710475) B2710475
theorem B1807019 : Blo 1204419 1807019 := bstep (se 1 (by rfl) ⟨1355264, by rfl⟩ : syracuseStep 1807019 = 2710529) B2710529
theorem B6517421 : Blo 1204419 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B1831609 : Blo 1204419 1831609 := bstep (se 2 (by rfl) ⟨686853, by rfl⟩ : syracuseStep 1831609 = 1373707) B1373707
theorem B1356475 : Blo 1204419 1356475 := bstep (se 1 (by rfl) ⟨1017356, by rfl⟩ : syracuseStep 1356475 = 2034713) B2034713
theorem B1807049 : Blo 1204419 1807049 := bstep (se 2 (by rfl) ⟨677643, by rfl⟩ : syracuseStep 1807049 = 1355287) B1355287
theorem B2896651 : Blo 1204419 2896651 := bstep (se 1 (by rfl) ⟨2172488, by rfl⟩ : syracuseStep 2896651 = 4344977) B4344977
theorem B1807163 : Blo 1204419 1807163 := bstep (se 1 (by rfl) ⟨1355372, by rfl⟩ : syracuseStep 1807163 = 2710745) B2710745
theorem B2896727 : Blo 1204419 2896727 := bstep (se 1 (by rfl) ⟨2172545, by rfl⟩ : syracuseStep 2896727 = 4345091) B4345091
theorem B4576115 : Blo 1204419 4576115 := bstep (se 1 (by rfl) ⟨3432086, by rfl⟩ : syracuseStep 4576115 = 6864173) B6864173
theorem B1807223 : Blo 1204419 1807223 := bstep (se 1 (by rfl) ⟨1355417, by rfl⟩ : syracuseStep 1807223 = 2710835) B2710835
theorem B1807247 : Blo 1204419 1807247 := bstep (se 1 (by rfl) ⟨1355435, by rfl⟩ : syracuseStep 1807247 = 2710871) B2710871
theorem B1807289 : Blo 1204419 1807289 := bstep (se 2 (by rfl) ⟨677733, by rfl⟩ : syracuseStep 1807289 = 1355467) B1355467
theorem B1807367 : Blo 1204419 1807367 := bstep (se 1 (by rfl) ⟨1355525, by rfl⟩ : syracuseStep 1807367 = 2711051) B2711051
theorem B1807403 : Blo 1204419 1807403 := bstep (se 1 (by rfl) ⟨1355552, by rfl⟩ : syracuseStep 1807403 = 2711105) B2711105
theorem B1717291 : Blo 1204419 1717291 := bstep (se 1 (by rfl) ⟨1287968, by rfl⟩ : syracuseStep 1717291 = 2575937) B2575937
theorem B3257405 : Blo 1204419 3257405 := bstep (se 3 (by rfl) ⟨610763, by rfl⟩ : syracuseStep 3257405 = 1221527) B1221527
theorem B4068413 : Blo 1204419 4068413 := bstep (se 3 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 4068413 = 1525655) B1525655
theorem B1807433 : Blo 1204419 1807433 := bstep (se 2 (by rfl) ⟨677787, by rfl⟩ : syracuseStep 1807433 = 1355575) B1355575
theorem B1356943 : Blo 1204419 1356943 := bstep (se 1 (by rfl) ⟨1017707, by rfl⟩ : syracuseStep 1356943 = 2035415) B2035415
theorem B1807547 : Blo 1204419 1807547 := bstep (se 1 (by rfl) ⟨1355660, by rfl⟩ : syracuseStep 1807547 = 2711321) B2711321
theorem B1807607 : Blo 1204419 1807607 := bstep (se 1 (by rfl) ⟨1355705, by rfl⟩ : syracuseStep 1807607 = 2711411) B2711411
theorem B1807631 : Blo 1204419 1807631 := bstep (se 1 (by rfl) ⟨1355723, by rfl⟩ : syracuseStep 1807631 = 2711447) B2711447
theorem B1717519 : Blo 1204419 1717519 := bstep (se 1 (by rfl) ⟨1288139, by rfl⟩ : syracuseStep 1717519 = 2576279) B2576279
theorem B1807673 : Blo 1204419 1807673 := bstep (se 2 (by rfl) ⟨677877, by rfl⟩ : syracuseStep 1807673 = 1355755) B1355755
theorem B21976379 : Blo 1204419 21976379 := bstep (se 1 (by rfl) ⟨16482284, by rfl⟩ : syracuseStep 21976379 = 32964569) B32964569
theorem B4576571 : Blo 1204419 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B13727069 : Blo 1204419 13727069 := bstep (se 3 (by rfl) ⟨2573825, by rfl⟩ : syracuseStep 13727069 = 5147651) B5147651
theorem B1807751 : Blo 1204419 1807751 := bstep (se 1 (by rfl) ⟨1355813, by rfl⟩ : syracuseStep 1807751 = 2711627) B2711627
theorem B1807787 : Blo 1204419 1807787 := bstep (se 1 (by rfl) ⟨1355840, by rfl⟩ : syracuseStep 1807787 = 2711681) B2711681
theorem B1807817 : Blo 1204419 1807817 := bstep (se 2 (by rfl) ⟨677931, by rfl⟩ : syracuseStep 1807817 = 1355863) B1355863
theorem B6100433 : Blo 1204419 6100433 := bstep (se 2 (by rfl) ⟨2287662, by rfl⟩ : syracuseStep 6100433 = 4575325) B4575325
theorem B1807931 : Blo 1204419 1807931 := bstep (se 1 (by rfl) ⟨1355948, by rfl⟩ : syracuseStep 1807931 = 2711897) B2711897
theorem B1807991 : Blo 1204419 1807991 := bstep (se 1 (by rfl) ⟨1355993, by rfl⟩ : syracuseStep 1807991 = 2711987) B2711987
theorem B1808015 : Blo 1204419 1808015 := bstep (se 1 (by rfl) ⟨1356011, by rfl⟩ : syracuseStep 1808015 = 2712023) B2712023
theorem B1808057 : Blo 1204419 1808057 := bstep (se 2 (by rfl) ⟨678021, by rfl⟩ : syracuseStep 1808057 = 1356043) B1356043
theorem B1808135 : Blo 1204419 1808135 := bstep (se 1 (by rfl) ⟨1356101, by rfl⟩ : syracuseStep 1808135 = 2712203) B2712203
theorem B4577057 : Blo 1204419 4577057 := bstep (se 2 (by rfl) ⟨1716396, by rfl⟩ : syracuseStep 4577057 = 3432793) B3432793
theorem B1808171 : Blo 1204419 1808171 := bstep (se 1 (by rfl) ⟨1356128, by rfl⟩ : syracuseStep 1808171 = 2712257) B2712257
theorem B12367667 : Blo 1204419 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B62666561 : Blo 1204419 62666561 := bstep (se 2 (by rfl) ⟨23499960, by rfl⟩ : syracuseStep 62666561 = 46999921) B46999921
theorem B1832777 : Blo 1204419 1832777 := bstep (se 2 (by rfl) ⟨687291, by rfl⟩ : syracuseStep 1832777 = 1374583) B1374583
theorem B1808201 : Blo 1204419 1808201 := bstep (se 2 (by rfl) ⟨678075, by rfl⟩ : syracuseStep 1808201 = 1356151) B1356151
theorem B3053447 : Blo 1204419 3053447 := bstep (se 1 (by rfl) ⟨2290085, by rfl⟩ : syracuseStep 3053447 = 4580171) B4580171
theorem B3053497 : Blo 1204419 3053497 := bstep (se 2 (by rfl) ⟨1145061, by rfl⟩ : syracuseStep 3053497 = 2290123) B2290123
theorem B1808315 : Blo 1204419 1808315 := bstep (se 1 (by rfl) ⟨1356236, by rfl⟩ : syracuseStep 1808315 = 2712473) B2712473
theorem B1808375 : Blo 1204419 1808375 := bstep (se 1 (by rfl) ⟨1356281, by rfl⟩ : syracuseStep 1808375 = 2712563) B2712563
theorem B1808399 : Blo 1204419 1808399 := bstep (se 1 (by rfl) ⟨1356299, by rfl⟩ : syracuseStep 1808399 = 2712599) B2712599
theorem B1808441 : Blo 1204419 1808441 := bstep (se 2 (by rfl) ⟨678165, by rfl⟩ : syracuseStep 1808441 = 1356331) B1356331
theorem B6789187 : Blo 1204419 6789187 := bstep (se 1 (by rfl) ⟨5091890, by rfl⟩ : syracuseStep 6789187 = 10183781) B10183781
theorem B6862967 : Blo 1204419 6862967 := bstep (se 1 (by rfl) ⟨5147225, by rfl⟩ : syracuseStep 6862967 = 10294451) B10294451
theorem B1808519 : Blo 1204419 1808519 := bstep (se 1 (by rfl) ⟨1356389, by rfl⟩ : syracuseStep 1808519 = 2712779) B2712779
theorem B3479699 : Blo 1204419 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B1808555 : Blo 1204419 1808555 := bstep (se 1 (by rfl) ⟨1356416, by rfl⟩ : syracuseStep 1808555 = 2712833) B2712833
theorem B1448123 : Blo 1204419 1448123 := bstep (se 1 (by rfl) ⟨1086092, by rfl⟩ : syracuseStep 1448123 = 2172185) B2172185
theorem B1808585 : Blo 1204419 1808585 := bstep (se 2 (by rfl) ⟨678219, by rfl⟩ : syracuseStep 1808585 = 1356439) B1356439
theorem B11589905 : Blo 1204419 11589905 := bstep (se 2 (by rfl) ⟨4346214, by rfl⟩ : syracuseStep 11589905 = 8692429) B8692429
theorem B1808699 : Blo 1204419 1808699 := bstep (se 1 (by rfl) ⟨1356524, by rfl⟩ : syracuseStep 1808699 = 2713049) B2713049
theorem B1808759 : Blo 1204419 1808759 := bstep (se 1 (by rfl) ⟨1356569, by rfl⟩ : syracuseStep 1808759 = 2713139) B2713139
theorem B1808783 : Blo 1204419 1808783 := bstep (se 1 (by rfl) ⟨1356587, by rfl⟩ : syracuseStep 1808783 = 2713175) B2713175
theorem B4069817 : Blo 1204419 4069817 := bstep (se 2 (by rfl) ⟨1526181, by rfl⟩ : syracuseStep 4069817 = 3052363) B3052363
theorem B1808825 : Blo 1204419 1808825 := bstep (se 2 (by rfl) ⟨678309, by rfl⟩ : syracuseStep 1808825 = 1356619) B1356619
theorem B1808903 : Blo 1204419 1808903 := bstep (se 1 (by rfl) ⟨1356677, by rfl⟩ : syracuseStep 1808903 = 2713355) B2713355
theorem B1808939 : Blo 1204419 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B5151275 : Blo 1204419 5151275 := bstep (se 1 (by rfl) ⟨3863456, by rfl⟩ : syracuseStep 5151275 = 7726913) B7726913
theorem B1808969 : Blo 1204419 1808969 := bstep (se 2 (by rfl) ⟨678363, by rfl⟩ : syracuseStep 1808969 = 1356727) B1356727
theorem B14654071 : Blo 1204419 14654071 := bstep (se 1 (by rfl) ⟨10990553, by rfl⟩ : syracuseStep 14654071 = 21981107) B21981107
theorem B2062967 : Blo 1204419 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B2710151 : Blo 1204419 2710151 := bstep (se 1 (by rfl) ⟨2032613, by rfl⟩ : syracuseStep 2710151 = 4065227) B4065227
theorem B1809083 : Blo 1204419 1809083 := bstep (se 1 (by rfl) ⟨1356812, by rfl⟩ : syracuseStep 1809083 = 2713625) B2713625
theorem B4578029 : Blo 1204419 4578029 := bstep (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) B1716761
theorem B1809143 : Blo 1204419 1809143 := bstep (se 1 (by rfl) ⟨1356857, by rfl⟩ : syracuseStep 1809143 = 2713715) B2713715
theorem B13728527 : Blo 1204419 13728527 := bstep (se 1 (by rfl) ⟨10296395, by rfl⟩ : syracuseStep 13728527 = 20592791) B20592791
theorem B1809167 : Blo 1204419 1809167 := bstep (se 1 (by rfl) ⟨1356875, by rfl⟩ : syracuseStep 1809167 = 2713751) B2713751
theorem B1809209 : Blo 1204419 1809209 := bstep (se 2 (by rfl) ⟨678453, by rfl⟩ : syracuseStep 1809209 = 1356907) B1356907
theorem B2710331 : Blo 1204419 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B1809287 : Blo 1204419 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B1809323 : Blo 1204419 1809323 := bstep (se 1 (by rfl) ⟨1356992, by rfl⟩ : syracuseStep 1809323 = 2713985) B2713985
theorem B2710457 : Blo 1204419 2710457 := bstep (se 2 (by rfl) ⟨1016421, by rfl⟩ : syracuseStep 2710457 = 2032843) B2032843
theorem B1809353 : Blo 1204419 1809353 := bstep (se 2 (by rfl) ⟨678507, by rfl⟩ : syracuseStep 1809353 = 1357015) B1357015
theorem B4070411 : Blo 1204419 4070411 := bstep (se 1 (by rfl) ⟨3052808, by rfl⟩ : syracuseStep 4070411 = 6105617) B6105617
theorem B1932331 : Blo 1204419 1932331 := bstep (se 1 (by rfl) ⟨1449248, by rfl⟩ : syracuseStep 1932331 = 2898497) B2898497
theorem B1809467 : Blo 1204419 1809467 := bstep (se 1 (by rfl) ⟨1357100, by rfl⟩ : syracuseStep 1809467 = 2714201) B2714201
theorem B7724119 : Blo 1204419 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B3259511 : Blo 1204419 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B4070519 : Blo 1204419 4070519 := bstep (se 1 (by rfl) ⟨3052889, by rfl⟩ : syracuseStep 4070519 = 6105779) B6105779
theorem B1809527 : Blo 1204419 1809527 := bstep (se 1 (by rfl) ⟨1357145, by rfl⟩ : syracuseStep 1809527 = 2714291) B2714291
theorem B1809551 : Blo 1204419 1809551 := bstep (se 1 (by rfl) ⟨1357163, by rfl⟩ : syracuseStep 1809551 = 2714327) B2714327
theorem B3431609 : Blo 1204419 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B1809593 : Blo 1204419 1809593 := bstep (se 2 (by rfl) ⟨678597, by rfl⟩ : syracuseStep 1809593 = 1357195) B1357195
theorem B2710799 : Blo 1204419 2710799 := bstep (se 1 (by rfl) ⟨2033099, by rfl⟩ : syracuseStep 2710799 = 4066199) B4066199
theorem B2710817 : Blo 1204419 2710817 := bstep (se 2 (by rfl) ⟨1016556, by rfl⟩ : syracuseStep 2710817 = 2033113) B2033113
theorem B13737275 : Blo 1204419 13737275 := bstep (se 1 (by rfl) ⟨10302956, by rfl⟩ : syracuseStep 13737275 = 20605913) B20605913
theorem B4341127 : Blo 1204419 4341127 := bstep (se 1 (by rfl) ⟨3255845, by rfl⟩ : syracuseStep 4341127 = 6511691) B6511691
theorem B4578713 : Blo 1204419 4578713 := bstep (se 2 (by rfl) ⟨1717017, by rfl⟩ : syracuseStep 4578713 = 3434035) B3434035
theorem B6102539 : Blo 1204419 6102539 := bstep (se 1 (by rfl) ⟨4576904, by rfl⟩ : syracuseStep 6102539 = 9153809) B9153809
theorem B18546205 : Blo 1204419 18546205 := bstep (se 3 (by rfl) ⟨3477413, by rfl⟩ : syracuseStep 18546205 = 6954827) B6954827
theorem B2711159 : Blo 1204419 2711159 := bstep (se 1 (by rfl) ⟨2033369, by rfl⟩ : syracuseStep 2711159 = 4066739) B4066739
theorem B6102701 : Blo 1204419 6102701 := bstep (se 3 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 6102701 = 2288513) B2288513
theorem B4071113 : Blo 1204419 4071113 := bstep (se 2 (by rfl) ⟨1526667, by rfl⟩ : syracuseStep 4071113 = 3053335) B3053335
theorem B4890401 : Blo 1204419 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B2711339 : Blo 1204419 2711339 := bstep (se 1 (by rfl) ⟨2033504, by rfl⟩ : syracuseStep 2711339 = 4067009) B4067009
theorem B2711609 : Blo 1204419 2711609 := bstep (se 2 (by rfl) ⟨1016853, by rfl⟩ : syracuseStep 2711609 = 2033707) B2033707
theorem B9052249 : Blo 1204419 9052249 := bstep (se 2 (by rfl) ⟨3394593, by rfl⟩ : syracuseStep 9052249 = 6789187) B6789187
theorem B1204423 : Blo 1204419 1204423 := bstep (se 1 (by rfl) ⟨903317, by rfl⟩ : syracuseStep 1204423 = 1806635) B1806635
theorem B1204443 : Blo 1204419 1204443 := bstep (se 1 (by rfl) ⟨903332, by rfl⟩ : syracuseStep 1204443 = 1806665) B1806665
theorem B11583755 : Blo 1204419 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B44597515 : Blo 1204419 44597515 := bstep (se 1 (by rfl) ⟨33448136, by rfl⟩ : syracuseStep 44597515 = 66896273) B66896273
theorem B1204519 : Blo 1204419 1204519 := bstep (se 1 (by rfl) ⟨903389, by rfl⟩ : syracuseStep 1204519 = 1806779) B1806779
theorem B1204559 : Blo 1204419 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B1204575 : Blo 1204419 1204575 := bstep (se 1 (by rfl) ⟨903431, by rfl⟩ : syracuseStep 1204575 = 1806863) B1806863
theorem B1220987 : Blo 1204419 1220987 := bstep (se 1 (by rfl) ⟨915740, by rfl⟩ : syracuseStep 1220987 = 1831481) B1831481
theorem B1204603 : Blo 1204419 1204603 := bstep (se 1 (by rfl) ⟨903452, by rfl⟩ : syracuseStep 1204603 = 1806905) B1806905
theorem B2711951 : Blo 1204419 2711951 := bstep (se 1 (by rfl) ⟨2033963, by rfl⟩ : syracuseStep 2711951 = 4067927) B4067927
theorem B1204655 : Blo 1204419 1204655 := bstep (se 1 (by rfl) ⟨903491, by rfl⟩ : syracuseStep 1204655 = 1806983) B1806983
theorem B1204679 : Blo 1204419 1204679 := bstep (se 1 (by rfl) ⟨903509, by rfl⟩ : syracuseStep 1204679 = 1807019) B1807019
theorem B1204699 : Blo 1204419 1204699 := bstep (se 1 (by rfl) ⟨903524, by rfl⟩ : syracuseStep 1204699 = 1807049) B1807049
theorem B1204775 : Blo 1204419 1204775 := bstep (se 1 (by rfl) ⟨903581, by rfl⟩ : syracuseStep 1204775 = 1807163) B1807163
theorem B1204815 : Blo 1204419 1204815 := bstep (se 1 (by rfl) ⟨903611, by rfl⟩ : syracuseStep 1204815 = 1807223) B1807223
theorem B1204831 : Blo 1204419 1204831 := bstep (se 1 (by rfl) ⟨903623, by rfl⟩ : syracuseStep 1204831 = 1807247) B1807247
theorem B1204859 : Blo 1204419 1204859 := bstep (se 1 (by rfl) ⟨903644, by rfl⟩ : syracuseStep 1204859 = 1807289) B1807289
theorem B1204911 : Blo 1204419 1204911 := bstep (se 1 (by rfl) ⟨903683, by rfl⟩ : syracuseStep 1204911 = 1807367) B1807367
theorem B1204935 : Blo 1204419 1204935 := bstep (se 1 (by rfl) ⟨903701, by rfl⟩ : syracuseStep 1204935 = 1807403) B1807403
theorem B8684243 : Blo 1204419 8684243 := bstep (se 1 (by rfl) ⟨6513182, by rfl⟩ : syracuseStep 8684243 = 13026365) B13026365
theorem B2171603 : Blo 1204419 2171603 := bstep (se 1 (by rfl) ⟨1628702, by rfl⟩ : syracuseStep 2171603 = 3257405) B3257405
theorem B2712275 : Blo 1204419 2712275 := bstep (se 1 (by rfl) ⟨2034206, by rfl⟩ : syracuseStep 2712275 = 4068413) B4068413
theorem B1204955 : Blo 1204419 1204955 := bstep (se 1 (by rfl) ⟨903716, by rfl⟩ : syracuseStep 1204955 = 1807433) B1807433
theorem B1205031 : Blo 1204419 1205031 := bstep (se 1 (by rfl) ⟨903773, by rfl⟩ : syracuseStep 1205031 = 1807547) B1807547
theorem B19538761 : Blo 1204419 19538761 := bstep (se 2 (by rfl) ⟨7327035, by rfl⟩ : syracuseStep 19538761 = 14654071) B14654071
theorem B1205071 : Blo 1204419 1205071 := bstep (se 1 (by rfl) ⟨903803, by rfl⟩ : syracuseStep 1205071 = 1807607) B1807607
theorem B1205087 : Blo 1204419 1205087 := bstep (se 1 (by rfl) ⟨903815, by rfl⟩ : syracuseStep 1205087 = 1807631) B1807631
theorem B1205115 : Blo 1204419 1205115 := bstep (se 1 (by rfl) ⟨903836, by rfl⟩ : syracuseStep 1205115 = 1807673) B1807673
theorem B9151379 : Blo 1204419 9151379 := bstep (se 1 (by rfl) ⟨6863534, by rfl⟩ : syracuseStep 9151379 = 13727069) B13727069
theorem B2442145 : Blo 1204419 2442145 := bstep (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) B1831609
theorem B1205167 : Blo 1204419 1205167 := bstep (se 1 (by rfl) ⟨903875, by rfl⟩ : syracuseStep 1205167 = 1807751) B1807751
theorem B4637627 : Blo 1204419 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B1205191 : Blo 1204419 1205191 := bstep (se 1 (by rfl) ⟨903893, by rfl⟩ : syracuseStep 1205191 = 1807787) B1807787
theorem B17384395 : Blo 1204419 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B1205211 : Blo 1204419 1205211 := bstep (se 1 (by rfl) ⟨903908, by rfl⟩ : syracuseStep 1205211 = 1807817) B1807817
theorem B5145601 : Blo 1204419 5145601 := bstep (se 2 (by rfl) ⟨1929600, by rfl⟩ : syracuseStep 5145601 = 3859201) B3859201
theorem B1205287 : Blo 1204419 1205287 := bstep (se 1 (by rfl) ⟨903965, by rfl⟩ : syracuseStep 1205287 = 1807931) B1807931
theorem B1205327 : Blo 1204419 1205327 := bstep (se 1 (by rfl) ⟨903995, by rfl⟩ : syracuseStep 1205327 = 1807991) B1807991
theorem B1205343 : Blo 1204419 1205343 := bstep (se 1 (by rfl) ⟨904007, by rfl⟩ : syracuseStep 1205343 = 1808015) B1808015
theorem B1205371 : Blo 1204419 1205371 := bstep (se 1 (by rfl) ⟨904028, by rfl⟩ : syracuseStep 1205371 = 1808057) B1808057
theorem B1205423 : Blo 1204419 1205423 := bstep (se 1 (by rfl) ⟨904067, by rfl⟩ : syracuseStep 1205423 = 1808135) B1808135
theorem B1205447 : Blo 1204419 1205447 := bstep (se 1 (by rfl) ⟨904085, by rfl⟩ : syracuseStep 1205447 = 1808171) B1808171
theorem B1221851 : Blo 1204419 1221851 := bstep (se 1 (by rfl) ⟨916388, by rfl⟩ : syracuseStep 1221851 = 1832777) B1832777
theorem B1205467 : Blo 1204419 1205467 := bstep (se 1 (by rfl) ⟨904100, by rfl⟩ : syracuseStep 1205467 = 1808201) B1808201
theorem B1205543 : Blo 1204419 1205543 := bstep (se 1 (by rfl) ⟨904157, by rfl⟩ : syracuseStep 1205543 = 1808315) B1808315
theorem B1205583 : Blo 1204419 1205583 := bstep (se 1 (by rfl) ⟨904187, by rfl⟩ : syracuseStep 1205583 = 1808375) B1808375
theorem B1205599 : Blo 1204419 1205599 := bstep (se 1 (by rfl) ⟨904199, by rfl⟩ : syracuseStep 1205599 = 1808399) B1808399
theorem B1205627 : Blo 1204419 1205627 := bstep (se 1 (by rfl) ⟨904220, by rfl⟩ : syracuseStep 1205627 = 1808441) B1808441
theorem B3433853 : Blo 1204419 3433853 := bstep (se 3 (by rfl) ⟨643847, by rfl⟩ : syracuseStep 3433853 = 1287695) B1287695
theorem B2033039 : Blo 1204419 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B1205679 : Blo 1204419 1205679 := bstep (se 1 (by rfl) ⟨904259, by rfl⟩ : syracuseStep 1205679 = 1808519) B1808519
theorem B1205703 : Blo 1204419 1205703 := bstep (se 1 (by rfl) ⟨904277, by rfl⟩ : syracuseStep 1205703 = 1808555) B1808555
theorem B10298825 : Blo 1204419 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B1205723 : Blo 1204419 1205723 := bstep (se 1 (by rfl) ⟨904292, by rfl⟩ : syracuseStep 1205723 = 1808585) B1808585
theorem B7726603 : Blo 1204419 7726603 := bstep (se 1 (by rfl) ⟨5794952, by rfl⟩ : syracuseStep 7726603 = 11589905) B11589905
theorem B1205799 : Blo 1204419 1205799 := bstep (se 1 (by rfl) ⟨904349, by rfl⟩ : syracuseStep 1205799 = 1808699) B1808699
theorem B1205839 : Blo 1204419 1205839 := bstep (se 1 (by rfl) ⟨904379, by rfl⟩ : syracuseStep 1205839 = 1808759) B1808759
theorem B1205855 : Blo 1204419 1205855 := bstep (se 1 (by rfl) ⟨904391, by rfl⟩ : syracuseStep 1205855 = 1808783) B1808783
theorem B2033275 : Blo 1204419 2033275 := bstep (se 1 (by rfl) ⟨1524956, by rfl⟩ : syracuseStep 2033275 = 3049913) B3049913
theorem B2713211 : Blo 1204419 2713211 := bstep (se 1 (by rfl) ⟨2034908, by rfl⟩ : syracuseStep 2713211 = 4069817) B4069817
theorem B1205883 : Blo 1204419 1205883 := bstep (se 1 (by rfl) ⟨904412, by rfl⟩ : syracuseStep 1205883 = 1808825) B1808825
theorem B1205935 : Blo 1204419 1205935 := bstep (se 1 (by rfl) ⟨904451, by rfl⟩ : syracuseStep 1205935 = 1808903) B1808903
theorem B4064957 : Blo 1204419 4064957 := bstep (se 3 (by rfl) ⟨762179, by rfl⟩ : syracuseStep 4064957 = 1524359) B1524359
theorem B1205959 : Blo 1204419 1205959 := bstep (se 1 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 1205959 = 1808939) B1808939
theorem B3434183 : Blo 1204419 3434183 := bstep (se 1 (by rfl) ⟨2575637, by rfl⟩ : syracuseStep 3434183 = 5151275) B5151275
theorem B1205979 : Blo 1204419 1205979 := bstep (se 1 (by rfl) ⟨904484, by rfl⟩ : syracuseStep 1205979 = 1808969) B1808969
theorem B2713337 : Blo 1204419 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B1206055 : Blo 1204419 1206055 := bstep (se 1 (by rfl) ⟨904541, by rfl⟩ : syracuseStep 1206055 = 1809083) B1809083
theorem B1206095 : Blo 1204419 1206095 := bstep (se 1 (by rfl) ⟨904571, by rfl⟩ : syracuseStep 1206095 = 1809143) B1809143
theorem B4065119 : Blo 1204419 4065119 := bstep (se 1 (by rfl) ⟨3048839, by rfl⟩ : syracuseStep 4065119 = 6097679) B6097679
theorem B9152351 : Blo 1204419 9152351 := bstep (se 1 (by rfl) ⟨6864263, by rfl⟩ : syracuseStep 9152351 = 13728527) B13728527
theorem B1206111 : Blo 1204419 1206111 := bstep (se 1 (by rfl) ⟨904583, by rfl⟩ : syracuseStep 1206111 = 1809167) B1809167
theorem B1206139 : Blo 1204419 1206139 := bstep (se 1 (by rfl) ⟨904604, by rfl⟩ : syracuseStep 1206139 = 1809209) B1809209
theorem B1206191 : Blo 1204419 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B1206215 : Blo 1204419 1206215 := bstep (se 1 (by rfl) ⟨904661, by rfl⟩ : syracuseStep 1206215 = 1809323) B1809323
theorem B1206235 : Blo 1204419 1206235 := bstep (se 1 (by rfl) ⟨904676, by rfl⟩ : syracuseStep 1206235 = 1809353) B1809353
theorem B4065281 : Blo 1204419 4065281 := bstep (se 2 (by rfl) ⟨1524480, by rfl⟩ : syracuseStep 4065281 = 3048961) B3048961
theorem B7718915 : Blo 1204419 7718915 := bstep (se 1 (by rfl) ⟨5789186, by rfl⟩ : syracuseStep 7718915 = 11578373) B11578373
theorem B2713607 : Blo 1204419 2713607 := bstep (se 1 (by rfl) ⟨2035205, by rfl⟩ : syracuseStep 2713607 = 4070411) B4070411
theorem B4573199 : Blo 1204419 4573199 := bstep (se 1 (by rfl) ⟨3429899, by rfl⟩ : syracuseStep 4573199 = 6859799) B6859799
theorem B30902309 : Blo 1204419 30902309 := bstep (se 4 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 30902309 = 5794183) B5794183
theorem B1206311 : Blo 1204419 1206311 := bstep (se 1 (by rfl) ⟨904733, by rfl⟩ : syracuseStep 1206311 = 1809467) B1809467
theorem B8685625 : Blo 1204419 8685625 := bstep (se 2 (by rfl) ⟨3257109, by rfl⟩ : syracuseStep 8685625 = 6514219) B6514219
theorem B2173007 : Blo 1204419 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B2713679 : Blo 1204419 2713679 := bstep (se 1 (by rfl) ⟨2035259, by rfl⟩ : syracuseStep 2713679 = 4070519) B4070519
theorem B1206351 : Blo 1204419 1206351 := bstep (se 1 (by rfl) ⟨904763, by rfl⟩ : syracuseStep 1206351 = 1809527) B1809527
theorem B35719261 : Blo 1204419 35719261 := bstep (se 3 (by rfl) ⟨6697361, by rfl⟩ : syracuseStep 35719261 = 13394723) B13394723
theorem B1206367 : Blo 1204419 1206367 := bstep (se 1 (by rfl) ⟨904775, by rfl⟩ : syracuseStep 1206367 = 1809551) B1809551
theorem B2287739 : Blo 1204419 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B1206395 : Blo 1204419 1206395 := bstep (se 1 (by rfl) ⟨904796, by rfl⟩ : syracuseStep 1206395 = 1809593) B1809593
theorem B63473969 : Blo 1204419 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B2034139 : Blo 1204419 2034139 := bstep (se 1 (by rfl) ⟨1525604, by rfl⟩ : syracuseStep 2034139 = 3051209) B3051209
theorem B2714075 : Blo 1204419 2714075 := bstep (se 1 (by rfl) ⟨2035556, by rfl⟩ : syracuseStep 2714075 = 4071113) B4071113
theorem B17369633 : Blo 1204419 17369633 := bstep (se 2 (by rfl) ⟨6513612, by rfl⟩ : syracuseStep 17369633 = 13027225) B13027225
theorem B2288225 : Blo 1204419 2288225 := bstep (se 2 (by rfl) ⟨858084, by rfl⟩ : syracuseStep 2288225 = 1716169) B1716169
theorem B1739387 : Blo 1204419 1739387 := bstep (se 1 (by rfl) ⟨1304540, by rfl⟩ : syracuseStep 1739387 = 2609081) B2609081
theorem B2091691 : Blo 1204419 2091691 := bstep (se 1 (by rfl) ⟨1568768, by rfl⟩ : syracuseStep 2091691 = 3137537) B3137537
theorem B4066091 : Blo 1204419 4066091 := bstep (se 1 (by rfl) ⟨3049568, by rfl⟩ : syracuseStep 4066091 = 6099137) B6099137
theorem B4402039 : Blo 1204419 4402039 := bstep (se 1 (by rfl) ⟨3301529, by rfl⟩ : syracuseStep 4402039 = 6603059) B6603059
theorem B2288567 : Blo 1204419 2288567 := bstep (se 1 (by rfl) ⟨1716425, by rfl⟩ : syracuseStep 2288567 = 3432851) B3432851
theorem B19565495 : Blo 1204419 19565495 := bstep (se 1 (by rfl) ⟨14674121, by rfl⟩ : syracuseStep 19565495 = 29348243) B29348243
theorem B4123649 : Blo 1204419 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B4066361 : Blo 1204419 4066361 := bstep (se 2 (by rfl) ⟨1524885, by rfl⟩ : syracuseStep 4066361 = 3049771) B3049771
theorem B2034767 : Blo 1204419 2034767 := bstep (se 1 (by rfl) ⟨1526075, by rfl⟩ : syracuseStep 2034767 = 3052151) B3052151
theorem B4344947 : Blo 1204419 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B6106265 : Blo 1204419 6106265 := bstep (se 2 (by rfl) ⟨2289849, by rfl⟩ : syracuseStep 6106265 = 4579699) B4579699
theorem B3050743 : Blo 1204419 3050743 := bstep (se 1 (by rfl) ⟨2288057, by rfl⟩ : syracuseStep 3050743 = 4576115) B4576115
theorem B2288969 : Blo 1204419 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B4066685 : Blo 1204419 4066685 := bstep (se 3 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 4066685 = 1525007) B1525007
theorem B4124033 : Blo 1204419 4124033 := bstep (se 2 (by rfl) ⟨1546512, by rfl⟩ : syracuseStep 4124033 = 3093025) B3093025
theorem B3051017 : Blo 1204419 3051017 := bstep (se 2 (by rfl) ⟨1144131, by rfl⟩ : syracuseStep 3051017 = 2288263) B2288263
theorem B14650919 : Blo 1204419 14650919 := bstep (se 1 (by rfl) ⟨10988189, by rfl⟩ : syracuseStep 14650919 = 21976379) B21976379
theorem B3051047 : Blo 1204419 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B4066955 : Blo 1204419 4066955 := bstep (se 1 (by rfl) ⟨3050216, by rfl⟩ : syracuseStep 4066955 = 6100433) B6100433
theorem B3305099 : Blo 1204419 3305099 := bstep (se 1 (by rfl) ⟨2478824, by rfl⟩ : syracuseStep 3305099 = 4957649) B4957649
theorem B3862201 : Blo 1204419 3862201 := bstep (se 2 (by rfl) ⟨1448325, by rfl⟩ : syracuseStep 3862201 = 2896651) B2896651
theorem B3051371 : Blo 1204419 3051371 := bstep (se 1 (by rfl) ⟨2288528, by rfl⟩ : syracuseStep 3051371 = 4577057) B4577057
theorem B3862379 : Blo 1204419 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B8245111 : Blo 1204419 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B2035631 : Blo 1204419 2035631 := bstep (se 1 (by rfl) ⟨1526723, by rfl⟩ : syracuseStep 2035631 = 3053447) B3053447
theorem B2289683 : Blo 1204419 2289683 := bstep (se 1 (by rfl) ⟨1717262, by rfl⟩ : syracuseStep 2289683 = 3434525) B3434525
theorem B2289721 : Blo 1204419 2289721 := bstep (se 2 (by rfl) ⟨858645, by rfl⟩ : syracuseStep 2289721 = 1717291) B1717291
theorem B2576441 : Blo 1204419 2576441 := bstep (se 2 (by rfl) ⟨966165, by rfl⟩ : syracuseStep 2576441 = 1932331) B1932331
theorem B4575311 : Blo 1204419 4575311 := bstep (se 1 (by rfl) ⟨3431483, by rfl⟩ : syracuseStep 4575311 = 6862967) B6862967
theorem B8695889 : Blo 1204419 8695889 := bstep (se 2 (by rfl) ⟨3260958, by rfl⟩ : syracuseStep 8695889 = 6521917) B6521917
theorem B1355899 : Blo 1204419 1355899 := bstep (se 1 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 1355899 = 2033849) B2033849
theorem B5501245 : Blo 1204419 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B2290025 : Blo 1204419 2290025 := bstep (se 2 (by rfl) ⟨858759, by rfl⟩ : syracuseStep 2290025 = 1717519) B1717519
theorem B3912065 : Blo 1204419 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B1806767 : Blo 1204419 1806767 := bstep (se 1 (by rfl) ⟨1355075, by rfl⟩ : syracuseStep 1806767 = 2710151) B2710151
theorem B37097945 : Blo 1204419 37097945 := bstep (se 2 (by rfl) ⟨13911729, by rfl⟩ : syracuseStep 37097945 = 27823459) B27823459
theorem B3052019 : Blo 1204419 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B5788169 : Blo 1204419 5788169 := bstep (se 2 (by rfl) ⟨2170563, by rfl⟩ : syracuseStep 5788169 = 4341127) B4341127
theorem B1806857 : Blo 1204419 1806857 := bstep (se 2 (by rfl) ⟨677571, by rfl⟩ : syracuseStep 1806857 = 1355143) B1355143
theorem B26063369 : Blo 1204419 26063369 := bstep (se 2 (by rfl) ⟨9773763, by rfl⟩ : syracuseStep 26063369 = 19547527) B19547527
theorem B4067873 : Blo 1204419 4067873 := bstep (se 2 (by rfl) ⟨1525452, by rfl⟩ : syracuseStep 4067873 = 3050905) B3050905
theorem B1806887 : Blo 1204419 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B1356367 : Blo 1204419 1356367 := bstep (se 1 (by rfl) ⟨1017275, by rfl⟩ : syracuseStep 1356367 = 2034551) B2034551
theorem B15446645 : Blo 1204419 15446645 := bstep (se 5 (by rfl) ⟨724061, by rfl⟩ : syracuseStep 15446645 = 1448123) B1448123
theorem B1806971 : Blo 1204419 1806971 := bstep (se 1 (by rfl) ⟨1355228, by rfl⟩ : syracuseStep 1806971 = 2710457) B2710457
theorem B24728273 : Blo 1204419 24728273 := bstep (se 2 (by rfl) ⟨9273102, by rfl⟩ : syracuseStep 24728273 = 18546205) B18546205
theorem B1807097 : Blo 1204419 1807097 := bstep (se 2 (by rfl) ⟨677661, by rfl⟩ : syracuseStep 1807097 = 1355323) B1355323
theorem B4068089 : Blo 1204419 4068089 := bstep (se 2 (by rfl) ⟨1525533, by rfl⟩ : syracuseStep 4068089 = 3051067) B3051067
theorem B6099785 : Blo 1204419 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B1807199 : Blo 1204419 1807199 := bstep (se 1 (by rfl) ⟨1355399, by rfl⟩ : syracuseStep 1807199 = 2710799) B2710799
theorem B1807211 : Blo 1204419 1807211 := bstep (se 1 (by rfl) ⟨1355408, by rfl⟩ : syracuseStep 1807211 = 2710817) B2710817
theorem B5223275 : Blo 1204419 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B1930159 : Blo 1204419 1930159 := bstep (se 1 (by rfl) ⟨1447619, by rfl⟩ : syracuseStep 1930159 = 2895239) B2895239
theorem B3052475 : Blo 1204419 3052475 := bstep (se 1 (by rfl) ⟨2289356, by rfl⟩ : syracuseStep 3052475 = 4578713) B4578713
theorem B1356763 : Blo 1204419 1356763 := bstep (se 1 (by rfl) ⟨1017572, by rfl⟩ : syracuseStep 1356763 = 2035145) B2035145
theorem B4068359 : Blo 1204419 4068359 := bstep (se 1 (by rfl) ⟨3051269, by rfl⟩ : syracuseStep 4068359 = 6102539) B6102539
theorem B1807439 : Blo 1204419 1807439 := bstep (se 1 (by rfl) ⟨1355579, by rfl⟩ : syracuseStep 1807439 = 2711159) B2711159
theorem B4068467 : Blo 1204419 4068467 := bstep (se 1 (by rfl) ⟨3051350, by rfl⟩ : syracuseStep 4068467 = 6102701) B6102701
theorem B1807559 : Blo 1204419 1807559 := bstep (se 1 (by rfl) ⟨1355669, by rfl⟩ : syracuseStep 1807559 = 2711339) B2711339
theorem B1807721 : Blo 1204419 1807721 := bstep (se 2 (by rfl) ⟨677895, by rfl⟩ : syracuseStep 1807721 = 1355791) B1355791
theorem B4068737 : Blo 1204419 4068737 := bstep (se 2 (by rfl) ⟨1525776, by rfl⟩ : syracuseStep 4068737 = 3051553) B3051553
theorem B1807799 : Blo 1204419 1807799 := bstep (se 1 (by rfl) ⟨1355849, by rfl⟩ : syracuseStep 1807799 = 2711699) B2711699
theorem B1807835 : Blo 1204419 1807835 := bstep (se 1 (by rfl) ⟨1355876, by rfl⟩ : syracuseStep 1807835 = 2711753) B2711753
theorem B3053153 : Blo 1204419 3053153 := bstep (se 2 (by rfl) ⟨1144932, by rfl⟩ : syracuseStep 3053153 = 2289865) B2289865
theorem B9279197 : Blo 1204419 9279197 := bstep (se 3 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 9279197 = 3479699) B3479699
theorem B19535651 : Blo 1204419 19535651 := bstep (se 1 (by rfl) ⟨14651738, by rfl⟩ : syracuseStep 19535651 = 29303477) B29303477
theorem B10295099 : Blo 1204419 10295099 := bstep (se 1 (by rfl) ⟨7721324, by rfl⟩ : syracuseStep 10295099 = 15442649) B15442649
theorem B4347715 : Blo 1204419 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B1808303 : Blo 1204419 1808303 := bstep (se 1 (by rfl) ⟨1356227, by rfl⟩ : syracuseStep 1808303 = 2712455) B2712455
theorem B9770939 : Blo 1204419 9770939 := bstep (se 1 (by rfl) ⟨7328204, by rfl⟩ : syracuseStep 9770939 = 14656409) B14656409
theorem B1808393 : Blo 1204419 1808393 := bstep (se 2 (by rfl) ⟨678147, by rfl⟩ : syracuseStep 1808393 = 1356295) B1356295
theorem B1808423 : Blo 1204419 1808423 := bstep (se 1 (by rfl) ⟨1356317, by rfl⟩ : syracuseStep 1808423 = 2712635) B2712635
theorem B2897977 : Blo 1204419 2897977 := bstep (se 2 (by rfl) ⟨1086741, by rfl⟩ : syracuseStep 2897977 = 2173483) B2173483
theorem B169187413 : Blo 1204419 169187413 := bstep (se 8 (by rfl) ⟨991332, by rfl⟩ : syracuseStep 169187413 = 1982665) B1982665
theorem B6101081 : Blo 1204419 6101081 := bstep (se 2 (by rfl) ⟨2287905, by rfl⟩ : syracuseStep 6101081 = 4575811) B4575811
theorem B1808507 : Blo 1204419 1808507 := bstep (se 1 (by rfl) ⟨1356380, by rfl⟩ : syracuseStep 1808507 = 2712761) B2712761
theorem B4069547 : Blo 1204419 4069547 := bstep (se 1 (by rfl) ⟨3052160, by rfl⟩ : syracuseStep 4069547 = 6104321) B6104321
theorem B1808633 : Blo 1204419 1808633 := bstep (se 2 (by rfl) ⟨678237, by rfl⟩ : syracuseStep 1808633 = 1356475) B1356475
theorem B6953303 : Blo 1204419 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B1808735 : Blo 1204419 1808735 := bstep (se 1 (by rfl) ⟨1356551, by rfl⟩ : syracuseStep 1808735 = 2713103) B2713103
theorem B1808747 : Blo 1204419 1808747 := bstep (se 1 (by rfl) ⟨1356560, by rfl⟩ : syracuseStep 1808747 = 2713121) B2713121
theorem B4577755 : Blo 1204419 4577755 := bstep (se 1 (by rfl) ⟨3433316, by rfl⟩ : syracuseStep 4577755 = 6866633) B6866633
theorem B2710025 : Blo 1204419 2710025 := bstep (se 2 (by rfl) ⟨1016259, by rfl⟩ : syracuseStep 2710025 = 2032519) B2032519
theorem B3430937 : Blo 1204419 3430937 := bstep (se 2 (by rfl) ⟨1286601, by rfl⟩ : syracuseStep 3430937 = 2573203) B2573203
theorem B41777707 : Blo 1204419 41777707 := bstep (se 1 (by rfl) ⟨31333280, by rfl⟩ : syracuseStep 41777707 = 62666561) B62666561
theorem B1448527 : Blo 1204419 1448527 := bstep (se 1 (by rfl) ⟨1086395, by rfl⟩ : syracuseStep 1448527 = 2172791) B2172791
theorem B1808975 : Blo 1204419 1808975 := bstep (se 1 (by rfl) ⟨1356731, by rfl⟩ : syracuseStep 1808975 = 2713463) B2713463
theorem B4070087 : Blo 1204419 4070087 := bstep (se 1 (by rfl) ⟨3052565, by rfl⟩ : syracuseStep 4070087 = 6105131) B6105131
theorem B1809095 : Blo 1204419 1809095 := bstep (se 1 (by rfl) ⟨1356821, by rfl⟩ : syracuseStep 1809095 = 2713643) B2713643
theorem B2710367 : Blo 1204419 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B1809257 : Blo 1204419 1809257 := bstep (se 2 (by rfl) ⟨678471, by rfl⟩ : syracuseStep 1809257 = 1356943) B1356943
theorem B1809335 : Blo 1204419 1809335 := bstep (se 1 (by rfl) ⟨1357001, by rfl⟩ : syracuseStep 1809335 = 2714003) B2714003
theorem B1809371 : Blo 1204419 1809371 := bstep (se 1 (by rfl) ⟨1357028, by rfl⟩ : syracuseStep 1809371 = 2714057) B2714057
theorem B7527397 : Blo 1204419 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B2710547 : Blo 1204419 2710547 := bstep (se 1 (by rfl) ⟨2032910, by rfl⟩ : syracuseStep 2710547 = 4065821) B4065821
theorem B2710889 : Blo 1204419 2710889 := bstep (se 2 (by rfl) ⟨1016583, by rfl⟩ : syracuseStep 2710889 = 2033167) B2033167
theorem B9158183 : Blo 1204419 9158183 := bstep (se 1 (by rfl) ⟨6868637, by rfl⟩ : syracuseStep 9158183 = 13737275) B13737275
theorem B4070951 : Blo 1204419 4070951 := bstep (se 1 (by rfl) ⟨3053213, by rfl⟩ : syracuseStep 4070951 = 6106427) B6106427
theorem B7724605 : Blo 1204419 7724605 := bstep (se 3 (by rfl) ⟨1448363, by rfl⟩ : syracuseStep 7724605 = 2896727) B2896727
theorem B4071059 : Blo 1204419 4071059 := bstep (se 1 (by rfl) ⟨3053294, by rfl⟩ : syracuseStep 4071059 = 6106589) B6106589
theorem B4579001 : Blo 1204419 4579001 := bstep (se 2 (by rfl) ⟨1717125, by rfl⟩ : syracuseStep 4579001 = 3434251) B3434251
theorem B4579031 : Blo 1204419 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B3260267 : Blo 1204419 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B4071275 : Blo 1204419 4071275 := bstep (se 1 (by rfl) ⟨3053456, by rfl⟩ : syracuseStep 4071275 = 6106913) B6106913
theorem B4071329 : Blo 1204419 4071329 := bstep (se 2 (by rfl) ⟨1526748, by rfl⟩ : syracuseStep 4071329 = 3053497) B3053497
theorem B2711483 : Blo 1204419 2711483 := bstep (se 1 (by rfl) ⟨2033612, by rfl⟩ : syracuseStep 2711483 = 4067225) B4067225
theorem B225583217 : Blo 1204419 225583217 := bstep (se 2 (by rfl) ⟨84593706, by rfl⟩ : syracuseStep 225583217 = 169187413) B169187413
theorem B1204511 : Blo 1204419 1204511 := bstep (se 1 (by rfl) ⟨903383, by rfl⟩ : syracuseStep 1204511 = 1806767) B1806767
theorem B24731963 : Blo 1204419 24731963 := bstep (se 1 (by rfl) ⟨18548972, by rfl⟩ : syracuseStep 24731963 = 37097945) B37097945
theorem B3858779 : Blo 1204419 3858779 := bstep (se 1 (by rfl) ⟨2894084, by rfl⟩ : syracuseStep 3858779 = 5788169) B5788169
theorem B1204571 : Blo 1204419 1204571 := bstep (se 1 (by rfl) ⟨903428, by rfl⟩ : syracuseStep 1204571 = 1806857) B1806857
theorem B17375579 : Blo 1204419 17375579 := bstep (se 1 (by rfl) ⟨13031684, by rfl⟩ : syracuseStep 17375579 = 26063369) B26063369
theorem B2711915 : Blo 1204419 2711915 := bstep (se 1 (by rfl) ⟨2033936, by rfl⟩ : syracuseStep 2711915 = 4067873) B4067873
theorem B1204591 : Blo 1204419 1204591 := bstep (se 1 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 1204591 = 1806887) B1806887
theorem B10297763 : Blo 1204419 10297763 := bstep (se 1 (by rfl) ⟨7723322, by rfl⟩ : syracuseStep 10297763 = 15446645) B15446645
theorem B1204647 : Blo 1204419 1204647 := bstep (se 1 (by rfl) ⟨903485, by rfl⟩ : syracuseStep 1204647 = 1806971) B1806971
theorem B1204731 : Blo 1204419 1204731 := bstep (se 1 (by rfl) ⟨903548, by rfl⟩ : syracuseStep 1204731 = 1807097) B1807097
theorem B2712059 : Blo 1204419 2712059 := bstep (se 1 (by rfl) ⟨2034044, by rfl⟩ : syracuseStep 2712059 = 4068089) B4068089
theorem B1204799 : Blo 1204419 1204799 := bstep (se 1 (by rfl) ⟨903599, by rfl⟩ : syracuseStep 1204799 = 1807199) B1807199
theorem B1204807 : Blo 1204419 1204807 := bstep (se 1 (by rfl) ⟨903605, by rfl⟩ : syracuseStep 1204807 = 1807211) B1807211
theorem B3482183 : Blo 1204419 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B2712185 : Blo 1204419 2712185 := bstep (se 2 (by rfl) ⟨1017069, by rfl⟩ : syracuseStep 2712185 = 2034139) B2034139
theorem B6103673 : Blo 1204419 6103673 := bstep (se 2 (by rfl) ⟨2288877, by rfl⟩ : syracuseStep 6103673 = 4577755) B4577755
theorem B2712239 : Blo 1204419 2712239 := bstep (se 1 (by rfl) ⟨2034179, by rfl⟩ : syracuseStep 2712239 = 4068359) B4068359
theorem B1204959 : Blo 1204419 1204959 := bstep (se 1 (by rfl) ⟨903719, by rfl⟩ : syracuseStep 1204959 = 1807439) B1807439
theorem B2712311 : Blo 1204419 2712311 := bstep (se 1 (by rfl) ⟨2034233, by rfl⟩ : syracuseStep 2712311 = 4068467) B4068467
theorem B1205039 : Blo 1204419 1205039 := bstep (se 1 (by rfl) ⟨903779, by rfl⟩ : syracuseStep 1205039 = 1807559) B1807559
theorem B1205147 : Blo 1204419 1205147 := bstep (se 1 (by rfl) ⟨903860, by rfl⟩ : syracuseStep 1205147 = 1807721) B1807721
theorem B2712491 : Blo 1204419 2712491 := bstep (se 1 (by rfl) ⟨2034368, by rfl⟩ : syracuseStep 2712491 = 4068737) B4068737
theorem B1205199 : Blo 1204419 1205199 := bstep (se 1 (by rfl) ⟨903899, by rfl⟩ : syracuseStep 1205199 = 1807799) B1807799
theorem B6865883 : Blo 1204419 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B1205223 : Blo 1204419 1205223 := bstep (se 1 (by rfl) ⟨903917, by rfl⟩ : syracuseStep 1205223 = 1807835) B1807835
theorem B26051681 : Blo 1204419 26051681 := bstep (se 2 (by rfl) ⟨9769380, by rfl⟩ : syracuseStep 26051681 = 19538761) B19538761
theorem B6186131 : Blo 1204419 6186131 := bstep (se 1 (by rfl) ⟨4639598, by rfl⟩ : syracuseStep 6186131 = 9279197) B9279197
theorem B2573545 : Blo 1204419 2573545 := bstep (se 2 (by rfl) ⟨965079, by rfl⟩ : syracuseStep 2573545 = 1930159) B1930159
theorem B1205535 : Blo 1204419 1205535 := bstep (se 1 (by rfl) ⟨904151, by rfl⟩ : syracuseStep 1205535 = 1808303) B1808303
theorem B6513959 : Blo 1204419 6513959 := bstep (se 1 (by rfl) ⟨4885469, by rfl⟩ : syracuseStep 6513959 = 9770939) B9770939
theorem B10036529 : Blo 1204419 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B5145943 : Blo 1204419 5145943 := bstep (se 1 (by rfl) ⟨3859457, by rfl⟩ : syracuseStep 5145943 = 7718915) B7718915
theorem B1205595 : Blo 1204419 1205595 := bstep (se 1 (by rfl) ⟨904196, by rfl⟩ : syracuseStep 1205595 = 1808393) B1808393
theorem B3048799 : Blo 1204419 3048799 := bstep (se 1 (by rfl) ⟨2286599, by rfl⟩ : syracuseStep 3048799 = 4573199) B4573199
theorem B1205615 : Blo 1204419 1205615 := bstep (se 1 (by rfl) ⟨904211, by rfl⟩ : syracuseStep 1205615 = 1808423) B1808423
theorem B1525159 : Blo 1204419 1525159 := bstep (se 1 (by rfl) ⟨1143869, by rfl⟩ : syracuseStep 1525159 = 2287739) B2287739
theorem B1205671 : Blo 1204419 1205671 := bstep (se 1 (by rfl) ⟨904253, by rfl⟩ : syracuseStep 1205671 = 1808507) B1808507
theorem B2713031 : Blo 1204419 2713031 := bstep (se 1 (by rfl) ⟨2034773, by rfl⟩ : syracuseStep 2713031 = 4069547) B4069547
theorem B1205755 : Blo 1204419 1205755 := bstep (se 1 (by rfl) ⟨904316, by rfl⟩ : syracuseStep 1205755 = 1808633) B1808633
theorem B1205823 : Blo 1204419 1205823 := bstep (se 1 (by rfl) ⟨904367, by rfl⟩ : syracuseStep 1205823 = 1808735) B1808735
theorem B1205831 : Blo 1204419 1205831 := bstep (se 1 (by rfl) ⟨904373, by rfl⟩ : syracuseStep 1205831 = 1808747) B1808747
theorem B4638365 : Blo 1204419 4638365 := bstep (se 3 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 4638365 = 1739387) B1739387
theorem B2287291 : Blo 1204419 2287291 := bstep (se 1 (by rfl) ⟨1715468, by rfl⟩ : syracuseStep 2287291 = 3430937) B3430937
theorem B1205983 : Blo 1204419 1205983 := bstep (se 1 (by rfl) ⟨904487, by rfl⟩ : syracuseStep 1205983 = 1808975) B1808975
theorem B1525483 : Blo 1204419 1525483 := bstep (se 1 (by rfl) ⟨1144112, by rfl⟩ : syracuseStep 1525483 = 2288225) B2288225
theorem B2713391 : Blo 1204419 2713391 := bstep (se 1 (by rfl) ⟨2035043, by rfl⟩ : syracuseStep 2713391 = 4070087) B4070087
theorem B1206063 : Blo 1204419 1206063 := bstep (se 1 (by rfl) ⟨904547, by rfl⟩ : syracuseStep 1206063 = 1809095) B1809095
theorem B1206171 : Blo 1204419 1206171 := bstep (se 1 (by rfl) ⟨904628, by rfl⟩ : syracuseStep 1206171 = 1809257) B1809257
theorem B1525711 : Blo 1204419 1525711 := bstep (se 1 (by rfl) ⟨1144283, by rfl⟩ : syracuseStep 1525711 = 2288567) B2288567
theorem B1206223 : Blo 1204419 1206223 := bstep (se 1 (by rfl) ⟨904667, by rfl⟩ : syracuseStep 1206223 = 1809335) B1809335
theorem B13043663 : Blo 1204419 13043663 := bstep (se 1 (by rfl) ⟨9782747, by rfl⟩ : syracuseStep 13043663 = 19565495) B19565495
theorem B1206247 : Blo 1204419 1206247 := bstep (se 1 (by rfl) ⟨904685, by rfl⟩ : syracuseStep 1206247 = 1809371) B1809371
theorem B10299473 : Blo 1204419 10299473 := bstep (se 2 (by rfl) ⟨3862302, by rfl⟩ : syracuseStep 10299473 = 7724605) B7724605
theorem B1525979 : Blo 1204419 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B2034011 : Blo 1204419 2034011 := bstep (se 1 (by rfl) ⟨1525508, by rfl⟩ : syracuseStep 2034011 = 3051017) B3051017
theorem B9767279 : Blo 1204419 9767279 := bstep (se 1 (by rfl) ⟨7325459, by rfl⟩ : syracuseStep 9767279 = 14650919) B14650919
theorem B2034031 : Blo 1204419 2034031 := bstep (se 1 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 2034031 = 3051047) B3051047
theorem B6105455 : Blo 1204419 6105455 := bstep (se 1 (by rfl) ⟨4579091, by rfl⟩ : syracuseStep 6105455 = 9158183) B9158183
theorem B2713967 : Blo 1204419 2713967 := bstep (se 1 (by rfl) ⟨2035475, by rfl⟩ : syracuseStep 2713967 = 4070951) B4070951
theorem B2714039 : Blo 1204419 2714039 := bstep (se 1 (by rfl) ⟨2035529, by rfl⟩ : syracuseStep 2714039 = 4071059) B4071059
theorem B2034247 : Blo 1204419 2034247 := bstep (se 1 (by rfl) ⟨1525685, by rfl⟩ : syracuseStep 2034247 = 3051371) B3051371
theorem B2574919 : Blo 1204419 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B2173511 : Blo 1204419 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B2714183 : Blo 1204419 2714183 := bstep (se 1 (by rfl) ⟨2035637, by rfl⟩ : syracuseStep 2714183 = 4071275) B4071275
theorem B2714219 : Blo 1204419 2714219 := bstep (se 1 (by rfl) ⟨2035664, by rfl⟩ : syracuseStep 2714219 = 4071329) B4071329
theorem B10996397 : Blo 1204419 10996397 := bstep (se 3 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 10996397 = 4123649) B4123649
theorem B1526455 : Blo 1204419 1526455 := bstep (se 1 (by rfl) ⟨1144841, by rfl⟩ : syracuseStep 1526455 = 2289683) B2289683
theorem B3050207 : Blo 1204419 3050207 := bstep (se 1 (by rfl) ⟨2287655, by rfl⟩ : syracuseStep 3050207 = 4575311) B4575311
theorem B12069665 : Blo 1204419 12069665 := bstep (se 2 (by rfl) ⟨4526124, by rfl⟩ : syracuseStep 12069665 = 9052249) B9052249
theorem B5794685 : Blo 1204419 5794685 := bstep (se 3 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 5794685 = 2173007) B2173007
theorem B1526683 : Blo 1204419 1526683 := bstep (se 1 (by rfl) ⟨1145012, by rfl⟩ : syracuseStep 1526683 = 2290025) B2290025
theorem B2608043 : Blo 1204419 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B2034679 : Blo 1204419 2034679 := bstep (se 1 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 2034679 = 3052019) B3052019
theorem B7334993 : Blo 1204419 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B16485515 : Blo 1204419 16485515 := bstep (se 1 (by rfl) ⟨12364136, by rfl⟩ : syracuseStep 16485515 = 24728273) B24728273
theorem B4066523 : Blo 1204419 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B3091751 : Blo 1204419 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B2034983 : Blo 1204419 2034983 := bstep (se 1 (by rfl) ⟨1526237, by rfl⟩ : syracuseStep 2034983 = 3052475) B3052475
theorem B2788921 : Blo 1204419 2788921 := bstep (se 2 (by rfl) ⟨1045845, by rfl⟩ : syracuseStep 2788921 = 2091691) B2091691
theorem B2289235 : Blo 1204419 2289235 := bstep (se 1 (by rfl) ⟨1716926, by rfl⟩ : syracuseStep 2289235 = 3433853) B3433853
theorem B1355359 : Blo 1204419 1355359 := bstep (se 1 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 1355359 = 2033039) B2033039
theorem B3255965 : Blo 1204419 3255965 := bstep (se 3 (by rfl) ⟨610493, by rfl⟩ : syracuseStep 3255965 = 1220987) B1220987
theorem B2035435 : Blo 1204419 2035435 := bstep (se 1 (by rfl) ⟨1526576, by rfl⟩ : syracuseStep 2035435 = 3053153) B3053153
theorem B2289455 : Blo 1204419 2289455 := bstep (se 1 (by rfl) ⟨1717091, by rfl⟩ : syracuseStep 2289455 = 3434183) B3434183
theorem B5869385 : Blo 1204419 5869385 := bstep (se 2 (by rfl) ⟨2201019, by rfl⟩ : syracuseStep 5869385 = 4402039) B4402039
theorem B3256193 : Blo 1204419 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B23179193 : Blo 1204419 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B6860801 : Blo 1204419 6860801 := bstep (se 2 (by rfl) ⟨2572800, by rfl⟩ : syracuseStep 6860801 = 5145601) B5145601
theorem B4067387 : Blo 1204419 4067387 := bstep (se 1 (by rfl) ⟨3050540, by rfl⟩ : syracuseStep 4067387 = 6101081) B6101081
theorem B42315979 : Blo 1204419 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B4067657 : Blo 1204419 4067657 := bstep (se 2 (by rfl) ⟨1525371, by rfl⟩ : syracuseStep 4067657 = 3050743) B3050743
theorem B1806683 : Blo 1204419 1806683 := bstep (se 1 (by rfl) ⟨1355012, by rfl⟩ : syracuseStep 1806683 = 2710025) B2710025
theorem B11579755 : Blo 1204419 11579755 := bstep (se 1 (by rfl) ⟨8684816, by rfl⟩ : syracuseStep 11579755 = 17369633) B17369633
theorem B1806911 : Blo 1204419 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B1807031 : Blo 1204419 1807031 := bstep (se 1 (by rfl) ⟨1355273, by rfl⟩ : syracuseStep 1807031 = 2710547) B2710547
theorem B10302137 : Blo 1204419 10302137 := bstep (se 2 (by rfl) ⟨3863301, by rfl⟩ : syracuseStep 10302137 = 7726603) B7726603
theorem B1356511 : Blo 1204419 1356511 := bstep (se 1 (by rfl) ⟨1017383, by rfl⟩ : syracuseStep 1356511 = 2034767) B2034767
theorem B2896631 : Blo 1204419 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B1807259 : Blo 1204419 1807259 := bstep (se 1 (by rfl) ⟨1355444, by rfl⟩ : syracuseStep 1807259 = 2710889) B2710889
theorem B5149601 : Blo 1204419 5149601 := bstep (se 2 (by rfl) ⟨1931100, by rfl⟩ : syracuseStep 5149601 = 3862201) B3862201
theorem B2749355 : Blo 1204419 2749355 := bstep (se 1 (by rfl) ⟨2062016, by rfl⟩ : syracuseStep 2749355 = 4124033) B4124033
theorem B5796953 : Blo 1204419 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B3052667 : Blo 1204419 3052667 := bstep (se 1 (by rfl) ⟨2289500, by rfl⟩ : syracuseStep 3052667 = 4579001) B4579001
theorem B3052687 : Blo 1204419 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B1357087 : Blo 1204419 1357087 := bstep (se 1 (by rfl) ⟨1017815, by rfl⟩ : syracuseStep 1357087 = 2035631) B2035631
theorem B1807655 : Blo 1204419 1807655 := bstep (se 1 (by rfl) ⟨1355741, by rfl⟩ : syracuseStep 1807655 = 2711483) B2711483
theorem B1807739 : Blo 1204419 1807739 := bstep (se 1 (by rfl) ⟨1355804, by rfl⟩ : syracuseStep 1807739 = 2711609) B2711609
theorem B1717627 : Blo 1204419 1717627 := bstep (se 1 (by rfl) ⟨1288220, by rfl⟩ : syracuseStep 1717627 = 2576441) B2576441
theorem B5797259 : Blo 1204419 5797259 := bstep (se 1 (by rfl) ⟨4347944, by rfl⟩ : syracuseStep 5797259 = 8695889) B8695889
theorem B11580833 : Blo 1204419 11580833 := bstep (se 2 (by rfl) ⟨4342812, by rfl⟩ : syracuseStep 11580833 = 8685625) B8685625
theorem B3052961 : Blo 1204419 3052961 := bstep (se 2 (by rfl) ⟨1144860, by rfl⟩ : syracuseStep 3052961 = 2289721) B2289721
theorem B3863969 : Blo 1204419 3863969 := bstep (se 2 (by rfl) ⟨1448988, by rfl⟩ : syracuseStep 3863969 = 2897977) B2897977
theorem B1807865 : Blo 1204419 1807865 := bstep (se 2 (by rfl) ⟨677949, by rfl⟩ : syracuseStep 1807865 = 1355899) B1355899
theorem B7722503 : Blo 1204419 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B1807967 : Blo 1204419 1807967 := bstep (se 1 (by rfl) ⟨1355975, by rfl⟩ : syracuseStep 1807967 = 2711951) B2711951
theorem B59463353 : Blo 1204419 59463353 := bstep (se 2 (by rfl) ⟨22298757, by rfl⟩ : syracuseStep 59463353 = 44597515) B44597515
theorem B5789495 : Blo 1204419 5789495 := bstep (se 1 (by rfl) ⟨4342121, by rfl⟩ : syracuseStep 5789495 = 8684243) B8684243
theorem B1447735 : Blo 1204419 1447735 := bstep (se 1 (by rfl) ⟨1085801, by rfl⟩ : syracuseStep 1447735 = 2171603) B2171603
theorem B1808183 : Blo 1204419 1808183 := bstep (se 1 (by rfl) ⟨1356137, by rfl⟩ : syracuseStep 1808183 = 2712275) B2712275
theorem B190502725 : Blo 1204419 190502725 := bstep (se 4 (by rfl) ⟨17859630, by rfl⟩ : syracuseStep 190502725 = 35719261) B35719261
theorem B3258269 : Blo 1204419 3258269 := bstep (se 3 (by rfl) ⟨610925, by rfl⟩ : syracuseStep 3258269 = 1221851) B1221851
theorem B6100919 : Blo 1204419 6100919 := bstep (se 1 (by rfl) ⟨4575689, by rfl⟩ : syracuseStep 6100919 = 9151379) B9151379
theorem B55703609 : Blo 1204419 55703609 := bstep (se 2 (by rfl) ⟨20888853, by rfl⟩ : syracuseStep 55703609 = 41777707) B41777707
theorem B1808489 : Blo 1204419 1808489 := bstep (se 2 (by rfl) ⟨678183, by rfl⟩ : syracuseStep 1808489 = 1356367) B1356367
theorem B1931369 : Blo 1204419 1931369 := bstep (se 2 (by rfl) ⟨724263, by rfl⟩ : syracuseStep 1931369 = 1448527) B1448527
theorem B1808807 : Blo 1204419 1808807 := bstep (se 1 (by rfl) ⟨1356605, by rfl⟩ : syracuseStep 1808807 = 2713211) B2713211
theorem B2709971 : Blo 1204419 2709971 := bstep (se 1 (by rfl) ⟨2032478, by rfl⟩ : syracuseStep 2709971 = 4064957) B4064957
theorem B1808891 : Blo 1204419 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B13023767 : Blo 1204419 13023767 := bstep (se 1 (by rfl) ⟨9767825, by rfl⟩ : syracuseStep 13023767 = 19535651) B19535651
theorem B6863399 : Blo 1204419 6863399 := bstep (se 1 (by rfl) ⟨5147549, by rfl⟩ : syracuseStep 6863399 = 10295099) B10295099
theorem B2710079 : Blo 1204419 2710079 := bstep (se 1 (by rfl) ⟨2032559, by rfl⟩ : syracuseStep 2710079 = 4065119) B4065119
theorem B6101567 : Blo 1204419 6101567 := bstep (se 1 (by rfl) ⟨4576175, by rfl⟩ : syracuseStep 6101567 = 9152351) B9152351
theorem B1809017 : Blo 1204419 1809017 := bstep (se 2 (by rfl) ⟨678381, by rfl⟩ : syracuseStep 1809017 = 1356763) B1356763
theorem B2710187 : Blo 1204419 2710187 := bstep (se 1 (by rfl) ⟨2032640, by rfl⟩ : syracuseStep 2710187 = 4065281) B4065281
theorem B1809071 : Blo 1204419 1809071 := bstep (se 1 (by rfl) ⟨1356803, by rfl⟩ : syracuseStep 1809071 = 2713607) B2713607
theorem B20601539 : Blo 1204419 20601539 := bstep (se 1 (by rfl) ⟨15451154, by rfl⟩ : syracuseStep 20601539 = 30902309) B30902309
theorem B1809119 : Blo 1204419 1809119 := bstep (se 1 (by rfl) ⟨1356839, by rfl⟩ : syracuseStep 1809119 = 2713679) B2713679
theorem B4635535 : Blo 1204419 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B1809383 : Blo 1204419 1809383 := bstep (se 1 (by rfl) ⟨1357037, by rfl⟩ : syracuseStep 1809383 = 2714075) B2714075
theorem B2710727 : Blo 1204419 2710727 := bstep (se 1 (by rfl) ⟨2033045, by rfl⟩ : syracuseStep 2710727 = 4066091) B4066091
theorem B2710907 : Blo 1204419 2710907 := bstep (se 1 (by rfl) ⟨2033180, by rfl⟩ : syracuseStep 2710907 = 4066361) B4066361
theorem B4070843 : Blo 1204419 4070843 := bstep (se 1 (by rfl) ⟨3053132, by rfl⟩ : syracuseStep 4070843 = 6106265) B6106265
theorem B2711033 : Blo 1204419 2711033 := bstep (se 2 (by rfl) ⟨1016637, by rfl⟩ : syracuseStep 2711033 = 2033275) B2033275
theorem B2711123 : Blo 1204419 2711123 := bstep (se 1 (by rfl) ⟨2033342, by rfl⟩ : syracuseStep 2711123 = 4066685) B4066685
theorem B2711303 : Blo 1204419 2711303 := bstep (se 1 (by rfl) ⟨2033477, by rfl⟩ : syracuseStep 2711303 = 4066955) B4066955
theorem B2203399 : Blo 1204419 2203399 := bstep (se 1 (by rfl) ⟨1652549, by rfl⟩ : syracuseStep 2203399 = 3305099) B3305099
theorem B10993481 : Blo 1204419 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B2711591 : Blo 1204419 2711591 := bstep (se 1 (by rfl) ⟨2033693, by rfl⟩ : syracuseStep 2711591 = 4067387) B4067387
theorem B150388811 : Blo 1204419 150388811 := bstep (se 1 (by rfl) ⟨112791608, by rfl⟩ : syracuseStep 150388811 = 225583217) B225583217
theorem B2711771 : Blo 1204419 2711771 := bstep (se 1 (by rfl) ⟨2033828, by rfl⟩ : syracuseStep 2711771 = 4067657) B4067657
theorem B1204455 : Blo 1204419 1204455 := bstep (se 1 (by rfl) ⟨903341, by rfl⟩ : syracuseStep 1204455 = 1806683) B1806683
theorem B11583719 : Blo 1204419 11583719 := bstep (se 1 (by rfl) ⟨8687789, by rfl⟩ : syracuseStep 11583719 = 17375579) B17375579
theorem B6865175 : Blo 1204419 6865175 := bstep (se 1 (by rfl) ⟨5148881, by rfl⟩ : syracuseStep 6865175 = 10297763) B10297763
theorem B1204607 : Blo 1204419 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B1204687 : Blo 1204419 1204687 := bstep (se 1 (by rfl) ⟨903515, by rfl⟩ : syracuseStep 1204687 = 1807031) B1807031
theorem B2712041 : Blo 1204419 2712041 := bstep (se 2 (by rfl) ⟨1017015, by rfl⟩ : syracuseStep 2712041 = 2034031) B2034031
theorem B1204839 : Blo 1204419 1204839 := bstep (se 1 (by rfl) ⟨903629, by rfl⟩ : syracuseStep 1204839 = 1807259) B1807259
theorem B3433067 : Blo 1204419 3433067 := bstep (se 1 (by rfl) ⟨2574800, by rfl⟩ : syracuseStep 3433067 = 5149601) B5149601
theorem B17367787 : Blo 1204419 17367787 := bstep (se 1 (by rfl) ⟨13025840, by rfl⟩ : syracuseStep 17367787 = 26051681) B26051681
theorem B2712329 : Blo 1204419 2712329 := bstep (se 2 (by rfl) ⟨1017123, by rfl⟩ : syracuseStep 2712329 = 2034247) B2034247
theorem B1205103 : Blo 1204419 1205103 := bstep (se 1 (by rfl) ⟨903827, by rfl⟩ : syracuseStep 1205103 = 1807655) B1807655
theorem B10290077 : Blo 1204419 10290077 := bstep (se 3 (by rfl) ⟨1929389, by rfl⟩ : syracuseStep 10290077 = 3858779) B3858779
theorem B1205159 : Blo 1204419 1205159 := bstep (se 1 (by rfl) ⟨903869, by rfl⟩ : syracuseStep 1205159 = 1807739) B1807739
theorem B1205243 : Blo 1204419 1205243 := bstep (se 1 (by rfl) ⟨903932, by rfl⟩ : syracuseStep 1205243 = 1807865) B1807865
theorem B1205311 : Blo 1204419 1205311 := bstep (se 1 (by rfl) ⟨903983, by rfl⟩ : syracuseStep 1205311 = 1807967) B1807967
theorem B3859663 : Blo 1204419 3859663 := bstep (se 1 (by rfl) ⟨2894747, by rfl⟩ : syracuseStep 3859663 = 5789495) B5789495
theorem B1205455 : Blo 1204419 1205455 := bstep (se 1 (by rfl) ⟨904091, by rfl⟩ : syracuseStep 1205455 = 1808183) B1808183
theorem B2172179 : Blo 1204419 2172179 := bstep (se 1 (by rfl) ⟨1629134, by rfl⟩ : syracuseStep 2172179 = 3258269) B3258269
theorem B2712905 : Blo 1204419 2712905 := bstep (se 2 (by rfl) ⟨1017339, by rfl⟩ : syracuseStep 2712905 = 2034679) B2034679
theorem B37135739 : Blo 1204419 37135739 := bstep (se 1 (by rfl) ⟨27851804, by rfl⟩ : syracuseStep 37135739 = 55703609) B55703609
theorem B6866315 : Blo 1204419 6866315 := bstep (se 1 (by rfl) ⟨5149736, by rfl⟩ : syracuseStep 6866315 = 10299473) B10299473
theorem B1205659 : Blo 1204419 1205659 := bstep (se 1 (by rfl) ⟨904244, by rfl⟩ : syracuseStep 1205659 = 1808489) B1808489
theorem B1205871 : Blo 1204419 1205871 := bstep (se 1 (by rfl) ⟨904403, by rfl⟩ : syracuseStep 1205871 = 1808807) B1808807
theorem B1205927 : Blo 1204419 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B1206011 : Blo 1204419 1206011 := bstep (se 1 (by rfl) ⟨904508, by rfl⟩ : syracuseStep 1206011 = 1809017) B1809017
theorem B1206047 : Blo 1204419 1206047 := bstep (se 1 (by rfl) ⟨904535, by rfl⟩ : syracuseStep 1206047 = 1809071) B1809071
theorem B4065065 : Blo 1204419 4065065 := bstep (se 2 (by rfl) ⟨1524399, by rfl⟩ : syracuseStep 4065065 = 3048799) B3048799
theorem B2033471 : Blo 1204419 2033471 := bstep (se 1 (by rfl) ⟨1525103, by rfl⟩ : syracuseStep 2033471 = 3050207) B3050207
theorem B1206079 : Blo 1204419 1206079 := bstep (se 1 (by rfl) ⟨904559, by rfl⟩ : syracuseStep 1206079 = 1809119) B1809119
theorem B8046443 : Blo 1204419 8046443 := bstep (se 1 (by rfl) ⟨6034832, by rfl⟩ : syracuseStep 8046443 = 12069665) B12069665
theorem B2033545 : Blo 1204419 2033545 := bstep (se 2 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 2033545 = 1525159) B1525159
theorem B1206255 : Blo 1204419 1206255 := bstep (se 1 (by rfl) ⟨904691, by rfl⟩ : syracuseStep 1206255 = 1809383) B1809383
theorem B3049721 : Blo 1204419 3049721 := bstep (se 2 (by rfl) ⟨1143645, by rfl⟩ : syracuseStep 3049721 = 2287291) B2287291
theorem B2713895 : Blo 1204419 2713895 := bstep (se 1 (by rfl) ⟨2035421, by rfl⟩ : syracuseStep 2713895 = 4070843) B4070843
theorem B2033977 : Blo 1204419 2033977 := bstep (se 2 (by rfl) ⟨762741, by rfl⟩ : syracuseStep 2033977 = 1525483) B1525483
theorem B2713913 : Blo 1204419 2713913 := bstep (se 2 (by rfl) ⟨1017717, by rfl⟩ : syracuseStep 2713913 = 2035435) B2035435
theorem B254003633 : Blo 1204419 254003633 := bstep (se 2 (by rfl) ⟨95251362, by rfl⟩ : syracuseStep 254003633 = 190502725) B190502725
theorem B1526303 : Blo 1204419 1526303 := bstep (se 1 (by rfl) ⟨1144727, by rfl⟩ : syracuseStep 1526303 = 2289455) B2289455
theorem B2034281 : Blo 1204419 2034281 := bstep (se 2 (by rfl) ⟨762855, by rfl⟩ : syracuseStep 2034281 = 1525711) B1525711
theorem B15452795 : Blo 1204419 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B4573867 : Blo 1204419 4573867 := bstep (se 1 (by rfl) ⟨3430400, by rfl⟩ : syracuseStep 4573867 = 6860801) B6860801
theorem B56421305 : Blo 1204419 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B13732901 : Blo 1204419 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B2321455 : Blo 1204419 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B6868091 : Blo 1204419 6868091 := bstep (se 1 (by rfl) ⟨5151068, by rfl⟩ : syracuseStep 6868091 = 10302137) B10302137
theorem B2035111 : Blo 1204419 2035111 := bstep (se 1 (by rfl) ⟨1526333, by rfl⟩ : syracuseStep 2035111 = 3052667) B3052667
theorem B4124087 : Blo 1204419 4124087 := bstep (se 1 (by rfl) ⟨3093065, by rfl⟩ : syracuseStep 4124087 = 6186131) B6186131
theorem B17370557 : Blo 1204419 17370557 := bstep (se 3 (by rfl) ⟨3256979, by rfl⟩ : syracuseStep 17370557 = 6513959) B6513959
theorem B2035273 : Blo 1204419 2035273 := bstep (se 2 (by rfl) ⟨763227, by rfl⟩ : syracuseStep 2035273 = 1526455) B1526455
theorem B7720555 : Blo 1204419 7720555 := bstep (se 1 (by rfl) ⟨5790416, by rfl⟩ : syracuseStep 7720555 = 11580833) B11580833
theorem B2035307 : Blo 1204419 2035307 := bstep (se 1 (by rfl) ⟨1526480, by rfl⟩ : syracuseStep 2035307 = 3052961) B3052961
theorem B2575979 : Blo 1204419 2575979 := bstep (se 1 (by rfl) ⟨1931984, by rfl⟩ : syracuseStep 2575979 = 3863969) B3863969
theorem B5148335 : Blo 1204419 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B3092243 : Blo 1204419 3092243 := bstep (se 1 (by rfl) ⟨2319182, by rfl⟩ : syracuseStep 3092243 = 4638365) B4638365
theorem B6180713 : Blo 1204419 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B2035577 : Blo 1204419 2035577 := bstep (se 2 (by rfl) ⟨763341, by rfl⟩ : syracuseStep 2035577 = 1526683) B1526683
theorem B4067279 : Blo 1204419 4067279 := bstep (se 1 (by rfl) ⟨3050459, by rfl⟩ : syracuseStep 4067279 = 6100919) B6100919
theorem B8695775 : Blo 1204419 8695775 := bstep (se 1 (by rfl) ⟨6521831, by rfl⟩ : syracuseStep 8695775 = 13043663) B13043663
theorem B5796029 : Blo 1204419 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B1356007 : Blo 1204419 1356007 := bstep (se 1 (by rfl) ⟨1017005, by rfl⟩ : syracuseStep 1356007 = 2034011) B2034011
theorem B1806647 : Blo 1204419 1806647 := bstep (se 1 (by rfl) ⟨1354985, by rfl⟩ : syracuseStep 1806647 = 2709971) B2709971
theorem B4575599 : Blo 1204419 4575599 := bstep (se 1 (by rfl) ⟨3431699, by rfl⟩ : syracuseStep 4575599 = 6863399) B6863399
theorem B1806719 : Blo 1204419 1806719 := bstep (se 1 (by rfl) ⟨1355039, by rfl⟩ : syracuseStep 1806719 = 2710079) B2710079
theorem B4067711 : Blo 1204419 4067711 := bstep (se 1 (by rfl) ⟨3050783, by rfl⟩ : syracuseStep 4067711 = 6101567) B6101567
theorem B1806791 : Blo 1204419 1806791 := bstep (se 1 (by rfl) ⟨1355093, by rfl⟩ : syracuseStep 1806791 = 2710187) B2710187
theorem B6861257 : Blo 1204419 6861257 := bstep (se 2 (by rfl) ⟨2572971, by rfl⟩ : syracuseStep 6861257 = 5145943) B5145943
theorem B13734359 : Blo 1204419 13734359 := bstep (se 1 (by rfl) ⟨10300769, by rfl⟩ : syracuseStep 13734359 = 20601539) B20601539
theorem B158568941 : Blo 1204419 158568941 := bstep (se 3 (by rfl) ⟨29731676, by rfl⟩ : syracuseStep 158568941 = 59463353) B59463353
theorem B2290169 : Blo 1204419 2290169 := bstep (se 2 (by rfl) ⟨858813, by rfl⟩ : syracuseStep 2290169 = 1717627) B1717627
theorem B3863123 : Blo 1204419 3863123 := bstep (se 1 (by rfl) ⟨2897342, by rfl⟩ : syracuseStep 3863123 = 5794685) B5794685
theorem B10990343 : Blo 1204419 10990343 := bstep (se 1 (by rfl) ⟨8242757, by rfl⟩ : syracuseStep 10990343 = 16485515) B16485515
theorem B3052313 : Blo 1204419 3052313 := bstep (se 2 (by rfl) ⟨1144617, by rfl⟩ : syracuseStep 3052313 = 2289235) B2289235
theorem B1807145 : Blo 1204419 1807145 := bstep (se 2 (by rfl) ⟨677679, by rfl⟩ : syracuseStep 1807145 = 1355359) B1355359
theorem B1807151 : Blo 1204419 1807151 := bstep (se 1 (by rfl) ⟨1355363, by rfl⟩ : syracuseStep 1807151 = 2710727) B2710727
theorem B2061167 : Blo 1204419 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1356655 : Blo 1204419 1356655 := bstep (se 1 (by rfl) ⟨1017491, by rfl⟩ : syracuseStep 1356655 = 2034983) B2034983
theorem B1807271 : Blo 1204419 1807271 := bstep (se 1 (by rfl) ⟨1355453, by rfl⟩ : syracuseStep 1807271 = 2710907) B2710907
theorem B1807355 : Blo 1204419 1807355 := bstep (se 1 (by rfl) ⟨1355516, by rfl⟩ : syracuseStep 1807355 = 2711033) B2711033
theorem B2937865 : Blo 1204419 2937865 := bstep (se 2 (by rfl) ⟨1101699, by rfl⟩ : syracuseStep 2937865 = 2203399) B2203399
theorem B1807415 : Blo 1204419 1807415 := bstep (se 1 (by rfl) ⟨1355561, by rfl⟩ : syracuseStep 1807415 = 2711123) B2711123
theorem B1930313 : Blo 1204419 1930313 := bstep (se 2 (by rfl) ⟨723867, by rfl⟩ : syracuseStep 1930313 = 1447735) B1447735
theorem B1807535 : Blo 1204419 1807535 := bstep (se 1 (by rfl) ⟨1355651, by rfl⟩ : syracuseStep 1807535 = 2711303) B2711303
theorem B3912923 : Blo 1204419 3912923 := bstep (se 1 (by rfl) ⟨2934692, by rfl⟩ : syracuseStep 3912923 = 5869385) B5869385
theorem B7328987 : Blo 1204419 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B16487975 : Blo 1204419 16487975 := bstep (se 1 (by rfl) ⟨12365981, by rfl⟩ : syracuseStep 16487975 = 24731963) B24731963
theorem B19559981 : Blo 1204419 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B1807943 : Blo 1204419 1807943 := bstep (se 1 (by rfl) ⟨1355957, by rfl⟩ : syracuseStep 1807943 = 2711915) B2711915
theorem B5150317 : Blo 1204419 5150317 := bstep (se 3 (by rfl) ⟨965684, by rfl⟩ : syracuseStep 5150317 = 1931369) B1931369
theorem B1808039 : Blo 1204419 1808039 := bstep (se 1 (by rfl) ⟨1356029, by rfl⟩ : syracuseStep 1808039 = 2712059) B2712059
theorem B1808123 : Blo 1204419 1808123 := bstep (se 1 (by rfl) ⟨1356092, by rfl⟩ : syracuseStep 1808123 = 2712185) B2712185
theorem B4069115 : Blo 1204419 4069115 := bstep (se 1 (by rfl) ⟨3051836, by rfl⟩ : syracuseStep 4069115 = 6103673) B6103673
theorem B1808159 : Blo 1204419 1808159 := bstep (se 1 (by rfl) ⟨1356119, by rfl⟩ : syracuseStep 1808159 = 2712239) B2712239
theorem B15439673 : Blo 1204419 15439673 := bstep (se 2 (by rfl) ⟨5789877, by rfl⟩ : syracuseStep 15439673 = 11579755) B11579755
theorem B1808207 : Blo 1204419 1808207 := bstep (se 1 (by rfl) ⟨1356155, by rfl⟩ : syracuseStep 1808207 = 2712311) B2712311
theorem B1931087 : Blo 1204419 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B4069277 : Blo 1204419 4069277 := bstep (se 3 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 4069277 = 1525979) B1525979
theorem B1832903 : Blo 1204419 1832903 := bstep (se 1 (by rfl) ⟨1374677, by rfl⟩ : syracuseStep 1832903 = 2749355) B2749355
theorem B1808327 : Blo 1204419 1808327 := bstep (se 1 (by rfl) ⟨1356245, by rfl⟩ : syracuseStep 1808327 = 2712491) B2712491
theorem B4577255 : Blo 1204419 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B3864635 : Blo 1204419 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B6691019 : Blo 1204419 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B3864839 : Blo 1204419 3864839 := bstep (se 1 (by rfl) ⟨2898629, by rfl⟩ : syracuseStep 3864839 = 5797259) B5797259
theorem B1808681 : Blo 1204419 1808681 := bstep (se 2 (by rfl) ⟨678255, by rfl⟩ : syracuseStep 1808681 = 1356511) B1356511
theorem B1808687 : Blo 1204419 1808687 := bstep (se 1 (by rfl) ⟨1356515, by rfl⟩ : syracuseStep 1808687 = 2713031) B2713031
theorem B1808927 : Blo 1204419 1808927 := bstep (se 1 (by rfl) ⟨1356695, by rfl⟩ : syracuseStep 1808927 = 2713391) B2713391
theorem B4070249 : Blo 1204419 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B6511519 : Blo 1204419 6511519 := bstep (se 1 (by rfl) ⟨4883639, by rfl⟩ : syracuseStep 6511519 = 9767279) B9767279
theorem B4070303 : Blo 1204419 4070303 := bstep (se 1 (by rfl) ⟨3052727, by rfl⟩ : syracuseStep 4070303 = 6105455) B6105455
theorem B1809311 : Blo 1204419 1809311 := bstep (se 1 (by rfl) ⟨1356983, by rfl⟩ : syracuseStep 1809311 = 2713967) B2713967
theorem B1809359 : Blo 1204419 1809359 := bstep (se 1 (by rfl) ⟨1357019, by rfl⟩ : syracuseStep 1809359 = 2714039) B2714039
theorem B3431393 : Blo 1204419 3431393 := bstep (se 2 (by rfl) ⟨1286772, by rfl⟩ : syracuseStep 3431393 = 2573545) B2573545
theorem B8682511 : Blo 1204419 8682511 := bstep (se 1 (by rfl) ⟨6511883, by rfl⟩ : syracuseStep 8682511 = 13023767) B13023767
theorem B1809449 : Blo 1204419 1809449 := bstep (se 2 (by rfl) ⟨678543, by rfl⟩ : syracuseStep 1809449 = 1357087) B1357087
theorem B1809455 : Blo 1204419 1809455 := bstep (se 1 (by rfl) ⟨1357091, by rfl⟩ : syracuseStep 1809455 = 2714183) B2714183
theorem B1809479 : Blo 1204419 1809479 := bstep (se 1 (by rfl) ⟨1357109, by rfl⟩ : syracuseStep 1809479 = 2714219) B2714219
theorem B7330931 : Blo 1204419 7330931 := bstep (se 1 (by rfl) ⟨5498198, by rfl⟩ : syracuseStep 7330931 = 10996397) B10996397
theorem B3718561 : Blo 1204419 3718561 := bstep (se 2 (by rfl) ⟨1394460, by rfl⟩ : syracuseStep 3718561 = 2788921) B2788921
theorem B2711015 : Blo 1204419 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B2170643 : Blo 1204419 2170643 := bstep (se 1 (by rfl) ⟨1627982, by rfl⟩ : syracuseStep 2170643 = 3255965) B3255965
theorem B6954781 : Blo 1204419 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B2170795 : Blo 1204419 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B1204431 : Blo 1204419 1204431 := bstep (se 1 (by rfl) ⟨903323, by rfl⟩ : syracuseStep 1204431 = 1806647) B1806647
theorem B1204479 : Blo 1204419 1204479 := bstep (se 1 (by rfl) ⟨903359, by rfl⟩ : syracuseStep 1204479 = 1806719) B1806719
theorem B2711807 : Blo 1204419 2711807 := bstep (se 1 (by rfl) ⟨2033855, by rfl⟩ : syracuseStep 2711807 = 4067711) B4067711
theorem B1204527 : Blo 1204419 1204527 := bstep (se 1 (by rfl) ⟨903395, by rfl⟩ : syracuseStep 1204527 = 1806791) B1806791
theorem B2711969 : Blo 1204419 2711969 := bstep (se 2 (by rfl) ⟨1016988, by rfl⟩ : syracuseStep 2711969 = 2033977) B2033977
theorem B1204763 : Blo 1204419 1204763 := bstep (se 1 (by rfl) ⟨903572, by rfl⟩ : syracuseStep 1204763 = 1807145) B1807145
theorem B17842717 : Blo 1204419 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B1204767 : Blo 1204419 1204767 := bstep (se 1 (by rfl) ⟨903575, by rfl⟩ : syracuseStep 1204767 = 1807151) B1807151
theorem B1204847 : Blo 1204419 1204847 := bstep (se 1 (by rfl) ⟨903635, by rfl⟩ : syracuseStep 1204847 = 1807271) B1807271
theorem B1204903 : Blo 1204419 1204903 := bstep (se 1 (by rfl) ⟨903677, by rfl⟩ : syracuseStep 1204903 = 1807355) B1807355
theorem B10306237 : Blo 1204419 10306237 := bstep (se 3 (by rfl) ⟨1932419, by rfl⟩ : syracuseStep 10306237 = 3864839) B3864839
theorem B1204943 : Blo 1204419 1204943 := bstep (se 1 (by rfl) ⟨903707, by rfl⟩ : syracuseStep 1204943 = 1807415) B1807415
theorem B1286875 : Blo 1204419 1286875 := bstep (se 1 (by rfl) ⟨965156, by rfl⟩ : syracuseStep 1286875 = 1930313) B1930313
theorem B1205023 : Blo 1204419 1205023 := bstep (se 1 (by rfl) ⟨903767, by rfl⟩ : syracuseStep 1205023 = 1807535) B1807535
theorem B24757159 : Blo 1204419 24757159 := bstep (se 1 (by rfl) ⟨18567869, by rfl⟩ : syracuseStep 24757159 = 37135739) B37135739
theorem B1205295 : Blo 1204419 1205295 := bstep (se 1 (by rfl) ⟨903971, by rfl⟩ : syracuseStep 1205295 = 1807943) B1807943
theorem B1205359 : Blo 1204419 1205359 := bstep (se 1 (by rfl) ⟨904019, by rfl⟩ : syracuseStep 1205359 = 1808039) B1808039
theorem B1205415 : Blo 1204419 1205415 := bstep (se 1 (by rfl) ⟨904061, by rfl⟩ : syracuseStep 1205415 = 1808123) B1808123
theorem B2712743 : Blo 1204419 2712743 := bstep (se 1 (by rfl) ⟨2034557, by rfl⟩ : syracuseStep 2712743 = 4069115) B4069115
theorem B1205439 : Blo 1204419 1205439 := bstep (se 1 (by rfl) ⟨904079, by rfl⟩ : syracuseStep 1205439 = 1808159) B1808159
theorem B1205471 : Blo 1204419 1205471 := bstep (se 1 (by rfl) ⟨904103, by rfl⟩ : syracuseStep 1205471 = 1808207) B1808207
theorem B2712851 : Blo 1204419 2712851 := bstep (se 1 (by rfl) ⟨2034638, by rfl⟩ : syracuseStep 2712851 = 4069277) B4069277
theorem B1221935 : Blo 1204419 1221935 := bstep (se 1 (by rfl) ⟨916451, by rfl⟩ : syracuseStep 1221935 = 1832903) B1832903
theorem B1205551 : Blo 1204419 1205551 := bstep (se 1 (by rfl) ⟨904163, by rfl⟩ : syracuseStep 1205551 = 1808327) B1808327
theorem B3917153 : Blo 1204419 3917153 := bstep (se 2 (by rfl) ⟨1468932, by rfl⟩ : syracuseStep 3917153 = 2937865) B2937865
theorem B11576681 : Blo 1204419 11576681 := bstep (se 2 (by rfl) ⟨4341255, by rfl⟩ : syracuseStep 11576681 = 8682511) B8682511
theorem B52159949 : Blo 1204419 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B2033147 : Blo 1204419 2033147 := bstep (se 1 (by rfl) ⟨1524860, by rfl⟩ : syracuseStep 2033147 = 3049721) B3049721
theorem B1205787 : Blo 1204419 1205787 := bstep (se 1 (by rfl) ⟨904340, by rfl⟩ : syracuseStep 1205787 = 1808681) B1808681
theorem B1205791 : Blo 1204419 1205791 := bstep (se 1 (by rfl) ⟨904343, by rfl⟩ : syracuseStep 1205791 = 1808687) B1808687
theorem B5146217 : Blo 1204419 5146217 := bstep (se 2 (by rfl) ⟨1929831, by rfl⟩ : syracuseStep 5146217 = 3859663) B3859663
theorem B1205951 : Blo 1204419 1205951 := bstep (se 1 (by rfl) ⟨904463, by rfl⟩ : syracuseStep 1205951 = 1808927) B1808927
theorem B4958081 : Blo 1204419 4958081 := bstep (se 2 (by rfl) ⟨1859280, by rfl⟩ : syracuseStep 4958081 = 3718561) B3718561
theorem B2713481 : Blo 1204419 2713481 := bstep (se 2 (by rfl) ⟨1017555, by rfl⟩ : syracuseStep 2713481 = 2035111) B2035111
theorem B2713499 : Blo 1204419 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B2713535 : Blo 1204419 2713535 := bstep (se 1 (by rfl) ⟨2035151, by rfl⟩ : syracuseStep 2713535 = 4070303) B4070303
theorem B1206207 : Blo 1204419 1206207 := bstep (se 1 (by rfl) ⟨904655, by rfl⟩ : syracuseStep 1206207 = 1809311) B1809311
theorem B1206239 : Blo 1204419 1206239 := bstep (se 1 (by rfl) ⟨904679, by rfl⟩ : syracuseStep 1206239 = 1809359) B1809359
theorem B2287595 : Blo 1204419 2287595 := bstep (se 1 (by rfl) ⟨1715696, by rfl⟩ : syracuseStep 2287595 = 3431393) B3431393
theorem B1206299 : Blo 1204419 1206299 := bstep (se 1 (by rfl) ⟨904724, by rfl⟩ : syracuseStep 1206299 = 1809449) B1809449
theorem B1206303 : Blo 1204419 1206303 := bstep (se 1 (by rfl) ⟨904727, by rfl⟩ : syracuseStep 1206303 = 1809455) B1809455
theorem B1206319 : Blo 1204419 1206319 := bstep (se 1 (by rfl) ⟨904739, by rfl⟩ : syracuseStep 1206319 = 1809479) B1809479
theorem B2713697 : Blo 1204419 2713697 := bstep (se 2 (by rfl) ⟨1017636, by rfl⟩ : syracuseStep 2713697 = 2035273) B2035273
theorem B6867089 : Blo 1204419 6867089 := bstep (se 2 (by rfl) ⟨2575158, by rfl⟩ : syracuseStep 6867089 = 5150317) B5150317
theorem B21457181 : Blo 1204419 21457181 := bstep (se 3 (by rfl) ⟨4023221, by rfl⟩ : syracuseStep 21457181 = 8046443) B8046443
theorem B2894393 : Blo 1204419 2894393 := bstep (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) B2170795
theorem B3050399 : Blo 1204419 3050399 := bstep (se 1 (by rfl) ⟨2287799, by rfl⟩ : syracuseStep 3050399 = 4575599) B4575599
theorem B4574171 : Blo 1204419 4574171 := bstep (se 1 (by rfl) ⟨3430628, by rfl⟩ : syracuseStep 4574171 = 6861257) B6861257
theorem B105712627 : Blo 1204419 105712627 := bstep (se 1 (by rfl) ⟨79284470, by rfl⟩ : syracuseStep 105712627 = 158568941) B158568941
theorem B1526779 : Blo 1204419 1526779 := bstep (se 1 (by rfl) ⟨1145084, by rfl⟩ : syracuseStep 1526779 = 2290169) B2290169
theorem B2575415 : Blo 1204419 2575415 := bstep (se 1 (by rfl) ⟨1931561, by rfl⟩ : syracuseStep 2575415 = 3863123) B3863123
theorem B2288711 : Blo 1204419 2288711 := bstep (se 1 (by rfl) ⟨1716533, by rfl⟩ : syracuseStep 2288711 = 3433067) B3433067
theorem B7326895 : Blo 1204419 7326895 := bstep (se 1 (by rfl) ⟨5495171, by rfl⟩ : syracuseStep 7326895 = 10990343) B10990343
theorem B2034875 : Blo 1204419 2034875 := bstep (se 1 (by rfl) ⟨1526156, by rfl⟩ : syracuseStep 2034875 = 3052313) B3052313
theorem B6860051 : Blo 1204419 6860051 := bstep (se 1 (by rfl) ⟨5145038, by rfl⟩ : syracuseStep 6860051 = 10290077) B10290077
theorem B2608615 : Blo 1204419 2608615 := bstep (se 1 (by rfl) ⟨1956461, by rfl⟩ : syracuseStep 2608615 = 3912923) B3912923
theorem B4885991 : Blo 1204419 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B6098489 : Blo 1204419 6098489 := bstep (se 2 (by rfl) ⟨2286933, by rfl⟩ : syracuseStep 6098489 = 4573867) B4573867
theorem B10293115 : Blo 1204419 10293115 := bstep (se 1 (by rfl) ⟨7719836, by rfl⟩ : syracuseStep 10293115 = 15439673) B15439673
theorem B1355647 : Blo 1204419 1355647 := bstep (se 1 (by rfl) ⟨1016735, by rfl⟩ : syracuseStep 1355647 = 2033471) B2033471
theorem B3051503 : Blo 1204419 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B2576423 : Blo 1204419 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B1356187 : Blo 1204419 1356187 := bstep (se 1 (by rfl) ⟨1017140, by rfl⟩ : syracuseStep 1356187 = 2034281) B2034281
theorem B10301863 : Blo 1204419 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B37614203 : Blo 1204419 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B9155267 : Blo 1204419 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B5788381 : Blo 1204419 5788381 := bstep (se 3 (by rfl) ⟨1085321, by rfl⟩ : syracuseStep 5788381 = 2170643) B2170643
theorem B8245981 : Blo 1204419 8245981 := bstep (se 3 (by rfl) ⟨1546121, by rfl⟩ : syracuseStep 8245981 = 3092243) B3092243
theorem B4887287 : Blo 1204419 4887287 := bstep (se 1 (by rfl) ⟨3665465, by rfl⟩ : syracuseStep 4887287 = 7330931) B7330931
theorem B10294073 : Blo 1204419 10294073 := bstep (se 2 (by rfl) ⟨3860277, by rfl⟩ : syracuseStep 10294073 = 7720555) B7720555
theorem B5149565 : Blo 1204419 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B2749391 : Blo 1204419 2749391 := bstep (se 1 (by rfl) ⟨2062043, by rfl⟩ : syracuseStep 2749391 = 4124087) B4124087
theorem B11580371 : Blo 1204419 11580371 := bstep (se 1 (by rfl) ⟨8685278, by rfl⟩ : syracuseStep 11580371 = 17370557) B17370557
theorem B1807343 : Blo 1204419 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B1356871 : Blo 1204419 1356871 := bstep (se 1 (by rfl) ⟨1017653, by rfl⟩ : syracuseStep 1356871 = 2035307) B2035307
theorem B1717319 : Blo 1204419 1717319 := bstep (se 1 (by rfl) ⟨1287989, by rfl⟩ : syracuseStep 1717319 = 2575979) B2575979
theorem B1357051 : Blo 1204419 1357051 := bstep (se 1 (by rfl) ⟨1017788, by rfl⟩ : syracuseStep 1357051 = 2035577) B2035577
theorem B5797183 : Blo 1204419 5797183 := bstep (se 1 (by rfl) ⟨4347887, by rfl⟩ : syracuseStep 5797183 = 8695775) B8695775
theorem B1807727 : Blo 1204419 1807727 := bstep (se 1 (by rfl) ⟨1355795, by rfl⟩ : syracuseStep 1807727 = 2711591) B2711591
theorem B100259207 : Blo 1204419 100259207 := bstep (se 1 (by rfl) ⟨75194405, by rfl⟩ : syracuseStep 100259207 = 150388811) B150388811
theorem B3864019 : Blo 1204419 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B1807847 : Blo 1204419 1807847 := bstep (se 1 (by rfl) ⟨1355885, by rfl⟩ : syracuseStep 1807847 = 2711771) B2711771
theorem B7722479 : Blo 1204419 7722479 := bstep (se 1 (by rfl) ⟨5791859, by rfl⟩ : syracuseStep 7722479 = 11583719) B11583719
theorem B4576783 : Blo 1204419 4576783 := bstep (se 1 (by rfl) ⟨3432587, by rfl⟩ : syracuseStep 4576783 = 6865175) B6865175
theorem B1808009 : Blo 1204419 1808009 := bstep (se 2 (by rfl) ⟨678003, by rfl⟩ : syracuseStep 1808009 = 1356007) B1356007
theorem B9156239 : Blo 1204419 9156239 := bstep (se 1 (by rfl) ⟨6867179, by rfl⟩ : syracuseStep 9156239 = 13734359) B13734359
theorem B1808027 : Blo 1204419 1808027 := bstep (se 1 (by rfl) ⟨1356020, by rfl⟩ : syracuseStep 1808027 = 2712041) B2712041
theorem B1808219 : Blo 1204419 1808219 := bstep (se 1 (by rfl) ⟨1356164, by rfl⟩ : syracuseStep 1808219 = 2712329) B2712329
theorem B1448119 : Blo 1204419 1448119 := bstep (se 1 (by rfl) ⟨1086089, by rfl⟩ : syracuseStep 1448119 = 2172179) B2172179
theorem B1808603 : Blo 1204419 1808603 := bstep (se 1 (by rfl) ⟨1356452, by rfl⟩ : syracuseStep 1808603 = 2712905) B2712905
theorem B4577543 : Blo 1204419 4577543 := bstep (se 1 (by rfl) ⟨3433157, by rfl⟩ : syracuseStep 4577543 = 6866315) B6866315
theorem B23157049 : Blo 1204419 23157049 := bstep (se 2 (by rfl) ⟨8683893, by rfl⟩ : syracuseStep 23157049 = 17367787) B17367787
theorem B10991983 : Blo 1204419 10991983 := bstep (se 1 (by rfl) ⟨8243987, by rfl⟩ : syracuseStep 10991983 = 16487975) B16487975
theorem B1808873 : Blo 1204419 1808873 := bstep (se 2 (by rfl) ⟨678327, by rfl⟩ : syracuseStep 1808873 = 1356655) B1356655
theorem B2710043 : Blo 1204419 2710043 := bstep (se 1 (by rfl) ⟨2032532, by rfl⟩ : syracuseStep 2710043 = 4065065) B4065065
theorem B8682025 : Blo 1204419 8682025 := bstep (se 2 (by rfl) ⟨3255759, by rfl⟩ : syracuseStep 8682025 = 6511519) B6511519
theorem B3095273 : Blo 1204419 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B4070141 : Blo 1204419 4070141 := bstep (se 3 (by rfl) ⟨763151, by rfl⟩ : syracuseStep 4070141 = 1526303) B1526303
theorem B1809263 : Blo 1204419 1809263 := bstep (se 1 (by rfl) ⟨1356947, by rfl⟩ : syracuseStep 1809263 = 2713895) B2713895
theorem B1809275 : Blo 1204419 1809275 := bstep (se 1 (by rfl) ⟨1356956, by rfl⟩ : syracuseStep 1809275 = 2713913) B2713913
theorem B169335755 : Blo 1204419 169335755 := bstep (se 1 (by rfl) ⟨127001816, by rfl⟩ : syracuseStep 169335755 = 254003633) B254003633
theorem B4578727 : Blo 1204419 4578727 := bstep (se 1 (by rfl) ⟨3434045, by rfl⟩ : syracuseStep 4578727 = 6868091) B6868091
theorem B5496445 : Blo 1204419 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B9273041 : Blo 1204419 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B3432223 : Blo 1204419 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B2711393 : Blo 1204419 2711393 := bstep (se 2 (by rfl) ⟨1016772, by rfl⟩ : syracuseStep 2711393 = 2033545) B2033545
theorem B4120475 : Blo 1204419 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B2711519 : Blo 1204419 2711519 := bstep (se 1 (by rfl) ⟨2033639, by rfl⟩ : syracuseStep 2711519 = 4067279) B4067279
theorem B4579517 : Blo 1204419 4579517 := bstep (se 3 (by rfl) ⟨858659, by rfl⟩ : syracuseStep 4579517 = 1717319) B1717319
theorem B30876065 : Blo 1204419 30876065 := bstep (se 2 (by rfl) ⟨11578524, by rfl⟩ : syracuseStep 30876065 = 23157049) B23157049
theorem B25076135 : Blo 1204419 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B6103511 : Blo 1204419 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B14655977 : Blo 1204419 14655977 := bstep (se 2 (by rfl) ⟨5495991, by rfl⟩ : syracuseStep 14655977 = 10991983) B10991983
theorem B13033973 : Blo 1204419 13033973 := bstep (se 5 (by rfl) ⟨610967, by rfl⟩ : syracuseStep 13033973 = 1221935) B1221935
theorem B3433043 : Blo 1204419 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B1204895 : Blo 1204419 1204895 := bstep (se 1 (by rfl) ⟨903671, by rfl⟩ : syracuseStep 1204895 = 1807343) B1807343
theorem B23790289 : Blo 1204419 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B11576033 : Blo 1204419 11576033 := bstep (se 2 (by rfl) ⟨4341012, by rfl⟩ : syracuseStep 11576033 = 8682025) B8682025
theorem B7717787 : Blo 1204419 7717787 := bstep (se 1 (by rfl) ⟨5788340, by rfl⟩ : syracuseStep 7717787 = 11576681) B11576681
theorem B1205151 : Blo 1204419 1205151 := bstep (se 1 (by rfl) ⟨903863, by rfl⟩ : syracuseStep 1205151 = 1807727) B1807727
theorem B66839471 : Blo 1204419 66839471 := bstep (se 1 (by rfl) ⟨50129603, by rfl⟩ : syracuseStep 66839471 = 100259207) B100259207
theorem B7717841 : Blo 1204419 7717841 := bstep (se 2 (by rfl) ⟨2894190, by rfl⟩ : syracuseStep 7717841 = 5788381) B5788381
theorem B1205231 : Blo 1204419 1205231 := bstep (se 1 (by rfl) ⟨903923, by rfl⟩ : syracuseStep 1205231 = 1807847) B1807847
theorem B1205339 : Blo 1204419 1205339 := bstep (se 1 (by rfl) ⟨904004, by rfl⟩ : syracuseStep 1205339 = 1808009) B1808009
theorem B6104159 : Blo 1204419 6104159 := bstep (se 1 (by rfl) ⟨4578119, by rfl⟩ : syracuseStep 6104159 = 9156239) B9156239
theorem B1205351 : Blo 1204419 1205351 := bstep (se 1 (by rfl) ⟨904013, by rfl⟩ : syracuseStep 1205351 = 1808027) B1808027
theorem B1205479 : Blo 1204419 1205479 := bstep (se 1 (by rfl) ⟨904109, by rfl⟩ : syracuseStep 1205479 = 1808219) B1808219
theorem B1525063 : Blo 1204419 1525063 := bstep (se 1 (by rfl) ⟨1143797, by rfl⟩ : syracuseStep 1525063 = 2287595) B2287595
theorem B1205735 : Blo 1204419 1205735 := bstep (se 1 (by rfl) ⟨904301, by rfl⟩ : syracuseStep 1205735 = 1808603) B1808603
theorem B1205915 : Blo 1204419 1205915 := bstep (se 1 (by rfl) ⟨904436, by rfl⟩ : syracuseStep 1205915 = 1808873) B1808873
theorem B2713427 : Blo 1204419 2713427 := bstep (se 1 (by rfl) ⟨2035070, by rfl⟩ : syracuseStep 2713427 = 4070141) B4070141
theorem B6104969 : Blo 1204419 6104969 := bstep (se 2 (by rfl) ⟨2289363, by rfl⟩ : syracuseStep 6104969 = 4578727) B4578727
theorem B1206175 : Blo 1204419 1206175 := bstep (se 1 (by rfl) ⟨904631, by rfl⟩ : syracuseStep 1206175 = 1809263) B1809263
theorem B1206183 : Blo 1204419 1206183 := bstep (se 1 (by rfl) ⟨904637, by rfl⟩ : syracuseStep 1206183 = 1809275) B1809275
theorem B2033599 : Blo 1204419 2033599 := bstep (se 1 (by rfl) ⟨1525199, by rfl⟩ : syracuseStep 2033599 = 3050399) B3050399
theorem B3049447 : Blo 1204419 3049447 := bstep (se 1 (by rfl) ⟨2287085, by rfl⟩ : syracuseStep 3049447 = 4574171) B4574171
theorem B1525807 : Blo 1204419 1525807 := bstep (se 1 (by rfl) ⟨1144355, by rfl⟩ : syracuseStep 1525807 = 2288711) B2288711
theorem B4573367 : Blo 1204419 4573367 := bstep (se 1 (by rfl) ⟨3430025, by rfl⟩ : syracuseStep 4573367 = 6860051) B6860051
theorem B4065659 : Blo 1204419 4065659 := bstep (se 1 (by rfl) ⟨3049244, by rfl⟩ : syracuseStep 4065659 = 6098489) B6098489
theorem B10987933 : Blo 1204419 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B13724153 : Blo 1204419 13724153 := bstep (se 2 (by rfl) ⟨5146557, by rfl⟩ : syracuseStep 13724153 = 10293115) B10293115
theorem B2034335 : Blo 1204419 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B6867773 : Blo 1204419 6867773 := bstep (se 3 (by rfl) ⟨1287707, by rfl⟩ : syracuseStep 6867773 = 2575415) B2575415
theorem B7720247 : Blo 1204419 7720247 := bstep (se 1 (by rfl) ⟨5790185, by rfl⟩ : syracuseStep 7720247 = 11580371) B11580371
theorem B13741649 : Blo 1204419 13741649 := bstep (se 2 (by rfl) ⟨5153118, by rfl⟩ : syracuseStep 13741649 = 10306237) B10306237
theorem B1715833 : Blo 1204419 1715833 := bstep (se 2 (by rfl) ⟨643437, by rfl⟩ : syracuseStep 1715833 = 1286875) B1286875
theorem B5148319 : Blo 1204419 5148319 := bstep (se 1 (by rfl) ⟨3861239, by rfl⟩ : syracuseStep 5148319 = 7722479) B7722479
theorem B1355431 : Blo 1204419 1355431 := bstep (se 1 (by rfl) ⟨1016573, by rfl⟩ : syracuseStep 1355431 = 2033147) B2033147
theorem B43978565 : Blo 1204419 43978565 := bstep (se 4 (by rfl) ⟨4122990, by rfl⟩ : syracuseStep 43978565 = 8245981) B8245981
theorem B33009545 : Blo 1204419 33009545 := bstep (se 2 (by rfl) ⟨12378579, by rfl⟩ : syracuseStep 33009545 = 24757159) B24757159
theorem B3305387 : Blo 1204419 3305387 := bstep (se 1 (by rfl) ⟨2479040, by rfl⟩ : syracuseStep 3305387 = 4958081) B4958081
theorem B2035705 : Blo 1204419 2035705 := bstep (se 2 (by rfl) ⟨763389, by rfl⟩ : syracuseStep 2035705 = 1526779) B1526779
theorem B3051695 : Blo 1204419 3051695 := bstep (se 1 (by rfl) ⟨2288771, by rfl⟩ : syracuseStep 3051695 = 4577543) B4577543
theorem B9769193 : Blo 1204419 9769193 := bstep (se 2 (by rfl) ⟨3663447, by rfl⟩ : syracuseStep 9769193 = 7326895) B7326895
theorem B1806695 : Blo 1204419 1806695 := bstep (se 1 (by rfl) ⟨1355021, by rfl⟩ : syracuseStep 1806695 = 2710043) B2710043
theorem B1929595 : Blo 1204419 1929595 := bstep (se 1 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 1929595 = 2894393) B2894393
theorem B7729577 : Blo 1204419 7729577 := bstep (se 2 (by rfl) ⟨2898591, by rfl⟩ : syracuseStep 7729577 = 5797183) B5797183
theorem B8254061 : Blo 1204419 8254061 := bstep (se 3 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 8254061 = 3095273) B3095273
theorem B112890503 : Blo 1204419 112890503 := bstep (se 1 (by rfl) ⟨84667877, by rfl⟩ : syracuseStep 112890503 = 169335755) B169335755
theorem B3478153 : Blo 1204419 3478153 := bstep (se 2 (by rfl) ⟨1304307, by rfl⟩ : syracuseStep 3478153 = 2608615) B2608615
theorem B1356583 : Blo 1204419 1356583 := bstep (se 1 (by rfl) ⟨1017437, by rfl⟩ : syracuseStep 1356583 = 2034875) B2034875
theorem B7328593 : Blo 1204419 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B3257327 : Blo 1204419 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B4576297 : Blo 1204419 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B6182027 : Blo 1204419 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B1807529 : Blo 1204419 1807529 := bstep (se 2 (by rfl) ⟨677823, by rfl⟩ : syracuseStep 1807529 = 1355647) B1355647
theorem B1807595 : Blo 1204419 1807595 := bstep (se 1 (by rfl) ⟨1355696, by rfl⟩ : syracuseStep 1807595 = 2711393) B2711393
theorem B1807679 : Blo 1204419 1807679 := bstep (se 1 (by rfl) ⟨1355759, by rfl⟩ : syracuseStep 1807679 = 2711519) B2711519
theorem B1717615 : Blo 1204419 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B1807871 : Blo 1204419 1807871 := bstep (se 1 (by rfl) ⟨1355903, by rfl⟩ : syracuseStep 1807871 = 2711807) B2711807
theorem B1930825 : Blo 1204419 1930825 := bstep (se 2 (by rfl) ⟨724059, by rfl⟩ : syracuseStep 1930825 = 1448119) B1448119
theorem B1807979 : Blo 1204419 1807979 := bstep (se 1 (by rfl) ⟨1355984, by rfl⟩ : syracuseStep 1807979 = 2711969) B2711969
theorem B3258191 : Blo 1204419 3258191 := bstep (se 1 (by rfl) ⟨2443643, by rfl⟩ : syracuseStep 3258191 = 4887287) B4887287
theorem B1808249 : Blo 1204419 1808249 := bstep (se 2 (by rfl) ⟨678093, by rfl⟩ : syracuseStep 1808249 = 1356187) B1356187
theorem B6862715 : Blo 1204419 6862715 := bstep (se 1 (by rfl) ⟨5147036, by rfl⟩ : syracuseStep 6862715 = 10294073) B10294073
theorem B13735817 : Blo 1204419 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B1832927 : Blo 1204419 1832927 := bstep (se 1 (by rfl) ⟨1374695, by rfl⟩ : syracuseStep 1832927 = 2749391) B2749391
theorem B57219149 : Blo 1204419 57219149 := bstep (se 3 (by rfl) ⟨10728590, by rfl⟩ : syracuseStep 57219149 = 21457181) B21457181
theorem B1808495 : Blo 1204419 1808495 := bstep (se 1 (by rfl) ⟨1356371, by rfl⟩ : syracuseStep 1808495 = 2712743) B2712743
theorem B1808567 : Blo 1204419 1808567 := bstep (se 1 (by rfl) ⟨1356425, by rfl⟩ : syracuseStep 1808567 = 2712851) B2712851
theorem B2611435 : Blo 1204419 2611435 := bstep (se 1 (by rfl) ⟨1958576, by rfl⟩ : syracuseStep 2611435 = 3917153) B3917153
theorem B34773299 : Blo 1204419 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B3430811 : Blo 1204419 3430811 := bstep (se 1 (by rfl) ⟨2573108, by rfl⟩ : syracuseStep 3430811 = 5146217) B5146217
theorem B1808987 : Blo 1204419 1808987 := bstep (se 1 (by rfl) ⟨1356740, by rfl⟩ : syracuseStep 1808987 = 2713481) B2713481
theorem B1808999 : Blo 1204419 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B1809023 : Blo 1204419 1809023 := bstep (se 1 (by rfl) ⟨1356767, by rfl⟩ : syracuseStep 1809023 = 2713535) B2713535
theorem B140950169 : Blo 1204419 140950169 := bstep (se 2 (by rfl) ⟨52856313, by rfl⟩ : syracuseStep 140950169 = 105712627) B105712627
theorem B1809131 : Blo 1204419 1809131 := bstep (se 1 (by rfl) ⟨1356848, by rfl⟩ : syracuseStep 1809131 = 2713697) B2713697
theorem B1809161 : Blo 1204419 1809161 := bstep (se 2 (by rfl) ⟨678435, by rfl⟩ : syracuseStep 1809161 = 1356871) B1356871
theorem B4578059 : Blo 1204419 4578059 := bstep (se 1 (by rfl) ⟨3433544, by rfl⟩ : syracuseStep 4578059 = 6867089) B6867089
theorem B1809401 : Blo 1204419 1809401 := bstep (se 2 (by rfl) ⟨678525, by rfl⟩ : syracuseStep 1809401 = 1357051) B1357051
theorem B5152025 : Blo 1204419 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B6102377 : Blo 1204419 6102377 := bstep (se 2 (by rfl) ⟨2288391, by rfl⟩ : syracuseStep 6102377 = 4576783) B4576783
theorem B6512795 : Blo 1204419 6512795 := bstep (se 1 (by rfl) ⟨4884596, by rfl⟩ : syracuseStep 6512795 = 9769193) B9769193
theorem B152584397 : Blo 1204419 152584397 := bstep (se 3 (by rfl) ⟨28609574, by rfl⟩ : syracuseStep 152584397 = 57219149) B57219149
theorem B1204463 : Blo 1204419 1204463 := bstep (se 1 (by rfl) ⟨903347, by rfl⟩ : syracuseStep 1204463 = 1806695) B1806695
theorem B5153051 : Blo 1204419 5153051 := bstep (se 1 (by rfl) ⟨3864788, by rfl⟩ : syracuseStep 5153051 = 7729577) B7729577
theorem B75260335 : Blo 1204419 75260335 := bstep (se 1 (by rfl) ⟨56445251, by rfl⟩ : syracuseStep 75260335 = 112890503) B112890503
theorem B7717355 : Blo 1204419 7717355 := bstep (se 1 (by rfl) ⟨5788016, by rfl⟩ : syracuseStep 7717355 = 11576033) B11576033
theorem B2572793 : Blo 1204419 2572793 := bstep (se 2 (by rfl) ⟨964797, by rfl⟩ : syracuseStep 2572793 = 1929595) B1929595
theorem B5145191 : Blo 1204419 5145191 := bstep (se 1 (by rfl) ⟨3858893, by rfl⟩ : syracuseStep 5145191 = 7717787) B7717787
theorem B5145227 : Blo 1204419 5145227 := bstep (se 1 (by rfl) ⟨3858920, by rfl⟩ : syracuseStep 5145227 = 7717841) B7717841
theorem B2171551 : Blo 1204419 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B13738733 : Blo 1204419 13738733 := bstep (se 3 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 13738733 = 5152025) B5152025
theorem B4121351 : Blo 1204419 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1205019 : Blo 1204419 1205019 := bstep (se 1 (by rfl) ⟨903764, by rfl⟩ : syracuseStep 1205019 = 1807529) B1807529
theorem B1205063 : Blo 1204419 1205063 := bstep (se 1 (by rfl) ⟨903797, by rfl⟩ : syracuseStep 1205063 = 1807595) B1807595
theorem B4637537 : Blo 1204419 4637537 := bstep (se 2 (by rfl) ⟨1739076, by rfl⟩ : syracuseStep 4637537 = 3478153) B3478153
theorem B1205119 : Blo 1204419 1205119 := bstep (se 1 (by rfl) ⟨903839, by rfl⟩ : syracuseStep 1205119 = 1807679) B1807679
theorem B31720385 : Blo 1204419 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B1205247 : Blo 1204419 1205247 := bstep (se 1 (by rfl) ⟨903935, by rfl⟩ : syracuseStep 1205247 = 1807871) B1807871
theorem B1205319 : Blo 1204419 1205319 := bstep (se 1 (by rfl) ⟨903989, by rfl⟩ : syracuseStep 1205319 = 1807979) B1807979
theorem B2172127 : Blo 1204419 2172127 := bstep (se 1 (by rfl) ⟨1629095, by rfl⟩ : syracuseStep 2172127 = 3258191) B3258191
theorem B1205499 : Blo 1204419 1205499 := bstep (se 1 (by rfl) ⟨904124, by rfl⟩ : syracuseStep 1205499 = 1808249) B1808249
theorem B1205663 : Blo 1204419 1205663 := bstep (se 1 (by rfl) ⟨904247, by rfl⟩ : syracuseStep 1205663 = 1808495) B1808495
theorem B3048911 : Blo 1204419 3048911 := bstep (se 1 (by rfl) ⟨2286683, by rfl⟩ : syracuseStep 3048911 = 4573367) B4573367
theorem B1205711 : Blo 1204419 1205711 := bstep (se 1 (by rfl) ⟨904283, by rfl⟩ : syracuseStep 1205711 = 1808567) B1808567
theorem B2287207 : Blo 1204419 2287207 := bstep (se 1 (by rfl) ⟨1715405, by rfl⟩ : syracuseStep 2287207 = 3430811) B3430811
theorem B1205991 : Blo 1204419 1205991 := bstep (se 1 (by rfl) ⟨904493, by rfl⟩ : syracuseStep 1205991 = 1808987) B1808987
theorem B1205999 : Blo 1204419 1205999 := bstep (se 1 (by rfl) ⟨904499, by rfl⟩ : syracuseStep 1205999 = 1808999) B1808999
theorem B1206015 : Blo 1204419 1206015 := bstep (se 1 (by rfl) ⟨904511, by rfl⟩ : syracuseStep 1206015 = 1809023) B1809023
theorem B2033417 : Blo 1204419 2033417 := bstep (se 2 (by rfl) ⟨762531, by rfl⟩ : syracuseStep 2033417 = 1525063) B1525063
theorem B1206087 : Blo 1204419 1206087 := bstep (se 1 (by rfl) ⟨904565, by rfl⟩ : syracuseStep 1206087 = 1809131) B1809131
theorem B1206107 : Blo 1204419 1206107 := bstep (se 1 (by rfl) ⟨904580, by rfl⟩ : syracuseStep 1206107 = 1809161) B1809161
theorem B9160613 : Blo 1204419 9160613 := bstep (se 4 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 9160613 = 1717615) B1717615
theorem B1206267 : Blo 1204419 1206267 := bstep (se 1 (by rfl) ⟨904700, by rfl⟩ : syracuseStep 1206267 = 1809401) B1809401
theorem B2574433 : Blo 1204419 2574433 := bstep (se 2 (by rfl) ⟨965412, by rfl⟩ : syracuseStep 2574433 = 1930825) B1930825
theorem B2287777 : Blo 1204419 2287777 := bstep (se 2 (by rfl) ⟨857916, by rfl⟩ : syracuseStep 2287777 = 1715833) B1715833
theorem B5146831 : Blo 1204419 5146831 := bstep (se 1 (by rfl) ⟨3860123, by rfl⟩ : syracuseStep 5146831 = 7720247) B7720247
theorem B88025453 : Blo 1204419 88025453 := bstep (se 3 (by rfl) ⟨16504772, by rfl⟩ : syracuseStep 88025453 = 33009545) B33009545
theorem B9161099 : Blo 1204419 9161099 := bstep (se 1 (by rfl) ⟨6870824, by rfl⟩ : syracuseStep 9161099 = 13741649) B13741649
theorem B4065929 : Blo 1204419 4065929 := bstep (se 2 (by rfl) ⟨1524723, by rfl⟩ : syracuseStep 4065929 = 3049447) B3049447
theorem B2714273 : Blo 1204419 2714273 := bstep (se 2 (by rfl) ⟨1017852, by rfl⟩ : syracuseStep 2714273 = 2035705) B2035705
theorem B2034409 : Blo 1204419 2034409 := bstep (se 2 (by rfl) ⟨762903, by rfl⟩ : syracuseStep 2034409 = 1525807) B1525807
theorem B2034463 : Blo 1204419 2034463 := bstep (se 1 (by rfl) ⟨1525847, by rfl⟩ : syracuseStep 2034463 = 3051695) B3051695
theorem B14650577 : Blo 1204419 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B44559647 : Blo 1204419 44559647 := bstep (se 1 (by rfl) ⟨33419735, by rfl⟩ : syracuseStep 44559647 = 66839471) B66839471
theorem B4575143 : Blo 1204419 4575143 := bstep (se 1 (by rfl) ⟨3431357, by rfl⟩ : syracuseStep 4575143 = 6862715) B6862715
theorem B9154781 : Blo 1204419 9154781 := bstep (se 3 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 9154781 = 3433043) B3433043
theorem B93966779 : Blo 1204419 93966779 := bstep (se 1 (by rfl) ⟨70475084, by rfl⟩ : syracuseStep 93966779 = 140950169) B140950169
theorem B1356223 : Blo 1204419 1356223 := bstep (se 1 (by rfl) ⟨1017167, by rfl⟩ : syracuseStep 1356223 = 2034335) B2034335
theorem B3052039 : Blo 1204419 3052039 := bstep (se 1 (by rfl) ⟨2289029, by rfl⟩ : syracuseStep 3052039 = 4578059) B4578059
theorem B1807241 : Blo 1204419 1807241 := bstep (se 2 (by rfl) ⟨677715, by rfl⟩ : syracuseStep 1807241 = 1355431) B1355431
theorem B55710613 : Blo 1204419 55710613 := bstep (se 6 (by rfl) ⟨1305717, by rfl⟩ : syracuseStep 55710613 = 2611435) B2611435
theorem B4068251 : Blo 1204419 4068251 := bstep (se 1 (by rfl) ⟨3051188, by rfl⟩ : syracuseStep 4068251 = 6102377) B6102377
theorem B4887805 : Blo 1204419 4887805 := bstep (se 3 (by rfl) ⟨916463, by rfl⟩ : syracuseStep 4887805 = 1832927) B1832927
theorem B3053011 : Blo 1204419 3053011 := bstep (se 1 (by rfl) ⟨2289758, by rfl⟩ : syracuseStep 3053011 = 4579517) B4579517
theorem B20584043 : Blo 1204419 20584043 := bstep (se 1 (by rfl) ⟨15438032, by rfl⟩ : syracuseStep 20584043 = 30876065) B30876065
theorem B16717423 : Blo 1204419 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B4069007 : Blo 1204419 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B9770651 : Blo 1204419 9770651 := bstep (se 1 (by rfl) ⟨7327988, by rfl⟩ : syracuseStep 9770651 = 14655977) B14655977
theorem B5502707 : Blo 1204419 5502707 := bstep (se 1 (by rfl) ⟨4127030, by rfl⟩ : syracuseStep 5502707 = 8254061) B8254061
theorem B4069439 : Blo 1204419 4069439 := bstep (se 1 (by rfl) ⟨3052079, by rfl⟩ : syracuseStep 4069439 = 6104159) B6104159
theorem B1808777 : Blo 1204419 1808777 := bstep (se 2 (by rfl) ⟨678291, by rfl⟩ : syracuseStep 1808777 = 1356583) B1356583
theorem B9771457 : Blo 1204419 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B1808951 : Blo 1204419 1808951 := bstep (se 1 (by rfl) ⟨1356713, by rfl⟩ : syracuseStep 1808951 = 2713427) B2713427
theorem B9157211 : Blo 1204419 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B4069979 : Blo 1204419 4069979 := bstep (se 1 (by rfl) ⟨3052484, by rfl⟩ : syracuseStep 4069979 = 6104969) B6104969
theorem B34757261 : Blo 1204419 34757261 := bstep (se 3 (by rfl) ⟨6516986, by rfl⟩ : syracuseStep 34757261 = 13033973) B13033973
theorem B6101729 : Blo 1204419 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B23182199 : Blo 1204419 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B2710439 : Blo 1204419 2710439 := bstep (se 1 (by rfl) ⟨2032829, by rfl⟩ : syracuseStep 2710439 = 4065659) B4065659
theorem B9149435 : Blo 1204419 9149435 := bstep (se 1 (by rfl) ⟨6862076, by rfl⟩ : syracuseStep 9149435 = 13724153) B13724153
theorem B4578515 : Blo 1204419 4578515 := bstep (se 1 (by rfl) ⟨3433886, by rfl⟩ : syracuseStep 4578515 = 6867773) B6867773
theorem B6864425 : Blo 1204419 6864425 := bstep (se 2 (by rfl) ⟨2574159, by rfl⟩ : syracuseStep 6864425 = 5148319) B5148319
theorem B29319043 : Blo 1204419 29319043 := bstep (se 1 (by rfl) ⟨21989282, by rfl⟩ : syracuseStep 29319043 = 43978565) B43978565
theorem B2711465 : Blo 1204419 2711465 := bstep (se 2 (by rfl) ⟨1016799, by rfl⟩ : syracuseStep 2711465 = 2033599) B2033599
theorem B2203591 : Blo 1204419 2203591 := bstep (se 1 (by rfl) ⟨1652693, by rfl⟩ : syracuseStep 2203591 = 3305387) B3305387
theorem B4341863 : Blo 1204419 4341863 := bstep (se 1 (by rfl) ⟨3256397, by rfl⟩ : syracuseStep 4341863 = 6512795) B6512795
theorem B3432577 : Blo 1204419 3432577 := bstep (se 2 (by rfl) ⟨1287216, by rfl⟩ : syracuseStep 3432577 = 2574433) B2574433
theorem B6103187 : Blo 1204419 6103187 := bstep (se 1 (by rfl) ⟨4577390, by rfl⟩ : syracuseStep 6103187 = 9154781) B9154781
theorem B62644519 : Blo 1204419 62644519 := bstep (se 1 (by rfl) ⟨46983389, by rfl⟩ : syracuseStep 62644519 = 93966779) B93966779
theorem B5144903 : Blo 1204419 5144903 := bstep (se 1 (by rfl) ⟨3858677, by rfl⟩ : syracuseStep 5144903 = 7717355) B7717355
theorem B9159155 : Blo 1204419 9159155 := bstep (se 1 (by rfl) ⟨6869366, by rfl⟩ : syracuseStep 9159155 = 13738733) B13738733
theorem B1204827 : Blo 1204419 1204827 := bstep (se 1 (by rfl) ⟨903620, by rfl⟩ : syracuseStep 1204827 = 1807241) B1807241
theorem B2712167 : Blo 1204419 2712167 := bstep (se 1 (by rfl) ⟨2034125, by rfl⟩ : syracuseStep 2712167 = 4068251) B4068251
theorem B2032607 : Blo 1204419 2032607 := bstep (se 1 (by rfl) ⟨1524455, by rfl⟩ : syracuseStep 2032607 = 3048911) B3048911
theorem B2712545 : Blo 1204419 2712545 := bstep (se 2 (by rfl) ⟨1017204, by rfl⟩ : syracuseStep 2712545 = 2034409) B2034409
theorem B2712617 : Blo 1204419 2712617 := bstep (se 2 (by rfl) ⟨1017231, by rfl⟩ : syracuseStep 2712617 = 2034463) B2034463
theorem B13722695 : Blo 1204419 13722695 := bstep (se 1 (by rfl) ⟨10292021, by rfl⟩ : syracuseStep 13722695 = 20584043) B20584043
theorem B2712671 : Blo 1204419 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B6513767 : Blo 1204419 6513767 := bstep (se 1 (by rfl) ⟨4885325, by rfl⟩ : syracuseStep 6513767 = 9770651) B9770651
theorem B2712959 : Blo 1204419 2712959 := bstep (se 1 (by rfl) ⟨2034719, by rfl⟩ : syracuseStep 2712959 = 4069439) B4069439
theorem B1205851 : Blo 1204419 1205851 := bstep (se 1 (by rfl) ⟨904388, by rfl⟩ : syracuseStep 1205851 = 1808777) B1808777
theorem B1205967 : Blo 1204419 1205967 := bstep (se 1 (by rfl) ⟨904475, by rfl⟩ : syracuseStep 1205967 = 1808951) B1808951
theorem B6104807 : Blo 1204419 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B2713319 : Blo 1204419 2713319 := bstep (se 1 (by rfl) ⟨2034989, by rfl⟩ : syracuseStep 2713319 = 4069979) B4069979
theorem B3049609 : Blo 1204419 3049609 := bstep (se 2 (by rfl) ⟨1143603, by rfl⟩ : syracuseStep 3049609 = 2287207) B2287207
theorem B9767051 : Blo 1204419 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B29706431 : Blo 1204419 29706431 := bstep (se 1 (by rfl) ⟨22279823, by rfl⟩ : syracuseStep 29706431 = 44559647) B44559647
theorem B3050095 : Blo 1204419 3050095 := bstep (se 1 (by rfl) ⟨2287571, by rfl⟩ : syracuseStep 3050095 = 4575143) B4575143
theorem B101722931 : Blo 1204419 101722931 := bstep (se 1 (by rfl) ⟨76292198, by rfl⟩ : syracuseStep 101722931 = 152584397) B152584397
theorem B3435367 : Blo 1204419 3435367 := bstep (se 1 (by rfl) ⟨2576525, by rfl⟩ : syracuseStep 3435367 = 5153051) B5153051
theorem B3050369 : Blo 1204419 3050369 := bstep (se 2 (by rfl) ⟨1143888, by rfl⟩ : syracuseStep 3050369 = 2287777) B2287777
theorem B1715195 : Blo 1204419 1715195 := bstep (se 1 (by rfl) ⟨1286396, by rfl⟩ : syracuseStep 1715195 = 2572793) B2572793
theorem B2747567 : Blo 1204419 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B100347113 : Blo 1204419 100347113 := bstep (se 2 (by rfl) ⟨37630167, by rfl⟩ : syracuseStep 100347113 = 75260335) B75260335
theorem B3091691 : Blo 1204419 3091691 := bstep (se 1 (by rfl) ⟨2318768, by rfl⟩ : syracuseStep 3091691 = 4637537) B4637537
theorem B13028609 : Blo 1204419 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B21146923 : Blo 1204419 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B2895401 : Blo 1204419 2895401 := bstep (se 2 (by rfl) ⟨1085775, by rfl⟩ : syracuseStep 2895401 = 2171551) B2171551
theorem B1355611 : Blo 1204419 1355611 := bstep (se 1 (by rfl) ⟨1016708, by rfl⟩ : syracuseStep 1355611 = 2033417) B2033417
theorem B74280817 : Blo 1204419 74280817 := bstep (se 2 (by rfl) ⟨27855306, by rfl⟩ : syracuseStep 74280817 = 55710613) B55710613
theorem B6107075 : Blo 1204419 6107075 := bstep (se 1 (by rfl) ⟨4580306, by rfl⟩ : syracuseStep 6107075 = 9160613) B9160613
theorem B58683635 : Blo 1204419 58683635 := bstep (se 1 (by rfl) ⟨44012726, by rfl⟩ : syracuseStep 58683635 = 88025453) B88025453
theorem B6107399 : Blo 1204419 6107399 := bstep (se 1 (by rfl) ⟨4580549, by rfl⟩ : syracuseStep 6107399 = 9161099) B9161099
theorem B2896169 : Blo 1204419 2896169 := bstep (se 2 (by rfl) ⟨1086063, by rfl⟩ : syracuseStep 2896169 = 2172127) B2172127
theorem B6517073 : Blo 1204419 6517073 := bstep (se 2 (by rfl) ⟨2443902, by rfl⟩ : syracuseStep 6517073 = 4887805) B4887805
theorem B23171507 : Blo 1204419 23171507 := bstep (se 1 (by rfl) ⟨17378630, by rfl⟩ : syracuseStep 23171507 = 34757261) B34757261
theorem B4067819 : Blo 1204419 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B15454799 : Blo 1204419 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B1806959 : Blo 1204419 1806959 := bstep (se 1 (by rfl) ⟨1355219, by rfl⟩ : syracuseStep 1806959 = 2710439) B2710439
theorem B6099623 : Blo 1204419 6099623 := bstep (se 1 (by rfl) ⟨4574717, by rfl⟩ : syracuseStep 6099623 = 9149435) B9149435
theorem B3052343 : Blo 1204419 3052343 := bstep (se 1 (by rfl) ⟨2289257, by rfl⟩ : syracuseStep 3052343 = 4578515) B4578515
theorem B4576283 : Blo 1204419 4576283 := bstep (se 1 (by rfl) ⟨3432212, by rfl⟩ : syracuseStep 4576283 = 6864425) B6864425
theorem B2938121 : Blo 1204419 2938121 := bstep (se 2 (by rfl) ⟨1101795, by rfl⟩ : syracuseStep 2938121 = 2203591) B2203591
theorem B1807643 : Blo 1204419 1807643 := bstep (se 1 (by rfl) ⟨1355732, by rfl⟩ : syracuseStep 1807643 = 2711465) B2711465
theorem B6862441 : Blo 1204419 6862441 := bstep (se 2 (by rfl) ⟨2573415, by rfl⟩ : syracuseStep 6862441 = 5146831) B5146831
theorem B3430127 : Blo 1204419 3430127 := bstep (se 1 (by rfl) ⟨2572595, by rfl⟩ : syracuseStep 3430127 = 5145191) B5145191
theorem B3430151 : Blo 1204419 3430151 := bstep (se 1 (by rfl) ⟨2572613, by rfl⟩ : syracuseStep 3430151 = 5145227) B5145227
theorem B1808297 : Blo 1204419 1808297 := bstep (se 2 (by rfl) ⟨678111, by rfl⟩ : syracuseStep 1808297 = 1356223) B1356223
theorem B4069385 : Blo 1204419 4069385 := bstep (se 2 (by rfl) ⟨1526019, by rfl⟩ : syracuseStep 4069385 = 3052039) B3052039
theorem B3668471 : Blo 1204419 3668471 := bstep (se 1 (by rfl) ⟨2751353, by rfl⟩ : syracuseStep 3668471 = 5502707) B5502707
theorem B2710619 : Blo 1204419 2710619 := bstep (se 1 (by rfl) ⟨2032964, by rfl⟩ : syracuseStep 2710619 = 4065929) B4065929
theorem B1809515 : Blo 1204419 1809515 := bstep (se 1 (by rfl) ⟨1357136, by rfl⟩ : syracuseStep 1809515 = 2714273) B2714273
theorem B4070681 : Blo 1204419 4070681 := bstep (se 2 (by rfl) ⟨1526505, by rfl⟩ : syracuseStep 4070681 = 3053011) B3053011
theorem B22289897 : Blo 1204419 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B39092057 : Blo 1204419 39092057 := bstep (se 2 (by rfl) ⟨14659521, by rfl⟩ : syracuseStep 39092057 = 29319043) B29319043
theorem B4071599 : Blo 1204419 4071599 := bstep (se 1 (by rfl) ⟨3053699, by rfl⟩ : syracuseStep 4071599 = 6107399) B6107399
theorem B2711879 : Blo 1204419 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B83526025 : Blo 1204419 83526025 := bstep (se 2 (by rfl) ⟨31322259, by rfl⟩ : syracuseStep 83526025 = 62644519) B62644519
theorem B1204639 : Blo 1204419 1204639 := bstep (se 1 (by rfl) ⟨903479, by rfl⟩ : syracuseStep 1204639 = 1806959) B1806959
theorem B79217149 : Blo 1204419 79217149 := bstep (se 3 (by rfl) ⟨14853215, by rfl⟩ : syracuseStep 79217149 = 29706431) B29706431
theorem B4342511 : Blo 1204419 4342511 := bstep (se 1 (by rfl) ⟨3256883, by rfl⟩ : syracuseStep 4342511 = 6513767) B6513767
theorem B1958747 : Blo 1204419 1958747 := bstep (se 1 (by rfl) ⟨1469060, by rfl⟩ : syracuseStep 1958747 = 2938121) B2938121
theorem B1205095 : Blo 1204419 1205095 := bstep (se 1 (by rfl) ⟨903821, by rfl⟩ : syracuseStep 1205095 = 1807643) B1807643
theorem B4580489 : Blo 1204419 4580489 := bstep (se 2 (by rfl) ⟨1717683, by rfl⟩ : syracuseStep 4580489 = 3435367) B3435367
theorem B2286767 : Blo 1204419 2286767 := bstep (se 1 (by rfl) ⟨1715075, by rfl⟩ : syracuseStep 2286767 = 3430151) B3430151
theorem B1205531 : Blo 1204419 1205531 := bstep (se 1 (by rfl) ⟨904148, by rfl⟩ : syracuseStep 1205531 = 1808297) B1808297
theorem B2712923 : Blo 1204419 2712923 := bstep (se 1 (by rfl) ⟨2034692, by rfl⟩ : syracuseStep 2712923 = 4069385) B4069385
theorem B67815287 : Blo 1204419 67815287 := bstep (se 1 (by rfl) ⟨50861465, by rfl⟩ : syracuseStep 67815287 = 101722931) B101722931
theorem B2033579 : Blo 1204419 2033579 := bstep (se 1 (by rfl) ⟨1525184, by rfl⟩ : syracuseStep 2033579 = 3050369) B3050369
theorem B1206343 : Blo 1204419 1206343 := bstep (se 1 (by rfl) ⟨904757, by rfl⟩ : syracuseStep 1206343 = 1809515) B1809515
theorem B66898075 : Blo 1204419 66898075 := bstep (se 1 (by rfl) ⟨50173556, by rfl⟩ : syracuseStep 66898075 = 100347113) B100347113
theorem B8685739 : Blo 1204419 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B2713787 : Blo 1204419 2713787 := bstep (se 1 (by rfl) ⟨2035340, by rfl⟩ : syracuseStep 2713787 = 4070681) B4070681
theorem B26061371 : Blo 1204419 26061371 := bstep (se 1 (by rfl) ⟨19546028, by rfl⟩ : syracuseStep 26061371 = 39092057) B39092057
theorem B4573853 : Blo 1204419 4573853 := bstep (se 3 (by rfl) ⟨857597, by rfl⟩ : syracuseStep 4573853 = 1715195) B1715195
theorem B2894575 : Blo 1204419 2894575 := bstep (se 1 (by rfl) ⟨2170931, by rfl⟩ : syracuseStep 2894575 = 4341863) B4341863
theorem B4066145 : Blo 1204419 4066145 := bstep (se 2 (by rfl) ⟨1524804, by rfl⟩ : syracuseStep 4066145 = 3049609) B3049609
theorem B4344715 : Blo 1204419 4344715 := bstep (se 1 (by rfl) ⟨3258536, by rfl⟩ : syracuseStep 4344715 = 6517073) B6517073
theorem B6106103 : Blo 1204419 6106103 := bstep (se 1 (by rfl) ⟨4579577, by rfl⟩ : syracuseStep 6106103 = 9159155) B9159155
theorem B4066415 : Blo 1204419 4066415 := bstep (se 1 (by rfl) ⟨3049811, by rfl⟩ : syracuseStep 4066415 = 6099623) B6099623
theorem B7326845 : Blo 1204419 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B2034895 : Blo 1204419 2034895 := bstep (se 1 (by rfl) ⟨1526171, by rfl⟩ : syracuseStep 2034895 = 3052343) B3052343
theorem B1355071 : Blo 1204419 1355071 := bstep (se 1 (by rfl) ⟨1016303, by rfl⟩ : syracuseStep 1355071 = 2032607) B2032607
theorem B3050855 : Blo 1204419 3050855 := bstep (se 1 (by rfl) ⟨2288141, by rfl⟩ : syracuseStep 3050855 = 4576283) B4576283
theorem B4066793 : Blo 1204419 4066793 := bstep (se 2 (by rfl) ⟨1525047, by rfl⟩ : syracuseStep 4066793 = 3050095) B3050095
theorem B112783589 : Blo 1204419 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B2445647 : Blo 1204419 2445647 := bstep (se 1 (by rfl) ⟨1834235, by rfl⟩ : syracuseStep 2445647 = 3668471) B3668471
theorem B9147005 : Blo 1204419 9147005 := bstep (se 3 (by rfl) ⟨1715063, by rfl⟩ : syracuseStep 9147005 = 3430127) B3430127
theorem B1807079 : Blo 1204419 1807079 := bstep (se 1 (by rfl) ⟨1355309, by rfl⟩ : syracuseStep 1807079 = 2710619) B2710619
theorem B2061127 : Blo 1204419 2061127 := bstep (se 1 (by rfl) ⟨1545845, by rfl⟩ : syracuseStep 2061127 = 3091691) B3091691
theorem B1930267 : Blo 1204419 1930267 := bstep (se 1 (by rfl) ⟨1447700, by rfl⟩ : syracuseStep 1930267 = 2895401) B2895401
theorem B1807481 : Blo 1204419 1807481 := bstep (se 2 (by rfl) ⟨677805, by rfl⟩ : syracuseStep 1807481 = 1355611) B1355611
theorem B4068791 : Blo 1204419 4068791 := bstep (se 1 (by rfl) ⟨3051593, by rfl⟩ : syracuseStep 4068791 = 6103187) B6103187
theorem B39122423 : Blo 1204419 39122423 := bstep (se 1 (by rfl) ⟨29341817, by rfl⟩ : syracuseStep 39122423 = 58683635) B58683635
theorem B4576769 : Blo 1204419 4576769 := bstep (se 2 (by rfl) ⟨1716288, by rfl⟩ : syracuseStep 4576769 = 3432577) B3432577
theorem B3429935 : Blo 1204419 3429935 := bstep (se 1 (by rfl) ⟨2572451, by rfl⟩ : syracuseStep 3429935 = 5144903) B5144903
theorem B15447671 : Blo 1204419 15447671 := bstep (se 1 (by rfl) ⟨11585753, by rfl⟩ : syracuseStep 15447671 = 23171507) B23171507
theorem B10303199 : Blo 1204419 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B1808111 : Blo 1204419 1808111 := bstep (se 1 (by rfl) ⟨1356083, by rfl⟩ : syracuseStep 1808111 = 2712167) B2712167
theorem B1808363 : Blo 1204419 1808363 := bstep (se 1 (by rfl) ⟨1356272, by rfl⟩ : syracuseStep 1808363 = 2712545) B2712545
theorem B1808411 : Blo 1204419 1808411 := bstep (se 1 (by rfl) ⟨1356308, by rfl⟩ : syracuseStep 1808411 = 2712617) B2712617
theorem B9148463 : Blo 1204419 9148463 := bstep (se 1 (by rfl) ⟨6861347, by rfl⟩ : syracuseStep 9148463 = 13722695) B13722695
theorem B1808447 : Blo 1204419 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B7723117 : Blo 1204419 7723117 := bstep (se 3 (by rfl) ⟨1448084, by rfl⟩ : syracuseStep 7723117 = 2896169) B2896169
theorem B1808639 : Blo 1204419 1808639 := bstep (se 1 (by rfl) ⟨1356479, by rfl⟩ : syracuseStep 1808639 = 2712959) B2712959
theorem B4069871 : Blo 1204419 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B1808879 : Blo 1204419 1808879 := bstep (se 1 (by rfl) ⟨1356659, by rfl⟩ : syracuseStep 1808879 = 2713319) B2713319
theorem B6511367 : Blo 1204419 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B396164357 : Blo 1204419 396164357 := bstep (se 4 (by rfl) ⟨37140408, by rfl⟩ : syracuseStep 396164357 = 74280817) B74280817
theorem B9149921 : Blo 1204419 9149921 := bstep (se 2 (by rfl) ⟨3431220, by rfl⟩ : syracuseStep 9149921 = 6862441) B6862441
theorem B14859931 : Blo 1204419 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B4071383 : Blo 1204419 4071383 := bstep (se 1 (by rfl) ⟨3053537, by rfl⟩ : syracuseStep 4071383 = 6107075) B6107075
theorem B10297489 : Blo 1204419 10297489 := bstep (se 2 (by rfl) ⟨3861558, by rfl⟩ : syracuseStep 10297489 = 7723117) B7723117
theorem B1204719 : Blo 1204419 1204719 := bstep (se 1 (by rfl) ⟨903539, by rfl⟩ : syracuseStep 1204719 = 1807079) B1807079
theorem B1204987 : Blo 1204419 1204987 := bstep (se 1 (by rfl) ⟨903740, by rfl⟩ : syracuseStep 1204987 = 1807481) B1807481
theorem B1524511 : Blo 1204419 1524511 := bstep (se 1 (by rfl) ⟨1143383, by rfl⟩ : syracuseStep 1524511 = 2286767) B2286767
theorem B6521725 : Blo 1204419 6521725 := bstep (se 3 (by rfl) ⟨1222823, by rfl⟩ : syracuseStep 6521725 = 2445647) B2445647
theorem B2712527 : Blo 1204419 2712527 := bstep (se 1 (by rfl) ⟨2034395, by rfl⟩ : syracuseStep 2712527 = 4068791) B4068791
theorem B3859433 : Blo 1204419 3859433 := bstep (se 2 (by rfl) ⟨1447287, by rfl⟩ : syracuseStep 3859433 = 2894575) B2894575
theorem B2286623 : Blo 1204419 2286623 := bstep (se 1 (by rfl) ⟨1714967, by rfl⟩ : syracuseStep 2286623 = 3429935) B3429935
theorem B10298447 : Blo 1204419 10298447 := bstep (se 1 (by rfl) ⟨7723835, by rfl⟩ : syracuseStep 10298447 = 15447671) B15447671
theorem B1205407 : Blo 1204419 1205407 := bstep (se 1 (by rfl) ⟨904055, by rfl⟩ : syracuseStep 1205407 = 1808111) B1808111
theorem B5792953 : Blo 1204419 5792953 := bstep (se 2 (by rfl) ⟨2172357, by rfl⟩ : syracuseStep 5792953 = 4344715) B4344715
theorem B1205575 : Blo 1204419 1205575 := bstep (se 1 (by rfl) ⟨904181, by rfl⟩ : syracuseStep 1205575 = 1808363) B1808363
theorem B1205607 : Blo 1204419 1205607 := bstep (se 1 (by rfl) ⟨904205, by rfl⟩ : syracuseStep 1205607 = 1808411) B1808411
theorem B2573689 : Blo 1204419 2573689 := bstep (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) B1930267
theorem B1205631 : Blo 1204419 1205631 := bstep (se 1 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 1205631 = 1808447) B1808447
theorem B1205759 : Blo 1204419 1205759 := bstep (se 1 (by rfl) ⟨904319, by rfl⟩ : syracuseStep 1205759 = 1808639) B1808639
theorem B2713193 : Blo 1204419 2713193 := bstep (se 2 (by rfl) ⟨1017447, by rfl⟩ : syracuseStep 2713193 = 2034895) B2034895
theorem B2713247 : Blo 1204419 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B1205919 : Blo 1204419 1205919 := bstep (se 1 (by rfl) ⟨904439, by rfl⟩ : syracuseStep 1205919 = 1808879) B1808879
theorem B3049235 : Blo 1204419 3049235 := bstep (se 1 (by rfl) ⟨2286926, by rfl⟩ : syracuseStep 3049235 = 4573853) B4573853
theorem B4884563 : Blo 1204419 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B2033903 : Blo 1204419 2033903 := bstep (se 1 (by rfl) ⟨1525427, by rfl⟩ : syracuseStep 2033903 = 3050855) B3050855
theorem B2714255 : Blo 1204419 2714255 := bstep (se 1 (by rfl) ⟨2035691, by rfl⟩ : syracuseStep 2714255 = 4071383) B4071383
theorem B2714399 : Blo 1204419 2714399 := bstep (se 1 (by rfl) ⟨2035799, by rfl⟩ : syracuseStep 2714399 = 4071599) B4071599
theorem B75189059 : Blo 1204419 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B89197433 : Blo 1204419 89197433 := bstep (se 2 (by rfl) ⟨33449037, by rfl⟩ : syracuseStep 89197433 = 66898075) B66898075
theorem B6098003 : Blo 1204419 6098003 := bstep (se 1 (by rfl) ⟨4573502, by rfl⟩ : syracuseStep 6098003 = 9147005) B9147005
theorem B105622865 : Blo 1204419 105622865 := bstep (se 2 (by rfl) ⟨39608574, by rfl⟩ : syracuseStep 105622865 = 79217149) B79217149
theorem B20893301 : Blo 1204419 20893301 := bstep (se 5 (by rfl) ⟨979373, by rfl⟩ : syracuseStep 20893301 = 1958747) B1958747
theorem B3051179 : Blo 1204419 3051179 := bstep (se 1 (by rfl) ⟨2288384, by rfl⟩ : syracuseStep 3051179 = 4576769) B4576769
theorem B2748169 : Blo 1204419 2748169 := bstep (se 2 (by rfl) ⟨1030563, by rfl⟩ : syracuseStep 2748169 = 2061127) B2061127
theorem B6868799 : Blo 1204419 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B1355719 : Blo 1204419 1355719 := bstep (se 1 (by rfl) ⟨1016789, by rfl⟩ : syracuseStep 1355719 = 2033579) B2033579
theorem B6098975 : Blo 1204419 6098975 := bstep (se 1 (by rfl) ⟨4574231, by rfl⟩ : syracuseStep 6098975 = 9148463) B9148463
theorem B1806761 : Blo 1204419 1806761 := bstep (se 2 (by rfl) ⟨677535, by rfl⟩ : syracuseStep 1806761 = 1355071) B1355071
theorem B11580029 : Blo 1204419 11580029 := bstep (se 3 (by rfl) ⟨2171255, by rfl⟩ : syracuseStep 11580029 = 4342511) B4342511
theorem B19813241 : Blo 1204419 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B6099947 : Blo 1204419 6099947 := bstep (se 1 (by rfl) ⟨4574960, by rfl⟩ : syracuseStep 6099947 = 9149921) B9149921
theorem B1807919 : Blo 1204419 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B11580985 : Blo 1204419 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B111368033 : Blo 1204419 111368033 := bstep (se 2 (by rfl) ⟨41763012, by rfl⟩ : syracuseStep 111368033 = 83526025) B83526025
theorem B3053659 : Blo 1204419 3053659 := bstep (se 1 (by rfl) ⟨2290244, by rfl⟩ : syracuseStep 3053659 = 4580489) B4580489
theorem B1808615 : Blo 1204419 1808615 := bstep (se 1 (by rfl) ⟨1356461, by rfl⟩ : syracuseStep 1808615 = 2712923) B2712923
theorem B26081615 : Blo 1204419 26081615 := bstep (se 1 (by rfl) ⟨19561211, by rfl⟩ : syracuseStep 26081615 = 39122423) B39122423
theorem B45210191 : Blo 1204419 45210191 := bstep (se 1 (by rfl) ⟨33907643, by rfl⟩ : syracuseStep 45210191 = 67815287) B67815287
theorem B1809191 : Blo 1204419 1809191 := bstep (se 1 (by rfl) ⟨1356893, by rfl⟩ : syracuseStep 1809191 = 2713787) B2713787
theorem B17374247 : Blo 1204419 17374247 := bstep (se 1 (by rfl) ⟨13030685, by rfl⟩ : syracuseStep 17374247 = 26061371) B26061371
theorem B4340911 : Blo 1204419 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B2710763 : Blo 1204419 2710763 := bstep (se 1 (by rfl) ⟨2033072, by rfl⟩ : syracuseStep 2710763 = 4066145) B4066145
theorem B4070735 : Blo 1204419 4070735 := bstep (se 1 (by rfl) ⟨3053051, by rfl⟩ : syracuseStep 4070735 = 6106103) B6106103
theorem B2710943 : Blo 1204419 2710943 := bstep (se 1 (by rfl) ⟨2033207, by rfl⟩ : syracuseStep 2710943 = 4066415) B4066415
theorem B264109571 : Blo 1204419 264109571 := bstep (se 1 (by rfl) ⟨198082178, by rfl⟩ : syracuseStep 264109571 = 396164357) B396164357
theorem B2711195 : Blo 1204419 2711195 := bstep (se 1 (by rfl) ⟨2033396, by rfl⟩ : syracuseStep 2711195 = 4066793) B4066793
theorem B4071545 : Blo 1204419 4071545 := bstep (se 2 (by rfl) ⟨1526829, by rfl⟩ : syracuseStep 4071545 = 3053659) B3053659
theorem B13729985 : Blo 1204419 13729985 := bstep (se 2 (by rfl) ⟨5148744, by rfl⟩ : syracuseStep 13729985 = 10297489) B10297489
theorem B1204507 : Blo 1204419 1204507 := bstep (se 1 (by rfl) ⟨903380, by rfl⟩ : syracuseStep 1204507 = 1806761) B1806761
theorem B2572955 : Blo 1204419 2572955 := bstep (se 1 (by rfl) ⟨1929716, by rfl⟩ : syracuseStep 2572955 = 3859433) B3859433
theorem B1524415 : Blo 1204419 1524415 := bstep (se 1 (by rfl) ⟨1143311, by rfl⟩ : syracuseStep 1524415 = 2286623) B2286623
theorem B6865631 : Blo 1204419 6865631 := bstep (se 1 (by rfl) ⟨5149223, by rfl⟩ : syracuseStep 6865631 = 10298447) B10298447
theorem B1205279 : Blo 1204419 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B2032681 : Blo 1204419 2032681 := bstep (se 2 (by rfl) ⟨762255, by rfl⟩ : syracuseStep 2032681 = 1524511) B1524511
theorem B2032823 : Blo 1204419 2032823 := bstep (se 1 (by rfl) ⟨1524617, by rfl⟩ : syracuseStep 2032823 = 3049235) B3049235
theorem B74245355 : Blo 1204419 74245355 := bstep (se 1 (by rfl) ⟨55684016, by rfl⟩ : syracuseStep 74245355 = 111368033) B111368033
theorem B1205743 : Blo 1204419 1205743 := bstep (se 1 (by rfl) ⟨904307, by rfl⟩ : syracuseStep 1205743 = 1808615) B1808615
theorem B1206127 : Blo 1204419 1206127 := bstep (se 1 (by rfl) ⟨904595, by rfl⟩ : syracuseStep 1206127 = 1809191) B1809191
theorem B4065335 : Blo 1204419 4065335 := bstep (se 1 (by rfl) ⟨3049001, by rfl⟩ : syracuseStep 4065335 = 6098003) B6098003
theorem B2713823 : Blo 1204419 2713823 := bstep (se 1 (by rfl) ⟨2035367, by rfl⟩ : syracuseStep 2713823 = 4070735) B4070735
theorem B176073047 : Blo 1204419 176073047 := bstep (se 1 (by rfl) ⟨132054785, by rfl⟩ : syracuseStep 176073047 = 264109571) B264109571
theorem B3664225 : Blo 1204419 3664225 := bstep (se 2 (by rfl) ⟨1374084, by rfl⟩ : syracuseStep 3664225 = 2748169) B2748169
theorem B13928867 : Blo 1204419 13928867 := bstep (se 1 (by rfl) ⟨10446650, by rfl⟩ : syracuseStep 13928867 = 20893301) B20893301
theorem B2034119 : Blo 1204419 2034119 := bstep (se 1 (by rfl) ⟨1525589, by rfl⟩ : syracuseStep 2034119 = 3051179) B3051179
theorem B4065983 : Blo 1204419 4065983 := bstep (se 1 (by rfl) ⟨3049487, by rfl⟩ : syracuseStep 4065983 = 6098975) B6098975
theorem B7720019 : Blo 1204419 7720019 := bstep (se 1 (by rfl) ⟨5790014, by rfl⟩ : syracuseStep 7720019 = 11580029) B11580029
theorem B13208827 : Blo 1204419 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B4066631 : Blo 1204419 4066631 := bstep (se 1 (by rfl) ⟨3049973, by rfl⟩ : syracuseStep 4066631 = 6099947) B6099947
theorem B8695633 : Blo 1204419 8695633 := bstep (se 2 (by rfl) ⟨3260862, by rfl⟩ : syracuseStep 8695633 = 6521725) B6521725
theorem B3256375 : Blo 1204419 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B1355935 : Blo 1204419 1355935 := bstep (se 1 (by rfl) ⟨1016951, by rfl⟩ : syracuseStep 1355935 = 2033903) B2033903
theorem B17387743 : Blo 1204419 17387743 := bstep (se 1 (by rfl) ⟨13040807, by rfl⟩ : syracuseStep 17387743 = 26081615) B26081615
theorem B5787881 : Blo 1204419 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B1807175 : Blo 1204419 1807175 := bstep (se 1 (by rfl) ⟨1355381, by rfl⟩ : syracuseStep 1807175 = 2710763) B2710763
theorem B70415243 : Blo 1204419 70415243 := bstep (se 1 (by rfl) ⟨52811432, by rfl⟩ : syracuseStep 70415243 = 105622865) B105622865
theorem B1807295 : Blo 1204419 1807295 := bstep (se 1 (by rfl) ⟨1355471, by rfl⟩ : syracuseStep 1807295 = 2710943) B2710943
theorem B1807463 : Blo 1204419 1807463 := bstep (se 1 (by rfl) ⟨1355597, by rfl⟩ : syracuseStep 1807463 = 2711195) B2711195
theorem B1807625 : Blo 1204419 1807625 := bstep (se 2 (by rfl) ⟨677859, by rfl⟩ : syracuseStep 1807625 = 1355719) B1355719
theorem B1808351 : Blo 1204419 1808351 := bstep (se 1 (by rfl) ⟨1356263, by rfl⟩ : syracuseStep 1808351 = 2712527) B2712527
theorem B1808795 : Blo 1204419 1808795 := bstep (se 1 (by rfl) ⟨1356596, by rfl⟩ : syracuseStep 1808795 = 2713193) B2713193
theorem B1808831 : Blo 1204419 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B120560509 : Blo 1204419 120560509 := bstep (se 3 (by rfl) ⟨22605095, by rfl⟩ : syracuseStep 120560509 = 45210191) B45210191
theorem B7723937 : Blo 1204419 7723937 := bstep (se 2 (by rfl) ⟨2896476, by rfl⟩ : syracuseStep 7723937 = 5792953) B5792953
theorem B1809503 : Blo 1204419 1809503 := bstep (se 1 (by rfl) ⟨1357127, by rfl⟩ : syracuseStep 1809503 = 2714255) B2714255
theorem B3431585 : Blo 1204419 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B1809599 : Blo 1204419 1809599 := bstep (se 1 (by rfl) ⟨1357199, by rfl⟩ : syracuseStep 1809599 = 2714399) B2714399
theorem B50126039 : Blo 1204419 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B59464955 : Blo 1204419 59464955 := bstep (se 1 (by rfl) ⟨44598716, by rfl⟩ : syracuseStep 59464955 = 89197433) B89197433
theorem B11582831 : Blo 1204419 11582831 := bstep (se 1 (by rfl) ⟨8687123, by rfl⟩ : syracuseStep 11582831 = 17374247) B17374247
theorem B15441313 : Blo 1204419 15441313 := bstep (se 2 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 15441313 = 11580985) B11580985
theorem B4579199 : Blo 1204419 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B4341833 : Blo 1204419 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B3858587 : Blo 1204419 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B23183657 : Blo 1204419 23183657 := bstep (se 2 (by rfl) ⟨8693871, by rfl⟩ : syracuseStep 23183657 = 17387743) B17387743
theorem B9150893 : Blo 1204419 9150893 := bstep (se 3 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 9150893 = 3431585) B3431585
theorem B1204783 : Blo 1204419 1204783 := bstep (se 1 (by rfl) ⟨903587, by rfl⟩ : syracuseStep 1204783 = 1807175) B1807175
theorem B1204863 : Blo 1204419 1204863 := bstep (se 1 (by rfl) ⟨903647, by rfl⟩ : syracuseStep 1204863 = 1807295) B1807295
theorem B1204975 : Blo 1204419 1204975 := bstep (se 1 (by rfl) ⟨903731, by rfl⟩ : syracuseStep 1204975 = 1807463) B1807463
theorem B49496903 : Blo 1204419 49496903 := bstep (se 1 (by rfl) ⟨37122677, by rfl⟩ : syracuseStep 49496903 = 74245355) B74245355
theorem B1205083 : Blo 1204419 1205083 := bstep (se 1 (by rfl) ⟨903812, by rfl⟩ : syracuseStep 1205083 = 1807625) B1807625
theorem B2032553 : Blo 1204419 2032553 := bstep (se 2 (by rfl) ⟨762207, by rfl⟩ : syracuseStep 2032553 = 1524415) B1524415
theorem B1205567 : Blo 1204419 1205567 := bstep (se 1 (by rfl) ⟨904175, by rfl⟩ : syracuseStep 1205567 = 1808351) B1808351
theorem B1205863 : Blo 1204419 1205863 := bstep (se 1 (by rfl) ⟨904397, by rfl⟩ : syracuseStep 1205863 = 1808795) B1808795
theorem B1205887 : Blo 1204419 1205887 := bstep (se 1 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 1205887 = 1808831) B1808831
theorem B20588417 : Blo 1204419 20588417 := bstep (se 2 (by rfl) ⟨7720656, by rfl⟩ : syracuseStep 20588417 = 15441313) B15441313
theorem B5146679 : Blo 1204419 5146679 := bstep (se 1 (by rfl) ⟨3860009, by rfl⟩ : syracuseStep 5146679 = 7720019) B7720019
theorem B1206335 : Blo 1204419 1206335 := bstep (se 1 (by rfl) ⟨904751, by rfl⟩ : syracuseStep 1206335 = 1809503) B1809503
theorem B1206399 : Blo 1204419 1206399 := bstep (se 1 (by rfl) ⟨904799, by rfl⟩ : syracuseStep 1206399 = 1809599) B1809599
theorem B33417359 : Blo 1204419 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B39643303 : Blo 1204419 39643303 := bstep (se 1 (by rfl) ⟨29732477, by rfl⟩ : syracuseStep 39643303 = 59464955) B59464955
theorem B20597165 : Blo 1204419 20597165 := bstep (se 3 (by rfl) ⟨3861968, by rfl⟩ : syracuseStep 20597165 = 7723937) B7723937
theorem B11594177 : Blo 1204419 11594177 := bstep (se 2 (by rfl) ⟨4347816, by rfl⟩ : syracuseStep 11594177 = 8695633) B8695633
theorem B2714363 : Blo 1204419 2714363 := bstep (se 1 (by rfl) ⟨2035772, by rfl⟩ : syracuseStep 2714363 = 4071545) B4071545
theorem B9153323 : Blo 1204419 9153323 := bstep (se 1 (by rfl) ⟨6864992, by rfl⟩ : syracuseStep 9153323 = 13729985) B13729985
theorem B1715303 : Blo 1204419 1715303 := bstep (se 1 (by rfl) ⟨1286477, by rfl⟩ : syracuseStep 1715303 = 2572955) B2572955
theorem B4885633 : Blo 1204419 4885633 := bstep (se 2 (by rfl) ⟨1832112, by rfl⟩ : syracuseStep 4885633 = 3664225) B3664225
theorem B46943495 : Blo 1204419 46943495 := bstep (se 1 (by rfl) ⟨35207621, by rfl⟩ : syracuseStep 46943495 = 70415243) B70415243
theorem B1355215 : Blo 1204419 1355215 := bstep (se 1 (by rfl) ⟨1016411, by rfl⟩ : syracuseStep 1355215 = 2032823) B2032823
theorem B160747345 : Blo 1204419 160747345 := bstep (se 2 (by rfl) ⟨60280254, by rfl⟩ : syracuseStep 160747345 = 120560509) B120560509
theorem B9285911 : Blo 1204419 9285911 := bstep (se 1 (by rfl) ⟨6964433, by rfl⟩ : syracuseStep 9285911 = 13928867) B13928867
theorem B1356079 : Blo 1204419 1356079 := bstep (se 1 (by rfl) ⟨1017059, by rfl⟩ : syracuseStep 1356079 = 2034119) B2034119
theorem B7721887 : Blo 1204419 7721887 := bstep (se 1 (by rfl) ⟨5791415, by rfl⟩ : syracuseStep 7721887 = 11582831) B11582831
theorem B3052799 : Blo 1204419 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B1807913 : Blo 1204419 1807913 := bstep (se 2 (by rfl) ⟨677967, by rfl⟩ : syracuseStep 1807913 = 1355935) B1355935
theorem B4577087 : Blo 1204419 4577087 := bstep (se 1 (by rfl) ⟨3432815, by rfl⟩ : syracuseStep 4577087 = 6865631) B6865631
theorem B2710223 : Blo 1204419 2710223 := bstep (se 1 (by rfl) ⟨2032667, by rfl⟩ : syracuseStep 2710223 = 4065335) B4065335
theorem B2710241 : Blo 1204419 2710241 := bstep (se 2 (by rfl) ⟨1016340, by rfl⟩ : syracuseStep 2710241 = 2032681) B2032681
theorem B1809215 : Blo 1204419 1809215 := bstep (se 1 (by rfl) ⟨1356911, by rfl⟩ : syracuseStep 1809215 = 2713823) B2713823
theorem B117382031 : Blo 1204419 117382031 := bstep (se 1 (by rfl) ⟨88036523, by rfl⟩ : syracuseStep 117382031 = 176073047) B176073047
theorem B17611769 : Blo 1204419 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B2710655 : Blo 1204419 2710655 := bstep (se 1 (by rfl) ⟨2032991, by rfl⟩ : syracuseStep 2710655 = 4065983) B4065983
theorem B2711087 : Blo 1204419 2711087 := bstep (se 1 (by rfl) ⟨2033315, by rfl⟩ : syracuseStep 2711087 = 4066631) B4066631
theorem B2572391 : Blo 1204419 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B32997935 : Blo 1204419 32997935 := bstep (se 1 (by rfl) ⟨24748451, by rfl⟩ : syracuseStep 32997935 = 49496903) B49496903
theorem B1205275 : Blo 1204419 1205275 := bstep (se 1 (by rfl) ⟨903956, by rfl⟩ : syracuseStep 1205275 = 1807913) B1807913
theorem B6514177 : Blo 1204419 6514177 := bstep (se 2 (by rfl) ⟨2442816, by rfl⟩ : syracuseStep 6514177 = 4885633) B4885633
theorem B13731443 : Blo 1204419 13731443 := bstep (se 1 (by rfl) ⟨10298582, by rfl⟩ : syracuseStep 13731443 = 20597165) B20597165
theorem B857319173 : Blo 1204419 857319173 := bstep (se 4 (by rfl) ⟨80373672, by rfl⟩ : syracuseStep 857319173 = 160747345) B160747345
theorem B1206143 : Blo 1204419 1206143 := bstep (se 1 (by rfl) ⟨904607, by rfl⟩ : syracuseStep 1206143 = 1809215) B1809215
theorem B31295663 : Blo 1204419 31295663 := bstep (se 1 (by rfl) ⟨23471747, by rfl⟩ : syracuseStep 31295663 = 46943495) B46943495
theorem B2894555 : Blo 1204419 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B52857737 : Blo 1204419 52857737 := bstep (se 2 (by rfl) ⟨19821651, by rfl⟩ : syracuseStep 52857737 = 39643303) B39643303
theorem B4574141 : Blo 1204419 4574141 := bstep (se 3 (by rfl) ⟨857651, by rfl⟩ : syracuseStep 4574141 = 1715303) B1715303
theorem B1355035 : Blo 1204419 1355035 := bstep (se 1 (by rfl) ⟨1016276, by rfl⟩ : syracuseStep 1355035 = 2032553) B2032553
theorem B2035199 : Blo 1204419 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B3051391 : Blo 1204419 3051391 := bstep (se 1 (by rfl) ⟨2288543, by rfl⟩ : syracuseStep 3051391 = 4577087) B4577087
theorem B13725611 : Blo 1204419 13725611 := bstep (se 1 (by rfl) ⟨10294208, by rfl⟩ : syracuseStep 13725611 = 20588417) B20588417
theorem B22278239 : Blo 1204419 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B7729451 : Blo 1204419 7729451 := bstep (se 1 (by rfl) ⟨5797088, by rfl⟩ : syracuseStep 7729451 = 11594177) B11594177
theorem B1806815 : Blo 1204419 1806815 := bstep (se 1 (by rfl) ⟨1355111, by rfl⟩ : syracuseStep 1806815 = 2710223) B2710223
theorem B1806827 : Blo 1204419 1806827 := bstep (se 1 (by rfl) ⟨1355120, by rfl⟩ : syracuseStep 1806827 = 2710241) B2710241
theorem B78254687 : Blo 1204419 78254687 := bstep (se 1 (by rfl) ⟨58691015, by rfl⟩ : syracuseStep 78254687 = 117382031) B117382031
theorem B1806953 : Blo 1204419 1806953 := bstep (se 2 (by rfl) ⟨677607, by rfl⟩ : syracuseStep 1806953 = 1355215) B1355215
theorem B1807103 : Blo 1204419 1807103 := bstep (se 1 (by rfl) ⟨1355327, by rfl⟩ : syracuseStep 1807103 = 2710655) B2710655
theorem B1807391 : Blo 1204419 1807391 := bstep (se 1 (by rfl) ⟨1355543, by rfl⟩ : syracuseStep 1807391 = 2711087) B2711087
theorem B6190607 : Blo 1204419 6190607 := bstep (se 1 (by rfl) ⟨4642955, by rfl⟩ : syracuseStep 6190607 = 9285911) B9285911
theorem B15455771 : Blo 1204419 15455771 := bstep (se 1 (by rfl) ⟨11591828, by rfl⟩ : syracuseStep 15455771 = 23183657) B23183657
theorem B6100595 : Blo 1204419 6100595 := bstep (se 1 (by rfl) ⟨4575446, by rfl⟩ : syracuseStep 6100595 = 9150893) B9150893
theorem B1808105 : Blo 1204419 1808105 := bstep (se 2 (by rfl) ⟨678039, by rfl⟩ : syracuseStep 1808105 = 1356079) B1356079
theorem B10295849 : Blo 1204419 10295849 := bstep (se 2 (by rfl) ⟨3860943, by rfl⟩ : syracuseStep 10295849 = 7721887) B7721887
theorem B3431119 : Blo 1204419 3431119 := bstep (se 1 (by rfl) ⟨2573339, by rfl⟩ : syracuseStep 3431119 = 5146679) B5146679
theorem B1809575 : Blo 1204419 1809575 := bstep (se 1 (by rfl) ⟨1357181, by rfl⟩ : syracuseStep 1809575 = 2714363) B2714363
theorem B6102215 : Blo 1204419 6102215 := bstep (se 1 (by rfl) ⟨4576661, by rfl⟩ : syracuseStep 6102215 = 9153323) B9153323
theorem B46964717 : Blo 1204419 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B14852159 : Blo 1204419 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B5152967 : Blo 1204419 5152967 := bstep (se 1 (by rfl) ⟨3864725, by rfl⟩ : syracuseStep 5152967 = 7729451) B7729451
theorem B1204543 : Blo 1204419 1204543 := bstep (se 1 (by rfl) ⟨903407, by rfl⟩ : syracuseStep 1204543 = 1806815) B1806815
theorem B1204551 : Blo 1204419 1204551 := bstep (se 1 (by rfl) ⟨903413, by rfl⟩ : syracuseStep 1204551 = 1806827) B1806827
theorem B1204635 : Blo 1204419 1204635 := bstep (se 1 (by rfl) ⟨903476, by rfl⟩ : syracuseStep 1204635 = 1806953) B1806953
theorem B1204735 : Blo 1204419 1204735 := bstep (se 1 (by rfl) ⟨903551, by rfl⟩ : syracuseStep 1204735 = 1807103) B1807103
theorem B1204927 : Blo 1204419 1204927 := bstep (se 1 (by rfl) ⟨903695, by rfl⟩ : syracuseStep 1204927 = 1807391) B1807391
theorem B1205403 : Blo 1204419 1205403 := bstep (se 1 (by rfl) ⟨904052, by rfl⟩ : syracuseStep 1205403 = 1808105) B1808105
theorem B7718813 : Blo 1204419 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B3049427 : Blo 1204419 3049427 := bstep (se 1 (by rfl) ⟨2287070, by rfl⟩ : syracuseStep 3049427 = 4574141) B4574141
theorem B8685569 : Blo 1204419 8685569 := bstep (se 2 (by rfl) ⟨3257088, by rfl⟩ : syracuseStep 8685569 = 6514177) B6514177
theorem B1206383 : Blo 1204419 1206383 := bstep (se 1 (by rfl) ⟨904787, by rfl⟩ : syracuseStep 1206383 = 1809575) B1809575
theorem B1714927 : Blo 1204419 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B21998623 : Blo 1204419 21998623 := bstep (se 1 (by rfl) ⟨16498967, by rfl⟩ : syracuseStep 21998623 = 32997935) B32997935
theorem B52169791 : Blo 1204419 52169791 := bstep (se 1 (by rfl) ⟨39127343, by rfl⟩ : syracuseStep 52169791 = 78254687) B78254687
theorem B4574825 : Blo 1204419 4574825 := bstep (se 2 (by rfl) ⟨1715559, by rfl⟩ : syracuseStep 4574825 = 3431119) B3431119
theorem B4067063 : Blo 1204419 4067063 := bstep (se 1 (by rfl) ⟨3050297, by rfl⟩ : syracuseStep 4067063 = 6100595) B6100595
theorem B9154295 : Blo 1204419 9154295 := bstep (se 1 (by rfl) ⟨6865721, by rfl⟩ : syracuseStep 9154295 = 13731443) B13731443
theorem B1806713 : Blo 1204419 1806713 := bstep (se 2 (by rfl) ⟨677517, by rfl⟩ : syracuseStep 1806713 = 1355035) B1355035
theorem B35238491 : Blo 1204419 35238491 := bstep (se 1 (by rfl) ⟨26428868, by rfl⟩ : syracuseStep 35238491 = 52857737) B52857737
theorem B4068143 : Blo 1204419 4068143 := bstep (se 1 (by rfl) ⟨3051107, by rfl⟩ : syracuseStep 4068143 = 6102215) B6102215
theorem B1356799 : Blo 1204419 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B4068521 : Blo 1204419 4068521 := bstep (se 2 (by rfl) ⟨1525695, by rfl⟩ : syracuseStep 4068521 = 3051391) B3051391
theorem B4127071 : Blo 1204419 4127071 := bstep (se 1 (by rfl) ⟨3095303, by rfl⟩ : syracuseStep 4127071 = 6190607) B6190607
theorem B10303847 : Blo 1204419 10303847 := bstep (se 1 (by rfl) ⟨7727885, by rfl⟩ : syracuseStep 10303847 = 15455771) B15455771
theorem B571546115 : Blo 1204419 571546115 := bstep (se 1 (by rfl) ⟨428659586, by rfl⟩ : syracuseStep 571546115 = 857319173) B857319173
theorem B20863775 : Blo 1204419 20863775 := bstep (se 1 (by rfl) ⟨15647831, by rfl⟩ : syracuseStep 20863775 = 31295663) B31295663
theorem B6863899 : Blo 1204419 6863899 := bstep (se 1 (by rfl) ⟨5147924, by rfl⟩ : syracuseStep 6863899 = 10295849) B10295849
theorem B9150407 : Blo 1204419 9150407 := bstep (se 1 (by rfl) ⟨6862805, by rfl⟩ : syracuseStep 9150407 = 13725611) B13725611
theorem B31309811 : Blo 1204419 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B1204475 : Blo 1204419 1204475 := bstep (se 1 (by rfl) ⟨903356, by rfl⟩ : syracuseStep 1204475 = 1806713) B1806713
theorem B2712095 : Blo 1204419 2712095 := bstep (se 1 (by rfl) ⟨2034071, by rfl⟩ : syracuseStep 2712095 = 4068143) B4068143
theorem B2712347 : Blo 1204419 2712347 := bstep (se 1 (by rfl) ⟨2034260, by rfl⟩ : syracuseStep 2712347 = 4068521) B4068521
theorem B2286569 : Blo 1204419 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B5145875 : Blo 1204419 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B2032951 : Blo 1204419 2032951 := bstep (se 1 (by rfl) ⟨1524713, by rfl⟩ : syracuseStep 2032951 = 3049427) B3049427
theorem B9151865 : Blo 1204419 9151865 := bstep (se 2 (by rfl) ⟨3431949, by rfl⟩ : syracuseStep 9151865 = 6863899) B6863899
theorem B69559721 : Blo 1204419 69559721 := bstep (se 2 (by rfl) ⟨26084895, by rfl⟩ : syracuseStep 69559721 = 52169791) B52169791
theorem B3049883 : Blo 1204419 3049883 := bstep (se 1 (by rfl) ⟨2287412, by rfl⟩ : syracuseStep 3049883 = 4574825) B4574825
theorem B3435311 : Blo 1204419 3435311 := bstep (se 1 (by rfl) ⟨2576483, by rfl⟩ : syracuseStep 3435311 = 5152967) B5152967
theorem B29331497 : Blo 1204419 29331497 := bstep (se 2 (by rfl) ⟨10999311, by rfl⟩ : syracuseStep 29331497 = 21998623) B21998623
theorem B6869231 : Blo 1204419 6869231 := bstep (se 1 (by rfl) ⟨5151923, by rfl⟩ : syracuseStep 6869231 = 10303847) B10303847
theorem B381030743 : Blo 1204419 381030743 := bstep (se 1 (by rfl) ⟨285773057, by rfl⟩ : syracuseStep 381030743 = 571546115) B571546115
theorem B55636733 : Blo 1204419 55636733 := bstep (se 3 (by rfl) ⟨10431887, by rfl⟩ : syracuseStep 55636733 = 20863775) B20863775
theorem B6100271 : Blo 1204419 6100271 := bstep (se 1 (by rfl) ⟨4575203, by rfl⟩ : syracuseStep 6100271 = 9150407) B9150407
theorem B9901439 : Blo 1204419 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B23492327 : Blo 1204419 23492327 := bstep (se 1 (by rfl) ⟨17619245, by rfl⟩ : syracuseStep 23492327 = 35238491) B35238491
theorem B5502761 : Blo 1204419 5502761 := bstep (se 2 (by rfl) ⟨2063535, by rfl⟩ : syracuseStep 5502761 = 4127071) B4127071
theorem B1809065 : Blo 1204419 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B5790379 : Blo 1204419 5790379 := bstep (se 1 (by rfl) ⟨4342784, by rfl⟩ : syracuseStep 5790379 = 8685569) B8685569
theorem B2711375 : Blo 1204419 2711375 := bstep (se 1 (by rfl) ⟨2033531, by rfl⟩ : syracuseStep 2711375 = 4067063) B4067063
theorem B6102863 : Blo 1204419 6102863 := bstep (se 1 (by rfl) ⟨4577147, by rfl⟩ : syracuseStep 6102863 = 9154295) B9154295
theorem B20873207 : Blo 1204419 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B78217325 : Blo 1204419 78217325 := bstep (se 3 (by rfl) ⟨14665748, by rfl⟩ : syracuseStep 78217325 = 29331497) B29331497
theorem B4579487 : Blo 1204419 4579487 := bstep (se 1 (by rfl) ⟨3434615, by rfl⟩ : syracuseStep 4579487 = 6869231) B6869231
theorem B2033255 : Blo 1204419 2033255 := bstep (se 1 (by rfl) ⟨1524941, by rfl⟩ : syracuseStep 2033255 = 3049883) B3049883
theorem B1206043 : Blo 1204419 1206043 := bstep (se 1 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 1206043 = 1809065) B1809065
theorem B62646205 : Blo 1204419 62646205 := bstep (se 3 (by rfl) ⟨11746163, by rfl⟩ : syracuseStep 62646205 = 23492327) B23492327
theorem B6097517 : Blo 1204419 6097517 := bstep (se 3 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 6097517 = 2286569) B2286569
theorem B254020495 : Blo 1204419 254020495 := bstep (se 1 (by rfl) ⟨190515371, by rfl⟩ : syracuseStep 254020495 = 381030743) B381030743
theorem B4066847 : Blo 1204419 4066847 := bstep (se 1 (by rfl) ⟨3050135, by rfl⟩ : syracuseStep 4066847 = 6100271) B6100271
theorem B7720505 : Blo 1204419 7720505 := bstep (se 2 (by rfl) ⟨2895189, by rfl⟩ : syracuseStep 7720505 = 5790379) B5790379
theorem B2290207 : Blo 1204419 2290207 := bstep (se 1 (by rfl) ⟨1717655, by rfl⟩ : syracuseStep 2290207 = 3435311) B3435311
theorem B1807583 : Blo 1204419 1807583 := bstep (se 1 (by rfl) ⟨1355687, by rfl⟩ : syracuseStep 1807583 = 2711375) B2711375
theorem B4068575 : Blo 1204419 4068575 := bstep (se 1 (by rfl) ⟨3051431, by rfl⟩ : syracuseStep 4068575 = 6102863) B6102863
theorem B13915471 : Blo 1204419 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B1808063 : Blo 1204419 1808063 := bstep (se 1 (by rfl) ⟨1356047, by rfl⟩ : syracuseStep 1808063 = 2712095) B2712095
theorem B37091155 : Blo 1204419 37091155 := bstep (se 1 (by rfl) ⟨27818366, by rfl⟩ : syracuseStep 37091155 = 55636733) B55636733
theorem B1808231 : Blo 1204419 1808231 := bstep (se 1 (by rfl) ⟨1356173, by rfl⟩ : syracuseStep 1808231 = 2712347) B2712347
theorem B3430583 : Blo 1204419 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B6101243 : Blo 1204419 6101243 := bstep (se 1 (by rfl) ⟨4575932, by rfl⟩ : syracuseStep 6101243 = 9151865) B9151865
theorem B6600959 : Blo 1204419 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B46373147 : Blo 1204419 46373147 := bstep (se 1 (by rfl) ⟨34779860, by rfl⟩ : syracuseStep 46373147 = 69559721) B69559721
theorem B3668507 : Blo 1204419 3668507 := bstep (se 1 (by rfl) ⟨2751380, by rfl⟩ : syracuseStep 3668507 = 5502761) B5502761
theorem B2710601 : Blo 1204419 2710601 := bstep (se 2 (by rfl) ⟨1016475, by rfl⟩ : syracuseStep 2710601 = 2032951) B2032951
theorem B1205055 : Blo 1204419 1205055 := bstep (se 1 (by rfl) ⟨903791, by rfl⟩ : syracuseStep 1205055 = 1807583) B1807583
theorem B2712383 : Blo 1204419 2712383 := bstep (se 1 (by rfl) ⟨2034287, by rfl⟩ : syracuseStep 2712383 = 4068575) B4068575
theorem B1205375 : Blo 1204419 1205375 := bstep (se 1 (by rfl) ⟨904031, by rfl⟩ : syracuseStep 1205375 = 1808063) B1808063
theorem B1205487 : Blo 1204419 1205487 := bstep (se 1 (by rfl) ⟨904115, by rfl⟩ : syracuseStep 1205487 = 1808231) B1808231
theorem B2287055 : Blo 1204419 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B4400639 : Blo 1204419 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B4065011 : Blo 1204419 4065011 := bstep (se 1 (by rfl) ⟨3048758, by rfl⟩ : syracuseStep 4065011 = 6097517) B6097517
theorem B5147003 : Blo 1204419 5147003 := bstep (se 1 (by rfl) ⟨3860252, by rfl⟩ : syracuseStep 5147003 = 7720505) B7720505
theorem B83528273 : Blo 1204419 83528273 := bstep (se 2 (by rfl) ⟨31323102, by rfl⟩ : syracuseStep 83528273 = 62646205) B62646205
theorem B52144883 : Blo 1204419 52144883 := bstep (se 1 (by rfl) ⟨39108662, by rfl⟩ : syracuseStep 52144883 = 78217325) B78217325
theorem B1355503 : Blo 1204419 1355503 := bstep (se 1 (by rfl) ⟨1016627, by rfl⟩ : syracuseStep 1355503 = 2033255) B2033255
theorem B338693993 : Blo 1204419 338693993 := bstep (se 2 (by rfl) ⟨127010247, by rfl⟩ : syracuseStep 338693993 = 254020495) B254020495
theorem B4067495 : Blo 1204419 4067495 := bstep (se 1 (by rfl) ⟨3050621, by rfl⟩ : syracuseStep 4067495 = 6101243) B6101243
theorem B2445671 : Blo 1204419 2445671 := bstep (se 1 (by rfl) ⟨1834253, by rfl⟩ : syracuseStep 2445671 = 3668507) B3668507
theorem B1807067 : Blo 1204419 1807067 := bstep (se 1 (by rfl) ⟨1355300, by rfl⟩ : syracuseStep 1807067 = 2710601) B2710601
theorem B3052991 : Blo 1204419 3052991 := bstep (se 1 (by rfl) ⟨2289743, by rfl⟩ : syracuseStep 3052991 = 4579487) B4579487
theorem B3053609 : Blo 1204419 3053609 := bstep (se 2 (by rfl) ⟨1145103, by rfl⟩ : syracuseStep 3053609 = 2290207) B2290207
theorem B30915431 : Blo 1204419 30915431 := bstep (se 1 (by rfl) ⟨23186573, by rfl⟩ : syracuseStep 30915431 = 46373147) B46373147
theorem B18553961 : Blo 1204419 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B2711231 : Blo 1204419 2711231 := bstep (se 1 (by rfl) ⟨2033423, by rfl⟩ : syracuseStep 2711231 = 4066847) B4066847
theorem B49454873 : Blo 1204419 49454873 := bstep (se 2 (by rfl) ⟨18545577, by rfl⟩ : syracuseStep 49454873 = 37091155) B37091155
theorem B2711663 : Blo 1204419 2711663 := bstep (se 1 (by rfl) ⟨2033747, by rfl⟩ : syracuseStep 2711663 = 4067495) B4067495
theorem B1204711 : Blo 1204419 1204711 := bstep (se 1 (by rfl) ⟨903533, by rfl⟩ : syracuseStep 1204711 = 1807067) B1807067
theorem B6521789 : Blo 1204419 6521789 := bstep (se 3 (by rfl) ⟨1222835, by rfl⟩ : syracuseStep 6521789 = 2445671) B2445671
theorem B2933759 : Blo 1204419 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B2035327 : Blo 1204419 2035327 := bstep (se 1 (by rfl) ⟨1526495, by rfl⟩ : syracuseStep 2035327 = 3052991) B3052991
theorem B6098813 : Blo 1204419 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B2035739 : Blo 1204419 2035739 := bstep (se 1 (by rfl) ⟨1526804, by rfl⟩ : syracuseStep 2035739 = 3053609) B3053609
theorem B55685515 : Blo 1204419 55685515 := bstep (se 1 (by rfl) ⟨41764136, by rfl⟩ : syracuseStep 55685515 = 83528273) B83528273
theorem B34763255 : Blo 1204419 34763255 := bstep (se 1 (by rfl) ⟨26072441, by rfl⟩ : syracuseStep 34763255 = 52144883) B52144883
theorem B1807337 : Blo 1204419 1807337 := bstep (se 2 (by rfl) ⟨677751, by rfl⟩ : syracuseStep 1807337 = 1355503) B1355503
theorem B1807487 : Blo 1204419 1807487 := bstep (se 1 (by rfl) ⟨1355615, by rfl⟩ : syracuseStep 1807487 = 2711231) B2711231
theorem B32969915 : Blo 1204419 32969915 := bstep (se 1 (by rfl) ⟨24727436, by rfl⟩ : syracuseStep 32969915 = 49454873) B49454873
theorem B1808255 : Blo 1204419 1808255 := bstep (se 1 (by rfl) ⟨1356191, by rfl⟩ : syracuseStep 1808255 = 2712383) B2712383
theorem B2710007 : Blo 1204419 2710007 := bstep (se 1 (by rfl) ⟨2032505, by rfl⟩ : syracuseStep 2710007 = 4065011) B4065011
theorem B3431335 : Blo 1204419 3431335 := bstep (se 1 (by rfl) ⟨2573501, by rfl⟩ : syracuseStep 3431335 = 5147003) B5147003
theorem B20610287 : Blo 1204419 20610287 := bstep (se 1 (by rfl) ⟨15457715, by rfl⟩ : syracuseStep 20610287 = 30915431) B30915431
theorem B12369307 : Blo 1204419 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B225795995 : Blo 1204419 225795995 := bstep (se 1 (by rfl) ⟨169346996, by rfl⟩ : syracuseStep 225795995 = 338693993) B338693993
theorem B23175503 : Blo 1204419 23175503 := bstep (se 1 (by rfl) ⟨17381627, by rfl⟩ : syracuseStep 23175503 = 34763255) B34763255
theorem B1204891 : Blo 1204419 1204891 := bstep (se 1 (by rfl) ⟨903668, by rfl⟩ : syracuseStep 1204891 = 1807337) B1807337
theorem B1204991 : Blo 1204419 1204991 := bstep (se 1 (by rfl) ⟨903743, by rfl⟩ : syracuseStep 1204991 = 1807487) B1807487
theorem B21979943 : Blo 1204419 21979943 := bstep (se 1 (by rfl) ⟨16484957, by rfl⟩ : syracuseStep 21979943 = 32969915) B32969915
theorem B1205503 : Blo 1204419 1205503 := bstep (se 1 (by rfl) ⟨904127, by rfl⟩ : syracuseStep 1205503 = 1808255) B1808255
theorem B16492409 : Blo 1204419 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B13740191 : Blo 1204419 13740191 := bstep (se 1 (by rfl) ⟨10305143, by rfl⟩ : syracuseStep 13740191 = 20610287) B20610287
theorem B2713769 : Blo 1204419 2713769 := bstep (se 2 (by rfl) ⟨1017663, by rfl⟩ : syracuseStep 2713769 = 2035327) B2035327
theorem B4065875 : Blo 1204419 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B150530663 : Blo 1204419 150530663 := bstep (se 1 (by rfl) ⟨112897997, by rfl⟩ : syracuseStep 150530663 = 225795995) B225795995
theorem B74247353 : Blo 1204419 74247353 := bstep (se 2 (by rfl) ⟨27842757, by rfl⟩ : syracuseStep 74247353 = 55685515) B55685515
theorem B4575113 : Blo 1204419 4575113 := bstep (se 2 (by rfl) ⟨1715667, by rfl⟩ : syracuseStep 4575113 = 3431335) B3431335
theorem B1806671 : Blo 1204419 1806671 := bstep (se 1 (by rfl) ⟨1355003, by rfl⟩ : syracuseStep 1806671 = 2710007) B2710007
theorem B1357159 : Blo 1204419 1357159 := bstep (se 1 (by rfl) ⟨1017869, by rfl⟩ : syracuseStep 1357159 = 2035739) B2035739
theorem B1807775 : Blo 1204419 1807775 := bstep (se 1 (by rfl) ⟨1355831, by rfl⟩ : syracuseStep 1807775 = 2711663) B2711663
theorem B4347859 : Blo 1204419 4347859 := bstep (se 1 (by rfl) ⟨3260894, by rfl⟩ : syracuseStep 4347859 = 6521789) B6521789
theorem B1955839 : Blo 1204419 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B1204447 : Blo 1204419 1204447 := bstep (se 1 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 1204447 = 1806671) B1806671
theorem B15450335 : Blo 1204419 15450335 := bstep (se 1 (by rfl) ⟨11587751, by rfl⟩ : syracuseStep 15450335 = 23175503) B23175503
theorem B1205183 : Blo 1204419 1205183 := bstep (se 1 (by rfl) ⟨903887, by rfl⟩ : syracuseStep 1205183 = 1807775) B1807775
theorem B10994939 : Blo 1204419 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B9160127 : Blo 1204419 9160127 := bstep (se 1 (by rfl) ⟨6870095, by rfl⟩ : syracuseStep 9160127 = 13740191) B13740191
theorem B49498235 : Blo 1204419 49498235 := bstep (se 1 (by rfl) ⟨37123676, by rfl⟩ : syracuseStep 49498235 = 74247353) B74247353
theorem B3050075 : Blo 1204419 3050075 := bstep (se 1 (by rfl) ⟨2287556, by rfl⟩ : syracuseStep 3050075 = 4575113) B4575113
theorem B2607785 : Blo 1204419 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B5797145 : Blo 1204419 5797145 := bstep (se 2 (by rfl) ⟨2173929, by rfl⟩ : syracuseStep 5797145 = 4347859) B4347859
theorem B14653295 : Blo 1204419 14653295 := bstep (se 1 (by rfl) ⟨10989971, by rfl⟩ : syracuseStep 14653295 = 21979943) B21979943
theorem B1809179 : Blo 1204419 1809179 := bstep (se 1 (by rfl) ⟨1356884, by rfl⟩ : syracuseStep 1809179 = 2713769) B2713769
theorem B401415101 : Blo 1204419 401415101 := bstep (se 3 (by rfl) ⟨75265331, by rfl⟩ : syracuseStep 401415101 = 150530663) B150530663
theorem B2710583 : Blo 1204419 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B1809545 : Blo 1204419 1809545 := bstep (se 2 (by rfl) ⟨678579, by rfl⟩ : syracuseStep 1809545 = 1357159) B1357159
theorem B32998823 : Blo 1204419 32998823 := bstep (se 1 (by rfl) ⟨24749117, by rfl⟩ : syracuseStep 32998823 = 49498235) B49498235
theorem B2033383 : Blo 1204419 2033383 := bstep (se 1 (by rfl) ⟨1525037, by rfl⟩ : syracuseStep 2033383 = 3050075) B3050075
theorem B1738523 : Blo 1204419 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B1206119 : Blo 1204419 1206119 := bstep (se 1 (by rfl) ⟨904589, by rfl⟩ : syracuseStep 1206119 = 1809179) B1809179
theorem B267610067 : Blo 1204419 267610067 := bstep (se 1 (by rfl) ⟨200707550, by rfl⟩ : syracuseStep 267610067 = 401415101) B401415101
theorem B1206363 : Blo 1204419 1206363 := bstep (se 1 (by rfl) ⟨904772, by rfl⟩ : syracuseStep 1206363 = 1809545) B1809545
theorem B10300223 : Blo 1204419 10300223 := bstep (se 1 (by rfl) ⟨7725167, by rfl⟩ : syracuseStep 10300223 = 15450335) B15450335
theorem B6106751 : Blo 1204419 6106751 := bstep (se 1 (by rfl) ⟨4580063, by rfl⟩ : syracuseStep 6106751 = 9160127) B9160127
theorem B9768863 : Blo 1204419 9768863 := bstep (se 1 (by rfl) ⟨7326647, by rfl⟩ : syracuseStep 9768863 = 14653295) B14653295
theorem B1807055 : Blo 1204419 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B7329959 : Blo 1204419 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B3864763 : Blo 1204419 3864763 := bstep (se 1 (by rfl) ⟨2898572, by rfl⟩ : syracuseStep 3864763 = 5797145) B5797145
theorem B5153017 : Blo 1204419 5153017 := bstep (se 2 (by rfl) ⟨1932381, by rfl⟩ : syracuseStep 5153017 = 3864763) B3864763
theorem B1204703 : Blo 1204419 1204703 := bstep (se 1 (by rfl) ⟨903527, by rfl⟩ : syracuseStep 1204703 = 1807055) B1807055
theorem B178406711 : Blo 1204419 178406711 := bstep (se 1 (by rfl) ⟨133805033, by rfl⟩ : syracuseStep 178406711 = 267610067) B267610067
theorem B6866815 : Blo 1204419 6866815 := bstep (se 1 (by rfl) ⟨5150111, by rfl⟩ : syracuseStep 6866815 = 10300223) B10300223
theorem B21999215 : Blo 1204419 21999215 := bstep (se 1 (by rfl) ⟨16499411, by rfl⟩ : syracuseStep 21999215 = 32998823) B32998823
theorem B4886639 : Blo 1204419 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B4636061 : Blo 1204419 4636061 := bstep (se 3 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 4636061 = 1738523) B1738523
theorem B2711177 : Blo 1204419 2711177 := bstep (se 2 (by rfl) ⟨1016691, by rfl⟩ : syracuseStep 2711177 = 2033383) B2033383
theorem B4071167 : Blo 1204419 4071167 := bstep (se 1 (by rfl) ⟨3053375, by rfl⟩ : syracuseStep 4071167 = 6106751) B6106751
theorem B6512575 : Blo 1204419 6512575 := bstep (se 1 (by rfl) ⟨4884431, by rfl⟩ : syracuseStep 6512575 = 9768863) B9768863
theorem B3090707 : Blo 1204419 3090707 := bstep (se 1 (by rfl) ⟨2318030, by rfl⟩ : syracuseStep 3090707 = 4636061) B4636061
theorem B14666143 : Blo 1204419 14666143 := bstep (se 1 (by rfl) ⟨10999607, by rfl⟩ : syracuseStep 14666143 = 21999215) B21999215
theorem B2714111 : Blo 1204419 2714111 := bstep (se 1 (by rfl) ⟨2035583, by rfl⟩ : syracuseStep 2714111 = 4071167) B4071167
theorem B1807451 : Blo 1204419 1807451 := bstep (se 1 (by rfl) ⟨1355588, by rfl⟩ : syracuseStep 1807451 = 2711177) B2711177
theorem B9155753 : Blo 1204419 9155753 := bstep (se 2 (by rfl) ⟨3433407, by rfl⟩ : syracuseStep 9155753 = 6866815) B6866815
theorem B3257759 : Blo 1204419 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B6870689 : Blo 1204419 6870689 := bstep (se 2 (by rfl) ⟨2576508, by rfl⟩ : syracuseStep 6870689 = 5153017) B5153017
theorem B118937807 : Blo 1204419 118937807 := bstep (se 1 (by rfl) ⟨89203355, by rfl⟩ : syracuseStep 118937807 = 178406711) B178406711
theorem B8683433 : Blo 1204419 8683433 := bstep (se 2 (by rfl) ⟨3256287, by rfl⟩ : syracuseStep 8683433 = 6512575) B6512575
theorem B19554857 : Blo 1204419 19554857 := bstep (se 2 (by rfl) ⟨7333071, by rfl⟩ : syracuseStep 19554857 = 14666143) B14666143
theorem B1204967 : Blo 1204419 1204967 := bstep (se 1 (by rfl) ⟨903725, by rfl⟩ : syracuseStep 1204967 = 1807451) B1807451
theorem B6103835 : Blo 1204419 6103835 := bstep (se 1 (by rfl) ⟨4577876, by rfl⟩ : syracuseStep 6103835 = 9155753) B9155753
theorem B4580459 : Blo 1204419 4580459 := bstep (se 1 (by rfl) ⟨3435344, by rfl⟩ : syracuseStep 4580459 = 6870689) B6870689
theorem B79291871 : Blo 1204419 79291871 := bstep (se 1 (by rfl) ⟨59468903, by rfl⟩ : syracuseStep 79291871 = 118937807) B118937807
theorem B8687357 : Blo 1204419 8687357 := bstep (se 3 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 8687357 = 3257759) B3257759
theorem B2060471 : Blo 1204419 2060471 := bstep (se 1 (by rfl) ⟨1545353, by rfl⟩ : syracuseStep 2060471 = 3090707) B3090707
theorem B5788955 : Blo 1204419 5788955 := bstep (se 1 (by rfl) ⟨4341716, by rfl⟩ : syracuseStep 5788955 = 8683433) B8683433
theorem B1809407 : Blo 1204419 1809407 := bstep (se 1 (by rfl) ⟨1357055, by rfl⟩ : syracuseStep 1809407 = 2714111) B2714111
theorem B1206271 : Blo 1204419 1206271 := bstep (se 1 (by rfl) ⟨904703, by rfl⟩ : syracuseStep 1206271 = 1809407) B1809407
theorem B13036571 : Blo 1204419 13036571 := bstep (se 1 (by rfl) ⟨9777428, by rfl⟩ : syracuseStep 13036571 = 19554857) B19554857
theorem B15437213 : Blo 1204419 15437213 := bstep (se 3 (by rfl) ⟨2894477, by rfl⟩ : syracuseStep 15437213 = 5788955) B5788955
theorem B1373647 : Blo 1204419 1373647 := bstep (se 1 (by rfl) ⟨1030235, by rfl⟩ : syracuseStep 1373647 = 2060471) B2060471
theorem B4069223 : Blo 1204419 4069223 := bstep (se 1 (by rfl) ⟨3051917, by rfl⟩ : syracuseStep 4069223 = 6103835) B6103835
theorem B3053639 : Blo 1204419 3053639 := bstep (se 1 (by rfl) ⟨2290229, by rfl⟩ : syracuseStep 3053639 = 4580459) B4580459
theorem B52861247 : Blo 1204419 52861247 := bstep (se 1 (by rfl) ⟨39645935, by rfl⟩ : syracuseStep 52861247 = 79291871) B79291871
theorem B5791571 : Blo 1204419 5791571 := bstep (se 1 (by rfl) ⟨4343678, by rfl⟩ : syracuseStep 5791571 = 8687357) B8687357
theorem B2712815 : Blo 1204419 2712815 := bstep (se 1 (by rfl) ⟨2034611, by rfl⟩ : syracuseStep 2712815 = 4069223) B4069223
theorem B10291475 : Blo 1204419 10291475 := bstep (se 1 (by rfl) ⟨7718606, by rfl⟩ : syracuseStep 10291475 = 15437213) B15437213
theorem B3861047 : Blo 1204419 3861047 := bstep (se 1 (by rfl) ⟨2895785, by rfl⟩ : syracuseStep 3861047 = 5791571) B5791571
theorem B2035759 : Blo 1204419 2035759 := bstep (se 1 (by rfl) ⟨1526819, by rfl⟩ : syracuseStep 2035759 = 3053639) B3053639
theorem B1831529 : Blo 1204419 1831529 := bstep (se 2 (by rfl) ⟨686823, by rfl⟩ : syracuseStep 1831529 = 1373647) B1373647
theorem B35240831 : Blo 1204419 35240831 := bstep (se 1 (by rfl) ⟨26430623, by rfl⟩ : syracuseStep 35240831 = 52861247) B52861247
theorem B8691047 : Blo 1204419 8691047 := bstep (se 1 (by rfl) ⟨6518285, by rfl⟩ : syracuseStep 8691047 = 13036571) B13036571
theorem B4884077 : Blo 1204419 4884077 := bstep (se 3 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 4884077 = 1831529) B1831529
theorem B2574031 : Blo 1204419 2574031 := bstep (se 1 (by rfl) ⟨1930523, by rfl⟩ : syracuseStep 2574031 = 3861047) B3861047
theorem B5794031 : Blo 1204419 5794031 := bstep (se 1 (by rfl) ⟨4345523, by rfl⟩ : syracuseStep 5794031 = 8691047) B8691047
theorem B2714345 : Blo 1204419 2714345 := bstep (se 2 (by rfl) ⟨1017879, by rfl⟩ : syracuseStep 2714345 = 2035759) B2035759
theorem B6860983 : Blo 1204419 6860983 := bstep (se 1 (by rfl) ⟨5145737, by rfl⟩ : syracuseStep 6860983 = 10291475) B10291475
theorem B1808543 : Blo 1204419 1808543 := bstep (se 1 (by rfl) ⟨1356407, by rfl⟩ : syracuseStep 1808543 = 2712815) B2712815
theorem B23493887 : Blo 1204419 23493887 := bstep (se 1 (by rfl) ⟨17620415, by rfl⟩ : syracuseStep 23493887 = 35240831) B35240831
theorem B1205695 : Blo 1204419 1205695 := bstep (se 1 (by rfl) ⟨904271, by rfl⟩ : syracuseStep 1205695 = 1808543) B1808543
theorem B3256051 : Blo 1204419 3256051 := bstep (se 1 (by rfl) ⟨2442038, by rfl⟩ : syracuseStep 3256051 = 4884077) B4884077
theorem B3862687 : Blo 1204419 3862687 := bstep (se 1 (by rfl) ⟨2897015, by rfl⟩ : syracuseStep 3862687 = 5794031) B5794031
theorem B9147977 : Blo 1204419 9147977 := bstep (se 2 (by rfl) ⟨3430491, by rfl⟩ : syracuseStep 9147977 = 6860983) B6860983
theorem B1809563 : Blo 1204419 1809563 := bstep (se 1 (by rfl) ⟨1357172, by rfl⟩ : syracuseStep 1809563 = 2714345) B2714345
theorem B15662591 : Blo 1204419 15662591 := bstep (se 1 (by rfl) ⟨11746943, by rfl⟩ : syracuseStep 15662591 = 23493887) B23493887
theorem B3432041 : Blo 1204419 3432041 := bstep (se 2 (by rfl) ⟨1287015, by rfl⟩ : syracuseStep 3432041 = 2574031) B2574031
theorem B1206375 : Blo 1204419 1206375 := bstep (se 1 (by rfl) ⟨904781, by rfl⟩ : syracuseStep 1206375 = 1809563) B1809563
theorem B2288027 : Blo 1204419 2288027 := bstep (se 1 (by rfl) ⟨1716020, by rfl⟩ : syracuseStep 2288027 = 3432041) B3432041
theorem B6098651 : Blo 1204419 6098651 := bstep (se 1 (by rfl) ⟨4573988, by rfl⟩ : syracuseStep 6098651 = 9147977) B9147977
theorem B10441727 : Blo 1204419 10441727 := bstep (se 1 (by rfl) ⟨7831295, by rfl⟩ : syracuseStep 10441727 = 15662591) B15662591
theorem B5150249 : Blo 1204419 5150249 := bstep (se 2 (by rfl) ⟨1931343, by rfl⟩ : syracuseStep 5150249 = 3862687) B3862687
theorem B4341401 : Blo 1204419 4341401 := bstep (se 2 (by rfl) ⟨1628025, by rfl⟩ : syracuseStep 4341401 = 3256051) B3256051
theorem B3433499 : Blo 1204419 3433499 := bstep (se 1 (by rfl) ⟨2575124, by rfl⟩ : syracuseStep 3433499 = 5150249) B5150249
theorem B2894267 : Blo 1204419 2894267 := bstep (se 1 (by rfl) ⟨2170700, by rfl⟩ : syracuseStep 2894267 = 4341401) B4341401
theorem B4065767 : Blo 1204419 4065767 := bstep (se 1 (by rfl) ⟨3049325, by rfl⟩ : syracuseStep 4065767 = 6098651) B6098651
theorem B6961151 : Blo 1204419 6961151 := bstep (se 1 (by rfl) ⟨5220863, by rfl⟩ : syracuseStep 6961151 = 10441727) B10441727
theorem B6101405 : Blo 1204419 6101405 := bstep (se 3 (by rfl) ⟨1144013, by rfl⟩ : syracuseStep 6101405 = 2288027) B2288027
theorem B2288999 : Blo 1204419 2288999 := bstep (se 1 (by rfl) ⟨1716749, by rfl⟩ : syracuseStep 2288999 = 3433499) B3433499
theorem B4067603 : Blo 1204419 4067603 := bstep (se 1 (by rfl) ⟨3050702, by rfl⟩ : syracuseStep 4067603 = 6101405) B6101405
theorem B1929511 : Blo 1204419 1929511 := bstep (se 1 (by rfl) ⟨1447133, by rfl⟩ : syracuseStep 1929511 = 2894267) B2894267
theorem B2710511 : Blo 1204419 2710511 := bstep (se 1 (by rfl) ⟨2032883, by rfl⟩ : syracuseStep 2710511 = 4065767) B4065767
theorem B18563069 : Blo 1204419 18563069 := bstep (se 3 (by rfl) ⟨3480575, by rfl⟩ : syracuseStep 18563069 = 6961151) B6961151
theorem B2711735 : Blo 1204419 2711735 := bstep (se 1 (by rfl) ⟨2033801, by rfl⟩ : syracuseStep 2711735 = 4067603) B4067603
theorem B6103997 : Blo 1204419 6103997 := bstep (se 3 (by rfl) ⟨1144499, by rfl⟩ : syracuseStep 6103997 = 2288999) B2288999
theorem B10290725 : Blo 1204419 10290725 := bstep (se 4 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 10290725 = 1929511) B1929511
theorem B1807007 : Blo 1204419 1807007 := bstep (se 1 (by rfl) ⟨1355255, by rfl⟩ : syracuseStep 1807007 = 2710511) B2710511
theorem B12375379 : Blo 1204419 12375379 := bstep (se 1 (by rfl) ⟨9281534, by rfl⟩ : syracuseStep 12375379 = 18563069) B18563069
theorem B1204671 : Blo 1204419 1204671 := bstep (se 1 (by rfl) ⟨903503, by rfl⟩ : syracuseStep 1204671 = 1807007) B1807007
theorem B16500505 : Blo 1204419 16500505 := bstep (se 2 (by rfl) ⟨6187689, by rfl⟩ : syracuseStep 16500505 = 12375379) B12375379
theorem B6860483 : Blo 1204419 6860483 := bstep (se 1 (by rfl) ⟨5145362, by rfl⟩ : syracuseStep 6860483 = 10290725) B10290725
theorem B1807823 : Blo 1204419 1807823 := bstep (se 1 (by rfl) ⟨1355867, by rfl⟩ : syracuseStep 1807823 = 2711735) B2711735
theorem B4069331 : Blo 1204419 4069331 := bstep (se 1 (by rfl) ⟨3051998, by rfl⟩ : syracuseStep 4069331 = 6103997) B6103997
theorem B1205215 : Blo 1204419 1205215 := bstep (se 1 (by rfl) ⟨903911, by rfl⟩ : syracuseStep 1205215 = 1807823) B1807823
theorem B2712887 : Blo 1204419 2712887 := bstep (se 1 (by rfl) ⟨2034665, by rfl⟩ : syracuseStep 2712887 = 4069331) B4069331
theorem B4573655 : Blo 1204419 4573655 := bstep (se 1 (by rfl) ⟨3430241, by rfl⟩ : syracuseStep 4573655 = 6860483) B6860483
theorem B22000673 : Blo 1204419 22000673 := bstep (se 2 (by rfl) ⟨8250252, by rfl⟩ : syracuseStep 22000673 = 16500505) B16500505
theorem B3049103 : Blo 1204419 3049103 := bstep (se 1 (by rfl) ⟨2286827, by rfl⟩ : syracuseStep 3049103 = 4573655) B4573655
theorem B58668461 : Blo 1204419 58668461 := bstep (se 3 (by rfl) ⟨11000336, by rfl⟩ : syracuseStep 58668461 = 22000673) B22000673
theorem B1808591 : Blo 1204419 1808591 := bstep (se 1 (by rfl) ⟨1356443, by rfl⟩ : syracuseStep 1808591 = 2712887) B2712887
theorem B2032735 : Blo 1204419 2032735 := bstep (se 1 (by rfl) ⟨1524551, by rfl⟩ : syracuseStep 2032735 = 3049103) B3049103
theorem B1205727 : Blo 1204419 1205727 := bstep (se 1 (by rfl) ⟨904295, by rfl⟩ : syracuseStep 1205727 = 1808591) B1808591
theorem B39112307 : Blo 1204419 39112307 := bstep (se 1 (by rfl) ⟨29334230, by rfl⟩ : syracuseStep 39112307 = 58668461) B58668461
theorem B2710313 : Blo 1204419 2710313 := bstep (se 2 (by rfl) ⟨1016367, by rfl⟩ : syracuseStep 2710313 = 2032735) B2032735
theorem B26074871 : Blo 1204419 26074871 := bstep (se 1 (by rfl) ⟨19556153, by rfl⟩ : syracuseStep 26074871 = 39112307) B39112307
theorem B1806875 : Blo 1204419 1806875 := bstep (se 1 (by rfl) ⟨1355156, by rfl⟩ : syracuseStep 1806875 = 2710313) B2710313
theorem B17383247 : Blo 1204419 17383247 := bstep (se 1 (by rfl) ⟨13037435, by rfl⟩ : syracuseStep 17383247 = 26074871) B26074871
theorem B1204583 : Blo 1204419 1204583 := bstep (se 1 (by rfl) ⟨903437, by rfl⟩ : syracuseStep 1204583 = 1806875) B1806875
theorem B11588831 : Blo 1204419 11588831 := bstep (se 1 (by rfl) ⟨8691623, by rfl⟩ : syracuseStep 11588831 = 17383247) B17383247
theorem B7725887 : Blo 1204419 7725887 := bstep (se 1 (by rfl) ⟨5794415, by rfl⟩ : syracuseStep 7725887 = 11588831) B11588831
theorem B5150591 : Blo 1204419 5150591 := bstep (se 1 (by rfl) ⟨3862943, by rfl⟩ : syracuseStep 5150591 = 7725887) B7725887
theorem B3433727 : Blo 1204419 3433727 := bstep (se 1 (by rfl) ⟨2575295, by rfl⟩ : syracuseStep 3433727 = 5150591) B5150591
theorem B2289151 : Blo 1204419 2289151 := bstep (se 1 (by rfl) ⟨1716863, by rfl⟩ : syracuseStep 2289151 = 3433727) B3433727
theorem B3052201 : Blo 1204419 3052201 := bstep (se 2 (by rfl) ⟨1144575, by rfl⟩ : syracuseStep 3052201 = 2289151) B2289151
theorem B4069601 : Blo 1204419 4069601 := bstep (se 2 (by rfl) ⟨1526100, by rfl⟩ : syracuseStep 4069601 = 3052201) B3052201
theorem B2713067 : Blo 1204419 2713067 := bstep (se 1 (by rfl) ⟨2034800, by rfl⟩ : syracuseStep 2713067 = 4069601) B4069601
theorem B1808711 : Blo 1204419 1808711 := bstep (se 1 (by rfl) ⟨1356533, by rfl⟩ : syracuseStep 1808711 = 2713067) B2713067
theorem B1205807 : Blo 1204419 1205807 := bstep (se 1 (by rfl) ⟨904355, by rfl⟩ : syracuseStep 1205807 = 1808711) B1808711

theorem C0 (j : ℕ) (h1 : 301104 ≤ j) (h2 : j ≤ 301604) : Blo 1204419 (4 * j + 3) := by
  interval_cases j
  · exact B1204419
  · exact B1204423
  · exact B1204427
  · exact B1204431
  · exact B1204435
  · exact B1204439
  · exact B1204443
  · exact B1204447
  · exact B1204451
  · exact B1204455
  · exact B1204459
  · exact B1204463
  · exact B1204467
  · exact B1204471
  · exact B1204475
  · exact B1204479
  · exact B1204483
  · exact B1204487
  · exact B1204491
  · exact B1204495
  · exact B1204499
  · exact B1204503
  · exact B1204507
  · exact B1204511
  · exact B1204515
  · exact B1204519
  · exact B1204523
  · exact B1204527
  · exact B1204531
  · exact B1204535
  · exact B1204539
  · exact B1204543
  · exact B1204547
  · exact B1204551
  · exact B1204555
  · exact B1204559
  · exact B1204563
  · exact B1204567
  · exact B1204571
  · exact B1204575
  · exact B1204579
  · exact B1204583
  · exact B1204587
  · exact B1204591
  · exact B1204595
  · exact B1204599
  · exact B1204603
  · exact B1204607
  · exact B1204611
  · exact B1204615
  · exact B1204619
  · exact B1204623
  · exact B1204627
  · exact B1204631
  · exact B1204635
  · exact B1204639
  · exact B1204643
  · exact B1204647
  · exact B1204651
  · exact B1204655
  · exact B1204659
  · exact B1204663
  · exact B1204667
  · exact B1204671
  · exact B1204675
  · exact B1204679
  · exact B1204683
  · exact B1204687
  · exact B1204691
  · exact B1204695
  · exact B1204699
  · exact B1204703
  · exact B1204707
  · exact B1204711
  · exact B1204715
  · exact B1204719
  · exact B1204723
  · exact B1204727
  · exact B1204731
  · exact B1204735
  · exact B1204739
  · exact B1204743
  · exact B1204747
  · exact B1204751
  · exact B1204755
  · exact B1204759
  · exact B1204763
  · exact B1204767
  · exact B1204771
  · exact B1204775
  · exact B1204779
  · exact B1204783
  · exact B1204787
  · exact B1204791
  · exact B1204795
  · exact B1204799
  · exact B1204803
  · exact B1204807
  · exact B1204811
  · exact B1204815
  · exact B1204819
  · exact B1204823
  · exact B1204827
  · exact B1204831
  · exact B1204835
  · exact B1204839
  · exact B1204843
  · exact B1204847
  · exact B1204851
  · exact B1204855
  · exact B1204859
  · exact B1204863
  · exact B1204867
  · exact B1204871
  · exact B1204875
  · exact B1204879
  · exact B1204883
  · exact B1204887
  · exact B1204891
  · exact B1204895
  · exact B1204899
  · exact B1204903
  · exact B1204907
  · exact B1204911
  · exact B1204915
  · exact B1204919
  · exact B1204923
  · exact B1204927
  · exact B1204931
  · exact B1204935
  · exact B1204939
  · exact B1204943
  · exact B1204947
  · exact B1204951
  · exact B1204955
  · exact B1204959
  · exact B1204963
  · exact B1204967
  · exact B1204971
  · exact B1204975
  · exact B1204979
  · exact B1204983
  · exact B1204987
  · exact B1204991
  · exact B1204995
  · exact B1204999
  · exact B1205003
  · exact B1205007
  · exact B1205011
  · exact B1205015
  · exact B1205019
  · exact B1205023
  · exact B1205027
  · exact B1205031
  · exact B1205035
  · exact B1205039
  · exact B1205043
  · exact B1205047
  · exact B1205051
  · exact B1205055
  · exact B1205059
  · exact B1205063
  · exact B1205067
  · exact B1205071
  · exact B1205075
  · exact B1205079
  · exact B1205083
  · exact B1205087
  · exact B1205091
  · exact B1205095
  · exact B1205099
  · exact B1205103
  · exact B1205107
  · exact B1205111
  · exact B1205115
  · exact B1205119
  · exact B1205123
  · exact B1205127
  · exact B1205131
  · exact B1205135
  · exact B1205139
  · exact B1205143
  · exact B1205147
  · exact B1205151
  · exact B1205155
  · exact B1205159
  · exact B1205163
  · exact B1205167
  · exact B1205171
  · exact B1205175
  · exact B1205179
  · exact B1205183
  · exact B1205187
  · exact B1205191
  · exact B1205195
  · exact B1205199
  · exact B1205203
  · exact B1205207
  · exact B1205211
  · exact B1205215
  · exact B1205219
  · exact B1205223
  · exact B1205227
  · exact B1205231
  · exact B1205235
  · exact B1205239
  · exact B1205243
  · exact B1205247
  · exact B1205251
  · exact B1205255
  · exact B1205259
  · exact B1205263
  · exact B1205267
  · exact B1205271
  · exact B1205275
  · exact B1205279
  · exact B1205283
  · exact B1205287
  · exact B1205291
  · exact B1205295
  · exact B1205299
  · exact B1205303
  · exact B1205307
  · exact B1205311
  · exact B1205315
  · exact B1205319
  · exact B1205323
  · exact B1205327
  · exact B1205331
  · exact B1205335
  · exact B1205339
  · exact B1205343
  · exact B1205347
  · exact B1205351
  · exact B1205355
  · exact B1205359
  · exact B1205363
  · exact B1205367
  · exact B1205371
  · exact B1205375
  · exact B1205379
  · exact B1205383
  · exact B1205387
  · exact B1205391
  · exact B1205395
  · exact B1205399
  · exact B1205403
  · exact B1205407
  · exact B1205411
  · exact B1205415
  · exact B1205419
  · exact B1205423
  · exact B1205427
  · exact B1205431
  · exact B1205435
  · exact B1205439
  · exact B1205443
  · exact B1205447
  · exact B1205451
  · exact B1205455
  · exact B1205459
  · exact B1205463
  · exact B1205467
  · exact B1205471
  · exact B1205475
  · exact B1205479
  · exact B1205483
  · exact B1205487
  · exact B1205491
  · exact B1205495
  · exact B1205499
  · exact B1205503
  · exact B1205507
  · exact B1205511
  · exact B1205515
  · exact B1205519
  · exact B1205523
  · exact B1205527
  · exact B1205531
  · exact B1205535
  · exact B1205539
  · exact B1205543
  · exact B1205547
  · exact B1205551
  · exact B1205555
  · exact B1205559
  · exact B1205563
  · exact B1205567
  · exact B1205571
  · exact B1205575
  · exact B1205579
  · exact B1205583
  · exact B1205587
  · exact B1205591
  · exact B1205595
  · exact B1205599
  · exact B1205603
  · exact B1205607
  · exact B1205611
  · exact B1205615
  · exact B1205619
  · exact B1205623
  · exact B1205627
  · exact B1205631
  · exact B1205635
  · exact B1205639
  · exact B1205643
  · exact B1205647
  · exact B1205651
  · exact B1205655
  · exact B1205659
  · exact B1205663
  · exact B1205667
  · exact B1205671
  · exact B1205675
  · exact B1205679
  · exact B1205683
  · exact B1205687
  · exact B1205691
  · exact B1205695
  · exact B1205699
  · exact B1205703
  · exact B1205707
  · exact B1205711
  · exact B1205715
  · exact B1205719
  · exact B1205723
  · exact B1205727
  · exact B1205731
  · exact B1205735
  · exact B1205739
  · exact B1205743
  · exact B1205747
  · exact B1205751
  · exact B1205755
  · exact B1205759
  · exact B1205763
  · exact B1205767
  · exact B1205771
  · exact B1205775
  · exact B1205779
  · exact B1205783
  · exact B1205787
  · exact B1205791
  · exact B1205795
  · exact B1205799
  · exact B1205803
  · exact B1205807
  · exact B1205811
  · exact B1205815
  · exact B1205819
  · exact B1205823
  · exact B1205827
  · exact B1205831
  · exact B1205835
  · exact B1205839
  · exact B1205843
  · exact B1205847
  · exact B1205851
  · exact B1205855
  · exact B1205859
  · exact B1205863
  · exact B1205867
  · exact B1205871
  · exact B1205875
  · exact B1205879
  · exact B1205883
  · exact B1205887
  · exact B1205891
  · exact B1205895
  · exact B1205899
  · exact B1205903
  · exact B1205907
  · exact B1205911
  · exact B1205915
  · exact B1205919
  · exact B1205923
  · exact B1205927
  · exact B1205931
  · exact B1205935
  · exact B1205939
  · exact B1205943
  · exact B1205947
  · exact B1205951
  · exact B1205955
  · exact B1205959
  · exact B1205963
  · exact B1205967
  · exact B1205971
  · exact B1205975
  · exact B1205979
  · exact B1205983
  · exact B1205987
  · exact B1205991
  · exact B1205995
  · exact B1205999
  · exact B1206003
  · exact B1206007
  · exact B1206011
  · exact B1206015
  · exact B1206019
  · exact B1206023
  · exact B1206027
  · exact B1206031
  · exact B1206035
  · exact B1206039
  · exact B1206043
  · exact B1206047
  · exact B1206051
  · exact B1206055
  · exact B1206059
  · exact B1206063
  · exact B1206067
  · exact B1206071
  · exact B1206075
  · exact B1206079
  · exact B1206083
  · exact B1206087
  · exact B1206091
  · exact B1206095
  · exact B1206099
  · exact B1206103
  · exact B1206107
  · exact B1206111
  · exact B1206115
  · exact B1206119
  · exact B1206123
  · exact B1206127
  · exact B1206131
  · exact B1206135
  · exact B1206139
  · exact B1206143
  · exact B1206147
  · exact B1206151
  · exact B1206155
  · exact B1206159
  · exact B1206163
  · exact B1206167
  · exact B1206171
  · exact B1206175
  · exact B1206179
  · exact B1206183
  · exact B1206187
  · exact B1206191
  · exact B1206195
  · exact B1206199
  · exact B1206203
  · exact B1206207
  · exact B1206211
  · exact B1206215
  · exact B1206219
  · exact B1206223
  · exact B1206227
  · exact B1206231
  · exact B1206235
  · exact B1206239
  · exact B1206243
  · exact B1206247
  · exact B1206251
  · exact B1206255
  · exact B1206259
  · exact B1206263
  · exact B1206267
  · exact B1206271
  · exact B1206275
  · exact B1206279
  · exact B1206283
  · exact B1206287
  · exact B1206291
  · exact B1206295
  · exact B1206299
  · exact B1206303
  · exact B1206307
  · exact B1206311
  · exact B1206315
  · exact B1206319
  · exact B1206323
  · exact B1206327
  · exact B1206331
  · exact B1206335
  · exact B1206339
  · exact B1206343
  · exact B1206347
  · exact B1206351
  · exact B1206355
  · exact B1206359
  · exact B1206363
  · exact B1206367
  · exact B1206371
  · exact B1206375
  · exact B1206379
  · exact B1206383
  · exact B1206387
  · exact B1206391
  · exact B1206395
  · exact B1206399
  · exact B1206403
  · exact B1206407
  · exact B1206411
  · exact B1206415
  · exact B1206419

theorem solution (m : ℕ) (hlo : 1204419 ≤ m) (hhi : m ≤ 1206419) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 301104 ≤ j := by omega
    have hj2 : j ≤ 301604 := by omega
    have hb : Blo 1204419 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
