-- Prove2me | solution 1 for syracuse_descends_range_1899435_1901435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:49.643746+00:00
-- url     : https://prove2.me/submissions/e4a872c0-d00d-4361-8329-71eb6e0b98cc

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

theorem B2136865 : Blo 1899435 2136865 := bbase (se 2 (by rfl) ⟨801324, by rfl⟩ : syracuseStep 2136865 = 1602649) (by norm_num)
theorem B2849153 : Blo 1899435 2849153 := bstep (se 2 (by rfl) ⟨1068432, by rfl⟩ : syracuseStep 2849153 = 2136865) B2136865
theorem B1899435 : Blo 1899435 1899435 := bstep (se 1 (by rfl) ⟨1424576, by rfl⟩ : syracuseStep 1899435 = 2849153) B2849153
theorem B4807957 : Blo 1899435 4807957 := bbase (se 6 (by rfl) ⟨112686, by rfl⟩ : syracuseStep 4807957 = 225373) (by norm_num)
theorem B6410609 : Blo 1899435 6410609 := bstep (se 2 (by rfl) ⟨2403978, by rfl⟩ : syracuseStep 6410609 = 4807957) B4807957
theorem B4273739 : Blo 1899435 4273739 := bstep (se 1 (by rfl) ⟨3205304, by rfl⟩ : syracuseStep 4273739 = 6410609) B6410609
theorem B2849159 : Blo 1899435 2849159 := bstep (se 1 (by rfl) ⟨2136869, by rfl⟩ : syracuseStep 2849159 = 4273739) B4273739
theorem B1899439 : Blo 1899435 1899439 := bstep (se 1 (by rfl) ⟨1424579, by rfl⟩ : syracuseStep 1899439 = 2849159) B2849159
theorem B2849165 : Blo 1899435 2849165 := bbase (se 3 (by rfl) ⟨534218, by rfl⟩ : syracuseStep 2849165 = 1068437) (by norm_num)
theorem B1899443 : Blo 1899435 1899443 := bstep (se 1 (by rfl) ⟨1424582, by rfl⟩ : syracuseStep 1899443 = 2849165) B2849165
theorem B4273757 : Blo 1899435 4273757 := bbase (se 3 (by rfl) ⟨801329, by rfl⟩ : syracuseStep 4273757 = 1602659) (by norm_num)
theorem B2849171 : Blo 1899435 2849171 := bstep (se 1 (by rfl) ⟨2136878, by rfl⟩ : syracuseStep 2849171 = 4273757) B4273757
theorem B1899447 : Blo 1899435 1899447 := bstep (se 1 (by rfl) ⟨1424585, by rfl⟩ : syracuseStep 1899447 = 2849171) B2849171
theorem B3205325 : Blo 1899435 3205325 := bbase (se 3 (by rfl) ⟨600998, by rfl⟩ : syracuseStep 3205325 = 1201997) (by norm_num)
theorem B2136883 : Blo 1899435 2136883 := bstep (se 1 (by rfl) ⟨1602662, by rfl⟩ : syracuseStep 2136883 = 3205325) B3205325
theorem B2849177 : Blo 1899435 2849177 := bstep (se 2 (by rfl) ⟨1068441, by rfl⟩ : syracuseStep 2849177 = 2136883) B2136883
theorem B1899451 : Blo 1899435 1899451 := bstep (se 1 (by rfl) ⟨1424588, by rfl⟩ : syracuseStep 1899451 = 2849177) B2849177
theorem B2281921 : Blo 1899435 2281921 := bbase (se 2 (by rfl) ⟨855720, by rfl⟩ : syracuseStep 2281921 = 1711441) (by norm_num)
theorem B12170245 : Blo 1899435 12170245 := bstep (se 4 (by rfl) ⟨1140960, by rfl⟩ : syracuseStep 12170245 = 2281921) B2281921
theorem B16226993 : Blo 1899435 16226993 := bstep (se 2 (by rfl) ⟨6085122, by rfl⟩ : syracuseStep 16226993 = 12170245) B12170245
theorem B10817995 : Blo 1899435 10817995 := bstep (se 1 (by rfl) ⟨8113496, by rfl⟩ : syracuseStep 10817995 = 16226993) B16226993
theorem B14423993 : Blo 1899435 14423993 := bstep (se 2 (by rfl) ⟨5408997, by rfl⟩ : syracuseStep 14423993 = 10817995) B10817995
theorem B9615995 : Blo 1899435 9615995 := bstep (se 1 (by rfl) ⟨7211996, by rfl⟩ : syracuseStep 9615995 = 14423993) B14423993
theorem B6410663 : Blo 1899435 6410663 := bstep (se 1 (by rfl) ⟨4807997, by rfl⟩ : syracuseStep 6410663 = 9615995) B9615995
theorem B4273775 : Blo 1899435 4273775 := bstep (se 1 (by rfl) ⟨3205331, by rfl⟩ : syracuseStep 4273775 = 6410663) B6410663
theorem B2849183 : Blo 1899435 2849183 := bstep (se 1 (by rfl) ⟨2136887, by rfl⟩ : syracuseStep 2849183 = 4273775) B4273775
theorem B1899455 : Blo 1899435 1899455 := bstep (se 1 (by rfl) ⟨1424591, by rfl⟩ : syracuseStep 1899455 = 2849183) B2849183
theorem B2849189 : Blo 1899435 2849189 := bbase (se 4 (by rfl) ⟨267111, by rfl⟩ : syracuseStep 2849189 = 534223) (by norm_num)
theorem B1899459 : Blo 1899435 1899459 := bstep (se 1 (by rfl) ⟨1424594, by rfl⟩ : syracuseStep 1899459 = 2849189) B2849189
theorem B2404009 : Blo 1899435 2404009 := bbase (se 2 (by rfl) ⟨901503, by rfl⟩ : syracuseStep 2404009 = 1803007) (by norm_num)
theorem B3205345 : Blo 1899435 3205345 := bstep (se 2 (by rfl) ⟨1202004, by rfl⟩ : syracuseStep 3205345 = 2404009) B2404009
theorem B4273793 : Blo 1899435 4273793 := bstep (se 2 (by rfl) ⟨1602672, by rfl⟩ : syracuseStep 4273793 = 3205345) B3205345
theorem B2849195 : Blo 1899435 2849195 := bstep (se 1 (by rfl) ⟨2136896, by rfl⟩ : syracuseStep 2849195 = 4273793) B4273793
theorem B1899463 : Blo 1899435 1899463 := bstep (se 1 (by rfl) ⟨1424597, by rfl⟩ : syracuseStep 1899463 = 2849195) B2849195
theorem B2136901 : Blo 1899435 2136901 := bbase (se 4 (by rfl) ⟨200334, by rfl⟩ : syracuseStep 2136901 = 400669) (by norm_num)
theorem B2849201 : Blo 1899435 2849201 := bstep (se 2 (by rfl) ⟨1068450, by rfl⟩ : syracuseStep 2849201 = 2136901) B2136901
theorem B1899467 : Blo 1899435 1899467 := bstep (se 1 (by rfl) ⟨1424600, by rfl⟩ : syracuseStep 1899467 = 2849201) B2849201
theorem B3606029 : Blo 1899435 3606029 := bbase (se 3 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 3606029 = 1352261) (by norm_num)
theorem B2404019 : Blo 1899435 2404019 := bstep (se 1 (by rfl) ⟨1803014, by rfl⟩ : syracuseStep 2404019 = 3606029) B3606029
theorem B6410717 : Blo 1899435 6410717 := bstep (se 3 (by rfl) ⟨1202009, by rfl⟩ : syracuseStep 6410717 = 2404019) B2404019
theorem B4273811 : Blo 1899435 4273811 := bstep (se 1 (by rfl) ⟨3205358, by rfl⟩ : syracuseStep 4273811 = 6410717) B6410717
theorem B2849207 : Blo 1899435 2849207 := bstep (se 1 (by rfl) ⟨2136905, by rfl⟩ : syracuseStep 2849207 = 4273811) B4273811
theorem B1899471 : Blo 1899435 1899471 := bstep (se 1 (by rfl) ⟨1424603, by rfl⟩ : syracuseStep 1899471 = 2849207) B2849207
theorem B2849213 : Blo 1899435 2849213 := bbase (se 3 (by rfl) ⟨534227, by rfl⟩ : syracuseStep 2849213 = 1068455) (by norm_num)
theorem B1899475 : Blo 1899435 1899475 := bstep (se 1 (by rfl) ⟨1424606, by rfl⟩ : syracuseStep 1899475 = 2849213) B2849213
theorem B4273829 : Blo 1899435 4273829 := bbase (se 4 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 4273829 = 801343) (by norm_num)
theorem B2849219 : Blo 1899435 2849219 := bstep (se 1 (by rfl) ⟨2136914, by rfl⟩ : syracuseStep 2849219 = 4273829) B4273829
theorem B1899479 : Blo 1899435 1899479 := bstep (se 1 (by rfl) ⟨1424609, by rfl⟩ : syracuseStep 1899479 = 2849219) B2849219
theorem B4808069 : Blo 1899435 4808069 := bbase (se 4 (by rfl) ⟨450756, by rfl⟩ : syracuseStep 4808069 = 901513) (by norm_num)
theorem B3205379 : Blo 1899435 3205379 := bstep (se 1 (by rfl) ⟨2404034, by rfl⟩ : syracuseStep 3205379 = 4808069) B4808069
theorem B2136919 : Blo 1899435 2136919 := bstep (se 1 (by rfl) ⟨1602689, by rfl⟩ : syracuseStep 2136919 = 3205379) B3205379
theorem B2849225 : Blo 1899435 2849225 := bstep (se 2 (by rfl) ⟨1068459, by rfl⟩ : syracuseStep 2849225 = 2136919) B2136919
theorem B1899483 : Blo 1899435 1899483 := bstep (se 1 (by rfl) ⟨1424612, by rfl⟩ : syracuseStep 1899483 = 2849225) B2849225
theorem B3042613 : Blo 1899435 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B4056817 : Blo 1899435 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B5409089 : Blo 1899435 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B3606059 : Blo 1899435 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B9616157 : Blo 1899435 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B6410771 : Blo 1899435 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B4273847 : Blo 1899435 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B2849231 : Blo 1899435 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B1899487 : Blo 1899435 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B2849237 : Blo 1899435 2849237 := bbase (se 7 (by rfl) ⟨33389, by rfl⟩ : syracuseStep 2849237 = 66779) (by norm_num)
theorem B1899491 : Blo 1899435 1899491 := bstep (se 1 (by rfl) ⟨1424618, by rfl⟩ : syracuseStep 1899491 = 2849237) B2849237
theorem B7212149 : Blo 1899435 7212149 := bbase (se 5 (by rfl) ⟨338069, by rfl⟩ : syracuseStep 7212149 = 676139) (by norm_num)
theorem B4808099 : Blo 1899435 4808099 := bstep (se 1 (by rfl) ⟨3606074, by rfl⟩ : syracuseStep 4808099 = 7212149) B7212149
theorem B3205399 : Blo 1899435 3205399 := bstep (se 1 (by rfl) ⟨2404049, by rfl⟩ : syracuseStep 3205399 = 4808099) B4808099
theorem B4273865 : Blo 1899435 4273865 := bstep (se 2 (by rfl) ⟨1602699, by rfl⟩ : syracuseStep 4273865 = 3205399) B3205399
theorem B2849243 : Blo 1899435 2849243 := bstep (se 1 (by rfl) ⟨2136932, by rfl⟩ : syracuseStep 2849243 = 4273865) B4273865
theorem B1899495 : Blo 1899435 1899495 := bstep (se 1 (by rfl) ⟨1424621, by rfl⟩ : syracuseStep 1899495 = 2849243) B2849243
theorem B2136937 : Blo 1899435 2136937 := bbase (se 2 (by rfl) ⟨801351, by rfl⟩ : syracuseStep 2136937 = 1602703) (by norm_num)
theorem B2849249 : Blo 1899435 2849249 := bstep (se 2 (by rfl) ⟨1068468, by rfl⟩ : syracuseStep 2849249 = 2136937) B2136937
theorem B1899499 : Blo 1899435 1899499 := bstep (se 1 (by rfl) ⟨1424624, by rfl⟩ : syracuseStep 1899499 = 2849249) B2849249
theorem B4332197 : Blo 1899435 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B2888131 : Blo 1899435 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B3850841 : Blo 1899435 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B2567227 : Blo 1899435 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B3422969 : Blo 1899435 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B2281979 : Blo 1899435 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B6085277 : Blo 1899435 6085277 := bstep (se 3 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 6085277 = 2281979) B2281979
theorem B4056851 : Blo 1899435 4056851 := bstep (se 1 (by rfl) ⟨3042638, by rfl⟩ : syracuseStep 4056851 = 6085277) B6085277
theorem B10818269 : Blo 1899435 10818269 := bstep (se 3 (by rfl) ⟨2028425, by rfl⟩ : syracuseStep 10818269 = 4056851) B4056851
theorem B7212179 : Blo 1899435 7212179 := bstep (se 1 (by rfl) ⟨5409134, by rfl⟩ : syracuseStep 7212179 = 10818269) B10818269
theorem B4808119 : Blo 1899435 4808119 := bstep (se 1 (by rfl) ⟨3606089, by rfl⟩ : syracuseStep 4808119 = 7212179) B7212179
theorem B6410825 : Blo 1899435 6410825 := bstep (se 2 (by rfl) ⟨2404059, by rfl⟩ : syracuseStep 6410825 = 4808119) B4808119
theorem B4273883 : Blo 1899435 4273883 := bstep (se 1 (by rfl) ⟨3205412, by rfl⟩ : syracuseStep 4273883 = 6410825) B6410825
theorem B2849255 : Blo 1899435 2849255 := bstep (se 1 (by rfl) ⟨2136941, by rfl⟩ : syracuseStep 2849255 = 4273883) B4273883
theorem B1899503 : Blo 1899435 1899503 := bstep (se 1 (by rfl) ⟨1424627, by rfl⟩ : syracuseStep 1899503 = 2849255) B2849255
theorem B2849261 : Blo 1899435 2849261 := bbase (se 3 (by rfl) ⟨534236, by rfl⟩ : syracuseStep 2849261 = 1068473) (by norm_num)
theorem B1899507 : Blo 1899435 1899507 := bstep (se 1 (by rfl) ⟨1424630, by rfl⟩ : syracuseStep 1899507 = 2849261) B2849261
theorem B4273901 : Blo 1899435 4273901 := bbase (se 3 (by rfl) ⟨801356, by rfl⟩ : syracuseStep 4273901 = 1602713) (by norm_num)
theorem B2849267 : Blo 1899435 2849267 := bstep (se 1 (by rfl) ⟨2136950, by rfl⟩ : syracuseStep 2849267 = 4273901) B4273901
theorem B1899511 : Blo 1899435 1899511 := bstep (se 1 (by rfl) ⟨1424633, by rfl⟩ : syracuseStep 1899511 = 2849267) B2849267
theorem B4563989 : Blo 1899435 4563989 := bbase (se 6 (by rfl) ⟨106968, by rfl⟩ : syracuseStep 4563989 = 213937) (by norm_num)
theorem B3042659 : Blo 1899435 3042659 := bstep (se 1 (by rfl) ⟨2281994, by rfl⟩ : syracuseStep 3042659 = 4563989) B4563989
theorem B2028439 : Blo 1899435 2028439 := bstep (se 1 (by rfl) ⟨1521329, by rfl⟩ : syracuseStep 2028439 = 3042659) B3042659
theorem B2704585 : Blo 1899435 2704585 := bstep (se 2 (by rfl) ⟨1014219, by rfl⟩ : syracuseStep 2704585 = 2028439) B2028439
theorem B3606113 : Blo 1899435 3606113 := bstep (se 2 (by rfl) ⟨1352292, by rfl⟩ : syracuseStep 3606113 = 2704585) B2704585
theorem B2404075 : Blo 1899435 2404075 := bstep (se 1 (by rfl) ⟨1803056, by rfl⟩ : syracuseStep 2404075 = 3606113) B3606113
theorem B3205433 : Blo 1899435 3205433 := bstep (se 2 (by rfl) ⟨1202037, by rfl⟩ : syracuseStep 3205433 = 2404075) B2404075
theorem B2136955 : Blo 1899435 2136955 := bstep (se 1 (by rfl) ⟨1602716, by rfl⟩ : syracuseStep 2136955 = 3205433) B3205433
theorem B2849273 : Blo 1899435 2849273 := bstep (se 2 (by rfl) ⟨1068477, by rfl⟩ : syracuseStep 2849273 = 2136955) B2136955
theorem B1899515 : Blo 1899435 1899515 := bstep (se 1 (by rfl) ⟨1424636, by rfl⟩ : syracuseStep 1899515 = 2849273) B2849273
theorem B3249173 : Blo 1899435 3249173 := bbase (se 6 (by rfl) ⟨76152, by rfl⟩ : syracuseStep 3249173 = 152305) (by norm_num)
theorem B8664461 : Blo 1899435 8664461 := bstep (se 3 (by rfl) ⟨1624586, by rfl⟩ : syracuseStep 8664461 = 3249173) B3249173
theorem B5776307 : Blo 1899435 5776307 := bstep (se 1 (by rfl) ⟨4332230, by rfl⟩ : syracuseStep 5776307 = 8664461) B8664461
theorem B61613941 : Blo 1899435 61613941 := bstep (se 5 (by rfl) ⟨2888153, by rfl⟩ : syracuseStep 61613941 = 5776307) B5776307
theorem B82151921 : Blo 1899435 82151921 := bstep (se 2 (by rfl) ⟨30806970, by rfl⟩ : syracuseStep 82151921 = 61613941) B61613941
theorem B54767947 : Blo 1899435 54767947 := bstep (se 1 (by rfl) ⟨41075960, by rfl⟩ : syracuseStep 54767947 = 82151921) B82151921
theorem B73023929 : Blo 1899435 73023929 := bstep (se 2 (by rfl) ⟨27383973, by rfl⟩ : syracuseStep 73023929 = 54767947) B54767947
theorem B48682619 : Blo 1899435 48682619 := bstep (se 1 (by rfl) ⟨36511964, by rfl⟩ : syracuseStep 48682619 = 73023929) B73023929
theorem B32455079 : Blo 1899435 32455079 := bstep (se 1 (by rfl) ⟨24341309, by rfl⟩ : syracuseStep 32455079 = 48682619) B48682619
theorem B21636719 : Blo 1899435 21636719 := bstep (se 1 (by rfl) ⟨16227539, by rfl⟩ : syracuseStep 21636719 = 32455079) B32455079
theorem B14424479 : Blo 1899435 14424479 := bstep (se 1 (by rfl) ⟨10818359, by rfl⟩ : syracuseStep 14424479 = 21636719) B21636719
theorem B9616319 : Blo 1899435 9616319 := bstep (se 1 (by rfl) ⟨7212239, by rfl⟩ : syracuseStep 9616319 = 14424479) B14424479
theorem B6410879 : Blo 1899435 6410879 := bstep (se 1 (by rfl) ⟨4808159, by rfl⟩ : syracuseStep 6410879 = 9616319) B9616319
theorem B4273919 : Blo 1899435 4273919 := bstep (se 1 (by rfl) ⟨3205439, by rfl⟩ : syracuseStep 4273919 = 6410879) B6410879
theorem B2849279 : Blo 1899435 2849279 := bstep (se 1 (by rfl) ⟨2136959, by rfl⟩ : syracuseStep 2849279 = 4273919) B4273919
theorem B1899519 : Blo 1899435 1899519 := bstep (se 1 (by rfl) ⟨1424639, by rfl⟩ : syracuseStep 1899519 = 2849279) B2849279
theorem B2849285 : Blo 1899435 2849285 := bbase (se 4 (by rfl) ⟨267120, by rfl⟩ : syracuseStep 2849285 = 534241) (by norm_num)
theorem B1899523 : Blo 1899435 1899523 := bstep (se 1 (by rfl) ⟨1424642, by rfl⟩ : syracuseStep 1899523 = 2849285) B2849285
theorem B3205453 : Blo 1899435 3205453 := bbase (se 3 (by rfl) ⟨601022, by rfl⟩ : syracuseStep 3205453 = 1202045) (by norm_num)
theorem B4273937 : Blo 1899435 4273937 := bstep (se 2 (by rfl) ⟨1602726, by rfl⟩ : syracuseStep 4273937 = 3205453) B3205453
theorem B2849291 : Blo 1899435 2849291 := bstep (se 1 (by rfl) ⟨2136968, by rfl⟩ : syracuseStep 2849291 = 4273937) B4273937
theorem B1899527 : Blo 1899435 1899527 := bstep (se 1 (by rfl) ⟨1424645, by rfl⟩ : syracuseStep 1899527 = 2849291) B2849291
theorem B2136973 : Blo 1899435 2136973 := bbase (se 3 (by rfl) ⟨400682, by rfl⟩ : syracuseStep 2136973 = 801365) (by norm_num)
theorem B2849297 : Blo 1899435 2849297 := bstep (se 2 (by rfl) ⟨1068486, by rfl⟩ : syracuseStep 2849297 = 2136973) B2136973
theorem B1899531 : Blo 1899435 1899531 := bstep (se 1 (by rfl) ⟨1424648, by rfl⟩ : syracuseStep 1899531 = 2849297) B2849297
theorem B6410933 : Blo 1899435 6410933 := bbase (se 5 (by rfl) ⟨300512, by rfl⟩ : syracuseStep 6410933 = 601025) (by norm_num)
theorem B4273955 : Blo 1899435 4273955 := bstep (se 1 (by rfl) ⟨3205466, by rfl⟩ : syracuseStep 4273955 = 6410933) B6410933
theorem B2849303 : Blo 1899435 2849303 := bstep (se 1 (by rfl) ⟨2136977, by rfl⟩ : syracuseStep 2849303 = 4273955) B4273955
theorem B1899535 : Blo 1899435 1899535 := bstep (se 1 (by rfl) ⟨1424651, by rfl⟩ : syracuseStep 1899535 = 2849303) B2849303
theorem B2849309 : Blo 1899435 2849309 := bbase (se 3 (by rfl) ⟨534245, by rfl⟩ : syracuseStep 2849309 = 1068491) (by norm_num)
theorem B1899539 : Blo 1899435 1899539 := bstep (se 1 (by rfl) ⟨1424654, by rfl⟩ : syracuseStep 1899539 = 2849309) B2849309
theorem B4273973 : Blo 1899435 4273973 := bbase (se 5 (by rfl) ⟨200342, by rfl⟩ : syracuseStep 4273973 = 400685) (by norm_num)
theorem B2849315 : Blo 1899435 2849315 := bstep (se 1 (by rfl) ⟨2136986, by rfl⟩ : syracuseStep 2849315 = 4273973) B4273973
theorem B1899543 : Blo 1899435 1899543 := bstep (se 1 (by rfl) ⟨1424657, by rfl⟩ : syracuseStep 1899543 = 2849315) B2849315
theorem B12170837 : Blo 1899435 12170837 := bbase (se 8 (by rfl) ⟨71313, by rfl⟩ : syracuseStep 12170837 = 142627) (by norm_num)
theorem B8113891 : Blo 1899435 8113891 := bstep (se 1 (by rfl) ⟨6085418, by rfl⟩ : syracuseStep 8113891 = 12170837) B12170837
theorem B10818521 : Blo 1899435 10818521 := bstep (se 2 (by rfl) ⟨4056945, by rfl⟩ : syracuseStep 10818521 = 8113891) B8113891
theorem B7212347 : Blo 1899435 7212347 := bstep (se 1 (by rfl) ⟨5409260, by rfl⟩ : syracuseStep 7212347 = 10818521) B10818521
theorem B4808231 : Blo 1899435 4808231 := bstep (se 1 (by rfl) ⟨3606173, by rfl⟩ : syracuseStep 4808231 = 7212347) B7212347
theorem B3205487 : Blo 1899435 3205487 := bstep (se 1 (by rfl) ⟨2404115, by rfl⟩ : syracuseStep 3205487 = 4808231) B4808231
theorem B2136991 : Blo 1899435 2136991 := bstep (se 1 (by rfl) ⟨1602743, by rfl⟩ : syracuseStep 2136991 = 3205487) B3205487
theorem B2849321 : Blo 1899435 2849321 := bstep (se 2 (by rfl) ⟨1068495, by rfl⟩ : syracuseStep 2849321 = 2136991) B2136991
theorem B1899547 : Blo 1899435 1899547 := bstep (se 1 (by rfl) ⟨1424660, by rfl⟩ : syracuseStep 1899547 = 2849321) B2849321
theorem B3249229 : Blo 1899435 3249229 := bbase (se 3 (by rfl) ⟨609230, by rfl⟩ : syracuseStep 3249229 = 1218461) (by norm_num)
theorem B4332305 : Blo 1899435 4332305 := bstep (se 2 (by rfl) ⟨1624614, by rfl⟩ : syracuseStep 4332305 = 3249229) B3249229
theorem B11552813 : Blo 1899435 11552813 := bstep (se 3 (by rfl) ⟨2166152, by rfl⟩ : syracuseStep 11552813 = 4332305) B4332305
theorem B7701875 : Blo 1899435 7701875 := bstep (se 1 (by rfl) ⟨5776406, by rfl⟩ : syracuseStep 7701875 = 11552813) B11552813
theorem B5134583 : Blo 1899435 5134583 := bstep (se 1 (by rfl) ⟨3850937, by rfl⟩ : syracuseStep 5134583 = 7701875) B7701875
theorem B3423055 : Blo 1899435 3423055 := bstep (se 1 (by rfl) ⟨2567291, by rfl⟩ : syracuseStep 3423055 = 5134583) B5134583
theorem B4564073 : Blo 1899435 4564073 := bstep (se 2 (by rfl) ⟨1711527, by rfl⟩ : syracuseStep 4564073 = 3423055) B3423055
theorem B12170861 : Blo 1899435 12170861 := bstep (se 3 (by rfl) ⟨2282036, by rfl⟩ : syracuseStep 12170861 = 4564073) B4564073
theorem B8113907 : Blo 1899435 8113907 := bstep (se 1 (by rfl) ⟨6085430, by rfl⟩ : syracuseStep 8113907 = 12170861) B12170861
theorem B5409271 : Blo 1899435 5409271 := bstep (se 1 (by rfl) ⟨4056953, by rfl⟩ : syracuseStep 5409271 = 8113907) B8113907
theorem B7212361 : Blo 1899435 7212361 := bstep (se 2 (by rfl) ⟨2704635, by rfl⟩ : syracuseStep 7212361 = 5409271) B5409271
theorem B9616481 : Blo 1899435 9616481 := bstep (se 2 (by rfl) ⟨3606180, by rfl⟩ : syracuseStep 9616481 = 7212361) B7212361
theorem B6410987 : Blo 1899435 6410987 := bstep (se 1 (by rfl) ⟨4808240, by rfl⟩ : syracuseStep 6410987 = 9616481) B9616481
theorem B4273991 : Blo 1899435 4273991 := bstep (se 1 (by rfl) ⟨3205493, by rfl⟩ : syracuseStep 4273991 = 6410987) B6410987
theorem B2849327 : Blo 1899435 2849327 := bstep (se 1 (by rfl) ⟨2136995, by rfl⟩ : syracuseStep 2849327 = 4273991) B4273991
theorem B1899551 : Blo 1899435 1899551 := bstep (se 1 (by rfl) ⟨1424663, by rfl⟩ : syracuseStep 1899551 = 2849327) B2849327
theorem B2849333 : Blo 1899435 2849333 := bbase (se 5 (by rfl) ⟨133562, by rfl⟩ : syracuseStep 2849333 = 267125) (by norm_num)
theorem B1899555 : Blo 1899435 1899555 := bstep (se 1 (by rfl) ⟨1424666, by rfl⟩ : syracuseStep 1899555 = 2849333) B2849333
theorem B4808261 : Blo 1899435 4808261 := bbase (se 4 (by rfl) ⟨450774, by rfl⟩ : syracuseStep 4808261 = 901549) (by norm_num)
theorem B3205507 : Blo 1899435 3205507 := bstep (se 1 (by rfl) ⟨2404130, by rfl⟩ : syracuseStep 3205507 = 4808261) B4808261
theorem B4274009 : Blo 1899435 4274009 := bstep (se 2 (by rfl) ⟨1602753, by rfl⟩ : syracuseStep 4274009 = 3205507) B3205507
theorem B2849339 : Blo 1899435 2849339 := bstep (se 1 (by rfl) ⟨2137004, by rfl⟩ : syracuseStep 2849339 = 4274009) B4274009
theorem B1899559 : Blo 1899435 1899559 := bstep (se 1 (by rfl) ⟨1424669, by rfl⟩ : syracuseStep 1899559 = 2849339) B2849339
theorem B2137009 : Blo 1899435 2137009 := bbase (se 2 (by rfl) ⟨801378, by rfl⟩ : syracuseStep 2137009 = 1602757) (by norm_num)
theorem B2849345 : Blo 1899435 2849345 := bstep (se 2 (by rfl) ⟨1068504, by rfl⟩ : syracuseStep 2849345 = 2137009) B2137009
theorem B1899563 : Blo 1899435 1899563 := bstep (se 1 (by rfl) ⟨1424672, by rfl⟩ : syracuseStep 1899563 = 2849345) B2849345
theorem B5409317 : Blo 1899435 5409317 := bbase (se 4 (by rfl) ⟨507123, by rfl⟩ : syracuseStep 5409317 = 1014247) (by norm_num)
theorem B3606211 : Blo 1899435 3606211 := bstep (se 1 (by rfl) ⟨2704658, by rfl⟩ : syracuseStep 3606211 = 5409317) B5409317
theorem B4808281 : Blo 1899435 4808281 := bstep (se 2 (by rfl) ⟨1803105, by rfl⟩ : syracuseStep 4808281 = 3606211) B3606211
theorem B6411041 : Blo 1899435 6411041 := bstep (se 2 (by rfl) ⟨2404140, by rfl⟩ : syracuseStep 6411041 = 4808281) B4808281
theorem B4274027 : Blo 1899435 4274027 := bstep (se 1 (by rfl) ⟨3205520, by rfl⟩ : syracuseStep 4274027 = 6411041) B6411041
theorem B2849351 : Blo 1899435 2849351 := bstep (se 1 (by rfl) ⟨2137013, by rfl⟩ : syracuseStep 2849351 = 4274027) B4274027
theorem B1899567 : Blo 1899435 1899567 := bstep (se 1 (by rfl) ⟨1424675, by rfl⟩ : syracuseStep 1899567 = 2849351) B2849351
theorem B2849357 : Blo 1899435 2849357 := bbase (se 3 (by rfl) ⟨534254, by rfl⟩ : syracuseStep 2849357 = 1068509) (by norm_num)
theorem B1899571 : Blo 1899435 1899571 := bstep (se 1 (by rfl) ⟨1424678, by rfl⟩ : syracuseStep 1899571 = 2849357) B2849357
theorem B4274045 : Blo 1899435 4274045 := bbase (se 3 (by rfl) ⟨801383, by rfl⟩ : syracuseStep 4274045 = 1602767) (by norm_num)
theorem B2849363 : Blo 1899435 2849363 := bstep (se 1 (by rfl) ⟨2137022, by rfl⟩ : syracuseStep 2849363 = 4274045) B4274045
theorem B1899575 : Blo 1899435 1899575 := bstep (se 1 (by rfl) ⟨1424681, by rfl⟩ : syracuseStep 1899575 = 2849363) B2849363
theorem B3205541 : Blo 1899435 3205541 := bbase (se 4 (by rfl) ⟨300519, by rfl⟩ : syracuseStep 3205541 = 601039) (by norm_num)
theorem B2137027 : Blo 1899435 2137027 := bstep (se 1 (by rfl) ⟨1602770, by rfl⟩ : syracuseStep 2137027 = 3205541) B3205541
theorem B2849369 : Blo 1899435 2849369 := bstep (se 2 (by rfl) ⟨1068513, by rfl⟩ : syracuseStep 2849369 = 2137027) B2137027
theorem B1899579 : Blo 1899435 1899579 := bstep (se 1 (by rfl) ⟨1424684, by rfl⟩ : syracuseStep 1899579 = 2849369) B2849369
theorem B6168565 : Blo 1899435 6168565 := bbase (se 5 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 6168565 = 578303) (by norm_num)
theorem B8224753 : Blo 1899435 8224753 := bstep (se 2 (by rfl) ⟨3084282, by rfl⟩ : syracuseStep 8224753 = 6168565) B6168565
theorem B10966337 : Blo 1899435 10966337 := bstep (se 2 (by rfl) ⟨4112376, by rfl⟩ : syracuseStep 10966337 = 8224753) B8224753
theorem B7310891 : Blo 1899435 7310891 := bstep (se 1 (by rfl) ⟨5483168, by rfl⟩ : syracuseStep 7310891 = 10966337) B10966337
theorem B4873927 : Blo 1899435 4873927 := bstep (se 1 (by rfl) ⟨3655445, by rfl⟩ : syracuseStep 4873927 = 7310891) B7310891
theorem B6498569 : Blo 1899435 6498569 := bstep (se 2 (by rfl) ⟨2436963, by rfl⟩ : syracuseStep 6498569 = 4873927) B4873927
theorem B4332379 : Blo 1899435 4332379 := bstep (se 1 (by rfl) ⟨3249284, by rfl⟩ : syracuseStep 4332379 = 6498569) B6498569
theorem B5776505 : Blo 1899435 5776505 := bstep (se 2 (by rfl) ⟨2166189, by rfl⟩ : syracuseStep 5776505 = 4332379) B4332379
theorem B3851003 : Blo 1899435 3851003 := bstep (se 1 (by rfl) ⟨2888252, by rfl⟩ : syracuseStep 3851003 = 5776505) B5776505
theorem B10269341 : Blo 1899435 10269341 := bstep (se 3 (by rfl) ⟨1925501, by rfl⟩ : syracuseStep 10269341 = 3851003) B3851003
theorem B6846227 : Blo 1899435 6846227 := bstep (se 1 (by rfl) ⟨5134670, by rfl⟩ : syracuseStep 6846227 = 10269341) B10269341
theorem B4564151 : Blo 1899435 4564151 := bstep (se 1 (by rfl) ⟨3423113, by rfl⟩ : syracuseStep 4564151 = 6846227) B6846227
theorem B3042767 : Blo 1899435 3042767 := bstep (se 1 (by rfl) ⟨2282075, by rfl⟩ : syracuseStep 3042767 = 4564151) B4564151
theorem B2028511 : Blo 1899435 2028511 := bstep (se 1 (by rfl) ⟨1521383, by rfl⟩ : syracuseStep 2028511 = 3042767) B3042767
theorem B2704681 : Blo 1899435 2704681 := bstep (se 2 (by rfl) ⟨1014255, by rfl⟩ : syracuseStep 2704681 = 2028511) B2028511
theorem B14424965 : Blo 1899435 14424965 := bstep (se 4 (by rfl) ⟨1352340, by rfl⟩ : syracuseStep 14424965 = 2704681) B2704681
theorem B9616643 : Blo 1899435 9616643 := bstep (se 1 (by rfl) ⟨7212482, by rfl⟩ : syracuseStep 9616643 = 14424965) B14424965
theorem B6411095 : Blo 1899435 6411095 := bstep (se 1 (by rfl) ⟨4808321, by rfl⟩ : syracuseStep 6411095 = 9616643) B9616643
theorem B4274063 : Blo 1899435 4274063 := bstep (se 1 (by rfl) ⟨3205547, by rfl⟩ : syracuseStep 4274063 = 6411095) B6411095
theorem B2849375 : Blo 1899435 2849375 := bstep (se 1 (by rfl) ⟨2137031, by rfl⟩ : syracuseStep 2849375 = 4274063) B4274063
theorem B1899583 : Blo 1899435 1899583 := bstep (se 1 (by rfl) ⟨1424687, by rfl⟩ : syracuseStep 1899583 = 2849375) B2849375
theorem B2849381 : Blo 1899435 2849381 := bbase (se 4 (by rfl) ⟨267129, by rfl⟩ : syracuseStep 2849381 = 534259) (by norm_num)
theorem B1899587 : Blo 1899435 1899587 := bstep (se 1 (by rfl) ⟨1424690, by rfl⟩ : syracuseStep 1899587 = 2849381) B2849381
theorem B2704693 : Blo 1899435 2704693 := bbase (se 5 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 2704693 = 253565) (by norm_num)
theorem B3606257 : Blo 1899435 3606257 := bstep (se 2 (by rfl) ⟨1352346, by rfl⟩ : syracuseStep 3606257 = 2704693) B2704693
theorem B2404171 : Blo 1899435 2404171 := bstep (se 1 (by rfl) ⟨1803128, by rfl⟩ : syracuseStep 2404171 = 3606257) B3606257
theorem B3205561 : Blo 1899435 3205561 := bstep (se 2 (by rfl) ⟨1202085, by rfl⟩ : syracuseStep 3205561 = 2404171) B2404171
theorem B4274081 : Blo 1899435 4274081 := bstep (se 2 (by rfl) ⟨1602780, by rfl⟩ : syracuseStep 4274081 = 3205561) B3205561
theorem B2849387 : Blo 1899435 2849387 := bstep (se 1 (by rfl) ⟨2137040, by rfl⟩ : syracuseStep 2849387 = 4274081) B4274081
theorem B1899591 : Blo 1899435 1899591 := bstep (se 1 (by rfl) ⟨1424693, by rfl⟩ : syracuseStep 1899591 = 2849387) B2849387
theorem B2137045 : Blo 1899435 2137045 := bbase (se 7 (by rfl) ⟨25043, by rfl⟩ : syracuseStep 2137045 = 50087) (by norm_num)
theorem B2849393 : Blo 1899435 2849393 := bstep (se 2 (by rfl) ⟨1068522, by rfl⟩ : syracuseStep 2849393 = 2137045) B2137045
theorem B1899595 : Blo 1899435 1899595 := bstep (se 1 (by rfl) ⟨1424696, by rfl⟩ : syracuseStep 1899595 = 2849393) B2849393
theorem B2404181 : Blo 1899435 2404181 := bbase (se 9 (by rfl) ⟨7043, by rfl⟩ : syracuseStep 2404181 = 14087) (by norm_num)
theorem B6411149 : Blo 1899435 6411149 := bstep (se 3 (by rfl) ⟨1202090, by rfl⟩ : syracuseStep 6411149 = 2404181) B2404181
theorem B4274099 : Blo 1899435 4274099 := bstep (se 1 (by rfl) ⟨3205574, by rfl⟩ : syracuseStep 4274099 = 6411149) B6411149
theorem B2849399 : Blo 1899435 2849399 := bstep (se 1 (by rfl) ⟨2137049, by rfl⟩ : syracuseStep 2849399 = 4274099) B4274099
theorem B1899599 : Blo 1899435 1899599 := bstep (se 1 (by rfl) ⟨1424699, by rfl⟩ : syracuseStep 1899599 = 2849399) B2849399
theorem B2849405 : Blo 1899435 2849405 := bbase (se 3 (by rfl) ⟨534263, by rfl⟩ : syracuseStep 2849405 = 1068527) (by norm_num)
theorem B1899603 : Blo 1899435 1899603 := bstep (se 1 (by rfl) ⟨1424702, by rfl⟩ : syracuseStep 1899603 = 2849405) B2849405
theorem B4274117 : Blo 1899435 4274117 := bbase (se 4 (by rfl) ⟨400698, by rfl⟩ : syracuseStep 4274117 = 801397) (by norm_num)
theorem B2849411 : Blo 1899435 2849411 := bstep (se 1 (by rfl) ⟨2137058, by rfl⟩ : syracuseStep 2849411 = 4274117) B4274117
theorem B1899607 : Blo 1899435 1899607 := bstep (se 1 (by rfl) ⟨1424705, by rfl⟩ : syracuseStep 1899607 = 2849411) B2849411
theorem B8114165 : Blo 1899435 8114165 := bbase (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) (by norm_num)
theorem B5409443 : Blo 1899435 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B3606295 : Blo 1899435 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B4808393 : Blo 1899435 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B3205595 : Blo 1899435 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B2137063 : Blo 1899435 2137063 := bstep (se 1 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 2137063 = 3205595) B3205595
theorem B2849417 : Blo 1899435 2849417 := bstep (se 2 (by rfl) ⟨1068531, by rfl⟩ : syracuseStep 2849417 = 2137063) B2137063
theorem B1899611 : Blo 1899435 1899611 := bstep (se 1 (by rfl) ⟨1424708, by rfl⟩ : syracuseStep 1899611 = 2849417) B2849417
theorem B9616805 : Blo 1899435 9616805 := bbase (se 4 (by rfl) ⟨901575, by rfl⟩ : syracuseStep 9616805 = 1803151) (by norm_num)
theorem B6411203 : Blo 1899435 6411203 := bstep (se 1 (by rfl) ⟨4808402, by rfl⟩ : syracuseStep 6411203 = 9616805) B9616805
theorem B4274135 : Blo 1899435 4274135 := bstep (se 1 (by rfl) ⟨3205601, by rfl⟩ : syracuseStep 4274135 = 6411203) B6411203
theorem B2849423 : Blo 1899435 2849423 := bstep (se 1 (by rfl) ⟨2137067, by rfl⟩ : syracuseStep 2849423 = 4274135) B4274135
theorem B1899615 : Blo 1899435 1899615 := bstep (se 1 (by rfl) ⟨1424711, by rfl⟩ : syracuseStep 1899615 = 2849423) B2849423
theorem B2849429 : Blo 1899435 2849429 := bbase (se 6 (by rfl) ⟨66783, by rfl⟩ : syracuseStep 2849429 = 133567) (by norm_num)
theorem B1899619 : Blo 1899435 1899619 := bstep (se 1 (by rfl) ⟨1424714, by rfl⟩ : syracuseStep 1899619 = 2849429) B2849429
theorem B4332469 : Blo 1899435 4332469 := bbase (se 5 (by rfl) ⟨203084, by rfl⟩ : syracuseStep 4332469 = 406169) (by norm_num)
theorem B5776625 : Blo 1899435 5776625 := bstep (se 2 (by rfl) ⟨2166234, by rfl⟩ : syracuseStep 5776625 = 4332469) B4332469
theorem B3851083 : Blo 1899435 3851083 := bstep (se 1 (by rfl) ⟨2888312, by rfl⟩ : syracuseStep 3851083 = 5776625) B5776625
theorem B20539109 : Blo 1899435 20539109 := bstep (se 4 (by rfl) ⟨1925541, by rfl⟩ : syracuseStep 20539109 = 3851083) B3851083
theorem B13692739 : Blo 1899435 13692739 := bstep (se 1 (by rfl) ⟨10269554, by rfl⟩ : syracuseStep 13692739 = 20539109) B20539109
theorem B18256985 : Blo 1899435 18256985 := bstep (se 2 (by rfl) ⟨6846369, by rfl⟩ : syracuseStep 18256985 = 13692739) B13692739
theorem B12171323 : Blo 1899435 12171323 := bstep (se 1 (by rfl) ⟨9128492, by rfl⟩ : syracuseStep 12171323 = 18256985) B18256985
theorem B8114215 : Blo 1899435 8114215 := bstep (se 1 (by rfl) ⟨6085661, by rfl⟩ : syracuseStep 8114215 = 12171323) B12171323
theorem B10818953 : Blo 1899435 10818953 := bstep (se 2 (by rfl) ⟨4057107, by rfl⟩ : syracuseStep 10818953 = 8114215) B8114215
theorem B7212635 : Blo 1899435 7212635 := bstep (se 1 (by rfl) ⟨5409476, by rfl⟩ : syracuseStep 7212635 = 10818953) B10818953
theorem B4808423 : Blo 1899435 4808423 := bstep (se 1 (by rfl) ⟨3606317, by rfl⟩ : syracuseStep 4808423 = 7212635) B7212635
theorem B3205615 : Blo 1899435 3205615 := bstep (se 1 (by rfl) ⟨2404211, by rfl⟩ : syracuseStep 3205615 = 4808423) B4808423
theorem B4274153 : Blo 1899435 4274153 := bstep (se 2 (by rfl) ⟨1602807, by rfl⟩ : syracuseStep 4274153 = 3205615) B3205615
theorem B2849435 : Blo 1899435 2849435 := bstep (se 1 (by rfl) ⟨2137076, by rfl⟩ : syracuseStep 2849435 = 4274153) B4274153
theorem B1899623 : Blo 1899435 1899623 := bstep (se 1 (by rfl) ⟨1424717, by rfl⟩ : syracuseStep 1899623 = 2849435) B2849435
theorem B2137081 : Blo 1899435 2137081 := bbase (se 2 (by rfl) ⟨801405, by rfl⟩ : syracuseStep 2137081 = 1602811) (by norm_num)
theorem B2849441 : Blo 1899435 2849441 := bstep (se 2 (by rfl) ⟨1068540, by rfl⟩ : syracuseStep 2849441 = 2137081) B2137081
theorem B1899627 : Blo 1899435 1899627 := bstep (se 1 (by rfl) ⟨1424720, by rfl⟩ : syracuseStep 1899627 = 2849441) B2849441
theorem B4168589 : Blo 1899435 4168589 := bbase (se 3 (by rfl) ⟨781610, by rfl⟩ : syracuseStep 4168589 = 1563221) (by norm_num)
theorem B11116237 : Blo 1899435 11116237 := bstep (se 3 (by rfl) ⟨2084294, by rfl⟩ : syracuseStep 11116237 = 4168589) B4168589
theorem B14821649 : Blo 1899435 14821649 := bstep (se 2 (by rfl) ⟨5558118, by rfl⟩ : syracuseStep 14821649 = 11116237) B11116237
theorem B9881099 : Blo 1899435 9881099 := bstep (se 1 (by rfl) ⟨7410824, by rfl⟩ : syracuseStep 9881099 = 14821649) B14821649
theorem B6587399 : Blo 1899435 6587399 := bstep (se 1 (by rfl) ⟨4940549, by rfl⟩ : syracuseStep 6587399 = 9881099) B9881099
theorem B4391599 : Blo 1899435 4391599 := bstep (se 1 (by rfl) ⟨3293699, by rfl⟩ : syracuseStep 4391599 = 6587399) B6587399
theorem B5855465 : Blo 1899435 5855465 := bstep (se 2 (by rfl) ⟨2195799, by rfl⟩ : syracuseStep 5855465 = 4391599) B4391599
theorem B3903643 : Blo 1899435 3903643 := bstep (se 1 (by rfl) ⟨2927732, by rfl⟩ : syracuseStep 3903643 = 5855465) B5855465
theorem B20819429 : Blo 1899435 20819429 := bstep (se 4 (by rfl) ⟨1951821, by rfl⟩ : syracuseStep 20819429 = 3903643) B3903643
theorem B13879619 : Blo 1899435 13879619 := bstep (se 1 (by rfl) ⟨10409714, by rfl⟩ : syracuseStep 13879619 = 20819429) B20819429
theorem B9253079 : Blo 1899435 9253079 := bstep (se 1 (by rfl) ⟨6939809, by rfl⟩ : syracuseStep 9253079 = 13879619) B13879619
theorem B6168719 : Blo 1899435 6168719 := bstep (se 1 (by rfl) ⟨4626539, by rfl⟩ : syracuseStep 6168719 = 9253079) B9253079
theorem B4112479 : Blo 1899435 4112479 := bstep (se 1 (by rfl) ⟨3084359, by rfl⟩ : syracuseStep 4112479 = 6168719) B6168719
theorem B5483305 : Blo 1899435 5483305 := bstep (se 2 (by rfl) ⟨2056239, by rfl⟩ : syracuseStep 5483305 = 4112479) B4112479
theorem B7311073 : Blo 1899435 7311073 := bstep (se 2 (by rfl) ⟨2741652, by rfl⟩ : syracuseStep 7311073 = 5483305) B5483305
theorem B9748097 : Blo 1899435 9748097 := bstep (se 2 (by rfl) ⟨3655536, by rfl⟩ : syracuseStep 9748097 = 7311073) B7311073
theorem B6498731 : Blo 1899435 6498731 := bstep (se 1 (by rfl) ⟨4874048, by rfl⟩ : syracuseStep 6498731 = 9748097) B9748097
theorem B17329949 : Blo 1899435 17329949 := bstep (se 3 (by rfl) ⟨3249365, by rfl⟩ : syracuseStep 17329949 = 6498731) B6498731
theorem B11553299 : Blo 1899435 11553299 := bstep (se 1 (by rfl) ⟨8664974, by rfl⟩ : syracuseStep 11553299 = 17329949) B17329949
theorem B7702199 : Blo 1899435 7702199 := bstep (se 1 (by rfl) ⟨5776649, by rfl⟩ : syracuseStep 7702199 = 11553299) B11553299
theorem B5134799 : Blo 1899435 5134799 := bstep (se 1 (by rfl) ⟨3851099, by rfl⟩ : syracuseStep 5134799 = 7702199) B7702199
theorem B13692797 : Blo 1899435 13692797 := bstep (se 3 (by rfl) ⟨2567399, by rfl⟩ : syracuseStep 13692797 = 5134799) B5134799
theorem B9128531 : Blo 1899435 9128531 := bstep (se 1 (by rfl) ⟨6846398, by rfl⟩ : syracuseStep 9128531 = 13692797) B13692797
theorem B6085687 : Blo 1899435 6085687 := bstep (se 1 (by rfl) ⟨4564265, by rfl⟩ : syracuseStep 6085687 = 9128531) B9128531
theorem B8114249 : Blo 1899435 8114249 := bstep (se 2 (by rfl) ⟨3042843, by rfl⟩ : syracuseStep 8114249 = 6085687) B6085687
theorem B5409499 : Blo 1899435 5409499 := bstep (se 1 (by rfl) ⟨4057124, by rfl⟩ : syracuseStep 5409499 = 8114249) B8114249
theorem B7212665 : Blo 1899435 7212665 := bstep (se 2 (by rfl) ⟨2704749, by rfl⟩ : syracuseStep 7212665 = 5409499) B5409499
theorem B4808443 : Blo 1899435 4808443 := bstep (se 1 (by rfl) ⟨3606332, by rfl⟩ : syracuseStep 4808443 = 7212665) B7212665
theorem B6411257 : Blo 1899435 6411257 := bstep (se 2 (by rfl) ⟨2404221, by rfl⟩ : syracuseStep 6411257 = 4808443) B4808443
theorem B4274171 : Blo 1899435 4274171 := bstep (se 1 (by rfl) ⟨3205628, by rfl⟩ : syracuseStep 4274171 = 6411257) B6411257
theorem B2849447 : Blo 1899435 2849447 := bstep (se 1 (by rfl) ⟨2137085, by rfl⟩ : syracuseStep 2849447 = 4274171) B4274171
theorem B1899631 : Blo 1899435 1899631 := bstep (se 1 (by rfl) ⟨1424723, by rfl⟩ : syracuseStep 1899631 = 2849447) B2849447
theorem B2849453 : Blo 1899435 2849453 := bbase (se 3 (by rfl) ⟨534272, by rfl⟩ : syracuseStep 2849453 = 1068545) (by norm_num)
theorem B1899635 : Blo 1899435 1899635 := bstep (se 1 (by rfl) ⟨1424726, by rfl⟩ : syracuseStep 1899635 = 2849453) B2849453
theorem B4274189 : Blo 1899435 4274189 := bbase (se 3 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 4274189 = 1602821) (by norm_num)
theorem B2849459 : Blo 1899435 2849459 := bstep (se 1 (by rfl) ⟨2137094, by rfl⟩ : syracuseStep 2849459 = 4274189) B4274189
theorem B1899639 : Blo 1899435 1899639 := bstep (se 1 (by rfl) ⟨1424729, by rfl⟩ : syracuseStep 1899639 = 2849459) B2849459
theorem B2404237 : Blo 1899435 2404237 := bbase (se 3 (by rfl) ⟨450794, by rfl⟩ : syracuseStep 2404237 = 901589) (by norm_num)
theorem B3205649 : Blo 1899435 3205649 := bstep (se 2 (by rfl) ⟨1202118, by rfl⟩ : syracuseStep 3205649 = 2404237) B2404237
theorem B2137099 : Blo 1899435 2137099 := bstep (se 1 (by rfl) ⟨1602824, by rfl⟩ : syracuseStep 2137099 = 3205649) B3205649
theorem B2849465 : Blo 1899435 2849465 := bstep (se 2 (by rfl) ⟨1068549, by rfl⟩ : syracuseStep 2849465 = 2137099) B2137099
theorem B1899643 : Blo 1899435 1899643 := bstep (se 1 (by rfl) ⟨1424732, by rfl⟩ : syracuseStep 1899643 = 2849465) B2849465
theorem B2313289 : Blo 1899435 2313289 := bbase (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) (by norm_num)
theorem B12337541 : Blo 1899435 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B8225027 : Blo 1899435 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B5483351 : Blo 1899435 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B3655567 : Blo 1899435 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B4874089 : Blo 1899435 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B6498785 : Blo 1899435 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B4332523 : Blo 1899435 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B5776697 : Blo 1899435 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B15404525 : Blo 1899435 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B10269683 : Blo 1899435 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B6846455 : Blo 1899435 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B18257213 : Blo 1899435 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B12171475 : Blo 1899435 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B16228633 : Blo 1899435 16228633 := bstep (se 2 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 16228633 = 12171475) B12171475
theorem B21638177 : Blo 1899435 21638177 := bstep (se 2 (by rfl) ⟨8114316, by rfl⟩ : syracuseStep 21638177 = 16228633) B16228633
theorem B14425451 : Blo 1899435 14425451 := bstep (se 1 (by rfl) ⟨10819088, by rfl⟩ : syracuseStep 14425451 = 21638177) B21638177
theorem B9616967 : Blo 1899435 9616967 := bstep (se 1 (by rfl) ⟨7212725, by rfl⟩ : syracuseStep 9616967 = 14425451) B14425451
theorem B6411311 : Blo 1899435 6411311 := bstep (se 1 (by rfl) ⟨4808483, by rfl⟩ : syracuseStep 6411311 = 9616967) B9616967
theorem B4274207 : Blo 1899435 4274207 := bstep (se 1 (by rfl) ⟨3205655, by rfl⟩ : syracuseStep 4274207 = 6411311) B6411311
theorem B2849471 : Blo 1899435 2849471 := bstep (se 1 (by rfl) ⟨2137103, by rfl⟩ : syracuseStep 2849471 = 4274207) B4274207
theorem B1899647 : Blo 1899435 1899647 := bstep (se 1 (by rfl) ⟨1424735, by rfl⟩ : syracuseStep 1899647 = 2849471) B2849471
theorem B2849477 : Blo 1899435 2849477 := bbase (se 4 (by rfl) ⟨267138, by rfl⟩ : syracuseStep 2849477 = 534277) (by norm_num)
theorem B1899651 : Blo 1899435 1899651 := bstep (se 1 (by rfl) ⟨1424738, by rfl⟩ : syracuseStep 1899651 = 2849477) B2849477
theorem B3205669 : Blo 1899435 3205669 := bbase (se 4 (by rfl) ⟨300531, by rfl⟩ : syracuseStep 3205669 = 601063) (by norm_num)
theorem B4274225 : Blo 1899435 4274225 := bstep (se 2 (by rfl) ⟨1602834, by rfl⟩ : syracuseStep 4274225 = 3205669) B3205669
theorem B2849483 : Blo 1899435 2849483 := bstep (se 1 (by rfl) ⟨2137112, by rfl⟩ : syracuseStep 2849483 = 4274225) B4274225
theorem B1899655 : Blo 1899435 1899655 := bstep (se 1 (by rfl) ⟨1424741, by rfl⟩ : syracuseStep 1899655 = 2849483) B2849483
theorem B2137117 : Blo 1899435 2137117 := bbase (se 3 (by rfl) ⟨400709, by rfl⟩ : syracuseStep 2137117 = 801419) (by norm_num)
theorem B2849489 : Blo 1899435 2849489 := bstep (se 2 (by rfl) ⟨1068558, by rfl⟩ : syracuseStep 2849489 = 2137117) B2137117
theorem B1899659 : Blo 1899435 1899659 := bstep (se 1 (by rfl) ⟨1424744, by rfl⟩ : syracuseStep 1899659 = 2849489) B2849489
theorem B6411365 : Blo 1899435 6411365 := bbase (se 4 (by rfl) ⟨601065, by rfl⟩ : syracuseStep 6411365 = 1202131) (by norm_num)
theorem B4274243 : Blo 1899435 4274243 := bstep (se 1 (by rfl) ⟨3205682, by rfl⟩ : syracuseStep 4274243 = 6411365) B6411365
theorem B2849495 : Blo 1899435 2849495 := bstep (se 1 (by rfl) ⟨2137121, by rfl⟩ : syracuseStep 2849495 = 4274243) B4274243
theorem B1899663 : Blo 1899435 1899663 := bstep (se 1 (by rfl) ⟨1424747, by rfl⟩ : syracuseStep 1899663 = 2849495) B2849495
theorem B2849501 : Blo 1899435 2849501 := bbase (se 3 (by rfl) ⟨534281, by rfl⟩ : syracuseStep 2849501 = 1068563) (by norm_num)
theorem B1899667 : Blo 1899435 1899667 := bstep (se 1 (by rfl) ⟨1424750, by rfl⟩ : syracuseStep 1899667 = 2849501) B2849501
theorem B4274261 : Blo 1899435 4274261 := bbase (se 8 (by rfl) ⟨25044, by rfl⟩ : syracuseStep 4274261 = 50089) (by norm_num)
theorem B2849507 : Blo 1899435 2849507 := bstep (se 1 (by rfl) ⟨2137130, by rfl⟩ : syracuseStep 2849507 = 4274261) B4274261
theorem B1899671 : Blo 1899435 1899671 := bstep (se 1 (by rfl) ⟨1424753, by rfl⟩ : syracuseStep 1899671 = 2849507) B2849507
theorem B6085829 : Blo 1899435 6085829 := bbase (se 4 (by rfl) ⟨570546, by rfl⟩ : syracuseStep 6085829 = 1141093) (by norm_num)
theorem B4057219 : Blo 1899435 4057219 := bstep (se 1 (by rfl) ⟨3042914, by rfl⟩ : syracuseStep 4057219 = 6085829) B6085829
theorem B5409625 : Blo 1899435 5409625 := bstep (se 2 (by rfl) ⟨2028609, by rfl⟩ : syracuseStep 5409625 = 4057219) B4057219
theorem B7212833 : Blo 1899435 7212833 := bstep (se 2 (by rfl) ⟨2704812, by rfl⟩ : syracuseStep 7212833 = 5409625) B5409625
theorem B4808555 : Blo 1899435 4808555 := bstep (se 1 (by rfl) ⟨3606416, by rfl⟩ : syracuseStep 4808555 = 7212833) B7212833
theorem B3205703 : Blo 1899435 3205703 := bstep (se 1 (by rfl) ⟨2404277, by rfl⟩ : syracuseStep 3205703 = 4808555) B4808555
theorem B2137135 : Blo 1899435 2137135 := bstep (se 1 (by rfl) ⟨1602851, by rfl⟩ : syracuseStep 2137135 = 3205703) B3205703
theorem B2849513 : Blo 1899435 2849513 := bstep (se 2 (by rfl) ⟨1068567, by rfl⟩ : syracuseStep 2849513 = 2137135) B2137135
theorem B1899675 : Blo 1899435 1899675 := bstep (se 1 (by rfl) ⟨1424756, by rfl⟩ : syracuseStep 1899675 = 2849513) B2849513
theorem B13693141 : Blo 1899435 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B18257521 : Blo 1899435 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B24343361 : Blo 1899435 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B16228907 : Blo 1899435 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B10819271 : Blo 1899435 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B7212847 : Blo 1899435 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B9617129 : Blo 1899435 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B6411419 : Blo 1899435 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B4274279 : Blo 1899435 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B2849519 : Blo 1899435 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B1899679 : Blo 1899435 1899679 := bstep (se 1 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 1899679 = 2849519) B2849519
theorem B2849525 : Blo 1899435 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B1899683 : Blo 1899435 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B6168901 : Blo 1899435 6168901 := bbase (se 4 (by rfl) ⟨578334, by rfl⟩ : syracuseStep 6168901 = 1156669) (by norm_num)
theorem B8225201 : Blo 1899435 8225201 := bstep (se 2 (by rfl) ⟨3084450, by rfl⟩ : syracuseStep 8225201 = 6168901) B6168901
theorem B5483467 : Blo 1899435 5483467 := bstep (se 1 (by rfl) ⟨4112600, by rfl⟩ : syracuseStep 5483467 = 8225201) B8225201
theorem B29245157 : Blo 1899435 29245157 := bstep (se 4 (by rfl) ⟨2741733, by rfl⟩ : syracuseStep 29245157 = 5483467) B5483467
theorem B19496771 : Blo 1899435 19496771 := bstep (se 1 (by rfl) ⟨14622578, by rfl⟩ : syracuseStep 19496771 = 29245157) B29245157
theorem B12997847 : Blo 1899435 12997847 := bstep (se 1 (by rfl) ⟨9748385, by rfl⟩ : syracuseStep 12997847 = 19496771) B19496771
theorem B8665231 : Blo 1899435 8665231 := bstep (se 1 (by rfl) ⟨6498923, by rfl⟩ : syracuseStep 8665231 = 12997847) B12997847
theorem B11553641 : Blo 1899435 11553641 := bstep (se 2 (by rfl) ⟨4332615, by rfl⟩ : syracuseStep 11553641 = 8665231) B8665231
theorem B7702427 : Blo 1899435 7702427 := bstep (se 1 (by rfl) ⟨5776820, by rfl⟩ : syracuseStep 7702427 = 11553641) B11553641
theorem B5134951 : Blo 1899435 5134951 := bstep (se 1 (by rfl) ⟨3851213, by rfl⟩ : syracuseStep 5134951 = 7702427) B7702427
theorem B6846601 : Blo 1899435 6846601 := bstep (se 2 (by rfl) ⟨2567475, by rfl⟩ : syracuseStep 6846601 = 5134951) B5134951
theorem B9128801 : Blo 1899435 9128801 := bstep (se 2 (by rfl) ⟨3423300, by rfl⟩ : syracuseStep 9128801 = 6846601) B6846601
theorem B6085867 : Blo 1899435 6085867 := bstep (se 1 (by rfl) ⟨4564400, by rfl⟩ : syracuseStep 6085867 = 9128801) B9128801
theorem B8114489 : Blo 1899435 8114489 := bstep (se 2 (by rfl) ⟨3042933, by rfl⟩ : syracuseStep 8114489 = 6085867) B6085867
theorem B5409659 : Blo 1899435 5409659 := bstep (se 1 (by rfl) ⟨4057244, by rfl⟩ : syracuseStep 5409659 = 8114489) B8114489
theorem B3606439 : Blo 1899435 3606439 := bstep (se 1 (by rfl) ⟨2704829, by rfl⟩ : syracuseStep 3606439 = 5409659) B5409659
theorem B4808585 : Blo 1899435 4808585 := bstep (se 2 (by rfl) ⟨1803219, by rfl⟩ : syracuseStep 4808585 = 3606439) B3606439
theorem B3205723 : Blo 1899435 3205723 := bstep (se 1 (by rfl) ⟨2404292, by rfl⟩ : syracuseStep 3205723 = 4808585) B4808585
theorem B4274297 : Blo 1899435 4274297 := bstep (se 2 (by rfl) ⟨1602861, by rfl⟩ : syracuseStep 4274297 = 3205723) B3205723
theorem B2849531 : Blo 1899435 2849531 := bstep (se 1 (by rfl) ⟨2137148, by rfl⟩ : syracuseStep 2849531 = 4274297) B4274297
theorem B1899687 : Blo 1899435 1899687 := bstep (se 1 (by rfl) ⟨1424765, by rfl⟩ : syracuseStep 1899687 = 2849531) B2849531
theorem B2137153 : Blo 1899435 2137153 := bbase (se 2 (by rfl) ⟨801432, by rfl⟩ : syracuseStep 2137153 = 1602865) (by norm_num)
theorem B2849537 : Blo 1899435 2849537 := bstep (se 2 (by rfl) ⟨1068576, by rfl⟩ : syracuseStep 2849537 = 2137153) B2137153
theorem B1899691 : Blo 1899435 1899691 := bstep (se 1 (by rfl) ⟨1424768, by rfl⟩ : syracuseStep 1899691 = 2849537) B2849537
theorem B4808605 : Blo 1899435 4808605 := bbase (se 3 (by rfl) ⟨901613, by rfl⟩ : syracuseStep 4808605 = 1803227) (by norm_num)
theorem B6411473 : Blo 1899435 6411473 := bstep (se 2 (by rfl) ⟨2404302, by rfl⟩ : syracuseStep 6411473 = 4808605) B4808605
theorem B4274315 : Blo 1899435 4274315 := bstep (se 1 (by rfl) ⟨3205736, by rfl⟩ : syracuseStep 4274315 = 6411473) B6411473
theorem B2849543 : Blo 1899435 2849543 := bstep (se 1 (by rfl) ⟨2137157, by rfl⟩ : syracuseStep 2849543 = 4274315) B4274315
theorem B1899695 : Blo 1899435 1899695 := bstep (se 1 (by rfl) ⟨1424771, by rfl⟩ : syracuseStep 1899695 = 2849543) B2849543
theorem B2849549 : Blo 1899435 2849549 := bbase (se 3 (by rfl) ⟨534290, by rfl⟩ : syracuseStep 2849549 = 1068581) (by norm_num)
theorem B1899699 : Blo 1899435 1899699 := bstep (se 1 (by rfl) ⟨1424774, by rfl⟩ : syracuseStep 1899699 = 2849549) B2849549
theorem B4274333 : Blo 1899435 4274333 := bbase (se 3 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 4274333 = 1602875) (by norm_num)
theorem B2849555 : Blo 1899435 2849555 := bstep (se 1 (by rfl) ⟨2137166, by rfl⟩ : syracuseStep 2849555 = 4274333) B4274333
theorem B1899703 : Blo 1899435 1899703 := bstep (se 1 (by rfl) ⟨1424777, by rfl⟩ : syracuseStep 1899703 = 2849555) B2849555
theorem B3205757 : Blo 1899435 3205757 := bbase (se 3 (by rfl) ⟨601079, by rfl⟩ : syracuseStep 3205757 = 1202159) (by norm_num)
theorem B2137171 : Blo 1899435 2137171 := bstep (se 1 (by rfl) ⟨1602878, by rfl⟩ : syracuseStep 2137171 = 3205757) B3205757
theorem B2849561 : Blo 1899435 2849561 := bstep (se 2 (by rfl) ⟨1068585, by rfl⟩ : syracuseStep 2849561 = 2137171) B2137171
theorem B1899707 : Blo 1899435 1899707 := bstep (se 1 (by rfl) ⟨1424780, by rfl⟩ : syracuseStep 1899707 = 2849561) B2849561
theorem B7034789 : Blo 1899435 7034789 := bbase (se 4 (by rfl) ⟨659511, by rfl⟩ : syracuseStep 7034789 = 1319023) (by norm_num)
theorem B4689859 : Blo 1899435 4689859 := bstep (se 1 (by rfl) ⟨3517394, by rfl⟩ : syracuseStep 4689859 = 7034789) B7034789
theorem B6253145 : Blo 1899435 6253145 := bstep (se 2 (by rfl) ⟨2344929, by rfl⟩ : syracuseStep 6253145 = 4689859) B4689859
theorem B4168763 : Blo 1899435 4168763 := bstep (se 1 (by rfl) ⟨3126572, by rfl⟩ : syracuseStep 4168763 = 6253145) B6253145
theorem B2779175 : Blo 1899435 2779175 := bstep (se 1 (by rfl) ⟨2084381, by rfl⟩ : syracuseStep 2779175 = 4168763) B4168763
theorem B7411133 : Blo 1899435 7411133 := bstep (se 3 (by rfl) ⟨1389587, by rfl⟩ : syracuseStep 7411133 = 2779175) B2779175
theorem B19763021 : Blo 1899435 19763021 := bstep (se 3 (by rfl) ⟨3705566, by rfl⟩ : syracuseStep 19763021 = 7411133) B7411133
theorem B13175347 : Blo 1899435 13175347 := bstep (se 1 (by rfl) ⟨9881510, by rfl⟩ : syracuseStep 13175347 = 19763021) B19763021
theorem B17567129 : Blo 1899435 17567129 := bstep (se 2 (by rfl) ⟨6587673, by rfl⟩ : syracuseStep 17567129 = 13175347) B13175347
theorem B46845677 : Blo 1899435 46845677 := bstep (se 3 (by rfl) ⟨8783564, by rfl⟩ : syracuseStep 46845677 = 17567129) B17567129
theorem B31230451 : Blo 1899435 31230451 := bstep (se 1 (by rfl) ⟨23422838, by rfl⟩ : syracuseStep 31230451 = 46845677) B46845677
theorem B41640601 : Blo 1899435 41640601 := bstep (se 2 (by rfl) ⟨15615225, by rfl⟩ : syracuseStep 41640601 = 31230451) B31230451
theorem B55520801 : Blo 1899435 55520801 := bstep (se 2 (by rfl) ⟨20820300, by rfl⟩ : syracuseStep 55520801 = 41640601) B41640601
theorem B37013867 : Blo 1899435 37013867 := bstep (se 1 (by rfl) ⟨27760400, by rfl⟩ : syracuseStep 37013867 = 55520801) B55520801
theorem B24675911 : Blo 1899435 24675911 := bstep (se 1 (by rfl) ⟨18506933, by rfl⟩ : syracuseStep 24675911 = 37013867) B37013867
theorem B16450607 : Blo 1899435 16450607 := bstep (se 1 (by rfl) ⟨12337955, by rfl⟩ : syracuseStep 16450607 = 24675911) B24675911
theorem B10967071 : Blo 1899435 10967071 := bstep (se 1 (by rfl) ⟨8225303, by rfl⟩ : syracuseStep 10967071 = 16450607) B16450607
theorem B14622761 : Blo 1899435 14622761 := bstep (se 2 (by rfl) ⟨5483535, by rfl⟩ : syracuseStep 14622761 = 10967071) B10967071
theorem B9748507 : Blo 1899435 9748507 := bstep (se 1 (by rfl) ⟨7311380, by rfl⟩ : syracuseStep 9748507 = 14622761) B14622761
theorem B12998009 : Blo 1899435 12998009 := bstep (se 2 (by rfl) ⟨4874253, by rfl⟩ : syracuseStep 12998009 = 9748507) B9748507
theorem B8665339 : Blo 1899435 8665339 := bstep (se 1 (by rfl) ⟨6499004, by rfl⟩ : syracuseStep 8665339 = 12998009) B12998009
theorem B11553785 : Blo 1899435 11553785 := bstep (se 2 (by rfl) ⟨4332669, by rfl⟩ : syracuseStep 11553785 = 8665339) B8665339
theorem B7702523 : Blo 1899435 7702523 := bstep (se 1 (by rfl) ⟨5776892, by rfl⟩ : syracuseStep 7702523 = 11553785) B11553785
theorem B5135015 : Blo 1899435 5135015 := bstep (se 1 (by rfl) ⟨3851261, by rfl⟩ : syracuseStep 5135015 = 7702523) B7702523
theorem B13693373 : Blo 1899435 13693373 := bstep (se 3 (by rfl) ⟨2567507, by rfl⟩ : syracuseStep 13693373 = 5135015) B5135015
theorem B9128915 : Blo 1899435 9128915 := bstep (se 1 (by rfl) ⟨6846686, by rfl⟩ : syracuseStep 9128915 = 13693373) B13693373
theorem B6085943 : Blo 1899435 6085943 := bstep (se 1 (by rfl) ⟨4564457, by rfl⟩ : syracuseStep 6085943 = 9128915) B9128915
theorem B4057295 : Blo 1899435 4057295 := bstep (se 1 (by rfl) ⟨3042971, by rfl⟩ : syracuseStep 4057295 = 6085943) B6085943
theorem B10819453 : Blo 1899435 10819453 := bstep (se 3 (by rfl) ⟨2028647, by rfl⟩ : syracuseStep 10819453 = 4057295) B4057295
theorem B14425937 : Blo 1899435 14425937 := bstep (se 2 (by rfl) ⟨5409726, by rfl⟩ : syracuseStep 14425937 = 10819453) B10819453
theorem B9617291 : Blo 1899435 9617291 := bstep (se 1 (by rfl) ⟨7212968, by rfl⟩ : syracuseStep 9617291 = 14425937) B14425937
theorem B6411527 : Blo 1899435 6411527 := bstep (se 1 (by rfl) ⟨4808645, by rfl⟩ : syracuseStep 6411527 = 9617291) B9617291
theorem B4274351 : Blo 1899435 4274351 := bstep (se 1 (by rfl) ⟨3205763, by rfl⟩ : syracuseStep 4274351 = 6411527) B6411527
theorem B2849567 : Blo 1899435 2849567 := bstep (se 1 (by rfl) ⟨2137175, by rfl⟩ : syracuseStep 2849567 = 4274351) B4274351
theorem B1899711 : Blo 1899435 1899711 := bstep (se 1 (by rfl) ⟨1424783, by rfl⟩ : syracuseStep 1899711 = 2849567) B2849567
theorem B2849573 : Blo 1899435 2849573 := bbase (se 4 (by rfl) ⟨267147, by rfl⟩ : syracuseStep 2849573 = 534295) (by norm_num)
theorem B1899715 : Blo 1899435 1899715 := bstep (se 1 (by rfl) ⟨1424786, by rfl⟩ : syracuseStep 1899715 = 2849573) B2849573
theorem B2404333 : Blo 1899435 2404333 := bbase (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) (by norm_num)
theorem B3205777 : Blo 1899435 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B4274369 : Blo 1899435 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B2849579 : Blo 1899435 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B1899719 : Blo 1899435 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B2137189 : Blo 1899435 2137189 := bbase (se 4 (by rfl) ⟨200361, by rfl⟩ : syracuseStep 2137189 = 400723) (by norm_num)
theorem B2849585 : Blo 1899435 2849585 := bstep (se 2 (by rfl) ⟨1068594, by rfl⟩ : syracuseStep 2849585 = 2137189) B2137189
theorem B1899723 : Blo 1899435 1899723 := bstep (se 1 (by rfl) ⟨1424792, by rfl⟩ : syracuseStep 1899723 = 2849585) B2849585
theorem B2028665 : Blo 1899435 2028665 := bbase (se 2 (by rfl) ⟨760749, by rfl⟩ : syracuseStep 2028665 = 1521499) (by norm_num)
theorem B5409773 : Blo 1899435 5409773 := bstep (se 3 (by rfl) ⟨1014332, by rfl⟩ : syracuseStep 5409773 = 2028665) B2028665
theorem B3606515 : Blo 1899435 3606515 := bstep (se 1 (by rfl) ⟨2704886, by rfl⟩ : syracuseStep 3606515 = 5409773) B5409773
theorem B2404343 : Blo 1899435 2404343 := bstep (se 1 (by rfl) ⟨1803257, by rfl⟩ : syracuseStep 2404343 = 3606515) B3606515
theorem B6411581 : Blo 1899435 6411581 := bstep (se 3 (by rfl) ⟨1202171, by rfl⟩ : syracuseStep 6411581 = 2404343) B2404343
theorem B4274387 : Blo 1899435 4274387 := bstep (se 1 (by rfl) ⟨3205790, by rfl⟩ : syracuseStep 4274387 = 6411581) B6411581
theorem B2849591 : Blo 1899435 2849591 := bstep (se 1 (by rfl) ⟨2137193, by rfl⟩ : syracuseStep 2849591 = 4274387) B4274387
theorem B1899727 : Blo 1899435 1899727 := bstep (se 1 (by rfl) ⟨1424795, by rfl⟩ : syracuseStep 1899727 = 2849591) B2849591
theorem B2849597 : Blo 1899435 2849597 := bbase (se 3 (by rfl) ⟨534299, by rfl⟩ : syracuseStep 2849597 = 1068599) (by norm_num)
theorem B1899731 : Blo 1899435 1899731 := bstep (se 1 (by rfl) ⟨1424798, by rfl⟩ : syracuseStep 1899731 = 2849597) B2849597
theorem B4274405 : Blo 1899435 4274405 := bbase (se 4 (by rfl) ⟨400725, by rfl⟩ : syracuseStep 4274405 = 801451) (by norm_num)
theorem B2849603 : Blo 1899435 2849603 := bstep (se 1 (by rfl) ⟨2137202, by rfl⟩ : syracuseStep 2849603 = 4274405) B4274405
theorem B1899735 : Blo 1899435 1899735 := bstep (se 1 (by rfl) ⟨1424801, by rfl⟩ : syracuseStep 1899735 = 2849603) B2849603
theorem B4808717 : Blo 1899435 4808717 := bbase (se 3 (by rfl) ⟨901634, by rfl⟩ : syracuseStep 4808717 = 1803269) (by norm_num)
theorem B3205811 : Blo 1899435 3205811 := bstep (se 1 (by rfl) ⟨2404358, by rfl⟩ : syracuseStep 3205811 = 4808717) B4808717
theorem B2137207 : Blo 1899435 2137207 := bstep (se 1 (by rfl) ⟨1602905, by rfl⟩ : syracuseStep 2137207 = 3205811) B3205811
theorem B2849609 : Blo 1899435 2849609 := bstep (se 2 (by rfl) ⟨1068603, by rfl⟩ : syracuseStep 2849609 = 2137207) B2137207
theorem B1899739 : Blo 1899435 1899739 := bstep (se 1 (by rfl) ⟨1424804, by rfl⟩ : syracuseStep 1899739 = 2849609) B2849609
theorem B2704909 : Blo 1899435 2704909 := bbase (se 3 (by rfl) ⟨507170, by rfl⟩ : syracuseStep 2704909 = 1014341) (by norm_num)
theorem B3606545 : Blo 1899435 3606545 := bstep (se 2 (by rfl) ⟨1352454, by rfl⟩ : syracuseStep 3606545 = 2704909) B2704909
theorem B9617453 : Blo 1899435 9617453 := bstep (se 3 (by rfl) ⟨1803272, by rfl⟩ : syracuseStep 9617453 = 3606545) B3606545
theorem B6411635 : Blo 1899435 6411635 := bstep (se 1 (by rfl) ⟨4808726, by rfl⟩ : syracuseStep 6411635 = 9617453) B9617453
theorem B4274423 : Blo 1899435 4274423 := bstep (se 1 (by rfl) ⟨3205817, by rfl⟩ : syracuseStep 4274423 = 6411635) B6411635
theorem B2849615 : Blo 1899435 2849615 := bstep (se 1 (by rfl) ⟨2137211, by rfl⟩ : syracuseStep 2849615 = 4274423) B4274423
theorem B1899743 : Blo 1899435 1899743 := bstep (se 1 (by rfl) ⟨1424807, by rfl⟩ : syracuseStep 1899743 = 2849615) B2849615
theorem B2849621 : Blo 1899435 2849621 := bbase (se 9 (by rfl) ⟨8348, by rfl⟩ : syracuseStep 2849621 = 16697) (by norm_num)
theorem B1899747 : Blo 1899435 1899747 := bstep (se 1 (by rfl) ⟨1424810, by rfl⟩ : syracuseStep 1899747 = 2849621) B2849621
theorem B4057381 : Blo 1899435 4057381 := bbase (se 4 (by rfl) ⟨380379, by rfl⟩ : syracuseStep 4057381 = 760759) (by norm_num)
theorem B5409841 : Blo 1899435 5409841 := bstep (se 2 (by rfl) ⟨2028690, by rfl⟩ : syracuseStep 5409841 = 4057381) B4057381
theorem B7213121 : Blo 1899435 7213121 := bstep (se 2 (by rfl) ⟨2704920, by rfl⟩ : syracuseStep 7213121 = 5409841) B5409841
theorem B4808747 : Blo 1899435 4808747 := bstep (se 1 (by rfl) ⟨3606560, by rfl⟩ : syracuseStep 4808747 = 7213121) B7213121
theorem B3205831 : Blo 1899435 3205831 := bstep (se 1 (by rfl) ⟨2404373, by rfl⟩ : syracuseStep 3205831 = 4808747) B4808747
theorem B4274441 : Blo 1899435 4274441 := bstep (se 2 (by rfl) ⟨1602915, by rfl⟩ : syracuseStep 4274441 = 3205831) B3205831
theorem B2849627 : Blo 1899435 2849627 := bstep (se 1 (by rfl) ⟨2137220, by rfl⟩ : syracuseStep 2849627 = 4274441) B4274441
theorem B1899751 : Blo 1899435 1899751 := bstep (se 1 (by rfl) ⟨1424813, by rfl⟩ : syracuseStep 1899751 = 2849627) B2849627
theorem B2137225 : Blo 1899435 2137225 := bbase (se 2 (by rfl) ⟨801459, by rfl⟩ : syracuseStep 2137225 = 1602919) (by norm_num)
theorem B2849633 : Blo 1899435 2849633 := bstep (se 2 (by rfl) ⟨1068612, by rfl⟩ : syracuseStep 2849633 = 2137225) B2137225
theorem B1899755 : Blo 1899435 1899755 := bstep (se 1 (by rfl) ⟨1424816, by rfl⟩ : syracuseStep 1899755 = 2849633) B2849633
theorem B53421781 : Blo 1899435 53421781 := bbase (se 7 (by rfl) ⟨626036, by rfl⟩ : syracuseStep 53421781 = 1252073) (by norm_num)
theorem B71229041 : Blo 1899435 71229041 := bstep (se 2 (by rfl) ⟨26710890, by rfl⟩ : syracuseStep 71229041 = 53421781) B53421781
theorem B47486027 : Blo 1899435 47486027 := bstep (se 1 (by rfl) ⟨35614520, by rfl⟩ : syracuseStep 47486027 = 71229041) B71229041
theorem B126629405 : Blo 1899435 126629405 := bstep (se 3 (by rfl) ⟨23743013, by rfl⟩ : syracuseStep 126629405 = 47486027) B47486027
theorem B84419603 : Blo 1899435 84419603 := bstep (se 1 (by rfl) ⟨63314702, by rfl⟩ : syracuseStep 84419603 = 126629405) B126629405
theorem B56279735 : Blo 1899435 56279735 := bstep (se 1 (by rfl) ⟨42209801, by rfl⟩ : syracuseStep 56279735 = 84419603) B84419603
theorem B37519823 : Blo 1899435 37519823 := bstep (se 1 (by rfl) ⟨28139867, by rfl⟩ : syracuseStep 37519823 = 56279735) B56279735
theorem B25013215 : Blo 1899435 25013215 := bstep (se 1 (by rfl) ⟨18759911, by rfl⟩ : syracuseStep 25013215 = 37519823) B37519823
theorem B33350953 : Blo 1899435 33350953 := bstep (se 2 (by rfl) ⟨12506607, by rfl⟩ : syracuseStep 33350953 = 25013215) B25013215
theorem B44467937 : Blo 1899435 44467937 := bstep (se 2 (by rfl) ⟨16675476, by rfl⟩ : syracuseStep 44467937 = 33350953) B33350953
theorem B29645291 : Blo 1899435 29645291 := bstep (se 1 (by rfl) ⟨22233968, by rfl⟩ : syracuseStep 29645291 = 44467937) B44467937
theorem B19763527 : Blo 1899435 19763527 := bstep (se 1 (by rfl) ⟨14822645, by rfl⟩ : syracuseStep 19763527 = 29645291) B29645291
theorem B26351369 : Blo 1899435 26351369 := bstep (se 2 (by rfl) ⟨9881763, by rfl⟩ : syracuseStep 26351369 = 19763527) B19763527
theorem B17567579 : Blo 1899435 17567579 := bstep (se 1 (by rfl) ⟨13175684, by rfl⟩ : syracuseStep 17567579 = 26351369) B26351369
theorem B11711719 : Blo 1899435 11711719 := bstep (se 1 (by rfl) ⟨8783789, by rfl⟩ : syracuseStep 11711719 = 17567579) B17567579
theorem B15615625 : Blo 1899435 15615625 := bstep (se 2 (by rfl) ⟨5855859, by rfl⟩ : syracuseStep 15615625 = 11711719) B11711719
theorem B20820833 : Blo 1899435 20820833 := bstep (se 2 (by rfl) ⟨7807812, by rfl⟩ : syracuseStep 20820833 = 15615625) B15615625
theorem B13880555 : Blo 1899435 13880555 := bstep (se 1 (by rfl) ⟨10410416, by rfl⟩ : syracuseStep 13880555 = 20820833) B20820833
theorem B9253703 : Blo 1899435 9253703 := bstep (se 1 (by rfl) ⟨6940277, by rfl⟩ : syracuseStep 9253703 = 13880555) B13880555
theorem B6169135 : Blo 1899435 6169135 := bstep (se 1 (by rfl) ⟨4626851, by rfl⟩ : syracuseStep 6169135 = 9253703) B9253703
theorem B8225513 : Blo 1899435 8225513 := bstep (se 2 (by rfl) ⟨3084567, by rfl⟩ : syracuseStep 8225513 = 6169135) B6169135
theorem B5483675 : Blo 1899435 5483675 := bstep (se 1 (by rfl) ⟨4112756, by rfl⟩ : syracuseStep 5483675 = 8225513) B8225513
theorem B3655783 : Blo 1899435 3655783 := bstep (se 1 (by rfl) ⟨2741837, by rfl⟩ : syracuseStep 3655783 = 5483675) B5483675
theorem B4874377 : Blo 1899435 4874377 := bstep (se 2 (by rfl) ⟨1827891, by rfl⟩ : syracuseStep 4874377 = 3655783) B3655783
theorem B6499169 : Blo 1899435 6499169 := bstep (se 2 (by rfl) ⟨2437188, by rfl⟩ : syracuseStep 6499169 = 4874377) B4874377
theorem B4332779 : Blo 1899435 4332779 := bstep (se 1 (by rfl) ⟨3249584, by rfl⟩ : syracuseStep 4332779 = 6499169) B6499169
theorem B2888519 : Blo 1899435 2888519 := bstep (se 1 (by rfl) ⟨2166389, by rfl⟩ : syracuseStep 2888519 = 4332779) B4332779
theorem B7702717 : Blo 1899435 7702717 := bstep (se 3 (by rfl) ⟨1444259, by rfl⟩ : syracuseStep 7702717 = 2888519) B2888519
theorem B10270289 : Blo 1899435 10270289 := bstep (se 2 (by rfl) ⟨3851358, by rfl⟩ : syracuseStep 10270289 = 7702717) B7702717
theorem B6846859 : Blo 1899435 6846859 := bstep (se 1 (by rfl) ⟨5135144, by rfl⟩ : syracuseStep 6846859 = 10270289) B10270289
theorem B36516581 : Blo 1899435 36516581 := bstep (se 4 (by rfl) ⟨3423429, by rfl⟩ : syracuseStep 36516581 = 6846859) B6846859
theorem B24344387 : Blo 1899435 24344387 := bstep (se 1 (by rfl) ⟨18258290, by rfl⟩ : syracuseStep 24344387 = 36516581) B36516581
theorem B16229591 : Blo 1899435 16229591 := bstep (se 1 (by rfl) ⟨12172193, by rfl⟩ : syracuseStep 16229591 = 24344387) B24344387
theorem B10819727 : Blo 1899435 10819727 := bstep (se 1 (by rfl) ⟨8114795, by rfl⟩ : syracuseStep 10819727 = 16229591) B16229591
theorem B7213151 : Blo 1899435 7213151 := bstep (se 1 (by rfl) ⟨5409863, by rfl⟩ : syracuseStep 7213151 = 10819727) B10819727
theorem B4808767 : Blo 1899435 4808767 := bstep (se 1 (by rfl) ⟨3606575, by rfl⟩ : syracuseStep 4808767 = 7213151) B7213151
theorem B6411689 : Blo 1899435 6411689 := bstep (se 2 (by rfl) ⟨2404383, by rfl⟩ : syracuseStep 6411689 = 4808767) B4808767
theorem B4274459 : Blo 1899435 4274459 := bstep (se 1 (by rfl) ⟨3205844, by rfl⟩ : syracuseStep 4274459 = 6411689) B6411689
theorem B2849639 : Blo 1899435 2849639 := bstep (se 1 (by rfl) ⟨2137229, by rfl⟩ : syracuseStep 2849639 = 4274459) B4274459
theorem B1899759 : Blo 1899435 1899759 := bstep (se 1 (by rfl) ⟨1424819, by rfl⟩ : syracuseStep 1899759 = 2849639) B2849639
theorem B2849645 : Blo 1899435 2849645 := bbase (se 3 (by rfl) ⟨534308, by rfl⟩ : syracuseStep 2849645 = 1068617) (by norm_num)
theorem B1899763 : Blo 1899435 1899763 := bstep (se 1 (by rfl) ⟨1424822, by rfl⟩ : syracuseStep 1899763 = 2849645) B2849645
theorem B4274477 : Blo 1899435 4274477 := bbase (se 3 (by rfl) ⟨801464, by rfl⟩ : syracuseStep 4274477 = 1602929) (by norm_num)
theorem B2849651 : Blo 1899435 2849651 := bstep (se 1 (by rfl) ⟨2137238, by rfl⟩ : syracuseStep 2849651 = 4274477) B4274477
theorem B1899767 : Blo 1899435 1899767 := bstep (se 1 (by rfl) ⟨1424825, by rfl⟩ : syracuseStep 1899767 = 2849651) B2849651
theorem B5777077 : Blo 1899435 5777077 := bbase (se 5 (by rfl) ⟨270800, by rfl⟩ : syracuseStep 5777077 = 541601) (by norm_num)
theorem B7702769 : Blo 1899435 7702769 := bstep (se 2 (by rfl) ⟨2888538, by rfl⟩ : syracuseStep 7702769 = 5777077) B5777077
theorem B5135179 : Blo 1899435 5135179 := bstep (se 1 (by rfl) ⟨3851384, by rfl⟩ : syracuseStep 5135179 = 7702769) B7702769
theorem B6846905 : Blo 1899435 6846905 := bstep (se 2 (by rfl) ⟨2567589, by rfl⟩ : syracuseStep 6846905 = 5135179) B5135179
theorem B4564603 : Blo 1899435 4564603 := bstep (se 1 (by rfl) ⟨3423452, by rfl⟩ : syracuseStep 4564603 = 6846905) B6846905
theorem B6086137 : Blo 1899435 6086137 := bstep (se 2 (by rfl) ⟨2282301, by rfl⟩ : syracuseStep 6086137 = 4564603) B4564603
theorem B8114849 : Blo 1899435 8114849 := bstep (se 2 (by rfl) ⟨3043068, by rfl⟩ : syracuseStep 8114849 = 6086137) B6086137
theorem B5409899 : Blo 1899435 5409899 := bstep (se 1 (by rfl) ⟨4057424, by rfl⟩ : syracuseStep 5409899 = 8114849) B8114849
theorem B3606599 : Blo 1899435 3606599 := bstep (se 1 (by rfl) ⟨2704949, by rfl⟩ : syracuseStep 3606599 = 5409899) B5409899
theorem B2404399 : Blo 1899435 2404399 := bstep (se 1 (by rfl) ⟨1803299, by rfl⟩ : syracuseStep 2404399 = 3606599) B3606599
theorem B3205865 : Blo 1899435 3205865 := bstep (se 2 (by rfl) ⟨1202199, by rfl⟩ : syracuseStep 3205865 = 2404399) B2404399
theorem B2137243 : Blo 1899435 2137243 := bstep (se 1 (by rfl) ⟨1602932, by rfl⟩ : syracuseStep 2137243 = 3205865) B3205865
theorem B2849657 : Blo 1899435 2849657 := bstep (se 2 (by rfl) ⟨1068621, by rfl⟩ : syracuseStep 2849657 = 2137243) B2137243
theorem B1899771 : Blo 1899435 1899771 := bstep (se 1 (by rfl) ⟨1424828, by rfl⟩ : syracuseStep 1899771 = 2849657) B2849657
theorem B14623253 : Blo 1899435 14623253 := bbase (se 6 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 14623253 = 685465) (by norm_num)
theorem B9748835 : Blo 1899435 9748835 := bstep (se 1 (by rfl) ⟨7311626, by rfl⟩ : syracuseStep 9748835 = 14623253) B14623253
theorem B6499223 : Blo 1899435 6499223 := bstep (se 1 (by rfl) ⟨4874417, by rfl⟩ : syracuseStep 6499223 = 9748835) B9748835
theorem B4332815 : Blo 1899435 4332815 := bstep (se 1 (by rfl) ⟨3249611, by rfl⟩ : syracuseStep 4332815 = 6499223) B6499223
theorem B2888543 : Blo 1899435 2888543 := bstep (se 1 (by rfl) ⟨2166407, by rfl⟩ : syracuseStep 2888543 = 4332815) B4332815
theorem B7702781 : Blo 1899435 7702781 := bstep (se 3 (by rfl) ⟨1444271, by rfl⟩ : syracuseStep 7702781 = 2888543) B2888543
theorem B20540749 : Blo 1899435 20540749 := bstep (se 3 (by rfl) ⟨3851390, by rfl⟩ : syracuseStep 20540749 = 7702781) B7702781
theorem B27387665 : Blo 1899435 27387665 := bstep (se 2 (by rfl) ⟨10270374, by rfl⟩ : syracuseStep 27387665 = 20540749) B20540749
theorem B18258443 : Blo 1899435 18258443 := bstep (se 1 (by rfl) ⟨13693832, by rfl⟩ : syracuseStep 18258443 = 27387665) B27387665
theorem B12172295 : Blo 1899435 12172295 := bstep (se 1 (by rfl) ⟨9129221, by rfl⟩ : syracuseStep 12172295 = 18258443) B18258443
theorem B32459453 : Blo 1899435 32459453 := bstep (se 3 (by rfl) ⟨6086147, by rfl⟩ : syracuseStep 32459453 = 12172295) B12172295
theorem B21639635 : Blo 1899435 21639635 := bstep (se 1 (by rfl) ⟨16229726, by rfl⟩ : syracuseStep 21639635 = 32459453) B32459453
theorem B14426423 : Blo 1899435 14426423 := bstep (se 1 (by rfl) ⟨10819817, by rfl⟩ : syracuseStep 14426423 = 21639635) B21639635
theorem B9617615 : Blo 1899435 9617615 := bstep (se 1 (by rfl) ⟨7213211, by rfl⟩ : syracuseStep 9617615 = 14426423) B14426423
theorem B6411743 : Blo 1899435 6411743 := bstep (se 1 (by rfl) ⟨4808807, by rfl⟩ : syracuseStep 6411743 = 9617615) B9617615
theorem B4274495 : Blo 1899435 4274495 := bstep (se 1 (by rfl) ⟨3205871, by rfl⟩ : syracuseStep 4274495 = 6411743) B6411743
theorem B2849663 : Blo 1899435 2849663 := bstep (se 1 (by rfl) ⟨2137247, by rfl⟩ : syracuseStep 2849663 = 4274495) B4274495
theorem B1899775 : Blo 1899435 1899775 := bstep (se 1 (by rfl) ⟨1424831, by rfl⟩ : syracuseStep 1899775 = 2849663) B2849663
theorem B2849669 : Blo 1899435 2849669 := bbase (se 4 (by rfl) ⟨267156, by rfl⟩ : syracuseStep 2849669 = 534313) (by norm_num)
theorem B1899779 : Blo 1899435 1899779 := bstep (se 1 (by rfl) ⟨1424834, by rfl⟩ : syracuseStep 1899779 = 2849669) B2849669
theorem B3205885 : Blo 1899435 3205885 := bbase (se 3 (by rfl) ⟨601103, by rfl⟩ : syracuseStep 3205885 = 1202207) (by norm_num)
theorem B4274513 : Blo 1899435 4274513 := bstep (se 2 (by rfl) ⟨1602942, by rfl⟩ : syracuseStep 4274513 = 3205885) B3205885
theorem B2849675 : Blo 1899435 2849675 := bstep (se 1 (by rfl) ⟨2137256, by rfl⟩ : syracuseStep 2849675 = 4274513) B4274513
theorem B1899783 : Blo 1899435 1899783 := bstep (se 1 (by rfl) ⟨1424837, by rfl⟩ : syracuseStep 1899783 = 2849675) B2849675
theorem B2137261 : Blo 1899435 2137261 := bbase (se 3 (by rfl) ⟨400736, by rfl⟩ : syracuseStep 2137261 = 801473) (by norm_num)
theorem B2849681 : Blo 1899435 2849681 := bstep (se 2 (by rfl) ⟨1068630, by rfl⟩ : syracuseStep 2849681 = 2137261) B2137261
theorem B1899787 : Blo 1899435 1899787 := bstep (se 1 (by rfl) ⟨1424840, by rfl⟩ : syracuseStep 1899787 = 2849681) B2849681
theorem B6411797 : Blo 1899435 6411797 := bbase (se 6 (by rfl) ⟨150276, by rfl⟩ : syracuseStep 6411797 = 300553) (by norm_num)
theorem B4274531 : Blo 1899435 4274531 := bstep (se 1 (by rfl) ⟨3205898, by rfl⟩ : syracuseStep 4274531 = 6411797) B6411797
theorem B2849687 : Blo 1899435 2849687 := bstep (se 1 (by rfl) ⟨2137265, by rfl⟩ : syracuseStep 2849687 = 4274531) B4274531
theorem B1899791 : Blo 1899435 1899791 := bstep (se 1 (by rfl) ⟨1424843, by rfl⟩ : syracuseStep 1899791 = 2849687) B2849687
theorem B2849693 : Blo 1899435 2849693 := bbase (se 3 (by rfl) ⟨534317, by rfl⟩ : syracuseStep 2849693 = 1068635) (by norm_num)
theorem B1899795 : Blo 1899435 1899795 := bstep (se 1 (by rfl) ⟨1424846, by rfl⟩ : syracuseStep 1899795 = 2849693) B2849693
theorem B4274549 : Blo 1899435 4274549 := bbase (se 5 (by rfl) ⟨200369, by rfl⟩ : syracuseStep 4274549 = 400739) (by norm_num)
theorem B2849699 : Blo 1899435 2849699 := bstep (se 1 (by rfl) ⟨2137274, by rfl⟩ : syracuseStep 2849699 = 4274549) B4274549
theorem B1899799 : Blo 1899435 1899799 := bstep (se 1 (by rfl) ⟨1424849, by rfl⟩ : syracuseStep 1899799 = 2849699) B2849699
theorem B5777173 : Blo 1899435 5777173 := bbase (se 6 (by rfl) ⟨135402, by rfl⟩ : syracuseStep 5777173 = 270805) (by norm_num)
theorem B7702897 : Blo 1899435 7702897 := bstep (se 2 (by rfl) ⟨2888586, by rfl⟩ : syracuseStep 7702897 = 5777173) B5777173
theorem B10270529 : Blo 1899435 10270529 := bstep (se 2 (by rfl) ⟨3851448, by rfl⟩ : syracuseStep 10270529 = 7702897) B7702897
theorem B6847019 : Blo 1899435 6847019 := bstep (se 1 (by rfl) ⟨5135264, by rfl⟩ : syracuseStep 6847019 = 10270529) B10270529
theorem B4564679 : Blo 1899435 4564679 := bstep (se 1 (by rfl) ⟨3423509, by rfl⟩ : syracuseStep 4564679 = 6847019) B6847019
theorem B12172477 : Blo 1899435 12172477 := bstep (se 3 (by rfl) ⟨2282339, by rfl⟩ : syracuseStep 12172477 = 4564679) B4564679
theorem B16229969 : Blo 1899435 16229969 := bstep (se 2 (by rfl) ⟨6086238, by rfl⟩ : syracuseStep 16229969 = 12172477) B12172477
theorem B10819979 : Blo 1899435 10819979 := bstep (se 1 (by rfl) ⟨8114984, by rfl⟩ : syracuseStep 10819979 = 16229969) B16229969
theorem B7213319 : Blo 1899435 7213319 := bstep (se 1 (by rfl) ⟨5409989, by rfl⟩ : syracuseStep 7213319 = 10819979) B10819979
theorem B4808879 : Blo 1899435 4808879 := bstep (se 1 (by rfl) ⟨3606659, by rfl⟩ : syracuseStep 4808879 = 7213319) B7213319
theorem B3205919 : Blo 1899435 3205919 := bstep (se 1 (by rfl) ⟨2404439, by rfl⟩ : syracuseStep 3205919 = 4808879) B4808879
theorem B2137279 : Blo 1899435 2137279 := bstep (se 1 (by rfl) ⟨1602959, by rfl⟩ : syracuseStep 2137279 = 3205919) B3205919
theorem B2849705 : Blo 1899435 2849705 := bstep (se 2 (by rfl) ⟨1068639, by rfl⟩ : syracuseStep 2849705 = 2137279) B2137279
theorem B1899803 : Blo 1899435 1899803 := bstep (se 1 (by rfl) ⟨1424852, by rfl⟩ : syracuseStep 1899803 = 2849705) B2849705
theorem B7213333 : Blo 1899435 7213333 := bbase (se 6 (by rfl) ⟨169062, by rfl⟩ : syracuseStep 7213333 = 338125) (by norm_num)
theorem B9617777 : Blo 1899435 9617777 := bstep (se 2 (by rfl) ⟨3606666, by rfl⟩ : syracuseStep 9617777 = 7213333) B7213333
theorem B6411851 : Blo 1899435 6411851 := bstep (se 1 (by rfl) ⟨4808888, by rfl⟩ : syracuseStep 6411851 = 9617777) B9617777
theorem B4274567 : Blo 1899435 4274567 := bstep (se 1 (by rfl) ⟨3205925, by rfl⟩ : syracuseStep 4274567 = 6411851) B6411851
theorem B2849711 : Blo 1899435 2849711 := bstep (se 1 (by rfl) ⟨2137283, by rfl⟩ : syracuseStep 2849711 = 4274567) B4274567
theorem B1899807 : Blo 1899435 1899807 := bstep (se 1 (by rfl) ⟨1424855, by rfl⟩ : syracuseStep 1899807 = 2849711) B2849711
theorem B2849717 : Blo 1899435 2849717 := bbase (se 5 (by rfl) ⟨133580, by rfl⟩ : syracuseStep 2849717 = 267161) (by norm_num)
theorem B1899811 : Blo 1899435 1899811 := bstep (se 1 (by rfl) ⟨1424858, by rfl⟩ : syracuseStep 1899811 = 2849717) B2849717
theorem B4808909 : Blo 1899435 4808909 := bbase (se 3 (by rfl) ⟨901670, by rfl⟩ : syracuseStep 4808909 = 1803341) (by norm_num)
theorem B3205939 : Blo 1899435 3205939 := bstep (se 1 (by rfl) ⟨2404454, by rfl⟩ : syracuseStep 3205939 = 4808909) B4808909
theorem B4274585 : Blo 1899435 4274585 := bstep (se 2 (by rfl) ⟨1602969, by rfl⟩ : syracuseStep 4274585 = 3205939) B3205939
theorem B2849723 : Blo 1899435 2849723 := bstep (se 1 (by rfl) ⟨2137292, by rfl⟩ : syracuseStep 2849723 = 4274585) B4274585
theorem B1899815 : Blo 1899435 1899815 := bstep (se 1 (by rfl) ⟨1424861, by rfl⟩ : syracuseStep 1899815 = 2849723) B2849723
theorem B2137297 : Blo 1899435 2137297 := bbase (se 2 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 2137297 = 1602973) (by norm_num)
theorem B2849729 : Blo 1899435 2849729 := bstep (se 2 (by rfl) ⟨1068648, by rfl⟩ : syracuseStep 2849729 = 2137297) B2137297
theorem B1899819 : Blo 1899435 1899819 := bstep (se 1 (by rfl) ⟨1424864, by rfl⟩ : syracuseStep 1899819 = 2849729) B2849729
theorem B8784085 : Blo 1899435 8784085 := bbase (se 7 (by rfl) ⟨102938, by rfl⟩ : syracuseStep 8784085 = 205877) (by norm_num)
theorem B11712113 : Blo 1899435 11712113 := bstep (se 2 (by rfl) ⟨4392042, by rfl⟩ : syracuseStep 11712113 = 8784085) B8784085
theorem B7808075 : Blo 1899435 7808075 := bstep (se 1 (by rfl) ⟨5856056, by rfl⟩ : syracuseStep 7808075 = 11712113) B11712113
theorem B5205383 : Blo 1899435 5205383 := bstep (se 1 (by rfl) ⟨3904037, by rfl⟩ : syracuseStep 5205383 = 7808075) B7808075
theorem B3470255 : Blo 1899435 3470255 := bstep (se 1 (by rfl) ⟨2602691, by rfl⟩ : syracuseStep 3470255 = 5205383) B5205383
theorem B2313503 : Blo 1899435 2313503 := bstep (se 1 (by rfl) ⟨1735127, by rfl⟩ : syracuseStep 2313503 = 3470255) B3470255
theorem B98709461 : Blo 1899435 98709461 := bstep (se 7 (by rfl) ⟨1156751, by rfl⟩ : syracuseStep 98709461 = 2313503) B2313503
theorem B65806307 : Blo 1899435 65806307 := bstep (se 1 (by rfl) ⟨49354730, by rfl⟩ : syracuseStep 65806307 = 98709461) B98709461
theorem B43870871 : Blo 1899435 43870871 := bstep (se 1 (by rfl) ⟨32903153, by rfl⟩ : syracuseStep 43870871 = 65806307) B65806307
theorem B29247247 : Blo 1899435 29247247 := bstep (se 1 (by rfl) ⟨21935435, by rfl⟩ : syracuseStep 29247247 = 43870871) B43870871
theorem B38996329 : Blo 1899435 38996329 := bstep (se 2 (by rfl) ⟨14623623, by rfl⟩ : syracuseStep 38996329 = 29247247) B29247247
theorem B51995105 : Blo 1899435 51995105 := bstep (se 2 (by rfl) ⟨19498164, by rfl⟩ : syracuseStep 51995105 = 38996329) B38996329
theorem B34663403 : Blo 1899435 34663403 := bstep (se 1 (by rfl) ⟨25997552, by rfl⟩ : syracuseStep 34663403 = 51995105) B51995105
theorem B23108935 : Blo 1899435 23108935 := bstep (se 1 (by rfl) ⟨17331701, by rfl⟩ : syracuseStep 23108935 = 34663403) B34663403
theorem B30811913 : Blo 1899435 30811913 := bstep (se 2 (by rfl) ⟨11554467, by rfl⟩ : syracuseStep 30811913 = 23108935) B23108935
theorem B20541275 : Blo 1899435 20541275 := bstep (se 1 (by rfl) ⟨15405956, by rfl⟩ : syracuseStep 20541275 = 30811913) B30811913
theorem B13694183 : Blo 1899435 13694183 := bstep (se 1 (by rfl) ⟨10270637, by rfl⟩ : syracuseStep 13694183 = 20541275) B20541275
theorem B9129455 : Blo 1899435 9129455 := bstep (se 1 (by rfl) ⟨6847091, by rfl⟩ : syracuseStep 9129455 = 13694183) B13694183
theorem B6086303 : Blo 1899435 6086303 := bstep (se 1 (by rfl) ⟨4564727, by rfl⟩ : syracuseStep 6086303 = 9129455) B9129455
theorem B4057535 : Blo 1899435 4057535 := bstep (se 1 (by rfl) ⟨3043151, by rfl⟩ : syracuseStep 4057535 = 6086303) B6086303
theorem B2705023 : Blo 1899435 2705023 := bstep (se 1 (by rfl) ⟨2028767, by rfl⟩ : syracuseStep 2705023 = 4057535) B4057535
theorem B3606697 : Blo 1899435 3606697 := bstep (se 2 (by rfl) ⟨1352511, by rfl⟩ : syracuseStep 3606697 = 2705023) B2705023
theorem B4808929 : Blo 1899435 4808929 := bstep (se 2 (by rfl) ⟨1803348, by rfl⟩ : syracuseStep 4808929 = 3606697) B3606697
theorem B6411905 : Blo 1899435 6411905 := bstep (se 2 (by rfl) ⟨2404464, by rfl⟩ : syracuseStep 6411905 = 4808929) B4808929
theorem B4274603 : Blo 1899435 4274603 := bstep (se 1 (by rfl) ⟨3205952, by rfl⟩ : syracuseStep 4274603 = 6411905) B6411905
theorem B2849735 : Blo 1899435 2849735 := bstep (se 1 (by rfl) ⟨2137301, by rfl⟩ : syracuseStep 2849735 = 4274603) B4274603
theorem B1899823 : Blo 1899435 1899823 := bstep (se 1 (by rfl) ⟨1424867, by rfl⟩ : syracuseStep 1899823 = 2849735) B2849735
theorem B2849741 : Blo 1899435 2849741 := bbase (se 3 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 2849741 = 1068653) (by norm_num)
theorem B1899827 : Blo 1899435 1899827 := bstep (se 1 (by rfl) ⟨1424870, by rfl⟩ : syracuseStep 1899827 = 2849741) B2849741
theorem B4274621 : Blo 1899435 4274621 := bbase (se 3 (by rfl) ⟨801491, by rfl⟩ : syracuseStep 4274621 = 1602983) (by norm_num)
theorem B2849747 : Blo 1899435 2849747 := bstep (se 1 (by rfl) ⟨2137310, by rfl⟩ : syracuseStep 2849747 = 4274621) B4274621
theorem B1899831 : Blo 1899435 1899831 := bstep (se 1 (by rfl) ⟨1424873, by rfl⟩ : syracuseStep 1899831 = 2849747) B2849747
theorem B3205973 : Blo 1899435 3205973 := bbase (se 9 (by rfl) ⟨9392, by rfl⟩ : syracuseStep 3205973 = 18785) (by norm_num)
theorem B2137315 : Blo 1899435 2137315 := bstep (se 1 (by rfl) ⟨1602986, by rfl⟩ : syracuseStep 2137315 = 3205973) B3205973
theorem B2849753 : Blo 1899435 2849753 := bstep (se 2 (by rfl) ⟨1068657, by rfl⟩ : syracuseStep 2849753 = 2137315) B2137315
theorem B1899835 : Blo 1899435 1899835 := bstep (se 1 (by rfl) ⟨1424876, by rfl⟩ : syracuseStep 1899835 = 2849753) B2849753
theorem B4564765 : Blo 1899435 4564765 := bbase (se 3 (by rfl) ⟨855893, by rfl⟩ : syracuseStep 4564765 = 1711787) (by norm_num)
theorem B6086353 : Blo 1899435 6086353 := bstep (se 2 (by rfl) ⟨2282382, by rfl⟩ : syracuseStep 6086353 = 4564765) B4564765
theorem B8115137 : Blo 1899435 8115137 := bstep (se 2 (by rfl) ⟨3043176, by rfl⟩ : syracuseStep 8115137 = 6086353) B6086353
theorem B5410091 : Blo 1899435 5410091 := bstep (se 1 (by rfl) ⟨4057568, by rfl⟩ : syracuseStep 5410091 = 8115137) B8115137
theorem B14426909 : Blo 1899435 14426909 := bstep (se 3 (by rfl) ⟨2705045, by rfl⟩ : syracuseStep 14426909 = 5410091) B5410091
theorem B9617939 : Blo 1899435 9617939 := bstep (se 1 (by rfl) ⟨7213454, by rfl⟩ : syracuseStep 9617939 = 14426909) B14426909
theorem B6411959 : Blo 1899435 6411959 := bstep (se 1 (by rfl) ⟨4808969, by rfl⟩ : syracuseStep 6411959 = 9617939) B9617939
theorem B4274639 : Blo 1899435 4274639 := bstep (se 1 (by rfl) ⟨3205979, by rfl⟩ : syracuseStep 4274639 = 6411959) B6411959
theorem B2849759 : Blo 1899435 2849759 := bstep (se 1 (by rfl) ⟨2137319, by rfl⟩ : syracuseStep 2849759 = 4274639) B4274639
theorem B1899839 : Blo 1899435 1899839 := bstep (se 1 (by rfl) ⟨1424879, by rfl⟩ : syracuseStep 1899839 = 2849759) B2849759
theorem B2849765 : Blo 1899435 2849765 := bbase (se 4 (by rfl) ⟨267165, by rfl⟩ : syracuseStep 2849765 = 534331) (by norm_num)
theorem B1899843 : Blo 1899435 1899843 := bstep (se 1 (by rfl) ⟨1424882, by rfl⟩ : syracuseStep 1899843 = 2849765) B2849765
theorem B8115173 : Blo 1899435 8115173 := bbase (se 4 (by rfl) ⟨760797, by rfl⟩ : syracuseStep 8115173 = 1521595) (by norm_num)
theorem B5410115 : Blo 1899435 5410115 := bstep (se 1 (by rfl) ⟨4057586, by rfl⟩ : syracuseStep 5410115 = 8115173) B8115173
theorem B3606743 : Blo 1899435 3606743 := bstep (se 1 (by rfl) ⟨2705057, by rfl⟩ : syracuseStep 3606743 = 5410115) B5410115
theorem B2404495 : Blo 1899435 2404495 := bstep (se 1 (by rfl) ⟨1803371, by rfl⟩ : syracuseStep 2404495 = 3606743) B3606743
theorem B3205993 : Blo 1899435 3205993 := bstep (se 2 (by rfl) ⟨1202247, by rfl⟩ : syracuseStep 3205993 = 2404495) B2404495
theorem B4274657 : Blo 1899435 4274657 := bstep (se 2 (by rfl) ⟨1602996, by rfl⟩ : syracuseStep 4274657 = 3205993) B3205993
theorem B2849771 : Blo 1899435 2849771 := bstep (se 1 (by rfl) ⟨2137328, by rfl⟩ : syracuseStep 2849771 = 4274657) B4274657
theorem B1899847 : Blo 1899435 1899847 := bstep (se 1 (by rfl) ⟨1424885, by rfl⟩ : syracuseStep 1899847 = 2849771) B2849771
theorem B2137333 : Blo 1899435 2137333 := bbase (se 5 (by rfl) ⟨100187, by rfl⟩ : syracuseStep 2137333 = 200375) (by norm_num)
theorem B2849777 : Blo 1899435 2849777 := bstep (se 2 (by rfl) ⟨1068666, by rfl⟩ : syracuseStep 2849777 = 2137333) B2137333
theorem B1899851 : Blo 1899435 1899851 := bstep (se 1 (by rfl) ⟨1424888, by rfl⟩ : syracuseStep 1899851 = 2849777) B2849777
theorem B2404505 : Blo 1899435 2404505 := bbase (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) (by norm_num)
theorem B6412013 : Blo 1899435 6412013 := bstep (se 3 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 6412013 = 2404505) B2404505
theorem B4274675 : Blo 1899435 4274675 := bstep (se 1 (by rfl) ⟨3206006, by rfl⟩ : syracuseStep 4274675 = 6412013) B6412013
theorem B2849783 : Blo 1899435 2849783 := bstep (se 1 (by rfl) ⟨2137337, by rfl⟩ : syracuseStep 2849783 = 4274675) B4274675
theorem B1899855 : Blo 1899435 1899855 := bstep (se 1 (by rfl) ⟨1424891, by rfl⟩ : syracuseStep 1899855 = 2849783) B2849783
theorem B2849789 : Blo 1899435 2849789 := bbase (se 3 (by rfl) ⟨534335, by rfl⟩ : syracuseStep 2849789 = 1068671) (by norm_num)
theorem B1899859 : Blo 1899435 1899859 := bstep (se 1 (by rfl) ⟨1424894, by rfl⟩ : syracuseStep 1899859 = 2849789) B2849789
theorem B4274693 : Blo 1899435 4274693 := bbase (se 4 (by rfl) ⟨400752, by rfl⟩ : syracuseStep 4274693 = 801505) (by norm_num)
theorem B2849795 : Blo 1899435 2849795 := bstep (se 1 (by rfl) ⟨2137346, by rfl⟩ : syracuseStep 2849795 = 4274693) B4274693
theorem B1899863 : Blo 1899435 1899863 := bstep (se 1 (by rfl) ⟨1424897, by rfl⟩ : syracuseStep 1899863 = 2849795) B2849795
theorem B3606781 : Blo 1899435 3606781 := bbase (se 3 (by rfl) ⟨676271, by rfl⟩ : syracuseStep 3606781 = 1352543) (by norm_num)
theorem B4809041 : Blo 1899435 4809041 := bstep (se 2 (by rfl) ⟨1803390, by rfl⟩ : syracuseStep 4809041 = 3606781) B3606781
theorem B3206027 : Blo 1899435 3206027 := bstep (se 1 (by rfl) ⟨2404520, by rfl⟩ : syracuseStep 3206027 = 4809041) B4809041
theorem B2137351 : Blo 1899435 2137351 := bstep (se 1 (by rfl) ⟨1603013, by rfl⟩ : syracuseStep 2137351 = 3206027) B3206027
theorem B2849801 : Blo 1899435 2849801 := bstep (se 2 (by rfl) ⟨1068675, by rfl⟩ : syracuseStep 2849801 = 2137351) B2137351
theorem B1899867 : Blo 1899435 1899867 := bstep (se 1 (by rfl) ⟨1424900, by rfl⟩ : syracuseStep 1899867 = 2849801) B2849801
theorem B9618101 : Blo 1899435 9618101 := bbase (se 5 (by rfl) ⟨450848, by rfl⟩ : syracuseStep 9618101 = 901697) (by norm_num)
theorem B6412067 : Blo 1899435 6412067 := bstep (se 1 (by rfl) ⟨4809050, by rfl⟩ : syracuseStep 6412067 = 9618101) B9618101
theorem B4274711 : Blo 1899435 4274711 := bstep (se 1 (by rfl) ⟨3206033, by rfl⟩ : syracuseStep 4274711 = 6412067) B6412067
theorem B2849807 : Blo 1899435 2849807 := bstep (se 1 (by rfl) ⟨2137355, by rfl⟩ : syracuseStep 2849807 = 4274711) B4274711
theorem B1899871 : Blo 1899435 1899871 := bstep (se 1 (by rfl) ⟨1424903, by rfl⟩ : syracuseStep 1899871 = 2849807) B2849807
theorem B2849813 : Blo 1899435 2849813 := bbase (se 6 (by rfl) ⟨66792, by rfl⟩ : syracuseStep 2849813 = 133585) (by norm_num)
theorem B1899875 : Blo 1899435 1899875 := bstep (se 1 (by rfl) ⟨1424906, by rfl⟩ : syracuseStep 1899875 = 2849813) B2849813
theorem B18259445 : Blo 1899435 18259445 := bbase (se 5 (by rfl) ⟨855911, by rfl⟩ : syracuseStep 18259445 = 1711823) (by norm_num)
theorem B12172963 : Blo 1899435 12172963 := bstep (se 1 (by rfl) ⟨9129722, by rfl⟩ : syracuseStep 12172963 = 18259445) B18259445
theorem B16230617 : Blo 1899435 16230617 := bstep (se 2 (by rfl) ⟨6086481, by rfl⟩ : syracuseStep 16230617 = 12172963) B12172963
theorem B10820411 : Blo 1899435 10820411 := bstep (se 1 (by rfl) ⟨8115308, by rfl⟩ : syracuseStep 10820411 = 16230617) B16230617
theorem B7213607 : Blo 1899435 7213607 := bstep (se 1 (by rfl) ⟨5410205, by rfl⟩ : syracuseStep 7213607 = 10820411) B10820411
theorem B4809071 : Blo 1899435 4809071 := bstep (se 1 (by rfl) ⟨3606803, by rfl⟩ : syracuseStep 4809071 = 7213607) B7213607
theorem B3206047 : Blo 1899435 3206047 := bstep (se 1 (by rfl) ⟨2404535, by rfl⟩ : syracuseStep 3206047 = 4809071) B4809071
theorem B4274729 : Blo 1899435 4274729 := bstep (se 2 (by rfl) ⟨1603023, by rfl⟩ : syracuseStep 4274729 = 3206047) B3206047
theorem B2849819 : Blo 1899435 2849819 := bstep (se 1 (by rfl) ⟨2137364, by rfl⟩ : syracuseStep 2849819 = 4274729) B4274729
theorem B1899879 : Blo 1899435 1899879 := bstep (se 1 (by rfl) ⟨1424909, by rfl⟩ : syracuseStep 1899879 = 2849819) B2849819
theorem B2137369 : Blo 1899435 2137369 := bbase (se 2 (by rfl) ⟨801513, by rfl⟩ : syracuseStep 2137369 = 1603027) (by norm_num)
theorem B2849825 : Blo 1899435 2849825 := bstep (se 2 (by rfl) ⟨1068684, by rfl⟩ : syracuseStep 2849825 = 2137369) B2137369
theorem B1899883 : Blo 1899435 1899883 := bstep (se 1 (by rfl) ⟨1424912, by rfl⟩ : syracuseStep 1899883 = 2849825) B2849825
theorem B7213637 : Blo 1899435 7213637 := bbase (se 4 (by rfl) ⟨676278, by rfl⟩ : syracuseStep 7213637 = 1352557) (by norm_num)
theorem B4809091 : Blo 1899435 4809091 := bstep (se 1 (by rfl) ⟨3606818, by rfl⟩ : syracuseStep 4809091 = 7213637) B7213637
theorem B6412121 : Blo 1899435 6412121 := bstep (se 2 (by rfl) ⟨2404545, by rfl⟩ : syracuseStep 6412121 = 4809091) B4809091
theorem B4274747 : Blo 1899435 4274747 := bstep (se 1 (by rfl) ⟨3206060, by rfl⟩ : syracuseStep 4274747 = 6412121) B6412121
theorem B2849831 : Blo 1899435 2849831 := bstep (se 1 (by rfl) ⟨2137373, by rfl⟩ : syracuseStep 2849831 = 4274747) B4274747
theorem B1899887 : Blo 1899435 1899887 := bstep (se 1 (by rfl) ⟨1424915, by rfl⟩ : syracuseStep 1899887 = 2849831) B2849831
theorem B2849837 : Blo 1899435 2849837 := bbase (se 3 (by rfl) ⟨534344, by rfl⟩ : syracuseStep 2849837 = 1068689) (by norm_num)
theorem B1899891 : Blo 1899435 1899891 := bstep (se 1 (by rfl) ⟨1424918, by rfl⟩ : syracuseStep 1899891 = 2849837) B2849837
theorem B4274765 : Blo 1899435 4274765 := bbase (se 3 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 4274765 = 1603037) (by norm_num)
theorem B2849843 : Blo 1899435 2849843 := bstep (se 1 (by rfl) ⟨2137382, by rfl⟩ : syracuseStep 2849843 = 4274765) B4274765
theorem B1899895 : Blo 1899435 1899895 := bstep (se 1 (by rfl) ⟨1424921, by rfl⟩ : syracuseStep 1899895 = 2849843) B2849843
theorem B2404561 : Blo 1899435 2404561 := bbase (se 2 (by rfl) ⟨901710, by rfl⟩ : syracuseStep 2404561 = 1803421) (by norm_num)
theorem B3206081 : Blo 1899435 3206081 := bstep (se 2 (by rfl) ⟨1202280, by rfl⟩ : syracuseStep 3206081 = 2404561) B2404561
theorem B2137387 : Blo 1899435 2137387 := bstep (se 1 (by rfl) ⟨1603040, by rfl⟩ : syracuseStep 2137387 = 3206081) B3206081
theorem B2849849 : Blo 1899435 2849849 := bstep (se 2 (by rfl) ⟨1068693, by rfl⟩ : syracuseStep 2849849 = 2137387) B2137387
theorem B1899899 : Blo 1899435 1899899 := bstep (se 1 (by rfl) ⟨1424924, by rfl⟩ : syracuseStep 1899899 = 2849849) B2849849
theorem B5777477 : Blo 1899435 5777477 := bbase (se 4 (by rfl) ⟨541638, by rfl⟩ : syracuseStep 5777477 = 1083277) (by norm_num)
theorem B3851651 : Blo 1899435 3851651 := bstep (se 1 (by rfl) ⟨2888738, by rfl⟩ : syracuseStep 3851651 = 5777477) B5777477
theorem B10271069 : Blo 1899435 10271069 := bstep (se 3 (by rfl) ⟨1925825, by rfl⟩ : syracuseStep 10271069 = 3851651) B3851651
theorem B6847379 : Blo 1899435 6847379 := bstep (se 1 (by rfl) ⟨5135534, by rfl⟩ : syracuseStep 6847379 = 10271069) B10271069
theorem B4564919 : Blo 1899435 4564919 := bstep (se 1 (by rfl) ⟨3423689, by rfl⟩ : syracuseStep 4564919 = 6847379) B6847379
theorem B3043279 : Blo 1899435 3043279 := bstep (se 1 (by rfl) ⟨2282459, by rfl⟩ : syracuseStep 3043279 = 4564919) B4564919
theorem B4057705 : Blo 1899435 4057705 := bstep (se 2 (by rfl) ⟨1521639, by rfl⟩ : syracuseStep 4057705 = 3043279) B3043279
theorem B21641093 : Blo 1899435 21641093 := bstep (se 4 (by rfl) ⟨2028852, by rfl⟩ : syracuseStep 21641093 = 4057705) B4057705
theorem B14427395 : Blo 1899435 14427395 := bstep (se 1 (by rfl) ⟨10820546, by rfl⟩ : syracuseStep 14427395 = 21641093) B21641093
theorem B9618263 : Blo 1899435 9618263 := bstep (se 1 (by rfl) ⟨7213697, by rfl⟩ : syracuseStep 9618263 = 14427395) B14427395
theorem B6412175 : Blo 1899435 6412175 := bstep (se 1 (by rfl) ⟨4809131, by rfl⟩ : syracuseStep 6412175 = 9618263) B9618263
theorem B4274783 : Blo 1899435 4274783 := bstep (se 1 (by rfl) ⟨3206087, by rfl⟩ : syracuseStep 4274783 = 6412175) B6412175
theorem B2849855 : Blo 1899435 2849855 := bstep (se 1 (by rfl) ⟨2137391, by rfl⟩ : syracuseStep 2849855 = 4274783) B4274783
theorem B1899903 : Blo 1899435 1899903 := bstep (se 1 (by rfl) ⟨1424927, by rfl⟩ : syracuseStep 1899903 = 2849855) B2849855
theorem B2849861 : Blo 1899435 2849861 := bbase (se 4 (by rfl) ⟨267174, by rfl⟩ : syracuseStep 2849861 = 534349) (by norm_num)
theorem B1899907 : Blo 1899435 1899907 := bstep (se 1 (by rfl) ⟨1424930, by rfl⟩ : syracuseStep 1899907 = 2849861) B2849861
theorem B3206101 : Blo 1899435 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B4274801 : Blo 1899435 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B2849867 : Blo 1899435 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B1899911 : Blo 1899435 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B2137405 : Blo 1899435 2137405 := bbase (se 3 (by rfl) ⟨400763, by rfl⟩ : syracuseStep 2137405 = 801527) (by norm_num)
theorem B2849873 : Blo 1899435 2849873 := bstep (se 2 (by rfl) ⟨1068702, by rfl⟩ : syracuseStep 2849873 = 2137405) B2137405
theorem B1899915 : Blo 1899435 1899915 := bstep (se 1 (by rfl) ⟨1424936, by rfl⟩ : syracuseStep 1899915 = 2849873) B2849873
theorem B6412229 : Blo 1899435 6412229 := bbase (se 4 (by rfl) ⟨601146, by rfl⟩ : syracuseStep 6412229 = 1202293) (by norm_num)
theorem B4274819 : Blo 1899435 4274819 := bstep (se 1 (by rfl) ⟨3206114, by rfl⟩ : syracuseStep 4274819 = 6412229) B6412229
theorem B2849879 : Blo 1899435 2849879 := bstep (se 1 (by rfl) ⟨2137409, by rfl⟩ : syracuseStep 2849879 = 4274819) B4274819
theorem B1899919 : Blo 1899435 1899919 := bstep (se 1 (by rfl) ⟨1424939, by rfl⟩ : syracuseStep 1899919 = 2849879) B2849879
theorem B2849885 : Blo 1899435 2849885 := bbase (se 3 (by rfl) ⟨534353, by rfl⟩ : syracuseStep 2849885 = 1068707) (by norm_num)
theorem B1899923 : Blo 1899435 1899923 := bstep (se 1 (by rfl) ⟨1424942, by rfl⟩ : syracuseStep 1899923 = 2849885) B2849885
theorem B4274837 : Blo 1899435 4274837 := bbase (se 6 (by rfl) ⟨100191, by rfl⟩ : syracuseStep 4274837 = 200383) (by norm_num)
theorem B2849891 : Blo 1899435 2849891 := bstep (se 1 (by rfl) ⟨2137418, by rfl⟩ : syracuseStep 2849891 = 4274837) B4274837
theorem B1899927 : Blo 1899435 1899927 := bstep (se 1 (by rfl) ⟨1424945, by rfl⟩ : syracuseStep 1899927 = 2849891) B2849891
theorem B3043325 : Blo 1899435 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B2028883 : Blo 1899435 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B2705177 : Blo 1899435 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B7213805 : Blo 1899435 7213805 := bstep (se 3 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 7213805 = 2705177) B2705177
theorem B4809203 : Blo 1899435 4809203 := bstep (se 1 (by rfl) ⟨3606902, by rfl⟩ : syracuseStep 4809203 = 7213805) B7213805
theorem B3206135 : Blo 1899435 3206135 := bstep (se 1 (by rfl) ⟨2404601, by rfl⟩ : syracuseStep 3206135 = 4809203) B4809203
theorem B2137423 : Blo 1899435 2137423 := bstep (se 1 (by rfl) ⟨1603067, by rfl⟩ : syracuseStep 2137423 = 3206135) B3206135
theorem B2849897 : Blo 1899435 2849897 := bstep (se 2 (by rfl) ⟨1068711, by rfl⟩ : syracuseStep 2849897 = 2137423) B2137423
theorem B1899931 : Blo 1899435 1899931 := bstep (se 1 (by rfl) ⟨1424948, by rfl⟩ : syracuseStep 1899931 = 2849897) B2849897
theorem B5777573 : Blo 1899435 5777573 := bbase (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) (by norm_num)
theorem B15406861 : Blo 1899435 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B20542481 : Blo 1899435 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B13694987 : Blo 1899435 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B9129991 : Blo 1899435 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B12173321 : Blo 1899435 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B8115547 : Blo 1899435 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B10820729 : Blo 1899435 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B7213819 : Blo 1899435 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B9618425 : Blo 1899435 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B6412283 : Blo 1899435 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B4274855 : Blo 1899435 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B2849903 : Blo 1899435 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B1899935 : Blo 1899435 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B2849909 : Blo 1899435 2849909 := bbase (se 5 (by rfl) ⟨133589, by rfl⟩ : syracuseStep 2849909 = 267179) (by norm_num)
theorem B1899939 : Blo 1899435 1899939 := bstep (se 1 (by rfl) ⟨1424954, by rfl⟩ : syracuseStep 1899939 = 2849909) B2849909
theorem B3606925 : Blo 1899435 3606925 := bbase (se 3 (by rfl) ⟨676298, by rfl⟩ : syracuseStep 3606925 = 1352597) (by norm_num)
theorem B4809233 : Blo 1899435 4809233 := bstep (se 2 (by rfl) ⟨1803462, by rfl⟩ : syracuseStep 4809233 = 3606925) B3606925
theorem B3206155 : Blo 1899435 3206155 := bstep (se 1 (by rfl) ⟨2404616, by rfl⟩ : syracuseStep 3206155 = 4809233) B4809233
theorem B4274873 : Blo 1899435 4274873 := bstep (se 2 (by rfl) ⟨1603077, by rfl⟩ : syracuseStep 4274873 = 3206155) B3206155
theorem B2849915 : Blo 1899435 2849915 := bstep (se 1 (by rfl) ⟨2137436, by rfl⟩ : syracuseStep 2849915 = 4274873) B4274873
theorem B1899943 : Blo 1899435 1899943 := bstep (se 1 (by rfl) ⟨1424957, by rfl⟩ : syracuseStep 1899943 = 2849915) B2849915
theorem B2137441 : Blo 1899435 2137441 := bbase (se 2 (by rfl) ⟨801540, by rfl⟩ : syracuseStep 2137441 = 1603081) (by norm_num)
theorem B2849921 : Blo 1899435 2849921 := bstep (se 2 (by rfl) ⟨1068720, by rfl⟩ : syracuseStep 2849921 = 2137441) B2137441
theorem B1899947 : Blo 1899435 1899947 := bstep (se 1 (by rfl) ⟨1424960, by rfl⟩ : syracuseStep 1899947 = 2849921) B2849921
theorem B4809253 : Blo 1899435 4809253 := bbase (se 4 (by rfl) ⟨450867, by rfl⟩ : syracuseStep 4809253 = 901735) (by norm_num)
theorem B6412337 : Blo 1899435 6412337 := bstep (se 2 (by rfl) ⟨2404626, by rfl⟩ : syracuseStep 6412337 = 4809253) B4809253
theorem B4274891 : Blo 1899435 4274891 := bstep (se 1 (by rfl) ⟨3206168, by rfl⟩ : syracuseStep 4274891 = 6412337) B6412337
theorem B2849927 : Blo 1899435 2849927 := bstep (se 1 (by rfl) ⟨2137445, by rfl⟩ : syracuseStep 2849927 = 4274891) B4274891
theorem B1899951 : Blo 1899435 1899951 := bstep (se 1 (by rfl) ⟨1424963, by rfl⟩ : syracuseStep 1899951 = 2849927) B2849927
theorem B2849933 : Blo 1899435 2849933 := bbase (se 3 (by rfl) ⟨534362, by rfl⟩ : syracuseStep 2849933 = 1068725) (by norm_num)
theorem B1899955 : Blo 1899435 1899955 := bstep (se 1 (by rfl) ⟨1424966, by rfl⟩ : syracuseStep 1899955 = 2849933) B2849933
theorem B4274909 : Blo 1899435 4274909 := bbase (se 3 (by rfl) ⟨801545, by rfl⟩ : syracuseStep 4274909 = 1603091) (by norm_num)
theorem B2849939 : Blo 1899435 2849939 := bstep (se 1 (by rfl) ⟨2137454, by rfl⟩ : syracuseStep 2849939 = 4274909) B4274909
theorem B1899959 : Blo 1899435 1899959 := bstep (se 1 (by rfl) ⟨1424969, by rfl⟩ : syracuseStep 1899959 = 2849939) B2849939
theorem B3206189 : Blo 1899435 3206189 := bbase (se 3 (by rfl) ⟨601160, by rfl⟩ : syracuseStep 3206189 = 1202321) (by norm_num)
theorem B2137459 : Blo 1899435 2137459 := bstep (se 1 (by rfl) ⟨1603094, by rfl⟩ : syracuseStep 2137459 = 3206189) B3206189
theorem B2849945 : Blo 1899435 2849945 := bstep (se 2 (by rfl) ⟨1068729, by rfl⟩ : syracuseStep 2849945 = 2137459) B2137459
theorem B1899963 : Blo 1899435 1899963 := bstep (se 1 (by rfl) ⟨1424972, by rfl⟩ : syracuseStep 1899963 = 2849945) B2849945
theorem B4874909 : Blo 1899435 4874909 := bbase (se 3 (by rfl) ⟨914045, by rfl⟩ : syracuseStep 4874909 = 1828091) (by norm_num)
theorem B51999029 : Blo 1899435 51999029 := bstep (se 5 (by rfl) ⟨2437454, by rfl⟩ : syracuseStep 51999029 = 4874909) B4874909
theorem B34666019 : Blo 1899435 34666019 := bstep (se 1 (by rfl) ⟨25999514, by rfl⟩ : syracuseStep 34666019 = 51999029) B51999029
theorem B23110679 : Blo 1899435 23110679 := bstep (se 1 (by rfl) ⟨17333009, by rfl⟩ : syracuseStep 23110679 = 34666019) B34666019
theorem B15407119 : Blo 1899435 15407119 := bstep (se 1 (by rfl) ⟨11555339, by rfl⟩ : syracuseStep 15407119 = 23110679) B23110679
theorem B20542825 : Blo 1899435 20542825 := bstep (se 2 (by rfl) ⟨7703559, by rfl⟩ : syracuseStep 20542825 = 15407119) B15407119
theorem B27390433 : Blo 1899435 27390433 := bstep (se 2 (by rfl) ⟨10271412, by rfl⟩ : syracuseStep 27390433 = 20542825) B20542825
theorem B36520577 : Blo 1899435 36520577 := bstep (se 2 (by rfl) ⟨13695216, by rfl⟩ : syracuseStep 36520577 = 27390433) B27390433
theorem B24347051 : Blo 1899435 24347051 := bstep (se 1 (by rfl) ⟨18260288, by rfl⟩ : syracuseStep 24347051 = 36520577) B36520577
theorem B16231367 : Blo 1899435 16231367 := bstep (se 1 (by rfl) ⟨12173525, by rfl⟩ : syracuseStep 16231367 = 24347051) B24347051
theorem B10820911 : Blo 1899435 10820911 := bstep (se 1 (by rfl) ⟨8115683, by rfl⟩ : syracuseStep 10820911 = 16231367) B16231367
theorem B14427881 : Blo 1899435 14427881 := bstep (se 2 (by rfl) ⟨5410455, by rfl⟩ : syracuseStep 14427881 = 10820911) B10820911
theorem B9618587 : Blo 1899435 9618587 := bstep (se 1 (by rfl) ⟨7213940, by rfl⟩ : syracuseStep 9618587 = 14427881) B14427881
theorem B6412391 : Blo 1899435 6412391 := bstep (se 1 (by rfl) ⟨4809293, by rfl⟩ : syracuseStep 6412391 = 9618587) B9618587
theorem B4274927 : Blo 1899435 4274927 := bstep (se 1 (by rfl) ⟨3206195, by rfl⟩ : syracuseStep 4274927 = 6412391) B6412391
theorem B2849951 : Blo 1899435 2849951 := bstep (se 1 (by rfl) ⟨2137463, by rfl⟩ : syracuseStep 2849951 = 4274927) B4274927
theorem B1899967 : Blo 1899435 1899967 := bstep (se 1 (by rfl) ⟨1424975, by rfl⟩ : syracuseStep 1899967 = 2849951) B2849951
theorem B2849957 : Blo 1899435 2849957 := bbase (se 4 (by rfl) ⟨267183, by rfl⟩ : syracuseStep 2849957 = 534367) (by norm_num)
theorem B1899971 : Blo 1899435 1899971 := bstep (se 1 (by rfl) ⟨1424978, by rfl⟩ : syracuseStep 1899971 = 2849957) B2849957
theorem B2404657 : Blo 1899435 2404657 := bbase (se 2 (by rfl) ⟨901746, by rfl⟩ : syracuseStep 2404657 = 1803493) (by norm_num)
theorem B3206209 : Blo 1899435 3206209 := bstep (se 2 (by rfl) ⟨1202328, by rfl⟩ : syracuseStep 3206209 = 2404657) B2404657
theorem B4274945 : Blo 1899435 4274945 := bstep (se 2 (by rfl) ⟨1603104, by rfl⟩ : syracuseStep 4274945 = 3206209) B3206209
theorem B2849963 : Blo 1899435 2849963 := bstep (se 1 (by rfl) ⟨2137472, by rfl⟩ : syracuseStep 2849963 = 4274945) B4274945
theorem B1899975 : Blo 1899435 1899975 := bstep (se 1 (by rfl) ⟨1424981, by rfl⟩ : syracuseStep 1899975 = 2849963) B2849963
theorem B2137477 : Blo 1899435 2137477 := bbase (se 4 (by rfl) ⟨200388, by rfl⟩ : syracuseStep 2137477 = 400777) (by norm_num)
theorem B2849969 : Blo 1899435 2849969 := bstep (se 2 (by rfl) ⟨1068738, by rfl⟩ : syracuseStep 2849969 = 2137477) B2137477
theorem B1899979 : Blo 1899435 1899979 := bstep (se 1 (by rfl) ⟨1424984, by rfl⟩ : syracuseStep 1899979 = 2849969) B2849969
theorem B4057877 : Blo 1899435 4057877 := bbase (se 6 (by rfl) ⟨95106, by rfl⟩ : syracuseStep 4057877 = 190213) (by norm_num)
theorem B2705251 : Blo 1899435 2705251 := bstep (se 1 (by rfl) ⟨2028938, by rfl⟩ : syracuseStep 2705251 = 4057877) B4057877
theorem B3607001 : Blo 1899435 3607001 := bstep (se 2 (by rfl) ⟨1352625, by rfl⟩ : syracuseStep 3607001 = 2705251) B2705251
theorem B2404667 : Blo 1899435 2404667 := bstep (se 1 (by rfl) ⟨1803500, by rfl⟩ : syracuseStep 2404667 = 3607001) B3607001
theorem B6412445 : Blo 1899435 6412445 := bstep (se 3 (by rfl) ⟨1202333, by rfl⟩ : syracuseStep 6412445 = 2404667) B2404667
theorem B4274963 : Blo 1899435 4274963 := bstep (se 1 (by rfl) ⟨3206222, by rfl⟩ : syracuseStep 4274963 = 6412445) B6412445
theorem B2849975 : Blo 1899435 2849975 := bstep (se 1 (by rfl) ⟨2137481, by rfl⟩ : syracuseStep 2849975 = 4274963) B4274963
theorem B1899983 : Blo 1899435 1899983 := bstep (se 1 (by rfl) ⟨1424987, by rfl⟩ : syracuseStep 1899983 = 2849975) B2849975
theorem B2849981 : Blo 1899435 2849981 := bbase (se 3 (by rfl) ⟨534371, by rfl⟩ : syracuseStep 2849981 = 1068743) (by norm_num)
theorem B1899987 : Blo 1899435 1899987 := bstep (se 1 (by rfl) ⟨1424990, by rfl⟩ : syracuseStep 1899987 = 2849981) B2849981
theorem B4274981 : Blo 1899435 4274981 := bbase (se 4 (by rfl) ⟨400779, by rfl⟩ : syracuseStep 4274981 = 801559) (by norm_num)
theorem B2849987 : Blo 1899435 2849987 := bstep (se 1 (by rfl) ⟨2137490, by rfl⟩ : syracuseStep 2849987 = 4274981) B4274981
theorem B1899991 : Blo 1899435 1899991 := bstep (se 1 (by rfl) ⟨1424993, by rfl⟩ : syracuseStep 1899991 = 2849987) B2849987
theorem B4809365 : Blo 1899435 4809365 := bbase (se 6 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 4809365 = 225439) (by norm_num)
theorem B3206243 : Blo 1899435 3206243 := bstep (se 1 (by rfl) ⟨2404682, by rfl⟩ : syracuseStep 3206243 = 4809365) B4809365
theorem B2137495 : Blo 1899435 2137495 := bstep (se 1 (by rfl) ⟨1603121, by rfl⟩ : syracuseStep 2137495 = 3206243) B3206243
theorem B2849993 : Blo 1899435 2849993 := bstep (se 2 (by rfl) ⟨1068747, by rfl⟩ : syracuseStep 2849993 = 2137495) B2137495
theorem B1899995 : Blo 1899435 1899995 := bstep (se 1 (by rfl) ⟨1424996, by rfl⟩ : syracuseStep 1899995 = 2849993) B2849993
theorem B2888885 : Blo 1899435 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B7703693 : Blo 1899435 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B5135795 : Blo 1899435 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B3423863 : Blo 1899435 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B2282575 : Blo 1899435 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B3043433 : Blo 1899435 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B8115821 : Blo 1899435 8115821 := bstep (se 3 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 8115821 = 3043433) B3043433
theorem B5410547 : Blo 1899435 5410547 := bstep (se 1 (by rfl) ⟨4057910, by rfl⟩ : syracuseStep 5410547 = 8115821) B8115821
theorem B3607031 : Blo 1899435 3607031 := bstep (se 1 (by rfl) ⟨2705273, by rfl⟩ : syracuseStep 3607031 = 5410547) B5410547
theorem B9618749 : Blo 1899435 9618749 := bstep (se 3 (by rfl) ⟨1803515, by rfl⟩ : syracuseStep 9618749 = 3607031) B3607031
theorem B6412499 : Blo 1899435 6412499 := bstep (se 1 (by rfl) ⟨4809374, by rfl⟩ : syracuseStep 6412499 = 9618749) B9618749
theorem B4274999 : Blo 1899435 4274999 := bstep (se 1 (by rfl) ⟨3206249, by rfl⟩ : syracuseStep 4274999 = 6412499) B6412499
theorem B2849999 : Blo 1899435 2849999 := bstep (se 1 (by rfl) ⟨2137499, by rfl⟩ : syracuseStep 2849999 = 4274999) B4274999
theorem B1899999 : Blo 1899435 1899999 := bstep (se 1 (by rfl) ⟨1424999, by rfl⟩ : syracuseStep 1899999 = 2849999) B2849999
theorem B2850005 : Blo 1899435 2850005 := bbase (se 7 (by rfl) ⟨33398, by rfl⟩ : syracuseStep 2850005 = 66797) (by norm_num)
theorem B1900003 : Blo 1899435 1900003 := bstep (se 1 (by rfl) ⟨1425002, by rfl⟩ : syracuseStep 1900003 = 2850005) B2850005
theorem B2705285 : Blo 1899435 2705285 := bbase (se 4 (by rfl) ⟨253620, by rfl⟩ : syracuseStep 2705285 = 507241) (by norm_num)
theorem B7214093 : Blo 1899435 7214093 := bstep (se 3 (by rfl) ⟨1352642, by rfl⟩ : syracuseStep 7214093 = 2705285) B2705285
theorem B4809395 : Blo 1899435 4809395 := bstep (se 1 (by rfl) ⟨3607046, by rfl⟩ : syracuseStep 4809395 = 7214093) B7214093
theorem B3206263 : Blo 1899435 3206263 := bstep (se 1 (by rfl) ⟨2404697, by rfl⟩ : syracuseStep 3206263 = 4809395) B4809395
theorem B4275017 : Blo 1899435 4275017 := bstep (se 2 (by rfl) ⟨1603131, by rfl⟩ : syracuseStep 4275017 = 3206263) B3206263
theorem B2850011 : Blo 1899435 2850011 := bstep (se 1 (by rfl) ⟨2137508, by rfl⟩ : syracuseStep 2850011 = 4275017) B4275017
theorem B1900007 : Blo 1899435 1900007 := bstep (se 1 (by rfl) ⟨1425005, by rfl⟩ : syracuseStep 1900007 = 2850011) B2850011
theorem B2137513 : Blo 1899435 2137513 := bbase (se 2 (by rfl) ⟨801567, by rfl⟩ : syracuseStep 2137513 = 1603135) (by norm_num)
theorem B2850017 : Blo 1899435 2850017 := bstep (se 2 (by rfl) ⟨1068756, by rfl⟩ : syracuseStep 2850017 = 2137513) B2137513
theorem B1900011 : Blo 1899435 1900011 := bstep (se 1 (by rfl) ⟨1425008, by rfl⟩ : syracuseStep 1900011 = 2850017) B2850017
theorem B6086917 : Blo 1899435 6086917 := bbase (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) (by norm_num)
theorem B8115889 : Blo 1899435 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B10821185 : Blo 1899435 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B7214123 : Blo 1899435 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B4809415 : Blo 1899435 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B6412553 : Blo 1899435 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B4275035 : Blo 1899435 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B2850023 : Blo 1899435 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B1900015 : Blo 1899435 1900015 := bstep (se 1 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 1900015 = 2850023) B2850023
theorem B2850029 : Blo 1899435 2850029 := bbase (se 3 (by rfl) ⟨534380, by rfl⟩ : syracuseStep 2850029 = 1068761) (by norm_num)
theorem B1900019 : Blo 1899435 1900019 := bstep (se 1 (by rfl) ⟨1425014, by rfl⟩ : syracuseStep 1900019 = 2850029) B2850029
theorem B4275053 : Blo 1899435 4275053 := bbase (se 3 (by rfl) ⟨801572, by rfl⟩ : syracuseStep 4275053 = 1603145) (by norm_num)
theorem B2850035 : Blo 1899435 2850035 := bstep (se 1 (by rfl) ⟨2137526, by rfl⟩ : syracuseStep 2850035 = 4275053) B4275053
theorem B1900023 : Blo 1899435 1900023 := bstep (se 1 (by rfl) ⟨1425017, by rfl⟩ : syracuseStep 1900023 = 2850035) B2850035
theorem B3607085 : Blo 1899435 3607085 := bbase (se 3 (by rfl) ⟨676328, by rfl⟩ : syracuseStep 3607085 = 1352657) (by norm_num)
theorem B2404723 : Blo 1899435 2404723 := bstep (se 1 (by rfl) ⟨1803542, by rfl⟩ : syracuseStep 2404723 = 3607085) B3607085
theorem B3206297 : Blo 1899435 3206297 := bstep (se 2 (by rfl) ⟨1202361, by rfl⟩ : syracuseStep 3206297 = 2404723) B2404723
theorem B2137531 : Blo 1899435 2137531 := bstep (se 1 (by rfl) ⟨1603148, by rfl⟩ : syracuseStep 2137531 = 3206297) B3206297
theorem B2850041 : Blo 1899435 2850041 := bstep (se 2 (by rfl) ⟨1068765, by rfl⟩ : syracuseStep 2850041 = 2137531) B2137531
theorem B1900027 : Blo 1899435 1900027 := bstep (se 1 (by rfl) ⟨1425020, by rfl⟩ : syracuseStep 1900027 = 2850041) B2850041
theorem B2742229 : Blo 1899435 2742229 := bbase (se 7 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 2742229 = 64271) (by norm_num)
theorem B3656305 : Blo 1899435 3656305 := bstep (se 2 (by rfl) ⟨1371114, by rfl⟩ : syracuseStep 3656305 = 2742229) B2742229
theorem B4875073 : Blo 1899435 4875073 := bstep (se 2 (by rfl) ⟨1828152, by rfl⟩ : syracuseStep 4875073 = 3656305) B3656305
theorem B26000389 : Blo 1899435 26000389 := bstep (se 4 (by rfl) ⟨2437536, by rfl⟩ : syracuseStep 26000389 = 4875073) B4875073
theorem B34667185 : Blo 1899435 34667185 := bstep (se 2 (by rfl) ⟨13000194, by rfl⟩ : syracuseStep 34667185 = 26000389) B26000389
theorem B46222913 : Blo 1899435 46222913 := bstep (se 2 (by rfl) ⟨17333592, by rfl⟩ : syracuseStep 46222913 = 34667185) B34667185
theorem B30815275 : Blo 1899435 30815275 := bstep (se 1 (by rfl) ⟨23111456, by rfl⟩ : syracuseStep 30815275 = 46222913) B46222913
theorem B41087033 : Blo 1899435 41087033 := bstep (se 2 (by rfl) ⟨15407637, by rfl⟩ : syracuseStep 41087033 = 30815275) B30815275
theorem B27391355 : Blo 1899435 27391355 := bstep (se 1 (by rfl) ⟨20543516, by rfl⟩ : syracuseStep 27391355 = 41087033) B41087033
theorem B18260903 : Blo 1899435 18260903 := bstep (se 1 (by rfl) ⟨13695677, by rfl⟩ : syracuseStep 18260903 = 27391355) B27391355
theorem B48695741 : Blo 1899435 48695741 := bstep (se 3 (by rfl) ⟨9130451, by rfl⟩ : syracuseStep 48695741 = 18260903) B18260903
theorem B32463827 : Blo 1899435 32463827 := bstep (se 1 (by rfl) ⟨24347870, by rfl⟩ : syracuseStep 32463827 = 48695741) B48695741
theorem B21642551 : Blo 1899435 21642551 := bstep (se 1 (by rfl) ⟨16231913, by rfl⟩ : syracuseStep 21642551 = 32463827) B32463827
theorem B14428367 : Blo 1899435 14428367 := bstep (se 1 (by rfl) ⟨10821275, by rfl⟩ : syracuseStep 14428367 = 21642551) B21642551
theorem B9618911 : Blo 1899435 9618911 := bstep (se 1 (by rfl) ⟨7214183, by rfl⟩ : syracuseStep 9618911 = 14428367) B14428367
theorem B6412607 : Blo 1899435 6412607 := bstep (se 1 (by rfl) ⟨4809455, by rfl⟩ : syracuseStep 6412607 = 9618911) B9618911
theorem B4275071 : Blo 1899435 4275071 := bstep (se 1 (by rfl) ⟨3206303, by rfl⟩ : syracuseStep 4275071 = 6412607) B6412607
theorem B2850047 : Blo 1899435 2850047 := bstep (se 1 (by rfl) ⟨2137535, by rfl⟩ : syracuseStep 2850047 = 4275071) B4275071
theorem B1900031 : Blo 1899435 1900031 := bstep (se 1 (by rfl) ⟨1425023, by rfl⟩ : syracuseStep 1900031 = 2850047) B2850047
theorem B2850053 : Blo 1899435 2850053 := bbase (se 4 (by rfl) ⟨267192, by rfl⟩ : syracuseStep 2850053 = 534385) (by norm_num)
theorem B1900035 : Blo 1899435 1900035 := bstep (se 1 (by rfl) ⟨1425026, by rfl⟩ : syracuseStep 1900035 = 2850053) B2850053
theorem B3206317 : Blo 1899435 3206317 := bbase (se 3 (by rfl) ⟨601184, by rfl⟩ : syracuseStep 3206317 = 1202369) (by norm_num)
theorem B4275089 : Blo 1899435 4275089 := bstep (se 2 (by rfl) ⟨1603158, by rfl⟩ : syracuseStep 4275089 = 3206317) B3206317
theorem B2850059 : Blo 1899435 2850059 := bstep (se 1 (by rfl) ⟨2137544, by rfl⟩ : syracuseStep 2850059 = 4275089) B4275089
theorem B1900039 : Blo 1899435 1900039 := bstep (se 1 (by rfl) ⟨1425029, by rfl⟩ : syracuseStep 1900039 = 2850059) B2850059
theorem B2137549 : Blo 1899435 2137549 := bbase (se 3 (by rfl) ⟨400790, by rfl⟩ : syracuseStep 2137549 = 801581) (by norm_num)
theorem B2850065 : Blo 1899435 2850065 := bstep (se 2 (by rfl) ⟨1068774, by rfl⟩ : syracuseStep 2850065 = 2137549) B2137549
theorem B1900043 : Blo 1899435 1900043 := bstep (se 1 (by rfl) ⟨1425032, by rfl⟩ : syracuseStep 1900043 = 2850065) B2850065
theorem B6412661 : Blo 1899435 6412661 := bbase (se 5 (by rfl) ⟨300593, by rfl⟩ : syracuseStep 6412661 = 601187) (by norm_num)
theorem B4275107 : Blo 1899435 4275107 := bstep (se 1 (by rfl) ⟨3206330, by rfl⟩ : syracuseStep 4275107 = 6412661) B6412661
theorem B2850071 : Blo 1899435 2850071 := bstep (se 1 (by rfl) ⟨2137553, by rfl⟩ : syracuseStep 2850071 = 4275107) B4275107
theorem B1900047 : Blo 1899435 1900047 := bstep (se 1 (by rfl) ⟨1425035, by rfl⟩ : syracuseStep 1900047 = 2850071) B2850071
theorem B2850077 : Blo 1899435 2850077 := bbase (se 3 (by rfl) ⟨534389, by rfl⟩ : syracuseStep 2850077 = 1068779) (by norm_num)
theorem B1900051 : Blo 1899435 1900051 := bstep (se 1 (by rfl) ⟨1425038, by rfl⟩ : syracuseStep 1900051 = 2850077) B2850077
theorem B4275125 : Blo 1899435 4275125 := bbase (se 5 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 4275125 = 400793) (by norm_num)
theorem B2850083 : Blo 1899435 2850083 := bstep (se 1 (by rfl) ⟨2137562, by rfl⟩ : syracuseStep 2850083 = 4275125) B4275125
theorem B1900055 : Blo 1899435 1900055 := bstep (se 1 (by rfl) ⟨1425041, by rfl⟩ : syracuseStep 1900055 = 2850083) B2850083
theorem B5135957 : Blo 1899435 5135957 := bbase (se 8 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 5135957 = 60187) (by norm_num)
theorem B3423971 : Blo 1899435 3423971 := bstep (se 1 (by rfl) ⟨2567978, by rfl⟩ : syracuseStep 3423971 = 5135957) B5135957
theorem B9130589 : Blo 1899435 9130589 := bstep (se 3 (by rfl) ⟨1711985, by rfl⟩ : syracuseStep 9130589 = 3423971) B3423971
theorem B6087059 : Blo 1899435 6087059 := bstep (se 1 (by rfl) ⟨4565294, by rfl⟩ : syracuseStep 6087059 = 9130589) B9130589
theorem B4058039 : Blo 1899435 4058039 := bstep (se 1 (by rfl) ⟨3043529, by rfl⟩ : syracuseStep 4058039 = 6087059) B6087059
theorem B10821437 : Blo 1899435 10821437 := bstep (se 3 (by rfl) ⟨2029019, by rfl⟩ : syracuseStep 10821437 = 4058039) B4058039
theorem B7214291 : Blo 1899435 7214291 := bstep (se 1 (by rfl) ⟨5410718, by rfl⟩ : syracuseStep 7214291 = 10821437) B10821437
theorem B4809527 : Blo 1899435 4809527 := bstep (se 1 (by rfl) ⟨3607145, by rfl⟩ : syracuseStep 4809527 = 7214291) B7214291
theorem B3206351 : Blo 1899435 3206351 := bstep (se 1 (by rfl) ⟨2404763, by rfl⟩ : syracuseStep 3206351 = 4809527) B4809527
theorem B2137567 : Blo 1899435 2137567 := bstep (se 1 (by rfl) ⟨1603175, by rfl⟩ : syracuseStep 2137567 = 3206351) B3206351
theorem B2850089 : Blo 1899435 2850089 := bstep (se 2 (by rfl) ⟨1068783, by rfl⟩ : syracuseStep 2850089 = 2137567) B2137567
theorem B1900059 : Blo 1899435 1900059 := bstep (se 1 (by rfl) ⟨1425044, by rfl⟩ : syracuseStep 1900059 = 2850089) B2850089
theorem B3470693 : Blo 1899435 3470693 := bbase (se 4 (by rfl) ⟨325377, by rfl⟩ : syracuseStep 3470693 = 650755) (by norm_num)
theorem B9255181 : Blo 1899435 9255181 := bstep (se 3 (by rfl) ⟨1735346, by rfl⟩ : syracuseStep 9255181 = 3470693) B3470693
theorem B12340241 : Blo 1899435 12340241 := bstep (se 2 (by rfl) ⟨4627590, by rfl⟩ : syracuseStep 12340241 = 9255181) B9255181
theorem B8226827 : Blo 1899435 8226827 := bstep (se 1 (by rfl) ⟨6170120, by rfl⟩ : syracuseStep 8226827 = 12340241) B12340241
theorem B5484551 : Blo 1899435 5484551 := bstep (se 1 (by rfl) ⟨4113413, by rfl⟩ : syracuseStep 5484551 = 8226827) B8226827
theorem B14625469 : Blo 1899435 14625469 := bstep (se 3 (by rfl) ⟨2742275, by rfl⟩ : syracuseStep 14625469 = 5484551) B5484551
theorem B19500625 : Blo 1899435 19500625 := bstep (se 2 (by rfl) ⟨7312734, by rfl⟩ : syracuseStep 19500625 = 14625469) B14625469
theorem B26000833 : Blo 1899435 26000833 := bstep (se 2 (by rfl) ⟨9750312, by rfl⟩ : syracuseStep 26000833 = 19500625) B19500625
theorem B34667777 : Blo 1899435 34667777 := bstep (se 2 (by rfl) ⟨13000416, by rfl⟩ : syracuseStep 34667777 = 26000833) B26000833
theorem B23111851 : Blo 1899435 23111851 := bstep (se 1 (by rfl) ⟨17333888, by rfl⟩ : syracuseStep 23111851 = 34667777) B34667777
theorem B30815801 : Blo 1899435 30815801 := bstep (se 2 (by rfl) ⟨11555925, by rfl⟩ : syracuseStep 30815801 = 23111851) B23111851
theorem B20543867 : Blo 1899435 20543867 := bstep (se 1 (by rfl) ⟨15407900, by rfl⟩ : syracuseStep 20543867 = 30815801) B30815801
theorem B13695911 : Blo 1899435 13695911 := bstep (se 1 (by rfl) ⟨10271933, by rfl⟩ : syracuseStep 13695911 = 20543867) B20543867
theorem B9130607 : Blo 1899435 9130607 := bstep (se 1 (by rfl) ⟨6847955, by rfl⟩ : syracuseStep 9130607 = 13695911) B13695911
theorem B6087071 : Blo 1899435 6087071 := bstep (se 1 (by rfl) ⟨4565303, by rfl⟩ : syracuseStep 6087071 = 9130607) B9130607
theorem B4058047 : Blo 1899435 4058047 := bstep (se 1 (by rfl) ⟨3043535, by rfl⟩ : syracuseStep 4058047 = 6087071) B6087071
theorem B5410729 : Blo 1899435 5410729 := bstep (se 2 (by rfl) ⟨2029023, by rfl⟩ : syracuseStep 5410729 = 4058047) B4058047
theorem B7214305 : Blo 1899435 7214305 := bstep (se 2 (by rfl) ⟨2705364, by rfl⟩ : syracuseStep 7214305 = 5410729) B5410729
theorem B9619073 : Blo 1899435 9619073 := bstep (se 2 (by rfl) ⟨3607152, by rfl⟩ : syracuseStep 9619073 = 7214305) B7214305
theorem B6412715 : Blo 1899435 6412715 := bstep (se 1 (by rfl) ⟨4809536, by rfl⟩ : syracuseStep 6412715 = 9619073) B9619073
theorem B4275143 : Blo 1899435 4275143 := bstep (se 1 (by rfl) ⟨3206357, by rfl⟩ : syracuseStep 4275143 = 6412715) B6412715
theorem B2850095 : Blo 1899435 2850095 := bstep (se 1 (by rfl) ⟨2137571, by rfl⟩ : syracuseStep 2850095 = 4275143) B4275143
theorem B1900063 : Blo 1899435 1900063 := bstep (se 1 (by rfl) ⟨1425047, by rfl⟩ : syracuseStep 1900063 = 2850095) B2850095
theorem B2850101 : Blo 1899435 2850101 := bbase (se 5 (by rfl) ⟨133598, by rfl⟩ : syracuseStep 2850101 = 267197) (by norm_num)
theorem B1900067 : Blo 1899435 1900067 := bstep (se 1 (by rfl) ⟨1425050, by rfl⟩ : syracuseStep 1900067 = 2850101) B2850101
theorem B4809557 : Blo 1899435 4809557 := bbase (se 9 (by rfl) ⟨14090, by rfl⟩ : syracuseStep 4809557 = 28181) (by norm_num)
theorem B3206371 : Blo 1899435 3206371 := bstep (se 1 (by rfl) ⟨2404778, by rfl⟩ : syracuseStep 3206371 = 4809557) B4809557
theorem B4275161 : Blo 1899435 4275161 := bstep (se 2 (by rfl) ⟨1603185, by rfl⟩ : syracuseStep 4275161 = 3206371) B3206371
theorem B2850107 : Blo 1899435 2850107 := bstep (se 1 (by rfl) ⟨2137580, by rfl⟩ : syracuseStep 2850107 = 4275161) B4275161
theorem B1900071 : Blo 1899435 1900071 := bstep (se 1 (by rfl) ⟨1425053, by rfl⟩ : syracuseStep 1900071 = 2850107) B2850107
theorem B2137585 : Blo 1899435 2137585 := bbase (se 2 (by rfl) ⟨801594, by rfl⟩ : syracuseStep 2137585 = 1603189) (by norm_num)
theorem B2850113 : Blo 1899435 2850113 := bstep (se 2 (by rfl) ⟨1068792, by rfl⟩ : syracuseStep 2850113 = 2137585) B2137585
theorem B1900075 : Blo 1899435 1900075 := bstep (se 1 (by rfl) ⟨1425056, by rfl⟩ : syracuseStep 1900075 = 2850113) B2850113
theorem B3250133 : Blo 1899435 3250133 := bbase (se 7 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 3250133 = 76175) (by norm_num)
theorem B2166755 : Blo 1899435 2166755 := bstep (se 1 (by rfl) ⟨1625066, by rfl⟩ : syracuseStep 2166755 = 3250133) B3250133
theorem B5778013 : Blo 1899435 5778013 := bstep (se 3 (by rfl) ⟨1083377, by rfl⟩ : syracuseStep 5778013 = 2166755) B2166755
theorem B7704017 : Blo 1899435 7704017 := bstep (se 2 (by rfl) ⟨2889006, by rfl⟩ : syracuseStep 7704017 = 5778013) B5778013
theorem B5136011 : Blo 1899435 5136011 := bstep (se 1 (by rfl) ⟨3852008, by rfl⟩ : syracuseStep 5136011 = 7704017) B7704017
theorem B3424007 : Blo 1899435 3424007 := bstep (se 1 (by rfl) ⟨2568005, by rfl⟩ : syracuseStep 3424007 = 5136011) B5136011
theorem B2282671 : Blo 1899435 2282671 := bstep (se 1 (by rfl) ⟨1712003, by rfl⟩ : syracuseStep 2282671 = 3424007) B3424007
theorem B12174245 : Blo 1899435 12174245 := bstep (se 4 (by rfl) ⟨1141335, by rfl⟩ : syracuseStep 12174245 = 2282671) B2282671
theorem B8116163 : Blo 1899435 8116163 := bstep (se 1 (by rfl) ⟨6087122, by rfl⟩ : syracuseStep 8116163 = 12174245) B12174245
theorem B5410775 : Blo 1899435 5410775 := bstep (se 1 (by rfl) ⟨4058081, by rfl⟩ : syracuseStep 5410775 = 8116163) B8116163
theorem B3607183 : Blo 1899435 3607183 := bstep (se 1 (by rfl) ⟨2705387, by rfl⟩ : syracuseStep 3607183 = 5410775) B5410775
theorem B4809577 : Blo 1899435 4809577 := bstep (se 2 (by rfl) ⟨1803591, by rfl⟩ : syracuseStep 4809577 = 3607183) B3607183
theorem B6412769 : Blo 1899435 6412769 := bstep (se 2 (by rfl) ⟨2404788, by rfl⟩ : syracuseStep 6412769 = 4809577) B4809577
theorem B4275179 : Blo 1899435 4275179 := bstep (se 1 (by rfl) ⟨3206384, by rfl⟩ : syracuseStep 4275179 = 6412769) B6412769
theorem B2850119 : Blo 1899435 2850119 := bstep (se 1 (by rfl) ⟨2137589, by rfl⟩ : syracuseStep 2850119 = 4275179) B4275179
theorem B1900079 : Blo 1899435 1900079 := bstep (se 1 (by rfl) ⟨1425059, by rfl⟩ : syracuseStep 1900079 = 2850119) B2850119
theorem B2850125 : Blo 1899435 2850125 := bbase (se 3 (by rfl) ⟨534398, by rfl⟩ : syracuseStep 2850125 = 1068797) (by norm_num)
theorem B1900083 : Blo 1899435 1900083 := bstep (se 1 (by rfl) ⟨1425062, by rfl⟩ : syracuseStep 1900083 = 2850125) B2850125
theorem B4275197 : Blo 1899435 4275197 := bbase (se 3 (by rfl) ⟨801599, by rfl⟩ : syracuseStep 4275197 = 1603199) (by norm_num)
theorem B2850131 : Blo 1899435 2850131 := bstep (se 1 (by rfl) ⟨2137598, by rfl⟩ : syracuseStep 2850131 = 4275197) B4275197
theorem B1900087 : Blo 1899435 1900087 := bstep (se 1 (by rfl) ⟨1425065, by rfl⟩ : syracuseStep 1900087 = 2850131) B2850131
theorem B3206405 : Blo 1899435 3206405 := bbase (se 4 (by rfl) ⟨300600, by rfl⟩ : syracuseStep 3206405 = 601201) (by norm_num)
theorem B2137603 : Blo 1899435 2137603 := bstep (se 1 (by rfl) ⟨1603202, by rfl⟩ : syracuseStep 2137603 = 3206405) B3206405
theorem B2850137 : Blo 1899435 2850137 := bstep (se 2 (by rfl) ⟨1068801, by rfl⟩ : syracuseStep 2850137 = 2137603) B2137603
theorem B1900091 : Blo 1899435 1900091 := bstep (se 1 (by rfl) ⟨1425068, by rfl⟩ : syracuseStep 1900091 = 2850137) B2850137
theorem B14428853 : Blo 1899435 14428853 := bbase (se 5 (by rfl) ⟨676352, by rfl⟩ : syracuseStep 14428853 = 1352705) (by norm_num)
theorem B9619235 : Blo 1899435 9619235 := bstep (se 1 (by rfl) ⟨7214426, by rfl⟩ : syracuseStep 9619235 = 14428853) B14428853
theorem B6412823 : Blo 1899435 6412823 := bstep (se 1 (by rfl) ⟨4809617, by rfl⟩ : syracuseStep 6412823 = 9619235) B9619235
theorem B4275215 : Blo 1899435 4275215 := bstep (se 1 (by rfl) ⟨3206411, by rfl⟩ : syracuseStep 4275215 = 6412823) B6412823
theorem B2850143 : Blo 1899435 2850143 := bstep (se 1 (by rfl) ⟨2137607, by rfl⟩ : syracuseStep 2850143 = 4275215) B4275215
theorem B1900095 : Blo 1899435 1900095 := bstep (se 1 (by rfl) ⟨1425071, by rfl⟩ : syracuseStep 1900095 = 2850143) B2850143
theorem B2850149 : Blo 1899435 2850149 := bbase (se 4 (by rfl) ⟨267201, by rfl⟩ : syracuseStep 2850149 = 534403) (by norm_num)
theorem B1900099 : Blo 1899435 1900099 := bstep (se 1 (by rfl) ⟨1425074, by rfl⟩ : syracuseStep 1900099 = 2850149) B2850149
theorem B3607229 : Blo 1899435 3607229 := bbase (se 3 (by rfl) ⟨676355, by rfl⟩ : syracuseStep 3607229 = 1352711) (by norm_num)
theorem B2404819 : Blo 1899435 2404819 := bstep (se 1 (by rfl) ⟨1803614, by rfl⟩ : syracuseStep 2404819 = 3607229) B3607229
theorem B3206425 : Blo 1899435 3206425 := bstep (se 2 (by rfl) ⟨1202409, by rfl⟩ : syracuseStep 3206425 = 2404819) B2404819
theorem B4275233 : Blo 1899435 4275233 := bstep (se 2 (by rfl) ⟨1603212, by rfl⟩ : syracuseStep 4275233 = 3206425) B3206425
theorem B2850155 : Blo 1899435 2850155 := bstep (se 1 (by rfl) ⟨2137616, by rfl⟩ : syracuseStep 2850155 = 4275233) B4275233
theorem B1900103 : Blo 1899435 1900103 := bstep (se 1 (by rfl) ⟨1425077, by rfl⟩ : syracuseStep 1900103 = 2850155) B2850155
theorem B2137621 : Blo 1899435 2137621 := bbase (se 6 (by rfl) ⟨50100, by rfl⟩ : syracuseStep 2137621 = 100201) (by norm_num)
theorem B2850161 : Blo 1899435 2850161 := bstep (se 2 (by rfl) ⟨1068810, by rfl⟩ : syracuseStep 2850161 = 2137621) B2137621
theorem B1900107 : Blo 1899435 1900107 := bstep (se 1 (by rfl) ⟨1425080, by rfl⟩ : syracuseStep 1900107 = 2850161) B2850161
theorem B2404829 : Blo 1899435 2404829 := bbase (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) (by norm_num)
theorem B6412877 : Blo 1899435 6412877 := bstep (se 3 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 6412877 = 2404829) B2404829
theorem B4275251 : Blo 1899435 4275251 := bstep (se 1 (by rfl) ⟨3206438, by rfl⟩ : syracuseStep 4275251 = 6412877) B6412877
theorem B2850167 : Blo 1899435 2850167 := bstep (se 1 (by rfl) ⟨2137625, by rfl⟩ : syracuseStep 2850167 = 4275251) B4275251
theorem B1900111 : Blo 1899435 1900111 := bstep (se 1 (by rfl) ⟨1425083, by rfl⟩ : syracuseStep 1900111 = 2850167) B2850167
theorem B2850173 : Blo 1899435 2850173 := bbase (se 3 (by rfl) ⟨534407, by rfl⟩ : syracuseStep 2850173 = 1068815) (by norm_num)
theorem B1900115 : Blo 1899435 1900115 := bstep (se 1 (by rfl) ⟨1425086, by rfl⟩ : syracuseStep 1900115 = 2850173) B2850173
theorem B4275269 : Blo 1899435 4275269 := bbase (se 4 (by rfl) ⟨400806, by rfl⟩ : syracuseStep 4275269 = 801613) (by norm_num)
theorem B2850179 : Blo 1899435 2850179 := bstep (se 1 (by rfl) ⟨2137634, by rfl⟩ : syracuseStep 2850179 = 4275269) B4275269
theorem B1900119 : Blo 1899435 1900119 := bstep (se 1 (by rfl) ⟨1425089, by rfl⟩ : syracuseStep 1900119 = 2850179) B2850179
theorem B5410901 : Blo 1899435 5410901 := bbase (se 8 (by rfl) ⟨31704, by rfl⟩ : syracuseStep 5410901 = 63409) (by norm_num)
theorem B3607267 : Blo 1899435 3607267 := bstep (se 1 (by rfl) ⟨2705450, by rfl⟩ : syracuseStep 3607267 = 5410901) B5410901
theorem B4809689 : Blo 1899435 4809689 := bstep (se 2 (by rfl) ⟨1803633, by rfl⟩ : syracuseStep 4809689 = 3607267) B3607267
theorem B3206459 : Blo 1899435 3206459 := bstep (se 1 (by rfl) ⟨2404844, by rfl⟩ : syracuseStep 3206459 = 4809689) B4809689
theorem B2137639 : Blo 1899435 2137639 := bstep (se 1 (by rfl) ⟨1603229, by rfl⟩ : syracuseStep 2137639 = 3206459) B3206459
theorem B2850185 : Blo 1899435 2850185 := bstep (se 2 (by rfl) ⟨1068819, by rfl⟩ : syracuseStep 2850185 = 2137639) B2137639
theorem B1900123 : Blo 1899435 1900123 := bstep (se 1 (by rfl) ⟨1425092, by rfl⟩ : syracuseStep 1900123 = 2850185) B2850185
theorem B9619397 : Blo 1899435 9619397 := bbase (se 4 (by rfl) ⟨901818, by rfl⟩ : syracuseStep 9619397 = 1803637) (by norm_num)
theorem B6412931 : Blo 1899435 6412931 := bstep (se 1 (by rfl) ⟨4809698, by rfl⟩ : syracuseStep 6412931 = 9619397) B9619397
theorem B4275287 : Blo 1899435 4275287 := bstep (se 1 (by rfl) ⟨3206465, by rfl⟩ : syracuseStep 4275287 = 6412931) B6412931
theorem B2850191 : Blo 1899435 2850191 := bstep (se 1 (by rfl) ⟨2137643, by rfl⟩ : syracuseStep 2850191 = 4275287) B4275287
theorem B1900127 : Blo 1899435 1900127 := bstep (se 1 (by rfl) ⟨1425095, by rfl⟩ : syracuseStep 1900127 = 2850191) B2850191
theorem B2850197 : Blo 1899435 2850197 := bbase (se 6 (by rfl) ⟨66801, by rfl⟩ : syracuseStep 2850197 = 133603) (by norm_num)
theorem B1900131 : Blo 1899435 1900131 := bstep (se 1 (by rfl) ⟨1425098, by rfl⟩ : syracuseStep 1900131 = 2850197) B2850197
theorem B4565477 : Blo 1899435 4565477 := bbase (se 4 (by rfl) ⟨428013, by rfl⟩ : syracuseStep 4565477 = 856027) (by norm_num)
theorem B3043651 : Blo 1899435 3043651 := bstep (se 1 (by rfl) ⟨2282738, by rfl⟩ : syracuseStep 3043651 = 4565477) B4565477
theorem B4058201 : Blo 1899435 4058201 := bstep (se 2 (by rfl) ⟨1521825, by rfl⟩ : syracuseStep 4058201 = 3043651) B3043651
theorem B10821869 : Blo 1899435 10821869 := bstep (se 3 (by rfl) ⟨2029100, by rfl⟩ : syracuseStep 10821869 = 4058201) B4058201
theorem B7214579 : Blo 1899435 7214579 := bstep (se 1 (by rfl) ⟨5410934, by rfl⟩ : syracuseStep 7214579 = 10821869) B10821869
theorem B4809719 : Blo 1899435 4809719 := bstep (se 1 (by rfl) ⟨3607289, by rfl⟩ : syracuseStep 4809719 = 7214579) B7214579
theorem B3206479 : Blo 1899435 3206479 := bstep (se 1 (by rfl) ⟨2404859, by rfl⟩ : syracuseStep 3206479 = 4809719) B4809719
theorem B4275305 : Blo 1899435 4275305 := bstep (se 2 (by rfl) ⟨1603239, by rfl⟩ : syracuseStep 4275305 = 3206479) B3206479
theorem B2850203 : Blo 1899435 2850203 := bstep (se 1 (by rfl) ⟨2137652, by rfl⟩ : syracuseStep 2850203 = 4275305) B4275305
theorem B1900135 : Blo 1899435 1900135 := bstep (se 1 (by rfl) ⟨1425101, by rfl⟩ : syracuseStep 1900135 = 2850203) B2850203
theorem B2137657 : Blo 1899435 2137657 := bbase (se 2 (by rfl) ⟨801621, by rfl⟩ : syracuseStep 2137657 = 1603243) (by norm_num)
theorem B2850209 : Blo 1899435 2850209 := bstep (se 2 (by rfl) ⟨1068828, by rfl⟩ : syracuseStep 2850209 = 2137657) B2137657
theorem B1900139 : Blo 1899435 1900139 := bstep (se 1 (by rfl) ⟨1425104, by rfl⟩ : syracuseStep 1900139 = 2850209) B2850209
theorem B2029109 : Blo 1899435 2029109 := bbase (se 5 (by rfl) ⟨95114, by rfl⟩ : syracuseStep 2029109 = 190229) (by norm_num)
theorem B5410957 : Blo 1899435 5410957 := bstep (se 3 (by rfl) ⟨1014554, by rfl⟩ : syracuseStep 5410957 = 2029109) B2029109
theorem B7214609 : Blo 1899435 7214609 := bstep (se 2 (by rfl) ⟨2705478, by rfl⟩ : syracuseStep 7214609 = 5410957) B5410957
theorem B4809739 : Blo 1899435 4809739 := bstep (se 1 (by rfl) ⟨3607304, by rfl⟩ : syracuseStep 4809739 = 7214609) B7214609
theorem B6412985 : Blo 1899435 6412985 := bstep (se 2 (by rfl) ⟨2404869, by rfl⟩ : syracuseStep 6412985 = 4809739) B4809739
theorem B4275323 : Blo 1899435 4275323 := bstep (se 1 (by rfl) ⟨3206492, by rfl⟩ : syracuseStep 4275323 = 6412985) B6412985
theorem B2850215 : Blo 1899435 2850215 := bstep (se 1 (by rfl) ⟨2137661, by rfl⟩ : syracuseStep 2850215 = 4275323) B4275323
theorem B1900143 : Blo 1899435 1900143 := bstep (se 1 (by rfl) ⟨1425107, by rfl⟩ : syracuseStep 1900143 = 2850215) B2850215
theorem B2850221 : Blo 1899435 2850221 := bbase (se 3 (by rfl) ⟨534416, by rfl⟩ : syracuseStep 2850221 = 1068833) (by norm_num)
theorem B1900147 : Blo 1899435 1900147 := bstep (se 1 (by rfl) ⟨1425110, by rfl⟩ : syracuseStep 1900147 = 2850221) B2850221
theorem B4275341 : Blo 1899435 4275341 := bbase (se 3 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 4275341 = 1603253) (by norm_num)
theorem B2850227 : Blo 1899435 2850227 := bstep (se 1 (by rfl) ⟨2137670, by rfl⟩ : syracuseStep 2850227 = 4275341) B4275341
theorem B1900151 : Blo 1899435 1900151 := bstep (se 1 (by rfl) ⟨1425113, by rfl⟩ : syracuseStep 1900151 = 2850227) B2850227
theorem B2404885 : Blo 1899435 2404885 := bbase (se 6 (by rfl) ⟨56364, by rfl⟩ : syracuseStep 2404885 = 112729) (by norm_num)
theorem B3206513 : Blo 1899435 3206513 := bstep (se 2 (by rfl) ⟨1202442, by rfl⟩ : syracuseStep 3206513 = 2404885) B2404885
theorem B2137675 : Blo 1899435 2137675 := bstep (se 1 (by rfl) ⟨1603256, by rfl⟩ : syracuseStep 2137675 = 3206513) B3206513
theorem B2850233 : Blo 1899435 2850233 := bstep (se 2 (by rfl) ⟨1068837, by rfl⟩ : syracuseStep 2850233 = 2137675) B2137675
theorem B1900155 : Blo 1899435 1900155 := bstep (se 1 (by rfl) ⟨1425116, by rfl⟩ : syracuseStep 1900155 = 2850233) B2850233
theorem B43878613 : Blo 1899435 43878613 := bbase (se 7 (by rfl) ⟨514202, by rfl⟩ : syracuseStep 43878613 = 1028405) (by norm_num)
theorem B58504817 : Blo 1899435 58504817 := bstep (se 2 (by rfl) ⟨21939306, by rfl⟩ : syracuseStep 58504817 = 43878613) B43878613
theorem B39003211 : Blo 1899435 39003211 := bstep (se 1 (by rfl) ⟨29252408, by rfl⟩ : syracuseStep 39003211 = 58504817) B58504817
theorem B52004281 : Blo 1899435 52004281 := bstep (se 2 (by rfl) ⟨19501605, by rfl⟩ : syracuseStep 52004281 = 39003211) B39003211
theorem B69339041 : Blo 1899435 69339041 := bstep (se 2 (by rfl) ⟨26002140, by rfl⟩ : syracuseStep 69339041 = 52004281) B52004281
theorem B46226027 : Blo 1899435 46226027 := bstep (se 1 (by rfl) ⟨34669520, by rfl⟩ : syracuseStep 46226027 = 69339041) B69339041
theorem B30817351 : Blo 1899435 30817351 := bstep (se 1 (by rfl) ⟨23113013, by rfl⟩ : syracuseStep 30817351 = 46226027) B46226027
theorem B41089801 : Blo 1899435 41089801 := bstep (se 2 (by rfl) ⟨15408675, by rfl⟩ : syracuseStep 41089801 = 30817351) B30817351
theorem B54786401 : Blo 1899435 54786401 := bstep (se 2 (by rfl) ⟨20544900, by rfl⟩ : syracuseStep 54786401 = 41089801) B41089801
theorem B36524267 : Blo 1899435 36524267 := bstep (se 1 (by rfl) ⟨27393200, by rfl⟩ : syracuseStep 36524267 = 54786401) B54786401
theorem B24349511 : Blo 1899435 24349511 := bstep (se 1 (by rfl) ⟨18262133, by rfl⟩ : syracuseStep 24349511 = 36524267) B36524267
theorem B16233007 : Blo 1899435 16233007 := bstep (se 1 (by rfl) ⟨12174755, by rfl⟩ : syracuseStep 16233007 = 24349511) B24349511
theorem B21644009 : Blo 1899435 21644009 := bstep (se 2 (by rfl) ⟨8116503, by rfl⟩ : syracuseStep 21644009 = 16233007) B16233007
theorem B14429339 : Blo 1899435 14429339 := bstep (se 1 (by rfl) ⟨10822004, by rfl⟩ : syracuseStep 14429339 = 21644009) B21644009
theorem B9619559 : Blo 1899435 9619559 := bstep (se 1 (by rfl) ⟨7214669, by rfl⟩ : syracuseStep 9619559 = 14429339) B14429339
theorem B6413039 : Blo 1899435 6413039 := bstep (se 1 (by rfl) ⟨4809779, by rfl⟩ : syracuseStep 6413039 = 9619559) B9619559
theorem B4275359 : Blo 1899435 4275359 := bstep (se 1 (by rfl) ⟨3206519, by rfl⟩ : syracuseStep 4275359 = 6413039) B6413039
theorem B2850239 : Blo 1899435 2850239 := bstep (se 1 (by rfl) ⟨2137679, by rfl⟩ : syracuseStep 2850239 = 4275359) B4275359
theorem B1900159 : Blo 1899435 1900159 := bstep (se 1 (by rfl) ⟨1425119, by rfl⟩ : syracuseStep 1900159 = 2850239) B2850239
theorem B2850245 : Blo 1899435 2850245 := bbase (se 4 (by rfl) ⟨267210, by rfl⟩ : syracuseStep 2850245 = 534421) (by norm_num)
theorem B1900163 : Blo 1899435 1900163 := bstep (se 1 (by rfl) ⟨1425122, by rfl⟩ : syracuseStep 1900163 = 2850245) B2850245
theorem B3206533 : Blo 1899435 3206533 := bbase (se 4 (by rfl) ⟨300612, by rfl⟩ : syracuseStep 3206533 = 601225) (by norm_num)
theorem B4275377 : Blo 1899435 4275377 := bstep (se 2 (by rfl) ⟨1603266, by rfl⟩ : syracuseStep 4275377 = 3206533) B3206533
theorem B2850251 : Blo 1899435 2850251 := bstep (se 1 (by rfl) ⟨2137688, by rfl⟩ : syracuseStep 2850251 = 4275377) B4275377
theorem B1900167 : Blo 1899435 1900167 := bstep (se 1 (by rfl) ⟨1425125, by rfl⟩ : syracuseStep 1900167 = 2850251) B2850251
theorem B2137693 : Blo 1899435 2137693 := bbase (se 3 (by rfl) ⟨400817, by rfl⟩ : syracuseStep 2137693 = 801635) (by norm_num)
theorem B2850257 : Blo 1899435 2850257 := bstep (se 2 (by rfl) ⟨1068846, by rfl⟩ : syracuseStep 2850257 = 2137693) B2137693
theorem B1900171 : Blo 1899435 1900171 := bstep (se 1 (by rfl) ⟨1425128, by rfl⟩ : syracuseStep 1900171 = 2850257) B2850257
theorem B6413093 : Blo 1899435 6413093 := bbase (se 4 (by rfl) ⟨601227, by rfl⟩ : syracuseStep 6413093 = 1202455) (by norm_num)
theorem B4275395 : Blo 1899435 4275395 := bstep (se 1 (by rfl) ⟨3206546, by rfl⟩ : syracuseStep 4275395 = 6413093) B6413093
theorem B2850263 : Blo 1899435 2850263 := bstep (se 1 (by rfl) ⟨2137697, by rfl⟩ : syracuseStep 2850263 = 4275395) B4275395
theorem B1900175 : Blo 1899435 1900175 := bstep (se 1 (by rfl) ⟨1425131, by rfl⟩ : syracuseStep 1900175 = 2850263) B2850263
theorem B2850269 : Blo 1899435 2850269 := bbase (se 3 (by rfl) ⟨534425, by rfl⟩ : syracuseStep 2850269 = 1068851) (by norm_num)
theorem B1900179 : Blo 1899435 1900179 := bstep (se 1 (by rfl) ⟨1425134, by rfl⟩ : syracuseStep 1900179 = 2850269) B2850269
theorem B4275413 : Blo 1899435 4275413 := bbase (se 7 (by rfl) ⟨50102, by rfl⟩ : syracuseStep 4275413 = 100205) (by norm_num)
theorem B2850275 : Blo 1899435 2850275 := bstep (se 1 (by rfl) ⟨2137706, by rfl⟩ : syracuseStep 2850275 = 4275413) B4275413
theorem B1900183 : Blo 1899435 1900183 := bstep (se 1 (by rfl) ⟨1425137, by rfl⟩ : syracuseStep 1900183 = 2850275) B2850275
theorem B2282801 : Blo 1899435 2282801 := bbase (se 2 (by rfl) ⟨856050, by rfl⟩ : syracuseStep 2282801 = 1712101) (by norm_num)
theorem B6087469 : Blo 1899435 6087469 := bstep (se 3 (by rfl) ⟨1141400, by rfl⟩ : syracuseStep 6087469 = 2282801) B2282801
theorem B8116625 : Blo 1899435 8116625 := bstep (se 2 (by rfl) ⟨3043734, by rfl⟩ : syracuseStep 8116625 = 6087469) B6087469
theorem B5411083 : Blo 1899435 5411083 := bstep (se 1 (by rfl) ⟨4058312, by rfl⟩ : syracuseStep 5411083 = 8116625) B8116625
theorem B7214777 : Blo 1899435 7214777 := bstep (se 2 (by rfl) ⟨2705541, by rfl⟩ : syracuseStep 7214777 = 5411083) B5411083
theorem B4809851 : Blo 1899435 4809851 := bstep (se 1 (by rfl) ⟨3607388, by rfl⟩ : syracuseStep 4809851 = 7214777) B7214777
theorem B3206567 : Blo 1899435 3206567 := bstep (se 1 (by rfl) ⟨2404925, by rfl⟩ : syracuseStep 3206567 = 4809851) B4809851
theorem B2137711 : Blo 1899435 2137711 := bstep (se 1 (by rfl) ⟨1603283, by rfl⟩ : syracuseStep 2137711 = 3206567) B3206567
theorem B2850281 : Blo 1899435 2850281 := bstep (se 2 (by rfl) ⟨1068855, by rfl⟩ : syracuseStep 2850281 = 2137711) B2137711
theorem B1900187 : Blo 1899435 1900187 := bstep (se 1 (by rfl) ⟨1425140, by rfl⟩ : syracuseStep 1900187 = 2850281) B2850281
theorem B9131221 : Blo 1899435 9131221 := bbase (se 7 (by rfl) ⟨107006, by rfl⟩ : syracuseStep 9131221 = 214013) (by norm_num)
theorem B12174961 : Blo 1899435 12174961 := bstep (se 2 (by rfl) ⟨4565610, by rfl⟩ : syracuseStep 12174961 = 9131221) B9131221
theorem B16233281 : Blo 1899435 16233281 := bstep (se 2 (by rfl) ⟨6087480, by rfl⟩ : syracuseStep 16233281 = 12174961) B12174961
theorem B10822187 : Blo 1899435 10822187 := bstep (se 1 (by rfl) ⟨8116640, by rfl⟩ : syracuseStep 10822187 = 16233281) B16233281
theorem B7214791 : Blo 1899435 7214791 := bstep (se 1 (by rfl) ⟨5411093, by rfl⟩ : syracuseStep 7214791 = 10822187) B10822187
theorem B9619721 : Blo 1899435 9619721 := bstep (se 2 (by rfl) ⟨3607395, by rfl⟩ : syracuseStep 9619721 = 7214791) B7214791
theorem B6413147 : Blo 1899435 6413147 := bstep (se 1 (by rfl) ⟨4809860, by rfl⟩ : syracuseStep 6413147 = 9619721) B9619721
theorem B4275431 : Blo 1899435 4275431 := bstep (se 1 (by rfl) ⟨3206573, by rfl⟩ : syracuseStep 4275431 = 6413147) B6413147
theorem B2850287 : Blo 1899435 2850287 := bstep (se 1 (by rfl) ⟨2137715, by rfl⟩ : syracuseStep 2850287 = 4275431) B4275431
theorem B1900191 : Blo 1899435 1900191 := bstep (se 1 (by rfl) ⟨1425143, by rfl⟩ : syracuseStep 1900191 = 2850287) B2850287
theorem B2850293 : Blo 1899435 2850293 := bbase (se 5 (by rfl) ⟨133607, by rfl⟩ : syracuseStep 2850293 = 267215) (by norm_num)
theorem B1900195 : Blo 1899435 1900195 := bstep (se 1 (by rfl) ⟨1425146, by rfl⟩ : syracuseStep 1900195 = 2850293) B2850293
theorem B2029169 : Blo 1899435 2029169 := bbase (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) (by norm_num)
theorem B5411117 : Blo 1899435 5411117 := bstep (se 3 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 5411117 = 2029169) B2029169
theorem B3607411 : Blo 1899435 3607411 := bstep (se 1 (by rfl) ⟨2705558, by rfl⟩ : syracuseStep 3607411 = 5411117) B5411117
theorem B4809881 : Blo 1899435 4809881 := bstep (se 2 (by rfl) ⟨1803705, by rfl⟩ : syracuseStep 4809881 = 3607411) B3607411
theorem B3206587 : Blo 1899435 3206587 := bstep (se 1 (by rfl) ⟨2404940, by rfl⟩ : syracuseStep 3206587 = 4809881) B4809881
theorem B4275449 : Blo 1899435 4275449 := bstep (se 2 (by rfl) ⟨1603293, by rfl⟩ : syracuseStep 4275449 = 3206587) B3206587
theorem B2850299 : Blo 1899435 2850299 := bstep (se 1 (by rfl) ⟨2137724, by rfl⟩ : syracuseStep 2850299 = 4275449) B4275449
theorem B1900199 : Blo 1899435 1900199 := bstep (se 1 (by rfl) ⟨1425149, by rfl⟩ : syracuseStep 1900199 = 2850299) B2850299
theorem B2137729 : Blo 1899435 2137729 := bbase (se 2 (by rfl) ⟨801648, by rfl⟩ : syracuseStep 2137729 = 1603297) (by norm_num)
theorem B2850305 : Blo 1899435 2850305 := bstep (se 2 (by rfl) ⟨1068864, by rfl⟩ : syracuseStep 2850305 = 2137729) B2137729
theorem B1900203 : Blo 1899435 1900203 := bstep (se 1 (by rfl) ⟨1425152, by rfl⟩ : syracuseStep 1900203 = 2850305) B2850305
theorem B4809901 : Blo 1899435 4809901 := bbase (se 3 (by rfl) ⟨901856, by rfl⟩ : syracuseStep 4809901 = 1803713) (by norm_num)
theorem B6413201 : Blo 1899435 6413201 := bstep (se 2 (by rfl) ⟨2404950, by rfl⟩ : syracuseStep 6413201 = 4809901) B4809901
theorem B4275467 : Blo 1899435 4275467 := bstep (se 1 (by rfl) ⟨3206600, by rfl⟩ : syracuseStep 4275467 = 6413201) B6413201
theorem B2850311 : Blo 1899435 2850311 := bstep (se 1 (by rfl) ⟨2137733, by rfl⟩ : syracuseStep 2850311 = 4275467) B4275467
theorem B1900207 : Blo 1899435 1900207 := bstep (se 1 (by rfl) ⟨1425155, by rfl⟩ : syracuseStep 1900207 = 2850311) B2850311
theorem B2850317 : Blo 1899435 2850317 := bbase (se 3 (by rfl) ⟨534434, by rfl⟩ : syracuseStep 2850317 = 1068869) (by norm_num)
theorem B1900211 : Blo 1899435 1900211 := bstep (se 1 (by rfl) ⟨1425158, by rfl⟩ : syracuseStep 1900211 = 2850317) B2850317
theorem B4275485 : Blo 1899435 4275485 := bbase (se 3 (by rfl) ⟨801653, by rfl⟩ : syracuseStep 4275485 = 1603307) (by norm_num)
theorem B2850323 : Blo 1899435 2850323 := bstep (se 1 (by rfl) ⟨2137742, by rfl⟩ : syracuseStep 2850323 = 4275485) B4275485
theorem B1900215 : Blo 1899435 1900215 := bstep (se 1 (by rfl) ⟨1425161, by rfl⟩ : syracuseStep 1900215 = 2850323) B2850323
theorem B3206621 : Blo 1899435 3206621 := bbase (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) (by norm_num)
theorem B2137747 : Blo 1899435 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B2850329 : Blo 1899435 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B1900219 : Blo 1899435 1900219 := bstep (se 1 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 1900219 = 2850329) B2850329
theorem B5485013 : Blo 1899435 5485013 := bbase (se 7 (by rfl) ⟨64277, by rfl⟩ : syracuseStep 5485013 = 128555) (by norm_num)
theorem B3656675 : Blo 1899435 3656675 := bstep (se 1 (by rfl) ⟨2742506, by rfl⟩ : syracuseStep 3656675 = 5485013) B5485013
theorem B9751133 : Blo 1899435 9751133 := bstep (se 3 (by rfl) ⟨1828337, by rfl⟩ : syracuseStep 9751133 = 3656675) B3656675
theorem B6500755 : Blo 1899435 6500755 := bstep (se 1 (by rfl) ⟨4875566, by rfl⟩ : syracuseStep 6500755 = 9751133) B9751133
theorem B34670693 : Blo 1899435 34670693 := bstep (se 4 (by rfl) ⟨3250377, by rfl⟩ : syracuseStep 34670693 = 6500755) B6500755
theorem B23113795 : Blo 1899435 23113795 := bstep (se 1 (by rfl) ⟨17335346, by rfl⟩ : syracuseStep 23113795 = 34670693) B34670693
theorem B30818393 : Blo 1899435 30818393 := bstep (se 2 (by rfl) ⟨11556897, by rfl⟩ : syracuseStep 30818393 = 23113795) B23113795
theorem B20545595 : Blo 1899435 20545595 := bstep (se 1 (by rfl) ⟨15409196, by rfl⟩ : syracuseStep 20545595 = 30818393) B30818393
theorem B13697063 : Blo 1899435 13697063 := bstep (se 1 (by rfl) ⟨10272797, by rfl⟩ : syracuseStep 13697063 = 20545595) B20545595
theorem B9131375 : Blo 1899435 9131375 := bstep (se 1 (by rfl) ⟨6848531, by rfl⟩ : syracuseStep 9131375 = 13697063) B13697063
theorem B6087583 : Blo 1899435 6087583 := bstep (se 1 (by rfl) ⟨4565687, by rfl⟩ : syracuseStep 6087583 = 9131375) B9131375
theorem B8116777 : Blo 1899435 8116777 := bstep (se 2 (by rfl) ⟨3043791, by rfl⟩ : syracuseStep 8116777 = 6087583) B6087583
theorem B10822369 : Blo 1899435 10822369 := bstep (se 2 (by rfl) ⟨4058388, by rfl⟩ : syracuseStep 10822369 = 8116777) B8116777
theorem B14429825 : Blo 1899435 14429825 := bstep (se 2 (by rfl) ⟨5411184, by rfl⟩ : syracuseStep 14429825 = 10822369) B10822369
theorem B9619883 : Blo 1899435 9619883 := bstep (se 1 (by rfl) ⟨7214912, by rfl⟩ : syracuseStep 9619883 = 14429825) B14429825
theorem B6413255 : Blo 1899435 6413255 := bstep (se 1 (by rfl) ⟨4809941, by rfl⟩ : syracuseStep 6413255 = 9619883) B9619883
theorem B4275503 : Blo 1899435 4275503 := bstep (se 1 (by rfl) ⟨3206627, by rfl⟩ : syracuseStep 4275503 = 6413255) B6413255
theorem B2850335 : Blo 1899435 2850335 := bstep (se 1 (by rfl) ⟨2137751, by rfl⟩ : syracuseStep 2850335 = 4275503) B4275503
theorem B1900223 : Blo 1899435 1900223 := bstep (se 1 (by rfl) ⟨1425167, by rfl⟩ : syracuseStep 1900223 = 2850335) B2850335
theorem B2850341 : Blo 1899435 2850341 := bbase (se 4 (by rfl) ⟨267219, by rfl⟩ : syracuseStep 2850341 = 534439) (by norm_num)
theorem B1900227 : Blo 1899435 1900227 := bstep (se 1 (by rfl) ⟨1425170, by rfl⟩ : syracuseStep 1900227 = 2850341) B2850341
theorem B2404981 : Blo 1899435 2404981 := bbase (se 5 (by rfl) ⟨112733, by rfl⟩ : syracuseStep 2404981 = 225467) (by norm_num)
theorem B3206641 : Blo 1899435 3206641 := bstep (se 2 (by rfl) ⟨1202490, by rfl⟩ : syracuseStep 3206641 = 2404981) B2404981
theorem B4275521 : Blo 1899435 4275521 := bstep (se 2 (by rfl) ⟨1603320, by rfl⟩ : syracuseStep 4275521 = 3206641) B3206641
theorem B2850347 : Blo 1899435 2850347 := bstep (se 1 (by rfl) ⟨2137760, by rfl⟩ : syracuseStep 2850347 = 4275521) B4275521
theorem B1900231 : Blo 1899435 1900231 := bstep (se 1 (by rfl) ⟨1425173, by rfl⟩ : syracuseStep 1900231 = 2850347) B2850347
theorem B2137765 : Blo 1899435 2137765 := bbase (se 4 (by rfl) ⟨200415, by rfl⟩ : syracuseStep 2137765 = 400831) (by norm_num)
theorem B2850353 : Blo 1899435 2850353 := bstep (se 2 (by rfl) ⟨1068882, by rfl⟩ : syracuseStep 2850353 = 2137765) B2137765
theorem B1900235 : Blo 1899435 1900235 := bstep (se 1 (by rfl) ⟨1425176, by rfl⟩ : syracuseStep 1900235 = 2850353) B2850353
theorem B8227589 : Blo 1899435 8227589 := bbase (se 4 (by rfl) ⟨771336, by rfl⟩ : syracuseStep 8227589 = 1542673) (by norm_num)
theorem B21940237 : Blo 1899435 21940237 := bstep (se 3 (by rfl) ⟨4113794, by rfl⟩ : syracuseStep 21940237 = 8227589) B8227589
theorem B29253649 : Blo 1899435 29253649 := bstep (se 2 (by rfl) ⟨10970118, by rfl⟩ : syracuseStep 29253649 = 21940237) B21940237
theorem B39004865 : Blo 1899435 39004865 := bstep (se 2 (by rfl) ⟨14626824, by rfl⟩ : syracuseStep 39004865 = 29253649) B29253649
theorem B26003243 : Blo 1899435 26003243 := bstep (se 1 (by rfl) ⟨19502432, by rfl⟩ : syracuseStep 26003243 = 39004865) B39004865
theorem B17335495 : Blo 1899435 17335495 := bstep (se 1 (by rfl) ⟨13001621, by rfl⟩ : syracuseStep 17335495 = 26003243) B26003243
theorem B23113993 : Blo 1899435 23113993 := bstep (se 2 (by rfl) ⟨8667747, by rfl⟩ : syracuseStep 23113993 = 17335495) B17335495
theorem B30818657 : Blo 1899435 30818657 := bstep (se 2 (by rfl) ⟨11556996, by rfl⟩ : syracuseStep 30818657 = 23113993) B23113993
theorem B20545771 : Blo 1899435 20545771 := bstep (se 1 (by rfl) ⟨15409328, by rfl⟩ : syracuseStep 20545771 = 30818657) B30818657
theorem B27394361 : Blo 1899435 27394361 := bstep (se 2 (by rfl) ⟨10272885, by rfl⟩ : syracuseStep 27394361 = 20545771) B20545771
theorem B18262907 : Blo 1899435 18262907 := bstep (se 1 (by rfl) ⟨13697180, by rfl⟩ : syracuseStep 18262907 = 27394361) B27394361
theorem B12175271 : Blo 1899435 12175271 := bstep (se 1 (by rfl) ⟨9131453, by rfl⟩ : syracuseStep 12175271 = 18262907) B18262907
theorem B8116847 : Blo 1899435 8116847 := bstep (se 1 (by rfl) ⟨6087635, by rfl⟩ : syracuseStep 8116847 = 12175271) B12175271
theorem B5411231 : Blo 1899435 5411231 := bstep (se 1 (by rfl) ⟨4058423, by rfl⟩ : syracuseStep 5411231 = 8116847) B8116847
theorem B3607487 : Blo 1899435 3607487 := bstep (se 1 (by rfl) ⟨2705615, by rfl⟩ : syracuseStep 3607487 = 5411231) B5411231
theorem B2404991 : Blo 1899435 2404991 := bstep (se 1 (by rfl) ⟨1803743, by rfl⟩ : syracuseStep 2404991 = 3607487) B3607487
theorem B6413309 : Blo 1899435 6413309 := bstep (se 3 (by rfl) ⟨1202495, by rfl⟩ : syracuseStep 6413309 = 2404991) B2404991
theorem B4275539 : Blo 1899435 4275539 := bstep (se 1 (by rfl) ⟨3206654, by rfl⟩ : syracuseStep 4275539 = 6413309) B6413309
theorem B2850359 : Blo 1899435 2850359 := bstep (se 1 (by rfl) ⟨2137769, by rfl⟩ : syracuseStep 2850359 = 4275539) B4275539
theorem B1900239 : Blo 1899435 1900239 := bstep (se 1 (by rfl) ⟨1425179, by rfl⟩ : syracuseStep 1900239 = 2850359) B2850359
theorem B2850365 : Blo 1899435 2850365 := bbase (se 3 (by rfl) ⟨534443, by rfl⟩ : syracuseStep 2850365 = 1068887) (by norm_num)
theorem B1900243 : Blo 1899435 1900243 := bstep (se 1 (by rfl) ⟨1425182, by rfl⟩ : syracuseStep 1900243 = 2850365) B2850365
theorem B4275557 : Blo 1899435 4275557 := bbase (se 4 (by rfl) ⟨400833, by rfl⟩ : syracuseStep 4275557 = 801667) (by norm_num)
theorem B2850371 : Blo 1899435 2850371 := bstep (se 1 (by rfl) ⟨2137778, by rfl⟩ : syracuseStep 2850371 = 4275557) B4275557
theorem B1900247 : Blo 1899435 1900247 := bstep (se 1 (by rfl) ⟨1425185, by rfl⟩ : syracuseStep 1900247 = 2850371) B2850371
theorem B4810013 : Blo 1899435 4810013 := bbase (se 3 (by rfl) ⟨901877, by rfl⟩ : syracuseStep 4810013 = 1803755) (by norm_num)
theorem B3206675 : Blo 1899435 3206675 := bstep (se 1 (by rfl) ⟨2405006, by rfl⟩ : syracuseStep 3206675 = 4810013) B4810013
theorem B2137783 : Blo 1899435 2137783 := bstep (se 1 (by rfl) ⟨1603337, by rfl⟩ : syracuseStep 2137783 = 3206675) B3206675
theorem B2850377 : Blo 1899435 2850377 := bstep (se 2 (by rfl) ⟨1068891, by rfl⟩ : syracuseStep 2850377 = 2137783) B2137783
theorem B1900251 : Blo 1899435 1900251 := bstep (se 1 (by rfl) ⟨1425188, by rfl⟩ : syracuseStep 1900251 = 2850377) B2850377
theorem B3607517 : Blo 1899435 3607517 := bbase (se 3 (by rfl) ⟨676409, by rfl⟩ : syracuseStep 3607517 = 1352819) (by norm_num)
theorem B9620045 : Blo 1899435 9620045 := bstep (se 3 (by rfl) ⟨1803758, by rfl⟩ : syracuseStep 9620045 = 3607517) B3607517
theorem B6413363 : Blo 1899435 6413363 := bstep (se 1 (by rfl) ⟨4810022, by rfl⟩ : syracuseStep 6413363 = 9620045) B9620045
theorem B4275575 : Blo 1899435 4275575 := bstep (se 1 (by rfl) ⟨3206681, by rfl⟩ : syracuseStep 4275575 = 6413363) B6413363
theorem B2850383 : Blo 1899435 2850383 := bstep (se 1 (by rfl) ⟨2137787, by rfl⟩ : syracuseStep 2850383 = 4275575) B4275575
theorem B1900255 : Blo 1899435 1900255 := bstep (se 1 (by rfl) ⟨1425191, by rfl⟩ : syracuseStep 1900255 = 2850383) B2850383
theorem B2850389 : Blo 1899435 2850389 := bbase (se 8 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 2850389 = 33403) (by norm_num)
theorem B1900259 : Blo 1899435 1900259 := bstep (se 1 (by rfl) ⟨1425194, by rfl⟩ : syracuseStep 1900259 = 2850389) B2850389
theorem B8116949 : Blo 1899435 8116949 := bbase (se 7 (by rfl) ⟨95120, by rfl⟩ : syracuseStep 8116949 = 190241) (by norm_num)
theorem B5411299 : Blo 1899435 5411299 := bstep (se 1 (by rfl) ⟨4058474, by rfl⟩ : syracuseStep 5411299 = 8116949) B8116949
theorem B7215065 : Blo 1899435 7215065 := bstep (se 2 (by rfl) ⟨2705649, by rfl⟩ : syracuseStep 7215065 = 5411299) B5411299
theorem B4810043 : Blo 1899435 4810043 := bstep (se 1 (by rfl) ⟨3607532, by rfl⟩ : syracuseStep 4810043 = 7215065) B7215065
theorem B3206695 : Blo 1899435 3206695 := bstep (se 1 (by rfl) ⟨2405021, by rfl⟩ : syracuseStep 3206695 = 4810043) B4810043
theorem B4275593 : Blo 1899435 4275593 := bstep (se 2 (by rfl) ⟨1603347, by rfl⟩ : syracuseStep 4275593 = 3206695) B3206695
theorem B2850395 : Blo 1899435 2850395 := bstep (se 1 (by rfl) ⟨2137796, by rfl⟩ : syracuseStep 2850395 = 4275593) B4275593
theorem B1900263 : Blo 1899435 1900263 := bstep (se 1 (by rfl) ⟨1425197, by rfl⟩ : syracuseStep 1900263 = 2850395) B2850395
theorem B2137801 : Blo 1899435 2137801 := bbase (se 2 (by rfl) ⟨801675, by rfl⟩ : syracuseStep 2137801 = 1603351) (by norm_num)
theorem B2850401 : Blo 1899435 2850401 := bstep (se 2 (by rfl) ⟨1068900, by rfl⟩ : syracuseStep 2850401 = 2137801) B2137801
theorem B1900267 : Blo 1899435 1900267 := bstep (se 1 (by rfl) ⟨1425200, by rfl⟩ : syracuseStep 1900267 = 2850401) B2850401
theorem B3852397 : Blo 1899435 3852397 := bbase (se 3 (by rfl) ⟨722324, by rfl⟩ : syracuseStep 3852397 = 1444649) (by norm_num)
theorem B5136529 : Blo 1899435 5136529 := bstep (se 2 (by rfl) ⟨1926198, by rfl⟩ : syracuseStep 5136529 = 3852397) B3852397
theorem B6848705 : Blo 1899435 6848705 := bstep (se 2 (by rfl) ⟨2568264, by rfl⟩ : syracuseStep 6848705 = 5136529) B5136529
theorem B4565803 : Blo 1899435 4565803 := bstep (se 1 (by rfl) ⟨3424352, by rfl⟩ : syracuseStep 4565803 = 6848705) B6848705
theorem B6087737 : Blo 1899435 6087737 := bstep (se 2 (by rfl) ⟨2282901, by rfl⟩ : syracuseStep 6087737 = 4565803) B4565803
theorem B16233965 : Blo 1899435 16233965 := bstep (se 3 (by rfl) ⟨3043868, by rfl⟩ : syracuseStep 16233965 = 6087737) B6087737
theorem B10822643 : Blo 1899435 10822643 := bstep (se 1 (by rfl) ⟨8116982, by rfl⟩ : syracuseStep 10822643 = 16233965) B16233965
theorem B7215095 : Blo 1899435 7215095 := bstep (se 1 (by rfl) ⟨5411321, by rfl⟩ : syracuseStep 7215095 = 10822643) B10822643
theorem B4810063 : Blo 1899435 4810063 := bstep (se 1 (by rfl) ⟨3607547, by rfl⟩ : syracuseStep 4810063 = 7215095) B7215095
theorem B6413417 : Blo 1899435 6413417 := bstep (se 2 (by rfl) ⟨2405031, by rfl⟩ : syracuseStep 6413417 = 4810063) B4810063
theorem B4275611 : Blo 1899435 4275611 := bstep (se 1 (by rfl) ⟨3206708, by rfl⟩ : syracuseStep 4275611 = 6413417) B6413417
theorem B2850407 : Blo 1899435 2850407 := bstep (se 1 (by rfl) ⟨2137805, by rfl⟩ : syracuseStep 2850407 = 4275611) B4275611
theorem B1900271 : Blo 1899435 1900271 := bstep (se 1 (by rfl) ⟨1425203, by rfl⟩ : syracuseStep 1900271 = 2850407) B2850407
theorem B2850413 : Blo 1899435 2850413 := bbase (se 3 (by rfl) ⟨534452, by rfl⟩ : syracuseStep 2850413 = 1068905) (by norm_num)
theorem B1900275 : Blo 1899435 1900275 := bstep (se 1 (by rfl) ⟨1425206, by rfl⟩ : syracuseStep 1900275 = 2850413) B2850413
theorem B4275629 : Blo 1899435 4275629 := bbase (se 3 (by rfl) ⟨801680, by rfl⟩ : syracuseStep 4275629 = 1603361) (by norm_num)
theorem B2850419 : Blo 1899435 2850419 := bstep (se 1 (by rfl) ⟨2137814, by rfl⟩ : syracuseStep 2850419 = 4275629) B4275629
theorem B1900279 : Blo 1899435 1900279 := bstep (se 1 (by rfl) ⟨1425209, by rfl⟩ : syracuseStep 1900279 = 2850419) B2850419
theorem B2282917 : Blo 1899435 2282917 := bbase (se 4 (by rfl) ⟨214023, by rfl⟩ : syracuseStep 2282917 = 428047) (by norm_num)
theorem B3043889 : Blo 1899435 3043889 := bstep (se 2 (by rfl) ⟨1141458, by rfl⟩ : syracuseStep 3043889 = 2282917) B2282917
theorem B2029259 : Blo 1899435 2029259 := bstep (se 1 (by rfl) ⟨1521944, by rfl⟩ : syracuseStep 2029259 = 3043889) B3043889
theorem B5411357 : Blo 1899435 5411357 := bstep (se 3 (by rfl) ⟨1014629, by rfl⟩ : syracuseStep 5411357 = 2029259) B2029259
theorem B3607571 : Blo 1899435 3607571 := bstep (se 1 (by rfl) ⟨2705678, by rfl⟩ : syracuseStep 3607571 = 5411357) B5411357
theorem B2405047 : Blo 1899435 2405047 := bstep (se 1 (by rfl) ⟨1803785, by rfl⟩ : syracuseStep 2405047 = 3607571) B3607571
theorem B3206729 : Blo 1899435 3206729 := bstep (se 2 (by rfl) ⟨1202523, by rfl⟩ : syracuseStep 3206729 = 2405047) B2405047
theorem B2137819 : Blo 1899435 2137819 := bstep (se 1 (by rfl) ⟨1603364, by rfl⟩ : syracuseStep 2137819 = 3206729) B3206729
theorem B2850425 : Blo 1899435 2850425 := bstep (se 2 (by rfl) ⟨1068909, by rfl⟩ : syracuseStep 2850425 = 2137819) B2137819
theorem B1900283 : Blo 1899435 1900283 := bstep (se 1 (by rfl) ⟨1425212, by rfl⟩ : syracuseStep 1900283 = 2850425) B2850425
theorem B14073845 : Blo 1899435 14073845 := bbase (se 5 (by rfl) ⟨659711, by rfl⟩ : syracuseStep 14073845 = 1319423) (by norm_num)
theorem B37530253 : Blo 1899435 37530253 := bstep (se 3 (by rfl) ⟨7036922, by rfl⟩ : syracuseStep 37530253 = 14073845) B14073845
theorem B50040337 : Blo 1899435 50040337 := bstep (se 2 (by rfl) ⟨18765126, by rfl⟩ : syracuseStep 50040337 = 37530253) B37530253
theorem B66720449 : Blo 1899435 66720449 := bstep (se 2 (by rfl) ⟨25020168, by rfl⟩ : syracuseStep 66720449 = 50040337) B50040337
theorem B44480299 : Blo 1899435 44480299 := bstep (se 1 (by rfl) ⟨33360224, by rfl⟩ : syracuseStep 44480299 = 66720449) B66720449
theorem B59307065 : Blo 1899435 59307065 := bstep (se 2 (by rfl) ⟨22240149, by rfl⟩ : syracuseStep 59307065 = 44480299) B44480299
theorem B39538043 : Blo 1899435 39538043 := bstep (se 1 (by rfl) ⟨29653532, by rfl⟩ : syracuseStep 39538043 = 59307065) B59307065
theorem B26358695 : Blo 1899435 26358695 := bstep (se 1 (by rfl) ⟨19769021, by rfl⟩ : syracuseStep 26358695 = 39538043) B39538043
theorem B17572463 : Blo 1899435 17572463 := bstep (se 1 (by rfl) ⟨13179347, by rfl⟩ : syracuseStep 17572463 = 26358695) B26358695
theorem B11714975 : Blo 1899435 11714975 := bstep (se 1 (by rfl) ⟨8786231, by rfl⟩ : syracuseStep 11714975 = 17572463) B17572463
theorem B7809983 : Blo 1899435 7809983 := bstep (se 1 (by rfl) ⟨5857487, by rfl⟩ : syracuseStep 7809983 = 11714975) B11714975
theorem B5206655 : Blo 1899435 5206655 := bstep (se 1 (by rfl) ⟨3904991, by rfl⟩ : syracuseStep 5206655 = 7809983) B7809983
theorem B3471103 : Blo 1899435 3471103 := bstep (se 1 (by rfl) ⟨2603327, by rfl⟩ : syracuseStep 3471103 = 5206655) B5206655
theorem B4628137 : Blo 1899435 4628137 := bstep (se 2 (by rfl) ⟨1735551, by rfl⟩ : syracuseStep 4628137 = 3471103) B3471103
theorem B6170849 : Blo 1899435 6170849 := bstep (se 2 (by rfl) ⟨2314068, by rfl⟩ : syracuseStep 6170849 = 4628137) B4628137
theorem B4113899 : Blo 1899435 4113899 := bstep (se 1 (by rfl) ⟨3085424, by rfl⟩ : syracuseStep 4113899 = 6170849) B6170849
theorem B2742599 : Blo 1899435 2742599 := bstep (se 1 (by rfl) ⟨2056949, by rfl⟩ : syracuseStep 2742599 = 4113899) B4113899
theorem B7313597 : Blo 1899435 7313597 := bstep (se 3 (by rfl) ⟨1371299, by rfl⟩ : syracuseStep 7313597 = 2742599) B2742599
theorem B4875731 : Blo 1899435 4875731 := bstep (se 1 (by rfl) ⟨3656798, by rfl⟩ : syracuseStep 4875731 = 7313597) B7313597
theorem B3250487 : Blo 1899435 3250487 := bstep (se 1 (by rfl) ⟨2437865, by rfl⟩ : syracuseStep 3250487 = 4875731) B4875731
theorem B2166991 : Blo 1899435 2166991 := bstep (se 1 (by rfl) ⟨1625243, by rfl⟩ : syracuseStep 2166991 = 3250487) B3250487
theorem B11557285 : Blo 1899435 11557285 := bstep (se 4 (by rfl) ⟨1083495, by rfl⟩ : syracuseStep 11557285 = 2166991) B2166991
theorem B61638853 : Blo 1899435 61638853 := bstep (se 4 (by rfl) ⟨5778642, by rfl⟩ : syracuseStep 61638853 = 11557285) B11557285
theorem B82185137 : Blo 1899435 82185137 := bstep (se 2 (by rfl) ⟨30819426, by rfl⟩ : syracuseStep 82185137 = 61638853) B61638853
theorem B54790091 : Blo 1899435 54790091 := bstep (se 1 (by rfl) ⟨41092568, by rfl⟩ : syracuseStep 54790091 = 82185137) B82185137
theorem B36526727 : Blo 1899435 36526727 := bstep (se 1 (by rfl) ⟨27395045, by rfl⟩ : syracuseStep 36526727 = 54790091) B54790091
theorem B24351151 : Blo 1899435 24351151 := bstep (se 1 (by rfl) ⟨18263363, by rfl⟩ : syracuseStep 24351151 = 36526727) B36526727
theorem B32468201 : Blo 1899435 32468201 := bstep (se 2 (by rfl) ⟨12175575, by rfl⟩ : syracuseStep 32468201 = 24351151) B24351151
theorem B21645467 : Blo 1899435 21645467 := bstep (se 1 (by rfl) ⟨16234100, by rfl⟩ : syracuseStep 21645467 = 32468201) B32468201
theorem B14430311 : Blo 1899435 14430311 := bstep (se 1 (by rfl) ⟨10822733, by rfl⟩ : syracuseStep 14430311 = 21645467) B21645467
theorem B9620207 : Blo 1899435 9620207 := bstep (se 1 (by rfl) ⟨7215155, by rfl⟩ : syracuseStep 9620207 = 14430311) B14430311
theorem B6413471 : Blo 1899435 6413471 := bstep (se 1 (by rfl) ⟨4810103, by rfl⟩ : syracuseStep 6413471 = 9620207) B9620207
theorem B4275647 : Blo 1899435 4275647 := bstep (se 1 (by rfl) ⟨3206735, by rfl⟩ : syracuseStep 4275647 = 6413471) B6413471
theorem B2850431 : Blo 1899435 2850431 := bstep (se 1 (by rfl) ⟨2137823, by rfl⟩ : syracuseStep 2850431 = 4275647) B4275647
theorem B1900287 : Blo 1899435 1900287 := bstep (se 1 (by rfl) ⟨1425215, by rfl⟩ : syracuseStep 1900287 = 2850431) B2850431
theorem B2850437 : Blo 1899435 2850437 := bbase (se 4 (by rfl) ⟨267228, by rfl⟩ : syracuseStep 2850437 = 534457) (by norm_num)
theorem B1900291 : Blo 1899435 1900291 := bstep (se 1 (by rfl) ⟨1425218, by rfl⟩ : syracuseStep 1900291 = 2850437) B2850437
theorem B3206749 : Blo 1899435 3206749 := bbase (se 3 (by rfl) ⟨601265, by rfl⟩ : syracuseStep 3206749 = 1202531) (by norm_num)
theorem B4275665 : Blo 1899435 4275665 := bstep (se 2 (by rfl) ⟨1603374, by rfl⟩ : syracuseStep 4275665 = 3206749) B3206749
theorem B2850443 : Blo 1899435 2850443 := bstep (se 1 (by rfl) ⟨2137832, by rfl⟩ : syracuseStep 2850443 = 4275665) B4275665
theorem B1900295 : Blo 1899435 1900295 := bstep (se 1 (by rfl) ⟨1425221, by rfl⟩ : syracuseStep 1900295 = 2850443) B2850443
theorem B2137837 : Blo 1899435 2137837 := bbase (se 3 (by rfl) ⟨400844, by rfl⟩ : syracuseStep 2137837 = 801689) (by norm_num)
theorem B2850449 : Blo 1899435 2850449 := bstep (se 2 (by rfl) ⟨1068918, by rfl⟩ : syracuseStep 2850449 = 2137837) B2137837
theorem B1900299 : Blo 1899435 1900299 := bstep (se 1 (by rfl) ⟨1425224, by rfl⟩ : syracuseStep 1900299 = 2850449) B2850449
theorem B6413525 : Blo 1899435 6413525 := bbase (se 7 (by rfl) ⟨75158, by rfl⟩ : syracuseStep 6413525 = 150317) (by norm_num)
theorem B4275683 : Blo 1899435 4275683 := bstep (se 1 (by rfl) ⟨3206762, by rfl⟩ : syracuseStep 4275683 = 6413525) B6413525
theorem B2850455 : Blo 1899435 2850455 := bstep (se 1 (by rfl) ⟨2137841, by rfl⟩ : syracuseStep 2850455 = 4275683) B4275683
theorem B1900303 : Blo 1899435 1900303 := bstep (se 1 (by rfl) ⟨1425227, by rfl⟩ : syracuseStep 1900303 = 2850455) B2850455
theorem B2850461 : Blo 1899435 2850461 := bbase (se 3 (by rfl) ⟨534461, by rfl⟩ : syracuseStep 2850461 = 1068923) (by norm_num)
theorem B1900307 : Blo 1899435 1900307 := bstep (se 1 (by rfl) ⟨1425230, by rfl⟩ : syracuseStep 1900307 = 2850461) B2850461
theorem B4275701 : Blo 1899435 4275701 := bbase (se 5 (by rfl) ⟨200423, by rfl⟩ : syracuseStep 4275701 = 400847) (by norm_num)
theorem B2850467 : Blo 1899435 2850467 := bstep (se 1 (by rfl) ⟨2137850, by rfl⟩ : syracuseStep 2850467 = 4275701) B4275701
theorem B1900311 : Blo 1899435 1900311 := bstep (se 1 (by rfl) ⟨1425233, by rfl⟩ : syracuseStep 1900311 = 2850467) B2850467
theorem B9510709 : Blo 1899435 9510709 := bbase (se 5 (by rfl) ⟨445814, by rfl⟩ : syracuseStep 9510709 = 891629) (by norm_num)
theorem B12680945 : Blo 1899435 12680945 := bstep (se 2 (by rfl) ⟨4755354, by rfl⟩ : syracuseStep 12680945 = 9510709) B9510709
theorem B8453963 : Blo 1899435 8453963 := bstep (se 1 (by rfl) ⟨6340472, by rfl⟩ : syracuseStep 8453963 = 12680945) B12680945
theorem B5635975 : Blo 1899435 5635975 := bstep (se 1 (by rfl) ⟨4226981, by rfl⟩ : syracuseStep 5635975 = 8453963) B8453963
theorem B7514633 : Blo 1899435 7514633 := bstep (se 2 (by rfl) ⟨2817987, by rfl⟩ : syracuseStep 7514633 = 5635975) B5635975
theorem B20039021 : Blo 1899435 20039021 := bstep (se 3 (by rfl) ⟨3757316, by rfl⟩ : syracuseStep 20039021 = 7514633) B7514633
theorem B13359347 : Blo 1899435 13359347 := bstep (se 1 (by rfl) ⟨10019510, by rfl⟩ : syracuseStep 13359347 = 20039021) B20039021
theorem B8906231 : Blo 1899435 8906231 := bstep (se 1 (by rfl) ⟨6679673, by rfl⟩ : syracuseStep 8906231 = 13359347) B13359347
theorem B23749949 : Blo 1899435 23749949 := bstep (se 3 (by rfl) ⟨4453115, by rfl⟩ : syracuseStep 23749949 = 8906231) B8906231
theorem B63333197 : Blo 1899435 63333197 := bstep (se 3 (by rfl) ⟨11874974, by rfl⟩ : syracuseStep 63333197 = 23749949) B23749949
theorem B42222131 : Blo 1899435 42222131 := bstep (se 1 (by rfl) ⟨31666598, by rfl⟩ : syracuseStep 42222131 = 63333197) B63333197
theorem B28148087 : Blo 1899435 28148087 := bstep (se 1 (by rfl) ⟨21111065, by rfl⟩ : syracuseStep 28148087 = 42222131) B42222131
theorem B18765391 : Blo 1899435 18765391 := bstep (se 1 (by rfl) ⟨14074043, by rfl⟩ : syracuseStep 18765391 = 28148087) B28148087
theorem B25020521 : Blo 1899435 25020521 := bstep (se 2 (by rfl) ⟨9382695, by rfl⟩ : syracuseStep 25020521 = 18765391) B18765391
theorem B16680347 : Blo 1899435 16680347 := bstep (se 1 (by rfl) ⟨12510260, by rfl⟩ : syracuseStep 16680347 = 25020521) B25020521
theorem B11120231 : Blo 1899435 11120231 := bstep (se 1 (by rfl) ⟨8340173, by rfl⟩ : syracuseStep 11120231 = 16680347) B16680347
theorem B7413487 : Blo 1899435 7413487 := bstep (se 1 (by rfl) ⟨5560115, by rfl⟩ : syracuseStep 7413487 = 11120231) B11120231
theorem B39538597 : Blo 1899435 39538597 := bstep (se 4 (by rfl) ⟨3706743, by rfl⟩ : syracuseStep 39538597 = 7413487) B7413487
theorem B52718129 : Blo 1899435 52718129 := bstep (se 2 (by rfl) ⟨19769298, by rfl⟩ : syracuseStep 52718129 = 39538597) B39538597
theorem B35145419 : Blo 1899435 35145419 := bstep (se 1 (by rfl) ⟨26359064, by rfl⟩ : syracuseStep 35145419 = 52718129) B52718129
theorem B374884469 : Blo 1899435 374884469 := bstep (se 5 (by rfl) ⟨17572709, by rfl⟩ : syracuseStep 374884469 = 35145419) B35145419
theorem B249922979 : Blo 1899435 249922979 := bstep (se 1 (by rfl) ⟨187442234, by rfl⟩ : syracuseStep 249922979 = 374884469) B374884469
theorem B166615319 : Blo 1899435 166615319 := bstep (se 1 (by rfl) ⟨124961489, by rfl⟩ : syracuseStep 166615319 = 249922979) B249922979
theorem B444307517 : Blo 1899435 444307517 := bstep (se 3 (by rfl) ⟨83307659, by rfl⟩ : syracuseStep 444307517 = 166615319) B166615319
theorem B296205011 : Blo 1899435 296205011 := bstep (se 1 (by rfl) ⟨222153758, by rfl⟩ : syracuseStep 296205011 = 444307517) B444307517
theorem B197470007 : Blo 1899435 197470007 := bstep (se 1 (by rfl) ⟨148102505, by rfl⟩ : syracuseStep 197470007 = 296205011) B296205011
theorem B131646671 : Blo 1899435 131646671 := bstep (se 1 (by rfl) ⟨98735003, by rfl⟩ : syracuseStep 131646671 = 197470007) B197470007
theorem B87764447 : Blo 1899435 87764447 := bstep (se 1 (by rfl) ⟨65823335, by rfl⟩ : syracuseStep 87764447 = 131646671) B131646671
theorem B58509631 : Blo 1899435 58509631 := bstep (se 1 (by rfl) ⟨43882223, by rfl⟩ : syracuseStep 58509631 = 87764447) B87764447
theorem B312051365 : Blo 1899435 312051365 := bstep (se 4 (by rfl) ⟨29254815, by rfl⟩ : syracuseStep 312051365 = 58509631) B58509631
theorem B208034243 : Blo 1899435 208034243 := bstep (se 1 (by rfl) ⟨156025682, by rfl⟩ : syracuseStep 208034243 = 312051365) B312051365
theorem B138689495 : Blo 1899435 138689495 := bstep (se 1 (by rfl) ⟨104017121, by rfl⟩ : syracuseStep 138689495 = 208034243) B208034243
theorem B92459663 : Blo 1899435 92459663 := bstep (se 1 (by rfl) ⟨69344747, by rfl⟩ : syracuseStep 92459663 = 138689495) B138689495
theorem B61639775 : Blo 1899435 61639775 := bstep (se 1 (by rfl) ⟨46229831, by rfl⟩ : syracuseStep 61639775 = 92459663) B92459663
theorem B41093183 : Blo 1899435 41093183 := bstep (se 1 (by rfl) ⟨30819887, by rfl⟩ : syracuseStep 41093183 = 61639775) B61639775
theorem B27395455 : Blo 1899435 27395455 := bstep (se 1 (by rfl) ⟨20546591, by rfl⟩ : syracuseStep 27395455 = 41093183) B41093183
theorem B36527273 : Blo 1899435 36527273 := bstep (se 2 (by rfl) ⟨13697727, by rfl⟩ : syracuseStep 36527273 = 27395455) B27395455
theorem B24351515 : Blo 1899435 24351515 := bstep (se 1 (by rfl) ⟨18263636, by rfl⟩ : syracuseStep 24351515 = 36527273) B36527273
theorem B16234343 : Blo 1899435 16234343 := bstep (se 1 (by rfl) ⟨12175757, by rfl⟩ : syracuseStep 16234343 = 24351515) B24351515
theorem B10822895 : Blo 1899435 10822895 := bstep (se 1 (by rfl) ⟨8117171, by rfl⟩ : syracuseStep 10822895 = 16234343) B16234343
theorem B7215263 : Blo 1899435 7215263 := bstep (se 1 (by rfl) ⟨5411447, by rfl⟩ : syracuseStep 7215263 = 10822895) B10822895
theorem B4810175 : Blo 1899435 4810175 := bstep (se 1 (by rfl) ⟨3607631, by rfl⟩ : syracuseStep 4810175 = 7215263) B7215263
theorem B3206783 : Blo 1899435 3206783 := bstep (se 1 (by rfl) ⟨2405087, by rfl⟩ : syracuseStep 3206783 = 4810175) B4810175
theorem B2137855 : Blo 1899435 2137855 := bstep (se 1 (by rfl) ⟨1603391, by rfl⟩ : syracuseStep 2137855 = 3206783) B3206783
theorem B2850473 : Blo 1899435 2850473 := bstep (se 2 (by rfl) ⟨1068927, by rfl⟩ : syracuseStep 2850473 = 2137855) B2137855
theorem B1900315 : Blo 1899435 1900315 := bstep (se 1 (by rfl) ⟨1425236, by rfl⟩ : syracuseStep 1900315 = 2850473) B2850473
theorem B2029297 : Blo 1899435 2029297 := bbase (se 2 (by rfl) ⟨760986, by rfl⟩ : syracuseStep 2029297 = 1521973) (by norm_num)
theorem B2705729 : Blo 1899435 2705729 := bstep (se 2 (by rfl) ⟨1014648, by rfl⟩ : syracuseStep 2705729 = 2029297) B2029297
theorem B7215277 : Blo 1899435 7215277 := bstep (se 3 (by rfl) ⟨1352864, by rfl⟩ : syracuseStep 7215277 = 2705729) B2705729
theorem B9620369 : Blo 1899435 9620369 := bstep (se 2 (by rfl) ⟨3607638, by rfl⟩ : syracuseStep 9620369 = 7215277) B7215277
theorem B6413579 : Blo 1899435 6413579 := bstep (se 1 (by rfl) ⟨4810184, by rfl⟩ : syracuseStep 6413579 = 9620369) B9620369
theorem B4275719 : Blo 1899435 4275719 := bstep (se 1 (by rfl) ⟨3206789, by rfl⟩ : syracuseStep 4275719 = 6413579) B6413579
theorem B2850479 : Blo 1899435 2850479 := bstep (se 1 (by rfl) ⟨2137859, by rfl⟩ : syracuseStep 2850479 = 4275719) B4275719
theorem B1900319 : Blo 1899435 1900319 := bstep (se 1 (by rfl) ⟨1425239, by rfl⟩ : syracuseStep 1900319 = 2850479) B2850479
theorem B2850485 : Blo 1899435 2850485 := bbase (se 5 (by rfl) ⟨133616, by rfl⟩ : syracuseStep 2850485 = 267233) (by norm_num)
theorem B1900323 : Blo 1899435 1900323 := bstep (se 1 (by rfl) ⟨1425242, by rfl⟩ : syracuseStep 1900323 = 2850485) B2850485
theorem B4810205 : Blo 1899435 4810205 := bbase (se 3 (by rfl) ⟨901913, by rfl⟩ : syracuseStep 4810205 = 1803827) (by norm_num)
theorem B3206803 : Blo 1899435 3206803 := bstep (se 1 (by rfl) ⟨2405102, by rfl⟩ : syracuseStep 3206803 = 4810205) B4810205
theorem B4275737 : Blo 1899435 4275737 := bstep (se 2 (by rfl) ⟨1603401, by rfl⟩ : syracuseStep 4275737 = 3206803) B3206803
theorem B2850491 : Blo 1899435 2850491 := bstep (se 1 (by rfl) ⟨2137868, by rfl⟩ : syracuseStep 2850491 = 4275737) B4275737
theorem B1900327 : Blo 1899435 1900327 := bstep (se 1 (by rfl) ⟨1425245, by rfl⟩ : syracuseStep 1900327 = 2850491) B2850491
theorem B2137873 : Blo 1899435 2137873 := bbase (se 2 (by rfl) ⟨801702, by rfl⟩ : syracuseStep 2137873 = 1603405) (by norm_num)
theorem B2850497 : Blo 1899435 2850497 := bstep (se 2 (by rfl) ⟨1068936, by rfl⟩ : syracuseStep 2850497 = 2137873) B2137873
theorem B1900331 : Blo 1899435 1900331 := bstep (se 1 (by rfl) ⟨1425248, by rfl⟩ : syracuseStep 1900331 = 2850497) B2850497
theorem B3607669 : Blo 1899435 3607669 := bbase (se 5 (by rfl) ⟨169109, by rfl⟩ : syracuseStep 3607669 = 338219) (by norm_num)
theorem B4810225 : Blo 1899435 4810225 := bstep (se 2 (by rfl) ⟨1803834, by rfl⟩ : syracuseStep 4810225 = 3607669) B3607669
theorem B6413633 : Blo 1899435 6413633 := bstep (se 2 (by rfl) ⟨2405112, by rfl⟩ : syracuseStep 6413633 = 4810225) B4810225
theorem B4275755 : Blo 1899435 4275755 := bstep (se 1 (by rfl) ⟨3206816, by rfl⟩ : syracuseStep 4275755 = 6413633) B6413633
theorem B2850503 : Blo 1899435 2850503 := bstep (se 1 (by rfl) ⟨2137877, by rfl⟩ : syracuseStep 2850503 = 4275755) B4275755
theorem B1900335 : Blo 1899435 1900335 := bstep (se 1 (by rfl) ⟨1425251, by rfl⟩ : syracuseStep 1900335 = 2850503) B2850503
theorem B2850509 : Blo 1899435 2850509 := bbase (se 3 (by rfl) ⟨534470, by rfl⟩ : syracuseStep 2850509 = 1068941) (by norm_num)
theorem B1900339 : Blo 1899435 1900339 := bstep (se 1 (by rfl) ⟨1425254, by rfl⟩ : syracuseStep 1900339 = 2850509) B2850509
theorem B4275773 : Blo 1899435 4275773 := bbase (se 3 (by rfl) ⟨801707, by rfl⟩ : syracuseStep 4275773 = 1603415) (by norm_num)
theorem B2850515 : Blo 1899435 2850515 := bstep (se 1 (by rfl) ⟨2137886, by rfl⟩ : syracuseStep 2850515 = 4275773) B4275773
theorem B1900343 : Blo 1899435 1900343 := bstep (se 1 (by rfl) ⟨1425257, by rfl⟩ : syracuseStep 1900343 = 2850515) B2850515
theorem B3206837 : Blo 1899435 3206837 := bbase (se 5 (by rfl) ⟨150320, by rfl⟩ : syracuseStep 3206837 = 300641) (by norm_num)
theorem B2137891 : Blo 1899435 2137891 := bstep (se 1 (by rfl) ⟨1603418, by rfl⟩ : syracuseStep 2137891 = 3206837) B3206837
theorem B2850521 : Blo 1899435 2850521 := bstep (se 2 (by rfl) ⟨1068945, by rfl⟩ : syracuseStep 2850521 = 2137891) B2137891
theorem B1900347 : Blo 1899435 1900347 := bstep (se 1 (by rfl) ⟨1425260, by rfl⟩ : syracuseStep 1900347 = 2850521) B2850521
theorem B3043997 : Blo 1899435 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B2029331 : Blo 1899435 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B5411549 : Blo 1899435 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B14430797 : Blo 1899435 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B9620531 : Blo 1899435 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B6413687 : Blo 1899435 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B4275791 : Blo 1899435 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B2850527 : Blo 1899435 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B1900351 : Blo 1899435 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B2850533 : Blo 1899435 2850533 := bbase (se 4 (by rfl) ⟨267237, by rfl⟩ : syracuseStep 2850533 = 534475) (by norm_num)
theorem B1900355 : Blo 1899435 1900355 := bstep (se 1 (by rfl) ⟨1425266, by rfl⟩ : syracuseStep 1900355 = 2850533) B2850533
theorem B5411573 : Blo 1899435 5411573 := bbase (se 5 (by rfl) ⟨253667, by rfl⟩ : syracuseStep 5411573 = 507335) (by norm_num)
theorem B3607715 : Blo 1899435 3607715 := bstep (se 1 (by rfl) ⟨2705786, by rfl⟩ : syracuseStep 3607715 = 5411573) B5411573
theorem B2405143 : Blo 1899435 2405143 := bstep (se 1 (by rfl) ⟨1803857, by rfl⟩ : syracuseStep 2405143 = 3607715) B3607715
theorem B3206857 : Blo 1899435 3206857 := bstep (se 2 (by rfl) ⟨1202571, by rfl⟩ : syracuseStep 3206857 = 2405143) B2405143
theorem B4275809 : Blo 1899435 4275809 := bstep (se 2 (by rfl) ⟨1603428, by rfl⟩ : syracuseStep 4275809 = 3206857) B3206857
theorem B2850539 : Blo 1899435 2850539 := bstep (se 1 (by rfl) ⟨2137904, by rfl⟩ : syracuseStep 2850539 = 4275809) B4275809
theorem B1900359 : Blo 1899435 1900359 := bstep (se 1 (by rfl) ⟨1425269, by rfl⟩ : syracuseStep 1900359 = 2850539) B2850539
theorem B2137909 : Blo 1899435 2137909 := bbase (se 5 (by rfl) ⟨100214, by rfl⟩ : syracuseStep 2137909 = 200429) (by norm_num)
theorem B2850545 : Blo 1899435 2850545 := bstep (se 2 (by rfl) ⟨1068954, by rfl⟩ : syracuseStep 2850545 = 2137909) B2137909
theorem B1900363 : Blo 1899435 1900363 := bstep (se 1 (by rfl) ⟨1425272, by rfl⟩ : syracuseStep 1900363 = 2850545) B2850545
theorem B2405153 : Blo 1899435 2405153 := bbase (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) (by norm_num)
theorem B6413741 : Blo 1899435 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B4275827 : Blo 1899435 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B2850551 : Blo 1899435 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B1900367 : Blo 1899435 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B2850557 : Blo 1899435 2850557 := bbase (se 3 (by rfl) ⟨534479, by rfl⟩ : syracuseStep 2850557 = 1068959) (by norm_num)
theorem B1900371 : Blo 1899435 1900371 := bstep (se 1 (by rfl) ⟨1425278, by rfl⟩ : syracuseStep 1900371 = 2850557) B2850557
theorem B4275845 : Blo 1899435 4275845 := bbase (se 4 (by rfl) ⟨400860, by rfl⟩ : syracuseStep 4275845 = 801721) (by norm_num)
theorem B2850563 : Blo 1899435 2850563 := bstep (se 1 (by rfl) ⟨2137922, by rfl⟩ : syracuseStep 2850563 = 4275845) B4275845
theorem B1900375 : Blo 1899435 1900375 := bstep (se 1 (by rfl) ⟨1425281, by rfl⟩ : syracuseStep 1900375 = 2850563) B2850563
theorem B6088085 : Blo 1899435 6088085 := bbase (se 6 (by rfl) ⟨142689, by rfl⟩ : syracuseStep 6088085 = 285379) (by norm_num)
theorem B4058723 : Blo 1899435 4058723 := bstep (se 1 (by rfl) ⟨3044042, by rfl⟩ : syracuseStep 4058723 = 6088085) B6088085
theorem B2705815 : Blo 1899435 2705815 := bstep (se 1 (by rfl) ⟨2029361, by rfl⟩ : syracuseStep 2705815 = 4058723) B4058723
theorem B3607753 : Blo 1899435 3607753 := bstep (se 2 (by rfl) ⟨1352907, by rfl⟩ : syracuseStep 3607753 = 2705815) B2705815
theorem B4810337 : Blo 1899435 4810337 := bstep (se 2 (by rfl) ⟨1803876, by rfl⟩ : syracuseStep 4810337 = 3607753) B3607753
theorem B3206891 : Blo 1899435 3206891 := bstep (se 1 (by rfl) ⟨2405168, by rfl⟩ : syracuseStep 3206891 = 4810337) B4810337
theorem B2137927 : Blo 1899435 2137927 := bstep (se 1 (by rfl) ⟨1603445, by rfl⟩ : syracuseStep 2137927 = 3206891) B3206891
theorem B2850569 : Blo 1899435 2850569 := bstep (se 2 (by rfl) ⟨1068963, by rfl⟩ : syracuseStep 2850569 = 2137927) B2137927
theorem B1900379 : Blo 1899435 1900379 := bstep (se 1 (by rfl) ⟨1425284, by rfl⟩ : syracuseStep 1900379 = 2850569) B2850569
theorem B9620693 : Blo 1899435 9620693 := bbase (se 7 (by rfl) ⟨112742, by rfl⟩ : syracuseStep 9620693 = 225485) (by norm_num)
theorem B6413795 : Blo 1899435 6413795 := bstep (se 1 (by rfl) ⟨4810346, by rfl⟩ : syracuseStep 6413795 = 9620693) B9620693
theorem B4275863 : Blo 1899435 4275863 := bstep (se 1 (by rfl) ⟨3206897, by rfl⟩ : syracuseStep 4275863 = 6413795) B6413795
theorem B2850575 : Blo 1899435 2850575 := bstep (se 1 (by rfl) ⟨2137931, by rfl⟩ : syracuseStep 2850575 = 4275863) B4275863
theorem B1900383 : Blo 1899435 1900383 := bstep (se 1 (by rfl) ⟨1425287, by rfl⟩ : syracuseStep 1900383 = 2850575) B2850575
theorem B2850581 : Blo 1899435 2850581 := bbase (se 6 (by rfl) ⟨66810, by rfl⟩ : syracuseStep 2850581 = 133621) (by norm_num)
theorem B1900387 : Blo 1899435 1900387 := bstep (se 1 (by rfl) ⟨1425290, by rfl⟩ : syracuseStep 1900387 = 2850581) B2850581
theorem B7810405 : Blo 1899435 7810405 := bbase (se 4 (by rfl) ⟨732225, by rfl⟩ : syracuseStep 7810405 = 1464451) (by norm_num)
theorem B41655493 : Blo 1899435 41655493 := bstep (se 4 (by rfl) ⟨3905202, by rfl⟩ : syracuseStep 41655493 = 7810405) B7810405
theorem B55540657 : Blo 1899435 55540657 := bstep (se 2 (by rfl) ⟨20827746, by rfl⟩ : syracuseStep 55540657 = 41655493) B41655493
theorem B74054209 : Blo 1899435 74054209 := bstep (se 2 (by rfl) ⟨27770328, by rfl⟩ : syracuseStep 74054209 = 55540657) B55540657
theorem B98738945 : Blo 1899435 98738945 := bstep (se 2 (by rfl) ⟨37027104, by rfl⟩ : syracuseStep 98738945 = 74054209) B74054209
theorem B65825963 : Blo 1899435 65825963 := bstep (se 1 (by rfl) ⟨49369472, by rfl⟩ : syracuseStep 65825963 = 98738945) B98738945
theorem B43883975 : Blo 1899435 43883975 := bstep (se 1 (by rfl) ⟨32912981, by rfl⟩ : syracuseStep 43883975 = 65825963) B65825963
theorem B117023933 : Blo 1899435 117023933 := bstep (se 3 (by rfl) ⟨21941987, by rfl⟩ : syracuseStep 117023933 = 43883975) B43883975
theorem B78015955 : Blo 1899435 78015955 := bstep (se 1 (by rfl) ⟨58511966, by rfl⟩ : syracuseStep 78015955 = 117023933) B117023933
theorem B104021273 : Blo 1899435 104021273 := bstep (se 2 (by rfl) ⟨39007977, by rfl⟩ : syracuseStep 104021273 = 78015955) B78015955
theorem B69347515 : Blo 1899435 69347515 := bstep (se 1 (by rfl) ⟨52010636, by rfl⟩ : syracuseStep 69347515 = 104021273) B104021273
theorem B92463353 : Blo 1899435 92463353 := bstep (se 2 (by rfl) ⟨34673757, by rfl⟩ : syracuseStep 92463353 = 69347515) B69347515
theorem B61642235 : Blo 1899435 61642235 := bstep (se 1 (by rfl) ⟨46231676, by rfl⟩ : syracuseStep 61642235 = 92463353) B92463353
theorem B41094823 : Blo 1899435 41094823 := bstep (se 1 (by rfl) ⟨30821117, by rfl⟩ : syracuseStep 41094823 = 61642235) B61642235
theorem B54793097 : Blo 1899435 54793097 := bstep (se 2 (by rfl) ⟨20547411, by rfl⟩ : syracuseStep 54793097 = 41094823) B41094823
theorem B36528731 : Blo 1899435 36528731 := bstep (se 1 (by rfl) ⟨27396548, by rfl⟩ : syracuseStep 36528731 = 54793097) B54793097
theorem B24352487 : Blo 1899435 24352487 := bstep (se 1 (by rfl) ⟨18264365, by rfl⟩ : syracuseStep 24352487 = 36528731) B36528731
theorem B16234991 : Blo 1899435 16234991 := bstep (se 1 (by rfl) ⟨12176243, by rfl⟩ : syracuseStep 16234991 = 24352487) B24352487
theorem B10823327 : Blo 1899435 10823327 := bstep (se 1 (by rfl) ⟨8117495, by rfl⟩ : syracuseStep 10823327 = 16234991) B16234991
theorem B7215551 : Blo 1899435 7215551 := bstep (se 1 (by rfl) ⟨5411663, by rfl⟩ : syracuseStep 7215551 = 10823327) B10823327
theorem B4810367 : Blo 1899435 4810367 := bstep (se 1 (by rfl) ⟨3607775, by rfl⟩ : syracuseStep 4810367 = 7215551) B7215551
theorem B3206911 : Blo 1899435 3206911 := bstep (se 1 (by rfl) ⟨2405183, by rfl⟩ : syracuseStep 3206911 = 4810367) B4810367
theorem B4275881 : Blo 1899435 4275881 := bstep (se 2 (by rfl) ⟨1603455, by rfl⟩ : syracuseStep 4275881 = 3206911) B3206911
theorem B2850587 : Blo 1899435 2850587 := bstep (se 1 (by rfl) ⟨2137940, by rfl⟩ : syracuseStep 2850587 = 4275881) B4275881
theorem B1900391 : Blo 1899435 1900391 := bstep (se 1 (by rfl) ⟨1425293, by rfl⟩ : syracuseStep 1900391 = 2850587) B2850587
theorem B2137945 : Blo 1899435 2137945 := bbase (se 2 (by rfl) ⟨801729, by rfl⟩ : syracuseStep 2137945 = 1603459) (by norm_num)
theorem B2850593 : Blo 1899435 2850593 := bstep (se 2 (by rfl) ⟨1068972, by rfl⟩ : syracuseStep 2850593 = 2137945) B2137945
theorem B1900395 : Blo 1899435 1900395 := bstep (se 1 (by rfl) ⟨1425296, by rfl⟩ : syracuseStep 1900395 = 2850593) B2850593
theorem B4058765 : Blo 1899435 4058765 := bbase (se 3 (by rfl) ⟨761018, by rfl⟩ : syracuseStep 4058765 = 1522037) (by norm_num)
theorem B2705843 : Blo 1899435 2705843 := bstep (se 1 (by rfl) ⟨2029382, by rfl⟩ : syracuseStep 2705843 = 4058765) B4058765
theorem B7215581 : Blo 1899435 7215581 := bstep (se 3 (by rfl) ⟨1352921, by rfl⟩ : syracuseStep 7215581 = 2705843) B2705843
theorem B4810387 : Blo 1899435 4810387 := bstep (se 1 (by rfl) ⟨3607790, by rfl⟩ : syracuseStep 4810387 = 7215581) B7215581
theorem B6413849 : Blo 1899435 6413849 := bstep (se 2 (by rfl) ⟨2405193, by rfl⟩ : syracuseStep 6413849 = 4810387) B4810387
theorem B4275899 : Blo 1899435 4275899 := bstep (se 1 (by rfl) ⟨3206924, by rfl⟩ : syracuseStep 4275899 = 6413849) B6413849
theorem B2850599 : Blo 1899435 2850599 := bstep (se 1 (by rfl) ⟨2137949, by rfl⟩ : syracuseStep 2850599 = 4275899) B4275899
theorem B1900399 : Blo 1899435 1900399 := bstep (se 1 (by rfl) ⟨1425299, by rfl⟩ : syracuseStep 1900399 = 2850599) B2850599
theorem B2850605 : Blo 1899435 2850605 := bbase (se 3 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 2850605 = 1068977) (by norm_num)
theorem B1900403 : Blo 1899435 1900403 := bstep (se 1 (by rfl) ⟨1425302, by rfl⟩ : syracuseStep 1900403 = 2850605) B2850605
theorem B4275917 : Blo 1899435 4275917 := bbase (se 3 (by rfl) ⟨801734, by rfl⟩ : syracuseStep 4275917 = 1603469) (by norm_num)
theorem B2850611 : Blo 1899435 2850611 := bstep (se 1 (by rfl) ⟨2137958, by rfl⟩ : syracuseStep 2850611 = 4275917) B4275917
theorem B1900407 : Blo 1899435 1900407 := bstep (se 1 (by rfl) ⟨1425305, by rfl⟩ : syracuseStep 1900407 = 2850611) B2850611
theorem B2405209 : Blo 1899435 2405209 := bbase (se 2 (by rfl) ⟨901953, by rfl⟩ : syracuseStep 2405209 = 1803907) (by norm_num)
theorem B3206945 : Blo 1899435 3206945 := bstep (se 2 (by rfl) ⟨1202604, by rfl⟩ : syracuseStep 3206945 = 2405209) B2405209
theorem B2137963 : Blo 1899435 2137963 := bstep (se 1 (by rfl) ⟨1603472, by rfl⟩ : syracuseStep 2137963 = 3206945) B3206945
theorem B2850617 : Blo 1899435 2850617 := bstep (se 2 (by rfl) ⟨1068981, by rfl⟩ : syracuseStep 2850617 = 2137963) B2137963
theorem B1900411 : Blo 1899435 1900411 := bstep (se 1 (by rfl) ⟨1425308, by rfl⟩ : syracuseStep 1900411 = 2850617) B2850617
theorem B4566149 : Blo 1899435 4566149 := bbase (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) (by norm_num)
theorem B3044099 : Blo 1899435 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B8117597 : Blo 1899435 8117597 := bstep (se 3 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 8117597 = 3044099) B3044099
theorem B21646925 : Blo 1899435 21646925 := bstep (se 3 (by rfl) ⟨4058798, by rfl⟩ : syracuseStep 21646925 = 8117597) B8117597
theorem B14431283 : Blo 1899435 14431283 := bstep (se 1 (by rfl) ⟨10823462, by rfl⟩ : syracuseStep 14431283 = 21646925) B21646925
theorem B9620855 : Blo 1899435 9620855 := bstep (se 1 (by rfl) ⟨7215641, by rfl⟩ : syracuseStep 9620855 = 14431283) B14431283
theorem B6413903 : Blo 1899435 6413903 := bstep (se 1 (by rfl) ⟨4810427, by rfl⟩ : syracuseStep 6413903 = 9620855) B9620855
theorem B4275935 : Blo 1899435 4275935 := bstep (se 1 (by rfl) ⟨3206951, by rfl⟩ : syracuseStep 4275935 = 6413903) B6413903
theorem B2850623 : Blo 1899435 2850623 := bstep (se 1 (by rfl) ⟨2137967, by rfl⟩ : syracuseStep 2850623 = 4275935) B4275935
theorem B1900415 : Blo 1899435 1900415 := bstep (se 1 (by rfl) ⟨1425311, by rfl⟩ : syracuseStep 1900415 = 2850623) B2850623
theorem B2850629 : Blo 1899435 2850629 := bbase (se 4 (by rfl) ⟨267246, by rfl⟩ : syracuseStep 2850629 = 534493) (by norm_num)
theorem B1900419 : Blo 1899435 1900419 := bstep (se 1 (by rfl) ⟨1425314, by rfl⟩ : syracuseStep 1900419 = 2850629) B2850629
theorem B3206965 : Blo 1899435 3206965 := bbase (se 5 (by rfl) ⟨150326, by rfl⟩ : syracuseStep 3206965 = 300653) (by norm_num)
theorem B4275953 : Blo 1899435 4275953 := bstep (se 2 (by rfl) ⟨1603482, by rfl⟩ : syracuseStep 4275953 = 3206965) B3206965
theorem B2850635 : Blo 1899435 2850635 := bstep (se 1 (by rfl) ⟨2137976, by rfl⟩ : syracuseStep 2850635 = 4275953) B4275953
theorem B1900423 : Blo 1899435 1900423 := bstep (se 1 (by rfl) ⟨1425317, by rfl⟩ : syracuseStep 1900423 = 2850635) B2850635
theorem B2137981 : Blo 1899435 2137981 := bbase (se 3 (by rfl) ⟨400871, by rfl⟩ : syracuseStep 2137981 = 801743) (by norm_num)
theorem B2850641 : Blo 1899435 2850641 := bstep (se 2 (by rfl) ⟨1068990, by rfl⟩ : syracuseStep 2850641 = 2137981) B2137981
theorem B1900427 : Blo 1899435 1900427 := bstep (se 1 (by rfl) ⟨1425320, by rfl⟩ : syracuseStep 1900427 = 2850641) B2850641
theorem B6413957 : Blo 1899435 6413957 := bbase (se 4 (by rfl) ⟨601308, by rfl⟩ : syracuseStep 6413957 = 1202617) (by norm_num)
theorem B4275971 : Blo 1899435 4275971 := bstep (se 1 (by rfl) ⟨3206978, by rfl⟩ : syracuseStep 4275971 = 6413957) B6413957
theorem B2850647 : Blo 1899435 2850647 := bstep (se 1 (by rfl) ⟨2137985, by rfl⟩ : syracuseStep 2850647 = 4275971) B4275971
theorem B1900431 : Blo 1899435 1900431 := bstep (se 1 (by rfl) ⟨1425323, by rfl⟩ : syracuseStep 1900431 = 2850647) B2850647
theorem B2850653 : Blo 1899435 2850653 := bbase (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) (by norm_num)
theorem B1900435 : Blo 1899435 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B4275989 : Blo 1899435 4275989 := bbase (se 6 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 4275989 = 200437) (by norm_num)
theorem B2850659 : Blo 1899435 2850659 := bstep (se 1 (by rfl) ⟨2137994, by rfl⟩ : syracuseStep 2850659 = 4275989) B4275989
theorem B1900439 : Blo 1899435 1900439 := bstep (se 1 (by rfl) ⟨1425329, by rfl⟩ : syracuseStep 1900439 = 2850659) B2850659
theorem B7215749 : Blo 1899435 7215749 := bbase (se 4 (by rfl) ⟨676476, by rfl⟩ : syracuseStep 7215749 = 1352953) (by norm_num)
theorem B4810499 : Blo 1899435 4810499 := bstep (se 1 (by rfl) ⟨3607874, by rfl⟩ : syracuseStep 4810499 = 7215749) B7215749
theorem B3206999 : Blo 1899435 3206999 := bstep (se 1 (by rfl) ⟨2405249, by rfl⟩ : syracuseStep 3206999 = 4810499) B4810499
theorem B2137999 : Blo 1899435 2137999 := bstep (se 1 (by rfl) ⟨1603499, by rfl⟩ : syracuseStep 2137999 = 3206999) B3206999
theorem B2850665 : Blo 1899435 2850665 := bstep (se 2 (by rfl) ⟨1068999, by rfl⟩ : syracuseStep 2850665 = 2137999) B2137999
theorem B1900443 : Blo 1899435 1900443 := bstep (se 1 (by rfl) ⟨1425332, by rfl⟩ : syracuseStep 1900443 = 2850665) B2850665
theorem B2283113 : Blo 1899435 2283113 := bbase (se 2 (by rfl) ⟨856167, by rfl⟩ : syracuseStep 2283113 = 1712335) (by norm_num)
theorem B6088301 : Blo 1899435 6088301 := bstep (se 3 (by rfl) ⟨1141556, by rfl⟩ : syracuseStep 6088301 = 2283113) B2283113
theorem B4058867 : Blo 1899435 4058867 := bstep (se 1 (by rfl) ⟨3044150, by rfl⟩ : syracuseStep 4058867 = 6088301) B6088301
theorem B10823645 : Blo 1899435 10823645 := bstep (se 3 (by rfl) ⟨2029433, by rfl⟩ : syracuseStep 10823645 = 4058867) B4058867
theorem B7215763 : Blo 1899435 7215763 := bstep (se 1 (by rfl) ⟨5411822, by rfl⟩ : syracuseStep 7215763 = 10823645) B10823645
theorem B9621017 : Blo 1899435 9621017 := bstep (se 2 (by rfl) ⟨3607881, by rfl⟩ : syracuseStep 9621017 = 7215763) B7215763
theorem B6414011 : Blo 1899435 6414011 := bstep (se 1 (by rfl) ⟨4810508, by rfl⟩ : syracuseStep 6414011 = 9621017) B9621017
theorem B4276007 : Blo 1899435 4276007 := bstep (se 1 (by rfl) ⟨3207005, by rfl⟩ : syracuseStep 4276007 = 6414011) B6414011
theorem B2850671 : Blo 1899435 2850671 := bstep (se 1 (by rfl) ⟨2138003, by rfl⟩ : syracuseStep 2850671 = 4276007) B4276007
theorem B1900447 : Blo 1899435 1900447 := bstep (se 1 (by rfl) ⟨1425335, by rfl⟩ : syracuseStep 1900447 = 2850671) B2850671
theorem B2850677 : Blo 1899435 2850677 := bbase (se 5 (by rfl) ⟨133625, by rfl⟩ : syracuseStep 2850677 = 267251) (by norm_num)
theorem B1900451 : Blo 1899435 1900451 := bstep (se 1 (by rfl) ⟨1425338, by rfl⟩ : syracuseStep 1900451 = 2850677) B2850677
theorem B4058885 : Blo 1899435 4058885 := bbase (se 4 (by rfl) ⟨380520, by rfl⟩ : syracuseStep 4058885 = 761041) (by norm_num)
theorem B2705923 : Blo 1899435 2705923 := bstep (se 1 (by rfl) ⟨2029442, by rfl⟩ : syracuseStep 2705923 = 4058885) B4058885
theorem B3607897 : Blo 1899435 3607897 := bstep (se 2 (by rfl) ⟨1352961, by rfl⟩ : syracuseStep 3607897 = 2705923) B2705923
theorem B4810529 : Blo 1899435 4810529 := bstep (se 2 (by rfl) ⟨1803948, by rfl⟩ : syracuseStep 4810529 = 3607897) B3607897
theorem B3207019 : Blo 1899435 3207019 := bstep (se 1 (by rfl) ⟨2405264, by rfl⟩ : syracuseStep 3207019 = 4810529) B4810529
theorem B4276025 : Blo 1899435 4276025 := bstep (se 2 (by rfl) ⟨1603509, by rfl⟩ : syracuseStep 4276025 = 3207019) B3207019
theorem B2850683 : Blo 1899435 2850683 := bstep (se 1 (by rfl) ⟨2138012, by rfl⟩ : syracuseStep 2850683 = 4276025) B4276025
theorem B1900455 : Blo 1899435 1900455 := bstep (se 1 (by rfl) ⟨1425341, by rfl⟩ : syracuseStep 1900455 = 2850683) B2850683
theorem B2138017 : Blo 1899435 2138017 := bbase (se 2 (by rfl) ⟨801756, by rfl⟩ : syracuseStep 2138017 = 1603513) (by norm_num)
theorem B2850689 : Blo 1899435 2850689 := bstep (se 2 (by rfl) ⟨1069008, by rfl⟩ : syracuseStep 2850689 = 2138017) B2138017
theorem B1900459 : Blo 1899435 1900459 := bstep (se 1 (by rfl) ⟨1425344, by rfl⟩ : syracuseStep 1900459 = 2850689) B2850689
theorem B4810549 : Blo 1899435 4810549 := bbase (se 5 (by rfl) ⟨225494, by rfl⟩ : syracuseStep 4810549 = 450989) (by norm_num)
theorem B6414065 : Blo 1899435 6414065 := bstep (se 2 (by rfl) ⟨2405274, by rfl⟩ : syracuseStep 6414065 = 4810549) B4810549
theorem B4276043 : Blo 1899435 4276043 := bstep (se 1 (by rfl) ⟨3207032, by rfl⟩ : syracuseStep 4276043 = 6414065) B6414065
theorem B2850695 : Blo 1899435 2850695 := bstep (se 1 (by rfl) ⟨2138021, by rfl⟩ : syracuseStep 2850695 = 4276043) B4276043
theorem B1900463 : Blo 1899435 1900463 := bstep (se 1 (by rfl) ⟨1425347, by rfl⟩ : syracuseStep 1900463 = 2850695) B2850695
theorem B2850701 : Blo 1899435 2850701 := bbase (se 3 (by rfl) ⟨534506, by rfl⟩ : syracuseStep 2850701 = 1069013) (by norm_num)
theorem B1900467 : Blo 1899435 1900467 := bstep (se 1 (by rfl) ⟨1425350, by rfl⟩ : syracuseStep 1900467 = 2850701) B2850701
theorem B4276061 : Blo 1899435 4276061 := bbase (se 3 (by rfl) ⟨801761, by rfl⟩ : syracuseStep 4276061 = 1603523) (by norm_num)
theorem B2850707 : Blo 1899435 2850707 := bstep (se 1 (by rfl) ⟨2138030, by rfl⟩ : syracuseStep 2850707 = 4276061) B4276061
theorem B1900471 : Blo 1899435 1900471 := bstep (se 1 (by rfl) ⟨1425353, by rfl⟩ : syracuseStep 1900471 = 2850707) B2850707
theorem B3207053 : Blo 1899435 3207053 := bbase (se 3 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 3207053 = 1202645) (by norm_num)
theorem B2138035 : Blo 1899435 2138035 := bstep (se 1 (by rfl) ⟨1603526, by rfl⟩ : syracuseStep 2138035 = 3207053) B3207053
theorem B2850713 : Blo 1899435 2850713 := bstep (se 2 (by rfl) ⟨1069017, by rfl⟩ : syracuseStep 2850713 = 2138035) B2138035
theorem B1900475 : Blo 1899435 1900475 := bstep (se 1 (by rfl) ⟨1425356, by rfl⟩ : syracuseStep 1900475 = 2850713) B2850713
theorem B7705637 : Blo 1899435 7705637 := bbase (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) (by norm_num)
theorem B5137091 : Blo 1899435 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B3424727 : Blo 1899435 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B9132605 : Blo 1899435 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B6088403 : Blo 1899435 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B16235741 : Blo 1899435 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B10823827 : Blo 1899435 10823827 := bstep (se 1 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 10823827 = 16235741) B16235741
theorem B14431769 : Blo 1899435 14431769 := bstep (se 2 (by rfl) ⟨5411913, by rfl⟩ : syracuseStep 14431769 = 10823827) B10823827
theorem B9621179 : Blo 1899435 9621179 := bstep (se 1 (by rfl) ⟨7215884, by rfl⟩ : syracuseStep 9621179 = 14431769) B14431769
theorem B6414119 : Blo 1899435 6414119 := bstep (se 1 (by rfl) ⟨4810589, by rfl⟩ : syracuseStep 6414119 = 9621179) B9621179
theorem B4276079 : Blo 1899435 4276079 := bstep (se 1 (by rfl) ⟨3207059, by rfl⟩ : syracuseStep 4276079 = 6414119) B6414119
theorem B2850719 : Blo 1899435 2850719 := bstep (se 1 (by rfl) ⟨2138039, by rfl⟩ : syracuseStep 2850719 = 4276079) B4276079
theorem B1900479 : Blo 1899435 1900479 := bstep (se 1 (by rfl) ⟨1425359, by rfl⟩ : syracuseStep 1900479 = 2850719) B2850719
theorem B2850725 : Blo 1899435 2850725 := bbase (se 4 (by rfl) ⟨267255, by rfl⟩ : syracuseStep 2850725 = 534511) (by norm_num)
theorem B1900483 : Blo 1899435 1900483 := bstep (se 1 (by rfl) ⟨1425362, by rfl⟩ : syracuseStep 1900483 = 2850725) B2850725
theorem B2405305 : Blo 1899435 2405305 := bbase (se 2 (by rfl) ⟨901989, by rfl⟩ : syracuseStep 2405305 = 1803979) (by norm_num)
theorem B3207073 : Blo 1899435 3207073 := bstep (se 2 (by rfl) ⟨1202652, by rfl⟩ : syracuseStep 3207073 = 2405305) B2405305
theorem B4276097 : Blo 1899435 4276097 := bstep (se 2 (by rfl) ⟨1603536, by rfl⟩ : syracuseStep 4276097 = 3207073) B3207073
theorem B2850731 : Blo 1899435 2850731 := bstep (se 1 (by rfl) ⟨2138048, by rfl⟩ : syracuseStep 2850731 = 4276097) B4276097
theorem B1900487 : Blo 1899435 1900487 := bstep (se 1 (by rfl) ⟨1425365, by rfl⟩ : syracuseStep 1900487 = 2850731) B2850731
theorem B2138053 : Blo 1899435 2138053 := bbase (se 4 (by rfl) ⟨200442, by rfl⟩ : syracuseStep 2138053 = 400885) (by norm_num)
theorem B2850737 : Blo 1899435 2850737 := bstep (se 2 (by rfl) ⟨1069026, by rfl⟩ : syracuseStep 2850737 = 2138053) B2138053
theorem B1900491 : Blo 1899435 1900491 := bstep (se 1 (by rfl) ⟨1425368, by rfl⟩ : syracuseStep 1900491 = 2850737) B2850737
theorem B3607973 : Blo 1899435 3607973 := bbase (se 4 (by rfl) ⟨338247, by rfl⟩ : syracuseStep 3607973 = 676495) (by norm_num)
theorem B2405315 : Blo 1899435 2405315 := bstep (se 1 (by rfl) ⟨1803986, by rfl⟩ : syracuseStep 2405315 = 3607973) B3607973
theorem B6414173 : Blo 1899435 6414173 := bstep (se 3 (by rfl) ⟨1202657, by rfl⟩ : syracuseStep 6414173 = 2405315) B2405315
theorem B4276115 : Blo 1899435 4276115 := bstep (se 1 (by rfl) ⟨3207086, by rfl⟩ : syracuseStep 4276115 = 6414173) B6414173
theorem B2850743 : Blo 1899435 2850743 := bstep (se 1 (by rfl) ⟨2138057, by rfl⟩ : syracuseStep 2850743 = 4276115) B4276115
theorem B1900495 : Blo 1899435 1900495 := bstep (se 1 (by rfl) ⟨1425371, by rfl⟩ : syracuseStep 1900495 = 2850743) B2850743
theorem B2850749 : Blo 1899435 2850749 := bbase (se 3 (by rfl) ⟨534515, by rfl⟩ : syracuseStep 2850749 = 1069031) (by norm_num)
theorem B1900499 : Blo 1899435 1900499 := bstep (se 1 (by rfl) ⟨1425374, by rfl⟩ : syracuseStep 1900499 = 2850749) B2850749
theorem B4276133 : Blo 1899435 4276133 := bbase (se 4 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 4276133 = 801775) (by norm_num)
theorem B2850755 : Blo 1899435 2850755 := bstep (se 1 (by rfl) ⟨2138066, by rfl⟩ : syracuseStep 2850755 = 4276133) B4276133
theorem B1900503 : Blo 1899435 1900503 := bstep (se 1 (by rfl) ⟨1425377, by rfl⟩ : syracuseStep 1900503 = 2850755) B2850755
theorem B4810661 : Blo 1899435 4810661 := bbase (se 4 (by rfl) ⟨450999, by rfl⟩ : syracuseStep 4810661 = 901999) (by norm_num)
theorem B3207107 : Blo 1899435 3207107 := bstep (se 1 (by rfl) ⟨2405330, by rfl⟩ : syracuseStep 3207107 = 4810661) B4810661
theorem B2138071 : Blo 1899435 2138071 := bstep (se 1 (by rfl) ⟨1603553, by rfl⟩ : syracuseStep 2138071 = 3207107) B3207107
theorem B2850761 : Blo 1899435 2850761 := bstep (se 2 (by rfl) ⟨1069035, by rfl⟩ : syracuseStep 2850761 = 2138071) B2138071
theorem B1900507 : Blo 1899435 1900507 := bstep (se 1 (by rfl) ⟨1425380, by rfl⟩ : syracuseStep 1900507 = 2850761) B2850761
theorem B5412005 : Blo 1899435 5412005 := bbase (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) (by norm_num)
theorem B3608003 : Blo 1899435 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B9621341 : Blo 1899435 9621341 := bstep (se 3 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 9621341 = 3608003) B3608003
theorem B6414227 : Blo 1899435 6414227 := bstep (se 1 (by rfl) ⟨4810670, by rfl⟩ : syracuseStep 6414227 = 9621341) B9621341
theorem B4276151 : Blo 1899435 4276151 := bstep (se 1 (by rfl) ⟨3207113, by rfl⟩ : syracuseStep 4276151 = 6414227) B6414227
theorem B2850767 : Blo 1899435 2850767 := bstep (se 1 (by rfl) ⟨2138075, by rfl⟩ : syracuseStep 2850767 = 4276151) B4276151
theorem B1900511 : Blo 1899435 1900511 := bstep (se 1 (by rfl) ⟨1425383, by rfl⟩ : syracuseStep 1900511 = 2850767) B2850767
theorem B2850773 : Blo 1899435 2850773 := bbase (se 7 (by rfl) ⟨33407, by rfl⟩ : syracuseStep 2850773 = 66815) (by norm_num)
theorem B1900515 : Blo 1899435 1900515 := bstep (se 1 (by rfl) ⟨1425386, by rfl⟩ : syracuseStep 1900515 = 2850773) B2850773
theorem B7216037 : Blo 1899435 7216037 := bbase (se 4 (by rfl) ⟨676503, by rfl⟩ : syracuseStep 7216037 = 1353007) (by norm_num)
theorem B4810691 : Blo 1899435 4810691 := bstep (se 1 (by rfl) ⟨3608018, by rfl⟩ : syracuseStep 4810691 = 7216037) B7216037
theorem B3207127 : Blo 1899435 3207127 := bstep (se 1 (by rfl) ⟨2405345, by rfl⟩ : syracuseStep 3207127 = 4810691) B4810691
theorem B4276169 : Blo 1899435 4276169 := bstep (se 2 (by rfl) ⟨1603563, by rfl⟩ : syracuseStep 4276169 = 3207127) B3207127
theorem B2850779 : Blo 1899435 2850779 := bstep (se 1 (by rfl) ⟨2138084, by rfl⟩ : syracuseStep 2850779 = 4276169) B4276169
theorem B1900519 : Blo 1899435 1900519 := bstep (se 1 (by rfl) ⟨1425389, by rfl⟩ : syracuseStep 1900519 = 2850779) B2850779
theorem B2138089 : Blo 1899435 2138089 := bbase (se 2 (by rfl) ⟨801783, by rfl⟩ : syracuseStep 2138089 = 1603567) (by norm_num)
theorem B2850785 : Blo 1899435 2850785 := bstep (se 2 (by rfl) ⟨1069044, by rfl⟩ : syracuseStep 2850785 = 2138089) B2138089
theorem B1900523 : Blo 1899435 1900523 := bstep (se 1 (by rfl) ⟨1425392, by rfl⟩ : syracuseStep 1900523 = 2850785) B2850785
theorem B3852917 : Blo 1899435 3852917 := bbase (se 5 (by rfl) ⟨180605, by rfl⟩ : syracuseStep 3852917 = 361211) (by norm_num)
theorem B2568611 : Blo 1899435 2568611 := bstep (se 1 (by rfl) ⟨1926458, by rfl⟩ : syracuseStep 2568611 = 3852917) B3852917
theorem B6849629 : Blo 1899435 6849629 := bstep (se 3 (by rfl) ⟨1284305, by rfl⟩ : syracuseStep 6849629 = 2568611) B2568611
theorem B4566419 : Blo 1899435 4566419 := bstep (se 1 (by rfl) ⟨3424814, by rfl⟩ : syracuseStep 4566419 = 6849629) B6849629
theorem B3044279 : Blo 1899435 3044279 := bstep (se 1 (by rfl) ⟨2283209, by rfl⟩ : syracuseStep 3044279 = 4566419) B4566419
theorem B2029519 : Blo 1899435 2029519 := bstep (se 1 (by rfl) ⟨1522139, by rfl⟩ : syracuseStep 2029519 = 3044279) B3044279
theorem B10824101 : Blo 1899435 10824101 := bstep (se 4 (by rfl) ⟨1014759, by rfl⟩ : syracuseStep 10824101 = 2029519) B2029519
theorem B7216067 : Blo 1899435 7216067 := bstep (se 1 (by rfl) ⟨5412050, by rfl⟩ : syracuseStep 7216067 = 10824101) B10824101
theorem B4810711 : Blo 1899435 4810711 := bstep (se 1 (by rfl) ⟨3608033, by rfl⟩ : syracuseStep 4810711 = 7216067) B7216067
theorem B6414281 : Blo 1899435 6414281 := bstep (se 2 (by rfl) ⟨2405355, by rfl⟩ : syracuseStep 6414281 = 4810711) B4810711
theorem B4276187 : Blo 1899435 4276187 := bstep (se 1 (by rfl) ⟨3207140, by rfl⟩ : syracuseStep 4276187 = 6414281) B6414281
theorem B2850791 : Blo 1899435 2850791 := bstep (se 1 (by rfl) ⟨2138093, by rfl⟩ : syracuseStep 2850791 = 4276187) B4276187
theorem B1900527 : Blo 1899435 1900527 := bstep (se 1 (by rfl) ⟨1425395, by rfl⟩ : syracuseStep 1900527 = 2850791) B2850791
theorem B2850797 : Blo 1899435 2850797 := bbase (se 3 (by rfl) ⟨534524, by rfl⟩ : syracuseStep 2850797 = 1069049) (by norm_num)
theorem B1900531 : Blo 1899435 1900531 := bstep (se 1 (by rfl) ⟨1425398, by rfl⟩ : syracuseStep 1900531 = 2850797) B2850797
theorem B4276205 : Blo 1899435 4276205 := bbase (se 3 (by rfl) ⟨801788, by rfl⟩ : syracuseStep 4276205 = 1603577) (by norm_num)
theorem B2850803 : Blo 1899435 2850803 := bstep (se 1 (by rfl) ⟨2138102, by rfl⟩ : syracuseStep 2850803 = 4276205) B4276205
theorem B1900535 : Blo 1899435 1900535 := bstep (se 1 (by rfl) ⟨1425401, by rfl⟩ : syracuseStep 1900535 = 2850803) B2850803
theorem B3424837 : Blo 1899435 3424837 := bbase (se 4 (by rfl) ⟨321078, by rfl⟩ : syracuseStep 3424837 = 642157) (by norm_num)
theorem B4566449 : Blo 1899435 4566449 := bstep (se 2 (by rfl) ⟨1712418, by rfl⟩ : syracuseStep 4566449 = 3424837) B3424837
theorem B3044299 : Blo 1899435 3044299 := bstep (se 1 (by rfl) ⟨2283224, by rfl⟩ : syracuseStep 3044299 = 4566449) B4566449
theorem B4059065 : Blo 1899435 4059065 := bstep (se 2 (by rfl) ⟨1522149, by rfl⟩ : syracuseStep 4059065 = 3044299) B3044299
theorem B2706043 : Blo 1899435 2706043 := bstep (se 1 (by rfl) ⟨2029532, by rfl⟩ : syracuseStep 2706043 = 4059065) B4059065
theorem B3608057 : Blo 1899435 3608057 := bstep (se 2 (by rfl) ⟨1353021, by rfl⟩ : syracuseStep 3608057 = 2706043) B2706043
theorem B2405371 : Blo 1899435 2405371 := bstep (se 1 (by rfl) ⟨1804028, by rfl⟩ : syracuseStep 2405371 = 3608057) B3608057
theorem B3207161 : Blo 1899435 3207161 := bstep (se 2 (by rfl) ⟨1202685, by rfl⟩ : syracuseStep 3207161 = 2405371) B2405371
theorem B2138107 : Blo 1899435 2138107 := bstep (se 1 (by rfl) ⟨1603580, by rfl⟩ : syracuseStep 2138107 = 3207161) B3207161
theorem B2850809 : Blo 1899435 2850809 := bstep (se 2 (by rfl) ⟨1069053, by rfl⟩ : syracuseStep 2850809 = 2138107) B2138107
theorem B1900539 : Blo 1899435 1900539 := bstep (se 1 (by rfl) ⟨1425404, by rfl⟩ : syracuseStep 1900539 = 2850809) B2850809
theorem B2603677 : Blo 1899435 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B3471569 : Blo 1899435 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B2314379 : Blo 1899435 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B6171677 : Blo 1899435 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B4114451 : Blo 1899435 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B702199637 : Blo 1899435 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B468133091 : Blo 1899435 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B312088727 : Blo 1899435 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B832236605 : Blo 1899435 832236605 := bstep (se 3 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 832236605 = 312088727) B312088727
theorem B554824403 : Blo 1899435 554824403 := bstep (se 1 (by rfl) ⟨416118302, by rfl⟩ : syracuseStep 554824403 = 832236605) B832236605
theorem B369882935 : Blo 1899435 369882935 := bstep (se 1 (by rfl) ⟨277412201, by rfl⟩ : syracuseStep 369882935 = 554824403) B554824403
theorem B246588623 : Blo 1899435 246588623 := bstep (se 1 (by rfl) ⟨184941467, by rfl⟩ : syracuseStep 246588623 = 369882935) B369882935
theorem B164392415 : Blo 1899435 164392415 := bstep (se 1 (by rfl) ⟨123294311, by rfl⟩ : syracuseStep 164392415 = 246588623) B246588623
theorem B109594943 : Blo 1899435 109594943 := bstep (se 1 (by rfl) ⟨82196207, by rfl⟩ : syracuseStep 109594943 = 164392415) B164392415
theorem B73063295 : Blo 1899435 73063295 := bstep (se 1 (by rfl) ⟨54797471, by rfl⟩ : syracuseStep 73063295 = 109594943) B109594943
theorem B48708863 : Blo 1899435 48708863 := bstep (se 1 (by rfl) ⟨36531647, by rfl⟩ : syracuseStep 48708863 = 73063295) B73063295
theorem B32472575 : Blo 1899435 32472575 := bstep (se 1 (by rfl) ⟨24354431, by rfl⟩ : syracuseStep 32472575 = 48708863) B48708863
theorem B21648383 : Blo 1899435 21648383 := bstep (se 1 (by rfl) ⟨16236287, by rfl⟩ : syracuseStep 21648383 = 32472575) B32472575
theorem B14432255 : Blo 1899435 14432255 := bstep (se 1 (by rfl) ⟨10824191, by rfl⟩ : syracuseStep 14432255 = 21648383) B21648383
theorem B9621503 : Blo 1899435 9621503 := bstep (se 1 (by rfl) ⟨7216127, by rfl⟩ : syracuseStep 9621503 = 14432255) B14432255
theorem B6414335 : Blo 1899435 6414335 := bstep (se 1 (by rfl) ⟨4810751, by rfl⟩ : syracuseStep 6414335 = 9621503) B9621503
theorem B4276223 : Blo 1899435 4276223 := bstep (se 1 (by rfl) ⟨3207167, by rfl⟩ : syracuseStep 4276223 = 6414335) B6414335
theorem B2850815 : Blo 1899435 2850815 := bstep (se 1 (by rfl) ⟨2138111, by rfl⟩ : syracuseStep 2850815 = 4276223) B4276223
theorem B1900543 : Blo 1899435 1900543 := bstep (se 1 (by rfl) ⟨1425407, by rfl⟩ : syracuseStep 1900543 = 2850815) B2850815
theorem B2850821 : Blo 1899435 2850821 := bbase (se 4 (by rfl) ⟨267264, by rfl⟩ : syracuseStep 2850821 = 534529) (by norm_num)
theorem B1900547 : Blo 1899435 1900547 := bstep (se 1 (by rfl) ⟨1425410, by rfl⟩ : syracuseStep 1900547 = 2850821) B2850821
theorem B3207181 : Blo 1899435 3207181 := bbase (se 3 (by rfl) ⟨601346, by rfl⟩ : syracuseStep 3207181 = 1202693) (by norm_num)
theorem B4276241 : Blo 1899435 4276241 := bstep (se 2 (by rfl) ⟨1603590, by rfl⟩ : syracuseStep 4276241 = 3207181) B3207181
theorem B2850827 : Blo 1899435 2850827 := bstep (se 1 (by rfl) ⟨2138120, by rfl⟩ : syracuseStep 2850827 = 4276241) B4276241
theorem B1900551 : Blo 1899435 1900551 := bstep (se 1 (by rfl) ⟨1425413, by rfl⟩ : syracuseStep 1900551 = 2850827) B2850827
theorem B2138125 : Blo 1899435 2138125 := bbase (se 3 (by rfl) ⟨400898, by rfl⟩ : syracuseStep 2138125 = 801797) (by norm_num)
theorem B2850833 : Blo 1899435 2850833 := bstep (se 2 (by rfl) ⟨1069062, by rfl⟩ : syracuseStep 2850833 = 2138125) B2138125
theorem B1900555 : Blo 1899435 1900555 := bstep (se 1 (by rfl) ⟨1425416, by rfl⟩ : syracuseStep 1900555 = 2850833) B2850833
theorem B6414389 : Blo 1899435 6414389 := bbase (se 5 (by rfl) ⟨300674, by rfl⟩ : syracuseStep 6414389 = 601349) (by norm_num)
theorem B4276259 : Blo 1899435 4276259 := bstep (se 1 (by rfl) ⟨3207194, by rfl⟩ : syracuseStep 4276259 = 6414389) B6414389
theorem B2850839 : Blo 1899435 2850839 := bstep (se 1 (by rfl) ⟨2138129, by rfl⟩ : syracuseStep 2850839 = 4276259) B4276259
theorem B1900559 : Blo 1899435 1900559 := bstep (se 1 (by rfl) ⟨1425419, by rfl⟩ : syracuseStep 1900559 = 2850839) B2850839
theorem B2850845 : Blo 1899435 2850845 := bbase (se 3 (by rfl) ⟨534533, by rfl⟩ : syracuseStep 2850845 = 1069067) (by norm_num)
theorem B1900563 : Blo 1899435 1900563 := bstep (se 1 (by rfl) ⟨1425422, by rfl⟩ : syracuseStep 1900563 = 2850845) B2850845
theorem B4276277 : Blo 1899435 4276277 := bbase (se 5 (by rfl) ⟨200450, by rfl⟩ : syracuseStep 4276277 = 400901) (by norm_num)
theorem B2850851 : Blo 1899435 2850851 := bstep (se 1 (by rfl) ⟨2138138, by rfl⟩ : syracuseStep 2850851 = 4276277) B4276277
theorem B1900567 : Blo 1899435 1900567 := bstep (se 1 (by rfl) ⟨1425425, by rfl⟩ : syracuseStep 1900567 = 2850851) B2850851
theorem B2057257 : Blo 1899435 2057257 := bbase (se 2 (by rfl) ⟨771471, by rfl⟩ : syracuseStep 2057257 = 1542943) (by norm_num)
theorem B10972037 : Blo 1899435 10972037 := bstep (se 4 (by rfl) ⟨1028628, by rfl⟩ : syracuseStep 10972037 = 2057257) B2057257
theorem B29258765 : Blo 1899435 29258765 := bstep (se 3 (by rfl) ⟨5486018, by rfl⟩ : syracuseStep 29258765 = 10972037) B10972037
theorem B19505843 : Blo 1899435 19505843 := bstep (se 1 (by rfl) ⟨14629382, by rfl⟩ : syracuseStep 19505843 = 29258765) B29258765
theorem B13003895 : Blo 1899435 13003895 := bstep (se 1 (by rfl) ⟨9752921, by rfl⟩ : syracuseStep 13003895 = 19505843) B19505843
theorem B8669263 : Blo 1899435 8669263 := bstep (se 1 (by rfl) ⟨6501947, by rfl⟩ : syracuseStep 8669263 = 13003895) B13003895
theorem B11559017 : Blo 1899435 11559017 := bstep (se 2 (by rfl) ⟨4334631, by rfl⟩ : syracuseStep 11559017 = 8669263) B8669263
theorem B7706011 : Blo 1899435 7706011 := bstep (se 1 (by rfl) ⟨5779508, by rfl⟩ : syracuseStep 7706011 = 11559017) B11559017
theorem B10274681 : Blo 1899435 10274681 := bstep (se 2 (by rfl) ⟨3853005, by rfl⟩ : syracuseStep 10274681 = 7706011) B7706011
theorem B6849787 : Blo 1899435 6849787 := bstep (se 1 (by rfl) ⟨5137340, by rfl⟩ : syracuseStep 6849787 = 10274681) B10274681
theorem B9133049 : Blo 1899435 9133049 := bstep (se 2 (by rfl) ⟨3424893, by rfl⟩ : syracuseStep 9133049 = 6849787) B6849787
theorem B6088699 : Blo 1899435 6088699 := bstep (se 1 (by rfl) ⟨4566524, by rfl⟩ : syracuseStep 6088699 = 9133049) B9133049
theorem B8118265 : Blo 1899435 8118265 := bstep (se 2 (by rfl) ⟨3044349, by rfl⟩ : syracuseStep 8118265 = 6088699) B6088699
theorem B10824353 : Blo 1899435 10824353 := bstep (se 2 (by rfl) ⟨4059132, by rfl⟩ : syracuseStep 10824353 = 8118265) B8118265
theorem B7216235 : Blo 1899435 7216235 := bstep (se 1 (by rfl) ⟨5412176, by rfl⟩ : syracuseStep 7216235 = 10824353) B10824353
theorem B4810823 : Blo 1899435 4810823 := bstep (se 1 (by rfl) ⟨3608117, by rfl⟩ : syracuseStep 4810823 = 7216235) B7216235
theorem B3207215 : Blo 1899435 3207215 := bstep (se 1 (by rfl) ⟨2405411, by rfl⟩ : syracuseStep 3207215 = 4810823) B4810823
theorem B2138143 : Blo 1899435 2138143 := bstep (se 1 (by rfl) ⟨1603607, by rfl⟩ : syracuseStep 2138143 = 3207215) B3207215
theorem B2850857 : Blo 1899435 2850857 := bstep (se 2 (by rfl) ⟨1069071, by rfl⟩ : syracuseStep 2850857 = 2138143) B2138143
theorem B1900571 : Blo 1899435 1900571 := bstep (se 1 (by rfl) ⟨1425428, by rfl⟩ : syracuseStep 1900571 = 2850857) B2850857
theorem B3853013 : Blo 1899435 3853013 := bbase (se 7 (by rfl) ⟨45152, by rfl⟩ : syracuseStep 3853013 = 90305) (by norm_num)
theorem B10274701 : Blo 1899435 10274701 := bstep (se 3 (by rfl) ⟨1926506, by rfl⟩ : syracuseStep 10274701 = 3853013) B3853013
theorem B13699601 : Blo 1899435 13699601 := bstep (se 2 (by rfl) ⟨5137350, by rfl⟩ : syracuseStep 13699601 = 10274701) B10274701
theorem B9133067 : Blo 1899435 9133067 := bstep (se 1 (by rfl) ⟨6849800, by rfl⟩ : syracuseStep 9133067 = 13699601) B13699601
theorem B6088711 : Blo 1899435 6088711 := bstep (se 1 (by rfl) ⟨4566533, by rfl⟩ : syracuseStep 6088711 = 9133067) B9133067
theorem B8118281 : Blo 1899435 8118281 := bstep (se 2 (by rfl) ⟨3044355, by rfl⟩ : syracuseStep 8118281 = 6088711) B6088711
theorem B5412187 : Blo 1899435 5412187 := bstep (se 1 (by rfl) ⟨4059140, by rfl⟩ : syracuseStep 5412187 = 8118281) B8118281
theorem B7216249 : Blo 1899435 7216249 := bstep (se 2 (by rfl) ⟨2706093, by rfl⟩ : syracuseStep 7216249 = 5412187) B5412187
theorem B9621665 : Blo 1899435 9621665 := bstep (se 2 (by rfl) ⟨3608124, by rfl⟩ : syracuseStep 9621665 = 7216249) B7216249
theorem B6414443 : Blo 1899435 6414443 := bstep (se 1 (by rfl) ⟨4810832, by rfl⟩ : syracuseStep 6414443 = 9621665) B9621665
theorem B4276295 : Blo 1899435 4276295 := bstep (se 1 (by rfl) ⟨3207221, by rfl⟩ : syracuseStep 4276295 = 6414443) B6414443
theorem B2850863 : Blo 1899435 2850863 := bstep (se 1 (by rfl) ⟨2138147, by rfl⟩ : syracuseStep 2850863 = 4276295) B4276295
theorem B1900575 : Blo 1899435 1900575 := bstep (se 1 (by rfl) ⟨1425431, by rfl⟩ : syracuseStep 1900575 = 2850863) B2850863
theorem B2850869 : Blo 1899435 2850869 := bbase (se 5 (by rfl) ⟨133634, by rfl⟩ : syracuseStep 2850869 = 267269) (by norm_num)
theorem B1900579 : Blo 1899435 1900579 := bstep (se 1 (by rfl) ⟨1425434, by rfl⟩ : syracuseStep 1900579 = 2850869) B2850869
theorem B4810853 : Blo 1899435 4810853 := bbase (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) (by norm_num)
theorem B3207235 : Blo 1899435 3207235 := bstep (se 1 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 3207235 = 4810853) B4810853
theorem B4276313 : Blo 1899435 4276313 := bstep (se 2 (by rfl) ⟨1603617, by rfl⟩ : syracuseStep 4276313 = 3207235) B3207235
theorem B2850875 : Blo 1899435 2850875 := bstep (se 1 (by rfl) ⟨2138156, by rfl⟩ : syracuseStep 2850875 = 4276313) B4276313
theorem B1900583 : Blo 1899435 1900583 := bstep (se 1 (by rfl) ⟨1425437, by rfl⟩ : syracuseStep 1900583 = 2850875) B2850875
theorem B2138161 : Blo 1899435 2138161 := bbase (se 2 (by rfl) ⟨801810, by rfl⟩ : syracuseStep 2138161 = 1603621) (by norm_num)
theorem B2850881 : Blo 1899435 2850881 := bstep (se 2 (by rfl) ⟨1069080, by rfl⟩ : syracuseStep 2850881 = 2138161) B2138161
theorem B1900587 : Blo 1899435 1900587 := bstep (se 1 (by rfl) ⟨1425440, by rfl⟩ : syracuseStep 1900587 = 2850881) B2850881
theorem B2438257 : Blo 1899435 2438257 := bbase (se 2 (by rfl) ⟨914346, by rfl⟩ : syracuseStep 2438257 = 1828693) (by norm_num)
theorem B3251009 : Blo 1899435 3251009 := bstep (se 2 (by rfl) ⟨1219128, by rfl⟩ : syracuseStep 3251009 = 2438257) B2438257
theorem B2167339 : Blo 1899435 2167339 := bstep (se 1 (by rfl) ⟨1625504, by rfl⟩ : syracuseStep 2167339 = 3251009) B3251009
theorem B2889785 : Blo 1899435 2889785 := bstep (se 2 (by rfl) ⟨1083669, by rfl⟩ : syracuseStep 2889785 = 2167339) B2167339
theorem B1926523 : Blo 1899435 1926523 := bstep (se 1 (by rfl) ⟨1444892, by rfl⟩ : syracuseStep 1926523 = 2889785) B2889785
theorem B10274789 : Blo 1899435 10274789 := bstep (se 4 (by rfl) ⟨963261, by rfl⟩ : syracuseStep 10274789 = 1926523) B1926523
theorem B6849859 : Blo 1899435 6849859 := bstep (se 1 (by rfl) ⟨5137394, by rfl⟩ : syracuseStep 6849859 = 10274789) B10274789
theorem B9133145 : Blo 1899435 9133145 := bstep (se 2 (by rfl) ⟨3424929, by rfl⟩ : syracuseStep 9133145 = 6849859) B6849859
theorem B6088763 : Blo 1899435 6088763 := bstep (se 1 (by rfl) ⟨4566572, by rfl⟩ : syracuseStep 6088763 = 9133145) B9133145
theorem B4059175 : Blo 1899435 4059175 := bstep (se 1 (by rfl) ⟨3044381, by rfl⟩ : syracuseStep 4059175 = 6088763) B6088763
theorem B5412233 : Blo 1899435 5412233 := bstep (se 2 (by rfl) ⟨2029587, by rfl⟩ : syracuseStep 5412233 = 4059175) B4059175
theorem B3608155 : Blo 1899435 3608155 := bstep (se 1 (by rfl) ⟨2706116, by rfl⟩ : syracuseStep 3608155 = 5412233) B5412233
theorem B4810873 : Blo 1899435 4810873 := bstep (se 2 (by rfl) ⟨1804077, by rfl⟩ : syracuseStep 4810873 = 3608155) B3608155
theorem B6414497 : Blo 1899435 6414497 := bstep (se 2 (by rfl) ⟨2405436, by rfl⟩ : syracuseStep 6414497 = 4810873) B4810873
theorem B4276331 : Blo 1899435 4276331 := bstep (se 1 (by rfl) ⟨3207248, by rfl⟩ : syracuseStep 4276331 = 6414497) B6414497
theorem B2850887 : Blo 1899435 2850887 := bstep (se 1 (by rfl) ⟨2138165, by rfl⟩ : syracuseStep 2850887 = 4276331) B4276331
theorem B1900591 : Blo 1899435 1900591 := bstep (se 1 (by rfl) ⟨1425443, by rfl⟩ : syracuseStep 1900591 = 2850887) B2850887
theorem B2850893 : Blo 1899435 2850893 := bbase (se 3 (by rfl) ⟨534542, by rfl⟩ : syracuseStep 2850893 = 1069085) (by norm_num)
theorem B1900595 : Blo 1899435 1900595 := bstep (se 1 (by rfl) ⟨1425446, by rfl⟩ : syracuseStep 1900595 = 2850893) B2850893
theorem B4276349 : Blo 1899435 4276349 := bbase (se 3 (by rfl) ⟨801815, by rfl⟩ : syracuseStep 4276349 = 1603631) (by norm_num)
theorem B2850899 : Blo 1899435 2850899 := bstep (se 1 (by rfl) ⟨2138174, by rfl⟩ : syracuseStep 2850899 = 4276349) B4276349
theorem B1900599 : Blo 1899435 1900599 := bstep (se 1 (by rfl) ⟨1425449, by rfl⟩ : syracuseStep 1900599 = 2850899) B2850899
theorem B3207269 : Blo 1899435 3207269 := bbase (se 4 (by rfl) ⟨300681, by rfl⟩ : syracuseStep 3207269 = 601363) (by norm_num)
theorem B2138179 : Blo 1899435 2138179 := bstep (se 1 (by rfl) ⟨1603634, by rfl⟩ : syracuseStep 2138179 = 3207269) B3207269
theorem B2850905 : Blo 1899435 2850905 := bstep (se 2 (by rfl) ⟨1069089, by rfl⟩ : syracuseStep 2850905 = 2138179) B2138179
theorem B1900603 : Blo 1899435 1900603 := bstep (se 1 (by rfl) ⟨1425452, by rfl⟩ : syracuseStep 1900603 = 2850905) B2850905
theorem B8669429 : Blo 1899435 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B5779619 : Blo 1899435 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B3853079 : Blo 1899435 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B2568719 : Blo 1899435 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B6849917 : Blo 1899435 6849917 := bstep (se 3 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 6849917 = 2568719) B2568719
theorem B4566611 : Blo 1899435 4566611 := bstep (se 1 (by rfl) ⟨3424958, by rfl⟩ : syracuseStep 4566611 = 6849917) B6849917
theorem B3044407 : Blo 1899435 3044407 := bstep (se 1 (by rfl) ⟨2283305, by rfl⟩ : syracuseStep 3044407 = 4566611) B4566611
theorem B4059209 : Blo 1899435 4059209 := bstep (se 2 (by rfl) ⟨1522203, by rfl⟩ : syracuseStep 4059209 = 3044407) B3044407
theorem B2706139 : Blo 1899435 2706139 := bstep (se 1 (by rfl) ⟨2029604, by rfl⟩ : syracuseStep 2706139 = 4059209) B4059209
theorem B14432741 : Blo 1899435 14432741 := bstep (se 4 (by rfl) ⟨1353069, by rfl⟩ : syracuseStep 14432741 = 2706139) B2706139
theorem B9621827 : Blo 1899435 9621827 := bstep (se 1 (by rfl) ⟨7216370, by rfl⟩ : syracuseStep 9621827 = 14432741) B14432741
theorem B6414551 : Blo 1899435 6414551 := bstep (se 1 (by rfl) ⟨4810913, by rfl⟩ : syracuseStep 6414551 = 9621827) B9621827
theorem B4276367 : Blo 1899435 4276367 := bstep (se 1 (by rfl) ⟨3207275, by rfl⟩ : syracuseStep 4276367 = 6414551) B6414551
theorem B2850911 : Blo 1899435 2850911 := bstep (se 1 (by rfl) ⟨2138183, by rfl⟩ : syracuseStep 2850911 = 4276367) B4276367
theorem B1900607 : Blo 1899435 1900607 := bstep (se 1 (by rfl) ⟨1425455, by rfl⟩ : syracuseStep 1900607 = 2850911) B2850911
theorem B2850917 : Blo 1899435 2850917 := bbase (se 4 (by rfl) ⟨267273, by rfl⟩ : syracuseStep 2850917 = 534547) (by norm_num)
theorem B1900611 : Blo 1899435 1900611 := bstep (se 1 (by rfl) ⟨1425458, by rfl⟩ : syracuseStep 1900611 = 2850917) B2850917
theorem B8229221 : Blo 1899435 8229221 := bbase (se 4 (by rfl) ⟨771489, by rfl⟩ : syracuseStep 8229221 = 1542979) (by norm_num)
theorem B5486147 : Blo 1899435 5486147 := bstep (se 1 (by rfl) ⟨4114610, by rfl⟩ : syracuseStep 5486147 = 8229221) B8229221
theorem B3657431 : Blo 1899435 3657431 := bstep (se 1 (by rfl) ⟨2743073, by rfl⟩ : syracuseStep 3657431 = 5486147) B5486147
theorem B9753149 : Blo 1899435 9753149 := bstep (se 3 (by rfl) ⟨1828715, by rfl⟩ : syracuseStep 9753149 = 3657431) B3657431
theorem B26008397 : Blo 1899435 26008397 := bstep (se 3 (by rfl) ⟨4876574, by rfl⟩ : syracuseStep 26008397 = 9753149) B9753149
theorem B17338931 : Blo 1899435 17338931 := bstep (se 1 (by rfl) ⟨13004198, by rfl⟩ : syracuseStep 17338931 = 26008397) B26008397
theorem B11559287 : Blo 1899435 11559287 := bstep (se 1 (by rfl) ⟨8669465, by rfl⟩ : syracuseStep 11559287 = 17338931) B17338931
theorem B7706191 : Blo 1899435 7706191 := bstep (se 1 (by rfl) ⟨5779643, by rfl⟩ : syracuseStep 7706191 = 11559287) B11559287
theorem B10274921 : Blo 1899435 10274921 := bstep (se 2 (by rfl) ⟨3853095, by rfl⟩ : syracuseStep 10274921 = 7706191) B7706191
theorem B6849947 : Blo 1899435 6849947 := bstep (se 1 (by rfl) ⟨5137460, by rfl⟩ : syracuseStep 6849947 = 10274921) B10274921
theorem B4566631 : Blo 1899435 4566631 := bstep (se 1 (by rfl) ⟨3424973, by rfl⟩ : syracuseStep 4566631 = 6849947) B6849947
theorem B6088841 : Blo 1899435 6088841 := bstep (se 2 (by rfl) ⟨2283315, by rfl⟩ : syracuseStep 6088841 = 4566631) B4566631
theorem B4059227 : Blo 1899435 4059227 := bstep (se 1 (by rfl) ⟨3044420, by rfl⟩ : syracuseStep 4059227 = 6088841) B6088841
theorem B2706151 : Blo 1899435 2706151 := bstep (se 1 (by rfl) ⟨2029613, by rfl⟩ : syracuseStep 2706151 = 4059227) B4059227
theorem B3608201 : Blo 1899435 3608201 := bstep (se 2 (by rfl) ⟨1353075, by rfl⟩ : syracuseStep 3608201 = 2706151) B2706151
theorem B2405467 : Blo 1899435 2405467 := bstep (se 1 (by rfl) ⟨1804100, by rfl⟩ : syracuseStep 2405467 = 3608201) B3608201
theorem B3207289 : Blo 1899435 3207289 := bstep (se 2 (by rfl) ⟨1202733, by rfl⟩ : syracuseStep 3207289 = 2405467) B2405467
theorem B4276385 : Blo 1899435 4276385 := bstep (se 2 (by rfl) ⟨1603644, by rfl⟩ : syracuseStep 4276385 = 3207289) B3207289
theorem B2850923 : Blo 1899435 2850923 := bstep (se 1 (by rfl) ⟨2138192, by rfl⟩ : syracuseStep 2850923 = 4276385) B4276385
theorem B1900615 : Blo 1899435 1900615 := bstep (se 1 (by rfl) ⟨1425461, by rfl⟩ : syracuseStep 1900615 = 2850923) B2850923
theorem B2138197 : Blo 1899435 2138197 := bbase (se 8 (by rfl) ⟨12528, by rfl⟩ : syracuseStep 2138197 = 25057) (by norm_num)
theorem B2850929 : Blo 1899435 2850929 := bstep (se 2 (by rfl) ⟨1069098, by rfl⟩ : syracuseStep 2850929 = 2138197) B2138197
theorem B1900619 : Blo 1899435 1900619 := bstep (se 1 (by rfl) ⟨1425464, by rfl⟩ : syracuseStep 1900619 = 2850929) B2850929
theorem B2405477 : Blo 1899435 2405477 := bbase (se 4 (by rfl) ⟨225513, by rfl⟩ : syracuseStep 2405477 = 451027) (by norm_num)
theorem B6414605 : Blo 1899435 6414605 := bstep (se 3 (by rfl) ⟨1202738, by rfl⟩ : syracuseStep 6414605 = 2405477) B2405477
theorem B4276403 : Blo 1899435 4276403 := bstep (se 1 (by rfl) ⟨3207302, by rfl⟩ : syracuseStep 4276403 = 6414605) B6414605
theorem B2850935 : Blo 1899435 2850935 := bstep (se 1 (by rfl) ⟨2138201, by rfl⟩ : syracuseStep 2850935 = 4276403) B4276403
theorem B1900623 : Blo 1899435 1900623 := bstep (se 1 (by rfl) ⟨1425467, by rfl⟩ : syracuseStep 1900623 = 2850935) B2850935
theorem B2850941 : Blo 1899435 2850941 := bbase (se 3 (by rfl) ⟨534551, by rfl⟩ : syracuseStep 2850941 = 1069103) (by norm_num)
theorem B1900627 : Blo 1899435 1900627 := bstep (se 1 (by rfl) ⟨1425470, by rfl⟩ : syracuseStep 1900627 = 2850941) B2850941
theorem B4276421 : Blo 1899435 4276421 := bbase (se 4 (by rfl) ⟨400914, by rfl⟩ : syracuseStep 4276421 = 801829) (by norm_num)
theorem B2850947 : Blo 1899435 2850947 := bstep (se 1 (by rfl) ⟨2138210, by rfl⟩ : syracuseStep 2850947 = 4276421) B4276421
theorem B1900631 : Blo 1899435 1900631 := bstep (se 1 (by rfl) ⟨1425473, by rfl⟩ : syracuseStep 1900631 = 2850947) B2850947
theorem B2568757 : Blo 1899435 2568757 := bbase (se 5 (by rfl) ⟨120410, by rfl⟩ : syracuseStep 2568757 = 240821) (by norm_num)
theorem B3425009 : Blo 1899435 3425009 := bstep (se 2 (by rfl) ⟨1284378, by rfl⟩ : syracuseStep 3425009 = 2568757) B2568757
theorem B9133357 : Blo 1899435 9133357 := bstep (se 3 (by rfl) ⟨1712504, by rfl⟩ : syracuseStep 9133357 = 3425009) B3425009
theorem B12177809 : Blo 1899435 12177809 := bstep (se 2 (by rfl) ⟨4566678, by rfl⟩ : syracuseStep 12177809 = 9133357) B9133357
theorem B8118539 : Blo 1899435 8118539 := bstep (se 1 (by rfl) ⟨6088904, by rfl⟩ : syracuseStep 8118539 = 12177809) B12177809
theorem B5412359 : Blo 1899435 5412359 := bstep (se 1 (by rfl) ⟨4059269, by rfl⟩ : syracuseStep 5412359 = 8118539) B8118539
theorem B3608239 : Blo 1899435 3608239 := bstep (se 1 (by rfl) ⟨2706179, by rfl⟩ : syracuseStep 3608239 = 5412359) B5412359
theorem B4810985 : Blo 1899435 4810985 := bstep (se 2 (by rfl) ⟨1804119, by rfl⟩ : syracuseStep 4810985 = 3608239) B3608239
theorem B3207323 : Blo 1899435 3207323 := bstep (se 1 (by rfl) ⟨2405492, by rfl⟩ : syracuseStep 3207323 = 4810985) B4810985
theorem B2138215 : Blo 1899435 2138215 := bstep (se 1 (by rfl) ⟨1603661, by rfl⟩ : syracuseStep 2138215 = 3207323) B3207323
theorem B2850953 : Blo 1899435 2850953 := bstep (se 2 (by rfl) ⟨1069107, by rfl⟩ : syracuseStep 2850953 = 2138215) B2138215
theorem B1900635 : Blo 1899435 1900635 := bstep (se 1 (by rfl) ⟨1425476, by rfl⟩ : syracuseStep 1900635 = 2850953) B2850953
theorem B9621989 : Blo 1899435 9621989 := bbase (se 4 (by rfl) ⟨902061, by rfl⟩ : syracuseStep 9621989 = 1804123) (by norm_num)
theorem B6414659 : Blo 1899435 6414659 := bstep (se 1 (by rfl) ⟨4810994, by rfl⟩ : syracuseStep 6414659 = 9621989) B9621989
theorem B4276439 : Blo 1899435 4276439 := bstep (se 1 (by rfl) ⟨3207329, by rfl⟩ : syracuseStep 4276439 = 6414659) B6414659
theorem B2850959 : Blo 1899435 2850959 := bstep (se 1 (by rfl) ⟨2138219, by rfl⟩ : syracuseStep 2850959 = 4276439) B4276439
theorem B1900639 : Blo 1899435 1900639 := bstep (se 1 (by rfl) ⟨1425479, by rfl⟩ : syracuseStep 1900639 = 2850959) B2850959
theorem B2850965 : Blo 1899435 2850965 := bbase (se 6 (by rfl) ⟨66819, by rfl⟩ : syracuseStep 2850965 = 133639) (by norm_num)
theorem B1900643 : Blo 1899435 1900643 := bstep (se 1 (by rfl) ⟨1425482, by rfl⟩ : syracuseStep 1900643 = 2850965) B2850965
theorem B2568773 : Blo 1899435 2568773 := bbase (se 4 (by rfl) ⟨240822, by rfl⟩ : syracuseStep 2568773 = 481645) (by norm_num)
theorem B6850061 : Blo 1899435 6850061 := bstep (se 3 (by rfl) ⟨1284386, by rfl⟩ : syracuseStep 6850061 = 2568773) B2568773
theorem B4566707 : Blo 1899435 4566707 := bstep (se 1 (by rfl) ⟨3425030, by rfl⟩ : syracuseStep 4566707 = 6850061) B6850061
theorem B3044471 : Blo 1899435 3044471 := bstep (se 1 (by rfl) ⟨2283353, by rfl⟩ : syracuseStep 3044471 = 4566707) B4566707
theorem B8118589 : Blo 1899435 8118589 := bstep (se 3 (by rfl) ⟨1522235, by rfl⟩ : syracuseStep 8118589 = 3044471) B3044471
theorem B10824785 : Blo 1899435 10824785 := bstep (se 2 (by rfl) ⟨4059294, by rfl⟩ : syracuseStep 10824785 = 8118589) B8118589
theorem B7216523 : Blo 1899435 7216523 := bstep (se 1 (by rfl) ⟨5412392, by rfl⟩ : syracuseStep 7216523 = 10824785) B10824785
theorem B4811015 : Blo 1899435 4811015 := bstep (se 1 (by rfl) ⟨3608261, by rfl⟩ : syracuseStep 4811015 = 7216523) B7216523
theorem B3207343 : Blo 1899435 3207343 := bstep (se 1 (by rfl) ⟨2405507, by rfl⟩ : syracuseStep 3207343 = 4811015) B4811015
theorem B4276457 : Blo 1899435 4276457 := bstep (se 2 (by rfl) ⟨1603671, by rfl⟩ : syracuseStep 4276457 = 3207343) B3207343
theorem B2850971 : Blo 1899435 2850971 := bstep (se 1 (by rfl) ⟨2138228, by rfl⟩ : syracuseStep 2850971 = 4276457) B4276457
theorem B1900647 : Blo 1899435 1900647 := bstep (se 1 (by rfl) ⟨1425485, by rfl⟩ : syracuseStep 1900647 = 2850971) B2850971
theorem B2138233 : Blo 1899435 2138233 := bbase (se 2 (by rfl) ⟨801837, by rfl⟩ : syracuseStep 2138233 = 1603675) (by norm_num)
theorem B2850977 : Blo 1899435 2850977 := bstep (se 2 (by rfl) ⟨1069116, by rfl⟩ : syracuseStep 2850977 = 2138233) B2138233
theorem B1900651 : Blo 1899435 1900651 := bstep (se 1 (by rfl) ⟨1425488, by rfl⟩ : syracuseStep 1900651 = 2850977) B2850977
theorem B3251117 : Blo 1899435 3251117 := bbase (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) (by norm_num)
theorem B8669645 : Blo 1899435 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B5779763 : Blo 1899435 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B3853175 : Blo 1899435 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B41100533 : Blo 1899435 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B27400355 : Blo 1899435 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B18266903 : Blo 1899435 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B12177935 : Blo 1899435 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B8118623 : Blo 1899435 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B5412415 : Blo 1899435 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B7216553 : Blo 1899435 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B4811035 : Blo 1899435 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B6414713 : Blo 1899435 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B4276475 : Blo 1899435 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B2850983 : Blo 1899435 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B1900655 : Blo 1899435 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B2850989 : Blo 1899435 2850989 := bbase (se 3 (by rfl) ⟨534560, by rfl⟩ : syracuseStep 2850989 = 1069121) (by norm_num)
theorem B1900659 : Blo 1899435 1900659 := bstep (se 1 (by rfl) ⟨1425494, by rfl⟩ : syracuseStep 1900659 = 2850989) B2850989
theorem B4276493 : Blo 1899435 4276493 := bbase (se 3 (by rfl) ⟨801842, by rfl⟩ : syracuseStep 4276493 = 1603685) (by norm_num)
theorem B2850995 : Blo 1899435 2850995 := bstep (se 1 (by rfl) ⟨2138246, by rfl⟩ : syracuseStep 2850995 = 4276493) B4276493
theorem B1900663 : Blo 1899435 1900663 := bstep (se 1 (by rfl) ⟨1425497, by rfl⟩ : syracuseStep 1900663 = 2850995) B2850995
theorem B2405533 : Blo 1899435 2405533 := bbase (se 3 (by rfl) ⟨451037, by rfl⟩ : syracuseStep 2405533 = 902075) (by norm_num)
theorem B3207377 : Blo 1899435 3207377 := bstep (se 2 (by rfl) ⟨1202766, by rfl⟩ : syracuseStep 3207377 = 2405533) B2405533
theorem B2138251 : Blo 1899435 2138251 := bstep (se 1 (by rfl) ⟨1603688, by rfl⟩ : syracuseStep 2138251 = 3207377) B3207377
theorem B2851001 : Blo 1899435 2851001 := bstep (se 2 (by rfl) ⟨1069125, by rfl⟩ : syracuseStep 2851001 = 2138251) B2138251
theorem B1900667 : Blo 1899435 1900667 := bstep (se 1 (by rfl) ⟨1425500, by rfl⟩ : syracuseStep 1900667 = 2851001) B2851001
theorem B3044509 : Blo 1899435 3044509 := bbase (se 3 (by rfl) ⟨570845, by rfl⟩ : syracuseStep 3044509 = 1141691) (by norm_num)
theorem B16237381 : Blo 1899435 16237381 := bstep (se 4 (by rfl) ⟨1522254, by rfl⟩ : syracuseStep 16237381 = 3044509) B3044509
theorem B21649841 : Blo 1899435 21649841 := bstep (se 2 (by rfl) ⟨8118690, by rfl⟩ : syracuseStep 21649841 = 16237381) B16237381
theorem B14433227 : Blo 1899435 14433227 := bstep (se 1 (by rfl) ⟨10824920, by rfl⟩ : syracuseStep 14433227 = 21649841) B21649841
theorem B9622151 : Blo 1899435 9622151 := bstep (se 1 (by rfl) ⟨7216613, by rfl⟩ : syracuseStep 9622151 = 14433227) B14433227
theorem B6414767 : Blo 1899435 6414767 := bstep (se 1 (by rfl) ⟨4811075, by rfl⟩ : syracuseStep 6414767 = 9622151) B9622151
theorem B4276511 : Blo 1899435 4276511 := bstep (se 1 (by rfl) ⟨3207383, by rfl⟩ : syracuseStep 4276511 = 6414767) B6414767
theorem B2851007 : Blo 1899435 2851007 := bstep (se 1 (by rfl) ⟨2138255, by rfl⟩ : syracuseStep 2851007 = 4276511) B4276511
theorem B1900671 : Blo 1899435 1900671 := bstep (se 1 (by rfl) ⟨1425503, by rfl⟩ : syracuseStep 1900671 = 2851007) B2851007
theorem B2851013 : Blo 1899435 2851013 := bbase (se 4 (by rfl) ⟨267282, by rfl⟩ : syracuseStep 2851013 = 534565) (by norm_num)
theorem B1900675 : Blo 1899435 1900675 := bstep (se 1 (by rfl) ⟨1425506, by rfl⟩ : syracuseStep 1900675 = 2851013) B2851013
theorem B3207397 : Blo 1899435 3207397 := bbase (se 4 (by rfl) ⟨300693, by rfl⟩ : syracuseStep 3207397 = 601387) (by norm_num)
theorem B4276529 : Blo 1899435 4276529 := bstep (se 2 (by rfl) ⟨1603698, by rfl⟩ : syracuseStep 4276529 = 3207397) B3207397
theorem B2851019 : Blo 1899435 2851019 := bstep (se 1 (by rfl) ⟨2138264, by rfl⟩ : syracuseStep 2851019 = 4276529) B4276529
theorem B1900679 : Blo 1899435 1900679 := bstep (se 1 (by rfl) ⟨1425509, by rfl⟩ : syracuseStep 1900679 = 2851019) B2851019
theorem B2138269 : Blo 1899435 2138269 := bbase (se 3 (by rfl) ⟨400925, by rfl⟩ : syracuseStep 2138269 = 801851) (by norm_num)
theorem B2851025 : Blo 1899435 2851025 := bstep (se 2 (by rfl) ⟨1069134, by rfl⟩ : syracuseStep 2851025 = 2138269) B2138269
theorem B1900683 : Blo 1899435 1900683 := bstep (se 1 (by rfl) ⟨1425512, by rfl⟩ : syracuseStep 1900683 = 2851025) B2851025
theorem B6414821 : Blo 1899435 6414821 := bbase (se 4 (by rfl) ⟨601389, by rfl⟩ : syracuseStep 6414821 = 1202779) (by norm_num)
theorem B4276547 : Blo 1899435 4276547 := bstep (se 1 (by rfl) ⟨3207410, by rfl⟩ : syracuseStep 4276547 = 6414821) B6414821
theorem B2851031 : Blo 1899435 2851031 := bstep (se 1 (by rfl) ⟨2138273, by rfl⟩ : syracuseStep 2851031 = 4276547) B4276547
theorem B1900687 : Blo 1899435 1900687 := bstep (se 1 (by rfl) ⟨1425515, by rfl⟩ : syracuseStep 1900687 = 2851031) B2851031
theorem B2851037 : Blo 1899435 2851037 := bbase (se 3 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 2851037 = 1069139) (by norm_num)
theorem B1900691 : Blo 1899435 1900691 := bstep (se 1 (by rfl) ⟨1425518, by rfl⟩ : syracuseStep 1900691 = 2851037) B2851037
theorem B4276565 : Blo 1899435 4276565 := bbase (se 10 (by rfl) ⟨6264, by rfl⟩ : syracuseStep 4276565 = 12529) (by norm_num)
theorem B2851043 : Blo 1899435 2851043 := bstep (se 1 (by rfl) ⟨2138282, by rfl⟩ : syracuseStep 2851043 = 4276565) B4276565
theorem B1900695 : Blo 1899435 1900695 := bstep (se 1 (by rfl) ⟨1425521, by rfl⟩ : syracuseStep 1900695 = 2851043) B2851043
theorem B3425125 : Blo 1899435 3425125 := bbase (se 4 (by rfl) ⟨321105, by rfl⟩ : syracuseStep 3425125 = 642211) (by norm_num)
theorem B4566833 : Blo 1899435 4566833 := bstep (se 2 (by rfl) ⟨1712562, by rfl⟩ : syracuseStep 4566833 = 3425125) B3425125
theorem B3044555 : Blo 1899435 3044555 := bstep (se 1 (by rfl) ⟨2283416, by rfl⟩ : syracuseStep 3044555 = 4566833) B4566833
theorem B2029703 : Blo 1899435 2029703 := bstep (se 1 (by rfl) ⟨1522277, by rfl⟩ : syracuseStep 2029703 = 3044555) B3044555
theorem B5412541 : Blo 1899435 5412541 := bstep (se 3 (by rfl) ⟨1014851, by rfl⟩ : syracuseStep 5412541 = 2029703) B2029703
theorem B7216721 : Blo 1899435 7216721 := bstep (se 2 (by rfl) ⟨2706270, by rfl⟩ : syracuseStep 7216721 = 5412541) B5412541
theorem B4811147 : Blo 1899435 4811147 := bstep (se 1 (by rfl) ⟨3608360, by rfl⟩ : syracuseStep 4811147 = 7216721) B7216721
theorem B3207431 : Blo 1899435 3207431 := bstep (se 1 (by rfl) ⟨2405573, by rfl⟩ : syracuseStep 3207431 = 4811147) B4811147
theorem B2138287 : Blo 1899435 2138287 := bstep (se 1 (by rfl) ⟨1603715, by rfl⟩ : syracuseStep 2138287 = 3207431) B3207431
theorem B2851049 : Blo 1899435 2851049 := bstep (se 2 (by rfl) ⟨1069143, by rfl⟩ : syracuseStep 2851049 = 2138287) B2138287
theorem B1900699 : Blo 1899435 1900699 := bstep (se 1 (by rfl) ⟨1425524, by rfl⟩ : syracuseStep 1900699 = 2851049) B2851049
theorem B6850261 : Blo 1899435 6850261 := bbase (se 7 (by rfl) ⟨80276, by rfl⟩ : syracuseStep 6850261 = 160553) (by norm_num)
theorem B36534725 : Blo 1899435 36534725 := bstep (se 4 (by rfl) ⟨3425130, by rfl⟩ : syracuseStep 36534725 = 6850261) B6850261
theorem B24356483 : Blo 1899435 24356483 := bstep (se 1 (by rfl) ⟨18267362, by rfl⟩ : syracuseStep 24356483 = 36534725) B36534725
theorem B16237655 : Blo 1899435 16237655 := bstep (se 1 (by rfl) ⟨12178241, by rfl⟩ : syracuseStep 16237655 = 24356483) B24356483
theorem B10825103 : Blo 1899435 10825103 := bstep (se 1 (by rfl) ⟨8118827, by rfl⟩ : syracuseStep 10825103 = 16237655) B16237655
theorem B7216735 : Blo 1899435 7216735 := bstep (se 1 (by rfl) ⟨5412551, by rfl⟩ : syracuseStep 7216735 = 10825103) B10825103
theorem B9622313 : Blo 1899435 9622313 := bstep (se 2 (by rfl) ⟨3608367, by rfl⟩ : syracuseStep 9622313 = 7216735) B7216735
theorem B6414875 : Blo 1899435 6414875 := bstep (se 1 (by rfl) ⟨4811156, by rfl⟩ : syracuseStep 6414875 = 9622313) B9622313
theorem B4276583 : Blo 1899435 4276583 := bstep (se 1 (by rfl) ⟨3207437, by rfl⟩ : syracuseStep 4276583 = 6414875) B6414875
theorem B2851055 : Blo 1899435 2851055 := bstep (se 1 (by rfl) ⟨2138291, by rfl⟩ : syracuseStep 2851055 = 4276583) B4276583
theorem B1900703 : Blo 1899435 1900703 := bstep (se 1 (by rfl) ⟨1425527, by rfl⟩ : syracuseStep 1900703 = 2851055) B2851055
theorem B2851061 : Blo 1899435 2851061 := bbase (se 5 (by rfl) ⟨133643, by rfl⟩ : syracuseStep 2851061 = 267287) (by norm_num)
theorem B1900707 : Blo 1899435 1900707 := bstep (se 1 (by rfl) ⟨1425530, by rfl⟩ : syracuseStep 1900707 = 2851061) B2851061
theorem B2929397 : Blo 1899435 2929397 := bbase (se 5 (by rfl) ⟨137315, by rfl⟩ : syracuseStep 2929397 = 274631) (by norm_num)
theorem B7811725 : Blo 1899435 7811725 := bstep (se 3 (by rfl) ⟨1464698, by rfl⟩ : syracuseStep 7811725 = 2929397) B2929397
theorem B10415633 : Blo 1899435 10415633 := bstep (se 2 (by rfl) ⟨3905862, by rfl⟩ : syracuseStep 10415633 = 7811725) B7811725
theorem B27775021 : Blo 1899435 27775021 := bstep (se 3 (by rfl) ⟨5207816, by rfl⟩ : syracuseStep 27775021 = 10415633) B10415633
theorem B37033361 : Blo 1899435 37033361 := bstep (se 2 (by rfl) ⟨13887510, by rfl⟩ : syracuseStep 37033361 = 27775021) B27775021
theorem B24688907 : Blo 1899435 24688907 := bstep (se 1 (by rfl) ⟨18516680, by rfl⟩ : syracuseStep 24688907 = 37033361) B37033361
theorem B16459271 : Blo 1899435 16459271 := bstep (se 1 (by rfl) ⟨12344453, by rfl⟩ : syracuseStep 16459271 = 24688907) B24688907
theorem B10972847 : Blo 1899435 10972847 := bstep (se 1 (by rfl) ⟨8229635, by rfl⟩ : syracuseStep 10972847 = 16459271) B16459271
theorem B7315231 : Blo 1899435 7315231 := bstep (se 1 (by rfl) ⟨5486423, by rfl⟩ : syracuseStep 7315231 = 10972847) B10972847
theorem B9753641 : Blo 1899435 9753641 := bstep (se 2 (by rfl) ⟨3657615, by rfl⟩ : syracuseStep 9753641 = 7315231) B7315231
theorem B6502427 : Blo 1899435 6502427 := bstep (se 1 (by rfl) ⟨4876820, by rfl⟩ : syracuseStep 6502427 = 9753641) B9753641
theorem B4334951 : Blo 1899435 4334951 := bstep (se 1 (by rfl) ⟨3251213, by rfl⟩ : syracuseStep 4334951 = 6502427) B6502427
theorem B2889967 : Blo 1899435 2889967 := bstep (se 1 (by rfl) ⟨2167475, by rfl⟩ : syracuseStep 2889967 = 4334951) B4334951
theorem B3853289 : Blo 1899435 3853289 := bstep (se 2 (by rfl) ⟨1444983, by rfl⟩ : syracuseStep 3853289 = 2889967) B2889967
theorem B10275437 : Blo 1899435 10275437 := bstep (se 3 (by rfl) ⟨1926644, by rfl⟩ : syracuseStep 10275437 = 3853289) B3853289
theorem B27401165 : Blo 1899435 27401165 := bstep (se 3 (by rfl) ⟨5137718, by rfl⟩ : syracuseStep 27401165 = 10275437) B10275437
theorem B18267443 : Blo 1899435 18267443 := bstep (se 1 (by rfl) ⟨13700582, by rfl⟩ : syracuseStep 18267443 = 27401165) B27401165
theorem B12178295 : Blo 1899435 12178295 := bstep (se 1 (by rfl) ⟨9133721, by rfl⟩ : syracuseStep 12178295 = 18267443) B18267443
theorem B8118863 : Blo 1899435 8118863 := bstep (se 1 (by rfl) ⟨6089147, by rfl⟩ : syracuseStep 8118863 = 12178295) B12178295
theorem B5412575 : Blo 1899435 5412575 := bstep (se 1 (by rfl) ⟨4059431, by rfl⟩ : syracuseStep 5412575 = 8118863) B8118863
theorem B3608383 : Blo 1899435 3608383 := bstep (se 1 (by rfl) ⟨2706287, by rfl⟩ : syracuseStep 3608383 = 5412575) B5412575
theorem B4811177 : Blo 1899435 4811177 := bstep (se 2 (by rfl) ⟨1804191, by rfl⟩ : syracuseStep 4811177 = 3608383) B3608383
theorem B3207451 : Blo 1899435 3207451 := bstep (se 1 (by rfl) ⟨2405588, by rfl⟩ : syracuseStep 3207451 = 4811177) B4811177
theorem B4276601 : Blo 1899435 4276601 := bstep (se 2 (by rfl) ⟨1603725, by rfl⟩ : syracuseStep 4276601 = 3207451) B3207451
theorem B2851067 : Blo 1899435 2851067 := bstep (se 1 (by rfl) ⟨2138300, by rfl⟩ : syracuseStep 2851067 = 4276601) B4276601
theorem B1900711 : Blo 1899435 1900711 := bstep (se 1 (by rfl) ⟨1425533, by rfl⟩ : syracuseStep 1900711 = 2851067) B2851067
theorem B2138305 : Blo 1899435 2138305 := bbase (se 2 (by rfl) ⟨801864, by rfl⟩ : syracuseStep 2138305 = 1603729) (by norm_num)
theorem B2851073 : Blo 1899435 2851073 := bstep (se 2 (by rfl) ⟨1069152, by rfl⟩ : syracuseStep 2851073 = 2138305) B2138305
theorem B1900715 : Blo 1899435 1900715 := bstep (se 1 (by rfl) ⟨1425536, by rfl⟩ : syracuseStep 1900715 = 2851073) B2851073
theorem B4811197 : Blo 1899435 4811197 := bbase (se 3 (by rfl) ⟨902099, by rfl⟩ : syracuseStep 4811197 = 1804199) (by norm_num)
theorem B6414929 : Blo 1899435 6414929 := bstep (se 2 (by rfl) ⟨2405598, by rfl⟩ : syracuseStep 6414929 = 4811197) B4811197
theorem B4276619 : Blo 1899435 4276619 := bstep (se 1 (by rfl) ⟨3207464, by rfl⟩ : syracuseStep 4276619 = 6414929) B6414929
theorem B2851079 : Blo 1899435 2851079 := bstep (se 1 (by rfl) ⟨2138309, by rfl⟩ : syracuseStep 2851079 = 4276619) B4276619
theorem B1900719 : Blo 1899435 1900719 := bstep (se 1 (by rfl) ⟨1425539, by rfl⟩ : syracuseStep 1900719 = 2851079) B2851079
theorem B2851085 : Blo 1899435 2851085 := bbase (se 3 (by rfl) ⟨534578, by rfl⟩ : syracuseStep 2851085 = 1069157) (by norm_num)
theorem B1900723 : Blo 1899435 1900723 := bstep (se 1 (by rfl) ⟨1425542, by rfl⟩ : syracuseStep 1900723 = 2851085) B2851085
theorem B4276637 : Blo 1899435 4276637 := bbase (se 3 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 4276637 = 1603739) (by norm_num)
theorem B2851091 : Blo 1899435 2851091 := bstep (se 1 (by rfl) ⟨2138318, by rfl⟩ : syracuseStep 2851091 = 4276637) B4276637
theorem B1900727 : Blo 1899435 1900727 := bstep (se 1 (by rfl) ⟨1425545, by rfl⟩ : syracuseStep 1900727 = 2851091) B2851091
theorem B3207485 : Blo 1899435 3207485 := bbase (se 3 (by rfl) ⟨601403, by rfl⟩ : syracuseStep 3207485 = 1202807) (by norm_num)
theorem B2138323 : Blo 1899435 2138323 := bstep (se 1 (by rfl) ⟨1603742, by rfl⟩ : syracuseStep 2138323 = 3207485) B3207485
theorem B2851097 : Blo 1899435 2851097 := bstep (se 2 (by rfl) ⟨1069161, by rfl⟩ : syracuseStep 2851097 = 2138323) B2138323
theorem B1900731 : Blo 1899435 1900731 := bstep (se 1 (by rfl) ⟨1425548, by rfl⟩ : syracuseStep 1900731 = 2851097) B2851097
theorem B2029741 : Blo 1899435 2029741 := bbase (se 3 (by rfl) ⟨380576, by rfl⟩ : syracuseStep 2029741 = 761153) (by norm_num)
theorem B10825285 : Blo 1899435 10825285 := bstep (se 4 (by rfl) ⟨1014870, by rfl⟩ : syracuseStep 10825285 = 2029741) B2029741
theorem B14433713 : Blo 1899435 14433713 := bstep (se 2 (by rfl) ⟨5412642, by rfl⟩ : syracuseStep 14433713 = 10825285) B10825285
theorem B9622475 : Blo 1899435 9622475 := bstep (se 1 (by rfl) ⟨7216856, by rfl⟩ : syracuseStep 9622475 = 14433713) B14433713
theorem B6414983 : Blo 1899435 6414983 := bstep (se 1 (by rfl) ⟨4811237, by rfl⟩ : syracuseStep 6414983 = 9622475) B9622475
theorem B4276655 : Blo 1899435 4276655 := bstep (se 1 (by rfl) ⟨3207491, by rfl⟩ : syracuseStep 4276655 = 6414983) B6414983
theorem B2851103 : Blo 1899435 2851103 := bstep (se 1 (by rfl) ⟨2138327, by rfl⟩ : syracuseStep 2851103 = 4276655) B4276655
theorem B1900735 : Blo 1899435 1900735 := bstep (se 1 (by rfl) ⟨1425551, by rfl⟩ : syracuseStep 1900735 = 2851103) B2851103
theorem B2851109 : Blo 1899435 2851109 := bbase (se 4 (by rfl) ⟨267291, by rfl⟩ : syracuseStep 2851109 = 534583) (by norm_num)
theorem B1900739 : Blo 1899435 1900739 := bstep (se 1 (by rfl) ⟨1425554, by rfl⟩ : syracuseStep 1900739 = 2851109) B2851109
theorem B2405629 : Blo 1899435 2405629 := bbase (se 3 (by rfl) ⟨451055, by rfl⟩ : syracuseStep 2405629 = 902111) (by norm_num)
theorem B3207505 : Blo 1899435 3207505 := bstep (se 2 (by rfl) ⟨1202814, by rfl⟩ : syracuseStep 3207505 = 2405629) B2405629
theorem B4276673 : Blo 1899435 4276673 := bstep (se 2 (by rfl) ⟨1603752, by rfl⟩ : syracuseStep 4276673 = 3207505) B3207505
theorem B2851115 : Blo 1899435 2851115 := bstep (se 1 (by rfl) ⟨2138336, by rfl⟩ : syracuseStep 2851115 = 4276673) B4276673
theorem B1900743 : Blo 1899435 1900743 := bstep (se 1 (by rfl) ⟨1425557, by rfl⟩ : syracuseStep 1900743 = 2851115) B2851115
theorem B2138341 : Blo 1899435 2138341 := bbase (se 4 (by rfl) ⟨200469, by rfl⟩ : syracuseStep 2138341 = 400939) (by norm_num)
theorem B2851121 : Blo 1899435 2851121 := bstep (se 2 (by rfl) ⟨1069170, by rfl⟩ : syracuseStep 2851121 = 2138341) B2138341
theorem B1900747 : Blo 1899435 1900747 := bstep (se 1 (by rfl) ⟨1425560, by rfl⟩ : syracuseStep 1900747 = 2851121) B2851121
theorem B4059517 : Blo 1899435 4059517 := bbase (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) (by norm_num)
theorem B5412689 : Blo 1899435 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B3608459 : Blo 1899435 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B2405639 : Blo 1899435 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B6415037 : Blo 1899435 6415037 := bstep (se 3 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 6415037 = 2405639) B2405639
theorem B4276691 : Blo 1899435 4276691 := bstep (se 1 (by rfl) ⟨3207518, by rfl⟩ : syracuseStep 4276691 = 6415037) B6415037
theorem B2851127 : Blo 1899435 2851127 := bstep (se 1 (by rfl) ⟨2138345, by rfl⟩ : syracuseStep 2851127 = 4276691) B4276691
theorem B1900751 : Blo 1899435 1900751 := bstep (se 1 (by rfl) ⟨1425563, by rfl⟩ : syracuseStep 1900751 = 2851127) B2851127
theorem B2851133 : Blo 1899435 2851133 := bbase (se 3 (by rfl) ⟨534587, by rfl⟩ : syracuseStep 2851133 = 1069175) (by norm_num)
theorem B1900755 : Blo 1899435 1900755 := bstep (se 1 (by rfl) ⟨1425566, by rfl⟩ : syracuseStep 1900755 = 2851133) B2851133
theorem B4276709 : Blo 1899435 4276709 := bbase (se 4 (by rfl) ⟨400941, by rfl⟩ : syracuseStep 4276709 = 801883) (by norm_num)
theorem B2851139 : Blo 1899435 2851139 := bstep (se 1 (by rfl) ⟨2138354, by rfl⟩ : syracuseStep 2851139 = 4276709) B4276709
theorem B1900759 : Blo 1899435 1900759 := bstep (se 1 (by rfl) ⟨1425569, by rfl⟩ : syracuseStep 1900759 = 2851139) B2851139
theorem B4811309 : Blo 1899435 4811309 := bbase (se 3 (by rfl) ⟨902120, by rfl⟩ : syracuseStep 4811309 = 1804241) (by norm_num)
theorem B3207539 : Blo 1899435 3207539 := bstep (se 1 (by rfl) ⟨2405654, by rfl⟩ : syracuseStep 3207539 = 4811309) B4811309
theorem B2138359 : Blo 1899435 2138359 := bstep (se 1 (by rfl) ⟨1603769, by rfl⟩ : syracuseStep 2138359 = 3207539) B3207539
theorem B2851145 : Blo 1899435 2851145 := bstep (se 2 (by rfl) ⟨1069179, by rfl⟩ : syracuseStep 2851145 = 2138359) B2138359
theorem B1900763 : Blo 1899435 1900763 := bstep (se 1 (by rfl) ⟨1425572, by rfl⟩ : syracuseStep 1900763 = 2851145) B2851145
theorem B7315445 : Blo 1899435 7315445 := bbase (se 5 (by rfl) ⟨342911, by rfl⟩ : syracuseStep 7315445 = 685823) (by norm_num)
theorem B19507853 : Blo 1899435 19507853 := bstep (se 3 (by rfl) ⟨3657722, by rfl⟩ : syracuseStep 19507853 = 7315445) B7315445
theorem B13005235 : Blo 1899435 13005235 := bstep (se 1 (by rfl) ⟨9753926, by rfl⟩ : syracuseStep 13005235 = 19507853) B19507853
theorem B17340313 : Blo 1899435 17340313 := bstep (se 2 (by rfl) ⟨6502617, by rfl⟩ : syracuseStep 17340313 = 13005235) B13005235
theorem B23120417 : Blo 1899435 23120417 := bstep (se 2 (by rfl) ⟨8670156, by rfl⟩ : syracuseStep 23120417 = 17340313) B17340313
theorem B15413611 : Blo 1899435 15413611 := bstep (se 1 (by rfl) ⟨11560208, by rfl⟩ : syracuseStep 15413611 = 23120417) B23120417
theorem B20551481 : Blo 1899435 20551481 := bstep (se 2 (by rfl) ⟨7706805, by rfl⟩ : syracuseStep 20551481 = 15413611) B15413611
theorem B13700987 : Blo 1899435 13700987 := bstep (se 1 (by rfl) ⟨10275740, by rfl⟩ : syracuseStep 13700987 = 20551481) B20551481
theorem B9133991 : Blo 1899435 9133991 := bstep (se 1 (by rfl) ⟨6850493, by rfl⟩ : syracuseStep 9133991 = 13700987) B13700987
theorem B6089327 : Blo 1899435 6089327 := bstep (se 1 (by rfl) ⟨4566995, by rfl⟩ : syracuseStep 6089327 = 9133991) B9133991
theorem B4059551 : Blo 1899435 4059551 := bstep (se 1 (by rfl) ⟨3044663, by rfl⟩ : syracuseStep 4059551 = 6089327) B6089327
theorem B2706367 : Blo 1899435 2706367 := bstep (se 1 (by rfl) ⟨2029775, by rfl⟩ : syracuseStep 2706367 = 4059551) B4059551
theorem B3608489 : Blo 1899435 3608489 := bstep (se 2 (by rfl) ⟨1353183, by rfl⟩ : syracuseStep 3608489 = 2706367) B2706367
theorem B9622637 : Blo 1899435 9622637 := bstep (se 3 (by rfl) ⟨1804244, by rfl⟩ : syracuseStep 9622637 = 3608489) B3608489
theorem B6415091 : Blo 1899435 6415091 := bstep (se 1 (by rfl) ⟨4811318, by rfl⟩ : syracuseStep 6415091 = 9622637) B9622637
theorem B4276727 : Blo 1899435 4276727 := bstep (se 1 (by rfl) ⟨3207545, by rfl⟩ : syracuseStep 4276727 = 6415091) B6415091
theorem B2851151 : Blo 1899435 2851151 := bstep (se 1 (by rfl) ⟨2138363, by rfl⟩ : syracuseStep 2851151 = 4276727) B4276727
theorem B1900767 : Blo 1899435 1900767 := bstep (se 1 (by rfl) ⟨1425575, by rfl⟩ : syracuseStep 1900767 = 2851151) B2851151
theorem B2851157 : Blo 1899435 2851157 := bbase (se 10 (by rfl) ⟨4176, by rfl⟩ : syracuseStep 2851157 = 8353) (by norm_num)
theorem B1900771 : Blo 1899435 1900771 := bstep (se 1 (by rfl) ⟨1425578, by rfl⟩ : syracuseStep 1900771 = 2851157) B2851157
theorem B5412757 : Blo 1899435 5412757 := bbase (se 6 (by rfl) ⟨126861, by rfl⟩ : syracuseStep 5412757 = 253723) (by norm_num)
theorem B7217009 : Blo 1899435 7217009 := bstep (se 2 (by rfl) ⟨2706378, by rfl⟩ : syracuseStep 7217009 = 5412757) B5412757
theorem B4811339 : Blo 1899435 4811339 := bstep (se 1 (by rfl) ⟨3608504, by rfl⟩ : syracuseStep 4811339 = 7217009) B7217009
theorem B3207559 : Blo 1899435 3207559 := bstep (se 1 (by rfl) ⟨2405669, by rfl⟩ : syracuseStep 3207559 = 4811339) B4811339
theorem B4276745 : Blo 1899435 4276745 := bstep (se 2 (by rfl) ⟨1603779, by rfl⟩ : syracuseStep 4276745 = 3207559) B3207559
theorem B2851163 : Blo 1899435 2851163 := bstep (se 1 (by rfl) ⟨2138372, by rfl⟩ : syracuseStep 2851163 = 4276745) B4276745
theorem B1900775 : Blo 1899435 1900775 := bstep (se 1 (by rfl) ⟨1425581, by rfl⟩ : syracuseStep 1900775 = 2851163) B2851163
theorem B2138377 : Blo 1899435 2138377 := bbase (se 2 (by rfl) ⟨801891, by rfl⟩ : syracuseStep 2138377 = 1603783) (by norm_num)
theorem B2851169 : Blo 1899435 2851169 := bstep (se 2 (by rfl) ⟨1069188, by rfl⟩ : syracuseStep 2851169 = 2138377) B2138377
theorem B1900779 : Blo 1899435 1900779 := bstep (se 1 (by rfl) ⟨1425584, by rfl⟩ : syracuseStep 1900779 = 2851169) B2851169
theorem B4877005 : Blo 1899435 4877005 := bbase (se 3 (by rfl) ⟨914438, by rfl⟩ : syracuseStep 4877005 = 1828877) (by norm_num)
theorem B6502673 : Blo 1899435 6502673 := bstep (se 2 (by rfl) ⟨2438502, by rfl⟩ : syracuseStep 6502673 = 4877005) B4877005
theorem B4335115 : Blo 1899435 4335115 := bstep (se 1 (by rfl) ⟨3251336, by rfl⟩ : syracuseStep 4335115 = 6502673) B6502673
theorem B5780153 : Blo 1899435 5780153 := bstep (se 2 (by rfl) ⟨2167557, by rfl⟩ : syracuseStep 5780153 = 4335115) B4335115
theorem B3853435 : Blo 1899435 3853435 := bstep (se 1 (by rfl) ⟨2890076, by rfl⟩ : syracuseStep 3853435 = 5780153) B5780153
theorem B5137913 : Blo 1899435 5137913 := bstep (se 2 (by rfl) ⟨1926717, by rfl⟩ : syracuseStep 5137913 = 3853435) B3853435
theorem B3425275 : Blo 1899435 3425275 := bstep (se 1 (by rfl) ⟨2568956, by rfl⟩ : syracuseStep 3425275 = 5137913) B5137913
theorem B4567033 : Blo 1899435 4567033 := bstep (se 2 (by rfl) ⟨1712637, by rfl⟩ : syracuseStep 4567033 = 3425275) B3425275
theorem B24357509 : Blo 1899435 24357509 := bstep (se 4 (by rfl) ⟨2283516, by rfl⟩ : syracuseStep 24357509 = 4567033) B4567033
theorem B16238339 : Blo 1899435 16238339 := bstep (se 1 (by rfl) ⟨12178754, by rfl⟩ : syracuseStep 16238339 = 24357509) B24357509
theorem B10825559 : Blo 1899435 10825559 := bstep (se 1 (by rfl) ⟨8119169, by rfl⟩ : syracuseStep 10825559 = 16238339) B16238339
theorem B7217039 : Blo 1899435 7217039 := bstep (se 1 (by rfl) ⟨5412779, by rfl⟩ : syracuseStep 7217039 = 10825559) B10825559
theorem B4811359 : Blo 1899435 4811359 := bstep (se 1 (by rfl) ⟨3608519, by rfl⟩ : syracuseStep 4811359 = 7217039) B7217039
theorem B6415145 : Blo 1899435 6415145 := bstep (se 2 (by rfl) ⟨2405679, by rfl⟩ : syracuseStep 6415145 = 4811359) B4811359
theorem B4276763 : Blo 1899435 4276763 := bstep (se 1 (by rfl) ⟨3207572, by rfl⟩ : syracuseStep 4276763 = 6415145) B6415145
theorem B2851175 : Blo 1899435 2851175 := bstep (se 1 (by rfl) ⟨2138381, by rfl⟩ : syracuseStep 2851175 = 4276763) B4276763
theorem B1900783 : Blo 1899435 1900783 := bstep (se 1 (by rfl) ⟨1425587, by rfl⟩ : syracuseStep 1900783 = 2851175) B2851175
theorem B2851181 : Blo 1899435 2851181 := bbase (se 3 (by rfl) ⟨534596, by rfl⟩ : syracuseStep 2851181 = 1069193) (by norm_num)
theorem B1900787 : Blo 1899435 1900787 := bstep (se 1 (by rfl) ⟨1425590, by rfl⟩ : syracuseStep 1900787 = 2851181) B2851181
theorem B4276781 : Blo 1899435 4276781 := bbase (se 3 (by rfl) ⟨801896, by rfl⟩ : syracuseStep 4276781 = 1603793) (by norm_num)
theorem B2851187 : Blo 1899435 2851187 := bstep (se 1 (by rfl) ⟨2138390, by rfl⟩ : syracuseStep 2851187 = 4276781) B4276781
theorem B1900791 : Blo 1899435 1900791 := bstep (se 1 (by rfl) ⟨1425593, by rfl⟩ : syracuseStep 1900791 = 2851187) B2851187
theorem B10275893 : Blo 1899435 10275893 := bbase (se 5 (by rfl) ⟨481682, by rfl⟩ : syracuseStep 10275893 = 963365) (by norm_num)
theorem B6850595 : Blo 1899435 6850595 := bstep (se 1 (by rfl) ⟨5137946, by rfl⟩ : syracuseStep 6850595 = 10275893) B10275893
theorem B18268253 : Blo 1899435 18268253 := bstep (se 3 (by rfl) ⟨3425297, by rfl⟩ : syracuseStep 18268253 = 6850595) B6850595
theorem B12178835 : Blo 1899435 12178835 := bstep (se 1 (by rfl) ⟨9134126, by rfl⟩ : syracuseStep 12178835 = 18268253) B18268253
theorem B8119223 : Blo 1899435 8119223 := bstep (se 1 (by rfl) ⟨6089417, by rfl⟩ : syracuseStep 8119223 = 12178835) B12178835
theorem B5412815 : Blo 1899435 5412815 := bstep (se 1 (by rfl) ⟨4059611, by rfl⟩ : syracuseStep 5412815 = 8119223) B8119223
theorem B3608543 : Blo 1899435 3608543 := bstep (se 1 (by rfl) ⟨2706407, by rfl⟩ : syracuseStep 3608543 = 5412815) B5412815
theorem B2405695 : Blo 1899435 2405695 := bstep (se 1 (by rfl) ⟨1804271, by rfl⟩ : syracuseStep 2405695 = 3608543) B3608543
theorem B3207593 : Blo 1899435 3207593 := bstep (se 2 (by rfl) ⟨1202847, by rfl⟩ : syracuseStep 3207593 = 2405695) B2405695
theorem B2138395 : Blo 1899435 2138395 := bstep (se 1 (by rfl) ⟨1603796, by rfl⟩ : syracuseStep 2138395 = 3207593) B3207593
theorem B2851193 : Blo 1899435 2851193 := bstep (se 2 (by rfl) ⟨1069197, by rfl⟩ : syracuseStep 2851193 = 2138395) B2138395
theorem B1900795 : Blo 1899435 1900795 := bstep (se 1 (by rfl) ⟨1425596, by rfl⟩ : syracuseStep 1900795 = 2851193) B2851193
theorem B32476949 : Blo 1899435 32476949 := bbase (se 6 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 32476949 = 1522357) (by norm_num)
theorem B21651299 : Blo 1899435 21651299 := bstep (se 1 (by rfl) ⟨16238474, by rfl⟩ : syracuseStep 21651299 = 32476949) B32476949
theorem B14434199 : Blo 1899435 14434199 := bstep (se 1 (by rfl) ⟨10825649, by rfl⟩ : syracuseStep 14434199 = 21651299) B21651299
theorem B9622799 : Blo 1899435 9622799 := bstep (se 1 (by rfl) ⟨7217099, by rfl⟩ : syracuseStep 9622799 = 14434199) B14434199
theorem B6415199 : Blo 1899435 6415199 := bstep (se 1 (by rfl) ⟨4811399, by rfl⟩ : syracuseStep 6415199 = 9622799) B9622799
theorem B4276799 : Blo 1899435 4276799 := bstep (se 1 (by rfl) ⟨3207599, by rfl⟩ : syracuseStep 4276799 = 6415199) B6415199
theorem B2851199 : Blo 1899435 2851199 := bstep (se 1 (by rfl) ⟨2138399, by rfl⟩ : syracuseStep 2851199 = 4276799) B4276799
theorem B1900799 : Blo 1899435 1900799 := bstep (se 1 (by rfl) ⟨1425599, by rfl⟩ : syracuseStep 1900799 = 2851199) B2851199
theorem B2851205 : Blo 1899435 2851205 := bbase (se 4 (by rfl) ⟨267300, by rfl⟩ : syracuseStep 2851205 = 534601) (by norm_num)
theorem B1900803 : Blo 1899435 1900803 := bstep (se 1 (by rfl) ⟨1425602, by rfl⟩ : syracuseStep 1900803 = 2851205) B2851205
theorem B3207613 : Blo 1899435 3207613 := bbase (se 3 (by rfl) ⟨601427, by rfl⟩ : syracuseStep 3207613 = 1202855) (by norm_num)
theorem B4276817 : Blo 1899435 4276817 := bstep (se 2 (by rfl) ⟨1603806, by rfl⟩ : syracuseStep 4276817 = 3207613) B3207613
theorem B2851211 : Blo 1899435 2851211 := bstep (se 1 (by rfl) ⟨2138408, by rfl⟩ : syracuseStep 2851211 = 4276817) B4276817
theorem B1900807 : Blo 1899435 1900807 := bstep (se 1 (by rfl) ⟨1425605, by rfl⟩ : syracuseStep 1900807 = 2851211) B2851211
theorem B2138413 : Blo 1899435 2138413 := bbase (se 3 (by rfl) ⟨400952, by rfl⟩ : syracuseStep 2138413 = 801905) (by norm_num)
theorem B2851217 : Blo 1899435 2851217 := bstep (se 2 (by rfl) ⟨1069206, by rfl⟩ : syracuseStep 2851217 = 2138413) B2138413
theorem B1900811 : Blo 1899435 1900811 := bstep (se 1 (by rfl) ⟨1425608, by rfl⟩ : syracuseStep 1900811 = 2851217) B2851217
theorem B6415253 : Blo 1899435 6415253 := bbase (se 6 (by rfl) ⟨150357, by rfl⟩ : syracuseStep 6415253 = 300715) (by norm_num)
theorem B4276835 : Blo 1899435 4276835 := bstep (se 1 (by rfl) ⟨3207626, by rfl⟩ : syracuseStep 4276835 = 6415253) B6415253
theorem B2851223 : Blo 1899435 2851223 := bstep (se 1 (by rfl) ⟨2138417, by rfl⟩ : syracuseStep 2851223 = 4276835) B4276835
theorem B1900815 : Blo 1899435 1900815 := bstep (se 1 (by rfl) ⟨1425611, by rfl⟩ : syracuseStep 1900815 = 2851223) B2851223
theorem B2851229 : Blo 1899435 2851229 := bbase (se 3 (by rfl) ⟨534605, by rfl⟩ : syracuseStep 2851229 = 1069211) (by norm_num)
theorem B1900819 : Blo 1899435 1900819 := bstep (se 1 (by rfl) ⟨1425614, by rfl⟩ : syracuseStep 1900819 = 2851229) B2851229
theorem B4276853 : Blo 1899435 4276853 := bbase (se 5 (by rfl) ⟨200477, by rfl⟩ : syracuseStep 4276853 = 400955) (by norm_num)
theorem B2851235 : Blo 1899435 2851235 := bstep (se 1 (by rfl) ⟨2138426, by rfl⟩ : syracuseStep 2851235 = 4276853) B4276853
theorem B1900823 : Blo 1899435 1900823 := bstep (se 1 (by rfl) ⟨1425617, by rfl⟩ : syracuseStep 1900823 = 2851235) B2851235
theorem B12345205 : Blo 1899435 12345205 := bbase (se 5 (by rfl) ⟨578681, by rfl⟩ : syracuseStep 12345205 = 1157363) (by norm_num)
theorem B16460273 : Blo 1899435 16460273 := bstep (se 2 (by rfl) ⟨6172602, by rfl⟩ : syracuseStep 16460273 = 12345205) B12345205
theorem B10973515 : Blo 1899435 10973515 := bstep (se 1 (by rfl) ⟨8230136, by rfl⟩ : syracuseStep 10973515 = 16460273) B16460273
theorem B14631353 : Blo 1899435 14631353 := bstep (se 2 (by rfl) ⟨5486757, by rfl⟩ : syracuseStep 14631353 = 10973515) B10973515
theorem B9754235 : Blo 1899435 9754235 := bstep (se 1 (by rfl) ⟨7315676, by rfl⟩ : syracuseStep 9754235 = 14631353) B14631353
theorem B6502823 : Blo 1899435 6502823 := bstep (se 1 (by rfl) ⟨4877117, by rfl⟩ : syracuseStep 6502823 = 9754235) B9754235
theorem B4335215 : Blo 1899435 4335215 := bstep (se 1 (by rfl) ⟨3251411, by rfl⟩ : syracuseStep 4335215 = 6502823) B6502823
theorem B11560573 : Blo 1899435 11560573 := bstep (se 3 (by rfl) ⟨2167607, by rfl⟩ : syracuseStep 11560573 = 4335215) B4335215
theorem B15414097 : Blo 1899435 15414097 := bstep (se 2 (by rfl) ⟨5780286, by rfl⟩ : syracuseStep 15414097 = 11560573) B11560573
theorem B20552129 : Blo 1899435 20552129 := bstep (se 2 (by rfl) ⟨7707048, by rfl⟩ : syracuseStep 20552129 = 15414097) B15414097
theorem B13701419 : Blo 1899435 13701419 := bstep (se 1 (by rfl) ⟨10276064, by rfl⟩ : syracuseStep 13701419 = 20552129) B20552129
theorem B9134279 : Blo 1899435 9134279 := bstep (se 1 (by rfl) ⟨6850709, by rfl⟩ : syracuseStep 9134279 = 13701419) B13701419
theorem B6089519 : Blo 1899435 6089519 := bstep (se 1 (by rfl) ⟨4567139, by rfl⟩ : syracuseStep 6089519 = 9134279) B9134279
theorem B16238717 : Blo 1899435 16238717 := bstep (se 3 (by rfl) ⟨3044759, by rfl⟩ : syracuseStep 16238717 = 6089519) B6089519
theorem B10825811 : Blo 1899435 10825811 := bstep (se 1 (by rfl) ⟨8119358, by rfl⟩ : syracuseStep 10825811 = 16238717) B16238717
theorem B7217207 : Blo 1899435 7217207 := bstep (se 1 (by rfl) ⟨5412905, by rfl⟩ : syracuseStep 7217207 = 10825811) B10825811
theorem B4811471 : Blo 1899435 4811471 := bstep (se 1 (by rfl) ⟨3608603, by rfl⟩ : syracuseStep 4811471 = 7217207) B7217207
theorem B3207647 : Blo 1899435 3207647 := bstep (se 1 (by rfl) ⟨2405735, by rfl⟩ : syracuseStep 3207647 = 4811471) B4811471
theorem B2138431 : Blo 1899435 2138431 := bstep (se 1 (by rfl) ⟨1603823, by rfl⟩ : syracuseStep 2138431 = 3207647) B3207647
theorem B2851241 : Blo 1899435 2851241 := bstep (se 2 (by rfl) ⟨1069215, by rfl⟩ : syracuseStep 2851241 = 2138431) B2138431
theorem B1900827 : Blo 1899435 1900827 := bstep (se 1 (by rfl) ⟨1425620, by rfl⟩ : syracuseStep 1900827 = 2851241) B2851241
theorem B7217221 : Blo 1899435 7217221 := bbase (se 4 (by rfl) ⟨676614, by rfl⟩ : syracuseStep 7217221 = 1353229) (by norm_num)
theorem B9622961 : Blo 1899435 9622961 := bstep (se 2 (by rfl) ⟨3608610, by rfl⟩ : syracuseStep 9622961 = 7217221) B7217221
theorem B6415307 : Blo 1899435 6415307 := bstep (se 1 (by rfl) ⟨4811480, by rfl⟩ : syracuseStep 6415307 = 9622961) B9622961
theorem B4276871 : Blo 1899435 4276871 := bstep (se 1 (by rfl) ⟨3207653, by rfl⟩ : syracuseStep 4276871 = 6415307) B6415307
theorem B2851247 : Blo 1899435 2851247 := bstep (se 1 (by rfl) ⟨2138435, by rfl⟩ : syracuseStep 2851247 = 4276871) B4276871
theorem B1900831 : Blo 1899435 1900831 := bstep (se 1 (by rfl) ⟨1425623, by rfl⟩ : syracuseStep 1900831 = 2851247) B2851247
theorem B2851253 : Blo 1899435 2851253 := bbase (se 5 (by rfl) ⟨133652, by rfl⟩ : syracuseStep 2851253 = 267305) (by norm_num)
theorem B1900835 : Blo 1899435 1900835 := bstep (se 1 (by rfl) ⟨1425626, by rfl⟩ : syracuseStep 1900835 = 2851253) B2851253
theorem B4811501 : Blo 1899435 4811501 := bbase (se 3 (by rfl) ⟨902156, by rfl⟩ : syracuseStep 4811501 = 1804313) (by norm_num)
theorem B3207667 : Blo 1899435 3207667 := bstep (se 1 (by rfl) ⟨2405750, by rfl⟩ : syracuseStep 3207667 = 4811501) B4811501
theorem B4276889 : Blo 1899435 4276889 := bstep (se 2 (by rfl) ⟨1603833, by rfl⟩ : syracuseStep 4276889 = 3207667) B3207667
theorem B2851259 : Blo 1899435 2851259 := bstep (se 1 (by rfl) ⟨2138444, by rfl⟩ : syracuseStep 2851259 = 4276889) B4276889
theorem B1900839 : Blo 1899435 1900839 := bstep (se 1 (by rfl) ⟨1425629, by rfl⟩ : syracuseStep 1900839 = 2851259) B2851259
theorem B2138449 : Blo 1899435 2138449 := bbase (se 2 (by rfl) ⟨801918, by rfl⟩ : syracuseStep 2138449 = 1603837) (by norm_num)
theorem B2851265 : Blo 1899435 2851265 := bstep (se 2 (by rfl) ⟨1069224, by rfl⟩ : syracuseStep 2851265 = 2138449) B2138449
theorem B1900843 : Blo 1899435 1900843 := bstep (se 1 (by rfl) ⟨1425632, by rfl⟩ : syracuseStep 1900843 = 2851265) B2851265
theorem B2029861 : Blo 1899435 2029861 := bbase (se 4 (by rfl) ⟨190299, by rfl⟩ : syracuseStep 2029861 = 380599) (by norm_num)
theorem B2706481 : Blo 1899435 2706481 := bstep (se 2 (by rfl) ⟨1014930, by rfl⟩ : syracuseStep 2706481 = 2029861) B2029861
theorem B3608641 : Blo 1899435 3608641 := bstep (se 2 (by rfl) ⟨1353240, by rfl⟩ : syracuseStep 3608641 = 2706481) B2706481
theorem B4811521 : Blo 1899435 4811521 := bstep (se 2 (by rfl) ⟨1804320, by rfl⟩ : syracuseStep 4811521 = 3608641) B3608641
theorem B6415361 : Blo 1899435 6415361 := bstep (se 2 (by rfl) ⟨2405760, by rfl⟩ : syracuseStep 6415361 = 4811521) B4811521
theorem B4276907 : Blo 1899435 4276907 := bstep (se 1 (by rfl) ⟨3207680, by rfl⟩ : syracuseStep 4276907 = 6415361) B6415361
theorem B2851271 : Blo 1899435 2851271 := bstep (se 1 (by rfl) ⟨2138453, by rfl⟩ : syracuseStep 2851271 = 4276907) B4276907
theorem B1900847 : Blo 1899435 1900847 := bstep (se 1 (by rfl) ⟨1425635, by rfl⟩ : syracuseStep 1900847 = 2851271) B2851271
theorem B2851277 : Blo 1899435 2851277 := bbase (se 3 (by rfl) ⟨534614, by rfl⟩ : syracuseStep 2851277 = 1069229) (by norm_num)
theorem B1900851 : Blo 1899435 1900851 := bstep (se 1 (by rfl) ⟨1425638, by rfl⟩ : syracuseStep 1900851 = 2851277) B2851277
theorem B4276925 : Blo 1899435 4276925 := bbase (se 3 (by rfl) ⟨801923, by rfl⟩ : syracuseStep 4276925 = 1603847) (by norm_num)
theorem B2851283 : Blo 1899435 2851283 := bstep (se 1 (by rfl) ⟨2138462, by rfl⟩ : syracuseStep 2851283 = 4276925) B4276925
theorem B1900855 : Blo 1899435 1900855 := bstep (se 1 (by rfl) ⟨1425641, by rfl⟩ : syracuseStep 1900855 = 2851283) B2851283
theorem B3207701 : Blo 1899435 3207701 := bbase (se 6 (by rfl) ⟨75180, by rfl⟩ : syracuseStep 3207701 = 150361) (by norm_num)
theorem B2138467 : Blo 1899435 2138467 := bstep (se 1 (by rfl) ⟨1603850, by rfl⟩ : syracuseStep 2138467 = 3207701) B3207701
theorem B2851289 : Blo 1899435 2851289 := bstep (se 2 (by rfl) ⟨1069233, by rfl⟩ : syracuseStep 2851289 = 2138467) B2138467
theorem B1900859 : Blo 1899435 1900859 := bstep (se 1 (by rfl) ⟨1425644, by rfl⟩ : syracuseStep 1900859 = 2851289) B2851289
theorem B3853597 : Blo 1899435 3853597 := bbase (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) (by norm_num)
theorem B5138129 : Blo 1899435 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B3425419 : Blo 1899435 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B18268901 : Blo 1899435 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B12179267 : Blo 1899435 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B8119511 : Blo 1899435 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B5413007 : Blo 1899435 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B14434685 : Blo 1899435 14434685 := bstep (se 3 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 14434685 = 5413007) B5413007
theorem B9623123 : Blo 1899435 9623123 := bstep (se 1 (by rfl) ⟨7217342, by rfl⟩ : syracuseStep 9623123 = 14434685) B14434685
theorem B6415415 : Blo 1899435 6415415 := bstep (se 1 (by rfl) ⟨4811561, by rfl⟩ : syracuseStep 6415415 = 9623123) B9623123
theorem B4276943 : Blo 1899435 4276943 := bstep (se 1 (by rfl) ⟨3207707, by rfl⟩ : syracuseStep 4276943 = 6415415) B6415415
theorem B2851295 : Blo 1899435 2851295 := bstep (se 1 (by rfl) ⟨2138471, by rfl⟩ : syracuseStep 2851295 = 4276943) B4276943
theorem B1900863 : Blo 1899435 1900863 := bstep (se 1 (by rfl) ⟨1425647, by rfl⟩ : syracuseStep 1900863 = 2851295) B2851295
theorem B2851301 : Blo 1899435 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B1900867 : Blo 1899435 1900867 := bstep (se 1 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 1900867 = 2851301) B2851301
theorem B4692725 : Blo 1899435 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B3128483 : Blo 1899435 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B8342621 : Blo 1899435 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B5561747 : Blo 1899435 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B3707831 : Blo 1899435 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B2471887 : Blo 1899435 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B13183397 : Blo 1899435 13183397 := bstep (se 4 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 13183397 = 2471887) B2471887
theorem B8788931 : Blo 1899435 8788931 := bstep (se 1 (by rfl) ⟨6591698, by rfl⟩ : syracuseStep 8788931 = 13183397) B13183397
theorem B5859287 : Blo 1899435 5859287 := bstep (se 1 (by rfl) ⟨4394465, by rfl⟩ : syracuseStep 5859287 = 8788931) B8788931
theorem B3906191 : Blo 1899435 3906191 := bstep (se 1 (by rfl) ⟨2929643, by rfl⟩ : syracuseStep 3906191 = 5859287) B5859287
theorem B10416509 : Blo 1899435 10416509 := bstep (se 3 (by rfl) ⟨1953095, by rfl⟩ : syracuseStep 10416509 = 3906191) B3906191
theorem B6944339 : Blo 1899435 6944339 := bstep (se 1 (by rfl) ⟨5208254, by rfl⟩ : syracuseStep 6944339 = 10416509) B10416509
theorem B4629559 : Blo 1899435 4629559 := bstep (se 1 (by rfl) ⟨3472169, by rfl⟩ : syracuseStep 4629559 = 6944339) B6944339
theorem B6172745 : Blo 1899435 6172745 := bstep (se 2 (by rfl) ⟨2314779, by rfl⟩ : syracuseStep 6172745 = 4629559) B4629559
theorem B16460653 : Blo 1899435 16460653 := bstep (se 3 (by rfl) ⟨3086372, by rfl⟩ : syracuseStep 16460653 = 6172745) B6172745
theorem B21947537 : Blo 1899435 21947537 := bstep (se 2 (by rfl) ⟨8230326, by rfl⟩ : syracuseStep 21947537 = 16460653) B16460653
theorem B14631691 : Blo 1899435 14631691 := bstep (se 1 (by rfl) ⟨10973768, by rfl⟩ : syracuseStep 14631691 = 21947537) B21947537
theorem B19508921 : Blo 1899435 19508921 := bstep (se 2 (by rfl) ⟨7315845, by rfl⟩ : syracuseStep 19508921 = 14631691) B14631691
theorem B13005947 : Blo 1899435 13005947 := bstep (se 1 (by rfl) ⟨9754460, by rfl⟩ : syracuseStep 13005947 = 19508921) B19508921
theorem B34682525 : Blo 1899435 34682525 := bstep (se 3 (by rfl) ⟨6502973, by rfl⟩ : syracuseStep 34682525 = 13005947) B13005947
theorem B23121683 : Blo 1899435 23121683 := bstep (se 1 (by rfl) ⟨17341262, by rfl⟩ : syracuseStep 23121683 = 34682525) B34682525
theorem B15414455 : Blo 1899435 15414455 := bstep (se 1 (by rfl) ⟨11560841, by rfl⟩ : syracuseStep 15414455 = 23121683) B23121683
theorem B10276303 : Blo 1899435 10276303 := bstep (se 1 (by rfl) ⟨7707227, by rfl⟩ : syracuseStep 10276303 = 15414455) B15414455
theorem B13701737 : Blo 1899435 13701737 := bstep (se 2 (by rfl) ⟨5138151, by rfl⟩ : syracuseStep 13701737 = 10276303) B10276303
theorem B9134491 : Blo 1899435 9134491 := bstep (se 1 (by rfl) ⟨6850868, by rfl⟩ : syracuseStep 9134491 = 13701737) B13701737
theorem B12179321 : Blo 1899435 12179321 := bstep (se 2 (by rfl) ⟨4567245, by rfl⟩ : syracuseStep 12179321 = 9134491) B9134491
theorem B8119547 : Blo 1899435 8119547 := bstep (se 1 (by rfl) ⟨6089660, by rfl⟩ : syracuseStep 8119547 = 12179321) B12179321
theorem B5413031 : Blo 1899435 5413031 := bstep (se 1 (by rfl) ⟨4059773, by rfl⟩ : syracuseStep 5413031 = 8119547) B8119547
theorem B3608687 : Blo 1899435 3608687 := bstep (se 1 (by rfl) ⟨2706515, by rfl⟩ : syracuseStep 3608687 = 5413031) B5413031
theorem B2405791 : Blo 1899435 2405791 := bstep (se 1 (by rfl) ⟨1804343, by rfl⟩ : syracuseStep 2405791 = 3608687) B3608687
theorem B3207721 : Blo 1899435 3207721 := bstep (se 2 (by rfl) ⟨1202895, by rfl⟩ : syracuseStep 3207721 = 2405791) B2405791
theorem B4276961 : Blo 1899435 4276961 := bstep (se 2 (by rfl) ⟨1603860, by rfl⟩ : syracuseStep 4276961 = 3207721) B3207721
theorem B2851307 : Blo 1899435 2851307 := bstep (se 1 (by rfl) ⟨2138480, by rfl⟩ : syracuseStep 2851307 = 4276961) B4276961
theorem B1900871 : Blo 1899435 1900871 := bstep (se 1 (by rfl) ⟨1425653, by rfl⟩ : syracuseStep 1900871 = 2851307) B2851307
theorem B2138485 : Blo 1899435 2138485 := bbase (se 5 (by rfl) ⟨100241, by rfl⟩ : syracuseStep 2138485 = 200483) (by norm_num)
theorem B2851313 : Blo 1899435 2851313 := bstep (se 2 (by rfl) ⟨1069242, by rfl⟩ : syracuseStep 2851313 = 2138485) B2138485
theorem B1900875 : Blo 1899435 1900875 := bstep (se 1 (by rfl) ⟨1425656, by rfl⟩ : syracuseStep 1900875 = 2851313) B2851313
theorem B2405801 : Blo 1899435 2405801 := bbase (se 2 (by rfl) ⟨902175, by rfl⟩ : syracuseStep 2405801 = 1804351) (by norm_num)
theorem B6415469 : Blo 1899435 6415469 := bstep (se 3 (by rfl) ⟨1202900, by rfl⟩ : syracuseStep 6415469 = 2405801) B2405801
theorem B4276979 : Blo 1899435 4276979 := bstep (se 1 (by rfl) ⟨3207734, by rfl⟩ : syracuseStep 4276979 = 6415469) B6415469
theorem B2851319 : Blo 1899435 2851319 := bstep (se 1 (by rfl) ⟨2138489, by rfl⟩ : syracuseStep 2851319 = 4276979) B4276979
theorem B1900879 : Blo 1899435 1900879 := bstep (se 1 (by rfl) ⟨1425659, by rfl⟩ : syracuseStep 1900879 = 2851319) B2851319
theorem B2851325 : Blo 1899435 2851325 := bbase (se 3 (by rfl) ⟨534623, by rfl⟩ : syracuseStep 2851325 = 1069247) (by norm_num)
theorem B1900883 : Blo 1899435 1900883 := bstep (se 1 (by rfl) ⟨1425662, by rfl⟩ : syracuseStep 1900883 = 2851325) B2851325
theorem B4276997 : Blo 1899435 4276997 := bbase (se 4 (by rfl) ⟨400968, by rfl⟩ : syracuseStep 4276997 = 801937) (by norm_num)
theorem B2851331 : Blo 1899435 2851331 := bstep (se 1 (by rfl) ⟨2138498, by rfl⟩ : syracuseStep 2851331 = 4276997) B4276997
theorem B1900887 : Blo 1899435 1900887 := bstep (se 1 (by rfl) ⟨1425665, by rfl⟩ : syracuseStep 1900887 = 2851331) B2851331
theorem B3608725 : Blo 1899435 3608725 := bbase (se 6 (by rfl) ⟨84579, by rfl⟩ : syracuseStep 3608725 = 169159) (by norm_num)
theorem B4811633 : Blo 1899435 4811633 := bstep (se 2 (by rfl) ⟨1804362, by rfl⟩ : syracuseStep 4811633 = 3608725) B3608725
theorem B3207755 : Blo 1899435 3207755 := bstep (se 1 (by rfl) ⟨2405816, by rfl⟩ : syracuseStep 3207755 = 4811633) B4811633
theorem B2138503 : Blo 1899435 2138503 := bstep (se 1 (by rfl) ⟨1603877, by rfl⟩ : syracuseStep 2138503 = 3207755) B3207755
theorem B2851337 : Blo 1899435 2851337 := bstep (se 2 (by rfl) ⟨1069251, by rfl⟩ : syracuseStep 2851337 = 2138503) B2138503
theorem B1900891 : Blo 1899435 1900891 := bstep (se 1 (by rfl) ⟨1425668, by rfl⟩ : syracuseStep 1900891 = 2851337) B2851337
theorem B9623285 : Blo 1899435 9623285 := bbase (se 5 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 9623285 = 902183) (by norm_num)
theorem B6415523 : Blo 1899435 6415523 := bstep (se 1 (by rfl) ⟨4811642, by rfl⟩ : syracuseStep 6415523 = 9623285) B9623285
theorem B4277015 : Blo 1899435 4277015 := bstep (se 1 (by rfl) ⟨3207761, by rfl⟩ : syracuseStep 4277015 = 6415523) B6415523
theorem B2851343 : Blo 1899435 2851343 := bstep (se 1 (by rfl) ⟨2138507, by rfl⟩ : syracuseStep 2851343 = 4277015) B4277015
theorem B1900895 : Blo 1899435 1900895 := bstep (se 1 (by rfl) ⟨1425671, by rfl⟩ : syracuseStep 1900895 = 2851343) B2851343
theorem B2851349 : Blo 1899435 2851349 := bbase (se 6 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 2851349 = 133657) (by norm_num)
theorem B1900899 : Blo 1899435 1900899 := bstep (se 1 (by rfl) ⟨1425674, by rfl⟩ : syracuseStep 1900899 = 2851349) B2851349
theorem B2283661 : Blo 1899435 2283661 := bbase (se 3 (by rfl) ⟨428186, by rfl⟩ : syracuseStep 2283661 = 856373) (by norm_num)
theorem B3044881 : Blo 1899435 3044881 := bstep (se 2 (by rfl) ⟨1141830, by rfl⟩ : syracuseStep 3044881 = 2283661) B2283661
theorem B16239365 : Blo 1899435 16239365 := bstep (se 4 (by rfl) ⟨1522440, by rfl⟩ : syracuseStep 16239365 = 3044881) B3044881
theorem B10826243 : Blo 1899435 10826243 := bstep (se 1 (by rfl) ⟨8119682, by rfl⟩ : syracuseStep 10826243 = 16239365) B16239365
theorem B7217495 : Blo 1899435 7217495 := bstep (se 1 (by rfl) ⟨5413121, by rfl⟩ : syracuseStep 7217495 = 10826243) B10826243
theorem B4811663 : Blo 1899435 4811663 := bstep (se 1 (by rfl) ⟨3608747, by rfl⟩ : syracuseStep 4811663 = 7217495) B7217495
theorem B3207775 : Blo 1899435 3207775 := bstep (se 1 (by rfl) ⟨2405831, by rfl⟩ : syracuseStep 3207775 = 4811663) B4811663
theorem B4277033 : Blo 1899435 4277033 := bstep (se 2 (by rfl) ⟨1603887, by rfl⟩ : syracuseStep 4277033 = 3207775) B3207775
theorem B2851355 : Blo 1899435 2851355 := bstep (se 1 (by rfl) ⟨2138516, by rfl⟩ : syracuseStep 2851355 = 4277033) B4277033
theorem B1900903 : Blo 1899435 1900903 := bstep (se 1 (by rfl) ⟨1425677, by rfl⟩ : syracuseStep 1900903 = 2851355) B2851355
theorem B2138521 : Blo 1899435 2138521 := bbase (se 2 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 2138521 = 1603891) (by norm_num)
theorem B2851361 : Blo 1899435 2851361 := bstep (se 2 (by rfl) ⟨1069260, by rfl⟩ : syracuseStep 2851361 = 2138521) B2138521
theorem B1900907 : Blo 1899435 1900907 := bstep (se 1 (by rfl) ⟨1425680, by rfl⟩ : syracuseStep 1900907 = 2851361) B2851361
theorem B7217525 : Blo 1899435 7217525 := bbase (se 5 (by rfl) ⟨338321, by rfl⟩ : syracuseStep 7217525 = 676643) (by norm_num)
theorem B4811683 : Blo 1899435 4811683 := bstep (se 1 (by rfl) ⟨3608762, by rfl⟩ : syracuseStep 4811683 = 7217525) B7217525
theorem B6415577 : Blo 1899435 6415577 := bstep (se 2 (by rfl) ⟨2405841, by rfl⟩ : syracuseStep 6415577 = 4811683) B4811683
theorem B4277051 : Blo 1899435 4277051 := bstep (se 1 (by rfl) ⟨3207788, by rfl⟩ : syracuseStep 4277051 = 6415577) B6415577
theorem B2851367 : Blo 1899435 2851367 := bstep (se 1 (by rfl) ⟨2138525, by rfl⟩ : syracuseStep 2851367 = 4277051) B4277051
theorem B1900911 : Blo 1899435 1900911 := bstep (se 1 (by rfl) ⟨1425683, by rfl⟩ : syracuseStep 1900911 = 2851367) B2851367
theorem B2851373 : Blo 1899435 2851373 := bbase (se 3 (by rfl) ⟨534632, by rfl⟩ : syracuseStep 2851373 = 1069265) (by norm_num)
theorem B1900915 : Blo 1899435 1900915 := bstep (se 1 (by rfl) ⟨1425686, by rfl⟩ : syracuseStep 1900915 = 2851373) B2851373
theorem B4277069 : Blo 1899435 4277069 := bbase (se 3 (by rfl) ⟨801950, by rfl⟩ : syracuseStep 4277069 = 1603901) (by norm_num)
theorem B2851379 : Blo 1899435 2851379 := bstep (se 1 (by rfl) ⟨2138534, by rfl⟩ : syracuseStep 2851379 = 4277069) B4277069
theorem B1900919 : Blo 1899435 1900919 := bstep (se 1 (by rfl) ⟨1425689, by rfl⟩ : syracuseStep 1900919 = 2851379) B2851379
theorem B2405857 : Blo 1899435 2405857 := bbase (se 2 (by rfl) ⟨902196, by rfl⟩ : syracuseStep 2405857 = 1804393) (by norm_num)
theorem B3207809 : Blo 1899435 3207809 := bstep (se 2 (by rfl) ⟨1202928, by rfl⟩ : syracuseStep 3207809 = 2405857) B2405857
theorem B2138539 : Blo 1899435 2138539 := bstep (se 1 (by rfl) ⟨1603904, by rfl⟩ : syracuseStep 2138539 = 3207809) B3207809
theorem B2851385 : Blo 1899435 2851385 := bstep (se 2 (by rfl) ⟨1069269, by rfl⟩ : syracuseStep 2851385 = 2138539) B2138539
theorem B1900923 : Blo 1899435 1900923 := bstep (se 1 (by rfl) ⟨1425692, by rfl⟩ : syracuseStep 1900923 = 2851385) B2851385
theorem B21652757 : Blo 1899435 21652757 := bbase (se 6 (by rfl) ⟨507486, by rfl⟩ : syracuseStep 21652757 = 1014973) (by norm_num)
theorem B14435171 : Blo 1899435 14435171 := bstep (se 1 (by rfl) ⟨10826378, by rfl⟩ : syracuseStep 14435171 = 21652757) B21652757
theorem B9623447 : Blo 1899435 9623447 := bstep (se 1 (by rfl) ⟨7217585, by rfl⟩ : syracuseStep 9623447 = 14435171) B14435171
theorem B6415631 : Blo 1899435 6415631 := bstep (se 1 (by rfl) ⟨4811723, by rfl⟩ : syracuseStep 6415631 = 9623447) B9623447
theorem B4277087 : Blo 1899435 4277087 := bstep (se 1 (by rfl) ⟨3207815, by rfl⟩ : syracuseStep 4277087 = 6415631) B6415631
theorem B2851391 : Blo 1899435 2851391 := bstep (se 1 (by rfl) ⟨2138543, by rfl⟩ : syracuseStep 2851391 = 4277087) B4277087
theorem B1900927 : Blo 1899435 1900927 := bstep (se 1 (by rfl) ⟨1425695, by rfl⟩ : syracuseStep 1900927 = 2851391) B2851391
theorem B2851397 : Blo 1899435 2851397 := bbase (se 4 (by rfl) ⟨267318, by rfl⟩ : syracuseStep 2851397 = 534637) (by norm_num)
theorem B1900931 : Blo 1899435 1900931 := bstep (se 1 (by rfl) ⟨1425698, by rfl⟩ : syracuseStep 1900931 = 2851397) B2851397
theorem B3207829 : Blo 1899435 3207829 := bbase (se 6 (by rfl) ⟨75183, by rfl⟩ : syracuseStep 3207829 = 150367) (by norm_num)
theorem B4277105 : Blo 1899435 4277105 := bstep (se 2 (by rfl) ⟨1603914, by rfl⟩ : syracuseStep 4277105 = 3207829) B3207829
theorem B2851403 : Blo 1899435 2851403 := bstep (se 1 (by rfl) ⟨2138552, by rfl⟩ : syracuseStep 2851403 = 4277105) B4277105
theorem B1900935 : Blo 1899435 1900935 := bstep (se 1 (by rfl) ⟨1425701, by rfl⟩ : syracuseStep 1900935 = 2851403) B2851403
theorem B2138557 : Blo 1899435 2138557 := bbase (se 3 (by rfl) ⟨400979, by rfl⟩ : syracuseStep 2138557 = 801959) (by norm_num)
theorem B2851409 : Blo 1899435 2851409 := bstep (se 2 (by rfl) ⟨1069278, by rfl⟩ : syracuseStep 2851409 = 2138557) B2138557
theorem B1900939 : Blo 1899435 1900939 := bstep (se 1 (by rfl) ⟨1425704, by rfl⟩ : syracuseStep 1900939 = 2851409) B2851409
theorem B6415685 : Blo 1899435 6415685 := bbase (se 4 (by rfl) ⟨601470, by rfl⟩ : syracuseStep 6415685 = 1202941) (by norm_num)
theorem B4277123 : Blo 1899435 4277123 := bstep (se 1 (by rfl) ⟨3207842, by rfl⟩ : syracuseStep 4277123 = 6415685) B6415685
theorem B2851415 : Blo 1899435 2851415 := bstep (se 1 (by rfl) ⟨2138561, by rfl⟩ : syracuseStep 2851415 = 4277123) B4277123
theorem B1900943 : Blo 1899435 1900943 := bstep (se 1 (by rfl) ⟨1425707, by rfl⟩ : syracuseStep 1900943 = 2851415) B2851415
theorem B2851421 : Blo 1899435 2851421 := bbase (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) (by norm_num)
theorem B1900947 : Blo 1899435 1900947 := bstep (se 1 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 1900947 = 2851421) B2851421
theorem B4277141 : Blo 1899435 4277141 := bbase (se 6 (by rfl) ⟨100245, by rfl⟩ : syracuseStep 4277141 = 200491) (by norm_num)
theorem B2851427 : Blo 1899435 2851427 := bstep (se 1 (by rfl) ⟨2138570, by rfl⟩ : syracuseStep 2851427 = 4277141) B4277141
theorem B1900951 : Blo 1899435 1900951 := bstep (se 1 (by rfl) ⟨1425713, by rfl⟩ : syracuseStep 1900951 = 2851427) B2851427
theorem B3044965 : Blo 1899435 3044965 := bbase (se 4 (by rfl) ⟨285465, by rfl⟩ : syracuseStep 3044965 = 570931) (by norm_num)
theorem B4059953 : Blo 1899435 4059953 := bstep (se 2 (by rfl) ⟨1522482, by rfl⟩ : syracuseStep 4059953 = 3044965) B3044965
theorem B2706635 : Blo 1899435 2706635 := bstep (se 1 (by rfl) ⟨2029976, by rfl⟩ : syracuseStep 2706635 = 4059953) B4059953
theorem B7217693 : Blo 1899435 7217693 := bstep (se 3 (by rfl) ⟨1353317, by rfl⟩ : syracuseStep 7217693 = 2706635) B2706635
theorem B4811795 : Blo 1899435 4811795 := bstep (se 1 (by rfl) ⟨3608846, by rfl⟩ : syracuseStep 4811795 = 7217693) B7217693
theorem B3207863 : Blo 1899435 3207863 := bstep (se 1 (by rfl) ⟨2405897, by rfl⟩ : syracuseStep 3207863 = 4811795) B4811795
theorem B2138575 : Blo 1899435 2138575 := bstep (se 1 (by rfl) ⟨1603931, by rfl⟩ : syracuseStep 2138575 = 3207863) B3207863
theorem B2851433 : Blo 1899435 2851433 := bstep (se 2 (by rfl) ⟨1069287, by rfl⟩ : syracuseStep 2851433 = 2138575) B2138575
theorem B1900955 : Blo 1899435 1900955 := bstep (se 1 (by rfl) ⟨1425716, by rfl⟩ : syracuseStep 1900955 = 2851433) B2851433
theorem B6089941 : Blo 1899435 6089941 := bbase (se 7 (by rfl) ⟨71366, by rfl⟩ : syracuseStep 6089941 = 142733) (by norm_num)
theorem B8119921 : Blo 1899435 8119921 := bstep (se 2 (by rfl) ⟨3044970, by rfl⟩ : syracuseStep 8119921 = 6089941) B6089941
theorem B10826561 : Blo 1899435 10826561 := bstep (se 2 (by rfl) ⟨4059960, by rfl⟩ : syracuseStep 10826561 = 8119921) B8119921
theorem B7217707 : Blo 1899435 7217707 := bstep (se 1 (by rfl) ⟨5413280, by rfl⟩ : syracuseStep 7217707 = 10826561) B10826561
theorem B9623609 : Blo 1899435 9623609 := bstep (se 2 (by rfl) ⟨3608853, by rfl⟩ : syracuseStep 9623609 = 7217707) B7217707
theorem B6415739 : Blo 1899435 6415739 := bstep (se 1 (by rfl) ⟨4811804, by rfl⟩ : syracuseStep 6415739 = 9623609) B9623609
theorem B4277159 : Blo 1899435 4277159 := bstep (se 1 (by rfl) ⟨3207869, by rfl⟩ : syracuseStep 4277159 = 6415739) B6415739
theorem B2851439 : Blo 1899435 2851439 := bstep (se 1 (by rfl) ⟨2138579, by rfl⟩ : syracuseStep 2851439 = 4277159) B4277159
theorem B1900959 : Blo 1899435 1900959 := bstep (se 1 (by rfl) ⟨1425719, by rfl⟩ : syracuseStep 1900959 = 2851439) B2851439
theorem B2851445 : Blo 1899435 2851445 := bbase (se 5 (by rfl) ⟨133661, by rfl⟩ : syracuseStep 2851445 = 267323) (by norm_num)
theorem B1900963 : Blo 1899435 1900963 := bstep (se 1 (by rfl) ⟨1425722, by rfl⟩ : syracuseStep 1900963 = 2851445) B2851445
theorem B3608869 : Blo 1899435 3608869 := bbase (se 4 (by rfl) ⟨338331, by rfl⟩ : syracuseStep 3608869 = 676663) (by norm_num)
theorem B4811825 : Blo 1899435 4811825 := bstep (se 2 (by rfl) ⟨1804434, by rfl⟩ : syracuseStep 4811825 = 3608869) B3608869
theorem B3207883 : Blo 1899435 3207883 := bstep (se 1 (by rfl) ⟨2405912, by rfl⟩ : syracuseStep 3207883 = 4811825) B4811825
theorem B4277177 : Blo 1899435 4277177 := bstep (se 2 (by rfl) ⟨1603941, by rfl⟩ : syracuseStep 4277177 = 3207883) B3207883
theorem B2851451 : Blo 1899435 2851451 := bstep (se 1 (by rfl) ⟨2138588, by rfl⟩ : syracuseStep 2851451 = 4277177) B4277177
theorem B1900967 : Blo 1899435 1900967 := bstep (se 1 (by rfl) ⟨1425725, by rfl⟩ : syracuseStep 1900967 = 2851451) B2851451
theorem B2138593 : Blo 1899435 2138593 := bbase (se 2 (by rfl) ⟨801972, by rfl⟩ : syracuseStep 2138593 = 1603945) (by norm_num)
theorem B2851457 : Blo 1899435 2851457 := bstep (se 2 (by rfl) ⟨1069296, by rfl⟩ : syracuseStep 2851457 = 2138593) B2138593
theorem B1900971 : Blo 1899435 1900971 := bstep (se 1 (by rfl) ⟨1425728, by rfl⟩ : syracuseStep 1900971 = 2851457) B2851457
theorem B4811845 : Blo 1899435 4811845 := bbase (se 4 (by rfl) ⟨451110, by rfl⟩ : syracuseStep 4811845 = 902221) (by norm_num)
theorem B6415793 : Blo 1899435 6415793 := bstep (se 2 (by rfl) ⟨2405922, by rfl⟩ : syracuseStep 6415793 = 4811845) B4811845
theorem B4277195 : Blo 1899435 4277195 := bstep (se 1 (by rfl) ⟨3207896, by rfl⟩ : syracuseStep 4277195 = 6415793) B6415793
theorem B2851463 : Blo 1899435 2851463 := bstep (se 1 (by rfl) ⟨2138597, by rfl⟩ : syracuseStep 2851463 = 4277195) B4277195
theorem B1900975 : Blo 1899435 1900975 := bstep (se 1 (by rfl) ⟨1425731, by rfl⟩ : syracuseStep 1900975 = 2851463) B2851463
theorem B2851469 : Blo 1899435 2851469 := bbase (se 3 (by rfl) ⟨534650, by rfl⟩ : syracuseStep 2851469 = 1069301) (by norm_num)
theorem B1900979 : Blo 1899435 1900979 := bstep (se 1 (by rfl) ⟨1425734, by rfl⟩ : syracuseStep 1900979 = 2851469) B2851469
theorem B4277213 : Blo 1899435 4277213 := bbase (se 3 (by rfl) ⟨801977, by rfl⟩ : syracuseStep 4277213 = 1603955) (by norm_num)
theorem B2851475 : Blo 1899435 2851475 := bstep (se 1 (by rfl) ⟨2138606, by rfl⟩ : syracuseStep 2851475 = 4277213) B4277213
theorem B1900983 : Blo 1899435 1900983 := bstep (se 1 (by rfl) ⟨1425737, by rfl⟩ : syracuseStep 1900983 = 2851475) B2851475
theorem B3207917 : Blo 1899435 3207917 := bbase (se 3 (by rfl) ⟨601484, by rfl⟩ : syracuseStep 3207917 = 1202969) (by norm_num)
theorem B2138611 : Blo 1899435 2138611 := bstep (se 1 (by rfl) ⟨1603958, by rfl⟩ : syracuseStep 2138611 = 3207917) B3207917
theorem B2851481 : Blo 1899435 2851481 := bstep (se 2 (by rfl) ⟨1069305, by rfl⟩ : syracuseStep 2851481 = 2138611) B2138611
theorem B1900987 : Blo 1899435 1900987 := bstep (se 1 (by rfl) ⟨1425740, by rfl⟩ : syracuseStep 1900987 = 2851481) B2851481
theorem B10276949 : Blo 1899435 10276949 := bbase (se 8 (by rfl) ⟨60216, by rfl⟩ : syracuseStep 10276949 = 120433) (by norm_num)
theorem B6851299 : Blo 1899435 6851299 := bstep (se 1 (by rfl) ⟨5138474, by rfl⟩ : syracuseStep 6851299 = 10276949) B10276949
theorem B9135065 : Blo 1899435 9135065 := bstep (se 2 (by rfl) ⟨3425649, by rfl⟩ : syracuseStep 9135065 = 6851299) B6851299
theorem B24360173 : Blo 1899435 24360173 := bstep (se 3 (by rfl) ⟨4567532, by rfl⟩ : syracuseStep 24360173 = 9135065) B9135065
theorem B16240115 : Blo 1899435 16240115 := bstep (se 1 (by rfl) ⟨12180086, by rfl⟩ : syracuseStep 16240115 = 24360173) B24360173
theorem B10826743 : Blo 1899435 10826743 := bstep (se 1 (by rfl) ⟨8120057, by rfl⟩ : syracuseStep 10826743 = 16240115) B16240115
theorem B14435657 : Blo 1899435 14435657 := bstep (se 2 (by rfl) ⟨5413371, by rfl⟩ : syracuseStep 14435657 = 10826743) B10826743
theorem B9623771 : Blo 1899435 9623771 := bstep (se 1 (by rfl) ⟨7217828, by rfl⟩ : syracuseStep 9623771 = 14435657) B14435657
theorem B6415847 : Blo 1899435 6415847 := bstep (se 1 (by rfl) ⟨4811885, by rfl⟩ : syracuseStep 6415847 = 9623771) B9623771
theorem B4277231 : Blo 1899435 4277231 := bstep (se 1 (by rfl) ⟨3207923, by rfl⟩ : syracuseStep 4277231 = 6415847) B6415847
theorem B2851487 : Blo 1899435 2851487 := bstep (se 1 (by rfl) ⟨2138615, by rfl⟩ : syracuseStep 2851487 = 4277231) B4277231
theorem B1900991 : Blo 1899435 1900991 := bstep (se 1 (by rfl) ⟨1425743, by rfl⟩ : syracuseStep 1900991 = 2851487) B2851487
theorem B2851493 : Blo 1899435 2851493 := bbase (se 4 (by rfl) ⟨267327, by rfl⟩ : syracuseStep 2851493 = 534655) (by norm_num)
theorem B1900995 : Blo 1899435 1900995 := bstep (se 1 (by rfl) ⟨1425746, by rfl⟩ : syracuseStep 1900995 = 2851493) B2851493
theorem B2405953 : Blo 1899435 2405953 := bbase (se 2 (by rfl) ⟨902232, by rfl⟩ : syracuseStep 2405953 = 1804465) (by norm_num)
theorem B3207937 : Blo 1899435 3207937 := bstep (se 2 (by rfl) ⟨1202976, by rfl⟩ : syracuseStep 3207937 = 2405953) B2405953
theorem B4277249 : Blo 1899435 4277249 := bstep (se 2 (by rfl) ⟨1603968, by rfl⟩ : syracuseStep 4277249 = 3207937) B3207937
theorem B2851499 : Blo 1899435 2851499 := bstep (se 1 (by rfl) ⟨2138624, by rfl⟩ : syracuseStep 2851499 = 4277249) B4277249
theorem B1900999 : Blo 1899435 1900999 := bstep (se 1 (by rfl) ⟨1425749, by rfl⟩ : syracuseStep 1900999 = 2851499) B2851499
theorem B2138629 : Blo 1899435 2138629 := bbase (se 4 (by rfl) ⟨200496, by rfl⟩ : syracuseStep 2138629 = 400993) (by norm_num)
theorem B2851505 : Blo 1899435 2851505 := bstep (se 2 (by rfl) ⟨1069314, by rfl⟩ : syracuseStep 2851505 = 2138629) B2138629
theorem B1901003 : Blo 1899435 1901003 := bstep (se 1 (by rfl) ⟨1425752, by rfl⟩ : syracuseStep 1901003 = 2851505) B2851505
theorem B2706709 : Blo 1899435 2706709 := bbase (se 6 (by rfl) ⟨63438, by rfl⟩ : syracuseStep 2706709 = 126877) (by norm_num)
theorem B3608945 : Blo 1899435 3608945 := bstep (se 2 (by rfl) ⟨1353354, by rfl⟩ : syracuseStep 3608945 = 2706709) B2706709
theorem B2405963 : Blo 1899435 2405963 := bstep (se 1 (by rfl) ⟨1804472, by rfl⟩ : syracuseStep 2405963 = 3608945) B3608945
theorem B6415901 : Blo 1899435 6415901 := bstep (se 3 (by rfl) ⟨1202981, by rfl⟩ : syracuseStep 6415901 = 2405963) B2405963
theorem B4277267 : Blo 1899435 4277267 := bstep (se 1 (by rfl) ⟨3207950, by rfl⟩ : syracuseStep 4277267 = 6415901) B6415901
theorem B2851511 : Blo 1899435 2851511 := bstep (se 1 (by rfl) ⟨2138633, by rfl⟩ : syracuseStep 2851511 = 4277267) B4277267
theorem B1901007 : Blo 1899435 1901007 := bstep (se 1 (by rfl) ⟨1425755, by rfl⟩ : syracuseStep 1901007 = 2851511) B2851511
theorem B2851517 : Blo 1899435 2851517 := bbase (se 3 (by rfl) ⟨534659, by rfl⟩ : syracuseStep 2851517 = 1069319) (by norm_num)
theorem B1901011 : Blo 1899435 1901011 := bstep (se 1 (by rfl) ⟨1425758, by rfl⟩ : syracuseStep 1901011 = 2851517) B2851517
theorem B4277285 : Blo 1899435 4277285 := bbase (se 4 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 4277285 = 801991) (by norm_num)
theorem B2851523 : Blo 1899435 2851523 := bstep (se 1 (by rfl) ⟨2138642, by rfl⟩ : syracuseStep 2851523 = 4277285) B4277285
theorem B1901015 : Blo 1899435 1901015 := bstep (se 1 (by rfl) ⟨1425761, by rfl⟩ : syracuseStep 1901015 = 2851523) B2851523
theorem B4811957 : Blo 1899435 4811957 := bbase (se 5 (by rfl) ⟨225560, by rfl⟩ : syracuseStep 4811957 = 451121) (by norm_num)
theorem B3207971 : Blo 1899435 3207971 := bstep (se 1 (by rfl) ⟨2405978, by rfl⟩ : syracuseStep 3207971 = 4811957) B4811957
theorem B2138647 : Blo 1899435 2138647 := bstep (se 1 (by rfl) ⟨1603985, by rfl⟩ : syracuseStep 2138647 = 3207971) B3207971
theorem B2851529 : Blo 1899435 2851529 := bstep (se 2 (by rfl) ⟨1069323, by rfl⟩ : syracuseStep 2851529 = 2138647) B2138647
theorem B1901019 : Blo 1899435 1901019 := bstep (se 1 (by rfl) ⟨1425764, by rfl⟩ : syracuseStep 1901019 = 2851529) B2851529
theorem B2283805 : Blo 1899435 2283805 := bbase (se 3 (by rfl) ⟨428213, by rfl⟩ : syracuseStep 2283805 = 856427) (by norm_num)
theorem B12180293 : Blo 1899435 12180293 := bstep (se 4 (by rfl) ⟨1141902, by rfl⟩ : syracuseStep 12180293 = 2283805) B2283805
theorem B8120195 : Blo 1899435 8120195 := bstep (se 1 (by rfl) ⟨6090146, by rfl⟩ : syracuseStep 8120195 = 12180293) B12180293
theorem B5413463 : Blo 1899435 5413463 := bstep (se 1 (by rfl) ⟨4060097, by rfl⟩ : syracuseStep 5413463 = 8120195) B8120195
theorem B3608975 : Blo 1899435 3608975 := bstep (se 1 (by rfl) ⟨2706731, by rfl⟩ : syracuseStep 3608975 = 5413463) B5413463
theorem B9623933 : Blo 1899435 9623933 := bstep (se 3 (by rfl) ⟨1804487, by rfl⟩ : syracuseStep 9623933 = 3608975) B3608975
theorem B6415955 : Blo 1899435 6415955 := bstep (se 1 (by rfl) ⟨4811966, by rfl⟩ : syracuseStep 6415955 = 9623933) B9623933
theorem B4277303 : Blo 1899435 4277303 := bstep (se 1 (by rfl) ⟨3207977, by rfl⟩ : syracuseStep 4277303 = 6415955) B6415955
theorem B2851535 : Blo 1899435 2851535 := bstep (se 1 (by rfl) ⟨2138651, by rfl⟩ : syracuseStep 2851535 = 4277303) B4277303
theorem B1901023 : Blo 1899435 1901023 := bstep (se 1 (by rfl) ⟨1425767, by rfl⟩ : syracuseStep 1901023 = 2851535) B2851535
theorem B2851541 : Blo 1899435 2851541 := bbase (se 7 (by rfl) ⟨33416, by rfl⟩ : syracuseStep 2851541 = 66833) (by norm_num)
theorem B1901027 : Blo 1899435 1901027 := bstep (se 1 (by rfl) ⟨1425770, by rfl⟩ : syracuseStep 1901027 = 2851541) B2851541
theorem B2167841 : Blo 1899435 2167841 := bbase (se 2 (by rfl) ⟨812940, by rfl⟩ : syracuseStep 2167841 = 1625881) (by norm_num)
theorem B5780909 : Blo 1899435 5780909 := bstep (se 3 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 5780909 = 2167841) B2167841
theorem B3853939 : Blo 1899435 3853939 := bstep (se 1 (by rfl) ⟨2890454, by rfl⟩ : syracuseStep 3853939 = 5780909) B5780909
theorem B5138585 : Blo 1899435 5138585 := bstep (se 2 (by rfl) ⟨1926969, by rfl⟩ : syracuseStep 5138585 = 3853939) B3853939
theorem B3425723 : Blo 1899435 3425723 := bstep (se 1 (by rfl) ⟨2569292, by rfl⟩ : syracuseStep 3425723 = 5138585) B5138585
theorem B2283815 : Blo 1899435 2283815 := bstep (se 1 (by rfl) ⟨1712861, by rfl⟩ : syracuseStep 2283815 = 3425723) B3425723
theorem B6090173 : Blo 1899435 6090173 := bstep (se 3 (by rfl) ⟨1141907, by rfl⟩ : syracuseStep 6090173 = 2283815) B2283815
theorem B4060115 : Blo 1899435 4060115 := bstep (se 1 (by rfl) ⟨3045086, by rfl⟩ : syracuseStep 4060115 = 6090173) B6090173
theorem B2706743 : Blo 1899435 2706743 := bstep (se 1 (by rfl) ⟨2030057, by rfl⟩ : syracuseStep 2706743 = 4060115) B4060115
theorem B7217981 : Blo 1899435 7217981 := bstep (se 3 (by rfl) ⟨1353371, by rfl⟩ : syracuseStep 7217981 = 2706743) B2706743
theorem B4811987 : Blo 1899435 4811987 := bstep (se 1 (by rfl) ⟨3608990, by rfl⟩ : syracuseStep 4811987 = 7217981) B7217981
theorem B3207991 : Blo 1899435 3207991 := bstep (se 1 (by rfl) ⟨2405993, by rfl⟩ : syracuseStep 3207991 = 4811987) B4811987
theorem B4277321 : Blo 1899435 4277321 := bstep (se 2 (by rfl) ⟨1603995, by rfl⟩ : syracuseStep 4277321 = 3207991) B3207991
theorem B2851547 : Blo 1899435 2851547 := bstep (se 1 (by rfl) ⟨2138660, by rfl⟩ : syracuseStep 2851547 = 4277321) B4277321
theorem B1901031 : Blo 1899435 1901031 := bstep (se 1 (by rfl) ⟨1425773, by rfl⟩ : syracuseStep 1901031 = 2851547) B2851547
theorem B2138665 : Blo 1899435 2138665 := bbase (se 2 (by rfl) ⟨801999, by rfl⟩ : syracuseStep 2138665 = 1603999) (by norm_num)
theorem B2851553 : Blo 1899435 2851553 := bstep (se 2 (by rfl) ⟨1069332, by rfl⟩ : syracuseStep 2851553 = 2138665) B2138665
theorem B1901035 : Blo 1899435 1901035 := bstep (se 1 (by rfl) ⟨1425776, by rfl⟩ : syracuseStep 1901035 = 2851553) B2851553
theorem B2167849 : Blo 1899435 2167849 := bbase (se 2 (by rfl) ⟨812943, by rfl⟩ : syracuseStep 2167849 = 1625887) (by norm_num)
theorem B11561861 : Blo 1899435 11561861 := bstep (se 4 (by rfl) ⟨1083924, by rfl⟩ : syracuseStep 11561861 = 2167849) B2167849
theorem B7707907 : Blo 1899435 7707907 := bstep (se 1 (by rfl) ⟨5780930, by rfl⟩ : syracuseStep 7707907 = 11561861) B11561861
theorem B10277209 : Blo 1899435 10277209 := bstep (se 2 (by rfl) ⟨3853953, by rfl⟩ : syracuseStep 10277209 = 7707907) B7707907
theorem B13702945 : Blo 1899435 13702945 := bstep (se 2 (by rfl) ⟨5138604, by rfl⟩ : syracuseStep 13702945 = 10277209) B10277209
theorem B18270593 : Blo 1899435 18270593 := bstep (se 2 (by rfl) ⟨6851472, by rfl⟩ : syracuseStep 18270593 = 13702945) B13702945
theorem B12180395 : Blo 1899435 12180395 := bstep (se 1 (by rfl) ⟨9135296, by rfl⟩ : syracuseStep 12180395 = 18270593) B18270593
theorem B8120263 : Blo 1899435 8120263 := bstep (se 1 (by rfl) ⟨6090197, by rfl⟩ : syracuseStep 8120263 = 12180395) B12180395
theorem B10827017 : Blo 1899435 10827017 := bstep (se 2 (by rfl) ⟨4060131, by rfl⟩ : syracuseStep 10827017 = 8120263) B8120263
theorem B7218011 : Blo 1899435 7218011 := bstep (se 1 (by rfl) ⟨5413508, by rfl⟩ : syracuseStep 7218011 = 10827017) B10827017
theorem B4812007 : Blo 1899435 4812007 := bstep (se 1 (by rfl) ⟨3609005, by rfl⟩ : syracuseStep 4812007 = 7218011) B7218011
theorem B6416009 : Blo 1899435 6416009 := bstep (se 2 (by rfl) ⟨2406003, by rfl⟩ : syracuseStep 6416009 = 4812007) B4812007
theorem B4277339 : Blo 1899435 4277339 := bstep (se 1 (by rfl) ⟨3208004, by rfl⟩ : syracuseStep 4277339 = 6416009) B6416009
theorem B2851559 : Blo 1899435 2851559 := bstep (se 1 (by rfl) ⟨2138669, by rfl⟩ : syracuseStep 2851559 = 4277339) B4277339
theorem B1901039 : Blo 1899435 1901039 := bstep (se 1 (by rfl) ⟨1425779, by rfl⟩ : syracuseStep 1901039 = 2851559) B2851559
theorem B2851565 : Blo 1899435 2851565 := bbase (se 3 (by rfl) ⟨534668, by rfl⟩ : syracuseStep 2851565 = 1069337) (by norm_num)
theorem B1901043 : Blo 1899435 1901043 := bstep (se 1 (by rfl) ⟨1425782, by rfl⟩ : syracuseStep 1901043 = 2851565) B2851565
theorem B4277357 : Blo 1899435 4277357 := bbase (se 3 (by rfl) ⟨802004, by rfl⟩ : syracuseStep 4277357 = 1604009) (by norm_num)
theorem B2851571 : Blo 1899435 2851571 := bstep (se 1 (by rfl) ⟨2138678, by rfl⟩ : syracuseStep 2851571 = 4277357) B4277357
theorem B1901047 : Blo 1899435 1901047 := bstep (se 1 (by rfl) ⟨1425785, by rfl⟩ : syracuseStep 1901047 = 2851571) B2851571
theorem B3609029 : Blo 1899435 3609029 := bbase (se 4 (by rfl) ⟨338346, by rfl⟩ : syracuseStep 3609029 = 676693) (by norm_num)
theorem B2406019 : Blo 1899435 2406019 := bstep (se 1 (by rfl) ⟨1804514, by rfl⟩ : syracuseStep 2406019 = 3609029) B3609029
theorem B3208025 : Blo 1899435 3208025 := bstep (se 2 (by rfl) ⟨1203009, by rfl⟩ : syracuseStep 3208025 = 2406019) B2406019
theorem B2138683 : Blo 1899435 2138683 := bstep (se 1 (by rfl) ⟨1604012, by rfl⟩ : syracuseStep 2138683 = 3208025) B3208025
theorem B2851577 : Blo 1899435 2851577 := bstep (se 2 (by rfl) ⟨1069341, by rfl⟩ : syracuseStep 2851577 = 2138683) B2138683
theorem B1901051 : Blo 1899435 1901051 := bstep (se 1 (by rfl) ⟨1425788, by rfl⟩ : syracuseStep 1901051 = 2851577) B2851577
theorem B3658277 : Blo 1899435 3658277 := bbase (se 4 (by rfl) ⟨342963, by rfl⟩ : syracuseStep 3658277 = 685927) (by norm_num)
theorem B2438851 : Blo 1899435 2438851 := bstep (se 1 (by rfl) ⟨1829138, by rfl⟩ : syracuseStep 2438851 = 3658277) B3658277
theorem B3251801 : Blo 1899435 3251801 := bstep (se 2 (by rfl) ⟨1219425, by rfl⟩ : syracuseStep 3251801 = 2438851) B2438851
theorem B2167867 : Blo 1899435 2167867 := bstep (se 1 (by rfl) ⟨1625900, by rfl⟩ : syracuseStep 2167867 = 3251801) B3251801
theorem B11561957 : Blo 1899435 11561957 := bstep (se 4 (by rfl) ⟨1083933, by rfl⟩ : syracuseStep 11561957 = 2167867) B2167867
theorem B7707971 : Blo 1899435 7707971 := bstep (se 1 (by rfl) ⟨5780978, by rfl⟩ : syracuseStep 7707971 = 11561957) B11561957
theorem B5138647 : Blo 1899435 5138647 := bstep (se 1 (by rfl) ⟨3853985, by rfl⟩ : syracuseStep 5138647 = 7707971) B7707971
theorem B27406117 : Blo 1899435 27406117 := bstep (se 4 (by rfl) ⟨2569323, by rfl⟩ : syracuseStep 27406117 = 5138647) B5138647
theorem B36541489 : Blo 1899435 36541489 := bstep (se 2 (by rfl) ⟨13703058, by rfl⟩ : syracuseStep 36541489 = 27406117) B27406117
theorem B48721985 : Blo 1899435 48721985 := bstep (se 2 (by rfl) ⟨18270744, by rfl⟩ : syracuseStep 48721985 = 36541489) B36541489
theorem B32481323 : Blo 1899435 32481323 := bstep (se 1 (by rfl) ⟨24360992, by rfl⟩ : syracuseStep 32481323 = 48721985) B48721985
theorem B21654215 : Blo 1899435 21654215 := bstep (se 1 (by rfl) ⟨16240661, by rfl⟩ : syracuseStep 21654215 = 32481323) B32481323
theorem B14436143 : Blo 1899435 14436143 := bstep (se 1 (by rfl) ⟨10827107, by rfl⟩ : syracuseStep 14436143 = 21654215) B21654215
theorem B9624095 : Blo 1899435 9624095 := bstep (se 1 (by rfl) ⟨7218071, by rfl⟩ : syracuseStep 9624095 = 14436143) B14436143
theorem B6416063 : Blo 1899435 6416063 := bstep (se 1 (by rfl) ⟨4812047, by rfl⟩ : syracuseStep 6416063 = 9624095) B9624095
theorem B4277375 : Blo 1899435 4277375 := bstep (se 1 (by rfl) ⟨3208031, by rfl⟩ : syracuseStep 4277375 = 6416063) B6416063
theorem B2851583 : Blo 1899435 2851583 := bstep (se 1 (by rfl) ⟨2138687, by rfl⟩ : syracuseStep 2851583 = 4277375) B4277375
theorem B1901055 : Blo 1899435 1901055 := bstep (se 1 (by rfl) ⟨1425791, by rfl⟩ : syracuseStep 1901055 = 2851583) B2851583
theorem B2851589 : Blo 1899435 2851589 := bbase (se 4 (by rfl) ⟨267336, by rfl⟩ : syracuseStep 2851589 = 534673) (by norm_num)
theorem B1901059 : Blo 1899435 1901059 := bstep (se 1 (by rfl) ⟨1425794, by rfl⟩ : syracuseStep 1901059 = 2851589) B2851589
theorem B3208045 : Blo 1899435 3208045 := bbase (se 3 (by rfl) ⟨601508, by rfl⟩ : syracuseStep 3208045 = 1203017) (by norm_num)
theorem B4277393 : Blo 1899435 4277393 := bstep (se 2 (by rfl) ⟨1604022, by rfl⟩ : syracuseStep 4277393 = 3208045) B3208045
theorem B2851595 : Blo 1899435 2851595 := bstep (se 1 (by rfl) ⟨2138696, by rfl⟩ : syracuseStep 2851595 = 4277393) B4277393
theorem B1901063 : Blo 1899435 1901063 := bstep (se 1 (by rfl) ⟨1425797, by rfl⟩ : syracuseStep 1901063 = 2851595) B2851595
theorem B2138701 : Blo 1899435 2138701 := bbase (se 3 (by rfl) ⟨401006, by rfl⟩ : syracuseStep 2138701 = 802013) (by norm_num)
theorem B2851601 : Blo 1899435 2851601 := bstep (se 2 (by rfl) ⟨1069350, by rfl⟩ : syracuseStep 2851601 = 2138701) B2138701
theorem B1901067 : Blo 1899435 1901067 := bstep (se 1 (by rfl) ⟨1425800, by rfl⟩ : syracuseStep 1901067 = 2851601) B2851601
theorem B6416117 : Blo 1899435 6416117 := bbase (se 5 (by rfl) ⟨300755, by rfl⟩ : syracuseStep 6416117 = 601511) (by norm_num)
theorem B4277411 : Blo 1899435 4277411 := bstep (se 1 (by rfl) ⟨3208058, by rfl⟩ : syracuseStep 4277411 = 6416117) B6416117
theorem B2851607 : Blo 1899435 2851607 := bstep (se 1 (by rfl) ⟨2138705, by rfl⟩ : syracuseStep 2851607 = 4277411) B4277411
theorem B1901071 : Blo 1899435 1901071 := bstep (se 1 (by rfl) ⟨1425803, by rfl⟩ : syracuseStep 1901071 = 2851607) B2851607
theorem B2851613 : Blo 1899435 2851613 := bbase (se 3 (by rfl) ⟨534677, by rfl⟩ : syracuseStep 2851613 = 1069355) (by norm_num)
theorem B1901075 : Blo 1899435 1901075 := bstep (se 1 (by rfl) ⟨1425806, by rfl⟩ : syracuseStep 1901075 = 2851613) B2851613
theorem B4277429 : Blo 1899435 4277429 := bbase (se 5 (by rfl) ⟨200504, by rfl⟩ : syracuseStep 4277429 = 401009) (by norm_num)
theorem B2851619 : Blo 1899435 2851619 := bstep (se 1 (by rfl) ⟨2138714, by rfl⟩ : syracuseStep 2851619 = 4277429) B4277429
theorem B1901079 : Blo 1899435 1901079 := bstep (se 1 (by rfl) ⟨1425809, by rfl⟩ : syracuseStep 1901079 = 2851619) B2851619
theorem B2030113 : Blo 1899435 2030113 := bbase (se 2 (by rfl) ⟨761292, by rfl⟩ : syracuseStep 2030113 = 1522585) (by norm_num)
theorem B10827269 : Blo 1899435 10827269 := bstep (se 4 (by rfl) ⟨1015056, by rfl⟩ : syracuseStep 10827269 = 2030113) B2030113
theorem B7218179 : Blo 1899435 7218179 := bstep (se 1 (by rfl) ⟨5413634, by rfl⟩ : syracuseStep 7218179 = 10827269) B10827269
theorem B4812119 : Blo 1899435 4812119 := bstep (se 1 (by rfl) ⟨3609089, by rfl⟩ : syracuseStep 4812119 = 7218179) B7218179
theorem B3208079 : Blo 1899435 3208079 := bstep (se 1 (by rfl) ⟨2406059, by rfl⟩ : syracuseStep 3208079 = 4812119) B4812119
theorem B2138719 : Blo 1899435 2138719 := bstep (se 1 (by rfl) ⟨1604039, by rfl⟩ : syracuseStep 2138719 = 3208079) B3208079
theorem B2851625 : Blo 1899435 2851625 := bstep (se 2 (by rfl) ⟨1069359, by rfl⟩ : syracuseStep 2851625 = 2138719) B2138719
theorem B1901083 : Blo 1899435 1901083 := bstep (se 1 (by rfl) ⟨1425812, by rfl⟩ : syracuseStep 1901083 = 2851625) B2851625
theorem B2030117 : Blo 1899435 2030117 := bbase (se 4 (by rfl) ⟨190323, by rfl⟩ : syracuseStep 2030117 = 380647) (by norm_num)
theorem B5413645 : Blo 1899435 5413645 := bstep (se 3 (by rfl) ⟨1015058, by rfl⟩ : syracuseStep 5413645 = 2030117) B2030117
theorem B7218193 : Blo 1899435 7218193 := bstep (se 2 (by rfl) ⟨2706822, by rfl⟩ : syracuseStep 7218193 = 5413645) B5413645
theorem B9624257 : Blo 1899435 9624257 := bstep (se 2 (by rfl) ⟨3609096, by rfl⟩ : syracuseStep 9624257 = 7218193) B7218193
theorem B6416171 : Blo 1899435 6416171 := bstep (se 1 (by rfl) ⟨4812128, by rfl⟩ : syracuseStep 6416171 = 9624257) B9624257
theorem B4277447 : Blo 1899435 4277447 := bstep (se 1 (by rfl) ⟨3208085, by rfl⟩ : syracuseStep 4277447 = 6416171) B6416171
theorem B2851631 : Blo 1899435 2851631 := bstep (se 1 (by rfl) ⟨2138723, by rfl⟩ : syracuseStep 2851631 = 4277447) B4277447
theorem B1901087 : Blo 1899435 1901087 := bstep (se 1 (by rfl) ⟨1425815, by rfl⟩ : syracuseStep 1901087 = 2851631) B2851631
theorem B2851637 : Blo 1899435 2851637 := bbase (se 5 (by rfl) ⟨133670, by rfl⟩ : syracuseStep 2851637 = 267341) (by norm_num)
theorem B1901091 : Blo 1899435 1901091 := bstep (se 1 (by rfl) ⟨1425818, by rfl⟩ : syracuseStep 1901091 = 2851637) B2851637
theorem B4812149 : Blo 1899435 4812149 := bbase (se 5 (by rfl) ⟨225569, by rfl⟩ : syracuseStep 4812149 = 451139) (by norm_num)
theorem B3208099 : Blo 1899435 3208099 := bstep (se 1 (by rfl) ⟨2406074, by rfl⟩ : syracuseStep 3208099 = 4812149) B4812149
theorem B4277465 : Blo 1899435 4277465 := bstep (se 2 (by rfl) ⟨1604049, by rfl⟩ : syracuseStep 4277465 = 3208099) B3208099
theorem B2851643 : Blo 1899435 2851643 := bstep (se 1 (by rfl) ⟨2138732, by rfl⟩ : syracuseStep 2851643 = 4277465) B4277465
theorem B1901095 : Blo 1899435 1901095 := bstep (se 1 (by rfl) ⟨1425821, by rfl⟩ : syracuseStep 1901095 = 2851643) B2851643
theorem B2138737 : Blo 1899435 2138737 := bbase (se 2 (by rfl) ⟨802026, by rfl⟩ : syracuseStep 2138737 = 1604053) (by norm_num)
theorem B2851649 : Blo 1899435 2851649 := bstep (se 2 (by rfl) ⟨1069368, by rfl⟩ : syracuseStep 2851649 = 2138737) B2138737
theorem B1901099 : Blo 1899435 1901099 := bstep (se 1 (by rfl) ⟨1425824, by rfl⟩ : syracuseStep 1901099 = 2851649) B2851649
theorem B9135605 : Blo 1899435 9135605 := bbase (se 5 (by rfl) ⟨428231, by rfl⟩ : syracuseStep 9135605 = 856463) (by norm_num)
theorem B6090403 : Blo 1899435 6090403 := bstep (se 1 (by rfl) ⟨4567802, by rfl⟩ : syracuseStep 6090403 = 9135605) B9135605
theorem B8120537 : Blo 1899435 8120537 := bstep (se 2 (by rfl) ⟨3045201, by rfl⟩ : syracuseStep 8120537 = 6090403) B6090403
theorem B5413691 : Blo 1899435 5413691 := bstep (se 1 (by rfl) ⟨4060268, by rfl⟩ : syracuseStep 5413691 = 8120537) B8120537
theorem B3609127 : Blo 1899435 3609127 := bstep (se 1 (by rfl) ⟨2706845, by rfl⟩ : syracuseStep 3609127 = 5413691) B5413691
theorem B4812169 : Blo 1899435 4812169 := bstep (se 2 (by rfl) ⟨1804563, by rfl⟩ : syracuseStep 4812169 = 3609127) B3609127
theorem B6416225 : Blo 1899435 6416225 := bstep (se 2 (by rfl) ⟨2406084, by rfl⟩ : syracuseStep 6416225 = 4812169) B4812169
theorem B4277483 : Blo 1899435 4277483 := bstep (se 1 (by rfl) ⟨3208112, by rfl⟩ : syracuseStep 4277483 = 6416225) B6416225
theorem B2851655 : Blo 1899435 2851655 := bstep (se 1 (by rfl) ⟨2138741, by rfl⟩ : syracuseStep 2851655 = 4277483) B4277483
theorem B1901103 : Blo 1899435 1901103 := bstep (se 1 (by rfl) ⟨1425827, by rfl⟩ : syracuseStep 1901103 = 2851655) B2851655
theorem B2851661 : Blo 1899435 2851661 := bbase (se 3 (by rfl) ⟨534686, by rfl⟩ : syracuseStep 2851661 = 1069373) (by norm_num)
theorem B1901107 : Blo 1899435 1901107 := bstep (se 1 (by rfl) ⟨1425830, by rfl⟩ : syracuseStep 1901107 = 2851661) B2851661
theorem B4277501 : Blo 1899435 4277501 := bbase (se 3 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 4277501 = 1604063) (by norm_num)
theorem B2851667 : Blo 1899435 2851667 := bstep (se 1 (by rfl) ⟨2138750, by rfl⟩ : syracuseStep 2851667 = 4277501) B4277501
theorem B1901111 : Blo 1899435 1901111 := bstep (se 1 (by rfl) ⟨1425833, by rfl⟩ : syracuseStep 1901111 = 2851667) B2851667
theorem B3208133 : Blo 1899435 3208133 := bbase (se 4 (by rfl) ⟨300762, by rfl⟩ : syracuseStep 3208133 = 601525) (by norm_num)
theorem B2138755 : Blo 1899435 2138755 := bstep (se 1 (by rfl) ⟨1604066, by rfl⟩ : syracuseStep 2138755 = 3208133) B3208133
theorem B2851673 : Blo 1899435 2851673 := bstep (se 2 (by rfl) ⟨1069377, by rfl⟩ : syracuseStep 2851673 = 2138755) B2138755
theorem B1901115 : Blo 1899435 1901115 := bstep (se 1 (by rfl) ⟨1425836, by rfl⟩ : syracuseStep 1901115 = 2851673) B2851673
theorem B14436629 : Blo 1899435 14436629 := bbase (se 6 (by rfl) ⟨338358, by rfl⟩ : syracuseStep 14436629 = 676717) (by norm_num)
theorem B9624419 : Blo 1899435 9624419 := bstep (se 1 (by rfl) ⟨7218314, by rfl⟩ : syracuseStep 9624419 = 14436629) B14436629
theorem B6416279 : Blo 1899435 6416279 := bstep (se 1 (by rfl) ⟨4812209, by rfl⟩ : syracuseStep 6416279 = 9624419) B9624419
theorem B4277519 : Blo 1899435 4277519 := bstep (se 1 (by rfl) ⟨3208139, by rfl⟩ : syracuseStep 4277519 = 6416279) B6416279
theorem B2851679 : Blo 1899435 2851679 := bstep (se 1 (by rfl) ⟨2138759, by rfl⟩ : syracuseStep 2851679 = 4277519) B4277519
theorem B1901119 : Blo 1899435 1901119 := bstep (se 1 (by rfl) ⟨1425839, by rfl⟩ : syracuseStep 1901119 = 2851679) B2851679
theorem B2851685 : Blo 1899435 2851685 := bbase (se 4 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 2851685 = 534691) (by norm_num)
theorem B1901123 : Blo 1899435 1901123 := bstep (se 1 (by rfl) ⟨1425842, by rfl⟩ : syracuseStep 1901123 = 2851685) B2851685
theorem B3609173 : Blo 1899435 3609173 := bbase (se 8 (by rfl) ⟨21147, by rfl⟩ : syracuseStep 3609173 = 42295) (by norm_num)
theorem B2406115 : Blo 1899435 2406115 := bstep (se 1 (by rfl) ⟨1804586, by rfl⟩ : syracuseStep 2406115 = 3609173) B3609173
theorem B3208153 : Blo 1899435 3208153 := bstep (se 2 (by rfl) ⟨1203057, by rfl⟩ : syracuseStep 3208153 = 2406115) B2406115
theorem B4277537 : Blo 1899435 4277537 := bstep (se 2 (by rfl) ⟨1604076, by rfl⟩ : syracuseStep 4277537 = 3208153) B3208153
theorem B2851691 : Blo 1899435 2851691 := bstep (se 1 (by rfl) ⟨2138768, by rfl⟩ : syracuseStep 2851691 = 4277537) B4277537
theorem B1901127 : Blo 1899435 1901127 := bstep (se 1 (by rfl) ⟨1425845, by rfl⟩ : syracuseStep 1901127 = 2851691) B2851691
theorem B2138773 : Blo 1899435 2138773 := bbase (se 6 (by rfl) ⟨50127, by rfl⟩ : syracuseStep 2138773 = 100255) (by norm_num)
theorem B2851697 : Blo 1899435 2851697 := bstep (se 2 (by rfl) ⟨1069386, by rfl⟩ : syracuseStep 2851697 = 2138773) B2138773
theorem B1901131 : Blo 1899435 1901131 := bstep (se 1 (by rfl) ⟨1425848, by rfl⟩ : syracuseStep 1901131 = 2851697) B2851697
theorem B2406125 : Blo 1899435 2406125 := bbase (se 3 (by rfl) ⟨451148, by rfl⟩ : syracuseStep 2406125 = 902297) (by norm_num)
theorem B6416333 : Blo 1899435 6416333 := bstep (se 3 (by rfl) ⟨1203062, by rfl⟩ : syracuseStep 6416333 = 2406125) B2406125
theorem B4277555 : Blo 1899435 4277555 := bstep (se 1 (by rfl) ⟨3208166, by rfl⟩ : syracuseStep 4277555 = 6416333) B6416333
theorem B2851703 : Blo 1899435 2851703 := bstep (se 1 (by rfl) ⟨2138777, by rfl⟩ : syracuseStep 2851703 = 4277555) B4277555
theorem B1901135 : Blo 1899435 1901135 := bstep (se 1 (by rfl) ⟨1425851, by rfl⟩ : syracuseStep 1901135 = 2851703) B2851703
theorem B2851709 : Blo 1899435 2851709 := bbase (se 3 (by rfl) ⟨534695, by rfl⟩ : syracuseStep 2851709 = 1069391) (by norm_num)
theorem B1901139 : Blo 1899435 1901139 := bstep (se 1 (by rfl) ⟨1425854, by rfl⟩ : syracuseStep 1901139 = 2851709) B2851709
theorem B4277573 : Blo 1899435 4277573 := bbase (se 4 (by rfl) ⟨401022, by rfl⟩ : syracuseStep 4277573 = 802045) (by norm_num)
theorem B2851715 : Blo 1899435 2851715 := bstep (se 1 (by rfl) ⟨2138786, by rfl⟩ : syracuseStep 2851715 = 4277573) B4277573
theorem B1901143 : Blo 1899435 1901143 := bstep (se 1 (by rfl) ⟨1425857, by rfl⟩ : syracuseStep 1901143 = 2851715) B2851715
theorem B4567909 : Blo 1899435 4567909 := bbase (se 4 (by rfl) ⟨428241, by rfl⟩ : syracuseStep 4567909 = 856483) (by norm_num)
theorem B6090545 : Blo 1899435 6090545 := bstep (se 2 (by rfl) ⟨2283954, by rfl⟩ : syracuseStep 6090545 = 4567909) B4567909
theorem B4060363 : Blo 1899435 4060363 := bstep (se 1 (by rfl) ⟨3045272, by rfl⟩ : syracuseStep 4060363 = 6090545) B6090545
theorem B5413817 : Blo 1899435 5413817 := bstep (se 2 (by rfl) ⟨2030181, by rfl⟩ : syracuseStep 5413817 = 4060363) B4060363
theorem B3609211 : Blo 1899435 3609211 := bstep (se 1 (by rfl) ⟨2706908, by rfl⟩ : syracuseStep 3609211 = 5413817) B5413817
theorem B4812281 : Blo 1899435 4812281 := bstep (se 2 (by rfl) ⟨1804605, by rfl⟩ : syracuseStep 4812281 = 3609211) B3609211
theorem B3208187 : Blo 1899435 3208187 := bstep (se 1 (by rfl) ⟨2406140, by rfl⟩ : syracuseStep 3208187 = 4812281) B4812281
theorem B2138791 : Blo 1899435 2138791 := bstep (se 1 (by rfl) ⟨1604093, by rfl⟩ : syracuseStep 2138791 = 3208187) B3208187
theorem B2851721 : Blo 1899435 2851721 := bstep (se 2 (by rfl) ⟨1069395, by rfl⟩ : syracuseStep 2851721 = 2138791) B2138791
theorem B1901147 : Blo 1899435 1901147 := bstep (se 1 (by rfl) ⟨1425860, by rfl⟩ : syracuseStep 1901147 = 2851721) B2851721
theorem B9624581 : Blo 1899435 9624581 := bbase (se 4 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 9624581 = 1804609) (by norm_num)
theorem B6416387 : Blo 1899435 6416387 := bstep (se 1 (by rfl) ⟨4812290, by rfl⟩ : syracuseStep 6416387 = 9624581) B9624581
theorem B4277591 : Blo 1899435 4277591 := bstep (se 1 (by rfl) ⟨3208193, by rfl⟩ : syracuseStep 4277591 = 6416387) B6416387
theorem B2851727 : Blo 1899435 2851727 := bstep (se 1 (by rfl) ⟨2138795, by rfl⟩ : syracuseStep 2851727 = 4277591) B4277591
theorem B1901151 : Blo 1899435 1901151 := bstep (se 1 (by rfl) ⟨1425863, by rfl⟩ : syracuseStep 1901151 = 2851727) B2851727
theorem B2851733 : Blo 1899435 2851733 := bbase (se 6 (by rfl) ⟨66837, by rfl⟩ : syracuseStep 2851733 = 133675) (by norm_num)
theorem B1901155 : Blo 1899435 1901155 := bstep (se 1 (by rfl) ⟨1425866, by rfl⟩ : syracuseStep 1901155 = 2851733) B2851733
theorem B10827701 : Blo 1899435 10827701 := bbase (se 5 (by rfl) ⟨507548, by rfl⟩ : syracuseStep 10827701 = 1015097) (by norm_num)
theorem B7218467 : Blo 1899435 7218467 := bstep (se 1 (by rfl) ⟨5413850, by rfl⟩ : syracuseStep 7218467 = 10827701) B10827701
theorem B4812311 : Blo 1899435 4812311 := bstep (se 1 (by rfl) ⟨3609233, by rfl⟩ : syracuseStep 4812311 = 7218467) B7218467
theorem B3208207 : Blo 1899435 3208207 := bstep (se 1 (by rfl) ⟨2406155, by rfl⟩ : syracuseStep 3208207 = 4812311) B4812311
theorem B4277609 : Blo 1899435 4277609 := bstep (se 2 (by rfl) ⟨1604103, by rfl⟩ : syracuseStep 4277609 = 3208207) B3208207
theorem B2851739 : Blo 1899435 2851739 := bstep (se 1 (by rfl) ⟨2138804, by rfl⟩ : syracuseStep 2851739 = 4277609) B4277609
theorem B1901159 : Blo 1899435 1901159 := bstep (se 1 (by rfl) ⟨1425869, by rfl⟩ : syracuseStep 1901159 = 2851739) B2851739
theorem B2138809 : Blo 1899435 2138809 := bbase (se 2 (by rfl) ⟨802053, by rfl⟩ : syracuseStep 2138809 = 1604107) (by norm_num)
theorem B2851745 : Blo 1899435 2851745 := bstep (se 2 (by rfl) ⟨1069404, by rfl⟩ : syracuseStep 2851745 = 2138809) B2138809
theorem B1901163 : Blo 1899435 1901163 := bstep (se 1 (by rfl) ⟨1425872, by rfl⟩ : syracuseStep 1901163 = 2851745) B2851745
theorem B4060405 : Blo 1899435 4060405 := bbase (se 5 (by rfl) ⟨190331, by rfl⟩ : syracuseStep 4060405 = 380663) (by norm_num)
theorem B5413873 : Blo 1899435 5413873 := bstep (se 2 (by rfl) ⟨2030202, by rfl⟩ : syracuseStep 5413873 = 4060405) B4060405
theorem B7218497 : Blo 1899435 7218497 := bstep (se 2 (by rfl) ⟨2706936, by rfl⟩ : syracuseStep 7218497 = 5413873) B5413873
theorem B4812331 : Blo 1899435 4812331 := bstep (se 1 (by rfl) ⟨3609248, by rfl⟩ : syracuseStep 4812331 = 7218497) B7218497
theorem B6416441 : Blo 1899435 6416441 := bstep (se 2 (by rfl) ⟨2406165, by rfl⟩ : syracuseStep 6416441 = 4812331) B4812331
theorem B4277627 : Blo 1899435 4277627 := bstep (se 1 (by rfl) ⟨3208220, by rfl⟩ : syracuseStep 4277627 = 6416441) B6416441
theorem B2851751 : Blo 1899435 2851751 := bstep (se 1 (by rfl) ⟨2138813, by rfl⟩ : syracuseStep 2851751 = 4277627) B4277627
theorem B1901167 : Blo 1899435 1901167 := bstep (se 1 (by rfl) ⟨1425875, by rfl⟩ : syracuseStep 1901167 = 2851751) B2851751
theorem B2851757 : Blo 1899435 2851757 := bbase (se 3 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 2851757 = 1069409) (by norm_num)
theorem B1901171 : Blo 1899435 1901171 := bstep (se 1 (by rfl) ⟨1425878, by rfl⟩ : syracuseStep 1901171 = 2851757) B2851757
theorem B4277645 : Blo 1899435 4277645 := bbase (se 3 (by rfl) ⟨802058, by rfl⟩ : syracuseStep 4277645 = 1604117) (by norm_num)
theorem B2851763 : Blo 1899435 2851763 := bstep (se 1 (by rfl) ⟨2138822, by rfl⟩ : syracuseStep 2851763 = 4277645) B4277645
theorem B1901175 : Blo 1899435 1901175 := bstep (se 1 (by rfl) ⟨1425881, by rfl⟩ : syracuseStep 1901175 = 2851763) B2851763
theorem B2406181 : Blo 1899435 2406181 := bbase (se 4 (by rfl) ⟨225579, by rfl⟩ : syracuseStep 2406181 = 451159) (by norm_num)
theorem B3208241 : Blo 1899435 3208241 := bstep (se 2 (by rfl) ⟨1203090, by rfl⟩ : syracuseStep 3208241 = 2406181) B2406181
theorem B2138827 : Blo 1899435 2138827 := bstep (se 1 (by rfl) ⟨1604120, by rfl⟩ : syracuseStep 2138827 = 3208241) B3208241
theorem B2851769 : Blo 1899435 2851769 := bstep (se 2 (by rfl) ⟨1069413, by rfl⟩ : syracuseStep 2851769 = 2138827) B2138827
theorem B1901179 : Blo 1899435 1901179 := bstep (se 1 (by rfl) ⟨1425884, by rfl⟩ : syracuseStep 1901179 = 2851769) B2851769
theorem B4115837 : Blo 1899435 4115837 := bbase (se 3 (by rfl) ⟨771719, by rfl⟩ : syracuseStep 4115837 = 1543439) (by norm_num)
theorem B10975565 : Blo 1899435 10975565 := bstep (se 3 (by rfl) ⟨2057918, by rfl⟩ : syracuseStep 10975565 = 4115837) B4115837
theorem B29268173 : Blo 1899435 29268173 := bstep (se 3 (by rfl) ⟨5487782, by rfl⟩ : syracuseStep 29268173 = 10975565) B10975565
theorem B78048461 : Blo 1899435 78048461 := bstep (se 3 (by rfl) ⟨14634086, by rfl⟩ : syracuseStep 78048461 = 29268173) B29268173
theorem B52032307 : Blo 1899435 52032307 := bstep (se 1 (by rfl) ⟨39024230, by rfl⟩ : syracuseStep 52032307 = 78048461) B78048461
theorem B69376409 : Blo 1899435 69376409 := bstep (se 2 (by rfl) ⟨26016153, by rfl⟩ : syracuseStep 69376409 = 52032307) B52032307
theorem B46250939 : Blo 1899435 46250939 := bstep (se 1 (by rfl) ⟨34688204, by rfl⟩ : syracuseStep 46250939 = 69376409) B69376409
theorem B30833959 : Blo 1899435 30833959 := bstep (se 1 (by rfl) ⟨23125469, by rfl⟩ : syracuseStep 30833959 = 46250939) B46250939
theorem B41111945 : Blo 1899435 41111945 := bstep (se 2 (by rfl) ⟨15416979, by rfl⟩ : syracuseStep 41111945 = 30833959) B30833959
theorem B27407963 : Blo 1899435 27407963 := bstep (se 1 (by rfl) ⟨20555972, by rfl⟩ : syracuseStep 27407963 = 41111945) B41111945
theorem B18271975 : Blo 1899435 18271975 := bstep (se 1 (by rfl) ⟨13703981, by rfl⟩ : syracuseStep 18271975 = 27407963) B27407963
theorem B24362633 : Blo 1899435 24362633 := bstep (se 2 (by rfl) ⟨9135987, by rfl⟩ : syracuseStep 24362633 = 18271975) B18271975
theorem B16241755 : Blo 1899435 16241755 := bstep (se 1 (by rfl) ⟨12181316, by rfl⟩ : syracuseStep 16241755 = 24362633) B24362633
theorem B21655673 : Blo 1899435 21655673 := bstep (se 2 (by rfl) ⟨8120877, by rfl⟩ : syracuseStep 21655673 = 16241755) B16241755
theorem B14437115 : Blo 1899435 14437115 := bstep (se 1 (by rfl) ⟨10827836, by rfl⟩ : syracuseStep 14437115 = 21655673) B21655673
theorem B9624743 : Blo 1899435 9624743 := bstep (se 1 (by rfl) ⟨7218557, by rfl⟩ : syracuseStep 9624743 = 14437115) B14437115
theorem B6416495 : Blo 1899435 6416495 := bstep (se 1 (by rfl) ⟨4812371, by rfl⟩ : syracuseStep 6416495 = 9624743) B9624743
theorem B4277663 : Blo 1899435 4277663 := bstep (se 1 (by rfl) ⟨3208247, by rfl⟩ : syracuseStep 4277663 = 6416495) B6416495
theorem B2851775 : Blo 1899435 2851775 := bstep (se 1 (by rfl) ⟨2138831, by rfl⟩ : syracuseStep 2851775 = 4277663) B4277663
theorem B1901183 : Blo 1899435 1901183 := bstep (se 1 (by rfl) ⟨1425887, by rfl⟩ : syracuseStep 1901183 = 2851775) B2851775
theorem B2851781 : Blo 1899435 2851781 := bbase (se 4 (by rfl) ⟨267354, by rfl⟩ : syracuseStep 2851781 = 534709) (by norm_num)
theorem B1901187 : Blo 1899435 1901187 := bstep (se 1 (by rfl) ⟨1425890, by rfl⟩ : syracuseStep 1901187 = 2851781) B2851781
theorem B3208261 : Blo 1899435 3208261 := bbase (se 4 (by rfl) ⟨300774, by rfl⟩ : syracuseStep 3208261 = 601549) (by norm_num)
theorem B4277681 : Blo 1899435 4277681 := bstep (se 2 (by rfl) ⟨1604130, by rfl⟩ : syracuseStep 4277681 = 3208261) B3208261
theorem B2851787 : Blo 1899435 2851787 := bstep (se 1 (by rfl) ⟨2138840, by rfl⟩ : syracuseStep 2851787 = 4277681) B4277681
theorem B1901191 : Blo 1899435 1901191 := bstep (se 1 (by rfl) ⟨1425893, by rfl⟩ : syracuseStep 1901191 = 2851787) B2851787
theorem B2138845 : Blo 1899435 2138845 := bbase (se 3 (by rfl) ⟨401033, by rfl⟩ : syracuseStep 2138845 = 802067) (by norm_num)
theorem B2851793 : Blo 1899435 2851793 := bstep (se 2 (by rfl) ⟨1069422, by rfl⟩ : syracuseStep 2851793 = 2138845) B2138845
theorem B1901195 : Blo 1899435 1901195 := bstep (se 1 (by rfl) ⟨1425896, by rfl⟩ : syracuseStep 1901195 = 2851793) B2851793
theorem B6416549 : Blo 1899435 6416549 := bbase (se 4 (by rfl) ⟨601551, by rfl⟩ : syracuseStep 6416549 = 1203103) (by norm_num)
theorem B4277699 : Blo 1899435 4277699 := bstep (se 1 (by rfl) ⟨3208274, by rfl⟩ : syracuseStep 4277699 = 6416549) B6416549
theorem B2851799 : Blo 1899435 2851799 := bstep (se 1 (by rfl) ⟨2138849, by rfl⟩ : syracuseStep 2851799 = 4277699) B4277699
theorem B1901199 : Blo 1899435 1901199 := bstep (se 1 (by rfl) ⟨1425899, by rfl⟩ : syracuseStep 1901199 = 2851799) B2851799
theorem B2851805 : Blo 1899435 2851805 := bbase (se 3 (by rfl) ⟨534713, by rfl⟩ : syracuseStep 2851805 = 1069427) (by norm_num)
theorem B1901203 : Blo 1899435 1901203 := bstep (se 1 (by rfl) ⟨1425902, by rfl⟩ : syracuseStep 1901203 = 2851805) B2851805
theorem B4277717 : Blo 1899435 4277717 := bbase (se 7 (by rfl) ⟨50129, by rfl⟩ : syracuseStep 4277717 = 100259) (by norm_num)
theorem B2851811 : Blo 1899435 2851811 := bstep (se 1 (by rfl) ⟨2138858, by rfl⟩ : syracuseStep 2851811 = 4277717) B4277717
theorem B1901207 : Blo 1899435 1901207 := bstep (se 1 (by rfl) ⟨1425905, by rfl⟩ : syracuseStep 1901207 = 2851811) B2851811
theorem B1953445 : Blo 1899435 1953445 := bbase (se 4 (by rfl) ⟨183135, by rfl⟩ : syracuseStep 1953445 = 366271) (by norm_num)
theorem B2604593 : Blo 1899435 2604593 := bstep (se 2 (by rfl) ⟨976722, by rfl⟩ : syracuseStep 2604593 = 1953445) B1953445
theorem B6945581 : Blo 1899435 6945581 := bstep (se 3 (by rfl) ⟨1302296, by rfl⟩ : syracuseStep 6945581 = 2604593) B2604593
theorem B4630387 : Blo 1899435 4630387 := bstep (se 1 (by rfl) ⟨3472790, by rfl⟩ : syracuseStep 4630387 = 6945581) B6945581
theorem B6173849 : Blo 1899435 6173849 := bstep (se 2 (by rfl) ⟨2315193, by rfl⟩ : syracuseStep 6173849 = 4630387) B4630387
theorem B4115899 : Blo 1899435 4115899 := bstep (se 1 (by rfl) ⟨3086924, by rfl⟩ : syracuseStep 4115899 = 6173849) B6173849
theorem B21951461 : Blo 1899435 21951461 := bstep (se 4 (by rfl) ⟨2057949, by rfl⟩ : syracuseStep 21951461 = 4115899) B4115899
theorem B14634307 : Blo 1899435 14634307 := bstep (se 1 (by rfl) ⟨10975730, by rfl⟩ : syracuseStep 14634307 = 21951461) B21951461
theorem B19512409 : Blo 1899435 19512409 := bstep (se 2 (by rfl) ⟨7317153, by rfl⟩ : syracuseStep 19512409 = 14634307) B14634307
theorem B26016545 : Blo 1899435 26016545 := bstep (se 2 (by rfl) ⟨9756204, by rfl⟩ : syracuseStep 26016545 = 19512409) B19512409
theorem B17344363 : Blo 1899435 17344363 := bstep (se 1 (by rfl) ⟨13008272, by rfl⟩ : syracuseStep 17344363 = 26016545) B26016545
theorem B23125817 : Blo 1899435 23125817 := bstep (se 2 (by rfl) ⟨8672181, by rfl⟩ : syracuseStep 23125817 = 17344363) B17344363
theorem B15417211 : Blo 1899435 15417211 := bstep (se 1 (by rfl) ⟨11562908, by rfl⟩ : syracuseStep 15417211 = 23125817) B23125817
theorem B20556281 : Blo 1899435 20556281 := bstep (se 2 (by rfl) ⟨7708605, by rfl⟩ : syracuseStep 20556281 = 15417211) B15417211
theorem B13704187 : Blo 1899435 13704187 := bstep (se 1 (by rfl) ⟨10278140, by rfl⟩ : syracuseStep 13704187 = 20556281) B20556281
theorem B18272249 : Blo 1899435 18272249 := bstep (se 2 (by rfl) ⟨6852093, by rfl⟩ : syracuseStep 18272249 = 13704187) B13704187
theorem B12181499 : Blo 1899435 12181499 := bstep (se 1 (by rfl) ⟨9136124, by rfl⟩ : syracuseStep 12181499 = 18272249) B18272249
theorem B8120999 : Blo 1899435 8120999 := bstep (se 1 (by rfl) ⟨6090749, by rfl⟩ : syracuseStep 8120999 = 12181499) B12181499
theorem B5413999 : Blo 1899435 5413999 := bstep (se 1 (by rfl) ⟨4060499, by rfl⟩ : syracuseStep 5413999 = 8120999) B8120999
theorem B7218665 : Blo 1899435 7218665 := bstep (se 2 (by rfl) ⟨2706999, by rfl⟩ : syracuseStep 7218665 = 5413999) B5413999
theorem B4812443 : Blo 1899435 4812443 := bstep (se 1 (by rfl) ⟨3609332, by rfl⟩ : syracuseStep 4812443 = 7218665) B7218665
theorem B3208295 : Blo 1899435 3208295 := bstep (se 1 (by rfl) ⟨2406221, by rfl⟩ : syracuseStep 3208295 = 4812443) B4812443
theorem B2138863 : Blo 1899435 2138863 := bstep (se 1 (by rfl) ⟨1604147, by rfl⟩ : syracuseStep 2138863 = 3208295) B3208295
theorem B2851817 : Blo 1899435 2851817 := bstep (se 2 (by rfl) ⟨1069431, by rfl⟩ : syracuseStep 2851817 = 2138863) B2138863
theorem B1901211 : Blo 1899435 1901211 := bstep (se 1 (by rfl) ⟨1425908, by rfl⟩ : syracuseStep 1901211 = 2851817) B2851817
theorem B2890733 : Blo 1899435 2890733 := bbase (se 3 (by rfl) ⟨542012, by rfl⟩ : syracuseStep 2890733 = 1084025) (by norm_num)
theorem B7708621 : Blo 1899435 7708621 := bstep (se 3 (by rfl) ⟨1445366, by rfl⟩ : syracuseStep 7708621 = 2890733) B2890733
theorem B10278161 : Blo 1899435 10278161 := bstep (se 2 (by rfl) ⟨3854310, by rfl⟩ : syracuseStep 10278161 = 7708621) B7708621
theorem B6852107 : Blo 1899435 6852107 := bstep (se 1 (by rfl) ⟨5139080, by rfl⟩ : syracuseStep 6852107 = 10278161) B10278161
theorem B4568071 : Blo 1899435 4568071 := bstep (se 1 (by rfl) ⟨3426053, by rfl⟩ : syracuseStep 4568071 = 6852107) B6852107
theorem B6090761 : Blo 1899435 6090761 := bstep (se 2 (by rfl) ⟨2284035, by rfl⟩ : syracuseStep 6090761 = 4568071) B4568071
theorem B16242029 : Blo 1899435 16242029 := bstep (se 3 (by rfl) ⟨3045380, by rfl⟩ : syracuseStep 16242029 = 6090761) B6090761
theorem B10828019 : Blo 1899435 10828019 := bstep (se 1 (by rfl) ⟨8121014, by rfl⟩ : syracuseStep 10828019 = 16242029) B16242029
theorem B7218679 : Blo 1899435 7218679 := bstep (se 1 (by rfl) ⟨5414009, by rfl⟩ : syracuseStep 7218679 = 10828019) B10828019
theorem B9624905 : Blo 1899435 9624905 := bstep (se 2 (by rfl) ⟨3609339, by rfl⟩ : syracuseStep 9624905 = 7218679) B7218679
theorem B6416603 : Blo 1899435 6416603 := bstep (se 1 (by rfl) ⟨4812452, by rfl⟩ : syracuseStep 6416603 = 9624905) B9624905
theorem B4277735 : Blo 1899435 4277735 := bstep (se 1 (by rfl) ⟨3208301, by rfl⟩ : syracuseStep 4277735 = 6416603) B6416603
theorem B2851823 : Blo 1899435 2851823 := bstep (se 1 (by rfl) ⟨2138867, by rfl⟩ : syracuseStep 2851823 = 4277735) B4277735
theorem B1901215 : Blo 1899435 1901215 := bstep (se 1 (by rfl) ⟨1425911, by rfl⟩ : syracuseStep 1901215 = 2851823) B2851823
theorem B2851829 : Blo 1899435 2851829 := bbase (se 5 (by rfl) ⟨133679, by rfl⟩ : syracuseStep 2851829 = 267359) (by norm_num)
theorem B1901219 : Blo 1899435 1901219 := bstep (se 1 (by rfl) ⟨1425914, by rfl⟩ : syracuseStep 1901219 = 2851829) B2851829
theorem B4060525 : Blo 1899435 4060525 := bbase (se 3 (by rfl) ⟨761348, by rfl⟩ : syracuseStep 4060525 = 1522697) (by norm_num)
theorem B5414033 : Blo 1899435 5414033 := bstep (se 2 (by rfl) ⟨2030262, by rfl⟩ : syracuseStep 5414033 = 4060525) B4060525
theorem B3609355 : Blo 1899435 3609355 := bstep (se 1 (by rfl) ⟨2707016, by rfl⟩ : syracuseStep 3609355 = 5414033) B5414033
theorem B4812473 : Blo 1899435 4812473 := bstep (se 2 (by rfl) ⟨1804677, by rfl⟩ : syracuseStep 4812473 = 3609355) B3609355
theorem B3208315 : Blo 1899435 3208315 := bstep (se 1 (by rfl) ⟨2406236, by rfl⟩ : syracuseStep 3208315 = 4812473) B4812473
theorem B4277753 : Blo 1899435 4277753 := bstep (se 2 (by rfl) ⟨1604157, by rfl⟩ : syracuseStep 4277753 = 3208315) B3208315
theorem B2851835 : Blo 1899435 2851835 := bstep (se 1 (by rfl) ⟨2138876, by rfl⟩ : syracuseStep 2851835 = 4277753) B4277753
theorem B1901223 : Blo 1899435 1901223 := bstep (se 1 (by rfl) ⟨1425917, by rfl⟩ : syracuseStep 1901223 = 2851835) B2851835
theorem B2138881 : Blo 1899435 2138881 := bbase (se 2 (by rfl) ⟨802080, by rfl⟩ : syracuseStep 2138881 = 1604161) (by norm_num)
theorem B2851841 : Blo 1899435 2851841 := bstep (se 2 (by rfl) ⟨1069440, by rfl⟩ : syracuseStep 2851841 = 2138881) B2138881
theorem B1901227 : Blo 1899435 1901227 := bstep (se 1 (by rfl) ⟨1425920, by rfl⟩ : syracuseStep 1901227 = 2851841) B2851841
theorem B4812493 : Blo 1899435 4812493 := bbase (se 3 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 4812493 = 1804685) (by norm_num)
theorem B6416657 : Blo 1899435 6416657 := bstep (se 2 (by rfl) ⟨2406246, by rfl⟩ : syracuseStep 6416657 = 4812493) B4812493
theorem B4277771 : Blo 1899435 4277771 := bstep (se 1 (by rfl) ⟨3208328, by rfl⟩ : syracuseStep 4277771 = 6416657) B6416657
theorem B2851847 : Blo 1899435 2851847 := bstep (se 1 (by rfl) ⟨2138885, by rfl⟩ : syracuseStep 2851847 = 4277771) B4277771
theorem B1901231 : Blo 1899435 1901231 := bstep (se 1 (by rfl) ⟨1425923, by rfl⟩ : syracuseStep 1901231 = 2851847) B2851847
theorem B2851853 : Blo 1899435 2851853 := bbase (se 3 (by rfl) ⟨534722, by rfl⟩ : syracuseStep 2851853 = 1069445) (by norm_num)
theorem B1901235 : Blo 1899435 1901235 := bstep (se 1 (by rfl) ⟨1425926, by rfl⟩ : syracuseStep 1901235 = 2851853) B2851853
theorem B4277789 : Blo 1899435 4277789 := bbase (se 3 (by rfl) ⟨802085, by rfl⟩ : syracuseStep 4277789 = 1604171) (by norm_num)
theorem B2851859 : Blo 1899435 2851859 := bstep (se 1 (by rfl) ⟨2138894, by rfl⟩ : syracuseStep 2851859 = 4277789) B4277789
theorem B1901239 : Blo 1899435 1901239 := bstep (se 1 (by rfl) ⟨1425929, by rfl⟩ : syracuseStep 1901239 = 2851859) B2851859
theorem B3208349 : Blo 1899435 3208349 := bbase (se 3 (by rfl) ⟨601565, by rfl⟩ : syracuseStep 3208349 = 1203131) (by norm_num)
theorem B2138899 : Blo 1899435 2138899 := bstep (se 1 (by rfl) ⟨1604174, by rfl⟩ : syracuseStep 2138899 = 3208349) B3208349
theorem B2851865 : Blo 1899435 2851865 := bstep (se 2 (by rfl) ⟨1069449, by rfl⟩ : syracuseStep 2851865 = 2138899) B2138899
theorem B1901243 : Blo 1899435 1901243 := bstep (se 1 (by rfl) ⟨1425932, by rfl⟩ : syracuseStep 1901243 = 2851865) B2851865
theorem B2781421 : Blo 1899435 2781421 := bbase (se 3 (by rfl) ⟨521516, by rfl⟩ : syracuseStep 2781421 = 1043033) (by norm_num)
theorem B59336981 : Blo 1899435 59336981 := bstep (se 6 (by rfl) ⟨1390710, by rfl⟩ : syracuseStep 59336981 = 2781421) B2781421
theorem B39557987 : Blo 1899435 39557987 := bstep (se 1 (by rfl) ⟨29668490, by rfl⟩ : syracuseStep 39557987 = 59336981) B59336981
theorem B26371991 : Blo 1899435 26371991 := bstep (se 1 (by rfl) ⟨19778993, by rfl⟩ : syracuseStep 26371991 = 39557987) B39557987
theorem B70325309 : Blo 1899435 70325309 := bstep (se 3 (by rfl) ⟨13185995, by rfl⟩ : syracuseStep 70325309 = 26371991) B26371991
theorem B46883539 : Blo 1899435 46883539 := bstep (se 1 (by rfl) ⟨35162654, by rfl⟩ : syracuseStep 46883539 = 70325309) B70325309
theorem B62511385 : Blo 1899435 62511385 := bstep (se 2 (by rfl) ⟨23441769, by rfl⟩ : syracuseStep 62511385 = 46883539) B46883539
theorem B83348513 : Blo 1899435 83348513 := bstep (se 2 (by rfl) ⟨31255692, by rfl⟩ : syracuseStep 83348513 = 62511385) B62511385
theorem B55565675 : Blo 1899435 55565675 := bstep (se 1 (by rfl) ⟨41674256, by rfl⟩ : syracuseStep 55565675 = 83348513) B83348513
theorem B37043783 : Blo 1899435 37043783 := bstep (se 1 (by rfl) ⟨27782837, by rfl⟩ : syracuseStep 37043783 = 55565675) B55565675
theorem B24695855 : Blo 1899435 24695855 := bstep (se 1 (by rfl) ⟨18521891, by rfl⟩ : syracuseStep 24695855 = 37043783) B37043783
theorem B16463903 : Blo 1899435 16463903 := bstep (se 1 (by rfl) ⟨12347927, by rfl⟩ : syracuseStep 16463903 = 24695855) B24695855
theorem B43903741 : Blo 1899435 43903741 := bstep (se 3 (by rfl) ⟨8231951, by rfl⟩ : syracuseStep 43903741 = 16463903) B16463903
theorem B58538321 : Blo 1899435 58538321 := bstep (se 2 (by rfl) ⟨21951870, by rfl⟩ : syracuseStep 58538321 = 43903741) B43903741
theorem B39025547 : Blo 1899435 39025547 := bstep (se 1 (by rfl) ⟨29269160, by rfl⟩ : syracuseStep 39025547 = 58538321) B58538321
theorem B26017031 : Blo 1899435 26017031 := bstep (se 1 (by rfl) ⟨19512773, by rfl⟩ : syracuseStep 26017031 = 39025547) B39025547
theorem B17344687 : Blo 1899435 17344687 := bstep (se 1 (by rfl) ⟨13008515, by rfl⟩ : syracuseStep 17344687 = 26017031) B26017031
theorem B23126249 : Blo 1899435 23126249 := bstep (se 2 (by rfl) ⟨8672343, by rfl⟩ : syracuseStep 23126249 = 17344687) B17344687
theorem B61669997 : Blo 1899435 61669997 := bstep (se 3 (by rfl) ⟨11563124, by rfl⟩ : syracuseStep 61669997 = 23126249) B23126249
theorem B41113331 : Blo 1899435 41113331 := bstep (se 1 (by rfl) ⟨30834998, by rfl⟩ : syracuseStep 41113331 = 61669997) B61669997
theorem B27408887 : Blo 1899435 27408887 := bstep (se 1 (by rfl) ⟨20556665, by rfl⟩ : syracuseStep 27408887 = 41113331) B41113331
theorem B18272591 : Blo 1899435 18272591 := bstep (se 1 (by rfl) ⟨13704443, by rfl⟩ : syracuseStep 18272591 = 27408887) B27408887
theorem B12181727 : Blo 1899435 12181727 := bstep (se 1 (by rfl) ⟨9136295, by rfl⟩ : syracuseStep 12181727 = 18272591) B18272591
theorem B8121151 : Blo 1899435 8121151 := bstep (se 1 (by rfl) ⟨6090863, by rfl⟩ : syracuseStep 8121151 = 12181727) B12181727
theorem B10828201 : Blo 1899435 10828201 := bstep (se 2 (by rfl) ⟨4060575, by rfl⟩ : syracuseStep 10828201 = 8121151) B8121151
theorem B14437601 : Blo 1899435 14437601 := bstep (se 2 (by rfl) ⟨5414100, by rfl⟩ : syracuseStep 14437601 = 10828201) B10828201
theorem B9625067 : Blo 1899435 9625067 := bstep (se 1 (by rfl) ⟨7218800, by rfl⟩ : syracuseStep 9625067 = 14437601) B14437601
theorem B6416711 : Blo 1899435 6416711 := bstep (se 1 (by rfl) ⟨4812533, by rfl⟩ : syracuseStep 6416711 = 9625067) B9625067
theorem B4277807 : Blo 1899435 4277807 := bstep (se 1 (by rfl) ⟨3208355, by rfl⟩ : syracuseStep 4277807 = 6416711) B6416711
theorem B2851871 : Blo 1899435 2851871 := bstep (se 1 (by rfl) ⟨2138903, by rfl⟩ : syracuseStep 2851871 = 4277807) B4277807
theorem B1901247 : Blo 1899435 1901247 := bstep (se 1 (by rfl) ⟨1425935, by rfl⟩ : syracuseStep 1901247 = 2851871) B2851871
theorem B2851877 : Blo 1899435 2851877 := bbase (se 4 (by rfl) ⟨267363, by rfl⟩ : syracuseStep 2851877 = 534727) (by norm_num)
theorem B1901251 : Blo 1899435 1901251 := bstep (se 1 (by rfl) ⟨1425938, by rfl⟩ : syracuseStep 1901251 = 2851877) B2851877
theorem B2406277 : Blo 1899435 2406277 := bbase (se 4 (by rfl) ⟨225588, by rfl⟩ : syracuseStep 2406277 = 451177) (by norm_num)
theorem B3208369 : Blo 1899435 3208369 := bstep (se 2 (by rfl) ⟨1203138, by rfl⟩ : syracuseStep 3208369 = 2406277) B2406277
theorem B4277825 : Blo 1899435 4277825 := bstep (se 2 (by rfl) ⟨1604184, by rfl⟩ : syracuseStep 4277825 = 3208369) B3208369
theorem B2851883 : Blo 1899435 2851883 := bstep (se 1 (by rfl) ⟨2138912, by rfl⟩ : syracuseStep 2851883 = 4277825) B4277825
theorem B1901255 : Blo 1899435 1901255 := bstep (se 1 (by rfl) ⟨1425941, by rfl⟩ : syracuseStep 1901255 = 2851883) B2851883
theorem B2138917 : Blo 1899435 2138917 := bbase (se 4 (by rfl) ⟨200523, by rfl⟩ : syracuseStep 2138917 = 401047) (by norm_num)
theorem B2851889 : Blo 1899435 2851889 := bstep (se 2 (by rfl) ⟨1069458, by rfl⟩ : syracuseStep 2851889 = 2138917) B2138917
theorem B1901259 : Blo 1899435 1901259 := bstep (se 1 (by rfl) ⟨1425944, by rfl⟩ : syracuseStep 1901259 = 2851889) B2851889
theorem B8121221 : Blo 1899435 8121221 := bbase (se 4 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 8121221 = 1522729) (by norm_num)
theorem B5414147 : Blo 1899435 5414147 := bstep (se 1 (by rfl) ⟨4060610, by rfl⟩ : syracuseStep 5414147 = 8121221) B8121221
theorem B3609431 : Blo 1899435 3609431 := bstep (se 1 (by rfl) ⟨2707073, by rfl⟩ : syracuseStep 3609431 = 5414147) B5414147
theorem B2406287 : Blo 1899435 2406287 := bstep (se 1 (by rfl) ⟨1804715, by rfl⟩ : syracuseStep 2406287 = 3609431) B3609431
theorem B6416765 : Blo 1899435 6416765 := bstep (se 3 (by rfl) ⟨1203143, by rfl⟩ : syracuseStep 6416765 = 2406287) B2406287
theorem B4277843 : Blo 1899435 4277843 := bstep (se 1 (by rfl) ⟨3208382, by rfl⟩ : syracuseStep 4277843 = 6416765) B6416765
theorem B2851895 : Blo 1899435 2851895 := bstep (se 1 (by rfl) ⟨2138921, by rfl⟩ : syracuseStep 2851895 = 4277843) B4277843
theorem B1901263 : Blo 1899435 1901263 := bstep (se 1 (by rfl) ⟨1425947, by rfl⟩ : syracuseStep 1901263 = 2851895) B2851895
theorem B2851901 : Blo 1899435 2851901 := bbase (se 3 (by rfl) ⟨534731, by rfl⟩ : syracuseStep 2851901 = 1069463) (by norm_num)
theorem B1901267 : Blo 1899435 1901267 := bstep (se 1 (by rfl) ⟨1425950, by rfl⟩ : syracuseStep 1901267 = 2851901) B2851901
theorem B4277861 : Blo 1899435 4277861 := bbase (se 4 (by rfl) ⟨401049, by rfl⟩ : syracuseStep 4277861 = 802099) (by norm_num)
theorem B2851907 : Blo 1899435 2851907 := bstep (se 1 (by rfl) ⟨2138930, by rfl⟩ : syracuseStep 2851907 = 4277861) B4277861
theorem B1901271 : Blo 1899435 1901271 := bstep (se 1 (by rfl) ⟨1425953, by rfl⟩ : syracuseStep 1901271 = 2851907) B2851907
theorem B4812605 : Blo 1899435 4812605 := bbase (se 3 (by rfl) ⟨902363, by rfl⟩ : syracuseStep 4812605 = 1804727) (by norm_num)
theorem B3208403 : Blo 1899435 3208403 := bstep (se 1 (by rfl) ⟨2406302, by rfl⟩ : syracuseStep 3208403 = 4812605) B4812605
theorem B2138935 : Blo 1899435 2138935 := bstep (se 1 (by rfl) ⟨1604201, by rfl⟩ : syracuseStep 2138935 = 3208403) B3208403
theorem B2851913 : Blo 1899435 2851913 := bstep (se 2 (by rfl) ⟨1069467, by rfl⟩ : syracuseStep 2851913 = 2138935) B2138935
theorem B1901275 : Blo 1899435 1901275 := bstep (se 1 (by rfl) ⟨1425956, by rfl⟩ : syracuseStep 1901275 = 2851913) B2851913
theorem B3609461 : Blo 1899435 3609461 := bbase (se 5 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 3609461 = 338387) (by norm_num)
theorem B9625229 : Blo 1899435 9625229 := bstep (se 3 (by rfl) ⟨1804730, by rfl⟩ : syracuseStep 9625229 = 3609461) B3609461
theorem B6416819 : Blo 1899435 6416819 := bstep (se 1 (by rfl) ⟨4812614, by rfl⟩ : syracuseStep 6416819 = 9625229) B9625229
theorem B4277879 : Blo 1899435 4277879 := bstep (se 1 (by rfl) ⟨3208409, by rfl⟩ : syracuseStep 4277879 = 6416819) B6416819
theorem B2851919 : Blo 1899435 2851919 := bstep (se 1 (by rfl) ⟨2138939, by rfl⟩ : syracuseStep 2851919 = 4277879) B4277879
theorem B1901279 : Blo 1899435 1901279 := bstep (se 1 (by rfl) ⟨1425959, by rfl⟩ : syracuseStep 1901279 = 2851919) B2851919
theorem B2851925 : Blo 1899435 2851925 := bbase (se 8 (by rfl) ⟨16710, by rfl⟩ : syracuseStep 2851925 = 33421) (by norm_num)
theorem B1901283 : Blo 1899435 1901283 := bstep (se 1 (by rfl) ⟨1425962, by rfl⟩ : syracuseStep 1901283 = 2851925) B2851925
theorem B23126741 : Blo 1899435 23126741 := bbase (se 7 (by rfl) ⟨271016, by rfl⟩ : syracuseStep 23126741 = 542033) (by norm_num)
theorem B15417827 : Blo 1899435 15417827 := bstep (se 1 (by rfl) ⟨11563370, by rfl⟩ : syracuseStep 15417827 = 23126741) B23126741
theorem B10278551 : Blo 1899435 10278551 := bstep (se 1 (by rfl) ⟨7708913, by rfl⟩ : syracuseStep 10278551 = 15417827) B15417827
theorem B6852367 : Blo 1899435 6852367 := bstep (se 1 (by rfl) ⟨5139275, by rfl⟩ : syracuseStep 6852367 = 10278551) B10278551
theorem B9136489 : Blo 1899435 9136489 := bstep (se 2 (by rfl) ⟨3426183, by rfl⟩ : syracuseStep 9136489 = 6852367) B6852367
theorem B12181985 : Blo 1899435 12181985 := bstep (se 2 (by rfl) ⟨4568244, by rfl⟩ : syracuseStep 12181985 = 9136489) B9136489
theorem B8121323 : Blo 1899435 8121323 := bstep (se 1 (by rfl) ⟨6090992, by rfl⟩ : syracuseStep 8121323 = 12181985) B12181985
theorem B5414215 : Blo 1899435 5414215 := bstep (se 1 (by rfl) ⟨4060661, by rfl⟩ : syracuseStep 5414215 = 8121323) B8121323
theorem B7218953 : Blo 1899435 7218953 := bstep (se 2 (by rfl) ⟨2707107, by rfl⟩ : syracuseStep 7218953 = 5414215) B5414215
theorem B4812635 : Blo 1899435 4812635 := bstep (se 1 (by rfl) ⟨3609476, by rfl⟩ : syracuseStep 4812635 = 7218953) B7218953
theorem B3208423 : Blo 1899435 3208423 := bstep (se 1 (by rfl) ⟨2406317, by rfl⟩ : syracuseStep 3208423 = 4812635) B4812635
theorem B4277897 : Blo 1899435 4277897 := bstep (se 2 (by rfl) ⟨1604211, by rfl⟩ : syracuseStep 4277897 = 3208423) B3208423
theorem B2851931 : Blo 1899435 2851931 := bstep (se 1 (by rfl) ⟨2138948, by rfl⟩ : syracuseStep 2851931 = 4277897) B4277897
theorem B1901287 : Blo 1899435 1901287 := bstep (se 1 (by rfl) ⟨1425965, by rfl⟩ : syracuseStep 1901287 = 2851931) B2851931
theorem B2138953 : Blo 1899435 2138953 := bbase (se 2 (by rfl) ⟨802107, by rfl⟩ : syracuseStep 2138953 = 1604215) (by norm_num)
theorem B2851937 : Blo 1899435 2851937 := bstep (se 2 (by rfl) ⟨1069476, by rfl⟩ : syracuseStep 2851937 = 2138953) B2138953
theorem B1901291 : Blo 1899435 1901291 := bstep (se 1 (by rfl) ⟨1425968, by rfl⟩ : syracuseStep 1901291 = 2851937) B2851937
theorem B2168141 : Blo 1899435 2168141 := bbase (se 3 (by rfl) ⟨406526, by rfl⟩ : syracuseStep 2168141 = 813053) (by norm_num)
theorem B5781709 : Blo 1899435 5781709 := bstep (se 3 (by rfl) ⟨1084070, by rfl⟩ : syracuseStep 5781709 = 2168141) B2168141
theorem B7708945 : Blo 1899435 7708945 := bstep (se 2 (by rfl) ⟨2890854, by rfl⟩ : syracuseStep 7708945 = 5781709) B5781709
theorem B10278593 : Blo 1899435 10278593 := bstep (se 2 (by rfl) ⟨3854472, by rfl⟩ : syracuseStep 10278593 = 7708945) B7708945
theorem B6852395 : Blo 1899435 6852395 := bstep (se 1 (by rfl) ⟨5139296, by rfl⟩ : syracuseStep 6852395 = 10278593) B10278593
theorem B18273053 : Blo 1899435 18273053 := bstep (se 3 (by rfl) ⟨3426197, by rfl⟩ : syracuseStep 18273053 = 6852395) B6852395
theorem B12182035 : Blo 1899435 12182035 := bstep (se 1 (by rfl) ⟨9136526, by rfl⟩ : syracuseStep 12182035 = 18273053) B18273053
theorem B16242713 : Blo 1899435 16242713 := bstep (se 2 (by rfl) ⟨6091017, by rfl⟩ : syracuseStep 16242713 = 12182035) B12182035
theorem B10828475 : Blo 1899435 10828475 := bstep (se 1 (by rfl) ⟨8121356, by rfl⟩ : syracuseStep 10828475 = 16242713) B16242713
theorem B7218983 : Blo 1899435 7218983 := bstep (se 1 (by rfl) ⟨5414237, by rfl⟩ : syracuseStep 7218983 = 10828475) B10828475
theorem B4812655 : Blo 1899435 4812655 := bstep (se 1 (by rfl) ⟨3609491, by rfl⟩ : syracuseStep 4812655 = 7218983) B7218983
theorem B6416873 : Blo 1899435 6416873 := bstep (se 2 (by rfl) ⟨2406327, by rfl⟩ : syracuseStep 6416873 = 4812655) B4812655
theorem B4277915 : Blo 1899435 4277915 := bstep (se 1 (by rfl) ⟨3208436, by rfl⟩ : syracuseStep 4277915 = 6416873) B6416873
theorem B2851943 : Blo 1899435 2851943 := bstep (se 1 (by rfl) ⟨2138957, by rfl⟩ : syracuseStep 2851943 = 4277915) B4277915
theorem B1901295 : Blo 1899435 1901295 := bstep (se 1 (by rfl) ⟨1425971, by rfl⟩ : syracuseStep 1901295 = 2851943) B2851943
theorem B2851949 : Blo 1899435 2851949 := bbase (se 3 (by rfl) ⟨534740, by rfl⟩ : syracuseStep 2851949 = 1069481) (by norm_num)
theorem B1901299 : Blo 1899435 1901299 := bstep (se 1 (by rfl) ⟨1425974, by rfl⟩ : syracuseStep 1901299 = 2851949) B2851949
theorem B4277933 : Blo 1899435 4277933 := bbase (se 3 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 4277933 = 1604225) (by norm_num)
theorem B2851955 : Blo 1899435 2851955 := bstep (se 1 (by rfl) ⟨2138966, by rfl⟩ : syracuseStep 2851955 = 4277933) B4277933
theorem B1901303 : Blo 1899435 1901303 := bstep (se 1 (by rfl) ⟨1425977, by rfl⟩ : syracuseStep 1901303 = 2851955) B2851955
theorem B3426221 : Blo 1899435 3426221 := bbase (se 3 (by rfl) ⟨642416, by rfl⟩ : syracuseStep 3426221 = 1284833) (by norm_num)
theorem B2284147 : Blo 1899435 2284147 := bstep (se 1 (by rfl) ⟨1713110, by rfl⟩ : syracuseStep 2284147 = 3426221) B3426221
theorem B3045529 : Blo 1899435 3045529 := bstep (se 2 (by rfl) ⟨1142073, by rfl⟩ : syracuseStep 3045529 = 2284147) B2284147
theorem B4060705 : Blo 1899435 4060705 := bstep (se 2 (by rfl) ⟨1522764, by rfl⟩ : syracuseStep 4060705 = 3045529) B3045529
theorem B5414273 : Blo 1899435 5414273 := bstep (se 2 (by rfl) ⟨2030352, by rfl⟩ : syracuseStep 5414273 = 4060705) B4060705
theorem B3609515 : Blo 1899435 3609515 := bstep (se 1 (by rfl) ⟨2707136, by rfl⟩ : syracuseStep 3609515 = 5414273) B5414273
theorem B2406343 : Blo 1899435 2406343 := bstep (se 1 (by rfl) ⟨1804757, by rfl⟩ : syracuseStep 2406343 = 3609515) B3609515
theorem B3208457 : Blo 1899435 3208457 := bstep (se 2 (by rfl) ⟨1203171, by rfl⟩ : syracuseStep 3208457 = 2406343) B2406343
theorem B2138971 : Blo 1899435 2138971 := bstep (se 1 (by rfl) ⟨1604228, by rfl⟩ : syracuseStep 2138971 = 3208457) B3208457
theorem B2851961 : Blo 1899435 2851961 := bstep (se 2 (by rfl) ⟨1069485, by rfl⟩ : syracuseStep 2851961 = 2138971) B2138971
theorem B1901307 : Blo 1899435 1901307 := bstep (se 1 (by rfl) ⟨1425980, by rfl⟩ : syracuseStep 1901307 = 2851961) B2851961
theorem B18273205 : Blo 1899435 18273205 := bbase (se 5 (by rfl) ⟨856556, by rfl⟩ : syracuseStep 18273205 = 1713113) (by norm_num)
theorem B24364273 : Blo 1899435 24364273 := bstep (se 2 (by rfl) ⟨9136602, by rfl⟩ : syracuseStep 24364273 = 18273205) B18273205
theorem B32485697 : Blo 1899435 32485697 := bstep (se 2 (by rfl) ⟨12182136, by rfl⟩ : syracuseStep 32485697 = 24364273) B24364273
theorem B21657131 : Blo 1899435 21657131 := bstep (se 1 (by rfl) ⟨16242848, by rfl⟩ : syracuseStep 21657131 = 32485697) B32485697
theorem B14438087 : Blo 1899435 14438087 := bstep (se 1 (by rfl) ⟨10828565, by rfl⟩ : syracuseStep 14438087 = 21657131) B21657131
theorem B9625391 : Blo 1899435 9625391 := bstep (se 1 (by rfl) ⟨7219043, by rfl⟩ : syracuseStep 9625391 = 14438087) B14438087
theorem B6416927 : Blo 1899435 6416927 := bstep (se 1 (by rfl) ⟨4812695, by rfl⟩ : syracuseStep 6416927 = 9625391) B9625391
theorem B4277951 : Blo 1899435 4277951 := bstep (se 1 (by rfl) ⟨3208463, by rfl⟩ : syracuseStep 4277951 = 6416927) B6416927
theorem B2851967 : Blo 1899435 2851967 := bstep (se 1 (by rfl) ⟨2138975, by rfl⟩ : syracuseStep 2851967 = 4277951) B4277951
theorem B1901311 : Blo 1899435 1901311 := bstep (se 1 (by rfl) ⟨1425983, by rfl⟩ : syracuseStep 1901311 = 2851967) B2851967
theorem B2851973 : Blo 1899435 2851973 := bbase (se 4 (by rfl) ⟨267372, by rfl⟩ : syracuseStep 2851973 = 534745) (by norm_num)
theorem B1901315 : Blo 1899435 1901315 := bstep (se 1 (by rfl) ⟨1425986, by rfl⟩ : syracuseStep 1901315 = 2851973) B2851973
theorem B3208477 : Blo 1899435 3208477 := bbase (se 3 (by rfl) ⟨601589, by rfl⟩ : syracuseStep 3208477 = 1203179) (by norm_num)
theorem B4277969 : Blo 1899435 4277969 := bstep (se 2 (by rfl) ⟨1604238, by rfl⟩ : syracuseStep 4277969 = 3208477) B3208477
theorem B2851979 : Blo 1899435 2851979 := bstep (se 1 (by rfl) ⟨2138984, by rfl⟩ : syracuseStep 2851979 = 4277969) B4277969
theorem B1901319 : Blo 1899435 1901319 := bstep (se 1 (by rfl) ⟨1425989, by rfl⟩ : syracuseStep 1901319 = 2851979) B2851979
theorem B2138989 : Blo 1899435 2138989 := bbase (se 3 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 2138989 = 802121) (by norm_num)
theorem B2851985 : Blo 1899435 2851985 := bstep (se 2 (by rfl) ⟨1069494, by rfl⟩ : syracuseStep 2851985 = 2138989) B2138989
theorem B1901323 : Blo 1899435 1901323 := bstep (se 1 (by rfl) ⟨1425992, by rfl⟩ : syracuseStep 1901323 = 2851985) B2851985
theorem B6416981 : Blo 1899435 6416981 := bbase (se 8 (by rfl) ⟨37599, by rfl⟩ : syracuseStep 6416981 = 75199) (by norm_num)
theorem B4277987 : Blo 1899435 4277987 := bstep (se 1 (by rfl) ⟨3208490, by rfl⟩ : syracuseStep 4277987 = 6416981) B6416981
theorem B2851991 : Blo 1899435 2851991 := bstep (se 1 (by rfl) ⟨2138993, by rfl⟩ : syracuseStep 2851991 = 4277987) B4277987
theorem B1901327 : Blo 1899435 1901327 := bstep (se 1 (by rfl) ⟨1425995, by rfl⟩ : syracuseStep 1901327 = 2851991) B2851991
theorem B2851997 : Blo 1899435 2851997 := bbase (se 3 (by rfl) ⟨534749, by rfl⟩ : syracuseStep 2851997 = 1069499) (by norm_num)
theorem B1901331 : Blo 1899435 1901331 := bstep (se 1 (by rfl) ⟨1425998, by rfl⟩ : syracuseStep 1901331 = 2851997) B2851997
theorem B4278005 : Blo 1899435 4278005 := bbase (se 5 (by rfl) ⟨200531, by rfl⟩ : syracuseStep 4278005 = 401063) (by norm_num)
theorem B2852003 : Blo 1899435 2852003 := bstep (se 1 (by rfl) ⟨2139002, by rfl⟩ : syracuseStep 2852003 = 4278005) B4278005
theorem B1901335 : Blo 1899435 1901335 := bstep (se 1 (by rfl) ⟨1426001, by rfl⟩ : syracuseStep 1901335 = 2852003) B2852003
theorem B13705109 : Blo 1899435 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B9136739 : Blo 1899435 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B24364637 : Blo 1899435 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B16243091 : Blo 1899435 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B10828727 : Blo 1899435 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B7219151 : Blo 1899435 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B4812767 : Blo 1899435 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B3208511 : Blo 1899435 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B2139007 : Blo 1899435 2139007 := bstep (se 1 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 2139007 = 3208511) B3208511
theorem B2852009 : Blo 1899435 2852009 := bstep (se 2 (by rfl) ⟨1069503, by rfl⟩ : syracuseStep 2852009 = 2139007) B2139007
theorem B1901339 : Blo 1899435 1901339 := bstep (se 1 (by rfl) ⟨1426004, by rfl⟩ : syracuseStep 1901339 = 2852009) B2852009
theorem B4060781 : Blo 1899435 4060781 := bbase (se 3 (by rfl) ⟨761396, by rfl⟩ : syracuseStep 4060781 = 1522793) (by norm_num)
theorem B2707187 : Blo 1899435 2707187 := bstep (se 1 (by rfl) ⟨2030390, by rfl⟩ : syracuseStep 2707187 = 4060781) B4060781
theorem B7219165 : Blo 1899435 7219165 := bstep (se 3 (by rfl) ⟨1353593, by rfl⟩ : syracuseStep 7219165 = 2707187) B2707187
theorem B9625553 : Blo 1899435 9625553 := bstep (se 2 (by rfl) ⟨3609582, by rfl⟩ : syracuseStep 9625553 = 7219165) B7219165
theorem B6417035 : Blo 1899435 6417035 := bstep (se 1 (by rfl) ⟨4812776, by rfl⟩ : syracuseStep 6417035 = 9625553) B9625553
theorem B4278023 : Blo 1899435 4278023 := bstep (se 1 (by rfl) ⟨3208517, by rfl⟩ : syracuseStep 4278023 = 6417035) B6417035
theorem B2852015 : Blo 1899435 2852015 := bstep (se 1 (by rfl) ⟨2139011, by rfl⟩ : syracuseStep 2852015 = 4278023) B4278023
theorem B1901343 : Blo 1899435 1901343 := bstep (se 1 (by rfl) ⟨1426007, by rfl⟩ : syracuseStep 1901343 = 2852015) B2852015
theorem B2852021 : Blo 1899435 2852021 := bbase (se 5 (by rfl) ⟨133688, by rfl⟩ : syracuseStep 2852021 = 267377) (by norm_num)
theorem B1901347 : Blo 1899435 1901347 := bstep (se 1 (by rfl) ⟨1426010, by rfl⟩ : syracuseStep 1901347 = 2852021) B2852021
theorem B4812797 : Blo 1899435 4812797 := bbase (se 3 (by rfl) ⟨902399, by rfl⟩ : syracuseStep 4812797 = 1804799) (by norm_num)
theorem B3208531 : Blo 1899435 3208531 := bstep (se 1 (by rfl) ⟨2406398, by rfl⟩ : syracuseStep 3208531 = 4812797) B4812797
theorem B4278041 : Blo 1899435 4278041 := bstep (se 2 (by rfl) ⟨1604265, by rfl⟩ : syracuseStep 4278041 = 3208531) B3208531
theorem B2852027 : Blo 1899435 2852027 := bstep (se 1 (by rfl) ⟨2139020, by rfl⟩ : syracuseStep 2852027 = 4278041) B4278041
theorem B1901351 : Blo 1899435 1901351 := bstep (se 1 (by rfl) ⟨1426013, by rfl⟩ : syracuseStep 1901351 = 2852027) B2852027
theorem B2139025 : Blo 1899435 2139025 := bbase (se 2 (by rfl) ⟨802134, by rfl⟩ : syracuseStep 2139025 = 1604269) (by norm_num)
theorem B2852033 : Blo 1899435 2852033 := bstep (se 2 (by rfl) ⟨1069512, by rfl⟩ : syracuseStep 2852033 = 2139025) B2139025
theorem B1901355 : Blo 1899435 1901355 := bstep (se 1 (by rfl) ⟨1426016, by rfl⟩ : syracuseStep 1901355 = 2852033) B2852033
theorem B3609613 : Blo 1899435 3609613 := bbase (se 3 (by rfl) ⟨676802, by rfl⟩ : syracuseStep 3609613 = 1353605) (by norm_num)
theorem B4812817 : Blo 1899435 4812817 := bstep (se 2 (by rfl) ⟨1804806, by rfl⟩ : syracuseStep 4812817 = 3609613) B3609613
theorem B6417089 : Blo 1899435 6417089 := bstep (se 2 (by rfl) ⟨2406408, by rfl⟩ : syracuseStep 6417089 = 4812817) B4812817
theorem B4278059 : Blo 1899435 4278059 := bstep (se 1 (by rfl) ⟨3208544, by rfl⟩ : syracuseStep 4278059 = 6417089) B6417089
theorem B2852039 : Blo 1899435 2852039 := bstep (se 1 (by rfl) ⟨2139029, by rfl⟩ : syracuseStep 2852039 = 4278059) B4278059
theorem B1901359 : Blo 1899435 1901359 := bstep (se 1 (by rfl) ⟨1426019, by rfl⟩ : syracuseStep 1901359 = 2852039) B2852039
theorem B2852045 : Blo 1899435 2852045 := bbase (se 3 (by rfl) ⟨534758, by rfl⟩ : syracuseStep 2852045 = 1069517) (by norm_num)
theorem B1901363 : Blo 1899435 1901363 := bstep (se 1 (by rfl) ⟨1426022, by rfl⟩ : syracuseStep 1901363 = 2852045) B2852045
theorem B4278077 : Blo 1899435 4278077 := bbase (se 3 (by rfl) ⟨802139, by rfl⟩ : syracuseStep 4278077 = 1604279) (by norm_num)
theorem B2852051 : Blo 1899435 2852051 := bstep (se 1 (by rfl) ⟨2139038, by rfl⟩ : syracuseStep 2852051 = 4278077) B4278077
theorem B1901367 : Blo 1899435 1901367 := bstep (se 1 (by rfl) ⟨1426025, by rfl⟩ : syracuseStep 1901367 = 2852051) B2852051
theorem B3208565 : Blo 1899435 3208565 := bbase (se 5 (by rfl) ⟨150401, by rfl⟩ : syracuseStep 3208565 = 300803) (by norm_num)
theorem B2139043 : Blo 1899435 2139043 := bstep (se 1 (by rfl) ⟨1604282, by rfl⟩ : syracuseStep 2139043 = 3208565) B3208565
theorem B2852057 : Blo 1899435 2852057 := bstep (se 2 (by rfl) ⟨1069521, by rfl⟩ : syracuseStep 2852057 = 2139043) B2139043
theorem B1901371 : Blo 1899435 1901371 := bstep (se 1 (by rfl) ⟨1426028, by rfl⟩ : syracuseStep 1901371 = 2852057) B2852057
theorem B3045637 : Blo 1899435 3045637 := bbase (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) (by norm_num)
theorem B4060849 : Blo 1899435 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B5414465 : Blo 1899435 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B14438573 : Blo 1899435 14438573 := bstep (se 3 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 14438573 = 5414465) B5414465
theorem B9625715 : Blo 1899435 9625715 := bstep (se 1 (by rfl) ⟨7219286, by rfl⟩ : syracuseStep 9625715 = 14438573) B14438573
theorem B6417143 : Blo 1899435 6417143 := bstep (se 1 (by rfl) ⟨4812857, by rfl⟩ : syracuseStep 6417143 = 9625715) B9625715
theorem B4278095 : Blo 1899435 4278095 := bstep (se 1 (by rfl) ⟨3208571, by rfl⟩ : syracuseStep 4278095 = 6417143) B6417143
theorem B2852063 : Blo 1899435 2852063 := bstep (se 1 (by rfl) ⟨2139047, by rfl⟩ : syracuseStep 2852063 = 4278095) B4278095
theorem B1901375 : Blo 1899435 1901375 := bstep (se 1 (by rfl) ⟨1426031, by rfl⟩ : syracuseStep 1901375 = 2852063) B2852063
theorem B2852069 : Blo 1899435 2852069 := bbase (se 4 (by rfl) ⟨267381, by rfl⟩ : syracuseStep 2852069 = 534763) (by norm_num)
theorem B1901379 : Blo 1899435 1901379 := bstep (se 1 (by rfl) ⟨1426034, by rfl⟩ : syracuseStep 1901379 = 2852069) B2852069
theorem B6091301 : Blo 1899435 6091301 := bbase (se 4 (by rfl) ⟨571059, by rfl⟩ : syracuseStep 6091301 = 1142119) (by norm_num)
theorem B4060867 : Blo 1899435 4060867 := bstep (se 1 (by rfl) ⟨3045650, by rfl⟩ : syracuseStep 4060867 = 6091301) B6091301
theorem B5414489 : Blo 1899435 5414489 := bstep (se 2 (by rfl) ⟨2030433, by rfl⟩ : syracuseStep 5414489 = 4060867) B4060867
theorem B3609659 : Blo 1899435 3609659 := bstep (se 1 (by rfl) ⟨2707244, by rfl⟩ : syracuseStep 3609659 = 5414489) B5414489
theorem B2406439 : Blo 1899435 2406439 := bstep (se 1 (by rfl) ⟨1804829, by rfl⟩ : syracuseStep 2406439 = 3609659) B3609659
theorem B3208585 : Blo 1899435 3208585 := bstep (se 2 (by rfl) ⟨1203219, by rfl⟩ : syracuseStep 3208585 = 2406439) B2406439
theorem B4278113 : Blo 1899435 4278113 := bstep (se 2 (by rfl) ⟨1604292, by rfl⟩ : syracuseStep 4278113 = 3208585) B3208585
theorem B2852075 : Blo 1899435 2852075 := bstep (se 1 (by rfl) ⟨2139056, by rfl⟩ : syracuseStep 2852075 = 4278113) B4278113
theorem B1901383 : Blo 1899435 1901383 := bstep (se 1 (by rfl) ⟨1426037, by rfl⟩ : syracuseStep 1901383 = 2852075) B2852075
theorem B2139061 : Blo 1899435 2139061 := bbase (se 5 (by rfl) ⟨100268, by rfl⟩ : syracuseStep 2139061 = 200537) (by norm_num)
theorem B2852081 : Blo 1899435 2852081 := bstep (se 2 (by rfl) ⟨1069530, by rfl⟩ : syracuseStep 2852081 = 2139061) B2139061
theorem B1901387 : Blo 1899435 1901387 := bstep (se 1 (by rfl) ⟨1426040, by rfl⟩ : syracuseStep 1901387 = 2852081) B2852081
theorem B2406449 : Blo 1899435 2406449 := bbase (se 2 (by rfl) ⟨902418, by rfl⟩ : syracuseStep 2406449 = 1804837) (by norm_num)
theorem B6417197 : Blo 1899435 6417197 := bstep (se 3 (by rfl) ⟨1203224, by rfl⟩ : syracuseStep 6417197 = 2406449) B2406449
theorem B4278131 : Blo 1899435 4278131 := bstep (se 1 (by rfl) ⟨3208598, by rfl⟩ : syracuseStep 4278131 = 6417197) B6417197
theorem B2852087 : Blo 1899435 2852087 := bstep (se 1 (by rfl) ⟨2139065, by rfl⟩ : syracuseStep 2852087 = 4278131) B4278131
theorem B1901391 : Blo 1899435 1901391 := bstep (se 1 (by rfl) ⟨1426043, by rfl⟩ : syracuseStep 1901391 = 2852087) B2852087
theorem B2852093 : Blo 1899435 2852093 := bbase (se 3 (by rfl) ⟨534767, by rfl⟩ : syracuseStep 2852093 = 1069535) (by norm_num)
theorem B1901395 : Blo 1899435 1901395 := bstep (se 1 (by rfl) ⟨1426046, by rfl⟩ : syracuseStep 1901395 = 2852093) B2852093
theorem B4278149 : Blo 1899435 4278149 := bbase (se 4 (by rfl) ⟨401076, by rfl⟩ : syracuseStep 4278149 = 802153) (by norm_num)
theorem B2852099 : Blo 1899435 2852099 := bstep (se 1 (by rfl) ⟨2139074, by rfl⟩ : syracuseStep 2852099 = 4278149) B4278149
theorem B1901399 : Blo 1899435 1901399 := bstep (se 1 (by rfl) ⟨1426049, by rfl⟩ : syracuseStep 1901399 = 2852099) B2852099
theorem B4568525 : Blo 1899435 4568525 := bbase (se 3 (by rfl) ⟨856598, by rfl⟩ : syracuseStep 4568525 = 1713197) (by norm_num)
theorem B3045683 : Blo 1899435 3045683 := bstep (se 1 (by rfl) ⟨2284262, by rfl⟩ : syracuseStep 3045683 = 4568525) B4568525
theorem B2030455 : Blo 1899435 2030455 := bstep (se 1 (by rfl) ⟨1522841, by rfl⟩ : syracuseStep 2030455 = 3045683) B3045683
theorem B2707273 : Blo 1899435 2707273 := bstep (se 2 (by rfl) ⟨1015227, by rfl⟩ : syracuseStep 2707273 = 2030455) B2030455
theorem B3609697 : Blo 1899435 3609697 := bstep (se 2 (by rfl) ⟨1353636, by rfl⟩ : syracuseStep 3609697 = 2707273) B2707273
theorem B4812929 : Blo 1899435 4812929 := bstep (se 2 (by rfl) ⟨1804848, by rfl⟩ : syracuseStep 4812929 = 3609697) B3609697
theorem B3208619 : Blo 1899435 3208619 := bstep (se 1 (by rfl) ⟨2406464, by rfl⟩ : syracuseStep 3208619 = 4812929) B4812929
theorem B2139079 : Blo 1899435 2139079 := bstep (se 1 (by rfl) ⟨1604309, by rfl⟩ : syracuseStep 2139079 = 3208619) B3208619
theorem B2852105 : Blo 1899435 2852105 := bstep (se 2 (by rfl) ⟨1069539, by rfl⟩ : syracuseStep 2852105 = 2139079) B2139079
theorem B1901403 : Blo 1899435 1901403 := bstep (se 1 (by rfl) ⟨1426052, by rfl⟩ : syracuseStep 1901403 = 2852105) B2852105
theorem B9625877 : Blo 1899435 9625877 := bbase (se 6 (by rfl) ⟨225606, by rfl⟩ : syracuseStep 9625877 = 451213) (by norm_num)
theorem B6417251 : Blo 1899435 6417251 := bstep (se 1 (by rfl) ⟨4812938, by rfl⟩ : syracuseStep 6417251 = 9625877) B9625877
theorem B4278167 : Blo 1899435 4278167 := bstep (se 1 (by rfl) ⟨3208625, by rfl⟩ : syracuseStep 4278167 = 6417251) B6417251
theorem B2852111 : Blo 1899435 2852111 := bstep (se 1 (by rfl) ⟨2139083, by rfl⟩ : syracuseStep 2852111 = 4278167) B4278167
theorem B1901407 : Blo 1899435 1901407 := bstep (se 1 (by rfl) ⟨1426055, by rfl⟩ : syracuseStep 1901407 = 2852111) B2852111
theorem B2852117 : Blo 1899435 2852117 := bbase (se 6 (by rfl) ⟨66846, by rfl⟩ : syracuseStep 2852117 = 133693) (by norm_num)
theorem B1901411 : Blo 1899435 1901411 := bstep (se 1 (by rfl) ⟨1426058, by rfl⟩ : syracuseStep 1901411 = 2852117) B2852117
theorem B5488453 : Blo 1899435 5488453 := bbase (se 4 (by rfl) ⟨514542, by rfl⟩ : syracuseStep 5488453 = 1029085) (by norm_num)
theorem B7317937 : Blo 1899435 7317937 := bstep (se 2 (by rfl) ⟨2744226, by rfl⟩ : syracuseStep 7317937 = 5488453) B5488453
theorem B39028997 : Blo 1899435 39028997 := bstep (se 4 (by rfl) ⟨3658968, by rfl⟩ : syracuseStep 39028997 = 7317937) B7317937
theorem B104077325 : Blo 1899435 104077325 := bstep (se 3 (by rfl) ⟨19514498, by rfl⟩ : syracuseStep 104077325 = 39028997) B39028997
theorem B69384883 : Blo 1899435 69384883 := bstep (se 1 (by rfl) ⟨52038662, by rfl⟩ : syracuseStep 69384883 = 104077325) B104077325
theorem B92513177 : Blo 1899435 92513177 := bstep (se 2 (by rfl) ⟨34692441, by rfl⟩ : syracuseStep 92513177 = 69384883) B69384883
theorem B61675451 : Blo 1899435 61675451 := bstep (se 1 (by rfl) ⟨46256588, by rfl⟩ : syracuseStep 61675451 = 92513177) B92513177
theorem B41116967 : Blo 1899435 41116967 := bstep (se 1 (by rfl) ⟨30837725, by rfl⟩ : syracuseStep 41116967 = 61675451) B61675451
theorem B27411311 : Blo 1899435 27411311 := bstep (se 1 (by rfl) ⟨20558483, by rfl⟩ : syracuseStep 27411311 = 41116967) B41116967
theorem B18274207 : Blo 1899435 18274207 := bstep (se 1 (by rfl) ⟨13705655, by rfl⟩ : syracuseStep 18274207 = 27411311) B27411311
theorem B24365609 : Blo 1899435 24365609 := bstep (se 2 (by rfl) ⟨9137103, by rfl⟩ : syracuseStep 24365609 = 18274207) B18274207
theorem B16243739 : Blo 1899435 16243739 := bstep (se 1 (by rfl) ⟨12182804, by rfl⟩ : syracuseStep 16243739 = 24365609) B24365609
theorem B10829159 : Blo 1899435 10829159 := bstep (se 1 (by rfl) ⟨8121869, by rfl⟩ : syracuseStep 10829159 = 16243739) B16243739
theorem B7219439 : Blo 1899435 7219439 := bstep (se 1 (by rfl) ⟨5414579, by rfl⟩ : syracuseStep 7219439 = 10829159) B10829159
theorem B4812959 : Blo 1899435 4812959 := bstep (se 1 (by rfl) ⟨3609719, by rfl⟩ : syracuseStep 4812959 = 7219439) B7219439
theorem B3208639 : Blo 1899435 3208639 := bstep (se 1 (by rfl) ⟨2406479, by rfl⟩ : syracuseStep 3208639 = 4812959) B4812959
theorem B4278185 : Blo 1899435 4278185 := bstep (se 2 (by rfl) ⟨1604319, by rfl⟩ : syracuseStep 4278185 = 3208639) B3208639
theorem B2852123 : Blo 1899435 2852123 := bstep (se 1 (by rfl) ⟨2139092, by rfl⟩ : syracuseStep 2852123 = 4278185) B4278185
theorem B1901415 : Blo 1899435 1901415 := bstep (se 1 (by rfl) ⟨1426061, by rfl⟩ : syracuseStep 1901415 = 2852123) B2852123
theorem B2139097 : Blo 1899435 2139097 := bbase (se 2 (by rfl) ⟨802161, by rfl⟩ : syracuseStep 2139097 = 1604323) (by norm_num)
theorem B2852129 : Blo 1899435 2852129 := bstep (se 2 (by rfl) ⟨1069548, by rfl⟩ : syracuseStep 2852129 = 2139097) B2139097
theorem B1901419 : Blo 1899435 1901419 := bstep (se 1 (by rfl) ⟨1426064, by rfl⟩ : syracuseStep 1901419 = 2852129) B2852129
theorem B2707301 : Blo 1899435 2707301 := bbase (se 4 (by rfl) ⟨253809, by rfl⟩ : syracuseStep 2707301 = 507619) (by norm_num)
theorem B7219469 : Blo 1899435 7219469 := bstep (se 3 (by rfl) ⟨1353650, by rfl⟩ : syracuseStep 7219469 = 2707301) B2707301
theorem B4812979 : Blo 1899435 4812979 := bstep (se 1 (by rfl) ⟨3609734, by rfl⟩ : syracuseStep 4812979 = 7219469) B7219469
theorem B6417305 : Blo 1899435 6417305 := bstep (se 2 (by rfl) ⟨2406489, by rfl⟩ : syracuseStep 6417305 = 4812979) B4812979
theorem B4278203 : Blo 1899435 4278203 := bstep (se 1 (by rfl) ⟨3208652, by rfl⟩ : syracuseStep 4278203 = 6417305) B6417305
theorem B2852135 : Blo 1899435 2852135 := bstep (se 1 (by rfl) ⟨2139101, by rfl⟩ : syracuseStep 2852135 = 4278203) B4278203
theorem B1901423 : Blo 1899435 1901423 := bstep (se 1 (by rfl) ⟨1426067, by rfl⟩ : syracuseStep 1901423 = 2852135) B2852135
theorem B2852141 : Blo 1899435 2852141 := bbase (se 3 (by rfl) ⟨534776, by rfl⟩ : syracuseStep 2852141 = 1069553) (by norm_num)
theorem B1901427 : Blo 1899435 1901427 := bstep (se 1 (by rfl) ⟨1426070, by rfl⟩ : syracuseStep 1901427 = 2852141) B2852141
theorem B4278221 : Blo 1899435 4278221 := bbase (se 3 (by rfl) ⟨802166, by rfl⟩ : syracuseStep 4278221 = 1604333) (by norm_num)
theorem B2852147 : Blo 1899435 2852147 := bstep (se 1 (by rfl) ⟨2139110, by rfl⟩ : syracuseStep 2852147 = 4278221) B4278221
theorem B1901431 : Blo 1899435 1901431 := bstep (se 1 (by rfl) ⟨1426073, by rfl⟩ : syracuseStep 1901431 = 2852147) B2852147
theorem B2406505 : Blo 1899435 2406505 := bbase (se 2 (by rfl) ⟨902439, by rfl⟩ : syracuseStep 2406505 = 1804879) (by norm_num)
theorem B3208673 : Blo 1899435 3208673 := bstep (se 2 (by rfl) ⟨1203252, by rfl⟩ : syracuseStep 3208673 = 2406505) B2406505
theorem B2139115 : Blo 1899435 2139115 := bstep (se 1 (by rfl) ⟨1604336, by rfl⟩ : syracuseStep 2139115 = 3208673) B3208673
theorem B2852153 : Blo 1899435 2852153 := bstep (se 2 (by rfl) ⟨1069557, by rfl⟩ : syracuseStep 2852153 = 2139115) B2139115
theorem B1901435 : Blo 1899435 1901435 := bstep (se 1 (by rfl) ⟨1426076, by rfl⟩ : syracuseStep 1901435 = 2852153) B2852153
theorem C0 (j : ℕ) (h1 : 474858 ≤ j) (h2 : j ≤ 475358) : Blo 1899435 (4 * j + 3) := by
  interval_cases j
  · exact B1899435
  · exact B1899439
  · exact B1899443
  · exact B1899447
  · exact B1899451
  · exact B1899455
  · exact B1899459
  · exact B1899463
  · exact B1899467
  · exact B1899471
  · exact B1899475
  · exact B1899479
  · exact B1899483
  · exact B1899487
  · exact B1899491
  · exact B1899495
  · exact B1899499
  · exact B1899503
  · exact B1899507
  · exact B1899511
  · exact B1899515
  · exact B1899519
  · exact B1899523
  · exact B1899527
  · exact B1899531
  · exact B1899535
  · exact B1899539
  · exact B1899543
  · exact B1899547
  · exact B1899551
  · exact B1899555
  · exact B1899559
  · exact B1899563
  · exact B1899567
  · exact B1899571
  · exact B1899575
  · exact B1899579
  · exact B1899583
  · exact B1899587
  · exact B1899591
  · exact B1899595
  · exact B1899599
  · exact B1899603
  · exact B1899607
  · exact B1899611
  · exact B1899615
  · exact B1899619
  · exact B1899623
  · exact B1899627
  · exact B1899631
  · exact B1899635
  · exact B1899639
  · exact B1899643
  · exact B1899647
  · exact B1899651
  · exact B1899655
  · exact B1899659
  · exact B1899663
  · exact B1899667
  · exact B1899671
  · exact B1899675
  · exact B1899679
  · exact B1899683
  · exact B1899687
  · exact B1899691
  · exact B1899695
  · exact B1899699
  · exact B1899703
  · exact B1899707
  · exact B1899711
  · exact B1899715
  · exact B1899719
  · exact B1899723
  · exact B1899727
  · exact B1899731
  · exact B1899735
  · exact B1899739
  · exact B1899743
  · exact B1899747
  · exact B1899751
  · exact B1899755
  · exact B1899759
  · exact B1899763
  · exact B1899767
  · exact B1899771
  · exact B1899775
  · exact B1899779
  · exact B1899783
  · exact B1899787
  · exact B1899791
  · exact B1899795
  · exact B1899799
  · exact B1899803
  · exact B1899807
  · exact B1899811
  · exact B1899815
  · exact B1899819
  · exact B1899823
  · exact B1899827
  · exact B1899831
  · exact B1899835
  · exact B1899839
  · exact B1899843
  · exact B1899847
  · exact B1899851
  · exact B1899855
  · exact B1899859
  · exact B1899863
  · exact B1899867
  · exact B1899871
  · exact B1899875
  · exact B1899879
  · exact B1899883
  · exact B1899887
  · exact B1899891
  · exact B1899895
  · exact B1899899
  · exact B1899903
  · exact B1899907
  · exact B1899911
  · exact B1899915
  · exact B1899919
  · exact B1899923
  · exact B1899927
  · exact B1899931
  · exact B1899935
  · exact B1899939
  · exact B1899943
  · exact B1899947
  · exact B1899951
  · exact B1899955
  · exact B1899959
  · exact B1899963
  · exact B1899967
  · exact B1899971
  · exact B1899975
  · exact B1899979
  · exact B1899983
  · exact B1899987
  · exact B1899991
  · exact B1899995
  · exact B1899999
  · exact B1900003
  · exact B1900007
  · exact B1900011
  · exact B1900015
  · exact B1900019
  · exact B1900023
  · exact B1900027
  · exact B1900031
  · exact B1900035
  · exact B1900039
  · exact B1900043
  · exact B1900047
  · exact B1900051
  · exact B1900055
  · exact B1900059
  · exact B1900063
  · exact B1900067
  · exact B1900071
  · exact B1900075
  · exact B1900079
  · exact B1900083
  · exact B1900087
  · exact B1900091
  · exact B1900095
  · exact B1900099
  · exact B1900103
  · exact B1900107
  · exact B1900111
  · exact B1900115
  · exact B1900119
  · exact B1900123
  · exact B1900127
  · exact B1900131
  · exact B1900135
  · exact B1900139
  · exact B1900143
  · exact B1900147
  · exact B1900151
  · exact B1900155
  · exact B1900159
  · exact B1900163
  · exact B1900167
  · exact B1900171
  · exact B1900175
  · exact B1900179
  · exact B1900183
  · exact B1900187
  · exact B1900191
  · exact B1900195
  · exact B1900199
  · exact B1900203
  · exact B1900207
  · exact B1900211
  · exact B1900215
  · exact B1900219
  · exact B1900223
  · exact B1900227
  · exact B1900231
  · exact B1900235
  · exact B1900239
  · exact B1900243
  · exact B1900247
  · exact B1900251
  · exact B1900255
  · exact B1900259
  · exact B1900263
  · exact B1900267
  · exact B1900271
  · exact B1900275
  · exact B1900279
  · exact B1900283
  · exact B1900287
  · exact B1900291
  · exact B1900295
  · exact B1900299
  · exact B1900303
  · exact B1900307
  · exact B1900311
  · exact B1900315
  · exact B1900319
  · exact B1900323
  · exact B1900327
  · exact B1900331
  · exact B1900335
  · exact B1900339
  · exact B1900343
  · exact B1900347
  · exact B1900351
  · exact B1900355
  · exact B1900359
  · exact B1900363
  · exact B1900367
  · exact B1900371
  · exact B1900375
  · exact B1900379
  · exact B1900383
  · exact B1900387
  · exact B1900391
  · exact B1900395
  · exact B1900399
  · exact B1900403
  · exact B1900407
  · exact B1900411
  · exact B1900415
  · exact B1900419
  · exact B1900423
  · exact B1900427
  · exact B1900431
  · exact B1900435
  · exact B1900439
  · exact B1900443
  · exact B1900447
  · exact B1900451
  · exact B1900455
  · exact B1900459
  · exact B1900463
  · exact B1900467
  · exact B1900471
  · exact B1900475
  · exact B1900479
  · exact B1900483
  · exact B1900487
  · exact B1900491
  · exact B1900495
  · exact B1900499
  · exact B1900503
  · exact B1900507
  · exact B1900511
  · exact B1900515
  · exact B1900519
  · exact B1900523
  · exact B1900527
  · exact B1900531
  · exact B1900535
  · exact B1900539
  · exact B1900543
  · exact B1900547
  · exact B1900551
  · exact B1900555
  · exact B1900559
  · exact B1900563
  · exact B1900567
  · exact B1900571
  · exact B1900575
  · exact B1900579
  · exact B1900583
  · exact B1900587
  · exact B1900591
  · exact B1900595
  · exact B1900599
  · exact B1900603
  · exact B1900607
  · exact B1900611
  · exact B1900615
  · exact B1900619
  · exact B1900623
  · exact B1900627
  · exact B1900631
  · exact B1900635
  · exact B1900639
  · exact B1900643
  · exact B1900647
  · exact B1900651
  · exact B1900655
  · exact B1900659
  · exact B1900663
  · exact B1900667
  · exact B1900671
  · exact B1900675
  · exact B1900679
  · exact B1900683
  · exact B1900687
  · exact B1900691
  · exact B1900695
  · exact B1900699
  · exact B1900703
  · exact B1900707
  · exact B1900711
  · exact B1900715
  · exact B1900719
  · exact B1900723
  · exact B1900727
  · exact B1900731
  · exact B1900735
  · exact B1900739
  · exact B1900743
  · exact B1900747
  · exact B1900751
  · exact B1900755
  · exact B1900759
  · exact B1900763
  · exact B1900767
  · exact B1900771
  · exact B1900775
  · exact B1900779
  · exact B1900783
  · exact B1900787
  · exact B1900791
  · exact B1900795
  · exact B1900799
  · exact B1900803
  · exact B1900807
  · exact B1900811
  · exact B1900815
  · exact B1900819
  · exact B1900823
  · exact B1900827
  · exact B1900831
  · exact B1900835
  · exact B1900839
  · exact B1900843
  · exact B1900847
  · exact B1900851
  · exact B1900855
  · exact B1900859
  · exact B1900863
  · exact B1900867
  · exact B1900871
  · exact B1900875
  · exact B1900879
  · exact B1900883
  · exact B1900887
  · exact B1900891
  · exact B1900895
  · exact B1900899
  · exact B1900903
  · exact B1900907
  · exact B1900911
  · exact B1900915
  · exact B1900919
  · exact B1900923
  · exact B1900927
  · exact B1900931
  · exact B1900935
  · exact B1900939
  · exact B1900943
  · exact B1900947
  · exact B1900951
  · exact B1900955
  · exact B1900959
  · exact B1900963
  · exact B1900967
  · exact B1900971
  · exact B1900975
  · exact B1900979
  · exact B1900983
  · exact B1900987
  · exact B1900991
  · exact B1900995
  · exact B1900999
  · exact B1901003
  · exact B1901007
  · exact B1901011
  · exact B1901015
  · exact B1901019
  · exact B1901023
  · exact B1901027
  · exact B1901031
  · exact B1901035
  · exact B1901039
  · exact B1901043
  · exact B1901047
  · exact B1901051
  · exact B1901055
  · exact B1901059
  · exact B1901063
  · exact B1901067
  · exact B1901071
  · exact B1901075
  · exact B1901079
  · exact B1901083
  · exact B1901087
  · exact B1901091
  · exact B1901095
  · exact B1901099
  · exact B1901103
  · exact B1901107
  · exact B1901111
  · exact B1901115
  · exact B1901119
  · exact B1901123
  · exact B1901127
  · exact B1901131
  · exact B1901135
  · exact B1901139
  · exact B1901143
  · exact B1901147
  · exact B1901151
  · exact B1901155
  · exact B1901159
  · exact B1901163
  · exact B1901167
  · exact B1901171
  · exact B1901175
  · exact B1901179
  · exact B1901183
  · exact B1901187
  · exact B1901191
  · exact B1901195
  · exact B1901199
  · exact B1901203
  · exact B1901207
  · exact B1901211
  · exact B1901215
  · exact B1901219
  · exact B1901223
  · exact B1901227
  · exact B1901231
  · exact B1901235
  · exact B1901239
  · exact B1901243
  · exact B1901247
  · exact B1901251
  · exact B1901255
  · exact B1901259
  · exact B1901263
  · exact B1901267
  · exact B1901271
  · exact B1901275
  · exact B1901279
  · exact B1901283
  · exact B1901287
  · exact B1901291
  · exact B1901295
  · exact B1901299
  · exact B1901303
  · exact B1901307
  · exact B1901311
  · exact B1901315
  · exact B1901319
  · exact B1901323
  · exact B1901327
  · exact B1901331
  · exact B1901335
  · exact B1901339
  · exact B1901343
  · exact B1901347
  · exact B1901351
  · exact B1901355
  · exact B1901359
  · exact B1901363
  · exact B1901367
  · exact B1901371
  · exact B1901375
  · exact B1901379
  · exact B1901383
  · exact B1901387
  · exact B1901391
  · exact B1901395
  · exact B1901399
  · exact B1901403
  · exact B1901407
  · exact B1901411
  · exact B1901415
  · exact B1901419
  · exact B1901423
  · exact B1901427
  · exact B1901431
  · exact B1901435
theorem solution (m : ℕ) (hlo : 1899435 ≤ m) (hhi : m ≤ 1901435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 474858 ≤ j := by omega
    have hj2 : j ≤ 475358 := by omega
    have hb : Blo 1899435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
