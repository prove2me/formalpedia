-- Prove2me | solution 1 for syracuse_descends_range_2187435_2189435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:03.803143+00:00
-- url     : https://prove2.me/submissions/8d2cd395-b1cf-4fb4-9997-38a6acd89934

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

theorem B2460865 : Blo 2187435 2460865 := bbase (se 2 (by rfl) ⟨922824, by rfl⟩ : syracuseStep 2460865 = 1845649) (by norm_num)
theorem B3281153 : Blo 2187435 3281153 := bstep (se 2 (by rfl) ⟨1230432, by rfl⟩ : syracuseStep 3281153 = 2460865) B2460865
theorem B2187435 : Blo 2187435 2187435 := bstep (se 1 (by rfl) ⟨1640576, by rfl⟩ : syracuseStep 2187435 = 3281153) B3281153
theorem B5536957 : Blo 2187435 5536957 := bbase (se 3 (by rfl) ⟨1038179, by rfl⟩ : syracuseStep 5536957 = 2076359) (by norm_num)
theorem B7382609 : Blo 2187435 7382609 := bstep (se 2 (by rfl) ⟨2768478, by rfl⟩ : syracuseStep 7382609 = 5536957) B5536957
theorem B4921739 : Blo 2187435 4921739 := bstep (se 1 (by rfl) ⟨3691304, by rfl⟩ : syracuseStep 4921739 = 7382609) B7382609
theorem B3281159 : Blo 2187435 3281159 := bstep (se 1 (by rfl) ⟨2460869, by rfl⟩ : syracuseStep 3281159 = 4921739) B4921739
theorem B2187439 : Blo 2187435 2187439 := bstep (se 1 (by rfl) ⟨1640579, by rfl⟩ : syracuseStep 2187439 = 3281159) B3281159
theorem B3281165 : Blo 2187435 3281165 := bbase (se 3 (by rfl) ⟨615218, by rfl⟩ : syracuseStep 3281165 = 1230437) (by norm_num)
theorem B2187443 : Blo 2187435 2187443 := bstep (se 1 (by rfl) ⟨1640582, by rfl⟩ : syracuseStep 2187443 = 3281165) B3281165
theorem B4921757 : Blo 2187435 4921757 := bbase (se 3 (by rfl) ⟨922829, by rfl⟩ : syracuseStep 4921757 = 1845659) (by norm_num)
theorem B3281171 : Blo 2187435 3281171 := bstep (se 1 (by rfl) ⟨2460878, by rfl⟩ : syracuseStep 3281171 = 4921757) B4921757
theorem B2187447 : Blo 2187435 2187447 := bstep (se 1 (by rfl) ⟨1640585, by rfl⟩ : syracuseStep 2187447 = 3281171) B3281171
theorem B3691325 : Blo 2187435 3691325 := bbase (se 3 (by rfl) ⟨692123, by rfl⟩ : syracuseStep 3691325 = 1384247) (by norm_num)
theorem B2460883 : Blo 2187435 2460883 := bstep (se 1 (by rfl) ⟨1845662, by rfl⟩ : syracuseStep 2460883 = 3691325) B3691325
theorem B3281177 : Blo 2187435 3281177 := bstep (se 2 (by rfl) ⟨1230441, by rfl⟩ : syracuseStep 3281177 = 2460883) B2460883
theorem B2187451 : Blo 2187435 2187451 := bstep (se 1 (by rfl) ⟨1640588, by rfl⟩ : syracuseStep 2187451 = 3281177) B3281177
theorem B2335921 : Blo 2187435 2335921 := bbase (se 2 (by rfl) ⟨875970, by rfl⟩ : syracuseStep 2335921 = 1751941) (by norm_num)
theorem B12458245 : Blo 2187435 12458245 := bstep (se 4 (by rfl) ⟨1167960, by rfl⟩ : syracuseStep 12458245 = 2335921) B2335921
theorem B16610993 : Blo 2187435 16610993 := bstep (se 2 (by rfl) ⟨6229122, by rfl⟩ : syracuseStep 16610993 = 12458245) B12458245
theorem B11073995 : Blo 2187435 11073995 := bstep (se 1 (by rfl) ⟨8305496, by rfl⟩ : syracuseStep 11073995 = 16610993) B16610993
theorem B7382663 : Blo 2187435 7382663 := bstep (se 1 (by rfl) ⟨5536997, by rfl⟩ : syracuseStep 7382663 = 11073995) B11073995
theorem B4921775 : Blo 2187435 4921775 := bstep (se 1 (by rfl) ⟨3691331, by rfl⟩ : syracuseStep 4921775 = 7382663) B7382663
theorem B3281183 : Blo 2187435 3281183 := bstep (se 1 (by rfl) ⟨2460887, by rfl⟩ : syracuseStep 3281183 = 4921775) B4921775
theorem B2187455 : Blo 2187435 2187455 := bstep (se 1 (by rfl) ⟨1640591, by rfl⟩ : syracuseStep 2187455 = 3281183) B3281183
theorem B3281189 : Blo 2187435 3281189 := bbase (se 4 (by rfl) ⟨307611, by rfl⟩ : syracuseStep 3281189 = 615223) (by norm_num)
theorem B2187459 : Blo 2187435 2187459 := bstep (se 1 (by rfl) ⟨1640594, by rfl⟩ : syracuseStep 2187459 = 3281189) B3281189
theorem B2768509 : Blo 2187435 2768509 := bbase (se 3 (by rfl) ⟨519095, by rfl⟩ : syracuseStep 2768509 = 1038191) (by norm_num)
theorem B3691345 : Blo 2187435 3691345 := bstep (se 2 (by rfl) ⟨1384254, by rfl⟩ : syracuseStep 3691345 = 2768509) B2768509
theorem B4921793 : Blo 2187435 4921793 := bstep (se 2 (by rfl) ⟨1845672, by rfl⟩ : syracuseStep 4921793 = 3691345) B3691345
theorem B3281195 : Blo 2187435 3281195 := bstep (se 1 (by rfl) ⟨2460896, by rfl⟩ : syracuseStep 3281195 = 4921793) B4921793
theorem B2187463 : Blo 2187435 2187463 := bstep (se 1 (by rfl) ⟨1640597, by rfl⟩ : syracuseStep 2187463 = 3281195) B3281195
theorem B2460901 : Blo 2187435 2460901 := bbase (se 4 (by rfl) ⟨230709, by rfl⟩ : syracuseStep 2460901 = 461419) (by norm_num)
theorem B3281201 : Blo 2187435 3281201 := bstep (se 2 (by rfl) ⟨1230450, by rfl⟩ : syracuseStep 3281201 = 2460901) B2460901
theorem B2187467 : Blo 2187435 2187467 := bstep (se 1 (by rfl) ⟨1640600, by rfl⟩ : syracuseStep 2187467 = 3281201) B3281201
theorem B4671877 : Blo 2187435 4671877 := bbase (se 4 (by rfl) ⟨437988, by rfl⟩ : syracuseStep 4671877 = 875977) (by norm_num)
theorem B6229169 : Blo 2187435 6229169 := bstep (se 2 (by rfl) ⟨2335938, by rfl⟩ : syracuseStep 6229169 = 4671877) B4671877
theorem B4152779 : Blo 2187435 4152779 := bstep (se 1 (by rfl) ⟨3114584, by rfl⟩ : syracuseStep 4152779 = 6229169) B6229169
theorem B2768519 : Blo 2187435 2768519 := bstep (se 1 (by rfl) ⟨2076389, by rfl⟩ : syracuseStep 2768519 = 4152779) B4152779
theorem B7382717 : Blo 2187435 7382717 := bstep (se 3 (by rfl) ⟨1384259, by rfl⟩ : syracuseStep 7382717 = 2768519) B2768519
theorem B4921811 : Blo 2187435 4921811 := bstep (se 1 (by rfl) ⟨3691358, by rfl⟩ : syracuseStep 4921811 = 7382717) B7382717
theorem B3281207 : Blo 2187435 3281207 := bstep (se 1 (by rfl) ⟨2460905, by rfl⟩ : syracuseStep 3281207 = 4921811) B4921811
theorem B2187471 : Blo 2187435 2187471 := bstep (se 1 (by rfl) ⟨1640603, by rfl⟩ : syracuseStep 2187471 = 3281207) B3281207
theorem B3281213 : Blo 2187435 3281213 := bbase (se 3 (by rfl) ⟨615227, by rfl⟩ : syracuseStep 3281213 = 1230455) (by norm_num)
theorem B2187475 : Blo 2187435 2187475 := bstep (se 1 (by rfl) ⟨1640606, by rfl⟩ : syracuseStep 2187475 = 3281213) B3281213
theorem B4921829 : Blo 2187435 4921829 := bbase (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) (by norm_num)
theorem B3281219 : Blo 2187435 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B2187479 : Blo 2187435 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B5537069 : Blo 2187435 5537069 := bbase (se 3 (by rfl) ⟨1038200, by rfl⟩ : syracuseStep 5537069 = 2076401) (by norm_num)
theorem B3691379 : Blo 2187435 3691379 := bstep (se 1 (by rfl) ⟨2768534, by rfl⟩ : syracuseStep 3691379 = 5537069) B5537069
theorem B2460919 : Blo 2187435 2460919 := bstep (se 1 (by rfl) ⟨1845689, by rfl⟩ : syracuseStep 2460919 = 3691379) B3691379
theorem B3281225 : Blo 2187435 3281225 := bstep (se 2 (by rfl) ⟨1230459, by rfl⟩ : syracuseStep 3281225 = 2460919) B2460919
theorem B2187483 : Blo 2187435 2187483 := bstep (se 1 (by rfl) ⟨1640612, by rfl⟩ : syracuseStep 2187483 = 3281225) B3281225
theorem B8869333 : Blo 2187435 8869333 := bbase (se 7 (by rfl) ⟨103937, by rfl⟩ : syracuseStep 8869333 = 207875) (by norm_num)
theorem B11825777 : Blo 2187435 11825777 := bstep (se 2 (by rfl) ⟨4434666, by rfl⟩ : syracuseStep 11825777 = 8869333) B8869333
theorem B7883851 : Blo 2187435 7883851 := bstep (se 1 (by rfl) ⟨5912888, by rfl⟩ : syracuseStep 7883851 = 11825777) B11825777
theorem B10511801 : Blo 2187435 10511801 := bstep (se 2 (by rfl) ⟨3941925, by rfl⟩ : syracuseStep 10511801 = 7883851) B7883851
theorem B7007867 : Blo 2187435 7007867 := bstep (se 1 (by rfl) ⟨5255900, by rfl⟩ : syracuseStep 7007867 = 10511801) B10511801
theorem B4671911 : Blo 2187435 4671911 := bstep (se 1 (by rfl) ⟨3503933, by rfl⟩ : syracuseStep 4671911 = 7007867) B7007867
theorem B3114607 : Blo 2187435 3114607 := bstep (se 1 (by rfl) ⟨2335955, by rfl⟩ : syracuseStep 3114607 = 4671911) B4671911
theorem B4152809 : Blo 2187435 4152809 := bstep (se 2 (by rfl) ⟨1557303, by rfl⟩ : syracuseStep 4152809 = 3114607) B3114607
theorem B11074157 : Blo 2187435 11074157 := bstep (se 3 (by rfl) ⟨2076404, by rfl⟩ : syracuseStep 11074157 = 4152809) B4152809
theorem B7382771 : Blo 2187435 7382771 := bstep (se 1 (by rfl) ⟨5537078, by rfl⟩ : syracuseStep 7382771 = 11074157) B11074157
theorem B4921847 : Blo 2187435 4921847 := bstep (se 1 (by rfl) ⟨3691385, by rfl⟩ : syracuseStep 4921847 = 7382771) B7382771
theorem B3281231 : Blo 2187435 3281231 := bstep (se 1 (by rfl) ⟨2460923, by rfl⟩ : syracuseStep 3281231 = 4921847) B4921847
theorem B2187487 : Blo 2187435 2187487 := bstep (se 1 (by rfl) ⟨1640615, by rfl⟩ : syracuseStep 2187487 = 3281231) B3281231
theorem B3281237 : Blo 2187435 3281237 := bbase (se 10 (by rfl) ⟨4806, by rfl⟩ : syracuseStep 3281237 = 9613) (by norm_num)
theorem B2187491 : Blo 2187435 2187491 := bstep (se 1 (by rfl) ⟨1640618, by rfl⟩ : syracuseStep 2187491 = 3281237) B3281237
theorem B6229237 : Blo 2187435 6229237 := bbase (se 5 (by rfl) ⟨291995, by rfl⟩ : syracuseStep 6229237 = 583991) (by norm_num)
theorem B8305649 : Blo 2187435 8305649 := bstep (se 2 (by rfl) ⟨3114618, by rfl⟩ : syracuseStep 8305649 = 6229237) B6229237
theorem B5537099 : Blo 2187435 5537099 := bstep (se 1 (by rfl) ⟨4152824, by rfl⟩ : syracuseStep 5537099 = 8305649) B8305649
theorem B3691399 : Blo 2187435 3691399 := bstep (se 1 (by rfl) ⟨2768549, by rfl⟩ : syracuseStep 3691399 = 5537099) B5537099
theorem B4921865 : Blo 2187435 4921865 := bstep (se 2 (by rfl) ⟨1845699, by rfl⟩ : syracuseStep 4921865 = 3691399) B3691399
theorem B3281243 : Blo 2187435 3281243 := bstep (se 1 (by rfl) ⟨2460932, by rfl⟩ : syracuseStep 3281243 = 4921865) B4921865
theorem B2187495 : Blo 2187435 2187495 := bstep (se 1 (by rfl) ⟨1640621, by rfl⟩ : syracuseStep 2187495 = 3281243) B3281243
theorem B2460937 : Blo 2187435 2460937 := bbase (se 2 (by rfl) ⟨922851, by rfl⟩ : syracuseStep 2460937 = 1845703) (by norm_num)
theorem B3281249 : Blo 2187435 3281249 := bstep (se 2 (by rfl) ⟨1230468, by rfl⟩ : syracuseStep 3281249 = 2460937) B2460937
theorem B2187499 : Blo 2187435 2187499 := bstep (se 1 (by rfl) ⟨1640624, by rfl⟩ : syracuseStep 2187499 = 3281249) B3281249
theorem B2627969 : Blo 2187435 2627969 := bbase (se 2 (by rfl) ⟨985488, by rfl⟩ : syracuseStep 2627969 = 1970977) (by norm_num)
theorem B28031669 : Blo 2187435 28031669 := bstep (se 5 (by rfl) ⟨1313984, by rfl⟩ : syracuseStep 28031669 = 2627969) B2627969
theorem B18687779 : Blo 2187435 18687779 := bstep (se 1 (by rfl) ⟨14015834, by rfl⟩ : syracuseStep 18687779 = 28031669) B28031669
theorem B12458519 : Blo 2187435 12458519 := bstep (se 1 (by rfl) ⟨9343889, by rfl⟩ : syracuseStep 12458519 = 18687779) B18687779
theorem B8305679 : Blo 2187435 8305679 := bstep (se 1 (by rfl) ⟨6229259, by rfl⟩ : syracuseStep 8305679 = 12458519) B12458519
theorem B5537119 : Blo 2187435 5537119 := bstep (se 1 (by rfl) ⟨4152839, by rfl⟩ : syracuseStep 5537119 = 8305679) B8305679
theorem B7382825 : Blo 2187435 7382825 := bstep (se 2 (by rfl) ⟨2768559, by rfl⟩ : syracuseStep 7382825 = 5537119) B5537119
theorem B4921883 : Blo 2187435 4921883 := bstep (se 1 (by rfl) ⟨3691412, by rfl⟩ : syracuseStep 4921883 = 7382825) B7382825
theorem B3281255 : Blo 2187435 3281255 := bstep (se 1 (by rfl) ⟨2460941, by rfl⟩ : syracuseStep 3281255 = 4921883) B4921883
theorem B2187503 : Blo 2187435 2187503 := bstep (se 1 (by rfl) ⟨1640627, by rfl⟩ : syracuseStep 2187503 = 3281255) B3281255
theorem B3281261 : Blo 2187435 3281261 := bbase (se 3 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 3281261 = 1230473) (by norm_num)
theorem B2187507 : Blo 2187435 2187507 := bstep (se 1 (by rfl) ⟨1640630, by rfl⟩ : syracuseStep 2187507 = 3281261) B3281261
theorem B4921901 : Blo 2187435 4921901 := bbase (se 3 (by rfl) ⟨922856, by rfl⟩ : syracuseStep 4921901 = 1845713) (by norm_num)
theorem B3281267 : Blo 2187435 3281267 := bstep (se 1 (by rfl) ⟨2460950, by rfl⟩ : syracuseStep 3281267 = 4921901) B4921901
theorem B2187511 : Blo 2187435 2187511 := bstep (se 1 (by rfl) ⟨1640633, by rfl⟩ : syracuseStep 2187511 = 3281267) B3281267
theorem B2367857 : Blo 2187435 2367857 := bbase (se 2 (by rfl) ⟨887946, by rfl⟩ : syracuseStep 2367857 = 1775893) (by norm_num)
theorem B6314285 : Blo 2187435 6314285 := bstep (se 3 (by rfl) ⟨1183928, by rfl⟩ : syracuseStep 6314285 = 2367857) B2367857
theorem B16838093 : Blo 2187435 16838093 := bstep (se 3 (by rfl) ⟨3157142, by rfl⟩ : syracuseStep 16838093 = 6314285) B6314285
theorem B11225395 : Blo 2187435 11225395 := bstep (se 1 (by rfl) ⟨8419046, by rfl⟩ : syracuseStep 11225395 = 16838093) B16838093
theorem B14967193 : Blo 2187435 14967193 := bstep (se 2 (by rfl) ⟨5612697, by rfl⟩ : syracuseStep 14967193 = 11225395) B11225395
theorem B19956257 : Blo 2187435 19956257 := bstep (se 2 (by rfl) ⟨7483596, by rfl⟩ : syracuseStep 19956257 = 14967193) B14967193
theorem B13304171 : Blo 2187435 13304171 := bstep (se 1 (by rfl) ⟨9978128, by rfl⟩ : syracuseStep 13304171 = 19956257) B19956257
theorem B8869447 : Blo 2187435 8869447 := bstep (se 1 (by rfl) ⟨6652085, by rfl⟩ : syracuseStep 8869447 = 13304171) B13304171
theorem B11825929 : Blo 2187435 11825929 := bstep (se 2 (by rfl) ⟨4434723, by rfl⟩ : syracuseStep 11825929 = 8869447) B8869447
theorem B15767905 : Blo 2187435 15767905 := bstep (se 2 (by rfl) ⟨5912964, by rfl⟩ : syracuseStep 15767905 = 11825929) B11825929
theorem B21023873 : Blo 2187435 21023873 := bstep (se 2 (by rfl) ⟨7883952, by rfl⟩ : syracuseStep 21023873 = 15767905) B15767905
theorem B14015915 : Blo 2187435 14015915 := bstep (se 1 (by rfl) ⟨10511936, by rfl⟩ : syracuseStep 14015915 = 21023873) B21023873
theorem B9343943 : Blo 2187435 9343943 := bstep (se 1 (by rfl) ⟨7007957, by rfl⟩ : syracuseStep 9343943 = 14015915) B14015915
theorem B6229295 : Blo 2187435 6229295 := bstep (se 1 (by rfl) ⟨4671971, by rfl⟩ : syracuseStep 6229295 = 9343943) B9343943
theorem B4152863 : Blo 2187435 4152863 := bstep (se 1 (by rfl) ⟨3114647, by rfl⟩ : syracuseStep 4152863 = 6229295) B6229295
theorem B2768575 : Blo 2187435 2768575 := bstep (se 1 (by rfl) ⟨2076431, by rfl⟩ : syracuseStep 2768575 = 4152863) B4152863
theorem B3691433 : Blo 2187435 3691433 := bstep (se 2 (by rfl) ⟨1384287, by rfl⟩ : syracuseStep 3691433 = 2768575) B2768575
theorem B2460955 : Blo 2187435 2460955 := bstep (se 1 (by rfl) ⟨1845716, by rfl⟩ : syracuseStep 2460955 = 3691433) B3691433
theorem B3281273 : Blo 2187435 3281273 := bstep (se 2 (by rfl) ⟨1230477, by rfl⟩ : syracuseStep 3281273 = 2460955) B2460955
theorem B2187515 : Blo 2187435 2187515 := bstep (se 1 (by rfl) ⟨1640636, by rfl⟩ : syracuseStep 2187515 = 3281273) B3281273
theorem B37375829 : Blo 2187435 37375829 := bbase (se 9 (by rfl) ⟨109499, by rfl⟩ : syracuseStep 37375829 = 218999) (by norm_num)
theorem B24917219 : Blo 2187435 24917219 := bstep (se 1 (by rfl) ⟨18687914, by rfl⟩ : syracuseStep 24917219 = 37375829) B37375829
theorem B16611479 : Blo 2187435 16611479 := bstep (se 1 (by rfl) ⟨12458609, by rfl⟩ : syracuseStep 16611479 = 24917219) B24917219
theorem B11074319 : Blo 2187435 11074319 := bstep (se 1 (by rfl) ⟨8305739, by rfl⟩ : syracuseStep 11074319 = 16611479) B16611479
theorem B7382879 : Blo 2187435 7382879 := bstep (se 1 (by rfl) ⟨5537159, by rfl⟩ : syracuseStep 7382879 = 11074319) B11074319
theorem B4921919 : Blo 2187435 4921919 := bstep (se 1 (by rfl) ⟨3691439, by rfl⟩ : syracuseStep 4921919 = 7382879) B7382879
theorem B3281279 : Blo 2187435 3281279 := bstep (se 1 (by rfl) ⟨2460959, by rfl⟩ : syracuseStep 3281279 = 4921919) B4921919
theorem B2187519 : Blo 2187435 2187519 := bstep (se 1 (by rfl) ⟨1640639, by rfl⟩ : syracuseStep 2187519 = 3281279) B3281279
theorem B3281285 : Blo 2187435 3281285 := bbase (se 4 (by rfl) ⟨307620, by rfl⟩ : syracuseStep 3281285 = 615241) (by norm_num)
theorem B2187523 : Blo 2187435 2187523 := bstep (se 1 (by rfl) ⟨1640642, by rfl⟩ : syracuseStep 2187523 = 3281285) B3281285
theorem B3691453 : Blo 2187435 3691453 := bbase (se 3 (by rfl) ⟨692147, by rfl⟩ : syracuseStep 3691453 = 1384295) (by norm_num)
theorem B4921937 : Blo 2187435 4921937 := bstep (se 2 (by rfl) ⟨1845726, by rfl⟩ : syracuseStep 4921937 = 3691453) B3691453
theorem B3281291 : Blo 2187435 3281291 := bstep (se 1 (by rfl) ⟨2460968, by rfl⟩ : syracuseStep 3281291 = 4921937) B4921937
theorem B2187527 : Blo 2187435 2187527 := bstep (se 1 (by rfl) ⟨1640645, by rfl⟩ : syracuseStep 2187527 = 3281291) B3281291
theorem B2460973 : Blo 2187435 2460973 := bbase (se 3 (by rfl) ⟨461432, by rfl⟩ : syracuseStep 2460973 = 922865) (by norm_num)
theorem B3281297 : Blo 2187435 3281297 := bstep (se 2 (by rfl) ⟨1230486, by rfl⟩ : syracuseStep 3281297 = 2460973) B2460973
theorem B2187531 : Blo 2187435 2187531 := bstep (se 1 (by rfl) ⟨1640648, by rfl⟩ : syracuseStep 2187531 = 3281297) B3281297
theorem B7382933 : Blo 2187435 7382933 := bbase (se 6 (by rfl) ⟨173037, by rfl⟩ : syracuseStep 7382933 = 346075) (by norm_num)
theorem B4921955 : Blo 2187435 4921955 := bstep (se 1 (by rfl) ⟨3691466, by rfl⟩ : syracuseStep 4921955 = 7382933) B7382933
theorem B3281303 : Blo 2187435 3281303 := bstep (se 1 (by rfl) ⟨2460977, by rfl⟩ : syracuseStep 3281303 = 4921955) B4921955
theorem B2187535 : Blo 2187435 2187535 := bstep (se 1 (by rfl) ⟨1640651, by rfl⟩ : syracuseStep 2187535 = 3281303) B3281303
theorem B3281309 : Blo 2187435 3281309 := bbase (se 3 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 3281309 = 1230491) (by norm_num)
theorem B2187539 : Blo 2187435 2187539 := bstep (se 1 (by rfl) ⟨1640654, by rfl⟩ : syracuseStep 2187539 = 3281309) B3281309
theorem B4921973 : Blo 2187435 4921973 := bbase (se 5 (by rfl) ⟨230717, by rfl⟩ : syracuseStep 4921973 = 461435) (by norm_num)
theorem B3281315 : Blo 2187435 3281315 := bstep (se 1 (by rfl) ⟨2460986, by rfl⟩ : syracuseStep 3281315 = 4921973) B4921973
theorem B2187543 : Blo 2187435 2187543 := bstep (se 1 (by rfl) ⟨1640657, by rfl⟩ : syracuseStep 2187543 = 3281315) B3281315
theorem B11826101 : Blo 2187435 11826101 := bbase (se 5 (by rfl) ⟨554348, by rfl⟩ : syracuseStep 11826101 = 1108697) (by norm_num)
theorem B7884067 : Blo 2187435 7884067 := bstep (se 1 (by rfl) ⟨5913050, by rfl⟩ : syracuseStep 7884067 = 11826101) B11826101
theorem B10512089 : Blo 2187435 10512089 := bstep (se 2 (by rfl) ⟨3942033, by rfl⟩ : syracuseStep 10512089 = 7884067) B7884067
theorem B7008059 : Blo 2187435 7008059 := bstep (se 1 (by rfl) ⟨5256044, by rfl⟩ : syracuseStep 7008059 = 10512089) B10512089
theorem B18688157 : Blo 2187435 18688157 := bstep (se 3 (by rfl) ⟨3504029, by rfl⟩ : syracuseStep 18688157 = 7008059) B7008059
theorem B12458771 : Blo 2187435 12458771 := bstep (se 1 (by rfl) ⟨9344078, by rfl⟩ : syracuseStep 12458771 = 18688157) B18688157
theorem B8305847 : Blo 2187435 8305847 := bstep (se 1 (by rfl) ⟨6229385, by rfl⟩ : syracuseStep 8305847 = 12458771) B12458771
theorem B5537231 : Blo 2187435 5537231 := bstep (se 1 (by rfl) ⟨4152923, by rfl⟩ : syracuseStep 5537231 = 8305847) B8305847
theorem B3691487 : Blo 2187435 3691487 := bstep (se 1 (by rfl) ⟨2768615, by rfl⟩ : syracuseStep 3691487 = 5537231) B5537231
theorem B2460991 : Blo 2187435 2460991 := bstep (se 1 (by rfl) ⟨1845743, by rfl⟩ : syracuseStep 2460991 = 3691487) B3691487
theorem B3281321 : Blo 2187435 3281321 := bstep (se 2 (by rfl) ⟨1230495, by rfl⟩ : syracuseStep 3281321 = 2460991) B2460991
theorem B2187547 : Blo 2187435 2187547 := bstep (se 1 (by rfl) ⟨1640660, by rfl⟩ : syracuseStep 2187547 = 3281321) B3281321
theorem B8305861 : Blo 2187435 8305861 := bbase (se 4 (by rfl) ⟨778674, by rfl⟩ : syracuseStep 8305861 = 1557349) (by norm_num)
theorem B11074481 : Blo 2187435 11074481 := bstep (se 2 (by rfl) ⟨4152930, by rfl⟩ : syracuseStep 11074481 = 8305861) B8305861
theorem B7382987 : Blo 2187435 7382987 := bstep (se 1 (by rfl) ⟨5537240, by rfl⟩ : syracuseStep 7382987 = 11074481) B11074481
theorem B4921991 : Blo 2187435 4921991 := bstep (se 1 (by rfl) ⟨3691493, by rfl⟩ : syracuseStep 4921991 = 7382987) B7382987
theorem B3281327 : Blo 2187435 3281327 := bstep (se 1 (by rfl) ⟨2460995, by rfl⟩ : syracuseStep 3281327 = 4921991) B4921991
theorem B2187551 : Blo 2187435 2187551 := bstep (se 1 (by rfl) ⟨1640663, by rfl⟩ : syracuseStep 2187551 = 3281327) B3281327
theorem B3281333 : Blo 2187435 3281333 := bbase (se 5 (by rfl) ⟨153812, by rfl⟩ : syracuseStep 3281333 = 307625) (by norm_num)
theorem B2187555 : Blo 2187435 2187555 := bstep (se 1 (by rfl) ⟨1640666, by rfl⟩ : syracuseStep 2187555 = 3281333) B3281333
theorem B5537261 : Blo 2187435 5537261 := bbase (se 3 (by rfl) ⟨1038236, by rfl⟩ : syracuseStep 5537261 = 2076473) (by norm_num)
theorem B3691507 : Blo 2187435 3691507 := bstep (se 1 (by rfl) ⟨2768630, by rfl⟩ : syracuseStep 3691507 = 5537261) B5537261
theorem B4922009 : Blo 2187435 4922009 := bstep (se 2 (by rfl) ⟨1845753, by rfl⟩ : syracuseStep 4922009 = 3691507) B3691507
theorem B3281339 : Blo 2187435 3281339 := bstep (se 1 (by rfl) ⟨2461004, by rfl⟩ : syracuseStep 3281339 = 4922009) B4922009
theorem B2187559 : Blo 2187435 2187559 := bstep (se 1 (by rfl) ⟨1640669, by rfl⟩ : syracuseStep 2187559 = 3281339) B3281339
theorem B2461009 : Blo 2187435 2461009 := bbase (se 2 (by rfl) ⟨922878, by rfl⟩ : syracuseStep 2461009 = 1845757) (by norm_num)
theorem B3281345 : Blo 2187435 3281345 := bstep (se 2 (by rfl) ⟨1230504, by rfl⟩ : syracuseStep 3281345 = 2461009) B2461009
theorem B2187563 : Blo 2187435 2187563 := bstep (se 1 (by rfl) ⟨1640672, by rfl⟩ : syracuseStep 2187563 = 3281345) B3281345
theorem B2336041 : Blo 2187435 2336041 := bbase (se 2 (by rfl) ⟨876015, by rfl⟩ : syracuseStep 2336041 = 1752031) (by norm_num)
theorem B3114721 : Blo 2187435 3114721 := bstep (se 2 (by rfl) ⟨1168020, by rfl⟩ : syracuseStep 3114721 = 2336041) B2336041
theorem B4152961 : Blo 2187435 4152961 := bstep (se 2 (by rfl) ⟨1557360, by rfl⟩ : syracuseStep 4152961 = 3114721) B3114721
theorem B5537281 : Blo 2187435 5537281 := bstep (se 2 (by rfl) ⟨2076480, by rfl⟩ : syracuseStep 5537281 = 4152961) B4152961
theorem B7383041 : Blo 2187435 7383041 := bstep (se 2 (by rfl) ⟨2768640, by rfl⟩ : syracuseStep 7383041 = 5537281) B5537281
theorem B4922027 : Blo 2187435 4922027 := bstep (se 1 (by rfl) ⟨3691520, by rfl⟩ : syracuseStep 4922027 = 7383041) B7383041
theorem B3281351 : Blo 2187435 3281351 := bstep (se 1 (by rfl) ⟨2461013, by rfl⟩ : syracuseStep 3281351 = 4922027) B4922027
theorem B2187567 : Blo 2187435 2187567 := bstep (se 1 (by rfl) ⟨1640675, by rfl⟩ : syracuseStep 2187567 = 3281351) B3281351
theorem B3281357 : Blo 2187435 3281357 := bbase (se 3 (by rfl) ⟨615254, by rfl⟩ : syracuseStep 3281357 = 1230509) (by norm_num)
theorem B2187571 : Blo 2187435 2187571 := bstep (se 1 (by rfl) ⟨1640678, by rfl⟩ : syracuseStep 2187571 = 3281357) B3281357
theorem B4922045 : Blo 2187435 4922045 := bbase (se 3 (by rfl) ⟨922883, by rfl⟩ : syracuseStep 4922045 = 1845767) (by norm_num)
theorem B3281363 : Blo 2187435 3281363 := bstep (se 1 (by rfl) ⟨2461022, by rfl⟩ : syracuseStep 3281363 = 4922045) B4922045
theorem B2187575 : Blo 2187435 2187575 := bstep (se 1 (by rfl) ⟨1640681, by rfl⟩ : syracuseStep 2187575 = 3281363) B3281363
theorem B3691541 : Blo 2187435 3691541 := bbase (se 6 (by rfl) ⟨86520, by rfl⟩ : syracuseStep 3691541 = 173041) (by norm_num)
theorem B2461027 : Blo 2187435 2461027 := bstep (se 1 (by rfl) ⟨1845770, by rfl⟩ : syracuseStep 2461027 = 3691541) B3691541
theorem B3281369 : Blo 2187435 3281369 := bstep (se 2 (by rfl) ⟨1230513, by rfl⟩ : syracuseStep 3281369 = 2461027) B2461027
theorem B2187579 : Blo 2187435 2187579 := bstep (se 1 (by rfl) ⟨1640684, by rfl⟩ : syracuseStep 2187579 = 3281369) B3281369
theorem B5400533 : Blo 2187435 5400533 := bbase (se 7 (by rfl) ⟨63287, by rfl⟩ : syracuseStep 5400533 = 126575) (by norm_num)
theorem B14401421 : Blo 2187435 14401421 := bstep (se 3 (by rfl) ⟨2700266, by rfl⟩ : syracuseStep 14401421 = 5400533) B5400533
theorem B9600947 : Blo 2187435 9600947 := bstep (se 1 (by rfl) ⟨7200710, by rfl⟩ : syracuseStep 9600947 = 14401421) B14401421
theorem B6400631 : Blo 2187435 6400631 := bstep (se 1 (by rfl) ⟨4800473, by rfl⟩ : syracuseStep 6400631 = 9600947) B9600947
theorem B4267087 : Blo 2187435 4267087 := bstep (se 1 (by rfl) ⟨3200315, by rfl⟩ : syracuseStep 4267087 = 6400631) B6400631
theorem B22757797 : Blo 2187435 22757797 := bstep (se 4 (by rfl) ⟨2133543, by rfl⟩ : syracuseStep 22757797 = 4267087) B4267087
theorem B30343729 : Blo 2187435 30343729 := bstep (se 2 (by rfl) ⟨11378898, by rfl⟩ : syracuseStep 30343729 = 22757797) B22757797
theorem B40458305 : Blo 2187435 40458305 := bstep (se 2 (by rfl) ⟨15171864, by rfl⟩ : syracuseStep 40458305 = 30343729) B30343729
theorem B26972203 : Blo 2187435 26972203 := bstep (se 1 (by rfl) ⟨20229152, by rfl⟩ : syracuseStep 26972203 = 40458305) B40458305
theorem B35962937 : Blo 2187435 35962937 := bstep (se 2 (by rfl) ⟨13486101, by rfl⟩ : syracuseStep 35962937 = 26972203) B26972203
theorem B23975291 : Blo 2187435 23975291 := bstep (se 1 (by rfl) ⟨17981468, by rfl⟩ : syracuseStep 23975291 = 35962937) B35962937
theorem B15983527 : Blo 2187435 15983527 := bstep (se 1 (by rfl) ⟨11987645, by rfl⟩ : syracuseStep 15983527 = 23975291) B23975291
theorem B21311369 : Blo 2187435 21311369 := bstep (se 2 (by rfl) ⟨7991763, by rfl⟩ : syracuseStep 21311369 = 15983527) B15983527
theorem B14207579 : Blo 2187435 14207579 := bstep (se 1 (by rfl) ⟨10655684, by rfl⟩ : syracuseStep 14207579 = 21311369) B21311369
theorem B9471719 : Blo 2187435 9471719 := bstep (se 1 (by rfl) ⟨7103789, by rfl⟩ : syracuseStep 9471719 = 14207579) B14207579
theorem B6314479 : Blo 2187435 6314479 := bstep (se 1 (by rfl) ⟨4735859, by rfl⟩ : syracuseStep 6314479 = 9471719) B9471719
theorem B33677221 : Blo 2187435 33677221 := bstep (se 4 (by rfl) ⟨3157239, by rfl⟩ : syracuseStep 33677221 = 6314479) B6314479
theorem B44902961 : Blo 2187435 44902961 := bstep (se 2 (by rfl) ⟨16838610, by rfl⟩ : syracuseStep 44902961 = 33677221) B33677221
theorem B29935307 : Blo 2187435 29935307 := bstep (se 1 (by rfl) ⟨22451480, by rfl⟩ : syracuseStep 29935307 = 44902961) B44902961
theorem B19956871 : Blo 2187435 19956871 := bstep (se 1 (by rfl) ⟨14967653, by rfl⟩ : syracuseStep 19956871 = 29935307) B29935307
theorem B26609161 : Blo 2187435 26609161 := bstep (se 2 (by rfl) ⟨9978435, by rfl⟩ : syracuseStep 26609161 = 19956871) B19956871
theorem B35478881 : Blo 2187435 35478881 := bstep (se 2 (by rfl) ⟨13304580, by rfl⟩ : syracuseStep 35478881 = 26609161) B26609161
theorem B23652587 : Blo 2187435 23652587 := bstep (se 1 (by rfl) ⟨17739440, by rfl⟩ : syracuseStep 23652587 = 35478881) B35478881
theorem B15768391 : Blo 2187435 15768391 := bstep (se 1 (by rfl) ⟨11826293, by rfl⟩ : syracuseStep 15768391 = 23652587) B23652587
theorem B21024521 : Blo 2187435 21024521 := bstep (se 2 (by rfl) ⟨7884195, by rfl⟩ : syracuseStep 21024521 = 15768391) B15768391
theorem B14016347 : Blo 2187435 14016347 := bstep (se 1 (by rfl) ⟨10512260, by rfl⟩ : syracuseStep 14016347 = 21024521) B21024521
theorem B9344231 : Blo 2187435 9344231 := bstep (se 1 (by rfl) ⟨7008173, by rfl⟩ : syracuseStep 9344231 = 14016347) B14016347
theorem B6229487 : Blo 2187435 6229487 := bstep (se 1 (by rfl) ⟨4672115, by rfl⟩ : syracuseStep 6229487 = 9344231) B9344231
theorem B16611965 : Blo 2187435 16611965 := bstep (se 3 (by rfl) ⟨3114743, by rfl⟩ : syracuseStep 16611965 = 6229487) B6229487
theorem B11074643 : Blo 2187435 11074643 := bstep (se 1 (by rfl) ⟨8305982, by rfl⟩ : syracuseStep 11074643 = 16611965) B16611965
theorem B7383095 : Blo 2187435 7383095 := bstep (se 1 (by rfl) ⟨5537321, by rfl⟩ : syracuseStep 7383095 = 11074643) B11074643
theorem B4922063 : Blo 2187435 4922063 := bstep (se 1 (by rfl) ⟨3691547, by rfl⟩ : syracuseStep 4922063 = 7383095) B7383095
theorem B3281375 : Blo 2187435 3281375 := bstep (se 1 (by rfl) ⟨2461031, by rfl⟩ : syracuseStep 3281375 = 4922063) B4922063
theorem B2187583 : Blo 2187435 2187583 := bstep (se 1 (by rfl) ⟨1640687, by rfl⟩ : syracuseStep 2187583 = 3281375) B3281375
theorem B3281381 : Blo 2187435 3281381 := bbase (se 4 (by rfl) ⟨307629, by rfl⟩ : syracuseStep 3281381 = 615259) (by norm_num)
theorem B2187587 : Blo 2187435 2187587 := bstep (se 1 (by rfl) ⟨1640690, by rfl⟩ : syracuseStep 2187587 = 3281381) B3281381
theorem B2663933 : Blo 2187435 2663933 := bbase (se 3 (by rfl) ⟨499487, by rfl⟩ : syracuseStep 2663933 = 998975) (by norm_num)
theorem B7103821 : Blo 2187435 7103821 := bstep (se 3 (by rfl) ⟨1331966, by rfl⟩ : syracuseStep 7103821 = 2663933) B2663933
theorem B9471761 : Blo 2187435 9471761 := bstep (se 2 (by rfl) ⟨3551910, by rfl⟩ : syracuseStep 9471761 = 7103821) B7103821
theorem B6314507 : Blo 2187435 6314507 := bstep (se 1 (by rfl) ⟨4735880, by rfl⟩ : syracuseStep 6314507 = 9471761) B9471761
theorem B4209671 : Blo 2187435 4209671 := bstep (se 1 (by rfl) ⟨3157253, by rfl⟩ : syracuseStep 4209671 = 6314507) B6314507
theorem B11225789 : Blo 2187435 11225789 := bstep (se 3 (by rfl) ⟨2104835, by rfl⟩ : syracuseStep 11225789 = 4209671) B4209671
theorem B7483859 : Blo 2187435 7483859 := bstep (se 1 (by rfl) ⟨5612894, by rfl⟩ : syracuseStep 7483859 = 11225789) B11225789
theorem B4989239 : Blo 2187435 4989239 := bstep (se 1 (by rfl) ⟨3741929, by rfl⟩ : syracuseStep 4989239 = 7483859) B7483859
theorem B3326159 : Blo 2187435 3326159 := bstep (se 1 (by rfl) ⟨2494619, by rfl⟩ : syracuseStep 3326159 = 4989239) B4989239
theorem B2217439 : Blo 2187435 2217439 := bstep (se 1 (by rfl) ⟨1663079, by rfl⟩ : syracuseStep 2217439 = 3326159) B3326159
theorem B2956585 : Blo 2187435 2956585 := bstep (se 2 (by rfl) ⟨1108719, by rfl⟩ : syracuseStep 2956585 = 2217439) B2217439
theorem B3942113 : Blo 2187435 3942113 := bstep (se 2 (by rfl) ⟨1478292, by rfl⟩ : syracuseStep 3942113 = 2956585) B2956585
theorem B10512301 : Blo 2187435 10512301 := bstep (se 3 (by rfl) ⟨1971056, by rfl⟩ : syracuseStep 10512301 = 3942113) B3942113
theorem B14016401 : Blo 2187435 14016401 := bstep (se 2 (by rfl) ⟨5256150, by rfl⟩ : syracuseStep 14016401 = 10512301) B10512301
theorem B9344267 : Blo 2187435 9344267 := bstep (se 1 (by rfl) ⟨7008200, by rfl⟩ : syracuseStep 9344267 = 14016401) B14016401
theorem B6229511 : Blo 2187435 6229511 := bstep (se 1 (by rfl) ⟨4672133, by rfl⟩ : syracuseStep 6229511 = 9344267) B9344267
theorem B4153007 : Blo 2187435 4153007 := bstep (se 1 (by rfl) ⟨3114755, by rfl⟩ : syracuseStep 4153007 = 6229511) B6229511
theorem B2768671 : Blo 2187435 2768671 := bstep (se 1 (by rfl) ⟨2076503, by rfl⟩ : syracuseStep 2768671 = 4153007) B4153007
theorem B3691561 : Blo 2187435 3691561 := bstep (se 2 (by rfl) ⟨1384335, by rfl⟩ : syracuseStep 3691561 = 2768671) B2768671
theorem B4922081 : Blo 2187435 4922081 := bstep (se 2 (by rfl) ⟨1845780, by rfl⟩ : syracuseStep 4922081 = 3691561) B3691561
theorem B3281387 : Blo 2187435 3281387 := bstep (se 1 (by rfl) ⟨2461040, by rfl⟩ : syracuseStep 3281387 = 4922081) B4922081
theorem B2187591 : Blo 2187435 2187591 := bstep (se 1 (by rfl) ⟨1640693, by rfl⟩ : syracuseStep 2187591 = 3281387) B3281387
theorem B2461045 : Blo 2187435 2461045 := bbase (se 5 (by rfl) ⟨115361, by rfl⟩ : syracuseStep 2461045 = 230723) (by norm_num)
theorem B3281393 : Blo 2187435 3281393 := bstep (se 2 (by rfl) ⟨1230522, by rfl⟩ : syracuseStep 3281393 = 2461045) B2461045
theorem B2187595 : Blo 2187435 2187595 := bstep (se 1 (by rfl) ⟨1640696, by rfl⟩ : syracuseStep 2187595 = 3281393) B3281393
theorem B2768681 : Blo 2187435 2768681 := bbase (se 2 (by rfl) ⟨1038255, by rfl⟩ : syracuseStep 2768681 = 2076511) (by norm_num)
theorem B7383149 : Blo 2187435 7383149 := bstep (se 3 (by rfl) ⟨1384340, by rfl⟩ : syracuseStep 7383149 = 2768681) B2768681
theorem B4922099 : Blo 2187435 4922099 := bstep (se 1 (by rfl) ⟨3691574, by rfl⟩ : syracuseStep 4922099 = 7383149) B7383149
theorem B3281399 : Blo 2187435 3281399 := bstep (se 1 (by rfl) ⟨2461049, by rfl⟩ : syracuseStep 3281399 = 4922099) B4922099
theorem B2187599 : Blo 2187435 2187599 := bstep (se 1 (by rfl) ⟨1640699, by rfl⟩ : syracuseStep 2187599 = 3281399) B3281399
theorem B3281405 : Blo 2187435 3281405 := bbase (se 3 (by rfl) ⟨615263, by rfl⟩ : syracuseStep 3281405 = 1230527) (by norm_num)
theorem B2187603 : Blo 2187435 2187603 := bstep (se 1 (by rfl) ⟨1640702, by rfl⟩ : syracuseStep 2187603 = 3281405) B3281405
theorem B4922117 : Blo 2187435 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B3281411 : Blo 2187435 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B2187607 : Blo 2187435 2187607 := bstep (se 1 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 2187607 = 3281411) B3281411
theorem B4153045 : Blo 2187435 4153045 := bbase (se 7 (by rfl) ⟨48668, by rfl⟩ : syracuseStep 4153045 = 97337) (by norm_num)
theorem B5537393 : Blo 2187435 5537393 := bstep (se 2 (by rfl) ⟨2076522, by rfl⟩ : syracuseStep 5537393 = 4153045) B4153045
theorem B3691595 : Blo 2187435 3691595 := bstep (se 1 (by rfl) ⟨2768696, by rfl⟩ : syracuseStep 3691595 = 5537393) B5537393
theorem B2461063 : Blo 2187435 2461063 := bstep (se 1 (by rfl) ⟨1845797, by rfl⟩ : syracuseStep 2461063 = 3691595) B3691595
theorem B3281417 : Blo 2187435 3281417 := bstep (se 2 (by rfl) ⟨1230531, by rfl⟩ : syracuseStep 3281417 = 2461063) B2461063
theorem B2187611 : Blo 2187435 2187611 := bstep (se 1 (by rfl) ⟨1640708, by rfl⟩ : syracuseStep 2187611 = 3281417) B3281417
theorem B11074805 : Blo 2187435 11074805 := bbase (se 5 (by rfl) ⟨519131, by rfl⟩ : syracuseStep 11074805 = 1038263) (by norm_num)
theorem B7383203 : Blo 2187435 7383203 := bstep (se 1 (by rfl) ⟨5537402, by rfl⟩ : syracuseStep 7383203 = 11074805) B11074805
theorem B4922135 : Blo 2187435 4922135 := bstep (se 1 (by rfl) ⟨3691601, by rfl⟩ : syracuseStep 4922135 = 7383203) B7383203
theorem B3281423 : Blo 2187435 3281423 := bstep (se 1 (by rfl) ⟨2461067, by rfl⟩ : syracuseStep 3281423 = 4922135) B4922135
theorem B2187615 : Blo 2187435 2187615 := bstep (se 1 (by rfl) ⟨1640711, by rfl⟩ : syracuseStep 2187615 = 3281423) B3281423
theorem B3281429 : Blo 2187435 3281429 := bbase (se 6 (by rfl) ⟨76908, by rfl⟩ : syracuseStep 3281429 = 153817) (by norm_num)
theorem B2187619 : Blo 2187435 2187619 := bstep (se 1 (by rfl) ⟨1640714, by rfl⟩ : syracuseStep 2187619 = 3281429) B3281429
theorem B7884341 : Blo 2187435 7884341 := bbase (se 5 (by rfl) ⟨369578, by rfl⟩ : syracuseStep 7884341 = 739157) (by norm_num)
theorem B5256227 : Blo 2187435 5256227 := bstep (se 1 (by rfl) ⟨3942170, by rfl⟩ : syracuseStep 5256227 = 7884341) B7884341
theorem B3504151 : Blo 2187435 3504151 := bstep (se 1 (by rfl) ⟨2628113, by rfl⟩ : syracuseStep 3504151 = 5256227) B5256227
theorem B18688805 : Blo 2187435 18688805 := bstep (se 4 (by rfl) ⟨1752075, by rfl⟩ : syracuseStep 18688805 = 3504151) B3504151
theorem B12459203 : Blo 2187435 12459203 := bstep (se 1 (by rfl) ⟨9344402, by rfl⟩ : syracuseStep 12459203 = 18688805) B18688805
theorem B8306135 : Blo 2187435 8306135 := bstep (se 1 (by rfl) ⟨6229601, by rfl⟩ : syracuseStep 8306135 = 12459203) B12459203
theorem B5537423 : Blo 2187435 5537423 := bstep (se 1 (by rfl) ⟨4153067, by rfl⟩ : syracuseStep 5537423 = 8306135) B8306135
theorem B3691615 : Blo 2187435 3691615 := bstep (se 1 (by rfl) ⟨2768711, by rfl⟩ : syracuseStep 3691615 = 5537423) B5537423
theorem B4922153 : Blo 2187435 4922153 := bstep (se 2 (by rfl) ⟨1845807, by rfl⟩ : syracuseStep 4922153 = 3691615) B3691615
theorem B3281435 : Blo 2187435 3281435 := bstep (se 1 (by rfl) ⟨2461076, by rfl⟩ : syracuseStep 3281435 = 4922153) B4922153
theorem B2187623 : Blo 2187435 2187623 := bstep (se 1 (by rfl) ⟨1640717, by rfl⟩ : syracuseStep 2187623 = 3281435) B3281435
theorem B2461081 : Blo 2187435 2461081 := bbase (se 2 (by rfl) ⟨922905, by rfl⟩ : syracuseStep 2461081 = 1845811) (by norm_num)
theorem B3281441 : Blo 2187435 3281441 := bstep (se 2 (by rfl) ⟨1230540, by rfl⟩ : syracuseStep 3281441 = 2461081) B2461081
theorem B2187627 : Blo 2187435 2187627 := bstep (se 1 (by rfl) ⟨1640720, by rfl⟩ : syracuseStep 2187627 = 3281441) B3281441
theorem B8306165 : Blo 2187435 8306165 := bbase (se 5 (by rfl) ⟨389351, by rfl⟩ : syracuseStep 8306165 = 778703) (by norm_num)
theorem B5537443 : Blo 2187435 5537443 := bstep (se 1 (by rfl) ⟨4153082, by rfl⟩ : syracuseStep 5537443 = 8306165) B8306165
theorem B7383257 : Blo 2187435 7383257 := bstep (se 2 (by rfl) ⟨2768721, by rfl⟩ : syracuseStep 7383257 = 5537443) B5537443
theorem B4922171 : Blo 2187435 4922171 := bstep (se 1 (by rfl) ⟨3691628, by rfl⟩ : syracuseStep 4922171 = 7383257) B7383257
theorem B3281447 : Blo 2187435 3281447 := bstep (se 1 (by rfl) ⟨2461085, by rfl⟩ : syracuseStep 3281447 = 4922171) B4922171
theorem B2187631 : Blo 2187435 2187631 := bstep (se 1 (by rfl) ⟨1640723, by rfl⟩ : syracuseStep 2187631 = 3281447) B3281447
theorem B3281453 : Blo 2187435 3281453 := bbase (se 3 (by rfl) ⟨615272, by rfl⟩ : syracuseStep 3281453 = 1230545) (by norm_num)
theorem B2187635 : Blo 2187435 2187635 := bstep (se 1 (by rfl) ⟨1640726, by rfl⟩ : syracuseStep 2187635 = 3281453) B3281453
theorem B4922189 : Blo 2187435 4922189 := bbase (se 3 (by rfl) ⟨922910, by rfl⟩ : syracuseStep 4922189 = 1845821) (by norm_num)
theorem B3281459 : Blo 2187435 3281459 := bstep (se 1 (by rfl) ⟨2461094, by rfl⟩ : syracuseStep 3281459 = 4922189) B4922189
theorem B2187639 : Blo 2187435 2187639 := bstep (se 1 (by rfl) ⟨1640729, by rfl⟩ : syracuseStep 2187639 = 3281459) B3281459
theorem B2768737 : Blo 2187435 2768737 := bbase (se 2 (by rfl) ⟨1038276, by rfl⟩ : syracuseStep 2768737 = 2076553) (by norm_num)
theorem B3691649 : Blo 2187435 3691649 := bstep (se 2 (by rfl) ⟨1384368, by rfl⟩ : syracuseStep 3691649 = 2768737) B2768737
theorem B2461099 : Blo 2187435 2461099 := bstep (se 1 (by rfl) ⟨1845824, by rfl⟩ : syracuseStep 2461099 = 3691649) B3691649
theorem B3281465 : Blo 2187435 3281465 := bstep (se 2 (by rfl) ⟨1230549, by rfl⟩ : syracuseStep 3281465 = 2461099) B2461099
theorem B2187643 : Blo 2187435 2187643 := bstep (se 1 (by rfl) ⟨1640732, by rfl⟩ : syracuseStep 2187643 = 3281465) B3281465
theorem B24918677 : Blo 2187435 24918677 := bbase (se 6 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 24918677 = 1168063) (by norm_num)
theorem B16612451 : Blo 2187435 16612451 := bstep (se 1 (by rfl) ⟨12459338, by rfl⟩ : syracuseStep 16612451 = 24918677) B24918677
theorem B11074967 : Blo 2187435 11074967 := bstep (se 1 (by rfl) ⟨8306225, by rfl⟩ : syracuseStep 11074967 = 16612451) B16612451
theorem B7383311 : Blo 2187435 7383311 := bstep (se 1 (by rfl) ⟨5537483, by rfl⟩ : syracuseStep 7383311 = 11074967) B11074967
theorem B4922207 : Blo 2187435 4922207 := bstep (se 1 (by rfl) ⟨3691655, by rfl⟩ : syracuseStep 4922207 = 7383311) B7383311
theorem B3281471 : Blo 2187435 3281471 := bstep (se 1 (by rfl) ⟨2461103, by rfl⟩ : syracuseStep 3281471 = 4922207) B4922207
theorem B2187647 : Blo 2187435 2187647 := bstep (se 1 (by rfl) ⟨1640735, by rfl⟩ : syracuseStep 2187647 = 3281471) B3281471
theorem B3281477 : Blo 2187435 3281477 := bbase (se 4 (by rfl) ⟨307638, by rfl⟩ : syracuseStep 3281477 = 615277) (by norm_num)
theorem B2187651 : Blo 2187435 2187651 := bstep (se 1 (by rfl) ⟨1640738, by rfl⟩ : syracuseStep 2187651 = 3281477) B3281477
theorem B3691669 : Blo 2187435 3691669 := bbase (se 6 (by rfl) ⟨86523, by rfl⟩ : syracuseStep 3691669 = 173047) (by norm_num)
theorem B4922225 : Blo 2187435 4922225 := bstep (se 2 (by rfl) ⟨1845834, by rfl⟩ : syracuseStep 4922225 = 3691669) B3691669
theorem B3281483 : Blo 2187435 3281483 := bstep (se 1 (by rfl) ⟨2461112, by rfl⟩ : syracuseStep 3281483 = 4922225) B4922225
theorem B2187655 : Blo 2187435 2187655 := bstep (se 1 (by rfl) ⟨1640741, by rfl⟩ : syracuseStep 2187655 = 3281483) B3281483
theorem B2461117 : Blo 2187435 2461117 := bbase (se 3 (by rfl) ⟨461459, by rfl⟩ : syracuseStep 2461117 = 922919) (by norm_num)
theorem B3281489 : Blo 2187435 3281489 := bstep (se 2 (by rfl) ⟨1230558, by rfl⟩ : syracuseStep 3281489 = 2461117) B2461117
theorem B2187659 : Blo 2187435 2187659 := bstep (se 1 (by rfl) ⟨1640744, by rfl⟩ : syracuseStep 2187659 = 3281489) B3281489
theorem B7383365 : Blo 2187435 7383365 := bbase (se 4 (by rfl) ⟨692190, by rfl⟩ : syracuseStep 7383365 = 1384381) (by norm_num)
theorem B4922243 : Blo 2187435 4922243 := bstep (se 1 (by rfl) ⟨3691682, by rfl⟩ : syracuseStep 4922243 = 7383365) B7383365
theorem B3281495 : Blo 2187435 3281495 := bstep (se 1 (by rfl) ⟨2461121, by rfl⟩ : syracuseStep 3281495 = 4922243) B4922243
theorem B2187663 : Blo 2187435 2187663 := bstep (se 1 (by rfl) ⟨1640747, by rfl⟩ : syracuseStep 2187663 = 3281495) B3281495
theorem B3281501 : Blo 2187435 3281501 := bbase (se 3 (by rfl) ⟨615281, by rfl⟩ : syracuseStep 3281501 = 1230563) (by norm_num)
theorem B2187667 : Blo 2187435 2187667 := bstep (se 1 (by rfl) ⟨1640750, by rfl⟩ : syracuseStep 2187667 = 3281501) B3281501
theorem B4922261 : Blo 2187435 4922261 := bbase (se 6 (by rfl) ⟨115365, by rfl⟩ : syracuseStep 4922261 = 230731) (by norm_num)
theorem B3281507 : Blo 2187435 3281507 := bstep (se 1 (by rfl) ⟨2461130, by rfl⟩ : syracuseStep 3281507 = 4922261) B4922261
theorem B2187671 : Blo 2187435 2187671 := bstep (se 1 (by rfl) ⟨1640753, by rfl⟩ : syracuseStep 2187671 = 3281507) B3281507
theorem B2528753 : Blo 2187435 2528753 := bbase (se 2 (by rfl) ⟨948282, by rfl⟩ : syracuseStep 2528753 = 1896565) (by norm_num)
theorem B6743341 : Blo 2187435 6743341 := bstep (se 3 (by rfl) ⟨1264376, by rfl⟩ : syracuseStep 6743341 = 2528753) B2528753
theorem B35964485 : Blo 2187435 35964485 := bstep (se 4 (by rfl) ⟨3371670, by rfl⟩ : syracuseStep 35964485 = 6743341) B6743341
theorem B23976323 : Blo 2187435 23976323 := bstep (se 1 (by rfl) ⟨17982242, by rfl⟩ : syracuseStep 23976323 = 35964485) B35964485
theorem B15984215 : Blo 2187435 15984215 := bstep (se 1 (by rfl) ⟨11988161, by rfl⟩ : syracuseStep 15984215 = 23976323) B23976323
theorem B10656143 : Blo 2187435 10656143 := bstep (se 1 (by rfl) ⟨7992107, by rfl⟩ : syracuseStep 10656143 = 15984215) B15984215
theorem B7104095 : Blo 2187435 7104095 := bstep (se 1 (by rfl) ⟨5328071, by rfl⟩ : syracuseStep 7104095 = 10656143) B10656143
theorem B4736063 : Blo 2187435 4736063 := bstep (se 1 (by rfl) ⟨3552047, by rfl⟩ : syracuseStep 4736063 = 7104095) B7104095
theorem B3157375 : Blo 2187435 3157375 := bstep (se 1 (by rfl) ⟨2368031, by rfl⟩ : syracuseStep 3157375 = 4736063) B4736063
theorem B4209833 : Blo 2187435 4209833 := bstep (se 2 (by rfl) ⟨1578687, by rfl⟩ : syracuseStep 4209833 = 3157375) B3157375
theorem B11226221 : Blo 2187435 11226221 := bstep (se 3 (by rfl) ⟨2104916, by rfl⟩ : syracuseStep 11226221 = 4209833) B4209833
theorem B7484147 : Blo 2187435 7484147 := bstep (se 1 (by rfl) ⟨5613110, by rfl⟩ : syracuseStep 7484147 = 11226221) B11226221
theorem B4989431 : Blo 2187435 4989431 := bstep (se 1 (by rfl) ⟨3742073, by rfl⟩ : syracuseStep 4989431 = 7484147) B7484147
theorem B3326287 : Blo 2187435 3326287 := bstep (se 1 (by rfl) ⟨2494715, by rfl⟩ : syracuseStep 3326287 = 4989431) B4989431
theorem B4435049 : Blo 2187435 4435049 := bstep (se 2 (by rfl) ⟨1663143, by rfl⟩ : syracuseStep 4435049 = 3326287) B3326287
theorem B2956699 : Blo 2187435 2956699 := bstep (se 1 (by rfl) ⟨2217524, by rfl⟩ : syracuseStep 2956699 = 4435049) B4435049
theorem B3942265 : Blo 2187435 3942265 := bstep (se 2 (by rfl) ⟨1478349, by rfl⟩ : syracuseStep 3942265 = 2956699) B2956699
theorem B5256353 : Blo 2187435 5256353 := bstep (se 2 (by rfl) ⟨1971132, by rfl⟩ : syracuseStep 5256353 = 3942265) B3942265
theorem B3504235 : Blo 2187435 3504235 := bstep (se 1 (by rfl) ⟨2628176, by rfl⟩ : syracuseStep 3504235 = 5256353) B5256353
theorem B4672313 : Blo 2187435 4672313 := bstep (se 2 (by rfl) ⟨1752117, by rfl⟩ : syracuseStep 4672313 = 3504235) B3504235
theorem B3114875 : Blo 2187435 3114875 := bstep (se 1 (by rfl) ⟨2336156, by rfl⟩ : syracuseStep 3114875 = 4672313) B4672313
theorem B8306333 : Blo 2187435 8306333 := bstep (se 3 (by rfl) ⟨1557437, by rfl⟩ : syracuseStep 8306333 = 3114875) B3114875
theorem B5537555 : Blo 2187435 5537555 := bstep (se 1 (by rfl) ⟨4153166, by rfl⟩ : syracuseStep 5537555 = 8306333) B8306333
theorem B3691703 : Blo 2187435 3691703 := bstep (se 1 (by rfl) ⟨2768777, by rfl⟩ : syracuseStep 3691703 = 5537555) B5537555
theorem B2461135 : Blo 2187435 2461135 := bstep (se 1 (by rfl) ⟨1845851, by rfl⟩ : syracuseStep 2461135 = 3691703) B3691703
theorem B3281513 : Blo 2187435 3281513 := bstep (se 2 (by rfl) ⟨1230567, by rfl⟩ : syracuseStep 3281513 = 2461135) B2461135
theorem B2187675 : Blo 2187435 2187675 := bstep (se 1 (by rfl) ⟨1640756, by rfl⟩ : syracuseStep 2187675 = 3281513) B3281513
theorem B5328077 : Blo 2187435 5328077 := bbase (se 3 (by rfl) ⟨999014, by rfl⟩ : syracuseStep 5328077 = 1998029) (by norm_num)
theorem B14208205 : Blo 2187435 14208205 := bstep (se 3 (by rfl) ⟨2664038, by rfl⟩ : syracuseStep 14208205 = 5328077) B5328077
theorem B18944273 : Blo 2187435 18944273 := bstep (se 2 (by rfl) ⟨7104102, by rfl⟩ : syracuseStep 18944273 = 14208205) B14208205
theorem B12629515 : Blo 2187435 12629515 := bstep (se 1 (by rfl) ⟨9472136, by rfl⟩ : syracuseStep 12629515 = 18944273) B18944273
theorem B16839353 : Blo 2187435 16839353 := bstep (se 2 (by rfl) ⟨6314757, by rfl⟩ : syracuseStep 16839353 = 12629515) B12629515
theorem B44904941 : Blo 2187435 44904941 := bstep (se 3 (by rfl) ⟨8419676, by rfl⟩ : syracuseStep 44904941 = 16839353) B16839353
theorem B29936627 : Blo 2187435 29936627 := bstep (se 1 (by rfl) ⟨22452470, by rfl⟩ : syracuseStep 29936627 = 44904941) B44904941
theorem B19957751 : Blo 2187435 19957751 := bstep (se 1 (by rfl) ⟨14968313, by rfl⟩ : syracuseStep 19957751 = 29936627) B29936627
theorem B13305167 : Blo 2187435 13305167 := bstep (se 1 (by rfl) ⟨9978875, by rfl⟩ : syracuseStep 13305167 = 19957751) B19957751
theorem B8870111 : Blo 2187435 8870111 := bstep (se 1 (by rfl) ⟨6652583, by rfl⟩ : syracuseStep 8870111 = 13305167) B13305167
theorem B5913407 : Blo 2187435 5913407 := bstep (se 1 (by rfl) ⟨4435055, by rfl⟩ : syracuseStep 5913407 = 8870111) B8870111
theorem B3942271 : Blo 2187435 3942271 := bstep (se 1 (by rfl) ⟨2956703, by rfl⟩ : syracuseStep 3942271 = 5913407) B5913407
theorem B5256361 : Blo 2187435 5256361 := bstep (se 2 (by rfl) ⟨1971135, by rfl⟩ : syracuseStep 5256361 = 3942271) B3942271
theorem B7008481 : Blo 2187435 7008481 := bstep (se 2 (by rfl) ⟨2628180, by rfl⟩ : syracuseStep 7008481 = 5256361) B5256361
theorem B9344641 : Blo 2187435 9344641 := bstep (se 2 (by rfl) ⟨3504240, by rfl⟩ : syracuseStep 9344641 = 7008481) B7008481
theorem B12459521 : Blo 2187435 12459521 := bstep (se 2 (by rfl) ⟨4672320, by rfl⟩ : syracuseStep 12459521 = 9344641) B9344641
theorem B8306347 : Blo 2187435 8306347 := bstep (se 1 (by rfl) ⟨6229760, by rfl⟩ : syracuseStep 8306347 = 12459521) B12459521
theorem B11075129 : Blo 2187435 11075129 := bstep (se 2 (by rfl) ⟨4153173, by rfl⟩ : syracuseStep 11075129 = 8306347) B8306347
theorem B7383419 : Blo 2187435 7383419 := bstep (se 1 (by rfl) ⟨5537564, by rfl⟩ : syracuseStep 7383419 = 11075129) B11075129
theorem B4922279 : Blo 2187435 4922279 := bstep (se 1 (by rfl) ⟨3691709, by rfl⟩ : syracuseStep 4922279 = 7383419) B7383419
theorem B3281519 : Blo 2187435 3281519 := bstep (se 1 (by rfl) ⟨2461139, by rfl⟩ : syracuseStep 3281519 = 4922279) B4922279
theorem B2187679 : Blo 2187435 2187679 := bstep (se 1 (by rfl) ⟨1640759, by rfl⟩ : syracuseStep 2187679 = 3281519) B3281519
theorem B3281525 : Blo 2187435 3281525 := bbase (se 5 (by rfl) ⟨153821, by rfl⟩ : syracuseStep 3281525 = 307643) (by norm_num)
theorem B2187683 : Blo 2187435 2187683 := bstep (se 1 (by rfl) ⟨1640762, by rfl⟩ : syracuseStep 2187683 = 3281525) B3281525
theorem B4153189 : Blo 2187435 4153189 := bbase (se 4 (by rfl) ⟨389361, by rfl⟩ : syracuseStep 4153189 = 778723) (by norm_num)
theorem B5537585 : Blo 2187435 5537585 := bstep (se 2 (by rfl) ⟨2076594, by rfl⟩ : syracuseStep 5537585 = 4153189) B4153189
theorem B3691723 : Blo 2187435 3691723 := bstep (se 1 (by rfl) ⟨2768792, by rfl⟩ : syracuseStep 3691723 = 5537585) B5537585
theorem B4922297 : Blo 2187435 4922297 := bstep (se 2 (by rfl) ⟨1845861, by rfl⟩ : syracuseStep 4922297 = 3691723) B3691723
theorem B3281531 : Blo 2187435 3281531 := bstep (se 1 (by rfl) ⟨2461148, by rfl⟩ : syracuseStep 3281531 = 4922297) B4922297
theorem B2187687 : Blo 2187435 2187687 := bstep (se 1 (by rfl) ⟨1640765, by rfl⟩ : syracuseStep 2187687 = 3281531) B3281531
theorem B2461153 : Blo 2187435 2461153 := bbase (se 2 (by rfl) ⟨922932, by rfl⟩ : syracuseStep 2461153 = 1845865) (by norm_num)
theorem B3281537 : Blo 2187435 3281537 := bstep (se 2 (by rfl) ⟨1230576, by rfl⟩ : syracuseStep 3281537 = 2461153) B2461153
theorem B2187691 : Blo 2187435 2187691 := bstep (se 1 (by rfl) ⟨1640768, by rfl⟩ : syracuseStep 2187691 = 3281537) B3281537
theorem B5537605 : Blo 2187435 5537605 := bbase (se 4 (by rfl) ⟨519150, by rfl⟩ : syracuseStep 5537605 = 1038301) (by norm_num)
theorem B7383473 : Blo 2187435 7383473 := bstep (se 2 (by rfl) ⟨2768802, by rfl⟩ : syracuseStep 7383473 = 5537605) B5537605
theorem B4922315 : Blo 2187435 4922315 := bstep (se 1 (by rfl) ⟨3691736, by rfl⟩ : syracuseStep 4922315 = 7383473) B7383473
theorem B3281543 : Blo 2187435 3281543 := bstep (se 1 (by rfl) ⟨2461157, by rfl⟩ : syracuseStep 3281543 = 4922315) B4922315
theorem B2187695 : Blo 2187435 2187695 := bstep (se 1 (by rfl) ⟨1640771, by rfl⟩ : syracuseStep 2187695 = 3281543) B3281543
theorem B3281549 : Blo 2187435 3281549 := bbase (se 3 (by rfl) ⟨615290, by rfl⟩ : syracuseStep 3281549 = 1230581) (by norm_num)
theorem B2187699 : Blo 2187435 2187699 := bstep (se 1 (by rfl) ⟨1640774, by rfl⟩ : syracuseStep 2187699 = 3281549) B3281549
theorem B4922333 : Blo 2187435 4922333 := bbase (se 3 (by rfl) ⟨922937, by rfl⟩ : syracuseStep 4922333 = 1845875) (by norm_num)
theorem B3281555 : Blo 2187435 3281555 := bstep (se 1 (by rfl) ⟨2461166, by rfl⟩ : syracuseStep 3281555 = 4922333) B4922333
theorem B2187703 : Blo 2187435 2187703 := bstep (se 1 (by rfl) ⟨1640777, by rfl⟩ : syracuseStep 2187703 = 3281555) B3281555
theorem B3691757 : Blo 2187435 3691757 := bbase (se 3 (by rfl) ⟨692204, by rfl⟩ : syracuseStep 3691757 = 1384409) (by norm_num)
theorem B2461171 : Blo 2187435 2461171 := bstep (se 1 (by rfl) ⟨1845878, by rfl⟩ : syracuseStep 2461171 = 3691757) B3691757
theorem B3281561 : Blo 2187435 3281561 := bstep (se 2 (by rfl) ⟨1230585, by rfl⟩ : syracuseStep 3281561 = 2461171) B2461171
theorem B2187707 : Blo 2187435 2187707 := bstep (se 1 (by rfl) ⟨1640780, by rfl⟩ : syracuseStep 2187707 = 3281561) B3281561
theorem B4619141 : Blo 2187435 4619141 := bbase (se 4 (by rfl) ⟨433044, by rfl⟩ : syracuseStep 4619141 = 866089) (by norm_num)
theorem B3079427 : Blo 2187435 3079427 := bstep (se 1 (by rfl) ⟨2309570, by rfl⟩ : syracuseStep 3079427 = 4619141) B4619141
theorem B32847221 : Blo 2187435 32847221 := bstep (se 5 (by rfl) ⟨1539713, by rfl⟩ : syracuseStep 32847221 = 3079427) B3079427
theorem B21898147 : Blo 2187435 21898147 := bstep (se 1 (by rfl) ⟨16423610, by rfl⟩ : syracuseStep 21898147 = 32847221) B32847221
theorem B29197529 : Blo 2187435 29197529 := bstep (se 2 (by rfl) ⟨10949073, by rfl⟩ : syracuseStep 29197529 = 21898147) B21898147
theorem B19465019 : Blo 2187435 19465019 := bstep (se 1 (by rfl) ⟨14598764, by rfl⟩ : syracuseStep 19465019 = 29197529) B29197529
theorem B12976679 : Blo 2187435 12976679 := bstep (se 1 (by rfl) ⟨9732509, by rfl⟩ : syracuseStep 12976679 = 19465019) B19465019
theorem B8651119 : Blo 2187435 8651119 := bstep (se 1 (by rfl) ⟨6488339, by rfl⟩ : syracuseStep 8651119 = 12976679) B12976679
theorem B11534825 : Blo 2187435 11534825 := bstep (se 2 (by rfl) ⟨4325559, by rfl⟩ : syracuseStep 11534825 = 8651119) B8651119
theorem B30759533 : Blo 2187435 30759533 := bstep (se 3 (by rfl) ⟨5767412, by rfl⟩ : syracuseStep 30759533 = 11534825) B11534825
theorem B20506355 : Blo 2187435 20506355 := bstep (se 1 (by rfl) ⟨15379766, by rfl⟩ : syracuseStep 20506355 = 30759533) B30759533
theorem B13670903 : Blo 2187435 13670903 := bstep (se 1 (by rfl) ⟨10253177, by rfl⟩ : syracuseStep 13670903 = 20506355) B20506355
theorem B36455741 : Blo 2187435 36455741 := bstep (se 3 (by rfl) ⟨6835451, by rfl⟩ : syracuseStep 36455741 = 13670903) B13670903
theorem B24303827 : Blo 2187435 24303827 := bstep (se 1 (by rfl) ⟨18227870, by rfl⟩ : syracuseStep 24303827 = 36455741) B36455741
theorem B16202551 : Blo 2187435 16202551 := bstep (se 1 (by rfl) ⟨12151913, by rfl⟩ : syracuseStep 16202551 = 24303827) B24303827
theorem B21603401 : Blo 2187435 21603401 := bstep (se 2 (by rfl) ⟨8101275, by rfl⟩ : syracuseStep 21603401 = 16202551) B16202551
theorem B14402267 : Blo 2187435 14402267 := bstep (se 1 (by rfl) ⟨10801700, by rfl⟩ : syracuseStep 14402267 = 21603401) B21603401
theorem B9601511 : Blo 2187435 9601511 := bstep (se 1 (by rfl) ⟨7201133, by rfl⟩ : syracuseStep 9601511 = 14402267) B14402267
theorem B25604029 : Blo 2187435 25604029 := bstep (se 3 (by rfl) ⟨4800755, by rfl⟩ : syracuseStep 25604029 = 9601511) B9601511
theorem B34138705 : Blo 2187435 34138705 := bstep (se 2 (by rfl) ⟨12802014, by rfl⟩ : syracuseStep 34138705 = 25604029) B25604029
theorem B45518273 : Blo 2187435 45518273 := bstep (se 2 (by rfl) ⟨17069352, by rfl⟩ : syracuseStep 45518273 = 34138705) B34138705
theorem B30345515 : Blo 2187435 30345515 := bstep (se 1 (by rfl) ⟨22759136, by rfl⟩ : syracuseStep 30345515 = 45518273) B45518273
theorem B20230343 : Blo 2187435 20230343 := bstep (se 1 (by rfl) ⟨15172757, by rfl⟩ : syracuseStep 20230343 = 30345515) B30345515
theorem B13486895 : Blo 2187435 13486895 := bstep (se 1 (by rfl) ⟨10115171, by rfl⟩ : syracuseStep 13486895 = 20230343) B20230343
theorem B8991263 : Blo 2187435 8991263 := bstep (se 1 (by rfl) ⟨6743447, by rfl⟩ : syracuseStep 8991263 = 13486895) B13486895
theorem B5994175 : Blo 2187435 5994175 := bstep (se 1 (by rfl) ⟨4495631, by rfl⟩ : syracuseStep 5994175 = 8991263) B8991263
theorem B7992233 : Blo 2187435 7992233 := bstep (se 2 (by rfl) ⟨2997087, by rfl⟩ : syracuseStep 7992233 = 5994175) B5994175
theorem B5328155 : Blo 2187435 5328155 := bstep (se 1 (by rfl) ⟨3996116, by rfl⟩ : syracuseStep 5328155 = 7992233) B7992233
theorem B3552103 : Blo 2187435 3552103 := bstep (se 1 (by rfl) ⟨2664077, by rfl⟩ : syracuseStep 3552103 = 5328155) B5328155
theorem B4736137 : Blo 2187435 4736137 := bstep (se 2 (by rfl) ⟨1776051, by rfl⟩ : syracuseStep 4736137 = 3552103) B3552103
theorem B6314849 : Blo 2187435 6314849 := bstep (se 2 (by rfl) ⟨2368068, by rfl⟩ : syracuseStep 6314849 = 4736137) B4736137
theorem B4209899 : Blo 2187435 4209899 := bstep (se 1 (by rfl) ⟨3157424, by rfl⟩ : syracuseStep 4209899 = 6314849) B6314849
theorem B44905589 : Blo 2187435 44905589 := bstep (se 5 (by rfl) ⟨2104949, by rfl⟩ : syracuseStep 44905589 = 4209899) B4209899
theorem B29937059 : Blo 2187435 29937059 := bstep (se 1 (by rfl) ⟨22452794, by rfl⟩ : syracuseStep 29937059 = 44905589) B44905589
theorem B19958039 : Blo 2187435 19958039 := bstep (se 1 (by rfl) ⟨14968529, by rfl⟩ : syracuseStep 19958039 = 29937059) B29937059
theorem B13305359 : Blo 2187435 13305359 := bstep (se 1 (by rfl) ⟨9979019, by rfl⟩ : syracuseStep 13305359 = 19958039) B19958039
theorem B8870239 : Blo 2187435 8870239 := bstep (se 1 (by rfl) ⟨6652679, by rfl⟩ : syracuseStep 8870239 = 13305359) B13305359
theorem B11826985 : Blo 2187435 11826985 := bstep (se 2 (by rfl) ⟨4435119, by rfl⟩ : syracuseStep 11826985 = 8870239) B8870239
theorem B15769313 : Blo 2187435 15769313 := bstep (se 2 (by rfl) ⟨5913492, by rfl⟩ : syracuseStep 15769313 = 11826985) B11826985
theorem B10512875 : Blo 2187435 10512875 := bstep (se 1 (by rfl) ⟨7884656, by rfl⟩ : syracuseStep 10512875 = 15769313) B15769313
theorem B28034333 : Blo 2187435 28034333 := bstep (se 3 (by rfl) ⟨5256437, by rfl⟩ : syracuseStep 28034333 = 10512875) B10512875
theorem B18689555 : Blo 2187435 18689555 := bstep (se 1 (by rfl) ⟨14017166, by rfl⟩ : syracuseStep 18689555 = 28034333) B28034333
theorem B12459703 : Blo 2187435 12459703 := bstep (se 1 (by rfl) ⟨9344777, by rfl⟩ : syracuseStep 12459703 = 18689555) B18689555
theorem B16612937 : Blo 2187435 16612937 := bstep (se 2 (by rfl) ⟨6229851, by rfl⟩ : syracuseStep 16612937 = 12459703) B12459703
theorem B11075291 : Blo 2187435 11075291 := bstep (se 1 (by rfl) ⟨8306468, by rfl⟩ : syracuseStep 11075291 = 16612937) B16612937
theorem B7383527 : Blo 2187435 7383527 := bstep (se 1 (by rfl) ⟨5537645, by rfl⟩ : syracuseStep 7383527 = 11075291) B11075291
theorem B4922351 : Blo 2187435 4922351 := bstep (se 1 (by rfl) ⟨3691763, by rfl⟩ : syracuseStep 4922351 = 7383527) B7383527
theorem B3281567 : Blo 2187435 3281567 := bstep (se 1 (by rfl) ⟨2461175, by rfl⟩ : syracuseStep 3281567 = 4922351) B4922351
theorem B2187711 : Blo 2187435 2187711 := bstep (se 1 (by rfl) ⟨1640783, by rfl⟩ : syracuseStep 2187711 = 3281567) B3281567
theorem B3281573 : Blo 2187435 3281573 := bbase (se 4 (by rfl) ⟨307647, by rfl⟩ : syracuseStep 3281573 = 615295) (by norm_num)
theorem B2187715 : Blo 2187435 2187715 := bstep (se 1 (by rfl) ⟨1640786, by rfl⟩ : syracuseStep 2187715 = 3281573) B3281573
theorem B2768833 : Blo 2187435 2768833 := bbase (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) (by norm_num)
theorem B3691777 : Blo 2187435 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B4922369 : Blo 2187435 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B3281579 : Blo 2187435 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B2187719 : Blo 2187435 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B2461189 : Blo 2187435 2461189 := bbase (se 4 (by rfl) ⟨230736, by rfl⟩ : syracuseStep 2461189 = 461473) (by norm_num)
theorem B3281585 : Blo 2187435 3281585 := bstep (se 2 (by rfl) ⟨1230594, by rfl⟩ : syracuseStep 3281585 = 2461189) B2461189
theorem B2187723 : Blo 2187435 2187723 := bstep (se 1 (by rfl) ⟨1640792, by rfl⟩ : syracuseStep 2187723 = 3281585) B3281585
theorem B3114949 : Blo 2187435 3114949 := bbase (se 4 (by rfl) ⟨292026, by rfl⟩ : syracuseStep 3114949 = 584053) (by norm_num)
theorem B4153265 : Blo 2187435 4153265 := bstep (se 2 (by rfl) ⟨1557474, by rfl⟩ : syracuseStep 4153265 = 3114949) B3114949
theorem B2768843 : Blo 2187435 2768843 := bstep (se 1 (by rfl) ⟨2076632, by rfl⟩ : syracuseStep 2768843 = 4153265) B4153265
theorem B7383581 : Blo 2187435 7383581 := bstep (se 3 (by rfl) ⟨1384421, by rfl⟩ : syracuseStep 7383581 = 2768843) B2768843
theorem B4922387 : Blo 2187435 4922387 := bstep (se 1 (by rfl) ⟨3691790, by rfl⟩ : syracuseStep 4922387 = 7383581) B7383581
theorem B3281591 : Blo 2187435 3281591 := bstep (se 1 (by rfl) ⟨2461193, by rfl⟩ : syracuseStep 3281591 = 4922387) B4922387
theorem B2187727 : Blo 2187435 2187727 := bstep (se 1 (by rfl) ⟨1640795, by rfl⟩ : syracuseStep 2187727 = 3281591) B3281591
theorem B3281597 : Blo 2187435 3281597 := bbase (se 3 (by rfl) ⟨615299, by rfl⟩ : syracuseStep 3281597 = 1230599) (by norm_num)
theorem B2187731 : Blo 2187435 2187731 := bstep (se 1 (by rfl) ⟨1640798, by rfl⟩ : syracuseStep 2187731 = 3281597) B3281597
theorem B4922405 : Blo 2187435 4922405 := bbase (se 4 (by rfl) ⟨461475, by rfl⟩ : syracuseStep 4922405 = 922951) (by norm_num)
theorem B3281603 : Blo 2187435 3281603 := bstep (se 1 (by rfl) ⟨2461202, by rfl⟩ : syracuseStep 3281603 = 4922405) B4922405
theorem B2187735 : Blo 2187435 2187735 := bstep (se 1 (by rfl) ⟨1640801, by rfl⟩ : syracuseStep 2187735 = 3281603) B3281603
theorem B5537717 : Blo 2187435 5537717 := bbase (se 5 (by rfl) ⟨259580, by rfl⟩ : syracuseStep 5537717 = 519161) (by norm_num)
theorem B3691811 : Blo 2187435 3691811 := bstep (se 1 (by rfl) ⟨2768858, by rfl⟩ : syracuseStep 3691811 = 5537717) B5537717
theorem B2461207 : Blo 2187435 2461207 := bstep (se 1 (by rfl) ⟨1845905, by rfl⟩ : syracuseStep 2461207 = 3691811) B3691811
theorem B3281609 : Blo 2187435 3281609 := bstep (se 2 (by rfl) ⟨1230603, by rfl⟩ : syracuseStep 3281609 = 2461207) B2461207
theorem B2187739 : Blo 2187435 2187739 := bstep (se 1 (by rfl) ⟨1640804, by rfl⟩ : syracuseStep 2187739 = 3281609) B3281609
theorem B7884773 : Blo 2187435 7884773 := bbase (se 4 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 7884773 = 1478395) (by norm_num)
theorem B5256515 : Blo 2187435 5256515 := bstep (se 1 (by rfl) ⟨3942386, by rfl⟩ : syracuseStep 5256515 = 7884773) B7884773
theorem B14017373 : Blo 2187435 14017373 := bstep (se 3 (by rfl) ⟨2628257, by rfl⟩ : syracuseStep 14017373 = 5256515) B5256515
theorem B9344915 : Blo 2187435 9344915 := bstep (se 1 (by rfl) ⟨7008686, by rfl⟩ : syracuseStep 9344915 = 14017373) B14017373
theorem B6229943 : Blo 2187435 6229943 := bstep (se 1 (by rfl) ⟨4672457, by rfl⟩ : syracuseStep 6229943 = 9344915) B9344915
theorem B4153295 : Blo 2187435 4153295 := bstep (se 1 (by rfl) ⟨3114971, by rfl⟩ : syracuseStep 4153295 = 6229943) B6229943
theorem B11075453 : Blo 2187435 11075453 := bstep (se 3 (by rfl) ⟨2076647, by rfl⟩ : syracuseStep 11075453 = 4153295) B4153295
theorem B7383635 : Blo 2187435 7383635 := bstep (se 1 (by rfl) ⟨5537726, by rfl⟩ : syracuseStep 7383635 = 11075453) B11075453
theorem B4922423 : Blo 2187435 4922423 := bstep (se 1 (by rfl) ⟨3691817, by rfl⟩ : syracuseStep 4922423 = 7383635) B7383635
theorem B3281615 : Blo 2187435 3281615 := bstep (se 1 (by rfl) ⟨2461211, by rfl⟩ : syracuseStep 3281615 = 4922423) B4922423
theorem B2187743 : Blo 2187435 2187743 := bstep (se 1 (by rfl) ⟨1640807, by rfl⟩ : syracuseStep 2187743 = 3281615) B3281615
theorem B3281621 : Blo 2187435 3281621 := bbase (se 7 (by rfl) ⟨38456, by rfl⟩ : syracuseStep 3281621 = 76913) (by norm_num)
theorem B2187747 : Blo 2187435 2187747 := bstep (se 1 (by rfl) ⟨1640810, by rfl⟩ : syracuseStep 2187747 = 3281621) B3281621
theorem B2217601 : Blo 2187435 2217601 := bbase (se 2 (by rfl) ⟨831600, by rfl⟩ : syracuseStep 2217601 = 1663201) (by norm_num)
theorem B11827205 : Blo 2187435 11827205 := bstep (se 4 (by rfl) ⟨1108800, by rfl⟩ : syracuseStep 11827205 = 2217601) B2217601
theorem B7884803 : Blo 2187435 7884803 := bstep (se 1 (by rfl) ⟨5913602, by rfl⟩ : syracuseStep 7884803 = 11827205) B11827205
theorem B5256535 : Blo 2187435 5256535 := bstep (se 1 (by rfl) ⟨3942401, by rfl⟩ : syracuseStep 5256535 = 7884803) B7884803
theorem B7008713 : Blo 2187435 7008713 := bstep (se 2 (by rfl) ⟨2628267, by rfl⟩ : syracuseStep 7008713 = 5256535) B5256535
theorem B4672475 : Blo 2187435 4672475 := bstep (se 1 (by rfl) ⟨3504356, by rfl⟩ : syracuseStep 4672475 = 7008713) B7008713
theorem B3114983 : Blo 2187435 3114983 := bstep (se 1 (by rfl) ⟨2336237, by rfl⟩ : syracuseStep 3114983 = 4672475) B4672475
theorem B8306621 : Blo 2187435 8306621 := bstep (se 3 (by rfl) ⟨1557491, by rfl⟩ : syracuseStep 8306621 = 3114983) B3114983
theorem B5537747 : Blo 2187435 5537747 := bstep (se 1 (by rfl) ⟨4153310, by rfl⟩ : syracuseStep 5537747 = 8306621) B8306621
theorem B3691831 : Blo 2187435 3691831 := bstep (se 1 (by rfl) ⟨2768873, by rfl⟩ : syracuseStep 3691831 = 5537747) B5537747
theorem B4922441 : Blo 2187435 4922441 := bstep (se 2 (by rfl) ⟨1845915, by rfl⟩ : syracuseStep 4922441 = 3691831) B3691831
theorem B3281627 : Blo 2187435 3281627 := bstep (se 1 (by rfl) ⟨2461220, by rfl⟩ : syracuseStep 3281627 = 4922441) B4922441
theorem B2187751 : Blo 2187435 2187751 := bstep (se 1 (by rfl) ⟨1640813, by rfl⟩ : syracuseStep 2187751 = 3281627) B3281627
theorem B2461225 : Blo 2187435 2461225 := bbase (se 2 (by rfl) ⟨922959, by rfl⟩ : syracuseStep 2461225 = 1845919) (by norm_num)
theorem B3281633 : Blo 2187435 3281633 := bstep (se 2 (by rfl) ⟨1230612, by rfl⟩ : syracuseStep 3281633 = 2461225) B2461225
theorem B2187755 : Blo 2187435 2187755 := bstep (se 1 (by rfl) ⟨1640816, by rfl⟩ : syracuseStep 2187755 = 3281633) B3281633
theorem B13305653 : Blo 2187435 13305653 := bbase (se 5 (by rfl) ⟨623702, by rfl⟩ : syracuseStep 13305653 = 1247405) (by norm_num)
theorem B8870435 : Blo 2187435 8870435 := bstep (se 1 (by rfl) ⟨6652826, by rfl⟩ : syracuseStep 8870435 = 13305653) B13305653
theorem B5913623 : Blo 2187435 5913623 := bstep (se 1 (by rfl) ⟨4435217, by rfl⟩ : syracuseStep 5913623 = 8870435) B8870435
theorem B3942415 : Blo 2187435 3942415 := bstep (se 1 (by rfl) ⟨2956811, by rfl⟩ : syracuseStep 3942415 = 5913623) B5913623
theorem B21026213 : Blo 2187435 21026213 := bstep (se 4 (by rfl) ⟨1971207, by rfl⟩ : syracuseStep 21026213 = 3942415) B3942415
theorem B14017475 : Blo 2187435 14017475 := bstep (se 1 (by rfl) ⟨10513106, by rfl⟩ : syracuseStep 14017475 = 21026213) B21026213
theorem B9344983 : Blo 2187435 9344983 := bstep (se 1 (by rfl) ⟨7008737, by rfl⟩ : syracuseStep 9344983 = 14017475) B14017475
theorem B12459977 : Blo 2187435 12459977 := bstep (se 2 (by rfl) ⟨4672491, by rfl⟩ : syracuseStep 12459977 = 9344983) B9344983
theorem B8306651 : Blo 2187435 8306651 := bstep (se 1 (by rfl) ⟨6229988, by rfl⟩ : syracuseStep 8306651 = 12459977) B12459977
theorem B5537767 : Blo 2187435 5537767 := bstep (se 1 (by rfl) ⟨4153325, by rfl⟩ : syracuseStep 5537767 = 8306651) B8306651
theorem B7383689 : Blo 2187435 7383689 := bstep (se 2 (by rfl) ⟨2768883, by rfl⟩ : syracuseStep 7383689 = 5537767) B5537767
theorem B4922459 : Blo 2187435 4922459 := bstep (se 1 (by rfl) ⟨3691844, by rfl⟩ : syracuseStep 4922459 = 7383689) B7383689
theorem B3281639 : Blo 2187435 3281639 := bstep (se 1 (by rfl) ⟨2461229, by rfl⟩ : syracuseStep 3281639 = 4922459) B4922459
theorem B2187759 : Blo 2187435 2187759 := bstep (se 1 (by rfl) ⟨1640819, by rfl⟩ : syracuseStep 2187759 = 3281639) B3281639
theorem B3281645 : Blo 2187435 3281645 := bbase (se 3 (by rfl) ⟨615308, by rfl⟩ : syracuseStep 3281645 = 1230617) (by norm_num)
theorem B2187763 : Blo 2187435 2187763 := bstep (se 1 (by rfl) ⟨1640822, by rfl⟩ : syracuseStep 2187763 = 3281645) B3281645
theorem B4922477 : Blo 2187435 4922477 := bbase (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) (by norm_num)
theorem B3281651 : Blo 2187435 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B2187767 : Blo 2187435 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B4153349 : Blo 2187435 4153349 := bbase (se 4 (by rfl) ⟨389376, by rfl⟩ : syracuseStep 4153349 = 778753) (by norm_num)
theorem B2768899 : Blo 2187435 2768899 := bstep (se 1 (by rfl) ⟨2076674, by rfl⟩ : syracuseStep 2768899 = 4153349) B4153349
theorem B3691865 : Blo 2187435 3691865 := bstep (se 2 (by rfl) ⟨1384449, by rfl⟩ : syracuseStep 3691865 = 2768899) B2768899
theorem B2461243 : Blo 2187435 2461243 := bstep (se 1 (by rfl) ⟨1845932, by rfl⟩ : syracuseStep 2461243 = 3691865) B3691865
theorem B3281657 : Blo 2187435 3281657 := bstep (se 2 (by rfl) ⟨1230621, by rfl⟩ : syracuseStep 3281657 = 2461243) B2461243
theorem B2187771 : Blo 2187435 2187771 := bstep (se 1 (by rfl) ⟨1640828, by rfl⟩ : syracuseStep 2187771 = 3281657) B3281657
theorem B2806681 : Blo 2187435 2806681 := bbase (se 2 (by rfl) ⟨1052505, by rfl⟩ : syracuseStep 2806681 = 2105011) (by norm_num)
theorem B59875861 : Blo 2187435 59875861 := bstep (se 6 (by rfl) ⟨1403340, by rfl⟩ : syracuseStep 59875861 = 2806681) B2806681
theorem B79834481 : Blo 2187435 79834481 := bstep (se 2 (by rfl) ⟨29937930, by rfl⟩ : syracuseStep 79834481 = 59875861) B59875861
theorem B53222987 : Blo 2187435 53222987 := bstep (se 1 (by rfl) ⟨39917240, by rfl⟩ : syracuseStep 53222987 = 79834481) B79834481
theorem B35481991 : Blo 2187435 35481991 := bstep (se 1 (by rfl) ⟨26611493, by rfl⟩ : syracuseStep 35481991 = 53222987) B53222987
theorem B47309321 : Blo 2187435 47309321 := bstep (se 2 (by rfl) ⟨17740995, by rfl⟩ : syracuseStep 47309321 = 35481991) B35481991
theorem B31539547 : Blo 2187435 31539547 := bstep (se 1 (by rfl) ⟨23654660, by rfl⟩ : syracuseStep 31539547 = 47309321) B47309321
theorem B42052729 : Blo 2187435 42052729 := bstep (se 2 (by rfl) ⟨15769773, by rfl⟩ : syracuseStep 42052729 = 31539547) B31539547
theorem B56070305 : Blo 2187435 56070305 := bstep (se 2 (by rfl) ⟨21026364, by rfl⟩ : syracuseStep 56070305 = 42052729) B42052729
theorem B37380203 : Blo 2187435 37380203 := bstep (se 1 (by rfl) ⟨28035152, by rfl⟩ : syracuseStep 37380203 = 56070305) B56070305
theorem B24920135 : Blo 2187435 24920135 := bstep (se 1 (by rfl) ⟨18690101, by rfl⟩ : syracuseStep 24920135 = 37380203) B37380203
theorem B16613423 : Blo 2187435 16613423 := bstep (se 1 (by rfl) ⟨12460067, by rfl⟩ : syracuseStep 16613423 = 24920135) B24920135
theorem B11075615 : Blo 2187435 11075615 := bstep (se 1 (by rfl) ⟨8306711, by rfl⟩ : syracuseStep 11075615 = 16613423) B16613423
theorem B7383743 : Blo 2187435 7383743 := bstep (se 1 (by rfl) ⟨5537807, by rfl⟩ : syracuseStep 7383743 = 11075615) B11075615
theorem B4922495 : Blo 2187435 4922495 := bstep (se 1 (by rfl) ⟨3691871, by rfl⟩ : syracuseStep 4922495 = 7383743) B7383743
theorem B3281663 : Blo 2187435 3281663 := bstep (se 1 (by rfl) ⟨2461247, by rfl⟩ : syracuseStep 3281663 = 4922495) B4922495
theorem B2187775 : Blo 2187435 2187775 := bstep (se 1 (by rfl) ⟨1640831, by rfl⟩ : syracuseStep 2187775 = 3281663) B3281663
theorem B3281669 : Blo 2187435 3281669 := bbase (se 4 (by rfl) ⟨307656, by rfl⟩ : syracuseStep 3281669 = 615313) (by norm_num)
theorem B2187779 : Blo 2187435 2187779 := bstep (se 1 (by rfl) ⟨1640834, by rfl⟩ : syracuseStep 2187779 = 3281669) B3281669
theorem B3691885 : Blo 2187435 3691885 := bbase (se 3 (by rfl) ⟨692228, by rfl⟩ : syracuseStep 3691885 = 1384457) (by norm_num)
theorem B4922513 : Blo 2187435 4922513 := bstep (se 2 (by rfl) ⟨1845942, by rfl⟩ : syracuseStep 4922513 = 3691885) B3691885
theorem B3281675 : Blo 2187435 3281675 := bstep (se 1 (by rfl) ⟨2461256, by rfl⟩ : syracuseStep 3281675 = 4922513) B4922513
theorem B2187783 : Blo 2187435 2187783 := bstep (se 1 (by rfl) ⟨1640837, by rfl⟩ : syracuseStep 2187783 = 3281675) B3281675
theorem B2461261 : Blo 2187435 2461261 := bbase (se 3 (by rfl) ⟨461486, by rfl⟩ : syracuseStep 2461261 = 922973) (by norm_num)
theorem B3281681 : Blo 2187435 3281681 := bstep (se 2 (by rfl) ⟨1230630, by rfl⟩ : syracuseStep 3281681 = 2461261) B2461261
theorem B2187787 : Blo 2187435 2187787 := bstep (se 1 (by rfl) ⟨1640840, by rfl⟩ : syracuseStep 2187787 = 3281681) B3281681
theorem B7383797 : Blo 2187435 7383797 := bbase (se 5 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 7383797 = 692231) (by norm_num)
theorem B4922531 : Blo 2187435 4922531 := bstep (se 1 (by rfl) ⟨3691898, by rfl⟩ : syracuseStep 4922531 = 7383797) B7383797
theorem B3281687 : Blo 2187435 3281687 := bstep (se 1 (by rfl) ⟨2461265, by rfl⟩ : syracuseStep 3281687 = 4922531) B4922531
theorem B2187791 : Blo 2187435 2187791 := bstep (se 1 (by rfl) ⟨1640843, by rfl⟩ : syracuseStep 2187791 = 3281687) B3281687
theorem B3281693 : Blo 2187435 3281693 := bbase (se 3 (by rfl) ⟨615317, by rfl⟩ : syracuseStep 3281693 = 1230635) (by norm_num)
theorem B2187795 : Blo 2187435 2187795 := bstep (se 1 (by rfl) ⟨1640846, by rfl⟩ : syracuseStep 2187795 = 3281693) B3281693
theorem B4922549 : Blo 2187435 4922549 := bbase (se 5 (by rfl) ⟨230744, by rfl⟩ : syracuseStep 4922549 = 461489) (by norm_num)
theorem B3281699 : Blo 2187435 3281699 := bstep (se 1 (by rfl) ⟨2461274, by rfl⟩ : syracuseStep 3281699 = 4922549) B4922549
theorem B2187799 : Blo 2187435 2187799 := bstep (se 1 (by rfl) ⟨1640849, by rfl⟩ : syracuseStep 2187799 = 3281699) B3281699
theorem B2336293 : Blo 2187435 2336293 := bbase (se 4 (by rfl) ⟨219027, by rfl⟩ : syracuseStep 2336293 = 438055) (by norm_num)
theorem B12460229 : Blo 2187435 12460229 := bstep (se 4 (by rfl) ⟨1168146, by rfl⟩ : syracuseStep 12460229 = 2336293) B2336293
theorem B8306819 : Blo 2187435 8306819 := bstep (se 1 (by rfl) ⟨6230114, by rfl⟩ : syracuseStep 8306819 = 12460229) B12460229
theorem B5537879 : Blo 2187435 5537879 := bstep (se 1 (by rfl) ⟨4153409, by rfl⟩ : syracuseStep 5537879 = 8306819) B8306819
theorem B3691919 : Blo 2187435 3691919 := bstep (se 1 (by rfl) ⟨2768939, by rfl⟩ : syracuseStep 3691919 = 5537879) B5537879
theorem B2461279 : Blo 2187435 2461279 := bstep (se 1 (by rfl) ⟨1845959, by rfl⟩ : syracuseStep 2461279 = 3691919) B3691919
theorem B3281705 : Blo 2187435 3281705 := bstep (se 2 (by rfl) ⟨1230639, by rfl⟩ : syracuseStep 3281705 = 2461279) B2461279
theorem B2187803 : Blo 2187435 2187803 := bstep (se 1 (by rfl) ⟨1640852, by rfl⟩ : syracuseStep 2187803 = 3281705) B3281705
theorem B2336297 : Blo 2187435 2336297 := bbase (se 2 (by rfl) ⟨876111, by rfl⟩ : syracuseStep 2336297 = 1752223) (by norm_num)
theorem B6230125 : Blo 2187435 6230125 := bstep (se 3 (by rfl) ⟨1168148, by rfl⟩ : syracuseStep 6230125 = 2336297) B2336297
theorem B8306833 : Blo 2187435 8306833 := bstep (se 2 (by rfl) ⟨3115062, by rfl⟩ : syracuseStep 8306833 = 6230125) B6230125
theorem B11075777 : Blo 2187435 11075777 := bstep (se 2 (by rfl) ⟨4153416, by rfl⟩ : syracuseStep 11075777 = 8306833) B8306833
theorem B7383851 : Blo 2187435 7383851 := bstep (se 1 (by rfl) ⟨5537888, by rfl⟩ : syracuseStep 7383851 = 11075777) B11075777
theorem B4922567 : Blo 2187435 4922567 := bstep (se 1 (by rfl) ⟨3691925, by rfl⟩ : syracuseStep 4922567 = 7383851) B7383851
theorem B3281711 : Blo 2187435 3281711 := bstep (se 1 (by rfl) ⟨2461283, by rfl⟩ : syracuseStep 3281711 = 4922567) B4922567
theorem B2187807 : Blo 2187435 2187807 := bstep (se 1 (by rfl) ⟨1640855, by rfl⟩ : syracuseStep 2187807 = 3281711) B3281711
theorem B3281717 : Blo 2187435 3281717 := bbase (se 5 (by rfl) ⟨153830, by rfl⟩ : syracuseStep 3281717 = 307661) (by norm_num)
theorem B2187811 : Blo 2187435 2187811 := bstep (se 1 (by rfl) ⟨1640858, by rfl⟩ : syracuseStep 2187811 = 3281717) B3281717
theorem B5537909 : Blo 2187435 5537909 := bbase (se 5 (by rfl) ⟨259589, by rfl⟩ : syracuseStep 5537909 = 519179) (by norm_num)
theorem B3691939 : Blo 2187435 3691939 := bstep (se 1 (by rfl) ⟨2768954, by rfl⟩ : syracuseStep 3691939 = 5537909) B5537909
theorem B4922585 : Blo 2187435 4922585 := bstep (se 2 (by rfl) ⟨1845969, by rfl⟩ : syracuseStep 4922585 = 3691939) B3691939
theorem B3281723 : Blo 2187435 3281723 := bstep (se 1 (by rfl) ⟨2461292, by rfl⟩ : syracuseStep 3281723 = 4922585) B4922585
theorem B2187815 : Blo 2187435 2187815 := bstep (se 1 (by rfl) ⟨1640861, by rfl⟩ : syracuseStep 2187815 = 3281723) B3281723
theorem B2461297 : Blo 2187435 2461297 := bbase (se 2 (by rfl) ⟨922986, by rfl⟩ : syracuseStep 2461297 = 1845973) (by norm_num)
theorem B3281729 : Blo 2187435 3281729 := bstep (se 2 (by rfl) ⟨1230648, by rfl⟩ : syracuseStep 3281729 = 2461297) B2461297
theorem B2187819 : Blo 2187435 2187819 := bstep (se 1 (by rfl) ⟨1640864, by rfl⟩ : syracuseStep 2187819 = 3281729) B3281729
theorem B3742325 : Blo 2187435 3742325 := bbase (se 5 (by rfl) ⟨175421, by rfl⟩ : syracuseStep 3742325 = 350843) (by norm_num)
theorem B2494883 : Blo 2187435 2494883 := bstep (se 1 (by rfl) ⟨1871162, by rfl⟩ : syracuseStep 2494883 = 3742325) B3742325
theorem B6653021 : Blo 2187435 6653021 := bstep (se 3 (by rfl) ⟨1247441, by rfl⟩ : syracuseStep 6653021 = 2494883) B2494883
theorem B17741389 : Blo 2187435 17741389 := bstep (se 3 (by rfl) ⟨3326510, by rfl⟩ : syracuseStep 17741389 = 6653021) B6653021
theorem B23655185 : Blo 2187435 23655185 := bstep (se 2 (by rfl) ⟨8870694, by rfl⟩ : syracuseStep 23655185 = 17741389) B17741389
theorem B15770123 : Blo 2187435 15770123 := bstep (se 1 (by rfl) ⟨11827592, by rfl⟩ : syracuseStep 15770123 = 23655185) B23655185
theorem B10513415 : Blo 2187435 10513415 := bstep (se 1 (by rfl) ⟨7885061, by rfl⟩ : syracuseStep 10513415 = 15770123) B15770123
theorem B7008943 : Blo 2187435 7008943 := bstep (se 1 (by rfl) ⟨5256707, by rfl⟩ : syracuseStep 7008943 = 10513415) B10513415
theorem B9345257 : Blo 2187435 9345257 := bstep (se 2 (by rfl) ⟨3504471, by rfl⟩ : syracuseStep 9345257 = 7008943) B7008943
theorem B6230171 : Blo 2187435 6230171 := bstep (se 1 (by rfl) ⟨4672628, by rfl⟩ : syracuseStep 6230171 = 9345257) B9345257
theorem B4153447 : Blo 2187435 4153447 := bstep (se 1 (by rfl) ⟨3115085, by rfl⟩ : syracuseStep 4153447 = 6230171) B6230171
theorem B5537929 : Blo 2187435 5537929 := bstep (se 2 (by rfl) ⟨2076723, by rfl⟩ : syracuseStep 5537929 = 4153447) B4153447
theorem B7383905 : Blo 2187435 7383905 := bstep (se 2 (by rfl) ⟨2768964, by rfl⟩ : syracuseStep 7383905 = 5537929) B5537929
theorem B4922603 : Blo 2187435 4922603 := bstep (se 1 (by rfl) ⟨3691952, by rfl⟩ : syracuseStep 4922603 = 7383905) B7383905
theorem B3281735 : Blo 2187435 3281735 := bstep (se 1 (by rfl) ⟨2461301, by rfl⟩ : syracuseStep 3281735 = 4922603) B4922603
theorem B2187823 : Blo 2187435 2187823 := bstep (se 1 (by rfl) ⟨1640867, by rfl⟩ : syracuseStep 2187823 = 3281735) B3281735
theorem B3281741 : Blo 2187435 3281741 := bbase (se 3 (by rfl) ⟨615326, by rfl⟩ : syracuseStep 3281741 = 1230653) (by norm_num)
theorem B2187827 : Blo 2187435 2187827 := bstep (se 1 (by rfl) ⟨1640870, by rfl⟩ : syracuseStep 2187827 = 3281741) B3281741
theorem B4922621 : Blo 2187435 4922621 := bbase (se 3 (by rfl) ⟨922991, by rfl⟩ : syracuseStep 4922621 = 1845983) (by norm_num)
theorem B3281747 : Blo 2187435 3281747 := bstep (se 1 (by rfl) ⟨2461310, by rfl⟩ : syracuseStep 3281747 = 4922621) B4922621
theorem B2187831 : Blo 2187435 2187831 := bstep (se 1 (by rfl) ⟨1640873, by rfl⟩ : syracuseStep 2187831 = 3281747) B3281747
theorem B3691973 : Blo 2187435 3691973 := bbase (se 4 (by rfl) ⟨346122, by rfl⟩ : syracuseStep 3691973 = 692245) (by norm_num)
theorem B2461315 : Blo 2187435 2461315 := bstep (se 1 (by rfl) ⟨1845986, by rfl⟩ : syracuseStep 2461315 = 3691973) B3691973
theorem B3281753 : Blo 2187435 3281753 := bstep (se 2 (by rfl) ⟨1230657, by rfl⟩ : syracuseStep 3281753 = 2461315) B2461315
theorem B2187835 : Blo 2187435 2187835 := bstep (se 1 (by rfl) ⟨1640876, by rfl⟩ : syracuseStep 2187835 = 3281753) B3281753
theorem B16613909 : Blo 2187435 16613909 := bbase (se 6 (by rfl) ⟨389388, by rfl⟩ : syracuseStep 16613909 = 778777) (by norm_num)
theorem B11075939 : Blo 2187435 11075939 := bstep (se 1 (by rfl) ⟨8306954, by rfl⟩ : syracuseStep 11075939 = 16613909) B16613909
theorem B7383959 : Blo 2187435 7383959 := bstep (se 1 (by rfl) ⟨5537969, by rfl⟩ : syracuseStep 7383959 = 11075939) B11075939
theorem B4922639 : Blo 2187435 4922639 := bstep (se 1 (by rfl) ⟨3691979, by rfl⟩ : syracuseStep 4922639 = 7383959) B7383959
theorem B3281759 : Blo 2187435 3281759 := bstep (se 1 (by rfl) ⟨2461319, by rfl⟩ : syracuseStep 3281759 = 4922639) B4922639
theorem B2187839 : Blo 2187435 2187839 := bstep (se 1 (by rfl) ⟨1640879, by rfl⟩ : syracuseStep 2187839 = 3281759) B3281759
theorem B3281765 : Blo 2187435 3281765 := bbase (se 4 (by rfl) ⟨307665, by rfl⟩ : syracuseStep 3281765 = 615331) (by norm_num)
theorem B2187843 : Blo 2187435 2187843 := bstep (se 1 (by rfl) ⟨1640882, by rfl⟩ : syracuseStep 2187843 = 3281765) B3281765
theorem B4153493 : Blo 2187435 4153493 := bbase (se 6 (by rfl) ⟨97347, by rfl⟩ : syracuseStep 4153493 = 194695) (by norm_num)
theorem B2768995 : Blo 2187435 2768995 := bstep (se 1 (by rfl) ⟨2076746, by rfl⟩ : syracuseStep 2768995 = 4153493) B4153493
theorem B3691993 : Blo 2187435 3691993 := bstep (se 2 (by rfl) ⟨1384497, by rfl⟩ : syracuseStep 3691993 = 2768995) B2768995
theorem B4922657 : Blo 2187435 4922657 := bstep (se 2 (by rfl) ⟨1845996, by rfl⟩ : syracuseStep 4922657 = 3691993) B3691993
theorem B3281771 : Blo 2187435 3281771 := bstep (se 1 (by rfl) ⟨2461328, by rfl⟩ : syracuseStep 3281771 = 4922657) B4922657
theorem B2187847 : Blo 2187435 2187847 := bstep (se 1 (by rfl) ⟨1640885, by rfl⟩ : syracuseStep 2187847 = 3281771) B3281771
theorem B2461333 : Blo 2187435 2461333 := bbase (se 6 (by rfl) ⟨57687, by rfl⟩ : syracuseStep 2461333 = 115375) (by norm_num)
theorem B3281777 : Blo 2187435 3281777 := bstep (se 2 (by rfl) ⟨1230666, by rfl⟩ : syracuseStep 3281777 = 2461333) B2461333
theorem B2187851 : Blo 2187435 2187851 := bstep (se 1 (by rfl) ⟨1640888, by rfl⟩ : syracuseStep 2187851 = 3281777) B3281777
theorem B2769005 : Blo 2187435 2769005 := bbase (se 3 (by rfl) ⟨519188, by rfl⟩ : syracuseStep 2769005 = 1038377) (by norm_num)
theorem B7384013 : Blo 2187435 7384013 := bstep (se 3 (by rfl) ⟨1384502, by rfl⟩ : syracuseStep 7384013 = 2769005) B2769005
theorem B4922675 : Blo 2187435 4922675 := bstep (se 1 (by rfl) ⟨3692006, by rfl⟩ : syracuseStep 4922675 = 7384013) B7384013
theorem B3281783 : Blo 2187435 3281783 := bstep (se 1 (by rfl) ⟨2461337, by rfl⟩ : syracuseStep 3281783 = 4922675) B4922675
theorem B2187855 : Blo 2187435 2187855 := bstep (se 1 (by rfl) ⟨1640891, by rfl⟩ : syracuseStep 2187855 = 3281783) B3281783
theorem B3281789 : Blo 2187435 3281789 := bbase (se 3 (by rfl) ⟨615335, by rfl⟩ : syracuseStep 3281789 = 1230671) (by norm_num)
theorem B2187859 : Blo 2187435 2187859 := bstep (se 1 (by rfl) ⟨1640894, by rfl⟩ : syracuseStep 2187859 = 3281789) B3281789
theorem B4922693 : Blo 2187435 4922693 := bbase (se 4 (by rfl) ⟨461502, by rfl⟩ : syracuseStep 4922693 = 923005) (by norm_num)
theorem B3281795 : Blo 2187435 3281795 := bstep (se 1 (by rfl) ⟨2461346, by rfl⟩ : syracuseStep 3281795 = 4922693) B4922693
theorem B2187863 : Blo 2187435 2187863 := bstep (se 1 (by rfl) ⟨1640897, by rfl⟩ : syracuseStep 2187863 = 3281795) B3281795
theorem B4989869 : Blo 2187435 4989869 := bbase (se 3 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 4989869 = 1871201) (by norm_num)
theorem B3326579 : Blo 2187435 3326579 := bstep (se 1 (by rfl) ⟨2494934, by rfl⟩ : syracuseStep 3326579 = 4989869) B4989869
theorem B2217719 : Blo 2187435 2217719 := bstep (se 1 (by rfl) ⟨1663289, by rfl⟩ : syracuseStep 2217719 = 3326579) B3326579
theorem B5913917 : Blo 2187435 5913917 := bstep (se 3 (by rfl) ⟨1108859, by rfl⟩ : syracuseStep 5913917 = 2217719) B2217719
theorem B3942611 : Blo 2187435 3942611 := bstep (se 1 (by rfl) ⟨2956958, by rfl⟩ : syracuseStep 3942611 = 5913917) B5913917
theorem B2628407 : Blo 2187435 2628407 := bstep (se 1 (by rfl) ⟨1971305, by rfl⟩ : syracuseStep 2628407 = 3942611) B3942611
theorem B7009085 : Blo 2187435 7009085 := bstep (se 3 (by rfl) ⟨1314203, by rfl⟩ : syracuseStep 7009085 = 2628407) B2628407
theorem B4672723 : Blo 2187435 4672723 := bstep (se 1 (by rfl) ⟨3504542, by rfl⟩ : syracuseStep 4672723 = 7009085) B7009085
theorem B6230297 : Blo 2187435 6230297 := bstep (se 2 (by rfl) ⟨2336361, by rfl⟩ : syracuseStep 6230297 = 4672723) B4672723
theorem B4153531 : Blo 2187435 4153531 := bstep (se 1 (by rfl) ⟨3115148, by rfl⟩ : syracuseStep 4153531 = 6230297) B6230297
theorem B5538041 : Blo 2187435 5538041 := bstep (se 2 (by rfl) ⟨2076765, by rfl⟩ : syracuseStep 5538041 = 4153531) B4153531
theorem B3692027 : Blo 2187435 3692027 := bstep (se 1 (by rfl) ⟨2769020, by rfl⟩ : syracuseStep 3692027 = 5538041) B5538041
theorem B2461351 : Blo 2187435 2461351 := bstep (se 1 (by rfl) ⟨1846013, by rfl⟩ : syracuseStep 2461351 = 3692027) B3692027
theorem B3281801 : Blo 2187435 3281801 := bstep (se 2 (by rfl) ⟨1230675, by rfl⟩ : syracuseStep 3281801 = 2461351) B2461351
theorem B2187867 : Blo 2187435 2187867 := bstep (se 1 (by rfl) ⟨1640900, by rfl⟩ : syracuseStep 2187867 = 3281801) B3281801
theorem B11076101 : Blo 2187435 11076101 := bbase (se 4 (by rfl) ⟨1038384, by rfl⟩ : syracuseStep 11076101 = 2076769) (by norm_num)
theorem B7384067 : Blo 2187435 7384067 := bstep (se 1 (by rfl) ⟨5538050, by rfl⟩ : syracuseStep 7384067 = 11076101) B11076101
theorem B4922711 : Blo 2187435 4922711 := bstep (se 1 (by rfl) ⟨3692033, by rfl⟩ : syracuseStep 4922711 = 7384067) B7384067
theorem B3281807 : Blo 2187435 3281807 := bstep (se 1 (by rfl) ⟨2461355, by rfl⟩ : syracuseStep 3281807 = 4922711) B4922711
theorem B2187871 : Blo 2187435 2187871 := bstep (se 1 (by rfl) ⟨1640903, by rfl⟩ : syracuseStep 2187871 = 3281807) B3281807
theorem B3281813 : Blo 2187435 3281813 := bbase (se 6 (by rfl) ⟨76917, by rfl⟩ : syracuseStep 3281813 = 153835) (by norm_num)
theorem B2187875 : Blo 2187435 2187875 := bstep (se 1 (by rfl) ⟨1640906, by rfl⟩ : syracuseStep 2187875 = 3281813) B3281813
theorem B12460661 : Blo 2187435 12460661 := bbase (se 5 (by rfl) ⟨584093, by rfl⟩ : syracuseStep 12460661 = 1168187) (by norm_num)
theorem B8307107 : Blo 2187435 8307107 := bstep (se 1 (by rfl) ⟨6230330, by rfl⟩ : syracuseStep 8307107 = 12460661) B12460661
theorem B5538071 : Blo 2187435 5538071 := bstep (se 1 (by rfl) ⟨4153553, by rfl⟩ : syracuseStep 5538071 = 8307107) B8307107
theorem B3692047 : Blo 2187435 3692047 := bstep (se 1 (by rfl) ⟨2769035, by rfl⟩ : syracuseStep 3692047 = 5538071) B5538071
theorem B4922729 : Blo 2187435 4922729 := bstep (se 2 (by rfl) ⟨1846023, by rfl⟩ : syracuseStep 4922729 = 3692047) B3692047
theorem B3281819 : Blo 2187435 3281819 := bstep (se 1 (by rfl) ⟨2461364, by rfl⟩ : syracuseStep 3281819 = 4922729) B4922729
theorem B2187879 : Blo 2187435 2187879 := bstep (se 1 (by rfl) ⟨1640909, by rfl⟩ : syracuseStep 2187879 = 3281819) B3281819
theorem B2461369 : Blo 2187435 2461369 := bbase (se 2 (by rfl) ⟨923013, by rfl⟩ : syracuseStep 2461369 = 1846027) (by norm_num)
theorem B3281825 : Blo 2187435 3281825 := bstep (se 2 (by rfl) ⟨1230684, by rfl⟩ : syracuseStep 3281825 = 2461369) B2461369
theorem B2187883 : Blo 2187435 2187883 := bstep (se 1 (by rfl) ⟨1640912, by rfl⟩ : syracuseStep 2187883 = 3281825) B3281825
theorem B4672765 : Blo 2187435 4672765 := bbase (se 3 (by rfl) ⟨876143, by rfl⟩ : syracuseStep 4672765 = 1752287) (by norm_num)
theorem B6230353 : Blo 2187435 6230353 := bstep (se 2 (by rfl) ⟨2336382, by rfl⟩ : syracuseStep 6230353 = 4672765) B4672765
theorem B8307137 : Blo 2187435 8307137 := bstep (se 2 (by rfl) ⟨3115176, by rfl⟩ : syracuseStep 8307137 = 6230353) B6230353
theorem B5538091 : Blo 2187435 5538091 := bstep (se 1 (by rfl) ⟨4153568, by rfl⟩ : syracuseStep 5538091 = 8307137) B8307137
theorem B7384121 : Blo 2187435 7384121 := bstep (se 2 (by rfl) ⟨2769045, by rfl⟩ : syracuseStep 7384121 = 5538091) B5538091
theorem B4922747 : Blo 2187435 4922747 := bstep (se 1 (by rfl) ⟨3692060, by rfl⟩ : syracuseStep 4922747 = 7384121) B7384121
theorem B3281831 : Blo 2187435 3281831 := bstep (se 1 (by rfl) ⟨2461373, by rfl⟩ : syracuseStep 3281831 = 4922747) B4922747
theorem B2187887 : Blo 2187435 2187887 := bstep (se 1 (by rfl) ⟨1640915, by rfl⟩ : syracuseStep 2187887 = 3281831) B3281831
theorem B3281837 : Blo 2187435 3281837 := bbase (se 3 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 3281837 = 1230689) (by norm_num)
theorem B2187891 : Blo 2187435 2187891 := bstep (se 1 (by rfl) ⟨1640918, by rfl⟩ : syracuseStep 2187891 = 3281837) B3281837
theorem B4922765 : Blo 2187435 4922765 := bbase (se 3 (by rfl) ⟨923018, by rfl⟩ : syracuseStep 4922765 = 1846037) (by norm_num)
theorem B3281843 : Blo 2187435 3281843 := bstep (se 1 (by rfl) ⟨2461382, by rfl⟩ : syracuseStep 3281843 = 4922765) B4922765
theorem B2187895 : Blo 2187435 2187895 := bstep (se 1 (by rfl) ⟨1640921, by rfl⟩ : syracuseStep 2187895 = 3281843) B3281843
theorem B2769061 : Blo 2187435 2769061 := bbase (se 4 (by rfl) ⟨259599, by rfl⟩ : syracuseStep 2769061 = 519199) (by norm_num)
theorem B3692081 : Blo 2187435 3692081 := bstep (se 2 (by rfl) ⟨1384530, by rfl⟩ : syracuseStep 3692081 = 2769061) B2769061
theorem B2461387 : Blo 2187435 2461387 := bstep (se 1 (by rfl) ⟨1846040, by rfl⟩ : syracuseStep 2461387 = 3692081) B3692081
theorem B3281849 : Blo 2187435 3281849 := bstep (se 2 (by rfl) ⟨1230693, by rfl⟩ : syracuseStep 3281849 = 2461387) B2461387
theorem B2187899 : Blo 2187435 2187899 := bstep (se 1 (by rfl) ⟨1640924, by rfl⟩ : syracuseStep 2187899 = 3281849) B3281849
theorem B2248013 : Blo 2187435 2248013 := bbase (se 3 (by rfl) ⟨421502, by rfl⟩ : syracuseStep 2248013 = 843005) (by norm_num)
theorem B5994701 : Blo 2187435 5994701 := bstep (se 3 (by rfl) ⟨1124006, by rfl⟩ : syracuseStep 5994701 = 2248013) B2248013
theorem B3996467 : Blo 2187435 3996467 := bstep (se 1 (by rfl) ⟨2997350, by rfl⟩ : syracuseStep 3996467 = 5994701) B5994701
theorem B2664311 : Blo 2187435 2664311 := bstep (se 1 (by rfl) ⟨1998233, by rfl⟩ : syracuseStep 2664311 = 3996467) B3996467
theorem B7104829 : Blo 2187435 7104829 := bstep (se 3 (by rfl) ⟨1332155, by rfl⟩ : syracuseStep 7104829 = 2664311) B2664311
theorem B9473105 : Blo 2187435 9473105 := bstep (se 2 (by rfl) ⟨3552414, by rfl⟩ : syracuseStep 9473105 = 7104829) B7104829
theorem B6315403 : Blo 2187435 6315403 := bstep (se 1 (by rfl) ⟨4736552, by rfl⟩ : syracuseStep 6315403 = 9473105) B9473105
theorem B8420537 : Blo 2187435 8420537 := bstep (se 2 (by rfl) ⟨3157701, by rfl⟩ : syracuseStep 8420537 = 6315403) B6315403
theorem B22454765 : Blo 2187435 22454765 := bstep (se 3 (by rfl) ⟨4210268, by rfl⟩ : syracuseStep 22454765 = 8420537) B8420537
theorem B14969843 : Blo 2187435 14969843 := bstep (se 1 (by rfl) ⟨11227382, by rfl⟩ : syracuseStep 14969843 = 22454765) B22454765
theorem B9979895 : Blo 2187435 9979895 := bstep (se 1 (by rfl) ⟨7484921, by rfl⟩ : syracuseStep 9979895 = 14969843) B14969843
theorem B6653263 : Blo 2187435 6653263 := bstep (se 1 (by rfl) ⟨4989947, by rfl⟩ : syracuseStep 6653263 = 9979895) B9979895
theorem B8871017 : Blo 2187435 8871017 := bstep (se 2 (by rfl) ⟨3326631, by rfl⟩ : syracuseStep 8871017 = 6653263) B6653263
theorem B23656045 : Blo 2187435 23656045 := bstep (se 3 (by rfl) ⟨4435508, by rfl⟩ : syracuseStep 23656045 = 8871017) B8871017
theorem B31541393 : Blo 2187435 31541393 := bstep (se 2 (by rfl) ⟨11828022, by rfl⟩ : syracuseStep 31541393 = 23656045) B23656045
theorem B21027595 : Blo 2187435 21027595 := bstep (se 1 (by rfl) ⟨15770696, by rfl⟩ : syracuseStep 21027595 = 31541393) B31541393
theorem B28036793 : Blo 2187435 28036793 := bstep (se 2 (by rfl) ⟨10513797, by rfl⟩ : syracuseStep 28036793 = 21027595) B21027595
theorem B18691195 : Blo 2187435 18691195 := bstep (se 1 (by rfl) ⟨14018396, by rfl⟩ : syracuseStep 18691195 = 28036793) B28036793
theorem B24921593 : Blo 2187435 24921593 := bstep (se 2 (by rfl) ⟨9345597, by rfl⟩ : syracuseStep 24921593 = 18691195) B18691195
theorem B16614395 : Blo 2187435 16614395 := bstep (se 1 (by rfl) ⟨12460796, by rfl⟩ : syracuseStep 16614395 = 24921593) B24921593
theorem B11076263 : Blo 2187435 11076263 := bstep (se 1 (by rfl) ⟨8307197, by rfl⟩ : syracuseStep 11076263 = 16614395) B16614395
theorem B7384175 : Blo 2187435 7384175 := bstep (se 1 (by rfl) ⟨5538131, by rfl⟩ : syracuseStep 7384175 = 11076263) B11076263
theorem B4922783 : Blo 2187435 4922783 := bstep (se 1 (by rfl) ⟨3692087, by rfl⟩ : syracuseStep 4922783 = 7384175) B7384175
theorem B3281855 : Blo 2187435 3281855 := bstep (se 1 (by rfl) ⟨2461391, by rfl⟩ : syracuseStep 3281855 = 4922783) B4922783
theorem B2187903 : Blo 2187435 2187903 := bstep (se 1 (by rfl) ⟨1640927, by rfl⟩ : syracuseStep 2187903 = 3281855) B3281855
theorem B3281861 : Blo 2187435 3281861 := bbase (se 4 (by rfl) ⟨307674, by rfl⟩ : syracuseStep 3281861 = 615349) (by norm_num)
theorem B2187907 : Blo 2187435 2187907 := bstep (se 1 (by rfl) ⟨1640930, by rfl⟩ : syracuseStep 2187907 = 3281861) B3281861
theorem B3692101 : Blo 2187435 3692101 := bbase (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) (by norm_num)
theorem B4922801 : Blo 2187435 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B3281867 : Blo 2187435 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B2187911 : Blo 2187435 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B2461405 : Blo 2187435 2461405 := bbase (se 3 (by rfl) ⟨461513, by rfl⟩ : syracuseStep 2461405 = 923027) (by norm_num)
theorem B3281873 : Blo 2187435 3281873 := bstep (se 2 (by rfl) ⟨1230702, by rfl⟩ : syracuseStep 3281873 = 2461405) B2461405
theorem B2187915 : Blo 2187435 2187915 := bstep (se 1 (by rfl) ⟨1640936, by rfl⟩ : syracuseStep 2187915 = 3281873) B3281873
theorem B7384229 : Blo 2187435 7384229 := bbase (se 4 (by rfl) ⟨692271, by rfl⟩ : syracuseStep 7384229 = 1384543) (by norm_num)
theorem B4922819 : Blo 2187435 4922819 := bstep (se 1 (by rfl) ⟨3692114, by rfl⟩ : syracuseStep 4922819 = 7384229) B7384229
theorem B3281879 : Blo 2187435 3281879 := bstep (se 1 (by rfl) ⟨2461409, by rfl⟩ : syracuseStep 3281879 = 4922819) B4922819
theorem B2187919 : Blo 2187435 2187919 := bstep (se 1 (by rfl) ⟨1640939, by rfl⟩ : syracuseStep 2187919 = 3281879) B3281879
theorem B3281885 : Blo 2187435 3281885 := bbase (se 3 (by rfl) ⟨615353, by rfl⟩ : syracuseStep 3281885 = 1230707) (by norm_num)
theorem B2187923 : Blo 2187435 2187923 := bstep (se 1 (by rfl) ⟨1640942, by rfl⟩ : syracuseStep 2187923 = 3281885) B3281885
theorem B4922837 : Blo 2187435 4922837 := bbase (se 7 (by rfl) ⟨57689, by rfl⟩ : syracuseStep 4922837 = 115379) (by norm_num)
theorem B3281891 : Blo 2187435 3281891 := bstep (se 1 (by rfl) ⟨2461418, by rfl⟩ : syracuseStep 3281891 = 4922837) B4922837
theorem B2187927 : Blo 2187435 2187927 := bstep (se 1 (by rfl) ⟨1640945, by rfl⟩ : syracuseStep 2187927 = 3281891) B3281891
theorem B4990013 : Blo 2187435 4990013 := bbase (se 3 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 4990013 = 1871255) (by norm_num)
theorem B3326675 : Blo 2187435 3326675 := bstep (se 1 (by rfl) ⟨2495006, by rfl⟩ : syracuseStep 3326675 = 4990013) B4990013
theorem B8871133 : Blo 2187435 8871133 := bstep (se 3 (by rfl) ⟨1663337, by rfl⟩ : syracuseStep 8871133 = 3326675) B3326675
theorem B11828177 : Blo 2187435 11828177 := bstep (se 2 (by rfl) ⟨4435566, by rfl⟩ : syracuseStep 11828177 = 8871133) B8871133
theorem B7885451 : Blo 2187435 7885451 := bstep (se 1 (by rfl) ⟨5914088, by rfl⟩ : syracuseStep 7885451 = 11828177) B11828177
theorem B21027869 : Blo 2187435 21027869 := bstep (se 3 (by rfl) ⟨3942725, by rfl⟩ : syracuseStep 21027869 = 7885451) B7885451
theorem B14018579 : Blo 2187435 14018579 := bstep (se 1 (by rfl) ⟨10513934, by rfl⟩ : syracuseStep 14018579 = 21027869) B21027869
theorem B9345719 : Blo 2187435 9345719 := bstep (se 1 (by rfl) ⟨7009289, by rfl⟩ : syracuseStep 9345719 = 14018579) B14018579
theorem B6230479 : Blo 2187435 6230479 := bstep (se 1 (by rfl) ⟨4672859, by rfl⟩ : syracuseStep 6230479 = 9345719) B9345719
theorem B8307305 : Blo 2187435 8307305 := bstep (se 2 (by rfl) ⟨3115239, by rfl⟩ : syracuseStep 8307305 = 6230479) B6230479
theorem B5538203 : Blo 2187435 5538203 := bstep (se 1 (by rfl) ⟨4153652, by rfl⟩ : syracuseStep 5538203 = 8307305) B8307305
theorem B3692135 : Blo 2187435 3692135 := bstep (se 1 (by rfl) ⟨2769101, by rfl⟩ : syracuseStep 3692135 = 5538203) B5538203
theorem B2461423 : Blo 2187435 2461423 := bstep (se 1 (by rfl) ⟨1846067, by rfl⟩ : syracuseStep 2461423 = 3692135) B3692135
theorem B3281897 : Blo 2187435 3281897 := bstep (se 2 (by rfl) ⟨1230711, by rfl⟩ : syracuseStep 3281897 = 2461423) B2461423
theorem B2187931 : Blo 2187435 2187931 := bstep (se 1 (by rfl) ⟨1640948, by rfl⟩ : syracuseStep 2187931 = 3281897) B3281897
theorem B7009301 : Blo 2187435 7009301 := bbase (se 6 (by rfl) ⟨164280, by rfl⟩ : syracuseStep 7009301 = 328561) (by norm_num)
theorem B18691469 : Blo 2187435 18691469 := bstep (se 3 (by rfl) ⟨3504650, by rfl⟩ : syracuseStep 18691469 = 7009301) B7009301
theorem B12460979 : Blo 2187435 12460979 := bstep (se 1 (by rfl) ⟨9345734, by rfl⟩ : syracuseStep 12460979 = 18691469) B18691469
theorem B8307319 : Blo 2187435 8307319 := bstep (se 1 (by rfl) ⟨6230489, by rfl⟩ : syracuseStep 8307319 = 12460979) B12460979
theorem B11076425 : Blo 2187435 11076425 := bstep (se 2 (by rfl) ⟨4153659, by rfl⟩ : syracuseStep 11076425 = 8307319) B8307319
theorem B7384283 : Blo 2187435 7384283 := bstep (se 1 (by rfl) ⟨5538212, by rfl⟩ : syracuseStep 7384283 = 11076425) B11076425
theorem B4922855 : Blo 2187435 4922855 := bstep (se 1 (by rfl) ⟨3692141, by rfl⟩ : syracuseStep 4922855 = 7384283) B7384283
theorem B3281903 : Blo 2187435 3281903 := bstep (se 1 (by rfl) ⟨2461427, by rfl⟩ : syracuseStep 3281903 = 4922855) B4922855
theorem B2187935 : Blo 2187435 2187935 := bstep (se 1 (by rfl) ⟨1640951, by rfl⟩ : syracuseStep 2187935 = 3281903) B3281903
theorem B3281909 : Blo 2187435 3281909 := bbase (se 5 (by rfl) ⟨153839, by rfl⟩ : syracuseStep 3281909 = 307679) (by norm_num)
theorem B2187939 : Blo 2187435 2187939 := bstep (se 1 (by rfl) ⟨1640954, by rfl⟩ : syracuseStep 2187939 = 3281909) B3281909
theorem B4672885 : Blo 2187435 4672885 := bbase (se 5 (by rfl) ⟨219041, by rfl⟩ : syracuseStep 4672885 = 438083) (by norm_num)
theorem B6230513 : Blo 2187435 6230513 := bstep (se 2 (by rfl) ⟨2336442, by rfl⟩ : syracuseStep 6230513 = 4672885) B4672885
theorem B4153675 : Blo 2187435 4153675 := bstep (se 1 (by rfl) ⟨3115256, by rfl⟩ : syracuseStep 4153675 = 6230513) B6230513
theorem B5538233 : Blo 2187435 5538233 := bstep (se 2 (by rfl) ⟨2076837, by rfl⟩ : syracuseStep 5538233 = 4153675) B4153675
theorem B3692155 : Blo 2187435 3692155 := bstep (se 1 (by rfl) ⟨2769116, by rfl⟩ : syracuseStep 3692155 = 5538233) B5538233
theorem B4922873 : Blo 2187435 4922873 := bstep (se 2 (by rfl) ⟨1846077, by rfl⟩ : syracuseStep 4922873 = 3692155) B3692155
theorem B3281915 : Blo 2187435 3281915 := bstep (se 1 (by rfl) ⟨2461436, by rfl⟩ : syracuseStep 3281915 = 4922873) B4922873
theorem B2187943 : Blo 2187435 2187943 := bstep (se 1 (by rfl) ⟨1640957, by rfl⟩ : syracuseStep 2187943 = 3281915) B3281915
theorem B2461441 : Blo 2187435 2461441 := bbase (se 2 (by rfl) ⟨923040, by rfl⟩ : syracuseStep 2461441 = 1846081) (by norm_num)
theorem B3281921 : Blo 2187435 3281921 := bstep (se 2 (by rfl) ⟨1230720, by rfl⟩ : syracuseStep 3281921 = 2461441) B2461441
theorem B2187947 : Blo 2187435 2187947 := bstep (se 1 (by rfl) ⟨1640960, by rfl⟩ : syracuseStep 2187947 = 3281921) B3281921
theorem B5538253 : Blo 2187435 5538253 := bbase (se 3 (by rfl) ⟨1038422, by rfl⟩ : syracuseStep 5538253 = 2076845) (by norm_num)
theorem B7384337 : Blo 2187435 7384337 := bstep (se 2 (by rfl) ⟨2769126, by rfl⟩ : syracuseStep 7384337 = 5538253) B5538253
theorem B4922891 : Blo 2187435 4922891 := bstep (se 1 (by rfl) ⟨3692168, by rfl⟩ : syracuseStep 4922891 = 7384337) B7384337
theorem B3281927 : Blo 2187435 3281927 := bstep (se 1 (by rfl) ⟨2461445, by rfl⟩ : syracuseStep 3281927 = 4922891) B4922891
theorem B2187951 : Blo 2187435 2187951 := bstep (se 1 (by rfl) ⟨1640963, by rfl⟩ : syracuseStep 2187951 = 3281927) B3281927
theorem B3281933 : Blo 2187435 3281933 := bbase (se 3 (by rfl) ⟨615362, by rfl⟩ : syracuseStep 3281933 = 1230725) (by norm_num)
theorem B2187955 : Blo 2187435 2187955 := bstep (se 1 (by rfl) ⟨1640966, by rfl⟩ : syracuseStep 2187955 = 3281933) B3281933
theorem B4922909 : Blo 2187435 4922909 := bbase (se 3 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 4922909 = 1846091) (by norm_num)
theorem B3281939 : Blo 2187435 3281939 := bstep (se 1 (by rfl) ⟨2461454, by rfl⟩ : syracuseStep 3281939 = 4922909) B4922909
theorem B2187959 : Blo 2187435 2187959 := bstep (se 1 (by rfl) ⟨1640969, by rfl⟩ : syracuseStep 2187959 = 3281939) B3281939
theorem B3692189 : Blo 2187435 3692189 := bbase (se 3 (by rfl) ⟨692285, by rfl⟩ : syracuseStep 3692189 = 1384571) (by norm_num)
theorem B2461459 : Blo 2187435 2461459 := bstep (se 1 (by rfl) ⟨1846094, by rfl⟩ : syracuseStep 2461459 = 3692189) B3692189
theorem B3281945 : Blo 2187435 3281945 := bstep (se 2 (by rfl) ⟨1230729, by rfl⟩ : syracuseStep 3281945 = 2461459) B2461459
theorem B2187963 : Blo 2187435 2187963 := bstep (se 1 (by rfl) ⟨1640972, by rfl⟩ : syracuseStep 2187963 = 3281945) B3281945
theorem B4736693 : Blo 2187435 4736693 := bbase (se 5 (by rfl) ⟨222032, by rfl⟩ : syracuseStep 4736693 = 444065) (by norm_num)
theorem B3157795 : Blo 2187435 3157795 := bstep (se 1 (by rfl) ⟨2368346, by rfl⟩ : syracuseStep 3157795 = 4736693) B4736693
theorem B4210393 : Blo 2187435 4210393 := bstep (se 2 (by rfl) ⟨1578897, by rfl⟩ : syracuseStep 4210393 = 3157795) B3157795
theorem B5613857 : Blo 2187435 5613857 := bstep (se 2 (by rfl) ⟨2105196, by rfl⟩ : syracuseStep 5613857 = 4210393) B4210393
theorem B3742571 : Blo 2187435 3742571 := bstep (se 1 (by rfl) ⟨2806928, by rfl⟩ : syracuseStep 3742571 = 5613857) B5613857
theorem B2495047 : Blo 2187435 2495047 := bstep (se 1 (by rfl) ⟨1871285, by rfl⟩ : syracuseStep 2495047 = 3742571) B3742571
theorem B3326729 : Blo 2187435 3326729 := bstep (se 2 (by rfl) ⟨1247523, by rfl⟩ : syracuseStep 3326729 = 2495047) B2495047
theorem B8871277 : Blo 2187435 8871277 := bstep (se 3 (by rfl) ⟨1663364, by rfl⟩ : syracuseStep 8871277 = 3326729) B3326729
theorem B11828369 : Blo 2187435 11828369 := bstep (se 2 (by rfl) ⟨4435638, by rfl⟩ : syracuseStep 11828369 = 8871277) B8871277
theorem B31542317 : Blo 2187435 31542317 := bstep (se 3 (by rfl) ⟨5914184, by rfl⟩ : syracuseStep 31542317 = 11828369) B11828369
theorem B21028211 : Blo 2187435 21028211 := bstep (se 1 (by rfl) ⟨15771158, by rfl⟩ : syracuseStep 21028211 = 31542317) B31542317
theorem B14018807 : Blo 2187435 14018807 := bstep (se 1 (by rfl) ⟨10514105, by rfl⟩ : syracuseStep 14018807 = 21028211) B21028211
theorem B9345871 : Blo 2187435 9345871 := bstep (se 1 (by rfl) ⟨7009403, by rfl⟩ : syracuseStep 9345871 = 14018807) B14018807
theorem B12461161 : Blo 2187435 12461161 := bstep (se 2 (by rfl) ⟨4672935, by rfl⟩ : syracuseStep 12461161 = 9345871) B9345871
theorem B16614881 : Blo 2187435 16614881 := bstep (se 2 (by rfl) ⟨6230580, by rfl⟩ : syracuseStep 16614881 = 12461161) B12461161
theorem B11076587 : Blo 2187435 11076587 := bstep (se 1 (by rfl) ⟨8307440, by rfl⟩ : syracuseStep 11076587 = 16614881) B16614881
theorem B7384391 : Blo 2187435 7384391 := bstep (se 1 (by rfl) ⟨5538293, by rfl⟩ : syracuseStep 7384391 = 11076587) B11076587
theorem B4922927 : Blo 2187435 4922927 := bstep (se 1 (by rfl) ⟨3692195, by rfl⟩ : syracuseStep 4922927 = 7384391) B7384391
theorem B3281951 : Blo 2187435 3281951 := bstep (se 1 (by rfl) ⟨2461463, by rfl⟩ : syracuseStep 3281951 = 4922927) B4922927
theorem B2187967 : Blo 2187435 2187967 := bstep (se 1 (by rfl) ⟨1640975, by rfl⟩ : syracuseStep 2187967 = 3281951) B3281951
theorem B3281957 : Blo 2187435 3281957 := bbase (se 4 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 3281957 = 615367) (by norm_num)
theorem B2187971 : Blo 2187435 2187971 := bstep (se 1 (by rfl) ⟨1640978, by rfl⟩ : syracuseStep 2187971 = 3281957) B3281957
theorem B2769157 : Blo 2187435 2769157 := bbase (se 4 (by rfl) ⟨259608, by rfl⟩ : syracuseStep 2769157 = 519217) (by norm_num)
theorem B3692209 : Blo 2187435 3692209 := bstep (se 2 (by rfl) ⟨1384578, by rfl⟩ : syracuseStep 3692209 = 2769157) B2769157
theorem B4922945 : Blo 2187435 4922945 := bstep (se 2 (by rfl) ⟨1846104, by rfl⟩ : syracuseStep 4922945 = 3692209) B3692209
theorem B3281963 : Blo 2187435 3281963 := bstep (se 1 (by rfl) ⟨2461472, by rfl⟩ : syracuseStep 3281963 = 4922945) B4922945
theorem B2187975 : Blo 2187435 2187975 := bstep (se 1 (by rfl) ⟨1640981, by rfl⟩ : syracuseStep 2187975 = 3281963) B3281963
theorem B2461477 : Blo 2187435 2461477 := bbase (se 4 (by rfl) ⟨230763, by rfl⟩ : syracuseStep 2461477 = 461527) (by norm_num)
theorem B3281969 : Blo 2187435 3281969 := bstep (se 2 (by rfl) ⟨1230738, by rfl⟩ : syracuseStep 3281969 = 2461477) B2461477
theorem B2187979 : Blo 2187435 2187979 := bstep (se 1 (by rfl) ⟨1640984, by rfl⟩ : syracuseStep 2187979 = 3281969) B3281969
theorem B9345941 : Blo 2187435 9345941 := bbase (se 6 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 9345941 = 438091) (by norm_num)
theorem B6230627 : Blo 2187435 6230627 := bstep (se 1 (by rfl) ⟨4672970, by rfl⟩ : syracuseStep 6230627 = 9345941) B9345941
theorem B4153751 : Blo 2187435 4153751 := bstep (se 1 (by rfl) ⟨3115313, by rfl⟩ : syracuseStep 4153751 = 6230627) B6230627
theorem B2769167 : Blo 2187435 2769167 := bstep (se 1 (by rfl) ⟨2076875, by rfl⟩ : syracuseStep 2769167 = 4153751) B4153751
theorem B7384445 : Blo 2187435 7384445 := bstep (se 3 (by rfl) ⟨1384583, by rfl⟩ : syracuseStep 7384445 = 2769167) B2769167
theorem B4922963 : Blo 2187435 4922963 := bstep (se 1 (by rfl) ⟨3692222, by rfl⟩ : syracuseStep 4922963 = 7384445) B7384445
theorem B3281975 : Blo 2187435 3281975 := bstep (se 1 (by rfl) ⟨2461481, by rfl⟩ : syracuseStep 3281975 = 4922963) B4922963
theorem B2187983 : Blo 2187435 2187983 := bstep (se 1 (by rfl) ⟨1640987, by rfl⟩ : syracuseStep 2187983 = 3281975) B3281975
theorem B3281981 : Blo 2187435 3281981 := bbase (se 3 (by rfl) ⟨615371, by rfl⟩ : syracuseStep 3281981 = 1230743) (by norm_num)
theorem B2187987 : Blo 2187435 2187987 := bstep (se 1 (by rfl) ⟨1640990, by rfl⟩ : syracuseStep 2187987 = 3281981) B3281981
theorem B4922981 : Blo 2187435 4922981 := bbase (se 4 (by rfl) ⟨461529, by rfl⟩ : syracuseStep 4922981 = 923059) (by norm_num)
theorem B3281987 : Blo 2187435 3281987 := bstep (se 1 (by rfl) ⟨2461490, by rfl⟩ : syracuseStep 3281987 = 4922981) B4922981
theorem B2187991 : Blo 2187435 2187991 := bstep (se 1 (by rfl) ⟨1640993, by rfl⟩ : syracuseStep 2187991 = 3281987) B3281987
theorem B5538365 : Blo 2187435 5538365 := bbase (se 3 (by rfl) ⟨1038443, by rfl⟩ : syracuseStep 5538365 = 2076887) (by norm_num)
theorem B3692243 : Blo 2187435 3692243 := bstep (se 1 (by rfl) ⟨2769182, by rfl⟩ : syracuseStep 3692243 = 5538365) B5538365
theorem B2461495 : Blo 2187435 2461495 := bstep (se 1 (by rfl) ⟨1846121, by rfl⟩ : syracuseStep 2461495 = 3692243) B3692243
theorem B3281993 : Blo 2187435 3281993 := bstep (se 2 (by rfl) ⟨1230747, by rfl⟩ : syracuseStep 3281993 = 2461495) B2461495
theorem B2187995 : Blo 2187435 2187995 := bstep (se 1 (by rfl) ⟨1640996, by rfl⟩ : syracuseStep 2187995 = 3281993) B3281993
theorem B4153781 : Blo 2187435 4153781 := bbase (se 5 (by rfl) ⟨194708, by rfl⟩ : syracuseStep 4153781 = 389417) (by norm_num)
theorem B11076749 : Blo 2187435 11076749 := bstep (se 3 (by rfl) ⟨2076890, by rfl⟩ : syracuseStep 11076749 = 4153781) B4153781
theorem B7384499 : Blo 2187435 7384499 := bstep (se 1 (by rfl) ⟨5538374, by rfl⟩ : syracuseStep 7384499 = 11076749) B11076749
theorem B4922999 : Blo 2187435 4922999 := bstep (se 1 (by rfl) ⟨3692249, by rfl⟩ : syracuseStep 4922999 = 7384499) B7384499
theorem B3281999 : Blo 2187435 3281999 := bstep (se 1 (by rfl) ⟨2461499, by rfl⟩ : syracuseStep 3281999 = 4922999) B4922999
theorem B2187999 : Blo 2187435 2187999 := bstep (se 1 (by rfl) ⟨1640999, by rfl⟩ : syracuseStep 2187999 = 3281999) B3281999
theorem B3282005 : Blo 2187435 3282005 := bbase (se 8 (by rfl) ⟨19230, by rfl⟩ : syracuseStep 3282005 = 38461) (by norm_num)
theorem B2188003 : Blo 2187435 2188003 := bstep (se 1 (by rfl) ⟨1641002, by rfl⟩ : syracuseStep 2188003 = 3282005) B3282005
theorem B9473557 : Blo 2187435 9473557 := bbase (se 6 (by rfl) ⟨222036, by rfl⟩ : syracuseStep 9473557 = 444073) (by norm_num)
theorem B12631409 : Blo 2187435 12631409 := bstep (se 2 (by rfl) ⟨4736778, by rfl⟩ : syracuseStep 12631409 = 9473557) B9473557
theorem B8420939 : Blo 2187435 8420939 := bstep (se 1 (by rfl) ⟨6315704, by rfl⟩ : syracuseStep 8420939 = 12631409) B12631409
theorem B5613959 : Blo 2187435 5613959 := bstep (se 1 (by rfl) ⟨4210469, by rfl⟩ : syracuseStep 5613959 = 8420939) B8420939
theorem B14970557 : Blo 2187435 14970557 := bstep (se 3 (by rfl) ⟨2806979, by rfl⟩ : syracuseStep 14970557 = 5613959) B5613959
theorem B9980371 : Blo 2187435 9980371 := bstep (se 1 (by rfl) ⟨7485278, by rfl⟩ : syracuseStep 9980371 = 14970557) B14970557
theorem B13307161 : Blo 2187435 13307161 := bstep (se 2 (by rfl) ⟨4990185, by rfl⟩ : syracuseStep 13307161 = 9980371) B9980371
theorem B17742881 : Blo 2187435 17742881 := bstep (se 2 (by rfl) ⟨6653580, by rfl⟩ : syracuseStep 17742881 = 13307161) B13307161
theorem B11828587 : Blo 2187435 11828587 := bstep (se 1 (by rfl) ⟨8871440, by rfl⟩ : syracuseStep 11828587 = 17742881) B17742881
theorem B15771449 : Blo 2187435 15771449 := bstep (se 2 (by rfl) ⟨5914293, by rfl⟩ : syracuseStep 15771449 = 11828587) B11828587
theorem B10514299 : Blo 2187435 10514299 := bstep (se 1 (by rfl) ⟨7885724, by rfl⟩ : syracuseStep 10514299 = 15771449) B15771449
theorem B14019065 : Blo 2187435 14019065 := bstep (se 2 (by rfl) ⟨5257149, by rfl⟩ : syracuseStep 14019065 = 10514299) B10514299
theorem B9346043 : Blo 2187435 9346043 := bstep (se 1 (by rfl) ⟨7009532, by rfl⟩ : syracuseStep 9346043 = 14019065) B14019065
theorem B6230695 : Blo 2187435 6230695 := bstep (se 1 (by rfl) ⟨4673021, by rfl⟩ : syracuseStep 6230695 = 9346043) B9346043
theorem B8307593 : Blo 2187435 8307593 := bstep (se 2 (by rfl) ⟨3115347, by rfl⟩ : syracuseStep 8307593 = 6230695) B6230695
theorem B5538395 : Blo 2187435 5538395 := bstep (se 1 (by rfl) ⟨4153796, by rfl⟩ : syracuseStep 5538395 = 8307593) B8307593
theorem B3692263 : Blo 2187435 3692263 := bstep (se 1 (by rfl) ⟨2769197, by rfl⟩ : syracuseStep 3692263 = 5538395) B5538395
theorem B4923017 : Blo 2187435 4923017 := bstep (se 2 (by rfl) ⟨1846131, by rfl⟩ : syracuseStep 4923017 = 3692263) B3692263
theorem B3282011 : Blo 2187435 3282011 := bstep (se 1 (by rfl) ⟨2461508, by rfl⟩ : syracuseStep 3282011 = 4923017) B4923017
theorem B2188007 : Blo 2187435 2188007 := bstep (se 1 (by rfl) ⟨1641005, by rfl⟩ : syracuseStep 2188007 = 3282011) B3282011
theorem B2461513 : Blo 2187435 2461513 := bbase (se 2 (by rfl) ⟨923067, by rfl⟩ : syracuseStep 2461513 = 1846135) (by norm_num)
theorem B3282017 : Blo 2187435 3282017 := bstep (se 2 (by rfl) ⟨1230756, by rfl⟩ : syracuseStep 3282017 = 2461513) B2461513
theorem B2188011 : Blo 2187435 2188011 := bstep (se 1 (by rfl) ⟨1641008, by rfl⟩ : syracuseStep 2188011 = 3282017) B3282017
theorem B11828629 : Blo 2187435 11828629 := bbase (se 6 (by rfl) ⟨277233, by rfl⟩ : syracuseStep 11828629 = 554467) (by norm_num)
theorem B15771505 : Blo 2187435 15771505 := bstep (se 2 (by rfl) ⟨5914314, by rfl⟩ : syracuseStep 15771505 = 11828629) B11828629
theorem B21028673 : Blo 2187435 21028673 := bstep (se 2 (by rfl) ⟨7885752, by rfl⟩ : syracuseStep 21028673 = 15771505) B15771505
theorem B14019115 : Blo 2187435 14019115 := bstep (se 1 (by rfl) ⟨10514336, by rfl⟩ : syracuseStep 14019115 = 21028673) B21028673
theorem B18692153 : Blo 2187435 18692153 := bstep (se 2 (by rfl) ⟨7009557, by rfl⟩ : syracuseStep 18692153 = 14019115) B14019115
theorem B12461435 : Blo 2187435 12461435 := bstep (se 1 (by rfl) ⟨9346076, by rfl⟩ : syracuseStep 12461435 = 18692153) B18692153
theorem B8307623 : Blo 2187435 8307623 := bstep (se 1 (by rfl) ⟨6230717, by rfl⟩ : syracuseStep 8307623 = 12461435) B12461435
theorem B5538415 : Blo 2187435 5538415 := bstep (se 1 (by rfl) ⟨4153811, by rfl⟩ : syracuseStep 5538415 = 8307623) B8307623
theorem B7384553 : Blo 2187435 7384553 := bstep (se 2 (by rfl) ⟨2769207, by rfl⟩ : syracuseStep 7384553 = 5538415) B5538415
theorem B4923035 : Blo 2187435 4923035 := bstep (se 1 (by rfl) ⟨3692276, by rfl⟩ : syracuseStep 4923035 = 7384553) B7384553
theorem B3282023 : Blo 2187435 3282023 := bstep (se 1 (by rfl) ⟨2461517, by rfl⟩ : syracuseStep 3282023 = 4923035) B4923035
theorem B2188015 : Blo 2187435 2188015 := bstep (se 1 (by rfl) ⟨1641011, by rfl⟩ : syracuseStep 2188015 = 3282023) B3282023
theorem B3282029 : Blo 2187435 3282029 := bbase (se 3 (by rfl) ⟨615380, by rfl⟩ : syracuseStep 3282029 = 1230761) (by norm_num)
theorem B2188019 : Blo 2187435 2188019 := bstep (se 1 (by rfl) ⟨1641014, by rfl⟩ : syracuseStep 2188019 = 3282029) B3282029
theorem B4923053 : Blo 2187435 4923053 := bbase (se 3 (by rfl) ⟨923072, by rfl⟩ : syracuseStep 4923053 = 1846145) (by norm_num)
theorem B3282035 : Blo 2187435 3282035 := bstep (se 1 (by rfl) ⟨2461526, by rfl⟩ : syracuseStep 3282035 = 4923053) B4923053
theorem B2188023 : Blo 2187435 2188023 := bstep (se 1 (by rfl) ⟨1641017, by rfl⟩ : syracuseStep 2188023 = 3282035) B3282035
theorem B29941397 : Blo 2187435 29941397 := bbase (se 6 (by rfl) ⟨701751, by rfl⟩ : syracuseStep 29941397 = 1403503) (by norm_num)
theorem B19960931 : Blo 2187435 19960931 := bstep (se 1 (by rfl) ⟨14970698, by rfl⟩ : syracuseStep 19960931 = 29941397) B29941397
theorem B13307287 : Blo 2187435 13307287 := bstep (se 1 (by rfl) ⟨9980465, by rfl⟩ : syracuseStep 13307287 = 19960931) B19960931
theorem B17743049 : Blo 2187435 17743049 := bstep (se 2 (by rfl) ⟨6653643, by rfl⟩ : syracuseStep 17743049 = 13307287) B13307287
theorem B11828699 : Blo 2187435 11828699 := bstep (se 1 (by rfl) ⟨8871524, by rfl⟩ : syracuseStep 11828699 = 17743049) B17743049
theorem B7885799 : Blo 2187435 7885799 := bstep (se 1 (by rfl) ⟨5914349, by rfl⟩ : syracuseStep 7885799 = 11828699) B11828699
theorem B5257199 : Blo 2187435 5257199 := bstep (se 1 (by rfl) ⟨3942899, by rfl⟩ : syracuseStep 5257199 = 7885799) B7885799
theorem B3504799 : Blo 2187435 3504799 := bstep (se 1 (by rfl) ⟨2628599, by rfl⟩ : syracuseStep 3504799 = 5257199) B5257199
theorem B4673065 : Blo 2187435 4673065 := bstep (se 2 (by rfl) ⟨1752399, by rfl⟩ : syracuseStep 4673065 = 3504799) B3504799
theorem B6230753 : Blo 2187435 6230753 := bstep (se 2 (by rfl) ⟨2336532, by rfl⟩ : syracuseStep 6230753 = 4673065) B4673065
theorem B4153835 : Blo 2187435 4153835 := bstep (se 1 (by rfl) ⟨3115376, by rfl⟩ : syracuseStep 4153835 = 6230753) B6230753
theorem B2769223 : Blo 2187435 2769223 := bstep (se 1 (by rfl) ⟨2076917, by rfl⟩ : syracuseStep 2769223 = 4153835) B4153835
theorem B3692297 : Blo 2187435 3692297 := bstep (se 2 (by rfl) ⟨1384611, by rfl⟩ : syracuseStep 3692297 = 2769223) B2769223
theorem B2461531 : Blo 2187435 2461531 := bstep (se 1 (by rfl) ⟨1846148, by rfl⟩ : syracuseStep 2461531 = 3692297) B3692297
theorem B3282041 : Blo 2187435 3282041 := bstep (se 2 (by rfl) ⟨1230765, by rfl⟩ : syracuseStep 3282041 = 2461531) B2461531
theorem B2188027 : Blo 2187435 2188027 := bstep (se 1 (by rfl) ⟨1641020, by rfl⟩ : syracuseStep 2188027 = 3282041) B3282041
theorem B23657429 : Blo 2187435 23657429 := bbase (se 7 (by rfl) ⟨277235, by rfl⟩ : syracuseStep 23657429 = 554471) (by norm_num)
theorem B15771619 : Blo 2187435 15771619 := bstep (se 1 (by rfl) ⟨11828714, by rfl⟩ : syracuseStep 15771619 = 23657429) B23657429
theorem B21028825 : Blo 2187435 21028825 := bstep (se 2 (by rfl) ⟨7885809, by rfl⟩ : syracuseStep 21028825 = 15771619) B15771619
theorem B28038433 : Blo 2187435 28038433 := bstep (se 2 (by rfl) ⟨10514412, by rfl⟩ : syracuseStep 28038433 = 21028825) B21028825
theorem B37384577 : Blo 2187435 37384577 := bstep (se 2 (by rfl) ⟨14019216, by rfl⟩ : syracuseStep 37384577 = 28038433) B28038433
theorem B24923051 : Blo 2187435 24923051 := bstep (se 1 (by rfl) ⟨18692288, by rfl⟩ : syracuseStep 24923051 = 37384577) B37384577
theorem B16615367 : Blo 2187435 16615367 := bstep (se 1 (by rfl) ⟨12461525, by rfl⟩ : syracuseStep 16615367 = 24923051) B24923051
theorem B11076911 : Blo 2187435 11076911 := bstep (se 1 (by rfl) ⟨8307683, by rfl⟩ : syracuseStep 11076911 = 16615367) B16615367
theorem B7384607 : Blo 2187435 7384607 := bstep (se 1 (by rfl) ⟨5538455, by rfl⟩ : syracuseStep 7384607 = 11076911) B11076911
theorem B4923071 : Blo 2187435 4923071 := bstep (se 1 (by rfl) ⟨3692303, by rfl⟩ : syracuseStep 4923071 = 7384607) B7384607
theorem B3282047 : Blo 2187435 3282047 := bstep (se 1 (by rfl) ⟨2461535, by rfl⟩ : syracuseStep 3282047 = 4923071) B4923071
theorem B2188031 : Blo 2187435 2188031 := bstep (se 1 (by rfl) ⟨1641023, by rfl⟩ : syracuseStep 2188031 = 3282047) B3282047
theorem B3282053 : Blo 2187435 3282053 := bbase (se 4 (by rfl) ⟨307692, by rfl⟩ : syracuseStep 3282053 = 615385) (by norm_num)
theorem B2188035 : Blo 2187435 2188035 := bstep (se 1 (by rfl) ⟨1641026, by rfl⟩ : syracuseStep 2188035 = 3282053) B3282053
theorem B3692317 : Blo 2187435 3692317 := bbase (se 3 (by rfl) ⟨692309, by rfl⟩ : syracuseStep 3692317 = 1384619) (by norm_num)
theorem B4923089 : Blo 2187435 4923089 := bstep (se 2 (by rfl) ⟨1846158, by rfl⟩ : syracuseStep 4923089 = 3692317) B3692317
theorem B3282059 : Blo 2187435 3282059 := bstep (se 1 (by rfl) ⟨2461544, by rfl⟩ : syracuseStep 3282059 = 4923089) B4923089
theorem B2188039 : Blo 2187435 2188039 := bstep (se 1 (by rfl) ⟨1641029, by rfl⟩ : syracuseStep 2188039 = 3282059) B3282059
theorem B2461549 : Blo 2187435 2461549 := bbase (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) (by norm_num)
theorem B3282065 : Blo 2187435 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B2188043 : Blo 2187435 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B7384661 : Blo 2187435 7384661 := bbase (se 8 (by rfl) ⟨43269, by rfl⟩ : syracuseStep 7384661 = 86539) (by norm_num)
theorem B4923107 : Blo 2187435 4923107 := bstep (se 1 (by rfl) ⟨3692330, by rfl⟩ : syracuseStep 4923107 = 7384661) B7384661
theorem B3282071 : Blo 2187435 3282071 := bstep (se 1 (by rfl) ⟨2461553, by rfl⟩ : syracuseStep 3282071 = 4923107) B4923107
theorem B2188047 : Blo 2187435 2188047 := bstep (se 1 (by rfl) ⟨1641035, by rfl⟩ : syracuseStep 2188047 = 3282071) B3282071
theorem B3282077 : Blo 2187435 3282077 := bbase (se 3 (by rfl) ⟨615389, by rfl⟩ : syracuseStep 3282077 = 1230779) (by norm_num)
theorem B2188051 : Blo 2187435 2188051 := bstep (se 1 (by rfl) ⟨1641038, by rfl⟩ : syracuseStep 2188051 = 3282077) B3282077
theorem B4923125 : Blo 2187435 4923125 := bbase (se 5 (by rfl) ⟨230771, by rfl⟩ : syracuseStep 4923125 = 461543) (by norm_num)
theorem B3282083 : Blo 2187435 3282083 := bstep (se 1 (by rfl) ⟨2461562, by rfl⟩ : syracuseStep 3282083 = 4923125) B4923125
theorem B2188055 : Blo 2187435 2188055 := bstep (se 1 (by rfl) ⟨1641041, by rfl⟩ : syracuseStep 2188055 = 3282083) B3282083
theorem B10514549 : Blo 2187435 10514549 := bbase (se 5 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 10514549 = 985739) (by norm_num)
theorem B28038797 : Blo 2187435 28038797 := bstep (se 3 (by rfl) ⟨5257274, by rfl⟩ : syracuseStep 28038797 = 10514549) B10514549
theorem B18692531 : Blo 2187435 18692531 := bstep (se 1 (by rfl) ⟨14019398, by rfl⟩ : syracuseStep 18692531 = 28038797) B28038797
theorem B12461687 : Blo 2187435 12461687 := bstep (se 1 (by rfl) ⟨9346265, by rfl⟩ : syracuseStep 12461687 = 18692531) B18692531
theorem B8307791 : Blo 2187435 8307791 := bstep (se 1 (by rfl) ⟨6230843, by rfl⟩ : syracuseStep 8307791 = 12461687) B12461687
theorem B5538527 : Blo 2187435 5538527 := bstep (se 1 (by rfl) ⟨4153895, by rfl⟩ : syracuseStep 5538527 = 8307791) B8307791
theorem B3692351 : Blo 2187435 3692351 := bstep (se 1 (by rfl) ⟨2769263, by rfl⟩ : syracuseStep 3692351 = 5538527) B5538527
theorem B2461567 : Blo 2187435 2461567 := bstep (se 1 (by rfl) ⟨1846175, by rfl⟩ : syracuseStep 2461567 = 3692351) B3692351
theorem B3282089 : Blo 2187435 3282089 := bstep (se 2 (by rfl) ⟨1230783, by rfl⟩ : syracuseStep 3282089 = 2461567) B2461567
theorem B2188059 : Blo 2187435 2188059 := bstep (se 1 (by rfl) ⟨1641044, by rfl⟩ : syracuseStep 2188059 = 3282089) B3282089
theorem B4673141 : Blo 2187435 4673141 := bbase (se 5 (by rfl) ⟨219053, by rfl⟩ : syracuseStep 4673141 = 438107) (by norm_num)
theorem B3115427 : Blo 2187435 3115427 := bstep (se 1 (by rfl) ⟨2336570, by rfl⟩ : syracuseStep 3115427 = 4673141) B4673141
theorem B8307805 : Blo 2187435 8307805 := bstep (se 3 (by rfl) ⟨1557713, by rfl⟩ : syracuseStep 8307805 = 3115427) B3115427
theorem B11077073 : Blo 2187435 11077073 := bstep (se 2 (by rfl) ⟨4153902, by rfl⟩ : syracuseStep 11077073 = 8307805) B8307805
theorem B7384715 : Blo 2187435 7384715 := bstep (se 1 (by rfl) ⟨5538536, by rfl⟩ : syracuseStep 7384715 = 11077073) B11077073
theorem B4923143 : Blo 2187435 4923143 := bstep (se 1 (by rfl) ⟨3692357, by rfl⟩ : syracuseStep 4923143 = 7384715) B7384715
theorem B3282095 : Blo 2187435 3282095 := bstep (se 1 (by rfl) ⟨2461571, by rfl⟩ : syracuseStep 3282095 = 4923143) B4923143
theorem B2188063 : Blo 2187435 2188063 := bstep (se 1 (by rfl) ⟨1641047, by rfl⟩ : syracuseStep 2188063 = 3282095) B3282095
theorem B3282101 : Blo 2187435 3282101 := bbase (se 5 (by rfl) ⟨153848, by rfl⟩ : syracuseStep 3282101 = 307697) (by norm_num)
theorem B2188067 : Blo 2187435 2188067 := bstep (se 1 (by rfl) ⟨1641050, by rfl⟩ : syracuseStep 2188067 = 3282101) B3282101
theorem B5538557 : Blo 2187435 5538557 := bbase (se 3 (by rfl) ⟨1038479, by rfl⟩ : syracuseStep 5538557 = 2076959) (by norm_num)
theorem B3692371 : Blo 2187435 3692371 := bstep (se 1 (by rfl) ⟨2769278, by rfl⟩ : syracuseStep 3692371 = 5538557) B5538557
theorem B4923161 : Blo 2187435 4923161 := bstep (se 2 (by rfl) ⟨1846185, by rfl⟩ : syracuseStep 4923161 = 3692371) B3692371
theorem B3282107 : Blo 2187435 3282107 := bstep (se 1 (by rfl) ⟨2461580, by rfl⟩ : syracuseStep 3282107 = 4923161) B4923161
theorem B2188071 : Blo 2187435 2188071 := bstep (se 1 (by rfl) ⟨1641053, by rfl⟩ : syracuseStep 2188071 = 3282107) B3282107
theorem B2461585 : Blo 2187435 2461585 := bbase (se 2 (by rfl) ⟨923094, by rfl⟩ : syracuseStep 2461585 = 1846189) (by norm_num)
theorem B3282113 : Blo 2187435 3282113 := bstep (se 2 (by rfl) ⟨1230792, by rfl⟩ : syracuseStep 3282113 = 2461585) B2461585
theorem B2188075 : Blo 2187435 2188075 := bstep (se 1 (by rfl) ⟨1641056, by rfl⟩ : syracuseStep 2188075 = 3282113) B3282113
theorem B4153933 : Blo 2187435 4153933 := bbase (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) (by norm_num)
theorem B5538577 : Blo 2187435 5538577 := bstep (se 2 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 5538577 = 4153933) B4153933
theorem B7384769 : Blo 2187435 7384769 := bstep (se 2 (by rfl) ⟨2769288, by rfl⟩ : syracuseStep 7384769 = 5538577) B5538577
theorem B4923179 : Blo 2187435 4923179 := bstep (se 1 (by rfl) ⟨3692384, by rfl⟩ : syracuseStep 4923179 = 7384769) B7384769
theorem B3282119 : Blo 2187435 3282119 := bstep (se 1 (by rfl) ⟨2461589, by rfl⟩ : syracuseStep 3282119 = 4923179) B4923179
theorem B2188079 : Blo 2187435 2188079 := bstep (se 1 (by rfl) ⟨1641059, by rfl⟩ : syracuseStep 2188079 = 3282119) B3282119
theorem B3282125 : Blo 2187435 3282125 := bbase (se 3 (by rfl) ⟨615398, by rfl⟩ : syracuseStep 3282125 = 1230797) (by norm_num)
theorem B2188083 : Blo 2187435 2188083 := bstep (se 1 (by rfl) ⟨1641062, by rfl⟩ : syracuseStep 2188083 = 3282125) B3282125
theorem B4923197 : Blo 2187435 4923197 := bbase (se 3 (by rfl) ⟨923099, by rfl⟩ : syracuseStep 4923197 = 1846199) (by norm_num)
theorem B3282131 : Blo 2187435 3282131 := bstep (se 1 (by rfl) ⟨2461598, by rfl⟩ : syracuseStep 3282131 = 4923197) B4923197
theorem B2188087 : Blo 2187435 2188087 := bstep (se 1 (by rfl) ⟨1641065, by rfl⟩ : syracuseStep 2188087 = 3282131) B3282131
theorem B3692405 : Blo 2187435 3692405 := bbase (se 5 (by rfl) ⟨173081, by rfl⟩ : syracuseStep 3692405 = 346163) (by norm_num)
theorem B2461603 : Blo 2187435 2461603 := bstep (se 1 (by rfl) ⟨1846202, by rfl⟩ : syracuseStep 2461603 = 3692405) B3692405
theorem B3282137 : Blo 2187435 3282137 := bstep (se 2 (by rfl) ⟨1230801, by rfl⟩ : syracuseStep 3282137 = 2461603) B2461603
theorem B2188091 : Blo 2187435 2188091 := bstep (se 1 (by rfl) ⟨1641068, by rfl⟩ : syracuseStep 2188091 = 3282137) B3282137
theorem B3943021 : Blo 2187435 3943021 := bbase (se 3 (by rfl) ⟨739316, by rfl⟩ : syracuseStep 3943021 = 1478633) (by norm_num)
theorem B5257361 : Blo 2187435 5257361 := bstep (se 2 (by rfl) ⟨1971510, by rfl⟩ : syracuseStep 5257361 = 3943021) B3943021
theorem B3504907 : Blo 2187435 3504907 := bstep (se 1 (by rfl) ⟨2628680, by rfl⟩ : syracuseStep 3504907 = 5257361) B5257361
theorem B4673209 : Blo 2187435 4673209 := bstep (se 2 (by rfl) ⟨1752453, by rfl⟩ : syracuseStep 4673209 = 3504907) B3504907
theorem B6230945 : Blo 2187435 6230945 := bstep (se 2 (by rfl) ⟨2336604, by rfl⟩ : syracuseStep 6230945 = 4673209) B4673209
theorem B16615853 : Blo 2187435 16615853 := bstep (se 3 (by rfl) ⟨3115472, by rfl⟩ : syracuseStep 16615853 = 6230945) B6230945
theorem B11077235 : Blo 2187435 11077235 := bstep (se 1 (by rfl) ⟨8307926, by rfl⟩ : syracuseStep 11077235 = 16615853) B16615853
theorem B7384823 : Blo 2187435 7384823 := bstep (se 1 (by rfl) ⟨5538617, by rfl⟩ : syracuseStep 7384823 = 11077235) B11077235
theorem B4923215 : Blo 2187435 4923215 := bstep (se 1 (by rfl) ⟨3692411, by rfl⟩ : syracuseStep 4923215 = 7384823) B7384823
theorem B3282143 : Blo 2187435 3282143 := bstep (se 1 (by rfl) ⟨2461607, by rfl⟩ : syracuseStep 3282143 = 4923215) B4923215
theorem B2188095 : Blo 2187435 2188095 := bstep (se 1 (by rfl) ⟨1641071, by rfl⟩ : syracuseStep 2188095 = 3282143) B3282143
theorem B3282149 : Blo 2187435 3282149 := bbase (se 4 (by rfl) ⟨307701, by rfl⟩ : syracuseStep 3282149 = 615403) (by norm_num)
theorem B2188099 : Blo 2187435 2188099 := bstep (se 1 (by rfl) ⟨1641074, by rfl⟩ : syracuseStep 2188099 = 3282149) B3282149
theorem B5257381 : Blo 2187435 5257381 := bbase (se 4 (by rfl) ⟨492879, by rfl⟩ : syracuseStep 5257381 = 985759) (by norm_num)
theorem B7009841 : Blo 2187435 7009841 := bstep (se 2 (by rfl) ⟨2628690, by rfl⟩ : syracuseStep 7009841 = 5257381) B5257381
theorem B4673227 : Blo 2187435 4673227 := bstep (se 1 (by rfl) ⟨3504920, by rfl⟩ : syracuseStep 4673227 = 7009841) B7009841
theorem B6230969 : Blo 2187435 6230969 := bstep (se 2 (by rfl) ⟨2336613, by rfl⟩ : syracuseStep 6230969 = 4673227) B4673227
theorem B4153979 : Blo 2187435 4153979 := bstep (se 1 (by rfl) ⟨3115484, by rfl⟩ : syracuseStep 4153979 = 6230969) B6230969
theorem B2769319 : Blo 2187435 2769319 := bstep (se 1 (by rfl) ⟨2076989, by rfl⟩ : syracuseStep 2769319 = 4153979) B4153979
theorem B3692425 : Blo 2187435 3692425 := bstep (se 2 (by rfl) ⟨1384659, by rfl⟩ : syracuseStep 3692425 = 2769319) B2769319
theorem B4923233 : Blo 2187435 4923233 := bstep (se 2 (by rfl) ⟨1846212, by rfl⟩ : syracuseStep 4923233 = 3692425) B3692425
theorem B3282155 : Blo 2187435 3282155 := bstep (se 1 (by rfl) ⟨2461616, by rfl⟩ : syracuseStep 3282155 = 4923233) B4923233
theorem B2188103 : Blo 2187435 2188103 := bstep (se 1 (by rfl) ⟨1641077, by rfl⟩ : syracuseStep 2188103 = 3282155) B3282155
theorem B2461621 : Blo 2187435 2461621 := bbase (se 5 (by rfl) ⟨115388, by rfl⟩ : syracuseStep 2461621 = 230777) (by norm_num)
theorem B3282161 : Blo 2187435 3282161 := bstep (se 2 (by rfl) ⟨1230810, by rfl⟩ : syracuseStep 3282161 = 2461621) B2461621
theorem B2188107 : Blo 2187435 2188107 := bstep (se 1 (by rfl) ⟨1641080, by rfl⟩ : syracuseStep 2188107 = 3282161) B3282161
theorem B2769329 : Blo 2187435 2769329 := bbase (se 2 (by rfl) ⟨1038498, by rfl⟩ : syracuseStep 2769329 = 2076997) (by norm_num)
theorem B7384877 : Blo 2187435 7384877 := bstep (se 3 (by rfl) ⟨1384664, by rfl⟩ : syracuseStep 7384877 = 2769329) B2769329
theorem B4923251 : Blo 2187435 4923251 := bstep (se 1 (by rfl) ⟨3692438, by rfl⟩ : syracuseStep 4923251 = 7384877) B7384877
theorem B3282167 : Blo 2187435 3282167 := bstep (se 1 (by rfl) ⟨2461625, by rfl⟩ : syracuseStep 3282167 = 4923251) B4923251
theorem B2188111 : Blo 2187435 2188111 := bstep (se 1 (by rfl) ⟨1641083, by rfl⟩ : syracuseStep 2188111 = 3282167) B3282167
theorem B3282173 : Blo 2187435 3282173 := bbase (se 3 (by rfl) ⟨615407, by rfl⟩ : syracuseStep 3282173 = 1230815) (by norm_num)
theorem B2188115 : Blo 2187435 2188115 := bstep (se 1 (by rfl) ⟨1641086, by rfl⟩ : syracuseStep 2188115 = 3282173) B3282173
theorem B4923269 : Blo 2187435 4923269 := bbase (se 4 (by rfl) ⟨461556, by rfl⟩ : syracuseStep 4923269 = 923113) (by norm_num)
theorem B3282179 : Blo 2187435 3282179 := bstep (se 1 (by rfl) ⟨2461634, by rfl⟩ : syracuseStep 3282179 = 4923269) B4923269
theorem B2188119 : Blo 2187435 2188119 := bstep (se 1 (by rfl) ⟨1641089, by rfl⟩ : syracuseStep 2188119 = 3282179) B3282179
theorem B5329165 : Blo 2187435 5329165 := bbase (se 3 (by rfl) ⟨999218, by rfl⟩ : syracuseStep 5329165 = 1998437) (by norm_num)
theorem B7105553 : Blo 2187435 7105553 := bstep (se 2 (by rfl) ⟨2664582, by rfl⟩ : syracuseStep 7105553 = 5329165) B5329165
theorem B4737035 : Blo 2187435 4737035 := bstep (se 1 (by rfl) ⟨3552776, by rfl⟩ : syracuseStep 4737035 = 7105553) B7105553
theorem B3158023 : Blo 2187435 3158023 := bstep (se 1 (by rfl) ⟨2368517, by rfl⟩ : syracuseStep 3158023 = 4737035) B4737035
theorem B4210697 : Blo 2187435 4210697 := bstep (se 2 (by rfl) ⟨1579011, by rfl⟩ : syracuseStep 4210697 = 3158023) B3158023
theorem B2807131 : Blo 2187435 2807131 := bstep (se 1 (by rfl) ⟨2105348, by rfl⟩ : syracuseStep 2807131 = 4210697) B4210697
theorem B3742841 : Blo 2187435 3742841 := bstep (se 2 (by rfl) ⟨1403565, by rfl⟩ : syracuseStep 3742841 = 2807131) B2807131
theorem B2495227 : Blo 2187435 2495227 := bstep (se 1 (by rfl) ⟨1871420, by rfl⟩ : syracuseStep 2495227 = 3742841) B3742841
theorem B3326969 : Blo 2187435 3326969 := bstep (se 2 (by rfl) ⟨1247613, by rfl⟩ : syracuseStep 3326969 = 2495227) B2495227
theorem B2217979 : Blo 2187435 2217979 := bstep (se 1 (by rfl) ⟨1663484, by rfl⟩ : syracuseStep 2217979 = 3326969) B3326969
theorem B2957305 : Blo 2187435 2957305 := bstep (se 2 (by rfl) ⟨1108989, by rfl⟩ : syracuseStep 2957305 = 2217979) B2217979
theorem B3943073 : Blo 2187435 3943073 := bstep (se 2 (by rfl) ⟨1478652, by rfl⟩ : syracuseStep 3943073 = 2957305) B2957305
theorem B2628715 : Blo 2187435 2628715 := bstep (se 1 (by rfl) ⟨1971536, by rfl⟩ : syracuseStep 2628715 = 3943073) B3943073
theorem B3504953 : Blo 2187435 3504953 := bstep (se 2 (by rfl) ⟨1314357, by rfl⟩ : syracuseStep 3504953 = 2628715) B2628715
theorem B2336635 : Blo 2187435 2336635 := bstep (se 1 (by rfl) ⟨1752476, by rfl⟩ : syracuseStep 2336635 = 3504953) B3504953
theorem B3115513 : Blo 2187435 3115513 := bstep (se 2 (by rfl) ⟨1168317, by rfl⟩ : syracuseStep 3115513 = 2336635) B2336635
theorem B4154017 : Blo 2187435 4154017 := bstep (se 2 (by rfl) ⟨1557756, by rfl⟩ : syracuseStep 4154017 = 3115513) B3115513
theorem B5538689 : Blo 2187435 5538689 := bstep (se 2 (by rfl) ⟨2077008, by rfl⟩ : syracuseStep 5538689 = 4154017) B4154017
theorem B3692459 : Blo 2187435 3692459 := bstep (se 1 (by rfl) ⟨2769344, by rfl⟩ : syracuseStep 3692459 = 5538689) B5538689
theorem B2461639 : Blo 2187435 2461639 := bstep (se 1 (by rfl) ⟨1846229, by rfl⟩ : syracuseStep 2461639 = 3692459) B3692459
theorem B3282185 : Blo 2187435 3282185 := bstep (se 2 (by rfl) ⟨1230819, by rfl⟩ : syracuseStep 3282185 = 2461639) B2461639
theorem B2188123 : Blo 2187435 2188123 := bstep (se 1 (by rfl) ⟨1641092, by rfl⟩ : syracuseStep 2188123 = 3282185) B3282185
theorem B11077397 : Blo 2187435 11077397 := bbase (se 6 (by rfl) ⟨259626, by rfl⟩ : syracuseStep 11077397 = 519253) (by norm_num)
theorem B7384931 : Blo 2187435 7384931 := bstep (se 1 (by rfl) ⟨5538698, by rfl⟩ : syracuseStep 7384931 = 11077397) B11077397
theorem B4923287 : Blo 2187435 4923287 := bstep (se 1 (by rfl) ⟨3692465, by rfl⟩ : syracuseStep 4923287 = 7384931) B7384931
theorem B3282191 : Blo 2187435 3282191 := bstep (se 1 (by rfl) ⟨2461643, by rfl⟩ : syracuseStep 3282191 = 4923287) B4923287
theorem B2188127 : Blo 2187435 2188127 := bstep (se 1 (by rfl) ⟨1641095, by rfl⟩ : syracuseStep 2188127 = 3282191) B3282191
theorem B3282197 : Blo 2187435 3282197 := bbase (se 6 (by rfl) ⟨76926, by rfl⟩ : syracuseStep 3282197 = 153853) (by norm_num)
theorem B2188131 : Blo 2187435 2188131 := bstep (se 1 (by rfl) ⟨1641098, by rfl⟩ : syracuseStep 2188131 = 3282197) B3282197
theorem B19961909 : Blo 2187435 19961909 := bbase (se 5 (by rfl) ⟨935714, by rfl⟩ : syracuseStep 19961909 = 1871429) (by norm_num)
theorem B13307939 : Blo 2187435 13307939 := bstep (se 1 (by rfl) ⟨9980954, by rfl⟩ : syracuseStep 13307939 = 19961909) B19961909
theorem B8871959 : Blo 2187435 8871959 := bstep (se 1 (by rfl) ⟨6653969, by rfl⟩ : syracuseStep 8871959 = 13307939) B13307939
theorem B5914639 : Blo 2187435 5914639 := bstep (se 1 (by rfl) ⟨4435979, by rfl⟩ : syracuseStep 5914639 = 8871959) B8871959
theorem B31544741 : Blo 2187435 31544741 := bstep (se 4 (by rfl) ⟨2957319, by rfl⟩ : syracuseStep 31544741 = 5914639) B5914639
theorem B21029827 : Blo 2187435 21029827 := bstep (se 1 (by rfl) ⟨15772370, by rfl⟩ : syracuseStep 21029827 = 31544741) B31544741
theorem B28039769 : Blo 2187435 28039769 := bstep (se 2 (by rfl) ⟨10514913, by rfl⟩ : syracuseStep 28039769 = 21029827) B21029827
theorem B18693179 : Blo 2187435 18693179 := bstep (se 1 (by rfl) ⟨14019884, by rfl⟩ : syracuseStep 18693179 = 28039769) B28039769
theorem B12462119 : Blo 2187435 12462119 := bstep (se 1 (by rfl) ⟨9346589, by rfl⟩ : syracuseStep 12462119 = 18693179) B18693179
theorem B8308079 : Blo 2187435 8308079 := bstep (se 1 (by rfl) ⟨6231059, by rfl⟩ : syracuseStep 8308079 = 12462119) B12462119
theorem B5538719 : Blo 2187435 5538719 := bstep (se 1 (by rfl) ⟨4154039, by rfl⟩ : syracuseStep 5538719 = 8308079) B8308079
theorem B3692479 : Blo 2187435 3692479 := bstep (se 1 (by rfl) ⟨2769359, by rfl⟩ : syracuseStep 3692479 = 5538719) B5538719
theorem B4923305 : Blo 2187435 4923305 := bstep (se 2 (by rfl) ⟨1846239, by rfl⟩ : syracuseStep 4923305 = 3692479) B3692479
theorem B3282203 : Blo 2187435 3282203 := bstep (se 1 (by rfl) ⟨2461652, by rfl⟩ : syracuseStep 3282203 = 4923305) B4923305
theorem B2188135 : Blo 2187435 2188135 := bstep (se 1 (by rfl) ⟨1641101, by rfl⟩ : syracuseStep 2188135 = 3282203) B3282203
theorem B2461657 : Blo 2187435 2461657 := bbase (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) (by norm_num)
theorem B3282209 : Blo 2187435 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B2188139 : Blo 2187435 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B3115541 : Blo 2187435 3115541 := bbase (se 6 (by rfl) ⟨73020, by rfl⟩ : syracuseStep 3115541 = 146041) (by norm_num)
theorem B8308109 : Blo 2187435 8308109 := bstep (se 3 (by rfl) ⟨1557770, by rfl⟩ : syracuseStep 8308109 = 3115541) B3115541
theorem B5538739 : Blo 2187435 5538739 := bstep (se 1 (by rfl) ⟨4154054, by rfl⟩ : syracuseStep 5538739 = 8308109) B8308109
theorem B7384985 : Blo 2187435 7384985 := bstep (se 2 (by rfl) ⟨2769369, by rfl⟩ : syracuseStep 7384985 = 5538739) B5538739
theorem B4923323 : Blo 2187435 4923323 := bstep (se 1 (by rfl) ⟨3692492, by rfl⟩ : syracuseStep 4923323 = 7384985) B7384985
theorem B3282215 : Blo 2187435 3282215 := bstep (se 1 (by rfl) ⟨2461661, by rfl⟩ : syracuseStep 3282215 = 4923323) B4923323
theorem B2188143 : Blo 2187435 2188143 := bstep (se 1 (by rfl) ⟨1641107, by rfl⟩ : syracuseStep 2188143 = 3282215) B3282215
theorem B3282221 : Blo 2187435 3282221 := bbase (se 3 (by rfl) ⟨615416, by rfl⟩ : syracuseStep 3282221 = 1230833) (by norm_num)
theorem B2188147 : Blo 2187435 2188147 := bstep (se 1 (by rfl) ⟨1641110, by rfl⟩ : syracuseStep 2188147 = 3282221) B3282221
theorem B4923341 : Blo 2187435 4923341 := bbase (se 3 (by rfl) ⟨923126, by rfl⟩ : syracuseStep 4923341 = 1846253) (by norm_num)
theorem B3282227 : Blo 2187435 3282227 := bstep (se 1 (by rfl) ⟨2461670, by rfl⟩ : syracuseStep 3282227 = 4923341) B4923341
theorem B2188151 : Blo 2187435 2188151 := bstep (se 1 (by rfl) ⟨1641113, by rfl⟩ : syracuseStep 2188151 = 3282227) B3282227
theorem B2769385 : Blo 2187435 2769385 := bbase (se 2 (by rfl) ⟨1038519, by rfl⟩ : syracuseStep 2769385 = 2077039) (by norm_num)
theorem B3692513 : Blo 2187435 3692513 := bstep (se 2 (by rfl) ⟨1384692, by rfl⟩ : syracuseStep 3692513 = 2769385) B2769385
theorem B2461675 : Blo 2187435 2461675 := bstep (se 1 (by rfl) ⟨1846256, by rfl⟩ : syracuseStep 2461675 = 3692513) B3692513
theorem B3282233 : Blo 2187435 3282233 := bstep (se 2 (by rfl) ⟨1230837, by rfl⟩ : syracuseStep 3282233 = 2461675) B2461675
theorem B2188155 : Blo 2187435 2188155 := bstep (se 1 (by rfl) ⟨1641116, by rfl⟩ : syracuseStep 2188155 = 3282233) B3282233
theorem B2628757 : Blo 2187435 2628757 := bbase (se 6 (by rfl) ⟨61611, by rfl⟩ : syracuseStep 2628757 = 123223) (by norm_num)
theorem B14020037 : Blo 2187435 14020037 := bstep (se 4 (by rfl) ⟨1314378, by rfl⟩ : syracuseStep 14020037 = 2628757) B2628757
theorem B9346691 : Blo 2187435 9346691 := bstep (se 1 (by rfl) ⟨7010018, by rfl⟩ : syracuseStep 9346691 = 14020037) B14020037
theorem B24924509 : Blo 2187435 24924509 := bstep (se 3 (by rfl) ⟨4673345, by rfl⟩ : syracuseStep 24924509 = 9346691) B9346691
theorem B16616339 : Blo 2187435 16616339 := bstep (se 1 (by rfl) ⟨12462254, by rfl⟩ : syracuseStep 16616339 = 24924509) B24924509
theorem B11077559 : Blo 2187435 11077559 := bstep (se 1 (by rfl) ⟨8308169, by rfl⟩ : syracuseStep 11077559 = 16616339) B16616339
theorem B7385039 : Blo 2187435 7385039 := bstep (se 1 (by rfl) ⟨5538779, by rfl⟩ : syracuseStep 7385039 = 11077559) B11077559
theorem B4923359 : Blo 2187435 4923359 := bstep (se 1 (by rfl) ⟨3692519, by rfl⟩ : syracuseStep 4923359 = 7385039) B7385039
theorem B3282239 : Blo 2187435 3282239 := bstep (se 1 (by rfl) ⟨2461679, by rfl⟩ : syracuseStep 3282239 = 4923359) B4923359
theorem B2188159 : Blo 2187435 2188159 := bstep (se 1 (by rfl) ⟨1641119, by rfl⟩ : syracuseStep 2188159 = 3282239) B3282239
theorem B3282245 : Blo 2187435 3282245 := bbase (se 4 (by rfl) ⟨307710, by rfl⟩ : syracuseStep 3282245 = 615421) (by norm_num)
theorem B2188163 : Blo 2187435 2188163 := bstep (se 1 (by rfl) ⟨1641122, by rfl⟩ : syracuseStep 2188163 = 3282245) B3282245
theorem B3692533 : Blo 2187435 3692533 := bbase (se 5 (by rfl) ⟨173087, by rfl⟩ : syracuseStep 3692533 = 346175) (by norm_num)
theorem B4923377 : Blo 2187435 4923377 := bstep (se 2 (by rfl) ⟨1846266, by rfl⟩ : syracuseStep 4923377 = 3692533) B3692533
theorem B3282251 : Blo 2187435 3282251 := bstep (se 1 (by rfl) ⟨2461688, by rfl⟩ : syracuseStep 3282251 = 4923377) B4923377
theorem B2188167 : Blo 2187435 2188167 := bstep (se 1 (by rfl) ⟨1641125, by rfl⟩ : syracuseStep 2188167 = 3282251) B3282251
theorem B2461693 : Blo 2187435 2461693 := bbase (se 3 (by rfl) ⟨461567, by rfl⟩ : syracuseStep 2461693 = 923135) (by norm_num)
theorem B3282257 : Blo 2187435 3282257 := bstep (se 2 (by rfl) ⟨1230846, by rfl⟩ : syracuseStep 3282257 = 2461693) B2461693
theorem B2188171 : Blo 2187435 2188171 := bstep (se 1 (by rfl) ⟨1641128, by rfl⟩ : syracuseStep 2188171 = 3282257) B3282257
theorem B7385093 : Blo 2187435 7385093 := bbase (se 4 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 7385093 = 1384705) (by norm_num)
theorem B4923395 : Blo 2187435 4923395 := bstep (se 1 (by rfl) ⟨3692546, by rfl⟩ : syracuseStep 4923395 = 7385093) B7385093
theorem B3282263 : Blo 2187435 3282263 := bstep (se 1 (by rfl) ⟨2461697, by rfl⟩ : syracuseStep 3282263 = 4923395) B4923395
theorem B2188175 : Blo 2187435 2188175 := bstep (se 1 (by rfl) ⟨1641131, by rfl⟩ : syracuseStep 2188175 = 3282263) B3282263
theorem B3282269 : Blo 2187435 3282269 := bbase (se 3 (by rfl) ⟨615425, by rfl⟩ : syracuseStep 3282269 = 1230851) (by norm_num)
theorem B2188179 : Blo 2187435 2188179 := bstep (se 1 (by rfl) ⟨1641134, by rfl⟩ : syracuseStep 2188179 = 3282269) B3282269
theorem B4923413 : Blo 2187435 4923413 := bbase (se 6 (by rfl) ⟨115392, by rfl⟩ : syracuseStep 4923413 = 230785) (by norm_num)
theorem B3282275 : Blo 2187435 3282275 := bstep (se 1 (by rfl) ⟨2461706, by rfl⟩ : syracuseStep 3282275 = 4923413) B4923413
theorem B2188183 : Blo 2187435 2188183 := bstep (se 1 (by rfl) ⟨1641137, by rfl⟩ : syracuseStep 2188183 = 3282275) B3282275
theorem B8308277 : Blo 2187435 8308277 := bbase (se 5 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 8308277 = 778901) (by norm_num)
theorem B5538851 : Blo 2187435 5538851 := bstep (se 1 (by rfl) ⟨4154138, by rfl⟩ : syracuseStep 5538851 = 8308277) B8308277
theorem B3692567 : Blo 2187435 3692567 := bstep (se 1 (by rfl) ⟨2769425, by rfl⟩ : syracuseStep 3692567 = 5538851) B5538851
theorem B2461711 : Blo 2187435 2461711 := bstep (se 1 (by rfl) ⟨1846283, by rfl⟩ : syracuseStep 2461711 = 3692567) B3692567
theorem B3282281 : Blo 2187435 3282281 := bstep (se 2 (by rfl) ⟨1230855, by rfl⟩ : syracuseStep 3282281 = 2461711) B2461711
theorem B2188187 : Blo 2187435 2188187 := bstep (se 1 (by rfl) ⟨1641140, by rfl⟩ : syracuseStep 2188187 = 3282281) B3282281
theorem B3505061 : Blo 2187435 3505061 := bbase (se 4 (by rfl) ⟨328599, by rfl⟩ : syracuseStep 3505061 = 657199) (by norm_num)
theorem B2336707 : Blo 2187435 2336707 := bstep (se 1 (by rfl) ⟨1752530, by rfl⟩ : syracuseStep 2336707 = 3505061) B3505061
theorem B12462437 : Blo 2187435 12462437 := bstep (se 4 (by rfl) ⟨1168353, by rfl⟩ : syracuseStep 12462437 = 2336707) B2336707
theorem B8308291 : Blo 2187435 8308291 := bstep (se 1 (by rfl) ⟨6231218, by rfl⟩ : syracuseStep 8308291 = 12462437) B12462437
theorem B11077721 : Blo 2187435 11077721 := bstep (se 2 (by rfl) ⟨4154145, by rfl⟩ : syracuseStep 11077721 = 8308291) B8308291
theorem B7385147 : Blo 2187435 7385147 := bstep (se 1 (by rfl) ⟨5538860, by rfl⟩ : syracuseStep 7385147 = 11077721) B11077721
theorem B4923431 : Blo 2187435 4923431 := bstep (se 1 (by rfl) ⟨3692573, by rfl⟩ : syracuseStep 4923431 = 7385147) B7385147
theorem B3282287 : Blo 2187435 3282287 := bstep (se 1 (by rfl) ⟨2461715, by rfl⟩ : syracuseStep 3282287 = 4923431) B4923431
theorem B2188191 : Blo 2187435 2188191 := bstep (se 1 (by rfl) ⟨1641143, by rfl⟩ : syracuseStep 2188191 = 3282287) B3282287
theorem B3282293 : Blo 2187435 3282293 := bbase (se 5 (by rfl) ⟨153857, by rfl⟩ : syracuseStep 3282293 = 307715) (by norm_num)
theorem B2188195 : Blo 2187435 2188195 := bstep (se 1 (by rfl) ⟨1641146, by rfl⟩ : syracuseStep 2188195 = 3282293) B3282293
theorem B3115621 : Blo 2187435 3115621 := bbase (se 4 (by rfl) ⟨292089, by rfl⟩ : syracuseStep 3115621 = 584179) (by norm_num)
theorem B4154161 : Blo 2187435 4154161 := bstep (se 2 (by rfl) ⟨1557810, by rfl⟩ : syracuseStep 4154161 = 3115621) B3115621
theorem B5538881 : Blo 2187435 5538881 := bstep (se 2 (by rfl) ⟨2077080, by rfl⟩ : syracuseStep 5538881 = 4154161) B4154161
theorem B3692587 : Blo 2187435 3692587 := bstep (se 1 (by rfl) ⟨2769440, by rfl⟩ : syracuseStep 3692587 = 5538881) B5538881
theorem B4923449 : Blo 2187435 4923449 := bstep (se 2 (by rfl) ⟨1846293, by rfl⟩ : syracuseStep 4923449 = 3692587) B3692587
theorem B3282299 : Blo 2187435 3282299 := bstep (se 1 (by rfl) ⟨2461724, by rfl⟩ : syracuseStep 3282299 = 4923449) B4923449
theorem B2188199 : Blo 2187435 2188199 := bstep (se 1 (by rfl) ⟨1641149, by rfl⟩ : syracuseStep 2188199 = 3282299) B3282299
theorem B2461729 : Blo 2187435 2461729 := bbase (se 2 (by rfl) ⟨923148, by rfl⟩ : syracuseStep 2461729 = 1846297) (by norm_num)
theorem B3282305 : Blo 2187435 3282305 := bstep (se 2 (by rfl) ⟨1230864, by rfl⟩ : syracuseStep 3282305 = 2461729) B2461729
theorem B2188203 : Blo 2187435 2188203 := bstep (se 1 (by rfl) ⟨1641152, by rfl⟩ : syracuseStep 2188203 = 3282305) B3282305
theorem B5538901 : Blo 2187435 5538901 := bbase (se 8 (by rfl) ⟨32454, by rfl⟩ : syracuseStep 5538901 = 64909) (by norm_num)
theorem B7385201 : Blo 2187435 7385201 := bstep (se 2 (by rfl) ⟨2769450, by rfl⟩ : syracuseStep 7385201 = 5538901) B5538901
theorem B4923467 : Blo 2187435 4923467 := bstep (se 1 (by rfl) ⟨3692600, by rfl⟩ : syracuseStep 4923467 = 7385201) B7385201
theorem B3282311 : Blo 2187435 3282311 := bstep (se 1 (by rfl) ⟨2461733, by rfl⟩ : syracuseStep 3282311 = 4923467) B4923467
theorem B2188207 : Blo 2187435 2188207 := bstep (se 1 (by rfl) ⟨1641155, by rfl⟩ : syracuseStep 2188207 = 3282311) B3282311
theorem B3282317 : Blo 2187435 3282317 := bbase (se 3 (by rfl) ⟨615434, by rfl⟩ : syracuseStep 3282317 = 1230869) (by norm_num)
theorem B2188211 : Blo 2187435 2188211 := bstep (se 1 (by rfl) ⟨1641158, by rfl⟩ : syracuseStep 2188211 = 3282317) B3282317
theorem B4923485 : Blo 2187435 4923485 := bbase (se 3 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 4923485 = 1846307) (by norm_num)
theorem B3282323 : Blo 2187435 3282323 := bstep (se 1 (by rfl) ⟨2461742, by rfl⟩ : syracuseStep 3282323 = 4923485) B4923485
theorem B2188215 : Blo 2187435 2188215 := bstep (se 1 (by rfl) ⟨1641161, by rfl⟩ : syracuseStep 2188215 = 3282323) B3282323
theorem B3692621 : Blo 2187435 3692621 := bbase (se 3 (by rfl) ⟨692366, by rfl⟩ : syracuseStep 3692621 = 1384733) (by norm_num)
theorem B2461747 : Blo 2187435 2461747 := bstep (se 1 (by rfl) ⟨1846310, by rfl⟩ : syracuseStep 2461747 = 3692621) B3692621
theorem B3282329 : Blo 2187435 3282329 := bstep (se 2 (by rfl) ⟨1230873, by rfl⟩ : syracuseStep 3282329 = 2461747) B2461747
theorem B2188219 : Blo 2187435 2188219 := bstep (se 1 (by rfl) ⟨1641164, by rfl⟩ : syracuseStep 2188219 = 3282329) B3282329
theorem B70978517 : Blo 2187435 70978517 := bbase (se 7 (by rfl) ⟨831779, by rfl⟩ : syracuseStep 70978517 = 1663559) (by norm_num)
theorem B47319011 : Blo 2187435 47319011 := bstep (se 1 (by rfl) ⟨35489258, by rfl⟩ : syracuseStep 47319011 = 70978517) B70978517
theorem B31546007 : Blo 2187435 31546007 := bstep (se 1 (by rfl) ⟨23659505, by rfl⟩ : syracuseStep 31546007 = 47319011) B47319011
theorem B21030671 : Blo 2187435 21030671 := bstep (se 1 (by rfl) ⟨15773003, by rfl⟩ : syracuseStep 21030671 = 31546007) B31546007
theorem B14020447 : Blo 2187435 14020447 := bstep (se 1 (by rfl) ⟨10515335, by rfl⟩ : syracuseStep 14020447 = 21030671) B21030671
theorem B18693929 : Blo 2187435 18693929 := bstep (se 2 (by rfl) ⟨7010223, by rfl⟩ : syracuseStep 18693929 = 14020447) B14020447
theorem B12462619 : Blo 2187435 12462619 := bstep (se 1 (by rfl) ⟨9346964, by rfl⟩ : syracuseStep 12462619 = 18693929) B18693929
theorem B16616825 : Blo 2187435 16616825 := bstep (se 2 (by rfl) ⟨6231309, by rfl⟩ : syracuseStep 16616825 = 12462619) B12462619
theorem B11077883 : Blo 2187435 11077883 := bstep (se 1 (by rfl) ⟨8308412, by rfl⟩ : syracuseStep 11077883 = 16616825) B16616825
theorem B7385255 : Blo 2187435 7385255 := bstep (se 1 (by rfl) ⟨5538941, by rfl⟩ : syracuseStep 7385255 = 11077883) B11077883
theorem B4923503 : Blo 2187435 4923503 := bstep (se 1 (by rfl) ⟨3692627, by rfl⟩ : syracuseStep 4923503 = 7385255) B7385255
theorem B3282335 : Blo 2187435 3282335 := bstep (se 1 (by rfl) ⟨2461751, by rfl⟩ : syracuseStep 3282335 = 4923503) B4923503
theorem B2188223 : Blo 2187435 2188223 := bstep (se 1 (by rfl) ⟨1641167, by rfl⟩ : syracuseStep 2188223 = 3282335) B3282335
theorem B3282341 : Blo 2187435 3282341 := bbase (se 4 (by rfl) ⟨307719, by rfl⟩ : syracuseStep 3282341 = 615439) (by norm_num)
theorem B2188227 : Blo 2187435 2188227 := bstep (se 1 (by rfl) ⟨1641170, by rfl⟩ : syracuseStep 2188227 = 3282341) B3282341
theorem B2769481 : Blo 2187435 2769481 := bbase (se 2 (by rfl) ⟨1038555, by rfl⟩ : syracuseStep 2769481 = 2077111) (by norm_num)
theorem B3692641 : Blo 2187435 3692641 := bstep (se 2 (by rfl) ⟨1384740, by rfl⟩ : syracuseStep 3692641 = 2769481) B2769481
theorem B4923521 : Blo 2187435 4923521 := bstep (se 2 (by rfl) ⟨1846320, by rfl⟩ : syracuseStep 4923521 = 3692641) B3692641
theorem B3282347 : Blo 2187435 3282347 := bstep (se 1 (by rfl) ⟨2461760, by rfl⟩ : syracuseStep 3282347 = 4923521) B4923521
theorem B2188231 : Blo 2187435 2188231 := bstep (se 1 (by rfl) ⟨1641173, by rfl⟩ : syracuseStep 2188231 = 3282347) B3282347
theorem B2461765 : Blo 2187435 2461765 := bbase (se 4 (by rfl) ⟨230790, by rfl⟩ : syracuseStep 2461765 = 461581) (by norm_num)
theorem B3282353 : Blo 2187435 3282353 := bstep (se 2 (by rfl) ⟨1230882, by rfl⟩ : syracuseStep 3282353 = 2461765) B2461765
theorem B2188235 : Blo 2187435 2188235 := bstep (se 1 (by rfl) ⟨1641176, by rfl⟩ : syracuseStep 2188235 = 3282353) B3282353
theorem B4154237 : Blo 2187435 4154237 := bbase (se 3 (by rfl) ⟨778919, by rfl⟩ : syracuseStep 4154237 = 1557839) (by norm_num)
theorem B2769491 : Blo 2187435 2769491 := bstep (se 1 (by rfl) ⟨2077118, by rfl⟩ : syracuseStep 2769491 = 4154237) B4154237
theorem B7385309 : Blo 2187435 7385309 := bstep (se 3 (by rfl) ⟨1384745, by rfl⟩ : syracuseStep 7385309 = 2769491) B2769491
theorem B4923539 : Blo 2187435 4923539 := bstep (se 1 (by rfl) ⟨3692654, by rfl⟩ : syracuseStep 4923539 = 7385309) B7385309
theorem B3282359 : Blo 2187435 3282359 := bstep (se 1 (by rfl) ⟨2461769, by rfl⟩ : syracuseStep 3282359 = 4923539) B4923539
theorem B2188239 : Blo 2187435 2188239 := bstep (se 1 (by rfl) ⟨1641179, by rfl⟩ : syracuseStep 2188239 = 3282359) B3282359
theorem B3282365 : Blo 2187435 3282365 := bbase (se 3 (by rfl) ⟨615443, by rfl⟩ : syracuseStep 3282365 = 1230887) (by norm_num)
theorem B2188243 : Blo 2187435 2188243 := bstep (se 1 (by rfl) ⟨1641182, by rfl⟩ : syracuseStep 2188243 = 3282365) B3282365
theorem B4923557 : Blo 2187435 4923557 := bbase (se 4 (by rfl) ⟨461583, by rfl⟩ : syracuseStep 4923557 = 923167) (by norm_num)
theorem B3282371 : Blo 2187435 3282371 := bstep (se 1 (by rfl) ⟨2461778, by rfl⟩ : syracuseStep 3282371 = 4923557) B4923557
theorem B2188247 : Blo 2187435 2188247 := bstep (se 1 (by rfl) ⟨1641185, by rfl⟩ : syracuseStep 2188247 = 3282371) B3282371
theorem B5539013 : Blo 2187435 5539013 := bbase (se 4 (by rfl) ⟨519282, by rfl⟩ : syracuseStep 5539013 = 1038565) (by norm_num)
theorem B3692675 : Blo 2187435 3692675 := bstep (se 1 (by rfl) ⟨2769506, by rfl⟩ : syracuseStep 3692675 = 5539013) B5539013
theorem B2461783 : Blo 2187435 2461783 := bstep (se 1 (by rfl) ⟨1846337, by rfl⟩ : syracuseStep 2461783 = 3692675) B3692675
theorem B3282377 : Blo 2187435 3282377 := bstep (se 2 (by rfl) ⟨1230891, by rfl⟩ : syracuseStep 3282377 = 2461783) B2461783
theorem B2188251 : Blo 2187435 2188251 := bstep (se 1 (by rfl) ⟨1641188, by rfl⟩ : syracuseStep 2188251 = 3282377) B3282377
theorem B15773237 : Blo 2187435 15773237 := bbase (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) (by norm_num)
theorem B10515491 : Blo 2187435 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B7010327 : Blo 2187435 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B4673551 : Blo 2187435 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B6231401 : Blo 2187435 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B4154267 : Blo 2187435 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B11078045 : Blo 2187435 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B7385363 : Blo 2187435 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B4923575 : Blo 2187435 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B3282383 : Blo 2187435 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B2188255 : Blo 2187435 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B3282389 : Blo 2187435 3282389 := bbase (se 7 (by rfl) ⟨38465, by rfl⟩ : syracuseStep 3282389 = 76931) (by norm_num)
theorem B2188259 : Blo 2187435 2188259 := bstep (se 1 (by rfl) ⟨1641194, by rfl⟩ : syracuseStep 2188259 = 3282389) B3282389
theorem B8308565 : Blo 2187435 8308565 := bbase (se 9 (by rfl) ⟨24341, by rfl⟩ : syracuseStep 8308565 = 48683) (by norm_num)
theorem B5539043 : Blo 2187435 5539043 := bstep (se 1 (by rfl) ⟨4154282, by rfl⟩ : syracuseStep 5539043 = 8308565) B8308565
theorem B3692695 : Blo 2187435 3692695 := bstep (se 1 (by rfl) ⟨2769521, by rfl⟩ : syracuseStep 3692695 = 5539043) B5539043
theorem B4923593 : Blo 2187435 4923593 := bstep (se 2 (by rfl) ⟨1846347, by rfl⟩ : syracuseStep 4923593 = 3692695) B3692695
theorem B3282395 : Blo 2187435 3282395 := bstep (se 1 (by rfl) ⟨2461796, by rfl⟩ : syracuseStep 3282395 = 4923593) B4923593
theorem B2188263 : Blo 2187435 2188263 := bstep (se 1 (by rfl) ⟨1641197, by rfl⟩ : syracuseStep 2188263 = 3282395) B3282395
theorem B2461801 : Blo 2187435 2461801 := bbase (se 2 (by rfl) ⟨923175, by rfl⟩ : syracuseStep 2461801 = 1846351) (by norm_num)
theorem B3282401 : Blo 2187435 3282401 := bstep (se 2 (by rfl) ⟨1230900, by rfl⟩ : syracuseStep 3282401 = 2461801) B2461801
theorem B2188267 : Blo 2187435 2188267 := bstep (se 1 (by rfl) ⟨1641200, by rfl⟩ : syracuseStep 2188267 = 3282401) B3282401
theorem B3505189 : Blo 2187435 3505189 := bbase (se 4 (by rfl) ⟨328611, by rfl⟩ : syracuseStep 3505189 = 657223) (by norm_num)
theorem B4673585 : Blo 2187435 4673585 := bstep (se 2 (by rfl) ⟨1752594, by rfl⟩ : syracuseStep 4673585 = 3505189) B3505189
theorem B12462893 : Blo 2187435 12462893 := bstep (se 3 (by rfl) ⟨2336792, by rfl⟩ : syracuseStep 12462893 = 4673585) B4673585
theorem B8308595 : Blo 2187435 8308595 := bstep (se 1 (by rfl) ⟨6231446, by rfl⟩ : syracuseStep 8308595 = 12462893) B12462893
theorem B5539063 : Blo 2187435 5539063 := bstep (se 1 (by rfl) ⟨4154297, by rfl⟩ : syracuseStep 5539063 = 8308595) B8308595
theorem B7385417 : Blo 2187435 7385417 := bstep (se 2 (by rfl) ⟨2769531, by rfl⟩ : syracuseStep 7385417 = 5539063) B5539063
theorem B4923611 : Blo 2187435 4923611 := bstep (se 1 (by rfl) ⟨3692708, by rfl⟩ : syracuseStep 4923611 = 7385417) B7385417
theorem B3282407 : Blo 2187435 3282407 := bstep (se 1 (by rfl) ⟨2461805, by rfl⟩ : syracuseStep 3282407 = 4923611) B4923611
theorem B2188271 : Blo 2187435 2188271 := bstep (se 1 (by rfl) ⟨1641203, by rfl⟩ : syracuseStep 2188271 = 3282407) B3282407
theorem B3282413 : Blo 2187435 3282413 := bbase (se 3 (by rfl) ⟨615452, by rfl⟩ : syracuseStep 3282413 = 1230905) (by norm_num)
theorem B2188275 : Blo 2187435 2188275 := bstep (se 1 (by rfl) ⟨1641206, by rfl⟩ : syracuseStep 2188275 = 3282413) B3282413
theorem B4923629 : Blo 2187435 4923629 := bbase (se 3 (by rfl) ⟨923180, by rfl⟩ : syracuseStep 4923629 = 1846361) (by norm_num)
theorem B3282419 : Blo 2187435 3282419 := bstep (se 1 (by rfl) ⟨2461814, by rfl⟩ : syracuseStep 3282419 = 4923629) B4923629
theorem B2188279 : Blo 2187435 2188279 := bstep (se 1 (by rfl) ⟨1641209, by rfl⟩ : syracuseStep 2188279 = 3282419) B3282419
theorem B3115741 : Blo 2187435 3115741 := bbase (se 3 (by rfl) ⟨584201, by rfl⟩ : syracuseStep 3115741 = 1168403) (by norm_num)
theorem B4154321 : Blo 2187435 4154321 := bstep (se 2 (by rfl) ⟨1557870, by rfl⟩ : syracuseStep 4154321 = 3115741) B3115741
theorem B2769547 : Blo 2187435 2769547 := bstep (se 1 (by rfl) ⟨2077160, by rfl⟩ : syracuseStep 2769547 = 4154321) B4154321
theorem B3692729 : Blo 2187435 3692729 := bstep (se 2 (by rfl) ⟨1384773, by rfl⟩ : syracuseStep 3692729 = 2769547) B2769547
theorem B2461819 : Blo 2187435 2461819 := bstep (se 1 (by rfl) ⟨1846364, by rfl⟩ : syracuseStep 2461819 = 3692729) B3692729
theorem B3282425 : Blo 2187435 3282425 := bstep (se 2 (by rfl) ⟨1230909, by rfl⟩ : syracuseStep 3282425 = 2461819) B2461819
theorem B2188283 : Blo 2187435 2188283 := bstep (se 1 (by rfl) ⟨1641212, by rfl⟩ : syracuseStep 2188283 = 3282425) B3282425
theorem B84125141 : Blo 2187435 84125141 := bbase (se 7 (by rfl) ⟨985841, by rfl⟩ : syracuseStep 84125141 = 1971683) (by norm_num)
theorem B56083427 : Blo 2187435 56083427 := bstep (se 1 (by rfl) ⟨42062570, by rfl⟩ : syracuseStep 56083427 = 84125141) B84125141
theorem B37388951 : Blo 2187435 37388951 := bstep (se 1 (by rfl) ⟨28041713, by rfl⟩ : syracuseStep 37388951 = 56083427) B56083427
theorem B24925967 : Blo 2187435 24925967 := bstep (se 1 (by rfl) ⟨18694475, by rfl⟩ : syracuseStep 24925967 = 37388951) B37388951
theorem B16617311 : Blo 2187435 16617311 := bstep (se 1 (by rfl) ⟨12462983, by rfl⟩ : syracuseStep 16617311 = 24925967) B24925967
theorem B11078207 : Blo 2187435 11078207 := bstep (se 1 (by rfl) ⟨8308655, by rfl⟩ : syracuseStep 11078207 = 16617311) B16617311
theorem B7385471 : Blo 2187435 7385471 := bstep (se 1 (by rfl) ⟨5539103, by rfl⟩ : syracuseStep 7385471 = 11078207) B11078207
theorem B4923647 : Blo 2187435 4923647 := bstep (se 1 (by rfl) ⟨3692735, by rfl⟩ : syracuseStep 4923647 = 7385471) B7385471
theorem B3282431 : Blo 2187435 3282431 := bstep (se 1 (by rfl) ⟨2461823, by rfl⟩ : syracuseStep 3282431 = 4923647) B4923647
theorem B2188287 : Blo 2187435 2188287 := bstep (se 1 (by rfl) ⟨1641215, by rfl⟩ : syracuseStep 2188287 = 3282431) B3282431
theorem B3282437 : Blo 2187435 3282437 := bbase (se 4 (by rfl) ⟨307728, by rfl⟩ : syracuseStep 3282437 = 615457) (by norm_num)
theorem B2188291 : Blo 2187435 2188291 := bstep (se 1 (by rfl) ⟨1641218, by rfl⟩ : syracuseStep 2188291 = 3282437) B3282437
theorem B3692749 : Blo 2187435 3692749 := bbase (se 3 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 3692749 = 1384781) (by norm_num)
theorem B4923665 : Blo 2187435 4923665 := bstep (se 2 (by rfl) ⟨1846374, by rfl⟩ : syracuseStep 4923665 = 3692749) B3692749
theorem B3282443 : Blo 2187435 3282443 := bstep (se 1 (by rfl) ⟨2461832, by rfl⟩ : syracuseStep 3282443 = 4923665) B4923665
theorem B2188295 : Blo 2187435 2188295 := bstep (se 1 (by rfl) ⟨1641221, by rfl⟩ : syracuseStep 2188295 = 3282443) B3282443
theorem B2461837 : Blo 2187435 2461837 := bbase (se 3 (by rfl) ⟨461594, by rfl⟩ : syracuseStep 2461837 = 923189) (by norm_num)
theorem B3282449 : Blo 2187435 3282449 := bstep (se 2 (by rfl) ⟨1230918, by rfl⟩ : syracuseStep 3282449 = 2461837) B2461837
theorem B2188299 : Blo 2187435 2188299 := bstep (se 1 (by rfl) ⟨1641224, by rfl⟩ : syracuseStep 2188299 = 3282449) B3282449
theorem B7385525 : Blo 2187435 7385525 := bbase (se 5 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 7385525 = 692393) (by norm_num)
theorem B4923683 : Blo 2187435 4923683 := bstep (se 1 (by rfl) ⟨3692762, by rfl⟩ : syracuseStep 4923683 = 7385525) B7385525
theorem B3282455 : Blo 2187435 3282455 := bstep (se 1 (by rfl) ⟨2461841, by rfl⟩ : syracuseStep 3282455 = 4923683) B4923683
theorem B2188303 : Blo 2187435 2188303 := bstep (se 1 (by rfl) ⟨1641227, by rfl⟩ : syracuseStep 2188303 = 3282455) B3282455
theorem B3282461 : Blo 2187435 3282461 := bbase (se 3 (by rfl) ⟨615461, by rfl⟩ : syracuseStep 3282461 = 1230923) (by norm_num)
theorem B2188307 : Blo 2187435 2188307 := bstep (se 1 (by rfl) ⟨1641230, by rfl⟩ : syracuseStep 2188307 = 3282461) B3282461
theorem B4923701 : Blo 2187435 4923701 := bbase (se 5 (by rfl) ⟨230798, by rfl⟩ : syracuseStep 4923701 = 461597) (by norm_num)
theorem B3282467 : Blo 2187435 3282467 := bstep (se 1 (by rfl) ⟨2461850, by rfl⟩ : syracuseStep 3282467 = 4923701) B4923701
theorem B2188311 : Blo 2187435 2188311 := bstep (se 1 (by rfl) ⟨1641233, by rfl⟩ : syracuseStep 2188311 = 3282467) B3282467
theorem B6654517 : Blo 2187435 6654517 := bbase (se 5 (by rfl) ⟨311930, by rfl⟩ : syracuseStep 6654517 = 623861) (by norm_num)
theorem B35490757 : Blo 2187435 35490757 := bstep (se 4 (by rfl) ⟨3327258, by rfl⟩ : syracuseStep 35490757 = 6654517) B6654517
theorem B47321009 : Blo 2187435 47321009 := bstep (se 2 (by rfl) ⟨17745378, by rfl⟩ : syracuseStep 47321009 = 35490757) B35490757
theorem B31547339 : Blo 2187435 31547339 := bstep (se 1 (by rfl) ⟨23660504, by rfl⟩ : syracuseStep 31547339 = 47321009) B47321009
theorem B21031559 : Blo 2187435 21031559 := bstep (se 1 (by rfl) ⟨15773669, by rfl⟩ : syracuseStep 21031559 = 31547339) B31547339
theorem B14021039 : Blo 2187435 14021039 := bstep (se 1 (by rfl) ⟨10515779, by rfl⟩ : syracuseStep 14021039 = 21031559) B21031559
theorem B9347359 : Blo 2187435 9347359 := bstep (se 1 (by rfl) ⟨7010519, by rfl⟩ : syracuseStep 9347359 = 14021039) B14021039
theorem B12463145 : Blo 2187435 12463145 := bstep (se 2 (by rfl) ⟨4673679, by rfl⟩ : syracuseStep 12463145 = 9347359) B9347359
theorem B8308763 : Blo 2187435 8308763 := bstep (se 1 (by rfl) ⟨6231572, by rfl⟩ : syracuseStep 8308763 = 12463145) B12463145
theorem B5539175 : Blo 2187435 5539175 := bstep (se 1 (by rfl) ⟨4154381, by rfl⟩ : syracuseStep 5539175 = 8308763) B8308763
theorem B3692783 : Blo 2187435 3692783 := bstep (se 1 (by rfl) ⟨2769587, by rfl⟩ : syracuseStep 3692783 = 5539175) B5539175
theorem B2461855 : Blo 2187435 2461855 := bstep (se 1 (by rfl) ⟨1846391, by rfl⟩ : syracuseStep 2461855 = 3692783) B3692783
theorem B3282473 : Blo 2187435 3282473 := bstep (se 2 (by rfl) ⟨1230927, by rfl⟩ : syracuseStep 3282473 = 2461855) B2461855
theorem B2188315 : Blo 2187435 2188315 := bstep (se 1 (by rfl) ⟨1641236, by rfl⟩ : syracuseStep 2188315 = 3282473) B3282473
theorem B5691365 : Blo 2187435 5691365 := bbase (se 4 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 5691365 = 1067131) (by norm_num)
theorem B3794243 : Blo 2187435 3794243 := bstep (se 1 (by rfl) ⟨2845682, by rfl⟩ : syracuseStep 3794243 = 5691365) B5691365
theorem B10117981 : Blo 2187435 10117981 := bstep (se 3 (by rfl) ⟨1897121, by rfl⟩ : syracuseStep 10117981 = 3794243) B3794243
theorem B13490641 : Blo 2187435 13490641 := bstep (se 2 (by rfl) ⟨5058990, by rfl⟩ : syracuseStep 13490641 = 10117981) B10117981
theorem B17987521 : Blo 2187435 17987521 := bstep (se 2 (by rfl) ⟨6745320, by rfl⟩ : syracuseStep 17987521 = 13490641) B13490641
theorem B23983361 : Blo 2187435 23983361 := bstep (se 2 (by rfl) ⟨8993760, by rfl⟩ : syracuseStep 23983361 = 17987521) B17987521
theorem B15988907 : Blo 2187435 15988907 := bstep (se 1 (by rfl) ⟨11991680, by rfl⟩ : syracuseStep 15988907 = 23983361) B23983361
theorem B10659271 : Blo 2187435 10659271 := bstep (se 1 (by rfl) ⟨7994453, by rfl⟩ : syracuseStep 10659271 = 15988907) B15988907
theorem B14212361 : Blo 2187435 14212361 := bstep (se 2 (by rfl) ⟨5329635, by rfl⟩ : syracuseStep 14212361 = 10659271) B10659271
theorem B9474907 : Blo 2187435 9474907 := bstep (se 1 (by rfl) ⟨7106180, by rfl⟩ : syracuseStep 9474907 = 14212361) B14212361
theorem B12633209 : Blo 2187435 12633209 := bstep (se 2 (by rfl) ⟨4737453, by rfl⟩ : syracuseStep 12633209 = 9474907) B9474907
theorem B8422139 : Blo 2187435 8422139 := bstep (se 1 (by rfl) ⟨6316604, by rfl⟩ : syracuseStep 8422139 = 12633209) B12633209
theorem B5614759 : Blo 2187435 5614759 := bstep (se 1 (by rfl) ⟨4211069, by rfl⟩ : syracuseStep 5614759 = 8422139) B8422139
theorem B7486345 : Blo 2187435 7486345 := bstep (se 2 (by rfl) ⟨2807379, by rfl⟩ : syracuseStep 7486345 = 5614759) B5614759
theorem B9981793 : Blo 2187435 9981793 := bstep (se 2 (by rfl) ⟨3743172, by rfl⟩ : syracuseStep 9981793 = 7486345) B7486345
theorem B13309057 : Blo 2187435 13309057 := bstep (se 2 (by rfl) ⟨4990896, by rfl⟩ : syracuseStep 13309057 = 9981793) B9981793
theorem B17745409 : Blo 2187435 17745409 := bstep (se 2 (by rfl) ⟨6654528, by rfl⟩ : syracuseStep 17745409 = 13309057) B13309057
theorem B23660545 : Blo 2187435 23660545 := bstep (se 2 (by rfl) ⟨8872704, by rfl⟩ : syracuseStep 23660545 = 17745409) B17745409
theorem B31547393 : Blo 2187435 31547393 := bstep (se 2 (by rfl) ⟨11830272, by rfl⟩ : syracuseStep 31547393 = 23660545) B23660545
theorem B21031595 : Blo 2187435 21031595 := bstep (se 1 (by rfl) ⟨15773696, by rfl⟩ : syracuseStep 21031595 = 31547393) B31547393
theorem B14021063 : Blo 2187435 14021063 := bstep (se 1 (by rfl) ⟨10515797, by rfl⟩ : syracuseStep 14021063 = 21031595) B21031595
theorem B9347375 : Blo 2187435 9347375 := bstep (se 1 (by rfl) ⟨7010531, by rfl⟩ : syracuseStep 9347375 = 14021063) B14021063
theorem B6231583 : Blo 2187435 6231583 := bstep (se 1 (by rfl) ⟨4673687, by rfl⟩ : syracuseStep 6231583 = 9347375) B9347375
theorem B8308777 : Blo 2187435 8308777 := bstep (se 2 (by rfl) ⟨3115791, by rfl⟩ : syracuseStep 8308777 = 6231583) B6231583
theorem B11078369 : Blo 2187435 11078369 := bstep (se 2 (by rfl) ⟨4154388, by rfl⟩ : syracuseStep 11078369 = 8308777) B8308777
theorem B7385579 : Blo 2187435 7385579 := bstep (se 1 (by rfl) ⟨5539184, by rfl⟩ : syracuseStep 7385579 = 11078369) B11078369
theorem B4923719 : Blo 2187435 4923719 := bstep (se 1 (by rfl) ⟨3692789, by rfl⟩ : syracuseStep 4923719 = 7385579) B7385579
theorem B3282479 : Blo 2187435 3282479 := bstep (se 1 (by rfl) ⟨2461859, by rfl⟩ : syracuseStep 3282479 = 4923719) B4923719
theorem B2188319 : Blo 2187435 2188319 := bstep (se 1 (by rfl) ⟨1641239, by rfl⟩ : syracuseStep 2188319 = 3282479) B3282479
theorem B3282485 : Blo 2187435 3282485 := bbase (se 5 (by rfl) ⟨153866, by rfl⟩ : syracuseStep 3282485 = 307733) (by norm_num)
theorem B2188323 : Blo 2187435 2188323 := bstep (se 1 (by rfl) ⟨1641242, by rfl⟩ : syracuseStep 2188323 = 3282485) B3282485
theorem B5539205 : Blo 2187435 5539205 := bbase (se 4 (by rfl) ⟨519300, by rfl⟩ : syracuseStep 5539205 = 1038601) (by norm_num)
theorem B3692803 : Blo 2187435 3692803 := bstep (se 1 (by rfl) ⟨2769602, by rfl⟩ : syracuseStep 3692803 = 5539205) B5539205
theorem B4923737 : Blo 2187435 4923737 := bstep (se 2 (by rfl) ⟨1846401, by rfl⟩ : syracuseStep 4923737 = 3692803) B3692803
theorem B3282491 : Blo 2187435 3282491 := bstep (se 1 (by rfl) ⟨2461868, by rfl⟩ : syracuseStep 3282491 = 4923737) B4923737
theorem B2188327 : Blo 2187435 2188327 := bstep (se 1 (by rfl) ⟨1641245, by rfl⟩ : syracuseStep 2188327 = 3282491) B3282491
theorem B2461873 : Blo 2187435 2461873 := bbase (se 2 (by rfl) ⟨923202, by rfl⟩ : syracuseStep 2461873 = 1846405) (by norm_num)
theorem B3282497 : Blo 2187435 3282497 := bstep (se 2 (by rfl) ⟨1230936, by rfl⟩ : syracuseStep 3282497 = 2461873) B2461873
theorem B2188331 : Blo 2187435 2188331 := bstep (se 1 (by rfl) ⟨1641248, by rfl⟩ : syracuseStep 2188331 = 3282497) B3282497
theorem B2336861 : Blo 2187435 2336861 := bbase (se 3 (by rfl) ⟨438161, by rfl⟩ : syracuseStep 2336861 = 876323) (by norm_num)
theorem B6231629 : Blo 2187435 6231629 := bstep (se 3 (by rfl) ⟨1168430, by rfl⟩ : syracuseStep 6231629 = 2336861) B2336861
theorem B4154419 : Blo 2187435 4154419 := bstep (se 1 (by rfl) ⟨3115814, by rfl⟩ : syracuseStep 4154419 = 6231629) B6231629
theorem B5539225 : Blo 2187435 5539225 := bstep (se 2 (by rfl) ⟨2077209, by rfl⟩ : syracuseStep 5539225 = 4154419) B4154419
theorem B7385633 : Blo 2187435 7385633 := bstep (se 2 (by rfl) ⟨2769612, by rfl⟩ : syracuseStep 7385633 = 5539225) B5539225
theorem B4923755 : Blo 2187435 4923755 := bstep (se 1 (by rfl) ⟨3692816, by rfl⟩ : syracuseStep 4923755 = 7385633) B7385633
theorem B3282503 : Blo 2187435 3282503 := bstep (se 1 (by rfl) ⟨2461877, by rfl⟩ : syracuseStep 3282503 = 4923755) B4923755
theorem B2188335 : Blo 2187435 2188335 := bstep (se 1 (by rfl) ⟨1641251, by rfl⟩ : syracuseStep 2188335 = 3282503) B3282503
theorem B3282509 : Blo 2187435 3282509 := bbase (se 3 (by rfl) ⟨615470, by rfl⟩ : syracuseStep 3282509 = 1230941) (by norm_num)
theorem B2188339 : Blo 2187435 2188339 := bstep (se 1 (by rfl) ⟨1641254, by rfl⟩ : syracuseStep 2188339 = 3282509) B3282509
theorem B4923773 : Blo 2187435 4923773 := bbase (se 3 (by rfl) ⟨923207, by rfl⟩ : syracuseStep 4923773 = 1846415) (by norm_num)
theorem B3282515 : Blo 2187435 3282515 := bstep (se 1 (by rfl) ⟨2461886, by rfl⟩ : syracuseStep 3282515 = 4923773) B4923773
theorem B2188343 : Blo 2187435 2188343 := bstep (se 1 (by rfl) ⟨1641257, by rfl⟩ : syracuseStep 2188343 = 3282515) B3282515
theorem B3692837 : Blo 2187435 3692837 := bbase (se 4 (by rfl) ⟨346203, by rfl⟩ : syracuseStep 3692837 = 692407) (by norm_num)
theorem B2461891 : Blo 2187435 2461891 := bstep (se 1 (by rfl) ⟨1846418, by rfl⟩ : syracuseStep 2461891 = 3692837) B3692837
theorem B3282521 : Blo 2187435 3282521 := bstep (se 2 (by rfl) ⟨1230945, by rfl⟩ : syracuseStep 3282521 = 2461891) B2461891
theorem B2188347 : Blo 2187435 2188347 := bstep (se 1 (by rfl) ⟨1641260, by rfl⟩ : syracuseStep 2188347 = 3282521) B3282521
theorem B3115837 : Blo 2187435 3115837 := bbase (se 3 (by rfl) ⟨584219, by rfl⟩ : syracuseStep 3115837 = 1168439) (by norm_num)
theorem B16617797 : Blo 2187435 16617797 := bstep (se 4 (by rfl) ⟨1557918, by rfl⟩ : syracuseStep 16617797 = 3115837) B3115837
theorem B11078531 : Blo 2187435 11078531 := bstep (se 1 (by rfl) ⟨8308898, by rfl⟩ : syracuseStep 11078531 = 16617797) B16617797
theorem B7385687 : Blo 2187435 7385687 := bstep (se 1 (by rfl) ⟨5539265, by rfl⟩ : syracuseStep 7385687 = 11078531) B11078531
theorem B4923791 : Blo 2187435 4923791 := bstep (se 1 (by rfl) ⟨3692843, by rfl⟩ : syracuseStep 4923791 = 7385687) B7385687
theorem B3282527 : Blo 2187435 3282527 := bstep (se 1 (by rfl) ⟨2461895, by rfl⟩ : syracuseStep 3282527 = 4923791) B4923791
theorem B2188351 : Blo 2187435 2188351 := bstep (se 1 (by rfl) ⟨1641263, by rfl⟩ : syracuseStep 2188351 = 3282527) B3282527
theorem B3282533 : Blo 2187435 3282533 := bbase (se 4 (by rfl) ⟨307737, by rfl⟩ : syracuseStep 3282533 = 615475) (by norm_num)
theorem B2188355 : Blo 2187435 2188355 := bstep (se 1 (by rfl) ⟨1641266, by rfl⟩ : syracuseStep 2188355 = 3282533) B3282533
theorem B5257997 : Blo 2187435 5257997 := bbase (se 3 (by rfl) ⟨985874, by rfl⟩ : syracuseStep 5257997 = 1971749) (by norm_num)
theorem B3505331 : Blo 2187435 3505331 := bstep (se 1 (by rfl) ⟨2628998, by rfl⟩ : syracuseStep 3505331 = 5257997) B5257997
theorem B2336887 : Blo 2187435 2336887 := bstep (se 1 (by rfl) ⟨1752665, by rfl⟩ : syracuseStep 2336887 = 3505331) B3505331
theorem B3115849 : Blo 2187435 3115849 := bstep (se 2 (by rfl) ⟨1168443, by rfl⟩ : syracuseStep 3115849 = 2336887) B2336887
theorem B4154465 : Blo 2187435 4154465 := bstep (se 2 (by rfl) ⟨1557924, by rfl⟩ : syracuseStep 4154465 = 3115849) B3115849
theorem B2769643 : Blo 2187435 2769643 := bstep (se 1 (by rfl) ⟨2077232, by rfl⟩ : syracuseStep 2769643 = 4154465) B4154465
theorem B3692857 : Blo 2187435 3692857 := bstep (se 2 (by rfl) ⟨1384821, by rfl⟩ : syracuseStep 3692857 = 2769643) B2769643
theorem B4923809 : Blo 2187435 4923809 := bstep (se 2 (by rfl) ⟨1846428, by rfl⟩ : syracuseStep 4923809 = 3692857) B3692857
theorem B3282539 : Blo 2187435 3282539 := bstep (se 1 (by rfl) ⟨2461904, by rfl⟩ : syracuseStep 3282539 = 4923809) B4923809
theorem B2188359 : Blo 2187435 2188359 := bstep (se 1 (by rfl) ⟨1641269, by rfl⟩ : syracuseStep 2188359 = 3282539) B3282539
theorem B2461909 : Blo 2187435 2461909 := bbase (se 7 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 2461909 = 57701) (by norm_num)
theorem B3282545 : Blo 2187435 3282545 := bstep (se 2 (by rfl) ⟨1230954, by rfl⟩ : syracuseStep 3282545 = 2461909) B2461909
theorem B2188363 : Blo 2187435 2188363 := bstep (se 1 (by rfl) ⟨1641272, by rfl⟩ : syracuseStep 2188363 = 3282545) B3282545
theorem B2769653 : Blo 2187435 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B7385741 : Blo 2187435 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B4923827 : Blo 2187435 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B3282551 : Blo 2187435 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B2188367 : Blo 2187435 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B3282557 : Blo 2187435 3282557 := bbase (se 3 (by rfl) ⟨615479, by rfl⟩ : syracuseStep 3282557 = 1230959) (by norm_num)
theorem B2188371 : Blo 2187435 2188371 := bstep (se 1 (by rfl) ⟨1641278, by rfl⟩ : syracuseStep 2188371 = 3282557) B3282557
theorem B4923845 : Blo 2187435 4923845 := bbase (se 4 (by rfl) ⟨461610, by rfl⟩ : syracuseStep 4923845 = 923221) (by norm_num)
theorem B3282563 : Blo 2187435 3282563 := bstep (se 1 (by rfl) ⟨2461922, by rfl⟩ : syracuseStep 3282563 = 4923845) B4923845
theorem B2188375 : Blo 2187435 2188375 := bstep (se 1 (by rfl) ⟨1641281, by rfl⟩ : syracuseStep 2188375 = 3282563) B3282563
theorem B7010725 : Blo 2187435 7010725 := bbase (se 4 (by rfl) ⟨657255, by rfl⟩ : syracuseStep 7010725 = 1314511) (by norm_num)
theorem B9347633 : Blo 2187435 9347633 := bstep (se 2 (by rfl) ⟨3505362, by rfl⟩ : syracuseStep 9347633 = 7010725) B7010725
theorem B6231755 : Blo 2187435 6231755 := bstep (se 1 (by rfl) ⟨4673816, by rfl⟩ : syracuseStep 6231755 = 9347633) B9347633
theorem B4154503 : Blo 2187435 4154503 := bstep (se 1 (by rfl) ⟨3115877, by rfl⟩ : syracuseStep 4154503 = 6231755) B6231755
theorem B5539337 : Blo 2187435 5539337 := bstep (se 2 (by rfl) ⟨2077251, by rfl⟩ : syracuseStep 5539337 = 4154503) B4154503
theorem B3692891 : Blo 2187435 3692891 := bstep (se 1 (by rfl) ⟨2769668, by rfl⟩ : syracuseStep 3692891 = 5539337) B5539337
theorem B2461927 : Blo 2187435 2461927 := bstep (se 1 (by rfl) ⟨1846445, by rfl⟩ : syracuseStep 2461927 = 3692891) B3692891
theorem B3282569 : Blo 2187435 3282569 := bstep (se 2 (by rfl) ⟨1230963, by rfl⟩ : syracuseStep 3282569 = 2461927) B2461927
theorem B2188379 : Blo 2187435 2188379 := bstep (se 1 (by rfl) ⟨1641284, by rfl⟩ : syracuseStep 2188379 = 3282569) B3282569
theorem B11078693 : Blo 2187435 11078693 := bbase (se 4 (by rfl) ⟨1038627, by rfl⟩ : syracuseStep 11078693 = 2077255) (by norm_num)
theorem B7385795 : Blo 2187435 7385795 := bstep (se 1 (by rfl) ⟨5539346, by rfl⟩ : syracuseStep 7385795 = 11078693) B11078693
theorem B4923863 : Blo 2187435 4923863 := bstep (se 1 (by rfl) ⟨3692897, by rfl⟩ : syracuseStep 4923863 = 7385795) B7385795
theorem B3282575 : Blo 2187435 3282575 := bstep (se 1 (by rfl) ⟨2461931, by rfl⟩ : syracuseStep 3282575 = 4923863) B4923863
theorem B2188383 : Blo 2187435 2188383 := bstep (se 1 (by rfl) ⟨1641287, by rfl⟩ : syracuseStep 2188383 = 3282575) B3282575
theorem B3282581 : Blo 2187435 3282581 := bbase (se 6 (by rfl) ⟨76935, by rfl⟩ : syracuseStep 3282581 = 153871) (by norm_num)
theorem B2188387 : Blo 2187435 2188387 := bstep (se 1 (by rfl) ⟨1641290, by rfl⟩ : syracuseStep 2188387 = 3282581) B3282581
theorem B14021525 : Blo 2187435 14021525 := bbase (se 6 (by rfl) ⟨328629, by rfl⟩ : syracuseStep 14021525 = 657259) (by norm_num)
theorem B9347683 : Blo 2187435 9347683 := bstep (se 1 (by rfl) ⟨7010762, by rfl⟩ : syracuseStep 9347683 = 14021525) B14021525
theorem B12463577 : Blo 2187435 12463577 := bstep (se 2 (by rfl) ⟨4673841, by rfl⟩ : syracuseStep 12463577 = 9347683) B9347683
theorem B8309051 : Blo 2187435 8309051 := bstep (se 1 (by rfl) ⟨6231788, by rfl⟩ : syracuseStep 8309051 = 12463577) B12463577
theorem B5539367 : Blo 2187435 5539367 := bstep (se 1 (by rfl) ⟨4154525, by rfl⟩ : syracuseStep 5539367 = 8309051) B8309051
theorem B3692911 : Blo 2187435 3692911 := bstep (se 1 (by rfl) ⟨2769683, by rfl⟩ : syracuseStep 3692911 = 5539367) B5539367
theorem B4923881 : Blo 2187435 4923881 := bstep (se 2 (by rfl) ⟨1846455, by rfl⟩ : syracuseStep 4923881 = 3692911) B3692911
theorem B3282587 : Blo 2187435 3282587 := bstep (se 1 (by rfl) ⟨2461940, by rfl⟩ : syracuseStep 3282587 = 4923881) B4923881
theorem B2188391 : Blo 2187435 2188391 := bstep (se 1 (by rfl) ⟨1641293, by rfl⟩ : syracuseStep 2188391 = 3282587) B3282587
theorem B2461945 : Blo 2187435 2461945 := bbase (se 2 (by rfl) ⟨923229, by rfl⟩ : syracuseStep 2461945 = 1846459) (by norm_num)
theorem B3282593 : Blo 2187435 3282593 := bstep (se 2 (by rfl) ⟨1230972, by rfl⟩ : syracuseStep 3282593 = 2461945) B2461945
theorem B2188395 : Blo 2187435 2188395 := bstep (se 1 (by rfl) ⟨1641296, by rfl⟩ : syracuseStep 2188395 = 3282593) B3282593
theorem B9347717 : Blo 2187435 9347717 := bbase (se 4 (by rfl) ⟨876348, by rfl⟩ : syracuseStep 9347717 = 1752697) (by norm_num)
theorem B6231811 : Blo 2187435 6231811 := bstep (se 1 (by rfl) ⟨4673858, by rfl⟩ : syracuseStep 6231811 = 9347717) B9347717
theorem B8309081 : Blo 2187435 8309081 := bstep (se 2 (by rfl) ⟨3115905, by rfl⟩ : syracuseStep 8309081 = 6231811) B6231811
theorem B5539387 : Blo 2187435 5539387 := bstep (se 1 (by rfl) ⟨4154540, by rfl⟩ : syracuseStep 5539387 = 8309081) B8309081
theorem B7385849 : Blo 2187435 7385849 := bstep (se 2 (by rfl) ⟨2769693, by rfl⟩ : syracuseStep 7385849 = 5539387) B5539387
theorem B4923899 : Blo 2187435 4923899 := bstep (se 1 (by rfl) ⟨3692924, by rfl⟩ : syracuseStep 4923899 = 7385849) B7385849
theorem B3282599 : Blo 2187435 3282599 := bstep (se 1 (by rfl) ⟨2461949, by rfl⟩ : syracuseStep 3282599 = 4923899) B4923899
theorem B2188399 : Blo 2187435 2188399 := bstep (se 1 (by rfl) ⟨1641299, by rfl⟩ : syracuseStep 2188399 = 3282599) B3282599
theorem B3282605 : Blo 2187435 3282605 := bbase (se 3 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 3282605 = 1230977) (by norm_num)
theorem B2188403 : Blo 2187435 2188403 := bstep (se 1 (by rfl) ⟨1641302, by rfl⟩ : syracuseStep 2188403 = 3282605) B3282605
theorem B4923917 : Blo 2187435 4923917 := bbase (se 3 (by rfl) ⟨923234, by rfl⟩ : syracuseStep 4923917 = 1846469) (by norm_num)
theorem B3282611 : Blo 2187435 3282611 := bstep (se 1 (by rfl) ⟨2461958, by rfl⟩ : syracuseStep 3282611 = 4923917) B4923917
theorem B2188407 : Blo 2187435 2188407 := bstep (se 1 (by rfl) ⟨1641305, by rfl⟩ : syracuseStep 2188407 = 3282611) B3282611
theorem B2769709 : Blo 2187435 2769709 := bbase (se 3 (by rfl) ⟨519320, by rfl⟩ : syracuseStep 2769709 = 1038641) (by norm_num)
theorem B3692945 : Blo 2187435 3692945 := bstep (se 2 (by rfl) ⟨1384854, by rfl⟩ : syracuseStep 3692945 = 2769709) B2769709
theorem B2461963 : Blo 2187435 2461963 := bstep (se 1 (by rfl) ⟨1846472, by rfl⟩ : syracuseStep 2461963 = 3692945) B3692945
theorem B3282617 : Blo 2187435 3282617 := bstep (se 2 (by rfl) ⟨1230981, by rfl⟩ : syracuseStep 3282617 = 2461963) B2461963
theorem B2188411 : Blo 2187435 2188411 := bstep (se 1 (by rfl) ⟨1641308, by rfl⟩ : syracuseStep 2188411 = 3282617) B3282617
theorem B3943597 : Blo 2187435 3943597 := bbase (se 3 (by rfl) ⟨739424, by rfl⟩ : syracuseStep 3943597 = 1478849) (by norm_num)
theorem B5258129 : Blo 2187435 5258129 := bstep (se 2 (by rfl) ⟨1971798, by rfl⟩ : syracuseStep 5258129 = 3943597) B3943597
theorem B14021677 : Blo 2187435 14021677 := bstep (se 3 (by rfl) ⟨2629064, by rfl⟩ : syracuseStep 14021677 = 5258129) B5258129
theorem B18695569 : Blo 2187435 18695569 := bstep (se 2 (by rfl) ⟨7010838, by rfl⟩ : syracuseStep 18695569 = 14021677) B14021677
theorem B24927425 : Blo 2187435 24927425 := bstep (se 2 (by rfl) ⟨9347784, by rfl⟩ : syracuseStep 24927425 = 18695569) B18695569
theorem B16618283 : Blo 2187435 16618283 := bstep (se 1 (by rfl) ⟨12463712, by rfl⟩ : syracuseStep 16618283 = 24927425) B24927425
theorem B11078855 : Blo 2187435 11078855 := bstep (se 1 (by rfl) ⟨8309141, by rfl⟩ : syracuseStep 11078855 = 16618283) B16618283
theorem B7385903 : Blo 2187435 7385903 := bstep (se 1 (by rfl) ⟨5539427, by rfl⟩ : syracuseStep 7385903 = 11078855) B11078855
theorem B4923935 : Blo 2187435 4923935 := bstep (se 1 (by rfl) ⟨3692951, by rfl⟩ : syracuseStep 4923935 = 7385903) B7385903
theorem B3282623 : Blo 2187435 3282623 := bstep (se 1 (by rfl) ⟨2461967, by rfl⟩ : syracuseStep 3282623 = 4923935) B4923935
theorem B2188415 : Blo 2187435 2188415 := bstep (se 1 (by rfl) ⟨1641311, by rfl⟩ : syracuseStep 2188415 = 3282623) B3282623
theorem B3282629 : Blo 2187435 3282629 := bbase (se 4 (by rfl) ⟨307746, by rfl⟩ : syracuseStep 3282629 = 615493) (by norm_num)
theorem B2188419 : Blo 2187435 2188419 := bstep (se 1 (by rfl) ⟨1641314, by rfl⟩ : syracuseStep 2188419 = 3282629) B3282629
theorem B3692965 : Blo 2187435 3692965 := bbase (se 4 (by rfl) ⟨346215, by rfl⟩ : syracuseStep 3692965 = 692431) (by norm_num)
theorem B4923953 : Blo 2187435 4923953 := bstep (se 2 (by rfl) ⟨1846482, by rfl⟩ : syracuseStep 4923953 = 3692965) B3692965
theorem B3282635 : Blo 2187435 3282635 := bstep (se 1 (by rfl) ⟨2461976, by rfl⟩ : syracuseStep 3282635 = 4923953) B4923953
theorem B2188423 : Blo 2187435 2188423 := bstep (se 1 (by rfl) ⟨1641317, by rfl⟩ : syracuseStep 2188423 = 3282635) B3282635
theorem B2461981 : Blo 2187435 2461981 := bbase (se 3 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 2461981 = 923243) (by norm_num)
theorem B3282641 : Blo 2187435 3282641 := bstep (se 2 (by rfl) ⟨1230990, by rfl⟩ : syracuseStep 3282641 = 2461981) B2461981
theorem B2188427 : Blo 2187435 2188427 := bstep (se 1 (by rfl) ⟨1641320, by rfl⟩ : syracuseStep 2188427 = 3282641) B3282641
theorem B7385957 : Blo 2187435 7385957 := bbase (se 4 (by rfl) ⟨692433, by rfl⟩ : syracuseStep 7385957 = 1384867) (by norm_num)
theorem B4923971 : Blo 2187435 4923971 := bstep (se 1 (by rfl) ⟨3692978, by rfl⟩ : syracuseStep 4923971 = 7385957) B7385957
theorem B3282647 : Blo 2187435 3282647 := bstep (se 1 (by rfl) ⟨2461985, by rfl⟩ : syracuseStep 3282647 = 4923971) B4923971
theorem B2188431 : Blo 2187435 2188431 := bstep (se 1 (by rfl) ⟨1641323, by rfl⟩ : syracuseStep 2188431 = 3282647) B3282647
theorem B3282653 : Blo 2187435 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B2188435 : Blo 2187435 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B4923989 : Blo 2187435 4923989 := bbase (se 8 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 4923989 = 57703) (by norm_num)
theorem B3282659 : Blo 2187435 3282659 := bstep (se 1 (by rfl) ⟨2461994, by rfl⟩ : syracuseStep 3282659 = 4923989) B4923989
theorem B2188439 : Blo 2187435 2188439 := bstep (se 1 (by rfl) ⟨1641329, by rfl⟩ : syracuseStep 2188439 = 3282659) B3282659
theorem B8994277 : Blo 2187435 8994277 := bbase (se 4 (by rfl) ⟨843213, by rfl⟩ : syracuseStep 8994277 = 1686427) (by norm_num)
theorem B11992369 : Blo 2187435 11992369 := bstep (se 2 (by rfl) ⟨4497138, by rfl⟩ : syracuseStep 11992369 = 8994277) B8994277
theorem B15989825 : Blo 2187435 15989825 := bstep (se 2 (by rfl) ⟨5996184, by rfl⟩ : syracuseStep 15989825 = 11992369) B11992369
theorem B10659883 : Blo 2187435 10659883 := bstep (se 1 (by rfl) ⟨7994912, by rfl⟩ : syracuseStep 10659883 = 15989825) B15989825
theorem B14213177 : Blo 2187435 14213177 := bstep (se 2 (by rfl) ⟨5329941, by rfl⟩ : syracuseStep 14213177 = 10659883) B10659883
theorem B9475451 : Blo 2187435 9475451 := bstep (se 1 (by rfl) ⟨7106588, by rfl⟩ : syracuseStep 9475451 = 14213177) B14213177
theorem B6316967 : Blo 2187435 6316967 := bstep (se 1 (by rfl) ⟨4737725, by rfl⟩ : syracuseStep 6316967 = 9475451) B9475451
theorem B16845245 : Blo 2187435 16845245 := bstep (se 3 (by rfl) ⟨3158483, by rfl⟩ : syracuseStep 16845245 = 6316967) B6316967
theorem B11230163 : Blo 2187435 11230163 := bstep (se 1 (by rfl) ⟨8422622, by rfl⟩ : syracuseStep 11230163 = 16845245) B16845245
theorem B7486775 : Blo 2187435 7486775 := bstep (se 1 (by rfl) ⟨5615081, by rfl⟩ : syracuseStep 7486775 = 11230163) B11230163
theorem B4991183 : Blo 2187435 4991183 := bstep (se 1 (by rfl) ⟨3743387, by rfl⟩ : syracuseStep 4991183 = 7486775) B7486775
theorem B3327455 : Blo 2187435 3327455 := bstep (se 1 (by rfl) ⟨2495591, by rfl⟩ : syracuseStep 3327455 = 4991183) B4991183
theorem B2218303 : Blo 2187435 2218303 := bstep (se 1 (by rfl) ⟨1663727, by rfl⟩ : syracuseStep 2218303 = 3327455) B3327455
theorem B2957737 : Blo 2187435 2957737 := bstep (se 2 (by rfl) ⟨1109151, by rfl⟩ : syracuseStep 2957737 = 2218303) B2218303
theorem B3943649 : Blo 2187435 3943649 := bstep (se 2 (by rfl) ⟨1478868, by rfl⟩ : syracuseStep 3943649 = 2957737) B2957737
theorem B2629099 : Blo 2187435 2629099 := bstep (se 1 (by rfl) ⟨1971824, by rfl⟩ : syracuseStep 2629099 = 3943649) B3943649
theorem B3505465 : Blo 2187435 3505465 := bstep (se 2 (by rfl) ⟨1314549, by rfl⟩ : syracuseStep 3505465 = 2629099) B2629099
theorem B4673953 : Blo 2187435 4673953 := bstep (se 2 (by rfl) ⟨1752732, by rfl⟩ : syracuseStep 4673953 = 3505465) B3505465
theorem B6231937 : Blo 2187435 6231937 := bstep (se 2 (by rfl) ⟨2336976, by rfl⟩ : syracuseStep 6231937 = 4673953) B4673953
theorem B8309249 : Blo 2187435 8309249 := bstep (se 2 (by rfl) ⟨3115968, by rfl⟩ : syracuseStep 8309249 = 6231937) B6231937
theorem B5539499 : Blo 2187435 5539499 := bstep (se 1 (by rfl) ⟨4154624, by rfl⟩ : syracuseStep 5539499 = 8309249) B8309249
theorem B3692999 : Blo 2187435 3692999 := bstep (se 1 (by rfl) ⟨2769749, by rfl⟩ : syracuseStep 3692999 = 5539499) B5539499
theorem B2461999 : Blo 2187435 2461999 := bstep (se 1 (by rfl) ⟨1846499, by rfl⟩ : syracuseStep 2461999 = 3692999) B3692999
theorem B3282665 : Blo 2187435 3282665 := bstep (se 2 (by rfl) ⟨1230999, by rfl⟩ : syracuseStep 3282665 = 2461999) B2461999
theorem B2188443 : Blo 2187435 2188443 := bstep (se 1 (by rfl) ⟨1641332, by rfl⟩ : syracuseStep 2188443 = 3282665) B3282665
theorem B15989845 : Blo 2187435 15989845 := bbase (se 8 (by rfl) ⟨93690, by rfl⟩ : syracuseStep 15989845 = 187381) (by norm_num)
theorem B21319793 : Blo 2187435 21319793 := bstep (se 2 (by rfl) ⟨7994922, by rfl⟩ : syracuseStep 21319793 = 15989845) B15989845
theorem B14213195 : Blo 2187435 14213195 := bstep (se 1 (by rfl) ⟨10659896, by rfl⟩ : syracuseStep 14213195 = 21319793) B21319793
theorem B9475463 : Blo 2187435 9475463 := bstep (se 1 (by rfl) ⟨7106597, by rfl⟩ : syracuseStep 9475463 = 14213195) B14213195
theorem B6316975 : Blo 2187435 6316975 := bstep (se 1 (by rfl) ⟨4737731, by rfl⟩ : syracuseStep 6316975 = 9475463) B9475463
theorem B8422633 : Blo 2187435 8422633 := bstep (se 2 (by rfl) ⟨3158487, by rfl⟩ : syracuseStep 8422633 = 6316975) B6316975
theorem B11230177 : Blo 2187435 11230177 := bstep (se 2 (by rfl) ⟨4211316, by rfl⟩ : syracuseStep 11230177 = 8422633) B8422633
theorem B14973569 : Blo 2187435 14973569 := bstep (se 2 (by rfl) ⟨5615088, by rfl⟩ : syracuseStep 14973569 = 11230177) B11230177
theorem B9982379 : Blo 2187435 9982379 := bstep (se 1 (by rfl) ⟨7486784, by rfl⟩ : syracuseStep 9982379 = 14973569) B14973569
theorem B6654919 : Blo 2187435 6654919 := bstep (se 1 (by rfl) ⟨4991189, by rfl⟩ : syracuseStep 6654919 = 9982379) B9982379
theorem B8873225 : Blo 2187435 8873225 := bstep (se 2 (by rfl) ⟨3327459, by rfl⟩ : syracuseStep 8873225 = 6654919) B6654919
theorem B5915483 : Blo 2187435 5915483 := bstep (se 1 (by rfl) ⟨4436612, by rfl⟩ : syracuseStep 5915483 = 8873225) B8873225
theorem B3943655 : Blo 2187435 3943655 := bstep (se 1 (by rfl) ⟨2957741, by rfl⟩ : syracuseStep 3943655 = 5915483) B5915483
theorem B2629103 : Blo 2187435 2629103 := bstep (se 1 (by rfl) ⟨1971827, by rfl⟩ : syracuseStep 2629103 = 3943655) B3943655
theorem B28043765 : Blo 2187435 28043765 := bstep (se 5 (by rfl) ⟨1314551, by rfl⟩ : syracuseStep 28043765 = 2629103) B2629103
theorem B18695843 : Blo 2187435 18695843 := bstep (se 1 (by rfl) ⟨14021882, by rfl⟩ : syracuseStep 18695843 = 28043765) B28043765
theorem B12463895 : Blo 2187435 12463895 := bstep (se 1 (by rfl) ⟨9347921, by rfl⟩ : syracuseStep 12463895 = 18695843) B18695843
theorem B8309263 : Blo 2187435 8309263 := bstep (se 1 (by rfl) ⟨6231947, by rfl⟩ : syracuseStep 8309263 = 12463895) B12463895
theorem B11079017 : Blo 2187435 11079017 := bstep (se 2 (by rfl) ⟨4154631, by rfl⟩ : syracuseStep 11079017 = 8309263) B8309263
theorem B7386011 : Blo 2187435 7386011 := bstep (se 1 (by rfl) ⟨5539508, by rfl⟩ : syracuseStep 7386011 = 11079017) B11079017
theorem B4924007 : Blo 2187435 4924007 := bstep (se 1 (by rfl) ⟨3693005, by rfl⟩ : syracuseStep 4924007 = 7386011) B7386011
theorem B3282671 : Blo 2187435 3282671 := bstep (se 1 (by rfl) ⟨2462003, by rfl⟩ : syracuseStep 3282671 = 4924007) B4924007
theorem B2188447 : Blo 2187435 2188447 := bstep (se 1 (by rfl) ⟨1641335, by rfl⟩ : syracuseStep 2188447 = 3282671) B3282671
theorem B3282677 : Blo 2187435 3282677 := bbase (se 5 (by rfl) ⟨153875, by rfl⟩ : syracuseStep 3282677 = 307751) (by norm_num)
theorem B2188451 : Blo 2187435 2188451 := bstep (se 1 (by rfl) ⟨1641338, by rfl⟩ : syracuseStep 2188451 = 3282677) B3282677
theorem B9347957 : Blo 2187435 9347957 := bbase (se 5 (by rfl) ⟨438185, by rfl⟩ : syracuseStep 9347957 = 876371) (by norm_num)
theorem B6231971 : Blo 2187435 6231971 := bstep (se 1 (by rfl) ⟨4673978, by rfl⟩ : syracuseStep 6231971 = 9347957) B9347957
theorem B4154647 : Blo 2187435 4154647 := bstep (se 1 (by rfl) ⟨3115985, by rfl⟩ : syracuseStep 4154647 = 6231971) B6231971
theorem B5539529 : Blo 2187435 5539529 := bstep (se 2 (by rfl) ⟨2077323, by rfl⟩ : syracuseStep 5539529 = 4154647) B4154647
theorem B3693019 : Blo 2187435 3693019 := bstep (se 1 (by rfl) ⟨2769764, by rfl⟩ : syracuseStep 3693019 = 5539529) B5539529
theorem B4924025 : Blo 2187435 4924025 := bstep (se 2 (by rfl) ⟨1846509, by rfl⟩ : syracuseStep 4924025 = 3693019) B3693019
theorem B3282683 : Blo 2187435 3282683 := bstep (se 1 (by rfl) ⟨2462012, by rfl⟩ : syracuseStep 3282683 = 4924025) B4924025
theorem B2188455 : Blo 2187435 2188455 := bstep (se 1 (by rfl) ⟨1641341, by rfl⟩ : syracuseStep 2188455 = 3282683) B3282683
theorem B2462017 : Blo 2187435 2462017 := bbase (se 2 (by rfl) ⟨923256, by rfl⟩ : syracuseStep 2462017 = 1846513) (by norm_num)
theorem B3282689 : Blo 2187435 3282689 := bstep (se 2 (by rfl) ⟨1231008, by rfl⟩ : syracuseStep 3282689 = 2462017) B2462017
theorem B2188459 : Blo 2187435 2188459 := bstep (se 1 (by rfl) ⟨1641344, by rfl⟩ : syracuseStep 2188459 = 3282689) B3282689
theorem B5539549 : Blo 2187435 5539549 := bbase (se 3 (by rfl) ⟨1038665, by rfl⟩ : syracuseStep 5539549 = 2077331) (by norm_num)
theorem B7386065 : Blo 2187435 7386065 := bstep (se 2 (by rfl) ⟨2769774, by rfl⟩ : syracuseStep 7386065 = 5539549) B5539549
theorem B4924043 : Blo 2187435 4924043 := bstep (se 1 (by rfl) ⟨3693032, by rfl⟩ : syracuseStep 4924043 = 7386065) B7386065
theorem B3282695 : Blo 2187435 3282695 := bstep (se 1 (by rfl) ⟨2462021, by rfl⟩ : syracuseStep 3282695 = 4924043) B4924043
theorem B2188463 : Blo 2187435 2188463 := bstep (se 1 (by rfl) ⟨1641347, by rfl⟩ : syracuseStep 2188463 = 3282695) B3282695
theorem B3282701 : Blo 2187435 3282701 := bbase (se 3 (by rfl) ⟨615506, by rfl⟩ : syracuseStep 3282701 = 1231013) (by norm_num)
theorem B2188467 : Blo 2187435 2188467 := bstep (se 1 (by rfl) ⟨1641350, by rfl⟩ : syracuseStep 2188467 = 3282701) B3282701
theorem B4924061 : Blo 2187435 4924061 := bbase (se 3 (by rfl) ⟨923261, by rfl⟩ : syracuseStep 4924061 = 1846523) (by norm_num)
theorem B3282707 : Blo 2187435 3282707 := bstep (se 1 (by rfl) ⟨2462030, by rfl⟩ : syracuseStep 3282707 = 4924061) B4924061
theorem B2188471 : Blo 2187435 2188471 := bstep (se 1 (by rfl) ⟨1641353, by rfl⟩ : syracuseStep 2188471 = 3282707) B3282707
theorem B3693053 : Blo 2187435 3693053 := bbase (se 3 (by rfl) ⟨692447, by rfl⟩ : syracuseStep 3693053 = 1384895) (by norm_num)
theorem B2462035 : Blo 2187435 2462035 := bstep (se 1 (by rfl) ⟨1846526, by rfl⟩ : syracuseStep 2462035 = 3693053) B3693053
theorem B3282713 : Blo 2187435 3282713 := bstep (se 2 (by rfl) ⟨1231017, by rfl⟩ : syracuseStep 3282713 = 2462035) B2462035
theorem B2188475 : Blo 2187435 2188475 := bstep (se 1 (by rfl) ⟨1641356, by rfl⟩ : syracuseStep 2188475 = 3282713) B3282713
theorem B4674029 : Blo 2187435 4674029 := bbase (se 3 (by rfl) ⟨876380, by rfl⟩ : syracuseStep 4674029 = 1752761) (by norm_num)
theorem B12464077 : Blo 2187435 12464077 := bstep (se 3 (by rfl) ⟨2337014, by rfl⟩ : syracuseStep 12464077 = 4674029) B4674029
theorem B16618769 : Blo 2187435 16618769 := bstep (se 2 (by rfl) ⟨6232038, by rfl⟩ : syracuseStep 16618769 = 12464077) B12464077
theorem B11079179 : Blo 2187435 11079179 := bstep (se 1 (by rfl) ⟨8309384, by rfl⟩ : syracuseStep 11079179 = 16618769) B16618769
theorem B7386119 : Blo 2187435 7386119 := bstep (se 1 (by rfl) ⟨5539589, by rfl⟩ : syracuseStep 7386119 = 11079179) B11079179
theorem B4924079 : Blo 2187435 4924079 := bstep (se 1 (by rfl) ⟨3693059, by rfl⟩ : syracuseStep 4924079 = 7386119) B7386119
theorem B3282719 : Blo 2187435 3282719 := bstep (se 1 (by rfl) ⟨2462039, by rfl⟩ : syracuseStep 3282719 = 4924079) B4924079
theorem B2188479 : Blo 2187435 2188479 := bstep (se 1 (by rfl) ⟨1641359, by rfl⟩ : syracuseStep 2188479 = 3282719) B3282719
theorem B3282725 : Blo 2187435 3282725 := bbase (se 4 (by rfl) ⟨307755, by rfl⟩ : syracuseStep 3282725 = 615511) (by norm_num)
theorem B2188483 : Blo 2187435 2188483 := bstep (se 1 (by rfl) ⟨1641362, by rfl⟩ : syracuseStep 2188483 = 3282725) B3282725
theorem B2769805 : Blo 2187435 2769805 := bbase (se 3 (by rfl) ⟨519338, by rfl⟩ : syracuseStep 2769805 = 1038677) (by norm_num)
theorem B3693073 : Blo 2187435 3693073 := bstep (se 2 (by rfl) ⟨1384902, by rfl⟩ : syracuseStep 3693073 = 2769805) B2769805
theorem B4924097 : Blo 2187435 4924097 := bstep (se 2 (by rfl) ⟨1846536, by rfl⟩ : syracuseStep 4924097 = 3693073) B3693073
theorem B3282731 : Blo 2187435 3282731 := bstep (se 1 (by rfl) ⟨2462048, by rfl⟩ : syracuseStep 3282731 = 4924097) B4924097
theorem B2188487 : Blo 2187435 2188487 := bstep (se 1 (by rfl) ⟨1641365, by rfl⟩ : syracuseStep 2188487 = 3282731) B3282731
theorem B2462053 : Blo 2187435 2462053 := bbase (se 4 (by rfl) ⟨230817, by rfl⟩ : syracuseStep 2462053 = 461635) (by norm_num)
theorem B3282737 : Blo 2187435 3282737 := bstep (se 2 (by rfl) ⟨1231026, by rfl⟩ : syracuseStep 3282737 = 2462053) B2462053
theorem B2188491 : Blo 2187435 2188491 := bstep (se 1 (by rfl) ⟨1641368, by rfl⟩ : syracuseStep 2188491 = 3282737) B3282737
theorem B6232085 : Blo 2187435 6232085 := bbase (se 6 (by rfl) ⟨146064, by rfl⟩ : syracuseStep 6232085 = 292129) (by norm_num)
theorem B4154723 : Blo 2187435 4154723 := bstep (se 1 (by rfl) ⟨3116042, by rfl⟩ : syracuseStep 4154723 = 6232085) B6232085
theorem B2769815 : Blo 2187435 2769815 := bstep (se 1 (by rfl) ⟨2077361, by rfl⟩ : syracuseStep 2769815 = 4154723) B4154723
theorem B7386173 : Blo 2187435 7386173 := bstep (se 3 (by rfl) ⟨1384907, by rfl⟩ : syracuseStep 7386173 = 2769815) B2769815
theorem B4924115 : Blo 2187435 4924115 := bstep (se 1 (by rfl) ⟨3693086, by rfl⟩ : syracuseStep 4924115 = 7386173) B7386173
theorem B3282743 : Blo 2187435 3282743 := bstep (se 1 (by rfl) ⟨2462057, by rfl⟩ : syracuseStep 3282743 = 4924115) B4924115
theorem B2188495 : Blo 2187435 2188495 := bstep (se 1 (by rfl) ⟨1641371, by rfl⟩ : syracuseStep 2188495 = 3282743) B3282743
theorem B3282749 : Blo 2187435 3282749 := bbase (se 3 (by rfl) ⟨615515, by rfl⟩ : syracuseStep 3282749 = 1231031) (by norm_num)
theorem B2188499 : Blo 2187435 2188499 := bstep (se 1 (by rfl) ⟨1641374, by rfl⟩ : syracuseStep 2188499 = 3282749) B3282749
theorem B4924133 : Blo 2187435 4924133 := bbase (se 4 (by rfl) ⟨461637, by rfl⟩ : syracuseStep 4924133 = 923275) (by norm_num)
theorem B3282755 : Blo 2187435 3282755 := bstep (se 1 (by rfl) ⟨2462066, by rfl⟩ : syracuseStep 3282755 = 4924133) B4924133
theorem B2188503 : Blo 2187435 2188503 := bstep (se 1 (by rfl) ⟨1641377, by rfl⟩ : syracuseStep 2188503 = 3282755) B3282755
theorem B5539661 : Blo 2187435 5539661 := bbase (se 3 (by rfl) ⟨1038686, by rfl⟩ : syracuseStep 5539661 = 2077373) (by norm_num)
theorem B3693107 : Blo 2187435 3693107 := bstep (se 1 (by rfl) ⟨2769830, by rfl⟩ : syracuseStep 3693107 = 5539661) B5539661
theorem B2462071 : Blo 2187435 2462071 := bstep (se 1 (by rfl) ⟨1846553, by rfl⟩ : syracuseStep 2462071 = 3693107) B3693107
theorem B3282761 : Blo 2187435 3282761 := bstep (se 2 (by rfl) ⟨1231035, by rfl⟩ : syracuseStep 3282761 = 2462071) B2462071
theorem B2188507 : Blo 2187435 2188507 := bstep (se 1 (by rfl) ⟨1641380, by rfl⟩ : syracuseStep 2188507 = 3282761) B3282761
theorem B2337049 : Blo 2187435 2337049 := bbase (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) (by norm_num)
theorem B3116065 : Blo 2187435 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B4154753 : Blo 2187435 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B11079341 : Blo 2187435 11079341 := bstep (se 3 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 11079341 = 4154753) B4154753
theorem B7386227 : Blo 2187435 7386227 := bstep (se 1 (by rfl) ⟨5539670, by rfl⟩ : syracuseStep 7386227 = 11079341) B11079341
theorem B4924151 : Blo 2187435 4924151 := bstep (se 1 (by rfl) ⟨3693113, by rfl⟩ : syracuseStep 4924151 = 7386227) B7386227
theorem B3282767 : Blo 2187435 3282767 := bstep (se 1 (by rfl) ⟨2462075, by rfl⟩ : syracuseStep 3282767 = 4924151) B4924151
theorem B2188511 : Blo 2187435 2188511 := bstep (se 1 (by rfl) ⟨1641383, by rfl⟩ : syracuseStep 2188511 = 3282767) B3282767
theorem B3282773 : Blo 2187435 3282773 := bbase (se 9 (by rfl) ⟨9617, by rfl⟩ : syracuseStep 3282773 = 19235) (by norm_num)
theorem B2188515 : Blo 2187435 2188515 := bstep (se 1 (by rfl) ⟨1641386, by rfl⟩ : syracuseStep 2188515 = 3282773) B3282773
theorem B7011173 : Blo 2187435 7011173 := bbase (se 4 (by rfl) ⟨657297, by rfl⟩ : syracuseStep 7011173 = 1314595) (by norm_num)
theorem B4674115 : Blo 2187435 4674115 := bstep (se 1 (by rfl) ⟨3505586, by rfl⟩ : syracuseStep 4674115 = 7011173) B7011173
theorem B6232153 : Blo 2187435 6232153 := bstep (se 2 (by rfl) ⟨2337057, by rfl⟩ : syracuseStep 6232153 = 4674115) B4674115
theorem B8309537 : Blo 2187435 8309537 := bstep (se 2 (by rfl) ⟨3116076, by rfl⟩ : syracuseStep 8309537 = 6232153) B6232153
theorem B5539691 : Blo 2187435 5539691 := bstep (se 1 (by rfl) ⟨4154768, by rfl⟩ : syracuseStep 5539691 = 8309537) B8309537
theorem B3693127 : Blo 2187435 3693127 := bstep (se 1 (by rfl) ⟨2769845, by rfl⟩ : syracuseStep 3693127 = 5539691) B5539691
theorem B4924169 : Blo 2187435 4924169 := bstep (se 2 (by rfl) ⟨1846563, by rfl⟩ : syracuseStep 4924169 = 3693127) B3693127
theorem B3282779 : Blo 2187435 3282779 := bstep (se 1 (by rfl) ⟨2462084, by rfl⟩ : syracuseStep 3282779 = 4924169) B4924169
theorem B2188519 : Blo 2187435 2188519 := bstep (se 1 (by rfl) ⟨1641389, by rfl⟩ : syracuseStep 2188519 = 3282779) B3282779
theorem B2462089 : Blo 2187435 2462089 := bbase (se 2 (by rfl) ⟨923283, by rfl⟩ : syracuseStep 2462089 = 1846567) (by norm_num)
theorem B3282785 : Blo 2187435 3282785 := bstep (se 2 (by rfl) ⟨1231044, by rfl⟩ : syracuseStep 3282785 = 2462089) B2462089
theorem B2188523 : Blo 2187435 2188523 := bstep (se 1 (by rfl) ⟨1641392, by rfl⟩ : syracuseStep 2188523 = 3282785) B3282785
theorem B39930965 : Blo 2187435 39930965 := bbase (se 8 (by rfl) ⟨233970, by rfl⟩ : syracuseStep 39930965 = 467941) (by norm_num)
theorem B26620643 : Blo 2187435 26620643 := bstep (se 1 (by rfl) ⟨19965482, by rfl⟩ : syracuseStep 26620643 = 39930965) B39930965
theorem B17747095 : Blo 2187435 17747095 := bstep (se 1 (by rfl) ⟨13310321, by rfl⟩ : syracuseStep 17747095 = 26620643) B26620643
theorem B23662793 : Blo 2187435 23662793 := bstep (se 2 (by rfl) ⟨8873547, by rfl⟩ : syracuseStep 23662793 = 17747095) B17747095
theorem B63100781 : Blo 2187435 63100781 := bstep (se 3 (by rfl) ⟨11831396, by rfl⟩ : syracuseStep 63100781 = 23662793) B23662793
theorem B42067187 : Blo 2187435 42067187 := bstep (se 1 (by rfl) ⟨31550390, by rfl⟩ : syracuseStep 42067187 = 63100781) B63100781
theorem B28044791 : Blo 2187435 28044791 := bstep (se 1 (by rfl) ⟨21033593, by rfl⟩ : syracuseStep 28044791 = 42067187) B42067187
theorem B18696527 : Blo 2187435 18696527 := bstep (se 1 (by rfl) ⟨14022395, by rfl⟩ : syracuseStep 18696527 = 28044791) B28044791
theorem B12464351 : Blo 2187435 12464351 := bstep (se 1 (by rfl) ⟨9348263, by rfl⟩ : syracuseStep 12464351 = 18696527) B18696527
theorem B8309567 : Blo 2187435 8309567 := bstep (se 1 (by rfl) ⟨6232175, by rfl⟩ : syracuseStep 8309567 = 12464351) B12464351
theorem B5539711 : Blo 2187435 5539711 := bstep (se 1 (by rfl) ⟨4154783, by rfl⟩ : syracuseStep 5539711 = 8309567) B8309567
theorem B7386281 : Blo 2187435 7386281 := bstep (se 2 (by rfl) ⟨2769855, by rfl⟩ : syracuseStep 7386281 = 5539711) B5539711
theorem B4924187 : Blo 2187435 4924187 := bstep (se 1 (by rfl) ⟨3693140, by rfl⟩ : syracuseStep 4924187 = 7386281) B7386281
theorem B3282791 : Blo 2187435 3282791 := bstep (se 1 (by rfl) ⟨2462093, by rfl⟩ : syracuseStep 3282791 = 4924187) B4924187
theorem B2188527 : Blo 2187435 2188527 := bstep (se 1 (by rfl) ⟨1641395, by rfl⟩ : syracuseStep 2188527 = 3282791) B3282791
theorem B3282797 : Blo 2187435 3282797 := bbase (se 3 (by rfl) ⟨615524, by rfl⟩ : syracuseStep 3282797 = 1231049) (by norm_num)
theorem B2188531 : Blo 2187435 2188531 := bstep (se 1 (by rfl) ⟨1641398, by rfl⟩ : syracuseStep 2188531 = 3282797) B3282797
theorem B4924205 : Blo 2187435 4924205 := bbase (se 3 (by rfl) ⟨923288, by rfl⟩ : syracuseStep 4924205 = 1846577) (by norm_num)
theorem B3282803 : Blo 2187435 3282803 := bstep (se 1 (by rfl) ⟨2462102, by rfl⟩ : syracuseStep 3282803 = 4924205) B4924205
theorem B2188535 : Blo 2187435 2188535 := bstep (se 1 (by rfl) ⟨1641401, by rfl⟩ : syracuseStep 2188535 = 3282803) B3282803
theorem B5258429 : Blo 2187435 5258429 := bbase (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) (by norm_num)
theorem B3505619 : Blo 2187435 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B9348317 : Blo 2187435 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B6232211 : Blo 2187435 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B4154807 : Blo 2187435 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B2769871 : Blo 2187435 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B3693161 : Blo 2187435 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B2462107 : Blo 2187435 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B3282809 : Blo 2187435 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B2188539 : Blo 2187435 2188539 := bstep (se 1 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 2188539 = 3282809) B3282809
theorem B2368969 : Blo 2187435 2368969 := bbase (se 2 (by rfl) ⟨888363, by rfl⟩ : syracuseStep 2368969 = 1776727) (by norm_num)
theorem B12634501 : Blo 2187435 12634501 := bstep (se 4 (by rfl) ⟨1184484, by rfl⟩ : syracuseStep 12634501 = 2368969) B2368969
theorem B16846001 : Blo 2187435 16846001 := bstep (se 2 (by rfl) ⟨6317250, by rfl⟩ : syracuseStep 16846001 = 12634501) B12634501
theorem B11230667 : Blo 2187435 11230667 := bstep (se 1 (by rfl) ⟨8423000, by rfl⟩ : syracuseStep 11230667 = 16846001) B16846001
theorem B7487111 : Blo 2187435 7487111 := bstep (se 1 (by rfl) ⟨5615333, by rfl⟩ : syracuseStep 7487111 = 11230667) B11230667
theorem B19965629 : Blo 2187435 19965629 := bstep (se 3 (by rfl) ⟨3743555, by rfl⟩ : syracuseStep 19965629 = 7487111) B7487111
theorem B13310419 : Blo 2187435 13310419 := bstep (se 1 (by rfl) ⟨9982814, by rfl⟩ : syracuseStep 13310419 = 19965629) B19965629
theorem B17747225 : Blo 2187435 17747225 := bstep (se 2 (by rfl) ⟨6655209, by rfl⟩ : syracuseStep 17747225 = 13310419) B13310419
theorem B11831483 : Blo 2187435 11831483 := bstep (se 1 (by rfl) ⟨8873612, by rfl⟩ : syracuseStep 11831483 = 17747225) B17747225
theorem B7887655 : Blo 2187435 7887655 := bstep (se 1 (by rfl) ⟨5915741, by rfl⟩ : syracuseStep 7887655 = 11831483) B11831483
theorem B10516873 : Blo 2187435 10516873 := bstep (se 2 (by rfl) ⟨3943827, by rfl⟩ : syracuseStep 10516873 = 7887655) B7887655
theorem B14022497 : Blo 2187435 14022497 := bstep (se 2 (by rfl) ⟨5258436, by rfl⟩ : syracuseStep 14022497 = 10516873) B10516873
theorem B37393325 : Blo 2187435 37393325 := bstep (se 3 (by rfl) ⟨7011248, by rfl⟩ : syracuseStep 37393325 = 14022497) B14022497
theorem B24928883 : Blo 2187435 24928883 := bstep (se 1 (by rfl) ⟨18696662, by rfl⟩ : syracuseStep 24928883 = 37393325) B37393325
theorem B16619255 : Blo 2187435 16619255 := bstep (se 1 (by rfl) ⟨12464441, by rfl⟩ : syracuseStep 16619255 = 24928883) B24928883
theorem B11079503 : Blo 2187435 11079503 := bstep (se 1 (by rfl) ⟨8309627, by rfl⟩ : syracuseStep 11079503 = 16619255) B16619255
theorem B7386335 : Blo 2187435 7386335 := bstep (se 1 (by rfl) ⟨5539751, by rfl⟩ : syracuseStep 7386335 = 11079503) B11079503
theorem B4924223 : Blo 2187435 4924223 := bstep (se 1 (by rfl) ⟨3693167, by rfl⟩ : syracuseStep 4924223 = 7386335) B7386335
theorem B3282815 : Blo 2187435 3282815 := bstep (se 1 (by rfl) ⟨2462111, by rfl⟩ : syracuseStep 3282815 = 4924223) B4924223
theorem B2188543 : Blo 2187435 2188543 := bstep (se 1 (by rfl) ⟨1641407, by rfl⟩ : syracuseStep 2188543 = 3282815) B3282815
theorem B3282821 : Blo 2187435 3282821 := bbase (se 4 (by rfl) ⟨307764, by rfl⟩ : syracuseStep 3282821 = 615529) (by norm_num)
theorem B2188547 : Blo 2187435 2188547 := bstep (se 1 (by rfl) ⟨1641410, by rfl⟩ : syracuseStep 2188547 = 3282821) B3282821
theorem B3693181 : Blo 2187435 3693181 := bbase (se 3 (by rfl) ⟨692471, by rfl⟩ : syracuseStep 3693181 = 1384943) (by norm_num)
theorem B4924241 : Blo 2187435 4924241 := bstep (se 2 (by rfl) ⟨1846590, by rfl⟩ : syracuseStep 4924241 = 3693181) B3693181
theorem B3282827 : Blo 2187435 3282827 := bstep (se 1 (by rfl) ⟨2462120, by rfl⟩ : syracuseStep 3282827 = 4924241) B4924241
theorem B2188551 : Blo 2187435 2188551 := bstep (se 1 (by rfl) ⟨1641413, by rfl⟩ : syracuseStep 2188551 = 3282827) B3282827
theorem B2462125 : Blo 2187435 2462125 := bbase (se 3 (by rfl) ⟨461648, by rfl⟩ : syracuseStep 2462125 = 923297) (by norm_num)
theorem B3282833 : Blo 2187435 3282833 := bstep (se 2 (by rfl) ⟨1231062, by rfl⟩ : syracuseStep 3282833 = 2462125) B2462125
theorem B2188555 : Blo 2187435 2188555 := bstep (se 1 (by rfl) ⟨1641416, by rfl⟩ : syracuseStep 2188555 = 3282833) B3282833
theorem B7386389 : Blo 2187435 7386389 := bbase (se 6 (by rfl) ⟨173118, by rfl⟩ : syracuseStep 7386389 = 346237) (by norm_num)
theorem B4924259 : Blo 2187435 4924259 := bstep (se 1 (by rfl) ⟨3693194, by rfl⟩ : syracuseStep 4924259 = 7386389) B7386389
theorem B3282839 : Blo 2187435 3282839 := bstep (se 1 (by rfl) ⟨2462129, by rfl⟩ : syracuseStep 3282839 = 4924259) B4924259
theorem B2188559 : Blo 2187435 2188559 := bstep (se 1 (by rfl) ⟨1641419, by rfl⟩ : syracuseStep 2188559 = 3282839) B3282839
theorem B3282845 : Blo 2187435 3282845 := bbase (se 3 (by rfl) ⟨615533, by rfl⟩ : syracuseStep 3282845 = 1231067) (by norm_num)
theorem B2188563 : Blo 2187435 2188563 := bstep (se 1 (by rfl) ⟨1641422, by rfl⟩ : syracuseStep 2188563 = 3282845) B3282845
theorem B4924277 : Blo 2187435 4924277 := bbase (se 5 (by rfl) ⟨230825, by rfl⟩ : syracuseStep 4924277 = 461651) (by norm_num)
theorem B3282851 : Blo 2187435 3282851 := bstep (se 1 (by rfl) ⟨2462138, by rfl⟩ : syracuseStep 3282851 = 4924277) B4924277
theorem B2188567 : Blo 2187435 2188567 := bstep (se 1 (by rfl) ⟨1641425, by rfl⟩ : syracuseStep 2188567 = 3282851) B3282851
theorem B2957909 : Blo 2187435 2957909 := bbase (se 8 (by rfl) ⟨17331, by rfl⟩ : syracuseStep 2957909 = 34663) (by norm_num)
theorem B31551029 : Blo 2187435 31551029 := bstep (se 5 (by rfl) ⟨1478954, by rfl⟩ : syracuseStep 31551029 = 2957909) B2957909
theorem B21034019 : Blo 2187435 21034019 := bstep (se 1 (by rfl) ⟨15775514, by rfl⟩ : syracuseStep 21034019 = 31551029) B31551029
theorem B14022679 : Blo 2187435 14022679 := bstep (se 1 (by rfl) ⟨10517009, by rfl⟩ : syracuseStep 14022679 = 21034019) B21034019
theorem B18696905 : Blo 2187435 18696905 := bstep (se 2 (by rfl) ⟨7011339, by rfl⟩ : syracuseStep 18696905 = 14022679) B14022679
theorem B12464603 : Blo 2187435 12464603 := bstep (se 1 (by rfl) ⟨9348452, by rfl⟩ : syracuseStep 12464603 = 18696905) B18696905
theorem B8309735 : Blo 2187435 8309735 := bstep (se 1 (by rfl) ⟨6232301, by rfl⟩ : syracuseStep 8309735 = 12464603) B12464603
theorem B5539823 : Blo 2187435 5539823 := bstep (se 1 (by rfl) ⟨4154867, by rfl⟩ : syracuseStep 5539823 = 8309735) B8309735
theorem B3693215 : Blo 2187435 3693215 := bstep (se 1 (by rfl) ⟨2769911, by rfl⟩ : syracuseStep 3693215 = 5539823) B5539823
theorem B2462143 : Blo 2187435 2462143 := bstep (se 1 (by rfl) ⟨1846607, by rfl⟩ : syracuseStep 2462143 = 3693215) B3693215
theorem B3282857 : Blo 2187435 3282857 := bstep (se 2 (by rfl) ⟨1231071, by rfl⟩ : syracuseStep 3282857 = 2462143) B2462143
theorem B2188571 : Blo 2187435 2188571 := bstep (se 1 (by rfl) ⟨1641428, by rfl⟩ : syracuseStep 2188571 = 3282857) B3282857
theorem B8309749 : Blo 2187435 8309749 := bbase (se 5 (by rfl) ⟨389519, by rfl⟩ : syracuseStep 8309749 = 779039) (by norm_num)
theorem B11079665 : Blo 2187435 11079665 := bstep (se 2 (by rfl) ⟨4154874, by rfl⟩ : syracuseStep 11079665 = 8309749) B8309749
theorem B7386443 : Blo 2187435 7386443 := bstep (se 1 (by rfl) ⟨5539832, by rfl⟩ : syracuseStep 7386443 = 11079665) B11079665
theorem B4924295 : Blo 2187435 4924295 := bstep (se 1 (by rfl) ⟨3693221, by rfl⟩ : syracuseStep 4924295 = 7386443) B7386443
theorem B3282863 : Blo 2187435 3282863 := bstep (se 1 (by rfl) ⟨2462147, by rfl⟩ : syracuseStep 3282863 = 4924295) B4924295
theorem B2188575 : Blo 2187435 2188575 := bstep (se 1 (by rfl) ⟨1641431, by rfl⟩ : syracuseStep 2188575 = 3282863) B3282863
theorem B3282869 : Blo 2187435 3282869 := bbase (se 5 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 3282869 = 307769) (by norm_num)
theorem B2188579 : Blo 2187435 2188579 := bstep (se 1 (by rfl) ⟨1641434, by rfl⟩ : syracuseStep 2188579 = 3282869) B3282869
theorem B5539853 : Blo 2187435 5539853 := bbase (se 3 (by rfl) ⟨1038722, by rfl⟩ : syracuseStep 5539853 = 2077445) (by norm_num)
theorem B3693235 : Blo 2187435 3693235 := bstep (se 1 (by rfl) ⟨2769926, by rfl⟩ : syracuseStep 3693235 = 5539853) B5539853
theorem B4924313 : Blo 2187435 4924313 := bstep (se 2 (by rfl) ⟨1846617, by rfl⟩ : syracuseStep 4924313 = 3693235) B3693235
theorem B3282875 : Blo 2187435 3282875 := bstep (se 1 (by rfl) ⟨2462156, by rfl⟩ : syracuseStep 3282875 = 4924313) B4924313
theorem B2188583 : Blo 2187435 2188583 := bstep (se 1 (by rfl) ⟨1641437, by rfl⟩ : syracuseStep 2188583 = 3282875) B3282875
theorem B2462161 : Blo 2187435 2462161 := bbase (se 2 (by rfl) ⟨923310, by rfl⟩ : syracuseStep 2462161 = 1846621) (by norm_num)
theorem B3282881 : Blo 2187435 3282881 := bstep (se 2 (by rfl) ⟨1231080, by rfl⟩ : syracuseStep 3282881 = 2462161) B2462161
theorem B2188587 : Blo 2187435 2188587 := bstep (se 1 (by rfl) ⟨1641440, by rfl⟩ : syracuseStep 2188587 = 3282881) B3282881
theorem B4674269 : Blo 2187435 4674269 := bbase (se 3 (by rfl) ⟨876425, by rfl⟩ : syracuseStep 4674269 = 1752851) (by norm_num)
theorem B3116179 : Blo 2187435 3116179 := bstep (se 1 (by rfl) ⟨2337134, by rfl⟩ : syracuseStep 3116179 = 4674269) B4674269
theorem B4154905 : Blo 2187435 4154905 := bstep (se 2 (by rfl) ⟨1558089, by rfl⟩ : syracuseStep 4154905 = 3116179) B3116179
theorem B5539873 : Blo 2187435 5539873 := bstep (se 2 (by rfl) ⟨2077452, by rfl⟩ : syracuseStep 5539873 = 4154905) B4154905
theorem B7386497 : Blo 2187435 7386497 := bstep (se 2 (by rfl) ⟨2769936, by rfl⟩ : syracuseStep 7386497 = 5539873) B5539873
theorem B4924331 : Blo 2187435 4924331 := bstep (se 1 (by rfl) ⟨3693248, by rfl⟩ : syracuseStep 4924331 = 7386497) B7386497
theorem B3282887 : Blo 2187435 3282887 := bstep (se 1 (by rfl) ⟨2462165, by rfl⟩ : syracuseStep 3282887 = 4924331) B4924331
theorem B2188591 : Blo 2187435 2188591 := bstep (se 1 (by rfl) ⟨1641443, by rfl⟩ : syracuseStep 2188591 = 3282887) B3282887
theorem B3282893 : Blo 2187435 3282893 := bbase (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) (by norm_num)
theorem B2188595 : Blo 2187435 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B4924349 : Blo 2187435 4924349 := bbase (se 3 (by rfl) ⟨923315, by rfl⟩ : syracuseStep 4924349 = 1846631) (by norm_num)
theorem B3282899 : Blo 2187435 3282899 := bstep (se 1 (by rfl) ⟨2462174, by rfl⟩ : syracuseStep 3282899 = 4924349) B4924349
theorem B2188599 : Blo 2187435 2188599 := bstep (se 1 (by rfl) ⟨1641449, by rfl⟩ : syracuseStep 2188599 = 3282899) B3282899
theorem B3693269 : Blo 2187435 3693269 := bbase (se 7 (by rfl) ⟨43280, by rfl⟩ : syracuseStep 3693269 = 86561) (by norm_num)
theorem B2462179 : Blo 2187435 2462179 := bstep (se 1 (by rfl) ⟨1846634, by rfl⟩ : syracuseStep 2462179 = 3693269) B3693269
theorem B3282905 : Blo 2187435 3282905 := bstep (se 2 (by rfl) ⟨1231089, by rfl⟩ : syracuseStep 3282905 = 2462179) B2462179
theorem B2188603 : Blo 2187435 2188603 := bstep (se 1 (by rfl) ⟨1641452, by rfl⟩ : syracuseStep 2188603 = 3282905) B3282905
theorem B2495777 : Blo 2187435 2495777 := bbase (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) (by norm_num)
theorem B26621621 : Blo 2187435 26621621 := bstep (se 5 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 26621621 = 2495777) B2495777
theorem B17747747 : Blo 2187435 17747747 := bstep (se 1 (by rfl) ⟨13310810, by rfl⟩ : syracuseStep 17747747 = 26621621) B26621621
theorem B11831831 : Blo 2187435 11831831 := bstep (se 1 (by rfl) ⟨8873873, by rfl⟩ : syracuseStep 11831831 = 17747747) B17747747
theorem B7887887 : Blo 2187435 7887887 := bstep (se 1 (by rfl) ⟨5915915, by rfl⟩ : syracuseStep 7887887 = 11831831) B11831831
theorem B5258591 : Blo 2187435 5258591 := bstep (se 1 (by rfl) ⟨3943943, by rfl⟩ : syracuseStep 5258591 = 7887887) B7887887
theorem B3505727 : Blo 2187435 3505727 := bstep (se 1 (by rfl) ⟨2629295, by rfl⟩ : syracuseStep 3505727 = 5258591) B5258591
theorem B9348605 : Blo 2187435 9348605 := bstep (se 3 (by rfl) ⟨1752863, by rfl⟩ : syracuseStep 9348605 = 3505727) B3505727
theorem B6232403 : Blo 2187435 6232403 := bstep (se 1 (by rfl) ⟨4674302, by rfl⟩ : syracuseStep 6232403 = 9348605) B9348605
theorem B16619741 : Blo 2187435 16619741 := bstep (se 3 (by rfl) ⟨3116201, by rfl⟩ : syracuseStep 16619741 = 6232403) B6232403
theorem B11079827 : Blo 2187435 11079827 := bstep (se 1 (by rfl) ⟨8309870, by rfl⟩ : syracuseStep 11079827 = 16619741) B16619741
theorem B7386551 : Blo 2187435 7386551 := bstep (se 1 (by rfl) ⟨5539913, by rfl⟩ : syracuseStep 7386551 = 11079827) B11079827
theorem B4924367 : Blo 2187435 4924367 := bstep (se 1 (by rfl) ⟨3693275, by rfl⟩ : syracuseStep 4924367 = 7386551) B7386551
theorem B3282911 : Blo 2187435 3282911 := bstep (se 1 (by rfl) ⟨2462183, by rfl⟩ : syracuseStep 3282911 = 4924367) B4924367
theorem B2188607 : Blo 2187435 2188607 := bstep (se 1 (by rfl) ⟨1641455, by rfl⟩ : syracuseStep 2188607 = 3282911) B3282911
theorem B3282917 : Blo 2187435 3282917 := bbase (se 4 (by rfl) ⟨307773, by rfl⟩ : syracuseStep 3282917 = 615547) (by norm_num)
theorem B2188611 : Blo 2187435 2188611 := bstep (se 1 (by rfl) ⟨1641458, by rfl⟩ : syracuseStep 2188611 = 3282917) B3282917
theorem B2218477 : Blo 2187435 2218477 := bbase (se 3 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 2218477 = 831929) (by norm_num)
theorem B2957969 : Blo 2187435 2957969 := bstep (se 2 (by rfl) ⟨1109238, by rfl⟩ : syracuseStep 2957969 = 2218477) B2218477
theorem B7887917 : Blo 2187435 7887917 := bstep (se 3 (by rfl) ⟨1478984, by rfl⟩ : syracuseStep 7887917 = 2957969) B2957969
theorem B5258611 : Blo 2187435 5258611 := bstep (se 1 (by rfl) ⟨3943958, by rfl⟩ : syracuseStep 5258611 = 7887917) B7887917
theorem B7011481 : Blo 2187435 7011481 := bstep (se 2 (by rfl) ⟨2629305, by rfl⟩ : syracuseStep 7011481 = 5258611) B5258611
theorem B9348641 : Blo 2187435 9348641 := bstep (se 2 (by rfl) ⟨3505740, by rfl⟩ : syracuseStep 9348641 = 7011481) B7011481
theorem B6232427 : Blo 2187435 6232427 := bstep (se 1 (by rfl) ⟨4674320, by rfl⟩ : syracuseStep 6232427 = 9348641) B9348641
theorem B4154951 : Blo 2187435 4154951 := bstep (se 1 (by rfl) ⟨3116213, by rfl⟩ : syracuseStep 4154951 = 6232427) B6232427
theorem B2769967 : Blo 2187435 2769967 := bstep (se 1 (by rfl) ⟨2077475, by rfl⟩ : syracuseStep 2769967 = 4154951) B4154951
theorem B3693289 : Blo 2187435 3693289 := bstep (se 2 (by rfl) ⟨1384983, by rfl⟩ : syracuseStep 3693289 = 2769967) B2769967
theorem B4924385 : Blo 2187435 4924385 := bstep (se 2 (by rfl) ⟨1846644, by rfl⟩ : syracuseStep 4924385 = 3693289) B3693289
theorem B3282923 : Blo 2187435 3282923 := bstep (se 1 (by rfl) ⟨2462192, by rfl⟩ : syracuseStep 3282923 = 4924385) B4924385
theorem B2188615 : Blo 2187435 2188615 := bstep (se 1 (by rfl) ⟨1641461, by rfl⟩ : syracuseStep 2188615 = 3282923) B3282923
theorem B2462197 : Blo 2187435 2462197 := bbase (se 5 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 2462197 = 230831) (by norm_num)
theorem B3282929 : Blo 2187435 3282929 := bstep (se 2 (by rfl) ⟨1231098, by rfl⟩ : syracuseStep 3282929 = 2462197) B2462197
theorem B2188619 : Blo 2187435 2188619 := bstep (se 1 (by rfl) ⟨1641464, by rfl⟩ : syracuseStep 2188619 = 3282929) B3282929
theorem B2769977 : Blo 2187435 2769977 := bbase (se 2 (by rfl) ⟨1038741, by rfl⟩ : syracuseStep 2769977 = 2077483) (by norm_num)
theorem B7386605 : Blo 2187435 7386605 := bstep (se 3 (by rfl) ⟨1384988, by rfl⟩ : syracuseStep 7386605 = 2769977) B2769977
theorem B4924403 : Blo 2187435 4924403 := bstep (se 1 (by rfl) ⟨3693302, by rfl⟩ : syracuseStep 4924403 = 7386605) B7386605
theorem B3282935 : Blo 2187435 3282935 := bstep (se 1 (by rfl) ⟨2462201, by rfl⟩ : syracuseStep 3282935 = 4924403) B4924403
theorem B2188623 : Blo 2187435 2188623 := bstep (se 1 (by rfl) ⟨1641467, by rfl⟩ : syracuseStep 2188623 = 3282935) B3282935
theorem B3282941 : Blo 2187435 3282941 := bbase (se 3 (by rfl) ⟨615551, by rfl⟩ : syracuseStep 3282941 = 1231103) (by norm_num)
theorem B2188627 : Blo 2187435 2188627 := bstep (se 1 (by rfl) ⟨1641470, by rfl⟩ : syracuseStep 2188627 = 3282941) B3282941
theorem B4924421 : Blo 2187435 4924421 := bbase (se 4 (by rfl) ⟨461664, by rfl⟩ : syracuseStep 4924421 = 923329) (by norm_num)
theorem B3282947 : Blo 2187435 3282947 := bstep (se 1 (by rfl) ⟨2462210, by rfl⟩ : syracuseStep 3282947 = 4924421) B4924421
theorem B2188631 : Blo 2187435 2188631 := bstep (se 1 (by rfl) ⟨1641473, by rfl⟩ : syracuseStep 2188631 = 3282947) B3282947
theorem B4154989 : Blo 2187435 4154989 := bbase (se 3 (by rfl) ⟨779060, by rfl⟩ : syracuseStep 4154989 = 1558121) (by norm_num)
theorem B5539985 : Blo 2187435 5539985 := bstep (se 2 (by rfl) ⟨2077494, by rfl⟩ : syracuseStep 5539985 = 4154989) B4154989
theorem B3693323 : Blo 2187435 3693323 := bstep (se 1 (by rfl) ⟨2769992, by rfl⟩ : syracuseStep 3693323 = 5539985) B5539985
theorem B2462215 : Blo 2187435 2462215 := bstep (se 1 (by rfl) ⟨1846661, by rfl⟩ : syracuseStep 2462215 = 3693323) B3693323
theorem B3282953 : Blo 2187435 3282953 := bstep (se 2 (by rfl) ⟨1231107, by rfl⟩ : syracuseStep 3282953 = 2462215) B2462215
theorem B2188635 : Blo 2187435 2188635 := bstep (se 1 (by rfl) ⟨1641476, by rfl⟩ : syracuseStep 2188635 = 3282953) B3282953
theorem B11079989 : Blo 2187435 11079989 := bbase (se 5 (by rfl) ⟨519374, by rfl⟩ : syracuseStep 11079989 = 1038749) (by norm_num)
theorem B7386659 : Blo 2187435 7386659 := bstep (se 1 (by rfl) ⟨5539994, by rfl⟩ : syracuseStep 7386659 = 11079989) B11079989
theorem B4924439 : Blo 2187435 4924439 := bstep (se 1 (by rfl) ⟨3693329, by rfl⟩ : syracuseStep 4924439 = 7386659) B7386659
theorem B3282959 : Blo 2187435 3282959 := bstep (se 1 (by rfl) ⟨2462219, by rfl⟩ : syracuseStep 3282959 = 4924439) B4924439
theorem B2188639 : Blo 2187435 2188639 := bstep (se 1 (by rfl) ⟨1641479, by rfl⟩ : syracuseStep 2188639 = 3282959) B3282959
theorem B3282965 : Blo 2187435 3282965 := bbase (se 6 (by rfl) ⟨76944, by rfl⟩ : syracuseStep 3282965 = 153889) (by norm_num)
theorem B2188643 : Blo 2187435 2188643 := bstep (se 1 (by rfl) ⟨1641482, by rfl⟩ : syracuseStep 2188643 = 3282965) B3282965
theorem B2665217 : Blo 2187435 2665217 := bbase (se 2 (by rfl) ⟨999456, by rfl⟩ : syracuseStep 2665217 = 1998913) (by norm_num)
theorem B7107245 : Blo 2187435 7107245 := bstep (se 3 (by rfl) ⟨1332608, by rfl⟩ : syracuseStep 7107245 = 2665217) B2665217
theorem B75810613 : Blo 2187435 75810613 := bstep (se 5 (by rfl) ⟨3553622, by rfl⟩ : syracuseStep 75810613 = 7107245) B7107245
theorem B101080817 : Blo 2187435 101080817 := bstep (se 2 (by rfl) ⟨37905306, by rfl⟩ : syracuseStep 101080817 = 75810613) B75810613
theorem B67387211 : Blo 2187435 67387211 := bstep (se 1 (by rfl) ⟨50540408, by rfl⟩ : syracuseStep 67387211 = 101080817) B101080817
theorem B44924807 : Blo 2187435 44924807 := bstep (se 1 (by rfl) ⟨33693605, by rfl⟩ : syracuseStep 44924807 = 67387211) B67387211
theorem B29949871 : Blo 2187435 29949871 := bstep (se 1 (by rfl) ⟨22462403, by rfl⟩ : syracuseStep 29949871 = 44924807) B44924807
theorem B39933161 : Blo 2187435 39933161 := bstep (se 2 (by rfl) ⟨14974935, by rfl⟩ : syracuseStep 39933161 = 29949871) B29949871
theorem B26622107 : Blo 2187435 26622107 := bstep (se 1 (by rfl) ⟨19966580, by rfl⟩ : syracuseStep 26622107 = 39933161) B39933161
theorem B17748071 : Blo 2187435 17748071 := bstep (se 1 (by rfl) ⟨13311053, by rfl⟩ : syracuseStep 17748071 = 26622107) B26622107
theorem B11832047 : Blo 2187435 11832047 := bstep (se 1 (by rfl) ⟨8874035, by rfl⟩ : syracuseStep 11832047 = 17748071) B17748071
theorem B7888031 : Blo 2187435 7888031 := bstep (se 1 (by rfl) ⟨5916023, by rfl⟩ : syracuseStep 7888031 = 11832047) B11832047
theorem B5258687 : Blo 2187435 5258687 := bstep (se 1 (by rfl) ⟨3944015, by rfl⟩ : syracuseStep 5258687 = 7888031) B7888031
theorem B14023165 : Blo 2187435 14023165 := bstep (se 3 (by rfl) ⟨2629343, by rfl⟩ : syracuseStep 14023165 = 5258687) B5258687
theorem B18697553 : Blo 2187435 18697553 := bstep (se 2 (by rfl) ⟨7011582, by rfl⟩ : syracuseStep 18697553 = 14023165) B14023165
theorem B12465035 : Blo 2187435 12465035 := bstep (se 1 (by rfl) ⟨9348776, by rfl⟩ : syracuseStep 12465035 = 18697553) B18697553
theorem B8310023 : Blo 2187435 8310023 := bstep (se 1 (by rfl) ⟨6232517, by rfl⟩ : syracuseStep 8310023 = 12465035) B12465035
theorem B5540015 : Blo 2187435 5540015 := bstep (se 1 (by rfl) ⟨4155011, by rfl⟩ : syracuseStep 5540015 = 8310023) B8310023
theorem B3693343 : Blo 2187435 3693343 := bstep (se 1 (by rfl) ⟨2770007, by rfl⟩ : syracuseStep 3693343 = 5540015) B5540015
theorem B4924457 : Blo 2187435 4924457 := bstep (se 2 (by rfl) ⟨1846671, by rfl⟩ : syracuseStep 4924457 = 3693343) B3693343
theorem B3282971 : Blo 2187435 3282971 := bstep (se 1 (by rfl) ⟨2462228, by rfl⟩ : syracuseStep 3282971 = 4924457) B4924457
theorem B2188647 : Blo 2187435 2188647 := bstep (se 1 (by rfl) ⟨1641485, by rfl⟩ : syracuseStep 2188647 = 3282971) B3282971
theorem B2462233 : Blo 2187435 2462233 := bbase (se 2 (by rfl) ⟨923337, by rfl⟩ : syracuseStep 2462233 = 1846675) (by norm_num)
theorem B3282977 : Blo 2187435 3282977 := bstep (se 2 (by rfl) ⟨1231116, by rfl⟩ : syracuseStep 3282977 = 2462233) B2462233
theorem B2188651 : Blo 2187435 2188651 := bstep (se 1 (by rfl) ⟨1641488, by rfl⟩ : syracuseStep 2188651 = 3282977) B3282977
theorem B8310053 : Blo 2187435 8310053 := bbase (se 4 (by rfl) ⟨779067, by rfl⟩ : syracuseStep 8310053 = 1558135) (by norm_num)
theorem B5540035 : Blo 2187435 5540035 := bstep (se 1 (by rfl) ⟨4155026, by rfl⟩ : syracuseStep 5540035 = 8310053) B8310053
theorem B7386713 : Blo 2187435 7386713 := bstep (se 2 (by rfl) ⟨2770017, by rfl⟩ : syracuseStep 7386713 = 5540035) B5540035
theorem B4924475 : Blo 2187435 4924475 := bstep (se 1 (by rfl) ⟨3693356, by rfl⟩ : syracuseStep 4924475 = 7386713) B7386713
theorem B3282983 : Blo 2187435 3282983 := bstep (se 1 (by rfl) ⟨2462237, by rfl⟩ : syracuseStep 3282983 = 4924475) B4924475
theorem B2188655 : Blo 2187435 2188655 := bstep (se 1 (by rfl) ⟨1641491, by rfl⟩ : syracuseStep 2188655 = 3282983) B3282983
theorem B3282989 : Blo 2187435 3282989 := bbase (se 3 (by rfl) ⟨615560, by rfl⟩ : syracuseStep 3282989 = 1231121) (by norm_num)
theorem B2188659 : Blo 2187435 2188659 := bstep (se 1 (by rfl) ⟨1641494, by rfl⟩ : syracuseStep 2188659 = 3282989) B3282989
theorem B4924493 : Blo 2187435 4924493 := bbase (se 3 (by rfl) ⟨923342, by rfl⟩ : syracuseStep 4924493 = 1846685) (by norm_num)
theorem B3282995 : Blo 2187435 3282995 := bstep (se 1 (by rfl) ⟨2462246, by rfl⟩ : syracuseStep 3282995 = 4924493) B4924493
theorem B2188663 : Blo 2187435 2188663 := bstep (se 1 (by rfl) ⟨1641497, by rfl⟩ : syracuseStep 2188663 = 3282995) B3282995
theorem B2770033 : Blo 2187435 2770033 := bbase (se 2 (by rfl) ⟨1038762, by rfl⟩ : syracuseStep 2770033 = 2077525) (by norm_num)
theorem B3693377 : Blo 2187435 3693377 := bstep (se 2 (by rfl) ⟨1385016, by rfl⟩ : syracuseStep 3693377 = 2770033) B2770033
theorem B2462251 : Blo 2187435 2462251 := bstep (se 1 (by rfl) ⟨1846688, by rfl⟩ : syracuseStep 2462251 = 3693377) B3693377
theorem B3283001 : Blo 2187435 3283001 := bstep (se 2 (by rfl) ⟨1231125, by rfl⟩ : syracuseStep 3283001 = 2462251) B2462251
theorem B2188667 : Blo 2187435 2188667 := bstep (se 1 (by rfl) ⟨1641500, by rfl⟩ : syracuseStep 2188667 = 3283001) B3283001
theorem B7888117 : Blo 2187435 7888117 := bbase (se 5 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 7888117 = 739511) (by norm_num)
theorem B10517489 : Blo 2187435 10517489 := bstep (se 2 (by rfl) ⟨3944058, by rfl⟩ : syracuseStep 10517489 = 7888117) B7888117
theorem B7011659 : Blo 2187435 7011659 := bstep (se 1 (by rfl) ⟨5258744, by rfl⟩ : syracuseStep 7011659 = 10517489) B10517489
theorem B4674439 : Blo 2187435 4674439 := bstep (se 1 (by rfl) ⟨3505829, by rfl⟩ : syracuseStep 4674439 = 7011659) B7011659
theorem B24930341 : Blo 2187435 24930341 := bstep (se 4 (by rfl) ⟨2337219, by rfl⟩ : syracuseStep 24930341 = 4674439) B4674439
theorem B16620227 : Blo 2187435 16620227 := bstep (se 1 (by rfl) ⟨12465170, by rfl⟩ : syracuseStep 16620227 = 24930341) B24930341
theorem B11080151 : Blo 2187435 11080151 := bstep (se 1 (by rfl) ⟨8310113, by rfl⟩ : syracuseStep 11080151 = 16620227) B16620227
theorem B7386767 : Blo 2187435 7386767 := bstep (se 1 (by rfl) ⟨5540075, by rfl⟩ : syracuseStep 7386767 = 11080151) B11080151
theorem B4924511 : Blo 2187435 4924511 := bstep (se 1 (by rfl) ⟨3693383, by rfl⟩ : syracuseStep 4924511 = 7386767) B7386767
theorem B3283007 : Blo 2187435 3283007 := bstep (se 1 (by rfl) ⟨2462255, by rfl⟩ : syracuseStep 3283007 = 4924511) B4924511
theorem B2188671 : Blo 2187435 2188671 := bstep (se 1 (by rfl) ⟨1641503, by rfl⟩ : syracuseStep 2188671 = 3283007) B3283007
theorem B3283013 : Blo 2187435 3283013 := bbase (se 4 (by rfl) ⟨307782, by rfl⟩ : syracuseStep 3283013 = 615565) (by norm_num)
theorem B2188675 : Blo 2187435 2188675 := bstep (se 1 (by rfl) ⟨1641506, by rfl⟩ : syracuseStep 2188675 = 3283013) B3283013
theorem B3693397 : Blo 2187435 3693397 := bbase (se 9 (by rfl) ⟨10820, by rfl⟩ : syracuseStep 3693397 = 21641) (by norm_num)
theorem B4924529 : Blo 2187435 4924529 := bstep (se 2 (by rfl) ⟨1846698, by rfl⟩ : syracuseStep 4924529 = 3693397) B3693397
theorem B3283019 : Blo 2187435 3283019 := bstep (se 1 (by rfl) ⟨2462264, by rfl⟩ : syracuseStep 3283019 = 4924529) B4924529
theorem B2188679 : Blo 2187435 2188679 := bstep (se 1 (by rfl) ⟨1641509, by rfl⟩ : syracuseStep 2188679 = 3283019) B3283019
theorem B2462269 : Blo 2187435 2462269 := bbase (se 3 (by rfl) ⟨461675, by rfl⟩ : syracuseStep 2462269 = 923351) (by norm_num)
theorem B3283025 : Blo 2187435 3283025 := bstep (se 2 (by rfl) ⟨1231134, by rfl⟩ : syracuseStep 3283025 = 2462269) B2462269
theorem B2188683 : Blo 2187435 2188683 := bstep (se 1 (by rfl) ⟨1641512, by rfl⟩ : syracuseStep 2188683 = 3283025) B3283025
theorem B7386821 : Blo 2187435 7386821 := bbase (se 4 (by rfl) ⟨692514, by rfl⟩ : syracuseStep 7386821 = 1385029) (by norm_num)
theorem B4924547 : Blo 2187435 4924547 := bstep (se 1 (by rfl) ⟨3693410, by rfl⟩ : syracuseStep 4924547 = 7386821) B7386821
theorem B3283031 : Blo 2187435 3283031 := bstep (se 1 (by rfl) ⟨2462273, by rfl⟩ : syracuseStep 3283031 = 4924547) B4924547
theorem B2188687 : Blo 2187435 2188687 := bstep (se 1 (by rfl) ⟨1641515, by rfl⟩ : syracuseStep 2188687 = 3283031) B3283031
theorem B3283037 : Blo 2187435 3283037 := bbase (se 3 (by rfl) ⟨615569, by rfl⟩ : syracuseStep 3283037 = 1231139) (by norm_num)
theorem B2188691 : Blo 2187435 2188691 := bstep (se 1 (by rfl) ⟨1641518, by rfl⟩ : syracuseStep 2188691 = 3283037) B3283037
theorem B4924565 : Blo 2187435 4924565 := bbase (se 6 (by rfl) ⟨115419, by rfl⟩ : syracuseStep 4924565 = 230839) (by norm_num)
theorem B3283043 : Blo 2187435 3283043 := bstep (se 1 (by rfl) ⟨2462282, by rfl⟩ : syracuseStep 3283043 = 4924565) B4924565
theorem B2188695 : Blo 2187435 2188695 := bstep (se 1 (by rfl) ⟨1641521, by rfl⟩ : syracuseStep 2188695 = 3283043) B3283043
theorem B3116333 : Blo 2187435 3116333 := bbase (se 3 (by rfl) ⟨584312, by rfl⟩ : syracuseStep 3116333 = 1168625) (by norm_num)
theorem B8310221 : Blo 2187435 8310221 := bstep (se 3 (by rfl) ⟨1558166, by rfl⟩ : syracuseStep 8310221 = 3116333) B3116333
theorem B5540147 : Blo 2187435 5540147 := bstep (se 1 (by rfl) ⟨4155110, by rfl⟩ : syracuseStep 5540147 = 8310221) B8310221
theorem B3693431 : Blo 2187435 3693431 := bstep (se 1 (by rfl) ⟨2770073, by rfl⟩ : syracuseStep 3693431 = 5540147) B5540147
theorem B2462287 : Blo 2187435 2462287 := bstep (se 1 (by rfl) ⟨1846715, by rfl⟩ : syracuseStep 2462287 = 3693431) B3693431
theorem B3283049 : Blo 2187435 3283049 := bstep (se 2 (by rfl) ⟨1231143, by rfl⟩ : syracuseStep 3283049 = 2462287) B2462287
theorem B2188699 : Blo 2187435 2188699 := bstep (se 1 (by rfl) ⟨1641524, by rfl⟩ : syracuseStep 2188699 = 3283049) B3283049
theorem B21035285 : Blo 2187435 21035285 := bbase (se 6 (by rfl) ⟨493014, by rfl⟩ : syracuseStep 21035285 = 986029) (by norm_num)
theorem B14023523 : Blo 2187435 14023523 := bstep (se 1 (by rfl) ⟨10517642, by rfl⟩ : syracuseStep 14023523 = 21035285) B21035285
theorem B9349015 : Blo 2187435 9349015 := bstep (se 1 (by rfl) ⟨7011761, by rfl⟩ : syracuseStep 9349015 = 14023523) B14023523
theorem B12465353 : Blo 2187435 12465353 := bstep (se 2 (by rfl) ⟨4674507, by rfl⟩ : syracuseStep 12465353 = 9349015) B9349015
theorem B8310235 : Blo 2187435 8310235 := bstep (se 1 (by rfl) ⟨6232676, by rfl⟩ : syracuseStep 8310235 = 12465353) B12465353
theorem B11080313 : Blo 2187435 11080313 := bstep (se 2 (by rfl) ⟨4155117, by rfl⟩ : syracuseStep 11080313 = 8310235) B8310235
theorem B7386875 : Blo 2187435 7386875 := bstep (se 1 (by rfl) ⟨5540156, by rfl⟩ : syracuseStep 7386875 = 11080313) B11080313
theorem B4924583 : Blo 2187435 4924583 := bstep (se 1 (by rfl) ⟨3693437, by rfl⟩ : syracuseStep 4924583 = 7386875) B7386875
theorem B3283055 : Blo 2187435 3283055 := bstep (se 1 (by rfl) ⟨2462291, by rfl⟩ : syracuseStep 3283055 = 4924583) B4924583
theorem B2188703 : Blo 2187435 2188703 := bstep (se 1 (by rfl) ⟨1641527, by rfl⟩ : syracuseStep 2188703 = 3283055) B3283055
theorem B3283061 : Blo 2187435 3283061 := bbase (se 5 (by rfl) ⟨153893, by rfl⟩ : syracuseStep 3283061 = 307787) (by norm_num)
theorem B2188707 : Blo 2187435 2188707 := bstep (se 1 (by rfl) ⟨1641530, by rfl⟩ : syracuseStep 2188707 = 3283061) B3283061
theorem B4155133 : Blo 2187435 4155133 := bbase (se 3 (by rfl) ⟨779087, by rfl⟩ : syracuseStep 4155133 = 1558175) (by norm_num)
theorem B5540177 : Blo 2187435 5540177 := bstep (se 2 (by rfl) ⟨2077566, by rfl⟩ : syracuseStep 5540177 = 4155133) B4155133
theorem B3693451 : Blo 2187435 3693451 := bstep (se 1 (by rfl) ⟨2770088, by rfl⟩ : syracuseStep 3693451 = 5540177) B5540177
theorem B4924601 : Blo 2187435 4924601 := bstep (se 2 (by rfl) ⟨1846725, by rfl⟩ : syracuseStep 4924601 = 3693451) B3693451
theorem B3283067 : Blo 2187435 3283067 := bstep (se 1 (by rfl) ⟨2462300, by rfl⟩ : syracuseStep 3283067 = 4924601) B4924601
theorem B2188711 : Blo 2187435 2188711 := bstep (se 1 (by rfl) ⟨1641533, by rfl⟩ : syracuseStep 2188711 = 3283067) B3283067
theorem B2462305 : Blo 2187435 2462305 := bbase (se 2 (by rfl) ⟨923364, by rfl⟩ : syracuseStep 2462305 = 1846729) (by norm_num)
theorem B3283073 : Blo 2187435 3283073 := bstep (se 2 (by rfl) ⟨1231152, by rfl⟩ : syracuseStep 3283073 = 2462305) B2462305
theorem B2188715 : Blo 2187435 2188715 := bstep (se 1 (by rfl) ⟨1641536, by rfl⟩ : syracuseStep 2188715 = 3283073) B3283073
theorem B5540197 : Blo 2187435 5540197 := bbase (se 4 (by rfl) ⟨519393, by rfl⟩ : syracuseStep 5540197 = 1038787) (by norm_num)
theorem B7386929 : Blo 2187435 7386929 := bstep (se 2 (by rfl) ⟨2770098, by rfl⟩ : syracuseStep 7386929 = 5540197) B5540197
theorem B4924619 : Blo 2187435 4924619 := bstep (se 1 (by rfl) ⟨3693464, by rfl⟩ : syracuseStep 4924619 = 7386929) B7386929
theorem B3283079 : Blo 2187435 3283079 := bstep (se 1 (by rfl) ⟨2462309, by rfl⟩ : syracuseStep 3283079 = 4924619) B4924619
theorem B2188719 : Blo 2187435 2188719 := bstep (se 1 (by rfl) ⟨1641539, by rfl⟩ : syracuseStep 2188719 = 3283079) B3283079
theorem B3283085 : Blo 2187435 3283085 := bbase (se 3 (by rfl) ⟨615578, by rfl⟩ : syracuseStep 3283085 = 1231157) (by norm_num)
theorem B2188723 : Blo 2187435 2188723 := bstep (se 1 (by rfl) ⟨1641542, by rfl⟩ : syracuseStep 2188723 = 3283085) B3283085
theorem B4924637 : Blo 2187435 4924637 := bbase (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) (by norm_num)
theorem B3283091 : Blo 2187435 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B2188727 : Blo 2187435 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B3693485 : Blo 2187435 3693485 := bbase (se 3 (by rfl) ⟨692528, by rfl⟩ : syracuseStep 3693485 = 1385057) (by norm_num)
theorem B2462323 : Blo 2187435 2462323 := bstep (se 1 (by rfl) ⟨1846742, by rfl⟩ : syracuseStep 2462323 = 3693485) B3693485
theorem B3283097 : Blo 2187435 3283097 := bstep (se 2 (by rfl) ⟨1231161, by rfl⟩ : syracuseStep 3283097 = 2462323) B2462323
theorem B2188731 : Blo 2187435 2188731 := bstep (se 1 (by rfl) ⟨1641548, by rfl⟩ : syracuseStep 2188731 = 3283097) B3283097
theorem B16847477 : Blo 2187435 16847477 := bbase (se 5 (by rfl) ⟨789725, by rfl⟩ : syracuseStep 16847477 = 1579451) (by norm_num)
theorem B11231651 : Blo 2187435 11231651 := bstep (se 1 (by rfl) ⟨8423738, by rfl⟩ : syracuseStep 11231651 = 16847477) B16847477
theorem B7487767 : Blo 2187435 7487767 := bstep (se 1 (by rfl) ⟨5615825, by rfl⟩ : syracuseStep 7487767 = 11231651) B11231651
theorem B39934757 : Blo 2187435 39934757 := bstep (se 4 (by rfl) ⟨3743883, by rfl⟩ : syracuseStep 39934757 = 7487767) B7487767
theorem B26623171 : Blo 2187435 26623171 := bstep (se 1 (by rfl) ⟨19967378, by rfl⟩ : syracuseStep 26623171 = 39934757) B39934757
theorem B141990245 : Blo 2187435 141990245 := bstep (se 4 (by rfl) ⟨13311585, by rfl⟩ : syracuseStep 141990245 = 26623171) B26623171
theorem B94660163 : Blo 2187435 94660163 := bstep (se 1 (by rfl) ⟨70995122, by rfl⟩ : syracuseStep 94660163 = 141990245) B141990245
theorem B63106775 : Blo 2187435 63106775 := bstep (se 1 (by rfl) ⟨47330081, by rfl⟩ : syracuseStep 63106775 = 94660163) B94660163
theorem B42071183 : Blo 2187435 42071183 := bstep (se 1 (by rfl) ⟨31553387, by rfl⟩ : syracuseStep 42071183 = 63106775) B63106775
theorem B28047455 : Blo 2187435 28047455 := bstep (se 1 (by rfl) ⟨21035591, by rfl⟩ : syracuseStep 28047455 = 42071183) B42071183
theorem B18698303 : Blo 2187435 18698303 := bstep (se 1 (by rfl) ⟨14023727, by rfl⟩ : syracuseStep 18698303 = 28047455) B28047455
theorem B12465535 : Blo 2187435 12465535 := bstep (se 1 (by rfl) ⟨9349151, by rfl⟩ : syracuseStep 12465535 = 18698303) B18698303
theorem B16620713 : Blo 2187435 16620713 := bstep (se 2 (by rfl) ⟨6232767, by rfl⟩ : syracuseStep 16620713 = 12465535) B12465535
theorem B11080475 : Blo 2187435 11080475 := bstep (se 1 (by rfl) ⟨8310356, by rfl⟩ : syracuseStep 11080475 = 16620713) B16620713
theorem B7386983 : Blo 2187435 7386983 := bstep (se 1 (by rfl) ⟨5540237, by rfl⟩ : syracuseStep 7386983 = 11080475) B11080475
theorem B4924655 : Blo 2187435 4924655 := bstep (se 1 (by rfl) ⟨3693491, by rfl⟩ : syracuseStep 4924655 = 7386983) B7386983
theorem B3283103 : Blo 2187435 3283103 := bstep (se 1 (by rfl) ⟨2462327, by rfl⟩ : syracuseStep 3283103 = 4924655) B4924655
theorem B2188735 : Blo 2187435 2188735 := bstep (se 1 (by rfl) ⟨1641551, by rfl⟩ : syracuseStep 2188735 = 3283103) B3283103
theorem B3283109 : Blo 2187435 3283109 := bbase (se 4 (by rfl) ⟨307791, by rfl⟩ : syracuseStep 3283109 = 615583) (by norm_num)
theorem B2188739 : Blo 2187435 2188739 := bstep (se 1 (by rfl) ⟨1641554, by rfl⟩ : syracuseStep 2188739 = 3283109) B3283109
theorem B2770129 : Blo 2187435 2770129 := bbase (se 2 (by rfl) ⟨1038798, by rfl⟩ : syracuseStep 2770129 = 2077597) (by norm_num)
theorem B3693505 : Blo 2187435 3693505 := bstep (se 2 (by rfl) ⟨1385064, by rfl⟩ : syracuseStep 3693505 = 2770129) B2770129
theorem B4924673 : Blo 2187435 4924673 := bstep (se 2 (by rfl) ⟨1846752, by rfl⟩ : syracuseStep 4924673 = 3693505) B3693505
theorem B3283115 : Blo 2187435 3283115 := bstep (se 1 (by rfl) ⟨2462336, by rfl⟩ : syracuseStep 3283115 = 4924673) B4924673
theorem B2188743 : Blo 2187435 2188743 := bstep (se 1 (by rfl) ⟨1641557, by rfl⟩ : syracuseStep 2188743 = 3283115) B3283115
theorem B2462341 : Blo 2187435 2462341 := bbase (se 4 (by rfl) ⟨230844, by rfl⟩ : syracuseStep 2462341 = 461689) (by norm_num)
theorem B3283121 : Blo 2187435 3283121 := bstep (se 2 (by rfl) ⟨1231170, by rfl⟩ : syracuseStep 3283121 = 2462341) B2462341
theorem B2188747 : Blo 2187435 2188747 := bstep (se 1 (by rfl) ⟨1641560, by rfl⟩ : syracuseStep 2188747 = 3283121) B3283121
theorem B2629469 : Blo 2187435 2629469 := bbase (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) (by norm_num)
theorem B7011917 : Blo 2187435 7011917 := bstep (se 3 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 7011917 = 2629469) B2629469
theorem B4674611 : Blo 2187435 4674611 := bstep (se 1 (by rfl) ⟨3505958, by rfl⟩ : syracuseStep 4674611 = 7011917) B7011917
theorem B3116407 : Blo 2187435 3116407 := bstep (se 1 (by rfl) ⟨2337305, by rfl⟩ : syracuseStep 3116407 = 4674611) B4674611
theorem B4155209 : Blo 2187435 4155209 := bstep (se 2 (by rfl) ⟨1558203, by rfl⟩ : syracuseStep 4155209 = 3116407) B3116407
theorem B2770139 : Blo 2187435 2770139 := bstep (se 1 (by rfl) ⟨2077604, by rfl⟩ : syracuseStep 2770139 = 4155209) B4155209
theorem B7387037 : Blo 2187435 7387037 := bstep (se 3 (by rfl) ⟨1385069, by rfl⟩ : syracuseStep 7387037 = 2770139) B2770139
theorem B4924691 : Blo 2187435 4924691 := bstep (se 1 (by rfl) ⟨3693518, by rfl⟩ : syracuseStep 4924691 = 7387037) B7387037
theorem B3283127 : Blo 2187435 3283127 := bstep (se 1 (by rfl) ⟨2462345, by rfl⟩ : syracuseStep 3283127 = 4924691) B4924691
theorem B2188751 : Blo 2187435 2188751 := bstep (se 1 (by rfl) ⟨1641563, by rfl⟩ : syracuseStep 2188751 = 3283127) B3283127
theorem B3283133 : Blo 2187435 3283133 := bbase (se 3 (by rfl) ⟨615587, by rfl⟩ : syracuseStep 3283133 = 1231175) (by norm_num)
theorem B2188755 : Blo 2187435 2188755 := bstep (se 1 (by rfl) ⟨1641566, by rfl⟩ : syracuseStep 2188755 = 3283133) B3283133
theorem B4924709 : Blo 2187435 4924709 := bbase (se 4 (by rfl) ⟨461691, by rfl⟩ : syracuseStep 4924709 = 923383) (by norm_num)
theorem B3283139 : Blo 2187435 3283139 := bstep (se 1 (by rfl) ⟨2462354, by rfl⟩ : syracuseStep 3283139 = 4924709) B4924709
theorem B2188759 : Blo 2187435 2188759 := bstep (se 1 (by rfl) ⟨1641569, by rfl⟩ : syracuseStep 2188759 = 3283139) B3283139
theorem B5540309 : Blo 2187435 5540309 := bbase (se 7 (by rfl) ⟨64925, by rfl⟩ : syracuseStep 5540309 = 129851) (by norm_num)
theorem B3693539 : Blo 2187435 3693539 := bstep (se 1 (by rfl) ⟨2770154, by rfl⟩ : syracuseStep 3693539 = 5540309) B5540309
theorem B2462359 : Blo 2187435 2462359 := bstep (se 1 (by rfl) ⟨1846769, by rfl⟩ : syracuseStep 2462359 = 3693539) B3693539
theorem B3283145 : Blo 2187435 3283145 := bstep (se 2 (by rfl) ⟨1231179, by rfl⟩ : syracuseStep 3283145 = 2462359) B2462359
theorem B2188763 : Blo 2187435 2188763 := bstep (se 1 (by rfl) ⟨1641572, by rfl⟩ : syracuseStep 2188763 = 3283145) B3283145
theorem B11994133 : Blo 2187435 11994133 := bbase (se 6 (by rfl) ⟨281112, by rfl⟩ : syracuseStep 11994133 = 562225) (by norm_num)
theorem B15992177 : Blo 2187435 15992177 := bstep (se 2 (by rfl) ⟨5997066, by rfl⟩ : syracuseStep 15992177 = 11994133) B11994133
theorem B170583221 : Blo 2187435 170583221 := bstep (se 5 (by rfl) ⟨7996088, by rfl⟩ : syracuseStep 170583221 = 15992177) B15992177
theorem B113722147 : Blo 2187435 113722147 := bstep (se 1 (by rfl) ⟨85291610, by rfl⟩ : syracuseStep 113722147 = 170583221) B170583221
theorem B151629529 : Blo 2187435 151629529 := bstep (se 2 (by rfl) ⟨56861073, by rfl⟩ : syracuseStep 151629529 = 113722147) B113722147
theorem B202172705 : Blo 2187435 202172705 := bstep (se 2 (by rfl) ⟨75814764, by rfl⟩ : syracuseStep 202172705 = 151629529) B151629529
theorem B134781803 : Blo 2187435 134781803 := bstep (se 1 (by rfl) ⟨101086352, by rfl⟩ : syracuseStep 134781803 = 202172705) B202172705
theorem B89854535 : Blo 2187435 89854535 := bstep (se 1 (by rfl) ⟨67390901, by rfl⟩ : syracuseStep 89854535 = 134781803) B134781803
theorem B59903023 : Blo 2187435 59903023 := bstep (se 1 (by rfl) ⟨44927267, by rfl⟩ : syracuseStep 59903023 = 89854535) B89854535
theorem B79870697 : Blo 2187435 79870697 := bstep (se 2 (by rfl) ⟨29951511, by rfl⟩ : syracuseStep 79870697 = 59903023) B59903023
theorem B53247131 : Blo 2187435 53247131 := bstep (se 1 (by rfl) ⟨39935348, by rfl⟩ : syracuseStep 53247131 = 79870697) B79870697
theorem B35498087 : Blo 2187435 35498087 := bstep (se 1 (by rfl) ⟨26623565, by rfl⟩ : syracuseStep 35498087 = 53247131) B53247131
theorem B23665391 : Blo 2187435 23665391 := bstep (se 1 (by rfl) ⟨17749043, by rfl⟩ : syracuseStep 23665391 = 35498087) B35498087
theorem B15776927 : Blo 2187435 15776927 := bstep (se 1 (by rfl) ⟨11832695, by rfl⟩ : syracuseStep 15776927 = 23665391) B23665391
theorem B10517951 : Blo 2187435 10517951 := bstep (se 1 (by rfl) ⟨7888463, by rfl⟩ : syracuseStep 10517951 = 15776927) B15776927
theorem B7011967 : Blo 2187435 7011967 := bstep (se 1 (by rfl) ⟨5258975, by rfl⟩ : syracuseStep 7011967 = 10517951) B10517951
theorem B9349289 : Blo 2187435 9349289 := bstep (se 2 (by rfl) ⟨3505983, by rfl⟩ : syracuseStep 9349289 = 7011967) B7011967
theorem B6232859 : Blo 2187435 6232859 := bstep (se 1 (by rfl) ⟨4674644, by rfl⟩ : syracuseStep 6232859 = 9349289) B9349289
theorem B4155239 : Blo 2187435 4155239 := bstep (se 1 (by rfl) ⟨3116429, by rfl⟩ : syracuseStep 4155239 = 6232859) B6232859
theorem B11080637 : Blo 2187435 11080637 := bstep (se 3 (by rfl) ⟨2077619, by rfl⟩ : syracuseStep 11080637 = 4155239) B4155239
theorem B7387091 : Blo 2187435 7387091 := bstep (se 1 (by rfl) ⟨5540318, by rfl⟩ : syracuseStep 7387091 = 11080637) B11080637
theorem B4924727 : Blo 2187435 4924727 := bstep (se 1 (by rfl) ⟨3693545, by rfl⟩ : syracuseStep 4924727 = 7387091) B7387091
theorem B3283151 : Blo 2187435 3283151 := bstep (se 1 (by rfl) ⟨2462363, by rfl⟩ : syracuseStep 3283151 = 4924727) B4924727
theorem B2188767 : Blo 2187435 2188767 := bstep (se 1 (by rfl) ⟨1641575, by rfl⟩ : syracuseStep 2188767 = 3283151) B3283151
theorem B3283157 : Blo 2187435 3283157 := bbase (se 7 (by rfl) ⟨38474, by rfl⟩ : syracuseStep 3283157 = 76949) (by norm_num)
theorem B2188771 : Blo 2187435 2188771 := bstep (se 1 (by rfl) ⟨1641578, by rfl⟩ : syracuseStep 2188771 = 3283157) B3283157
theorem B3505997 : Blo 2187435 3505997 := bbase (se 3 (by rfl) ⟨657374, by rfl⟩ : syracuseStep 3505997 = 1314749) (by norm_num)
theorem B2337331 : Blo 2187435 2337331 := bstep (se 1 (by rfl) ⟨1752998, by rfl⟩ : syracuseStep 2337331 = 3505997) B3505997
theorem B3116441 : Blo 2187435 3116441 := bstep (se 2 (by rfl) ⟨1168665, by rfl⟩ : syracuseStep 3116441 = 2337331) B2337331
theorem B8310509 : Blo 2187435 8310509 := bstep (se 3 (by rfl) ⟨1558220, by rfl⟩ : syracuseStep 8310509 = 3116441) B3116441
theorem B5540339 : Blo 2187435 5540339 := bstep (se 1 (by rfl) ⟨4155254, by rfl⟩ : syracuseStep 5540339 = 8310509) B8310509
theorem B3693559 : Blo 2187435 3693559 := bstep (se 1 (by rfl) ⟨2770169, by rfl⟩ : syracuseStep 3693559 = 5540339) B5540339
theorem B4924745 : Blo 2187435 4924745 := bstep (se 2 (by rfl) ⟨1846779, by rfl⟩ : syracuseStep 4924745 = 3693559) B3693559
theorem B3283163 : Blo 2187435 3283163 := bstep (se 1 (by rfl) ⟨2462372, by rfl⟩ : syracuseStep 3283163 = 4924745) B4924745
theorem B2188775 : Blo 2187435 2188775 := bstep (se 1 (by rfl) ⟨1641581, by rfl⟩ : syracuseStep 2188775 = 3283163) B3283163
theorem B2462377 : Blo 2187435 2462377 := bbase (se 2 (by rfl) ⟨923391, by rfl⟩ : syracuseStep 2462377 = 1846783) (by norm_num)
theorem B3283169 : Blo 2187435 3283169 := bstep (se 2 (by rfl) ⟨1231188, by rfl⟩ : syracuseStep 3283169 = 2462377) B2462377
theorem B2188779 : Blo 2187435 2188779 := bstep (se 1 (by rfl) ⟨1641584, by rfl⟩ : syracuseStep 2188779 = 3283169) B3283169
theorem B3944261 : Blo 2187435 3944261 := bbase (se 4 (by rfl) ⟨369774, by rfl⟩ : syracuseStep 3944261 = 739549) (by norm_num)
theorem B2629507 : Blo 2187435 2629507 := bstep (se 1 (by rfl) ⟨1972130, by rfl⟩ : syracuseStep 2629507 = 3944261) B3944261
theorem B3506009 : Blo 2187435 3506009 := bstep (se 2 (by rfl) ⟨1314753, by rfl⟩ : syracuseStep 3506009 = 2629507) B2629507
theorem B9349357 : Blo 2187435 9349357 := bstep (se 3 (by rfl) ⟨1753004, by rfl⟩ : syracuseStep 9349357 = 3506009) B3506009
theorem B12465809 : Blo 2187435 12465809 := bstep (se 2 (by rfl) ⟨4674678, by rfl⟩ : syracuseStep 12465809 = 9349357) B9349357
theorem B8310539 : Blo 2187435 8310539 := bstep (se 1 (by rfl) ⟨6232904, by rfl⟩ : syracuseStep 8310539 = 12465809) B12465809
theorem B5540359 : Blo 2187435 5540359 := bstep (se 1 (by rfl) ⟨4155269, by rfl⟩ : syracuseStep 5540359 = 8310539) B8310539
theorem B7387145 : Blo 2187435 7387145 := bstep (se 2 (by rfl) ⟨2770179, by rfl⟩ : syracuseStep 7387145 = 5540359) B5540359
theorem B4924763 : Blo 2187435 4924763 := bstep (se 1 (by rfl) ⟨3693572, by rfl⟩ : syracuseStep 4924763 = 7387145) B7387145
theorem B3283175 : Blo 2187435 3283175 := bstep (se 1 (by rfl) ⟨2462381, by rfl⟩ : syracuseStep 3283175 = 4924763) B4924763
theorem B2188783 : Blo 2187435 2188783 := bstep (se 1 (by rfl) ⟨1641587, by rfl⟩ : syracuseStep 2188783 = 3283175) B3283175
theorem B3283181 : Blo 2187435 3283181 := bbase (se 3 (by rfl) ⟨615596, by rfl⟩ : syracuseStep 3283181 = 1231193) (by norm_num)
theorem B2188787 : Blo 2187435 2188787 := bstep (se 1 (by rfl) ⟨1641590, by rfl⟩ : syracuseStep 2188787 = 3283181) B3283181
theorem B4924781 : Blo 2187435 4924781 := bbase (se 3 (by rfl) ⟨923396, by rfl⟩ : syracuseStep 4924781 = 1846793) (by norm_num)
theorem B3283187 : Blo 2187435 3283187 := bstep (se 1 (by rfl) ⟨2462390, by rfl⟩ : syracuseStep 3283187 = 4924781) B4924781
theorem B2188791 : Blo 2187435 2188791 := bstep (se 1 (by rfl) ⟨1641593, by rfl⟩ : syracuseStep 2188791 = 3283187) B3283187
theorem B4155293 : Blo 2187435 4155293 := bbase (se 3 (by rfl) ⟨779117, by rfl⟩ : syracuseStep 4155293 = 1558235) (by norm_num)
theorem B2770195 : Blo 2187435 2770195 := bstep (se 1 (by rfl) ⟨2077646, by rfl⟩ : syracuseStep 2770195 = 4155293) B4155293
theorem B3693593 : Blo 2187435 3693593 := bstep (se 2 (by rfl) ⟨1385097, by rfl⟩ : syracuseStep 3693593 = 2770195) B2770195
theorem B2462395 : Blo 2187435 2462395 := bstep (se 1 (by rfl) ⟨1846796, by rfl⟩ : syracuseStep 2462395 = 3693593) B3693593
theorem B3283193 : Blo 2187435 3283193 := bstep (se 2 (by rfl) ⟨1231197, by rfl⟩ : syracuseStep 3283193 = 2462395) B2462395
theorem B2188795 : Blo 2187435 2188795 := bstep (se 1 (by rfl) ⟨1641596, by rfl⟩ : syracuseStep 2188795 = 3283193) B3283193
theorem B4437325 : Blo 2187435 4437325 := bbase (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) (by norm_num)
theorem B23665733 : Blo 2187435 23665733 := bstep (se 4 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 23665733 = 4437325) B4437325
theorem B15777155 : Blo 2187435 15777155 := bstep (se 1 (by rfl) ⟨11832866, by rfl⟩ : syracuseStep 15777155 = 23665733) B23665733
theorem B10518103 : Blo 2187435 10518103 := bstep (se 1 (by rfl) ⟨7888577, by rfl⟩ : syracuseStep 10518103 = 15777155) B15777155
theorem B56096549 : Blo 2187435 56096549 := bstep (se 4 (by rfl) ⟨5259051, by rfl⟩ : syracuseStep 56096549 = 10518103) B10518103
theorem B37397699 : Blo 2187435 37397699 := bstep (se 1 (by rfl) ⟨28048274, by rfl⟩ : syracuseStep 37397699 = 56096549) B56096549
theorem B24931799 : Blo 2187435 24931799 := bstep (se 1 (by rfl) ⟨18698849, by rfl⟩ : syracuseStep 24931799 = 37397699) B37397699
theorem B16621199 : Blo 2187435 16621199 := bstep (se 1 (by rfl) ⟨12465899, by rfl⟩ : syracuseStep 16621199 = 24931799) B24931799
theorem B11080799 : Blo 2187435 11080799 := bstep (se 1 (by rfl) ⟨8310599, by rfl⟩ : syracuseStep 11080799 = 16621199) B16621199
theorem B7387199 : Blo 2187435 7387199 := bstep (se 1 (by rfl) ⟨5540399, by rfl⟩ : syracuseStep 7387199 = 11080799) B11080799
theorem B4924799 : Blo 2187435 4924799 := bstep (se 1 (by rfl) ⟨3693599, by rfl⟩ : syracuseStep 4924799 = 7387199) B7387199
theorem B3283199 : Blo 2187435 3283199 := bstep (se 1 (by rfl) ⟨2462399, by rfl⟩ : syracuseStep 3283199 = 4924799) B4924799
theorem B2188799 : Blo 2187435 2188799 := bstep (se 1 (by rfl) ⟨1641599, by rfl⟩ : syracuseStep 2188799 = 3283199) B3283199
theorem B3283205 : Blo 2187435 3283205 := bbase (se 4 (by rfl) ⟨307800, by rfl⟩ : syracuseStep 3283205 = 615601) (by norm_num)
theorem B2188803 : Blo 2187435 2188803 := bstep (se 1 (by rfl) ⟨1641602, by rfl⟩ : syracuseStep 2188803 = 3283205) B3283205
theorem B3693613 : Blo 2187435 3693613 := bbase (se 3 (by rfl) ⟨692552, by rfl⟩ : syracuseStep 3693613 = 1385105) (by norm_num)
theorem B4924817 : Blo 2187435 4924817 := bstep (se 2 (by rfl) ⟨1846806, by rfl⟩ : syracuseStep 4924817 = 3693613) B3693613
theorem B3283211 : Blo 2187435 3283211 := bstep (se 1 (by rfl) ⟨2462408, by rfl⟩ : syracuseStep 3283211 = 4924817) B4924817
theorem B2188807 : Blo 2187435 2188807 := bstep (se 1 (by rfl) ⟨1641605, by rfl⟩ : syracuseStep 2188807 = 3283211) B3283211
theorem B2462413 : Blo 2187435 2462413 := bbase (se 3 (by rfl) ⟨461702, by rfl⟩ : syracuseStep 2462413 = 923405) (by norm_num)
theorem B3283217 : Blo 2187435 3283217 := bstep (se 2 (by rfl) ⟨1231206, by rfl⟩ : syracuseStep 3283217 = 2462413) B2462413
theorem B2188811 : Blo 2187435 2188811 := bstep (se 1 (by rfl) ⟨1641608, by rfl⟩ : syracuseStep 2188811 = 3283217) B3283217
theorem B7387253 : Blo 2187435 7387253 := bbase (se 5 (by rfl) ⟨346277, by rfl⟩ : syracuseStep 7387253 = 692555) (by norm_num)
theorem B4924835 : Blo 2187435 4924835 := bstep (se 1 (by rfl) ⟨3693626, by rfl⟩ : syracuseStep 4924835 = 7387253) B7387253
theorem B3283223 : Blo 2187435 3283223 := bstep (se 1 (by rfl) ⟨2462417, by rfl⟩ : syracuseStep 3283223 = 4924835) B4924835
theorem B2188815 : Blo 2187435 2188815 := bstep (se 1 (by rfl) ⟨1641611, by rfl⟩ : syracuseStep 2188815 = 3283223) B3283223
theorem B3283229 : Blo 2187435 3283229 := bbase (se 3 (by rfl) ⟨615605, by rfl⟩ : syracuseStep 3283229 = 1231211) (by norm_num)
theorem B2188819 : Blo 2187435 2188819 := bstep (se 1 (by rfl) ⟨1641614, by rfl⟩ : syracuseStep 2188819 = 3283229) B3283229
theorem B4924853 : Blo 2187435 4924853 := bbase (se 5 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 4924853 = 461705) (by norm_num)
theorem B3283235 : Blo 2187435 3283235 := bstep (se 1 (by rfl) ⟨2462426, by rfl⟩ : syracuseStep 3283235 = 4924853) B4924853
theorem B2188823 : Blo 2187435 2188823 := bstep (se 1 (by rfl) ⟨1641617, by rfl⟩ : syracuseStep 2188823 = 3283235) B3283235
theorem B4674773 : Blo 2187435 4674773 := bbase (se 7 (by rfl) ⟨54782, by rfl⟩ : syracuseStep 4674773 = 109565) (by norm_num)
theorem B12466061 : Blo 2187435 12466061 := bstep (se 3 (by rfl) ⟨2337386, by rfl⟩ : syracuseStep 12466061 = 4674773) B4674773
theorem B8310707 : Blo 2187435 8310707 := bstep (se 1 (by rfl) ⟨6233030, by rfl⟩ : syracuseStep 8310707 = 12466061) B12466061
theorem B5540471 : Blo 2187435 5540471 := bstep (se 1 (by rfl) ⟨4155353, by rfl⟩ : syracuseStep 5540471 = 8310707) B8310707
theorem B3693647 : Blo 2187435 3693647 := bstep (se 1 (by rfl) ⟨2770235, by rfl⟩ : syracuseStep 3693647 = 5540471) B5540471
theorem B2462431 : Blo 2187435 2462431 := bstep (se 1 (by rfl) ⟨1846823, by rfl⟩ : syracuseStep 2462431 = 3693647) B3693647
theorem B3283241 : Blo 2187435 3283241 := bstep (se 2 (by rfl) ⟨1231215, by rfl⟩ : syracuseStep 3283241 = 2462431) B2462431
theorem B2188827 : Blo 2187435 2188827 := bstep (se 1 (by rfl) ⟨1641620, by rfl⟩ : syracuseStep 2188827 = 3283241) B3283241
theorem B4674781 : Blo 2187435 4674781 := bbase (se 3 (by rfl) ⟨876521, by rfl⟩ : syracuseStep 4674781 = 1753043) (by norm_num)
theorem B6233041 : Blo 2187435 6233041 := bstep (se 2 (by rfl) ⟨2337390, by rfl⟩ : syracuseStep 6233041 = 4674781) B4674781
theorem B8310721 : Blo 2187435 8310721 := bstep (se 2 (by rfl) ⟨3116520, by rfl⟩ : syracuseStep 8310721 = 6233041) B6233041
theorem B11080961 : Blo 2187435 11080961 := bstep (se 2 (by rfl) ⟨4155360, by rfl⟩ : syracuseStep 11080961 = 8310721) B8310721
theorem B7387307 : Blo 2187435 7387307 := bstep (se 1 (by rfl) ⟨5540480, by rfl⟩ : syracuseStep 7387307 = 11080961) B11080961
theorem B4924871 : Blo 2187435 4924871 := bstep (se 1 (by rfl) ⟨3693653, by rfl⟩ : syracuseStep 4924871 = 7387307) B7387307
theorem B3283247 : Blo 2187435 3283247 := bstep (se 1 (by rfl) ⟨2462435, by rfl⟩ : syracuseStep 3283247 = 4924871) B4924871
theorem B2188831 : Blo 2187435 2188831 := bstep (se 1 (by rfl) ⟨1641623, by rfl⟩ : syracuseStep 2188831 = 3283247) B3283247
theorem B3283253 : Blo 2187435 3283253 := bbase (se 5 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 3283253 = 307805) (by norm_num)
theorem B2188835 : Blo 2187435 2188835 := bstep (se 1 (by rfl) ⟨1641626, by rfl⟩ : syracuseStep 2188835 = 3283253) B3283253
theorem B5540501 : Blo 2187435 5540501 := bbase (se 6 (by rfl) ⟨129855, by rfl⟩ : syracuseStep 5540501 = 259711) (by norm_num)
theorem B3693667 : Blo 2187435 3693667 := bstep (se 1 (by rfl) ⟨2770250, by rfl⟩ : syracuseStep 3693667 = 5540501) B5540501
theorem B4924889 : Blo 2187435 4924889 := bstep (se 2 (by rfl) ⟨1846833, by rfl⟩ : syracuseStep 4924889 = 3693667) B3693667
theorem B3283259 : Blo 2187435 3283259 := bstep (se 1 (by rfl) ⟨2462444, by rfl⟩ : syracuseStep 3283259 = 4924889) B4924889
theorem B2188839 : Blo 2187435 2188839 := bstep (se 1 (by rfl) ⟨1641629, by rfl⟩ : syracuseStep 2188839 = 3283259) B3283259
theorem B2462449 : Blo 2187435 2462449 := bbase (se 2 (by rfl) ⟨923418, by rfl⟩ : syracuseStep 2462449 = 1846837) (by norm_num)
theorem B3283265 : Blo 2187435 3283265 := bstep (se 2 (by rfl) ⟨1231224, by rfl⟩ : syracuseStep 3283265 = 2462449) B2462449
theorem B2188843 : Blo 2187435 2188843 := bstep (se 1 (by rfl) ⟨1641632, by rfl⟩ : syracuseStep 2188843 = 3283265) B3283265
theorem B10684133 : Blo 2187435 10684133 := bbase (se 4 (by rfl) ⟨1001637, by rfl⟩ : syracuseStep 10684133 = 2003275) (by norm_num)
theorem B7122755 : Blo 2187435 7122755 := bstep (se 1 (by rfl) ⟨5342066, by rfl⟩ : syracuseStep 7122755 = 10684133) B10684133
theorem B4748503 : Blo 2187435 4748503 := bstep (se 1 (by rfl) ⟨3561377, by rfl⟩ : syracuseStep 4748503 = 7122755) B7122755
theorem B6331337 : Blo 2187435 6331337 := bstep (se 2 (by rfl) ⟨2374251, by rfl⟩ : syracuseStep 6331337 = 4748503) B4748503
theorem B4220891 : Blo 2187435 4220891 := bstep (se 1 (by rfl) ⟨3165668, by rfl⟩ : syracuseStep 4220891 = 6331337) B6331337
theorem B2813927 : Blo 2187435 2813927 := bstep (se 1 (by rfl) ⟨2110445, by rfl⟩ : syracuseStep 2813927 = 4220891) B4220891
theorem B7503805 : Blo 2187435 7503805 := bstep (se 3 (by rfl) ⟨1406963, by rfl⟩ : syracuseStep 7503805 = 2813927) B2813927
theorem B40020293 : Blo 2187435 40020293 := bstep (se 4 (by rfl) ⟨3751902, by rfl⟩ : syracuseStep 40020293 = 7503805) B7503805
theorem B26680195 : Blo 2187435 26680195 := bstep (se 1 (by rfl) ⟨20010146, by rfl⟩ : syracuseStep 26680195 = 40020293) B40020293
theorem B35573593 : Blo 2187435 35573593 := bstep (se 2 (by rfl) ⟨13340097, by rfl⟩ : syracuseStep 35573593 = 26680195) B26680195
theorem B47431457 : Blo 2187435 47431457 := bstep (se 2 (by rfl) ⟨17786796, by rfl⟩ : syracuseStep 47431457 = 35573593) B35573593
theorem B31620971 : Blo 2187435 31620971 := bstep (se 1 (by rfl) ⟨23715728, by rfl⟩ : syracuseStep 31620971 = 47431457) B47431457
theorem B21080647 : Blo 2187435 21080647 := bstep (se 1 (by rfl) ⟨15810485, by rfl⟩ : syracuseStep 21080647 = 31620971) B31620971
theorem B28107529 : Blo 2187435 28107529 := bstep (se 2 (by rfl) ⟨10540323, by rfl⟩ : syracuseStep 28107529 = 21080647) B21080647
theorem B149906821 : Blo 2187435 149906821 := bstep (se 4 (by rfl) ⟨14053764, by rfl⟩ : syracuseStep 149906821 = 28107529) B28107529
theorem B199875761 : Blo 2187435 199875761 := bstep (se 2 (by rfl) ⟨74953410, by rfl⟩ : syracuseStep 199875761 = 149906821) B149906821
theorem B133250507 : Blo 2187435 133250507 := bstep (se 1 (by rfl) ⟨99937880, by rfl⟩ : syracuseStep 133250507 = 199875761) B199875761
theorem B88833671 : Blo 2187435 88833671 := bstep (se 1 (by rfl) ⟨66625253, by rfl⟩ : syracuseStep 88833671 = 133250507) B133250507
theorem B59222447 : Blo 2187435 59222447 := bstep (se 1 (by rfl) ⟨44416835, by rfl⟩ : syracuseStep 59222447 = 88833671) B88833671
theorem B39481631 : Blo 2187435 39481631 := bstep (se 1 (by rfl) ⟨29611223, by rfl⟩ : syracuseStep 39481631 = 59222447) B59222447
theorem B26321087 : Blo 2187435 26321087 := bstep (se 1 (by rfl) ⟨19740815, by rfl⟩ : syracuseStep 26321087 = 39481631) B39481631
theorem B70189565 : Blo 2187435 70189565 := bstep (se 3 (by rfl) ⟨13160543, by rfl⟩ : syracuseStep 70189565 = 26321087) B26321087
theorem B187172173 : Blo 2187435 187172173 := bstep (se 3 (by rfl) ⟨35094782, by rfl⟩ : syracuseStep 187172173 = 70189565) B70189565
theorem B998251589 : Blo 2187435 998251589 := bstep (se 4 (by rfl) ⟨93586086, by rfl⟩ : syracuseStep 998251589 = 187172173) B187172173
theorem B665501059 : Blo 2187435 665501059 := bstep (se 1 (by rfl) ⟨499125794, by rfl⟩ : syracuseStep 665501059 = 998251589) B998251589
theorem B887334745 : Blo 2187435 887334745 := bstep (se 2 (by rfl) ⟨332750529, by rfl⟩ : syracuseStep 887334745 = 665501059) B665501059
theorem B1183112993 : Blo 2187435 1183112993 := bstep (se 2 (by rfl) ⟨443667372, by rfl⟩ : syracuseStep 1183112993 = 887334745) B887334745
theorem B788741995 : Blo 2187435 788741995 := bstep (se 1 (by rfl) ⟨591556496, by rfl⟩ : syracuseStep 788741995 = 1183112993) B1183112993
theorem B1051655993 : Blo 2187435 1051655993 := bstep (se 2 (by rfl) ⟨394370997, by rfl⟩ : syracuseStep 1051655993 = 788741995) B788741995
theorem B701103995 : Blo 2187435 701103995 := bstep (se 1 (by rfl) ⟨525827996, by rfl⟩ : syracuseStep 701103995 = 1051655993) B1051655993
theorem B467402663 : Blo 2187435 467402663 := bstep (se 1 (by rfl) ⟨350551997, by rfl⟩ : syracuseStep 467402663 = 701103995) B701103995
theorem B311601775 : Blo 2187435 311601775 := bstep (se 1 (by rfl) ⟨233701331, by rfl⟩ : syracuseStep 311601775 = 467402663) B467402663
theorem B415469033 : Blo 2187435 415469033 := bstep (se 2 (by rfl) ⟨155800887, by rfl⟩ : syracuseStep 415469033 = 311601775) B311601775
theorem B276979355 : Blo 2187435 276979355 := bstep (se 1 (by rfl) ⟨207734516, by rfl⟩ : syracuseStep 276979355 = 415469033) B415469033
theorem B184652903 : Blo 2187435 184652903 := bstep (se 1 (by rfl) ⟨138489677, by rfl⟩ : syracuseStep 184652903 = 276979355) B276979355
theorem B492407741 : Blo 2187435 492407741 := bstep (se 3 (by rfl) ⟨92326451, by rfl⟩ : syracuseStep 492407741 = 184652903) B184652903
theorem B328271827 : Blo 2187435 328271827 := bstep (se 1 (by rfl) ⟨246203870, by rfl⟩ : syracuseStep 328271827 = 492407741) B492407741
theorem B437695769 : Blo 2187435 437695769 := bstep (se 2 (by rfl) ⟨164135913, by rfl⟩ : syracuseStep 437695769 = 328271827) B328271827
theorem B1167188717 : Blo 2187435 1167188717 := bstep (se 3 (by rfl) ⟨218847884, by rfl⟩ : syracuseStep 1167188717 = 437695769) B437695769
theorem B778125811 : Blo 2187435 778125811 := bstep (se 1 (by rfl) ⟨583594358, by rfl⟩ : syracuseStep 778125811 = 1167188717) B1167188717
theorem B1037501081 : Blo 2187435 1037501081 := bstep (se 2 (by rfl) ⟨389062905, by rfl⟩ : syracuseStep 1037501081 = 778125811) B778125811
theorem B691667387 : Blo 2187435 691667387 := bstep (se 1 (by rfl) ⟨518750540, by rfl⟩ : syracuseStep 691667387 = 1037501081) B1037501081
theorem B461111591 : Blo 2187435 461111591 := bstep (se 1 (by rfl) ⟨345833693, by rfl⟩ : syracuseStep 461111591 = 691667387) B691667387
theorem B307407727 : Blo 2187435 307407727 := bstep (se 1 (by rfl) ⟨230555795, by rfl⟩ : syracuseStep 307407727 = 461111591) B461111591
theorem B409876969 : Blo 2187435 409876969 := bstep (se 2 (by rfl) ⟨153703863, by rfl⟩ : syracuseStep 409876969 = 307407727) B307407727
theorem B546502625 : Blo 2187435 546502625 := bstep (se 2 (by rfl) ⟨204938484, by rfl⟩ : syracuseStep 546502625 = 409876969) B409876969
theorem B364335083 : Blo 2187435 364335083 := bstep (se 1 (by rfl) ⟨273251312, by rfl⟩ : syracuseStep 364335083 = 546502625) B546502625
theorem B242890055 : Blo 2187435 242890055 := bstep (se 1 (by rfl) ⟨182167541, by rfl⟩ : syracuseStep 242890055 = 364335083) B364335083
theorem B161926703 : Blo 2187435 161926703 := bstep (se 1 (by rfl) ⟨121445027, by rfl⟩ : syracuseStep 161926703 = 242890055) B242890055
theorem B107951135 : Blo 2187435 107951135 := bstep (se 1 (by rfl) ⟨80963351, by rfl⟩ : syracuseStep 107951135 = 161926703) B161926703
theorem B1151478773 : Blo 2187435 1151478773 := bstep (se 5 (by rfl) ⟨53975567, by rfl⟩ : syracuseStep 1151478773 = 107951135) B107951135
theorem B767652515 : Blo 2187435 767652515 := bstep (se 1 (by rfl) ⟨575739386, by rfl⟩ : syracuseStep 767652515 = 1151478773) B1151478773
theorem B511768343 : Blo 2187435 511768343 := bstep (se 1 (by rfl) ⟨383826257, by rfl⟩ : syracuseStep 511768343 = 767652515) B767652515
theorem B341178895 : Blo 2187435 341178895 := bstep (se 1 (by rfl) ⟨255884171, by rfl⟩ : syracuseStep 341178895 = 511768343) B511768343
theorem B454905193 : Blo 2187435 454905193 := bstep (se 2 (by rfl) ⟨170589447, by rfl⟩ : syracuseStep 454905193 = 341178895) B341178895
theorem B606540257 : Blo 2187435 606540257 := bstep (se 2 (by rfl) ⟨227452596, by rfl⟩ : syracuseStep 606540257 = 454905193) B454905193
theorem B404360171 : Blo 2187435 404360171 := bstep (se 1 (by rfl) ⟨303270128, by rfl⟩ : syracuseStep 404360171 = 606540257) B606540257
theorem B269573447 : Blo 2187435 269573447 := bstep (se 1 (by rfl) ⟨202180085, by rfl⟩ : syracuseStep 269573447 = 404360171) B404360171
theorem B179715631 : Blo 2187435 179715631 := bstep (se 1 (by rfl) ⟨134786723, by rfl⟩ : syracuseStep 179715631 = 269573447) B269573447
theorem B239620841 : Blo 2187435 239620841 := bstep (se 2 (by rfl) ⟨89857815, by rfl⟩ : syracuseStep 239620841 = 179715631) B179715631
theorem B159747227 : Blo 2187435 159747227 := bstep (se 1 (by rfl) ⟨119810420, by rfl⟩ : syracuseStep 159747227 = 239620841) B239620841
theorem B106498151 : Blo 2187435 106498151 := bstep (se 1 (by rfl) ⟨79873613, by rfl⟩ : syracuseStep 106498151 = 159747227) B159747227
theorem B70998767 : Blo 2187435 70998767 := bstep (se 1 (by rfl) ⟨53249075, by rfl⟩ : syracuseStep 70998767 = 106498151) B106498151
theorem B47332511 : Blo 2187435 47332511 := bstep (se 1 (by rfl) ⟨35499383, by rfl⟩ : syracuseStep 47332511 = 70998767) B70998767
theorem B31555007 : Blo 2187435 31555007 := bstep (se 1 (by rfl) ⟨23666255, by rfl⟩ : syracuseStep 31555007 = 47332511) B47332511
theorem B21036671 : Blo 2187435 21036671 := bstep (se 1 (by rfl) ⟨15777503, by rfl⟩ : syracuseStep 21036671 = 31555007) B31555007
theorem B14024447 : Blo 2187435 14024447 := bstep (se 1 (by rfl) ⟨10518335, by rfl⟩ : syracuseStep 14024447 = 21036671) B21036671
theorem B9349631 : Blo 2187435 9349631 := bstep (se 1 (by rfl) ⟨7012223, by rfl⟩ : syracuseStep 9349631 = 14024447) B14024447
theorem B6233087 : Blo 2187435 6233087 := bstep (se 1 (by rfl) ⟨4674815, by rfl⟩ : syracuseStep 6233087 = 9349631) B9349631
theorem B4155391 : Blo 2187435 4155391 := bstep (se 1 (by rfl) ⟨3116543, by rfl⟩ : syracuseStep 4155391 = 6233087) B6233087
theorem B5540521 : Blo 2187435 5540521 := bstep (se 2 (by rfl) ⟨2077695, by rfl⟩ : syracuseStep 5540521 = 4155391) B4155391
theorem B7387361 : Blo 2187435 7387361 := bstep (se 2 (by rfl) ⟨2770260, by rfl⟩ : syracuseStep 7387361 = 5540521) B5540521
theorem B4924907 : Blo 2187435 4924907 := bstep (se 1 (by rfl) ⟨3693680, by rfl⟩ : syracuseStep 4924907 = 7387361) B7387361
theorem B3283271 : Blo 2187435 3283271 := bstep (se 1 (by rfl) ⟨2462453, by rfl⟩ : syracuseStep 3283271 = 4924907) B4924907
theorem B2188847 : Blo 2187435 2188847 := bstep (se 1 (by rfl) ⟨1641635, by rfl⟩ : syracuseStep 2188847 = 3283271) B3283271
theorem B3283277 : Blo 2187435 3283277 := bbase (se 3 (by rfl) ⟨615614, by rfl⟩ : syracuseStep 3283277 = 1231229) (by norm_num)
theorem B2188851 : Blo 2187435 2188851 := bstep (se 1 (by rfl) ⟨1641638, by rfl⟩ : syracuseStep 2188851 = 3283277) B3283277
theorem B4924925 : Blo 2187435 4924925 := bbase (se 3 (by rfl) ⟨923423, by rfl⟩ : syracuseStep 4924925 = 1846847) (by norm_num)
theorem B3283283 : Blo 2187435 3283283 := bstep (se 1 (by rfl) ⟨2462462, by rfl⟩ : syracuseStep 3283283 = 4924925) B4924925
theorem B2188855 : Blo 2187435 2188855 := bstep (se 1 (by rfl) ⟨1641641, by rfl⟩ : syracuseStep 2188855 = 3283283) B3283283
theorem B3693701 : Blo 2187435 3693701 := bbase (se 4 (by rfl) ⟨346284, by rfl⟩ : syracuseStep 3693701 = 692569) (by norm_num)
theorem B2462467 : Blo 2187435 2462467 := bstep (se 1 (by rfl) ⟨1846850, by rfl⟩ : syracuseStep 2462467 = 3693701) B3693701
theorem B3283289 : Blo 2187435 3283289 := bstep (se 2 (by rfl) ⟨1231233, by rfl⟩ : syracuseStep 3283289 = 2462467) B2462467
theorem B2188859 : Blo 2187435 2188859 := bstep (se 1 (by rfl) ⟨1641644, by rfl⟩ : syracuseStep 2188859 = 3283289) B3283289
theorem B16621685 : Blo 2187435 16621685 := bbase (se 5 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 16621685 = 1558283) (by norm_num)
theorem B11081123 : Blo 2187435 11081123 := bstep (se 1 (by rfl) ⟨8310842, by rfl⟩ : syracuseStep 11081123 = 16621685) B16621685
theorem B7387415 : Blo 2187435 7387415 := bstep (se 1 (by rfl) ⟨5540561, by rfl⟩ : syracuseStep 7387415 = 11081123) B11081123
theorem B4924943 : Blo 2187435 4924943 := bstep (se 1 (by rfl) ⟨3693707, by rfl⟩ : syracuseStep 4924943 = 7387415) B7387415
theorem B3283295 : Blo 2187435 3283295 := bstep (se 1 (by rfl) ⟨2462471, by rfl⟩ : syracuseStep 3283295 = 4924943) B4924943
theorem B2188863 : Blo 2187435 2188863 := bstep (se 1 (by rfl) ⟨1641647, by rfl⟩ : syracuseStep 2188863 = 3283295) B3283295
theorem B3283301 : Blo 2187435 3283301 := bbase (se 4 (by rfl) ⟨307809, by rfl⟩ : syracuseStep 3283301 = 615619) (by norm_num)
theorem B2188867 : Blo 2187435 2188867 := bstep (se 1 (by rfl) ⟨1641650, by rfl⟩ : syracuseStep 2188867 = 3283301) B3283301
theorem B4155437 : Blo 2187435 4155437 := bbase (se 3 (by rfl) ⟨779144, by rfl⟩ : syracuseStep 4155437 = 1558289) (by norm_num)
theorem B2770291 : Blo 2187435 2770291 := bstep (se 1 (by rfl) ⟨2077718, by rfl⟩ : syracuseStep 2770291 = 4155437) B4155437
theorem B3693721 : Blo 2187435 3693721 := bstep (se 2 (by rfl) ⟨1385145, by rfl⟩ : syracuseStep 3693721 = 2770291) B2770291
theorem B4924961 : Blo 2187435 4924961 := bstep (se 2 (by rfl) ⟨1846860, by rfl⟩ : syracuseStep 4924961 = 3693721) B3693721
theorem B3283307 : Blo 2187435 3283307 := bstep (se 1 (by rfl) ⟨2462480, by rfl⟩ : syracuseStep 3283307 = 4924961) B4924961
theorem B2188871 : Blo 2187435 2188871 := bstep (se 1 (by rfl) ⟨1641653, by rfl⟩ : syracuseStep 2188871 = 3283307) B3283307
theorem B2462485 : Blo 2187435 2462485 := bbase (se 6 (by rfl) ⟨57714, by rfl⟩ : syracuseStep 2462485 = 115429) (by norm_num)
theorem B3283313 : Blo 2187435 3283313 := bstep (se 2 (by rfl) ⟨1231242, by rfl⟩ : syracuseStep 3283313 = 2462485) B2462485
theorem B2188875 : Blo 2187435 2188875 := bstep (se 1 (by rfl) ⟨1641656, by rfl⟩ : syracuseStep 2188875 = 3283313) B3283313
theorem B2770301 : Blo 2187435 2770301 := bbase (se 3 (by rfl) ⟨519431, by rfl⟩ : syracuseStep 2770301 = 1038863) (by norm_num)
theorem B7387469 : Blo 2187435 7387469 := bstep (se 3 (by rfl) ⟨1385150, by rfl⟩ : syracuseStep 7387469 = 2770301) B2770301
theorem B4924979 : Blo 2187435 4924979 := bstep (se 1 (by rfl) ⟨3693734, by rfl⟩ : syracuseStep 4924979 = 7387469) B7387469
theorem B3283319 : Blo 2187435 3283319 := bstep (se 1 (by rfl) ⟨2462489, by rfl⟩ : syracuseStep 3283319 = 4924979) B4924979
theorem B2188879 : Blo 2187435 2188879 := bstep (se 1 (by rfl) ⟨1641659, by rfl⟩ : syracuseStep 2188879 = 3283319) B3283319
theorem B3283325 : Blo 2187435 3283325 := bbase (se 3 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 3283325 = 1231247) (by norm_num)
theorem B2188883 : Blo 2187435 2188883 := bstep (se 1 (by rfl) ⟨1641662, by rfl⟩ : syracuseStep 2188883 = 3283325) B3283325
theorem B4924997 : Blo 2187435 4924997 := bbase (se 4 (by rfl) ⟨461718, by rfl⟩ : syracuseStep 4924997 = 923437) (by norm_num)
theorem B3283331 : Blo 2187435 3283331 := bstep (se 1 (by rfl) ⟨2462498, by rfl⟩ : syracuseStep 3283331 = 4924997) B4924997
theorem B2188887 : Blo 2187435 2188887 := bstep (se 1 (by rfl) ⟨1641665, by rfl⟩ : syracuseStep 2188887 = 3283331) B3283331
theorem B2218757 : Blo 2187435 2218757 := bbase (se 4 (by rfl) ⟨208008, by rfl⟩ : syracuseStep 2218757 = 416017) (by norm_num)
theorem B5916685 : Blo 2187435 5916685 := bstep (se 3 (by rfl) ⟨1109378, by rfl⟩ : syracuseStep 5916685 = 2218757) B2218757
theorem B7888913 : Blo 2187435 7888913 := bstep (se 2 (by rfl) ⟨2958342, by rfl⟩ : syracuseStep 7888913 = 5916685) B5916685
theorem B5259275 : Blo 2187435 5259275 := bstep (se 1 (by rfl) ⟨3944456, by rfl⟩ : syracuseStep 5259275 = 7888913) B7888913
theorem B3506183 : Blo 2187435 3506183 := bstep (se 1 (by rfl) ⟨2629637, by rfl⟩ : syracuseStep 3506183 = 5259275) B5259275
theorem B2337455 : Blo 2187435 2337455 := bstep (se 1 (by rfl) ⟨1753091, by rfl⟩ : syracuseStep 2337455 = 3506183) B3506183
theorem B6233213 : Blo 2187435 6233213 := bstep (se 3 (by rfl) ⟨1168727, by rfl⟩ : syracuseStep 6233213 = 2337455) B2337455
theorem B4155475 : Blo 2187435 4155475 := bstep (se 1 (by rfl) ⟨3116606, by rfl⟩ : syracuseStep 4155475 = 6233213) B6233213
theorem B5540633 : Blo 2187435 5540633 := bstep (se 2 (by rfl) ⟨2077737, by rfl⟩ : syracuseStep 5540633 = 4155475) B4155475
theorem B3693755 : Blo 2187435 3693755 := bstep (se 1 (by rfl) ⟨2770316, by rfl⟩ : syracuseStep 3693755 = 5540633) B5540633
theorem B2462503 : Blo 2187435 2462503 := bstep (se 1 (by rfl) ⟨1846877, by rfl⟩ : syracuseStep 2462503 = 3693755) B3693755
theorem B3283337 : Blo 2187435 3283337 := bstep (se 2 (by rfl) ⟨1231251, by rfl⟩ : syracuseStep 3283337 = 2462503) B2462503
theorem B2188891 : Blo 2187435 2188891 := bstep (se 1 (by rfl) ⟨1641668, by rfl⟩ : syracuseStep 2188891 = 3283337) B3283337
theorem B11081285 : Blo 2187435 11081285 := bbase (se 4 (by rfl) ⟨1038870, by rfl⟩ : syracuseStep 11081285 = 2077741) (by norm_num)
theorem B7387523 : Blo 2187435 7387523 := bstep (se 1 (by rfl) ⟨5540642, by rfl⟩ : syracuseStep 7387523 = 11081285) B11081285
theorem B4925015 : Blo 2187435 4925015 := bstep (se 1 (by rfl) ⟨3693761, by rfl⟩ : syracuseStep 4925015 = 7387523) B7387523
theorem B3283343 : Blo 2187435 3283343 := bstep (se 1 (by rfl) ⟨2462507, by rfl⟩ : syracuseStep 3283343 = 4925015) B4925015
theorem B2188895 : Blo 2187435 2188895 := bstep (se 1 (by rfl) ⟨1641671, by rfl⟩ : syracuseStep 2188895 = 3283343) B3283343
theorem B3283349 : Blo 2187435 3283349 := bbase (se 6 (by rfl) ⟨76953, by rfl⟩ : syracuseStep 3283349 = 153907) (by norm_num)
theorem B2188899 : Blo 2187435 2188899 := bstep (se 1 (by rfl) ⟨1641674, by rfl⟩ : syracuseStep 2188899 = 3283349) B3283349
theorem B3944477 : Blo 2187435 3944477 := bbase (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) (by norm_num)
theorem B10518605 : Blo 2187435 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B7012403 : Blo 2187435 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B4674935 : Blo 2187435 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B12466493 : Blo 2187435 12466493 := bstep (se 3 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 12466493 = 4674935) B4674935
theorem B8310995 : Blo 2187435 8310995 := bstep (se 1 (by rfl) ⟨6233246, by rfl⟩ : syracuseStep 8310995 = 12466493) B12466493
theorem B5540663 : Blo 2187435 5540663 := bstep (se 1 (by rfl) ⟨4155497, by rfl⟩ : syracuseStep 5540663 = 8310995) B8310995
theorem B3693775 : Blo 2187435 3693775 := bstep (se 1 (by rfl) ⟨2770331, by rfl⟩ : syracuseStep 3693775 = 5540663) B5540663
theorem B4925033 : Blo 2187435 4925033 := bstep (se 2 (by rfl) ⟨1846887, by rfl⟩ : syracuseStep 4925033 = 3693775) B3693775
theorem B3283355 : Blo 2187435 3283355 := bstep (se 1 (by rfl) ⟨2462516, by rfl⟩ : syracuseStep 3283355 = 4925033) B4925033
theorem B2188903 : Blo 2187435 2188903 := bstep (se 1 (by rfl) ⟨1641677, by rfl⟩ : syracuseStep 2188903 = 3283355) B3283355
theorem B2462521 : Blo 2187435 2462521 := bbase (se 2 (by rfl) ⟨923445, by rfl⟩ : syracuseStep 2462521 = 1846891) (by norm_num)
theorem B3283361 : Blo 2187435 3283361 := bstep (se 2 (by rfl) ⟨1231260, by rfl⟩ : syracuseStep 3283361 = 2462521) B2462521
theorem B2188907 : Blo 2187435 2188907 := bstep (se 1 (by rfl) ⟨1641680, by rfl⟩ : syracuseStep 2188907 = 3283361) B3283361
theorem B6233269 : Blo 2187435 6233269 := bbase (se 5 (by rfl) ⟨292184, by rfl⟩ : syracuseStep 6233269 = 584369) (by norm_num)
theorem B8311025 : Blo 2187435 8311025 := bstep (se 2 (by rfl) ⟨3116634, by rfl⟩ : syracuseStep 8311025 = 6233269) B6233269
theorem B5540683 : Blo 2187435 5540683 := bstep (se 1 (by rfl) ⟨4155512, by rfl⟩ : syracuseStep 5540683 = 8311025) B8311025
theorem B7387577 : Blo 2187435 7387577 := bstep (se 2 (by rfl) ⟨2770341, by rfl⟩ : syracuseStep 7387577 = 5540683) B5540683
theorem B4925051 : Blo 2187435 4925051 := bstep (se 1 (by rfl) ⟨3693788, by rfl⟩ : syracuseStep 4925051 = 7387577) B7387577
theorem B3283367 : Blo 2187435 3283367 := bstep (se 1 (by rfl) ⟨2462525, by rfl⟩ : syracuseStep 3283367 = 4925051) B4925051
theorem B2188911 : Blo 2187435 2188911 := bstep (se 1 (by rfl) ⟨1641683, by rfl⟩ : syracuseStep 2188911 = 3283367) B3283367
theorem B3283373 : Blo 2187435 3283373 := bbase (se 3 (by rfl) ⟨615632, by rfl⟩ : syracuseStep 3283373 = 1231265) (by norm_num)
theorem B2188915 : Blo 2187435 2188915 := bstep (se 1 (by rfl) ⟨1641686, by rfl⟩ : syracuseStep 2188915 = 3283373) B3283373
theorem B4925069 : Blo 2187435 4925069 := bbase (se 3 (by rfl) ⟨923450, by rfl⟩ : syracuseStep 4925069 = 1846901) (by norm_num)
theorem B3283379 : Blo 2187435 3283379 := bstep (se 1 (by rfl) ⟨2462534, by rfl⟩ : syracuseStep 3283379 = 4925069) B4925069
theorem B2188919 : Blo 2187435 2188919 := bstep (se 1 (by rfl) ⟨1641689, by rfl⟩ : syracuseStep 2188919 = 3283379) B3283379
theorem B2770357 : Blo 2187435 2770357 := bbase (se 5 (by rfl) ⟨129860, by rfl⟩ : syracuseStep 2770357 = 259721) (by norm_num)
theorem B3693809 : Blo 2187435 3693809 := bstep (se 2 (by rfl) ⟨1385178, by rfl⟩ : syracuseStep 3693809 = 2770357) B2770357
theorem B2462539 : Blo 2187435 2462539 := bstep (se 1 (by rfl) ⟨1846904, by rfl⟩ : syracuseStep 2462539 = 3693809) B3693809
theorem B3283385 : Blo 2187435 3283385 := bstep (se 2 (by rfl) ⟨1231269, by rfl⟩ : syracuseStep 3283385 = 2462539) B2462539
theorem B2188923 : Blo 2187435 2188923 := bstep (se 1 (by rfl) ⟨1641692, by rfl⟩ : syracuseStep 2188923 = 3283385) B3283385
theorem B9984565 : Blo 2187435 9984565 := bbase (se 5 (by rfl) ⟨468026, by rfl⟩ : syracuseStep 9984565 = 936053) (by norm_num)
theorem B53251013 : Blo 2187435 53251013 := bstep (se 4 (by rfl) ⟨4992282, by rfl⟩ : syracuseStep 53251013 = 9984565) B9984565
theorem B35500675 : Blo 2187435 35500675 := bstep (se 1 (by rfl) ⟨26625506, by rfl⟩ : syracuseStep 35500675 = 53251013) B53251013
theorem B47334233 : Blo 2187435 47334233 := bstep (se 2 (by rfl) ⟨17750337, by rfl⟩ : syracuseStep 47334233 = 35500675) B35500675
theorem B31556155 : Blo 2187435 31556155 := bstep (se 1 (by rfl) ⟨23667116, by rfl⟩ : syracuseStep 31556155 = 47334233) B47334233
theorem B42074873 : Blo 2187435 42074873 := bstep (se 2 (by rfl) ⟨15778077, by rfl⟩ : syracuseStep 42074873 = 31556155) B31556155
theorem B28049915 : Blo 2187435 28049915 := bstep (se 1 (by rfl) ⟨21037436, by rfl⟩ : syracuseStep 28049915 = 42074873) B42074873
theorem B18699943 : Blo 2187435 18699943 := bstep (se 1 (by rfl) ⟨14024957, by rfl⟩ : syracuseStep 18699943 = 28049915) B28049915
theorem B24933257 : Blo 2187435 24933257 := bstep (se 2 (by rfl) ⟨9349971, by rfl⟩ : syracuseStep 24933257 = 18699943) B18699943
theorem B16622171 : Blo 2187435 16622171 := bstep (se 1 (by rfl) ⟨12466628, by rfl⟩ : syracuseStep 16622171 = 24933257) B24933257
theorem B11081447 : Blo 2187435 11081447 := bstep (se 1 (by rfl) ⟨8311085, by rfl⟩ : syracuseStep 11081447 = 16622171) B16622171
theorem B7387631 : Blo 2187435 7387631 := bstep (se 1 (by rfl) ⟨5540723, by rfl⟩ : syracuseStep 7387631 = 11081447) B11081447
theorem B4925087 : Blo 2187435 4925087 := bstep (se 1 (by rfl) ⟨3693815, by rfl⟩ : syracuseStep 4925087 = 7387631) B7387631
theorem B3283391 : Blo 2187435 3283391 := bstep (se 1 (by rfl) ⟨2462543, by rfl⟩ : syracuseStep 3283391 = 4925087) B4925087
theorem B2188927 : Blo 2187435 2188927 := bstep (se 1 (by rfl) ⟨1641695, by rfl⟩ : syracuseStep 2188927 = 3283391) B3283391
theorem B3283397 : Blo 2187435 3283397 := bbase (se 4 (by rfl) ⟨307818, by rfl⟩ : syracuseStep 3283397 = 615637) (by norm_num)
theorem B2188931 : Blo 2187435 2188931 := bstep (se 1 (by rfl) ⟨1641698, by rfl⟩ : syracuseStep 2188931 = 3283397) B3283397
theorem B3693829 : Blo 2187435 3693829 := bbase (se 4 (by rfl) ⟨346296, by rfl⟩ : syracuseStep 3693829 = 692593) (by norm_num)
theorem B4925105 : Blo 2187435 4925105 := bstep (se 2 (by rfl) ⟨1846914, by rfl⟩ : syracuseStep 4925105 = 3693829) B3693829
theorem B3283403 : Blo 2187435 3283403 := bstep (se 1 (by rfl) ⟨2462552, by rfl⟩ : syracuseStep 3283403 = 4925105) B4925105
theorem B2188935 : Blo 2187435 2188935 := bstep (se 1 (by rfl) ⟨1641701, by rfl⟩ : syracuseStep 2188935 = 3283403) B3283403
theorem B2462557 : Blo 2187435 2462557 := bbase (se 3 (by rfl) ⟨461729, by rfl⟩ : syracuseStep 2462557 = 923459) (by norm_num)
theorem B3283409 : Blo 2187435 3283409 := bstep (se 2 (by rfl) ⟨1231278, by rfl⟩ : syracuseStep 3283409 = 2462557) B2462557
theorem B2188939 : Blo 2187435 2188939 := bstep (se 1 (by rfl) ⟨1641704, by rfl⟩ : syracuseStep 2188939 = 3283409) B3283409
theorem B7387685 : Blo 2187435 7387685 := bbase (se 4 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 7387685 = 1385191) (by norm_num)
theorem B4925123 : Blo 2187435 4925123 := bstep (se 1 (by rfl) ⟨3693842, by rfl⟩ : syracuseStep 4925123 = 7387685) B7387685
theorem B3283415 : Blo 2187435 3283415 := bstep (se 1 (by rfl) ⟨2462561, by rfl⟩ : syracuseStep 3283415 = 4925123) B4925123
theorem B2188943 : Blo 2187435 2188943 := bstep (se 1 (by rfl) ⟨1641707, by rfl⟩ : syracuseStep 2188943 = 3283415) B3283415
theorem B3283421 : Blo 2187435 3283421 := bbase (se 3 (by rfl) ⟨615641, by rfl⟩ : syracuseStep 3283421 = 1231283) (by norm_num)
theorem B2188947 : Blo 2187435 2188947 := bstep (se 1 (by rfl) ⟨1641710, by rfl⟩ : syracuseStep 2188947 = 3283421) B3283421
theorem B4925141 : Blo 2187435 4925141 := bbase (se 7 (by rfl) ⟨57716, by rfl⟩ : syracuseStep 4925141 = 115433) (by norm_num)
theorem B3283427 : Blo 2187435 3283427 := bstep (se 1 (by rfl) ⟨2462570, by rfl⟩ : syracuseStep 3283427 = 4925141) B4925141
theorem B2188951 : Blo 2187435 2188951 := bstep (se 1 (by rfl) ⟨1641713, by rfl⟩ : syracuseStep 2188951 = 3283427) B3283427
theorem B3506285 : Blo 2187435 3506285 := bbase (se 3 (by rfl) ⟨657428, by rfl⟩ : syracuseStep 3506285 = 1314857) (by norm_num)
theorem B9350093 : Blo 2187435 9350093 := bstep (se 3 (by rfl) ⟨1753142, by rfl⟩ : syracuseStep 9350093 = 3506285) B3506285
theorem B6233395 : Blo 2187435 6233395 := bstep (se 1 (by rfl) ⟨4675046, by rfl⟩ : syracuseStep 6233395 = 9350093) B9350093
theorem B8311193 : Blo 2187435 8311193 := bstep (se 2 (by rfl) ⟨3116697, by rfl⟩ : syracuseStep 8311193 = 6233395) B6233395
theorem B5540795 : Blo 2187435 5540795 := bstep (se 1 (by rfl) ⟨4155596, by rfl⟩ : syracuseStep 5540795 = 8311193) B8311193
theorem B3693863 : Blo 2187435 3693863 := bstep (se 1 (by rfl) ⟨2770397, by rfl⟩ : syracuseStep 3693863 = 5540795) B5540795
theorem B2462575 : Blo 2187435 2462575 := bstep (se 1 (by rfl) ⟨1846931, by rfl⟩ : syracuseStep 2462575 = 3693863) B3693863
theorem B3283433 : Blo 2187435 3283433 := bstep (se 2 (by rfl) ⟨1231287, by rfl⟩ : syracuseStep 3283433 = 2462575) B2462575
theorem B2188955 : Blo 2187435 2188955 := bstep (se 1 (by rfl) ⟨1641716, by rfl⟩ : syracuseStep 2188955 = 3283433) B3283433
theorem B2218825 : Blo 2187435 2218825 := bbase (se 2 (by rfl) ⟨832059, by rfl⟩ : syracuseStep 2218825 = 1664119) (by norm_num)
theorem B2958433 : Blo 2187435 2958433 := bstep (se 2 (by rfl) ⟨1109412, by rfl⟩ : syracuseStep 2958433 = 2218825) B2218825
theorem B15778309 : Blo 2187435 15778309 := bstep (se 4 (by rfl) ⟨1479216, by rfl⟩ : syracuseStep 15778309 = 2958433) B2958433
theorem B21037745 : Blo 2187435 21037745 := bstep (se 2 (by rfl) ⟨7889154, by rfl⟩ : syracuseStep 21037745 = 15778309) B15778309
theorem B14025163 : Blo 2187435 14025163 := bstep (se 1 (by rfl) ⟨10518872, by rfl⟩ : syracuseStep 14025163 = 21037745) B21037745
theorem B18700217 : Blo 2187435 18700217 := bstep (se 2 (by rfl) ⟨7012581, by rfl⟩ : syracuseStep 18700217 = 14025163) B14025163
theorem B12466811 : Blo 2187435 12466811 := bstep (se 1 (by rfl) ⟨9350108, by rfl⟩ : syracuseStep 12466811 = 18700217) B18700217
theorem B8311207 : Blo 2187435 8311207 := bstep (se 1 (by rfl) ⟨6233405, by rfl⟩ : syracuseStep 8311207 = 12466811) B12466811
theorem B11081609 : Blo 2187435 11081609 := bstep (se 2 (by rfl) ⟨4155603, by rfl⟩ : syracuseStep 11081609 = 8311207) B8311207
theorem B7387739 : Blo 2187435 7387739 := bstep (se 1 (by rfl) ⟨5540804, by rfl⟩ : syracuseStep 7387739 = 11081609) B11081609
theorem B4925159 : Blo 2187435 4925159 := bstep (se 1 (by rfl) ⟨3693869, by rfl⟩ : syracuseStep 4925159 = 7387739) B7387739
theorem B3283439 : Blo 2187435 3283439 := bstep (se 1 (by rfl) ⟨2462579, by rfl⟩ : syracuseStep 3283439 = 4925159) B4925159
theorem B2188959 : Blo 2187435 2188959 := bstep (se 1 (by rfl) ⟨1641719, by rfl⟩ : syracuseStep 2188959 = 3283439) B3283439
theorem B3283445 : Blo 2187435 3283445 := bbase (se 5 (by rfl) ⟨153911, by rfl⟩ : syracuseStep 3283445 = 307823) (by norm_num)
theorem B2188963 : Blo 2187435 2188963 := bstep (se 1 (by rfl) ⟨1641722, by rfl⟩ : syracuseStep 2188963 = 3283445) B3283445
theorem B6233429 : Blo 2187435 6233429 := bbase (se 11 (by rfl) ⟨4565, by rfl⟩ : syracuseStep 6233429 = 9131) (by norm_num)
theorem B4155619 : Blo 2187435 4155619 := bstep (se 1 (by rfl) ⟨3116714, by rfl⟩ : syracuseStep 4155619 = 6233429) B6233429
theorem B5540825 : Blo 2187435 5540825 := bstep (se 2 (by rfl) ⟨2077809, by rfl⟩ : syracuseStep 5540825 = 4155619) B4155619
theorem B3693883 : Blo 2187435 3693883 := bstep (se 1 (by rfl) ⟨2770412, by rfl⟩ : syracuseStep 3693883 = 5540825) B5540825
theorem B4925177 : Blo 2187435 4925177 := bstep (se 2 (by rfl) ⟨1846941, by rfl⟩ : syracuseStep 4925177 = 3693883) B3693883
theorem B3283451 : Blo 2187435 3283451 := bstep (se 1 (by rfl) ⟨2462588, by rfl⟩ : syracuseStep 3283451 = 4925177) B4925177
theorem B2188967 : Blo 2187435 2188967 := bstep (se 1 (by rfl) ⟨1641725, by rfl⟩ : syracuseStep 2188967 = 3283451) B3283451
theorem B2462593 : Blo 2187435 2462593 := bbase (se 2 (by rfl) ⟨923472, by rfl⟩ : syracuseStep 2462593 = 1846945) (by norm_num)
theorem B3283457 : Blo 2187435 3283457 := bstep (se 2 (by rfl) ⟨1231296, by rfl⟩ : syracuseStep 3283457 = 2462593) B2462593
theorem B2188971 : Blo 2187435 2188971 := bstep (se 1 (by rfl) ⟨1641728, by rfl⟩ : syracuseStep 2188971 = 3283457) B3283457
theorem B5540845 : Blo 2187435 5540845 := bbase (se 3 (by rfl) ⟨1038908, by rfl⟩ : syracuseStep 5540845 = 2077817) (by norm_num)
theorem B7387793 : Blo 2187435 7387793 := bstep (se 2 (by rfl) ⟨2770422, by rfl⟩ : syracuseStep 7387793 = 5540845) B5540845
theorem B4925195 : Blo 2187435 4925195 := bstep (se 1 (by rfl) ⟨3693896, by rfl⟩ : syracuseStep 4925195 = 7387793) B7387793
theorem B3283463 : Blo 2187435 3283463 := bstep (se 1 (by rfl) ⟨2462597, by rfl⟩ : syracuseStep 3283463 = 4925195) B4925195
theorem B2188975 : Blo 2187435 2188975 := bstep (se 1 (by rfl) ⟨1641731, by rfl⟩ : syracuseStep 2188975 = 3283463) B3283463
theorem B3283469 : Blo 2187435 3283469 := bbase (se 3 (by rfl) ⟨615650, by rfl⟩ : syracuseStep 3283469 = 1231301) (by norm_num)
theorem B2188979 : Blo 2187435 2188979 := bstep (se 1 (by rfl) ⟨1641734, by rfl⟩ : syracuseStep 2188979 = 3283469) B3283469
theorem B4925213 : Blo 2187435 4925213 := bbase (se 3 (by rfl) ⟨923477, by rfl⟩ : syracuseStep 4925213 = 1846955) (by norm_num)
theorem B3283475 : Blo 2187435 3283475 := bstep (se 1 (by rfl) ⟨2462606, by rfl⟩ : syracuseStep 3283475 = 4925213) B4925213
theorem B2188983 : Blo 2187435 2188983 := bstep (se 1 (by rfl) ⟨1641737, by rfl⟩ : syracuseStep 2188983 = 3283475) B3283475
theorem B3693917 : Blo 2187435 3693917 := bbase (se 3 (by rfl) ⟨692609, by rfl⟩ : syracuseStep 3693917 = 1385219) (by norm_num)
theorem B2462611 : Blo 2187435 2462611 := bstep (se 1 (by rfl) ⟨1846958, by rfl⟩ : syracuseStep 2462611 = 3693917) B3693917
theorem B3283481 : Blo 2187435 3283481 := bstep (se 2 (by rfl) ⟨1231305, by rfl⟩ : syracuseStep 3283481 = 2462611) B2462611
theorem B2188987 : Blo 2187435 2188987 := bstep (se 1 (by rfl) ⟨1641740, by rfl⟩ : syracuseStep 2188987 = 3283481) B3283481
theorem B9350245 : Blo 2187435 9350245 := bbase (se 4 (by rfl) ⟨876585, by rfl⟩ : syracuseStep 9350245 = 1753171) (by norm_num)
theorem B12466993 : Blo 2187435 12466993 := bstep (se 2 (by rfl) ⟨4675122, by rfl⟩ : syracuseStep 12466993 = 9350245) B9350245
theorem B16622657 : Blo 2187435 16622657 := bstep (se 2 (by rfl) ⟨6233496, by rfl⟩ : syracuseStep 16622657 = 12466993) B12466993
theorem B11081771 : Blo 2187435 11081771 := bstep (se 1 (by rfl) ⟨8311328, by rfl⟩ : syracuseStep 11081771 = 16622657) B16622657
theorem B7387847 : Blo 2187435 7387847 := bstep (se 1 (by rfl) ⟨5540885, by rfl⟩ : syracuseStep 7387847 = 11081771) B11081771
theorem B4925231 : Blo 2187435 4925231 := bstep (se 1 (by rfl) ⟨3693923, by rfl⟩ : syracuseStep 4925231 = 7387847) B7387847
theorem B3283487 : Blo 2187435 3283487 := bstep (se 1 (by rfl) ⟨2462615, by rfl⟩ : syracuseStep 3283487 = 4925231) B4925231
theorem B2188991 : Blo 2187435 2188991 := bstep (se 1 (by rfl) ⟨1641743, by rfl⟩ : syracuseStep 2188991 = 3283487) B3283487
theorem B3283493 : Blo 2187435 3283493 := bbase (se 4 (by rfl) ⟨307827, by rfl⟩ : syracuseStep 3283493 = 615655) (by norm_num)
theorem B2188995 : Blo 2187435 2188995 := bstep (se 1 (by rfl) ⟨1641746, by rfl⟩ : syracuseStep 2188995 = 3283493) B3283493
theorem B2770453 : Blo 2187435 2770453 := bbase (se 6 (by rfl) ⟨64932, by rfl⟩ : syracuseStep 2770453 = 129865) (by norm_num)
theorem B3693937 : Blo 2187435 3693937 := bstep (se 2 (by rfl) ⟨1385226, by rfl⟩ : syracuseStep 3693937 = 2770453) B2770453
theorem B4925249 : Blo 2187435 4925249 := bstep (se 2 (by rfl) ⟨1846968, by rfl⟩ : syracuseStep 4925249 = 3693937) B3693937
theorem B3283499 : Blo 2187435 3283499 := bstep (se 1 (by rfl) ⟨2462624, by rfl⟩ : syracuseStep 3283499 = 4925249) B4925249
theorem B2188999 : Blo 2187435 2188999 := bstep (se 1 (by rfl) ⟨1641749, by rfl⟩ : syracuseStep 2188999 = 3283499) B3283499
theorem B2462629 : Blo 2187435 2462629 := bbase (se 4 (by rfl) ⟨230871, by rfl⟩ : syracuseStep 2462629 = 461743) (by norm_num)
theorem B3283505 : Blo 2187435 3283505 := bstep (se 2 (by rfl) ⟨1231314, by rfl⟩ : syracuseStep 3283505 = 2462629) B2462629
theorem B2189003 : Blo 2187435 2189003 := bstep (se 1 (by rfl) ⟨1641752, by rfl⟩ : syracuseStep 2189003 = 3283505) B3283505
theorem B5916997 : Blo 2187435 5916997 := bbase (se 4 (by rfl) ⟨554718, by rfl⟩ : syracuseStep 5916997 = 1109437) (by norm_num)
theorem B7889329 : Blo 2187435 7889329 := bstep (se 2 (by rfl) ⟨2958498, by rfl⟩ : syracuseStep 7889329 = 5916997) B5916997
theorem B10519105 : Blo 2187435 10519105 := bstep (se 2 (by rfl) ⟨3944664, by rfl⟩ : syracuseStep 10519105 = 7889329) B7889329
theorem B14025473 : Blo 2187435 14025473 := bstep (se 2 (by rfl) ⟨5259552, by rfl⟩ : syracuseStep 14025473 = 10519105) B10519105
theorem B9350315 : Blo 2187435 9350315 := bstep (se 1 (by rfl) ⟨7012736, by rfl⟩ : syracuseStep 9350315 = 14025473) B14025473
theorem B6233543 : Blo 2187435 6233543 := bstep (se 1 (by rfl) ⟨4675157, by rfl⟩ : syracuseStep 6233543 = 9350315) B9350315
theorem B4155695 : Blo 2187435 4155695 := bstep (se 1 (by rfl) ⟨3116771, by rfl⟩ : syracuseStep 4155695 = 6233543) B6233543
theorem B2770463 : Blo 2187435 2770463 := bstep (se 1 (by rfl) ⟨2077847, by rfl⟩ : syracuseStep 2770463 = 4155695) B4155695
theorem B7387901 : Blo 2187435 7387901 := bstep (se 3 (by rfl) ⟨1385231, by rfl⟩ : syracuseStep 7387901 = 2770463) B2770463
theorem B4925267 : Blo 2187435 4925267 := bstep (se 1 (by rfl) ⟨3693950, by rfl⟩ : syracuseStep 4925267 = 7387901) B7387901
theorem B3283511 : Blo 2187435 3283511 := bstep (se 1 (by rfl) ⟨2462633, by rfl⟩ : syracuseStep 3283511 = 4925267) B4925267
theorem B2189007 : Blo 2187435 2189007 := bstep (se 1 (by rfl) ⟨1641755, by rfl⟩ : syracuseStep 2189007 = 3283511) B3283511
theorem B3283517 : Blo 2187435 3283517 := bbase (se 3 (by rfl) ⟨615659, by rfl⟩ : syracuseStep 3283517 = 1231319) (by norm_num)
theorem B2189011 : Blo 2187435 2189011 := bstep (se 1 (by rfl) ⟨1641758, by rfl⟩ : syracuseStep 2189011 = 3283517) B3283517
theorem B4925285 : Blo 2187435 4925285 := bbase (se 4 (by rfl) ⟨461745, by rfl⟩ : syracuseStep 4925285 = 923491) (by norm_num)
theorem B3283523 : Blo 2187435 3283523 := bstep (se 1 (by rfl) ⟨2462642, by rfl⟩ : syracuseStep 3283523 = 4925285) B4925285
theorem B2189015 : Blo 2187435 2189015 := bstep (se 1 (by rfl) ⟨1641761, by rfl⟩ : syracuseStep 2189015 = 3283523) B3283523
theorem B5540957 : Blo 2187435 5540957 := bbase (se 3 (by rfl) ⟨1038929, by rfl⟩ : syracuseStep 5540957 = 2077859) (by norm_num)
theorem B3693971 : Blo 2187435 3693971 := bstep (se 1 (by rfl) ⟨2770478, by rfl⟩ : syracuseStep 3693971 = 5540957) B5540957
theorem B2462647 : Blo 2187435 2462647 := bstep (se 1 (by rfl) ⟨1846985, by rfl⟩ : syracuseStep 2462647 = 3693971) B3693971
theorem B3283529 : Blo 2187435 3283529 := bstep (se 2 (by rfl) ⟨1231323, by rfl⟩ : syracuseStep 3283529 = 2462647) B2462647
theorem B2189019 : Blo 2187435 2189019 := bstep (se 1 (by rfl) ⟨1641764, by rfl⟩ : syracuseStep 2189019 = 3283529) B3283529
theorem B4155725 : Blo 2187435 4155725 := bbase (se 3 (by rfl) ⟨779198, by rfl⟩ : syracuseStep 4155725 = 1558397) (by norm_num)
theorem B11081933 : Blo 2187435 11081933 := bstep (se 3 (by rfl) ⟨2077862, by rfl⟩ : syracuseStep 11081933 = 4155725) B4155725
theorem B7387955 : Blo 2187435 7387955 := bstep (se 1 (by rfl) ⟨5540966, by rfl⟩ : syracuseStep 7387955 = 11081933) B11081933
theorem B4925303 : Blo 2187435 4925303 := bstep (se 1 (by rfl) ⟨3693977, by rfl⟩ : syracuseStep 4925303 = 7387955) B7387955
theorem B3283535 : Blo 2187435 3283535 := bstep (se 1 (by rfl) ⟨2462651, by rfl⟩ : syracuseStep 3283535 = 4925303) B4925303
theorem B2189023 : Blo 2187435 2189023 := bstep (se 1 (by rfl) ⟨1641767, by rfl⟩ : syracuseStep 2189023 = 3283535) B3283535
theorem B3283541 : Blo 2187435 3283541 := bbase (se 8 (by rfl) ⟨19239, by rfl⟩ : syracuseStep 3283541 = 38479) (by norm_num)
theorem B2189027 : Blo 2187435 2189027 := bstep (se 1 (by rfl) ⟨1641770, by rfl⟩ : syracuseStep 2189027 = 3283541) B3283541
theorem B2629805 : Blo 2187435 2629805 := bbase (se 3 (by rfl) ⟨493088, by rfl⟩ : syracuseStep 2629805 = 986177) (by norm_num)
theorem B7012813 : Blo 2187435 7012813 := bstep (se 3 (by rfl) ⟨1314902, by rfl⟩ : syracuseStep 7012813 = 2629805) B2629805
theorem B9350417 : Blo 2187435 9350417 := bstep (se 2 (by rfl) ⟨3506406, by rfl⟩ : syracuseStep 9350417 = 7012813) B7012813
theorem B6233611 : Blo 2187435 6233611 := bstep (se 1 (by rfl) ⟨4675208, by rfl⟩ : syracuseStep 6233611 = 9350417) B9350417
theorem B8311481 : Blo 2187435 8311481 := bstep (se 2 (by rfl) ⟨3116805, by rfl⟩ : syracuseStep 8311481 = 6233611) B6233611
theorem B5540987 : Blo 2187435 5540987 := bstep (se 1 (by rfl) ⟨4155740, by rfl⟩ : syracuseStep 5540987 = 8311481) B8311481
theorem B3693991 : Blo 2187435 3693991 := bstep (se 1 (by rfl) ⟨2770493, by rfl⟩ : syracuseStep 3693991 = 5540987) B5540987
theorem B4925321 : Blo 2187435 4925321 := bstep (se 2 (by rfl) ⟨1846995, by rfl⟩ : syracuseStep 4925321 = 3693991) B3693991
theorem B3283547 : Blo 2187435 3283547 := bstep (se 1 (by rfl) ⟨2462660, by rfl⟩ : syracuseStep 3283547 = 4925321) B4925321
theorem B2189031 : Blo 2187435 2189031 := bstep (se 1 (by rfl) ⟨1641773, by rfl⟩ : syracuseStep 2189031 = 3283547) B3283547
theorem B2462665 : Blo 2187435 2462665 := bbase (se 2 (by rfl) ⟨923499, by rfl⟩ : syracuseStep 2462665 = 1846999) (by norm_num)
theorem B3283553 : Blo 2187435 3283553 := bstep (se 2 (by rfl) ⟨1231332, by rfl⟩ : syracuseStep 3283553 = 2462665) B2462665
theorem B2189035 : Blo 2187435 2189035 := bstep (se 1 (by rfl) ⟨1641776, by rfl⟩ : syracuseStep 2189035 = 3283553) B3283553
theorem B5259629 : Blo 2187435 5259629 := bbase (se 3 (by rfl) ⟨986180, by rfl⟩ : syracuseStep 5259629 = 1972361) (by norm_num)
theorem B3506419 : Blo 2187435 3506419 := bstep (se 1 (by rfl) ⟨2629814, by rfl⟩ : syracuseStep 3506419 = 5259629) B5259629
theorem B18700901 : Blo 2187435 18700901 := bstep (se 4 (by rfl) ⟨1753209, by rfl⟩ : syracuseStep 18700901 = 3506419) B3506419
theorem B12467267 : Blo 2187435 12467267 := bstep (se 1 (by rfl) ⟨9350450, by rfl⟩ : syracuseStep 12467267 = 18700901) B18700901
theorem B8311511 : Blo 2187435 8311511 := bstep (se 1 (by rfl) ⟨6233633, by rfl⟩ : syracuseStep 8311511 = 12467267) B12467267
theorem B5541007 : Blo 2187435 5541007 := bstep (se 1 (by rfl) ⟨4155755, by rfl⟩ : syracuseStep 5541007 = 8311511) B8311511
theorem B7388009 : Blo 2187435 7388009 := bstep (se 2 (by rfl) ⟨2770503, by rfl⟩ : syracuseStep 7388009 = 5541007) B5541007
theorem B4925339 : Blo 2187435 4925339 := bstep (se 1 (by rfl) ⟨3694004, by rfl⟩ : syracuseStep 4925339 = 7388009) B7388009
theorem B3283559 : Blo 2187435 3283559 := bstep (se 1 (by rfl) ⟨2462669, by rfl⟩ : syracuseStep 3283559 = 4925339) B4925339
theorem B2189039 : Blo 2187435 2189039 := bstep (se 1 (by rfl) ⟨1641779, by rfl⟩ : syracuseStep 2189039 = 3283559) B3283559
theorem B3283565 : Blo 2187435 3283565 := bbase (se 3 (by rfl) ⟨615668, by rfl⟩ : syracuseStep 3283565 = 1231337) (by norm_num)
theorem B2189043 : Blo 2187435 2189043 := bstep (se 1 (by rfl) ⟨1641782, by rfl⟩ : syracuseStep 2189043 = 3283565) B3283565
theorem B4925357 : Blo 2187435 4925357 := bbase (se 3 (by rfl) ⟨923504, by rfl⟩ : syracuseStep 4925357 = 1847009) (by norm_num)
theorem B3283571 : Blo 2187435 3283571 := bstep (se 1 (by rfl) ⟨2462678, by rfl⟩ : syracuseStep 3283571 = 4925357) B4925357
theorem B2189047 : Blo 2187435 2189047 := bstep (se 1 (by rfl) ⟨1641785, by rfl⟩ : syracuseStep 2189047 = 3283571) B3283571
theorem B6233669 : Blo 2187435 6233669 := bbase (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) (by norm_num)
theorem B4155779 : Blo 2187435 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B2770519 : Blo 2187435 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B3694025 : Blo 2187435 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B2462683 : Blo 2187435 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B3283577 : Blo 2187435 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B2189051 : Blo 2187435 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B42077333 : Blo 2187435 42077333 := bbase (se 6 (by rfl) ⟨986187, by rfl⟩ : syracuseStep 42077333 = 1972375) (by norm_num)
theorem B28051555 : Blo 2187435 28051555 := bstep (se 1 (by rfl) ⟨21038666, by rfl⟩ : syracuseStep 28051555 = 42077333) B42077333
theorem B37402073 : Blo 2187435 37402073 := bstep (se 2 (by rfl) ⟨14025777, by rfl⟩ : syracuseStep 37402073 = 28051555) B28051555
theorem B24934715 : Blo 2187435 24934715 := bstep (se 1 (by rfl) ⟨18701036, by rfl⟩ : syracuseStep 24934715 = 37402073) B37402073
theorem B16623143 : Blo 2187435 16623143 := bstep (se 1 (by rfl) ⟨12467357, by rfl⟩ : syracuseStep 16623143 = 24934715) B24934715
theorem B11082095 : Blo 2187435 11082095 := bstep (se 1 (by rfl) ⟨8311571, by rfl⟩ : syracuseStep 11082095 = 16623143) B16623143
theorem B7388063 : Blo 2187435 7388063 := bstep (se 1 (by rfl) ⟨5541047, by rfl⟩ : syracuseStep 7388063 = 11082095) B11082095
theorem B4925375 : Blo 2187435 4925375 := bstep (se 1 (by rfl) ⟨3694031, by rfl⟩ : syracuseStep 4925375 = 7388063) B7388063
theorem B3283583 : Blo 2187435 3283583 := bstep (se 1 (by rfl) ⟨2462687, by rfl⟩ : syracuseStep 3283583 = 4925375) B4925375
theorem B2189055 : Blo 2187435 2189055 := bstep (se 1 (by rfl) ⟨1641791, by rfl⟩ : syracuseStep 2189055 = 3283583) B3283583
theorem B3283589 : Blo 2187435 3283589 := bbase (se 4 (by rfl) ⟨307836, by rfl⟩ : syracuseStep 3283589 = 615673) (by norm_num)
theorem B2189059 : Blo 2187435 2189059 := bstep (se 1 (by rfl) ⟨1641794, by rfl⟩ : syracuseStep 2189059 = 3283589) B3283589
theorem B3694045 : Blo 2187435 3694045 := bbase (se 3 (by rfl) ⟨692633, by rfl⟩ : syracuseStep 3694045 = 1385267) (by norm_num)
theorem B4925393 : Blo 2187435 4925393 := bstep (se 2 (by rfl) ⟨1847022, by rfl⟩ : syracuseStep 4925393 = 3694045) B3694045
theorem B3283595 : Blo 2187435 3283595 := bstep (se 1 (by rfl) ⟨2462696, by rfl⟩ : syracuseStep 3283595 = 4925393) B4925393
theorem B2189063 : Blo 2187435 2189063 := bstep (se 1 (by rfl) ⟨1641797, by rfl⟩ : syracuseStep 2189063 = 3283595) B3283595
theorem B2462701 : Blo 2187435 2462701 := bbase (se 3 (by rfl) ⟨461756, by rfl⟩ : syracuseStep 2462701 = 923513) (by norm_num)
theorem B3283601 : Blo 2187435 3283601 := bstep (se 2 (by rfl) ⟨1231350, by rfl⟩ : syracuseStep 3283601 = 2462701) B2462701
theorem B2189067 : Blo 2187435 2189067 := bstep (se 1 (by rfl) ⟨1641800, by rfl⟩ : syracuseStep 2189067 = 3283601) B3283601
theorem B7388117 : Blo 2187435 7388117 := bbase (se 7 (by rfl) ⟨86579, by rfl⟩ : syracuseStep 7388117 = 173159) (by norm_num)
theorem B4925411 : Blo 2187435 4925411 := bstep (se 1 (by rfl) ⟨3694058, by rfl⟩ : syracuseStep 4925411 = 7388117) B7388117
theorem B3283607 : Blo 2187435 3283607 := bstep (se 1 (by rfl) ⟨2462705, by rfl⟩ : syracuseStep 3283607 = 4925411) B4925411
theorem B2189071 : Blo 2187435 2189071 := bstep (se 1 (by rfl) ⟨1641803, by rfl⟩ : syracuseStep 2189071 = 3283607) B3283607
theorem B3283613 : Blo 2187435 3283613 := bbase (se 3 (by rfl) ⟨615677, by rfl⟩ : syracuseStep 3283613 = 1231355) (by norm_num)
theorem B2189075 : Blo 2187435 2189075 := bstep (se 1 (by rfl) ⟨1641806, by rfl⟩ : syracuseStep 2189075 = 3283613) B3283613
theorem B4925429 : Blo 2187435 4925429 := bbase (se 5 (by rfl) ⟨230879, by rfl⟩ : syracuseStep 4925429 = 461759) (by norm_num)
theorem B3283619 : Blo 2187435 3283619 := bstep (se 1 (by rfl) ⟨2462714, by rfl⟩ : syracuseStep 3283619 = 4925429) B4925429
theorem B2189079 : Blo 2187435 2189079 := bstep (se 1 (by rfl) ⟨1641809, by rfl⟩ : syracuseStep 2189079 = 3283619) B3283619
theorem B13495349 : Blo 2187435 13495349 := bbase (se 5 (by rfl) ⟨632594, by rfl⟩ : syracuseStep 13495349 = 1265189) (by norm_num)
theorem B8996899 : Blo 2187435 8996899 := bstep (se 1 (by rfl) ⟨6747674, by rfl⟩ : syracuseStep 8996899 = 13495349) B13495349
theorem B11995865 : Blo 2187435 11995865 := bstep (se 2 (by rfl) ⟨4498449, by rfl⟩ : syracuseStep 11995865 = 8996899) B8996899
theorem B7997243 : Blo 2187435 7997243 := bstep (se 1 (by rfl) ⟨5997932, by rfl⟩ : syracuseStep 7997243 = 11995865) B11995865
theorem B85303925 : Blo 2187435 85303925 := bstep (se 5 (by rfl) ⟨3998621, by rfl⟩ : syracuseStep 85303925 = 7997243) B7997243
theorem B56869283 : Blo 2187435 56869283 := bstep (se 1 (by rfl) ⟨42651962, by rfl⟩ : syracuseStep 56869283 = 85303925) B85303925
theorem B37912855 : Blo 2187435 37912855 := bstep (se 1 (by rfl) ⟨28434641, by rfl⟩ : syracuseStep 37912855 = 56869283) B56869283
theorem B50550473 : Blo 2187435 50550473 := bstep (se 2 (by rfl) ⟨18956427, by rfl⟩ : syracuseStep 50550473 = 37912855) B37912855
theorem B33700315 : Blo 2187435 33700315 := bstep (se 1 (by rfl) ⟨25275236, by rfl⟩ : syracuseStep 33700315 = 50550473) B50550473
theorem B44933753 : Blo 2187435 44933753 := bstep (se 2 (by rfl) ⟨16850157, by rfl⟩ : syracuseStep 44933753 = 33700315) B33700315
theorem B29955835 : Blo 2187435 29955835 := bstep (se 1 (by rfl) ⟨22466876, by rfl⟩ : syracuseStep 29955835 = 44933753) B44933753
theorem B39941113 : Blo 2187435 39941113 := bstep (se 2 (by rfl) ⟨14977917, by rfl⟩ : syracuseStep 39941113 = 29955835) B29955835
theorem B53254817 : Blo 2187435 53254817 := bstep (se 2 (by rfl) ⟨19970556, by rfl⟩ : syracuseStep 53254817 = 39941113) B39941113
theorem B35503211 : Blo 2187435 35503211 := bstep (se 1 (by rfl) ⟨26627408, by rfl⟩ : syracuseStep 35503211 = 53254817) B53254817
theorem B94675229 : Blo 2187435 94675229 := bstep (se 3 (by rfl) ⟨17751605, by rfl⟩ : syracuseStep 94675229 = 35503211) B35503211
theorem B63116819 : Blo 2187435 63116819 := bstep (se 1 (by rfl) ⟨47337614, by rfl⟩ : syracuseStep 63116819 = 94675229) B94675229
theorem B42077879 : Blo 2187435 42077879 := bstep (se 1 (by rfl) ⟨31558409, by rfl⟩ : syracuseStep 42077879 = 63116819) B63116819
theorem B28051919 : Blo 2187435 28051919 := bstep (se 1 (by rfl) ⟨21038939, by rfl⟩ : syracuseStep 28051919 = 42077879) B42077879
theorem B18701279 : Blo 2187435 18701279 := bstep (se 1 (by rfl) ⟨14025959, by rfl⟩ : syracuseStep 18701279 = 28051919) B28051919
theorem B12467519 : Blo 2187435 12467519 := bstep (se 1 (by rfl) ⟨9350639, by rfl⟩ : syracuseStep 12467519 = 18701279) B18701279
theorem B8311679 : Blo 2187435 8311679 := bstep (se 1 (by rfl) ⟨6233759, by rfl⟩ : syracuseStep 8311679 = 12467519) B12467519
theorem B5541119 : Blo 2187435 5541119 := bstep (se 1 (by rfl) ⟨4155839, by rfl⟩ : syracuseStep 5541119 = 8311679) B8311679
theorem B3694079 : Blo 2187435 3694079 := bstep (se 1 (by rfl) ⟨2770559, by rfl⟩ : syracuseStep 3694079 = 5541119) B5541119
theorem B2462719 : Blo 2187435 2462719 := bstep (se 1 (by rfl) ⟨1847039, by rfl⟩ : syracuseStep 2462719 = 3694079) B3694079
theorem B3283625 : Blo 2187435 3283625 := bstep (se 2 (by rfl) ⟨1231359, by rfl⟩ : syracuseStep 3283625 = 2462719) B2462719
theorem B2189083 : Blo 2187435 2189083 := bstep (se 1 (by rfl) ⟨1641812, by rfl⟩ : syracuseStep 2189083 = 3283625) B3283625
theorem B3116885 : Blo 2187435 3116885 := bbase (se 9 (by rfl) ⟨9131, by rfl⟩ : syracuseStep 3116885 = 18263) (by norm_num)
theorem B8311693 : Blo 2187435 8311693 := bstep (se 3 (by rfl) ⟨1558442, by rfl⟩ : syracuseStep 8311693 = 3116885) B3116885
theorem B11082257 : Blo 2187435 11082257 := bstep (se 2 (by rfl) ⟨4155846, by rfl⟩ : syracuseStep 11082257 = 8311693) B8311693
theorem B7388171 : Blo 2187435 7388171 := bstep (se 1 (by rfl) ⟨5541128, by rfl⟩ : syracuseStep 7388171 = 11082257) B11082257
theorem B4925447 : Blo 2187435 4925447 := bstep (se 1 (by rfl) ⟨3694085, by rfl⟩ : syracuseStep 4925447 = 7388171) B7388171
theorem B3283631 : Blo 2187435 3283631 := bstep (se 1 (by rfl) ⟨2462723, by rfl⟩ : syracuseStep 3283631 = 4925447) B4925447
theorem B2189087 : Blo 2187435 2189087 := bstep (se 1 (by rfl) ⟨1641815, by rfl⟩ : syracuseStep 2189087 = 3283631) B3283631
theorem B3283637 : Blo 2187435 3283637 := bbase (se 5 (by rfl) ⟨153920, by rfl⟩ : syracuseStep 3283637 = 307841) (by norm_num)
theorem B2189091 : Blo 2187435 2189091 := bstep (se 1 (by rfl) ⟨1641818, by rfl⟩ : syracuseStep 2189091 = 3283637) B3283637
theorem B5541149 : Blo 2187435 5541149 := bbase (se 3 (by rfl) ⟨1038965, by rfl⟩ : syracuseStep 5541149 = 2077931) (by norm_num)
theorem B3694099 : Blo 2187435 3694099 := bstep (se 1 (by rfl) ⟨2770574, by rfl⟩ : syracuseStep 3694099 = 5541149) B5541149
theorem B4925465 : Blo 2187435 4925465 := bstep (se 2 (by rfl) ⟨1847049, by rfl⟩ : syracuseStep 4925465 = 3694099) B3694099
theorem B3283643 : Blo 2187435 3283643 := bstep (se 1 (by rfl) ⟨2462732, by rfl⟩ : syracuseStep 3283643 = 4925465) B4925465
theorem B2189095 : Blo 2187435 2189095 := bstep (se 1 (by rfl) ⟨1641821, by rfl⟩ : syracuseStep 2189095 = 3283643) B3283643
theorem B2462737 : Blo 2187435 2462737 := bbase (se 2 (by rfl) ⟨923526, by rfl⟩ : syracuseStep 2462737 = 1847053) (by norm_num)
theorem B3283649 : Blo 2187435 3283649 := bstep (se 2 (by rfl) ⟨1231368, by rfl⟩ : syracuseStep 3283649 = 2462737) B2462737
theorem B2189099 : Blo 2187435 2189099 := bstep (se 1 (by rfl) ⟨1641824, by rfl⟩ : syracuseStep 2189099 = 3283649) B3283649
theorem B4155877 : Blo 2187435 4155877 := bbase (se 4 (by rfl) ⟨389613, by rfl⟩ : syracuseStep 4155877 = 779227) (by norm_num)
theorem B5541169 : Blo 2187435 5541169 := bstep (se 2 (by rfl) ⟨2077938, by rfl⟩ : syracuseStep 5541169 = 4155877) B4155877
theorem B7388225 : Blo 2187435 7388225 := bstep (se 2 (by rfl) ⟨2770584, by rfl⟩ : syracuseStep 7388225 = 5541169) B5541169
theorem B4925483 : Blo 2187435 4925483 := bstep (se 1 (by rfl) ⟨3694112, by rfl⟩ : syracuseStep 4925483 = 7388225) B7388225
theorem B3283655 : Blo 2187435 3283655 := bstep (se 1 (by rfl) ⟨2462741, by rfl⟩ : syracuseStep 3283655 = 4925483) B4925483
theorem B2189103 : Blo 2187435 2189103 := bstep (se 1 (by rfl) ⟨1641827, by rfl⟩ : syracuseStep 2189103 = 3283655) B3283655
theorem B3283661 : Blo 2187435 3283661 := bbase (se 3 (by rfl) ⟨615686, by rfl⟩ : syracuseStep 3283661 = 1231373) (by norm_num)
theorem B2189107 : Blo 2187435 2189107 := bstep (se 1 (by rfl) ⟨1641830, by rfl⟩ : syracuseStep 2189107 = 3283661) B3283661
theorem B4925501 : Blo 2187435 4925501 := bbase (se 3 (by rfl) ⟨923531, by rfl⟩ : syracuseStep 4925501 = 1847063) (by norm_num)
theorem B3283667 : Blo 2187435 3283667 := bstep (se 1 (by rfl) ⟨2462750, by rfl⟩ : syracuseStep 3283667 = 4925501) B4925501
theorem B2189111 : Blo 2187435 2189111 := bstep (se 1 (by rfl) ⟨1641833, by rfl⟩ : syracuseStep 2189111 = 3283667) B3283667
theorem B3694133 : Blo 2187435 3694133 := bbase (se 5 (by rfl) ⟨173162, by rfl⟩ : syracuseStep 3694133 = 346325) (by norm_num)
theorem B2462755 : Blo 2187435 2462755 := bstep (se 1 (by rfl) ⟨1847066, by rfl⟩ : syracuseStep 2462755 = 3694133) B3694133
theorem B3283673 : Blo 2187435 3283673 := bstep (se 2 (by rfl) ⟨1231377, by rfl⟩ : syracuseStep 3283673 = 2462755) B2462755
theorem B2189115 : Blo 2187435 2189115 := bstep (se 1 (by rfl) ⟨1641836, by rfl⟩ : syracuseStep 2189115 = 3283673) B3283673
theorem B6233861 : Blo 2187435 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B16623629 : Blo 2187435 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B11082419 : Blo 2187435 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B7388279 : Blo 2187435 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B4925519 : Blo 2187435 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B3283679 : Blo 2187435 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B2189119 : Blo 2187435 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B3283685 : Blo 2187435 3283685 := bbase (se 4 (by rfl) ⟨307845, by rfl⟩ : syracuseStep 3283685 = 615691) (by norm_num)
theorem B2189123 : Blo 2187435 2189123 := bstep (se 1 (by rfl) ⟨1641842, by rfl⟩ : syracuseStep 2189123 = 3283685) B3283685
theorem B2629921 : Blo 2187435 2629921 := bbase (se 2 (by rfl) ⟨986220, by rfl⟩ : syracuseStep 2629921 = 1972441) (by norm_num)
theorem B3506561 : Blo 2187435 3506561 := bstep (se 2 (by rfl) ⟨1314960, by rfl⟩ : syracuseStep 3506561 = 2629921) B2629921
theorem B2337707 : Blo 2187435 2337707 := bstep (se 1 (by rfl) ⟨1753280, by rfl⟩ : syracuseStep 2337707 = 3506561) B3506561
theorem B6233885 : Blo 2187435 6233885 := bstep (se 3 (by rfl) ⟨1168853, by rfl⟩ : syracuseStep 6233885 = 2337707) B2337707
theorem B4155923 : Blo 2187435 4155923 := bstep (se 1 (by rfl) ⟨3116942, by rfl⟩ : syracuseStep 4155923 = 6233885) B6233885
theorem B2770615 : Blo 2187435 2770615 := bstep (se 1 (by rfl) ⟨2077961, by rfl⟩ : syracuseStep 2770615 = 4155923) B4155923
theorem B3694153 : Blo 2187435 3694153 := bstep (se 2 (by rfl) ⟨1385307, by rfl⟩ : syracuseStep 3694153 = 2770615) B2770615
theorem B4925537 : Blo 2187435 4925537 := bstep (se 2 (by rfl) ⟨1847076, by rfl⟩ : syracuseStep 4925537 = 3694153) B3694153
theorem B3283691 : Blo 2187435 3283691 := bstep (se 1 (by rfl) ⟨2462768, by rfl⟩ : syracuseStep 3283691 = 4925537) B4925537
theorem B2189127 : Blo 2187435 2189127 := bstep (se 1 (by rfl) ⟨1641845, by rfl⟩ : syracuseStep 2189127 = 3283691) B3283691
theorem B2462773 : Blo 2187435 2462773 := bbase (se 5 (by rfl) ⟨115442, by rfl⟩ : syracuseStep 2462773 = 230885) (by norm_num)
theorem B3283697 : Blo 2187435 3283697 := bstep (se 2 (by rfl) ⟨1231386, by rfl⟩ : syracuseStep 3283697 = 2462773) B2462773
theorem B2189131 : Blo 2187435 2189131 := bstep (se 1 (by rfl) ⟨1641848, by rfl⟩ : syracuseStep 2189131 = 3283697) B3283697
theorem B2770625 : Blo 2187435 2770625 := bbase (se 2 (by rfl) ⟨1038984, by rfl⟩ : syracuseStep 2770625 = 2077969) (by norm_num)
theorem B7388333 : Blo 2187435 7388333 := bstep (se 3 (by rfl) ⟨1385312, by rfl⟩ : syracuseStep 7388333 = 2770625) B2770625
theorem B4925555 : Blo 2187435 4925555 := bstep (se 1 (by rfl) ⟨3694166, by rfl⟩ : syracuseStep 4925555 = 7388333) B7388333
theorem B3283703 : Blo 2187435 3283703 := bstep (se 1 (by rfl) ⟨2462777, by rfl⟩ : syracuseStep 3283703 = 4925555) B4925555
theorem B2189135 : Blo 2187435 2189135 := bstep (se 1 (by rfl) ⟨1641851, by rfl⟩ : syracuseStep 2189135 = 3283703) B3283703
theorem B3283709 : Blo 2187435 3283709 := bbase (se 3 (by rfl) ⟨615695, by rfl⟩ : syracuseStep 3283709 = 1231391) (by norm_num)
theorem B2189139 : Blo 2187435 2189139 := bstep (se 1 (by rfl) ⟨1641854, by rfl⟩ : syracuseStep 2189139 = 3283709) B3283709
theorem B4925573 : Blo 2187435 4925573 := bbase (se 4 (by rfl) ⟨461772, by rfl⟩ : syracuseStep 4925573 = 923545) (by norm_num)
theorem B3283715 : Blo 2187435 3283715 := bstep (se 1 (by rfl) ⟨2462786, by rfl⟩ : syracuseStep 3283715 = 4925573) B4925573
theorem B2189143 : Blo 2187435 2189143 := bstep (se 1 (by rfl) ⟨1641857, by rfl⟩ : syracuseStep 2189143 = 3283715) B3283715
theorem B2629945 : Blo 2187435 2629945 := bbase (se 2 (by rfl) ⟨986229, by rfl⟩ : syracuseStep 2629945 = 1972459) (by norm_num)
theorem B3506593 : Blo 2187435 3506593 := bstep (se 2 (by rfl) ⟨1314972, by rfl⟩ : syracuseStep 3506593 = 2629945) B2629945
theorem B4675457 : Blo 2187435 4675457 := bstep (se 2 (by rfl) ⟨1753296, by rfl⟩ : syracuseStep 4675457 = 3506593) B3506593
theorem B3116971 : Blo 2187435 3116971 := bstep (se 1 (by rfl) ⟨2337728, by rfl⟩ : syracuseStep 3116971 = 4675457) B4675457
theorem B4155961 : Blo 2187435 4155961 := bstep (se 2 (by rfl) ⟨1558485, by rfl⟩ : syracuseStep 4155961 = 3116971) B3116971
theorem B5541281 : Blo 2187435 5541281 := bstep (se 2 (by rfl) ⟨2077980, by rfl⟩ : syracuseStep 5541281 = 4155961) B4155961
theorem B3694187 : Blo 2187435 3694187 := bstep (se 1 (by rfl) ⟨2770640, by rfl⟩ : syracuseStep 3694187 = 5541281) B5541281
theorem B2462791 : Blo 2187435 2462791 := bstep (se 1 (by rfl) ⟨1847093, by rfl⟩ : syracuseStep 2462791 = 3694187) B3694187
theorem B3283721 : Blo 2187435 3283721 := bstep (se 2 (by rfl) ⟨1231395, by rfl⟩ : syracuseStep 3283721 = 2462791) B2462791
theorem B2189147 : Blo 2187435 2189147 := bstep (se 1 (by rfl) ⟨1641860, by rfl⟩ : syracuseStep 2189147 = 3283721) B3283721
theorem B11082581 : Blo 2187435 11082581 := bbase (se 9 (by rfl) ⟨32468, by rfl⟩ : syracuseStep 11082581 = 64937) (by norm_num)
theorem B7388387 : Blo 2187435 7388387 := bstep (se 1 (by rfl) ⟨5541290, by rfl⟩ : syracuseStep 7388387 = 11082581) B11082581
theorem B4925591 : Blo 2187435 4925591 := bstep (se 1 (by rfl) ⟨3694193, by rfl⟩ : syracuseStep 4925591 = 7388387) B7388387
theorem B3283727 : Blo 2187435 3283727 := bstep (se 1 (by rfl) ⟨2462795, by rfl⟩ : syracuseStep 3283727 = 4925591) B4925591
theorem B2189151 : Blo 2187435 2189151 := bstep (se 1 (by rfl) ⟨1641863, by rfl⟩ : syracuseStep 2189151 = 3283727) B3283727
theorem B3283733 : Blo 2187435 3283733 := bbase (se 6 (by rfl) ⟨76962, by rfl⟩ : syracuseStep 3283733 = 153925) (by norm_num)
theorem B2189155 : Blo 2187435 2189155 := bstep (se 1 (by rfl) ⟨1641866, by rfl⟩ : syracuseStep 2189155 = 3283733) B3283733
theorem B17994421 : Blo 2187435 17994421 := bbase (se 5 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 17994421 = 1686977) (by norm_num)
theorem B23992561 : Blo 2187435 23992561 := bstep (se 2 (by rfl) ⟨8997210, by rfl⟩ : syracuseStep 23992561 = 17994421) B17994421
theorem B31990081 : Blo 2187435 31990081 := bstep (se 2 (by rfl) ⟨11996280, by rfl⟩ : syracuseStep 31990081 = 23992561) B23992561
theorem B42653441 : Blo 2187435 42653441 := bstep (se 2 (by rfl) ⟨15995040, by rfl⟩ : syracuseStep 42653441 = 31990081) B31990081
theorem B28435627 : Blo 2187435 28435627 := bstep (se 1 (by rfl) ⟨21326720, by rfl⟩ : syracuseStep 28435627 = 42653441) B42653441
theorem B37914169 : Blo 2187435 37914169 := bstep (se 2 (by rfl) ⟨14217813, by rfl⟩ : syracuseStep 37914169 = 28435627) B28435627
theorem B50552225 : Blo 2187435 50552225 := bstep (se 2 (by rfl) ⟨18957084, by rfl⟩ : syracuseStep 50552225 = 37914169) B37914169
theorem B33701483 : Blo 2187435 33701483 := bstep (se 1 (by rfl) ⟨25276112, by rfl⟩ : syracuseStep 33701483 = 50552225) B50552225
theorem B22467655 : Blo 2187435 22467655 := bstep (se 1 (by rfl) ⟨16850741, by rfl⟩ : syracuseStep 22467655 = 33701483) B33701483
theorem B29956873 : Blo 2187435 29956873 := bstep (se 2 (by rfl) ⟨11233827, by rfl⟩ : syracuseStep 29956873 = 22467655) B22467655
theorem B39942497 : Blo 2187435 39942497 := bstep (se 2 (by rfl) ⟨14978436, by rfl⟩ : syracuseStep 39942497 = 29956873) B29956873
theorem B106513325 : Blo 2187435 106513325 := bstep (se 3 (by rfl) ⟨19971248, by rfl⟩ : syracuseStep 106513325 = 39942497) B39942497
theorem B71008883 : Blo 2187435 71008883 := bstep (se 1 (by rfl) ⟨53256662, by rfl⟩ : syracuseStep 71008883 = 106513325) B106513325
theorem B47339255 : Blo 2187435 47339255 := bstep (se 1 (by rfl) ⟨35504441, by rfl⟩ : syracuseStep 47339255 = 71008883) B71008883
theorem B31559503 : Blo 2187435 31559503 := bstep (se 1 (by rfl) ⟨23669627, by rfl⟩ : syracuseStep 31559503 = 47339255) B47339255
theorem B42079337 : Blo 2187435 42079337 := bstep (se 2 (by rfl) ⟨15779751, by rfl⟩ : syracuseStep 42079337 = 31559503) B31559503
theorem B28052891 : Blo 2187435 28052891 := bstep (se 1 (by rfl) ⟨21039668, by rfl⟩ : syracuseStep 28052891 = 42079337) B42079337
theorem B18701927 : Blo 2187435 18701927 := bstep (se 1 (by rfl) ⟨14026445, by rfl⟩ : syracuseStep 18701927 = 28052891) B28052891
theorem B12467951 : Blo 2187435 12467951 := bstep (se 1 (by rfl) ⟨9350963, by rfl⟩ : syracuseStep 12467951 = 18701927) B18701927
theorem B8311967 : Blo 2187435 8311967 := bstep (se 1 (by rfl) ⟨6233975, by rfl⟩ : syracuseStep 8311967 = 12467951) B12467951
theorem B5541311 : Blo 2187435 5541311 := bstep (se 1 (by rfl) ⟨4155983, by rfl⟩ : syracuseStep 5541311 = 8311967) B8311967
theorem B3694207 : Blo 2187435 3694207 := bstep (se 1 (by rfl) ⟨2770655, by rfl⟩ : syracuseStep 3694207 = 5541311) B5541311
theorem B4925609 : Blo 2187435 4925609 := bstep (se 2 (by rfl) ⟨1847103, by rfl⟩ : syracuseStep 4925609 = 3694207) B3694207
theorem B3283739 : Blo 2187435 3283739 := bstep (se 1 (by rfl) ⟨2462804, by rfl⟩ : syracuseStep 3283739 = 4925609) B4925609
theorem B2189159 : Blo 2187435 2189159 := bstep (se 1 (by rfl) ⟨1641869, by rfl⟩ : syracuseStep 2189159 = 3283739) B3283739
theorem B2462809 : Blo 2187435 2462809 := bbase (se 2 (by rfl) ⟨923553, by rfl⟩ : syracuseStep 2462809 = 1847107) (by norm_num)
theorem B3283745 : Blo 2187435 3283745 := bstep (se 2 (by rfl) ⟨1231404, by rfl⟩ : syracuseStep 3283745 = 2462809) B2462809
theorem B2189163 : Blo 2187435 2189163 := bstep (se 1 (by rfl) ⟨1641872, by rfl⟩ : syracuseStep 2189163 = 3283745) B3283745
theorem B2808469 : Blo 2187435 2808469 := bbase (se 6 (by rfl) ⟨65823, by rfl⟩ : syracuseStep 2808469 = 131647) (by norm_num)
theorem B3744625 : Blo 2187435 3744625 := bstep (se 2 (by rfl) ⟨1404234, by rfl⟩ : syracuseStep 3744625 = 2808469) B2808469
theorem B4992833 : Blo 2187435 4992833 := bstep (se 2 (by rfl) ⟨1872312, by rfl⟩ : syracuseStep 4992833 = 3744625) B3744625
theorem B3328555 : Blo 2187435 3328555 := bstep (se 1 (by rfl) ⟨2496416, by rfl⟩ : syracuseStep 3328555 = 4992833) B4992833
theorem B4438073 : Blo 2187435 4438073 := bstep (se 2 (by rfl) ⟨1664277, by rfl⟩ : syracuseStep 4438073 = 3328555) B3328555
theorem B2958715 : Blo 2187435 2958715 := bstep (se 1 (by rfl) ⟨2219036, by rfl⟩ : syracuseStep 2958715 = 4438073) B4438073
theorem B3944953 : Blo 2187435 3944953 := bstep (se 2 (by rfl) ⟨1479357, by rfl⟩ : syracuseStep 3944953 = 2958715) B2958715
theorem B5259937 : Blo 2187435 5259937 := bstep (se 2 (by rfl) ⟨1972476, by rfl⟩ : syracuseStep 5259937 = 3944953) B3944953
theorem B7013249 : Blo 2187435 7013249 := bstep (se 2 (by rfl) ⟨2629968, by rfl⟩ : syracuseStep 7013249 = 5259937) B5259937
theorem B4675499 : Blo 2187435 4675499 := bstep (se 1 (by rfl) ⟨3506624, by rfl⟩ : syracuseStep 4675499 = 7013249) B7013249
theorem B3116999 : Blo 2187435 3116999 := bstep (se 1 (by rfl) ⟨2337749, by rfl⟩ : syracuseStep 3116999 = 4675499) B4675499
theorem B8311997 : Blo 2187435 8311997 := bstep (se 3 (by rfl) ⟨1558499, by rfl⟩ : syracuseStep 8311997 = 3116999) B3116999
theorem B5541331 : Blo 2187435 5541331 := bstep (se 1 (by rfl) ⟨4155998, by rfl⟩ : syracuseStep 5541331 = 8311997) B8311997
theorem B7388441 : Blo 2187435 7388441 := bstep (se 2 (by rfl) ⟨2770665, by rfl⟩ : syracuseStep 7388441 = 5541331) B5541331
theorem B4925627 : Blo 2187435 4925627 := bstep (se 1 (by rfl) ⟨3694220, by rfl⟩ : syracuseStep 4925627 = 7388441) B7388441
theorem B3283751 : Blo 2187435 3283751 := bstep (se 1 (by rfl) ⟨2462813, by rfl⟩ : syracuseStep 3283751 = 4925627) B4925627
theorem B2189167 : Blo 2187435 2189167 := bstep (se 1 (by rfl) ⟨1641875, by rfl⟩ : syracuseStep 2189167 = 3283751) B3283751
theorem B3283757 : Blo 2187435 3283757 := bbase (se 3 (by rfl) ⟨615704, by rfl⟩ : syracuseStep 3283757 = 1231409) (by norm_num)
theorem B2189171 : Blo 2187435 2189171 := bstep (se 1 (by rfl) ⟨1641878, by rfl⟩ : syracuseStep 2189171 = 3283757) B3283757
theorem B4925645 : Blo 2187435 4925645 := bbase (se 3 (by rfl) ⟨923558, by rfl⟩ : syracuseStep 4925645 = 1847117) (by norm_num)
theorem B3283763 : Blo 2187435 3283763 := bstep (se 1 (by rfl) ⟨2462822, by rfl⟩ : syracuseStep 3283763 = 4925645) B4925645
theorem B2189175 : Blo 2187435 2189175 := bstep (se 1 (by rfl) ⟨1641881, by rfl⟩ : syracuseStep 2189175 = 3283763) B3283763
theorem B2770681 : Blo 2187435 2770681 := bbase (se 2 (by rfl) ⟨1039005, by rfl⟩ : syracuseStep 2770681 = 2078011) (by norm_num)
theorem B3694241 : Blo 2187435 3694241 := bstep (se 2 (by rfl) ⟨1385340, by rfl⟩ : syracuseStep 3694241 = 2770681) B2770681
theorem B2462827 : Blo 2187435 2462827 := bstep (se 1 (by rfl) ⟨1847120, by rfl⟩ : syracuseStep 2462827 = 3694241) B3694241
theorem B3283769 : Blo 2187435 3283769 := bstep (se 2 (by rfl) ⟨1231413, by rfl⟩ : syracuseStep 3283769 = 2462827) B2462827
theorem B2189179 : Blo 2187435 2189179 := bstep (se 1 (by rfl) ⟨1641884, by rfl⟩ : syracuseStep 2189179 = 3283769) B3283769
theorem B3944981 : Blo 2187435 3944981 := bbase (se 6 (by rfl) ⟨92460, by rfl⟩ : syracuseStep 3944981 = 184921) (by norm_num)
theorem B10519949 : Blo 2187435 10519949 := bstep (se 3 (by rfl) ⟨1972490, by rfl⟩ : syracuseStep 10519949 = 3944981) B3944981
theorem B7013299 : Blo 2187435 7013299 := bstep (se 1 (by rfl) ⟨5259974, by rfl⟩ : syracuseStep 7013299 = 10519949) B10519949
theorem B9351065 : Blo 2187435 9351065 := bstep (se 2 (by rfl) ⟨3506649, by rfl⟩ : syracuseStep 9351065 = 7013299) B7013299
theorem B24936173 : Blo 2187435 24936173 := bstep (se 3 (by rfl) ⟨4675532, by rfl⟩ : syracuseStep 24936173 = 9351065) B9351065
theorem B16624115 : Blo 2187435 16624115 := bstep (se 1 (by rfl) ⟨12468086, by rfl⟩ : syracuseStep 16624115 = 24936173) B24936173
theorem B11082743 : Blo 2187435 11082743 := bstep (se 1 (by rfl) ⟨8312057, by rfl⟩ : syracuseStep 11082743 = 16624115) B16624115
theorem B7388495 : Blo 2187435 7388495 := bstep (se 1 (by rfl) ⟨5541371, by rfl⟩ : syracuseStep 7388495 = 11082743) B11082743
theorem B4925663 : Blo 2187435 4925663 := bstep (se 1 (by rfl) ⟨3694247, by rfl⟩ : syracuseStep 4925663 = 7388495) B7388495
theorem B3283775 : Blo 2187435 3283775 := bstep (se 1 (by rfl) ⟨2462831, by rfl⟩ : syracuseStep 3283775 = 4925663) B4925663
theorem B2189183 : Blo 2187435 2189183 := bstep (se 1 (by rfl) ⟨1641887, by rfl⟩ : syracuseStep 2189183 = 3283775) B3283775
theorem B3283781 : Blo 2187435 3283781 := bbase (se 4 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 3283781 = 615709) (by norm_num)
theorem B2189187 : Blo 2187435 2189187 := bstep (se 1 (by rfl) ⟨1641890, by rfl⟩ : syracuseStep 2189187 = 3283781) B3283781
theorem B3694261 : Blo 2187435 3694261 := bbase (se 5 (by rfl) ⟨173168, by rfl⟩ : syracuseStep 3694261 = 346337) (by norm_num)
theorem B4925681 : Blo 2187435 4925681 := bstep (se 2 (by rfl) ⟨1847130, by rfl⟩ : syracuseStep 4925681 = 3694261) B3694261
theorem B3283787 : Blo 2187435 3283787 := bstep (se 1 (by rfl) ⟨2462840, by rfl⟩ : syracuseStep 3283787 = 4925681) B4925681
theorem B2189191 : Blo 2187435 2189191 := bstep (se 1 (by rfl) ⟨1641893, by rfl⟩ : syracuseStep 2189191 = 3283787) B3283787
theorem B2462845 : Blo 2187435 2462845 := bbase (se 3 (by rfl) ⟨461783, by rfl⟩ : syracuseStep 2462845 = 923567) (by norm_num)
theorem B3283793 : Blo 2187435 3283793 := bstep (se 2 (by rfl) ⟨1231422, by rfl⟩ : syracuseStep 3283793 = 2462845) B2462845
theorem B2189195 : Blo 2187435 2189195 := bstep (se 1 (by rfl) ⟨1641896, by rfl⟩ : syracuseStep 2189195 = 3283793) B3283793
theorem B7388549 : Blo 2187435 7388549 := bbase (se 4 (by rfl) ⟨692676, by rfl⟩ : syracuseStep 7388549 = 1385353) (by norm_num)
theorem B4925699 : Blo 2187435 4925699 := bstep (se 1 (by rfl) ⟨3694274, by rfl⟩ : syracuseStep 4925699 = 7388549) B7388549
theorem B3283799 : Blo 2187435 3283799 := bstep (se 1 (by rfl) ⟨2462849, by rfl⟩ : syracuseStep 3283799 = 4925699) B4925699
theorem B2189199 : Blo 2187435 2189199 := bstep (se 1 (by rfl) ⟨1641899, by rfl⟩ : syracuseStep 2189199 = 3283799) B3283799
theorem B3283805 : Blo 2187435 3283805 := bbase (se 3 (by rfl) ⟨615713, by rfl⟩ : syracuseStep 3283805 = 1231427) (by norm_num)
theorem B2189203 : Blo 2187435 2189203 := bstep (se 1 (by rfl) ⟨1641902, by rfl⟩ : syracuseStep 2189203 = 3283805) B3283805
theorem B4925717 : Blo 2187435 4925717 := bbase (se 6 (by rfl) ⟨115446, by rfl⟩ : syracuseStep 4925717 = 230893) (by norm_num)
theorem B3283811 : Blo 2187435 3283811 := bstep (se 1 (by rfl) ⟨2462858, by rfl⟩ : syracuseStep 3283811 = 4925717) B4925717
theorem B2189207 : Blo 2187435 2189207 := bstep (se 1 (by rfl) ⟨1641905, by rfl⟩ : syracuseStep 2189207 = 3283811) B3283811
theorem B8312165 : Blo 2187435 8312165 := bbase (se 4 (by rfl) ⟨779265, by rfl⟩ : syracuseStep 8312165 = 1558531) (by norm_num)
theorem B5541443 : Blo 2187435 5541443 := bstep (se 1 (by rfl) ⟨4156082, by rfl⟩ : syracuseStep 5541443 = 8312165) B8312165
theorem B3694295 : Blo 2187435 3694295 := bstep (se 1 (by rfl) ⟨2770721, by rfl⟩ : syracuseStep 3694295 = 5541443) B5541443
theorem B2462863 : Blo 2187435 2462863 := bstep (se 1 (by rfl) ⟨1847147, by rfl⟩ : syracuseStep 2462863 = 3694295) B3694295
theorem B3283817 : Blo 2187435 3283817 := bstep (se 2 (by rfl) ⟨1231431, by rfl⟩ : syracuseStep 3283817 = 2462863) B2462863
theorem B2189211 : Blo 2187435 2189211 := bstep (se 1 (by rfl) ⟨1641908, by rfl⟩ : syracuseStep 2189211 = 3283817) B3283817
theorem B3506701 : Blo 2187435 3506701 := bbase (se 3 (by rfl) ⟨657506, by rfl⟩ : syracuseStep 3506701 = 1315013) (by norm_num)
theorem B4675601 : Blo 2187435 4675601 := bstep (se 2 (by rfl) ⟨1753350, by rfl⟩ : syracuseStep 4675601 = 3506701) B3506701
theorem B12468269 : Blo 2187435 12468269 := bstep (se 3 (by rfl) ⟨2337800, by rfl⟩ : syracuseStep 12468269 = 4675601) B4675601
theorem B8312179 : Blo 2187435 8312179 := bstep (se 1 (by rfl) ⟨6234134, by rfl⟩ : syracuseStep 8312179 = 12468269) B12468269
theorem B11082905 : Blo 2187435 11082905 := bstep (se 2 (by rfl) ⟨4156089, by rfl⟩ : syracuseStep 11082905 = 8312179) B8312179
theorem B7388603 : Blo 2187435 7388603 := bstep (se 1 (by rfl) ⟨5541452, by rfl⟩ : syracuseStep 7388603 = 11082905) B11082905
theorem B4925735 : Blo 2187435 4925735 := bstep (se 1 (by rfl) ⟨3694301, by rfl⟩ : syracuseStep 4925735 = 7388603) B7388603
theorem B3283823 : Blo 2187435 3283823 := bstep (se 1 (by rfl) ⟨2462867, by rfl⟩ : syracuseStep 3283823 = 4925735) B4925735
theorem B2189215 : Blo 2187435 2189215 := bstep (se 1 (by rfl) ⟨1641911, by rfl⟩ : syracuseStep 2189215 = 3283823) B3283823
theorem B3283829 : Blo 2187435 3283829 := bbase (se 5 (by rfl) ⟨153929, by rfl⟩ : syracuseStep 3283829 = 307859) (by norm_num)
theorem B2189219 : Blo 2187435 2189219 := bstep (se 1 (by rfl) ⟨1641914, by rfl⟩ : syracuseStep 2189219 = 3283829) B3283829
theorem B7013429 : Blo 2187435 7013429 := bbase (se 5 (by rfl) ⟨328754, by rfl⟩ : syracuseStep 7013429 = 657509) (by norm_num)
theorem B4675619 : Blo 2187435 4675619 := bstep (se 1 (by rfl) ⟨3506714, by rfl⟩ : syracuseStep 4675619 = 7013429) B7013429
theorem B3117079 : Blo 2187435 3117079 := bstep (se 1 (by rfl) ⟨2337809, by rfl⟩ : syracuseStep 3117079 = 4675619) B4675619
theorem B4156105 : Blo 2187435 4156105 := bstep (se 2 (by rfl) ⟨1558539, by rfl⟩ : syracuseStep 4156105 = 3117079) B3117079
theorem B5541473 : Blo 2187435 5541473 := bstep (se 2 (by rfl) ⟨2078052, by rfl⟩ : syracuseStep 5541473 = 4156105) B4156105
theorem B3694315 : Blo 2187435 3694315 := bstep (se 1 (by rfl) ⟨2770736, by rfl⟩ : syracuseStep 3694315 = 5541473) B5541473
theorem B4925753 : Blo 2187435 4925753 := bstep (se 2 (by rfl) ⟨1847157, by rfl⟩ : syracuseStep 4925753 = 3694315) B3694315
theorem B3283835 : Blo 2187435 3283835 := bstep (se 1 (by rfl) ⟨2462876, by rfl⟩ : syracuseStep 3283835 = 4925753) B4925753
theorem B2189223 : Blo 2187435 2189223 := bstep (se 1 (by rfl) ⟨1641917, by rfl⟩ : syracuseStep 2189223 = 3283835) B3283835
theorem B2462881 : Blo 2187435 2462881 := bbase (se 2 (by rfl) ⟨923580, by rfl⟩ : syracuseStep 2462881 = 1847161) (by norm_num)
theorem B3283841 : Blo 2187435 3283841 := bstep (se 2 (by rfl) ⟨1231440, by rfl⟩ : syracuseStep 3283841 = 2462881) B2462881
theorem B2189227 : Blo 2187435 2189227 := bstep (se 1 (by rfl) ⟨1641920, by rfl⟩ : syracuseStep 2189227 = 3283841) B3283841
theorem B5541493 : Blo 2187435 5541493 := bbase (se 5 (by rfl) ⟨259757, by rfl⟩ : syracuseStep 5541493 = 519515) (by norm_num)
theorem B7388657 : Blo 2187435 7388657 := bstep (se 2 (by rfl) ⟨2770746, by rfl⟩ : syracuseStep 7388657 = 5541493) B5541493
theorem B4925771 : Blo 2187435 4925771 := bstep (se 1 (by rfl) ⟨3694328, by rfl⟩ : syracuseStep 4925771 = 7388657) B7388657
theorem B3283847 : Blo 2187435 3283847 := bstep (se 1 (by rfl) ⟨2462885, by rfl⟩ : syracuseStep 3283847 = 4925771) B4925771
theorem B2189231 : Blo 2187435 2189231 := bstep (se 1 (by rfl) ⟨1641923, by rfl⟩ : syracuseStep 2189231 = 3283847) B3283847
theorem B3283853 : Blo 2187435 3283853 := bbase (se 3 (by rfl) ⟨615722, by rfl⟩ : syracuseStep 3283853 = 1231445) (by norm_num)
theorem B2189235 : Blo 2187435 2189235 := bstep (se 1 (by rfl) ⟨1641926, by rfl⟩ : syracuseStep 2189235 = 3283853) B3283853
theorem B4925789 : Blo 2187435 4925789 := bbase (se 3 (by rfl) ⟨923585, by rfl⟩ : syracuseStep 4925789 = 1847171) (by norm_num)
theorem B3283859 : Blo 2187435 3283859 := bstep (se 1 (by rfl) ⟨2462894, by rfl⟩ : syracuseStep 3283859 = 4925789) B4925789
theorem B2189239 : Blo 2187435 2189239 := bstep (se 1 (by rfl) ⟨1641929, by rfl⟩ : syracuseStep 2189239 = 3283859) B3283859
theorem B3694349 : Blo 2187435 3694349 := bbase (se 3 (by rfl) ⟨692690, by rfl⟩ : syracuseStep 3694349 = 1385381) (by norm_num)
theorem B2462899 : Blo 2187435 2462899 := bstep (se 1 (by rfl) ⟨1847174, by rfl⟩ : syracuseStep 2462899 = 3694349) B3694349
theorem B3283865 : Blo 2187435 3283865 := bstep (se 2 (by rfl) ⟨1231449, by rfl⟩ : syracuseStep 3283865 = 2462899) B2462899
theorem B2189243 : Blo 2187435 2189243 := bstep (se 1 (by rfl) ⟨1641932, by rfl⟩ : syracuseStep 2189243 = 3283865) B3283865
theorem B18702677 : Blo 2187435 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B12468451 : Blo 2187435 12468451 := bstep (se 1 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 12468451 = 18702677) B18702677
theorem B16624601 : Blo 2187435 16624601 := bstep (se 2 (by rfl) ⟨6234225, by rfl⟩ : syracuseStep 16624601 = 12468451) B12468451
theorem B11083067 : Blo 2187435 11083067 := bstep (se 1 (by rfl) ⟨8312300, by rfl⟩ : syracuseStep 11083067 = 16624601) B16624601
theorem B7388711 : Blo 2187435 7388711 := bstep (se 1 (by rfl) ⟨5541533, by rfl⟩ : syracuseStep 7388711 = 11083067) B11083067
theorem B4925807 : Blo 2187435 4925807 := bstep (se 1 (by rfl) ⟨3694355, by rfl⟩ : syracuseStep 4925807 = 7388711) B7388711
theorem B3283871 : Blo 2187435 3283871 := bstep (se 1 (by rfl) ⟨2462903, by rfl⟩ : syracuseStep 3283871 = 4925807) B4925807
theorem B2189247 : Blo 2187435 2189247 := bstep (se 1 (by rfl) ⟨1641935, by rfl⟩ : syracuseStep 2189247 = 3283871) B3283871
theorem B3283877 : Blo 2187435 3283877 := bbase (se 4 (by rfl) ⟨307863, by rfl⟩ : syracuseStep 3283877 = 615727) (by norm_num)
theorem B2189251 : Blo 2187435 2189251 := bstep (se 1 (by rfl) ⟨1641938, by rfl⟩ : syracuseStep 2189251 = 3283877) B3283877
theorem B2770777 : Blo 2187435 2770777 := bbase (se 2 (by rfl) ⟨1039041, by rfl⟩ : syracuseStep 2770777 = 2078083) (by norm_num)
theorem B3694369 : Blo 2187435 3694369 := bstep (se 2 (by rfl) ⟨1385388, by rfl⟩ : syracuseStep 3694369 = 2770777) B2770777
theorem B4925825 : Blo 2187435 4925825 := bstep (se 2 (by rfl) ⟨1847184, by rfl⟩ : syracuseStep 4925825 = 3694369) B3694369
theorem B3283883 : Blo 2187435 3283883 := bstep (se 1 (by rfl) ⟨2462912, by rfl⟩ : syracuseStep 3283883 = 4925825) B4925825
theorem B2189255 : Blo 2187435 2189255 := bstep (se 1 (by rfl) ⟨1641941, by rfl⟩ : syracuseStep 2189255 = 3283883) B3283883
theorem B2462917 : Blo 2187435 2462917 := bbase (se 4 (by rfl) ⟨230898, by rfl⟩ : syracuseStep 2462917 = 461797) (by norm_num)
theorem B3283889 : Blo 2187435 3283889 := bstep (se 2 (by rfl) ⟨1231458, by rfl⟩ : syracuseStep 3283889 = 2462917) B2462917
theorem B2189259 : Blo 2187435 2189259 := bstep (se 1 (by rfl) ⟨1641944, by rfl⟩ : syracuseStep 2189259 = 3283889) B3283889
theorem B4156181 : Blo 2187435 4156181 := bbase (se 6 (by rfl) ⟨97410, by rfl⟩ : syracuseStep 4156181 = 194821) (by norm_num)
theorem B2770787 : Blo 2187435 2770787 := bstep (se 1 (by rfl) ⟨2078090, by rfl⟩ : syracuseStep 2770787 = 4156181) B4156181
theorem B7388765 : Blo 2187435 7388765 := bstep (se 3 (by rfl) ⟨1385393, by rfl⟩ : syracuseStep 7388765 = 2770787) B2770787
theorem B4925843 : Blo 2187435 4925843 := bstep (se 1 (by rfl) ⟨3694382, by rfl⟩ : syracuseStep 4925843 = 7388765) B7388765
theorem B3283895 : Blo 2187435 3283895 := bstep (se 1 (by rfl) ⟨2462921, by rfl⟩ : syracuseStep 3283895 = 4925843) B4925843
theorem B2189263 : Blo 2187435 2189263 := bstep (se 1 (by rfl) ⟨1641947, by rfl⟩ : syracuseStep 2189263 = 3283895) B3283895
theorem B3283901 : Blo 2187435 3283901 := bbase (se 3 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 3283901 = 1231463) (by norm_num)
theorem B2189267 : Blo 2187435 2189267 := bstep (se 1 (by rfl) ⟨1641950, by rfl⟩ : syracuseStep 2189267 = 3283901) B3283901
theorem B4925861 : Blo 2187435 4925861 := bbase (se 4 (by rfl) ⟨461799, by rfl⟩ : syracuseStep 4925861 = 923599) (by norm_num)
theorem B3283907 : Blo 2187435 3283907 := bstep (se 1 (by rfl) ⟨2462930, by rfl⟩ : syracuseStep 3283907 = 4925861) B4925861
theorem B2189271 : Blo 2187435 2189271 := bstep (se 1 (by rfl) ⟨1641953, by rfl⟩ : syracuseStep 2189271 = 3283907) B3283907
theorem B5541605 : Blo 2187435 5541605 := bbase (se 4 (by rfl) ⟨519525, by rfl⟩ : syracuseStep 5541605 = 1039051) (by norm_num)
theorem B3694403 : Blo 2187435 3694403 := bstep (se 1 (by rfl) ⟨2770802, by rfl⟩ : syracuseStep 3694403 = 5541605) B5541605
theorem B2462935 : Blo 2187435 2462935 := bstep (se 1 (by rfl) ⟨1847201, by rfl⟩ : syracuseStep 2462935 = 3694403) B3694403
theorem B3283913 : Blo 2187435 3283913 := bstep (se 2 (by rfl) ⟨1231467, by rfl⟩ : syracuseStep 3283913 = 2462935) B2462935
theorem B2189275 : Blo 2187435 2189275 := bstep (se 1 (by rfl) ⟨1641956, by rfl⟩ : syracuseStep 2189275 = 3283913) B3283913
theorem B2337869 : Blo 2187435 2337869 := bbase (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) (by norm_num)
theorem B6234317 : Blo 2187435 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B4156211 : Blo 2187435 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B11083229 : Blo 2187435 11083229 := bstep (se 3 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 11083229 = 4156211) B4156211
theorem B7388819 : Blo 2187435 7388819 := bstep (se 1 (by rfl) ⟨5541614, by rfl⟩ : syracuseStep 7388819 = 11083229) B11083229
theorem B4925879 : Blo 2187435 4925879 := bstep (se 1 (by rfl) ⟨3694409, by rfl⟩ : syracuseStep 4925879 = 7388819) B7388819
theorem B3283919 : Blo 2187435 3283919 := bstep (se 1 (by rfl) ⟨2462939, by rfl⟩ : syracuseStep 3283919 = 4925879) B4925879
theorem B2189279 : Blo 2187435 2189279 := bstep (se 1 (by rfl) ⟨1641959, by rfl⟩ : syracuseStep 2189279 = 3283919) B3283919
theorem B3283925 : Blo 2187435 3283925 := bbase (se 7 (by rfl) ⟨38483, by rfl⟩ : syracuseStep 3283925 = 76967) (by norm_num)
theorem B2189283 : Blo 2187435 2189283 := bstep (se 1 (by rfl) ⟨1641962, by rfl⟩ : syracuseStep 2189283 = 3283925) B3283925
theorem B8312453 : Blo 2187435 8312453 := bbase (se 4 (by rfl) ⟨779292, by rfl⟩ : syracuseStep 8312453 = 1558585) (by norm_num)
theorem B5541635 : Blo 2187435 5541635 := bstep (se 1 (by rfl) ⟨4156226, by rfl⟩ : syracuseStep 5541635 = 8312453) B8312453
theorem B3694423 : Blo 2187435 3694423 := bstep (se 1 (by rfl) ⟨2770817, by rfl⟩ : syracuseStep 3694423 = 5541635) B5541635
theorem B4925897 : Blo 2187435 4925897 := bstep (se 2 (by rfl) ⟨1847211, by rfl⟩ : syracuseStep 4925897 = 3694423) B3694423
theorem B3283931 : Blo 2187435 3283931 := bstep (se 1 (by rfl) ⟨2462948, by rfl⟩ : syracuseStep 3283931 = 4925897) B4925897
theorem B2189287 : Blo 2187435 2189287 := bstep (se 1 (by rfl) ⟨1641965, by rfl⟩ : syracuseStep 2189287 = 3283931) B3283931
theorem B2462953 : Blo 2187435 2462953 := bbase (se 2 (by rfl) ⟨923607, by rfl⟩ : syracuseStep 2462953 = 1847215) (by norm_num)
theorem B3283937 : Blo 2187435 3283937 := bstep (se 2 (by rfl) ⟨1231476, by rfl⟩ : syracuseStep 3283937 = 2462953) B2462953
theorem B2189291 : Blo 2187435 2189291 := bstep (se 1 (by rfl) ⟨1641968, by rfl⟩ : syracuseStep 2189291 = 3283937) B3283937
theorem B12468725 : Blo 2187435 12468725 := bbase (se 5 (by rfl) ⟨584471, by rfl⟩ : syracuseStep 12468725 = 1168943) (by norm_num)
theorem B8312483 : Blo 2187435 8312483 := bstep (se 1 (by rfl) ⟨6234362, by rfl⟩ : syracuseStep 8312483 = 12468725) B12468725
theorem B5541655 : Blo 2187435 5541655 := bstep (se 1 (by rfl) ⟨4156241, by rfl⟩ : syracuseStep 5541655 = 8312483) B8312483
theorem B7388873 : Blo 2187435 7388873 := bstep (se 2 (by rfl) ⟨2770827, by rfl⟩ : syracuseStep 7388873 = 5541655) B5541655
theorem B4925915 : Blo 2187435 4925915 := bstep (se 1 (by rfl) ⟨3694436, by rfl⟩ : syracuseStep 4925915 = 7388873) B7388873
theorem B3283943 : Blo 2187435 3283943 := bstep (se 1 (by rfl) ⟨2462957, by rfl⟩ : syracuseStep 3283943 = 4925915) B4925915
theorem B2189295 : Blo 2187435 2189295 := bstep (se 1 (by rfl) ⟨1641971, by rfl⟩ : syracuseStep 2189295 = 3283943) B3283943
theorem B3283949 : Blo 2187435 3283949 := bbase (se 3 (by rfl) ⟨615740, by rfl⟩ : syracuseStep 3283949 = 1231481) (by norm_num)
theorem B2189299 : Blo 2187435 2189299 := bstep (se 1 (by rfl) ⟨1641974, by rfl⟩ : syracuseStep 2189299 = 3283949) B3283949
theorem B4925933 : Blo 2187435 4925933 := bbase (se 3 (by rfl) ⟨923612, by rfl⟩ : syracuseStep 4925933 = 1847225) (by norm_num)
theorem B3283955 : Blo 2187435 3283955 := bstep (se 1 (by rfl) ⟨2462966, by rfl⟩ : syracuseStep 3283955 = 4925933) B4925933
theorem B2189303 : Blo 2187435 2189303 := bstep (se 1 (by rfl) ⟨1641977, by rfl⟩ : syracuseStep 2189303 = 3283955) B3283955
theorem B10520549 : Blo 2187435 10520549 := bbase (se 4 (by rfl) ⟨986301, by rfl⟩ : syracuseStep 10520549 = 1972603) (by norm_num)
theorem B7013699 : Blo 2187435 7013699 := bstep (se 1 (by rfl) ⟨5260274, by rfl⟩ : syracuseStep 7013699 = 10520549) B10520549
theorem B4675799 : Blo 2187435 4675799 := bstep (se 1 (by rfl) ⟨3506849, by rfl⟩ : syracuseStep 4675799 = 7013699) B7013699
theorem B3117199 : Blo 2187435 3117199 := bstep (se 1 (by rfl) ⟨2337899, by rfl⟩ : syracuseStep 3117199 = 4675799) B4675799
theorem B4156265 : Blo 2187435 4156265 := bstep (se 2 (by rfl) ⟨1558599, by rfl⟩ : syracuseStep 4156265 = 3117199) B3117199
theorem B2770843 : Blo 2187435 2770843 := bstep (se 1 (by rfl) ⟨2078132, by rfl⟩ : syracuseStep 2770843 = 4156265) B4156265
theorem B3694457 : Blo 2187435 3694457 := bstep (se 2 (by rfl) ⟨1385421, by rfl⟩ : syracuseStep 3694457 = 2770843) B2770843
theorem B2462971 : Blo 2187435 2462971 := bstep (se 1 (by rfl) ⟨1847228, by rfl⟩ : syracuseStep 2462971 = 3694457) B3694457
theorem B3283961 : Blo 2187435 3283961 := bstep (se 2 (by rfl) ⟨1231485, by rfl⟩ : syracuseStep 3283961 = 2462971) B2462971
theorem B2189307 : Blo 2187435 2189307 := bstep (se 1 (by rfl) ⟨1641980, by rfl⟩ : syracuseStep 2189307 = 3283961) B3283961
theorem B4007405 : Blo 2187435 4007405 := bbase (se 3 (by rfl) ⟨751388, by rfl⟩ : syracuseStep 4007405 = 1502777) (by norm_num)
theorem B2671603 : Blo 2187435 2671603 := bstep (se 1 (by rfl) ⟨2003702, by rfl⟩ : syracuseStep 2671603 = 4007405) B4007405
theorem B14248549 : Blo 2187435 14248549 := bstep (se 4 (by rfl) ⟨1335801, by rfl⟩ : syracuseStep 14248549 = 2671603) B2671603
theorem B18998065 : Blo 2187435 18998065 := bstep (se 2 (by rfl) ⟨7124274, by rfl⟩ : syracuseStep 18998065 = 14248549) B14248549
theorem B25330753 : Blo 2187435 25330753 := bstep (se 2 (by rfl) ⟨9499032, by rfl⟩ : syracuseStep 25330753 = 18998065) B18998065
theorem B33774337 : Blo 2187435 33774337 := bstep (se 2 (by rfl) ⟨12665376, by rfl⟩ : syracuseStep 33774337 = 25330753) B25330753
theorem B45032449 : Blo 2187435 45032449 := bstep (se 2 (by rfl) ⟨16887168, by rfl⟩ : syracuseStep 45032449 = 33774337) B33774337
theorem B60043265 : Blo 2187435 60043265 := bstep (se 2 (by rfl) ⟨22516224, by rfl⟩ : syracuseStep 60043265 = 45032449) B45032449
theorem B40028843 : Blo 2187435 40028843 := bstep (se 1 (by rfl) ⟨30021632, by rfl⟩ : syracuseStep 40028843 = 60043265) B60043265
theorem B26685895 : Blo 2187435 26685895 := bstep (se 1 (by rfl) ⟨20014421, by rfl⟩ : syracuseStep 26685895 = 40028843) B40028843
theorem B35581193 : Blo 2187435 35581193 := bstep (se 2 (by rfl) ⟨13342947, by rfl⟩ : syracuseStep 35581193 = 26685895) B26685895
theorem B23720795 : Blo 2187435 23720795 := bstep (se 1 (by rfl) ⟨17790596, by rfl⟩ : syracuseStep 23720795 = 35581193) B35581193
theorem B15813863 : Blo 2187435 15813863 := bstep (se 1 (by rfl) ⟨11860397, by rfl⟩ : syracuseStep 15813863 = 23720795) B23720795
theorem B10542575 : Blo 2187435 10542575 := bstep (se 1 (by rfl) ⟨7906931, by rfl⟩ : syracuseStep 10542575 = 15813863) B15813863
theorem B7028383 : Blo 2187435 7028383 := bstep (se 1 (by rfl) ⟨5271287, by rfl⟩ : syracuseStep 7028383 = 10542575) B10542575
theorem B9371177 : Blo 2187435 9371177 := bstep (se 2 (by rfl) ⟨3514191, by rfl⟩ : syracuseStep 9371177 = 7028383) B7028383
theorem B6247451 : Blo 2187435 6247451 := bstep (se 1 (by rfl) ⟨4685588, by rfl⟩ : syracuseStep 6247451 = 9371177) B9371177
theorem B4164967 : Blo 2187435 4164967 := bstep (se 1 (by rfl) ⟨3123725, by rfl⟩ : syracuseStep 4164967 = 6247451) B6247451
theorem B5553289 : Blo 2187435 5553289 := bstep (se 2 (by rfl) ⟨2082483, by rfl⟩ : syracuseStep 5553289 = 4164967) B4164967
theorem B7404385 : Blo 2187435 7404385 := bstep (se 2 (by rfl) ⟨2776644, by rfl⟩ : syracuseStep 7404385 = 5553289) B5553289
theorem B9872513 : Blo 2187435 9872513 := bstep (se 2 (by rfl) ⟨3702192, by rfl⟩ : syracuseStep 9872513 = 7404385) B7404385
theorem B6581675 : Blo 2187435 6581675 := bstep (se 1 (by rfl) ⟨4936256, by rfl⟩ : syracuseStep 6581675 = 9872513) B9872513
theorem B4387783 : Blo 2187435 4387783 := bstep (se 1 (by rfl) ⟨3290837, by rfl⟩ : syracuseStep 4387783 = 6581675) B6581675
theorem B5850377 : Blo 2187435 5850377 := bstep (se 2 (by rfl) ⟨2193891, by rfl⟩ : syracuseStep 5850377 = 4387783) B4387783
theorem B3900251 : Blo 2187435 3900251 := bstep (se 1 (by rfl) ⟨2925188, by rfl⟩ : syracuseStep 3900251 = 5850377) B5850377
theorem B2600167 : Blo 2187435 2600167 := bstep (se 1 (by rfl) ⟨1950125, by rfl⟩ : syracuseStep 2600167 = 3900251) B3900251
theorem B3466889 : Blo 2187435 3466889 := bstep (se 2 (by rfl) ⟨1300083, by rfl⟩ : syracuseStep 3466889 = 2600167) B2600167
theorem B2311259 : Blo 2187435 2311259 := bstep (se 1 (by rfl) ⟨1733444, by rfl⟩ : syracuseStep 2311259 = 3466889) B3466889
theorem B24653429 : Blo 2187435 24653429 := bstep (se 5 (by rfl) ⟨1155629, by rfl⟩ : syracuseStep 24653429 = 2311259) B2311259
theorem B16435619 : Blo 2187435 16435619 := bstep (se 1 (by rfl) ⟨12326714, by rfl⟩ : syracuseStep 16435619 = 24653429) B24653429
theorem B10957079 : Blo 2187435 10957079 := bstep (se 1 (by rfl) ⟨8217809, by rfl⟩ : syracuseStep 10957079 = 16435619) B16435619
theorem B29218877 : Blo 2187435 29218877 := bstep (se 3 (by rfl) ⟨5478539, by rfl⟩ : syracuseStep 29218877 = 10957079) B10957079
theorem B19479251 : Blo 2187435 19479251 := bstep (se 1 (by rfl) ⟨14609438, by rfl⟩ : syracuseStep 19479251 = 29218877) B29218877
theorem B12986167 : Blo 2187435 12986167 := bstep (se 1 (by rfl) ⟨9739625, by rfl⟩ : syracuseStep 12986167 = 19479251) B19479251
theorem B17314889 : Blo 2187435 17314889 := bstep (se 2 (by rfl) ⟨6493083, by rfl⟩ : syracuseStep 17314889 = 12986167) B12986167
theorem B46173037 : Blo 2187435 46173037 := bstep (se 3 (by rfl) ⟨8657444, by rfl⟩ : syracuseStep 46173037 = 17314889) B17314889
theorem B61564049 : Blo 2187435 61564049 := bstep (se 2 (by rfl) ⟨23086518, by rfl⟩ : syracuseStep 61564049 = 46173037) B46173037
theorem B41042699 : Blo 2187435 41042699 := bstep (se 1 (by rfl) ⟨30782024, by rfl⟩ : syracuseStep 41042699 = 61564049) B61564049
theorem B27361799 : Blo 2187435 27361799 := bstep (se 1 (by rfl) ⟨20521349, by rfl⟩ : syracuseStep 27361799 = 41042699) B41042699
theorem B18241199 : Blo 2187435 18241199 := bstep (se 1 (by rfl) ⟨13680899, by rfl⟩ : syracuseStep 18241199 = 27361799) B27361799
theorem B12160799 : Blo 2187435 12160799 := bstep (se 1 (by rfl) ⟨9120599, by rfl⟩ : syracuseStep 12160799 = 18241199) B18241199
theorem B8107199 : Blo 2187435 8107199 := bstep (se 1 (by rfl) ⟨6080399, by rfl⟩ : syracuseStep 8107199 = 12160799) B12160799
theorem B5404799 : Blo 2187435 5404799 := bstep (se 1 (by rfl) ⟨4053599, by rfl⟩ : syracuseStep 5404799 = 8107199) B8107199
theorem B3603199 : Blo 2187435 3603199 := bstep (se 1 (by rfl) ⟨2702399, by rfl⟩ : syracuseStep 3603199 = 5404799) B5404799
theorem B4804265 : Blo 2187435 4804265 := bstep (se 2 (by rfl) ⟨1801599, by rfl⟩ : syracuseStep 4804265 = 3603199) B3603199
theorem B3202843 : Blo 2187435 3202843 := bstep (se 1 (by rfl) ⟨2402132, by rfl⟩ : syracuseStep 3202843 = 4804265) B4804265
theorem B4270457 : Blo 2187435 4270457 := bstep (se 2 (by rfl) ⟨1601421, by rfl⟩ : syracuseStep 4270457 = 3202843) B3202843
theorem B2846971 : Blo 2187435 2846971 := bstep (se 1 (by rfl) ⟨2135228, by rfl⟩ : syracuseStep 2846971 = 4270457) B4270457
theorem B15183845 : Blo 2187435 15183845 := bstep (se 4 (by rfl) ⟨1423485, by rfl⟩ : syracuseStep 15183845 = 2846971) B2846971
theorem B10122563 : Blo 2187435 10122563 := bstep (se 1 (by rfl) ⟨7591922, by rfl⟩ : syracuseStep 10122563 = 15183845) B15183845
theorem B26993501 : Blo 2187435 26993501 := bstep (se 3 (by rfl) ⟨5061281, by rfl⟩ : syracuseStep 26993501 = 10122563) B10122563
theorem B17995667 : Blo 2187435 17995667 := bstep (se 1 (by rfl) ⟨13496750, by rfl⟩ : syracuseStep 17995667 = 26993501) B26993501
theorem B47988445 : Blo 2187435 47988445 := bstep (se 3 (by rfl) ⟨8997833, by rfl⟩ : syracuseStep 47988445 = 17995667) B17995667
theorem B63984593 : Blo 2187435 63984593 := bstep (se 2 (by rfl) ⟨23994222, by rfl⟩ : syracuseStep 63984593 = 47988445) B47988445
theorem B42656395 : Blo 2187435 42656395 := bstep (se 1 (by rfl) ⟨31992296, by rfl⟩ : syracuseStep 42656395 = 63984593) B63984593
theorem B56875193 : Blo 2187435 56875193 := bstep (se 2 (by rfl) ⟨21328197, by rfl⟩ : syracuseStep 56875193 = 42656395) B42656395
theorem B37916795 : Blo 2187435 37916795 := bstep (se 1 (by rfl) ⟨28437596, by rfl⟩ : syracuseStep 37916795 = 56875193) B56875193
theorem B101111453 : Blo 2187435 101111453 := bstep (se 3 (by rfl) ⟨18958397, by rfl⟩ : syracuseStep 101111453 = 37916795) B37916795
theorem B67407635 : Blo 2187435 67407635 := bstep (se 1 (by rfl) ⟨50555726, by rfl⟩ : syracuseStep 67407635 = 101111453) B101111453
theorem B44938423 : Blo 2187435 44938423 := bstep (se 1 (by rfl) ⟨33703817, by rfl⟩ : syracuseStep 44938423 = 67407635) B67407635
theorem B59917897 : Blo 2187435 59917897 := bstep (se 2 (by rfl) ⟨22469211, by rfl⟩ : syracuseStep 59917897 = 44938423) B44938423
theorem B319562117 : Blo 2187435 319562117 := bstep (se 4 (by rfl) ⟨29958948, by rfl⟩ : syracuseStep 319562117 = 59917897) B59917897
theorem B213041411 : Blo 2187435 213041411 := bstep (se 1 (by rfl) ⟨159781058, by rfl⟩ : syracuseStep 213041411 = 319562117) B319562117
theorem B142027607 : Blo 2187435 142027607 := bstep (se 1 (by rfl) ⟨106520705, by rfl⟩ : syracuseStep 142027607 = 213041411) B213041411
theorem B94685071 : Blo 2187435 94685071 := bstep (se 1 (by rfl) ⟨71013803, by rfl⟩ : syracuseStep 94685071 = 142027607) B142027607
theorem B126246761 : Blo 2187435 126246761 := bstep (se 2 (by rfl) ⟨47342535, by rfl⟩ : syracuseStep 126246761 = 94685071) B94685071
theorem B84164507 : Blo 2187435 84164507 := bstep (se 1 (by rfl) ⟨63123380, by rfl⟩ : syracuseStep 84164507 = 126246761) B126246761
theorem B56109671 : Blo 2187435 56109671 := bstep (se 1 (by rfl) ⟨42082253, by rfl⟩ : syracuseStep 56109671 = 84164507) B84164507
theorem B37406447 : Blo 2187435 37406447 := bstep (se 1 (by rfl) ⟨28054835, by rfl⟩ : syracuseStep 37406447 = 56109671) B56109671
theorem B24937631 : Blo 2187435 24937631 := bstep (se 1 (by rfl) ⟨18703223, by rfl⟩ : syracuseStep 24937631 = 37406447) B37406447
theorem B16625087 : Blo 2187435 16625087 := bstep (se 1 (by rfl) ⟨12468815, by rfl⟩ : syracuseStep 16625087 = 24937631) B24937631
theorem B11083391 : Blo 2187435 11083391 := bstep (se 1 (by rfl) ⟨8312543, by rfl⟩ : syracuseStep 11083391 = 16625087) B16625087
theorem B7388927 : Blo 2187435 7388927 := bstep (se 1 (by rfl) ⟨5541695, by rfl⟩ : syracuseStep 7388927 = 11083391) B11083391
theorem B4925951 : Blo 2187435 4925951 := bstep (se 1 (by rfl) ⟨3694463, by rfl⟩ : syracuseStep 4925951 = 7388927) B7388927
theorem B3283967 : Blo 2187435 3283967 := bstep (se 1 (by rfl) ⟨2462975, by rfl⟩ : syracuseStep 3283967 = 4925951) B4925951
theorem B2189311 : Blo 2187435 2189311 := bstep (se 1 (by rfl) ⟨1641983, by rfl⟩ : syracuseStep 2189311 = 3283967) B3283967
theorem B3283973 : Blo 2187435 3283973 := bbase (se 4 (by rfl) ⟨307872, by rfl⟩ : syracuseStep 3283973 = 615745) (by norm_num)
theorem B2189315 : Blo 2187435 2189315 := bstep (se 1 (by rfl) ⟨1641986, by rfl⟩ : syracuseStep 2189315 = 3283973) B3283973
theorem B3694477 : Blo 2187435 3694477 := bbase (se 3 (by rfl) ⟨692714, by rfl⟩ : syracuseStep 3694477 = 1385429) (by norm_num)
theorem B4925969 : Blo 2187435 4925969 := bstep (se 2 (by rfl) ⟨1847238, by rfl⟩ : syracuseStep 4925969 = 3694477) B3694477
theorem B3283979 : Blo 2187435 3283979 := bstep (se 1 (by rfl) ⟨2462984, by rfl⟩ : syracuseStep 3283979 = 4925969) B4925969
theorem B2189319 : Blo 2187435 2189319 := bstep (se 1 (by rfl) ⟨1641989, by rfl⟩ : syracuseStep 2189319 = 3283979) B3283979
theorem B2462989 : Blo 2187435 2462989 := bbase (se 3 (by rfl) ⟨461810, by rfl⟩ : syracuseStep 2462989 = 923621) (by norm_num)
theorem B3283985 : Blo 2187435 3283985 := bstep (se 2 (by rfl) ⟨1231494, by rfl⟩ : syracuseStep 3283985 = 2462989) B2462989
theorem B2189323 : Blo 2187435 2189323 := bstep (se 1 (by rfl) ⟨1641992, by rfl⟩ : syracuseStep 2189323 = 3283985) B3283985
theorem B7388981 : Blo 2187435 7388981 := bbase (se 5 (by rfl) ⟨346358, by rfl⟩ : syracuseStep 7388981 = 692717) (by norm_num)
theorem B4925987 : Blo 2187435 4925987 := bstep (se 1 (by rfl) ⟨3694490, by rfl⟩ : syracuseStep 4925987 = 7388981) B7388981
theorem B3283991 : Blo 2187435 3283991 := bstep (se 1 (by rfl) ⟨2462993, by rfl⟩ : syracuseStep 3283991 = 4925987) B4925987
theorem B2189327 : Blo 2187435 2189327 := bstep (se 1 (by rfl) ⟨1641995, by rfl⟩ : syracuseStep 2189327 = 3283991) B3283991
theorem B3283997 : Blo 2187435 3283997 := bbase (se 3 (by rfl) ⟨615749, by rfl⟩ : syracuseStep 3283997 = 1231499) (by norm_num)
theorem B2189331 : Blo 2187435 2189331 := bstep (se 1 (by rfl) ⟨1641998, by rfl⟩ : syracuseStep 2189331 = 3283997) B3283997
theorem B4926005 : Blo 2187435 4926005 := bbase (se 5 (by rfl) ⟨230906, by rfl⟩ : syracuseStep 4926005 = 461813) (by norm_num)
theorem B3284003 : Blo 2187435 3284003 := bstep (se 1 (by rfl) ⟨2463002, by rfl⟩ : syracuseStep 3284003 = 4926005) B4926005
theorem B2189335 : Blo 2187435 2189335 := bstep (se 1 (by rfl) ⟨1642001, by rfl⟩ : syracuseStep 2189335 = 3284003) B3284003
theorem B9351733 : Blo 2187435 9351733 := bbase (se 5 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 9351733 = 876725) (by norm_num)
theorem B12468977 : Blo 2187435 12468977 := bstep (se 2 (by rfl) ⟨4675866, by rfl⟩ : syracuseStep 12468977 = 9351733) B9351733
theorem B8312651 : Blo 2187435 8312651 := bstep (se 1 (by rfl) ⟨6234488, by rfl⟩ : syracuseStep 8312651 = 12468977) B12468977
theorem B5541767 : Blo 2187435 5541767 := bstep (se 1 (by rfl) ⟨4156325, by rfl⟩ : syracuseStep 5541767 = 8312651) B8312651
theorem B3694511 : Blo 2187435 3694511 := bstep (se 1 (by rfl) ⟨2770883, by rfl⟩ : syracuseStep 3694511 = 5541767) B5541767
theorem B2463007 : Blo 2187435 2463007 := bstep (se 1 (by rfl) ⟨1847255, by rfl⟩ : syracuseStep 2463007 = 3694511) B3694511
theorem B3284009 : Blo 2187435 3284009 := bstep (se 2 (by rfl) ⟨1231503, by rfl⟩ : syracuseStep 3284009 = 2463007) B2463007
theorem B2189339 : Blo 2187435 2189339 := bstep (se 1 (by rfl) ⟨1642004, by rfl⟩ : syracuseStep 2189339 = 3284009) B3284009
theorem B9351749 : Blo 2187435 9351749 := bbase (se 4 (by rfl) ⟨876726, by rfl⟩ : syracuseStep 9351749 = 1753453) (by norm_num)
theorem B6234499 : Blo 2187435 6234499 := bstep (se 1 (by rfl) ⟨4675874, by rfl⟩ : syracuseStep 6234499 = 9351749) B9351749
theorem B8312665 : Blo 2187435 8312665 := bstep (se 2 (by rfl) ⟨3117249, by rfl⟩ : syracuseStep 8312665 = 6234499) B6234499
theorem B11083553 : Blo 2187435 11083553 := bstep (se 2 (by rfl) ⟨4156332, by rfl⟩ : syracuseStep 11083553 = 8312665) B8312665
theorem B7389035 : Blo 2187435 7389035 := bstep (se 1 (by rfl) ⟨5541776, by rfl⟩ : syracuseStep 7389035 = 11083553) B11083553
theorem B4926023 : Blo 2187435 4926023 := bstep (se 1 (by rfl) ⟨3694517, by rfl⟩ : syracuseStep 4926023 = 7389035) B7389035
theorem B3284015 : Blo 2187435 3284015 := bstep (se 1 (by rfl) ⟨2463011, by rfl⟩ : syracuseStep 3284015 = 4926023) B4926023
theorem B2189343 : Blo 2187435 2189343 := bstep (se 1 (by rfl) ⟨1642007, by rfl⟩ : syracuseStep 2189343 = 3284015) B3284015
theorem B3284021 : Blo 2187435 3284021 := bbase (se 5 (by rfl) ⟨153938, by rfl⟩ : syracuseStep 3284021 = 307877) (by norm_num)
theorem B2189347 : Blo 2187435 2189347 := bstep (se 1 (by rfl) ⟨1642010, by rfl⟩ : syracuseStep 2189347 = 3284021) B3284021
theorem B5541797 : Blo 2187435 5541797 := bbase (se 4 (by rfl) ⟨519543, by rfl⟩ : syracuseStep 5541797 = 1039087) (by norm_num)
theorem B3694531 : Blo 2187435 3694531 := bstep (se 1 (by rfl) ⟨2770898, by rfl⟩ : syracuseStep 3694531 = 5541797) B5541797
theorem B4926041 : Blo 2187435 4926041 := bstep (se 2 (by rfl) ⟨1847265, by rfl⟩ : syracuseStep 4926041 = 3694531) B3694531
theorem B3284027 : Blo 2187435 3284027 := bstep (se 1 (by rfl) ⟨2463020, by rfl⟩ : syracuseStep 3284027 = 4926041) B4926041
theorem B2189351 : Blo 2187435 2189351 := bstep (se 1 (by rfl) ⟨1642013, by rfl⟩ : syracuseStep 2189351 = 3284027) B3284027
theorem B2463025 : Blo 2187435 2463025 := bbase (se 2 (by rfl) ⟨923634, by rfl⟩ : syracuseStep 2463025 = 1847269) (by norm_num)
theorem B3284033 : Blo 2187435 3284033 := bstep (se 2 (by rfl) ⟨1231512, by rfl⟩ : syracuseStep 3284033 = 2463025) B2463025
theorem B2189355 : Blo 2187435 2189355 := bstep (se 1 (by rfl) ⟨1642016, by rfl⟩ : syracuseStep 2189355 = 3284033) B3284033
theorem B4675909 : Blo 2187435 4675909 := bbase (se 4 (by rfl) ⟨438366, by rfl⟩ : syracuseStep 4675909 = 876733) (by norm_num)
theorem B6234545 : Blo 2187435 6234545 := bstep (se 2 (by rfl) ⟨2337954, by rfl⟩ : syracuseStep 6234545 = 4675909) B4675909
theorem B4156363 : Blo 2187435 4156363 := bstep (se 1 (by rfl) ⟨3117272, by rfl⟩ : syracuseStep 4156363 = 6234545) B6234545
theorem B5541817 : Blo 2187435 5541817 := bstep (se 2 (by rfl) ⟨2078181, by rfl⟩ : syracuseStep 5541817 = 4156363) B4156363
theorem B7389089 : Blo 2187435 7389089 := bstep (se 2 (by rfl) ⟨2770908, by rfl⟩ : syracuseStep 7389089 = 5541817) B5541817
theorem B4926059 : Blo 2187435 4926059 := bstep (se 1 (by rfl) ⟨3694544, by rfl⟩ : syracuseStep 4926059 = 7389089) B7389089
theorem B3284039 : Blo 2187435 3284039 := bstep (se 1 (by rfl) ⟨2463029, by rfl⟩ : syracuseStep 3284039 = 4926059) B4926059
theorem B2189359 : Blo 2187435 2189359 := bstep (se 1 (by rfl) ⟨1642019, by rfl⟩ : syracuseStep 2189359 = 3284039) B3284039
theorem B3284045 : Blo 2187435 3284045 := bbase (se 3 (by rfl) ⟨615758, by rfl⟩ : syracuseStep 3284045 = 1231517) (by norm_num)
theorem B2189363 : Blo 2187435 2189363 := bstep (se 1 (by rfl) ⟨1642022, by rfl⟩ : syracuseStep 2189363 = 3284045) B3284045
theorem B4926077 : Blo 2187435 4926077 := bbase (se 3 (by rfl) ⟨923639, by rfl⟩ : syracuseStep 4926077 = 1847279) (by norm_num)
theorem B3284051 : Blo 2187435 3284051 := bstep (se 1 (by rfl) ⟨2463038, by rfl⟩ : syracuseStep 3284051 = 4926077) B4926077
theorem B2189367 : Blo 2187435 2189367 := bstep (se 1 (by rfl) ⟨1642025, by rfl⟩ : syracuseStep 2189367 = 3284051) B3284051
theorem B3694565 : Blo 2187435 3694565 := bbase (se 4 (by rfl) ⟨346365, by rfl⟩ : syracuseStep 3694565 = 692731) (by norm_num)
theorem B2463043 : Blo 2187435 2463043 := bstep (se 1 (by rfl) ⟨1847282, by rfl⟩ : syracuseStep 2463043 = 3694565) B3694565
theorem B3284057 : Blo 2187435 3284057 := bstep (se 2 (by rfl) ⟨1231521, by rfl⟩ : syracuseStep 3284057 = 2463043) B2463043
theorem B2189371 : Blo 2187435 2189371 := bstep (se 1 (by rfl) ⟨1642028, by rfl⟩ : syracuseStep 2189371 = 3284057) B3284057
theorem B5617469 : Blo 2187435 5617469 := bbase (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) (by norm_num)
theorem B14979917 : Blo 2187435 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B39946445 : Blo 2187435 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B26630963 : Blo 2187435 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B17753975 : Blo 2187435 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B11835983 : Blo 2187435 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B7890655 : Blo 2187435 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B10520873 : Blo 2187435 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B7013915 : Blo 2187435 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B4675943 : Blo 2187435 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B3117295 : Blo 2187435 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B16625573 : Blo 2187435 16625573 := bstep (se 4 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 16625573 = 3117295) B3117295
theorem B11083715 : Blo 2187435 11083715 := bstep (se 1 (by rfl) ⟨8312786, by rfl⟩ : syracuseStep 11083715 = 16625573) B16625573
theorem B7389143 : Blo 2187435 7389143 := bstep (se 1 (by rfl) ⟨5541857, by rfl⟩ : syracuseStep 7389143 = 11083715) B11083715
theorem B4926095 : Blo 2187435 4926095 := bstep (se 1 (by rfl) ⟨3694571, by rfl⟩ : syracuseStep 4926095 = 7389143) B7389143
theorem B3284063 : Blo 2187435 3284063 := bstep (se 1 (by rfl) ⟨2463047, by rfl⟩ : syracuseStep 3284063 = 4926095) B4926095
theorem B2189375 : Blo 2187435 2189375 := bstep (se 1 (by rfl) ⟨1642031, by rfl⟩ : syracuseStep 2189375 = 3284063) B3284063
theorem B3284069 : Blo 2187435 3284069 := bbase (se 4 (by rfl) ⟨307881, by rfl⟩ : syracuseStep 3284069 = 615763) (by norm_num)
theorem B2189379 : Blo 2187435 2189379 := bstep (se 1 (by rfl) ⟨1642034, by rfl⟩ : syracuseStep 2189379 = 3284069) B3284069
theorem B13497205 : Blo 2187435 13497205 := bbase (se 5 (by rfl) ⟨632681, by rfl⟩ : syracuseStep 13497205 = 1265363) (by norm_num)
theorem B17996273 : Blo 2187435 17996273 := bstep (se 2 (by rfl) ⟨6748602, by rfl⟩ : syracuseStep 17996273 = 13497205) B13497205
theorem B11997515 : Blo 2187435 11997515 := bstep (se 1 (by rfl) ⟨8998136, by rfl⟩ : syracuseStep 11997515 = 17996273) B17996273
theorem B31993373 : Blo 2187435 31993373 := bstep (se 3 (by rfl) ⟨5998757, by rfl⟩ : syracuseStep 31993373 = 11997515) B11997515
theorem B21328915 : Blo 2187435 21328915 := bstep (se 1 (by rfl) ⟨15996686, by rfl⟩ : syracuseStep 21328915 = 31993373) B31993373
theorem B28438553 : Blo 2187435 28438553 := bstep (se 2 (by rfl) ⟨10664457, by rfl⟩ : syracuseStep 28438553 = 21328915) B21328915
theorem B18959035 : Blo 2187435 18959035 := bstep (se 1 (by rfl) ⟨14219276, by rfl⟩ : syracuseStep 18959035 = 28438553) B28438553
theorem B25278713 : Blo 2187435 25278713 := bstep (se 2 (by rfl) ⟨9479517, by rfl⟩ : syracuseStep 25278713 = 18959035) B18959035
theorem B16852475 : Blo 2187435 16852475 := bstep (se 1 (by rfl) ⟨12639356, by rfl⟩ : syracuseStep 16852475 = 25278713) B25278713
theorem B44939933 : Blo 2187435 44939933 := bstep (se 3 (by rfl) ⟨8426237, by rfl⟩ : syracuseStep 44939933 = 16852475) B16852475
theorem B29959955 : Blo 2187435 29959955 := bstep (se 1 (by rfl) ⟨22469966, by rfl⟩ : syracuseStep 29959955 = 44939933) B44939933
theorem B19973303 : Blo 2187435 19973303 := bstep (se 1 (by rfl) ⟨14979977, by rfl⟩ : syracuseStep 19973303 = 29959955) B29959955
theorem B13315535 : Blo 2187435 13315535 := bstep (se 1 (by rfl) ⟨9986651, by rfl⟩ : syracuseStep 13315535 = 19973303) B19973303
theorem B8877023 : Blo 2187435 8877023 := bstep (se 1 (by rfl) ⟨6657767, by rfl⟩ : syracuseStep 8877023 = 13315535) B13315535
theorem B5918015 : Blo 2187435 5918015 := bstep (se 1 (by rfl) ⟨4438511, by rfl⟩ : syracuseStep 5918015 = 8877023) B8877023
theorem B3945343 : Blo 2187435 3945343 := bstep (se 1 (by rfl) ⟨2959007, by rfl⟩ : syracuseStep 3945343 = 5918015) B5918015
theorem B5260457 : Blo 2187435 5260457 := bstep (se 2 (by rfl) ⟨1972671, by rfl⟩ : syracuseStep 5260457 = 3945343) B3945343
theorem B3506971 : Blo 2187435 3506971 := bstep (se 1 (by rfl) ⟨2630228, by rfl⟩ : syracuseStep 3506971 = 5260457) B5260457
theorem B4675961 : Blo 2187435 4675961 := bstep (se 2 (by rfl) ⟨1753485, by rfl⟩ : syracuseStep 4675961 = 3506971) B3506971
theorem B3117307 : Blo 2187435 3117307 := bstep (se 1 (by rfl) ⟨2337980, by rfl⟩ : syracuseStep 3117307 = 4675961) B4675961
theorem B4156409 : Blo 2187435 4156409 := bstep (se 2 (by rfl) ⟨1558653, by rfl⟩ : syracuseStep 4156409 = 3117307) B3117307
theorem B2770939 : Blo 2187435 2770939 := bstep (se 1 (by rfl) ⟨2078204, by rfl⟩ : syracuseStep 2770939 = 4156409) B4156409
theorem B3694585 : Blo 2187435 3694585 := bstep (se 2 (by rfl) ⟨1385469, by rfl⟩ : syracuseStep 3694585 = 2770939) B2770939
theorem B4926113 : Blo 2187435 4926113 := bstep (se 2 (by rfl) ⟨1847292, by rfl⟩ : syracuseStep 4926113 = 3694585) B3694585
theorem B3284075 : Blo 2187435 3284075 := bstep (se 1 (by rfl) ⟨2463056, by rfl⟩ : syracuseStep 3284075 = 4926113) B4926113
theorem B2189383 : Blo 2187435 2189383 := bstep (se 1 (by rfl) ⟨1642037, by rfl⟩ : syracuseStep 2189383 = 3284075) B3284075
theorem B2463061 : Blo 2187435 2463061 := bbase (se 14 (by rfl) ⟨225, by rfl⟩ : syracuseStep 2463061 = 451) (by norm_num)
theorem B3284081 : Blo 2187435 3284081 := bstep (se 2 (by rfl) ⟨1231530, by rfl⟩ : syracuseStep 3284081 = 2463061) B2463061
theorem B2189387 : Blo 2187435 2189387 := bstep (se 1 (by rfl) ⟨1642040, by rfl⟩ : syracuseStep 2189387 = 3284081) B3284081
theorem B2770949 : Blo 2187435 2770949 := bbase (se 4 (by rfl) ⟨259776, by rfl⟩ : syracuseStep 2770949 = 519553) (by norm_num)
theorem B7389197 : Blo 2187435 7389197 := bstep (se 3 (by rfl) ⟨1385474, by rfl⟩ : syracuseStep 7389197 = 2770949) B2770949
theorem B4926131 : Blo 2187435 4926131 := bstep (se 1 (by rfl) ⟨3694598, by rfl⟩ : syracuseStep 4926131 = 7389197) B7389197
theorem B3284087 : Blo 2187435 3284087 := bstep (se 1 (by rfl) ⟨2463065, by rfl⟩ : syracuseStep 3284087 = 4926131) B4926131
theorem B2189391 : Blo 2187435 2189391 := bstep (se 1 (by rfl) ⟨1642043, by rfl⟩ : syracuseStep 2189391 = 3284087) B3284087
theorem B3284093 : Blo 2187435 3284093 := bbase (se 3 (by rfl) ⟨615767, by rfl⟩ : syracuseStep 3284093 = 1231535) (by norm_num)
theorem B2189395 : Blo 2187435 2189395 := bstep (se 1 (by rfl) ⟨1642046, by rfl⟩ : syracuseStep 2189395 = 3284093) B3284093
theorem B4926149 : Blo 2187435 4926149 := bbase (se 4 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 4926149 = 923653) (by norm_num)
theorem B3284099 : Blo 2187435 3284099 := bstep (se 1 (by rfl) ⟨2463074, by rfl⟩ : syracuseStep 3284099 = 4926149) B4926149
theorem B2189399 : Blo 2187435 2189399 := bstep (se 1 (by rfl) ⟨1642049, by rfl⟩ : syracuseStep 2189399 = 3284099) B3284099
theorem B2999405 : Blo 2187435 2999405 := bbase (se 3 (by rfl) ⟨562388, by rfl⟩ : syracuseStep 2999405 = 1124777) (by norm_num)
theorem B127974613 : Blo 2187435 127974613 := bstep (se 7 (by rfl) ⟨1499702, by rfl⟩ : syracuseStep 127974613 = 2999405) B2999405
theorem B170632817 : Blo 2187435 170632817 := bstep (se 2 (by rfl) ⟨63987306, by rfl⟩ : syracuseStep 170632817 = 127974613) B127974613
theorem B113755211 : Blo 2187435 113755211 := bstep (se 1 (by rfl) ⟨85316408, by rfl⟩ : syracuseStep 113755211 = 170632817) B170632817
theorem B75836807 : Blo 2187435 75836807 := bstep (se 1 (by rfl) ⟨56877605, by rfl⟩ : syracuseStep 75836807 = 113755211) B113755211
theorem B50557871 : Blo 2187435 50557871 := bstep (se 1 (by rfl) ⟨37918403, by rfl⟩ : syracuseStep 50557871 = 75836807) B75836807
theorem B33705247 : Blo 2187435 33705247 := bstep (se 1 (by rfl) ⟨25278935, by rfl⟩ : syracuseStep 33705247 = 50557871) B50557871
theorem B44940329 : Blo 2187435 44940329 := bstep (se 2 (by rfl) ⟨16852623, by rfl⟩ : syracuseStep 44940329 = 33705247) B33705247
theorem B29960219 : Blo 2187435 29960219 := bstep (se 1 (by rfl) ⟨22470164, by rfl⟩ : syracuseStep 29960219 = 44940329) B44940329
theorem B19973479 : Blo 2187435 19973479 := bstep (se 1 (by rfl) ⟨14980109, by rfl⟩ : syracuseStep 19973479 = 29960219) B29960219
theorem B26631305 : Blo 2187435 26631305 := bstep (se 2 (by rfl) ⟨9986739, by rfl⟩ : syracuseStep 26631305 = 19973479) B19973479
theorem B17754203 : Blo 2187435 17754203 := bstep (se 1 (by rfl) ⟨13315652, by rfl⟩ : syracuseStep 17754203 = 26631305) B26631305
theorem B11836135 : Blo 2187435 11836135 := bstep (se 1 (by rfl) ⟨8877101, by rfl⟩ : syracuseStep 11836135 = 17754203) B17754203
theorem B15781513 : Blo 2187435 15781513 := bstep (se 2 (by rfl) ⟨5918067, by rfl⟩ : syracuseStep 15781513 = 11836135) B11836135
theorem B21042017 : Blo 2187435 21042017 := bstep (se 2 (by rfl) ⟨7890756, by rfl⟩ : syracuseStep 21042017 = 15781513) B15781513
theorem B14028011 : Blo 2187435 14028011 := bstep (se 1 (by rfl) ⟨10521008, by rfl⟩ : syracuseStep 14028011 = 21042017) B21042017
theorem B9352007 : Blo 2187435 9352007 := bstep (se 1 (by rfl) ⟨7014005, by rfl⟩ : syracuseStep 9352007 = 14028011) B14028011
theorem B6234671 : Blo 2187435 6234671 := bstep (se 1 (by rfl) ⟨4676003, by rfl⟩ : syracuseStep 6234671 = 9352007) B9352007
theorem B4156447 : Blo 2187435 4156447 := bstep (se 1 (by rfl) ⟨3117335, by rfl⟩ : syracuseStep 4156447 = 6234671) B6234671
theorem B5541929 : Blo 2187435 5541929 := bstep (se 2 (by rfl) ⟨2078223, by rfl⟩ : syracuseStep 5541929 = 4156447) B4156447
theorem B3694619 : Blo 2187435 3694619 := bstep (se 1 (by rfl) ⟨2770964, by rfl⟩ : syracuseStep 3694619 = 5541929) B5541929
theorem B2463079 : Blo 2187435 2463079 := bstep (se 1 (by rfl) ⟨1847309, by rfl⟩ : syracuseStep 2463079 = 3694619) B3694619
theorem B3284105 : Blo 2187435 3284105 := bstep (se 2 (by rfl) ⟨1231539, by rfl⟩ : syracuseStep 3284105 = 2463079) B2463079
theorem B2189403 : Blo 2187435 2189403 := bstep (se 1 (by rfl) ⟨1642052, by rfl⟩ : syracuseStep 2189403 = 3284105) B3284105
theorem B11083877 : Blo 2187435 11083877 := bbase (se 4 (by rfl) ⟨1039113, by rfl⟩ : syracuseStep 11083877 = 2078227) (by norm_num)
theorem B7389251 : Blo 2187435 7389251 := bstep (se 1 (by rfl) ⟨5541938, by rfl⟩ : syracuseStep 7389251 = 11083877) B11083877
theorem B4926167 : Blo 2187435 4926167 := bstep (se 1 (by rfl) ⟨3694625, by rfl⟩ : syracuseStep 4926167 = 7389251) B7389251
theorem B3284111 : Blo 2187435 3284111 := bstep (se 1 (by rfl) ⟨2463083, by rfl⟩ : syracuseStep 3284111 = 4926167) B4926167
theorem B2189407 : Blo 2187435 2189407 := bstep (se 1 (by rfl) ⟨1642055, by rfl⟩ : syracuseStep 2189407 = 3284111) B3284111
theorem B3284117 : Blo 2187435 3284117 := bbase (se 6 (by rfl) ⟨76971, by rfl⟩ : syracuseStep 3284117 = 153943) (by norm_num)
theorem B2189411 : Blo 2187435 2189411 := bstep (se 1 (by rfl) ⟨1642058, by rfl⟩ : syracuseStep 2189411 = 3284117) B3284117
theorem B3420389 : Blo 2187435 3420389 := bbase (se 4 (by rfl) ⟨320661, by rfl⟩ : syracuseStep 3420389 = 641323) (by norm_num)
theorem B2280259 : Blo 2187435 2280259 := bstep (se 1 (by rfl) ⟨1710194, by rfl⟩ : syracuseStep 2280259 = 3420389) B3420389
theorem B3040345 : Blo 2187435 3040345 := bstep (se 2 (by rfl) ⟨1140129, by rfl⟩ : syracuseStep 3040345 = 2280259) B2280259
theorem B4053793 : Blo 2187435 4053793 := bstep (se 2 (by rfl) ⟨1520172, by rfl⟩ : syracuseStep 4053793 = 3040345) B3040345
theorem B5405057 : Blo 2187435 5405057 := bstep (se 2 (by rfl) ⟨2026896, by rfl⟩ : syracuseStep 5405057 = 4053793) B4053793
theorem B3603371 : Blo 2187435 3603371 := bstep (se 1 (by rfl) ⟨2702528, by rfl⟩ : syracuseStep 3603371 = 5405057) B5405057
theorem B38435957 : Blo 2187435 38435957 := bstep (se 5 (by rfl) ⟨1801685, by rfl⟩ : syracuseStep 38435957 = 3603371) B3603371
theorem B25623971 : Blo 2187435 25623971 := bstep (se 1 (by rfl) ⟨19217978, by rfl⟩ : syracuseStep 25623971 = 38435957) B38435957
theorem B17082647 : Blo 2187435 17082647 := bstep (se 1 (by rfl) ⟨12811985, by rfl⟩ : syracuseStep 17082647 = 25623971) B25623971
theorem B11388431 : Blo 2187435 11388431 := bstep (se 1 (by rfl) ⟨8541323, by rfl⟩ : syracuseStep 11388431 = 17082647) B17082647
theorem B7592287 : Blo 2187435 7592287 := bstep (se 1 (by rfl) ⟨5694215, by rfl⟩ : syracuseStep 7592287 = 11388431) B11388431
theorem B10123049 : Blo 2187435 10123049 := bstep (se 2 (by rfl) ⟨3796143, by rfl⟩ : syracuseStep 10123049 = 7592287) B7592287
theorem B6748699 : Blo 2187435 6748699 := bstep (se 1 (by rfl) ⟨5061524, by rfl⟩ : syracuseStep 6748699 = 10123049) B10123049
theorem B8998265 : Blo 2187435 8998265 := bstep (se 2 (by rfl) ⟨3374349, by rfl⟩ : syracuseStep 8998265 = 6748699) B6748699
theorem B5998843 : Blo 2187435 5998843 := bstep (se 1 (by rfl) ⟨4499132, by rfl⟩ : syracuseStep 5998843 = 8998265) B8998265
theorem B31993829 : Blo 2187435 31993829 := bstep (se 4 (by rfl) ⟨2999421, by rfl⟩ : syracuseStep 31993829 = 5998843) B5998843
theorem B21329219 : Blo 2187435 21329219 := bstep (se 1 (by rfl) ⟨15996914, by rfl⟩ : syracuseStep 21329219 = 31993829) B31993829
theorem B14219479 : Blo 2187435 14219479 := bstep (se 1 (by rfl) ⟨10664609, by rfl⟩ : syracuseStep 14219479 = 21329219) B21329219
theorem B18959305 : Blo 2187435 18959305 := bstep (se 2 (by rfl) ⟨7109739, by rfl⟩ : syracuseStep 18959305 = 14219479) B14219479
theorem B25279073 : Blo 2187435 25279073 := bstep (se 2 (by rfl) ⟨9479652, by rfl⟩ : syracuseStep 25279073 = 18959305) B18959305
theorem B16852715 : Blo 2187435 16852715 := bstep (se 1 (by rfl) ⟨12639536, by rfl⟩ : syracuseStep 16852715 = 25279073) B25279073
theorem B11235143 : Blo 2187435 11235143 := bstep (se 1 (by rfl) ⟨8426357, by rfl⟩ : syracuseStep 11235143 = 16852715) B16852715
theorem B29960381 : Blo 2187435 29960381 := bstep (se 3 (by rfl) ⟨5617571, by rfl⟩ : syracuseStep 29960381 = 11235143) B11235143
theorem B19973587 : Blo 2187435 19973587 := bstep (se 1 (by rfl) ⟨14980190, by rfl⟩ : syracuseStep 19973587 = 29960381) B29960381
theorem B26631449 : Blo 2187435 26631449 := bstep (se 2 (by rfl) ⟨9986793, by rfl⟩ : syracuseStep 26631449 = 19973587) B19973587
theorem B17754299 : Blo 2187435 17754299 := bstep (se 1 (by rfl) ⟨13315724, by rfl⟩ : syracuseStep 17754299 = 26631449) B26631449
theorem B11836199 : Blo 2187435 11836199 := bstep (se 1 (by rfl) ⟨8877149, by rfl⟩ : syracuseStep 11836199 = 17754299) B17754299
theorem B7890799 : Blo 2187435 7890799 := bstep (se 1 (by rfl) ⟨5918099, by rfl⟩ : syracuseStep 7890799 = 11836199) B11836199
theorem B10521065 : Blo 2187435 10521065 := bstep (se 2 (by rfl) ⟨3945399, by rfl⟩ : syracuseStep 10521065 = 7890799) B7890799
theorem B7014043 : Blo 2187435 7014043 := bstep (se 1 (by rfl) ⟨5260532, by rfl⟩ : syracuseStep 7014043 = 10521065) B10521065
theorem B9352057 : Blo 2187435 9352057 := bstep (se 2 (by rfl) ⟨3507021, by rfl⟩ : syracuseStep 9352057 = 7014043) B7014043
theorem B12469409 : Blo 2187435 12469409 := bstep (se 2 (by rfl) ⟨4676028, by rfl⟩ : syracuseStep 12469409 = 9352057) B9352057
theorem B8312939 : Blo 2187435 8312939 := bstep (se 1 (by rfl) ⟨6234704, by rfl⟩ : syracuseStep 8312939 = 12469409) B12469409
theorem B5541959 : Blo 2187435 5541959 := bstep (se 1 (by rfl) ⟨4156469, by rfl⟩ : syracuseStep 5541959 = 8312939) B8312939
theorem B3694639 : Blo 2187435 3694639 := bstep (se 1 (by rfl) ⟨2770979, by rfl⟩ : syracuseStep 3694639 = 5541959) B5541959
theorem B4926185 : Blo 2187435 4926185 := bstep (se 2 (by rfl) ⟨1847319, by rfl⟩ : syracuseStep 4926185 = 3694639) B3694639
theorem B3284123 : Blo 2187435 3284123 := bstep (se 1 (by rfl) ⟨2463092, by rfl⟩ : syracuseStep 3284123 = 4926185) B4926185
theorem B2189415 : Blo 2187435 2189415 := bstep (se 1 (by rfl) ⟨1642061, by rfl⟩ : syracuseStep 2189415 = 3284123) B3284123
theorem B2463097 : Blo 2187435 2463097 := bbase (se 2 (by rfl) ⟨923661, by rfl⟩ : syracuseStep 2463097 = 1847323) (by norm_num)
theorem B3284129 : Blo 2187435 3284129 := bstep (se 2 (by rfl) ⟨1231548, by rfl⟩ : syracuseStep 3284129 = 2463097) B2463097
theorem B2189419 : Blo 2187435 2189419 := bstep (se 1 (by rfl) ⟨1642064, by rfl⟩ : syracuseStep 2189419 = 3284129) B3284129
theorem B8426389 : Blo 2187435 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B11235185 : Blo 2187435 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B7490123 : Blo 2187435 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B4993415 : Blo 2187435 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B3328943 : Blo 2187435 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B35508725 : Blo 2187435 35508725 := bstep (se 5 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 35508725 = 3328943) B3328943
theorem B23672483 : Blo 2187435 23672483 := bstep (se 1 (by rfl) ⟨17754362, by rfl⟩ : syracuseStep 23672483 = 35508725) B35508725
theorem B15781655 : Blo 2187435 15781655 := bstep (se 1 (by rfl) ⟨11836241, by rfl⟩ : syracuseStep 15781655 = 23672483) B23672483
theorem B10521103 : Blo 2187435 10521103 := bstep (se 1 (by rfl) ⟨7890827, by rfl⟩ : syracuseStep 10521103 = 15781655) B15781655
theorem B14028137 : Blo 2187435 14028137 := bstep (se 2 (by rfl) ⟨5260551, by rfl⟩ : syracuseStep 14028137 = 10521103) B10521103
theorem B9352091 : Blo 2187435 9352091 := bstep (se 1 (by rfl) ⟨7014068, by rfl⟩ : syracuseStep 9352091 = 14028137) B14028137
theorem B6234727 : Blo 2187435 6234727 := bstep (se 1 (by rfl) ⟨4676045, by rfl⟩ : syracuseStep 6234727 = 9352091) B9352091
theorem B8312969 : Blo 2187435 8312969 := bstep (se 2 (by rfl) ⟨3117363, by rfl⟩ : syracuseStep 8312969 = 6234727) B6234727
theorem B5541979 : Blo 2187435 5541979 := bstep (se 1 (by rfl) ⟨4156484, by rfl⟩ : syracuseStep 5541979 = 8312969) B8312969
theorem B7389305 : Blo 2187435 7389305 := bstep (se 2 (by rfl) ⟨2770989, by rfl⟩ : syracuseStep 7389305 = 5541979) B5541979
theorem B4926203 : Blo 2187435 4926203 := bstep (se 1 (by rfl) ⟨3694652, by rfl⟩ : syracuseStep 4926203 = 7389305) B7389305
theorem B3284135 : Blo 2187435 3284135 := bstep (se 1 (by rfl) ⟨2463101, by rfl⟩ : syracuseStep 3284135 = 4926203) B4926203
theorem B2189423 : Blo 2187435 2189423 := bstep (se 1 (by rfl) ⟨1642067, by rfl⟩ : syracuseStep 2189423 = 3284135) B3284135
theorem B3284141 : Blo 2187435 3284141 := bbase (se 3 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 3284141 = 1231553) (by norm_num)
theorem B2189427 : Blo 2187435 2189427 := bstep (se 1 (by rfl) ⟨1642070, by rfl⟩ : syracuseStep 2189427 = 3284141) B3284141
theorem B4926221 : Blo 2187435 4926221 := bbase (se 3 (by rfl) ⟨923666, by rfl⟩ : syracuseStep 4926221 = 1847333) (by norm_num)
theorem B3284147 : Blo 2187435 3284147 := bstep (se 1 (by rfl) ⟨2463110, by rfl⟩ : syracuseStep 3284147 = 4926221) B4926221
theorem B2189431 : Blo 2187435 2189431 := bstep (se 1 (by rfl) ⟨1642073, by rfl⟩ : syracuseStep 2189431 = 3284147) B3284147
theorem B2771005 : Blo 2187435 2771005 := bbase (se 3 (by rfl) ⟨519563, by rfl⟩ : syracuseStep 2771005 = 1039127) (by norm_num)
theorem B3694673 : Blo 2187435 3694673 := bstep (se 2 (by rfl) ⟨1385502, by rfl⟩ : syracuseStep 3694673 = 2771005) B2771005
theorem B2463115 : Blo 2187435 2463115 := bstep (se 1 (by rfl) ⟨1847336, by rfl⟩ : syracuseStep 2463115 = 3694673) B3694673
theorem B3284153 : Blo 2187435 3284153 := bstep (se 2 (by rfl) ⟨1231557, by rfl⟩ : syracuseStep 3284153 = 2463115) B2463115
theorem B2189435 : Blo 2187435 2189435 := bstep (se 1 (by rfl) ⟨1642076, by rfl⟩ : syracuseStep 2189435 = 3284153) B3284153
theorem C0 (j : ℕ) (h1 : 546858 ≤ j) (h2 : j ≤ 547358) : Blo 2187435 (4 * j + 3) := by
  interval_cases j
  · exact B2187435
  · exact B2187439
  · exact B2187443
  · exact B2187447
  · exact B2187451
  · exact B2187455
  · exact B2187459
  · exact B2187463
  · exact B2187467
  · exact B2187471
  · exact B2187475
  · exact B2187479
  · exact B2187483
  · exact B2187487
  · exact B2187491
  · exact B2187495
  · exact B2187499
  · exact B2187503
  · exact B2187507
  · exact B2187511
  · exact B2187515
  · exact B2187519
  · exact B2187523
  · exact B2187527
  · exact B2187531
  · exact B2187535
  · exact B2187539
  · exact B2187543
  · exact B2187547
  · exact B2187551
  · exact B2187555
  · exact B2187559
  · exact B2187563
  · exact B2187567
  · exact B2187571
  · exact B2187575
  · exact B2187579
  · exact B2187583
  · exact B2187587
  · exact B2187591
  · exact B2187595
  · exact B2187599
  · exact B2187603
  · exact B2187607
  · exact B2187611
  · exact B2187615
  · exact B2187619
  · exact B2187623
  · exact B2187627
  · exact B2187631
  · exact B2187635
  · exact B2187639
  · exact B2187643
  · exact B2187647
  · exact B2187651
  · exact B2187655
  · exact B2187659
  · exact B2187663
  · exact B2187667
  · exact B2187671
  · exact B2187675
  · exact B2187679
  · exact B2187683
  · exact B2187687
  · exact B2187691
  · exact B2187695
  · exact B2187699
  · exact B2187703
  · exact B2187707
  · exact B2187711
  · exact B2187715
  · exact B2187719
  · exact B2187723
  · exact B2187727
  · exact B2187731
  · exact B2187735
  · exact B2187739
  · exact B2187743
  · exact B2187747
  · exact B2187751
  · exact B2187755
  · exact B2187759
  · exact B2187763
  · exact B2187767
  · exact B2187771
  · exact B2187775
  · exact B2187779
  · exact B2187783
  · exact B2187787
  · exact B2187791
  · exact B2187795
  · exact B2187799
  · exact B2187803
  · exact B2187807
  · exact B2187811
  · exact B2187815
  · exact B2187819
  · exact B2187823
  · exact B2187827
  · exact B2187831
  · exact B2187835
  · exact B2187839
  · exact B2187843
  · exact B2187847
  · exact B2187851
  · exact B2187855
  · exact B2187859
  · exact B2187863
  · exact B2187867
  · exact B2187871
  · exact B2187875
  · exact B2187879
  · exact B2187883
  · exact B2187887
  · exact B2187891
  · exact B2187895
  · exact B2187899
  · exact B2187903
  · exact B2187907
  · exact B2187911
  · exact B2187915
  · exact B2187919
  · exact B2187923
  · exact B2187927
  · exact B2187931
  · exact B2187935
  · exact B2187939
  · exact B2187943
  · exact B2187947
  · exact B2187951
  · exact B2187955
  · exact B2187959
  · exact B2187963
  · exact B2187967
  · exact B2187971
  · exact B2187975
  · exact B2187979
  · exact B2187983
  · exact B2187987
  · exact B2187991
  · exact B2187995
  · exact B2187999
  · exact B2188003
  · exact B2188007
  · exact B2188011
  · exact B2188015
  · exact B2188019
  · exact B2188023
  · exact B2188027
  · exact B2188031
  · exact B2188035
  · exact B2188039
  · exact B2188043
  · exact B2188047
  · exact B2188051
  · exact B2188055
  · exact B2188059
  · exact B2188063
  · exact B2188067
  · exact B2188071
  · exact B2188075
  · exact B2188079
  · exact B2188083
  · exact B2188087
  · exact B2188091
  · exact B2188095
  · exact B2188099
  · exact B2188103
  · exact B2188107
  · exact B2188111
  · exact B2188115
  · exact B2188119
  · exact B2188123
  · exact B2188127
  · exact B2188131
  · exact B2188135
  · exact B2188139
  · exact B2188143
  · exact B2188147
  · exact B2188151
  · exact B2188155
  · exact B2188159
  · exact B2188163
  · exact B2188167
  · exact B2188171
  · exact B2188175
  · exact B2188179
  · exact B2188183
  · exact B2188187
  · exact B2188191
  · exact B2188195
  · exact B2188199
  · exact B2188203
  · exact B2188207
  · exact B2188211
  · exact B2188215
  · exact B2188219
  · exact B2188223
  · exact B2188227
  · exact B2188231
  · exact B2188235
  · exact B2188239
  · exact B2188243
  · exact B2188247
  · exact B2188251
  · exact B2188255
  · exact B2188259
  · exact B2188263
  · exact B2188267
  · exact B2188271
  · exact B2188275
  · exact B2188279
  · exact B2188283
  · exact B2188287
  · exact B2188291
  · exact B2188295
  · exact B2188299
  · exact B2188303
  · exact B2188307
  · exact B2188311
  · exact B2188315
  · exact B2188319
  · exact B2188323
  · exact B2188327
  · exact B2188331
  · exact B2188335
  · exact B2188339
  · exact B2188343
  · exact B2188347
  · exact B2188351
  · exact B2188355
  · exact B2188359
  · exact B2188363
  · exact B2188367
  · exact B2188371
  · exact B2188375
  · exact B2188379
  · exact B2188383
  · exact B2188387
  · exact B2188391
  · exact B2188395
  · exact B2188399
  · exact B2188403
  · exact B2188407
  · exact B2188411
  · exact B2188415
  · exact B2188419
  · exact B2188423
  · exact B2188427
  · exact B2188431
  · exact B2188435
  · exact B2188439
  · exact B2188443
  · exact B2188447
  · exact B2188451
  · exact B2188455
  · exact B2188459
  · exact B2188463
  · exact B2188467
  · exact B2188471
  · exact B2188475
  · exact B2188479
  · exact B2188483
  · exact B2188487
  · exact B2188491
  · exact B2188495
  · exact B2188499
  · exact B2188503
  · exact B2188507
  · exact B2188511
  · exact B2188515
  · exact B2188519
  · exact B2188523
  · exact B2188527
  · exact B2188531
  · exact B2188535
  · exact B2188539
  · exact B2188543
  · exact B2188547
  · exact B2188551
  · exact B2188555
  · exact B2188559
  · exact B2188563
  · exact B2188567
  · exact B2188571
  · exact B2188575
  · exact B2188579
  · exact B2188583
  · exact B2188587
  · exact B2188591
  · exact B2188595
  · exact B2188599
  · exact B2188603
  · exact B2188607
  · exact B2188611
  · exact B2188615
  · exact B2188619
  · exact B2188623
  · exact B2188627
  · exact B2188631
  · exact B2188635
  · exact B2188639
  · exact B2188643
  · exact B2188647
  · exact B2188651
  · exact B2188655
  · exact B2188659
  · exact B2188663
  · exact B2188667
  · exact B2188671
  · exact B2188675
  · exact B2188679
  · exact B2188683
  · exact B2188687
  · exact B2188691
  · exact B2188695
  · exact B2188699
  · exact B2188703
  · exact B2188707
  · exact B2188711
  · exact B2188715
  · exact B2188719
  · exact B2188723
  · exact B2188727
  · exact B2188731
  · exact B2188735
  · exact B2188739
  · exact B2188743
  · exact B2188747
  · exact B2188751
  · exact B2188755
  · exact B2188759
  · exact B2188763
  · exact B2188767
  · exact B2188771
  · exact B2188775
  · exact B2188779
  · exact B2188783
  · exact B2188787
  · exact B2188791
  · exact B2188795
  · exact B2188799
  · exact B2188803
  · exact B2188807
  · exact B2188811
  · exact B2188815
  · exact B2188819
  · exact B2188823
  · exact B2188827
  · exact B2188831
  · exact B2188835
  · exact B2188839
  · exact B2188843
  · exact B2188847
  · exact B2188851
  · exact B2188855
  · exact B2188859
  · exact B2188863
  · exact B2188867
  · exact B2188871
  · exact B2188875
  · exact B2188879
  · exact B2188883
  · exact B2188887
  · exact B2188891
  · exact B2188895
  · exact B2188899
  · exact B2188903
  · exact B2188907
  · exact B2188911
  · exact B2188915
  · exact B2188919
  · exact B2188923
  · exact B2188927
  · exact B2188931
  · exact B2188935
  · exact B2188939
  · exact B2188943
  · exact B2188947
  · exact B2188951
  · exact B2188955
  · exact B2188959
  · exact B2188963
  · exact B2188967
  · exact B2188971
  · exact B2188975
  · exact B2188979
  · exact B2188983
  · exact B2188987
  · exact B2188991
  · exact B2188995
  · exact B2188999
  · exact B2189003
  · exact B2189007
  · exact B2189011
  · exact B2189015
  · exact B2189019
  · exact B2189023
  · exact B2189027
  · exact B2189031
  · exact B2189035
  · exact B2189039
  · exact B2189043
  · exact B2189047
  · exact B2189051
  · exact B2189055
  · exact B2189059
  · exact B2189063
  · exact B2189067
  · exact B2189071
  · exact B2189075
  · exact B2189079
  · exact B2189083
  · exact B2189087
  · exact B2189091
  · exact B2189095
  · exact B2189099
  · exact B2189103
  · exact B2189107
  · exact B2189111
  · exact B2189115
  · exact B2189119
  · exact B2189123
  · exact B2189127
  · exact B2189131
  · exact B2189135
  · exact B2189139
  · exact B2189143
  · exact B2189147
  · exact B2189151
  · exact B2189155
  · exact B2189159
  · exact B2189163
  · exact B2189167
  · exact B2189171
  · exact B2189175
  · exact B2189179
  · exact B2189183
  · exact B2189187
  · exact B2189191
  · exact B2189195
  · exact B2189199
  · exact B2189203
  · exact B2189207
  · exact B2189211
  · exact B2189215
  · exact B2189219
  · exact B2189223
  · exact B2189227
  · exact B2189231
  · exact B2189235
  · exact B2189239
  · exact B2189243
  · exact B2189247
  · exact B2189251
  · exact B2189255
  · exact B2189259
  · exact B2189263
  · exact B2189267
  · exact B2189271
  · exact B2189275
  · exact B2189279
  · exact B2189283
  · exact B2189287
  · exact B2189291
  · exact B2189295
  · exact B2189299
  · exact B2189303
  · exact B2189307
  · exact B2189311
  · exact B2189315
  · exact B2189319
  · exact B2189323
  · exact B2189327
  · exact B2189331
  · exact B2189335
  · exact B2189339
  · exact B2189343
  · exact B2189347
  · exact B2189351
  · exact B2189355
  · exact B2189359
  · exact B2189363
  · exact B2189367
  · exact B2189371
  · exact B2189375
  · exact B2189379
  · exact B2189383
  · exact B2189387
  · exact B2189391
  · exact B2189395
  · exact B2189399
  · exact B2189403
  · exact B2189407
  · exact B2189411
  · exact B2189415
  · exact B2189419
  · exact B2189423
  · exact B2189427
  · exact B2189431
  · exact B2189435
theorem solution (m : ℕ) (hlo : 2187435 ≤ m) (hhi : m ≤ 2189435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 546858 ≤ j := by omega
    have hj2 : j ≤ 547358 := by omega
    have hb : Blo 2187435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
