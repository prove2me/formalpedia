-- Prove2me | solution 1 for syracuse_descends_range_1963435_1965435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:54.747175+00:00
-- url     : https://prove2.me/submissions/86c4ae1d-2189-4b32-92c9-d52a8c840f4f

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

theorem B2208865 : Blo 1963435 2208865 := bbase (se 2 (by rfl) ⟨828324, by rfl⟩ : syracuseStep 2208865 = 1656649) (by norm_num)
theorem B2945153 : Blo 1963435 2945153 := bstep (se 2 (by rfl) ⟨1104432, by rfl⟩ : syracuseStep 2945153 = 2208865) B2208865
theorem B1963435 : Blo 1963435 1963435 := bstep (se 1 (by rfl) ⟨1472576, by rfl⟩ : syracuseStep 1963435 = 2945153) B2945153
theorem B4969957 : Blo 1963435 4969957 := bbase (se 4 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 4969957 = 931867) (by norm_num)
theorem B6626609 : Blo 1963435 6626609 := bstep (se 2 (by rfl) ⟨2484978, by rfl⟩ : syracuseStep 6626609 = 4969957) B4969957
theorem B4417739 : Blo 1963435 4417739 := bstep (se 1 (by rfl) ⟨3313304, by rfl⟩ : syracuseStep 4417739 = 6626609) B6626609
theorem B2945159 : Blo 1963435 2945159 := bstep (se 1 (by rfl) ⟨2208869, by rfl⟩ : syracuseStep 2945159 = 4417739) B4417739
theorem B1963439 : Blo 1963435 1963439 := bstep (se 1 (by rfl) ⟨1472579, by rfl⟩ : syracuseStep 1963439 = 2945159) B2945159
theorem B2945165 : Blo 1963435 2945165 := bbase (se 3 (by rfl) ⟨552218, by rfl⟩ : syracuseStep 2945165 = 1104437) (by norm_num)
theorem B1963443 : Blo 1963435 1963443 := bstep (se 1 (by rfl) ⟨1472582, by rfl⟩ : syracuseStep 1963443 = 2945165) B2945165
theorem B4417757 : Blo 1963435 4417757 := bbase (se 3 (by rfl) ⟨828329, by rfl⟩ : syracuseStep 4417757 = 1656659) (by norm_num)
theorem B2945171 : Blo 1963435 2945171 := bstep (se 1 (by rfl) ⟨2208878, by rfl⟩ : syracuseStep 2945171 = 4417757) B4417757
theorem B1963447 : Blo 1963435 1963447 := bstep (se 1 (by rfl) ⟨1472585, by rfl⟩ : syracuseStep 1963447 = 2945171) B2945171
theorem B3313325 : Blo 1963435 3313325 := bbase (se 3 (by rfl) ⟨621248, by rfl⟩ : syracuseStep 3313325 = 1242497) (by norm_num)
theorem B2208883 : Blo 1963435 2208883 := bstep (se 1 (by rfl) ⟨1656662, by rfl⟩ : syracuseStep 2208883 = 3313325) B3313325
theorem B2945177 : Blo 1963435 2945177 := bstep (se 2 (by rfl) ⟨1104441, by rfl⟩ : syracuseStep 2945177 = 2208883) B2208883
theorem B1963451 : Blo 1963435 1963451 := bstep (se 1 (by rfl) ⟨1472588, by rfl⟩ : syracuseStep 1963451 = 2945177) B2945177
theorem B6462965 : Blo 1963435 6462965 := bbase (se 5 (by rfl) ⟨302951, by rfl⟩ : syracuseStep 6462965 = 605903) (by norm_num)
theorem B4308643 : Blo 1963435 4308643 := bstep (se 1 (by rfl) ⟨3231482, by rfl⟩ : syracuseStep 4308643 = 6462965) B6462965
theorem B5744857 : Blo 1963435 5744857 := bstep (se 2 (by rfl) ⟨2154321, by rfl⟩ : syracuseStep 5744857 = 4308643) B4308643
theorem B7659809 : Blo 1963435 7659809 := bstep (se 2 (by rfl) ⟨2872428, by rfl⟩ : syracuseStep 7659809 = 5744857) B5744857
theorem B5106539 : Blo 1963435 5106539 := bstep (se 1 (by rfl) ⟨3829904, by rfl⟩ : syracuseStep 5106539 = 7659809) B7659809
theorem B3404359 : Blo 1963435 3404359 := bstep (se 1 (by rfl) ⟨2553269, by rfl⟩ : syracuseStep 3404359 = 5106539) B5106539
theorem B18156581 : Blo 1963435 18156581 := bstep (se 4 (by rfl) ⟨1702179, by rfl⟩ : syracuseStep 18156581 = 3404359) B3404359
theorem B12104387 : Blo 1963435 12104387 := bstep (se 1 (by rfl) ⟨9078290, by rfl⟩ : syracuseStep 12104387 = 18156581) B18156581
theorem B8069591 : Blo 1963435 8069591 := bstep (se 1 (by rfl) ⟨6052193, by rfl⟩ : syracuseStep 8069591 = 12104387) B12104387
theorem B21518909 : Blo 1963435 21518909 := bstep (se 3 (by rfl) ⟨4034795, by rfl⟩ : syracuseStep 21518909 = 8069591) B8069591
theorem B14345939 : Blo 1963435 14345939 := bstep (se 1 (by rfl) ⟨10759454, by rfl⟩ : syracuseStep 14345939 = 21518909) B21518909
theorem B9563959 : Blo 1963435 9563959 := bstep (se 1 (by rfl) ⟨7172969, by rfl⟩ : syracuseStep 9563959 = 14345939) B14345939
theorem B51007781 : Blo 1963435 51007781 := bstep (se 4 (by rfl) ⟨4781979, by rfl⟩ : syracuseStep 51007781 = 9563959) B9563959
theorem B34005187 : Blo 1963435 34005187 := bstep (se 1 (by rfl) ⟨25503890, by rfl⟩ : syracuseStep 34005187 = 51007781) B51007781
theorem B45340249 : Blo 1963435 45340249 := bstep (se 2 (by rfl) ⟨17002593, by rfl⟩ : syracuseStep 45340249 = 34005187) B34005187
theorem B60453665 : Blo 1963435 60453665 := bstep (se 2 (by rfl) ⟨22670124, by rfl⟩ : syracuseStep 60453665 = 45340249) B45340249
theorem B40302443 : Blo 1963435 40302443 := bstep (se 1 (by rfl) ⟨30226832, by rfl⟩ : syracuseStep 40302443 = 60453665) B60453665
theorem B26868295 : Blo 1963435 26868295 := bstep (se 1 (by rfl) ⟨20151221, by rfl⟩ : syracuseStep 26868295 = 40302443) B40302443
theorem B35824393 : Blo 1963435 35824393 := bstep (se 2 (by rfl) ⟨13434147, by rfl⟩ : syracuseStep 35824393 = 26868295) B26868295
theorem B47765857 : Blo 1963435 47765857 := bstep (se 2 (by rfl) ⟨17912196, by rfl⟩ : syracuseStep 47765857 = 35824393) B35824393
theorem B63687809 : Blo 1963435 63687809 := bstep (se 2 (by rfl) ⟨23882928, by rfl⟩ : syracuseStep 63687809 = 47765857) B47765857
theorem B42458539 : Blo 1963435 42458539 := bstep (se 1 (by rfl) ⟨31843904, by rfl⟩ : syracuseStep 42458539 = 63687809) B63687809
theorem B56611385 : Blo 1963435 56611385 := bstep (se 2 (by rfl) ⟨21229269, by rfl⟩ : syracuseStep 56611385 = 42458539) B42458539
theorem B37740923 : Blo 1963435 37740923 := bstep (se 1 (by rfl) ⟨28305692, by rfl⟩ : syracuseStep 37740923 = 56611385) B56611385
theorem B25160615 : Blo 1963435 25160615 := bstep (se 1 (by rfl) ⟨18870461, by rfl⟩ : syracuseStep 25160615 = 37740923) B37740923
theorem B16773743 : Blo 1963435 16773743 := bstep (se 1 (by rfl) ⟨12580307, by rfl⟩ : syracuseStep 16773743 = 25160615) B25160615
theorem B11182495 : Blo 1963435 11182495 := bstep (se 1 (by rfl) ⟨8386871, by rfl⟩ : syracuseStep 11182495 = 16773743) B16773743
theorem B14909993 : Blo 1963435 14909993 := bstep (se 2 (by rfl) ⟨5591247, by rfl⟩ : syracuseStep 14909993 = 11182495) B11182495
theorem B9939995 : Blo 1963435 9939995 := bstep (se 1 (by rfl) ⟨7454996, by rfl⟩ : syracuseStep 9939995 = 14909993) B14909993
theorem B6626663 : Blo 1963435 6626663 := bstep (se 1 (by rfl) ⟨4969997, by rfl⟩ : syracuseStep 6626663 = 9939995) B9939995
theorem B4417775 : Blo 1963435 4417775 := bstep (se 1 (by rfl) ⟨3313331, by rfl⟩ : syracuseStep 4417775 = 6626663) B6626663
theorem B2945183 : Blo 1963435 2945183 := bstep (se 1 (by rfl) ⟨2208887, by rfl⟩ : syracuseStep 2945183 = 4417775) B4417775
theorem B1963455 : Blo 1963435 1963455 := bstep (se 1 (by rfl) ⟨1472591, by rfl⟩ : syracuseStep 1963455 = 2945183) B2945183
theorem B2945189 : Blo 1963435 2945189 := bbase (se 4 (by rfl) ⟨276111, by rfl⟩ : syracuseStep 2945189 = 552223) (by norm_num)
theorem B1963459 : Blo 1963435 1963459 := bstep (se 1 (by rfl) ⟨1472594, by rfl⟩ : syracuseStep 1963459 = 2945189) B2945189
theorem B2485009 : Blo 1963435 2485009 := bbase (se 2 (by rfl) ⟨931878, by rfl⟩ : syracuseStep 2485009 = 1863757) (by norm_num)
theorem B3313345 : Blo 1963435 3313345 := bstep (se 2 (by rfl) ⟨1242504, by rfl⟩ : syracuseStep 3313345 = 2485009) B2485009
theorem B4417793 : Blo 1963435 4417793 := bstep (se 2 (by rfl) ⟨1656672, by rfl⟩ : syracuseStep 4417793 = 3313345) B3313345
theorem B2945195 : Blo 1963435 2945195 := bstep (se 1 (by rfl) ⟨2208896, by rfl⟩ : syracuseStep 2945195 = 4417793) B4417793
theorem B1963463 : Blo 1963435 1963463 := bstep (se 1 (by rfl) ⟨1472597, by rfl⟩ : syracuseStep 1963463 = 2945195) B2945195
theorem B2208901 : Blo 1963435 2208901 := bbase (se 4 (by rfl) ⟨207084, by rfl⟩ : syracuseStep 2208901 = 414169) (by norm_num)
theorem B2945201 : Blo 1963435 2945201 := bstep (se 2 (by rfl) ⟨1104450, by rfl⟩ : syracuseStep 2945201 = 2208901) B2208901
theorem B1963467 : Blo 1963435 1963467 := bstep (se 1 (by rfl) ⟨1472600, by rfl⟩ : syracuseStep 1963467 = 2945201) B2945201
theorem B30227093 : Blo 1963435 30227093 := bbase (se 6 (by rfl) ⟨708447, by rfl⟩ : syracuseStep 30227093 = 1416895) (by norm_num)
theorem B20151395 : Blo 1963435 20151395 := bstep (se 1 (by rfl) ⟨15113546, by rfl⟩ : syracuseStep 20151395 = 30227093) B30227093
theorem B13434263 : Blo 1963435 13434263 := bstep (se 1 (by rfl) ⟨10075697, by rfl⟩ : syracuseStep 13434263 = 20151395) B20151395
theorem B8956175 : Blo 1963435 8956175 := bstep (se 1 (by rfl) ⟨6717131, by rfl⟩ : syracuseStep 8956175 = 13434263) B13434263
theorem B23883133 : Blo 1963435 23883133 := bstep (se 3 (by rfl) ⟨4478087, by rfl⟩ : syracuseStep 23883133 = 8956175) B8956175
theorem B31844177 : Blo 1963435 31844177 := bstep (se 2 (by rfl) ⟨11941566, by rfl⟩ : syracuseStep 31844177 = 23883133) B23883133
theorem B21229451 : Blo 1963435 21229451 := bstep (se 1 (by rfl) ⟨15922088, by rfl⟩ : syracuseStep 21229451 = 31844177) B31844177
theorem B14152967 : Blo 1963435 14152967 := bstep (se 1 (by rfl) ⟨10614725, by rfl⟩ : syracuseStep 14152967 = 21229451) B21229451
theorem B9435311 : Blo 1963435 9435311 := bstep (se 1 (by rfl) ⟨7076483, by rfl⟩ : syracuseStep 9435311 = 14152967) B14152967
theorem B6290207 : Blo 1963435 6290207 := bstep (se 1 (by rfl) ⟨4717655, by rfl⟩ : syracuseStep 6290207 = 9435311) B9435311
theorem B4193471 : Blo 1963435 4193471 := bstep (se 1 (by rfl) ⟨3145103, by rfl⟩ : syracuseStep 4193471 = 6290207) B6290207
theorem B2795647 : Blo 1963435 2795647 := bstep (se 1 (by rfl) ⟨2096735, by rfl⟩ : syracuseStep 2795647 = 4193471) B4193471
theorem B3727529 : Blo 1963435 3727529 := bstep (se 2 (by rfl) ⟨1397823, by rfl⟩ : syracuseStep 3727529 = 2795647) B2795647
theorem B2485019 : Blo 1963435 2485019 := bstep (se 1 (by rfl) ⟨1863764, by rfl⟩ : syracuseStep 2485019 = 3727529) B3727529
theorem B6626717 : Blo 1963435 6626717 := bstep (se 3 (by rfl) ⟨1242509, by rfl⟩ : syracuseStep 6626717 = 2485019) B2485019
theorem B4417811 : Blo 1963435 4417811 := bstep (se 1 (by rfl) ⟨3313358, by rfl⟩ : syracuseStep 4417811 = 6626717) B6626717
theorem B2945207 : Blo 1963435 2945207 := bstep (se 1 (by rfl) ⟨2208905, by rfl⟩ : syracuseStep 2945207 = 4417811) B4417811
theorem B1963471 : Blo 1963435 1963471 := bstep (se 1 (by rfl) ⟨1472603, by rfl⟩ : syracuseStep 1963471 = 2945207) B2945207
theorem B2945213 : Blo 1963435 2945213 := bbase (se 3 (by rfl) ⟨552227, by rfl⟩ : syracuseStep 2945213 = 1104455) (by norm_num)
theorem B1963475 : Blo 1963435 1963475 := bstep (se 1 (by rfl) ⟨1472606, by rfl⟩ : syracuseStep 1963475 = 2945213) B2945213
theorem B4417829 : Blo 1963435 4417829 := bbase (se 4 (by rfl) ⟨414171, by rfl⟩ : syracuseStep 4417829 = 828343) (by norm_num)
theorem B2945219 : Blo 1963435 2945219 := bstep (se 1 (by rfl) ⟨2208914, by rfl⟩ : syracuseStep 2945219 = 4417829) B4417829
theorem B1963479 : Blo 1963435 1963479 := bstep (se 1 (by rfl) ⟨1472609, by rfl⟩ : syracuseStep 1963479 = 2945219) B2945219
theorem B4970069 : Blo 1963435 4970069 := bbase (se 8 (by rfl) ⟨29121, by rfl⟩ : syracuseStep 4970069 = 58243) (by norm_num)
theorem B3313379 : Blo 1963435 3313379 := bstep (se 1 (by rfl) ⟨2485034, by rfl⟩ : syracuseStep 3313379 = 4970069) B4970069
theorem B2208919 : Blo 1963435 2208919 := bstep (se 1 (by rfl) ⟨1656689, by rfl⟩ : syracuseStep 2208919 = 3313379) B3313379
theorem B2945225 : Blo 1963435 2945225 := bstep (se 2 (by rfl) ⟨1104459, by rfl⟩ : syracuseStep 2945225 = 2208919) B2208919
theorem B1963483 : Blo 1963435 1963483 := bstep (se 1 (by rfl) ⟨1472612, by rfl⟩ : syracuseStep 1963483 = 2945225) B2945225
theorem B4717693 : Blo 1963435 4717693 := bbase (se 3 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 4717693 = 1769135) (by norm_num)
theorem B6290257 : Blo 1963435 6290257 := bstep (se 2 (by rfl) ⟨2358846, by rfl⟩ : syracuseStep 6290257 = 4717693) B4717693
theorem B8387009 : Blo 1963435 8387009 := bstep (se 2 (by rfl) ⟨3145128, by rfl⟩ : syracuseStep 8387009 = 6290257) B6290257
theorem B5591339 : Blo 1963435 5591339 := bstep (se 1 (by rfl) ⟨4193504, by rfl⟩ : syracuseStep 5591339 = 8387009) B8387009
theorem B3727559 : Blo 1963435 3727559 := bstep (se 1 (by rfl) ⟨2795669, by rfl⟩ : syracuseStep 3727559 = 5591339) B5591339
theorem B9940157 : Blo 1963435 9940157 := bstep (se 3 (by rfl) ⟨1863779, by rfl⟩ : syracuseStep 9940157 = 3727559) B3727559
theorem B6626771 : Blo 1963435 6626771 := bstep (se 1 (by rfl) ⟨4970078, by rfl⟩ : syracuseStep 6626771 = 9940157) B9940157
theorem B4417847 : Blo 1963435 4417847 := bstep (se 1 (by rfl) ⟨3313385, by rfl⟩ : syracuseStep 4417847 = 6626771) B6626771
theorem B2945231 : Blo 1963435 2945231 := bstep (se 1 (by rfl) ⟨2208923, by rfl⟩ : syracuseStep 2945231 = 4417847) B4417847
theorem B1963487 : Blo 1963435 1963487 := bstep (se 1 (by rfl) ⟨1472615, by rfl⟩ : syracuseStep 1963487 = 2945231) B2945231
theorem B2945237 : Blo 1963435 2945237 := bbase (se 7 (by rfl) ⟨34514, by rfl⟩ : syracuseStep 2945237 = 69029) (by norm_num)
theorem B1963491 : Blo 1963435 1963491 := bstep (se 1 (by rfl) ⟨1472618, by rfl⟩ : syracuseStep 1963491 = 2945237) B2945237
theorem B2096761 : Blo 1963435 2096761 := bbase (se 2 (by rfl) ⟨786285, by rfl⟩ : syracuseStep 2096761 = 1572571) (by norm_num)
theorem B2795681 : Blo 1963435 2795681 := bstep (se 2 (by rfl) ⟨1048380, by rfl⟩ : syracuseStep 2795681 = 2096761) B2096761
theorem B7455149 : Blo 1963435 7455149 := bstep (se 3 (by rfl) ⟨1397840, by rfl⟩ : syracuseStep 7455149 = 2795681) B2795681
theorem B4970099 : Blo 1963435 4970099 := bstep (se 1 (by rfl) ⟨3727574, by rfl⟩ : syracuseStep 4970099 = 7455149) B7455149
theorem B3313399 : Blo 1963435 3313399 := bstep (se 1 (by rfl) ⟨2485049, by rfl⟩ : syracuseStep 3313399 = 4970099) B4970099
theorem B4417865 : Blo 1963435 4417865 := bstep (se 2 (by rfl) ⟨1656699, by rfl⟩ : syracuseStep 4417865 = 3313399) B3313399
theorem B2945243 : Blo 1963435 2945243 := bstep (se 1 (by rfl) ⟨2208932, by rfl⟩ : syracuseStep 2945243 = 4417865) B4417865
theorem B1963495 : Blo 1963435 1963495 := bstep (se 1 (by rfl) ⟨1472621, by rfl⟩ : syracuseStep 1963495 = 2945243) B2945243
theorem B2208937 : Blo 1963435 2208937 := bbase (se 2 (by rfl) ⟨828351, by rfl⟩ : syracuseStep 2208937 = 1656703) (by norm_num)
theorem B2945249 : Blo 1963435 2945249 := bstep (se 2 (by rfl) ⟨1104468, by rfl⟩ : syracuseStep 2945249 = 2208937) B2208937
theorem B1963499 : Blo 1963435 1963499 := bstep (se 1 (by rfl) ⟨1472624, by rfl⟩ : syracuseStep 1963499 = 2945249) B2945249
theorem B8387077 : Blo 1963435 8387077 := bbase (se 4 (by rfl) ⟨786288, by rfl⟩ : syracuseStep 8387077 = 1572577) (by norm_num)
theorem B11182769 : Blo 1963435 11182769 := bstep (se 2 (by rfl) ⟨4193538, by rfl⟩ : syracuseStep 11182769 = 8387077) B8387077
theorem B7455179 : Blo 1963435 7455179 := bstep (se 1 (by rfl) ⟨5591384, by rfl⟩ : syracuseStep 7455179 = 11182769) B11182769
theorem B4970119 : Blo 1963435 4970119 := bstep (se 1 (by rfl) ⟨3727589, by rfl⟩ : syracuseStep 4970119 = 7455179) B7455179
theorem B6626825 : Blo 1963435 6626825 := bstep (se 2 (by rfl) ⟨2485059, by rfl⟩ : syracuseStep 6626825 = 4970119) B4970119
theorem B4417883 : Blo 1963435 4417883 := bstep (se 1 (by rfl) ⟨3313412, by rfl⟩ : syracuseStep 4417883 = 6626825) B6626825
theorem B2945255 : Blo 1963435 2945255 := bstep (se 1 (by rfl) ⟨2208941, by rfl⟩ : syracuseStep 2945255 = 4417883) B4417883
theorem B1963503 : Blo 1963435 1963503 := bstep (se 1 (by rfl) ⟨1472627, by rfl⟩ : syracuseStep 1963503 = 2945255) B2945255
theorem B2945261 : Blo 1963435 2945261 := bbase (se 3 (by rfl) ⟨552236, by rfl⟩ : syracuseStep 2945261 = 1104473) (by norm_num)
theorem B1963507 : Blo 1963435 1963507 := bstep (se 1 (by rfl) ⟨1472630, by rfl⟩ : syracuseStep 1963507 = 2945261) B2945261
theorem B4417901 : Blo 1963435 4417901 := bbase (se 3 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 4417901 = 1656713) (by norm_num)
theorem B2945267 : Blo 1963435 2945267 := bstep (se 1 (by rfl) ⟨2208950, by rfl⟩ : syracuseStep 2945267 = 4417901) B4417901
theorem B1963511 : Blo 1963435 1963511 := bstep (se 1 (by rfl) ⟨1472633, by rfl⟩ : syracuseStep 1963511 = 2945267) B2945267
theorem B3727613 : Blo 1963435 3727613 := bbase (se 3 (by rfl) ⟨698927, by rfl⟩ : syracuseStep 3727613 = 1397855) (by norm_num)
theorem B2485075 : Blo 1963435 2485075 := bstep (se 1 (by rfl) ⟨1863806, by rfl⟩ : syracuseStep 2485075 = 3727613) B3727613
theorem B3313433 : Blo 1963435 3313433 := bstep (se 2 (by rfl) ⟨1242537, by rfl⟩ : syracuseStep 3313433 = 2485075) B2485075
theorem B2208955 : Blo 1963435 2208955 := bstep (se 1 (by rfl) ⟨1656716, by rfl⟩ : syracuseStep 2208955 = 3313433) B3313433
theorem B2945273 : Blo 1963435 2945273 := bstep (se 2 (by rfl) ⟨1104477, by rfl⟩ : syracuseStep 2945273 = 2208955) B2208955
theorem B1963515 : Blo 1963435 1963515 := bstep (se 1 (by rfl) ⟨1472636, by rfl⟩ : syracuseStep 1963515 = 2945273) B2945273
theorem B7961237 : Blo 1963435 7961237 := bbase (se 6 (by rfl) ⟨186591, by rfl⟩ : syracuseStep 7961237 = 373183) (by norm_num)
theorem B5307491 : Blo 1963435 5307491 := bstep (se 1 (by rfl) ⟨3980618, by rfl⟩ : syracuseStep 5307491 = 7961237) B7961237
theorem B3538327 : Blo 1963435 3538327 := bstep (se 1 (by rfl) ⟨2653745, by rfl⟩ : syracuseStep 3538327 = 5307491) B5307491
theorem B4717769 : Blo 1963435 4717769 := bstep (se 2 (by rfl) ⟨1769163, by rfl⟩ : syracuseStep 4717769 = 3538327) B3538327
theorem B50322869 : Blo 1963435 50322869 := bstep (se 5 (by rfl) ⟨2358884, by rfl⟩ : syracuseStep 50322869 = 4717769) B4717769
theorem B33548579 : Blo 1963435 33548579 := bstep (se 1 (by rfl) ⟨25161434, by rfl⟩ : syracuseStep 33548579 = 50322869) B50322869
theorem B22365719 : Blo 1963435 22365719 := bstep (se 1 (by rfl) ⟨16774289, by rfl⟩ : syracuseStep 22365719 = 33548579) B33548579
theorem B14910479 : Blo 1963435 14910479 := bstep (se 1 (by rfl) ⟨11182859, by rfl⟩ : syracuseStep 14910479 = 22365719) B22365719
theorem B9940319 : Blo 1963435 9940319 := bstep (se 1 (by rfl) ⟨7455239, by rfl⟩ : syracuseStep 9940319 = 14910479) B14910479
theorem B6626879 : Blo 1963435 6626879 := bstep (se 1 (by rfl) ⟨4970159, by rfl⟩ : syracuseStep 6626879 = 9940319) B9940319
theorem B4417919 : Blo 1963435 4417919 := bstep (se 1 (by rfl) ⟨3313439, by rfl⟩ : syracuseStep 4417919 = 6626879) B6626879
theorem B2945279 : Blo 1963435 2945279 := bstep (se 1 (by rfl) ⟨2208959, by rfl⟩ : syracuseStep 2945279 = 4417919) B4417919
theorem B1963519 : Blo 1963435 1963519 := bstep (se 1 (by rfl) ⟨1472639, by rfl⟩ : syracuseStep 1963519 = 2945279) B2945279
theorem B2945285 : Blo 1963435 2945285 := bbase (se 4 (by rfl) ⟨276120, by rfl⟩ : syracuseStep 2945285 = 552241) (by norm_num)
theorem B1963523 : Blo 1963435 1963523 := bstep (se 1 (by rfl) ⟨1472642, by rfl⟩ : syracuseStep 1963523 = 2945285) B2945285
theorem B3313453 : Blo 1963435 3313453 := bbase (se 3 (by rfl) ⟨621272, by rfl⟩ : syracuseStep 3313453 = 1242545) (by norm_num)
theorem B4417937 : Blo 1963435 4417937 := bstep (se 2 (by rfl) ⟨1656726, by rfl⟩ : syracuseStep 4417937 = 3313453) B3313453
theorem B2945291 : Blo 1963435 2945291 := bstep (se 1 (by rfl) ⟨2208968, by rfl⟩ : syracuseStep 2945291 = 4417937) B4417937
theorem B1963527 : Blo 1963435 1963527 := bstep (se 1 (by rfl) ⟨1472645, by rfl⟩ : syracuseStep 1963527 = 2945291) B2945291
theorem B2208973 : Blo 1963435 2208973 := bbase (se 3 (by rfl) ⟨414182, by rfl⟩ : syracuseStep 2208973 = 828365) (by norm_num)
theorem B2945297 : Blo 1963435 2945297 := bstep (se 2 (by rfl) ⟨1104486, by rfl⟩ : syracuseStep 2945297 = 2208973) B2208973
theorem B1963531 : Blo 1963435 1963531 := bstep (se 1 (by rfl) ⟨1472648, by rfl⟩ : syracuseStep 1963531 = 2945297) B2945297
theorem B6626933 : Blo 1963435 6626933 := bbase (se 5 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 6626933 = 621275) (by norm_num)
theorem B4417955 : Blo 1963435 4417955 := bstep (se 1 (by rfl) ⟨3313466, by rfl⟩ : syracuseStep 4417955 = 6626933) B6626933
theorem B2945303 : Blo 1963435 2945303 := bstep (se 1 (by rfl) ⟨2208977, by rfl⟩ : syracuseStep 2945303 = 4417955) B4417955
theorem B1963535 : Blo 1963435 1963535 := bstep (se 1 (by rfl) ⟨1472651, by rfl⟩ : syracuseStep 1963535 = 2945303) B2945303
theorem B2945309 : Blo 1963435 2945309 := bbase (se 3 (by rfl) ⟨552245, by rfl⟩ : syracuseStep 2945309 = 1104491) (by norm_num)
theorem B1963539 : Blo 1963435 1963539 := bstep (se 1 (by rfl) ⟨1472654, by rfl⟩ : syracuseStep 1963539 = 2945309) B2945309
theorem B4417973 : Blo 1963435 4417973 := bbase (se 5 (by rfl) ⟨207092, by rfl⟩ : syracuseStep 4417973 = 414185) (by norm_num)
theorem B2945315 : Blo 1963435 2945315 := bstep (se 1 (by rfl) ⟨2208986, by rfl⟩ : syracuseStep 2945315 = 4417973) B4417973
theorem B1963543 : Blo 1963435 1963543 := bstep (se 1 (by rfl) ⟨1472657, by rfl⟩ : syracuseStep 1963543 = 2945315) B2945315
theorem B3980677 : Blo 1963435 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B5307569 : Blo 1963435 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B3538379 : Blo 1963435 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B2358919 : Blo 1963435 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B3145225 : Blo 1963435 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B4193633 : Blo 1963435 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B11183021 : Blo 1963435 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B7455347 : Blo 1963435 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B4970231 : Blo 1963435 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B3313487 : Blo 1963435 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B2208991 : Blo 1963435 2208991 := bstep (se 1 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 2208991 = 3313487) B3313487
theorem B2945321 : Blo 1963435 2945321 := bstep (se 2 (by rfl) ⟨1104495, by rfl⟩ : syracuseStep 2945321 = 2208991) B2208991
theorem B1963547 : Blo 1963435 1963547 := bstep (se 1 (by rfl) ⟨1472660, by rfl⟩ : syracuseStep 1963547 = 2945321) B2945321
theorem B10615157 : Blo 1963435 10615157 := bbase (se 5 (by rfl) ⟨497585, by rfl⟩ : syracuseStep 10615157 = 995171) (by norm_num)
theorem B7076771 : Blo 1963435 7076771 := bstep (se 1 (by rfl) ⟨5307578, by rfl⟩ : syracuseStep 7076771 = 10615157) B10615157
theorem B4717847 : Blo 1963435 4717847 := bstep (se 1 (by rfl) ⟨3538385, by rfl⟩ : syracuseStep 4717847 = 7076771) B7076771
theorem B3145231 : Blo 1963435 3145231 := bstep (se 1 (by rfl) ⟨2358923, by rfl⟩ : syracuseStep 3145231 = 4717847) B4717847
theorem B4193641 : Blo 1963435 4193641 := bstep (se 2 (by rfl) ⟨1572615, by rfl⟩ : syracuseStep 4193641 = 3145231) B3145231
theorem B5591521 : Blo 1963435 5591521 := bstep (se 2 (by rfl) ⟨2096820, by rfl⟩ : syracuseStep 5591521 = 4193641) B4193641
theorem B7455361 : Blo 1963435 7455361 := bstep (se 2 (by rfl) ⟨2795760, by rfl⟩ : syracuseStep 7455361 = 5591521) B5591521
theorem B9940481 : Blo 1963435 9940481 := bstep (se 2 (by rfl) ⟨3727680, by rfl⟩ : syracuseStep 9940481 = 7455361) B7455361
theorem B6626987 : Blo 1963435 6626987 := bstep (se 1 (by rfl) ⟨4970240, by rfl⟩ : syracuseStep 6626987 = 9940481) B9940481
theorem B4417991 : Blo 1963435 4417991 := bstep (se 1 (by rfl) ⟨3313493, by rfl⟩ : syracuseStep 4417991 = 6626987) B6626987
theorem B2945327 : Blo 1963435 2945327 := bstep (se 1 (by rfl) ⟨2208995, by rfl⟩ : syracuseStep 2945327 = 4417991) B4417991
theorem B1963551 : Blo 1963435 1963551 := bstep (se 1 (by rfl) ⟨1472663, by rfl⟩ : syracuseStep 1963551 = 2945327) B2945327
theorem B2945333 : Blo 1963435 2945333 := bbase (se 5 (by rfl) ⟨138062, by rfl⟩ : syracuseStep 2945333 = 276125) (by norm_num)
theorem B1963555 : Blo 1963435 1963555 := bstep (se 1 (by rfl) ⟨1472666, by rfl⟩ : syracuseStep 1963555 = 2945333) B2945333
theorem B4970261 : Blo 1963435 4970261 := bbase (se 6 (by rfl) ⟨116490, by rfl⟩ : syracuseStep 4970261 = 232981) (by norm_num)
theorem B3313507 : Blo 1963435 3313507 := bstep (se 1 (by rfl) ⟨2485130, by rfl⟩ : syracuseStep 3313507 = 4970261) B4970261
theorem B4418009 : Blo 1963435 4418009 := bstep (se 2 (by rfl) ⟨1656753, by rfl⟩ : syracuseStep 4418009 = 3313507) B3313507
theorem B2945339 : Blo 1963435 2945339 := bstep (se 1 (by rfl) ⟨2209004, by rfl⟩ : syracuseStep 2945339 = 4418009) B4418009
theorem B1963559 : Blo 1963435 1963559 := bstep (se 1 (by rfl) ⟨1472669, by rfl⟩ : syracuseStep 1963559 = 2945339) B2945339
theorem B2209009 : Blo 1963435 2209009 := bbase (se 2 (by rfl) ⟨828378, by rfl⟩ : syracuseStep 2209009 = 1656757) (by norm_num)
theorem B2945345 : Blo 1963435 2945345 := bstep (se 2 (by rfl) ⟨1104504, by rfl⟩ : syracuseStep 2945345 = 2209009) B2209009
theorem B1963563 : Blo 1963435 1963563 := bstep (se 1 (by rfl) ⟨1472672, by rfl⟩ : syracuseStep 1963563 = 2945345) B2945345
theorem B18871541 : Blo 1963435 18871541 := bbase (se 5 (by rfl) ⟨884603, by rfl⟩ : syracuseStep 18871541 = 1769207) (by norm_num)
theorem B12581027 : Blo 1963435 12581027 := bstep (se 1 (by rfl) ⟨9435770, by rfl⟩ : syracuseStep 12581027 = 18871541) B18871541
theorem B8387351 : Blo 1963435 8387351 := bstep (se 1 (by rfl) ⟨6290513, by rfl⟩ : syracuseStep 8387351 = 12581027) B12581027
theorem B5591567 : Blo 1963435 5591567 := bstep (se 1 (by rfl) ⟨4193675, by rfl⟩ : syracuseStep 5591567 = 8387351) B8387351
theorem B3727711 : Blo 1963435 3727711 := bstep (se 1 (by rfl) ⟨2795783, by rfl⟩ : syracuseStep 3727711 = 5591567) B5591567
theorem B4970281 : Blo 1963435 4970281 := bstep (se 2 (by rfl) ⟨1863855, by rfl⟩ : syracuseStep 4970281 = 3727711) B3727711
theorem B6627041 : Blo 1963435 6627041 := bstep (se 2 (by rfl) ⟨2485140, by rfl⟩ : syracuseStep 6627041 = 4970281) B4970281
theorem B4418027 : Blo 1963435 4418027 := bstep (se 1 (by rfl) ⟨3313520, by rfl⟩ : syracuseStep 4418027 = 6627041) B6627041
theorem B2945351 : Blo 1963435 2945351 := bstep (se 1 (by rfl) ⟨2209013, by rfl⟩ : syracuseStep 2945351 = 4418027) B4418027
theorem B1963567 : Blo 1963435 1963567 := bstep (se 1 (by rfl) ⟨1472675, by rfl⟩ : syracuseStep 1963567 = 2945351) B2945351
theorem B2945357 : Blo 1963435 2945357 := bbase (se 3 (by rfl) ⟨552254, by rfl⟩ : syracuseStep 2945357 = 1104509) (by norm_num)
theorem B1963571 : Blo 1963435 1963571 := bstep (se 1 (by rfl) ⟨1472678, by rfl⟩ : syracuseStep 1963571 = 2945357) B2945357
theorem B4418045 : Blo 1963435 4418045 := bbase (se 3 (by rfl) ⟨828383, by rfl⟩ : syracuseStep 4418045 = 1656767) (by norm_num)
theorem B2945363 : Blo 1963435 2945363 := bstep (se 1 (by rfl) ⟨2209022, by rfl⟩ : syracuseStep 2945363 = 4418045) B4418045
theorem B1963575 : Blo 1963435 1963575 := bstep (se 1 (by rfl) ⟨1472681, by rfl⟩ : syracuseStep 1963575 = 2945363) B2945363
theorem B3313541 : Blo 1963435 3313541 := bbase (se 4 (by rfl) ⟨310644, by rfl⟩ : syracuseStep 3313541 = 621289) (by norm_num)
theorem B2209027 : Blo 1963435 2209027 := bstep (se 1 (by rfl) ⟨1656770, by rfl⟩ : syracuseStep 2209027 = 3313541) B3313541
theorem B2945369 : Blo 1963435 2945369 := bstep (se 2 (by rfl) ⟨1104513, by rfl⟩ : syracuseStep 2945369 = 2209027) B2209027
theorem B1963579 : Blo 1963435 1963579 := bstep (se 1 (by rfl) ⟨1472684, by rfl⟩ : syracuseStep 1963579 = 2945369) B2945369
theorem B14910965 : Blo 1963435 14910965 := bbase (se 5 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 14910965 = 1397903) (by norm_num)
theorem B9940643 : Blo 1963435 9940643 := bstep (se 1 (by rfl) ⟨7455482, by rfl⟩ : syracuseStep 9940643 = 14910965) B14910965
theorem B6627095 : Blo 1963435 6627095 := bstep (se 1 (by rfl) ⟨4970321, by rfl⟩ : syracuseStep 6627095 = 9940643) B9940643
theorem B4418063 : Blo 1963435 4418063 := bstep (se 1 (by rfl) ⟨3313547, by rfl⟩ : syracuseStep 4418063 = 6627095) B6627095
theorem B2945375 : Blo 1963435 2945375 := bstep (se 1 (by rfl) ⟨2209031, by rfl⟩ : syracuseStep 2945375 = 4418063) B4418063
theorem B1963583 : Blo 1963435 1963583 := bstep (se 1 (by rfl) ⟨1472687, by rfl⟩ : syracuseStep 1963583 = 2945375) B2945375
theorem B2945381 : Blo 1963435 2945381 := bbase (se 4 (by rfl) ⟨276129, by rfl⟩ : syracuseStep 2945381 = 552259) (by norm_num)
theorem B1963587 : Blo 1963435 1963587 := bstep (se 1 (by rfl) ⟨1472690, by rfl⟩ : syracuseStep 1963587 = 2945381) B2945381
theorem B3727757 : Blo 1963435 3727757 := bbase (se 3 (by rfl) ⟨698954, by rfl⟩ : syracuseStep 3727757 = 1397909) (by norm_num)
theorem B2485171 : Blo 1963435 2485171 := bstep (se 1 (by rfl) ⟨1863878, by rfl⟩ : syracuseStep 2485171 = 3727757) B3727757
theorem B3313561 : Blo 1963435 3313561 := bstep (se 2 (by rfl) ⟨1242585, by rfl⟩ : syracuseStep 3313561 = 2485171) B2485171
theorem B4418081 : Blo 1963435 4418081 := bstep (se 2 (by rfl) ⟨1656780, by rfl⟩ : syracuseStep 4418081 = 3313561) B3313561
theorem B2945387 : Blo 1963435 2945387 := bstep (se 1 (by rfl) ⟨2209040, by rfl⟩ : syracuseStep 2945387 = 4418081) B4418081
theorem B1963591 : Blo 1963435 1963591 := bstep (se 1 (by rfl) ⟨1472693, by rfl⟩ : syracuseStep 1963591 = 2945387) B2945387
theorem B2209045 : Blo 1963435 2209045 := bbase (se 6 (by rfl) ⟨51774, by rfl⟩ : syracuseStep 2209045 = 103549) (by norm_num)
theorem B2945393 : Blo 1963435 2945393 := bstep (se 2 (by rfl) ⟨1104522, by rfl⟩ : syracuseStep 2945393 = 2209045) B2209045
theorem B1963595 : Blo 1963435 1963595 := bstep (se 1 (by rfl) ⟨1472696, by rfl⟩ : syracuseStep 1963595 = 2945393) B2945393
theorem B2485181 : Blo 1963435 2485181 := bbase (se 3 (by rfl) ⟨465971, by rfl⟩ : syracuseStep 2485181 = 931943) (by norm_num)
theorem B6627149 : Blo 1963435 6627149 := bstep (se 3 (by rfl) ⟨1242590, by rfl⟩ : syracuseStep 6627149 = 2485181) B2485181
theorem B4418099 : Blo 1963435 4418099 := bstep (se 1 (by rfl) ⟨3313574, by rfl⟩ : syracuseStep 4418099 = 6627149) B6627149
theorem B2945399 : Blo 1963435 2945399 := bstep (se 1 (by rfl) ⟨2209049, by rfl⟩ : syracuseStep 2945399 = 4418099) B4418099
theorem B1963599 : Blo 1963435 1963599 := bstep (se 1 (by rfl) ⟨1472699, by rfl⟩ : syracuseStep 1963599 = 2945399) B2945399
theorem B2945405 : Blo 1963435 2945405 := bbase (se 3 (by rfl) ⟨552263, by rfl⟩ : syracuseStep 2945405 = 1104527) (by norm_num)
theorem B1963603 : Blo 1963435 1963603 := bstep (se 1 (by rfl) ⟨1472702, by rfl⟩ : syracuseStep 1963603 = 2945405) B2945405
theorem B4418117 : Blo 1963435 4418117 := bbase (se 4 (by rfl) ⟨414198, by rfl⟩ : syracuseStep 4418117 = 828397) (by norm_num)
theorem B2945411 : Blo 1963435 2945411 := bstep (se 1 (by rfl) ⟨2209058, by rfl⟩ : syracuseStep 2945411 = 4418117) B4418117
theorem B1963607 : Blo 1963435 1963607 := bstep (se 1 (by rfl) ⟨1472705, by rfl⟩ : syracuseStep 1963607 = 2945411) B2945411
theorem B2096885 : Blo 1963435 2096885 := bbase (se 5 (by rfl) ⟨98291, by rfl⟩ : syracuseStep 2096885 = 196583) (by norm_num)
theorem B5591693 : Blo 1963435 5591693 := bstep (se 3 (by rfl) ⟨1048442, by rfl⟩ : syracuseStep 5591693 = 2096885) B2096885
theorem B3727795 : Blo 1963435 3727795 := bstep (se 1 (by rfl) ⟨2795846, by rfl⟩ : syracuseStep 3727795 = 5591693) B5591693
theorem B4970393 : Blo 1963435 4970393 := bstep (se 2 (by rfl) ⟨1863897, by rfl⟩ : syracuseStep 4970393 = 3727795) B3727795
theorem B3313595 : Blo 1963435 3313595 := bstep (se 1 (by rfl) ⟨2485196, by rfl⟩ : syracuseStep 3313595 = 4970393) B4970393
theorem B2209063 : Blo 1963435 2209063 := bstep (se 1 (by rfl) ⟨1656797, by rfl⟩ : syracuseStep 2209063 = 3313595) B3313595
theorem B2945417 : Blo 1963435 2945417 := bstep (se 2 (by rfl) ⟨1104531, by rfl⟩ : syracuseStep 2945417 = 2209063) B2209063
theorem B1963611 : Blo 1963435 1963611 := bstep (se 1 (by rfl) ⟨1472708, by rfl⟩ : syracuseStep 1963611 = 2945417) B2945417
theorem B9940805 : Blo 1963435 9940805 := bbase (se 4 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 9940805 = 1863901) (by norm_num)
theorem B6627203 : Blo 1963435 6627203 := bstep (se 1 (by rfl) ⟨4970402, by rfl⟩ : syracuseStep 6627203 = 9940805) B9940805
theorem B4418135 : Blo 1963435 4418135 := bstep (se 1 (by rfl) ⟨3313601, by rfl⟩ : syracuseStep 4418135 = 6627203) B6627203
theorem B2945423 : Blo 1963435 2945423 := bstep (se 1 (by rfl) ⟨2209067, by rfl⟩ : syracuseStep 2945423 = 4418135) B4418135
theorem B1963615 : Blo 1963435 1963615 := bstep (se 1 (by rfl) ⟨1472711, by rfl⟩ : syracuseStep 1963615 = 2945423) B2945423
theorem B2945429 : Blo 1963435 2945429 := bbase (se 6 (by rfl) ⟨69033, by rfl⟩ : syracuseStep 2945429 = 138067) (by norm_num)
theorem B1963619 : Blo 1963435 1963619 := bstep (se 1 (by rfl) ⟨1472714, by rfl⟩ : syracuseStep 1963619 = 2945429) B2945429
theorem B6290693 : Blo 1963435 6290693 := bbase (se 4 (by rfl) ⟨589752, by rfl⟩ : syracuseStep 6290693 = 1179505) (by norm_num)
theorem B4193795 : Blo 1963435 4193795 := bstep (se 1 (by rfl) ⟨3145346, by rfl⟩ : syracuseStep 4193795 = 6290693) B6290693
theorem B11183453 : Blo 1963435 11183453 := bstep (se 3 (by rfl) ⟨2096897, by rfl⟩ : syracuseStep 11183453 = 4193795) B4193795
theorem B7455635 : Blo 1963435 7455635 := bstep (se 1 (by rfl) ⟨5591726, by rfl⟩ : syracuseStep 7455635 = 11183453) B11183453
theorem B4970423 : Blo 1963435 4970423 := bstep (se 1 (by rfl) ⟨3727817, by rfl⟩ : syracuseStep 4970423 = 7455635) B7455635
theorem B3313615 : Blo 1963435 3313615 := bstep (se 1 (by rfl) ⟨2485211, by rfl⟩ : syracuseStep 3313615 = 4970423) B4970423
theorem B4418153 : Blo 1963435 4418153 := bstep (se 2 (by rfl) ⟨1656807, by rfl⟩ : syracuseStep 4418153 = 3313615) B3313615
theorem B2945435 : Blo 1963435 2945435 := bstep (se 1 (by rfl) ⟨2209076, by rfl⟩ : syracuseStep 2945435 = 4418153) B4418153
theorem B1963623 : Blo 1963435 1963623 := bstep (se 1 (by rfl) ⟨1472717, by rfl⟩ : syracuseStep 1963623 = 2945435) B2945435
theorem B2209081 : Blo 1963435 2209081 := bbase (se 2 (by rfl) ⟨828405, by rfl⟩ : syracuseStep 2209081 = 1656811) (by norm_num)
theorem B2945441 : Blo 1963435 2945441 := bstep (se 2 (by rfl) ⟨1104540, by rfl⟩ : syracuseStep 2945441 = 2209081) B2209081
theorem B1963627 : Blo 1963435 1963627 := bstep (se 1 (by rfl) ⟨1472720, by rfl⟩ : syracuseStep 1963627 = 2945441) B2945441
theorem B5591749 : Blo 1963435 5591749 := bbase (se 4 (by rfl) ⟨524226, by rfl⟩ : syracuseStep 5591749 = 1048453) (by norm_num)
theorem B7455665 : Blo 1963435 7455665 := bstep (se 2 (by rfl) ⟨2795874, by rfl⟩ : syracuseStep 7455665 = 5591749) B5591749
theorem B4970443 : Blo 1963435 4970443 := bstep (se 1 (by rfl) ⟨3727832, by rfl⟩ : syracuseStep 4970443 = 7455665) B7455665
theorem B6627257 : Blo 1963435 6627257 := bstep (se 2 (by rfl) ⟨2485221, by rfl⟩ : syracuseStep 6627257 = 4970443) B4970443
theorem B4418171 : Blo 1963435 4418171 := bstep (se 1 (by rfl) ⟨3313628, by rfl⟩ : syracuseStep 4418171 = 6627257) B6627257
theorem B2945447 : Blo 1963435 2945447 := bstep (se 1 (by rfl) ⟨2209085, by rfl⟩ : syracuseStep 2945447 = 4418171) B4418171
theorem B1963631 : Blo 1963435 1963631 := bstep (se 1 (by rfl) ⟨1472723, by rfl⟩ : syracuseStep 1963631 = 2945447) B2945447
theorem B2945453 : Blo 1963435 2945453 := bbase (se 3 (by rfl) ⟨552272, by rfl⟩ : syracuseStep 2945453 = 1104545) (by norm_num)
theorem B1963635 : Blo 1963435 1963635 := bstep (se 1 (by rfl) ⟨1472726, by rfl⟩ : syracuseStep 1963635 = 2945453) B2945453
theorem B4418189 : Blo 1963435 4418189 := bbase (se 3 (by rfl) ⟨828410, by rfl⟩ : syracuseStep 4418189 = 1656821) (by norm_num)
theorem B2945459 : Blo 1963435 2945459 := bstep (se 1 (by rfl) ⟨2209094, by rfl⟩ : syracuseStep 2945459 = 4418189) B4418189
theorem B1963639 : Blo 1963435 1963639 := bstep (se 1 (by rfl) ⟨1472729, by rfl⟩ : syracuseStep 1963639 = 2945459) B2945459
theorem B2485237 : Blo 1963435 2485237 := bbase (se 5 (by rfl) ⟨116495, by rfl⟩ : syracuseStep 2485237 = 232991) (by norm_num)
theorem B3313649 : Blo 1963435 3313649 := bstep (se 2 (by rfl) ⟨1242618, by rfl⟩ : syracuseStep 3313649 = 2485237) B2485237
theorem B2209099 : Blo 1963435 2209099 := bstep (se 1 (by rfl) ⟨1656824, by rfl⟩ : syracuseStep 2209099 = 3313649) B3313649
theorem B2945465 : Blo 1963435 2945465 := bstep (se 2 (by rfl) ⟨1104549, by rfl⟩ : syracuseStep 2945465 = 2209099) B2209099
theorem B1963643 : Blo 1963435 1963643 := bstep (se 1 (by rfl) ⟨1472732, by rfl⟩ : syracuseStep 1963643 = 2945465) B2945465
theorem B25506389 : Blo 1963435 25506389 := bbase (se 8 (by rfl) ⟨149451, by rfl⟩ : syracuseStep 25506389 = 298903) (by norm_num)
theorem B17004259 : Blo 1963435 17004259 := bstep (se 1 (by rfl) ⟨12753194, by rfl⟩ : syracuseStep 17004259 = 25506389) B25506389
theorem B22672345 : Blo 1963435 22672345 := bstep (se 2 (by rfl) ⟨8502129, by rfl⟩ : syracuseStep 22672345 = 17004259) B17004259
theorem B30229793 : Blo 1963435 30229793 := bstep (se 2 (by rfl) ⟨11336172, by rfl⟩ : syracuseStep 30229793 = 22672345) B22672345
theorem B20153195 : Blo 1963435 20153195 := bstep (se 1 (by rfl) ⟨15114896, by rfl⟩ : syracuseStep 20153195 = 30229793) B30229793
theorem B13435463 : Blo 1963435 13435463 := bstep (se 1 (by rfl) ⟨10076597, by rfl⟩ : syracuseStep 13435463 = 20153195) B20153195
theorem B8956975 : Blo 1963435 8956975 := bstep (se 1 (by rfl) ⟨6717731, by rfl⟩ : syracuseStep 8956975 = 13435463) B13435463
theorem B11942633 : Blo 1963435 11942633 := bstep (se 2 (by rfl) ⟨4478487, by rfl⟩ : syracuseStep 11942633 = 8956975) B8956975
theorem B7961755 : Blo 1963435 7961755 := bstep (se 1 (by rfl) ⟨5971316, by rfl⟩ : syracuseStep 7961755 = 11942633) B11942633
theorem B10615673 : Blo 1963435 10615673 := bstep (se 2 (by rfl) ⟨3980877, by rfl⟩ : syracuseStep 10615673 = 7961755) B7961755
theorem B7077115 : Blo 1963435 7077115 := bstep (se 1 (by rfl) ⟨5307836, by rfl⟩ : syracuseStep 7077115 = 10615673) B10615673
theorem B37744613 : Blo 1963435 37744613 := bstep (se 4 (by rfl) ⟨3538557, by rfl⟩ : syracuseStep 37744613 = 7077115) B7077115
theorem B25163075 : Blo 1963435 25163075 := bstep (se 1 (by rfl) ⟨18872306, by rfl⟩ : syracuseStep 25163075 = 37744613) B37744613
theorem B16775383 : Blo 1963435 16775383 := bstep (se 1 (by rfl) ⟨12581537, by rfl⟩ : syracuseStep 16775383 = 25163075) B25163075
theorem B22367177 : Blo 1963435 22367177 := bstep (se 2 (by rfl) ⟨8387691, by rfl⟩ : syracuseStep 22367177 = 16775383) B16775383
theorem B14911451 : Blo 1963435 14911451 := bstep (se 1 (by rfl) ⟨11183588, by rfl⟩ : syracuseStep 14911451 = 22367177) B22367177
theorem B9940967 : Blo 1963435 9940967 := bstep (se 1 (by rfl) ⟨7455725, by rfl⟩ : syracuseStep 9940967 = 14911451) B14911451
theorem B6627311 : Blo 1963435 6627311 := bstep (se 1 (by rfl) ⟨4970483, by rfl⟩ : syracuseStep 6627311 = 9940967) B9940967
theorem B4418207 : Blo 1963435 4418207 := bstep (se 1 (by rfl) ⟨3313655, by rfl⟩ : syracuseStep 4418207 = 6627311) B6627311
theorem B2945471 : Blo 1963435 2945471 := bstep (se 1 (by rfl) ⟨2209103, by rfl⟩ : syracuseStep 2945471 = 4418207) B4418207
theorem B1963647 : Blo 1963435 1963647 := bstep (se 1 (by rfl) ⟨1472735, by rfl⟩ : syracuseStep 1963647 = 2945471) B2945471
theorem B2945477 : Blo 1963435 2945477 := bbase (se 4 (by rfl) ⟨276138, by rfl⟩ : syracuseStep 2945477 = 552277) (by norm_num)
theorem B1963651 : Blo 1963435 1963651 := bstep (se 1 (by rfl) ⟨1472738, by rfl⟩ : syracuseStep 1963651 = 2945477) B2945477
theorem B3313669 : Blo 1963435 3313669 := bbase (se 4 (by rfl) ⟨310656, by rfl⟩ : syracuseStep 3313669 = 621313) (by norm_num)
theorem B4418225 : Blo 1963435 4418225 := bstep (se 2 (by rfl) ⟨1656834, by rfl⟩ : syracuseStep 4418225 = 3313669) B3313669
theorem B2945483 : Blo 1963435 2945483 := bstep (se 1 (by rfl) ⟨2209112, by rfl⟩ : syracuseStep 2945483 = 4418225) B4418225
theorem B1963655 : Blo 1963435 1963655 := bstep (se 1 (by rfl) ⟨1472741, by rfl⟩ : syracuseStep 1963655 = 2945483) B2945483
theorem B2209117 : Blo 1963435 2209117 := bbase (se 3 (by rfl) ⟨414209, by rfl⟩ : syracuseStep 2209117 = 828419) (by norm_num)
theorem B2945489 : Blo 1963435 2945489 := bstep (se 2 (by rfl) ⟨1104558, by rfl⟩ : syracuseStep 2945489 = 2209117) B2209117
theorem B1963659 : Blo 1963435 1963659 := bstep (se 1 (by rfl) ⟨1472744, by rfl⟩ : syracuseStep 1963659 = 2945489) B2945489
theorem B6627365 : Blo 1963435 6627365 := bbase (se 4 (by rfl) ⟨621315, by rfl⟩ : syracuseStep 6627365 = 1242631) (by norm_num)
theorem B4418243 : Blo 1963435 4418243 := bstep (se 1 (by rfl) ⟨3313682, by rfl⟩ : syracuseStep 4418243 = 6627365) B6627365
theorem B2945495 : Blo 1963435 2945495 := bstep (se 1 (by rfl) ⟨2209121, by rfl⟩ : syracuseStep 2945495 = 4418243) B4418243
theorem B1963663 : Blo 1963435 1963663 := bstep (se 1 (by rfl) ⟨1472747, by rfl⟩ : syracuseStep 1963663 = 2945495) B2945495
theorem B2945501 : Blo 1963435 2945501 := bbase (se 3 (by rfl) ⟨552281, by rfl⟩ : syracuseStep 2945501 = 1104563) (by norm_num)
theorem B1963667 : Blo 1963435 1963667 := bstep (se 1 (by rfl) ⟨1472750, by rfl⟩ : syracuseStep 1963667 = 2945501) B2945501
theorem B4418261 : Blo 1963435 4418261 := bbase (se 7 (by rfl) ⟨51776, by rfl⟩ : syracuseStep 4418261 = 103553) (by norm_num)
theorem B2945507 : Blo 1963435 2945507 := bstep (se 1 (by rfl) ⟨2209130, by rfl⟩ : syracuseStep 2945507 = 4418261) B4418261
theorem B1963671 : Blo 1963435 1963671 := bstep (se 1 (by rfl) ⟨1472753, by rfl⟩ : syracuseStep 1963671 = 2945507) B2945507
theorem B8387813 : Blo 1963435 8387813 := bbase (se 4 (by rfl) ⟨786357, by rfl⟩ : syracuseStep 8387813 = 1572715) (by norm_num)
theorem B5591875 : Blo 1963435 5591875 := bstep (se 1 (by rfl) ⟨4193906, by rfl⟩ : syracuseStep 5591875 = 8387813) B8387813
theorem B7455833 : Blo 1963435 7455833 := bstep (se 2 (by rfl) ⟨2795937, by rfl⟩ : syracuseStep 7455833 = 5591875) B5591875
theorem B4970555 : Blo 1963435 4970555 := bstep (se 1 (by rfl) ⟨3727916, by rfl⟩ : syracuseStep 4970555 = 7455833) B7455833
theorem B3313703 : Blo 1963435 3313703 := bstep (se 1 (by rfl) ⟨2485277, by rfl⟩ : syracuseStep 3313703 = 4970555) B4970555
theorem B2209135 : Blo 1963435 2209135 := bstep (se 1 (by rfl) ⟨1656851, by rfl⟩ : syracuseStep 2209135 = 3313703) B3313703
theorem B2945513 : Blo 1963435 2945513 := bstep (se 2 (by rfl) ⟨1104567, by rfl⟩ : syracuseStep 2945513 = 2209135) B2209135
theorem B1963675 : Blo 1963435 1963675 := bstep (se 1 (by rfl) ⟨1472756, by rfl⟩ : syracuseStep 1963675 = 2945513) B2945513
theorem B2588401 : Blo 1963435 2588401 := bbase (se 2 (by rfl) ⟨970650, by rfl⟩ : syracuseStep 2588401 = 1941301) (by norm_num)
theorem B13804805 : Blo 1963435 13804805 := bstep (se 4 (by rfl) ⟨1294200, by rfl⟩ : syracuseStep 13804805 = 2588401) B2588401
theorem B9203203 : Blo 1963435 9203203 := bstep (se 1 (by rfl) ⟨6902402, by rfl⟩ : syracuseStep 9203203 = 13804805) B13804805
theorem B12270937 : Blo 1963435 12270937 := bstep (se 2 (by rfl) ⟨4601601, by rfl⟩ : syracuseStep 12270937 = 9203203) B9203203
theorem B16361249 : Blo 1963435 16361249 := bstep (se 2 (by rfl) ⟨6135468, by rfl⟩ : syracuseStep 16361249 = 12270937) B12270937
theorem B43629997 : Blo 1963435 43629997 := bstep (se 3 (by rfl) ⟨8180624, by rfl⟩ : syracuseStep 43629997 = 16361249) B16361249
theorem B58173329 : Blo 1963435 58173329 := bstep (se 2 (by rfl) ⟨21814998, by rfl⟩ : syracuseStep 58173329 = 43629997) B43629997
theorem B155128877 : Blo 1963435 155128877 := bstep (se 3 (by rfl) ⟨29086664, by rfl⟩ : syracuseStep 155128877 = 58173329) B58173329
theorem B103419251 : Blo 1963435 103419251 := bstep (se 1 (by rfl) ⟨77564438, by rfl⟩ : syracuseStep 103419251 = 155128877) B155128877
theorem B68946167 : Blo 1963435 68946167 := bstep (se 1 (by rfl) ⟨51709625, by rfl⟩ : syracuseStep 68946167 = 103419251) B103419251
theorem B45964111 : Blo 1963435 45964111 := bstep (se 1 (by rfl) ⟨34473083, by rfl⟩ : syracuseStep 45964111 = 68946167) B68946167
theorem B61285481 : Blo 1963435 61285481 := bstep (se 2 (by rfl) ⟨22982055, by rfl⟩ : syracuseStep 61285481 = 45964111) B45964111
theorem B40856987 : Blo 1963435 40856987 := bstep (se 1 (by rfl) ⟨30642740, by rfl⟩ : syracuseStep 40856987 = 61285481) B61285481
theorem B27237991 : Blo 1963435 27237991 := bstep (se 1 (by rfl) ⟨20428493, by rfl⟩ : syracuseStep 27237991 = 40856987) B40856987
theorem B36317321 : Blo 1963435 36317321 := bstep (se 2 (by rfl) ⟨13618995, by rfl⟩ : syracuseStep 36317321 = 27237991) B27237991
theorem B24211547 : Blo 1963435 24211547 := bstep (se 1 (by rfl) ⟨18158660, by rfl⟩ : syracuseStep 24211547 = 36317321) B36317321
theorem B16141031 : Blo 1963435 16141031 := bstep (se 1 (by rfl) ⟨12105773, by rfl⟩ : syracuseStep 16141031 = 24211547) B24211547
theorem B10760687 : Blo 1963435 10760687 := bstep (se 1 (by rfl) ⟨8070515, by rfl⟩ : syracuseStep 10760687 = 16141031) B16141031
theorem B7173791 : Blo 1963435 7173791 := bstep (se 1 (by rfl) ⟨5380343, by rfl⟩ : syracuseStep 7173791 = 10760687) B10760687
theorem B4782527 : Blo 1963435 4782527 := bstep (se 1 (by rfl) ⟨3586895, by rfl⟩ : syracuseStep 4782527 = 7173791) B7173791
theorem B3188351 : Blo 1963435 3188351 := bstep (se 1 (by rfl) ⟨2391263, by rfl⟩ : syracuseStep 3188351 = 4782527) B4782527
theorem B2125567 : Blo 1963435 2125567 := bstep (se 1 (by rfl) ⟨1594175, by rfl⟩ : syracuseStep 2125567 = 3188351) B3188351
theorem B11336357 : Blo 1963435 11336357 := bstep (se 4 (by rfl) ⟨1062783, by rfl⟩ : syracuseStep 11336357 = 2125567) B2125567
theorem B7557571 : Blo 1963435 7557571 := bstep (se 1 (by rfl) ⟨5668178, by rfl⟩ : syracuseStep 7557571 = 11336357) B11336357
theorem B10076761 : Blo 1963435 10076761 := bstep (se 2 (by rfl) ⟨3778785, by rfl⟩ : syracuseStep 10076761 = 7557571) B7557571
theorem B13435681 : Blo 1963435 13435681 := bstep (se 2 (by rfl) ⟨5038380, by rfl⟩ : syracuseStep 13435681 = 10076761) B10076761
theorem B17914241 : Blo 1963435 17914241 := bstep (se 2 (by rfl) ⟨6717840, by rfl⟩ : syracuseStep 17914241 = 13435681) B13435681
theorem B47771309 : Blo 1963435 47771309 := bstep (se 3 (by rfl) ⟨8957120, by rfl⟩ : syracuseStep 47771309 = 17914241) B17914241
theorem B31847539 : Blo 1963435 31847539 := bstep (se 1 (by rfl) ⟨23885654, by rfl⟩ : syracuseStep 31847539 = 47771309) B47771309
theorem B42463385 : Blo 1963435 42463385 := bstep (se 2 (by rfl) ⟨15923769, by rfl⟩ : syracuseStep 42463385 = 31847539) B31847539
theorem B28308923 : Blo 1963435 28308923 := bstep (se 1 (by rfl) ⟨21231692, by rfl⟩ : syracuseStep 28308923 = 42463385) B42463385
theorem B18872615 : Blo 1963435 18872615 := bstep (se 1 (by rfl) ⟨14154461, by rfl⟩ : syracuseStep 18872615 = 28308923) B28308923
theorem B12581743 : Blo 1963435 12581743 := bstep (se 1 (by rfl) ⟨9436307, by rfl⟩ : syracuseStep 12581743 = 18872615) B18872615
theorem B16775657 : Blo 1963435 16775657 := bstep (se 2 (by rfl) ⟨6290871, by rfl⟩ : syracuseStep 16775657 = 12581743) B12581743
theorem B11183771 : Blo 1963435 11183771 := bstep (se 1 (by rfl) ⟨8387828, by rfl⟩ : syracuseStep 11183771 = 16775657) B16775657
theorem B7455847 : Blo 1963435 7455847 := bstep (se 1 (by rfl) ⟨5591885, by rfl⟩ : syracuseStep 7455847 = 11183771) B11183771
theorem B9941129 : Blo 1963435 9941129 := bstep (se 2 (by rfl) ⟨3727923, by rfl⟩ : syracuseStep 9941129 = 7455847) B7455847
theorem B6627419 : Blo 1963435 6627419 := bstep (se 1 (by rfl) ⟨4970564, by rfl⟩ : syracuseStep 6627419 = 9941129) B9941129
theorem B4418279 : Blo 1963435 4418279 := bstep (se 1 (by rfl) ⟨3313709, by rfl⟩ : syracuseStep 4418279 = 6627419) B6627419
theorem B2945519 : Blo 1963435 2945519 := bstep (se 1 (by rfl) ⟨2209139, by rfl⟩ : syracuseStep 2945519 = 4418279) B4418279
theorem B1963679 : Blo 1963435 1963679 := bstep (se 1 (by rfl) ⟨1472759, by rfl⟩ : syracuseStep 1963679 = 2945519) B2945519
theorem B2945525 : Blo 1963435 2945525 := bbase (se 5 (by rfl) ⟨138071, by rfl⟩ : syracuseStep 2945525 = 276143) (by norm_num)
theorem B1963683 : Blo 1963435 1963683 := bstep (se 1 (by rfl) ⟨1472762, by rfl⟩ : syracuseStep 1963683 = 2945525) B2945525
theorem B5591909 : Blo 1963435 5591909 := bbase (se 4 (by rfl) ⟨524241, by rfl⟩ : syracuseStep 5591909 = 1048483) (by norm_num)
theorem B3727939 : Blo 1963435 3727939 := bstep (se 1 (by rfl) ⟨2795954, by rfl⟩ : syracuseStep 3727939 = 5591909) B5591909
theorem B4970585 : Blo 1963435 4970585 := bstep (se 2 (by rfl) ⟨1863969, by rfl⟩ : syracuseStep 4970585 = 3727939) B3727939
theorem B3313723 : Blo 1963435 3313723 := bstep (se 1 (by rfl) ⟨2485292, by rfl⟩ : syracuseStep 3313723 = 4970585) B4970585
theorem B4418297 : Blo 1963435 4418297 := bstep (se 2 (by rfl) ⟨1656861, by rfl⟩ : syracuseStep 4418297 = 3313723) B3313723
theorem B2945531 : Blo 1963435 2945531 := bstep (se 1 (by rfl) ⟨2209148, by rfl⟩ : syracuseStep 2945531 = 4418297) B4418297
theorem B1963687 : Blo 1963435 1963687 := bstep (se 1 (by rfl) ⟨1472765, by rfl⟩ : syracuseStep 1963687 = 2945531) B2945531
theorem B2209153 : Blo 1963435 2209153 := bbase (se 2 (by rfl) ⟨828432, by rfl⟩ : syracuseStep 2209153 = 1656865) (by norm_num)
theorem B2945537 : Blo 1963435 2945537 := bstep (se 2 (by rfl) ⟨1104576, by rfl⟩ : syracuseStep 2945537 = 2209153) B2209153
theorem B1963691 : Blo 1963435 1963691 := bstep (se 1 (by rfl) ⟨1472768, by rfl⟩ : syracuseStep 1963691 = 2945537) B2945537
theorem B4970605 : Blo 1963435 4970605 := bbase (se 3 (by rfl) ⟨931988, by rfl⟩ : syracuseStep 4970605 = 1863977) (by norm_num)
theorem B6627473 : Blo 1963435 6627473 := bstep (se 2 (by rfl) ⟨2485302, by rfl⟩ : syracuseStep 6627473 = 4970605) B4970605
theorem B4418315 : Blo 1963435 4418315 := bstep (se 1 (by rfl) ⟨3313736, by rfl⟩ : syracuseStep 4418315 = 6627473) B6627473
theorem B2945543 : Blo 1963435 2945543 := bstep (se 1 (by rfl) ⟨2209157, by rfl⟩ : syracuseStep 2945543 = 4418315) B4418315
theorem B1963695 : Blo 1963435 1963695 := bstep (se 1 (by rfl) ⟨1472771, by rfl⟩ : syracuseStep 1963695 = 2945543) B2945543
theorem B2945549 : Blo 1963435 2945549 := bbase (se 3 (by rfl) ⟨552290, by rfl⟩ : syracuseStep 2945549 = 1104581) (by norm_num)
theorem B1963699 : Blo 1963435 1963699 := bstep (se 1 (by rfl) ⟨1472774, by rfl⟩ : syracuseStep 1963699 = 2945549) B2945549
theorem B4418333 : Blo 1963435 4418333 := bbase (se 3 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 4418333 = 1656875) (by norm_num)
theorem B2945555 : Blo 1963435 2945555 := bstep (se 1 (by rfl) ⟨2209166, by rfl⟩ : syracuseStep 2945555 = 4418333) B4418333
theorem B1963703 : Blo 1963435 1963703 := bstep (se 1 (by rfl) ⟨1472777, by rfl⟩ : syracuseStep 1963703 = 2945555) B2945555
theorem B3313757 : Blo 1963435 3313757 := bbase (se 3 (by rfl) ⟨621329, by rfl⟩ : syracuseStep 3313757 = 1242659) (by norm_num)
theorem B2209171 : Blo 1963435 2209171 := bstep (se 1 (by rfl) ⟨1656878, by rfl⟩ : syracuseStep 2209171 = 3313757) B3313757
theorem B2945561 : Blo 1963435 2945561 := bstep (se 2 (by rfl) ⟨1104585, by rfl⟩ : syracuseStep 2945561 = 2209171) B2209171
theorem B1963707 : Blo 1963435 1963707 := bstep (se 1 (by rfl) ⟨1472780, by rfl⟩ : syracuseStep 1963707 = 2945561) B2945561
theorem B10616021 : Blo 1963435 10616021 := bbase (se 7 (by rfl) ⟨124406, by rfl⟩ : syracuseStep 10616021 = 248813) (by norm_num)
theorem B7077347 : Blo 1963435 7077347 := bstep (se 1 (by rfl) ⟨5308010, by rfl⟩ : syracuseStep 7077347 = 10616021) B10616021
theorem B4718231 : Blo 1963435 4718231 := bstep (se 1 (by rfl) ⟨3538673, by rfl⟩ : syracuseStep 4718231 = 7077347) B7077347
theorem B3145487 : Blo 1963435 3145487 := bstep (se 1 (by rfl) ⟨2359115, by rfl⟩ : syracuseStep 3145487 = 4718231) B4718231
theorem B8387965 : Blo 1963435 8387965 := bstep (se 3 (by rfl) ⟨1572743, by rfl⟩ : syracuseStep 8387965 = 3145487) B3145487
theorem B11183953 : Blo 1963435 11183953 := bstep (se 2 (by rfl) ⟨4193982, by rfl⟩ : syracuseStep 11183953 = 8387965) B8387965
theorem B14911937 : Blo 1963435 14911937 := bstep (se 2 (by rfl) ⟨5591976, by rfl⟩ : syracuseStep 14911937 = 11183953) B11183953
theorem B9941291 : Blo 1963435 9941291 := bstep (se 1 (by rfl) ⟨7455968, by rfl⟩ : syracuseStep 9941291 = 14911937) B14911937
theorem B6627527 : Blo 1963435 6627527 := bstep (se 1 (by rfl) ⟨4970645, by rfl⟩ : syracuseStep 6627527 = 9941291) B9941291
theorem B4418351 : Blo 1963435 4418351 := bstep (se 1 (by rfl) ⟨3313763, by rfl⟩ : syracuseStep 4418351 = 6627527) B6627527
theorem B2945567 : Blo 1963435 2945567 := bstep (se 1 (by rfl) ⟨2209175, by rfl⟩ : syracuseStep 2945567 = 4418351) B4418351
theorem B1963711 : Blo 1963435 1963711 := bstep (se 1 (by rfl) ⟨1472783, by rfl⟩ : syracuseStep 1963711 = 2945567) B2945567
theorem B2945573 : Blo 1963435 2945573 := bbase (se 4 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 2945573 = 552295) (by norm_num)
theorem B1963715 : Blo 1963435 1963715 := bstep (se 1 (by rfl) ⟨1472786, by rfl⟩ : syracuseStep 1963715 = 2945573) B2945573
theorem B2485333 : Blo 1963435 2485333 := bbase (se 8 (by rfl) ⟨14562, by rfl⟩ : syracuseStep 2485333 = 29125) (by norm_num)
theorem B3313777 : Blo 1963435 3313777 := bstep (se 2 (by rfl) ⟨1242666, by rfl⟩ : syracuseStep 3313777 = 2485333) B2485333
theorem B4418369 : Blo 1963435 4418369 := bstep (se 2 (by rfl) ⟨1656888, by rfl⟩ : syracuseStep 4418369 = 3313777) B3313777
theorem B2945579 : Blo 1963435 2945579 := bstep (se 1 (by rfl) ⟨2209184, by rfl⟩ : syracuseStep 2945579 = 4418369) B4418369
theorem B1963719 : Blo 1963435 1963719 := bstep (se 1 (by rfl) ⟨1472789, by rfl⟩ : syracuseStep 1963719 = 2945579) B2945579
theorem B2209189 : Blo 1963435 2209189 := bbase (se 4 (by rfl) ⟨207111, by rfl⟩ : syracuseStep 2209189 = 414223) (by norm_num)
theorem B2945585 : Blo 1963435 2945585 := bstep (se 2 (by rfl) ⟨1104594, by rfl⟩ : syracuseStep 2945585 = 2209189) B2209189
theorem B1963723 : Blo 1963435 1963723 := bstep (se 1 (by rfl) ⟨1472792, by rfl⟩ : syracuseStep 1963723 = 2945585) B2945585
theorem B11943125 : Blo 1963435 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B7962083 : Blo 1963435 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B5308055 : Blo 1963435 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B3538703 : Blo 1963435 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B2359135 : Blo 1963435 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B12582053 : Blo 1963435 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B8388035 : Blo 1963435 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B5592023 : Blo 1963435 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B3728015 : Blo 1963435 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B2485343 : Blo 1963435 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B6627581 : Blo 1963435 6627581 := bstep (se 3 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 6627581 = 2485343) B2485343
theorem B4418387 : Blo 1963435 4418387 := bstep (se 1 (by rfl) ⟨3313790, by rfl⟩ : syracuseStep 4418387 = 6627581) B6627581
theorem B2945591 : Blo 1963435 2945591 := bstep (se 1 (by rfl) ⟨2209193, by rfl⟩ : syracuseStep 2945591 = 4418387) B4418387
theorem B1963727 : Blo 1963435 1963727 := bstep (se 1 (by rfl) ⟨1472795, by rfl⟩ : syracuseStep 1963727 = 2945591) B2945591
theorem B2945597 : Blo 1963435 2945597 := bbase (se 3 (by rfl) ⟨552299, by rfl⟩ : syracuseStep 2945597 = 1104599) (by norm_num)
theorem B1963731 : Blo 1963435 1963731 := bstep (se 1 (by rfl) ⟨1472798, by rfl⟩ : syracuseStep 1963731 = 2945597) B2945597
theorem B4418405 : Blo 1963435 4418405 := bbase (se 4 (by rfl) ⟨414225, by rfl⟩ : syracuseStep 4418405 = 828451) (by norm_num)
theorem B2945603 : Blo 1963435 2945603 := bstep (se 1 (by rfl) ⟨2209202, by rfl⟩ : syracuseStep 2945603 = 4418405) B4418405
theorem B1963735 : Blo 1963435 1963735 := bstep (se 1 (by rfl) ⟨1472801, by rfl⟩ : syracuseStep 1963735 = 2945603) B2945603
theorem B4970717 : Blo 1963435 4970717 := bbase (se 3 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 4970717 = 1864019) (by norm_num)
theorem B3313811 : Blo 1963435 3313811 := bstep (se 1 (by rfl) ⟨2485358, by rfl⟩ : syracuseStep 3313811 = 4970717) B4970717
theorem B2209207 : Blo 1963435 2209207 := bstep (se 1 (by rfl) ⟨1656905, by rfl⟩ : syracuseStep 2209207 = 3313811) B3313811
theorem B2945609 : Blo 1963435 2945609 := bstep (se 2 (by rfl) ⟨1104603, by rfl⟩ : syracuseStep 2945609 = 2209207) B2209207
theorem B1963739 : Blo 1963435 1963739 := bstep (se 1 (by rfl) ⟨1472804, by rfl⟩ : syracuseStep 1963739 = 2945609) B2945609
theorem B3728045 : Blo 1963435 3728045 := bbase (se 3 (by rfl) ⟨699008, by rfl⟩ : syracuseStep 3728045 = 1398017) (by norm_num)
theorem B9941453 : Blo 1963435 9941453 := bstep (se 3 (by rfl) ⟨1864022, by rfl⟩ : syracuseStep 9941453 = 3728045) B3728045
theorem B6627635 : Blo 1963435 6627635 := bstep (se 1 (by rfl) ⟨4970726, by rfl⟩ : syracuseStep 6627635 = 9941453) B9941453
theorem B4418423 : Blo 1963435 4418423 := bstep (se 1 (by rfl) ⟨3313817, by rfl⟩ : syracuseStep 4418423 = 6627635) B6627635
theorem B2945615 : Blo 1963435 2945615 := bstep (se 1 (by rfl) ⟨2209211, by rfl⟩ : syracuseStep 2945615 = 4418423) B4418423
theorem B1963743 : Blo 1963435 1963743 := bstep (se 1 (by rfl) ⟨1472807, by rfl⟩ : syracuseStep 1963743 = 2945615) B2945615
theorem B2945621 : Blo 1963435 2945621 := bbase (se 8 (by rfl) ⟨17259, by rfl⟩ : syracuseStep 2945621 = 34519) (by norm_num)
theorem B1963747 : Blo 1963435 1963747 := bstep (se 1 (by rfl) ⟨1472810, by rfl⟩ : syracuseStep 1963747 = 2945621) B2945621
theorem B8502581 : Blo 1963435 8502581 := bbase (se 5 (by rfl) ⟨398558, by rfl⟩ : syracuseStep 8502581 = 797117) (by norm_num)
theorem B5668387 : Blo 1963435 5668387 := bstep (se 1 (by rfl) ⟨4251290, by rfl⟩ : syracuseStep 5668387 = 8502581) B8502581
theorem B30231397 : Blo 1963435 30231397 := bstep (se 4 (by rfl) ⟨2834193, by rfl⟩ : syracuseStep 30231397 = 5668387) B5668387
theorem B40308529 : Blo 1963435 40308529 := bstep (se 2 (by rfl) ⟨15115698, by rfl⟩ : syracuseStep 40308529 = 30231397) B30231397
theorem B53744705 : Blo 1963435 53744705 := bstep (se 2 (by rfl) ⟨20154264, by rfl⟩ : syracuseStep 53744705 = 40308529) B40308529
theorem B35829803 : Blo 1963435 35829803 := bstep (se 1 (by rfl) ⟨26872352, by rfl⟩ : syracuseStep 35829803 = 53744705) B53744705
theorem B23886535 : Blo 1963435 23886535 := bstep (se 1 (by rfl) ⟨17914901, by rfl⟩ : syracuseStep 23886535 = 35829803) B35829803
theorem B31848713 : Blo 1963435 31848713 := bstep (se 2 (by rfl) ⟨11943267, by rfl⟩ : syracuseStep 31848713 = 23886535) B23886535
theorem B21232475 : Blo 1963435 21232475 := bstep (se 1 (by rfl) ⟨15924356, by rfl⟩ : syracuseStep 21232475 = 31848713) B31848713
theorem B14154983 : Blo 1963435 14154983 := bstep (se 1 (by rfl) ⟨10616237, by rfl⟩ : syracuseStep 14154983 = 21232475) B21232475
theorem B9436655 : Blo 1963435 9436655 := bstep (se 1 (by rfl) ⟨7077491, by rfl⟩ : syracuseStep 9436655 = 14154983) B14154983
theorem B6291103 : Blo 1963435 6291103 := bstep (se 1 (by rfl) ⟨4718327, by rfl⟩ : syracuseStep 6291103 = 9436655) B9436655
theorem B8388137 : Blo 1963435 8388137 := bstep (se 2 (by rfl) ⟨3145551, by rfl⟩ : syracuseStep 8388137 = 6291103) B6291103
theorem B5592091 : Blo 1963435 5592091 := bstep (se 1 (by rfl) ⟨4194068, by rfl⟩ : syracuseStep 5592091 = 8388137) B8388137
theorem B7456121 : Blo 1963435 7456121 := bstep (se 2 (by rfl) ⟨2796045, by rfl⟩ : syracuseStep 7456121 = 5592091) B5592091
theorem B4970747 : Blo 1963435 4970747 := bstep (se 1 (by rfl) ⟨3728060, by rfl⟩ : syracuseStep 4970747 = 7456121) B7456121
theorem B3313831 : Blo 1963435 3313831 := bstep (se 1 (by rfl) ⟨2485373, by rfl⟩ : syracuseStep 3313831 = 4970747) B4970747
theorem B4418441 : Blo 1963435 4418441 := bstep (se 2 (by rfl) ⟨1656915, by rfl⟩ : syracuseStep 4418441 = 3313831) B3313831
theorem B2945627 : Blo 1963435 2945627 := bstep (se 1 (by rfl) ⟨2209220, by rfl⟩ : syracuseStep 2945627 = 4418441) B4418441
theorem B1963751 : Blo 1963435 1963751 := bstep (se 1 (by rfl) ⟨1472813, by rfl⟩ : syracuseStep 1963751 = 2945627) B2945627
theorem B2209225 : Blo 1963435 2209225 := bbase (se 2 (by rfl) ⟨828459, by rfl⟩ : syracuseStep 2209225 = 1656919) (by norm_num)
theorem B2945633 : Blo 1963435 2945633 := bstep (se 2 (by rfl) ⟨1104612, by rfl⟩ : syracuseStep 2945633 = 2209225) B2209225
theorem B1963755 : Blo 1963435 1963755 := bstep (se 1 (by rfl) ⟨1472816, by rfl⟩ : syracuseStep 1963755 = 2945633) B2945633
theorem B16776341 : Blo 1963435 16776341 := bbase (se 6 (by rfl) ⟨393195, by rfl⟩ : syracuseStep 16776341 = 786391) (by norm_num)
theorem B11184227 : Blo 1963435 11184227 := bstep (se 1 (by rfl) ⟨8388170, by rfl⟩ : syracuseStep 11184227 = 16776341) B16776341
theorem B7456151 : Blo 1963435 7456151 := bstep (se 1 (by rfl) ⟨5592113, by rfl⟩ : syracuseStep 7456151 = 11184227) B11184227
theorem B4970767 : Blo 1963435 4970767 := bstep (se 1 (by rfl) ⟨3728075, by rfl⟩ : syracuseStep 4970767 = 7456151) B7456151
theorem B6627689 : Blo 1963435 6627689 := bstep (se 2 (by rfl) ⟨2485383, by rfl⟩ : syracuseStep 6627689 = 4970767) B4970767
theorem B4418459 : Blo 1963435 4418459 := bstep (se 1 (by rfl) ⟨3313844, by rfl⟩ : syracuseStep 4418459 = 6627689) B6627689
theorem B2945639 : Blo 1963435 2945639 := bstep (se 1 (by rfl) ⟨2209229, by rfl⟩ : syracuseStep 2945639 = 4418459) B4418459
theorem B1963759 : Blo 1963435 1963759 := bstep (se 1 (by rfl) ⟨1472819, by rfl⟩ : syracuseStep 1963759 = 2945639) B2945639
theorem B2945645 : Blo 1963435 2945645 := bbase (se 3 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 2945645 = 1104617) (by norm_num)
theorem B1963763 : Blo 1963435 1963763 := bstep (se 1 (by rfl) ⟨1472822, by rfl⟩ : syracuseStep 1963763 = 2945645) B2945645
theorem B4418477 : Blo 1963435 4418477 := bbase (se 3 (by rfl) ⟨828464, by rfl⟩ : syracuseStep 4418477 = 1656929) (by norm_num)
theorem B2945651 : Blo 1963435 2945651 := bstep (se 1 (by rfl) ⟨2209238, by rfl⟩ : syracuseStep 2945651 = 4418477) B4418477
theorem B1963767 : Blo 1963435 1963767 := bstep (se 1 (by rfl) ⟨1472825, by rfl⟩ : syracuseStep 1963767 = 2945651) B2945651
theorem B5592149 : Blo 1963435 5592149 := bbase (se 8 (by rfl) ⟨32766, by rfl⟩ : syracuseStep 5592149 = 65533) (by norm_num)
theorem B3728099 : Blo 1963435 3728099 := bstep (se 1 (by rfl) ⟨2796074, by rfl⟩ : syracuseStep 3728099 = 5592149) B5592149
theorem B2485399 : Blo 1963435 2485399 := bstep (se 1 (by rfl) ⟨1864049, by rfl⟩ : syracuseStep 2485399 = 3728099) B3728099
theorem B3313865 : Blo 1963435 3313865 := bstep (se 2 (by rfl) ⟨1242699, by rfl⟩ : syracuseStep 3313865 = 2485399) B2485399
theorem B2209243 : Blo 1963435 2209243 := bstep (se 1 (by rfl) ⟨1656932, by rfl⟩ : syracuseStep 2209243 = 3313865) B3313865
theorem B2945657 : Blo 1963435 2945657 := bstep (se 2 (by rfl) ⟨1104621, by rfl⟩ : syracuseStep 2945657 = 2209243) B2209243
theorem B1963771 : Blo 1963435 1963771 := bstep (se 1 (by rfl) ⟨1472828, by rfl⟩ : syracuseStep 1963771 = 2945657) B2945657
theorem B7557941 : Blo 1963435 7557941 := bbase (se 5 (by rfl) ⟨354278, by rfl⟩ : syracuseStep 7557941 = 708557) (by norm_num)
theorem B5038627 : Blo 1963435 5038627 := bstep (se 1 (by rfl) ⟨3778970, by rfl⟩ : syracuseStep 5038627 = 7557941) B7557941
theorem B6718169 : Blo 1963435 6718169 := bstep (se 2 (by rfl) ⟨2519313, by rfl⟩ : syracuseStep 6718169 = 5038627) B5038627
theorem B4478779 : Blo 1963435 4478779 := bstep (se 1 (by rfl) ⟨3359084, by rfl⟩ : syracuseStep 4478779 = 6718169) B6718169
theorem B23886821 : Blo 1963435 23886821 := bstep (se 4 (by rfl) ⟨2239389, by rfl⟩ : syracuseStep 23886821 = 4478779) B4478779
theorem B15924547 : Blo 1963435 15924547 := bstep (se 1 (by rfl) ⟨11943410, by rfl⟩ : syracuseStep 15924547 = 23886821) B23886821
theorem B21232729 : Blo 1963435 21232729 := bstep (se 2 (by rfl) ⟨7962273, by rfl⟩ : syracuseStep 21232729 = 15924547) B15924547
theorem B28310305 : Blo 1963435 28310305 := bstep (se 2 (by rfl) ⟨10616364, by rfl⟩ : syracuseStep 28310305 = 21232729) B21232729
theorem B37747073 : Blo 1963435 37747073 := bstep (se 2 (by rfl) ⟨14155152, by rfl⟩ : syracuseStep 37747073 = 28310305) B28310305
theorem B25164715 : Blo 1963435 25164715 := bstep (se 1 (by rfl) ⟨18873536, by rfl⟩ : syracuseStep 25164715 = 37747073) B37747073
theorem B33552953 : Blo 1963435 33552953 := bstep (se 2 (by rfl) ⟨12582357, by rfl⟩ : syracuseStep 33552953 = 25164715) B25164715
theorem B22368635 : Blo 1963435 22368635 := bstep (se 1 (by rfl) ⟨16776476, by rfl⟩ : syracuseStep 22368635 = 33552953) B33552953
theorem B14912423 : Blo 1963435 14912423 := bstep (se 1 (by rfl) ⟨11184317, by rfl⟩ : syracuseStep 14912423 = 22368635) B22368635
theorem B9941615 : Blo 1963435 9941615 := bstep (se 1 (by rfl) ⟨7456211, by rfl⟩ : syracuseStep 9941615 = 14912423) B14912423
theorem B6627743 : Blo 1963435 6627743 := bstep (se 1 (by rfl) ⟨4970807, by rfl⟩ : syracuseStep 6627743 = 9941615) B9941615
theorem B4418495 : Blo 1963435 4418495 := bstep (se 1 (by rfl) ⟨3313871, by rfl⟩ : syracuseStep 4418495 = 6627743) B6627743
theorem B2945663 : Blo 1963435 2945663 := bstep (se 1 (by rfl) ⟨2209247, by rfl⟩ : syracuseStep 2945663 = 4418495) B4418495
theorem B1963775 : Blo 1963435 1963775 := bstep (se 1 (by rfl) ⟨1472831, by rfl⟩ : syracuseStep 1963775 = 2945663) B2945663
theorem B2945669 : Blo 1963435 2945669 := bbase (se 4 (by rfl) ⟨276156, by rfl⟩ : syracuseStep 2945669 = 552313) (by norm_num)
theorem B1963779 : Blo 1963435 1963779 := bstep (se 1 (by rfl) ⟨1472834, by rfl⟩ : syracuseStep 1963779 = 2945669) B2945669
theorem B3313885 : Blo 1963435 3313885 := bbase (se 3 (by rfl) ⟨621353, by rfl⟩ : syracuseStep 3313885 = 1242707) (by norm_num)
theorem B4418513 : Blo 1963435 4418513 := bstep (se 2 (by rfl) ⟨1656942, by rfl⟩ : syracuseStep 4418513 = 3313885) B3313885
theorem B2945675 : Blo 1963435 2945675 := bstep (se 1 (by rfl) ⟨2209256, by rfl⟩ : syracuseStep 2945675 = 4418513) B4418513
theorem B1963783 : Blo 1963435 1963783 := bstep (se 1 (by rfl) ⟨1472837, by rfl⟩ : syracuseStep 1963783 = 2945675) B2945675
theorem B2209261 : Blo 1963435 2209261 := bbase (se 3 (by rfl) ⟨414236, by rfl⟩ : syracuseStep 2209261 = 828473) (by norm_num)
theorem B2945681 : Blo 1963435 2945681 := bstep (se 2 (by rfl) ⟨1104630, by rfl⟩ : syracuseStep 2945681 = 2209261) B2209261
theorem B1963787 : Blo 1963435 1963787 := bstep (se 1 (by rfl) ⟨1472840, by rfl⟩ : syracuseStep 1963787 = 2945681) B2945681
theorem B6627797 : Blo 1963435 6627797 := bbase (se 7 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 6627797 = 155339) (by norm_num)
theorem B4418531 : Blo 1963435 4418531 := bstep (se 1 (by rfl) ⟨3313898, by rfl⟩ : syracuseStep 4418531 = 6627797) B6627797
theorem B2945687 : Blo 1963435 2945687 := bstep (se 1 (by rfl) ⟨2209265, by rfl⟩ : syracuseStep 2945687 = 4418531) B4418531
theorem B1963791 : Blo 1963435 1963791 := bstep (se 1 (by rfl) ⟨1472843, by rfl⟩ : syracuseStep 1963791 = 2945687) B2945687
theorem B2945693 : Blo 1963435 2945693 := bbase (se 3 (by rfl) ⟨552317, by rfl⟩ : syracuseStep 2945693 = 1104635) (by norm_num)
theorem B1963795 : Blo 1963435 1963795 := bstep (se 1 (by rfl) ⟨1472846, by rfl⟩ : syracuseStep 1963795 = 2945693) B2945693
theorem B4418549 : Blo 1963435 4418549 := bbase (se 5 (by rfl) ⟨207119, by rfl⟩ : syracuseStep 4418549 = 414239) (by norm_num)
theorem B2945699 : Blo 1963435 2945699 := bstep (se 1 (by rfl) ⟨2209274, by rfl⟩ : syracuseStep 2945699 = 4418549) B4418549
theorem B1963799 : Blo 1963435 1963799 := bstep (se 1 (by rfl) ⟨1472849, by rfl⟩ : syracuseStep 1963799 = 2945699) B2945699
theorem B7962389 : Blo 1963435 7962389 := bbase (se 6 (by rfl) ⟨186618, by rfl⟩ : syracuseStep 7962389 = 373237) (by norm_num)
theorem B5308259 : Blo 1963435 5308259 := bstep (se 1 (by rfl) ⟨3981194, by rfl⟩ : syracuseStep 5308259 = 7962389) B7962389
theorem B56621429 : Blo 1963435 56621429 := bstep (se 5 (by rfl) ⟨2654129, by rfl⟩ : syracuseStep 56621429 = 5308259) B5308259
theorem B37747619 : Blo 1963435 37747619 := bstep (se 1 (by rfl) ⟨28310714, by rfl⟩ : syracuseStep 37747619 = 56621429) B56621429
theorem B25165079 : Blo 1963435 25165079 := bstep (se 1 (by rfl) ⟨18873809, by rfl⟩ : syracuseStep 25165079 = 37747619) B37747619
theorem B16776719 : Blo 1963435 16776719 := bstep (se 1 (by rfl) ⟨12582539, by rfl⟩ : syracuseStep 16776719 = 25165079) B25165079
theorem B11184479 : Blo 1963435 11184479 := bstep (se 1 (by rfl) ⟨8388359, by rfl⟩ : syracuseStep 11184479 = 16776719) B16776719
theorem B7456319 : Blo 1963435 7456319 := bstep (se 1 (by rfl) ⟨5592239, by rfl⟩ : syracuseStep 7456319 = 11184479) B11184479
theorem B4970879 : Blo 1963435 4970879 := bstep (se 1 (by rfl) ⟨3728159, by rfl⟩ : syracuseStep 4970879 = 7456319) B7456319
theorem B3313919 : Blo 1963435 3313919 := bstep (se 1 (by rfl) ⟨2485439, by rfl⟩ : syracuseStep 3313919 = 4970879) B4970879
theorem B2209279 : Blo 1963435 2209279 := bstep (se 1 (by rfl) ⟨1656959, by rfl⟩ : syracuseStep 2209279 = 3313919) B3313919
theorem B2945705 : Blo 1963435 2945705 := bstep (se 2 (by rfl) ⟨1104639, by rfl⟩ : syracuseStep 2945705 = 2209279) B2209279
theorem B1963803 : Blo 1963435 1963803 := bstep (se 1 (by rfl) ⟨1472852, by rfl⟩ : syracuseStep 1963803 = 2945705) B2945705
theorem B2796125 : Blo 1963435 2796125 := bbase (se 3 (by rfl) ⟨524273, by rfl⟩ : syracuseStep 2796125 = 1048547) (by norm_num)
theorem B7456333 : Blo 1963435 7456333 := bstep (se 3 (by rfl) ⟨1398062, by rfl⟩ : syracuseStep 7456333 = 2796125) B2796125
theorem B9941777 : Blo 1963435 9941777 := bstep (se 2 (by rfl) ⟨3728166, by rfl⟩ : syracuseStep 9941777 = 7456333) B7456333
theorem B6627851 : Blo 1963435 6627851 := bstep (se 1 (by rfl) ⟨4970888, by rfl⟩ : syracuseStep 6627851 = 9941777) B9941777
theorem B4418567 : Blo 1963435 4418567 := bstep (se 1 (by rfl) ⟨3313925, by rfl⟩ : syracuseStep 4418567 = 6627851) B6627851
theorem B2945711 : Blo 1963435 2945711 := bstep (se 1 (by rfl) ⟨2209283, by rfl⟩ : syracuseStep 2945711 = 4418567) B4418567
theorem B1963807 : Blo 1963435 1963807 := bstep (se 1 (by rfl) ⟨1472855, by rfl⟩ : syracuseStep 1963807 = 2945711) B2945711
theorem B2945717 : Blo 1963435 2945717 := bbase (se 5 (by rfl) ⟨138080, by rfl⟩ : syracuseStep 2945717 = 276161) (by norm_num)
theorem B1963811 : Blo 1963435 1963811 := bstep (se 1 (by rfl) ⟨1472858, by rfl⟩ : syracuseStep 1963811 = 2945717) B2945717
theorem B4970909 : Blo 1963435 4970909 := bbase (se 3 (by rfl) ⟨932045, by rfl⟩ : syracuseStep 4970909 = 1864091) (by norm_num)
theorem B3313939 : Blo 1963435 3313939 := bstep (se 1 (by rfl) ⟨2485454, by rfl⟩ : syracuseStep 3313939 = 4970909) B4970909
theorem B4418585 : Blo 1963435 4418585 := bstep (se 2 (by rfl) ⟨1656969, by rfl⟩ : syracuseStep 4418585 = 3313939) B3313939
theorem B2945723 : Blo 1963435 2945723 := bstep (se 1 (by rfl) ⟨2209292, by rfl⟩ : syracuseStep 2945723 = 4418585) B4418585
theorem B1963815 : Blo 1963435 1963815 := bstep (se 1 (by rfl) ⟨1472861, by rfl⟩ : syracuseStep 1963815 = 2945723) B2945723
theorem B2209297 : Blo 1963435 2209297 := bbase (se 2 (by rfl) ⟨828486, by rfl⟩ : syracuseStep 2209297 = 1656973) (by norm_num)
theorem B2945729 : Blo 1963435 2945729 := bstep (se 2 (by rfl) ⟨1104648, by rfl⟩ : syracuseStep 2945729 = 2209297) B2209297
theorem B1963819 : Blo 1963435 1963819 := bstep (se 1 (by rfl) ⟨1472864, by rfl⟩ : syracuseStep 1963819 = 2945729) B2945729
theorem B3728197 : Blo 1963435 3728197 := bbase (se 4 (by rfl) ⟨349518, by rfl⟩ : syracuseStep 3728197 = 699037) (by norm_num)
theorem B4970929 : Blo 1963435 4970929 := bstep (se 2 (by rfl) ⟨1864098, by rfl⟩ : syracuseStep 4970929 = 3728197) B3728197
theorem B6627905 : Blo 1963435 6627905 := bstep (se 2 (by rfl) ⟨2485464, by rfl⟩ : syracuseStep 6627905 = 4970929) B4970929
theorem B4418603 : Blo 1963435 4418603 := bstep (se 1 (by rfl) ⟨3313952, by rfl⟩ : syracuseStep 4418603 = 6627905) B6627905
theorem B2945735 : Blo 1963435 2945735 := bstep (se 1 (by rfl) ⟨2209301, by rfl⟩ : syracuseStep 2945735 = 4418603) B4418603
theorem B1963823 : Blo 1963435 1963823 := bstep (se 1 (by rfl) ⟨1472867, by rfl⟩ : syracuseStep 1963823 = 2945735) B2945735
theorem B2945741 : Blo 1963435 2945741 := bbase (se 3 (by rfl) ⟨552326, by rfl⟩ : syracuseStep 2945741 = 1104653) (by norm_num)
theorem B1963827 : Blo 1963435 1963827 := bstep (se 1 (by rfl) ⟨1472870, by rfl⟩ : syracuseStep 1963827 = 2945741) B2945741
theorem B4418621 : Blo 1963435 4418621 := bbase (se 3 (by rfl) ⟨828491, by rfl⟩ : syracuseStep 4418621 = 1656983) (by norm_num)
theorem B2945747 : Blo 1963435 2945747 := bstep (se 1 (by rfl) ⟨2209310, by rfl⟩ : syracuseStep 2945747 = 4418621) B4418621
theorem B1963831 : Blo 1963435 1963831 := bstep (se 1 (by rfl) ⟨1472873, by rfl⟩ : syracuseStep 1963831 = 2945747) B2945747
theorem B3313973 : Blo 1963435 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B2209315 : Blo 1963435 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B2945753 : Blo 1963435 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B1963835 : Blo 1963435 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B5592341 : Blo 1963435 5592341 := bbase (se 6 (by rfl) ⟨131070, by rfl⟩ : syracuseStep 5592341 = 262141) (by norm_num)
theorem B14912909 : Blo 1963435 14912909 := bstep (se 3 (by rfl) ⟨2796170, by rfl⟩ : syracuseStep 14912909 = 5592341) B5592341
theorem B9941939 : Blo 1963435 9941939 := bstep (se 1 (by rfl) ⟨7456454, by rfl⟩ : syracuseStep 9941939 = 14912909) B14912909
theorem B6627959 : Blo 1963435 6627959 := bstep (se 1 (by rfl) ⟨4970969, by rfl⟩ : syracuseStep 6627959 = 9941939) B9941939
theorem B4418639 : Blo 1963435 4418639 := bstep (se 1 (by rfl) ⟨3313979, by rfl⟩ : syracuseStep 4418639 = 6627959) B6627959
theorem B2945759 : Blo 1963435 2945759 := bstep (se 1 (by rfl) ⟨2209319, by rfl⟩ : syracuseStep 2945759 = 4418639) B4418639
theorem B1963839 : Blo 1963435 1963839 := bstep (se 1 (by rfl) ⟨1472879, by rfl⟩ : syracuseStep 1963839 = 2945759) B2945759
theorem B2945765 : Blo 1963435 2945765 := bbase (se 4 (by rfl) ⟨276165, by rfl⟩ : syracuseStep 2945765 = 552331) (by norm_num)
theorem B1963843 : Blo 1963435 1963843 := bstep (se 1 (by rfl) ⟨1472882, by rfl⟩ : syracuseStep 1963843 = 2945765) B2945765
theorem B2097137 : Blo 1963435 2097137 := bbase (se 2 (by rfl) ⟨786426, by rfl⟩ : syracuseStep 2097137 = 1572853) (by norm_num)
theorem B5592365 : Blo 1963435 5592365 := bstep (se 3 (by rfl) ⟨1048568, by rfl⟩ : syracuseStep 5592365 = 2097137) B2097137
theorem B3728243 : Blo 1963435 3728243 := bstep (se 1 (by rfl) ⟨2796182, by rfl⟩ : syracuseStep 3728243 = 5592365) B5592365
theorem B2485495 : Blo 1963435 2485495 := bstep (se 1 (by rfl) ⟨1864121, by rfl⟩ : syracuseStep 2485495 = 3728243) B3728243
theorem B3313993 : Blo 1963435 3313993 := bstep (se 2 (by rfl) ⟨1242747, by rfl⟩ : syracuseStep 3313993 = 2485495) B2485495
theorem B4418657 : Blo 1963435 4418657 := bstep (se 2 (by rfl) ⟨1656996, by rfl⟩ : syracuseStep 4418657 = 3313993) B3313993
theorem B2945771 : Blo 1963435 2945771 := bstep (se 1 (by rfl) ⟨2209328, by rfl⟩ : syracuseStep 2945771 = 4418657) B4418657
theorem B1963847 : Blo 1963435 1963847 := bstep (se 1 (by rfl) ⟨1472885, by rfl⟩ : syracuseStep 1963847 = 2945771) B2945771
theorem B2209333 : Blo 1963435 2209333 := bbase (se 5 (by rfl) ⟨103562, by rfl⟩ : syracuseStep 2209333 = 207125) (by norm_num)
theorem B2945777 : Blo 1963435 2945777 := bstep (se 2 (by rfl) ⟨1104666, by rfl⟩ : syracuseStep 2945777 = 2209333) B2209333
theorem B1963851 : Blo 1963435 1963851 := bstep (se 1 (by rfl) ⟨1472888, by rfl⟩ : syracuseStep 1963851 = 2945777) B2945777
theorem B2485505 : Blo 1963435 2485505 := bbase (se 2 (by rfl) ⟨932064, by rfl⟩ : syracuseStep 2485505 = 1864129) (by norm_num)
theorem B6628013 : Blo 1963435 6628013 := bstep (se 3 (by rfl) ⟨1242752, by rfl⟩ : syracuseStep 6628013 = 2485505) B2485505
theorem B4418675 : Blo 1963435 4418675 := bstep (se 1 (by rfl) ⟨3314006, by rfl⟩ : syracuseStep 4418675 = 6628013) B6628013
theorem B2945783 : Blo 1963435 2945783 := bstep (se 1 (by rfl) ⟨2209337, by rfl⟩ : syracuseStep 2945783 = 4418675) B4418675
theorem B1963855 : Blo 1963435 1963855 := bstep (se 1 (by rfl) ⟨1472891, by rfl⟩ : syracuseStep 1963855 = 2945783) B2945783
theorem B2945789 : Blo 1963435 2945789 := bbase (se 3 (by rfl) ⟨552335, by rfl⟩ : syracuseStep 2945789 = 1104671) (by norm_num)
theorem B1963859 : Blo 1963435 1963859 := bstep (se 1 (by rfl) ⟨1472894, by rfl⟩ : syracuseStep 1963859 = 2945789) B2945789
theorem B4418693 : Blo 1963435 4418693 := bbase (se 4 (by rfl) ⟨414252, by rfl⟩ : syracuseStep 4418693 = 828505) (by norm_num)
theorem B2945795 : Blo 1963435 2945795 := bstep (se 1 (by rfl) ⟨2209346, by rfl⟩ : syracuseStep 2945795 = 4418693) B4418693
theorem B1963863 : Blo 1963435 1963863 := bstep (se 1 (by rfl) ⟨1472897, by rfl⟩ : syracuseStep 1963863 = 2945795) B2945795
theorem B4194317 : Blo 1963435 4194317 := bbase (se 3 (by rfl) ⟨786434, by rfl⟩ : syracuseStep 4194317 = 1572869) (by norm_num)
theorem B2796211 : Blo 1963435 2796211 := bstep (se 1 (by rfl) ⟨2097158, by rfl⟩ : syracuseStep 2796211 = 4194317) B4194317
theorem B3728281 : Blo 1963435 3728281 := bstep (se 2 (by rfl) ⟨1398105, by rfl⟩ : syracuseStep 3728281 = 2796211) B2796211
theorem B4971041 : Blo 1963435 4971041 := bstep (se 2 (by rfl) ⟨1864140, by rfl⟩ : syracuseStep 4971041 = 3728281) B3728281
theorem B3314027 : Blo 1963435 3314027 := bstep (se 1 (by rfl) ⟨2485520, by rfl⟩ : syracuseStep 3314027 = 4971041) B4971041
theorem B2209351 : Blo 1963435 2209351 := bstep (se 1 (by rfl) ⟨1657013, by rfl⟩ : syracuseStep 2209351 = 3314027) B3314027
theorem B2945801 : Blo 1963435 2945801 := bstep (se 2 (by rfl) ⟨1104675, by rfl⟩ : syracuseStep 2945801 = 2209351) B2209351
theorem B1963867 : Blo 1963435 1963867 := bstep (se 1 (by rfl) ⟨1472900, by rfl⟩ : syracuseStep 1963867 = 2945801) B2945801
theorem B9942101 : Blo 1963435 9942101 := bbase (se 8 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 9942101 = 116509) (by norm_num)
theorem B6628067 : Blo 1963435 6628067 := bstep (se 1 (by rfl) ⟨4971050, by rfl⟩ : syracuseStep 6628067 = 9942101) B9942101
theorem B4418711 : Blo 1963435 4418711 := bstep (se 1 (by rfl) ⟨3314033, by rfl⟩ : syracuseStep 4418711 = 6628067) B6628067
theorem B2945807 : Blo 1963435 2945807 := bstep (se 1 (by rfl) ⟨2209355, by rfl⟩ : syracuseStep 2945807 = 4418711) B4418711
theorem B1963871 : Blo 1963435 1963871 := bstep (se 1 (by rfl) ⟨1472903, by rfl⟩ : syracuseStep 1963871 = 2945807) B2945807
theorem B2945813 : Blo 1963435 2945813 := bbase (se 6 (by rfl) ⟨69042, by rfl⟩ : syracuseStep 2945813 = 138085) (by norm_num)
theorem B1963875 : Blo 1963435 1963875 := bstep (se 1 (by rfl) ⟨1472906, by rfl⟩ : syracuseStep 1963875 = 2945813) B2945813
theorem B37749077 : Blo 1963435 37749077 := bbase (se 10 (by rfl) ⟨55296, by rfl⟩ : syracuseStep 37749077 = 110593) (by norm_num)
theorem B25166051 : Blo 1963435 25166051 := bstep (se 1 (by rfl) ⟨18874538, by rfl⟩ : syracuseStep 25166051 = 37749077) B37749077
theorem B16777367 : Blo 1963435 16777367 := bstep (se 1 (by rfl) ⟨12583025, by rfl⟩ : syracuseStep 16777367 = 25166051) B25166051
theorem B11184911 : Blo 1963435 11184911 := bstep (se 1 (by rfl) ⟨8388683, by rfl⟩ : syracuseStep 11184911 = 16777367) B16777367
theorem B7456607 : Blo 1963435 7456607 := bstep (se 1 (by rfl) ⟨5592455, by rfl⟩ : syracuseStep 7456607 = 11184911) B11184911
theorem B4971071 : Blo 1963435 4971071 := bstep (se 1 (by rfl) ⟨3728303, by rfl⟩ : syracuseStep 4971071 = 7456607) B7456607
theorem B3314047 : Blo 1963435 3314047 := bstep (se 1 (by rfl) ⟨2485535, by rfl⟩ : syracuseStep 3314047 = 4971071) B4971071
theorem B4418729 : Blo 1963435 4418729 := bstep (se 2 (by rfl) ⟨1657023, by rfl⟩ : syracuseStep 4418729 = 3314047) B3314047
theorem B2945819 : Blo 1963435 2945819 := bstep (se 1 (by rfl) ⟨2209364, by rfl⟩ : syracuseStep 2945819 = 4418729) B4418729
theorem B1963879 : Blo 1963435 1963879 := bstep (se 1 (by rfl) ⟨1472909, by rfl⟩ : syracuseStep 1963879 = 2945819) B2945819
theorem B2209369 : Blo 1963435 2209369 := bbase (se 2 (by rfl) ⟨828513, by rfl⟩ : syracuseStep 2209369 = 1657027) (by norm_num)
theorem B2945825 : Blo 1963435 2945825 := bstep (se 2 (by rfl) ⟨1104684, by rfl⟩ : syracuseStep 2945825 = 2209369) B2209369
theorem B1963883 : Blo 1963435 1963883 := bstep (se 1 (by rfl) ⟨1472912, by rfl⟩ : syracuseStep 1963883 = 2945825) B2945825
theorem B36321173 : Blo 1963435 36321173 := bbase (se 6 (by rfl) ⟨851277, by rfl⟩ : syracuseStep 36321173 = 1702555) (by norm_num)
theorem B24214115 : Blo 1963435 24214115 := bstep (se 1 (by rfl) ⟨18160586, by rfl⟩ : syracuseStep 24214115 = 36321173) B36321173
theorem B16142743 : Blo 1963435 16142743 := bstep (se 1 (by rfl) ⟨12107057, by rfl⟩ : syracuseStep 16142743 = 24214115) B24214115
theorem B21523657 : Blo 1963435 21523657 := bstep (se 2 (by rfl) ⟨8071371, by rfl⟩ : syracuseStep 21523657 = 16142743) B16142743
theorem B28698209 : Blo 1963435 28698209 := bstep (se 2 (by rfl) ⟨10761828, by rfl⟩ : syracuseStep 28698209 = 21523657) B21523657
theorem B19132139 : Blo 1963435 19132139 := bstep (se 1 (by rfl) ⟨14349104, by rfl⟩ : syracuseStep 19132139 = 28698209) B28698209
theorem B12754759 : Blo 1963435 12754759 := bstep (se 1 (by rfl) ⟨9566069, by rfl⟩ : syracuseStep 12754759 = 19132139) B19132139
theorem B17006345 : Blo 1963435 17006345 := bstep (se 2 (by rfl) ⟨6377379, by rfl⟩ : syracuseStep 17006345 = 12754759) B12754759
theorem B11337563 : Blo 1963435 11337563 := bstep (se 1 (by rfl) ⟨8503172, by rfl⟩ : syracuseStep 11337563 = 17006345) B17006345
theorem B7558375 : Blo 1963435 7558375 := bstep (se 1 (by rfl) ⟨5668781, by rfl⟩ : syracuseStep 7558375 = 11337563) B11337563
theorem B10077833 : Blo 1963435 10077833 := bstep (se 2 (by rfl) ⟨3779187, by rfl⟩ : syracuseStep 10077833 = 7558375) B7558375
theorem B6718555 : Blo 1963435 6718555 := bstep (se 1 (by rfl) ⟨5038916, by rfl⟩ : syracuseStep 6718555 = 10077833) B10077833
theorem B8958073 : Blo 1963435 8958073 := bstep (se 2 (by rfl) ⟨3359277, by rfl⟩ : syracuseStep 8958073 = 6718555) B6718555
theorem B11944097 : Blo 1963435 11944097 := bstep (se 2 (by rfl) ⟨4479036, by rfl⟩ : syracuseStep 11944097 = 8958073) B8958073
theorem B7962731 : Blo 1963435 7962731 := bstep (se 1 (by rfl) ⟨5972048, by rfl⟩ : syracuseStep 7962731 = 11944097) B11944097
theorem B5308487 : Blo 1963435 5308487 := bstep (se 1 (by rfl) ⟨3981365, by rfl⟩ : syracuseStep 5308487 = 7962731) B7962731
theorem B3538991 : Blo 1963435 3538991 := bstep (se 1 (by rfl) ⟨2654243, by rfl⟩ : syracuseStep 3538991 = 5308487) B5308487
theorem B9437309 : Blo 1963435 9437309 := bstep (se 3 (by rfl) ⟨1769495, by rfl⟩ : syracuseStep 9437309 = 3538991) B3538991
theorem B6291539 : Blo 1963435 6291539 := bstep (se 1 (by rfl) ⟨4718654, by rfl⟩ : syracuseStep 6291539 = 9437309) B9437309
theorem B4194359 : Blo 1963435 4194359 := bstep (se 1 (by rfl) ⟨3145769, by rfl⟩ : syracuseStep 4194359 = 6291539) B6291539
theorem B2796239 : Blo 1963435 2796239 := bstep (se 1 (by rfl) ⟨2097179, by rfl⟩ : syracuseStep 2796239 = 4194359) B4194359
theorem B7456637 : Blo 1963435 7456637 := bstep (se 3 (by rfl) ⟨1398119, by rfl⟩ : syracuseStep 7456637 = 2796239) B2796239
theorem B4971091 : Blo 1963435 4971091 := bstep (se 1 (by rfl) ⟨3728318, by rfl⟩ : syracuseStep 4971091 = 7456637) B7456637
theorem B6628121 : Blo 1963435 6628121 := bstep (se 2 (by rfl) ⟨2485545, by rfl⟩ : syracuseStep 6628121 = 4971091) B4971091
theorem B4418747 : Blo 1963435 4418747 := bstep (se 1 (by rfl) ⟨3314060, by rfl⟩ : syracuseStep 4418747 = 6628121) B6628121
theorem B2945831 : Blo 1963435 2945831 := bstep (se 1 (by rfl) ⟨2209373, by rfl⟩ : syracuseStep 2945831 = 4418747) B4418747
theorem B1963887 : Blo 1963435 1963887 := bstep (se 1 (by rfl) ⟨1472915, by rfl⟩ : syracuseStep 1963887 = 2945831) B2945831
theorem B2945837 : Blo 1963435 2945837 := bbase (se 3 (by rfl) ⟨552344, by rfl⟩ : syracuseStep 2945837 = 1104689) (by norm_num)
theorem B1963891 : Blo 1963435 1963891 := bstep (se 1 (by rfl) ⟨1472918, by rfl⟩ : syracuseStep 1963891 = 2945837) B2945837
theorem B4418765 : Blo 1963435 4418765 := bbase (se 3 (by rfl) ⟨828518, by rfl⟩ : syracuseStep 4418765 = 1657037) (by norm_num)
theorem B2945843 : Blo 1963435 2945843 := bstep (se 1 (by rfl) ⟨2209382, by rfl⟩ : syracuseStep 2945843 = 4418765) B4418765
theorem B1963895 : Blo 1963435 1963895 := bstep (se 1 (by rfl) ⟨1472921, by rfl⟩ : syracuseStep 1963895 = 2945843) B2945843
theorem B2485561 : Blo 1963435 2485561 := bbase (se 2 (by rfl) ⟨932085, by rfl⟩ : syracuseStep 2485561 = 1864171) (by norm_num)
theorem B3314081 : Blo 1963435 3314081 := bstep (se 2 (by rfl) ⟨1242780, by rfl⟩ : syracuseStep 3314081 = 2485561) B2485561
theorem B2209387 : Blo 1963435 2209387 := bstep (se 1 (by rfl) ⟨1657040, by rfl⟩ : syracuseStep 2209387 = 3314081) B3314081
theorem B2945849 : Blo 1963435 2945849 := bstep (se 2 (by rfl) ⟨1104693, by rfl⟩ : syracuseStep 2945849 = 2209387) B2209387
theorem B1963899 : Blo 1963435 1963899 := bstep (se 1 (by rfl) ⟨1472924, by rfl⟩ : syracuseStep 1963899 = 2945849) B2945849
theorem B6291589 : Blo 1963435 6291589 := bbase (se 4 (by rfl) ⟨589836, by rfl⟩ : syracuseStep 6291589 = 1179673) (by norm_num)
theorem B8388785 : Blo 1963435 8388785 := bstep (se 2 (by rfl) ⟨3145794, by rfl⟩ : syracuseStep 8388785 = 6291589) B6291589
theorem B22370093 : Blo 1963435 22370093 := bstep (se 3 (by rfl) ⟨4194392, by rfl⟩ : syracuseStep 22370093 = 8388785) B8388785
theorem B14913395 : Blo 1963435 14913395 := bstep (se 1 (by rfl) ⟨11185046, by rfl⟩ : syracuseStep 14913395 = 22370093) B22370093
theorem B9942263 : Blo 1963435 9942263 := bstep (se 1 (by rfl) ⟨7456697, by rfl⟩ : syracuseStep 9942263 = 14913395) B14913395
theorem B6628175 : Blo 1963435 6628175 := bstep (se 1 (by rfl) ⟨4971131, by rfl⟩ : syracuseStep 6628175 = 9942263) B9942263
theorem B4418783 : Blo 1963435 4418783 := bstep (se 1 (by rfl) ⟨3314087, by rfl⟩ : syracuseStep 4418783 = 6628175) B6628175
theorem B2945855 : Blo 1963435 2945855 := bstep (se 1 (by rfl) ⟨2209391, by rfl⟩ : syracuseStep 2945855 = 4418783) B4418783
theorem B1963903 : Blo 1963435 1963903 := bstep (se 1 (by rfl) ⟨1472927, by rfl⟩ : syracuseStep 1963903 = 2945855) B2945855
theorem B2945861 : Blo 1963435 2945861 := bbase (se 4 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 2945861 = 552349) (by norm_num)
theorem B1963907 : Blo 1963435 1963907 := bstep (se 1 (by rfl) ⟨1472930, by rfl⟩ : syracuseStep 1963907 = 2945861) B2945861
theorem B3314101 : Blo 1963435 3314101 := bbase (se 5 (by rfl) ⟨155348, by rfl⟩ : syracuseStep 3314101 = 310697) (by norm_num)
theorem B4418801 : Blo 1963435 4418801 := bstep (se 2 (by rfl) ⟨1657050, by rfl⟩ : syracuseStep 4418801 = 3314101) B3314101
theorem B2945867 : Blo 1963435 2945867 := bstep (se 1 (by rfl) ⟨2209400, by rfl⟩ : syracuseStep 2945867 = 4418801) B4418801
theorem B1963911 : Blo 1963435 1963911 := bstep (se 1 (by rfl) ⟨1472933, by rfl⟩ : syracuseStep 1963911 = 2945867) B2945867
theorem B2209405 : Blo 1963435 2209405 := bbase (se 3 (by rfl) ⟨414263, by rfl⟩ : syracuseStep 2209405 = 828527) (by norm_num)
theorem B2945873 : Blo 1963435 2945873 := bstep (se 2 (by rfl) ⟨1104702, by rfl⟩ : syracuseStep 2945873 = 2209405) B2209405
theorem B1963915 : Blo 1963435 1963915 := bstep (se 1 (by rfl) ⟨1472936, by rfl⟩ : syracuseStep 1963915 = 2945873) B2945873
theorem B6628229 : Blo 1963435 6628229 := bbase (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) (by norm_num)
theorem B4418819 : Blo 1963435 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B2945879 : Blo 1963435 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B1963919 : Blo 1963435 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B2945885 : Blo 1963435 2945885 := bbase (se 3 (by rfl) ⟨552353, by rfl⟩ : syracuseStep 2945885 = 1104707) (by norm_num)
theorem B1963923 : Blo 1963435 1963923 := bstep (se 1 (by rfl) ⟨1472942, by rfl⟩ : syracuseStep 1963923 = 2945885) B2945885
theorem B4418837 : Blo 1963435 4418837 := bbase (se 6 (by rfl) ⟨103566, by rfl⟩ : syracuseStep 4418837 = 207133) (by norm_num)
theorem B2945891 : Blo 1963435 2945891 := bstep (se 1 (by rfl) ⟨2209418, by rfl⟩ : syracuseStep 2945891 = 4418837) B4418837
theorem B1963927 : Blo 1963435 1963927 := bstep (se 1 (by rfl) ⟨1472945, by rfl⟩ : syracuseStep 1963927 = 2945891) B2945891
theorem B7456805 : Blo 1963435 7456805 := bbase (se 4 (by rfl) ⟨699075, by rfl⟩ : syracuseStep 7456805 = 1398151) (by norm_num)
theorem B4971203 : Blo 1963435 4971203 := bstep (se 1 (by rfl) ⟨3728402, by rfl⟩ : syracuseStep 4971203 = 7456805) B7456805
theorem B3314135 : Blo 1963435 3314135 := bstep (se 1 (by rfl) ⟨2485601, by rfl⟩ : syracuseStep 3314135 = 4971203) B4971203
theorem B2209423 : Blo 1963435 2209423 := bstep (se 1 (by rfl) ⟨1657067, by rfl⟩ : syracuseStep 2209423 = 3314135) B3314135
theorem B2945897 : Blo 1963435 2945897 := bstep (se 2 (by rfl) ⟨1104711, by rfl⟩ : syracuseStep 2945897 = 2209423) B2209423
theorem B1963931 : Blo 1963435 1963931 := bstep (se 1 (by rfl) ⟨1472948, by rfl⟩ : syracuseStep 1963931 = 2945897) B2945897
theorem B4194461 : Blo 1963435 4194461 := bbase (se 3 (by rfl) ⟨786461, by rfl⟩ : syracuseStep 4194461 = 1572923) (by norm_num)
theorem B11185229 : Blo 1963435 11185229 := bstep (se 3 (by rfl) ⟨2097230, by rfl⟩ : syracuseStep 11185229 = 4194461) B4194461
theorem B7456819 : Blo 1963435 7456819 := bstep (se 1 (by rfl) ⟨5592614, by rfl⟩ : syracuseStep 7456819 = 11185229) B11185229
theorem B9942425 : Blo 1963435 9942425 := bstep (se 2 (by rfl) ⟨3728409, by rfl⟩ : syracuseStep 9942425 = 7456819) B7456819
theorem B6628283 : Blo 1963435 6628283 := bstep (se 1 (by rfl) ⟨4971212, by rfl⟩ : syracuseStep 6628283 = 9942425) B9942425
theorem B4418855 : Blo 1963435 4418855 := bstep (se 1 (by rfl) ⟨3314141, by rfl⟩ : syracuseStep 4418855 = 6628283) B6628283
theorem B2945903 : Blo 1963435 2945903 := bstep (se 1 (by rfl) ⟨2209427, by rfl⟩ : syracuseStep 2945903 = 4418855) B4418855
theorem B1963935 : Blo 1963435 1963935 := bstep (se 1 (by rfl) ⟨1472951, by rfl⟩ : syracuseStep 1963935 = 2945903) B2945903
theorem B2945909 : Blo 1963435 2945909 := bbase (se 5 (by rfl) ⟨138089, by rfl⟩ : syracuseStep 2945909 = 276179) (by norm_num)
theorem B1963939 : Blo 1963435 1963939 := bstep (se 1 (by rfl) ⟨1472954, by rfl⟩ : syracuseStep 1963939 = 2945909) B2945909
theorem B40862485 : Blo 1963435 40862485 := bbase (se 6 (by rfl) ⟨957714, by rfl⟩ : syracuseStep 40862485 = 1915429) (by norm_num)
theorem B217933253 : Blo 1963435 217933253 := bstep (se 4 (by rfl) ⟨20431242, by rfl⟩ : syracuseStep 217933253 = 40862485) B40862485
theorem B145288835 : Blo 1963435 145288835 := bstep (se 1 (by rfl) ⟨108966626, by rfl⟩ : syracuseStep 145288835 = 217933253) B217933253
theorem B96859223 : Blo 1963435 96859223 := bstep (se 1 (by rfl) ⟨72644417, by rfl⟩ : syracuseStep 96859223 = 145288835) B145288835
theorem B64572815 : Blo 1963435 64572815 := bstep (se 1 (by rfl) ⟨48429611, by rfl⟩ : syracuseStep 64572815 = 96859223) B96859223
theorem B43048543 : Blo 1963435 43048543 := bstep (se 1 (by rfl) ⟨32286407, by rfl⟩ : syracuseStep 43048543 = 64572815) B64572815
theorem B57398057 : Blo 1963435 57398057 := bstep (se 2 (by rfl) ⟨21524271, by rfl⟩ : syracuseStep 57398057 = 43048543) B43048543
theorem B38265371 : Blo 1963435 38265371 := bstep (se 1 (by rfl) ⟨28699028, by rfl⟩ : syracuseStep 38265371 = 57398057) B57398057
theorem B25510247 : Blo 1963435 25510247 := bstep (se 1 (by rfl) ⟨19132685, by rfl⟩ : syracuseStep 25510247 = 38265371) B38265371
theorem B17006831 : Blo 1963435 17006831 := bstep (se 1 (by rfl) ⟨12755123, by rfl⟩ : syracuseStep 17006831 = 25510247) B25510247
theorem B11337887 : Blo 1963435 11337887 := bstep (se 1 (by rfl) ⟨8503415, by rfl⟩ : syracuseStep 11337887 = 17006831) B17006831
theorem B7558591 : Blo 1963435 7558591 := bstep (se 1 (by rfl) ⟨5668943, by rfl⟩ : syracuseStep 7558591 = 11337887) B11337887
theorem B10078121 : Blo 1963435 10078121 := bstep (se 2 (by rfl) ⟨3779295, by rfl⟩ : syracuseStep 10078121 = 7558591) B7558591
theorem B6718747 : Blo 1963435 6718747 := bstep (se 1 (by rfl) ⟨5039060, by rfl⟩ : syracuseStep 6718747 = 10078121) B10078121
theorem B8958329 : Blo 1963435 8958329 := bstep (se 2 (by rfl) ⟨3359373, by rfl⟩ : syracuseStep 8958329 = 6718747) B6718747
theorem B5972219 : Blo 1963435 5972219 := bstep (se 1 (by rfl) ⟨4479164, by rfl⟩ : syracuseStep 5972219 = 8958329) B8958329
theorem B3981479 : Blo 1963435 3981479 := bstep (se 1 (by rfl) ⟨2986109, by rfl⟩ : syracuseStep 3981479 = 5972219) B5972219
theorem B10617277 : Blo 1963435 10617277 := bstep (se 3 (by rfl) ⟨1990739, by rfl⟩ : syracuseStep 10617277 = 3981479) B3981479
theorem B14156369 : Blo 1963435 14156369 := bstep (se 2 (by rfl) ⟨5308638, by rfl⟩ : syracuseStep 14156369 = 10617277) B10617277
theorem B9437579 : Blo 1963435 9437579 := bstep (se 1 (by rfl) ⟨7078184, by rfl⟩ : syracuseStep 9437579 = 14156369) B14156369
theorem B6291719 : Blo 1963435 6291719 := bstep (se 1 (by rfl) ⟨4718789, by rfl⟩ : syracuseStep 6291719 = 9437579) B9437579
theorem B4194479 : Blo 1963435 4194479 := bstep (se 1 (by rfl) ⟨3145859, by rfl⟩ : syracuseStep 4194479 = 6291719) B6291719
theorem B2796319 : Blo 1963435 2796319 := bstep (se 1 (by rfl) ⟨2097239, by rfl⟩ : syracuseStep 2796319 = 4194479) B4194479
theorem B3728425 : Blo 1963435 3728425 := bstep (se 2 (by rfl) ⟨1398159, by rfl⟩ : syracuseStep 3728425 = 2796319) B2796319
theorem B4971233 : Blo 1963435 4971233 := bstep (se 2 (by rfl) ⟨1864212, by rfl⟩ : syracuseStep 4971233 = 3728425) B3728425
theorem B3314155 : Blo 1963435 3314155 := bstep (se 1 (by rfl) ⟨2485616, by rfl⟩ : syracuseStep 3314155 = 4971233) B4971233
theorem B4418873 : Blo 1963435 4418873 := bstep (se 2 (by rfl) ⟨1657077, by rfl⟩ : syracuseStep 4418873 = 3314155) B3314155
theorem B2945915 : Blo 1963435 2945915 := bstep (se 1 (by rfl) ⟨2209436, by rfl⟩ : syracuseStep 2945915 = 4418873) B4418873
theorem B1963943 : Blo 1963435 1963943 := bstep (se 1 (by rfl) ⟨1472957, by rfl⟩ : syracuseStep 1963943 = 2945915) B2945915
theorem B2209441 : Blo 1963435 2209441 := bbase (se 2 (by rfl) ⟨828540, by rfl⟩ : syracuseStep 2209441 = 1657081) (by norm_num)
theorem B2945921 : Blo 1963435 2945921 := bstep (se 2 (by rfl) ⟨1104720, by rfl⟩ : syracuseStep 2945921 = 2209441) B2209441
theorem B1963947 : Blo 1963435 1963947 := bstep (se 1 (by rfl) ⟨1472960, by rfl⟩ : syracuseStep 1963947 = 2945921) B2945921
theorem B4971253 : Blo 1963435 4971253 := bbase (se 5 (by rfl) ⟨233027, by rfl⟩ : syracuseStep 4971253 = 466055) (by norm_num)
theorem B6628337 : Blo 1963435 6628337 := bstep (se 2 (by rfl) ⟨2485626, by rfl⟩ : syracuseStep 6628337 = 4971253) B4971253
theorem B4418891 : Blo 1963435 4418891 := bstep (se 1 (by rfl) ⟨3314168, by rfl⟩ : syracuseStep 4418891 = 6628337) B6628337
theorem B2945927 : Blo 1963435 2945927 := bstep (se 1 (by rfl) ⟨2209445, by rfl⟩ : syracuseStep 2945927 = 4418891) B4418891
theorem B1963951 : Blo 1963435 1963951 := bstep (se 1 (by rfl) ⟨1472963, by rfl⟩ : syracuseStep 1963951 = 2945927) B2945927
theorem B2945933 : Blo 1963435 2945933 := bbase (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) (by norm_num)
theorem B1963955 : Blo 1963435 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B4418909 : Blo 1963435 4418909 := bbase (se 3 (by rfl) ⟨828545, by rfl⟩ : syracuseStep 4418909 = 1657091) (by norm_num)
theorem B2945939 : Blo 1963435 2945939 := bstep (se 1 (by rfl) ⟨2209454, by rfl⟩ : syracuseStep 2945939 = 4418909) B4418909
theorem B1963959 : Blo 1963435 1963959 := bstep (se 1 (by rfl) ⟨1472969, by rfl⟩ : syracuseStep 1963959 = 2945939) B2945939
theorem B3314189 : Blo 1963435 3314189 := bbase (se 3 (by rfl) ⟨621410, by rfl⟩ : syracuseStep 3314189 = 1242821) (by norm_num)
theorem B2209459 : Blo 1963435 2209459 := bstep (se 1 (by rfl) ⟨1657094, by rfl⟩ : syracuseStep 2209459 = 3314189) B3314189
theorem B2945945 : Blo 1963435 2945945 := bstep (se 2 (by rfl) ⟨1104729, by rfl⟩ : syracuseStep 2945945 = 2209459) B2209459
theorem B1963963 : Blo 1963435 1963963 := bstep (se 1 (by rfl) ⟨1472972, by rfl⟩ : syracuseStep 1963963 = 2945945) B2945945
theorem B3779341 : Blo 1963435 3779341 := bbase (se 3 (by rfl) ⟨708626, by rfl⟩ : syracuseStep 3779341 = 1417253) (by norm_num)
theorem B20156485 : Blo 1963435 20156485 := bstep (se 4 (by rfl) ⟨1889670, by rfl⟩ : syracuseStep 20156485 = 3779341) B3779341
theorem B26875313 : Blo 1963435 26875313 := bstep (se 2 (by rfl) ⟨10078242, by rfl⟩ : syracuseStep 26875313 = 20156485) B20156485
theorem B17916875 : Blo 1963435 17916875 := bstep (se 1 (by rfl) ⟨13437656, by rfl⟩ : syracuseStep 17916875 = 26875313) B26875313
theorem B11944583 : Blo 1963435 11944583 := bstep (se 1 (by rfl) ⟨8958437, by rfl⟩ : syracuseStep 11944583 = 17916875) B17916875
theorem B7963055 : Blo 1963435 7963055 := bstep (se 1 (by rfl) ⟨5972291, by rfl⟩ : syracuseStep 7963055 = 11944583) B11944583
theorem B5308703 : Blo 1963435 5308703 := bstep (se 1 (by rfl) ⟨3981527, by rfl⟩ : syracuseStep 5308703 = 7963055) B7963055
theorem B3539135 : Blo 1963435 3539135 := bstep (se 1 (by rfl) ⟨2654351, by rfl⟩ : syracuseStep 3539135 = 5308703) B5308703
theorem B2359423 : Blo 1963435 2359423 := bstep (se 1 (by rfl) ⟨1769567, by rfl⟩ : syracuseStep 2359423 = 3539135) B3539135
theorem B3145897 : Blo 1963435 3145897 := bstep (se 2 (by rfl) ⟨1179711, by rfl⟩ : syracuseStep 3145897 = 2359423) B2359423
theorem B16778117 : Blo 1963435 16778117 := bstep (se 4 (by rfl) ⟨1572948, by rfl⟩ : syracuseStep 16778117 = 3145897) B3145897
theorem B11185411 : Blo 1963435 11185411 := bstep (se 1 (by rfl) ⟨8389058, by rfl⟩ : syracuseStep 11185411 = 16778117) B16778117
theorem B14913881 : Blo 1963435 14913881 := bstep (se 2 (by rfl) ⟨5592705, by rfl⟩ : syracuseStep 14913881 = 11185411) B11185411
theorem B9942587 : Blo 1963435 9942587 := bstep (se 1 (by rfl) ⟨7456940, by rfl⟩ : syracuseStep 9942587 = 14913881) B14913881
theorem B6628391 : Blo 1963435 6628391 := bstep (se 1 (by rfl) ⟨4971293, by rfl⟩ : syracuseStep 6628391 = 9942587) B9942587
theorem B4418927 : Blo 1963435 4418927 := bstep (se 1 (by rfl) ⟨3314195, by rfl⟩ : syracuseStep 4418927 = 6628391) B6628391
theorem B2945951 : Blo 1963435 2945951 := bstep (se 1 (by rfl) ⟨2209463, by rfl⟩ : syracuseStep 2945951 = 4418927) B4418927
theorem B1963967 : Blo 1963435 1963967 := bstep (se 1 (by rfl) ⟨1472975, by rfl⟩ : syracuseStep 1963967 = 2945951) B2945951
theorem B2945957 : Blo 1963435 2945957 := bbase (se 4 (by rfl) ⟨276183, by rfl⟩ : syracuseStep 2945957 = 552367) (by norm_num)
theorem B1963971 : Blo 1963435 1963971 := bstep (se 1 (by rfl) ⟨1472978, by rfl⟩ : syracuseStep 1963971 = 2945957) B2945957
theorem B2485657 : Blo 1963435 2485657 := bbase (se 2 (by rfl) ⟨932121, by rfl⟩ : syracuseStep 2485657 = 1864243) (by norm_num)
theorem B3314209 : Blo 1963435 3314209 := bstep (se 2 (by rfl) ⟨1242828, by rfl⟩ : syracuseStep 3314209 = 2485657) B2485657
theorem B4418945 : Blo 1963435 4418945 := bstep (se 2 (by rfl) ⟨1657104, by rfl⟩ : syracuseStep 4418945 = 3314209) B3314209
theorem B2945963 : Blo 1963435 2945963 := bstep (se 1 (by rfl) ⟨2209472, by rfl⟩ : syracuseStep 2945963 = 4418945) B4418945
theorem B1963975 : Blo 1963435 1963975 := bstep (se 1 (by rfl) ⟨1472981, by rfl⟩ : syracuseStep 1963975 = 2945963) B2945963
theorem B2209477 : Blo 1963435 2209477 := bbase (se 4 (by rfl) ⟨207138, by rfl⟩ : syracuseStep 2209477 = 414277) (by norm_num)
theorem B2945969 : Blo 1963435 2945969 := bstep (se 2 (by rfl) ⟨1104738, by rfl⟩ : syracuseStep 2945969 = 2209477) B2209477
theorem B1963979 : Blo 1963435 1963979 := bstep (se 1 (by rfl) ⟨1472984, by rfl⟩ : syracuseStep 1963979 = 2945969) B2945969
theorem B3728501 : Blo 1963435 3728501 := bbase (se 5 (by rfl) ⟨174773, by rfl⟩ : syracuseStep 3728501 = 349547) (by norm_num)
theorem B2485667 : Blo 1963435 2485667 := bstep (se 1 (by rfl) ⟨1864250, by rfl⟩ : syracuseStep 2485667 = 3728501) B3728501
theorem B6628445 : Blo 1963435 6628445 := bstep (se 3 (by rfl) ⟨1242833, by rfl⟩ : syracuseStep 6628445 = 2485667) B2485667
theorem B4418963 : Blo 1963435 4418963 := bstep (se 1 (by rfl) ⟨3314222, by rfl⟩ : syracuseStep 4418963 = 6628445) B6628445
theorem B2945975 : Blo 1963435 2945975 := bstep (se 1 (by rfl) ⟨2209481, by rfl⟩ : syracuseStep 2945975 = 4418963) B4418963
theorem B1963983 : Blo 1963435 1963983 := bstep (se 1 (by rfl) ⟨1472987, by rfl⟩ : syracuseStep 1963983 = 2945975) B2945975
theorem B2945981 : Blo 1963435 2945981 := bbase (se 3 (by rfl) ⟨552371, by rfl⟩ : syracuseStep 2945981 = 1104743) (by norm_num)
theorem B1963987 : Blo 1963435 1963987 := bstep (se 1 (by rfl) ⟨1472990, by rfl⟩ : syracuseStep 1963987 = 2945981) B2945981
theorem B4418981 : Blo 1963435 4418981 := bbase (se 4 (by rfl) ⟨414279, by rfl⟩ : syracuseStep 4418981 = 828559) (by norm_num)
theorem B2945987 : Blo 1963435 2945987 := bstep (se 1 (by rfl) ⟨2209490, by rfl⟩ : syracuseStep 2945987 = 4418981) B4418981
theorem B1963991 : Blo 1963435 1963991 := bstep (se 1 (by rfl) ⟨1472993, by rfl⟩ : syracuseStep 1963991 = 2945987) B2945987
theorem B4971365 : Blo 1963435 4971365 := bbase (se 4 (by rfl) ⟨466065, by rfl⟩ : syracuseStep 4971365 = 932131) (by norm_num)
theorem B3314243 : Blo 1963435 3314243 := bstep (se 1 (by rfl) ⟨2485682, by rfl⟩ : syracuseStep 3314243 = 4971365) B4971365
theorem B2209495 : Blo 1963435 2209495 := bstep (se 1 (by rfl) ⟨1657121, by rfl⟩ : syracuseStep 2209495 = 3314243) B3314243
theorem B2945993 : Blo 1963435 2945993 := bstep (se 2 (by rfl) ⟨1104747, by rfl⟩ : syracuseStep 2945993 = 2209495) B2209495
theorem B1963995 : Blo 1963435 1963995 := bstep (se 1 (by rfl) ⟨1472996, by rfl⟩ : syracuseStep 1963995 = 2945993) B2945993
theorem B3145949 : Blo 1963435 3145949 := bbase (se 3 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 3145949 = 1179731) (by norm_num)
theorem B2097299 : Blo 1963435 2097299 := bstep (se 1 (by rfl) ⟨1572974, by rfl⟩ : syracuseStep 2097299 = 3145949) B3145949
theorem B5592797 : Blo 1963435 5592797 := bstep (se 3 (by rfl) ⟨1048649, by rfl⟩ : syracuseStep 5592797 = 2097299) B2097299
theorem B3728531 : Blo 1963435 3728531 := bstep (se 1 (by rfl) ⟨2796398, by rfl⟩ : syracuseStep 3728531 = 5592797) B5592797
theorem B9942749 : Blo 1963435 9942749 := bstep (se 3 (by rfl) ⟨1864265, by rfl⟩ : syracuseStep 9942749 = 3728531) B3728531
theorem B6628499 : Blo 1963435 6628499 := bstep (se 1 (by rfl) ⟨4971374, by rfl⟩ : syracuseStep 6628499 = 9942749) B9942749
theorem B4418999 : Blo 1963435 4418999 := bstep (se 1 (by rfl) ⟨3314249, by rfl⟩ : syracuseStep 4418999 = 6628499) B6628499
theorem B2945999 : Blo 1963435 2945999 := bstep (se 1 (by rfl) ⟨2209499, by rfl⟩ : syracuseStep 2945999 = 4418999) B4418999
theorem B1963999 : Blo 1963435 1963999 := bstep (se 1 (by rfl) ⟨1472999, by rfl⟩ : syracuseStep 1963999 = 2945999) B2945999
theorem B2946005 : Blo 1963435 2946005 := bbase (se 7 (by rfl) ⟨34523, by rfl⟩ : syracuseStep 2946005 = 69047) (by norm_num)
theorem B1964003 : Blo 1963435 1964003 := bstep (se 1 (by rfl) ⟨1473002, by rfl⟩ : syracuseStep 1964003 = 2946005) B2946005
theorem B7457093 : Blo 1963435 7457093 := bbase (se 4 (by rfl) ⟨699102, by rfl⟩ : syracuseStep 7457093 = 1398205) (by norm_num)
theorem B4971395 : Blo 1963435 4971395 := bstep (se 1 (by rfl) ⟨3728546, by rfl⟩ : syracuseStep 4971395 = 7457093) B7457093
theorem B3314263 : Blo 1963435 3314263 := bstep (se 1 (by rfl) ⟨2485697, by rfl⟩ : syracuseStep 3314263 = 4971395) B4971395
theorem B4419017 : Blo 1963435 4419017 := bstep (se 2 (by rfl) ⟨1657131, by rfl⟩ : syracuseStep 4419017 = 3314263) B3314263
theorem B2946011 : Blo 1963435 2946011 := bstep (se 1 (by rfl) ⟨2209508, by rfl⟩ : syracuseStep 2946011 = 4419017) B4419017
theorem B1964007 : Blo 1963435 1964007 := bstep (se 1 (by rfl) ⟨1473005, by rfl⟩ : syracuseStep 1964007 = 2946011) B2946011
theorem B2209513 : Blo 1963435 2209513 := bbase (se 2 (by rfl) ⟨828567, by rfl⟩ : syracuseStep 2209513 = 1657135) (by norm_num)
theorem B2946017 : Blo 1963435 2946017 := bstep (se 2 (by rfl) ⟨1104756, by rfl⟩ : syracuseStep 2946017 = 2209513) B2209513
theorem B1964011 : Blo 1963435 1964011 := bstep (se 1 (by rfl) ⟨1473008, by rfl⟩ : syracuseStep 1964011 = 2946017) B2946017
theorem B11185685 : Blo 1963435 11185685 := bbase (se 6 (by rfl) ⟨262164, by rfl⟩ : syracuseStep 11185685 = 524329) (by norm_num)
theorem B7457123 : Blo 1963435 7457123 := bstep (se 1 (by rfl) ⟨5592842, by rfl⟩ : syracuseStep 7457123 = 11185685) B11185685
theorem B4971415 : Blo 1963435 4971415 := bstep (se 1 (by rfl) ⟨3728561, by rfl⟩ : syracuseStep 4971415 = 7457123) B7457123
theorem B6628553 : Blo 1963435 6628553 := bstep (se 2 (by rfl) ⟨2485707, by rfl⟩ : syracuseStep 6628553 = 4971415) B4971415
theorem B4419035 : Blo 1963435 4419035 := bstep (se 1 (by rfl) ⟨3314276, by rfl⟩ : syracuseStep 4419035 = 6628553) B6628553
theorem B2946023 : Blo 1963435 2946023 := bstep (se 1 (by rfl) ⟨2209517, by rfl⟩ : syracuseStep 2946023 = 4419035) B4419035
theorem B1964015 : Blo 1963435 1964015 := bstep (se 1 (by rfl) ⟨1473011, by rfl⟩ : syracuseStep 1964015 = 2946023) B2946023
theorem B2946029 : Blo 1963435 2946029 := bbase (se 3 (by rfl) ⟨552380, by rfl⟩ : syracuseStep 2946029 = 1104761) (by norm_num)
theorem B1964019 : Blo 1963435 1964019 := bstep (se 1 (by rfl) ⟨1473014, by rfl⟩ : syracuseStep 1964019 = 2946029) B2946029
theorem B4419053 : Blo 1963435 4419053 := bbase (se 3 (by rfl) ⟨828572, by rfl⟩ : syracuseStep 4419053 = 1657145) (by norm_num)
theorem B2946035 : Blo 1963435 2946035 := bstep (se 1 (by rfl) ⟨2209526, by rfl⟩ : syracuseStep 2946035 = 4419053) B4419053
theorem B1964023 : Blo 1963435 1964023 := bstep (se 1 (by rfl) ⟨1473017, by rfl⟩ : syracuseStep 1964023 = 2946035) B2946035
theorem B6291989 : Blo 1963435 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B4194659 : Blo 1963435 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B2796439 : Blo 1963435 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B3728585 : Blo 1963435 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B2485723 : Blo 1963435 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B3314297 : Blo 1963435 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B2209531 : Blo 1963435 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B2946041 : Blo 1963435 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B1964027 : Blo 1963435 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B2834597 : Blo 1963435 2834597 := bbase (se 4 (by rfl) ⟨265743, by rfl⟩ : syracuseStep 2834597 = 531487) (by norm_num)
theorem B7558925 : Blo 1963435 7558925 := bstep (se 3 (by rfl) ⟨1417298, by rfl⟩ : syracuseStep 7558925 = 2834597) B2834597
theorem B20157133 : Blo 1963435 20157133 := bstep (se 3 (by rfl) ⟨3779462, by rfl⟩ : syracuseStep 20157133 = 7558925) B7558925
theorem B26876177 : Blo 1963435 26876177 := bstep (se 2 (by rfl) ⟨10078566, by rfl⟩ : syracuseStep 26876177 = 20157133) B20157133
theorem B17917451 : Blo 1963435 17917451 := bstep (se 1 (by rfl) ⟨13438088, by rfl⟩ : syracuseStep 17917451 = 26876177) B26876177
theorem B11944967 : Blo 1963435 11944967 := bstep (se 1 (by rfl) ⟨8958725, by rfl⟩ : syracuseStep 11944967 = 17917451) B17917451
theorem B31853245 : Blo 1963435 31853245 := bstep (se 3 (by rfl) ⟨5972483, by rfl⟩ : syracuseStep 31853245 = 11944967) B11944967
theorem B42470993 : Blo 1963435 42470993 := bstep (se 2 (by rfl) ⟨15926622, by rfl⟩ : syracuseStep 42470993 = 31853245) B31853245
theorem B113255981 : Blo 1963435 113255981 := bstep (se 3 (by rfl) ⟨21235496, by rfl⟩ : syracuseStep 113255981 = 42470993) B42470993
theorem B75503987 : Blo 1963435 75503987 := bstep (se 1 (by rfl) ⟨56627990, by rfl⟩ : syracuseStep 75503987 = 113255981) B113255981
theorem B50335991 : Blo 1963435 50335991 := bstep (se 1 (by rfl) ⟨37751993, by rfl⟩ : syracuseStep 50335991 = 75503987) B75503987
theorem B33557327 : Blo 1963435 33557327 := bstep (se 1 (by rfl) ⟨25167995, by rfl⟩ : syracuseStep 33557327 = 50335991) B50335991
theorem B22371551 : Blo 1963435 22371551 := bstep (se 1 (by rfl) ⟨16778663, by rfl⟩ : syracuseStep 22371551 = 33557327) B33557327
theorem B14914367 : Blo 1963435 14914367 := bstep (se 1 (by rfl) ⟨11185775, by rfl⟩ : syracuseStep 14914367 = 22371551) B22371551
theorem B9942911 : Blo 1963435 9942911 := bstep (se 1 (by rfl) ⟨7457183, by rfl⟩ : syracuseStep 9942911 = 14914367) B14914367
theorem B6628607 : Blo 1963435 6628607 := bstep (se 1 (by rfl) ⟨4971455, by rfl⟩ : syracuseStep 6628607 = 9942911) B9942911
theorem B4419071 : Blo 1963435 4419071 := bstep (se 1 (by rfl) ⟨3314303, by rfl⟩ : syracuseStep 4419071 = 6628607) B6628607
theorem B2946047 : Blo 1963435 2946047 := bstep (se 1 (by rfl) ⟨2209535, by rfl⟩ : syracuseStep 2946047 = 4419071) B4419071
theorem B1964031 : Blo 1963435 1964031 := bstep (se 1 (by rfl) ⟨1473023, by rfl⟩ : syracuseStep 1964031 = 2946047) B2946047
theorem B2946053 : Blo 1963435 2946053 := bbase (se 4 (by rfl) ⟨276192, by rfl⟩ : syracuseStep 2946053 = 552385) (by norm_num)
theorem B1964035 : Blo 1963435 1964035 := bstep (se 1 (by rfl) ⟨1473026, by rfl⟩ : syracuseStep 1964035 = 2946053) B2946053
theorem B3314317 : Blo 1963435 3314317 := bbase (se 3 (by rfl) ⟨621434, by rfl⟩ : syracuseStep 3314317 = 1242869) (by norm_num)
theorem B4419089 : Blo 1963435 4419089 := bstep (se 2 (by rfl) ⟨1657158, by rfl⟩ : syracuseStep 4419089 = 3314317) B3314317
theorem B2946059 : Blo 1963435 2946059 := bstep (se 1 (by rfl) ⟨2209544, by rfl⟩ : syracuseStep 2946059 = 4419089) B4419089
theorem B1964039 : Blo 1963435 1964039 := bstep (se 1 (by rfl) ⟨1473029, by rfl⟩ : syracuseStep 1964039 = 2946059) B2946059
theorem B2209549 : Blo 1963435 2209549 := bbase (se 3 (by rfl) ⟨414290, by rfl⟩ : syracuseStep 2209549 = 828581) (by norm_num)
theorem B2946065 : Blo 1963435 2946065 := bstep (se 2 (by rfl) ⟨1104774, by rfl⟩ : syracuseStep 2946065 = 2209549) B2209549
theorem B1964043 : Blo 1963435 1964043 := bstep (se 1 (by rfl) ⟨1473032, by rfl⟩ : syracuseStep 1964043 = 2946065) B2946065
theorem B6628661 : Blo 1963435 6628661 := bbase (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) (by norm_num)
theorem B4419107 : Blo 1963435 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B2946071 : Blo 1963435 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B1964047 : Blo 1963435 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B2946077 : Blo 1963435 2946077 := bbase (se 3 (by rfl) ⟨552389, by rfl⟩ : syracuseStep 2946077 = 1104779) (by norm_num)
theorem B1964051 : Blo 1963435 1964051 := bstep (se 1 (by rfl) ⟨1473038, by rfl⟩ : syracuseStep 1964051 = 2946077) B2946077
theorem B4419125 : Blo 1963435 4419125 := bbase (se 5 (by rfl) ⟨207146, by rfl⟩ : syracuseStep 4419125 = 414293) (by norm_num)
theorem B2946083 : Blo 1963435 2946083 := bstep (se 1 (by rfl) ⟨2209562, by rfl⟩ : syracuseStep 2946083 = 4419125) B4419125
theorem B1964055 : Blo 1963435 1964055 := bstep (se 1 (by rfl) ⟨1473041, by rfl⟩ : syracuseStep 1964055 = 2946083) B2946083
theorem B3146045 : Blo 1963435 3146045 := bbase (se 3 (by rfl) ⟨589883, by rfl⟩ : syracuseStep 3146045 = 1179767) (by norm_num)
theorem B8389453 : Blo 1963435 8389453 := bstep (se 3 (by rfl) ⟨1573022, by rfl⟩ : syracuseStep 8389453 = 3146045) B3146045
theorem B11185937 : Blo 1963435 11185937 := bstep (se 2 (by rfl) ⟨4194726, by rfl⟩ : syracuseStep 11185937 = 8389453) B8389453
theorem B7457291 : Blo 1963435 7457291 := bstep (se 1 (by rfl) ⟨5592968, by rfl⟩ : syracuseStep 7457291 = 11185937) B11185937
theorem B4971527 : Blo 1963435 4971527 := bstep (se 1 (by rfl) ⟨3728645, by rfl⟩ : syracuseStep 4971527 = 7457291) B7457291
theorem B3314351 : Blo 1963435 3314351 := bstep (se 1 (by rfl) ⟨2485763, by rfl⟩ : syracuseStep 3314351 = 4971527) B4971527
theorem B2209567 : Blo 1963435 2209567 := bstep (se 1 (by rfl) ⟨1657175, by rfl⟩ : syracuseStep 2209567 = 3314351) B3314351
theorem B2946089 : Blo 1963435 2946089 := bstep (se 2 (by rfl) ⟨1104783, by rfl⟩ : syracuseStep 2946089 = 2209567) B2209567
theorem B1964059 : Blo 1963435 1964059 := bstep (se 1 (by rfl) ⟨1473044, by rfl⟩ : syracuseStep 1964059 = 2946089) B2946089
theorem B4719077 : Blo 1963435 4719077 := bbase (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) (by norm_num)
theorem B3146051 : Blo 1963435 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B8389469 : Blo 1963435 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B5592979 : Blo 1963435 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B7457305 : Blo 1963435 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B9943073 : Blo 1963435 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B6628715 : Blo 1963435 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B4419143 : Blo 1963435 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B2946095 : Blo 1963435 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B1964063 : Blo 1963435 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B2946101 : Blo 1963435 2946101 := bbase (se 5 (by rfl) ⟨138098, by rfl⟩ : syracuseStep 2946101 = 276197) (by norm_num)
theorem B1964067 : Blo 1963435 1964067 := bstep (se 1 (by rfl) ⟨1473050, by rfl⟩ : syracuseStep 1964067 = 2946101) B2946101
theorem B4971557 : Blo 1963435 4971557 := bbase (se 4 (by rfl) ⟨466083, by rfl⟩ : syracuseStep 4971557 = 932167) (by norm_num)
theorem B3314371 : Blo 1963435 3314371 := bstep (se 1 (by rfl) ⟨2485778, by rfl⟩ : syracuseStep 3314371 = 4971557) B4971557
theorem B4419161 : Blo 1963435 4419161 := bstep (se 2 (by rfl) ⟨1657185, by rfl⟩ : syracuseStep 4419161 = 3314371) B3314371
theorem B2946107 : Blo 1963435 2946107 := bstep (se 1 (by rfl) ⟨2209580, by rfl⟩ : syracuseStep 2946107 = 4419161) B4419161
theorem B1964071 : Blo 1963435 1964071 := bstep (se 1 (by rfl) ⟨1473053, by rfl⟩ : syracuseStep 1964071 = 2946107) B2946107
theorem B2209585 : Blo 1963435 2209585 := bbase (se 2 (by rfl) ⟨828594, by rfl⟩ : syracuseStep 2209585 = 1657189) (by norm_num)
theorem B2946113 : Blo 1963435 2946113 := bstep (se 2 (by rfl) ⟨1104792, by rfl⟩ : syracuseStep 2946113 = 2209585) B2209585
theorem B1964075 : Blo 1963435 1964075 := bstep (se 1 (by rfl) ⟨1473056, by rfl⟩ : syracuseStep 1964075 = 2946113) B2946113
theorem B3146077 : Blo 1963435 3146077 := bbase (se 3 (by rfl) ⟨589889, by rfl⟩ : syracuseStep 3146077 = 1179779) (by norm_num)
theorem B4194769 : Blo 1963435 4194769 := bstep (se 2 (by rfl) ⟨1573038, by rfl⟩ : syracuseStep 4194769 = 3146077) B3146077
theorem B5593025 : Blo 1963435 5593025 := bstep (se 2 (by rfl) ⟨2097384, by rfl⟩ : syracuseStep 5593025 = 4194769) B4194769
theorem B3728683 : Blo 1963435 3728683 := bstep (se 1 (by rfl) ⟨2796512, by rfl⟩ : syracuseStep 3728683 = 5593025) B5593025
theorem B4971577 : Blo 1963435 4971577 := bstep (se 2 (by rfl) ⟨1864341, by rfl⟩ : syracuseStep 4971577 = 3728683) B3728683
theorem B6628769 : Blo 1963435 6628769 := bstep (se 2 (by rfl) ⟨2485788, by rfl⟩ : syracuseStep 6628769 = 4971577) B4971577
theorem B4419179 : Blo 1963435 4419179 := bstep (se 1 (by rfl) ⟨3314384, by rfl⟩ : syracuseStep 4419179 = 6628769) B6628769
theorem B2946119 : Blo 1963435 2946119 := bstep (se 1 (by rfl) ⟨2209589, by rfl⟩ : syracuseStep 2946119 = 4419179) B4419179
theorem B1964079 : Blo 1963435 1964079 := bstep (se 1 (by rfl) ⟨1473059, by rfl⟩ : syracuseStep 1964079 = 2946119) B2946119
theorem B2946125 : Blo 1963435 2946125 := bbase (se 3 (by rfl) ⟨552398, by rfl⟩ : syracuseStep 2946125 = 1104797) (by norm_num)
theorem B1964083 : Blo 1963435 1964083 := bstep (se 1 (by rfl) ⟨1473062, by rfl⟩ : syracuseStep 1964083 = 2946125) B2946125
theorem B4419197 : Blo 1963435 4419197 := bbase (se 3 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 4419197 = 1657199) (by norm_num)
theorem B2946131 : Blo 1963435 2946131 := bstep (se 1 (by rfl) ⟨2209598, by rfl⟩ : syracuseStep 2946131 = 4419197) B4419197
theorem B1964087 : Blo 1963435 1964087 := bstep (se 1 (by rfl) ⟨1473065, by rfl⟩ : syracuseStep 1964087 = 2946131) B2946131
theorem B3314405 : Blo 1963435 3314405 := bbase (se 4 (by rfl) ⟨310725, by rfl⟩ : syracuseStep 3314405 = 621451) (by norm_num)
theorem B2209603 : Blo 1963435 2209603 := bstep (se 1 (by rfl) ⟨1657202, by rfl⟩ : syracuseStep 2209603 = 3314405) B3314405
theorem B2946137 : Blo 1963435 2946137 := bstep (se 2 (by rfl) ⟨1104801, by rfl⟩ : syracuseStep 2946137 = 2209603) B2209603
theorem B1964091 : Blo 1963435 1964091 := bstep (se 1 (by rfl) ⟨1473068, by rfl⟩ : syracuseStep 1964091 = 2946137) B2946137
theorem B2359577 : Blo 1963435 2359577 := bbase (se 2 (by rfl) ⟨884841, by rfl⟩ : syracuseStep 2359577 = 1769683) (by norm_num)
theorem B6292205 : Blo 1963435 6292205 := bstep (se 3 (by rfl) ⟨1179788, by rfl⟩ : syracuseStep 6292205 = 2359577) B2359577
theorem B4194803 : Blo 1963435 4194803 := bstep (se 1 (by rfl) ⟨3146102, by rfl⟩ : syracuseStep 4194803 = 6292205) B6292205
theorem B2796535 : Blo 1963435 2796535 := bstep (se 1 (by rfl) ⟨2097401, by rfl⟩ : syracuseStep 2796535 = 4194803) B4194803
theorem B14914853 : Blo 1963435 14914853 := bstep (se 4 (by rfl) ⟨1398267, by rfl⟩ : syracuseStep 14914853 = 2796535) B2796535
theorem B9943235 : Blo 1963435 9943235 := bstep (se 1 (by rfl) ⟨7457426, by rfl⟩ : syracuseStep 9943235 = 14914853) B14914853
theorem B6628823 : Blo 1963435 6628823 := bstep (se 1 (by rfl) ⟨4971617, by rfl⟩ : syracuseStep 6628823 = 9943235) B9943235
theorem B4419215 : Blo 1963435 4419215 := bstep (se 1 (by rfl) ⟨3314411, by rfl⟩ : syracuseStep 4419215 = 6628823) B6628823
theorem B2946143 : Blo 1963435 2946143 := bstep (se 1 (by rfl) ⟨2209607, by rfl⟩ : syracuseStep 2946143 = 4419215) B4419215
theorem B1964095 : Blo 1963435 1964095 := bstep (se 1 (by rfl) ⟨1473071, by rfl⟩ : syracuseStep 1964095 = 2946143) B2946143
theorem B2946149 : Blo 1963435 2946149 := bbase (se 4 (by rfl) ⟨276201, by rfl⟩ : syracuseStep 2946149 = 552403) (by norm_num)
theorem B1964099 : Blo 1963435 1964099 := bstep (se 1 (by rfl) ⟨1473074, by rfl⟩ : syracuseStep 1964099 = 2946149) B2946149
theorem B4194821 : Blo 1963435 4194821 := bbase (se 4 (by rfl) ⟨393264, by rfl⟩ : syracuseStep 4194821 = 786529) (by norm_num)
theorem B2796547 : Blo 1963435 2796547 := bstep (se 1 (by rfl) ⟨2097410, by rfl⟩ : syracuseStep 2796547 = 4194821) B4194821
theorem B3728729 : Blo 1963435 3728729 := bstep (se 2 (by rfl) ⟨1398273, by rfl⟩ : syracuseStep 3728729 = 2796547) B2796547
theorem B2485819 : Blo 1963435 2485819 := bstep (se 1 (by rfl) ⟨1864364, by rfl⟩ : syracuseStep 2485819 = 3728729) B3728729
theorem B3314425 : Blo 1963435 3314425 := bstep (se 2 (by rfl) ⟨1242909, by rfl⟩ : syracuseStep 3314425 = 2485819) B2485819
theorem B4419233 : Blo 1963435 4419233 := bstep (se 2 (by rfl) ⟨1657212, by rfl⟩ : syracuseStep 4419233 = 3314425) B3314425
theorem B2946155 : Blo 1963435 2946155 := bstep (se 1 (by rfl) ⟨2209616, by rfl⟩ : syracuseStep 2946155 = 4419233) B4419233
theorem B1964103 : Blo 1963435 1964103 := bstep (se 1 (by rfl) ⟨1473077, by rfl⟩ : syracuseStep 1964103 = 2946155) B2946155
theorem B2209621 : Blo 1963435 2209621 := bbase (se 9 (by rfl) ⟨6473, by rfl⟩ : syracuseStep 2209621 = 12947) (by norm_num)
theorem B2946161 : Blo 1963435 2946161 := bstep (se 2 (by rfl) ⟨1104810, by rfl⟩ : syracuseStep 2946161 = 2209621) B2209621
theorem B1964107 : Blo 1963435 1964107 := bstep (se 1 (by rfl) ⟨1473080, by rfl⟩ : syracuseStep 1964107 = 2946161) B2946161
theorem B2485829 : Blo 1963435 2485829 := bbase (se 4 (by rfl) ⟨233046, by rfl⟩ : syracuseStep 2485829 = 466093) (by norm_num)
theorem B6628877 : Blo 1963435 6628877 := bstep (se 3 (by rfl) ⟨1242914, by rfl⟩ : syracuseStep 6628877 = 2485829) B2485829
theorem B4419251 : Blo 1963435 4419251 := bstep (se 1 (by rfl) ⟨3314438, by rfl⟩ : syracuseStep 4419251 = 6628877) B6628877
theorem B2946167 : Blo 1963435 2946167 := bstep (se 1 (by rfl) ⟨2209625, by rfl⟩ : syracuseStep 2946167 = 4419251) B4419251
theorem B1964111 : Blo 1963435 1964111 := bstep (se 1 (by rfl) ⟨1473083, by rfl⟩ : syracuseStep 1964111 = 2946167) B2946167
theorem B2946173 : Blo 1963435 2946173 := bbase (se 3 (by rfl) ⟨552407, by rfl⟩ : syracuseStep 2946173 = 1104815) (by norm_num)
theorem B1964115 : Blo 1963435 1964115 := bstep (se 1 (by rfl) ⟨1473086, by rfl⟩ : syracuseStep 1964115 = 2946173) B2946173
theorem B4419269 : Blo 1963435 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B2946179 : Blo 1963435 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1964119 : Blo 1963435 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B2391805 : Blo 1963435 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B3189073 : Blo 1963435 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B4252097 : Blo 1963435 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B2834731 : Blo 1963435 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B3779641 : Blo 1963435 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B20158085 : Blo 1963435 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B13438723 : Blo 1963435 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B17918297 : Blo 1963435 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B11945531 : Blo 1963435 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B7963687 : Blo 1963435 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B42472997 : Blo 1963435 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B28315331 : Blo 1963435 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B18876887 : Blo 1963435 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B12584591 : Blo 1963435 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B8389727 : Blo 1963435 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B5593151 : Blo 1963435 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B3728767 : Blo 1963435 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B4971689 : Blo 1963435 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B3314459 : Blo 1963435 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B2209639 : Blo 1963435 2209639 := bstep (se 1 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 2209639 = 3314459) B3314459
theorem B2946185 : Blo 1963435 2946185 := bstep (se 2 (by rfl) ⟨1104819, by rfl⟩ : syracuseStep 2946185 = 2209639) B2209639
theorem B1964123 : Blo 1963435 1964123 := bstep (se 1 (by rfl) ⟨1473092, by rfl⟩ : syracuseStep 1964123 = 2946185) B2946185
theorem B9943397 : Blo 1963435 9943397 := bbase (se 4 (by rfl) ⟨932193, by rfl⟩ : syracuseStep 9943397 = 1864387) (by norm_num)
theorem B6628931 : Blo 1963435 6628931 := bstep (se 1 (by rfl) ⟨4971698, by rfl⟩ : syracuseStep 6628931 = 9943397) B9943397
theorem B4419287 : Blo 1963435 4419287 := bstep (se 1 (by rfl) ⟨3314465, by rfl⟩ : syracuseStep 4419287 = 6628931) B6628931
theorem B2946191 : Blo 1963435 2946191 := bstep (se 1 (by rfl) ⟨2209643, by rfl⟩ : syracuseStep 2946191 = 4419287) B4419287
theorem B1964127 : Blo 1963435 1964127 := bstep (se 1 (by rfl) ⟨1473095, by rfl⟩ : syracuseStep 1964127 = 2946191) B2946191
theorem B2946197 : Blo 1963435 2946197 := bbase (se 6 (by rfl) ⟨69051, by rfl⟩ : syracuseStep 2946197 = 138103) (by norm_num)
theorem B1964131 : Blo 1963435 1964131 := bstep (se 1 (by rfl) ⟨1473098, by rfl⟩ : syracuseStep 1964131 = 2946197) B2946197
theorem B2359625 : Blo 1963435 2359625 := bbase (se 2 (by rfl) ⟨884859, by rfl⟩ : syracuseStep 2359625 = 1769719) (by norm_num)
theorem B6292333 : Blo 1963435 6292333 := bstep (se 3 (by rfl) ⟨1179812, by rfl⟩ : syracuseStep 6292333 = 2359625) B2359625
theorem B8389777 : Blo 1963435 8389777 := bstep (se 2 (by rfl) ⟨3146166, by rfl⟩ : syracuseStep 8389777 = 6292333) B6292333
theorem B11186369 : Blo 1963435 11186369 := bstep (se 2 (by rfl) ⟨4194888, by rfl⟩ : syracuseStep 11186369 = 8389777) B8389777
theorem B7457579 : Blo 1963435 7457579 := bstep (se 1 (by rfl) ⟨5593184, by rfl⟩ : syracuseStep 7457579 = 11186369) B11186369
theorem B4971719 : Blo 1963435 4971719 := bstep (se 1 (by rfl) ⟨3728789, by rfl⟩ : syracuseStep 4971719 = 7457579) B7457579
theorem B3314479 : Blo 1963435 3314479 := bstep (se 1 (by rfl) ⟨2485859, by rfl⟩ : syracuseStep 3314479 = 4971719) B4971719
theorem B4419305 : Blo 1963435 4419305 := bstep (se 2 (by rfl) ⟨1657239, by rfl⟩ : syracuseStep 4419305 = 3314479) B3314479
theorem B2946203 : Blo 1963435 2946203 := bstep (se 1 (by rfl) ⟨2209652, by rfl⟩ : syracuseStep 2946203 = 4419305) B4419305
theorem B1964135 : Blo 1963435 1964135 := bstep (se 1 (by rfl) ⟨1473101, by rfl⟩ : syracuseStep 1964135 = 2946203) B2946203
theorem B2209657 : Blo 1963435 2209657 := bbase (se 2 (by rfl) ⟨828621, by rfl⟩ : syracuseStep 2209657 = 1657243) (by norm_num)
theorem B2946209 : Blo 1963435 2946209 := bstep (se 2 (by rfl) ⟨1104828, by rfl⟩ : syracuseStep 2946209 = 2209657) B2209657
theorem B1964139 : Blo 1963435 1964139 := bstep (se 1 (by rfl) ⟨1473104, by rfl⟩ : syracuseStep 1964139 = 2946209) B2946209
theorem B4719269 : Blo 1963435 4719269 := bbase (se 4 (by rfl) ⟨442431, by rfl⟩ : syracuseStep 4719269 = 884863) (by norm_num)
theorem B12584717 : Blo 1963435 12584717 := bstep (se 3 (by rfl) ⟨2359634, by rfl⟩ : syracuseStep 12584717 = 4719269) B4719269
theorem B8389811 : Blo 1963435 8389811 := bstep (se 1 (by rfl) ⟨6292358, by rfl⟩ : syracuseStep 8389811 = 12584717) B12584717
theorem B5593207 : Blo 1963435 5593207 := bstep (se 1 (by rfl) ⟨4194905, by rfl⟩ : syracuseStep 5593207 = 8389811) B8389811
theorem B7457609 : Blo 1963435 7457609 := bstep (se 2 (by rfl) ⟨2796603, by rfl⟩ : syracuseStep 7457609 = 5593207) B5593207
theorem B4971739 : Blo 1963435 4971739 := bstep (se 1 (by rfl) ⟨3728804, by rfl⟩ : syracuseStep 4971739 = 7457609) B7457609
theorem B6628985 : Blo 1963435 6628985 := bstep (se 2 (by rfl) ⟨2485869, by rfl⟩ : syracuseStep 6628985 = 4971739) B4971739
theorem B4419323 : Blo 1963435 4419323 := bstep (se 1 (by rfl) ⟨3314492, by rfl⟩ : syracuseStep 4419323 = 6628985) B6628985
theorem B2946215 : Blo 1963435 2946215 := bstep (se 1 (by rfl) ⟨2209661, by rfl⟩ : syracuseStep 2946215 = 4419323) B4419323
theorem B1964143 : Blo 1963435 1964143 := bstep (se 1 (by rfl) ⟨1473107, by rfl⟩ : syracuseStep 1964143 = 2946215) B2946215
theorem B2946221 : Blo 1963435 2946221 := bbase (se 3 (by rfl) ⟨552416, by rfl⟩ : syracuseStep 2946221 = 1104833) (by norm_num)
theorem B1964147 : Blo 1963435 1964147 := bstep (se 1 (by rfl) ⟨1473110, by rfl⟩ : syracuseStep 1964147 = 2946221) B2946221
theorem B4419341 : Blo 1963435 4419341 := bbase (se 3 (by rfl) ⟨828626, by rfl⟩ : syracuseStep 4419341 = 1657253) (by norm_num)
theorem B2946227 : Blo 1963435 2946227 := bstep (se 1 (by rfl) ⟨2209670, by rfl⟩ : syracuseStep 2946227 = 4419341) B4419341
theorem B1964151 : Blo 1963435 1964151 := bstep (se 1 (by rfl) ⟨1473113, by rfl⟩ : syracuseStep 1964151 = 2946227) B2946227
theorem B2485885 : Blo 1963435 2485885 := bbase (se 3 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 2485885 = 932207) (by norm_num)
theorem B3314513 : Blo 1963435 3314513 := bstep (se 2 (by rfl) ⟨1242942, by rfl⟩ : syracuseStep 3314513 = 2485885) B2485885
theorem B2209675 : Blo 1963435 2209675 := bstep (se 1 (by rfl) ⟨1657256, by rfl⟩ : syracuseStep 2209675 = 3314513) B3314513
theorem B2946233 : Blo 1963435 2946233 := bstep (se 2 (by rfl) ⟨1104837, by rfl⟩ : syracuseStep 2946233 = 2209675) B2209675
theorem B1964155 : Blo 1963435 1964155 := bstep (se 1 (by rfl) ⟨1473116, by rfl⟩ : syracuseStep 1964155 = 2946233) B2946233
theorem B5309221 : Blo 1963435 5309221 := bbase (se 4 (by rfl) ⟨497739, by rfl⟩ : syracuseStep 5309221 = 995479) (by norm_num)
theorem B7078961 : Blo 1963435 7078961 := bstep (se 2 (by rfl) ⟨2654610, by rfl⟩ : syracuseStep 7078961 = 5309221) B5309221
theorem B4719307 : Blo 1963435 4719307 := bstep (se 1 (by rfl) ⟨3539480, by rfl⟩ : syracuseStep 4719307 = 7078961) B7078961
theorem B6292409 : Blo 1963435 6292409 := bstep (se 2 (by rfl) ⟨2359653, by rfl⟩ : syracuseStep 6292409 = 4719307) B4719307
theorem B16779757 : Blo 1963435 16779757 := bstep (se 3 (by rfl) ⟨3146204, by rfl⟩ : syracuseStep 16779757 = 6292409) B6292409
theorem B22373009 : Blo 1963435 22373009 := bstep (se 2 (by rfl) ⟨8389878, by rfl⟩ : syracuseStep 22373009 = 16779757) B16779757
theorem B14915339 : Blo 1963435 14915339 := bstep (se 1 (by rfl) ⟨11186504, by rfl⟩ : syracuseStep 14915339 = 22373009) B22373009
theorem B9943559 : Blo 1963435 9943559 := bstep (se 1 (by rfl) ⟨7457669, by rfl⟩ : syracuseStep 9943559 = 14915339) B14915339
theorem B6629039 : Blo 1963435 6629039 := bstep (se 1 (by rfl) ⟨4971779, by rfl⟩ : syracuseStep 6629039 = 9943559) B9943559
theorem B4419359 : Blo 1963435 4419359 := bstep (se 1 (by rfl) ⟨3314519, by rfl⟩ : syracuseStep 4419359 = 6629039) B6629039
theorem B2946239 : Blo 1963435 2946239 := bstep (se 1 (by rfl) ⟨2209679, by rfl⟩ : syracuseStep 2946239 = 4419359) B4419359
theorem B1964159 : Blo 1963435 1964159 := bstep (se 1 (by rfl) ⟨1473119, by rfl⟩ : syracuseStep 1964159 = 2946239) B2946239
theorem B2946245 : Blo 1963435 2946245 := bbase (se 4 (by rfl) ⟨276210, by rfl⟩ : syracuseStep 2946245 = 552421) (by norm_num)
theorem B1964163 : Blo 1963435 1964163 := bstep (se 1 (by rfl) ⟨1473122, by rfl⟩ : syracuseStep 1964163 = 2946245) B2946245
theorem B3314533 : Blo 1963435 3314533 := bbase (se 4 (by rfl) ⟨310737, by rfl⟩ : syracuseStep 3314533 = 621475) (by norm_num)
theorem B4419377 : Blo 1963435 4419377 := bstep (se 2 (by rfl) ⟨1657266, by rfl⟩ : syracuseStep 4419377 = 3314533) B3314533
theorem B2946251 : Blo 1963435 2946251 := bstep (se 1 (by rfl) ⟨2209688, by rfl⟩ : syracuseStep 2946251 = 4419377) B4419377
theorem B1964167 : Blo 1963435 1964167 := bstep (se 1 (by rfl) ⟨1473125, by rfl⟩ : syracuseStep 1964167 = 2946251) B2946251
theorem B2209693 : Blo 1963435 2209693 := bbase (se 3 (by rfl) ⟨414317, by rfl⟩ : syracuseStep 2209693 = 828635) (by norm_num)
theorem B2946257 : Blo 1963435 2946257 := bstep (se 2 (by rfl) ⟨1104846, by rfl⟩ : syracuseStep 2946257 = 2209693) B2209693
theorem B1964171 : Blo 1963435 1964171 := bstep (se 1 (by rfl) ⟨1473128, by rfl⟩ : syracuseStep 1964171 = 2946257) B2946257
theorem B6629093 : Blo 1963435 6629093 := bbase (se 4 (by rfl) ⟨621477, by rfl⟩ : syracuseStep 6629093 = 1242955) (by norm_num)
theorem B4419395 : Blo 1963435 4419395 := bstep (se 1 (by rfl) ⟨3314546, by rfl⟩ : syracuseStep 4419395 = 6629093) B6629093
theorem B2946263 : Blo 1963435 2946263 := bstep (se 1 (by rfl) ⟨2209697, by rfl⟩ : syracuseStep 2946263 = 4419395) B4419395
theorem B1964175 : Blo 1963435 1964175 := bstep (se 1 (by rfl) ⟨1473131, by rfl⟩ : syracuseStep 1964175 = 2946263) B2946263
theorem B2946269 : Blo 1963435 2946269 := bbase (se 3 (by rfl) ⟨552425, by rfl⟩ : syracuseStep 2946269 = 1104851) (by norm_num)
theorem B1964179 : Blo 1963435 1964179 := bstep (se 1 (by rfl) ⟨1473134, by rfl⟩ : syracuseStep 1964179 = 2946269) B2946269
theorem B4419413 : Blo 1963435 4419413 := bbase (se 9 (by rfl) ⟨12947, by rfl⟩ : syracuseStep 4419413 = 25895) (by norm_num)
theorem B2946275 : Blo 1963435 2946275 := bstep (se 1 (by rfl) ⟨2209706, by rfl⟩ : syracuseStep 2946275 = 4419413) B4419413
theorem B1964183 : Blo 1963435 1964183 := bstep (se 1 (by rfl) ⟨1473137, by rfl⟩ : syracuseStep 1964183 = 2946275) B2946275
theorem B5593333 : Blo 1963435 5593333 := bbase (se 5 (by rfl) ⟨262187, by rfl⟩ : syracuseStep 5593333 = 524375) (by norm_num)
theorem B7457777 : Blo 1963435 7457777 := bstep (se 2 (by rfl) ⟨2796666, by rfl⟩ : syracuseStep 7457777 = 5593333) B5593333
theorem B4971851 : Blo 1963435 4971851 := bstep (se 1 (by rfl) ⟨3728888, by rfl⟩ : syracuseStep 4971851 = 7457777) B7457777
theorem B3314567 : Blo 1963435 3314567 := bstep (se 1 (by rfl) ⟨2485925, by rfl⟩ : syracuseStep 3314567 = 4971851) B4971851
theorem B2209711 : Blo 1963435 2209711 := bstep (se 1 (by rfl) ⟨1657283, by rfl⟩ : syracuseStep 2209711 = 3314567) B3314567
theorem B2946281 : Blo 1963435 2946281 := bstep (se 2 (by rfl) ⟨1104855, by rfl⟩ : syracuseStep 2946281 = 2209711) B2209711
theorem B1964187 : Blo 1963435 1964187 := bstep (se 1 (by rfl) ⟨1473140, by rfl⟩ : syracuseStep 1964187 = 2946281) B2946281
theorem B5178149 : Blo 1963435 5178149 := bbase (se 4 (by rfl) ⟨485451, by rfl⟩ : syracuseStep 5178149 = 970903) (by norm_num)
theorem B3452099 : Blo 1963435 3452099 := bstep (se 1 (by rfl) ⟨2589074, by rfl⟩ : syracuseStep 3452099 = 5178149) B5178149
theorem B9205597 : Blo 1963435 9205597 := bstep (se 3 (by rfl) ⟨1726049, by rfl⟩ : syracuseStep 9205597 = 3452099) B3452099
theorem B785544277 : Blo 1963435 785544277 := bstep (se 8 (by rfl) ⟨4602798, by rfl⟩ : syracuseStep 785544277 = 9205597) B9205597
theorem B1047392369 : Blo 1963435 1047392369 := bstep (se 2 (by rfl) ⟨392772138, by rfl⟩ : syracuseStep 1047392369 = 785544277) B785544277
theorem B698261579 : Blo 1963435 698261579 := bstep (se 1 (by rfl) ⟨523696184, by rfl⟩ : syracuseStep 698261579 = 1047392369) B1047392369
theorem B465507719 : Blo 1963435 465507719 := bstep (se 1 (by rfl) ⟨349130789, by rfl⟩ : syracuseStep 465507719 = 698261579) B698261579
theorem B310338479 : Blo 1963435 310338479 := bstep (se 1 (by rfl) ⟨232753859, by rfl⟩ : syracuseStep 310338479 = 465507719) B465507719
theorem B206892319 : Blo 1963435 206892319 := bstep (se 1 (by rfl) ⟨155169239, by rfl⟩ : syracuseStep 206892319 = 310338479) B310338479
theorem B275856425 : Blo 1963435 275856425 := bstep (se 2 (by rfl) ⟨103446159, by rfl⟩ : syracuseStep 275856425 = 206892319) B206892319
theorem B183904283 : Blo 1963435 183904283 := bstep (se 1 (by rfl) ⟨137928212, by rfl⟩ : syracuseStep 183904283 = 275856425) B275856425
theorem B122602855 : Blo 1963435 122602855 := bstep (se 1 (by rfl) ⟨91952141, by rfl⟩ : syracuseStep 122602855 = 183904283) B183904283
theorem B163470473 : Blo 1963435 163470473 := bstep (se 2 (by rfl) ⟨61301427, by rfl⟩ : syracuseStep 163470473 = 122602855) B122602855
theorem B108980315 : Blo 1963435 108980315 := bstep (se 1 (by rfl) ⟨81735236, by rfl⟩ : syracuseStep 108980315 = 163470473) B163470473
theorem B72653543 : Blo 1963435 72653543 := bstep (se 1 (by rfl) ⟨54490157, by rfl⟩ : syracuseStep 72653543 = 108980315) B108980315
theorem B48435695 : Blo 1963435 48435695 := bstep (se 1 (by rfl) ⟨36326771, by rfl⟩ : syracuseStep 48435695 = 72653543) B72653543
theorem B32290463 : Blo 1963435 32290463 := bstep (se 1 (by rfl) ⟨24217847, by rfl⟩ : syracuseStep 32290463 = 48435695) B48435695
theorem B21526975 : Blo 1963435 21526975 := bstep (se 1 (by rfl) ⟨16145231, by rfl⟩ : syracuseStep 21526975 = 32290463) B32290463
theorem B28702633 : Blo 1963435 28702633 := bstep (se 2 (by rfl) ⟨10763487, by rfl⟩ : syracuseStep 28702633 = 21526975) B21526975
theorem B38270177 : Blo 1963435 38270177 := bstep (se 2 (by rfl) ⟨14351316, by rfl⟩ : syracuseStep 38270177 = 28702633) B28702633
theorem B25513451 : Blo 1963435 25513451 := bstep (se 1 (by rfl) ⟨19135088, by rfl⟩ : syracuseStep 25513451 = 38270177) B38270177
theorem B17008967 : Blo 1963435 17008967 := bstep (se 1 (by rfl) ⟨12756725, by rfl⟩ : syracuseStep 17008967 = 25513451) B25513451
theorem B45357245 : Blo 1963435 45357245 := bstep (se 3 (by rfl) ⟨8504483, by rfl⟩ : syracuseStep 45357245 = 17008967) B17008967
theorem B30238163 : Blo 1963435 30238163 := bstep (se 1 (by rfl) ⟨22678622, by rfl⟩ : syracuseStep 30238163 = 45357245) B45357245
theorem B20158775 : Blo 1963435 20158775 := bstep (se 1 (by rfl) ⟨15119081, by rfl⟩ : syracuseStep 20158775 = 30238163) B30238163
theorem B215026933 : Blo 1963435 215026933 := bstep (se 5 (by rfl) ⟨10079387, by rfl⟩ : syracuseStep 215026933 = 20158775) B20158775
theorem B286702577 : Blo 1963435 286702577 := bstep (se 2 (by rfl) ⟨107513466, by rfl⟩ : syracuseStep 286702577 = 215026933) B215026933
theorem B191135051 : Blo 1963435 191135051 := bstep (se 1 (by rfl) ⟨143351288, by rfl⟩ : syracuseStep 191135051 = 286702577) B286702577
theorem B127423367 : Blo 1963435 127423367 := bstep (se 1 (by rfl) ⟨95567525, by rfl⟩ : syracuseStep 127423367 = 191135051) B191135051
theorem B84948911 : Blo 1963435 84948911 := bstep (se 1 (by rfl) ⟨63711683, by rfl⟩ : syracuseStep 84948911 = 127423367) B127423367
theorem B56632607 : Blo 1963435 56632607 := bstep (se 1 (by rfl) ⟨42474455, by rfl⟩ : syracuseStep 56632607 = 84948911) B84948911
theorem B37755071 : Blo 1963435 37755071 := bstep (se 1 (by rfl) ⟨28316303, by rfl⟩ : syracuseStep 37755071 = 56632607) B56632607
theorem B25170047 : Blo 1963435 25170047 := bstep (se 1 (by rfl) ⟨18877535, by rfl⟩ : syracuseStep 25170047 = 37755071) B37755071
theorem B16780031 : Blo 1963435 16780031 := bstep (se 1 (by rfl) ⟨12585023, by rfl⟩ : syracuseStep 16780031 = 25170047) B25170047
theorem B11186687 : Blo 1963435 11186687 := bstep (se 1 (by rfl) ⟨8390015, by rfl⟩ : syracuseStep 11186687 = 16780031) B16780031
theorem B7457791 : Blo 1963435 7457791 := bstep (se 1 (by rfl) ⟨5593343, by rfl⟩ : syracuseStep 7457791 = 11186687) B11186687
theorem B9943721 : Blo 1963435 9943721 := bstep (se 2 (by rfl) ⟨3728895, by rfl⟩ : syracuseStep 9943721 = 7457791) B7457791
theorem B6629147 : Blo 1963435 6629147 := bstep (se 1 (by rfl) ⟨4971860, by rfl⟩ : syracuseStep 6629147 = 9943721) B9943721
theorem B4419431 : Blo 1963435 4419431 := bstep (se 1 (by rfl) ⟨3314573, by rfl⟩ : syracuseStep 4419431 = 6629147) B6629147
theorem B2946287 : Blo 1963435 2946287 := bstep (se 1 (by rfl) ⟨2209715, by rfl⟩ : syracuseStep 2946287 = 4419431) B4419431
theorem B1964191 : Blo 1963435 1964191 := bstep (se 1 (by rfl) ⟨1473143, by rfl⟩ : syracuseStep 1964191 = 2946287) B2946287
theorem B2946293 : Blo 1963435 2946293 := bbase (se 5 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 2946293 = 276215) (by norm_num)
theorem B1964195 : Blo 1963435 1964195 := bstep (se 1 (by rfl) ⟨1473146, by rfl⟩ : syracuseStep 1964195 = 2946293) B2946293
theorem B12585077 : Blo 1963435 12585077 := bbase (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) (by norm_num)
theorem B8390051 : Blo 1963435 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B5593367 : Blo 1963435 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B3728911 : Blo 1963435 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B4971881 : Blo 1963435 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B3314587 : Blo 1963435 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B4419449 : Blo 1963435 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B2946299 : Blo 1963435 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B1964199 : Blo 1963435 1964199 := bstep (se 1 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 1964199 = 2946299) B2946299
theorem B2209729 : Blo 1963435 2209729 := bbase (se 2 (by rfl) ⟨828648, by rfl⟩ : syracuseStep 2209729 = 1657297) (by norm_num)
theorem B2946305 : Blo 1963435 2946305 := bstep (se 2 (by rfl) ⟨1104864, by rfl⟩ : syracuseStep 2946305 = 2209729) B2209729
theorem B1964203 : Blo 1963435 1964203 := bstep (se 1 (by rfl) ⟨1473152, by rfl⟩ : syracuseStep 1964203 = 2946305) B2946305
theorem B4971901 : Blo 1963435 4971901 := bbase (se 3 (by rfl) ⟨932231, by rfl⟩ : syracuseStep 4971901 = 1864463) (by norm_num)
theorem B6629201 : Blo 1963435 6629201 := bstep (se 2 (by rfl) ⟨2485950, by rfl⟩ : syracuseStep 6629201 = 4971901) B4971901
theorem B4419467 : Blo 1963435 4419467 := bstep (se 1 (by rfl) ⟨3314600, by rfl⟩ : syracuseStep 4419467 = 6629201) B6629201
theorem B2946311 : Blo 1963435 2946311 := bstep (se 1 (by rfl) ⟨2209733, by rfl⟩ : syracuseStep 2946311 = 4419467) B4419467
theorem B1964207 : Blo 1963435 1964207 := bstep (se 1 (by rfl) ⟨1473155, by rfl⟩ : syracuseStep 1964207 = 2946311) B2946311
theorem B2946317 : Blo 1963435 2946317 := bbase (se 3 (by rfl) ⟨552434, by rfl⟩ : syracuseStep 2946317 = 1104869) (by norm_num)
theorem B1964211 : Blo 1963435 1964211 := bstep (se 1 (by rfl) ⟨1473158, by rfl⟩ : syracuseStep 1964211 = 2946317) B2946317
theorem B4419485 : Blo 1963435 4419485 := bbase (se 3 (by rfl) ⟨828653, by rfl⟩ : syracuseStep 4419485 = 1657307) (by norm_num)
theorem B2946323 : Blo 1963435 2946323 := bstep (se 1 (by rfl) ⟨2209742, by rfl⟩ : syracuseStep 2946323 = 4419485) B4419485
theorem B1964215 : Blo 1963435 1964215 := bstep (se 1 (by rfl) ⟨1473161, by rfl⟩ : syracuseStep 1964215 = 2946323) B2946323
theorem B3314621 : Blo 1963435 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B2209747 : Blo 1963435 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B2946329 : Blo 1963435 2946329 := bstep (se 2 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 2946329 = 2209747) B2209747
theorem B1964219 : Blo 1963435 1964219 := bstep (se 1 (by rfl) ⟨1473164, by rfl⟩ : syracuseStep 1964219 = 2946329) B2946329
theorem B11186869 : Blo 1963435 11186869 := bbase (se 5 (by rfl) ⟨524384, by rfl⟩ : syracuseStep 11186869 = 1048769) (by norm_num)
theorem B14915825 : Blo 1963435 14915825 := bstep (se 2 (by rfl) ⟨5593434, by rfl⟩ : syracuseStep 14915825 = 11186869) B11186869
theorem B9943883 : Blo 1963435 9943883 := bstep (se 1 (by rfl) ⟨7457912, by rfl⟩ : syracuseStep 9943883 = 14915825) B14915825
theorem B6629255 : Blo 1963435 6629255 := bstep (se 1 (by rfl) ⟨4971941, by rfl⟩ : syracuseStep 6629255 = 9943883) B9943883
theorem B4419503 : Blo 1963435 4419503 := bstep (se 1 (by rfl) ⟨3314627, by rfl⟩ : syracuseStep 4419503 = 6629255) B6629255
theorem B2946335 : Blo 1963435 2946335 := bstep (se 1 (by rfl) ⟨2209751, by rfl⟩ : syracuseStep 2946335 = 4419503) B4419503
theorem B1964223 : Blo 1963435 1964223 := bstep (se 1 (by rfl) ⟨1473167, by rfl⟩ : syracuseStep 1964223 = 2946335) B2946335
theorem B2946341 : Blo 1963435 2946341 := bbase (se 4 (by rfl) ⟨276219, by rfl⟩ : syracuseStep 2946341 = 552439) (by norm_num)
theorem B1964227 : Blo 1963435 1964227 := bstep (se 1 (by rfl) ⟨1473170, by rfl⟩ : syracuseStep 1964227 = 2946341) B2946341
theorem B2485981 : Blo 1963435 2485981 := bbase (se 3 (by rfl) ⟨466121, by rfl⟩ : syracuseStep 2485981 = 932243) (by norm_num)
theorem B3314641 : Blo 1963435 3314641 := bstep (se 2 (by rfl) ⟨1242990, by rfl⟩ : syracuseStep 3314641 = 2485981) B2485981
theorem B4419521 : Blo 1963435 4419521 := bstep (se 2 (by rfl) ⟨1657320, by rfl⟩ : syracuseStep 4419521 = 3314641) B3314641
theorem B2946347 : Blo 1963435 2946347 := bstep (se 1 (by rfl) ⟨2209760, by rfl⟩ : syracuseStep 2946347 = 4419521) B4419521
theorem B1964231 : Blo 1963435 1964231 := bstep (se 1 (by rfl) ⟨1473173, by rfl⟩ : syracuseStep 1964231 = 2946347) B2946347
theorem B2209765 : Blo 1963435 2209765 := bbase (se 4 (by rfl) ⟨207165, by rfl⟩ : syracuseStep 2209765 = 414331) (by norm_num)
theorem B2946353 : Blo 1963435 2946353 := bstep (se 2 (by rfl) ⟨1104882, by rfl⟩ : syracuseStep 2946353 = 2209765) B2209765
theorem B1964235 : Blo 1963435 1964235 := bstep (se 1 (by rfl) ⟨1473176, by rfl⟩ : syracuseStep 1964235 = 2946353) B2946353
theorem B24218453 : Blo 1963435 24218453 := bbase (se 9 (by rfl) ⟨70952, by rfl⟩ : syracuseStep 24218453 = 141905) (by norm_num)
theorem B16145635 : Blo 1963435 16145635 := bstep (se 1 (by rfl) ⟨12109226, by rfl⟩ : syracuseStep 16145635 = 24218453) B24218453
theorem B21527513 : Blo 1963435 21527513 := bstep (se 2 (by rfl) ⟨8072817, by rfl⟩ : syracuseStep 21527513 = 16145635) B16145635
theorem B14351675 : Blo 1963435 14351675 := bstep (se 1 (by rfl) ⟨10763756, by rfl⟩ : syracuseStep 14351675 = 21527513) B21527513
theorem B38271133 : Blo 1963435 38271133 := bstep (se 3 (by rfl) ⟨7175837, by rfl⟩ : syracuseStep 38271133 = 14351675) B14351675
theorem B51028177 : Blo 1963435 51028177 := bstep (se 2 (by rfl) ⟨19135566, by rfl⟩ : syracuseStep 51028177 = 38271133) B38271133
theorem B68037569 : Blo 1963435 68037569 := bstep (se 2 (by rfl) ⟨25514088, by rfl⟩ : syracuseStep 68037569 = 51028177) B51028177
theorem B45358379 : Blo 1963435 45358379 := bstep (se 1 (by rfl) ⟨34018784, by rfl⟩ : syracuseStep 45358379 = 68037569) B68037569
theorem B30238919 : Blo 1963435 30238919 := bstep (se 1 (by rfl) ⟨22679189, by rfl⟩ : syracuseStep 30238919 = 45358379) B45358379
theorem B20159279 : Blo 1963435 20159279 := bstep (se 1 (by rfl) ⟨15119459, by rfl⟩ : syracuseStep 20159279 = 30238919) B30238919
theorem B13439519 : Blo 1963435 13439519 := bstep (se 1 (by rfl) ⟨10079639, by rfl⟩ : syracuseStep 13439519 = 20159279) B20159279
theorem B8959679 : Blo 1963435 8959679 := bstep (se 1 (by rfl) ⟨6719759, by rfl⟩ : syracuseStep 8959679 = 13439519) B13439519
theorem B5973119 : Blo 1963435 5973119 := bstep (se 1 (by rfl) ⟨4479839, by rfl⟩ : syracuseStep 5973119 = 8959679) B8959679
theorem B3982079 : Blo 1963435 3982079 := bstep (se 1 (by rfl) ⟨2986559, by rfl⟩ : syracuseStep 3982079 = 5973119) B5973119
theorem B10618877 : Blo 1963435 10618877 := bstep (se 3 (by rfl) ⟨1991039, by rfl⟩ : syracuseStep 10618877 = 3982079) B3982079
theorem B7079251 : Blo 1963435 7079251 := bstep (se 1 (by rfl) ⟨5309438, by rfl⟩ : syracuseStep 7079251 = 10618877) B10618877
theorem B9439001 : Blo 1963435 9439001 := bstep (se 2 (by rfl) ⟨3539625, by rfl⟩ : syracuseStep 9439001 = 7079251) B7079251
theorem B6292667 : Blo 1963435 6292667 := bstep (se 1 (by rfl) ⟨4719500, by rfl⟩ : syracuseStep 6292667 = 9439001) B9439001
theorem B4195111 : Blo 1963435 4195111 := bstep (se 1 (by rfl) ⟨3146333, by rfl⟩ : syracuseStep 4195111 = 6292667) B6292667
theorem B5593481 : Blo 1963435 5593481 := bstep (se 2 (by rfl) ⟨2097555, by rfl⟩ : syracuseStep 5593481 = 4195111) B4195111
theorem B3728987 : Blo 1963435 3728987 := bstep (se 1 (by rfl) ⟨2796740, by rfl⟩ : syracuseStep 3728987 = 5593481) B5593481
theorem B2485991 : Blo 1963435 2485991 := bstep (se 1 (by rfl) ⟨1864493, by rfl⟩ : syracuseStep 2485991 = 3728987) B3728987
theorem B6629309 : Blo 1963435 6629309 := bstep (se 3 (by rfl) ⟨1242995, by rfl⟩ : syracuseStep 6629309 = 2485991) B2485991
theorem B4419539 : Blo 1963435 4419539 := bstep (se 1 (by rfl) ⟨3314654, by rfl⟩ : syracuseStep 4419539 = 6629309) B6629309
theorem B2946359 : Blo 1963435 2946359 := bstep (se 1 (by rfl) ⟨2209769, by rfl⟩ : syracuseStep 2946359 = 4419539) B4419539
theorem B1964239 : Blo 1963435 1964239 := bstep (se 1 (by rfl) ⟨1473179, by rfl⟩ : syracuseStep 1964239 = 2946359) B2946359
theorem B2946365 : Blo 1963435 2946365 := bbase (se 3 (by rfl) ⟨552443, by rfl⟩ : syracuseStep 2946365 = 1104887) (by norm_num)
theorem B1964243 : Blo 1963435 1964243 := bstep (se 1 (by rfl) ⟨1473182, by rfl⟩ : syracuseStep 1964243 = 2946365) B2946365
theorem B4419557 : Blo 1963435 4419557 := bbase (se 4 (by rfl) ⟨414333, by rfl⟩ : syracuseStep 4419557 = 828667) (by norm_num)
theorem B2946371 : Blo 1963435 2946371 := bstep (se 1 (by rfl) ⟨2209778, by rfl⟩ : syracuseStep 2946371 = 4419557) B4419557
theorem B1964247 : Blo 1963435 1964247 := bstep (se 1 (by rfl) ⟨1473185, by rfl⟩ : syracuseStep 1964247 = 2946371) B2946371
theorem B4972013 : Blo 1963435 4972013 := bbase (se 3 (by rfl) ⟨932252, by rfl⟩ : syracuseStep 4972013 = 1864505) (by norm_num)
theorem B3314675 : Blo 1963435 3314675 := bstep (se 1 (by rfl) ⟨2486006, by rfl⟩ : syracuseStep 3314675 = 4972013) B4972013
theorem B2209783 : Blo 1963435 2209783 := bstep (se 1 (by rfl) ⟨1657337, by rfl⟩ : syracuseStep 2209783 = 3314675) B3314675
theorem B2946377 : Blo 1963435 2946377 := bstep (se 2 (by rfl) ⟨1104891, by rfl⟩ : syracuseStep 2946377 = 2209783) B2209783
theorem B1964251 : Blo 1963435 1964251 := bstep (se 1 (by rfl) ⟨1473188, by rfl⟩ : syracuseStep 1964251 = 2946377) B2946377
theorem B2654741 : Blo 1963435 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B7079309 : Blo 1963435 7079309 := bstep (se 3 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 7079309 = 2654741) B2654741
theorem B4719539 : Blo 1963435 4719539 := bstep (se 1 (by rfl) ⟨3539654, by rfl⟩ : syracuseStep 4719539 = 7079309) B7079309
theorem B3146359 : Blo 1963435 3146359 := bstep (se 1 (by rfl) ⟨2359769, by rfl⟩ : syracuseStep 3146359 = 4719539) B4719539
theorem B4195145 : Blo 1963435 4195145 := bstep (se 2 (by rfl) ⟨1573179, by rfl⟩ : syracuseStep 4195145 = 3146359) B3146359
theorem B2796763 : Blo 1963435 2796763 := bstep (se 1 (by rfl) ⟨2097572, by rfl⟩ : syracuseStep 2796763 = 4195145) B4195145
theorem B3729017 : Blo 1963435 3729017 := bstep (se 2 (by rfl) ⟨1398381, by rfl⟩ : syracuseStep 3729017 = 2796763) B2796763
theorem B9944045 : Blo 1963435 9944045 := bstep (se 3 (by rfl) ⟨1864508, by rfl⟩ : syracuseStep 9944045 = 3729017) B3729017
theorem B6629363 : Blo 1963435 6629363 := bstep (se 1 (by rfl) ⟨4972022, by rfl⟩ : syracuseStep 6629363 = 9944045) B9944045
theorem B4419575 : Blo 1963435 4419575 := bstep (se 1 (by rfl) ⟨3314681, by rfl⟩ : syracuseStep 4419575 = 6629363) B6629363
theorem B2946383 : Blo 1963435 2946383 := bstep (se 1 (by rfl) ⟨2209787, by rfl⟩ : syracuseStep 2946383 = 4419575) B4419575
theorem B1964255 : Blo 1963435 1964255 := bstep (se 1 (by rfl) ⟨1473191, by rfl⟩ : syracuseStep 1964255 = 2946383) B2946383
theorem B2946389 : Blo 1963435 2946389 := bbase (se 13 (by rfl) ⟨539, by rfl⟩ : syracuseStep 2946389 = 1079) (by norm_num)
theorem B1964259 : Blo 1963435 1964259 := bstep (se 1 (by rfl) ⟨1473194, by rfl⟩ : syracuseStep 1964259 = 2946389) B2946389
theorem B2097581 : Blo 1963435 2097581 := bbase (se 3 (by rfl) ⟨393296, by rfl⟩ : syracuseStep 2097581 = 786593) (by norm_num)
theorem B5593549 : Blo 1963435 5593549 := bstep (se 3 (by rfl) ⟨1048790, by rfl⟩ : syracuseStep 5593549 = 2097581) B2097581
theorem B7458065 : Blo 1963435 7458065 := bstep (se 2 (by rfl) ⟨2796774, by rfl⟩ : syracuseStep 7458065 = 5593549) B5593549
theorem B4972043 : Blo 1963435 4972043 := bstep (se 1 (by rfl) ⟨3729032, by rfl⟩ : syracuseStep 4972043 = 7458065) B7458065
theorem B3314695 : Blo 1963435 3314695 := bstep (se 1 (by rfl) ⟨2486021, by rfl⟩ : syracuseStep 3314695 = 4972043) B4972043
theorem B4419593 : Blo 1963435 4419593 := bstep (se 2 (by rfl) ⟨1657347, by rfl⟩ : syracuseStep 4419593 = 3314695) B3314695
theorem B2946395 : Blo 1963435 2946395 := bstep (se 1 (by rfl) ⟨2209796, by rfl⟩ : syracuseStep 2946395 = 4419593) B4419593
theorem B1964263 : Blo 1963435 1964263 := bstep (se 1 (by rfl) ⟨1473197, by rfl⟩ : syracuseStep 1964263 = 2946395) B2946395
theorem B2209801 : Blo 1963435 2209801 := bbase (se 2 (by rfl) ⟨828675, by rfl⟩ : syracuseStep 2209801 = 1657351) (by norm_num)
theorem B2946401 : Blo 1963435 2946401 := bstep (se 2 (by rfl) ⟨1104900, by rfl⟩ : syracuseStep 2946401 = 2209801) B2209801
theorem B1964267 : Blo 1963435 1964267 := bstep (se 1 (by rfl) ⟨1473200, by rfl⟩ : syracuseStep 1964267 = 2946401) B2946401
theorem B4729445 : Blo 1963435 4729445 := bbase (se 4 (by rfl) ⟨443385, by rfl⟩ : syracuseStep 4729445 = 886771) (by norm_num)
theorem B3152963 : Blo 1963435 3152963 := bstep (se 1 (by rfl) ⟨2364722, by rfl⟩ : syracuseStep 3152963 = 4729445) B4729445
theorem B8407901 : Blo 1963435 8407901 := bstep (se 3 (by rfl) ⟨1576481, by rfl⟩ : syracuseStep 8407901 = 3152963) B3152963
theorem B22421069 : Blo 1963435 22421069 := bstep (se 3 (by rfl) ⟨4203950, by rfl⟩ : syracuseStep 22421069 = 8407901) B8407901
theorem B14947379 : Blo 1963435 14947379 := bstep (se 1 (by rfl) ⟨11210534, by rfl⟩ : syracuseStep 14947379 = 22421069) B22421069
theorem B9964919 : Blo 1963435 9964919 := bstep (se 1 (by rfl) ⟨7473689, by rfl⟩ : syracuseStep 9964919 = 14947379) B14947379
theorem B26573117 : Blo 1963435 26573117 := bstep (se 3 (by rfl) ⟨4982459, by rfl⟩ : syracuseStep 26573117 = 9964919) B9964919
theorem B70861645 : Blo 1963435 70861645 := bstep (se 3 (by rfl) ⟨13286558, by rfl⟩ : syracuseStep 70861645 = 26573117) B26573117
theorem B377928773 : Blo 1963435 377928773 := bstep (se 4 (by rfl) ⟨35430822, by rfl⟩ : syracuseStep 377928773 = 70861645) B70861645
theorem B251952515 : Blo 1963435 251952515 := bstep (se 1 (by rfl) ⟨188964386, by rfl⟩ : syracuseStep 251952515 = 377928773) B377928773
theorem B167968343 : Blo 1963435 167968343 := bstep (se 1 (by rfl) ⟨125976257, by rfl⟩ : syracuseStep 167968343 = 251952515) B251952515
theorem B111978895 : Blo 1963435 111978895 := bstep (se 1 (by rfl) ⟨83984171, by rfl⟩ : syracuseStep 111978895 = 167968343) B167968343
theorem B149305193 : Blo 1963435 149305193 := bstep (se 2 (by rfl) ⟨55989447, by rfl⟩ : syracuseStep 149305193 = 111978895) B111978895
theorem B99536795 : Blo 1963435 99536795 := bstep (se 1 (by rfl) ⟨74652596, by rfl⟩ : syracuseStep 99536795 = 149305193) B149305193
theorem B66357863 : Blo 1963435 66357863 := bstep (se 1 (by rfl) ⟨49768397, by rfl⟩ : syracuseStep 66357863 = 99536795) B99536795
theorem B44238575 : Blo 1963435 44238575 := bstep (se 1 (by rfl) ⟨33178931, by rfl⟩ : syracuseStep 44238575 = 66357863) B66357863
theorem B29492383 : Blo 1963435 29492383 := bstep (se 1 (by rfl) ⟨22119287, by rfl⟩ : syracuseStep 29492383 = 44238575) B44238575
theorem B39323177 : Blo 1963435 39323177 := bstep (se 2 (by rfl) ⟨14746191, by rfl⟩ : syracuseStep 39323177 = 29492383) B29492383
theorem B26215451 : Blo 1963435 26215451 := bstep (se 1 (by rfl) ⟨19661588, by rfl⟩ : syracuseStep 26215451 = 39323177) B39323177
theorem B17476967 : Blo 1963435 17476967 := bstep (se 1 (by rfl) ⟨13107725, by rfl⟩ : syracuseStep 17476967 = 26215451) B26215451
theorem B11651311 : Blo 1963435 11651311 := bstep (se 1 (by rfl) ⟨8738483, by rfl⟩ : syracuseStep 11651311 = 17476967) B17476967
theorem B15535081 : Blo 1963435 15535081 := bstep (se 2 (by rfl) ⟨5825655, by rfl⟩ : syracuseStep 15535081 = 11651311) B11651311
theorem B82853765 : Blo 1963435 82853765 := bstep (se 4 (by rfl) ⟨7767540, by rfl⟩ : syracuseStep 82853765 = 15535081) B15535081
theorem B55235843 : Blo 1963435 55235843 := bstep (se 1 (by rfl) ⟨41426882, by rfl⟩ : syracuseStep 55235843 = 82853765) B82853765
theorem B36823895 : Blo 1963435 36823895 := bstep (se 1 (by rfl) ⟨27617921, by rfl⟩ : syracuseStep 36823895 = 55235843) B55235843
theorem B24549263 : Blo 1963435 24549263 := bstep (se 1 (by rfl) ⟨18411947, by rfl⟩ : syracuseStep 24549263 = 36823895) B36823895
theorem B16366175 : Blo 1963435 16366175 := bstep (se 1 (by rfl) ⟨12274631, by rfl⟩ : syracuseStep 16366175 = 24549263) B24549263
theorem B10910783 : Blo 1963435 10910783 := bstep (se 1 (by rfl) ⟨8183087, by rfl⟩ : syracuseStep 10910783 = 16366175) B16366175
theorem B29095421 : Blo 1963435 29095421 := bstep (se 3 (by rfl) ⟨5455391, by rfl⟩ : syracuseStep 29095421 = 10910783) B10910783
theorem B77587789 : Blo 1963435 77587789 := bstep (se 3 (by rfl) ⟨14547710, by rfl⟩ : syracuseStep 77587789 = 29095421) B29095421
theorem B103450385 : Blo 1963435 103450385 := bstep (se 2 (by rfl) ⟨38793894, by rfl⟩ : syracuseStep 103450385 = 77587789) B77587789
theorem B68966923 : Blo 1963435 68966923 := bstep (se 1 (by rfl) ⟨51725192, by rfl⟩ : syracuseStep 68966923 = 103450385) B103450385
theorem B91955897 : Blo 1963435 91955897 := bstep (se 2 (by rfl) ⟨34483461, by rfl⟩ : syracuseStep 91955897 = 68966923) B68966923
theorem B61303931 : Blo 1963435 61303931 := bstep (se 1 (by rfl) ⟨45977948, by rfl⟩ : syracuseStep 61303931 = 91955897) B91955897
theorem B40869287 : Blo 1963435 40869287 := bstep (se 1 (by rfl) ⟨30651965, by rfl⟩ : syracuseStep 40869287 = 61303931) B61303931
theorem B27246191 : Blo 1963435 27246191 := bstep (se 1 (by rfl) ⟨20434643, by rfl⟩ : syracuseStep 27246191 = 40869287) B40869287
theorem B72656509 : Blo 1963435 72656509 := bstep (se 3 (by rfl) ⟨13623095, by rfl⟩ : syracuseStep 72656509 = 27246191) B27246191
theorem B96875345 : Blo 1963435 96875345 := bstep (se 2 (by rfl) ⟨36328254, by rfl⟩ : syracuseStep 96875345 = 72656509) B72656509
theorem B64583563 : Blo 1963435 64583563 := bstep (se 1 (by rfl) ⟨48437672, by rfl⟩ : syracuseStep 64583563 = 96875345) B96875345
theorem B86111417 : Blo 1963435 86111417 := bstep (se 2 (by rfl) ⟨32291781, by rfl⟩ : syracuseStep 86111417 = 64583563) B64583563
theorem B57407611 : Blo 1963435 57407611 := bstep (se 1 (by rfl) ⟨43055708, by rfl⟩ : syracuseStep 57407611 = 86111417) B86111417
theorem B76543481 : Blo 1963435 76543481 := bstep (se 2 (by rfl) ⟨28703805, by rfl⟩ : syracuseStep 76543481 = 57407611) B57407611
theorem B51028987 : Blo 1963435 51028987 := bstep (se 1 (by rfl) ⟨38271740, by rfl⟩ : syracuseStep 51028987 = 76543481) B76543481
theorem B68038649 : Blo 1963435 68038649 := bstep (se 2 (by rfl) ⟨25514493, by rfl⟩ : syracuseStep 68038649 = 51028987) B51028987
theorem B45359099 : Blo 1963435 45359099 := bstep (se 1 (by rfl) ⟨34019324, by rfl⟩ : syracuseStep 45359099 = 68038649) B68038649
theorem B30239399 : Blo 1963435 30239399 := bstep (se 1 (by rfl) ⟨22679549, by rfl⟩ : syracuseStep 30239399 = 45359099) B45359099
theorem B20159599 : Blo 1963435 20159599 := bstep (se 1 (by rfl) ⟨15119699, by rfl⟩ : syracuseStep 20159599 = 30239399) B30239399
theorem B26879465 : Blo 1963435 26879465 := bstep (se 2 (by rfl) ⟨10079799, by rfl⟩ : syracuseStep 26879465 = 20159599) B20159599
theorem B17919643 : Blo 1963435 17919643 := bstep (se 1 (by rfl) ⟨13439732, by rfl⟩ : syracuseStep 17919643 = 26879465) B26879465
theorem B23892857 : Blo 1963435 23892857 := bstep (se 2 (by rfl) ⟨8959821, by rfl⟩ : syracuseStep 23892857 = 17919643) B17919643
theorem B15928571 : Blo 1963435 15928571 := bstep (se 1 (by rfl) ⟨11946428, by rfl⟩ : syracuseStep 15928571 = 23892857) B23892857
theorem B10619047 : Blo 1963435 10619047 := bstep (se 1 (by rfl) ⟨7964285, by rfl⟩ : syracuseStep 10619047 = 15928571) B15928571
theorem B14158729 : Blo 1963435 14158729 := bstep (se 2 (by rfl) ⟨5309523, by rfl⟩ : syracuseStep 14158729 = 10619047) B10619047
theorem B18878305 : Blo 1963435 18878305 := bstep (se 2 (by rfl) ⟨7079364, by rfl⟩ : syracuseStep 18878305 = 14158729) B14158729
theorem B25171073 : Blo 1963435 25171073 := bstep (se 2 (by rfl) ⟨9439152, by rfl⟩ : syracuseStep 25171073 = 18878305) B18878305
theorem B16780715 : Blo 1963435 16780715 := bstep (se 1 (by rfl) ⟨12585536, by rfl⟩ : syracuseStep 16780715 = 25171073) B25171073
theorem B11187143 : Blo 1963435 11187143 := bstep (se 1 (by rfl) ⟨8390357, by rfl⟩ : syracuseStep 11187143 = 16780715) B16780715
theorem B7458095 : Blo 1963435 7458095 := bstep (se 1 (by rfl) ⟨5593571, by rfl⟩ : syracuseStep 7458095 = 11187143) B11187143
theorem B4972063 : Blo 1963435 4972063 := bstep (se 1 (by rfl) ⟨3729047, by rfl⟩ : syracuseStep 4972063 = 7458095) B7458095
theorem B6629417 : Blo 1963435 6629417 := bstep (se 2 (by rfl) ⟨2486031, by rfl⟩ : syracuseStep 6629417 = 4972063) B4972063
theorem B4419611 : Blo 1963435 4419611 := bstep (se 1 (by rfl) ⟨3314708, by rfl⟩ : syracuseStep 4419611 = 6629417) B6629417
theorem B2946407 : Blo 1963435 2946407 := bstep (se 1 (by rfl) ⟨2209805, by rfl⟩ : syracuseStep 2946407 = 4419611) B4419611
theorem B1964271 : Blo 1963435 1964271 := bstep (se 1 (by rfl) ⟨1473203, by rfl⟩ : syracuseStep 1964271 = 2946407) B2946407
theorem B2946413 : Blo 1963435 2946413 := bbase (se 3 (by rfl) ⟨552452, by rfl⟩ : syracuseStep 2946413 = 1104905) (by norm_num)
theorem B1964275 : Blo 1963435 1964275 := bstep (se 1 (by rfl) ⟨1473206, by rfl⟩ : syracuseStep 1964275 = 2946413) B2946413
theorem B4419629 : Blo 1963435 4419629 := bbase (se 3 (by rfl) ⟨828680, by rfl⟩ : syracuseStep 4419629 = 1657361) (by norm_num)
theorem B2946419 : Blo 1963435 2946419 := bstep (se 1 (by rfl) ⟨2209814, by rfl⟩ : syracuseStep 2946419 = 4419629) B4419629
theorem B1964279 : Blo 1963435 1964279 := bstep (se 1 (by rfl) ⟨1473209, by rfl⟩ : syracuseStep 1964279 = 2946419) B2946419
theorem B4479941 : Blo 1963435 4479941 := bbase (se 4 (by rfl) ⟨419994, by rfl⟩ : syracuseStep 4479941 = 839989) (by norm_num)
theorem B2986627 : Blo 1963435 2986627 := bstep (se 1 (by rfl) ⟨2239970, by rfl⟩ : syracuseStep 2986627 = 4479941) B4479941
theorem B3982169 : Blo 1963435 3982169 := bstep (se 2 (by rfl) ⟨1493313, by rfl⟩ : syracuseStep 3982169 = 2986627) B2986627
theorem B2654779 : Blo 1963435 2654779 := bstep (se 1 (by rfl) ⟨1991084, by rfl⟩ : syracuseStep 2654779 = 3982169) B3982169
theorem B3539705 : Blo 1963435 3539705 := bstep (se 2 (by rfl) ⟨1327389, by rfl⟩ : syracuseStep 3539705 = 2654779) B2654779
theorem B9439213 : Blo 1963435 9439213 := bstep (se 3 (by rfl) ⟨1769852, by rfl⟩ : syracuseStep 9439213 = 3539705) B3539705
theorem B12585617 : Blo 1963435 12585617 := bstep (se 2 (by rfl) ⟨4719606, by rfl⟩ : syracuseStep 12585617 = 9439213) B9439213
theorem B8390411 : Blo 1963435 8390411 := bstep (se 1 (by rfl) ⟨6292808, by rfl⟩ : syracuseStep 8390411 = 12585617) B12585617
theorem B5593607 : Blo 1963435 5593607 := bstep (se 1 (by rfl) ⟨4195205, by rfl⟩ : syracuseStep 5593607 = 8390411) B8390411
theorem B3729071 : Blo 1963435 3729071 := bstep (se 1 (by rfl) ⟨2796803, by rfl⟩ : syracuseStep 3729071 = 5593607) B5593607
theorem B2486047 : Blo 1963435 2486047 := bstep (se 1 (by rfl) ⟨1864535, by rfl⟩ : syracuseStep 2486047 = 3729071) B3729071
theorem B3314729 : Blo 1963435 3314729 := bstep (se 2 (by rfl) ⟨1243023, by rfl⟩ : syracuseStep 3314729 = 2486047) B2486047
theorem B2209819 : Blo 1963435 2209819 := bstep (se 1 (by rfl) ⟨1657364, by rfl⟩ : syracuseStep 2209819 = 3314729) B3314729
theorem B2946425 : Blo 1963435 2946425 := bstep (se 2 (by rfl) ⟨1104909, by rfl⟩ : syracuseStep 2946425 = 2209819) B2209819
theorem B1964283 : Blo 1963435 1964283 := bstep (se 1 (by rfl) ⟨1473212, by rfl⟩ : syracuseStep 1964283 = 2946425) B2946425
theorem B34019605 : Blo 1963435 34019605 := bbase (se 6 (by rfl) ⟨797334, by rfl⟩ : syracuseStep 34019605 = 1594669) (by norm_num)
theorem B45359473 : Blo 1963435 45359473 := bstep (se 2 (by rfl) ⟨17009802, by rfl⟩ : syracuseStep 45359473 = 34019605) B34019605
theorem B60479297 : Blo 1963435 60479297 := bstep (se 2 (by rfl) ⟨22679736, by rfl⟩ : syracuseStep 60479297 = 45359473) B45359473
theorem B40319531 : Blo 1963435 40319531 := bstep (se 1 (by rfl) ⟨30239648, by rfl⟩ : syracuseStep 40319531 = 60479297) B60479297
theorem B26879687 : Blo 1963435 26879687 := bstep (se 1 (by rfl) ⟨20159765, by rfl⟩ : syracuseStep 26879687 = 40319531) B40319531
theorem B17919791 : Blo 1963435 17919791 := bstep (se 1 (by rfl) ⟨13439843, by rfl⟩ : syracuseStep 17919791 = 26879687) B26879687
theorem B11946527 : Blo 1963435 11946527 := bstep (se 1 (by rfl) ⟨8959895, by rfl⟩ : syracuseStep 11946527 = 17919791) B17919791
theorem B7964351 : Blo 1963435 7964351 := bstep (se 1 (by rfl) ⟨5973263, by rfl⟩ : syracuseStep 7964351 = 11946527) B11946527
theorem B5309567 : Blo 1963435 5309567 := bstep (se 1 (by rfl) ⟨3982175, by rfl⟩ : syracuseStep 5309567 = 7964351) B7964351
theorem B3539711 : Blo 1963435 3539711 := bstep (se 1 (by rfl) ⟨2654783, by rfl⟩ : syracuseStep 3539711 = 5309567) B5309567
theorem B9439229 : Blo 1963435 9439229 := bstep (se 3 (by rfl) ⟨1769855, by rfl⟩ : syracuseStep 9439229 = 3539711) B3539711
theorem B6292819 : Blo 1963435 6292819 := bstep (se 1 (by rfl) ⟨4719614, by rfl⟩ : syracuseStep 6292819 = 9439229) B9439229
theorem B33561701 : Blo 1963435 33561701 := bstep (se 4 (by rfl) ⟨3146409, by rfl⟩ : syracuseStep 33561701 = 6292819) B6292819
theorem B22374467 : Blo 1963435 22374467 := bstep (se 1 (by rfl) ⟨16780850, by rfl⟩ : syracuseStep 22374467 = 33561701) B33561701
theorem B14916311 : Blo 1963435 14916311 := bstep (se 1 (by rfl) ⟨11187233, by rfl⟩ : syracuseStep 14916311 = 22374467) B22374467
theorem B9944207 : Blo 1963435 9944207 := bstep (se 1 (by rfl) ⟨7458155, by rfl⟩ : syracuseStep 9944207 = 14916311) B14916311
theorem B6629471 : Blo 1963435 6629471 := bstep (se 1 (by rfl) ⟨4972103, by rfl⟩ : syracuseStep 6629471 = 9944207) B9944207
theorem B4419647 : Blo 1963435 4419647 := bstep (se 1 (by rfl) ⟨3314735, by rfl⟩ : syracuseStep 4419647 = 6629471) B6629471
theorem B2946431 : Blo 1963435 2946431 := bstep (se 1 (by rfl) ⟨2209823, by rfl⟩ : syracuseStep 2946431 = 4419647) B4419647
theorem B1964287 : Blo 1963435 1964287 := bstep (se 1 (by rfl) ⟨1473215, by rfl⟩ : syracuseStep 1964287 = 2946431) B2946431
theorem B2946437 : Blo 1963435 2946437 := bbase (se 4 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 2946437 = 552457) (by norm_num)
theorem B1964291 : Blo 1963435 1964291 := bstep (se 1 (by rfl) ⟨1473218, by rfl⟩ : syracuseStep 1964291 = 2946437) B2946437
theorem B3314749 : Blo 1963435 3314749 := bbase (se 3 (by rfl) ⟨621515, by rfl⟩ : syracuseStep 3314749 = 1243031) (by norm_num)
theorem B4419665 : Blo 1963435 4419665 := bstep (se 2 (by rfl) ⟨1657374, by rfl⟩ : syracuseStep 4419665 = 3314749) B3314749
theorem B2946443 : Blo 1963435 2946443 := bstep (se 1 (by rfl) ⟨2209832, by rfl⟩ : syracuseStep 2946443 = 4419665) B4419665
theorem B1964295 : Blo 1963435 1964295 := bstep (se 1 (by rfl) ⟨1473221, by rfl⟩ : syracuseStep 1964295 = 2946443) B2946443
theorem B2209837 : Blo 1963435 2209837 := bbase (se 3 (by rfl) ⟨414344, by rfl⟩ : syracuseStep 2209837 = 828689) (by norm_num)
theorem B2946449 : Blo 1963435 2946449 := bstep (se 2 (by rfl) ⟨1104918, by rfl⟩ : syracuseStep 2946449 = 2209837) B2209837
theorem B1964299 : Blo 1963435 1964299 := bstep (se 1 (by rfl) ⟨1473224, by rfl⟩ : syracuseStep 1964299 = 2946449) B2946449
theorem B6629525 : Blo 1963435 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B4419683 : Blo 1963435 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B2946455 : Blo 1963435 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B1964303 : Blo 1963435 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B2946461 : Blo 1963435 2946461 := bbase (se 3 (by rfl) ⟨552461, by rfl⟩ : syracuseStep 2946461 = 1104923) (by norm_num)
theorem B1964307 : Blo 1963435 1964307 := bstep (se 1 (by rfl) ⟨1473230, by rfl⟩ : syracuseStep 1964307 = 2946461) B2946461
theorem B4419701 : Blo 1963435 4419701 := bbase (se 5 (by rfl) ⟨207173, by rfl⟩ : syracuseStep 4419701 = 414347) (by norm_num)
theorem B2946467 : Blo 1963435 2946467 := bstep (se 1 (by rfl) ⟨2209850, by rfl⟩ : syracuseStep 2946467 = 4419701) B4419701
theorem B1964311 : Blo 1963435 1964311 := bstep (se 1 (by rfl) ⟨1473233, by rfl⟩ : syracuseStep 1964311 = 2946467) B2946467
theorem B7079525 : Blo 1963435 7079525 := bbase (se 4 (by rfl) ⟨663705, by rfl⟩ : syracuseStep 7079525 = 1327411) (by norm_num)
theorem B4719683 : Blo 1963435 4719683 := bstep (se 1 (by rfl) ⟨3539762, by rfl⟩ : syracuseStep 4719683 = 7079525) B7079525
theorem B3146455 : Blo 1963435 3146455 := bstep (se 1 (by rfl) ⟨2359841, by rfl⟩ : syracuseStep 3146455 = 4719683) B4719683
theorem B16781093 : Blo 1963435 16781093 := bstep (se 4 (by rfl) ⟨1573227, by rfl⟩ : syracuseStep 16781093 = 3146455) B3146455
theorem B11187395 : Blo 1963435 11187395 := bstep (se 1 (by rfl) ⟨8390546, by rfl⟩ : syracuseStep 11187395 = 16781093) B16781093
theorem B7458263 : Blo 1963435 7458263 := bstep (se 1 (by rfl) ⟨5593697, by rfl⟩ : syracuseStep 7458263 = 11187395) B11187395
theorem B4972175 : Blo 1963435 4972175 := bstep (se 1 (by rfl) ⟨3729131, by rfl⟩ : syracuseStep 4972175 = 7458263) B7458263
theorem B3314783 : Blo 1963435 3314783 := bstep (se 1 (by rfl) ⟨2486087, by rfl⟩ : syracuseStep 3314783 = 4972175) B4972175
theorem B2209855 : Blo 1963435 2209855 := bstep (se 1 (by rfl) ⟨1657391, by rfl⟩ : syracuseStep 2209855 = 3314783) B3314783
theorem B2946473 : Blo 1963435 2946473 := bstep (se 2 (by rfl) ⟨1104927, by rfl⟩ : syracuseStep 2946473 = 2209855) B2209855
theorem B1964315 : Blo 1963435 1964315 := bstep (se 1 (by rfl) ⟨1473236, by rfl⟩ : syracuseStep 1964315 = 2946473) B2946473
theorem B7458277 : Blo 1963435 7458277 := bbase (se 4 (by rfl) ⟨699213, by rfl⟩ : syracuseStep 7458277 = 1398427) (by norm_num)
theorem B9944369 : Blo 1963435 9944369 := bstep (se 2 (by rfl) ⟨3729138, by rfl⟩ : syracuseStep 9944369 = 7458277) B7458277
theorem B6629579 : Blo 1963435 6629579 := bstep (se 1 (by rfl) ⟨4972184, by rfl⟩ : syracuseStep 6629579 = 9944369) B9944369
theorem B4419719 : Blo 1963435 4419719 := bstep (se 1 (by rfl) ⟨3314789, by rfl⟩ : syracuseStep 4419719 = 6629579) B6629579
theorem B2946479 : Blo 1963435 2946479 := bstep (se 1 (by rfl) ⟨2209859, by rfl⟩ : syracuseStep 2946479 = 4419719) B4419719
theorem B1964319 : Blo 1963435 1964319 := bstep (se 1 (by rfl) ⟨1473239, by rfl⟩ : syracuseStep 1964319 = 2946479) B2946479
theorem B2946485 : Blo 1963435 2946485 := bbase (se 5 (by rfl) ⟨138116, by rfl⟩ : syracuseStep 2946485 = 276233) (by norm_num)
theorem B1964323 : Blo 1963435 1964323 := bstep (se 1 (by rfl) ⟨1473242, by rfl⟩ : syracuseStep 1964323 = 2946485) B2946485
theorem B4972205 : Blo 1963435 4972205 := bbase (se 3 (by rfl) ⟨932288, by rfl⟩ : syracuseStep 4972205 = 1864577) (by norm_num)
theorem B3314803 : Blo 1963435 3314803 := bstep (se 1 (by rfl) ⟨2486102, by rfl⟩ : syracuseStep 3314803 = 4972205) B4972205
theorem B4419737 : Blo 1963435 4419737 := bstep (se 2 (by rfl) ⟨1657401, by rfl⟩ : syracuseStep 4419737 = 3314803) B3314803
theorem B2946491 : Blo 1963435 2946491 := bstep (se 1 (by rfl) ⟨2209868, by rfl⟩ : syracuseStep 2946491 = 4419737) B4419737
theorem B1964327 : Blo 1963435 1964327 := bstep (se 1 (by rfl) ⟨1473245, by rfl⟩ : syracuseStep 1964327 = 2946491) B2946491
theorem B2209873 : Blo 1963435 2209873 := bbase (se 2 (by rfl) ⟨828702, by rfl⟩ : syracuseStep 2209873 = 1657405) (by norm_num)
theorem B2946497 : Blo 1963435 2946497 := bstep (se 2 (by rfl) ⟨1104936, by rfl⟩ : syracuseStep 2946497 = 2209873) B2209873
theorem B1964331 : Blo 1963435 1964331 := bstep (se 1 (by rfl) ⟨1473248, by rfl⟩ : syracuseStep 1964331 = 2946497) B2946497
theorem B2796877 : Blo 1963435 2796877 := bbase (se 3 (by rfl) ⟨524414, by rfl⟩ : syracuseStep 2796877 = 1048829) (by norm_num)
theorem B3729169 : Blo 1963435 3729169 := bstep (se 2 (by rfl) ⟨1398438, by rfl⟩ : syracuseStep 3729169 = 2796877) B2796877
theorem B4972225 : Blo 1963435 4972225 := bstep (se 2 (by rfl) ⟨1864584, by rfl⟩ : syracuseStep 4972225 = 3729169) B3729169
theorem B6629633 : Blo 1963435 6629633 := bstep (se 2 (by rfl) ⟨2486112, by rfl⟩ : syracuseStep 6629633 = 4972225) B4972225
theorem B4419755 : Blo 1963435 4419755 := bstep (se 1 (by rfl) ⟨3314816, by rfl⟩ : syracuseStep 4419755 = 6629633) B6629633
theorem B2946503 : Blo 1963435 2946503 := bstep (se 1 (by rfl) ⟨2209877, by rfl⟩ : syracuseStep 2946503 = 4419755) B4419755
theorem B1964335 : Blo 1963435 1964335 := bstep (se 1 (by rfl) ⟨1473251, by rfl⟩ : syracuseStep 1964335 = 2946503) B2946503
theorem B2946509 : Blo 1963435 2946509 := bbase (se 3 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 2946509 = 1104941) (by norm_num)
theorem B1964339 : Blo 1963435 1964339 := bstep (se 1 (by rfl) ⟨1473254, by rfl⟩ : syracuseStep 1964339 = 2946509) B2946509
theorem B4419773 : Blo 1963435 4419773 := bbase (se 3 (by rfl) ⟨828707, by rfl⟩ : syracuseStep 4419773 = 1657415) (by norm_num)
theorem B2946515 : Blo 1963435 2946515 := bstep (se 1 (by rfl) ⟨2209886, by rfl⟩ : syracuseStep 2946515 = 4419773) B4419773
theorem B1964343 : Blo 1963435 1964343 := bstep (se 1 (by rfl) ⟨1473257, by rfl⟩ : syracuseStep 1964343 = 2946515) B2946515
theorem B3314837 : Blo 1963435 3314837 := bbase (se 6 (by rfl) ⟨77691, by rfl⟩ : syracuseStep 3314837 = 155383) (by norm_num)
theorem B2209891 : Blo 1963435 2209891 := bstep (se 1 (by rfl) ⟨1657418, by rfl⟩ : syracuseStep 2209891 = 3314837) B3314837
theorem B2946521 : Blo 1963435 2946521 := bstep (se 2 (by rfl) ⟨1104945, by rfl⟩ : syracuseStep 2946521 = 2209891) B2209891
theorem B1964347 : Blo 1963435 1964347 := bstep (se 1 (by rfl) ⟨1473260, by rfl⟩ : syracuseStep 1964347 = 2946521) B2946521
theorem B7079653 : Blo 1963435 7079653 := bbase (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) (by norm_num)
theorem B9439537 : Blo 1963435 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B12586049 : Blo 1963435 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B8390699 : Blo 1963435 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B5593799 : Blo 1963435 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B14916797 : Blo 1963435 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B9944531 : Blo 1963435 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B6629687 : Blo 1963435 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B4419791 : Blo 1963435 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B2946527 : Blo 1963435 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B1964351 : Blo 1963435 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B2946533 : Blo 1963435 2946533 := bbase (se 4 (by rfl) ⟨276237, by rfl⟩ : syracuseStep 2946533 = 552475) (by norm_num)
theorem B1964355 : Blo 1963435 1964355 := bstep (se 1 (by rfl) ⟨1473266, by rfl⟩ : syracuseStep 1964355 = 2946533) B2946533
theorem B1991161 : Blo 1963435 1991161 := bbase (se 2 (by rfl) ⟨746685, by rfl⟩ : syracuseStep 1991161 = 1493371) (by norm_num)
theorem B10619525 : Blo 1963435 10619525 := bstep (se 4 (by rfl) ⟨995580, by rfl⟩ : syracuseStep 10619525 = 1991161) B1991161
theorem B28318733 : Blo 1963435 28318733 := bstep (se 3 (by rfl) ⟨5309762, by rfl⟩ : syracuseStep 28318733 = 10619525) B10619525
theorem B18879155 : Blo 1963435 18879155 := bstep (se 1 (by rfl) ⟨14159366, by rfl⟩ : syracuseStep 18879155 = 28318733) B28318733
theorem B12586103 : Blo 1963435 12586103 := bstep (se 1 (by rfl) ⟨9439577, by rfl⟩ : syracuseStep 12586103 = 18879155) B18879155
theorem B8390735 : Blo 1963435 8390735 := bstep (se 1 (by rfl) ⟨6293051, by rfl⟩ : syracuseStep 8390735 = 12586103) B12586103
theorem B5593823 : Blo 1963435 5593823 := bstep (se 1 (by rfl) ⟨4195367, by rfl⟩ : syracuseStep 5593823 = 8390735) B8390735
theorem B3729215 : Blo 1963435 3729215 := bstep (se 1 (by rfl) ⟨2796911, by rfl⟩ : syracuseStep 3729215 = 5593823) B5593823
theorem B2486143 : Blo 1963435 2486143 := bstep (se 1 (by rfl) ⟨1864607, by rfl⟩ : syracuseStep 2486143 = 3729215) B3729215
theorem B3314857 : Blo 1963435 3314857 := bstep (se 2 (by rfl) ⟨1243071, by rfl⟩ : syracuseStep 3314857 = 2486143) B2486143
theorem B4419809 : Blo 1963435 4419809 := bstep (se 2 (by rfl) ⟨1657428, by rfl⟩ : syracuseStep 4419809 = 3314857) B3314857
theorem B2946539 : Blo 1963435 2946539 := bstep (se 1 (by rfl) ⟨2209904, by rfl⟩ : syracuseStep 2946539 = 4419809) B4419809
theorem B1964359 : Blo 1963435 1964359 := bstep (se 1 (by rfl) ⟨1473269, by rfl⟩ : syracuseStep 1964359 = 2946539) B2946539
theorem B2209909 : Blo 1963435 2209909 := bbase (se 5 (by rfl) ⟨103589, by rfl⟩ : syracuseStep 2209909 = 207179) (by norm_num)
theorem B2946545 : Blo 1963435 2946545 := bstep (se 2 (by rfl) ⟨1104954, by rfl⟩ : syracuseStep 2946545 = 2209909) B2209909
theorem B1964363 : Blo 1963435 1964363 := bstep (se 1 (by rfl) ⟨1473272, by rfl⟩ : syracuseStep 1964363 = 2946545) B2946545
theorem B2486153 : Blo 1963435 2486153 := bbase (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) (by norm_num)
theorem B6629741 : Blo 1963435 6629741 := bstep (se 3 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 6629741 = 2486153) B2486153
theorem B4419827 : Blo 1963435 4419827 := bstep (se 1 (by rfl) ⟨3314870, by rfl⟩ : syracuseStep 4419827 = 6629741) B6629741
theorem B2946551 : Blo 1963435 2946551 := bstep (se 1 (by rfl) ⟨2209913, by rfl⟩ : syracuseStep 2946551 = 4419827) B4419827
theorem B1964367 : Blo 1963435 1964367 := bstep (se 1 (by rfl) ⟨1473275, by rfl⟩ : syracuseStep 1964367 = 2946551) B2946551
theorem B2946557 : Blo 1963435 2946557 := bbase (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) (by norm_num)
theorem B1964371 : Blo 1963435 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B4419845 : Blo 1963435 4419845 := bbase (se 4 (by rfl) ⟨414360, by rfl⟩ : syracuseStep 4419845 = 828721) (by norm_num)
theorem B2946563 : Blo 1963435 2946563 := bstep (se 1 (by rfl) ⟨2209922, by rfl⟩ : syracuseStep 2946563 = 4419845) B4419845
theorem B1964375 : Blo 1963435 1964375 := bstep (se 1 (by rfl) ⟨1473281, by rfl⟩ : syracuseStep 1964375 = 2946563) B2946563
theorem B3729253 : Blo 1963435 3729253 := bbase (se 4 (by rfl) ⟨349617, by rfl⟩ : syracuseStep 3729253 = 699235) (by norm_num)
theorem B4972337 : Blo 1963435 4972337 := bstep (se 2 (by rfl) ⟨1864626, by rfl⟩ : syracuseStep 4972337 = 3729253) B3729253
theorem B3314891 : Blo 1963435 3314891 := bstep (se 1 (by rfl) ⟨2486168, by rfl⟩ : syracuseStep 3314891 = 4972337) B4972337
theorem B2209927 : Blo 1963435 2209927 := bstep (se 1 (by rfl) ⟨1657445, by rfl⟩ : syracuseStep 2209927 = 3314891) B3314891
theorem B2946569 : Blo 1963435 2946569 := bstep (se 2 (by rfl) ⟨1104963, by rfl⟩ : syracuseStep 2946569 = 2209927) B2209927
theorem B1964379 : Blo 1963435 1964379 := bstep (se 1 (by rfl) ⟨1473284, by rfl⟩ : syracuseStep 1964379 = 2946569) B2946569
theorem B9944693 : Blo 1963435 9944693 := bbase (se 5 (by rfl) ⟨466157, by rfl⟩ : syracuseStep 9944693 = 932315) (by norm_num)
theorem B6629795 : Blo 1963435 6629795 := bstep (se 1 (by rfl) ⟨4972346, by rfl⟩ : syracuseStep 6629795 = 9944693) B9944693
theorem B4419863 : Blo 1963435 4419863 := bstep (se 1 (by rfl) ⟨3314897, by rfl⟩ : syracuseStep 4419863 = 6629795) B6629795
theorem B2946575 : Blo 1963435 2946575 := bstep (se 1 (by rfl) ⟨2209931, by rfl⟩ : syracuseStep 2946575 = 4419863) B4419863
theorem B1964383 : Blo 1963435 1964383 := bstep (se 1 (by rfl) ⟨1473287, by rfl⟩ : syracuseStep 1964383 = 2946575) B2946575
theorem B2946581 : Blo 1963435 2946581 := bbase (se 6 (by rfl) ⟨69060, by rfl⟩ : syracuseStep 2946581 = 138121) (by norm_num)
theorem B1964387 : Blo 1963435 1964387 := bstep (se 1 (by rfl) ⟨1473290, by rfl⟩ : syracuseStep 1964387 = 2946581) B2946581
theorem B2240093 : Blo 1963435 2240093 := bbase (se 3 (by rfl) ⟨420017, by rfl⟩ : syracuseStep 2240093 = 840035) (by norm_num)
theorem B5973581 : Blo 1963435 5973581 := bstep (se 3 (by rfl) ⟨1120046, by rfl⟩ : syracuseStep 5973581 = 2240093) B2240093
theorem B3982387 : Blo 1963435 3982387 := bstep (se 1 (by rfl) ⟨2986790, by rfl⟩ : syracuseStep 3982387 = 5973581) B5973581
theorem B5309849 : Blo 1963435 5309849 := bstep (se 2 (by rfl) ⟨1991193, by rfl⟩ : syracuseStep 5309849 = 3982387) B3982387
theorem B3539899 : Blo 1963435 3539899 := bstep (se 1 (by rfl) ⟨2654924, by rfl⟩ : syracuseStep 3539899 = 5309849) B5309849
theorem B4719865 : Blo 1963435 4719865 := bstep (se 2 (by rfl) ⟨1769949, by rfl⟩ : syracuseStep 4719865 = 3539899) B3539899
theorem B6293153 : Blo 1963435 6293153 := bstep (se 2 (by rfl) ⟨2359932, by rfl⟩ : syracuseStep 6293153 = 4719865) B4719865
theorem B16781741 : Blo 1963435 16781741 := bstep (se 3 (by rfl) ⟨3146576, by rfl⟩ : syracuseStep 16781741 = 6293153) B6293153
theorem B11187827 : Blo 1963435 11187827 := bstep (se 1 (by rfl) ⟨8390870, by rfl⟩ : syracuseStep 11187827 = 16781741) B16781741
theorem B7458551 : Blo 1963435 7458551 := bstep (se 1 (by rfl) ⟨5593913, by rfl⟩ : syracuseStep 7458551 = 11187827) B11187827
theorem B4972367 : Blo 1963435 4972367 := bstep (se 1 (by rfl) ⟨3729275, by rfl⟩ : syracuseStep 4972367 = 7458551) B7458551
theorem B3314911 : Blo 1963435 3314911 := bstep (se 1 (by rfl) ⟨2486183, by rfl⟩ : syracuseStep 3314911 = 4972367) B4972367
theorem B4419881 : Blo 1963435 4419881 := bstep (se 2 (by rfl) ⟨1657455, by rfl⟩ : syracuseStep 4419881 = 3314911) B3314911
theorem B2946587 : Blo 1963435 2946587 := bstep (se 1 (by rfl) ⟨2209940, by rfl⟩ : syracuseStep 2946587 = 4419881) B4419881
theorem B1964391 : Blo 1963435 1964391 := bstep (se 1 (by rfl) ⟨1473293, by rfl⟩ : syracuseStep 1964391 = 2946587) B2946587
theorem B2209945 : Blo 1963435 2209945 := bbase (se 2 (by rfl) ⟨828729, by rfl⟩ : syracuseStep 2209945 = 1657459) (by norm_num)
theorem B2946593 : Blo 1963435 2946593 := bstep (se 2 (by rfl) ⟨1104972, by rfl⟩ : syracuseStep 2946593 = 2209945) B2209945
theorem B1964395 : Blo 1963435 1964395 := bstep (se 1 (by rfl) ⟨1473296, by rfl⟩ : syracuseStep 1964395 = 2946593) B2946593
theorem B7458581 : Blo 1963435 7458581 := bbase (se 6 (by rfl) ⟨174810, by rfl⟩ : syracuseStep 7458581 = 349621) (by norm_num)
theorem B4972387 : Blo 1963435 4972387 := bstep (se 1 (by rfl) ⟨3729290, by rfl⟩ : syracuseStep 4972387 = 7458581) B7458581
theorem B6629849 : Blo 1963435 6629849 := bstep (se 2 (by rfl) ⟨2486193, by rfl⟩ : syracuseStep 6629849 = 4972387) B4972387
theorem B4419899 : Blo 1963435 4419899 := bstep (se 1 (by rfl) ⟨3314924, by rfl⟩ : syracuseStep 4419899 = 6629849) B6629849
theorem B2946599 : Blo 1963435 2946599 := bstep (se 1 (by rfl) ⟨2209949, by rfl⟩ : syracuseStep 2946599 = 4419899) B4419899
theorem B1964399 : Blo 1963435 1964399 := bstep (se 1 (by rfl) ⟨1473299, by rfl⟩ : syracuseStep 1964399 = 2946599) B2946599
theorem B2946605 : Blo 1963435 2946605 := bbase (se 3 (by rfl) ⟨552488, by rfl⟩ : syracuseStep 2946605 = 1104977) (by norm_num)
theorem B1964403 : Blo 1963435 1964403 := bstep (se 1 (by rfl) ⟨1473302, by rfl⟩ : syracuseStep 1964403 = 2946605) B2946605
theorem B4419917 : Blo 1963435 4419917 := bbase (se 3 (by rfl) ⟨828734, by rfl⟩ : syracuseStep 4419917 = 1657469) (by norm_num)
theorem B2946611 : Blo 1963435 2946611 := bstep (se 1 (by rfl) ⟨2209958, by rfl⟩ : syracuseStep 2946611 = 4419917) B4419917
theorem B1964407 : Blo 1963435 1964407 := bstep (se 1 (by rfl) ⟨1473305, by rfl⟩ : syracuseStep 1964407 = 2946611) B2946611
theorem B2486209 : Blo 1963435 2486209 := bbase (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) (by norm_num)
theorem B3314945 : Blo 1963435 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B2209963 : Blo 1963435 2209963 := bstep (se 1 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 2209963 = 3314945) B3314945
theorem B2946617 : Blo 1963435 2946617 := bstep (se 2 (by rfl) ⟨1104981, by rfl⟩ : syracuseStep 2946617 = 2209963) B2209963
theorem B1964411 : Blo 1963435 1964411 := bstep (se 1 (by rfl) ⟨1473308, by rfl⟩ : syracuseStep 1964411 = 2946617) B2946617
theorem B2654957 : Blo 1963435 2654957 := bbase (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) (by norm_num)
theorem B7079885 : Blo 1963435 7079885 := bstep (se 3 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 7079885 = 2654957) B2654957
theorem B4719923 : Blo 1963435 4719923 := bstep (se 1 (by rfl) ⟨3539942, by rfl⟩ : syracuseStep 4719923 = 7079885) B7079885
theorem B3146615 : Blo 1963435 3146615 := bstep (se 1 (by rfl) ⟨2359961, by rfl⟩ : syracuseStep 3146615 = 4719923) B4719923
theorem B2097743 : Blo 1963435 2097743 := bstep (se 1 (by rfl) ⟨1573307, by rfl⟩ : syracuseStep 2097743 = 3146615) B3146615
theorem B22375925 : Blo 1963435 22375925 := bstep (se 5 (by rfl) ⟨1048871, by rfl⟩ : syracuseStep 22375925 = 2097743) B2097743
theorem B14917283 : Blo 1963435 14917283 := bstep (se 1 (by rfl) ⟨11187962, by rfl⟩ : syracuseStep 14917283 = 22375925) B22375925
theorem B9944855 : Blo 1963435 9944855 := bstep (se 1 (by rfl) ⟨7458641, by rfl⟩ : syracuseStep 9944855 = 14917283) B14917283
theorem B6629903 : Blo 1963435 6629903 := bstep (se 1 (by rfl) ⟨4972427, by rfl⟩ : syracuseStep 6629903 = 9944855) B9944855
theorem B4419935 : Blo 1963435 4419935 := bstep (se 1 (by rfl) ⟨3314951, by rfl⟩ : syracuseStep 4419935 = 6629903) B6629903
theorem B2946623 : Blo 1963435 2946623 := bstep (se 1 (by rfl) ⟨2209967, by rfl⟩ : syracuseStep 2946623 = 4419935) B4419935
theorem B1964415 : Blo 1963435 1964415 := bstep (se 1 (by rfl) ⟨1473311, by rfl⟩ : syracuseStep 1964415 = 2946623) B2946623
theorem B2946629 : Blo 1963435 2946629 := bbase (se 4 (by rfl) ⟨276246, by rfl⟩ : syracuseStep 2946629 = 552493) (by norm_num)
theorem B1964419 : Blo 1963435 1964419 := bstep (se 1 (by rfl) ⟨1473314, by rfl⟩ : syracuseStep 1964419 = 2946629) B2946629
theorem B3314965 : Blo 1963435 3314965 := bbase (se 6 (by rfl) ⟨77694, by rfl⟩ : syracuseStep 3314965 = 155389) (by norm_num)
theorem B4419953 : Blo 1963435 4419953 := bstep (se 2 (by rfl) ⟨1657482, by rfl⟩ : syracuseStep 4419953 = 3314965) B3314965
theorem B2946635 : Blo 1963435 2946635 := bstep (se 1 (by rfl) ⟨2209976, by rfl⟩ : syracuseStep 2946635 = 4419953) B4419953
theorem B1964423 : Blo 1963435 1964423 := bstep (se 1 (by rfl) ⟨1473317, by rfl⟩ : syracuseStep 1964423 = 2946635) B2946635
theorem B2209981 : Blo 1963435 2209981 := bbase (se 3 (by rfl) ⟨414371, by rfl⟩ : syracuseStep 2209981 = 828743) (by norm_num)
theorem B2946641 : Blo 1963435 2946641 := bstep (se 2 (by rfl) ⟨1104990, by rfl⟩ : syracuseStep 2946641 = 2209981) B2209981
theorem B1964427 : Blo 1963435 1964427 := bstep (se 1 (by rfl) ⟨1473320, by rfl⟩ : syracuseStep 1964427 = 2946641) B2946641
theorem B6629957 : Blo 1963435 6629957 := bbase (se 4 (by rfl) ⟨621558, by rfl⟩ : syracuseStep 6629957 = 1243117) (by norm_num)
theorem B4419971 : Blo 1963435 4419971 := bstep (se 1 (by rfl) ⟨3314978, by rfl⟩ : syracuseStep 4419971 = 6629957) B6629957
theorem B2946647 : Blo 1963435 2946647 := bstep (se 1 (by rfl) ⟨2209985, by rfl⟩ : syracuseStep 2946647 = 4419971) B4419971
theorem B1964431 : Blo 1963435 1964431 := bstep (se 1 (by rfl) ⟨1473323, by rfl⟩ : syracuseStep 1964431 = 2946647) B2946647
theorem B2946653 : Blo 1963435 2946653 := bbase (se 3 (by rfl) ⟨552497, by rfl⟩ : syracuseStep 2946653 = 1104995) (by norm_num)
theorem B1964435 : Blo 1963435 1964435 := bstep (se 1 (by rfl) ⟨1473326, by rfl⟩ : syracuseStep 1964435 = 2946653) B2946653
theorem B4419989 : Blo 1963435 4419989 := bbase (se 6 (by rfl) ⟨103593, by rfl⟩ : syracuseStep 4419989 = 207187) (by norm_num)
theorem B2946659 : Blo 1963435 2946659 := bstep (se 1 (by rfl) ⟨2209994, by rfl⟩ : syracuseStep 2946659 = 4419989) B4419989
theorem B1964439 : Blo 1963435 1964439 := bstep (se 1 (by rfl) ⟨1473329, by rfl⟩ : syracuseStep 1964439 = 2946659) B2946659
theorem B3982493 : Blo 1963435 3982493 := bbase (se 3 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 3982493 = 1493435) (by norm_num)
theorem B10619981 : Blo 1963435 10619981 := bstep (se 3 (by rfl) ⟨1991246, by rfl⟩ : syracuseStep 10619981 = 3982493) B3982493
theorem B7079987 : Blo 1963435 7079987 := bstep (se 1 (by rfl) ⟨5309990, by rfl⟩ : syracuseStep 7079987 = 10619981) B10619981
theorem B4719991 : Blo 1963435 4719991 := bstep (se 1 (by rfl) ⟨3539993, by rfl⟩ : syracuseStep 4719991 = 7079987) B7079987
theorem B6293321 : Blo 1963435 6293321 := bstep (se 2 (by rfl) ⟨2359995, by rfl⟩ : syracuseStep 6293321 = 4719991) B4719991
theorem B4195547 : Blo 1963435 4195547 := bstep (se 1 (by rfl) ⟨3146660, by rfl⟩ : syracuseStep 4195547 = 6293321) B6293321
theorem B2797031 : Blo 1963435 2797031 := bstep (se 1 (by rfl) ⟨2097773, by rfl⟩ : syracuseStep 2797031 = 4195547) B4195547
theorem B7458749 : Blo 1963435 7458749 := bstep (se 3 (by rfl) ⟨1398515, by rfl⟩ : syracuseStep 7458749 = 2797031) B2797031
theorem B4972499 : Blo 1963435 4972499 := bstep (se 1 (by rfl) ⟨3729374, by rfl⟩ : syracuseStep 4972499 = 7458749) B7458749
theorem B3314999 : Blo 1963435 3314999 := bstep (se 1 (by rfl) ⟨2486249, by rfl⟩ : syracuseStep 3314999 = 4972499) B4972499
theorem B2209999 : Blo 1963435 2209999 := bstep (se 1 (by rfl) ⟨1657499, by rfl⟩ : syracuseStep 2209999 = 3314999) B3314999
theorem B2946665 : Blo 1963435 2946665 := bstep (se 2 (by rfl) ⟨1104999, by rfl⟩ : syracuseStep 2946665 = 2209999) B2209999
theorem B1964443 : Blo 1963435 1964443 := bstep (se 1 (by rfl) ⟨1473332, by rfl⟩ : syracuseStep 1964443 = 2946665) B2946665
theorem B8391109 : Blo 1963435 8391109 := bbase (se 4 (by rfl) ⟨786666, by rfl⟩ : syracuseStep 8391109 = 1573333) (by norm_num)
theorem B11188145 : Blo 1963435 11188145 := bstep (se 2 (by rfl) ⟨4195554, by rfl⟩ : syracuseStep 11188145 = 8391109) B8391109
theorem B7458763 : Blo 1963435 7458763 := bstep (se 1 (by rfl) ⟨5594072, by rfl⟩ : syracuseStep 7458763 = 11188145) B11188145
theorem B9945017 : Blo 1963435 9945017 := bstep (se 2 (by rfl) ⟨3729381, by rfl⟩ : syracuseStep 9945017 = 7458763) B7458763
theorem B6630011 : Blo 1963435 6630011 := bstep (se 1 (by rfl) ⟨4972508, by rfl⟩ : syracuseStep 6630011 = 9945017) B9945017
theorem B4420007 : Blo 1963435 4420007 := bstep (se 1 (by rfl) ⟨3315005, by rfl⟩ : syracuseStep 4420007 = 6630011) B6630011
theorem B2946671 : Blo 1963435 2946671 := bstep (se 1 (by rfl) ⟨2210003, by rfl⟩ : syracuseStep 2946671 = 4420007) B4420007
theorem B1964447 : Blo 1963435 1964447 := bstep (se 1 (by rfl) ⟨1473335, by rfl⟩ : syracuseStep 1964447 = 2946671) B2946671
theorem B2946677 : Blo 1963435 2946677 := bbase (se 5 (by rfl) ⟨138125, by rfl⟩ : syracuseStep 2946677 = 276251) (by norm_num)
theorem B1964451 : Blo 1963435 1964451 := bstep (se 1 (by rfl) ⟨1473338, by rfl⟩ : syracuseStep 1964451 = 2946677) B2946677
theorem B3729397 : Blo 1963435 3729397 := bbase (se 5 (by rfl) ⟨174815, by rfl⟩ : syracuseStep 3729397 = 349631) (by norm_num)
theorem B4972529 : Blo 1963435 4972529 := bstep (se 2 (by rfl) ⟨1864698, by rfl⟩ : syracuseStep 4972529 = 3729397) B3729397
theorem B3315019 : Blo 1963435 3315019 := bstep (se 1 (by rfl) ⟨2486264, by rfl⟩ : syracuseStep 3315019 = 4972529) B4972529
theorem B4420025 : Blo 1963435 4420025 := bstep (se 2 (by rfl) ⟨1657509, by rfl⟩ : syracuseStep 4420025 = 3315019) B3315019
theorem B2946683 : Blo 1963435 2946683 := bstep (se 1 (by rfl) ⟨2210012, by rfl⟩ : syracuseStep 2946683 = 4420025) B4420025
theorem B1964455 : Blo 1963435 1964455 := bstep (se 1 (by rfl) ⟨1473341, by rfl⟩ : syracuseStep 1964455 = 2946683) B2946683
theorem B2210017 : Blo 1963435 2210017 := bbase (se 2 (by rfl) ⟨828756, by rfl⟩ : syracuseStep 2210017 = 1657513) (by norm_num)
theorem B2946689 : Blo 1963435 2946689 := bstep (se 2 (by rfl) ⟨1105008, by rfl⟩ : syracuseStep 2946689 = 2210017) B2210017
theorem B1964459 : Blo 1963435 1964459 := bstep (se 1 (by rfl) ⟨1473344, by rfl⟩ : syracuseStep 1964459 = 2946689) B2946689
theorem B4972549 : Blo 1963435 4972549 := bbase (se 4 (by rfl) ⟨466176, by rfl⟩ : syracuseStep 4972549 = 932353) (by norm_num)
theorem B6630065 : Blo 1963435 6630065 := bstep (se 2 (by rfl) ⟨2486274, by rfl⟩ : syracuseStep 6630065 = 4972549) B4972549
theorem B4420043 : Blo 1963435 4420043 := bstep (se 1 (by rfl) ⟨3315032, by rfl⟩ : syracuseStep 4420043 = 6630065) B6630065
theorem B2946695 : Blo 1963435 2946695 := bstep (se 1 (by rfl) ⟨2210021, by rfl⟩ : syracuseStep 2946695 = 4420043) B4420043
theorem B1964463 : Blo 1963435 1964463 := bstep (se 1 (by rfl) ⟨1473347, by rfl⟩ : syracuseStep 1964463 = 2946695) B2946695
theorem B2946701 : Blo 1963435 2946701 := bbase (se 3 (by rfl) ⟨552506, by rfl⟩ : syracuseStep 2946701 = 1105013) (by norm_num)
theorem B1964467 : Blo 1963435 1964467 := bstep (se 1 (by rfl) ⟨1473350, by rfl⟩ : syracuseStep 1964467 = 2946701) B2946701
theorem B4420061 : Blo 1963435 4420061 := bbase (se 3 (by rfl) ⟨828761, by rfl⟩ : syracuseStep 4420061 = 1657523) (by norm_num)
theorem B2946707 : Blo 1963435 2946707 := bstep (se 1 (by rfl) ⟨2210030, by rfl⟩ : syracuseStep 2946707 = 4420061) B4420061
theorem B1964471 : Blo 1963435 1964471 := bstep (se 1 (by rfl) ⟨1473353, by rfl⟩ : syracuseStep 1964471 = 2946707) B2946707
theorem B3315053 : Blo 1963435 3315053 := bbase (se 3 (by rfl) ⟨621572, by rfl⟩ : syracuseStep 3315053 = 1243145) (by norm_num)
theorem B2210035 : Blo 1963435 2210035 := bstep (se 1 (by rfl) ⟨1657526, by rfl⟩ : syracuseStep 2210035 = 3315053) B3315053
theorem B2946713 : Blo 1963435 2946713 := bstep (se 2 (by rfl) ⟨1105017, by rfl⟩ : syracuseStep 2946713 = 2210035) B2210035
theorem B1964475 : Blo 1963435 1964475 := bstep (se 1 (by rfl) ⟨1473356, by rfl⟩ : syracuseStep 1964475 = 2946713) B2946713
theorem B3780325 : Blo 1963435 3780325 := bbase (se 4 (by rfl) ⟨354405, by rfl⟩ : syracuseStep 3780325 = 708811) (by norm_num)
theorem B5040433 : Blo 1963435 5040433 := bstep (se 2 (by rfl) ⟨1890162, by rfl⟩ : syracuseStep 5040433 = 3780325) B3780325
theorem B6720577 : Blo 1963435 6720577 := bstep (se 2 (by rfl) ⟨2520216, by rfl⟩ : syracuseStep 6720577 = 5040433) B5040433
theorem B35843077 : Blo 1963435 35843077 := bstep (se 4 (by rfl) ⟨3360288, by rfl⟩ : syracuseStep 35843077 = 6720577) B6720577
theorem B47790769 : Blo 1963435 47790769 := bstep (se 2 (by rfl) ⟨17921538, by rfl⟩ : syracuseStep 47790769 = 35843077) B35843077
theorem B63721025 : Blo 1963435 63721025 := bstep (se 2 (by rfl) ⟨23895384, by rfl⟩ : syracuseStep 63721025 = 47790769) B47790769
theorem B42480683 : Blo 1963435 42480683 := bstep (se 1 (by rfl) ⟨31860512, by rfl⟩ : syracuseStep 42480683 = 63721025) B63721025
theorem B28320455 : Blo 1963435 28320455 := bstep (se 1 (by rfl) ⟨21240341, by rfl⟩ : syracuseStep 28320455 = 42480683) B42480683
theorem B18880303 : Blo 1963435 18880303 := bstep (se 1 (by rfl) ⟨14160227, by rfl⟩ : syracuseStep 18880303 = 28320455) B28320455
theorem B25173737 : Blo 1963435 25173737 := bstep (se 2 (by rfl) ⟨9440151, by rfl⟩ : syracuseStep 25173737 = 18880303) B18880303
theorem B16782491 : Blo 1963435 16782491 := bstep (se 1 (by rfl) ⟨12586868, by rfl⟩ : syracuseStep 16782491 = 25173737) B25173737
theorem B11188327 : Blo 1963435 11188327 := bstep (se 1 (by rfl) ⟨8391245, by rfl⟩ : syracuseStep 11188327 = 16782491) B16782491
theorem B14917769 : Blo 1963435 14917769 := bstep (se 2 (by rfl) ⟨5594163, by rfl⟩ : syracuseStep 14917769 = 11188327) B11188327
theorem B9945179 : Blo 1963435 9945179 := bstep (se 1 (by rfl) ⟨7458884, by rfl⟩ : syracuseStep 9945179 = 14917769) B14917769
theorem B6630119 : Blo 1963435 6630119 := bstep (se 1 (by rfl) ⟨4972589, by rfl⟩ : syracuseStep 6630119 = 9945179) B9945179
theorem B4420079 : Blo 1963435 4420079 := bstep (se 1 (by rfl) ⟨3315059, by rfl⟩ : syracuseStep 4420079 = 6630119) B6630119
theorem B2946719 : Blo 1963435 2946719 := bstep (se 1 (by rfl) ⟨2210039, by rfl⟩ : syracuseStep 2946719 = 4420079) B4420079
theorem B1964479 : Blo 1963435 1964479 := bstep (se 1 (by rfl) ⟨1473359, by rfl⟩ : syracuseStep 1964479 = 2946719) B2946719
theorem B2946725 : Blo 1963435 2946725 := bbase (se 4 (by rfl) ⟨276255, by rfl⟩ : syracuseStep 2946725 = 552511) (by norm_num)
theorem B1964483 : Blo 1963435 1964483 := bstep (se 1 (by rfl) ⟨1473362, by rfl⟩ : syracuseStep 1964483 = 2946725) B2946725
theorem B2486305 : Blo 1963435 2486305 := bbase (se 2 (by rfl) ⟨932364, by rfl⟩ : syracuseStep 2486305 = 1864729) (by norm_num)
theorem B3315073 : Blo 1963435 3315073 := bstep (se 2 (by rfl) ⟨1243152, by rfl⟩ : syracuseStep 3315073 = 2486305) B2486305
theorem B4420097 : Blo 1963435 4420097 := bstep (se 2 (by rfl) ⟨1657536, by rfl⟩ : syracuseStep 4420097 = 3315073) B3315073
theorem B2946731 : Blo 1963435 2946731 := bstep (se 1 (by rfl) ⟨2210048, by rfl⟩ : syracuseStep 2946731 = 4420097) B4420097
theorem B1964487 : Blo 1963435 1964487 := bstep (se 1 (by rfl) ⟨1473365, by rfl⟩ : syracuseStep 1964487 = 2946731) B2946731
theorem B2210053 : Blo 1963435 2210053 := bbase (se 4 (by rfl) ⟨207192, by rfl⟩ : syracuseStep 2210053 = 414385) (by norm_num)
theorem B2946737 : Blo 1963435 2946737 := bstep (se 2 (by rfl) ⟨1105026, by rfl⟩ : syracuseStep 2946737 = 2210053) B2210053
theorem B1964491 : Blo 1963435 1964491 := bstep (se 1 (by rfl) ⟨1473368, by rfl⟩ : syracuseStep 1964491 = 2946737) B2946737
theorem B2097829 : Blo 1963435 2097829 := bbase (se 4 (by rfl) ⟨196671, by rfl⟩ : syracuseStep 2097829 = 393343) (by norm_num)
theorem B2797105 : Blo 1963435 2797105 := bstep (se 2 (by rfl) ⟨1048914, by rfl⟩ : syracuseStep 2797105 = 2097829) B2097829
theorem B3729473 : Blo 1963435 3729473 := bstep (se 2 (by rfl) ⟨1398552, by rfl⟩ : syracuseStep 3729473 = 2797105) B2797105
theorem B2486315 : Blo 1963435 2486315 := bstep (se 1 (by rfl) ⟨1864736, by rfl⟩ : syracuseStep 2486315 = 3729473) B3729473
theorem B6630173 : Blo 1963435 6630173 := bstep (se 3 (by rfl) ⟨1243157, by rfl⟩ : syracuseStep 6630173 = 2486315) B2486315
theorem B4420115 : Blo 1963435 4420115 := bstep (se 1 (by rfl) ⟨3315086, by rfl⟩ : syracuseStep 4420115 = 6630173) B6630173
theorem B2946743 : Blo 1963435 2946743 := bstep (se 1 (by rfl) ⟨2210057, by rfl⟩ : syracuseStep 2946743 = 4420115) B4420115
theorem B1964495 : Blo 1963435 1964495 := bstep (se 1 (by rfl) ⟨1473371, by rfl⟩ : syracuseStep 1964495 = 2946743) B2946743
theorem B2946749 : Blo 1963435 2946749 := bbase (se 3 (by rfl) ⟨552515, by rfl⟩ : syracuseStep 2946749 = 1105031) (by norm_num)
theorem B1964499 : Blo 1963435 1964499 := bstep (se 1 (by rfl) ⟨1473374, by rfl⟩ : syracuseStep 1964499 = 2946749) B2946749
theorem B4420133 : Blo 1963435 4420133 := bbase (se 4 (by rfl) ⟨414387, by rfl⟩ : syracuseStep 4420133 = 828775) (by norm_num)
theorem B2946755 : Blo 1963435 2946755 := bstep (se 1 (by rfl) ⟨2210066, by rfl⟩ : syracuseStep 2946755 = 4420133) B4420133
theorem B1964503 : Blo 1963435 1964503 := bstep (se 1 (by rfl) ⟨1473377, by rfl⟩ : syracuseStep 1964503 = 2946755) B2946755
theorem B4972661 : Blo 1963435 4972661 := bbase (se 5 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 4972661 = 466187) (by norm_num)
theorem B3315107 : Blo 1963435 3315107 := bstep (se 1 (by rfl) ⟨2486330, by rfl⟩ : syracuseStep 3315107 = 4972661) B4972661
theorem B2210071 : Blo 1963435 2210071 := bstep (se 1 (by rfl) ⟨1657553, by rfl⟩ : syracuseStep 2210071 = 3315107) B3315107
theorem B2946761 : Blo 1963435 2946761 := bstep (se 2 (by rfl) ⟨1105035, by rfl⟩ : syracuseStep 2946761 = 2210071) B2210071
theorem B1964507 : Blo 1963435 1964507 := bstep (se 1 (by rfl) ⟨1473380, by rfl⟩ : syracuseStep 1964507 = 2946761) B2946761
theorem B2986973 : Blo 1963435 2986973 := bbase (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) (by norm_num)
theorem B1991315 : Blo 1963435 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B5310173 : Blo 1963435 5310173 := bstep (se 3 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 5310173 = 1991315) B1991315
theorem B3540115 : Blo 1963435 3540115 := bstep (se 1 (by rfl) ⟨2655086, by rfl⟩ : syracuseStep 3540115 = 5310173) B5310173
theorem B18880613 : Blo 1963435 18880613 := bstep (se 4 (by rfl) ⟨1770057, by rfl⟩ : syracuseStep 18880613 = 3540115) B3540115
theorem B12587075 : Blo 1963435 12587075 := bstep (se 1 (by rfl) ⟨9440306, by rfl⟩ : syracuseStep 12587075 = 18880613) B18880613
theorem B8391383 : Blo 1963435 8391383 := bstep (se 1 (by rfl) ⟨6293537, by rfl⟩ : syracuseStep 8391383 = 12587075) B12587075
theorem B5594255 : Blo 1963435 5594255 := bstep (se 1 (by rfl) ⟨4195691, by rfl⟩ : syracuseStep 5594255 = 8391383) B8391383
theorem B3729503 : Blo 1963435 3729503 := bstep (se 1 (by rfl) ⟨2797127, by rfl⟩ : syracuseStep 3729503 = 5594255) B5594255
theorem B9945341 : Blo 1963435 9945341 := bstep (se 3 (by rfl) ⟨1864751, by rfl⟩ : syracuseStep 9945341 = 3729503) B3729503
theorem B6630227 : Blo 1963435 6630227 := bstep (se 1 (by rfl) ⟨4972670, by rfl⟩ : syracuseStep 6630227 = 9945341) B9945341
theorem B4420151 : Blo 1963435 4420151 := bstep (se 1 (by rfl) ⟨3315113, by rfl⟩ : syracuseStep 4420151 = 6630227) B6630227
theorem B2946767 : Blo 1963435 2946767 := bstep (se 1 (by rfl) ⟨2210075, by rfl⟩ : syracuseStep 2946767 = 4420151) B4420151
theorem B1964511 : Blo 1963435 1964511 := bstep (se 1 (by rfl) ⟨1473383, by rfl⟩ : syracuseStep 1964511 = 2946767) B2946767
theorem B2946773 : Blo 1963435 2946773 := bbase (se 7 (by rfl) ⟨34532, by rfl⟩ : syracuseStep 2946773 = 69065) (by norm_num)
theorem B1964515 : Blo 1963435 1964515 := bstep (se 1 (by rfl) ⟨1473386, by rfl⟩ : syracuseStep 1964515 = 2946773) B2946773
theorem B4195709 : Blo 1963435 4195709 := bbase (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) (by norm_num)
theorem B2797139 : Blo 1963435 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B7459037 : Blo 1963435 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B4972691 : Blo 1963435 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B3315127 : Blo 1963435 3315127 := bstep (se 1 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 3315127 = 4972691) B4972691
theorem B4420169 : Blo 1963435 4420169 := bstep (se 2 (by rfl) ⟨1657563, by rfl⟩ : syracuseStep 4420169 = 3315127) B3315127
theorem B2946779 : Blo 1963435 2946779 := bstep (se 1 (by rfl) ⟨2210084, by rfl⟩ : syracuseStep 2946779 = 4420169) B4420169
theorem B1964519 : Blo 1963435 1964519 := bstep (se 1 (by rfl) ⟨1473389, by rfl⟩ : syracuseStep 1964519 = 2946779) B2946779
theorem B2210089 : Blo 1963435 2210089 := bbase (se 2 (by rfl) ⟨828783, by rfl⟩ : syracuseStep 2210089 = 1657567) (by norm_num)
theorem B2946785 : Blo 1963435 2946785 := bstep (se 2 (by rfl) ⟨1105044, by rfl⟩ : syracuseStep 2946785 = 2210089) B2210089
theorem B1964523 : Blo 1963435 1964523 := bstep (se 1 (by rfl) ⟨1473392, by rfl⟩ : syracuseStep 1964523 = 2946785) B2946785
theorem B6812437 : Blo 1963435 6812437 := bbase (se 6 (by rfl) ⟨159666, by rfl⟩ : syracuseStep 6812437 = 319333) (by norm_num)
theorem B9083249 : Blo 1963435 9083249 := bstep (se 2 (by rfl) ⟨3406218, by rfl⟩ : syracuseStep 9083249 = 6812437) B6812437
theorem B6055499 : Blo 1963435 6055499 := bstep (se 1 (by rfl) ⟨4541624, by rfl⟩ : syracuseStep 6055499 = 9083249) B9083249
theorem B16147997 : Blo 1963435 16147997 := bstep (se 3 (by rfl) ⟨3027749, by rfl⟩ : syracuseStep 16147997 = 6055499) B6055499
theorem B10765331 : Blo 1963435 10765331 := bstep (se 1 (by rfl) ⟨8073998, by rfl⟩ : syracuseStep 10765331 = 16147997) B16147997
theorem B7176887 : Blo 1963435 7176887 := bstep (se 1 (by rfl) ⟨5382665, by rfl⟩ : syracuseStep 7176887 = 10765331) B10765331
theorem B4784591 : Blo 1963435 4784591 := bstep (se 1 (by rfl) ⟨3588443, by rfl⟩ : syracuseStep 4784591 = 7176887) B7176887
theorem B12758909 : Blo 1963435 12758909 := bstep (se 3 (by rfl) ⟨2392295, by rfl⟩ : syracuseStep 12758909 = 4784591) B4784591
theorem B136095029 : Blo 1963435 136095029 := bstep (se 5 (by rfl) ⟨6379454, by rfl⟩ : syracuseStep 136095029 = 12758909) B12758909
theorem B90730019 : Blo 1963435 90730019 := bstep (se 1 (by rfl) ⟨68047514, by rfl⟩ : syracuseStep 90730019 = 136095029) B136095029
theorem B60486679 : Blo 1963435 60486679 := bstep (se 1 (by rfl) ⟨45365009, by rfl⟩ : syracuseStep 60486679 = 90730019) B90730019
theorem B80648905 : Blo 1963435 80648905 := bstep (se 2 (by rfl) ⟨30243339, by rfl⟩ : syracuseStep 80648905 = 60486679) B60486679
theorem B107531873 : Blo 1963435 107531873 := bstep (se 2 (by rfl) ⟨40324452, by rfl⟩ : syracuseStep 107531873 = 80648905) B80648905
theorem B71687915 : Blo 1963435 71687915 := bstep (se 1 (by rfl) ⟨53765936, by rfl⟩ : syracuseStep 71687915 = 107531873) B107531873
theorem B47791943 : Blo 1963435 47791943 := bstep (se 1 (by rfl) ⟨35843957, by rfl⟩ : syracuseStep 47791943 = 71687915) B71687915
theorem B31861295 : Blo 1963435 31861295 := bstep (se 1 (by rfl) ⟨23895971, by rfl⟩ : syracuseStep 31861295 = 47791943) B47791943
theorem B21240863 : Blo 1963435 21240863 := bstep (se 1 (by rfl) ⟨15930647, by rfl⟩ : syracuseStep 21240863 = 31861295) B31861295
theorem B14160575 : Blo 1963435 14160575 := bstep (se 1 (by rfl) ⟨10620431, by rfl⟩ : syracuseStep 14160575 = 21240863) B21240863
theorem B9440383 : Blo 1963435 9440383 := bstep (se 1 (by rfl) ⟨7080287, by rfl⟩ : syracuseStep 9440383 = 14160575) B14160575
theorem B12587177 : Blo 1963435 12587177 := bstep (se 2 (by rfl) ⟨4720191, by rfl⟩ : syracuseStep 12587177 = 9440383) B9440383
theorem B8391451 : Blo 1963435 8391451 := bstep (se 1 (by rfl) ⟨6293588, by rfl⟩ : syracuseStep 8391451 = 12587177) B12587177
theorem B11188601 : Blo 1963435 11188601 := bstep (se 2 (by rfl) ⟨4195725, by rfl⟩ : syracuseStep 11188601 = 8391451) B8391451
theorem B7459067 : Blo 1963435 7459067 := bstep (se 1 (by rfl) ⟨5594300, by rfl⟩ : syracuseStep 7459067 = 11188601) B11188601
theorem B4972711 : Blo 1963435 4972711 := bstep (se 1 (by rfl) ⟨3729533, by rfl⟩ : syracuseStep 4972711 = 7459067) B7459067
theorem B6630281 : Blo 1963435 6630281 := bstep (se 2 (by rfl) ⟨2486355, by rfl⟩ : syracuseStep 6630281 = 4972711) B4972711
theorem B4420187 : Blo 1963435 4420187 := bstep (se 1 (by rfl) ⟨3315140, by rfl⟩ : syracuseStep 4420187 = 6630281) B6630281
theorem B2946791 : Blo 1963435 2946791 := bstep (se 1 (by rfl) ⟨2210093, by rfl⟩ : syracuseStep 2946791 = 4420187) B4420187
theorem B1964527 : Blo 1963435 1964527 := bstep (se 1 (by rfl) ⟨1473395, by rfl⟩ : syracuseStep 1964527 = 2946791) B2946791
theorem B2946797 : Blo 1963435 2946797 := bbase (se 3 (by rfl) ⟨552524, by rfl⟩ : syracuseStep 2946797 = 1105049) (by norm_num)
theorem B1964531 : Blo 1963435 1964531 := bstep (se 1 (by rfl) ⟨1473398, by rfl⟩ : syracuseStep 1964531 = 2946797) B2946797
theorem B4420205 : Blo 1963435 4420205 := bbase (se 3 (by rfl) ⟨828788, by rfl⟩ : syracuseStep 4420205 = 1657577) (by norm_num)
theorem B2946803 : Blo 1963435 2946803 := bstep (se 1 (by rfl) ⟨2210102, by rfl⟩ : syracuseStep 2946803 = 4420205) B4420205
theorem B1964535 : Blo 1963435 1964535 := bstep (se 1 (by rfl) ⟨1473401, by rfl⟩ : syracuseStep 1964535 = 2946803) B2946803
theorem B3729557 : Blo 1963435 3729557 := bbase (se 6 (by rfl) ⟨87411, by rfl⟩ : syracuseStep 3729557 = 174823) (by norm_num)
theorem B2486371 : Blo 1963435 2486371 := bstep (se 1 (by rfl) ⟨1864778, by rfl⟩ : syracuseStep 2486371 = 3729557) B3729557
theorem B3315161 : Blo 1963435 3315161 := bstep (se 2 (by rfl) ⟨1243185, by rfl⟩ : syracuseStep 3315161 = 2486371) B2486371
theorem B2210107 : Blo 1963435 2210107 := bstep (se 1 (by rfl) ⟨1657580, by rfl⟩ : syracuseStep 2210107 = 3315161) B3315161
theorem B2946809 : Blo 1963435 2946809 := bstep (se 2 (by rfl) ⟨1105053, by rfl⟩ : syracuseStep 2946809 = 2210107) B2210107
theorem B1964539 : Blo 1963435 1964539 := bstep (se 1 (by rfl) ⟨1473404, by rfl⟩ : syracuseStep 1964539 = 2946809) B2946809
theorem B8961061 : Blo 1963435 8961061 := bbase (se 4 (by rfl) ⟨840099, by rfl⟩ : syracuseStep 8961061 = 1680199) (by norm_num)
theorem B11948081 : Blo 1963435 11948081 := bstep (se 2 (by rfl) ⟨4480530, by rfl⟩ : syracuseStep 11948081 = 8961061) B8961061
theorem B31861549 : Blo 1963435 31861549 := bstep (se 3 (by rfl) ⟨5974040, by rfl⟩ : syracuseStep 31861549 = 11948081) B11948081
theorem B42482065 : Blo 1963435 42482065 := bstep (se 2 (by rfl) ⟨15930774, by rfl⟩ : syracuseStep 42482065 = 31861549) B31861549
theorem B56642753 : Blo 1963435 56642753 := bstep (se 2 (by rfl) ⟨21241032, by rfl⟩ : syracuseStep 56642753 = 42482065) B42482065
theorem B37761835 : Blo 1963435 37761835 := bstep (se 1 (by rfl) ⟨28321376, by rfl⟩ : syracuseStep 37761835 = 56642753) B56642753
theorem B50349113 : Blo 1963435 50349113 := bstep (se 2 (by rfl) ⟨18880917, by rfl⟩ : syracuseStep 50349113 = 37761835) B37761835
theorem B33566075 : Blo 1963435 33566075 := bstep (se 1 (by rfl) ⟨25174556, by rfl⟩ : syracuseStep 33566075 = 50349113) B50349113
theorem B22377383 : Blo 1963435 22377383 := bstep (se 1 (by rfl) ⟨16783037, by rfl⟩ : syracuseStep 22377383 = 33566075) B33566075
theorem B14918255 : Blo 1963435 14918255 := bstep (se 1 (by rfl) ⟨11188691, by rfl⟩ : syracuseStep 14918255 = 22377383) B22377383
theorem B9945503 : Blo 1963435 9945503 := bstep (se 1 (by rfl) ⟨7459127, by rfl⟩ : syracuseStep 9945503 = 14918255) B14918255
theorem B6630335 : Blo 1963435 6630335 := bstep (se 1 (by rfl) ⟨4972751, by rfl⟩ : syracuseStep 6630335 = 9945503) B9945503
theorem B4420223 : Blo 1963435 4420223 := bstep (se 1 (by rfl) ⟨3315167, by rfl⟩ : syracuseStep 4420223 = 6630335) B6630335
theorem B2946815 : Blo 1963435 2946815 := bstep (se 1 (by rfl) ⟨2210111, by rfl⟩ : syracuseStep 2946815 = 4420223) B4420223
theorem B1964543 : Blo 1963435 1964543 := bstep (se 1 (by rfl) ⟨1473407, by rfl⟩ : syracuseStep 1964543 = 2946815) B2946815
theorem B2946821 : Blo 1963435 2946821 := bbase (se 4 (by rfl) ⟨276264, by rfl⟩ : syracuseStep 2946821 = 552529) (by norm_num)
theorem B1964547 : Blo 1963435 1964547 := bstep (se 1 (by rfl) ⟨1473410, by rfl⟩ : syracuseStep 1964547 = 2946821) B2946821
theorem B3315181 : Blo 1963435 3315181 := bbase (se 3 (by rfl) ⟨621596, by rfl⟩ : syracuseStep 3315181 = 1243193) (by norm_num)
theorem B4420241 : Blo 1963435 4420241 := bstep (se 2 (by rfl) ⟨1657590, by rfl⟩ : syracuseStep 4420241 = 3315181) B3315181
theorem B2946827 : Blo 1963435 2946827 := bstep (se 1 (by rfl) ⟨2210120, by rfl⟩ : syracuseStep 2946827 = 4420241) B4420241
theorem B1964551 : Blo 1963435 1964551 := bstep (se 1 (by rfl) ⟨1473413, by rfl⟩ : syracuseStep 1964551 = 2946827) B2946827
theorem B2210125 : Blo 1963435 2210125 := bbase (se 3 (by rfl) ⟨414398, by rfl⟩ : syracuseStep 2210125 = 828797) (by norm_num)
theorem B2946833 : Blo 1963435 2946833 := bstep (se 2 (by rfl) ⟨1105062, by rfl⟩ : syracuseStep 2946833 = 2210125) B2210125
theorem B1964555 : Blo 1963435 1964555 := bstep (se 1 (by rfl) ⟨1473416, by rfl⟩ : syracuseStep 1964555 = 2946833) B2946833
theorem B6630389 : Blo 1963435 6630389 := bbase (se 5 (by rfl) ⟨310799, by rfl⟩ : syracuseStep 6630389 = 621599) (by norm_num)
theorem B4420259 : Blo 1963435 4420259 := bstep (se 1 (by rfl) ⟨3315194, by rfl⟩ : syracuseStep 4420259 = 6630389) B6630389
theorem B2946839 : Blo 1963435 2946839 := bstep (se 1 (by rfl) ⟨2210129, by rfl⟩ : syracuseStep 2946839 = 4420259) B4420259
theorem B1964559 : Blo 1963435 1964559 := bstep (se 1 (by rfl) ⟨1473419, by rfl⟩ : syracuseStep 1964559 = 2946839) B2946839
theorem B2946845 : Blo 1963435 2946845 := bbase (se 3 (by rfl) ⟨552533, by rfl⟩ : syracuseStep 2946845 = 1105067) (by norm_num)
theorem B1964563 : Blo 1963435 1964563 := bstep (se 1 (by rfl) ⟨1473422, by rfl⟩ : syracuseStep 1964563 = 2946845) B2946845
theorem B4420277 : Blo 1963435 4420277 := bbase (se 5 (by rfl) ⟨207200, by rfl⟩ : syracuseStep 4420277 = 414401) (by norm_num)
theorem B2946851 : Blo 1963435 2946851 := bstep (se 1 (by rfl) ⟨2210138, by rfl⟩ : syracuseStep 2946851 = 4420277) B4420277
theorem B1964567 : Blo 1963435 1964567 := bstep (se 1 (by rfl) ⟨1473425, by rfl⟩ : syracuseStep 1964567 = 2946851) B2946851
theorem B11188853 : Blo 1963435 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B7459235 : Blo 1963435 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4972823 : Blo 1963435 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B3315215 : Blo 1963435 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B2210143 : Blo 1963435 2210143 := bstep (se 1 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 2210143 = 3315215) B3315215
theorem B2946857 : Blo 1963435 2946857 := bstep (se 2 (by rfl) ⟨1105071, by rfl⟩ : syracuseStep 2946857 = 2210143) B2210143
theorem B1964571 : Blo 1963435 1964571 := bstep (se 1 (by rfl) ⟨1473428, by rfl⟩ : syracuseStep 1964571 = 2946857) B2946857
theorem B5594437 : Blo 1963435 5594437 := bbase (se 4 (by rfl) ⟨524478, by rfl⟩ : syracuseStep 5594437 = 1048957) (by norm_num)
theorem B7459249 : Blo 1963435 7459249 := bstep (se 2 (by rfl) ⟨2797218, by rfl⟩ : syracuseStep 7459249 = 5594437) B5594437
theorem B9945665 : Blo 1963435 9945665 := bstep (se 2 (by rfl) ⟨3729624, by rfl⟩ : syracuseStep 9945665 = 7459249) B7459249
theorem B6630443 : Blo 1963435 6630443 := bstep (se 1 (by rfl) ⟨4972832, by rfl⟩ : syracuseStep 6630443 = 9945665) B9945665
theorem B4420295 : Blo 1963435 4420295 := bstep (se 1 (by rfl) ⟨3315221, by rfl⟩ : syracuseStep 4420295 = 6630443) B6630443
theorem B2946863 : Blo 1963435 2946863 := bstep (se 1 (by rfl) ⟨2210147, by rfl⟩ : syracuseStep 2946863 = 4420295) B4420295
theorem B1964575 : Blo 1963435 1964575 := bstep (se 1 (by rfl) ⟨1473431, by rfl⟩ : syracuseStep 1964575 = 2946863) B2946863
theorem B2946869 : Blo 1963435 2946869 := bbase (se 5 (by rfl) ⟨138134, by rfl⟩ : syracuseStep 2946869 = 276269) (by norm_num)
theorem B1964579 : Blo 1963435 1964579 := bstep (se 1 (by rfl) ⟨1473434, by rfl⟩ : syracuseStep 1964579 = 2946869) B2946869
theorem B4972853 : Blo 1963435 4972853 := bbase (se 5 (by rfl) ⟨233102, by rfl⟩ : syracuseStep 4972853 = 466205) (by norm_num)
theorem B3315235 : Blo 1963435 3315235 := bstep (se 1 (by rfl) ⟨2486426, by rfl⟩ : syracuseStep 3315235 = 4972853) B4972853
theorem B4420313 : Blo 1963435 4420313 := bstep (se 2 (by rfl) ⟨1657617, by rfl⟩ : syracuseStep 4420313 = 3315235) B3315235
theorem B2946875 : Blo 1963435 2946875 := bstep (se 1 (by rfl) ⟨2210156, by rfl⟩ : syracuseStep 2946875 = 4420313) B4420313
theorem B1964583 : Blo 1963435 1964583 := bstep (se 1 (by rfl) ⟨1473437, by rfl⟩ : syracuseStep 1964583 = 2946875) B2946875
theorem B2210161 : Blo 1963435 2210161 := bbase (se 2 (by rfl) ⟨828810, by rfl⟩ : syracuseStep 2210161 = 1657621) (by norm_num)
theorem B2946881 : Blo 1963435 2946881 := bstep (se 2 (by rfl) ⟨1105080, by rfl⟩ : syracuseStep 2946881 = 2210161) B2210161
theorem B1964587 : Blo 1963435 1964587 := bstep (se 1 (by rfl) ⟨1473440, by rfl⟩ : syracuseStep 1964587 = 2946881) B2946881
theorem B2360173 : Blo 1963435 2360173 := bbase (se 3 (by rfl) ⟨442532, by rfl⟩ : syracuseStep 2360173 = 885065) (by norm_num)
theorem B3146897 : Blo 1963435 3146897 := bstep (se 2 (by rfl) ⟨1180086, by rfl⟩ : syracuseStep 3146897 = 2360173) B2360173
theorem B8391725 : Blo 1963435 8391725 := bstep (se 3 (by rfl) ⟨1573448, by rfl⟩ : syracuseStep 8391725 = 3146897) B3146897
theorem B5594483 : Blo 1963435 5594483 := bstep (se 1 (by rfl) ⟨4195862, by rfl⟩ : syracuseStep 5594483 = 8391725) B8391725
theorem B3729655 : Blo 1963435 3729655 := bstep (se 1 (by rfl) ⟨2797241, by rfl⟩ : syracuseStep 3729655 = 5594483) B5594483
theorem B4972873 : Blo 1963435 4972873 := bstep (se 2 (by rfl) ⟨1864827, by rfl⟩ : syracuseStep 4972873 = 3729655) B3729655
theorem B6630497 : Blo 1963435 6630497 := bstep (se 2 (by rfl) ⟨2486436, by rfl⟩ : syracuseStep 6630497 = 4972873) B4972873
theorem B4420331 : Blo 1963435 4420331 := bstep (se 1 (by rfl) ⟨3315248, by rfl⟩ : syracuseStep 4420331 = 6630497) B6630497
theorem B2946887 : Blo 1963435 2946887 := bstep (se 1 (by rfl) ⟨2210165, by rfl⟩ : syracuseStep 2946887 = 4420331) B4420331
theorem B1964591 : Blo 1963435 1964591 := bstep (se 1 (by rfl) ⟨1473443, by rfl⟩ : syracuseStep 1964591 = 2946887) B2946887
theorem B2946893 : Blo 1963435 2946893 := bbase (se 3 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 2946893 = 1105085) (by norm_num)
theorem B1964595 : Blo 1963435 1964595 := bstep (se 1 (by rfl) ⟨1473446, by rfl⟩ : syracuseStep 1964595 = 2946893) B2946893
theorem B4420349 : Blo 1963435 4420349 := bbase (se 3 (by rfl) ⟨828815, by rfl⟩ : syracuseStep 4420349 = 1657631) (by norm_num)
theorem B2946899 : Blo 1963435 2946899 := bstep (se 1 (by rfl) ⟨2210174, by rfl⟩ : syracuseStep 2946899 = 4420349) B4420349
theorem B1964599 : Blo 1963435 1964599 := bstep (se 1 (by rfl) ⟨1473449, by rfl⟩ : syracuseStep 1964599 = 2946899) B2946899
theorem B3315269 : Blo 1963435 3315269 := bbase (se 4 (by rfl) ⟨310806, by rfl⟩ : syracuseStep 3315269 = 621613) (by norm_num)
theorem B2210179 : Blo 1963435 2210179 := bstep (se 1 (by rfl) ⟨1657634, by rfl⟩ : syracuseStep 2210179 = 3315269) B3315269
theorem B2946905 : Blo 1963435 2946905 := bstep (se 2 (by rfl) ⟨1105089, by rfl⟩ : syracuseStep 2946905 = 2210179) B2210179
theorem B1964603 : Blo 1963435 1964603 := bstep (se 1 (by rfl) ⟨1473452, by rfl⟩ : syracuseStep 1964603 = 2946905) B2946905
theorem B14918741 : Blo 1963435 14918741 := bbase (se 8 (by rfl) ⟨87414, by rfl⟩ : syracuseStep 14918741 = 174829) (by norm_num)
theorem B9945827 : Blo 1963435 9945827 := bstep (se 1 (by rfl) ⟨7459370, by rfl⟩ : syracuseStep 9945827 = 14918741) B14918741
theorem B6630551 : Blo 1963435 6630551 := bstep (se 1 (by rfl) ⟨4972913, by rfl⟩ : syracuseStep 6630551 = 9945827) B9945827
theorem B4420367 : Blo 1963435 4420367 := bstep (se 1 (by rfl) ⟨3315275, by rfl⟩ : syracuseStep 4420367 = 6630551) B6630551
theorem B2946911 : Blo 1963435 2946911 := bstep (se 1 (by rfl) ⟨2210183, by rfl⟩ : syracuseStep 2946911 = 4420367) B4420367
theorem B1964607 : Blo 1963435 1964607 := bstep (se 1 (by rfl) ⟨1473455, by rfl⟩ : syracuseStep 1964607 = 2946911) B2946911
theorem B2946917 : Blo 1963435 2946917 := bbase (se 4 (by rfl) ⟨276273, by rfl⟩ : syracuseStep 2946917 = 552547) (by norm_num)
theorem B1964611 : Blo 1963435 1964611 := bstep (se 1 (by rfl) ⟨1473458, by rfl⟩ : syracuseStep 1964611 = 2946917) B2946917
theorem B3729701 : Blo 1963435 3729701 := bbase (se 4 (by rfl) ⟨349659, by rfl⟩ : syracuseStep 3729701 = 699319) (by norm_num)
theorem B2486467 : Blo 1963435 2486467 := bstep (se 1 (by rfl) ⟨1864850, by rfl⟩ : syracuseStep 2486467 = 3729701) B3729701
theorem B3315289 : Blo 1963435 3315289 := bstep (se 2 (by rfl) ⟨1243233, by rfl⟩ : syracuseStep 3315289 = 2486467) B2486467
theorem B4420385 : Blo 1963435 4420385 := bstep (se 2 (by rfl) ⟨1657644, by rfl⟩ : syracuseStep 4420385 = 3315289) B3315289
theorem B2946923 : Blo 1963435 2946923 := bstep (se 1 (by rfl) ⟨2210192, by rfl⟩ : syracuseStep 2946923 = 4420385) B4420385
theorem B1964615 : Blo 1963435 1964615 := bstep (se 1 (by rfl) ⟨1473461, by rfl⟩ : syracuseStep 1964615 = 2946923) B2946923
theorem B2210197 : Blo 1963435 2210197 := bbase (se 6 (by rfl) ⟨51801, by rfl⟩ : syracuseStep 2210197 = 103603) (by norm_num)
theorem B2946929 : Blo 1963435 2946929 := bstep (se 2 (by rfl) ⟨1105098, by rfl⟩ : syracuseStep 2946929 = 2210197) B2210197
theorem B1964619 : Blo 1963435 1964619 := bstep (se 1 (by rfl) ⟨1473464, by rfl⟩ : syracuseStep 1964619 = 2946929) B2946929
theorem B2486477 : Blo 1963435 2486477 := bbase (se 3 (by rfl) ⟨466214, by rfl⟩ : syracuseStep 2486477 = 932429) (by norm_num)
theorem B6630605 : Blo 1963435 6630605 := bstep (se 3 (by rfl) ⟨1243238, by rfl⟩ : syracuseStep 6630605 = 2486477) B2486477
theorem B4420403 : Blo 1963435 4420403 := bstep (se 1 (by rfl) ⟨3315302, by rfl⟩ : syracuseStep 4420403 = 6630605) B6630605
theorem B2946935 : Blo 1963435 2946935 := bstep (se 1 (by rfl) ⟨2210201, by rfl⟩ : syracuseStep 2946935 = 4420403) B4420403
theorem B1964623 : Blo 1963435 1964623 := bstep (se 1 (by rfl) ⟨1473467, by rfl⟩ : syracuseStep 1964623 = 2946935) B2946935
theorem B2946941 : Blo 1963435 2946941 := bbase (se 3 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 2946941 = 1105103) (by norm_num)
theorem B1964627 : Blo 1963435 1964627 := bstep (se 1 (by rfl) ⟨1473470, by rfl⟩ : syracuseStep 1964627 = 2946941) B2946941
theorem B4420421 : Blo 1963435 4420421 := bbase (se 4 (by rfl) ⟨414414, by rfl⟩ : syracuseStep 4420421 = 828829) (by norm_num)
theorem B2946947 : Blo 1963435 2946947 := bstep (se 1 (by rfl) ⟨2210210, by rfl⟩ : syracuseStep 2946947 = 4420421) B4420421
theorem B1964631 : Blo 1963435 1964631 := bstep (se 1 (by rfl) ⟨1473473, by rfl⟩ : syracuseStep 1964631 = 2946947) B2946947
theorem B4195957 : Blo 1963435 4195957 := bbase (se 5 (by rfl) ⟨196685, by rfl⟩ : syracuseStep 4195957 = 393371) (by norm_num)
theorem B5594609 : Blo 1963435 5594609 := bstep (se 2 (by rfl) ⟨2097978, by rfl⟩ : syracuseStep 5594609 = 4195957) B4195957
theorem B3729739 : Blo 1963435 3729739 := bstep (se 1 (by rfl) ⟨2797304, by rfl⟩ : syracuseStep 3729739 = 5594609) B5594609
theorem B4972985 : Blo 1963435 4972985 := bstep (se 2 (by rfl) ⟨1864869, by rfl⟩ : syracuseStep 4972985 = 3729739) B3729739
theorem B3315323 : Blo 1963435 3315323 := bstep (se 1 (by rfl) ⟨2486492, by rfl⟩ : syracuseStep 3315323 = 4972985) B4972985
theorem B2210215 : Blo 1963435 2210215 := bstep (se 1 (by rfl) ⟨1657661, by rfl⟩ : syracuseStep 2210215 = 3315323) B3315323
theorem B2946953 : Blo 1963435 2946953 := bstep (se 2 (by rfl) ⟨1105107, by rfl⟩ : syracuseStep 2946953 = 2210215) B2210215
theorem B1964635 : Blo 1963435 1964635 := bstep (se 1 (by rfl) ⟨1473476, by rfl⟩ : syracuseStep 1964635 = 2946953) B2946953
theorem B9945989 : Blo 1963435 9945989 := bbase (se 4 (by rfl) ⟨932436, by rfl⟩ : syracuseStep 9945989 = 1864873) (by norm_num)
theorem B6630659 : Blo 1963435 6630659 := bstep (se 1 (by rfl) ⟨4972994, by rfl⟩ : syracuseStep 6630659 = 9945989) B9945989
theorem B4420439 : Blo 1963435 4420439 := bstep (se 1 (by rfl) ⟨3315329, by rfl⟩ : syracuseStep 4420439 = 6630659) B6630659
theorem B2946959 : Blo 1963435 2946959 := bstep (se 1 (by rfl) ⟨2210219, by rfl⟩ : syracuseStep 2946959 = 4420439) B4420439
theorem B1964639 : Blo 1963435 1964639 := bstep (se 1 (by rfl) ⟨1473479, by rfl⟩ : syracuseStep 1964639 = 2946959) B2946959
theorem B2946965 : Blo 1963435 2946965 := bbase (se 6 (by rfl) ⟨69069, by rfl⟩ : syracuseStep 2946965 = 138139) (by norm_num)
theorem B1964643 : Blo 1963435 1964643 := bstep (se 1 (by rfl) ⟨1473482, by rfl⟩ : syracuseStep 1964643 = 2946965) B2946965
theorem B6721157 : Blo 1963435 6721157 := bbase (se 4 (by rfl) ⟨630108, by rfl⟩ : syracuseStep 6721157 = 1260217) (by norm_num)
theorem B4480771 : Blo 1963435 4480771 := bstep (se 1 (by rfl) ⟨3360578, by rfl⟩ : syracuseStep 4480771 = 6721157) B6721157
theorem B5974361 : Blo 1963435 5974361 := bstep (se 2 (by rfl) ⟨2240385, by rfl⟩ : syracuseStep 5974361 = 4480771) B4480771
theorem B3982907 : Blo 1963435 3982907 := bstep (se 1 (by rfl) ⟨2987180, by rfl⟩ : syracuseStep 3982907 = 5974361) B5974361
theorem B2655271 : Blo 1963435 2655271 := bstep (se 1 (by rfl) ⟨1991453, by rfl⟩ : syracuseStep 2655271 = 3982907) B3982907
theorem B3540361 : Blo 1963435 3540361 := bstep (se 2 (by rfl) ⟨1327635, by rfl⟩ : syracuseStep 3540361 = 2655271) B2655271
theorem B4720481 : Blo 1963435 4720481 := bstep (se 2 (by rfl) ⟨1770180, by rfl⟩ : syracuseStep 4720481 = 3540361) B3540361
theorem B3146987 : Blo 1963435 3146987 := bstep (se 1 (by rfl) ⟨2360240, by rfl⟩ : syracuseStep 3146987 = 4720481) B4720481
theorem B2097991 : Blo 1963435 2097991 := bstep (se 1 (by rfl) ⟨1573493, by rfl⟩ : syracuseStep 2097991 = 3146987) B3146987
theorem B11189285 : Blo 1963435 11189285 := bstep (se 4 (by rfl) ⟨1048995, by rfl⟩ : syracuseStep 11189285 = 2097991) B2097991
theorem B7459523 : Blo 1963435 7459523 := bstep (se 1 (by rfl) ⟨5594642, by rfl⟩ : syracuseStep 7459523 = 11189285) B11189285
theorem B4973015 : Blo 1963435 4973015 := bstep (se 1 (by rfl) ⟨3729761, by rfl⟩ : syracuseStep 4973015 = 7459523) B7459523
theorem B3315343 : Blo 1963435 3315343 := bstep (se 1 (by rfl) ⟨2486507, by rfl⟩ : syracuseStep 3315343 = 4973015) B4973015
theorem B4420457 : Blo 1963435 4420457 := bstep (se 2 (by rfl) ⟨1657671, by rfl⟩ : syracuseStep 4420457 = 3315343) B3315343
theorem B2946971 : Blo 1963435 2946971 := bstep (se 1 (by rfl) ⟨2210228, by rfl⟩ : syracuseStep 2946971 = 4420457) B4420457
theorem B1964647 : Blo 1963435 1964647 := bstep (se 1 (by rfl) ⟨1473485, by rfl⟩ : syracuseStep 1964647 = 2946971) B2946971
theorem B2210233 : Blo 1963435 2210233 := bbase (se 2 (by rfl) ⟨828837, by rfl⟩ : syracuseStep 2210233 = 1657675) (by norm_num)
theorem B2946977 : Blo 1963435 2946977 := bstep (se 2 (by rfl) ⟨1105116, by rfl⟩ : syracuseStep 2946977 = 2210233) B2210233
theorem B1964651 : Blo 1963435 1964651 := bstep (se 1 (by rfl) ⟨1473488, by rfl⟩ : syracuseStep 1964651 = 2946977) B2946977
theorem B2425093 : Blo 1963435 2425093 := bbase (se 4 (by rfl) ⟨227352, by rfl⟩ : syracuseStep 2425093 = 454705) (by norm_num)
theorem B12933829 : Blo 1963435 12933829 := bstep (se 4 (by rfl) ⟨1212546, by rfl⟩ : syracuseStep 12933829 = 2425093) B2425093
theorem B17245105 : Blo 1963435 17245105 := bstep (se 2 (by rfl) ⟨6466914, by rfl⟩ : syracuseStep 17245105 = 12933829) B12933829
theorem B91973893 : Blo 1963435 91973893 := bstep (se 4 (by rfl) ⟨8622552, by rfl⟩ : syracuseStep 91973893 = 17245105) B17245105
theorem B122631857 : Blo 1963435 122631857 := bstep (se 2 (by rfl) ⟨45986946, by rfl⟩ : syracuseStep 122631857 = 91973893) B91973893
theorem B81754571 : Blo 1963435 81754571 := bstep (se 1 (by rfl) ⟨61315928, by rfl⟩ : syracuseStep 81754571 = 122631857) B122631857
theorem B54503047 : Blo 1963435 54503047 := bstep (se 1 (by rfl) ⟨40877285, by rfl⟩ : syracuseStep 54503047 = 81754571) B81754571
theorem B72670729 : Blo 1963435 72670729 := bstep (se 2 (by rfl) ⟨27251523, by rfl⟩ : syracuseStep 72670729 = 54503047) B54503047
theorem B96894305 : Blo 1963435 96894305 := bstep (se 2 (by rfl) ⟨36335364, by rfl⟩ : syracuseStep 96894305 = 72670729) B72670729
theorem B64596203 : Blo 1963435 64596203 := bstep (se 1 (by rfl) ⟨48447152, by rfl⟩ : syracuseStep 64596203 = 96894305) B96894305
theorem B43064135 : Blo 1963435 43064135 := bstep (se 1 (by rfl) ⟨32298101, by rfl⟩ : syracuseStep 43064135 = 64596203) B64596203
theorem B28709423 : Blo 1963435 28709423 := bstep (se 1 (by rfl) ⟨21532067, by rfl⟩ : syracuseStep 28709423 = 43064135) B43064135
theorem B19139615 : Blo 1963435 19139615 := bstep (se 1 (by rfl) ⟨14354711, by rfl⟩ : syracuseStep 19139615 = 28709423) B28709423
theorem B12759743 : Blo 1963435 12759743 := bstep (se 1 (by rfl) ⟨9569807, by rfl⟩ : syracuseStep 12759743 = 19139615) B19139615
theorem B8506495 : Blo 1963435 8506495 := bstep (se 1 (by rfl) ⟨6379871, by rfl⟩ : syracuseStep 8506495 = 12759743) B12759743
theorem B11341993 : Blo 1963435 11341993 := bstep (se 2 (by rfl) ⟨4253247, by rfl⟩ : syracuseStep 11341993 = 8506495) B8506495
theorem B15122657 : Blo 1963435 15122657 := bstep (se 2 (by rfl) ⟨5670996, by rfl⟩ : syracuseStep 15122657 = 11341993) B11341993
theorem B40327085 : Blo 1963435 40327085 := bstep (se 3 (by rfl) ⟨7561328, by rfl⟩ : syracuseStep 40327085 = 15122657) B15122657
theorem B26884723 : Blo 1963435 26884723 := bstep (se 1 (by rfl) ⟨20163542, by rfl⟩ : syracuseStep 26884723 = 40327085) B40327085
theorem B35846297 : Blo 1963435 35846297 := bstep (se 2 (by rfl) ⟨13442361, by rfl⟩ : syracuseStep 35846297 = 26884723) B26884723
theorem B23897531 : Blo 1963435 23897531 := bstep (se 1 (by rfl) ⟨17923148, by rfl⟩ : syracuseStep 23897531 = 35846297) B35846297
theorem B15931687 : Blo 1963435 15931687 := bstep (se 1 (by rfl) ⟨11948765, by rfl⟩ : syracuseStep 15931687 = 23897531) B23897531
theorem B21242249 : Blo 1963435 21242249 := bstep (se 2 (by rfl) ⟨7965843, by rfl⟩ : syracuseStep 21242249 = 15931687) B15931687
theorem B14161499 : Blo 1963435 14161499 := bstep (se 1 (by rfl) ⟨10621124, by rfl⟩ : syracuseStep 14161499 = 21242249) B21242249
theorem B9440999 : Blo 1963435 9440999 := bstep (se 1 (by rfl) ⟨7080749, by rfl⟩ : syracuseStep 9440999 = 14161499) B14161499
theorem B6293999 : Blo 1963435 6293999 := bstep (se 1 (by rfl) ⟨4720499, by rfl⟩ : syracuseStep 6293999 = 9440999) B9440999
theorem B4195999 : Blo 1963435 4195999 := bstep (se 1 (by rfl) ⟨3146999, by rfl⟩ : syracuseStep 4195999 = 6293999) B6293999
theorem B5594665 : Blo 1963435 5594665 := bstep (se 2 (by rfl) ⟨2097999, by rfl⟩ : syracuseStep 5594665 = 4195999) B4195999
theorem B7459553 : Blo 1963435 7459553 := bstep (se 2 (by rfl) ⟨2797332, by rfl⟩ : syracuseStep 7459553 = 5594665) B5594665
theorem B4973035 : Blo 1963435 4973035 := bstep (se 1 (by rfl) ⟨3729776, by rfl⟩ : syracuseStep 4973035 = 7459553) B7459553
theorem B6630713 : Blo 1963435 6630713 := bstep (se 2 (by rfl) ⟨2486517, by rfl⟩ : syracuseStep 6630713 = 4973035) B4973035
theorem B4420475 : Blo 1963435 4420475 := bstep (se 1 (by rfl) ⟨3315356, by rfl⟩ : syracuseStep 4420475 = 6630713) B6630713
theorem B2946983 : Blo 1963435 2946983 := bstep (se 1 (by rfl) ⟨2210237, by rfl⟩ : syracuseStep 2946983 = 4420475) B4420475
theorem B1964655 : Blo 1963435 1964655 := bstep (se 1 (by rfl) ⟨1473491, by rfl⟩ : syracuseStep 1964655 = 2946983) B2946983
theorem B2946989 : Blo 1963435 2946989 := bbase (se 3 (by rfl) ⟨552560, by rfl⟩ : syracuseStep 2946989 = 1105121) (by norm_num)
theorem B1964659 : Blo 1963435 1964659 := bstep (se 1 (by rfl) ⟨1473494, by rfl⟩ : syracuseStep 1964659 = 2946989) B2946989
theorem B4420493 : Blo 1963435 4420493 := bbase (se 3 (by rfl) ⟨828842, by rfl⟩ : syracuseStep 4420493 = 1657685) (by norm_num)
theorem B2946995 : Blo 1963435 2946995 := bstep (se 1 (by rfl) ⟨2210246, by rfl⟩ : syracuseStep 2946995 = 4420493) B4420493
theorem B1964663 : Blo 1963435 1964663 := bstep (se 1 (by rfl) ⟨1473497, by rfl⟩ : syracuseStep 1964663 = 2946995) B2946995
theorem B2486533 : Blo 1963435 2486533 := bbase (se 4 (by rfl) ⟨233112, by rfl⟩ : syracuseStep 2486533 = 466225) (by norm_num)
theorem B3315377 : Blo 1963435 3315377 := bstep (se 2 (by rfl) ⟨1243266, by rfl⟩ : syracuseStep 3315377 = 2486533) B2486533
theorem B2210251 : Blo 1963435 2210251 := bstep (se 1 (by rfl) ⟨1657688, by rfl⟩ : syracuseStep 2210251 = 3315377) B3315377
theorem B2947001 : Blo 1963435 2947001 := bstep (se 2 (by rfl) ⟨1105125, by rfl⟩ : syracuseStep 2947001 = 2210251) B2210251
theorem B1964667 : Blo 1963435 1964667 := bstep (se 1 (by rfl) ⟨1473500, by rfl⟩ : syracuseStep 1964667 = 2947001) B2947001
theorem B1991477 : Blo 1963435 1991477 := bbase (se 5 (by rfl) ⟨93350, by rfl⟩ : syracuseStep 1991477 = 186701) (by norm_num)
theorem B5310605 : Blo 1963435 5310605 := bstep (se 3 (by rfl) ⟨995738, by rfl⟩ : syracuseStep 5310605 = 1991477) B1991477
theorem B3540403 : Blo 1963435 3540403 := bstep (se 1 (by rfl) ⟨2655302, by rfl⟩ : syracuseStep 3540403 = 5310605) B5310605
theorem B4720537 : Blo 1963435 4720537 := bstep (se 2 (by rfl) ⟨1770201, by rfl⟩ : syracuseStep 4720537 = 3540403) B3540403
theorem B25176197 : Blo 1963435 25176197 := bstep (se 4 (by rfl) ⟨2360268, by rfl⟩ : syracuseStep 25176197 = 4720537) B4720537
theorem B16784131 : Blo 1963435 16784131 := bstep (se 1 (by rfl) ⟨12588098, by rfl⟩ : syracuseStep 16784131 = 25176197) B25176197
theorem B22378841 : Blo 1963435 22378841 := bstep (se 2 (by rfl) ⟨8392065, by rfl⟩ : syracuseStep 22378841 = 16784131) B16784131
theorem B14919227 : Blo 1963435 14919227 := bstep (se 1 (by rfl) ⟨11189420, by rfl⟩ : syracuseStep 14919227 = 22378841) B22378841
theorem B9946151 : Blo 1963435 9946151 := bstep (se 1 (by rfl) ⟨7459613, by rfl⟩ : syracuseStep 9946151 = 14919227) B14919227
theorem B6630767 : Blo 1963435 6630767 := bstep (se 1 (by rfl) ⟨4973075, by rfl⟩ : syracuseStep 6630767 = 9946151) B9946151
theorem B4420511 : Blo 1963435 4420511 := bstep (se 1 (by rfl) ⟨3315383, by rfl⟩ : syracuseStep 4420511 = 6630767) B6630767
theorem B2947007 : Blo 1963435 2947007 := bstep (se 1 (by rfl) ⟨2210255, by rfl⟩ : syracuseStep 2947007 = 4420511) B4420511
theorem B1964671 : Blo 1963435 1964671 := bstep (se 1 (by rfl) ⟨1473503, by rfl⟩ : syracuseStep 1964671 = 2947007) B2947007
theorem B2947013 : Blo 1963435 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B1964675 : Blo 1963435 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B3315397 : Blo 1963435 3315397 := bbase (se 4 (by rfl) ⟨310818, by rfl⟩ : syracuseStep 3315397 = 621637) (by norm_num)
theorem B4420529 : Blo 1963435 4420529 := bstep (se 2 (by rfl) ⟨1657698, by rfl⟩ : syracuseStep 4420529 = 3315397) B3315397
theorem B2947019 : Blo 1963435 2947019 := bstep (se 1 (by rfl) ⟨2210264, by rfl⟩ : syracuseStep 2947019 = 4420529) B4420529
theorem B1964679 : Blo 1963435 1964679 := bstep (se 1 (by rfl) ⟨1473509, by rfl⟩ : syracuseStep 1964679 = 2947019) B2947019
theorem B2210269 : Blo 1963435 2210269 := bbase (se 3 (by rfl) ⟨414425, by rfl⟩ : syracuseStep 2210269 = 828851) (by norm_num)
theorem B2947025 : Blo 1963435 2947025 := bstep (se 2 (by rfl) ⟨1105134, by rfl⟩ : syracuseStep 2947025 = 2210269) B2210269
theorem B1964683 : Blo 1963435 1964683 := bstep (se 1 (by rfl) ⟨1473512, by rfl⟩ : syracuseStep 1964683 = 2947025) B2947025
theorem B6630821 : Blo 1963435 6630821 := bbase (se 4 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 6630821 = 1243279) (by norm_num)
theorem B4420547 : Blo 1963435 4420547 := bstep (se 1 (by rfl) ⟨3315410, by rfl⟩ : syracuseStep 4420547 = 6630821) B6630821
theorem B2947031 : Blo 1963435 2947031 := bstep (se 1 (by rfl) ⟨2210273, by rfl⟩ : syracuseStep 2947031 = 4420547) B4420547
theorem B1964687 : Blo 1963435 1964687 := bstep (se 1 (by rfl) ⟨1473515, by rfl⟩ : syracuseStep 1964687 = 2947031) B2947031
theorem B2947037 : Blo 1963435 2947037 := bbase (se 3 (by rfl) ⟨552569, by rfl⟩ : syracuseStep 2947037 = 1105139) (by norm_num)
theorem B1964691 : Blo 1963435 1964691 := bstep (se 1 (by rfl) ⟨1473518, by rfl⟩ : syracuseStep 1964691 = 2947037) B2947037
theorem B4420565 : Blo 1963435 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B2947043 : Blo 1963435 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B1964695 : Blo 1963435 1964695 := bstep (se 1 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 1964695 = 2947043) B2947043
theorem B5974517 : Blo 1963435 5974517 := bbase (se 5 (by rfl) ⟨280055, by rfl⟩ : syracuseStep 5974517 = 560111) (by norm_num)
theorem B15932045 : Blo 1963435 15932045 := bstep (se 3 (by rfl) ⟨2987258, by rfl⟩ : syracuseStep 15932045 = 5974517) B5974517
theorem B10621363 : Blo 1963435 10621363 := bstep (se 1 (by rfl) ⟨7966022, by rfl⟩ : syracuseStep 10621363 = 15932045) B15932045
theorem B14161817 : Blo 1963435 14161817 := bstep (se 2 (by rfl) ⟨5310681, by rfl⟩ : syracuseStep 14161817 = 10621363) B10621363
theorem B9441211 : Blo 1963435 9441211 := bstep (se 1 (by rfl) ⟨7080908, by rfl⟩ : syracuseStep 9441211 = 14161817) B14161817
theorem B12588281 : Blo 1963435 12588281 := bstep (se 2 (by rfl) ⟨4720605, by rfl⟩ : syracuseStep 12588281 = 9441211) B9441211
theorem B8392187 : Blo 1963435 8392187 := bstep (se 1 (by rfl) ⟨6294140, by rfl⟩ : syracuseStep 8392187 = 12588281) B12588281
theorem B5594791 : Blo 1963435 5594791 := bstep (se 1 (by rfl) ⟨4196093, by rfl⟩ : syracuseStep 5594791 = 8392187) B8392187
theorem B7459721 : Blo 1963435 7459721 := bstep (se 2 (by rfl) ⟨2797395, by rfl⟩ : syracuseStep 7459721 = 5594791) B5594791
theorem B4973147 : Blo 1963435 4973147 := bstep (se 1 (by rfl) ⟨3729860, by rfl⟩ : syracuseStep 4973147 = 7459721) B7459721
theorem B3315431 : Blo 1963435 3315431 := bstep (se 1 (by rfl) ⟨2486573, by rfl⟩ : syracuseStep 3315431 = 4973147) B4973147
theorem B2210287 : Blo 1963435 2210287 := bstep (se 1 (by rfl) ⟨1657715, by rfl⟩ : syracuseStep 2210287 = 3315431) B3315431
theorem B2947049 : Blo 1963435 2947049 := bstep (se 2 (by rfl) ⟨1105143, by rfl⟩ : syracuseStep 2947049 = 2210287) B2210287
theorem B1964699 : Blo 1963435 1964699 := bstep (se 1 (by rfl) ⟨1473524, by rfl⟩ : syracuseStep 1964699 = 2947049) B2947049
theorem B16784405 : Blo 1963435 16784405 := bbase (se 6 (by rfl) ⟨393384, by rfl⟩ : syracuseStep 16784405 = 786769) (by norm_num)
theorem B11189603 : Blo 1963435 11189603 := bstep (se 1 (by rfl) ⟨8392202, by rfl⟩ : syracuseStep 11189603 = 16784405) B16784405
theorem B7459735 : Blo 1963435 7459735 := bstep (se 1 (by rfl) ⟨5594801, by rfl⟩ : syracuseStep 7459735 = 11189603) B11189603
theorem B9946313 : Blo 1963435 9946313 := bstep (se 2 (by rfl) ⟨3729867, by rfl⟩ : syracuseStep 9946313 = 7459735) B7459735
theorem B6630875 : Blo 1963435 6630875 := bstep (se 1 (by rfl) ⟨4973156, by rfl⟩ : syracuseStep 6630875 = 9946313) B9946313
theorem B4420583 : Blo 1963435 4420583 := bstep (se 1 (by rfl) ⟨3315437, by rfl⟩ : syracuseStep 4420583 = 6630875) B6630875
theorem B2947055 : Blo 1963435 2947055 := bstep (se 1 (by rfl) ⟨2210291, by rfl⟩ : syracuseStep 2947055 = 4420583) B4420583
theorem B1964703 : Blo 1963435 1964703 := bstep (se 1 (by rfl) ⟨1473527, by rfl⟩ : syracuseStep 1964703 = 2947055) B2947055
theorem B2947061 : Blo 1963435 2947061 := bbase (se 5 (by rfl) ⟨138143, by rfl⟩ : syracuseStep 2947061 = 276287) (by norm_num)
theorem B1964707 : Blo 1963435 1964707 := bstep (se 1 (by rfl) ⟨1473530, by rfl⟩ : syracuseStep 1964707 = 2947061) B2947061
theorem B9441269 : Blo 1963435 9441269 := bbase (se 5 (by rfl) ⟨442559, by rfl⟩ : syracuseStep 9441269 = 885119) (by norm_num)
theorem B6294179 : Blo 1963435 6294179 := bstep (se 1 (by rfl) ⟨4720634, by rfl⟩ : syracuseStep 6294179 = 9441269) B9441269
theorem B4196119 : Blo 1963435 4196119 := bstep (se 1 (by rfl) ⟨3147089, by rfl⟩ : syracuseStep 4196119 = 6294179) B6294179
theorem B5594825 : Blo 1963435 5594825 := bstep (se 2 (by rfl) ⟨2098059, by rfl⟩ : syracuseStep 5594825 = 4196119) B4196119
theorem B3729883 : Blo 1963435 3729883 := bstep (se 1 (by rfl) ⟨2797412, by rfl⟩ : syracuseStep 3729883 = 5594825) B5594825
theorem B4973177 : Blo 1963435 4973177 := bstep (se 2 (by rfl) ⟨1864941, by rfl⟩ : syracuseStep 4973177 = 3729883) B3729883
theorem B3315451 : Blo 1963435 3315451 := bstep (se 1 (by rfl) ⟨2486588, by rfl⟩ : syracuseStep 3315451 = 4973177) B4973177
theorem B4420601 : Blo 1963435 4420601 := bstep (se 2 (by rfl) ⟨1657725, by rfl⟩ : syracuseStep 4420601 = 3315451) B3315451
theorem B2947067 : Blo 1963435 2947067 := bstep (se 1 (by rfl) ⟨2210300, by rfl⟩ : syracuseStep 2947067 = 4420601) B4420601
theorem B1964711 : Blo 1963435 1964711 := bstep (se 1 (by rfl) ⟨1473533, by rfl⟩ : syracuseStep 1964711 = 2947067) B2947067
theorem B2210305 : Blo 1963435 2210305 := bbase (se 2 (by rfl) ⟨828864, by rfl⟩ : syracuseStep 2210305 = 1657729) (by norm_num)
theorem B2947073 : Blo 1963435 2947073 := bstep (se 2 (by rfl) ⟨1105152, by rfl⟩ : syracuseStep 2947073 = 2210305) B2210305
theorem B1964715 : Blo 1963435 1964715 := bstep (se 1 (by rfl) ⟨1473536, by rfl⟩ : syracuseStep 1964715 = 2947073) B2947073
theorem B4973197 : Blo 1963435 4973197 := bbase (se 3 (by rfl) ⟨932474, by rfl⟩ : syracuseStep 4973197 = 1864949) (by norm_num)
theorem B6630929 : Blo 1963435 6630929 := bstep (se 2 (by rfl) ⟨2486598, by rfl⟩ : syracuseStep 6630929 = 4973197) B4973197
theorem B4420619 : Blo 1963435 4420619 := bstep (se 1 (by rfl) ⟨3315464, by rfl⟩ : syracuseStep 4420619 = 6630929) B6630929
theorem B2947079 : Blo 1963435 2947079 := bstep (se 1 (by rfl) ⟨2210309, by rfl⟩ : syracuseStep 2947079 = 4420619) B4420619
theorem B1964719 : Blo 1963435 1964719 := bstep (se 1 (by rfl) ⟨1473539, by rfl⟩ : syracuseStep 1964719 = 2947079) B2947079
theorem B2947085 : Blo 1963435 2947085 := bbase (se 3 (by rfl) ⟨552578, by rfl⟩ : syracuseStep 2947085 = 1105157) (by norm_num)
theorem B1964723 : Blo 1963435 1964723 := bstep (se 1 (by rfl) ⟨1473542, by rfl⟩ : syracuseStep 1964723 = 2947085) B2947085
theorem B4420637 : Blo 1963435 4420637 := bbase (se 3 (by rfl) ⟨828869, by rfl⟩ : syracuseStep 4420637 = 1657739) (by norm_num)
theorem B2947091 : Blo 1963435 2947091 := bstep (se 1 (by rfl) ⟨2210318, by rfl⟩ : syracuseStep 2947091 = 4420637) B4420637
theorem B1964727 : Blo 1963435 1964727 := bstep (se 1 (by rfl) ⟨1473545, by rfl⟩ : syracuseStep 1964727 = 2947091) B2947091
theorem B3315485 : Blo 1963435 3315485 := bbase (se 3 (by rfl) ⟨621653, by rfl⟩ : syracuseStep 3315485 = 1243307) (by norm_num)
theorem B2210323 : Blo 1963435 2210323 := bstep (se 1 (by rfl) ⟨1657742, by rfl⟩ : syracuseStep 2210323 = 3315485) B3315485
theorem B2947097 : Blo 1963435 2947097 := bstep (se 2 (by rfl) ⟨1105161, by rfl⟩ : syracuseStep 2947097 = 2210323) B2210323
theorem B1964731 : Blo 1963435 1964731 := bstep (se 1 (by rfl) ⟨1473548, by rfl⟩ : syracuseStep 1964731 = 2947097) B2947097
theorem B2655389 : Blo 1963435 2655389 := bbase (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) (by norm_num)
theorem B7081037 : Blo 1963435 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B4720691 : Blo 1963435 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B12588509 : Blo 1963435 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B8392339 : Blo 1963435 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B11189785 : Blo 1963435 11189785 := bstep (se 2 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 11189785 = 8392339) B8392339
theorem B14919713 : Blo 1963435 14919713 := bstep (se 2 (by rfl) ⟨5594892, by rfl⟩ : syracuseStep 14919713 = 11189785) B11189785
theorem B9946475 : Blo 1963435 9946475 := bstep (se 1 (by rfl) ⟨7459856, by rfl⟩ : syracuseStep 9946475 = 14919713) B14919713
theorem B6630983 : Blo 1963435 6630983 := bstep (se 1 (by rfl) ⟨4973237, by rfl⟩ : syracuseStep 6630983 = 9946475) B9946475
theorem B4420655 : Blo 1963435 4420655 := bstep (se 1 (by rfl) ⟨3315491, by rfl⟩ : syracuseStep 4420655 = 6630983) B6630983
theorem B2947103 : Blo 1963435 2947103 := bstep (se 1 (by rfl) ⟨2210327, by rfl⟩ : syracuseStep 2947103 = 4420655) B4420655
theorem B1964735 : Blo 1963435 1964735 := bstep (se 1 (by rfl) ⟨1473551, by rfl⟩ : syracuseStep 1964735 = 2947103) B2947103
theorem B2947109 : Blo 1963435 2947109 := bbase (se 4 (by rfl) ⟨276291, by rfl⟩ : syracuseStep 2947109 = 552583) (by norm_num)
theorem B1964739 : Blo 1963435 1964739 := bstep (se 1 (by rfl) ⟨1473554, by rfl⟩ : syracuseStep 1964739 = 2947109) B2947109
theorem B2486629 : Blo 1963435 2486629 := bbase (se 4 (by rfl) ⟨233121, by rfl⟩ : syracuseStep 2486629 = 466243) (by norm_num)
theorem B3315505 : Blo 1963435 3315505 := bstep (se 2 (by rfl) ⟨1243314, by rfl⟩ : syracuseStep 3315505 = 2486629) B2486629
theorem B4420673 : Blo 1963435 4420673 := bstep (se 2 (by rfl) ⟨1657752, by rfl⟩ : syracuseStep 4420673 = 3315505) B3315505
theorem B2947115 : Blo 1963435 2947115 := bstep (se 1 (by rfl) ⟨2210336, by rfl⟩ : syracuseStep 2947115 = 4420673) B4420673
theorem B1964743 : Blo 1963435 1964743 := bstep (se 1 (by rfl) ⟨1473557, by rfl⟩ : syracuseStep 1964743 = 2947115) B2947115
theorem B2210341 : Blo 1963435 2210341 := bbase (se 4 (by rfl) ⟨207219, by rfl⟩ : syracuseStep 2210341 = 414439) (by norm_num)
theorem B2947121 : Blo 1963435 2947121 := bstep (se 2 (by rfl) ⟨1105170, by rfl⟩ : syracuseStep 2947121 = 2210341) B2210341
theorem B1964747 : Blo 1963435 1964747 := bstep (se 1 (by rfl) ⟨1473560, by rfl⟩ : syracuseStep 1964747 = 2947121) B2947121
theorem B9441461 : Blo 1963435 9441461 := bbase (se 5 (by rfl) ⟨442568, by rfl⟩ : syracuseStep 9441461 = 885137) (by norm_num)
theorem B6294307 : Blo 1963435 6294307 := bstep (se 1 (by rfl) ⟨4720730, by rfl⟩ : syracuseStep 6294307 = 9441461) B9441461
theorem B8392409 : Blo 1963435 8392409 := bstep (se 2 (by rfl) ⟨3147153, by rfl⟩ : syracuseStep 8392409 = 6294307) B6294307
theorem B5594939 : Blo 1963435 5594939 := bstep (se 1 (by rfl) ⟨4196204, by rfl⟩ : syracuseStep 5594939 = 8392409) B8392409
theorem B3729959 : Blo 1963435 3729959 := bstep (se 1 (by rfl) ⟨2797469, by rfl⟩ : syracuseStep 3729959 = 5594939) B5594939
theorem B2486639 : Blo 1963435 2486639 := bstep (se 1 (by rfl) ⟨1864979, by rfl⟩ : syracuseStep 2486639 = 3729959) B3729959
theorem B6631037 : Blo 1963435 6631037 := bstep (se 3 (by rfl) ⟨1243319, by rfl⟩ : syracuseStep 6631037 = 2486639) B2486639
theorem B4420691 : Blo 1963435 4420691 := bstep (se 1 (by rfl) ⟨3315518, by rfl⟩ : syracuseStep 4420691 = 6631037) B6631037
theorem B2947127 : Blo 1963435 2947127 := bstep (se 1 (by rfl) ⟨2210345, by rfl⟩ : syracuseStep 2947127 = 4420691) B4420691
theorem B1964751 : Blo 1963435 1964751 := bstep (se 1 (by rfl) ⟨1473563, by rfl⟩ : syracuseStep 1964751 = 2947127) B2947127
theorem B2947133 : Blo 1963435 2947133 := bbase (se 3 (by rfl) ⟨552587, by rfl⟩ : syracuseStep 2947133 = 1105175) (by norm_num)
theorem B1964755 : Blo 1963435 1964755 := bstep (se 1 (by rfl) ⟨1473566, by rfl⟩ : syracuseStep 1964755 = 2947133) B2947133
theorem B4420709 : Blo 1963435 4420709 := bbase (se 4 (by rfl) ⟨414441, by rfl⟩ : syracuseStep 4420709 = 828883) (by norm_num)
theorem B2947139 : Blo 1963435 2947139 := bstep (se 1 (by rfl) ⟨2210354, by rfl⟩ : syracuseStep 2947139 = 4420709) B4420709
theorem B1964759 : Blo 1963435 1964759 := bstep (se 1 (by rfl) ⟨1473569, by rfl⟩ : syracuseStep 1964759 = 2947139) B2947139
theorem B4973309 : Blo 1963435 4973309 := bbase (se 3 (by rfl) ⟨932495, by rfl⟩ : syracuseStep 4973309 = 1864991) (by norm_num)
theorem B3315539 : Blo 1963435 3315539 := bstep (se 1 (by rfl) ⟨2486654, by rfl⟩ : syracuseStep 3315539 = 4973309) B4973309
theorem B2210359 : Blo 1963435 2210359 := bstep (se 1 (by rfl) ⟨1657769, by rfl⟩ : syracuseStep 2210359 = 3315539) B3315539
theorem B2947145 : Blo 1963435 2947145 := bstep (se 2 (by rfl) ⟨1105179, by rfl⟩ : syracuseStep 2947145 = 2210359) B2210359
theorem B1964763 : Blo 1963435 1964763 := bstep (se 1 (by rfl) ⟨1473572, by rfl⟩ : syracuseStep 1964763 = 2947145) B2947145
theorem B3729989 : Blo 1963435 3729989 := bbase (se 4 (by rfl) ⟨349686, by rfl⟩ : syracuseStep 3729989 = 699373) (by norm_num)
theorem B9946637 : Blo 1963435 9946637 := bstep (se 3 (by rfl) ⟨1864994, by rfl⟩ : syracuseStep 9946637 = 3729989) B3729989
theorem B6631091 : Blo 1963435 6631091 := bstep (se 1 (by rfl) ⟨4973318, by rfl⟩ : syracuseStep 6631091 = 9946637) B9946637
theorem B4420727 : Blo 1963435 4420727 := bstep (se 1 (by rfl) ⟨3315545, by rfl⟩ : syracuseStep 4420727 = 6631091) B6631091
theorem B2947151 : Blo 1963435 2947151 := bstep (se 1 (by rfl) ⟨2210363, by rfl⟩ : syracuseStep 2947151 = 4420727) B4420727
theorem B1964767 : Blo 1963435 1964767 := bstep (se 1 (by rfl) ⟨1473575, by rfl⟩ : syracuseStep 1964767 = 2947151) B2947151
theorem B2947157 : Blo 1963435 2947157 := bbase (se 8 (by rfl) ⟨17268, by rfl⟩ : syracuseStep 2947157 = 34537) (by norm_num)
theorem B1964771 : Blo 1963435 1964771 := bstep (se 1 (by rfl) ⟨1473578, by rfl⟩ : syracuseStep 1964771 = 2947157) B2947157
theorem B3028133 : Blo 1963435 3028133 := bbase (se 4 (by rfl) ⟨283887, by rfl⟩ : syracuseStep 3028133 = 567775) (by norm_num)
theorem B2018755 : Blo 1963435 2018755 := bstep (se 1 (by rfl) ⟨1514066, by rfl⟩ : syracuseStep 2018755 = 3028133) B3028133
theorem B2691673 : Blo 1963435 2691673 := bstep (se 2 (by rfl) ⟨1009377, by rfl⟩ : syracuseStep 2691673 = 2018755) B2018755
theorem B14355589 : Blo 1963435 14355589 := bstep (se 4 (by rfl) ⟨1345836, by rfl⟩ : syracuseStep 14355589 = 2691673) B2691673
theorem B19140785 : Blo 1963435 19140785 := bstep (se 2 (by rfl) ⟨7177794, by rfl⟩ : syracuseStep 19140785 = 14355589) B14355589
theorem B12760523 : Blo 1963435 12760523 := bstep (se 1 (by rfl) ⟨9570392, by rfl⟩ : syracuseStep 12760523 = 19140785) B19140785
theorem B8507015 : Blo 1963435 8507015 := bstep (se 1 (by rfl) ⟨6380261, by rfl⟩ : syracuseStep 8507015 = 12760523) B12760523
theorem B5671343 : Blo 1963435 5671343 := bstep (se 1 (by rfl) ⟨4253507, by rfl⟩ : syracuseStep 5671343 = 8507015) B8507015
theorem B15123581 : Blo 1963435 15123581 := bstep (se 3 (by rfl) ⟨2835671, by rfl⟩ : syracuseStep 15123581 = 5671343) B5671343
theorem B10082387 : Blo 1963435 10082387 := bstep (se 1 (by rfl) ⟨7561790, by rfl⟩ : syracuseStep 10082387 = 15123581) B15123581
theorem B6721591 : Blo 1963435 6721591 := bstep (se 1 (by rfl) ⟨5041193, by rfl⟩ : syracuseStep 6721591 = 10082387) B10082387
theorem B8962121 : Blo 1963435 8962121 := bstep (se 2 (by rfl) ⟨3360795, by rfl⟩ : syracuseStep 8962121 = 6721591) B6721591
theorem B23898989 : Blo 1963435 23898989 := bstep (se 3 (by rfl) ⟨4481060, by rfl⟩ : syracuseStep 23898989 = 8962121) B8962121
theorem B63730637 : Blo 1963435 63730637 := bstep (se 3 (by rfl) ⟨11949494, by rfl⟩ : syracuseStep 63730637 = 23898989) B23898989
theorem B42487091 : Blo 1963435 42487091 := bstep (se 1 (by rfl) ⟨31865318, by rfl⟩ : syracuseStep 42487091 = 63730637) B63730637
theorem B28324727 : Blo 1963435 28324727 := bstep (se 1 (by rfl) ⟨21243545, by rfl⟩ : syracuseStep 28324727 = 42487091) B42487091
theorem B18883151 : Blo 1963435 18883151 := bstep (se 1 (by rfl) ⟨14162363, by rfl⟩ : syracuseStep 18883151 = 28324727) B28324727
theorem B12588767 : Blo 1963435 12588767 := bstep (se 1 (by rfl) ⟨9441575, by rfl⟩ : syracuseStep 12588767 = 18883151) B18883151
theorem B8392511 : Blo 1963435 8392511 := bstep (se 1 (by rfl) ⟨6294383, by rfl⟩ : syracuseStep 8392511 = 12588767) B12588767
theorem B5595007 : Blo 1963435 5595007 := bstep (se 1 (by rfl) ⟨4196255, by rfl⟩ : syracuseStep 5595007 = 8392511) B8392511
theorem B7460009 : Blo 1963435 7460009 := bstep (se 2 (by rfl) ⟨2797503, by rfl⟩ : syracuseStep 7460009 = 5595007) B5595007
theorem B4973339 : Blo 1963435 4973339 := bstep (se 1 (by rfl) ⟨3730004, by rfl⟩ : syracuseStep 4973339 = 7460009) B7460009
theorem B3315559 : Blo 1963435 3315559 := bstep (se 1 (by rfl) ⟨2486669, by rfl⟩ : syracuseStep 3315559 = 4973339) B4973339
theorem B4420745 : Blo 1963435 4420745 := bstep (se 2 (by rfl) ⟨1657779, by rfl⟩ : syracuseStep 4420745 = 3315559) B3315559
theorem B2947163 : Blo 1963435 2947163 := bstep (se 1 (by rfl) ⟨2210372, by rfl⟩ : syracuseStep 2947163 = 4420745) B4420745
theorem B1964775 : Blo 1963435 1964775 := bstep (se 1 (by rfl) ⟨1473581, by rfl⟩ : syracuseStep 1964775 = 2947163) B2947163
theorem B2210377 : Blo 1963435 2210377 := bbase (se 2 (by rfl) ⟨828891, by rfl⟩ : syracuseStep 2210377 = 1657783) (by norm_num)
theorem B2947169 : Blo 1963435 2947169 := bstep (se 2 (by rfl) ⟨1105188, by rfl⟩ : syracuseStep 2947169 = 2210377) B2210377
theorem B1964779 : Blo 1963435 1964779 := bstep (se 1 (by rfl) ⟨1473584, by rfl⟩ : syracuseStep 1964779 = 2947169) B2947169
theorem B3540605 : Blo 1963435 3540605 := bbase (se 3 (by rfl) ⟨663863, by rfl⟩ : syracuseStep 3540605 = 1327727) (by norm_num)
theorem B9441613 : Blo 1963435 9441613 := bstep (se 3 (by rfl) ⟨1770302, by rfl⟩ : syracuseStep 9441613 = 3540605) B3540605
theorem B12588817 : Blo 1963435 12588817 := bstep (se 2 (by rfl) ⟨4720806, by rfl⟩ : syracuseStep 12588817 = 9441613) B9441613
theorem B16785089 : Blo 1963435 16785089 := bstep (se 2 (by rfl) ⟨6294408, by rfl⟩ : syracuseStep 16785089 = 12588817) B12588817
theorem B11190059 : Blo 1963435 11190059 := bstep (se 1 (by rfl) ⟨8392544, by rfl⟩ : syracuseStep 11190059 = 16785089) B16785089
theorem B7460039 : Blo 1963435 7460039 := bstep (se 1 (by rfl) ⟨5595029, by rfl⟩ : syracuseStep 7460039 = 11190059) B11190059
theorem B4973359 : Blo 1963435 4973359 := bstep (se 1 (by rfl) ⟨3730019, by rfl⟩ : syracuseStep 4973359 = 7460039) B7460039
theorem B6631145 : Blo 1963435 6631145 := bstep (se 2 (by rfl) ⟨2486679, by rfl⟩ : syracuseStep 6631145 = 4973359) B4973359
theorem B4420763 : Blo 1963435 4420763 := bstep (se 1 (by rfl) ⟨3315572, by rfl⟩ : syracuseStep 4420763 = 6631145) B6631145
theorem B2947175 : Blo 1963435 2947175 := bstep (se 1 (by rfl) ⟨2210381, by rfl⟩ : syracuseStep 2947175 = 4420763) B4420763
theorem B1964783 : Blo 1963435 1964783 := bstep (se 1 (by rfl) ⟨1473587, by rfl⟩ : syracuseStep 1964783 = 2947175) B2947175
theorem B2947181 : Blo 1963435 2947181 := bbase (se 3 (by rfl) ⟨552596, by rfl⟩ : syracuseStep 2947181 = 1105193) (by norm_num)
theorem B1964787 : Blo 1963435 1964787 := bstep (se 1 (by rfl) ⟨1473590, by rfl⟩ : syracuseStep 1964787 = 2947181) B2947181
theorem B4420781 : Blo 1963435 4420781 := bbase (se 3 (by rfl) ⟨828896, by rfl⟩ : syracuseStep 4420781 = 1657793) (by norm_num)
theorem B2947187 : Blo 1963435 2947187 := bstep (se 1 (by rfl) ⟨2210390, by rfl⟩ : syracuseStep 2947187 = 4420781) B4420781
theorem B1964791 : Blo 1963435 1964791 := bstep (se 1 (by rfl) ⟨1473593, by rfl⟩ : syracuseStep 1964791 = 2947187) B2947187
theorem B4720837 : Blo 1963435 4720837 := bbase (se 4 (by rfl) ⟨442578, by rfl⟩ : syracuseStep 4720837 = 885157) (by norm_num)
theorem B6294449 : Blo 1963435 6294449 := bstep (se 2 (by rfl) ⟨2360418, by rfl⟩ : syracuseStep 6294449 = 4720837) B4720837
theorem B4196299 : Blo 1963435 4196299 := bstep (se 1 (by rfl) ⟨3147224, by rfl⟩ : syracuseStep 4196299 = 6294449) B6294449
theorem B5595065 : Blo 1963435 5595065 := bstep (se 2 (by rfl) ⟨2098149, by rfl⟩ : syracuseStep 5595065 = 4196299) B4196299
theorem B3730043 : Blo 1963435 3730043 := bstep (se 1 (by rfl) ⟨2797532, by rfl⟩ : syracuseStep 3730043 = 5595065) B5595065
theorem B2486695 : Blo 1963435 2486695 := bstep (se 1 (by rfl) ⟨1865021, by rfl⟩ : syracuseStep 2486695 = 3730043) B3730043
theorem B3315593 : Blo 1963435 3315593 := bstep (se 2 (by rfl) ⟨1243347, by rfl⟩ : syracuseStep 3315593 = 2486695) B2486695
theorem B2210395 : Blo 1963435 2210395 := bstep (se 1 (by rfl) ⟨1657796, by rfl⟩ : syracuseStep 2210395 = 3315593) B3315593
theorem B2947193 : Blo 1963435 2947193 := bstep (se 2 (by rfl) ⟨1105197, by rfl⟩ : syracuseStep 2947193 = 2210395) B2210395
theorem B1964795 : Blo 1963435 1964795 := bstep (se 1 (by rfl) ⟨1473596, by rfl⟩ : syracuseStep 1964795 = 2947193) B2947193
theorem B3983213 : Blo 1963435 3983213 := bbase (se 3 (by rfl) ⟨746852, by rfl⟩ : syracuseStep 3983213 = 1493705) (by norm_num)
theorem B10621901 : Blo 1963435 10621901 := bstep (se 3 (by rfl) ⟨1991606, by rfl⟩ : syracuseStep 10621901 = 3983213) B3983213
theorem B7081267 : Blo 1963435 7081267 := bstep (se 1 (by rfl) ⟨5310950, by rfl⟩ : syracuseStep 7081267 = 10621901) B10621901
theorem B9441689 : Blo 1963435 9441689 := bstep (se 2 (by rfl) ⟨3540633, by rfl⟩ : syracuseStep 9441689 = 7081267) B7081267
theorem B25177837 : Blo 1963435 25177837 := bstep (se 3 (by rfl) ⟨4720844, by rfl⟩ : syracuseStep 25177837 = 9441689) B9441689
theorem B33570449 : Blo 1963435 33570449 := bstep (se 2 (by rfl) ⟨12588918, by rfl⟩ : syracuseStep 33570449 = 25177837) B25177837
theorem B22380299 : Blo 1963435 22380299 := bstep (se 1 (by rfl) ⟨16785224, by rfl⟩ : syracuseStep 22380299 = 33570449) B33570449
theorem B14920199 : Blo 1963435 14920199 := bstep (se 1 (by rfl) ⟨11190149, by rfl⟩ : syracuseStep 14920199 = 22380299) B22380299
theorem B9946799 : Blo 1963435 9946799 := bstep (se 1 (by rfl) ⟨7460099, by rfl⟩ : syracuseStep 9946799 = 14920199) B14920199
theorem B6631199 : Blo 1963435 6631199 := bstep (se 1 (by rfl) ⟨4973399, by rfl⟩ : syracuseStep 6631199 = 9946799) B9946799
theorem B4420799 : Blo 1963435 4420799 := bstep (se 1 (by rfl) ⟨3315599, by rfl⟩ : syracuseStep 4420799 = 6631199) B6631199
theorem B2947199 : Blo 1963435 2947199 := bstep (se 1 (by rfl) ⟨2210399, by rfl⟩ : syracuseStep 2947199 = 4420799) B4420799
theorem B1964799 : Blo 1963435 1964799 := bstep (se 1 (by rfl) ⟨1473599, by rfl⟩ : syracuseStep 1964799 = 2947199) B2947199
theorem B2947205 : Blo 1963435 2947205 := bbase (se 4 (by rfl) ⟨276300, by rfl⟩ : syracuseStep 2947205 = 552601) (by norm_num)
theorem B1964803 : Blo 1963435 1964803 := bstep (se 1 (by rfl) ⟨1473602, by rfl⟩ : syracuseStep 1964803 = 2947205) B2947205
theorem B3315613 : Blo 1963435 3315613 := bbase (se 3 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 3315613 = 1243355) (by norm_num)
theorem B4420817 : Blo 1963435 4420817 := bstep (se 2 (by rfl) ⟨1657806, by rfl⟩ : syracuseStep 4420817 = 3315613) B3315613
theorem B2947211 : Blo 1963435 2947211 := bstep (se 1 (by rfl) ⟨2210408, by rfl⟩ : syracuseStep 2947211 = 4420817) B4420817
theorem B1964807 : Blo 1963435 1964807 := bstep (se 1 (by rfl) ⟨1473605, by rfl⟩ : syracuseStep 1964807 = 2947211) B2947211
theorem B2210413 : Blo 1963435 2210413 := bbase (se 3 (by rfl) ⟨414452, by rfl⟩ : syracuseStep 2210413 = 828905) (by norm_num)
theorem B2947217 : Blo 1963435 2947217 := bstep (se 2 (by rfl) ⟨1105206, by rfl⟩ : syracuseStep 2947217 = 2210413) B2210413
theorem B1964811 : Blo 1963435 1964811 := bstep (se 1 (by rfl) ⟨1473608, by rfl⟩ : syracuseStep 1964811 = 2947217) B2947217
theorem B6631253 : Blo 1963435 6631253 := bbase (se 9 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 6631253 = 38855) (by norm_num)
theorem B4420835 : Blo 1963435 4420835 := bstep (se 1 (by rfl) ⟨3315626, by rfl⟩ : syracuseStep 4420835 = 6631253) B6631253
theorem B2947223 : Blo 1963435 2947223 := bstep (se 1 (by rfl) ⟨2210417, by rfl⟩ : syracuseStep 2947223 = 4420835) B4420835
theorem B1964815 : Blo 1963435 1964815 := bstep (se 1 (by rfl) ⟨1473611, by rfl⟩ : syracuseStep 1964815 = 2947223) B2947223
theorem B2947229 : Blo 1963435 2947229 := bbase (se 3 (by rfl) ⟨552605, by rfl⟩ : syracuseStep 2947229 = 1105211) (by norm_num)
theorem B1964819 : Blo 1963435 1964819 := bstep (se 1 (by rfl) ⟨1473614, by rfl⟩ : syracuseStep 1964819 = 2947229) B2947229
theorem B4420853 : Blo 1963435 4420853 := bbase (se 5 (by rfl) ⟨207227, by rfl⟩ : syracuseStep 4420853 = 414455) (by norm_num)
theorem B2947235 : Blo 1963435 2947235 := bstep (se 1 (by rfl) ⟨2210426, by rfl⟩ : syracuseStep 2947235 = 4420853) B4420853
theorem B1964823 : Blo 1963435 1964823 := bstep (se 1 (by rfl) ⟨1473617, by rfl⟩ : syracuseStep 1964823 = 2947235) B2947235
theorem B2987453 : Blo 1963435 2987453 := bbase (se 3 (by rfl) ⟨560147, by rfl⟩ : syracuseStep 2987453 = 1120295) (by norm_num)
theorem B7966541 : Blo 1963435 7966541 := bstep (se 3 (by rfl) ⟨1493726, by rfl⟩ : syracuseStep 7966541 = 2987453) B2987453
theorem B5311027 : Blo 1963435 5311027 := bstep (se 1 (by rfl) ⟨3983270, by rfl⟩ : syracuseStep 5311027 = 7966541) B7966541
theorem B28325477 : Blo 1963435 28325477 := bstep (se 4 (by rfl) ⟨2655513, by rfl⟩ : syracuseStep 28325477 = 5311027) B5311027
theorem B18883651 : Blo 1963435 18883651 := bstep (se 1 (by rfl) ⟨14162738, by rfl⟩ : syracuseStep 18883651 = 28325477) B28325477
theorem B25178201 : Blo 1963435 25178201 := bstep (se 2 (by rfl) ⟨9441825, by rfl⟩ : syracuseStep 25178201 = 18883651) B18883651
theorem B16785467 : Blo 1963435 16785467 := bstep (se 1 (by rfl) ⟨12589100, by rfl⟩ : syracuseStep 16785467 = 25178201) B25178201
theorem B11190311 : Blo 1963435 11190311 := bstep (se 1 (by rfl) ⟨8392733, by rfl⟩ : syracuseStep 11190311 = 16785467) B16785467
theorem B7460207 : Blo 1963435 7460207 := bstep (se 1 (by rfl) ⟨5595155, by rfl⟩ : syracuseStep 7460207 = 11190311) B11190311
theorem B4973471 : Blo 1963435 4973471 := bstep (se 1 (by rfl) ⟨3730103, by rfl⟩ : syracuseStep 4973471 = 7460207) B7460207
theorem B3315647 : Blo 1963435 3315647 := bstep (se 1 (by rfl) ⟨2486735, by rfl⟩ : syracuseStep 3315647 = 4973471) B4973471
theorem B2210431 : Blo 1963435 2210431 := bstep (se 1 (by rfl) ⟨1657823, by rfl⟩ : syracuseStep 2210431 = 3315647) B3315647
theorem B2947241 : Blo 1963435 2947241 := bstep (se 2 (by rfl) ⟨1105215, by rfl⟩ : syracuseStep 2947241 = 2210431) B2210431
theorem B1964827 : Blo 1963435 1964827 := bstep (se 1 (by rfl) ⟨1473620, by rfl⟩ : syracuseStep 1964827 = 2947241) B2947241
theorem B9441845 : Blo 1963435 9441845 := bbase (se 5 (by rfl) ⟨442586, by rfl⟩ : syracuseStep 9441845 = 885173) (by norm_num)
theorem B6294563 : Blo 1963435 6294563 := bstep (se 1 (by rfl) ⟨4720922, by rfl⟩ : syracuseStep 6294563 = 9441845) B9441845
theorem B4196375 : Blo 1963435 4196375 := bstep (se 1 (by rfl) ⟨3147281, by rfl⟩ : syracuseStep 4196375 = 6294563) B6294563
theorem B2797583 : Blo 1963435 2797583 := bstep (se 1 (by rfl) ⟨2098187, by rfl⟩ : syracuseStep 2797583 = 4196375) B4196375
theorem B7460221 : Blo 1963435 7460221 := bstep (se 3 (by rfl) ⟨1398791, by rfl⟩ : syracuseStep 7460221 = 2797583) B2797583
theorem B9946961 : Blo 1963435 9946961 := bstep (se 2 (by rfl) ⟨3730110, by rfl⟩ : syracuseStep 9946961 = 7460221) B7460221
theorem B6631307 : Blo 1963435 6631307 := bstep (se 1 (by rfl) ⟨4973480, by rfl⟩ : syracuseStep 6631307 = 9946961) B9946961
theorem B4420871 : Blo 1963435 4420871 := bstep (se 1 (by rfl) ⟨3315653, by rfl⟩ : syracuseStep 4420871 = 6631307) B6631307
theorem B2947247 : Blo 1963435 2947247 := bstep (se 1 (by rfl) ⟨2210435, by rfl⟩ : syracuseStep 2947247 = 4420871) B4420871
theorem B1964831 : Blo 1963435 1964831 := bstep (se 1 (by rfl) ⟨1473623, by rfl⟩ : syracuseStep 1964831 = 2947247) B2947247
theorem B2947253 : Blo 1963435 2947253 := bbase (se 5 (by rfl) ⟨138152, by rfl⟩ : syracuseStep 2947253 = 276305) (by norm_num)
theorem B1964835 : Blo 1963435 1964835 := bstep (se 1 (by rfl) ⟨1473626, by rfl⟩ : syracuseStep 1964835 = 2947253) B2947253
theorem B4973501 : Blo 1963435 4973501 := bbase (se 3 (by rfl) ⟨932531, by rfl⟩ : syracuseStep 4973501 = 1865063) (by norm_num)
theorem B3315667 : Blo 1963435 3315667 := bstep (se 1 (by rfl) ⟨2486750, by rfl⟩ : syracuseStep 3315667 = 4973501) B4973501
theorem B4420889 : Blo 1963435 4420889 := bstep (se 2 (by rfl) ⟨1657833, by rfl⟩ : syracuseStep 4420889 = 3315667) B3315667
theorem B2947259 : Blo 1963435 2947259 := bstep (se 1 (by rfl) ⟨2210444, by rfl⟩ : syracuseStep 2947259 = 4420889) B4420889
theorem B1964839 : Blo 1963435 1964839 := bstep (se 1 (by rfl) ⟨1473629, by rfl⟩ : syracuseStep 1964839 = 2947259) B2947259
theorem B2210449 : Blo 1963435 2210449 := bbase (se 2 (by rfl) ⟨828918, by rfl⟩ : syracuseStep 2210449 = 1657837) (by norm_num)
theorem B2947265 : Blo 1963435 2947265 := bstep (se 2 (by rfl) ⟨1105224, by rfl⟩ : syracuseStep 2947265 = 2210449) B2210449
theorem B1964843 : Blo 1963435 1964843 := bstep (se 1 (by rfl) ⟨1473632, by rfl⟩ : syracuseStep 1964843 = 2947265) B2947265
theorem B3730141 : Blo 1963435 3730141 := bbase (se 3 (by rfl) ⟨699401, by rfl⟩ : syracuseStep 3730141 = 1398803) (by norm_num)
theorem B4973521 : Blo 1963435 4973521 := bstep (se 2 (by rfl) ⟨1865070, by rfl⟩ : syracuseStep 4973521 = 3730141) B3730141
theorem B6631361 : Blo 1963435 6631361 := bstep (se 2 (by rfl) ⟨2486760, by rfl⟩ : syracuseStep 6631361 = 4973521) B4973521
theorem B4420907 : Blo 1963435 4420907 := bstep (se 1 (by rfl) ⟨3315680, by rfl⟩ : syracuseStep 4420907 = 6631361) B6631361
theorem B2947271 : Blo 1963435 2947271 := bstep (se 1 (by rfl) ⟨2210453, by rfl⟩ : syracuseStep 2947271 = 4420907) B4420907
theorem B1964847 : Blo 1963435 1964847 := bstep (se 1 (by rfl) ⟨1473635, by rfl⟩ : syracuseStep 1964847 = 2947271) B2947271
theorem B2947277 : Blo 1963435 2947277 := bbase (se 3 (by rfl) ⟨552614, by rfl⟩ : syracuseStep 2947277 = 1105229) (by norm_num)
theorem B1964851 : Blo 1963435 1964851 := bstep (se 1 (by rfl) ⟨1473638, by rfl⟩ : syracuseStep 1964851 = 2947277) B2947277
theorem B4420925 : Blo 1963435 4420925 := bbase (se 3 (by rfl) ⟨828923, by rfl⟩ : syracuseStep 4420925 = 1657847) (by norm_num)
theorem B2947283 : Blo 1963435 2947283 := bstep (se 1 (by rfl) ⟨2210462, by rfl⟩ : syracuseStep 2947283 = 4420925) B4420925
theorem B1964855 : Blo 1963435 1964855 := bstep (se 1 (by rfl) ⟨1473641, by rfl⟩ : syracuseStep 1964855 = 2947283) B2947283
theorem B3315701 : Blo 1963435 3315701 := bbase (se 5 (by rfl) ⟨155423, by rfl⟩ : syracuseStep 3315701 = 310847) (by norm_num)
theorem B2210467 : Blo 1963435 2210467 := bstep (se 1 (by rfl) ⟨1657850, by rfl⟩ : syracuseStep 2210467 = 3315701) B3315701
theorem B2947289 : Blo 1963435 2947289 := bstep (se 2 (by rfl) ⟨1105233, by rfl⟩ : syracuseStep 2947289 = 2210467) B2210467
theorem B1964859 : Blo 1963435 1964859 := bstep (se 1 (by rfl) ⟨1473644, by rfl⟩ : syracuseStep 1964859 = 2947289) B2947289
theorem B2126849 : Blo 1963435 2126849 := bbase (se 2 (by rfl) ⟨797568, by rfl⟩ : syracuseStep 2126849 = 1595137) (by norm_num)
theorem B22686389 : Blo 1963435 22686389 := bstep (se 5 (by rfl) ⟨1063424, by rfl⟩ : syracuseStep 22686389 = 2126849) B2126849
theorem B15124259 : Blo 1963435 15124259 := bstep (se 1 (by rfl) ⟨11343194, by rfl⟩ : syracuseStep 15124259 = 22686389) B22686389
theorem B40331357 : Blo 1963435 40331357 := bstep (se 3 (by rfl) ⟨7562129, by rfl⟩ : syracuseStep 40331357 = 15124259) B15124259
theorem B26887571 : Blo 1963435 26887571 := bstep (se 1 (by rfl) ⟨20165678, by rfl⟩ : syracuseStep 26887571 = 40331357) B40331357
theorem B17925047 : Blo 1963435 17925047 := bstep (se 1 (by rfl) ⟨13443785, by rfl⟩ : syracuseStep 17925047 = 26887571) B26887571
theorem B11950031 : Blo 1963435 11950031 := bstep (se 1 (by rfl) ⟨8962523, by rfl⟩ : syracuseStep 11950031 = 17925047) B17925047
theorem B7966687 : Blo 1963435 7966687 := bstep (se 1 (by rfl) ⟨5975015, by rfl⟩ : syracuseStep 7966687 = 11950031) B11950031
theorem B10622249 : Blo 1963435 10622249 := bstep (se 2 (by rfl) ⟨3983343, by rfl⟩ : syracuseStep 10622249 = 7966687) B7966687
theorem B7081499 : Blo 1963435 7081499 := bstep (se 1 (by rfl) ⟨5311124, by rfl⟩ : syracuseStep 7081499 = 10622249) B10622249
theorem B4720999 : Blo 1963435 4720999 := bstep (se 1 (by rfl) ⟨3540749, by rfl⟩ : syracuseStep 4720999 = 7081499) B7081499
theorem B6294665 : Blo 1963435 6294665 := bstep (se 2 (by rfl) ⟨2360499, by rfl⟩ : syracuseStep 6294665 = 4720999) B4720999
theorem B4196443 : Blo 1963435 4196443 := bstep (se 1 (by rfl) ⟨3147332, by rfl⟩ : syracuseStep 4196443 = 6294665) B6294665
theorem B5595257 : Blo 1963435 5595257 := bstep (se 2 (by rfl) ⟨2098221, by rfl⟩ : syracuseStep 5595257 = 4196443) B4196443
theorem B14920685 : Blo 1963435 14920685 := bstep (se 3 (by rfl) ⟨2797628, by rfl⟩ : syracuseStep 14920685 = 5595257) B5595257
theorem B9947123 : Blo 1963435 9947123 := bstep (se 1 (by rfl) ⟨7460342, by rfl⟩ : syracuseStep 9947123 = 14920685) B14920685
theorem B6631415 : Blo 1963435 6631415 := bstep (se 1 (by rfl) ⟨4973561, by rfl⟩ : syracuseStep 6631415 = 9947123) B9947123
theorem B4420943 : Blo 1963435 4420943 := bstep (se 1 (by rfl) ⟨3315707, by rfl⟩ : syracuseStep 4420943 = 6631415) B6631415
theorem B2947295 : Blo 1963435 2947295 := bstep (se 1 (by rfl) ⟨2210471, by rfl⟩ : syracuseStep 2947295 = 4420943) B4420943
theorem B1964863 : Blo 1963435 1964863 := bstep (se 1 (by rfl) ⟨1473647, by rfl⟩ : syracuseStep 1964863 = 2947295) B2947295
theorem B2947301 : Blo 1963435 2947301 := bbase (se 4 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 2947301 = 552619) (by norm_num)
theorem B1964867 : Blo 1963435 1964867 := bstep (se 1 (by rfl) ⟨1473650, by rfl⟩ : syracuseStep 1964867 = 2947301) B2947301
theorem B4196461 : Blo 1963435 4196461 := bbase (se 3 (by rfl) ⟨786836, by rfl⟩ : syracuseStep 4196461 = 1573673) (by norm_num)
theorem B5595281 : Blo 1963435 5595281 := bstep (se 2 (by rfl) ⟨2098230, by rfl⟩ : syracuseStep 5595281 = 4196461) B4196461
theorem B3730187 : Blo 1963435 3730187 := bstep (se 1 (by rfl) ⟨2797640, by rfl⟩ : syracuseStep 3730187 = 5595281) B5595281
theorem B2486791 : Blo 1963435 2486791 := bstep (se 1 (by rfl) ⟨1865093, by rfl⟩ : syracuseStep 2486791 = 3730187) B3730187
theorem B3315721 : Blo 1963435 3315721 := bstep (se 2 (by rfl) ⟨1243395, by rfl⟩ : syracuseStep 3315721 = 2486791) B2486791
theorem B4420961 : Blo 1963435 4420961 := bstep (se 2 (by rfl) ⟨1657860, by rfl⟩ : syracuseStep 4420961 = 3315721) B3315721
theorem B2947307 : Blo 1963435 2947307 := bstep (se 1 (by rfl) ⟨2210480, by rfl⟩ : syracuseStep 2947307 = 4420961) B4420961
theorem B1964871 : Blo 1963435 1964871 := bstep (se 1 (by rfl) ⟨1473653, by rfl⟩ : syracuseStep 1964871 = 2947307) B2947307
theorem B2210485 : Blo 1963435 2210485 := bbase (se 5 (by rfl) ⟨103616, by rfl⟩ : syracuseStep 2210485 = 207233) (by norm_num)
theorem B2947313 : Blo 1963435 2947313 := bstep (se 2 (by rfl) ⟨1105242, by rfl⟩ : syracuseStep 2947313 = 2210485) B2210485
theorem B1964875 : Blo 1963435 1964875 := bstep (se 1 (by rfl) ⟨1473656, by rfl⟩ : syracuseStep 1964875 = 2947313) B2947313
theorem B2486801 : Blo 1963435 2486801 := bbase (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) (by norm_num)
theorem B6631469 : Blo 1963435 6631469 := bstep (se 3 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 6631469 = 2486801) B2486801
theorem B4420979 : Blo 1963435 4420979 := bstep (se 1 (by rfl) ⟨3315734, by rfl⟩ : syracuseStep 4420979 = 6631469) B6631469
theorem B2947319 : Blo 1963435 2947319 := bstep (se 1 (by rfl) ⟨2210489, by rfl⟩ : syracuseStep 2947319 = 4420979) B4420979
theorem B1964879 : Blo 1963435 1964879 := bstep (se 1 (by rfl) ⟨1473659, by rfl⟩ : syracuseStep 1964879 = 2947319) B2947319
theorem B2947325 : Blo 1963435 2947325 := bbase (se 3 (by rfl) ⟨552623, by rfl⟩ : syracuseStep 2947325 = 1105247) (by norm_num)
theorem B1964883 : Blo 1963435 1964883 := bstep (se 1 (by rfl) ⟨1473662, by rfl⟩ : syracuseStep 1964883 = 2947325) B2947325
theorem B4420997 : Blo 1963435 4420997 := bbase (se 4 (by rfl) ⟨414468, by rfl⟩ : syracuseStep 4420997 = 828937) (by norm_num)
theorem B2947331 : Blo 1963435 2947331 := bstep (se 1 (by rfl) ⟨2210498, by rfl⟩ : syracuseStep 2947331 = 4420997) B4420997
theorem B1964887 : Blo 1963435 1964887 := bstep (se 1 (by rfl) ⟨1473665, by rfl⟩ : syracuseStep 1964887 = 2947331) B2947331
theorem B2797669 : Blo 1963435 2797669 := bbase (se 4 (by rfl) ⟨262281, by rfl⟩ : syracuseStep 2797669 = 524563) (by norm_num)
theorem B3730225 : Blo 1963435 3730225 := bstep (se 2 (by rfl) ⟨1398834, by rfl⟩ : syracuseStep 3730225 = 2797669) B2797669
theorem B4973633 : Blo 1963435 4973633 := bstep (se 2 (by rfl) ⟨1865112, by rfl⟩ : syracuseStep 4973633 = 3730225) B3730225
theorem B3315755 : Blo 1963435 3315755 := bstep (se 1 (by rfl) ⟨2486816, by rfl⟩ : syracuseStep 3315755 = 4973633) B4973633
theorem B2210503 : Blo 1963435 2210503 := bstep (se 1 (by rfl) ⟨1657877, by rfl⟩ : syracuseStep 2210503 = 3315755) B3315755
theorem B2947337 : Blo 1963435 2947337 := bstep (se 2 (by rfl) ⟨1105251, by rfl⟩ : syracuseStep 2947337 = 2210503) B2210503
theorem B1964891 : Blo 1963435 1964891 := bstep (se 1 (by rfl) ⟨1473668, by rfl⟩ : syracuseStep 1964891 = 2947337) B2947337
theorem B9947285 : Blo 1963435 9947285 := bbase (se 6 (by rfl) ⟨233139, by rfl⟩ : syracuseStep 9947285 = 466279) (by norm_num)
theorem B6631523 : Blo 1963435 6631523 := bstep (se 1 (by rfl) ⟨4973642, by rfl⟩ : syracuseStep 6631523 = 9947285) B9947285
theorem B4421015 : Blo 1963435 4421015 := bstep (se 1 (by rfl) ⟨3315761, by rfl⟩ : syracuseStep 4421015 = 6631523) B6631523
theorem B2947343 : Blo 1963435 2947343 := bstep (se 1 (by rfl) ⟨2210507, by rfl⟩ : syracuseStep 2947343 = 4421015) B4421015
theorem B1964895 : Blo 1963435 1964895 := bstep (se 1 (by rfl) ⟨1473671, by rfl⟩ : syracuseStep 1964895 = 2947343) B2947343
theorem B2947349 : Blo 1963435 2947349 := bbase (se 6 (by rfl) ⟨69078, by rfl⟩ : syracuseStep 2947349 = 138157) (by norm_num)
theorem B1964899 : Blo 1963435 1964899 := bstep (se 1 (by rfl) ⟨1473674, by rfl⟩ : syracuseStep 1964899 = 2947349) B2947349
theorem B2126893 : Blo 1963435 2126893 := bbase (se 3 (by rfl) ⟨398792, by rfl⟩ : syracuseStep 2126893 = 797585) (by norm_num)
theorem B2835857 : Blo 1963435 2835857 := bstep (se 2 (by rfl) ⟨1063446, by rfl⟩ : syracuseStep 2835857 = 2126893) B2126893
theorem B7562285 : Blo 1963435 7562285 := bstep (se 3 (by rfl) ⟨1417928, by rfl⟩ : syracuseStep 7562285 = 2835857) B2835857
theorem B5041523 : Blo 1963435 5041523 := bstep (se 1 (by rfl) ⟨3781142, by rfl⟩ : syracuseStep 5041523 = 7562285) B7562285
theorem B3361015 : Blo 1963435 3361015 := bstep (se 1 (by rfl) ⟨2520761, by rfl⟩ : syracuseStep 3361015 = 5041523) B5041523
theorem B4481353 : Blo 1963435 4481353 := bstep (se 2 (by rfl) ⟨1680507, by rfl⟩ : syracuseStep 4481353 = 3361015) B3361015
theorem B5975137 : Blo 1963435 5975137 := bstep (se 2 (by rfl) ⟨2240676, by rfl⟩ : syracuseStep 5975137 = 4481353) B4481353
theorem B7966849 : Blo 1963435 7966849 := bstep (se 2 (by rfl) ⟨2987568, by rfl⟩ : syracuseStep 7966849 = 5975137) B5975137
theorem B10622465 : Blo 1963435 10622465 := bstep (se 2 (by rfl) ⟨3983424, by rfl⟩ : syracuseStep 10622465 = 7966849) B7966849
theorem B7081643 : Blo 1963435 7081643 := bstep (se 1 (by rfl) ⟨5311232, by rfl⟩ : syracuseStep 7081643 = 10622465) B10622465
theorem B4721095 : Blo 1963435 4721095 := bstep (se 1 (by rfl) ⟨3540821, by rfl⟩ : syracuseStep 4721095 = 7081643) B7081643
theorem B25179173 : Blo 1963435 25179173 := bstep (se 4 (by rfl) ⟨2360547, by rfl⟩ : syracuseStep 25179173 = 4721095) B4721095
theorem B16786115 : Blo 1963435 16786115 := bstep (se 1 (by rfl) ⟨12589586, by rfl⟩ : syracuseStep 16786115 = 25179173) B25179173
theorem B11190743 : Blo 1963435 11190743 := bstep (se 1 (by rfl) ⟨8393057, by rfl⟩ : syracuseStep 11190743 = 16786115) B16786115
theorem B7460495 : Blo 1963435 7460495 := bstep (se 1 (by rfl) ⟨5595371, by rfl⟩ : syracuseStep 7460495 = 11190743) B11190743
theorem B4973663 : Blo 1963435 4973663 := bstep (se 1 (by rfl) ⟨3730247, by rfl⟩ : syracuseStep 4973663 = 7460495) B7460495
theorem B3315775 : Blo 1963435 3315775 := bstep (se 1 (by rfl) ⟨2486831, by rfl⟩ : syracuseStep 3315775 = 4973663) B4973663
theorem B4421033 : Blo 1963435 4421033 := bstep (se 2 (by rfl) ⟨1657887, by rfl⟩ : syracuseStep 4421033 = 3315775) B3315775
theorem B2947355 : Blo 1963435 2947355 := bstep (se 1 (by rfl) ⟨2210516, by rfl⟩ : syracuseStep 2947355 = 4421033) B4421033
theorem B1964903 : Blo 1963435 1964903 := bstep (se 1 (by rfl) ⟨1473677, by rfl⟩ : syracuseStep 1964903 = 2947355) B2947355
theorem B2210521 : Blo 1963435 2210521 := bbase (se 2 (by rfl) ⟨828945, by rfl⟩ : syracuseStep 2210521 = 1657891) (by norm_num)
theorem B2947361 : Blo 1963435 2947361 := bstep (se 2 (by rfl) ⟨1105260, by rfl⟩ : syracuseStep 2947361 = 2210521) B2210521
theorem B1964907 : Blo 1963435 1964907 := bstep (se 1 (by rfl) ⟨1473680, by rfl⟩ : syracuseStep 1964907 = 2947361) B2947361
theorem B2098273 : Blo 1963435 2098273 := bbase (se 2 (by rfl) ⟨786852, by rfl⟩ : syracuseStep 2098273 = 1573705) (by norm_num)
theorem B2797697 : Blo 1963435 2797697 := bstep (se 2 (by rfl) ⟨1049136, by rfl⟩ : syracuseStep 2797697 = 2098273) B2098273
theorem B7460525 : Blo 1963435 7460525 := bstep (se 3 (by rfl) ⟨1398848, by rfl⟩ : syracuseStep 7460525 = 2797697) B2797697
theorem B4973683 : Blo 1963435 4973683 := bstep (se 1 (by rfl) ⟨3730262, by rfl⟩ : syracuseStep 4973683 = 7460525) B7460525
theorem B6631577 : Blo 1963435 6631577 := bstep (se 2 (by rfl) ⟨2486841, by rfl⟩ : syracuseStep 6631577 = 4973683) B4973683
theorem B4421051 : Blo 1963435 4421051 := bstep (se 1 (by rfl) ⟨3315788, by rfl⟩ : syracuseStep 4421051 = 6631577) B6631577
theorem B2947367 : Blo 1963435 2947367 := bstep (se 1 (by rfl) ⟨2210525, by rfl⟩ : syracuseStep 2947367 = 4421051) B4421051
theorem B1964911 : Blo 1963435 1964911 := bstep (se 1 (by rfl) ⟨1473683, by rfl⟩ : syracuseStep 1964911 = 2947367) B2947367
theorem B2947373 : Blo 1963435 2947373 := bbase (se 3 (by rfl) ⟨552632, by rfl⟩ : syracuseStep 2947373 = 1105265) (by norm_num)
theorem B1964915 : Blo 1963435 1964915 := bstep (se 1 (by rfl) ⟨1473686, by rfl⟩ : syracuseStep 1964915 = 2947373) B2947373
theorem B4421069 : Blo 1963435 4421069 := bbase (se 3 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 4421069 = 1657901) (by norm_num)
theorem B2947379 : Blo 1963435 2947379 := bstep (se 1 (by rfl) ⟨2210534, by rfl⟩ : syracuseStep 2947379 = 4421069) B4421069
theorem B1964919 : Blo 1963435 1964919 := bstep (se 1 (by rfl) ⟨1473689, by rfl⟩ : syracuseStep 1964919 = 2947379) B2947379
theorem B2486857 : Blo 1963435 2486857 := bbase (se 2 (by rfl) ⟨932571, by rfl⟩ : syracuseStep 2486857 = 1865143) (by norm_num)
theorem B3315809 : Blo 1963435 3315809 := bstep (se 2 (by rfl) ⟨1243428, by rfl⟩ : syracuseStep 3315809 = 2486857) B2486857
theorem B2210539 : Blo 1963435 2210539 := bstep (se 1 (by rfl) ⟨1657904, by rfl⟩ : syracuseStep 2210539 = 3315809) B3315809
theorem B2947385 : Blo 1963435 2947385 := bstep (se 2 (by rfl) ⟨1105269, by rfl⟩ : syracuseStep 2947385 = 2210539) B2210539
theorem B1964923 : Blo 1963435 1964923 := bstep (se 1 (by rfl) ⟨1473692, by rfl⟩ : syracuseStep 1964923 = 2947385) B2947385
theorem B10220741 : Blo 1963435 10220741 := bbase (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) (by norm_num)
theorem B6813827 : Blo 1963435 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B4542551 : Blo 1963435 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B3028367 : Blo 1963435 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B8075645 : Blo 1963435 8075645 := bstep (se 3 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 8075645 = 3028367) B3028367
theorem B5383763 : Blo 1963435 5383763 := bstep (se 1 (by rfl) ⟨4037822, by rfl⟩ : syracuseStep 5383763 = 8075645) B8075645
theorem B3589175 : Blo 1963435 3589175 := bstep (se 1 (by rfl) ⟨2691881, by rfl⟩ : syracuseStep 3589175 = 5383763) B5383763
theorem B2392783 : Blo 1963435 2392783 := bstep (se 1 (by rfl) ⟨1794587, by rfl⟩ : syracuseStep 2392783 = 3589175) B3589175
theorem B51046037 : Blo 1963435 51046037 := bstep (se 6 (by rfl) ⟨1196391, by rfl⟩ : syracuseStep 51046037 = 2392783) B2392783
theorem B34030691 : Blo 1963435 34030691 := bstep (se 1 (by rfl) ⟨25523018, by rfl⟩ : syracuseStep 34030691 = 51046037) B51046037
theorem B22687127 : Blo 1963435 22687127 := bstep (se 1 (by rfl) ⟨17015345, by rfl⟩ : syracuseStep 22687127 = 34030691) B34030691
theorem B15124751 : Blo 1963435 15124751 := bstep (se 1 (by rfl) ⟨11343563, by rfl⟩ : syracuseStep 15124751 = 22687127) B22687127
theorem B10083167 : Blo 1963435 10083167 := bstep (se 1 (by rfl) ⟨7562375, by rfl⟩ : syracuseStep 10083167 = 15124751) B15124751
theorem B6722111 : Blo 1963435 6722111 := bstep (se 1 (by rfl) ⟨5041583, by rfl⟩ : syracuseStep 6722111 = 10083167) B10083167
theorem B4481407 : Blo 1963435 4481407 := bstep (se 1 (by rfl) ⟨3361055, by rfl⟩ : syracuseStep 4481407 = 6722111) B6722111
theorem B5975209 : Blo 1963435 5975209 := bstep (se 2 (by rfl) ⟨2240703, by rfl⟩ : syracuseStep 5975209 = 4481407) B4481407
theorem B7966945 : Blo 1963435 7966945 := bstep (se 2 (by rfl) ⟨2987604, by rfl⟩ : syracuseStep 7966945 = 5975209) B5975209
theorem B10622593 : Blo 1963435 10622593 := bstep (se 2 (by rfl) ⟨3983472, by rfl⟩ : syracuseStep 10622593 = 7966945) B7966945
theorem B14163457 : Blo 1963435 14163457 := bstep (se 2 (by rfl) ⟨5311296, by rfl⟩ : syracuseStep 14163457 = 10622593) B10622593
theorem B18884609 : Blo 1963435 18884609 := bstep (se 2 (by rfl) ⟨7081728, by rfl⟩ : syracuseStep 18884609 = 14163457) B14163457
theorem B12589739 : Blo 1963435 12589739 := bstep (se 1 (by rfl) ⟨9442304, by rfl⟩ : syracuseStep 12589739 = 18884609) B18884609
theorem B8393159 : Blo 1963435 8393159 := bstep (se 1 (by rfl) ⟨6294869, by rfl⟩ : syracuseStep 8393159 = 12589739) B12589739
theorem B22381757 : Blo 1963435 22381757 := bstep (se 3 (by rfl) ⟨4196579, by rfl⟩ : syracuseStep 22381757 = 8393159) B8393159
theorem B14921171 : Blo 1963435 14921171 := bstep (se 1 (by rfl) ⟨11190878, by rfl⟩ : syracuseStep 14921171 = 22381757) B22381757
theorem B9947447 : Blo 1963435 9947447 := bstep (se 1 (by rfl) ⟨7460585, by rfl⟩ : syracuseStep 9947447 = 14921171) B14921171
theorem B6631631 : Blo 1963435 6631631 := bstep (se 1 (by rfl) ⟨4973723, by rfl⟩ : syracuseStep 6631631 = 9947447) B9947447
theorem B4421087 : Blo 1963435 4421087 := bstep (se 1 (by rfl) ⟨3315815, by rfl⟩ : syracuseStep 4421087 = 6631631) B6631631
theorem B2947391 : Blo 1963435 2947391 := bstep (se 1 (by rfl) ⟨2210543, by rfl⟩ : syracuseStep 2947391 = 4421087) B4421087
theorem B1964927 : Blo 1963435 1964927 := bstep (se 1 (by rfl) ⟨1473695, by rfl⟩ : syracuseStep 1964927 = 2947391) B2947391
theorem B2947397 : Blo 1963435 2947397 := bbase (se 4 (by rfl) ⟨276318, by rfl⟩ : syracuseStep 2947397 = 552637) (by norm_num)
theorem B1964931 : Blo 1963435 1964931 := bstep (se 1 (by rfl) ⟨1473698, by rfl⟩ : syracuseStep 1964931 = 2947397) B2947397
theorem B3315829 : Blo 1963435 3315829 := bbase (se 5 (by rfl) ⟨155429, by rfl⟩ : syracuseStep 3315829 = 310859) (by norm_num)
theorem B4421105 : Blo 1963435 4421105 := bstep (se 2 (by rfl) ⟨1657914, by rfl⟩ : syracuseStep 4421105 = 3315829) B3315829
theorem B2947403 : Blo 1963435 2947403 := bstep (se 1 (by rfl) ⟨2210552, by rfl⟩ : syracuseStep 2947403 = 4421105) B4421105
theorem B1964935 : Blo 1963435 1964935 := bstep (se 1 (by rfl) ⟨1473701, by rfl⟩ : syracuseStep 1964935 = 2947403) B2947403
theorem B2210557 : Blo 1963435 2210557 := bbase (se 3 (by rfl) ⟨414479, by rfl⟩ : syracuseStep 2210557 = 828959) (by norm_num)
theorem B2947409 : Blo 1963435 2947409 := bstep (se 2 (by rfl) ⟨1105278, by rfl⟩ : syracuseStep 2947409 = 2210557) B2210557
theorem B1964939 : Blo 1963435 1964939 := bstep (se 1 (by rfl) ⟨1473704, by rfl⟩ : syracuseStep 1964939 = 2947409) B2947409
theorem B6631685 : Blo 1963435 6631685 := bbase (se 4 (by rfl) ⟨621720, by rfl⟩ : syracuseStep 6631685 = 1243441) (by norm_num)
theorem B4421123 : Blo 1963435 4421123 := bstep (se 1 (by rfl) ⟨3315842, by rfl⟩ : syracuseStep 4421123 = 6631685) B6631685
theorem B2947415 : Blo 1963435 2947415 := bstep (se 1 (by rfl) ⟨2210561, by rfl⟩ : syracuseStep 2947415 = 4421123) B4421123
theorem B1964943 : Blo 1963435 1964943 := bstep (se 1 (by rfl) ⟨1473707, by rfl⟩ : syracuseStep 1964943 = 2947415) B2947415
theorem B2947421 : Blo 1963435 2947421 := bbase (se 3 (by rfl) ⟨552641, by rfl⟩ : syracuseStep 2947421 = 1105283) (by norm_num)
theorem B1964947 : Blo 1963435 1964947 := bstep (se 1 (by rfl) ⟨1473710, by rfl⟩ : syracuseStep 1964947 = 2947421) B2947421
theorem B4421141 : Blo 1963435 4421141 := bbase (se 6 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 4421141 = 207241) (by norm_num)
theorem B2947427 : Blo 1963435 2947427 := bstep (se 1 (by rfl) ⟨2210570, by rfl⟩ : syracuseStep 2947427 = 4421141) B4421141
theorem B1964951 : Blo 1963435 1964951 := bstep (se 1 (by rfl) ⟨1473713, by rfl⟩ : syracuseStep 1964951 = 2947427) B2947427
theorem B7460693 : Blo 1963435 7460693 := bbase (se 9 (by rfl) ⟨21857, by rfl⟩ : syracuseStep 7460693 = 43715) (by norm_num)
theorem B4973795 : Blo 1963435 4973795 := bstep (se 1 (by rfl) ⟨3730346, by rfl⟩ : syracuseStep 4973795 = 7460693) B7460693
theorem B3315863 : Blo 1963435 3315863 := bstep (se 1 (by rfl) ⟨2486897, by rfl⟩ : syracuseStep 3315863 = 4973795) B4973795
theorem B2210575 : Blo 1963435 2210575 := bstep (se 1 (by rfl) ⟨1657931, by rfl⟩ : syracuseStep 2210575 = 3315863) B3315863
theorem B2947433 : Blo 1963435 2947433 := bstep (se 2 (by rfl) ⟨1105287, by rfl⟩ : syracuseStep 2947433 = 2210575) B2210575
theorem B1964955 : Blo 1963435 1964955 := bstep (se 1 (by rfl) ⟨1473716, by rfl⟩ : syracuseStep 1964955 = 2947433) B2947433
theorem B11191061 : Blo 1963435 11191061 := bbase (se 6 (by rfl) ⟨262290, by rfl⟩ : syracuseStep 11191061 = 524581) (by norm_num)
theorem B7460707 : Blo 1963435 7460707 := bstep (se 1 (by rfl) ⟨5595530, by rfl⟩ : syracuseStep 7460707 = 11191061) B11191061
theorem B9947609 : Blo 1963435 9947609 := bstep (se 2 (by rfl) ⟨3730353, by rfl⟩ : syracuseStep 9947609 = 7460707) B7460707
theorem B6631739 : Blo 1963435 6631739 := bstep (se 1 (by rfl) ⟨4973804, by rfl⟩ : syracuseStep 6631739 = 9947609) B9947609
theorem B4421159 : Blo 1963435 4421159 := bstep (se 1 (by rfl) ⟨3315869, by rfl⟩ : syracuseStep 4421159 = 6631739) B6631739
theorem B2947439 : Blo 1963435 2947439 := bstep (se 1 (by rfl) ⟨2210579, by rfl⟩ : syracuseStep 2947439 = 4421159) B4421159
theorem B1964959 : Blo 1963435 1964959 := bstep (se 1 (by rfl) ⟨1473719, by rfl⟩ : syracuseStep 1964959 = 2947439) B2947439
theorem B2947445 : Blo 1963435 2947445 := bbase (se 5 (by rfl) ⟨138161, by rfl⟩ : syracuseStep 2947445 = 276323) (by norm_num)
theorem B1964963 : Blo 1963435 1964963 := bstep (se 1 (by rfl) ⟨1473722, by rfl⟩ : syracuseStep 1964963 = 2947445) B2947445
theorem B2098333 : Blo 1963435 2098333 := bbase (se 3 (by rfl) ⟨393437, by rfl⟩ : syracuseStep 2098333 = 786875) (by norm_num)
theorem B2797777 : Blo 1963435 2797777 := bstep (se 2 (by rfl) ⟨1049166, by rfl⟩ : syracuseStep 2797777 = 2098333) B2098333
theorem B3730369 : Blo 1963435 3730369 := bstep (se 2 (by rfl) ⟨1398888, by rfl⟩ : syracuseStep 3730369 = 2797777) B2797777
theorem B4973825 : Blo 1963435 4973825 := bstep (se 2 (by rfl) ⟨1865184, by rfl⟩ : syracuseStep 4973825 = 3730369) B3730369
theorem B3315883 : Blo 1963435 3315883 := bstep (se 1 (by rfl) ⟨2486912, by rfl⟩ : syracuseStep 3315883 = 4973825) B4973825
theorem B4421177 : Blo 1963435 4421177 := bstep (se 2 (by rfl) ⟨1657941, by rfl⟩ : syracuseStep 4421177 = 3315883) B3315883
theorem B2947451 : Blo 1963435 2947451 := bstep (se 1 (by rfl) ⟨2210588, by rfl⟩ : syracuseStep 2947451 = 4421177) B4421177
theorem B1964967 : Blo 1963435 1964967 := bstep (se 1 (by rfl) ⟨1473725, by rfl⟩ : syracuseStep 1964967 = 2947451) B2947451
theorem B2210593 : Blo 1963435 2210593 := bbase (se 2 (by rfl) ⟨828972, by rfl⟩ : syracuseStep 2210593 = 1657945) (by norm_num)
theorem B2947457 : Blo 1963435 2947457 := bstep (se 2 (by rfl) ⟨1105296, by rfl⟩ : syracuseStep 2947457 = 2210593) B2210593
theorem B1964971 : Blo 1963435 1964971 := bstep (se 1 (by rfl) ⟨1473728, by rfl⟩ : syracuseStep 1964971 = 2947457) B2947457
theorem B4973845 : Blo 1963435 4973845 := bbase (se 6 (by rfl) ⟨116574, by rfl⟩ : syracuseStep 4973845 = 233149) (by norm_num)
theorem B6631793 : Blo 1963435 6631793 := bstep (se 2 (by rfl) ⟨2486922, by rfl⟩ : syracuseStep 6631793 = 4973845) B4973845
theorem B4421195 : Blo 1963435 4421195 := bstep (se 1 (by rfl) ⟨3315896, by rfl⟩ : syracuseStep 4421195 = 6631793) B6631793
theorem B2947463 : Blo 1963435 2947463 := bstep (se 1 (by rfl) ⟨2210597, by rfl⟩ : syracuseStep 2947463 = 4421195) B4421195
theorem B1964975 : Blo 1963435 1964975 := bstep (se 1 (by rfl) ⟨1473731, by rfl⟩ : syracuseStep 1964975 = 2947463) B2947463
theorem B2947469 : Blo 1963435 2947469 := bbase (se 3 (by rfl) ⟨552650, by rfl⟩ : syracuseStep 2947469 = 1105301) (by norm_num)
theorem B1964979 : Blo 1963435 1964979 := bstep (se 1 (by rfl) ⟨1473734, by rfl⟩ : syracuseStep 1964979 = 2947469) B2947469
theorem B4421213 : Blo 1963435 4421213 := bbase (se 3 (by rfl) ⟨828977, by rfl⟩ : syracuseStep 4421213 = 1657955) (by norm_num)
theorem B2947475 : Blo 1963435 2947475 := bstep (se 1 (by rfl) ⟨2210606, by rfl⟩ : syracuseStep 2947475 = 4421213) B4421213
theorem B1964983 : Blo 1963435 1964983 := bstep (se 1 (by rfl) ⟨1473737, by rfl⟩ : syracuseStep 1964983 = 2947475) B2947475
theorem B3315917 : Blo 1963435 3315917 := bbase (se 3 (by rfl) ⟨621734, by rfl⟩ : syracuseStep 3315917 = 1243469) (by norm_num)
theorem B2210611 : Blo 1963435 2210611 := bstep (se 1 (by rfl) ⟨1657958, by rfl⟩ : syracuseStep 2210611 = 3315917) B3315917
theorem B2947481 : Blo 1963435 2947481 := bstep (se 2 (by rfl) ⟨1105305, by rfl⟩ : syracuseStep 2947481 = 2210611) B2210611
theorem B1964987 : Blo 1963435 1964987 := bstep (se 1 (by rfl) ⟨1473740, by rfl⟩ : syracuseStep 1964987 = 2947481) B2947481
theorem B2360653 : Blo 1963435 2360653 := bbase (se 3 (by rfl) ⟨442622, by rfl⟩ : syracuseStep 2360653 = 885245) (by norm_num)
theorem B12590149 : Blo 1963435 12590149 := bstep (se 4 (by rfl) ⟨1180326, by rfl⟩ : syracuseStep 12590149 = 2360653) B2360653
theorem B16786865 : Blo 1963435 16786865 := bstep (se 2 (by rfl) ⟨6295074, by rfl⟩ : syracuseStep 16786865 = 12590149) B12590149
theorem B11191243 : Blo 1963435 11191243 := bstep (se 1 (by rfl) ⟨8393432, by rfl⟩ : syracuseStep 11191243 = 16786865) B16786865
theorem B14921657 : Blo 1963435 14921657 := bstep (se 2 (by rfl) ⟨5595621, by rfl⟩ : syracuseStep 14921657 = 11191243) B11191243
theorem B9947771 : Blo 1963435 9947771 := bstep (se 1 (by rfl) ⟨7460828, by rfl⟩ : syracuseStep 9947771 = 14921657) B14921657
theorem B6631847 : Blo 1963435 6631847 := bstep (se 1 (by rfl) ⟨4973885, by rfl⟩ : syracuseStep 6631847 = 9947771) B9947771
theorem B4421231 : Blo 1963435 4421231 := bstep (se 1 (by rfl) ⟨3315923, by rfl⟩ : syracuseStep 4421231 = 6631847) B6631847
theorem B2947487 : Blo 1963435 2947487 := bstep (se 1 (by rfl) ⟨2210615, by rfl⟩ : syracuseStep 2947487 = 4421231) B4421231
theorem B1964991 : Blo 1963435 1964991 := bstep (se 1 (by rfl) ⟨1473743, by rfl⟩ : syracuseStep 1964991 = 2947487) B2947487
theorem B2947493 : Blo 1963435 2947493 := bbase (se 4 (by rfl) ⟨276327, by rfl⟩ : syracuseStep 2947493 = 552655) (by norm_num)
theorem B1964995 : Blo 1963435 1964995 := bstep (se 1 (by rfl) ⟨1473746, by rfl⟩ : syracuseStep 1964995 = 2947493) B2947493
theorem B2486953 : Blo 1963435 2486953 := bbase (se 2 (by rfl) ⟨932607, by rfl⟩ : syracuseStep 2486953 = 1865215) (by norm_num)
theorem B3315937 : Blo 1963435 3315937 := bstep (se 2 (by rfl) ⟨1243476, by rfl⟩ : syracuseStep 3315937 = 2486953) B2486953
theorem B4421249 : Blo 1963435 4421249 := bstep (se 2 (by rfl) ⟨1657968, by rfl⟩ : syracuseStep 4421249 = 3315937) B3315937
theorem B2947499 : Blo 1963435 2947499 := bstep (se 1 (by rfl) ⟨2210624, by rfl⟩ : syracuseStep 2947499 = 4421249) B4421249
theorem B1964999 : Blo 1963435 1964999 := bstep (se 1 (by rfl) ⟨1473749, by rfl⟩ : syracuseStep 1964999 = 2947499) B2947499
theorem B2210629 : Blo 1963435 2210629 := bbase (se 4 (by rfl) ⟨207246, by rfl⟩ : syracuseStep 2210629 = 414493) (by norm_num)
theorem B2947505 : Blo 1963435 2947505 := bstep (se 2 (by rfl) ⟨1105314, by rfl⟩ : syracuseStep 2947505 = 2210629) B2210629
theorem B1965003 : Blo 1963435 1965003 := bstep (se 1 (by rfl) ⟨1473752, by rfl⟩ : syracuseStep 1965003 = 2947505) B2947505
theorem B3730445 : Blo 1963435 3730445 := bbase (se 3 (by rfl) ⟨699458, by rfl⟩ : syracuseStep 3730445 = 1398917) (by norm_num)
theorem B2486963 : Blo 1963435 2486963 := bstep (se 1 (by rfl) ⟨1865222, by rfl⟩ : syracuseStep 2486963 = 3730445) B3730445
theorem B6631901 : Blo 1963435 6631901 := bstep (se 3 (by rfl) ⟨1243481, by rfl⟩ : syracuseStep 6631901 = 2486963) B2486963
theorem B4421267 : Blo 1963435 4421267 := bstep (se 1 (by rfl) ⟨3315950, by rfl⟩ : syracuseStep 4421267 = 6631901) B6631901
theorem B2947511 : Blo 1963435 2947511 := bstep (se 1 (by rfl) ⟨2210633, by rfl⟩ : syracuseStep 2947511 = 4421267) B4421267
theorem B1965007 : Blo 1963435 1965007 := bstep (se 1 (by rfl) ⟨1473755, by rfl⟩ : syracuseStep 1965007 = 2947511) B2947511
theorem B2947517 : Blo 1963435 2947517 := bbase (se 3 (by rfl) ⟨552659, by rfl⟩ : syracuseStep 2947517 = 1105319) (by norm_num)
theorem B1965011 : Blo 1963435 1965011 := bstep (se 1 (by rfl) ⟨1473758, by rfl⟩ : syracuseStep 1965011 = 2947517) B2947517
theorem B4421285 : Blo 1963435 4421285 := bbase (se 4 (by rfl) ⟨414495, by rfl⟩ : syracuseStep 4421285 = 828991) (by norm_num)
theorem B2947523 : Blo 1963435 2947523 := bstep (se 1 (by rfl) ⟨2210642, by rfl⟩ : syracuseStep 2947523 = 4421285) B4421285
theorem B1965015 : Blo 1963435 1965015 := bstep (se 1 (by rfl) ⟨1473761, by rfl⟩ : syracuseStep 1965015 = 2947523) B2947523
theorem B4973957 : Blo 1963435 4973957 := bbase (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) (by norm_num)
theorem B3315971 : Blo 1963435 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B2210647 : Blo 1963435 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B2947529 : Blo 1963435 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B1965019 : Blo 1963435 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B3147589 : Blo 1963435 3147589 := bbase (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) (by norm_num)
theorem B4196785 : Blo 1963435 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B5595713 : Blo 1963435 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B3730475 : Blo 1963435 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B9947933 : Blo 1963435 9947933 := bstep (se 3 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 9947933 = 3730475) B3730475
theorem B6631955 : Blo 1963435 6631955 := bstep (se 1 (by rfl) ⟨4973966, by rfl⟩ : syracuseStep 6631955 = 9947933) B9947933
theorem B4421303 : Blo 1963435 4421303 := bstep (se 1 (by rfl) ⟨3315977, by rfl⟩ : syracuseStep 4421303 = 6631955) B6631955
theorem B2947535 : Blo 1963435 2947535 := bstep (se 1 (by rfl) ⟨2210651, by rfl⟩ : syracuseStep 2947535 = 4421303) B4421303
theorem B1965023 : Blo 1963435 1965023 := bstep (se 1 (by rfl) ⟨1473767, by rfl⟩ : syracuseStep 1965023 = 2947535) B2947535
theorem B2947541 : Blo 1963435 2947541 := bbase (se 7 (by rfl) ⟨34541, by rfl⟩ : syracuseStep 2947541 = 69083) (by norm_num)
theorem B1965027 : Blo 1963435 1965027 := bstep (se 1 (by rfl) ⟨1473770, by rfl⟩ : syracuseStep 1965027 = 2947541) B2947541
theorem B7460981 : Blo 1963435 7460981 := bbase (se 5 (by rfl) ⟨349733, by rfl⟩ : syracuseStep 7460981 = 699467) (by norm_num)
theorem B4973987 : Blo 1963435 4973987 := bstep (se 1 (by rfl) ⟨3730490, by rfl⟩ : syracuseStep 4973987 = 7460981) B7460981
theorem B3315991 : Blo 1963435 3315991 := bstep (se 1 (by rfl) ⟨2486993, by rfl⟩ : syracuseStep 3315991 = 4973987) B4973987
theorem B4421321 : Blo 1963435 4421321 := bstep (se 2 (by rfl) ⟨1657995, by rfl⟩ : syracuseStep 4421321 = 3315991) B3315991
theorem B2947547 : Blo 1963435 2947547 := bstep (se 1 (by rfl) ⟨2210660, by rfl⟩ : syracuseStep 2947547 = 4421321) B4421321
theorem B1965031 : Blo 1963435 1965031 := bstep (se 1 (by rfl) ⟨1473773, by rfl⟩ : syracuseStep 1965031 = 2947547) B2947547
theorem B2210665 : Blo 1963435 2210665 := bbase (se 2 (by rfl) ⟨828999, by rfl⟩ : syracuseStep 2210665 = 1657999) (by norm_num)
theorem B2947553 : Blo 1963435 2947553 := bstep (se 2 (by rfl) ⟨1105332, by rfl⟩ : syracuseStep 2947553 = 2210665) B2210665
theorem B1965035 : Blo 1963435 1965035 := bstep (se 1 (by rfl) ⟨1473776, by rfl⟩ : syracuseStep 1965035 = 2947553) B2947553
theorem B3983701 : Blo 1963435 3983701 := bbase (se 10 (by rfl) ⟨5835, by rfl⟩ : syracuseStep 3983701 = 11671) (by norm_num)
theorem B5311601 : Blo 1963435 5311601 := bstep (se 2 (by rfl) ⟨1991850, by rfl⟩ : syracuseStep 5311601 = 3983701) B3983701
theorem B3541067 : Blo 1963435 3541067 := bstep (se 1 (by rfl) ⟨2655800, by rfl⟩ : syracuseStep 3541067 = 5311601) B5311601
theorem B2360711 : Blo 1963435 2360711 := bstep (se 1 (by rfl) ⟨1770533, by rfl⟩ : syracuseStep 2360711 = 3541067) B3541067
theorem B6295229 : Blo 1963435 6295229 := bstep (se 3 (by rfl) ⟨1180355, by rfl⟩ : syracuseStep 6295229 = 2360711) B2360711
theorem B4196819 : Blo 1963435 4196819 := bstep (se 1 (by rfl) ⟨3147614, by rfl⟩ : syracuseStep 4196819 = 6295229) B6295229
theorem B11191517 : Blo 1963435 11191517 := bstep (se 3 (by rfl) ⟨2098409, by rfl⟩ : syracuseStep 11191517 = 4196819) B4196819
theorem B7461011 : Blo 1963435 7461011 := bstep (se 1 (by rfl) ⟨5595758, by rfl⟩ : syracuseStep 7461011 = 11191517) B11191517
theorem B4974007 : Blo 1963435 4974007 := bstep (se 1 (by rfl) ⟨3730505, by rfl⟩ : syracuseStep 4974007 = 7461011) B7461011
theorem B6632009 : Blo 1963435 6632009 := bstep (se 2 (by rfl) ⟨2487003, by rfl⟩ : syracuseStep 6632009 = 4974007) B4974007
theorem B4421339 : Blo 1963435 4421339 := bstep (se 1 (by rfl) ⟨3316004, by rfl⟩ : syracuseStep 4421339 = 6632009) B6632009
theorem B2947559 : Blo 1963435 2947559 := bstep (se 1 (by rfl) ⟨2210669, by rfl⟩ : syracuseStep 2947559 = 4421339) B4421339
theorem B1965039 : Blo 1963435 1965039 := bstep (se 1 (by rfl) ⟨1473779, by rfl⟩ : syracuseStep 1965039 = 2947559) B2947559
theorem B2947565 : Blo 1963435 2947565 := bbase (se 3 (by rfl) ⟨552668, by rfl⟩ : syracuseStep 2947565 = 1105337) (by norm_num)
theorem B1965043 : Blo 1963435 1965043 := bstep (se 1 (by rfl) ⟨1473782, by rfl⟩ : syracuseStep 1965043 = 2947565) B2947565
theorem B4421357 : Blo 1963435 4421357 := bbase (se 3 (by rfl) ⟨829004, by rfl⟩ : syracuseStep 4421357 = 1658009) (by norm_num)
theorem B2947571 : Blo 1963435 2947571 := bstep (se 1 (by rfl) ⟨2210678, by rfl⟩ : syracuseStep 2947571 = 4421357) B4421357
theorem B1965047 : Blo 1963435 1965047 := bstep (se 1 (by rfl) ⟨1473785, by rfl⟩ : syracuseStep 1965047 = 2947571) B2947571
theorem B4721453 : Blo 1963435 4721453 := bbase (se 3 (by rfl) ⟨885272, by rfl⟩ : syracuseStep 4721453 = 1770545) (by norm_num)
theorem B3147635 : Blo 1963435 3147635 := bstep (se 1 (by rfl) ⟨2360726, by rfl⟩ : syracuseStep 3147635 = 4721453) B4721453
theorem B2098423 : Blo 1963435 2098423 := bstep (se 1 (by rfl) ⟨1573817, by rfl⟩ : syracuseStep 2098423 = 3147635) B3147635
theorem B2797897 : Blo 1963435 2797897 := bstep (se 2 (by rfl) ⟨1049211, by rfl⟩ : syracuseStep 2797897 = 2098423) B2098423
theorem B3730529 : Blo 1963435 3730529 := bstep (se 2 (by rfl) ⟨1398948, by rfl⟩ : syracuseStep 3730529 = 2797897) B2797897
theorem B2487019 : Blo 1963435 2487019 := bstep (se 1 (by rfl) ⟨1865264, by rfl⟩ : syracuseStep 2487019 = 3730529) B3730529
theorem B3316025 : Blo 1963435 3316025 := bstep (se 2 (by rfl) ⟨1243509, by rfl⟩ : syracuseStep 3316025 = 2487019) B2487019
theorem B2210683 : Blo 1963435 2210683 := bstep (se 1 (by rfl) ⟨1658012, by rfl⟩ : syracuseStep 2210683 = 3316025) B3316025
theorem B2947577 : Blo 1963435 2947577 := bstep (se 2 (by rfl) ⟨1105341, by rfl⟩ : syracuseStep 2947577 = 2210683) B2210683
theorem B1965051 : Blo 1963435 1965051 := bstep (se 1 (by rfl) ⟨1473788, by rfl⟩ : syracuseStep 1965051 = 2947577) B2947577
theorem B22688597 : Blo 1963435 22688597 := bbase (se 9 (by rfl) ⟨66470, by rfl⟩ : syracuseStep 22688597 = 132941) (by norm_num)
theorem B60502925 : Blo 1963435 60502925 := bstep (se 3 (by rfl) ⟨11344298, by rfl⟩ : syracuseStep 60502925 = 22688597) B22688597
theorem B40335283 : Blo 1963435 40335283 := bstep (se 1 (by rfl) ⟨30251462, by rfl⟩ : syracuseStep 40335283 = 60502925) B60502925
theorem B53780377 : Blo 1963435 53780377 := bstep (se 2 (by rfl) ⟨20167641, by rfl⟩ : syracuseStep 53780377 = 40335283) B40335283
theorem B71707169 : Blo 1963435 71707169 := bstep (se 2 (by rfl) ⟨26890188, by rfl⟩ : syracuseStep 71707169 = 53780377) B53780377
theorem B47804779 : Blo 1963435 47804779 := bstep (se 1 (by rfl) ⟨35853584, by rfl⟩ : syracuseStep 47804779 = 71707169) B71707169
theorem B63739705 : Blo 1963435 63739705 := bstep (se 2 (by rfl) ⟨23902389, by rfl⟩ : syracuseStep 63739705 = 47804779) B47804779
theorem B84986273 : Blo 1963435 84986273 := bstep (se 2 (by rfl) ⟨31869852, by rfl⟩ : syracuseStep 84986273 = 63739705) B63739705
theorem B56657515 : Blo 1963435 56657515 := bstep (se 1 (by rfl) ⟨42493136, by rfl⟩ : syracuseStep 56657515 = 84986273) B84986273
theorem B75543353 : Blo 1963435 75543353 := bstep (se 2 (by rfl) ⟨28328757, by rfl⟩ : syracuseStep 75543353 = 56657515) B56657515
theorem B50362235 : Blo 1963435 50362235 := bstep (se 1 (by rfl) ⟨37771676, by rfl⟩ : syracuseStep 50362235 = 75543353) B75543353
theorem B33574823 : Blo 1963435 33574823 := bstep (se 1 (by rfl) ⟨25181117, by rfl⟩ : syracuseStep 33574823 = 50362235) B50362235
theorem B22383215 : Blo 1963435 22383215 := bstep (se 1 (by rfl) ⟨16787411, by rfl⟩ : syracuseStep 22383215 = 33574823) B33574823
theorem B14922143 : Blo 1963435 14922143 := bstep (se 1 (by rfl) ⟨11191607, by rfl⟩ : syracuseStep 14922143 = 22383215) B22383215
theorem B9948095 : Blo 1963435 9948095 := bstep (se 1 (by rfl) ⟨7461071, by rfl⟩ : syracuseStep 9948095 = 14922143) B14922143
theorem B6632063 : Blo 1963435 6632063 := bstep (se 1 (by rfl) ⟨4974047, by rfl⟩ : syracuseStep 6632063 = 9948095) B9948095
theorem B4421375 : Blo 1963435 4421375 := bstep (se 1 (by rfl) ⟨3316031, by rfl⟩ : syracuseStep 4421375 = 6632063) B6632063
theorem B2947583 : Blo 1963435 2947583 := bstep (se 1 (by rfl) ⟨2210687, by rfl⟩ : syracuseStep 2947583 = 4421375) B4421375
theorem B1965055 : Blo 1963435 1965055 := bstep (se 1 (by rfl) ⟨1473791, by rfl⟩ : syracuseStep 1965055 = 2947583) B2947583
theorem B2947589 : Blo 1963435 2947589 := bbase (se 4 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 2947589 = 552673) (by norm_num)
theorem B1965059 : Blo 1963435 1965059 := bstep (se 1 (by rfl) ⟨1473794, by rfl⟩ : syracuseStep 1965059 = 2947589) B2947589
theorem B3316045 : Blo 1963435 3316045 := bbase (se 3 (by rfl) ⟨621758, by rfl⟩ : syracuseStep 3316045 = 1243517) (by norm_num)
theorem B4421393 : Blo 1963435 4421393 := bstep (se 2 (by rfl) ⟨1658022, by rfl⟩ : syracuseStep 4421393 = 3316045) B3316045
theorem B2947595 : Blo 1963435 2947595 := bstep (se 1 (by rfl) ⟨2210696, by rfl⟩ : syracuseStep 2947595 = 4421393) B4421393
theorem B1965063 : Blo 1963435 1965063 := bstep (se 1 (by rfl) ⟨1473797, by rfl⟩ : syracuseStep 1965063 = 2947595) B2947595
theorem B2210701 : Blo 1963435 2210701 := bbase (se 3 (by rfl) ⟨414506, by rfl⟩ : syracuseStep 2210701 = 829013) (by norm_num)
theorem B2947601 : Blo 1963435 2947601 := bstep (se 2 (by rfl) ⟨1105350, by rfl⟩ : syracuseStep 2947601 = 2210701) B2210701
theorem B1965067 : Blo 1963435 1965067 := bstep (se 1 (by rfl) ⟨1473800, by rfl⟩ : syracuseStep 1965067 = 2947601) B2947601
theorem B6632117 : Blo 1963435 6632117 := bbase (se 5 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 6632117 = 621761) (by norm_num)
theorem B4421411 : Blo 1963435 4421411 := bstep (se 1 (by rfl) ⟨3316058, by rfl⟩ : syracuseStep 4421411 = 6632117) B6632117
theorem B2947607 : Blo 1963435 2947607 := bstep (se 1 (by rfl) ⟨2210705, by rfl⟩ : syracuseStep 2947607 = 4421411) B4421411
theorem B1965071 : Blo 1963435 1965071 := bstep (se 1 (by rfl) ⟨1473803, by rfl⟩ : syracuseStep 1965071 = 2947607) B2947607
theorem B2947613 : Blo 1963435 2947613 := bbase (se 3 (by rfl) ⟨552677, by rfl⟩ : syracuseStep 2947613 = 1105355) (by norm_num)
theorem B1965075 : Blo 1963435 1965075 := bstep (se 1 (by rfl) ⟨1473806, by rfl⟩ : syracuseStep 1965075 = 2947613) B2947613
theorem B4421429 : Blo 1963435 4421429 := bbase (se 5 (by rfl) ⟨207254, by rfl⟩ : syracuseStep 4421429 = 414509) (by norm_num)
theorem B2947619 : Blo 1963435 2947619 := bstep (se 1 (by rfl) ⟨2210714, by rfl⟩ : syracuseStep 2947619 = 4421429) B4421429
theorem B1965079 : Blo 1963435 1965079 := bstep (se 1 (by rfl) ⟨1473809, by rfl⟩ : syracuseStep 1965079 = 2947619) B2947619
theorem B12590741 : Blo 1963435 12590741 := bbase (se 6 (by rfl) ⟨295095, by rfl⟩ : syracuseStep 12590741 = 590191) (by norm_num)
theorem B8393827 : Blo 1963435 8393827 := bstep (se 1 (by rfl) ⟨6295370, by rfl⟩ : syracuseStep 8393827 = 12590741) B12590741
theorem B11191769 : Blo 1963435 11191769 := bstep (se 2 (by rfl) ⟨4196913, by rfl⟩ : syracuseStep 11191769 = 8393827) B8393827
theorem B7461179 : Blo 1963435 7461179 := bstep (se 1 (by rfl) ⟨5595884, by rfl⟩ : syracuseStep 7461179 = 11191769) B11191769
theorem B4974119 : Blo 1963435 4974119 := bstep (se 1 (by rfl) ⟨3730589, by rfl⟩ : syracuseStep 4974119 = 7461179) B7461179
theorem B3316079 : Blo 1963435 3316079 := bstep (se 1 (by rfl) ⟨2487059, by rfl⟩ : syracuseStep 3316079 = 4974119) B4974119
theorem B2210719 : Blo 1963435 2210719 := bstep (se 1 (by rfl) ⟨1658039, by rfl⟩ : syracuseStep 2210719 = 3316079) B3316079
theorem B2947625 : Blo 1963435 2947625 := bstep (se 2 (by rfl) ⟨1105359, by rfl⟩ : syracuseStep 2947625 = 2210719) B2210719
theorem B1965083 : Blo 1963435 1965083 := bstep (se 1 (by rfl) ⟨1473812, by rfl⟩ : syracuseStep 1965083 = 2947625) B2947625
theorem B5041997 : Blo 1963435 5041997 := bbase (se 3 (by rfl) ⟨945374, by rfl⟩ : syracuseStep 5041997 = 1890749) (by norm_num)
theorem B3361331 : Blo 1963435 3361331 := bstep (se 1 (by rfl) ⟨2520998, by rfl⟩ : syracuseStep 3361331 = 5041997) B5041997
theorem B2240887 : Blo 1963435 2240887 := bstep (se 1 (by rfl) ⟨1680665, by rfl⟩ : syracuseStep 2240887 = 3361331) B3361331
theorem B2987849 : Blo 1963435 2987849 := bstep (se 2 (by rfl) ⟨1120443, by rfl⟩ : syracuseStep 2987849 = 2240887) B2240887
theorem B1991899 : Blo 1963435 1991899 := bstep (se 1 (by rfl) ⟨1493924, by rfl⟩ : syracuseStep 1991899 = 2987849) B2987849
theorem B2655865 : Blo 1963435 2655865 := bstep (se 2 (by rfl) ⟨995949, by rfl⟩ : syracuseStep 2655865 = 1991899) B1991899
theorem B3541153 : Blo 1963435 3541153 := bstep (se 2 (by rfl) ⟨1327932, by rfl⟩ : syracuseStep 3541153 = 2655865) B2655865
theorem B4721537 : Blo 1963435 4721537 := bstep (se 2 (by rfl) ⟨1770576, by rfl⟩ : syracuseStep 4721537 = 3541153) B3541153
theorem B12590765 : Blo 1963435 12590765 := bstep (se 3 (by rfl) ⟨2360768, by rfl⟩ : syracuseStep 12590765 = 4721537) B4721537
theorem B8393843 : Blo 1963435 8393843 := bstep (se 1 (by rfl) ⟨6295382, by rfl⟩ : syracuseStep 8393843 = 12590765) B12590765
theorem B5595895 : Blo 1963435 5595895 := bstep (se 1 (by rfl) ⟨4196921, by rfl⟩ : syracuseStep 5595895 = 8393843) B8393843
theorem B7461193 : Blo 1963435 7461193 := bstep (se 2 (by rfl) ⟨2797947, by rfl⟩ : syracuseStep 7461193 = 5595895) B5595895
theorem B9948257 : Blo 1963435 9948257 := bstep (se 2 (by rfl) ⟨3730596, by rfl⟩ : syracuseStep 9948257 = 7461193) B7461193
theorem B6632171 : Blo 1963435 6632171 := bstep (se 1 (by rfl) ⟨4974128, by rfl⟩ : syracuseStep 6632171 = 9948257) B9948257
theorem B4421447 : Blo 1963435 4421447 := bstep (se 1 (by rfl) ⟨3316085, by rfl⟩ : syracuseStep 4421447 = 6632171) B6632171
theorem B2947631 : Blo 1963435 2947631 := bstep (se 1 (by rfl) ⟨2210723, by rfl⟩ : syracuseStep 2947631 = 4421447) B4421447
theorem B1965087 : Blo 1963435 1965087 := bstep (se 1 (by rfl) ⟨1473815, by rfl⟩ : syracuseStep 1965087 = 2947631) B2947631
theorem B2947637 : Blo 1963435 2947637 := bbase (se 5 (by rfl) ⟨138170, by rfl⟩ : syracuseStep 2947637 = 276341) (by norm_num)
theorem B1965091 : Blo 1963435 1965091 := bstep (se 1 (by rfl) ⟨1473818, by rfl⟩ : syracuseStep 1965091 = 2947637) B2947637
theorem B4974149 : Blo 1963435 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B3316099 : Blo 1963435 3316099 := bstep (se 1 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 3316099 = 4974149) B4974149
theorem B4421465 : Blo 1963435 4421465 := bstep (se 2 (by rfl) ⟨1658049, by rfl⟩ : syracuseStep 4421465 = 3316099) B3316099
theorem B2947643 : Blo 1963435 2947643 := bstep (se 1 (by rfl) ⟨2210732, by rfl⟩ : syracuseStep 2947643 = 4421465) B4421465
theorem B1965095 : Blo 1963435 1965095 := bstep (se 1 (by rfl) ⟨1473821, by rfl⟩ : syracuseStep 1965095 = 2947643) B2947643
theorem B2210737 : Blo 1963435 2210737 := bbase (se 2 (by rfl) ⟨829026, by rfl⟩ : syracuseStep 2210737 = 1658053) (by norm_num)
theorem B2947649 : Blo 1963435 2947649 := bstep (se 2 (by rfl) ⟨1105368, by rfl⟩ : syracuseStep 2947649 = 2210737) B2210737
theorem B1965099 : Blo 1963435 1965099 := bstep (se 1 (by rfl) ⟨1473824, by rfl⟩ : syracuseStep 1965099 = 2947649) B2947649
theorem B5595941 : Blo 1963435 5595941 := bbase (se 4 (by rfl) ⟨524619, by rfl⟩ : syracuseStep 5595941 = 1049239) (by norm_num)
theorem B3730627 : Blo 1963435 3730627 := bstep (se 1 (by rfl) ⟨2797970, by rfl⟩ : syracuseStep 3730627 = 5595941) B5595941
theorem B4974169 : Blo 1963435 4974169 := bstep (se 2 (by rfl) ⟨1865313, by rfl⟩ : syracuseStep 4974169 = 3730627) B3730627
theorem B6632225 : Blo 1963435 6632225 := bstep (se 2 (by rfl) ⟨2487084, by rfl⟩ : syracuseStep 6632225 = 4974169) B4974169
theorem B4421483 : Blo 1963435 4421483 := bstep (se 1 (by rfl) ⟨3316112, by rfl⟩ : syracuseStep 4421483 = 6632225) B6632225
theorem B2947655 : Blo 1963435 2947655 := bstep (se 1 (by rfl) ⟨2210741, by rfl⟩ : syracuseStep 2947655 = 4421483) B4421483
theorem B1965103 : Blo 1963435 1965103 := bstep (se 1 (by rfl) ⟨1473827, by rfl⟩ : syracuseStep 1965103 = 2947655) B2947655
theorem B2947661 : Blo 1963435 2947661 := bbase (se 3 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 2947661 = 1105373) (by norm_num)
theorem B1965107 : Blo 1963435 1965107 := bstep (se 1 (by rfl) ⟨1473830, by rfl⟩ : syracuseStep 1965107 = 2947661) B2947661
theorem B4421501 : Blo 1963435 4421501 := bbase (se 3 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 4421501 = 1658063) (by norm_num)
theorem B2947667 : Blo 1963435 2947667 := bstep (se 1 (by rfl) ⟨2210750, by rfl⟩ : syracuseStep 2947667 = 4421501) B4421501
theorem B1965111 : Blo 1963435 1965111 := bstep (se 1 (by rfl) ⟨1473833, by rfl⟩ : syracuseStep 1965111 = 2947667) B2947667
theorem B3316133 : Blo 1963435 3316133 := bbase (se 4 (by rfl) ⟨310887, by rfl⟩ : syracuseStep 3316133 = 621775) (by norm_num)
theorem B2210755 : Blo 1963435 2210755 := bstep (se 1 (by rfl) ⟨1658066, by rfl⟩ : syracuseStep 2210755 = 3316133) B3316133
theorem B2947673 : Blo 1963435 2947673 := bstep (se 2 (by rfl) ⟨1105377, by rfl⟩ : syracuseStep 2947673 = 2210755) B2210755
theorem B1965115 : Blo 1963435 1965115 := bstep (se 1 (by rfl) ⟨1473836, by rfl⟩ : syracuseStep 1965115 = 2947673) B2947673
theorem B4786037 : Blo 1963435 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B3190691 : Blo 1963435 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B8508509 : Blo 1963435 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B5672339 : Blo 1963435 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B3781559 : Blo 1963435 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B2521039 : Blo 1963435 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B3361385 : Blo 1963435 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B8963693 : Blo 1963435 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B5975795 : Blo 1963435 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B15935453 : Blo 1963435 15935453 := bstep (se 3 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 15935453 = 5975795) B5975795
theorem B10623635 : Blo 1963435 10623635 := bstep (se 1 (by rfl) ⟨7967726, by rfl⟩ : syracuseStep 10623635 = 15935453) B15935453
theorem B7082423 : Blo 1963435 7082423 := bstep (se 1 (by rfl) ⟨5311817, by rfl⟩ : syracuseStep 7082423 = 10623635) B10623635
theorem B4721615 : Blo 1963435 4721615 := bstep (se 1 (by rfl) ⟨3541211, by rfl⟩ : syracuseStep 4721615 = 7082423) B7082423
theorem B3147743 : Blo 1963435 3147743 := bstep (se 1 (by rfl) ⟨2360807, by rfl⟩ : syracuseStep 3147743 = 4721615) B4721615
theorem B2098495 : Blo 1963435 2098495 := bstep (se 1 (by rfl) ⟨1573871, by rfl⟩ : syracuseStep 2098495 = 3147743) B3147743
theorem B2797993 : Blo 1963435 2797993 := bstep (se 2 (by rfl) ⟨1049247, by rfl⟩ : syracuseStep 2797993 = 2098495) B2098495
theorem B14922629 : Blo 1963435 14922629 := bstep (se 4 (by rfl) ⟨1398996, by rfl⟩ : syracuseStep 14922629 = 2797993) B2797993
theorem B9948419 : Blo 1963435 9948419 := bstep (se 1 (by rfl) ⟨7461314, by rfl⟩ : syracuseStep 9948419 = 14922629) B14922629
theorem B6632279 : Blo 1963435 6632279 := bstep (se 1 (by rfl) ⟨4974209, by rfl⟩ : syracuseStep 6632279 = 9948419) B9948419
theorem B4421519 : Blo 1963435 4421519 := bstep (se 1 (by rfl) ⟨3316139, by rfl⟩ : syracuseStep 4421519 = 6632279) B6632279
theorem B2947679 : Blo 1963435 2947679 := bstep (se 1 (by rfl) ⟨2210759, by rfl⟩ : syracuseStep 2947679 = 4421519) B4421519
theorem B1965119 : Blo 1963435 1965119 := bstep (se 1 (by rfl) ⟨1473839, by rfl⟩ : syracuseStep 1965119 = 2947679) B2947679
theorem B2947685 : Blo 1963435 2947685 := bbase (se 4 (by rfl) ⟨276345, by rfl⟩ : syracuseStep 2947685 = 552691) (by norm_num)
theorem B1965123 : Blo 1963435 1965123 := bstep (se 1 (by rfl) ⟨1473842, by rfl⟩ : syracuseStep 1965123 = 2947685) B2947685
theorem B2798005 : Blo 1963435 2798005 := bbase (se 5 (by rfl) ⟨131156, by rfl⟩ : syracuseStep 2798005 = 262313) (by norm_num)
theorem B3730673 : Blo 1963435 3730673 := bstep (se 2 (by rfl) ⟨1399002, by rfl⟩ : syracuseStep 3730673 = 2798005) B2798005
theorem B2487115 : Blo 1963435 2487115 := bstep (se 1 (by rfl) ⟨1865336, by rfl⟩ : syracuseStep 2487115 = 3730673) B3730673
theorem B3316153 : Blo 1963435 3316153 := bstep (se 2 (by rfl) ⟨1243557, by rfl⟩ : syracuseStep 3316153 = 2487115) B2487115
theorem B4421537 : Blo 1963435 4421537 := bstep (se 2 (by rfl) ⟨1658076, by rfl⟩ : syracuseStep 4421537 = 3316153) B3316153
theorem B2947691 : Blo 1963435 2947691 := bstep (se 1 (by rfl) ⟨2210768, by rfl⟩ : syracuseStep 2947691 = 4421537) B4421537
theorem B1965127 : Blo 1963435 1965127 := bstep (se 1 (by rfl) ⟨1473845, by rfl⟩ : syracuseStep 1965127 = 2947691) B2947691
theorem B2210773 : Blo 1963435 2210773 := bbase (se 7 (by rfl) ⟨25907, by rfl⟩ : syracuseStep 2210773 = 51815) (by norm_num)
theorem B2947697 : Blo 1963435 2947697 := bstep (se 2 (by rfl) ⟨1105386, by rfl⟩ : syracuseStep 2947697 = 2210773) B2210773
theorem B1965131 : Blo 1963435 1965131 := bstep (se 1 (by rfl) ⟨1473848, by rfl⟩ : syracuseStep 1965131 = 2947697) B2947697
theorem B2487125 : Blo 1963435 2487125 := bbase (se 9 (by rfl) ⟨7286, by rfl⟩ : syracuseStep 2487125 = 14573) (by norm_num)
theorem B6632333 : Blo 1963435 6632333 := bstep (se 3 (by rfl) ⟨1243562, by rfl⟩ : syracuseStep 6632333 = 2487125) B2487125
theorem B4421555 : Blo 1963435 4421555 := bstep (se 1 (by rfl) ⟨3316166, by rfl⟩ : syracuseStep 4421555 = 6632333) B6632333
theorem B2947703 : Blo 1963435 2947703 := bstep (se 1 (by rfl) ⟨2210777, by rfl⟩ : syracuseStep 2947703 = 4421555) B4421555
theorem B1965135 : Blo 1963435 1965135 := bstep (se 1 (by rfl) ⟨1473851, by rfl⟩ : syracuseStep 1965135 = 2947703) B2947703
theorem B2947709 : Blo 1963435 2947709 := bbase (se 3 (by rfl) ⟨552695, by rfl⟩ : syracuseStep 2947709 = 1105391) (by norm_num)
theorem B1965139 : Blo 1963435 1965139 := bstep (se 1 (by rfl) ⟨1473854, by rfl⟩ : syracuseStep 1965139 = 2947709) B2947709
theorem B4421573 : Blo 1963435 4421573 := bbase (se 4 (by rfl) ⟨414522, by rfl⟩ : syracuseStep 4421573 = 829045) (by norm_num)
theorem B2947715 : Blo 1963435 2947715 := bstep (se 1 (by rfl) ⟨2210786, by rfl⟩ : syracuseStep 2947715 = 4421573) B4421573
theorem B1965143 : Blo 1963435 1965143 := bstep (se 1 (by rfl) ⟨1473857, by rfl⟩ : syracuseStep 1965143 = 2947715) B2947715
theorem B8394101 : Blo 1963435 8394101 := bbase (se 5 (by rfl) ⟨393473, by rfl⟩ : syracuseStep 8394101 = 786947) (by norm_num)
theorem B5596067 : Blo 1963435 5596067 := bstep (se 1 (by rfl) ⟨4197050, by rfl⟩ : syracuseStep 5596067 = 8394101) B8394101
theorem B3730711 : Blo 1963435 3730711 := bstep (se 1 (by rfl) ⟨2798033, by rfl⟩ : syracuseStep 3730711 = 5596067) B5596067
theorem B4974281 : Blo 1963435 4974281 := bstep (se 2 (by rfl) ⟨1865355, by rfl⟩ : syracuseStep 4974281 = 3730711) B3730711
theorem B3316187 : Blo 1963435 3316187 := bstep (se 1 (by rfl) ⟨2487140, by rfl⟩ : syracuseStep 3316187 = 4974281) B4974281
theorem B2210791 : Blo 1963435 2210791 := bstep (se 1 (by rfl) ⟨1658093, by rfl⟩ : syracuseStep 2210791 = 3316187) B3316187
theorem B2947721 : Blo 1963435 2947721 := bstep (se 2 (by rfl) ⟨1105395, by rfl⟩ : syracuseStep 2947721 = 2210791) B2210791
theorem B1965147 : Blo 1963435 1965147 := bstep (se 1 (by rfl) ⟨1473860, by rfl⟩ : syracuseStep 1965147 = 2947721) B2947721
theorem B9948581 : Blo 1963435 9948581 := bbase (se 4 (by rfl) ⟨932679, by rfl⟩ : syracuseStep 9948581 = 1865359) (by norm_num)
theorem B6632387 : Blo 1963435 6632387 := bstep (se 1 (by rfl) ⟨4974290, by rfl⟩ : syracuseStep 6632387 = 9948581) B9948581
theorem B4421591 : Blo 1963435 4421591 := bstep (se 1 (by rfl) ⟨3316193, by rfl⟩ : syracuseStep 4421591 = 6632387) B6632387
theorem B2947727 : Blo 1963435 2947727 := bstep (se 1 (by rfl) ⟨2210795, by rfl⟩ : syracuseStep 2947727 = 4421591) B4421591
theorem B1965151 : Blo 1963435 1965151 := bstep (se 1 (by rfl) ⟨1473863, by rfl⟩ : syracuseStep 1965151 = 2947727) B2947727
theorem B2947733 : Blo 1963435 2947733 := bbase (se 6 (by rfl) ⟨69087, by rfl⟩ : syracuseStep 2947733 = 138175) (by norm_num)
theorem B1965155 : Blo 1963435 1965155 := bstep (se 1 (by rfl) ⟨1473866, by rfl⟩ : syracuseStep 1965155 = 2947733) B2947733
theorem B7563269 : Blo 1963435 7563269 := bbase (se 4 (by rfl) ⟨709056, by rfl⟩ : syracuseStep 7563269 = 1418113) (by norm_num)
theorem B5042179 : Blo 1963435 5042179 := bstep (se 1 (by rfl) ⟨3781634, by rfl⟩ : syracuseStep 5042179 = 7563269) B7563269
theorem B6722905 : Blo 1963435 6722905 := bstep (se 2 (by rfl) ⟨2521089, by rfl⟩ : syracuseStep 6722905 = 5042179) B5042179
theorem B8963873 : Blo 1963435 8963873 := bstep (se 2 (by rfl) ⟨3361452, by rfl⟩ : syracuseStep 8963873 = 6722905) B6722905
theorem B5975915 : Blo 1963435 5975915 := bstep (se 1 (by rfl) ⟨4481936, by rfl⟩ : syracuseStep 5975915 = 8963873) B8963873
theorem B15935773 : Blo 1963435 15935773 := bstep (se 3 (by rfl) ⟨2987957, by rfl⟩ : syracuseStep 15935773 = 5975915) B5975915
theorem B21247697 : Blo 1963435 21247697 := bstep (se 2 (by rfl) ⟨7967886, by rfl⟩ : syracuseStep 21247697 = 15935773) B15935773
theorem B14165131 : Blo 1963435 14165131 := bstep (se 1 (by rfl) ⟨10623848, by rfl⟩ : syracuseStep 14165131 = 21247697) B21247697
theorem B18886841 : Blo 1963435 18886841 := bstep (se 2 (by rfl) ⟨7082565, by rfl⟩ : syracuseStep 18886841 = 14165131) B14165131
theorem B12591227 : Blo 1963435 12591227 := bstep (se 1 (by rfl) ⟨9443420, by rfl⟩ : syracuseStep 12591227 = 18886841) B18886841
theorem B8394151 : Blo 1963435 8394151 := bstep (se 1 (by rfl) ⟨6295613, by rfl⟩ : syracuseStep 8394151 = 12591227) B12591227
theorem B11192201 : Blo 1963435 11192201 := bstep (se 2 (by rfl) ⟨4197075, by rfl⟩ : syracuseStep 11192201 = 8394151) B8394151
theorem B7461467 : Blo 1963435 7461467 := bstep (se 1 (by rfl) ⟨5596100, by rfl⟩ : syracuseStep 7461467 = 11192201) B11192201
theorem B4974311 : Blo 1963435 4974311 := bstep (se 1 (by rfl) ⟨3730733, by rfl⟩ : syracuseStep 4974311 = 7461467) B7461467
theorem B3316207 : Blo 1963435 3316207 := bstep (se 1 (by rfl) ⟨2487155, by rfl⟩ : syracuseStep 3316207 = 4974311) B4974311
theorem B4421609 : Blo 1963435 4421609 := bstep (se 2 (by rfl) ⟨1658103, by rfl⟩ : syracuseStep 4421609 = 3316207) B3316207
theorem B2947739 : Blo 1963435 2947739 := bstep (se 1 (by rfl) ⟨2210804, by rfl⟩ : syracuseStep 2947739 = 4421609) B4421609
theorem B1965159 : Blo 1963435 1965159 := bstep (se 1 (by rfl) ⟨1473869, by rfl⟩ : syracuseStep 1965159 = 2947739) B2947739
theorem B2210809 : Blo 1963435 2210809 := bbase (se 2 (by rfl) ⟨829053, by rfl⟩ : syracuseStep 2210809 = 1658107) (by norm_num)
theorem B2947745 : Blo 1963435 2947745 := bstep (se 2 (by rfl) ⟨1105404, by rfl⟩ : syracuseStep 2947745 = 2210809) B2210809
theorem B1965163 : Blo 1963435 1965163 := bstep (se 1 (by rfl) ⟨1473872, by rfl⟩ : syracuseStep 1965163 = 2947745) B2947745
theorem B2655973 : Blo 1963435 2655973 := bbase (se 4 (by rfl) ⟨248997, by rfl⟩ : syracuseStep 2655973 = 497995) (by norm_num)
theorem B14165189 : Blo 1963435 14165189 := bstep (se 4 (by rfl) ⟨1327986, by rfl⟩ : syracuseStep 14165189 = 2655973) B2655973
theorem B9443459 : Blo 1963435 9443459 := bstep (se 1 (by rfl) ⟨7082594, by rfl⟩ : syracuseStep 9443459 = 14165189) B14165189
theorem B6295639 : Blo 1963435 6295639 := bstep (se 1 (by rfl) ⟨4721729, by rfl⟩ : syracuseStep 6295639 = 9443459) B9443459
theorem B8394185 : Blo 1963435 8394185 := bstep (se 2 (by rfl) ⟨3147819, by rfl⟩ : syracuseStep 8394185 = 6295639) B6295639
theorem B5596123 : Blo 1963435 5596123 := bstep (se 1 (by rfl) ⟨4197092, by rfl⟩ : syracuseStep 5596123 = 8394185) B8394185
theorem B7461497 : Blo 1963435 7461497 := bstep (se 2 (by rfl) ⟨2798061, by rfl⟩ : syracuseStep 7461497 = 5596123) B5596123
theorem B4974331 : Blo 1963435 4974331 := bstep (se 1 (by rfl) ⟨3730748, by rfl⟩ : syracuseStep 4974331 = 7461497) B7461497
theorem B6632441 : Blo 1963435 6632441 := bstep (se 2 (by rfl) ⟨2487165, by rfl⟩ : syracuseStep 6632441 = 4974331) B4974331
theorem B4421627 : Blo 1963435 4421627 := bstep (se 1 (by rfl) ⟨3316220, by rfl⟩ : syracuseStep 4421627 = 6632441) B6632441
theorem B2947751 : Blo 1963435 2947751 := bstep (se 1 (by rfl) ⟨2210813, by rfl⟩ : syracuseStep 2947751 = 4421627) B4421627
theorem B1965167 : Blo 1963435 1965167 := bstep (se 1 (by rfl) ⟨1473875, by rfl⟩ : syracuseStep 1965167 = 2947751) B2947751
theorem B2947757 : Blo 1963435 2947757 := bbase (se 3 (by rfl) ⟨552704, by rfl⟩ : syracuseStep 2947757 = 1105409) (by norm_num)
theorem B1965171 : Blo 1963435 1965171 := bstep (se 1 (by rfl) ⟨1473878, by rfl⟩ : syracuseStep 1965171 = 2947757) B2947757
theorem B4421645 : Blo 1963435 4421645 := bbase (se 3 (by rfl) ⟨829058, by rfl⟩ : syracuseStep 4421645 = 1658117) (by norm_num)
theorem B2947763 : Blo 1963435 2947763 := bstep (se 1 (by rfl) ⟨2210822, by rfl⟩ : syracuseStep 2947763 = 4421645) B4421645
theorem B1965175 : Blo 1963435 1965175 := bstep (se 1 (by rfl) ⟨1473881, by rfl⟩ : syracuseStep 1965175 = 2947763) B2947763
theorem B2487181 : Blo 1963435 2487181 := bbase (se 3 (by rfl) ⟨466346, by rfl⟩ : syracuseStep 2487181 = 932693) (by norm_num)
theorem B3316241 : Blo 1963435 3316241 := bstep (se 2 (by rfl) ⟨1243590, by rfl⟩ : syracuseStep 3316241 = 2487181) B2487181
theorem B2210827 : Blo 1963435 2210827 := bstep (se 1 (by rfl) ⟨1658120, by rfl⟩ : syracuseStep 2210827 = 3316241) B3316241
theorem B2947769 : Blo 1963435 2947769 := bstep (se 2 (by rfl) ⟨1105413, by rfl⟩ : syracuseStep 2947769 = 2210827) B2210827
theorem B1965179 : Blo 1963435 1965179 := bstep (se 1 (by rfl) ⟨1473884, by rfl⟩ : syracuseStep 1965179 = 2947769) B2947769
theorem B2425745 : Blo 1963435 2425745 := bbase (se 2 (by rfl) ⟨909654, by rfl⟩ : syracuseStep 2425745 = 1819309) (by norm_num)
theorem B6468653 : Blo 1963435 6468653 := bstep (se 3 (by rfl) ⟨1212872, by rfl⟩ : syracuseStep 6468653 = 2425745) B2425745
theorem B4312435 : Blo 1963435 4312435 := bstep (se 1 (by rfl) ⟨3234326, by rfl⟩ : syracuseStep 4312435 = 6468653) B6468653
theorem B5749913 : Blo 1963435 5749913 := bstep (se 2 (by rfl) ⟨2156217, by rfl⟩ : syracuseStep 5749913 = 4312435) B4312435
theorem B3833275 : Blo 1963435 3833275 := bstep (se 1 (by rfl) ⟨2874956, by rfl⟩ : syracuseStep 3833275 = 5749913) B5749913
theorem B5111033 : Blo 1963435 5111033 := bstep (se 2 (by rfl) ⟨1916637, by rfl⟩ : syracuseStep 5111033 = 3833275) B3833275
theorem B13629421 : Blo 1963435 13629421 := bstep (se 3 (by rfl) ⟨2555516, by rfl⟩ : syracuseStep 13629421 = 5111033) B5111033
theorem B18172561 : Blo 1963435 18172561 := bstep (se 2 (by rfl) ⟨6814710, by rfl⟩ : syracuseStep 18172561 = 13629421) B13629421
theorem B24230081 : Blo 1963435 24230081 := bstep (se 2 (by rfl) ⟨9086280, by rfl⟩ : syracuseStep 24230081 = 18172561) B18172561
theorem B16153387 : Blo 1963435 16153387 := bstep (se 1 (by rfl) ⟨12115040, by rfl⟩ : syracuseStep 16153387 = 24230081) B24230081
theorem B344605589 : Blo 1963435 344605589 := bstep (se 6 (by rfl) ⟨8076693, by rfl⟩ : syracuseStep 344605589 = 16153387) B16153387
theorem B229737059 : Blo 1963435 229737059 := bstep (se 1 (by rfl) ⟨172302794, by rfl⟩ : syracuseStep 229737059 = 344605589) B344605589
theorem B153158039 : Blo 1963435 153158039 := bstep (se 1 (by rfl) ⟨114868529, by rfl⟩ : syracuseStep 153158039 = 229737059) B229737059
theorem B102105359 : Blo 1963435 102105359 := bstep (se 1 (by rfl) ⟨76579019, by rfl⟩ : syracuseStep 102105359 = 153158039) B153158039
theorem B68070239 : Blo 1963435 68070239 := bstep (se 1 (by rfl) ⟨51052679, by rfl⟩ : syracuseStep 68070239 = 102105359) B102105359
theorem B45380159 : Blo 1963435 45380159 := bstep (se 1 (by rfl) ⟨34035119, by rfl⟩ : syracuseStep 45380159 = 68070239) B68070239
theorem B30253439 : Blo 1963435 30253439 := bstep (se 1 (by rfl) ⟨22690079, by rfl⟩ : syracuseStep 30253439 = 45380159) B45380159
theorem B20168959 : Blo 1963435 20168959 := bstep (se 1 (by rfl) ⟨15126719, by rfl⟩ : syracuseStep 20168959 = 30253439) B30253439
theorem B26891945 : Blo 1963435 26891945 := bstep (se 2 (by rfl) ⟨10084479, by rfl⟩ : syracuseStep 26891945 = 20168959) B20168959
theorem B17927963 : Blo 1963435 17927963 := bstep (se 1 (by rfl) ⟨13445972, by rfl⟩ : syracuseStep 17927963 = 26891945) B26891945
theorem B11951975 : Blo 1963435 11951975 := bstep (se 1 (by rfl) ⟨8963981, by rfl⟩ : syracuseStep 11951975 = 17927963) B17927963
theorem B7967983 : Blo 1963435 7967983 := bstep (se 1 (by rfl) ⟨5975987, by rfl⟩ : syracuseStep 7967983 = 11951975) B11951975
theorem B10623977 : Blo 1963435 10623977 := bstep (se 2 (by rfl) ⟨3983991, by rfl⟩ : syracuseStep 10623977 = 7967983) B7967983
theorem B7082651 : Blo 1963435 7082651 := bstep (se 1 (by rfl) ⟨5311988, by rfl⟩ : syracuseStep 7082651 = 10623977) B10623977
theorem B18887069 : Blo 1963435 18887069 := bstep (se 3 (by rfl) ⟨3541325, by rfl⟩ : syracuseStep 18887069 = 7082651) B7082651
theorem B12591379 : Blo 1963435 12591379 := bstep (se 1 (by rfl) ⟨9443534, by rfl⟩ : syracuseStep 12591379 = 18887069) B18887069
theorem B16788505 : Blo 1963435 16788505 := bstep (se 2 (by rfl) ⟨6295689, by rfl⟩ : syracuseStep 16788505 = 12591379) B12591379
theorem B22384673 : Blo 1963435 22384673 := bstep (se 2 (by rfl) ⟨8394252, by rfl⟩ : syracuseStep 22384673 = 16788505) B16788505
theorem B14923115 : Blo 1963435 14923115 := bstep (se 1 (by rfl) ⟨11192336, by rfl⟩ : syracuseStep 14923115 = 22384673) B22384673
theorem B9948743 : Blo 1963435 9948743 := bstep (se 1 (by rfl) ⟨7461557, by rfl⟩ : syracuseStep 9948743 = 14923115) B14923115
theorem B6632495 : Blo 1963435 6632495 := bstep (se 1 (by rfl) ⟨4974371, by rfl⟩ : syracuseStep 6632495 = 9948743) B9948743
theorem B4421663 : Blo 1963435 4421663 := bstep (se 1 (by rfl) ⟨3316247, by rfl⟩ : syracuseStep 4421663 = 6632495) B6632495
theorem B2947775 : Blo 1963435 2947775 := bstep (se 1 (by rfl) ⟨2210831, by rfl⟩ : syracuseStep 2947775 = 4421663) B4421663
theorem B1965183 : Blo 1963435 1965183 := bstep (se 1 (by rfl) ⟨1473887, by rfl⟩ : syracuseStep 1965183 = 2947775) B2947775
theorem B2947781 : Blo 1963435 2947781 := bbase (se 4 (by rfl) ⟨276354, by rfl⟩ : syracuseStep 2947781 = 552709) (by norm_num)
theorem B1965187 : Blo 1963435 1965187 := bstep (se 1 (by rfl) ⟨1473890, by rfl⟩ : syracuseStep 1965187 = 2947781) B2947781
theorem B3316261 : Blo 1963435 3316261 := bbase (se 4 (by rfl) ⟨310899, by rfl⟩ : syracuseStep 3316261 = 621799) (by norm_num)
theorem B4421681 : Blo 1963435 4421681 := bstep (se 2 (by rfl) ⟨1658130, by rfl⟩ : syracuseStep 4421681 = 3316261) B3316261
theorem B2947787 : Blo 1963435 2947787 := bstep (se 1 (by rfl) ⟨2210840, by rfl⟩ : syracuseStep 2947787 = 4421681) B4421681
theorem B1965191 : Blo 1963435 1965191 := bstep (se 1 (by rfl) ⟨1473893, by rfl⟩ : syracuseStep 1965191 = 2947787) B2947787
theorem B2210845 : Blo 1963435 2210845 := bbase (se 3 (by rfl) ⟨414533, by rfl⟩ : syracuseStep 2210845 = 829067) (by norm_num)
theorem B2947793 : Blo 1963435 2947793 := bstep (se 2 (by rfl) ⟨1105422, by rfl⟩ : syracuseStep 2947793 = 2210845) B2210845
theorem B1965195 : Blo 1963435 1965195 := bstep (se 1 (by rfl) ⟨1473896, by rfl⟩ : syracuseStep 1965195 = 2947793) B2947793
theorem B6632549 : Blo 1963435 6632549 := bbase (se 4 (by rfl) ⟨621801, by rfl⟩ : syracuseStep 6632549 = 1243603) (by norm_num)
theorem B4421699 : Blo 1963435 4421699 := bstep (se 1 (by rfl) ⟨3316274, by rfl⟩ : syracuseStep 4421699 = 6632549) B6632549
theorem B2947799 : Blo 1963435 2947799 := bstep (se 1 (by rfl) ⟨2210849, by rfl⟩ : syracuseStep 2947799 = 4421699) B4421699
theorem B1965199 : Blo 1963435 1965199 := bstep (se 1 (by rfl) ⟨1473899, by rfl⟩ : syracuseStep 1965199 = 2947799) B2947799
theorem B2947805 : Blo 1963435 2947805 := bbase (se 3 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 2947805 = 1105427) (by norm_num)
theorem B1965203 : Blo 1963435 1965203 := bstep (se 1 (by rfl) ⟨1473902, by rfl⟩ : syracuseStep 1965203 = 2947805) B2947805
theorem B4421717 : Blo 1963435 4421717 := bbase (se 8 (by rfl) ⟨25908, by rfl⟩ : syracuseStep 4421717 = 51817) (by norm_num)
theorem B2947811 : Blo 1963435 2947811 := bstep (se 1 (by rfl) ⟨2210858, by rfl⟩ : syracuseStep 2947811 = 4421717) B4421717
theorem B1965207 : Blo 1963435 1965207 := bstep (se 1 (by rfl) ⟨1473905, by rfl⟩ : syracuseStep 1965207 = 2947811) B2947811
theorem B6295781 : Blo 1963435 6295781 := bbase (se 4 (by rfl) ⟨590229, by rfl⟩ : syracuseStep 6295781 = 1180459) (by norm_num)
theorem B4197187 : Blo 1963435 4197187 := bstep (se 1 (by rfl) ⟨3147890, by rfl⟩ : syracuseStep 4197187 = 6295781) B6295781
theorem B5596249 : Blo 1963435 5596249 := bstep (se 2 (by rfl) ⟨2098593, by rfl⟩ : syracuseStep 5596249 = 4197187) B4197187
theorem B7461665 : Blo 1963435 7461665 := bstep (se 2 (by rfl) ⟨2798124, by rfl⟩ : syracuseStep 7461665 = 5596249) B5596249
theorem B4974443 : Blo 1963435 4974443 := bstep (se 1 (by rfl) ⟨3730832, by rfl⟩ : syracuseStep 4974443 = 7461665) B7461665
theorem B3316295 : Blo 1963435 3316295 := bstep (se 1 (by rfl) ⟨2487221, by rfl⟩ : syracuseStep 3316295 = 4974443) B4974443
theorem B2210863 : Blo 1963435 2210863 := bstep (se 1 (by rfl) ⟨1658147, by rfl⟩ : syracuseStep 2210863 = 3316295) B3316295
theorem B2947817 : Blo 1963435 2947817 := bstep (se 2 (by rfl) ⟨1105431, by rfl⟩ : syracuseStep 2947817 = 2210863) B2210863
theorem B1965211 : Blo 1963435 1965211 := bstep (se 1 (by rfl) ⟨1473908, by rfl⟩ : syracuseStep 1965211 = 2947817) B2947817
theorem B5976085 : Blo 1963435 5976085 := bbase (se 6 (by rfl) ⟨140064, by rfl⟩ : syracuseStep 5976085 = 280129) (by norm_num)
theorem B7968113 : Blo 1963435 7968113 := bstep (se 2 (by rfl) ⟨2988042, by rfl⟩ : syracuseStep 7968113 = 5976085) B5976085
theorem B5312075 : Blo 1963435 5312075 := bstep (se 1 (by rfl) ⟨3984056, by rfl⟩ : syracuseStep 5312075 = 7968113) B7968113
theorem B14165533 : Blo 1963435 14165533 := bstep (se 3 (by rfl) ⟨2656037, by rfl⟩ : syracuseStep 14165533 = 5312075) B5312075
theorem B18887377 : Blo 1963435 18887377 := bstep (se 2 (by rfl) ⟨7082766, by rfl⟩ : syracuseStep 18887377 = 14165533) B14165533
theorem B25183169 : Blo 1963435 25183169 := bstep (se 2 (by rfl) ⟨9443688, by rfl⟩ : syracuseStep 25183169 = 18887377) B18887377
theorem B16788779 : Blo 1963435 16788779 := bstep (se 1 (by rfl) ⟨12591584, by rfl⟩ : syracuseStep 16788779 = 25183169) B25183169
theorem B11192519 : Blo 1963435 11192519 := bstep (se 1 (by rfl) ⟨8394389, by rfl⟩ : syracuseStep 11192519 = 16788779) B16788779
theorem B7461679 : Blo 1963435 7461679 := bstep (se 1 (by rfl) ⟨5596259, by rfl⟩ : syracuseStep 7461679 = 11192519) B11192519
theorem B9948905 : Blo 1963435 9948905 := bstep (se 2 (by rfl) ⟨3730839, by rfl⟩ : syracuseStep 9948905 = 7461679) B7461679
theorem B6632603 : Blo 1963435 6632603 := bstep (se 1 (by rfl) ⟨4974452, by rfl⟩ : syracuseStep 6632603 = 9948905) B9948905
theorem B4421735 : Blo 1963435 4421735 := bstep (se 1 (by rfl) ⟨3316301, by rfl⟩ : syracuseStep 4421735 = 6632603) B6632603
theorem B2947823 : Blo 1963435 2947823 := bstep (se 1 (by rfl) ⟨2210867, by rfl⟩ : syracuseStep 2947823 = 4421735) B4421735
theorem B1965215 : Blo 1963435 1965215 := bstep (se 1 (by rfl) ⟨1473911, by rfl⟩ : syracuseStep 1965215 = 2947823) B2947823
theorem B2947829 : Blo 1963435 2947829 := bbase (se 5 (by rfl) ⟨138179, by rfl⟩ : syracuseStep 2947829 = 276359) (by norm_num)
theorem B1965219 : Blo 1963435 1965219 := bstep (se 1 (by rfl) ⟨1473914, by rfl⟩ : syracuseStep 1965219 = 2947829) B2947829
theorem B1992037 : Blo 1963435 1992037 := bbase (se 4 (by rfl) ⟨186753, by rfl⟩ : syracuseStep 1992037 = 373507) (by norm_num)
theorem B2656049 : Blo 1963435 2656049 := bstep (se 2 (by rfl) ⟨996018, by rfl⟩ : syracuseStep 2656049 = 1992037) B1992037
theorem B7082797 : Blo 1963435 7082797 := bstep (se 3 (by rfl) ⟨1328024, by rfl⟩ : syracuseStep 7082797 = 2656049) B2656049
theorem B9443729 : Blo 1963435 9443729 := bstep (se 2 (by rfl) ⟨3541398, by rfl⟩ : syracuseStep 9443729 = 7082797) B7082797
theorem B6295819 : Blo 1963435 6295819 := bstep (se 1 (by rfl) ⟨4721864, by rfl⟩ : syracuseStep 6295819 = 9443729) B9443729
theorem B8394425 : Blo 1963435 8394425 := bstep (se 2 (by rfl) ⟨3147909, by rfl⟩ : syracuseStep 8394425 = 6295819) B6295819
theorem B5596283 : Blo 1963435 5596283 := bstep (se 1 (by rfl) ⟨4197212, by rfl⟩ : syracuseStep 5596283 = 8394425) B8394425
theorem B3730855 : Blo 1963435 3730855 := bstep (se 1 (by rfl) ⟨2798141, by rfl⟩ : syracuseStep 3730855 = 5596283) B5596283
theorem B4974473 : Blo 1963435 4974473 := bstep (se 2 (by rfl) ⟨1865427, by rfl⟩ : syracuseStep 4974473 = 3730855) B3730855
theorem B3316315 : Blo 1963435 3316315 := bstep (se 1 (by rfl) ⟨2487236, by rfl⟩ : syracuseStep 3316315 = 4974473) B4974473
theorem B4421753 : Blo 1963435 4421753 := bstep (se 2 (by rfl) ⟨1658157, by rfl⟩ : syracuseStep 4421753 = 3316315) B3316315
theorem B2947835 : Blo 1963435 2947835 := bstep (se 1 (by rfl) ⟨2210876, by rfl⟩ : syracuseStep 2947835 = 4421753) B4421753
theorem B1965223 : Blo 1963435 1965223 := bstep (se 1 (by rfl) ⟨1473917, by rfl⟩ : syracuseStep 1965223 = 2947835) B2947835
theorem B2210881 : Blo 1963435 2210881 := bbase (se 2 (by rfl) ⟨829080, by rfl⟩ : syracuseStep 2210881 = 1658161) (by norm_num)
theorem B2947841 : Blo 1963435 2947841 := bstep (se 2 (by rfl) ⟨1105440, by rfl⟩ : syracuseStep 2947841 = 2210881) B2210881
theorem B1965227 : Blo 1963435 1965227 := bstep (se 1 (by rfl) ⟨1473920, by rfl⟩ : syracuseStep 1965227 = 2947841) B2947841
theorem B4974493 : Blo 1963435 4974493 := bbase (se 3 (by rfl) ⟨932717, by rfl⟩ : syracuseStep 4974493 = 1865435) (by norm_num)
theorem B6632657 : Blo 1963435 6632657 := bstep (se 2 (by rfl) ⟨2487246, by rfl⟩ : syracuseStep 6632657 = 4974493) B4974493
theorem B4421771 : Blo 1963435 4421771 := bstep (se 1 (by rfl) ⟨3316328, by rfl⟩ : syracuseStep 4421771 = 6632657) B6632657
theorem B2947847 : Blo 1963435 2947847 := bstep (se 1 (by rfl) ⟨2210885, by rfl⟩ : syracuseStep 2947847 = 4421771) B4421771
theorem B1965231 : Blo 1963435 1965231 := bstep (se 1 (by rfl) ⟨1473923, by rfl⟩ : syracuseStep 1965231 = 2947847) B2947847
theorem B2947853 : Blo 1963435 2947853 := bbase (se 3 (by rfl) ⟨552722, by rfl⟩ : syracuseStep 2947853 = 1105445) (by norm_num)
theorem B1965235 : Blo 1963435 1965235 := bstep (se 1 (by rfl) ⟨1473926, by rfl⟩ : syracuseStep 1965235 = 2947853) B2947853
theorem B4421789 : Blo 1963435 4421789 := bbase (se 3 (by rfl) ⟨829085, by rfl⟩ : syracuseStep 4421789 = 1658171) (by norm_num)
theorem B2947859 : Blo 1963435 2947859 := bstep (se 1 (by rfl) ⟨2210894, by rfl⟩ : syracuseStep 2947859 = 4421789) B4421789
theorem B1965239 : Blo 1963435 1965239 := bstep (se 1 (by rfl) ⟨1473929, by rfl⟩ : syracuseStep 1965239 = 2947859) B2947859
theorem B3316349 : Blo 1963435 3316349 := bbase (se 3 (by rfl) ⟨621815, by rfl⟩ : syracuseStep 3316349 = 1243631) (by norm_num)
theorem B2210899 : Blo 1963435 2210899 := bstep (se 1 (by rfl) ⟨1658174, by rfl⟩ : syracuseStep 2210899 = 3316349) B3316349
theorem B2947865 : Blo 1963435 2947865 := bstep (se 2 (by rfl) ⟨1105449, by rfl⟩ : syracuseStep 2947865 = 2210899) B2210899
theorem B1965243 : Blo 1963435 1965243 := bstep (se 1 (by rfl) ⟨1473932, by rfl⟩ : syracuseStep 1965243 = 2947865) B2947865
theorem B1992061 : Blo 1963435 1992061 := bbase (se 3 (by rfl) ⟨373511, by rfl⟩ : syracuseStep 1992061 = 747023) (by norm_num)
theorem B2656081 : Blo 1963435 2656081 := bstep (se 2 (by rfl) ⟨996030, by rfl⟩ : syracuseStep 2656081 = 1992061) B1992061
theorem B14165765 : Blo 1963435 14165765 := bstep (se 4 (by rfl) ⟨1328040, by rfl⟩ : syracuseStep 14165765 = 2656081) B2656081
theorem B9443843 : Blo 1963435 9443843 := bstep (se 1 (by rfl) ⟨7082882, by rfl⟩ : syracuseStep 9443843 = 14165765) B14165765
theorem B6295895 : Blo 1963435 6295895 := bstep (se 1 (by rfl) ⟨4721921, by rfl⟩ : syracuseStep 6295895 = 9443843) B9443843
theorem B4197263 : Blo 1963435 4197263 := bstep (se 1 (by rfl) ⟨3147947, by rfl⟩ : syracuseStep 4197263 = 6295895) B6295895
theorem B11192701 : Blo 1963435 11192701 := bstep (se 3 (by rfl) ⟨2098631, by rfl⟩ : syracuseStep 11192701 = 4197263) B4197263
theorem B14923601 : Blo 1963435 14923601 := bstep (se 2 (by rfl) ⟨5596350, by rfl⟩ : syracuseStep 14923601 = 11192701) B11192701
theorem B9949067 : Blo 1963435 9949067 := bstep (se 1 (by rfl) ⟨7461800, by rfl⟩ : syracuseStep 9949067 = 14923601) B14923601
theorem B6632711 : Blo 1963435 6632711 := bstep (se 1 (by rfl) ⟨4974533, by rfl⟩ : syracuseStep 6632711 = 9949067) B9949067
theorem B4421807 : Blo 1963435 4421807 := bstep (se 1 (by rfl) ⟨3316355, by rfl⟩ : syracuseStep 4421807 = 6632711) B6632711
theorem B2947871 : Blo 1963435 2947871 := bstep (se 1 (by rfl) ⟨2210903, by rfl⟩ : syracuseStep 2947871 = 4421807) B4421807
theorem B1965247 : Blo 1963435 1965247 := bstep (se 1 (by rfl) ⟨1473935, by rfl⟩ : syracuseStep 1965247 = 2947871) B2947871
theorem B2947877 : Blo 1963435 2947877 := bbase (se 4 (by rfl) ⟨276363, by rfl⟩ : syracuseStep 2947877 = 552727) (by norm_num)
theorem B1965251 : Blo 1963435 1965251 := bstep (se 1 (by rfl) ⟨1473938, by rfl⟩ : syracuseStep 1965251 = 2947877) B2947877
theorem B2487277 : Blo 1963435 2487277 := bbase (se 3 (by rfl) ⟨466364, by rfl⟩ : syracuseStep 2487277 = 932729) (by norm_num)
theorem B3316369 : Blo 1963435 3316369 := bstep (se 2 (by rfl) ⟨1243638, by rfl⟩ : syracuseStep 3316369 = 2487277) B2487277
theorem B4421825 : Blo 1963435 4421825 := bstep (se 2 (by rfl) ⟨1658184, by rfl⟩ : syracuseStep 4421825 = 3316369) B3316369
theorem B2947883 : Blo 1963435 2947883 := bstep (se 1 (by rfl) ⟨2210912, by rfl⟩ : syracuseStep 2947883 = 4421825) B4421825
theorem B1965255 : Blo 1963435 1965255 := bstep (se 1 (by rfl) ⟨1473941, by rfl⟩ : syracuseStep 1965255 = 2947883) B2947883
theorem B2210917 : Blo 1963435 2210917 := bbase (se 4 (by rfl) ⟨207273, by rfl⟩ : syracuseStep 2210917 = 414547) (by norm_num)
theorem B2947889 : Blo 1963435 2947889 := bstep (se 2 (by rfl) ⟨1105458, by rfl⟩ : syracuseStep 2947889 = 2210917) B2210917
theorem B1965259 : Blo 1963435 1965259 := bstep (se 1 (by rfl) ⟨1473944, by rfl⟩ : syracuseStep 1965259 = 2947889) B2947889
theorem B2098649 : Blo 1963435 2098649 := bbase (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) (by norm_num)
theorem B5596397 : Blo 1963435 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B3730931 : Blo 1963435 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B2487287 : Blo 1963435 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B6632765 : Blo 1963435 6632765 := bstep (se 3 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 6632765 = 2487287) B2487287
theorem B4421843 : Blo 1963435 4421843 := bstep (se 1 (by rfl) ⟨3316382, by rfl⟩ : syracuseStep 4421843 = 6632765) B6632765
theorem B2947895 : Blo 1963435 2947895 := bstep (se 1 (by rfl) ⟨2210921, by rfl⟩ : syracuseStep 2947895 = 4421843) B4421843
theorem B1965263 : Blo 1963435 1965263 := bstep (se 1 (by rfl) ⟨1473947, by rfl⟩ : syracuseStep 1965263 = 2947895) B2947895
theorem B2947901 : Blo 1963435 2947901 := bbase (se 3 (by rfl) ⟨552731, by rfl⟩ : syracuseStep 2947901 = 1105463) (by norm_num)
theorem B1965267 : Blo 1963435 1965267 := bstep (se 1 (by rfl) ⟨1473950, by rfl⟩ : syracuseStep 1965267 = 2947901) B2947901
theorem B4421861 : Blo 1963435 4421861 := bbase (se 4 (by rfl) ⟨414549, by rfl⟩ : syracuseStep 4421861 = 829099) (by norm_num)
theorem B2947907 : Blo 1963435 2947907 := bstep (se 1 (by rfl) ⟨2210930, by rfl⟩ : syracuseStep 2947907 = 4421861) B4421861
theorem B1965271 : Blo 1963435 1965271 := bstep (se 1 (by rfl) ⟨1473953, by rfl⟩ : syracuseStep 1965271 = 2947907) B2947907
theorem B4974605 : Blo 1963435 4974605 := bbase (se 3 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 4974605 = 1865477) (by norm_num)
theorem B3316403 : Blo 1963435 3316403 := bstep (se 1 (by rfl) ⟨2487302, by rfl⟩ : syracuseStep 3316403 = 4974605) B4974605
theorem B2210935 : Blo 1963435 2210935 := bstep (se 1 (by rfl) ⟨1658201, by rfl⟩ : syracuseStep 2210935 = 3316403) B3316403
theorem B2947913 : Blo 1963435 2947913 := bstep (se 2 (by rfl) ⟨1105467, by rfl⟩ : syracuseStep 2947913 = 2210935) B2210935
theorem B1965275 : Blo 1963435 1965275 := bstep (se 1 (by rfl) ⟨1473956, by rfl⟩ : syracuseStep 1965275 = 2947913) B2947913
theorem B2798221 : Blo 1963435 2798221 := bbase (se 3 (by rfl) ⟨524666, by rfl⟩ : syracuseStep 2798221 = 1049333) (by norm_num)
theorem B3730961 : Blo 1963435 3730961 := bstep (se 2 (by rfl) ⟨1399110, by rfl⟩ : syracuseStep 3730961 = 2798221) B2798221
theorem B9949229 : Blo 1963435 9949229 := bstep (se 3 (by rfl) ⟨1865480, by rfl⟩ : syracuseStep 9949229 = 3730961) B3730961
theorem B6632819 : Blo 1963435 6632819 := bstep (se 1 (by rfl) ⟨4974614, by rfl⟩ : syracuseStep 6632819 = 9949229) B9949229
theorem B4421879 : Blo 1963435 4421879 := bstep (se 1 (by rfl) ⟨3316409, by rfl⟩ : syracuseStep 4421879 = 6632819) B6632819
theorem B2947919 : Blo 1963435 2947919 := bstep (se 1 (by rfl) ⟨2210939, by rfl⟩ : syracuseStep 2947919 = 4421879) B4421879
theorem B1965279 : Blo 1963435 1965279 := bstep (se 1 (by rfl) ⟨1473959, by rfl⟩ : syracuseStep 1965279 = 2947919) B2947919
theorem B2947925 : Blo 1963435 2947925 := bbase (se 9 (by rfl) ⟨8636, by rfl⟩ : syracuseStep 2947925 = 17273) (by norm_num)
theorem B1965283 : Blo 1963435 1965283 := bstep (se 1 (by rfl) ⟨1473962, by rfl⟩ : syracuseStep 1965283 = 2947925) B2947925
theorem B4197349 : Blo 1963435 4197349 := bbase (se 4 (by rfl) ⟨393501, by rfl⟩ : syracuseStep 4197349 = 787003) (by norm_num)
theorem B5596465 : Blo 1963435 5596465 := bstep (se 2 (by rfl) ⟨2098674, by rfl⟩ : syracuseStep 5596465 = 4197349) B4197349
theorem B7461953 : Blo 1963435 7461953 := bstep (se 2 (by rfl) ⟨2798232, by rfl⟩ : syracuseStep 7461953 = 5596465) B5596465
theorem B4974635 : Blo 1963435 4974635 := bstep (se 1 (by rfl) ⟨3730976, by rfl⟩ : syracuseStep 4974635 = 7461953) B7461953
theorem B3316423 : Blo 1963435 3316423 := bstep (se 1 (by rfl) ⟨2487317, by rfl⟩ : syracuseStep 3316423 = 4974635) B4974635
theorem B4421897 : Blo 1963435 4421897 := bstep (se 2 (by rfl) ⟨1658211, by rfl⟩ : syracuseStep 4421897 = 3316423) B3316423
theorem B2947931 : Blo 1963435 2947931 := bstep (se 1 (by rfl) ⟨2210948, by rfl⟩ : syracuseStep 2947931 = 4421897) B4421897
theorem B1965287 : Blo 1963435 1965287 := bstep (se 1 (by rfl) ⟨1473965, by rfl⟩ : syracuseStep 1965287 = 2947931) B2947931
theorem B2210953 : Blo 1963435 2210953 := bbase (se 2 (by rfl) ⟨829107, by rfl⟩ : syracuseStep 2210953 = 1658215) (by norm_num)
theorem B2947937 : Blo 1963435 2947937 := bstep (se 2 (by rfl) ⟨1105476, by rfl⟩ : syracuseStep 2947937 = 2210953) B2210953
theorem B1965291 : Blo 1963435 1965291 := bstep (se 1 (by rfl) ⟨1473968, by rfl⟩ : syracuseStep 1965291 = 2947937) B2947937
theorem B8077157 : Blo 1963435 8077157 := bbase (se 4 (by rfl) ⟨757233, by rfl⟩ : syracuseStep 8077157 = 1514467) (by norm_num)
theorem B5384771 : Blo 1963435 5384771 := bstep (se 1 (by rfl) ⟨4038578, by rfl⟩ : syracuseStep 5384771 = 8077157) B8077157
theorem B3589847 : Blo 1963435 3589847 := bstep (se 1 (by rfl) ⟨2692385, by rfl⟩ : syracuseStep 3589847 = 5384771) B5384771
theorem B2393231 : Blo 1963435 2393231 := bstep (se 1 (by rfl) ⟨1794923, by rfl⟩ : syracuseStep 2393231 = 3589847) B3589847
theorem B25527797 : Blo 1963435 25527797 := bstep (se 5 (by rfl) ⟨1196615, by rfl⟩ : syracuseStep 25527797 = 2393231) B2393231
theorem B17018531 : Blo 1963435 17018531 := bstep (se 1 (by rfl) ⟨12763898, by rfl⟩ : syracuseStep 17018531 = 25527797) B25527797
theorem B11345687 : Blo 1963435 11345687 := bstep (se 1 (by rfl) ⟨8509265, by rfl⟩ : syracuseStep 11345687 = 17018531) B17018531
theorem B7563791 : Blo 1963435 7563791 := bstep (se 1 (by rfl) ⟨5672843, by rfl⟩ : syracuseStep 7563791 = 11345687) B11345687
theorem B20170109 : Blo 1963435 20170109 := bstep (se 3 (by rfl) ⟨3781895, by rfl⟩ : syracuseStep 20170109 = 7563791) B7563791
theorem B13446739 : Blo 1963435 13446739 := bstep (se 1 (by rfl) ⟨10085054, by rfl⟩ : syracuseStep 13446739 = 20170109) B20170109
theorem B17928985 : Blo 1963435 17928985 := bstep (se 2 (by rfl) ⟨6723369, by rfl⟩ : syracuseStep 17928985 = 13446739) B13446739
theorem B23905313 : Blo 1963435 23905313 := bstep (se 2 (by rfl) ⟨8964492, by rfl⟩ : syracuseStep 23905313 = 17928985) B17928985
theorem B15936875 : Blo 1963435 15936875 := bstep (se 1 (by rfl) ⟨11952656, by rfl⟩ : syracuseStep 15936875 = 23905313) B23905313
theorem B10624583 : Blo 1963435 10624583 := bstep (se 1 (by rfl) ⟨7968437, by rfl⟩ : syracuseStep 10624583 = 15936875) B15936875
theorem B7083055 : Blo 1963435 7083055 := bstep (se 1 (by rfl) ⟨5312291, by rfl⟩ : syracuseStep 7083055 = 10624583) B10624583
theorem B37776293 : Blo 1963435 37776293 := bstep (se 4 (by rfl) ⟨3541527, by rfl⟩ : syracuseStep 37776293 = 7083055) B7083055
theorem B25184195 : Blo 1963435 25184195 := bstep (se 1 (by rfl) ⟨18888146, by rfl⟩ : syracuseStep 25184195 = 37776293) B37776293
theorem B16789463 : Blo 1963435 16789463 := bstep (se 1 (by rfl) ⟨12592097, by rfl⟩ : syracuseStep 16789463 = 25184195) B25184195
theorem B11192975 : Blo 1963435 11192975 := bstep (se 1 (by rfl) ⟨8394731, by rfl⟩ : syracuseStep 11192975 = 16789463) B16789463
theorem B7461983 : Blo 1963435 7461983 := bstep (se 1 (by rfl) ⟨5596487, by rfl⟩ : syracuseStep 7461983 = 11192975) B11192975
theorem B4974655 : Blo 1963435 4974655 := bstep (se 1 (by rfl) ⟨3730991, by rfl⟩ : syracuseStep 4974655 = 7461983) B7461983
theorem B6632873 : Blo 1963435 6632873 := bstep (se 2 (by rfl) ⟨2487327, by rfl⟩ : syracuseStep 6632873 = 4974655) B4974655
theorem B4421915 : Blo 1963435 4421915 := bstep (se 1 (by rfl) ⟨3316436, by rfl⟩ : syracuseStep 4421915 = 6632873) B6632873
theorem B2947943 : Blo 1963435 2947943 := bstep (se 1 (by rfl) ⟨2210957, by rfl⟩ : syracuseStep 2947943 = 4421915) B4421915
theorem B1965295 : Blo 1963435 1965295 := bstep (se 1 (by rfl) ⟨1473971, by rfl⟩ : syracuseStep 1965295 = 2947943) B2947943
theorem B2947949 : Blo 1963435 2947949 := bbase (se 3 (by rfl) ⟨552740, by rfl⟩ : syracuseStep 2947949 = 1105481) (by norm_num)
theorem B1965299 : Blo 1963435 1965299 := bstep (se 1 (by rfl) ⟨1473974, by rfl⟩ : syracuseStep 1965299 = 2947949) B2947949
theorem B4421933 : Blo 1963435 4421933 := bbase (se 3 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 4421933 = 1658225) (by norm_num)
theorem B2947955 : Blo 1963435 2947955 := bstep (se 1 (by rfl) ⟨2210966, by rfl⟩ : syracuseStep 2947955 = 4421933) B4421933
theorem B1965303 : Blo 1963435 1965303 := bstep (se 1 (by rfl) ⟨1473977, by rfl⟩ : syracuseStep 1965303 = 2947955) B2947955
theorem B3984245 : Blo 1963435 3984245 := bbase (se 5 (by rfl) ⟨186761, by rfl⟩ : syracuseStep 3984245 = 373523) (by norm_num)
theorem B2656163 : Blo 1963435 2656163 := bstep (se 1 (by rfl) ⟨1992122, by rfl⟩ : syracuseStep 2656163 = 3984245) B3984245
theorem B7083101 : Blo 1963435 7083101 := bstep (se 3 (by rfl) ⟨1328081, by rfl⟩ : syracuseStep 7083101 = 2656163) B2656163
theorem B4722067 : Blo 1963435 4722067 := bstep (se 1 (by rfl) ⟨3541550, by rfl⟩ : syracuseStep 4722067 = 7083101) B7083101
theorem B6296089 : Blo 1963435 6296089 := bstep (se 2 (by rfl) ⟨2361033, by rfl⟩ : syracuseStep 6296089 = 4722067) B4722067
theorem B8394785 : Blo 1963435 8394785 := bstep (se 2 (by rfl) ⟨3148044, by rfl⟩ : syracuseStep 8394785 = 6296089) B6296089
theorem B5596523 : Blo 1963435 5596523 := bstep (se 1 (by rfl) ⟨4197392, by rfl⟩ : syracuseStep 5596523 = 8394785) B8394785
theorem B3731015 : Blo 1963435 3731015 := bstep (se 1 (by rfl) ⟨2798261, by rfl⟩ : syracuseStep 3731015 = 5596523) B5596523
theorem B2487343 : Blo 1963435 2487343 := bstep (se 1 (by rfl) ⟨1865507, by rfl⟩ : syracuseStep 2487343 = 3731015) B3731015
theorem B3316457 : Blo 1963435 3316457 := bstep (se 2 (by rfl) ⟨1243671, by rfl⟩ : syracuseStep 3316457 = 2487343) B2487343
theorem B2210971 : Blo 1963435 2210971 := bstep (se 1 (by rfl) ⟨1658228, by rfl⟩ : syracuseStep 2210971 = 3316457) B3316457
theorem B2947961 : Blo 1963435 2947961 := bstep (se 2 (by rfl) ⟨1105485, by rfl⟩ : syracuseStep 2947961 = 2210971) B2210971
theorem B1965307 : Blo 1963435 1965307 := bstep (se 1 (by rfl) ⟨1473980, by rfl⟩ : syracuseStep 1965307 = 2947961) B2947961
theorem B12115829 : Blo 1963435 12115829 := bbase (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) (by norm_num)
theorem B8077219 : Blo 1963435 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B43078501 : Blo 1963435 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B57438001 : Blo 1963435 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B76584001 : Blo 1963435 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B102112001 : Blo 1963435 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B68074667 : Blo 1963435 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B45383111 : Blo 1963435 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B30255407 : Blo 1963435 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B20170271 : Blo 1963435 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B13446847 : Blo 1963435 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B17929129 : Blo 1963435 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B23905505 : Blo 1963435 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B15937003 : Blo 1963435 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B21249337 : Blo 1963435 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B28332449 : Blo 1963435 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B18888299 : Blo 1963435 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B12592199 : Blo 1963435 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B33579197 : Blo 1963435 33579197 := bstep (se 3 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 33579197 = 12592199) B12592199
theorem B22386131 : Blo 1963435 22386131 := bstep (se 1 (by rfl) ⟨16789598, by rfl⟩ : syracuseStep 22386131 = 33579197) B33579197
theorem B14924087 : Blo 1963435 14924087 := bstep (se 1 (by rfl) ⟨11193065, by rfl⟩ : syracuseStep 14924087 = 22386131) B22386131
theorem B9949391 : Blo 1963435 9949391 := bstep (se 1 (by rfl) ⟨7462043, by rfl⟩ : syracuseStep 9949391 = 14924087) B14924087
theorem B6632927 : Blo 1963435 6632927 := bstep (se 1 (by rfl) ⟨4974695, by rfl⟩ : syracuseStep 6632927 = 9949391) B9949391
theorem B4421951 : Blo 1963435 4421951 := bstep (se 1 (by rfl) ⟨3316463, by rfl⟩ : syracuseStep 4421951 = 6632927) B6632927
theorem B2947967 : Blo 1963435 2947967 := bstep (se 1 (by rfl) ⟨2210975, by rfl⟩ : syracuseStep 2947967 = 4421951) B4421951
theorem B1965311 : Blo 1963435 1965311 := bstep (se 1 (by rfl) ⟨1473983, by rfl⟩ : syracuseStep 1965311 = 2947967) B2947967
theorem B2947973 : Blo 1963435 2947973 := bbase (se 4 (by rfl) ⟨276372, by rfl⟩ : syracuseStep 2947973 = 552745) (by norm_num)
theorem B1965315 : Blo 1963435 1965315 := bstep (se 1 (by rfl) ⟨1473986, by rfl⟩ : syracuseStep 1965315 = 2947973) B2947973
theorem B3316477 : Blo 1963435 3316477 := bbase (se 3 (by rfl) ⟨621839, by rfl⟩ : syracuseStep 3316477 = 1243679) (by norm_num)
theorem B4421969 : Blo 1963435 4421969 := bstep (se 2 (by rfl) ⟨1658238, by rfl⟩ : syracuseStep 4421969 = 3316477) B3316477
theorem B2947979 : Blo 1963435 2947979 := bstep (se 1 (by rfl) ⟨2210984, by rfl⟩ : syracuseStep 2947979 = 4421969) B4421969
theorem B1965319 : Blo 1963435 1965319 := bstep (se 1 (by rfl) ⟨1473989, by rfl⟩ : syracuseStep 1965319 = 2947979) B2947979
theorem B2210989 : Blo 1963435 2210989 := bbase (se 3 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 2210989 = 829121) (by norm_num)
theorem B2947985 : Blo 1963435 2947985 := bstep (se 2 (by rfl) ⟨1105494, by rfl⟩ : syracuseStep 2947985 = 2210989) B2210989
theorem B1965323 : Blo 1963435 1965323 := bstep (se 1 (by rfl) ⟨1473992, by rfl⟩ : syracuseStep 1965323 = 2947985) B2947985
theorem B6632981 : Blo 1963435 6632981 := bbase (se 6 (by rfl) ⟨155460, by rfl⟩ : syracuseStep 6632981 = 310921) (by norm_num)
theorem B4421987 : Blo 1963435 4421987 := bstep (se 1 (by rfl) ⟨3316490, by rfl⟩ : syracuseStep 4421987 = 6632981) B6632981
theorem B2947991 : Blo 1963435 2947991 := bstep (se 1 (by rfl) ⟨2210993, by rfl⟩ : syracuseStep 2947991 = 4421987) B4421987
theorem B1965327 : Blo 1963435 1965327 := bstep (se 1 (by rfl) ⟨1473995, by rfl⟩ : syracuseStep 1965327 = 2947991) B2947991
theorem B2947997 : Blo 1963435 2947997 := bbase (se 3 (by rfl) ⟨552749, by rfl⟩ : syracuseStep 2947997 = 1105499) (by norm_num)
theorem B1965331 : Blo 1963435 1965331 := bstep (se 1 (by rfl) ⟨1473998, by rfl⟩ : syracuseStep 1965331 = 2947997) B2947997
theorem B4422005 : Blo 1963435 4422005 := bbase (se 5 (by rfl) ⟨207281, by rfl⟩ : syracuseStep 4422005 = 414563) (by norm_num)
theorem B2948003 : Blo 1963435 2948003 := bstep (se 1 (by rfl) ⟨2211002, by rfl⟩ : syracuseStep 2948003 = 4422005) B4422005
theorem B1965335 : Blo 1963435 1965335 := bstep (se 1 (by rfl) ⟨1474001, by rfl⟩ : syracuseStep 1965335 = 2948003) B2948003
theorem B3781981 : Blo 1963435 3781981 := bbase (se 3 (by rfl) ⟨709121, by rfl⟩ : syracuseStep 3781981 = 1418243) (by norm_num)
theorem B20170565 : Blo 1963435 20170565 := bstep (se 4 (by rfl) ⟨1890990, by rfl⟩ : syracuseStep 20170565 = 3781981) B3781981
theorem B13447043 : Blo 1963435 13447043 := bstep (se 1 (by rfl) ⟨10085282, by rfl⟩ : syracuseStep 13447043 = 20170565) B20170565
theorem B8964695 : Blo 1963435 8964695 := bstep (se 1 (by rfl) ⟨6723521, by rfl⟩ : syracuseStep 8964695 = 13447043) B13447043
theorem B23905853 : Blo 1963435 23905853 := bstep (se 3 (by rfl) ⟨4482347, by rfl⟩ : syracuseStep 23905853 = 8964695) B8964695
theorem B15937235 : Blo 1963435 15937235 := bstep (se 1 (by rfl) ⟨11952926, by rfl⟩ : syracuseStep 15937235 = 23905853) B23905853
theorem B10624823 : Blo 1963435 10624823 := bstep (se 1 (by rfl) ⟨7968617, by rfl⟩ : syracuseStep 10624823 = 15937235) B15937235
theorem B7083215 : Blo 1963435 7083215 := bstep (se 1 (by rfl) ⟨5312411, by rfl⟩ : syracuseStep 7083215 = 10624823) B10624823
theorem B4722143 : Blo 1963435 4722143 := bstep (se 1 (by rfl) ⟨3541607, by rfl⟩ : syracuseStep 4722143 = 7083215) B7083215
theorem B12592381 : Blo 1963435 12592381 := bstep (se 3 (by rfl) ⟨2361071, by rfl⟩ : syracuseStep 12592381 = 4722143) B4722143
theorem B16789841 : Blo 1963435 16789841 := bstep (se 2 (by rfl) ⟨6296190, by rfl⟩ : syracuseStep 16789841 = 12592381) B12592381
theorem B11193227 : Blo 1963435 11193227 := bstep (se 1 (by rfl) ⟨8394920, by rfl⟩ : syracuseStep 11193227 = 16789841) B16789841
theorem B7462151 : Blo 1963435 7462151 := bstep (se 1 (by rfl) ⟨5596613, by rfl⟩ : syracuseStep 7462151 = 11193227) B11193227
theorem B4974767 : Blo 1963435 4974767 := bstep (se 1 (by rfl) ⟨3731075, by rfl⟩ : syracuseStep 4974767 = 7462151) B7462151
theorem B3316511 : Blo 1963435 3316511 := bstep (se 1 (by rfl) ⟨2487383, by rfl⟩ : syracuseStep 3316511 = 4974767) B4974767
theorem B2211007 : Blo 1963435 2211007 := bstep (se 1 (by rfl) ⟨1658255, by rfl⟩ : syracuseStep 2211007 = 3316511) B3316511
theorem B2948009 : Blo 1963435 2948009 := bstep (se 2 (by rfl) ⟨1105503, by rfl⟩ : syracuseStep 2948009 = 2211007) B2211007
theorem B1965339 : Blo 1963435 1965339 := bstep (se 1 (by rfl) ⟨1474004, by rfl⟩ : syracuseStep 1965339 = 2948009) B2948009
theorem B7462165 : Blo 1963435 7462165 := bbase (se 6 (by rfl) ⟨174894, by rfl⟩ : syracuseStep 7462165 = 349789) (by norm_num)
theorem B9949553 : Blo 1963435 9949553 := bstep (se 2 (by rfl) ⟨3731082, by rfl⟩ : syracuseStep 9949553 = 7462165) B7462165
theorem B6633035 : Blo 1963435 6633035 := bstep (se 1 (by rfl) ⟨4974776, by rfl⟩ : syracuseStep 6633035 = 9949553) B9949553
theorem B4422023 : Blo 1963435 4422023 := bstep (se 1 (by rfl) ⟨3316517, by rfl⟩ : syracuseStep 4422023 = 6633035) B6633035
theorem B2948015 : Blo 1963435 2948015 := bstep (se 1 (by rfl) ⟨2211011, by rfl⟩ : syracuseStep 2948015 = 4422023) B4422023
theorem B1965343 : Blo 1963435 1965343 := bstep (se 1 (by rfl) ⟨1474007, by rfl⟩ : syracuseStep 1965343 = 2948015) B2948015
theorem B2948021 : Blo 1963435 2948021 := bbase (se 5 (by rfl) ⟨138188, by rfl⟩ : syracuseStep 2948021 = 276377) (by norm_num)
theorem B1965347 : Blo 1963435 1965347 := bstep (se 1 (by rfl) ⟨1474010, by rfl⟩ : syracuseStep 1965347 = 2948021) B2948021
theorem B4974797 : Blo 1963435 4974797 := bbase (se 3 (by rfl) ⟨932774, by rfl⟩ : syracuseStep 4974797 = 1865549) (by norm_num)
theorem B3316531 : Blo 1963435 3316531 := bstep (se 1 (by rfl) ⟨2487398, by rfl⟩ : syracuseStep 3316531 = 4974797) B4974797
theorem B4422041 : Blo 1963435 4422041 := bstep (se 2 (by rfl) ⟨1658265, by rfl⟩ : syracuseStep 4422041 = 3316531) B3316531
theorem B2948027 : Blo 1963435 2948027 := bstep (se 1 (by rfl) ⟨2211020, by rfl⟩ : syracuseStep 2948027 = 4422041) B4422041
theorem B1965351 : Blo 1963435 1965351 := bstep (se 1 (by rfl) ⟨1474013, by rfl⟩ : syracuseStep 1965351 = 2948027) B2948027
theorem B2211025 : Blo 1963435 2211025 := bbase (se 2 (by rfl) ⟨829134, by rfl⟩ : syracuseStep 2211025 = 1658269) (by norm_num)
theorem B2948033 : Blo 1963435 2948033 := bstep (se 2 (by rfl) ⟨1105512, by rfl⟩ : syracuseStep 2948033 = 2211025) B2211025
theorem B1965355 : Blo 1963435 1965355 := bstep (se 1 (by rfl) ⟨1474016, by rfl⟩ : syracuseStep 1965355 = 2948033) B2948033
theorem B5673029 : Blo 1963435 5673029 := bbase (se 4 (by rfl) ⟨531846, by rfl⟩ : syracuseStep 5673029 = 1063693) (by norm_num)
theorem B60512309 : Blo 1963435 60512309 := bstep (se 5 (by rfl) ⟨2836514, by rfl⟩ : syracuseStep 60512309 = 5673029) B5673029
theorem B40341539 : Blo 1963435 40341539 := bstep (se 1 (by rfl) ⟨30256154, by rfl⟩ : syracuseStep 40341539 = 60512309) B60512309
theorem B26894359 : Blo 1963435 26894359 := bstep (se 1 (by rfl) ⟨20170769, by rfl⟩ : syracuseStep 26894359 = 40341539) B40341539
theorem B35859145 : Blo 1963435 35859145 := bstep (se 2 (by rfl) ⟨13447179, by rfl⟩ : syracuseStep 35859145 = 26894359) B26894359
theorem B47812193 : Blo 1963435 47812193 := bstep (se 2 (by rfl) ⟨17929572, by rfl⟩ : syracuseStep 47812193 = 35859145) B35859145
theorem B31874795 : Blo 1963435 31874795 := bstep (se 1 (by rfl) ⟨23906096, by rfl⟩ : syracuseStep 31874795 = 47812193) B47812193
theorem B21249863 : Blo 1963435 21249863 := bstep (se 1 (by rfl) ⟨15937397, by rfl⟩ : syracuseStep 21249863 = 31874795) B31874795
theorem B14166575 : Blo 1963435 14166575 := bstep (se 1 (by rfl) ⟨10624931, by rfl⟩ : syracuseStep 14166575 = 21249863) B21249863
theorem B9444383 : Blo 1963435 9444383 := bstep (se 1 (by rfl) ⟨7083287, by rfl⟩ : syracuseStep 9444383 = 14166575) B14166575
theorem B6296255 : Blo 1963435 6296255 := bstep (se 1 (by rfl) ⟨4722191, by rfl⟩ : syracuseStep 6296255 = 9444383) B9444383
theorem B4197503 : Blo 1963435 4197503 := bstep (se 1 (by rfl) ⟨3148127, by rfl⟩ : syracuseStep 4197503 = 6296255) B6296255
theorem B2798335 : Blo 1963435 2798335 := bstep (se 1 (by rfl) ⟨2098751, by rfl⟩ : syracuseStep 2798335 = 4197503) B4197503
theorem B3731113 : Blo 1963435 3731113 := bstep (se 2 (by rfl) ⟨1399167, by rfl⟩ : syracuseStep 3731113 = 2798335) B2798335
theorem B4974817 : Blo 1963435 4974817 := bstep (se 2 (by rfl) ⟨1865556, by rfl⟩ : syracuseStep 4974817 = 3731113) B3731113
theorem B6633089 : Blo 1963435 6633089 := bstep (se 2 (by rfl) ⟨2487408, by rfl⟩ : syracuseStep 6633089 = 4974817) B4974817
theorem B4422059 : Blo 1963435 4422059 := bstep (se 1 (by rfl) ⟨3316544, by rfl⟩ : syracuseStep 4422059 = 6633089) B6633089
theorem B2948039 : Blo 1963435 2948039 := bstep (se 1 (by rfl) ⟨2211029, by rfl⟩ : syracuseStep 2948039 = 4422059) B4422059
theorem B1965359 : Blo 1963435 1965359 := bstep (se 1 (by rfl) ⟨1474019, by rfl⟩ : syracuseStep 1965359 = 2948039) B2948039
theorem B2948045 : Blo 1963435 2948045 := bbase (se 3 (by rfl) ⟨552758, by rfl⟩ : syracuseStep 2948045 = 1105517) (by norm_num)
theorem B1965363 : Blo 1963435 1965363 := bstep (se 1 (by rfl) ⟨1474022, by rfl⟩ : syracuseStep 1965363 = 2948045) B2948045
theorem B4422077 : Blo 1963435 4422077 := bbase (se 3 (by rfl) ⟨829139, by rfl⟩ : syracuseStep 4422077 = 1658279) (by norm_num)
theorem B2948051 : Blo 1963435 2948051 := bstep (se 1 (by rfl) ⟨2211038, by rfl⟩ : syracuseStep 2948051 = 4422077) B4422077
theorem B1965367 : Blo 1963435 1965367 := bstep (se 1 (by rfl) ⟨1474025, by rfl⟩ : syracuseStep 1965367 = 2948051) B2948051
theorem B3316565 : Blo 1963435 3316565 := bbase (se 9 (by rfl) ⟨9716, by rfl⟩ : syracuseStep 3316565 = 19433) (by norm_num)
theorem B2211043 : Blo 1963435 2211043 := bstep (se 1 (by rfl) ⟨1658282, by rfl⟩ : syracuseStep 2211043 = 3316565) B3316565
theorem B2948057 : Blo 1963435 2948057 := bstep (se 2 (by rfl) ⟨1105521, by rfl⟩ : syracuseStep 2948057 = 2211043) B2211043
theorem B1965371 : Blo 1963435 1965371 := bstep (se 1 (by rfl) ⟨1474028, by rfl⟩ : syracuseStep 1965371 = 2948057) B2948057
theorem B4722229 : Blo 1963435 4722229 := bbase (se 5 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 4722229 = 442709) (by norm_num)
theorem B6296305 : Blo 1963435 6296305 := bstep (se 2 (by rfl) ⟨2361114, by rfl⟩ : syracuseStep 6296305 = 4722229) B4722229
theorem B8395073 : Blo 1963435 8395073 := bstep (se 2 (by rfl) ⟨3148152, by rfl⟩ : syracuseStep 8395073 = 6296305) B6296305
theorem B5596715 : Blo 1963435 5596715 := bstep (se 1 (by rfl) ⟨4197536, by rfl⟩ : syracuseStep 5596715 = 8395073) B8395073
theorem B14924573 : Blo 1963435 14924573 := bstep (se 3 (by rfl) ⟨2798357, by rfl⟩ : syracuseStep 14924573 = 5596715) B5596715
theorem B9949715 : Blo 1963435 9949715 := bstep (se 1 (by rfl) ⟨7462286, by rfl⟩ : syracuseStep 9949715 = 14924573) B14924573
theorem B6633143 : Blo 1963435 6633143 := bstep (se 1 (by rfl) ⟨4974857, by rfl⟩ : syracuseStep 6633143 = 9949715) B9949715
theorem B4422095 : Blo 1963435 4422095 := bstep (se 1 (by rfl) ⟨3316571, by rfl⟩ : syracuseStep 4422095 = 6633143) B6633143
theorem B2948063 : Blo 1963435 2948063 := bstep (se 1 (by rfl) ⟨2211047, by rfl⟩ : syracuseStep 2948063 = 4422095) B4422095
theorem B1965375 : Blo 1963435 1965375 := bstep (se 1 (by rfl) ⟨1474031, by rfl⟩ : syracuseStep 1965375 = 2948063) B2948063
theorem B2948069 : Blo 1963435 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B1965379 : Blo 1963435 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B8395109 : Blo 1963435 8395109 := bbase (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) (by norm_num)
theorem B5596739 : Blo 1963435 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B3731159 : Blo 1963435 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B2487439 : Blo 1963435 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B3316585 : Blo 1963435 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B4422113 : Blo 1963435 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B2948075 : Blo 1963435 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B1965383 : Blo 1963435 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B2211061 : Blo 1963435 2211061 := bbase (se 5 (by rfl) ⟨103643, by rfl⟩ : syracuseStep 2211061 = 207287) (by norm_num)
theorem B2948081 : Blo 1963435 2948081 := bstep (se 2 (by rfl) ⟨1105530, by rfl⟩ : syracuseStep 2948081 = 2211061) B2211061
theorem B1965387 : Blo 1963435 1965387 := bstep (se 1 (by rfl) ⟨1474040, by rfl⟩ : syracuseStep 1965387 = 2948081) B2948081
theorem B2487449 : Blo 1963435 2487449 := bbase (se 2 (by rfl) ⟨932793, by rfl⟩ : syracuseStep 2487449 = 1865587) (by norm_num)
theorem B6633197 : Blo 1963435 6633197 := bstep (se 3 (by rfl) ⟨1243724, by rfl⟩ : syracuseStep 6633197 = 2487449) B2487449
theorem B4422131 : Blo 1963435 4422131 := bstep (se 1 (by rfl) ⟨3316598, by rfl⟩ : syracuseStep 4422131 = 6633197) B6633197
theorem B2948087 : Blo 1963435 2948087 := bstep (se 1 (by rfl) ⟨2211065, by rfl⟩ : syracuseStep 2948087 = 4422131) B4422131
theorem B1965391 : Blo 1963435 1965391 := bstep (se 1 (by rfl) ⟨1474043, by rfl⟩ : syracuseStep 1965391 = 2948087) B2948087
theorem B2948093 : Blo 1963435 2948093 := bbase (se 3 (by rfl) ⟨552767, by rfl⟩ : syracuseStep 2948093 = 1105535) (by norm_num)
theorem B1965395 : Blo 1963435 1965395 := bstep (se 1 (by rfl) ⟨1474046, by rfl⟩ : syracuseStep 1965395 = 2948093) B2948093
theorem B4422149 : Blo 1963435 4422149 := bbase (se 4 (by rfl) ⟨414576, by rfl⟩ : syracuseStep 4422149 = 829153) (by norm_num)
theorem B2948099 : Blo 1963435 2948099 := bstep (se 1 (by rfl) ⟨2211074, by rfl⟩ : syracuseStep 2948099 = 4422149) B4422149
theorem B1965399 : Blo 1963435 1965399 := bstep (se 1 (by rfl) ⟨1474049, by rfl⟩ : syracuseStep 1965399 = 2948099) B2948099
theorem B3731197 : Blo 1963435 3731197 := bbase (se 3 (by rfl) ⟨699599, by rfl⟩ : syracuseStep 3731197 = 1399199) (by norm_num)
theorem B4974929 : Blo 1963435 4974929 := bstep (se 2 (by rfl) ⟨1865598, by rfl⟩ : syracuseStep 4974929 = 3731197) B3731197
theorem B3316619 : Blo 1963435 3316619 := bstep (se 1 (by rfl) ⟨2487464, by rfl⟩ : syracuseStep 3316619 = 4974929) B4974929
theorem B2211079 : Blo 1963435 2211079 := bstep (se 1 (by rfl) ⟨1658309, by rfl⟩ : syracuseStep 2211079 = 3316619) B3316619
theorem B2948105 : Blo 1963435 2948105 := bstep (se 2 (by rfl) ⟨1105539, by rfl⟩ : syracuseStep 2948105 = 2211079) B2211079
theorem B1965403 : Blo 1963435 1965403 := bstep (se 1 (by rfl) ⟨1474052, by rfl⟩ : syracuseStep 1965403 = 2948105) B2948105
theorem B9949877 : Blo 1963435 9949877 := bbase (se 5 (by rfl) ⟨466400, by rfl⟩ : syracuseStep 9949877 = 932801) (by norm_num)
theorem B6633251 : Blo 1963435 6633251 := bstep (se 1 (by rfl) ⟨4974938, by rfl⟩ : syracuseStep 6633251 = 9949877) B9949877
theorem B4422167 : Blo 1963435 4422167 := bstep (se 1 (by rfl) ⟨3316625, by rfl⟩ : syracuseStep 4422167 = 6633251) B6633251
theorem B2948111 : Blo 1963435 2948111 := bstep (se 1 (by rfl) ⟨2211083, by rfl⟩ : syracuseStep 2948111 = 4422167) B4422167
theorem B1965407 : Blo 1963435 1965407 := bstep (se 1 (by rfl) ⟨1474055, by rfl⟩ : syracuseStep 1965407 = 2948111) B2948111
theorem B2948117 : Blo 1963435 2948117 := bbase (se 6 (by rfl) ⟨69096, by rfl⟩ : syracuseStep 2948117 = 138193) (by norm_num)
theorem B1965411 : Blo 1963435 1965411 := bstep (se 1 (by rfl) ⟨1474058, by rfl⟩ : syracuseStep 1965411 = 2948117) B2948117
theorem B18889301 : Blo 1963435 18889301 := bbase (se 8 (by rfl) ⟨110679, by rfl⟩ : syracuseStep 18889301 = 221359) (by norm_num)
theorem B12592867 : Blo 1963435 12592867 := bstep (se 1 (by rfl) ⟨9444650, by rfl⟩ : syracuseStep 12592867 = 18889301) B18889301
theorem B16790489 : Blo 1963435 16790489 := bstep (se 2 (by rfl) ⟨6296433, by rfl⟩ : syracuseStep 16790489 = 12592867) B12592867
theorem B11193659 : Blo 1963435 11193659 := bstep (se 1 (by rfl) ⟨8395244, by rfl⟩ : syracuseStep 11193659 = 16790489) B16790489
theorem B7462439 : Blo 1963435 7462439 := bstep (se 1 (by rfl) ⟨5596829, by rfl⟩ : syracuseStep 7462439 = 11193659) B11193659
theorem B4974959 : Blo 1963435 4974959 := bstep (se 1 (by rfl) ⟨3731219, by rfl⟩ : syracuseStep 4974959 = 7462439) B7462439
theorem B3316639 : Blo 1963435 3316639 := bstep (se 1 (by rfl) ⟨2487479, by rfl⟩ : syracuseStep 3316639 = 4974959) B4974959
theorem B4422185 : Blo 1963435 4422185 := bstep (se 2 (by rfl) ⟨1658319, by rfl⟩ : syracuseStep 4422185 = 3316639) B3316639
theorem B2948123 : Blo 1963435 2948123 := bstep (se 1 (by rfl) ⟨2211092, by rfl⟩ : syracuseStep 2948123 = 4422185) B4422185
theorem B1965415 : Blo 1963435 1965415 := bstep (se 1 (by rfl) ⟨1474061, by rfl⟩ : syracuseStep 1965415 = 2948123) B2948123
theorem B2211097 : Blo 1963435 2211097 := bbase (se 2 (by rfl) ⟨829161, by rfl⟩ : syracuseStep 2211097 = 1658323) (by norm_num)
theorem B2948129 : Blo 1963435 2948129 := bstep (se 2 (by rfl) ⟨1105548, by rfl⟩ : syracuseStep 2948129 = 2211097) B2211097
theorem B1965419 : Blo 1963435 1965419 := bstep (se 1 (by rfl) ⟨1474064, by rfl⟩ : syracuseStep 1965419 = 2948129) B2948129
theorem B7462469 : Blo 1963435 7462469 := bbase (se 4 (by rfl) ⟨699606, by rfl⟩ : syracuseStep 7462469 = 1399213) (by norm_num)
theorem B4974979 : Blo 1963435 4974979 := bstep (se 1 (by rfl) ⟨3731234, by rfl⟩ : syracuseStep 4974979 = 7462469) B7462469
theorem B6633305 : Blo 1963435 6633305 := bstep (se 2 (by rfl) ⟨2487489, by rfl⟩ : syracuseStep 6633305 = 4974979) B4974979
theorem B4422203 : Blo 1963435 4422203 := bstep (se 1 (by rfl) ⟨3316652, by rfl⟩ : syracuseStep 4422203 = 6633305) B6633305
theorem B2948135 : Blo 1963435 2948135 := bstep (se 1 (by rfl) ⟨2211101, by rfl⟩ : syracuseStep 2948135 = 4422203) B4422203
theorem B1965423 : Blo 1963435 1965423 := bstep (se 1 (by rfl) ⟨1474067, by rfl⟩ : syracuseStep 1965423 = 2948135) B2948135
theorem B2948141 : Blo 1963435 2948141 := bbase (se 3 (by rfl) ⟨552776, by rfl⟩ : syracuseStep 2948141 = 1105553) (by norm_num)
theorem B1965427 : Blo 1963435 1965427 := bstep (se 1 (by rfl) ⟨1474070, by rfl⟩ : syracuseStep 1965427 = 2948141) B2948141
theorem B4422221 : Blo 1963435 4422221 := bbase (se 3 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 4422221 = 1658333) (by norm_num)
theorem B2948147 : Blo 1963435 2948147 := bstep (se 1 (by rfl) ⟨2211110, by rfl⟩ : syracuseStep 2948147 = 4422221) B4422221
theorem B1965431 : Blo 1963435 1965431 := bstep (se 1 (by rfl) ⟨1474073, by rfl⟩ : syracuseStep 1965431 = 2948147) B2948147
theorem B2487505 : Blo 1963435 2487505 := bbase (se 2 (by rfl) ⟨932814, by rfl⟩ : syracuseStep 2487505 = 1865629) (by norm_num)
theorem B3316673 : Blo 1963435 3316673 := bstep (se 2 (by rfl) ⟨1243752, by rfl⟩ : syracuseStep 3316673 = 2487505) B2487505
theorem B2211115 : Blo 1963435 2211115 := bstep (se 1 (by rfl) ⟨1658336, by rfl⟩ : syracuseStep 2211115 = 3316673) B3316673
theorem B2948153 : Blo 1963435 2948153 := bstep (se 2 (by rfl) ⟨1105557, by rfl⟩ : syracuseStep 2948153 = 2211115) B2211115
theorem B1965435 : Blo 1963435 1965435 := bstep (se 1 (by rfl) ⟨1474076, by rfl⟩ : syracuseStep 1965435 = 2948153) B2948153
theorem C0 (j : ℕ) (h1 : 490858 ≤ j) (h2 : j ≤ 491358) : Blo 1963435 (4 * j + 3) := by
  interval_cases j
  · exact B1963435
  · exact B1963439
  · exact B1963443
  · exact B1963447
  · exact B1963451
  · exact B1963455
  · exact B1963459
  · exact B1963463
  · exact B1963467
  · exact B1963471
  · exact B1963475
  · exact B1963479
  · exact B1963483
  · exact B1963487
  · exact B1963491
  · exact B1963495
  · exact B1963499
  · exact B1963503
  · exact B1963507
  · exact B1963511
  · exact B1963515
  · exact B1963519
  · exact B1963523
  · exact B1963527
  · exact B1963531
  · exact B1963535
  · exact B1963539
  · exact B1963543
  · exact B1963547
  · exact B1963551
  · exact B1963555
  · exact B1963559
  · exact B1963563
  · exact B1963567
  · exact B1963571
  · exact B1963575
  · exact B1963579
  · exact B1963583
  · exact B1963587
  · exact B1963591
  · exact B1963595
  · exact B1963599
  · exact B1963603
  · exact B1963607
  · exact B1963611
  · exact B1963615
  · exact B1963619
  · exact B1963623
  · exact B1963627
  · exact B1963631
  · exact B1963635
  · exact B1963639
  · exact B1963643
  · exact B1963647
  · exact B1963651
  · exact B1963655
  · exact B1963659
  · exact B1963663
  · exact B1963667
  · exact B1963671
  · exact B1963675
  · exact B1963679
  · exact B1963683
  · exact B1963687
  · exact B1963691
  · exact B1963695
  · exact B1963699
  · exact B1963703
  · exact B1963707
  · exact B1963711
  · exact B1963715
  · exact B1963719
  · exact B1963723
  · exact B1963727
  · exact B1963731
  · exact B1963735
  · exact B1963739
  · exact B1963743
  · exact B1963747
  · exact B1963751
  · exact B1963755
  · exact B1963759
  · exact B1963763
  · exact B1963767
  · exact B1963771
  · exact B1963775
  · exact B1963779
  · exact B1963783
  · exact B1963787
  · exact B1963791
  · exact B1963795
  · exact B1963799
  · exact B1963803
  · exact B1963807
  · exact B1963811
  · exact B1963815
  · exact B1963819
  · exact B1963823
  · exact B1963827
  · exact B1963831
  · exact B1963835
  · exact B1963839
  · exact B1963843
  · exact B1963847
  · exact B1963851
  · exact B1963855
  · exact B1963859
  · exact B1963863
  · exact B1963867
  · exact B1963871
  · exact B1963875
  · exact B1963879
  · exact B1963883
  · exact B1963887
  · exact B1963891
  · exact B1963895
  · exact B1963899
  · exact B1963903
  · exact B1963907
  · exact B1963911
  · exact B1963915
  · exact B1963919
  · exact B1963923
  · exact B1963927
  · exact B1963931
  · exact B1963935
  · exact B1963939
  · exact B1963943
  · exact B1963947
  · exact B1963951
  · exact B1963955
  · exact B1963959
  · exact B1963963
  · exact B1963967
  · exact B1963971
  · exact B1963975
  · exact B1963979
  · exact B1963983
  · exact B1963987
  · exact B1963991
  · exact B1963995
  · exact B1963999
  · exact B1964003
  · exact B1964007
  · exact B1964011
  · exact B1964015
  · exact B1964019
  · exact B1964023
  · exact B1964027
  · exact B1964031
  · exact B1964035
  · exact B1964039
  · exact B1964043
  · exact B1964047
  · exact B1964051
  · exact B1964055
  · exact B1964059
  · exact B1964063
  · exact B1964067
  · exact B1964071
  · exact B1964075
  · exact B1964079
  · exact B1964083
  · exact B1964087
  · exact B1964091
  · exact B1964095
  · exact B1964099
  · exact B1964103
  · exact B1964107
  · exact B1964111
  · exact B1964115
  · exact B1964119
  · exact B1964123
  · exact B1964127
  · exact B1964131
  · exact B1964135
  · exact B1964139
  · exact B1964143
  · exact B1964147
  · exact B1964151
  · exact B1964155
  · exact B1964159
  · exact B1964163
  · exact B1964167
  · exact B1964171
  · exact B1964175
  · exact B1964179
  · exact B1964183
  · exact B1964187
  · exact B1964191
  · exact B1964195
  · exact B1964199
  · exact B1964203
  · exact B1964207
  · exact B1964211
  · exact B1964215
  · exact B1964219
  · exact B1964223
  · exact B1964227
  · exact B1964231
  · exact B1964235
  · exact B1964239
  · exact B1964243
  · exact B1964247
  · exact B1964251
  · exact B1964255
  · exact B1964259
  · exact B1964263
  · exact B1964267
  · exact B1964271
  · exact B1964275
  · exact B1964279
  · exact B1964283
  · exact B1964287
  · exact B1964291
  · exact B1964295
  · exact B1964299
  · exact B1964303
  · exact B1964307
  · exact B1964311
  · exact B1964315
  · exact B1964319
  · exact B1964323
  · exact B1964327
  · exact B1964331
  · exact B1964335
  · exact B1964339
  · exact B1964343
  · exact B1964347
  · exact B1964351
  · exact B1964355
  · exact B1964359
  · exact B1964363
  · exact B1964367
  · exact B1964371
  · exact B1964375
  · exact B1964379
  · exact B1964383
  · exact B1964387
  · exact B1964391
  · exact B1964395
  · exact B1964399
  · exact B1964403
  · exact B1964407
  · exact B1964411
  · exact B1964415
  · exact B1964419
  · exact B1964423
  · exact B1964427
  · exact B1964431
  · exact B1964435
  · exact B1964439
  · exact B1964443
  · exact B1964447
  · exact B1964451
  · exact B1964455
  · exact B1964459
  · exact B1964463
  · exact B1964467
  · exact B1964471
  · exact B1964475
  · exact B1964479
  · exact B1964483
  · exact B1964487
  · exact B1964491
  · exact B1964495
  · exact B1964499
  · exact B1964503
  · exact B1964507
  · exact B1964511
  · exact B1964515
  · exact B1964519
  · exact B1964523
  · exact B1964527
  · exact B1964531
  · exact B1964535
  · exact B1964539
  · exact B1964543
  · exact B1964547
  · exact B1964551
  · exact B1964555
  · exact B1964559
  · exact B1964563
  · exact B1964567
  · exact B1964571
  · exact B1964575
  · exact B1964579
  · exact B1964583
  · exact B1964587
  · exact B1964591
  · exact B1964595
  · exact B1964599
  · exact B1964603
  · exact B1964607
  · exact B1964611
  · exact B1964615
  · exact B1964619
  · exact B1964623
  · exact B1964627
  · exact B1964631
  · exact B1964635
  · exact B1964639
  · exact B1964643
  · exact B1964647
  · exact B1964651
  · exact B1964655
  · exact B1964659
  · exact B1964663
  · exact B1964667
  · exact B1964671
  · exact B1964675
  · exact B1964679
  · exact B1964683
  · exact B1964687
  · exact B1964691
  · exact B1964695
  · exact B1964699
  · exact B1964703
  · exact B1964707
  · exact B1964711
  · exact B1964715
  · exact B1964719
  · exact B1964723
  · exact B1964727
  · exact B1964731
  · exact B1964735
  · exact B1964739
  · exact B1964743
  · exact B1964747
  · exact B1964751
  · exact B1964755
  · exact B1964759
  · exact B1964763
  · exact B1964767
  · exact B1964771
  · exact B1964775
  · exact B1964779
  · exact B1964783
  · exact B1964787
  · exact B1964791
  · exact B1964795
  · exact B1964799
  · exact B1964803
  · exact B1964807
  · exact B1964811
  · exact B1964815
  · exact B1964819
  · exact B1964823
  · exact B1964827
  · exact B1964831
  · exact B1964835
  · exact B1964839
  · exact B1964843
  · exact B1964847
  · exact B1964851
  · exact B1964855
  · exact B1964859
  · exact B1964863
  · exact B1964867
  · exact B1964871
  · exact B1964875
  · exact B1964879
  · exact B1964883
  · exact B1964887
  · exact B1964891
  · exact B1964895
  · exact B1964899
  · exact B1964903
  · exact B1964907
  · exact B1964911
  · exact B1964915
  · exact B1964919
  · exact B1964923
  · exact B1964927
  · exact B1964931
  · exact B1964935
  · exact B1964939
  · exact B1964943
  · exact B1964947
  · exact B1964951
  · exact B1964955
  · exact B1964959
  · exact B1964963
  · exact B1964967
  · exact B1964971
  · exact B1964975
  · exact B1964979
  · exact B1964983
  · exact B1964987
  · exact B1964991
  · exact B1964995
  · exact B1964999
  · exact B1965003
  · exact B1965007
  · exact B1965011
  · exact B1965015
  · exact B1965019
  · exact B1965023
  · exact B1965027
  · exact B1965031
  · exact B1965035
  · exact B1965039
  · exact B1965043
  · exact B1965047
  · exact B1965051
  · exact B1965055
  · exact B1965059
  · exact B1965063
  · exact B1965067
  · exact B1965071
  · exact B1965075
  · exact B1965079
  · exact B1965083
  · exact B1965087
  · exact B1965091
  · exact B1965095
  · exact B1965099
  · exact B1965103
  · exact B1965107
  · exact B1965111
  · exact B1965115
  · exact B1965119
  · exact B1965123
  · exact B1965127
  · exact B1965131
  · exact B1965135
  · exact B1965139
  · exact B1965143
  · exact B1965147
  · exact B1965151
  · exact B1965155
  · exact B1965159
  · exact B1965163
  · exact B1965167
  · exact B1965171
  · exact B1965175
  · exact B1965179
  · exact B1965183
  · exact B1965187
  · exact B1965191
  · exact B1965195
  · exact B1965199
  · exact B1965203
  · exact B1965207
  · exact B1965211
  · exact B1965215
  · exact B1965219
  · exact B1965223
  · exact B1965227
  · exact B1965231
  · exact B1965235
  · exact B1965239
  · exact B1965243
  · exact B1965247
  · exact B1965251
  · exact B1965255
  · exact B1965259
  · exact B1965263
  · exact B1965267
  · exact B1965271
  · exact B1965275
  · exact B1965279
  · exact B1965283
  · exact B1965287
  · exact B1965291
  · exact B1965295
  · exact B1965299
  · exact B1965303
  · exact B1965307
  · exact B1965311
  · exact B1965315
  · exact B1965319
  · exact B1965323
  · exact B1965327
  · exact B1965331
  · exact B1965335
  · exact B1965339
  · exact B1965343
  · exact B1965347
  · exact B1965351
  · exact B1965355
  · exact B1965359
  · exact B1965363
  · exact B1965367
  · exact B1965371
  · exact B1965375
  · exact B1965379
  · exact B1965383
  · exact B1965387
  · exact B1965391
  · exact B1965395
  · exact B1965399
  · exact B1965403
  · exact B1965407
  · exact B1965411
  · exact B1965415
  · exact B1965419
  · exact B1965423
  · exact B1965427
  · exact B1965431
  · exact B1965435
theorem solution (m : ℕ) (hlo : 1963435 ≤ m) (hhi : m ≤ 1965435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 490858 ≤ j := by omega
    have hj2 : j ≤ 491358 := by omega
    have hb : Blo 1963435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
